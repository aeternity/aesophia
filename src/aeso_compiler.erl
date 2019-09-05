%%%-------------------------------------------------------------------
%%% @author Happi (Erik Stenman)
%%% @copyright (C) 2017, Aeternity Anstalt
%%% @doc
%%%     Compiler from Aeterinty Sophia language to the Aeternity VM, aevm.
%%% @end
%%% Created : 12 Dec 2017
%%%-------------------------------------------------------------------
-module(aeso_compiler).

-export([ file/1
        , file/2
        , from_string/2
        , check_call/4
        , create_calldata/3  %% deprecated
        , create_calldata/4
        , version/0
        , sophia_type_to_typerep/1
        , to_sophia_value/4  %% deprecated, need a backend
        , to_sophia_value/5
        , decode_calldata/3  %% deprecated
        , decode_calldata/4
        , parse/2
        , add_include_path/2
        ]).

-include_lib("aebytecode/include/aeb_opcodes.hrl").
-include("aeso_icode.hrl").


-type option() :: pp_sophia_code
                | pp_ast
                | pp_types
                | pp_typed_ast
                | pp_icode
                | pp_assembler
                | pp_bytecode
                | no_code
                | {backend, aevm | fate}
                | {include, {file_system, [string()]} |
                            {explicit_files, #{string() => binary()}}}
                | {src_file, string()}.
-type options() :: [option()].

-export_type([ option/0
             , options/0
             ]).

-spec version() -> {ok, binary()} | {error, term()}.
version() ->
    case lists:keyfind(aesophia, 1, application:loaded_applications()) of
        false ->
            case application:load(aesophia) of
                ok ->
                    case application:get_key(aesophia, vsn) of
                        {ok, VsnString} ->
                            {ok, list_to_binary(VsnString)};
                        undefined ->
                            {error, failed_to_load_aesophia}
                    end;
                Err = {error, _} ->
                    Err
            end;
        {_App, _Des, VsnString} ->
            {ok, list_to_binary(VsnString)}
    end.

-spec file(string()) -> {ok, map()} | {error, binary()}.
file(Filename) ->
    file(Filename, []).

-spec file(string(), options()) -> {ok, map()} | {error, binary()}.
file(File, Options0) ->
    Options = add_include_path(File, Options0),
    case read_contract(File) of
        {ok, Bin} -> from_string(Bin, [{src_file, File} | Options]);
        {error, Error} ->
	    ErrorString = [File,": ",file:format_error(Error)],
	    {error, join_errors("File errors", [ErrorString], fun(E) -> E end)}
    end.

add_include_path(File, Options) ->
    case lists:keymember(include, 1, Options) of
        true  -> Options;
        false ->
            Dir = filename:dirname(File),
            {ok, Cwd} = file:get_cwd(),
            [{include, {file_system, [Cwd, Dir]}} | Options]
    end.

-spec from_string(binary() | string(), options()) -> {ok, map()} | {error, binary()}.
from_string(Contract, Options) ->
    from_string(proplists:get_value(backend, Options, aevm), Contract, Options).

from_string(Backend, ContractBin, Options) when is_binary(ContractBin) ->
    from_string(Backend, binary_to_list(ContractBin), Options);
from_string(Backend, ContractString, Options) ->
    try
        from_string1(Backend, ContractString, Options)
    catch
        throw:{error, Errors} -> {error, Errors}
    end.

from_string1(aevm, ContractString, Options) ->
    #{icode := Icode} = string_to_code(ContractString, Options),
    TypeInfo  = extract_type_info(Icode),
    Assembler = assemble(Icode, Options),
    pp_assembler(Assembler, Options),
    ByteCodeList = to_bytecode(Assembler, Options),
    ByteCode = << << B:8 >> || B <- ByteCodeList >>,
    pp_bytecode(ByteCode, Options),
    {ok, Version} = version(),
    {ok, #{byte_code => ByteCode,
           compiler_version => Version,
           contract_source => ContractString,
           type_info => TypeInfo,
           abi_version => aeb_aevm_abi:abi_version(),
           payable => maps:get(payable, Icode)
          }};
from_string1(fate, ContractString, Options) ->
    #{fcode := FCode} = string_to_code(ContractString, Options),
    FateCode = aeso_fcode_to_fate:compile(FCode, Options),
    ByteCode = aeb_fate_code:serialize(FateCode, []),
    {ok, Version} = version(),
    {ok, #{byte_code => ByteCode,
           compiler_version => Version,
           contract_source => ContractString,
           type_info => [],
           fate_code => FateCode,
           abi_version => aeb_fate_abi:abi_version(),
           payable => maps:get(payable, FCode)
          }}.

-spec string_to_code(string(), options()) -> map().
string_to_code(ContractString, Options) ->
    Ast = parse(ContractString, Options),
    pp_sophia_code(Ast, Options),
    pp_ast(Ast, Options),
    {TypeEnv, TypedAst} = aeso_ast_infer_types:infer(Ast, [return_env | Options]),
    pp_typed_ast(TypedAst, Options),
    case proplists:get_value(backend, Options, aevm) of
        aevm ->
            Icode = ast_to_icode(TypedAst, Options),
            pp_icode(Icode, Options),
            #{ icode => Icode,
               typed_ast => TypedAst,
               type_env  => TypeEnv};
        fate ->
            Fcode = aeso_ast_to_fcode:ast_to_fcode(TypedAst, Options),
            #{ fcode => Fcode,
               typed_ast => TypedAst,
               type_env  => TypeEnv}
    end.

join_errors(Prefix, Errors, Pfun) ->
    Ess = [ Pfun(E) || E <- Errors ],
    list_to_binary(string:join([Prefix|Ess], "\n")).

-define(CALL_NAME,   "__call").
-define(DECODE_NAME, "__decode").

%% Takes a string containing a contract with a declaration/prototype of a
%% function (foo, say) and adds function __call() = foo(args) calling this
%% function. Returns the name of the called functions, typereps and Erlang
%% terms for the arguments.
%% NOTE: Special treatment for "init" since it might be implicit and has
%%       a special return type (typerep, T)
-spec check_call(string(), string(), [string()], options()) -> {ok, string(), {[Type], Type}, [term()]}
                                                                   | {ok, string(), [term()]}
                                                                   | {error, term()}
    when Type :: term().
check_call(Source, "init" = FunName, Args, Options) ->
    case check_call1(Source, FunName, Args, Options) of
        Err = {error, _} when Args == [] ->
            %% Try with default init-function
            case check_call1(insert_init_function(Source, Options), FunName, Args, Options) of
                {error, _} -> Err; %% The first error is most likely better...
                Res        -> Res
            end;
        Res ->
            Res
    end;
check_call(Source, FunName, Args, Options) ->
    check_call1(Source, FunName, Args, Options).

check_call1(ContractString0, FunName, Args, Options) ->
    try
        case proplists:get_value(backend, Options, aevm) of
            aevm ->
                %% First check the contract without the __call function
                #{} = string_to_code(ContractString0, Options),
                ContractString = insert_call_function(ContractString0, ?CALL_NAME, FunName, Args, Options),
                #{typed_ast := TypedAst,
                  icode     := Icode} = string_to_code(ContractString, Options),
                {ok, {FunName, {fun_t, _, _, ArgTypes, RetType}}} = get_call_type(TypedAst),
                ArgVMTypes = [ aeso_ast_to_icode:ast_typerep(T, Icode) || T <- ArgTypes ],
                RetVMType  = case RetType of
                                 {id, _, "_"} -> any;
                                 _            -> aeso_ast_to_icode:ast_typerep(RetType, Icode)
                             end,
                #{ functions := Funs } = Icode,
                ArgIcode = get_arg_icode(Funs),
                ArgTerms = [ icode_to_term(T, Arg) ||
                               {T, Arg} <- lists:zip(ArgVMTypes, ArgIcode) ],
                RetVMType1 =
                    case FunName of
                        "init" -> {tuple, [typerep, RetVMType]};
                        _ -> RetVMType
                    end,
                {ok, FunName, {ArgVMTypes, RetVMType1}, ArgTerms};
            fate ->
                %% First check the contract without the __call function
                #{fcode := OrgFcode} = string_to_code(ContractString0, Options),
                FateCode = aeso_fcode_to_fate:compile(OrgFcode, []),
                %% collect all hashes and compute the first name without hash collision to
                SymbolHashes = maps:keys(aeb_fate_code:symbols(FateCode)),
                CallName = first_none_match(?CALL_NAME, SymbolHashes,
                                            lists:seq($1, $9) ++ lists:seq($A, $Z) ++ lists:seq($a, $z)),
                ContractString = insert_call_function(ContractString0, CallName, FunName, Args, Options),
                #{fcode := Fcode} = string_to_code(ContractString, Options),
                CallArgs = arguments_of_body(CallName, FunName, Fcode),
                {ok, FunName, CallArgs}
        end
    catch
        throw:{error, Errors} -> {error, Errors};
        error:{badmatch, {error, missing_call_function}} ->
            {error, join_errors("Type errors", ["missing __call function"],
                                fun (E) -> E end)}
    end.

arguments_of_body(CallName, _FunName, Fcode) ->
    #{body := Body} = maps:get({entrypoint, list_to_binary(CallName)}, maps:get(functions, Fcode)),
    {def, _FName, Args} = Body,
    %% FName is either {entrypoint, list_to_binary(FunName)} or 'init'
    [ aeso_fcode_to_fate:term_to_fate(A) || A <- Args ].

first_none_match(_CallName, _Hashes, []) ->
    error(unable_to_find_unique_call_name);
first_none_match(CallName, Hashes, [Char|Chars]) ->
    case not lists:member(aeb_fate_code:symbol_identifier(list_to_binary(CallName)), Hashes) of
        true ->
            CallName;
        false ->
            first_none_match(?CALL_NAME++[Char], Hashes, Chars)
    end.

%% Add the __call function to a contract.
-spec insert_call_function(string(), string(), string(), [string()], options()) -> string().
insert_call_function(Code, Call, FunName, Args, Options) ->
    Ast = parse(Code, Options),
    Ind = last_contract_indent(Ast),
    lists:flatten(
        [ Code,
          "\n\n",
          lists:duplicate(Ind, " "),
          "stateful entrypoint ", Call, "() = ", FunName, "(", string:join(Args, ","), ")\n"
        ]).

-spec insert_init_function(string(), options()) -> string().
insert_init_function(Code, Options) ->
    Ast = parse(Code, Options),
    Ind = last_contract_indent(Ast),
    lists:flatten(
        [ Code,
          "\n\n",
          lists:duplicate(Ind, " "), "entrypoint init() = ()\n"
        ]).

last_contract_indent(Decls) ->
    case lists:last(Decls) of
        {_, _, _, [Decl | _]} -> aeso_syntax:get_ann(col, Decl, 1) - 1;
        _                     -> 0
    end.

-spec to_sophia_value(string(), string(), ok | error | revert, aeb_aevm_data:data()) ->
        {ok, aeso_syntax:expr()} | {error, term()}.
to_sophia_value(ContractString, Fun, ResType, Data) ->
    to_sophia_value(ContractString, Fun, ResType, Data, [{backend, aevm}]).

-spec to_sophia_value(string(), string(), ok | error | revert, binary(), options()) ->
        {ok, aeso_syntax:expr()} | {error, term()}.
to_sophia_value(_, _, error, Err, _Options) ->
    {ok, {app, [], {id, [], "error"}, [{string, [], Err}]}};
to_sophia_value(_, _, revert, Data, Options) ->
    case proplists:get_value(backend, Options, aevm) of
        aevm ->
            case aeb_heap:from_binary(string, Data) of
                {ok, Err} -> {ok, {app, [], {id, [], "abort"}, [{string, [], Err}]}};
                {error, _} = Err -> Err
            end;
        fate ->
            Err = aeb_fate_encoding:deserialize(Data),
            {ok, {app, [], {id, [], "abort"}, [{string, [], Err}]}}
    end;
to_sophia_value(ContractString, FunName, ok, Data, Options0) ->
    Options = [no_code | Options0],
    try
        Code = string_to_code(ContractString, Options),
        #{ typed_ast := TypedAst, type_env  := TypeEnv} = Code,
        {ok, _, Type0} = get_decode_type(FunName, TypedAst),
        Type   = aeso_ast_infer_types:unfold_types_in_type(TypeEnv, Type0, [unfold_record_types, unfold_variant_types]),

        case proplists:get_value(backend, Options, aevm) of
            aevm ->
                Icode  = maps:get(icode, Code),
                VmType = aeso_ast_to_icode:ast_typerep(Type, Icode),
                case aeb_heap:from_binary(VmType, Data) of
                    {ok, VmValue} ->
                        try
                            {ok, aeso_vm_decode:from_aevm(VmType, Type, VmValue)}
                        catch throw:cannot_translate_to_sophia ->
                            Type0Str = prettypr:format(aeso_pretty:type(Type0)),
                            {error, join_errors("Translation error", [lists:flatten(io_lib:format("Cannot translate VM value ~p\n  of type ~p\n  to Sophia type ~s\n",
                                                                                    [Data, VmType, Type0Str]))],
                                                fun (E) -> E end)}
                        end;
                    {error, _Err} ->
                        {error, join_errors("Decode errors", [lists:flatten(io_lib:format("Failed to decode binary at type ~p", [VmType]))],
                                            fun(E) -> E end)}
                end;
            fate ->
               try
                   {ok, aeso_vm_decode:from_fate(Type, aeb_fate_encoding:deserialize(Data))}
               catch throw:cannot_translate_to_sophia ->
                   {error, join_errors("Translation error",
                                       [lists:flatten(io_lib:format("Cannot translate fate value ~p\n of Sophia type ~s\n",
                                                                    [aeb_fate_encoding:deserialize(Data), Type]))],
                                       fun (E) -> E end)};
                     _:R ->
                   {error, iolist_to_binary(io_lib:format("Decode error ~p: ~p\n", [R, erlang:get_stacktrace()]))}
               end
        end
    catch
        throw:{error, Errors} -> {error, Errors};
        error:{badmatch, {error, missing_function}} ->
            {error, join_errors("Type errors", ["no function: '" ++ FunName ++ "'"],
                                fun (E) -> E end)}
    end.


-spec create_calldata(string(), string(), [string()]) ->
                             {ok, binary(), aeb_aevm_data:type(), aeb_aevm_data:type()}
                             | {error, term()}.
create_calldata(Code, Fun, Args) ->
    create_calldata(Code, Fun, Args, [{backend, aevm}]).

-spec create_calldata(string(), string(), [string()], [{atom(), any()}]) ->
                             {ok, binary()}
                             | {error, term()}.
create_calldata(Code, Fun, Args, Options0) ->
    Options = [no_code | Options0],
    case proplists:get_value(backend, Options, aevm) of
        aevm ->
            case check_call(Code, Fun, Args, Options) of
                {ok, FunName, {ArgTypes, RetType}, VMArgs} ->
                    aeb_aevm_abi:create_calldata(FunName, VMArgs, ArgTypes, RetType);
                {error, _} = Err -> Err
            end;
        fate ->
            case check_call(Code, Fun, Args, Options) of
                {ok, FunName, FateArgs} ->
                    aeb_fate_abi:create_calldata(FunName, FateArgs);
                {error, _} = Err -> Err
            end
    end.

-spec decode_calldata(string(), string(), binary()) ->
                             {ok, [aeso_syntax:type()], [aeso_syntax:expr()]}
                             | {error, term()}.
decode_calldata(ContractString, FunName, Calldata) ->
    decode_calldata(ContractString, FunName, Calldata, [{backend, aevm}]).

decode_calldata(ContractString, FunName, Calldata, Options0) ->
    Options = [no_code | Options0],
    try
        Code = string_to_code(ContractString, Options),
        #{ typed_ast := TypedAst, type_env  := TypeEnv} = Code,

        {ok, Args, _} = get_decode_type(FunName, TypedAst),
        DropArg       = fun({arg, _, _, T}) -> T; (T) -> T end,
        ArgTypes      = lists:map(DropArg, Args),
        Type0         = {tuple_t, [], ArgTypes},
        %% user defined data types such as variants needed to match against
        Type          = aeso_ast_infer_types:unfold_types_in_type(TypeEnv, Type0, [unfold_record_types, unfold_variant_types]),
        case proplists:get_value(backend, Options, aevm) of
            aevm ->
                Icode  = maps:get(icode, Code),
                VmType = aeso_ast_to_icode:ast_typerep(Type, Icode),
                case aeb_heap:from_binary({tuple, [word, VmType]}, Calldata) of
                    {ok, {_, VmValue}} ->
                        try
                            {tuple, [], Values} = aeso_vm_decode:from_aevm(VmType, Type, VmValue),
                            %% Values are Sophia expressions in AST format
                            {ok, ArgTypes, Values}
                        catch throw:cannot_translate_to_sophia ->
                                Type0Str = prettypr:format(aeso_pretty:type(Type0)),
                                {error, join_errors("Translation error",
                                                    [lists:flatten(io_lib:format("Cannot translate VM value ~p\n  of type ~p\n  to Sophia type ~s\n",
                                                                                 [VmValue, VmType, Type0Str]))],
                                                    fun (E) -> E end)}
                        end;
                    {error, _Err} ->
                        {error, join_errors("Decode errors", [lists:flatten(io_lib:format("Failed to decode binary at type ~p", [VmType]))],
                                            fun(E) -> E end)}
                end;
            fate ->
                case aeb_fate_abi:decode_calldata(FunName, Calldata) of
                    {ok, FateArgs} ->
                        try
                            {tuple_t, [], ArgTypes1} = Type,
                            AstArgs = [ aeso_vm_decode:from_fate(ArgType, FateArg)
                                        || {ArgType, FateArg} <- lists:zip(ArgTypes1, FateArgs)],
                            {ok, ArgTypes, AstArgs}
                        catch throw:cannot_translate_to_sophia ->
                                Type0Str = prettypr:format(aeso_pretty:type(Type0)),
                                {error, join_errors("Translation error",
                                                    [lists:flatten(io_lib:format("Cannot translate fate value ~p\n of Sophia type ~s\n",
                                                                                 [FateArgs, Type0Str]))],
                                                    fun (E) -> E end)}
                        end;
                    {error, _} ->
                        {error, join_errors("Decode errors", ["Failed to decode binary"],
                                            fun(E) -> E end)}
                end
        end
    catch
        throw:{error, Errors} ->
            {error, Errors};
        error:{badmatch, {error, missing_function}} ->
            {error, join_errors("Type errors", ["no function: '" ++ FunName ++ "'"],
                                fun (E) -> E end)}
    end.

get_arg_icode(Funs) ->
    case [ Args || {[_, ?CALL_NAME], _, _, {funcall, _, Args}, _} <- Funs ] of
        [Args] -> Args;
        []     -> error({missing_call_function, Funs})
    end.

get_call_type([{contract, _, _, Defs}]) ->
    case [ {lists:last(QFunName), FunType}
          || {letfun, _, {id, _, ?CALL_NAME}, [], _Ret,
                {typed, _,
                    {app, _,
                        {typed, _, {qid, _, QFunName}, FunType}, _}, _}} <- Defs ] of
        [Call] -> {ok, Call};
        []     -> {error, missing_call_function}
    end;
get_call_type([_ | Contracts]) ->
    %% The __call should be in the final contract
    get_call_type(Contracts).

get_decode_type(FunName, [{contract, _, _, Defs}]) ->
    GetType = fun({letfun, _, {id, _, Name}, Args, Ret, _})               when Name == FunName -> [{Args, Ret}];
                 ({fun_decl, _, {id, _, Name}, {fun_t, _, _, Args, Ret}}) when Name == FunName -> [{Args, Ret}];
                 (_) -> [] end,
    case lists:flatmap(GetType, Defs) of
        [{Args, Ret}] -> {ok, Args, Ret};
        []            ->
            case FunName of
                "init" -> {ok, [], {tuple_t, [], []}};
                 _ -> {error, missing_function}
            end
    end;
get_decode_type(FunName, [_ | Contracts]) ->
    %% The __decode should be in the final contract
    get_decode_type(FunName, Contracts).

%% Translate an icode value (error if not value) to an Erlang term that can be
%% consumed by aeb_heap:to_binary().
icode_to_term(word, {integer, N}) -> N;
icode_to_term(word, {unop, '-', {integer, N}}) -> -N;
icode_to_term(string, {tuple, [{integer, Len} | Words]}) ->
    <<Str:Len/binary, _/binary>> = << <<W:256>> || {integer, W} <- Words >>,
    Str;
icode_to_term({list, T}, {list, Vs}) ->
    [ icode_to_term(T, V) || V <- Vs ];
icode_to_term({tuple, Ts}, {tuple, Vs}) ->
    list_to_tuple(icodes_to_terms(Ts, Vs));
icode_to_term({variant, Cs}, {tuple, [{integer, Tag} | Args]}) ->
    Ts = lists:nth(Tag + 1, Cs),
    {variant, Tag, icodes_to_terms(Ts, Args)};
icode_to_term(T = {map, KT, VT}, M) ->
    %% Maps are compiled to builtin and primop calls, so this gets a little hairy
    case M of
        {funcall, {var_ref, {builtin, map_put}}, [M1, K, V]} ->
            Map = icode_to_term(T, M1),
            Key = icode_to_term(KT, K),
            Val = icode_to_term(VT, V),
            Map#{ Key => Val };
        #prim_call_contract{ address = {integer, 0},
                             arg = {tuple, [{integer, ?PRIM_CALL_MAP_EMPTY}, _, _]} } ->
            #{};
        _ -> throw({todo, M})
    end;
icode_to_term(typerep, _) ->
    throw({todo, typerep});
icode_to_term(T, V) ->
    throw({not_a_value, T, V}).

icodes_to_terms(Ts, Vs) ->
    [ icode_to_term(T, V) || {T, V} <- lists:zip(Ts, Vs) ].

ast_to_icode(TypedAst, Options) ->
    aeso_ast_to_icode:convert_typed(TypedAst, Options).

assemble(Icode, Options) ->
    aeso_icode_to_asm:convert(Icode, Options).


to_bytecode(['COMMENT',_|Rest],_Options) ->
    to_bytecode(Rest,_Options);
to_bytecode([Op|Rest], Options) ->
    [aeb_opcodes:m_to_op(Op)|to_bytecode(Rest, Options)];
to_bytecode([], _) -> [].

extract_type_info(#{functions := Functions} =_Icode) ->
    ArgTypesOnly = fun(As) -> [ T || {_, T} <- As ] end,
    Payable = fun(Attrs) -> proplists:get_value(payable, Attrs, false) end,
    TypeInfo = [aeb_aevm_abi:function_type_info(list_to_binary(lists:last(Name)),
                                            Payable(Attrs), ArgTypesOnly(Args), TypeRep)
                || {Name, Attrs, Args,_Body, TypeRep} <- Functions,
                   not is_tuple(Name),
                   not lists:member(private, Attrs)
               ],
    lists:sort(TypeInfo).

pp_sophia_code(C, Opts)->  pp(C, Opts, pp_sophia_code, fun(Code) ->
                                io:format("~s\n", [prettypr:format(aeso_pretty:decls(Code))])
                            end).
pp_ast(C, Opts)      ->  pp(C, Opts, pp_ast, fun aeso_ast:pp/1).
pp_typed_ast(C, Opts)->  pp(C, Opts, pp_typed_ast, fun aeso_ast:pp_typed/1).
pp_icode(C, Opts)    ->  pp(C, Opts, pp_icode, fun aeso_icode:pp/1).
pp_assembler(C, Opts)->  pp(C, Opts, pp_assembler, fun aeb_asm:pp/1).
pp_bytecode(C, Opts) ->  pp(C, Opts, pp_bytecode, fun aeb_disassemble:pp/1).

pp(Code, Options, Option, PPFun) ->
    case proplists:lookup(Option, Options) of
        {Option, true} ->
            PPFun(Code);
        none ->
            ok
    end.

%% -------------------------------------------------------------------

sophia_type_to_typerep(String) ->
    {ok, Ast} = aeso_parser:type(String),
    try aeso_ast_to_icode:ast_typerep(Ast) of
        Type -> {ok, Type}
    catch _:_ -> {error, bad_type}
    end.

-spec parse(string(), aeso_compiler:options()) -> none() | aeso_syntax:ast().
parse(Text, Options) ->
    parse(Text, sets:new(), Options).

-spec parse(string(), sets:set(), aeso_compiler:options()) -> none() | aeso_syntax:ast().
parse(Text, Included, Options) ->
    aeso_parser:string(Text, Included, Options).

read_contract(Name) ->
    file:read_file(Name).
