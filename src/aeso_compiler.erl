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
        , check_call/2
        , create_calldata/3
        , version/0
        , sophia_type_to_typerep/1
        , to_sophia_value/4
        , to_sophia_value/5
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
                | {include, {file_system, [string()]} |
                            {explicit_files, #{string() => binary()}}}
                | {src_file, string()}.
-type options() :: [option()].

-export_type([ option/0
             , options/0
             ]).

-define(COMPILER_VERSION_1, 1).
-define(COMPILER_VERSION_2, 2).

-define(COMPILER_VERSION, ?COMPILER_VERSION_2).

-spec version() -> pos_integer().
version() ->
    ?COMPILER_VERSION.

-spec file(string()) -> {ok, map()} | {error, binary()}.
file(Filename) ->
    Dir = filename:dirname(Filename),
    {ok, Cwd} = file:get_cwd(),
    file(Filename, [{include, {file_system, [Cwd, Dir]}}]).

-spec file(string(), options()) -> {ok, map()} | {error, binary()}.
file(File, Options) ->
    case read_contract(File) of
        {ok, Bin} -> from_string(Bin, [{src_file, File} | Options]);
        {error, Error} ->
	    ErrorString = [File,": ",file:format_error(Error)],
	    {error, join_errors("File errors", [ErrorString], fun(E) -> E end)}
    end.

-spec from_string(binary() | string(), options()) -> {ok, map()} | {error, binary()}.
from_string(ContractBin, Options) when is_binary(ContractBin) ->
    from_string(binary_to_list(ContractBin), Options);
from_string(ContractString, Options) ->
    try
        Ast = parse(ContractString, Options),
        ok = pp_sophia_code(Ast, Options),
        ok = pp_ast(Ast, Options),
        TypedAst = aeso_ast_infer_types:infer(Ast, Options),
        %% pp_types is handled inside aeso_ast_infer_types.
        ok = pp_typed_ast(TypedAst, Options),
        ICode = to_icode(TypedAst, Options),
        TypeInfo = extract_type_info(ICode),
        ok = pp_icode(ICode, Options),
        Assembler =  assemble(ICode, Options),
        ok = pp_assembler(Assembler, Options),
        ByteCodeList = to_bytecode(Assembler, Options),
        ByteCode = << << B:8 >> || B <- ByteCodeList >>,
        ok = pp_bytecode(ByteCode, Options),
        {ok, #{byte_code => ByteCode,
               compiler_version => version(),
               contract_source => ContractString,
               type_info => TypeInfo
              }}
    catch
        %% The compiler errors.
        error:{parse_errors, Errors} ->
            {error, join_errors("Parse errors", Errors, fun(E) -> E end)};
        error:{type_errors, Errors} ->
            {error, join_errors("Type errors", Errors, fun(E) -> E end)};
        error:{code_errors, Errors} ->
            {error, join_errors("Code errors", Errors,
                                fun (E) -> io_lib:format("~p", [E]) end)}
        %% General programming errors in the compiler just signal error.
    end.

join_errors(Prefix, Errors, Pfun) ->
    Ess = [ Pfun(E) || E <- Errors ],
    list_to_binary(string:join([Prefix|Ess], "\n")).

-define(CALL_NAME,   "__call").
-define(DECODE_NAME, "__decode").

%% Takes a string containing a contract with a declaration/prototype of a
%% function (foo, say) and a function __call() = foo(args) calling this
%% function. Returns the name of the called functions, typereps and Erlang
%% terms for the arguments.
-spec check_call(string(), options()) -> {ok, string(), {[Type], Type | any}, [term()]} | {error, term()}
    when Type :: term().
check_call(ContractString, Options) ->
    try
        Ast = parse(ContractString, Options),
        ok = pp_sophia_code(Ast, Options),
        ok = pp_ast(Ast, Options),
        TypedAst = aeso_ast_infer_types:infer(Ast, [permissive_address_literals]),
        {ok, {FunName, {fun_t, _, _, ArgTypes, RetType}}} = get_call_type(TypedAst),
        ok = pp_typed_ast(TypedAst, Options),
        Icode = to_icode(TypedAst, Options),
        ArgVMTypes = [ aeso_ast_to_icode:ast_typerep(T, Icode) || T <- ArgTypes ],
        RetVMType  = case RetType of
                         {id, _, "_"} -> any;
                         _            -> aeso_ast_to_icode:ast_typerep(RetType, Icode)
                     end,
        ok = pp_icode(Icode, Options),
        #{ functions := Funs } = Icode,
        ArgIcode = get_arg_icode(Funs),
        ArgTerms = [ icode_to_term(T, Arg) ||
                       {T, Arg} <- lists:zip(ArgVMTypes, ArgIcode) ],
        {ok, FunName, {ArgVMTypes, RetVMType}, ArgTerms}
    catch
        error:{parse_errors, Errors} ->
            {error, join_errors("Parse errors", Errors, fun (E) -> E end)};
        error:{type_errors, Errors} ->
            {error, join_errors("Type errors", Errors, fun (E) -> E end)};
        error:{badmatch, {error, missing_call_function}} ->
            {error, join_errors("Type errors", ["missing __call function"],
                                fun (E) -> E end)};
        throw:Error ->                          %Don't ask
            {error, join_errors("Code errors", [Error],
                                fun (E) -> io_lib:format("~p", [E]) end)}
    end.

-spec to_sophia_value(string(), string(), ok | error | revert, aeso_sophia:data()) ->
        {ok, aeso_syntax:expr()} | {error, term()}.
to_sophia_value(ContractString, Fun, ResType, Data) ->
    to_sophia_value(ContractString, Fun, ResType, Data, []).

-spec to_sophia_value(string(), string(), ok | error | revert, binary(), options()) ->
        {ok, aeso_syntax:expr()} | {error, term()}.
to_sophia_value(_, _, error, Err, _Options) ->
    {ok, {app, [], {id, [], "error"}, [{string, [], Err}]}};
to_sophia_value(_, _, revert, Data, _Options) ->
    case aeso_heap:from_binary(string, Data) of
        {ok, Err} -> {ok, {app, [], {id, [], "abort"}, [{string, [], Err}]}};
        {error, _} = Err -> Err
    end;
to_sophia_value(ContractString, FunName, ok, Data, Options) ->
    try
        Ast = parse(ContractString, Options),
        ok = pp_sophia_code(Ast, Options),
        ok = pp_ast(Ast, Options),
        {Env, TypedAst} = aeso_ast_infer_types:infer(Ast, [return_env]),
        ok = pp_typed_ast(TypedAst, Options),
        {ok, Type0} = get_decode_type(FunName, TypedAst),
        Type = aeso_ast_infer_types:unfold_types_in_type(Env, Type0, [unfold_record_types, unfold_variant_types]),
        Icode = to_icode(TypedAst, Options),
        VmType = aeso_ast_to_icode:ast_typerep(Type, Icode),
        ok = pp_icode(Icode, Options),
        case aeso_heap:from_binary(VmType, Data) of
            {ok, VmValue} ->
                try
                    {ok, translate_vm_value(VmType, Type, VmValue)}
                catch throw:cannot_translate_to_sophia ->
                    Type0Str = prettypr:format(aeso_pretty:type(Type0)),
                    {error, join_errors("Translation error", [lists:flatten(io_lib:format("Cannot translate VM value ~p\n  of type ~p\n  to Sophia type ~s\n",
                                                                            [Data, VmType, Type0Str]))],
                                        fun (E) -> E end)}
                end;
            {error, _Err} ->
                {error, join_errors("Decode errors", [lists:flatten(io_lib:format("Failed to decode binary at type ~p", [VmType]))],
                                    fun(E) -> E end)}
        end
    catch
        error:{parse_errors, Errors} ->
            {error, join_errors("Parse errors", Errors, fun (E) -> E end)};
        error:{type_errors, Errors} ->
            {error, join_errors("Type errors", Errors, fun (E) -> E end)};
        error:{badmatch, {error, missing_function}} ->
            {error, join_errors("Type errors", ["no function: '" ++ FunName ++ "'"],
                                fun (E) -> E end)};
        throw:Error ->                          %Don't ask
            {error, join_errors("Code errors", [Error],
                                fun (E) -> io_lib:format("~p", [E]) end)}
    end.

address_literal(N) -> {hash, [], <<N:256>>}.  % TODO

%% TODO: somewhere else
translate_vm_value(word,   {id, _, "address"},                     N) -> address_literal(N);
translate_vm_value(word,   {app_t, _, {id, _, "oracle"}, _},       N) -> address_literal(N);
translate_vm_value(word,   {app_t, _, {id, _, "oracle_query"}, _}, N) -> address_literal(N);
translate_vm_value(word,   {id, _, "hash"},    N) -> {hash, [], <<N:256>>};
translate_vm_value(word,   {id, _, "int"},     N) -> {int, [], N};
translate_vm_value(word,   {id, _, "bits"},    N) -> error({todo, bits, N});
translate_vm_value(word,   {id, _, "bool"},    N) -> {bool, [], N /= 0};
translate_vm_value({tuple, [word, word]}, {id, _, "signature"}, {tuple, [Hi, Lo]}) ->
    {hash, [], <<Hi:256, Lo:256>>};
translate_vm_value(string, {id, _, "string"}, S) -> {string, [], S};
translate_vm_value({list, VmType}, {app_t, _, {id, _, "list"}, [Type]}, List) ->
    {list, [], [translate_vm_value(VmType, Type, X) || X <- List]};
translate_vm_value({option, VmType}, {app_t, _, {id, _, "option"}, [Type]}, Val) ->
    case Val of
        none              -> {con, [], "None"};
        {some, X}         -> {app, [], {con, [], "Some"}, [translate_vm_value(VmType, Type, X)]}
    end;
translate_vm_value({variant, [[], [VmType]]}, {app_t, _, {id, _, "option"}, [Type]}, Val) ->
    case Val of
        {variant, 0, []}  -> {con, [], "None"};
        {variant, 1, [X]} -> {app, [], {con, [], "Some"}, [translate_vm_value(VmType, Type, X)]}
    end;
translate_vm_value({tuple, VmTypes}, {tuple_t, _, Types}, Val)
        when length(VmTypes) == length(Types),
             length(VmTypes) == tuple_size(Val) ->
    {tuple, [], [translate_vm_value(VmType, Type, X)
                 || {VmType, Type, X} <- lists:zip3(VmTypes, Types, tuple_to_list(Val))]};
translate_vm_value({tuple, VmTypes}, {record_t, Fields}, Val)
        when length(VmTypes) == length(Fields),
             length(VmTypes) == tuple_size(Val) ->
    {record, [], [ {field, [], [{proj, [], FName}], translate_vm_value(VmType, FType, X)}
                   || {VmType, {field_t, _, FName, FType}, X} <- lists:zip3(VmTypes, Fields, tuple_to_list(Val)) ]};
translate_vm_value({map, VmKeyType, VmValType}, {app_t, _, {id, _, "map"}, [KeyType, ValType]}, Map)
        when is_map(Map) ->
    {map, [], [ {translate_vm_value(VmKeyType, KeyType, Key),
                 translate_vm_value(VmValType, ValType, Val)}
                || {Key, Val} <- maps:to_list(Map) ]};
translate_vm_value({variant, VmCons}, {variant_t, Cons}, {variant, Tag, Args})
        when length(VmCons) == length(Cons),
             length(VmCons) > Tag ->
    VmTypes = lists:nth(Tag + 1, VmCons),
    ConType = lists:nth(Tag + 1, Cons),
    translate_vm_value(VmTypes, ConType, Args);
translate_vm_value(VmTypes, {constr_t, _, Con, Types}, Args)
        when length(VmTypes) == length(Types),
             length(VmTypes) == length(Args) ->
    {app, [], Con, [ translate_vm_value(VmType, Type, Arg)
                     || {VmType, Type, Arg} <- lists:zip3(VmTypes, Types, Args) ]};
translate_vm_value(_VmType, _Type, _Data) ->
    throw(cannot_translate_to_sophia).

-spec create_calldata(map(), string(), string()) ->
                             {ok, binary(), aeso_sophia:type(), aeso_sophia:type()}
                                 | {error, argument_syntax_error}.
create_calldata(Contract, "", CallCode) when is_map(Contract) ->
    case check_call(CallCode, []) of
        {ok, FunName, {ArgTypes, RetType}, Args} ->
            aeso_abi:create_calldata(Contract, FunName, Args, ArgTypes, RetType);
        {error, _} = Err -> Err
    end;
create_calldata(Contract, Function, Argument) when is_map(Contract) ->
    %% Slightly hacky shortcut to let you get away without writing the full
    %% call contract code.
    %% Function should be "foo : type", and
    %% Argument should be "Arg1, Arg2, .., ArgN" (no parens)
    case string:lexemes(Function, ": ") of
        %% If function is a single word fallback to old calldata generation
        [FunName] -> aeso_abi:old_create_calldata(Contract, FunName, Argument);
        [FunName | _] ->
            Args    = lists:map(fun($\n) -> 32; (X) -> X end, Argument),    %% newline to space
            CallContract = lists:flatten(
                [ "contract MakeCall =\n"
                , "  function ", Function, "\n"
                , "  function __call() = ", FunName, "(", Args, ")"
                ]),
            create_calldata(Contract, "", CallContract)
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
    GetType = fun({letfun, _, {id, _, Name}, _, Ret, _})               when Name == FunName -> [Ret];
                 ({fun_decl, _, {id, _, Name}, {fun_t, _, _, _, Ret}}) when Name == FunName -> [Ret];
                 (_) -> [] end,
    io:format("~p\n", [Defs]),
    case lists:flatmap(GetType, Defs) of
        [Type] -> {ok, Type};
        []     -> {error, missing_function}
    end;
get_decode_type(FunName, [_ | Contracts]) ->
    %% The __decode should be in the final contract
    get_decode_type(FunName, Contracts).

%% Translate an icode value (error if not value) to an Erlang term that can be
%% consumed by aeso_heap:to_binary().
icode_to_term(word, {integer, N}) -> N;
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

to_icode(TypedAst, Options) ->
    aeso_ast_to_icode:convert_typed(TypedAst, Options).

assemble(Icode, Options) ->
    aeso_icode_to_asm:convert(Icode, Options).


to_bytecode(['COMMENT',_|Rest],_Options) ->
    to_bytecode(Rest,_Options);
to_bytecode([Op|Rest], Options) ->
    [aeb_opcodes:m_to_op(Op)|to_bytecode(Rest, Options)];
to_bytecode([], _) -> [].

extract_type_info(#{functions := Functions} =_Icode) ->
    TypeInfo = [aeso_abi:function_type_info(list_to_binary(lists:last(Name)), Args, TypeRep)
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
%% TODO: Tempoary parser hook below...

sophia_type_to_typerep(String) ->
    {ok, Ast} = aeso_parser:type(String),
    try aeso_ast_to_icode:ast_typerep(Ast) of
        Type -> {ok, Type}
    catch _:_ -> {error, bad_type}
    end.

parse(Text, Options) ->
    %% Try and return something sensible here!
    case aeso_parser:string(Text, Options) of
        %% Yay, it worked!
        {ok, Contract} -> Contract;
        %% Scan errors.
        {error, {Pos, scan_error}} ->
            parse_error(Pos, "scan error");
        {error, {Pos, scan_error_no_state}} ->
            parse_error(Pos, "scan error");
        %% Parse errors.
        {error, {Pos, parse_error, Error}} ->
            parse_error(Pos, Error);
        {error, {Pos, ambiguous_parse, As}} ->
            ErrorString = io_lib:format("Ambiguous ~p", [As]),
            parse_error(Pos, ErrorString);
        %% Include error
        {error, {Pos, include_error, File}} ->
            parse_error(Pos, io_lib:format("could not find include file '~s'", [File]))
    end.

parse_error(Pos, ErrorString) ->
    Error = io_lib:format("~s: ~s", [pos_error(Pos), ErrorString]),
    error({parse_errors, [Error]}).

read_contract(Name) ->
    file:read_file(Name).

pos_error({Line, Pos}) ->
    io_lib:format("line ~p, column ~p", [Line, Pos]);
pos_error({no_file, Line, Pos}) ->
    pos_error({Line, Pos});
pos_error({File, Line, Pos}) ->
    io_lib:format("file ~s, line ~p, column ~p", [File, Line, Pos]).

