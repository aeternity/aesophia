%%%-------------------------------------------------------------------
%%% @author Happi (Erik Stenman)
%%% @copyright (C) 2017, Aeternity Anstalt
%%% @doc
%%%     Compiler from Aeterinty Sophia language to FATE.
%%% @end
%%% Created : 12 Dec 2017
%%%-------------------------------------------------------------------
-module(aeso_compiler).

-export([ file/1
        , file/2
        , from_string/2
        , check_call/4
        , decode_value/4
        , encode_value/4
        , create_calldata/3
        , create_calldata/4
        , version/0
        , numeric_version/0
        , to_sophia_value/4
        , to_sophia_value/5
        , decode_calldata/3
        , decode_calldata/4
        , parse/2
        , add_include_path/2
        , validate_byte_code/3
        ]).

-include_lib("aebytecode/include/aeb_opcodes.hrl").
-include("aeso_utils.hrl").


-type option() :: pp_sophia_code
                | pp_ast
                | pp_types
                | pp_typed_ast
                | pp_assembler
                | no_code
                | keep_included
                | debug_mode
                | {include, {file_system, [string()]} |
                            {explicit_files, #{string() => binary()}}}
                | {src_file, string()}
                | {aci, aeso_aci:aci_type()}.
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

-spec numeric_version() -> {ok, [non_neg_integer()]} | {error, term()}.
numeric_version() ->
    case version() of
        {ok, Bin} ->
            [NoSuf | _] = binary:split(Bin, <<"-">>),
            Numbers     = binary:split(NoSuf, <<".">>, [global]),
            {ok, [binary_to_integer(Num) || Num <- Numbers]};
        {error, _} = Err ->
            Err
    end.

-spec file(string()) -> {ok, map()} | {error, [aeso_errors:error()]}.
file(Filename) ->
    file(Filename, []).

-spec file(string(), options()) -> {ok, map()} | {error, [aeso_errors:error()]}.
file(File, Options0) ->
    Options = add_include_path(File, Options0),
    case read_contract(File) of
        {ok, Bin} -> from_string(Bin, [{src_file, File} | Options]);
        {error, Error} ->
            Msg = lists:flatten([File,": ",file:format_error(Error)]),
            {error, [aeso_errors:new(file_error, Msg)]}
    end.

add_include_path(File, Options) ->
    case lists:keymember(include, 1, Options) of
        true  -> Options;
        false ->
            Dir = filename:dirname(File),
            {ok, Cwd} = file:get_cwd(),
            [{include, {file_system, [Cwd, Dir]}} | Options]
    end.

-spec from_string(binary() | string(), options()) -> {ok, map()} | {error, [aeso_errors:error()]}.
from_string(ContractBin, Options) when is_binary(ContractBin) ->
    from_string(binary_to_list(ContractBin), Options);
from_string(ContractString, Options) ->
    try
        from_string1(ContractString, Options)
    catch
        throw:{error, Errors} -> {error, Errors}
    end.

from_string1(ContractString, Options) ->
    #{ fcode := FCode
     , fcode_env := FCodeEnv
     , folded_typed_ast := FoldedTypedAst
     , warnings := Warnings } = string_to_code(ContractString, Options),
    #{ child_con_env := ChildContracts } = FCodeEnv,
    SavedFreshNames = maps:get(saved_fresh_names, FCodeEnv, #{}),
    FateCode = aeso_fcode_to_fate:compile(ChildContracts, FCode, SavedFreshNames, Options),
    pp_assembler(FateCode, Options),
    ByteCode = aeb_fate_code:serialize(FateCode, []),
    {ok, Version} = version(),
    Res = #{byte_code => ByteCode,
            compiler_version => Version,
            contract_source => ContractString,
            type_info => [],
            fate_code => FateCode,
            abi_version => aeb_fate_abi:abi_version(),
            payable => maps:get(payable, FCode),
            warnings => Warnings
           },
    {ok, maybe_generate_aci(Res, FoldedTypedAst, Options)}.

maybe_generate_aci(Result, FoldedTypedAst, Options) ->
    case proplists:get_value(aci, Options) of
        undefined ->
            Result;
        Type ->
            {ok, Aci} = aeso_aci:from_typed_ast(Type, FoldedTypedAst),
            maps:put(aci, Aci, Result)
    end.

-spec string_to_code(string(), options()) -> map().
string_to_code(ContractString, Options) ->
    Ast = parse(ContractString, Options),
    pp_sophia_code(Ast, Options),
    pp_ast(Ast, Options),
    {TypeEnv, FoldedTypedAst, UnfoldedTypedAst, Warnings} = aeso_ast_infer_types:infer(Ast, [return_env | Options]),
    pp_typed_ast(UnfoldedTypedAst, Options),
    {Env, Fcode} = aeso_ast_to_fcode:ast_to_fcode(UnfoldedTypedAst, [{original_src, ContractString}|Options]),
    #{ fcode => Fcode
    ,  fcode_env => Env
    ,  unfolded_typed_ast => UnfoldedTypedAst
    ,  folded_typed_ast => FoldedTypedAst
    ,  type_env  => TypeEnv
    ,  ast => Ast
    ,  warnings => Warnings }.

-define(CALL_NAME,   "__call").

%% Takes a string containing a contract with a declaration/prototype of a
%% function (foo, say) and adds function __call() = foo(args) calling this
%% function. Returns the name of the called functions, typereps and Erlang
%% terms for the arguments.
%% NOTE: Special treatment for "init" since it might be implicit and has
%%       a special return type (typerep, T)
-spec check_call(string(), string(), [string()], options()) -> {ok, string(), [term()]}
                                                             | {error, [aeso_errors:error()]}.
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
    case add_extra_call(ContractString0, {call, FunName, Args}, Options) of
        {ok, CallName, Code} ->
            {def, _, FcodeArgs} = get_call_body(CallName, Code),
            {ok, FunName, [ aeso_fcode_to_fate:term_to_fate(A) || A <- FcodeArgs ]};
        Err = {error, _} ->
            Err
    end.

add_extra_call(Contract0, Call, Options) ->
    try
        %% First check the contract without the __call function
        #{fcode := OrgFcode
        , fcode_env := #{child_con_env := ChildContracts}
        , ast := Ast} = string_to_code(Contract0, Options),
        FateCode = aeso_fcode_to_fate:compile(ChildContracts, OrgFcode, #{}, []),
        %% collect all hashes and compute the first name without hash collision to
        SymbolHashes = maps:keys(aeb_fate_code:symbols(FateCode)),
        CallName = first_none_match(?CALL_NAME, SymbolHashes,
                                    lists:seq($1, $9) ++ lists:seq($A, $Z) ++ lists:seq($a, $z)),
        Contract = insert_call_function(Ast, Contract0, CallName, Call),
        {ok, CallName, string_to_code(Contract, Options)}
    catch
        throw:{error, Errors} -> {error, Errors}
    end.

get_call_body(CallName, #{fcode := Fcode}) ->
    #{body := Body} = maps:get({entrypoint, list_to_binary(CallName)}, maps:get(functions, Fcode)),
    Body.

encode_value(Contract0, Type, Value, Options) ->
    case add_extra_call(Contract0, {value, Type, Value}, Options) of
        {ok, CallName, Code} ->
            Body = get_call_body(CallName, Code),
            {ok, aeb_fate_encoding:serialize(aeso_fcode_to_fate:term_to_fate(Body))};
        Err = {error, _} ->
            Err
    end.

decode_value(Contract0, Type, FateValue, Options) ->
    case add_extra_call(Contract0, {type, Type}, Options) of
        {ok, CallName, Code} ->
            #{ unfolded_typed_ast := TypedAst
             , type_env           := TypeEnv} = Code,
            {ok, _, Type0} = get_decode_type(CallName, TypedAst),
            Type1 = aeso_ast_infer_types:unfold_types_in_type(TypeEnv, Type0, [unfold_record_types, unfold_variant_types]),
            fate_data_to_sophia_value(Type0, Type1, FateValue);
        Err = {error, _} ->
            Err
    end.

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
-spec insert_call_function(aeso_syntax:ast(), string(), string(),
                           {call, string(), [string()]} | {value, string(), string()} | {type, string()}) -> string().
insert_call_function(Ast, Code, Call, {call, FunName, Args}) ->
    Ind = last_contract_indent(Ast),
    lists:flatten(
        [ Code,
          "\n\n",
          lists:duplicate(Ind, " "),
          "stateful entrypoint ", Call, "() = ", FunName, "(", string:join(Args, ","), ")\n"
        ]);
insert_call_function(Ast, Code, Call, {value, Type, Value}) ->
    Ind = last_contract_indent(Ast),
    lists:flatten(
        [ Code,
          "\n\n",
          lists:duplicate(Ind, " "),
          "entrypoint ", Call, "() : ", Type, " = ", Value, "\n"
        ]);
insert_call_function(Ast, Code, Call, {type, Type}) ->
    Ind = last_contract_indent(Ast),
    lists:flatten(
        [ Code,
          "\n\n",
          lists:duplicate(Ind, " "),
          "entrypoint ", Call, "(val : ", Type, ") = val\n"
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
        {_, _, _, _, [Decl | _]} -> aeso_syntax:get_ann(col, Decl, 1) - 1;
        _                        -> 0
    end.

-spec to_sophia_value(string(), string(), ok | error | revert, binary()) ->
          {ok, aeso_syntax:expr()} | {error, [aeso_errors:error()]}.
to_sophia_value(ContractString, Fun, ResType, Data) ->
    to_sophia_value(ContractString, Fun, ResType, Data, []).
-spec to_sophia_value(string(), string(), ok | error | revert, binary(), options()) ->
        {ok, aeso_syntax:expr()} | {error, [aeso_errors:error()]}.
to_sophia_value(_, _, error, Err, _Options) ->
    {ok, {app, [], {id, [], "error"}, [{string, [], Err}]}};
to_sophia_value(_, _, revert, Data, _Options) ->
    try aeso_vm_decode:from_fate({id, [], "string"}, aeb_fate_encoding:deserialize(Data)) of
        Err ->
            {ok, {app, [], {id, [], "abort"}, [Err]}}
    catch _:_ ->
            Msg = "Could not deserialize the revert message",
            {error, [aeso_errors:new(data_error, Msg)]}
    end;
to_sophia_value(ContractString, FunName, ok, Data, Options0) ->
    Options = [no_code | Options0],
    try
        Code = string_to_code(ContractString, Options),
        #{ unfolded_typed_ast := TypedAst, type_env  := TypeEnv} = Code,
        {ok, _, Type0} = get_decode_type(FunName, TypedAst),
        Type   = aeso_ast_infer_types:unfold_types_in_type(TypeEnv, Type0, [unfold_record_types, unfold_variant_types]),

        fate_data_to_sophia_value(Type0, Type, Data)
    catch
        throw:{error, Errors} -> {error, Errors}
    end.

fate_data_to_sophia_value(Type, UnfoldedType, FateData) ->
    try
        {ok, aeso_vm_decode:from_fate(UnfoldedType, aeb_fate_encoding:deserialize(FateData))}
    catch throw:cannot_translate_to_sophia ->
            Type1 = prettypr:format(aeso_pretty:type(Type)),
            Msg = io_lib:format("Cannot translate FATE value ~p\n  of Sophia type ~s",
                                [aeb_fate_encoding:deserialize(FateData), Type1]),
            {error, [aeso_errors:new(data_error, Msg)]};
          _:_ ->
            Type1 = prettypr:format(aeso_pretty:type(Type)),
            Msg = io_lib:format("Failed to decode binary as type ~s", [Type1]),
            {error, [aeso_errors:new(data_error, Msg)]}
    end.

-spec create_calldata(string(), string(), [string()]) ->
          {ok, binary()} | {error, [aeso_errors:error()]}.
create_calldata(Code, Fun, Args) ->
    create_calldata(Code, Fun, Args, []).
-spec create_calldata(string(), string(), [string()], [{atom(), any()}]) ->
                             {ok, binary()} | {error, [aeso_errors:error()]}.
create_calldata(Code, Fun, Args, Options0) ->
    Options = [no_code | Options0],
    case check_call(Code, Fun, Args, Options) of
        {ok, FunName, FateArgs} ->
            aeb_fate_abi:create_calldata(FunName, FateArgs);
        {error, _} = Err -> Err
    end.

-spec decode_calldata(string(), string(), binary()) ->
          {ok, [aeso_syntax:type()], [aeso_syntax:expr()]}
        | {error, [aeso_errors:error()]}.
decode_calldata(ContractString, FunName, Calldata) ->
    decode_calldata(ContractString, FunName, Calldata, []).
-spec decode_calldata(string(), string(), binary(), options()) ->
          {ok, [aeso_syntax:type()], [aeso_syntax:expr()]}
        | {error, [aeso_errors:error()]}.
decode_calldata(ContractString, FunName, Calldata, Options0) ->
    Options = [no_code | Options0],
    try
        Code = string_to_code(ContractString, Options),
        #{ unfolded_typed_ast := TypedAst, type_env  := TypeEnv} = Code,

        {ok, Args, _} = get_decode_type(FunName, TypedAst),
        GetType       = fun({typed, _, _, T}) -> T; (T) -> T end,
        ArgTypes      = lists:map(GetType, Args),
        Type0         = {tuple_t, [], ArgTypes},
        %% user defined data types such as variants needed to match against
        Type          = aeso_ast_infer_types:unfold_types_in_type(TypeEnv, Type0, [unfold_record_types, unfold_variant_types]),
        case aeb_fate_abi:decode_calldata(FunName, Calldata) of
            {ok, FateArgs} ->
                try
                    {tuple_t, [], ArgTypes1} = Type,
                    AstArgs = [ aeso_vm_decode:from_fate(ArgType, FateArg)
                                || {ArgType, FateArg} <- lists:zip(ArgTypes1, FateArgs)],
                    {ok, ArgTypes, AstArgs}
                catch throw:cannot_translate_to_sophia ->
                        Type0Str = prettypr:format(aeso_pretty:type(Type0)),
                        Msg = io_lib:format("Cannot translate FATE value ~p\n  to Sophia type ~s",
                                            [FateArgs, Type0Str]),
                        {error, [aeso_errors:new(data_error, Msg)]}
                end;
            {error, _} ->
                Msg = io_lib:format("Failed to decode calldata binary", []),
                {error, [aeso_errors:new(data_error, Msg)]}
        end
    catch
        throw:{error, Errors} -> {error, Errors}
    end.

-dialyzer({nowarn_function, get_decode_type/2}).
get_decode_type(FunName, [{Contract, Ann, _, _, Defs}]) when ?IS_CONTRACT_HEAD(Contract) ->
    GetType = fun({letfun, _, {id, _, Name}, Args, Ret, _})               when Name == FunName -> [{Args, Ret}];
                 ({fun_decl, _, {id, _, Name}, {fun_t, _, _, Args, Ret}}) when Name == FunName -> [{Args, Ret}];
                 (_) -> [] end,
    case lists:flatmap(GetType, Defs) of
        [{Args, Ret}] -> {ok, Args, Ret};
        []            ->
            case FunName of
                "init" -> {ok, [], {tuple_t, [], []}};
                 _ ->
                    Msg = io_lib:format("Function '~s' is missing in contract", [FunName]),
                    Pos = aeso_errors:pos(Ann),
                    aeso_errors:throw(aeso_errors:new(data_error, Pos, Msg))
            end
    end;
get_decode_type(FunName, [_ | Contracts]) ->
    %% The __decode should be in the final contract
    get_decode_type(FunName, Contracts).

pp_sophia_code(C, Opts)->  pp(C, Opts, pp_sophia_code, fun(Code) ->
                                io:format("~s\n", [prettypr:format(aeso_pretty:decls(Code))])
                            end).
pp_ast(C, Opts)      ->  pp(C, Opts, pp_ast, fun aeso_ast:pp/1).
pp_typed_ast(C, Opts)->  pp(C, Opts, pp_typed_ast, fun aeso_ast:pp_typed/1).

pp_assembler(C, Opts) ->  pp(C, Opts, pp_assembler, fun(Asm) -> io:format("~s", [aeb_fate_asm:pp(Asm)]) end).

pp(Code, Options, Option, PPFun) ->
    case proplists:lookup(Option, Options) of
        {Option1, true} when Option1 =:= Option ->
            PPFun(Code);
        none ->
            ok
    end.

%% -- Byte code validation ---------------------------------------------------

-define(protect(Tag, Code), fun() -> try Code catch _:Err1 -> throw({Tag, Err1}) end end()).

-spec validate_byte_code(map(), string(), options()) -> ok | {error, [aeso_errors:error()]}.
validate_byte_code(#{ byte_code := ByteCode, payable := Payable }, Source, Options) ->
    Fail = fun(Err) -> {error, [aeso_errors:new(data_error, Err)]} end,
    try
        FCode1 = ?protect(deserialize, aeb_fate_code:strip_init_function(aeb_fate_code:deserialize(ByteCode))),
        {FCode2, SrcPayable} =
            ?protect(compile,
                     begin
                         {ok, #{ byte_code := SrcByteCode, payable := SrcPayable }} =
                             from_string1(Source, Options),
                         FCode = aeb_fate_code:deserialize(SrcByteCode),
                         {aeb_fate_code:strip_init_function(FCode), SrcPayable}
                     end),
        case compare_fate_code(FCode1, FCode2) of
            ok when SrcPayable /= Payable ->
                Not = fun(true) -> ""; (false) -> " not" end,
                Fail(io_lib:format("Byte code contract is~s payable, but source code contract is~s.\n",
                                   [Not(Payable), Not(SrcPayable)]));
            ok           -> ok;
            {error, Why} -> Fail(io_lib:format("Byte code does not match source code.\n~s", [Why]))
        end
    catch
        throw:{deserialize, _}         -> Fail("Invalid byte code");
        throw:{compile, {error, Errs}} -> {error, Errs}
    end.

compare_fate_code(FCode1, FCode2) ->
    Funs1 = aeb_fate_code:functions(FCode1),
    Funs2 = aeb_fate_code:functions(FCode2),
    Syms1 = aeb_fate_code:symbols(FCode1),
    Syms2 = aeb_fate_code:symbols(FCode2),
    FunHashes1 = maps:keys(Funs1),
    FunHashes2 = maps:keys(Funs2),
    case FunHashes1 == FunHashes2 of
        false ->
            InByteCode   = [ binary_to_list(maps:get(H, Syms1)) || H <- FunHashes1 -- FunHashes2 ],
            InSourceCode = [ binary_to_list(maps:get(H, Syms2)) || H <- FunHashes2 -- FunHashes1 ],
            Msg = [ io_lib:format("- Functions in the byte code but not in the source code:\n"
                                  "    ~s\n", [string:join(InByteCode, ", ")]) || InByteCode /= [] ] ++
                  [ io_lib:format("- Functions in the source code but not in the byte code:\n"
                                  "    ~s\n", [string:join(InSourceCode, ", ")]) || InSourceCode /= [] ],
            {error, Msg};
        true ->
            case lists:append([ compare_fate_fun(maps:get(H, Syms1), Fun1, Fun2)
                                || {{H, Fun1}, {_, Fun2}} <- lists:zip(maps:to_list(Funs1),
                                                                       maps:to_list(Funs2)) ]) of
                [] -> ok;
                Errs -> {error, Errs}
            end
    end.

compare_fate_fun(_Name, Fun, Fun) -> [];
compare_fate_fun(Name, {Attr, Type, _}, {Attr, Type, _}) ->
    [io_lib:format("- The implementation of the function ~s is different.\n", [Name])];
compare_fate_fun(Name, {Attr1, Type, _}, {Attr2, Type, _}) ->
    [io_lib:format("- The attributes of the function ~s differ:\n"
                   "    Byte code:   ~s\n"
                   "    Source code: ~s\n",
                   [Name, string:join([ atom_to_list(A) || A <- Attr1 ], ", "),
                          string:join([ atom_to_list(A) || A <- Attr2 ], ", ")])];
compare_fate_fun(Name, {_, Type1, _}, {_, Type2, _}) ->
    [io_lib:format("- The type of the function ~s differs:\n"
                   "    Byte code:   ~s\n"
                   "    Source code: ~s\n",
                   [Name, pp_fate_sig(Type1), pp_fate_sig(Type2)])].

pp_fate_sig({[Arg], Res}) ->
    io_lib:format("~s => ~s", [pp_fate_type(Arg), pp_fate_type(Res)]);
pp_fate_sig({Args, Res}) ->
    io_lib:format("(~s) => ~s", [string:join([pp_fate_type(Arg) || Arg <- Args], ", "), pp_fate_type(Res)]).

pp_fate_type(T) -> io_lib:format("~w", [T]).

%% -------------------------------------------------------------------

-spec parse(string(), aeso_compiler:options()) -> none() | aeso_syntax:ast().
parse(Text, Options) ->
    parse(Text, sets:new(), Options).

-spec parse(string(), sets:set(), aeso_compiler:options()) -> none() | aeso_syntax:ast().
parse(Text, Included, Options) ->
    aeso_parser:string(Text, Included, Options).

read_contract(Name) ->
    file:read_file(Name).
