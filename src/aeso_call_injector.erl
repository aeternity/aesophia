%%%-------------------------------------------------------------------
%%% Call injection helpers split from aeso_compiler
%%%-------------------------------------------------------------------
-module(aeso_call_injector).

-export([ check_call/4
        , insert_call_function/4
        , insert_init_function/2
        , get_call_body/2
        , first_none_match/3
        , add_extra_call/3
        ]).

-define(CALL_NAME,   "__call").

check_call(Source, "init" = FunName, Args, Options) ->
    case check_call1(Source, FunName, Args, Options) of
        Err = {error, _} when Args == [] ->
            case check_call1(insert_init_function(Source, Options), FunName, Args, Options) of
                {error, _} -> Err;
                Res        -> Res
            end;
        Res -> Res
    end;
check_call(Source, FunName, Args, Options) ->
    check_call1(Source, FunName, Args, Options).

check_call1(ContractString0, FunName, Args, Options) ->
    case add_extra_call(ContractString0, {call, FunName, Args}, Options) of
        {ok, CallName, Code} ->
            {def, _, _, FcodeArgs} = get_call_body(CallName, Code),
            {ok, FunName, [ aeso_fcode_to_fate:term_to_fate(A) || A <- FcodeArgs ]};
        Err = {error, _} -> Err
    end.

add_extra_call(Contract0, Call, Options) ->
    %% Basic input validation to reduce injection risk when concatenating source
    case validate_insertion_inputs(Call) of
        ok ->
            try
                #{fcode := OrgFcode,
                  fcode_env := #{child_con_env := ChildContracts},
                  ast := Ast} = aeso_compiler:string_to_code(Contract0, Options),
                FateCode = aeso_fcode_to_fate:compile(ChildContracts, OrgFcode, #{}, []),
                SymbolHashes = maps:keys(aeb_fate_code:symbols(FateCode)),
                CallName = first_none_match(?CALL_NAME, SymbolHashes,
                                            lists:seq($1, $9) ++ lists:seq($A, $Z) ++ lists:seq($a, $z)),
                Contract = insert_call_function(Ast, Contract0, CallName, Call),
                {ok, CallName, aeso_compiler:string_to_code(Contract, Options)}
            catch
                throw:{error, E2} -> {error, E2}
            end;
        {error, E1} -> {error, E1}
    end.

get_call_body(CallName, #{fcode := Fcode}) ->
    #{body := Body} = maps:get({entrypoint, list_to_binary(CallName)}, maps:get(functions, Fcode)),
    Body.

first_none_match(_CallName, _Hashes, []) ->
    error(unable_to_find_unique_call_name);
first_none_match(CallName, Hashes, [Char|Chars]) ->
    case not lists:member(aeb_fate_code:symbol_identifier(list_to_binary(CallName)), Hashes) of
        true -> CallName;
        false -> first_none_match(?CALL_NAME++[Char], Hashes, Chars)
    end.

insert_call_function(Ast, Code, Call, {call, FunName, Args}) ->
    Ind = last_contract_indent(Ast),
    lists:flatten([
        Code, "\n\n",
        lists:duplicate(Ind, " "),
        "stateful entrypoint ", Call, "() = ", FunName, "(", string:join(Args, ","), ")\n"
    ]);
insert_call_function(Ast, Code, Call, {value, Type, Value}) ->
    Ind = last_contract_indent(Ast),
    lists:flatten([
        Code, "\n\n",
        lists:duplicate(Ind, " "),
        "entrypoint ", Call, "() : ", Type, " = ", Value, "\n"
    ]);
insert_call_function(Ast, Code, Call, {type, Type}) ->
    Ind = last_contract_indent(Ast),
    lists:flatten([
        Code, "\n\n",
        lists:duplicate(Ind, " "),
        "entrypoint ", Call, "(val : ", Type, ") : ", Type, " = val\n"
    ]).

insert_init_function(Code, Options) ->
    Ast = aeso_compiler:parse(Code, Options),
    Ind = last_contract_indent(Ast),
    lists:flatten([
        Code, "\n\n",
        lists:duplicate(Ind, " "), "entrypoint init() = ()\n"
    ]).

last_contract_indent(Decls) ->
    case lists:last(Decls) of
        {_, _, _, _, [Decl | _]} -> aeso_syntax:get_ann(col, Decl, 1) - 1;
        _                        -> 0
    end.

%% -- Validation helpers ------------------------------------------------------

validate_insertion_inputs({call, FunName, Args}) ->
    case validate_fun_name(FunName) of
        ok -> validate_args(Args);
        {error, E} -> {error, E}
    end;
validate_insertion_inputs({value, Type, Value}) ->
    case ensure_single_line(Type) of
        ok -> ensure_single_line(Value);
        {error, E} -> {error, E}
    end;
validate_insertion_inputs({type, Type}) -> ensure_single_line(Type).

validate_fun_name(Name) when is_list(Name) ->
    case re:run(Name, "^[a-z][A-Za-z0-9_]*$", [{capture, none}]) of
        match   -> ok;
        nomatch -> {error, [aeso_errors:new(data_error, io_lib:format("Invalid function name '~s'", [Name]))]}
    end;
validate_fun_name(_) -> {error, [aeso_errors:new(data_error, "Invalid function name")]}.

validate_args(Args) when is_list(Args) ->
    case lists:all(fun ensure_single_line_ok/1, Args) of
        true  -> ok;
        false -> {error, [aeso_errors:new(data_error, "Arguments must be single-line strings")]}
    end.

ensure_single_line_ok(S) -> ensure_single_line(S) == ok.

ensure_single_line(S) when is_list(S) ->
    case lists:any(fun(C) -> C == $\n orelse C == $\r end, S) of
        true  -> {error, [aeso_errors:new(data_error, "Newlines in inserted code are not allowed")]};
        false -> ok
    end;
ensure_single_line(_) -> {error, [aeso_errors:new(data_error, "Invalid argument type")] }.


