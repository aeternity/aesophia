-module(aeso_smt).

-compile([export_all]).

-type formula() :: {var, string()}
                 | {param, string()}
                 | {int, integer()}
                 | {list, [formula()]}
                 | {app, string(), [formula()]}
                   .

-define(TIMEOUT, 10000).

start_z3() ->
    PortOpts = [exit_status, {line, 100000}],
    Port = open_port({spawn, "z3 -in -t:" ++ integer_to_list(?TIMEOUT)}, PortOpts),
    persistent_term:put(z3_connection, Port),
    send_z3_success({app, "set-option", [{param, "print-success"}, {var, "true"}]}),
    ok.

stop_z3() ->
    port_close(persistent_term:get(z3_connection)),
    persistent_term:erase(z3_connection).

get_z3() ->
    Z3 = persistent_term:get(z3_connection, undefined),
    if Z3 =:= undefined -> throw(z3_disconnected);
       true -> ok
    end,
    Z3.

send_z3(Query) ->
    Z3 = get_z3(),
    QueryStr = pp_formula(Query),
    %% io:format("~s\n", [QueryStr]),
    port_command(Z3, binary:list_to_bin(QueryStr ++ "\n")).

check_sat() ->
    send_z3({app, "check-sat", []}),
    receive
        {_, {data, {eol, Resp}}} ->
            %% io:format("Z3: " ++ Resp ++ "\n"),
            case string:trim(Resp) of
                "sat"   -> true;
                "unsat" -> false;
                X -> throw({smt_error, X})
            end
    after ?TIMEOUT * 2 -> {error, timeout}
    end.

send_z3_success(Query) ->
    send_z3(Query),
    receive
        {_, {data, {eol, Resp}}} ->
            %% io:format("Z3: " ++ Resp ++ "\n"),
            case string:trim(Resp) of
                "success" -> success;
                X         -> error({smt_error, X})
            end
    after 5000 -> {error, timeout}
    end.

assert(Form) ->
    send_z3_success({app, "assert", [Form]}).

declare_const(Var, Type) ->
    send_z3_success({app, "declare-const", [Var, Type]}).

push() ->
    send_z3_success({app, "push", []}).
pop() ->
    send_z3_success({app, "pop", []}).
scoped(Fun) ->
    push(),
    R = Fun(),
    pop(),
    R.


pp_formula({var, Name}) -> Name;
pp_formula({param, Name}) -> [$:, Name];
pp_formula({int, I}) -> integer_to_list(I);
pp_formula({app, Fun, Args}) ->
    io_lib:format("(~s)", [pp_formulae([{var, Fun}|Args])]);
pp_formula({list, Xs}) ->
    io_lib:format("(~s)", [pp_formulae(Xs)]).


pp_formulae([]) ->
    "";
pp_formulae([H]) ->
    pp_formula(H);
pp_formulae([H|T]) ->
    io_lib:format("~s ~s", [pp_formula(H), pp_formulae(T)]).
