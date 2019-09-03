%%%-------------------------------------------------------------------
%%% @author Ulf Norell
%%% @copyright (C) 2019, Aeternity Anstalt
%%% @doc
%%%     Formatting of code generation errors.
%%% @end
%%%
%%%-------------------------------------------------------------------
-module(aeso_code_errors).

-export([format/1]).

format({last_declaration_must_be_contract, Decl = {namespace, _, {con, _, C}, _}}) ->
    Msg = io_lib:format("Expected a contract as the last declaration instead of the namespace '~s'\n",
                        [C]),
    mk_err(pos(Decl), Msg);
format({missing_init_function, Con}) ->
    Msg = io_lib:format("Missing init function for the contract '~s'.\n", [pp_expr(Con)]),
    Cxt = "The 'init' function can only be omitted if the state type is 'unit'.\n",
    mk_err(pos(Con), Msg, Cxt);
format({missing_definition, Id}) ->
    Msg = io_lib:format("Missing definition of function '~s'.\n", [pp_expr(Id)]),
    mk_err(pos(Id), Msg);
format({parameterized_state, Decl}) ->
    Msg = "The state type cannot be parameterized.\n",
    mk_err(pos(Decl), Msg);
format({parameterized_event, Decl}) ->
    Msg = "The event type cannot be parameterized.\n",
    mk_err(pos(Decl), Msg);
format({invalid_entrypoint, Why, Ann, {id, _, Name}, Thing}) ->
    What = case Why of higher_order -> "higher-order (contains function types)";
                       polymorphic  -> "polymorphic (contains type variables)" end,
    ThingS = case Thing of
                 {argument, X, T} -> io_lib:format("argument\n~s\n", [pp_typed(X, T)]);
                 {result, T}      -> io_lib:format("return type\n~s\n", [pp_type(2, T)])
             end,
    Bad = case Thing of
              {argument, _, _} -> io_lib:format("has a ~s type", [What]);
              {result, _}      -> io_lib:format("is ~s", [What])
          end,
    Msg = io_lib:format("The ~sof entrypoint '~s' ~s.\n",
                        [ThingS, Name, Bad]),
    case Why of
        polymorphic  -> mk_err(pos(Ann), Msg, "Use the FATE backend if you want polymorphic entrypoints.\n");
        higher_order -> mk_err(pos(Ann), Msg)
    end;
format({cant_compare_type_aevm, Ann, Op, Type}) ->
    StringAndTuple = [ "- type string\n"
                       "- tuple or record of word type\n" || lists:member(Op, ['==', '!=']) ],
    Msg = io_lib:format("Cannot compare values of type\n"
                        "~s\n"
                        "The AEVM only supports '~s' on values of\n"
                        "- word type (int, bool, bits, address, oracle(_, _), etc)\n"
                        "~s",
                        [pp_type(2, Type), Op, StringAndTuple]),
    Cxt = "Use FATE if you need to compare arbitrary types.\n",
    mk_err(pos(Ann), Msg, Cxt);
format({invalid_aens_resolve_type, Ann, T}) ->
    Msg = io_lib:format("Invalid return type of AENS.resolve:\n"
                        "~s\n"
                        "It must be a string or a pubkey type (address, oracle, etc).\n",
                        [pp_type(2, T)]),
    mk_err(pos(Ann), Msg);
format({unapplied_contract_call, Contract}) ->
    Msg = io_lib:format("The AEVM does not support unapplied contract call to\n"
                        "~s\n", [pp_expr(2, Contract)]),
    Cxt = "Use FATE if you need this.\n",
    mk_err(pos(Contract), Msg, Cxt);
format({invalid_map_key_type, Why, Ann, Type}) ->
    Msg = io_lib:format("Invalid map key type\n~s\n", [pp_type(2, Type)]),
    Cxt = case Why of
             polymorphic -> "Map keys cannot be polymorphic in the AEVM. Use FATE if you need this.\n";
             function    -> "Map keys cannot be higher-order.\n"
          end,
    mk_err(pos(Ann), Msg, Cxt);
format({invalid_oracle_type, Why, What, Ann, Type}) ->
    WhyS = case Why of higher_order -> "higher-order (contain function types)";
                       polymorphic  -> "polymorphic (contain type variables)" end,
    Msg = io_lib:format("Invalid oracle type\n~s\n", [pp_type(2, Type)]),
    Cxt = io_lib:format("The ~s type must not be ~s.\n", [What, WhyS]),
    mk_err(pos(Ann), Msg, Cxt);
format({higher_order_state, {type_def, Ann, _, _, State}}) ->
    Msg = io_lib:format("Invalid state type\n~s\n", [pp_type(2, State)]),
    Cxt = "The state cannot contain functions in the AEVM. Use FATE if you need this.\n",
    mk_err(pos(Ann), Msg, Cxt);

format(Err) ->
    mk_err(aeso_errors:pos(0, 0), io_lib:format("Unknown error: ~p\n", [Err])).

pos(Ann) ->
    File = aeso_syntax:get_ann(file, Ann, no_file),
    Line = aeso_syntax:get_ann(line, Ann, 0),
    Col  = aeso_syntax:get_ann(col, Ann, 0),
    aeso_errors:pos(File, Line, Col).

pp_typed(E, T) ->
    prettypr:format(prettypr:nest(2,
    lists:foldr(fun prettypr:beside/2, prettypr:empty(),
                [aeso_pretty:expr(E), prettypr:text(" : "),
                 aeso_pretty:type(T)]))).

pp_expr(E) ->
    pp_expr(0, E).

pp_expr(N, E) ->
    prettypr:format(prettypr:nest(N, aeso_pretty:expr(E))).

pp_type(N, T) ->
    prettypr:format(prettypr:nest(N, aeso_pretty:type(T))).

mk_err(Pos, Msg) ->
    aeso_errors:new(code_error, Pos, lists:flatten(Msg)).

mk_err(Pos, Msg, Cxt) ->
    aeso_errors:new(code_error, Pos, lists:flatten(Msg), lists:flatten(Cxt)).

