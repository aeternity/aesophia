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
format({parameterized_state, Decl}) ->
    Msg = "The state type cannot be parameterized.\n",
    mk_err(pos(Decl), Msg);
format({parameterized_event, Decl}) ->
    Msg = "The event type cannot be parameterized.\n",
    mk_err(pos(Decl), Msg);
format({entrypoint_argument_must_have_monomorphic_type, Ann, {id, _, Name}, X, T}) ->
    Msg = io_lib:format("The argument\n~s\nof entrypoint '~s' does not have a monomorphic type.\n",
                        [pp_typed(X, T), Name]),
    Cxt = "Use the FATE backend if you want polymorphic entrypoints.",
    mk_err(pos(Ann), Msg, Cxt);
format({cant_compare_type_aevm, Ann, Op, Type}) ->
    StringAndTuple = [ "- type string\n"
                       "- tuple or record of word type\n" || lists:member(Op, ['==', '!=']) ],
    Msg = io_lib:format("Cannot compare values of type\n"
                        "~s\n"
                        "The AEVM only supports '~s' on values of\n"
                        "- word type (int, bool, bits, address, oracle(_, _), etc)\n"
                        "~s"
                        "Use FATE if you need to compare arbitrary types.\n",
                        [pp_type(2, Type), Op, StringAndTuple]),
    mk_err(pos(Ann), Msg);
format({invalid_aens_resolve_type, Ann, T}) ->
    Msg = io_lib:format("Invalid return type of AENS.resolve:\n"
                        "~s\n"
                        "It must be a string or a pubkey type (address, oracle, etc).\n",
                        [pp_type(2, T)]),
    mk_err(pos(Ann), Msg);
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
    prettypr:format(aeso_pretty:expr(E)).

pp_type(N, T) ->
    prettypr:format(prettypr:nest(N, aeso_pretty:type(T))).

mk_err(Pos, Msg) ->
    aeso_errors:new(code_error, Pos, lists:flatten(Msg)).

mk_err(Pos, Msg, Cxt) ->
    aeso_errors:new(code_error, Pos, lists:flatten(Msg), lists:flatten(Cxt)).

