%%%-------------------------------------------------------------------
%%% @author Ulf Norell
%%% @copyright (C) 2019, Aeternity Anstalt
%%% @doc
%%%     Formatting of code generation errors.
%%% @end
%%%
%%%-------------------------------------------------------------------
-module(aeso_code_errors).

-export([format/1, pos/1]).

format({invalid_aens_resolve_type, Ann, T}) ->
    Msg = io_lib:format("Invalid return type of AENS.resolve:\n"
                        "~s\n"
                        "It must be a string or a pubkey type (address, oracle, etc).",
                        [pp_type(2, T)]),
    mk_err(pos(Ann), Msg);
format({invalid_oracle_type, Why, What, Ann, Type}) ->
    WhyS = case Why of higher_order -> "higher-order (contain function types)";
                       polymorphic  -> "polymorphic (contain type variables)" end,
    Msg = io_lib:format("Invalid oracle type\n~s", [pp_type(2, Type)]),
    Cxt = io_lib:format("The ~s type must not be ~s.", [What, WhyS]),
    mk_err(pos(Ann), Msg, Cxt);
format({var_args_not_set, Expr}) ->
    mk_err( pos(Expr), "Could not deduce type of variable arguments list"
          , "When compiling " ++ pp_expr(Expr)
          );

format(Err) ->
    mk_err(aeso_errors:pos(0, 0), io_lib:format("Unknown error: ~p\n", [Err])).

pos(Ann) ->
    File = aeso_syntax:get_ann(file, Ann, no_file),
    Line = aeso_syntax:get_ann(line, Ann, 0),
    Col  = aeso_syntax:get_ann(col, Ann, 0),
    aeso_errors:pos(File, Line, Col).

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

