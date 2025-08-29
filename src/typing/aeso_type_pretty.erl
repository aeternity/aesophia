%%%-------------------------------------------------------------------
%%% @copyright (C) 2025, Aeternity Anstalt
%%% @doc Pretty printing helpers for Sophia typing/errors.
%%% @end
%%%-------------------------------------------------------------------
-module(aeso_type_pretty).

-export([
    pp_expr/1,
    pp_expr/2,
    pp_type/1,
    pp_type/2,
    pp_typed/3,
    pp/1,
    pp_context/1,
    pp_loc/1
]).

%% -------------------------------------------------------------------
%% Public API
%% -------------------------------------------------------------------

pp_expr(Expr) ->
    pp_expr("", Expr).

pp_expr(Label, Expr) ->
    prettypr:format(prettypr:beside(prettypr:text(Label), aeso_pretty:expr(Expr, [show_generated])), 80, 80).

pp_type(Type) ->
    pp_type("", Type).

pp_type(Label, Type) ->
    prettypr:format(prettypr:beside(prettypr:text(Label), aeso_pretty:type(Type, [show_generated])), 80, 80).

pp_typed(Label, E, T = {type_sig, _, _, _, _, _}) ->
    pp_typed(Label, E, typesig_to_fun_t(T));
pp_typed(Label, {typed, _, Expr, _}, Type) ->
    pp_typed(Label, Expr, Type);
pp_typed(Label, Expr, Type) ->
    pp_expr(Label, {typed, [], Expr, Type}).

pp(T = {type_sig, _, _, _, _, _}) ->
    pp(typesig_to_fun_t(T));
pp([]) ->
    "";
pp([T]) ->
    pp(T);
pp([T|Ts]) ->
    [pp(T), ", "|pp(Ts)];
pp({id, _, Name}) ->
    Name;
pp({qid, _, Name}) ->
    string:join(Name, ".");
pp({con, _, Name}) ->
    Name;
pp({qcon, _, Name}) ->
    string:join(Name, ".");
pp({uvar, _, Ref}) ->
    ["?u" | integer_to_list(erlang:phash2(Ref, 16384)) ];
pp({tvar, _, Name}) ->
    Name;
pp({if_t, _, Id, Then, Else}) ->
    ["if(", pp([Id, Then, Else]), ")"]; 
pp({tuple_t, _, []}) ->
    "unit";
pp({tuple_t, _, Cpts}) ->
    ["(", string:join(lists:map(fun pp/1, Cpts), " * "), ")"]; 
pp({bytes_t, _, any}) -> "bytes()";
pp({bytes_t, _, Len}) ->
    ["bytes(", integer_to_list(Len), ")"]; 
pp({app_t, _, T, []}) ->
    pp(T);
pp({app_t, _, Type, Args}) ->
    [pp(Type), "(", pp(Args), ")"]; 
pp({named_arg_t, _, Name, Type, _Default}) ->
    [pp(Name), " : ", pp(Type)];
pp({fun_t, _, Named = {uvar, _, _}, As, B}) ->
    ["(", pp(Named), " | ", pp(As), ") => ", pp(B)];
pp({fun_t, _, Named, As, B}) when is_list(Named) ->
    ["(", pp(Named ++ As), ") => ", pp(B)];
pp(Other) ->
    io_lib:format("~p", [Other]).

pp_context([{fun_name, Id}]) -> ["a call to ", pp(Id)];
pp_context([result | Ctx]) -> ["the result of ", pp_context(Ctx)];
pp_context([{arg, N} | Ctx]) ->
  Cnt = fun(1) -> "first";
           (2) -> "second";
           (3) -> "third";
           (I) -> io_lib:format("~pth", [I])
        end,
  ["the ", Cnt(N), " argument of ", pp_context(Ctx)];
pp_context(none) -> "unknown context".

pp_loc(T) ->
    {File, IncludeType, Line, Col} = loc(T),
    case {Line, Col} of
        {0, 0} -> "(builtin location)";
        _      -> case IncludeType of
                      none -> io_lib:format("line ~p, column ~p", [Line, Col]);
                      _    -> io_lib:format("line ~p, column ~p in ~s", [Line, Col, File])
                  end
    end.

%% -------------------------------------------------------------------
%% Internal helpers
%% -------------------------------------------------------------------

typesig_to_fun_t({type_sig, Ann, _Constr, Named, Args, Res}) ->
    {fun_t, Ann, Named, Args, Res}.

src_file(T)      -> aeso_syntax:get_ann(file, T, no_file).
include_type(T)  -> aeso_syntax:get_ann(include_type, T, none).
line_number(T)   -> aeso_syntax:get_ann(line, T, 0).
column_number(T) -> aeso_syntax:get_ann(col, T, 0).

loc(T) ->
    {src_file(T), include_type(T), line_number(T), column_number(T)}.


