%%%-------------------------------------------------------------------
%%% @doc Pretty-printer for Fcode and Fexpr terms.
%%%      Extracted from `aeso_ast_to_fcode` to reduce module size and
%%%      improve maintainability. No semantic changes.
%%%-------------------------------------------------------------------
-module(aeso_fcode_pp).

-export([format_fcode/1, format_fexpr/1]).

%% Types are referenced from aeso_ast_to_fcode to avoid duplication
-compile({nowarn_unused_function, [pp_text/1, pp_int/1]}).

%% API
-spec format_fcode(aeso_ast_to_fcode:fcode()) -> string().
format_fcode(#{ functions := Funs }) ->
    prettypr:format(format_funs(Funs)).

-spec format_fexpr(aeso_ast_to_fcode:fexpr()) -> string().
format_fexpr(E) ->
    prettypr:format(pp_fexpr(E)).

%% Internal pretty helpers
-spec format_funs(aeso_ast_to_fcode:functions()) -> prettypr:document().
format_funs(Funs) ->
    pp_above([ pp_fun(Name, Def) || {Name, Def} <- maps:to_list(Funs) ]).

-spec pp_fun(aeso_ast_to_fcode:fun_name(), aeso_ast_to_fcode:fun_def()) -> prettypr:document().
pp_fun(Name, #{ args := Args, return := Return, body := Body }) ->
    PPArg = fun({X, T}) -> pp_beside([pp_text(X), pp_text(" : "), pp_ftype(T)]) end,
    pp_above(pp_beside([pp_text("function "), pp_fun_name(Name),
               pp_parens(pp_par(pp_punctuate(pp_text(","), [PPArg(Arg) || Arg <- Args]))),
               pp_text(" : "), pp_ftype(Return), pp_text(" =")]),
             prettypr:nest(2, pp_fexpr(Body))).

-spec pp_fun_name(aeso_ast_to_fcode:fun_name()) -> prettypr:document().
pp_fun_name(event)           -> pp_text(event);
pp_fun_name({entrypoint, E}) -> pp_text(binary_to_list(E));
pp_fun_name({local_fun, Q})  -> pp_text(string:join(Q, ".")).

-spec pp_text(binary() | string() | atom() | integer()) -> prettypr:document().
pp_text(<<>>) -> prettypr:text("\"\"");
pp_text(Bin) when is_binary(Bin) -> prettypr:text(lists:flatten(io_lib:format("~p", [binary_to_list(Bin)])));
pp_text(S) when is_list(S) -> prettypr:text(lists:concat([S]));
pp_text(A) when is_atom(A) -> prettypr:text(atom_to_list(A));
pp_text(N) when is_integer(N) -> prettypr:text(integer_to_list(N)).

-spec pp_int(integer()) -> prettypr:document().
pp_int(I) -> prettypr:text(integer_to_list(I)).

-spec pp_beside([prettypr:document()]) -> prettypr:document().
pp_beside([])       -> prettypr:empty();
pp_beside([X])      -> X;
pp_beside([X | Xs]) -> pp_beside(X, pp_beside(Xs)).

-spec pp_beside(prettypr:document(), prettypr:document()) -> prettypr:document().
pp_beside(A, B) -> prettypr:beside(A, B).

-spec pp_above([prettypr:document()]) -> prettypr:document().
pp_above([])       -> prettypr:empty();
pp_above([X])      -> X;
pp_above([X | Xs]) -> pp_above(X, pp_above(Xs)).

-spec pp_above(prettypr:document(), prettypr:document()) -> prettypr:document().
pp_above(A, B) -> prettypr:above(A, B).

-spec pp_parens(prettypr:document()) -> prettypr:document().
pp_parens(Doc) -> pp_beside([pp_text("("), Doc, pp_text(")")]).

-spec pp_braces(prettypr:document()) -> prettypr:document().
pp_braces(Doc) -> pp_beside([pp_text("{"), Doc, pp_text("}")]).

-spec pp_punctuate(prettypr:document(), [prettypr:document()]) -> [prettypr:document()].
pp_punctuate(_Sep, [])      -> [];
pp_punctuate(_Sep, [X])     -> [X];
pp_punctuate(Sep, [X | Xs]) -> [pp_beside(X, Sep) | pp_punctuate(Sep, Xs)].

-spec pp_par([prettypr:document()]) -> prettypr:document().
pp_par([]) -> prettypr:empty();
pp_par(Xs) -> prettypr:par(Xs).

-spec pp_fexpr(aeso_ast_to_fcode:fexpr()) -> prettypr:document().
pp_fexpr({lit, _, {typerep, T}}) ->
    pp_ftype(T);
pp_fexpr({lit, _, {contract_code, Contract}}) ->
    pp_beside(pp_text("contract "), pp_text(Contract));
pp_fexpr({lit, _, {Tag, Lit}}) ->
    aeso_pretty:expr({Tag, [], Lit});
pp_fexpr({nil, _}) ->
    pp_text("[]");
pp_fexpr({var, _, X}) -> pp_text(X);
pp_fexpr({def, Fun}) -> pp_fun_name(Fun);
pp_fexpr({def_u, _, Fun, Ar}) ->
    pp_beside([pp_fun_name(Fun), pp_text("/"), pp_int(Ar)]);
pp_fexpr({def, _, Fun, Args}) ->
    pp_call(pp_fun_name(Fun), Args);
pp_fexpr({con, _, _, I, []}) ->
    pp_beside(pp_text("C"), pp_int(I));
pp_fexpr({con, FAnn, _, I, Es}) ->
    pp_beside(pp_fexpr({con, FAnn, [], I, []}),
              pp_fexpr({tuple, FAnn, Es}));
pp_fexpr({tuple, _, Es}) ->
    pp_parens(pp_par(pp_punctuate(pp_text(","), [pp_fexpr(E) || E <- Es])));
pp_fexpr({proj, _, E, I}) ->
    pp_beside([pp_fexpr(E), pp_text("."), pp_int(I)]);
pp_fexpr({lam, FAnn, Xs, A}) ->
    pp_par([pp_fexpr({tuple, FAnn, [{var, FAnn, X} || X <- Xs]}), pp_text("=>"),
            prettypr:nest(2, pp_fexpr(A))]);
pp_fexpr({closure, _, Fun, ClEnv}) ->
    FVs = case ClEnv of
              {tuple, _, Xs} -> Xs;
              {var, _, _}    -> [ClEnv]
          end,
    pp_call(pp_text("__CLOSURE__"), [{def, Fun} | FVs]);
pp_fexpr({set_proj, _, E, I, A}) ->
    pp_beside(pp_fexpr(E), pp_braces(pp_beside([pp_int(I), pp_text(" = "), pp_fexpr(A)])));
pp_fexpr({op, _, Op, [A, B] = Args}) ->
    case is_infix(Op) of
        false -> pp_call(pp_text(Op), Args);
        true  -> pp_parens(pp_par([pp_fexpr(A), pp_text(Op), pp_fexpr(B)]))
    end;
pp_fexpr({op, _, Op, [A] = Args}) ->
    case is_infix(Op) of
        false -> pp_call(pp_text(Op), Args);
        true  -> pp_parens(pp_par([pp_text(Op), pp_fexpr(A)]))
    end;
pp_fexpr({op, FAnn, Op, As}) ->
    pp_beside(pp_text(Op), pp_fexpr({tuple, FAnn, As}));
pp_fexpr({'let', _, _, _, _} = Expr) ->
    Lets = fun Lets({'let', _, Y, C, D}) ->
                        {Ls, E} = Lets(D),
                        {[{Y, C} | Ls], E};
               Lets(E) -> {[], E} end,
    {Ls, Body} = Lets(Expr),
    pp_parens(
      pp_par(
        [ pp_beside([ pp_text("let "),
                      pp_above([ pp_par([pp_text(X), pp_text("="), prettypr:nest(2, pp_fexpr(A))]) || {X, A} <- Ls ]),
                      pp_text(" in ") ]),
          pp_fexpr(Body) ]));
pp_fexpr({builtin_u, _, B, N}) ->
    pp_beside([pp_text(B), pp_text("/"), pp_text(N)]);
pp_fexpr({builtin_u, FAnn, B, N, TypeArgs}) ->
    pp_beside([pp_text(B), pp_text("@"), pp_fexpr({tuple, FAnn, TypeArgs}), pp_text("/"), pp_text(N)]);
pp_fexpr({builtin, _, B, As}) ->
    pp_call(pp_text(B), As);
pp_fexpr({remote_u, _, ArgsT, RetT, Ct, Fun}) ->
    pp_beside([pp_fexpr(Ct), pp_text("."), pp_fun_name(Fun), pp_text(" : "), pp_ftype({function, ArgsT, RetT})]);
pp_fexpr({remote, _, ArgsT, RetT, Ct, Fun, As}) ->
    pp_call(pp_parens(pp_beside([pp_fexpr(Ct), pp_text("."), pp_fun_name(Fun), pp_text(" : "), pp_ftype({function, ArgsT, RetT})])), As);
pp_fexpr({funcall, _, Fun, As}) ->
    pp_call(pp_fexpr(Fun), As);
pp_fexpr({set_state, FAnn, R, A}) ->
    pp_call(pp_text("set_state"), [{lit, FAnn, {int, R}}, A]);
pp_fexpr({get_state, FAnn, R}) ->
    pp_call(pp_text("get_state"), [{lit, FAnn, {int, R}}]);
pp_fexpr({switch, _, Split}) -> pp_split(Split).

-spec pp_call(prettypr:document(), [aeso_ast_to_fcode:fexpr()]) -> prettypr:document().
pp_call(Fun, Args) ->
    pp_beside(Fun, pp_fexpr({tuple, [], Args})).

-spec pp_call_t(string(), [aeso_ast_to_fcode:ftype()]) -> prettypr:document().
pp_call_t(Fun, Args) ->
    pp_beside(pp_text(Fun), pp_ftype({tuple, Args})).

-spec pp_ftype(aeso_ast_to_fcode:ftype()) -> any().
pp_ftype(T) when is_atom(T) -> pp_text(T);
pp_ftype(any) -> pp_text("_");
pp_ftype({tvar, X}) -> pp_text(X);
pp_ftype({bytes, N}) -> pp_call(pp_text("bytes"), [{lit, [], {int, N}}]);
pp_ftype({oracle, Q, R}) -> pp_call_t("oracle", [Q, R]);
pp_ftype({tuple, Ts}) ->
    pp_parens(pp_par(pp_punctuate(pp_text(" *"), [pp_ftype(T) || T <- Ts])));
pp_ftype({list, T}) ->
    pp_call_t("list", [T]);
pp_ftype({function, Args, Res}) ->
    pp_par([pp_ftype({tuple, Args}), pp_text("=>"), pp_ftype(Res)]);
pp_ftype({map, Key, Val}) ->
    pp_call_t("map", [Key, Val]);
pp_ftype({variant, Cons}) ->
    pp_par(
    pp_punctuate(pp_text(" |"),
                 [ case Args of
                     [] -> pp_fexpr({con, [], [], I - 1, []});
                     _  -> pp_beside(pp_fexpr({con, [], [], I - 1, []}), pp_ftype({tuple, Args}))
                   end || {I, Args} <- indexed(Cons)]));
pp_ftype([]) ->
    %% NOTE: This could happen with `{typerep, []}` since `[]` is not a ftype().
    %% TODO: It would be better to make sure that `{typerep, []}` does not arrive here.
    pp_text("[]").

-spec pp_split(aeso_ast_to_fcode:fsplit()) -> prettypr:document().
pp_split({nosplit, _, E}) -> pp_fexpr(E);
pp_split({split, Type, X, Alts}) ->
    pp_above([pp_beside([pp_text("switch("), pp_text(X), pp_text(" : "), pp_ftype(Type), pp_text(")")])] ++
             [prettypr:nest(2, pp_case(Alt)) || Alt <- Alts]).

-spec pp_case(aeso_ast_to_fcode:fcase()) -> prettypr:document().
pp_case({'case', Pat, Split}) ->
    prettypr:sep([pp_beside(pp_pat(Pat), pp_text(" =>")),
                  prettypr:nest(2, pp_split(Split))]).

-spec pp_pat(aeso_ast_to_fcode:fsplit_pat()) -> prettypr:document().
pp_pat({tuple, Xs})            -> pp_fexpr({tuple, [], [{var, [], X} || X <- Xs]});
pp_pat({'::', X, Xs})          -> pp_fexpr({op, [], '::', [{var, [], X}, {var, [], Xs}]});
pp_pat({con, As, I, Xs})       -> pp_fexpr({con, [], As, I, [{var, [], X} || X <- Xs]});
pp_pat({var, X})               -> pp_fexpr({var, [], X});
pp_pat(P = {Tag, _}) when Tag == bool; Tag == int; Tag == string
                               -> pp_fexpr({lit, [], P});
pp_pat(nil)                    -> pp_fexpr({nil, []});
pp_pat({assign, X, Y})         -> pp_beside([pp_text(X), pp_text(" = "), pp_text(Y)]).

-spec is_infix(aeso_ast_to_fcode:op()) -> boolean().
is_infix(Op) ->
    C = hd(atom_to_list(Op)),
    C < $a orelse C > $z.

-spec indexed([term()]) -> [{integer(), term()}].
indexed(Xs) ->
    lists:zip(lists:seq(1, length(Xs)), Xs).


