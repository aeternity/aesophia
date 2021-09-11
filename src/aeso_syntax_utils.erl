%%%-------------------------------------------------------------------
%%% @copyright (C) 2018, Aeternity Anstalt
%%% @doc
%%%     Sophia syntax utilities.
%%% @end
%%%-------------------------------------------------------------------
-module(aeso_syntax_utils).

-export([used_ids/1, used_types/2, used/1]).

-record(alg, {zero, plus, scoped}).

-type alg(A) :: #alg{ zero   :: A
                    , plus   :: fun((A, A) -> A)
                    , scoped :: fun((A, A) -> A) }.

-type kind() :: decl | type | bind_type | expr | bind_expr.

-spec fold(alg(A), fun((kind(), _) -> A), kind(), E | [E]) -> A
    when E :: aeso_syntax:decl()
            | aeso_syntax:typedef()
            | aeso_syntax:field_t()
            | aeso_syntax:constructor_t()
            | aeso_syntax:type()
            | aeso_syntax:expr()
            | aeso_syntax:pat()
            | aeso_syntax:arg()
            | aeso_syntax:alt()
            | aeso_syntax:elim()
            | aeso_syntax:arg_expr()
            | aeso_syntax:field(aeso_syntax:expr())
            | aeso_syntax:stmt().
fold(Alg = #alg{zero = Zero, plus = Plus, scoped = Scoped}, Fun, K, X) ->
    Sum  = fun(Xs) -> lists:foldl(Plus, Zero, Xs) end,
    Same = fun(A) -> fold(Alg, Fun, K, A) end,
    Decl = fun(D) -> fold(Alg, Fun, decl, D) end,
    Type = fun(T) -> fold(Alg, Fun, type, T) end,
    Expr = fun(E) -> fold(Alg, Fun, expr, E) end,
    BindExpr = fun(P) -> fold(Alg, Fun, bind_expr, P) end,
    BindType = fun(T) -> fold(Alg, Fun, bind_type, T) end,
    Top = Fun(K, X),
    Rec = case X of
            %% lists (bound things in head scope over tail)
            [A | As]                 -> Scoped(Same(A), Same(As));
            %% decl()
            {contract, _, _, Ds}     -> Decl(Ds);
            {namespace, _, _, Ds}    -> Decl(Ds);
            {type_def, _, I, _, D}   -> Plus(BindType(I), Decl(D));
            {fun_decl, _, _, T}      -> Type(T);
            {letval, _, P, E}        -> Scoped(BindExpr(P), Expr(E));
            {letfun, _, F, Xs, T, E} -> Sum([BindExpr(F), Type(T), Expr(Xs ++ [E])]);
            {fun_clauses, _, _, T, Cs} -> Sum([Type(T) | [Decl(C) || C <- Cs]]);
            %% typedef()
            {alias_t, T}    -> Type(T);
            {record_t, Fs}  -> Type(Fs);
            {variant_t, Cs} -> Type(Cs);
            %% field_t() and constructor_t()
            {field_t, _, _, T}   -> Type(T);
            {constr_t, _, _, Ts} -> Type(Ts);
            %% type()
            {fun_t, _, Named, Args, Ret} -> Type([Named, Args, Ret]);
            {app_t, _, T, Ts}            -> Type([T | Ts]);
            {tuple_t, _, Ts}             -> Type(Ts);
            %% named_arg_t()
            {named_arg_t, _, _, T, E} -> Plus(Type(T), Expr(E));
            %% expr()
            {lam, _, Args, E}      -> Scoped(BindExpr(Args), Expr(E));
            {'if', _, A, B, C}     -> Expr([A, B, C]);
            {switch, _, E, Alts}   -> Expr([E, Alts]);
            {app, _, A, As}        -> Expr([A | As]);
            {proj, _, E, _}        -> Expr(E);
            {tuple, _, As}         -> Expr(As);
            {list, _, As}          -> Expr(As);
            {list_comp, _, Y, []}  -> Expr(Y);
            {list_comp, A, Y, [{comprehension_bind, I, E}|R]} ->
                Plus(Expr(E), Scoped(BindExpr(I), Expr({list_comp, A, Y, R})));
            {list_comp, A, Y, [{comprehension_if, _, E}|R]} ->
                Plus(Expr(E), Expr({list_comp, A, Y, R}));
            {list_comp, A, Y, [D = {letval, _, Pat, _} | R]} ->
                Plus(Decl(D), Scoped(BindExpr(Pat), Expr({list_comp, A, Y, R})));
            {list_comp, A, Y, [D = {letfun, _, F, _, _, _} | R]} ->
                Plus(Decl(D), Scoped(BindExpr(F), Expr({list_comp, A, Y, R})));
            {typed, _, E, T}       -> Plus(Expr(E), Type(T));
            {record, _, Fs}        -> Expr(Fs);
            {record, _, E, Fs}     -> Expr([E | Fs]);
            {map, _, E, Fs}        -> Expr([E | Fs]);
            {map, _, KVs}          -> Sum([Expr([Key, Val]) || {Key, Val} <- KVs]);
            {map_get, _, A, B}     -> Expr([A, B]);
            {map_get, _, A, B, C}  -> Expr([A, B, C]);
            {block, _, Ss}         -> Expr(Ss);
            {letpat, _, X, P}      -> Plus(BindExpr(X), Expr(P));
            %% field()
            {field, _, LV, E}    -> Expr([LV, E]);
            {field, _, LV, _, E} -> Expr([LV, E]);
            %% arg()
            {arg, _, Y, T} -> Plus(BindExpr(Y), Type(T));
            %% alt()
            {'case', _, P, E} -> Scoped(BindExpr(P), Expr(E));
            %% elim()
            {proj, _, _}    -> Zero;
            {map_get, _, E} -> Expr(E);
            %% arg_expr()
            {named_arg, _, _, E} -> Expr(E);
            _ -> Alg#alg.zero
          end,
    (Alg#alg.plus)(Top, Rec).

%% Name dependencies

used_ids(E) ->
    [ X || {{term, [X]}, _} <- used(E) ].

used_types([Top] = _CurrentNS, T) ->
    F = fun({{type, [X]}, _}) -> [X];
           ({{type, [Top1, X]}, _}) when Top1 == Top -> [X];
           (_) -> []
        end,
    lists:flatmap(F, used(T)).

-type entity() :: {term, [string()]}
                | {type, [string()]}
                | {namespace, [string()]}.

-spec entity_alg() -> alg(#{entity() => aeso_syntax:ann()}).
entity_alg() ->
    IsBound = fun({K, _}) -> lists:member(K, [bound_term, bound_type]) end,
    Unbind  = fun(bound_term) -> term; (bound_type) -> type end,
    Remove  = fun(Keys, Map) -> maps:without(Keys, Map) end,
    Scoped = fun(Xs, Ys) ->
                Bound  = [E || E <- maps:keys(Xs), IsBound(E)],
                Bound1 = [ {Unbind(Tag), X} || {Tag, X} <- Bound ],
                Others = Remove(Bound1, Ys),
                maps:merge(Remove(Bound, Xs), Others)
            end,
    #alg{ zero   = #{}
        , plus   = fun maps:merge/2
        , scoped = Scoped }.

-spec used(_) -> [{entity(), aeso_syntax:ann()}].
used(D) ->
    Kind = fun(expr)      -> term;
              (bind_expr) -> bound_term;
              (type)      -> type;
              (bind_type) -> bound_type
           end,
    NS = fun(Xs) -> {namespace, lists:droplast(Xs)} end,
    NotBound = fun({{Tag, _}, _}) -> not lists:member(Tag, [bound_term, bound_type]) end,
    Xs =
        maps:to_list(fold(entity_alg(),
            fun(K, {id,   Ann, X})  -> #{{Kind(K), [X]} => Ann};
               (K, {qid,  Ann, Xs}) -> #{{Kind(K), Xs}  => Ann, NS(Xs) => Ann};
               (K, {con,  Ann, X})  -> #{{Kind(K), [X]} => Ann};
               (K, {qcon, Ann, Xs}) -> #{{Kind(K), Xs}  => Ann, NS(Xs) => Ann};
               (_, _)             -> #{}
            end, decl, D)),
    lists:filter(NotBound, Xs).

