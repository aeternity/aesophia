%%%-------------------------------------------------------------------
%%% @copyright (C) 2018, Aeternity Anstalt
%%% @doc
%%%     Sophia syntax utilities.
%%% @end
%%%-------------------------------------------------------------------
-module(aeso_syntax_utils).

-export([used_ids/1, used_types/1, used/1]).

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
            {type_decl, _, I, _}     -> BindType(I);
            {type_def, _, I, _, D}   -> Plus(BindType(I), Decl(D));
            {fun_decl, _, _, T}      -> Type(T);
            {letval, _, F, T, E}     -> Sum([BindExpr(F), Type(T), Expr(E)]);
            {letfun, _, F, Xs, T, E} -> Sum([BindExpr(F), Type(T), Scoped(BindExpr(Xs), Expr(E))]);
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
            {typed, _, E, T}       -> Plus(Expr(E), Type(T));
            {record, _, Fs}        -> Expr(Fs);
            {record, _, E, Fs}     -> Expr([E | Fs]);
            {map, _, E, Fs}        -> Expr([E | Fs]);
            {map, _, KVs}          -> Sum([Expr([Key, Val]) || {Key, Val} <- KVs]);
            {map_get, _, A, B}     -> Expr([A, B]);
            {map_get, _, A, B, C}  -> Expr([A, B, C]);
            {block, _, Ss}         -> Expr(Ss);
            %% field()
            {field, _, LV, E}    -> Expr([LV, E]);
            {field, _, LV, _, E} -> Expr([LV, E]);
            %% arg()
            {arg, _, X, T} -> Plus(Expr(X), Type(T));
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
    [ X || {term, [X]} <- used(E) ].

used_types(T) ->
    [ X || {type, [X]} <- used(T) ].

-type entity() :: {term, [string()]}
                | {type, [string()]}
                | {namespace, [string()]}.

-spec entity_alg() -> alg([entity()]).
entity_alg() ->
    IsBound = fun({K, _}) -> lists:member(K, [bound_term, bound_type]) end,
    Unbind  = fun(bound_term) -> term; (bound_type) -> type end,
    Scoped = fun(Xs, Ys) ->
                {Bound, Others} = lists:partition(IsBound, Ys),
                Bound1 = [ {Unbind(Tag), X} || {Tag, X} <- Bound ],
                lists:umerge(Xs -- Bound1, Others)
            end,
    #alg{ zero   = []
        , plus   = fun lists:umerge/2
        , scoped = Scoped }.

-spec used(_) -> [entity()].
used(D) ->
    Kind = fun(expr)      -> term;
              (bind_expr) -> bound_term;
              (type)      -> type;
              (bind_type) -> bound_type
           end,
    NS = fun(Xs) -> {namespace, lists:droplast(Xs)} end,
    NotBound = fun({Tag, _}) -> not lists:member(Tag, [bound_term, bound_type]) end,
    Xs =
        fold(entity_alg(),
            fun(K, {id,   _, X})  -> [{Kind(K), [X]}];
               (K, {qid,  _, Xs}) -> [{Kind(K), Xs}, NS(Xs)];
               (K, {con,  _, X})  -> [{Kind(K), [X]}];
               (K, {qcon, _, Xs}) -> [{Kind(K), Xs}, NS(Xs)];
               (_, _)             -> []
            end, decl, D),
    lists:filter(NotBound, Xs).

