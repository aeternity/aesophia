%%%-------------------------------------------------------------------
%%% @copyright (C) 2018, Aeternity Anstalt
%%% @doc
%%%     Sophia syntax utilities.
%%% @end
%%%-------------------------------------------------------------------
-module(aeso_syntax_utils).

-export([used_ids/1, used_types/1, fold/4]).

-record(alg, {zero, plus, minus}). %% minus for variable binding

-type alg(A) :: #alg{ zero  :: A
                    , plus  :: fun((A, A) -> A)
                    , minus :: fun((A, A) -> A) }.

-type kind() :: decl | type | expr | pat.

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
fold(Alg, Fun, K, Xs) when is_list(Xs) ->
    lists:foldl(fun(X, A) -> (Alg#alg.plus)(A, fold(Alg, Fun, K, X)) end,
                Alg#alg.zero, Xs);
fold(Alg = #alg{zero = Zero, plus = Plus, minus = Minus}, Fun, K, X) ->
    Sum  = fun(Xs) -> lists:foldl(Plus, Zero, Xs) end,
    Decl = fun(D) -> fold(Alg, Fun, decl, D) end,
    Type = fun(T) -> fold(Alg, Fun, type, T) end,
    Expr = fun(E) -> fold(Alg, Fun, expr, E) end,
    Pat  = fun(P) -> fold(Alg, Fun, pat,  P) end,
    Top = Fun(K, X),
    LetBound = fun LB ({letval, _, Y, _, _})    -> Expr(Y);
                   LB ({letfun, _, F, _, _, _}) -> Expr(F);
                   LB ({letrec, _, Ds})         -> Sum(lists:map(LB, Ds));
                   LB (_)                       -> Zero
                end,
    Rec = case X of
            %% decl()
            {contract, _, _, Ds}     -> Decl(Ds);
            {namespace, _, _, Ds}    -> Decl(Ds);
            {type_decl, _, _, _}     -> Zero;
            {type_def, _, _, _, D}   -> Decl(D);
            {fun_decl, _, _, T}      -> Type(T);
            {letval, _, _, T, E}     -> Plus(Type(T), Expr(E));
            {letfun, _, _, Xs, T, E} -> Plus(Type(T), Minus(Expr(E), Expr(Xs)));
            {letrec, _, Ds}          -> Decl(Ds);
            %% typedef()
            {alias_t, T}    -> Type(T);
            {record_t, Fs}  -> Type(Fs);
            {variant_t, Cs} -> Type(Cs);
            %% field_t() and constructor_t()
            {field_t, _, _, T}   -> Type(T);
            {constr_t, _, _, Ts} -> Type(Ts);
            %% type()
            {fun_t, _, Named, Args, Ret} -> Type([Named, Args, Ret]);
            {app_t, _, T, Ts} -> Type([T | Ts]);
            {tuple_t, _, Ts} -> Type(Ts);
            %% named_arg_t()
            {named_arg_t, _, _, T, E} -> Plus(Type(T), Expr(E));
            %% expr()
            {lam, _, Args, E}      -> Minus(Expr(E), Expr(Args));
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
            {block, Ann, [S | Ss]} -> Plus(Expr(S), Minus(Expr({block, Ann, Ss}), LetBound(S)));
            {block, _, []}         -> Zero;
            %% field()
            {field, _, LV, E}    -> Expr([LV, E]);
            {field, _, LV, _, E} -> Expr([LV, E]);
            %% arg()
            {arg, _, X, T} -> Plus(Expr(X), Type(T));
            %% alt()
            {'case', _, P, E} -> Minus(Expr(E), Pat(P));
            %% elim()
            {proj, _, _}    -> Zero;
            {map_get, _, E} -> Expr(E);
            %% arg_expr()
            {named_arg, _, _, E} -> Expr(E);
            _ -> Alg#alg.zero
          end,
    (Alg#alg.plus)(Top, Rec).

%% Var set combinators

-spec ulist_alg() -> alg([any()]).
ulist_alg() -> #alg{ zero = [], plus = fun lists:umerge/2, minus = fun erlang:'--'/2 }.

used_ids(E) ->
    fold(ulist_alg(),
         fun(expr, {id, _, X}) -> [X];
            (pat,  {id, _, X}) -> [X];
            (_, _) -> [] end, decl, E).

used_types(T) ->
    fold(ulist_alg(),
         fun(type, {id, _, X}) -> [X];
            (_, _) -> [] end, decl, T).

