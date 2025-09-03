%%%-------------------------------------------------------------------
%%% @copyright (C) 2018, Aeternity Anstalt
%%% @doc
%%%     Helper functions for type system operations.
%%% @end
%%%-------------------------------------------------------------------

-module(aeso_type_helpers).

-export([ dereference/1
        , dereference_deep/1
        , fun_arity/1
        , name/1
        , option_t/2
        , opposite_variance/1
        , qcon/2
        , qid/2
        , qname/1
        , set_qname/2
        , fresh_uvar/1
        , type_error/1
        , typesig_to_fun_t/1
        , get_oracle_type/3
        , pos/1
        , pos/2
        ]).

-include("aeso_types.hrl").

-spec option_t(aeso_syntax:ann(), utype()) -> utype().
option_t(As, T) -> {app_t, As, {id, As, "option"}, [T]}.

-spec typesig_to_fun_t(typesig()) -> utype().
typesig_to_fun_t({type_sig, Ann, _Constr, Named, Args, Res}) ->
    {fun_t, Ann, Named, Args, Res}.

%% -- Name manipulation ------------------------------------------------------

-spec qname(type_id()) -> qname().
qname({id,   _, X})  -> [X];
qname({qid,  _, Xs}) -> Xs;
qname({con,  _, X})  -> [X];
qname({qcon, _, Xs}) -> Xs.

-spec name(Named | {typed, _, Named, _}) -> name() when
      Named :: aeso_syntax:id() | aeso_syntax:con().
name({typed, _, X, _}) -> name(X);
name({id, _, X}) -> X;
name({con, _, X}) -> X.

-spec qid(aeso_syntax:ann(), qname()) -> aeso_syntax:id() | aeso_syntax:qid().
qid(Ann, [X]) -> {id, Ann, X};
qid(Ann, Xs)  -> {qid, Ann, Xs}.

-spec qcon(aeso_syntax:ann(), qname()) -> aeso_syntax:con() | aeso_syntax:qcon().
qcon(Ann, [X]) -> {con, Ann, X};
qcon(Ann, Xs)  -> {qcon, Ann, Xs}.

-spec set_qname(qname(), type_id()) -> type_id().
set_qname(Xs, {id,   Ann, _}) -> qid(Ann, Xs);
set_qname(Xs, {qid,  Ann, _}) -> qid(Ann, Xs);
set_qname(Xs, {con,  Ann, _}) -> qcon(Ann, Xs);
set_qname(Xs, {qcon, Ann, _}) -> qcon(Ann, Xs).

%% -- Type utilities ---------------------------------------------------------

%% Dereference a unification variable to its current binding
-spec dereference(utype()) -> utype().
dereference(T = {uvar, _, R}) ->
    case aeso_type_ets:lookup(type_vars, R) of
        [] ->
            T;
        [{R, Type}] ->
            dereference(Type)
    end;
dereference(T) ->
    T.

%% Deep dereference - recursively dereference all unification variables in a type
-spec dereference_deep(utype()) -> utype().
dereference_deep(Type) ->
    case dereference(Type) of
        Tup when is_tuple(Tup) ->
            list_to_tuple(dereference_deep(tuple_to_list(Tup)));
        [H | T] -> [dereference_deep(H) | dereference_deep(T)];
        T -> T
    end.

%% Create a fresh unification variable with given annotations
-spec fresh_uvar(aeso_syntax:ann()) -> utype().
fresh_uvar(Attrs) -> {uvar, Attrs, make_ref()}.

fun_arity({fun_t, _, _, Args, _}) -> length(Args);
fun_arity(_)                      -> none.

%% Flip variance for contravariant positions
-spec opposite_variance(covariant | contravariant | invariant | bivariant) -> 
                       covariant | contravariant | invariant | bivariant.
opposite_variance(invariant) -> invariant;
opposite_variance(covariant) -> contravariant;
opposite_variance(contravariant) -> covariant;
opposite_variance(bivariant) -> bivariant.

%% -- Position utilities ------------------------------------------------------

-spec pos(aeso_syntax:ann() | tuple()) -> aeso_errors:pos().
pos(T) ->
    aeso_errors:pos(aeso_syntax:get_ann(file, T, no_file),
                    aeso_syntax:get_ann(line, T, 0),
                    aeso_syntax:get_ann(col, T, 0)).

-spec pos(non_neg_integer(), non_neg_integer()) -> aeso_errors:pos().
pos(L, C) ->
    aeso_errors:pos(L, C).

%% -- Error management -------------------------------------------------------

-spec type_error(term()) -> true.
type_error(Err) ->
    aeso_type_ets:insert(type_errors, Err).

%% -- Oracle type helpers ----------------------------------------------------

get_oracle_type({qid, _, ["Oracle", "register"]},      _        , OType) -> OType;
get_oracle_type({qid, _, ["Oracle", "query"]},        [OType| _], _    ) -> OType;
get_oracle_type({qid, _, ["Oracle", "get_question"]}, [OType| _], _    ) -> OType;
get_oracle_type({qid, _, ["Oracle", "get_answer"]},   [OType| _], _    ) -> OType;
get_oracle_type({qid, _, ["Oracle", "check"]},        [OType| _], _    ) -> OType;
get_oracle_type({qid, _, ["Oracle", "check_query"]},  [OType| _], _    ) -> OType;
get_oracle_type({qid, _, ["Oracle", "respond"]},      [OType| _], _    ) -> OType;
get_oracle_type(_Fun, _Args, _Ret) -> false.
