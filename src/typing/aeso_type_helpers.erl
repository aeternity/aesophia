%%%-------------------------------------------------------------------
%%% @copyright (C) 2018, Aeternity Anstalt
%%% @doc
%%%     Helper functions for type system operations.
%%% @end
%%%-------------------------------------------------------------------

-module(aeso_type_helpers).

-export([fun_arity/1, name/1, option_t/2, qid/2, qname/1, typesig_to_fun_t/1]).

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

%% -- Type utilities ---------------------------------------------------------

fun_arity({fun_t, _, _, Args, _}) -> length(Args);
fun_arity(_)                      -> none.
