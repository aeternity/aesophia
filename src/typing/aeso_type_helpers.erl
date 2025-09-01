%%%-------------------------------------------------------------------
%%% @copyright (C) 2018, Aeternity Anstalt
%%% @doc
%%%     Helper functions for type system operations.
%%% @end
%%%-------------------------------------------------------------------

-module(aeso_type_helpers).

-export([option_t/2, typesig_to_fun_t/1]).

-include("aeso_types.hrl").

-spec option_t(aeso_syntax:ann(), utype()) -> utype().
option_t(As, T) -> {app_t, As, {id, As, "option"}, [T]}.

-spec typesig_to_fun_t(typesig()) -> utype().
typesig_to_fun_t({type_sig, Ann, _Constr, Named, Args, Res}) ->
    {fun_t, Ann, Named, Args, Res}.
