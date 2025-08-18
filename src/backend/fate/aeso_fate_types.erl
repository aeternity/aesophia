%%%-------------------------------------------------------------------
%%% @doc Type lowering helpers for FATE backend
%%%-------------------------------------------------------------------
-module(aeso_fate_types).

-export([typesig_to_scode/2, type_to_scode/1, types_to_scode/1]).

-include("aeso_fate_env.hrl").

-define(tvars, '$tvars').

typesig_to_scode(Args, Res) ->
    put(?tvars, {0, #{}}),
    R = {[type_to_scode(T) || {_, T} <- Args], type_to_scode(Res)},
    erase(?tvars),
    R.

type_to_scode(integer)         -> integer;
type_to_scode(boolean)         -> boolean;
type_to_scode(string)          -> string;
type_to_scode(address)         -> address;
type_to_scode({bytes, N})      -> {bytes, N};
type_to_scode(contract)        -> contract;
type_to_scode({oracle, _, _})  -> oracle;
type_to_scode(oracle_query)    -> oracle_query;
type_to_scode(name)            -> name;
type_to_scode(channel)         -> channel;
type_to_scode(bits)            -> bits;
type_to_scode(any)             -> any;
type_to_scode({variant, Cons}) -> {variant, [{tuple, types_to_scode(Con)} || Con <- Cons]};
type_to_scode({list, Type})    -> {list, type_to_scode(Type)};
type_to_scode({tuple, [Type]}) -> type_to_scode(Type);
type_to_scode({tuple, Types})  -> {tuple, types_to_scode(Types)};
type_to_scode({map, Key, Val}) -> {map, type_to_scode(Key), type_to_scode(Val)};
type_to_scode({function, _Args, _Res}) -> {tuple, [string, any]};
type_to_scode({tvar, X}) ->
    {I, Vars} = get(?tvars),
    case maps:get(X, Vars, false) of
        false ->
            put(?tvars, {I + 1, Vars#{ X => I }}),
            {tvar, I};
        J -> {tvar, J}
    end;
type_to_scode(L) when is_list(L) -> {tuple, types_to_scode(L)}.

types_to_scode(Ts) -> lists:map(fun type_to_scode/1, Ts).


