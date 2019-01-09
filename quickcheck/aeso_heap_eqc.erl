%%% File        : aeso_heap_eqc.erl
%%% Author      : Ulf Norell
%%% Description :
%%% Created     : 28 May 2018 by Ulf Norell
-module(aeso_heap_eqc).

-compile([export_all, nowarn_export_all]).
-include_lib("eqc/include/eqc.hrl").

-define(SANDBOX(Code), sandbox(fun() -> Code end)).

sandbox(Code) ->
    Parent = self(),
    Tag    = make_ref(),
    {Pid, Ref} = spawn_monitor(fun() -> Parent ! {Tag, Code()} end),
    receive
        {Tag, Res} -> erlang:demonitor(Ref, [flush]), {ok, Res};
        {'DOWN', Ref, process, Pid, Reason} -> {error, Reason}
    after 100 ->
        exit(Pid, kill),
        {error, loop}
    end.

prop_from_binary() ->
    ?FORALL({T, Bin}, {type(), blob()},
    begin
    Tag = fun(X) when is_atom(X) -> X; (X) when is_tuple(X) -> element(1, X) end,
    case ?SANDBOX(aeso_heap:from_binary(T, Bin)) of
        {ok, Res} -> collect({Tag(T), element(1, Res)}, true);
        Err       -> equals(Err, {ok, '_'})
    end end).

type() -> ?LET(Depth, choose(0, 2), type(Depth, true)).
type(Depth, TypeRep) ->
    oneof(
    [ elements([word, string] ++ [typerep || TypeRep]) ] ++
    [ ?LETSHRINK([T], [type(Depth - 1, TypeRep)], {list, T})       || Depth > 0 ] ++
    [ ?LETSHRINK([T], [type(Depth - 1, TypeRep)], {option, T})     || Depth > 0 ] ++
    [ ?LETSHRINK(Ts,  list(type(Depth - 1, TypeRep)), {tuple, Ts}) || Depth > 0 ] ++
    [ ?LETSHRINK([K, V], vector(2, type(Depth - 1, TypeRep)), {map, K, V}) || Depth > 0 ] ++
    []
    ).

blob() ->
    ?LET(Blobs, list(oneof([ ?LET(Ws, words(), return(from_words(Ws)))
                           , binary() ])),
    return(list_to_binary(Blobs))).

words() -> list(word()).
word() ->
    frequency(
    [ {4, ?LET(N, nat(), 32 * N)}
    , {1, choose(0, 320)}
    , {2, -1}
    , {2, elements(["foo", "zzzzz"])} ]).

from_words(Ws) ->
    << <<(from_word(W))/binary>> || W <- Ws >>.

from_word(W) when is_integer(W) ->
    <<W:256>>;
from_word(S) when is_list(S) ->
    Len = length(S),
    Bin = <<(list_to_binary(S))/binary, 0:(32 - Len)/unit:8>>,
    <<Len:256, Bin/binary>>.

typerep() -> ?LET(Depth, choose(0, 2),
             ?LET(T, type(Depth, true), return(typerep(T)))).

typerep(word)          -> word;
typerep(string)        -> string;
typerep(typerep)       -> typerep;
typerep({tuple, Ts})   -> {tuple, typerep(Ts)};
typerep({list, T})     -> {list, typerep(T)};
typerep({variant, Cs}) -> {variant, typerep(Cs)};
typerep({option, T})   -> {variant, [[], [typerep(T)]]};
typerep({map, K, V})   -> {list, typerep({tuple, [K, V]})};
typerep([])            -> [];
typerep([T | Ts])      -> [typerep(T) | typerep(Ts)].

value(word) ->
    <<N:256>> = <<(-1):256>>,
    choose(0, N);
value(string) ->
    ?LET(N, choose(0, 128), binary(N));
value(typerep) ->
    typerep();
value({list, T}) ->
    list(value(T));
value({option, T}) ->
    weighted_default({1, none}, {3, {some, value(T)}});
value({tuple, Ts}) ->
    ?LET(Vs, [ value(T) || T <- Ts ], list_to_tuple(Vs));
value({map, K, V}) ->
    map(value(K), value(V));
value({variant, Cs}) ->
    ?LET(I, choose(0, length(Cs) - 1),
    {variant, I, [ value(T) || T <- lists:nth(I + 1, Cs) ]}).

typed_val() ->
    ?LET(T, type(), ?LET(V, value(T), return({T, V}))).

prop_roundtrip() ->
    ?FORALL(T, type(),
    ?FORALL(V, value(T),
    ?FORALL(B, choose(0, 4),
    equals(aeso_heap:from_binary(T, aeso_heap:to_binary(V, B * 32), B * 32),
           {ok, V})))).

