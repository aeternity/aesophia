%%% File        : aeso_utils_eqc.erl
%%% Author      : Ulf Norell
%%% Description :
%%% Created     : 2 Jul 2018 by Ulf Norell
-module(aeso_utils_eqc).

-compile([export_all, nowarn_export_all]).

-include_lib("eqc/include/eqc.hrl").

%% QuickCheck property

graph() ->
    ?LET(M, map(choose(0, 10), list(choose(0, 10))),
    return(complete(M))).

complete(G) ->
    Is = lists:usort(lists:concat(maps:values(G))),
    maps:merge(maps:from_list([ {I, []} || I <- Is ]), G).

prop_scc() ->
    ?FORALL(G, graph(),
    begin
        SCCs = aeso_utils:scc(G),
        BadSCC = fun({acyclic, I}) -> reachable_from(G, I, I);
                    ({cyclic, Is}) -> [] /= [ {I, J} || I <- Is, J <- Is, not reachable_from(G, I, J) ]
                 end,
        ToList = fun({acyclic, I}) -> [I];
                    ({cyclic, Is}) -> Is end,
        ?WHENFAIL(eqc:format("SCCs = ~p\n", [SCCs]),
        conjunction(
            [ {elems,  equals(lists:sort(lists:flatmap(ToList, SCCs)), lists:sort(maps:keys(G)))}
            , {sorted, equals([], [ {I, J} || {I, Js} <- maps:to_list(G),
                                              J <- Js,
                                              find_component(I, SCCs) < find_component(J, SCCs) ])}
            , {precise, equals([], [ SCC || SCC <- SCCs, BadSCC(SCC) ])}
            ]))
    end).

reachable_from(Graph, I, J) ->
    reachable_from1(Graph, maps:get(I, Graph, []), J).

reachable_from1(_, [], _) -> false;
reachable_from1(_, [I | _], I) -> true;
reachable_from1(Graph, [I | Is], J) ->
    case maps:get(I, Graph, undefined) of
        undefined -> reachable_from1(Graph, Is, J);
        Js        -> reachable_from1(maps:remove(I, Graph), Js ++ Is, J)
    end.

find_component(X, SCCs) ->
    ISCCs = lists:zip(SCCs, lists:seq(1, length(SCCs))),
    HasX  = fun({acyclic, Y}) -> X == Y;
               ({cyclic, Ys}) -> lists:member(X, Ys) end,
    case [ I || {SCC, I} <- ISCCs, HasX(SCC) ] of
        [I | _] -> I;
        []      -> false
    end.

