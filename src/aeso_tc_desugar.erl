-module(aeso_tc_desugar).

-export([ desugar/1
        , desugar_clauses/4
        , process_blocks/1
        ]).

%% -- Moved functions --------------------------------------------------------

type_error(A) -> aeso_tc_errors:type_error(A).

%% ---------------------------------------------------------------------------

%% Restructure blocks into multi-clause fundefs (`fun_clauses`).
-spec process_blocks([aeso_syntax:decl()]) -> [aeso_syntax:decl()].
process_blocks(Decls) ->
    lists:flatmap(
      fun({block, Ann, Ds}) -> process_block(Ann, Ds);
         (Decl)             -> [Decl] end, Decls).

-spec process_block(aeso_syntax:ann(), [aeso_syntax:decl()]) -> [aeso_syntax:decl()].
process_block(_, []) -> [];
process_block(_, [Decl]) -> [Decl];
process_block(_Ann, [Decl | Decls]) ->
    IsThis = fun(Name) -> fun({letfun, _, {id, _, Name1}, _, _, _}) -> Name == Name1;
                             (_) -> false end end,
    case Decl of
        {fun_decl, Ann1, Id = {id, _, Name}, Type} ->
            {Clauses, Rest} = lists:splitwith(IsThis(Name), Decls),
            [type_error({mismatched_decl_in_funblock, Name, D1}) || D1 <- Rest],
            [{fun_clauses, Ann1, Id, Type, Clauses}];
        {letfun, Ann1, Id = {id, _, Name}, _, _, _} ->
            {Clauses, Rest} = lists:splitwith(IsThis(Name), [Decl | Decls]),
            [type_error({mismatched_decl_in_funblock, Name, D1}) || D1 <- Rest],
            [{fun_clauses, Ann1, Id, {id, [{origin, system} | Ann1], "_"}, Clauses}]
    end.

desugar_clauses(Ann, Fun, {type_sig, _, _, _, ArgTypes, RetType}, Clauses) ->
    NeedDesugar =
        case Clauses of
            [{letfun, _, _, As, _, [{guarded, _, [], _}]}] -> lists:any(fun({typed, _, {id, _, _}, _}) -> false; (_) -> true end, As);
            _                                              -> true
        end,
    case NeedDesugar of
        false -> [Clause] = Clauses, Clause;
        true  ->
            NoAnn = [{origin, system}],
            Args = [ {typed, NoAnn, {id, NoAnn, "x#" ++ integer_to_list(I)}, Type}
                     || {I, Type} <- indexed(1, ArgTypes) ],
            Tuple = fun([X]) -> X;
                       (As) -> {typed, NoAnn, {tuple, NoAnn, As}, {tuple_t, NoAnn, ArgTypes}}
                    end,
            {letfun, Ann, Fun, Args, RetType, [{guarded, NoAnn, [], {typed, NoAnn,
               {switch, NoAnn, Tuple(Args),
                 [ {'case', AnnC, Tuple(ArgsC), GuardedBodies}
                 || {letfun, AnnC, _, ArgsC, _, GuardedBodies} <- Clauses ]}, RetType}}]}
    end.

%% -- Pre-type checking desugaring -------------------------------------------

%% Desugars nested record/map updates as follows:
%%  { x.y = v1, x.z @ z = f(z) } becomes { x @ __x = __x { y = v1, z @ z = f(z) } }
%%  { [k1].x = v1, [k2].y = v2 } becomes { [k1] @ __x = __x { x = v1 }, [k2] @ __x = __x { y = v2 } }
%% There's no comparison of k1 and k2 to group the updates if they are equal.
desugar({record, Ann, Rec, Updates}) ->
    {record, Ann, Rec, desugar_updates(Updates)};
desugar({map, Ann, Map, Updates}) ->
    {map, Ann, Map, desugar_updates(Updates)};
desugar([H|T]) ->
  [desugar(H) | desugar(T)];
desugar(T) when is_tuple(T) ->
  list_to_tuple(desugar(tuple_to_list(T)));
desugar(X) -> X.

desugar_updates([]) -> [];
desugar_updates([Upd | Updates]) ->
    {Key, MakeField, Rest} = update_key(Upd),
    {More, Updates1}       = updates_key(Key, Updates),
    %% Check conflicts
    case length([ [] || [] <- [Rest | More] ]) of
        N when N > 1 -> type_error({conflicting_updates_for_field, Upd, Key});
        _ -> ok
    end,
    [MakeField(lists:append([Rest | More])) | desugar_updates(Updates1)].

%% TODO: refactor representation to make this not horrible
update_key(Fld = {field, _, [Elim], _}) ->
    {elim_key(Elim), fun(_) -> Fld end, []};
update_key(Fld = {field, _, [Elim], _, _}) ->
    {elim_key(Elim), fun(_) -> Fld end, []};
update_key({field, Ann, [P = {proj, _, {id, _, Name}} | Rest], Value}) ->
    {Name, fun(Flds) -> {field, Ann, [P], {id, [], "__x"},
                            desugar(map_or_record(Ann, {id, [], "__x"}, Flds))}
           end, [{field, Ann, Rest, Value}]};
update_key({field, Ann, [P = {proj, _, {id, _, Name}} | Rest], Id, Value}) ->
    {Name, fun(Flds) -> {field, Ann, [P], {id, [], "__x"},
                            desugar(map_or_record(Ann, {id, [], "__x"}, Flds))}
           end, [{field, Ann, Rest, Id, Value}]};
update_key({field, Ann, [K = {map_get, _, _} | Rest], Value}) ->
    {map_key, fun(Flds) -> {field, Ann, [K], {id, [], "__x"},
                            desugar(map_or_record(Ann, {id, [], "__x"}, Flds))}
              end, [{field, Ann, Rest, Value}]};
update_key({field, Ann, [K = {map_get, _, _, _} | Rest], Value}) ->
    {map_key, fun(Flds) -> {field, Ann, [K], {id, [], "__x"},
                            desugar(map_or_record(Ann, {id, [], "__x"}, Flds))}
              end, [{field, Ann, Rest, Value}]};
update_key({field, Ann, [K = {map_get, _, _, _} | Rest], Id, Value}) ->
    {map_key, fun(Flds) -> {field, Ann, [K], {id, [], "__x"},
                            desugar(map_or_record(Ann, {id, [], "__x"}, Flds))}
              end, [{field, Ann, Rest, Id, Value}]};
update_key({field, Ann, [K = {map_get, _, _} | Rest], Id, Value}) ->
    {map_key, fun(Flds) -> {field, Ann, [K], {id, [], "__x"},
                            desugar(map_or_record(Ann, {id, [], "__x"}, Flds))}
              end, [{field, Ann, Rest, Id, Value}]}.

map_or_record(Ann, Val, Flds = [Fld | _]) ->
    Kind = case element(3, Fld) of
             [{proj, _, _}       | _] -> record;
             [{map_get, _, _}    | _] -> map;
             [{map_get, _, _, _} | _] -> map
           end,
    {Kind, Ann, Val, Flds}.

elim_key({proj, _, {id, _, Name}}) -> Name;
elim_key({map_get, _, _, _})       -> map_key;  %% no grouping on map keys (yet)
elim_key({map_get, _, _})          -> map_key.

updates_key(map_key, Updates) -> {[], Updates};
updates_key(Name, Updates) ->
    Xs = [ {Upd, Name1 == Name, Rest}
           || Upd <- Updates,
              {Name1, _, Rest} <- [update_key(Upd)] ],
    Updates1 = [ Upd  || {Upd, false, _} <- Xs ],
    More     = [ Rest || {_, true, Rest} <- Xs ],
    {More, Updates1}.

indexed(I, Xs) ->
    lists:zip(lists:seq(I, I + length(Xs) - 1), Xs).
