-module(aeso_tc_fresh).

-export([ fresh_uvar/1
        , freshen/1
        , create_freshen_tvars/0
        , destroy_freshen_tvars/0
        , freshen_type/2
        , freshen_type_sig/2
        ]).

fresh_uvar(Attrs) ->
    {uvar, Attrs, make_ref()}.

create_freshen_tvars() ->
    aeso_tc_ets_manager:ets_new(freshen_tvars, [set]).

destroy_freshen_tvars() ->
    aeso_tc_ets_manager:ets_delete(freshen_tvars).

freshen_type(Ann, Type) ->
    create_freshen_tvars(),
    Type1 = freshen(Ann, Type),
    destroy_freshen_tvars(),
    Type1.

freshen(Type) ->
    freshen(aeso_syntax:get_ann(Type), Type).

freshen(Ann, {tvar, _, Name}) ->
    NewT = case aeso_tc_ets_manager:ets_lookup(freshen_tvars, Name) of
               []          -> fresh_uvar(Ann);
               [{Name, T}] -> T
           end,
    aeso_tc_ets_manager:ets_insert(freshen_tvars, {Name, NewT}),
    NewT;
freshen(Ann, {bytes_t, _, any}) ->
    X = fresh_uvar(Ann),
    aeso_tc_constraints:add_is_bytes_constraint(X),
    X;
freshen(Ann, T) when is_tuple(T) ->
    list_to_tuple(freshen(Ann, tuple_to_list(T)));
freshen(Ann, [A | B]) ->
    [freshen(Ann, A) | freshen(Ann, B)];
freshen(_, X) ->
    X.

freshen_type_sig(Ann, TypeSig = {type_sig, _, Constr, _, _, _}) ->
    FunT = freshen_type(Ann, aeso_tc_type_utils:typesig_to_fun_t(TypeSig)),
    apply_typesig_constraint(Ann, Constr, FunT),
    FunT.

apply_typesig_constraint(_Ann, none, _FunT) -> ok;
apply_typesig_constraint(Ann, address_to_contract, {fun_t, _, [], [_], Type}) ->
    aeso_tc_constraints:add_is_contract_constraint(Type, {address_to_contract, Ann});
apply_typesig_constraint(Ann, bytes_concat, {fun_t, _, [], [A, B], C}) ->
    aeso_tc_constraints:add_add_bytes_constraint(Ann, concat, A, B, C);
apply_typesig_constraint(Ann, bytes_split, {fun_t, _, [], [C], {tuple_t, _, [A, B]}}) ->
    aeso_tc_constraints:add_add_bytes_constraint(Ann, split, A, B, C);
apply_typesig_constraint(Ann, bytecode_hash, {fun_t, _, _, [Con], _}) ->
    aeso_tc_constraints:add_is_contract_constraint(Con, {bytecode_hash, Ann}).
