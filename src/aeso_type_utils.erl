-module(aeso_type_utils).

-export([ dereference/1
        , dereference_deep/1
        , instantiate/1
        , typesig_to_fun_t/1
        ]).

typesig_to_fun_t({type_sig, Ann, _Constr, Named, Args, Res}) ->
    {fun_t, Ann, Named, Args, Res}.

dereference(T = {uvar, _, R}) ->
    case aeso_ets_manager:ets_lookup(type_vars, R) of
        [] ->
            T;
        [{R, Type}] ->
            dereference(Type)
    end;
dereference(T) ->
    T.

dereference_deep(Type) ->
    case dereference(Type) of
        Tup when is_tuple(Tup) ->
            list_to_tuple(dereference_deep(tuple_to_list(Tup)));
        [H | T] -> [dereference_deep(H) | dereference_deep(T)];
        T -> T
    end.

%% Dereferences all uvars and replaces the uninstantiated ones with a
%% succession of tvars.
instantiate(E) ->
    instantiate1(dereference(E)).

instantiate1({uvar, Attr, R}) ->
    Next = proplists:get_value(next, aeso_ets_manager:ets_lookup(type_vars, next), 0),
    TVar = {tvar, Attr, "'" ++ integer_to_tvar(Next)},
    aeso_ets_manager:ets_insert(type_vars, [{next, Next + 1}, {R, TVar}]),
    TVar;
instantiate1({fun_t, Ann, Named, Args, Ret}) ->
    case dereference(Named) of
        {uvar, _, R} ->
            %% Uninstantiated named args map to the empty list
            NoNames = [],
            aeso_ets_manager:ets_insert(type_vars, [{R, NoNames}]),
            {fun_t, Ann, NoNames, instantiate(Args), instantiate(Ret)};
        Named1 ->
            {fun_t, Ann, instantiate1(Named1), instantiate(Args), instantiate(Ret)}
    end;
instantiate1(T) when is_tuple(T) ->
    list_to_tuple(instantiate1(tuple_to_list(T)));
instantiate1([A|B]) ->
    [instantiate(A)|instantiate(B)];
instantiate1(X) ->
    X.

integer_to_tvar(X) when X < 26 ->
    [$a + X];
integer_to_tvar(X) ->
    [integer_to_tvar(X div 26)] ++ [$a + (X rem 26)].
