-module(aeso_tc_ets_manager).

-export([ ets_init/0
        , ets_new/2
        , ets_lookup/2
        , ets_insert/2
        , ets_insert_new/2
        , ets_insert_ordered/2
        , ets_delete/1
        , ets_delete/2
        , ets_match_delete/2
        , ets_tab2list/1
        , ets_tab2list_ordered/1
        , ets_tab_exists/1
        , clean_up_ets/0
        ]).

%% Clean up all the ets tables (in case of an exception)

ets_tables() ->
    [options, type_vars, constraints, freshen_tvars, type_errors,
     defined_contracts, warnings, function_calls, all_functions,
     type_vars_variance, functions_to_implement].

clean_up_ets() ->
    [ catch ets_delete(Tab) || Tab <- ets_tables() ],
    ok.

%% Named interface to ETS tables implemented without names.
%% The interface functions behave as the standard ETS interface.

ets_init() ->
    put(aeso_ast_infer_types, #{}).

ets_tab_exists(Name) ->
    Tabs = get(aeso_ast_infer_types),
    case maps:find(Name, Tabs) of
        {ok, _} -> true;
        error   -> false
    end.

ets_tabid(Name) ->
    #{Name := TabId} = get(aeso_ast_infer_types),
    TabId.

ets_new(Name, Opts) ->
    %% Ensure the table is NOT named!
    TabId = ets:new(Name, Opts -- [named_table]),
    Tabs = get(aeso_ast_infer_types),
    put(aeso_ast_infer_types, Tabs#{Name => TabId}),
    Name.

ets_delete(Name) ->
    Tabs = get(aeso_ast_infer_types),
    #{Name := TabId} = Tabs,
    put(aeso_ast_infer_types, maps:remove(Name, Tabs)),
    ets:delete(TabId).

ets_delete(Name, Key) ->
    TabId = ets_tabid(Name),
    ets:delete(TabId, Key).

ets_insert(Name, Object) ->
    TabId = ets_tabid(Name),
    ets:insert(TabId, Object).

ets_insert_new(Name, Object) ->
    TabId = ets_tabid(Name),
    ets:insert_new(TabId, Object).

ets_lookup(Name, Key) ->
    TabId = ets_tabid(Name),
    ets:lookup(TabId, Key).

ets_match_delete(Name, Pattern) ->
    TabId = ets_tabid(Name),
    ets:match_delete(TabId, Pattern).

ets_tab2list(Name) ->
    TabId = ets_tabid(Name),
    ets:tab2list(TabId).

ets_insert_ordered(_, []) -> true;
ets_insert_ordered(Name, [H|T]) ->
    ets_insert_ordered(Name, H),
    ets_insert_ordered(Name, T);
ets_insert_ordered(Name, Object) ->
    Count = next_count(),
    TabId = ets_tabid(Name),
    ets:insert(TabId, {Count, Object}).

ets_tab2list_ordered(Name) ->
    [E || {_, E} <- ets_tab2list(Name)].

next_count() ->
    V = case get(counter) of
            undefined ->
                0;
            X -> X
        end,
    put(counter, V + 1),
    V.
