-module(aeso_type_ets).

-export([
    clean_up_ets/0,
    delete/1,
    delete/2,
    init/0,
    insert/2,
    insert_new/2,
    insert_ordered/2,
    lookup/2,
    match_delete/2,
    new/2,
    tab2list/1,
    tab2list_ordered/1,
    tab_exists/1
]).

%% Named interface to ETS tables implemented without names.
%% The interface functions behave as the standard ETS interface.

init() ->
    put(aeso_type_ets, #{}).

tab_exists(Name) ->
    Tabs = get(aeso_type_ets),
    case maps:find(Name, Tabs) of
        {ok, _} -> true;
        error   -> false
    end.

tabid(Name) ->
    #{Name := TabId} = get(aeso_type_ets),
    TabId.

new(Name, Opts) ->
    %% Ensure the table is NOT named!
    TabId = ets:new(Name, Opts -- [named_table]),
    Tabs = get(aeso_type_ets),
    put(aeso_type_ets, Tabs#{Name => TabId}),
    Name.

delete(Name) ->
    Tabs = get(aeso_type_ets),
    #{Name := TabId} = Tabs,
    put(aeso_type_ets, maps:remove(Name, Tabs)),
    ets:delete(TabId).

delete(Name, Key) ->
    TabId = tabid(Name),
    ets:delete(TabId, Key).

insert(Name, Object) ->
    TabId = tabid(Name),
    ets:insert(TabId, Object).

insert_new(Name, Object) ->
    TabId = tabid(Name),
    ets:insert_new(TabId, Object).

lookup(Name, Key) ->
    TabId = tabid(Name),
    ets:lookup(TabId, Key).

match_delete(Name, Pattern) ->
    TabId = tabid(Name),
    ets:match_delete(TabId, Pattern).

tab2list(Name) ->
    TabId = tabid(Name),
    ets:tab2list(TabId).

insert_ordered(_Name, []) -> true;
insert_ordered(Name, [H|T]) ->
    insert_ordered(Name, H),
    insert_ordered(Name, T);
insert_ordered(Name, Object) ->
    Count = next_count(),
    TabId = tabid(Name),
    ets:insert(TabId, {Count, Object}).

tab2list_ordered(Name) ->
    [E || {_, E} <- tab2list(Name)].

next_count() ->
    V = case get(counter) of
            undefined ->
                0;
            X -> X
        end,
    put(counter, V + 1),
    V.

%% Cleanup

ets_tables() ->
    [options, type_vars, constraints, freshen_tvars, type_errors,
     defined_contracts, warnings, function_calls, all_functions,
     type_vars_variance, functions_to_implement].

clean_up_ets() ->
    [ catch delete(Tab) || Tab <- ets_tables() ],
    ok.
