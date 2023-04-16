-module(aeso_ast_code_analysis).


all_warnings() ->
    [ warn_unused_includes
    , warn_unused_stateful
    , warn_unused_variables
    , warn_unused_typedefs
    , warn_unused_return_value
    , warn_unused_functions
    , warn_shadowing
    , warn_division_by_zero
    , warn_negative_spend ].


when_warning(Warn, Do) ->
    case lists:member(Warn, all_warnings()) of
        false ->
            create_type_errors(),
            type_error({unknown_warning, Warn}),
            destroy_and_report_type_errors(global_env());
        true ->
            case ets_tab_exists(warnings) of
                true ->
                    IsEnabled = get_option(Warn, false),
                    IsAll = get_option(warn_all, false) andalso lists:member(Warn, all_warnings()),
                    if
                        IsEnabled orelse IsAll -> Do();
                        true -> ok
                    end;
                false ->
                    ok
            end
    end.

%% Warnings (Unused includes)

potential_unused_include(Ann, SrcFile) ->
    IsIncluded = aeso_syntax:get_ann(include_type, Ann, none) =/= none,
    case IsIncluded of
        false -> ok;
        true  ->
            case aeso_syntax:get_ann(file, Ann, no_file) of
                no_file -> ok;
                File    -> ets_insert(warnings, {unused_include, File, SrcFile})
            end
    end.

used_include(Ann) ->
    case aeso_syntax:get_ann(file, Ann, no_file) of
        no_file -> ok;
        File    -> ets_match_delete(warnings, {unused_include, File, '_'})
    end.

%% Warnings (Unused stateful)

potential_unused_stateful(Ann, Fun) ->
    case aeso_syntax:get_ann(stateful, Ann, false) of
        false -> ok;
        true  -> ets_insert(warnings, {unused_stateful, Ann, Fun})
    end.

used_stateful(Fun) ->
    ets_match_delete(warnings, {unused_stateful, '_', Fun}).

%% Warnings (Unused type defs)

potential_unused_typedefs(Namespace, TypeDefs) ->
    lists:map(fun({type_def, Ann, Id, Args, _}) ->
        ets_insert(warnings, {unused_typedef, Ann, Namespace ++ qname(Id), length(Args)}) end, TypeDefs).

used_typedef(TypeAliasId, Arity) ->
    ets_match_delete(warnings, {unused_typedef, '_', qname(TypeAliasId), Arity}).

%% Warnings (Unused variables)

potential_unused_variables(Namespace, Fun, Vars0) ->
    Vars = [ Var || Var = {id, _, VarName} <- Vars0, VarName /= "_" ],
    lists:map(fun({id, Ann, VarName}) ->
        ets_insert(warnings, {unused_variable, Ann, Namespace, Fun, VarName}) end, Vars).

used_variable(Namespace, Fun, [VarName]) ->
    ets_match_delete(warnings, {unused_variable, '_', Namespace, Fun, VarName});
used_variable(_, _, _) -> ok.

%% Warnings (Unused return value)

potential_unused_return_value({typed, Ann, {app, _, {typed, _, _, {fun_t, _, _, _, {id, _, Type}}}, _}, _}) when Type /= "unit" ->
    ets_insert(warnings, {unused_return_value, Ann});
potential_unused_return_value(_) -> ok.

%% Warnings (Unused functions)

create_unused_functions() ->
    ets_new(function_calls, [bag]),
    ets_new(all_functions, [set]).

register_function_call(Caller, Callee) ->
    ets_insert(function_calls, {Caller, Callee}).

potential_unused_function(#env{ what = namespace }, Ann, FunQName, FunId) ->
    ets_insert(all_functions, {Ann, FunQName, FunId, not aeso_syntax:get_ann(private, Ann, false)});
potential_unused_function(_Env, Ann, FunQName, FunId) ->
    ets_insert(all_functions, {Ann, FunQName, FunId, aeso_syntax:get_ann(entrypoint, Ann, false)}).

remove_used_funs(All) ->
    {Used, Unused} = lists:partition(fun({_, _, _, IsUsed}) -> IsUsed end, All),
    CallsByUsed = lists:flatmap(fun({_, F, _, _}) -> ets_lookup(function_calls, F) end, Used),
    CalledFuns = sets:from_list(lists:map(fun({_, Callee}) -> Callee end, CallsByUsed)),
    MarkUsedFun = fun(Fun, Acc) ->
                      case lists:keyfind(Fun, 2, Acc) of
                          false -> Acc;
                          T     -> lists:keyreplace(Fun, 2, Acc, setelement(4, T, true))
                      end
                  end,
    NewUnused = sets:fold(MarkUsedFun, Unused, CalledFuns),
    case lists:keyfind(true, 4, NewUnused) of
        false -> NewUnused;
        _     -> remove_used_funs(NewUnused)
    end.

destroy_and_report_unused_functions() ->
    AllFuns = ets_tab2list(all_functions),
    lists:map(fun({Ann, _, FunId, _}) -> ets_insert(warnings, {unused_function, Ann, name(FunId)}) end,
              remove_used_funs(AllFuns)),
    ets_delete(all_functions),
    ets_delete(function_calls).

%% Warnings (Shadowing)

warn_potential_shadowing(_, "_", _) -> ok;
warn_potential_shadowing(Ann, Name, Vars) ->
    case proplists:get_value(Name, Vars, false) of
        false -> ok;
        {AnnOld, _} -> ets_insert(warnings, {shadowing, Ann, Name, AnnOld})
    end.

%% Warnings (Division by zero)

warn_potential_division_by_zero(Ann, Op, Args) ->
    case {Op, Args} of
        {{'/', _}, [_, {int, _, 0}]} -> ets_insert(warnings, {division_by_zero, Ann});
        _ -> ok
    end.

%% Warnings (Negative spends)

warn_potential_negative_spend(Ann, Fun, Args) ->
    case {Fun, Args} of
        { {typed, _, {qid, _, ["Chain", "spend"]}, _}
        , [_, {typed, _, {app, _, {'-', _}, [{typed, _, {int, _, X}, _}]}, _}]} when X > 0 ->
            ets_insert(warnings, {negative_spend, Ann});
        _ -> ok
    end.
