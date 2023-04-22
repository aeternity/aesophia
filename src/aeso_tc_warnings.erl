-module(aeso_tc_warnings).

-export([ warn_potential_shadowing/3
        , used_include/1
        , create_unused_functions/0
        , destroy_and_report_unused_functions/0
        , destroy_and_report_warnings_as_type_errors/0
        , potential_unused_include/2
        , potential_unused_typedefs/2
        , potential_unused_constants/2
        , potential_unused_stateful/2
        , potential_unused_variables/3
        , potential_unused_function/4
        , mk_warning/1
        , used_variable/3
        , register_function_call/2
        , used_constant/2
        , used_stateful/1
        , warn_potential_negative_spend/3
        , warn_potential_division_by_zero/3
        , potential_unused_return_value/1
        , used_typedef/2
        , all_warnings/0
        ]).

%% -- Moved functions --------------------------------------------------------

name(A) -> aeso_tc_name_manip:name(A).
qname(A) -> aeso_tc_name_manip:qname(A).

%% -------

pos(A) -> aeso_tc_ann_manip:pos(A).

%% -------

pp_loc(A) -> aeso_tc_pp:pp_loc(A).

%% ---------------------------------------------------------------------------

all_warnings() ->
    [ warn_unused_includes
    , warn_unused_stateful
    , warn_unused_variables
    , warn_unused_constants
    , warn_unused_typedefs
    , warn_unused_return_value
    , warn_unused_functions
    , warn_shadowing
    , warn_division_by_zero
    , warn_negative_spend ].

%% Warnings (Unused includes)

potential_unused_include(Ann, SrcFile) ->
    IsIncluded = aeso_syntax:get_ann(include_type, Ann, none) =/= none,
    case IsIncluded of
        false -> ok;
        true  ->
            case aeso_syntax:get_ann(file, Ann, no_file) of
                no_file -> ok;
                File    -> aeso_ets_manager:ets_insert(warnings, {unused_include, File, SrcFile})
            end
    end.

used_include(Ann) ->
    case aeso_syntax:get_ann(file, Ann, no_file) of
        no_file -> ok;
        File    -> aeso_ets_manager:ets_match_delete(warnings, {unused_include, File, '_'})
    end.

%% Warnings (Unused stateful)

potential_unused_stateful(Ann, Fun) ->
    case aeso_syntax:get_ann(stateful, Ann, false) of
        false -> ok;
        true  -> aeso_ets_manager:ets_insert(warnings, {unused_stateful, Ann, Fun})
    end.

used_stateful(Fun) ->
    aeso_ets_manager:ets_match_delete(warnings, {unused_stateful, '_', Fun}).

%% Warnings (Unused type defs)

potential_unused_typedefs(Namespace, TypeDefs) ->
    lists:map(fun({type_def, Ann, Id, Args, _}) ->
        aeso_ets_manager:ets_insert(warnings, {unused_typedef, Ann, Namespace ++ qname(Id), length(Args)}) end, TypeDefs).

used_typedef(TypeAliasId, Arity) ->
    aeso_ets_manager:ets_match_delete(warnings, {unused_typedef, '_', qname(TypeAliasId), Arity}).

%% Warnings (Unused variables)

potential_unused_variables(Namespace, Fun, Vars0) ->
    Vars = [ Var || Var = {id, _, VarName} <- Vars0, VarName /= "_" ],
    lists:map(fun({id, Ann, VarName}) ->
        aeso_ets_manager:ets_insert(warnings, {unused_variable, Ann, Namespace, Fun, VarName}) end, Vars).

used_variable(Namespace, Fun, [VarName]) ->
    aeso_ets_manager:ets_match_delete(warnings, {unused_variable, '_', Namespace, Fun, VarName});
used_variable(_, _, _) -> ok.

%% Warnings (Unused constants)

potential_unused_constants(Env, Consts) ->
    case aeso_ast_infer_types:get_env_what(Env) of
        namespace -> [];
        _ ->
            [ aeso_ets_manager:ets_insert(warnings, {unused_constant, Ann, aeso_ast_infer_types:get_env_namespace(Env), Name}) || {letval, _, {id, Ann, Name}, _} <- Consts ]
    end.

used_constant(Namespace = [Contract], [Contract, ConstName]) ->
    aeso_ets_manager:ets_match_delete(warnings, {unused_constant, '_', Namespace, ConstName});
used_constant(_, _) -> ok.

%% Warnings (Unused return value)

potential_unused_return_value({typed, Ann, {app, _, {typed, _, _, {fun_t, _, _, _, {id, _, Type}}}, _}, _}) when Type /= "unit" ->
    aeso_ets_manager:ets_insert(warnings, {unused_return_value, Ann});
potential_unused_return_value(_) -> ok.

%% Warnings (Unused functions)

create_unused_functions() ->
    aeso_ets_manager:ets_new(function_calls, [bag]),
    aeso_ets_manager:ets_new(all_functions, [set]).

register_function_call(Caller, Callee) ->
    aeso_ets_manager:ets_insert(function_calls, {Caller, Callee}).

potential_unused_function(Env, Ann, FunQName, FunId) ->
    case aeso_ast_infer_types:get_env_what(Env) of
        namespace ->
            aeso_ets_manager:ets_insert(all_functions, {Ann, FunQName, FunId, not aeso_syntax:get_ann(private, Ann, false)});
        _ ->
            aeso_ets_manager:ets_insert(all_functions, {Ann, FunQName, FunId, aeso_syntax:get_ann(entrypoint, Ann, false)})
    end.

remove_used_funs(All) ->
    {Used, Unused} = lists:partition(fun({_, _, _, IsUsed}) -> IsUsed end, All),
    CallsByUsed = lists:flatmap(fun({_, F, _, _}) -> aeso_ets_manager:ets_lookup(function_calls, F) end, Used),
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
    AllFuns = aeso_ets_manager:ets_tab2list(all_functions),
    lists:map(fun({Ann, _, FunId, _}) -> aeso_ets_manager:ets_insert(warnings, {unused_function, Ann, name(FunId)}) end,
              remove_used_funs(AllFuns)),
    aeso_ets_manager:ets_delete(all_functions),
    aeso_ets_manager:ets_delete(function_calls).

%% Warnings (Shadowing)

warn_potential_shadowing(_, _, "_") -> ok;
warn_potential_shadowing(Env, Ann, Name) ->
    Vars = aeso_ast_infer_types:get_env_vars(Env),
    Consts = aeso_ast_infer_types:get_current_scope_consts(Env),
    case proplists:get_value(Name, Vars ++ Consts, false) of
        false -> ok;
        {AnnOld, _} -> aeso_ets_manager:ets_insert(warnings, {shadowing, Ann, Name, AnnOld})
    end.

%% Warnings (Division by zero)

warn_potential_division_by_zero(Ann, Op, Args) ->
    case {Op, Args} of
        {{'/', _}, [_, {int, _, 0}]} -> aeso_ets_manager:ets_insert(warnings, {division_by_zero, Ann});
        _ -> ok
    end.

%% Warnings (Negative spends)

warn_potential_negative_spend(Ann, Fun, Args) ->
    case {Fun, Args} of
        { {typed, _, {qid, _, ["Chain", "spend"]}, _}
        , [_, {typed, _, {app, _, {'-', _}, [{typed, _, {int, _, X}, _}]}, _}]} when X > 0 ->
            aeso_ets_manager:ets_insert(warnings, {negative_spend, Ann});
        _ -> ok
    end.

destroy_and_report_warnings_as_type_errors() ->
    Warnings = [ mk_warning(Warn) || Warn <- aeso_ets_manager:ets_tab2list(warnings) ],
    Errors = lists:map(fun mk_t_err_from_warn/1, Warnings),
    aeso_errors:throw(Errors).  %% No-op if Warnings == []

mk_t_err_from_warn(Warn) ->
    aeso_warnings:warn_to_err(type_error, Warn).

mk_warning({unused_include, FileName, SrcFile}) ->
    Msg = io_lib:format("The file `~s` is included but not used.", [FileName]),
    aeso_warnings:new(aeso_errors:pos(SrcFile, 0, 0), Msg);
mk_warning({unused_stateful, Ann, FunName}) ->
    Msg = io_lib:format("The function `~s` is unnecessarily marked as stateful.", [name(FunName)]),
    aeso_warnings:new(pos(Ann), Msg);
mk_warning({unused_variable, Ann, _Namespace, _Fun, VarName}) ->
    Msg = io_lib:format("The variable `~s` is defined but never used.", [VarName]),
    aeso_warnings:new(pos(Ann), Msg);
mk_warning({unused_constant, Ann, _Namespace, ConstName}) ->
    Msg = io_lib:format("The constant `~s` is defined but never used.", [ConstName]),
    aeso_warnings:new(pos(Ann), Msg);
mk_warning({unused_typedef, Ann, QName, _Arity}) ->
    Msg = io_lib:format("The type `~s` is defined but never used.", [lists:last(QName)]),
    aeso_warnings:new(pos(Ann), Msg);
mk_warning({unused_return_value, Ann}) ->
    Msg = io_lib:format("Unused return value.", []),
    aeso_warnings:new(pos(Ann), Msg);
mk_warning({unused_function, Ann, FunName}) ->
    Msg = io_lib:format("The function `~s` is defined but never used.", [FunName]),
    aeso_warnings:new(pos(Ann), Msg);
mk_warning({shadowing, Ann, VarName, AnnOld}) ->
    Msg = io_lib:format("The definition of `~s` shadows an older definition at ~s.", [VarName, pp_loc(AnnOld)]),
    aeso_warnings:new(pos(Ann), Msg);
mk_warning({division_by_zero, Ann}) ->
    Msg = io_lib:format("Division by zero.", []),
    aeso_warnings:new(pos(Ann), Msg);
mk_warning({negative_spend, Ann}) ->
    Msg = io_lib:format("Negative spend.", []),
    aeso_warnings:new(pos(Ann), Msg);
mk_warning(Warn) ->
    Msg = io_lib:format("Unknown warning: ~p", [Warn]),
    aeso_warnings:new(Msg).
