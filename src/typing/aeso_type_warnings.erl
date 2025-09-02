%%%-------------------------------------------------------------------
%%% @copyright (C) 2018, Aeternity Anstalt
%%% @doc
%%%     Type warning generation and tracking for Sophia type checker.
%%%     This module provides warning creation functions and handles tracking
%%%     of various unused constructs (includes, stateful, typedefs, etc).
%%% @end
%%%-------------------------------------------------------------------

-module(aeso_type_warnings).

-include("aeso_types.hrl").

-export([
    mk_warning/1,
    potential_unused_include/2,
    used_include/1,
    potential_unused_stateful/2,
    used_stateful/1,
    potential_unused_typedefs/2,
    used_typedef/2,
    potential_unused_variables/3,
    used_variable/3,
    potential_unused_constants/2,
    used_constant/2,
    potential_unused_return_value/1,
    warn_potential_division_by_zero/3,
    warn_potential_negative_spend/3,
    warn_potential_shadowing/3,
    when_warning/2,
    create_unused_functions/0,
    register_function_call/2,
    potential_unused_function/4,
    remove_used_funs/1,
    destroy_and_report_unused_functions/0
]).



%% Helper functions for mk_warning
pos(T)    -> aeso_errors:pos(aeso_syntax:get_ann(file, T, no_file),
                             aeso_syntax:get_ann(line, T, 0),
                             aeso_syntax:get_ann(col, T, 0)).

pp_loc(T) -> aeso_type_pretty:pp_loc(T).

name({typed, _, X, _}) -> name(X);
name({id, _, X}) -> X;
name({con, _, X}) -> X.

%% Main warning creation function
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

%% -------------------------------------------------------------------
%% Functions for tracking and reporting unused code warnings
%% -------------------------------------------------------------------

%% Include warnings
potential_unused_include(Ann, SrcFile) ->
    IsIncluded = aeso_syntax:get_ann(include_type, Ann, none) =/= none,
    case IsIncluded of
        false -> ok;
        true  ->
            case aeso_syntax:get_ann(file, Ann, no_file) of
                no_file -> ok;
                File    -> aeso_type_ets:insert(warnings, {unused_include, File, SrcFile})
            end
    end.

used_include(Ann) ->
    case aeso_syntax:get_ann(file, Ann, no_file) of
        no_file -> ok;
        File    -> aeso_type_ets:match_delete(warnings, {unused_include, File, '_'})
    end.

%% Stateful warnings
potential_unused_stateful(Ann, Fun) ->
    case aeso_syntax:get_ann(stateful, Ann, false) of
        false -> ok;
        true  -> aeso_type_ets:insert(warnings, {unused_stateful, Ann, Fun})
    end.

used_stateful(Fun) ->
    aeso_type_ets:match_delete(warnings, {unused_stateful, '_', Fun}).

%% Typedef warnings
potential_unused_typedefs(Namespace, TypeDefs) ->
    lists:map(
      fun({type_def, _Ann, {id, _, "event"}, _Args, _}) ->
              ok;
         ({type_def, Ann, Id, Args, _}) ->
              aeso_type_ets:insert(warnings, {unused_typedef, Ann, Namespace ++ qname(Id), length(Args)})
      end,
      TypeDefs
     ).

used_typedef(TypeAliasId, Arity) ->
    aeso_type_ets:match_delete(warnings, {unused_typedef, '_', qname(TypeAliasId), Arity}).

%% Variable warnings
potential_unused_variables(Namespace, Fun, Vars0) ->
    Vars = [ Var || Var = {id, _, VarName} <- Vars0, VarName /= "_" ],
    lists:map(fun({id, Ann, VarName}) ->
        aeso_type_ets:insert(warnings, {unused_variable, Ann, Namespace, Fun, VarName}) end, Vars).

used_variable(Namespace, Fun, [VarName]) ->
    aeso_type_ets:match_delete(warnings, {unused_variable, '_', Namespace, Fun, VarName});
used_variable(_, _, _) -> ok.

%% Constant warnings
potential_unused_constants(#env{ what = namespace }, _Consts) ->
    [];
potential_unused_constants(#env{ namespace = Namespace }, Consts) ->
    [ aeso_type_ets:insert(warnings, {unused_constant, Ann, Namespace, Name}) || {letval, _, {id, Ann, Name}, _} <- Consts ].

used_constant(Namespace = [Contract], [Contract, ConstName]) ->
    aeso_type_ets:match_delete(warnings, {unused_constant, '_', Namespace, ConstName});
used_constant(_, _) -> ok.

%% Return value warnings
potential_unused_return_value({typed, Ann, {app, _, {typed, _, _, {fun_t, _, _, _, {id, _, Type}}}, _}, _}) when Type /= "unit" ->
    aeso_type_ets:insert(warnings, {unused_return_value, Ann});
potential_unused_return_value(_) -> ok.

%% Division by zero warnings
warn_potential_division_by_zero(Ann, Op, Args) ->
    case {Op, Args} of
        {{'/', _}, [_, {int, _, 0}]} -> aeso_type_ets:insert(warnings, {division_by_zero, Ann});
        _ -> ok
    end.

%% Negative spend warnings
warn_potential_negative_spend(Ann, Fun, Args) ->
    case {Fun, Args} of
        { {typed, _, {qid, _, ["Chain", "spend"]}, _}
        , [_, {typed, _, {app, _, {'-', _}, [{typed, _, {int, _, X}, _}]}, _}]} when X > 0 ->
            aeso_type_ets:insert(warnings, {negative_spend, Ann});
        _ -> ok
    end.

%% Unused function warnings
create_unused_functions() ->
    aeso_type_ets:new(function_calls, [bag]),
    aeso_type_ets:new(all_functions, [set]).

register_function_call(Caller, Callee) ->
    aeso_type_ets:insert(function_calls, {Caller, Callee}).

potential_unused_function(#env{ what = namespace }, Ann, FunQName, FunId) ->
    aeso_type_ets:insert(all_functions, {Ann, FunQName, FunId, not aeso_syntax:get_ann(private, Ann, false)});
potential_unused_function(_Env, Ann, FunQName, FunId) ->
    aeso_type_ets:insert(all_functions, {Ann, FunQName, FunId, aeso_syntax:get_ann(entrypoint, Ann, false)}).

remove_used_funs(All) ->
    {Used, Unused} = lists:partition(fun({_, _, _, IsUsed}) -> IsUsed end, All),
    CallsByUsed = lists:flatmap(fun({_, F, _, _}) -> aeso_type_ets:lookup(function_calls, F) end, Used),
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
    AllFuns = aeso_type_ets:tab2list(all_functions),
    lists:map(fun({Ann, _, FunId, _}) -> aeso_type_ets:insert(warnings, {unused_function, Ann, name(FunId)}) end,
              remove_used_funs(AllFuns)),
    aeso_type_ets:delete(all_functions),
    aeso_type_ets:delete(function_calls).

%% Warning for potential variable shadowing
warn_potential_shadowing(_, _, "_") -> ok;
warn_potential_shadowing(Env = #env{ vars = Vars }, Ann, Name) ->
    CurrentScope = aeso_type_env:get_current_scope(Env),
    Consts = CurrentScope#scope.consts,
    case proplists:get_value(Name, Vars ++ Consts, false) of
        false -> ok;
        {AnnOld, _} -> aeso_type_ets:insert(warnings, {shadowing, Ann, Name, AnnOld})
    end.

%% -------------------------------------------------------------------
%% Helper functions (merged and deduplicated)
%% -------------------------------------------------------------------

qname({id, _, Name}) -> [Name];
qname({qid, _, Names}) -> Names;
qname({con, _, Name}) -> [Name];
qname({qcon, _, Names}) -> Names.

%% Warning management functions
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

when_warning(Warn, Do) ->
    case lists:member(Warn, all_warnings()) of
        false ->
            aeso_type_errors:create_type_errors(),
            aeso_type_errors:type_error({unknown_warning, Warn}),
            aeso_type_errors:destroy_and_report_type_errors(aeso_type_env:global_env());
        true ->
            case aeso_type_ets:tab_exists(warnings) of
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

%% Options management (duplicated from aeso_type_infer to avoid dependency)
get_option(Key, Default) ->
    case aeso_type_ets:lookup(options, Key) of
        [{Key, Val}] -> Val;
        _            -> Default
    end.
