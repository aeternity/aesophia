-module(aeso_tc_unify).

-export([unify/4]).

%% -- Circular dependency ----------------------------------------------------

opposite_variance(A) -> aeso_ast_infer_types:opposite_variance(A).

%% -- Moved functions --------------------------------------------------------

unfold_types_in_type(A, B, C) -> aeso_tc_type_unfolding:unfold_types_in_type(A, B, C).

%% -------

type_error(A) -> aeso_tc_errors:type_error(A).
cannot_unify(A, B, C, D) -> aeso_tc_errors:cannot_unify(A, B, C, D).

%% ---------------------------------------------------------------------------

unify(Env, A, B, When) -> unify0(Env, A, B, covariant, When).

unify0(_, {id, _, "_"}, _, _Variance, _When) -> true;
unify0(_, _, {id, _, "_"}, _Variance, _When) -> true;
unify0(Env, A, B, Variance, When) ->
    Options =
        case When of    %% Improve source location for map_in_map_key errors
            {check_expr, E, _, _} -> [{ann, aeso_syntax:get_ann(E)}];
            _                     -> []
        end,
    A1 = aeso_tc_type_utils:dereference(unfold_types_in_type(Env, A, Options)),
    B1 = aeso_tc_type_utils:dereference(unfold_types_in_type(Env, B, Options)),
    unify1(Env, A1, B1, Variance, When).

unify1(_Env, {uvar, _, R}, {uvar, _, R}, _Variance, _When) ->
    true;
unify1(_Env, {uvar, _, _}, {fun_t, _, _, var_args, _}, _Variance, When) ->
    type_error({unify_varargs, When});
unify1(Env, {uvar, A, R}, T, _Variance, When) ->
    case occurs_check(R, T) of
        true ->
            case aeso_tc_env:unify_throws(Env) of
                true ->
                    cannot_unify({uvar, A, R}, T, none, When);
                false ->
                    ok
            end,
            false;
        false ->
            aeso_tc_ets_manager:ets_insert(type_vars, {R, T}),
            true
    end;
unify1(Env, T, {uvar, A, R}, Variance, When) ->
    unify1(Env, {uvar, A, R}, T, Variance, When);
unify1(_Env, {tvar, _, X}, {tvar, _, X}, _Variance, _When) -> true; %% Rigid type variables
unify1(Env, [A|B], [C|D], [V|Variances], When) ->
    unify0(Env, A, C, V, When) andalso unify0(Env, B, D, Variances, When);
unify1(Env, [A|B], [C|D], Variance, When) ->
    unify0(Env, A, C, Variance, When) andalso unify0(Env, B, D, Variance, When);
unify1(_Env, X, X, _Variance, _When) ->
    true;
unify1(_Env, _A, {id, _, "void"}, Variance, _When)
  when Variance == covariant orelse Variance == bivariant ->
    true;
unify1(_Env, {id, _, "void"}, _B, Variance, _When)
  when Variance == contravariant orelse Variance == bivariant ->
    true;
unify1(_Env, {id, _, Name}, {id, _, Name}, _Variance, _When) ->
    true;
unify1(Env, A = {con, _, NameA}, B = {con, _, NameB}, Variance, When) ->
    case is_subtype(Env, NameA, NameB, Variance) of
        true -> true;
        false ->
            case aeso_tc_env:unify_throws(Env) of
                true ->
                    IsSubtype = is_subtype(Env, NameA, NameB, contravariant) orelse
                                is_subtype(Env, NameA, NameB, covariant),
                    Cxt = case IsSubtype of
                              true  -> Variance;
                              false -> none
                          end,
                    cannot_unify(A, B, Cxt, When);
                false ->
                    ok
            end,
            false
    end;
unify1(_Env, {qid, _, Name}, {qid, _, Name}, _Variance, _When) ->
    true;
unify1(_Env, {qcon, _, Name}, {qcon, _, Name}, _Variance, _When) ->
    true;
unify1(_Env, {bytes_t, _, Len}, {bytes_t, _, Len}, _Variance, _When) ->
    true;
unify1(Env, {if_t, _, {id, _, Id}, Then1, Else1}, {if_t, _, {id, _, Id}, Then2, Else2}, Variance, When) ->
    unify0(Env, Then1, Then2, Variance, When) andalso
    unify0(Env, Else1, Else2, Variance, When);

unify1(_Env, {fun_t, _, _, _, _}, {fun_t, _, _, var_args, _}, _Variance, When) ->
    type_error({unify_varargs, When});
unify1(_Env, {fun_t, _, _, var_args, _}, {fun_t, _, _, _, _}, _Variance, When) ->
    type_error({unify_varargs, When});
unify1(Env, {fun_t, _, Named1, Args1, Result1}, {fun_t, _, Named2, Args2, Result2}, Variance, When)
  when length(Args1) == length(Args2) ->
    unify0(Env, Named1, Named2, opposite_variance(Variance), When) andalso
    unify0(Env, Args1, Args2, opposite_variance(Variance), When) andalso
    unify0(Env, Result1, Result2, Variance, When);
unify1(Env, {app_t, _, {Tag, _, F}, Args1}, {app_t, _, {Tag, _, F}, Args2}, Variance, When)
  when length(Args1) == length(Args2), Tag == id orelse Tag == qid ->
    Variances = case aeso_tc_ets_manager:ets_lookup(type_vars_variance, F) of
                    [{_, Vs}] ->
                        case Variance of
                            contravariant -> lists:map(fun opposite_variance/1, Vs);
                            invariant     -> invariant;
                            _             -> Vs
                        end;
                    _ -> invariant
                end,
    unify1(Env, Args1, Args2, Variances, When);
unify1(Env, {tuple_t, _, As}, {tuple_t, _, Bs}, Variance, When)
  when length(As) == length(Bs) ->
    unify0(Env, As, Bs, Variance, When);
unify1(Env, {named_arg_t, _, Id1, Type1, _}, {named_arg_t, _, Id2, Type2, _}, Variance, When) ->
    unify1(Env, Id1, Id2, Variance, {arg_name, Id1, Id2, When}),
    unify1(Env, Type1, Type2, Variance, When);
%% The grammar is a bit inconsistent about whether types without
%% arguments are represented as applications to an empty list of
%% parameters or not. We therefore allow them to unify.
unify1(Env, {app_t, _, T, []}, B, Variance, When) ->
    unify0(Env, T, B, Variance, When);
unify1(Env, A, {app_t, _, T, []}, Variance, When) ->
    unify0(Env, A, T, Variance, When);
unify1(Env, A, B, _Variance, When) ->
    case aeso_tc_env:unify_throws(Env) of
        true ->
            cannot_unify(A, B, none, When);
        false ->
            ok
    end,
    false.

is_subtype(_Env, NameA, NameB, invariant) ->
    NameA == NameB;
is_subtype(Env, NameA, NameB, covariant) ->
    is_subtype(Env, NameA, NameB);
is_subtype(Env, NameA, NameB, contravariant) ->
    is_subtype(Env, NameB, NameA);
is_subtype(Env, NameA, NameB, bivariant) ->
    is_subtype(Env, NameA, NameB) orelse is_subtype(Env, NameB, NameA).

is_subtype(Env, Child, Base) ->
    Parents = maps:get(Child, aeso_tc_env:contract_parents(Env), []),
    if
        Child == Base ->
            true;
        Parents == [] ->
            false;
        true ->
            case lists:member(Base, Parents) of
                true -> true;
                false -> lists:any(fun(Parent) -> is_subtype(Env, Parent, Base) end, Parents)
            end
    end.

occurs_check(R, T) ->
    occurs_check1(R, aeso_tc_type_utils:dereference(T)).

occurs_check1(R, {uvar, _, R1}) -> R == R1;
occurs_check1(_, {id, _, _}) -> false;
occurs_check1(_, {con, _, _}) -> false;
occurs_check1(_, {qid, _, _}) -> false;
occurs_check1(_, {qcon, _, _}) -> false;
occurs_check1(_, {tvar, _, _}) -> false;
occurs_check1(_, {bytes_t, _, _}) -> false;
occurs_check1(R, {fun_t, _, Named, Args, Res}) ->
    occurs_check(R, [Res, Named | Args]);
occurs_check1(R, {app_t, _, T, Ts}) ->
    occurs_check(R, [T | Ts]);
occurs_check1(R, {tuple_t, _, Ts}) ->
    occurs_check(R, Ts);
occurs_check1(R, {named_arg_t, _, _, T, _}) ->
    occurs_check(R, T);
occurs_check1(R, {record_t, Fields}) ->
    occurs_check(R, Fields);
occurs_check1(R, {field_t, _, _, T}) ->
    occurs_check(R, T);
occurs_check1(R, {if_t, _, _, Then, Else}) ->
    occurs_check(R, [Then, Else]);
occurs_check1(R, [H | T]) ->
    occurs_check(R, H) orelse occurs_check(R, T);
occurs_check1(_, []) -> false.
