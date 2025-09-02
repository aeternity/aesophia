%%%-------------------------------------------------------------------
%%% @copyright (C) 2025, Aeternity Anstalt
%%% @doc Type unification utilities for Sophia.
%%% @end
%%%-------------------------------------------------------------------
-module(aeso_type_unify).


-include("aeso_types.hrl").

-export([
    dereference/1,
    dereference_deep/1,
    fresh_uvar/1,
    instantiate/1,
    opposite_variance/1,
    unify/4
]).

%% -------------------------------------------------------------------
%% Dereferencing
%% -------------------------------------------------------------------

dereference(T = {uvar, _, R}) ->
    case aeso_infer_ets:lookup(type_vars, R) of
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

%% -------------------------------------------------------------------
%% Occurs check
%% -------------------------------------------------------------------

occurs_check(R, T) ->
    occurs_check1(R, dereference(T)).

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

%% -------------------------------------------------------------------
%% Fresh variables
%% -------------------------------------------------------------------

fresh_uvar(Attrs) ->
    {uvar, Attrs, make_ref()}.

%% -------------------------------------------------------------------
%% Instantiation
%% -------------------------------------------------------------------

%% Dereferences all uvars and replaces the uninstantiated ones with a
%% succession of tvars.
instantiate(E) ->
    instantiate1(dereference(E)).

instantiate1({uvar, Attr, R}) ->
    Next = proplists:get_value(next, aeso_infer_ets:lookup(type_vars, next), 0),
    TVar = {tvar, Attr, "'" ++ integer_to_tvar(Next)},
    aeso_infer_ets:insert(type_vars, [{next, Next + 1}, {R, TVar}]),
    TVar;
instantiate1({fun_t, Ann, Named, Args, Ret}) ->
    case dereference(Named) of
        {uvar, _, R} ->
            %% Uninstantiated named args map to the empty list
            NoNames = [],
            aeso_infer_ets:insert(type_vars, [{R, NoNames}]),
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
    integer_to_tvar(X div 26 - 1) ++ [$a + (X rem 26)].

%% -------------------------------------------------------------------
%% Unification
%% -------------------------------------------------------------------

unify(Env, A, B, When) -> unify0(Env, A, B, covariant, When).

unify0(_, {id, _, "_"}, _, _Variance, _When) -> true;
unify0(_, _, {id, _, "_"}, _Variance, _When) -> true;
unify0(Env, A, B, Variance, When) ->
    Options =
        case When of    %% Improve source location for map_in_map_key errors
            {check_expr, E, _, _} -> [{ann, aeso_syntax:get_ann(E)}];
            _                     -> []
        end,
    A1 = dereference(aeso_type_unfold:unfold_types_in_type(Env, A, Options)),
    B1 = dereference(aeso_type_unfold:unfold_types_in_type(Env, B, Options)),
    unify1(Env, A1, B1, Variance, When).

unify1(_Env, {uvar, _, R}, {uvar, _, R}, _Variance, _When) ->
    true;
unify1(_Env, {uvar, _, _}, {fun_t, _, _, var_args, _}, _Variance, When) ->
    aeso_type_errors:type_error({unify_varargs, When}),
    false;
unify1(_Env, {uvar, A, R}, T, _Variance, When) ->
    case occurs_check(R, T) of
        true ->
            cannot_unify({uvar, A, R}, T, none, When),
            false;
        false ->
            aeso_infer_ets:insert(type_vars, {R, T}),
            true
    end;
unify1(Env, T, {uvar, A, R}, Variance, When) ->
    unify1(Env, {uvar, A, R}, T, Variance, When);
unify1(_Env, {tvar, _, X}, {tvar, _, X}, _Variance, _When) -> true; %% Rigid type variables
unify1(Env, [A|B], [C|D], [V|Variances], When) ->
    unify0(Env, A, C, V, When) and unify0(Env, B, D, Variances, When);
unify1(Env, [A|B], [C|D], Variance, When) ->
    unify0(Env, A, C, Variance, When) and unify0(Env, B, D, Variance, When);
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
            IsSubtype = is_subtype(Env, NameA, NameB, contravariant) orelse
                        is_subtype(Env, NameA, NameB, covariant),
            Cxt = case IsSubtype of
                      true  -> Variance;
                      false -> none
                  end,
            cannot_unify(A, B, Cxt, When),
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
    aeso_type_errors:type_error({unify_varargs, When}),
    false;
unify1(_Env, {fun_t, _, _, var_args, _}, {fun_t, _, _, _, _}, _Variance, When) ->
    aeso_type_errors:type_error({unify_varargs, When}),
    false;
unify1(Env, {fun_t, _, Named1, Args1, Result1}, {fun_t, _, Named2, Args2, Result2}, Variance, When)
  when length(Args1) == length(Args2) ->
    unify0(Env, Named1, Named2, opposite_variance(Variance), When) and
    unify0(Env, Args1, Args2, opposite_variance(Variance), When) and
    unify0(Env, Result1, Result2, Variance, When);
unify1(Env, {app_t, _, {Tag, _, F}, Args1}, {app_t, _, {Tag, _, F}, Args2}, Variance, When)
  when length(Args1) == length(Args2), Tag == id orelse Tag == qid ->
    Variances = case aeso_infer_ets:lookup(type_vars_variance, F) of
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
    unify1(Env, Id1, Id2, Variance, {arg_name, Id1, Id2, When}) andalso
    unify1(Env, Type1, Type2, Variance, When);
%% The grammar is a bit inconsistent about whether types without
%% arguments are represented as applications to an empty list of
%% parameters or not. We therefore allow them to unify.
unify1(Env, {app_t, _, T, []}, B, Variance, When) ->
    unify0(Env, T, B, Variance, When);
unify1(Env, A, {app_t, _, T, []}, Variance, When) ->
    unify0(Env, A, T, Variance, When);
unify1(_Env, A, B, _Variance, When) ->
    cannot_unify(A, B, none, When),
    false.

%% -------------------------------------------------------------------
%% Subtyping
%% -------------------------------------------------------------------

is_subtype(_Env, NameA, NameB, invariant) ->
    NameA == NameB;
is_subtype(Env, NameA, NameB, covariant) ->
    is_subtype(Env, NameA, NameB);
is_subtype(Env, NameA, NameB, contravariant) ->
    is_subtype(Env, NameB, NameA);
is_subtype(Env, NameA, NameB, bivariant) ->
    is_subtype(Env, NameA, NameB) orelse is_subtype(Env, NameB, NameA).

is_subtype(Env, Child, Base) ->
    Parents = maps:get(Child, Env#env.contract_parents, []),
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

%% -------------------------------------------------------------------
%% Variance helpers
%% -------------------------------------------------------------------

opposite_variance(invariant) -> invariant;
opposite_variance(covariant) -> contravariant;
opposite_variance(contravariant) -> covariant;
opposite_variance(bivariant) -> bivariant.

%% -------------------------------------------------------------------
%% Error reporting
%% -------------------------------------------------------------------

%% Save unification failures for error messages.
cannot_unify(A, B, Cxt, When) ->
    aeso_type_errors:type_error({cannot_unify, A, B, Cxt, When}).