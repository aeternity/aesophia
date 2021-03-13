
-define(op(Ann, A, Op, B), {app, [{format, infix}|Ann], {Op, Ann}, [A, B]}).
-define(op(Ann, Op, B), {app, [{format, prefix}|Ann], {Op, Ann}, [B]}).

-define(int(Ann, I), {int, Ann, I}).
-define(int_tp, {id, _, "int"}).
-define(int_t(Ann), {id, Ann, "int"}).

-define(d_pos_int(Ann), ?refined(?int_t(Ann), [?op(Ann, ?nu(Ann), '>', ?int(Ann, 0))])).
-define(d_nonneg_int(Ann), ?refined(?int_t(Ann), [?op(Ann, ?nu(Ann), '>=', ?int(Ann, 0))])).
%% -define(d_nonzero_int, refined(?int_t, [?op(?nu(), '!=', ?int(0))])).

-define(bool(Ann, B), {bool, Ann, B}).
-define(bool_tp, {id, _, "bool"}).
-define(bool_t(Ann), {id, Ann, "bool"}).

%% -define(tuple(S), {tuple, _, S}).
-define(tuple_tp(T), {tuple_t, _, T}).
%% -define(tuple_t(T), {tuple_t, ?ann(), T}).

-define(tuple_proj_id(Ann, N, I),
        {id, Ann, lists:flatten(io_lib:format("$tuple~p.~p", [N, I]))}).
-define(adt_proj_id(Ann, QCon, I),
        {id, Ann, lists:flatten(io_lib:format("~s.~p", [string:join(qname(QCon), "."), I]))}).

%% -define(string(S), {string, _, S}).
-define(string_tp, {id, _, "string"}).
%% -define(string_t, {id, ?ann(), "string"}).

-define(typed(Expr, Type), {typed, element(2, Expr), Expr, Type}).
-define(typed_p(Expr), {typed, _, Expr, _}).
-define(typed_p(Expr, Type), {typed, _, Expr, Type}).

-define(refined(Id, T, Q),
    {refined_t, element(2, T), Id, T, Q}).
-define(refined(T, Q),
    (fun(Id) ->
            ?refined(Id, T, apply_subst(?nu(element(2, T)), Id, Q))
     end)
      (fresh_id(
         element(2, T),
         case T of
             ?int_tp -> "n";
             ?bool_tp -> "b";
             ?string_tp -> "s";
             _ when element(1, T) == id -> name(T);
             _ -> "v"
         end
        ))).
-define(refined(T), ?refined(T, [])).

-define(ann(), [{origin, hagia}]).
-define(ann_of(E), element(2, E)).

-define(nu(Ann), {id, Ann, "$self"}).
-define(nu_p, {id, _, "$self"}).
