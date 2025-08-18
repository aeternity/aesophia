%%%-------------------------------------------------------------------
%%% @doc Fcode optimization passes (inlining, binding, let-floating,
%%%      simplification, dropping unused lets, dead code elimination).
%%%      Extracted from `aeso_ast_to_fcode` without semantic changes.
%%%-------------------------------------------------------------------
-module(aeso_fcode_opt).

-export([optimize_fcode/2]).

-spec optimize_fcode(aeso_ast_to_fcode:fcode(), [term()]) -> aeso_ast_to_fcode:fcode().
optimize_fcode(Code = #{ functions := Funs }, Options) ->
    Code1 = Code#{ functions := maps:map(fun(Name, Def) -> optimize_fun(Code, Name, Def, Options) end, Funs) },
    eliminate_dead_code(Code1).

-spec optimize_fun(aeso_ast_to_fcode:fcode(), aeso_ast_to_fcode:fun_name(), aeso_ast_to_fcode:fun_def(), [term()]) -> aeso_ast_to_fcode:fun_def().
optimize_fun(Fcode, Fun, Def = #{ body := Body0 }, Options) ->
    Inliner              = proplists:get_value(optimize_inliner,                Options, true),
    InlineLocalFunctions = proplists:get_value(optimize_inline_local_functions, Options, true),
    BindSubexpressions   = proplists:get_value(optimize_bind_subexpressions,    Options, true),
    LetFloating          = proplists:get_value(optimize_let_floating,           Options, true),
    Simplifier           = proplists:get_value(optimize_simplifier,             Options, true),
    DropUnusedLets       = proplists:get_value(optimize_drop_unused_lets,       Options, true),

    Body1 = if Inliner              -> inliner   (Fcode, Fun, Body0); true -> Body0 end,
    Body2 = if InlineLocalFunctions -> inline_local_functions(Body1); true -> Body1 end,
    Body3 = if BindSubexpressions   -> bind_subexpressions   (Body2); true -> Body2 end,
    Body4 = if LetFloating          -> let_floating          (Body3); true -> Body3 end,
    Body5 = if Simplifier           -> simplifier            (Body4); true -> Body4 end,
    Body6 = if DropUnusedLets       -> drop_unused_lets      (Body5); true -> Body5 end,

    Def#{ body := Body6 }.

%% --- Inlining ---

-spec inliner(aeso_ast_to_fcode:fcode(), aeso_ast_to_fcode:fun_name(), aeso_ast_to_fcode:fexpr()) -> aeso_ast_to_fcode:fexpr().
inliner(Fcode, Fun, {def, _, Fun1, Args} = E) when Fun1 /= Fun ->
    case should_inline(Fcode, Fun1) of
        false -> E;
        true  -> inline(Fcode, Fun1, Args)
    end;
inliner(_Fcode, _Fun, E) -> E.

-spec should_inline(aeso_ast_to_fcode:fcode(), aeso_ast_to_fcode:fun_name()) -> boolean().
should_inline(_Fcode, _Fun1) -> false == list_to_atom("true").

-spec inline(aeso_ast_to_fcode:fcode(), aeso_ast_to_fcode:fun_name(), [aeso_ast_to_fcode:fexpr()]) -> aeso_ast_to_fcode:fexpr().
inline(_Fcode, Fun, Args) -> {def, [], Fun, Args}. %% TODO actual inlining

%% --- Bind subexpressions ---

-define(make_lets(Xs, Es, Body), make_lets(Es, fun(Xs) -> Body end)).
-define(make_let(X, Expr, Body), aeso_ast_to_fcode:make_let(Expr, fun(X) -> Body end)).

-spec bind_subexpressions(aeso_ast_to_fcode:fexpr()) -> aeso_ast_to_fcode:fexpr().
bind_subexpressions(Expr) ->
    aeso_ast_to_fcode:bottom_up(fun bind_subexpressions/2, Expr).

-spec bind_subexpressions(aeso_ast_to_fcode:expr_env(), aeso_ast_to_fcode:fexpr()) -> aeso_ast_to_fcode:fexpr().
bind_subexpressions(_, {tuple, FAnn, Es}) ->
    ?make_lets(Xs, Es, {tuple, FAnn, Xs});
bind_subexpressions(_, {set_proj, FAnn, A, I, B}) ->
    ?make_lets([X, Y], [A, B], {set_proj, FAnn, X, I, Y});
bind_subexpressions(_, E) -> E.

-spec make_lets([aeso_ast_to_fcode:fexpr()], fun(([aeso_ast_to_fcode:fexpr()]) -> aeso_ast_to_fcode:fexpr())) -> aeso_ast_to_fcode:fexpr().
make_lets(Es, Body) -> make_lets(Es, [], Body).

-spec make_lets([aeso_ast_to_fcode:fexpr()], [aeso_ast_to_fcode:fexpr()], fun(([aeso_ast_to_fcode:fexpr()]) -> aeso_ast_to_fcode:fexpr())) -> aeso_ast_to_fcode:fexpr().
make_lets([], Xs, Body)       -> Body(lists:reverse(Xs));
make_lets([{var, _, _} = E | Es], Xs, Body) ->
    make_lets(Es, [E | Xs], Body);
make_lets([{lit, _, _} = E | Es], Xs, Body) ->
    make_lets(Es, [E | Xs], Body);
make_lets([E | Es], Xs, Body) ->
    ?make_let(X, E, make_lets(Es, [X | Xs], Body)).

%% --- Inline local functions ---

-spec inline_local_functions(aeso_ast_to_fcode:fexpr()) -> aeso_ast_to_fcode:fexpr().
inline_local_functions(Expr) ->
    aeso_ast_to_fcode:bottom_up(fun inline_local_functions/2, Expr).

-spec inline_local_functions(aeso_ast_to_fcode:expr_env(), aeso_ast_to_fcode:fexpr()) -> aeso_ast_to_fcode:fexpr().
inline_local_functions(Env, {funcall, _, {proj, _, {var, _, Y}, 0}, [{proj, _, {var, _, Y}, 1} | Args]} = Expr) ->
    case maps:get(Y, Env, free) of
        {lam, _, Xs, Body} -> aeso_ast_to_fcode:let_bind(lists:zip(Xs, Args), Body);
        _                  -> Expr
    end;
inline_local_functions(_, Expr) -> Expr.

%% --- Let-floating ---

-spec let_floating(aeso_ast_to_fcode:fexpr()) -> aeso_ast_to_fcode:fexpr().
let_floating(Expr) -> aeso_ast_to_fcode:bottom_up(fun let_float/2, Expr).

-spec let_float(aeso_ast_to_fcode:expr_env(), aeso_ast_to_fcode:fexpr()) -> aeso_ast_to_fcode:fexpr().
let_float(_, {'let', FAnn, X, E, Body}) ->
    pull_out_let({'let', FAnn, X, {here, E}, Body});
let_float(_, {proj, FAnn, E, I}) ->
    pull_out_let({proj, FAnn, {here, E}, I});
let_float(_, {set_proj, FAnn, E, I, V}) ->
    pull_out_let({set_proj, FAnn, {here, E}, I, {here, V}});
let_float(_, {op, FAnn, Op, Es}) ->
    {Lets, Es1} = pull_out_let([{here, E} || E <- Es]),
    aeso_ast_to_fcode:let_bind(Lets, {op, FAnn, Op, Es1});
let_float(_, E) -> E.

-spec pull_out_let(aeso_ast_to_fcode:fexpr() | [aeso_ast_to_fcode:fexpr()]) -> aeso_ast_to_fcode:fexpr() | {Lets, [aeso_ast_to_fcode:fexpr()]} when
      Lets :: [{aeso_ast_to_fcode:var_name(), aeso_ast_to_fcode:fexpr()}].
pull_out_let(Expr) when is_tuple(Expr) ->
    {Lets, Es} = pull_out_let(tuple_to_list(Expr)),
    Inner = list_to_tuple(Es),
    aeso_ast_to_fcode:let_bind(Lets, Inner);
pull_out_let(Es) when is_list(Es) ->
    case lists:splitwith(fun({here, _}) -> false; (_) -> true end, Es) of
        {Es0, [{here, E} | Es1]} ->
            case aeso_ast_to_fcode:let_view(E) of
                {[], _}    ->
                    {Lets, Es2} = pull_out_let(Es1),
                    {Lets, Es0 ++ [E] ++ Es2};
                {Lets, E1} ->
                    {Lets1, Es2} = pull_out_let(Es1),
                    {Lets ++ Lets1, Es0 ++ [E1] ++ Es2}
            end;
        {_, []} -> {[], Es}
    end.

%% --- Simplification ---

-spec simplifier(aeso_ast_to_fcode:fexpr()) -> aeso_ast_to_fcode:fexpr().
simplifier(Expr) ->
    aeso_ast_to_fcode:bottom_up(fun simplify/2, Expr).

-spec simplify(aeso_ast_to_fcode:expr_env(), aeso_ast_to_fcode:fexpr()) -> aeso_ast_to_fcode:fexpr().
simplify(_Env, {proj, FAnn, {tuple, _, Es}, I}) ->
    It  = lists:nth(I + 1, Es),
    X   = aeso_ast_to_fcode:fresh_name(),
    Dup = aeso_ast_to_fcode:safe_to_duplicate(It),
    Val = if Dup -> It; true -> {var, FAnn, X} end,
    lists:foldr(
      fun({J, E}, Rest) when I == J ->
            case Dup of
                true  -> Rest;
                false -> {'let', FAnn, X, E, Rest}
            end;
         ({_, E}, Rest) ->
            case aeso_ast_to_fcode:read_only(E) of
                true  -> Rest;
                false -> {'let', FAnn, "_", E, Rest}
            end
        end, Val, aeso_ast_to_fcode:indexed(Es));
simplify(Env, {proj, _, Var = {var, _, _}, I} = Expr) ->
    case simpl_proj(Env, I, Var) of
        false -> Expr;
        E     -> E
    end;
simplify(Env, {switch, FAnn, Split}) ->
    case simpl_switch(Env, FAnn, [], Split) of
        nomatch -> {builtin, FAnn, abort, [{lit, FAnn, {string, <<"Incomplete patterns">>}}]};
        Expr    -> Expr
    end;
simplify(_, E) ->
    E.

-spec simpl_proj(aeso_ast_to_fcode:expr_env(), integer(), aeso_ast_to_fcode:fexpr()) -> aeso_ast_to_fcode:fexpr() | false.
simpl_proj(Env, I, Expr) ->
    IfSafe = fun(E) -> case aeso_ast_to_fcode:safe_to_duplicate(E) of
                         true -> E;
                         false -> false
                       end end,
    case Expr of
        false                    -> false;
        {var, _, X}              -> simpl_proj(Env, I, maps:get(X, Env, false));
        {tuple, _, Es}           -> IfSafe(lists:nth(I + 1, Es));
        {set_proj, _, _, I, Val} -> IfSafe(Val);
        {set_proj, _, E, _, _}   -> simpl_proj(Env, I, E);
        {proj, _, E, J}          -> simpl_proj(Env, I, simpl_proj(Env, J, E));
        _                        -> false
    end.

-spec get_catchalls([aeso_ast_to_fcode:fcase()]) -> [aeso_ast_to_fcode:fcase()].
get_catchalls(Alts) ->
    [ C || C = {'case', {var, _}, _} <- Alts ].

-spec add_catchalls([aeso_ast_to_fcode:fcase()], [aeso_ast_to_fcode:fcase()]) -> [aeso_ast_to_fcode:fcase()].
add_catchalls(Alts, []) -> Alts;
add_catchalls(Alts, Catchalls) ->
    case lists:splitwith(fun({'case', {var, _}, _}) -> false; (_) -> true end,
                         Alts) of
        {Alts1, [C]} -> Alts1 ++ [nest_catchalls([C | Catchalls])];
        {_, []}      -> Alts  ++ [nest_catchalls(Catchalls)]
    end.

-spec nest_catchalls([aeso_ast_to_fcode:fcase()]) -> aeso_ast_to_fcode:fcase().
nest_catchalls([C = {'case', {var, _}, {nosplit, _, _}} | _]) -> C;
nest_catchalls([{'case', P = {var, _}, {split, Type, X, Alts}} | Catchalls]) ->
    {'case', P, {split, Type, X, add_catchalls(Alts, Catchalls)}}.

-spec simpl_switch(aeso_ast_to_fcode:expr_env(), aeso_ast_to_fcode:fann(), [aeso_ast_to_fcode:fcase()], aeso_ast_to_fcode:fsplit()) -> aeso_ast_to_fcode:fexpr() | nomatch.
simpl_switch(_Env, _FAnn, _, {nosplit, _, E}) -> E;
simpl_switch(Env, FAnn, Catchalls, {split, Type, X, Alts}) ->
    Alts1 = add_catchalls(Alts, Catchalls),
    Stuck = {switch, FAnn, {split, Type, X, Alts1}},
    case aeso_ast_to_fcode:constructor_form(Env, {var, [], X}) of
        false -> Stuck;
        E     -> simpl_case(Env, E, Alts1)
    end.

-spec simpl_case(aeso_ast_to_fcode:expr_env(), aeso_ast_to_fcode:fexpr(), [aeso_ast_to_fcode:fcase()]) -> aeso_ast_to_fcode:fexpr() | nomatch.
simpl_case(_, _, []) -> nomatch;
simpl_case(Env, E, [{'case', Pat, Body} | Alts]) ->
    case match_pat(Pat, E) of
        false -> simpl_case(Env, E, Alts);
        Binds ->
            Env1 = maps:merge(Env, maps:from_list(Binds)),
            case simpl_switch(Env1, aeso_ast_to_fcode:get_fann(E), get_catchalls(Alts), Body) of
                nomatch -> simpl_case(Env, E, Alts);
                Body1   -> aeso_ast_to_fcode:let_bind(Binds, Body1)
            end
    end.

-spec match_pat(aeso_ast_to_fcode:fsplit_pat(), aeso_ast_to_fcode:fexpr()) -> false | [{aeso_ast_to_fcode:var_name(), aeso_ast_to_fcode:fexpr()}].
match_pat({tuple, Xs}, {tuple, _, Es})         -> lists:zip(Xs, Es);
match_pat({con, _, C, Xs}, {con, _, _, C, Es}) -> lists:zip(Xs, Es);
match_pat(L, {lit, _, L})                      -> [];
match_pat(nil, {nil, _})                       -> [];
match_pat({'::', X, Y}, {op, _, '::', [A, B]}) -> [{X, A}, {Y, B}];
match_pat({var, X}, E)                         -> [{X, E}];
match_pat({assign, X, P}, E)                   -> [{X, E}, {P, E}];
match_pat(_, _)                                -> false.

%% --- Drop unused lets ---

-spec drop_unused_lets(aeso_ast_to_fcode:fexpr()) -> aeso_ast_to_fcode:fexpr().
drop_unused_lets(Expr) -> aeso_ast_to_fcode:bottom_up(fun drop_unused_lets/2, Expr).

-spec drop_unused_lets(aeso_ast_to_fcode:expr_env(), aeso_ast_to_fcode:fexpr()) -> aeso_ast_to_fcode:fexpr().
drop_unused_lets(_, {'let', FAnn, X, E, Body} = Expr) ->
    case {aeso_ast_to_fcode:read_only(E), not lists:member(X, aeso_ast_to_fcode:free_vars(Body))} of
        {true, true}  -> Body;
        {false, true} -> {'let', FAnn, "_", E, Body};
        _             -> Expr
    end;
drop_unused_lets(_, Expr) -> Expr.

%% --- Deadcode elimination ---

-spec eliminate_dead_code(aeso_ast_to_fcode:fcode()) -> aeso_ast_to_fcode:fcode().
eliminate_dead_code(Code = #{ functions := Funs }) ->
    UsedFuns = used_functions(Funs),
    Code#{ functions := maps:filter(fun(Name, _) -> maps:is_key(Name, UsedFuns) end,
                                    Funs) }.

-spec used_functions(aeso_ast_to_fcode:functions()) -> #{ aeso_ast_to_fcode:fun_name() => true }.
used_functions(Funs) ->
    Exported = [ Fun || {Fun, #{ attrs := Attrs }} <- maps:to_list(Funs),
                        not lists:member(private, Attrs) ],
    used_functions(#{}, Exported, Funs).

-spec used_functions(#{ aeso_ast_to_fcode:fun_name() => true }, [aeso_ast_to_fcode:fun_name()], aeso_ast_to_fcode:functions()) -> #{ aeso_ast_to_fcode:fun_name() => true }.
used_functions(Used, [], _) -> Used;
used_functions(Used, [Name | Rest], Defs) ->
    case maps:is_key(Name, Used) of
        true  -> used_functions(Used, Rest, Defs);
        false ->
            New =
                case maps:get(Name, Defs, undef) of
                    undef             -> [];
                    #{ body := Body } -> aeso_ast_to_fcode:used_defs(Body)
                end,
            used_functions(Used#{ Name => true }, New ++ Rest, Defs)
    end.


