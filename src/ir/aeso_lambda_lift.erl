%%%-------------------------------------------------------------------
%%% @doc Lambda lifting for Fexpr: converts lambdas into top-level functions
%%%      and replaces occurrences with closures. Extracted from
%%%      `aeso_ast_to_fcode` without semantic changes.
%%%-------------------------------------------------------------------
-module(aeso_lambda_lift).

-export([lambda_lift/1]).

-spec lambda_lift(aeso_ast_to_fcode:fcode()) -> aeso_ast_to_fcode:fcode().
lambda_lift(FCode = #{ functions := Funs, state_layout := StateLayout }) ->
    NewFuns =
        [ {FunName, FunDef}
          || {ParentName, ParentDef} <- maps:to_list(Funs),
             {NewParentDef, Lambdas} <- [lambda_lift_fun(StateLayout, ParentName, ParentDef)],
             {FunName, FunDef} <- [{ParentName, NewParentDef} | maps:to_list(Lambdas)]
        ],
    FCode#{ functions := maps:from_list(NewFuns) }.

-define(lambda_key, '%lambdalifted').

-spec init_lambda_funs() -> term().
init_lambda_funs() -> put(?lambda_key, #{}).

-spec get_lambda_funs() -> term().
get_lambda_funs()  ->
    Lambdas = erase(?lambda_key),
    %% Remove name feed entries and leave only actual functions
    maps:filter(fun({fresh, _}, _) -> false;
                   (_, _) -> true
                end, Lambdas).

-spec add_lambda_fun(aeso_ast_to_fcode:fun_name(), aeso_ast_to_fcode:fann(), aeso_ast_to_fcode:fun_def()) -> aeso_ast_to_fcode:fun_name().
add_lambda_fun(Parent, FAnn, Def) ->
    Funs = get(?lambda_key),
    LambdaId = maps:get({fresh, Parent}, Funs, 0),
    Name = lambda_name(FAnn, LambdaId, Parent),
    put(?lambda_key, Funs#{ Name => Def, {fresh, Parent} => LambdaId + 1}),
    Name.

-spec lambda_name(aeso_ast_to_fcode:fann(), non_neg_integer(), aeso_ast_to_fcode:fun_name()) -> aeso_ast_to_fcode:fun_name().
lambda_name(FAnn, Id, PName) ->
    PSName = case PName of
                 {entrypoint, N} -> [binary_to_list(N)];
                 {local_fun, Ns} -> Ns
             end,
    {_File, Line, Col} = aeso_ast_to_fcode:ann_loc(FAnn),
    Name = PSName ++
           [ "%lambda"
           , if is_integer(Line) -> integer_to_list(Line); true -> "" end
           , if is_integer(Col) -> integer_to_list(Col); true -> "" end
           , integer_to_list(Id)],
    {local_fun, Name}.

-spec lambda_lift_fun(aeso_ast_to_fcode:state_layout(), aeso_ast_to_fcode:fun_name(), aeso_ast_to_fcode:fun_def()) -> {aeso_ast_to_fcode:fun_def(), #{aeso_ast_to_fcode:var_name() => term()}}.
lambda_lift_fun(Layout, Name, Def = #{ body := Body }) ->
    %% Not thread safe! We initialize state per functions not to depend on the order in which
    %% functions are processed.
    init_lambda_funs(),
    NewDef = Def#{ body := lambda_lift_expr(Layout, Name, Body) },
    {NewDef, get_lambda_funs()}.

-spec lifted_fun([aeso_ast_to_fcode:var_name()], [aeso_ast_to_fcode:var_name()], aeso_ast_to_fcode:fexpr()) -> aeso_ast_to_fcode:fun_def().
lifted_fun([Z], Xs, Body) ->
    #{ attrs  => [private],
       args   => [{Z, any} | [{X, any} || X <- Xs]],
       return => any,
       body   => Body };
lifted_fun(FVs, Xs, Body) ->
    Z    = "%env",
    FAnn = aeso_ast_to_fcode:get_fann(Body),
    Proj = fun({I, Y}, E) -> {'let', FAnn, Y, {proj, FAnn, {var, FAnn, Z}, I - 1}, E} end,
    #{ attrs  => [private],
       args   => [{Z, any} | [{X, any} || X <- Xs]],
       return => any,
       body   => lists:foldr(Proj, Body, aeso_ast_to_fcode:indexed(FVs))
     }.

-spec make_closure(aeso_ast_to_fcode:fun_name(), aeso_ast_to_fcode:fann(), [aeso_ast_to_fcode:var_name()], [aeso_ast_to_fcode:var_name()], aeso_ast_to_fcode:fexpr()) -> aeso_ast_to_fcode:fexpr().
make_closure(ParentName, FAnn, FVs, Xs, Body) ->
    Name  = add_lambda_fun(ParentName, FAnn, lifted_fun(FVs, Xs, Body)),
    Tup = fun([Y]) -> Y; (Ys) -> {tuple, FAnn, Ys} end,
    {closure, FAnn, Name, Tup([{var, FAnn, Y} || Y <- FVs])}.

-spec lambda_lift_expr(aeso_ast_to_fcode:state_layout(), aeso_ast_to_fcode:fun_name(), aeso_ast_to_fcode:fexpr()) -> aeso_ast_to_fcode:fexpr().
lambda_lift_expr(Layout, Name, L = {lam, FAnn, Xs, Body}) ->
    FVs   = aeso_ast_to_fcode:free_vars(L),
    make_closure(Name, FAnn, FVs, Xs, lambda_lift_expr(Layout, Name, Body));
lambda_lift_expr(Layout, Name, UExpr) when element(1, UExpr) == def_u; element(1, UExpr) == builtin_u ->
    [Tag, FAnn, F, Ar | _] = tuple_to_list(UExpr),
    ExtraArgs = case UExpr of
                    {builtin_u, _, _, _, TypeArgs} -> TypeArgs;
                    _                              -> []
                end,
    Xs   = [ lists:concat(["arg", I]) || I <- lists:seq(1, Ar) ],
    Args = [{var, aeso_ast_to_fcode:get_fann(UExpr), X} || X <- Xs] ++ ExtraArgs,
    Body = case Tag of
               builtin_u -> aeso_ast_to_fcode:builtin_to_fcode(Layout, aeso_ast_to_fcode:get_fann(UExpr), F, Args);
               def_u     -> {def, aeso_ast_to_fcode:get_fann(UExpr), F, Args}
           end,
    make_closure(Name, FAnn, [], Xs, Body);
lambda_lift_expr(Layout, Name, {remote_u, FAnn, ArgsT, RetT, Ct, F}) ->
    FVs  = aeso_ast_to_fcode:free_vars(Ct),
    Ct1  = lambda_lift_expr(Layout, Name, Ct),
    NamedArgCount = 3,
    Xs   = [ lists:concat(["arg", I]) || I <- lists:seq(1, length(ArgsT) + NamedArgCount) ],
    Args = [{var, [], X} || X <- Xs],
    make_closure(Name, FAnn, FVs, Xs, {remote, FAnn, ArgsT, RetT, Ct1, F, Args});
lambda_lift_expr(Layout, Name, Expr) ->
    case Expr of
        {lit, _, _}               -> Expr;
        {nil, _}                  -> Expr;
        {var, _, _}               -> Expr;
        {closure, _, _, _}        -> Expr;
        {def, FAnn, D, As}        -> {def, FAnn, D, lambda_lift_exprs(Layout, Name, As)};
        {builtin, FAnn, B, As}    -> {builtin, FAnn, B, lambda_lift_exprs(Layout, Name, As)};
        {remote, FAnn, ArgsT, RetT, Ct, F, As} -> {remote, FAnn, ArgsT, RetT, lambda_lift_expr(Layout, Name, Ct), F, lambda_lift_exprs(Layout, Name, As)};
        {con, FAnn, Ar, C, As}    -> {con, FAnn, Ar, C, lambda_lift_exprs(Layout, Name, As)};
        {tuple, FAnn, As}         -> {tuple, FAnn, lambda_lift_exprs(Layout, Name, As)};
        {proj, FAnn, A, I}        -> {proj, FAnn, lambda_lift_expr(Layout, Name, A), I};
        {set_proj, FAnn, A, I, B} -> {set_proj, FAnn, lambda_lift_expr(Layout, Name, A), I, lambda_lift_expr(Layout, Name, B)};
        {op, FAnn, Op, As}        -> {op, FAnn, Op, lambda_lift_exprs(Layout, Name, As)};
        {'let', FAnn, X, A, B}    -> {'let', FAnn, X, lambda_lift_expr(Layout, Name, A), lambda_lift_expr(Layout, Name, B)};
        {funcall, FAnn, A, Bs}    -> {funcall, FAnn, lambda_lift_expr(Layout, Name, A), lambda_lift_exprs(Layout, Name, Bs)};
        {set_state, FAnn, R, A}   -> {set_state, FAnn, R, lambda_lift_expr(Layout, Name, A)};
        {get_state, _, _}         -> Expr;
        {switch, FAnn, S}         -> {switch, FAnn, lambda_lift_expr(Layout, Name, S)};
        {split, Type, X, Alts}    -> {split, Type, X, lambda_lift_exprs(Layout, Name, Alts)};
        {nosplit, Rens, A}        -> {nosplit, Rens, lambda_lift_expr(Layout, Name, A)};
        {'case', P, S}            -> {'case', P, lambda_lift_expr(Layout, Name, S)}
    end.

-spec lambda_lift_exprs(aeso_ast_to_fcode:state_layout(), aeso_ast_to_fcode:fun_name(), [aeso_ast_to_fcode:fexpr()]) -> [aeso_ast_to_fcode:fexpr()].
lambda_lift_exprs(Layout, Name, As) -> [lambda_lift_expr(Layout, Name, A) || A <- As].


