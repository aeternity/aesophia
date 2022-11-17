-module(aeso_code_analysis).

-export([analyze/1]).

%-record(env, {vars = [] :: list()}).
%
%-type env() :: #env{}.

-record(analysis,
    { defined_types = sets:new() :: sets:set()
    , defined_funs  = sets:new() :: sets:set()
    , used_types    = sets:new() :: sets:set()
    , used_funs     = sets:new() :: sets:set()
    , used_includes = sets:new() :: sets:set()
    , unused_stateful = sets:new() :: sets:set()
    %, used_vars       = [] :: list()
    %, defined_vars    = [] :: list()
    %, used_consts     = [] :: list()
    %, shadowing_pairs = [] :: list()
    %, unused_retval   = [] :: list()
    }).

%-type analysis() :: #analysis{}.

-define(P(X), io:format(??X ++ ":\n~p\n", [X])).

-record(alg,
    { zero   :: A
    , plus   :: fun((A, A) -> A)
    , scoped :: fun((A, A) -> A) }).

work(expr, X = {qid, Ann, Fun}) ->
    ?P(X),
    ?P(aeso_syntax:get_ann(stateful, Ann, none)),
    ?P(""),
    #analysis{used_funs = sets:from_list([Fun])};
work(type, {qid, _, Type}) ->
    #analysis{used_types = sets:from_list([Type])};
work(bind_type, {id, _, Type}) ->
    #analysis{defined_types = sets:from_list([Type])};
work(_, _) ->
    #analysis{}.

-spec analyze(aeso_syntax:ast()) -> ok.
analyze([{Contract, _Ann, {con, _, _ConName}, _Impls, Decls} | Rest])
  when Contract == contract_main;
       Contract == contract_child ->
    analyze_contract(Decls),
    analyze(Rest);
analyze([{namespace, _Ann, {con, _, _NSName}, Decls} | Rest]) ->
    analyze_contract(Decls),
    analyze(Rest);
analyze([]) ->
    error("End of code analysis").

analyze_contract(Decls) ->
    Funs    = [ Fun || Fun = {letfun, _, _, _, _, _} <- Decls],
    _Types  = [ Def || Def = {type_def, _, _, _, _} <- Decls ],
    _Consts = [ Const || Const = {letval, _, _, _} <- Decls ],

    Alg =
        #alg{ zero = #analysis{}
            , plus = fun merge/2
            , scoped = fun merge/2 },
    Res0 = aeso_syntax_utils:fold(
        Alg,
        fun work/2,
        decl,
        Decls),
    Res = merge(Res0, #analysis{defined_funs = Funs}),
    UsedTypes = sets:to_list(Res#analysis.used_types),
    UsedFuns  = sets:to_list(Res#analysis.used_funs),
    ?P(UsedFuns),
    ?P(UsedTypes),

    %Res = [ {Name, analyze_fun(Fun)} || Fun = {letfun, _, {id, _, Name}, _, _, _} <- Funs ],

    ?P(Res).
%
%analyze_fun({letfun, _, _FunId, _Args, _, GuardedBodies}) ->
%    lists:foldl(fun merge/2, #analysis{}, [(analyze_expr(#env{}, Body)) || {guarded, _, _, Body} <- GuardedBodies ]).
%
%-spec analyze_expr(env(), aeso_syntax:expr()) -> analysis().
%analyze_expr(Env, {lam, _, Args, Expr}) ->
%    NewVars = [ Id || {arg, _, Id, _} <- Args ],
%    Env1 = lists:foldl(fun bind_var/2, Env, NewVars),
%    Analysis = analyze_expr(Env1, Expr),
%    Analysis#analysis{defined_vars = Analysis#analysis.defined_vars ++ NewVars};
%%analyze_expr(Env, {'if', ann(), expr(), expr(), expr()}) ->
%%    ok;
%%analyze_expr(Env, {switch, ann(), expr(), [alt()]}) ->
%%    ok;
%analyze_expr(Env, {app, _, Expr, _Args}) ->
%    analyze_expr(Env, Expr);
%%analyze_expr(Env, {proj, ann(), expr(), id()}) ->
%%    ok;
%analyze_expr(Env, {tuple, _, Exprs}) ->
%    lists:foldl(fun merge/2, #analysis{}, [ analyze_expr(Env, Expr) || Expr <- Exprs ]);
%%analyze_expr(Env, {list, ann(), [expr()]}) ->
%%    ok;
%%analyze_expr(Env, {list_comp, ann(), expr(), [comprehension_exp()]}) ->
%%    ok;
%analyze_expr(Env, {typed, _, Expr, Type}) ->
%    merge(analyze_expr(Env, Expr), analyze_type(Env, Type));
%%analyze_expr(Env, {record_or_map(), ann(), [field(expr())]}) ->
%%    ok;
%%analyze_expr(Env, {record_or_map(), ann(), expr(), [field(expr())]}) ->
%%    ok;
%%analyze_expr(Env, {map, ann(), [{expr(), expr()}]}) ->
%%    ok;
%%analyze_expr(Env, {map_get, ann(), expr(), expr()}) ->
%%    ok;
%%analyze_expr(Env, {map_get, ann(), expr(), expr(), expr()}) ->
%%    ok;
%analyze_expr(Env, {block, _, Stmts}) ->
%    analyze_block(Env, Stmts);
%%analyze_expr(Env, {op(), ann()}) ->
%%    ok;
%analyze_expr(_Env, {int, _, _}) ->
%    #analysis{};
%analyze_expr(Env, Id = {id, _, _}) ->
%    #analysis{used_vars = [lookup_var(Id, Env)]};
%analyze_expr(_Env, {qcon, _, _}) ->
%    #analysis{}.
%%analyze_expr(Env, QId = {qid, _, _}) ->
%%    #analysis{used_funs = lookup_fun(QId, Env)}.
%%analyze_expr(Env, qid() | con() | qcon()) ->
%%    ok;
%%analyze_expr(Env, constant()) ->
%%    ok;
%%analyze_expr(Env, letpat()) ->
%%    ok.
%
%analyze_block(_Env, []) ->
%    #analysis{};
%analyze_block(Env, [E]) ->
%    analyze_expr(Env, E);
%analyze_block(Env, [{letval, _, {typed, _, Id = {id, _, _}, _}, Expr} | Stmts]) ->
%    Env1 = bind_var(Id, Env),
%    Analysis = analyze_block(Env1, Stmts),
%    Analysis2 = merge(Analysis, analyze_expr(Env1, Expr)),
%    Analysis2#analysis{defined_vars = Analysis2#analysis.defined_vars ++ [Id]}.
%
%analyze_type(_Env, {id, _, Id}) ->
%    #analysis{used_types = [Id]};
%analyze_type(_Env, {qid, _, QId}) ->
%    #analysis{used_types = [QId]};
%analyze_type(Env, {fun_t, _, _, Types, Type}) ->
%    merge(lists:foldl(fun merge/2, #analysis{}, [analyze_type(Env, T) || T <- Types]), analyze_type(Env, Type));
%analyze_type(_Env, {tuple_t, _, _}) ->
%    #analysis{}.
%
%bind_var(VarId, Env = #env{vars = Vars}) ->
%    check_shadowing(VarId, Vars),
%    Env#env{vars = [VarId | Vars]}.
%
%check_shadowing(Var = {id, _, VarName}, Ids) ->
%    Shadowed =
%        lists:search(fun({id, _, Name}) when Name == VarName -> true;
%                        (_)                                  -> false
%                    end, Ids),
%    case Shadowed of
%        false ->
%            #analysis{};
%        {value, ShadowedVar} ->
%            #analysis{shadowing_pairs = [{Var, ShadowedVar}]}
%    end.
%
%lookup_var({id, _, VarName}, Env) ->
%    {value, Var}=
%        lists:search(
%            fun({id, _, Name}) when Name == VarName -> true;
%               (_)                                  -> false
%            end, Env#env.vars),
%    Var.


merge(A1, A2) ->
    #analysis{ used_types = sets:union(A1#analysis.used_types, A2#analysis.used_types)
             , used_funs  = sets:union(A1#analysis.used_funs,  A2#analysis.used_funs) }.


%% the set of unused functions is the different between the 2 sets:
%% - In a contract:
%%  * all user-defined functions
%%  * all function calls
%% - In a namespace:
%%  * all user-defined private functions
%%  * all function calls
%% Note: this only applies to functions, not entrypoints

%% Unused variables:
%% -----------------
%% Scope: function
%% Algo: if a variable is not used in its current scope, then it's reported.
%% Functions that are declared in one scope but not used, and then declared
%% in a different scope and used, should be considered.
%% 
%% Unused stateful:
%% ----------------
%% Scope: function
%% Algo: check all function calls in the function, if none of them requires
%% stateful, then we say that it's unused.
%% 
%% Unused constants:
%% -----------------
%% Scope: contract or namespace
%% Algo: same as variables, but the scope is fixed to the contract or the namespace.
%% 
%% Unused typedefs:
%% ----------------
%% Scope: contract or namespace
%% Algo: check the types of all expressions in the contract or namespace, if the type
%% doesn't show up anywhere, then the typedef is not used.
