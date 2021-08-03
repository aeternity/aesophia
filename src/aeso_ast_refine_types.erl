-module(aeso_ast_refine_types).

-export([ refine_ast/2, apply_subst/3, apply_subst/2, init_refiner/0
        , type_binds/1, type_binds/2, pred_of/2, path_pred/1, init_env/1, bind_var/3
        , impl_holds/3, impl_holds/4, solve/3, split_constr/1
        ]).
-export([pp_error/1]).

-include_lib("eunit/include/eunit.hrl").
-include("aeso_ast_refine_types.hrl").
-include("aeso_ast_refine_types_stdlib.hrl").
-define(DBG_TEXT_COLOR, "\e[1;33m").
-define(DBG_EXPR_COLOR, "\e[0;1m\e[1m").
-define(DBG_STR_COLOR, "\e[1;32m").
-define(DBG_RESET_COLOR, "\e[0m").
-define(DBG_COLOR(S),
        lists:flatten(
          ?DBG_TEXT_COLOR
          ++ string:replace(
               lists:flatten(
                 string:replace(S, "~s", ?DBG_STR_COLOR ++ "~s" ++ ?DBG_TEXT_COLOR, all)
                ),
               "~p", ?DBG_EXPR_COLOR ++ "~p" ++ ?DBG_TEXT_COLOR, all)
          ++ ?DBG_RESET_COLOR
         )).
-define(DBG(A, B), ?debugFmt(?DBG_COLOR(A), B)).
-define(DBG(A), ?debugMsg(?DBG_COLOR(A))).

%% -- Types --------------------------------------------------------------------

%% Type imports
-type predicate()   :: aeso_syntax:predicate().
-type expr()        :: aeso_syntax:expr().
-type pat()         :: aeso_syntax:pat().
-type decl()        :: aeso_syntax:decl().
-type letfun()      :: aeso_syntax:letfun().
-type fundecl()     :: aeso_syntax:fundecl().
-type ast()         :: aeso_syntax:ast().
-type type()        :: aeso_syntax:type().
-type dep_type(Q)   :: aeso_syntax:dep_type(Q).
-type dep_arg_t(Q)  :: aeso_syntax:dep_arg_t(Q).
-type id()          :: aeso_syntax:id().
-type qid()         :: aeso_syntax:qid().
-type con()         :: aeso_syntax:con().
-type qcon()        :: aeso_syntax:qcon().
-type ann()         :: aeso_syntax:ann().

-type type_id() :: id() | qid() | con() | qcon().

-type typedef() :: {[aeso_syntax:tvar()], aeso_syntax:typedef()
                   | {contract_t, [aeso_syntax:field_t()]}}.


%% Names
-type name() :: string().
-type qname() :: [name()].

%% Liquid type variable
-type ltvar() :: {ltvar, name()}.

%% Substitution of a variable with an expression
-type subst() :: {name(), expr()}.

%% Uninstantiated predicate template
-type template() :: {template, [subst()], ltvar()}.

-type liquid_qual() ::  predicate() | template().

%% Liquid type, possibly uninstantiated
-type lutype() :: dep_type(liquid_qual()).

-type fun_env()  :: #{name() => {ann(), template()}}.
-type var_env()  :: #{name() => {ann(), template()}}.
-type type_env() :: [{name(),   {ann(), typedef()}}]. % order matters

-type args_substs() :: #{name() => subst()}.

-record(scope, { fun_env = #{} :: fun_env()
               , type_env = [] :: type_env()
               , args_substs = #{} :: args_substs()
               }).
-type scope() :: #scope{}.

-type namespace_type() :: namespace | contract_main | contract_child | contract_interface.

-record(env,
        { scopes           = #{[] => #scope{}} :: #{qname() => scope()}
        , var_env          = #{}               :: var_env()
        , path_pred        = []                :: predicate()
        , cool_ints        = []                :: [integer()]
        , namespace        = []                :: qname()
        , namespaces       = #{}               :: #{qname() => namespace_type()}
        , stateful         = #{}               :: #{qname() => boolean()}
        , tc_env
        }).
-type env() :: #env{}.

-type constr_id() :: {atom(), integer()}.

%% Constraint
-type constr() :: {subtype, constr_id(), ann(), env(), lutype(), lutype()}
                | {well_formed, constr_id(), env(), lutype()}
                | {reachable, constr_id(), env()}
                | {unreachable, constr_id(), ann(), env()}.

%% Information about ltvar
-record(ltinfo, {id :: id(), base :: type(), predicate :: predicate(), env :: env()}).
-type ltinfo() :: #ltinfo{}.

%% Predicate assignment
-type assignment() :: #{name() => ltinfo()}.

%% Position in type
-type variance() :: contravariant | covariant | forced_covariant | forced_contravariant.

state_t(Ann, #env{namespace = NS, tc_env = TCEnv}) ->
    Qid = {qid, Ann, NS ++ ["state"]},
    aeso_ast_infer_types:unfold_types_in_type(TCEnv, Qid, []).

%% -- Name manipulation --------------------------------------------------------

-spec name(aeso_syntax:id() | aeso_syntax:con()) -> name().
name({_, _, X}) -> X.

-spec qname(type_id()) -> qname().
qname({id,   _, X})  -> [X];
qname({qid,  _, Xs}) -> Xs;
qname({con,  _, X})  -> [X];
qname({qcon, _, Xs}) -> Xs.

-spec qid(ann(), qname()) -> aeso_syntax:id() | aeso_syntax:qid().
qid(Ann, [X]) -> {id, Ann, X};
qid(Ann, Xs) when is_list(Xs) -> {qid, Ann, Xs}.

id(Ann, X) ->
    {id, Ann, X}.

-spec qcon(ann(), qname()) -> aeso_syntax:con() | aeso_syntax:qcon().
qcon(Ann, [X]) -> {con, Ann, X};
qcon(Ann, Xs) when is_list(Xs)  -> {qcon, Ann, Xs}.

-spec set_qname(qname(), type_id()) -> type_id().
set_qname(Xs, {id,   Ann, _}) -> qid(Ann, Xs);
set_qname(Xs, {qid,  Ann, _}) -> qid(Ann, Xs);
set_qname(Xs, {con,  Ann, _}) -> qcon(Ann, Xs);
set_qname(Xs, {qcon, Ann, _}) -> qcon(Ann, Xs).


%% -- Environment ---------------------------------------------------------------------

-spec push_scope(aeso_syntax:con(), env()) -> env().
push_scope(Con, Env) ->
    Name   = name(Con),
    New    = Env#env.namespace ++ [Name],
    Scopes = Env#env.scopes,
    Env#env{ namespace = New,
             scopes =
                 case maps:get(New, Scopes, undefined) of
                     undefined -> Scopes#{ New => #scope{} };
                     _         -> Scopes
                 end
           }.

-spec pop_scope(env()) -> env().
pop_scope(Env) ->
    Env#env{ namespace = lists:droplast(Env#env.namespace) }.


-spec namespace_type(env()) -> namespace_type() | toplevel.
namespace_type(#env{namespace = NS, namespaces = NSs}) ->
    maps:get(NS, NSs, toplevel).

-spec on_current_scope(env(), fun((scope()) -> scope())) -> env().
on_current_scope(Env = #env{ namespace = NS, scopes = Scopes }, Fun) ->
    Scope = maps:get(NS, Scopes),
    Env#env{ scopes = Scopes#{ NS => Fun(Scope) } }.

-spec set_stateful(id(), env()) -> env().
set_stateful(Id, Env) ->
    Name = name(Id),
    NS = Env#env.namespace,
    Env#env{stateful = (Env#env.stateful)#{NS ++ [Name] => true}}.

-spec bind_var(id(), lutype(), env()) -> env().
bind_var(Id = {id, Ann, Name}, T, Env = #env{var_env = VarEnv}) ->
    case maps:get(Name, VarEnv, none) of
        none -> ok;
        _    ->
            throw({overwrite, Id})
    end,
    Ann1 = if element(1, T) =:= fun_t;
              element(1, T) =:= dep_fun_t -> [{stateful, true}|Ann];
              true -> Ann
           end,
    Env#env{ var_env = VarEnv#{Name => {Ann1, T}}}.

-spec ensure_var(id(), lutype(), env()) -> env().
ensure_var({id, Ann, Name}, T, Env = #env{var_env = VarEnv}) ->
    Ann1 = if element(1, T) =:= fun_t;
              element(1, T) =:= dep_fun_t -> [{stateful, true}|Ann];
              true -> Ann
           end,
    case maps:get(Name, VarEnv, none) of
        none -> Env#env{ var_env = VarEnv#{Name => {Ann1, T}}};
        _    -> Env
    end.

-spec bind_vars([{id(), lutype()}], env()) -> env().
bind_vars([], Env) -> Env;
bind_vars([{X, T} | Vars], Env) ->
    bind_vars(Vars, bind_var(X, T, Env)).

-spec bind_args([dep_arg_t(liquid_qual())], env()) -> env().
bind_args([], Env) -> Env;
bind_args([{dep_arg_t, _, {id, Ann, "_"}, T} | Vars], Env) ->
    X = fresh_id(Ann, "arg_b"),
    bind_args(Vars, bind_var(X, T, Env));
bind_args([{dep_arg_t, _, X, T} | Vars], Env) ->
    bind_args(Vars, bind_var(X, T, Env)).

-spec ensure_args([dep_arg_t(liquid_qual())], env()) -> env().
ensure_args([], Env) -> Env;
ensure_args([{dep_arg_t, _, {id, Ann, "_"}, T} | Vars], Env) ->
    X = fresh_id(Ann, "arg_e"),
    ensure_args(Vars, ensure_var(X, T, Env));
ensure_args([{dep_arg_t, _, X, T} | Vars], Env) ->
    ensure_args(Vars, ensure_var(X, T, Env)).

-spec bind_fun(name(), lutype(), env()) -> env().
bind_fun(X, Type, Env) ->
    on_current_scope(
      Env, fun(Scope = #scope{ fun_env = Funs }) ->
                   Scope#scope{ fun_env = Funs#{X => {?ann_of(Type), Type}} }
           end).

-spec bind_funs([{name(), lutype()}], env()) -> env().
bind_funs([], Env) -> Env;
bind_funs([{Id, Type} | Rest], Env) ->
    bind_funs(Rest, bind_fun(Id, Type, Env)).

-spec register_args_subst(name(), subst(), env()) -> env().
register_args_subst(X, Subst, Env) ->
    on_current_scope(
      Env, fun(Scope = #scope{ args_substs = Substs }) ->
                   Scope#scope{ args_substs = Substs#{X => Subst} }
           end).

-spec register_args_substs([{name(), subst()}], env()) -> env().
register_args_substs([], Env) -> Env;
register_args_substs([{Id, Subst} | Rest], Env) ->
    register_args_substs(Rest, register_args_subst(Id, Subst, Env)).

-spec bind_type(id(), [type()], typedef(), env()) -> env().
bind_type({id, Ann, Name}, Args, Def, Env) ->
    on_current_scope(Env, fun(Scope = #scope{ type_env = Types }) ->
                                  Scope#scope{ type_env = [{Name, {Ann, {Args, Def}}}|Types] }
                          end).

bind_namespace({con, Ann, Q}, NS, Env) ->
    bind_namespace({qcon, Ann, [Q]}, NS, Env);
bind_namespace({qcon, _, QName}, NS, Env = #env{namespaces = NSs}) ->
    Env#env{namespaces = NSs#{QName => NS}}.

-spec assert(expr() | predicate(), env()) -> env().
assert(L, Env = #env{path_pred = GP}) when is_list(L) ->
    Env#env{path_pred = L ++ GP};
assert(E, Env = #env{path_pred = GP}) ->
    Env#env{path_pred = [E|GP]}.


%% What scopes could a given name come from?
-spec possible_scopes(env(), qname()) -> [qname()].
possible_scopes(#env{ namespace = Current}, Name) ->
    Qual = lists:droplast(Name),
    [ lists:sublist(Current, I) ++ Qual || I <- lists:seq(0, length(Current)) ].

-spec lookup_type(env(), type_id()) -> false | {qname(), ann(), typedef()}.
lookup_type(Env, Id) ->
    lookup_env(Env, type, qname(Id)).

-spec lookup_env(env(), term, qname()) -> false | {qname(), ann(), lutype()};
                (env(), type, qname()) -> false | {qname(), ann(), typedef()};
                (env(), subst, qname()) -> false | subst().
lookup_env(Env, Kind, Name) ->
    Var = case Name of
            [X] when Kind == term -> maps:get(X, Env#env.var_env, false);
            _                     -> false
          end,
    case Var of
        false ->
            Names = [ Qual ++ [lists:last(Name)] || Qual <- possible_scopes(Env, Name) ],
            case [ Res || QName <- Names, Res <- [lookup_env1(Env, Kind, QName)], Res /= false] of
                []    -> false;
                [Res] -> Res;
                Many  ->
                    error({ambiguous_name, Many})
            end;
        {Ann, Type} -> {Name, Ann, Type}
    end.

-spec lookup_env1(env(), term | type | subst, qname()) -> false | {qname(), {ann(), lutype()}} | subst().
lookup_env1(#env{ scopes = Scopes }, Kind, QName) ->
    Qual = lists:droplast(QName),
    Name = lists:last(QName),
    case maps:get(Qual, Scopes, false) of
        false -> false;
        #scope{ fun_env = Funs, type_env = Types, args_substs = Substs } ->
            case case Kind of
                     term -> maps:get(Name, Funs, false);
                     subst -> {subst, maps:get(Name, Substs, false)};
                     type -> proplists:get_value(Name, Types, false)
                 end of
                false -> false;
                {subst, Subst} -> Subst;
                {Ann, E} -> {QName, Ann, E}
            end
    end.

-spec is_stateful(env(), type_id()) -> boolean().
is_stateful(#env{stateful = Stateful}, Id) ->
    maps:get(qname(Id), Stateful, false).

-spec type_of(env(), type_id()) -> {qname(), ann(), lutype()}.
type_of(Env, Id) ->
    case lookup_env(Env, term, qname(Id)) of
        false ->
            undefined;
        {QId, Ann, Ty} -> {set_qname(QId, Id), Ann, Ty}
    end.

-spec args_subst_of(env(), type_id()) -> subst().
args_subst_of(Env, Id) ->
    case lookup_env(Env, subst, qname(Id)) of
        false ->
            undefined;
        Subst -> Subst
    end.

-spec bind_assg(assignment(), env()) -> env().
bind_assg(Assg, Env) ->
    lists:foldl(
      fun({_, LT}, Env0) ->
              Type = ?refined(LT#ltinfo.id, LT#ltinfo.base, LT#ltinfo.predicate),
              ensure_var(LT#ltinfo.id, Type, Env0)
      end, Env, maps:to_list(Assg)
     ).

-spec global_type_binds(env()) -> [{expr(), lutype()}].
global_type_binds(#env{scopes = Scopes}) ->
    [ {qid(Ann, ScopePath ++ [Var]), Type}
      || {ScopePath, #scope{fun_env = FEnv}} <- maps:to_list(Scopes),
         {Var, {Ann, Type}} <- maps:to_list(FEnv)
    ].

-spec local_type_binds(assignment(), env()) -> [{expr(), lutype()}].
local_type_binds(Assg, Env) ->
    Env1 = bind_assg(Assg, Env),
    VEnv = Env1#env.var_env,
    [ begin
          Qid = qid(VarAnn, [Var]),
          {Qid,
           case Type of
               {refined_t, _, Id, _, _} ->
                   apply_subst(Id, Qid, Type);
               {dep_variant_t, _, Id, _, _, _} ->
                   apply_subst(Id, Qid, Type);
               {dep_list_t, _, Id, _, _} ->
                   apply_subst(Id, Qid, Type);
               _ -> Type
           end
          }
      end
      || {Var, {VarAnn, Type}} <- maps:to_list(VEnv)
    ].

-spec type_binds(env()) -> [{expr(), lutype()}].
type_binds(Env) ->
    type_binds(#{}, Env).
-spec type_binds(assignment(), env()) -> [{expr(), lutype()}].
type_binds(Assg, Env) ->
    global_type_binds(Env) ++ local_type_binds(Assg, Env).

-spec prim_type_binds(env()) -> [{expr(), lutype()}].
prim_type_binds(Env) ->
    prim_type_binds(fun(X) -> X end, local_type_binds(#{}, Env)).
prim_type_binds(Access, TB) ->
    [ Q
     || {Var, Type} <- TB,
        Q <- case Type of
                 {refined_t, _, _, _, _} ->
                     [{Access(Var), Type}];
                 {tuple_t, Ann, Fields} ->
                     N = length(Fields),
                     prim_type_binds(
                       fun(X) -> {proj, Ann, Access(Var), X} end,
                       lists:zip(
                         [?tuple_proj_id(Ann, N, I) || I <- lists:seq(1, N)],
                         Fields
                        )
                      );
                 {dep_record_t, Ann, RT, Fields} ->
                     QName = case RT of
                                 {qid, _, Q} -> Q;
                                 {app_t, _, {qid, _, Q}, _} -> Q
                             end,
                     prim_type_binds(
                       fun(X) -> {proj, Ann, Access(Var), X} end,
                       [{qid(FAnn, QName ++ [name(Field)]), T}
                        || {field_t, FAnn, Field, T} <- Fields]
                      );
                 {dep_list_t, Ann, Id, _, LenPred} ->
                     [{Access(Var), ?refined(Id, ?int_t(Ann), LenPred)}];
                 _ -> []
             end
    ].


-spec type_defs(env()) -> [{qid(), typedef()}].
type_defs(#env{tc_env = TCEnv, scopes = Scopes}) ->
    Types = [ {qid(Ann, ScopePath ++ [Var]),
               aeso_ast_infer_types:unfold_types_in_type(
                 TCEnv, TypeDef, []
                )
              }
              || {ScopePath, #scope{type_env = TEnv}} <- maps:to_list(Scopes),
                 {Var, {Ann, TypeDef}} <- TEnv
            ],
    lists:reverse(Types).

-spec path_pred(env()) -> predicate().
path_pred(#env{path_pred = PathPred}) ->
    PathPred.

%% -- Initialization -----------------------------------------------------------

-spec init_refiner() -> ok.
init_refiner() ->
    put(ltvar_supply, 0),
    put(id_supply, 0),
    put(refiner_errors, []),
    ok.

init_env(TCEnv) ->
    Ann     = ?ann(),
    Bool    = {id, Ann, "bool"},
    String  = {id, Ann, "string"},
    Address = {id, Ann, "address"},
    Hash    = {id, Ann, "hash"},
    Bits    = {id, Ann, "bits"},
    Bytes   = fun(Len) -> {bytes_t, Ann, Len} end,
    Unit    = {tuple_t, Ann, []},
    Option  = fun(T) -> {app_t, Ann, {id, Ann, "option"}, [T]} end,
    DFun    = fun(Ts, T) -> {dep_fun_t, Ann, Ts, T} end,
    DFun1   = fun(S, T) -> DFun([S], T) end,
    %% Lambda    = fun(Ts, T) -> {fun_t, Ann, [], Ts, T} end,
    %% Lambda1   = fun(S, T) -> Lambda([S], T) end,
    StateDFun  = fun(Ts, T) -> {dep_fun_t, [stateful|Ann], Ts, T} end,
    Arg     = fun(Name, Type) -> {dep_arg_t, Ann, id(Ann, Name), Type} end,

    MkDefs = fun(Defs) ->
                     maps:from_list([{X, {Ann, T}} || {X, T} <- Defs])
             end,

    ChainScope = #scope
        { fun_env = MkDefs(
                     %% Spend transaction.
                    [{"spend",        StateDFun([Arg("addr", Address),
                                                 Arg("amount", ?refined(?int_t(Ann), [?op(Ann, ?nu(Ann), '=<', {qid, Ann, ["Contract", "balance"]})]))], Unit)},
                     %% Chain environment
                     {"balance",      DFun1(Arg("addr", Address), ?d_nonneg_int(Ann))},
                     {"block_hash",   DFun1(Arg("h", ?d_nonneg_int(Ann)), Option(Hash))},
                     {"timestamp",    ?d_pos_int(Ann)},
                     {"block_height", ?d_pos_int(Ann)},
                     {"difficulty",   ?d_nonneg_int(Ann)},
                     {"gas_limit",    ?d_pos_int(Ann)}])
        },

    ContractScope = #scope
        { fun_env = MkDefs(
                    [{"balance", ?d_nonneg_int(Ann)}]) },

    CallScope = #scope
        { fun_env = MkDefs(
                    [{"value",     ?d_nonneg_int(Ann)},
                     {"gas_price", ?d_pos_int(Ann)},
                     {"gas_left",  DFun([], ?d_pos_int(Ann))}])
        },

    %% Strings
    StringScope = #scope
        { fun_env = MkDefs(
                     [{"length",  DFun1(Arg("str", String), ?d_nonneg_int(Ann))}])
        },

    %% Bits
    BitsScope = #scope
        { fun_env = MkDefs(
                     [{"set",     DFun([Arg("bits", Bits), Arg("idx", ?d_nonneg_int(Ann))], Bits)},
                      {"clear",   DFun([Arg("bits", Bits), Arg("idx", ?d_nonneg_int(Ann))], Bits)},
                      {"test",    DFun([Arg("bits", Bits), Arg("idx", ?d_nonneg_int(Ann))], Bool)},
                      {"sum",     DFun1(Arg("bits", Bits), ?d_nonneg_int(Ann))}])
                     },

    %% Bytes
    BytesScope = #scope
        { fun_env = MkDefs(
                   [{"to_int", DFun1(Arg("bytes", Bytes(any)), ?d_nonneg_int(Ann))}]) },

    TopScope = #scope
        { fun_env  = MkDefs(
                    [])
        , type_env =
              [ {"option", {Ann,
                            {[{tvar, Ann, "'a"}],
                             {variant_t,
                              [ {constr_t, Ann, {con, Ann, "None"}, []}
                              , {constr_t, Ann, {con, Ann, "Some"}, [{tvar, Ann, "'a"}]}
                              ]
                             }
                            }}
                 }
              ]
        },

    #env{ scopes =
            #{ []           => TopScope
             , ["Chain"]    => ChainScope
             , ["Contract"] => ContractScope
             , ["Call"]     => CallScope
             , ["String"]   => StringScope
             , ["Bits"]     => BitsScope
             , ["Bytes"]    => BytesScope
             }
        , tc_env = TCEnv
        }.

find_cool_ints(Expr) ->
    sets:to_list(find_cool_ints(Expr, sets:from_list([0, 1, -1]))).
find_cool_ints({int, _, I}, Acc) ->
    sets:add_element(-I, sets:add_element(I, Acc));
find_cool_ints({list, _, L}, Acc) ->
    find_cool_ints(L, sets:add_element(length(L), Acc));
find_cool_ints({app, _, {'::', _}, [H, T]}, Acc0) ->
    Acc1 = find_cool_ints([H, T], Acc0),
    sets:union(Acc1,
               sets:from_list([I + 1 || I <- sets:to_list(Acc1)])
              );
%% find_cool_ints({app, _, {'-', _}, [L, R]}, Acc0) ->
%%     Acc1 = find_cool_ints([L, R], Acc0),
%%     AccL = sets:to_list(Acc1),
%%     sets:union(Acc1,
%%                sets:from_list([I1 - I2
%%                                || I1 <- AccL,
%%                                   I2 <- AccL
%%                               ])
%%               );
%% find_cool_ints({app, _, {'+', _}, [L, R]}, Acc0) ->
%%     Acc1 = find_cool_ints([L, R], Acc0),
%%     AccL = sets:to_list(Acc1),
%%     sets:union(Acc1,
%%                sets:from_list([I1 + I2
%%                                || I1 <- AccL,
%%                                   I2 <- AccL
%%                               ])
%%               );
find_cool_ints({app, _, {'++', _}, [L, R]}, Acc0) ->
    Acc1 = find_cool_ints([L, R], Acc0),
    AccL = sets:to_list(Acc1),
    sets:union(Acc1,
               sets:from_list([I1 + I2
                               || I1 <- AccL,
                                  I2 <- AccL
                              ])
              );
find_cool_ints([H|T], Acc) ->
    find_cool_ints(T, find_cool_ints(H, Acc));
find_cool_ints(T, Acc) when is_tuple(T) ->
    case tuple_to_list(T) of
        [_Tag, _Ann|Rest] -> find_cool_ints(Rest, Acc);
        L -> find_cool_ints(L, Acc)
    end;
find_cool_ints(M, Acc) when is_map(M) ->
    find_cool_ints(maps:to_list(M), Acc);
find_cool_ints(_, Acc) ->
    Acc.

with_cool_ints_from(AST, Env = #env{cool_ints = CI}) ->
    Env#env{cool_ints = find_cool_ints(AST) ++ CI}.


find_tuple_sizes(Expr) ->
    sets:to_list(find_tuple_sizes(Expr, sets:from_list([0, 1, 2, 3]))).
find_tuple_sizes({tuple_t, _, T}, Acc) ->
    find_tuple_sizes(T, sets:add_element(length(T), Acc));
find_tuple_sizes({tuple, _, T}, Acc) ->
    find_tuple_sizes(T, sets:add_element(length(T), Acc));
find_tuple_sizes([H|T], Acc) ->
    find_tuple_sizes(T, find_tuple_sizes(H, Acc));
find_tuple_sizes(T, Acc) when is_tuple(T) ->
    find_tuple_sizes(tuple_to_list(T), Acc);
find_tuple_sizes(_, Acc) ->
    Acc.

-spec register_ast_funs(ast(), env()) -> env().
register_ast_funs(AST, Env) ->
    lists:foldr(
      fun({namespace, _, {con, _, CName}, _}, Env0)
            when ?IS_STDLIB(CName) ->
              Env0;
         ({HEAD, _, Con, Defs}, Env0)
            when HEAD =:= namespace;
                 HEAD =:= contract_main;
                 HEAD =:= contract_child;
                 HEAD =:= contract_interface ->
              Env1 = push_scope(Con, Env0),
              {Funs, ArgsSubsts} = register_funs(Env1, Defs),
              Env2 = bind_funs(Funs, Env1),
              Env3 = register_args_substs(ArgsSubsts, Env2),
              Env4 = bind_funs(
                       [ {Name, fresh_liquid(Env2, Name, Type)}
                         || {fun_decl, _, {id, _, Name}, Type} <- Defs
                       ],
                       Env3),
              Env5 = pop_scope(Env4),
              Env5
      end,
     Env, AST).

register_funs(Env, Defs) ->
    lists:unzip(
      [ begin
            {TypeDep, ArgsSubst} = make_topfun(Env, FAnn, Id, Args),
            {{Name, TypeDep}, {Name, ArgsSubst}}
        end
        || {letfun, FAnn, Id = {id, _, Name}, Args, _, _} <- Defs
      ]).

make_topfun(Env, FAnn, Id, Args) ->
    TCEnv = Env#env.tc_env,
    NS    = Env#env.namespace,
    Stateful = proplists:get_value(stateful, FAnn, false),
    PurifierST = init_purifier_st(FAnn, Env),
    {_, {_, {type_sig, TSAnn, _, [], ArgsT, RetT}}} =
        aeso_ast_infer_types:lookup_env(
          TCEnv, term, FAnn, NS ++ qname(Id)),
    check_arg_assumptions(Id, FAnn, ArgsT),
    {DepArgsT, ArgsSubst} =
        fresh_liquid_args(
          Env,
          [ {Arg, purify_type(ArgT, PurifierST)}
            || {?typed_p(Arg), ArgT} <- lists:zip(Args, ArgsT)
          ]
         ),
    RetT1 = apply_subst(ArgsSubst, RetT),
    DepArgsT1 =
        [ element(1, fresh_liquid_arg(Env, init_state_var(FAnn, state_t(FAnn, Env))))
        , element(1, fresh_liquid_arg(Env, init_balance_var(FAnn)))
        | fresh_wildcards(DepArgsT)
        ],
    DepRetT1 =
        case Stateful of
            false -> fresh_liquid(Env, "ret", RetT1);
            true ->
                fresh_liquid(Env, "ret", wrap_state_t(RetT1, init_purifier_st(?ann_of(RetT), Env)))
        end,
    DepRetT2 = purify_type(DepRetT1, PurifierST),
    {{dep_fun_t, TSAnn, DepArgsT1, DepRetT2}, ArgsSubst}.

check_arg_assumptions({id, _, Name}, Ann, Args) ->
    case proplists:get_value(entrypoint, Ann, false) of
        true ->
            [ case has_assumptions(Arg) of
                  true -> add_error({entrypoint_arg_assump, {Name, Ann, Arg}});
                  false -> ok
              end
              || Arg <- Args
            ];
        false -> ok
    end.

%% Check if the type is not strictly less general than its base type
has_assumptions(T) ->
    has_assumptions(covariant, T).
has_assumptions(covariant, {refined_t, _, _, _, [_|_]}) ->
    true;
has_assumptions(covariant, {dep_variant_t, _, _, _, [_|_], _}) ->
    true;
has_assumptions(covariant, {dep_list_t, _, _, _, [_|_]}) ->
    true;
has_assumptions(Variance, {dep_fun_t, _, Args, RetT}) ->
    has_assumptions(switch_variance(Variance), Args)
        orelse has_assumptions(Variance, RetT);
has_assumptions(Variance, {fun_t, _, Named, Args, RetT}) ->
    has_assumptions(switch_variance(Variance), Args)
        orelse has_assumptions(switch_variance(Variance), Named)
        orelse has_assumptions(Variance, RetT);
has_assumptions(Variance, {type_sig, _, _, Named, Args, RetT}) ->
    has_assumptions(switch_variance(Variance), Args)
        orelse has_assumptions(switch_variance(Variance), Named)
        orelse has_assumptions(Variance, RetT);
has_assumptions(Variance, {app_t, _, {id, _, "map"}, [K, V]}) ->
    has_assumptions(switch_variance(Variance), K)
        orelse has_assumptions(Variance, V);
has_assumptions(Variance, {tuple_t, _, Args}) ->
    has_assumptions(Variance, Args);
has_assumptions(Variance, {dep_record_t, _, _, Fields}) ->
    has_assumptions(Variance, Fields);
has_assumptions(Variance, {dep_variant_t, _, _, _, _, Constrs}) ->
    has_assumptions(Variance, Constrs);
has_assumptions(Variance, {dep_list_t, _, _, ElemT, _}) ->
    has_assumptions(Variance, ElemT);
has_assumptions(Variance, [H|T]) ->
    has_assumptions(Variance, H) orelse has_assumptions(Variance, T);
has_assumptions(Variance, T) when is_tuple(T) ->
    has_assumptions(Variance, tuple_to_list(T));
has_assumptions(_, _) ->
    false.

strip_typed({typed, _, X, _}) ->
    strip_typed(X);
strip_typed([H|T]) ->
    [strip_typed(H)|strip_typed(T)];
strip_typed(T) when is_tuple(T) ->
    list_to_tuple(strip_typed(tuple_to_list(T)));
strip_typed(M) when is_map(M) ->
    maps:from_list(strip_typed(maps:to_list(M)));
strip_typed(X) -> X.



%% -- Fresh stuff --------------------------------------------------------------

fresh_supply() ->
    I = get(ltvar_supply),
    put(ltvar_supply, I + 1),
    I.

constr_id(When) ->
    Id = fresh_supply(),
    {When, Id}.

-spec fresh_ltvar(name()) -> ltvar().
fresh_ltvar(Name) ->
    I = fresh_supply(),
    {ltvar, lists:flatten(Name) ++ "_" ++ integer_to_list(I)}.

-spec fresh_template(variance(), name()) -> lutype().
fresh_template(covariant, Name) -> {template, [], fresh_ltvar(Name)};
fresh_template(contravariant, _) -> [];
fresh_template(forced_covariant, Name) -> fresh_template(covariant, Name);
fresh_template(forced_contravariant, Name) -> fresh_template(contravariant, Name).

-spec fresh_name(name()) -> name().
fresh_name(Name) ->
    I = get(id_supply),
    put(id_supply, I + 1),
    Name ++ "_" ++ integer_to_list(I).

-spec fresh_id(ann(), name()) -> type_id().
fresh_id(Ann, Name) ->
    N = fresh_name(Name),
    {id, Ann, N}.
fresh_id(Ann, Name, Type) ->
    Id = fresh_id(Ann, Name),
    ?typed(Id, Type).


%% Decorates base types with templates through the AST
-spec fresh_liquid(env(), name(), term()) -> term().
fresh_liquid(Env, Hint, Type) ->
    fresh_liquid(Env, covariant, Hint, Type).

-spec fresh_liquid(env(), variance(), name(), term()) -> term().
fresh_liquid(_Env, _Variance, _Hint, Type = {refined_t, _, _, _, _}) ->
    Type;
fresh_liquid(_Env, _Variance, _Hint, Type = {dep_fun_t, _, _, _}) ->
    Type;
fresh_liquid(_Env, _Variance, _Hint, Type = {dep_arg_t, _, _, _}) ->
    Type;
fresh_liquid(Env, Variance, _, {dep_record_t, Ann, Rec, Fields}) ->
    Qid = case Rec of
              {app_t, _, Q, _} -> Q;
              _ -> Rec
          end,
    {dep_record_t, Ann, Rec,
     [ fresh_liquid_field(Env, Variance, Qid, Field, FType)
       || {_FIELD_HEAD, _, Field, FType} <- Fields
     ]
    };
fresh_liquid(Env, Variance, Hint, {dep_variant_t, Ann, Id, Type, TagPred, Constrs}) ->
    {dep_variant_t, Ann, Id, Type, TagPred,
     [ {constr_t, CAnn, Con,
        fresh_liquid(Env, Variance, Hint ++ "_" ++ name(Con), Vals)}
       || {_CONSTR_HEAD, CAnn, Con, Vals} <- Constrs
     ]
    };
fresh_liquid(Env, Variance, _Hint, {dep_list_t, Ann, Id, ElemT, LenPred}) when is_list(LenPred) ->
    {dep_list_t, Ann, Id, fresh_liquid(Env, Variance, name(Id), ElemT),
     [?op(Ann, Id, '>=', ?int(Ann, 0)) | LenPred]};
fresh_liquid(Env, Variance, _Hint, {dep_list_t, Ann, Id, ElemT, LenPred}) ->
    {dep_list_t, Ann, Id, fresh_liquid(Env, Variance, name(Id), ElemT), LenPred};
fresh_liquid(_Env, Variance, Hint, Type = {id, Ann, Name}) ->
    {refined_t, Ann,
     fresh_id(Ann,
              case Name of
                  "int" -> "n";
                  "bool" -> "p";
                  "string" -> "s";
                  _ -> Name
              end),
     Type, fresh_template(Variance, Hint)};
fresh_liquid(_Env, Variance, Hint, Type = {con, Ann, Name}) ->
    {refined_t, Ann, fresh_id(Ann, string:to_lower(Name)), Type, fresh_template(Variance, Hint)};
fresh_liquid(_Env, Variance, Hint, Type = {qcon, Ann, Name}) ->
    {refined_t, Ann, fresh_id(Ann, string:to_lower(lists:last(Name))), Type, fresh_template(Variance, Hint)};
fresh_liquid(_Env, Variance, Hint, Type = {tvar, Ann, [_|Name]}) ->
    {refined_t, Ann, fresh_id(Ann, Name), Type, fresh_template(Variance, Hint)};
fresh_liquid(Env, Variance, Hint, Type = {qid, Ann, _}) ->
    fresh_liquid(Env, Variance, Hint, {app_t, Ann, Type, []});
fresh_liquid(Env, Variance, Hint, {app_t, Ann, Id = {id, _, "map"}, [K, V]}) ->
    {app_t, Ann, Id,
     [ fresh_liquid(Env, switch_variance(Variance), Hint ++ "_key", K)
     , fresh_liquid(Env,                  Variance, Hint ++ "_val", V)
     ]};
fresh_liquid(Env, Variance, Hint, {app_t, Ann, {id, _, "list"}, [Elem]})
  when Variance =:= contravariant; Variance =:= forced_contravariant ->
    Id = fresh_id(Ann, Hint),
    {dep_list_t, Ann, Id, fresh_liquid(Env, Variance, Hint, Elem), [?op(Ann, Id, '>=', ?int(Ann, 0))]};
fresh_liquid(Env, Variance, Hint, {app_t, Ann, {id, _, "list"}, [Elem]}) ->
    Id = fresh_id(Ann, Hint),
    {dep_list_t, Ann, Id, fresh_liquid(Env, Variance, Hint, Elem),
     fresh_template(Variance, Hint)};
fresh_liquid(Env, Variance, Hint, {app_t, Ann, {id, IAnn, Name}, Args}) ->
    fresh_liquid(Env, Variance, Hint, {app_t, Ann, {qid, IAnn, [Name]}, Args});
fresh_liquid(Env, Variance, Hint,
             Type = {app_t, _, Qid = {qid, Ann, _}, Args}) ->
    case lookup_type(Env, Qid) of
        false ->
            case Qid of
                {qid, _, [_, "state"]} -> {tuple_t, Ann, []};
                _ -> error({undefined_type, Qid})
            end;
        {_, _, {TArgs, TDef}} ->
            Subst = lists:zip(TArgs, Args),
            case TDef of
                {alias_t, Type1} ->
                    fresh_liquid(Env, Variance, Hint, apply_subst(Subst, Type1));
                {record_t, Fields} ->
                    {dep_record_t, Ann, Type,
                     [ fresh_liquid_field(Env, Variance, Qid, Field, apply_subst(Subst, FType))
                      || {field_t, _, Field, FType} <- Fields
                     ]
                    };
                {variant_t, Constrs} ->
                    Id = fresh_id(Ann, Hint),
                    DepConstrs =
                        [ {constr_t, CAnn, Con,
                           fresh_liquid(Env, Variance, Hint ++ "_" ++ name(Con),
                                        apply_subst(Subst, Vals))}
                          || {constr_t, CAnn, Con, Vals} <- Constrs
                        ],
                    {dep_variant_t, Ann, Id, Type,
                     fresh_template(Variance, Hint ++ "_tag"), DepConstrs}
            end
    end;
fresh_liquid(Env, Variance, Hint, {type_sig, Ann, _, Named, Args, Ret}) ->
    fresh_liquid(Env, Variance, Hint, {fun_t, Ann, Named, Args, Ret});
fresh_liquid(Env, Variance, Hint, {fun_t, Ann, Named, Args, Ret}) ->
    {ArgsN, SubstN} = fresh_liquid_args(Env, switch_variance(Variance), Named),
    {ArgsU, SubstU} =
        fresh_liquid_args(
          Env, switch_variance(Variance),
          [ begin
                ArgId = case Arg of
                            {refined_t, _, Id, _, _} -> Id;
                            {dep_list_t, _, Id, _, _} -> Id;
                            _ -> fresh_id(?ann_of(Arg), "arg_l")
                        end,
                {ArgId, Arg}
            end
           || Arg <- Args
          ]
         ),
    Args1 = ArgsN ++ ArgsU,
    Subst = SubstN ++ SubstU,
    Ret1 = apply_subst(Subst, Ret),
    {dep_fun_t, Ann, Args1, fresh_liquid(Env, Variance, Hint, Ret1)};
fresh_liquid(Env, Variance, Hint, {tuple_t, Ann, Types}) ->
    {tuple_t, Ann, fresh_liquid(Env, Variance, Hint, Types)};
fresh_liquid(_Env, _, _, []) -> [];
fresh_liquid(Env, Variance, Hint, [H|T]) ->
    [fresh_liquid(Env, Variance, Hint, H)|fresh_liquid(Env, Variance, Hint, T)];
fresh_liquid(Env, Variance, Hint, T) when is_tuple(T) ->
    list_to_tuple(fresh_liquid(Env, Variance, Hint, tuple_to_list(T)));
fresh_liquid(_Env, _, _, X) -> X.

fresh_liquid_arg(Env, ?typed_p(Id, Type)) ->
    fresh_liquid_arg(Env, Id, Type).
fresh_liquid_arg(Env, Id, Type) ->
    fresh_liquid_arg(Env, contravariant, Id, Type).
fresh_liquid_arg(Env, Variance, Id, Type) ->
    {DepType, Sub} =
        case fresh_liquid(Env, Variance, name(Id), Type) of
            {refined_t, Ann, TId, Base, Pred} ->
                {{refined_t, Ann, Id, Base, apply_subst(TId, Id, Pred)}, [{TId, Id}]};
            {dep_list_t, Ann, TId, Elem, Pred} ->
                {{dep_list_t, Ann, Id, Elem, apply_subst(TId, Id, Pred)}, [{TId, Id}]};
            {dep_variant_t, Ann, TId, Tag, Constrs} ->
                {{dep_variant_t, Ann, Id, apply_subst(TId, Id, Tag), Constrs}, [{TId, Id}]};
            T -> {T, []}
        end,
    {{dep_arg_t, ?ann_of(Id), Id, DepType}, Sub}.

fresh_liquid_args(Env, Args) ->
    fresh_liquid_args(Env, contravariant, Args).
fresh_liquid_args(_Env, _Variance, []) ->
    {[], []};
fresh_liquid_args(Env, Variance, [Arg = {dep_arg_t, _, _, _}|Rest]) ->
    {Args, Sub} = fresh_liquid_args(Env, Variance, Rest),
    {[Arg|Args], Sub};
fresh_liquid_args(Env, Variance, [Arg|Rest]) ->
    {Id, Type} = case Arg of
                     {arg, _, I, T} -> {I, T};
                     ?typed_p(I, T) -> {I, T};
                     {named_arg_t, _, I, T} -> {I, T};
                     {I, T} -> {I, T}
                 end,
    {Arg1, Sub} = fresh_liquid_arg(Env, Variance, Id, Type),
    {Args, Subs} = fresh_liquid_args(Env, Variance, Rest),
    {[Arg1|Args], Sub ++ Subs}.

fresh_liquid_field(Env, Variance, _, Id, Type) ->
    {{dep_arg_t, A, I, DT}, _} = fresh_liquid_arg(Env, Variance, Id, Type),
    {field_t, A, I, DT}.

-spec switch_variance(variance()) -> variance().
switch_variance(covariant) ->
    contravariant;
switch_variance(contravariant) ->
    covariant;
switch_variance(forced_covariant) ->
    forced_covariant;
switch_variance(forced_contravariant) ->
    forced_contravariant.

fresh_wildcards({typed, Ann, {id, Ann, "_"}, T}) ->
    {typed, Ann, fresh_id(Ann, "x"), T};
fresh_wildcards({id, Ann, "_"}) ->
    fresh_id(Ann, "x");
fresh_wildcards({dep_arg_t, Ann, {id, IAnn, "_"}, T}) ->
    {dep_arg_t, Ann, fresh_id(IAnn, "arg_w"), T};
fresh_wildcards([H|T]) ->
    [fresh_wildcards(H)|fresh_wildcards(T)];
fresh_wildcards(X) -> X.


%% -- Utils --------------------------------------------------------------------


base_type({refined_t, _, _, T, _}) ->
    T;
base_type({dep_list_t, Ann, _, ElemT, _}) ->
    {app_t, Ann, {id, Ann, "list"}, [base_type(ElemT)]};
base_type({dep_record_t, _, T, _}) ->
    T;
base_type({dep_variant_t, _, _, T, _, _}) ->
    T;
base_type({dep_fun_t, Ann, Args, Ret}) ->
    {fun_t, Ann, [],
     [base_type(ArgT) || {dep_arg_t, _, _, ArgT} <- Args],
     base_type(Ret)
    };
base_type({tuple_t, Ann, Types}) ->
    {tuple_t, Ann, [base_type(T) || T <- Types]};
base_type({app_t, Ann, T, Args}) ->
    {app_t, Ann, T, [base_type(A) || A <- Args]};
base_type(T) -> T.


add_error(Err) ->
    Errs = get(refiner_errors),
    put(refiner_errors, [strip_typed(Err)|Errs]),
    error.


%% -- Entrypoint ---------------------------------------------------------------

refine_ast(TCEnv, AST) ->
    Env0 = init_env(TCEnv),
    Env1 = with_cool_ints_from(TCEnv, with_cool_ints_from(AST, Env0)),
    Env2 = register_namespaces(AST, Env1),
    Env3 = register_typedefs(AST, Env2),
    Env4 = register_stateful(AST, Env3),
    try
        Env5 = register_ast_funs(AST, Env4),
        {AST1, CS0} = constr_ast(Env5, AST),
        CS1 = split_constr(CS0),
        %[ ?DBG("SUBTYPE ~p:\n~s\n<:\n~s", [Id, aeso_pretty:pp(type, strip_typed(T1)), aeso_pretty:pp(type, strip_typed(T2))])
        %  || {subtype, Id, _, _, T1, T2} <- CS1
        %],
        {Env5, solve(Env5, AST1, CS1)}
    of
        {EnvErlangSucks, {ok, AST2}} -> {ok, {EnvErlangSucks, AST2}};
        {_, Err = {error, _}} -> Err
    catch {ErrType, _}=E
                when ErrType =:= refinement_errors;
                     ErrType =:= overwrite;
                     ErrType =:= entrypoint_arg_assump;
                     ErrType =:= smt_error
                     -> {error, E}
    end.


%% -- Constraint generation ----------------------------------------------------

-spec constr_ast(env(), ast()) -> {ast(), [constr()]}.
constr_ast(Env, AST) ->
    lists:foldl(
      fun ({namespace, _, {con, _, NS}, _}, ST)
            when ?IS_STDLIB(NS) ->
              ST;
          (Def, {Decls, S00}) ->
              {Decl, S01} = constr_con(Env, Def, S00),
              {[Decl|Decls], S01}
      end,
      {[], []}, AST
     ).

-spec constr_con(env(), decl(), [constr()]) -> {decl(), [constr()]}.
constr_con(Env0, {Tag, Ann, Con, Defs}, S0)
  when Tag =:= contract_main;
       Tag =:= contract_child;
       Tag =:= contract_interface;
       Tag =:= namespace ->
    Env1 = push_scope(Con, Env0),
    {Defs1, S1} =
        lists:foldl(
          fun(Def, {Decls, S00}) when element(1, Def) =:= letfun ->
                  {Decl, S01} = constr_letfun(Env1, Def, S00),
                  {[Decl|Decls], S01};
             (_, Acc) -> Acc
          end,
          {[], S0}, Defs
         ),
    {{Tag, Ann, Con, Defs1}, S1}.

-spec constr_letfun(env(), letfun(), [constr()]) -> {fundecl(), [constr()]}.
constr_letfun(Env0, {letfun, Ann, Id, Args, RetT, Body}, S0) ->
    PurifierST = init_purifier_st(?ann_of(RetT), Env0),
    {_, _, GlobFunT = {dep_fun_t, _, _, GlobRetT}} = type_of(Env0, Id),
    Args0 = fresh_wildcards(Args),
    Args1 =
        [?typed(Arg, purify_type(ArgT, PurifierST)) || ?typed_p(Arg, ArgT) <- Args0],
    Args2 =
        [init_state_var(Ann, state_t(Ann, Env0)), init_balance_var(Ann) | Args1],
    {ArgsT, _ArgsSubst} = fresh_liquid_args(Env0, Args2),
    ArgsSubst = args_subst_of(Env0, Id),
    Env1 = bind_args(ArgsT, Env0),
    Env2 = ensure_args(apply_subst([{B, A} || {A, B} <- ArgsSubst], ArgsT), Env1),
    Env3 = assert(
             [?op(Ann, I1, '==', I2) || {I1, I2} <- ArgsSubst],
             Env2),
    Body0 = apply_subst(ArgsSubst, Body),
    Body1 = a_normalize(Body0),
    Body2 =
        case namespace_type(Env0) of
            namespace -> Body1;
            _ ->
                case proplists:get_value(stateful, Ann, false) of
                    false -> purify_expr_to_pure(Body1, PurifierST);
                    true  -> case purify_expr(Body1, PurifierST) of
                                 {impure, B} -> B;
                                 {pure, B} -> wrap_state(B, PurifierST)
                             end
                end
        end,
    Body3 = a_normalize(Body2),
    %?DBG("ANORM\n~s", [aeso_pretty:pp(expr, Body1)]),
    %?DBG("PURIFIED\n~s", [aeso_pretty:pp(expr, Body3)]),
    {BodyT, S1} = constr_expr(Env3, Body3, S0),
    InnerFunT = {dep_fun_t, Ann, ArgsT, BodyT},
    S3 = [ {subtype, constr_id(letfun_top_decl), Ann, Env3, BodyT, GlobRetT}
         , {well_formed, constr_id(letfun_glob), Env0, GlobFunT}
         , {well_formed, constr_id(letfun_int), Env0, InnerFunT}
         | S1
         ],

    {{fun_decl, Ann, Id, GlobFunT}, S3}.

register_namespaces([{Tag, _, Con, _}|Rest], Env)
  when Tag =:= contract_main;
       Tag =:= contract_child;
       Tag =:= contract_interface;
       Tag =:= namespace ->
    register_namespaces(Rest, bind_namespace(Con, Tag, Env));
register_namespaces([], Env) ->
    Env.

register_typedefs([{Tag, _, Con, Defs}|Rest], Env0)
  when Tag =:= contract_main;
       Tag =:= contract_child;
       Tag =:= contract_interface;
       Tag =:= namespace ->
    Env1 = push_scope(Con, Env0),
    Env2 = register_typedefs(Defs, Env1),
    Env3 = pop_scope(Env2),
    register_typedefs(Rest, Env3);
register_typedefs([{type_def, _, Id, Args, TDef}|Rest], Env) ->
    register_typedefs(Rest, bind_type(Id, Args, TDef, Env));
register_typedefs([_|Rest], Env) ->
    register_typedefs(Rest, Env);
register_typedefs([], Env) ->
    Env.

register_stateful([{Tag, _, Con, Defs}|Rest], Env0)
  when Tag =:= contract_main;
       Tag =:= contract_child;
       Tag =:= contract_interface;
       Tag =:= namespace ->
    Env1 = push_scope(Con, Env0),
    Env2 = register_stateful(Defs, Env1),
    Env3 = pop_scope(Env2),
    register_stateful(Rest, Env3);
register_stateful([LF|Rest], Env)
  when element(1, LF) =:= letfun;
       element(1, LF) =:= fundecl ->
    Env1 = case aeso_syntax:get_ann(stateful, LF, false) of
               true  -> set_stateful(element(3, LF), Env);
               false -> Env
           end,
    register_stateful(Rest, Env1);
register_stateful([_|Rest], Env) ->
    register_stateful(Rest, Env);
register_stateful([], Env) ->
    Env.


constr_expr_list(Env, Es, S) ->
    constr_expr_list(Env, Es, [], S).
constr_expr_list(_, [], Acc, S) ->
    {lists:reverse(Acc), S};
constr_expr_list(Env, [H|T], Acc, S0) ->
    {H1, S1} = constr_expr(Env, H, S0),
    constr_expr_list(Env, T, [H1|Acc], S1).

constr_expr(Env, ?typed_p(Expr, Type), S0) ->
    Base = base_type(Type),
    case Base /= Type andalso has_assumptions(Type) of
        false ->
            %% Nothing interesting
            constr_expr(Env, Expr, Type, S0);
        true ->
            DType = fresh_liquid(Env, "typed", Type),
            {ExprT, S1} = constr_expr(Env, Expr, Base, S0),
            {ExprT,
             %% Inferred type <: Declared type, because the user can generalize Cat to Animal
             [ {subtype, constr_id(typed), ?ann_of(Type), Env, ExprT, DType}
             , {well_formed, constr_id(typed), Env, DType}
             | S1
             ]
            }
    end;
constr_expr(Env, ?typed_p(Expr, T), S) ->
    constr_expr(Env, Expr, T, S);
constr_expr(_, X, _) ->
    error({untyped, X}).

constr_expr(Env, {app, Ann, F, Args}, RetT, S)
  when element(1, F) =/= typed ->
    %% Here we fix the untyped operators
    ArgTypes = [ArgT || {typed, _, _, ArgT} <- Args],
    TypedF = {typed, Ann, F, {fun_t, Ann, [], ArgTypes, RetT}},
    constr_expr(Env, {app, Ann, TypedF, Args}, RetT, S);
constr_expr(Env, {block, Ann, Stmts}, T, S) ->
    ExprT = fresh_liquid(Env, "block", T),
    {RestT, S1} = constr_expr(Env, Stmts, T, S),
    { ExprT,
     [ {well_formed, constr_id(block), Env, ExprT}
     , {subtype, constr_id(block), Ann, Env, RestT, ExprT}
     | S1
     ]
    };
constr_expr(Env, {typed, Ann, E, T1}, T2, S0) ->
    DT2 = fresh_liquid(Env, "typed", T2),
    {DT1, S1} = constr_expr(Env, E, T1, S0),
    {DT2,
     [ {well_formed, constr_id(exp_typed), Env, DT2}
     , {subtype, constr_id(exp_typed), Ann, Env, DT1, DT2}
     | S1
     ]
    };
constr_expr(Env, Expr = {IdHead, Ann, Name}, T, S)
  when IdHead =:= id; IdHead =:= qid ->
    DT = fresh_liquid(Env, Name, T), %% This is to solve aliases etc
    BaseT = base_type(DT),
    if element(1, BaseT) =:= id;
       element(1, BaseT) =:= tvar ->
            {?refined(BaseT, [?op(Ann, ?nu(Ann), '==', Expr)]), S};
       element(1, DT) =:= dep_list_t ->
            {dep_list_t, TAnn, _, ElemT, _} = DT,
            FreshId = fresh_id(Ann, Name),
            {{dep_list_t, TAnn, FreshId, ElemT, [?op(Ann, FreshId, '==', Expr)]},
             [{well_formed, constr_id(IdHead), Env, DT}|S]
            };
       true ->
            case type_of(Env, Expr) of
                {_, _, DT1} ->
                    {DT1, S};
                undefined ->
                    {DT,
                     [ {well_formed, constr_id(IdHead), Env, DT}
                     | S
                     ]
                    }
            end
    end;
constr_expr(_Env, I = {int, Ann, _}, T = ?int_tp, S) ->
    {?refined(T, [?op(Ann, ?nu(Ann), '==', I)]), S};
constr_expr(_Env, I = {char, Ann, _}, T, S) ->
    {?refined(T, [?op(Ann, ?nu(Ann), '==', I)]), S};
constr_expr(_Env, {address, _, _}, T, S0) ->
    {?refined(T), S0};
constr_expr(_Env, {string, _, _}, T, S0) ->
    {?refined(T), S0};
constr_expr(_Env, {bool, Ann, B}, T, S) ->
    {?refined(T, [if B -> ?nu(Ann); true -> ?op(Ann, '!', ?nu(Ann)) end]), S};

?STDLIB_CONSTRS

constr_expr(Env, {tuple, Ann, Elems}, _, S0) ->
    {ElemsT, S1} = constr_expr_list(Env, Elems, S0),
    {{tuple_t, Ann, ElemsT},
     S1
    };
constr_expr(Env, {record, Ann, FieldVals}, T, S0) ->
    {Fields, Vals} =
        lists:unzip([{Field, Val} || {field, _, [{proj, _, Field}], Val} <- FieldVals]),
    {ValsT, S1} = constr_expr_list(Env, Vals, S0),
    {{dep_record_t, Ann, T,
      [{field_t, ?ann_of(Field), Field, ValT}
       || {Field, ValT} <- lists:zip(Fields, ValsT)]},
     S1
    };
constr_expr(Env, {record, Ann, Expr, FieldVals}, T, S0) ->
    {{dep_record_t, _, _, Fields}, S1} = constr_expr(Env, Expr, S0),
    Fields1S =
        [ case [{FAnn, Val} || {field, FAnn, [{proj, _, {id, _, UpdFname}}], Val} <- FieldVals, UpdFname == FName] of
              [] -> {Field, []};
              [{FAnn, Val}] ->
                  {ValT, S} = constr_expr(Env, Val, []),
                  {{field_t, FAnn, FId, ValT}, S}
          end
         || Field = {field_t, _, FId = {id, _, FName}, _} <- Fields
        ],
    {Fields1, Ss} = lists:unzip(Fields1S),
    S2 = lists:concat(Ss) ++ S1,
    {{dep_record_t, Ann, T, Fields1},
     S2
    };
constr_expr(_Env0, {list_comp, _Ann, _Yield, _Gens}, _T, _S0) ->
    error({list_comprehension_not_supported});

constr_expr(_Env, Expr = {CmpOp, Ann}, {fun_t, _, _, [OpLT, OpRT], RetT = ?bool_tp}, S)
  when CmpOp =:= '<';
       CmpOp =:= '=<';
       CmpOp =:= '>';
       CmpOp =:= '>=';
       CmpOp =:= '==';
       CmpOp =:= '!=' ->
    OpLV = fresh_id(?ann_of(OpLT), "opl"),
    OpRV = fresh_id(?ann_of(OpRT), "opr"),
    { {dep_fun_t, Ann,
       [ {dep_arg_t, ?ann_of(OpLT), OpLV, ?refined(OpLV, OpLT, [])}
       , {dep_arg_t, ?ann_of(OpRT), OpRV, ?refined(OpRV, OpRT, [])}
       ],
       ?refined(RetT, [?op(Ann, ?nu(Ann), '==', {app, [{format, infix}|Ann], Expr, [OpLV, OpRV]})])
      }
    , S
    };
constr_expr(_Env, Expr = {Op, Ann}, {fun_t, _, _, [OpLT, OpRT], RetT}, S)
  when Op =:= '&&';
       Op =:= '||';
       Op =:= '+';
       Op =:= '*';
       Op =:= '-';
       Op =:= '/';
       Op =:= 'mod';
       Op =:= '^' ->
    OpLV = fresh_id(?ann_of(OpLT), "opl"),
    OpRV = fresh_id(?ann_of(OpRT), "opr"),
    { {dep_fun_t, Ann,
       [ {dep_arg_t, ?ann_of(OpLT), OpLV, ?refined(OpLV, OpLT, [])}
       , {dep_arg_t, ?ann_of(OpRT), OpRV,
          ?refined(OpRV, OpRT,
                   case Op of
                       'mod' -> [?op(Ann, OpRV, '>',  ?int(Ann, 0))];
                       '/'   -> [?op(Ann, OpRV, '!=', ?int(Ann, 0))];
                       '^'   -> [?op(Ann, OpRV, '>=', ?int(Ann, 0))];
                       _     -> []
                   end)}
       ], ?refined(RetT, [?op(Ann, ?nu(Ann), '==', {app, [{format, infix}|Ann], Expr, [OpLV, OpRV]})])
      }
    , S
    };
constr_expr(_Env, Expr = {'-', Ann}, T, S) ->
    N = fresh_id(Ann, "n"),
    { {dep_fun_t, Ann,
       [{dep_arg_t, Ann, N, ?refined(N, ?int_t(?ann_of(T)), [])}],
       ?refined(?int_t(?ann_of(T)),
                [?op(Ann, ?nu(Ann), '==', {app, [{format, prefix}|Ann], Expr, [N]})])
      }
    , S
    };
constr_expr(Env, {app, Ann, ?typed_p({'::', OpAnn}), [OpL, OpR]}, {app_t, _, {id, _, "list"}, [ElemT]}, S0) ->
    {DepElemLT, S1} = constr_expr(Env, OpL, S0),
    {{dep_list_t, _, _, DepElemRT, _}, S2} = constr_expr(Env, OpR, S1),
    DepElemT = fresh_liquid(Env, "elem_cat", ElemT),
    Id = fresh_id(Ann, "cons"),
    LenPred = [?op(Ann, Id, '==', ?op(OpAnn, OpR, '+', ?int(OpAnn, 1)))],
    {{dep_list_t, Ann, Id, DepElemT, LenPred},
     [ {well_formed, constr_id(cons), Env, DepElemT}
     , {subtype, constr_id(cons), Ann, Env, DepElemLT, DepElemT}
     , {subtype, constr_id(cons), Ann, Env, DepElemRT, DepElemT}
     | S2
     ]
    };
constr_expr(Env, {app, Ann, ?typed_p({'++', OpAnn}), [OpL, OpR]}, {app_t, _, {id, _, "list"}, [ElemT]}, S0) ->
    {{dep_list_t, _, _, DepElemLT, _}, S1} = constr_expr(Env, OpL, S0),
    {{dep_list_t, _, _, DepElemRT, _}, S2} = constr_expr(Env, OpR, S1),
    DepElemT = fresh_liquid(Env, "elem_cat", ElemT),
    Id = fresh_id(Ann, "cat"),
    LenPred = [?op(OpAnn, Id, '==', ?op(OpAnn, OpL, '+', OpR))],
    {{dep_list_t, Ann, Id, DepElemT, LenPred},
     [ {well_formed, constr_id(cat), Env, DepElemT}
     , {subtype, constr_id(cat), Ann, Env, DepElemLT, DepElemT}
     , {subtype, constr_id(cat), Ann, Env, DepElemRT, DepElemT}
     | S2
     ]
    };
constr_expr(Env, {app, Ann, ?typed_p({id, _, "abort"}), _}, T, S0) ->
    ExprT = fresh_liquid(Env, "abort", T),
    {ExprT,
     [ {unreachable, constr_id(abort), Ann, Env}
     , {well_formed, constr_id(abort), Env, ExprT}
     |S0
     ]
    };
constr_expr(Env, {con, Ann, "None"}, Type, S0) ->
    constr_expr(Env, {app, Ann, ?typed({qcon, Ann, ["None"]}, Type), []}, Type, S0);
constr_expr(Env, QCon = {qcon, Ann, _}, Type = {fun_t, _, _, ArgsT, RetT}, S0) ->
    %% Lambda-constructor
    Args = [ fresh_id(?ann_of(ArgT), "con_arg", ArgT) || ArgT <- ArgsT],
    Lam =
        {lam, Ann,
         [ {arg, ?ann_of(ArgT), Arg, ArgT}
           || {?typed_p(Arg), ArgT} <- lists:zip(Args, ArgsT)
         ],
         ?typed({app, Ann, QCon, Args}, RetT)
        },
    constr_expr(Env, Lam, Type, S0);
constr_expr(Env, QCon = {qcon, Ann, _}, Type, S0) ->
    %% Nullary constructor
    constr_expr(Env, {app, Ann, ?typed(QCon, Type), []}, Type, S0);
constr_expr(Env, {app, Ann, ?typed_p({con, CAnn, "Some"}, CType), Args}, Type, S0) ->
    constr_expr(Env, {app, Ann, ?typed({qcon, CAnn, ["Some"]}, CType), Args}, Type, S0);
constr_expr(Env, {app, Ann, ?typed_p(QCon = {qcon, _, QName}), Args}, Type, S0) ->
    {TypeQid, AppliedTypeArgs} =
        case Type of
            {qid, _, _} -> {Type, []};
            {app_t, _, T, A} -> {T, A}
        end,
    {ArgsT, S1} = constr_expr_list(Env, Args, S0),
    {_, _, {DeclaredTypeArgs, {variant_t, Constrs}}} = lookup_type(Env, TypeQid),
    TypeSubst = lists:zip(DeclaredTypeArgs, AppliedTypeArgs),

    DepConstrs =
        [ {constr_t, CAnn, Con,
           case lists:last(QName) == name(Con) of
               true  -> ArgsT;
               false -> [?refined(Arg, [?bool(CAnn, false)]) || Arg <- ConArgs]
           end
          }
          || {constr_t, CAnn, Con, ConArgs} <- Constrs
        ],
    Id = fresh_id(Ann, lists:last(QName)),
    {{dep_variant_t, Ann, Id, Type, [{is_tag, Ann, Id, QCon, ArgsT, Type}],
      apply_subst(TypeSubst, DepConstrs)},
     S1
    };
constr_expr(Env, {app, Ann, F = ?typed_p(_, {fun_t, _, NamedT, _, _}), Args0}, _, S0) ->
    NamedArgs = [Arg || Arg = {named_arg, _, _, _} <- Args0],
    Args =
        [ case [ArgValue
                || {named_arg, _, ArgName, ArgValue} <- NamedArgs,
                   ArgName == TArgName
               ] of
              [Arg] -> Arg;
              [] -> TArgDefault
          end
         || {named_arg_t, _, TArgName, _, TArgDefault} <- NamedT
        ] ++ (Args0 -- NamedArgs),
    {_FDT = {dep_fun_t, _, ArgsFT, RetT}, S1} = constr_expr(Env, F, S0),
    {ArgsT, S2} = constr_expr_list(Env, Args, S1),
    ArgSubst = [{X, Expr} || {{dep_arg_t, _, X, _}, Expr} <- lists:zip(ArgsFT, Args)],
    RetT1 = apply_subst(ArgSubst, RetT),
    { RetT1
    , [{subtype, constr_id(app), [{context, {app, Ann, F, N}}|?ann_of(ArgT)],
        Env, ArgT, ArgFT}
       || {{dep_arg_t, _, _, ArgFT}, ArgT, N} <- lists:zip3(ArgsFT, ArgsT, lists:seq(1, length(ArgsT)))
      ] ++ S2
    };
constr_expr(Env, {'if', Ann, Cond, Then, Else}, T, S0) ->
    ExprT = fresh_liquid(Env, "if", T),
    {_, S1} = constr_expr(Env, Cond, S0),
    EnvThen = assert(Cond, Env),
    EnvElse = assert(?op(Ann, '!', Cond), Env),
    {ThenT, S2} = constr_expr(EnvThen, Then, S1),
    {ElseT, S3} = constr_expr(EnvElse,Else, S2),
    { ExprT
    , [ {well_formed, constr_id('if'), Env, ExprT}
      , {reachable, constr_id(then), ?ann_of(Then), EnvThen}
      , {reachable, constr_id(else), ?ann_of(Else), EnvElse}
      , {subtype, constr_id(then), [{context, then}|?ann_of(Then)], EnvThen, ThenT, ExprT}
      , {subtype, constr_id(else), [{context, else}|?ann_of(Else)], EnvElse, ElseT, ExprT}
      | S3
      ]
    };
constr_expr(Env, {switch, _, Switched, Alts}, T, S0) ->
    ExprT = fresh_liquid(Env, "switch", T),
    {SwitchedT, S1} = constr_expr(Env, Switched, S0),
    S2 = constr_cases(Env, Switched, SwitchedT, ExprT, Alts, S1),
    {ExprT
    , [{well_formed, constr_id(switch), Env, ExprT}|S2]
    };
constr_expr(Env, {lam, _, Args, Body}, {fun_t, TAnn, [], _, RetT}, S0) ->
    {DepArgsT, ArgSubst} = fresh_liquid_args(Env, Args),
    RetT1 = apply_subst(ArgSubst, RetT),
    DepRetT = fresh_liquid(Env, "lam", RetT1),
    ExprT = {dep_fun_t, TAnn, DepArgsT, DepRetT},
    EnvBody = bind_args(DepArgsT, Env),
    {BodyT, S1} = constr_expr(EnvBody, Body, S0),
    {ExprT,
     [ {well_formed, constr_id(lam), Env, {dep_fun_t, TAnn, DepArgsT, DepRetT}}
     , {subtype, constr_id(lam), ?ann_of(Body), EnvBody, BodyT, DepRetT}
     | S1
     ]
    };
constr_expr(Env, {proj, Ann, Rec, Field}, T, S0) ->
    ExprT = fresh_liquid(Env, "proj", T),
    {{dep_record_t, _, BaseRec, Fields}, S1} = constr_expr(Env, Rec, S0),
    RecId = case BaseRec of
                {app_t, _, Id, _} -> Id;
                _ -> BaseRec
            end,
    case ExprT of
        {refined_t, TAnn, TId, TBase, _} ->
            {{refined_t, TAnn, TId, TBase,
              [?op(Ann, TId, '==', {proj, Ann, Rec, qid(Ann, qname(RecId) ++ [name(Field)])})]},
             S1
            };
        _ ->
            [FieldT] =
                [ RecFieldT
                  || {field_t, _, RecFieldName, RecFieldT} <- Fields,
                     name(Field) == name(RecFieldName)
                ],
            {ExprT,
             [ {well_formed, constr_id(proj), Env, ExprT}
             , {subtype, constr_id(proj), Ann, Env, FieldT, ExprT}
             | S1
             ]
            }
    end;
constr_expr(Env, {list, Ann, Elems}, {app_t, TAnn, _, [ElemT]}, S0) ->
    DepElemT = fresh_liquid(Env, "list", ElemT),
    {DepElemsT, S1} = constr_expr_list(Env, Elems, S0),
    S2 =
        [ {subtype, constr_id(list), Ann, Env, DepElemTI, DepElemT}
         || DepElemTI <- DepElemsT
        ] ++ S1,
    Id = fresh_id(Ann, "list"),
    {{dep_list_t, TAnn, Id, DepElemT, [?op(Ann, Id, '==', ?int(Ann, length(Elems)))]},
     [ {well_formed, constr_id(list), Env, DepElemT}
     | S2
     ]
    };

constr_expr(Env, [E], T, S0) ->
    constr_expr(Env, E, T, S0);
constr_expr(Env0, [{letval, Ann, Pat, Val}|Rest], T, S0) ->
    ExprT = fresh_liquid(Env0, "letval", T),
    {ValT, S1} = constr_expr(Env0, Val, S0),
    {Env1, EnvFail} = match_to_pattern(Env0, Pat, Val, ValT),
    {RestT, S2} = constr_expr(Env1, Rest, T, S1),
    {ExprT,
     [ {well_formed, constr_id(letval), Env0, ExprT}
     , {subtype, constr_id(letval), Ann, Env1, RestT, ExprT}
     , {unreachable, constr_id(letval), Ann, EnvFail}
     | S2
     ]
    };
constr_expr(Env0, [{letfun, Ann, Id, Args, RetT, Body}|Rest], T, S0) ->
    ArgsTypes = [ArgT || {typed, _, _, ArgT} <- Args],
    ExprT = {fun_t, Ann, [], ArgsTypes, RetT},
    constr_expr(
      Env0,
      [ {letval, Ann, ?typed(Id, ExprT),
         ?typed(
            {lam, Ann,
             [ {arg, ArgAnn, ArgId, ArgT}
               || {typed, ArgAnn, ArgId, ArgT} <- Args
             ], Body},
            ExprT)
           }
      | Rest
      ], T, S0
     );
constr_expr(Env,
            [ ?typed_p({app, Ann, {typed, _, {id, _, "require"}, _}, [Cond, _]})
            | Rest
            ], T, S0) ->
    Env1 = assert(Cond, Env),
    constr_expr(Env1, Rest, T, [{reachable, constr_id(require), Ann, Env1}|S0]);
constr_expr(Env, [Expr|Rest], T, S0) ->
    {_, S1} = constr_expr(Env, Expr, S0),
    {RestT, S2} = constr_expr(Env, Rest, T, S1),
    {RestT,
     S2
    };
constr_expr(_Env, [], T, S) ->
    {T, S};
constr_expr(_, A, B, _) ->
    error({todo, A, B}).

constr_cases(_Env, _Switched, _SwitchedT, _ExprT, Alts, S) ->
    constr_cases(_Env, _Switched, _SwitchedT, _ExprT, Alts, 1, S).
constr_cases(Env, Switched, _SwitchedT, _ExprT, [], _N, S) ->
    [{unreachable, constr_id(switch_trap), ?ann_of(Switched), Env}|S];
constr_cases(Env0, Switched, SwitchedT, ExprT,
             [{'case', Ann, Pat, Case}|Rest], N, S0) ->
    {EnvCase, EnvCont} = match_to_pattern(Env0, Pat, Switched, SwitchedT),
    {CaseDT, S1} = constr_expr(EnvCase, Case, S0),
    constr_cases(EnvCont, Switched, SwitchedT, ExprT, Rest,
                 [ {subtype, constr_id('case'), [{context, {switch, N}}|Ann], EnvCase, CaseDT, ExprT}
                 , {reachable, constr_id('case'), Ann, EnvCase}
                 | S1
                 ]
                ).

%% match_to_pattern computes
%%   - Env which will bind variables
%%   - Env which asserts that the match cannot succeed
-spec match_to_pattern(env(), pat(), expr(), type()) -> {env(), env()}.
match_to_pattern(Env0, Pat, Expr, Type) ->
    {Env1, Pred} = match_to_pattern(Env0, Pat, Expr, Type, []),
    EnvMatch = assert(Pred, Env1),
    EnvNoMatch =
        case Pred of
            [] -> assert(?bool(?ann_of(Pat), false), Env0);
            [H|T] ->
                PredExpr = lists:foldl(
                             fun(E, Acc) -> ?op(?ann_of(E), E, '&&', Acc)
                             end, H, T
                            ),
                assert(?op(?ann_of(Pat), '!',  PredExpr), Env0)
        end,
    {EnvMatch, EnvNoMatch}.
match_to_pattern(Env, {typed, _, Pat, _}, Expr, Type, Pred) ->
    match_to_pattern(Env, Pat, Expr, Type, Pred);
match_to_pattern(Env, {id, _, "_"}, _Expr, _Type, Pred) ->
    {Env, Pred};
match_to_pattern(Env, Id = {id, _, _}, _Expr, Type, Pred) ->
    {bind_var(Id, Type, Env), Pred};
match_to_pattern(Env, _Pat, {id, _, "_"}, _Type, Pred) ->
    {Env, Pred}; % Useful in lists
match_to_pattern(Env, I = {int, Ann, _}, Expr, _Type, Pred) ->
    {Env, [?op(Ann, Expr, '==', I)|Pred]};
match_to_pattern(Env, {bool, _, true}, Expr, _Type, Pred) ->
    {Env, [Expr|Pred]};
match_to_pattern(Env, {bool, Ann, false}, Expr, _Type, Pred) ->
    {Env, [?op(Ann, '!', Expr)|Pred]};
match_to_pattern(Env, {tuple, _, Pats}, Expr, {tuple_t, _, Types}, Pred) ->
    N = length(Pats),
    lists:foldl(
      fun({{Pat, PatT}, I}, {Env0, Pred0}) ->
              Ann = ?ann_of(Pat),
              Proj = {proj, Ann, Expr, ?tuple_proj_id(Ann, N, I)},
              match_to_pattern(Env0, Pat, Proj, PatT, Pred0)
      end,
      {Env, Pred}, lists:zip(lists:zip(Pats, Types), lists:seq(1, N))
     );
match_to_pattern(Env, {record, _, Fields}, Expr, {dep_record_t, _, Type, FieldsT}, Pred) ->
    FieldTypes =
        [{field_t, Ann, Field, FieldT} || {{id, Ann, Field}, FieldT} <- FieldsT],
    Qid = case Type of
              {qid, _, _} -> Type;
              {app_t, _, Q, _} -> Q
          end,
    lists:foldl(
      fun({field, _, [{proj, _, Field}], Pat}, {Env0, Pred0}) ->
              PatT = proplists:get_value(name(Field), FieldTypes),
              Ann = ?ann_of(Pat),
              Proj = {proj, Ann, Expr, qid(?ann_of(Field), qname(Qid) ++ [name(Field)])},
              match_to_pattern(Env0, Pat, Proj, PatT, Pred0)
      end,
      {Env, Pred}, Fields
     );
match_to_pattern(Env, {con, Ann, CName}, Expr, DepT, Pred0) ->
    match_to_pattern(Env, {qcon, Ann, [CName]}, Expr, DepT, Pred0);
match_to_pattern(Env, QCon = {qcon, Ann, _},
                 Expr, DepT = {dep_variant_t, _, _, Type, _, _}, Pred0) ->
    %% This is for sure a nullary constructor
    match_to_pattern(Env, {app, Ann, ?typed(QCon, Type), []}, Expr, DepT, Pred0);
match_to_pattern(Env, {app, Ann, ?typed_p({con, Ann, CName}, T), Args}, Expr, DepT, Pred0) ->
    match_to_pattern(Env, {app, Ann, ?typed({qcon, Ann, [CName]}, T), Args}, Expr, DepT, Pred0);
match_to_pattern(Env, {app, Ann, ?typed_p(QCon = {qcon, _, QName}), Args},
                 Expr, {dep_variant_t, _, _, Type, _Tag, Constrs}, Pred0) ->
    N = length(Args),
    [ArgTypes] =
        [ ConArgs
         || {constr_t, _, {con, _, CName}, ConArgs} <- Constrs,
            lists:last(QName) == CName
        ],
    Pred1 = [{is_tag, Ann, Expr, QCon, ArgTypes, Type}|Pred0],
    lists:foldl(
      fun({{Arg, ArgT}, I}, {Env0, Pred}) ->
              ArgAnn = ?ann_of(Arg),
              Proj = {proj, ArgAnn, Expr, ?adt_proj_id(Ann, QCon, I)},
              match_to_pattern(Env0, Arg, Proj, ArgT, Pred)
      end,
      {Env, Pred1}, lists:zip(lists:zip(Args, ArgTypes), lists:seq(1, N))
     );
match_to_pattern(Env, {list, Ann, Pats}, Expr, {dep_list_t, _, _, ElemT, _}, Pred) ->
    N = length(Pats),
    lists:foldl(
      fun(Pat, {Env0, Pred0}) ->
              match_to_pattern(Env0, Pat, {id, ?ann_of(Pat), "_"}, ElemT, Pred0)
      end,
      {Env, [?op(Ann, Expr, '==', ?int(Ann, N)) | Pred]}, Pats
     );
match_to_pattern(Env0, {app, Ann, ?typed_p({'::', OpAnn}), [H,T]}, Expr, {dep_list_t, TAnn, _, ElemT, _}, Pred0) ->
    Pred1 = [ ?op(OpAnn, Expr, '>', ?int(OpAnn, 0))
            | Pred0
            ],
    {Env1, Pred2} = match_to_pattern(Env0, H, {id, Ann, "_"}, ElemT, Pred1),
    Id = fresh_id(Ann, "cons"),
    TailT = {dep_list_t, TAnn, Id, ElemT,
             [ ?op(OpAnn, Id, '==', ?op(OpAnn, Expr, '-', ?int(OpAnn, 1)))
             ]},
    Env2 = bind_var(Id, TailT, Env1),
    match_to_pattern(Env2, T, Id, TailT, Pred2).

%% -- Substitution -------------------------------------------------------------

apply_subst({id, _, N}, {id, _, N}, In) ->
    In;
apply_subst({id, _, X}, Expr, {id, _, X}) ->
    Expr;
apply_subst({qid, _, X}, Expr, {qid, _, X}) ->
    Expr;
apply_subst({tvar, _, X}, Expr, {tvar, _, X}) ->
    Expr;
apply_subst({ltvar, X}, Expr, {ltvar, X}) ->
    Expr;
apply_subst(X, Expr, {template, S1, T}) ->
    {template, [{X, Expr}|S1], T};
apply_subst({id, _, Name}, _, T = {refined_t, _, {id, _, Name}, T, _}) ->
    T;
apply_subst({id, _, Name}, _, T = {dep_list_t, _, {id, _, Name}, T, _}) ->
    T;
apply_subst(X, Expr, {refined_t, Ann, Id, T, Qual}) ->
    {refined_t, Ann, Id, apply_subst(X, Expr, T), apply_subst(X, Expr, Qual)};
apply_subst(X, Expr, {dep_list_t, Ann, Id, T, Qual}) ->
    {dep_list_t, Ann, Id, apply_subst(X, Expr, T), apply_subst(X, Expr, Qual)};
apply_subst(X, Expr, {dep_fun_t, Ann, Args, RetT}) ->
    {dep_fun_t, Ann, apply_subst(X, Expr, Args),
     case X of
         {id, _, Name} ->
             case [{} || {dep_arg_t, _, {id, _, ArgName}, _} <- Args, ArgName =:= Name] of
                 [] -> apply_subst(X, Expr, RetT);
                 _ -> RetT
             end;
         _ -> apply_subst(X, Expr, RetT)
     end
    };
apply_subst(X, Expr, [H|T]) -> [apply_subst(X, Expr, H)|apply_subst(X, Expr, T)];
apply_subst(X, Expr, T) when is_tuple(T) ->
    list_to_tuple(apply_subst(X, Expr, tuple_to_list(T)));
apply_subst(_X, _Expr, X) -> X.

apply_subst(Subs, Q) when is_map(Subs) ->
    apply_subst(maps:to_list(Subs), Q);
apply_subst(Subs, Q) when is_list(Subs) ->
    lists:foldl(fun({X, Expr}, Q0) -> apply_subst(X, Expr, Q0) end, Q, Subs).


%% -- Assignments --------------------------------------------------------------

cmp_qualifiers(SelfId, Thing) ->
    %% [].
    [ ?op(?ann_of(SelfId), SelfId, '=<', Thing)
    , ?op(?ann_of(SelfId), SelfId, '>=', Thing)
    , ?op(?ann_of(SelfId), SelfId, '>', Thing)
    , ?op(?ann_of(SelfId), SelfId, '<', Thing)
    ].

eq_qualifiers(SelfId, Thing) ->
    [ ?op(?ann_of(SelfId), SelfId, '==', Thing)
    , ?op(?ann_of(SelfId), SelfId, '!=', Thing)
    ].

int_qualifiers(SelfId, Thing) ->
    cmp_qualifiers(SelfId, Thing) ++ eq_qualifiers(SelfId, Thing).

plus_int_qualifiers(_, {int, _, 0}, _Thing) -> [];
plus_int_qualifiers(SelfId, Int, Thing) ->
    int_qualifiers(SelfId, ?op(?ann_of(SelfId), Thing, '+', Int)) ++
    int_qualifiers(SelfId, ?op(?ann_of(SelfId), Thing, '-', Int)).

var_int_qualifiers(SelfId, Var) ->
    int_qualifiers(SelfId, Var) ++ plus_int_qualifiers(SelfId, ?int(?ann_of(SelfId), 1), Var).

inst_pred_variant_tag(SelfId, Qid, Type, Constrs, Subst) ->
    [ {is_tag, ?ann_of(SelfId), SelfId,
       qcon(?ann_of(Con), lists:droplast(qname(Qid)) ++ qname(Con)),
       apply_subst(Subst, Args),
       apply_subst(Subst, Type)}
      || {constr_t, _, Con, Args} <- Constrs
    ] ++
    [ ?op(?ann_of(SelfId), '!', {is_tag, ?ann_of(SelfId), SelfId,
                                 qcon(?ann_of(Con), lists:droplast(qname(Qid)) ++ qname(Con)),
                                 apply_subst(Subst, Args),
                                 apply_subst(Subst, Type)})
      || {constr_t, _, Con, Args} <- Constrs
    ].

inst_pred_int(Env, SelfId) ->
    lists:concat(
      [ [Q || CoolInt <- Env#env.cool_ints,
              Q <- int_qualifiers(SelfId, ?int(?ann_of(SelfId), CoolInt))
        ]
      , [ Q || {Var, {refined_t, _, _, ?int_tp, _}} <- prim_type_binds(Env),
               Q <- var_int_qualifiers(SelfId, Var)
        ]
      , [ Q || {Var, {dep_list_t, _, _, _, _}} <- prim_type_binds(Env),
               Q <- var_int_qualifiers(SelfId, Var)
        ]
      ]
     ).

inst_pred_bool(Env, SelfId) ->
    lists:concat(
      [ [Q || CoolBool <- [true, false],
              Q <- eq_qualifiers(SelfId, ?bool(?ann_of(SelfId), CoolBool))
        ]
      , [ Q || {Var, {refined_t, _, _, ?bool_tp, _}} <- prim_type_binds(Env),
               Q <- eq_qualifiers(SelfId, Var)
        ]
      , [ BQ
         || {Var, T} <- prim_type_binds(Env),
            Q <- case T of
                     {refined_t, _, _, ?int_tp, _} -> inst_pred_int(Env, Var);
                     {dep_list_t, _, _, _, _} -> inst_pred_int(Env, Var);
                     {refined_t, _, _, {tvar, _, TVar}, _} -> inst_pred_tvar(Env, Var, TVar);
                     _ -> [] %% TODO Variants and records. Beware O(n^2)
                 end,
            BQ <- [?op(?ann_of(T), SelfId, '==', Q), ?op(?ann_of(T), SelfId, '!=', Q)]
        ]
      ]
     ).

inst_pred_tvar(Env, SelfId, TVar) ->
    [ Q || {Var, {refined_t, _, _, {tvar, _, TVar1}, _}} <- prim_type_binds(Env),
           TVar == TVar1,
           Q <- eq_qualifiers(SelfId, Var)
    ] ++ [?bool(?ann_of(SelfId), false)].

inst_pred(Env, SelfId, {dep_list_t, Ann, _, _, _}) ->
    inst_pred(Env, SelfId, ?int_t(Ann));
inst_pred(Env, SelfId, {dep_record_t, _, BaseT, _}) ->
    inst_pred(Env, SelfId, BaseT);
inst_pred(Env, SelfId, {dep_variant_t, _, _, BaseT, _, _}) ->
    inst_pred(Env, SelfId, BaseT);
inst_pred(Env, SelfId, {refined_t, _, _, BaseT, _}) ->
    inst_pred(Env, SelfId, BaseT);
inst_pred(Env = #env{tc_env = TCEnv}, SelfId, BaseT) ->
    case BaseT of
        ?int_tp ->
            inst_pred_int(Env, SelfId);
        ?bool_tp ->
            inst_pred_bool(Env, SelfId);
        {qid, _, _} ->
            case lookup_type(Env, BaseT) of
                {_, _, {[], {variant_t, Constrs}}} ->
                    inst_pred_variant_tag(
                      SelfId, BaseT, BaseT, aeso_ast_infer_types:unfold_types_in_type(TCEnv, Constrs, []), []);
                X -> error({todo, {inst_pred, X}})
            end;
        {app_t, _, Qid = {qid, _, _}, Args} ->
            case lookup_type(Env, Qid) of
                {_, _, {AppArgs, {variant_t, Constrs}}} ->
                    Subst = lists:zip(Args, AppArgs),
                    inst_pred_variant_tag(
                      SelfId,
                      Qid,
                      BaseT,
                      aeso_ast_infer_types:unfold_types_in_type(TCEnv, Constrs, []),
                      Subst
                     );
                X -> error({todo, {inst_pred, X}})
            end;
        {tvar, _, TVar} ->
            inst_pred_tvar(Env, SelfId, TVar);
        _ -> []
    end.

init_assg(Cs) ->
    lists:foldl(
      fun({well_formed, _, Env, {refined_t, _, Id, BaseT, {template, _, LV}}}, Acc) ->
              AllQs = inst_pred(Env, Id, BaseT),
              Acc#{LV => #ltinfo{id = Id, base = BaseT, env = Env, predicate = AllQs}};
         (_, Acc) ->
              Acc
      end, #{}, Cs).

assg_of(Assg, {template, Subst, Var}) ->
    apply_subst(Subst, assg_of(Assg, Var));
assg_of(Assg, Var = {ltvar, _}) ->
    case maps:get(Var, Assg, undef) of
        undef -> error({undef_assg, Var});
        A -> A
    end.


apply_assg(Assg, Var = {ltvar, _}) ->
    case maps:get(Var, Assg, false) of
        #ltinfo{predicate = P} ->
            P;
        false -> []
    end;
apply_assg(Assg, {template, S, T}) ->
    apply_assg(Assg, apply_subst(S, T));
apply_assg(Assg, [H|T]) -> [apply_assg(Assg, H)|apply_assg(Assg, T)];
apply_assg(Assg, T) when is_tuple(T) ->
    list_to_tuple(apply_assg(Assg, tuple_to_list(T)));
apply_assg(_, X) -> X.


pred_of(Assg, Var = {ltvar, _}) ->
    (assg_of(Assg, Var))#ltinfo.predicate;
pred_of(_, P) when is_list(P)   ->
    P;
pred_of(Assg, {template, Subst, P}) ->
    apply_subst(Subst, pred_of(Assg, P));
pred_of(Assg, {refined_t, _, _, _, P}) ->
    pred_of(Assg, P);
pred_of(Assg, Env = #env{path_pred = PathPred}) ->
    ScopePred = type_binds_pred(Assg, type_binds(Env)),
    ScopePred ++ PathPred;
pred_of(_, _) ->
    [].

type_binds_pred(Assg, TB) ->
    type_binds_pred(Assg, fun(X) -> X end, TB).
type_binds_pred(Assg, Access, TB) ->
    [ Q
     || {Var, Type} <- TB,
        Q <- case Type of
                 {refined_t, _, Id, _, P} ->
                     apply_subst(Id, Access(Var), pred_of(Assg, P));
                 {tuple_t, Ann, Fields} ->
                     N = length(Fields),
                     type_binds_pred(
                       Assg,
                       fun(X) -> {proj, Ann, Access(Var), X} end,
                       lists:zip(
                         [?tuple_proj_id(Ann, N, I) || I <- lists:seq(1, N)],
                         Fields
                        )
                      );
                 {dep_record_t, Ann, RT, Fields} ->
                     QName = case RT of
                                 {qid, _, Q} -> Q;
                                 {app_t, _, {qid, _, Q}, _} -> Q
                             end,
                     type_binds_pred(
                       Assg,
                       fun(X) -> {proj, Ann, Access(Var), X} end,
                       [{qid(FAnn, QName ++ [name(Field)]), T}
                        || {field_t, FAnn, Field, T} <- Fields]
                      );
                 {dep_variant_t, _, Id, VT, Tag, Constrs} ->
                     QName = case VT of
                                 {qid, _, Q} -> Q;
                                 {app_t, _, {qid, _, Q}, _} -> Q;
                                 {id, _, Q} -> [Q];
                                 {app_t, _, {id, _, Q}, _} -> [Q]
                             end,
                     TagPred = apply_subst(Id, Access(Var), pred_of(Assg, Tag)),
                     ConPred =
                         lists:flatten(
                           [ type_binds_pred(
                               Assg,
                               fun(X) -> {proj, CAnn, Access(Var), X} end,
                               lists:zip(
                                 [?adt_proj_id(CAnn, qid(CAnn, lists:droplast(QName) ++ [name(Con)]), I)
                                  || I <- lists:seq(1, length(Args))],
                                 Args
                              )
                              )
                             || {constr_t, CAnn, Con, Args} <- Constrs
                           ]),
                     TagPred ++ ConPred;
                 {dep_list_t, Ann, Id, ElemT, LenPred} ->
                     [?op(Ann, Access(Var), '>=', ?int(Ann, 0))] ++
                     type_binds_pred(Assg, Access, [ElemT]) ++
                     apply_subst(Id, Access(Var), pred_of(Assg, LenPred));
                 _ -> []
             end
    ].


simplify_assg(Assg) ->
    maps:map(fun(_K, V = #ltinfo{env = KEnv, id = Id, base = BaseType, predicate = Qs}) ->
                     V#ltinfo{
                       predicate =
                           simplify_pred(
                             Assg,
                             bind_var(Id, BaseType, KEnv),
                             Qs
                            )
                      }
             end, Assg).

%% -- Solving ------------------------------------------------------------------

split_constr(L) when is_list(L) ->
    split_constr(L, []).
split_constr([H|T], Acc) ->
    HC = split_constr1(H),
    split_constr(T, HC ++ Acc);
split_constr([], Acc) ->
    filter_obvious(Acc).

split_constr1(C = {subtype, Ref, Ann, Env0, SubT, SupT}) ->
    case {SubT, SupT} of
        { {dep_fun_t, _, ArgsSub, RetSub}
        , {dep_fun_t, _, ArgsSup, RetSup}
        } ->
            Contra =
                [ {subtype, Ref, Ann, Env0, ArgSupT, ArgSubT} %% contravariant!
                 || {{dep_arg_t, _, ArgSubT}, {dep_arg_t, _, ArgSupT}}
                        <- lists:zip(ArgsSub, ArgsSup)
                ],
            Env1 = bind_args(ArgsSup, Env0),
            Subst =
                [{Id1, Id2} || {{dep_arg_t, _, Id1, _}, {dep_arg_t, _, Id2, _}}
                                   <- lists:zip(ArgsSub, ArgsSup)],
            split_constr([{subtype, Ref, Ann, Env1, apply_subst(Subst, RetSub), RetSup}|Contra]);
        {{tuple_t, _, TSubs}, {tuple_t, _, TSups}} ->
            split_constr([{subtype, Ref, Ann, Env0, TSub, TSup} ||
                             {TSub, TSup} <- lists:zip(TSubs, TSups)]);
        { {dep_record_t, _, _, FieldsSub}
        , {dep_record_t, _, _, FieldsSup}
        } ->
            FieldsSub1 = lists:keysort(3, FieldsSub),
            FieldsSup1 = lists:keysort(3, FieldsSup),
            split_constr(
              [ {subtype, Ref, Ann, Env0, FTSub, FTSup}
               || {{field_t, _, _, FTSub}, {field_t, _, _, FTSup}} <- lists:zip(FieldsSub1, FieldsSup1)
              ]
             );
        { {dep_variant_t, _, IdSub, TypeSub, TagSub, ConstrsSub}
        , {dep_variant_t, _, IdSup, TypeSup, TagSup, ConstrsSup}
        } ->
            ConstrsSplit =
                [ {subtype, Ref, Ann, Env0, ArgSub, ArgSup}
                  || { {constr_t, _, _, ArgsSub}
                     , {constr_t, _, _, ArgsSup}
                     } <- lists:zip(ConstrsSub, ConstrsSup),
                     {ArgSub, ArgSup} <- lists:zip(ArgsSub, ArgsSup)
                ],
            split_constr(
              [ {subtype, Ref, Ann, Env0, ?refined(IdSub, TypeSub, TagSub), ?refined(IdSup, TypeSup, TagSup)}
              | ConstrsSplit
              ]
             );
        { {dep_list_t, _, IdSub, DepElemSub, LenQualSub}
        , {dep_list_t, _, IdSup, DepElemSup, LenQualSup}
        } ->
            split_constr(
              [ {subtype, Ref, Ann, Env0,
                 ?refined(IdSub, ?int_t(Ann), LenQualSub),
                 ?refined(IdSup, ?int_t(Ann), LenQualSup)}
              , {subtype, Ref, Ann, Env0, DepElemSub, DepElemSup}
              ]
             );
        { {dep_list_t, _, IdSub, DepElemSub, LenQualSub}
        , {refined_t, _, IdSub, BaseSup = ?int_tp, LenQualSup}
        } ->
            split_constr1(
              {subtype, Ref, Ann, Env0,
               ?refined(IdSub, ?int_t(?ann_of(DepElemSub)), LenQualSub),
               ?refined(IdSub, BaseSup, LenQualSup)}
             );
        { {refined_t, _, IdSub, BaseSub = ?int_tp, LenQualSub}
        , {dep_list_t, _, IdSup, DepElemSup, LenQualSup}
        } ->
            split_constr1(
              {subtype, Ref, Ann, Env0,
               ?refined(IdSub, BaseSub, LenQualSub),
               ?refined(IdSup, ?int_t(?ann_of(DepElemSup)), LenQualSup)}
             );
        _ ->
            [C]
    end;
split_constr1(C = {well_formed, Ref, Env0, T}) ->
    case T of
        {dep_fun_t, _, Args, Ret} ->
            FromArgs =
                [ {well_formed, Ref, Env0, ArgT}
                  || {dep_arg_t, _, _, ArgT} <- Args
                ],
            Env1 = bind_args(Args, Env0),
            split_constr([{well_formed, Ref, Env1, Ret}|FromArgs]);
        {tuple_t, _, Ts} ->
            split_constr([{well_formed, Ref, Env0, Tt} || Tt <- Ts]);
        {dep_record_t, _, _, Fields} ->
            split_constr([{well_formed, Ref, Env0, TF} || {field_t, _, _, TF} <- Fields]);
        {dep_variant_t, _, Id, Type, Tag, Constrs} ->
            ConstrsSplit =
                [ {well_formed, Ref, Env0, Arg}
                  || {constr_t, _, _, Args} <- Constrs,
                     Arg <- Args
                ],
            split_constr(
              [ {well_formed, Ref, Env0, ?refined(Id, Type, Tag)}
              | ConstrsSplit
              ]
             );
        {dep_list_t, Ann, Id, DepElem, LenQual} ->
            split_constr(
              [ {well_formed, Ref, Env0, ?refined(Id, ?int_t(Ann), LenQual)}
              , {well_formed, Ref, Env0, DepElem}
              ]);
        _ ->
            [C]
    end;
split_constr1(C = {reachable, _Ref, _, _}) ->
    [C];
split_constr1(C = {unreachable, _Ref, _, _}) ->
    [C].

filter_obvious(L) ->
    filter_obvious(L, []).
filter_obvious([], Acc) ->
    Acc;
filter_obvious([H|T], Acc) ->
    case H of
        {subtype, _, _, _, _, {refined_t, _, _, _, []}} ->
            filter_obvious(T, Acc);
        {well_formed, _, _, {refined_t, _, _, _, []}} ->
            filter_obvious(T, Acc);
         _ -> filter_obvious(T, [H|Acc])
    end.

-spec solve(env(), aeso_syntax:ast(), [constr()]) -> {ok, assignment()} | {error, term()}.
solve(Env, AST0, CS) ->
    case aeso_smt:scoped(
           fun() ->
                   declare_tuples(find_tuple_sizes(AST0)),
                   declare_datatypes(type_defs(Env)),
                   run_solve(CS)
           end) of
        Assg ->
            case get(refiner_errors) of
                [] ->
                    AST1 = apply_assg(Assg, AST0),
                    AST2 = strip_typed(AST1),
                    {ok, AST2};
                Errs -> {error, {refinement_errors, Errs}}
            end
    end.

-spec run_solve([constr()]) -> assignment().
run_solve(Cs0) ->
    Cs1 = [C || C = {subtype, _, _, _, _, _} <- Cs0],
    Assg0 = run_solve(init_assg(Cs0), Cs1, Cs1),
    check_reachable(Assg0, Cs0),
    simplify_assg(Assg0).
run_solve(Assg, _, []) ->
    Assg;
run_solve(Assg, AllCs, [C|Rest]) ->
    case valid_in(C, Assg) of
        false ->
            Weakened = weaken(C, Assg),
            if Weakened == Assg -> error({weaken_failed, Assg});
               true -> run_solve(Weakened, AllCs, AllCs)
            end;
        true  ->
            run_solve(Assg, AllCs, Rest);
        error ->
            %% Error has been registered.
            run_solve(Assg, AllCs -- [C], Rest)
    end.

valid_in({well_formed, _, _, _}, _) ->
    true;
valid_in({subtype, _Ref, Ann, Env,
          _SB = {refined_t, _, SubId, _, SubP},
          _SP = {refined_t, _, SupId, Base, SupP}
         }, Assg) when is_list(SupP) ->
    SubPred = pred_of(Assg, SubP),
    SupPred = pred_of(Assg, SupP),
    AssumpPred = SubPred,
    ConclPred  = apply_subst(SupId, SubId, SupPred),
    Env1 = ensure_var(SubId, Base, Env),
    case impl_holds(Assg, Env1, AssumpPred, ConclPred) of
        true ->
            true;
        false ->
            %?DBG("~s -> ~s", [name(SupId), name(SubId)]),
            %?DBG("CONTRADICT ON ~p \n~s\n<:\n~s", [_Ref, aeso_pretty:pp(predicate, strip_typed(pred_of(Assg, Env) ++ AssumpPred)), aeso_pretty:pp(predicate, strip_typed(ConclPred))]),
            %?DBG("IN\n~s", [aeso_pretty:pp(predicate, strip_typed(pred_of(Assg, Env1)))]),
            SimpAssump = simplify_pred(Assg, Env1,
                                       pred_of(Assg, Env1) ++ AssumpPred),
            add_error({contradict, {Ann, strip_typed(SimpAssump), strip_typed(ConclPred)}})
    end;
valid_in({subtype, _Ref, _, Env,
          {refined_t, _, SubId, _, SubPredVar},
          {refined_t, _, SupId, _, {template, Subst, Var}}
         }, Assg) ->
    #ltinfo{id = Id, base = Base, predicate = Pred} = assg_of(Assg, Var),
    SubPred = pred_of(Assg, SubPredVar),
    SupPred = apply_subst(Subst, Pred),
    AssumpPred = apply_subst(SubId, Id, SubPred),
    ConclPred  = apply_subst(SupId, Id, SupPred),
    Env1 = bind_var(Id, Base, Env),
    impl_holds(Assg, Env1, AssumpPred, ConclPred);
valid_in({subtype, Ref, Ann, Env, Sub, Sup}, Assg)
  when element(1, Sub) =:= id;
       element(1, Sub) =:= tvar ->
    valid_in({subtype, Ref, Ann, Env, ?refined(Sub), Sup}, Assg);
valid_in(_C = {subtype, _Ref, _, _, _T1, _T2}, _) -> %% In typechecker we trust
    %% ?DBG("SKIP CONSTR ~p\n~s\n<:~s", [_Ref, aeso_pretty:pp(type, _T1), aeso_pretty:pp(type, _T2)]),
    true;
valid_in(_, _) ->
    true.


weaken({subtype, _Ref, _, Env,
        {refined_t, _, SubId,    _, SubPredVar},
        {refined_t, _, SupId, _, {template, Subst, Var}}
       }, Assg) ->
    Ltinfo = #ltinfo{id = Id, base = Base, predicate = Pred} = assg_of(Assg, Var),
    SubPred = pred_of(Assg, SubPredVar),
    AssumpPred = apply_subst(SubId, Id, SubPred),
    Env1 = bind_var(Id, Base, Env),
    Filtered =
        [Q || Q <- Pred,
             impl_holds(Assg, Env1, AssumpPred, apply_subst([{SupId, Id}|Subst], Q))
        ],
    %% ?DBG("WEAKENED (~s <: ~s  --> ~s) ~p\nUNDER\n~s\nFROM\n~s\nTO\n~s", [name(SubId), name(SupId), name(Id), _Ref, aeso_pretty:pp(predicate, AssumpPred), aeso_pretty:pp(predicate, Pred), aeso_pretty:pp(predicate, Filtered)]),
    NewLtinfo = Ltinfo#ltinfo{
                 predicate = Filtered
                },
    Assg#{Var => NewLtinfo};
weaken({well_formed, _, _Env, {refined_t, _, _, _, _}}, Assg) ->
    Assg.

check_reachable(Assg, [{reachable, _, Ann, Env}|Rest]) ->
    case impl_holds(Assg, Env, [], [?bool(Ann, false)]) of
        true ->
            add_error({valid_unreachable, {Ann, Env}});
        false ->
            check_reachable(Assg, Rest)
    end;
check_reachable(Assg, [{unreachable, _, Ann, Env}|Rest]) ->
    case impl_holds(Assg, Env, [], [?bool(Ann, false)]) of
        true -> check_reachable(Assg, Rest);
        false -> add_error({invalid_reachable, {Ann, Env}})
    end;
check_reachable(Assg, [_|Rest]) ->
    check_reachable(Assg, Rest);
check_reachable(_, []) ->
    ok.


%% -- SMT Solving --------------------------------------------------------------

declare_tuples([]) ->
    ok;
declare_tuples([N|Rest]) ->
    Seq = lists:seq(1, N),
    aeso_smt:send_z3_success(
      {app, "declare-datatypes",
       [{list, [{var, "T" ++ integer_to_list(I)}
                || I <- Seq
               ]},
        {list, [{app, "$tuple" ++ integer_to_list(N),
                 [{app, "$mk_tuple" ++ integer_to_list(N),
                   [{app, name(?tuple_proj_id(?ann(), N, I)),
                     [{var, "T" ++ integer_to_list(I)}]}
                    || I <- Seq
                   ]
                  }
                 ]
                }
               ]}
       ]
      }
     ),
    declare_tuples(Rest).

%% TODO fix this disgusting shit
declare_datatypes([]) ->
    ok;
declare_datatypes([{Name, {Args, TDef}}|Rest]) ->
    TName = string:join(qname(Name), "."),
    TypeSubst = [{Arg, fresh_id(?ann(), "t")} || Arg <- Args],
    SMTArgs = [T || {_, T} <- TypeSubst],
    case TDef of
        {alias_t, _} -> ok;
        {record_t, Fields} ->
            aeso_smt:send_z3_success(
              {app, "declare-datatypes",
               [{list, [type_to_smt(A) || A <- SMTArgs]},
                 {list, [{app, TName,
                         [{app, "$mk_" ++ TName,
                           [{app, TName ++ "." ++ name(FName),
                             [type_to_smt(apply_subst(TypeSubst, T))]}
                            || {field_t, _, FName, T} <- Fields
                           ]
                          }
                         ]
                        }
                       ]}
                ]
              }
             );
        {variant_t, Constrs} ->
            aeso_smt:send_z3_success(
              {app, "declare-datatypes",
               [{list, [type_to_smt(A) || A <- SMTArgs]},
                {list, [ {app, TName,
                          [ begin
                                QualCon = lists:droplast(qname(Name)) ++ [name(Con)],
                                ConName = string:join(QualCon, "."),
                                {app, ConName,
                                 [{app, name(?adt_proj_id(?ann(), qid(?ann(), QualCon), I)),
                                   [type_to_smt(apply_subst(TypeSubst, T))]}
                                  || {T, I} <-
                                         lists:zip(
                                           ConArgs,
                                           lists:seq(1, length(ConArgs))
                                          )
                                 ]
                                }
                            end
                            || {constr_t, _, Con, ConArgs} <- Constrs
                         ]
                        }
                       ]}
               ]
              }
             )
    end,
    declare_datatypes(Rest).

declare_type_binds(Assg, Env) ->
    [ begin
          aeso_smt:declare_const(expr_to_smt(Var), type_to_smt(T1))
      end
      || {Var, T} <- type_binds(Assg, Env), element(1, T) =/= dep_fun_t,
         T1 <-
             [aeso_ast_infer_types:unfold_types_in_type(Env#env.tc_env, T, [])],
         is_smt_expr(Var),
         is_smt_type(T1)
    ],
    [ begin
          aeso_smt:assert(expr_to_smt(Q))
      end
      || Q <- pred_of(Assg, Env)
    ].

impl_holds(Env, Assump, Concl) ->
    impl_holds(#{}, Env, Assump, Concl).
impl_holds(Assg, Env, Assump, Concl) when not is_list(Assump) ->
    impl_holds(Assg, Env, [Assump], Concl);
impl_holds(Assg, Env, Assump, Concl) when not is_list(Concl) ->
    impl_holds(Assg, Env, Assump, [Concl]);
impl_holds(_, _, _, []) -> true;
impl_holds(Assg, Env, Assump, Concl) ->
    ConclExpr  = {app, ?ann(), {'&&', ?ann()}, Concl}, %% Improper Sophia expr but who cares
    aeso_smt:scoped(
      fun() ->
              declare_type_binds(Assg, Env),
              [ aeso_smt:assert(expr_to_smt(Expr))
                || Expr <- Assump
              ],
              aeso_smt:assert(expr_to_smt(?op(?ann(), '!', ConclExpr))),
              case aeso_smt:check_sat() of
                  {error, Err} -> throw({smt_error, Err});
                  Res ->
                      not Res
              end
      end).


is_smt_type(Expr) ->
    try type_to_smt(Expr) of
        _ -> true
    catch throw:{not_smt_type, _} ->
            false
    end.

type_to_smt({refined_t, _, _, T, _}) ->
    type_to_smt(T);
type_to_smt(?bool_tp) ->
    {var, "Bool"};
type_to_smt(?int_tp) ->
    {var, "Int"};
type_to_smt({id, _, "char"}) ->
    {var, "Int"};
type_to_smt({id, _, "address"}) ->
    {var, "Int"};
type_to_smt({id, _, "string"}) ->
    {var, "Int"};
type_to_smt({id, _, I}) ->
    {var, I};
type_to_smt({tvar, _, _}) ->
    {var, "Int"}; % lol
type_to_smt({qid, _, QVar}) ->
    {var, string:join(QVar, ".")};
type_to_smt(?tuple_tp(Types)) ->
    N = length(Types),
    {app, "$tuple" ++ integer_to_list(N),
     [type_to_smt(T) || T <- Types]
    };
type_to_smt({dep_record_t, _, T, _}) ->
    type_to_smt(T);
type_to_smt({dep_variant_t, _, _, T, _, _}) ->
    type_to_smt(T);
type_to_smt({dep_list_t, _, _, _, _}) ->
    {var, "Int"};  % Lists are yet lengths
type_to_smt({app_t, _, {id, _, "list"}, _}) ->
    {var, "Int"}; % Lists are yet lengths
type_to_smt({app_t, _, T, Args}) ->
    {var, T1} = type_to_smt(T),
    {app, T1, lists:map(fun type_to_smt/1, Args)};
type_to_smt(T) ->
    ?DBG("NOT SMT TYPE ~p", [T]),
    throw({not_smt_type, T}).

is_smt_expr(Expr) ->
    try expr_to_smt(Expr) of
        _ -> true
    catch throw:{not_smt_expr, _} ->
            false
    end.

expr_to_smt({id, _, Var}) ->
    {var, lists:flatten(string:replace(Var, "#", "$", all))};
expr_to_smt({con, _, Var}) ->
    {var, Var};
expr_to_smt({qid, _, QVar}) ->
    {var, string:join(QVar, ".")};
expr_to_smt({qcon, _, QVar}) ->
    {var, string:join(QVar, ".")};
expr_to_smt({bool, _, true}) ->
    {var, "true"};
expr_to_smt({bool, _, false}) ->
    {var, "false"};
expr_to_smt({int, _, I}) ->
    {int, I};
expr_to_smt({string, _, S}) ->
    %% FIXME this sucks as it doesn't play well with the concatenation
    {int, binary:decode_unsigned(crypto:hash(md5, S))};
expr_to_smt({typed, _, E, _}) ->
    expr_to_smt(E);
expr_to_smt(E = {app, _, F, Args}) ->
    case expr_to_smt(F) of
        {var, Fun} ->
            {app, Fun, [expr_to_smt(Arg) || Arg <- Args]};
        _ -> throw({not_smt_expr, E})
    end;
expr_to_smt({proj, Ann, E, Field}) ->
    expr_to_smt({app, Ann, Field, [E]});
expr_to_smt({is_tag, _, What, QCon, [], Base}) ->
    {app, "=",
     [ {app, "as", [expr_to_smt(What), type_to_smt(Base)]}
     , {var, string:join(qname(QCon), ".")}
     ]
    };
expr_to_smt({is_tag, _, What, QCon, Args, Base}) ->
    MakeArg = fun(I) -> {var, "$arg" ++ integer_to_list(I)}
              end,
    Arity = length(Args),
    {app, "exists",
     [ {list,
        [ {list, [ MakeArg(I), type_to_smt(ArgT)]}
          || {ArgT, I} <- lists:zip(Args, lists:seq(1, Arity))
        ]
       }
     , {app, "=",
        [ {app, "as", [expr_to_smt(What), type_to_smt(Base)]}
        , {app, string:join(qname(QCon), "."),
                        [MakeArg(I) || I <- lists:seq(1, Arity)]
          }
        ]
       }
     ]
    };
expr_to_smt({'&&', _}) -> {var, "&&"};
expr_to_smt({'||', _}) -> {var, "||"};
expr_to_smt({'=<', _}) -> {var, "<="};
expr_to_smt({'>=', _}) -> {var, ">="};
expr_to_smt({'==', _}) -> {var, "="};
expr_to_smt({'!=', _}) -> {var, "distinct"};
expr_to_smt({'<', _})  -> {var, "<"};
expr_to_smt({'>', _})  -> {var, ">"};
expr_to_smt({'+', _})  -> {var, "+"};
expr_to_smt({'-', _})  -> {var, "-"};
expr_to_smt({'*', _})  -> {var, "*"};
expr_to_smt({'/', _})  -> {var, "div"};
expr_to_smt({'!', _})  -> {var, "not"};
expr_to_smt({'^', _})  -> {var, "^"};
expr_to_smt({'mod', _})  -> {var, "mod"};
expr_to_smt(E) ->
    %% ?DBG("NOT SMT EXPR ~p", [E]),
    throw({not_smt_expr, E}).


%% -- Simplification -----------------------------------------------------------

flip_op('>') ->
    '<';
flip_op('<') ->
    '>';
flip_op('>=') ->
    '=<';
flip_op('=<') ->
    '>=';
flip_op('==') ->
    '==';
flip_op('!=') ->
    '!=';
flip_op('+') ->
    '+';
flip_op('*') ->
    '*';
flip_op(_) ->
    no_flip.

sort_preds_by_meaningfulness(Preds0) ->
    Preds1 = %% Move vars to the left side if it makes sense
        [ case {R, flip_op(Op)} of
              {?nu_p, FlipOp} when FlipOp =/= no_flip ->
                  {app, Ann, {FlipOp, OpAnn}, [R, L]};
              {{id, _, _}, FlipOp} when FlipOp =/= no_flip ->
                  {app, Ann, {FlipOp, OpAnn}, [R, L]};
              {{qid, _, _}, FlipOp} when FlipOp =/= no_flip ->
                  {app, Ann, {FlipOp, OpAnn}, [R, L]};
              _ -> Q
          end
         || Q = {app, Ann, {Op, OpAnn}, [L, R]} <- Preds0
        ],
    Preds2 = lists:usort(Preds1),
    OpList =
        lists:zip(lists:reverse(['==', '>', '<', '>=', '=<', '!=']), lists:seq(1, 6)),
    Cmp = fun ({app, _, {OpL, _}, [LL, LR]}, {app, _, {OpR, _}, [RL, RR]}) ->
                  SimplBonus = fun SB(?nu_p)        -> 1000000000000000;
                                   SB({int, _, I})  -> 1000000 * (-abs(I));
                                   SB({bool, _, _}) -> 10000;
                                   SB({id, _, _})   -> 1000;
                                   SB({qid, _, _})  -> 100;
                                   SB({app, _, _, _}) -> -10000000000;
                                   SB({typed, _, E, _}) -> SB(E);
                                   SB(_) -> 0
                               end,
                  ValueL = proplists:get_value(OpL, OpList, 0) + SimplBonus(LL) + SimplBonus(LR),
                  ValueR = proplists:get_value(OpR, OpList, 0) + SimplBonus(RL) + SimplBonus(RR),
                  ValueL =< ValueR;
              (_, _) -> true
          end,
    TagPreds = [P || P <- Preds0, element(1, P) == is_tag],
    lists:sort(Cmp, Preds2) ++ TagPreds.

%% this is absolutely heuristic
%% simplify_pred(_, _, Pred) -> Pred;
simplify_pred(Assg, Env, Pred) ->
    %% ?DBG("*** SIMPLIFY PRED"),
    case impl_holds(Assg, Env, Pred, [{bool, ?ann(), false}]) of
        true -> [{bool, ?ann(), false}];
        false -> simplify_pred(Assg, Env, [], sort_preds_by_meaningfulness(Pred))
    end.
simplify_pred(_Assg, _Env, Prev, []) ->
    Prev;
simplify_pred(Assg, Env, Prev, [Q|Post]) ->
    case impl_holds(Assg, Env, Prev ++ Post, Q) of
        true ->
            simplify_pred(Assg, Env, Prev, Post);
        false ->
            simplify_pred(Assg, Env, [Q|Prev], Post)
    end.


%% -- A-Normalization ----------------------------------------------------------

%% A-Normalization – No compound expr may consist of compound exprs
a_normalize(Expr = {typed, Ann, _, Type}) ->
    {Expr1, Decls} = a_normalize(Expr, []),
    case Decls of
        [] -> Expr1;
        _ -> ?typed({block, Ann, lists:reverse([Expr1|Decls])}, Type)
    end.

a_normalize({typed, _, Expr, Type}, Decls) ->
    a_normalize(Expr, Type, Decls);
a_normalize(Expr = {Op, _}, Decls) when is_atom(Op) ->
    {Expr, Decls};
a_normalize(L, Decls) when is_list(L) ->
    a_normalize_list(L, [], Decls).

a_normalize({app, Ann, Fun, Args}, Type, Decls0) ->
    {Fun1,  Decls1} = a_normalize_to_simpl(Fun, Decls0),
    {Args1, Decls2} = a_normalize_to_simpl(Args, Decls1),
    {?typed({app, Ann, Fun1, Args1}, Type),
     Decls2
    };
a_normalize({'if', Ann, Cond, Then, Else}, Type, Decls0) ->
    {Cond1, Decls1} = a_normalize_to_simpl(Cond, Decls0),
    Then1 = a_normalize(Then),
    Else1 = a_normalize(Else),
    {?typed({'if', Ann, Cond1, Then1, Else1}, Type),
     Decls1
    };
a_normalize({switch, Ann, Expr, Alts}, Type, Decls0) ->
    {Expr1, Decls1} = a_normalize_to_simpl(Expr, Decls0),
    Alts1 =
        [ {'case', CAnn, Pat, a_normalize(CaseExpr)}
          || {'case', CAnn, Pat, CaseExpr} <- Alts
        ],
    {?typed({switch, Ann, Expr1, Alts1}, Type),
     Decls1
    };
a_normalize({lam, Ann, Args, Body}, Type, Decls0) ->
    Body1 = a_normalize(Body),
    {?typed({lam, Ann, Args, Body1}, Type),
     Decls0
    };
a_normalize({tuple, Ann, Elems}, Type, Decls0) ->
    {Elems1, Decls1} = a_normalize_to_simpl_list(Elems, [], Decls0),
    {?typed({tuple, Ann, Elems1}, Type),
     Decls1
    };
a_normalize({record, Ann, FieldVals}, Type, Decls0) ->
    Vals = [Val || {field, _, _, Val} <- FieldVals],
    {Vals1, Decls1} = a_normalize_to_simpl_list(Vals, [], Decls0),
    {?typed({record, Ann,
             [{field, FAnn, Field, Val}
              || {Val, {field, FAnn, Field, _}} <- lists:zip(Vals1, FieldVals)]
            }, Type),
     Decls1
    };
a_normalize({record, Ann, Expr, FieldVals}, Type, Decls0) ->
    {Expr1, Decls1} = a_normalize_to_simpl(Expr, Decls0),
    {FieldVals1, Decls2} =
        lists:foldr(
          fun({field_upd, FAnn, [Field = {proj, ProjAnn, ProjField}],
               Lambda = ?typed_p(_, LambdaT = {fun_t, _, _, _, FieldT})}, {FVs, Decls1_0}) ->
                  ModId = fresh_id(FAnn, "mod_field", LambdaT),
                  Proj = ?typed({proj, ProjAnn, Expr1, ProjField}, FieldT),
                  {[{field, FAnn, [Field], ?typed({app, FAnn, ModId, [Proj]}, FieldT)}|FVs],
                   [ {letval, FAnn, ModId, a_normalize(Lambda)}
                   | Decls1_0
                   ]
                  };
             %% ({field_upd, FAnn, Access, TODO
             %%   Lambda = ?typed_p(_, LambdaT = {fun_t, _, _, _, FieldT})}, {FVs, Decls1_0}) ->
             %%      ModId = fresh_id(Ann, "mod_field", LambdaT),
             %%      Proj =
             %%          lists:foldl(
             %%            fun({proj, ProjAnn, ProjField}, PrevExpr) ->
             %%                    {proj, ProjAnn, PrevExpr, ProjField}
             %%            end,
             %%            Expr1, Access),
             %%      {[{field, FAnn, Access, ?typed({app, FAnn, ModId, Proj}, FieldT)}|FVs],
             %%       [ {letval, FAnn, ModId, a_normalize(Lambda)}
             %%       | Decls1_0
             %%       ]
             %%      };
             (FV, {FVs, Decls1_0}) -> {[FV|FVs], Decls1_0}
          end,
          {[], Decls1}, FieldVals),
    Vals = [Val || {field, _, _, Val} <- FieldVals1],
    {Vals1, Decls3} = a_normalize_to_simpl_list(Vals, [], Decls2),
    {?typed({record, Ann, Expr1,
             [{field, FAnn, Field, Val}
              || {Val, {field, FAnn, Field, _}} <- lists:zip(Vals1, FieldVals1)]
            }, Type),
     Decls3
    };
a_normalize({proj, Ann, Expr, Field}, Type, Decls0) ->
    {Expr1, Decls1} = a_normalize_to_simpl(Expr, Decls0),
    {?typed({proj, Ann, Expr1, Field}, Type),
     Decls1
    };
a_normalize({list, Ann, Elems}, Type, Decls0) ->
    {Elems1, Decls1} = a_normalize_to_simpl_list(Elems, [], Decls0),
    {?typed({list, Ann, Elems1}, Type),
     Decls1
    };
a_normalize({list_comp, Ann, Yield, Gens}, Type, Decls0) ->
    {?typed(
        {list_comp, Ann,
         a_normalize(Yield),
         [case G of
              {comprehension_if, GAnn, Expr} ->
                  {comprehension_if, GAnn, a_normalize(Expr)};
              {letval, GAnn, Pat, Body} ->
                  {letval, GAnn, Pat, a_normalize(Body)};
              {comprehension_bind, Pat, Body} ->
                  {comprehension_bind, Pat, a_normalize(Body)}
          end
          || G <- Gens]
        },
       Type),
     Decls0
    };
a_normalize({block, Ann, Stmts}, Type, Decls0) ->
    Stmts1 = a_normalize_block(Stmts, Type, []),
    {?typed({block, Ann, Stmts1}, Type),
     Decls0
    };
a_normalize(Expr, Type, Decls) ->
    {?typed(Expr, Type),
     Decls
    }.

a_normalize_block([], _Type, Acc) ->
    lists:reverse(Acc);
%% a_normalize_block([{letval, Ann, Pat, Body}|Rest], Type, Acc)  when element(1, Pat) /= id ->
%%     Switch = {switch, Ann, Body, [{'case', Ann, Pat, ?typed({block, Ann, Rest}, Type)}]},
%%     a_normalize_block([?typed(Switch, Type)], Type, Acc);
a_normalize_block([{letval, Ann, Pat, Body}|Rest], Type, Acc0) ->
    {Body1, Acc1} = a_normalize(Body, Acc0),
    a_normalize_block(Rest, Type, [{letval, Ann, Pat, Body1}|Acc1]);
a_normalize_block([{letfun, Ann, Name, Args, RetT, Body}|Rest], Type, Acc) ->
    a_normalize_block(Rest, Type, [{letfun, Ann, Name, Args, RetT, a_normalize(Body)}|Acc]);
a_normalize_block([Expr|Rest], Type, Acc0) ->
    {Expr1, Acc1} = a_normalize(Expr, Acc0),
    a_normalize_block(Rest, Type, [Expr1|Acc1]).

a_normalize_list([], Acc, Decls) ->
    {lists:reverse(Acc), Decls};
a_normalize_list([Expr|Rest], Acc, Decls0) ->
    {Expr1, Decls1} = a_normalize(Expr, Decls0),
    a_normalize_list(Rest, [Expr1|Acc], Decls1).


a_normalize_to_simpl({typed, _, Expr, Type}, Decls) ->
    a_normalize_to_simpl(Expr, Type, Decls);
a_normalize_to_simpl(Expr = {Op, _}, Decls) when is_atom(Op) ->
    {Expr, Decls};
a_normalize_to_simpl(L, Decls) when is_list(L) ->
    a_normalize_to_simpl_list(L, [], Decls).


a_normalize_to_simpl(?typed_p(E, T1), Type, Decls0) ->
    {E1, Decls1} = a_normalize_to_simpl(E, T1, Decls0),
    {?typed(E1, Type), Decls1};
a_normalize_to_simpl(Expr = {id, _, _}, Type, Decls) ->
    {?typed(Expr, Type), Decls};
a_normalize_to_simpl(Expr = {qid, _, _}, Type, Decls) ->
    {?typed(Expr, Type), Decls};
a_normalize_to_simpl(Expr = {con, _, _}, Type, Decls) ->
    {?typed(Expr, Type), Decls};
a_normalize_to_simpl(Expr = {qcon, _, _}, Type, Decls) ->
    {?typed(Expr, Type), Decls};
a_normalize_to_simpl(Expr = {int, _, _}, Type, Decls) ->
    {?typed(Expr, Type), Decls};
a_normalize_to_simpl(Expr = {bool, _, _}, Type, Decls) ->
    {?typed(Expr, Type), Decls};
a_normalize_to_simpl(Expr = {string, _, _}, Type, Decls) ->
    {?typed(Expr, Type), Decls};
a_normalize_to_simpl(Expr = {tuple, _, []}, Type, Decls) ->
    {?typed(Expr, Type), Decls};
a_normalize_to_simpl(Expr = {Op, _}, Type, Decls) when is_atom(Op) ->
    {?typed(Expr, Type), Decls};
a_normalize_to_simpl(Expr, Type, Decls0) ->
    {Expr1, Decls1} = a_normalize(Expr, Type, Decls0),
    Var = fresh_id(?ann_of(Expr), "anorm_" ++ atom_to_list(element(1, Expr)), Type),
    {Var,
     [{letval, ?ann_of(Expr), Var, Expr1}|Decls1]
    }.

a_normalize_to_simpl_list([], Acc, Decls) ->
    {lists:reverse(Acc), Decls};
a_normalize_to_simpl_list([{letval, Ann, Pat, Body}|Rest], Acc, Decls0) ->
    {Body1, Decls1} = a_normalize_to_simpl(Body, Decls0),
    a_normalize_to_simpl_list(Rest, Acc, [{letval, Ann, Pat, Body1}|Decls1]);
a_normalize_to_simpl_list([Expr|Rest], Acc, Decls0) ->
    {Expr1, Decls1} = a_normalize_to_simpl(Expr, Decls0),
    a_normalize_to_simpl_list(Rest, [Expr1|Acc], Decls1).


%% -- State purification ------------------------------------------------------

balance_t(Ann) ->
    ?int_t(Ann).

init_state_var(Ann, Type) ->
    ?typed({id, Ann, "$init_state"}, Type).

init_balance_var(Ann) ->
    ?typed({id, Ann, "$init_balance"}, ?d_nonneg_int(Ann)).

-record (purifier_st,
         { state :: expr()
         , balance :: expr()
         , env :: env()
         }).
-type purifier_st() :: #purifier_st{}.

-spec init_purifier_st(ann(), env()) -> purifier_st().
init_purifier_st(Ann, Env) ->
    #purifier_st{ state = init_state_var(Ann, state_t(Ann, Env))
                , balance = init_balance_var(Ann)
                , env = Env
                }.

get_state_t(#purifier_st{state = ?typed_p(_, StateT)}) ->
    StateT.

wrap_if_pure({Pure, E}, ST) ->
    wrap_if_pure(Pure, E, ST).
wrap_if_pure(pure, E, ST) ->
    wrap_state(E, ST);
wrap_if_pure(impure, E, _) ->
    E.

wrap_if_impure({Pure, E}, ST) ->
    wrap_if_impure(Pure, E, ST).
wrap_if_impure(impure, E, ST) ->
    wrap_state(E, ST);
wrap_if_impure(pure, E, _) ->
    E.

wrap_state(E = ?typed_p(_, T), ST) ->
    ?typed(
       {tuple, ?ann_of(E),
        [E, ST#purifier_st.state, ST#purifier_st.balance]
       }, wrap_state_t(T, ST)).

wrap_state_t(T, ST) ->
    {tuple_t, ?ann_of(T),
     [T, get_state_t(ST), balance_t(?ann_of(T))]
    }.

unwrap_state(Pat, ST) ->
    STVar = fresh_id(?ann_of(Pat), "$state", get_state_t(ST)),
    BLVar = fresh_id(?ann_of(Pat), "$balance", balance_t(?ann_of(Pat))),
    Pat1 = {tuple, ?ann_of(Pat), [Pat, STVar, BLVar]},
    {Pat1, ST#purifier_st{state = STVar, balance = BLVar}}.

pure_plus(pure, pure) ->
    pure;
pure_plus(_, _) ->
    impure.

pure_prod(impure, impure) ->
    impure;
pure_prod(_, _) ->
    pure.

switch_pure(pure) ->
    impure;
switch_pure(impure) ->
    pure.


purify_many(E1, E2, ST) ->
    case {purify_expr(E1, ST), purify_expr(E2, ST)} of
        {{pure, P1}, {pure, P2}} ->
            {pure, {P1, P2}};
        {S1, S2} ->
            {impure, {wrap_if_pure(S1, ST), wrap_if_pure(S2, ST)}}
    end.
purify_many(L, ST) when is_list(L) ->
    L1 = [purify_expr(E, ST)|| E <- L],
    case lists:any(fun({impure, _}) -> true; (_) -> false end, L1) of
        true ->
            {impure, [wrap_if_pure(Pure, E, ST) || {Pure, E} <- L1]};
        false -> {pure, [E || {_, E} <- L1]}
    end.

purify_expr(?typed_p(E, T), ST) ->
    purify_expr(E, T, ST);
purify_expr(Ex, _) ->
    error({untyped, Ex}).

purify_typed(pure, E, T, ST) ->
    {pure, ?typed(E, purify_type(T, ST))};
purify_typed(impure, E, T, ST) ->
    {impure, ?typed(E, wrap_state_t(purify_type(T, ST), ST))}.

purify_expr(?typed_p(E, T), T1, ST) ->
    {Pure, E1} = purify_expr(E, T, ST),
    purify_typed(Pure, E1, T1, ST);

purify_expr(Id = {id, _, _}, {fun_t, TAnn, [], ArgsT, RetT}, ST) ->
    %% This is a lambda so we treat it as stateful
    %% TODO actually not, it may be pure assigned to a var
    %% The env should follow statefulness and purity
    ArgsT1 = [get_state_t(ST), balance_t(TAnn)|ArgsT],
    RetT1 = wrap_state_t(RetT, ST),
    {pure, ?typed(Id, {fun_t, [{stateful, true}|TAnn], [], ArgsT1, RetT1})};
purify_expr(Id = {id, _, _}, T, _ST) ->
    {pure, ?typed(Id, T)};

%% State get
purify_expr({qid, _, [_, "state"]}, T, ST) ->
    ?typed_p(STVar) = ST#purifier_st.state,
    {pure, ?typed(STVar, purify_type(T, ST))};
%% Balance get
purify_expr({qid, Ann, ["Contract", "balance"]}, _, ST) ->
    {pure, ?typed(ST#purifier_st.balance, ?d_nonneg_int(Ann))};
%% Qualified function
purify_expr(Qid = {qid, _, _}, T = {fun_t, _, _, _, RetTUS}, ST) ->
    Stateful = is_stateful(ST#purifier_st.env, Qid),
    {fun_t, AnnT, [], ArgsT, RetTS} = purify_type(T, ST),
    RetT1 = case Stateful of
                true  -> RetTS;
                false -> RetTUS
            end,
    {pure, ?typed(Qid, {fun_t, AnnT, [], ArgsT, RetT1})};

purify_expr(Expr = {Op, _}, T, _ST) when is_atom(Op) ->
    {pure, ?typed(Expr, T)};

%% Operator
purify_expr({app, Ann, Fun = ?typed_p({Op, _}), Args}, T, ST) when is_atom(Op) ->
    {pure, Fun1} = purify_expr(Fun, ST),
    {pure, Args1} = purify_many(Args, ST),
    {pure, ?typed({app, Ann, Fun1, Args1}, T)};
%% Builtin namespace which interacts with the state
purify_expr({app, Ann, ?typed_p(Fun = {qid, _, [NS, FunName]}, FunT), Args}, T, ST)
  when ?IS_STDLIB(NS) andalso ?IS_STDLIB_STATEFUL(NS, FunName) ->
    Args1 = [ ST#purifier_st.state, ST#purifier_st.balance
            | [drop_purity(purify_expr(A, ST)) || A <- Args]],
    {fun_t, FTAnn, [], ArgsT, RetT} = purify_type(FunT, ST),
    FunT1 = {fun_t, FTAnn, [], ArgsT, wrap_state_t(RetT, ST)},
    purify_typed(impure, {app, Ann, ?typed(Fun, FunT1), Args1}, T, ST);
%% Builtin namespace which doesn't interact with the state
purify_expr({app, Ann, Fun = ?typed_p({qid, _, [NS, _]}), Args}, T, ST)
  when ?IS_STDLIB(NS) ->
    Args1 = [drop_purity(purify_expr(A, ST)) || A <- Args],
    {pure, ?typed({app, Ann, Fun, Args1}, T)};
%% Toplevel stateless builtins
purify_expr({app, Ann, Fun = ?typed_p({id, _, FName}), Args}, T, ST)
  when FName == "require" orelse FName == "abort" ->
    Args1 = [drop_purity(purify_expr(A, ST)) || A <- Args],
    {pure, ?typed({app, Ann, Fun, Args1}, T)};
%% Put
purify_expr({app, _, ?typed_p({qid, QAnn, [_, "put"]}), [State]}, T, ST) ->
    {pure, ?typed_p(State1)} = purify_expr(State, ST),
    {impure, wrap_state(
               ?typed({tuple, QAnn, []}, purify_type(T, ST)),
               ST#purifier_st{state = ?typed(State1, get_state_t(ST))})};
%% Constructor
purify_expr({app, Ann, Fun = ?typed_p({HEAD, _, _}), Args}, T, ST) when HEAD == qcon; HEAD == con ->
    Args1 = [drop_purity(purify_expr(A, ST)) || A <- Args],
    {pure, ?typed({app, Ann, Fun, Args1}, T)};
%% Casual function call
purify_expr({app, Ann, Fun, Args}, RetT, ST) ->
    {pure, Fun1 = ?typed_p(_, {fun_t, FAnn, _, _, _})} = purify_expr(Fun, ST),
    Pure =
        case aeso_syntax:get_ann(stateful, FAnn, false) orelse
            case Fun of
                ?typed_p(FId = {HEAD, _, _}) when HEAD == qid ->
                    is_stateful(ST#purifier_st.env, FId);
                _ -> false
            end
        of
            false -> pure;
            true  -> impure
        end,
    RetT1 =
        case Pure of
            pure   -> RetT;
            impure -> wrap_state_t(RetT, ST)
        end,
    Args1 = [ ST#purifier_st.state, ST#purifier_st.balance
            | [drop_purity(purify_expr(A, ST)) || A <- Args]],
    {Pure, ?typed({app, Ann, Fun1, Args1}, RetT1)};

purify_expr({'if', Ann, Cond, Then, Else}, T, ST) ->
    {pure, Cond1} = purify_expr(Cond, ST),
    {Pure, {Then1, Else1}} = purify_many(Then, Else, ST),
    purify_typed(Pure, {'if', Ann, Cond1, Then1, Else1}, T, ST);
purify_expr({switch, Ann, Switch, Cases}, T, ST) ->
    {pure, Switch1} = purify_expr(Switch, ST),
    Bodies = [Body || {'case', _, _, Body} <- Cases],
    {Pure, Bodies1} = purify_many(Bodies, ST),
    purify_typed(
      Pure,
      {switch, Ann, Switch1,
       [{'case', CAnn, Pat, Body}
        || {Body, {'case', CAnn, Pat, _}} <- lists:zip(Bodies1, Cases)]},
      T, ST);
purify_expr({lam, Ann, Args, Body}, {fun_t, TAnn, [], TArgs, _}, ST) ->
    StateVarT = ?typed_p(StateVar, StateT) = fresh_id(Ann, "$lam_state", get_state_t(ST)),
    BalanceVarT = ?typed_p(BalanceVar, BalanceT) = fresh_id(Ann, "$lam_balance", balance_t(Ann)),
    Args1 = [{arg, Ann, StateVar, StateT}, {arg, Ann, BalanceVar, BalanceT} | Args],
    BodyST = ST#purifier_st{state = StateVarT, balance = BalanceVarT},
    {BodyPure, ?typed_p(_, BodyT) = Body1} =
        purify_expr(Body, BodyST),
    Body2 = wrap_if_pure(BodyPure, Body1, BodyST),
    purify_typed(
      pure, {lam, Ann, Args1, Body2},
      {fun_t, [{stateful, true}|TAnn], [], [get_state_t(ST), balance_t(Ann)|TArgs], BodyT},
      ST
     );
purify_expr({block, Ann, Stmts}, T, ST) ->
    {Pure, Stmts1} = purify_block(pure, Stmts, ST),
    purify_typed(Pure, {block, Ann, Stmts1}, T, ST);
purify_expr({list_comp, Ann, Yield, Gens}, T, ST) ->
    {Pure, Yield1} = purify_expr(Yield, ST),
    %% TODO  not actually, but nobody sane would abuse it
    purify_typed(
      Pure,
      {list_comp, Ann, Yield1,
       [case G of
            {comprehension_if, GAnn, Expr} ->
                {comprehension_if, GAnn, drop_purity(purify_expr(Expr, ST))};
            {letval, GAnn, Pat, Body} ->
                {letval, GAnn, Pat, drop_purity(purify_expr(Body, ST))};
            {comprehension_bind, Pat, Body} ->
                {comprehension_bind, Pat, drop_purity(purify_expr(Body, ST))}
        end
        || G <- Gens]
      },
      T, ST);
purify_expr({record, Ann, Fields}, T, ST) ->
    Fields1 =
        [ {field, FAnn, Proj, drop_purity(purify_expr(Val, ST))}
         || {field, FAnn, Proj, Val} <- Fields
        ],
    {pure, ?typed({record, Ann, Fields1}, T)};
purify_expr({proj, Ann, Expr, Field}, T, ST) ->
    {pure, ?typed({proj, Ann, drop_purity(purify_expr(Expr, ST)), Field}, T)};
purify_expr({tuple, Ann, Vals}, T, ST) ->
    Vals1 = [drop_purity(purify_expr(Val, ST)) || Val <- Vals],
    {pure, ?typed({tuple, Ann, Vals1}, T)};
purify_expr({list, Ann, Vals}, T, ST) ->
    Vals1 = [drop_purity(purify_expr(Val, ST)) || Val <- Vals],
    {pure, ?typed({list, Ann, Vals1}, T)};
purify_expr(E, T, ST) ->
    purify_typed(pure, E, T, ST).

purify_block(PurePrev, [Expr], ST) ->
    {PureExpr, Expr1} = purify_expr(Expr, ST),
    Pure = pure_plus(PurePrev, PureExpr),
    PureToWrap = pure_prod(switch_pure(PureExpr), PurePrev),
    {Pure, [wrap_if_impure(PureToWrap, Expr1, ST)]};
purify_block(PurePrev, [{letval, Ann, Pat, Expr}|Rest], ST) ->
    {PureExpr, Expr1} = purify_expr(Expr, ST),
    PureNext = pure_plus(PurePrev, PureExpr),
    case PureExpr of
        pure ->
            {Pure, Rest1} = purify_block(PureNext, Rest, ST),
            {Pure, [{letval, Ann, Pat, Expr1}|Rest1]};
        impure ->
            {Pat1, ST1} = unwrap_state(Pat, ST),
            {_, Rest1} = purify_block(PureNext, Rest, ST1),
            {impure,
             [ {letval, Ann, Pat1, Expr1}
             | Rest1
             ]}
    end;
purify_block(PurePrev, [Stmt|Rest], ST) ->
    {PureStmt, Stmt1} = purify_expr(Stmt, ST),
    PureNext = pure_plus(PurePrev, PureStmt),
    case PureStmt of
        pure ->
            {Pure, Rest1} = purify_block(PureNext, Rest, ST),
            {Pure, [Stmt1|Rest1]};
        impure ->
            {Pat, ST1} = unwrap_state({id, ?ann_of(Stmt), "_"}, ST),
            {_, Rest1} = purify_block(PureNext, Rest, ST1),
            {impure,
            [ {letval, ?ann_of(Stmt), Pat, Stmt1}
            | Rest1
            ]}
    end.

purify_type({fun_t, Ann, [], Args, Ret}, ST) ->
    {fun_t, Ann, [],
     [get_state_t(ST), balance_t(Ann) | [purify_type(Arg, ST) || Arg <- Args]],
     wrap_state_t(purify_type(Ret, ST), ST)};
purify_type({app_t, Ann, T, Args}, ST) ->
    {app_t, Ann, T, [purify_type(Arg, ST) || Arg <- Args]};
purify_type({tuple_t, Ann, Args}, ST) ->
    {tuple_t, Ann, [purify_type(Arg, ST) || Arg <- Args]};
purify_type({dep_fun_t, Ann, Args, Ret}, ST) ->
    Env = ST#purifier_st.env,
    BalanceId = fresh_id(Ann, "$balance"),
    StateId = fresh_id(Ann, "$state", {qid, Ann, Env#env.namespace ++ ["state"]}),
    {dep_fun_t, Ann,
     [ element(1, fresh_liquid_arg(Env, StateId))
     , {dep_arg_t, Ann, BalanceId, ?refined(BalanceId, ?int_t(Ann), [?op(Ann, BalanceId, '>=', ?int(Ann, 0))])}
     | [{dep_arg_t, ArgAnn, Id, purify_type(Arg, ST)} || {dep_arg_t, ArgAnn, Id, Arg} <- Args]],
     wrap_state_t(purify_type(Ret, ST), ST)};
purify_type({dep_list_t, Ann, Id, ElemT, Qual}, ST) ->
    {dep_list_t, Ann, Id, purify_type(ElemT, ST), Qual};
purify_type({dep_record_t, Ann, Base, Fields}, ST) ->
    {dep_record_t, Ann, Base,
     [{field_t, FAnn, Id, purify_type(FType, ST)} || {field_t, FAnn, Id, FType} <- Fields]};
purify_type({dep_variant_t, Ann, Id, Base, Constrs}, ST) ->
    {dep_variant_t, Ann, Id, Base,
     [{constr_t, FAnn, Con, [purify_type(Arg, ST) || Arg <- Args]}
     || {constr_t, FAnn, Con, Args} <- Constrs]};
purify_type(T, _) -> T.


drop_purity({impure, E}) ->
    E;
drop_purity({pure, E}) ->
    E.

purify_expr_to_pure(Expr, ST) ->
    Ann = ?ann_of(Expr),
    case purify_expr(Expr, ST) of
        {pure, B} -> B;
        {impure, BTyped = ?typed_p(_, BST = {tuple_t, _, [BType, SType, BalType]})} ->
            ?typed(
               {switch, Ann, BTyped,
                [ {'case', Ann,
                   ?typed(
                      {tuple, Ann, [ ?typed({id, Ann, "$pure"}, BType)
                                   , ?typed({id, Ann, "_"}, SType)
                                   , ?typed({id, Ann, "_"}, BalType)
                                   ]},
                      BST),
                   ?typed({id, Ann, "$pure"}, BType)
                  }
                ]
               },
               BType
              )
    end.


%% -- Errors -------------------------------------------------------------------

pp_error({contradict, {Ann, Assump, Promise}}) ->
    io_lib:format("Could not prove the promise at ~s ~p:~p\n"
              "~s:\n"
              "  ~s\n"
              "from the assumption\n"
              "  ~s\n",
              [aeso_syntax:get_ann(file, Ann, ""),
               aeso_syntax:get_ann(line, Ann, 0),
               aeso_syntax:get_ann(col, Ann, 0),
               pp_context(aeso_syntax:get_ann(context, Ann, none)),
               aeso_pretty:pp(predicate, Promise),
               aeso_pretty:pp(predicate, Assump)]
             );
pp_error({invalid_reachable, {Ann, Pred}}) ->
    io_lib:format("Could not ensure safety of the control flow at ~s ~p:~p\n"
              "Could not prove that\n"
              "  ~s\n"
              "never holds.",
              [aeso_syntax:get_ann(file, Ann, ""),
               aeso_syntax:get_ann(line, Ann, 0),
               aeso_syntax:get_ann(col, Ann, 0),
               aeso_pretty:pp(predicate, aeso_ast_refine_types:path_pred(Pred))
              ]
             );
pp_error({valid_unreachable, {Ann, Pred}}) ->
    io_lib:format("Found dead code at ~s ~p:~p\n"
              "by proving that\n"
              "  ~s\n"
              "never holds.",
              [aeso_syntax:get_ann(file, Ann, ""),
               aeso_syntax:get_ann(line, Ann, 0),
               aeso_syntax:get_ann(col, Ann, 0),
               aeso_pretty:pp(predicate, aeso_ast_refine_types:path_pred(Pred))
              ]
             );
pp_error({overwrite, Id}) ->
    io_lib:format("Illegal redefinition of the variable ~s at ~s ~p:~p",
                  [aeso_pretty:pp(expr, Id),
                   aeso_syntax:get_ann(file, Id, ""),
                   aeso_syntax:get_ann(line, Id, 0),
                   aeso_syntax:get_ann(col, Id, 0)
                  ]
                 );
pp_error({entrypoint_arg_assump, {Name, Ann, T}}) ->
    io_lib:format("The entrypoint ~s has got assumptions on its argument at ~s ~p:~p.\n"
              "These assumptions won't be checked after the contract is deployed.\n"
              "Please provide ~s an external type declaration and validate the data using\n"
              "  `require : (bool, string) => unit` function.\n"
              "The illegal type was\n"
              "  ~s",
              [Name,
               aeso_syntax:get_ann(file, Ann, ""),
               aeso_syntax:get_ann(line, Ann, 0),
               aeso_syntax:get_ann(col, Ann, 0),
               Name,
               aeso_pretty:pp(type, T)
              ]
             );
pp_error({smt_error, ErrStr}) -> ErrStr;
pp_error({refinement_errors, Errs}) ->
    string:join([pp_error(E) || E <- Errs], "\n\n");
pp_error(ErrBin) ->
    io_lib:format("\nerror: ~s", [ErrBin]),
    error(ErrBin).


pp_context(none) ->
    "";
pp_context({app, Ann, Fun, N}) ->
    io_lib:format(
      "arising from an application of ~p to its ~s argument",
      [ aeso_pretty:pp(expr, strip_typed(Fun))
      , case aeso_syntax:get_ann(format, Ann, prefix) of
            prefix -> case abs(N rem 10) of
                          1 -> integer_to_list(N) ++ "st";
                          2 -> integer_to_list(N) ++ "nd";
                          3 -> integer_to_list(N) ++ "rd";
                          _ -> integer_to_list(N) ++ "th"
                      end;
            infix -> case N of
                         1 -> "left";
                         2 -> "right"
                     end
        end
      ]);
pp_context(then) ->
    "arising from the assumption of the `if` condition";
pp_context(else) ->
    "arising from the negation of the `if` condition";
pp_context({switch, N}) ->
    io_lib:format(
      "arising from the assumption of triggering the ~s branch of `switch`",
      [case abs(N rem 10) of
          1 -> integer_to_list(N) ++ "st";
          2 -> integer_to_list(N) ++ "nd";
          3 -> integer_to_list(N) ++ "rd";
          _ -> integer_to_list(N) ++ "th"
      end
      ]
     ).
