-module(aeso_ast_types_env).

%% Unifiable type. Similar to type, but includes `uvar`.
-type utype() :: {fun_t, aeso_syntax:ann(), named_args_t(), [utype()] | var_args, utype()}
               | {app_t, aeso_syntax:ann(), utype(), [utype()]}
               | {tuple_t, aeso_syntax:ann(), [utype()]}
               | aeso_syntax:id()  | aeso_syntax:qid()
               | aeso_syntax:con() | aeso_syntax:qcon()  %% contracts
               | aeso_syntax:tvar()
               | {if_t, aeso_syntax:ann(), aeso_syntax:id(), utype(), utype()}  %% Can branch on named argument (protected)
               | uvar().

%% Unifiable "wobbly" type variable
-type uvar() :: {uvar, aeso_syntax:ann(), reference()}.

-type named_args_t() :: uvar() | #{aeso_syntax:name() => {ann(), utype(), aeso_syntax:expr()}}.

-type type_id() :: aeso_syntax:id() | aeso_syntax:qid() | aeso_syntax:con() | aeso_syntax:qcon().

-define(is_type_id(T), element(1, T) =:= id orelse
                       element(1, T) =:= qid orelse
                       element(1, T) =:= con orelse
                       element(1, T) =:= qcon).

-type why_record() :: aeso_syntax:field(aeso_syntax:expr())
                    | {var_args, aeso_syntax:ann(), aeso_syntax:expr()}
                    | {proj, aeso_syntax:ann(), aeso_syntax:expr(), aeso_syntax:id()}.

-type pos() :: aeso_errors:pos().

-record(named_argument_constraint,
    {args :: named_args_t(),
     name :: aeso_syntax:id(),
     type :: utype()}).

-record(dependent_type_constraint,
    { named_args_t     :: named_args_t()
    , named_args       :: [aeso_syntax:arg_expr()]
    , general_type     :: utype()
    , specialized_type :: utype()
    , context          :: term() }).

-type named_argument_constraint() :: #named_argument_constraint{} | #dependent_type_constraint{}.

-record(field_constraint,
    { record_t :: utype()
    , field    :: aeso_syntax:id()
    , field_t  :: utype()
    , kind     :: project | create | update %% Projection constraints can match contract
    , context  :: why_record() }).          %% types, but field constraints only record types.

%% Constraint checking that 'record_t' has precisely 'fields'.
-record(record_create_constraint,
    { record_t :: utype()
    , fields   :: [aeso_syntax:id()]
    , context  :: why_record() }).

-record(is_contract_constraint,
    { contract_t :: utype(),
      context    :: {contract_literal, aeso_syntax:expr()} |
                    {address_to_contract, aeso_syntax:ann()} |
                    {bytecode_hash, aeso_syntax:ann()} |
                    {var_args, aeso_syntax:ann(), aeso_syntax:expr()},
      force_def = false :: boolean()
    }).

-type field_constraint() :: #field_constraint{} | #record_create_constraint{} | #is_contract_constraint{}.

-type byte_constraint() :: {is_bytes, utype()}
                         | {add_bytes, aeso_syntax:ann(), concat | split, utype(), utype(), utype()}.

-type aens_resolve_constraint() :: {aens_resolve_type, utype()}.
-type oracle_type_constraint() :: {oracle_type, aeso_syntax:ann(), utype()}.

-type constraint() :: named_argument_constraint() | field_constraint() | byte_constraint()
                    | aens_resolve_constraint() | oracle_type_constraint().

-record(field_info,
    { ann      :: aeso_syntax:ann()
    , field_t  :: utype()
    , record_t :: utype()
    , kind     :: contract | record }).

-type field_info() :: #field_info{}.

-type access() :: public | private | internal.

-type typedef() :: {[aeso_syntax:tvar()], aeso_syntax:typedef() | {contract_t, [aeso_syntax:field_t()]}}
                 | {builtin, non_neg_integer()}.

-type type() :: aeso_syntax:type().
-type name() :: string().
-type qname() :: [string()].
-type typesig() :: {type_sig, aeso_syntax:ann(), type_constraints(), [aeso_syntax:named_arg_t()], [type()], type()}.

-type namespace_alias() :: none | name().
-type namespace_parts() :: none | {for, [name()]} | {hiding, [name()]}.
-type used_namespaces() :: [{qname(), namespace_alias(), namespace_parts()}].

-type type_constraints() :: none | bytes_concat | bytes_split | address_to_contract | bytecode_hash.

-type variance() :: invariant | covariant | contravariant | bivariant.

-type fun_info()  :: {aeso_syntax:ann(), typesig() | type()}.
-type type_info() :: {aeso_syntax:ann(), typedef()}.
-type var_info()  :: {aeso_syntax:ann(), utype()}.

-type fun_env()  :: [{name(), fun_info()}].
-type type_env() :: [{name(), type_info()}].

-record(scope, { funs   = [] :: fun_env()
               , types  = [] :: type_env()
               , access = public :: access()
               , kind   = namespace :: namespace | contract
               , ann    = [{origin, system}] :: aeso_syntax:ann()
               }).

-type scope() :: #scope{}.

-record(env,
    { scopes           = #{ [] => #scope{}} :: #{ qname() => scope() }
    , vars             = []                 :: [{name(), var_info()}]
    , typevars         = unrestricted       :: unrestricted | [name()]
    , fields           = #{}                :: #{ name() => [field_info()] }    %% fields are global
    , contract_parents = #{}                :: #{ name() => [name()] }
    , namespace        = []                 :: qname()
    , used_namespaces  = []                 :: used_namespaces()
    , in_pattern       = false              :: boolean()
    , in_guard         = false              :: boolean()
    , stateful         = false              :: boolean()
    , unify_throws     = true               :: boolean()
    , current_function = none               :: none | aeso_syntax:id()
    , what             = top                :: top | namespace | contract | contract_interface
    }).

-type env() :: #env{}.


%% -- Environment manipulation -----------------------------------------------

-spec switch_scope(qname(), env()) -> env().
switch_scope(Scope, Env) ->
    Env#env{namespace = Scope}.

-spec push_scope(namespace | contract, aeso_syntax:con(), env()) -> env().
push_scope(Kind, Con, Env) ->
    Ann  = aeso_syntax:get_ann(Con),
    Name = name(Con),
    New  = Env#env.namespace ++ [Name],
    Env#env{ namespace = New, scopes = (Env#env.scopes)#{ New => #scope{ kind = Kind, ann = Ann } } }.

-spec pop_scope(env()) -> env().
pop_scope(Env) ->
    Env#env{ namespace = lists:droplast(Env#env.namespace) }.

-spec get_scope(env(), qname()) -> false | scope().
get_scope(#env{ scopes = Scopes }, Name) ->
    maps:get(Name, Scopes, false).

-spec on_current_scope(env(), fun((scope()) -> scope())) -> env().
on_current_scope(Env = #env{ namespace = NS, scopes = Scopes }, Fun) ->
    Scope = maps:get(NS, Scopes),
    Env#env{ scopes = Scopes#{ NS => Fun(Scope) } }.

-spec on_scopes(env(), fun((scope()) -> scope())) -> env().
on_scopes(Env = #env{ scopes = Scopes }, Fun) ->
    Env#env{ scopes = maps:map(fun(_, Scope) -> Fun(Scope) end, Scopes) }.

-spec bind_var(aeso_syntax:id(), utype(), env()) -> env().
bind_var({id, Ann, X}, T, Env = #env{ vars = Vars }) ->
    when_warning(warn_shadowing, fun() -> warn_potential_shadowing(Ann, X, Vars) end),
    Env#env{ vars = [{X, {Ann, T}} | Env#env.vars] }.

-spec bind_vars([{aeso_syntax:id(), utype()}], env()) -> env().
bind_vars([], Env) -> Env;
bind_vars([{X, T} | Vars], Env) ->
    bind_vars(Vars, bind_var(X, T, Env)).

-spec bind_tvars([aeso_syntax:tvar()], env()) -> env().
bind_tvars(Xs, Env) ->
    Env#env{ typevars = [X || {tvar, _, X} <- Xs] }.

-spec check_tvar(env(), aeso_syntax:tvar()) -> aeso_syntax:tvar() | no_return().
check_tvar(#env{ typevars = TVars}, T = {tvar, _, X}) ->
    case TVars == unrestricted orelse lists:member(X, TVars) of
        true  -> ok;
        false -> type_error({unbound_type, T})
    end,
    T.

-spec bind_fun(name(), type() | typesig(), env()) -> env().
bind_fun(X, Type, Env) ->
    case lookup_env(Env, term, [], [X]) of
        false -> force_bind_fun(X, Type, Env);
        {_QId, {Ann1, _}} ->
            type_error({duplicate_definition, X, [Ann1, aeso_syntax:get_ann(Type)]}),
            Env
    end.

-spec force_bind_fun(name(), type() | typesig(), env()) -> env().
force_bind_fun(X, Type, Env = #env{ what = What }) ->
    Ann    = aeso_syntax:get_ann(Type),
    NoCode = get_option(no_code, false),
    Entry = if X == "init", What == contract, not NoCode ->
                    {reserved_init, Ann, Type};
               What == contract; What == contract_interface -> {contract_fun, Ann, Type};
               true -> {Ann, Type}
            end,
    on_current_scope(Env, fun(Scope = #scope{ funs = Funs }) ->
                            Scope#scope{ funs = [{X, Entry} | Funs] }
                          end).

-spec bind_funs([{name(), type() | typesig()}], env()) -> env().
bind_funs([], Env) -> Env;
bind_funs([{Id, Type} | Rest], Env) ->
    bind_funs(Rest, bind_fun(Id, Type, Env)).

-spec bind_type(name(), aeso_syntax:ann(), typedef(), env()) -> env().
bind_type(X, Ann, Def, Env) ->
    on_current_scope(Env, fun(Scope = #scope{ types = Types }) ->
                            Scope#scope{ types = [{X, {Ann, Def}} | Types] }
                          end).

%% Bind state primitives
-spec bind_state(env()) -> env().
bind_state(Env) ->
    Ann   = [{origin, system}],
    Unit  = {tuple_t, Ann, []},
    State =
        case lookup_type(Env, {id, Ann, "state"}) of
            {S, _} -> {qid, Ann, S};
            false  -> Unit
        end,
    Env1 = bind_funs([{"state", State},
                      {"put", {type_sig, [stateful | Ann], none, [], [State], Unit}}], Env),

    case lookup_type(Env, {id, Ann, "event"}) of
        {E, _} ->
            %% We bind Chain.event in a local 'Chain' namespace.
            Event = {qid, Ann, E},
            pop_scope(
              bind_fun("event", {fun_t, Ann, [], [Event], Unit},
              push_scope(namespace, {con, Ann, "Chain"}, Env1)));
        false  -> Env1
    end.

-spec bind_field_append(name(), field_info(), env()) -> env().
bind_field_append(X, Info, Env = #env{ fields = Fields }) ->
    Fields1 = maps:update_with(X, fun(Infos) -> [Info | Infos] end, [Info], Fields),
    Env#env{ fields = Fields1 }.

-spec bind_field_update(name(), field_info(), env()) -> env().
bind_field_update(X, Info, Env = #env{ fields = Fields }) ->
    Fields1 = maps:update_with(X, fun([_ | Infos]) -> [Info | Infos]; ([]) -> [Info] end, [Info], Fields),
    Env#env{ fields = Fields1 }.

-spec bind_fields([{name(), field_info()}], typed | untyped, env()) -> env().
bind_fields([], _Typing, Env) -> Env;
bind_fields([{Id, Info} | Rest], Typing, Env) ->
    NewEnv = case Typing of
                 untyped -> bind_field_append(Id, Info, Env);
                 typed   -> bind_field_update(Id, Info, Env)
             end,
    bind_fields(Rest, Typing, NewEnv).

-spec bind_contract(typed | untyped, aeso_syntax:decl(), env()) -> env().
bind_contract(Typing, {Contract, Ann, Id, _Impls, Contents}, Env)
  when ?IS_CONTRACT_HEAD(Contract) ->
    Key         = name(Id),
    Sys         = [{origin, system}],
    TypeOrFresh = fun({typed, _, _, Type}) -> Type; (_) -> fresh_uvar(Sys) end,
    Fields      =
        [ {field_t, AnnF, Entrypoint, contract_call_type(Type)}
          || {fun_decl, AnnF, Entrypoint, Type = {fun_t, _, _, _, _}} <- Contents ] ++
        [ {field_t, AnnF, Entrypoint,
           contract_call_type(
             {fun_t, AnnF, [], [TypeOrFresh(Arg) || Arg <- Args], TypeOrFresh(Ret)})
          }
          || {letfun, AnnF, Entrypoint = {id, _, Name}, Args, _Type, [{guarded, _, [], Ret}]} <- Contents,
             Name =/= "init"
        ] ++
        %% Predefined fields
        [ {field_t, Sys, {id, Sys, "address"}, {id, Sys, "address"}} ] ++
        [ {field_t, Sys, {id, Sys, ?CONSTRUCTOR_MOCK_NAME},
           contract_call_type(
             case [ [TypeOrFresh(Arg) || Arg <- Args]
                    || {letfun, AnnF, {id, _, "init"}, Args, _, _} <- Contents,
                       aeso_syntax:get_ann(entrypoint, AnnF, false)]
                 ++ [ Args
                      || {fun_decl, AnnF, {id, _, "init"}, {fun_t, _, _, Args, _}} <- Contents,
                         aeso_syntax:get_ann(entrypoint, AnnF, false)]
                 ++ [ Args
                      || {fun_decl, AnnF, {id, _, "init"}, {type_sig, _, _, _, Args, _}} <- Contents,
                         aeso_syntax:get_ann(entrypoint, AnnF, false)]
             of
                 [] -> {fun_t, [stateful,payable|Sys], [], [], {id, Sys, "void"}};
                 [Args] -> {fun_t, [stateful,payable|Sys], [], Args, {id, Sys, "void"}}
             end
            )
          }
        ],
    FieldInfo = [ {Entrypoint, #field_info{ ann      = FieldAnn,
                                            kind     = contract,
                                            field_t  = Type,
                                            record_t = Id }}
                || {field_t, _, {id, FieldAnn, Entrypoint}, Type} <- Fields ],
    bind_type(Key, Ann, {[], {contract_t, Fields}},
        bind_fields(FieldInfo, Typing, Env)).

%% What scopes could a given name come from?
-spec possible_scopes(env(), qname()) -> [qname()].
possible_scopes(#env{ namespace = Current, used_namespaces = UsedNamespaces }, Name) ->
    Qual = lists:droplast(Name),
    NewQuals = case lists:filter(fun(X) -> element(2, X) == Qual end, UsedNamespaces) of
                   [] ->
                       [Qual];
                   Namespaces ->
                       lists:map(fun(X) -> element(1, X) end, Namespaces)
               end,
    Ret1 = [ lists:sublist(Current, I) ++ Q || I <- lists:seq(0, length(Current)), Q <- NewQuals ],
    Ret2 = [ Namespace ++ Q || {Namespace, none, _} <- UsedNamespaces, Q <- NewQuals ],
    lists:usort(Ret1 ++ Ret2).

-spec visible_in_used_namespaces(used_namespaces(), qname()) -> boolean().
visible_in_used_namespaces(UsedNamespaces, QName) ->
    Qual = lists:droplast(QName),
    Name = lists:last(QName),
    case lists:filter(fun({Ns, _, _}) -> Qual == Ns end, UsedNamespaces) of
        [] ->
            true;
        Namespaces ->
            IsVisible = fun(Namespace) ->
                            case Namespace of
                                {_, _, {for, Names}} ->
                                    lists:member(Name, Names);
                                {_, _, {hiding, Names}} ->
                                    not lists:member(Name, Names);
                                _ ->
                                    true
                            end
                        end,
            lists:any(IsVisible, Namespaces)
    end.

lookup_name(Env, As, Name) ->
    lookup_name(Env, As, Name, []).

lookup_name(Env = #env{ namespace = NS, current_function = CurFn }, As, Id, Options) ->
    case lookup_env(Env, term, As, qname(Id)) of
        false ->
            type_error({unbound_variable, Id}),
            {Id, fresh_uvar(As)};
        {QId, {_, Ty}} ->
            when_warning(warn_unused_variables, fun() -> used_variable(NS, name(CurFn), QId) end),
            when_warning(warn_unused_functions,
                         fun() -> register_function_call(NS ++ qname(CurFn), QId) end),
            Freshen = proplists:get_value(freshen, Options, false),
            check_stateful(Env, Id, Ty),
            Ty1 = case Ty of
                    {type_sig, _, _, _, _, _} -> freshen_type_sig(As, Ty);
                    _ when Freshen            -> freshen_type(As, Ty);
                    _                         -> Ty
                  end,
            {set_qname(QId, Id), Ty1}
    end.

-spec lookup_type(env(), type_id()) -> false | {qname(), type_info()}.
lookup_type(Env, Id) ->
    lookup_env(Env, type, aeso_syntax:get_ann(Id), qname(Id)).

-spec lookup_env(env(), term, aeso_syntax:ann(), qname()) -> false | {qname(), fun_info()};
                (env(), type, aeso_syntax:ann(), qname()) -> false | {qname(), type_info()}.
lookup_env(Env, Kind, Ann, Name) ->
    Var = case Name of
            [X] when Kind == term -> proplists:get_value(X, Env#env.vars, false);
            _                     -> false
          end,
    case Var of
        {Ann1, Type} -> {Name, {Ann1, Type}};
        false ->
            Names = [ Qual ++ [lists:last(Name)] || Qual <- possible_scopes(Env, Name) ],
            case [ Res || QName <- Names, Res <- [lookup_env1(Env, Kind, Ann, QName)], Res /= false] of
                []    -> false;
                [Res = {_, {AnnR, _}}] ->
                    when_warning(warn_unused_includes,
                                 fun() ->
                                         %% If a file is used from a different file, we
                                         %% can then mark it as used
                                         F1 = proplists:get_value(file, Ann, no_file),
                                         F2 = proplists:get_value(file, AnnR, no_file),
                                         if
                                             F1 /= F2 ->
                                                 used_include(AnnR);
                                             true ->
                                                 ok
                                         end
                                 end),
                    Res;
                Many  ->
                    type_error({ambiguous_name, qid(Ann, Name), [{qid, A, Q} || {Q, {A, _}} <- Many]}),
                    false
            end
    end.

-spec lookup_env1(env(), type | term, aeso_syntax:ann(), qname()) -> false | {qname(), fun_info() | type_info()}.
lookup_env1(#env{ namespace = Current, used_namespaces = UsedNamespaces, scopes = Scopes }, Kind, Ann, QName) ->
    Qual = lists:droplast(QName),
    Name = lists:last(QName),
    QNameIsEvent = lists:suffix(["Chain", "event"], QName),
    AllowPrivate = lists:prefix(Qual, Current),
    %% Get the scope
    case maps:get(Qual, Scopes, false) of
        false -> false; %% TODO: return reason for not in scope
        #scope{ funs = Funs, types = Types } ->
            Defs = case Kind of
                     type -> Types;
                     term -> Funs
                   end,
            %% Look up the unqualified name
            case proplists:get_value(Name, Defs, false) of
                false -> false;
                {reserved_init, Ann1, Type} ->
                    type_error({cannot_call_init_function, Ann}),
                    {QName, {Ann1, Type}};  %% Return the type to avoid an extra not-in-scope error
                {contract_fun, Ann1, Type} when AllowPrivate orelse QNameIsEvent ->
                    {QName, {Ann1, Type}};
                {contract_fun, Ann1, Type} ->
                    type_error({contract_treated_as_namespace, Ann, QName}),
                    {QName, {Ann1, Type}};
                {Ann1, _} = E ->
                    %% Check that it's not private (or we can see private funs)
                    case not is_private(Ann1) orelse AllowPrivate of
                        true  ->
                            case visible_in_used_namespaces(UsedNamespaces, QName) of
                                true -> {QName, E};
                                false -> false
                            end;
                        false -> false
                    end
            end
    end.

fun_arity({fun_t, _, _, Args, _}) -> length(Args);
fun_arity(_)                      -> none.

-spec lookup_record_field(env(), name()) -> [field_info()].
lookup_record_field(Env, FieldName) ->
    maps:get(FieldName, Env#env.fields, []).

%% For 'create' or 'update' constraints we don't consider contract types.
-spec lookup_record_field(env(), name(), create | project | update) -> [field_info()].
lookup_record_field(Env, FieldName, Kind) ->
    [ Fld || Fld = #field_info{ kind = K } <- lookup_record_field(Env, FieldName),
             Kind == project orelse K /= contract ].

lookup_record_field_arity(Env, FieldName, Arity, Kind) ->
    Fields = lookup_record_field(Env, FieldName, Kind),
    [ Fld || Fld = #field_info{ field_t = FldType } <- Fields,
             fun_arity(dereference_deep(FldType)) == Arity ].

%% Environment containing language primitives
-spec global_env() -> env().
global_env() ->
    Ann     = [{origin, system}],
    Int     = {id, Ann, "int"},
    Char    = {id, Ann, "char"},
    Bool    = {id, Ann, "bool"},
    String  = {id, Ann, "string"},
    Address = {id, Ann, "address"},
    Hash    = {id, Ann, "hash"},
    Bits    = {id, Ann, "bits"},
    Bytes   = fun(Len) -> {bytes_t, Ann, Len} end,
    Oracle  = fun(Q, R) -> {app_t, Ann, {id, Ann, "oracle"}, [Q, R]} end,
    Query   = fun(Q, R) -> {app_t, Ann, {id, Ann, "oracle_query"}, [Q, R]} end,
    Unit    = {tuple_t, Ann, []},
    List    = fun(T) -> {app_t, Ann, {id, Ann, "list"}, [T]} end,
    Option  = fun(T) -> {app_t, Ann, {id, Ann, "option"}, [T]} end,
    Map     = fun(A, B) -> {app_t, Ann, {id, Ann, "map"}, [A, B]} end,
    Pair    = fun(A, B) -> {tuple_t, Ann, [A, B]} end,
    FunC    = fun(C, Ts, T) -> {type_sig, Ann, C, [], Ts, T} end,
    FunC1   = fun(C, S, T) -> {type_sig, Ann, C, [], [S], T} end,
    Fun     = fun(Ts, T) -> FunC(none, Ts, T) end,
    Fun1    = fun(S, T) -> Fun([S], T) end,
    FunCN   = fun(C, Named, Normal, Ret) -> {type_sig, Ann, C, Named, Normal, Ret} end,
    FunN    = fun(Named, Normal, Ret) -> FunCN(none, Named, Normal, Ret) end,
    %% Lambda    = fun(Ts, T) -> {fun_t, Ann, [], Ts, T} end,
    %% Lambda1   = fun(S, T) -> Lambda([S], T) end,
    StateFun  = fun(Ts, T) -> {type_sig, [stateful|Ann], none, [], Ts, T} end,
    TVar      = fun(X) -> {tvar, Ann, "'" ++ X} end,
    SignId    = {id, Ann, "signature"},
    SignDef   = {bytes, Ann, <<0:64/unit:8>>},
    Signature = {named_arg_t, Ann, SignId, SignId, {typed, Ann, SignDef, SignId}},
    SignFun   = fun(Ts, T) -> {type_sig, [stateful|Ann], none, [Signature], Ts, T} end,
    TTL       = {qid, Ann, ["Chain", "ttl"]},
    Pointee   = {qid, Ann, ["AENS", "pointee"]},
    AENSName  = {qid, Ann, ["AENS", "name"]},
    Fr        = {qid, Ann, ["MCL_BLS12_381", "fr"]},
    Fp        = {qid, Ann, ["MCL_BLS12_381", "fp"]},
    Fp2       = {tuple_t, Ann, [Fp, Fp]},
    G1        = {tuple_t, Ann, [Fp, Fp, Fp]},
    G2        = {tuple_t, Ann, [Fp2, Fp2, Fp2]},
    GT        = {tuple_t, Ann, lists:duplicate(12, Fp)},
    Tx        = {qid, Ann, ["Chain", "tx"]},
    GAMetaTx  = {qid, Ann, ["Chain", "ga_meta_tx"]},
    BaseTx    = {qid, Ann, ["Chain", "base_tx"]},
    PayForTx  = {qid, Ann, ["Chain", "paying_for_tx"]},

    FldT      = fun(Id, T) -> {field_t, Ann, {id, Ann, Id}, T} end,
    TxFlds    = [{"paying_for", Option(PayForTx)}, {"ga_metas", List(GAMetaTx)},
                 {"actor", Address}, {"fee", Int}, {"ttl", Int}, {"tx", BaseTx}],
    TxType    = {record_t, [FldT(N, T) || {N, T} <- TxFlds ]},
    Stateful  = fun(T) -> setelement(2, T, [stateful|element(2, T)]) end,

    Fee       = Int,
    [A, Q, R, K, V] = lists:map(TVar, ["a", "q", "r", "k", "v"]),

    MkDefs = fun(Defs) -> [{X, {Ann, if is_integer(T) -> {builtin, T}; true -> T end}} || {X, T} <- Defs] end,

    TopScope = #scope
        { funs  = MkDefs(
                     %% Option constructors
                    [{"None", Option(A)},
                     {"Some", Fun1(A, Option(A))},
                     %% TTL constructors
                     {"RelativeTTL", Fun1(Int, TTL)},
                     {"FixedTTL",    Fun1(Int, TTL)},
                     %% Abort/exit
                     {"abort", Fun1(String, A)},
                     {"exit", Fun1(String, A)},
                     {"require", Fun([Bool, String], Unit)}])
        , types = MkDefs(
                    [{"int", 0}, {"bool", 0}, {"char", 0}, {"string", 0}, {"address", 0},
                     {"void", 0},
                     {"unit", {[], {alias_t, Unit}}},
                     {"hash", {[], {alias_t, Bytes(32)}}},
                     {"signature", {[], {alias_t, Bytes(64)}}},
                     {"bits", 0},
                     {"option", 1}, {"list", 1}, {"map", 2},
                     {"oracle", 2}, {"oracle_query", 2}
                     ]) },

    ChainScope = #scope
        { funs = MkDefs(
                     %% Spend transaction.
                    [{"spend",        StateFun([Address, Int], Unit)},
                     %% Chain environment
                     {"balance",      Fun1(Address, Int)},
                     {"block_hash",   Fun1(Int, Option(Hash))},
                     {"coinbase",     Address},
                     {"timestamp",    Int},
                     {"block_height", Int},
                     {"difficulty",   Int},
                     {"gas_limit",    Int},
                     {"bytecode_hash",FunC1(bytecode_hash, A, Option(Hash))},
                     {"create",       Stateful(
                                        FunN([ {named_arg_t, Ann, {id, Ann, "value"}, Int, {typed, Ann, {int, Ann, 0}, Int}}
                                             ], var_args, A))},
                     {"clone",        Stateful(
                                        FunN([ {named_arg_t, Ann, {id, Ann, "gas"}, Int,
                                                {typed, Ann,
                                                 {app, Ann,
                                                  {typed, Ann, {qid, Ann, ["Call","gas_left"]},
                                                   typesig_to_fun_t(Fun([], Int))
                                                  },
                                                  []}, Int
                                                }}
                                             , {named_arg_t, Ann, {id, Ann, "value"}, Int, {typed, Ann, {int, Ann, 0}, Int}}
                                             , {named_arg_t, Ann, {id, Ann, "protected"}, Bool, {typed, Ann, {bool, Ann, false}, Bool}}
                                             , {named_arg_t, Ann, {id, Ann, "ref"}, A, undefined}
                                             ], var_args, A))},
                     %% Tx constructors
                     {"GAMetaTx",     Fun([Address, Int], GAMetaTx)},
                     {"PayingForTx",  Fun([Address, Int], PayForTx)},
                     {"SpendTx",      Fun([Address, Int, String], BaseTx)},
                     {"OracleRegisterTx",       BaseTx},
                     {"OracleQueryTx",          BaseTx},
                     {"OracleResponseTx",       BaseTx},
                     {"OracleExtendTx",         BaseTx},
                     {"NamePreclaimTx",         BaseTx},
                     {"NameClaimTx",            Fun([String], BaseTx)},
                     {"NameUpdateTx",           Fun([Hash], BaseTx)},
                     {"NameRevokeTx",           Fun([Hash], BaseTx)},
                     {"NameTransferTx",         Fun([Address, Hash], BaseTx)},
                     {"ChannelCreateTx",        Fun([Address], BaseTx)},
                     {"ChannelDepositTx",       Fun([Address, Int], BaseTx)},
                     {"ChannelWithdrawTx",      Fun([Address, Int], BaseTx)},
                     {"ChannelForceProgressTx", Fun([Address], BaseTx)},
                     {"ChannelCloseMutualTx",   Fun([Address], BaseTx)},
                     {"ChannelCloseSoloTx",     Fun([Address], BaseTx)},
                     {"ChannelSlashTx",         Fun([Address], BaseTx)},
                     {"ChannelSettleTx",        Fun([Address], BaseTx)},
                     {"ChannelSnapshotSoloTx",  Fun([Address], BaseTx)},
                     {"ContractCreateTx",       Fun([Int], BaseTx)},
                     {"ContractCallTx",         Fun([Address, Int], BaseTx)},
                     {"GAAttachTx",             BaseTx}
                    ])
        , types = MkDefs([{"ttl", 0}, {"tx", {[], TxType}},
                          {"base_tx", 0},
                          {"paying_for_tx", 0}, {"ga_meta_tx", 0}]) },

    ContractScope = #scope
        { funs = MkDefs(
                    [{"address", Address},
                     {"creator", Address},
                     {"balance", Int}]) },

    CallScope = #scope
        { funs = MkDefs(
                    [{"origin",    Address},
                     {"caller",    Address},
                     {"value",     Int},
                     {"gas_price", Int},
                     {"fee",       Int},
                     {"gas_left",  Fun([], Int)}])
        },

    OracleScope = #scope
        { funs = MkDefs(
                    [{"register",     SignFun([Address, Fee, TTL], Oracle(Q, R))},
                     {"expiry",       Fun([Oracle(Q, R)], Fee)},
                     {"query_fee",    Fun([Oracle(Q, R)], Fee)},
                     {"query",        StateFun([Oracle(Q, R), Q, Fee, TTL, TTL], Query(Q, R))},
                     {"get_question", Fun([Oracle(Q, R), Query(Q, R)], Q)},
                     {"respond",      SignFun([Oracle(Q, R), Query(Q, R), R], Unit)},
                     {"extend",       SignFun([Oracle(Q, R), TTL], Unit)},
                     {"get_answer",   Fun([Oracle(Q, R), Query(Q, R)], option_t(Ann, R))},
                     {"check",        Fun([Oracle(Q, R)], Bool)},
                     {"check_query",  Fun([Oracle(Q,R), Query(Q, R)], Bool)}]) },

    AENSScope = #scope
        { funs = MkDefs(
                     [{"resolve",  Fun([String, String], option_t(Ann, A))},
                      {"preclaim", SignFun([Address, Hash], Unit)},
                      {"claim",    SignFun([Address, String, Int, Int], Unit)},
                      {"transfer", SignFun([Address, Address, String], Unit)},
                      {"revoke",   SignFun([Address, String], Unit)},
                      {"update",   SignFun([Address, String, Option(TTL), Option(Int), Option(Map(String, Pointee))], Unit)},
                      {"lookup",   Fun([String], option_t(Ann, AENSName))},
                      %% AENS pointee constructors
                      {"AccountPt",  Fun1(Address, Pointee)},
                      {"OraclePt",   Fun1(Address, Pointee)},
                      {"ContractPt", Fun1(Address, Pointee)},
                      {"ChannelPt",  Fun1(Address, Pointee)},
                      %% Name object constructor
                      {"Name",   Fun([Address, TTL, Map(String, Pointee)], AENSName)}
                     ])
        , types = MkDefs([{"pointee", 0}, {"name", 0}]) },

    MapScope = #scope
        { funs = MkDefs(
                     [{"from_list",      Fun1(List(Pair(K, V)), Map(K, V))},
                      {"to_list",        Fun1(Map(K, V), List(Pair(K, V)))},
                      {"lookup",         Fun([K, Map(K, V)], Option(V))},
                      {"lookup_default", Fun([K, Map(K, V), V], V)},
                      {"delete",         Fun([K, Map(K, V)], Map(K, V))},
                      {"member",         Fun([K, Map(K, V)], Bool)},
                      {"size",           Fun1(Map(K, V), Int)}]) },

    %% Crypto/Curve operations
    CryptoScope = #scope
        { funs = MkDefs(
                     [{"verify_sig",           Fun([Hash, Address, SignId], Bool)},
                      {"verify_sig_secp256k1", Fun([Hash, Bytes(64), SignId], Bool)},
                      {"ecverify_secp256k1",   Fun([Hash, Bytes(20), Bytes(65)], Bool)},
                      {"ecrecover_secp256k1",  Fun([Hash, Bytes(65)], Option(Bytes(20)))},
                      {"sha3",     Fun1(A, Hash)},
                      {"sha256",   Fun1(A, Hash)},
                      {"blake2b",  Fun1(A, Hash)}]) },

    %% Fancy BLS12-381 crypto operations
    MCL_BLS12_381_Scope = #scope
        { funs = MkDefs(
                     [{"g1_neg",     Fun1(G1, G1)},
                      {"g1_norm",    Fun1(G1, G1)},
                      {"g1_valid",   Fun1(G1, Bool)},
                      {"g1_is_zero", Fun1(G1, Bool)},
                      {"g1_add",     Fun ([G1, G1], G1)},
                      {"g1_mul",     Fun ([Fr, G1], G1)},

                      {"g2_neg",     Fun1(G2, G2)},
                      {"g2_norm",    Fun1(G2, G2)},
                      {"g2_valid",   Fun1(G2, Bool)},
                      {"g2_is_zero", Fun1(G2, Bool)},
                      {"g2_add",     Fun ([G2, G2], G2)},
                      {"g2_mul",     Fun ([Fr, G2], G2)},

                      {"gt_inv",      Fun1(GT, GT)},
                      {"gt_add",      Fun ([GT, GT], GT)},
                      {"gt_mul",      Fun ([GT, GT], GT)},
                      {"gt_pow",      Fun ([GT, Fr], GT)},
                      {"gt_is_one",   Fun1(GT, Bool)},
                      {"pairing",     Fun ([G1, G2], GT)},
                      {"miller_loop", Fun ([G1, G2], GT)},
                      {"final_exp",   Fun1(GT, GT)},

                      {"int_to_fr", Fun1(Int, Fr)},
                      {"int_to_fp", Fun1(Int, Fp)},
                      {"fr_to_int", Fun1(Fr, Int)},
                      {"fp_to_int", Fun1(Fp, Int)}
                     ]),
          types = MkDefs(
                     [{"fr",  0}, {"fp",  0}]) },

    %% Authentication
    AuthScope = #scope
        { funs = MkDefs(
                     [{"tx_hash", Option(Hash)},
                      {"tx",      Option(Tx)}  ]) },

    %% Strings
    StringScope = #scope
        { funs = MkDefs(
                     [{"length",    Fun1(String, Int)},
                      {"concat",    Fun([String, String], String)},
                      {"to_list",   Fun1(String, List(Char))},
                      {"from_list", Fun1(List(Char), String)},
                      {"to_upper",  Fun1(String, String)},
                      {"to_lower",  Fun1(String, String)},
                      {"sha3",      Fun1(String, Hash)},
                      {"sha256",    Fun1(String, Hash)},
                      {"blake2b",   Fun1(String, Hash)}
                     ]) },

    %% Chars
    CharScope = #scope
        { funs = MkDefs(
                     [{"to_int",   Fun1(Char, Int)},
                      {"from_int", Fun1(Int, Option(Char))}]) },

    %% Bits
    BitsScope = #scope
        { funs = MkDefs(
                     [{"set",          Fun([Bits, Int], Bits)},
                      {"clear",        Fun([Bits, Int], Bits)},
                      {"test",         Fun([Bits, Int], Bool)},
                      {"sum",          Fun1(Bits, Int)},
                      {"intersection", Fun([Bits, Bits], Bits)},
                      {"union",        Fun([Bits, Bits], Bits)},
                      {"difference",   Fun([Bits, Bits], Bits)},
                      {"none",         Bits},
                      {"all",          Bits}]) },

    %% Bytes
    BytesScope = #scope
        { funs = MkDefs(
                   [{"to_int", Fun1(Bytes(any), Int)},
                    {"to_str", Fun1(Bytes(any), String)},
                    {"concat", FunC(bytes_concat, [Bytes(any), Bytes(any)], Bytes(any))},
                    {"split",  FunC(bytes_split, [Bytes(any)], Pair(Bytes(any), Bytes(any)))}
                   ]) },

    %% Conversion
    IntScope     = #scope{ funs = MkDefs([{"to_str", Fun1(Int,     String)}]) },
    AddressScope = #scope{ funs = MkDefs([{"to_str", Fun1(Address, String)},
                                          {"to_contract", FunC(address_to_contract, [Address], A)},
                                          {"is_oracle", Fun1(Address, Bool)},
                                          {"is_contract", Fun1(Address, Bool)},
                                          {"is_payable", Fun1(Address, Bool)}]) },


    #env{ scopes =
            #{ []           => TopScope
             , ["Chain"]    => ChainScope
             , ["Contract"] => ContractScope
             , ["Call"]     => CallScope
             , ["Oracle"]   => OracleScope
             , ["AENS"]     => AENSScope
             , ["Map"]      => MapScope
             , ["Auth"]     => AuthScope
             , ["Crypto"]   => CryptoScope
             , ["MCL_BLS12_381"] => MCL_BLS12_381_Scope
             , ["StringInternal"] => StringScope
             , ["Char"]     => CharScope
             , ["Bits"]     => BitsScope
             , ["Bytes"]    => BytesScope
             , ["Int"]      => IntScope
             , ["Address"]  => AddressScope
             }
          , fields =
             maps:from_list([{N, [#field_info{ ann = [], field_t = T, record_t = Tx, kind = record }]}
                             || {N, T} <- TxFlds ])
        }.


-spec init_env(list(option())) -> env().
init_env(_Options) -> global_env().



next_count() ->
    V = case get(counter) of
            undefined ->
                0;
            X -> X
        end,
    put(counter, V + 1),
    V.

%%% ETS AND CONSTRAINTS

is_contract_defined(C) ->
    ets_lookup(defined_contracts, qname(C)) =/= [].


ets_tables() ->
    [options, type_vars, constraints, freshen_tvars, type_errors,
     defined_contracts, warnings, function_calls, all_functions,
     type_vars_variance, functions_to_implement].

clean_up_ets() ->
    [ catch ets_delete(Tab) || Tab <- ets_tables() ],
    ok.

%% Named interface to ETS tables implemented without names.
%% The interface functions behave as the standard ETS interface.

ets_init() ->
    put(aeso_ast_infer_types, #{}),
    create_options(Options),
    ets_new(defined_contracts, [bag]),
    ets_new(type_vars, [set]),
    ets_new(warnings, [bag]),
    ets_new(functions_to_implement, [set]),
    when_warning(warn_unused_functions, fun() -> create_unused_functions() end),
    check_modifiers(Env, Contracts),
    create_type_var_variance(),
    create_type_errors(),
    ok.

ets_tab_exists(Name) ->
    Tabs = get(aeso_ast_infer_types),
    case maps:find(Name, Tabs) of
        {ok, _} -> true;
        error   -> false
    end.

ets_tabid(Name) ->
    #{Name := TabId} = get(aeso_ast_infer_types),
    TabId.

ets_new(Name, Opts) ->
    %% Ensure the table is NOT named!
    TabId = ets:new(Name, Opts -- [named_table]),
    Tabs = get(aeso_ast_infer_types),
    put(aeso_ast_infer_types, Tabs#{Name => TabId}),
    Name.

ets_delete(Name) ->
    Tabs = get(aeso_ast_infer_types),
    #{Name := TabId} = Tabs,
    put(aeso_ast_infer_types, maps:remove(Name, Tabs)),
    ets:delete(TabId).

ets_delete(Name, Key) ->
    TabId = ets_tabid(Name),
    ets:delete(TabId, Key).

ets_insert(Name, Object) ->
    TabId = ets_tabid(Name),
    ets:insert(TabId, Object).

ets_insert_new(Name, Object) ->
    TabId = ets_tabid(Name),
    ets:insert_new(TabId, Object).

ets_lookup(Name, Key) ->
    TabId = ets_tabid(Name),
    ets:lookup(TabId, Key).

ets_match_delete(Name, Pattern) ->
    TabId = ets_tabid(Name),
    ets:match_delete(TabId, Pattern).

ets_tab2list(Name) ->
    TabId = ets_tabid(Name),
    ets:tab2list(TabId).

ets_insert_ordered(_, []) -> true;
ets_insert_ordered(Name, [H|T]) ->
    ets_insert_ordered(Name, H),
    ets_insert_ordered(Name, T);
ets_insert_ordered(Name, Object) ->
    Count = next_count(),
    TabId = ets_tabid(Name),
    ets:insert(TabId, {Count, Object}).

ets_tab2list_ordered(Name) ->
    [E || {_, E} <- ets_tab2list(Name)].

%% Options

create_options(Options) ->
    ets_new(options, [set]),
    Tup = fun(Opt) when is_atom(Opt) -> {Opt, true};
             (Opt) when is_tuple(Opt) -> Opt end,
    ets_insert(options, lists:map(Tup, Options)).

get_option(Key, Default) ->
    case ets_lookup(options, Key) of
        [{Key, Val}] -> Val;
        _            -> Default
    end.

when_option(Opt, Do) ->
    get_option(Opt, false) andalso Do().

%% -- Constraints --

create_constraints() ->
    ets_new(constraints, [ordered_set]).

-spec add_constraint(constraint() | [constraint()]) -> true.
add_constraint(Constraint) ->
    ets_insert_ordered(constraints, Constraint).

get_constraints() ->
    ets_tab2list_ordered(constraints).

destroy_constraints() ->
    ets_delete(constraints).


create_type_errors() ->
    ets_new(type_errors, [bag]).

destroy_and_report_type_errors(Env) ->
    Errors0 = lists:reverse(ets_tab2list(type_errors)),
    %% io:format("Type errors now: ~p\n", [Errors0]),
    ets_delete(type_errors),
    Errors  = [ mk_error(unqualify(Env, Err)) || Err <- Errors0 ],
    aeso_errors:throw(Errors).  %% No-op if Errors == []

destroy_and_report_warnings_as_type_errors() ->
    Warnings = [ mk_warning(Warn) || Warn <- ets_tab2list(warnings) ],
    Errors = lists:map(fun mk_t_err_from_warn/1, Warnings),
    aeso_errors:throw(Errors).  %% No-op if Warnings == []

create_type_vars_variance() ->
    ets_new(type_vars_variance, [set]),
    %% Set the variance for builtin types
    ets_insert(type_vars_variance, {"list", [covariant]}),
    ets_insert(type_vars_variance, {"option", [covariant]}),
    ets_insert(type_vars_variance, {"map", [covariant, covariant]}),
    ets_insert(type_vars_variance, {"oracle", [contravariant, covariant]}),
    ets_insert(type_vars_variance, {"oracle_query", [covariant, covariant]}),
    ok.


create_freshen_tvars() ->
    ets_new(freshen_tvars, [set]).

destroy_freshen_tvars() ->
    ets_delete(freshen_tvars).


%%%% TYPES


%% Contract entrypoints take three named arguments
%%  gas       : int  = Call.gas_left()
%%  value     : int  = 0
%%  protected : bool = false
contract_call_type({fun_t, Ann, [], Args, Ret}) ->
    Id    = fun(X) -> {id, Ann, X} end,
    Int   = Id("int"),
    Typed = fun(E, T) -> {typed, Ann, E, T} end,
    Named = fun(Name, Default = {typed, _, _, T}) -> {named_arg_t, Ann, Id(Name), T, Default} end,
    {fun_t, Ann, [Named("gas",   Typed({app, Ann, Typed({qid, Ann, ["Call", "gas_left"]},
                                                        {fun_t, Ann, [], [], Int}),
                                        []}, Int)),
                  Named("value", Typed({int, Ann, 0}, Int)),
                  Named("protected", Typed({bool, Ann, false}, Id("bool")))],
     Args, {if_t, Ann, Id("protected"), {app_t, Ann, {id, Ann, "option"}, [Ret]}, Ret}}.


%% -- Name manipulation ------------------------------------------------------

-spec qname(type_id()) -> qname().
qname({id,   _, X})  -> [X];
qname({qid,  _, Xs}) -> Xs;
qname({con,  _, X})  -> [X];
qname({qcon, _, Xs}) -> Xs.

-spec name(aeso_syntax:id() | aeso_syntax:con()) -> name().
name({_, _, X}) -> X.

-spec qid(aeso_syntax:ann(), qname()) -> aeso_syntax:id() | aeso_syntax:qid().
qid(Ann, [X]) -> {id, Ann, X};
qid(Ann, Xs)  -> {qid, Ann, Xs}.

-spec qcon(aeso_syntax:ann(), qname()) -> aeso_syntax:con() | aeso_syntax:qcon().
qcon(Ann, [X]) -> {con, Ann, X};
qcon(Ann, Xs)  -> {qcon, Ann, Xs}.

-spec set_qname(qname(), type_id()) -> type_id().
set_qname(Xs, {id,   Ann, _}) -> qid(Ann, Xs);
set_qname(Xs, {qid,  Ann, _}) -> qid(Ann, Xs);
set_qname(Xs, {con,  Ann, _}) -> qcon(Ann, Xs);
set_qname(Xs, {qcon, Ann, _}) -> qcon(Ann, Xs).

is_private(Ann) -> proplists:get_value(private, Ann, false).


option_t(As, T) -> {app_t, As, {id, As, "option"}, [T]}.
map_t(As, K, V) -> {app_t, As, {id, As, "map"}, [K, V]}.


free_vars({int, _, _})    -> [];
free_vars({char, _, _})   -> [];
free_vars({string, _, _}) -> [];
free_vars({bool, _, _})   -> [];
free_vars(Id={id, _, _})  -> [Id];
free_vars({con, _, _})    -> [];
free_vars({qcon, _, _})   -> [];
free_vars({tuple, _, Cpts}) ->
    free_vars(Cpts);
free_vars({list, _, Elems}) ->
    free_vars(Elems);
free_vars({app, _, {'::', _}, Args}) ->
    free_vars(Args);
free_vars({app, _, {con, _, _}, Args}) ->
    free_vars(Args);
free_vars({app, _, {qcon, _, _}, Args}) ->
    free_vars(Args);
free_vars({record, _, Fields}) ->
    free_vars([E || {field, _, _, E} <- Fields]);
free_vars({typed, _, A, _}) ->
    free_vars(A);
free_vars({letpat, _, Id, Pat}) ->
    free_vars(Id) ++ free_vars(Pat);
free_vars(L) when is_list(L) ->
    [V || Elem <- L,
          V <- free_vars(Elem)].


specialize_dependent_type(Env, Type) ->
    case dereference(Type) of
        {if_t, _, {id, _, Arg}, Then, Else} ->
            Val = maps:get(Arg, Env),
            case Val of
                {typed, _, {bool, _, true}, _}  -> Then;
                {typed, _, {bool, _, false}, _} -> Else;
                _ ->
                    type_error({named_argument_must_be_literal_bool, Arg, Val}),
                    fresh_uvar(aeso_syntax:get_ann(Val))
            end;
        _ -> Type   %% Currently no deep dependent types
    end.


%% During type inference, record types are represented by their
%% names. But, before we pass the typed program to the code generator,
%% we replace record types annotating expressions with their
%% definition. This enables the code generator to see the fields.
unfold_record_types(Env, T) ->
    unfold_types(Env, T, [unfold_record_types]).

unfold_types(Env, {typed, Attr, E, Type}, Options) ->
    Options1 = [{ann, Attr} | lists:keydelete(ann, 1, Options)],
    {typed, Attr, unfold_types(Env, E, Options), unfold_types_in_type(Env, Type, Options1)};
unfold_types(Env, {arg, Attr, Id, Type}, Options) ->
    {arg, Attr, Id, unfold_types_in_type(Env, Type, Options)};
unfold_types(Env, {type_sig, Ann, Constr, NamedArgs, Args, Ret}, Options) ->
    {type_sig, Ann, Constr,
               unfold_types_in_type(Env, NamedArgs, Options),
               unfold_types_in_type(Env, Args, Options),
               unfold_types_in_type(Env, Ret, Options)};
unfold_types(Env, {type_def, Ann, Name, Args, Def}, Options) ->
    {type_def, Ann, Name, Args, unfold_types_in_type(Env, Def, Options)};
unfold_types(Env, {fun_decl, Ann, Name, Type}, Options) ->
    {fun_decl, Ann, Name, unfold_types(Env, Type, Options)};
unfold_types(Env, {letfun, Ann, Name, Args, Type, [{guarded, AnnG, [], Body}]}, Options) ->
    {letfun, Ann, Name, unfold_types(Env, Args, Options), unfold_types_in_type(Env, Type, Options), [{guarded, AnnG, [], unfold_types(Env, Body, Options)}]};
unfold_types(Env, T, Options) when is_tuple(T) ->
    list_to_tuple(unfold_types(Env, tuple_to_list(T), Options));
unfold_types(Env, [H|T], Options) ->
    [unfold_types(Env, H, Options)|unfold_types(Env, T, Options)];
unfold_types(_Env, X, _Options) ->
    X.

unfold_types_in_type(Env, T) ->
    unfold_types_in_type(Env, T, []).

unfold_types_in_type(Env, {app_t, Ann, Id = {id, _, "map"}, Args = [KeyType0, _]}, Options) ->
    Args1 = [KeyType, _] = unfold_types_in_type(Env, Args, Options),
    Ann1 = proplists:get_value(ann, Options, aeso_syntax:get_ann(KeyType0)),
    [ type_error({map_in_map_key, Ann1, KeyType0}) || has_maps(KeyType) ],
    {app_t, Ann, Id, Args1};
unfold_types_in_type(Env, {app_t, Ann, Id, Args}, Options) when ?is_type_id(Id) ->
    when_warning(warn_unused_typedefs, fun() -> used_typedef(Id, length(Args)) end),
    UnfoldRecords  = proplists:get_value(unfold_record_types, Options, false),
    UnfoldVariants = proplists:get_value(unfold_variant_types, Options, false),
    case lookup_type(Env, Id) of
        {_, {_, {Formals, {record_t, Fields}}}} when UnfoldRecords, length(Formals) == length(Args) ->
            {record_t,
             unfold_types_in_type(Env,
               subst_tvars(lists:zip(Formals, Args), Fields), Options)};
        {_, {_, {Formals, {alias_t, Type}}}} when length(Formals) == length(Args) ->
            unfold_types_in_type(Env, subst_tvars(lists:zip(Formals, Args), Type), Options);
        {_, {_, {Formals, {variant_t, Constrs}}}} when UnfoldVariants, length(Formals) == length(Args) ->
            %% TODO: unfolding variant types will not work well if we add recursive types!
            {variant_t,
             unfold_types_in_type(Env,
                subst_tvars(lists:zip(Formals, Args), Constrs), Options)};
        _ ->
            %% Not a record type, or ill-formed record type.
            {app_t, Ann, Id, unfold_types_in_type(Env, Args, Options)}
    end;
unfold_types_in_type(Env, Id, Options) when ?is_type_id(Id) ->
    %% Like the case above, but for types without parameters.
    when_warning(warn_unused_typedefs, fun() -> used_typedef(Id, 0) end),
    UnfoldRecords = proplists:get_value(unfold_record_types, Options, false),
    UnfoldVariants = proplists:get_value(unfold_variant_types, Options, false),
    case lookup_type(Env, Id) of
        {_, {_, {[], {record_t, Fields}}}} when UnfoldRecords ->
            {record_t, unfold_types_in_type(Env, Fields, Options)};
        {_, {_, {[], {variant_t, Constrs}}}} when UnfoldVariants ->
            {variant_t, unfold_types_in_type(Env, Constrs, Options)};
        {_, {_, {[], {alias_t, Type1}}}} ->
            unfold_types_in_type(Env, Type1, Options);
        _ ->
            %% Not a record type, or ill-formed record type
            Id
    end;
unfold_types_in_type(Env, {field_t, Attr, Name, Type}, Options) ->
    {field_t, Attr, Name, unfold_types_in_type(Env, Type, Options)};
unfold_types_in_type(Env, {constr_t, Ann, Con, Types}, Options) ->
    {constr_t, Ann, Con, unfold_types_in_type(Env, Types, Options)};
unfold_types_in_type(Env, {named_arg_t, Ann, Con, Types, Default}, Options) ->
    {named_arg_t, Ann, Con, unfold_types_in_type(Env, Types, Options), Default};
unfold_types_in_type(Env, T, Options) when is_tuple(T) ->
    list_to_tuple(unfold_types_in_type(Env, tuple_to_list(T), Options));
unfold_types_in_type(Env, [H|T], Options) ->
    [unfold_types_in_type(Env, H, Options)|unfold_types_in_type(Env, T, Options)];
unfold_types_in_type(_Env, X, _Options) ->
    X.

has_maps({app_t, _, {id, _, "map"}, _}) ->
    true;
has_maps(L) when is_list(L) ->
    lists:any(fun has_maps/1, L);
has_maps(T) when is_tuple(T) ->
    has_maps(tuple_to_list(T));
has_maps(_) -> false.

subst_tvars(Env, Type) ->
    subst_tvars1([{V, T} || {{tvar, _, V}, T} <- Env], Type).

subst_tvars1(Env, T={tvar, _, Name}) ->
    proplists:get_value(Name, Env, T);
subst_tvars1(Env, [H|T]) ->
    [subst_tvars1(Env, H)|subst_tvars1(Env, T)];
subst_tvars1(Env, Type) when is_tuple(Type) ->
    list_to_tuple(subst_tvars1(Env, tuple_to_list(Type)));
subst_tvars1(_Env, X) ->
    X.

%% Unification

unify(Env, A, B, When) -> unify0(Env, A, B, covariant, When).

unify0(_, {id, _, "_"}, _, _Variance, _When) -> true;
unify0(_, _, {id, _, "_"}, _Variance, _When) -> true;
unify0(Env, A, B, Variance, When) ->
    Options =
        case When of    %% Improve source location for map_in_map_key errors
            {check_expr, E, _, _} -> [{ann, aeso_syntax:get_ann(E)}];
            _                     -> []
        end,
    A1 = dereference(unfold_types_in_type(Env, A, Options)),
    B1 = dereference(unfold_types_in_type(Env, B, Options)),
    unify1(Env, A1, B1, Variance, When).

unify1(_Env, {uvar, _, R}, {uvar, _, R}, _Variance, _When) ->
    true;
unify1(_Env, {uvar, _, _}, {fun_t, _, _, var_args, _}, _Variance, When) ->
    type_error({unify_varargs, When});
unify1(Env, {uvar, A, R}, T, _Variance, When) ->
    case occurs_check(R, T) of
        true ->
            if
                Env#env.unify_throws ->
                    cannot_unify({uvar, A, R}, T, none, When);
                true ->
                    ok
            end,
            false;
        false ->
            ets_insert(type_vars, {R, T}),
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
            if
                Env#env.unify_throws ->
                    IsSubtype = is_subtype(Env, NameA, NameB, contravariant) orelse
                                is_subtype(Env, NameA, NameB, covariant),
                    Cxt = case IsSubtype of
                              true  -> Variance;
                              false -> none
                          end,
                    cannot_unify(A, B, Cxt, When);
                true ->
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
    Variances = case ets_lookup(type_vars_variance, F) of
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
    if
        Env#env.unify_throws ->
            cannot_unify(A, B, none, When);
        true ->
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

dereference(T = {uvar, _, R}) ->
    case ets_lookup(type_vars, R) of
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

fresh_uvar(Attrs) ->
    {uvar, Attrs, make_ref()}.

create_freshen_tvars() ->
    ets_new(freshen_tvars, [set]).

destroy_freshen_tvars() ->
    ets_delete(freshen_tvars).

freshen_type(Ann, Type) ->
    create_freshen_tvars(),
    Type1 = freshen(Ann, Type),
    destroy_freshen_tvars(),
    Type1.

freshen(Type) ->
    freshen(aeso_syntax:get_ann(Type), Type).

freshen(Ann, {tvar, _, Name}) ->
    NewT = case ets_lookup(freshen_tvars, Name) of
               []          -> fresh_uvar(Ann);
               [{Name, T}] -> T
           end,
    ets_insert(freshen_tvars, {Name, NewT}),
    NewT;
freshen(Ann, {bytes_t, _, any}) ->
    X = fresh_uvar(Ann),
    add_constraint({is_bytes, X}),
    X;
freshen(Ann, T) when is_tuple(T) ->
    list_to_tuple(freshen(Ann, tuple_to_list(T)));
freshen(Ann, [A | B]) ->
    [freshen(Ann, A) | freshen(Ann, B)];
freshen(_, X) ->
    X.

freshen_type_sig(Ann, TypeSig = {type_sig, _, Constr, _, _, _}) ->
    FunT = freshen_type(Ann, typesig_to_fun_t(TypeSig)),
    apply_typesig_constraint(Ann, Constr, FunT),
    FunT.


%% Dereferences all uvars and replaces the uninstantiated ones with a
%% succession of tvars.
instantiate(E) ->
    instantiate1(dereference(E)).

instantiate1({uvar, Attr, R}) ->
    Next = proplists:get_value(next, ets_lookup(type_vars, next), 0),
    TVar = {tvar, Attr, "'" ++ integer_to_tvar(Next)},
    ets_insert(type_vars, [{next, Next + 1}, {R, TVar}]),
    TVar;
instantiate1({fun_t, Ann, Named, Args, Ret}) ->
    case dereference(Named) of
        {uvar, _, R} ->
            %% Uninstantiated named args map to the empty list
            NoNames = [],
            ets_insert(type_vars, [{R, NoNames}]),
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
    [integer_to_tvar(X div 26)] ++ [$a + (X rem 26)].


is_word_type({id, _, Name}) ->
    lists:member(Name, ["int", "address", "hash", "bits", "bool"]);
is_word_type({app_t, _, {id, _, Name}, [_, _]}) ->
    lists:member(Name, ["oracle", "oracle_query"]);
is_word_type({bytes_t, _, N}) -> N =< 32;
is_word_type({con, _, _}) -> true;
is_word_type({qcon, _, _}) -> true;
is_word_type(_) -> false.

is_string_type({id, _, "string"}) -> true;
is_string_type({bytes_t, _, N}) -> N > 32;
is_string_type(_) -> false.


typesig_to_fun_t({type_sig, Ann, _Constr, Named, Args, Res}) ->
    {fun_t, Ann, Named, Args, Res}.


get_letfun_id({fun_clauses, _, Id, _, _}) -> Id;
get_letfun_id({letfun, _, Id, _, _, _})   -> Id.


arg_type(ArgAnn, {id, Ann, "_"}) ->
    case aeso_syntax:get_ann(origin, Ann, user) of
        system -> fresh_uvar(ArgAnn);
        user   -> fresh_uvar(Ann)
    end;
arg_type(ArgAnn, {app_t, Attrs, Name, Args}) ->
    {app_t, Attrs, Name, [arg_type(ArgAnn, T) || T <- Args]};
arg_type(_, T) ->
    T.


app_t(_Ann, Name, [])  -> Name;
app_t(Ann, Name, Args) -> {app_t, Ann, Name, Args}.

print_typesig({Name, TypeSig}) ->
    ?PRINT_TYPES("Inferred ~s : ~s\n", [Name, pp(TypeSig)]).


%% Strip current namespace from error message for nicer printing.
unqualify(#env{ namespace = NS }, {qid, Ann, Xs}) ->
    qid(Ann, unqualify1(NS, Xs));
unqualify(#env{ namespace = NS }, {qcon, Ann, Xs}) ->
    qcon(Ann, unqualify1(NS, Xs));
unqualify(Env, T) when is_tuple(T) ->
    list_to_tuple(unqualify(Env, tuple_to_list(T)));
unqualify(Env, [H | T]) -> [unqualify(Env, H) | unqualify(Env, T)];
unqualify(_Env, X) -> X.

unqualify1(NS, Xs) ->
    try lists:split(length(NS), Xs) of
        {NS, Ys} -> Ys;
        _        -> Xs
    catch _:_ -> Xs
    end.


get_oracle_type({qid, _, ["Oracle", "register"]},      _        , OType) -> OType;
get_oracle_type({qid, _, ["Oracle", "query"]},        [OType| _], _    ) -> OType;
get_oracle_type({qid, _, ["Oracle", "get_question"]}, [OType| _], _    ) -> OType;
get_oracle_type({qid, _, ["Oracle", "get_answer"]},   [OType| _], _    ) -> OType;
get_oracle_type({qid, _, ["Oracle", "check"]},        [OType| _], _    ) -> OType;
get_oracle_type({qid, _, ["Oracle", "check_query"]},  [OType| _], _    ) -> OType;
get_oracle_type({qid, _, ["Oracle", "respond"]},      [OType| _], _    ) -> OType;
get_oracle_type(_Fun, _Args, _Ret) -> false.


record_type_name({app_t, _Attrs, RecId, _Args}) when ?is_type_id(RecId) ->
    RecId;
record_type_name(RecId) when ?is_type_id(RecId) ->
    RecId;
record_type_name(_Other) ->
    %% io:format("~p is not a record type\n", [Other]),
    {id, [{origin, system}], "not_a_record_type"}.
