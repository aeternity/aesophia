-module(aeso_type_env).


-type utype() :: {fun_t, aeso_syntax:ann(), named_args_t(), [utype()] | var_args, utype()}
               | {app_t, aeso_syntax:ann(), utype(), [utype()]}
               | {tuple_t, aeso_syntax:ann(), [utype()]}
               | aeso_syntax:id()  | aeso_syntax:qid()
               | aeso_syntax:con() | aeso_syntax:qcon()  %% contracts
               | aeso_syntax:tvar()
               | {if_t, aeso_syntax:ann(), aeso_syntax:id(), utype(), utype()}  %% Can branch on named argument (protected)
               | uvar().

-type uvar() :: {uvar, aeso_syntax:ann(), reference()}.

-type named_args_t() :: uvar() | [{named_arg_t, aeso_syntax:ann(), aeso_syntax:id(), utype(), aeso_syntax:expr()}].

-type type_id() :: aeso_syntax:id() | aeso_syntax:qid() | aeso_syntax:con() | aeso_syntax:qcon().

-define(is_type_id(T), element(1, T) =:= id orelse
        element(1, T) =:= qid orelse
        element(1, T) =:= con orelse
        element(1, T) =:= qcon).


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


-type fun_info()  :: {aeso_syntax:ann(), typesig() | type()}.
-type type_info() :: {aeso_syntax:ann(), typedef()}.
-type var_info()  :: {aeso_syntax:ann(), utype()}.

-type fun_env()  :: [{name(), fun_info()}].
-type type_env() :: [{name(), type_info()}].


-record(field_info,
        { ann      :: aeso_syntax:ann()
        , field_t  :: utype()
        , record_t :: utype()
        , kind     :: contract | record }).

-type field_info() :: #field_info{}.


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
               What == contract_interface -> {contract_fun, Ann, Type};
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

-spec bind_field(name(), field_info(), env()) -> env().
bind_field(X, Info, Env = #env{ fields = Fields }) ->
    Fields1 = maps:update_with(X, fun(Infos) -> [Info | Infos] end, [Info], Fields),
    Env#env{ fields = Fields1 }.

-spec bind_fields([{name(), field_info()}], env()) -> env().
bind_fields([], Env) -> Env;
bind_fields([{Id, Info} | Rest], Env) ->
    bind_fields(Rest, bind_field(Id, Info, Env)).

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

-spec bind_contract(aeso_syntax:decl(), env()) -> env().
bind_contract({Contract, Ann, Id, _Impls, Contents}, Env)
  when ?IS_CONTRACT_HEAD(Contract) ->
    Key    = name(Id),
    Sys    = [{origin, system}],
    Fields =
        [ {field_t, AnnF, Entrypoint, contract_call_type(Type)}
          || {fun_decl, AnnF, Entrypoint, Type} <- Contents ] ++
        [ {field_t, AnnF, Entrypoint,
           contract_call_type(
             {fun_t, AnnF, [], [ArgT || {typed, _, _, ArgT} <- Args], RetT})
          }
          || {letfun, AnnF, Entrypoint = {id, _, Name}, Args, _Type, [{guarded, _, [], {typed, _, _, RetT}}]} <- Contents,
             Name =/= "init"
        ] ++
        %% Predefined fields
        [ {field_t, Sys, {id, Sys, "address"}, {id, Sys, "address"}} ] ++
        [ {field_t, Sys, {id, Sys, ?CONSTRUCTOR_MOCK_NAME},
           contract_call_type(
             case [ [ArgT || {typed, _, _, ArgT} <- Args]
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
        bind_fields(FieldInfo, Env)).

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

-spec lookup_env1(env(), type | term, aeso_syntax:ann(), qname()) -> false | {qname(), fun_info()}.
lookup_env1(#env{ namespace = Current, used_namespaces = UsedNamespaces, scopes = Scopes }, Kind, Ann, QName) ->
    Qual = lists:droplast(QName),
    Name = lists:last(QName),
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

-spec lookup_record_field(env(), name()) -> [field_info()].
lookup_record_field(Env, FieldName) ->
    maps:get(FieldName, Env#env.fields, []).

%% For 'create' or 'update' constraints we don't consider contract types.
-spec lookup_record_field(env(), name(), create | project | update) -> [field_info()].
lookup_record_field(Env, FieldName, Kind) ->
    [ Fld || Fld = #field_info{ kind = K } <- lookup_record_field(Env, FieldName),
             Kind == project orelse K /= contract ].

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

%% -- The rest ---------------------------------------------------------------

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
                     %% Abort
                     {"abort", Fun1(String, A)},
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

option_t(As, T) -> {app_t, As, {id, As, "option"}, [T]}.
map_t(As, K, V) -> {app_t, As, {id, As, "map"}, [K, V]}.
