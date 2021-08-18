%%%-------------------------------------------------------------------
%%% @copyright (C) 2018, Aeternity Anstalt
%%% @doc
%%%     Type checker for Sophia.
%%% @end
%%%-------------------------------------------------------------------

%%% All state is kept in a set of ETS tables. These are NOT named
%%% tables and the table ids are kept in process dictionary in a map
%%% under the key 'aeso_ast_infer_types'. This allows multiple
%%% instances of the compiler to be run in parallel.

-module(aeso_ast_infer_types).

-export([ infer/1
        , infer/2
        , unfold_types_in_type/3
        , pp_type/2
        ]).

-include("aeso_utils.hrl").

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

-type type_constraints() :: none | bytes_concat | bytes_split | address_to_contract | bytecode_hash.

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
    , namespace        = []                 :: qname()
    , used_namespaces  = []                 :: list({qname(), namespace_alias()})
    , in_pattern       = false              :: boolean()
    , stateful         = false              :: boolean()
    , current_function = none               :: none | aeso_syntax:id()
    , what             = top                :: top | namespace | contract | contract_interface
    }).

-type env() :: #env{}.

-define(PRINT_TYPES(Fmt, Args),
        when_option(pp_types, fun () -> io:format(Fmt, Args) end)).
-define(CONSTRUCTOR_MOCK_NAME, "#__constructor__#").

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
bind_var({id, Ann, X}, T, Env) ->
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
bind_contract({Contract, Ann, Id, Contents}, Env)
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
          || {letfun, AnnF, Entrypoint = {id, _, Name}, Args, _Type, {typed, _, _, RetT}} <- Contents,
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
    Ret = [ lists:sublist(Current, I) ++ Q || I <- lists:seq(0, length(Current)), Q <- NewQuals ] ++ [ Namespace ++ Q || {Namespace, none} <- UsedNamespaces, Q <- NewQuals ],
    Ret.

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
                [Res] -> Res;
                Many  ->
                    type_error({ambiguous_name, [{qid, A, Q} || {Q, {A, _}} <- Many]}),
                    false
            end
    end.

-spec lookup_env1(env(), type | term, aeso_syntax:ann(), qname()) -> false | {qname(), fun_info()}.
lookup_env1(#env{ namespace = Current, scopes = Scopes }, Kind, Ann, QName) ->
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
                        true  -> {QName, E};
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

-spec infer(aeso_syntax:ast()) -> {aeso_syntax:ast(), aeso_syntax:ast()} | {env(), aeso_syntax:ast(), aeso_syntax:ast()}.
infer(Contracts) ->
    infer(Contracts, []).

-type option() :: return_env | dont_unfold | no_code | debug_mode | term().

-spec init_env(list(option())) -> env().
init_env(_Options) -> global_env().

-spec infer(aeso_syntax:ast(), list(option())) ->
  {aeso_syntax:ast(), aeso_syntax:ast()} | {env(), aeso_syntax:ast(), aeso_syntax:ast()}.
infer([], Options) ->
    create_type_errors(),
    type_error({no_decls, proplists:get_value(src_file, Options, no_file)}),
    destroy_and_report_type_errors(init_env(Options));
infer(Contracts, Options) ->
    ets_init(), %% Init the ETS table state
    try
        Env = init_env(Options),
        create_options(Options),
        ets_new(defined_contracts, [bag]),
        ets_new(type_vars, [set]),
        check_modifiers(Env, Contracts),
        create_type_errors(),
        Contracts1 = identify_main_contract(Contracts, Options),
        destroy_and_report_type_errors(Env),
        {Env1, Decls} = infer1(Env, Contracts1, [], Options),
        {Env2, DeclsFolded, DeclsUnfolded} =
            case proplists:get_value(dont_unfold, Options, false) of
                true  -> {Env1, Decls, Decls};
                false -> E = on_scopes(Env1, fun(Scope) -> unfold_record_types(Env1, Scope) end),
                         {E, Decls, unfold_record_types(E, Decls)}
            end,
        case proplists:get_value(return_env, Options, false) of
            false -> {DeclsFolded, DeclsUnfolded};
            true  -> {Env2, DeclsFolded, DeclsUnfolded}
        end
    after
        clean_up_ets()
    end.

-spec infer1(env(), [aeso_syntax:decl()], [aeso_syntax:decl()], list(option())) ->
    {env(), [aeso_syntax:decl()]}.
infer1(Env, [], Acc, _Options) -> {Env, lists:reverse(Acc)};
infer1(Env, [{Contract, Ann, ConName, Code} | Rest], Acc, Options)
  when ?IS_CONTRACT_HEAD(Contract) ->
    %% do type inference on each contract independently.
    check_scope_name_clash(Env, contract, ConName),
    What = case Contract of
               contract_main -> contract;
               contract_child -> contract;
               contract_interface -> contract_interface
           end,
    case What of
        contract -> ets_insert(defined_contracts, {qname(ConName)});
        contract_interface -> ok
    end,
    {Env1, Code1} = infer_contract_top(push_scope(contract, ConName, Env), What, Code, Options),
    Contract1 = {Contract, Ann, ConName, Code1},
    Env2 = pop_scope(Env1),
    Env3 = bind_contract(Contract1, Env2),
    infer1(Env3, Rest, [Contract1 | Acc], Options);
infer1(Env, [{namespace, Ann, Name, Code} | Rest], Acc, Options) ->
    check_scope_name_clash(Env, namespace, Name),
    {Env1, Code1} = infer_contract_top(push_scope(namespace, Name, Env), namespace, Code, Options),
    Namespace1 = {namespace, Ann, Name, Code1},
    infer1(pop_scope(Env1), Rest, [Namespace1 | Acc], Options);
infer1(Env, [Using = {using, _, _} | Rest], Acc, Options) ->
    infer1(check_usings(Env, [Using]), Rest, Acc, Options);
infer1(Env, [Using = {using, _, _, _} | Rest], Acc, Options) ->
    infer1(check_usings(Env, [Using]), Rest, Acc, Options);
infer1(Env, [{pragma, _, _} | Rest], Acc, Options) ->
    %% Pragmas are checked in check_modifiers
    infer1(Env, Rest, Acc, Options).

%% Asserts that the main contract is somehow defined.
identify_main_contract(Contracts, Options) ->
    Children   = [C || C = {contract_child, _, _, _} <- Contracts],
    Mains      = [C || C = {contract_main, _, _, _} <- Contracts],
    case Mains of
        [] -> case Children of
                  [] -> type_error(
                          {main_contract_undefined,
                           [{file, File} || {src_file, File} <- Options]});
                  [{contract_child, Ann, Con, Body}] ->
                      (Contracts -- Children) ++ [{contract_main, Ann, Con, Body}];
                  [H|_] -> type_error({ambiguous_main_contract,
                                       aeso_syntax:get_ann(H)})
              end;
        [_] -> (Contracts -- Mains) ++ Mains; %% Move to the end
        [H|_] -> type_error({multiple_main_contracts,
                             aeso_syntax:get_ann(H)})
    end.

check_scope_name_clash(Env, Kind, Name) ->
    case get_scope(Env, qname(Name)) of
        false -> ok;
        #scope{ kind = K, ann = Ann } ->
            create_type_errors(),
            type_error({duplicate_scope, Kind, Name, K, Ann}),
            destroy_and_report_type_errors(Env)
    end.

-spec infer_contract_top(env(), contract_interface | contract | namespace, [aeso_syntax:decl()], list(option())) ->
    {env(), [aeso_syntax:decl()]}.
infer_contract_top(Env, Kind, Defs0, Options) ->
    create_type_errors(),
    Defs = desugar(Defs0),
    destroy_and_report_type_errors(Env),
    infer_contract(Env, Kind, Defs, Options).

%% infer_contract takes a proplist mapping global names to types, and
%% a list of definitions.
-spec infer_contract(env(), contract_interface | contract | namespace, [aeso_syntax:decl()], list(option())) -> {env(), [aeso_syntax:decl()]}.
infer_contract(Env0, What, Defs0, Options) ->
    create_type_errors(),
    Defs01 = process_blocks(Defs0),
    Defs = case lists:member(debug_mode, Options) of
               true  -> expose_internals(Defs01, What);
               false -> Defs01
           end,
    destroy_and_report_type_errors(Env0),
    Env  = Env0#env{ what = What },
    Kind = fun({type_def, _, _, _, _})    -> type;
              ({letfun, _, _, _, _, _})   -> function;
              ({fun_clauses, _, _, _, _}) -> function;
              ({fun_decl, _, _, _})       -> prototype;
              ({using, _, _})             -> using;
              ({using, _, _, _})          -> using;
              (_)                         -> unexpected
           end,
    Get = fun(K, In) -> [ Def || Def <- In, Kind(Def) == K ] end,
    Env01 = check_usings(Env, Get(using, Defs)),
    {Env1, TypeDefs} = check_typedefs(Env01, Get(type, Defs)),
    create_type_errors(),
    check_unexpected(Get(unexpected, Defs)),
    Env2 =
        case What of
            namespace          -> Env1;
            contract_interface -> Env1;
            contract           -> bind_state(Env1)   %% bind state and put
        end,
    {ProtoSigs, Decls} = lists:unzip([ check_fundecl(Env1, Decl) || Decl <- Get(prototype, Defs) ]),
    Env3      = bind_funs(ProtoSigs, Env2),
    Functions = Get(function, Defs),
    %% Check for duplicates in Functions (we turn it into a map below)
    FunBind   = fun({letfun, Ann, {id, _, Fun}, _, _, _})   -> {Fun, {tuple_t, Ann, []}};
                   ({fun_clauses, Ann, {id, _, Fun}, _, _}) -> {Fun, {tuple_t, Ann, []}} end,
    FunName   = fun(Def) -> {Name, _} = FunBind(Def), Name end,
    _         = bind_funs(lists:map(FunBind, Functions), #env{}),
    FunMap    = maps:from_list([ {FunName(Def), Def} || Def <- Functions ]),
    check_reserved_entrypoints(FunMap),
    DepGraph  = maps:map(fun(_, Def) -> aeso_syntax_utils:used_ids(Def) end, FunMap),
    SCCs      = aeso_utils:scc(DepGraph),
    {Env4, Defs1} = check_sccs(Env3, FunMap, SCCs, []),
    %% Check that `init` doesn't read or write the state
    check_state_dependencies(Env4, Defs1),
    destroy_and_report_type_errors(Env4),
    %% Add inferred types of definitions
    {Env4, TypeDefs ++ Decls ++ Defs1}.

%% Restructure blocks into multi-clause fundefs (`fun_clauses`).
-spec process_blocks([aeso_syntax:decl()]) -> [aeso_syntax:decl()].
process_blocks(Decls) ->
    lists:flatmap(
      fun({block, Ann, Ds}) -> process_block(Ann, Ds);
         (Decl)             -> [Decl] end, Decls).

-spec process_block(aeso_syntax:ann(), [aeso_syntax:decl()]) -> [aeso_syntax:decl()].
process_block(_, []) -> [];
process_block(_, [Decl]) -> [Decl];
process_block(_Ann, [Decl | Decls]) ->
    IsThis = fun(Name) -> fun({letfun, _, {id, _, Name1}, _, _, _}) -> Name == Name1;
                             (_) -> false end end,
    case Decl of
        {fun_decl, Ann1, Id = {id, _, Name}, Type} ->
            {Clauses, Rest} = lists:splitwith(IsThis(Name), Decls),
            [type_error({mismatched_decl_in_funblock, Name, D1}) || D1 <- Rest],
            [{fun_clauses, Ann1, Id, Type, Clauses}];
        {letfun, Ann1, Id = {id, _, Name}, _, _, _} ->
            {Clauses, Rest} = lists:splitwith(IsThis(Name), [Decl | Decls]),
            [type_error({mismatched_decl_in_funblock, Name, D1}) || D1 <- Rest],
            [{fun_clauses, Ann1, Id, {id, [{origin, system} | Ann1], "_"}, Clauses}]
    end.

%% Turns private stuff into public stuff
expose_internals(Defs, What) ->
    [ begin
          Ann = element(2, Def),
          NewAnn = case What of
                       namespace          -> [A ||A <- Ann, A /= {private, true}, A /= private];
                       contract           -> [{entrypoint, true}|Ann];  % minor duplication
                       contract_interface -> Ann
                   end,
          Def1 = setelement(2, Def, NewAnn),
          case Def1 of  % fix inner clauses
              {fun_clauses, Ans, Id, T, Clauses} ->
                  {fun_clauses, Ans, Id, T, expose_internals(Clauses, What)};
              _ -> Def1
          end
      end
     || Def <- Defs
    ].

-spec check_typedefs(env(), [aeso_syntax:decl()]) -> {env(), [aeso_syntax:decl()]}.
check_typedefs(Env = #env{ namespace = Ns }, Defs) ->
    create_type_errors(),
    GetName  = fun({type_def, _, {id, _, Name}, _, _}) -> Name end,
    TypeMap  = maps:from_list([ {GetName(Def), Def} || Def <- Defs ]),
    DepGraph = maps:map(fun(_, Def) -> aeso_syntax_utils:used_types(Ns, Def) end, TypeMap),
    SCCs     = aeso_utils:scc(DepGraph),
    {Env1, Defs1} = check_typedef_sccs(Env, TypeMap, SCCs, []),
    destroy_and_report_type_errors(Env),
    {Env1, Defs1}.

-spec check_typedef_sccs(env(), #{ name() => aeso_syntax:decl() },
                         [{acyclic, name()} | {cyclic, [name()]}], [aeso_syntax:decl()]) ->
        {env(), [aeso_syntax:decl()]}.
check_typedef_sccs(Env, _TypeMap, [], Acc) -> {Env, lists:reverse(Acc)};
check_typedef_sccs(Env, TypeMap, [{acyclic, Name} | SCCs], Acc) ->
    case maps:get(Name, TypeMap, undefined) of
        undefined -> check_typedef_sccs(Env, TypeMap, SCCs, Acc);    %% Builtin type
        {type_def, Ann, D, Xs, Def0} ->
            Def  = check_event(Env, Name, Ann, check_typedef(bind_tvars(Xs, Env), Def0)),
            Acc1 = [{type_def, Ann, D, Xs, Def} | Acc],
            Env1 = bind_type(Name, Ann, {Xs, Def}, Env),
            case Def of
                {alias_t, _}  -> check_typedef_sccs(Env1, TypeMap, SCCs, Acc1);
                {record_t, Fields} ->
                    %% check_type to get qualified name
                    RecTy = check_type(Env1, app_t(Ann, D, Xs)),
                    Env2 = check_fields(Env1, TypeMap, RecTy, Fields),
                    check_typedef_sccs(Env2, TypeMap, SCCs, Acc1);
                {variant_t, Cons} ->
                    Target   = check_type(Env1, app_t(Ann, D, Xs)),
                    ConType  = fun([]) -> Target; (Args) -> {type_sig, Ann, none, [], Args, Target} end,
                    ConTypes = [ begin
                                    {constr_t, _, {con, _, Con}, Args} = ConDef,
                                    {Con, ConType(Args)}
                                 end || ConDef <- Cons ],
                    check_repeated_constructors([ {Con, ConType(Args)} || {constr_t, _, Con, Args} <- Cons ]),
                    [ check_constructor_overlap(Env1, Con, Target) || {constr_t, _, Con, _} <- Cons ],
                    check_typedef_sccs(bind_funs(ConTypes, Env1), TypeMap, SCCs, Acc1)
            end
    end;
check_typedef_sccs(Env, TypeMap, [{cyclic, Names} | SCCs], Acc) ->
    Id = fun(X) -> {type_def, _, D, _, _} = maps:get(X, TypeMap), D end,
    type_error({recursive_types_not_implemented, lists:map(Id, Names)}),
    check_typedef_sccs(Env, TypeMap, SCCs, Acc).

-spec check_typedef(env(), aeso_syntax:typedef()) -> aeso_syntax:typedef().
check_typedef(Env, {alias_t, Type}) ->
    {alias_t, check_type(Env, Type)};
check_typedef(Env, {record_t, Fields}) ->
    {record_t, [ {field_t, Ann, Id, check_type(Env, Type)} || {field_t, Ann, Id, Type} <- Fields ]};
check_typedef(Env, {variant_t, Cons}) ->
    {variant_t, [ {constr_t, Ann, Con, [ check_type(Env, Arg) || Arg <- Args ]}
                || {constr_t, Ann, Con, Args} <- Cons ]}.

check_usings(Env, []) ->
    Env;
check_usings(Env = #env{ used_namespaces = UsedNamespaces }, [{using, _, Con} | Rest]) ->
    check_usings(Env#env{ used_namespaces = UsedNamespaces ++ [{qname(Con), none}] }, Rest);
check_usings(Env = #env{ used_namespaces = UsedNamespaces }, [{using, _, Con, Alias} | Rest]) ->
    check_usings(Env#env{ used_namespaces = UsedNamespaces ++ [{qname(Con), qname(Alias)}] }, Rest).

check_unexpected(Xs) ->
    [ type_error(X) || X <- Xs ].

check_modifiers(Env, Contracts) ->
    create_type_errors(),
    check_modifiers_(Env, Contracts),
    destroy_and_report_type_errors(Env).

check_modifiers_(Env, [{Contract, _, Con, Decls} | Rest])
  when ?IS_CONTRACT_HEAD(Contract) ->
    IsInterface = Contract =:= contract_interface,
    check_modifiers1(contract, Decls),
    case {lists:keymember(letfun, 1, Decls),
            [ D || D <- Decls, aeso_syntax:get_ann(entrypoint, D, false) ]} of
        {true, []} -> type_error({contract_has_no_entrypoints, Con});
        _ when IsInterface ->
            case [ {AnnF, Id} || {letfun, AnnF, Id, _, _, _} <- Decls ] of
                [{AnnF, Id} | _] -> type_error({definition_in_contract_interface, AnnF, Id});
                [] -> ok
            end;
        _ -> ok
    end,
    check_modifiers_(Env, Rest);
check_modifiers_(Env, [{namespace, _, _, Decls} | Rest]) ->
    check_modifiers1(namespace, Decls),
    check_modifiers_(Env, Rest);
check_modifiers_(Env, [{pragma, Ann, Pragma} | Rest]) ->
    check_pragma(Env, Ann, Pragma),
    check_modifiers_(Env, Rest);
check_modifiers_(Env, [{using, _, _} | Rest]) ->
    check_modifiers_(Env, Rest);
check_modifiers_(Env, [{using, _, _, _} | Rest]) ->
    check_modifiers_(Env, Rest);
check_modifiers_(Env, [Decl | Rest]) ->
    type_error({bad_top_level_decl, Decl}),
    check_modifiers_(Env, Rest);
check_modifiers_(_Env, []) -> ok.

-spec check_pragma(env(), aeso_syntax:ann(), aeso_syntax:pragma()) -> ok.
check_pragma(_Env, Ann, {compiler, Op, Ver}) ->
    case aeso_compiler:numeric_version() of
        {error, Err}  -> type_error({failed_to_get_compiler_version, Err});
        {ok, Version} ->
            Strip = fun(V) -> lists:reverse(lists:dropwhile(fun(X) -> X == 0 end, lists:reverse(V))) end,
            case apply(erlang, Op, [Strip(Version), Strip(Ver)]) of
                true  -> ok;
                false -> type_error({compiler_version_mismatch, Ann, Version, Op, Ver})
            end
    end.

-spec check_modifiers1(contract | namespace, [aeso_syntax:decl()] | aeso_syntax:decl()) -> ok.
check_modifiers1(What, Decls) when is_list(Decls) ->
    _ = [ check_modifiers1(What, Decl) || Decl <- Decls ],
    ok;
check_modifiers1(What, Decl) when element(1, Decl) == letfun; element(1, Decl) == fun_decl ->
    Public     = aeso_syntax:get_ann(public,     Decl, false),
    Private    = aeso_syntax:get_ann(private,    Decl, false),
    Payable    = aeso_syntax:get_ann(payable,    Decl, false),
    Entrypoint = aeso_syntax:get_ann(entrypoint, Decl, false),
    FunDecl    = element(1, Decl) == fun_decl,
    {id, _, Name} = element(3, Decl),
    IsInit     = Name == "init" andalso What == contract,
    _ = [ type_error({proto_must_be_entrypoint, Decl})    || FunDecl, Private orelse not Entrypoint, What == contract ],
    _ = [ type_error({proto_in_namespace, Decl})          || FunDecl, What == namespace ],
    _ = [ type_error({init_must_be_an_entrypoint, Decl})  || not Entrypoint, IsInit ],
    _ = [ type_error({init_must_not_be_payable, Decl})    || Payable, IsInit ],
    _ = [ type_error({public_modifier_in_contract, Decl}) || Public, not Private, not Entrypoint, What == contract ],
    _ = [ type_error({entrypoint_in_namespace, Decl})     || Entrypoint, What == namespace ],
    _ = [ type_error({private_entrypoint, Decl})          || Private, Entrypoint ],
    _ = [ type_error({private_and_public, Decl})          || Private, Public ],
    ok;
check_modifiers1(_, _) -> ok.

-spec check_type(env(), aeso_syntax:type()) -> aeso_syntax:type().
check_type(Env, T) ->
    check_type(Env, T, 0).

%% Check a type against an arity.
-spec check_type(env(), utype(), non_neg_integer()) -> utype().
check_type(Env, T = {tvar, _, _}, Arity) ->
    [ type_error({higher_kinded_typevar, T}) || Arity /= 0 ],
    check_tvar(Env, T);
check_type(_Env, X = {id, Ann, "_"}, Arity) ->
    ensure_base_type(X, Arity),
    fresh_uvar(Ann);
check_type(Env, X = {Tag, _, _}, Arity) when Tag == con; Tag == qcon; Tag == id; Tag == qid ->
    case lookup_type(Env, X) of
        {Q, {_, Def}} ->
            Arity1 = case Def of
                        {builtin, Ar} -> Ar;
                        {Args, _}     -> length(Args)
                     end,
            [ type_error({wrong_type_arguments, X, Arity, Arity1}) || Arity /= Arity1 ],
            set_qname(Q, X);
        false  -> type_error({unbound_type, X}), X
    end;
check_type(Env, Type = {tuple_t, Ann, Types}, Arity) ->
    ensure_base_type(Type, Arity),
    {tuple_t, Ann, [ check_type(Env, T, 0) || T <- Types ]};
check_type(_Env, Type = {bytes_t, _Ann, _Len}, Arity) ->
    ensure_base_type(Type, Arity),
    Type;
check_type(Env, {app_t, Ann, Type, Types}, Arity) ->
    Types1 = [ check_type(Env, T, 0) || T <- Types ],
    Type1  = check_type(Env, Type, Arity + length(Types)),
    {app_t, Ann, Type1, Types1};
check_type(Env, Type = {fun_t, Ann, NamedArgs, Args, Ret}, Arity) ->
    ensure_base_type(Type, Arity),
    NamedArgs1 = [ check_named_arg(Env, NamedArg) || NamedArg <- NamedArgs ],
    Args1      = [ check_type(Env, Arg, 0) || Arg <- Args ],
    Ret1       = check_type(Env, Ret, 0),
    {fun_t, Ann, NamedArgs1, Args1, Ret1};
check_type(_Env, Type = {uvar, _, _}, Arity) ->
    ensure_base_type(Type, Arity),
    Type;
check_type(_Env, {args_t, Ann, Ts}, _) ->
    type_error({new_tuple_syntax, Ann, Ts}),
    {tuple_t, Ann, Ts}.

ensure_base_type(Type, Arity) ->
    [ type_error({wrong_type_arguments, Type, Arity, 0}) || Arity /= 0 ],
    ok.

-spec check_named_arg(env(), aeso_syntax:named_arg_t()) -> aeso_syntax:named_arg_t().
check_named_arg(Env, {named_arg_t, Ann, Id, Type, Default}) ->
    Type1 = check_type(Env, Type),
    {typed, _, Default1, _} = check_expr(Env, Default, Type1),
    {named_arg_t, Ann, Id, Type1, Default1}.

-spec check_fields(env(), #{ name() => aeso_syntax:decl() }, type(), [aeso_syntax:field_t()]) -> env().
check_fields(Env, _TypeMap, _, []) -> Env;
check_fields(Env, TypeMap, RecTy, [{field_t, Ann, Id, Type} | Fields]) ->
    Env1 = bind_field(name(Id), #field_info{ ann = Ann, kind = record, field_t = Type, record_t = RecTy }, Env),
    check_fields(Env1, TypeMap, RecTy, Fields).

check_event(Env, "event", Ann, Def) ->
    case Def of
        {variant_t, Cons} ->
            {variant_t, [ check_event_con(Env, Con) || Con <- Cons ]};
        _ ->
            type_error({event_must_be_variant_type, Ann}),
            Def
    end;
check_event(_Env, _Name, _Ann, Def) -> Def.

check_event_con(Env, {constr_t, Ann, Con, Args}) ->
    IsIndexed  = fun(T) ->
                     T1 = unfold_types_in_type(Env, T),
                     %% `indexed` is optional but if used it has to be correctly used
                     case {is_word_type(T1), is_string_type(T1), aeso_syntax:get_ann(indexed, T, false)} of
                         {true, _, _}        -> indexed;
                         {false, true, true} -> type_error({indexed_type_must_be_word, T, T1});
                         {false, true, _}    -> notindexed;
                         {false, false, _}   -> type_error({event_arg_type_word_or_string, T, T1}), error
                     end
                 end,
    Indices    = lists:map(IsIndexed, Args),
    Indexed    = [ T || T <- Args, IsIndexed(T) == indexed ],
    NonIndexed = Args -- Indexed,
    [ type_error({event_0_to_3_indexed_values, Con}) || length(Indexed) > 3 ],
    [ type_error({event_0_to_1_string_values, Con}) || length(NonIndexed) > 1 ],
    {constr_t, [{indices, Indices} | Ann], Con, Args}.

%% Not so nice.
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

-spec check_constructor_overlap(env(), aeso_syntax:con(), type()) -> ok | no_return().
check_constructor_overlap(Env, Con = {con, Ann, Name}, NewType) ->
    case lookup_env(Env, term, Ann, Name) of
        false -> ok;
        {_, {Ann, Type}} ->
            OldType = case Type of {type_sig, _, _, _, _, T} -> T;
                                   _ -> Type end,
            OldCon  = {con, Ann, Name},
            type_error({repeated_constructor, [{OldCon, OldType}, {Con, NewType}]})
    end.

check_repeated_constructors(Cons) ->
    Names      = [ Name || {{con, _, Name}, _} <- Cons ],
    Duplicated = lists:usort(Names -- lists:usort(Names)),
    Fail       = fun(Name) ->
                    type_error({repeated_constructor, [ CT || CT = {{con, _, C}, _} <- Cons, C == Name ]})
                 end,
    [ Fail(Dup) || Dup <- Duplicated ],
    ok.

-spec check_sccs(env(), #{ name() => aeso_syntax:decl() }, [{acyclic, name()} | {cyclic, [name()]}], [aeso_syntax:decl()]) ->
        {env(), [aeso_syntax:decl()]}.
check_sccs(Env, _, [], Acc) -> {Env, lists:reverse(Acc)};
check_sccs(Env = #env{}, Funs, [{acyclic, X} | SCCs], Acc) ->
    case maps:get(X, Funs, undefined) of
        undefined ->    %% Previously defined function
            check_sccs(Env, Funs, SCCs, Acc);
        Def ->
            {{_, TypeSig}, Def1} = infer_nonrec(Env, Def),
            Env1 = bind_fun(X, TypeSig, Env),
            check_sccs(Env1, Funs, SCCs, [Def1 | Acc])
    end;
check_sccs(Env = #env{}, Funs, [{cyclic, Xs} | SCCs], Acc) ->
    Defs = [ maps:get(X, Funs) || X <- Xs ],
    {TypeSigs, Defs1} = infer_letrec(Env, Defs),
    Env1 = bind_funs(TypeSigs, Env),
    check_sccs(Env1, Funs, SCCs, Defs1 ++ Acc).

check_reserved_entrypoints(Funs) ->
    Reserved = ["address"],
    _ = [ type_error({reserved_entrypoint, Name, Def})
            || {Name, Def} <- maps:to_list(Funs), lists:member(Name, Reserved) ],
    ok.

-spec check_fundecl(env(), aeso_syntax:decl()) -> {{name(), typesig()}, aeso_syntax:decl()}.
check_fundecl(Env, {fun_decl, Ann, Id = {id, _, Name}, Type = {fun_t, _, _, _, _}}) ->
    Type1 = {fun_t, _, Named, Args, Ret} = check_type(Env, Type),
    {{Name, {type_sig, Ann, none, Named, Args, Ret}}, {fun_decl, Ann, Id, Type1}};
check_fundecl(Env, {fun_decl, Ann, Id = {id, _, Name}, Type}) ->
    type_error({fundecl_must_have_funtype, Ann, Id, Type}),
    {{Name, {type_sig, Ann, none, [], [], Type}}, check_type(Env, Type)}.

infer_nonrec(Env, LetFun) ->
    create_constraints(),
    NewLetFun = infer_letfun(Env, LetFun),
    check_special_funs(Env, NewLetFun),
    destroy_and_report_unsolved_constraints(Env),
    Result = {TypeSig, _} = instantiate(NewLetFun),
    print_typesig(TypeSig),
    Result.

%% Currenty only the init function.
check_special_funs(Env, {{"init", Type}, _}) ->
    {type_sig, Ann, _Constr, _Named, _Args, Res} = Type,
    State =
        %% We might have implicit (no) state.
        case lookup_type(Env, {id, [], "state"}) of
            false  -> {tuple_t, [{origin, system}], []};
            {S, _} -> {qid, [], S}
        end,
    unify(Env, Res, State, {checking_init_type, Ann});
check_special_funs(_, _) -> ok.

typesig_to_fun_t({type_sig, Ann, _Constr, Named, Args, Res}) ->
    {fun_t, Ann, Named, Args, Res}.

infer_letrec(Env, Defs) ->
    create_constraints(),
    Funs = lists:map(fun({letfun, _, {id, Ann, Name}, _, _, _})   -> {Name, fresh_uvar(Ann)};
                        ({fun_clauses, _, {id, Ann, Name}, _, _}) -> {Name, fresh_uvar(Ann)}
                     end, Defs),
    ExtendEnv = bind_funs(Funs, Env),
    Inferred =
        [ begin
            Res    = {{Name, TypeSig}, _} = infer_letfun(ExtendEnv, LF),
            Got    = proplists:get_value(Name, Funs),
            Expect = typesig_to_fun_t(TypeSig),
            unify(Env, Got, Expect, {check_typesig, Name, Got, Expect}),
            solve_field_constraints(Env),
            ?PRINT_TYPES("Checked ~s : ~s\n",
                         [Name, pp(dereference_deep(Got))]),
            Res
          end || LF <- Defs ],
    destroy_and_report_unsolved_constraints(Env),
    TypeSigs = instantiate([Sig || {Sig, _} <- Inferred]),
    NewDefs  = instantiate([D || {_, D} <- Inferred]),
    [print_typesig(S) || S <- TypeSigs],
    {TypeSigs, NewDefs}.

infer_letfun(Env, {fun_clauses, Ann, Fun = {id, _, Name}, Type, Clauses}) ->
    Type1 = check_type(Env, Type),
    {NameSigs, Clauses1} = lists:unzip([ infer_letfun1(Env, Clause) || Clause <- Clauses ]),
    {_, Sigs = [Sig | _]} = lists:unzip(NameSigs),
    _ = [ begin
            ClauseT = typesig_to_fun_t(ClauseSig),
            unify(Env, ClauseT, Type1, {check_typesig, Name, ClauseT, Type1})
          end || ClauseSig <- Sigs ],
    {{Name, Sig}, desugar_clauses(Ann, Fun, Sig, Clauses1)};
infer_letfun(Env, LetFun = {letfun, Ann, Fun, _, _, _}) ->
    {{Name, Sig}, Clause} = infer_letfun1(Env, LetFun),
    {{Name, Sig}, desugar_clauses(Ann, Fun, Sig, [Clause])}.

infer_letfun1(Env0, {letfun, Attrib, Fun = {id, NameAttrib, Name}, Args, What, Body}) ->
    Env = Env0#env{ stateful = aeso_syntax:get_ann(stateful, Attrib, false),
                    current_function = Fun },
    {NewEnv, {typed, _, {tuple, _, TypedArgs}, {tuple_t, _, ArgTypes}}} = infer_pattern(Env, {tuple, [{origin, system} | NameAttrib], Args}),
    ExpectedType = check_type(Env, arg_type(NameAttrib, What)),
    NewBody={typed, _, _, ResultType} = check_expr(NewEnv, Body, ExpectedType),
    NamedArgs = [],
    TypeSig = {type_sig, Attrib, none, NamedArgs, ArgTypes, ResultType},
    {{Name, TypeSig},
     {letfun, Attrib, {id, NameAttrib, Name}, TypedArgs, ResultType, NewBody}}.

desugar_clauses(Ann, Fun, {type_sig, _, _, _, ArgTypes, RetType}, Clauses) ->
    NeedDesugar =
        case Clauses of
            [{letfun, _, _, As, _, _}] -> lists:any(fun({typed, _, {id, _, _}, _}) -> false; (_) -> true end, As);
            _                          -> true
        end,
    case NeedDesugar of
        false -> [Clause] = Clauses, Clause;
        true  ->
            NoAnn = [{origin, system}],
            Args = [ {typed, NoAnn, {id, NoAnn, "x#" ++ integer_to_list(I)}, Type}
                     || {I, Type} <- indexed(1, ArgTypes) ],
            Tuple = fun([X]) -> X;
                       (As) -> {typed, NoAnn, {tuple, NoAnn, As}, {tuple_t, NoAnn, ArgTypes}}
                    end,
            {letfun, Ann, Fun, Args, RetType,
             {typed, NoAnn,
              {switch, NoAnn, Tuple(Args),
                [ {'case', AnnC, Tuple(ArgsC), Body}
                || {letfun, AnnC, _, ArgsC, _, Body} <- Clauses ]}, RetType}}
    end.

print_typesig({Name, TypeSig}) ->
    ?PRINT_TYPES("Inferred ~s : ~s\n", [Name, pp(TypeSig)]).

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

lookup_name(Env, As, Name) ->
    lookup_name(Env, As, Name, []).

lookup_name(Env, As, Id, Options) ->
    case lookup_env(Env, term, As, qname(Id)) of
        false ->
            type_error({unbound_variable, Id}),
            {Id, fresh_uvar(As)};
        {QId, {_, Ty}} ->
            Freshen = proplists:get_value(freshen, Options, false),
            check_stateful(Env, Id, Ty),
            Ty1 = case Ty of
                    {type_sig, _, _, _, _, _} -> freshen_type_sig(As, Ty);
                    _ when Freshen            -> freshen_type(As, Ty);
                    _                         -> Ty
                  end,
            {set_qname(QId, Id), Ty1}
    end.

check_stateful(#env{ stateful = false, current_function = Fun }, Id, Type = {type_sig, _, _, _, _, _}) ->
    case aeso_syntax:get_ann(stateful, Type, false) of
        false -> ok;
        true  ->
            type_error({stateful_not_allowed, Id, Fun})
    end;
check_stateful(_Env, _Id, _Type) -> ok.

%% Hack: don't allow passing the 'value' named arg if not stateful. This only
%% works since the user can't create functions with named arguments.
check_stateful_named_arg(#env{ stateful = false, current_function = Fun }, {id, _, "value"}, Default) ->
    case Default of
        {int, _, 0} -> ok;
        _           -> type_error({value_arg_not_allowed, Default, Fun})
    end;
check_stateful_named_arg(_, _, _) -> ok.

%% Check that `init` doesn't read or write the state
check_state_dependencies(Env, Defs) ->
    Top       = Env#env.namespace,
    GetState  = Top ++ ["state"],
    SetState  = Top ++ ["put"],
    Init      = Top ++ ["init"],
    UsedNames = fun(X) -> [{Xs, Ann} || {{term, Xs}, Ann} <- aeso_syntax_utils:used(X)] end,
    Funs      = [ {Top ++ [Name], Fun} || Fun = {letfun, _, {id, _, Name}, _Args, _Type, _Body} <- Defs ],
    Deps      = maps:from_list([{Name, UsedNames(Def)} || {Name, Def} <- Funs]),
    case maps:get(Init, Deps, false) of
        false -> ok;    %% No init, so nothing to check
        _     ->
            [ type_error({init_depends_on_state, state, Chain})
              || Chain <- get_call_chains(Deps, Init, GetState) ],
            [ type_error({init_depends_on_state, put, Chain})
              || Chain <- get_call_chains(Deps, Init, SetState) ],
            ok
    end.

%% Compute all paths (not sharing intermediate nodes) from Start to Stop in Graph.
get_call_chains(Graph, Start, Stop) ->
    get_call_chains(Graph, #{}, queue:from_list([{Start, [], []}]), Stop, []).

get_call_chains(Graph, Visited, Queue, Stop, Acc) ->
    case queue:out(Queue) of
        {empty, _} -> lists:reverse(Acc);
        {{value, {Stop, Ann, Path}}, Queue1} ->
            get_call_chains(Graph, Visited, Queue1, Stop, [lists:reverse([{Stop, Ann} | Path]) | Acc]);
        {{value, {Node, Ann, Path}}, Queue1} ->
            case maps:is_key(Node, Visited) of
                true  -> get_call_chains(Graph, Visited, Queue1, Stop, Acc);
                false ->
                    Calls = maps:get(Node, Graph, []),
                    NewQ  = queue:from_list([{New, Ann1, [{Node, Ann} | Path]} || {New, Ann1} <- Calls]),
                    get_call_chains(Graph, Visited#{Node => true}, queue:join(Queue1, NewQ), Stop, Acc)
            end
    end.

check_expr(Env, Expr, Type) ->
    {typed, Ann, Expr1, Type1} = infer_expr(Env, Expr),
    unify(Env, Type1, Type, {check_expr, Expr, Type1, Type}),
    {typed, Ann, Expr1, Type}.  %% Keep the user-given type

infer_expr(_Env, Body={bool, As, _}) ->
    {typed, As, Body, {id, As, "bool"}};
infer_expr(_Env, Body={int, As, _}) ->
    {typed, As, Body, {id, As, "int"}};
infer_expr(_Env, Body={char, As, _}) ->
    {typed, As, Body, {id, As, "char"}};
infer_expr(_Env, Body={string, As, _}) ->
    {typed, As, Body, {id, As, "string"}};
infer_expr(_Env, Body={bytes, As, Bin}) ->
    {typed, As, Body, {bytes_t, As, byte_size(Bin)}};
infer_expr(_Env, Body={account_pubkey, As, _}) ->
    {typed, As, Body, {id, As, "address"}};
infer_expr(_Env, Body={oracle_pubkey, As, _}) ->
    Q = fresh_uvar(As),
    R = fresh_uvar(As),
    {typed, As, Body, {app_t, As, {id, As, "oracle"}, [Q, R]}};
infer_expr(_Env, Body={oracle_query_id, As, _}) ->
    Q = fresh_uvar(As),
    R = fresh_uvar(As),
    {typed, As, Body, {app_t, As, {id, As, "oracle_query"}, [Q, R]}};
infer_expr(_Env, Body={contract_pubkey, As, _}) ->
    Con = fresh_uvar(As),
    constrain([#is_contract_constraint{ contract_t = Con,
                                        context    = {contract_literal, Body} }]),
    {typed, As, Body, Con};
infer_expr(_Env, Body={id, As, "_"}) ->
    {typed, As, Body, fresh_uvar(As)};
infer_expr(Env, Id = {Tag, As, _}) when Tag == id; Tag == qid ->
    {QName, Type} = lookup_name(Env, As, Id),
    {typed, As, QName, Type};
infer_expr(Env, Id = {Tag, As, _}) when Tag == con; Tag == qcon ->
    {QName, Type} = lookup_name(Env, As, Id, [freshen]),
    {typed, As, QName, Type};
infer_expr(Env, {tuple, As, Cpts}) ->
    NewCpts = [infer_expr(Env, C) || C <- Cpts],
    CptTypes = [T || {typed, _, _, T} <- NewCpts],
    {typed, As, {tuple, As, NewCpts}, {tuple_t, As, CptTypes}};
infer_expr(Env, {list, As, Elems}) ->
    ElemType = fresh_uvar(As),
    NewElems = [check_expr(Env, X, ElemType) || X <- Elems],
    {typed, As, {list, As, NewElems}, {app_t, As, {id, As, "list"}, [ElemType]}};
infer_expr(Env, {list_comp, As, Yield, []}) ->
    {typed, _, _, Type} = TypedYield = infer_expr(Env, Yield),
    {typed, As, {list_comp, As, TypedYield, []}, {app_t, As, {id, As, "list"}, [Type]}};
infer_expr(Env, {list_comp, As, Yield, [{comprehension_bind, Pat, BExpr}|Rest]}) ->
    TypedBind = {typed, As2, _, TypeBExpr} = infer_expr(Env, BExpr),
    {NewE, TypedPat = {typed, _, _, PatType}} = infer_pattern(Env, Pat),
    unify( Env
         , TypeBExpr
         , {app_t, As, {id, As, "list"}, [PatType]}
         , {list_comp, TypedBind, TypeBExpr, {app_t, As2, {id, As, "list"}, [PatType]}}),
    {typed, _, {list_comp, _, TypedYield, TypedRest}, ResType} =
        infer_expr(NewE, {list_comp, As, Yield, Rest}),
    { typed
    , As
    , {list_comp, As, TypedYield, [{comprehension_bind, TypedPat, TypedBind}|TypedRest]}
    , ResType};
infer_expr(Env, {list_comp, AttrsL, Yield, [{comprehension_if, AttrsIF, Cond}|Rest]}) ->
    NewCond = check_expr(Env, Cond, {id, AttrsIF, "bool"}),
    {typed, _, {list_comp, _, TypedYield, TypedRest}, ResType} =
        infer_expr(Env, {list_comp, AttrsL, Yield, Rest}),
    { typed
    , AttrsL
    , {list_comp, AttrsL, TypedYield, [{comprehension_if, AttrsIF, NewCond}|TypedRest]}
    , ResType};
infer_expr(Env, {list_comp, AsLC, Yield, [{letval, AsLV, Pattern, E}|Rest]}) ->
    NewE = {typed, _, _, PatType} = infer_expr(Env, E),
    BlockType = fresh_uvar(AsLV),
    {'case', _, NewPattern, NewRest} =
        infer_case( Env
                  , AsLC
                  , Pattern
                  , PatType
                  , {list_comp, AsLC, Yield, Rest}
                  , BlockType),
    {typed, _, {list_comp, _, TypedYield, TypedRest}, ResType} = NewRest,
    { typed
    , AsLC
    , {list_comp, AsLC, TypedYield, [{letval, AsLV, NewPattern, NewE}|TypedRest]}
    , ResType
    };
infer_expr(Env, {list_comp, AsLC, Yield, [Def={letfun, AsLF, _, _, _, _}|Rest]}) ->
    {{Name, TypeSig}, LetFun} = infer_letfun(Env, Def),
    FunT = typesig_to_fun_t(TypeSig),
    NewE = bind_var({id, AsLF, Name}, FunT, Env),
    {typed, _, {list_comp, _, TypedYield, TypedRest}, ResType} =
        infer_expr(NewE, {list_comp, AsLC, Yield, Rest}),
    { typed
    , AsLC
    , {list_comp, AsLC, TypedYield, [LetFun|TypedRest]}
    , ResType
    };
infer_expr(Env, {typed, As, Body, Type}) ->
    Type1 = check_type(Env, Type),
    {typed, _, NewBody, NewType} = check_expr(Env, Body, Type1),
    {typed, As, NewBody, NewType};
infer_expr(Env, {app, Ann, Fun, Args0} = App) ->
    {NamedArgs, Args} = split_args(Args0),
    case aeso_syntax:get_ann(format, Ann) of
        infix ->
            infer_op(Env, Ann, Fun, Args, fun infer_infix/1);
        prefix ->
            infer_op(Env, Ann, Fun, Args, fun infer_prefix/1);
        _ ->
            NamedArgsVar = fresh_uvar(Ann),
            NamedArgs1 = [ infer_named_arg(Env, NamedArgsVar, Arg) || Arg <- NamedArgs ],
            NewFun0 = infer_expr(Env, Fun),
            NewArgs = [infer_expr(Env, A) || A <- Args],
            ArgTypes = [T || {typed, _, _, T} <- NewArgs],
            NewFun1 = {typed, _, _, FunType} = infer_var_args_fun(Env, NewFun0, NamedArgs1, ArgTypes),
            When = {infer_app, Fun, NamedArgs1, Args, FunType, ArgTypes},
            GeneralResultType = fresh_uvar(Ann),
            ResultType = fresh_uvar(Ann),
            unify(Env, FunType, {fun_t, [], NamedArgsVar, ArgTypes, GeneralResultType}, When),
            add_named_argument_constraint(
              #dependent_type_constraint{ named_args_t = NamedArgsVar,
                                          named_args   = NamedArgs1,
                                          general_type = GeneralResultType,
                                          specialized_type = ResultType,
                                          context = {check_return, App} }),
            {typed, Ann, {app, Ann, NewFun1, NamedArgs1 ++ NewArgs}, dereference(ResultType)}
    end;
infer_expr(Env, {'if', Attrs, Cond, Then, Else}) ->
    NewCond = check_expr(Env, Cond, {id, Attrs, "bool"}),
    NewThen = {typed, _, _, ThenType} = infer_expr(Env, Then),
    NewElse = {typed, _, _, ElseType} = infer_expr(Env, Else),
    unify(Env, ThenType, ElseType, {if_branches, Then, ThenType, Else, ElseType}),
    {typed, Attrs, {'if', Attrs, NewCond, NewThen, NewElse}, ThenType};
infer_expr(Env, {switch, Attrs, Expr, Cases}) ->
    NewExpr = {typed, _, _, ExprType} = infer_expr(Env, Expr),
    SwitchType = fresh_uvar(Attrs),
    NewCases = [infer_case(Env, As, Pattern, ExprType, Branch, SwitchType)
                || {'case', As, Pattern, Branch} <- Cases],
    {typed, Attrs, {switch, Attrs, NewExpr, NewCases}, SwitchType};
infer_expr(Env, {record, Attrs, Fields}) ->
    RecordType = fresh_uvar(Attrs),
    NewFields = [{field, A, FieldName, infer_expr(Env, Expr)}
                 || {field, A, FieldName, Expr} <- Fields],
    RecordType1 = unfold_types_in_type(Env, RecordType),
    constrain([ #record_create_constraint{
                    record_t = RecordType1,
                    fields   = [ FieldName || {field, _, [{proj, _, FieldName}], _} <- Fields ],
                    context  = Attrs } || not Env#env.in_pattern ] ++
              [begin
                [{proj, _, FieldName}] = LV,
                #field_constraint{
                    record_t = RecordType1,
                    field    = FieldName,
                    field_t  = T,
                    kind     = create,
                    context  = Fld}
               end || {Fld, {field, _, LV, {typed, _, _, T}}} <- lists:zip(Fields, NewFields)]),
    {typed, Attrs, {record, Attrs, NewFields}, RecordType};
infer_expr(Env, {record, Attrs, Record, Update}) ->
    NewRecord = {typed, _, _, RecordType} = infer_expr(Env, Record),
    NewUpdate = [ check_record_update(Env, RecordType, Fld) || Fld <- Update ],
    {typed, Attrs, {record, Attrs, NewRecord, NewUpdate}, RecordType};
infer_expr(Env, {proj, Attrs, Record, FieldName}) ->
    NewRecord = {typed, _, _, RecordType} = infer_expr(Env, Record),
    FieldType = fresh_uvar(Attrs),
    constrain([#field_constraint{
        record_t = unfold_types_in_type(Env, RecordType),
        field    = FieldName,
        field_t  = FieldType,
        kind     = project,
        context  = {proj, Attrs, Record, FieldName} }]),
    {typed, Attrs, {proj, Attrs, NewRecord, FieldName}, FieldType};
%% Maps
infer_expr(Env, {map_get, Attrs, Map, Key}) ->  %% map lookup
    KeyType = fresh_uvar(Attrs),
    ValType = fresh_uvar(Attrs),
    MapType = map_t(Attrs, KeyType, ValType),
    Map1 = check_expr(Env, Map, MapType),
    Key1 = check_expr(Env, Key, KeyType),
    {typed, Attrs, {map_get, Attrs, Map1, Key1}, ValType};
infer_expr(Env, {map_get, Attrs, Map, Key, Val}) ->  %% map lookup with default
    KeyType = fresh_uvar(Attrs),
    ValType = fresh_uvar(Attrs),
    MapType = map_t(Attrs, KeyType, ValType),
    Map1 = check_expr(Env, Map, MapType),
    Key1 = check_expr(Env, Key, KeyType),
    Val1 = check_expr(Env, Val, ValType),
    {typed, Attrs, {map_get, Attrs, Map1, Key1, Val1}, ValType};
infer_expr(Env, {map, Attrs, KVs}) ->   %% map construction
    KeyType = fresh_uvar(Attrs),
    ValType = fresh_uvar(Attrs),
    KVs1 = [ {check_expr(Env, K, KeyType), check_expr(Env, V, ValType)}
             || {K, V} <- KVs ],
    {typed, Attrs, {map, Attrs, KVs1}, map_t(Attrs, KeyType, ValType)};
infer_expr(Env, {map, Attrs, Map, Updates}) -> %% map update
    KeyType  = fresh_uvar(Attrs),
    ValType  = fresh_uvar(Attrs),
    MapType  = map_t(Attrs, KeyType, ValType),
    Map1     = check_expr(Env, Map, MapType),
    Updates1 = [ check_map_update(Env, Upd, KeyType, ValType) || Upd <- Updates ],
    {typed, Attrs, {map, Attrs, Map1, Updates1}, MapType};
infer_expr(Env, {block, Attrs, Stmts}) ->
    BlockType = fresh_uvar(Attrs),
    NewStmts = infer_block(Env, Attrs, Stmts, BlockType),
    {typed, Attrs, {block, Attrs, NewStmts}, BlockType};
infer_expr(_Env, {record_or_map_error, Attrs, Fields}) ->
    type_error({mixed_record_and_map, {record, Attrs, Fields}}),
    Type = fresh_uvar(Attrs),
    {typed, Attrs, {record, Attrs, []}, Type};
infer_expr(Env, {record_or_map_error, Attrs, Expr, []}) ->
    type_error({empty_record_or_map_update, {record, Attrs, Expr, []}}),
    infer_expr(Env, Expr);
infer_expr(Env, {record_or_map_error, Attrs, Expr, Fields}) ->
    type_error({mixed_record_and_map, {record, Attrs, Expr, Fields}}),
    infer_expr(Env, Expr);
infer_expr(Env, {lam, Attrs, Args, Body}) ->
    ArgTypes = [fresh_uvar(As) || {arg, As, _, _} <- Args],
    ArgPatterns = [{typed, As, Pat, check_type(Env, T)} || {arg, As, Pat, T} <- Args],
    ResultType = fresh_uvar(Attrs),
    {'case', _, {typed, _, {tuple, _, NewArgPatterns}, _}, NewBody} =
        infer_case(Env, Attrs, {tuple, Attrs, ArgPatterns}, {tuple_t, Attrs, ArgTypes}, Body, ResultType),
    NewArgs = [{arg, As, NewPat, NewT} || {typed, As, NewPat, NewT} <- NewArgPatterns],
    {typed, Attrs, {lam, Attrs, NewArgs, NewBody}, {fun_t, Attrs, [], ArgTypes, ResultType}};
infer_expr(Env, Let = {letval, Attrs, _, _}) ->
    type_error({missing_body_for_let, Attrs}),
    infer_expr(Env, {block, Attrs, [Let, abort_expr(Attrs, "missing body")]});
infer_expr(Env, Let = {letfun, Attrs, _, _, _, _}) ->
    type_error({missing_body_for_let, Attrs}),
    infer_expr(Env, {block, Attrs, [Let, abort_expr(Attrs, "missing body")]}).

infer_var_args_fun(Env, {typed, Ann, Fun, FunType0}, NamedArgs, ArgTypes) ->
    FunType =
        case Fun of
            {qid, _, ["Chain", "create"]} ->
                {fun_t, _, NamedArgsT, var_args, RetT} = FunType0,
                GasCapMock    = {named_arg_t, Ann, {id, Ann, "gas"}, {id, Ann, "int"}, {int, Ann, 0}},
                ProtectedMock = {named_arg_t, Ann, {id, Ann, "protected"}, {id, Ann, "bool"}, {bool, Ann, false}},
                NamedArgsT1 = case NamedArgsT of
                                  [Value|Rest] -> [GasCapMock, Value, ProtectedMock|Rest];
                                  % generally type error, but will be caught
                                  _ -> [GasCapMock, ProtectedMock|NamedArgsT]
                              end,
                check_contract_construction(Env, true, RetT, Fun, NamedArgsT1, ArgTypes, RetT),
                {fun_t, Ann, NamedArgsT, ArgTypes, RetT};
            {qid, _, ["Chain", "clone"]} ->
                {fun_t, _, NamedArgsT, var_args, RetT} = FunType0,
                ContractT =
                    case [ContractT || {named_arg, _, {id, _, "ref"}, {typed, _, _, ContractT}} <- NamedArgs] of
                        [C] -> C;
                        _ -> type_error({clone_no_contract, Ann}),
                             fresh_uvar(Ann)
                    end,
                NamedArgsTNoRef =
                    lists:filter(fun({named_arg_t, _, {id, _, "ref"}, _, _}) -> false; (_) -> true end, NamedArgsT),
                check_contract_construction(Env, false, ContractT, Fun, NamedArgsTNoRef, ArgTypes, RetT),
                {fun_t, Ann, NamedArgsT, ArgTypes,
                 {if_t, Ann, {id, Ann, "protected"}, {app_t, Ann, {id, Ann, "option"}, [RetT]}, RetT}};
            _ -> FunType0
        end,
    {typed, Ann, Fun, FunType}.

-spec check_contract_construction(env(), boolean(), utype(), utype(), named_args_t(), [utype()], utype()) -> ok.
check_contract_construction(Env, ForceDef, ContractT, Fun, NamedArgsT, ArgTypes, RetT) ->
    Ann = aeso_syntax:get_ann(Fun),
    InitT = fresh_uvar(Ann),
    unify(Env, InitT, {fun_t, Ann, NamedArgsT, ArgTypes, fresh_uvar(Ann)}, {checking_init_args, Ann, ContractT, ArgTypes}),
    unify(Env, RetT, ContractT, {return_contract, Fun, ContractT}),
    constrain(
      [ #field_constraint{
           record_t = unfold_types_in_type(Env, ContractT),
           field    = {id, Ann, ?CONSTRUCTOR_MOCK_NAME},
           field_t  = InitT,
           kind     = project,
           context  = {var_args, Ann, Fun} }
      , #is_contract_constraint{ contract_t = ContractT,
                                 context    = {var_args, Ann, Fun},
                                 force_def  = ForceDef
                               }
      ]),
    ok.

split_args(Args0) ->
    NamedArgs = [ Arg || Arg = {named_arg, _, _, _} <- Args0 ],
    Args      = Args0 -- NamedArgs,
    {NamedArgs, Args}.

infer_named_arg(Env, NamedArgs, {named_arg, Ann, Id, E}) ->
    CheckedExpr = {typed, _, _, ArgType} = infer_expr(Env, E),
    check_stateful_named_arg(Env, Id, E),
    add_named_argument_constraint(
        #named_argument_constraint{
            args = NamedArgs,
            name = Id,
            type = ArgType }),
    {named_arg, Ann, Id, CheckedExpr}.

check_map_update(Env, {field, Ann, [{map_get, Ann1, Key}], Val}, KeyType, ValType) ->
    Key1 = check_expr(Env, Key, KeyType),
    Val1 = check_expr(Env, Val, ValType),
    {field, Ann, [{map_get, Ann1, Key1}], Val1};
check_map_update(_Env, Upd={field, _Ann, [{map_get, _Ann1, _Key, _Def}], _Val}, _KeyType, _ValType) ->
    type_error({unnamed_map_update_with_default, Upd});
check_map_update(Env, {field, Ann, [{map_get, Ann1, Key}], Id, Val}, KeyType, ValType) ->
    FunType = {fun_t, Ann, [], [ValType], ValType},
    Key1    = check_expr(Env, Key, KeyType),
    Fun     = check_expr(Env, {lam, Ann1, [{arg, Ann1, Id, ValType}], Val}, FunType),
    {field_upd, Ann, [{map_get, Ann1, Key1}], Fun};
check_map_update(Env, {field, Ann, [{map_get, Ann1, Key, Def}], Id, Val}, KeyType, ValType) ->
    FunType = {fun_t, Ann, [], [ValType], ValType},
    Key1    = check_expr(Env, Key, KeyType),
    Def1    = check_expr(Env, Def, ValType),
    Fun     = check_expr(Env, {lam, Ann1, [{arg, Ann1, Id, ValType}], Val}, FunType),
    {field_upd, Ann, [{map_get, Ann1, Key1, Def1}], Fun};
check_map_update(_, {field, Ann, Flds, _}, _, _) ->
    error({nested_map_updates_not_implemented, Ann, Flds}).

check_record_update(Env, RecordType, Fld) ->
    [field, Ann, LV = [{proj, Ann1, FieldName}] | Val] = tuple_to_list(Fld),
    FldType = fresh_uvar(Ann),
    Fld1 = case Val of
            [Expr] ->
                {field, Ann, LV, check_expr(Env, Expr, FldType)};
            [Id, Expr] ->
                Fun     = {lam, Ann1, [{arg, Ann1, Id, FldType}], Expr},
                FunType = {fun_t, Ann1, [], [FldType], FldType},
                {field_upd, Ann, LV, check_expr(Env, Fun, FunType)}
        end,
    constrain([#field_constraint{
        record_t = unfold_types_in_type(Env, RecordType),
        field    = FieldName,
        field_t  = FldType,
        kind     = update,
        context  = Fld }]),
    Fld1.

infer_op(Env, As, Op, Args, InferOp) ->
    TypedArgs = [infer_expr(Env, A) || A <- Args],
    ArgTypes = [T || {typed, _, _, T} <- TypedArgs],
    Inferred = {fun_t, _, _, OperandTypes, ResultType} = InferOp(Op),
    unify(Env, ArgTypes, OperandTypes, {infer_app, Op, [], Args, Inferred, ArgTypes}),
    {typed, As, {app, As, Op, TypedArgs}, ResultType}.

infer_pattern(Env, Pattern) ->
    Vars = free_vars(Pattern),
    Names = [N || {id, _, N} <- Vars, N /= "_"],
    case Names -- lists:usort(Names) of
        [] -> ok;
        Nonlinear -> type_error({non_linear_pattern, Pattern, lists:usort(Nonlinear)})
    end,
    NewEnv = bind_vars([{Var, fresh_uvar(Ann1)} || Var = {id, Ann1, _} <- Vars], Env#env{ in_pattern = true }),
    NewPattern = infer_expr(NewEnv, Pattern),
    {NewEnv#env{ in_pattern = Env#env.in_pattern }, NewPattern}.

infer_case(Env, Attrs, Pattern, ExprType, Branch, SwitchType) ->
    {NewEnv, NewPattern = {typed, _, _, PatType}} = infer_pattern(Env, Pattern),
    NewBranch  = check_expr(NewEnv#env{ in_pattern = false }, Branch, SwitchType),
    unify(Env, PatType, ExprType, {case_pat, Pattern, PatType, ExprType}),
    {'case', Attrs, NewPattern, NewBranch}.

%% NewStmts = infer_block(Env, Attrs, Stmts, BlockType)
infer_block(_Env, Attrs, [], BlockType) ->
    error({impossible, empty_block, Attrs, BlockType});
infer_block(Env, _, [E], BlockType) ->
    [check_expr(Env, E, BlockType)];
infer_block(Env, Attrs, [Def={letfun, Ann, _, _, _, _}|Rest], BlockType) ->
    {{Name, TypeSig}, LetFun} = infer_letfun(Env, Def),
    FunT = typesig_to_fun_t(TypeSig),
    NewE = bind_var({id, Ann, Name}, FunT, Env),
    [LetFun|infer_block(NewE, Attrs, Rest, BlockType)];
infer_block(Env, _, [{letval, Attrs, Pattern, E}|Rest], BlockType) ->
    NewE = {typed, _, _, PatType} = infer_expr(Env, E),
    {'case', _, NewPattern, {typed, _, {block, _, NewRest}, _}} =
        infer_case(Env, Attrs, Pattern, PatType, {block, Attrs, Rest}, BlockType),
    [{letval, Attrs, NewPattern, NewE}|NewRest];
infer_block(Env, Attrs, [Using = {using, _, _} | Rest], BlockType) ->
    infer_block(check_usings(Env, [Using]), Attrs, Rest, BlockType);
infer_block(Env, Attrs, [Using = {using, _, _, _} | Rest], BlockType) ->
    infer_block(check_usings(Env, [Using]), Attrs, Rest, BlockType);
infer_block(Env, Attrs, [E|Rest], BlockType) ->
    [infer_expr(Env, E)|infer_block(Env, Attrs, Rest, BlockType)].

infer_infix({BoolOp, As})
  when BoolOp =:= '&&'; BoolOp =:= '||' ->
    Bool = {id, As, "bool"},
    {fun_t, As, [], [Bool,Bool], Bool};
infer_infix({IntOp, As})
  when IntOp == '+';    IntOp == '-';   IntOp == '*';   IntOp == '/';
       IntOp == '^';    IntOp == 'mod' ->
    Int = {id, As, "int"},
    {fun_t, As, [], [Int, Int], Int};
infer_infix({RelOp, As})
  when RelOp == '=='; RelOp == '!=';
       RelOp == '<';  RelOp == '>';
       RelOp == '<='; RelOp == '=<'; RelOp == '>=' ->
    T = fresh_uvar(As),     %% allow any type here, check in ast_to_icode that we have comparison for it
    Bool = {id, As, "bool"},
    {fun_t, As, [], [T, T], Bool};
infer_infix({'..', As}) ->
    Int = {id, As, "int"},
    {fun_t, As, [], [Int, Int], {app_t, As, {id, As, "list"}, [Int]}};
infer_infix({'::', As}) ->
    ElemType = fresh_uvar(As),
    ListType = {app_t, As, {id, As, "list"}, [ElemType]},
    {fun_t, As, [], [ElemType, ListType], ListType};
infer_infix({'++', As}) ->
    ElemType = fresh_uvar(As),
    ListType = {app_t, As, {id, As, "list"}, [ElemType]},
    {fun_t, As, [], [ListType, ListType], ListType}.

infer_prefix({'!',As}) ->
    Bool = {id, As, "bool"},
    {fun_t, As, [], [Bool], Bool};
infer_prefix({IntOp,As}) when IntOp =:= '-' ->
    Int = {id, As, "int"},
    {fun_t, As, [], [Int], Int}.

abort_expr(Ann, Str) ->
    {app, Ann, {id, Ann, "abort"}, [{string, Ann, Str}]}.

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
free_vars(L) when is_list(L) ->
    [V || Elem <- L,
          V <- free_vars(Elem)].

next_count() ->
    V = case get(counter) of
            undefined ->
                0;
            X -> X
        end,
    put(counter, V + 1),
    V.

%% Clean up all the ets tables (in case of an exception)

ets_tables() ->
    [options, type_vars, type_defs, record_fields, named_argument_constraints,
     field_constraints, freshen_tvars, type_errors, defined_contracts].

clean_up_ets() ->
    [ catch ets_delete(Tab) || Tab <- ets_tables() ],
    ok.

%% Named interface to ETS tables implemented without names.
%% The interface functions behave as the standard ETS interface.

ets_init() ->
    put(aeso_ast_infer_types, #{}).

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

ets_insert(Name, Object) ->
    TabId = ets_tabid(Name),
    ets:insert(TabId, Object).

ets_lookup(Name, Key) ->
    TabId = ets_tabid(Name),
    ets:lookup(TabId, Key).

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
    create_named_argument_constraints(),
    create_bytes_constraints(),
    create_field_constraints().

destroy_and_report_unsolved_constraints(Env) ->
    solve_field_constraints(Env),
    solve_named_argument_constraints(Env),
    solve_bytes_constraints(Env),
    destroy_and_report_unsolved_bytes_constraints(Env),
    destroy_and_report_unsolved_named_argument_constraints(Env),
    destroy_and_report_unsolved_field_constraints(Env).

%% -- Named argument constraints --

create_named_argument_constraints() ->
    ets_new(named_argument_constraints, [ordered_set]).

destroy_named_argument_constraints() ->
    ets_delete(named_argument_constraints).

get_named_argument_constraints() ->
    ets_tab2list_ordered(named_argument_constraints).

-spec add_named_argument_constraint(named_argument_constraint()) -> ok.
add_named_argument_constraint(Constraint) ->
    ets_insert_ordered(named_argument_constraints, Constraint),
    ok.

solve_named_argument_constraints(Env) ->
    Unsolved = solve_named_argument_constraints(Env, get_named_argument_constraints()),
    Unsolved == [].

-spec solve_named_argument_constraints(env(), [named_argument_constraint()]) -> [named_argument_constraint()].
solve_named_argument_constraints(Env, Constraints0) ->
    [ C || C <- dereference_deep(Constraints0),
           unsolved == check_named_argument_constraint(Env, C) ].

%% If false, a type error has been emitted, so it's safe to drop the constraint.
-spec check_named_argument_constraint(env(), named_argument_constraint()) -> true | false | unsolved.
check_named_argument_constraint(_Env, #named_argument_constraint{ args = {uvar, _, _} }) ->
    unsolved;
check_named_argument_constraint(Env,
        C = #named_argument_constraint{ args = Args,
                                        name = Id = {id, _, Name},
                                        type = Type }) ->
    case [ T || {named_arg_t, _, {id, _, Name1}, T, _} <- Args, Name1 == Name ] of
        []  ->
            type_error({bad_named_argument, Args, Id}),
            false;
        [T] -> unify(Env, T, Type, {check_named_arg_constraint, C}), true
    end;
check_named_argument_constraint(Env,
        #dependent_type_constraint{ named_args_t = NamedArgsT0,
                                    named_args = NamedArgs,
                                    general_type = GenType,
                                    specialized_type = SpecType,
                                    context = {check_return, App} }) ->
    NamedArgsT = dereference(NamedArgsT0),
    case dereference(NamedArgsT0) of
        [_ | _] = NamedArgsT ->
            GetVal = fun(Name, Default) ->
                        hd([ Val || {named_arg, _, {id, _, N}, Val} <- NamedArgs, N == Name] ++
                           [ Default ])
                     end,
            ArgEnv = maps:from_list([ {Name, GetVal(Name, Default)}
                                      || {named_arg_t, _, {id, _, Name}, _, Default} <- NamedArgsT ]),
            GenType1 = specialize_dependent_type(ArgEnv, GenType),
            unify(Env, GenType1, SpecType, {check_expr, App, GenType1, SpecType}),
            true;
        _ -> unify(Env, GenType, SpecType, {check_expr, App, GenType, SpecType}), true
    end.

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


destroy_and_report_unsolved_named_argument_constraints(Env) ->
    Unsolved = solve_named_argument_constraints(Env, get_named_argument_constraints()),
    [ type_error({unsolved_named_argument_constraint, C}) || C <- Unsolved ],
    destroy_named_argument_constraints(),
    ok.

%% -- Bytes constraints --

-type byte_constraint() :: {is_bytes, utype()}
                         | {add_bytes, aeso_syntax:ann(), concat | split, utype(), utype(), utype()}.

create_bytes_constraints() ->
    ets_new(bytes_constraints, [ordered_set]).

get_bytes_constraints() ->
    ets_tab2list_ordered(bytes_constraints).

-spec add_bytes_constraint(byte_constraint()) -> true.
add_bytes_constraint(Constraint) ->
    ets_insert_ordered(bytes_constraints, Constraint).

solve_bytes_constraints(Env) ->
    [ solve_bytes_constraint(Env, C) || C <- get_bytes_constraints() ],
    ok.

solve_bytes_constraint(_Env, {is_bytes, _}) -> ok;
solve_bytes_constraint(Env, {add_bytes, Ann, _, A0, B0, C0}) ->
    A = unfold_types_in_type(Env, dereference(A0)),
    B = unfold_types_in_type(Env, dereference(B0)),
    C = unfold_types_in_type(Env, dereference(C0)),
    case {A, B, C} of
        {{bytes_t, _, M}, {bytes_t, _, N}, _} -> unify(Env, {bytes_t, Ann, M + N}, C, {at, Ann});
        {{bytes_t, _, M}, _, {bytes_t, _, R}} when R >= M -> unify(Env, {bytes_t, Ann, R - M}, B, {at, Ann});
        {_, {bytes_t, _, N}, {bytes_t, _, R}} when R >= N -> unify(Env, {bytes_t, Ann, R - N}, A, {at, Ann});
        _ -> ok
    end.

destroy_bytes_constraints() ->
    ets_delete(bytes_constraints).

destroy_and_report_unsolved_bytes_constraints(Env) ->
    Constraints     = get_bytes_constraints(),
    InAddConstraint = [ T || {add_bytes, _, _, A, B, C} <- Constraints,
                             T <- [A, B, C],
                             element(1, T) /= bytes_t ],
    %% Skip is_bytes constraints for types that occur in add_bytes constraints
    %% (no need to generate error messages for both is_bytes and add_bytes).
    Skip = fun({is_bytes, T}) -> lists:member(T, InAddConstraint);
              (_) -> false end,
    [ check_bytes_constraint(Env, C) || C <- Constraints, not Skip(C) ],
    destroy_bytes_constraints().

check_bytes_constraint(Env, {is_bytes, Type}) ->
    Type1 = unfold_types_in_type(Env, instantiate(Type)),
    case Type1 of
        {bytes_t, _, _} -> ok;
        _               ->
            type_error({unknown_byte_length, Type})
    end;
check_bytes_constraint(Env, {add_bytes, Ann, Fun, A0, B0, C0}) ->
    A = unfold_types_in_type(Env, instantiate(A0)),
    B = unfold_types_in_type(Env, instantiate(B0)),
    C = unfold_types_in_type(Env, instantiate(C0)),
    case {A, B, C} of
        {{bytes_t, _, _M}, {bytes_t, _, _N}, {bytes_t, _, _R}} ->
            ok; %% If all are solved we checked M + N == R in solve_bytes_constraint.
        _ -> type_error({unsolved_bytes_constraint, Ann, Fun, A, B, C})
    end.

%% -- Field constraints --

create_field_constraints() ->
    %% A relation from uvars to constraints
    ets_new(field_constraints, [ordered_set]).

destroy_field_constraints() ->
    ets_delete(field_constraints).

-spec constrain([field_constraint()]) -> true.
constrain(FieldConstraints) ->
    ets_insert_ordered(field_constraints, FieldConstraints).

-spec get_field_constraints() -> [field_constraint()].
get_field_constraints() ->
    ets_tab2list_ordered(field_constraints).

solve_field_constraints(Env) ->
    FieldCs =
        lists:filter(fun(#field_constraint{}) -> true; (_) -> false end,
                        get_field_constraints()),
    solve_field_constraints(Env, FieldCs).

check_record_create_constraints(_, []) -> ok;
check_record_create_constraints(Env, [C | Cs]) ->
    #record_create_constraint{
        record_t = Type,
        fields   = Fields,
        context  = When } = C,
    Type1 = unfold_types_in_type(Env, instantiate(Type)),
    try lookup_type(Env, record_type_name(Type1)) of
        {_QId, {_Ann, {_Args, {record_t, RecFields}}}} ->
            ActualNames = [ Fld || {field_t, _, {id, _, Fld}, _} <- RecFields ],
            GivenNames  = [ Fld || {id, _, Fld} <- Fields ],
            case ActualNames -- GivenNames of   %% We know already that we don't have too many fields
                []      -> ok;
                Missing -> type_error({missing_fields, When, Type1, Missing})
            end;
        _ -> %% We can get here if there are other type errors.
            ok
    catch _:_ ->    %% Might be unsolved, we get a different error in that case
        ok
    end,
    check_record_create_constraints(Env, Cs).

is_contract_defined(C) ->
    ets_lookup(defined_contracts, qname(C)) =/= [].

check_is_contract_constraints(_Env, []) -> ok;
check_is_contract_constraints(Env, [C | Cs]) ->
    #is_contract_constraint{ contract_t = Type, context = Cxt, force_def = ForceDef } = C,
    Type1 = unfold_types_in_type(Env, instantiate(Type)),
    TypeName = record_type_name(Type1),
    case lookup_type(Env, TypeName) of
        {_, {_Ann, {[], {contract_t, _}}}} ->
            case not ForceDef orelse is_contract_defined(TypeName) of
                true -> ok;
                false -> type_error({contract_lacks_definition, Type1, Cxt})
                end;
        _ -> type_error({not_a_contract_type, Type1, Cxt})
    end,
    check_is_contract_constraints(Env, Cs).

-spec solve_field_constraints(env(), [field_constraint()]) -> ok.
solve_field_constraints(Env, Constraints) ->
    %% First look for record fields that appear in only one type definition
    IsAmbiguous = fun(#field_constraint{
                        record_t = RecordType,
                        field    = Field={id, _Attrs, FieldName},
                        field_t  = FieldType,
                        kind     = Kind,
                        context  = When }) ->
        case lookup_record_field(Env, FieldName, Kind) of
            [] ->
                type_error({undefined_field, Field}),
                false;
            [#field_info{field_t = FldType, record_t = RecType}] ->
                create_freshen_tvars(),
                FreshFldType = freshen(FldType),
                FreshRecType = freshen(RecType),
                destroy_freshen_tvars(),
                unify(Env, FreshFldType, FieldType, {field_constraint, FreshFldType, FieldType, When}),
                unify(Env, FreshRecType, RecordType, {record_constraint, FreshRecType, RecordType, When}),
                false;
            _ ->
                %% ambiguity--need cleverer strategy
                true
         end end,
    AmbiguousConstraints = lists:filter(IsAmbiguous, Constraints),
    solve_ambiguous_field_constraints(Env, AmbiguousConstraints).

-spec solve_ambiguous_field_constraints(env(), [field_constraint()]) -> ok.
solve_ambiguous_field_constraints(Env, Constraints) ->
    Unknown = solve_known_record_types(Env, Constraints),
    if Unknown == [] -> ok;
       length(Unknown) < length(Constraints) ->
            %% progress! Keep trying.
            solve_ambiguous_field_constraints(Env, Unknown);
       true ->
            case solve_unknown_record_types(Env, Unknown) of
                true -> %% Progress!
                    solve_ambiguous_field_constraints(Env, Unknown);
                _ -> ok %% No progress. Report errors later.
            end
    end.

-spec solve_unknown_record_types(env(), [field_constraint()]) -> true | [tuple()].
solve_unknown_record_types(Env, Unknown) ->
    UVars = lists:usort([UVar || #field_constraint{record_t = UVar = {uvar, _, _}} <- Unknown]),
    Solutions = [solve_for_uvar(Env, UVar, [{Kind, When, Field}
                                            || #field_constraint{record_t = U, field = Field, kind = Kind, context = When} <- Unknown,
                                               U == UVar])
                 || UVar <- UVars],
    case lists:member(true, Solutions) of
        true  -> true;
        false -> Solutions
    end.

-spec solve_known_record_types(env(), [field_constraint()]) -> [field_constraint()].
solve_known_record_types(Env, Constraints) ->
    DerefConstraints =
        [ C#field_constraint{record_t = dereference(RecordType)}
         || C = #field_constraint{record_t = RecordType} <- Constraints ],
    SolvedConstraints =
        [begin
            #field_constraint{record_t = RecType,
                              field    = FieldName,
                              field_t  = FieldType,
                              context  = When} = C,
            RecId = record_type_name(RecType),
            Attrs = aeso_syntax:get_ann(RecId),
            case lookup_type(Env, RecId) of
                {_, {_Ann, {Formals, {What, Fields}}}} when What =:= record_t; What =:= contract_t ->
                     FieldTypes = [{Name, Type} || {field_t, _, {id, _, Name}, Type} <- Fields],
                     {id, _, FieldString} = FieldName,
                     case proplists:get_value(FieldString, FieldTypes) of
                         undefined ->
                             type_error({missing_field, FieldName, RecId}),
                             not_solved;
                         FldType ->
                             create_freshen_tvars(),
                             FreshFldType = freshen(FldType),
                             FreshRecType = freshen(app_t(Attrs, RecId, Formals)),
                             destroy_freshen_tvars(),
                             unify(Env, FreshFldType, FieldType, {field_constraint, FreshFldType, FieldType, When}),
                             unify(Env, FreshRecType, RecType, {record_constraint, FreshRecType, RecType, When}),
                             C
                     end;
                _ ->
                    type_error({not_a_record_type, instantiate(RecType), When}),
                    not_solved
             end
         end
         || C <- DerefConstraints,
            case C#field_constraint.record_t of
                {uvar, _, _} -> false;
                _          -> true
            end],
    DerefConstraints--SolvedConstraints.

destroy_and_report_unsolved_field_constraints(Env) ->
    {FieldCs, OtherCs} =
        lists:partition(fun(#field_constraint{}) -> true; (_) -> false end,
                        get_field_constraints()),
    {CreateCs, OtherCs1} =
        lists:partition(fun(#record_create_constraint{}) -> true; (_) -> false end,
                        OtherCs),
    {ContractCs, []} =
        lists:partition(fun(#is_contract_constraint{}) -> true; (_) -> false end, OtherCs1),
    Unknown  = solve_known_record_types(Env, FieldCs),
    if Unknown == [] -> ok;
       true ->
            case solve_unknown_record_types(Env, Unknown) of
                true   -> ok;
                Errors -> [ type_error(Err) || Err <- Errors ]
            end
    end,
    check_record_create_constraints(Env, CreateCs),
    check_is_contract_constraints(Env, ContractCs),
    destroy_field_constraints(),
    ok.

record_type_name({app_t, _Attrs, RecId, _Args}) when ?is_type_id(RecId) ->
    RecId;
record_type_name(RecId) when ?is_type_id(RecId) ->
    RecId;
record_type_name(_Other) ->
    %% io:format("~p is not a record type\n", [Other]),
    {id, [{origin, system}], "not_a_record_type"}.

solve_for_uvar(Env, UVar = {uvar, Attrs, _}, Fields0) ->
    Fields = [{Kind, Fld} || {Kind, _, Fld} <- Fields0],
    [{_, When, _} | _] = Fields0,    %% Get the location from the first field
    %% If we have 'create' constraints they must be complete.
    Covering = lists:usort([ Name || {create, {id, _, Name}} <- Fields ]),
    %% Does this set of fields uniquely identify a record type?
    FieldNames = [ Name || {_Kind, {id, _, Name}} <- Fields ],
    UniqueFields = lists:usort(FieldNames),
    Candidates = [RecType || #field_info{record_t = RecType} <- lookup_record_field(Env, hd(FieldNames))],
    TypesAndFields = [case lookup_type(Env, record_type_name(RecType)) of
                        {_, {_, {_, {record_t, RecFields}}}} ->
                            {RecType, [Field || {field_t, _, {id, _, Field}, _} <- RecFields]};
                        {_, {_, {_, {contract_t, ConFields}}}} ->
                            %% TODO: is this right?
                            {RecType, [Field || {field_t, _, {id, _, Field}, _} <- ConFields]};
                        false -> %% impossible?
                            error({no_definition_for, record_type_name(RecType), in, Env})
                      end
                      || RecType <- Candidates],
    PartialSolutions =
        lists:sort([{RecType, if Covering == [] -> []; true -> RecFields -- Covering end}
                    || {RecType, RecFields} <- TypesAndFields,
                       UniqueFields -- RecFields == []]),
    Solutions = [RecName || {RecName, []} <- PartialSolutions],
    case {Solutions, PartialSolutions} of
        {[], []} ->
            {no_records_with_all_fields, Fields};
        {[], _} ->
            case PartialSolutions of
                [{RecType, Missing} | _] -> %% TODO: better error if ambiguous
                    {missing_fields, When, RecType, Missing}
            end;
        {[RecType], _} ->
            RecName = record_type_name(RecType),
            {_, {_, {Formals, {_RecOrCon, _}}}} = lookup_type(Env, RecName),
            create_freshen_tvars(),
            FreshRecType = freshen(app_t(Attrs, RecName, Formals)),
            destroy_freshen_tvars(),
            unify(Env, UVar, FreshRecType, {solve_rec_type, UVar, Fields}),
            true;
        {StillPossible, _} ->
            {ambiguous_record, Fields, StillPossible}
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
unfold_types(Env, {letfun, Ann, Name, Args, Type, Body}, Options) ->
    {letfun, Ann, Name, unfold_types(Env, Args, Options), unfold_types_in_type(Env, Type, Options), unfold_types(Env, Body, Options)};
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

unify(_, {id, _, "_"}, _, _When) -> true;
unify(_, _, {id, _, "_"}, _When) -> true;
unify(Env, A, B, When) ->
    Options =
        case When of    %% Improve source location for map_in_map_key errors
            {check_expr, E, _, _} -> [{ann, aeso_syntax:get_ann(E)}];
            _                     -> []
        end,
    A1 = dereference(unfold_types_in_type(Env, A, Options)),
    B1 = dereference(unfold_types_in_type(Env, B, Options)),
    unify1(Env, A1, B1, When).

unify1(_Env, {uvar, _, R}, {uvar, _, R}, _When) ->
    true;
unify1(_Env, {uvar, A, R}, T, When) ->
    case occurs_check(R, T) of
        true ->
            cannot_unify({uvar, A, R}, T, When),
            false;
        false ->
            ets_insert(type_vars, {R, T}),
            true
    end;
unify1(Env, T, {uvar, A, R}, When) ->
    unify1(Env, {uvar, A, R}, T, When);
unify1(_Env, {tvar, _, X}, {tvar, _, X}, _When) -> true; %% Rigid type variables
unify1(Env, [A|B], [C|D], When) ->
    unify(Env, A, C, When) andalso unify(Env, B, D, When);
unify1(_Env, X, X, _When) ->
    true;
unify1(_Env, {id, _, Name}, {id, _, Name}, _When) ->
    true;
unify1(_Env, {con, _, Name}, {con, _, Name}, _When) ->
    true;
unify1(_Env, {qid, _, Name}, {qid, _, Name}, _When) ->
    true;
unify1(_Env, {qcon, _, Name}, {qcon, _, Name}, _When) ->
    true;
unify1(_Env, {bytes_t, _, Len}, {bytes_t, _, Len}, _When) ->
    true;
unify1(Env, {if_t, _, {id, _, Id}, Then1, Else1}, {if_t, _, {id, _, Id}, Then2, Else2}, When) ->
    unify(Env, Then1, Then2, When) andalso
    unify(Env, Else1, Else2, When);

unify1(_Env, {fun_t, _, _, _, _}, {fun_t, _, _, var_args, _}, When) ->
    type_error({unify_varargs, When});
unify1(_Env, {fun_t, _, _, var_args, _}, {fun_t, _, _, _, _}, When) ->
    type_error({unify_varargs, When});
unify1(Env, {fun_t, _, Named1, Args1, Result1}, {fun_t, _, Named2, Args2, Result2}, When)
  when length(Args1) == length(Args2) ->
    unify(Env, Named1, Named2, When) andalso
    unify(Env, Args1, Args2, When) andalso unify(Env, Result1, Result2, When);
unify1(Env, {app_t, _, {Tag, _, F}, Args1}, {app_t, _, {Tag, _, F}, Args2}, When)
  when length(Args1) == length(Args2), Tag == id orelse Tag == qid ->
    unify(Env, Args1, Args2, When);
unify1(Env, {tuple_t, _, As}, {tuple_t, _, Bs}, When)
  when length(As) == length(Bs) ->
    unify(Env, As, Bs, When);
unify1(Env, {named_arg_t, _, Id1, Type1, _}, {named_arg_t, _, Id2, Type2, _}, When) ->
    unify1(Env, Id1, Id2, {arg_name, Id1, Id2, When}),
    unify1(Env, Type1, Type2, When);
%% The grammar is a bit inconsistent about whether types without
%% arguments are represented as applications to an empty list of
%% parameters or not. We therefore allow them to unify.
unify1(Env, {app_t, _, T, []}, B, When) ->
    unify(Env, T, B, When);
unify1(Env, A, {app_t, _, T, []}, When) ->
    unify(Env, A, T, When);
unify1(_Env, A, B, When) ->
    cannot_unify(A, B, When),
    false.

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
    add_bytes_constraint({is_bytes, X}),
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

apply_typesig_constraint(_Ann, none, _FunT) -> ok;
apply_typesig_constraint(Ann, address_to_contract, {fun_t, _, [], [_], Type}) ->
    constrain([#is_contract_constraint{ contract_t = Type,
                                        context    = {address_to_contract, Ann}}]);
apply_typesig_constraint(Ann, bytes_concat, {fun_t, _, [], [A, B], C}) ->
    add_bytes_constraint({add_bytes, Ann, concat, A, B, C});
apply_typesig_constraint(Ann, bytes_split, {fun_t, _, [], [C], {tuple_t, _, [A, B]}}) ->
    add_bytes_constraint({add_bytes, Ann, split, A, B, C});
apply_typesig_constraint(Ann, bytecode_hash, {fun_t, _, _, [Con], _}) ->
    constrain([#is_contract_constraint{ contract_t = Con,
                                        context    = {bytecode_hash, Ann} }]).


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


%% Save unification failures for error messages.

cannot_unify(A, B, When) ->
    type_error({cannot_unify, A, B, When}).

type_error(Err) ->
    ets_insert(type_errors, Err).

create_type_errors() ->
    ets_new(type_errors, [bag]).

destroy_and_report_type_errors(Env) ->
    Errors0 = lists:reverse(ets_tab2list(type_errors)),
    %% io:format("Type errors now: ~p\n", [Errors0]),
    ets_delete(type_errors),
    Errors  = [ mk_error(unqualify(Env, Err)) || Err <- Errors0 ],
    aeso_errors:throw(Errors).  %% No-op if Errors == []

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

mk_t_err(Pos, Msg) ->
    aeso_errors:new(type_error, Pos, lists:flatten(Msg)).
mk_t_err(Pos, Msg, Ctxt) ->
    aeso_errors:new(type_error, Pos, lists:flatten(Msg), lists:flatten(Ctxt)).

mk_error({no_decls, File}) ->
    Pos = aeso_errors:pos(File, 0, 0),
    mk_t_err(Pos, "Empty contract\n");
mk_error({mismatched_decl_in_funblock, Name, Decl}) ->
    Msg = io_lib:format("Mismatch in the function block. Expected implementation/type declaration of ~s function\n", [Name]),
    mk_t_err(pos(Decl), Msg);
mk_error({higher_kinded_typevar, T}) ->
    Msg = io_lib:format("Type ~s is a higher kinded type variable\n"
                        "(takes another type as an argument)\n", [pp(instantiate(T))]
                       ),
    mk_t_err(pos(T), Msg);
mk_error({wrong_type_arguments, X, ArityGiven, ArityReal}) ->
    Msg = io_lib:format("Arity for ~s doesn't match. Expected ~p, got ~p\n"
                       , [pp(instantiate(X)), ArityReal, ArityGiven]
                       ),
    mk_t_err(pos(X), Msg);
mk_error({unnamed_map_update_with_default, Upd}) ->
    Msg = "Invalid map update with default\n",
    mk_t_err(pos(Upd), Msg);
mk_error({fundecl_must_have_funtype, _Ann, Id, Type}) ->
    Msg = io_lib:format("~s at ~s was declared with an invalid type ~s.\n"
                       "Entrypoints and functions must have functional types"
                       , [pp(Id), pp_loc(Id), pp(instantiate(Type))]),
    mk_t_err(pos(Id), Msg);
mk_error({cannot_unify, A, B, When}) ->
    Msg = io_lib:format("Cannot unify ~s\n         and ~s\n",
                        [pp(instantiate(A)), pp(instantiate(B))]),
    {Pos, Ctxt} = pp_when(When),
    mk_t_err(Pos, Msg, Ctxt);
mk_error({unbound_variable, Id}) ->
    Msg = io_lib:format("Unbound variable ~s at ~s\n", [pp(Id), pp_loc(Id)]),
    case Id of
        {qid, _, ["Chain", "event"]} ->
            Cxt = "Did you forget to define the event type?",
            mk_t_err(pos(Id), Msg, Cxt);
        _ -> mk_t_err(pos(Id), Msg)
    end;
mk_error({undefined_field, Id}) ->
    Msg = io_lib:format("Unbound field ~s at ~s\n", [pp(Id), pp_loc(Id)]),
    mk_t_err(pos(Id), Msg);
mk_error({not_a_record_type, Type, Why}) ->
    Msg = io_lib:format("~s\n", [pp_type("Not a record type: ", Type)]),
    {Pos, Ctxt} = pp_why_record(Why),
    mk_t_err(Pos, Msg, Ctxt);
mk_error({not_a_contract_type, Type, Cxt}) ->
    Msg =
        case Type of
            {tvar, _, _} ->
                "Unresolved contract type\n";
            _ ->
                io_lib:format("The type ~s is not a contract type\n", [pp_type("", Type)])
        end,
    {Pos, Cxt1} =
        case Cxt of
            {var_args, Ann, Fun} ->
                {pos(Ann),
                 io_lib:format("when calling variadic function\n~s\n", [pp_expr("  ", Fun)])};
            {contract_literal, Lit} ->
                {pos(Lit),
                 io_lib:format("when checking that the contract literal\n~s\n"
                               "has the type\n~s\n",
                               [pp_expr("  ", Lit), pp_type("  ", Type)])};
            {address_to_contract, Ann} ->
                {pos(Ann),
                 io_lib:format("when checking that the call to\n  Address.to_contract\n"
                               "has the type\n~s\n",
                               [pp_type("  ", Type)])}
        end,
    mk_t_err(Pos, Msg, Cxt1);
mk_error({non_linear_pattern, Pattern, Nonlinear}) ->
    Msg = io_lib:format("Repeated name~s ~s in pattern\n~s (at ~s)\n",
                        [plural("", "s", Nonlinear), string:join(Nonlinear, ", "),
                         pp_expr("  ", Pattern), pp_loc(Pattern)]),
    mk_t_err(pos(Pattern), Msg);
mk_error({ambiguous_record, Fields = [{_, First} | _], Candidates}) ->
    Msg = io_lib:format("Ambiguous record type with field~s ~s (at ~s) could be one of\n~s",
                        [plural("", "s", Fields), string:join([ pp(F) || {_, F} <- Fields ], ", "),
                        pp_loc(First), [ ["  - ", pp(C), " (at ", pp_loc(C), ")\n"] || C <- Candidates ]]),
    mk_t_err(pos(First), Msg);
mk_error({missing_field, Field, Rec}) ->
    Msg = io_lib:format("Record type ~s does not have field ~s (at ~s)\n",
                        [pp(Rec), pp(Field), pp_loc(Field)]),
    mk_t_err(pos(Field), Msg);
mk_error({missing_fields, Ann, RecType, Fields}) ->
    Msg = io_lib:format("The field~s ~s ~s missing when constructing an element of type ~s (at ~s)\n",
                        [plural("", "s", Fields), string:join(Fields, ", "),
                         plural("is", "are", Fields), pp(RecType), pp_loc(Ann)]),
    mk_t_err(pos(Ann), Msg);
mk_error({no_records_with_all_fields, Fields = [{_, First} | _]}) ->
    Msg = io_lib:format("No record type with field~s ~s (at ~s)\n",
                        [plural("", "s", Fields), string:join([ pp(F) || {_, F} <- Fields ], ", "),
                         pp_loc(First)]),
    mk_t_err(pos(First), Msg);
mk_error({recursive_types_not_implemented, Types}) ->
    S = plural(" is", "s are mutually", Types),
    Msg = io_lib:format("The following type~s recursive, which is not yet supported:\n~s",
                        [S, [io_lib:format("  - ~s (at ~s)\n", [pp(T), pp_loc(T)]) || T <- Types]]),
    mk_t_err(pos(hd(Types)), Msg);
mk_error({event_must_be_variant_type, Where}) ->
    Msg = io_lib:format("The event type must be a variant type (at ~s)\n", [pp_loc(Where)]),
    mk_t_err(pos(Where), Msg);
mk_error({indexed_type_must_be_word, Type, Type}) ->
    Msg = io_lib:format("The indexed type ~s (at ~s) is not a word type\n",
                        [pp_type("", Type), pp_loc(Type)]),
    mk_t_err(pos(Type), Msg);
mk_error({indexed_type_must_be_word, Type, Type1}) ->
    Msg = io_lib:format("The indexed type ~s (at ~s) equals ~s which is not a word type\n",
                        [pp_type("", Type), pp_loc(Type), pp_type("", Type1)]),
    mk_t_err(pos(Type), Msg);
mk_error({event_0_to_3_indexed_values, Constr}) ->
    Msg = io_lib:format("The event constructor ~s (at ~s) has too many indexed values (max 3)\n",
                        [name(Constr), pp_loc(Constr)]),
    mk_t_err(pos(Constr), Msg);
mk_error({event_0_to_1_string_values, Constr}) ->
    Msg = io_lib:format("The event constructor ~s (at ~s) has too many non-indexed values (max 1)\n",
                        [name(Constr), pp_loc(Constr)]),
    mk_t_err(pos(Constr), Msg);
mk_error({repeated_constructor, Cs}) ->
    Msg = io_lib:format("Variant types must have distinct constructor names\n~s",
                        [[ io_lib:format("~s  (at ~s)\n", [pp_typed("  - ", C, T), pp_loc(C)]) || {C, T} <- Cs ]]),
    mk_t_err(pos(element(1, hd(Cs))), Msg);
mk_error({bad_named_argument, [], Name}) ->
    Msg = io_lib:format("Named argument ~s (at ~s) supplied to function expecting no named arguments.\n",
                        [pp(Name), pp_loc(Name)]),
    mk_t_err(pos(Name), Msg);
mk_error({bad_named_argument, Args, Name}) ->
    Msg = io_lib:format("Named argument ~s (at ~s) is not one of the expected named arguments\n~s",
                        [pp(Name), pp_loc(Name),
                        [ io_lib:format("~s\n", [pp_typed("  - ", Arg, Type)])
                          || {named_arg_t, _, Arg, Type, _} <- Args ]]),
    mk_t_err(pos(Name), Msg);
mk_error({unsolved_named_argument_constraint, #named_argument_constraint{name = Name, type = Type}}) ->
    Msg = io_lib:format("Named argument ~s (at ~s) supplied to function with unknown named arguments.\n",
                        [pp_typed("", Name, Type), pp_loc(Name)]),
    mk_t_err(pos(Name), Msg);
mk_error({reserved_entrypoint, Name, Def}) ->
    Msg = io_lib:format("The name '~s' is reserved and cannot be used for a\n"
                        "top-level contract function (at ~s).\n", [Name, pp_loc(Def)]),
    mk_t_err(pos(Def), Msg);
mk_error({duplicate_definition, Name, Locs}) ->
    Msg = io_lib:format("Duplicate definitions of ~s at\n~s",
                        [Name, [ ["  - ", pp_loc(L), "\n"] || L <- Locs ]]),
    mk_t_err(pos(lists:last(Locs)), Msg);
mk_error({duplicate_scope, Kind, Name, OtherKind, L}) ->
    Msg = io_lib:format("The ~p ~s (at ~s) has the same name as a ~p at ~s\n",
                        [Kind, pp(Name), pp_loc(Name), OtherKind, pp_loc(L)]),
    mk_t_err(pos(Name), Msg);
mk_error({include, _, {string, Pos, Name}}) ->
    Msg = io_lib:format("Include of '~s' at ~s\nnot allowed, include only allowed at top level.\n",
                        [binary_to_list(Name), pp_loc(Pos)]),
    mk_t_err(pos(Pos), Msg);
mk_error({namespace, _Pos, {con, Pos, Name}, _Def}) ->
    Msg = io_lib:format("Nested namespaces are not allowed\nNamespace '~s' at ~s not defined at top level.\n",
                        [Name, pp_loc(Pos)]),
    mk_t_err(pos(Pos), Msg);
mk_error({Contract, _Pos, {con, Pos, Name}, _Def}) when ?IS_CONTRACT_HEAD(Contract) ->
    Msg = io_lib:format("Nested contracts are not allowed\nContract '~s' at ~s not defined at top level.\n",
                        [Name, pp_loc(Pos)]),
    mk_t_err(pos(Pos), Msg);
mk_error({type_decl, _, {id, Pos, Name}, _}) ->
    Msg = io_lib:format("Empty type declarations are not supported\nType ~s at ~s lacks a definition\n",
                        [Name, pp_loc(Pos)]),
    mk_t_err(pos(Pos), Msg);
mk_error({letval, _Pos, {id, Pos, Name}, _Def}) ->
    Msg = io_lib:format("Toplevel \"let\" definitions are not supported\nValue ~s at ~s could be replaced by 0-argument function\n",
                        [Name, pp_loc(Pos)]),
    mk_t_err(pos(Pos), Msg);
mk_error({stateful_not_allowed, Id, Fun}) ->
    Msg = io_lib:format("Cannot reference stateful function ~s (at ~s)\nin the definition of non-stateful function ~s.\n",
                        [pp(Id), pp_loc(Id), pp(Fun)]),
    mk_t_err(pos(Id), Msg);
mk_error({value_arg_not_allowed, Value, Fun}) ->
    Msg = io_lib:format("Cannot pass non-zero value argument ~s (at ~s)\nin the definition of non-stateful function ~s.\n",
                        [pp_expr("", Value), pp_loc(Value), pp(Fun)]),
    mk_t_err(pos(Value), Msg);
mk_error({init_depends_on_state, Which, [_Init | Chain]}) ->
    WhichCalls = fun("put") -> ""; ("state") -> ""; (_) -> ", which calls" end,
    Msg = io_lib:format("The init function should return the initial state as its result and cannot ~s the state,\nbut it calls\n~s",
                        [if Which == put -> "write"; true -> "read" end,
                         [ io_lib:format("  - ~s (at ~s)~s\n", [Fun, pp_loc(Ann), WhichCalls(Fun)])
                           || {[_, Fun], Ann} <- Chain]]),
    mk_t_err(pos(element(2, hd(Chain))), Msg);
mk_error({missing_body_for_let, Ann}) ->
    Msg = io_lib:format("Let binding at ~s must be followed by an expression\n", [pp_loc(Ann)]),
    mk_t_err(pos(Ann), Msg);
mk_error({public_modifier_in_contract, Decl}) ->
    Decl1 = mk_entrypoint(Decl),
    Msg = io_lib:format("Use 'entrypoint' instead of 'function' for public function ~s (at ~s):\n~s\n",
                        [pp_expr("", element(3, Decl)), pp_loc(Decl),
                         prettypr:format(prettypr:nest(2, aeso_pretty:decl(Decl1)))]),
    mk_t_err(pos(Decl), Msg);
mk_error({init_must_be_an_entrypoint, Decl}) ->
    Decl1 = mk_entrypoint(Decl),
    Msg = io_lib:format("The init function (at ~s) must be an entrypoint:\n~s\n",
                        [pp_loc(Decl),
                         prettypr:format(prettypr:nest(2, aeso_pretty:decl(Decl1)))]),
    mk_t_err(pos(Decl), Msg);
mk_error({init_must_not_be_payable, Decl}) ->
    Msg = io_lib:format("The init function (at ~s) cannot be payable.\n"
                        "You don't need the 'payable' annotation to be able to attach\n"
                        "funds to the create contract transaction.",
                        [pp_loc(Decl)]),
    mk_t_err(pos(Decl), Msg);
mk_error({proto_must_be_entrypoint, Decl}) ->
    Decl1 = mk_entrypoint(Decl),
    Msg = io_lib:format("Use 'entrypoint' for declaration of ~s (at ~s):\n~s\n",
                        [pp_expr("", element(3, Decl)), pp_loc(Decl),
                         prettypr:format(prettypr:nest(2, aeso_pretty:decl(Decl1)))]),
    mk_t_err(pos(Decl), Msg);
mk_error({proto_in_namespace, Decl}) ->
    Msg = io_lib:format("Namespaces cannot contain function prototypes (at ~s).\n",
                        [pp_loc(Decl)]),
    mk_t_err(pos(Decl), Msg);
mk_error({entrypoint_in_namespace, Decl}) ->
    Msg = io_lib:format("Namespaces cannot contain entrypoints (at ~s). Use 'function' instead.\n",
                        [pp_loc(Decl)]),
    mk_t_err(pos(Decl), Msg);
mk_error({private_entrypoint, Decl}) ->
    Msg = io_lib:format("The entrypoint ~s (at ~s) cannot be private. Use 'function' instead.\n",
                        [pp_expr("", element(3, Decl)), pp_loc(Decl)]),
    mk_t_err(pos(Decl), Msg);
mk_error({private_and_public, Decl}) ->
    Msg = io_lib:format("The function ~s (at ~s) cannot be both public and private.\n",
                        [pp_expr("", element(3, Decl)), pp_loc(Decl)]),
    mk_t_err(pos(Decl), Msg);
mk_error({contract_has_no_entrypoints, Con}) ->
    Msg = io_lib:format("The contract ~s (at ~s) has no entrypoints. Since Sophia version 3.2, public\n"
                        "contract functions must be declared with the 'entrypoint' keyword instead of\n"
                        "'function'.\n", [pp_expr("", Con), pp_loc(Con)]),
    mk_t_err(pos(Con), Msg);
mk_error({definition_in_contract_interface, Ann, {id, _, Id}}) ->
    Msg = "Contract interfaces cannot contain defined functions or entrypoints.\n",
    Cxt = io_lib:format("Fix: replace the definition of '~s' by a type signature.\n", [Id]),
    mk_t_err(pos(Ann), Msg, Cxt);
mk_error({unbound_type, Type}) ->
    Msg = io_lib:format("Unbound type ~s (at ~s).\n", [pp_type("", Type), pp_loc(Type)]),
    mk_t_err(pos(Type), Msg);
mk_error({new_tuple_syntax, Ann, Ts}) ->
    Msg = io_lib:format("Invalid type\n~s  (at ~s)\nThe syntax of tuple types changed in Sophia version 4.0. Did you mean\n~s\n",
                        [pp_type("  ", {args_t, Ann, Ts}), pp_loc(Ann), pp_type("  ", {tuple_t, Ann, Ts})]),
    mk_t_err(pos(Ann), Msg);
mk_error({map_in_map_key, Ann, KeyType}) ->
    Msg = io_lib:format("Invalid key type\n~s\n", [pp_type("  ", KeyType)]),
    Cxt = "Map keys cannot contain other maps.\n",
    mk_t_err(pos(Ann), Msg, Cxt);
mk_error({cannot_call_init_function, Ann}) ->
    Msg = "The 'init' function is called exclusively by the create contract transaction\n"
          "and cannot be called from the contract code.\n",
    mk_t_err(pos(Ann), Msg);
mk_error({contract_treated_as_namespace, Ann, [Con, Fun] = QName}) ->
    Msg = io_lib:format("Invalid call to contract entrypoint '~s'.\n", [string:join(QName, ".")]),
    Cxt = io_lib:format("It must be called as 'c.~s' for some c : ~s.\n", [Fun, Con]),
    mk_t_err(pos(Ann), Msg, Cxt);
mk_error({bad_top_level_decl, Decl}) ->
    What = case element(1, Decl) of
               letval -> "function or entrypoint";
               _      -> "contract or namespace"
           end,
    Id = element(3, Decl),
    Msg = io_lib:format("The definition of '~s' must appear inside a ~s.\n",
                        [pp_expr("", Id), What]),
    mk_t_err(pos(Decl), Msg);
mk_error({unknown_byte_length, Type}) ->
    Msg = io_lib:format("Cannot resolve length of byte array.\n", []),
    mk_t_err(pos(Type), Msg);
mk_error({unsolved_bytes_constraint, Ann, concat, A, B, C}) ->
    Msg = io_lib:format("Failed to resolve byte array lengths in call to Bytes.concat with arguments of type\n"
                        "~s  (at ~s)\n~s  (at ~s)\nand result type\n~s  (at ~s)\n",
                        [pp_type("  - ", A), pp_loc(A), pp_type("  - ", B),
                         pp_loc(B), pp_type("  - ", C), pp_loc(C)]),
    mk_t_err(pos(Ann), Msg);
mk_error({unsolved_bytes_constraint, Ann, split, A, B, C}) ->
    Msg = io_lib:format("Failed to resolve byte array lengths in call to Bytes.split with argument of type\n"
                        "~s  (at ~s)\nand result types\n~s  (at ~s)\n~s  (at ~s)\n",
                        [ pp_type("  - ", C), pp_loc(C), pp_type("  - ", A), pp_loc(A),
                          pp_type("  - ", B), pp_loc(B)]),
    mk_t_err(pos(Ann), Msg);
mk_error({failed_to_get_compiler_version, Err}) ->
    Msg = io_lib:format("Failed to get compiler version. Error:\n  ~p\n", [Err]),
    mk_t_err(pos(0, 0), Msg);
mk_error({compiler_version_mismatch, Ann, Version, Op, Bound}) ->
    PrintV = fun(V) -> string:join([integer_to_list(N) || N <- V], ".") end,
    Msg = io_lib:format("Cannot compile with this version of the compiler,\n"
                        "because it does not satisfy the constraint"
                        " ~s ~s ~s\n", [PrintV(Version), Op, PrintV(Bound)]),
    mk_t_err(pos(Ann), Msg);
mk_error({empty_record_or_map_update, Expr}) ->
    Msg = io_lib:format("Empty record/map update\n~s",
                        [pp_expr("  ", Expr)]),
    mk_t_err(pos(Expr), Msg);
mk_error({mixed_record_and_map, Expr}) ->
    Msg = io_lib:format("Mixed record fields and map keys in\n~s",
                        [pp_expr("  ", Expr)]),
    mk_t_err(pos(Expr), Msg);
mk_error({named_argument_must_be_literal_bool, Name, Arg}) ->
    Msg = io_lib:format("Invalid '~s' argument\n~s\nIt must be either 'true' or 'false'.", [Name, pp_expr("  ", instantiate(Arg))]),
    mk_t_err(pos(Arg), Msg);
mk_error({conflicting_updates_for_field, Upd, Key}) ->
    Msg = io_lib:format("Conflicting updates for field '~s'\n", [Key]),
    mk_t_err(pos(Upd), Msg);
mk_error({ambiguous_main_contract, Ann}) ->
    Msg = "Could not deduce the main contract. You can point it out manually with the `main` keyword.",
    mk_t_err(pos(Ann), Msg);
mk_error({main_contract_undefined, Ann}) ->
    Msg = "No contract defined.\n",
    mk_t_err(pos(Ann), Msg);
mk_error({multiple_main_contracts, Ann}) ->
    Msg = "Only one main contract can be defined.\n",
    mk_t_err(pos(Ann), Msg);
mk_error({unify_varargs, When}) ->
    Msg = "Cannot unify variable argument list.\n",
    {Pos, Ctxt} = pp_when(When),
    mk_t_err(Pos, Msg, Ctxt);
mk_error({clone_no_contract, Ann}) ->
    Msg = "Chain.clone requires `ref` named argument of contract type.\n",
    mk_t_err(pos(Ann), Msg);
mk_error({contract_lacks_definition, Type, When}) ->
    Msg = io_lib:format(
            "~s is not implemented.\n",
            [pp_type(Type)]
           ),
    {Pos, Ctxt} = pp_when(When),
    mk_t_err(Pos, Msg, Ctxt);
mk_error(Err) ->
    Msg = io_lib:format("Unknown error: ~p\n", [Err]),
    mk_t_err(pos(0, 0), Msg).

mk_entrypoint(Decl) ->
    Ann   = [entrypoint | lists:keydelete(public, 1,
                          lists:keydelete(private, 1,
                            aeso_syntax:get_ann(Decl))) -- [public, private]],
    aeso_syntax:set_ann(Ann, Decl).

pp_when({todo, What}) -> {pos(0, 0), io_lib:format("[TODO] ~p\n", [What])};
pp_when({at, Ann}) -> {pos(Ann), io_lib:format("at ~s\n", [pp_loc(Ann)])};
pp_when({check_typesig, Name, Inferred, Given}) ->
    {pos(Given),
     io_lib:format("when checking the definition of ~s (at ~s)\n"
                   "  inferred type: ~s\n"
                   "  given type:    ~s\n",
         [Name, pp_loc(Given), pp(instantiate(Inferred)), pp(instantiate(Given))])};
pp_when({infer_app, Fun, NamedArgs, Args, Inferred0, ArgTypes0}) ->
    Inferred = instantiate(Inferred0),
    ArgTypes = instantiate(ArgTypes0),
    {pos(Fun),
     io_lib:format("when checking the application at ~s of\n"
                   "~s\n"
                   "to arguments\n~s",
                   [pp_loc(Fun),
                    pp_typed("  ", Fun, Inferred),
                    [ [pp_expr("  ", NamedArg), "\n"] || NamedArg <- NamedArgs ] ++
                    [ [pp_typed("  ", Arg, ArgT), "\n"]
                       || {Arg, ArgT} <- lists:zip(Args, ArgTypes) ] ])};
pp_when({field_constraint, FieldType0, InferredType0, Fld}) ->
    FieldType    = instantiate(FieldType0),
    InferredType = instantiate(InferredType0),
    {pos(Fld),
     case Fld of
         {var_args, _Ann, _Fun} ->
             io_lib:format("when checking contract construction of type\n~s (at ~s)\nagainst the expected type\n~s\n",
                          [pp_type("  ", FieldType),
                           pp_loc(Fld),
                           pp_type("  ", InferredType)
                          ]);
         {field, _Ann, LV, Id, E} ->
             io_lib:format("when checking the assignment of the field\n~s (at ~s)\nto the old value ~s and the new value\n~s\n",
                 [pp_typed("  ", {lvalue, [], LV}, FieldType),
                  pp_loc(Fld),
                  pp(Id),
                  pp_typed("  ", E, InferredType)]);
         {field, _Ann, LV, E} ->
             io_lib:format("when checking the assignment of the field\n~s (at ~s)\nto the value\n~s\n",
                 [pp_typed("  ", {lvalue, [], LV}, FieldType),
                  pp_loc(Fld),
                  pp_typed("  ", E, InferredType)]);
         {proj, _Ann, _Rec, _Fld} ->
             io_lib:format("when checking the record projection at ~s\n~s\nagainst the expected type\n~s\n",
                 [pp_loc(Fld),
                  pp_typed("  ", Fld, FieldType),
                  pp_type("  ", InferredType)])
     end};
pp_when({record_constraint, RecType0, InferredType0, Fld}) ->
    RecType      = instantiate(RecType0),
    InferredType = instantiate(InferredType0),
    {Pos, WhyRec} = pp_why_record(Fld),
    case Fld of
        {var_args, _Ann, _Fun} ->
            {Pos,
             io_lib:format("when checking that contract construction of type\n~s\n~s\n"
                           "matches the expected type\n~s\n",
                           [pp_type("  ", RecType), WhyRec, pp_type("  ", InferredType)]
                          )
            };
        {field, _Ann, _LV, _Id, _E} ->
            {Pos,
             io_lib:format("when checking that the record type\n~s\n~s\n"
                           "matches the expected type\n~s\n",
                 [pp_type("  ", RecType), WhyRec, pp_type("  ", InferredType)])};
        {field, _Ann, _LV, _E} ->
            {Pos,
             io_lib:format("when checking that the record type\n~s\n~s\n"
                           "matches the expected type\n~s\n",
                 [pp_type("  ", RecType), WhyRec, pp_type("  ", InferredType)])};
        {proj, _Ann, Rec, _FldName} ->
            {pos(Rec),
             io_lib:format("when checking that the expression\n~s (at ~s)\nhas type\n~s\n~s\n",
                 [pp_typed("  ", Rec, InferredType), pp_loc(Rec),
                  pp_type("  ", RecType), WhyRec])}
    end;
pp_when({if_branches, Then, ThenType0, Else, ElseType0}) ->
    {ThenType, ElseType} = instantiate({ThenType0, ElseType0}),
    Branches = [ {Then, ThenType} | [ {B, ElseType} || B <- if_branches(Else) ] ],
    {pos(element(1, hd(Branches))),
     io_lib:format("when comparing the types of the if-branches\n"
                   "~s", [ [ io_lib:format("~s (at ~s)\n", [pp_typed("  - ", B, BType), pp_loc(B)])
                           || {B, BType} <- Branches ] ])};
pp_when({case_pat, Pat, PatType0, ExprType0}) ->
    {PatType, ExprType} = instantiate({PatType0, ExprType0}),
    {pos(Pat),
     io_lib:format("when checking the type of the pattern at ~s\n~s\n"
                   "against the expected type\n~s\n",
                   [pp_loc(Pat), pp_typed("  ", Pat, PatType),
                    pp_type("  ", ExprType)])};
pp_when({check_expr, Expr, Inferred0, Expected0}) ->
    {Inferred, Expected} = instantiate({Inferred0, Expected0}),
    {pos(Expr),
     io_lib:format("when checking the type of the expression at ~s\n~s\n"
                   "against the expected type\n~s\n",
                   [pp_loc(Expr), pp_typed("  ", Expr, Inferred),
                    pp_type("  ", Expected)])};
pp_when({checking_init_type, Ann}) ->
    {pos(Ann),
     io_lib:format("when checking that 'init' returns a value of type 'state' at ~s\n",
                   [pp_loc(Ann)])};
pp_when({list_comp, BindExpr, Inferred0, Expected0}) ->
    {Inferred, Expected} = instantiate({Inferred0, Expected0}),
    {pos(BindExpr),
     io_lib:format("when checking rvalue of list comprehension binding at ~s\n~s\n"
                   "against type \n~s\n",
                   [pp_loc(BindExpr), pp_typed("  ", BindExpr, Inferred), pp_type("  ", Expected)])};
pp_when({check_named_arg_constraint, C}) ->
    {id, _, Name} = Arg = C#named_argument_constraint.name,
    [Type | _] = [ Type || {named_arg_t, _, {id, _, Name1}, Type, _} <- C#named_argument_constraint.args, Name1 == Name ],
    Err = io_lib:format("when checking named argument\n~s\nagainst inferred type\n~s",
                        [pp_typed("  ", Arg, Type), pp_type("  ", C#named_argument_constraint.type)]),
    {pos(Arg), Err};
pp_when({checking_init_args, Ann, Con0, ArgTypes0}) ->
    Con = instantiate(Con0),
    ArgTypes = instantiate(ArgTypes0),
    {pos(Ann),
     io_lib:format("when checking arguments of ~s's init entrypoint to match\n(~s)",
                   [pp_type(Con), string:join([pp_type(A) || A <- ArgTypes], ", ")])
    };
pp_when({return_contract, App, Con0}) ->
    Con = instantiate(Con0),
    {pos(App)
    , io_lib:format("when checking that expression returns contract of type\n~s", [pp_type("  ", Con)])
    };
pp_when({arg_name, Id1, Id2, When}) ->
    {Pos, Ctx} = pp_when(When),
    {Pos
    , io_lib:format("when unifying names of named arguments: ~s and ~s\n~s", [pp_expr(Id1), pp_expr(Id2), Ctx])
    };
pp_when({var_args, Ann, Fun}) ->
    {pos(Ann)
    , io_lib:format("when resolving arguments of variadic function\n~s\n", [pp_expr("  ", Fun)])
    };
pp_when(unknown) -> {pos(0,0), ""}.

-spec pp_why_record(why_record()) -> {pos(), iolist()}.
pp_why_record({var_args, Ann, Fun}) ->
    {pos(Ann),
     io_lib:format("arising from resolution of variadic function ~s (at ~s)",
                   [pp_expr(Fun), pp_loc(Fun)])};
pp_why_record(Fld = {field, _Ann, LV, _E}) ->
    {pos(Fld),
     io_lib:format("arising from an assignment of the field ~s (at ~s)",
                   [pp_expr({lvalue, [], LV}), pp_loc(Fld)])};
pp_why_record(Fld = {field, _Ann, LV, _Alias, _E}) ->
    {pos(Fld),
     io_lib:format("arising from an assignment of the field ~s (at ~s)",
                   [pp_expr({lvalue, [], LV}), pp_loc(Fld)])};
pp_why_record({proj, _Ann, Rec, FldName}) ->
    {pos(Rec),
     io_lib:format("arising from the projection of the field ~s (at ~s)",
         [pp(FldName), pp_loc(Rec)])}.


if_branches(If = {'if', Ann, _, Then, Else}) ->
    case proplists:get_value(format, Ann) of
        elif -> [Then | if_branches(Else)];
        _    -> [If]
    end;
if_branches(E) -> [E].

pp_typed(Label, E, T = {type_sig, _, _, _, _, _}) -> pp_typed(Label, E, typesig_to_fun_t(T));
pp_typed(Label, {typed, _, Expr, _}, Type) ->
    pp_typed(Label, Expr, Type);
pp_typed(Label, Expr, Type) ->
    pp_expr(Label, {typed, [], Expr, Type}).

pp_expr(Expr) ->
    pp_expr("", Expr).
pp_expr(Label, Expr) ->
    prettypr:format(prettypr:beside(prettypr:text(Label), aeso_pretty:expr(Expr, [show_generated]))).

pp_type(Type) ->
    pp_type("", Type).
pp_type(Label, Type) ->
    prettypr:format(prettypr:beside(prettypr:text(Label), aeso_pretty:type(Type, [show_generated]))).

src_file(T)      -> aeso_syntax:get_ann(file, T, no_file).
line_number(T)   -> aeso_syntax:get_ann(line, T, 0).
column_number(T) -> aeso_syntax:get_ann(col, T, 0).

pos(T)    -> aeso_errors:pos(src_file(T), line_number(T), column_number(T)).
pos(L, C) -> aeso_errors:pos(L, C).

loc(T) ->
    {line_number(T), column_number(T)}.

pp_loc(T) ->
    {Line, Col} = loc(T),
    case {Line, Col} of
        {0, 0} -> "(builtin location)";
        _      -> io_lib:format("line ~p, column ~p", [Line, Col])
    end.

plural(No, _Yes, [_]) -> No;
plural(_No, Yes, _)   -> Yes.

pp(T = {type_sig, _, _, _, _, _}) ->
    pp(typesig_to_fun_t(T));
pp([]) ->
    "";
pp([T]) ->
    pp(T);
pp([T|Ts]) ->
    [pp(T), ", "|pp(Ts)];
pp({id, _, Name}) ->
    Name;
pp({qid, _, Name}) ->
    string:join(Name, ".");
pp({con, _, Name}) ->
    Name;
pp({qcon, _, Name}) ->
    string:join(Name, ".");
pp({uvar, _, Ref}) ->
    %% Show some unique representation
    ["?u" | integer_to_list(erlang:phash2(Ref, 16384)) ];
pp({tvar, _, Name}) ->
    Name;
pp({if_t, _, Id, Then, Else}) ->
    ["if(", pp([Id, Then, Else]), ")"];
pp({tuple_t, _, []}) ->
    "unit";
pp({tuple_t, _, Cpts}) ->
    ["(", string:join(lists:map(fun pp/1, Cpts), " * "), ")"];
pp({bytes_t, _, any}) -> "bytes(_)";
pp({bytes_t, _, Len}) ->
    ["bytes(", integer_to_list(Len), ")"];
pp({app_t, _, T, []}) ->
    pp(T);
pp({app_t, _, Type, Args}) ->
    [pp(Type), "(", pp(Args), ")"];
pp({named_arg_t, _, Name, Type, _Default}) ->
    [pp(Name), " : ", pp(Type)];
pp({fun_t, _, Named = {uvar, _, _}, As, B}) ->
    ["(", pp(Named), " | ", pp(As), ") => ", pp(B)];
pp({fun_t, _, Named, As, B}) when is_list(Named) ->
    ["(", pp(Named ++ As), ") => ", pp(B)];
pp(Other) ->
    io_lib:format("~p", [Other]).

%% -- Pre-type checking desugaring -------------------------------------------

%% Desugars nested record/map updates as follows:
%%  { x.y = v1, x.z @ z = f(z) } becomes { x @ __x = __x { y = v1, z @ z = f(z) } }
%%  { [k1].x = v1, [k2].y = v2 } becomes { [k1] @ __x = __x { x = v1 }, [k2] @ __x = __x { y = v2 } }
%% There's no comparison of k1 and k2 to group the updates if they are equal.
desugar({record, Ann, Rec, Updates}) ->
    {record, Ann, Rec, desugar_updates(Updates)};
desugar({map, Ann, Map, Updates}) ->
    {map, Ann, Map, desugar_updates(Updates)};
desugar([H|T]) ->
  [desugar(H) | desugar(T)];
desugar(T) when is_tuple(T) ->
  list_to_tuple(desugar(tuple_to_list(T)));
desugar(X) -> X.

desugar_updates([]) -> [];
desugar_updates([Upd | Updates]) ->
    {Key, MakeField, Rest} = update_key(Upd),
    {More, Updates1}       = updates_key(Key, Updates),
    %% Check conflicts
    case length([ [] || [] <- [Rest | More] ]) of
        N when N > 1 -> type_error({conflicting_updates_for_field, Upd, Key});
        _ -> ok
    end,
    [MakeField(lists:append([Rest | More])) | desugar_updates(Updates1)].

%% TODO: refactor representation to make this not horrible
update_key(Fld = {field, _, [Elim], _}) ->
    {elim_key(Elim), fun(_) -> Fld end, []};
update_key(Fld = {field, _, [Elim], _, _}) ->
    {elim_key(Elim), fun(_) -> Fld end, []};
update_key({field, Ann, [P = {proj, _, {id, _, Name}} | Rest], Value}) ->
    {Name, fun(Flds) -> {field, Ann, [P], {id, [], "__x"},
                            desugar(map_or_record(Ann, {id, [], "__x"}, Flds))}
           end, [{field, Ann, Rest, Value}]};
update_key({field, Ann, [P = {proj, _, {id, _, Name}} | Rest], Id, Value}) ->
    {Name, fun(Flds) -> {field, Ann, [P], {id, [], "__x"},
                            desugar(map_or_record(Ann, {id, [], "__x"}, Flds))}
           end, [{field, Ann, Rest, Id, Value}]};
update_key({field, Ann, [K = {map_get, _, _} | Rest], Value}) ->
    {map_key, fun(Flds) -> {field, Ann, [K], {id, [], "__x"},
                            desugar(map_or_record(Ann, {id, [], "__x"}, Flds))}
              end, [{field, Ann, Rest, Value}]};
update_key({field, Ann, [K = {map_get, _, _, _} | Rest], Value}) ->
    {map_key, fun(Flds) -> {field, Ann, [K], {id, [], "__x"},
                            desugar(map_or_record(Ann, {id, [], "__x"}, Flds))}
              end, [{field, Ann, Rest, Value}]};
update_key({field, Ann, [K = {map_get, _, _, _} | Rest], Id, Value}) ->
    {map_key, fun(Flds) -> {field, Ann, [K], {id, [], "__x"},
                            desugar(map_or_record(Ann, {id, [], "__x"}, Flds))}
              end, [{field, Ann, Rest, Id, Value}]};
update_key({field, Ann, [K = {map_get, _, _} | Rest], Id, Value}) ->
    {map_key, fun(Flds) -> {field, Ann, [K], {id, [], "__x"},
                            desugar(map_or_record(Ann, {id, [], "__x"}, Flds))}
              end, [{field, Ann, Rest, Id, Value}]}.

map_or_record(Ann, Val, Flds = [Fld | _]) ->
    Kind = case element(3, Fld) of
             [{proj, _, _}       | _] -> record;
             [{map_get, _, _}    | _] -> map;
             [{map_get, _, _, _} | _] -> map
           end,
    {Kind, Ann, Val, Flds}.

elim_key({proj, _, {id, _, Name}}) -> Name;
elim_key({map_get, _, _, _})       -> map_key;  %% no grouping on map keys (yet)
elim_key({map_get, _, _})          -> map_key.

updates_key(map_key, Updates) -> {[], Updates};
updates_key(Name, Updates) ->
    Xs = [ {Upd, Name1 == Name, Rest}
           || Upd <- Updates,
              {Name1, _, Rest} <- [update_key(Upd)] ],
    Updates1 = [ Upd  || {Upd, false, _} <- Xs ],
    More     = [ Rest || {_, true, Rest} <- Xs ],
    {More, Updates1}.

indexed(I, Xs) ->
    lists:zip(lists:seq(I, I + length(Xs) - 1), Xs).

