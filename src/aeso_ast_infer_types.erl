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
        , unfold_types_in_type/2
        , unfold_types_in_type/3
          %% TODO: Newly added
        , get_named_argument_constraint_name/1
        , get_named_argument_constraint_args/1
        , get_named_argument_constraint_type/1
        ]).

%% Newly exported
-export([ fresh_uvar/1
        , freshen_type/2
        , freshen_type_sig/2
        , infer_const/2
        ]).
-export_type([ utype/0
             , typesig/0
             ]).

-include("aeso_utils.hrl").

-type env() :: aeso_tc_env:env().

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

-define(is_type_id(T), element(1, T) =:= id orelse
                       element(1, T) =:= qid orelse
                       element(1, T) =:= con orelse
                       element(1, T) =:= qcon).

-type why_record() :: aeso_syntax:field(aeso_syntax:expr())
                    | {var_args, aeso_syntax:ann(), aeso_syntax:expr()}
                    | {proj, aeso_syntax:ann(), aeso_syntax:expr(), aeso_syntax:id()}.

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

-type type() :: aeso_syntax:type().
-type name() :: string().
-type typesig() :: {type_sig, aeso_syntax:ann(), type_constraints(), [aeso_syntax:named_arg_t()], [type()], type()}.

-type type_constraints() :: none | bytes_concat | bytes_split | address_to_contract | bytecode_hash.

-type variance() :: invariant | covariant | contravariant | bivariant.

-define(PRINT_TYPES(Fmt, Args),
        when_option(pp_types, fun () -> io:format(Fmt, Args) end)).
-define(CONSTRUCTOR_MOCK_NAME, "#__constructor__#").

%% -- Moved functions --------------------------------------------------------

name(A) -> aeso_tc_name_manip:name(A).
qname(A) -> aeso_tc_name_manip:qname(A).
set_qname(A, B) -> aeso_tc_name_manip:set_qname(A, B).

%% -------

type_error(A) -> aeso_tc_errors:type_error(A).
create_type_errors() -> aeso_tc_errors:create_type_errors().
destroy_and_report_type_errors(A) -> aeso_tc_errors:destroy_and_report_type_errors(A).
cannot_unify(A, B, C, D) -> aeso_tc_errors:cannot_unify(A, B, C, D).

%% -------

pp(A) -> aeso_tc_pp:pp(A).

%% -------

create_unused_functions() -> aeso_tc_warnings:create_unused_functions().
destroy_and_report_unused_functions() -> aeso_tc_warnings:destroy_and_report_unused_functions().
destroy_and_report_warnings_as_type_errors() -> aeso_tc_warnings:destroy_and_report_warnings_as_type_errors().
potential_unused_include(A, B) -> aeso_tc_warnings:potential_unused_include(A, B).
potential_unused_typedefs(A, B) -> aeso_tc_warnings:potential_unused_typedefs(A, B).
potential_unused_constants(A, B) -> aeso_tc_warnings:potential_unused_constants(A, B).
potential_unused_stateful(A, B) -> aeso_tc_warnings:potential_unused_stateful(A, B).
potential_unused_variables(A, B, C) -> aeso_tc_warnings:potential_unused_variables(A, B, C).
potential_unused_function(A, B, C, D) -> aeso_tc_warnings:potential_unused_function(A, B, C, D).
mk_warning(A) -> aeso_tc_warnings:mk_warning(A).
used_stateful(A) -> aeso_tc_warnings:used_stateful(A).
warn_potential_negative_spend(A, B, C) -> aeso_tc_warnings:warn_potential_negative_spend(A, B, C).
warn_potential_division_by_zero(A, B, C) -> aeso_tc_warnings:warn_potential_division_by_zero(A, B, C).
potential_unused_return_value(A) -> aeso_tc_warnings:potential_unused_return_value(A).
used_typedef(A, B) -> aeso_tc_warnings:used_typedef(A, B).

%% -------

desugar(A) -> aeso_tc_desugar:desugar(A).
desugar_clauses(A, B, C, D) -> aeso_tc_desugar:desugar_clauses(A, B, C, D).
process_blocks(A) -> aeso_tc_desugar:process_blocks(A).

%% -------

create_options(A) -> aeso_tc_options:create_options(A).
get_option(A, B) -> aeso_tc_options:get_option(A, B).
when_option(A, B) -> aeso_tc_options:when_option(A, B).
when_warning(A, B) -> aeso_tc_options:when_warning(A, B).

%% -- New functions ----------------------------------------------------------

get_named_argument_constraint_name(#named_argument_constraint{name = Name}) -> Name.
get_named_argument_constraint_args(#named_argument_constraint{args = Args}) -> Args.
get_named_argument_constraint_type(#named_argument_constraint{type = Type}) -> Type.

%% -- The rest ---------------------------------------------------------------

map_t(As, K, V) -> {app_t, As, {id, As, "map"}, [K, V]}.

-spec infer(aeso_syntax:ast()) -> {aeso_syntax:ast(), aeso_syntax:ast(), [aeso_warnings:warning()]} | {env(), aeso_syntax:ast(), aeso_syntax:ast(), [aeso_warnings:warning()]}.
infer(Contracts) ->
    infer(Contracts, []).

-type option() :: return_env | dont_unfold | no_code | debug_mode | term().

-spec infer(aeso_syntax:ast(), list(option())) ->
  {aeso_syntax:ast(), aeso_syntax:ast(), [aeso_warnings:warning()]} | {env(), aeso_syntax:ast(), aeso_syntax:ast(), [aeso_warnings:warning()]}.
infer([], Options) ->
    create_type_errors(),
    type_error({no_decls, proplists:get_value(src_file, Options, no_file)}),
    destroy_and_report_type_errors(aeso_tc_env:init_env(Options));
infer(Contracts, Options) ->
    aeso_tc_ets_manager:ets_init(), %% Init the ETS table state
    try
        Env = aeso_tc_env:init_env(Options),
        create_options(Options),
        aeso_tc_ets_manager:ets_new(defined_contracts, [bag]),
        aeso_tc_ets_manager:ets_new(type_vars, [set]),
        aeso_tc_ets_manager:ets_new(warnings, [bag]),
        aeso_tc_ets_manager:ets_new(type_vars_variance, [set]),
        aeso_tc_ets_manager:ets_new(functions_to_implement, [set]),
        %% Set the variance for builtin types
        aeso_tc_ets_manager:ets_insert(type_vars_variance, {"list", [covariant]}),
        aeso_tc_ets_manager:ets_insert(type_vars_variance, {"option", [covariant]}),
        aeso_tc_ets_manager:ets_insert(type_vars_variance, {"map", [covariant, covariant]}),
        aeso_tc_ets_manager:ets_insert(type_vars_variance, {"oracle", [contravariant, covariant]}),
        aeso_tc_ets_manager:ets_insert(type_vars_variance, {"oracle_query", [covariant, covariant]}),

        when_warning(warn_unused_functions, fun() -> create_unused_functions() end),
        check_modifiers(Env, Contracts),
        create_type_errors(),
        Contracts1 = identify_main_contract(Contracts, Options),
        destroy_and_report_type_errors(Env),
        {Env1, Decls} = infer1(Env, Contracts1, [], Options),
        when_warning(warn_unused_functions, fun() -> destroy_and_report_unused_functions() end),
        when_option(warn_error, fun() -> destroy_and_report_warnings_as_type_errors() end),
        WarningsUnsorted = lists:map(fun mk_warning/1, aeso_tc_ets_manager:ets_tab2list(warnings)),
        Warnings = aeso_warnings:sort_warnings(WarningsUnsorted),
        {Env2, DeclsFolded, DeclsUnfolded} =
            case proplists:get_value(dont_unfold, Options, false) of
                true  -> {Env1, Decls, Decls};
                false -> E = aeso_tc_env:on_scopes(Env1, fun(Scope) -> unfold_record_types(Env1, Scope) end),
                         {E, Decls, unfold_record_types(E, Decls)}
            end,
        case proplists:get_value(return_env, Options, false) of
            false -> {DeclsFolded, DeclsUnfolded, Warnings};
            true  -> {Env2, DeclsFolded, DeclsUnfolded, Warnings}
        end
    after
        aeso_tc_ets_manager:clean_up_ets()
    end.

-spec infer1(env(), [aeso_syntax:decl()], [aeso_syntax:decl()], list(option())) ->
    {env(), [aeso_syntax:decl()]}.
infer1(Env, [], Acc, _Options) -> {Env, lists:reverse(Acc)};
infer1(Env0, [Contract0 = {Contract, Ann, ConName, Impls, Code} | Rest], Acc, Options)
  when ?IS_CONTRACT_HEAD(Contract) ->
    %% do type inference on each contract independently.
    Parents = maps:put(name(ConName),
                       [name(Impl) || Impl <- Impls],
                       aeso_tc_env:contract_parents(Env0)),
    Env = aeso_tc_env:set_contract_parents(Parents, Env0),
    check_scope_name_clash(Env, contract, ConName),
    What = case Contract of
               contract_main -> contract;
               contract_child -> contract;
               contract_interface -> contract_interface
           end,
    case What of
        contract -> aeso_tc_ets_manager:ets_insert(defined_contracts, {qname(ConName)});
        contract_interface -> ok
    end,
    check_contract_preserved_payability(Env, ConName, Ann, Impls, Acc, What),
    populate_functions_to_implement(Env, ConName, Impls, Acc),
    Env1 = aeso_tc_env:bind_contract(untyped, Contract0, Env),
    {Env2, Code1} = infer_contract_top(aeso_tc_env:push_scope(contract, ConName, Env1), What, Code, Options),
    report_unimplemented_functions(Env1, ConName),
    Contract1 = {Contract, Ann, ConName, Impls, Code1},
    Env3 = aeso_tc_env:pop_scope(Env2),
    %% Rebinding because the qualifications of types are added during type inference. Could we do better?
    Env4 = aeso_tc_env:bind_contract(typed, Contract1, Env3),
    infer1(Env4, Rest, [Contract1 | Acc], Options);
infer1(Env, [{namespace, Ann, Name, Code} | Rest], Acc, Options) ->
    when_warning(warn_unused_includes,
                 fun() ->
                     SrcFile = proplists:get_value(src_file, Options, no_file),
                     potential_unused_include(Ann, SrcFile)
                 end),
    check_scope_name_clash(Env, namespace, Name),
    {Env1, Code1} = infer_contract_top(aeso_tc_env:push_scope(namespace, Name, Env), namespace, Code, Options),
    Namespace1 = {namespace, Ann, Name, Code1},
    infer1(aeso_tc_env:pop_scope(Env1), Rest, [Namespace1 | Acc], Options);
infer1(Env, [Using = {using, _, _, _, _} | Rest], Acc, Options) ->
    infer1(check_usings(Env, Using), Rest, Acc, Options);
infer1(Env, [{pragma, _, _} | Rest], Acc, Options) ->
    %% Pragmas are checked in check_modifiers
    infer1(Env, Rest, Acc, Options).

-spec check_contract_preserved_payability(env(), Con, Ann, Impls, Contracts, Kind) -> ok | no_return() when
      Con :: aeso_syntax:con(),
      Ann :: aeso_syntax:ann(),
      Impls :: [Con],
      Contracts :: [aeso_syntax:decl()],
      Kind :: contract | contract_interface.
check_contract_preserved_payability(Env, ContractName, ContractAnn, Impls, DefinedContracts, Kind) ->
    Payable = proplists:get_value(payable, ContractAnn, false),
    ImplsNames = [ name(I) || I <- Impls ],
    Interfaces = [ Con || I = {contract_interface, _, Con, _, _} <- DefinedContracts,
                          lists:member(name(Con), ImplsNames),
                          aeso_syntax:get_ann(payable, I, false) ],

    create_type_errors(),
    [ type_error({unpreserved_payablity, Kind, ContractName, I}) || I <- Interfaces, Payable == false ],
    destroy_and_report_type_errors(Env),

    ok.

%% Report all functions that were not implemented by the contract ContractName.
-spec report_unimplemented_functions(env(), ContractName) -> ok | no_return() when
      ContractName :: aeso_syntax:con().
report_unimplemented_functions(Env, ContractName) ->
    create_type_errors(),
    [ type_error({unimplemented_interface_function, ContractName, name(I), FunName})
      || {FunName, I, _} <- aeso_tc_ets_manager:ets_tab2list(functions_to_implement) ],
    destroy_and_report_type_errors(Env).

%% Return a list of all function declarations to be implemented, given the list
%% of interfaces to be implemented Impls and all the previously defined
%% contracts DefinedContracts>
-spec functions_to_implement(Impls, DefinedContracts) -> [{InterfaceCon, FunDecl}] when
      Impls :: [aeso_syntax:con()],
      DefinedContracts :: [aeso_syntax:decl()],
      InterfaceCon :: aeso_syntax:con(),
      FunDecl :: aeso_syntax:fundecl().
functions_to_implement(Impls, DefinedContracts) ->
    ImplsNames = [ name(I) || I <- Impls ],
    Interfaces = [ I || I = {contract_interface, _, Con, _, _} <- DefinedContracts,
                        lists:member(name(Con), ImplsNames) ],

    %% All implemented intrefaces should already be defined
    InterfacesNames = [name(element(3, I)) || I <- Interfaces],
    [ begin
        Found = lists:member(name(Impl), InterfacesNames),
        Found orelse type_error({referencing_undefined_interface, Impl})
      end || Impl <- Impls
    ],

    lists:flatten([ [ {Con, Decl} || Decl <- Decls] || {contract_interface, _, Con, _, Decls} <- Interfaces ]).

%% Fill the ets table functions_to_implement with functions from the implemented
%% interfaces Impls.
-spec populate_functions_to_implement(env(), ContractName, Impls, DefinedContracts) -> ok | no_return() when
      ContractName :: aeso_syntax:con(),
      Impls :: [aeso_syntax:con()],
      DefinedContracts :: [aeso_syntax:decl()].
populate_functions_to_implement(Env, ContractName, Impls, DefinedContracts) ->
    create_type_errors(),
    [ begin
        Inserted = aeso_tc_ets_manager:ets_insert_new(functions_to_implement, {name(Id), I, Decl}),
        [{_, I2, _}] = aeso_tc_ets_manager:ets_lookup(functions_to_implement, name(Id)),
        Inserted orelse type_error({interface_implementation_conflict, ContractName, I, I2, Id})
      end || {I, Decl = {fun_decl, _, Id, _}} <- functions_to_implement(Impls, DefinedContracts) ],
    destroy_and_report_type_errors(Env).

%% Asserts that the main contract is somehow defined.
identify_main_contract(Contracts, Options) ->
    Children   = [C || C = {contract_child, _, _, _, _} <- Contracts],
    Mains      = [C || C = {contract_main, _, _, _, _} <- Contracts],
    case Mains of
        [] -> case Children of
                  [] -> type_error(
                          {main_contract_undefined,
                           [{file, File} || {src_file, File} <- Options]});
                  [{contract_child, Ann, Con, Impls, Body}] ->
                      (Contracts -- Children) ++ [{contract_main, Ann, Con, Impls, Body}];
                  [H|_] -> type_error({ambiguous_main_contract,
                                       aeso_syntax:get_ann(H)})
              end;
        [_] -> (Contracts -- Mains) ++ Mains; %% Move to the end
        [H|_] -> type_error({multiple_main_contracts,
                             aeso_syntax:get_ann(H)})
    end.

check_scope_name_clash(Env, Kind, Name) ->
    case aeso_tc_env:get_scope(Env, qname(Name)) of
        false -> ok;
        Scope ->
            K   = aeso_tc_env:scope_kind(Scope),
            Ann = aeso_tc_env:scope_ann(Scope),
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
    Env  = aeso_tc_env:set_what(What, Env0),
    Kind = fun({type_def, _, _, _, _})    -> type;
              ({letfun, _, _, _, _, _})   -> function;
              ({fun_clauses, _, _, _, _}) -> function;
              ({fun_decl, _, _, _})       -> prototype;
              ({using, _, _, _, _})       -> using;
              ({letval, _, _, _})         -> constant;
              (_)                         -> unexpected
           end,
    Get = fun(K, In) -> [ Def || Def <- In, Kind(Def) == K ] end,
    OldUsedNamespaces = aeso_tc_env:used_namespaces(Env),
    Env01 = check_usings(Env, Get(using, Defs)),
    {Env1, TypeDefs} = check_typedefs(Env01, Get(type, Defs)),
    when_warning(warn_unused_typedefs, fun() -> potential_unused_typedefs(aeso_tc_env:namespace(Env), TypeDefs) end),
    create_type_errors(),
    check_unexpected(Get(unexpected, Defs)),
    Env2 =
        case What of
            namespace          -> Env1;
            contract_interface -> Env1;
            contract           -> aeso_tc_env:bind_state(Env1)   %% bind state and put
        end,
    {Env2C, Consts} = check_constants(Env2, Get(constant, Defs)),
    {ProtoSigs, Decls} = lists:unzip([ check_fundecl(Env2C, Decl) || Decl <- Get(prototype, Defs) ]),
    [ type_error({missing_definition, Id}) || {fun_decl, _, Id, _} <- Decls,
                                              What =:= contract,
                                              get_option(no_code, false) =:= false ],
    Env3      = aeso_tc_env:bind_funs(ProtoSigs, Env2C),
    Functions = Get(function, Defs),
    %% Check for duplicates in Functions (we turn it into a map below)
    FunBind   = fun({letfun, Ann, {id, _, Fun}, _, _, _})   -> {Fun, {tuple_t, Ann, []}};
                   ({fun_clauses, Ann, {id, _, Fun}, _, _}) -> {Fun, {tuple_t, Ann, []}} end,
    FunName   = fun(Def) -> {Name, _} = FunBind(Def), Name end,
    _         = aeso_tc_env:bind_funs(lists:map(FunBind, Functions), aeso_tc_env:empty_env()),
    FunMap    = maps:from_list([ {FunName(Def), Def} || Def <- Functions ]),
    check_reserved_entrypoints(FunMap),
    DepGraph  = maps:map(fun(_, Def) -> aeso_syntax_utils:used_ids(Def) end, FunMap),
    SCCs      = aeso_utils:scc(DepGraph),
    {Env4, Defs1} = check_sccs(Env3, FunMap, SCCs, []),
    %% Remove namespaces used in the current namespace
    Env5 = aeso_tc_env:set_used_namespaces(OldUsedNamespaces, Env4),
    %% Check that `init` doesn't read or write the state and that `init` is not missing
    check_state(Env4, Defs1),
    %% Check that entrypoints have first-order arg types and return types
    check_entrypoints(Defs1),
    destroy_and_report_type_errors(Env4),
    %% Add inferred types of definitions
    {Env5, TypeDefs ++ Decls ++ Consts ++ Defs1}.

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
check_typedefs(Env, Defs) ->
    create_type_errors(),
    GetName  = fun({type_def, _, {id, _, Name}, _, _}) -> Name end,
    TypeMap  = maps:from_list([ {GetName(Def), Def} || Def <- Defs ]),
    DepGraph = maps:map(fun(_, Def) -> aeso_syntax_utils:used_types(aeso_tc_env:namespace(Env), Def) end, TypeMap),
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
            check_parameterizable(D, Xs),
            Def  = check_event(Env, Name, Ann, check_typedef(aeso_tc_env:bind_tvars(Xs, Env), Def0)),
            Acc1 = [{type_def, Ann, D, Xs, Def} | Acc],
            Env1 = aeso_tc_env:bind_type(Name, Ann, {Xs, Def}, Env),
            case Def of
                {alias_t, _}  -> check_typedef_sccs(Env1, TypeMap, SCCs, Acc1);
                {record_t, []} ->
                    type_error({empty_record_definition, Ann, Name}),
                    check_typedef_sccs(Env1, TypeMap, SCCs, Acc1);
                {record_t, Fields} ->
                    aeso_tc_ets_manager:ets_insert(type_vars_variance, {aeso_tc_env:namespace(Env) ++ qname(D),
                                                    infer_type_vars_variance(Xs, Fields)}),
                    %% check_type to get qualified name
                    RecTy = check_type(Env1, app_t(Ann, D, Xs)),
                    Env2 = aeso_tc_env:bind_fields_append(Env1, TypeMap, RecTy, Fields),
                    check_typedef_sccs(Env2, TypeMap, SCCs, Acc1);
                {variant_t, Cons} ->
                    aeso_tc_ets_manager:ets_insert(type_vars_variance, {aeso_tc_env:namespace(Env) ++ qname(D),
                                                    infer_type_vars_variance(Xs, Cons)}),
                    Target   = check_type(Env1, app_t(Ann, D, Xs)),
                    ConType  = fun([]) -> Target; (Args) -> {type_sig, Ann, none, [], Args, Target} end,
                    ConTypes = [ begin
                                    {constr_t, _, {con, _, Con}, Args} = ConDef,
                                    {Con, ConType(Args)}
                                 end || ConDef <- Cons ],
                    check_repeated_constructors([ {Con, ConType(Args)} || {constr_t, _, Con, Args} <- Cons ]),
                    [ check_constructor_overlap(Env1, Con, Target) || {constr_t, _, Con, _} <- Cons ],
                    check_typedef_sccs(aeso_tc_env:bind_funs(ConTypes, Env1), TypeMap, SCCs, Acc1)
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

infer_type_vars_variance(TypeParams, Cons) ->
    % args from all type constructors
    FlatArgs = lists:flatten([Args || {constr_t, _, _, Args} <- Cons]) ++ [Type || {field_t, _, _, Type} <- Cons],

    Vs = lists:flatten([infer_type_vars_variance(Arg) || Arg <- FlatArgs]),
    lists:map(fun({tvar, _, TVar}) ->
                      S = sets:from_list([Variance || {TV, Variance} <- Vs, TV == TVar]),
                      IsCovariant     = sets:is_element(covariant, S),
                      IsContravariant = sets:is_element(contravariant, S),
                      case {IsCovariant, IsContravariant} of
                          {true,   true} -> invariant;
                          {true,  false} -> covariant;
                          {false,  true} -> contravariant;
                          {false, false} -> bivariant
                      end
              end, TypeParams).

-spec infer_type_vars_variance(utype()) -> [{name(), variance()}].
infer_type_vars_variance(Types)
  when is_list(Types) ->
    lists:flatten([infer_type_vars_variance(T) || T <- Types]);
infer_type_vars_variance({app_t, _, Type, Args}) ->
    Variances = case aeso_tc_ets_manager:ets_lookup(type_vars_variance, qname(Type)) of
                    [{_, Vs}] -> Vs;
                    _ -> lists:duplicate(length(Args), covariant)
                end,
    TypeVarsVariance = [{TVar, Variance}
                        || {{tvar, _, TVar}, Variance} <- lists:zip(Args, Variances)],
    TypeVarsVariance;
infer_type_vars_variance({tvar, _, TVar}) -> [{TVar, covariant}];
infer_type_vars_variance({fun_t, _, [], Args, Res}) ->
    ArgsVariance = infer_type_vars_variance(Args),
    ResVariance = infer_type_vars_variance(Res),
    FlippedArgsVariance = lists:map(fun({TVar, Variance}) -> {TVar, opposite_variance(Variance)} end, ArgsVariance),
    FlippedArgsVariance ++ ResVariance;
infer_type_vars_variance(_) -> [].

opposite_variance(invariant) -> invariant;
opposite_variance(covariant) -> contravariant;
opposite_variance(contravariant) -> covariant;
opposite_variance(bivariant) -> bivariant.

-spec check_constants(env(), [aeso_syntax:decl()]) -> {env(), [aeso_syntax:decl()]}.
check_constants(Env, Consts) ->
    HasValidId = fun({letval, _, {id, _, _}, _})                -> true;
                    ({letval, _, {typed, _, {id, _, _}, _}, _}) -> true;
                    (_)                                         -> false
                 end,
    {Valid, Invalid} = lists:partition(HasValidId, Consts),
    [ type_error({invalid_const_id, aeso_syntax:get_ann(Pat)}) || {letval, _, Pat, _} <- Invalid ],
    [ type_error({illegal_const_in_interface, Ann}) || {letval, Ann, _, _} <- Valid, aeso_tc_env:what(Env) == contract_interface ],
    when_warning(warn_unused_constants, fun() -> potential_unused_constants(Env, Valid) end),
    ConstMap = maps:from_list([ {name(Id), Const} || Const = {letval, _, Id, _} <- Valid ]),
    DepGraph = maps:map(fun(_, Const) -> aeso_syntax_utils:used_ids(Const) end, ConstMap),
    SCCs = aeso_utils:scc(DepGraph),
    aeso_tc_env:bind_consts(Env, ConstMap, SCCs, []).

check_usings(Env, []) ->
    Env;
check_usings(Env, [{using, Ann, Con, Alias, Parts} | Rest]) ->
    AliasName = case Alias of
                    none ->
                        none;
                    _ ->
                        qname(Alias)
                end,
    case aeso_tc_env:get_scope(Env, qname(Con)) of
        false ->
            create_type_errors(),
            type_error({using_undefined_namespace, Ann, qname(Con)}),
            destroy_and_report_type_errors(Env);
        Scope ->
            case aeso_tc_env:scope_kind(Scope) of
                contract ->
                    create_type_errors(),
                    type_error({using_undefined_namespace, Ann, qname(Con)}),
                    destroy_and_report_type_errors(Env);
                _ ->
                    Nsp = case Parts of
                            none ->
                                {qname(Con), AliasName, none};
                            {ForOrHiding, Ids} ->
                                IsUndefined = fun(Id) ->
                                                    proplists:lookup(name(Id), aeso_tc_env:scope_funs(Scope)) == none
                                                end,
                                UndefinedIds = lists:filter(IsUndefined, Ids),
                                case UndefinedIds of
                                    [] ->
                                        {qname(Con), AliasName, {ForOrHiding, lists:map(fun name/1, Ids)}};
                                    _ ->
                                        create_type_errors(),
                                        type_error({using_undefined_namespace_parts, Ann, qname(Con), lists:map(fun qname/1, UndefinedIds)}),
                                        destroy_and_report_type_errors(Env)
                                end
                        end,
                    check_usings(aeso_tc_env:set_used_namespaces(aeso_tc_env:used_namespaces(Env) ++ [Nsp], Env), Rest)
            end
    end;
check_usings(Env, Using = {using, _, _, _, _}) ->
    check_usings(Env, [Using]).

check_unexpected(Xs) ->
    [ type_error(X) || X <- Xs ].

check_modifiers(Env, Contracts) ->
    create_type_errors(),
    check_modifiers_(Env, Contracts),
    destroy_and_report_type_errors(Env).

check_modifiers_(Env, [{Contract, _, Con, _Impls, Decls} | Rest])
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
check_modifiers_(Env, [{using, _, _, _, _} | Rest]) ->
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
    case aeso_tc_env:lookup_type(Env, X) of
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

-spec check_tvar(env(), aeso_syntax:tvar()) -> aeso_syntax:tvar() | no_return().
check_tvar(Env, T = {tvar, _, X}) ->
    TVars = aeso_tc_env:typevars(Env),
    case TVars == unrestricted orelse lists:member(X, TVars) of
        true  -> ok;
        false -> type_error({unbound_type, T})
    end,
    T.

ensure_base_type(Type, Arity) ->
    [ type_error({wrong_type_arguments, Type, Arity, 0}) || Arity /= 0 ],
    ok.

-spec check_named_arg(env(), aeso_syntax:named_arg_t()) -> aeso_syntax:named_arg_t().
check_named_arg(Env, {named_arg_t, Ann, Id, Type, Default}) ->
    Type1 = check_type(Env, Type),
    {typed, _, Default1, _} = check_expr(Env, Default, Type1),
    {named_arg_t, Ann, Id, Type1, Default1}.

check_parameterizable({id, Ann, "event"}, [_ | _]) ->
    type_error({parameterized_event, Ann});
check_parameterizable({id, Ann, "state"}, [_ | _]) ->
    type_error({parameterized_state, Ann});
check_parameterizable(_Name, _Xs) ->
    ok.

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
    case aeso_tc_env:lookup_env(Env, term, Ann, Name) of
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
check_sccs(Env, Funs, [{acyclic, X} | SCCs], Acc) ->
    case maps:get(X, Funs, undefined) of
        undefined ->    %% Previously defined function
            check_sccs(Env, Funs, SCCs, Acc);
        Def ->
            {{_, TypeSig}, Def1} = infer_nonrec(Env, Def),
            Env1 = aeso_tc_env:bind_fun(X, TypeSig, Env),
            check_sccs(Env1, Funs, SCCs, [Def1 | Acc])
    end;
check_sccs(Env, Funs, [{cyclic, Xs} | SCCs], Acc) ->
    Defs = [ maps:get(X, Funs) || X <- Xs ],
    {TypeSigs, Defs1} = infer_letrec(Env, Defs),
    Env1 = aeso_tc_env:bind_funs(TypeSigs, Env),
    check_sccs(Env1, Funs, SCCs, Defs1 ++ Acc).

check_reserved_entrypoints(Funs) ->
    Reserved = ["address"],
    _ = [ type_error({reserved_entrypoint, Name, Def})
            || {Name, Def} <- maps:to_list(Funs), lists:member(Name, Reserved) ],
    ok.

-spec check_fundecl(env(), aeso_syntax:decl()) -> {{name(), typesig()}, aeso_syntax:decl()}.
check_fundecl(Env, {fun_decl, Ann, Id = {id, _, Name}, Type = {fun_t, _, _, _, _}}) ->
    Type1 = {fun_t, _, Named, Args, Ret} = check_type(Env, Type),
    TypeSig = {type_sig, Ann, none, Named, Args, Ret},
    register_implementation(Id, TypeSig),
    {{Name, TypeSig}, {fun_decl, Ann, Id, Type1}};
check_fundecl(Env, {fun_decl, Ann, Id = {id, _, Name}, Type}) ->
    type_error({fundecl_must_have_funtype, Ann, Id, Type}),
    {{Name, {type_sig, Ann, none, [], [], Type}}, check_type(Env, Type)}.

%% Register the function FunId as implemented by deleting it from the functions
%% to be implemented table if it is included there, or return true otherwise.
-spec register_implementation(FunId, FunSig) -> true | no_return() when
      FunId :: aeso_syntax:id(),
      FunSig :: typesig().
register_implementation(Id, Sig) ->
    Name = name(Id),
    case aeso_tc_ets_manager:ets_lookup(functions_to_implement, Name) of
        [{Name, Interface, Decl = {fun_decl, _, DeclId, _}}] ->
            DeclStateful   = aeso_syntax:get_ann(stateful,   Decl, false),
            DeclPayable    = aeso_syntax:get_ann(payable,    Decl, false),

            SigEntrypoint = aeso_syntax:get_ann(entrypoint, Sig, false),
            SigStateful   = aeso_syntax:get_ann(stateful,   Sig, false),
            SigPayable    = aeso_syntax:get_ann(payable,    Sig, false),

            [ type_error({function_should_be_entrypoint, Id, DeclId, Interface})
                || not SigEntrypoint ],

            [ type_error({entrypoint_cannot_be_stateful, Id, DeclId, Interface})
                || SigStateful andalso not DeclStateful ],

            [ type_error({entrypoint_must_be_payable, Id, DeclId, Interface})
                || not SigPayable andalso DeclPayable ],

            aeso_tc_ets_manager:ets_delete(functions_to_implement, Name);
        [] ->
            true;
        _ ->
            error("Ets set has multiple keys")
    end.

infer_nonrec(Env, LetFun) ->
    create_constraints(),
    NewLetFun = {{_, Sig}, _} = infer_letfun(Env, LetFun),
    check_special_funs(Env, NewLetFun),
    register_implementation(get_letfun_id(LetFun), Sig),
    solve_then_destroy_and_report_unsolved_constraints(Env),
    Result = {TypeSig, _} = aeso_tc_type_utils:instantiate(NewLetFun),
    print_typesig(TypeSig),
    Result.

%% Currenty only the init function.
check_special_funs(Env, {{"init", Type}, _}) ->
    {type_sig, Ann, _Constr, _Named, _Args, Res} = Type,
    State =
        %% We might have implicit (no) state.
        case aeso_tc_env:lookup_type(Env, {id, [], "state"}) of
            false  -> {tuple_t, [{origin, system}], []};
            {S, _} -> {qid, [], S}
        end,
    unify(Env, Res, State, {checking_init_type, Ann});
check_special_funs(_, _) -> ok.

infer_letrec(Env, Defs) ->
    create_constraints(),
    Funs = lists:map(fun({letfun, _, {id, Ann, Name}, _, _, _})   -> {Name, fresh_uvar(Ann)};
                        ({fun_clauses, _, {id, Ann, Name}, _, _}) -> {Name, fresh_uvar(Ann)}
                     end, Defs),
    ExtendEnv = aeso_tc_env:bind_funs(Funs, Env),
    Inferred =
        [ begin
            Res    = {{Name, TypeSig}, LetFun} = infer_letfun(ExtendEnv, LF),
            register_implementation(get_letfun_id(LetFun), TypeSig),
            Got    = proplists:get_value(Name, Funs),
            Expect = aeso_tc_type_utils:typesig_to_fun_t(TypeSig),
            unify(Env, Got, Expect, {check_typesig, Name, Got, Expect}),
            solve_constraints(Env),
            ?PRINT_TYPES("Checked ~s : ~s\n",
                         [Name, pp(aeso_tc_type_utils:dereference_deep(Got))]),
            Res
          end || LF <- Defs ],
    solve_then_destroy_and_report_unsolved_constraints(Env),
    TypeSigs = aeso_tc_type_utils:instantiate([Sig || {Sig, _} <- Inferred]),
    NewDefs  = aeso_tc_type_utils:instantiate([D || {_, D} <- Inferred]),
    [print_typesig(S) || S <- TypeSigs],
    {TypeSigs, NewDefs}.

infer_letfun(Env, {fun_clauses, Ann, Fun = {id, _, Name}, Type, Clauses}) ->
    when_warning(warn_unused_stateful, fun() -> potential_unused_stateful(Ann, Fun) end),
    when_warning(warn_unused_functions,
                 fun() -> potential_unused_function(Env, Ann, aeso_tc_env:namespace(Env) ++ qname(Fun), Fun) end),
    Type1 = check_type(Env, Type),
    {NameSigs, Clauses1} = lists:unzip([ infer_letfun1(Env, Clause) || Clause <- Clauses ]),
    {_, Sigs = [Sig | _]} = lists:unzip(NameSigs),
    _ = [ begin
            ClauseT = aeso_tc_type_utils:typesig_to_fun_t(ClauseSig),
            unify(Env, ClauseT, Type1, {check_typesig, Name, ClauseT, Type1})
          end || ClauseSig <- Sigs ],
    {{Name, Sig}, desugar_clauses(Ann, Fun, Sig, Clauses1)};
infer_letfun(Env, LetFun = {letfun, Ann, Fun, _, _, _}) ->
    when_warning(warn_unused_stateful, fun() -> potential_unused_stateful(Ann, Fun) end),
    when_warning(warn_unused_functions, fun() -> potential_unused_function(Env, Ann, aeso_tc_env:namespace(Env) ++ qname(Fun), Fun) end),
    {{Name, Sig}, Clause} = infer_letfun1(Env, LetFun),
    {{Name, Sig}, desugar_clauses(Ann, Fun, Sig, [Clause])}.

infer_letfun1(Env0, {letfun, Attrib, Fun = {id, NameAttrib, Name}, Args, What, GuardedBodies}) ->
    Env1 = aeso_tc_env:set_stateful(aeso_syntax:get_ann(stateful, Attrib, false), Env0),
    Env = aeso_tc_env:set_current_function(Fun, Env1),
    {NewEnv, {typed, _, {tuple, _, TypedArgs}, {tuple_t, _, ArgTypes}}} = infer_pattern(Env, {tuple, [{origin, system} | NameAttrib], Args}),
    when_warning(warn_unused_variables, fun() -> potential_unused_variables(aeso_tc_env:namespace(Env0), Name, free_vars(Args)) end),
    ExpectedType = check_type(Env, arg_type(NameAttrib, What)),
    InferGuardedBodies = fun({guarded, Ann, Guards, Body}) ->
        NewGuards = lists:map(fun(Guard) ->
                                  check_expr(aeso_tc_env:set_in_guard(true, NewEnv), Guard, {id, Attrib, "bool"})
                              end, Guards),
        NewBody = check_expr(NewEnv, Body, ExpectedType),
        {guarded, Ann, NewGuards, NewBody}
    end,
    NewGuardedBodies = [{guarded, _, _, {typed, _, _, ResultType}} | _] = lists:map(InferGuardedBodies, GuardedBodies),
    NamedArgs = [],
    TypeSig = {type_sig, Attrib, none, NamedArgs, ArgTypes, ResultType},
    {{Name, TypeSig},
     {letfun, Attrib, {id, NameAttrib, Name}, TypedArgs, ResultType, NewGuardedBodies}}.

get_letfun_id({fun_clauses, _, Id, _, _}) -> Id;
get_letfun_id({letfun, _, Id, _, _, _})   -> Id.

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

%% Hack: don't allow passing the 'value' named arg if not stateful. This only
%% works since the user can't create functions with named arguments.
check_stateful_named_arg(Env, {id, _, "value"}, Default) ->
    case Default of
        {int, _, 0} -> ok;
        _           ->
            Fun = aeso_tc_env:current_function(Env),
            case aeso_tc_env:stateful(Env) of
                true  -> when_warning(warn_unused_stateful, fun() -> used_stateful(Fun) end);
                false -> type_error({value_arg_not_allowed, Default, Fun})
            end
    end;
check_stateful_named_arg(_, _, _) -> ok.

check_entrypoints(Defs) ->
    [ ensure_first_order_entrypoint(LetFun)
      || LetFun <- Defs,
         aeso_syntax:get_ann(entrypoint, LetFun, false),
         get_option(allow_higher_order_entrypoints, false) =:= false ].

ensure_first_order_entrypoint({letfun, Ann, Id = {id, _, Name}, Args, Ret, _}) ->
    [ ensure_first_order(ArgType, {higher_order_entrypoint, AnnArg, Id, {argument, ArgId, ArgType}})
      || {typed, AnnArg, ArgId, ArgType} <- Args ],
    [ ensure_first_order(Ret, {higher_order_entrypoint, Ann, Id, {result, Ret}})
      || Name /= "init" ],  %% init can return higher-order values, since they're written to the store
                            %% rather than being returned.
    ok.

ensure_first_order(Type, Err) ->
    is_first_order(Type) orelse type_error(Err).

is_first_order({fun_t, _, _, _, _})    -> false;
is_first_order(Ts) when is_list(Ts)    -> lists:all(fun is_first_order/1, Ts);
is_first_order(Tup) when is_tuple(Tup) -> is_first_order(tuple_to_list(Tup));
is_first_order(_)                      -> true.

ensure_monomorphic(Type, Err) ->
    is_monomorphic(Type) orelse type_error(Err).

is_monomorphic({tvar, _, _})           -> false;
is_monomorphic(Ts) when is_list(Ts)    -> lists:all(fun is_monomorphic/1, Ts);
is_monomorphic(Tup) when is_tuple(Tup) -> is_monomorphic(tuple_to_list(Tup));
is_monomorphic(_)                      -> true.

check_state_init(Env) ->
    Top = aeso_tc_env:namespace(Env),
    StateType = aeso_tc_env:lookup_type(Env, {id, [{origin, system}], "state"}),
    case unfold_types_in_type(Env, StateType) of
        false  ->
            ok;
        {_, {_, {_, {alias_t, {tuple_t, _, []}}}}} ->  %% type state = ()
            ok;
        _ ->
            AnnCon = aeso_tc_env:scope_ann(aeso_tc_env:get_scope(Env, Top)),
            type_error({missing_init_function, {con, AnnCon, lists:last(Top)}})
    end.

%% Check that `init` doesn't read or write the state and that `init` is defined
%% when the state type is not unit
check_state(Env, Defs) ->
    Top       = aeso_tc_env:namespace(Env),
    GetState  = Top ++ ["state"],
    SetState  = Top ++ ["put"],
    Init      = Top ++ ["init"],
    UsedNames = fun(X) -> [{Xs, Ann} || {{term, Xs}, Ann} <- aeso_syntax_utils:used(X)] end,
    Funs      = [ {Top ++ [Name], Fun} || Fun = {letfun, _, {id, _, Name}, _Args, _Type, _GuardedBodies} <- Defs ],
    Deps      = maps:from_list([{Name, UsedNames(Def)} || {Name, Def} <- Funs]),
    case maps:get(Init, Deps, false) of
        false -> get_option(no_code, false) orelse check_state_init(Env);
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
    add_constraint([#is_contract_constraint{ contract_t = Con,
                                        context    = {contract_literal, Body} }]),
    {typed, As, Body, Con};
infer_expr(_Env, Body={id, As, "_"}) ->
    {typed, As, Body, fresh_uvar(As)};
infer_expr(_Env, Body={id, As, "???"}) ->
    T = fresh_uvar(As),
    type_error({hole_found, As, T}),
    {typed, As, Body, T};
infer_expr(Env, Id = {Tag, As, _}) when Tag == id; Tag == qid ->
    {QName, Type} = aeso_tc_env:lookup_name(Env, As, Id),
    {typed, As, QName, Type};
infer_expr(Env, Id = {Tag, As, _}) when Tag == con; Tag == qcon ->
    {QName, Type} = aeso_tc_env:lookup_name(Env, As, Id, [freshen]),
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
    {'case', _, NewPattern, [{guarded, _, [], NewRest}]} =
        infer_case( Env
                  , AsLC
                  , Pattern
                  , PatType
                  , [{guarded, AsLC, [], {list_comp, AsLC, Yield, Rest}}]
                  , BlockType),
    {typed, _, {list_comp, _, TypedYield, TypedRest}, ResType} = NewRest,
    { typed
    , AsLC
    , {list_comp, AsLC, TypedYield, [{letval, AsLV, NewPattern, NewE}|TypedRest]}
    , ResType
    };
infer_expr(Env, {list_comp, AsLC, Yield, [Def={letfun, AsLF, _, _, _, _}|Rest]}) ->
    {{Name, TypeSig}, LetFun} = infer_letfun(Env, Def),
    FunT = aeso_tc_type_utils:typesig_to_fun_t(TypeSig),
    NewE = aeso_tc_env:bind_var({id, AsLF, Name}, FunT, Env),
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
            NewFun1 = {typed, _, FunName, FunType} = infer_var_args_fun(Env, NewFun0, NamedArgs1, ArgTypes),
            When = {infer_app, Fun, NamedArgs1, Args, FunType, ArgTypes},
            GeneralResultType = fresh_uvar(Ann),
            ResultType = fresh_uvar(Ann),
            unify(Env, FunType, {fun_t, [], NamedArgsVar, ArgTypes, GeneralResultType}, When),
            when_warning(warn_negative_spend, fun() -> warn_potential_negative_spend(Ann, NewFun1, NewArgs) end),
            [ add_constraint({aens_resolve_type, GeneralResultType})
              || element(3, FunName) =:= ["AENS", "resolve"] ],
            [ add_constraint({oracle_type, Ann, OType})
              || OType <- [get_oracle_type(FunName, ArgTypes, GeneralResultType)],
                 OType =/= false ],
            add_constraint(
              #dependent_type_constraint{ named_args_t = NamedArgsVar,
                                          named_args   = NamedArgs1,
                                          general_type = GeneralResultType,
                                          specialized_type = ResultType,
                                          context = {check_return, App} }),
            {typed, Ann, {app, Ann, NewFun1, NamedArgs1 ++ NewArgs}, aeso_tc_type_utils:dereference(ResultType)}
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
    NewCases = [infer_case(Env, As, Pattern, ExprType, GuardedBranches, SwitchType)
                || {'case', As, Pattern, GuardedBranches} <- Cases],
    {typed, Attrs, {switch, Attrs, NewExpr, NewCases}, SwitchType};
infer_expr(Env, {record, Attrs, Fields}) ->
    RecordType = fresh_uvar(Attrs),
    NewFields = [{field, A, FieldName, infer_expr(Env, Expr)}
                 || {field, A, FieldName, Expr} <- Fields],
    RecordType1 = unfold_types_in_type(Env, RecordType),
    add_constraint([ #record_create_constraint{
                         record_t = RecordType1,
                         fields   = [ FieldName || {field, _, [{proj, _, FieldName}], _} <- Fields ],
                         context  = Attrs } || not aeso_tc_env:in_pattern(Env) ] ++
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
    add_constraint([#field_constraint{
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
    {'case', _, {typed, _, {tuple, _, NewArgPatterns}, _}, [{guarded, _, [], NewBody}]} =
        infer_case(Env, Attrs, {tuple, Attrs, ArgPatterns}, {tuple_t, Attrs, ArgTypes}, [{guarded, Attrs, [], Body}], ResultType),
    NewArgs = [{arg, As, NewPat, NewT} || {typed, As, NewPat, NewT} <- NewArgPatterns],
    {typed, Attrs, {lam, Attrs, NewArgs, NewBody}, {fun_t, Attrs, [], ArgTypes, ResultType}};
infer_expr(Env, {letpat, Attrs, Id, Pattern}) ->
    NewPattern = {typed, _, _, PatType} = infer_expr(Env, Pattern),
    {typed, Attrs, {letpat, Attrs, check_expr(Env, Id, PatType), NewPattern}, PatType};
infer_expr(Env, Let = {letval, Attrs, _, _}) ->
    type_error({missing_body_for_let, Attrs}),
    infer_expr(Env, {block, Attrs, [Let, abort_expr(Attrs, "missing body")]});
infer_expr(Env, Let = {letfun, Attrs, _, _, _, _}) ->
    type_error({missing_body_for_let, Attrs}),
    infer_expr(Env, {block, Attrs, [Let, abort_expr(Attrs, "missing body")]}).

check_valid_const_expr({bool, _, _}) ->
    true;
check_valid_const_expr({int, _, _}) ->
    true;
check_valid_const_expr({char, _, _}) ->
    true;
check_valid_const_expr({string, _, _}) ->
    true;
check_valid_const_expr({bytes, _, _}) ->
    true;
check_valid_const_expr({account_pubkey, _, _}) ->
    true;
check_valid_const_expr({oracle_pubkey, _, _}) ->
    true;
check_valid_const_expr({oracle_query_id, _, _}) ->
    true;
check_valid_const_expr({contract_pubkey, _, _}) ->
    true;
check_valid_const_expr({id, _, "_"}) ->
    true;
check_valid_const_expr({Tag, _, _}) when Tag == id; Tag == qid; Tag == con; Tag == qcon ->
    true;
check_valid_const_expr({tuple, _, Cpts}) ->
    lists:all(fun(X) -> X end, [ check_valid_const_expr(C) || C <- Cpts ]);
check_valid_const_expr({list, _, Elems}) ->
    lists:all(fun(X) -> X end, [ check_valid_const_expr(Elem) || Elem <- Elems ]);
check_valid_const_expr({list_comp, _, _, _}) ->
    false;
check_valid_const_expr({typed, _, Body, _}) ->
    check_valid_const_expr(Body);
check_valid_const_expr({app, Ann, Fun, Args0}) ->
    {_, Args} = split_args(Args0),
    case aeso_syntax:get_ann(format, Ann) of
        infix ->
            lists:all(fun(X) -> X end, [ check_valid_const_expr(Arg) || Arg <- Args ]);
        prefix ->
            lists:all(fun(X) -> X end, [ check_valid_const_expr(Arg) || Arg <- Args ]);
        _ ->
            %% Applications of data constructors are allowed in constants
            lists:member(element(1, Fun), [con, qcon])
    end;
check_valid_const_expr({'if', _, _, _, _}) ->
    false;
check_valid_const_expr({switch, _, _, _}) ->
    false;
check_valid_const_expr({record, _, Fields}) ->
    lists:all(fun(X) -> X end, [ check_valid_const_expr(Expr) || {field, _, _, Expr} <- Fields ]);
check_valid_const_expr({record, _, _, _}) ->
    false;
check_valid_const_expr({proj, _, Record, _}) ->
    check_valid_const_expr(Record);
% Maps
check_valid_const_expr({map_get, _, _, _}) ->  %% map lookup
    false;
check_valid_const_expr({map_get, _, _, _, _}) ->  %% map lookup with default
    false;
check_valid_const_expr({map, _, KVs}) ->   %% map construction
    lists:all(fun(X) -> X end, [ check_valid_const_expr(K) andalso check_valid_const_expr(V) || {K, V} <- KVs ]);
check_valid_const_expr({map, _, _, _}) -> %% map update
    false;
check_valid_const_expr({block, _, _}) ->
    false;
check_valid_const_expr({record_or_map_error, _, Fields}) ->
    lists:all(fun(X) -> X end, [ check_valid_const_expr(Expr) || {field, _, _, Expr} <- Fields ]);
check_valid_const_expr({record_or_map_error, _, _, _}) ->
    false;
check_valid_const_expr({lam, _, _, _}) ->
    false;
check_valid_const_expr({letpat, _, _, _}) ->
    false;
check_valid_const_expr({letval, _, _, _}) ->
    false;
check_valid_const_expr({letfun, _, _, _, _, _}) ->
    false.

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
    add_constraint(
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
    add_constraint(
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
    add_constraint([#field_constraint{
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
    when_warning(warn_division_by_zero, fun() -> warn_potential_division_by_zero(As, Op, Args) end),
    {typed, As, {app, As, Op, TypedArgs}, ResultType}.

infer_pattern(Env, Pattern) ->
    Vars = free_vars(Pattern),
    Names = [N || {id, _, N} <- Vars, N /= "_"],
    case Names -- lists:usort(Names) of
        [] -> ok;
        Nonlinear -> type_error({non_linear_pattern, Pattern, lists:usort(Nonlinear)})
    end,
    NewEnv = aeso_tc_env:bind_vars([{Var, fresh_uvar(Ann1)} || Var = {id, Ann1, _} <- Vars], aeso_tc_env:set_in_pattern(true, Env)),
    NewPattern = infer_expr(NewEnv, Pattern),
    {aeso_tc_env:set_in_pattern(aeso_tc_env:in_pattern(Env), NewEnv), NewPattern}.

infer_case(Env, Attrs, Pattern, ExprType, GuardedBranches, SwitchType) ->
    {NewEnv, NewPattern = {typed, _, _, PatType}} = infer_pattern(Env, Pattern),

    %% Make sure we are inside a function before warning about potentially unused var
    [ when_warning(warn_unused_variables,
                   fun() -> potential_unused_variables(aeso_tc_env:namespace(Env), Fun, free_vars(Pattern)) end)
      || {id, _, Fun} <- [aeso_tc_env:current_function(Env)] ],

    InferGuardedBranches = fun({guarded, Ann, Guards, Branch}) ->
        NewGuards = lists:map(fun(Guard) ->
                                  check_expr(aeso_tc_env:set_in_guard(true, NewEnv), Guard, {id, Attrs, "bool"})
                              end, Guards),
        NewBranch = check_expr(aeso_tc_env:set_in_pattern(false, NewEnv), Branch, SwitchType),
        {guarded, Ann, NewGuards, NewBranch}
    end,
    NewGuardedBranches = lists:map(InferGuardedBranches, GuardedBranches),
    unify(Env, ExprType, PatType, {case_pat, Pattern, PatType, ExprType}),
    {'case', Attrs, NewPattern, NewGuardedBranches}.

%% NewStmts = infer_block(Env, Attrs, Stmts, BlockType)
infer_block(_Env, Attrs, [], BlockType) ->
    error({impossible, empty_block, Attrs, BlockType});
infer_block(Env, _, [E], BlockType) ->
    [check_expr(Env, E, BlockType)];
infer_block(Env, Attrs, [Def={letfun, Ann, _, _, _, _}|Rest], BlockType) ->
    {{Name, TypeSig}, LetFun} = infer_letfun(Env, Def),
    FunT = aeso_tc_type_utils:typesig_to_fun_t(TypeSig),
    NewE = aeso_tc_env:bind_var({id, Ann, Name}, FunT, Env),
    [LetFun|infer_block(NewE, Attrs, Rest, BlockType)];
infer_block(Env, _, [{letval, Attrs, Pattern, E}|Rest], BlockType) ->
    NewE = {typed, _, _, PatType} = infer_expr(Env, E),
    {'case', _, NewPattern, [{guarded, _, [], {typed, _, {block, _, NewRest}, _}}]} =
        infer_case(Env, Attrs, Pattern, PatType, [{guarded, Attrs, [], {block, Attrs, Rest}}], BlockType),
    [{letval, Attrs, NewPattern, NewE}|NewRest];
infer_block(Env, Attrs, [Using = {using, _, _, _, _} | Rest], BlockType) ->
    infer_block(check_usings(Env, Using), Attrs, Rest, BlockType);
infer_block(Env, Attrs, [E|Rest], BlockType) ->
    NewE = infer_expr(Env, E),
    when_warning(warn_unused_return_value, fun() -> potential_unused_return_value(NewE) end),
    [NewE|infer_block(Env, Attrs, Rest, BlockType)].

infer_const(Env, {letval, Ann, TypedId = {typed, _, Id = {id, _, _}, Type}, Expr}) ->
    check_valid_const_expr(Expr) orelse type_error({invalid_const_expr, Id}),
    NewExpr = check_expr(aeso_tc_env:set_current_const(Id, Env), Expr, Type),
    {letval, Ann, TypedId, NewExpr};
infer_const(Env, {letval, Ann, Id = {id, AnnId, _}, Expr}) ->
    check_valid_const_expr(Expr) orelse type_error({invalid_const_expr, Id}),
    create_constraints(),
    NewExpr = {typed, _, _, Type} = infer_expr(aeso_tc_env:set_current_const(Id, Env), Expr),
    solve_then_destroy_and_report_unsolved_constraints(Env),
    IdType = setelement(2, Type, AnnId),
    NewId = {typed, aeso_syntax:get_ann(Id), Id, IdType},
    aeso_tc_type_utils:instantiate({letval, Ann, NewId, NewExpr}).

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
    T = fresh_uvar(As),     %% allow any type here, check in the backend that we have comparison for it
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
    {fun_t, As, [], [ListType, ListType], ListType};
infer_infix({'|>', As}) ->
    ArgType = fresh_uvar(As),
    ResType = fresh_uvar(As),
    FunType = {fun_t, As, [], [ArgType], ResType},
    {fun_t, As, [], [ArgType, FunType], ResType}.

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
free_vars({letpat, _, Id, Pat}) ->
    free_vars(Id) ++ free_vars(Pat);
free_vars(L) when is_list(L) ->
    [V || Elem <- L,
          V <- free_vars(Elem)].

%% -- Constraints --

create_constraints() ->
    aeso_tc_ets_manager:ets_new(constraints, [ordered_set]).

-spec add_constraint(constraint() | [constraint()]) -> true.
add_constraint(Constraint) ->
    aeso_tc_ets_manager:ets_insert_ordered(constraints, Constraint).

get_constraints() ->
    aeso_tc_ets_manager:ets_tab2list_ordered(constraints).

destroy_constraints() ->
    aeso_tc_ets_manager:ets_delete(constraints).

-spec solve_constraints(env()) -> ok.
solve_constraints(Env) ->
    %% First look for record fields that appear in only one type definition
    IsAmbiguous =
        fun(#field_constraint{
               record_t = RecordType,
               field    = Field={id, _Attrs, FieldName},
               field_t  = FieldType,
               kind     = Kind,
               context  = When }) ->
                Arity = aeso_tc_type_utils:fun_arity(aeso_tc_type_utils:dereference_deep(FieldType)),
                FieldInfos = case Arity of
                                 none -> aeso_tc_env:lookup_record_field(Env, FieldName, Kind);
                                 _    -> aeso_tc_env:lookup_record_field_arity(Env, FieldName, Arity, Kind)
                             end,
                case FieldInfos of
                    [] ->
                        type_error({undefined_field, Field}),
                        false;
                    [Fld] ->
                        FldType = aeso_tc_env:field_info_field_t(Fld),
                        RecType = aeso_tc_env:field_info_record_t(Fld),
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
                end;
           (_) -> true
        end,
    AmbiguousConstraints = lists:filter(IsAmbiguous, get_constraints()),

    % The two passes on AmbiguousConstraints are needed
    solve_ambiguous_constraints(Env, AmbiguousConstraints ++ AmbiguousConstraints).

-spec solve_ambiguous_constraints(env(), [constraint()]) -> ok.
solve_ambiguous_constraints(Env, Constraints) ->
    Unknown = solve_known_record_types(Env, Constraints),
    if Unknown == [] -> ok;
       length(Unknown) < length(Constraints) ->
            %% progress! Keep trying.
            solve_ambiguous_constraints(Env, Unknown);
       true ->
            case solve_unknown_record_types(Env, Unknown) of
                true -> %% Progress!
                    solve_ambiguous_constraints(Env, Unknown);
                _ -> ok %% No progress. Report errors later.
            end
    end.

solve_then_destroy_and_report_unsolved_constraints(Env) ->
    solve_constraints(Env),
    destroy_and_report_unsolved_constraints(Env).

destroy_and_report_unsolved_constraints(Env) ->
    {FieldCs, OtherCs} =
        lists:partition(fun(#field_constraint{}) -> true; (_) -> false end,
                        get_constraints()),
    {CreateCs, OtherCs1} =
        lists:partition(fun(#record_create_constraint{}) -> true; (_) -> false end,
                        OtherCs),
    {ContractCs, OtherCs2} =
        lists:partition(fun(#is_contract_constraint{}) -> true; (_) -> false end, OtherCs1),
    {NamedArgCs, OtherCs3} =
        lists:partition(fun(#dependent_type_constraint{}) -> true;
                           (#named_argument_constraint{}) -> true;
                           (_)                            -> false
                        end, OtherCs2),
    {BytesCs, OtherCs4} =
        lists:partition(fun({is_bytes, _})              -> true;
                           ({add_bytes, _, _, _, _, _}) -> true;
                           (_)                          -> false
                        end, OtherCs3),
    {AensResolveCs, OtherCs5} =
        lists:partition(fun({aens_resolve_type, _}) -> true;
                           (_)                      -> false
                        end, OtherCs4),
    {OracleTypeCs, []} =
        lists:partition(fun({oracle_type, _, _}) -> true;
                           (_)                   -> false
                        end, OtherCs5),

    Unsolved = [ S || S <- [ solve_constraint(Env, aeso_tc_type_utils:dereference_deep(C)) || C <- NamedArgCs ],
                      S == unsolved ],
    [ type_error({unsolved_named_argument_constraint, C}) || C <- Unsolved ],

    Unknown = solve_known_record_types(Env, FieldCs),
    if Unknown == [] -> ok;
       true ->
            case solve_unknown_record_types(Env, Unknown) of
                true   -> ok;
                Errors -> [ type_error(Err) || Err <- Errors ]
            end
    end,

    check_record_create_constraints(Env, CreateCs),
    check_is_contract_constraints(Env, ContractCs),
    check_bytes_constraints(Env, BytesCs),
    check_aens_resolve_constraints(Env, AensResolveCs),
    check_oracle_type_constraints(Env, OracleTypeCs),

    destroy_constraints().

get_oracle_type({qid, _, ["Oracle", "register"]},      _        , OType) -> OType;
get_oracle_type({qid, _, ["Oracle", "query"]},        [OType| _], _    ) -> OType;
get_oracle_type({qid, _, ["Oracle", "get_question"]}, [OType| _], _    ) -> OType;
get_oracle_type({qid, _, ["Oracle", "get_answer"]},   [OType| _], _    ) -> OType;
get_oracle_type({qid, _, ["Oracle", "check"]},        [OType| _], _    ) -> OType;
get_oracle_type({qid, _, ["Oracle", "check_query"]},  [OType| _], _    ) -> OType;
get_oracle_type({qid, _, ["Oracle", "respond"]},      [OType| _], _    ) -> OType;
get_oracle_type(_Fun, _Args, _Ret) -> false.

%% -- Named argument constraints --

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
    NamedArgsT = aeso_tc_type_utils:dereference(NamedArgsT0),
    case aeso_tc_type_utils:dereference(NamedArgsT0) of
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
    case aeso_tc_type_utils:dereference(Type) of
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

%% -- Bytes constraints --

solve_constraint(_Env, #field_constraint{record_t = {uvar, _, _}}) ->
    not_solved;
solve_constraint(Env, C = #field_constraint{record_t = RecType,
                                            field    = FieldName,
                                            field_t  = FieldType,
                                            context  = When}) ->
    RecId = record_type_name(RecType),
    Attrs = aeso_syntax:get_ann(RecId),
    case aeso_tc_env:lookup_type(Env, RecId) of
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
            type_error({not_a_record_type, aeso_tc_type_utils:instantiate(RecType), When}),
            not_solved
    end;
solve_constraint(Env, C = #dependent_type_constraint{}) ->
    check_named_argument_constraint(Env, C);
solve_constraint(Env, C = #named_argument_constraint{}) ->
    check_named_argument_constraint(Env, C);
solve_constraint(_Env, {is_bytes, _}) -> ok;
solve_constraint(Env, {add_bytes, Ann, _, A0, B0, C0}) ->
    A = unfold_types_in_type(Env, aeso_tc_type_utils:dereference(A0)),
    B = unfold_types_in_type(Env, aeso_tc_type_utils:dereference(B0)),
    C = unfold_types_in_type(Env, aeso_tc_type_utils:dereference(C0)),
    case {A, B, C} of
        {{bytes_t, _, M}, {bytes_t, _, N}, _} -> unify(Env, {bytes_t, Ann, M + N}, C, {at, Ann});
        {{bytes_t, _, M}, _, {bytes_t, _, R}} when R >= M -> unify(Env, {bytes_t, Ann, R - M}, B, {at, Ann});
        {_, {bytes_t, _, N}, {bytes_t, _, R}} when R >= N -> unify(Env, {bytes_t, Ann, R - N}, A, {at, Ann});
        _ -> ok
    end;
solve_constraint(_, _) -> ok.

check_bytes_constraints(Env, Constraints) ->
    InAddConstraint = [ T || {add_bytes, _, _, A, B, C} <- Constraints,
                             T <- [A, B, C],
                             element(1, T) /= bytes_t ],
    %% Skip is_bytes constraints for types that occur in add_bytes constraints
    %% (no need to generate error messages for both is_bytes and add_bytes).
    Skip = fun({is_bytes, T}) -> lists:member(T, InAddConstraint);
              (_) -> false end,
    [ check_bytes_constraint(Env, C) || C <- Constraints, not Skip(C) ].

check_bytes_constraint(Env, {is_bytes, Type}) ->
    Type1 = unfold_types_in_type(Env, aeso_tc_type_utils:instantiate(Type)),
    case Type1 of
        {bytes_t, _, _} -> ok;
        _               ->
            type_error({unknown_byte_length, Type})
    end;
check_bytes_constraint(Env, {add_bytes, Ann, Fun, A0, B0, C0}) ->
    A = unfold_types_in_type(Env, aeso_tc_type_utils:instantiate(A0)),
    B = unfold_types_in_type(Env, aeso_tc_type_utils:instantiate(B0)),
    C = unfold_types_in_type(Env, aeso_tc_type_utils:instantiate(C0)),
    case {A, B, C} of
        {{bytes_t, _, _M}, {bytes_t, _, _N}, {bytes_t, _, _R}} ->
            ok; %% If all are solved we checked M + N == R in solve_constraint.
        _ -> type_error({unsolved_bytes_constraint, Ann, Fun, A, B, C})
    end.

check_aens_resolve_constraints(_Env, []) ->
    ok;
check_aens_resolve_constraints(Env, [{aens_resolve_type, Type} | Rest]) ->
    Type1 = unfold_types_in_type(Env, aeso_tc_type_utils:instantiate(Type)),
    {app_t, _, {id, _, "option"}, [Type2]} = Type1,
    case Type2 of
        {id, _, "string"} -> ok;
        {id, _, "address"} -> ok;
        {con, _, _} -> ok;
        {app_t, _, {id, _, "oracle"}, [_, _]} -> ok;
        {app_t, _, {id, _, "oracle_query"}, [_, _]} -> ok;
        _ -> type_error({invalid_aens_resolve_type, aeso_syntax:get_ann(Type), Type2})
    end,
    check_aens_resolve_constraints(Env, Rest).

check_oracle_type_constraints(_Env, []) ->
    ok;
check_oracle_type_constraints(Env, [{oracle_type, Ann, OType} | Rest]) ->
    Type = unfold_types_in_type(Env, aeso_tc_type_utils:instantiate(OType)),
    {app_t, _, {id, _, "oracle"}, [QType, RType]} = Type,
    ensure_monomorphic(QType, {invalid_oracle_type, polymorphic,  query,    Ann, Type}),
    ensure_monomorphic(RType, {invalid_oracle_type, polymorphic,  response, Ann, Type}),
    ensure_first_order(QType, {invalid_oracle_type, higher_order, query,    Ann, Type}),
    ensure_first_order(RType, {invalid_oracle_type, higher_order, response, Ann, Type}),
    check_oracle_type_constraints(Env, Rest).

%% -- Field constraints --

check_record_create_constraints(_, []) -> ok;
check_record_create_constraints(Env, [C | Cs]) ->
    #record_create_constraint{
        record_t = Type,
        fields   = Fields,
        context  = When } = C,
    Type1 = unfold_types_in_type(Env, aeso_tc_type_utils:instantiate(Type)),
    try aeso_tc_env:lookup_type(Env, record_type_name(Type1)) of
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
    aeso_tc_ets_manager:ets_lookup(defined_contracts, qname(C)) =/= [].

check_is_contract_constraints(_Env, []) -> ok;
check_is_contract_constraints(Env, [C | Cs]) ->
    #is_contract_constraint{ contract_t = Type, context = Cxt, force_def = ForceDef } = C,
    Type1 = unfold_types_in_type(Env, aeso_tc_type_utils:instantiate(Type)),
    TypeName = record_type_name(Type1),
    case aeso_tc_env:lookup_type(Env, TypeName) of
        {_, {_Ann, {[], {contract_t, _}}}} ->
            case not ForceDef orelse is_contract_defined(TypeName) of
                true -> ok;
                false -> type_error({contract_lacks_definition, Type1, Cxt})
                end;
        _ -> type_error({not_a_contract_type, Type1, Cxt})
    end,
    check_is_contract_constraints(Env, Cs).

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

%% This will solve all kinds of constraints but will only return the
%% unsolved field constraints
-spec solve_known_record_types(env(), [constraint()]) -> [field_constraint()].
solve_known_record_types(Env, Constraints) ->
    DerefConstraints = lists:map(fun(C = #field_constraint{record_t = RecordType}) ->
                                        C#field_constraint{record_t = aeso_tc_type_utils:dereference(RecordType)};
                                    (C) -> aeso_tc_type_utils:dereference_deep(C)
                                 end, Constraints),
    SolvedConstraints = lists:map(fun(C) -> solve_constraint(Env, aeso_tc_type_utils:dereference_deep(C)) end, DerefConstraints),
    Unsolved = DerefConstraints--SolvedConstraints,
    lists:filter(fun(#field_constraint{}) -> true; (_) -> false end, Unsolved).

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
    Candidates = [aeso_tc_env:field_info_record_t(Fld) || Fld <- aeso_tc_env:lookup_record_field(Env, hd(FieldNames))],
    TypesAndFields = [case aeso_tc_env:lookup_type(Env, record_type_name(RecType)) of
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
            {_, {_, {Formals, {_RecOrCon, _}}}} = aeso_tc_env:lookup_type(Env, RecName),
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
    case aeso_tc_env:lookup_type(Env, Id) of
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
    case aeso_tc_env:lookup_type(Env, Id) of
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

fresh_uvar(Attrs) ->
    {uvar, Attrs, make_ref()}.

create_freshen_tvars() ->
    aeso_tc_ets_manager:ets_new(freshen_tvars, [set]).

destroy_freshen_tvars() ->
    aeso_tc_ets_manager:ets_delete(freshen_tvars).

freshen_type(Ann, Type) ->
    create_freshen_tvars(),
    Type1 = freshen(Ann, Type),
    destroy_freshen_tvars(),
    Type1.

freshen(Type) ->
    freshen(aeso_syntax:get_ann(Type), Type).

freshen(Ann, {tvar, _, Name}) ->
    NewT = case aeso_tc_ets_manager:ets_lookup(freshen_tvars, Name) of
               []          -> fresh_uvar(Ann);
               [{Name, T}] -> T
           end,
    aeso_tc_ets_manager:ets_insert(freshen_tvars, {Name, NewT}),
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
    FunT = freshen_type(Ann, aeso_tc_type_utils:typesig_to_fun_t(TypeSig)),
    apply_typesig_constraint(Ann, Constr, FunT),
    FunT.

apply_typesig_constraint(_Ann, none, _FunT) -> ok;
apply_typesig_constraint(Ann, address_to_contract, {fun_t, _, [], [_], Type}) ->
    add_constraint([#is_contract_constraint{ contract_t = Type,
                                             context    = {address_to_contract, Ann}}]);
apply_typesig_constraint(Ann, bytes_concat, {fun_t, _, [], [A, B], C}) ->
    add_constraint({add_bytes, Ann, concat, A, B, C});
apply_typesig_constraint(Ann, bytes_split, {fun_t, _, [], [C], {tuple_t, _, [A, B]}}) ->
    add_constraint({add_bytes, Ann, split, A, B, C});
apply_typesig_constraint(Ann, bytecode_hash, {fun_t, _, _, [Con], _}) ->
    add_constraint([#is_contract_constraint{ contract_t = Con,
                                             context    = {bytecode_hash, Ann} }]).
