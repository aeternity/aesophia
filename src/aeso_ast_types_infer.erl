-module(aeso_ast_types_infer).


desugar_clauses(Ann, Fun, {type_sig, _, _, _, ArgTypes, RetType}, Clauses) ->
    NeedDesugar =
        case Clauses of
            [{letfun, _, _, As, _, [{guarded, _, [], _}]}] -> lists:any(fun({typed, _, {id, _, _}, _}) -> false; (_) -> true end, As);
            _                                              -> true
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
            {letfun, Ann, Fun, Args, RetType, [{guarded, NoAnn, [], {typed, NoAnn,
               {switch, NoAnn, Tuple(Args),
                 [ {'case', AnnC, Tuple(ArgsC), GuardedBodies}
                 || {letfun, AnnC, _, ArgsC, _, GuardedBodies} <- Clauses ]}, RetType}}]}
    end.


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


%%% INFER


-spec infer([aeso_syntax:ast()]) -> {aeso_syntax:ast(), aeso_syntax:ast(), [aeso_warnings:warning()]} | {env(), aeso_syntax:ast(), aeso_syntax:ast(), [aeso_warnings:warning()]}.
infer(Modules) ->
    infer(Modules, []).

infer(Modules, Options) ->
    infer(init_env(Options), Modules, Options).

infer(Env, Modules, Options) ->
    ets_init(),
    try
        {Env1, Modules1} = infer(Env, Modules, [], Options),
        when_warning(warn_unused_functions, fun() -> destroy_and_report_unused_functions() end),
        when_option(warn_error, fun() -> destroy_and_report_warnings_as_type_errors() end),
        WarningsUnsorted = lists:map(fun mk_warning/1, ets_tab2list(warnings)),
        Warnings = aeso_warnings:sort_warnings(WarningsUnsorted),
        {Env1, Modules1, Warnings}
        end
    after
        clean_up_ets()
    end.

-spec infer(aeso_syntax:ast(), list(option())) ->
  {aeso_syntax:ast(), aeso_syntax:ast(), [aeso_warnings:warning()]} | {env(), aeso_syntax:ast(), aeso_syntax:ast(), [aeso_warnings:warning()]}.
infer(Env, [[]|Rest], Acc, Options) ->
    type_error({no_decls, proplists:get_value(src_file, Options, no_file)}),
    infer(Env, Rest, Acc, Options);
infer(Env, [Module|Rest], Acc, Options) ->
    {Env1, Modules1} = infer1(Env, Module, [], Options),
    infer(Env1, Rest, [Module1|Acc], Options);
infer(Env, [], Acc, _) ->
    Modules = lists:reverse(Acc),
    {Env, Modules}.

-spec infer1(env(), [aeso_syntax:decl()], [aeso_syntax:decl()], list(option())) ->
    {env(), [aeso_syntax:decl()]}.
infer1(Env, [], Acc, _Options) -> {Env, lists:reverse(Acc)};
infer1(Env0, [Contract0 = {Contract, Ann, ConName, Impls, Code} | Rest], Acc, Options)
  when ?IS_CONTRACT_HEAD(Contract) ->
    %% do type inference on each contract independently.
    Env = Env0#env{ contract_parents = maps:put(name(ConName),
                                                [name(Impl) || Impl <- Impls],
                                                Env0#env.contract_parents) },
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
    check_contract_preserved_payability(Env, ConName, Ann, Impls, Acc, What),
    populate_functions_to_implement(Env, ConName, Impls, Acc),
    Env1 = bind_contract(untyped, Contract0, Env),
    {Env2, Code1} = infer_contract_top(push_scope(contract, ConName, Env1), What, Code, Options),
    report_unimplemented_functions(Env1, ConName),
    Contract1 = {Contract, Ann, ConName, Impls, Code1},
    Env3 = pop_scope(Env2),
    %% Rebinding because the qualifications of types are added during type inference. Could we do better?
    Env4 = bind_contract(typed, Contract1, Env3),
    infer1(Env4, Rest, [Contract1 | Acc], Options);
infer1(Env, [{namespace, Ann, Name, Code} | Rest], Acc, Options) ->
    when_warning(warn_unused_includes,
                 fun() ->
                     SrcFile = proplists:get_value(src_file, Options, no_file),
                     potential_unused_include(Ann, SrcFile)
                 end),
    check_scope_name_clash(Env, namespace, Name),
    {Env1, Code1} = infer_contract_top(push_scope(namespace, Name, Env), namespace, Code, Options),
    Namespace1 = {namespace, Ann, Name, Code1},
    infer1(pop_scope(Env1), Rest, [Namespace1 | Acc], Options);
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
      || {FunName, I, _} <- ets_tab2list(functions_to_implement) ],
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
        Inserted = ets_insert_new(functions_to_implement, {name(Id), I, Decl}),
        [{_, I2, _}] = ets_lookup(functions_to_implement, name(Id)),
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
              ({using, _, _, _, _})       -> using;
              (_)                         -> unexpected
           end,
    Get = fun(K, In) -> [ Def || Def <- In, Kind(Def) == K ] end,
    OldUsedNamespaces = Env#env.used_namespaces,
    Env01 = check_usings(Env, Get(using, Defs)),
    {Env1, TypeDefs} = check_typedefs(Env01, Get(type, Defs)),
    when_warning(warn_unused_typedefs, fun() -> potential_unused_typedefs(Env#env.namespace, TypeDefs) end),
    create_type_errors(),
    check_unexpected(Get(unexpected, Defs)),
    Env2 =
        case What of
            namespace          -> Env1;
            contract_interface -> Env1;
            contract           -> bind_state(Env1)   %% bind state and put
        end,
    {ProtoSigs, Decls} = lists:unzip([ check_fundecl(Env1, Decl) || Decl <- Get(prototype, Defs) ]),
    [ type_error({missing_definition, Id}) || {fun_decl, _, Id, _} <- Decls,
                                              What =:= contract,
                                              get_option(no_code, false) =:= false ],
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
    %% Remove namespaces used in the current namespace
    Env5 = Env4#env{ used_namespaces = OldUsedNamespaces },
    %% Check that `init` doesn't read or write the state and that `init` is not missing
    check_state(Env4, Defs1),
    %% Check that entrypoints have first-order arg types and return types
    check_entrypoints(Defs1),
    destroy_and_report_type_errors(Env4),
    %% Add inferred types of definitions
    {Env5, TypeDefs ++ Decls ++ Defs1}.

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
            check_parameterizable(D, Xs),
            Def  = check_event(Env, Name, Ann, check_typedef(bind_tvars(Xs, Env), Def0)),
            Acc1 = [{type_def, Ann, D, Xs, Def} | Acc],
            Env1 = bind_type(Name, Ann, {Xs, Def}, Env),
            case Def of
                {alias_t, _}  -> check_typedef_sccs(Env1, TypeMap, SCCs, Acc1);
                {record_t, []} ->
                    type_error({empty_record_definition, Ann, Name}),
                    check_typedef_sccs(Env1, TypeMap, SCCs, Acc1);
                {record_t, Fields} ->
                    ets_insert(type_vars_variance, {Env#env.namespace ++ qname(D),
                                                    infer_type_vars_variance(Xs, Fields)}),
                    %% check_type to get qualified name
                    RecTy = check_type(Env1, app_t(Ann, D, Xs)),
                    Env2 = check_fields(Env1, TypeMap, RecTy, Fields),
                    check_typedef_sccs(Env2, TypeMap, SCCs, Acc1);
                {variant_t, Cons} ->
                    ets_insert(type_vars_variance, {Env#env.namespace ++ qname(D),
                                                    infer_type_vars_variance(Xs, Cons)}),
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
    Variances = case ets_lookup(type_vars_variance, qname(Type)) of
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

check_usings(Env, []) ->
    Env;
check_usings(Env = #env{ used_namespaces = UsedNamespaces }, [{using, Ann, Con, Alias, Parts} | Rest]) ->
    AliasName = case Alias of
                    none ->
                        none;
                    _ ->
                        qname(Alias)
                end,
    case get_scope(Env, qname(Con)) of
        false ->
            create_type_errors(),
            type_error({using_undefined_namespace, Ann, qname(Con)}),
            destroy_and_report_type_errors(Env);
        #scope{kind = contract} ->
            create_type_errors(),
            type_error({using_undefined_namespace, Ann, qname(Con)}),
            destroy_and_report_type_errors(Env);
        Scope ->
            Nsp = case Parts of
                      none ->
                          {qname(Con), AliasName, none};
                      {ForOrHiding, Ids} ->
                          IsUndefined = fun(Id) ->
                                            proplists:lookup(name(Id), Scope#scope.funs) == none
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
            check_usings(Env#env{ used_namespaces = UsedNamespaces ++ [Nsp] }, Rest)
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
    Env1 = bind_field_append(name(Id), #field_info{ ann = Ann, kind = record, field_t = Type, record_t = RecTy }, Env),
    check_fields(Env1, TypeMap, RecTy, Fields).

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
    case ets_lookup(functions_to_implement, Name) of
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

            ets_delete(functions_to_implement, Name);
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


infer_letrec(Env, Defs) ->
    create_constraints(),
    Funs = lists:map(fun({letfun, _, {id, Ann, Name}, _, _, _})   -> {Name, fresh_uvar(Ann)};
                        ({fun_clauses, _, {id, Ann, Name}, _, _}) -> {Name, fresh_uvar(Ann)}
                     end, Defs),
    ExtendEnv = bind_funs(Funs, Env),
    Inferred =
        [ begin
            Res    = {{Name, TypeSig}, LetFun} = infer_letfun(ExtendEnv, LF),
            register_implementation(get_letfun_id(LetFun), TypeSig),
            Got    = proplists:get_value(Name, Funs),
            Expect = typesig_to_fun_t(TypeSig),
            unify(Env, Got, Expect, {check_typesig, Name, Got, Expect}),
            solve_constraints(Env),
            ?PRINT_TYPES("Checked ~s : ~s\n",
                         [Name, pp(dereference_deep(Got))]),
            Res
          end || LF <- Defs ],
    solve_then_destroy_and_report_unsolved_constraints(Env),
    TypeSigs = instantiate([Sig || {Sig, _} <- Inferred]),
    NewDefs  = instantiate([D || {_, D} <- Inferred]),
    [print_typesig(S) || S <- TypeSigs],
    {TypeSigs, NewDefs}.

infer_letfun(Env = #env{ namespace = Namespace }, {fun_clauses, Ann, Fun = {id, _, Name}, Type, Clauses}) ->
    when_warning(warn_unused_stateful, fun() -> potential_unused_stateful(Ann, Fun) end),
    when_warning(warn_unused_functions,
                 fun() -> potential_unused_function(Env, Ann, Namespace ++ qname(Fun), Fun) end),
    Type1 = check_type(Env, Type),
    {NameSigs, Clauses1} = lists:unzip([ infer_letfun1(Env, Clause) || Clause <- Clauses ]),
    {_, Sigs = [Sig | _]} = lists:unzip(NameSigs),
    _ = [ begin
            ClauseT = typesig_to_fun_t(ClauseSig),
            unify(Env, ClauseT, Type1, {check_typesig, Name, ClauseT, Type1})
          end || ClauseSig <- Sigs ],
    {{Name, Sig}, desugar_clauses(Ann, Fun, Sig, Clauses1)};
infer_letfun(Env = #env{ namespace = Namespace }, LetFun = {letfun, Ann, Fun, _, _, _}) ->
    when_warning(warn_unused_stateful, fun() -> potential_unused_stateful(Ann, Fun) end),
    when_warning(warn_unused_functions, fun() -> potential_unused_function(Env, Ann, Namespace ++ qname(Fun), Fun) end),
    {{Name, Sig}, Clause} = infer_letfun1(Env, LetFun),
    {{Name, Sig}, desugar_clauses(Ann, Fun, Sig, [Clause])}.

infer_letfun1(Env0 = #env{ namespace = NS }, {letfun, Attrib, Fun = {id, NameAttrib, Name}, Args, What, GuardedBodies}) ->
    Env = Env0#env{ stateful = aeso_syntax:get_ann(stateful, Attrib, false),
                    current_function = Fun },
    {NewEnv, {typed, _, {tuple, _, TypedArgs}, {tuple_t, _, ArgTypes}}} = infer_pattern(Env, {tuple, [{origin, system} | NameAttrib], Args}),
    when_warning(warn_unused_variables, fun() -> potential_unused_variables(NS, Name, free_vars(Args)) end),
    ExpectedType = check_type(Env, arg_type(NameAttrib, What)),
    InferGuardedBodies = fun({guarded, Ann, Guards, Body}) ->
        NewGuards = lists:map(fun(Guard) ->
                                  check_expr(NewEnv#env{ in_guard = true }, Guard, {id, Attrib, "bool"})
                              end, Guards),
        NewBody = check_expr(NewEnv, Body, ExpectedType),
        {guarded, Ann, NewGuards, NewBody}
    end,
    NewGuardedBodies = [{guarded, _, _, {typed, _, _, ResultType}} | _] = lists:map(InferGuardedBodies, GuardedBodies),
    NamedArgs = [],
    TypeSig = {type_sig, Attrib, none, NamedArgs, ArgTypes, ResultType},
    {{Name, TypeSig},
     {letfun, Attrib, {id, NameAttrib, Name}, TypedArgs, ResultType, NewGuardedBodies}}.


check_stateful(#env{ in_guard = true }, Id, Type = {type_sig, _, _, _, _, _}) ->
    case aeso_syntax:get_ann(stateful, Type, false) of
        false -> ok;
        true  ->
            type_error({stateful_not_allowed_in_guards, Id})
    end;
check_stateful(#env{ stateful = false, current_function = Fun }, Id, Type = {type_sig, _, _, _, _, _}) ->
    case aeso_syntax:get_ann(stateful, Type, false) of
        false -> ok;
        true  ->
            type_error({stateful_not_allowed, Id, Fun})
    end;
check_stateful(#env { current_function = Fun }, _Id, _Type) ->
    when_warning(warn_unused_stateful, fun() -> used_stateful(Fun) end),
    ok.


%% Hack: don't allow passing the 'value' named arg if not stateful. This only
%% works since the user can't create functions with named arguments.
check_stateful_named_arg(#env{ stateful = Stateful, current_function = Fun }, {id, _, "value"}, Default) ->
    case Default of
        {int, _, 0} -> ok;
        _           ->
            case Stateful of
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
    Top = Env#env.namespace,
    StateType = lookup_type(Env, {id, [{origin, system}], "state"}),
    case unfold_types_in_type(Env, StateType) of
        false  ->
            ok;
        {_, {_, {_, {alias_t, {tuple_t, _, []}}}}} ->  %% type state = ()
            ok;
        _ ->
            #scope{ ann = AnnCon } = get_scope(Env, Top),
            type_error({missing_init_function, {con, AnnCon, lists:last(Top)}})
    end.

%% Check that `init` doesn't read or write the state and that `init` is defined
%% when the state type is not unit
check_state(Env, Defs) ->
    Top       = Env#env.namespace,
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
    NewEnv = bind_vars([{Var, fresh_uvar(Ann1)} || Var = {id, Ann1, _} <- Vars], Env#env{ in_pattern = true }),
    NewPattern = infer_expr(NewEnv, Pattern),
    {NewEnv#env{ in_pattern = Env#env.in_pattern }, NewPattern}.

infer_case(Env = #env{ namespace = NS, current_function = {id, _, Fun} }, Attrs, Pattern, ExprType, GuardedBranches, SwitchType) ->
    {NewEnv, NewPattern = {typed, _, _, PatType}} = infer_pattern(Env, Pattern),
    when_warning(warn_unused_variables, fun() -> potential_unused_variables(NS, Fun, free_vars(Pattern)) end),
    InferGuardedBranches = fun({guarded, Ann, Guards, Branch}) ->
        NewGuards = lists:map(fun(Guard) ->
                                  check_expr(NewEnv#env{ in_guard = true }, Guard, {id, Attrs, "bool"})
                              end, Guards),
        NewBranch = check_expr(NewEnv#env{ in_pattern = false }, Branch, SwitchType),
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
    FunT = typesig_to_fun_t(TypeSig),
    NewE = bind_var({id, Ann, Name}, FunT, Env),
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
