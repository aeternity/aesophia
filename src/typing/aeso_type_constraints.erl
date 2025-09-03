%%%-------------------------------------------------------------------
%%% @copyright (C) 2018, Aeternity Anstalt
%%% @doc
%%%     Constraint solving for Sophia type checker.
%%%     This module handles all constraint generation, solving, and checking
%%%     that was previously part of aeso_type_infer.
%%% @end
%%%-------------------------------------------------------------------

-module(aeso_type_constraints).

-export([ create_constraints/0
        , add_constraint/1
        , solve_all_constraints/1
        , solve_then_destroy_and_report_unsolved_constraints/1
        , freshen_type/3
        , freshen_type_sig/3
        ]).

-include("aeso_types.hrl").

%% -- Constraint Management --

create_constraints() ->
    aeso_type_ets:new(constraints, [ordered_set]).

-spec add_constraint(constraint() | [constraint()]) -> true.
add_constraint(Constraint) ->
    aeso_type_ets:insert_ordered(constraints, Constraint).

get_constraints() ->
    aeso_type_ets:tab2list_ordered(constraints).

destroy_constraints() ->
    aeso_type_ets:delete(constraints).

%% -- Constraint Solving --

%% Solve all constraints by iterating until no-progress
-spec solve_all_constraints(env()) -> ok.
solve_all_constraints(Env) ->
    Constraints = [C || C <- get_constraints(), not one_shot_field_constraint(Env, C) ],
    solve_constraints_top(Env, Constraints).

solve_constraints_top(Env, Constraints) ->
    UnsolvedCs = solve_constraints(Env, Constraints),
    Progress   = solve_unknown_record_constraints(Env, UnsolvedCs),

    if length(UnsolvedCs) < length(Constraints) orelse Progress == true ->
        solve_constraints_top(Env, UnsolvedCs);
       true ->
        ok
    end.

-spec solve_constraints(env(), [constraint()]) -> [constraint()].
solve_constraints(Env, Constraints) ->
    [ C1 || C <- Constraints, C1 <- [dereference_deep(C)], not solve_constraint(Env, C1) ].

solve_unknown_record_constraints(Env, Constraints) ->
    FieldCs      = lists:filter(fun(#field_constraint{record_t = {uvar, _, _}}) -> true; (_) -> false end, Constraints),
    FieldCsUVars = lists:usort([UVar || #field_constraint{record_t = UVar = {uvar, _, _}} <- FieldCs]),

    FieldConstraint = fun(#field_constraint{ field = F, kind = K, context = Ctx }) -> {K, Ctx, F} end,
    FieldsForUVar = fun(UVar) ->
                        [ FieldConstraint(FC) || FC = #field_constraint{record_t = U} <- FieldCs, U == UVar ]
                    end,

    Solutions = [ solve_for_uvar(Env, UVar, FieldsForUVar(UVar)) || UVar <- FieldCsUVars ],
    case lists:member(true, Solutions) of
        true  -> true;
        false -> Solutions
    end.

%% -- Simple constraints --
%% Returns true if solved (unified or type error)
solve_constraint(_Env, #field_constraint{record_t = {uvar, _, _}}) ->
    false;
solve_constraint(Env, #field_constraint{record_t = RecordType,
                                              field    = Field = {id, _As, FieldName},
                                              field_t  = FieldType,
                                              context  = When}) ->
    RecId = record_type_name(RecordType),
    Attrs = aeso_syntax:get_ann(RecId),
    case aeso_type_env:lookup_type(Env, RecId) of
        {_, {_Ann, {Formals, {What, Fields}}}} when What =:= record_t; What =:= contract_t ->
            FieldTypes = [{Name, Type} || {field_t, _, {id, _, Name}, Type} <- Fields],
            case proplists:get_value(FieldName, FieldTypes) of
                undefined ->
                    type_error({missing_field, Field, RecId});
                FldType ->
                    solve_field_constraint(Env, FieldType, FldType, RecordType, app_t(Attrs, RecId, Formals), When)
            end;
        _ ->
            type_error({not_a_record_type, instantiate(RecordType), When})
    end,
    true;
solve_constraint(Env, C = #dependent_type_constraint{}) ->
    check_named_argument_constraint(Env, C);
solve_constraint(Env, C = #named_argument_constraint{}) ->
    check_named_argument_constraint(Env, C);
solve_constraint(_Env, {is_bytes, _, _}) -> false;
solve_constraint(_Env, {is_fixed_bytes, _, _}) -> false;
solve_constraint(Env, {add_bytes, Ann, Action, A0, B0, C0}) ->
    A = aeso_type_unfold:unfold_types_in_type(Env, dereference(A0)),
    B = aeso_type_unfold:unfold_types_in_type(Env, dereference(B0)),
    C = aeso_type_unfold:unfold_types_in_type(Env, dereference(C0)),
    case {A, B, C} of
        {{bytes_t, _, M}, {bytes_t, _, N}, _} when is_integer(M), is_integer(N) ->
            unify(Env, {bytes_t, Ann, M + N}, C, {at, Ann});
        {{bytes_t, _, M}, _, {bytes_t, _, R}} when is_integer(M), is_integer(R), R >= M ->
            unify(Env, {bytes_t, Ann, R - M}, B, {at, Ann});
        {_, {bytes_t, _, N}, {bytes_t, _, R}} when is_integer(N), is_integer(R), R >= N ->
            unify(Env, {bytes_t, Ann, R - N}, A, {at, Ann});
        {{bytes_t, _, _}, {bytes_t, _, _}, _} when Action == concat ->
            unify(Env, {bytes_t, Ann, any}, C, {at, Ann});
        _ -> false
    end;
solve_constraint(_, _) -> false.

one_shot_field_constraint(Env, C = #field_constraint{record_t = RecordType,
                                                     field    = Field = {id, _As, FieldName},
                                                     field_t  = FieldType,
                                                     kind     = Kind,
                                                     context  = When}) ->
    Arity = aeso_type_helpers:fun_arity(dereference_deep(FieldType)),
    FieldInfos = case Arity of
                     none -> aeso_type_env:lookup_record_field(Env, FieldName, Kind);
                     _    -> aeso_type_env:lookup_record_field_arity(Env, FieldName, Arity, Kind)
                 end,

    case FieldInfos of
        [] ->
            type_error({undefined_field, Field}),
            true;
        [#field_info{field_t = FldType, record_t = RecType}] ->
            solve_field_constraint(Env, FieldType, FldType, RecordType, RecType, When),
            true;
        _ ->
            solve_constraint(Env, C)
    end;
one_shot_field_constraint(_Env, _Constraint) ->
    false.

solve_field_constraint(Env, FieldType, FldType, RecordType, RecType, When) ->
    create_freshen_tvars(),
    FreshFldType = freshen(FldType),
    FreshRecType = freshen(RecType),
    destroy_freshen_tvars(),
    unify(Env, FreshFldType, FieldType, {field_constraint, FreshFldType, FieldType, When}),
    unify(Env, FreshRecType, RecordType, {record_constraint, FreshRecType, RecordType, When}).

solve_then_destroy_and_report_unsolved_constraints(Env) ->
    solve_all_constraints(Env),
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
        lists:partition(fun({is_bytes, _, _})           -> true;
                           ({is_fixed_bytes, _, _})     -> true;
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

    check_field_constraints(Env, FieldCs),
    check_record_create_constraints(Env, CreateCs),
    check_is_contract_constraints(Env, ContractCs),
    check_named_args_constraints(Env, NamedArgCs),
    check_bytes_constraints(Env, BytesCs),
    check_aens_resolve_constraints(Env, AensResolveCs),
    check_oracle_type_constraints(Env, OracleTypeCs),

    destroy_constraints().

%% -- Named argument constraints --

%% True if solved (unified or type error), false otherwise
-spec check_named_argument_constraint(env(), named_argument_constraint()) -> true | false.
check_named_argument_constraint(_Env, #named_argument_constraint{ args = {uvar, _, _} }) ->
    false;
check_named_argument_constraint(Env,
        C = #named_argument_constraint{ args = Args,
                                        name = Id = {id, _, Name},
                                        type = Type }) ->
    case [ T || {named_arg_t, _, {id, _, Name1}, T, _} <- Args, Name1 == Name ] of
        []  ->
            type_error({bad_named_argument, Args, Id});
        [T] ->
            unify(Env, T, Type, {check_named_arg_constraint, C})
    end,
    true;
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
            unify(Env, GenType1, SpecType, {check_expr, App, GenType1, SpecType});
        _ ->
            unify(Env, GenType, SpecType, {check_expr, App, GenType, SpecType})
    end,
    true.

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

check_field_constraints(Env, Constraints) ->
    UnsolvedFieldCs = solve_constraints(Env, Constraints),
    case solve_unknown_record_constraints(Env, UnsolvedFieldCs) of
        true   -> ok;
        Errors -> [ type_error(Err) || Err <- Errors ]
    end.

check_named_args_constraints(Env, Constraints) ->
    UnsolvedNamedArgCs = solve_constraints(Env, Constraints),
    [ type_error({unsolved_named_argument_constraint, C}) || C <- UnsolvedNamedArgCs ].

check_bytes_constraints(Env, Constraints) ->
    InAddConstraint = [ T || {add_bytes, _, _, A, B, C} <- Constraints,
                             T <- [A, B, C],
                             element(1, T) /= bytes_t ],
    InSplitConstraint = [ T || {add_bytes, _, split, A, B, C} <- Constraints,
                               T <- [A, B, C],
                               element(1, T) /= bytes_t ],
    %% Skip is_bytes constraints for types that occur in add_bytes constraints
    %% (no need to generate error messages for both is_bytes and add_bytes).
    Skip = fun({is_bytes, _, T}) -> lists:member(T, InAddConstraint);
              ({is_fixed_bytes, _, T}) -> lists:member(T, InSplitConstraint);
              (_) -> false end,
    [ check_bytes_constraint(Env, C) || C <- Constraints, not Skip(C) ].

check_bytes_constraint(Env, {is_bytes, Ann, Type}) ->
    Type1 = aeso_type_unfold:unfold_types_in_type(Env, instantiate(Type)),
    case Type1 of
        {bytes_t, _, N} when is_integer(N); N == any -> ok;
        _               ->
            type_error({unknown_byte_type, Ann, Type})
    end;
check_bytes_constraint(Env, {is_fixed_bytes, Ann, Type}) ->
    Type1 = aeso_type_unfold:unfold_types_in_type(Env, instantiate(Type)),
    case Type1 of
        {bytes_t, _, N} when is_integer(N) -> ok;
        _                                  ->
            type_error({unknown_byte_length, Ann, Type})
    end;
check_bytes_constraint(Env, {add_bytes, Ann, Fun, A0, B0, C0}) ->
    A = aeso_type_unfold:unfold_types_in_type(Env, instantiate(A0)),
    B = aeso_type_unfold:unfold_types_in_type(Env, instantiate(B0)),
    C = aeso_type_unfold:unfold_types_in_type(Env, instantiate(C0)),
    case {A, B, C} of
        {{bytes_t, _, _M}, {bytes_t, _, _N}, {bytes_t, _, _R}} ->
            ok; %% If all are solved we checked M + N == R in solve_constraint.
        _ -> type_error({unsolved_bytes_constraint, Ann, Fun, A, B, C})
    end.

check_aens_resolve_constraints(_Env, []) ->
    ok;
check_aens_resolve_constraints(Env, [{aens_resolve_type, Type} | Rest]) ->
    Type1 = aeso_type_unfold:unfold_types_in_type(Env, instantiate(Type)),
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
    Type = aeso_type_unfold:unfold_types_in_type(Env, instantiate(OType)),
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
    Type1 = aeso_type_unfold:unfold_types_in_type(Env, instantiate(Type)),
    try aeso_type_env:lookup_type(Env, record_type_name(Type1)) of
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
    aeso_type_ets:lookup(defined_contracts, aeso_type_helpers:qname(C)) =/= [].

check_is_contract_constraints(_Env, []) -> ok;
check_is_contract_constraints(Env, [C | Cs]) ->
    #is_contract_constraint{ contract_t = Type, context = Cxt, force_def = ForceDef } = C,
    Type1 = aeso_type_unfold:unfold_types_in_type(Env, instantiate(Type)),
    TypeName = record_type_name(Type1),
    case aeso_type_env:lookup_type(Env, TypeName) of
        {_, {_Ann, {[], {contract_t, _}}}} ->
            case not ForceDef orelse is_contract_defined(TypeName) of
                true -> ok;
                false -> type_error({contract_lacks_definition, Type1, Cxt})
                end;
        _ -> type_error({not_a_contract_type, Type1, Cxt})
    end,
    check_is_contract_constraints(Env, Cs).

record_type_name({app_t, _Attrs, RecId, _Args}) when ?is_type_id(RecId) ->
    RecId;
record_type_name(RecId) when ?is_type_id(RecId) ->
    RecId;
record_type_name(_Other) ->
    {id, [{origin, system}], "not_a_record_type"}.

solve_for_uvar(Env, UVar = {uvar, Attrs, _}, Fields0) ->
    Fields = [{Kind, Fld} || {Kind, _, Fld} <- Fields0],
    [{_, When, _} | _] = Fields0,    %% Get the location from the first field
    %% If we have 'create' constraints they must be complete.
    Covering = lists:usort([ Name || {create, {id, _, Name}} <- Fields ]),
    %% Does this set of fields uniquely identify a record type?
    FieldNames = [ Name || {_Kind, {id, _, Name}} <- Fields ],
    UniqueFields = lists:usort(FieldNames),
    Candidates = [RecType || #field_info{record_t = RecType} <- aeso_type_env:lookup_record_field(Env, hd(FieldNames))],
    TypesAndFields = [case aeso_type_env:lookup_type(Env, record_type_name(RecType)) of
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
            {_, {_, {Formals, {_RecOrCon, _}}}} = aeso_type_env:lookup_type(Env, RecName),
            create_freshen_tvars(),
            FreshRecType = freshen(app_t(Attrs, RecName, Formals)),
            destroy_freshen_tvars(),
            unify(Env, UVar, FreshRecType, {solve_rec_type, UVar, Fields}),
            true;
        {StillPossible, _} ->
            {ambiguous_record, Fields, StillPossible}
    end.

%% -- Type signature constraints --

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



%% -- Freshen functionality --

create_freshen_tvars() ->
    aeso_type_ets:new(freshen_tvars, [set]).

destroy_freshen_tvars() ->
    aeso_type_ets:delete(freshen_tvars).

freshen_type(Ann, Type, Ctx) ->
    create_freshen_tvars(),
    Type1 = freshen(Ann, Type, Ctx),
    destroy_freshen_tvars(),
    Type1.

freshen(Type) ->
    freshen(aeso_syntax:get_ann(Type), Type, none).

freshen(Ann, {tvar, _, Name}, _Ctx) ->
    NewT = case aeso_type_ets:lookup(freshen_tvars, Name) of
               []          -> fresh_uvar(Ann);
               [{Name, T}] -> T
           end,
    aeso_type_ets:insert(freshen_tvars, {Name, NewT}),
    NewT;
freshen(Ann, {bytes_t, _, '_'}, Ctx) ->
    X = fresh_uvar(Ann),
    add_constraint({is_bytes, Ctx, X}),
    X;
freshen(Ann, {bytes_t, _, fixed}, Ctx) ->
    X = fresh_uvar(Ann),
    add_constraint({is_fixed_bytes, Ctx, X}),
    X;
freshen(Ann, {fun_t, FAnn, NamedArgs, Args, Result}, Ctx) when is_list(Args) ->
    {fun_t, FAnn, freshen(Ann, NamedArgs, Ctx),
     [ freshen(Ann, Arg, [{arg, Ix} | Ctx]) || {Arg, Ix} <- lists:zip(Args, lists:seq(1, length(Args))) ],
     freshen(Ann, Result, [result | Ctx])};
freshen(Ann, {fun_t, FAnn, NamedArgs, Arg, Result}, Ctx) ->
    {fun_t, FAnn, freshen(Ann, NamedArgs, Ctx), freshen(Ann, Arg, Ctx), freshen(Ann, Result, [result | Ctx])};
freshen(Ann, T, Ctx) when is_tuple(T) ->
    list_to_tuple(freshen(Ann, tuple_to_list(T), Ctx));
freshen(Ann, [A | B], Ctx) ->
    [freshen(Ann, A, Ctx) | freshen(Ann, B, Ctx)];
freshen(_, X, _Ctx) ->
    X.

freshen_type_sig(Ann, TypeSig = {type_sig, _, Constr, _, _, _}, Ctx) ->
    FunT = freshen_type(Ann, aeso_type_helpers:typesig_to_fun_t(TypeSig), Ctx),
    apply_typesig_constraint(Ann, Constr, FunT),
    FunT.

%% -- Helper functions --

app_t(_Ann, Name, [])  -> Name;
app_t(Ann, Name, Args) -> {app_t, Ann, Name, Args}.

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

%% -- Delegation functions --

unify(Env, A, B, When) -> aeso_type_unify:unify(Env, A, B, When).
dereference(T) -> aeso_type_helpers:dereference(T).
dereference_deep(T) -> aeso_type_helpers:dereference_deep(T).
instantiate(E) -> aeso_type_unify:instantiate(E).
fresh_uvar(Attrs) -> aeso_type_helpers:fresh_uvar(Attrs).
type_error(Err) -> aeso_type_helpers:type_error(Err).
