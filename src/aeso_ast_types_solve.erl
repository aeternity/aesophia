-module(aeso_ast_types_solve).



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
                Arity = fun_arity(dereference_deep(FieldType)),
                FieldInfos = case Arity of
                                 none -> lookup_record_field(Env, FieldName, Kind);
                                 _    -> lookup_record_field_arity(Env, FieldName, Arity, Kind)
                             end,
                case FieldInfos of
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

    Unsolved = [ S || S <- [ solve_constraint(Env, dereference_deep(C)) || C <- NamedArgCs ],
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

solve_constraint(_Env, #field_constraint{record_t = {uvar, _, _}}) ->
    not_solved;
solve_constraint(Env, C = #field_constraint{record_t = RecType,
                                            field    = FieldName,
                                            field_t  = FieldType,
                                            context  = When}) ->
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
    end;
solve_constraint(Env, C = #dependent_type_constraint{}) ->
    check_named_argument_constraint(Env, C);
solve_constraint(Env, C = #named_argument_constraint{}) ->
    check_named_argument_constraint(Env, C);
solve_constraint(_Env, {is_bytes, _}) -> ok;
solve_constraint(Env, {add_bytes, Ann, _, A0, B0, C0}) ->
    A = unfold_types_in_type(Env, dereference(A0)),
    B = unfold_types_in_type(Env, dereference(B0)),
    C = unfold_types_in_type(Env, dereference(C0)),
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
            ok; %% If all are solved we checked M + N == R in solve_constraint.
        _ -> type_error({unsolved_bytes_constraint, Ann, Fun, A, B, C})
    end.

check_aens_resolve_constraints(_Env, []) ->
    ok;
check_aens_resolve_constraints(Env, [{aens_resolve_type, Type} | Rest]) ->
    Type1 = unfold_types_in_type(Env, instantiate(Type)),
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
    Type = unfold_types_in_type(Env, instantiate(OType)),
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
                                        C#field_constraint{record_t = dereference(RecordType)};
                                    (C) -> dereference_deep(C)
                                 end, Constraints),
    SolvedConstraints = lists:map(fun(C) -> solve_constraint(Env, dereference_deep(C)) end, DerefConstraints),
    Unsolved = DerefConstraints--SolvedConstraints,
    lists:filter(fun(#field_constraint{}) -> true; (_) -> false end, Unsolved).

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
