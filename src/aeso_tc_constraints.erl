-module(aeso_tc_constraints).

-export([ solve_constraints/1
        , solve_then_destroy_and_report_unsolved_constraints/1
        , create_constraints/0
        , add_is_contract_constraint/2
        , add_is_contract_constraint/3
        , add_is_bytes_constraint/1
        , add_add_bytes_constraint/5
        , add_aens_resolve_constraint/1
        , add_oracle_type_constraint/2
        , add_named_argument_constraint/3
        , add_field_constraint/5
        , add_dependent_type_constraint/5
        , add_record_create_constraint/3
        ]).

%% -- Duplicated types -------------------------------------------------------

-type uvar() :: {uvar, aeso_syntax:ann(), reference()}.
-type named_args_t() :: uvar() | [{named_arg_t, aeso_syntax:ann(), aeso_syntax:id(), utype(), aeso_syntax:expr()}].
-type utype() :: aeso_tc_typedefs:utype().

%% -- Duplicated macros ------------------------------------------------------

-define(is_type_id(T), element(1, T) =:= id orelse
                       element(1, T) =:= qid orelse
                       element(1, T) =:= con orelse
                       element(1, T) =:= qcon).

%% -- Moved functions --------------------------------------------------------

unify(A, B, C, D) -> aeso_tc_unify:unify(A, B, C, D).

%% -------

unfold_types_in_type(A, B) -> aeso_tc_type_unfolding:unfold_types_in_type(A, B).

%% -------

qname(A) -> aeso_tc_name_manip:qname(A).

%% -------

type_error(A) -> aeso_tc_errors:type_error(A).

%% -------

is_monomorphic(A) -> aeso_tc_type_utils:is_monomorphic(A).
is_first_order(A) -> aeso_tc_type_utils:is_first_order(A).
app_t(A, B, C) -> aeso_tc_type_utils:app_t(A, B, C).
fresh_uvar(A) -> aeso_tc_type_utils:fresh_uvar(A).

%% -------

freshen(A) -> aeso_tc_env:freshen(A).
create_freshen_tvars() -> aeso_tc_env:create_freshen_tvars().
destroy_freshen_tvars() -> aeso_tc_env:destroy_freshen_tvars().

%% ---------------------------------------------------------------------------

-type env() :: aeso_tc_env:env().

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

-spec add_constraint(constraint()) -> true.
add_constraint(Constraint) ->
    aeso_tc_ets_manager:ets_insert_ordered(constraints, Constraint).

add_is_contract_constraint(ContractT, Context) ->
    add_constraint(
        #is_contract_constraint{
            contract_t = ContractT,
            context    = Context }).

add_is_contract_constraint(ContractT, Context, ForceDef) ->
    add_constraint(
        #is_contract_constraint{
            contract_t = ContractT,
            context    = Context,
            force_def  = ForceDef }).

add_aens_resolve_constraint(Type) ->
    add_constraint({aens_resolve_type, Type}).

add_oracle_type_constraint(Ann, Type) ->
    add_constraint({oracle_type, Ann, Type}).

add_named_argument_constraint(Args, Name, Type) ->
    add_constraint(
        #named_argument_constraint{
            args = Args,
            name = Name,
            type = Type }).

add_is_bytes_constraint(Type) ->
    add_constraint({is_bytes, Type}).

add_add_bytes_constraint(Ann, Kind, A, B, C) ->
    add_constraint({add_bytes, Ann, Kind, A, B, C}).

add_field_constraint(RecordT, Field, FieldT, Kind, Context) ->
    add_constraint(#field_constraint{
        record_t = RecordT,
        field    = Field,
        field_t  = FieldT,
        kind     = Kind,
        context  = Context }).

add_dependent_type_constraint(NamedArgsT, NamedArgs, GeneralType, SpecializedType, Context) ->
    add_constraint(#dependent_type_constraint{
        named_args_t     = NamedArgsT,
        named_args       = NamedArgs,
        general_type     = GeneralType,
        specialized_type = SpecializedType,
        context          = Context }).

add_record_create_constraint(RecordT, Fields, Context) ->
    add_constraint(#record_create_constraint{
        record_t = RecordT,
        fields   = Fields,
        context  = Context }).

create_constraints() ->
    aeso_tc_ets_manager:ets_new(constraints, [ordered_set]).

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
    [ type_error({unsolved_named_argument_constraint, Name, Type})
        || #named_argument_constraint{name = Name, type = Type} <- Unsolved ],

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
    #named_argument_constraint{ args = Args,
                                name = Id = {id, _, Name},
                                type = Type }) ->
    case [ T || {named_arg_t, _, {id, _, Name1}, T, _} <- Args, Name1 == Name ] of
        []  ->
            type_error({bad_named_argument, Args, Id}),
            false;
        [T] -> unify(Env, T, Type, {check_named_arg_constraint, Args, Id, Type}), true
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
    is_monomorphic(QType) orelse type_error({invalid_oracle_type, polymorphic,  query,    Ann, Type}),
    is_monomorphic(RType) orelse type_error({invalid_oracle_type, polymorphic,  response, Ann, Type}),
    is_first_order(QType) orelse type_error({invalid_oracle_type, higher_order, query,    Ann, Type}),
    is_first_order(RType) orelse type_error({invalid_oracle_type, higher_order, response, Ann, Type}),
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
