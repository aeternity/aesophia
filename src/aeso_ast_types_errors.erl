-module(aeso_ast_types_errors).


cannot_unify(A, B, Cxt, When) ->
    type_error({cannot_unify, A, B, Cxt, When}).


type_error(Err) ->
    ets_insert(type_errors, Err).


mk_t_err(Pos, Msg) ->
    aeso_errors:new(type_error, Pos, lists:flatten(Msg)).
mk_t_err(Pos, Msg, Ctxt) ->
    aeso_errors:new(type_error, Pos, lists:flatten(Msg), lists:flatten(Ctxt)).

mk_t_err_from_warn(Warn) ->
    aeso_warnings:warn_to_err(type_error, Warn).

mk_error({no_decls, File}) ->
    Pos = aeso_errors:pos(File, 0, 0),
    mk_t_err(Pos, "Empty contract");
mk_error({mismatched_decl_in_funblock, Name, Decl}) ->
    Msg = io_lib:format("Mismatch in the function block. Expected implementation/type declaration of ~s function", [Name]),
    mk_t_err(pos(Decl), Msg);
mk_error({higher_kinded_typevar, T}) ->
    Msg = io_lib:format("Type `~s` is a higher kinded type variable "
                        "(takes another type as an argument)", [pp(instantiate(T))]
                       ),
    mk_t_err(pos(T), Msg);
mk_error({wrong_type_arguments, X, ArityGiven, ArityReal}) ->
    Msg = io_lib:format("Arity for ~s doesn't match. Expected ~p, got ~p"
                       , [pp(instantiate(X)), ArityReal, ArityGiven]
                       ),
    mk_t_err(pos(X), Msg);
mk_error({unnamed_map_update_with_default, Upd}) ->
    Msg = "Invalid map update with default",
    mk_t_err(pos(Upd), Msg);
mk_error({fundecl_must_have_funtype, _Ann, Id, Type}) ->
    Msg = io_lib:format("`~s` was declared with an invalid type `~s`. "
                       "Entrypoints and functions must have functional types"
                       , [pp(Id), pp(instantiate(Type))]),
    mk_t_err(pos(Id), Msg);
mk_error({cannot_unify, A, B, Cxt, When}) ->
    VarianceContext = case Cxt of
                          none -> "";
                          _    -> io_lib:format(" in a ~p context", [Cxt])
                      end,
    Msg = io_lib:format("Cannot unify `~s` and `~s`" ++ VarianceContext,
                        [pp(instantiate(A)), pp(instantiate(B))]),
    {Pos, Ctxt} = pp_when(When),
    mk_t_err(Pos, Msg, Ctxt);
mk_error({hole_found, Ann, Type}) ->
    Msg = io_lib:format("Found a hole of type `~s`", [pp(instantiate(Type))]),
    mk_t_err(pos(Ann), Msg);
mk_error({unbound_variable, Id}) ->
    Msg = io_lib:format("Unbound variable `~s`", [pp(Id)]),
    case Id of
        {qid, _, ["Chain", "event"]} ->
            Cxt = "Did you forget to define the event type?",
            mk_t_err(pos(Id), Msg, Cxt);
        _ -> mk_t_err(pos(Id), Msg)
    end;
mk_error({undefined_field, Id}) ->
    Msg = io_lib:format("Unbound field ~s", [pp(Id)]),
    mk_t_err(pos(Id), Msg);
mk_error({not_a_record_type, Type, Why}) ->
    Msg = io_lib:format("Not a record type: `~s`", [pp_type(Type)]),
    {Pos, Ctxt} = pp_why_record(Why),
    mk_t_err(Pos, Msg, Ctxt);
mk_error({not_a_contract_type, Type, Cxt}) ->
    Msg =
        case Type of
            {tvar, _, _} ->
                "Unresolved contract type";
            _ ->
                io_lib:format("The type `~s` is not a contract type", [pp_type(Type)])
        end,
    {Pos, Cxt1} =
        case Cxt of
            {var_args, Ann, Fun} ->
                {pos(Ann),
                 io_lib:format("when calling variadic function `~s`", [pp_expr(Fun)])};
            {contract_literal, Lit} ->
                {pos(Lit),
                 io_lib:format("when checking that the contract literal `~s` has the type `~s`",
                               [pp_expr(Lit), pp_type(Type)])};
            {address_to_contract, Ann} ->
                {pos(Ann),
                 io_lib:format("when checking that the call to `Address.to_contract` has the type `~s`",
                               [pp_type(Type)])}
        end,
    mk_t_err(Pos, Msg, Cxt1);
mk_error({non_linear_pattern, Pattern, Nonlinear}) ->
    Msg = io_lib:format("Repeated name~s ~s in the pattern `~s`",
                        [plural("", "s", Nonlinear),
                         string:join(lists:map(fun(F) -> "`" ++ F ++ "`" end, Nonlinear), ", "),
                         pp_expr(Pattern)]),
    mk_t_err(pos(Pattern), Msg);
mk_error({ambiguous_record, Fields = [{_, First} | _], Candidates}) ->
    Msg = io_lib:format("Ambiguous record type with field~s ~s could be one of~s",
                        [plural("", "s", Fields),
                         string:join([ "`" ++ pp(F) ++ "`" || {_, F} <- Fields ], ", "),
                         [ ["\n  - ", "`" ++ pp(C) ++ "`", " (at ", pp_loc(C), ")"] || C <- Candidates ]]),
    mk_t_err(pos(First), Msg);
mk_error({missing_field, Field, Rec}) ->
    Msg = io_lib:format("Record type `~s` does not have field `~s`",
                        [pp(Rec), pp(Field)]),
    mk_t_err(pos(Field), Msg);
mk_error({missing_fields, Ann, RecType, Fields}) ->
    Msg = io_lib:format("The field~s ~s ~s missing when constructing an element of type `~s`",
                        [plural("", "s", Fields),
                         string:join(lists:map(fun(F) -> "`" ++ F ++ "`" end, Fields), ", "),
                         plural("is", "are", Fields), pp(RecType)]),
    mk_t_err(pos(Ann), Msg);
mk_error({no_records_with_all_fields, Fields = [{_, First} | _]}) ->
    Msg = io_lib:format("No record type with field~s ~s",
                        [plural("", "s", Fields),
                         string:join([ "`" ++ pp(F) ++ "`" || {_, F} <- Fields ], ", ")]),
    mk_t_err(pos(First), Msg);
mk_error({recursive_types_not_implemented, Types}) ->
    S = plural(" is", "s are mutually", Types),
    Msg = io_lib:format("The following type~s recursive, which is not yet supported:~s",
                        [S, [io_lib:format("\n  - `~s` (at ~s)", [pp(T), pp_loc(T)]) || T <- Types]]),
    mk_t_err(pos(hd(Types)), Msg);
mk_error({event_must_be_variant_type, Where}) ->
    Msg = io_lib:format("The event type must be a variant type", []),
    mk_t_err(pos(Where), Msg);
mk_error({indexed_type_must_be_word, Type, Type}) ->
    Msg = io_lib:format("The indexed type `~s` is not a word type",
                        [pp_type(Type)]),
    mk_t_err(pos(Type), Msg);
mk_error({indexed_type_must_be_word, Type, Type1}) ->
    Msg = io_lib:format("The indexed type `~s` equals `~s` which is not a word type",
                        [pp_type(Type), pp_type(Type1)]),
    mk_t_err(pos(Type), Msg);
mk_error({event_0_to_3_indexed_values, Constr}) ->
    Msg = io_lib:format("The event constructor `~s` has too many indexed values (max 3)",
                        [name(Constr)]),
    mk_t_err(pos(Constr), Msg);
mk_error({event_0_to_1_string_values, Constr}) ->
    Msg = io_lib:format("The event constructor `~s` has too many non-indexed values (max 1)",
                        [name(Constr)]),
    mk_t_err(pos(Constr), Msg);
mk_error({repeated_constructor, Cs}) ->
    Msg = io_lib:format("Variant types must have distinct constructor names~s",
                        [[ io_lib:format("\n`~s`  (at ~s)", [pp_typed("  - ", C, T), pp_loc(C)]) || {C, T} <- Cs ]]),
    mk_t_err(pos(element(1, hd(Cs))), Msg);
mk_error({bad_named_argument, [], Name}) ->
    Msg = io_lib:format("Named argument ~s supplied to function expecting no named arguments.",
                        [pp(Name)]),
    mk_t_err(pos(Name), Msg);
mk_error({bad_named_argument, Args, Name}) ->
    Msg = io_lib:format("Named argument `~s` is not one of the expected named arguments~s",
                        [pp(Name),
                        [ io_lib:format("\n  - `~s`", [pp_typed("", Arg, Type)])
                          || {named_arg_t, _, Arg, Type, _} <- Args ]]),
    mk_t_err(pos(Name), Msg);
mk_error({unsolved_named_argument_constraint, #named_argument_constraint{name = Name, type = Type}}) ->
    Msg = io_lib:format("Named argument ~s supplied to function with unknown named arguments.",
                        [pp_typed("", Name, Type)]),
    mk_t_err(pos(Name), Msg);
mk_error({reserved_entrypoint, Name, Def}) ->
    Msg = io_lib:format("The name '~s' is reserved and cannot be used for a "
                        "top-level contract function.", [Name]),
    mk_t_err(pos(Def), Msg);
mk_error({duplicate_definition, Name, Locs}) ->
    Msg = io_lib:format("Duplicate definitions of `~s` at~s",
                        [Name, [ ["\n  - ", pp_loc(L)] || L <- Locs ]]),
    mk_t_err(pos(lists:last(Locs)), Msg);
mk_error({duplicate_scope, Kind, Name, OtherKind, L}) ->
    Msg = io_lib:format("The ~p `~s` has the same name as a ~p at ~s",
                        [Kind, pp(Name), OtherKind, pp_loc(L)]),
    mk_t_err(pos(Name), Msg);
mk_error({include, _, {string, Pos, Name}}) ->
    Msg = io_lib:format("Include of `~s` is not allowed, include only allowed at top level.",
                        [binary_to_list(Name)]),
    mk_t_err(pos(Pos), Msg);
mk_error({namespace, _Pos, {con, Pos, Name}, _Def}) ->
    Msg = io_lib:format("Nested namespaces are not allowed. Namespace `~s` is not defined at top level.",
                        [Name]),
    mk_t_err(pos(Pos), Msg);
mk_error({Contract, _Pos, {con, Pos, Name}, _Impls, _Def}) when ?IS_CONTRACT_HEAD(Contract) ->
    Msg = io_lib:format("Nested contracts are not allowed. Contract `~s` is not defined at top level.",
                        [Name]),
    mk_t_err(pos(Pos), Msg);
mk_error({type_decl, _, {id, Pos, Name}, _}) ->
    Msg = io_lib:format("Empty type declarations are not supported. Type `~s` lacks a definition",
                        [Name]),
    mk_t_err(pos(Pos), Msg);
mk_error({letval, _Pos, {id, Pos, Name}, _Def}) ->
    Msg = io_lib:format("Toplevel \"let\" definitions are not supported. Value `~s` could be replaced by 0-argument function.",
                        [Name]),
    mk_t_err(pos(Pos), Msg);
mk_error({stateful_not_allowed, Id, Fun}) ->
    Msg = io_lib:format("Cannot reference stateful function `~s` in the definition of non-stateful function `~s`.",
                        [pp(Id), pp(Fun)]),
    mk_t_err(pos(Id), Msg);
mk_error({stateful_not_allowed_in_guards, Id}) ->
    Msg = io_lib:format("Cannot reference stateful function `~s` in a pattern guard.",
                        [pp(Id)]),
    mk_t_err(pos(Id), Msg);
mk_error({value_arg_not_allowed, Value, Fun}) ->
    Msg = io_lib:format("Cannot pass non-zero value argument `~s` in the definition of non-stateful function `~s`.",
                        [pp_expr(Value), pp(Fun)]),
    mk_t_err(pos(Value), Msg);
mk_error({init_depends_on_state, Which, [_Init | Chain]}) ->
    WhichCalls = fun("put") -> ""; ("state") -> ""; (_) -> ", which calls" end,
    Msg = io_lib:format("The `init` function should return the initial state as its result and cannot ~s the state, but it calls~s",
                        [if Which == put -> "write"; true -> "read" end,
                         [ io_lib:format("\n  - `~s` (at ~s)~s", [Fun, pp_loc(Ann), WhichCalls(Fun)])
                           || {[_, Fun], Ann} <- Chain]]),
    mk_t_err(pos(element(2, hd(Chain))), Msg);
mk_error({missing_body_for_let, Ann}) ->
    Msg = io_lib:format("Let binding must be followed by an expression.", []),
    mk_t_err(pos(Ann), Msg);
mk_error({public_modifier_in_contract, Decl}) ->
    Decl1 = mk_entrypoint(Decl),
    Msg = io_lib:format("Use `entrypoint` instead of `function` for public function `~s`: `~s`",
                        [pp_expr(element(3, Decl)),
                         prettypr:format(aeso_pretty:decl(Decl1))]),
    mk_t_err(pos(Decl), Msg);
mk_error({init_must_be_an_entrypoint, Decl}) ->
    Decl1 = mk_entrypoint(Decl),
    Msg = io_lib:format("The init function must be an entrypoint: ~s",
                        [prettypr:format(prettypr:nest(2, aeso_pretty:decl(Decl1)))]),
    mk_t_err(pos(Decl), Msg);
mk_error({init_must_not_be_payable, Decl}) ->
    Msg = io_lib:format("The init function cannot be payable. "
                        "You don't need the 'payable' annotation to be able to attach "
                        "funds to the create contract transaction.",
                        []),
    mk_t_err(pos(Decl), Msg);
mk_error({proto_must_be_entrypoint, Decl}) ->
    Decl1 = mk_entrypoint(Decl),
    Msg = io_lib:format("Use `entrypoint` for declaration of `~s`: `~s`",
                        [pp_expr(element(3, Decl)),
                         prettypr:format(aeso_pretty:decl(Decl1))]),
    mk_t_err(pos(Decl), Msg);
mk_error({proto_in_namespace, Decl}) ->
    Msg = io_lib:format("Namespaces cannot contain function prototypes.", []),
    mk_t_err(pos(Decl), Msg);
mk_error({entrypoint_in_namespace, Decl}) ->
    Msg = io_lib:format("Namespaces cannot contain entrypoints. Use `function` instead.", []),
    mk_t_err(pos(Decl), Msg);
mk_error({private_entrypoint, Decl}) ->
    Msg = io_lib:format("The entrypoint `~s` cannot be private. Use `function` instead.",
                        [pp_expr(element(3, Decl))]),
    mk_t_err(pos(Decl), Msg);
mk_error({private_and_public, Decl}) ->
    Msg = io_lib:format("The function `~s` cannot be both public and private.",
                        [pp_expr(element(3, Decl))]),
    mk_t_err(pos(Decl), Msg);
mk_error({contract_has_no_entrypoints, Con}) ->
    Msg = io_lib:format("The contract `~s` has no entrypoints. Since Sophia version 3.2, public "
                        "contract functions must be declared with the `entrypoint` keyword instead of "
                        "`function`.", [pp_expr(Con)]),
    mk_t_err(pos(Con), Msg);
mk_error({definition_in_contract_interface, Ann, {id, _, Id}}) ->
    Msg = "Contract interfaces cannot contain defined functions or entrypoints.",
    Cxt = io_lib:format("Fix: replace the definition of `~s` by a type signature.", [Id]),
    mk_t_err(pos(Ann), Msg, Cxt);
mk_error({unbound_type, Type}) ->
    Msg = io_lib:format("Unbound type ~s.", [pp_type(Type)]),
    mk_t_err(pos(Type), Msg);
mk_error({new_tuple_syntax, Ann, Ts}) ->
    Msg = io_lib:format("Invalid type `~s`. The syntax of tuple types changed in Sophia version 4.0. Did you mean `~s`",
                        [pp_type({args_t, Ann, Ts}), pp_type({tuple_t, Ann, Ts})]),
    mk_t_err(pos(Ann), Msg);
mk_error({map_in_map_key, Ann, KeyType}) ->
    Msg = io_lib:format("Invalid key type `~s`", [pp_type(KeyType)]),
    Cxt = "Map keys cannot contain other maps.",
    mk_t_err(pos(Ann), Msg, Cxt);
mk_error({cannot_call_init_function, Ann}) ->
    Msg = "The 'init' function is called exclusively by the create contract transaction "
          "and cannot be called from the contract code.",
    mk_t_err(pos(Ann), Msg);
mk_error({contract_treated_as_namespace, Ann, [Con, Fun] = QName}) ->
    Msg = io_lib:format("Invalid call to contract entrypoint `~s`.", [string:join(QName, ".")]),
    Cxt = io_lib:format("It must be called as `c.~s` for some `c : ~s`.", [Fun, Con]),
    mk_t_err(pos(Ann), Msg, Cxt);
mk_error({bad_top_level_decl, Decl}) ->
    What = case element(1, Decl) of
               letval -> "function or entrypoint";
               _      -> "contract or namespace"
           end,
    Id = element(3, Decl),
    Msg = io_lib:format("The definition of '~s' must appear inside a ~s.",
                        [pp_expr(Id), What]),
    mk_t_err(pos(Decl), Msg);
mk_error({unknown_byte_length, Type}) ->
    Msg = io_lib:format("Cannot resolve length of byte array.", []),
    mk_t_err(pos(Type), Msg);
mk_error({unsolved_bytes_constraint, Ann, concat, A, B, C}) ->
    Msg = io_lib:format("Failed to resolve byte array lengths in call to Bytes.concat with arguments of type\n"
                        "~s  (at ~s)\n~s  (at ~s)\nand result type\n~s  (at ~s)",
                        [pp_type("  - ", A), pp_loc(A), pp_type("  - ", B),
                         pp_loc(B), pp_type("  - ", C), pp_loc(C)]),
    mk_t_err(pos(Ann), Msg);
mk_error({unsolved_bytes_constraint, Ann, split, A, B, C}) ->
    Msg = io_lib:format("Failed to resolve byte array lengths in call to Bytes.split with argument of type\n"
                        "~s  (at ~s)\nand result types\n~s  (at ~s)\n~s  (at ~s)",
                        [ pp_type("  - ", C), pp_loc(C), pp_type("  - ", A), pp_loc(A),
                          pp_type("  - ", B), pp_loc(B)]),
    mk_t_err(pos(Ann), Msg);
mk_error({failed_to_get_compiler_version, Err}) ->
    Msg = io_lib:format("Failed to get compiler version. Error: ~p", [Err]),
    mk_t_err(pos(0, 0), Msg);
mk_error({compiler_version_mismatch, Ann, Version, Op, Bound}) ->
    PrintV = fun(V) -> string:join([integer_to_list(N) || N <- V], ".") end,
    Msg = io_lib:format("Cannot compile with this version of the compiler, "
                        "because it does not satisfy the constraint"
                        " ~s ~s ~s", [PrintV(Version), Op, PrintV(Bound)]),
    mk_t_err(pos(Ann), Msg);
mk_error({empty_record_or_map_update, Expr}) ->
    Msg = io_lib:format("Empty record/map update `~s`", [pp_expr(Expr)]),
    mk_t_err(pos(Expr), Msg);
mk_error({mixed_record_and_map, Expr}) ->
    Msg = io_lib:format("Mixed record fields and map keys in `~s`", [pp_expr(Expr)]),
    mk_t_err(pos(Expr), Msg);
mk_error({named_argument_must_be_literal_bool, Name, Arg}) ->
    Msg = io_lib:format("Invalid `~s` argument `~s`. "
                        "It must be either `true` or `false`.",
                        [Name, pp_expr(instantiate(Arg))]),
    mk_t_err(pos(Arg), Msg);
mk_error({conflicting_updates_for_field, Upd, Key}) ->
    Msg = io_lib:format("Conflicting updates for field '~s'", [Key]),
    mk_t_err(pos(Upd), Msg);
mk_error({ambiguous_main_contract, Ann}) ->
    Msg = "Could not deduce the main contract. You can point it out manually with the `main` keyword.",
    mk_t_err(pos(Ann), Msg);
mk_error({main_contract_undefined, Ann}) ->
    Msg = "No contract defined.",
    mk_t_err(pos(Ann), Msg);
mk_error({multiple_main_contracts, Ann}) ->
    Msg = "Only one main contract can be defined.",
    mk_t_err(pos(Ann), Msg);
mk_error({unify_varargs, When}) ->
    Msg = "Cannot infer types for variable argument list.",
    {Pos, Ctxt} = pp_when(When),
    mk_t_err(Pos, Msg, Ctxt);
mk_error({clone_no_contract, Ann}) ->
    Msg = "Chain.clone requires `ref` named argument of contract type.",
    mk_t_err(pos(Ann), Msg);
mk_error({contract_lacks_definition, Type, When}) ->
    Msg = io_lib:format(
            "~s is not implemented.",
            [pp_type(Type)]
           ),
    {Pos, Ctxt} = pp_when(When),
    mk_t_err(Pos, Msg, Ctxt);
mk_error({ambiguous_name, Name, QIds}) ->
    Msg = io_lib:format("Ambiguous name `~s` could be one of~s",
                        [pp(Name),
                         [io_lib:format("\n  - `~s` (at ~s)", [pp(QId), pp_loc(QId)]) || QId <- QIds]]),
    mk_t_err(pos(Name), Msg);
mk_error({using_undefined_namespace, Ann, Namespace}) ->
    Msg = io_lib:format("Cannot use undefined namespace ~s", [Namespace]),
    mk_t_err(pos(Ann), Msg);
mk_error({using_undefined_namespace_parts, Ann, Namespace, Parts}) ->
    PartsStr = lists:concat(lists:join(", ", Parts)),
    Msg = io_lib:format("The namespace ~s does not define the following names: ~s", [Namespace, PartsStr]),
    mk_t_err(pos(Ann), Msg);
mk_error({unknown_warning, Warning}) ->
    Msg = io_lib:format("Trying to report unknown warning: ~p", [Warning]),
    mk_t_err(pos(0, 0), Msg);
mk_error({empty_record_definition, Ann, Name}) ->
    Msg = io_lib:format("Empty record definitions are not allowed. Cannot define the record `~s`", [Name]),
    mk_t_err(pos(Ann), Msg);
mk_error({unimplemented_interface_function, ConId, InterfaceName, FunName}) ->
    Msg = io_lib:format("Unimplemented entrypoint `~s` from the interface `~s` in the contract `~s`", [FunName, InterfaceName, pp(ConId)]),
    mk_t_err(pos(ConId), Msg);
mk_error({referencing_undefined_interface, InterfaceId}) ->
    Msg = io_lib:format("Trying to implement or extend an undefined interface `~s`", [pp(InterfaceId)]),
    mk_t_err(pos(InterfaceId), Msg);
mk_error({missing_definition, Id}) ->
    Msg = io_lib:format("Missing definition of function `~s`", [name(Id)]),
    mk_t_err(pos(Id), Msg);
mk_error({parameterized_state, Ann}) ->
    Msg = "The state type cannot be parameterized",
    mk_t_err(pos(Ann), Msg);
mk_error({parameterized_event, Ann}) ->
    Msg = "The event type cannot be parameterized",
    mk_t_err(pos(Ann), Msg);
mk_error({missing_init_function, Con}) ->
    Msg = io_lib:format("Missing `init` function for the contract `~s`.", [name(Con)]),
    Cxt = "The `init` function can only be omitted if the state type is `unit`",
    mk_t_err(pos(Con), Msg, Cxt);
mk_error({higher_order_entrypoint, Ann, {id, _, Name}, Thing}) ->
    What = "higher-order (contains function types)",
    ThingS = case Thing of
                 {argument, X, T} -> io_lib:format("argument\n~s`\n", [pp_typed("  `", X, T)]);
                 {result, T}      -> io_lib:format("return type\n~s`\n", [pp_type("  `", T)])
             end,
    Bad = case Thing of
              {argument, _, _} -> io_lib:format("has a ~s type", [What]);
              {result, _}      -> io_lib:format("is ~s", [What])
          end,
    Msg = io_lib:format("The ~sof entrypoint `~s` ~s",
                        [ThingS, Name, Bad]),
    mk_t_err(pos(Ann), Msg);
mk_error({invalid_aens_resolve_type, Ann, T}) ->
    Msg = io_lib:format("Invalid return type of `AENS.resolve`:\n"
                        "~s`\n"
                        "It must be a `string` or a pubkey type (`address`, `oracle`, etc)",
                        [pp_type("  `", T)]),
    mk_t_err(pos(Ann), Msg);
mk_error({invalid_oracle_type, Why, What, Ann, Type}) ->
    WhyS = case Why of higher_order -> "higher-order (contain function types)";
                       polymorphic  -> "polymorphic (contain type variables)" end,
    Msg = io_lib:format("Invalid oracle type\n~s`", [pp_type("  `", Type)]),
    Cxt = io_lib:format("The ~s type must not be ~s", [What, WhyS]),
    mk_t_err(pos(Ann), Msg, Cxt);
mk_error({interface_implementation_conflict, Contract, I1, I2, Fun}) ->
    Msg = io_lib:format("Both interfaces `~s` and `~s` implemented by "
                        "the contract `~s` have a function called `~s`",
                        [name(I1), name(I2), name(Contract), name(Fun)]),
    mk_t_err(pos(Contract), Msg);
mk_error({function_should_be_entrypoint, Impl, Base, Interface}) ->
    Msg = io_lib:format("`~s` must be declared as an entrypoint instead of a function "
                        "in order to implement the entrypoint `~s` from the interface `~s`",
                        [name(Impl), name(Base), name(Interface)]),
    mk_t_err(pos(Impl), Msg);
mk_error({entrypoint_cannot_be_stateful, Impl, Base, Interface}) ->
    Msg = io_lib:format("`~s` cannot be stateful because the entrypoint `~s` in the "
                        "interface `~s` is not stateful",
                        [name(Impl), name(Base), name(Interface)]),
    mk_t_err(pos(Impl), Msg);
mk_error({entrypoint_must_be_payable, Impl, Base, Interface}) ->
    Msg = io_lib:format("`~s` must be payable because the entrypoint `~s` in the "
                        "interface `~s` is payable",
                        [name(Impl), name(Base), name(Interface)]),
    mk_t_err(pos(Impl), Msg);
mk_error({unpreserved_payablity, Kind, ContractCon, InterfaceCon}) ->
    KindStr = case Kind of
                  contract -> "contract";
                  contract_interface -> "interface"
              end,
    Msg = io_lib:format("Non-payable ~s `~s` cannot implement payable interface `~s`",
                        [KindStr, name(ContractCon), name(InterfaceCon)]),
    mk_t_err(pos(ContractCon), Msg);
mk_error(Err) ->
    Msg = io_lib:format("Unknown error: ~p", [Err]),
    mk_t_err(pos(0, 0), Msg).

mk_warning({unused_include, FileName, SrcFile}) ->
    Msg = io_lib:format("The file `~s` is included but not used.", [FileName]),
    aeso_warnings:new(aeso_errors:pos(SrcFile, 0, 0), Msg);
mk_warning({unused_stateful, Ann, FunName}) ->
    Msg = io_lib:format("The function `~s` is unnecessarily marked as stateful.", [name(FunName)]),
    aeso_warnings:new(pos(Ann), Msg);
mk_warning({unused_variable, Ann, _Namespace, _Fun, VarName}) ->
    Msg = io_lib:format("The variable `~s` is defined but never used.", [VarName]),
    aeso_warnings:new(pos(Ann), Msg);
mk_warning({unused_typedef, Ann, QName, _Arity}) ->
    Msg = io_lib:format("The type `~s` is defined but never used.", [lists:last(QName)]),
    aeso_warnings:new(pos(Ann), Msg);
mk_warning({unused_return_value, Ann}) ->
    Msg = io_lib:format("Unused return value.", []),
    aeso_warnings:new(pos(Ann), Msg);
mk_warning({unused_function, Ann, FunName}) ->
    Msg = io_lib:format("The function `~s` is defined but never used.", [FunName]),
    aeso_warnings:new(pos(Ann), Msg);
mk_warning({shadowing, Ann, VarName, AnnOld}) ->
    Msg = io_lib:format("The definition of `~s` shadows an older definition at ~s.", [VarName, pp_loc(AnnOld)]),
    aeso_warnings:new(pos(Ann), Msg);
mk_warning({division_by_zero, Ann}) ->
    Msg = io_lib:format("Division by zero.", []),
    aeso_warnings:new(pos(Ann), Msg);
mk_warning({negative_spend, Ann}) ->
    Msg = io_lib:format("Negative spend.", []),
    aeso_warnings:new(pos(Ann), Msg);
mk_warning(Warn) ->
    Msg = io_lib:format("Unknown warning: ~p", [Warn]),
    aeso_warnings:new(Msg).

mk_entrypoint(Decl) ->
    Ann   = [entrypoint | lists:keydelete(public, 1,
                          lists:keydelete(private, 1,
                            aeso_syntax:get_ann(Decl))) -- [public, private]],
    aeso_syntax:set_ann(Ann, Decl).

pp_when({todo, What}) -> {pos(0, 0), io_lib:format("[TODO] ~p", [What])};
pp_when({at, Ann}) -> {pos(Ann), io_lib:format("at ~s", [pp_loc(Ann)])};
pp_when({check_typesig, Name, Inferred, Given}) ->
    {pos(Given),
     io_lib:format("when checking the definition of `~s`\n"
                   "  inferred type: `~s`\n"
                   "  given type:    `~s`",
         [Name, pp(instantiate(Inferred)), pp(instantiate(Given))])};
pp_when({infer_app, Fun, NamedArgs, Args, Inferred0, ArgTypes0}) ->
    Inferred = instantiate(Inferred0),
    ArgTypes = instantiate(ArgTypes0),
    {pos(Fun),
     io_lib:format("when checking the application of\n"
                   "  `~s`\n"
                   "to arguments~s",
                   [pp_typed("", Fun, Inferred),
                    [ ["\n  ", "`" ++ pp_expr(NamedArg) ++ "`"] || NamedArg <- NamedArgs ] ++
                    [ ["\n  ", "`" ++ pp_typed("", Arg, ArgT) ++ "`"]
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
             io_lib:format("when checking the assignment of the field `~s` to the old value `~s` and the new value `~s`",
                 [pp_typed("", {lvalue, [], LV}, FieldType),
                  pp(Id),
                  pp_typed("", E, InferredType)]);
         {field, _Ann, LV, E} ->
             io_lib:format("when checking the assignment of the field `~s` to the value `~s`",
                 [pp_typed("", {lvalue, [], LV}, FieldType),
                  pp_typed("", E, InferredType)]);
         {proj, _Ann, _Rec, _Fld} ->
             io_lib:format("when checking the record projection `~s` against the expected type `~s`",
                 [pp_typed("  ", Fld, FieldType),
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
                           "matches the expected type\n~s",
                           [pp_type("  ", RecType), WhyRec, pp_type("  ", InferredType)]
                          )
            };
        {field, _Ann, _LV, _Id, _E} ->
            {Pos,
             io_lib:format("when checking that the record type\n~s\n~s\n"
                           "matches the expected type\n~s",
                 [pp_type("  ", RecType), WhyRec, pp_type("  ", InferredType)])};
        {field, _Ann, _LV, _E} ->
            {Pos,
             io_lib:format("when checking that the record type\n~s\n~s\n"
                           "matches the expected type\n~s",
                 [pp_type("  ", RecType), WhyRec, pp_type("  ", InferredType)])};
        {proj, _Ann, Rec, _FldName} ->
            {pos(Rec),
             io_lib:format("when checking that the expression\n~s (at ~s)\nhas type\n~s\n~s",
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
     io_lib:format("when checking the type of the pattern `~s` against the expected type `~s`",
                   [pp_typed("", Pat, PatType),
                    pp_type(ExprType)])};
pp_when({check_expr, Expr, Inferred0, Expected0}) ->
    {Inferred, Expected} = instantiate({Inferred0, Expected0}),
    {pos(Expr),
     io_lib:format("when checking the type of the expression `~s` against the expected type `~s`",
                   [pp_typed("", Expr, Inferred), pp_type(Expected)])};
pp_when({checking_init_type, Ann}) ->
    {pos(Ann),
     io_lib:format("when checking that `init` returns a value of type `state`", [])};
pp_when({list_comp, BindExpr, Inferred0, Expected0}) ->
    {Inferred, Expected} = instantiate({Inferred0, Expected0}),
    {pos(BindExpr),
     io_lib:format("when checking rvalue of list comprehension binding `~s` against type `~s`",
                   [pp_typed("", BindExpr, Inferred), pp_type(Expected)])};
pp_when({check_named_arg_constraint, C}) ->
    {id, _, Name} = Arg = C#named_argument_constraint.name,
    [Type | _] = [ Type || {named_arg_t, _, {id, _, Name1}, Type, _} <- C#named_argument_constraint.args, Name1 == Name ],
    Err = io_lib:format("when checking named argument `~s` against inferred type `~s`",
                        [pp_typed("", Arg, Type), pp_type(C#named_argument_constraint.type)]),
    {pos(Arg), Err};
pp_when({checking_init_args, Ann, Con0, ArgTypes0}) ->
    Con = instantiate(Con0),
    ArgTypes = instantiate(ArgTypes0),
    {pos(Ann),
     io_lib:format("when checking arguments of `~s`'s init entrypoint to match\n(~s)",
                   [pp_type(Con), string:join([pp_type(A) || A <- ArgTypes], ", ")])
    };
pp_when({return_contract, App, Con0}) ->
    Con = instantiate(Con0),
    {pos(App)
    , io_lib:format("when checking that expression returns contract of type `~s`", [pp_type(Con)])
    };
pp_when({arg_name, Id1, Id2, When}) ->
    {Pos, Ctx} = pp_when(When),
    {Pos
    , io_lib:format("when unifying names of named arguments: `~s` and `~s`\n~s", [pp_expr(Id1), pp_expr(Id2), Ctx])
    };
pp_when({var_args, Ann, Fun}) ->
    {pos(Ann)
    , io_lib:format("when resolving arguments of variadic function `~s`", [pp_expr(Fun)])
    };
pp_when(unknown) -> {pos(0,0), ""}.

-spec pp_why_record(why_record()) -> {pos(), iolist()}.
pp_why_record({var_args, Ann, Fun}) ->
    {pos(Ann),
     io_lib:format("arising from resolution of variadic function `~s`",
                   [pp_expr(Fun)])};
pp_why_record(Fld = {field, _Ann, LV, _E}) ->
    {pos(Fld),
     io_lib:format("arising from an assignment of the field `~s`",
                   [pp_expr({lvalue, [], LV})])};
pp_why_record(Fld = {field, _Ann, LV, _Alias, _E}) ->
    {pos(Fld),
     io_lib:format("arising from an assignment of the field `~s`",
                   [pp_expr({lvalue, [], LV})])};
pp_why_record({proj, _Ann, Rec, FldName}) ->
    {pos(Rec),
     io_lib:format("arising from the projection of the field `~s`",
         [pp(FldName)])}.


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
    prettypr:format(prettypr:beside(prettypr:text(Label), aeso_pretty:expr(Expr, [show_generated])), 80, 80).

pp_type(Type) ->
    pp_type("", Type).
pp_type(Label, Type) ->
    prettypr:format(prettypr:beside(prettypr:text(Label), aeso_pretty:type(Type, [show_generated])), 80, 80).

src_file(T)      -> aeso_syntax:get_ann(file, T, no_file).
include_type(T)  -> aeso_syntax:get_ann(include_type, T, none).
line_number(T)   -> aeso_syntax:get_ann(line, T, 0).
column_number(T) -> aeso_syntax:get_ann(col, T, 0).

pos(T)    -> aeso_errors:pos(src_file(T), line_number(T), column_number(T)).
pos(L, C) -> aeso_errors:pos(L, C).

loc(T) ->
    {src_file(T), include_type(T), line_number(T), column_number(T)}.

pp_loc(T) ->
    {File, IncludeType, Line, Col} = loc(T),
    case {Line, Col} of
        {0, 0} -> "(builtin location)";
        _      -> case IncludeType of
                      none -> io_lib:format("line ~p, column ~p", [Line, Col]);
                      _    -> io_lib:format("line ~p, column ~p in ~s", [Line, Col, File])
                  end
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


plural(No, _Yes, [_]) -> No;
plural(_No, Yes, _)   -> Yes.
