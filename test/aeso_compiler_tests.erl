%%% -*- erlang-indent-level:4; indent-tabs-mode: nil -*-
%%%-------------------------------------------------------------------
%%% @copyright (C) 2018, Aeternity Anstalt
%%% @doc Test Sophia language compiler.
%%%
%%% @end
%%%-------------------------------------------------------------------

-module(aeso_compiler_tests).

-compile([export_all, nowarn_export_all]).

-include_lib("eunit/include/eunit.hrl").

run_test(Test) ->
    TestFun = list_to_atom(lists:concat([Test, "_test_"])),
    [ begin
          io:format("~s\n", [Label]),
          Fun()
      end || {Label, Fun} <- ?MODULE:TestFun() ],
    ok.

%%  Very simply test compile the given contracts. Only basic checks
%%  are made on the output, just that it is a binary which indicates
%%  that the compilation worked.
simple_compile_test_() ->
    [ {"Testing the " ++ ContractName ++ " contract",
       fun() ->
           case compile(ContractName) of
               #{fate_code := Code} ->
                   Code1 = aeb_fate_code:deserialize(aeb_fate_code:serialize(Code)),
                   ?assertMatch({X, X}, {Code1, Code});
               Error -> io:format("\n\n~p\n\n", [Error]), print_and_throw(Error)
           end
       end} || ContractName <- compilable_contracts()] ++
    [ {"Test file not found error",
       fun() ->
           {error, Errors} = aeso_compiler:file("does_not_exist.aes"),
           ExpErr = <<"File error:\ndoes_not_exist.aes: no such file or directory">>,
           check_errors([ExpErr], Errors)
       end} ] ++
    [ {"Testing error messages of " ++ ContractName,
       fun() ->
           Errors = compile(ContractName, [warn_all, warn_error]),
           check_errors(ExpectedErrors, Errors)
       end} ||
           {ContractName, ExpectedErrors} <- failing_contracts() ] ++
    [ {"Testing code generation error messages of " ++ ContractName,
       fun() ->
               Errors = compile(ContractName),
               check_errors([ExpectedError], Errors)
       end} ||
           {ContractName, ExpectedError} <- failing_code_gen_contracts()] ++
    [ {"Testing include with explicit files",
       fun() ->
           FileSystem = maps:from_list(
               [ begin
                   {ok, Bin} = file:read_file(filename:join([aeso_test_utils:contract_path(), File])),
                   {File, Bin}
                 end || File <- ["included.aes", "../contracts/included2.aes"] ]),
           #{byte_code := Code1} = compile("include", [{include, {explicit_files, FileSystem}}]),
           #{byte_code := Code2} = compile("include"),
           ?assertMatch(true, Code1 == Code2)
       end} ] ++
    [ {"Testing deadcode elimination",
       fun() ->
           #{ byte_code := NoDeadCode } = compile("nodeadcode"),
           #{ byte_code := DeadCode   } = compile("deadcode"),
           SizeNoDeadCode = byte_size(NoDeadCode),
           SizeDeadCode   = byte_size(DeadCode),
           Delta          = 20,
           ?assertMatch({_, _, true}, {SizeDeadCode, SizeNoDeadCode, SizeDeadCode + Delta < SizeNoDeadCode}),
           ok
       end} ] ++
    [ {"Testing warning messages",
       fun() ->
           #{ warnings := Warnings } = compile("warnings", [warn_all]),
           check_warnings(warnings(), Warnings)
       end} ] ++
    [].

%% Check if all modules in the standard library compile
stdlib_test_() ->
    {ok, Files} = file:list_dir(aeso_stdlib:stdlib_include_path()),
    [ { "Testing " ++ File ++ " from the stdlib",
      fun() ->
          String = "include \"" ++ File ++ "\"\nmain contract Test =\n  entrypoint f(x) = x",
          Options = [{src_file, File}],
          case aeso_compiler:from_string(String, Options) of
              {ok, #{fate_code := Code}} ->
                  Code1 = aeb_fate_code:deserialize(aeb_fate_code:serialize(Code)),
                  ?assertMatch({X, X}, {Code1, Code});
              {error, Error} -> io:format("\n\n~p\n\n", [Error]), print_and_throw(Error)
          end
      end} || File <- Files,
              lists:suffix(".aes", File)
    ].

check_errors(no_error, Actual) -> ?assertMatch(#{}, Actual);
check_errors(Expect, #{}) ->
    ?assertEqual({error, Expect}, ok);
check_errors(Expect0, Actual0) ->
    Expect = lists:sort(Expect0),
    Actual = [ list_to_binary(string:trim(aeso_errors:pp(Err))) || Err <- Actual0 ],
    case {Expect -- Actual, Actual -- Expect} of
        {[], Extra}   -> ?assertMatch({unexpected, []}, {unexpected, Extra});
        {Missing, []} -> ?assertMatch({missing, []}, {missing, Missing});
        {Missing, Extra} -> ?assertEqual(Missing, Extra)
    end.

check_warnings(Expect0, Actual0) ->
    Expect = lists:sort(Expect0),
    Actual = [ list_to_binary(string:trim(aeso_warnings:pp(Warn))) || Warn <- Actual0 ],
    case {Expect -- Actual, Actual -- Expect} of
        {[], Extra}   -> ?assertMatch({unexpected, []}, {unexpected, Extra});
        {Missing, []} -> ?assertMatch({missing, []}, {missing, Missing});
        {Missing, Extra} -> ?assertEqual(Missing, Extra)
    end.

compile(Name) ->
    compile( Name, [{include, {file_system, [aeso_test_utils:contract_path()]}}]).

compile(Name, Options) ->
    String = aeso_test_utils:read_contract(Name),
    Options1 =
        case lists:member(Name, debug_mode_contracts()) of
            true  -> [debug_mode];
            false -> []
        end ++
        [ {src_file, Name ++ ".aes"}
        , {include, {file_system, [aeso_test_utils:contract_path()]}}
        ] ++ Options,
    case aeso_compiler:from_string(String, Options1) of
        {ok, Map}                                        -> Map;
        {error, ErrorString} when is_binary(ErrorString) -> ErrorString;
        {error, Errors}                                  -> Errors
    end.

%% compilable_contracts() -> [ContractName].
%%  The currently compilable contracts.

compilable_contracts() ->
    ["complex_types",
     "counter",
     "dutch_auction",
     "environment",
     "factorial",
     "functions",
     "fundme",
     "identity",
     "maps",
     "oracles",
     "remote_call",
     "remote_call_ambiguous_record",
     "simple",
     "simple_storage",
     "spend_test",
     "stack",
     "test",
     "builtin_bug",
     "builtin_map_get_bug",
     "lc_record_bug",
     "nodeadcode",
     "deadcode",
     "variant_types",
     "state_handling",
     "events",
     "include",
     "basic_auth",
     "basic_auth_tx",
     "bitcoin_auth",
     "address_literals",
     "bytes_equality",
     "address_chain",
     "namespace_bug",
     "bytes_to_x",
     "bytes_concat",
     "aens",
     "aens_update",
     "tuple_match",
     "cyclic_include",
     "stdlib_include",
     "double_include",
     "manual_stdlib_include",
     "list_comp",
     "payable",
     "unapplied_builtins",
     "underscore_number_literals",
     "pairing_crypto",
     "qualified_constructor",
     "let_patterns",
     "lhs_matching",
     "more_strings",
     "protected_call",
     "hermetization_turnoff",
     "multiple_contracts",
     "clone",
     "clone_simple",
     "create",
     "child_contract_init_bug",
     "using_namespace",
     "assign_patterns",
     "patterns_guards",
     "pipe_operator",
     "contract_polymorphism",
     "contract_interface_polymorphism",
     "test" % Custom general-purpose test file. Keep it last on the list.
    ].

debug_mode_contracts() ->
    ["hermetization_turnoff"].

%% Contracts that should produce type errors

-define(Pos(Kind, File, Line, Col), (list_to_binary(Kind))/binary, " error in '",
                                    (list_to_binary(File))/binary, ".aes' at line " ??Line ", col " ??Col ":\n").
-define(Pos(Line, Col), ?Pos(__Kind, __File, Line, Col)).

-define(ERROR(Kind, Name, Errs),
    (fun() ->
        __Kind = Kind,
        __File = ??Name,
        {__File, Errs}
     end)()).

-define(TYPE_ERROR(Name, Errs), ?ERROR("Type", Name, Errs)).
-define(PARSE_ERROR(Name, Errs), ?ERROR("Parse", Name, Errs)).

-define(PosW(Kind, File, Line, Col), (list_to_binary(Kind))/binary, " in '",
                                     (list_to_binary(File))/binary, ".aes' at line " ??Line ", col " ??Col ":\n").
-define(PosW(Line, Col), ?PosW(__Kind, __File, Line, Col)).

-define(WARNING(Name, Warns),
    (fun() ->
        __Kind = "Warning",
        __File = ??Name,
        Warns
     end)()).

warnings() ->
    ?WARNING(warnings,
     [<<?PosW(0, 0)
        "The file `Triple.aes` is included but not used.">>,
      <<?PosW(13, 3)
        "The function `h` is defined but never used.">>,
      <<?PosW(19, 3)
        "The type `unused_type` is defined but never used.">>,
      <<?PosW(23, 54)
        "Negative spend.">>,
      <<?PosW(27, 9)
        "The definition of `x` shadows an older definition at line 26, column 9.">>,
      <<?PosW(30, 36)
        "Division by zero.">>,
      <<?PosW(32, 3)
        "The function `unused_stateful` is unnecessarily marked as stateful.">>,
      <<?PosW(35, 31)
        "The variable `unused_arg` is defined but never used.">>,
      <<?PosW(36, 9)
        "The variable `unused_var` is defined but never used.">>,
      <<?PosW(41, 3)
        "The function `unused_function` is defined but never used.">>,
      <<?PosW(42, 3)
        "The function `recursive_unused_function` is defined but never used.">>,
      <<?PosW(43, 3)
        "The function `called_unused_function1` is defined but never used.">>,
      <<?PosW(44, 3)
        "The function `called_unused_function2` is defined but never used.">>,
      <<?PosW(48, 5)
        "Unused return value.">>
     ]).

failing_contracts() ->
    {ok, V} = aeso_compiler:numeric_version(),
    Version = list_to_binary(string:join([integer_to_list(N) || N <- V], ".")),
    %% Parse errors
    [ ?PARSE_ERROR(field_parse_error,
       [<<?Pos(5, 26)
          "Cannot use nested fields or keys in record construction: p.x">>])
    , ?PARSE_ERROR(vsemi,  [<<?Pos(3, 3) "Unexpected indentation. Did you forget a '}'?">>])
    , ?PARSE_ERROR(vclose, [<<?Pos(4, 3) "Unexpected indentation. Did you forget a ']'?">>])
    , ?PARSE_ERROR(indent_fail, [<<?Pos(3, 2) "Unexpected token 'entrypoint'.">>])
    , ?PARSE_ERROR(assign_pattern_to_pattern, [<<?Pos(3, 22) "Unexpected token '='.">>])

    %% Type errors
    , ?TYPE_ERROR(name_clash,
       [<<?Pos(14, 3)
          "Duplicate definitions of `abort` at\n"
          "  - (builtin location)\n"
          "  - line 14, column 3">>,
        <<?Pos(15, 3)
          "Duplicate definitions of `require` at\n"
          "  - (builtin location)\n"
          "  - line 15, column 3">>,
        <<?Pos(11, 3)
          "Duplicate definitions of `double_def` at\n"
          "  - line 10, column 3\n"
          "  - line 11, column 3">>,
        <<?Pos(5, 3)
          "Duplicate definitions of `double_proto` at\n"
          "  - line 4, column 3\n"
          "  - line 5, column 3">>,
        <<?Pos(8, 3)
          "Duplicate definitions of `proto_and_def` at\n"
          "  - line 7, column 3\n"
          "  - line 8, column 3">>,
        <<?Pos(16, 3)
          "Duplicate definitions of `put` at\n"
          "  - (builtin location)\n"
          "  - line 16, column 3">>,
        <<?Pos(17, 3)
          "Duplicate definitions of `state` at\n"
          "  - (builtin location)\n"
          "  - line 17, column 3">>])
    , ?TYPE_ERROR(type_errors,
       [<<?Pos(17, 23)
          "Unbound variable `zz`">>,
        <<?Pos(26, 9)
          "Cannot unify `int` and `list(int)`\n"
          "when checking the application of\n"
          "  `(::) : (int, list(int)) => list(int)`\n"
          "to arguments\n"
          "  `x : int`\n"
          "  `x : int`">>,
        <<?Pos(9, 48)
          "Cannot unify `string` and `int`\n"
          "when checking the assignment of the field `x : map(string, string)` "
          "to the old value `__x` and the new value `__x {[\"foo\"] @ x = x + 1} : map(string, int)`">>,
        <<?Pos(34, 47)
          "Cannot unify `int` and `string`\n"
          "when checking the type of the expression `1 : int` "
          "against the expected type `string`">>,
        <<?Pos(34, 52)
          "Cannot unify `string` and `int`\n"
          "when checking the type of the expression `\"bla\" : string` "
          "against the expected type `int`">>,
        <<?Pos(32, 18)
          "Cannot unify `string` and `int`\n"
          "when checking the type of the expression `\"x\" : string` "
          "against the expected type `int`">>,
        <<?Pos(11, 58)
          "Cannot unify `string` and `int`\n"
          "when checking the type of the expression `\"foo\" : string` "
          "against the expected type `int`">>,
        <<?Pos(38, 13)
          "Cannot unify `int` and `string`\n"
          "when comparing the types of the if-branches\n"
          "  - w : int (at line 38, column 13)\n"
          "  - z : string (at line 39, column 10)">>,
        <<?Pos(22, 40)
          "Not a record type: `string`\n"
          "arising from the projection of the field `y`">>,
        <<?Pos(21, 44)
          "Not a record type: `string`\n"
          "arising from an assignment of the field `y`">>,
        <<?Pos(20, 40)
          "Not a record type: `string`\n"
          "arising from an assignment of the field `y`">>,
        <<?Pos(19, 37)
          "Not a record type: `string`\n"
          "arising from an assignment of the field `y`">>,
        <<?Pos(13, 27)
          "Ambiguous record type with field `y` could be one of\n"
          "  - `r` (at line 4, column 10)\n"
          "  - `r'` (at line 5, column 10)">>,
        <<?Pos(26, 7)
          "Repeated name `x` in the pattern `x :: x`">>,
        <<?Pos(44, 14)
          "Repeated names `x`, `y` in the pattern `(x : int, y, x : string, y : bool)`">>,
        <<?Pos(44, 39)
          "Cannot unify `int` and `string`\n"
          "when checking the type of the expression `x : int` "
          "against the expected type `string`">>,
        <<?Pos(44, 72)
          "Cannot unify `int` and `string`\n"
          "when checking the type of the expression `x : int` "
          "against the expected type `string`">>,
        <<?Pos(14, 24)
          "No record type with fields `y`, `z`">>,
        <<?Pos(15, 26)
          "The field `z` is missing when constructing an element of type `r2`">>,
        <<?Pos(15, 24)
          "Record type `r2` does not have field `y`">>,
        <<?Pos(47, 5)
          "Let binding must be followed by an expression.">>,
        <<?Pos(50, 5)
          "Let binding must be followed by an expression.">>,
        <<?Pos(54, 5)
          "Let binding must be followed by an expression.">>,
        <<?Pos(58, 5)
          "Let binding must be followed by an expression.">>,
        <<?Pos(63, 5)
          "Cannot unify `int` and `bool`\n"
          "when checking the type of the expression `id(n) : int` "
          "against the expected type `bool`">>])
    , ?TYPE_ERROR(init_type_error,
       [<<?Pos(7, 3)
          "Cannot unify `string` and `map(int, int)`\n"
          "when checking that `init` returns a value of type `state`">>])
    , ?TYPE_ERROR(missing_state_type,
       [<<?Pos(5, 3)
          "Cannot unify `string` and `unit`\n"
          "when checking that `init` returns a value of type `state`">>])
    , ?TYPE_ERROR(missing_fields_in_record_expression,
       [<<?Pos(7, 42)
          "The field `x` is missing when constructing an element of type `r('a)`">>,
        <<?Pos(8, 42)
          "The field `y` is missing when constructing an element of type `r(int)`">>,
        <<?Pos(6, 42)
          "The fields `y`, `z` are missing when constructing an element of type `r('a)`">>])
    , ?TYPE_ERROR(namespace_clash_builtin,
       [<<?Pos(4, 10)
          "The contract `Call` has the same name as a namespace at (builtin location)">>])
    , ?TYPE_ERROR(namespace_clash_included,
       [<<?Pos(5, 11)
          "The namespace `BLS12_381` has the same name as a namespace at line 1, column 11 in BLS12_381.aes">>])
    , ?TYPE_ERROR(namespace_clash_same_file,
       [<<?Pos(4, 11)
          "The namespace `Nmsp` has the same name as a namespace at line 1, column 11">>])
    , ?TYPE_ERROR(bad_events,
        [<<?Pos(9, 25)
           "The indexed type `string` is not a word type">>,
         <<?Pos(10, 25)
           "The indexed type `alias_string` equals `string` which is not a word type">>])
    , ?TYPE_ERROR(bad_events2,
        [<<?Pos(9, 7)
           "The event constructor `BadEvent1` has too many non-indexed values (max 1)">>,
         <<?Pos(10, 7)
           "The event constructor `BadEvent2` has too many indexed values (max 3)">>])
    , ?TYPE_ERROR(type_clash,
        [<<?Pos(12, 42)
           "Cannot unify `int` and `string`\n"
           "when checking the type of the expression `r.foo() : map(int, string)` "
           "against the expected type `map(string, int)`">>])
    , ?TYPE_ERROR(not_toplevel_include,
                  [<<?Pos(2, 11)
                     "Include of `included.aes` is not allowed, include only allowed at top level.">>])
    , ?TYPE_ERROR(not_toplevel_namespace,
                  [<<?Pos(2, 13)
                     "Nested namespaces are not allowed. Namespace `Foo` is not defined at top level.">>])
    , ?TYPE_ERROR(not_toplevel_contract,
        [<<?Pos(2, 12)
           "Nested contracts are not allowed. Contract `Con` is not defined at top level.">>])
    , ?TYPE_ERROR(bad_address_literals,
        [<<?Pos(11, 5)
           "Cannot unify `address` and `oracle(int, bool)`\n"
           "when checking the type of the expression `ak_2gx9MEFxKvY9vMG5YnqnXWv1hCsX7rgnfvBLJS4aQurustR1rt : address` "
           "against the expected type `oracle(int, bool)`">>,
         <<?Pos(9, 5)
           "Cannot unify `address` and `Remote`\n"
           "when checking the type of the expression `ak_2gx9MEFxKvY9vMG5YnqnXWv1hCsX7rgnfvBLJS4aQurustR1rt : address` "
           "against the expected type `Remote`">>,
         <<?Pos(7, 5)
           "Cannot unify `address` and `bytes(32)`\n"
           "when checking the type of the expression `ak_2gx9MEFxKvY9vMG5YnqnXWv1hCsX7rgnfvBLJS4aQurustR1rt : address` "
           "against the expected type `bytes(32)`">>,
         <<?Pos(14, 5)
           "Cannot unify `oracle('a, 'b)` and `oracle_query(int, bool)`\n"
           "when checking the type of the expression "
           "`ok_2YNyxd6TRJPNrTcEDCe9ra59SVUdp9FR9qWC5msKZWYD9bP9z5 : oracle('a, 'b)` "
           "against the expected type `oracle_query(int, bool)`">>,
         <<?Pos(16, 5)
           "Cannot unify `oracle('c, 'd)` and `bytes(32)`\n"
           "when checking the type of the expression "
           "`ok_2YNyxd6TRJPNrTcEDCe9ra59SVUdp9FR9qWC5msKZWYD9bP9z5 : oracle('c, 'd)` "
           "against the expected type `bytes(32)`">>,
         <<?Pos(18, 5)
           "Cannot unify `oracle('e, 'f)` and `Remote`\n"
           "when checking the type of the expression "
           "`ok_2YNyxd6TRJPNrTcEDCe9ra59SVUdp9FR9qWC5msKZWYD9bP9z5 : oracle('e, 'f)` "
           "against the expected type `Remote`">>,
         <<?Pos(21, 5)
           "Cannot unify `oracle_query('g, 'h)` and `oracle(int, bool)`\n"
           "when checking the type of the expression "
           "`oq_2oRvyowJuJnEkxy58Ckkw77XfWJrmRgmGaLzhdqb67SKEL1gPY : oracle_query('g, 'h)` "
           "against the expected type `oracle(int, bool)`">>,
         <<?Pos(23, 5)
           "Cannot unify `oracle_query('i, 'j)` and `bytes(32)`\n"
           "when checking the type of the expression "
           "`oq_2oRvyowJuJnEkxy58Ckkw77XfWJrmRgmGaLzhdqb67SKEL1gPY : oracle_query('i, 'j)` "
           "against the expected type `bytes(32)`">>,
         <<?Pos(25, 5)
           "Cannot unify `oracle_query('k, 'l)` and `Remote`\n"
           "when checking the type of the expression "
           "`oq_2oRvyowJuJnEkxy58Ckkw77XfWJrmRgmGaLzhdqb67SKEL1gPY : oracle_query('k, 'l)` "
           "against the expected type `Remote`">>,
         <<?Pos(28, 5)
           "The type `address` is not a contract type\n"
           "when checking that the contract literal "
           "`ct_Ez6MyeTMm17YnTnDdHTSrzMEBKmy7Uz2sXu347bTDPgVH2ifJ` "
           "has the type `address`">>,
         <<?Pos(30, 5)
           "The type `oracle(int, bool)` is not a contract type\n"
           "when checking that the contract literal "
           "`ct_Ez6MyeTMm17YnTnDdHTSrzMEBKmy7Uz2sXu347bTDPgVH2ifJ` "
           "has the type `oracle(int, bool)`">>,
         <<?Pos(32, 5)
           "The type `bytes(32)` is not a contract type\n"
           "when checking that the contract literal "
           "`ct_Ez6MyeTMm17YnTnDdHTSrzMEBKmy7Uz2sXu347bTDPgVH2ifJ` "
           "has the type `bytes(32)`">>,
         <<?Pos(34, 5),
           "The type `address` is not a contract type\n"
           "when checking that the call to `Address.to_contract` "
           "has the type `address`">>])
    , ?TYPE_ERROR(stateful,
       [<<?Pos(13, 35)
          "Cannot reference stateful function `Chain.spend` in the definition of non-stateful function `fail1`.">>,
        <<?Pos(14, 35)
          "Cannot reference stateful function `local_spend` in the definition of non-stateful function `fail2`.">>,
        <<?Pos(16, 15)
          "Cannot reference stateful function `Chain.spend` in the definition of non-stateful function `fail3`.">>,
        <<?Pos(20, 31)
          "Cannot reference stateful function `Chain.spend` in the definition of non-stateful function `fail4`.">>,
        <<?Pos(35, 47)
          "Cannot reference stateful function `Chain.spend` in the definition of non-stateful function `fail5`.">>,
        <<?Pos(48, 57)
          "Cannot pass non-zero value argument `1000` in the definition of non-stateful function `fail6`.">>,
        <<?Pos(49, 56)
          "Cannot pass non-zero value argument `1000` in the definition of non-stateful function `fail7`.">>,
        <<?Pos(52, 17)
          "Cannot pass non-zero value argument `1000` in the definition of non-stateful function `fail8`.">>])
    , ?TYPE_ERROR(bad_init_state_access,
       [<<?Pos(11, 5)
          "The `init` function should return the initial state as its result and cannot write the state, "
          "but it calls\n"
          "  - `set_state` (at line 11, column 5), which calls\n"
          "  - `roundabout` (at line 8, column 38), which calls\n"
          "  - `put` (at line 7, column 39)">>,
        <<?Pos(12, 5)
          "The `init` function should return the initial state as its result and cannot read the state, "
          "but it calls\n"
          "  - `new_state` (at line 12, column 5), which calls\n"
          "  - `state` (at line 5, column 29)">>,
        <<?Pos(13, 13)
          "The `init` function should return the initial state as its result and cannot read the state, "
          "but it calls\n"
          "  - `state` (at line 13, column 13)">>])
    , ?TYPE_ERROR(modifier_checks,
       [<<?Pos(11, 3)
          "The function `all_the_things` cannot be both public and private.">>,
        <<?Pos(3, 3)
          "Namespaces cannot contain entrypoints. Use `function` instead.">>,
        <<?Pos(5, 10)
          "The contract `Remote` has no entrypoints. Since Sophia version 3.2, "
          "public contract functions must be declared with the `entrypoint` "
          "keyword instead of `function`.">>,
        <<?Pos(12, 3)
          "The entrypoint `wha` cannot be private. Use `function` instead.">>,
        <<?Pos(6, 3)
          "Use `entrypoint` for declaration of `foo`: `entrypoint foo : () => unit`">>,
        <<?Pos(10, 3)
          "Use `entrypoint` instead of `function` for public function `foo`: `entrypoint foo() = ()`">>,
        <<?Pos(6, 3)
          "Use `entrypoint` instead of `function` for public function `foo`: `entrypoint foo : () => unit`">>])
    , ?TYPE_ERROR(list_comp_not_a_list,
      [<<?Pos(2, 36)
         "Cannot unify `int` and `list('a)`\n"
         "when checking rvalue of list comprehension binding `1 : int` against type `list('a)`">>
      ])
    , ?TYPE_ERROR(list_comp_if_not_bool,
      [<<?Pos(2, 44)
         "Cannot unify `int` and `bool`\n"
         "when checking the type of the expression `3 : int` against the expected type `bool`">>
      ])
    , ?TYPE_ERROR(list_comp_bad_shadow,
      [<<?Pos(2, 53)
         "Cannot unify `int` and `string`\n"
         "when checking the type of the pattern `x : int` against the expected type `string`">>
      ])
    , ?TYPE_ERROR(map_as_map_key,
       [<<?Pos(5, 47)
         "Invalid key type `map(int, int)`\n"
         "Map keys cannot contain other maps.">>,
        <<?Pos(6, 31)
         "Invalid key type `list(map(int, int))`\n"
         "Map keys cannot contain other maps.">>,
        <<?Pos(6, 31)
         "Invalid key type `lm`\n"
         "Map keys cannot contain other maps.">>])
    , ?TYPE_ERROR(calling_init_function,
       [<<?Pos(7, 28)
          "The 'init' function is called exclusively by the create contract transaction "
          "and cannot be called from the contract code.">>])
    , ?TYPE_ERROR(bad_top_level_decl,
        [<<?Pos(1, 1) "The definition of 'square' must appear inside a contract or namespace.">>])
    , ?TYPE_ERROR(missing_event_type,
        [<<?Pos(3, 5)
           "Unbound variable `Chain.event`\n"
           "Did you forget to define the event type?">>])
    , ?TYPE_ERROR(bad_bytes_concat,
        [<<?Pos(12, 40)
           "Failed to resolve byte array lengths in call to Bytes.concat with arguments of type\n"
           "  - 'g  (at line 12, column 20)\n"
           "  - 'h  (at line 12, column 23)\n"
           "and result type\n"
           "  - bytes(10)  (at line 12, column 28)">>,
         <<?Pos(13, 28)
           "Failed to resolve byte array lengths in call to Bytes.concat with arguments of type\n"
           "  - 'd  (at line 13, column 20)\n"
           "  - 'e  (at line 13, column 23)\n"
           "and result type\n"
           "  - 'f  (at line 13, column 14)">>,
         <<?Pos(15, 5)
           "Cannot unify `bytes(26)` and `bytes(25)`\n"
           "when checking the type of the expression `Bytes.concat(x, y) : bytes(26)` "
           "against the expected type `bytes(25)`">>,
         <<?Pos(17, 5)
           "Failed to resolve byte array lengths in call to Bytes.concat with arguments of type\n"
           "  - bytes(6)  (at line 16, column 24)\n"
           "  - 'b  (at line 16, column 34)\n"
           "and result type\n"
           "  - 'c  (at line 16, column 39)">>,
         <<?Pos(19, 25)
           "Cannot resolve length of byte array.">>])
    , ?TYPE_ERROR(bad_bytes_split,
         [<<?Pos(13, 5)
            "Failed to resolve byte array lengths in call to Bytes.split with argument of type\n"
            "  - 'f  (at line 12, column 20)\n"
            "and result types\n"
            "  - 'e  (at line 12, column 25)\n"
            "  - bytes(20)  (at line 12, column 29)">>,
          <<?Pos(16, 5)
            "Failed to resolve byte array lengths in call to Bytes.split with argument of type\n"
            "  - bytes(15)  (at line 15, column 24)\n"
            "and result types\n"
            "  - 'c  (at line 16, column 5)\n"
            "  - 'd  (at line 16, column 5)">>,
          <<?Pos(19, 5)
            "Failed to resolve byte array lengths in call to Bytes.split with argument of type\n"
            "  - 'b  (at line 18, column 20)\n"
            "and result types\n"
            "  - bytes(20)  (at line 18, column 25)\n"
            "  - 'a  (at line 18, column 37)">>])
    , ?TYPE_ERROR(wrong_compiler_version,
        [<<?Pos(1, 1)
           "Cannot compile with this version of the compiler, "
           "because it does not satisfy the constraint ", Version/binary, " < 1.0">>,
         <<?Pos(2, 1)
           "Cannot compile with this version of the compiler, "
           "because it does not satisfy the constraint ", Version/binary, " == 9.9.9">>])
    , ?TYPE_ERROR(interface_with_defs,
         [<<?Pos(2, 3)
            "Contract interfaces cannot contain defined functions or entrypoints.\n"
            "Fix: replace the definition of `foo` by a type signature.">>])
    , ?TYPE_ERROR(contract_as_namespace,
         [<<?Pos(5, 28)
            "Invalid call to contract entrypoint `Foo.foo`.\n"
            "It must be called as `c.foo` for some `c : Foo`.">>])
    , ?TYPE_ERROR(toplevel_let,
                  [<<?Pos(2, 7)
                     "Toplevel \"let\" definitions are not supported. "
                     "Value `this_is_illegal` could be replaced by 0-argument function.">>])
    , ?TYPE_ERROR(empty_typedecl,
                  [<<?Pos(2, 8)
                     "Empty type declarations are not supported. "
                     "Type `t` lacks a definition">>])
    , ?TYPE_ERROR(higher_kinded_type,
                  [<<?Pos(2, 35)
                     "Type `'m` is a higher kinded type variable "
                     "(takes another type as an argument)">>])
    , ?TYPE_ERROR(bad_arity,
                  [<<?Pos(3, 20)
                     "Arity for id doesn't match. Expected 1, got 0">>,
                   <<?Pos(3, 25)
                     "Cannot unify `int` and `id`\n"
                     "when checking the type of the expression `123 : int` "
                     "against the expected type `id`">>,
                   <<?Pos(4, 20)
                     "Arity for id doesn't match. Expected 1, got 2">>,
                   <<?Pos(4, 35)
                     "Cannot unify `int` and `id(int, int)`\n"
                     "when checking the type of the expression `123 : int` "
                     "against the expected type `id(int, int)`">>])
    , ?TYPE_ERROR(bad_unnamed_map_update_default,
                  [<<?Pos(4, 17)
                     "Invalid map update with default">>])
    , ?TYPE_ERROR(non_functional_entrypoint,
                  [<<?Pos(2, 14)
                     "`f` was declared with an invalid type `int`. "
                     "Entrypoints and functions must have functional types">>])
    , ?TYPE_ERROR(bad_records,
        [<<?Pos(3, 16)
           "Mixed record fields and map keys in `{x = 0, [0] = 1}`">>,
         <<?Pos(4, 6)
           "Mixed record fields and map keys in `r {x = 0, [0] = 1}`">>,
         <<?Pos(5, 6)
           "Empty record/map update `r {}`">>
        ])
    , ?TYPE_ERROR(bad_protected_call,
        [<<?Pos(6, 22)
           "Invalid `protected` argument `(0 : int) == (1 : int) : bool`. "
           "It must be either `true` or `false`.">>
        ])
    , ?TYPE_ERROR(bad_function_block,
                  [<<?Pos(4, 5)
                     "Mismatch in the function block. Expected implementation/type declaration of g function">>,
                   <<?Pos(5, 5)
                     "Mismatch in the function block. Expected implementation/type declaration of g function">>
                  ])
    , ?TYPE_ERROR(just_an_empty_file,
                  [<<?Pos(0, 0)
                     "Empty contract">>
                  ])
    , ?TYPE_ERROR(bad_number_of_args,
                  [<<?Pos(3, 39)
                     "Cannot unify `() => unit` and `(int) => 'a`\n",
                     "when checking the application of\n"
                     "  `f : () => unit`\n"
                     "to arguments\n"
                     "  `1 : int`">>,
                   <<?Pos(4, 20)
                     "Cannot unify `(int, string) => 'e` and `(int) => 'd`\n"
                     "when checking the application of\n"
                     "  `g : (int, string) => 'e`\n"
                     "to arguments\n"
                     "  `1 : int`">>,
                   <<?Pos(5, 20)
                     "Cannot unify `(int, string) => 'c` and `(string) => 'b`\n"
                     "when checking the application of\n"
                     "  `g : (int, string) => 'c`\n"
                     "to arguments\n"
                     "  `\"Litwo, ojczyzno moja\" : string`">>
                  ])
    , ?TYPE_ERROR(bad_state,
                  [<<?Pos(4, 16)
                     "Conflicting updates for field 'foo'">>])
    , ?TYPE_ERROR(factories_type_errors,
                  [<<?Pos(10,18)
                    "Chain.clone requires `ref` named argument of contract type.">>,
                   <<?Pos(11,18)
                     "Cannot unify `(gas : int, value : int, protected : bool) => if(protected, option(void), void)` and `(gas : int, value : int, protected : bool, int, bool) => 'b`\n"
                     "when checking contract construction of type\n  (gas : int, value : int, protected : bool) =>\n    if(protected, option(void), void) (at line 11, column 18)\nagainst the expected type\n  (gas : int, value : int, protected : bool, int, bool) => 'b">>,
                   <<?Pos(12,37)
                     "Cannot unify `int` and `bool`\n"
                     "when checking named argument `gas : int` against inferred type `bool`">>,
                   <<?Pos(13,18),
                     "Kaboom is not implemented.\n"
                     "when resolving arguments of variadic function `Chain.create`">>,
                   <<?Pos(18,18)
                     "Cannot unify `(gas : int, value : int, protected : bool, int, bool) => if(protected, option(void), void)` and `(gas : int, value : int, protected : bool) => 'a`\n"
                     "when checking contract construction of type\n  (gas : int, value : int, protected : bool, int, bool) =>\n    if(protected, option(void), void) (at line 18, column 18)\nagainst the expected type\n  (gas : int, value : int, protected : bool) => 'a">>,
                   <<?Pos(19,42),
                     "Named argument `protected` is not one of the expected named arguments\n  - `value : int`">>,
                   <<?Pos(20,42),
                     "Cannot unify `int` and `bool`\n"
                     "when checking named argument `value : int` against inferred type `bool`">>
                  ])
    , ?TYPE_ERROR(ambiguous_main,
                  [<<?Pos(1,1)
                    "Could not deduce the main contract. You can point it out manually with the `main` keyword.">>
                  ])
    , ?TYPE_ERROR(no_main_contract,
                  [<<?Pos(0,0)
                     "No contract defined.">>
                  ])
    , ?TYPE_ERROR(multiple_main_contracts,
                   [<<?Pos(1,6)
                      "Only one main contract can be defined.">>
                   ])
    , ?TYPE_ERROR(using_namespace_ambiguous_name,
                  [ <<?Pos(13,23)
                      "Ambiguous name `A.f` could be one of\n"
                      "  - `Xa.f` (at line 2, column 3)\n"
                      "  - `Xb.f` (at line 5, column 3)">>
                  , <<?Pos(13,23)
                      "Unbound variable `A.f`">>
                  ])
    , ?TYPE_ERROR(using_namespace_wrong_scope,
                  [ <<?Pos(19,5)
                      "Unbound variable `f`">>
                  , <<?Pos(21,23)
                      "Unbound variable `f`">>
                  ])
    , ?TYPE_ERROR(using_namespace_undefined,
                  [<<?Pos(2,3)
                     "Cannot use undefined namespace MyUndefinedNamespace">>
                  ])
    , ?TYPE_ERROR(using_namespace_undefined_parts,
                  [<<?Pos(5,3)
                     "The namespace Nsp does not define the following names: a">>
                  ])
    , ?TYPE_ERROR(using_namespace_hidden_parts,
                  [<<?Pos(8,23)
                     "Unbound variable `g`">>
                  ])
    , ?TYPE_ERROR(stateful_pattern_guard,
                  [<<?Pos(8,12)
                     "Cannot reference stateful function `g` in a pattern guard.">>
                  ])
    , ?TYPE_ERROR(non_boolean_pattern_guard,
                  [<<?Pos(4,24)
                     "Cannot unify `string` and `bool`\n"
                     "when checking the type of the expression `\"y\" : string` "
                     "against the expected type `bool`">>
                  ])
    , ?TYPE_ERROR(empty_record_definition,
                  [<<?Pos(2,5)
                     "Empty record definitions are not allowed. Cannot define the record `r`">>
                  ])
    , ?TYPE_ERROR(warnings,
                  [<<?Pos(0, 0)
                      "The file `Triple.aes` is included but not used.">>,
                   <<?Pos(13, 3)
                     "The function `h` is defined but never used.">>,
                   <<?Pos(19, 3)
                     "The type `unused_type` is defined but never used.">>,
                   <<?Pos(23, 54)
                     "Negative spend.">>,
                   <<?Pos(27, 9)
                     "The definition of `x` shadows an older definition at line 26, column 9.">>,
                   <<?Pos(30, 36)
                     "Division by zero.">>,
                   <<?Pos(32, 3)
                     "The function `unused_stateful` is unnecessarily marked as stateful.">>,
                   <<?Pos(35, 31)
                     "The variable `unused_arg` is defined but never used.">>,
                   <<?Pos(36, 9)
                     "The variable `unused_var` is defined but never used.">>,
                   <<?Pos(41, 3)
                     "The function `unused_function` is defined but never used.">>,
                   <<?Pos(42, 3)
                     "The function `recursive_unused_function` is defined but never used.">>,
                   <<?Pos(43, 3)
                     "The function `called_unused_function1` is defined but never used.">>,
                   <<?Pos(44, 3)
                     "The function `called_unused_function2` is defined but never used.">>,
                   <<?Pos(48, 5)
                     "Unused return value.">>
                  ])
    , ?TYPE_ERROR(contract_interface_polymorphism_recursive,
                  [<<?Pos(1,24)
                     "Trying to implement or extend an undefined interface Z at line 1, column 24">>
                  ])
    , ?TYPE_ERROR(contract_interface_polymorphism_same_decl_multi_interface,
                  [<<?Pos(7,10)
                     "Unimplemented function f from the interface I in the contract C">>
                  ])
    , ?TYPE_ERROR(contract_polymorphism_missing_implementation,
                  [<<?Pos(7,10)
                     "Unimplemented function f from the interface I1 in the contract C">>
                  ])
    , ?TYPE_ERROR(contract_polymorphism_same_decl_multi_interface,
                  [<<?Pos(7,10)
                     "Unimplemented function f from the interface J in the contract C">>
                  ])
    , ?TYPE_ERROR(contract_polymorphism_undefined_interface,
                  [<<?Pos(1,14)
                     "Trying to implement or extend an undefined interface I at line 1, column 14">>
                  ])
    , ?TYPE_ERROR(contract_interface_polymorphism_undefined_interface,
                  [<<?Pos(1,24)
                     "Trying to implement or extend an undefined interface H at line 1, column 24">>
                  ])
    ].

-define(Path(File), "code_errors/" ??File).
-define(Msg(File, Line, Col, Err), <<?Pos("Code generation", ?Path(File), Line, Col) Err>>).

-define(FATE_ERR(File, Line, Col, Err), {?Path(File), ?Msg(File, Line, Col, Err)}).

failing_code_gen_contracts() ->
    [ ?FATE_ERR(missing_definition, 2, 14,
            "Missing definition of function 'foo'.")
    , ?FATE_ERR(higher_order_entrypoint, 2, 20,
            "The argument\n"
            "  f : (int) => int\n"
            "of entrypoint 'apply' has a higher-order (contains function types) type.")
    , ?FATE_ERR(higher_order_entrypoint_return, 2, 3,
            "The return type\n"
            "  (int) => int\n"
            "of entrypoint 'add' is higher-order (contains function types).")
    , ?FATE_ERR(missing_init_function, 1, 10,
            "Missing init function for the contract 'MissingInitFunction'.\n"
            "The 'init' function can only be omitted if the state type is 'unit'.")
    , ?FATE_ERR(parameterised_state, 3, 8,
            "The state type cannot be parameterized.")
    , ?FATE_ERR(parameterised_event, 3, 12,
            "The event type cannot be parameterized.")
    , ?FATE_ERR(polymorphic_aens_resolve, 4, 5,
            "Invalid return type of AENS.resolve:\n"
            "  'a\n"
            "It must be a string or a pubkey type (address, oracle, etc).")
    , ?FATE_ERR(bad_aens_resolve, 6, 5,
            "Invalid return type of AENS.resolve:\n"
            "  list(int)\n"
            "It must be a string or a pubkey type (address, oracle, etc).")
    , ?FATE_ERR(polymorphic_query_type, 3, 5,
            "Invalid oracle type\n"
            "  oracle('a, 'b)\n"
            "The query type must not be polymorphic (contain type variables).")
    , ?FATE_ERR(polymorphic_response_type, 3, 5,
            "Invalid oracle type\n"
            "  oracle(string, 'r)\n"
            "The response type must not be polymorphic (contain type variables).")
    , ?FATE_ERR(higher_order_query_type, 3, 5,
            "Invalid oracle type\n"
            "  oracle((int) => int, string)\n"
            "The query type must not be higher-order (contain function types).")
    , ?FATE_ERR(higher_order_response_type, 3, 5,
            "Invalid oracle type\n"
            "  oracle(string, (int) => int)\n"
            "The response type must not be higher-order (contain function types).")
    , ?FATE_ERR(child_with_decls, 2, 14,
            "Missing definition of function 'f'.")
    ].

validation_test_() ->
    [{"Validation fail: " ++ C1 ++ " /= " ++ C2,
      fun() ->
        Actual = case validate(C1, C2) of
                    {error, Errs} -> Errs;
                    ok -> #{}
                 end,
        check_errors(Expect, Actual)
      end} || {C1, C2, Expect} <- validation_fails()] ++
    [{"Validation of " ++ C,
      fun() ->
        ?assertEqual(ok, validate(C, C))
      end} || C <- compilable_contracts()].

validation_fails() ->
    [{"deadcode", "nodeadcode",
      [<<"Data error:\n"
         "Byte code does not match source code.\n"
         "- Functions in the source code but not in the byte code:\n"
         "    .MyList.map2">>]},
     {"validation_test1", "validation_test2",
      [<<"Data error:\n"
         "Byte code does not match source code.\n"
         "- The implementation of the function code_fail is different.\n"
         "- The attributes of the function attr_fail differ:\n"
         "    Byte code:   payable\n"
         "    Source code: \n"
         "- The type of the function type_fail differs:\n"
         "    Byte code:   integer => integer\n"
         "    Source code: {tvar,0} => {tvar,0}">>]},
     {"validation_test1", "validation_test3",
      [<<"Data error:\n"
         "Byte code contract is not payable, but source code contract is.">>]}].

validate(Contract1, Contract2) ->
    case compile(Contract1) of
        ByteCode = #{ fate_code := FCode } ->
            FCode1   = aeb_fate_code:serialize(aeb_fate_code:strip_init_function(FCode)),
            Source   = aeso_test_utils:read_contract(Contract2),
            aeso_compiler:validate_byte_code(
              ByteCode#{ byte_code := FCode1 }, Source,
              case lists:member(Contract2, debug_mode_contracts()) of
                  true  -> [debug_mode];
                  false -> []
              end ++
                  [{include, {file_system, [aeso_test_utils:contract_path()]}}]);
        Error -> print_and_throw(Error)
    end.

print_and_throw(Err) ->
    case Err of
        ErrBin when is_binary(ErrBin) ->
            io:format("\n~s", [ErrBin]),
            error(ErrBin);
        Errors ->
            io:format("Compilation error:\n~s", [string:join([aeso_errors:pp(E) || E <- Errors], "\n\n")]),
            error(compilation_error)
    end.
