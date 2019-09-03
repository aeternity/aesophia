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

%%  Very simply test compile the given contracts. Only basic checks
%%  are made on the output, just that it is a binary which indicates
%%  that the compilation worked.
simple_compile_test_() ->
    [ {"Testing the " ++ ContractName ++ " contract with the " ++ atom_to_list(Backend) ++ " backend",
       fun() ->
           case compile(Backend, ContractName) of
               #{byte_code := ByteCode,
                 contract_source := _,
                 type_info := _} when Backend == aevm ->
                   ?assertMatch(Code when is_binary(Code), ByteCode);
               #{fate_code := Code} when Backend == fate ->
                   Code1 = aeb_fate_code:deserialize(aeb_fate_code:serialize(Code)),
                   ?assertMatch({X, X}, {Code1, Code});
               ErrBin ->
                   io:format("\n~s", [ErrBin]),
                   error(ErrBin)
           end
       end} || ContractName <- compilable_contracts(), Backend <- [aevm, fate],
               not lists:member(ContractName, not_yet_compilable(Backend))] ++
    [ {"Testing error messages of " ++ ContractName,
       fun() ->
           Errors = compile(aevm, ContractName),
           check_errors(ExpectedErrors, Errors)
       end} ||
           {ContractName, ExpectedErrors} <- failing_contracts() ] ++
    [ {"Testing " ++ atom_to_list(Backend) ++ " code generation error messages of " ++ ContractName,
       fun() ->
           Errors = compile(Backend, ContractName),
           Expect =
               case is_binary(ExpectedError) of
                   true  -> [ExpectedError];
                   false ->
                       case proplists:get_value(Backend, ExpectedError, no_error) of
                           no_error -> no_error;
                           Err      -> [Err]
                       end
               end,
           check_errors(Expect, Errors)
       end} ||
           {ContractName, ExpectedError} <- failing_code_gen_contracts(),
           Backend <- [aevm, fate] ] ++
    [ {"Testing include with explicit files",
       fun() ->
           FileSystem = maps:from_list(
               [ begin
                   {ok, Bin} = file:read_file(filename:join([aeso_test_utils:contract_path(), File])),
                   {File, Bin}
                 end || File <- ["included.aes", "../contracts/included2.aes"] ]),
           #{byte_code := Code1} = compile(aevm, "include", [{include, {explicit_files, FileSystem}}]),
           #{byte_code := Code2} = compile(aevm, "include"),
           ?assertMatch(true, Code1 == Code2)
       end} ] ++
    [ {"Testing deadcode elimination for " ++ atom_to_list(Backend),
       fun() ->
           #{ byte_code := NoDeadCode } = compile(Backend, "nodeadcode"),
           #{ byte_code := DeadCode   } = compile(Backend, "deadcode"),
           SizeNoDeadCode = byte_size(NoDeadCode),
           SizeDeadCode   = byte_size(DeadCode),
           Delta          = if Backend == aevm -> 40;
                               Backend == fate -> 20 end,
           ?assertMatch({_, _, true}, {SizeDeadCode, SizeNoDeadCode, SizeDeadCode + Delta < SizeNoDeadCode}),
           ok
       end} || Backend <- [aevm, fate] ] ++
    [].

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

compile(Backend, Name) ->
    compile(Backend, Name,
            [{include, {file_system, [aeso_test_utils:contract_path()]}}]).

compile(Backend, Name, Options) ->
    String = aeso_test_utils:read_contract(Name),
    case aeso_compiler:from_string(String, [{src_file, Name ++ ".aes"}, {backend, Backend} | Options]) of
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
     "simple",
     "simple_storage",
     "spend_test",
     "stack",
     "test",
     "builtin_bug",
     "builtin_map_get_bug",
     "nodeadcode",
     "deadcode",
     "variant_types",
     "state_handling",
     "events",
     "include",
     "basic_auth",
     "bitcoin_auth",
     "address_literals",
     "bytes_equality",
     "address_chain",
     "namespace_bug",
     "bytes_to_x",
     "aens",
     "tuple_match",
     "cyclic_include",
     "stdlib_include",
     "double_include",
     "manual_stdlib_include",
     "list_comp",
     "payable"
    ].

not_yet_compilable(fate) -> [];
not_yet_compilable(aevm) -> [].

%% Contracts that should produce type errors

-define(Pos(File, Line, Col), "In '", (list_to_binary(File))/binary, ".aes' at line " ??Line ", col " ??Col ":\n").
-define(Pos(Line, Col), ?Pos(__File, Line, Col)).

-define(TEST(Name, Errs),
    (fun() ->
        __File = ??Name,
        {__File, Errs}
     end)()).

failing_contracts() ->
    %% Parse errors
    [ ?TEST(field_parse_error,
       [<<?Pos(5, 26)
          "Cannot use nested fields or keys in record construction: p.x">>])
    , ?TEST(vsemi,  [<<?Pos(3, 3) "Unexpected indentation. Did you forget a '}'?">>])
    , ?TEST(vclose, [<<?Pos(4, 3) "Unexpected indentation. Did you forget a ']'?">>])
    , ?TEST(indent_fail, [<<?Pos(3, 2) "Unexpected token 'entrypoint'.">>])

    %% Type errors
    , ?TEST(name_clash,
       [<<?Pos(14, 3)
          "Duplicate definitions of abort at\n"
          "  - (builtin location)\n"
          "  - line 14, column 3">>,
        <<?Pos(15, 3)
          "Duplicate definitions of require at\n"
          "  - (builtin location)\n"
          "  - line 15, column 3">>,
        <<?Pos(11, 3)
          "Duplicate definitions of double_def at\n"
          "  - line 10, column 3\n"
          "  - line 11, column 3">>,
        <<?Pos(5, 3)
          "Duplicate definitions of double_proto at\n"
          "  - line 4, column 3\n"
          "  - line 5, column 3">>,
        <<?Pos(8, 3)
          "Duplicate definitions of proto_and_def at\n"
          "  - line 7, column 3\n"
          "  - line 8, column 3">>,
        <<?Pos(16, 3)
          "Duplicate definitions of put at\n"
          "  - (builtin location)\n"
          "  - line 16, column 3">>,
        <<?Pos(17, 3)
          "Duplicate definitions of state at\n"
          "  - (builtin location)\n"
          "  - line 17, column 3">>])
    , ?TEST(type_errors,
       [<<?Pos(17, 23)
          "Unbound variable zz at line 17, column 23">>,
        <<?Pos(26, 9)
          "Cannot unify int\n"
          "         and list(int)\n"
          "when checking the application at line 26, column 9 of\n"
          "  (::) : (int, list(int)) => list(int)\n"
          "to arguments\n"
          "  x : int\n"
          "  x : int">>,
        <<?Pos(9, 48)
          "Cannot unify string\n"
          "         and int\n"
          "when checking the assignment of the field\n"
          "  x : map(string, string) (at line 9, column 48)\n"
          "to the old value __x and the new value\n"
          "  __x {[\"foo\"] @ x = x + 1} : map(string, int)">>,
        <<?Pos(34, 47)
          "Cannot unify int\n"
          "         and string\n"
          "when checking the type of the expression at line 34, column 47\n"
          "  1 : int\n"
          "against the expected type\n"
          "  string">>,
        <<?Pos(34, 52)
          "Cannot unify string\n"
          "         and int\n"
          "when checking the type of the expression at line 34, column 52\n"
          "  \"bla\" : string\n"
          "against the expected type\n"
          "  int">>,
        <<?Pos(32, 18)
          "Cannot unify string\n"
          "         and int\n"
          "when checking the type of the expression at line 32, column 18\n"
          "  \"x\" : string\n"
          "against the expected type\n"
          "  int">>,
        <<?Pos(11, 58)
          "Cannot unify string\n"
          "         and int\n"
          "when checking the type of the expression at line 11, column 58\n"
          "  \"foo\" : string\n"
          "against the expected type\n"
          "  int">>,
        <<?Pos(38, 13)
          "Cannot unify int\n"
          "         and string\n"
          "when comparing the types of the if-branches\n"
          "  - w : int (at line 38, column 13)\n"
          "  - z : string (at line 39, column 10)">>,
        <<?Pos(22, 40)
          "Not a record type: string\n"
          "arising from the projection of the field y (at line 22, column 40)">>,
        <<?Pos(21, 44)
          "Not a record type: string\n"
          "arising from an assignment of the field y (at line 21, column 44)">>,
        <<?Pos(20, 40)
          "Not a record type: string\n"
          "arising from an assignment of the field y (at line 20, column 40)">>,
        <<?Pos(19, 37)
          "Not a record type: string\n"
          "arising from an assignment of the field y (at line 19, column 37)">>,
        <<?Pos(13, 27)
          "Ambiguous record type with field y (at line 13, column 27) could be one of\n"
          "  - r (at line 4, column 10)\n"
          "  - r' (at line 5, column 10)">>,
        <<?Pos(26, 7)
          "Repeated name x in pattern\n"
          "  x :: x (at line 26, column 7)">>,
        <<?Pos(44, 14)
          "Repeated argument x to function repeated_arg (at line 44, column 14).">>,
        <<?Pos(44, 14)
          "Repeated argument y to function repeated_arg (at line 44, column 14).">>,
        <<?Pos(14, 24)
          "No record type with fields y, z (at line 14, column 24)">>,
        <<?Pos(15, 26)
          "The field z is missing when constructing an element of type r2 (at line 15, column 26)">>,
        <<?Pos(15, 24)
          "Record type r2 does not have field y (at line 15, column 24)">>,
        <<?Pos(47, 5)
          "Let binding at line 47, column 5 must be followed by an expression">>,
        <<?Pos(50, 5)
          "Let binding at line 50, column 5 must be followed by an expression">>,
        <<?Pos(54, 5)
          "Let binding at line 54, column 5 must be followed by an expression">>,
        <<?Pos(58, 5)
          "Let binding at line 58, column 5 must be followed by an expression">>])
    , ?TEST(init_type_error,
       [<<?Pos(7, 3)
          "Cannot unify string\n"
          "         and map(int, int)\n"
          "when checking that 'init' returns a value of type 'state' at line 7, column 3">>])
    , ?TEST(missing_state_type,
       [<<?Pos(5, 3)
          "Cannot unify string\n"
          "         and unit\n"
          "when checking that 'init' returns a value of type 'state' at line 5, column 3">>])
    , ?TEST(missing_fields_in_record_expression,
       [<<?Pos(7, 42)
          "The field x is missing when constructing an element of type r('a) (at line 7, column 42)">>,
        <<?Pos(8, 42)
          "The field y is missing when constructing an element of type r(int) (at line 8, column 42)">>,
        <<?Pos(6, 42)
          "The fields y, z are missing when constructing an element of type r('a) (at line 6, column 42)">>])
    , ?TEST(namespace_clash,
       [<<?Pos(4, 10)
          "The contract Call (at line 4, column 10) has the same name as a namespace at (builtin location)">>])
    , ?TEST(bad_events,
        [<<?Pos(9, 25)
           "The indexed type string (at line 9, column 25) is not a word type">>,
         <<?Pos(10, 25)
           "The indexed type alias_string (at line 10, column 25) equals string which is not a word type">>])
    , ?TEST(bad_events2,
        [<<?Pos(9, 7)
           "The event constructor BadEvent1 (at line 9, column 7) has too many non-indexed values (max 1)">>,
         <<?Pos(10, 7)
           "The event constructor BadEvent2 (at line 10, column 7) has too many indexed values (max 3)">>])
    , ?TEST(type_clash,
        [<<?Pos(12, 42)
           "Cannot unify int\n"
           "         and string\n"
           "when checking the record projection at line 12, column 42\n"
           "  r.foo : (gas : int, value : int) => Remote.themap\n"
           "against the expected type\n"
           "  (gas : int, value : int) => map(string, int)">>])
    , ?TEST(bad_include_and_ns,
        [<<?Pos(2, 11)
           "Include of 'included.aes' at line 2, column 11\nnot allowed, include only allowed at top level.">>,
         <<?Pos(3, 13)
           "Nested namespace not allowed\nNamespace 'Foo' at line 3, column 13 not defined at top level.">>])
    , ?TEST(bad_address_literals,
        [<<?Pos(32, 5)
           "The type bytes(32) is not a contract type\n"
           "when checking that the contract literal at line 32, column 5\n"
           "  ct_Ez6MyeTMm17YnTnDdHTSrzMEBKmy7Uz2sXu347bTDPgVH2ifJ\n"
           "has the type\n"
           "  bytes(32)">>,
         <<?Pos(30, 5)
           "The type oracle(int, bool) is not a contract type\n"
           "when checking that the contract literal at line 30, column 5\n"
           "  ct_Ez6MyeTMm17YnTnDdHTSrzMEBKmy7Uz2sXu347bTDPgVH2ifJ\n"
           "has the type\n"
           "  oracle(int, bool)">>,
         <<?Pos(28, 5)
           "The type address is not a contract type\n"
           "when checking that the contract literal at line 28, column 5\n"
           "  ct_Ez6MyeTMm17YnTnDdHTSrzMEBKmy7Uz2sXu347bTDPgVH2ifJ\n"
           "has the type\n"
           "  address">>,
         <<?Pos(25, 5)
           "Cannot unify oracle_query('a, 'b)\n"
           "         and Remote\n"
           "when checking the type of the expression at line 25, column 5\n"
           "  oq_2oRvyowJuJnEkxy58Ckkw77XfWJrmRgmGaLzhdqb67SKEL1gPY :\n"
           "    oracle_query('a, 'b)\n"
           "against the expected type\n"
           "  Remote">>,
         <<?Pos(23, 5)
           "Cannot unify oracle_query('c, 'd)\n"
           "         and bytes(32)\n"
           "when checking the type of the expression at line 23, column 5\n"
           "  oq_2oRvyowJuJnEkxy58Ckkw77XfWJrmRgmGaLzhdqb67SKEL1gPY :\n"
           "    oracle_query('c, 'd)\n"
           "against the expected type\n"
           "  bytes(32)">>,
         <<?Pos(21, 5)
           "Cannot unify oracle_query('e, 'f)\n"
           "         and oracle(int, bool)\n"
           "when checking the type of the expression at line 21, column 5\n"
           "  oq_2oRvyowJuJnEkxy58Ckkw77XfWJrmRgmGaLzhdqb67SKEL1gPY :\n"
           "    oracle_query('e, 'f)\n"
           "against the expected type\n"
           "  oracle(int, bool)">>,
         <<?Pos(18, 5)
           "Cannot unify oracle('g, 'h)\n"
           "         and Remote\n"
           "when checking the type of the expression at line 18, column 5\n"
           "  ok_2YNyxd6TRJPNrTcEDCe9ra59SVUdp9FR9qWC5msKZWYD9bP9z5 :\n"
           "    oracle('g, 'h)\n"
           "against the expected type\n"
           "  Remote">>,
         <<?Pos(16, 5)
           "Cannot unify oracle('i, 'j)\n"
           "         and bytes(32)\n"
           "when checking the type of the expression at line 16, column 5\n"
           "  ok_2YNyxd6TRJPNrTcEDCe9ra59SVUdp9FR9qWC5msKZWYD9bP9z5 :\n"
           "    oracle('i, 'j)\n"
           "against the expected type\n"
           "  bytes(32)">>,
         <<?Pos(14, 5)
           "Cannot unify oracle('k, 'l)\n"
           "         and oracle_query(int, bool)\n"
           "when checking the type of the expression at line 14, column 5\n"
           "  ok_2YNyxd6TRJPNrTcEDCe9ra59SVUdp9FR9qWC5msKZWYD9bP9z5 :\n"
           "    oracle('k, 'l)\n"
           "against the expected type\n"
           "  oracle_query(int, bool)">>,
         <<?Pos(11, 5)
           "Cannot unify address\n"
           "         and oracle(int, bool)\n"
           "when checking the type of the expression at line 11, column 5\n"
           "  ak_2gx9MEFxKvY9vMG5YnqnXWv1hCsX7rgnfvBLJS4aQurustR1rt : address\n"
           "against the expected type\n"
           "  oracle(int, bool)">>,
         <<?Pos(9, 5)
           "Cannot unify address\n"
           "         and Remote\n"
           "when checking the type of the expression at line 9, column 5\n"
           "  ak_2gx9MEFxKvY9vMG5YnqnXWv1hCsX7rgnfvBLJS4aQurustR1rt : address\n"
           "against the expected type\n"
           "  Remote">>,
         <<?Pos(7, 5)
           "Cannot unify address\n"
           "         and bytes(32)\n"
           "when checking the type of the expression at line 7, column 5\n"
           "  ak_2gx9MEFxKvY9vMG5YnqnXWv1hCsX7rgnfvBLJS4aQurustR1rt : address\n"
           "against the expected type\n"
           "  bytes(32)">>])
    , ?TEST(stateful,
       [<<?Pos(13, 35)
          "Cannot reference stateful function Chain.spend (at line 13, column 35)\nin the definition of non-stateful function fail1.">>,
        <<?Pos(14, 35)
          "Cannot reference stateful function local_spend (at line 14, column 35)\nin the definition of non-stateful function fail2.">>,
        <<?Pos(16, 15)
          "Cannot reference stateful function Chain.spend (at line 16, column 15)\nin the definition of non-stateful function fail3.">>,
        <<?Pos(20, 31)
          "Cannot reference stateful function Chain.spend (at line 20, column 31)\nin the definition of non-stateful function fail4.">>,
        <<?Pos(35, 47)
          "Cannot reference stateful function Chain.spend (at line 35, column 47)\nin the definition of non-stateful function fail5.">>,
        <<?Pos(48, 57)
          "Cannot pass non-zero value argument 1000 (at line 48, column 57)\nin the definition of non-stateful function fail6.">>,
        <<?Pos(49, 56)
          "Cannot pass non-zero value argument 1000 (at line 49, column 56)\nin the definition of non-stateful function fail7.">>,
        <<?Pos(52, 17)
          "Cannot pass non-zero value argument 1000 (at line 52, column 17)\nin the definition of non-stateful function fail8.">>])
    , ?TEST(bad_init_state_access,
       [<<?Pos(11, 5)
          "The init function should return the initial state as its result and cannot write the state,\n"
          "but it calls\n"
          "  - set_state (at line 11, column 5), which calls\n"
          "  - roundabout (at line 8, column 38), which calls\n"
          "  - put (at line 7, column 39)">>,
        <<?Pos(12, 5)
          "The init function should return the initial state as its result and cannot read the state,\n"
          "but it calls\n"
          "  - new_state (at line 12, column 5), which calls\n"
          "  - state (at line 5, column 29)">>,
        <<?Pos(13, 13)
          "The init function should return the initial state as its result and cannot read the state,\n"
          "but it calls\n"
          "  - state (at line 13, column 13)">>])
    , ?TEST(modifier_checks,
       [<<?Pos(11, 3)
          "The function all_the_things (at line 11, column 3) cannot be both public and private.">>,
        <<?Pos(3, 3)
          "Namespaces cannot contain entrypoints (at line 3, column 3). Use 'function' instead.">>,
        <<?Pos(5, 10)
          "The contract Remote (at line 5, column 10) has no entrypoints. Since Sophia version 3.2, public\ncontract functions must be declared with the 'entrypoint' keyword instead of\n'function'.">>,
        <<?Pos(12, 3)
          "The entrypoint wha (at line 12, column 3) cannot be private. Use 'function' instead.">>,
        <<?Pos(6, 3)
          "Use 'entrypoint' for declaration of foo (at line 6, column 3):\n  entrypoint foo : () => unit">>,
        <<?Pos(10, 3)
          "Use 'entrypoint' instead of 'function' for public function foo (at line 10, column 3):\n  entrypoint foo() = ()">>,
        <<?Pos(6, 3)
          "Use 'entrypoint' instead of 'function' for public function foo (at line 6, column 3):\n  entrypoint foo : () => unit">>])
    , ?TEST(list_comp_not_a_list,
      [<<?Pos(2, 36)
         "Cannot unify int\n         and list('a)\nwhen checking rvalue of list comprehension binding at line 2, column 36\n  1 : int\nagainst type \n  list('a)">>
      ])
    , ?TEST(list_comp_if_not_bool,
      [<<?Pos(2, 44)
         "Cannot unify int\n         and bool\nwhen checking the type of the expression at line 2, column 44\n  3 : int\nagainst the expected type\n  bool">>
      ])
    , ?TEST(list_comp_bad_shadow,
      [<<?Pos(2, 53)
         "Cannot unify int\n         and string\nwhen checking the type of the pattern at line 2, column 53\n  x : int\nagainst the expected type\n  string">>
      ])
    , ?TEST(map_as_map_key,
       [<<?Pos(5, 25)
         "Invalid key type\n"
         "  map(int, int)\n"
         "Map keys cannot contain other maps.">>,
        <<?Pos(6, 25)
         "Invalid key type\n"
         "  lm\n"
         "Map keys cannot contain other maps.">>])
    , ?TEST(calling_init_function,
       [<<?Pos(7, 28)
          "The 'init' function is called exclusively by the create contract transaction\n"
          "and cannot be called from the contract code.">>])
    , ?TEST(bad_top_level_decl,
        [<<?Pos(1, 1) "The definition of 'square' must appear inside a contract or namespace.">>])
    ].

-define(Path(File), "code_errors/" ??File).
-define(Msg(File, Line, Col, Err), <<?Pos(?Path(File), Line, Col) Err>>).

-define(SAME(File, Line, Col, Err), {?Path(File), ?Msg(File, Line, Col, Err)}).
-define(AEVM(File, Line, Col, Err), {?Path(File), [{aevm, ?Msg(File, Line, Col, Err)}]}).
-define(FATE(File, Line, Col, Err), {?Path(File), [{fate, ?Msg(File, Line, Col, Err)}]}).
-define(BOTH(File, Line, Col, ErrAEVM, ErrFATE),
        {?Path(File), [{aevm, ?Msg(File, Line, Col, ErrAEVM)},
                       {fate, ?Msg(File, Line, Col, ErrFATE)}]}).

failing_code_gen_contracts() ->
    [ ?SAME(last_declaration_must_be_contract, 1, 1,
            "Expected a contract as the last declaration instead of the namespace 'LastDeclarationIsNotAContract'")
    , ?SAME(missing_definition, 2, 14,
            "Missing definition of function 'foo'.")
    , ?AEVM(polymorphic_entrypoint, 2, 17,
            "The argument\n"
            "  x : 'a\n"
            "of entrypoint 'id' has a polymorphic (contains type variables) type.\n"
            "Use the FATE backend if you want polymorphic entrypoints.")
    , ?AEVM(polymorphic_entrypoint_return, 2, 3,
            "The return type\n"
            "  'a\n"
            "of entrypoint 'fail' is polymorphic (contains type variables).\n"
            "Use the FATE backend if you want polymorphic entrypoints.")
    , ?SAME(higher_order_entrypoint, 2, 20,
            "The argument\n"
            "  f : (int) => int\n"
            "of entrypoint 'apply' has a higher-order (contains function types) type.")
    , ?SAME(higher_order_entrypoint_return, 2, 3,
            "The return type\n"
            "  (int) => int\n"
            "of entrypoint 'add' is higher-order (contains function types).")
    , ?SAME(missing_init_function, 1, 10,
            "Missing init function for the contract 'MissingInitFunction'.\n"
            "The 'init' function can only be omitted if the state type is 'unit'.")
    , ?SAME(parameterised_state, 3, 8,
            "The state type cannot be parameterized.")
    , ?SAME(parameterised_event, 3, 12,
            "The event type cannot be parameterized.")
    , ?SAME(polymorphic_aens_resolve, 4, 5,
            "Invalid return type of AENS.resolve:\n"
            "  'a\n"
            "It must be a string or a pubkey type (address, oracle, etc).")
    , ?SAME(bad_aens_resolve, 6, 5,
            "Invalid return type of AENS.resolve:\n"
            "  list(int)\n"
            "It must be a string or a pubkey type (address, oracle, etc).")
    , ?AEVM(polymorphic_compare, 4, 5,
            "Cannot compare values of type\n"
            "  'a\n"
            "The AEVM only supports '==' on values of\n"
            "- word type (int, bool, bits, address, oracle(_, _), etc)\n"
            "- type string\n"
            "- tuple or record of word type\n"
            "Use FATE if you need to compare arbitrary types.")
    , ?AEVM(complex_compare, 4, 5,
            "Cannot compare values of type\n"
            "  (string * int)\n"
            "The AEVM only supports '!=' on values of\n"
            "- word type (int, bool, bits, address, oracle(_, _), etc)\n"
            "- type string\n"
            "- tuple or record of word type\n"
            "Use FATE if you need to compare arbitrary types.")
    , ?AEVM(complex_compare_leq, 4, 5,
            "Cannot compare values of type\n"
            "  (int * int)\n"
            "The AEVM only supports '=<' on values of\n"
            "- word type (int, bool, bits, address, oracle(_, _), etc)\n"
            "Use FATE if you need to compare arbitrary types.")
    , ?AEVM(higher_order_compare, 4, 5,
            "Cannot compare values of type\n"
            "  (int) => int\n"
            "The AEVM only supports '<' on values of\n"
            "- word type (int, bool, bits, address, oracle(_, _), etc)\n"
            "Use FATE if you need to compare arbitrary types.")
    , ?AEVM(unapplied_contract_call, 6, 19,
            "The AEVM does not support unapplied contract call to\n"
            "  r : Remote\n"
            "Use FATE if you need this.")
    , ?AEVM(polymorphic_map_keys, 4, 34,
            "Invalid map key type\n"
            "  'a\n"
            "Map keys cannot be polymorphic in the AEVM. Use FATE if you need this.")
    , ?AEVM(higher_order_map_keys, 4, 42,
            "Invalid map key type\n"
            "  (int) => int\n"
            "Map keys cannot be higher-order.")
    , ?SAME(polymorphic_query_type, 3, 5,
            "Invalid oracle type\n"
            "  oracle('a, 'b)\n"
            "The query type must not be polymorphic (contain type variables).")
    , ?SAME(polymorphic_response_type, 3, 5,
            "Invalid oracle type\n"
            "  oracle(string, 'r)\n"
            "The response type must not be polymorphic (contain type variables).")
    , ?SAME(higher_order_query_type, 3, 5,
            "Invalid oracle type\n"
            "  oracle((int) => int, string)\n"
            "The query type must not be higher-order (contain function types).")
    , ?SAME(higher_order_response_type, 3, 5,
            "Invalid oracle type\n"
            "  oracle(string, (int) => int)\n"
            "The response type must not be higher-order (contain function types).")
    ].

