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
            case compile(aevm, ContractName) of
                <<"Type errors\n", ErrorString/binary>> ->
                    check_errors(lists:sort(ExpectedErrors), ErrorString);
                <<"Parse errors\n", ErrorString/binary>> ->
                    check_errors(lists:sort(ExpectedErrors), ErrorString)
            end
        end} ||
            {ContractName, ExpectedErrors} <- failing_contracts() ] ++
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
     [ {"Testing deadcode elimination",
        fun() ->
            #{ byte_code := NoDeadCode } = compile(aevm, "nodeadcode"),
            #{ byte_code := DeadCode   } = compile(aevm, "deadcode"),
            SizeNoDeadCode = byte_size(NoDeadCode),
            SizeDeadCode   = byte_size(DeadCode),
            ?assertMatch({_, _, true}, {SizeDeadCode, SizeNoDeadCode, SizeDeadCode + 40 < SizeNoDeadCode}),
            ok
        end} ].

check_errors(Expect, ErrorString) ->
    %% This removes the final single \n as well.
    Actual = binary:split(<<ErrorString/binary,$\n>>, <<"\n\n">>, [global,trim]),
    case {Expect -- Actual, Actual -- Expect} of
        {[], Extra}   -> ?assertMatch({unexpected, []}, {unexpected, Extra});
        {Missing, []} -> ?assertMatch({missing, []}, {missing, Missing});
        {Missing, Extra} -> ?assertEqual(Missing, Extra)
    end.

compile(Backend, Name) ->
    compile(Backend, Name,
            [{include, {file_system, [aeso_test_utils:contract_path()]}}]
            ++ [no_implicit_stdlib || not wants_stdlib(Name)]).

compile(Backend, Name, Options) ->
    String = aeso_test_utils:read_contract(Name),
    case aeso_compiler:from_string(String, [{src_file, Name}, {backend, Backend} | Options]) of
        {ok, Map}            -> Map;
        {error, ErrorString} -> ErrorString
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
     "list_comp"
    ].

not_yet_compilable(fate) -> [];
not_yet_compilable(aevm) -> [].

%% Contracts that should produce type errors

failing_contracts() ->
    [ {"name_clash",
       [<<"Duplicate definitions of abort at\n"
          "  - (builtin location)\n"
          "  - line 14, column 3">>,
        <<"Duplicate definitions of require at\n"
          "  - (builtin location)\n"
          "  - line 15, column 3">>,
        <<"Duplicate definitions of double_def at\n"
          "  - line 10, column 3\n"
          "  - line 11, column 3">>,
        <<"Duplicate definitions of double_proto at\n"
          "  - line 4, column 3\n"
          "  - line 5, column 3">>,
        <<"Duplicate definitions of proto_and_def at\n"
          "  - line 7, column 3\n"
          "  - line 8, column 3">>,
        <<"Duplicate definitions of put at\n"
          "  - (builtin location)\n"
          "  - line 16, column 3">>,
        <<"Duplicate definitions of state at\n"
          "  - (builtin location)\n"
          "  - line 17, column 3">>]}
    , {"type_errors",
       [<<"Unbound variable zz at line 17, column 23">>,
        <<"Cannot unify int\n"
          "         and list(int)\n"
          "when checking the application at line 26, column 9 of\n"
          "  (::) : (int, list(int)) => list(int)\n"
          "to arguments\n"
          "  x : int\n"
          "  x : int">>,
        <<"Cannot unify string\n"
          "         and int\n"
          "when checking the assignment of the field\n"
          "  x : map(string, string) (at line 9, column 48)\n"
          "to the old value __x and the new value\n"
          "  __x {[\"foo\"] @ x = x + 1} : map(string, int)">>,
        <<"Cannot unify int\n"
          "         and string\n"
          "when checking the type of the expression at line 34, column 47\n"
          "  1 : int\n"
          "against the expected type\n"
          "  string">>,
        <<"Cannot unify string\n"
          "         and int\n"
          "when checking the type of the expression at line 34, column 52\n"
          "  \"bla\" : string\n"
          "against the expected type\n"
          "  int">>,
        <<"Cannot unify string\n"
          "         and int\n"
          "when checking the type of the expression at line 32, column 18\n"
          "  \"x\" : string\n"
          "against the expected type\n"
          "  int">>,
        <<"Cannot unify string\n"
          "         and int\n"
          "when checking the type of the expression at line 11, column 58\n"
          "  \"foo\" : string\n"
          "against the expected type\n"
          "  int">>,
        <<"Cannot unify int\n"
          "         and string\n"
          "when comparing the types of the if-branches\n"
          "  - w : int (at line 38, column 13)\n"
          "  - z : string (at line 39, column 10)">>,
        <<"Not a record type: string\n"
          "arising from the projection of the field y (at line 22, column 40)">>,
        <<"Not a record type: string\n"
          "arising from an assignment of the field y (at line 21, column 44)">>,
        <<"Not a record type: string\n"
          "arising from an assignment of the field y (at line 20, column 40)">>,
        <<"Not a record type: string\n"
          "arising from an assignment of the field y (at line 19, column 37)">>,
        <<"Ambiguous record type with field y (at line 13, column 27) could be one of\n"
          "  - r (at line 4, column 10)\n"
          "  - r' (at line 5, column 10)">>,
        <<"Repeated name x in pattern\n"
          "  x :: x (at line 26, column 7)">>,
        <<"Repeated argument x to function repeated_arg (at line 44, column 14).">>,
        <<"Repeated argument y to function repeated_arg (at line 44, column 14).">>,
        <<"No record type with fields y, z (at line 14, column 24)">>,
        <<"The field z is missing when constructing an element of type r2 (at line 15, column 26)">>,
        <<"Record type r2 does not have field y (at line 15, column 24)">>,
        <<"Let binding at line 47, column 5 must be followed by an expression">>,
        <<"Let binding at line 50, column 5 must be followed by an expression">>,
        <<"Let binding at line 54, column 5 must be followed by an expression">>,
        <<"Let binding at line 58, column 5 must be followed by an expression">>]}
    , {"init_type_error",
       [<<"Cannot unify string\n"
          "         and map(int, int)\n"
          "when checking that 'init' returns a value of type 'state' at line 7, column 3">>]}
    , {"missing_state_type",
       [<<"Cannot unify string\n"
          "         and unit\n"
          "when checking that 'init' returns a value of type 'state' at line 5, column 3">>]}
    , {"missing_fields_in_record_expression",
       [<<"The field x is missing when constructing an element of type r('a) (at line 7, column 42)">>,
        <<"The field y is missing when constructing an element of type r(int) (at line 8, column 42)">>,
        <<"The fields y, z are missing when constructing an element of type r('a) (at line 6, column 42)">>]}
    , {"namespace_clash",
       [<<"The contract Call (at line 4, column 10) has the same name as a namespace at (builtin location)">>]}
    , {"bad_events",
        [<<"The indexed type string (at line 9, column 25) is not a word type">>,
         <<"The indexed type alias_string (at line 10, column 25) equals string which is not a word type">>]}
    , {"bad_events2",
        [<<"The event constructor BadEvent1 (at line 9, column 7) has too many non-indexed values (max 1)">>,
         <<"The event constructor BadEvent2 (at line 10, column 7) has too many indexed values (max 3)">>]}
    , {"type_clash",
        [<<"Cannot unify int\n"
           "         and string\n"
           "when checking the record projection at line 12, column 42\n"
           "  r.foo : (gas : int, value : int) => Remote.themap\n"
           "against the expected type\n"
           "  (gas : int, value : int) => map(string, int)">>]}
    , {"bad_include_and_ns",
        [<<"Include of 'included.aes' at line 2, column 11\nnot allowed, include only allowed at top level.">>,
         <<"Nested namespace not allowed\nNamespace 'Foo' at line 3, column 13 not defined at top level.">>]}
    , {"bad_address_literals",
        [<<"The type bytes(32) is not a contract type\n"
           "when checking that the contract literal at line 32, column 5\n"
           "  ct_Ez6MyeTMm17YnTnDdHTSrzMEBKmy7Uz2sXu347bTDPgVH2ifJ\n"
           "has the type\n"
           "  bytes(32)">>,
         <<"The type oracle(int, bool) is not a contract type\n"
           "when checking that the contract literal at line 30, column 5\n"
           "  ct_Ez6MyeTMm17YnTnDdHTSrzMEBKmy7Uz2sXu347bTDPgVH2ifJ\n"
           "has the type\n"
           "  oracle(int, bool)">>,
         <<"The type address is not a contract type\n"
           "when checking that the contract literal at line 28, column 5\n"
           "  ct_Ez6MyeTMm17YnTnDdHTSrzMEBKmy7Uz2sXu347bTDPgVH2ifJ\n"
           "has the type\n"
           "  address">>,
         <<"Cannot unify oracle_query('a, 'b)\n"
           "         and Remote\n"
           "when checking the type of the expression at line 25, column 5\n"
           "  oq_2oRvyowJuJnEkxy58Ckkw77XfWJrmRgmGaLzhdqb67SKEL1gPY :\n"
           "    oracle_query('a, 'b)\n"
           "against the expected type\n"
           "  Remote">>,
         <<"Cannot unify oracle_query('c, 'd)\n"
           "         and bytes(32)\n"
           "when checking the type of the expression at line 23, column 5\n"
           "  oq_2oRvyowJuJnEkxy58Ckkw77XfWJrmRgmGaLzhdqb67SKEL1gPY :\n"
           "    oracle_query('c, 'd)\n"
           "against the expected type\n"
           "  bytes(32)">>,
         <<"Cannot unify oracle_query('e, 'f)\n"
           "         and oracle(int, bool)\n"
           "when checking the type of the expression at line 21, column 5\n"
           "  oq_2oRvyowJuJnEkxy58Ckkw77XfWJrmRgmGaLzhdqb67SKEL1gPY :\n"
           "    oracle_query('e, 'f)\n"
           "against the expected type\n"
           "  oracle(int, bool)">>,
         <<"Cannot unify oracle('g, 'h)\n"
           "         and Remote\n"
           "when checking the type of the expression at line 18, column 5\n"
           "  ok_2YNyxd6TRJPNrTcEDCe9ra59SVUdp9FR9qWC5msKZWYD9bP9z5 :\n"
           "    oracle('g, 'h)\n"
           "against the expected type\n"
           "  Remote">>,
         <<"Cannot unify oracle('i, 'j)\n"
           "         and bytes(32)\n"
           "when checking the type of the expression at line 16, column 5\n"
           "  ok_2YNyxd6TRJPNrTcEDCe9ra59SVUdp9FR9qWC5msKZWYD9bP9z5 :\n"
           "    oracle('i, 'j)\n"
           "against the expected type\n"
           "  bytes(32)">>,
         <<"Cannot unify oracle('k, 'l)\n"
           "         and oracle_query(int, bool)\n"
           "when checking the type of the expression at line 14, column 5\n"
           "  ok_2YNyxd6TRJPNrTcEDCe9ra59SVUdp9FR9qWC5msKZWYD9bP9z5 :\n"
           "    oracle('k, 'l)\n"
           "against the expected type\n"
           "  oracle_query(int, bool)">>,
         <<"Cannot unify address\n"
           "         and oracle(int, bool)\n"
           "when checking the type of the expression at line 11, column 5\n"
           "  ak_2gx9MEFxKvY9vMG5YnqnXWv1hCsX7rgnfvBLJS4aQurustR1rt : address\n"
           "against the expected type\n"
           "  oracle(int, bool)">>,
         <<"Cannot unify address\n"
           "         and Remote\n"
           "when checking the type of the expression at line 9, column 5\n"
           "  ak_2gx9MEFxKvY9vMG5YnqnXWv1hCsX7rgnfvBLJS4aQurustR1rt : address\n"
           "against the expected type\n"
           "  Remote">>,
         <<"Cannot unify address\n"
           "         and bytes(32)\n"
           "when checking the type of the expression at line 7, column 5\n"
           "  ak_2gx9MEFxKvY9vMG5YnqnXWv1hCsX7rgnfvBLJS4aQurustR1rt : address\n"
           "against the expected type\n"
           "  bytes(32)">>]}
    , {"stateful",
       [<<"Cannot reference stateful function Chain.spend (at line 13, column 35)\nin the definition of non-stateful function fail1.">>,
        <<"Cannot reference stateful function local_spend (at line 14, column 35)\nin the definition of non-stateful function fail2.">>,
        <<"Cannot reference stateful function Chain.spend (at line 16, column 15)\nin the definition of non-stateful function fail3.">>,
        <<"Cannot reference stateful function Chain.spend (at line 20, column 31)\nin the definition of non-stateful function fail4.">>,
        <<"Cannot reference stateful function Chain.spend (at line 35, column 47)\nin the definition of non-stateful function fail5.">>,
        <<"Cannot pass non-zero value argument 1000 (at line 48, column 57)\nin the definition of non-stateful function fail6.">>,
        <<"Cannot pass non-zero value argument 1000 (at line 49, column 56)\nin the definition of non-stateful function fail7.">>,
        <<"Cannot pass non-zero value argument 1000 (at line 52, column 17)\nin the definition of non-stateful function fail8.">>]}
    , {"bad_init_state_access",
       [<<"The init function should return the initial state as its result and cannot write the state,\n"
          "but it calls\n"
          "  - set_state (at line 11, column 5), which calls\n"
          "  - roundabout (at line 8, column 38), which calls\n"
          "  - put (at line 7, column 39)">>,
        <<"The init function should return the initial state as its result and cannot read the state,\n"
          "but it calls\n"
          "  - new_state (at line 12, column 5), which calls\n"
          "  - state (at line 5, column 29)">>,
        <<"The init function should return the initial state as its result and cannot read the state,\n"
          "but it calls\n"
          "  - state (at line 13, column 13)">>]}
    , {"field_parse_error",
       [<<"line 6, column 1: In field_parse_error at 5:26:\n"
          "Cannot use nested fields or keys in record construction: p.x\n">>]}
    , {"modifier_checks",
       [<<"The function all_the_things (at line 11, column 3) cannot be both public and private.">>,
        <<"Namespaces cannot contain entrypoints (at line 3, column 3). Use 'function' instead.">>,
        <<"The contract Remote (at line 5, column 10) has no entrypoints. Since Sophia version 3.2, public\ncontract functions must be declared with the 'entrypoint' keyword instead of\n'function'.">>,
        <<"The entrypoint wha (at line 12, column 3) cannot be private. Use 'function' instead.">>,
        <<"Use 'entrypoint' for declaration of foo (at line 6, column 3):\n  entrypoint foo : () => unit">>,
        <<"Use 'entrypoint' instead of 'function' for public function foo (at line 10, column 3):\n  entrypoint foo() = ()">>,
        <<"Use 'entrypoint' instead of 'function' for public function foo (at line 6, column 3):\n  entrypoint foo : () => unit">>]}
    , {"list_comp_not_a_list",
      [<<"Cannot unify int\n         and list('a)\nwhen checking rvalue of list comprehension binding at line 2, column 36\n  1 : int\nagainst type \n  list('a)">>
      ]}
    , {"list_comp_if_not_bool",
      [<<"Cannot unify int\n         and bool\nwhen checking the type of the expression at line 2, column 44\n  3 : int\nagainst the expected type\n  bool">>
      ]}
    , {"list_comp_bad_shadow",
      [<<"Cannot unify int\n         and string\nwhen checking the type of the pattern at line 2, column 53\n  x : int\nagainst the expected type\n  string">>
      ]}
    ].

wants_stdlib(Name) ->
    lists:member
      (Name,
       [ "stdlib_include",
         "list_comp",
         "list_comp_not_a_list",
         "list_comp_if_not_bool",
         "list_comp_bad_shadow"
       ]).
