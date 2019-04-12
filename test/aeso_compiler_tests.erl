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
     [ {"Testing the " ++ ContractName ++ " contract",
        fun() ->
            case compile(ContractName) of
                #{byte_code := ByteCode,
                  contract_source := _,
                  type_info := _} -> ?assertMatch(Code when is_binary(Code), ByteCode);
                ErrBin ->
                    io:format("\n~s", [ErrBin]),
                    error(ErrBin)
            end
        end} || ContractName <- compilable_contracts() ] ++
     [ {"Testing error messages of " ++ ContractName,
        fun() ->
            case compile(ContractName) of
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

compile(Name) ->
    compile(Name, [{include, {file_system, [aeso_test_utils:contract_path()]}}]).

compile(Name, Options) ->
    String = aeso_test_utils:read_contract(Name),
    case aeso_compiler:from_string(String, [{src_file, Name} | Options]) of
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
     "address_literals"
    ].

%% Contracts that should produce type errors

failing_contracts() ->
    [ {"name_clash",
       [<<"Duplicate definitions of abort at\n"
          "  - (builtin location)\n"
          "  - line 14, column 3">>,
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
          "  - line 15, column 3">>,
        <<"Duplicate definitions of state at\n"
          "  - (builtin location)\n"
          "  - line 16, column 3">>]}
    , {"type_errors",
       [<<"Unbound variable zz at line 17, column 21">>,
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
          "  x : map(string, string) (at line 9, column 46)\n"
          "to the old value __x and the new value\n"
          "  __x {[\"foo\"] @ x = x + 1} : map(string, int)">>,
        <<"Cannot unify int\n"
          "         and string\n"
          "when checking the type of the expression at line 34, column 45\n"
          "  1 : int\n"
          "against the expected type\n"
          "  string">>,
        <<"Cannot unify string\n"
          "         and int\n"
          "when checking the type of the expression at line 34, column 50\n"
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
          "when checking the type of the expression at line 11, column 56\n"
          "  \"foo\" : string\n"
          "against the expected type\n"
          "  int">>,
        <<"Cannot unify int\n"
          "         and string\n"
          "when comparing the types of the if-branches\n"
          "  - w : int (at line 38, column 13)\n"
          "  - z : string (at line 39, column 10)">>,
        <<"Not a record type: string\n"
          "arising from the projection of the field y (at line 22, column 38)">>,
        <<"Not a record type: string\n"
          "arising from an assignment of the field y (at line 21, column 42)">>,
        <<"Not a record type: string\n"
          "arising from an assignment of the field y (at line 20, column 38)">>,
        <<"Not a record type: string\n"
          "arising from an assignment of the field y (at line 19, column 35)">>,
        <<"Ambiguous record type with field y (at line 13, column 25) could be one of\n"
          "  - r (at line 4, column 10)\n"
          "  - r' (at line 5, column 10)">>,
        <<"Repeated name x in pattern\n"
          "  x :: x (at line 26, column 7)">>,
        <<"No record type with fields y, z (at line 14, column 22)">>,
        <<"The field z is missing when constructing an element of type r2 (at line 15, column 24)">>,
        <<"Record type r2 does not have field y (at line 15, column 22)">>]}
    , {"init_type_error",
       [<<"Cannot unify string\n"
          "         and map(int, int)\n"
          "when checking that 'init' returns a value of type 'state' at line 7, column 3">>]}
    , {"missing_state_type",
       [<<"Cannot unify string\n"
          "         and ()\n"
          "when checking that 'init' returns a value of type 'state' at line 5, column 3">>]}
    , {"missing_fields_in_record_expression",
       [<<"The field x is missing when constructing an element of type r('a) (at line 7, column 40)">>,
        <<"The field y is missing when constructing an element of type r(int) (at line 8, column 40)">>,
        <<"The fields y, z are missing when constructing an element of type r('1) (at line 6, column 40)">>]}
    , {"namespace_clash",
       [<<"The contract Call (at line 4, column 10) has the same name as a namespace at (builtin location)">>]}
    , {"bad_events",
        [<<"The payload type int (at line 10, column 30) should be string">>,
         <<"The payload type alias_address (at line 12, column 30) equals address but it should be string">>,
         <<"The indexed type string (at line 9, column 25) is not a word type">>,
         <<"The indexed type alias_string (at line 11, column 25) equals string which is not a word type">>]}
    , {"bad_events2",
        [<<"The event constructor BadEvent1 (at line 9, column 7) has too many non-indexed values (max 1)">>,
         <<"The event constructor BadEvent2 (at line 10, column 7) has too many indexed values (max 3)">>,
         <<"The event constructor BadEvent3 (at line 11, column 7) has too many non-indexed values (max 1)">>,
         <<"The payload type address (at line 11, column 17) should be string">>,
         <<"The payload type int (at line 11, column 26) should be string">>]}
    , {"type_clash",
        [<<"Cannot unify int\n"
           "         and string\n"
           "when checking the record projection at line 12, column 40\n"
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
         <<"Cannot unify oracle_query('1, '2)\n"
           "         and Remote\n"
           "when checking the type of the expression at line 25, column 5\n"
           "  oq_2oRvyowJuJnEkxy58Ckkw77XfWJrmRgmGaLzhdqb67SKEL1gPY :\n"
           "    oracle_query('1, '2)\n"
           "against the expected type\n"
           "  Remote">>,
         <<"Cannot unify oracle_query('3, '4)\n"
           "         and bytes(32)\n"
           "when checking the type of the expression at line 23, column 5\n"
           "  oq_2oRvyowJuJnEkxy58Ckkw77XfWJrmRgmGaLzhdqb67SKEL1gPY :\n"
           "    oracle_query('3, '4)\n"
           "against the expected type\n"
           "  bytes(32)">>,
         <<"Cannot unify oracle_query('5, '6)\n"
           "         and oracle(int, bool)\n"
           "when checking the type of the expression at line 21, column 5\n"
           "  oq_2oRvyowJuJnEkxy58Ckkw77XfWJrmRgmGaLzhdqb67SKEL1gPY :\n"
           "    oracle_query('5, '6)\n"
           "against the expected type\n"
           "  oracle(int, bool)">>,
         <<"Cannot unify oracle('7, '8)\n"
           "         and Remote\n"
           "when checking the type of the expression at line 18, column 5\n"
           "  ok_2YNyxd6TRJPNrTcEDCe9ra59SVUdp9FR9qWC5msKZWYD9bP9z5 :\n"
           "    oracle('7, '8)\n"
           "against the expected type\n"
           "  Remote">>,
         <<"Cannot unify oracle('9, '10)\n"
           "         and bytes(32)\n"
           "when checking the type of the expression at line 16, column 5\n"
           "  ok_2YNyxd6TRJPNrTcEDCe9ra59SVUdp9FR9qWC5msKZWYD9bP9z5 :\n"
           "    oracle('9, '10)\n"
           "against the expected type\n"
           "  bytes(32)">>,
         <<"Cannot unify oracle('11, '12)\n"
           "         and oracle_query(int, bool)\n"
           "when checking the type of the expression at line 14, column 5\n"
           "  ok_2YNyxd6TRJPNrTcEDCe9ra59SVUdp9FR9qWC5msKZWYD9bP9z5 :\n"
           "    oracle('11, '12)\n"
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
    ].
