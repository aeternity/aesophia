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
               Error -> io:format("\n\n~p\n\n", [Error]), print_and_throw(Error)
           end
       end} || ContractName <- compilable_contracts(), Backend <- [aevm, fate],
               not lists:member(ContractName, not_compilable_on(Backend))] ++
    [ {"Test file not found error",
       fun() ->
           {error, Errors} = aeso_compiler:file("does_not_exist.aes"),
           ExpErr = <<"File error:\ndoes_not_exist.aes: no such file or directory">>,
           check_errors([ExpErr], Errors)
       end} ] ++
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

%% Check if all modules in the standard library compile
stdlib_test_() ->
    {ok, Files} = file:list_dir(aeso_stdlib:stdlib_include_path()),
    [ { "Testing " ++ File ++ " from the stdlib",
      fun() ->
          String = "include \"" ++ File ++ "\"\nmain contract Test =\n  entrypoint f(x) = x",
          Options = [{src_file, File}, {backend, fate}],
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

compile(Backend, Name) ->
    compile(Backend, Name,
            [{include, {file_system, [aeso_test_utils:contract_path()]}}]).

compile(Backend, Name, Options) ->
    String = aeso_test_utils:read_contract(Name),
    Options1 =
        case lists:member(Name, debug_mode_contracts()) of
            true  -> [debug_mode];
            false -> []
        end ++
        [ {src_file, Name ++ ".aes"}, {backend, Backend}
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
     "test" % Custom general-purpose test file. Keep it last on the list.
    ].

not_compilable_on(fate) -> [];
not_compilable_on(aevm) -> compilable_contracts().

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

    %% Type errors
    , ?TYPE_ERROR(name_clash,
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
    , ?TYPE_ERROR(type_errors,
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
          "Repeated names x, y in pattern\n"
          "  (x : int, y, x : string, y : bool) (at line 44, column 14)">>,
        <<?Pos(44, 39)
          "Cannot unify int\n"
          "         and string\n"
          "when checking the type of the expression at line 44, column 39\n"
          "  x : int\n"
          "against the expected type\n"
          "  string">>,
        <<?Pos(44, 72)
          "Cannot unify int\n"
          "         and string\n"
          "when checking the type of the expression at line 44, column 72\n"
          "  x : int\n"
          "against the expected type\n"
          "  string">>,
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
          "Let binding at line 58, column 5 must be followed by an expression">>,
        <<?Pos(63, 5)
          "Cannot unify int\n"
          "         and bool\n"
          "when checking the type of the expression at line 63, column 5\n"
          "  id(n) : int\n"
          "against the expected type\n"
          "  bool">>])
    , ?TYPE_ERROR(init_type_error,
       [<<?Pos(7, 3)
          "Cannot unify string\n"
          "         and map(int, int)\n"
          "when checking that 'init' returns a value of type 'state' at line 7, column 3">>])
    , ?TYPE_ERROR(missing_state_type,
       [<<?Pos(5, 3)
          "Cannot unify string\n"
          "         and unit\n"
          "when checking that 'init' returns a value of type 'state' at line 5, column 3">>])
    , ?TYPE_ERROR(missing_fields_in_record_expression,
       [<<?Pos(7, 42)
          "The field x is missing when constructing an element of type r('a) (at line 7, column 42)">>,
        <<?Pos(8, 42)
          "The field y is missing when constructing an element of type r(int) (at line 8, column 42)">>,
        <<?Pos(6, 42)
          "The fields y, z are missing when constructing an element of type r('a) (at line 6, column 42)">>])
    , ?TYPE_ERROR(namespace_clash,
       [<<?Pos(4, 10)
          "The contract Call (at line 4, column 10) has the same name as a namespace at (builtin location)">>])
    , ?TYPE_ERROR(bad_events,
        [<<?Pos(9, 25)
           "The indexed type string (at line 9, column 25) is not a word type">>,
         <<?Pos(10, 25)
           "The indexed type alias_string (at line 10, column 25) equals string which is not a word type">>])
    , ?TYPE_ERROR(bad_events2,
        [<<?Pos(9, 7)
           "The event constructor BadEvent1 (at line 9, column 7) has too many non-indexed values (max 1)">>,
         <<?Pos(10, 7)
           "The event constructor BadEvent2 (at line 10, column 7) has too many indexed values (max 3)">>])
    , ?TYPE_ERROR(type_clash,
        [<<?Pos(12, 42)
           "Cannot unify int\n"
           "         and string\n"
           "when checking the type of the expression at line 12, column 42\n"
           "  r.foo() : map(int, string)\n"
           "against the expected type\n"
           "  map(string, int)">>])
    , ?TYPE_ERROR(not_toplevel_include,
                  [<<?Pos(2, 11)
                     "Include of 'included.aes' at line 2, column 11\nnot allowed, include only allowed at top level.">>])
    , ?TYPE_ERROR(not_toplevel_namespace,
                  [<<?Pos(2, 13)
                     "Nested namespaces are not allowed\nNamespace 'Foo' at line 2, column 13 not defined at top level.">>])
    , ?TYPE_ERROR(not_toplevel_contract,
        [<<?Pos(2, 12)
           "Nested contracts are not allowed\nContract 'Con' at line 2, column 12 not defined at top level.">>])
    , ?TYPE_ERROR(bad_address_literals,
        [<<?Pos(11, 5)
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
           "  bytes(32)">>,
         <<?Pos(14, 5)
           "Cannot unify oracle('a, 'b)\n"
           "         and oracle_query(int, bool)\n"
           "when checking the type of the expression at line 14, column 5\n"
           "  ok_2YNyxd6TRJPNrTcEDCe9ra59SVUdp9FR9qWC5msKZWYD9bP9z5 :\n"
           "    oracle('a, 'b)\n"
           "against the expected type\n"
           "  oracle_query(int, bool)">>,
         <<?Pos(16, 5)
           "Cannot unify oracle('c, 'd)\n"
           "         and bytes(32)\n"
           "when checking the type of the expression at line 16, column 5\n"
           "  ok_2YNyxd6TRJPNrTcEDCe9ra59SVUdp9FR9qWC5msKZWYD9bP9z5 :\n"
           "    oracle('c, 'd)\n"
           "against the expected type\n"
           "  bytes(32)">>,
         <<?Pos(18, 5)
           "Cannot unify oracle('e, 'f)\n"
           "         and Remote\n"
           "when checking the type of the expression at line 18, column 5\n"
           "  ok_2YNyxd6TRJPNrTcEDCe9ra59SVUdp9FR9qWC5msKZWYD9bP9z5 :\n"
           "    oracle('e, 'f)\n"
           "against the expected type\n"
           "  Remote">>,
         <<?Pos(21, 5)
           "Cannot unify oracle_query('g, 'h)\n"
           "         and oracle(int, bool)\n"
           "when checking the type of the expression at line 21, column 5\n"
           "  oq_2oRvyowJuJnEkxy58Ckkw77XfWJrmRgmGaLzhdqb67SKEL1gPY :\n"
           "    oracle_query('g, 'h)\n"
           "against the expected type\n"
           "  oracle(int, bool)">>,
         <<?Pos(23, 5)
           "Cannot unify oracle_query('i, 'j)\n"
           "         and bytes(32)\n"
           "when checking the type of the expression at line 23, column 5\n"
           "  oq_2oRvyowJuJnEkxy58Ckkw77XfWJrmRgmGaLzhdqb67SKEL1gPY :\n"
           "    oracle_query('i, 'j)\n"
           "against the expected type\n"
           "  bytes(32)">>,
         <<?Pos(25, 5)
           "Cannot unify oracle_query('k, 'l)\n"
           "         and Remote\n"
           "when checking the type of the expression at line 25, column 5\n"
           "  oq_2oRvyowJuJnEkxy58Ckkw77XfWJrmRgmGaLzhdqb67SKEL1gPY :\n"
           "    oracle_query('k, 'l)\n"
           "against the expected type\n"
           "  Remote">>,
         <<?Pos(28, 5)
           "The type address is not a contract type\n"
           "when checking that the contract literal\n"
           "  ct_Ez6MyeTMm17YnTnDdHTSrzMEBKmy7Uz2sXu347bTDPgVH2ifJ\n"
           "has the type\n"
           "  address">>,
         <<?Pos(30, 5)
           "The type oracle(int, bool) is not a contract type\n"
           "when checking that the contract literal\n"
           "  ct_Ez6MyeTMm17YnTnDdHTSrzMEBKmy7Uz2sXu347bTDPgVH2ifJ\n"
           "has the type\n"
           "  oracle(int, bool)">>,
         <<?Pos(32, 5)
           "The type bytes(32) is not a contract type\n"
           "when checking that the contract literal\n"
           "  ct_Ez6MyeTMm17YnTnDdHTSrzMEBKmy7Uz2sXu347bTDPgVH2ifJ\n"
           "has the type\n"
           "  bytes(32)">>,
         <<?Pos(34, 5),
           "The type address is not a contract type\n"
           "when checking that the call to\n"
           "  Address.to_contract\n"
           "has the type\n"
           "  address">>])
    , ?TYPE_ERROR(stateful,
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
    , ?TYPE_ERROR(bad_init_state_access,
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
    , ?TYPE_ERROR(modifier_checks,
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
    , ?TYPE_ERROR(list_comp_not_a_list,
      [<<?Pos(2, 36)
         "Cannot unify int\n         and list('a)\nwhen checking rvalue of list comprehension binding at line 2, column 36\n  1 : int\nagainst type \n  list('a)">>
      ])
    , ?TYPE_ERROR(list_comp_if_not_bool,
      [<<?Pos(2, 44)
         "Cannot unify int\n         and bool\nwhen checking the type of the expression at line 2, column 44\n  3 : int\nagainst the expected type\n  bool">>
      ])
    , ?TYPE_ERROR(list_comp_bad_shadow,
      [<<?Pos(2, 53)
         "Cannot unify int\n         and string\nwhen checking the type of the pattern at line 2, column 53\n  x : int\nagainst the expected type\n  string">>
      ])
    , ?TYPE_ERROR(map_as_map_key,
       [<<?Pos(5, 47)
         "Invalid key type\n"
         "  map(int, int)\n"
         "Map keys cannot contain other maps.">>,
        <<?Pos(6, 31)
         "Invalid key type\n"
         "  list(map(int, int))\n"
         "Map keys cannot contain other maps.">>,
        <<?Pos(6, 31)
         "Invalid key type\n"
         "  lm\n"
         "Map keys cannot contain other maps.">>])
    , ?TYPE_ERROR(calling_init_function,
       [<<?Pos(7, 28)
          "The 'init' function is called exclusively by the create contract transaction\n"
          "and cannot be called from the contract code.">>])
    , ?TYPE_ERROR(bad_top_level_decl,
        [<<?Pos(1, 1) "The definition of 'square' must appear inside a contract or namespace.">>])
    , ?TYPE_ERROR(missing_event_type,
        [<<?Pos(3, 5)
           "Unbound variable Chain.event at line 3, column 5\n"
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
           "Cannot unify bytes(26)\n"
           "         and bytes(25)\n"
           "at line 15, column 5">>,
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
           "Cannot compile with this version of the compiler,\n"
           "because it does not satisfy the constraint ", Version/binary, " < 1.0">>,
         <<?Pos(2, 1)
           "Cannot compile with this version of the compiler,\n"
           "because it does not satisfy the constraint ", Version/binary, " == 9.9.9">>])
    , ?TYPE_ERROR(interface_with_defs,
         [<<?Pos(2, 3)
            "Contract interfaces cannot contain defined functions or entrypoints.\n"
            "Fix: replace the definition of 'foo' by a type signature.">>])
    , ?TYPE_ERROR(contract_as_namespace,
         [<<?Pos(5, 28)
            "Invalid call to contract entrypoint 'Foo.foo'.\n"
            "It must be called as 'c.foo' for some c : Foo.">>])
    , ?TYPE_ERROR(toplevel_let,
                  [<<?Pos(2, 7)
                     "Toplevel \"let\" definitions are not supported\n"
                     "Value this_is_illegal at line 2, column 7 could be replaced by 0-argument function">>])
    , ?TYPE_ERROR(empty_typedecl,
                  [<<?Pos(2, 8)
                     "Empty type declarations are not supported\n"
                     "Type t at line 2, column 8 lacks a definition">>])
    , ?TYPE_ERROR(higher_kinded_type,
                  [<<?Pos(2, 35)
                     "Type 'm is a higher kinded type variable\n"
                     "(takes another type as an argument)">>])
    , ?TYPE_ERROR(bad_arity,
                  [<<?Pos(3, 20)
                     "Arity for id doesn't match. Expected 1, got 0">>,
                   <<?Pos(3, 25)
                     "Cannot unify int\n"
                     "         and id\n"
                     "when checking the type of the expression at line 3, column 25\n"
                     "  123 : int\n"
                     "against the expected type\n"
                     "  id">>,
                   <<?Pos(4, 20)
                     "Arity for id doesn't match. Expected 1, got 2">>,
                   <<?Pos(4, 35)
                     "Cannot unify int\n"
                     "         and id(int, int)\n"
                     "when checking the type of the expression at line 4, column 35\n"
                     "  123 : int\n"
                     "against the expected type\n"
                     "  id(int, int)">>])
    , ?TYPE_ERROR(bad_unnamed_map_update_default,
                  [<<?Pos(4, 17)
                     "Invalid map update with default">>])
    , ?TYPE_ERROR(non_functional_entrypoint,
                  [<<?Pos(2, 14)
                     "f at line 2, column 14 was declared with an invalid type int.\n"
                     "Entrypoints and functions must have functional types">>])
    , ?TYPE_ERROR(bad_records,
        [<<?Pos(3, 16)
           "Mixed record fields and map keys in\n"
           "  {x = 0, [0] = 1}">>,
         <<?Pos(4, 6)
           "Mixed record fields and map keys in\n"
           "  r {x = 0, [0] = 1}">>,
         <<?Pos(5, 6)
           "Empty record/map update\n"
           "  r {}">>
        ])
    , ?TYPE_ERROR(bad_protected_call,
        [<<?Pos(6, 22)
           "Invalid 'protected' argument\n"
           "  (0 : int) == (1 : int) : bool\n"
           "It must be either 'true' or 'false'.">>
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
                     "Cannot unify () => unit\n"
                     "         and (int) => 'a\n",
                     "when checking the application at line 3, column 39 of\n"
                     "  f : () => unit\n"
                     "to arguments\n"
                     "  1 : int">>,
                   <<?Pos(4, 20)
                     "Cannot unify (int, string) => 'e\n"
                     "         and (int) => 'd\n"
                     "when checking the application at line 4, column 20 of\n"
                     "  g : (int, string) => 'e\n"
                     "to arguments\n"
                     "  1 : int">>,
                   <<?Pos(5, 20)
                     "Cannot unify (int, string) => 'c\n"
                     "         and (string) => 'b\n"
                     "when checking the application at line 5, column 20 of\n"
                     "  g : (int, string) => 'c\nto arguments\n"
                     "  \"Litwo, ojczyzno moja\" : string">>
                  ])
    , ?TYPE_ERROR(bad_state,
                  [<<?Pos(4, 16)
                     "Conflicting updates for field 'foo'">>])
    , ?TYPE_ERROR(factories_type_errors,
                  [<<?Pos(10,18)
                    "Chain.clone requires `ref` named argument of contract type.">>,
                   <<?Pos(11,18)
                     "Cannot unify (gas : int, value : int, protected : bool) => if(protected, option(void), void)\n         and (gas : int, value : int, protected : bool, int, bool) => 'b\n"
                     "when checking contract construction of type\n  (gas : int, value : int, protected : bool) =>\n    if(protected, option(void), void) (at line 11, column 18)\nagainst the expected type\n  (gas : int, value : int, protected : bool, int, bool) => 'b">>,
                   <<?Pos(12,37)
                     "Cannot unify int\n         and bool\n"
                     "when checking named argument\n  gas : int\nagainst inferred type\n  bool">>,
                   <<?Pos(13,18),
                     "Kaboom is not implemented.\n"
                     "when resolving arguments of variadic function\n  Chain.create">>,
                   <<?Pos(18,18)
                     "Cannot unify (gas : int, value : int, protected : bool, int, bool) => if(protected, option(void), void)\n         and (gas : int, value : int, protected : bool) => 'a\n"
                     "when checking contract construction of type\n  (gas : int, value : int, protected : bool, int, bool) =>\n    if(protected, option(void), void) (at line 18, column 18)\nagainst the expected type\n  (gas : int, value : int, protected : bool) => 'a">>,
                   <<?Pos(19,42),
                     "Named argument protected (at line 19, column 42) is not one of the expected named arguments\n  - value : int">>,
                   <<?Pos(20,42),
                     "Cannot unify int\n         and bool\n"
                     "when checking named argument\n  value : int\nagainst inferred type\n  bool">>
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
                  [ <<?Pos(2,3)
                      "Ambiguous name: Xa.f at line 2, column 3\nXb.f at line 5, column 3">>
                  , <<?Pos(13,23)
                      "Unbound variable A.f at line 13, column 23">>
                  ])
    ].

-define(Path(File), "code_errors/" ??File).
-define(Msg(File, Line, Col, Err), <<?Pos("Code generation", ?Path(File), Line, Col) Err>>).

-define(SAME(File, Line, Col, Err), {?Path(File), ?Msg(File, Line, Col, Err)}).
-define(AEVM(File, Line, Col, Err), {?Path(File), [{aevm, ?Msg(File, Line, Col, Err)}]}).
-define(FATE(File, Line, Col, Err), {?Path(File), [{fate, ?Msg(File, Line, Col, Err)}]}).
-define(BOTH(File, Line, Col, ErrAEVM, ErrFATE),
        {?Path(File), [{aevm, ?Msg(File, Line, Col, ErrAEVM)},
                       {fate, ?Msg(File, Line, Col, ErrFATE)}]}).

failing_code_gen_contracts() ->
    [ ?SAME(missing_definition, 2, 14,
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
    , ?AEVM(unapplied_named_arg_builtin, 4, 15,
            "The AEVM does not support unapplied use of Oracle.register.\n"
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
    , ?AEVM(higher_order_state, 3, 3,
            "Invalid state type\n"
            "  {f : (int) => int}\n"
            "The state cannot contain functions in the AEVM. Use FATE if you need this.")
    , ?FATE(child_with_decls, 2, 14,
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
    case compile(fate, Contract1) of
        ByteCode = #{ fate_code := FCode } ->
            FCode1   = aeb_fate_code:serialize(aeb_fate_code:strip_init_function(FCode)),
            Source   = aeso_test_utils:read_contract(Contract2),
            aeso_compiler:validate_byte_code(
              ByteCode#{ byte_code := FCode1 }, Source,
              case lists:member(Contract2, debug_mode_contracts()) of
                  true  -> [debug_mode];
                  false -> []
              end ++
                  [{backend, fate}, {include, {file_system, [aeso_test_utils:contract_path()]}}]);
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
