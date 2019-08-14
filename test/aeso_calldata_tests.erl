%%% -*- erlang-indent-level:4; indent-tabs-mode: nil -*-
%%%-------------------------------------------------------------------
%%% @copyright (C) 2019, Aeternity Anstalt
%%% @doc Test Sophia language compiler.
%%%
%%% @end
%%%-------------------------------------------------------------------

-module(aeso_calldata_tests).

-compile([export_all, nowarn_export_all]).

-include_lib("eunit/include/eunit.hrl").

%%  Very simply test compile the given contracts. Only basic checks
%%  are made on the output, just that it is a binary which indicates
%%  that the compilation worked.
calldata_test_() ->
     [ {"Testing " ++ ContractName ++ " contract calling " ++ Fun,
        fun() ->
           ContractString = aeso_test_utils:read_contract(ContractName),
           AevmExprs =
              case not lists:member(ContractName, not_yet_compilable(aevm)) of
                  true -> ast_exprs(ContractString, Fun, Args, [{backend, aevm}]
                                    ++ [no_implicit_stdlib || not aeso_compiler_tests:wants_stdlib(ContractName)]);
                  false -> undefined
              end,
           FateExprs =
              case not lists:member(ContractName, not_yet_compilable(fate)) of
                  true -> ast_exprs(ContractString, Fun, Args, [{backend, fate}]
                                    ++ [no_implicit_stdlib || not aeso_compiler_tests:wants_stdlib(ContractName)]);
                  false -> undefined
              end,
           case FateExprs == undefined orelse AevmExprs == undefined of
               true -> ok;
               false ->
                   ?assertEqual(FateExprs, AevmExprs)
           end
        end} || {ContractName, Fun, Args} <- compilable_contracts()].

calldata_aci_test_() ->
     [ {"Testing " ++ ContractName ++ " contract calling " ++ Fun,
        fun() ->
           ContractString       = aeso_test_utils:read_contract(ContractName),
           {ok, ContractACIBin} = aeso_aci:contract_interface(string, ContractString),
           ContractACI = binary_to_list(ContractACIBin),
           io:format("ACI:\n~s\n", [ContractACIBin]),
           AevmExprs =
              case not lists:member(ContractName, not_yet_compilable(aevm)) of
                  true -> ast_exprs(ContractACI, Fun, Args, [{backend, aevm}]
                                    ++ [no_implicit_stdlib || not aeso_compiler_tests:wants_stdlib(ContractName)]);
                  false -> undefined
              end,
           FateExprs =
              case not lists:member(ContractName, not_yet_compilable(fate)) of
                  true -> ast_exprs(ContractACI, Fun, Args, [{backend, fate}]
                                    ++ [no_implicit_stdlib || not aeso_compiler_tests:wants_stdlib(ContractName)]);
                  false -> undefined
              end,
           case FateExprs == undefined orelse AevmExprs == undefined of
               true -> ok;
               false ->
                   ?assertEqual(FateExprs, AevmExprs)
           end
        end} || {ContractName, Fun, Args} <- compilable_contracts()].


ast_exprs(ContractString, Fun, Args, Opts) ->
    {ok, Data} = (catch aeso_compiler:create_calldata(ContractString, Fun, Args, Opts)),
    {ok, _Types, Exprs} = (catch aeso_compiler:decode_calldata(ContractString, Fun, Data, Opts)),
    ?assert(is_list(Exprs)),
    Exprs.

check_errors(Expect, ErrorString) ->
    %% This removes the final single \n as well.
    Actual = binary:split(<<ErrorString/binary,$\n>>, <<"\n\n">>, [global,trim]),
    case {Expect -- Actual, Actual -- Expect} of
        {[], Extra}   -> ?assertMatch({unexpected, []}, {unexpected, Extra});
        {Missing, []} -> ?assertMatch({missing, []}, {missing, Missing});
        {Missing, Extra} -> ?assertEqual(Missing, Extra)
    end.

%% compilable_contracts() -> [ContractName].
%%  The currently compilable contracts.

compilable_contracts() ->
    [
     {"identity", "init", []},
     {"maps", "init", []},
     {"funargs", "menot", ["false"]},
     {"funargs", "append", ["[\"false\", \" is\", \" not\", \" true\"]"]},
     %% TODO {"funargs", "bitsum", ["Bits.all"]},
     {"funargs", "read", ["{label = \"question 1\", result = 4}"]},
     {"funargs", "sjutton", ["#0011012003100011012003100011012003"]},
     {"funargs", "sextiosju", ["#01020304050607080910111213141516171819202122232425262728293031323334353637383940"
                               "414243444546474849505152535455565758596061626364656667"]},
     {"funargs", "trettiotva", ["#0102030405060708091011121314151617181920212223242526272829303132"]},
     {"funargs", "find_oracle", ["ok_2YNyxd6TRJPNrTcEDCe9ra59SVUdp9FR9qWC5msKZWYD9bP9z5"]},
     {"funargs", "find_query", ["oq_2oRvyowJuJnEkxy58Ckkw77XfWJrmRgmGaLzhdqb67SKEL1gPY"]},
     {"funargs", "traffic_light", ["Green"]},
     {"funargs", "traffic_light", ["Pantone(12)"]},
     {"funargs", "tuples", ["()"]},
     %% TODO {"funargs", "due", ["FixedTTL(1020)"]},
     {"variant_types", "init", []},
     {"basic_auth", "init", []},
     {"address_literals", "init", []},
     {"bytes_equality", "init", []},
     {"address_chain", "init", []},
     {"counter", "init",
      ["-3334353637383940202122232425262728293031323334353637"]},
     {"dutch_auction", "init",
      ["ak_2gx9MEFxKvY9vMG5YnqnXWv1hCsX7rgnfvBLJS4aQurustR1rt", "200000", "1000"]},
     {"maps", "fromlist_i",
      ["[(1, {x = 1, y = 2}), (2, {x = 3, y = 4}), (3, {x = 4, y = 4})]"]},
     {"maps", "get_i", ["1", "{}"]},
     {"maps", "get_i", ["1", "{[1] = {x = 3, y = 4}}"]},
     {"maps", "get_i", ["1", "{[1] = {x = 3, y = 4}, [2] = {x = 4, y = 5}}"]},
     {"maps", "get_i", ["1", "{[1] = {x = 3, y = 4}, [2] = {x = 4, y = 5}, [3] = {x = 5, y = 6}}"]},
     {"strings", "str_concat", ["\"test\"","\"me\""]},
     {"complex_types", "filter_some", ["[Some(11), Some(12), None]"]},
     {"complex_types", "init", ["ct_Ez6MyeTMm17YnTnDdHTSrzMEBKmy7Uz2sXu347bTDPgVH2ifJ"]},
     {"__call" "init", []},
     {"bitcoin_auth", "authorize", ["1", "#0102030405060708090a0b0c0d0e0f101718192021222324252627282930313233343536373839401a1b1c1d1e1f202122232425262728293031323334353637"]},
     {"bitcoin_auth", "to_sign", ["#0102030405060708090a0b0c0d0e0f1017181920212223242526272829303132", "2"]},
     {"stub", "foo", ["42"]},
     {"stub", "foo", ["-42"]}
    ].

not_yet_compilable(fate) ->
    [];
not_yet_compilable(aevm) ->
    [].
