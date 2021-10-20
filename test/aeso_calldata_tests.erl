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
                  true -> ast_exprs(ContractString, Fun, Args, [{backend, aevm}]);
                  false -> undefined
              end,
           FateExprs =
              case not lists:member(ContractName, not_yet_compilable(fate)) of
                  true -> ast_exprs(ContractString, Fun, Args, [{backend, fate}]);
                  false -> undefined
              end,
           ParsedExprs = parse_args(Fun, Args),
           [ ?assertEqual(ParsedExprs, AevmExprs) || AevmExprs /= undefined ],
           [ ?assertEqual(ParsedExprs, FateExprs) || FateExprs /= undefined ],
           ok
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
                  true -> ast_exprs(ContractACI, Fun, Args, [{backend, aevm}]);
                  false -> undefined
              end,
           FateExprs =
              case not lists:member(ContractName, not_yet_compilable(fate)) of
                  true -> ast_exprs(ContractACI, Fun, Args, [{backend, fate}]);
                  false -> undefined
              end,
           ParsedExprs = parse_args(Fun, Args),
           [ ?assertEqual(ParsedExprs, AevmExprs) || AevmExprs /= undefined ],
           [ ?assertEqual(ParsedExprs, FateExprs) || FateExprs /= undefined ],
           ok
        end} || {ContractName, Fun, Args} <- compilable_contracts()].

parse_args(Fun, Args) ->
    [{contract_main, _, _, [{letfun, _, _, _, _, [{guarded, _, [], {app, _, _, AST}}]}]}] =
        aeso_parser:string("main contract Temp = function foo() = " ++ Fun ++ "(" ++ string:join(Args, ", ") ++ ")"),
    strip_ann(AST).

strip_ann(T) when is_tuple(T) ->
    strip_ann1(setelement(2, T, []));
strip_ann(X) -> strip_ann1(X).

strip_ann1({map, [], KVs}) ->
    {map, [], [{strip_ann(K), strip_ann(V)} || {K, V} <- KVs]};
strip_ann1(T) when is_tuple(T) ->
    list_to_tuple(strip_ann1(tuple_to_list(T)));
strip_ann1(L) when is_list(L) ->
    lists:map(fun strip_ann/1, L);
strip_ann1(X) -> X.

ast_exprs(ContractString, Fun, Args, Opts) ->
    {ok, Data} = (catch aeso_compiler:create_calldata(ContractString, Fun, Args, Opts)),
    {ok, _Types, Exprs} = (catch aeso_compiler:decode_calldata(ContractString, Fun, Data, Opts)),
    ?assert(is_list(Exprs)),
    strip_ann(Exprs).

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
     {"funargs", "bitsum", ["Bits.all"]},
     {"funargs", "bitsum", ["Bits.clear(Bits.clear(Bits.all, 4), 2)"]}, %% Order matters for test
     {"funargs", "bitsum", ["Bits.set(Bits.set(Bits.none, 4), 2)"]},
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
     {"funargs", "due", ["FixedTTL(1020)"]},
     {"funargs", "singleton_rec", ["{x = 1000}"]},
     {"funargs", "aens_name", ["AENS.Name(ak_2dATVcZ9KJU5a8hdsVtTv21pYiGWiPbmVcU1Pz72FFqpk9pSRR, RelativeTTL(100), {[\"pt1\"] = AENS.AccountPt(ak_2dATVcZ9KJU5a8hdsVtTv21pYiGWiPbmVcU1Pz72FFqpk9pSRR)})"]},
     {"funargs", "aens_pointee", ["AENS.AccountPt(ak_2dATVcZ9KJU5a8hdsVtTv21pYiGWiPbmVcU1Pz72FFqpk9pSRR)"]},
     {"funargs", "aens_pointee", ["AENS.OraclePt(ak_2dATVcZ9KJU5a8hdsVtTv21pYiGWiPbmVcU1Pz72FFqpk9pSRR)"]},
     {"funargs", "aens_pointee", ["AENS.ContractPt(ak_2dATVcZ9KJU5a8hdsVtTv21pYiGWiPbmVcU1Pz72FFqpk9pSRR)"]},
     {"funargs", "aens_pointee", ["AENS.ChannelPt(ak_2dATVcZ9KJU5a8hdsVtTv21pYiGWiPbmVcU1Pz72FFqpk9pSRR)"]},
     {"funargs", "chain_ga_meta_tx", ["Chain.GAMetaTx(ak_2dATVcZ9KJU5a8hdsVtTv21pYiGWiPbmVcU1Pz72FFqpk9pSRR, 42)"]},
     {"funargs", "chain_paying_for_tx", ["Chain.PayingForTx(ak_2dATVcZ9KJU5a8hdsVtTv21pYiGWiPbmVcU1Pz72FFqpk9pSRR, 42)"]},
     {"funargs", "chain_base_tx", ["Chain.SpendTx(ak_2dATVcZ9KJU5a8hdsVtTv21pYiGWiPbmVcU1Pz72FFqpk9pSRR, 42,\"foo\")"]},
     {"funargs", "chain_base_tx", ["Chain.ContractCreateTx(12234)"]},
     {"funargs", "chain_base_tx", ["Chain.ContractCallTx(ak_2dATVcZ9KJU5a8hdsVtTv21pYiGWiPbmVcU1Pz72FFqpk9pSRR, 12234)"]},
     {"funargs", "chain_base_tx", ["Chain.OracleRegisterTx"]},
     {"funargs", "chain_base_tx", ["Chain.OracleQueryTx"]},
     {"funargs", "chain_base_tx", ["Chain.OracleResponseTx"]},
     {"funargs", "chain_base_tx", ["Chain.OracleExtendTx"]},
     {"funargs", "chain_base_tx", ["Chain.NamePreclaimTx"]},
     {"funargs", "chain_base_tx", ["Chain.NameClaimTx(\"acoolname.chain\")"]},
     {"funargs", "chain_base_tx", ["Chain.NameUpdateTx(#ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)"]},
     {"funargs", "chain_base_tx", ["Chain.NameRevokeTx(#ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)"]},
     {"funargs", "chain_base_tx", ["Chain.NameTransferTx(ak_2dATVcZ9KJU5a8hdsVtTv21pYiGWiPbmVcU1Pz72FFqpk9pSRR, #ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)"]},
     {"funargs", "chain_base_tx", ["Chain.GAAttachTx"]},
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
     {"bitcoin_auth", "authorize", ["1", "#0102030405060708090a0b0c0d0e0f101718192021222324252627282930313233343536373839401a1b1c1d1e1f20212223242526272829303132333435363738"]},
     {"bitcoin_auth", "to_sign", ["#0102030405060708090a0b0c0d0e0f1017181920212223242526272829303132", "2"]},
     {"stub", "foo", ["42"]},
     {"stub", "foo", ["-42"]},
     {"payable", "foo", ["42"]}
    ].

not_yet_compilable(fate) ->
    [];
not_yet_compilable(aevm) ->
    ["funargs", "strings"].
