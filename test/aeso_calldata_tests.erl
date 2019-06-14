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
     [ {"Testing the " ++ ContractName ++ " contract with the " ++ atom_to_list(Backend) ++ " backend",
        fun() ->
            ContractString = aeso_test_utils:read_contract(ContractName),
            Res = aeso_compiler:create_calldata(ContractString, Fun, Args, [{backend, Backend}]),
            case Backend of
                aevm ->
                    ?assertMatch({ok, _, _, _}, Res);
                fate ->
                    ?assertMatch({ok, _}, Res)
            end
        end} || {ContractName, Fun, Args} <- compilable_contracts(), Backend <- [aevm, fate],
                not lists:member(ContractName, not_yet_compilable(Backend))].

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
     {"oracles", "init", []},
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
     {"complex_types", "filter_some", ["[Some(1), Some(2), None]"]},
     {"complex_types", "init", ["ct_Ez6MyeTMm17YnTnDdHTSrzMEBKmy7Uz2sXu347bTDPgVH2ifJ"]},
     {"__call" "init", []},
     {"bitcoin_auth", "authorize", ["1", "#0102030405060708090a0b0c0d0e0f101718192021222324252627282930313233343536373839401a1b1c1d1e1f202122232425262728293031323334353637"]},
     {"bitcoin_auth", "to_sign", ["#0102030405060708090a0b0c0d0e0f1017181920212223242526272829303132", "2"]}

    ].

not_yet_compilable(fate) ->
    ["oracles",             %% Oracle.register
     "events",
     "address_literals",    %% oracle_query_id literals
     "address_chain"        %% Oracle.check_query
    ];
not_yet_compilable(aevm) ->
    ["__call"].
