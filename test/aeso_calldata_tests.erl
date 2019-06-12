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
            Res = aeso_compiler:create_calldata(ContractString, "init", [], [{backend, Backend}]),
            case Backend of
                aevm ->
                    ?assertMatch({ok, _, _, _}, Res);
                fate ->
                    ?assertMatch({ok, _}, Res)
            end
        end} || ContractName <- compilable_contracts(), Backend <- [aevm, fate],
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
     "functions",
     "identity",
     "maps",
     "oracles",
     "remote_call",
     "simple",
     "spend_test",
     "test",
     "builtin_bug",
     "builtin_map_get_bug",
     "nodeadcode",
     "deadcode",
     "variant_types",
     "events",
     "basic_auth",
     "address_literals",
     "bytes_equality",
     "address_chain",
     "__call"
    ].

not_yet_compilable(fate) ->
    ["oracles",             %% Oracle.register
     "events",
     "basic_auth",          %% auth_tx_hash instruction
     "address_literals",    %% oracle_query_id literals
     "address_chain"        %% Oracle.check_query
    ];
not_yet_compilable(aevm) ->
    ["__call"].
