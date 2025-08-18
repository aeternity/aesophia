%%%-------------------------------------------------------------------
%%% @doc Builtins lowering to FATE scode
%%%-------------------------------------------------------------------
-module(aeso_fate_builtins).

-export([builtin_to_scode/3, call_to_scode/3, tuple/1, push/1]).

-include("aeso_fate_env.hrl").

%% Reuse helpers
push(A) -> {'STORE', ?a, A}.

tuple(0) -> push(?i({tuple, {}}));
tuple(N) -> aeb_fate_ops:tuple(?a, N).

call_to_scode(Env, CallCode, Args) ->
    [[aeso_fate_codegen:to_scode(aeso_fate_codegen:notail(Env), A) || A <- lists:reverse(Args)],
     CallCode].

builtin_to_scode(Env, chain_event, Args) ->
    call_to_scode(Env, [erlang:apply(aeb_fate_ops, log, lists:duplicate(length(Args), ?a)),
                        tuple(0)], Args);
builtin_to_scode(_Env, map_empty, []) ->
    [aeb_fate_ops:map_empty(?a)];
builtin_to_scode(_Env, bits_none, []) ->
    [aeb_fate_ops:bits_none(?a)];
builtin_to_scode(_Env, bits_all, []) ->
    [aeb_fate_ops:bits_all(?a)];
builtin_to_scode(Env, bytes_to_int, [_] = Args) ->
    call_to_scode(Env, aeb_fate_ops:bytes_to_int(?a, ?a), Args);
builtin_to_scode(Env, bytes_to_str, [_] = Args) ->
    call_to_scode(Env, aeb_fate_ops:bytes_to_str(?a, ?a), Args);
builtin_to_scode(Env, bytes_concat, [_, _] = Args) ->
    call_to_scode(Env, aeb_fate_ops:bytes_concat(?a, ?a, ?a), Args);
builtin_to_scode(Env, bytes_split, [_, _] = Args) ->
    call_to_scode(Env, aeb_fate_ops:bytes_split(?a, ?a, ?a), Args);
builtin_to_scode(Env, bytes_split_any, [_, _] = Args) ->
    call_to_scode(Env, aeb_fate_ops:bytes_split_any(?a, ?a, ?a), Args);
builtin_to_scode(Env, bytes_to_fixed_size, [_, _] = Args) ->
    call_to_scode(Env, aeb_fate_ops:bytes_to_fixed_size(?a, ?a, ?a), Args);
builtin_to_scode(Env, bytes_to_any_size, [A]) ->
    [aeso_fate_codegen:to_scode(Env, A)];
builtin_to_scode(Env, bytes_size, [_] = Args) ->
    call_to_scode(Env, aeb_fate_ops:bytes_size(?a, ?a), Args);
builtin_to_scode(Env, abort, [_] = Args) ->
    call_to_scode(Env, aeb_fate_ops:abort(?a), Args);
builtin_to_scode(Env, exit, [_] = Args) ->
    call_to_scode(Env, aeb_fate_ops:exit(?a), Args);
builtin_to_scode(Env, chain_spend, [_, _] = Args) ->
    call_to_scode(Env, [aeb_fate_ops:spend(?a, ?a), tuple(0)], Args);
builtin_to_scode(Env, chain_balance, [_] = Args) ->
    call_to_scode(Env, aeb_fate_ops:balance_other(?a, ?a), Args);
builtin_to_scode(Env, chain_block_hash, [_] = Args) ->
    call_to_scode(Env, aeb_fate_ops:blockhash(?a, ?a), Args);
builtin_to_scode(_Env, chain_coinbase, []) -> [aeb_fate_ops:beneficiary(?a)];
builtin_to_scode(_Env, chain_timestamp, []) -> [aeb_fate_ops:timestamp(?a)];
builtin_to_scode(_Env, chain_block_height, []) -> [aeb_fate_ops:generation(?a)];
builtin_to_scode(_Env, chain_difficulty, []) -> [aeb_fate_ops:difficulty(?a)];
builtin_to_scode(_Env, chain_gas_limit, []) -> [aeb_fate_ops:gaslimit(?a)];
builtin_to_scode(_Env, chain_network_id, []) -> [aeb_fate_ops:network_id(?a)];
builtin_to_scode(_Env, contract_balance, []) -> [aeb_fate_ops:balance(?a)];
builtin_to_scode(_Env, contract_address, []) -> [aeb_fate_ops:address(?a)];
builtin_to_scode(_Env, contract_creator, []) -> [aeb_fate_ops:contract_creator(?a)];
builtin_to_scode(_Env, call_origin, []) -> [aeb_fate_ops:origin(?a)];
builtin_to_scode(_Env, call_caller, []) -> [aeb_fate_ops:caller(?a)];
builtin_to_scode(_Env, call_value, []) -> [aeb_fate_ops:call_value(?a)];
builtin_to_scode(_Env, call_gas_price, []) -> [aeb_fate_ops:gasprice(?a)];
builtin_to_scode(_Env, call_fee, []) -> [aeb_fate_ops:fee(?a)];
builtin_to_scode(_Env, call_gas_left, []) -> [aeb_fate_ops:gas(?a)];
builtin_to_scode(Env, oracle_register, [_Sign,_Account,_QFee,_TTL,_QType,_RType] = Args) ->
    call_to_scode(Env, aeb_fate_ops:oracle_register(?a, ?a, ?a, ?a, ?a, ?a, ?a), Args);
builtin_to_scode(Env, oracle_expiry, [_Oracle] = Args) ->
    call_to_scode(Env, aeb_fate_ops:oracle_expiry(?a, ?a), Args);
builtin_to_scode(Env, oracle_query_fee, [_Oracle] = Args) ->
    call_to_scode(Env, aeb_fate_ops:oracle_query_fee(?a, ?a), Args);
builtin_to_scode(Env, oracle_query, [_Oracle, _Question, _QFee, _QTTL, _RTTL, _QType, _RType] = Args) ->
    call_to_scode(Env, aeb_fate_ops:oracle_query(?a, ?a, ?a, ?a, ?a, ?a, ?a, ?a), Args);
builtin_to_scode(Env, oracle_get_question, [_Oracle, _QueryId, _QType, _RType] = Args) ->
    call_to_scode(Env, aeb_fate_ops:oracle_get_question(?a, ?a, ?a, ?a, ?a), Args);
builtin_to_scode(Env, oracle_respond, [_Sign, _Oracle, _QueryId, _Response, _QType, _RType] = Args) ->
    call_to_scode(Env, [aeb_fate_ops:oracle_respond(?a, ?a, ?a, ?a, ?a, ?a), tuple(0)], Args);
builtin_to_scode(Env, oracle_extend, [_Sign, _Oracle, _TTL] = Args) ->
    call_to_scode(Env, [aeb_fate_ops:oracle_extend(?a, ?a, ?a), tuple(0)], Args);
builtin_to_scode(Env, oracle_get_answer, [_Oracle, _QueryId, _QType, _RType] = Args) ->
    call_to_scode(Env, aeb_fate_ops:oracle_get_answer(?a, ?a, ?a, ?a, ?a), Args);
builtin_to_scode(Env, oracle_check, [_Oracle, _QType, _RType] = Args) ->
    call_to_scode(Env, aeb_fate_ops:oracle_check(?a, ?a, ?a, ?a), Args);
builtin_to_scode(Env, oracle_check_query, [_Oracle, _Query, _QType, _RType] = Args) ->
    call_to_scode(Env, aeb_fate_ops:oracle_check_query(?a, ?a, ?a, ?a, ?a), Args);
builtin_to_scode(Env, address_is_oracle, [_] = Args) ->
    call_to_scode(Env, aeb_fate_ops:is_oracle(?a, ?a), Args);
builtin_to_scode(Env, address_is_contract, [_] = Args) ->
    call_to_scode(Env, aeb_fate_ops:is_contract(?a, ?a), Args);
builtin_to_scode(Env, address_is_payable, [_] = Args) ->
    call_to_scode(Env, aeb_fate_ops:is_payable(?a, ?a), Args);
builtin_to_scode(Env, aens_resolve, [_Name, _Key, _Type] = Args) ->
    call_to_scode(Env, aeb_fate_ops:aens_resolve(?a, ?a, ?a, ?a), Args);
builtin_to_scode(Env, aens_preclaim, [_Sign, _Account, _Hash] = Args) ->
    call_to_scode(Env, [aeb_fate_ops:aens_preclaim(?a, ?a, ?a), tuple(0)], Args);
builtin_to_scode(Env, aens_claim, [_Sign, _Account, _NameString, _Salt, _NameFee] = Args) ->
    call_to_scode(Env, [aeb_fate_ops:aens_claim(?a, ?a, ?a, ?a, ?a), tuple(0)], Args);
builtin_to_scode(Env, aens_transfer, [_Sign, _From, _To, _Name] = Args) ->
    call_to_scode(Env, [aeb_fate_ops:aens_transfer(?a, ?a, ?a, ?a), tuple(0)], Args);
builtin_to_scode(Env, aens_revoke, [_Sign, _Account, _Name] = Args) ->
    call_to_scode(Env, [aeb_fate_ops:aens_revoke(?a, ?a, ?a), tuple(0)], Args);
builtin_to_scode(Env, aens_update, [_Sign, _Account, _NameString, _TTL, _ClientTTL, _Pointers] = Args) ->
    call_to_scode(Env, [aeb_fate_ops:aens_update(?a, ?a, ?a, ?a, ?a, ?a), tuple(0)], Args);
builtin_to_scode(Env, aens_lookup, [_Name] = Args) ->
    call_to_scode(Env, aeb_fate_ops:aens_lookup(?a, ?a), Args);
builtin_to_scode(_Env, auth_tx_hash, []) -> [aeb_fate_ops:auth_tx_hash(?a)];
builtin_to_scode(_Env, auth_tx, []) -> [aeb_fate_ops:auth_tx(?a)];
builtin_to_scode(Env, chain_bytecode_hash, [_Addr] = Args) ->
    call_to_scode(Env, aeb_fate_ops:bytecode_hash(?a, ?a), Args);
builtin_to_scode(Env, chain_clone, [InitArgsT, GasCap, Value, Prot, Contract | InitArgs]) ->
    case GasCap of
        {builtin, _, call_gas_left, _} ->
            call_to_scode(Env, aeb_fate_ops:clone(?a, ?a, ?a, ?a), [Contract, InitArgsT, Value, Prot | InitArgs]);
        _ ->
            call_to_scode(Env, aeb_fate_ops:clone_g(?a, ?a, ?a, ?a, ?a), [Contract, InitArgsT, Value, GasCap, Prot | InitArgs])
    end;
builtin_to_scode(Env, chain_create, [Code, InitArgsT, Value | InitArgs]) ->
    call_to_scode(Env, aeb_fate_ops:create(?a, ?a, ?a), [Code, InitArgsT, Value | InitArgs]).


