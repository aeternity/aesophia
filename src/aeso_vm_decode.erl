%%%-------------------------------------------------------------------
%%% @copyright (C) 2017, Aeternity Anstalt
%%% @doc Decoding aevm and fate data to AST
%%%
%%% @end
%%%-------------------------------------------------------------------

-module(aeso_vm_decode).

-export([ from_aevm/3, from_fate/2 ]).

-include_lib("aebytecode/include/aeb_fate_data.hrl").

address_literal(Type, N) -> {Type, [], <<N:256>>}.

-spec from_aevm(aeb_aevm_data:type(), aeso_syntax:type(), aeb_aevm_data:data()) -> aeso_syntax:expr().
from_aevm(word, {id, _, "address"},                     N) -> address_literal(account_pubkey, N);
from_aevm(word, {app_t, _, {id, _, "oracle"}, _},       N) -> address_literal(oracle_pubkey, N);
from_aevm(word, {app_t, _, {id, _, "oracle_query"}, _}, N) -> address_literal(oracle_query_id, N);
from_aevm(word, {con, _, _Name},                        N) -> address_literal(contract_pubkey, N);
from_aevm(word, {id, _, "int"}, N0) ->
    <<N:256/signed>> = <<N0:256>>,
    if N < 0 -> {app, [{format, prefix}], {'-', []}, [{int, [], -N}]};
       true  -> {int, [], N} end;
from_aevm(word, {id, _, "bits"}, N0) ->
    <<N:256/signed>> = <<N0:256>>,
    make_bits(N);
from_aevm(word, {id, _, "bool"}, N) -> {bool, [], N /= 0};
from_aevm(word, {bytes_t, _, Len}, Val) when Len =< 32 ->
    <<Bytes:Len/unit:8, _/binary>> = <<Val:32/unit:8>>,
    {bytes, [], <<Bytes:Len/unit:8>>};
from_aevm({tuple, _}, {bytes_t, _, Len}, Val) ->
    {bytes, [], binary:part(<< <<W:32/unit:8>> || W <- tuple_to_list(Val) >>, 0, Len)};
from_aevm(string, {id, _, "string"}, S) -> {string, [], S};
from_aevm({list, VmType}, {app_t, _, {id, _, "list"}, [Type]}, List) ->
    {list, [], [from_aevm(VmType, Type, X) || X <- List]};
from_aevm({variant, [[], [VmType]]}, {app_t, _, {id, _, "option"}, [Type]}, Val) ->
    case Val of
        {variant, 0, []}  -> {con, [], "None"};
        {variant, 1, [X]} -> {app, [], {con, [], "Some"}, [from_aevm(VmType, Type, X)]}
    end;
from_aevm({tuple, VmTypes}, {tuple_t, _, Types}, Val)
        when length(VmTypes) == length(Types),
             length(VmTypes) == tuple_size(Val) ->
    {tuple, [], [from_aevm(VmType, Type, X)
                 || {VmType, Type, X} <- lists:zip3(VmTypes, Types, tuple_to_list(Val))]};
from_aevm({tuple, VmTypes}, {record_t, Fields}, Val)
        when length(VmTypes) == length(Fields),
             length(VmTypes) == tuple_size(Val) ->
    {record, [], [ {field, [], [{proj, [], FName}], from_aevm(VmType, FType, X)}
                   || {VmType, {field_t, _, FName, FType}, X} <- lists:zip3(VmTypes, Fields, tuple_to_list(Val)) ]};
from_aevm({map, VmKeyType, VmValType}, {app_t, _, {id, _, "map"}, [KeyType, ValType]}, Map)
        when is_map(Map) ->
    {map, [], [ {from_aevm(VmKeyType, KeyType, Key),
                 from_aevm(VmValType, ValType, Val)}
                || {Key, Val} <- maps:to_list(Map) ]};
from_aevm({variant, VmCons}, {variant_t, Cons}, {variant, Tag, Args})
        when length(VmCons) == length(Cons),
             length(VmCons) > Tag ->
    VmTypes = lists:nth(Tag + 1, VmCons),
    ConType = lists:nth(Tag + 1, Cons),
    from_aevm(VmTypes, ConType, Args);
from_aevm([], {constr_t, _, Con, []}, []) -> Con;
from_aevm(VmTypes, {constr_t, _, Con, Types}, Args)
        when length(VmTypes) == length(Types),
             length(VmTypes) == length(Args) ->
    {app, [], Con, [ from_aevm(VmType, Type, Arg)
                     || {VmType, Type, Arg} <- lists:zip3(VmTypes, Types, Args) ]};
from_aevm(_VmType, _Type, _Data) ->
    throw(cannot_translate_to_sophia).


-spec from_fate(aeso_syntax:type(), aeb_fate_data:fate_type()) -> aeso_syntax:expr().
from_fate({id, _, "address"}, ?FATE_ADDRESS(Bin)) -> {account_pubkey, [], Bin};
from_fate({app_t, _, {id, _, "oracle"}, _}, ?FATE_ORACLE(Bin)) -> {oracle_pubkey, [], Bin};
from_fate({app_t, _, {id, _, "oracle_query"}, _}, ?FATE_ORACLE_Q(Bin)) -> {oracle_query_id, [], Bin};
from_fate({con, _, _Name},  ?FATE_CONTRACT(Bin)) -> {contract_pubkey, [], Bin};
from_fate({bytes_t, _, N},  ?FATE_BYTES(Bin)) when byte_size(Bin) == N -> {bytes, [], Bin};
from_fate({id, _, "bits"},  ?FATE_BITS(N)) -> make_bits(N);
from_fate({id, _, "int"},     N) when is_integer(N) ->
    if N < 0 -> {app, [{format, prefix}], {'-', []}, [{int, [], -N}]};
       true  -> {int, [], N} end;
from_fate({id, _, "bool"},    B) when is_boolean(B) -> {bool, [], B};
from_fate({id, _, "string"}, S) when is_binary(S) -> {string, [], S};
from_fate({app_t, _, {id, _, "list"}, [Type]}, List) when is_list(List) ->
    {list, [], [from_fate(Type, X) || X <- List]};
from_fate({app_t, _, {id, _, "option"}, [Type]}, Val) ->
    case Val of
        {variant, [0, 1], 0, {}}  -> {con, [], "None"};
        {variant, [0, 1], 1, {X}} -> {app, [], {con, [], "Some"}, [from_fate(Type, X)]}
    end;
from_fate({tuple_t, _, []}, ?FATE_UNIT) ->
     {tuple, [], []};
from_fate({tuple_t, _, Types}, ?FATE_TUPLE(Val))
        when length(Types) == tuple_size(Val) ->
    {tuple, [], [from_fate(Type, X)
                 || {Type, X} <- lists:zip(Types, tuple_to_list(Val))]};
from_fate({record_t, [{field_t, _, FName, FType}]}, Val) ->
    {record, [], [{field, [], [{proj, [], FName}], from_fate(FType, Val)}]};
from_fate({record_t, Fields}, ?FATE_TUPLE(Val))
        when length(Fields) == tuple_size(Val) ->
    {record, [], [ {field, [], [{proj, [], FName}], from_fate(FType, X)}
                   || {{field_t, _, FName, FType}, X} <- lists:zip(Fields, tuple_to_list(Val)) ]};
from_fate({app_t, _, {id, _, "map"}, [KeyType, ValType]}, Map)
        when is_map(Map) ->
    {map, [], [ {from_fate(KeyType, Key),
                 from_fate(ValType, Val)}
                || {Key, Val} <- maps:to_list(Map) ]};
from_fate({variant_t, Cons}, {variant, Ar, Tag, Args})
        when length(Cons) > Tag ->
    ConType = lists:nth(Tag + 1, Cons),
    Arity = lists:nth(Tag + 1, Ar),
    case tuple_to_list(Args) of
        ArgList when length(ArgList) == Arity ->
            from_fate(ConType, ArgList);
        _ -> throw(cannot_translate_to_sophia)
    end;
from_fate({constr_t, _, Con, []}, []) -> Con;
from_fate({constr_t, _, Con, Types}, Args)
        when length(Types) == length(Args) ->
    {app, [], Con, [ from_fate(Type, Arg)
                     || {Type, Arg} <- lists:zip(Types, Args) ]};
from_fate({qid, _, QType}, Val) ->
    from_fate_builtin(QType, Val);
from_fate(_Type, _Data) ->
    throw(cannot_translate_to_sophia).


from_fate_builtin(QType, Val) ->
    Con = fun([Name | _] = Names) when is_list(Name) -> {qcon, [], Names};
             (Name) -> {con, [], Name} end,
    App = fun(Name, []) -> Con(Name);
             (Name, Value) -> {app, [], Con(Name), Value} end,
    Chk = fun(Type, Value) -> from_fate(Type, Value) end,
    Int = {id, [], "int"},
    Str = {id, [], "string"},
    Adr = {id, [], "address"},
    Hsh = {bytes_t, [], 32},
    I32 = {bytes_t, [], 32},
    I48 = {bytes_t, [], 48},
    Qid = fun(Name) -> {qid, [], Name} end,
    Map = fun(KT, VT) -> {app_t, [], {id, [], "map"}, [KT, VT]} end,
    ChainTxArities = [3, 0, 0, 0, 0, 0, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 0],

    case {QType, Val} of
        {["Chain", "ttl"], {variant, [1, 1], 0, {X}}} -> App("RelativeTTL", [Chk(Int, X)]);
        {["Chain", "ttl"], {variant, [1, 1], 1, {X}}} -> App("FixedTTL", [Chk(Int, X)]);

        {["AENS", "name"], {variant, [3], 0, {Addr, TTL, Ptrs}}} ->
            App(["AENS","Name"], [Chk(Adr, Addr), Chk(Qid(["Chain", "ttl"]), TTL),
                              Chk(Map(Str, Qid(["AENS", "pointee"])), Ptrs)]);

        {["AENS", "pointee"], {variant, [1, 1, 1, 1], 0, {Addr}}} ->
            App(["AENS","AccountPt"], [Chk(Adr, Addr)]);
        {["AENS", "pointee"], {variant, [1, 1, 1, 1], 1, {Addr}}} ->
            App(["AENS","OraclePt"], [Chk(Adr, Addr)]);
        {["AENS", "pointee"], {variant, [1, 1, 1, 1], 2, {Addr}}} ->
            App(["AENS","ContractPt"], [Chk(Adr, Addr)]);
        {["AENS", "pointee"], {variant, [1, 1, 1, 1], 3, {Addr}}} ->
            App(["AENS","ChannelPt"], [Chk(Adr, Addr)]);

        {["Chain", "ga_meta_tx"], {variant, [2], 0, {Addr, X}}} ->
            App(["Chain","GAMetaTx"], [Chk(Adr, Addr), Chk(Int, X)]);

        {["Chain", "paying_for_tx"], {variant, [2], 0, {Addr, X}}} ->
            App(["Chain","PayingForTx"], [Chk(Adr, Addr), Chk(Int, X)]);

        {["Chain", "base_tx"], {variant, ChainTxArities, 0, {Addr, Fee, Payload}}} ->
            App(["Chain","SpendTx"], [Chk(Adr, Addr), Chk(Int, Fee), Chk(Str, Payload)]);
        {["Chain", "base_tx"], {variant, ChainTxArities, 1, {}}} ->
            App(["Chain","OracleRegisterTx"], []);
        {["Chain", "base_tx"], {variant, ChainTxArities, 2, {}}} ->
            App(["Chain","OracleQueryTx"], []);
        {["Chain", "base_tx"], {variant, ChainTxArities, 3, {}}} ->
            App(["Chain","OracleResponseTx"], []);
        {["Chain", "base_tx"], {variant, ChainTxArities, 4, {}}} ->
            App(["Chain","OracleExtendTx"], []);
        {["Chain", "base_tx"], {variant, ChainTxArities, 5, {}}} ->
            App(["Chain","NamePreclaimTx"], []);
        {["Chain", "base_tx"], {variant, ChainTxArities, 6, {Name}}} ->
            App(["Chain","NameClaimTx"], [Chk(Str, Name)]);
        {["Chain", "base_tx"], {variant, ChainTxArities, 7, {NameHash}}} ->
            App(["Chain","NameUpdateTx"], [Chk(Hsh, NameHash)]);
        {["Chain", "base_tx"], {variant, ChainTxArities, 8, {NameHash}}} ->
            App(["Chain","NameRevokeTx"], [Chk(Hsh, NameHash)]);
        {["Chain", "base_tx"], {variant, ChainTxArities, 9, {NewOwner, NameHash}}} ->
            App(["Chain","NameTransferTx"], [Chk(Adr, NewOwner), Chk(Hsh, NameHash)]);
        {["Chain", "base_tx"], {variant, ChainTxArities, 10, {Addr}}} ->
            App(["Chain","ChannelCreateTx"], [Chk(Adr, Addr)]);
        {["Chain", "base_tx"], {variant, ChainTxArities, 11, {Addr, Amount}}} ->
            App(["Chain","ChannelDepositTx"], [Chk(Adr, Addr), Chk(Int, Amount)]);
        {["Chain", "base_tx"], {variant, ChainTxArities, 12, {Addr, Amount}}} ->
            App(["Chain","ChannelWithdrawTx"], [Chk(Adr, Addr), Chk(Int, Amount)]);
        {["Chain", "base_tx"], {variant, ChainTxArities, 13, {Addr}}} ->
            App(["Chain","ChannelForceProgressTx"], [Chk(Adr, Addr)]);
        {["Chain", "base_tx"], {variant, ChainTxArities, 14, {Addr}}} ->
            App(["Chain","ChannelCloseMutualTx"], [Chk(Adr, Addr)]);
        {["Chain", "base_tx"], {variant, ChainTxArities, 15, {Addr}}} ->
            App(["Chain","ChannelCloseSoloTx"], [Chk(Adr, Addr)]);
        {["Chain", "base_tx"], {variant, ChainTxArities, 16, {Addr}}} ->
            App(["Chain","ChannelSlashTx"], [Chk(Adr, Addr)]);
        {["Chain", "base_tx"], {variant, ChainTxArities, 17, {Addr}}} ->
            App(["Chain","ChannelSettleTx"], [Chk(Adr, Addr)]);
        {["Chain", "base_tx"], {variant, ChainTxArities, 18, {Addr}}} ->
            App(["Chain","ChannelSnapshotSoloTx"], [Chk(Adr, Addr)]);
        {["Chain", "base_tx"], {variant, ChainTxArities, 19, {Amount}}} ->
            App(["Chain","ContractCreateTx"], [Chk(Int, Amount)]);
        {["Chain", "base_tx"], {variant, ChainTxArities, 20, {Addr, Amount}}} ->
            App(["Chain","ContractCallTx"], [Chk(Adr, Addr), Chk(Int, Amount)]);
        {["Chain", "base_tx"], {variant, ChainTxArities, 21, {}}} ->
            App(["Chain","GAAttachTx"], []);

        {["MCL_BLS12_381", "fp"], X} ->
            App(["MCL_BLS12_381", "fp"], [Chk(I32, X)]);
        {["MCL_BLS12_381", "fr"], X} ->
            App(["MCL_BLS12_381", "fr"], [Chk(I48, X)]);

        _ ->
            throw(cannot_translate_to_sophia)
    end.

make_bits(N) ->
    Id = fun(F) -> {qid, [], ["Bits", F]} end,
    if N < 0 -> make_bits(Id("clear"), Id("all"), 0, bnot N);
       true  -> make_bits(Id("set"), Id("none"), 0, N) end.

make_bits(_Set, Zero, _I, 0) -> Zero;
make_bits(Set, Zero, I, N) when 0 == N rem 2 ->
    make_bits(Set, Zero, I + 1, N div 2);
make_bits(Set, Zero, I, N) ->
    {app, [], Set, [make_bits(Set, Zero, I + 1, N div 2), {int, [], I}]}.

