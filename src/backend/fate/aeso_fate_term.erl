%%%-------------------------------------------------------------------
%%% @doc Term-to-FATE constant folding and code serialization helpers
%%%-------------------------------------------------------------------
-module(aeso_fate_term).

-export([term_to_fate/1, term_to_fate/2, term_to_fate/3, lit_to_fate/2, serialize_contract_code/2]).

-include("aeso_fate_env.hrl").

serialize_contract_code(Env, C) ->
    Cache = case get(contract_code_cache) of
                undefined -> put(contract_code_cache, #{}), #{};
                Res       -> Res
            end,
    case maps:get(C, Cache, none) of
        none ->
            Options = Env#env.options,
            SavedFreshNames = Env#env.saved_fresh_names,
            FCode = maps:get(C, Env#env.child_contracts),
            FateCode = aeso_fcode_to_fate:compile(Env#env.child_contracts, FCode, SavedFreshNames, Options),
            ByteCode = aeb_fate_code:serialize(FateCode, []),
            {ok, Version} = aeso_compiler:version(),
            OriginalSourceCode = proplists:get_value(original_src, Options, ""),
            Code = #{byte_code => ByteCode,
                     compiler_version => Version,
                     source_hash => crypto:hash(sha256, OriginalSourceCode ++ [0] ++ C),
                     type_info => [],
                     abi_version => aeb_fate_abi:abi_version(),
                     payable => maps:get(payable, FCode)
                   },
            Serialized = aeser_contract_code:serialize(Code),
            put(contract_code_cache, maps:put(C, Serialized, Cache)),
            Serialized;
        Serialized -> Serialized
    end.

lit_to_fate(Env, L) ->
    case L of
        {int, N}             -> aeb_fate_data:make_integer(N);
        {string, S}          -> aeb_fate_data:make_string(S);
        {bytes, B}           -> aeb_fate_data:make_bytes(B);
        {bool, B}            -> aeb_fate_data:make_boolean(B);
        {account_pubkey, K}  -> aeb_fate_data:make_address(K);
        {signature, S}       -> aeb_fate_data:make_bytes(S);
        {contract_pubkey, K} -> aeb_fate_data:make_contract(K);
        {oracle_pubkey, K}   -> aeb_fate_data:make_oracle(K);
        {oracle_query_id, H} -> aeb_fate_data:make_oracle_query(H);
        {contract_code, C}   -> aeb_fate_data:make_contract_bytearray(serialize_contract_code(Env, C));
        {typerep, T}         -> aeb_fate_data:make_typerep(aeso_fate_types:type_to_scode(T))
     end.

term_to_fate(E) -> term_to_fate(#env{}, #{}, E).
term_to_fate(GlobEnv, E) -> term_to_fate(GlobEnv, #{}, E).

term_to_fate(GlobEnv, _Env, {lit, _, L}) ->
    lit_to_fate(GlobEnv, L);
%% negative literals are parsed as 0 - N
term_to_fate(_GlobEnv, _Env, {op, _, '-', [{lit, _, {int, 0}}, {lit, _, {int, N}}]}) ->
    aeb_fate_data:make_integer(-N);
term_to_fate(_GlobEnv, _Env, {nil, _}) ->
    aeb_fate_data:make_list([]);
term_to_fate(GlobEnv, Env, {op, _, '::', [Hd, Tl]}) ->
    %% The Tl will translate into a list, because FATE lists are just lists
    [term_to_fate(GlobEnv, Env, Hd) | term_to_fate(GlobEnv, Env, Tl)];
term_to_fate(GlobEnv, Env, {tuple, _, As}) ->
    aeb_fate_data:make_tuple(list_to_tuple([ term_to_fate(GlobEnv, Env, A) || A<-As]));
term_to_fate(GlobEnv, Env, {con, _, Ar, I, As}) ->
    FateAs = [ term_to_fate(GlobEnv, Env, A) || A <- As ],
    aeb_fate_data:make_variant(Ar, I, list_to_tuple(FateAs));
term_to_fate(_GlobEnv, _Env, {builtin, _, bits_all, []}) ->
    aeb_fate_data:make_bits(-1);
term_to_fate(_GlobEnv, _Env, {builtin, _, bits_none, []}) ->
    aeb_fate_data:make_bits(0);
term_to_fate(GlobEnv, _Env, {op, _, bits_set, [B, I]}) ->
    {bits, N} = term_to_fate(GlobEnv, B),
    J         = term_to_fate(GlobEnv, I),
    {bits, N bor (1 bsl J)};
term_to_fate(GlobEnv, _Env, {op, _, bits_clear, [B, I]}) ->
    {bits, N} = term_to_fate(GlobEnv, B),
    J         = term_to_fate(GlobEnv, I),
    {bits, N band bnot (1 bsl J)};
term_to_fate(GlobEnv, Env, {'let', _, X, E, Body}) ->
    Env1 = Env#{ X => term_to_fate(GlobEnv, Env, E) },
    term_to_fate(GlobEnv, Env1, Body);
term_to_fate(_GlobEnv, Env, {var, _, X}) ->
    case maps:get(X, Env, undefined) of
        undefined -> throw(not_a_fate_value);
        V         -> V
    end;
term_to_fate(_GlobEnv, _Env, {builtin, _, map_empty, []}) ->
    aeb_fate_data:make_map(#{});
term_to_fate(GlobEnv, Env, {op, _, map_set, [M, K, V]}) ->
    Map = term_to_fate(GlobEnv, Env, M),
    Map#{term_to_fate(GlobEnv, Env, K) => term_to_fate(GlobEnv, Env, V)};
term_to_fate(GlobEnv, Env, {builtin, _, bytes_to_any_size, [Bs]}) ->
    term_to_fate(GlobEnv, Env, Bs);
term_to_fate(_GlobEnv, _Env, _) ->
    throw(not_a_fate_value).


