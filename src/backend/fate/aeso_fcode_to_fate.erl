%%%-------------------------------------------------------------------
%%% @author Ulf Norell
%%% @copyright (C) 2019, Aeternity Anstalt
%%% @doc
%%%     Fate backend for Sophia compiler
%%% @end
%%% Created : 11 Jan 2019
%%%
%%%-------------------------------------------------------------------
-module(aeso_fcode_to_fate).
-behaviour(aeso_backend).

-export([compile/3, compile/4, term_to_fate/1, term_to_fate/2]).
%% Temporary exports for refactor shims
-export([annotate_code/1, simplify/2, debug/3]).
%% Public helpers referenced by extracted modules
-export([make_function_id/1, make_function_name/1, code_error/1]).

-ifdef(TEST).
-export([]).
-endif.

%% -- Preamble ---------------------------------------------------------------

-include("aeso_fate_env.hrl").

-define(TODO(What), error({todo, ?FILE, ?LINE, ?FUNCTION_NAME, What})).

%% -- Debugging --------------------------------------------------------------

is_debug(Tag, Options) ->
    Tags = proplists:get_value(debug, Options, []),
    Tags == all orelse lists:member(Tag, Tags).

-define(debug(Tag, Options, Fmt, Args),
        aeso_fate_debug:debug(Tag, Options, fun() -> io:format(Fmt, Args) end)).

debug(Tag, Options, Fun) -> aeso_fate_debug:debug(Tag, Options, Fun).

-dialyzer({nowarn_function, [code_error/1]}).
code_error(Err) ->
    Pos = aeso_errors:pos(0, 0),
    Msg = lists:flatten(io_lib:format("Unknown error: ~p\n", [Err])),
    aeso_errors:throw(aeso_errors:new(code_error, Pos, Msg)).

%% -- Main -------------------------------------------------------------------

%% @doc Main entry point.
compile(FCode, SavedFreshNames, Options) ->
    compile(#{}, FCode, SavedFreshNames, Options).
compile(ChildContracts, FCode, SavedFreshNames, Options) ->
    #{ contract_name := ContractName,
       functions     := Functions } = FCode,
    SFuns  = functions_to_scode(ChildContracts, ContractName, Functions, SavedFreshNames, Options),
    SFuns1 = aeso_fate_opt:optimize_scode(SFuns, Options),
    FateCode = aeso_fate_blocks:to_basic_blocks(SFuns1),
    ?debug(compile, Options, "~s\n", [aeb_fate_asm:pp(FateCode)]),
    case proplists:get_value(include_child_contract_symbols, Options, false) of
        false -> FateCode;
        true  -> add_child_symbols(ChildContracts, FateCode)
    end.

make_function_id(X) ->
    aeb_fate_code:symbol_identifier(make_function_name(X)).

make_function_name(event)              -> <<"Chain.event">>;
make_function_name({entrypoint, Name}) -> Name;
make_function_name({local_fun, Xs})    -> list_to_binary("." ++ string:join(Xs, ".")).

add_child_symbols(ChildContracts, FateCode) ->
    Funs = lists:flatten([ maps:keys(ChildFuns) || {_, #{functions := ChildFuns}} <- maps:to_list(ChildContracts) ]),
    Symbols = maps:from_list([ {make_function_id(FName), make_function_name(FName)} || FName <- Funs ]),
    aeb_fate_code:update_symbols(FateCode, Symbols).

functions_to_scode(ChildContracts, ContractName, Functions, SavedFreshNames, Options) ->
    FunNames = maps:keys(Functions),
    maps:from_list(
        [ {make_function_name(Name), function_to_scode(ChildContracts, ContractName, FunNames, Name, Attrs, Args, Body, Type, SavedFreshNames, Options)}
        || {Name, #{args   := Args,
                    body   := Body,
                    attrs  := Attrs,
                    return := Type}} <- maps:to_list(Functions)]).

function_to_scode(ChildContracts, ContractName, Functions, Name, Attrs0, Args, Body, ResType, SavedFreshNames, Options) ->
    {ArgTypes, ResType1} = aeso_fate_types:typesig_to_scode(Args, ResType),
    Attrs = [ A || A <- Attrs0, A == private orelse A == payable ],
    Env = init_env(ChildContracts, ContractName, Functions, Name, Args, SavedFreshNames, Options),
    ArgsNames = [ X || {X, _} <- lists:reverse(Env#env.vars) ],

    %% DBG_LOC is added before the function body to make it possible to break
    %% at the function signature
    SCode = aeso_fate_codegen:to_scode(Env, Body),
    DbgSCode = aeso_fate_debug:dbg_contract(Env) ++ aeso_fate_debug:dbg_loc(Env, Attrs0) ++ aeso_fate_debug:dbg_scoped_vars(Env, ArgsNames, SCode),
    {Attrs, {ArgTypes, ResType1}, DbgSCode}.

%% types lowered via aeso_fate_types

%% -- Phase I ----------------------------------------------------------------
%%  Icode to structured assembly

%% -- Environment functions --

init_env(ChildContracts, ContractName, FunNames, Name, Args, SavedFreshNames, Options) ->
    #env{ vars              = [ {X, {arg, I}} || {I, {X, _}} <- with_ixs(Args) ],
          contract          = ContractName,
          child_contracts   = ChildContracts,
          locals            = FunNames,
          current_function  = Name,
          options           = Options,
          tailpos           = true,
          saved_fresh_names = SavedFreshNames,
          debug_info        = proplists:get_value(debug_info, Options, false) }.

%% env helpers moved to aeso_fate_codegen

%% Delegate public term API to aeso_fate_term
term_to_fate(E) -> aeso_fate_term:term_to_fate(E).
term_to_fate(GlobEnv, E) -> aeso_fate_term:term_to_fate(GlobEnv, E).

%% -- Phase II ---------------------------------------------------------------
%%  Optimize

%% optimizer moved to aeso_fate_opt

%% -- Analysis --

annotate_code(Code) ->
    annotate_code(5, [], Code).

annotate_code(Fuel, LiveTop, Code) ->
    {Code1, LiveIn} = ann_live(LiveTop, Code, []),
    case LiveIn == LiveTop of
        true  -> Code1;
        false when Fuel =< 0 ->
            code_error(liveness_analysis_out_of_fuel);
        false -> annotate_code(Fuel - 1, LiveIn, Code)
    end.

ann_live(_LiveTop, missing, _LiveOut) -> {missing, []};
ann_live(_LiveTop, [], LiveOut)       -> {[], LiveOut};
ann_live(LiveTop, [I | Is], LiveOut) ->
    {Is1, LiveMid} = ann_live(LiveTop, Is, LiveOut),
    {I1, LiveIn}   = ann_live1(LiveTop, I, LiveMid),
    {[I1 | Is1], LiveIn}.

ann_live1(_LiveTop, switch_body, LiveOut) ->
    Ann = #{ live_in => LiveOut, live_out => LiveOut },
    {{i, Ann, switch_body}, LiveOut};
ann_live1(LiveTop, loop, _LiveOut) ->
    Ann = #{ live_in => LiveTop, live_out => [] },
    {{i, Ann, loop}, LiveTop};
ann_live1(LiveTop, {switch, Arg, Type, Alts, Def}, LiveOut) ->
    Read              = [Arg || is_reg(Arg)],
    {Alts1, LiveAlts} = lists:unzip([ ann_live(LiveTop, Alt, LiveOut) || Alt <- Alts ]),
    {Def1,  LiveDef}  = ann_live(LiveTop, Def, LiveOut),
    LiveIn = ordsets:union([Read, LiveDef | LiveAlts]),
    {{switch, Arg, Type, Alts1, Def1}, LiveIn};
ann_live1(_LiveTop, I, LiveOut) ->
    #{ read := Reads0, write := W } = attributes(I),
    Reads   = lists:filter(fun is_reg/1, Reads0),
    %% If we write it here it's not live in (unless we also read it)
    LiveIn = ordsets:union(LiveOut -- [W], Reads),
    Ann = #{ live_in => LiveIn, live_out => LiveOut },
    {{i, Ann, I}, LiveIn}.

is_reg(?a)             -> false;
is_reg(none)           -> false;
is_reg(pc)             -> false;
is_reg({immediate, _}) -> false;
is_reg({arg, _})       -> true;
is_reg({store, _})     -> true;
is_reg({var, _})       -> true.

%% Instruction attributes: reads, writes and purity (pure means no writing to the chain).
attributes(I) ->
    Set  = fun(L) when is_list(L) -> ordsets:from_list(L);
              (X)                 -> ordsets:from_list([X]) end,
    Attr = fun(W, R, P) -> #{read => Set(R), write => W, pure => P}  end,
    Pure   = fun(W, R) -> Attr(W, R, true) end,
    Impure = fun(W, R) -> Attr(W, R, false) end,
    case I of
        loop                                  -> Impure(pc, []);
        switch_body                           -> Pure(none, []);
        'RETURN'                              -> Impure(pc, []);
        {'DBG_LOC', _, _}                     -> Impure(none, []);
        {'DBG_DEF', _, _}                     -> Impure(none, []);
        {'DBG_UNDEF', _, _}                   -> Impure(none, []);
        {'DBG_CONTRACT', _}                   -> Impure(none, []);
        {'RETURNR', A}                        -> Impure(pc, A);
        {'CALL', A}                           -> Impure(?a, [A]);
        {'CALL_R', A, _, B, C, D}             -> Impure(?a, [A, B, C, D]);
        {'CALL_GR', A, _, B, C, D, E}         -> Impure(?a, [A, B, C, D, E]);
        {'CALL_PGR', A, _, B, C, D, E, F}     -> Impure(?a, [A, B, C, D, E, F]);
        {'CALL_T', A}                         -> Impure(pc, [A]);
        {'CALL_VALUE', A}                     -> Pure(A, []);
        {'JUMP', _}                           -> Impure(pc, []);
        {'JUMPIF', A, _}                      -> Impure(pc, A);
        {'SWITCH_V2', A, _, _}                -> Impure(pc, A);
        {'SWITCH_V3', A, _, _, _}             -> Impure(pc, A);
        {'SWITCH_VN', A, _}                   -> Impure(pc, A);
        {'PUSH', A}                           -> Pure(?a, A);
        'DUPA'                                -> Pure(?a, ?a);
        {'DUP', A}                            -> Pure(?a, A);
        {'POP', A}                            -> Pure(A, ?a);
        {'STORE', A, B}                       -> Pure(A, B);
        'INCA'                                -> Pure(?a, ?a);
        {'INC', A}                            -> Pure(A, A);
        'DECA'                                -> Pure(?a, ?a);
        {'DEC', A}                            -> Pure(A, A);
        {'ADD', A, B, C}                      -> Pure(A, [B, C]);
        {'SUB', A, B, C}                      -> Pure(A, [B, C]);
        {'MUL', A, B, C}                      -> Pure(A, [B, C]);
        {'DIV', A, B, C}                      -> Pure(A, [B, C]);
        {'MOD', A, B, C}                      -> Pure(A, [B, C]);
        {'POW', A, B, C}                      -> Pure(A, [B, C]);
        {'MULMOD', A, B, C, D}                -> Pure(A, [B, C, D]);
        {'BAND', A, B, C}                     -> Pure(A, [B, C]);
        {'BOR', A, B, C}                      -> Pure(A, [B, C]);
        {'BXOR', A, B, C}                     -> Pure(A, [B, C]);
        {'BNOT', A, B}                        -> Pure(A, [B]);
        {'BSL', A, B, C}                      -> Pure(A, [B, C]);
        {'BSR', A, B, C}                      -> Pure(A, [B, C]);
        {'LT', A, B, C}                       -> Pure(A, [B, C]);
        {'GT', A, B, C}                       -> Pure(A, [B, C]);
        {'EQ', A, B, C}                       -> Pure(A, [B, C]);
        {'ELT', A, B, C}                      -> Pure(A, [B, C]);
        {'EGT', A, B, C}                      -> Pure(A, [B, C]);
        {'NEQ', A, B, C}                      -> Pure(A, [B, C]);
        {'AND', A, B, C}                      -> Pure(A, [B, C]);
        {'OR', A, B, C}                       -> Pure(A, [B, C]);
        {'NOT', A, B}                         -> Pure(A, B);
        {'TUPLE', A, N}                       -> Pure(A, [?a || N > 0]);
        {'ELEMENT', A, B, C}                  -> Pure(A, [B, C]);
        {'SETELEMENT', A, B, C, D}            -> Pure(A, [B, C, D]);
        {'MAP_EMPTY', A}                      -> Pure(A, []);
        {'MAP_LOOKUP', A, B, C}               -> Pure(A, [B, C]);
        {'MAP_LOOKUPD', A, B, C, D}           -> Pure(A, [B, C, D]);
        {'MAP_UPDATE', A, B, C, D}            -> Pure(A, [B, C, D]);
        {'MAP_DELETE', A, B, C}               -> Pure(A, [B, C]);
        {'MAP_MEMBER', A, B, C}               -> Pure(A, [B, C]);
        {'MAP_FROM_LIST', A, B}               -> Pure(A, B);
        {'MAP_TO_LIST', A, B}                 -> Pure(A, B);
        {'MAP_SIZE', A, B}                    -> Pure(A, B);
        {'NIL', A}                            -> Pure(A, []);
        {'IS_NIL', A, B}                      -> Pure(A, B);
        {'CONS', A, B, C}                     -> Pure(A, [B, C]);
        {'HD', A, B}                          -> Pure(A, B);
        {'TL', A, B}                          -> Pure(A, B);
        {'LENGTH', A, B}                      -> Pure(A, B);
        {'APPEND', A, B, C}                   -> Pure(A, [B, C]);
        {'STR_JOIN', A, B, C}                 -> Pure(A, [B, C]);
        {'INT_TO_STR', A, B}                  -> Pure(A, B);
        {'INT_TO_BYTES', A, B, C}             -> Pure(A, [B, C]);
        {'ADDR_TO_STR', A, B}                 -> Pure(A, B);
        {'STR_REVERSE', A, B}                 -> Pure(A, B);
        {'STR_LENGTH', A, B}                  -> Pure(A, B);
        {'STR_TO_BYTES', A, B}                -> Pure(A, B);
        {'INT_TO_ADDR', A, B}                 -> Pure(A, B);
        {'VARIANT', A, B, C, D}               -> Pure(A, [?a, B, C, D]);
        {'VARIANT_TEST', A, B, C}             -> Pure(A, [B, C]);
        {'VARIANT_ELEMENT', A, B, C}          -> Pure(A, [B, C]);
        'BITS_NONEA'                          -> Pure(?a, []);
        {'BITS_NONE', A}                      -> Pure(A, []);
        'BITS_ALLA'                           -> Pure(?a, []);
        {'BITS_ALL', A}                       -> Pure(A, []);
        {'BITS_ALL_N', A, B}                  -> Pure(A, B);
        {'BITS_SET', A, B, C}                 -> Pure(A, [B, C]);
        {'BITS_CLEAR', A, B, C}               -> Pure(A, [B, C]);
        {'BITS_TEST', A, B, C}                -> Pure(A, [B, C]);
        {'BITS_SUM', A, B}                    -> Pure(A, B);
        {'BITS_OR', A, B, C}                  -> Pure(A, [B, C]);
        {'BITS_AND', A, B, C}                 -> Pure(A, [B, C]);
        {'BITS_DIFF', A, B, C}                -> Pure(A, [B, C]);
        {'SHA3', A, B}                        -> Pure(A, [B]);
        {'SHA256', A, B}                      -> Pure(A, [B]);
        {'BLAKE2B', A, B}                     -> Pure(A, [B]);
        {'POSEIDON', A, B, C}                 -> Pure(A, [B, C]);
        {'VERIFY_SIG', A, B, C, D}            -> Pure(A, [B, C, D]);
        {'VERIFY_SIG_SECP256K1', A, B, C, D}  -> Pure(A, [B, C, D]);
        {'ECVERIFY_SECP256K1', A, B, C, D}    -> Pure(A, [B, C, D]);
        {'ECRECOVER_SECP256K1', A, B, C}      -> Pure(A, [B, C]);
        {'CONTRACT_TO_ADDRESS', A, B}         -> Pure(A, [B]);
        {'ADDRESS_TO_CONTRACT', A, B}         -> Pure(A, [B]);
        {'ADDRESS_TO_BYTES', A, B}            -> Pure(A, [B]);
        {'AUTH_TX_HASH', A}                   -> Pure(A, []);
        {'AUTH_TX', A}                        -> Pure(A, []);
        {'BYTES_TO_INT', A, B}                -> Pure(A, [B]);
        {'BYTES_TO_STR', A, B}                -> Pure(A, [B]);
        {'BYTES_CONCAT', A, B, C}             -> Pure(A, [B, C]);
        {'BYTES_SPLIT', A, B, C}              -> Pure(A, [B, C]);
        {'BYTES_SPLIT_ANY', A, B, C}          -> Pure(A, [B, C]);
        {'BYTES_SIZE', A, B}                  -> Pure(A, B);
        {'BYTES_TO_FIXED_SIZE', A, B, C}      -> Pure(A, [B, C]);
        {'ORACLE_CHECK', A, B, C, D}          -> Pure(A, [B, C, D]);
        {'ORACLE_CHECK_QUERY', A, B, C, D, E} -> Pure(A, [B, C, D, E]);
        {'IS_ORACLE', A, B}                   -> Pure(A, [B]);
        {'IS_CONTRACT', A, B}                 -> Pure(A, [B]);
        {'IS_PAYABLE', A, B}                  -> Pure(A, [B]);
        {'CREATOR', A}                        -> Pure(A, []);
        {'ADDRESS', A}                        -> Pure(A, []);
        {'BALANCE', A}                        -> Pure(A, []);
        {'BALANCE_OTHER', A, B}               -> Pure(A, [B]);
        {'ORIGIN', A}                         -> Pure(A, []);
        {'CALLER', A}                         -> Pure(A, []);
        {'GASPRICE', A}                       -> Pure(A, []);
        {'FEE', A}                            -> Pure(A, []);
        {'BLOCKHASH', A, B}                   -> Pure(A, [B]);
        {'BENEFICIARY', A}                    -> Pure(A, []);
        {'TIMESTAMP', A}                      -> Pure(A, []);
        {'GENERATION', A}                     -> Pure(A, []);
        {'MICROBLOCK', A}                     -> Pure(A, []);
        {'DIFFICULTY', A}                     -> Pure(A, []);
        {'GASLIMIT', A}                       -> Pure(A, []);
        {'NETWORK_ID', A}                     -> Pure(A, []);
        {'GAS', A}                            -> Pure(A, []);
        {'LOG0', A}                           -> Impure(none, [A]);
        {'LOG1', A, B}                        -> Impure(none, [A, B]);
        {'LOG2', A, B, C}                     -> Impure(none, [A, B, C]);
        {'LOG3', A, B, C, D}                  -> Impure(none, [A, B, C, D]);
        {'LOG4', A, B, C, D, E}               -> Impure(none, [A, B, C, D, E]);
        'DEACTIVATE'                          -> Impure(none, []);
        {'SPEND', A, B}                       -> Impure(none, [A, B]);
        {'ORACLE_REGISTER', A, B, C, D, E, F, G} -> Impure(A, [B, C, D, E, F, G]);
        {'ORACLE_QUERY', A, B, C, D, E, F, G, H} -> Impure(A, [B, C, D, E, F, G, H]);
        {'ORACLE_RESPOND', A, B, C, D, E, F}  -> Impure(none, [A, B, C, D, E, F]);
        {'ORACLE_EXTEND', A, B, C}            -> Impure(none, [A, B, C]);
        {'ORACLE_GET_ANSWER', A, B, C, D, E}  -> Pure(A, [B, C, D, E]);
        {'ORACLE_GET_QUESTION', A, B, C, D, E}-> Pure(A, [B, C, D, E]);
        {'ORACLE_QUERY_FEE', A, B}            -> Pure(A, [B]);
        {'ORACLE_EXPIRY', A, B}               -> Impure(A, [B]);
        {'AENS_RESOLVE', A, B, C, D}          -> Impure(A, [B, C, D]);
        {'AENS_PRECLAIM', A, B, C}            -> Impure(none, [A, B, C]);
        {'AENS_CLAIM', A, B, C, D, E}         -> Impure(none, [A, B, C, D, E]);
        {'AENS_UPDATE', A, B, C, D, E, F}     -> Impure(none, [A, B, C, D, E, F]);
        {'AENS_TRANSFER', A, B, C, D}         -> Impure(none, [A, B, C, D]);
        {'AENS_REVOKE', A, B, C}              -> Impure(none, [A, B, C]);
        {'AENS_LOOKUP', A, B}                 -> Impure(A, [B]);
        {'BLS12_381_G1_NEG', A, B}            -> Pure(A, [B]);
        {'BLS12_381_G1_NORM', A, B}           -> Pure(A, [B]);
        {'BLS12_381_G1_VALID', A, B}          -> Pure(A, [B]);
        {'BLS12_381_G1_IS_ZERO', A, B}        -> Pure(A, [B]);
        {'BLS12_381_G1_ADD', A, B, C}         -> Pure(A, [B, C]);
        {'BLS12_381_G1_MUL', A, B, C}         -> Pure(A, [B, C]);
        {'BLS12_381_G2_NEG', A, B}            -> Pure(A, [B]);
        {'BLS12_381_G2_NORM', A, B}           -> Pure(A, [B]);
        {'BLS12_381_G2_VALID', A, B}          -> Pure(A, [B]);
        {'BLS12_381_G2_IS_ZERO', A, B}        -> Pure(A, [B]);
        {'BLS12_381_G2_ADD', A, B, C}         -> Pure(A, [B, C]);
        {'BLS12_381_G2_MUL', A, B, C}         -> Pure(A, [B, C]);
        {'BLS12_381_GT_INV', A, B}            -> Pure(A, [B]);
        {'BLS12_381_GT_ADD', A, B, C}         -> Pure(A, [B, C]);
        {'BLS12_381_GT_MUL', A, B, C}         -> Pure(A, [B, C]);
        {'BLS12_381_GT_POW', A, B, C}         -> Pure(A, [B, C]);
        {'BLS12_381_GT_IS_ONE', A, B}         -> Pure(A, [B]);
        {'BLS12_381_PAIRING', A, B, C}        -> Pure(A, [B, C]);
        {'BLS12_381_MILLER_LOOP', A, B, C}    -> Pure(A, [B, C]);
        {'BLS12_381_FINAL_EXP', A, B}         -> Pure(A, [B]);
        {'BLS12_381_INT_TO_FR', A, B}         -> Pure(A, [B]);
        {'BLS12_381_INT_TO_FP', A, B}         -> Pure(A, [B]);
        {'BLS12_381_FR_TO_INT', A, B}         -> Pure(A, [B]);
        {'BLS12_381_FP_TO_INT', A, B}         -> Pure(A, [B]);
        {'STR_TO_LIST', A, B}                 -> Pure(A, [B]);
        {'STR_FROM_LIST', A, B}               -> Pure(A, [B]);
        {'STR_TO_UPPER', A, B}                -> Pure(A, [B]);
        {'STR_TO_LOWER', A, B}                -> Pure(A, [B]);
        {'CHAR_TO_INT', A, B}                 -> Pure(A, [B]);
        {'CHAR_FROM_INT', A, B}               -> Pure(A, [B]);
        {'CREATE', A, B, C}                   -> Impure(?a, [A, B, C]);
        {'CLONE', A, B, C, D}                 -> Impure(?a, [A, B, C, D]);
        {'CLONE_G', A, B, C, D, E}            -> Impure(?a, [A, B, C, D, E]);
        {'BYTECODE_HASH', A, B}               -> Impure(A, [B]);
        {'ABORT', A}                          -> Impure(pc, A);
        {'EXIT', A}                           -> Impure(pc, A);
        'NOP'                                 -> Pure(none, [])
    end.

var_writes({i, _, I}) -> var_writes(I);
var_writes(I) ->
    #{ write := W } = attributes(I),
    case W of
        {var, _}   -> [W];
        {arg, _}   -> [W];
        {store, _} -> [W];
        {stack, _} -> [];
        none       -> [];
        pc         -> []
    end.

-spec independent(sinstr_a(), sinstr_a()) -> boolean().
%% independent({switch, _, _, _, _}, _) -> false;       %% Commented due to Dialyzer whinging
independent(_, {switch, _, _, _, _}) -> false;
independent({i, _, I}, {i, _, J}) ->
    #{ write := WI, read := RI, pure := PureI } = attributes(I),
    #{ write := WJ, read := RJ, pure := PureJ } = attributes(J),

    StackI = lists:member(?a, [WI | RI]),
    StackJ = lists:member(?a, [WJ | RJ]),

    ReadStoreI = [] /= [ x || {store, _} <- RI ],
    ReadStoreJ = [] /= [ x || {store, _} <- RJ ],

    if  WI == pc; WJ == pc       -> false;  %% no jumps
        not (PureI or PureJ)     -> false;  %% at least one is pure
        StackI and StackJ        -> false;  %% cannot both use the stack
        WI == WJ                 -> false;  %% cannot write to the same register
        ReadStoreI and not PureJ -> false;  %% can't read store/state if other is impure
        ReadStoreJ and not PureI -> false;  %% can't read store/state if other is impure
        true                     ->
            %% and cannot write to each other's inputs
            not lists:member(WI, RJ) andalso
            not lists:member(WJ, RI)
    end.

merge_ann(#{ live_in := LiveIn }, #{ live_out := LiveOut }) ->
    #{ live_in => LiveIn, live_out => LiveOut }.

%% Swap two instructions. Precondition: the instructions are independent/2.
swap_instrs({i, #{ live_in := Live1 }, I}, {i, #{ live_in := Live2, live_out := Live3 }, J}) ->
    %% Since I and J are independent the J can't read or write anything in
    %% that I writes.
    WritesI = ordsets:subtract(Live2, Live1),
    %% Any final reads by J, that I does not read should be removed from Live2.
    #{ read := ReadsI } = attributes(I),
    ReadsJ  = ordsets:subtract(Live2, ordsets:union(Live3, ReadsI)),
    Live2_  = ordsets:subtract(ordsets:union([Live1, Live2, Live3]), ordsets:union(WritesI, ReadsJ)),
    {{i, #{ live_in => Live1,  live_out => Live2_ }, J},
     {i, #{ live_in => Live2_, live_out => Live3  }, I}}.

live_in({store, _}, _) -> true;
live_in(R, #{ live_in  := LiveIn  }) -> ordsets:is_element(R, LiveIn);
live_in(R, {i, Ann, _}) -> live_in(R, Ann);
live_in(R, [I = {i, _, _} | _]) -> live_in(R, I);
live_in(R, [{switch, A, _, Alts, Def} | _]) ->
    R == A orelse lists:any(fun(Code) -> live_in(R, Code) end, [Def | Alts]);
live_in(_, missing) -> false;
live_in(_, []) -> false.

live_out({store, _}, _) -> true;
live_out(R, #{ live_out := LiveOut }) -> ordsets:is_element(R, LiveOut).

%% -- Optimizations --

simplify([], _) -> [];
simplify(missing, _) -> missing;
simplify([I | Code], Options) ->
    simpl_top(simpl_s(I, Options), simplify(Code, Options), Options).

simpl_s({switch, Arg, Type, Alts, Def}, Options) ->
    {switch, Arg, Type, [simplify(A, Options) || A <- Alts], simplify(Def, Options)};
simpl_s(I, _) -> I.

%% Safe-guard against loops in the rewriting. Shouldn't happen so throw an
%% error if we run out.
-define(SIMPL_FUEL, 5000).

simpl_top(I, Code, Options) ->
    simpl_top(?SIMPL_FUEL, I, Code, Options).

simpl_top(0, I, Code, _Options) ->
    code_error({optimizer_out_of_fuel, I, Code});
simpl_top(Fuel, I, Code, Options) ->
    Rules = [R || R = {Rule, _} <- rules(), proplists:get_value(Rule, Options, true)],
    apply_rules(Fuel, Rules, I, Code, Options).

apply_rules(Fuel, Rules, I, Code, Options) ->
    Cons = fun(X, Xs) -> simpl_top(Fuel - 1, X, Xs, Options) end,
    case apply_rules_once(Rules, I, Code) of
        false -> [I | Code];
        {RName, New, Rest} ->
            case is_debug(opt_rules, Options) of
                true ->
                    {OldCode, NewCode} = drop_common_suffix([I | Code], New ++ Rest),
                    ?debug(opt_rules, Options, "  Applied ~p\n", [RName]);
                false -> ok
            end,
            lists:foldr(Cons, Rest, New)
    end.

apply_rules_once([], _, _) ->
    false;
apply_rules_once([{RName, Rule} | Rules], I, Code) ->
    case Rule(I, Code) of
        false       -> apply_rules_once(Rules, I, Code);
        {New, Rest} -> {RName, New, Rest}
    end.

-define(RULE(Name), {Name, fun Name/2}).

merge_rules() ->
    [?RULE(optimize_push_consume),
     ?RULE(optimize_one_shot_var),
     ?RULE(optimize_write_to_dead_var),
     ?RULE(optimize_inline_switch_target)
    ].

rules() ->
    merge_rules() ++
    [?RULE(optimize_swap_push),
     ?RULE(optimize_swap_pop),
     ?RULE(optimize_swap_write),
     ?RULE(optimize_constant_propagation),
     ?RULE(optimize_prune_impossible_branches),
     ?RULE(optimize_single_successful_branch),
     ?RULE(optimize_inline_store),
     ?RULE(optimize_float_switch_body)
    ].

%% Removing pushes that are immediately consumed.
optimize_push_consume({i, Ann1, {'STORE', ?a, A}}, Code) ->
    inline_push(Ann1, A, 0, Code, []);
%% Writing directly to memory instead of going through the accumulator.
optimize_push_consume({i, Ann1, I}, [{i, Ann2, {'STORE', R, ?a}} | Code]) ->
    IsPush =
        case op_view(I) of
            {_, ?a, _} -> true;
            _          -> false
        end orelse
        case I of
            {'VARIANT', ?a, _, _, _} -> true;
            _                        -> false
        end,
    if IsPush -> {[{i, merge_ann(Ann1, Ann2), setelement(2, I, R)}], Code};
       true   -> false end;
optimize_push_consume(_, _) -> false.

inline_push(Ann, Arg, Stack, [{i, _, switch_body} = AI | Code], Acc) ->
    {AI1, {i, Ann1, _}} = swap_instrs({i, Ann, {'STORE', ?a, Arg}}, AI),
    inline_push(Ann1, Arg, Stack, Code, [AI1 | Acc]);
inline_push(Ann1, Arg, Stack, [{i, Ann2, I} = AI | Code], Acc) ->
    case op_view(I) of
        {Op, R, As} ->
            Consumes = length([ ?a || ?a <- As ]),
            Produces = length([ ?a || ?a == R  ]),
            case Consumes > Stack of
                true ->
                    {As0, As1} = split_stack_arg(Stack, As),
                    Acc1 = [{i, merge_ann(Ann1, Ann2), from_op_view(Op, R, As0 ++ [Arg] ++ As1)} | Acc],
                    {lists:reverse(Acc1), Code};
                false when Arg /= R ->
                    {AI1, {i, Ann1b, _}} = swap_instrs({i, Ann1, {'STORE', ?a, Arg}}, AI),
                    inline_push(Ann1b, Arg, Stack + Produces - Consumes, Code, [AI1 | Acc]);
                false -> false
            end;
        _ -> false
    end;
inline_push(_, _, _, _, _) -> false.

split_stack_arg(N, As) -> split_stack_arg(N, As, []).
split_stack_arg(0, [?a | As], Acc) ->
    {lists:reverse(Acc), As};
split_stack_arg(N, [A | As], Acc) ->
    N1 = if A == ?a -> N - 1;
            true    -> N end,
    split_stack_arg(N1, As, [A | Acc]).

%% Move PUSHes past non-stack instructions.
optimize_swap_push(Push = {i, _, PushI}, [I | Code]) ->
    case op_view(PushI) of
        {_, ?a, _} ->
            case independent(Push, I) of
                true ->
                    {I1, Push1} = swap_instrs(Push, I),
                    {[I1, Push1], Code};
                false -> false
            end;
        _ -> false
    end;
optimize_swap_push(_, _) -> false.

%% Move non-stack instruction past POPs.
optimize_swap_pop(IA = {i, _, I}, [JA = {i, _, J} | Code]) ->
    case independent(IA, JA) of
        true ->
            case {op_view(I), op_view(J)} of
                {false, _} -> false;
                {_, false} -> false;
                {{_, IR, IAs}, {_, RJ, JAs}} ->
                    NonStackI = not lists:member(?a, [IR | IAs]),
                    %% RJ /= ?a to not conflict with optimize_swap_push
                    PopJ      = RJ /= ?a andalso lists:member(?a, JAs),
                    case NonStackI andalso PopJ of
                        false -> false;
                        true  ->
                            {JA1, IA1} = swap_instrs(IA, JA),
                            {[JA1, IA1], Code}
                    end
            end;
        false -> false
    end;
optimize_swap_pop(_, _) -> false.

%% Match up writes to variables with instructions further down.
optimize_swap_write(I = {i, _, _}, [J | Code]) ->
    case {var_writes(I), independent(I, J)} of
        {[_], true} ->
            {J1, I1} = swap_instrs(I, J),
            optimize_swap_write([J1], I1, Code);
        _ -> false
    end;
optimize_swap_write(_, _) -> false.

optimize_swap_write(Pre, I, [{i, _, switch_body} = J | Code]) ->
    {J1, I1} = swap_instrs(I, J),
    optimize_swap_write([J1 | Pre], I1, Code);
optimize_swap_write(Pre, I, Code0 = [J | Code]) ->
    case apply_rules_once(merge_rules(), I, Code0) of
        {_Rule, New, Rest} ->
            {lists:reverse(Pre) ++ New, Rest};
        false ->
            case independent(I, J) of
                false -> false;
                true  ->
                    {J1, I1} = swap_instrs(I, J),
                    optimize_swap_write([J1 | Pre], I1, Code)
            end
    end;
optimize_swap_write(_, _, _) -> false.

%% Precompute instructions with known values
optimize_constant_propagation(Cons = {i, Ann1, {'CONS', R, X, Xs}}, [{i, Ann, {'IS_NIL', S, R}} | Code]) ->
    Store = {i, Ann, {'STORE', S, ?i(false)}},
    Cons1 = case R of
                ?a -> {i, Ann1, {'CONS', ?void, X, Xs}};
                _  -> Cons
            end,
    {[Cons1, Store], Code};
optimize_constant_propagation(Nil = {i, Ann1, {'NIL', R}}, [{i, Ann, {'IS_NIL', S, R}} | Code]) ->
    Store = {i, Ann, {'STORE', S, ?i(true)}},
    Nil1 = case R of
               ?a -> {i, Ann1, {'NIL', ?void}};
               _  -> Nil
           end,
    {[Nil1, Store], Code};
optimize_constant_propagation({i, Ann, I}, Code) ->
    case op_view(I) of
        false -> false;
        {Op, R, As} ->
            Vs = [V || ?i(V) <- As],
            case length(Vs) == length(As) of
                false -> false;
                true  ->
                    case eval_op(Op, Vs) of
                        no_eval -> false;
                        V       -> {[{i, Ann, {'STORE', R, ?i(V)}}], Code}
                    end
            end
    end;
optimize_constant_propagation(_, _) -> false.

eval_op('ADD', [X, Y]) when is_integer(X), is_integer(Y) -> X + Y;
eval_op('SUB', [X, Y]) when is_integer(X), is_integer(Y) -> X - Y;
eval_op('MUL', [X, Y]) when is_integer(X), is_integer(Y) -> X * Y;
eval_op('DIV', [X, Y]) when is_integer(X), is_integer(Y), Y /= 0 -> X div Y;
eval_op('MOD', [X, Y]) when is_integer(X), is_integer(Y), Y /= 0 -> X rem Y;
eval_op('POW', [_, _])  -> no_eval;
eval_op('LT', [X, Y])   -> X < Y;
eval_op('GT', [X, Y])   -> X > Y;
eval_op('EQ', [X, Y])   -> X =:= Y;
eval_op('ELT', [X, Y])  -> X =< Y;
eval_op('EGT', [X, Y])  -> X >= Y;
eval_op('NEQ', [X, Y])  -> X =/= Y;
eval_op('NOT', [true])  -> false;
eval_op('NOT', [false]) -> true;
eval_op(_, _)           -> no_eval.   %% TODO: bits?

%% Prune impossible branches from switches
optimize_prune_impossible_branches({switch, ?i(V), Type, Alts, missing}, Code) ->
    case pick_branch(Type, V, Alts) of
        false -> false;
        Alt   -> {Alt, Code}
    end;
optimize_prune_impossible_branches({switch, ?i(V), boolean, [False, True] = Alts, Def}, Code) when V == true; V == false ->
    Alts1 = [if V -> missing; true -> False   end,
             if V -> True;    true -> missing end],
    case Alts == Alts1 of
        true  -> false;
        false ->
            case Alts1 of
                [missing, missing] -> {Def, Code};
                _                  -> {[{switch, ?i(V), boolean, Alts1, Def}], Code}
            end
    end;
optimize_prune_impossible_branches(Variant = {i, _, {'VARIANT', R, ?i(_), ?i(Tag), ?i(_)}},
                            [{switch, R, Type = {variant, _}, Alts, missing} | Code]) when is_integer(Tag) ->
    case {R, lists:nth(Tag + 1, Alts)} of
        {_, missing} ->
            Alts1 = [missing || _ <- Alts],
            case Alts == Alts1 of
                true -> false;
                false -> {[Variant, {switch, R, Type, Alts1, missing}], Code}
            end;
        {?a, Alt} -> {Alt, Code};
        {_,  Alt} ->
            case live_in(R, Alt) of
                true  -> {[Variant | Alt], Code};
                false -> {Alt, Code}
            end
    end;
optimize_prune_impossible_branches(_, _) -> false.

pick_branch(boolean, V, [False, True]) when V == true; V == false ->
    Alt = if V -> True; true -> False end,
    case Alt of
        missing -> false;
        _       -> Alt
    end;
pick_branch(_Type, _V, _Alts) ->
    false.

%% If there's a single branch that doesn't abort we can push the code for that
%% out of the switch.
optimize_single_successful_branch({switch, R, Type, Alts, Def}, Code) ->
    case push_code_out_of_switch([Def | Alts]) of
        {_, none} -> false;
        {_, many} -> false;
        {_, [{i, _, switch_body}]} -> false;
        {[Def1 | Alts1], PushedOut} ->
            {[{switch, R, Type, Alts1, Def1} | PushedOut], Code}
    end;
optimize_single_successful_branch(_, _) -> false.

push_code_out_of_switch([]) -> {[], none};
push_code_out_of_switch([Alt | Alts]) ->
    {Alt1, PushedAlt}   = push_code_out_of_alt(Alt),
    {Alts1, PushedAlts} = push_code_out_of_switch(Alts),
    Pushed =
        case {PushedAlt, PushedAlts} of
            {none, _} -> PushedAlts;
            {_, none} -> PushedAlt;
            _         -> many
        end,
    {[Alt1 | Alts1], Pushed}.

push_code_out_of_alt(missing) -> {missing, none};
push_code_out_of_alt([Body = {i, _, switch_body} | Code]) ->
    case does_abort(Code) of
        true  -> {[Body | Code], none};
        false -> {[Body], [Body | Code]}  %% Duplicate the switch_body, in case we apply this in the middle of a switch
    end;
push_code_out_of_alt([{switch, R, Type, Alts, Def}]) ->
    {[Def1 | Alts1], Pushed} = push_code_out_of_switch([Def | Alts]),
    {[{switch, R, Type, Alts1, Def1}], Pushed};
push_code_out_of_alt(Code) ->
    {Code, many}. %% Conservative

does_abort([I | Code]) ->
    does_abort(I) orelse does_abort(Code);
does_abort({i, _, {'ABORT', _}}) -> true;
does_abort({i, _, {'EXIT', _}}) -> true;
does_abort(missing) -> true;
does_abort({switch, _, _, Alts, Def}) ->
    lists:all(fun does_abort/1, [Def | Alts]);
does_abort(_) -> false.

%% STORE R A, SWITCH R --> SWITCH A
optimize_inline_switch_target({i, Ann, {'STORE', R, A}}, [{switch, R, Type, Alts, Def} | Code]) ->
    Ann1   =
        case is_reg(A) of
            true  -> Ann#{ live_out := ordsets:add_element(A, maps:get(live_out, Ann)) };
            false -> Ann
        end,
    Store  = {i, Ann1, {'STORE', R, A}},
    Switch = {switch, A, Type, Alts, Def},
    case R of
        A        -> false;
        ?a       -> {[Switch], Code};
        {var, _} ->
            case lists:any(fun(Alt) -> live_in(R, Alt) end, [Def | Alts]) of
                false             -> {[Switch], Code};
                true when A /= ?a -> {[Store, Switch], Code};
                true              -> false
            end;
        _        -> false %% impossible
    end;
optimize_inline_switch_target(_, _) -> false.

%% Float switch-body to closest switch
optimize_float_switch_body(I = {i, _, _}, [J = {i, _, switch_body} | Code]) ->
    {J1, I1} = swap_instrs(I, J),
    {[], [J1, I1 | Code]};
optimize_float_switch_body(_, _) -> false.

%% Inline stores
optimize_inline_store({i, _, {'STORE', R, R}}, Code) ->
    {[], Code};
optimize_inline_store(I = {i, _, {'STORE', R = {var, _}, A}}, Code) ->
    %% Not when A is var unless updating the annotations properly.
    Inline = case A of
                 {arg, _}   -> true;
                 ?i(_)      -> true;
                 {store, _} -> true;
                 _          -> false
             end,
    if Inline -> optimize_inline_store([I], false, R, A, Code);
       true   -> false end;
optimize_inline_store(_, _) -> false.

optimize_inline_store(Acc, Progress, R, A, [I = {i, _, switch_body} | Code]) ->
    optimize_inline_store([I | Acc], Progress, R, A, Code);
optimize_inline_store(Acc, Progress, R, A, [{i, Ann, I} | Code]) ->
    #{ write := W } = attributes(I),
    Inl = fun(X) when X == R -> A; (X) -> X end,
    case live_in(R, Ann) of
        false -> false;  %% No more reads of R
        true  ->
            {I1, Progress1} =
                case op_view(I) of
                    {Op, S, As} ->
                        case lists:member(R, As) of
                            true  -> {from_op_view(Op, S, lists:map(Inl, As)), true};
                            false -> {I, Progress}
                        end;
                    _ -> {I, Progress}
                end,
            Acc1 = [{i, Ann, I1} | Acc],
            %% Stop if write to R or A
            case lists:member(W, [R, A]) of
                true when Progress1 -> {lists:reverse(Acc1), Code};
                true                -> false;
                false               -> optimize_inline_store(Acc1, Progress1, R, A, Code)
            end
    end;
optimize_inline_store(Acc, true, _, _, Code) -> {lists:reverse(Acc), Code};
optimize_inline_store(_, false, _, _, _) -> false.

%% Shortcut write followed by final read
optimize_one_shot_var({i, Ann1, I}, [{i, Ann2, J} | Code]) ->
    case op_view(I) of
        {Op, R = {var, _}, As} ->
            Copy = case J of
                       {'STORE', S, R} -> {write_to, S};
                       _               -> false
                   end,
            case {live_out(R, Ann2), Copy} of
                {false, {write_to, X}} ->
                    {[{i, merge_ann(Ann1, Ann2), from_op_view(Op, X, As)}], Code};
                _ -> false
            end;
        _ -> false
    end;
optimize_one_shot_var(_, _) -> false.

%% Remove writes to dead variables
optimize_write_to_dead_var({i, _, {'STORE', ?void, ?a}}, _) -> false; %% Avoid looping
optimize_write_to_dead_var({i, Ann, I}, Code) ->
    #{ pure := Pure } = attributes(I),
    case op_view(I) of
        {_Op, R, As} when R /= ?a, Pure ->
            case live_out(R, Ann) of
                false ->
                    %% Subtle: we still have to pop the stack if any of the arguments
                    %% came from there.
                    {[{i, Ann, {'STORE', ?void, ?a}} || X <- As, X == ?a], Code};
                true -> false
            end;
        _ -> false
    end;
optimize_write_to_dead_var(_, _) -> false.

op_view({'ABORT', R}) -> {'ABORT', none, [R]};
op_view({'EXIT', R}) -> {'EXIT', none, [R]};
op_view(T) when is_tuple(T) ->
    [Op, R | As] = tuple_to_list(T),
    CheckReads = fun(Rs, X) -> case [] == Rs -- [dst, src] of true -> X; false -> false end end,
    case attributes(list_to_tuple([Op, dst | [src || _ <- As]])) of
        #{ write := dst, read := Rs  } -> CheckReads(Rs, {Op, R, As});
        #{ write := none, read := Rs } -> CheckReads(Rs, {Op, none, [R | As]});
        _                              -> false
    end;
op_view(_) -> false.

from_op_view(Op, none, As) -> list_to_tuple([Op | As]);
from_op_view(Op, R, As) -> list_to_tuple([Op, R | As]).

%% Desugar and specialize and remove annotations
%% desugar/unannotate moved to aeso_fate_opt

%% Phase III moved to aeso_fate_blocks

%% -- Helpers ----------------------------------------------------------------

with_ixs(Xs) ->
    lists:zip(lists:seq(0, length(Xs) - 1), Xs).

drop_common_suffix(Xs, Ys) ->
    drop_common_suffix_r(lists:reverse(Xs), lists:reverse(Ys)).

drop_common_suffix_r([X | Xs], [X | Ys]) ->
    drop_common_suffix_r(Xs, Ys);
drop_common_suffix_r(Xs, Ys) ->
    {lists:reverse(Xs), lists:reverse(Ys)}.
