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

-export([compile/2]).

%% -- Preamble ---------------------------------------------------------------

-type scode()  :: [sinstr()].
-type sinstr() :: {switch, arg(), stype(), [maybe_scode()], maybe_scode()}  %% last arg is catch-all
                | switch_body
                | tuple().    %% FATE instruction

-type arg() :: aeb_fate_code:fate_arg().

%% Annotated scode
-type scode_a()  :: [sinstr_a()].
-type sinstr_a() :: {switch, arg(), stype(), [maybe_scode_a()], maybe_scode_a()}  %% last arg is catch-all
                  | switch_body
                  | {i, ann(), tuple()}.    %% FATE instruction

-type ann() :: #{ live_in := vars(), live_out := vars() }.
-type var() :: {var, integer()}.
-type vars() :: ordsets:ordset(var()).

-type stype()         :: tuple | boolean | {variant, [non_neg_integer()]}.
-type maybe_scode()   :: missing | scode().
-type maybe_scode_a() :: missing | scode_a().

-define(TODO(What), error({todo, ?FILE, ?LINE, ?FUNCTION_NAME, What})).

-define(i(X), {immediate, X}).
-define(a, {stack, 0}).
-define(s, {var, -1}).  %% TODO: until we have state support in FATE

-define(IsOp(Op), (
     Op =:= 'STORE'           orelse
     Op =:= 'ADD'             orelse
     Op =:= 'SUB'             orelse
     Op =:= 'MUL'             orelse
     Op =:= 'DIV'             orelse
     Op =:= 'MOD'             orelse
     Op =:= 'POW'             orelse
     Op =:= 'LT'              orelse
     Op =:= 'GT'              orelse
     Op =:= 'EQ'              orelse
     Op =:= 'ELT'             orelse
     Op =:= 'EGT'             orelse
     Op =:= 'NEQ'             orelse
     Op =:= 'AND'             orelse
     Op =:= 'OR'              orelse
     Op =:= 'NOT'             orelse
     Op =:= 'ELEMENT'         orelse
     Op =:= 'MAP_EMPTY'       orelse
     Op =:= 'MAP_LOOKUP'      orelse
     Op =:= 'MAP_LOOKUPD'     orelse
     Op =:= 'MAP_UPDATE'      orelse
     Op =:= 'MAP_DELETE'      orelse
     Op =:= 'MAP_MEMBER'      orelse
     Op =:= 'MAP_FROM_LIST'   orelse
     Op =:= 'NIL'             orelse
     Op =:= 'IS_NIL'          orelse
     Op =:= 'CONS'            orelse
     Op =:= 'HD'              orelse
     Op =:= 'TL'              orelse
     Op =:= 'LENGTH'          orelse
     Op =:= 'APPEND'          orelse
     Op =:= 'STR_JOIN'        orelse
     Op =:= 'INT_TO_STR'      orelse
     Op =:= 'ADDR_TO_STR'     orelse
     Op =:= 'STR_REVERSE'     orelse
     Op =:= 'INT_TO_ADDR'     orelse
     Op =:= 'VARIANT_TEST'    orelse
     Op =:= 'VARIANT_ELEMENT' orelse
     Op =:= 'BITS_NONE'       orelse
     Op =:= 'BITS_ALL'        orelse
     Op =:= 'BITS_ALL_N'      orelse
     Op =:= 'BITS_SET'        orelse
     Op =:= 'BITS_CLEAR'      orelse
     Op =:= 'BITS_TEST'       orelse
     Op =:= 'BITS_SUM'        orelse
     Op =:= 'BITS_OR'         orelse
     Op =:= 'BITS_AND'        orelse
     Op =:= 'BITS_DIFF'       orelse
     false)).

-record(env, { contract, vars = [], locals = [], tailpos = true }).

%% -- Debugging --------------------------------------------------------------

debug(Tag, Options, Fmt, Args) ->
    Tags = proplists:get_value(debug, Options, []),
    case Tags == all orelse lists:member(Tag, Tags) orelse Tag == any andalso Tags /= [] of
        true  -> io:format(Fmt, Args);
        false -> ok
    end.

%% -- Main -------------------------------------------------------------------

%% @doc Main entry point.
compile(FCode, Options) ->
    #{ contract_name := ContractName,
       state_type    := _StateType,
       functions     := Functions } = FCode,
    SFuns  = functions_to_scode(ContractName, Functions, Options),
    SFuns1 = optimize_scode(SFuns, Options),
    BBFuns = to_basic_blocks(SFuns1, Options),
    FateCode = #{ functions   => BBFuns,
                  symbols     => #{},
                  annotations => #{} },
    debug(compile, Options, "~s\n", [aeb_fate_asm:pp(FateCode)]),
    FateCode.

make_function_name(init)               -> <<"init">>;
make_function_name({entrypoint, Name}) -> Name;
make_function_name({local_fun, Xs})    -> list_to_binary("." ++ string:join(Xs, ".")).

functions_to_scode(ContractName, Functions, Options) ->
    FunNames = maps:keys(Functions),
    maps:from_list(
        [ {make_function_name(Name), function_to_scode(ContractName, FunNames, Name, Args, Body, Type, Options)}
        || {Name, #{args   := Args,
                    body   := Body,
                    return := Type}} <- maps:to_list(Functions),
           Name /= init ]).  %% TODO: skip init for now

function_to_scode(ContractName, Functions, _Name, Args, Body, ResType, _Options) ->
    ArgTypes = [ type_to_scode(T) || {_, T} <- Args ],
    SCode    = to_scode(init_env(ContractName, Functions, Args), Body),
    {{ArgTypes, type_to_scode(ResType)}, SCode}.

type_to_scode({variant, Cons}) -> {variant, lists:map(fun length/1, Cons)};
type_to_scode({list, Type})    -> {list, type_to_scode(Type)};
type_to_scode({tuple, Types})  -> {tuple, lists:map(fun type_to_scode/1, Types)};
type_to_scode({map, Key, Val}) -> {map, type_to_scode(Key), type_to_scode(Val)};
type_to_scode({function, _Args, _Res}) -> {tuple, [string, any]};
type_to_scode(T)               -> T.

%% -- Phase I ----------------------------------------------------------------
%%  Icode to structured assembly

%% -- Environment functions --

init_env(ContractName, FunNames, Args) ->
    #env{ vars      = [ {X, {arg, I}} || {I, {X, _}} <- with_ixs(Args) ],
          contract  = ContractName,
          locals    = FunNames,
          tailpos   = true }.

next_var(#env{ vars = Vars }) ->
    1 + lists:max([-1 | [J || {_, {var, J}} <- Vars]]).

bind_var(Name, Var, Env = #env{ vars = Vars }) ->
    Env#env{ vars = [{Name, Var} | Vars] }.

bind_local(Name, Env) ->
    I = next_var(Env),
    {I, bind_var(Name, {var, I}, Env)}.

notail(Env) -> Env#env{ tailpos = false }.

code_error(Err) -> error(Err).

lookup_var(#env{vars = Vars}, X) ->
    case lists:keyfind(X, 1, Vars) of
        {_, Var} -> Var;
        false    -> code_error({unbound_variable, X, Vars})
    end.

%% -- The compiler --

to_scode(_Env, {int, N}) ->
    [push(?i(N))];

to_scode(_Env, {string, S}) ->
    [push(?i(aeb_fate_data:make_string(S)))];

to_scode(_Env, {bool, B}) ->
    [push(?i(B))];

to_scode(_Env, {account_pubkey, K}) ->
    [push(?i(aeb_fate_data:make_address(K)))];

to_scode(_Env, {contract_pubkey, K}) ->
    [push(?i(aeb_fate_data:make_contract(K)))];

to_scode(_Env, {oracle_pubkey, K}) ->
    [push(?i(aeb_fate_data:make_oracle(K)))];

to_scode(_Env, {oracle_query_id, K}) ->
    %% Not actually in FATE yet
    [push(?i(aeb_fate_data:make_oracle_query(K)))];

to_scode(_Env, nil) ->
    [aeb_fate_code:nil(?a)];

to_scode(Env, {var, X}) ->
    [push(lookup_var(Env, X))];

to_scode(Env, {con, Ar, I, As}) ->
    N = length(As),
    [[to_scode(notail(Env), A) || A <- As],
     aeb_fate_code:variant(?a, ?i(Ar), ?i(I), ?i(N))];

to_scode(Env, {tuple, As}) ->
    N = length(As),
    [[ to_scode(notail(Env), A) || A <- As ],
     aeb_fate_code:tuple(N)];

to_scode(Env, {proj, E, I}) ->
    [to_scode(notail(Env), E),
     aeb_fate_code:element_op(?a, ?i(I), ?a)];

to_scode(Env, {set_proj, R, I, E}) ->
    [to_scode(notail(Env), E),
     to_scode(notail(Env), R),
     aeb_fate_code:setelement(?a, ?i(I), ?a, ?a)];

to_scode(Env, {op, Op, Args}) ->
    call_to_scode(Env, op_to_scode(Op), Args);

to_scode(Env, {'let', X, {var, Y}, Body}) ->
    Env1 = bind_var(X, lookup_var(Env, Y), Env),
    to_scode(Env1, Body);
to_scode(Env, {'let', X, Expr, Body}) ->
    {I, Env1} = bind_local(X, Env),
    [ to_scode(notail(Env), Expr),
      aeb_fate_code:store({var, I}, {stack, 0}),
      to_scode(Env1, Body) ];

to_scode(Env, {def, Fun, Args}) ->
    FName = make_function_name(Fun),
    Lbl   = aeb_fate_data:make_string(FName),
    [ [to_scode(notail(Env), Arg) || Arg <- lists:reverse(Args)],
      local_call(Env, ?i(Lbl)) ];
to_scode(Env, {funcall, Fun, Args}) ->
    [ [to_scode(notail(Env), Arg) || Arg <- lists:reverse(Args)],
      to_scode(Env, Fun),
      local_call(Env, ?a) ];

to_scode(Env, {switch, Case}) ->
    split_to_scode(Env, Case);

to_scode(Env, {builtin, B, Args}) ->
    builtin_to_scode(Env, B, Args);

to_scode(Env, {closure, Fun, FVs}) ->
    to_scode(Env, {tuple, [{string, make_function_name(Fun)}, FVs]});

to_scode(_Env, Icode) -> ?TODO(Icode).

local_call( Env, Fun) when Env#env.tailpos -> aeb_fate_code:call_t(Fun);
local_call(_Env, Fun)                      -> aeb_fate_code:call(Fun).


split_to_scode(Env, {nosplit, Expr}) ->
    [switch_body, to_scode(Env, Expr)];
split_to_scode(Env, {split, {tuple, _}, X, Alts}) ->
    {Def, Alts1} = catchall_to_scode(Env, X, Alts),
    Arg = lookup_var(Env, X),
    Alt = case [ {Xs, Split} || {'case', {tuple, Xs}, Split} <- Alts1 ] of
            []            -> missing;
            [{Xs, S} | _] ->
                {Code, Env1} = match_tuple(Env, Arg, Xs),
                [Code, split_to_scode(Env1, S)]
          end,
    case Def == missing andalso Alt /= missing of
       true  -> Alt;   % skip the switch if single tuple pattern
       false -> [{switch, Arg, tuple, [Alt], Def}]
    end;
split_to_scode(Env, {split, boolean, X, Alts}) ->
    {Def, Alts1} = catchall_to_scode(Env, X, Alts),
    GetAlt = fun(B) ->
                 case lists:keyfind({bool, B}, 2, Alts1) of
                     false          -> missing;
                     {'case', _, S} -> split_to_scode(Env, S)
                 end
             end,
    SAlts = [GetAlt(false), GetAlt(true)],
    Arg   = lookup_var(Env, X),
    [{switch, Arg, boolean, SAlts, Def}];
split_to_scode(Env, {split, {list, _}, X, Alts}) ->
    {Def, Alts1} = catchall_to_scode(Env, X, Alts),
    Arg = lookup_var(Env, X),
    GetAlt = fun(P) ->
                 case [C || C = {'case', Pat, _} <- Alts1, Pat == P orelse is_tuple(Pat) andalso element(1, Pat) == P] of
                     []      -> missing;
                     [{'case', nil, S} | _]           -> split_to_scode(Env, S);
                     [{'case', {'::', Y, Z}, S} | _] ->
                         {I, Env1} = bind_local(Y, Env),
                         {J, Env2} = bind_local(Z, Env1),
                         [aeb_fate_code:hd({var, I}, Arg),
                          aeb_fate_code:tl({var, J}, Arg),
                          split_to_scode(Env2, S)]
                 end
             end,
    SAlts = [GetAlt('::'), GetAlt(nil)],
    [aeb_fate_code:is_nil(?a, Arg),
     {switch, ?a, boolean, SAlts, Def}];
split_to_scode(Env, {split, Type, X, Alts}) when Type == integer; Type == string ->
    {Def, Alts1} = catchall_to_scode(Env, X, Alts),
    literal_split_to_scode(Env, Type, lookup_var(Env, X), Alts1, Def);
split_to_scode(Env, {split, {variant, Cons}, X, Alts}) ->
    {Def, Alts1} = catchall_to_scode(Env, X, Alts),
    Arg = lookup_var(Env, X),
    GetAlt = fun(I) ->
                case [{Xs, S} || {'case', {con, _, J, Xs}, S} <- Alts1, I == J] of
                    [] -> missing;
                    [{Xs, S} | _] ->
                        {Code, Env1} = match_variant(Env, Arg, Xs),
                        [Code, split_to_scode(Env1, S)]
                end
             end,
    SType  = {variant, [length(Args) || Args <- Cons]},
    case {[GetAlt(I) || I <- lists:seq(0, length(Cons) - 1)], Def} of
        %% Skip the switch for single constructor datatypes (with no catchall)
        {[SAlt], missing} when SAlt /= missing -> SAlt;
        {SAlts, _} -> [{switch, Arg, SType, SAlts, Def}]
    end.

literal_split_to_scode(_Env, _Type, Arg, [], Def) ->
    {switch, Arg, boolean, [missing, missing], Def};
literal_split_to_scode(Env, Type, Arg, [{'case', Lit, Body} | Alts], Def) when Type == integer; Type == string ->
    True = split_to_scode(Env, Body),
    False =
        case Alts of
            [] -> missing;
            _  -> literal_split_to_scode(Env, Type, Arg, Alts, missing)
        end,
    SLit = case Lit of
               {int, N} -> N;
               {string, S} -> aeb_fate_data:make_string(S)
           end,
    [aeb_fate_code:eq(?a, Arg, ?i(SLit)),
     {switch, ?a, boolean, [False, True], Def}].

catchall_to_scode(Env, X, Alts) -> catchall_to_scode(Env, X, Alts, []).

catchall_to_scode(Env, X, [{'case', {var, Y}, Split} | _], Acc) ->
    Env1 = bind_var(Y, lookup_var(Env, X), Env),
    {split_to_scode(Env1, Split), lists:reverse(Acc)};
catchall_to_scode(Env, X, [Alt | Alts], Acc) ->
    catchall_to_scode(Env, X, Alts, [Alt | Acc]);
catchall_to_scode(_, _, [], Acc) -> {missing, lists:reverse(Acc)}.

%% Tuple is in the accumulator. Arguments are the variable names.
match_tuple(Env, Arg, Xs) ->
    match_tuple(Env, 0, fun aeb_fate_code:element_op/3, Arg, Xs).

match_variant(Env, Arg, Xs) ->
    Elem = fun(Dst, I, Val) -> aeb_fate_code:variant_element(Dst, Val, I) end,
    match_tuple(Env, 0, Elem, Arg, Xs).

match_tuple(Env, I, Elem, Arg, ["_" | Xs]) ->
    match_tuple(Env, I + 1, Elem, Arg, Xs);
match_tuple(Env, I, Elem, Arg, [X | Xs]) ->
    {J,    Env1} = bind_local(X, Env),
    {Code, Env2} = match_tuple(Env1, I + 1, Elem, Arg, Xs),
    {[Elem({var, J}, ?i(I), Arg), Code], Env2};
match_tuple(Env, _, _, _, []) ->
    {[], Env}.

%% -- Builtins --

call_to_scode(Env, CallCode, Args) ->
    [[to_scode(notail(Env), A) || A <- lists:reverse(Args)],
     CallCode].

builtin_to_scode(_Env, get_state, none) ->
    [push(?s)];
builtin_to_scode(Env, set_state, [_] = Args) ->
    call_to_scode(Env, [aeb_fate_code:store(?s, ?a),
                        aeb_fate_code:tuple(0)], Args);
builtin_to_scode(_Env, event, [_] = _Args) ->
    ?TODO(fate_event_instruction);
builtin_to_scode(_Env, map_empty, none) ->
    [aeb_fate_code:map_empty(?a)];
builtin_to_scode(_Env, bits_none, none) ->
    [aeb_fate_code:bits_none(?a)];
builtin_to_scode(_Env, bits_all, none) ->
    [aeb_fate_code:bits_all(?a)];
builtin_to_scode(Env, abort, [_] = Args) ->
    call_to_scode(Env, aeb_fate_code:abort(?a), Args);
builtin_to_scode(Env, chain_spend, [_, _] = Args) ->
    call_to_scode(Env, [aeb_fate_code:spend(?a, ?a),
                        aeb_fate_code:tuple(0)], Args);
builtin_to_scode(Env, chain_balance, [_] = Args) ->
    call_to_scode(Env, aeb_fate_code:balance_other(?a, ?a), Args);
builtin_to_scode(_Env, chain_block_hash, [{builtin, chain_block_height, none}]) ->
    [aeb_fate_code:blockhash(?a)];
builtin_to_scode(_Env, chain_block_hash, [_]) ->
    ?TODO(fate_block_hash_at_height_instruction);
builtin_to_scode(_Env, chain_coinbase, none) ->
    [aeb_fate_code:beneficiary(?a)];
builtin_to_scode(_Env, chain_timestamp, none) ->
    [aeb_fate_code:timestamp(?a)];
builtin_to_scode(_Env, chain_block_height, none) ->
    [aeb_fate_code:generation(?a)];
builtin_to_scode(_Env, chain_difficulty, none) ->
    [aeb_fate_code:difficulty(?a)];
builtin_to_scode(_Env, chain_gas_limit, none) ->
    [aeb_fate_code:gaslimit(?a)];
builtin_to_scode(_Env, contract_balance, none) ->
    [aeb_fate_code:balance(?a)];
builtin_to_scode(_Env, contract_address, none) ->
    [aeb_fate_code:address(?a)];
builtin_to_scode(_Env, call_origin, none) ->
    [aeb_fate_code:origin(?a)];
builtin_to_scode(_Env, call_caller, none) ->
    [aeb_fate_code:caller(?a)];
builtin_to_scode(_Env, call_value, none) ->
    ?TODO(fate_call_value_instruction);
builtin_to_scode(_Env, call_gas_price, none) ->
    [aeb_fate_code:gasprice(?a)];
builtin_to_scode(_Env, call_gas_left, []) ->
    [aeb_fate_code:gas(?a)];
builtin_to_scode(_Env, oracle_register, [_, _, _, _] = _Args) ->
    ?TODO(fate_oracle_register_instruction);
builtin_to_scode(_Env, oracle_query_fee, [_] = _Args) ->
    ?TODO(fate_oracle_query_fee_instruction);
builtin_to_scode(_Env, oracle_query, [_, _, _, _, _] = _Args) ->
    ?TODO(fate_oracle_query_instruction);
builtin_to_scode(_Env, oracle_get_question, [_, _] = _Args) ->
    ?TODO(fate_oracle_get_question_instruction);
builtin_to_scode(_Env, oracle_respond, [_, _, _, _] = _Args) ->
    ?TODO(fate_oracle_respond_instruction);
builtin_to_scode(_Env, oracle_extend, [_, _, _] = _Args) ->
    ?TODO(fate_oracle_extend_instruction);
builtin_to_scode(_Env, oracle_get_answer, [_, _] = _Args) ->
    ?TODO(fate_oracle_get_answer_instruction);
builtin_to_scode(_Env, aens_resolve, [_, _] = _Args) ->
    ?TODO(fate_aens_resolve_instruction);
builtin_to_scode(_Env, aens_preclaim, [_, _, _] = _Args) ->
    ?TODO(fate_aens_preclaim_instruction);
builtin_to_scode(_Env, aens_claim, [_, _, _, _] = _Args) ->
    ?TODO(fate_aens_claim_instruction);
builtin_to_scode(_Env, aens_transfer, [_, _, _, _] = _Args) ->
    ?TODO(fate_aens_transfer_instruction);
builtin_to_scode(_Env, aens_revoke, [_, _, _] = _Args) ->
    ?TODO(fate_aens_revoke_instruction);
builtin_to_scode(_Env, crypto_ecverify, [_, _, _] = _Args) ->
    ?TODO(fate_crypto_ecverify_instruction);
builtin_to_scode(_Env, crypto_ecverify_secp256k1, [_, _, _] = _Args) ->
    ?TODO(fate_crypto_ecverify_secp256k1_instruction);
builtin_to_scode(_Env, crypto_sha3, [_] = _Args) ->
    ?TODO(fate_crypto_sha3_instruction);
builtin_to_scode(_Env, crypto_sha256, [_] = _Args) ->
    ?TODO(fate_crypto_sha256_instruction);
builtin_to_scode(_Env, crypto_blake2b, [_] = _Args) ->
    ?TODO(fate_crypto_blake2b_instruction);
builtin_to_scode(_Env, auth_tx_hash, none) ->
    ?TODO(fate_auth_tx_hash_instruction);
builtin_to_scode(_, B, Args) ->
    ?TODO({builtin, B, Args}).

%% -- Operators --

op_to_scode('+')               -> aeb_fate_code:add(?a, ?a, ?a);
op_to_scode('-')               -> aeb_fate_code:sub(?a, ?a, ?a);
op_to_scode('*')               -> aeb_fate_code:mul(?a, ?a, ?a);
op_to_scode('/')               -> aeb_fate_code:divide(?a, ?a, ?a);
op_to_scode(mod)               -> aeb_fate_code:modulo(?a, ?a, ?a);
op_to_scode('^')               -> aeb_fate_code:pow(?a, ?a, ?a);
op_to_scode('++')              -> aeb_fate_code:append(?a, ?a, ?a);
op_to_scode('::')              -> aeb_fate_code:cons(?a, ?a, ?a);
op_to_scode('<')               -> aeb_fate_code:lt(?a, ?a, ?a);
op_to_scode('>')               -> aeb_fate_code:gt(?a, ?a, ?a);
op_to_scode('=<')              -> aeb_fate_code:elt(?a, ?a, ?a);
op_to_scode('>=')              -> aeb_fate_code:egt(?a, ?a, ?a);
op_to_scode('==')              -> aeb_fate_code:eq(?a, ?a, ?a);
op_to_scode('!=')              -> aeb_fate_code:neq(?a, ?a, ?a);
op_to_scode('!')               -> aeb_fate_code:not_op(?a, ?a);
op_to_scode(map_get)           -> aeb_fate_code:map_lookup(?a, ?a, ?a);
op_to_scode(map_get_d)         -> aeb_fate_code:map_lookup(?a, ?a, ?a, ?a);
op_to_scode(map_set)           -> aeb_fate_code:map_update(?a, ?a, ?a, ?a);
op_to_scode(map_from_list)     -> aeb_fate_code:map_from_list(?a, ?a);
op_to_scode(map_to_list)       -> ?TODO(fate_map_to_list_instruction);
op_to_scode(map_delete)        -> aeb_fate_code:map_delete(?a, ?a, ?a);
op_to_scode(map_member)        -> aeb_fate_code:map_member(?a, ?a, ?a);
op_to_scode(map_size)          -> ?TODO(fate_map_size_instruction);
op_to_scode(string_length)     -> ?TODO(fate_string_length_instruction);
op_to_scode(string_concat)     -> aeb_fate_code:str_join(?a, ?a, ?a);
op_to_scode(bits_set)          -> aeb_fate_code:bits_set(?a, ?a, ?a);
op_to_scode(bits_clear)        -> aeb_fate_code:bits_clear(?a, ?a, ?a);
op_to_scode(bits_test)         -> aeb_fate_code:bits_test(?a, ?a, ?a);
op_to_scode(bits_sum)          -> aeb_fate_code:bits_sum(?a, ?a);
op_to_scode(bits_intersection) -> aeb_fate_code:bits_and(?a, ?a, ?a);
op_to_scode(bits_union)        -> aeb_fate_code:bits_or(?a, ?a, ?a);
op_to_scode(bits_difference)   -> aeb_fate_code:bits_diff(?a, ?a, ?a);
op_to_scode(address_to_str)    -> aeb_fate_code:addr_to_str(?a, ?a);
op_to_scode(int_to_str)        -> aeb_fate_code:int_to_str(?a, ?a).

%% PUSH and STORE ?a are the same, so we use STORE to make optimizations
%% easier, and specialize to PUSH (which is cheaper) at the end.
push(A) -> aeb_fate_code:store(?a, A).

%% -- Phase II ---------------------------------------------------------------
%%  Optimize

optimize_scode(Funs, Options) ->
    maps:map(fun(Name, Def) -> optimize_fun(Funs, Name, Def, Options) end,
             Funs).

flatten(missing) -> missing;
flatten(Code)    -> lists:map(fun flatten_s/1, lists:flatten(Code)).

flatten_s({switch, Arg, Type, Alts, Catch}) ->
    {switch, Arg, Type, [flatten(Alt) || Alt <- Alts], flatten(Catch)};
flatten_s(I) -> I.

-define(MAX_SIMPL_ITERATIONS, 10).

optimize_fun(_Funs, Name, {{Args, Res}, Code}, Options) ->
    Code0 = flatten(Code),
    debug(opt, Options, "Optimizing ~s\n", [Name]),
    Code1 = simpl_loop(0, Code0, Options),
    Code2 = desugar(Code1),
    {{Args, Res}, Code2}.

simpl_loop(N, Code, Options) when N >= ?MAX_SIMPL_ITERATIONS ->
    debug(opt, Options, "  No simpl_loop fixed_point after ~p iterations.\n\n", [N]),
    Code;
simpl_loop(N, Code, Options) ->
    ACode = annotate_code(Code),
    [ debug(opt, Options, "  annotated:\n~s\n", [pp_ann("    ", ACode)]) || N == 0 ],
    Code1 = simplify(ACode, Options),
    [ debug(opt, Options, "  optimized:\n~s\n", [pp_ann("    ", Code1)]) || Code1 /= ACode ],
    Code2 = unannotate(Code1),
    case Code == Code2 of
        true  ->
            debug(opt, Options, "  Reached simpl_loop fixed point after ~p iteration~s.\n\n",
                                [N, if N /= 1 -> "s"; true -> "" end]),
            Code2;
        false -> simpl_loop(N + 1, Code2, Options)
    end.

pp_ann(Ind, [{switch, Arg, Type, Alts, Def} | Code]) ->
    Tags =
        case Type of
            boolean       -> ["FALSE", "TRUE"];
            tuple         -> ["(_)"];
            {variant, Ar} -> ["C" ++ integer_to_list(I) || I <- lists:seq(0, length(Ar) - 1)]
        end,
    Ind1 = "  " ++ Ind,
    Ind2 = "  " ++ Ind1,
    [Ind, "SWITCH ", pp_arg(Arg), "\n",
     [[Ind1, Tag, " =>\n", pp_ann(Ind2, Alt)]
      || {Tag, Alt} <- lists:zip(Tags, Alts), Alt /= missing],
     [[Ind1, "_ =>\n", pp_ann(Ind2, Def)] || Def /= missing],
     pp_ann(Ind, Code)];
pp_ann(Ind, [switch_body | Code]) ->
    [Ind, "SWITCH-BODY\n", pp_ann(Ind, Code)];
pp_ann(Ind, [{i, #{ live_in := In, live_out := Out }, I} | Code]) ->
    Fmt = fun([]) -> "()";
             (Xs) -> string:join([lists:concat(["var", N]) || {var, N} <- Xs], " ")
          end,
    Op  = [Ind, aeb_fate_pp:format_op(I, #{})],
    Ann = [["   % ", Fmt(In), " -> ", Fmt(Out)] || In ++ Out /= []],
    [io_lib:format("~-40s~s\n", [Op, Ann]),
     pp_ann(Ind, Code)];
pp_ann(_, []) -> [].


pp_arg(?i(I))    -> io_lib:format("~w", [I]);
pp_arg({arg, N}) -> io_lib:format("arg~p", [N]);
pp_arg({var, N}) -> io_lib:format("var~p", [N]);
pp_arg(?a)       -> "a".

%% -- Analysis --

annotate_code(Code) ->
    {WCode, _} = ann_writes(Code, ordsets:new(), []),
    {RCode, _} = ann_reads(WCode, ordsets:new(), []),
    RCode.

%% Reverses the code
ann_writes(missing, Writes, []) -> {missing, Writes};
ann_writes([switch_body | Code], Writes, Acc) ->
    ann_writes(Code, Writes, [switch_body | Acc]);
ann_writes([{switch, Arg, Type, Alts, Def} | Code], Writes, Acc) ->
    {Alts1, WritesAlts} = lists:unzip([ ann_writes(Alt, Writes, []) || Alt <- Alts ]),
    {Def1, WritesDef}   = ann_writes(Def, Writes, []),
    Writes1 = ordsets:union(Writes, ordsets:intersection([WritesDef | WritesAlts])),
    ann_writes(Code, Writes1, [{switch, Arg, Type, Alts1, Def1} | Acc]);
ann_writes([I | Code], Writes, Acc) ->
    Ws = var_writes(I),
    Writes1 = ordsets:union(Writes, Ws),
    Ann = #{ writes_in => Writes, writes_out => Writes1 },
    ann_writes(Code, Writes1, [{i, Ann, I} | Acc]);
ann_writes([], Writes, Acc) ->
    {Acc, Writes}.

%% Takes reversed code and unreverses it.
ann_reads(missing, Reads, []) -> {missing, Reads};
ann_reads([switch_body | Code], Reads, Acc) ->
    ann_reads(Code, Reads, [switch_body | Acc]);
ann_reads([{switch, Arg, Type, Alts, Def} | Code], Reads, Acc) ->
    {Alts1, ReadsAlts} = lists:unzip([ ann_reads(Alt, Reads, []) || Alt <- Alts ]),
    {Def1, ReadsDef}   = ann_reads(Def, Reads, []),
    Reads1 = ordsets:union([[Arg], Reads, ReadsDef | ReadsAlts]),
    ann_reads(Code, Reads1, [{switch, Arg, Type, Alts1, Def1} | Acc]);
ann_reads([{i, Ann, I} | Code], Reads, Acc) ->
    #{ writes_in := WritesIn, writes_out := WritesOut } = Ann,
    #{ read := Rs, write := W, pure := Pure } = attributes(I),
    Reads1  =
        case {W, Pure andalso not ordsets:is_element(W, Reads)} of
            %% This is a little bit dangerous: if writing to a dead variable, we ignore
            %% the reads. Relies on dead writes to be removed by the
            %% optimisations below (r_write_to_dead_var).
            {{var, _}, true} -> Reads;
            _                -> ordsets:union(Reads, Rs)
        end,
    LiveIn  = ordsets:intersection(Reads1, WritesIn),
    LiveOut = ordsets:intersection(Reads, WritesOut),
    Ann1    = #{ live_in => LiveIn, live_out => LiveOut },
    ann_reads(Code, Reads1, [{i, Ann1, I} | Acc]);
ann_reads([], Reads, Acc) -> {Acc, Reads}.

%% Instruction attributes: reads, writes and purity (pure means no side-effects
%% aside from the reads and writes).
attributes(I) ->
    Set  = fun(L) when is_list(L) -> ordsets:from_list(L);
              (X)                 -> ordsets:from_list([X]) end,
    Attr = fun(W, R, P) -> #{read => Set(R), write => W, pure => P}  end,
    Pure   = fun(W, R) -> Attr(W, R, true) end,
    Impure = fun(W, R) -> Attr(W, R, false) end,
    case I of
        'RETURN'                              -> Impure(pc, []);
        {'RETURNR', A}                        -> Impure(pc, A);
        {'CALL', _}                           -> Impure(?a, []);
        {'CALL_R', A, _}                      -> Impure(?a, A);
        {'CALL_T', _}                         -> Impure(pc, []);
        {'CALL_TR', A, _}                     -> Impure(pc, A);
        {'JUMP', _}                           -> Impure(pc, []);
        {'JUMPIF', A, _}                      -> Impure(pc, A);
        {'SWITCH_V2', A, _, _}                -> Impure(pc, A);
        {'SWITCH_V3', A, _, _, _}             -> Impure(pc, A);
        {'SWITCH_VN', A, _}                   -> Impure(pc, A);
        {'PUSH', A}                           -> Pure(?a, A);
        'DUPA'                                -> Pure(?a, []);
        {'DUP', A}                            -> Pure(?a, A);
        {'POP', A}                            -> Pure(A, ?a);
        {'STORE', A, B}                       -> Pure(A, B);
        'INCA'                                -> Pure(?a, ?a);
        {'INC', A}                            -> Pure(A, A);
        'DECA'                                -> Pure(?a, []);
        {'DEC', A}                            -> Pure(A, A);
        {'ADD', A, B, C}                      -> Pure(A, [B, C]);
        {'SUB', A, B, C}                      -> Pure(A, [B, C]);
        {'MUL', A, B, C}                      -> Pure(A, [B, C]);
        {'DIV', A, B, C}                      -> Pure(A, [B, C]);
        {'MOD', A, B, C}                      -> Pure(A, [B, C]);
        {'POW', A, B, C}                      -> Pure(A, [B, C]);
        {'LT', A, B, C}                       -> Pure(A, [B, C]);
        {'GT', A, B, C}                       -> Pure(A, [B, C]);
        {'EQ', A, B, C}                       -> Pure(A, [B, C]);
        {'ELT', A, B, C}                      -> Pure(A, [B, C]);
        {'EGT', A, B, C}                      -> Pure(A, [B, C]);
        {'NEQ', A, B, C}                      -> Pure(A, [B, C]);
        {'AND', A, B, C}                      -> Pure(A, [B, C]);
        {'OR', A, B, C}                       -> Pure(A, [B, C]);
        {'NOT', A, B}                         -> Pure(A, B);
        {'TUPLE', _}                          -> Pure(?a, []);
        {'ELEMENT', A, B, C}                  -> Pure(A, [B, C]);
        {'SETELEMENT', A, B, C, D}            -> Pure(A, [B, C, D]);
        {'MAP_EMPTY', A}                      -> Pure(A, []);
        {'MAP_LOOKUP', A, B, C}               -> Pure(A, [B, C]);
        {'MAP_LOOKUPD', A, B, C, D}           -> Pure(A, [B, C, D]);
        {'MAP_UPDATE', A, B, C, D}            -> Pure(A, [B, C, D]);
        {'MAP_DELETE', A, B, C}               -> Pure(A, [B, C]);
        {'MAP_MEMBER', A, B, C}               -> Pure(A, [B, C]);
        {'MAP_FROM_LIST', A, B}               -> Pure(A, B);
        {'NIL', A}                            -> Pure(A, []);
        {'IS_NIL', A, B}                      -> Pure(A, B);
        {'CONS', A, B, C}                     -> Pure(A, [B, C]);
        {'HD', A, B}                          -> Pure(A, B);
        {'TL', A, B}                          -> Pure(A, B);
        {'LENGTH', A, B}                      -> Pure(A, B);
        {'APPEND', A, B, C}                   -> Pure(A, [B, C]);
        {'STR_JOIN', A, B, C}                 -> Pure(A, [B, C]);
        {'INT_TO_STR', A, B}                  -> Pure(A, B);
        {'ADDR_TO_STR', A, B}                 -> Pure(A, B);
        {'STR_REVERSE', A, B}                 -> Pure(A, B);
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
        {'ADDRESS', A}                        -> Pure(A, []);
        {'BALANCE', A}                        -> Impure(A, []);
        {'BALANCE_OTHER', A, B}               -> Impure(A, [B]);
        {'ORIGIN', A}                         -> Pure(A, []);
        {'CALLER', A}                         -> Pure(A, []);
        {'GASPRICE', A}                       -> Pure(A, []);
        {'BLOCKHASH', A}                      -> Pure(A, []);
        {'BENEFICIARY', A}                    -> Pure(A, []);
        {'TIMESTAMP', A}                      -> Pure(A, []);
        {'GENERATION', A}                     -> Pure(A, []);
        {'MICROBLOCK', A}                     -> Pure(A, []);
        {'DIFFICULTY', A}                     -> Pure(A, []);
        {'GASLIMIT', A}                       -> Pure(A, []);
        {'GAS', A}                            -> Impure(?a, A);
        {'LOG0', A, B}                        -> Impure(none, [A, B]);
        {'LOG1', A, B, C}                     -> Impure(none, [A, B, C]);
        {'LOG2', A, B, C, D}                  -> Impure(none, [A, B, C, D]);
        {'LOG3', A, B, C, D, E}               -> Impure(none, [A, B, C, D, E]);
        {'LOG4', A, B, C, D, E, F}            -> Impure(none, [A, B, C, D, E, F]);
        'DEACTIVATE'                          -> Impure(none, []);
        {'SPEND', A, B}                       -> Impure(none, [A, B]);

        {'ORACLE_REGISTER', A, B, C, D, E, F} -> Impure(A, [B, C, D, E, F]);
        'ORACLE_QUERY'                        -> Impure(?a, []);  %% TODO
        'ORACLE_RESPOND'                      -> Impure(?a, []);  %% TODO
        'ORACLE_EXTEND'                       -> Impure(?a, []);  %% TODO
        'ORACLE_GET_ANSWER'                   -> Impure(?a, []);  %% TODO
        'ORACLE_GET_QUESTION'                 -> Impure(?a, []);  %% TODO
        'ORACLE_QUERY_FEE'                    -> Impure(?a, []);  %% TODO
        'AENS_RESOLVE'                        -> Impure(?a, []);  %% TODO
        'AENS_PRECLAIM'                       -> Impure(?a, []);  %% TODO
        'AENS_CLAIM'                          -> Impure(?a, []);  %% TODO
        'AENS_UPDATE'                         -> Impure(?a, []);  %% TODO
        'AENS_TRANSFER'                       -> Impure(?a, []);  %% TODO
        'AENS_REVOKE'                         -> Impure(?a, []);  %% TODO
        'ECVERIFY'                            -> Pure(?a, []);  %% TODO
        'SHA3'                                -> Pure(?a, []);  %% TODO
        'SHA256'                              -> Pure(?a, []);  %% TODO
        'BLAKE2B'                             -> Pure(?a, []);  %% TODO
        {'ABORT', A}                          -> Impure(pc, A);
        {'EXIT', A}                           -> Impure(pc, A);
        'NOP'                                 -> Pure(none, [])
    end.

var_writes({i, _, I}) -> var_writes(I);
var_writes(I) ->
    #{ write := W } = attributes(I),
    case W of
        {var, _} -> [W];
        _        -> []
    end.

independent({switch, _, _, _, _}, _) -> false;
independent(_, {switch, _, _, _, _}) -> false;
independent(switch_body, _) -> true;
independent(_, switch_body) -> true;
independent({i, _, I}, {i, _, J}) ->
    #{ write := WI, read := RI, pure := PureI } = attributes(I),
    #{ write := WJ, read := RJ, pure := PureJ } = attributes(J),

    StackI = lists:member(?a, [WI | RI]),
    StackJ = lists:member(?a, [WJ | RJ]),

    if  WI == pc; WJ == pc   -> false;     %% no jumps
        not (PureI or PureJ) -> false;     %% at least one is pure
        StackI and StackJ    -> false;     %% cannot both use the stack
        true                 ->
            %% and cannot write to each other's inputs
            not lists:member(WI, RJ) andalso
            not lists:member(WJ, RI)
    end.

merge_ann(#{ live_in := LiveIn }, #{ live_out := LiveOut }) ->
    #{ live_in => LiveIn, live_out => LiveOut }.

%% Swap two instructions. Precondition: the instructions are independent/2.
swap_instrs(I, switch_body) -> {switch_body, I};
swap_instrs(switch_body, I) -> {I, switch_body};
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

live_in(R, #{ live_in  := LiveIn  }) -> ordsets:is_element(R, LiveIn);
live_in(R, {i, Ann, _}) -> live_in(R, Ann);
live_in(R, [I = {i, _, _} | _]) -> live_in(R, I);
live_in(R, [switch_body | Code]) -> live_in(R, Code);
live_in(R, [{switch, A, _, Alts, Def} | _]) ->
    R == A orelse lists:any(fun(Code) -> live_in(R, Code) end, [Def | Alts]);
live_in(_, missing) -> false;
live_in(_, []) -> false.

live_out(R, #{ live_out := LiveOut }) -> ordsets:is_element(R, LiveOut).

%% -- Optimizations --

simplify([], _) -> [];
simplify(missing, _) -> missing;
simplify([I | Code], Options) ->
    simpl_top(simpl_s(I, Options), simplify(Code, Options), Options).

simpl_s({switch, Arg, Type, Alts, Def}, Options) ->
    {switch, Arg, Type, [simplify(A, Options) || A <- Alts], simplify(Def, Options)};
simpl_s(I, _) -> I.

simpl_top(I, Code, Options) ->
    apply_rules(rules(), I, Code, Options).

apply_rules(Rules, I, Code, Options) ->
    Cons = fun(X, Xs) -> simpl_top(X, Xs, Options) end,
    case apply_rules_once(Rules, I, Code) of
        false -> [I | Code];
        {RName, New, Rest} ->
            debug(opt_rules, Options, "  Applied ~p:\n~s  ==>\n~s\n", [RName, pp_ann("    ", [I | Code]), pp_ann("    ", New ++ Rest)]),
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
    [?RULE(r_push_consume),
     ?RULE(r_one_shot_var),
     ?RULE(r_write_to_dead_var),
     ?RULE(r_inline_switch_target)
    ].

rules() ->
    merge_rules() ++
    [?RULE(r_dup_to_push),
     ?RULE(r_swap_push),
     ?RULE(r_swap_write),
     ?RULE(r_constant_propagation),
     ?RULE(r_prune_impossible_branches),
     ?RULE(r_inline_store),
     ?RULE(r_float_switch_body)
    ].

%% Removing pushes that are immediately consumed.
r_push_consume({i, Ann1, {'STORE', ?a, A}}, [{i, Ann2, {'POP', B}} | Code]) ->
    case live_out(B, Ann2) of
        true  -> {[{i, merge_ann(Ann1, Ann2), {'STORE', B, A}}], Code};
        false -> {[], Code}
    end;
r_push_consume({i, Ann1, {'STORE', ?a, A}}, Code) ->
    inline_push(Ann1, A, 0, Code, []);
%% Writing directly to memory instead of going through the accumulator.
r_push_consume({i, Ann1, I}, [{i, Ann2, {'STORE', R, ?a}} | Code]) ->
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
r_push_consume(_, _) -> false.

inline_push(Ann, Arg, Stack, [switch_body | Code], Acc) ->
    inline_push(Ann, Arg, Stack, Code, [switch_body | Acc]);
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
                false ->
                    {AI1, {i, Ann1b, _}} = swap_instrs({i, Ann1, {'STORE', ?a, Arg}}, AI),
                    inline_push(Ann1b, Arg, Stack + Produces - Consumes, Code, [AI1 | Acc])
            end;
        false -> false
    end;
inline_push(_, _, _, _, _) -> false.

split_stack_arg(N, As) -> split_stack_arg(N, As, []).
split_stack_arg(0, [?a | As], Acc) ->
    {lists:reverse(Acc), As};
split_stack_arg(N, [A | As], Acc) ->
    N1 = if A == ?a -> N - 1;
            true    -> N end,
    split_stack_arg(N1, As, [A | Acc]).

%% Changing PUSH A, DUPA to PUSH A, PUSH A enables further optimisations
r_dup_to_push({i, Ann1, Push={'STORE', ?a, _}}, [{i, Ann2, 'DUPA'} | Code]) ->
    #{ live_in  := LiveIn  } = Ann1,
    Ann1_ = Ann1#{ live_out => LiveIn },
    Ann2_ = Ann2#{ live_in  => LiveIn },
    {[{i, Ann1_, Push}, {i, Ann2_, Push}], Code};
r_dup_to_push(_, _) -> false.

%% Move PUSH A past non-stack instructions.
r_swap_push(Push = {i, _, {'STORE', ?a, _}}, [I | Code]) ->
    case independent(Push, I) of
        true ->
            {I1, Push1} = swap_instrs(Push, I),
            {[I1, Push1], Code};
        false -> false
    end;
r_swap_push(_, _) -> false.

%% Match up writes to variables with instructions further down.
r_swap_write(I = {i, _, _}, [J | Code]) ->
    case {var_writes(I), independent(I, J)} of
        {[_], true} ->
            {J1, I1} = swap_instrs(I, J),
            r_swap_write([J1], I1, Code);
        _ -> false
    end;
r_swap_write(_, _) -> false.

r_swap_write(Pre, I, [switch_body | Code]) ->
    r_swap_write([switch_body | Pre], I, Code);
r_swap_write(Pre, I, Code0 = [J | Code]) ->
    case apply_rules_once(merge_rules(), I, Code0) of
        {_Rule, New, Rest} ->
            {lists:reverse(Pre) ++ New, Rest};
        false ->
            case independent(I, J) of
                false -> false;
                true  ->
                    {J1, I1} = swap_instrs(I, J),
                    r_swap_write([J1 | Pre], I1, Code)
            end
    end;
r_swap_write(_, _, _) -> false.

%% Precompute instructions with known values
r_constant_propagation(Cons = {i, _, {'CONS', R, _, _}}, [{i, Ann, {'IS_NIL', S, R}} | Code]) ->
    Store = {i, Ann, {'STORE', S, ?i(false)}},
    case R of
        ?a -> {[Store], Code};
        _  -> {[Cons, Store], Code}
    end;
r_constant_propagation(Cons = {i, _, {'NIL', R}}, [{i, Ann, {'IS_NIL', S, R}} | Code]) ->
    Store = {i, Ann, {'STORE', S, ?i(true)}},
    case R of
        ?a -> {[Store], Code};
        _  -> {[Cons, Store], Code}
    end;
r_constant_propagation({i, Ann, I}, Code) ->
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
r_constant_propagation(_, _) -> false.

eval_op('ADD', [X, Y]) -> X + Y;
eval_op('SUB', [X, Y]) -> X - Y;
eval_op('MUL', [X, Y]) -> X * Y;
eval_op('DIV', [X, Y]) when Y /= 0 -> X div Y;
eval_op('MOD', [X, Y]) when Y /= 0 -> X rem Y;
eval_op('POW', [_, _]) -> no_eval;
eval_op('LT', [X, Y])  -> X < Y;
eval_op('GT', [X, Y])  -> X > Y;
eval_op('EQ', [X, Y])  -> X =:= Y;
eval_op('ELT', [X, Y]) -> X =< Y;
eval_op('EGT', [X, Y]) -> X >= Y;
eval_op('NEQ', [X, Y]) -> X =/= Y;
eval_op('NOT', [X])    -> not X;
eval_op(_, _)          -> no_eval.   %% TODO: bits?

%% Prune impossible branches from switches
r_prune_impossible_branches({switch, ?i(V), Type, Alts, missing}, Code) ->
    case pick_branch(Type, V, Alts) of
        false -> false;
        Alt   -> {Alt, Code}
    end;
r_prune_impossible_branches({switch, ?i(V), boolean, [False, True] = Alts, Def}, Code) ->
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
r_prune_impossible_branches(Variant = {i, _, {'VARIANT', R, ?i(_), ?i(Tag), ?i(_)}},
                            [{switch, R, Type, Alts, missing} | Code]) ->
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
r_prune_impossible_branches(_, _) -> false.

pick_branch(boolean, V, [False, True]) ->
    Alt = if V -> True; true -> False end,
    case Alt of
        missing -> false;
        _       -> Alt
    end;
pick_branch(_Type, _V, _Alts) ->
    false.

%% STORE R A, SWITCH R --> SWITCH A
r_inline_switch_target(Store = {i, _, {'STORE', R, A}}, [{switch, R, Type, Alts, Def} | Code]) ->
    Switch = {switch, A, Type, Alts, Def},
    case R of
        ?a       -> {[Switch], Code};
        {var, _} ->
            case lists:any(fun(Alt) -> live_in(R, Alt) end, [Def | Alts]) of
                false             -> {[Switch], Code};
                true when A /= ?a -> {[Store, Switch], Code};
                true              -> false
            end;
        _        -> false %% impossible
    end;
r_inline_switch_target(_, _) -> false.

%% Float switch-body to closest switch
r_float_switch_body(I = {i, _, _}, [switch_body | Code]) ->
    {[], [switch_body, I | Code]};
r_float_switch_body(_, _) -> false.

%% Inline stores
r_inline_store(I = {i, _, {'STORE', R = {var, _}, A}}, Code) ->
    %% Not when A is var unless updating the annotations properly.
    Inline = case A of
                 {arg, _} -> true;
                 ?i(_)    -> true;
                 _        -> false
             end,
    if Inline -> r_inline_store([I], R, A, Code);
       true   -> false end;
r_inline_store(_, _) -> false.

r_inline_store(Acc, R, A, [switch_body | Code]) ->
    r_inline_store([switch_body | Acc], R, A, Code);
r_inline_store(Acc, R, A, [{i, Ann, I} | Code]) ->
    #{ write := W, pure := Pure } = attributes(I),
    Inl = fun(X) when X == R -> A; (X) -> X end,
    case not live_in(R, Ann) orelse not Pure orelse lists:member(W, [R, A]) of
        true  -> false;
        false ->
            case op_view(I) of
                {Op, S, As} ->
                    case lists:member(R, As) of
                        true ->
                            Acc1 = [{i, Ann, from_op_view(Op, S, lists:map(Inl, As))} | Acc],
                            case r_inline_store(Acc1, R, A, Code) of
                                false        -> {lists:reverse(Acc1), Code};
                                {_, _} = Res -> Res
                            end;
                        false ->
                            r_inline_store([{i, Ann, I} | Acc], R, A, Code)
                    end;
                _ -> r_inline_store([{i, Ann, I} | Acc], R, A, Code)
            end
    end;
r_inline_store(_Acc, _, _, _) -> false.

%% Shortcut write followed by final read
r_one_shot_var({i, Ann1, I}, [{i, Ann2, J} | Code]) ->
    case op_view(I) of
        {Op, R, As} ->
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
r_one_shot_var(_, _) -> false.

%% Remove writes to dead variables
r_write_to_dead_var({i, Ann, I}, Code) ->
    case op_view(I) of
        {_Op, R = {var, _}, As} ->
            case live_out(R, Ann) of
                false ->
                    %% Subtle: we still have to pop the stack if any of the arguments
                    %% came from there. In this case we pop to R, which we know is
                    %% unused.
                    {[{i, Ann, {'POP', R}} || X <- As, X == ?a], Code};
                true -> false
            end;
        _ -> false
    end;
r_write_to_dead_var(_, _) -> false.

op_view(T) when is_tuple(T) ->
    case tuple_to_list(T) of
        [Op, R | As] when ?IsOp(Op) ->
            {Op, R, As};
        _ -> false
    end;
op_view(_) -> false.

from_op_view(Op, R, As) -> list_to_tuple([Op, R | As]).

%% Desugar and specialize and remove annotations
-spec unannotate(scode_a())  -> scode();
                (sinstr_a()) -> sinstr();
                (missing)    -> missing.
unannotate(switch_body) -> [switch_body];
unannotate({switch, Arg, Type, Alts, Def}) ->
    [{switch, Arg, Type, [unannotate(A) || A <- Alts], unannotate(Def)}];
unannotate(missing) -> missing;
unannotate(Code) when is_list(Code) ->
    lists:flatmap(fun unannotate/1, Code);
unannotate({i, _Ann, I}) -> [I].

%% Desugar and specialize
desugar({'ADD', ?a, ?i(1), ?a})     -> [aeb_fate_code:inc()];
desugar({'SUB', ?a, ?a, ?i(1)})     -> [aeb_fate_code:dec()];
desugar({'STORE', ?a, A})           -> [aeb_fate_code:push(A)];
desugar({switch, Arg, Type, Alts, Def}) ->
    [{switch, Arg, Type, [desugar(A) || A <- Alts], desugar(Def)}];
desugar(missing) -> missing;
desugar(Code) when is_list(Code) ->
    lists:flatmap(fun desugar/1, Code);
desugar(I) -> [I].

%% -- Phase III --------------------------------------------------------------
%%  Constructing basic blocks

to_basic_blocks(Funs, Options) ->
    maps:from_list([ {Name, {{Args, Res},
                             bb(Name, Code ++ [aeb_fate_code:return()], Options)}}
                     || {Name, {{Args, Res}, Code}} <- maps:to_list(Funs) ]).

bb(_Name, Code, _Options) ->
    Blocks0 = blocks(Code),
    Blocks1 = optimize_blocks(Blocks0),
    Blocks  = lists:flatmap(fun split_calls/1, Blocks1),
    Labels  = maps:from_list([ {Ref, I} || {I, {Ref, _}} <- with_ixs(Blocks) ]),
    BBs     = [ set_labels(Labels, B) || B <- Blocks ],
    maps:from_list(BBs).

%% -- Break up scode into basic blocks --

-type bbref() :: reference().

%% Code to be turned into blocks.
-record(blk, { ref             :: bbref(),        %% block id
               code            :: scode(),
               catchall = none :: bbref() | none  %% closest catchall
             }).

-type bb()     :: {bbref(), bcode()}.
-type bcode()  :: [binstr()].
-type binstr() :: {jump, bbref()}
                | {jumpif, bbref()}
                | tuple().   %% FATE instruction

-spec blocks(scode()) -> [bb()].
blocks(Code) ->
    Top = make_ref(),
    blocks([#blk{ref = Top, code = Code}], []).

-spec blocks([#blk{}], [bb()]) -> [bb()].
blocks([], Acc) ->
    lists:reverse(Acc);
blocks([Blk | Blocks], Acc) ->
    block(Blk, [], Blocks, Acc).

-spec block(#blk{}, bcode(), [#blk{}], [bb()]) -> [bb()].
block(#blk{ref = Ref, code = []}, CodeAcc, Blocks, BlockAcc) ->
    blocks(Blocks, [{Ref, lists:reverse(CodeAcc)} | BlockAcc]);
block(Blk = #blk{code = [switch_body | Code]}, Acc, Blocks, BlockAcc) ->
    %% Reached the body of a switch. Clear catchall ref.
    block(Blk#blk{code = Code, catchall = none}, Acc, Blocks, BlockAcc);
block(Blk = #blk{code     = [{switch, Arg, Type, Alts, Default} | Code],
                 catchall = Catchall}, Acc, Blocks, BlockAcc) ->
    FreshBlk = fun(C, Ca) ->
                   R = make_ref(),
                   {R, [#blk{ref = R, code = C, catchall = Ca}]}
               end,
    {RestRef, RestBlk} = FreshBlk(Code, Catchall),
    {DefRef, DefBlk} =
        case Default of
            missing when Catchall == none ->
                FreshBlk([aeb_fate_code:abort(?i(<<"Incomplete patterns">>))], none);
            missing -> {Catchall, []};
            _       -> FreshBlk(Default ++ [{jump, RestRef}], Catchall)
                       %% ^ fall-through to the outer catchall
        end,
    {Blk1, Code1, AltBlks} =
        case Type of
            boolean ->
                [FalseCode, TrueCode] = Alts,
                {ThenRef, ThenBlk} =
                    case TrueCode of
                        missing -> {DefRef, []};
                        _       -> FreshBlk(TrueCode ++ [{jump, RestRef}], DefRef)
                    end,
                ElseCode =
                    case FalseCode of
                        missing -> [{jump, DefRef}];
                        _       -> FalseCode ++ [{jump, RestRef}]
                    end,
                case lists:usort(Alts) == [missing] of
                    true  -> {Blk#blk{code = [{jump, DefRef}]}, [], []};
                    false ->
                        case Arg of
                            ?i(false) -> {Blk#blk{code = ElseCode}, [], ThenBlk};
                            ?i(true)  -> {Blk#blk{code = []}, [{jump, ThenRef}], ThenBlk};
                            _         -> {Blk#blk{code = ElseCode}, [{jumpif, Arg, ThenRef}], ThenBlk}
                        end
                end;
            tuple ->
                [TCode] = Alts,
                {Blk#blk{code = TCode ++ [{jump, RestRef}]}, [], []};
            {variant, [_]} ->
                %% [SINGLE_CON_SWITCH] Single constructor switches don't need a
                %% switch instruction.
                [AltCode] = Alts,
                {Blk#blk{code = AltCode ++ [{jump, RestRef}]}, [], []};
            {variant, _Ar} ->
                MkBlk = fun(missing) -> {DefRef, []};
                           (ACode)   -> FreshBlk(ACode ++ [{jump, RestRef}], DefRef)
                        end,
                {AltRefs, AltBs} = lists:unzip(lists:map(MkBlk, Alts)),
                {Blk#blk{code = []}, [{switch, Arg, AltRefs}], lists:append(AltBs)}
        end,
    Blk2 = Blk1#blk{catchall = DefRef}, %% Update catchall ref
    block(Blk2, Code1 ++ Acc, DefBlk ++ RestBlk ++ AltBlks ++ Blocks, BlockAcc);
block(Blk = #blk{code = [I | Code]}, Acc, Blocks, BlockAcc) ->
    block(Blk#blk{code = Code}, [I | Acc], Blocks, BlockAcc).

%% -- Reorder, inline, and remove dead blocks --

optimize_blocks(Blocks) ->
    %% We need to look at the last instruction a lot, so reverse all blocks.
    Rev       = fun(Bs) -> [ {Ref, lists:reverse(Code)} || {Ref, Code} <- Bs ] end,
    RBlocks   = Rev(Blocks),
    RBlockMap = maps:from_list(RBlocks),
    RBlocks1  = reorder_blocks(RBlocks, []),
    RBlocks2  = [ {Ref, inline_block(RBlockMap, Ref, Code)} || {Ref, Code} <- RBlocks1 ],
    RBlocks3  = remove_dead_blocks(RBlocks2),
    RBlocks4  = [ {Ref, tweak_returns(Code)} || {Ref, Code} <- RBlocks3 ],
    Rev(RBlocks4).

%% Choose the next block based on the final jump.
reorder_blocks([], Acc) ->
    lists:reverse(Acc);
reorder_blocks([{Ref, Code} | Blocks], Acc) ->
    reorder_blocks(Ref, Code, Blocks, Acc).

reorder_blocks(Ref, Code, Blocks, Acc) ->
    Acc1 = [{Ref, Code} | Acc],
    case Code of
        ['RETURN'|_]          -> reorder_blocks(Blocks, Acc1);
        [{'RETURNR', _}|_]    -> reorder_blocks(Blocks, Acc1);
        [{'CALL_T', _}|_]     -> reorder_blocks(Blocks, Acc1);
        [{'CALL_TR', _, _}|_] -> reorder_blocks(Blocks, Acc1);
        [{'ABORT', _}|_]      -> reorder_blocks(Blocks, Acc1);
        [{switch, _, _}|_]    -> reorder_blocks(Blocks, Acc1);
        [{jump, L}|_]         ->
            NotL = fun({L1, _}) -> L1 /= L end,
            case lists:splitwith(NotL, Blocks) of
                {Blocks1, [{L, Code1} | Blocks2]} ->
                    reorder_blocks(L, Code1, Blocks1 ++ Blocks2, Acc1);
                {_, []} -> reorder_blocks(Blocks, Acc1)
            end
    end.

%% Inline short blocks (≤ 2 instructions)
inline_block(BlockMap, Ref, [{jump, L} | Code] = Code0) when L /= Ref ->
    case maps:get(L, BlockMap, nocode) of
        Dest when length(Dest) < 3 ->
            %% Remove Ref to avoid infinite loops
            inline_block(maps:remove(Ref, BlockMap), L, Dest) ++ Code;
        _ -> Code0
    end;
inline_block(_, _, Code) -> Code.

%% Remove unused blocks
remove_dead_blocks(Blocks = [{Top, _} | _]) ->
    BlockMap   = maps:from_list(Blocks),
    LiveBlocks = chase_labels([Top], BlockMap, #{}),
    [ B || B = {L, _} <- Blocks, maps:is_key(L, LiveBlocks) ].

chase_labels([], _, Live) -> Live;
chase_labels([L | Ls], Map, Live) ->
    Code = maps:get(L, Map),
    Jump = fun({jump, A})       -> [A || not maps:is_key(A, Live)];
              ({jumpif, _, A})  -> [A || not maps:is_key(A, Live)];
              ({switch, _, As}) -> [A || A <- As, not maps:is_key(A, Live)];
              (_)               -> [] end,
    New  = lists:flatmap(Jump, Code),
    chase_labels(New ++ Ls, Map, Live#{ L => true }).

%% Replace PUSH, RETURN by RETURNR, drop returns after tail calls.
tweak_returns(['RETURN', {'PUSH', A} | Code])              -> [{'RETURNR', A} | Code];
tweak_returns(['RETURN' | Code = [{'CALL_T', _} | _]])     -> Code;
tweak_returns(['RETURN' | Code = [{'CALL_TR', _, _} | _]]) -> Code;
tweak_returns(['RETURN' | Code = [{'ABORT', _} | _]])      -> Code;
tweak_returns(Code) -> Code.

%% -- Split basic blocks at CALL instructions --
%%  Calls can only return to a new basic block.

split_calls({Ref, Code}) ->
    split_calls(Ref, Code, [], []).

split_calls(Ref, [], Acc, Blocks) ->
    lists:reverse([{Ref, lists:reverse(Acc)} | Blocks]);
split_calls(Ref, [I = {CALL, _} | Code], Acc, Blocks) when CALL == 'CALL'; CALL == 'CALL_R' ->
    split_calls(make_ref(), Code, [], [{Ref, lists:reverse([I | Acc])} | Blocks]);
split_calls(Ref, [I | Code], Acc, Blocks) ->
    split_calls(Ref, Code, [I | Acc], Blocks).

%% -- Translate label refs to indices --

set_labels(Labels, {Ref, Code}) when is_reference(Ref) ->
    {maps:get(Ref, Labels), [ set_labels(Labels, I) || I <- Code ]};
set_labels(Labels, {jump, Ref})   -> aeb_fate_code:jump(maps:get(Ref, Labels));
set_labels(Labels, {jumpif, Arg, Ref}) -> aeb_fate_code:jumpif(Arg, maps:get(Ref, Labels));
set_labels(Labels, {switch, Arg, Refs}) ->
    case [ maps:get(Ref, Labels) || Ref <- Refs ] of
        [R1, R2]     -> aeb_fate_code:switch(Arg, R1, R2);
        [R1, R2, R3] -> aeb_fate_code:switch(Arg, R1, R2, R3);
        Rs           -> aeb_fate_code:switch(Arg, Rs)
    end;
set_labels(_, I) -> I.

%% -- Helpers ----------------------------------------------------------------

with_ixs(Xs) ->
    lists:zip(lists:seq(0, length(Xs) - 1), Xs).

