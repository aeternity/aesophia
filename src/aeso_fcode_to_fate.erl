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

-export([compile/2, term_to_fate/1]).

%% -- Preamble ---------------------------------------------------------------

-type scode()  :: [sinstr()].
-type sinstr() :: {switch, arg(), stype(), [maybe_scode()], maybe_scode()}  %% last arg is catch-all
                | switch_body
                | tuple().    %% FATE instruction

-type arg() :: tuple(). %% Not exported: aeb_fate_ops:fate_arg().

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
-define(void, {var, 9999}).

-define(IsState(X), (is_tuple(X) andalso tuple_size(X) =:= 2 andalso element(1, X) =:= var andalso element(2, X) < 0)).

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
     Op =:= 'MAP_TO_LIST'     orelse
     Op =:= 'MAP_SIZE'        orelse
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
     Op =:= 'STR_LENGTH'      orelse
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
     Op =:= 'SHA3'            orelse
     Op =:= 'SHA256'          orelse
     Op =:= 'BLAKE2B'         orelse
     Op =:= 'ECVERIFY'        orelse
     Op =:= 'ECVERIFY_SECP256K1' orelse
     Op =:= 'CONTRACT_TO_ADDRESS' orelse
     Op =:= 'AUTH_TX_HASH'    orelse
     Op =:= 'BYTES_TO_INT'    orelse
     Op =:= 'BYTES_TO_STR'    orelse
     Op =:= 'ORACLE_CHECK'    orelse
     Op =:= 'ORACLE_CHECK_QUERY' orelse
     Op =:= 'IS_ORACLE'       orelse
     Op =:= 'IS_CONTRACT'     orelse
     Op =:= 'CREATOR'         orelse
     false)).

-record(env, { contract, vars = [], locals = [], tailpos = true }).

%% -- Debugging --------------------------------------------------------------

debug(Tag, Options, Fmt, Args) ->
    Tags = proplists:get_value(debug, Options, []),
    case Tags == all orelse lists:member(Tag, Tags) of
        true  -> io:format(Fmt, Args);
        false -> ok
    end.

%% -- Main -------------------------------------------------------------------

%% @doc Main entry point.
compile(FCode, Options) ->
    #{ contract_name := ContractName,
       state_type    := StateType,
       functions     := Functions } = FCode,
    SFuns  = functions_to_scode(ContractName, Functions, Options),
    SFuns1 = optimize_scode(SFuns, Options),
    SFuns2 = add_default_init_function(SFuns1, StateType),
    FateCode = to_basic_blocks(SFuns2),
    debug(compile, Options, "~s\n", [aeb_fate_asm:pp(FateCode)]),
    FateCode.

make_function_id(X) ->
    aeb_fate_code:symbol_identifier(make_function_name(X)).

make_function_name(init)               -> <<"INIT">>;
make_function_name(event)              -> <<"Chain.event">>;
make_function_name({entrypoint, Name}) -> Name;
make_function_name({local_fun, Xs})    -> list_to_binary("." ++ string:join(Xs, ".")).

functions_to_scode(ContractName, Functions, Options) ->
    FunNames = maps:keys(Functions),
    maps:from_list(
        [ {make_function_name(Name), function_to_scode(ContractName, FunNames, Name, Args, Body, Type, Options)}
        || {Name, #{args   := Args,
                    body   := Body,
                    return := Type}} <- maps:to_list(Functions)]).

function_to_scode(ContractName, Functions, _Name, Args, Body, ResType, _Options) ->
    {ArgTypes, ResType1} = typesig_to_scode(Args, ResType),
    SCode    = to_scode(init_env(ContractName, Functions, Args), Body),
    {{ArgTypes, ResType1}, SCode}.

-define(tvars, '$tvars').

typesig_to_scode(Args, Res) ->
    put(?tvars, {0, #{}}),
    R = {[type_to_scode(T) || {_, T} <- Args], type_to_scode(Res)},
    erase(?tvars),
    R.

type_to_scode(integer)         -> integer;
type_to_scode(boolean)         -> boolean;
type_to_scode(string)          -> string;
type_to_scode(address)         -> address;
type_to_scode({bytes, N})      -> {bytes, N};
type_to_scode(contract)        -> contract;
type_to_scode({oracle, _, _})  -> oracle;
type_to_scode(oracle_query)    -> oracle_query;
type_to_scode(name)            -> name;
type_to_scode(channel)         -> channel;
type_to_scode(bits)            -> bits;
type_to_scode(any)             -> any;
type_to_scode({variant, Cons}) -> {variant, lists:map(fun(T) -> type_to_scode({tuple, T}) end, Cons)};
type_to_scode({list, Type})    -> {list, type_to_scode(Type)};
type_to_scode({tuple, Types})  -> {tuple, lists:map(fun type_to_scode/1, Types)};
type_to_scode({map, Key, Val}) -> {map, type_to_scode(Key), type_to_scode(Val)};
type_to_scode({function, _Args, _Res}) -> {tuple, [string, any]};
type_to_scode({tvar, X}) ->
    {I, Vars} = get(?tvars),
    case maps:get(X, Vars, false) of
        false ->
            put(?tvars, {I + 1, Vars#{ X => I }}),
            {tvar, I};
        J -> {tvar, J}
    end.

add_default_init_function(SFuns, StateType) when StateType /= {tuple, []} ->
    %% Only add default if the type is unit.
    SFuns;
add_default_init_function(SFuns, {tuple, []}) ->
    %% Only add default if the init function is not present
    InitName = make_function_name({entrypoint, <<"init">>}),
    case maps:find(InitName, SFuns) of
        {ok, _} ->
            SFuns;
        error ->
            Sig = {[], {tuple, []}},
            Body = [tuple(0)],
            SFuns#{ InitName => {Sig, Body} }
    end.

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

lit_to_fate(L) ->
    case L of
        {int, N}             -> aeb_fate_data:make_integer(N);
        {string, S}          -> aeb_fate_data:make_string(S);
        {bytes, B}           -> aeb_fate_data:make_bytes(B);
        {bool, B}            -> aeb_fate_data:make_boolean(B);
        {account_pubkey, K}  -> aeb_fate_data:make_address(K);
        {contract_pubkey, K} -> aeb_fate_data:make_contract(K);
        {oracle_pubkey, K}   -> aeb_fate_data:make_oracle(K);
        {oracle_query_id, H} -> aeb_fate_data:make_oracle_query(H);
        {typerep, T}         -> aeb_fate_data:make_typerep(type_to_scode(T))
     end.

term_to_fate({lit, L}) ->
    lit_to_fate(L);
%% negative literals are parsed as 0 - N
term_to_fate({op, '-', [{lit, {int, 0}}, {lit, {int, N}}]}) ->
    aeb_fate_data:make_integer(-N);
term_to_fate(nil) ->
    aeb_fate_data:make_list([]);
term_to_fate({op, '::', [Hd, Tl]}) ->
    %% The Tl will translate into a list, because FATE lists are just lists
    [term_to_fate(Hd) | term_to_fate(Tl)];
term_to_fate({tuple, As}) ->
    aeb_fate_data:make_tuple(list_to_tuple([ term_to_fate(A) || A<-As]));
term_to_fate({con, Ar, I, As}) ->
    FateAs = [ term_to_fate(A) || A <- As ],
    aeb_fate_data:make_variant(Ar, I, list_to_tuple(FateAs));
term_to_fate({builtin, map_empty, []}) ->
    aeb_fate_data:make_map(#{});
term_to_fate({'let', _, {builtin, map_empty, []}, Set}) ->
    aeb_fate_data:make_map(map_to_fate(Set)).

map_to_fate({op, map_set, [{var, _}, K, V]}) ->
    #{term_to_fate(K) => term_to_fate(V)};
map_to_fate({op, map_set, [Set, K, V]}) ->
    Map = map_to_fate(Set), Map#{term_to_fate(K) => term_to_fate(V)}.

to_scode(_Env, {lit, L}) ->
    [push(?i(lit_to_fate(L)))];

to_scode(_Env, nil) ->
    [aeb_fate_ops:nil(?a)];

to_scode(Env, {var, X}) ->
    [push(lookup_var(Env, X))];

to_scode(Env, {con, Ar, I, As}) ->
    N = length(As),
    [[to_scode(notail(Env), A) || A <- As],
     aeb_fate_ops:variant(?a, ?i(Ar), ?i(I), ?i(N))];

to_scode(Env, {tuple, As}) ->
    N = length(As),
    [[ to_scode(notail(Env), A) || A <- As ],
     tuple(N)];

to_scode(Env, {proj, E, I}) ->
    [to_scode(notail(Env), E),
     aeb_fate_ops:element_op(?a, ?i(I), ?a)];

to_scode(Env, {set_proj, R, I, E}) ->
    [to_scode(notail(Env), E),
     to_scode(notail(Env), R),
     aeb_fate_ops:setelement(?a, ?i(I), ?a, ?a)];

to_scode(Env, {op, Op, Args}) ->
    call_to_scode(Env, op_to_scode(Op), Args);

to_scode(Env, {'let', X, {var, Y}, Body}) ->
    Env1 = bind_var(X, lookup_var(Env, Y), Env),
    to_scode(Env1, Body);
to_scode(Env, {'let', X, Expr, Body}) ->
    {I, Env1} = bind_local(X, Env),
    [ to_scode(notail(Env), Expr),
      aeb_fate_ops:store({var, I}, {stack, 0}),
      to_scode(Env1, Body) ];

to_scode(Env, {def, Fun, Args}) ->
    FName = make_function_id(Fun),
    Lbl   = aeb_fate_data:make_string(FName),
    call_to_scode(Env, local_call(Env, ?i(Lbl)), Args);
to_scode(Env, {funcall, Fun, Args}) ->
    call_to_scode(Env, [to_scode(Env, Fun), local_call(Env, ?a)], Args);

to_scode(Env, {builtin, B, Args}) ->
    builtin_to_scode(Env, B, Args);

to_scode(Env, {remote, Ct, Fun, [{builtin, call_gas_left, _}, Value | Args]}) ->
    %% Gas is not limited.
    Lbl  = make_function_id(Fun),
    Call = aeb_fate_ops:call_r(?a, Lbl, length(Args), ?a),    %% No remote tail calls
    call_to_scode(Env, Call, [Ct, Value | Args]);

to_scode(Env, {remote, Ct, Fun, [Gas, Value | Args]}) ->
    %% Gas is limited.
    Lbl = make_function_id(Fun),
    Call = aeb_fate_ops:call_gr(?a, Lbl, length(Args), ?a, ?a),   %% No remote tail calls
    call_to_scode(Env, Call, [Ct, Value, Gas | Args]);

to_scode(Env, {closure, Fun, FVs}) ->
    to_scode(Env, {tuple, [{lit, {string, make_function_id(Fun)}}, FVs]});

to_scode(Env, {switch, Case}) ->
    split_to_scode(Env, Case).

local_call( Env, Fun) when Env#env.tailpos -> aeb_fate_ops:call_t(Fun);
local_call(_Env, Fun)                      -> aeb_fate_ops:call(Fun).

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
                         [aeb_fate_ops:hd({var, I}, Arg),
                          aeb_fate_ops:tl({var, J}, Arg),
                          split_to_scode(Env2, S)]
                 end
             end,
    SAlts = [GetAlt('::'), GetAlt(nil)],
    [aeb_fate_ops:is_nil(?a, Arg),
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
    [aeb_fate_ops:eq(?a, Arg, ?i(SLit)),
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
    match_tuple(Env, 0, fun aeb_fate_ops:element_op/3, Arg, Xs).

match_variant(Env, Arg, Xs) ->
    Elem = fun(Dst, I, Val) -> aeb_fate_ops:variant_element(Dst, Val, I) end,
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

builtin_to_scode(_Env, get_state, []) ->
    [push(?s)];
builtin_to_scode(Env, set_state, [_] = Args) ->
    call_to_scode(Env, [aeb_fate_ops:store(?s, ?a),
                        tuple(0)], Args);
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
builtin_to_scode(Env, abort, [_] = Args) ->
    call_to_scode(Env, aeb_fate_ops:abort(?a), Args);
builtin_to_scode(Env, chain_spend, [_, _] = Args) ->
    call_to_scode(Env, [aeb_fate_ops:spend(?a, ?a),
                        tuple(0)], Args);
builtin_to_scode(Env, chain_balance, [_] = Args) ->
    call_to_scode(Env, aeb_fate_ops:balance_other(?a, ?a), Args);
builtin_to_scode(Env, chain_block_hash, [_] = Args) ->
    call_to_scode(Env, aeb_fate_ops:blockhash(?a, ?a), Args);
builtin_to_scode(_Env, chain_coinbase, []) ->
    [aeb_fate_ops:beneficiary(?a)];
builtin_to_scode(_Env, chain_timestamp, []) ->
    [aeb_fate_ops:timestamp(?a)];
builtin_to_scode(_Env, chain_block_height, []) ->
    [aeb_fate_ops:generation(?a)];
builtin_to_scode(_Env, chain_difficulty, []) ->
    [aeb_fate_ops:difficulty(?a)];
builtin_to_scode(_Env, chain_gas_limit, []) ->
    [aeb_fate_ops:gaslimit(?a)];
builtin_to_scode(_Env, contract_balance, []) ->
    [aeb_fate_ops:balance(?a)];
builtin_to_scode(_Env, contract_address, []) ->
    [aeb_fate_ops:address(?a)];
builtin_to_scode(_Env, contract_creator, []) ->
    [aeb_fate_ops:contract_creator(?a)];
builtin_to_scode(_Env, call_origin, []) ->
    [aeb_fate_ops:origin(?a)];
builtin_to_scode(_Env, call_caller, []) ->
    [aeb_fate_ops:caller(?a)];
builtin_to_scode(_Env, call_value, []) ->
    [aeb_fate_ops:call_value(?a)];
builtin_to_scode(_Env, call_gas_price, []) ->
    [aeb_fate_ops:gasprice(?a)];
builtin_to_scode(_Env, call_gas_left, []) ->
    [aeb_fate_ops:gas(?a)];
builtin_to_scode(Env, oracle_register, [_Sign,_Account,_QFee,_TTL,_QType,_RType] = Args) ->
    call_to_scode(Env, aeb_fate_ops:oracle_register(?a, ?a, ?a, ?a, ?a, ?a, ?a), Args);
builtin_to_scode(Env, oracle_query_fee, [_Oracle] = Args) ->
    call_to_scode(Env, aeb_fate_ops:oracle_query_fee(?a, ?a), Args);
builtin_to_scode(Env, oracle_query, [_Oracle, _Question, _QFee, _QTTL, _RTTL, _QType, _RType] = Args) ->
    call_to_scode(Env, aeb_fate_ops:oracle_query(?a, ?a, ?a, ?a, ?a, ?a, ?a, ?a), Args);
builtin_to_scode(Env, oracle_get_question, [_Oracle, _QueryId, _QType, _RType] = Args) ->
    call_to_scode(Env, aeb_fate_ops:oracle_get_question(?a, ?a, ?a, ?a, ?a), Args);
builtin_to_scode(Env, oracle_respond, [_Sign, _Oracle, _QueryId, _Response, _QType, _RType] = Args) ->
    call_to_scode(Env, [aeb_fate_ops:oracle_respond(?a, ?a, ?a, ?a, ?a, ?a),
                        tuple(0)], Args);
builtin_to_scode(Env, oracle_extend, [_Sign, _Oracle, _TTL] = Args) ->
    call_to_scode(Env, [aeb_fate_ops:oracle_extend(?a, ?a, ?a),
                        tuple(0)], Args);
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
builtin_to_scode(Env, aens_resolve, [_Name, _Key, _Type] = Args) ->
    call_to_scode(Env, aeb_fate_ops:aens_resolve(?a, ?a, ?a, ?a), Args);
builtin_to_scode(Env, aens_preclaim, [_Sign, _Account, _Hash] = Args) ->
    call_to_scode(Env, [aeb_fate_ops:aens_preclaim(?a, ?a, ?a),
                        tuple(0)], Args);
builtin_to_scode(Env, aens_claim, [_Sign, _Account, _NameString, _Salt, _NameFee] = Args) ->
    call_to_scode(Env, [aeb_fate_ops:aens_claim(?a, ?a, ?a, ?a, ?a),
                        tuple(0)], Args);
builtin_to_scode(Env, aens_transfer, [_Sign, _From, _To, _Name] = Args) ->
    call_to_scode(Env, [aeb_fate_ops:aens_transfer(?a, ?a, ?a, ?a),
                        tuple(0)], Args);
builtin_to_scode(Env, aens_revoke, [_Sign, _Account, _Name] = Args) ->
    call_to_scode(Env, [aeb_fate_ops:aens_revoke(?a, ?a, ?a),
                        tuple(0)], Args);
builtin_to_scode(_Env, auth_tx_hash, []) ->
    [aeb_fate_ops:auth_tx_hash(?a)].

%% -- Operators --

op_to_scode('+')               -> aeb_fate_ops:add(?a, ?a, ?a);
op_to_scode('-')               -> aeb_fate_ops:sub(?a, ?a, ?a);
op_to_scode('*')               -> aeb_fate_ops:mul(?a, ?a, ?a);
op_to_scode('/')               -> aeb_fate_ops:divide(?a, ?a, ?a);
op_to_scode(mod)               -> aeb_fate_ops:modulo(?a, ?a, ?a);
op_to_scode('^')               -> aeb_fate_ops:pow(?a, ?a, ?a);
op_to_scode('++')              -> aeb_fate_ops:append(?a, ?a, ?a);
op_to_scode('::')              -> aeb_fate_ops:cons(?a, ?a, ?a);
op_to_scode('<')               -> aeb_fate_ops:lt(?a, ?a, ?a);
op_to_scode('>')               -> aeb_fate_ops:gt(?a, ?a, ?a);
op_to_scode('=<')              -> aeb_fate_ops:elt(?a, ?a, ?a);
op_to_scode('>=')              -> aeb_fate_ops:egt(?a, ?a, ?a);
op_to_scode('==')              -> aeb_fate_ops:eq(?a, ?a, ?a);
op_to_scode('!=')              -> aeb_fate_ops:neq(?a, ?a, ?a);
op_to_scode('!')               -> aeb_fate_ops:not_op(?a, ?a);
op_to_scode(map_get)           -> aeb_fate_ops:map_lookup(?a, ?a, ?a);
op_to_scode(map_get_d)         -> aeb_fate_ops:map_lookup(?a, ?a, ?a, ?a);
op_to_scode(map_set)           -> aeb_fate_ops:map_update(?a, ?a, ?a, ?a);
op_to_scode(map_from_list)     -> aeb_fate_ops:map_from_list(?a, ?a);
op_to_scode(map_to_list)       -> aeb_fate_ops:map_to_list(?a, ?a);
op_to_scode(map_delete)        -> aeb_fate_ops:map_delete(?a, ?a, ?a);
op_to_scode(map_member)        -> aeb_fate_ops:map_member(?a, ?a, ?a);
op_to_scode(map_size)          -> aeb_fate_ops:map_size_(?a, ?a);
op_to_scode(string_length)     -> aeb_fate_ops:str_length(?a, ?a);
op_to_scode(string_concat)     -> aeb_fate_ops:str_join(?a, ?a, ?a);
op_to_scode(bits_set)          -> aeb_fate_ops:bits_set(?a, ?a, ?a);
op_to_scode(bits_clear)        -> aeb_fate_ops:bits_clear(?a, ?a, ?a);
op_to_scode(bits_test)         -> aeb_fate_ops:bits_test(?a, ?a, ?a);
op_to_scode(bits_sum)          -> aeb_fate_ops:bits_sum(?a, ?a);
op_to_scode(bits_intersection) -> aeb_fate_ops:bits_and(?a, ?a, ?a);
op_to_scode(bits_union)        -> aeb_fate_ops:bits_or(?a, ?a, ?a);
op_to_scode(bits_difference)   -> aeb_fate_ops:bits_diff(?a, ?a, ?a);
op_to_scode(address_to_str)    -> aeb_fate_ops:addr_to_str(?a, ?a);
op_to_scode(int_to_str)        -> aeb_fate_ops:int_to_str(?a, ?a);
op_to_scode(contract_to_address)       -> aeb_fate_ops:contract_to_address(?a, ?a);
op_to_scode(crypto_ecverify)           -> aeb_fate_ops:ecverify(?a, ?a, ?a, ?a);
op_to_scode(crypto_ecverify_secp256k1) -> aeb_fate_ops:ecverify_secp256k1(?a, ?a, ?a, ?a);
op_to_scode(crypto_sha3)               -> aeb_fate_ops:sha3(?a, ?a);
op_to_scode(crypto_sha256)             -> aeb_fate_ops:sha256(?a, ?a);
op_to_scode(crypto_blake2b)            -> aeb_fate_ops:blake2b(?a, ?a);
op_to_scode(string_sha3)               -> aeb_fate_ops:sha3(?a, ?a);
op_to_scode(string_sha256)             -> aeb_fate_ops:sha256(?a, ?a);
op_to_scode(string_blake2b)            -> aeb_fate_ops:blake2b(?a, ?a).

%% PUSH and STORE ?a are the same, so we use STORE to make optimizations
%% easier, and specialize to PUSH (which is cheaper) at the end.
push(A) -> aeb_fate_ops:store(?a, A).

tuple(0) -> push(?i({tuple, {}}));
tuple(N) -> aeb_fate_ops:tuple(?a, N).

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
pp_arg({var, N}) when N < 0 -> io_lib:format("store~p", [-N]);
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
    Ws = [ W || W <- var_writes(I), not ?IsState(W) ],
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
        {'CALL_R', A, _, _, B}                -> Impure(?a, [A, B]);
        {'CALL_GR', A, _, _, B, C}            -> Impure(?a, [A, B, C]);
        {'CALL_T', _}                         -> Impure(pc, []);
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
        {'ADDR_TO_STR', A, B}                 -> Pure(A, B);
        {'STR_REVERSE', A, B}                 -> Pure(A, B);
        {'STR_LENGTH', A, B}                  -> Pure(A, B);
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
        {'ECVERIFY', A, B, C, D}              -> Pure(A, [B, C, D]);
        {'ECVERIFY_SECP256K1', A, B, C, D}    -> Pure(A, [B, C, D]);
        {'CONTRACT_TO_ADDRESS', A, B}         -> Pure(A, [B]);
        {'AUTH_TX_HASH', A}                   -> Pure(A, []);
        {'BYTES_TO_INT', A, B}                -> Pure(A, [B]);
        {'BYTES_TO_STR', A, B}                -> Pure(A, [B]);
        {'ORACLE_CHECK', A, B, C, D}          -> Impure(A, [B, C, D]);
        {'ORACLE_CHECK_QUERY', A, B, C, D, E} -> Impure(A, [B, C, D, E]);
        {'IS_ORACLE', A, B}                   -> Impure(A, [B]);
        {'IS_CONTRACT', A, B}                 -> Impure(A, [B]);
        {'CREATOR', A}                        -> Pure(A, []);
        {'ADDRESS', A}                        -> Pure(A, []);
        {'BALANCE', A}                        -> Impure(A, []);
        {'BALANCE_OTHER', A, B}               -> Impure(A, [B]);
        {'ORIGIN', A}                         -> Pure(A, []);
        {'CALLER', A}                         -> Pure(A, []);
        {'GASPRICE', A}                       -> Pure(A, []);
        {'BLOCKHASH', A, B}                   -> Impure(A, [B]);
        {'BENEFICIARY', A}                    -> Pure(A, []);
        {'TIMESTAMP', A}                      -> Pure(A, []);
        {'GENERATION', A}                     -> Pure(A, []);
        {'MICROBLOCK', A}                     -> Pure(A, []);
        {'DIFFICULTY', A}                     -> Pure(A, []);
        {'GASLIMIT', A}                       -> Pure(A, []);
        {'GAS', A}                            -> Impure(?a, A);
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
        {'ORACLE_GET_ANSWER', A, B, C, D, E}  -> Impure(A, [B, C, D, E]);
        {'ORACLE_GET_QUESTION', A, B, C, D, E}-> Impure(A, [B, C, D, E]);
        {'ORACLE_QUERY_FEE', A, B}            -> Impure(A, [B]);
        {'AENS_RESOLVE', A, B, C, D}          -> Impure(A, [B, C, D]);
        {'AENS_PRECLAIM', A, B, C}            -> Impure(none, [A, B, C]);
        {'AENS_CLAIM', A, B, C, D, E}         -> Impure(none, [A, B, C, D, E]);
        'AENS_UPDATE'                         -> Impure(none, []);%% TODO
        {'AENS_TRANSFER', A, B, C, D}         -> Impure(none, [A, B, C, D]);
        {'AENS_REVOKE', A, B, C}              -> Impure(none, [A, B, C]);
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

-spec independent(sinstr_a(), sinstr_a()) -> boolean().
%% independent({switch, _, _, _, _}, _) -> false;       %% Commented due to Dialyzer whinging
independent(_, {switch, _, _, _, _}) -> false;
%% independent(switch_body, _) -> true;
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
%% swap_instrs(switch_body, I) -> {I, switch_body};   %% Commented due to Dialyzer whinging
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

live_in(R, _) when ?IsState(R) -> true;
live_in(R, #{ live_in  := LiveIn  }) -> ordsets:is_element(R, LiveIn);
live_in(R, {i, Ann, _}) -> live_in(R, Ann);
live_in(R, [I = {i, _, _} | _]) -> live_in(R, I);
live_in(R, [switch_body | Code]) -> live_in(R, Code);
live_in(R, [{switch, A, _, Alts, Def} | _]) ->
    R == A orelse lists:any(fun(Code) -> live_in(R, Code) end, [Def | Alts]);
live_in(_, missing) -> false;
live_in(_, []) -> false.

live_out(R, _) when ?IsState(R) -> true;
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
    [?RULE(r_swap_push),
     ?RULE(r_swap_write),
     ?RULE(r_constant_propagation),
     ?RULE(r_prune_impossible_branches),
     ?RULE(r_inline_store),
     ?RULE(r_float_switch_body)
    ].

%% Removing pushes that are immediately consumed.
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
r_write_to_dead_var({i, _, {'STORE', ?void, ?a}}, _) -> false; %% Avoid looping
r_write_to_dead_var({i, Ann, I}, Code) ->
    case op_view(I) of
        {_Op, R = {var, _}, As} ->
            case live_out(R, Ann) of
                false ->
                    %% Subtle: we still have to pop the stack if any of the arguments
                    %% came from there.
                    {[{i, Ann, {'STORE', ?void, ?a}} || X <- As, X == ?a], Code};
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
desugar({'ADD', ?a, ?i(1), ?a})     -> [aeb_fate_ops:inc()];
desugar({'SUB', ?a, ?a, ?i(1)})     -> [aeb_fate_ops:dec()];
desugar({'STORE', ?a, A})           -> [aeb_fate_ops:push(A)];
desugar({switch, Arg, Type, Alts, Def}) ->
    [{switch, Arg, Type, [desugar(A) || A <- Alts], desugar(Def)}];
desugar(missing) -> missing;
desugar(Code) when is_list(Code) ->
    lists:flatmap(fun desugar/1, Code);
desugar(I) -> [I].

%% -- Phase III --------------------------------------------------------------
%%  Constructing basic blocks

to_basic_blocks(Funs) ->
    to_basic_blocks(maps:to_list(Funs), aeb_fate_code:new()).

to_basic_blocks([{Name, {Sig, Code}}|Left], Acc) ->
    BB = bb(Name, Code ++ [aeb_fate_ops:return()]),
    to_basic_blocks(Left, aeb_fate_code:insert_fun(Name, Sig, BB, Acc));
to_basic_blocks([], Acc) ->
    Acc.

bb(_Name, Code) ->
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
                FreshBlk([aeb_fate_ops:exit(?i(<<"Incomplete patterns">>))], none);
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
        [{'EXIT', _}|_]       -> reorder_blocks(Blocks, Acc1);
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
tweak_returns(['RETURN', {'PUSH', A} | Code])          -> [{'RETURNR', A} | Code];
tweak_returns(['RETURN' | Code = [{'CALL_T', _} | _]]) -> Code;
tweak_returns(['RETURN' | Code = [{'ABORT', _} | _]])  -> Code;
tweak_returns(['RETURN' | Code = [{'EXIT', _} | _]])   -> Code;
tweak_returns(Code) -> Code.

%% -- Split basic blocks at CALL instructions --
%%  Calls can only return to a new basic block. Also splits at JUMPIF instructions.

split_calls({Ref, Code}) ->
    split_calls(Ref, Code, [], []).

split_calls(Ref, [], Acc, Blocks) ->
    lists:reverse([{Ref, lists:reverse(Acc)} | Blocks]);
split_calls(Ref, [I | Code], Acc, Blocks) when element(1, I) == 'CALL';
                                               element(1, I) == 'CALL_R';
                                               element(1, I) == 'CALL_GR';
                                               element(1, I) == 'jumpif' ->
    split_calls(make_ref(), Code, [], [{Ref, lists:reverse([I | Acc])} | Blocks]);
split_calls(Ref, [{'ABORT', _} = I | _Code], Acc, Blocks) ->
    lists:reverse([{Ref, lists:reverse([I | Acc])} | Blocks]);
split_calls(Ref, [{'EXIT', _} = I | _Code], Acc, Blocks) ->
    lists:reverse([{Ref, lists:reverse([I | Acc])} | Blocks]);
split_calls(Ref, [I | Code], Acc, Blocks) ->
    split_calls(Ref, Code, [I | Acc], Blocks).

%% -- Translate label refs to indices --

set_labels(Labels, {Ref, Code}) when is_reference(Ref) ->
    {maps:get(Ref, Labels), [ set_labels(Labels, I) || I <- Code ]};
set_labels(Labels, {jump, Ref})   -> aeb_fate_ops:jump(maps:get(Ref, Labels));
set_labels(Labels, {jumpif, Arg, Ref}) -> aeb_fate_ops:jumpif(Arg, maps:get(Ref, Labels));
set_labels(Labels, {switch, Arg, Refs}) ->
    case [ maps:get(Ref, Labels) || Ref <- Refs ] of
        [R1, R2]     -> aeb_fate_ops:switch(Arg, R1, R2);
        [R1, R2, R3] -> aeb_fate_ops:switch(Arg, R1, R2, R3);
        Rs           -> aeb_fate_ops:switch(Arg, Rs)
    end;
set_labels(_, I) -> I.

%% -- Helpers ----------------------------------------------------------------

with_ixs(Xs) ->
    lists:zip(lists:seq(0, length(Xs) - 1), Xs).
