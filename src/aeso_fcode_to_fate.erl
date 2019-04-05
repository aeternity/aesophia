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
-compile([export_all, no_warn_export_all]).

%% -- Preamble ---------------------------------------------------------------

-define(TODO(What), error({todo, ?FILE, ?LINE, ?FUNCTION_NAME, What})).

-define(i(X), {immediate, X}).
-define(a, {stack, 0}).

-define(IsBinOp(Op),
    (Op =:= 'ADD' orelse
     Op =:= 'SUB' orelse
     Op =:= 'MUL' orelse
     Op =:= 'DIV' orelse
     Op =:= 'MOD' orelse
     Op =:= 'POW' orelse
     Op =:= 'LT'  orelse
     Op =:= 'GT'  orelse
     Op =:= 'EQ'  orelse
     Op =:= 'ELT' orelse
     Op =:= 'EGT' orelse
     Op =:= 'NEQ' orelse
     Op =:= 'AND' orelse
     Op =:= 'OR'  orelse
     Op =:= 'ELEMENT')).

-record(env, { args = [], stack = [], locals = [], tailpos = true }).

%% -- Debugging --------------------------------------------------------------

debug(Tag, Options, Fmt, Args) ->
    Tags = proplists:get_value(debug, Options, []),
    case Tags == all orelse lists:member(Tag, Tags) orelse Tag == any andalso Tags /= [] of
        true  -> io:format(Fmt, Args);
        false -> ok
    end.

%% -- Main -------------------------------------------------------------------

%% @doc Main entry point.
compile(ICode, Options) ->
    #{ contract_name := _ContractName,
       state_type    := _StateType,
       functions     := Functions } = ICode,
    SFuns  = functions_to_scode(Functions, Options),
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

functions_to_scode(Functions, Options) ->
    maps:from_list(
        [ {make_function_name(Name), function_to_scode(Name, Args, Body, Type, Options)}
        || {Name, #{args   := Args,
                    body   := Body,
                    return := Type}} <- maps:to_list(Functions),
           Name /= init ]).  %% TODO: skip init for now

function_to_scode(Name, Args, Body, ResType, Options) ->
    debug(scode, Options, "Compiling ~p ~p : ~p ->\n  ~p\n", [Name, Args, ResType, Body]),
    ArgTypes = [ T || {_, T} <- Args ],
    SCode    = to_scode(init_env(Args), Body),
    debug(scode, Options, "  scode: ~p\n", [SCode]),
    {{ArgTypes, ResType}, SCode}.

%% -- Phase I ----------------------------------------------------------------
%%  Icode to structured assembly

%% -- Environment functions --

init_env(Args) ->
    #env{ args = Args, stack = [], tailpos = true }.

push_env(Type, Env) ->
    Env#env{ stack = [Type | Env#env.stack] }.

bind_local(Name, Env = #env{ locals = Locals }) ->
    I = length(Locals),
    {I, Env#env{ locals = [{Name, I} | Locals] }}.

notail(Env) -> Env#env{ tailpos = false }.

lookup_var(Env = #env{ args = Args, locals = Locals }, X) ->
    case {lists:keyfind(X, 1, Locals), keyfind_index(X, 1, Args)} of
        {false, false}  -> error({unbound_variable, X, Env});
        {false, Arg}    -> {arg, Arg};
        {{_, Local}, _} -> {var, Local}
    end.

%% -- The compiler --

to_scode(_Env, {integer, N}) ->
    [aeb_fate_code:push(?i(N))];    %% Doesn't exist (yet), translated by desugaring

to_scode(Env, {var, X}) ->
    [aeb_fate_code:push(lookup_var(Env, X))];

to_scode(Env, {tuple, As}) ->
    N = length(As),
    [[ to_scode(Env, A) || A <- As ],
     aeb_fate_code:tuple(N)];

to_scode(Env, {binop, Type, Op, A, B}) ->
    [ to_scode(notail(Env), B),
      to_scode(push_env(Type, Env), A),
      binop_to_scode(Op) ];

to_scode(Env, {'if', Dec, Then, Else}) ->
    [ to_scode(notail(Env), Dec),
      {ifte, to_scode(Env, Then), to_scode(Env, Else)} ];

to_scode(Env, {'let', X, Expr, Body}) ->
    {I, Env1} = bind_local(X, Env),
    [ to_scode(Env, Expr),
      aeb_fate_code:store({var, I}, {stack, 0}),
      to_scode(Env1, Body) ];

to_scode(Env, {switch, Case}) ->
    case_to_scode(Env, Case);

to_scode(_Env, Icode) -> ?TODO(Icode).

case_to_scode(Env, {nosplit, _Xs, Expr}) ->
    %% TODO: need to worry about variable names?
    to_scode(Env, Expr);
case_to_scode(Env, {split, _Type, X, [{'case', {tuple, Xs}, Case}], nodefault}) ->
    {Code, Env1} = match_tuple(Env, Xs),
    [aeb_fate_code:push(lookup_var(Env, X)),
     Code, case_to_scode(Env1, Case)];
case_to_scode(_, Split = {split, _, _, _, _}) ->
    ?TODO({'case', Split}).

%% Tuple is in the accumulator. Arguments are the variable names.
match_tuple(Env, Xs) ->
    match_tuple(Env, 0, Xs).

match_tuple(Env, I, ["_" | Xs]) ->
    match_tuple(Env, I + 1, Xs);
match_tuple(Env, I, [X | Xs]) ->
    {J,    Env1} = bind_local(X, Env),
    {Code, Env2} = match_tuple(Env1, I + 1, Xs),
    {[ [aeb_fate_code:dup() || [] /= [Y || Y <- Xs, Y /= "_"]],  %% Don't DUP the last one
       aeb_fate_code:element_op({var, J}, ?i(I), ?a),
       Code], Env2};
match_tuple(Env, _, []) ->
    {[], Env}.

%% -- Operators --

binop_to_scode('+') -> add_a_a_a();  %% Optimization introduces other variants
binop_to_scode('-') -> sub_a_a_a();
binop_to_scode('==') -> eq_a_a_a().
% binop_to_scode(Op) -> ?TODO(Op).

add_a_a_a() -> aeb_fate_code:add(?a, ?a, ?a).
sub_a_a_a() -> aeb_fate_code:sub(?a, ?a, ?a).
eq_a_a_a()  -> aeb_fate_code:eq(?a, ?a, ?a).

%% -- Phase II ---------------------------------------------------------------
%%  Optimize

optimize_scode(Funs, Options) ->
    maps:map(fun(Name, Def) -> optimize_fun(Funs, Name, Def, Options) end,
             Funs).

flatten(Code) -> lists:map(fun flatten_s/1, lists:flatten(Code)).

flatten_s({ifte, Then, Else}) -> {ifte, flatten(Then), flatten(Else)};
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

pp_ann(Ind, [{ifte, Then, Else} | Code]) ->
    [Ind, "IF-THEN\n",
     pp_ann("  " ++ Ind, Then),
     Ind, "ELSE\n",
     pp_ann("  " ++ Ind, Else),
     pp_ann(Ind, Code)];
pp_ann(Ind, [{#{ live_in := In, live_out := Out }, I} | Code]) ->
    Fmt = fun([]) -> "()";
             (Xs) -> string:join([lists:concat(["var", N]) || {var, N} <- Xs], " ")
          end,
    Op  = [Ind, aeb_fate_pp:format_op(I, #{})],
    Ann = [["   % ", Fmt(In), " -> ", Fmt(Out)] || In ++ Out /= []],
    [io_lib:format("~-40s~s\n", [Op, Ann]),
     pp_ann(Ind, Code)];
pp_ann(_, []) -> [].

%% -- Analysis --

annotate_code(Code) ->
    {WCode, _} = ann_writes(Code, ordsets:new(), []),
    {RCode, _} = ann_reads(WCode, ordsets:new(), []),
    RCode.

%% Reverses the code
ann_writes([{ifte, Then, Else} | Code], Writes, Acc) ->
    {Then1, WritesThen} = ann_writes(Then, Writes, []),
    {Else1, WritesElse} = ann_writes(Else, Writes, []),
    Writes1 = ordsets:union(Writes, ordsets:intersection(WritesThen, WritesElse)),
    ann_writes(Code, Writes1, [{ifte, Then1, Else1} | Acc]);
ann_writes([I | Code], Writes, Acc) ->
    Ws = var_writes(I),
    Writes1 = ordsets:union(Writes, Ws),
    Ann = #{ writes_in => Writes, writes_out => Writes1 },
    ann_writes(Code, Writes1, [{Ann, I} | Acc]);
ann_writes([], Writes, Acc) ->
    {Acc, Writes}.

%% Takes reversed code and unreverses it.
ann_reads([{ifte, Then, Else} | Code], Reads, Acc) ->
    {Then1, ReadsThen} = ann_reads(Then, Reads, []),
    {Else1, ReadsElse} = ann_reads(Else, Reads, []),
    Reads1 = ordsets:union(Reads, ordsets:union(ReadsThen, ReadsElse)),
    ann_reads(Code, Reads1, [{ifte, Then1, Else1} | Acc]);
ann_reads([{Ann, I} | Code], Reads, Acc) ->
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
    ann_reads(Code, Reads1, [{Ann1, I} | Acc]);
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
        {'STR_EQ', A, B, C}                   -> Pure(A, [B, C]);
        {'STR_JOIN', A, B, C}                 -> Pure(A, [B, C]);
        {'INT_TO_STR', A, B}                  -> Pure(A, B);
        {'ADDR_TO_STR', A, B}                 -> Pure(A, B);
        {'STR_REVERSE', A, B}                 -> Pure(A, B);
        {'INT_TO_ADDR', A, B}                 -> Pure(A, B);
        {'VARIANT', A, B, C, D}               -> Pure(A, [B, C, D]);
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
        {'BALANCE', A}                        -> Pure(A, []);
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

var_writes(I) ->
    #{ write := W } = attributes(I),
    case W of
        {var, _} -> [W];
        _        -> []
    end.

independent({ifte, _, _}, _) -> false;
independent(_, {ifte, _, _}) -> false;
independent(I, J) ->
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
swap_instrs({#{ live_in := Live1, live_out := Live2 }, I}, {#{ live_in := Live2, live_out := Live3 }, J}) ->
    %% Since I and J are independent the J can't read or write anything in
    %% that I writes.
    WritesI = ordsets:subtract(Live2, Live1),
    %% Any final reads by J, that I does not read should be removed from Live2.
    #{ read := ReadsI } = attributes(I),
    ReadsJ  = ordsets:subtract(Live2, ordsets:union(Live3, ReadsI)),
    Live2_  = ordsets:subtract(ordsets:union([Live1, Live2, Live3]), ordsets:union(WritesI, ReadsJ)),
    {{#{ live_in => Live1,  live_out => Live2_ }, J},
     {#{ live_in => Live2_, live_out => Live3  }, I}}.

live_in(R,  #{ live_in  := LiveIn  }) -> ordsets:is_element(R, LiveIn).
live_out(R, #{ live_out := LiveOut }) -> ordsets:is_element(R, LiveOut).

%% -- Optimizations --

simplify([], _) -> [];
simplify([I | Code], Options) ->
    simpl_top(simpl_s(I, Options), simplify(Code, Options), Options).

simpl_s({ifte, Then, Else}, Options) ->
    {ifte, simplify(Then, Options), simplify(Else, Options)};
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
     ?RULE(r_write_to_dead_var)
    ].

rules() ->
    merge_rules() ++
    [?RULE(r_dup_to_push),
     ?RULE(r_swap_push),
     ?RULE(r_swap_write),
     ?RULE(r_inline)
    ].

%% Removing pushes that are immediately consumed.
r_push_consume({Ann1, {'PUSH', A}}, [{Ann2, {Op, R, ?a, B}} | Code]) when ?IsBinOp(Op) ->
    {[{merge_ann(Ann1, Ann2), {Op, R, A, B}}], Code};
r_push_consume({Ann1, {'PUSH', B}}, [{Ann2, {Op, R, A, ?a}} | Code]) when A /= ?a, ?IsBinOp(Op) ->
    {[{merge_ann(Ann1, Ann2), {Op, R, A, B}}], Code};
r_push_consume({Ann1, {'PUSH', A}}, [{Ann2, {'STORE', R, ?a}} | Code]) ->
    {[{merge_ann(Ann1, Ann2), {'STORE', R, A}}], Code};
r_push_consume({Ann1, {'PUSH', A}}, [{Ann2, {'POP', B}} | Code]) ->
    case live_out(B, Ann2) of
        true  -> {[{merge_ann(Ann1, Ann2), {'STORE', B, A}}], Code};
        false -> {[], Code}
    end;
%% Writing directly to memory instead of going through the accumulator.
r_push_consume({Ann1, {Op, ?a, A, B}}, [{Ann2, {'STORE', R, ?a}} | Code]) when ?IsBinOp(Op) ->
    {[{merge_ann(Ann1, Ann2), {Op, R, A, B}}], Code};

r_push_consume(_, _) -> false.

%% Changing PUSH A, DUPA to PUSH A, PUSH A enables further optimisations
r_dup_to_push({Ann1, Push={'PUSH', _}}, [{Ann2, 'DUPA'} | Code]) ->
    #{ live_in  := LiveIn  } = Ann1,
    Ann1_ = Ann1#{ live_out => LiveIn },
    Ann2_ = Ann2#{ live_in  => LiveIn },
    {[{Ann1_, Push}, {Ann2_, Push}], Code};
r_dup_to_push(_, _) -> false.

%% Move PUSH A past non-stack instructions.
r_swap_push(PushA = {_, Push = {'PUSH', _}}, [IA = {_, I} | Code]) ->
    case independent(Push, I) of
        true ->
            {I1, Push1} = swap_instrs(PushA, IA),
            {[I1, Push1], Code};
        false -> false
    end;
r_swap_push(_, _) -> false.

%% Match up writes to variables with instructions further down.
r_swap_write(IA = {_, I}, [JA = {_, J} | Code]) ->
    case {var_writes(I), independent(I, J)} of
        {[_], true} ->
            {J1, I1} = swap_instrs(IA, JA),
            r_swap_write([J1], I1, Code);
        _ -> false
    end;
r_swap_write(_, _) -> false.

r_swap_write(Pre, IA = {_, I}, Code0 = [JA = {_, J} | Code]) ->
    case apply_rules_once(merge_rules(), IA, Code0) of
        {_Rule, New, Rest} ->
            {lists:reverse(Pre) ++ New, Rest};
        false ->
            case independent(I, J) of
                false -> false;
                true  ->
                    {J1, I1} = swap_instrs(IA, JA),
                    r_swap_write([J1 | Pre], I1, Code)
            end
    end;
r_swap_write(_, _, []) -> false.

%% Inline stores
r_inline(I = {_, {'STORE', R = {var, _}, A = {arg, _}}}, Code) ->
    %% Not when A is var unless updating the annotations properly.
    r_inline([I], R, A, Code);
r_inline(_, _) -> false.

r_inline(Acc, R, A, [{Ann, I} | Code]) ->
    #{ write := W, pure := Pure } = attributes(I),
    Inl = fun(X) when X == R -> A; (X) -> X end,
    case not live_in(R, Ann) orelse not Pure orelse lists:member(W, [R, A]) of
        true  -> false;
        false ->
            case I of
                {Op, S, B, C} when ?IsBinOp(Op), B == R orelse C == R ->
                    Acc1 = [{Ann, {Op, S, Inl(B), Inl(C)}} | Acc],
                    case r_inline(Acc1, R, A, Code) of
                        false -> {lists:reverse(Acc1), Code};
                        {New, Rest} -> {New, Rest}
                    end;
                _ -> r_inline([{Ann, I} | Acc], R, A, Code)
            end
    end;
r_inline(_Acc, _, _, []) -> false.

%% Shortcut write followed by final read
r_one_shot_var({Ann1, {Op, R = {var, _}, A, B}}, [{Ann2, J} | Code]) when ?IsBinOp(Op) ->
    Copy = case J of
               {'PUSH', R}     -> {write_to, ?a};
               {'STORE', S, R} -> {write_to, S};
               _               -> false
           end,
    case {live_out(R, Ann2), Copy} of
        {false, {write_to, X}} ->
            {[{merge_ann(Ann1, Ann2), {Op, X, A, B}}], Code};
        _ -> false
    end;
r_one_shot_var(_, _) -> false.

%% Remove writes to dead variables
r_write_to_dead_var({Ann, {Op, R = {var, _}, A, B}}, Code) when ?IsBinOp(Op) ->
    case live_out(R, Ann) of
        false ->
            %% Subtle: we still have to pop the stack if any of the arguments
            %% came from there. In this case we pop to R, which we know is
            %% unused.
            {[{Ann, {'POP', R}} || X <- [A, B], X == ?a], Code};
        true -> false
    end;
r_write_to_dead_var({Ann, {'STORE', R = {var, _}, A}}, Code) when A /= ?a ->
    case live_out(R, Ann) of
        false ->
            case Code of
                []                  -> {[], []};
                [{Ann1, I} | Code1] ->
                    {[], [{merge_ann(Ann, Ann1), I} | Code1]}
            end;
        true  -> false
    end;
r_write_to_dead_var(_, _) -> false.


%% Desugar and specialize and remove annotations
unannotate({ifte, Then, Else}) -> [{ifte, unannotate(Then), unannotate(Else)}];
unannotate(Code) when is_list(Code) ->
    lists:flatmap(fun unannotate/1, Code);
unannotate({_Ann, I}) -> [I].

%% Desugar and specialize and remove annotations
desugar({'ADD', ?a, ?i(1), ?a})     -> [aeb_fate_code:inc()];
desugar({'SUB', ?a, ?a, ?i(1)})     -> [aeb_fate_code:dec()];
desugar({ifte, Then, Else}) -> [{ifte, desugar(Then), desugar(Else)}];
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
    Blocks  = optimize_blocks(Blocks0),
    Labels  = maps:from_list([ {Ref, I} || {I, {Ref, _}} <- with_ixs(Blocks) ]),
    BBs     = [ set_labels(Labels, B) || B <- Blocks ],
    maps:from_list(BBs).

%% -- Break up scode into basic blocks --

blocks(Code) ->
    Top = make_ref(),
    blocks([{Top, Code}], []).

blocks([], Acc) ->
    lists:reverse(Acc);
blocks([{Ref, Code} | Blocks], Acc) ->
    block(Ref, Code, [], Blocks, Acc).

block(Ref, [], CodeAcc, Blocks, BlockAcc) ->
    blocks(Blocks, [{Ref, lists:reverse(CodeAcc)} | BlockAcc]);
block(Ref, [{ifte, Then, Else} | Code], Acc, Blocks, BlockAcc) ->
    ThenLbl = make_ref(),
    RestLbl = make_ref(),
    block(Ref, Else ++ [{jump, RestLbl}],
               [{jumpif, ThenLbl} | Acc],
               [{ThenLbl, Then ++ [{jump, RestLbl}]},
                {RestLbl, Code} | Blocks],
               BlockAcc);
block(Ref, [I | Code], Acc, Blocks, BlockAcc) ->
    block(Ref, Code, [I | Acc], Blocks, BlockAcc).

%% -- Reorder, inline, and remove dead blocks --

optimize_blocks(Blocks) ->
    %% We need to look at the last instruction a lot, so reverse all blocks.
    Rev       = fun(Bs) -> [ {Ref, lists:reverse(Code)} || {Ref, Code} <- Bs ] end,
    RBlocks   = Rev(Blocks),
    RBlockMap = maps:from_list(RBlocks),
    RBlocks1  = reorder_blocks(RBlocks, []),
    RBlocks2  = [ {Ref, inline_block(RBlockMap, Ref, Code)} || {Ref, Code} <- RBlocks1 ],
    RBlocks3  = remove_dead_blocks(RBlocks2),
    RBlocks4  = [ {Ref, use_returnr(Code)} || {Ref, Code} <- RBlocks3 ],
    Rev(RBlocks4).

%% Choose the next block based on the final jump.
reorder_blocks([], Acc) ->
    lists:reverse(Acc);
reorder_blocks([{Ref, Code} | Blocks], Acc) ->
    reorder_blocks(Ref, Code, Blocks, Acc).

reorder_blocks(Ref, Code, Blocks, Acc) ->
    Acc1 = [{Ref, Code} | Acc],
    case Code of
        ['RETURN'|_]        -> reorder_blocks(Blocks, Acc1);
        [{'RETURNR', _}|_]  -> reorder_blocks(Blocks, Acc1);
        [{jump, L}|_]     ->
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
    Jump = fun({jump, A})   -> [A || not maps:is_key(A, Live)];
              ({jumpif, A}) -> [A || not maps:is_key(A, Live)];
              (_)                 -> [] end,
    New  = lists:flatmap(Jump, Code),
    chase_labels(New ++ Ls, Map, Live#{ L => true }).

%% Replace PUSH, RETURN by RETURNR
use_returnr(['RETURN', {'PUSH', A} | Code]) ->
    [{'RETURNR', A} | Code];
use_returnr(Code) -> Code.

%% -- Translate label refs to indices --

set_labels(Labels, {Ref, Code}) when is_reference(Ref) ->
    {maps:get(Ref, Labels), [ set_labels(Labels, I) || I <- Code ]};
set_labels(Labels, {jump, Ref})   -> aeb_fate_code:jump(maps:get(Ref, Labels));
set_labels(Labels, {jumpif, Ref}) -> aeb_fate_code:jumpif(?a, maps:get(Ref, Labels));
set_labels(_, I) -> I.

%% -- Helpers ----------------------------------------------------------------

with_ixs(Xs) ->
    lists:zip(lists:seq(0, length(Xs) - 1), Xs).

keyfind_index(X, J, Xs) ->
    case [ I || {I, E} <- with_ixs(Xs), X == element(J, E) ] of
        [I | _] -> I;
        []      -> false
    end.

find_index(X, Xs) ->
    case lists:keyfind(X, 2, with_ixs(Xs)) of
        {I, _} -> I;
        false  -> false
    end.

