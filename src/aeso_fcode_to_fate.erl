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
    {length(Locals), Env#env{ locals = Locals ++ [Name] }}.

notail(Env) -> Env#env{ tailpos = false }.

lookup_var(Env = #env{ args = Args, locals = Locals }, X) ->
    case {find_index(X, Locals), keyfind_index(X, 1, Args)} of
        {false, false} -> error({unbound_variable, X, Env});
        {false, Arg}   -> {arg, Arg};
        {Local, _}     -> {var, Local}
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

to_scode(Env, {switch, Expr, Alts}) ->
    [ to_scode(notail(Env), Expr),
      alts_to_scode(Env, Alts) ];

to_scode(_Env, Icode) -> ?TODO(Icode).

alts_to_scode(Env, [{'case', {var, X}, Body}]) ->
    {I, Env1} = bind_local(X, Env),
    [ aeb_fate_code:store({var, I}, {stack, 0}),
      to_scode(Env1, Body) ];
alts_to_scode(Env, Alts = [{'case', {tuple, Pats}, Body}]) ->
    Xs = lists:flatmap(fun({var, X}) -> [X]; (_) -> [] end, Pats),
    N  = length(Pats),
    case length(Xs) == N of
        false -> ?TODO(Alts);
        true  ->
            {Code, Env1} = match_tuple(Env, Xs),
            [Code, to_scode(Env1, Body)]
    end;
alts_to_scode(_Env, Alts) ->
    ?TODO(Alts).

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

optimize_fun(_Funs, Name, {{Args, Res}, Code}, Options) ->
    Code0 = flatten(Code),
    debug(opt, Options, "Optimizing ~s\n", [Name]),
    ACode = annotate_code(Code0),
    debug(opt, Options, "  original:\n~s\n", [pp_ann("    ", ACode)]),
    Code1 = simplify(ACode, Options),
    debug(opt, Options, "  optimized:\n~s\n", [pp_ann("    ", Code1)]),
    Code2 = desugar(Code1),
    {{Args, Res}, Code2}.

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
    #{ write := Ws } = attributes(I),
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
    #{ read := Rs, write := Ws, pure := Pure } = attributes(I),
    Reads1  =
        case Pure andalso length(Ws) == 1 andalso not ordsets:is_element(hd(Ws), Reads) of
            %% This is a little bit dangerous: if writing to a dead variable, we ignore
            %% the reads. Relies on dead writes to be removed by the
            %% optimisations below (r_write_to_dead_var).
            true  -> Reads;
            false -> ordsets:union(Reads, Rs)
        end,
    LiveIn  = ordsets:intersection(Reads1, WritesIn),
    LiveOut = ordsets:intersection(Reads, WritesOut),
    Ann1    = #{ live_in => LiveIn, live_out => LiveOut },
    ann_reads(Code, Reads1, [{Ann1, I} | Acc]);
ann_reads([], Reads, Acc) -> {Acc, Reads}.

%% Read/write to variables and purity.
attributes(I) ->
    Set  = fun(L) when is_list(L) -> ordsets:from_list([X || X <- L, X /= ?a]);
              (X)                 -> ordsets:from_list([X || X /= ?a]) end,
    WR   = fun(W, R) -> #{read => Set(R), write => Set(W), pure => false}  end,
    R    = fun(X) -> WR([], X) end,
    W    = fun(X) -> WR(X, []) end,
    None = WR([], []),
    Pure = fun(A) -> A#{ pure := true } end,
    case I of
        'RETURN'                              -> None;
        {'RETURNR', A}                        -> R(A);
        {'CALL', _}                           -> None;
        {'CALL_R', A, _}                      -> R(A);
        {'CALL_T', _}                         -> None;
        {'CALL_TR', A, _}                     -> R(A);
        {'JUMP', _}                           -> Pure(None);
        {'JUMPIF', A, _}                      -> Pure(R(A));
        {'SWITCH_V2', A, _, _}                -> Pure(R(A));
        {'SWITCH_V3', A, _, _, _}             -> Pure(R(A));
        {'SWITCH_VN', A, _}                   -> Pure(R(A));
        {'PUSH', A}                           -> Pure(R(A));
        'DUPA'                                -> Pure(None);
        {'DUP', A}                            -> Pure(R(A));
        {'POP', A}                            -> Pure(W(A));
        {'STORE', A, B}                       -> Pure(WR(A, B));
        'INCA'                                -> Pure(None);
        {'INC', A}                            -> Pure(WR(A, A));
        'DECA'                                -> Pure(None);
        {'DEC', A}                            -> Pure(WR(A, A));
        {'ADD', A, B, C}                      -> Pure(WR(A, [B, C]));
        {'SUB', A, B, C}                      -> Pure(WR(A, [B, C]));
        {'MUL', A, B, C}                      -> Pure(WR(A, [B, C]));
        {'DIV', A, B, C}                      -> Pure(WR(A, [B, C]));
        {'MOD', A, B, C}                      -> Pure(WR(A, [B, C]));
        {'POW', A, B, C}                      -> Pure(WR(A, [B, C]));
        {'LT', A, B, C}                       -> Pure(WR(A, [B, C]));
        {'GT', A, B, C}                       -> Pure(WR(A, [B, C]));
        {'EQ', A, B, C}                       -> Pure(WR(A, [B, C]));
        {'ELT', A, B, C}                      -> Pure(WR(A, [B, C]));
        {'EGT', A, B, C}                      -> Pure(WR(A, [B, C]));
        {'NEQ', A, B, C}                      -> Pure(WR(A, [B, C]));
        {'AND', A, B, C}                      -> Pure(WR(A, [B, C]));
        {'OR', A, B, C}                       -> Pure(WR(A, [B, C]));
        {'NOT', A, B}                         -> Pure(WR(A, B));
        {'TUPLE', _}                          -> Pure(None);
        {'ELEMENT', A, B, C}                  -> Pure(WR(A, [B, C]));
        {'MAP_EMPTY', A}                      -> Pure(W(A));
        {'MAP_LOOKUP', A, B, C}               -> Pure(WR(A, [B, C]));
        {'MAP_LOOKUPD', A, B, C, D}           -> Pure(WR(A, [B, C, D]));
        {'MAP_UPDATE', A, B, C, D}            -> Pure(WR(A, [B, C, D]));
        {'MAP_DELETE', A, B, C}               -> Pure(WR(A, [B, C]));
        {'MAP_MEMBER', A, B, C}               -> Pure(WR(A, [B, C]));
        {'MAP_FROM_LIST', A, B}               -> Pure(WR(A, B));
        {'NIL', A}                            -> Pure(W(A));
        {'IS_NIL', A, B}                      -> Pure(WR(A, B));
        {'CONS', A, B, C}                     -> Pure(WR(A, [B, C]));
        {'HD', A, B}                          -> Pure(WR(A, B));
        {'TL', A, B}                          -> Pure(WR(A, B));
        {'LENGTH', A, B}                      -> Pure(WR(A, B));
        {'STR_EQ', A, B, C}                   -> Pure(WR(A, [B, C]));
        {'STR_JOIN', A, B, C}                 -> Pure(WR(A, [B, C]));
        {'INT_TO_STR', A, B}                  -> Pure(WR(A, B));
        {'ADDR_TO_STR', A, B}                 -> Pure(WR(A, B));
        {'STR_REVERSE', A, B}                 -> Pure(WR(A, B));
        {'INT_TO_ADDR', A, B}                 -> Pure(WR(A, B));
        {'VARIANT', A, B, C, D}               -> Pure(WR(A, [B, C, D]));
        {'VARIANT_TEST', A, B, C}             -> Pure(WR(A, [B, C]));
        {'VARIANT_ELEMENT', A, B, C}          -> Pure(WR(A, [B, C]));
        'BITS_NONEA'                          -> Pure(None);
        {'BITS_NONE', A}                      -> Pure(W(A));
        'BITS_ALLA'                           -> Pure(None);
        {'BITS_ALL', A}                       -> Pure(W(A));
        {'BITS_ALL_N', A, B}                  -> Pure(WR(A, B));
        {'BITS_SET', A, B, C}                 -> Pure(WR(A, [B, C]));
        {'BITS_CLEAR', A, B, C}               -> Pure(WR(A, [B, C]));
        {'BITS_TEST', A, B, C}                -> Pure(WR(A, [B, C]));
        {'BITS_SUM', A, B}                    -> Pure(WR(A, B));
        {'BITS_OR', A, B, C}                  -> Pure(WR(A, [B, C]));
        {'BITS_AND', A, B, C}                 -> Pure(WR(A, [B, C]));
        {'BITS_DIFF', A, B, C}                -> Pure(WR(A, [B, C]));
        {'ADDRESS', A}                        -> Pure(W(A));
        {'BALANCE', A}                        -> Pure(W(A));
        {'ORIGIN', A}                         -> Pure(W(A));
        {'CALLER', A}                         -> Pure(W(A));
        {'GASPRICE', A}                       -> Pure(W(A));
        {'BLOCKHASH', A}                      -> Pure(W(A));
        {'BENEFICIARY', A}                    -> Pure(W(A));
        {'TIMESTAMP', A}                      -> Pure(W(A));
        {'GENERATION', A}                     -> Pure(W(A));
        {'MICROBLOCK', A}                     -> Pure(W(A));
        {'DIFFICULTY', A}                     -> Pure(W(A));
        {'GASLIMIT', A}                       -> Pure(W(A));
        {'GAS', A}                            -> Pure(W(A));
        {'LOG0', A, B}                        -> R([A, B]);
        {'LOG1', A, B, C}                     -> R([A, B, C]);
        {'LOG2', A, B, C, D}                  -> R([A, B, C, D]);
        {'LOG3', A, B, C, D, E}               -> R([A, B, C, D, E]);
        {'LOG4', A, B, C, D, E, F}            -> R([A, B, C, D, E, F]);
        'DEACTIVATE'                          -> None;
        {'SPEND', A, B}                       -> R([A, B]);
        {'ORACLE_REGISTER', A, B, C, D, E, F} -> WR(A, [B, C, D, E, F]);
        'ORACLE_QUERY'                        -> None;  %% TODO
        'ORACLE_RESPOND'                      -> None;  %% TODO
        'ORACLE_EXTEND'                       -> None;  %% TODO
        'ORACLE_GET_ANSWER'                   -> None;  %% TODO
        'ORACLE_GET_QUESTION'                 -> None;  %% TODO
        'ORACLE_QUERY_FEE'                    -> None;  %% TODO
        'AENS_RESOLVE'                        -> None;  %% TODO
        'AENS_PRECLAIM'                       -> None;  %% TODO
        'AENS_CLAIM'                          -> None;  %% TODO
        'AENS_UPDATE'                         -> None;  %% TODO
        'AENS_TRANSFER'                       -> None;  %% TODO
        'AENS_REVOKE'                         -> None;  %% TODO
        'ECVERIFY'                            -> Pure(None);  %% TODO
        'SHA3'                                -> Pure(None);  %% TODO
        'SHA256'                              -> Pure(None);  %% TODO
        'BLAKE2B'                             -> Pure(None);  %% TODO
        {'ABORT', A}                          -> R(A);
        {'EXIT', A}                           -> R(A);
        'NOP'                                 -> Pure(None)
    end.

merge_ann(#{ live_in := LiveIn }, #{ live_out := LiveOut }) ->
    #{ live_in => LiveIn, live_out => LiveOut }.

%% When swapping two instructions
swap_ann(#{ live_in := Live1, live_out := Live2 }, #{ live_in := Live2, live_out := Live3 }) ->
    Live2_ = ordsets:union([Live1, Live2, Live3]), %% Conservative approximation
    {#{ live_in => Live1,  live_out => Live2_ },
     #{ live_in => Live2_, live_out => Live3 }}.

%% live_in(R,  #{ live_in  := LiveIn  }) -> ordsets:is_element(R, LiveIn).
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

apply_rules([], I, Code, _) ->
    [I | Code];
apply_rules([{_RName, Rule} | Rules], I, Code, Options) ->
    Cons = fun(X, Xs) -> simpl_top(X, Xs, Options) end,
    case Rule(I, Code) of
        false       -> apply_rules(Rules, I, Code, Options);
        {New, Rest} ->
            debug(opt_rules, Options, "Applied ~p:\n~s  ==>\n~s", [_RName, pp_ann("    ", [I | Code]), pp_ann("    ", New ++ Rest)]),
            lists:foldr(Cons, Rest, New)
    end.

-define(RULE(Name), {Name, fun Name/2}).

rules() ->
    [?RULE(r_push_consume),
     ?RULE(r_dup_to_push),
     ?RULE(r_swap_instrs),
     ?RULE(r_one_shot_var),
     ?RULE(r_write_to_dead_var)
    ].

%% Removing pushes that are immediately consumed.
r_push_consume({Ann1, {'PUSH', A}}, [{Ann2, {Op, R, ?a, B}} | Code]) when ?IsBinOp(Op) ->
    {[{merge_ann(Ann1, Ann2), {Op, R, A, B}}], Code};
r_push_consume({Ann1, {'PUSH', B}}, [{Ann2, {Op, R, A, ?a}} | Code]) when A /= ?a, ?IsBinOp(Op) ->
    {[{merge_ann(Ann1, Ann2), {Op, R, A, B}}], Code};
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
r_dup_to_push(I = {Ann, {'PUSH', A}}, [{_, 'DUPA'} | Code]) ->
    #{ live_in := Live } = Ann,
    Ann1 = #{ live_in => Live, live_out => Live },
    {[{Ann1, {'PUSH', A}}, I], Code};
r_dup_to_push(_, _) -> false.

%% Move PUSH A past an operator. Make sure the next instruction isn't writing
%% to A, pushing to the stack or reading the accumulator.
r_swap_instrs({Ann1, {'PUSH', A}}, [{Ann2, I = {Op, R, B, C}} | Code]) when ?IsBinOp(Op), A /= R, A /= ?a, B /= ?a, C /= ?a ->
    {Ann1_, Ann2_} = swap_ann(Ann1, Ann2),
    {[{Ann1_, I}, {Ann2_, {'PUSH', A}}], Code};

%% Move writes to a variable as late as possible
r_swap_instrs({Ann1, I1 = {Op1, R = {var, _}, A, B}}, [{Ann2, I2 = {Op2, S, C, D}} | Code])
        when ?IsBinOp(Op1), ?IsBinOp(Op2),
             element(1, S) /= var orelse S < R,
             S /= A, S /= B, C /= R, D /= R,
             A /= ?a andalso B /= ?a orelse S /= ?a andalso C /= ?a andalso D /= ?a ->
    {Ann1_, Ann2_} = swap_ann(Ann1, Ann2),
    {[{Ann1_, I2}, {Ann2_, I1}], Code};
r_swap_instrs(_, _) -> false.

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
r_write_to_dead_var(_, _) -> false.


%% Desugar and specialize and remove annotations
desugar({_Ann, {'ADD', ?a, ?i(1), ?a}})     -> [aeb_fate_code:inc()];
desugar({_Ann, {'SUB', ?a, ?a, ?i(1)}})     -> [aeb_fate_code:dec()];
desugar({ifte, Then, Else}) -> [{ifte, desugar(Then), desugar(Else)}];
desugar(Code) when is_list(Code) ->
    lists:flatmap(fun desugar/1, Code);
desugar({_Ann, I}) -> [I].

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

