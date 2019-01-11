%%%-------------------------------------------------------------------
%%% @author Ulf Norell
%%% @copyright (C) 2019, Aeternity Anstalt
%%% @doc
%%%     Fate backend for Sophia compiler
%%% @end
%%% Created : 11 Jan 2019
%%%
%%%-------------------------------------------------------------------
-module(aeso_icode_to_fate).

-include("aeso_icode.hrl").

-export([compile/2]).

%% -- Preamble ---------------------------------------------------------------

-define(TODO(What), error({todo, ?FILE, ?LINE, ?FUNCTION_NAME, What})).

-define(i(__X__), {immediate, __X__}).
-define(a, {stack, 0}).

-record(env, { args = [], stack = [], tailpos = true }).

%% -- Debugging --------------------------------------------------------------

%% debug(Options, Fmt) -> debug(Options, Fmt, []).
debug(Options, Fmt, Args) ->
    case proplists:get_value(debug, Options, true) of
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
    to_basic_blocks(SFuns1, Options).

functions_to_scode(Functions, Options) ->
    maps:from_list(
        [ {list_to_binary(Name), function_to_scode(Name, Args, Body, Type, Options)}
        || {Name, _Ann, Args, Body, Type} <- Functions, Name /= "init" ]).  %% TODO: skip init for now

function_to_scode(Name, Args, Body, Type, Options) ->
    debug(Options, "Compiling ~p ~p : ~p ->\n  ~p\n", [Name, Args, Type, Body]),
    ArgTypes = [ icode_type_to_fate(T) || {_, T} <- Args ],
    ResType  = icode_type_to_fate(Type),
    SCode    = to_scode(init_env(Args), Body),
    debug(Options, "  scode: ~p\n", [SCode]),
    {{ArgTypes, ResType}, SCode}.

%% -- Types ------------------------------------------------------------------

%% TODO: the Fate types don't seem to be specified anywhere...
icode_type_to_fate(word)           -> integer;
icode_type_to_fate(string)         -> string;
icode_type_to_fate({tuple, Types}) ->
    {tuple, lists:map(fun icode_type_to_fate/1, Types)};
icode_type_to_fate({list, Type})   ->
    {list, icode_type_to_fate(Type)};
icode_type_to_fate(typerep) -> typerep;
icode_type_to_fate(Type) -> ?TODO(Type).

%% -- Phase I ----------------------------------------------------------------
%%  Icode to structured assembly

%% -- Environment functions --

init_env(Args) ->
    #env{ args = Args, stack = [], tailpos = true }.

push_env(Type, Env) ->
    Env#env{ stack = [{"_", Type} | Env#env.stack] }.

notail(Env) -> Env#env{ tailpos = false }.

lookup_var(#env{ args = Args, stack = S }, X) ->
    case {keyfind_index(X, 1, S), keyfind_index(X, 1, Args)} of
        {false, false} -> false;
        {false, Arg}   -> {arg, Arg};
        {Local, _}     -> {stack, Local}
    end.

%% -- The compiler --

to_scode(_Env, #integer{ value = N }) ->
    [aeb_fate_code:push(?i(N))];    %% Doesn't exist (yet), translated by desugaring

to_scode(Env, #var_ref{name = X}) ->
    case lookup_var(Env, X) of
        false      -> error({unbound_variable, X, Env});
        {stack, N} -> [aeb_fate_code:dup(N)];
        {arg, N}   -> [aeb_fate_code:push({arg, N})]
    end;
to_scode(Env, #binop{ op = Op, left = A, right = B }) ->
    [ to_scode(notail(Env), B)
    , to_scode(push_env(binop_type_r(Op), Env), A)
    , binop_to_scode(Op) ];

to_scode(Env, #ifte{decision = Dec, then = Then, else = Else}) ->
    [ to_scode(notail(Env), Dec)
    , {ifte, to_scode(Env, Then), to_scode(Env, Else)} ];

to_scode(_Env, Icode) -> ?TODO(Icode).

%% -- Operators --

binop_types('+')  -> {word, word};
binop_types('-')  -> {word, word};
binop_types('==') -> {word, word};
binop_types(Op)   -> ?TODO(Op).

%% binop_type_l(Op) -> element(1, binop_types(Op)).
binop_type_r(Op) -> element(2, binop_types(Op)).

binop_to_scode('+') -> add_a_a_a();  %% Optimization introduces other variants
binop_to_scode('-') -> sub_a_a_a();
binop_to_scode('==') -> eq_a_a_a();
binop_to_scode(Op) -> ?TODO(Op).

add_a_a_a() -> aeb_fate_code:add(?a, ?a, ?a).
sub_a_a_a() -> aeb_fate_code:sub(?a, ?a, ?a).
eq_a_a_a() -> aeb_fate_code:eq(?a, ?a, ?a).

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
    debug(Options, "Optimizing ~s\n", [Name]),
    debug(Options, "  original  : ~p\n", [Code0]),
    Code1 = simplify(Code0),
    debug(Options, "  simplified: ~p\n", [Code1]),
    Code2 = desugar(Code1),
    debug(Options, "  desugared : ~p\n", [Code2]),
    {{Args, Res}, Code2}.

simplify([]) -> [];
simplify([I | Code]) ->
    simpl_top(simpl_s(I), simplify(Code)).

simpl_s({ifte, Then, Else}) ->
    {ifte, simplify(Then), simplify(Else)};
simpl_s(I) -> I.

%% add_i 0 --> nop
simpl_top({'ADD', _, ?i(0), _}, Code) -> Code;
%% push n, add_a --> add_i n
simpl_top({'PUSH', ?a, ?i(N)},
          [{'ADD', ?a, ?a, ?a} | Code]) ->
    simpl_top( aeb_fate_code:add(?a, ?i(N), ?a), Code);
%% push n, add_i m --> add_i (n + m)
simpl_top({'PUSH', ?a, ?i(N)}, [{'ADD', ?a, ?i(M), ?a} | Code]) ->
    simpl_top(aeb_fate_code:push(?i(N + M)), Code);
%% add_i n, add_i m --> add_i (n + m)
simpl_top({'ADD', ?a, ?i(N), ?a}, [{'ADD', ?a, ?i(M), ?a} | Code]) ->
    simpl_top({'ADD', ?a, ?i(N + M), ?a}, Code);

simpl_top(I, Code) -> [I | Code].

%% Desugar and specialize
desugar({'ADD', ?a, ?i(1), ?a})     -> [aeb_fate_code:inca()];
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

bb(Name, Code, Options) ->
    Blocks0 = blocks(Code),
    Blocks  = optimize_blocks(Blocks0),
    Labels  = maps:from_list([ {Ref, I} || {I, {Ref, _}} <- with_ixs(Blocks) ]),
    BBs     = [ set_labels(Labels, B) || B <- Blocks ],
    debug(Options, "Final code for ~s:\n  ~p\n", [Name, BBs]),
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
    Rev(RBlocks3).

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

