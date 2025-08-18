%%%-------------------------------------------------------------------
%%% @doc Build FATE basic blocks from structured code (scode)
%%%-------------------------------------------------------------------
-module(aeso_fate_blocks).

-export([to_basic_blocks/1]).

-spec to_basic_blocks(map()) -> term().
to_basic_blocks(Funs) ->
    to_basic_blocks(maps:to_list(Funs), aeb_fate_code:new()).

to_basic_blocks([{Name, {Attrs, Sig, Code}}|Left], Acc) ->
    BB = bb(Name, Code ++ [aeb_fate_ops:return()]),
    to_basic_blocks(Left, aeb_fate_code:insert_fun(Name, Attrs, Sig, BB, Acc));
to_basic_blocks([], Acc) ->
    Acc.

bb(_Name, Code) ->
    Blocks0 = blocks(Code),
    Blocks1 = optimize_blocks(Blocks0),
    Blocks  = lists:flatmap(fun split_calls/1, Blocks1),
    Labels  = maps:from_list([ {Ref, I} || {I, {Ref, _}} <- with_ixs(Blocks) ]),
    BBs     = [ set_labels(Labels, B) || B <- Blocks ],
    maps:from_list(dbg_loc_filter(BBs)).

dbg_loc_filter(BBs) ->
    dbg_loc_filter(BBs, [], [], sets:new()).

dbg_loc_filter([], _, AllBlocks, _) ->
    lists:reverse(AllBlocks);
dbg_loc_filter([{I, []} | Rest], AllOps, AllBlocks, DbgLocs) ->
    dbg_loc_filter(Rest, [], [{I, lists:reverse(AllOps)} | AllBlocks], DbgLocs);
dbg_loc_filter([{I, [Op = {'DBG_LOC', _, _} | Ops]} | Rest], AllOps, AllBlocks, DbgLocs) ->
    case sets:is_element(Op, DbgLocs) of
        true  -> dbg_loc_filter([{I, Ops} | Rest], AllOps, AllBlocks, DbgLocs);
        false -> dbg_loc_filter([{I, Ops} | Rest], [Op | AllOps], AllBlocks, sets:add_element(Op, DbgLocs))
    end;
dbg_loc_filter([{I, [Op | Ops]} | Rest], AllOps, AllBlocks, DbgLocs) ->
    dbg_loc_filter([{I, Ops} | Rest], [Op | AllOps], AllBlocks, DbgLocs).

-type bbref() :: reference().
-record(blk, { ref :: bbref(), code :: list(), catchall = none :: bbref() | none }).

blocks(Code) ->
    Top = make_ref(),
    blocks([#blk{ref = Top, code = Code}], []).

blocks([], Acc) ->
    lists:reverse(Acc);
blocks([Blk | Blocks], Acc) ->
    block(Blk, [], Blocks, Acc).

block(#blk{ref = Ref, code = []}, CodeAcc, Blocks, BlockAcc) ->
    blocks(Blocks, [{Ref, lists:reverse(CodeAcc)} | BlockAcc]);
block(Blk = #blk{code = [switch_body | Code]}, Acc, Blocks, BlockAcc) ->
    block(Blk#blk{code = Code, catchall = none}, Acc, Blocks, BlockAcc);
block(Blk = #blk{code = [{switch, Arg, Type, Alts, Default} | Code], catchall = Catchall}, Acc, Blocks, BlockAcc) ->
    FreshBlk = fun(C, Ca) -> R = make_ref(), {R, [#blk{ref = R, code = C, catchall = Ca}]} end,
    {RestRef, RestBlk} = FreshBlk(Code, Catchall),
    {DefRef, DefBlk} =
        case Default of
            missing when Catchall == none -> FreshBlk([aeb_fate_ops:abort({immediate, <<"Incomplete patterns">>})], none);
            missing -> {Catchall, []};
            _       -> FreshBlk(Default ++ [{jump, RestRef}], Catchall)
        end,
    Pop = [{'POP', {var, 9999}} || Arg == {stack, 0}],
    {Blk1, Code1, AltBlks} =
        case Type of
            boolean ->
                [FalseCode, TrueCode] = Alts,
                {ThenRef, ThenBlk} = case TrueCode of missing -> {DefRef, []}; _ -> FreshBlk(TrueCode ++ [{jump, RestRef}], DefRef) end,
                ElseCode = case FalseCode of missing -> [{jump, DefRef}]; _ -> FalseCode ++ [{jump, RestRef}] end,
                case lists:usort(Alts) == [missing] of
                    true  -> {Blk#blk{code = Pop ++ [{jump, DefRef}]}, [], []};
                    false ->
                        case Arg of
                            {immediate, false} -> {Blk#blk{code = ElseCode}, [], ThenBlk};
                            {immediate, true}  -> {Blk#blk{code = []}, [{jump, ThenRef}], ThenBlk};
                            _                   -> {Blk#blk{code = ElseCode}, [{jumpif, Arg, ThenRef}], ThenBlk}
                        end
                end;
            tuple ->
                [TCode] = Alts,
                case TCode of
                    missing -> {Blk#blk{code = Pop ++ [{jump, DefRef}]}, [], []};
                    _       -> {Blk#blk{code = Pop ++ TCode ++ [{jump, RestRef}]}, [], []}
                end;
            {variant, [_]} ->
                [AltCode] = Alts,
                case AltCode of
                    missing -> {Blk#blk{code = Pop ++ [{jump, DefRef}]}, [], []};
                    _       -> {Blk#blk{code = Pop ++ AltCode ++ [{jump, RestRef}]}, [], []}
                end;
            {variant, _Ar} ->
                case lists:usort(Alts) == [missing] of
                    true  -> {Blk#blk{code = Pop ++ [{jump, DefRef}]}, [], []};
                    false ->
                        MkBlk = fun(missing) -> {DefRef, []}; (ACode) -> FreshBlk(ACode ++ [{jump, RestRef}], DefRef) end,
                        {AltRefs, AltBs} = lists:unzip(lists:map(MkBlk, Alts)),
                        {Blk#blk{code = []}, [{switch, Arg, AltRefs}], lists:append(AltBs)}
                end
        end,
    Blk2 = Blk1#blk{catchall = DefRef},
    block(Blk2, Code1 ++ Acc, DefBlk ++ RestBlk ++ AltBlks ++ Blocks, BlockAcc);
block(Blk = #blk{code = [I | Code]}, Acc, Blocks, BlockAcc) ->
    block(Blk#blk{code = Code}, [I | Acc], Blocks, BlockAcc).

optimize_blocks(Blocks) ->
    Rev = fun(Bs) -> [ {Ref, lists:reverse(Code)} || {Ref, Code} <- Bs ] end,
    RBlocks   = Rev(Blocks),
    RBlockMap = maps:from_list(RBlocks),
    RBlocks1  = reorder_blocks(RBlocks, []),
    RBlocks2  = [ {Ref, inline_block(RBlockMap, Ref, Code)} || {Ref, Code} <- RBlocks1 ],
    RBlocks3  = shortcut_jump_chains(RBlocks2),
    RBlocks4  = remove_dead_blocks(RBlocks3),
    RBlocks5  = [ {Ref, tweak_returns(Code)} || {Ref, Code} <- RBlocks4 ],
    Rev(RBlocks5).

reorder_blocks([], Acc) -> lists:reverse(Acc);
reorder_blocks([{Ref, Code} | Blocks], Acc) -> reorder_blocks(Ref, Code, Blocks, Acc).
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
                {Blocks1, [{L, Code1} | Blocks2]} -> reorder_blocks(L, Code1, Blocks1 ++ Blocks2, Acc1);
                {_, []} -> reorder_blocks(Blocks, Acc1)
            end
    end.

inline_block(BlockMap, Ref, [{jump, L} | Code] = Code0) when L /= Ref ->
    case maps:get(L, BlockMap, nocode) of
        Dest when length(Dest) < 3 -> inline_block(maps:remove(Ref, BlockMap), L, Dest) ++ Code;
        _ -> Code0
    end;
inline_block(_, _, Code) -> Code.

shortcut_jump_chains(RBlocks) ->
    Subst = lists:foldl(fun({L1, [{jump, L2}]}, Sub) -> Sub#{ L1 => maps:get(L2, Sub, L2) };
                           (_, Sub) -> Sub end, #{}, RBlocks),
    [ {Ref, update_labels(Subst, Code)} || {Ref, Code} <- RBlocks ].

update_labels(Sub, Ref) when is_reference(Ref) -> maps:get(Ref, Sub, Ref);
update_labels(Sub, L) when is_list(L) -> lists:map(fun(X) -> update_labels(Sub, X) end, L);
update_labels(Sub, T) when is_tuple(T) -> list_to_tuple(update_labels(Sub, tuple_to_list(T)));
update_labels(_, X) -> X.

remove_dead_blocks(Blocks = [{Top, _} | _]) ->
    BlockMap   = maps:from_list(Blocks),
    LiveBlocks = chase_labels([Top], BlockMap, #{}),
    [ B || B = {L, _} <- Blocks, maps:is_key(L, LiveBlocks) ].

chase_labels([], _, Live) -> Live;
chase_labels([L | Ls], Map, Live) ->
    Code = maps:get(L, Map),
    Jump = fun({jump, A}) -> [A || not maps:is_key(A, Live)];
               ({jumpif, _, A})  -> [A || not maps:is_key(A, Live)];
               ({switch, _, As}) -> [A || A <- As, not maps:is_key(A, Live)];
               (_)               -> [] end,
    New  = lists:flatmap(Jump, Code),
    chase_labels(New ++ Ls, Map, Live#{ L => true }).

tweak_returns(['RETURN', {'PUSH', A} | Code])          -> [{'RETURNR', A} | Code];
tweak_returns(['RETURN' | Code = [{'CALL_T', _} | _]]) -> Code;
tweak_returns(['RETURN' | Code = [{'ABORT', _} | _]])  -> Code;
tweak_returns(['RETURN' | Code = [{'EXIT', _} | _]])   -> Code;
tweak_returns(['RETURN' | Code = [loop | _]])          -> Code;
tweak_returns(Code) -> Code.

split_calls({Ref, Code}) -> split_calls(Ref, Code, [], []).
split_calls(Ref, [], Acc, Blocks) -> lists:reverse([{Ref, lists:reverse(Acc)} | Blocks]);
split_calls(Ref, [I | Code], Acc, Blocks) when element(1, I) == 'CALL';
                                               element(1, I) == 'CALL_R';
                                               element(1, I) == 'CALL_GR';
                                               element(1, I) == 'CALL_PGR';
                                               element(1, I) == 'CREATE';
                                               element(1, I) == 'CLONE';
                                               element(1, I) == 'CLONE_G';
                                               element(1, I) == 'jumpif' ->
    split_calls(make_ref(), Code, [], [{Ref, lists:reverse([I | Acc])} | Blocks]);
split_calls(Ref, [{'ABORT', _} = I | _Code], Acc, Blocks) -> lists:reverse([{Ref, lists:reverse([I | Acc])} | Blocks]);
split_calls(Ref, [{'EXIT', _} = I | _Code], Acc, Blocks)  -> lists:reverse([{Ref, lists:reverse([I | Acc])} | Blocks]);
split_calls(Ref, [I | Code], Acc, Blocks) -> split_calls(Ref, Code, [I | Acc], Blocks).

set_labels(Labels, {Ref, Code}) when is_reference(Ref) -> {maps:get(Ref, Labels), [ set_labels(Labels, I) || I <- Code ]};
set_labels(_Labels, loop)              -> aeb_fate_ops:jump(0);
set_labels(Labels, {jump, Ref})        -> aeb_fate_ops:jump(maps:get(Ref, Labels));
set_labels(Labels, {jumpif, Arg, Ref}) -> aeb_fate_ops:jumpif(Arg, maps:get(Ref, Labels));
set_labels(Labels, {switch, Arg, Refs}) ->
    case [ maps:get(Ref, Labels) || Ref <- Refs ] of
        [R1, R2]     -> aeb_fate_ops:switch(Arg, R1, R2);
        [R1, R2, R3] -> aeb_fate_ops:switch(Arg, R1, R2, R3);
        Rs           -> aeb_fate_ops:switch(Arg, Rs)
    end;
set_labels(_, I) -> I.

with_ixs(Xs) -> lists:zip(lists:seq(0, length(Xs) - 1), Xs).


