%%%-------------------------------------------------------------------
%%% @copyright (C) 2018, Aeternity Anstalt
%%% @doc
%%%     Compiler builtin functions for Aeterinty Sophia language.
%%% @end
%%% Created : 20 Dec 2018
%%%
%%%-------------------------------------------------------------------

-module(aeso_builtins).

-export([ builtin_function/1
        , check_event_type/1
        , used_builtins/1 ]).

-import(aeso_ast_to_icode, [prim_call/5]).

-include_lib("aebytecode/include/aeb_opcodes.hrl").
-include("aeso_icode.hrl").

used_builtins(#funcall{ function = #var_ref{ name = {builtin, Builtin} }, args = Args }) ->
    lists:umerge(dep_closure([Builtin]), used_builtins(Args));
used_builtins([H|T]) ->
  lists:umerge(used_builtins(H), used_builtins(T));
used_builtins(T) when is_tuple(T) ->
  used_builtins(tuple_to_list(T));
used_builtins(M) when is_map(M) ->
  used_builtins(maps:to_list(M));
used_builtins(_) -> [].

builtin_deps(Builtin) ->
    lists:usort(builtin_deps1(Builtin)).

builtin_deps1({map_lookup_default, Type}) -> [{map_lookup, Type}];
builtin_deps1({map_get, Type})            -> [{map_lookup, Type}];
builtin_deps1(map_member)                 -> [{map_lookup, word}];
builtin_deps1({map_upd, Type})            -> [{map_get, Type}, map_put];
builtin_deps1({map_upd_default, Type})    -> [{map_lookup_default, Type}, map_put];
builtin_deps1(map_from_list)              -> [map_put];
builtin_deps1(str_equal)                  -> [str_equal_p];
builtin_deps1(string_concat)              -> [string_concat_inner1, string_copy, string_shift_copy];
builtin_deps1(int_to_str)                 -> [{baseX_int, 10}];
builtin_deps1(addr_to_str)                -> [{baseX_int, 58}];
builtin_deps1({baseX_int, X})             -> [{baseX_int_pad, X}];
builtin_deps1({baseX_int_pad, X})         -> [{baseX_int_encode, X}];
builtin_deps1({baseX_int_encode, X})      -> [{baseX_int_encode_, X}, {baseX_tab, X}, {baseX_digits, X}];
builtin_deps1({bytes_to_str, _})          -> [bytes_to_str_worker];
builtin_deps1(string_reverse)             -> [string_reverse_];
builtin_deps1(require)                    -> [abort];
builtin_deps1(_)                          -> [].

dep_closure(Deps) ->
    case lists:umerge(lists:map(fun builtin_deps/1, Deps)) of
        []    -> Deps;
        Deps1 -> lists:umerge(Deps, dep_closure(Deps1))
    end.

%% Helper functions/macros
v(X) when is_atom(X) -> v(atom_to_list(X));
v(X) when is_list(X) -> #var_ref{name = X}.

option_none()  -> {tuple, [{integer, 0}]}.
option_some(X) -> {tuple, [{integer, 1}, X]}.

-define(HASH_BYTES, 32).

-define(call(Fun, Args), #funcall{ function = #var_ref{ name = {builtin, Fun} }, args = Args }).
-define(I(X), {integer, X}).
-define(V(X), v(X)).
-define(A(Op), aeb_opcodes:mnemonic(Op)).
-define(LET(Var, Expr, Body), {switch, Expr, [{v(Var), Body}]}).
-define(DEREF(Var, Ptr, Body), {switch, operand(Ptr), [{{tuple, [v(Var)]}, Body}]}).
-define(NXT(Ptr), op('+', Ptr, 32)).
-define(NEG(A), op('/', A, {unop, '-', {integer, 1}})).
-define(BYTE(Ix, Word), op('byte', Ix, Word)).

-define(EQ(A, B), op('==', A, B)).
-define(LT(A, B), op('<', A, B)).
-define(GT(A, B), op('>', A, B)).
-define(ADD(A, B), op('+', A, B)).
-define(SUB(A, B), op('-', A, B)).
-define(MUL(A, B), op('*', A, B)).
-define(DIV(A, B), op('div', A, B)).
-define(MOD(A, B), op('mod', A, B)).
-define(EXP(A, B), op('^', A, B)).
-define(AND(A, B), op('&&', A, B)).

%% Bit shift operations takes their arguments backwards!?
-define(BSL(X, B), op('bsl', ?MUL(B, 8), X)).
-define(BSR(X, B), op('bsr', ?MUL(B, 8), X)).

op(Op, A, B) -> {binop, Op, operand(A), operand(B)}.

operand(A) when is_atom(A) -> v(A);
operand(I) when is_integer(I) -> {integer, I};
operand(T) -> T.

check_event_type(Icode) ->
    case maps:get(event_type, Icode) of
        {variant_t, Cons} ->
            check_event_type(Cons, Icode);
        _ ->
            error({event_should_be_variant_type})
    end.

check_event_type(Evts, Icode) ->
    [ check_event_type(Name, Ix, T, Icode)
      || {constr_t, Ann, {con, _, Name}, Types} <- Evts,
         {Ix, T} <- lists:zip(aeso_syntax:get_ann(indices, Ann), Types) ].

check_event_type(EvtName, Ix, Type, Icode) ->
    VMType =
        try
           aeso_ast_to_icode:ast_typerep(Type, Icode)
        catch _:_ ->
            error({EvtName, could_not_resolve_type, Type})
        end,
    case {Ix, VMType, Type} of
        {indexed, word, _}      -> ok;
        {notindexed, string, _} -> ok;
        {notindexed, _, {bytes_t, _, N}} when N > 32 -> ok;
        {indexed, _, _}         -> error({EvtName, indexed_field_should_be_word, is, VMType});
        {notindexed, _, _}      -> error({EvtName, payload_should_be_string, is, VMType})
    end.

bfun(B, {IArgs, IExpr, IRet}) ->
    {{builtin, B}, [private], IArgs, IExpr, IRet}.

builtin_function(BF) ->
    case BF of
        {event, EventT}            -> bfun(BF, builtin_event(EventT));
        abort                      -> bfun(BF, builtin_abort());
        require                    -> bfun(BF, builtin_require());
        {map_lookup, Type}         -> bfun(BF, builtin_map_lookup(Type));
        map_put                    -> bfun(BF, builtin_map_put());
        map_delete                 -> bfun(BF, builtin_map_delete());
        map_size                   -> bfun(BF, builtin_map_size());
        {map_get, Type}            -> bfun(BF, builtin_map_get(Type));
        {map_lookup_default, Type} -> bfun(BF, builtin_map_lookup_default(Type));
        map_member                 -> bfun(BF, builtin_map_member());
        {map_upd, Type}            -> bfun(BF, builtin_map_upd(Type));
        {map_upd_default, Type}    -> bfun(BF, builtin_map_upd_default(Type));
        map_from_list              -> bfun(BF, builtin_map_from_list());
        list_concat                -> bfun(BF, builtin_list_concat());
        string_length              -> bfun(BF, builtin_string_length());
        string_concat              -> bfun(BF, builtin_string_concat());
        string_concat_inner1       -> bfun(BF, builtin_string_concat_inner1());
        string_copy                -> bfun(BF, builtin_string_copy());
        string_shift_copy          -> bfun(BF, builtin_string_shift_copy());
        str_equal_p                -> bfun(BF, builtin_str_equal_p());
        str_equal                  -> bfun(BF, builtin_str_equal());
        popcount                   -> bfun(BF, builtin_popcount());
        int_to_str                 -> bfun(BF, builtin_int_to_str());
        addr_to_str                -> bfun(BF, builtin_addr_to_str());
        {baseX_int, X}             -> bfun(BF, builtin_baseX_int(X));
        {baseX_digits, X}          -> bfun(BF, builtin_baseX_digits(X));
        {baseX_tab, X}             -> bfun(BF, builtin_baseX_tab(X));
        {baseX_int_pad, X}         -> bfun(BF, builtin_baseX_int_pad(X));
        {baseX_int_encode, X}      -> bfun(BF, builtin_baseX_int_encode(X));
        {baseX_int_encode_, X}     -> bfun(BF, builtin_baseX_int_encode_(X));
        {bytes_to_int, N}          -> bfun(BF, builtin_bytes_to_int(N));
        {bytes_to_str, N}          -> bfun(BF, builtin_bytes_to_str(N));
        bytes_to_str_worker        -> bfun(BF, builtin_bytes_to_str_worker());
        string_reverse             -> bfun(BF, builtin_string_reverse());
        string_reverse_            -> bfun(BF, builtin_string_reverse_())
    end.

%% Event primitive (dependent on Event type)
%%
%% We need to switch on the event and prepare the correct #event for icode_to_asm
%% NOTE: we assume all errors are already checked!
builtin_event(EventT) ->
    A         = fun(X) -> aeb_opcodes:mnemonic(X) end,
    VIx       = fun(Ix) -> v(lists:concat(["v", Ix])) end,
    ArgPats   = fun(Ts) -> [ VIx(Ix) || Ix <- lists:seq(0, length(Ts) - 1) ] end,
    Payload = %% Should put data ptr, length on stack.
        fun([])            -> {inline_asm, [A(?PUSH1), 0, A(?PUSH1), 0]};
           ([{{id, _, "string"}, V}]) ->
                {seq, [V, {inline_asm, [A(?DUP1), A(?MLOAD),  %% length, ptr
                       A(?SWAP1), A(?PUSH1), 32, A(?ADD)]}]}; %% ptr+32, length
           ([{{bytes_t, _, N}, V}]) -> {seq, [V, {integer, N}, {inline_asm, A(?SWAP1)}]}
        end,
    Ix =
        fun({bytes_t, _, N}, V) when N < 32 -> ?BSR(V, 32 - N);
           (_, V) -> V end,
    Clause =
        fun(_Tag, {con, _, Con}, IxTypes) ->
            Types     = [ T || {_Ix, T} <- IxTypes ],
            Indexed   = [ Ix(Type, Var) || {Var, {indexed, Type}} <- lists:zip(ArgPats(Types), IxTypes) ],
            Data      = [ {Type, Var} || {Var, {notindexed, Type}} <- lists:zip(ArgPats(Types), IxTypes) ],
            {ok, <<EvtIndexN:256>>} = eblake2:blake2b(?HASH_BYTES, list_to_binary(Con)),
            EvtIndex  = {integer, EvtIndexN},
            {event, lists:reverse(Indexed) ++ [EvtIndex], Payload(Data)}
        end,
    Pat = fun(Tag, Types) -> {tuple, [{integer, Tag} | ArgPats(Types)]} end,

    {variant_t, Cons} = EventT,
    Tags              = lists:seq(0, length(Cons) - 1),

    {[{"e", event}],
     {switch, v(e),
         [{Pat(Tag, Types), Clause(Tag, Con, lists:zip(aeso_syntax:get_ann(indices, Ann), Types))}
          || {Tag, {constr_t, Ann, Con, Types}} <- lists:zip(Tags, Cons) ]},
     {tuple, []}}.

%% Abort primitive.
builtin_abort() ->
    A = fun(X) -> aeb_opcodes:mnemonic(X) end,
    {[{"s", string}],
     {inline_asm, [A(?PUSH1),0,  %% Push a dummy 0 for the first arg
                   A(?REVERT)]}, %% Stack: 0,Ptr
     {tuple,[]}}.

builtin_require() ->
    {[{"c", word}, {"msg", string}],
     {ifte, ?V(c), {tuple, []}, ?call(abort, [?V(msg)])},
     {tuple, []}}.

%% Map primitives
builtin_map_lookup(Type) ->
    Ret = aeso_icode:option_typerep(Type),
    {[{"m", word}, {"k", word}],
     prim_call(?PRIM_CALL_MAP_GET, #integer{value = 0},
               [#var_ref{name = "m"}, #var_ref{name = "k"}],
               [word, word], Ret),
     Ret}.

builtin_map_put() ->
    %% We don't need the types for put.
    {[{"m", word}, {"k", word}, {"v", word}],
     prim_call(?PRIM_CALL_MAP_PUT, #integer{value = 0},
               [v(m), v(k), v(v)], [word, word, word], word),
     word}.

builtin_map_delete() ->
    {[{"m", word}, {"k", word}],
     prim_call(?PRIM_CALL_MAP_DELETE, #integer{value = 0},
               [v(m), v(k)], [word, word], word),
     word}.

builtin_map_size() ->
    {[{"m", word}],
     prim_call(?PRIM_CALL_MAP_SIZE, #integer{value = 0},
               [v(m)], [word], word),
     word}.

%% Map builtins
builtin_map_get(Type) ->
    %% function map_get(m, k) =
    %%   switch(map_lookup(m, k))
    %%     Some(v) => v
    {[{"m", word}, {"k", word}],
     {switch, ?call({map_lookup, Type}, [v(m), v(k)]), [{option_some(v(v)), v(v)}]},
     Type}.

builtin_map_lookup_default(Type) ->
    %% function map_lookup_default(m, k, default) =
    %%   switch(map_lookup(m, k))
    %%     None    => default
    %%     Some(v) => v
    {[{"m", word}, {"k", word}, {"default", Type}],
     {switch, ?call({map_lookup, Type}, [v(m), v(k)]),
         [{option_none(),     v(default)},
          {option_some(v(v)), v(v)}]},
     Type}.

builtin_map_member() ->
    %% function map_member(m, k) : bool =
    %%   switch(Map.lookup(m, k))
    %%     None => false
    %%     _    => true
    {[{"m", word}, {"k", word}],
     {switch, ?call({map_lookup, word}, [v(m), v(k)]),
         [{option_none(), {integer, 0}},
          {{var_ref, "_"}, {integer, 1}}]},
     word}.

builtin_map_upd(Type) ->
    %% function map_upd(map, key, fun) =
    %%   map_put(map, key, fun(map_get(map, key)))
    {[{"map", word}, {"key", word}, {"valfun", word}],
     ?call(map_put,
        [v(map), v(key),
         #funcall{ function = v(valfun),
                   args     = [?call({map_get, Type}, [v(map), v(key)])] }]),
     word}.

builtin_map_upd_default(Type) ->
    %% function map_upd(map, key, val, fun) =
    %%   map_put(map, key, fun(map_lookup_default(map, key, val)))
    {[{"map", word}, {"key", word}, {"val", word}, {"valfun", word}],
     ?call(map_put,
        [v(map), v(key),
         #funcall{ function = v(valfun),
                   args     = [?call({map_lookup_default, Type}, [v(map), v(key), v(val)])] }]),
     word}.

builtin_map_from_list() ->
    %% function map_from_list(xs, acc) =
    %%   switch(xs)
    %%     [] => acc
    %%     (k, v) :: xs => map_from_list(xs, acc { [k] = v })
    {[{"xs", {list, {tuple, [word, word]}}}, {"acc", word}],
     {switch, v(xs),
        [{{list, []}, v(acc)},
         {{binop, '::', {tuple, [v(k), v(v)]}, v(ys)},
          ?call(map_from_list,
            [v(ys), ?call(map_put, [v(acc), v(k), v(v)])])}]},
     word}.

%% list_concat
%%
%% Concatenates two lists.
builtin_list_concat() ->
    {[{"l1", {list, word}}, {"l2", {list, word}}],
     {switch, v(l1),
        [{{list, []}, v(l2)},
         {{binop, '::', v(hd), v(tl)},
          {binop, '::', v(hd), ?call(list_concat, [v(tl), v(l2)])}}
        ]
     },
     word}.

builtin_string_length() ->
    %% function length(str) =
    %%   switch(str)
    %%      {n} -> n  // (ab)use the representation
    {[{"s", string}],
     ?DEREF(n, s, ?V(n)),
     word}.

%% str_concat - concatenate two strings
%%
%% Unless the second string is the empty string, a new string is created at the
%% top of the Heap and the address to it is returned. The tricky bit is when
%% the words from the second string has to be shifted to fit next to the first
%% string.
builtin_string_concat() ->
    {[{"s1", string}, {"s2", string}],
     ?DEREF(n1, s1,
     ?DEREF(n2, s2,
        {ifte, ?EQ(n1, 0),
            ?V(s2), %% First string is empty return second string
            {ifte, ?EQ(n2, 0),
                ?V(s1), %% Second string is empty return first string
                ?LET(ret, {inline_asm, [?A(?MSIZE)]},
                    {seq, [?ADD(n1, n2), {inline_asm, [?A(?MSIZE), ?A(?MSTORE)]}, %% Store total len
                           ?call(string_concat_inner1, [?V(n1), ?NXT(s1), ?V(n2), ?NXT(s2)]),
                           {inline_asm, [?A(?POP)]}, %% Discard fun ret val
                           ?V(ret)                   %% Put the actual return value
                          ]})}
        }
     )),
     word}.

builtin_string_concat_inner1() ->
    %% Copy all whole words from the first string, and set up for word fusion
    %% Special case when the length of the first string is divisible by 32.
    {[{"n1", word}, {"p1", pointer}, {"n2", word}, {"p2", pointer}],
     ?LET(w1, ?call(string_copy, [?V(n1), ?V(p1)]),
        ?LET(nx, ?MOD(n1, 32),
        {ifte, ?EQ(nx, 0),
            ?LET(w2, ?call(string_copy, [?V(n2), ?V(p2)]),
                {seq, [?V(w2), {inline_asm, [?A(?MSIZE), ?A(?MSTORE), ?A(?MSIZE)]}]}),
            ?call(string_shift_copy, [?V(nx), ?V(w1), ?V(n2), ?V(p2)])
        })),
     word}.

builtin_string_copy() ->
    {[{"n", word}, {"p", pointer}],
     ?DEREF(w, p,
        {ifte, ?GT(n, 31),
            {seq, [?V(w), {inline_asm, [?A(?MSIZE), ?A(?MSTORE)]},
                   ?call(string_copy, [?SUB(n, 32), ?NXT(p)])]},
            ?V(w)
        }),
     word}.

builtin_string_shift_copy() ->
    {[{"off", word}, {"dst", word}, {"n", word}, {"p", pointer}],
     ?DEREF(w, p,
        {seq, [?ADD(dst, ?BSR(w, off)), {inline_asm, [?A(?MSIZE), ?A(?MSTORE)]},
               {ifte, ?GT(n, ?SUB(32, off)),
                    ?call(string_shift_copy, [?V(off), ?BSL(w, ?SUB(32, off)), ?SUB(n, 32), ?NXT(p)]),
                    {inline_asm, [?A(?MSIZE)]}}]
        }),
     word}.

builtin_str_equal_p() ->
    %% function str_equal_p(n, p1, p2) =
    %%   if(n =< 0) true
    %%   else
    %%      let w1 = *p1
    %%      let w2 = *p2
    %%      w1 == w2 && str_equal_p(n - 32, p1 + 32, p2 + 32)
    {[{"n", word}, {"p1", pointer}, {"p2", pointer}],
     {ifte, ?LT(n, 1),
         ?I(1),
         ?DEREF(w1, p1,
         ?DEREF(w2, p2,
             ?AND(?EQ(w1, w2),
                  ?call(str_equal_p, [?SUB(n, 32), ?NXT(p1), ?NXT(p2)]))))},
     word}.

builtin_str_equal() ->
    %% function str_equal(s1, s2) =
    %%   let n1 = length(s1)
    %%   let n2 = length(s2)
    %%   n1 == n2 && str_equal_p(n1, s1 + 32, s2 + 32)
    {[{"s1", string}, {"s2", string}],
     ?DEREF(n1, s1,
     ?DEREF(n2, s2,
         ?AND(?EQ(n1, n2), ?call(str_equal_p, [?V(n1), ?NXT(s1), ?NXT(s2)]))
     )),
     word}.

%% Count the number of 1s in a bit field.
builtin_popcount() ->
    %% function popcount(bits, acc) =
    %%   if (bits == 0) acc
    %%   else popcount(bits bsr 1, acc + bits band 1)
    {[{"bits", word}, {"acc", word}],
     {ifte, ?EQ(bits, 0),
        ?V(acc),
        ?call(popcount, [op('bsr', 1, bits), ?ADD(acc, op('band', bits, 1))])
     }, word}.

builtin_int_to_str() ->
    {[{"i", word}], ?call({baseX_int, 10}, [?V(i)]), word}.

builtin_baseX_tab(_X = 10) ->
    {[{"ix", word}], ?ADD($0, ix), word};
builtin_baseX_tab(_X = 58) ->
    <<Fst32:256>> = <<"123456789ABCDEFGHJKLMNPQRSTUVWXY">>,
    <<Lst26:256>> = <<"Zabcdefghijkmnopqrstuvwxyz", 0:48>>,
    {[{"ix", word}],
     {ifte, ?LT(ix, 32),
         ?BYTE(ix, Fst32),
         ?BYTE(?SUB(ix, 32), Lst26)
     },
     word}.

builtin_baseX_int(X) ->
    {[{"w", word}],
     ?LET(ret, {inline_asm, [?A(?MSIZE)]},
        {seq, [?call({baseX_int_pad, X}, [?V(w), ?I(0), ?I(0)]), {inline_asm, [?A(?POP)]}, ?V(ret)]}),
     word}.

builtin_baseX_int_pad(X = 10) ->
    {[{"src", word}, {"ix", word}, {"dst", word}],
     {ifte, ?LT(src, 0),
        ?call({baseX_int_encode, X}, [?NEG(src), ?I(1), ?BSL($-, 31)]),
        ?call({baseX_int_encode, X}, [?V(src), ?V(ix), ?V(dst)])},
     word};
builtin_baseX_int_pad(X = 16) ->
    {[{"src", word}, {"ix", word}, {"dst", word}],
        ?call({baseX_int_encode, X}, [?V(src), ?V(ix), ?V(dst)]),
     word};
builtin_baseX_int_pad(X = 58) ->
    {[{"src", word}, {"ix", word}, {"dst", word}],
     {ifte, ?GT(?ADD(?DIV(ix, 31), ?BYTE(ix, src)), 0),
         ?call({baseX_int_encode, X}, [?V(src), ?V(ix), ?V(dst)]),
         ?call({baseX_int_pad, X}, [?V(src), ?ADD(ix, 1), ?ADD(dst, ?BSL($1, ?SUB(31, ix)))])},
     word}.

builtin_baseX_int_encode(X) ->
    {[{"src", word}, {"ix", word}, {"dst", word}],
     ?LET(n, ?call({baseX_digits, X}, [?V(src), ?I(0)]),
        {seq, [?ADD(n, ?ADD(ix, 1)), {inline_asm, [?A(?MSIZE), ?A(?MSTORE)]},
               ?call({baseX_int_encode_, X}, [?V(src), ?V(dst), ?EXP(X, n), ?V(ix)])]}),
     word}.

builtin_baseX_int_encode_(X) ->
    {[{"src", word}, {"dst", word}, {"fac", word}, {"ix", word}],
     {ifte, ?EQ(fac, 0),
         {seq, [?V(dst), {inline_asm, [?A(?MSIZE), ?A(?MSTORE), ?A(?MSIZE)]}]},
         {ifte, ?EQ(ix, 32),
              %% We've filled a word, write it and start on new word
              {seq, [?V(dst), {inline_asm, [?A(?MSIZE), ?A(?MSTORE)]},
                     ?call({baseX_int_encode_, X}, [?V(src), ?I(0), ?V(fac), ?I(0)])]},
              ?call({baseX_int_encode_, X},
                    [?MOD(src, fac), ?ADD(dst, ?BSL(?call({baseX_tab, X}, [?DIV(src, fac)]), ?SUB(31, ix))),
                     ?DIV(fac, X), ?ADD(ix, 1)])}
     },
     word}.

builtin_baseX_digits(X) ->
    {[{"x0", word}, {"dgts", word}],
     ?LET(x1, ?DIV(x0, X),
        {ifte, ?EQ(x1, 0), ?V(dgts), ?call({baseX_digits, X}, [?V(x1), ?ADD(dgts, 1)])}),
     word}.

builtin_bytes_to_int(32) ->
    {[{"w", word}], ?V(w), word};
builtin_bytes_to_int(N) when N < 32 ->
    {[{"w", word}], ?BSR(w, 32 - N), word};
builtin_bytes_to_int(N) when N > 32 ->
    LastFullWord = N div 32 - 1,
    Body = case N rem 32 of
                0 -> ?DEREF(n, ?ADD(b, LastFullWord * 32), ?V(n));
                R ->
                    ?DEREF(hi, ?ADD(b, LastFullWord * 32),
                    ?DEREF(lo, ?ADD(b, (LastFullWord + 1) * 32),
                    ?ADD(?BSR(lo, 32 - R), ?BSL(hi, R))))
           end,
    {[{"b", pointer}], Body, word}.

builtin_bytes_to_str_worker() ->
    <<Tab:256>> = <<"0123456789ABCDEF________________">>,
    {[{"w", word}, {"offs", word}, {"acc", word}],
     {seq, [{ifte, ?AND(?GT(offs, 0), ?EQ(0, ?MOD(offs, 16))),
                    {seq, [?V(acc), {inline_asm, [?A(?MSIZE), ?A(?MSTORE)]}]},
                    {inline_asm, []}},
            {ifte, ?EQ(offs, 32), {inline_asm, [?A(?MSIZE)]},
                ?LET(b,  ?BYTE(offs, w),
                ?LET(lo, ?BYTE(?MOD(b, 16), Tab),
                ?LET(hi, ?BYTE(op('bsr', 4 , b), Tab),
                ?call(bytes_to_str_worker,
                      [?V(w), ?ADD(offs, 1), ?ADD(?BSL(acc, 2), ?ADD(?BSL(hi, 1), lo))]))))
            }
           ]},
     word}.

builtin_bytes_to_str(N) when N =< 32 ->
    {[{"w", word}],
     ?LET(ret, {inline_asm, [?A(?MSIZE)]},
     {seq, [?I(N * 2), {inline_asm, [?A(?MSIZE), ?A(?MSTORE)]},
            ?call(bytes_to_str_worker, [?V(w), ?I(0), ?I(0)]),
            {inline_asm, [?A(?POP)]},
            ?V(ret)]}),
     string};
builtin_bytes_to_str(N) when N > 32 ->
    Work = fun(I) ->
            [?DEREF(w, ?ADD(p, 32 * I), ?call(bytes_to_str_worker, [?V(w), ?I(0), ?I(0)])),
             {inline_asm, [?A(?POP)]}]
           end,
    {[{"p", pointer}],
     ?LET(ret, {inline_asm, [?A(?MSIZE)]},
     {seq, [?I(N * 2), {inline_asm, [?A(?MSIZE), ?A(?MSTORE)]}] ++
           lists:append([ Work(I) || I <- lists:seq(0, (N + 31) div 32 - 1) ]) ++
           [?V(ret)]}),
     string}.

builtin_string_reverse() ->
    {[{"s", string}],
     ?DEREF(n, s,
     ?LET(ret, {inline_asm, [?A(?MSIZE)]},
         {seq, [?V(n), {inline_asm, [?A(?MSIZE), ?A(?MSTORE)]},
                ?call(string_reverse_, [?NXT(s), ?I(0), ?I(31), ?SUB(?V(n), 1)]),
                {inline_asm, [?A(?POP)]}, ?V(ret)]})),
     word}.

builtin_string_reverse_() ->
    {[{"p", pointer}, {"x", word}, {"i1", word}, {"i2", word}],
     {ifte, ?LT(i2, 0),
         {seq, [?V(x), {inline_asm, [?A(?MSIZE), ?A(?MSTORE), ?A(?MSIZE)]}]},
         ?LET(p1, ?ADD(p, ?MUL(?DIV(i2, 32), 32)),
         ?DEREF(w, p1,
         ?LET(b, ?BYTE(?MOD(i2, 32), w),
         {ifte, ?LT(i1, 0),
             {seq, [?V(x), {inline_asm, [?A(?MSIZE), ?A(?MSTORE)]},
                    ?call(string_reverse_,
                          [?V(p), ?BSL(b, 31), ?I(30), ?SUB(i2, 1)])]},
             ?call(string_reverse_,
                   [?V(p), ?ADD(x, ?BSL(b, i1)), ?SUB(i1, 1), ?SUB(i2, 1)])})))},
     word}.

builtin_addr_to_str() ->
    {[{"a", word}], ?call({baseX_int, 58}, [?V(a)]), word}.

