%%%-------------------------------------------------------------------
%%% @doc Case/switch lowering from Icode to structured scode
%%%-------------------------------------------------------------------
-module(aeso_fate_case).

-export([split_to_scode/2]).

-include("aeso_fate_env.hrl").

split_to_scode(Env, {nosplit, Renames, Expr}) ->
    [switch_body, aeso_fate_debug:dbg_scoped_vars(Env, Renames, aeso_fate_codegen:to_scode(Env, Expr))];
split_to_scode(Env, {split, {tuple, _}, X, Alts}) ->
    {Def, Alts1} = catchall_to_scode(Env, X, Alts),
    Arg = aeso_fate_codegen:lookup_var(Env, X),
    Alt = case [ {Xs, Split} || {'case', {tuple, Xs}, Split} <- Alts1 ] of
            []            -> missing;
            [{Xs, S} | _] ->
                {Code, Env1} = match_tuple(Env, Arg, Xs),
                [Code, split_to_scode(Env1, S)]
          end,
    case Def == missing andalso Alt /= missing of
       true  -> Alt;
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
    Arg   = aeso_fate_codegen:lookup_var(Env, X),
    [{switch, Arg, boolean, SAlts, Def}];
split_to_scode(Env, {split, {list, _}, X, Alts}) ->
    {Def, Alts1} = catchall_to_scode(Env, X, Alts),
    Arg = aeso_fate_codegen:lookup_var(Env, X),
    GetAlt = fun(P) ->
                 case [C || C = {'case', Pat, _} <- Alts1, Pat == P orelse is_tuple(Pat) andalso element(1, Pat) == P] of
                     []      -> missing;
                     [{'case', nil, S} | _]           -> split_to_scode(Env, S);
                     [{'case', {'::', Y, Z}, S} | _] ->
                         {I, Env1} = aeso_fate_codegen:bind_local(Y, Env),
                         {J, Env2} = aeso_fate_codegen:bind_local(Z, Env1),
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
    literal_split_to_scode(Env, Type, aeso_fate_codegen:lookup_var(Env, X), Alts1, Def);
split_to_scode(Env, {split, {variant, Cons}, X, Alts}) ->
    {Def, Alts1} = catchall_to_scode(Env, X, Alts),
    Arg = aeso_fate_codegen:lookup_var(Env, X),
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
        {[SAlt], missing} when SAlt /= missing -> SAlt;
        {SAlts, _} -> [{switch, Arg, SType, SAlts, Def}]
    end.

literal_split_to_scode(_Env, _Type, Arg, [], Def) ->
    {switch, Arg, boolean, [missing, missing], Def};
literal_split_to_scode(Env, Type, Arg, [{'case', Lit, Body} | Alts], Def) when Type == integer; Type == string ->
    True = split_to_scode(Env, Body),
    False = case Alts of [] -> missing; _  -> literal_split_to_scode(Env, Type, Arg, Alts, missing) end,
    SLit = case Lit of {int, N} -> N; {string, S} -> aeb_fate_data:make_string(S) end,
    [aeb_fate_ops:eq(?a, Arg, ?i(SLit)),
     {switch, ?a, boolean, [False, True], Def}].

catchall_to_scode(Env, X, Alts) -> catchall_to_scode(Env, X, Alts, []).
catchall_to_scode(Env, X, [{'case', {var, Y}, Split} | _], Acc) ->
    Env1 = aeso_fate_codegen:bind_var(Y, aeso_fate_codegen:lookup_var(Env, X), Env),
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
    {J,    Env1} = aeso_fate_codegen:bind_local(X, Env),
    {Code, Env2} = match_tuple(Env1, I + 1, Elem, Arg, Xs),
    {[Elem({var, J}, ?i(I), Arg), Code], Env2};
match_tuple(Env, _, _, _, []) ->
    {[], Env}.


