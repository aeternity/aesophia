%%%-------------------------------------------------------------------
%%% @doc Code generation: lower Icode to structured scode with env mgmt
%%%-------------------------------------------------------------------
-module(aeso_fate_codegen).

-export([
    functions_to_scode/5,
    function_to_scode/10,
    init_env/7,
    next_var/1,
    bind_var/3,
    bind_local/2,
    notail/1,
    lookup_var/2,
    to_scode/2,
    call_to_scode/3
]).

-include("aeso_fate_env.hrl").

functions_to_scode(ChildContracts, ContractName, Functions, SavedFreshNames, Options) ->
    FunNames = maps:keys(Functions),
    maps:from_list(
        [ {aeso_fcode_to_fate:make_function_name(Name),
           function_to_scode(ChildContracts, ContractName, FunNames, Name, Attrs, Args, Body, Type, SavedFreshNames, Options)}
        || {Name, #{args   := Args,
                     body   := Body,
                     attrs  := Attrs,
                     return := Type}} <- maps:to_list(Functions)]).

function_to_scode(ChildContracts, ContractName, Functions, Name, Attrs0, Args, Body, ResType, SavedFreshNames, Options) ->
    {ArgTypes, ResType1} = aeso_fate_types:typesig_to_scode(Args, ResType),
    Attrs = [ A || A <- Attrs0, A == private orelse A == payable ],
    Env = init_env(ChildContracts, ContractName, Functions, Name, Args, SavedFreshNames, Options),
    ArgsNames = [ X || {X, _} <- lists:reverse(Env#env.vars) ],
    SCode = to_scode(Env, Body),
    DbgSCode = aeso_fate_debug:dbg_contract(Env) ++ aeso_fate_debug:dbg_loc(Env, Attrs0) ++ aeso_fate_debug:dbg_scoped_vars(Env, ArgsNames, SCode),
    {Attrs, {ArgTypes, ResType1}, DbgSCode}.

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

next_var(#env{ vars = Vars }) ->
    1 + lists:max([-1 | [J || {_, {var, J}} <- Vars]]).

bind_var(Name, Var, Env = #env{ vars = Vars }) ->
    Env#env{ vars = [{Name, Var} | Vars] }.

bind_local(Name, Env) ->
    I = next_var(Env),
    {I, bind_var(Name, {var, I}, Env)}.

notail(Env) -> Env#env{ tailpos = false }.

lookup_var(#env{vars = Vars}, X) ->
    case lists:keyfind(X, 1, Vars) of
        {_, Var} -> Var;
        false    -> aeso_fcode_to_fate:code_error({unbound_variable, X, Vars})
    end.

%% -- Lowering --
to_scode(Env, T) ->
    try aeso_fate_term:term_to_fate(Env, T) of
        V ->
            FAnn = element(2, T),
            [aeso_fate_debug:dbg_loc(Env, FAnn), push(?i(V))]
    catch throw:not_a_fate_value ->
        to_scode1(Env, T)
    end.

to_scode1(Env, {lit, Ann, L}) ->
    [ aeso_fate_debug:dbg_loc(Env, Ann), push(?i(aeso_fate_term:lit_to_fate(Env, L))) ];
to_scode1(Env, {nil, Ann}) ->
    [ aeso_fate_debug:dbg_loc(Env, Ann), aeb_fate_ops:nil(?a) ];
to_scode1(Env, {var, Ann, X}) ->
    [ aeso_fate_debug:dbg_loc(Env, Ann), push(lookup_var(Env, X)) ];
to_scode1(Env, {con, Ann, Ar, I, As}) ->
    N = length(As),
    [ aeso_fate_debug:dbg_loc(Env, Ann),
      [to_scode(notail(Env), A) || A <- As],
      aeb_fate_ops:variant(?a, ?i(Ar), ?i(I), ?i(N)) ];
to_scode1(Env, {tuple, Ann, As}) ->
    N = length(As),
    [ aeso_fate_debug:dbg_loc(Env, Ann),
      [ to_scode(notail(Env), A) || A <- As ],
      tuple(N) ];
to_scode1(Env, {proj, Ann, E, I}) ->
    [ aeso_fate_debug:dbg_loc(Env, Ann), to_scode(notail(Env), E), aeb_fate_ops:element_op(?a, ?i(I), ?a) ];
to_scode1(Env, {set_proj, Ann, R, I, E}) ->
    [ aeso_fate_debug:dbg_loc(Env, Ann), to_scode(notail(Env), E), to_scode(notail(Env), R), aeb_fate_ops:setelement(?a, ?i(I), ?a, ?a) ];
to_scode1(Env, {op, Ann, Op, Args}) ->
    [ aeso_fate_debug:dbg_loc(Env, Ann) | call_to_scode(Env, aeso_fate_opmap:op_to_scode(Op), Args) ];
to_scode1(Env, {'let', Ann, X, {var, _, Y}, Body}) ->
    Env1 = bind_var(X, lookup_var(Env, Y), Env),
    [ aeso_fate_debug:dbg_loc(Env, Ann) | aeso_fate_debug:dbg_scoped_vars(Env1, [X], to_scode(Env1, Body)) ];
to_scode1(Env, {'let', Ann, X, Expr, Body}) ->
    {I, Env1} = bind_local(X, Env),
    SCode = [ to_scode(notail(Env), Expr), aeb_fate_ops:store({var, I}, {stack, 0}), to_scode(Env1, Body) ],
    [ aeso_fate_debug:dbg_loc(Env, Ann) | aeso_fate_debug:dbg_scoped_vars(Env1, [X], SCode) ];
to_scode1(Env = #env{ current_function = Fun, tailpos = true, debug_info = false }, {def, Ann, Fun, Args}) ->
    {Vars, Code, _Env} =
        lists:foldl(fun(Arg, {Is, Acc, Env1}) ->
                        {I, Env2} = bind_local("_", Env1),
                        ArgCode   = to_scode(notail(Env2), Arg),
                        Acc1 = [Acc, ArgCode, aeb_fate_ops:store({var, I}, ?a)],
                        {[I | Is], Acc1, Env2}
                    end, {[], [], Env}, Args),
    [ aeso_fate_debug:dbg_loc(Env, Ann),
      Code,
      [ aeb_fate_ops:store({arg, I}, {var, J}) || {I, J} <- lists:zip(lists:seq(0, length(Vars) - 1), lists:reverse(Vars)) ],
      loop ];
to_scode1(Env, {def, Ann, Fun, Args}) ->
    FName = aeso_fcode_to_fate:make_function_id(Fun),
    Lbl   = aeb_fate_data:make_string(FName),
    [ aeso_fate_debug:dbg_loc(Env, Ann) | call_to_scode(Env, local_call(Env, ?i(Lbl)), Args) ];
to_scode1(Env, {funcall, Ann, Fun, Args}) ->
    [ aeso_fate_debug:dbg_loc(Env, Ann) | call_to_scode(Env, [to_scode(Env, Fun), local_call(Env, ?a)], Args) ];
to_scode1(Env, {builtin, Ann, B, Args}) ->
    [ aeso_fate_debug:dbg_loc(Env, Ann) | aeso_fate_builtins:builtin_to_scode(Env, B, Args) ];
to_scode1(Env, {remote, Ann, ArgsT, RetT, Ct, Fun, [Gas, Value, Protected | Args]}) ->
    Lbl = aeso_fcode_to_fate:make_function_id(Fun),
    {ArgTypes, RetType0} = aeso_fate_types:typesig_to_scode([{"_", T} || T <- ArgsT], RetT),
    ArgType = ?i(aeb_fate_data:make_typerep({tuple, ArgTypes})),
    RetType = ?i(aeb_fate_data:make_typerep(RetType0)),
    SCode = case Protected of
        {lit, _, {bool, false}} ->
            case Gas of
                {builtin, _, call_gas_left, _} ->
                    Call = aeb_fate_ops:call_r(?a, Lbl, ArgType, RetType, ?a),
                    call_to_scode(Env, Call, [Ct, Value | Args]);
                _ ->
                    Call = aeb_fate_ops:call_gr(?a, Lbl, ArgType, RetType, ?a, ?a),
                    call_to_scode(Env, Call, [Ct, Value, Gas | Args])
            end;
        {lit, _, {bool, true}} ->
            Call = aeb_fate_ops:call_pgr(?a, Lbl, ArgType, RetType, ?a, ?a, ?i(true)),
            call_to_scode(Env, Call, [Ct, Value, Gas | Args]);
        _ ->
            Call = aeb_fate_ops:call_pgr(?a, Lbl, ArgType, RetType, ?a, ?a, ?a),
            call_to_scode(Env, Call, [Ct, Value, Gas, Protected | Args])
    end,
    [ aeso_fate_debug:dbg_loc(Env, Ann) | SCode ];
to_scode1(Env, {get_state, Ann, Reg}) -> [ aeso_fate_debug:dbg_loc(Env, Ann), push(?s(Reg)) ];
to_scode1(Env, {set_state, Ann, Reg, Val}) -> [ aeso_fate_debug:dbg_loc(Env, Ann) | call_to_scode(Env, [{'STORE', ?s(Reg), ?a}, tuple(0)], [Val]) ];
to_scode1(Env, {closure, Ann, Fun, FVs}) -> [ to_scode(Env, {tuple, Ann, [{lit, Ann, {string, aeso_fcode_to_fate:make_function_id(Fun)}}, FVs]}) ];
to_scode1(Env, {switch, Ann, Case}) -> [ aeso_fate_debug:dbg_loc(Env, Ann) | aeso_fate_case:split_to_scode(Env, Case) ].

local_call( Env = #env{debug_info = false}, Fun) when Env#env.tailpos -> aeb_fate_ops:call_t(Fun);
local_call(_Env, Fun)                                                 -> aeb_fate_ops:call(Fun).

call_to_scode(Env, CallCode, Args) -> [[to_scode(notail(Env), A) || A <- lists:reverse(Args)], CallCode].

%% PUSH and STORE ?a are the same, so we use STORE to make optimizations easier
push(A) -> {'STORE', ?a, A}.

tuple(0) -> push(?i({tuple, {}}));
tuple(N) -> aeb_fate_ops:tuple(?a, N).

with_ixs(Xs) -> lists:zip(lists:seq(0, length(Xs) - 1), Xs).


