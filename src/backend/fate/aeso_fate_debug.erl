%%%-------------------------------------------------------------------
%%% @doc Debug helpers and annotations for FATE backend
%%%-------------------------------------------------------------------
-module(aeso_fate_debug).

-export([is_debug/2, debug/3,
         dbg_contract/1, dbg_loc/2,
         dbg_scoped_vars/3, dbg_scoped_var/4,
         is_fresh_name/1, dbg_undef/2]).

-include("aeso_fate_env.hrl").

is_debug(Tag, Options) ->
    Tags = proplists:get_value(debug, Options, []),
    Tags == all orelse lists:member(Tag, Tags).

debug(Tag, Options, Fun) ->
    case is_debug(Tag, Options) of
        true  -> Fun();
        false -> ok
    end.

dbg_contract(#env{debug_info = false}) -> [];
dbg_contract(#env{contract = Contract}) ->
    [{'DBG_CONTRACT', {immediate, Contract}}].

dbg_loc(#env{debug_info = false}, _) -> [];
dbg_loc(_Env, Ann) ->
    File = case proplists:get_value(file, Ann, no_file) of
                no_file -> "";
                F       -> F
            end,
    Line = proplists:get_value(line, Ann, undefined),
    case Line of
        undefined -> [];
        _         -> [{'DBG_LOC', {immediate, File}, {immediate, Line}}]
    end.

dbg_scoped_vars(#env{debug_info = false}, _, SCode) -> SCode;
dbg_scoped_vars(_Env, [], SCode) -> SCode;
dbg_scoped_vars(Env, [{SavedVarName, Var} | Rest], SCode) ->
    dbg_scoped_vars(Env, Rest, dbg_scoped_var(Env, SavedVarName, Var, SCode));
dbg_scoped_vars(Env = #env{saved_fresh_names = SavedFreshNames}, [Var | Rest], SCode) ->
    SavedVarName = maps:get(Var, SavedFreshNames, Var),
    dbg_scoped_vars(Env, Rest, dbg_scoped_var(Env, SavedVarName, Var, SCode)).

dbg_scoped_var(Env, SavedVarName, Var, SCode) ->
    case SavedVarName == "_" orelse is_fresh_name(SavedVarName) of
        true -> SCode;
        false ->
            Register = aeso_fate_codegen:lookup_var(Env, Var),
            Def      = [{'DBG_DEF',   {immediate, SavedVarName}, Register}],
            Undef    = [{'DBG_UNDEF', {immediate, SavedVarName}, Register}],
            Def ++ dbg_undef(Undef, SCode)
    end.

is_fresh_name([$% | _]) -> true;
is_fresh_name(_) -> false.

dbg_undef(_Undef, missing) -> missing;
dbg_undef(Undef, loop) -> [Undef, loop];
dbg_undef(Undef, switch_body) -> [switch_body, Undef];
dbg_undef(Undef, {switch, Arg, Type, Alts, Catch}) ->
    NewAlts   = [ dbg_undef(Undef, Alt) || Alt <- Alts ],
    NewCatch  = dbg_undef(Undef, Catch),
    {switch, Arg, Type, NewAlts, NewCatch};
dbg_undef(Undef, SCode) when is_list(SCode) ->
    lists:droplast(SCode) ++ [dbg_undef(Undef, lists:last(SCode))];
dbg_undef(Undef, SCode) when is_tuple(SCode); is_atom(SCode) ->
    [Mnemonic | _] =
        case is_tuple(SCode) of
            true  -> tuple_to_list(SCode);
            false -> [SCode]
        end,
    Op = aeb_fate_opcodes:m_to_op(Mnemonic),
    case aeb_fate_opcodes:end_bb(Op) of
        true  -> [Undef, SCode];
        false -> [SCode, Undef]
    end.


