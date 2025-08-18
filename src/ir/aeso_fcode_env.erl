%%%-------------------------------------------------------------------
%%% @doc Environment and name-resolution utilities for Fcode lowering.
%%%      Extracted from `aeso_ast_to_fcode` for modularity.
%%%-------------------------------------------------------------------
-module(aeso_fcode_env).

-export([init_env/1, state_layout/1,
         add_fun_env/2, lookup_fun/2,
         bind_type/3, bind_constructors/2,
         lookup_con/2, resolve_var/3,
         qname/2, current_namespace/1
        ]).

-include("aeso_utils.hrl").

-spec init_env([aeso_ast_to_fcode:option()]) -> aeso_ast_to_fcode:env().
init_env(Options) ->
    aeso_ast_to_fcode:init_env(Options).

-spec state_layout(aeso_ast_to_fcode:env()) -> aeso_ast_to_fcode:state_layout().
state_layout(Env) -> maps:get(state_layout, Env, {reg, 1}).

-spec add_fun_env(aeso_ast_to_fcode:env(), [aeso_syntax:decl()]) -> aeso_ast_to_fcode:env().
add_fun_env(Env, Decls) -> aeso_ast_to_fcode:add_fun_env(Env, Decls).

-spec lookup_fun(aeso_ast_to_fcode:env(), aeso_ast_to_fcode:sophia_name()) -> aeso_ast_to_fcode:fun_name().
lookup_fun(Env, Name) -> aeso_ast_to_fcode:lookup_fun(Env, Name).

-spec bind_type(aeso_ast_to_fcode:env(), aeso_ast_to_fcode:sophia_name(), aeso_ast_to_fcode:type_def()) -> aeso_ast_to_fcode:env().
bind_type(Env, Q, FDef) -> aeso_ast_to_fcode:bind_type(Env, Q, FDef).

-spec bind_constructors(aeso_ast_to_fcode:env(), aeso_ast_to_fcode:con_env()) -> aeso_ast_to_fcode:env().
bind_constructors(Env, NewCons) -> aeso_ast_to_fcode:bind_constructors(Env, NewCons).

-spec lookup_con(aeso_ast_to_fcode:env(), aeso_syntax:con() | aeso_syntax:qcon() | aeso_ast_to_fcode:sophia_name()) -> aeso_ast_to_fcode:con_tag().
lookup_con(Env, Con) -> aeso_ast_to_fcode:lookup_con(Env, Con).

-spec resolve_var(aeso_ast_to_fcode:env(), aeso_syntax:ann(), [aeso_syntax:name()]) -> aeso_ast_to_fcode:fexpr().
resolve_var(Env, Ann, Xs) -> aeso_ast_to_fcode:resolve_var(Env, Ann, Xs).

-spec qname(aeso_ast_to_fcode:env(), string()) -> aeso_ast_to_fcode:sophia_name().
qname(Env, Name) -> aeso_ast_to_fcode:qname(Env, Name).

-spec current_namespace(aeso_ast_to_fcode:env()) -> string().
current_namespace(Env) -> aeso_ast_to_fcode:current_namespace(Env).


