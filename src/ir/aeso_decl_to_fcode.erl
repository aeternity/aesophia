%%%-------------------------------------------------------------------
%%% @doc Declaration lowering: functions, constants, typedefs to Fcode.
%%%      Thin wrapper delegating to existing implementations for now.
%%%-------------------------------------------------------------------
-module(aeso_decl_to_fcode).

-export([decls_to_fcode/2, decl_to_fcode/2, args_to_fcode/2]).

-include("aeso_utils.hrl").

-spec decls_to_fcode(aeso_ast_to_fcode:env(), [aeso_syntax:decl()]) -> aeso_ast_to_fcode:env().
decls_to_fcode(Env, Decls) -> aeso_ast_to_fcode:decls_to_fcode(Env, Decls).

-spec decl_to_fcode(aeso_ast_to_fcode:env(), aeso_syntax:decl()) -> aeso_ast_to_fcode:env().
decl_to_fcode(Env, Decl) -> aeso_ast_to_fcode:decl_to_fcode(Env, Decl).

-spec args_to_fcode(aeso_ast_to_fcode:env(), [aeso_syntax:pat()]) -> [{aeso_ast_to_fcode:var_name(), aeso_ast_to_fcode:ftype()}].
args_to_fcode(Env, Args) -> aeso_ast_to_fcode:args_to_fcode(Env, Args).


