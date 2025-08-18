%%%-------------------------------------------------------------------
%%% @doc Expression lowering and helpers. Thin wrapper delegating to
%%%      existing implementations for now.
%%%-------------------------------------------------------------------
-module(aeso_expr_to_fexpr).

-export([expr_to_fcode/2, expr_to_fcode/3]).

-include("aeso_utils.hrl").

-spec expr_to_fcode(aeso_ast_to_fcode:env(), aeso_syntax:expr()) -> aeso_ast_to_fcode:fexpr().
expr_to_fcode(Env, Expr) -> aeso_ast_to_fcode:expr_to_fcode(Env, Expr).

-spec expr_to_fcode(aeso_ast_to_fcode:env(), aeso_syntax:type() | no_type, aeso_syntax:expr()) -> aeso_ast_to_fcode:fexpr().
expr_to_fcode(Env, Type, Expr) -> aeso_ast_to_fcode:expr_to_fcode(Env, Type, Expr).


