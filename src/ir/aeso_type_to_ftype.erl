%%%-------------------------------------------------------------------
%%% @doc Type translation from Sophia types to Fcode ftype.
%%%      Thin wrapper delegating to existing implementations for now.
%%%-------------------------------------------------------------------
-module(aeso_type_to_ftype).

-export([type_to_fcode/2, type_to_fcode/3, typedef_to_fcode/5]).

-include("aeso_utils.hrl").

-spec type_to_fcode(aeso_ast_to_fcode:env(), aeso_syntax:type()) -> aeso_ast_to_fcode:ftype().
type_to_fcode(Env, Type) -> aeso_ast_to_fcode:type_to_fcode(Env, Type).

-spec type_to_fcode(aeso_ast_to_fcode:env(), #{aeso_ast_to_fcode:var_name() => aeso_ast_to_fcode:ftype()}, aeso_syntax:type()) -> aeso_ast_to_fcode:ftype().
type_to_fcode(Env, Sub, Type) -> aeso_ast_to_fcode:type_to_fcode(Env, Sub, Type).

-spec typedef_to_fcode(aeso_ast_to_fcode:env(), aeso_syntax:id(), [aeso_syntax:tvar()], aeso_syntax:typedef(), aeso_ast_to_fcode:env()) -> aeso_ast_to_fcode:env().
typedef_to_fcode(Env, Name, Xs, Def, _) -> aeso_ast_to_fcode:typedef_to_fcode(Env, Name, Xs, Def).


