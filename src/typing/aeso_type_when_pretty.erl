%%%-------------------------------------------------------------------
%%% @copyright (C) 2025, Aeternity Anstalt
%%% @doc Pretty printing for typechecking context records (why_record).
%%% @end
%%%-------------------------------------------------------------------
-module(aeso_type_when_pretty).

-include("aeso_why_record.hrl").

-export([
    pp_why_record/1
]).

-spec pp_why_record(why_record()) -> {aeso_errors:pos(), iolist()}.
pp_why_record({var_args, Ann, Fun}) ->
    {pos(Ann),
     io_lib:format("arising from resolution of variadic function `~s`",
                   [aeso_type_pretty:pp_expr(Fun)])};
pp_why_record(Fld = {field, _Ann, LV, _E}) ->
    {pos(Fld),
     io_lib:format("arising from an assignment of the field `~s`",
                   [aeso_type_pretty:pp_expr({lvalue, [], LV})])};
pp_why_record(Fld = {field, _Ann, LV, _Alias, _E}) ->
    {pos(Fld),
     io_lib:format("arising from an assignment of the field `~s`",
                   [aeso_type_pretty:pp_expr({lvalue, [], LV})])};
pp_why_record({proj, _Ann, Rec, FldName}) ->
    {pos(Rec),
     io_lib:format("arising from the projection of the field `~s`",
         [aeso_type_pretty:pp(FldName)])}.

pos(T) ->
    aeso_errors:pos(aeso_syntax:get_ann(file, T, no_file),
                    aeso_syntax:get_ann(line, T, 0),
                    aeso_syntax:get_ann(col, T, 0)).


