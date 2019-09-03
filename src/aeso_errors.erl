%%%-------------------------------------------------------------------
%%% @copyright (C) 2019, Aeternity Anstalt
%%% @doc ADT for structured error messages + formatting.
%%%
%%% @end
%%%-------------------------------------------------------------------

-module(aeso_errors).

-type src_file()   :: no_file | iolist().

-record(pos, { file = no_file :: src_file()
             , line = 0       :: non_neg_integer()
             , col  = 0       :: non_neg_integer()
             }).

-type pos()        :: #pos{}.
-type error_type() :: type_error | parse_error | code_error | internal_error.

-record(err, { pos = #pos{}   :: pos()
             , type           :: error_type()
             , message        :: iolist()
             , context = none :: none | iolist()
             }).

-opaque error() :: #err{}.

-export_type([error/0, pos/0]).

-export([ err_msg/1
        , msg/1
        , new/3
        , new/4
        , pos/2
        , pos/3
        , pp/1
        , throw/1
        , type/1
        ]).

new(Type, Pos, Msg) ->
    #err{ type = Type, pos = Pos, message = Msg }.

new(Type, Pos, Msg, Ctxt) ->
    #err{ type = Type, pos = Pos, message = Msg, context = Ctxt }.

pos(Line, Col) ->
    #pos{ line = Line, col = Col }.

pos(File, Line, Col) ->
    #pos{ file = File, line = Line, col = Col }.

throw([]) -> ok;
throw(Errs) when is_list(Errs) ->
    erlang:throw({error, Errs});
throw(#err{} = Err) ->
    erlang:throw({error, [Err]}).

msg(#err{ message = Msg, context = none }) -> Msg;
msg(#err{ message = Msg, context = Ctxt }) -> Msg ++ Ctxt.

err_msg(#err{ pos = Pos } = Err) ->
    lists:flatten(io_lib:format("~s~s", [str_pos(Pos), msg(Err)])).

str_pos(#pos{file = no_file, line = L, col = C}) ->
    io_lib:format("~p:~p:", [L, C]);
str_pos(#pos{file = F, line = L, col = C}) ->
    io_lib:format("~s:~p:~p:", [F, L, C]).

type(#err{ type = Type }) -> Type.

pp(#err{ pos = Pos } = Err) ->
    lists:flatten(io_lib:format("~s\n~s", [pp_pos(Pos), msg(Err)])).

pp_pos(#pos{file = no_file, line = L, col = C}) ->
    io_lib:format("At line ~p, col ~p:", [L, C]);
pp_pos(#pos{file = F, line = L, col = C}) ->
    io_lib:format("In '~s' at line ~p, col ~p:", [F, L, C]).
