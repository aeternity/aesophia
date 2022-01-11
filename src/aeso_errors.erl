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
-type error_type() :: type_error | parse_error | code_error
                    | file_error | data_error | internal_error.

-record(err, { pos = #pos{}   :: pos()
             , type           :: error_type()
             , message        :: iolist()
             , context = none :: none | iolist()
             }).

-opaque error() :: #err{}.

-export_type([error/0, pos/0]).

-export([ err_msg/1
        , msg/1
        , msg_oneline/1
        , new/2
        , new/3
        , new/4
        , pos/2
        , pos/3
        , pp/1
        , pp_oneline/1
        , pp_pos/1
        , to_json/1
        , throw/1
        , type/1
        ]).

new(Type, Msg) ->
    new(Type, pos(0, 0), Msg).

new(Type, Pos, Msg) ->
    #err{ type = Type, pos = Pos, message = Msg }.

new(Type, Pos, Msg, Ctxt) ->
    #err{ type = Type, pos = Pos, message = Msg, context = Ctxt }.

pos(Line, Col) ->
    #pos{ line = Line, col = Col }.

pos(File, Line, Col) ->
    #pos{ file = File, line = Line, col = Col }.

-spec throw(_) -> ok | no_return().
throw([]) -> ok;
throw(Errs) when is_list(Errs) ->
    SortedErrs = lists:sort(fun(E1, E2) -> E1#err.pos =< E2#err.pos end, Errs),
    erlang:throw({error, SortedErrs});
throw(#err{} = Err) ->
    erlang:throw({error, [Err]}).

msg(#err{ message = Msg, context = none }) -> Msg;
msg(#err{ message = Msg, context = Ctxt }) -> Msg ++ "\n" ++ Ctxt.

msg_oneline(#err{ message = Msg, context = none }) -> Msg;
msg_oneline(#err{ message = Msg, context = Ctxt }) -> Msg ++ " - " ++ Ctxt.

err_msg(#err{ pos = Pos } = Err) ->
    lists:flatten(io_lib:format("~s~s\n", [str_pos(Pos), msg(Err)])).

str_pos(#pos{file = no_file, line = L, col = C}) ->
    io_lib:format("~p:~p:", [L, C]);
str_pos(#pos{file = F, line = L, col = C}) ->
    io_lib:format("~s:~p:~p:", [F, L, C]).

type(#err{ type = Type }) -> Type.

pp(#err{ type = Kind, pos = Pos } = Err) ->
    lists:flatten(io_lib:format("~s~s:\n~s\n", [pp_kind(Kind), pp_pos(Pos), msg(Err)])).

pp_oneline(#err{ type = Kind, pos = Pos } = Err) ->
    Msg = msg_oneline(Err),
    OneLineMsg = re:replace(Msg, "[\s\\n]+", " ", [global]),
    lists:flatten(io_lib:format("~s~s: ~s", [pp_kind(Kind), pp_pos(Pos), OneLineMsg])).

pp_kind(type_error)     -> "Type error";
pp_kind(parse_error)    -> "Parse error";
pp_kind(code_error)     -> "Code generation error";
pp_kind(file_error)     -> "File error";
pp_kind(data_error)     -> "Data error";
pp_kind(internal_error) -> "Internal error".

pp_pos(#pos{file = no_file, line = 0, col = 0}) ->
    "";
pp_pos(#pos{file = no_file, line = L, col = C}) ->
    io_lib:format(" at line ~p, col ~p", [L, C]);
pp_pos(#pos{file = F, line = L, col = C}) ->
    io_lib:format(" in '~s' at line ~p, col ~p", [F, L, C]).

to_json(#err{pos = Pos, type = Type, message = Msg, context = Cxt}) ->
    Json = #{ pos     => pos_to_json(Pos),
              type    => atom_to_binary(Type, utf8),
              message => iolist_to_binary(Msg) },
    case Cxt of
        none -> Json;
        _    -> Json#{ context => iolist_to_binary(Cxt) }
    end.

pos_to_json(#pos{ file = File, line = Line, col = Col }) ->
    Json = #{ line => Line, col => Col },
    case File of
        no_file -> Json;
        _       -> Json#{ file => iolist_to_binary(File) }
    end.

