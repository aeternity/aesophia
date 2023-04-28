-module(aeso_warnings).
-vsn("7.1.1").

-record(warn, { pos     :: aeso_errors:pos()
              , message :: iolist()
              }).

-opaque warning() :: #warn{}.

-export_type([warning/0]).

-export([ new/1
        , new/2
        , warn_to_err/2
        , sort_warnings/1
        , pp/1
        ]).

new(Msg) ->
    new(aeso_errors:pos(0, 0), Msg).

new(Pos, Msg) ->
    #warn{ pos = Pos, message = Msg }.

warn_to_err(Kind, #warn{ pos = Pos, message = Msg }) ->
    aeso_errors:new(Kind, Pos, lists:flatten(Msg)).

sort_warnings(Warnings) ->
    lists:sort(fun(W1, W2) -> W1#warn.pos =< W2#warn.pos end, Warnings).

pp(#warn{ pos = Pos, message = Msg }) ->
    lists:flatten(io_lib:format("Warning~s:\n~s", [aeso_errors:pp_pos(Pos), Msg])).
