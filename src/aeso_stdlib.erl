%%%-------------------------------------------------------------------
%%% @author Radosław Rowicki
%%% @copyright (C) 2019, Aeternity Anstalt
%%% @doc
%%%     Standard library for Sophia
%%% @end
%%% Created : 6 July 2019
%%%
%%%-------------------------------------------------------------------

-module(aeso_stdlib).
-vsn("7.1.2").

-export([stdlib_include_path/0]).

stdlib_include_path() ->
    {file, Path} = code:is_loaded(?MODULE),
    filename:join(filename:dirname(filename:dirname(Path)), "priv/stdlib").
