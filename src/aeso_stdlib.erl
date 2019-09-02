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

-export([stdlib_include_path/0]).

stdlib_include_path() ->
    filename:join([code:priv_dir(aesophia), "stdlib"]).

