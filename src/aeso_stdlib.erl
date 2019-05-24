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

-export([stdlib/0]).

stdlib() ->
    maps:from_list(
      [ {<<"List.aes">>, std_list()}
      ]
     ).

std_list() ->
"
namespace List =
  function length(l) = length_(l, 0)
  private function length_(l, n) = switch(l)
    [] => n
    _::t => length_(t, n + 1)

  function foldr(cons, nil, l) = switch(l)
    [] => nil
    h::t => cons(h, foldr(cons, nil, t))

  function foldl(rcons, acc, l) = switch(l)
    [] => acc
    h::t => foldl(rcons, rcons(acc, h), t)

  function reverse(l) =
    foldr((el, cont) => (lst) => cont(el::lst), (x) => x, l)([])

  function map(f, l) = map_(f, l, [])
  private function map_(f, l, acc) = switch(l)
    [] => reverse(acc)
    h::t => map_(f, t, f(h)::acc)

  function flat_map(f, l) = switch(l)
    [] => []
    h::t => f(h) ++ flat_map(f, t)
".
