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

  function empty(l) = switch(l)
    [] => true
    _  => false

  function length(l) = length_(l, 0)
  private function length_(l, acc) = switch(l)
    [] => acc
    _::t => length_(t, acc + 1)

  function foldr(cons, nil, l) = switch(l)
    [] => nil
    h::t => cons(h, foldr(cons, nil, t))

  function foldl(rcons, acc, l) = switch(l)
    [] => acc
    h::t => foldl(rcons, rcons(acc, h), t)

  function reverse(l) = foldl((lst, el) => el :: lst, [], l)

  function map(f, l) = map_(f, l, [])
  private function map_(f, l, acc) = switch(l)
    [] => reverse(acc)
    h::t => map_(f, t, f(h)::acc)

  function flat_map(f, l) = switch(l)
    [] => []
    h::t => f(h) ++ flat_map(f, t)

  function concats(ll) = foldr((l1, l2) => l1 ++ l2, [], ll)

  function filter(p, l) = filter_(p, l, [])
  private function filter_(p, l, acc) = switch(l)
    [] => reverse(acc)
    h::t => filter_(p, t, if(p(h)) h::acc else acc)

  function all(p, l) = foldl((prev, next) => prev && p(next), true, l)
  function any(p, l) = foldl((prev, next) => prev || p(next), false, l)

  /* Take `n` first elements */
  function take(n, l) = if(n < 0) abort(\"Take negative number of elements\") else take_(n, l, [])
  private function take_(n, l, acc) =
    if(n == 0) reverse(acc)
    else switch(l)
      [] => reverse(acc)
      h::t => take_(n-1, t, h::acc)

  /* Drop `n` first elements */
  function drop(n, l) =
   if(n < 0) abort(\"Drop negative number of elements\")
   elif (n == 0) l
   else switch(l)
      [] => []
      h::t => drop(n-1, t)

  /* Get the longest prefix of a list in which every element matches predicate `p` */
  function take_while(p, l) = take_while_(p, l, [])
  private function take_while_(p, l, acc) = switch(l)
    [] => reverse(acc)
    h::t => if(p(h)) take_while_(p, t, h::acc) else reverse(acc)

  /* Drop elements from `l` until `p` holds */
  function drop_while(p, l) = switch(l)
    [] => []
    h::t => if(p(h)) drop_while(p, t) else l

  /* Zips two list by applying bimapping function on respective elements. Drops longer tail. */
  function zip_with(f, l1, l2) = zip_with_(f, l1, l2, [])
  private function zip_with_(f, l1, l2, acc) = switch ((l1, l2))
    (h1::t1, h2::t2) => zip_with_(f, t1, t2, f(h1, h2)::acc)
    _ => reverse(acc)

  /* Zips two lists into list of pairs. Drops longer tail. */
  function zip(l1, l2) = zip_with((a, b) => (a, b), l1, l2)

  /* Splits list into two lists of elements that respectively match and don't match predicate `p` */
  function partition(p, l) = partition_(p, l, [], [])
  private function partition_(p, l, acc_t, acc_f) = switch(l)
    [] => (reverse(acc_t), reverse(acc_f))
    h::t => if(p(h)) partition_(p, t, h::acc_t, acc_f) else partition_(p, t, acc_t, h::acc_f)

  // TODO: Improve?
  function sort(lesser_cmp, l) = switch(l)
    [] => []
    h::t => switch (partition((x) => lesser_cmp(x, h), t))
      (lesser, bigger) => sort(lesser_cmp, lesser) ++ h::sort(lesser_cmp, bigger)
".
