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

-export([stdlib/0, stdlib_list/0]).

stdlib() ->
    maps:from_list(stdlib_list()).

stdlib_list() ->
    [ {<<"List.aes">>, std_list()}
    , {<<"Func.aes">>, std_func()}
    , {<<"Option.aes">>, std_option()}
    , {<<"Pair.aes">>, std_pair()}
    , {<<"Triple.aes">>, std_triple()}
    ].

std_func() ->
"
namespace Func =

  function id(x : 'a) : 'a = x

  function const(x : 'a) : 'b => 'a = (y) => x

  function flip(f : ('a, 'b) => 'c) : ('b, 'a) => 'c = (b, a) => f(a, b)

  function comp(f : 'b => 'c, g : 'a => 'b) : 'a => 'c = (x) => f(g(x))

  function pipe(f : 'a => 'b, g : 'b => 'c) : 'a => 'c = (x) => g(f(x))

  function iter(n : int, f : 'a => 'a) : 'a => 'a = iter_(n, f, (x) => x)
  private function iter_(n : int, f : 'a => 'a, acc : 'a => 'a) : 'a => 'a =
    if(n == 0) acc
    elif(n == 1) comp(f, acc)
    else iter_(n / 2, comp(f, f), if(n mod 2 == 0) acc else comp(f, acc))

  function curry2(f : ('a, 'b) => 'c) : 'a => ('b => 'c) =
    (x) => (y) => f(x, y)
  function curry3(f : ('a, 'b, 'c) => 'd) : 'a => ('b => ('c => 'd)) =
    (x) => (y) => (z) => f(x, y, z)

  function uncurry2(f : 'a => ('b => 'c)) : ('a, 'b) => 'c =
    (x, y) => f(x)(y)
  function uncurry3(f : 'a => ('b => ('c => 'd))) : ('a, 'b, 'c) => 'd =
    (x, y, z) => f(x)(y)(z)

// TODO : parser fails here, probably a bug. Uncomment when resolved.
//  function tuplify2(f : ('a, 'b) => 'c) : (('a, 'b)) => 'c =
//    (t) => switch(t)
//      (x, y) => f(x, y)
//  function tuplify3(f : ('a, 'b, 'c) => 'd) : (('a, 'b, 'c)) => 'd =
//    (t) => switch(t)
//      (x, y, z) => f(x, y, z)

//  function untuplify2(f : (('a, 'b)) => 'c) : ('a, 'b) => 'c =
//    (x, y) => f((x, y))
//  function untuplify3(f : (('a, 'b, 'c)) => 'd) : ('a, 'b, 'c) => 'd =
//    (x, y, z) => f((x, y, z))
".

std_list() ->"
namespace List =

  function is_empty(l : list('a)) : bool = switch(l)
    [] => true
    _  => false

  function first(l : list('a)) : option('a) = switch(l)
    [] => None
    h::_ => Some(h)

  function tail(l : list('a)) : option(list('a)) = switch(l)
    [] => None
    _::t => Some(t)

  function last(l : list('a)) : option('a) = switch(l)
    [] => None
    [x] => Some(x)
    _::t => last(t)

  function find(p : 'a => bool, l : list('a)) : option('a) = switch(l)
    [] => None
    h::t => if(p(h)) Some(h) else find(p, t)

  function find_all(p : 'a => bool, l : list('a)) : list('a) = find_all_(p, l, [])
  private function find_all_(p : 'a => bool, l : list('a), acc : list('a)) : list('a) = switch(l)
    [] => reverse(acc)
    h::t => find_all_(p, t, if(p(h)) h::acc else acc)

  function find_indices(p : 'a => bool, l : list('a)) : list(int) = find_indices_(p, l, 0, [])
  private function find_indices_( p : 'a => bool
                                , l : list('a)
                                , n : int
                                , acc : list(int)
                                ) : list(int) = switch(l)
    [] => reverse(acc)
    h::t => find_indices_(p, t, n+1, if(p(h)) n::acc else acc)

  function nth(n : int, l : list('a)) : option('a) = switch(l)
    h::t => if(n == 0) Some(h) else nth(n-1, t)
    [] => None

  /* Unsafe version of `nth` */
  function get(n : int, l : list('a)) : 'a = switch(l)
    [] => abort(\"Out of index get\")
    h::t => if(n == 0) h else get(n-1, t)


  function length(l : list('a)) : int = length_(l, 0)
  private function length_(l : list('a), acc : int) : int = switch(l)
    [] => acc
    _::t => length_(t, acc + 1)


  /* Unsafe. Replaces `n`th element of `l` with `e`. Crashes on over/underflow */
  function replace_at(n : int, e : 'a, l : list('a)) : list('a) =
    if(n<0) abort(\"insert_at underflow\") else replace_at_(n, e, l, [])
  private function replace_at_(n : int, e : 'a, l : list('a), acc : list('a)) : list('a) =
   switch(l)
     [] => abort(\"replace_at overflow\")
     h::t => if (n == 0) reverse(e::acc) ++ t
             else replace_at_(n-1, e, t, h::acc)

  /* Unsafe. Adds `e` to `l` to be its `n`th element. Crashes on over/underflow */
  function insert_at(n : int, e : 'a, l : list('a)) : list('a) =
    if(n<0) abort(\"insert_at underflow\") else insert_at_(n, e, l, [])
  private function insert_at_(n : int, e : 'a, l : list('a), acc : list('a)) : list('a) =
   if (n == 0) reverse(e::acc) ++ l
   else switch(l)
     [] => abort(\"insert_at overflow\")
     h::t => insert_at_(n-1, e, t, h::acc)

  function insert_by(f : (('a, 'a) => bool), x : 'a, l : list('a)) : list('a) =
    switch(l)
      [] => [x]
      (e :: l') =>
        if(f(x, e))
          e :: insert_by(f, x, l')
        else
          x :: l

  function foldr(cons : ('a, 'b) => 'b, nil : 'b, l : list('a)) : 'b = switch(l)
    [] => nil
    h::t => cons(h, foldr(cons, nil, t))

  function foldl(rcons : ('b, 'a) => 'b, acc : 'b, l : list('a)) : 'b = switch(l)
    [] => acc
    h::t => foldl(rcons, rcons(acc, h), t)

  function foreach(f : 'a => (), l : list('a)) : () =
    switch(l)
     [] => ()
     e :: l' =>
       f(e)
       foreach(f, l')


  function reverse(l : list('a)) : list('a) = foldl((lst, el) => el :: lst, [], l)


  function map(f : 'a => 'b, l : list('a)) : list('b) = map_(f, l, [])
  private function map_(f : 'a => 'b, l : list('a), acc : list('b)) : list('b) = switch(l)
    [] => reverse(acc)
    h::t => map_(f, t, f(h)::acc)

  function flat_map(f : 'a => list('b), l : list('a)) : list('b) = flat_map_(f, l, [])
  private function flat_map_(f : 'a => list('b), l : list('a), acc : list('b)) : list('b) = switch(l)
    [] => reverse(acc)
    h::t => flat_map_(f, t, reverse(f(h)) ++ acc)

  function filter(p : 'a => bool, l : list('a)) : list('a) = filter_(p, l, [])
  private function filter_(p : 'a => bool, l : list('a), acc : list('a)) : list('a) = switch(l)
    [] => reverse(acc)
    h::t => filter_(p, t, if(p(h)) h::acc else acc)

  /* Take `n` first elements */
  function take(n : int, l : list('a)) : list('a) =
    if(n < 0) abort(\"Take negative number of elements\") else take_(n, l, [])
  private function take_(n : int, l : list('a), acc : list('a)) : list('a) =
    if(n == 0) reverse(acc)
    else switch(l)
      [] => reverse(acc)
      h::t => take_(n-1, t, h::acc)

  /* Drop `n` first elements */
  function drop(n : int, l : list('a)) : list('a) =
   if(n < 0) abort(\"Drop negative number of elements\")
   elif (n == 0) l
   else switch(l)
      [] => []
      h::t => drop(n-1, t)

  /* Get the longest prefix of a list in which every element matches predicate `p` */
  function take_while(p : 'a => bool, l : list('a)) : list('a) = take_while_(p, l, [])
  private function take_while_(p : 'a => bool, l : list('a), acc : list('a)) : list('a) = switch(l)
    [] => reverse(acc)
    h::t => if(p(h)) take_while_(p, t, h::acc) else reverse(acc)

  /* Drop elements from `l` until `p` holds */
  function drop_while(p : 'a => bool, l : list('a)) : list('a) = switch(l)
    [] => []
    h::t => if(p(h)) drop_while(p, t) else l

  /* Splits list into two lists of elements that respectively match and don't match predicate `p` */
  function partition(p : 'a => bool, l : list('a)) : (list('a), list('a)) = partition_(p, l, [], [])
  private function partition_( p : 'a => bool
                             , l : list('a)
                             , acc_t : list('a)
                             , acc_f : list('a)
                             ) : (list('a), list('a)) = switch(l)
    [] => (reverse(acc_t), reverse(acc_f))
    h::t => if(p(h)) partition_(p, t, h::acc_t, acc_f) else partition_(p, t, acc_t, h::acc_f)


  function concats(ll : list(list('a))) : list('a) = foldr((l1, l2) => l1 ++ l2, [], ll)

  function all(p : 'a => bool, l : list('a)) : bool = foldl((prev, next) => prev && p(next), true, l)

  function any(p : 'a => bool, l : list('a)) : bool = foldl((prev, next) => prev || p(next), false, l)

  function sum(l : list(int)) : int = foldl ((a, b) => a + b, 0, l)

  function product(l : list(int)) : int = foldl((a, b) => a * b, 1, l)


  /* Zips two list by applying bimapping function on respective elements. Drops longer tail. */
  function zip_with(f : ('a, 'b) => 'c, l1 : list('a), l2 : list('b)) : list('c) = zip_with_(f, l1, l2, [])
  private function zip_with_( f : ('a, 'b) => 'c
                            , l1 : list('a)
                            , l2 : list('b)
                            , acc : list('c)
                            ) : list('c) = switch ((l1, l2))
    (h1::t1, h2::t2) => zip_with_(f, t1, t2, f(h1, h2)::acc)
    _ => reverse(acc)

  /* Zips two lists into list of pairs. Drops longer tail. */
  function zip(l1 : list('a), l2 : list('b)) : list(('a, 'b)) = zip_with((a, b) => (a, b), l1, l2)

  function unzip(l : list(('a, 'b))) : (list('a), list('b)) = unzip_(l, [], [])
  private function unzip_( l : list(('a, 'b))
                         , acc_l : list('a)
                         , acc_r : list('b)
                         ) : (list('a), list('b)) = switch(l)
    [] => (reverse(acc_l), reverse(acc_r))
    (left, right)::t => unzip_(t, left::acc_l, right::acc_r)


  // TODO: Improve?
  function sort(lesser_cmp : ('a, 'a) => bool, l : list('a)) : list('a) = switch(l)
    [] => []
    h::t => switch (partition((x) => lesser_cmp(x, h), t))
      (lesser, bigger) => sort(lesser_cmp, lesser) ++ h::sort(lesser_cmp, bigger)


  function intersperse(delim : 'a, l : list('a)) : list('a) = intersperse_(delim, l, [])
  private function intersperse_(delim : 'a, l : list('a), acc : list('a)) : list('a) = switch(l)
    [] => reverse(acc)
    [e] => reverse(e::acc)
    h::t => intersperse_(delim, t, h::delim::acc)


  function enumerate(l : list('a)) : list((int, 'a)) = enumerate_(l, 0, [])
  private function enumerate_(l : list('a), n : int, acc : list((int, 'a))) : list((int, 'a)) = switch(l)
    [] => reverse(acc)
    h::t => enumerate_(t, n + 1, (n, h)::acc)

".

std_option() -> "
include \"List.aes\"

namespace Option =

  function is_none(o : option('a)) : bool = switch(o)
    None => true
    Some(_) => false

  function is_some(o : option('a)) : bool = switch(o)
    None => false
    Some(_) => true


  function match(n : 'b, s : 'a => 'b, o : option('a)) : 'b = switch(o)
    None => n
    Some(x) => s(x)

  function default(def : 'a, o : option('a)) : 'a = match(def, (x) => x, o)

  function force(o : option('a)) : 'a = default(abort(\"Forced None value\"), o)

  function on_elem(f : 'a => (), o : option('a)) : () = match((), f, o)


  function map(f : 'a => 'b, o : option('a)) : option('b) = switch(o)
    None => None
    Some(x) => Some(f(x))

  function map2(f : ('a, 'b) => 'c
               , o1 : option('a)
               , o2 : option('b)
               ) : option('c) = switch((o1, o2))
    (Some(x1), Some(x2)) => Some(f(x1, x2))
    _ => None

  function map3( f : ('a, 'b, 'c) => 'd
               , o1 : option('a)
               , o2 : option('b)
               , o3 : option('c)
               ) : option('d) = switch((o1, o2, o3))
    (Some(x1), Some(x2), Some(x3)) => Some(f(x1, x2, x3))
    _ => None

  function app_over(f : option ('a => 'b), o : option('a)) : option('b) = switch((f, o))
    (Some(ff), Some(xx)) => Some(ff(xx))
    _ => None

  function flat_map(f : 'a => option('b), o : option('a)) : option('b) = switch(o)
    None => None
    Some(x) => f(x)


  function to_list(o : option('a)) : list('a) = switch(o)
    None => []
    Some(x) => [x]

  function filter_options(l : list(option('a))) : list('a) = filter_options_(l, [])
  private function filter_options_(l : list (option('a)), acc : list('a)) : list('a) = switch(l)
    [] => List.reverse(acc)
    None::t => filter_options_(t, acc)
    Some(x)::t => filter_options_(t, x::acc)

  function seq_options(l : list (option('a))) : option (list('a)) = seq_options_(l, [])
  private function seq_options_(l : list (option('a)), acc : list('a)) : option(list('a)) = switch(l)
    [] => Some(List.reverse(acc))
    None::t => None
    Some(x)::t => seq_options_(t, x::acc)


  function choose(o1 : option('a), o2 : option('a)) : option('a) =
    if(is_some(o1)) o1 else o2

  function choose_first(l : list(option('a))) : option('a) = switch(l)
    [] => None
    None::t => choose_first(t)
    Some(x)::_ => Some(x)
".

std_pair() -> "
namespace Pair =

  function fst(t : ('a, 'b)) : 'a = switch(t)
    (x, _) => x

  function snd(t : ('a, 'b)) : 'b = switch(t)
    (_, y) => y


  function map1(f : 'a => 'c, t : ('a, 'b)) : ('c, 'b) = switch(t)
    (x, y) => (f(x), y)

  function map2(f : 'b => 'c, t : ('a, 'b)) : ('a, 'c) = switch(t)
    (x, y) => (x, f(y))

  function bimap(f : 'a => 'c, g : 'b => 'd, t : ('a, 'b)) : ('c, 'd) = switch(t)
    (x, y) => (f(x), g(y))


  function swap(t : ('a, 'b)) : ('b, 'a) = switch(t)
    (x, y) => (y, x)
".

std_triple() -> "
namespace Triple =

  function fst(t : ('a, 'b, 'c)) : 'a = switch(t)
    (x, _, _) => x

  function snd(t : ('a, 'b, 'c)) : 'b = switch(t)
    (_, y, _) => y

  function thd(t : ('a, 'b, 'c)) : 'c = switch(t)
    (_, _, z) => z


  function map1(f : 'a => 'm, t : ('a, 'b, 'c)) : ('m, 'b, 'c) = switch(t)
    (x, y, z) => (f(x), y, z)

  function map2(f : 'b => 'm, t : ('a, 'b, 'c)) : ('a, 'm, 'c) = switch(t)
    (x, y, z) => (x, f(y), z)

  function map3(f : 'c => 'm, t : ('a, 'b, 'c)) : ('a, 'b, 'm) = switch(t)
    (x, y, z) => (x, y, f(z))

  function trimap( f : 'a => 'x
                 , g : 'b => 'y
                 , h : 'c => 'z
                 , t : ('a, 'b, 'c)
                 ) : ('x, 'y, 'z) = switch(t)
    (x, y, z) => (f(x), g(y), h(z))


  function swap(t : ('a, 'b, 'c)) : ('c, 'b, 'a) = switch(t)
    (x, y, z) => (z, y, x)

  function rotr(t : ('a, 'b, 'c)) : ('c, 'a, 'b) = switch(t)
    (x, y, z) => (z, x, y)

  function rotl(t : ('a, 'b, 'c)) : ('b, 'c, 'a) = switch(t)
    (x, y, z) => (y, z, x)
".
