# Features
## Contracts

The main unit of code in Sophia is the *contract*.

- A contract implementation, or simply a contract, is the code for a
  smart contract and consists of a list of types, entrypoints and local
  functions. Only the entrypoints can be called from outside the contract.
- A contract instance is an entity living on the block chain (or in a state
  channel). Each instance has an address that can be used to call its
  entrypoints, either from another contract or in a call transaction.
- A contract may define a type `state` encapsulating its local
  state. When creating a new contract the `init` entrypoint is executed and the
  state is initialized to its return value.

The language offers some primitive functions to interact with the blockchain and contracts.
Please refer to the [Chain](sophia_stdlib.md#chain), [Contract](sophia_stdlib.md#contract)
and the [Call](sophia_stdlib.md#call) namespaces in the documentation.

### Calling other contracts

To call a function in another contract you need the address to an instance of
the contract. The type of the address must be a contract type, which consists
of a number of type definitions and entrypoint declarations. For instance,

```sophia
// A contract type
contract interface VotingType =
  entrypoint vote : string => unit
```

Now given contract address of type `VotingType` you can call the `vote`
entrypoint of that contract:

```sophia
contract VoteTwice =
  entrypoint voteTwice(v : VotingType, alt : string) =
    v.vote(alt)
    v.vote(alt)
```

Contract calls take two optional named arguments `gas : int` and `value : int`
that lets you set a gas limit and provide tokens to a contract call. If omitted
the defaults are no gas limit and no tokens. Suppose there is a fee for voting:

```sophia
  entrypoint voteTwice(v : VotingType, fee : int, alt : string) =
    v.vote(value = fee, alt)
    v.vote(value = fee, alt)
```

Named arguments can be given in any order.

Note that reentrant calls are not permitted. In other words, when calling
another contract it cannot call you back (directly or indirectly).

To construct a value of a contract type you can give a contract address literal
(for instance `ct_2gPXZnZdKU716QBUFKaT4VdBZituK93KLvHJB3n4EnbrHHw4Ay`), or
convert an account address to a contract address using `Address.to_contract`.
Note that if the contract does not exist, or it doesn't have the entrypoint, or
the type of the entrypoint does not match the stated contract type, the call
fails.

To recover the underlying `address` of a contract instance there is a field
`address : address`. For instance, to send tokens to the voting contract (given that it is payable)
without calling it you can write

```sophia
  entrypoint pay(v : VotingType, amount : int) =
    Chain.spend(v.address, amount)
```

### Protected contract calls

If a contract call fails for any reason (for instance, the remote contract
crashes or runs out of gas, or the entrypoint doesn't exist or has the wrong
type) the parent call also fails. To make it possible to recover from failures,
contract calls takes a named argument `protected : bool` (default `false`).

The protected argument must be a literal boolean, and when set to `true`
changes the type of the contract call, wrapping the result in an `option` type.
If the call fails the result is `None`, otherwise it's `Some(r)` where `r` is
the return value of the call.

```sophia
contract interface VotingType =
  entrypoint vote : string => unit

contract Voter =
  entrypoint tryVote(v : VotingType, alt : string) =
    switch(v.vote(alt, protected = true) : option(unit))
      None    => "Voting failed"
      Some(_) => "Voting successful"
```

Any gas that was consumed by the contract call before the failure stays
consumed, which means that in order to protect against the remote contract
running out of gas it is necessary to set a gas limit using the `gas` argument.
However, note that errors that would normally consume all the gas in the
transaction still only uses up the gas spent running the contract.

Any side effects (state change, token transfers, etc.) made by a failing
protected call is rolled back, just like they would be in the unprotected case.


### Contract factories and child contracts

Since the version 6.0.0 Sophia supports deploying contracts by other
contracts. This can be done in two ways:

- Contract cloning via [`Chain.clone`](sophia_stdlib.md#clone)
- Direct deploy via [`Chain.create`](sophia_stdlib.md#create)

These functions take variable number of arguments that must match the created
contract's `init` function. Beside that they take some additional named
arguments – please refer to their documentation for the details.

While `Chain.clone` requires only a `contract interface` and a living instance
of a given contract on the chain, `Chain.create` needs a full definition of a
to-create contract defined by the standard `contract` syntax, for example

```sophia
contract IntHolder =
  type state = int
  entrypoint init(x) = x
  entrypoint get() = state

main contract IntHolderFactory =
  stateful entrypoint new(x : int) : IntHolder =
    let ih = Chain.create(x) : IntHolder
    ih
```

In case of a presence of child contracts (`IntHolder` in this case), the main
contract must be pointed out with the `main` keyword as shown in the example.

### Contract interfaces and polymorphism

Contracts can implement one or multiple interfaces, the contract has to define
every entrypoint from the implemented interface and the entrypoints in both
the contract and implemented interface should have compatible types.

```
contract interface Animal =
  entrypoint sound : () => string

 contract Cat : Animal =
  entrypoint sound() = "Cat sound"
```

Contract interfaces can extend other interfaces. An extended interface has to
declare all entrypoints from every parent interface. All the declarations in the extended
interface must have types compatible with the declarations from the parent
interface.

```
contract interface II =
  entrypoint f : () => unit

contract interface I : II =
  entrypoint f : () => unit
  entrypoint g : () => unit

contract C : I =
  entrypoint f() = ()
  entrypoint g() = ()
```

It is only possible to implement (or extend) an interface that has been already
defined earlier in the file (or in an included file). Therefore recursive
interface implementation is not allowed in Sophia.

```
// The following code would show an error

contract interface X : Z =
     entrypoint x : () => int

 contract interface Y : X =
     entrypoint x : () => int
     entrypoint y : () => int

 contract interface Z : Y =
     entrypoint x : () => int
     entrypoint y : () => int
     entrypoint z : () => int

 contract C : Z =
     entrypoint x() = 1
     entrypoint y() = 1
     entrypoint z() = 1
```

#### Adding or removing modifiers

When a `contract` or a `contract interface` implements another `contract interface`, the `payable` and `stateful` modifiers can be kept or changed, both in the contract and in the entrypoints, according to the following rules:

1. A `payable` contract or interface can implement a `payable` interface or a non-`payable` interface.
2. A non-`payable` contract or interface can only implement a non-`payable` interface, and cannot implement a `payable` interface.
3. A `payable` entrypoint can implement a `payable` entrypoint or a non-`payable` entrypoint.
4. A non-`payable` entrypoint can only implement a non-`payable` entrypoint, and cannot implement a `payable` entrypoint.
5. A non-`stateful` entrypoint can implement a `stateful` entrypoint or a non-`stateful` entrypoint.
6. A `stateful` entrypoint can only implement a `stateful` entrypoint, and cannot implement a non-`stateful` entrypoint.

#### Subtyping and variance

Subtyping in Sophia follows common rules that take type variance into account. As described by [Wikipedia](https://en.wikipedia.org/wiki/Covariance_and_contravariance_(computer_science)),

>Variance refers to how subtyping between more complex types relates to subtyping between their components.

This concept plays an important role in complex types such as tuples, `datatype`s and functions. Depending on the context, it can apply to positions in the structure of a type, or type parameters of generic types. There are four kinds of variances:

- covariant
- contravariant
- invariant
- bivariant

A type is said to be on a "covariant" position when it describes output or a result of some computation. Analogously, position is "contravariant" when it is an input, or a parameter. Intuitively, when a part of the type is produced by values of it, it is covariant. When it is consumed, it is contravariant. When a type appears to be simultaneously input and output, it is described as invariant. If a type is neither of those (that is, it's unused) it's bivariant. Furthermore, whenever a complex type appears on a contravariant position, all its covariant components become contravariant and vice versa.

Variance influences how subtyping is applied. Types on covariant positions are subtyped normally, while contravariant the opposite way. Invariant types have to be exactly the same in order for subtyping to work. Bivariant types are always compatible.

A good example of where it matters can be pictured by subtyping of function types. Let us assume there is a contract interface `Animal` and two contracts that implement it: `Dog` and `Cat`.

```sophia
contract interface Animal =
  entrypoint age : () => int

contract Dog : Animal =
  entrypoint age() = // ...
  entrypoint woof() = "woof"

contract Cat : Animal =
  entrypoint age() = // ...
  entrypoint meow() = "meow"
```

The assumption of this exercise is that cats do not bark (because `Cat` does not define the `woof` entrypoint). If subtyping rules were applied naively, that is if we let `Dog => Dog` be a subtype of `Animal => Animal`, the following code would break:

```sophia
let f : (Dog) => string  = d => d.woof()
let g : (Animal) => string  = f
let c : Cat = Chain.create()
g(c)  // Cat barking!
```

That is because arguments of functions are contravariant, as opposed to return the type which is covariant. Because of that, the assignment of `f` to `g` is invalid - while `Dog` is a subtype of `Animal`, `Dog => string` is **not** a subtype of `Animal => string`. However, `Animal => string` **is** a subtype of `Dog => string`. More than that, `(Dog => Animal) => Dog` is a subtype of `(Animal => Dog) => Animal`.

This has consequences on how user-defined generic types work. A type variable gains its variance from its role in the type definition as shown in the example:

```sophia
datatype co('a) = Co('a) // co is covariant on 'a
datatype ct('a) = Ct('a => unit) // ct is contravariant on 'a
datatype in('a) = In('a => 'a) // in is invariant on 'a
datatype bi('a) = Bi // bi is bivariant on 'a
```

The following facts apply here:

- `co('a)` is a subtype of `co('b)` when `'a` is a subtype of `'b`
- `ct('a)` is a subtype of `ct('b)` when `'b` is a subtype of `'a`
- `in('a)` is a subtype of `in('b)` when `'a` is equal to `'b`
- `bi('a)` is a subtype of `bi('b)` always

That altogether induce the following rules of subtyping in Sophia:

- A function type `(Args1) => Ret1` is a subtype of `(Args2) => Ret2` when `Ret1`
is a subtype of `Ret2` and each argument type from `Args2` is a subtype of its
counterpart in `Args1`.

- A list type `list(A)` is a subtype of `list(B)` if `A` is a subtype of `B`.

- An option type `option(A)` is a subtype of `option(B)` if `A` is a subtype of `B`.

- A map type `map(A1, A2)` is a subtype of `map(B1, B2)` if `A1` is a subtype
of `B1`, and `A2` is a subtype of `B2`.

- An oracle type `oracle(A1, A2)` is a subtype of `oracle(B1, B2)` if `B1` is
a subtype of `A1`, and `A2` is a subtype of `B2`.

- An oracle_query type `oracle_query(A1, A2)` is a subtype of `oracle_query(B1, B2)`
if `A1` is a subtype of `B1`, and `A2` is a subtype of `B2`.

- A user-defined datatype `t(Args1)` is a subtype of `t(Args2)`

- When a user-defined type `t('a)` is covariant in `'a`, then `t(A)` is a
subtype of `t(B)` when `A` is a subtype of `B`.

- When a user-defined type `t('a)` is contravariant in `'a`, then `t(A)` is a
subtype of `t(B)` when `B` is a subtype of `A`.

- When a user-defined type `t('a)` is binvariant in `'a`, then `t(A)` is a
subtype of `t(B)` when either `A` is a subtype of `B` or when `B` is a subtype
of `A`.

- When a user-defined type `t('a)` is invariant in `'a`, then `t(A)` can never be
a subtype of `t(B)`.

## Mutable state

Sophia does not have arbitrary mutable state, but only a limited form of state
associated with each contract instance.

- Each contract defines a type `state` encapsulating its mutable state.
  The type `state` defaults to the `unit`.
- The initial state of a contract is computed by the contract's `init`
  function. The `init` function is *pure* and returns the initial state as its
  return value.
  If the type `state` is `unit`, the `init` function defaults to returning the value `()`.
  At contract creation time, the `init` function is executed and
  its result is stored as the contract state.
- The value of the state is accessible from inside the contract
  through an implicitly bound variable `state`.
- State updates are performed by calling a function `put : state => unit`.
- Aside from the `put` function (and similar functions for transactions
  and events), the language is purely functional.
- Functions modifying the state need to be annotated with the `stateful` keyword (see below).

To make it convenient to update parts of a deeply nested state Sophia
provides special syntax for map/record updates.

### Stateful functions

Top-level functions and entrypoints must be annotated with the
`stateful` keyword to be allowed to affect the state of the running contract.
For instance,

```sophia
  stateful entrypoint set_state(s : state) =
    put(s)
```

Without the `stateful` annotation the compiler does not allow the call to
`put`. A `stateful` annotation is required to

* Use a stateful primitive function. These are
  - `put`
  - `Chain.spend`
  - `Oracle.register`
  - `Oracle.query`
  - `Oracle.respond`
  - `Oracle.extend`
  - `AENS.preclaim`
  - `AENS.claim`
  - `AENS.transfer`
  - `AENS.revoke`
  - `AENS.update`
* Call a `stateful` function in the current contract
* Call another contract with a non-zero `value` argument.

A `stateful` annotation *is not* required to

* Read the contract state.
* Issue an event using the `event` function.
* Call another contract with `value = 0`, even if the called function is stateful.

## Payable

### Payable contracts

A concrete contract is by default *not* payable. Any attempt at spending to such
a contract (either a `Chain.spend` or a normal spend transaction) will fail. If a
contract shall be able to receive funds in this way it has to be declared `payable`:

```sophia
// A payable contract
payable contract ExampleContract =
  stateful entrypoint do_stuff() = ...
```

If in doubt, it is possible to check if an address is payable using
`Address.is_payable(addr)`.

### Payable entrypoints

A contract entrypoint is by default *not* payable. Any call to such a function
(either a [Remote call](#calling-other-contracts) or a contract call transaction)
that has a non-zero `value` will fail. Contract entrypoints that should be called
with a non-zero value should be declared `payable`.

```sophia
payable stateful entrypoint buy(to : address) =
  if(Call.value > 42)
    transfer_item(to)
  else
    abort("Value too low")
```

## Namespaces

Code can be split into libraries using the `namespace` construct. Namespaces
can appear at the top-level and can contain type and function definitions, but
not entrypoints. Outside the namespace you can refer to the (non-private) names
by qualifying them with the namespace (`Namespace.name`).
For example,

```sophia
namespace Library =
  type number = int
  function inc(x : number) : number = x + 1

contract MyContract =
  entrypoint plus2(x) : Library.number =
    Library.inc(Library.inc(x))
```

Functions in namespaces have access to the same environment (including the
`Chain`, `Call`, and `Contract`, builtin namespaces) as function in a contract,
with the exception of `state`, `put` and `Chain.event` since these are
dependent on the specific state and event types of the contract.

To avoid mentioning the namespace every time it is used, Sophia allows
including the namespace in the current scope with the `using` keyword:
```
include "Pair.aes"
using Pair
contract C =
  type state = int
  entrypoint init() =
    let p = (1, 2)
    fst(p)  // this is the same as Pair.fst(p)
```

It is also possible to make an alias for the namespace with the `as` keyword:
```
include "Pair.aes"
contract C =
  using Pair as P
  type state = int
  entrypoint init() =
    let p = (1, 2)
    P.fst(p)  // this is the same as Pair.fst(p)
```

Having the same alias for multiple namespaces is possible and it allows
referening functions that are defined in different namespaces and have
different names with the same alias:
```
namespace Xa = function f() = 1
namespace Xb = function g() = 2
contract Cntr =
  using Xa as A
  using Xb as A
  type state = int
  entrypoint init() = A.f() + A.g()
```

Note that using functions with the same name would result in an ambiguous name
error:
```
namespace Xa = function f() = 1
namespace Xb = function f() = 2
contract Cntr =
  using Xa as A
  using Xb as A
  type state = int

  // the next line has an error because f is defined in both Xa and Xb
  entrypoint init() = A.f()
```

Importing specific parts of a namespace or hiding these parts can also be
done like this:
```
using Pair for [fst, snd]       // this will only import fst and snd
using Triple hiding [fst, snd]  // this will import everything except for fst and snd
```

Note that it is possible to use a namespace in the top level of the file, in the
contract level, namespace level, or in the function level.

## Splitting code over multiple files

Code from another file can be included in a contract using an `include`
statement. These must appear at the top-level (outside the main contract). The
included file can contain one or more namespaces and abstract contracts. For
example, if the file `library.aes` contains

```sophia
namespace Library =
  function inc(x) = x + 1
```

you can use it from another file using an `include`:

```sophia
include "library.aes"
contract MyContract =
  entrypoint plus2(x) = Library.inc(Library.inc(x))
```

This behaves as if the contents of `library.aes` was textually inserted into
the file, except that error messages will refer to the original source
locations. The language will try to include each file at most one time automatically,
so even cyclic includes should be working without any special tinkering.

### Include files using relative paths

When including code from another file using the `include` statement, the path
is relative to _the file that includes it_. Consider the following file tree:
```
c1.aes
c3.aes
dir1/c2.aes
dir1/c3.aes
```

If `c1.aes` contains `include "c3.aes"` it will include the top level `c3.aes`,
while if `c2.aes` contained the same line it would as expected include
`dir1/c3.aes`.

Note: Prior to v7.5.0, it would consider the include path relative to _the main
contract file_ (or any explicitly set include path).

## Standard library

Sophia offers [standard library](sophia_stdlib.md) which exposes some
primitive operations and some higher level utilities. The builtin
namespaces like `Chain`, `Contract`, `Map`
are included by default and are supported internally by the compiler.
Others like `List`, `Frac`, `Option` need to be manually included using the
`include` directive. For example
```sophia
include "List.aes"
include "Pair.aes"
-- Map is already there!

namespace C =
  entrypoint keys(m : map('a, 'b)) : list('a) =
    List.map(Pair.fst, (Map.to_list(m)))
```

## Types
Sophia has the following types:

| Type                 | Description                                                                                 | Example                                                      |
|----------------------|---------------------------------------------------------------------------------------------|--------------------------------------------------------------|
| int                  | A 2-complement integer                                                                      | ```-1```                                                     |
| address              | æternity address, 32 bytes                                                                 | ```Call.origin```                                            |
| bool                 | A Boolean                                                                                   | ```true```                                                   |
| bits                 | A bit field                                                                                 | ```Bits.none```                                              |
| bytes(n)             | A byte array with `n` bytes                                                                 | ```#fedcba9876543210```                                      |
| string               | An array of bytes                                                                           | ```"Foo"```                                                  |
| list                 | A homogeneous immutable singly linked list.                                                 | ```[1, 2, 3]```                                              |
| ('a, 'b) => 'c       | A function. Parentheses can be skipped if there is only one argument                        | ```(x : int, y : int) => x + y```                            |
| tuple                | An ordered heterogeneous array                                                              | ```(42, "Foo", true)```                                      |
| record               | An immutable key value store with fixed key names and typed values                          | ``` record balance = { owner: address, value: int } ```      |
| map                  | An immutable key value store with dynamic mapping of keys of one type to values of one type | ```type accounts = map(string, address)```                   |
| option('a)           | An optional value either None or Some('a)                                                   | ```Some(42)```                                               |
| state                | A user defined type holding the contract state                                              | ```record state = { owner: address, magic_key: bytes(4) }``` |
| event                | An append only list of blockchain events (or log entries)                                   | ```datatype event = EventX(indexed int, string)```           |
| hash                 | A 32-byte hash - equivalent to `bytes(32)`                                                  |                                                              |
| signature            | A signature - equivalent to `bytes(64)`                                                     |                                                              |
| Chain.ttl            | Time-to-live (fixed height or relative to current block)                                    | ```FixedTTL(1050)``` ```RelativeTTL(50)```                   |
| oracle('a, 'b)       | And oracle answering questions of type 'a with answers of type 'b                           | ```Oracle.register(acct, qfee, ttl)```                       |
| oracle_query('a, 'b) | A specific oracle query                                                                     | ```Oracle.query(o, q, qfee, qttl, rttl)```                   |
| contract             | A user defined, typed, contract address                                                     | ```function call_remote(r : RemoteContract) = r.fun()```     |

## Literals
| Type                 | Constant/Literal example(s)                                                                                                         |
| ----------           | -------------------------------                                                                                                     |
| int                  | `-1`, `2425`, `4598275923475723498573485768`                                                                                        |
| address              | `ak_2gx9MEFxKvY9vMG5YnqnXWv1hCsX7rgnfvBLJS4aQurustR1rt`                                                                             |
| bool                 | `true`, `false`                                                                                                                     |
| bits                 | `Bits.none`, `Bits.all`                                                                                                             |
| bytes(8)             | `#fedcba9876543210`                                                                                                                 |
| string               | `"This is a string"`                                                                                                                |
| list                 | `[1, 2, 3]`, `[(true, 24), (false, 19), (false, -42)]`                                                                              |
| tuple                | `(42, "Foo", true)`                                                                                                                 |
| record               | `{ owner = Call.origin, value = 100000000 }`                                                                                        |
| map                  | `{["foo"] = 19, ["bar"] = 42}`, `{}`                                                                                                |
| option(int)          | `Some(42)`, `None`                                                                                                                  |
| state                | `state{ owner = Call.origin, magic_key = #a298105f }`                                                                               |
| event                | `EventX(0, "Hello")`                                                                                                                |
| hash                 | `#000102030405060708090a0b0c0d0e0f000102030405060708090a0b0c0d0e0f`                                                                 |
| signature            | `#000102030405060708090a0b0c0d0e0f000102030405060708090a0b0c0d0e0f000102030405060708090a0b0c0d0e0f000102030405060708090a0b0c0d0e0f` |
| Chain.ttl            | `FixedTTL(1050)`, `RelativeTTL(50)`                                                                                                 |
| oracle('a, 'b)       | `ok_2YNyxd6TRJPNrTcEDCe9ra59SVUdp9FR9qWC5msKZWYD9bP9z5`                                                                             |
| oracle_query('a, 'b) | `oq_2oRvyowJuJnEkxy58Ckkw77XfWJrmRgmGaLzhdqb67SKEL1gPY`                                                                             |
| contract             | `ct_Ez6MyeTMm17YnTnDdHTSrzMEBKmy7Uz2sXu347bTDPgVH2ifJ`                                                                              |

## Hole expression

Hole expressions, written as `???`, are expressions that are used as a placeholder. During compilation, the compiler will generate a type error indication the type of the hole expression.

```
include "List.aes"
contract C =
    entrypoint f() =
        List.sum(List.map(???, [1,2,3]))
```

A hole expression found in the example above will generate the error `` Found a hole of type `(int) => int` ``. This says that the compiler expects a function from `int` to `int` in place of the `???` placeholder.

## Constants

Constants in Sophia are contract-level bindings that can be used in either contracts or namespaces. The value of a constant can be a literal, another constant, or arithmetic operations applied to other constants. Lists, tuples, maps, and records can also be used to define a constant as long as their elements are also constants.

The following visibility rules apply to constants:
*  Constants defined inside a contract are private in that contract. Thus, cannot be accessed through instances of their defining contract.
* Constants defined inside a namespace are public. Thus, can be used in other contracts or namespaces.
* Constants cannot be defined inside a contract interface.

When a constant is shadowed, it can be accessed using its qualified name:

```
contract C =
  let c = 1
  entrypoint f() =
    let c = 2
    c + C.c  // the result is 3
```

The name of the constant must be an id; therefore, no pattern matching is allowed when defining a constant:

```
contract C
  let x::y::_ = [1,2,3]  // this will result in an error
```

## Arithmetic

Sophia integers (`int`) are represented by arbitrary-sized signed words and support the following
arithmetic operations:
- addition (`x + y`)
- subtraction (`x - y`)
- multiplication (`x * y`)
- division (`x / y`), truncated towards zero
- remainder (`x mod y`), satisfying `y * (x / y) + x mod y == x` for non-zero `y`
- exponentiation (`x ^ y`)

All operations are *safe* with respect to overflow and underflow.
The division and modulo operations throw an arithmetic error if the
right-hand operand is zero.

Sophia arbitrary-sized integers (FATE) also supports the following bitwise operations:
- bitwise and (`x band y`)
- bitwise or (`x bor y`)
- bitwise xor (`x bxor y`)
- bitwise not (`bnot x`)
- arithmetic bitshift left (`x << n`)
- arithmetic bitshift right (`x >> n`)

## Bit fields

Sophia integers do not support bit arithmetic. Instead there is a separate
type `bits`. See the standard library [documentation](sophia_stdlib.md#bits).

A bit field can be of arbitrary size (but it is still represented by the
corresponding integer, so setting very high bits can be expensive).

## Type aliases

Type aliases can be introduced with the `type` keyword and can be
parameterized. For instance

```sophia
type number = int
type string_map('a) = map(string, 'a)
```

A type alias and its definition can be used interchangeably. Sophia does not support
higher-kinded types, meaning that following type alias is invalid: `type wrap('f, 'a) = 'f('a)`

## Algebraic data types

Sophia supports algebraic data types (variant types) and pattern matching. Data
types are declared by giving a list of constructors with
their respective arguments. For instance,

```sophia
datatype one_or_both('a, 'b) = Left('a) | Right('b) | Both('a, 'b)
```

Elements of data types can be pattern matched against, using the `switch` construct:

```sophia
function get_left(x : one_or_both('a, 'b)) : option('a) =
  switch(x)
    Left(x)    => Some(x)
    Right(_)   => None
    Both(x, _) => Some(x)
```

or directly in the left-hand side:
```sophia
function
  get_left : one_or_both('a, 'b) => option('a)
  get_left(Left(x))    = Some(x)
  get_left(Right(_))   = None
  get_left(Both(x, _)) = Some(x)
```

*NOTE: Data types cannot currently be recursive.*

Sophia also supports the assignment of patterns to variables:
```sophia
function f(x) = switch(x)
  h1::(t = h2::_) => (h1 + h2)::t  // same as `h1::h2::k => (h1 + h2)::h2::k`
  _ => x

function g(p : int * option(int)) : int =
  let (a, (o = Some(b))) = p  // o is equal to Pair.snd(p)
  b
```

Guards are boolean expressions that can be used on patterns in both switch
statements and functions definitions. If a guard expression evaluates to
`true`, then the corresponding body will be used. Otherwise, the next pattern
will be checked:

```sophia
function get_left_if_positive(x : one_or_both(int, 'b)) : option(int) =
  switch(x)
    Left(x)    | x > 0 => Some(x)
    Both(x, _) | x > 0 => Some(x)
    _                  => None
```

```sophia
function
  get_left_if_positive : one_or_both(int, 'b) => option(int)
  get_left_if_positive(Left(x))    | x > 0 = Some(x)
  get_left_if_positive(Both(x, _)) | x > 0 = Some(x)
  get_left_if_positive(_)                  = None
```

Guards cannot be stateful even when used inside a stateful function.

## Lists

A Sophia list is a dynamically sized, homogenous, immutable, singly
linked list. A list is constructed with the syntax `[1, 2, 3]`. The
elements of a list can be any of datatype but they must have the same
type. The type of lists with elements of type `'e` is written
`list('e)`. For example we can have the following lists:

```sophia
[1, 33, 2, 666]                                                   : list(int)
[(1, "aaa"), (10, "jjj"), (666, "the beast")]                     : list(int * string)
[{[1] = "aaa", [10] = "jjj"}, {[5] = "eee", [666] = "the beast"}] : list(map(int, string))
```

New elements can be prepended to the front of a list with the `::`
operator. So `42 :: [1, 2, 3]` returns the list `[42, 1, 2, 3]`. The
concatenation operator `++` appends its second argument to its first
and returns the resulting list. So concatenating two lists
`[1, 22, 33] ++ [10, 18, 55]` returns the list `[1, 22, 33, 10, 18, 55]`.

Sophia supports list comprehensions known from languages like Python, Haskell or Erlang.
Example syntax:
```sophia
[x + y | x <- [1,2,3,4,5], let k = x*x, if (k > 5), y <- [k, k+1, k+2]]
// yields [12,13,14,20,21,22,30,31,32]
```

Lists can be constructed using the range syntax using special `..` operator:
```sophia
[1..4] == [1,2,3,4]
```
The ranges are always ascending and have step equal to 1.


Please refer to the [standard library](sophia_stdlib.md#list) for the predefined functionalities.

## Maps and records

A Sophia record type is given by a fixed set of fields with associated,
possibly different, types. For instance
```sophia
  record account = { name    : string,
                     balance : int,
                     history : list(transaction) }
```

Maps, on the other hand, can contain an arbitrary number of key-value bindings,
but of a fixed type. The type of maps with keys of type `'k` and values of type
`'v` is written `map('k, 'v)`. The key type can be any type that does not
contain a map or a function type.

Please refer to the [standard library](sophia_stdlib.md#map) for the predefined functionalities.

### Constructing maps and records

A value of record type is constructed by giving a value for each of the fields.
For the example above,
```sophia
  function new_account(name) =
    {name = name, balance = 0, history = []}
```
Maps are constructed similarly, with keys enclosed in square brackets
```sophia
  function example_map() : map(string, int) =
    {["key1"] = 1, ["key2"] = 2}
```
The empty map is written `{}`.

### Accessing values

Record fields access is written `r.f` and map lookup `m[k]`. For instance,
```sophia
  function get_balance(a : address, accounts : map(address, account)) =
    accounts[a].balance
```
Looking up a non-existing key in a map results in contract execution failing. A
default value to return for non-existing keys can be provided using the syntax
`m[k = default]`. See also `Map.member` and `Map.lookup` below.

### Updating a value

Record field updates are written `r{f = v}`. This creates a new record value
which is the same as `r`, but with the value of the field `f` replaced by `v`.
Similarly, `m{[k] = v}` constructs a map with the same values as `m` except
that `k` maps to `v`. It makes no difference if `m` has a mapping for `k` or
not.

It is possible to give a name to the old value of a field or mapping in an
update: instead of `acc{ balance = acc.balance + 100 }` it is possible to write
`acc{ balance @ b = b + 100 }`, binding `b` to `acc.balance`. When giving a
name to a map value (`m{ [k] @ x = v }`), the corresponding key must be present
in the map or execution fails, but a default value can be provided:
`m{ [k = default] @ x = v }`. In this case `x` is bound to `default` if
`k` is not in the map.

Updates can be nested:
```sophia
function clear_history(a : address, accounts : map(address, account)) : map(address, account) =
  accounts{ [a].history = [] }
```
This is equivalent to `accounts{ [a] @ acc = acc{ history = [] } }` and thus
requires `a` to be present in the accounts map. To have `clear_history` create
an account if `a` is not in the map you can write (given a function `empty_account`):
```sophia
  accounts{ [a = empty_account()].history = [] }
```

### Map implementation

Internally in the VM maps are implemented as hash maps and support fast lookup
and update. Large maps can be stored in the contract state and the size of the
map does not contribute to the gas costs of a contract call reading or updating
it.

## Strings

There is a builtin type `string`, which can be seen as an array of bytes.
Strings can be compared for equality (`==`, `!=`), used as keys in maps and
records, and used in builtin functions `String.length`, `String.concat` and
the hash functions described below.

Please refer to the `String` [library documentation](sophia_stdlib.md#string).

## Chars

There is a builtin type `char` (the underlying representation being an integer),
mainly used to manipulate strings via `String.to_list`/`String.from_list`.

Characters can also be introduced as character literals (`'x', '+', ...).

Please refer to the `Char` [library documentation](sophia_stdlib.md#char).

## Byte arrays

Byte arrays are fixed size arrays of 8-bit integers. They are described in hexadecimal system,
for example the literal `#cafe` creates a two-element array of bytes `ca` (202) and `fe` (254)
and thus is a value of type `bytes(2)`.

Please refer to the `Bytes` [library documentation](sophia_stdlib.md#bytes).

## Cryptographic builtins

Libraries [Crypto](sophia_stdlib.md#crypto) and [String](sophia_stdlib.md#string) provide functions to
hash objects, verify signatures etc. The `hash` is a type alias for `bytes(32)`.

## Authorization interface

When a Generalized account is authorized, the authorization function needs
access to the transaction and the transaction hash for the wrapped transaction. (A `GAMetaTx`
wrapping a transaction.) The transaction and the transaction hash is available in the primitive
`Auth.tx` and `Auth.tx_hash` respectively, they are *only* available during authentication if invoked by a
normal contract call they return `None`.

## Oracle interface
You can attach an oracle to the current contract and you can interact with oracles
through the Oracle interface.

For a full description of how Oracle works see
[Oracles](https://github.com/aeternity/protocol/blob/master/oracles/oracles.md#oracles).
For a functionality documentation refer to the [standard library](sophia_stdlib.md#oracle).

### Example

Example for an oracle answering questions of type `string` with answers of type `int`:
```sophia
contract Oracles =

  stateful entrypoint registerOracle(acct : address,
                                     sign : signature,   // Signed network id + oracle address + contract address
                                     qfee : int,
                                     ttl  : Chain.ttl) : oracle(string, int) =
     Oracle.register(acct, signature = sign, qfee, ttl)

  entrypoint queryFee(o : oracle(string, int)) : int =
    Oracle.query_fee(o)

  payable stateful entrypoint createQuery(o    : oracle_query(string, int),
                                          q    : string,
                                          qfee : int,
                                          qttl : Chain.ttl,
                                          rttl : int) : oracle_query(string, int) =
    require(qfee =< Call.value, "insufficient value for qfee")
    Oracle.query(o, q, qfee, qttl, RelativeTTL(rttl))

  stateful entrypoint extendOracle(o   : oracle(string, int),
                                   ttl : Chain.ttl) : unit =
    Oracle.extend(o, ttl)

  stateful entrypoint signExtendOracle(o    : oracle(string, int),
                                       sign : signature,   // Signed network id + oracle address + contract address
                                       ttl  : Chain.ttl) : unit =
    Oracle.extend(o, signature = sign, ttl)

  stateful entrypoint respond(o    : oracle(string, int),
                              q    : oracle_query(string, int),
                              sign : signature,        // Signed network id + oracle query id + contract address
                              r    : int) =
    Oracle.respond(o, q, signature = sign, r)

  entrypoint getQuestion(o : oracle(string, int),
                         q : oracle_query(string, int)) : string =
    Oracle.get_question(o, q)

  entrypoint hasAnswer(o : oracle(string, int),
                       q : oracle_query(string, int)) =
    switch(Oracle.get_answer(o, q))
      None    => false
      Some(_) => true

  entrypoint getAnswer(o : oracle(string, int),
                       q : oracle_query(string, int)) : option(int) =
    Oracle.get_answer(o, q)
```

### Sanity checks

When an Oracle literal is passed to a contract, no deep checks are performed.
For extra safety [Oracle.check](sophia_stdlib.md#check) and [Oracle.check_query](sophia_stdlib.md#check_query)
functions are provided.

## AENS interface

Contracts can interact with the
[æternity naming system](https://github.com/aeternity/protocol/blob/master/AENS.md).
For this purpose the [AENS](sophia_stdlib.md#aens) library was exposed.

### Example

In this example we assume that the name `name` already exists, and is owned by
an account with address `addr`. In order to allow a contract `ct` to handle
`name` the account holder needs to create a
[signature](#delegation-signature) `sig` of `addr | name.hash | ct.address`.

Armed with this information we can for example write a function that extends
the name if it expires within 1000 blocks:
```sophia
  stateful entrypoint extend_if_necessary(addr : address, name : string, sig : signature) =
    switch(AENS.lookup(name))
      None => ()
      Some(AENS.Name(_, FixedTTL(expiry), _)) =>
        if(Chain.block_height + 1000 > expiry)
          AENS.update(addr, name, Some(RelativeTTL(50000)), None, None, signature = sig)
```

And we can write functions that adds and removes keys from the pointers of the
name:
```sophia
  stateful entrypoint add_key(addr : address, name : string, key : string,
                              pt : AENS.pointee, sig : signature) =
    switch(AENS.lookup(name))
      None => ()
      Some(AENS.Name(_, _, ptrs)) =>
        AENS.update(addr, name, None, None, Some(ptrs{[key] = pt}), signature = sig)

  stateful entrypoint delete_key(addr : address, name : string,
                                 key : string, sig : signature) =
    switch(AENS.lookup(name))
      None => ()
      Some(AENS.Name(_, _, ptrs)) =>
        let ptrs = Map.delete(key, ptrs)
        AENS.update(addr, name, None, None, Some(ptrs), signature = sig)
```

*Note:* From the Iris hardfork more strict rules apply for AENS pointers, when
a Sophia contract lookup or update (bad) legacy pointers, the bad keys are
automatically removed so they will not appear in the pointers map.

## Events

Sophia contracts log structured messages to an event log in the resulting
blockchain transaction. The event log is quite similar to [Events in
Solidity](https://solidity.readthedocs.io/en/v0.4.24/contracts.html#events).
Events are further discussed in the [protocol](https://github.com/aeternity/protocol/blob/master/contracts/events.md).


To use events a contract must declare a datatype `event`, and events are then
logged using the `Chain.event` function:

```sophia
  datatype event
    = Event1(int, int, string)
    | Event2(string, address)

  Chain.event(e : event) : unit
```

The event can have 0-3 *indexed* fields, and an optional *payload* field. A
field is indexed if it fits in a 32-byte word, i.e.
- `bool`
- `int`
- `bits`
- `address`
- `oracle(_, _)`
- `oracle_query(_, _)`
- contract types
- `bytes(n)` for `n` ≤ 32, in particular `hash`

The payload field must be either a string or a byte array of more than 32 bytes.
The fields can appear in any order.

*NOTE:* Indexing is not part of the core æternity node.

Events are emitted by using the `Chain.event` function. The following function
will emit one Event of each kind in the example.

```sophia
  entrypoint emit_events() : () =
    Chain.event(Event1(42, 34, "foo"))
    Chain.event(Event2("This is not indexed", Contract.address))
```

### Argument order

It is only possible to have one (1) `string` parameter in the event, but it can
be placed in any position (and its value will end up in the `data` field), i.e.
```sophia
AnotherEvent(string, indexed address)

...

Chain.event(AnotherEvent("This is not indexed", Contract.address))
```
would yield exactly the same result in the example above!

## Compiler pragmas

To enforce that a contract is only compiled with specific versions of the
Sophia compiler, you can give one or more `@compiler` pragmas at the
top-level (typically at the beginning) of a file. For instance, to enforce that
a contract is compiled with version 4.3 of the compiler you write

```sophia
@compiler >= 4.3
@compiler <  4.4
```

Valid operators in compiler pragmas are `<`, `=<`, `==`, `>=`, and `>`. Version
numbers are given as a sequence of non-negative integers separated by dots.
Trailing zeros are ignored, so `4.0.0 == 4`. If a constraint is violated an
error is reported and compilation fails.

## Exceptions

Contracts can fail with an (uncatchable) exception using the built-in function

```sophia
abort(reason : string) : 'a
```

Calling abort causes the top-level call transaction to return an error result
containing the `reason` string. Only the gas used up to and including the abort
call is charged. This is different from termination due to a crash which
consumes all available gas.

For convenience the following function is also built-in:

```sophia
function require(b : bool, err : string) =
    if(!b) abort(err)
```

Aside from that, there is an almost equivalent function `exit`

```sophia
exit(reason : string) : 'a
```

Just like `abort`, it breaks the execution with the given reason. The difference
however is in the gas consumption — while `abort` returns unused gas, a call to
`exit` burns it all.

## Delegation signature

Some chain operations (`Oracle.<operation>` and `AENS.<operation>`) have an
optional delegation signature. This is typically used when a user/accounts
would like to allow a contract to act on it's behalf. The exact data to be
signed varies for the different operations, but in all cases you should prepend
the signature data with the `network_id` (`ae_mainnet` for the æternity mainnet, etc.).
