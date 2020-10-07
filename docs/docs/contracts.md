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
Please refer to the [Chain](sophia_stdlib.md#Chain), [Contract](sophia_stdlib.md#Contract)
and the [Call](sophia_stdlib.md#Call) namespaces in the documentation.

#### Calling other contracts

To call a function in another contract you need the address to an instance of
the contract. The type of the address must be a contract type, which consists
of a number of type definitions and entrypoint declarations. For instance,

```javascript
// A contract type
contract VotingType =
  entrypoint vote : string => unit
```

Now given contract address of type `VotingType` you can call the `vote`
entrypoint of that contract:

```javascript
contract VoteTwice =
  entrypoint voteTwice(v : VotingType, alt : string) =
    v.vote(alt)
    v.vote(alt)
```

Contract calls take two optional named arguments `gas : int` and `value : int`
that lets you set a gas limit and provide tokens to a contract call. If omitted
the defaults are no gas limit and no tokens. Suppose there is a fee for voting:

```javascript
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

```javascript
  entrypoint pay(v : VotingType, amount : int) =
    Chain.spend(v.address, amount)
```

#### Protected contract calls

!!! attention
    This feature is not part of the current protocol version and could be implemented in a future protocol upgrade. 

If a contract call fails for any reason (for instance, the remote contract
crashes or runs out of gas, or the entrypoint doesn't exist or has the wrong
type) the parent call also fails. To make it possible to recover from failures,
contract calls takes a named argument `protected : bool` (default `false`).
The protected argument must be a literal boolean, and when set to `true`
changes the type of the contract call, wrapping the result in an `option` type.
If the call fails the result is `None`, otherwise it's `Some(r)` where `r` is
the return value of the call.
```sophia
contract VotingType =
  entrypoint : vote : string => unit
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

### Mutable state

Sophia does not have arbitrary mutable state, but only a limited form of
state associated with each contract instance.

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

#### Stateful functions

Top-level functions and entrypoints must be annotated with the
`stateful` keyword to be allowed to affect the state of the running contract.
For instance,

```javascript
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
* Call a `stateful` function in the current contract
* Call another contract with a non-zero `value` argument.

A `stateful` annotation *is not* required to

* Read the contract state.
* Issue an event using the `event` function.
* Call another contract with `value = 0`, even if the called function is stateful.

### Payable

#### Payable contracts

A concrete contract is by default *not* payable. Any attempt at spending to such
a contract (either a `Chain.spend` or a normal spend transaction) will fail. If a
contract shall be able to receive funds in this way it has to be declared `payable`:

```javascript
// A payable contract
payable contract ExampleContract =
  stateful entrypoint do_stuff() = ...
```

If in doubt, it is possible to check if an address is payable using
`Address.is_payable(addr)`.

#### Payable entrypoints

A contract entrypoint is by default *not* payable. Any call to such a function
(either a [Remote call](contracts.md#calling-other-contracts) or a contract call transaction)
that has a non-zero `value` will fail. Contract entrypoints that should be called
with a non-zero value should be declared `payable`.

```javascript
payable stateful entrypoint buy(to : address) =
  if(Call.value > 42)
    transfer_item(to)
  else
    abort("Value too low")
```

Note: In the Aeternity VM (AEVM) contracts and entrypoints were by default
payable until the Lima release.

### Namespaces

Code can be split into libraries using the `namespace` construct. Namespaces
can appear at the top-level and can contain type and function definitions, but
not entrypoints. Outside the namespace you can refer to the (non-private) names
by qualifying them with the namespace (`Namespace.name`).
For example,

```
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

### Splitting code over multiple files

!!! info
    This feature is currently not supported by the [AEstudio IDE](https://studio.aepps.com/)
    and shall only be used with the standalone compiler.

Code from another file can be included in a contract using an `include`
statement. These must appear at the top-level (outside the main contract). The
included file can contain one or more namespaces and abstract contracts. For
example, if the file `library.aes` contains

```
namespace Library =
  function inc(x) = x + 1
```

you can use it from another file using an `include`:

```
include "library.aes"
contract MyContract =
  entrypoint plus2(x) = Library.inc(Library.inc(x))
```

This behaves as if the contents of `library.aes` was textually inserted into
the file, except that error messages will refer to the original source
locations. The language will try to include each file at most one time automatically,
so even cyclic includes should be working without any special tinkering.

### Standard library

Sophia offers [standard library](sophia_stdlib.md) which exposes some 
primitive operations and some higher level utilities. The builtin
namespaces like `Chain`, `Contract`, `Map`
are included by default and are supported internally by the compiler.
Others like `List`, `Frac`, `Option` need to be manually included using the
`include` directive. For example
```
include "List.aes"
include "Pair.aes"
-- Map is already there!

namespace C =
  entrypoint keys(m : map('a, 'b)) : list('a) =
    List.map(Pair.fst, (Map.to_list(m)))
```

### Types
Sophia has the following types:

| Type                 | Description                                                                                 | Example                                                      |
|----------------------|---------------------------------------------------------------------------------------------|--------------------------------------------------------------|
| int                  | A 2-complement integer                                                                      | ```-1```                                                     |
| address              | Aeternity address, 32 bytes                                                                 | ```Call.origin```                                            |
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

### Literals
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

### Arithmetic

Sophia integers (`int`) are represented by 256-bit (AEVM) or arbitrary-sized (FATE) signed words and supports the following
arithmetic operations:
- addition (`x + y`)
- subtraction (`x - y`)
- multiplication (`x * y`)
- division (`x / y`), truncated towards zero
- remainder (`x mod y`), satisfying `y * (x / y) + x mod y == x` for non-zero `y`
- exponentiation (`x ^ y`)

All operations are *safe* with respect to overflow and underflow. On AEVM they behave as the corresponding
operations on arbitrary-size integers and fail with `arithmetic_error` if the
result cannot be represented by a 256-bit signed word. For example, `2 ^ 255`
fails rather than wrapping around to -2²⁵⁵.

The division and modulo operations also throw an arithmetic error if the
second argument is zero.

### Bit fields

Sophia integers do not support bit arithmetic. Instead there is a separate
type `bits`. See the standard library [documentation](sophia_stdlib.md#Bits).

On the AEVM a bit field is represented by a 256-bit word and reading or writing
a bit outside the 0..255 range fails with an `arithmetic_error`. On FATE a bit
field can be of arbitrary size (but it is still represented by the
corresponding integer, so setting very high bits can be expensive).

### Type aliases

Type aliases can be introduced with the `type` keyword and can be
parameterized. For instance

```
type number = int
type string_map('a) = map(string, 'a)
```

A type alias and its definition can be used interchangeably. Sophia does not support
higher-kinded types, meaning that following type alias is invalid: `type wrap('f, 'a) = 'f('a)`

### Algebraic data types

Sophia supports algebraic data types (variant types) and pattern matching. Data
types are declared by giving a list of constructors with
their respective arguments. For instance,

```
datatype one_or_both('a, 'b) = Left('a) | Right('b) | Both('a, 'b)
```

Elements of data types can be pattern matched against, using the `switch` construct:

```
function get_left(x : one_or_both('a, 'b)) : option('a) =
  switch(x)
    Left(x)    => Some(x)
    Right(_)   => None
    Both(x, _) => Some(x)
```

or directly in the left-hand side:
```
function
  get_left : one_or_both('a, 'b) => option('a)
  get_left(Left(x))    = Some(x)
  get_left(Right(_))   = None
  get_left(Both(x, _)) = Some(x)
```

*NOTE: Data types cannot currently be recursive.*

### Lists

A Sophia list is a dynamically sized, homogenous, immutable, singly
linked list. A list is constructed with the syntax `[1, 2, 3]`. The
elements of a list can be any of datatype but they must have the same
type. The type of lists with elements of type `'e` is written
`list('e)`. For example we can have the following lists:

```
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
```
[x + y | x <- [1,2,3,4,5], let k = x*x, if (k > 5), y <- [k, k+1, k+2]]
// yields [12,13,14,20,21,22,30,31,32]
```

Lists can be constructed using the range syntax using special `..` operator:
```
[1..4] == [1,2,3,4] 
```
The ranges are always ascending and have step equal to 1.


Please refer to the [standard library](sophia_stdlib.md#List) for the predefined functionalities.

### Maps and records

A Sophia record type is given by a fixed set of fields with associated,
possibly different, types. For instance
```
  record account = { name    : string,
                     balance : int,
                     history : list(transaction) }
```

Maps, on the other hand, can contain an arbitrary number of key-value bindings,
but of a fixed type. The type of maps with keys of type `'k` and values of type
`'v` is written `map('k, 'v)`. The key type can be any type that does not
contain a map or a function type.

Please refer to the [standard library](sophia_stdlib.md#Map) for the predefined functionalities.

#### Constructing maps and records

A value of record type is constructed by giving a value for each of the fields.
For the example above,
```
  function new_account(name) =
    {name = name, balance = 0, history = []}
```
Maps are constructed similarly, with keys enclosed in square brackets
```
  function example_map() : map(string, int) =
    {["key1"] = 1, ["key2"] = 2}
```
The empty map is written `{}`.

#### Accessing values

Record fields access is written `r.f` and map lookup `m[k]`. For instance,
```
  function get_balance(a : address, accounts : map(address, account)) =
    accounts[a].balance
```
Looking up a non-existing key in a map results in contract execution failing. A
default value to return for non-existing keys can be provided using the syntax
`m[k = default]`. See also `Map.member` and `Map.lookup` below.

#### Updating a value

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
```
function clear_history(a : address, accounts : map(address, account)) : map(address, account) =
  accounts{ [a].history = [] }
```
This is equivalent to `accounts{ [a] @ acc = acc{ history = [] } }` and thus
requires `a` to be present in the accounts map. To have `clear_history` create
an account if `a` is not in the map you can write (given a function `empty_account`):
```
  accounts{ [a = empty_account()].history = [] }
```

#### Map implementation

Internally in the VM maps are implemented as hash maps and support fast lookup
and update. Large maps can be stored in the contract state and the size of the
map does not contribute to the gas costs of a contract call reading or updating
it.

### Strings

There is a builtin type `string`, which can be seen as an array of bytes.
Strings can be compared for equality (`==`, `!=`), used as keys in maps and
records, and used in builtin functions `String.length`, `String.concat` and
the hash functions described below.

Please refer to the `String` [library documentation](sophia_stdlib.md#String).

### Byte arrays

Byte arrays are fixed size arrays of 8-bit integers. They are described in hexadecimal system,
for example the literal `#cafe` creates a two-element array of bytes `ca` (202) and `fe` (254)
and thus is a value of type `bytes(2)`.

Please refer to the `Bytes` [library documentation](sophia_stdlib.md#Bytes).


### Cryptographic builtins

Libraries [Crypto](sophia_stdlib.md#Crypto) and [String](sophia_stdlib.md#String) provide functions to 
hash objects, verify signatures etc. The `hash` is a type alias for `bytes(32)`.

#### AEVM note
The hash functions in `String` hash strings interpreted as byte arrays, and
the `Crypto` hash functions accept an element of any (first-order) type. The
result is the hash of the binary encoding of the argument as [described
below](#encoding-sophia-values-as-binaries). Note that this means that for `s :
string`, `String.sha3(s)` and `Crypto.sha3(s)` will give different results on AEVM.


### Authorization interface

When a Generalized account is authorized, the authorization function needs
access to the transaction and the transaction hash for the wrapped transaction. (A `GAMetaTx`
wrapping a transaction.) The transaction and the transaction hash is available in the primitive
`Auth.tx` and `Auth.tx_hash` respectively, they are *only* available during authentication if invoked by a
normal contract call they return `None`.

### Oracle interface
You can attach an oracle to the current contract and you can interact with oracles
through the Oracle interface.

For a full description of how Oracle works see
[Oracles](https://github.com/aeternity/protocol/blob/master/oracles/oracles.md#oracles).
For a functionality documentation refer to the [standard library](sophia_stdlib.md#Oracle).


#### Example

Example for an oracle answering questions of type `string` with answers of type `int`:
```
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
                              sign : signature,   // Signed network id + oracle address + contract address
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

#### Sanity checks

When an Oracle literal is passed to a contract, no deep checks are performed. 
For extra safety [Oracle.check](sophia_stdlib.md#check) and [Oracle.check_query](sophia_stdlib.md#check_query)
functions are provided.

### AENS interface

Contracts can interact with the
[Aeternity Naming System](https://github.com/aeternity/protocol/blob/master/AENS.md).
For this purpose the [AENS](sophia_stdlib.md#AENS) library was exposed.

#### Example

In this example we assume that the name `name` already exists, and is owned by
an account with address `addr`. In order to allow a contract `ct` to handle
`name` the account holder needs to create a
[signature](examples.md#delegation-signature) `sig` of `addr | name.hash | ct.address`.

Armed with this information we can for example write a function that extends
the name if it expires within 1000 blocks:
```
  stateful entrypoint extend_if_necessary(addr : address, name : string, sig : signature) =
    switch(AENS.lookup(name))
      None => ()
      Some(AENS.Name(_, FixedTTL(expiry), _)) =>
        if(Chain.block_height + 1000 > expiry)
          AENS.update(addr, name, Some(RelativeTTL(50000)), None, None, signature = sig)
```

And we can write functions that adds and removes keys from the pointers of the
name:
```
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


### Events

Sophia contracts log structured messages to an event log in the resulting
blockchain transaction. The event log is quite similar to [Events in
Solidity](https://solidity.readthedocs.io/en/v0.4.24/contracts.html#events).
Events are further discussed in the [protocol](https://github.com/aeternity/protocol/blob/master/contracts/events.md).


To use events a contract must declare a datatype `event`, and events are then
logged using the `Chain.event` function:

```
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

*NOTE:* Indexing is not part of the core aeternity node.

Events are emitted by using the `Chain.event` function. The following function
will emit one Event of each kind in the example.

```
  entrypoint emit_events() : () =
    Chain.event(TheFirstEvent(42))
    Chain.event(AnotherEvent(Contract.address, "This is not indexed"))
```

#### Argument order

It is only possible to have one (1) `string` parameter in the event, but it can
be placed in any position (and its value will end up in the `data` field), i.e.
```
AnotherEvent(string, indexed address)

...

Chain.event(AnotherEvent("This is not indexed", Contract.address))
```
would yield exactly the same result in the example above!

### Compiler pragmas

To enforce that a contract is only compiled with specific versions of the
Sophia compiler, you can give one or more `@compiler` pragmas at the
top-level (typically at the beginning) of a file. For instance, to enforce that
a contract is compiled with version 4.3 of the compiler you write

```
@compiler >= 4.3
@compiler <  4.4
```

Valid operators in compiler pragmas are `<`, `=<`, `==`, `>=`, and `>`. Version
numbers are given as a sequence of non-negative integers separated by dots.
Trailing zeros are ignored, so `4.0.0 == 4`. If a constraint is violated an
error is reported and compilation fails.

### Exceptions

Contracts can fail with an (uncatchable) exception using the built-in function

```
abort(reason : string) : 'a
```

Calling abort causes the top-level call transaction to return an error result
containing the `reason` string. Only the gas used up to and including the abort
call is charged. This is different from termination due to a crash which
consumes all available gas.

For convenience the following function is also built-in:

```
function require(b : bool, err : string) =
    if(!b) abort(err)
```
