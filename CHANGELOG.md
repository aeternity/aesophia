# Changelog
All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [CERES 8.0.0]
### Added
- Bitwise operations for integers: `band`, `bor`, `bxor`, `bnot`, `<<` and `>>`.
- `Int.mulmod` - combined builtin operation for multiplication and modulus.
- `Crypto.poseidon` - a ZK/SNARK-friendly hash function (over the BLS12-381 scalar field).
- `Address.to_bytes` - convert an address to its binary representation (for hashing, etc.).
- Raw data pointers added to AENS. In short we have introduced a new namespace
  `AENSv2`; they contain types similar to the old `AENS`; `AENS.name` and
  `AENS.pointee`, where the latter now has a constructor `DataPt(string)`. All
  AENS actions have been moved to `AENSv2`, and `AENSv2.lookup` and
  `AENSv2.update` consume and produce the new types. The old `AENS` namespace
  only contains the old datatypes, that can be used to interface existing
  contracts. Standard library `AENSCompat` is added to convert between old and
  new pointers.
- Introduce arbitrary sized binary arrays (type `bytes()`); adding `Bytes.split_any`,
  `Bytes.to_fixed_size`, `Bytes.to_any_size`, `Bytes.size`, `String.to_bytes`,
  and `Int.to_bytes`; and adjust `Bytes.concat` to allow both fixed and arbitrary
  sized byte arrays.
### Changed
### Removed
- `Bitwise.aes` standard library is removed - the builtin operations are superior.

## [Unreleased]
### Added
### Changed
### Removed
### Fixed

## [7.4.1]
### Changed
- Improve how includes with relative paths are resolved during parsing/compilation. Relative
  include paths are now always relative to the file containing the `include` statement.
### Fixed
- Disable unused type warnings for types used inside of records.

## [7.4.0]
### Changed
- Names of lifted lambdas now consist of parent function's name and their
  position in the source code.
### Fixed
- Lifted lambdas get their names assigned deterministically.

## [7.3.0]
### Fixed
- Fixed a bug with polymorphism that allowed functions with the same name but different type to be considered as implementations for their corresponding interface function.
- Fixed a bug in the byte code optimization that incorrectly reordered dependent instructions.

## [7.2.1]
### Fixed
- Fixed bugs with the newly added debugging symbols

## [7.2.0]
### Added
- Toplevel compile-time constants
  ```
  namespace N =
    let nc = 1
  contract C =
    let cc = 2
  ```
- API functions for encoding/decoding Sophia values to/from FATE.
### Removed
- Remove the mapping from variables to FATE registers from the compilation output.
### Fixed
- Warning about unused include when there is no include.

## [7.1.0]
### Added
- Options to enable/disable certain optimizations.
- The ability to call a different instance of the current contract
  ```
  contract Main =
    entrypoint spend(x : int) : int = x
    entrypoint f(c : Main) : int = c.spend(10)
  ```
- Return a mapping from variables to FATE registers in the compilation output.
- Hole expression.
### Changed
- Type definitions serialised to ACI as `typedefs` field instead of `type_defs` to increase compatibility.
- Check contracts and entrypoints modifiers when implementing interfaces.
- Contracts can no longer be used as namespaces.
- Do not show unused stateful warning for functions that call other contracts with a non-zero value argument.
### Fixed
- Typechecker crashes if Chain.create or Chain.clone are used without arguments.

## [7.0.1]
### Added
- Add CONTRIBUTING.md file.
### Changed
- Update Sophia syntax docs to include missing information about existing syntax.
### Fixed
- [404](https://github.com/aeternity/aesophia/issues/404) Contract polymorphism crashes on non-obvious child contract typing.

## [7.0.0]
### Added
- Added support for `EXIT` opcode via `exit : (string) => 'a` function (behaves same as `ABORT`, but consumes all gas).
- Compiler warnings for the following: shadowing, negative spends, division by zero, unused functions, unused includes, unused stateful annotations, unused variables, unused parameters, unused user-defined type, dead return value.
- The pipe operator |>
  ```
  [1, 2, 3] |> List.first |> Option.is_some  // Option.is_some(List.first([1, 2, 3]))
  ```
- Allow binary operators to be used as lambdas
  ```
  function sum(l : list(int)) : int = foldl((+), 0, l)
  function logical_and(x, y) = (&&)(x, y)
  ```
- Contract interfaces polymorphism
### Changed
- Error messages have been restructured (less newlines) to provide more unified errors. Also `pp_oneline/1` has been added.
- Ban empty record definitions (e.g. `record r = {}` would give an error).
### Removed
- Support for AEVM has been entirely wiped

## [6.1.0] - 2021-10-20
### Added
- `Bitwise` stdlib
- `Set` stdlib
- `Option.force_msg`
- Loading namespaces into the current scope (e.g. `using Pair`)
- Assign patterns to variables (e.g. `let x::(t = y::_) = [1, 2, 3, 4]` where `t == [2, 3, 4]`)
- Add builtin types (`AENS.name, AENS.pointee, Chain.ttl, Chain.base_tx, Chain.ga_meta_tx, Chain.paying_for_tx`) to
  the calldata and result decoder
- Patterns guards
  ```
  switch(x)
    a::[] | a > 10 => 1
    _              => 2
  ```
  ```
  function
    f(a::[]) | a > 10 = 1
    f(_)              = 2
  ```
### Changed
- Fixed the ACI renderer, it shouldn't drop the `stateful` modifier

## [6.0.2] 2021-07-05
### Changed
- `List.from_to_step` now forbids non-positive step (this change does
  *not* alter the behavior of the previously deployed contracts)
- Fixed leaking state between contracts

## [6.0.1] 2021-06-24
### Changed
- Fixed a bug in calldata encoding for contracts containing multiple contracts
- Fixed a missing `include` in the `Frac` standard library

## [6.0.0] 2021-05-26
### Added
- Child contracts
- `Chain.clone`
- `Chain.create`
- `Chain.bytecode_hash`
- Minor support for variadic functions
- `void` type that represents an empty type
- `Call.fee` builtin
### Changed
- Contract interfaces must be now invocated by `contract interface` keywords
- `main` keyword to indicate the main contract in case there are child contracts around
- `List.sum` and `List.product` no longer use `List.foldl`
### Removed

## [5.0.0] 2021-04-30
### Added
- A new and improved [`String` standard library](https://github.com/aeternity/aesophia/blob/master/docs/sophia_stdlib.md#string)
  has been added. Use it by `include "String.aes"`. It includes functions for
  turning strings into lists of characters for detailed manipulation. For
  example:
  ```
  include "String.aes"
  contract C =
    entrypoint filter_all_a(s: string) : string =
      String.from_list(List.filter((c : char) => c != 'a', String.to_list(s)))
  ```
  will return a list with all `a`'s removed.

  There are also convenience functions `split`, `concat`, `to_upper`,
  `to_lower`, etc.

  All String functions in FATEv2 operate on unicode code points.
- Operations for pairing-based cryptography has been added the operations
  are in the standard library [BLS12_381](https://github.com/aeternity/aesophia/blob/master/docs/sophia_stdlib.md#bls12_381).
  With these operations it is possible to do Zero Knowledge-proofs, etc.
  The operations are for the BLS12-381 curve (as the name suggests).
- Calls to functions in other contracts (i.e. _remote calls_) can now be
  [`protected`](https://github.com/aeternity/aesophia/blob/master/docs/sophia.md#protected-contract-calls).
  If a contract call fails for any reason (for instance, the remote contract
  crashes or runs out of gas, or the entrypoint doesn't exist or has the
  wrong type) the parent call also fails. To make it possible to recover
  from failures, contract calls takes a named argument `protected : bool`
  (default `false`).

  If `protected = true` the result of the contract call is wrapped in an
  `option`, and `Some(value)` indicates a succesful execution and `None`
  indicates that the contract call failed. Note: any gas consumed until
  the failure is still charged, but all side effects in the remote
  contract are rolled back on failure.
- A new chain operation [`AENS.update`](https://github.com/aeternity/aesophia/blob/master/docs/sophia.md#aens-interface)
  is supported.
- New chain exploring operations `AENS.lookup` and `Oracle.expiry` to
  look up an AENS record and the expiry of an Oracle respectively, are added.
- Transaction introspection (`Auth.tx`) has been added. When a Generalized
  account is authorized, the authorization function needs access to the
  transaction (and the transaction hash) for the wrapped transaction. The
  transaction and the transaction hash is available `Auth.tx`, it is only
  available during authentication if invoked by a normal contract call
  it returns `None`. Example:
  ```
  switch(Auth.tx)
    None      => abort("Not in Auth context")
    Some(tx0) =>
      switch(tx0.tx)
        Chain.SpendTx(_, amount, _)  => amount > 400
        Chain.ContractCallTx(_, _)   => true
        _                            => false
  ```
- A debug mode is a added to the compiler. Right now its only use is to
  turn off hermetization.
### Changed
- The function `Chain.block_hash(height)` is now (in FATEv2) defined for
  the current height - this used to be an error.
- Standard library: Sort is optimized to do `mergesort` and a `contains`
  function is added.
- Improved type errors and explicit errors for some syntax errors (empty code
  blocks, etc.).
- Compiler optimization: The ACI is generated alongside bytecode. This means
  that multiple compiler passes can be avoided.
- Compiler optimization: Improved parsing (less stack used when transpiled).
- A bug where constraints were handled out of order fixed.
- Fixed calldata decoding for singleton records.
- Improved the documentation w.r.t. signatures, especially stressing the fact that
  the network ID is a part of what is signed.
### Removed

## [4.3.0]
### Added
- Added documentation (moved from `protocol`)
- `Frac.aes` – library for rational numbers
- Added some more meaningful error messages
- Exported several parsing functionalities
 - With option `keep_included` it is possible to see which files were included during the parse
 - There is a function `run_parser` that be used to evaluate any parsing rule
 - Exported parsers: `body`, `type` and `decl`
### Changed
- Performance improvements in the standard library
- Fixed ACI encoder to handle `-` unary operator
- Fixed including by absolute path
- Fixed variant type printing in the ACI error messages
- Fixed pretty printing of combined function clauses
### Removed
- `let` definitions are no longer supported in the toplevel of the contract
- type declarations are no longer supported

## [4.2.0] - 2020-01-15
### Added
- Allow separate entrypoint/function type signature and definition, and pattern
  matching in left-hand sides:
  ```
    function
      length : list('a) => int
      length([])      = 0
      length(x :: xs) = 1 + length(xs)
  ```
- Allow pattern matching in list comprehension generators (filtering out match
  failures):
  ```
    function somes(xs : list(option('a))) : list('a) =
      [ x | Some(x) <- xs ]
  ```
- Allow pattern matching in let-bindings (aborting on match failures):
  ```
    function test(m : map(int, int)) =
        let Some(x) = Map.lookup(m, 0)
        x
  ```
### Changed
- FATE code generator improvements.
- Bug fix: Handle qualified constructors in patterns.
- Bug fix: Allow switching also on negative numbers.
### Removed

## [4.1.0] - 2019-11-26
### Added
- Support encoding and decoding bit fields in call arguments and results.
### Changed
- Various improvements to FATE code generator.
### Removed

## [4.0.0] - 2019-10-11
### Added
- `Address.to_contract` - casts an address to a (any) contract type.
- Pragma to check compiler version, e.g. `@compiler >= 4.0`.
- Handle numeric escapes, i.e. `"\x19Ethereum Signed Message:\n"`, and similar strings.
- `Bytes.concat` and `Bytes.split` are added to be able to
  (de-)construct byte arrays.
- `[a..b]` language construct, returning the list of numbers between
  `a` and `b` (inclusive). Returns the empty list if `a` > `b`.
- [Standard libraries](https://github.com/aeternity/aesophia/blob/master/docs/sophia_stdlib.md)
- Checks that `init` is not called from other functions.
- FATE backend - the compiler is able to produce VM code for both `AEVM` and `FATE`. Many
  of the APIs now take `{backend, aevm | fate}` to decide wich backend to produce artifacts
  for.
- New builtin functions `Crypto.ecrecover_secp256k1: (hash, bytes(65)) => option(bytes(20))`
  and `Crypto.ecverify_secp256k1 : (hash, bytes(20), bytes(65)) => bool` for recovering
  and verifying an Ethereum address for a message hash and a signature.
- Sophia supports list comprehensions known from languages like Python, Haskell or Erlang.
  Example syntax:
```
[x + y | x <- [1,2,3,4,5], let k = x*x, if (k > 5), y <- [k, k+1, k+2]]
// yields [12,13,14,20,21,22,30,31,32]
```
- A new contract, and endpoint, modifier `payable` is introduced. Contracts, and enpoints,
  that shall be able to receive funds should be marked as payable. `Address.is_payable(a)`
  can be used to check if an (contract) address is payable or not.
### Changed
- Nice type error if contract function is called as from a namespace.
- Fail on function definitions in contracts other than the main contract.
- Bug fix in variable optimization - don't discard writes to the store/state.
- Bug fixes in error reporting.
- Bug fix in variable liveness analysis for FATE.
- Error messages are changed into a uniform format, and more helpful
  messages have been added.
- `Crypto.<hash_fun>` and `String.<hash_fun>` for byte arrays now only
  hash the actual byte array - not the internal ABI format.
- More strict checks for polymorphic oracles and higher order oracles
  and entrypoints.
- `AENS.claim` is updated with a `NameFee` field - to be able to do
  name auctions within contracts.
- Fixed a bug in `Bytes.to_str` for AEVM.
- New syntax for tuple types. Now 0-tuple type is encoded as `unit` instead of `()` and
  regular tuples are encoded by interspersing inner types with `*`, for instance `int * string`.
  Parens are not necessary. Note it only affects the types, values remain as their were before,
  so `(1, "a") : int * string`
- The `AENS.transfer` and `AENS.revoke` functions have been updated to take a name `string`
  instead of a name `hash`.
- Fixed a bug where the `AEVM` backend complained about a missing `init` function when
  trying to generate calldata from an ACI-generated interface.
- Compiler now returns the ABI-version in the compiler result map.
- Renamed `Crypto.ecverify` and `Crypto.ecverify_secp256k1` into `Crypto.verify_sig` and
  `Crypto.verify_sig_secp256k1` respectively.
### Removed

## [3.2.0] - 2019-06-28
### Added
- New builtin function `require : (bool, string) => ()`. Defined as
    ```
    function require(b, err) = if(!b) abort(err)
    ```
- New builtin functions
    ```
    Bytes.to_str : bytes(_) => string
    Bytes.to_int : bytes(_) => int
    ```
  for converting a byte array to a hex string and interpreting it as a
  big-endian encoded integer respectively.
### Changed
- Public contract functions must now be declared as *entrypoints*:
  ```
  contract Example =
    // Exported
    entrypoint exported_fun(x) = local_fun(x)
    // Not exported
    function local_fun(x) = x
  ```
  Functions in namespaces still use `function` (and `private function` for
  private functions).
- The return type of `Chain.block_hash(height)` has changed, it used to
  be `int`, where `0` denoted an incorrect height. New return type is
  `option(hash)`, where `None` represents an incorrect height.
- Event name hashes now use BLAKE2b instead of Keccak256.
- Fixed bugs when defining record types in namespaces.
- Fixed a bug in include path handling when passing options to the compiler.
### Removed

## [3.1.0] - 2019-06-03
### Added
### Changed
- Keyword `indexed` is now optional for word typed (`bool`, `int`, `address`,
  ...) event arguments.
- State variable pretty printing now produce `'a, 'b, ...` instead of `'1, '2, ...`.
- ACI is restructured and improved:
    - `state` and `event` types (if present) now appear at the top level.
    - Namespaces and remote interfaces are no longer ignored.
    - All type definitions are included in the interface rendering.
    - API functions are renamed, new functions are `contract_interface`
      and `render_aci_json`.
- Fixed a bug in `create_calldata`/`to_sophia_value` - it can now handle negative
  literals.
### Removed

## [3.0.0] - 2019-05-21
### Added
- `stateful` annotations are now properly enforced. Functions must be marked stateful
  in order to update the state or spend tokens.
- Primitives `Contract.creator`, `Address.is_contract`, `Address.is_oracle`,
  `Oracle.check` and `Oracle.check_query` has been added to Sophia.
- A byte array type `bytes(N)` has been added to generalize `hash (== bytes(32))` and
  `signature (== bytes(64))` and allow for byte arrays of arbitrary fixed length.
- `Crypto.ecverify_secp256k1` has been added.
### Changed
- Address literals (+ Oracle, Oracle query and remote contracts) have been changed
  from `#<hex>` to address as `ak_<base58check>`, oracle `ok_<base58check>`,
  oracle query `oq_<base58check>` and remote contract `ct_<base58check>`.
- The compilation and typechecking of `letfun` (e.g. `let m(f, xs) = map(f, xs)`) was
  not working properly and has been fixed.
### Removed
- `let rec` has been removed from the language, it has never worked.
- The standalone CLI compiler is served in the repo `aeternity/aesophia_cli` and has
  been completely removed from `aesophia`.

## [2.1.0] - 2019-04-11
### Added
- Stubs (not yet wired up) for compilation to FATE
- Add functions specific for Calldata decoding
- Support for `Auth.tx_hash`, not available in AEVM until Fortuna release

### Changed
- Improvements to the ACI generator

## [2.0.0] - 2019-03-11
### Added
- Add `Crypto.ecverify` to the compiler.
- Add `Crypto.sha3`, `Crypto.blake2`, `Crypto.sha256`, `String.blake2` and
  `String.sha256` to the compiler.
- Add the `bits` type for working with bit fields in Sophia.
- Add Namespaces to Sophia in order to simplify using library contracts, etc.
- Add a missig type check on the `init` function - detects programmer errors earlier.
- Add the ACI (Aeternity Contract Interface) generator.

### Changed
- Use native bit shift operations in builtin functions, reducing gas cost.
- Improve type checking of `record` fields - generates more understandable error messages.
- Improved, more coherent, error messages.
- Simplify calldata creation - instead of passing a compiled contract, simply
  pass a (stubbed) contract string.

[Unreleased]: https://github.com/aeternity/aesophia/compare/v7.4.1...HEAD
[7.4.1]: https://github.com/aeternity/aesophia/compare/v7.4.0...v7.4.1
[7.4.0]: https://github.com/aeternity/aesophia/compare/v7.3.0...v7.4.0
[7.3.0]: https://github.com/aeternity/aesophia/compare/v7.2.1...v7.3.0
[7.2.1]: https://github.com/aeternity/aesophia/compare/v7.2.0...v7.2.1
[7.2.0]: https://github.com/aeternity/aesophia/compare/v7.1.0...v7.2.0
[7.1.0]: https://github.com/aeternity/aesophia/compare/v7.0.1...v7.1.0
[7.0.1]: https://github.com/aeternity/aesophia/compare/v7.0.0...v7.0.1
[7.0.0]: https://github.com/aeternity/aesophia/compare/v6.1.0...v7.0.0
[6.1.0]: https://github.com/aeternity/aesophia/compare/v6.0.2...v6.1.0
[6.0.2]: https://github.com/aeternity/aesophia/compare/v6.0.1...v6.0.2
[6.0.1]: https://github.com/aeternity/aesophia/compare/v6.0.0...v6.0.1
[6.0.0]: https://github.com/aeternity/aesophia/compare/v5.0.0...v6.0.0
[5.0.0]: https://github.com/aeternity/aesophia/compare/v4.3.0...v5.0.0
[4.3.0]: https://github.com/aeternity/aesophia/compare/v4.2.0...v4.3.0
[4.2.0]: https://github.com/aeternity/aesophia/compare/v4.1.0...v4.2.0
[4.1.0]: https://github.com/aeternity/aesophia/compare/v4.0.0...v4.1.0
[4.0.0]: https://github.com/aeternity/aesophia/compare/v3.2.0...v4.0.0
[3.2.0]: https://github.com/aeternity/aesophia/compare/v3.1.0...v3.2.0
[3.1.0]: https://github.com/aeternity/aesophia/compare/v3.0.0...v3.1.0
[3.0.0]: https://github.com/aeternity/aesophia/compare/v2.1.0...v3.0.0
[2.1.0]: https://github.com/aeternity/aesophia/compare/v2.0.0...v2.1.0
[2.0.0]: https://github.com/aeternity/aesophia/tag/v2.0.0
