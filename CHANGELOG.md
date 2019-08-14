# Changelog
All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]
### Added
- New builtin function `Crypto.ecrecover_secp256k1: (hash, bytes(65)) => bytes(32)`
  for recovering Ethereum address from message hash and signature.

### Changed
- New syntax for tuple types. Now 0-tuple type is encoded as `unit` instead of `()` and
  regular tuples are encoded by interspersing inner types with `*`, for instance `int * string`. 
  Parens are not necessary. Note it only affects the types, values remain as their were before,
  so `(1, "a") : int * string`

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

[Unreleased]: https://github.com/aeternity/aesophia/compare/v3.2.0...HEAD
[3.2.0]: https://github.com/aeternity/aesophia/compare/v3.1.0...v3.2.0
[3.1.0]: https://github.com/aeternity/aesophia/compare/v3.0.0...v3.1.0
[3.0.0]: https://github.com/aeternity/aesophia/compare/v2.1.0...v3.0.0
[2.1.0]: https://github.com/aeternity/aesophia/compare/v2.0.0...v2.1.0
[2.0.0]: https://github.com/aeternity/aesophia/tag/v2.0.0
