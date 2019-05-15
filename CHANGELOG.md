# Changelog
All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]
### Added
- `stateful` annotations are now properly enforced. Functions must be marked stateful
  in order to update the state or spend tokens.
### Changed
### Removed

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

[Unreleased]: https://github.com/aeternity/aesophia/compare/v2.1.0...HEAD
[2.1.0]: https://github.com/aeternity/aesophia/compare/v2.0.0...v2.1.0
[2.0.0]: https://github.com/aeternity/aesophia/tag/v2.0.0
