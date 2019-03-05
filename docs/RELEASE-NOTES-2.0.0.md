# About this release

This is the `aesophia` compiler version 2.0.0. The main changes compared to version 1.2.0 are:

* Add `Crypto.ecverify` to the compiler.
* Add `Crypto.sha3`, `Crypto.blake2`, `Crypto.sha256`, `String.blake2` and
  `String.sha256` to the compiler.
* Add the `bits` type for working with bit fields in Sophia.
* Use native bit shift operations in builtin functions, reducing gas cost.
* Add Namespaces to Sophia in order to simplify using library contracts, etc.
* Simplify calldata creation - instead of passing a compiled contract, simply
  pass a (stubbed) contract string.
* Add a missig type check on the `init` function - detects programmer errors earlier.
* Improve type checking of `record` fields - generates more understandable error messages.
* Improved, more coherent, error messages.
* Add the ACI (Aeternity Contract Interface) generator.
