# Sophia Compiler

This is the **sophia** compiler for the æternity system which compiles contracts written in **sophia** to [FATE](https://github.com/aeternity/protocol/blob/master/contracts/fate.md) instructions.

The compiler is currently being used three places

* [The command line compiler](https://github.com/aeternity/aesophia\_cli)
* [The HTTP compiler](https://github.com/aeternity/aesophia\_http)
* In [Aeternity node](https://github.com/aeternity/aeternity) tests

## Documentation

* [Smart Contracts on aeternity Blockchain](https://github.com/aeternity/protocol/blob/master/contracts/contracts.md).
* [Sophia Documentation](../).
* [Sophia Standard Library](../sophia\_stdlib.md).

## Versioning

Versioning should follow the [semantic versioning](https://semver.org/spec/v2.0.0) guidelines. Id est, given a version number MAJOR.MINOR.PATCH, increment the:

* MAJOR version when you make incompatible API changes
* MINOR version when you add functionality in a backwards compatible manner
* PATCH version when you make backwards compatible bug fixes

## Interface Modules

The basic modules for interfacing the compiler:

* [aeso\_compiler: the Sophia compiler](aeso\_compiler.md)
* [aeso\_aci: the ACI interface](../aeso\_aci.md)
