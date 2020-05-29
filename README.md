# aesophia

This is the __sophia__ compiler for the æternity system which compiles contracts written in __sophia__ to [FATE](https://github.com/aeternity/protocol/blob/master/contracts/fate.md) instructions.

The compiler is currently being used three places
 - [The command line compiler](https://github.com/aeternity/aesophia_cli)
 - [The HTTP compiler](https://github.com/aeternity/aesophia_http)
 - In [Aeternity node](https://github.com/aeternity/aeternity) tests

## Documentation

* [Smart Contracts on aeternity Blockchain](https://github.com/aeternity/protocol/blob/master/contracts/contracts.md).
* [Sophia Documentation](docs/sophia.md).
* [Sophia Standard Library](docs/sophia_stdlib.md).

## Versioning

`aesophia` has a version that is only loosely connected to the version of the
Aeternity node - in principle they will share the major version but not
minor/patch version. The `aesophia` compiler version MUST be bumped whenever
there is a change in how byte code is generated, but it MAY also be bumped upon
API changes etc.

## Interface Modules

The basic modules for interfacing the compiler:

* [aeso_compiler: the Sophia compiler](./docs/aeso_compiler.md)
* [aeso_aci: the ACI interface](./docs/aeso_aci.md)
