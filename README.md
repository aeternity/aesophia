# aesophia

This is the __sophia__ compiler for the æternity system which compiles contracts written in __sophia__ code to the æternity VM code.

For more information about æternity smart contracts and the sophia language see [Smart Contracts](https://github.com/aeternity/protocol/blob/master/contracts/contracts.md) and the [Sophia Language](https://github.com/aeternity/protocol/blob/master/contracts/sophia.md).

It is an OTP application written in Erlang and is by default included in
[the æternity node](https://github.com/aeternity/epoch). However, it can
also be included in other systems to compile contracts coded in sophia which
can then be loaded into the æternity system.

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
