# aesophia

This is the __sophia__ compiler for the æternity system which compiles contracts written in __sophia__ code to the æternity VM code.

For more information about æternity smart contracts and the sophia language see [Smart Contracts](https://github.com/aeternity/protocol/blob/master/contracts/contracts.md) and the [Sophia Language](https://github.com/aeternity/protocol/blob/master/contracts/sophia.md).

It is an OTP application written in Erlang and is by default included in
[the æternity node](https://github.com/aeternity/epoch). However, it can
also be included in other system to compile contracts coded in sophia which
can then be loaded into the æternity system.

## Modules

### aeso_compiler

The Sophia compiler

### Description

This module provides the interface to the standard Sophia compiler. It
returns the compiled module in a map which can then be loaded.

### Types
```erlang
contract_string() = string() | binary()
contract_map() = #{bytecode => binary(),
                   compiler_version => string(),
                   contract_souce => string(),
                   type_info => type_info()}
type_info()
errorstring() = binary()
```
### Exports

#### file(File)
#### file(File, Options) -> CompRet
#### from_string(ContractString, Options) -> CompRet

Types

``` erlang
ContractString = contract_string()
Options = [Option]
CompRet = {ok,ContractMap} | {error,ErrorString}
ContractMap = contract_map()
ErrorString = errorstring()
```

Compile a contract defined in a file or in a string.

The **pp_** options all print to standard output the following:

`pp_sophia_code` - print the input Sophia code.

`pp_ast` - print the AST of the code

`pp_types` - print information about the types

`pp_typed_ast` - print the AST with type information at each node

`pp_icode` - print the internal code structure

`pp_assembler` - print the generated assembler code

`pp_bytecode` - print the bytecode instructions

#### check_call(ContractString, Options) -> CheckRet

Types
```
ContractString = string() | binary()
CheckRet = {ok,string(),{Types,Type | any()},Terms} | {error,Term}
Types = [Type]
Type = term()
```
Check a call in contract through the `__call` function.

#### sophia_type_to_typerep(String) -> TypeRep

Types
``` erlang
 {ok,TypeRep} | {error, badtype}
```

Get the type representation of a type declaration.

#### version() -> Version

Types

``` erlang
Version = integer()
```

Get the current version of the Sophia compiler.
