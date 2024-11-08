# aeso_compiler

### Module

### aeso_compiler

The Sophia compiler

### Description

This module provides the interface to the standard Sophia compiler. It
returns the compiled module in a map which can then be loaded.

### Types
``` erlang
contract_string() = string() | binary()
contract_map() = #{bytecode => binary(),
                   compiler_version => binary(),
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

#### version() -> {ok, Version} | {error, term()}

Types

``` erlang
Version = binary()
```

Get the current version of the Sophia compiler.
