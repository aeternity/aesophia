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

`pp_assembler` - print the generated assembler code

The option `include_child_contract_symbols` includes the symbols of child contracts functions in the generated fate code. It is turned off by default to avoid making contracts bigger on chain.

The option `debug_info` includes information related to debugging in the compiler output. Currently this option only includes the mapping from variables to registers.

#### Options to control which compiler optimizations should run:

By default all optimizations are turned on, to disable an optimization, it should be
explicitly set to false and passed as a compiler option.

List of optimizations:

- optimize_inliner
- optimize_inline_local_functions
- optimize_bind_subexpressions
- optimize_let_floating
- optimize_simplifier
- optimize_drop_unused_lets
- optimize_push_consume
- optimize_one_shot_var
- optimize_write_to_dead_var
- optimize_inline_switch_target
- optimize_swap_push
- optimize_swap_pop
- optimize_swap_write
- optimize_constant_propagation
- optimize_prune_impossible_branches
- optimize_single_successful_branch
- optimize_inline_store
- optimize_float_switch_bod

#### check_call(ContractString, Options) -> CheckRet

Types
```
ContractString = string() | binary()
CheckRet = {ok,string(),{Types,Type | any()},Terms} | {error,Term}
Types = [Type]
Type = term()
```
Check a call in contract through the `__call` function.

#### version() -> {ok, Version} | {error, term()}

Types

``` erlang
Version = binary()
```

Get the current version of the Sophia compiler.
