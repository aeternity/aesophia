# aeso_compiler

### What this is

`aeso_compiler` is the high-level API to compile Sophia smart contracts to FATE bytecode. Think of it as a library that takes source code through the classic compiler stages (parse, type check, IR, backend) and gives you both intermediate results and final bytecode.

### The compilation pipeline

```
Source (.aes)
   │
   ├─ Parse → AST
   │
   ├─ Type inference → Typed AST
   │
   ├─ IR Lowering → fcode + env
   │
   └─ Backend → FATE → Serialized bytecode
```

- The orchestration lives in `src/pipeline/aeso_pipeline.erl`.
- Frontend parsing is in `src/frontend` (scanner, parser, includes, pretty printing).
- Typing lives in `src/typing`.
- Backends (e.g., FATE) live in `src/backend`.

### Quick start: compile from a file or string

```erlang
{ok, Map} = aeso_compiler:file("contracts/simple.aes").
%% Map contains keys like: byte_code, fate_code, compiler_version, warnings

Source = "contract Simple =\n  entrypoint add(x : int, y : int) = x + y\n".
{ok, Map2} = aeso_compiler:from_string(Source, []).
```

Get intermediate representations without producing bytecode:

```erlang
IR = aeso_compiler:string_to_code(Source, []).
%% IR#{ast := Ast, unfolded_typed_ast := TypedAst, fcode := FCode, warnings := Warnings}
```

### Value and calldata helpers

- Build calldata for an entrypoint call:
```erlang
{ok, Calldata} = aeso_compiler:create_calldata(Source, "add", ["1", "2"], []).
```
- Decode calldata (types and values):
```erlang
{ok, Types, Values} = aeso_compiler:decode_calldata(Source, "add", Calldata, []).
```
- Encode/decode individual values:
```erlang
FateVal = aeso_compiler:encode_value(Source, "int", 42, []).
SophiaVal = aeso_compiler:decode_value(Source, "int", FateVal, []).
```
- Decode a contract call result back to a Sophia expression:
```erlang
{ok, Expr} = aeso_compiler:to_sophia_value(Source, "add", ok, FateBinary, []).
```

### Printing helpers (developer visibility)

Pass any of these atoms inside the `Options` list to print intermediate forms:
- `pp_sophia_code`: input Sophia code
- `pp_ast`: AST
- `pp_types`: type information
- `pp_typed_ast`: typed AST
- `pp_assembler`: generated assembler/FATE code

Example:
```erlang
Opts = [pp_sophia_code, pp_ast, pp_types, pp_typed_ast, pp_assembler].
{ok, _} = aeso_compiler:from_string(Source, Opts).
```

### Options overview

Common options you may use:
- `{include, {file_system, [Dir1, Dir2, ...]}}`: where to look for includes
- `{src_file, string()}` and `{src_dir, string()}`: source metadata for better errors
- `{aci, Type}`: include ACI (contract interface) in result; see `aeso_aci`
- `no_code`: skip code emission when you only analyze
- `keep_included`: keep included files in certain outputs
- `debug_mode`: enable extra diagnostics (when supported)

Note: Additional backend and optimization flags may exist; see source for specifics.

### API reference (selected)

- `file(File) -> {ok, Map} | {error, Errors}`
- `file(File, Options) -> {ok, Map} | {error, Errors}`
- `from_string(ContractString, Options) -> {ok, Map} | {error, Errors}`
- `string_to_code(ContractString, Options) -> Map` (ASTs, fcode, env, warnings)
- `create_calldata(Code, Fun, ArgStrings[, Options]) -> {ok, binary()} | {error, Errors}`
- `decode_calldata(Code, Fun, Calldata[, Options]) -> {ok, [Type], [Expr]} | {error, Errors}`
- `encode_value(Code, Type, Value, Options)` / `decode_value(Code, Type, FateValue, Options)`
- `to_sophia_value(Code, Fun, ok|error|revert, Binary[, Options]) -> {ok, Expr} | {error, Errors}`
- `version() -> {ok, VersionBin} | {error, term()}`

### Errors and warnings

Most functions return either `{ok, ...}` or `{error, [aeso_errors:error()]}`. Warnings are returned in the result maps under the `warnings` key, not as errors. Parse/type/validation errors include precise source positions where possible.

### See also

- `src/pipeline/aeso_pipeline.erl`: the orchestrator for the stages
- `src/frontend/aeso_parser.erl`: parsing and includes
- `src/typing/aeso_ast_infer_types.erl`: type inference
- `src/ir/aeso_ast_to_fcode.erl`: IR lowering
- `src/backend/fate/*`: FATE backend and serialization
