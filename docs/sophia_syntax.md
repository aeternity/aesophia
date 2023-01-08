# Syntax

## Lexical syntax

### Comments

Single line comments start with `//` and block comments are enclosed in `/*`
and `*/` and can be nested.

### Keywords

```
contract include let switch type record datatype if elif else function
stateful payable true false mod public entrypoint private indexed namespace
interface main using as for hiding
```

### Tokens

- `Id = [a-z_][A-Za-z0-9_']*` identifiers start with a lower case letter.
- `Con = [A-Z][A-Za-z0-9_']*` constructors start with an upper case letter.
- `QId = (Con\.)+Id` qualified identifiers (e.g. `Map.member`)
- `QCon = (Con\.)+Con` qualified constructor
- `TVar = 'Id` type variable (e.g `'a`, `'b`)
- `Int = [0-9]+(_[0-9]+)*|0x[0-9A-Fa-f]+(_[0-9A-Fa-f]+)*` integer literal with optional `_` separators
- `Bytes = #[0-9A-Fa-f]+(_[0-9A-Fa-f]+)*` byte array literal with optional `_` separators
- `String` string literal enclosed in `"` with escape character `\`
- `Char` character literal enclosed in `'` with escape character `\`
- `AccountAddress` base58-encoded 32 byte account pubkey with `ak_` prefix
- `ContractAddress` base58-encoded 32 byte contract address with `ct_` prefix
- `OracleAddress` base58-encoded 32 byte oracle address with `ok_` prefix
- `OracleQueryId` base58-encoded 32 byte oracle query id with `oq_` prefix

Valid string escape codes are

| Escape        |       ASCII |   |
|---------------|-------------|---|
| `\b`          |           8 |   |
| `\t`          |           9 |   |
| `\n`          |          10 |   |
| `\v`          |          11 |   |
| `\f`          |          12 |   |
| `\r`          |          13 |   |
| `\e`          |          27 |   |
| `\xHexDigits` | *HexDigits* |   |


See the [identifier encoding scheme](https://github.com/aeternity/protocol/blob/master/node/api/api_encoding.md) for the
details on the base58 literals.

## Layout blocks

Sophia uses Python-style layout rules to group declarations and statements. A
layout block with more than one element must start on a separate line and be
indented more than the currently enclosing layout block. Blocks with a single
element can be written on the same line as the previous token.

Each element of the block must share the same indentation and no part of an
element may be indented less than the indentation of the block. For instance

```sophia
contract Layout =
  function foo() = 0  // no layout
  function bar() =    // layout block starts on next line
    let x = foo()     // indented more than 2 spaces
    x
     + 1              // the '+' is indented more than the 'x'
```

## Notation

In describing the syntax below, we use the following conventions:

- Upper-case identifiers denote non-terminals (like `Expr`) or terminals with
  some associated value (like `Id`).
- Keywords and symbols are enclosed in single quotes: `'let'` or `'='`.
- Choices are separated by vertical bars: `|`.
- Optional elements are enclosed in `[` square brackets `]`.
- `(` Parentheses `)` are used for grouping.
- Zero or more repetitions are denoted by a postfix `*`, and one or more
  repetitions by a `+`.
- `Block(X)` denotes a layout block of `X`s.
- `Sep(X, S)` is short for `[X (S X)*]`, i.e. a possibly empty sequence of `X`s
  separated by `S`s.
- `Sep1(X, S)` is short for `X (S X)*`, i.e. same as `Sep`, but must not be empty.


## Declarations

A Sophia file consists of a sequence of *declarations* in a layout block.

```c
File ::= Block(TopDecl)

TopDecl ::= ['payable'] ['main'] 'contract' Con [Implement] '=' Block(Decl)
          | 'contract' 'interface' Con [Implement] '=' Block(Decl)
          | 'namespace' Con '=' Block(Decl)
          | '@compiler' PragmaOp Version
          | 'include' String
          | Using

Implement ::= ':' Sep1(Con, ',')

Decl ::= 'type'     Id ['(' TVar* ')'] '=' TypeAlias
       | 'record'   Id ['(' TVar* ')'] '=' RecordType
       | 'datatype' Id ['(' TVar* ')'] '=' DataType
       | (EModifier* 'entrypoint' | FModifier* 'function') Block(FunDecl)
       | Using

FunDecl ::= Id ':' Type                             // Type signature
          | Id Args [':' Type] '=' Block(Stmt)      // Definition
          | Id Args [':' Type] Block(GuardedDef)    // Guarded definitions

GuardedDef ::= '|' Sep1(Expr, ',') '=' Block(Stmt)

Using ::= 'using' Con ['as' Con] [UsingParts]
UsingParts ::= 'for' '[' Sep1(Id, ',') ']'
             | 'hiding' '[' Sep1(Id, ',') ']'

PragmaOp ::= '<' | '=<' | '==' | '>=' | '>'
Version  ::= Sep1(Int, '.')

EModifier ::= 'payable' | 'stateful'
FModifier ::= 'stateful' | 'private'

Args ::= '(' Sep(Pattern, ',') ')'
```

Contract declarations must appear at the top-level.

For example,
```sophia
contract Test =
  type t = int
  entrypoint add (x : t, y : t) = x + y
```

There are three forms of type declarations: type aliases (declared with the
`type` keyword), record type definitions (`record`) and data type definitions
(`datatype`):

```c
TypeAlias  ::= Type
RecordType ::= '{' Sep(FieldType, ',') '}'
DataType   ::= Sep1(ConDecl, '|')

FieldType  ::= Id ':' Type
ConDecl    ::= Con ['(' Sep1(Type, ',') ')']
```

For example,
```sophia
record   point('a) = {x : 'a, y : 'a}
datatype shape('a) = Circle(point('a), 'a) | Rect(point('a), point('a))
type     int_shape = shape(int)
```

## Types

```c
Type ::= Domain '=>' Type             // Function type
       | Type '(' Sep(Type, ',') ')'  // Type application
       | '(' Type ')'                 // Parens
       | 'unit' | Sep(Type, '*')      // Tuples
       | Id | QId | TVar

Domain ::= Type                       // Single argument
         | '(' Sep(Type, ',') ')'     // Multiple arguments
```

The function type arrow associates to the right.

Example,
```sophia
'a => list('a) => (int * list('a))
```

## Statements

Function bodies are blocks of *statements*, where a statement is one of the following

```c
Stmt ::= 'switch' '(' Expr ')' Block(Case)
       | 'if' '(' Expr ')' Block(Stmt)
       | 'elif' '(' Expr ')' Block(Stmt)
       | 'else' Block(Stmt)
       | 'let' LetDef
       | Using
       | Expr

LetDef ::= Id Args [':' Type] '=' Block(Stmt)   // Function definition
         | Pattern '=' Block(Stmt)              // Value definition

Case    ::= Pattern '=>' Block(Stmt)
          | Pattern Block(GuardedCase)

GuardedCase ::= '|' Sep1(Expr, ',') '=>' Block(Stmt)

Pattern ::= Expr
```

`if` statements can be followed by zero or more `elif` statements and an optional final `else` statement. For example,

```sophia
let x : int = 4
switch(f(x))
  None => 0
  Some(y) =>
    if(y > 10)
      "too big"
    elif(y < 3)
      "too small"
    else
      "just right"
```

## Expressions

```c
Expr ::= '(' LamArgs ')' '=>' Block(Stmt)   // Anonymous function    (x) => x + 1
       | '(' BinOp ')'                      // Operator lambda       (+)
       | 'if' '(' Expr ')' Expr 'else' Expr // If expression         if(x < y) y else x
       | Expr ':' Type                      // Type annotation       5 : int
       | Expr BinOp Expr                    // Binary operator       x + y
       | UnOp Expr                          // Unary operator        ! b
       | Expr '(' Sep(Expr, ',') ')'        // Application           f(x, y)
       | Expr '.' Id                        // Projection            state.x
       | Expr '[' Expr ']'                  // Map lookup            map[key]
       | Expr '{' Sep(FieldUpdate, ',') '}' // Record or map update  r{ fld[key].x = y }
       | '[' Sep(Expr, ',') ']'             // List                  [1, 2, 3]
       | '[' Expr '|' Sep(Generator, ',') ']'
                                            // List comprehension    [k | x <- [1], if (f(x)), let k = x+1]
       | '[' Expr '..' Expr ']'             // List range            [1..n]
       | '{' Sep(FieldUpdate, ',') '}'      // Record or map value   {x = 0, y = 1}, {[key] = val}
       | '(' Expr ')'                       // Parens                (1 + 2) * 3
       | '(' Expr '=' Expr ')'              // Assign pattern        (y = x::_)
       | Id | Con | QId | QCon              // Identifiers           x, None, Map.member, AELib.Token
       | Int | Bytes | String | Char        // Literals              123, 0xff, #00abc123, "foo", '%'
       | AccountAddress | ContractAddress   // Chain identifiers
       | OracleAddress | OracleQueryId      // Chain identifiers
       | '???'                              // Hole expression       1 + ???

Generator ::= Pattern '<-' Expr   // Generator
            | 'if' '(' Expr ')'   // Guard
            | LetDef              // Definition

LamArgs ::= '(' Sep(LamArg, ',') ')'
LamArg  ::= Id [':' Type]

FieldUpdate ::= Path '=' Expr
Path ::= Id                 // Record field
       | '[' Expr ']'       // Map key
       | Path '.' Id        // Nested record field
       | Path '[' Expr ']'  // Nested map key

BinOp ::= '||' | '&&' | '<' | '>' | '=<' | '>=' | '==' | '!='
        | '::' | '++' | '+' | '-' | '*' | '/' | 'mod' | '^'
        | '|>'
UnOp  ::= '-' | '!'
```

## Operators types

| Operators | Type
| --- | ---
| `-` `+` `*` `/` `mod` `^` | arithmetic operators
| `!` `&&` `||` | logical operators
| `==` `!=` `<` `>` `=<` `>=` | comparison operators
| `::` `++` | list operators
| `|>` | functional operators

## Operator precedence

In order of highest to lowest precedence.

| Operators | Associativity
| --- | ---
| `!` | right
| `^` | left
| `*` `/` `mod` | left
| `-` (unary) | right
| `+` `-` | left
| `::` `++` | right
| `<` `>` `=<` `>=` `==` `!=` | none
| `&&` | right
| `||` | right
| `|>` | left
