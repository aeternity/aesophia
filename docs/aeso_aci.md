# aeso_aci

### Module

### aeso_aci

The ACI interface encoder and decoder.

### Description

This module provides an interface to generate and convert between
Sophia contracts and a suitable JSON encoding of contract
interface. As yet the interface is very basic.

Encoding this contract:

```
contract Answers =
  record state = { a : answers }
  type answers() = map(string, int)

  stateful function init() = { a = {} }
  private function the_answer() = 42
  function new_answer(q : string, a : int) : answers() = { [q] = a }
```

generates the following JSON structure representing the contract interface:


``` json
{
  "contract": {
    "name": "Answers",
    "type_defs": [
      {
        "name": "state",
        "vars": [],
        "typedef": {
          "record": [
            {
              "name": "a",
              "type": {
                "map": {
                  "key": "string",
                  "value": "int"
                }
              }
            }
          ]
        }
      },
      {
        "name": "answers",
        "vars": [],
        "typedef": {
          "map": {
            "key": "string",
            "value": "int"
          }
        }
      }
    ],
    "functions": [
      {
        "name": "init",
        "arguments": [],
        "returns": {
          "record": [
            {
              "name": "a",
              "type": {
                "map": {
                  "key": "string",
                  "value": "int"
                }
              }
            }
          ]
        },
        "stateful": true
      },
      {
        "name": "new_answer",
        "arguments": [
          {
            "name": "q",
            "type": [
              "string"
            ]
          },
          {
            "name": "a",
            "type": [
              "int"
            ]
          }
        ],
        "returns": {
          "map": {
            "key": "string",
            "value": "int"
          }
        },
        "stateful": false
      }
    ]
  }
}
```

When that encoding is decoded the following include definition is generated:

```
contract Answers =
  function new_answer : (string, int) => map(string, int)
```

### Types
``` erlang
contract_string() = string() | binary()
json_string() = binary()
```

### Exports

#### encode_contract(ContractString) -> {ok,JSONstring} | {error,ErrorString}

Types

``` erlang
ConstractString = contract_string()
JSONstring = json_string()
```

Generate the JSON encoding of the interface to a contract. The type definitions and non-private functions are included in the JSON string.

#### decode_contract(JSONstring) -> ConstractString.

Types

``` erlang
ConstractString = contract_string()
JSONstring = json_string()
```

Take a JSON encoding of a contract interface and generate and generate a contract definition which can be included in another contract.

#### encode_type(TypeAST) -> JSONstring.

Types

``` erlang
JSONstring = json_string()
```

Generate the JSON encoding of a type from the AST of the type.

#### encode_arg(ArgAST) -> JSONstring.

Types

``` erlang
JSONstring = json_string()
```

Generate the JSON encoding of a function argument from the AST of the argument.

#### encode_stmt(StmtAST) -> JSONstring.

Types

``` erlang
JSONstring = json_string()
```

Generate the JSON encoding of a statement from the AST of the statement.

#### encode_expr(ExprAST) -> JSONstring.

Types

``` erlang
JSONstring = json_string()
```

Generate the JSON encoding of an expression from the AST of the expression.

### Example run

This is an example of using the ACI generator from an Erlang shell. The file called `aci_test.aes` contains the contract in the description from which we want to generate files `aci_test.json` which is the JSON encoding of the contract interface and `aci_test.include` which is the contract definition to be included inside another contract.

``` erlang
1> {ok,Contract} = file:read_file("aci_test.aes").
{ok,<<"contract Answers =\n  record state = { a : answers }\n  type answers() = map(string, int)\n\n  stateful function"...>>}
2> {ok,Encoding} = aeso_aci:encode_contract(Contract).
<<"{\"contract\":{\"name\":\"Answers\",\"type_defs\":[{\"name\":\"state\",\"vars\":[],\"typedef\":\"{a : map(string,int)}\"},{\"name\":\"ans"...>>
3> file:write_file("aci_test.aci", Encoding).
ok
4> Decoded = aeso_aci:decode_contract(Encoding).
<<"contract Answers =\n  function new_answer : (string, int) => map(string, int)\n">>
5> file:write_file("aci_test.include", Decoded).
ok
6> jsx:prettify(Encoding).
<<"{\n  \"contract\": {\n    \"name\": \"Answers\",\n    \"type_defs\": [\n      {\n        \"name\": \"state\",\n        \"vars\": [],\n   "...>>
```

The final call to `jsx:prettify(Encoding)` returns the encoding in a
more easily readable form. This is what is shown in the description
above.

### Notes

The ACI generator currently cannot properly handle types defined using `datatype`.
