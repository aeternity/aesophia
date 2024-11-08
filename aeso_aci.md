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
    "functions": [
      {
        "arguments": [],
        "name": "init",
        "returns": "Answers.state",
        "stateful": true
      },
      {
        "arguments": [
          {
            "name": "q",
            "type": "string"
          },
          {
            "name": "a",
            "type": "int"
          }
        ],
        "name": "new_answer",
        "returns": {
          "map": [
            "string",
            "int"
          ]
        },
        "stateful": false
      }
    ],
    "name": "Answers",
    "state": {
      "record": [
        {
          "name": "a",
          "type": "Answers.answers"
        }
      ]
    },
    "type_defs": [
      {
        "name": "answers",
        "typedef": {
          "map": [
            "string",
            "int"
          ]
        },
        "vars": []
      }
    ]
  }
}
```

When that encoding is decoded the following include definition is generated:

```
contract Answers =
  record state = {a : Answers.answers}
  type answers = map(string, int)
  function init : () => Answers.state
  function new_answer : (string, int) => map(string, int)
```

### Types
```erlang
-type aci_type()  :: json | string.
-type json()      :: jsx:json_term().
-type json_text() :: binary().
```

### Exports

#### contract\_interface(aci\_type(), string()) -> {ok, json() | string()} | {error, term()}

Generate the JSON encoding of the interface to a contract. The type definitions
and non-private functions are included in the JSON string.

#### render\_aci\_json(json() | json\_text()) -> string().

Take a JSON encoding of a contract interface and generate a contract interface
that can be included in another contract.

### Example run

This is an example of using the ACI generator from an Erlang shell. The file
called `aci_test.aes` contains the contract in the description from which we
want to generate files `aci_test.json` which is the JSON encoding of the
contract interface and `aci_test.include` which is the contract definition to
be included inside another contract.

``` erlang
1> {ok,Contract} = file:read_file("aci_test.aes").
{ok,<<"contract Answers =\n  record state = { a : answers }\n  type answers() = map(string, int)\n\n  stateful function"...>>}
2> {ok,JsonACI} = aeso_aci:contract_interface(json, Contract).
{ok,[#{contract =>
           #{functions =>
                 [#{arguments => [],name => <<"init">>,
                    returns => <<"Answers.state">>,stateful => true},
                  #{arguments =>
                        [#{name => <<"q">>,type => <<"string">>},
                         #{name => <<"a">>,type => <<"int">>}],
                    name => <<"new_answer">>,
                    returns => #{<<"map">> => [<<"string">>,<<"int">>]},
                    stateful => false}],
             name => <<"Answers">>,
             state =>
                 #{record =>
                       [#{name => <<"a">>,type => <<"Answers.answers">>}]},
             type_defs =>
                 [#{name => <<"answers">>,
                    typedef => #{<<"map">> => [<<"string">>,<<"int">>]},
                    vars => []}]}}]}
3> file:write_file("aci_test.aci", jsx:encode(JsonACI)).
ok
4> {ok,InterfaceStub} = aeso_aci:render_aci_json(JsonACI).
{ok,<<"contract Answers =\n  record state = {a : Answers.answers}\n  type answers = map(string, int)\n  function init "...>>}
5> file:write_file("aci_test.include", InterfaceStub).
ok
6> jsx:prettify(jsx:encode(JsonACI)).
<<"[\n  {\n    \"contract\": {\n      \"functions\": [\n        {\n          \"arguments\": [],\n          \"name\": \"init\",\n        "...>>
```

The final call to `jsx:prettify(jsx:encode(JsonACI))` returns the encoding in a
more easily readable form. This is what is shown in the description above.
