-module(aeso_abi_tests).

-include_lib("eunit/include/eunit.hrl").
-compile([export_all, nowarn_export_all]).

-define(SANDBOX(Code), sandbox(fun() -> Code end)).
-define(DUMMY_HASH_WORD, 16#123).
-define(DUMMY_HASH, <<0:30/unit:8, 127, 119>>). %% 16#123
-define(DUMMY_HASH_LIT, "#0000000000000000000000000000000000000000000000000000000000000123").

sandbox(Code) ->
    Parent = self(),
    Tag    = make_ref(),
    {Pid, Ref} = spawn_monitor(fun() -> Parent ! {Tag, Code()} end),
    receive
        {Tag, Res} -> erlang:demonitor(Ref, [flush]), {ok, Res};
        {'DOWN', Ref, process, Pid, Reason} -> {error, Reason}
    after 100 ->
        exit(Pid, kill),
        {error, loop}
    end.

malicious_from_binary_test() ->
    CircularList = from_words([32, 1, 32]), %% Xs = 1 :: Xs
    {ok, {error, circular_references}}   = ?SANDBOX(aeb_heap:from_binary({list, word}, CircularList)),
    {ok, {error, {binary_too_short, _}}} = ?SANDBOX(aeb_heap:from_binary(word, <<1, 2, 3, 4>>)),
    ok.

from_words(Ws) ->
    << <<(from_word(W))/binary>> || W <- Ws >>.

from_word(W) when is_integer(W) ->
    <<W:256>>;
from_word(S) when is_list(S) ->
    Len = length(S),
    Bin = <<(list_to_binary(S))/binary, 0:(32 - Len)/unit:8>>,
    <<Len:256, Bin/binary>>.

encode_decode_test() ->
    encode_decode(word, 42),
    42 = encode_decode(word, 42),
    -1 = encode_decode(signed_word, -1),
    <<"Hello world">> = encode_decode(string, <<"Hello world">>),
    {} = encode_decode({tuple, []}, {}),
    {42} = encode_decode({tuple, [word]}, {42}),
    {42, 0} = encode_decode({tuple, [word, word]}, {42, 0}),
    [] = encode_decode({list, word}, []),
    [32] = encode_decode({list, word}, [32]),
    none = encode_decode({option, word}, none),
    {some, 1} = encode_decode({option, word}, {some, 1}),
    string = encode_decode(typerep, string),
    word = encode_decode(typerep, word),
    {list, word} = encode_decode(typerep, {list, word}),
    {tuple, [word]} = encode_decode(typerep, {tuple, [word]}),
    1 = encode_decode(word, 1),
    0 = encode_decode(word, 0),
    ok.

encode_decode_sophia_test() -> ok.
%encode_decode_sophia_test() ->
%    Check = fun(Type, Str) -> case {encode_decode_sophia_string(Type, Str), Str} of
%                                {X, X} -> ok;
%                                Other -> Other
%                              end end,
%    ok = Check("int", "42"),
%    ok = Check("int", "- 42"),
%    ok = Check("bool", "true"),
%    ok = Check("bool", "false"),
%    ok = Check("string", "\"Hello\""),
%    ok = Check("string * list(int) * option(bool)",
%               "(\"Hello\", [1, 2, 3], Some(true))"),
%    ok = Check("variant", "Blue({[\"x\"] = 1})"),
%    ok = Check("r", "{x = (\"foo\", 0), y = Red}"),
%    ok.
%
%to_sophia_value_neg_test() ->
%    Code = [ "contract Foo =\n"
%             "  entrypoint x(y : int) : string = \"hello\"\n" ],
%
%    {error, [Err1]} = aeso_compiler:to_sophia_value(Code, "x", ok, encode(12)),
%    ?assertEqual("Data error:\nFailed to decode binary as type string\n", aeso_errors:pp(Err1)),
%    {error, [Err2]} = aeso_compiler:to_sophia_value(Code, "x", ok, encode(12), [{backend, fate}]),
%    ?assertEqual("Data error:\nFailed to decode binary as type string\n", aeso_errors:pp(Err2)),
%
%    {error, [Err3]} = aeso_compiler:to_sophia_value(Code, "x", revert, encode(12)),
%    ?assertEqual("Data error:\nCould not interpret the revert message\n", aeso_errors:pp(Err3)),
%    {error, [Err4]} = aeso_compiler:to_sophia_value(Code, "x", revert, encode(12), [{backend, fate}]),
%    ?assertEqual("Data error:\nCould not deserialize the revert message\n", aeso_errors:pp(Err4)),
%    ok.

encode_calldata_neg_test() ->
    Code = [ "contract Foo =\n"
             "  entrypoint x(y : int) : string = \"hello\"\n" ],

    ExpErr1 = "Type error at line 5, col 34:\nCannot unify int\n         and bool\n"
              "when checking the application at line 5, column 34 of\n"
              "  x : (int) => string\nto arguments\n  true : bool\n",
    {error, [Err1]} = aeso_compiler:create_calldata(Code, "x", ["true"]),
    ?assertEqual(ExpErr1, aeso_errors:pp(Err1)),
    {error, [Err2]} = aeso_compiler:create_calldata(Code, "x", ["true"], [{backend, fate}]),
    ?assertEqual(ExpErr1, aeso_errors:pp(Err2)),

    ok.

decode_calldata_neg_test() -> ok.
%decode_calldata_neg_test() ->
%    Code1 = [ "contract Foo =\n"
%              "  entrypoint x(y : int) : string = \"hello\"\n" ],
%    Code2 = [ "contract Foo =\n"
%              "  entrypoint x(y : string) : int = 42\n" ],
%
%    {ok, CallDataAEVM} = aeso_compiler:create_calldata(Code1, "x", ["42"]),
%    {ok, CallDataFATE} = aeso_compiler:create_calldata(Code1, "x", ["42"], [{backend, fate}]),
%
%    {error, [Err1]} = aeso_compiler:decode_calldata(Code2, "x", CallDataAEVM),
%    ?assertEqual("Data error:\nFailed to decode calldata as type {tuple,[string]}\n", aeso_errors:pp(Err1)),
%    {error, [Err2]} = aeso_compiler:decode_calldata(Code2, "x", <<1,2,3>>, [{backend, fate}]),
%    ?assertEqual("Data error:\nFailed to decode calldata binary\n", aeso_errors:pp(Err2)),
%    {error, [Err3]} = aeso_compiler:decode_calldata(Code2, "x", CallDataFATE, [{backend, fate}]),
%    ?assertEqual("Data error:\nCannot translate FATE value \"*\"\n  to Sophia type (string)\n", aeso_errors:pp(Err3)),
%
%    {error, [Err4]} = aeso_compiler:decode_calldata(Code2, "y", CallDataAEVM),
%    ?assertEqual("Data error at line 1, col 1:\nFunction 'y' is missing in contract\n", aeso_errors:pp(Err4)),
%    {error, [Err5]} = aeso_compiler:decode_calldata(Code2, "y", CallDataFATE, [{backend, fate}]),
%    ?assertEqual("Data error at line 1, col 1:\nFunction 'y' is missing in contract\n", aeso_errors:pp(Err5)),
%    ok.


encode_decode_sophia_string(SophiaType, String) ->
    io:format("String ~p~n", [String]),
    Code = [ "contract MakeCall =\n"
           , "  type arg_type = ", SophiaType, "\n"
           , "  type an_alias('a) = string * 'a\n"
           , "  record r = {x : an_alias(int), y : variant}\n"
           , "  datatype variant = Red | Blue(map(string, int))\n"
           , "  entrypoint foo : arg_type => arg_type\n" ],
    case aeso_compiler:check_call(lists:flatten(Code), "foo", [String], [no_code]) of
        {ok, _, {[Type], _}, [Arg]} ->
            io:format("Type ~p~n", [Type]),
            Data = encode(Arg),
            case aeso_compiler:to_sophia_value(Code, "foo", ok, Data, [no_code]) of
                {ok, Sophia} ->
                    lists:flatten(io_lib:format("~s", [prettypr:format(aeso_pretty:expr(Sophia))]));
                {error, Err} ->
                    io:format("~s\n", [Err]),
                    {error, Err}
            end;
        {error, Err} ->
            io:format("~s\n", [Err]),
            {error, Err}
    end.

calldata_test() -> ok.
%calldata_test() ->
%    [42, <<"foobar">>] = encode_decode_calldata("foo", ["int", "string"], ["42", "\"foobar\""]),
%    Map = #{ <<"a">> => 4 },
%    [{variant, 1, [Map]}, {{<<"b">>, 5}, {variant, 0, []}}] =
%        encode_decode_calldata("foo", ["variant", "r"], ["Blue({[\"a\"] = 4})", "{x = (\"b\", 5), y = Red}"]),
%    [?DUMMY_HASH_WORD, 16#456] = encode_decode_calldata("foo", ["bytes(32)", "address"],
%                                                        [?DUMMY_HASH_LIT, "ak_1111111111111111111111111111113AFEFpt5"]),
%    [?DUMMY_HASH_WORD, ?DUMMY_HASH_WORD] =
%        encode_decode_calldata("foo", ["bytes(32)", "hash"], [?DUMMY_HASH_LIT, ?DUMMY_HASH_LIT]),
%
%    [119, {0, 0}] = encode_decode_calldata("foo", ["int", "signature"], ["119", [$# | lists:duplicate(128, $0)]]),
%
%    [16#456] = encode_decode_calldata("foo", ["Remote"], ["ct_1111111111111111111111111111113AFEFpt5"]),
%
%    ok.

calldata_init_test() -> ok.
%calldata_init_test() ->
%    encode_decode_calldata("init", ["int"], ["42"], {tuple, [typerep, word]}),
%
%    Code = parameterized_contract("foo", ["int"]),
%    encode_decode_calldata_(Code, "init", [], {tuple, [typerep, {tuple, []}]}).

calldata_indent_test() -> ok.
%calldata_indent_test() ->
%    Test = fun(Extra) ->
%            Code = parameterized_contract(Extra, "foo", ["int"]),
%            encode_decode_calldata_(Code, "foo", ["42"], word)
%           end,
%    Test("  stateful entrypoint bla() = ()"),
%    Test("  type x = int"),
%    Test("  stateful entrypoint bla(x : int) =\n"
%         "    x + 1"),
%    Test("  stateful entrypoint bla(x : int) : int =\n"
%         "    x + 1"),
%    ok.

parameterized_contract(FunName, Types) ->
    parameterized_contract([], FunName, Types).

parameterized_contract(ExtraCode, FunName, Types) ->
    lists:flatten(
        ["contract Remote =\n"
         "  entrypoint bla : () => unit\n\n"
         "main contract Dummy =\n",
         ExtraCode, "\n",
         "  type an_alias('a) = string * 'a\n"
         "  record r = {x : an_alias(int), y : variant}\n"
         "  datatype variant = Red | Blue(map(string, int))\n"
         "  entrypoint ", FunName, " : (", string:join(Types, ", "), ") => int\n" ]).

oracle_test() -> ok.
%oracle_test() ->
%    Contract =
%        "contract OracleTest =\n"
%        "  entrypoint question(o, q : oracle_query(list(string), option(int))) =\n"
%        "    Oracle.get_question(o, q)\n",
%    {ok, _, {[word, word], {list, string}}, [16#123, 16#456]} =
%        aeso_compiler:check_call(Contract, "question", ["ok_111111111111111111111111111111ZrdqRz9",
%                                                        "oq_1111111111111111111111111111113AFEFpt5"], [no_code]),
%
%    ok.

permissive_literals_fail_test() ->
    Contract =
        "contract OracleTest =\n"
        "  stateful entrypoint haxx(o : oracle(list(string), option(int))) =\n"
        "    Chain.spend(o, 1000000)\n",
    {error, [Err]} =
        aeso_compiler:check_call(Contract, "haxx", ["#123"], []),
    ?assertMatch("Type error at line 3, col 5:\nCannot unify" ++ _, aeso_errors:pp(Err)),
    ?assertEqual(type_error, aeso_errors:type(Err)),
    ok.

encode_decode_calldata(FunName, Types, Args) ->
    encode_decode_calldata(FunName, Types, Args, word).

encode_decode_calldata(FunName, Types, Args, RetType) ->
    Code = parameterized_contract(FunName, Types),
    encode_decode_calldata_(Code, FunName, Args, RetType).

encode_decode_calldata_(Code, FunName, Args, RetVMType) ->
    {ok, Calldata} = aeso_compiler:create_calldata(Code, FunName, Args, []),
    {ok, _, {ArgTypes, RetType}, _} = aeso_compiler:check_call(Code, FunName, Args, [{backend, aevm}, no_code]),
    ?assertEqual(RetType, RetVMType),
    CalldataType = {tuple, [word, {tuple, ArgTypes}]},
    {ok, {_Hash, ArgTuple}} = aeb_heap:from_binary(CalldataType, Calldata),
    case FunName of
        "init" ->
            ok;
        _ ->
            {ok, _ArgTypes, ValueASTs} = aeso_compiler:decode_calldata(Code, FunName, Calldata, []),
            Values = [ prettypr:format(aeso_pretty:expr(V)) || V <- ValueASTs ],
            ?assertMatch({X, X}, {Args, Values})
    end,
    tuple_to_list(ArgTuple).

encode_decode(T, D) ->
    ?assertEqual(D, decode(T, encode(D))),
    D.

encode(D) ->
    aeb_heap:to_binary(D).

decode(T,B) ->
    {ok, D} = aeb_heap:from_binary(T, B),
    D.
