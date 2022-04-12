-module(aeso_abi_tests).

-include_lib("eunit/include/eunit.hrl").
-compile([export_all, nowarn_export_all]).

-define(SANDBOX(Code), sandbox(fun() -> Code end)).
-define(DUMMY_HASH_WORD, 16#123).
-define(DUMMY_HASH_LIT, "#0000000000000000000000000000000000000000000000000000000000000123").

sandbox(Code) ->
    Parent = self(),
    Tag    = make_ref(),
    {Pid, Ref} = spawn_monitor(fun() -> Parent ! {Tag, Code()} end),
    receive
        {Tag1, Res} when Tag1 =:= Tag -> erlang:demonitor(Ref, [flush]), {ok, Res};
        {'DOWN', Ref1, process, Pid1, Reason} when Ref1 =:= Ref andalso Pid1 =:= Pid -> {error, Reason}
    after 100 ->
        exit(Pid, kill),
        {error, loop}
    end.

from_words(Ws) ->
    << <<(from_word(W))/binary>> || W <- Ws >>.

from_word(W) when is_integer(W) ->
    <<W:256>>;
from_word(S) when is_list(S) ->
    Len = length(S),
    Bin = <<(list_to_binary(S))/binary, 0:(32 - Len)/unit:8>>,
    <<Len:256, Bin/binary>>.

encode_decode_test() ->
    Tests =
        [42, 1, 0 -1, <<"Hello">>,
         {tuple, {}}, {tuple, {42}}, {tuple, {21, 37}},
         [], [42], [21, 37],
         {variant, [0, 1], 0, {}}, {variant, [0, 1], 1, {42}}, {variant, [2], 0, {21, 37}},
         {typerep, string}, {typerep, integer}, {typerep, {list, integer}}, {typerep, {tuple, [integer]}}
        ],
    [?assertEqual(Test, encode_decode(Test)) || Test <- Tests],
    ok.

encode_decode_sophia_test() ->
    Check = fun(Type, Str) -> case {encode_decode_sophia_string(Type, Str), Str} of
                                {X, X} -> ok;
                                Other -> Other
                              end end,
    ok = Check("int", "42"),
    ok = Check("int", "- 42"),
    ok = Check("bool", "true"),
    ok = Check("bool", "false"),
    ok = Check("string", "\"Hello\""),
    ok = Check("string * list(int) * option(bool)",
               "(\"Hello\", [1, 2, 3], Some(true))"),
    ok = Check("variant", "Blue({[\"x\"] = 1})"),
    ok = Check("r", "{x = (\"foo\", 0), y = Red}"),
    ok.

to_sophia_value_mcl_bls12_381_test() ->
    Code = "include \"BLS12_381.aes\"\n"
           "contract C =\n"
           "  entrypoint test_bls12_381_fp(x : int) = BLS12_381.int_to_fp(x)\n"
           "  entrypoint test_bls12_381_fr(x : int) = BLS12_381.int_to_fr(x)\n"
           "  entrypoint test_bls12_381_g1(x : int) = BLS12_381.mk_g1(x, x, x)\n",

    Opts = [{backend, fate}],

    CallValue32 = aeb_fate_encoding:serialize({bytes, <<20:256>>}),
    CallValue48 = aeb_fate_encoding:serialize({bytes, <<55:384>>}),
    CallValueTp = aeb_fate_encoding:serialize({tuple, {{bytes, <<15:256>>}, {bytes, <<160:256>>}, {bytes, <<1234:256>>}}}),

    {ok,     _} = aeso_compiler:to_sophia_value(Code, "test_bls12_381_fp", ok, CallValue32, Opts),
    {error,  _} = aeso_compiler:to_sophia_value(Code, "test_bls12_381_fp", ok, CallValue48, Opts),
    {ok,     _} = aeso_compiler:to_sophia_value(Code, "test_bls12_381_fr", ok, CallValue48, Opts),
    {error,  _} = aeso_compiler:to_sophia_value(Code, "test_bls12_381_fr", ok, CallValue32, Opts),
    {ok,     _} = aeso_compiler:to_sophia_value(Code, "test_bls12_381_g1", ok, CallValueTp, Opts),

    ok.

to_sophia_value_neg_test() ->
    Code = [ "contract Foo =\n"
             "  entrypoint f(x : int) : string = \"hello\"\n" ],

    {error, [Err1]} = aeso_compiler:to_sophia_value(Code, "f", ok, encode(12)),
    ?assertEqual("Data error:\nCannot translate FATE value 12\n  of Sophia type string\n", aeso_errors:pp(Err1)),

    {error, [Err2]} = aeso_compiler:to_sophia_value(Code, "f", revert, encode(12)),
    ?assertEqual("Data error:\nCould not deserialize the revert message\n", aeso_errors:pp(Err2)),
    ok.

encode_calldata_neg_test() ->
    Code = [ "contract Foo =\n"
             "  entrypoint f(x : int) : string = \"hello\"\n" ],

    ExpErr1 = "Type error at line 5, col 34:\nCannot unify `int` and `bool`\n"
              "when checking the application of\n"
              "  `f : (int) => string`\n"
              "to arguments\n"
              "  `true : bool`\n",
    {error, [Err1]} = aeso_compiler:create_calldata(Code, "f", ["true"]),
    ?assertEqual(ExpErr1, aeso_errors:pp(Err1)),

    ok.

decode_calldata_neg_test() ->
    Code1 = [ "contract Foo =\n"
              "  entrypoint f(x : int) : string = \"hello\"\n" ],
    Code2 = [ "contract Foo =\n"
              "  entrypoint f(x : string) : int = 42\n" ],

    {ok, CallDataFATE} = aeso_compiler:create_calldata(Code1, "f", ["42"]),

    {error, [Err1]} = aeso_compiler:decode_calldata(Code2, "f", <<1,2,3>>),
    ?assertEqual("Data error:\nFailed to decode calldata binary\n", aeso_errors:pp(Err1)),
    {error, [Err2]} = aeso_compiler:decode_calldata(Code2, "f", CallDataFATE),
    ?assertEqual("Data error:\nCannot translate FATE value \"*\"\n  to Sophia type (string)\n", aeso_errors:pp(Err2)),

    {error, [Err3]} = aeso_compiler:decode_calldata(Code2, "x", CallDataFATE),
    ?assertEqual("Data error at line 1, col 1:\nFunction 'x' is missing in contract\n", aeso_errors:pp(Err3)),
    ok.


encode_decode_sophia_string(SophiaType, String) ->
    io:format("String ~p~n", [String]),
    Code = [ "contract MakeCall =\n"
           , "  type arg_type = ", SophiaType, "\n"
           , "  type an_alias('a) = string * 'a\n"
           , "  record r = {x : an_alias(int), y : variant}\n"
           , "  datatype variant = Red | Blue(map(string, int))\n"
           , "  entrypoint foo : arg_type => arg_type\n" ],
    case aeso_compiler:check_call(lists:flatten(Code), "foo", [String], [no_code]) of
        {ok, _, [Arg]} ->
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

calldata_test() ->
    [42, <<"foobar">>] = encode_decode_calldata("foo", ["int", "string"], ["42", "\"foobar\""]),
    [{variant, [0,1], 1, {#{ <<"a">> := 4 }}}, {tuple, {{tuple, {<<"b">>, 5}}, {variant, [0,1], 0, {}}}}] =
        encode_decode_calldata("foo", ["variant", "r"], ["Blue({[\"a\"] = 4})", "{x = (\"b\", 5), y = Red}"]),
    [{bytes, <<291:256>>}, {address, <<1110:256>>}] =
        encode_decode_calldata("foo", ["bytes(32)", "address"],
                               [?DUMMY_HASH_LIT, "ak_1111111111111111111111111111113AFEFpt5"]),
    [{bytes, <<291:256>>}, {bytes, <<291:256>>}] =
        encode_decode_calldata("foo", ["bytes(32)", "hash"], [?DUMMY_HASH_LIT, ?DUMMY_HASH_LIT]),

    [119, {bytes, <<0:64/unit:8>>}] = encode_decode_calldata("foo", ["int", "signature"], ["119", [$# | lists:duplicate(128, $0)]]),

    [{contract, <<1110:256>>}] = encode_decode_calldata("foo", ["Remote"], ["ct_1111111111111111111111111111113AFEFpt5"]),

    ok.

calldata_init_test() ->
    encode_decode_calldata("init", ["int"], ["42"]),

    Code = parameterized_contract("foo", ["int"]),
    encode_decode_calldata_(Code, "init", []),

    ok.

calldata_indent_test() ->
    Test = fun(Extra) ->
            Code = parameterized_contract(Extra, "foo", ["int"]),
            encode_decode_calldata_(Code, "foo", ["42"])
           end,
    Test("  stateful entrypoint bla() = ()"),
    Test("  type x = int"),
    Test("  stateful entrypoint bla(x : int) =\n"
         "    x + 1"),
    Test("  stateful entrypoint bla(x : int) : int =\n"
         "    x + 1"),
    ok.

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

oracle_test() ->
    Contract =
        "contract OracleTest =\n"
        "  entrypoint question(o, q : oracle_query(list(string), option(int))) =\n"
        "    Oracle.get_question(o, q)\n",
    ?assertEqual({ok, "question", [{oracle, <<291:256>>}, {oracle_query, <<1110:256>>}]},
                 aeso_compiler:check_call(Contract, "question", ["ok_111111111111111111111111111111ZrdqRz9",
                                                                 "oq_1111111111111111111111111111113AFEFpt5"], [no_code])),

    ok.

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
    Code = parameterized_contract(FunName, Types),
    encode_decode_calldata_(Code, FunName, Args).

encode_decode_calldata_(Code, FunName, Args) ->
    {ok, Calldata} = aeso_compiler:create_calldata(Code, FunName, Args, []),
    {ok, _, _} = aeso_compiler:check_call(Code, FunName, Args, [no_code]),
    case FunName of
        "init" ->
            [];
        _ ->
            {ok, FateArgs} = aeb_fate_abi:decode_calldata(FunName, Calldata),
            FateArgs
    end.

encode_decode(D) ->
    ?assertEqual(D, decode(encode(D))),
    D.

encode(D) ->
    aeb_fate_encoding:serialize(D).

decode(B) ->
    aeb_fate_encoding:deserialize(B).
