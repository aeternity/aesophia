-module(aeso_abi_tests).

-include_lib("eunit/include/eunit.hrl").
-compile(export_all).

-define(SANDBOX(Code), sandbox(fun() -> Code end)).

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
    {ok, {error, circular_references}}   = ?SANDBOX(aeso_heap:from_binary({list, word}, CircularList)),
    {ok, {error, {binary_too_short, _}}} = ?SANDBOX(aeso_heap:from_binary(word, <<1, 2, 3, 4>>)),
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

encode_decode_sophia_test() ->
    Check = fun(Type, Str) -> case {encode_decode_sophia_string(Type, Str), Str} of
                                {X, X} -> ok;
                                Other -> Other
                              end end,
    ok = Check("int", "42"),
    ok = Check("bool", "true"),
    ok = Check("bool", "false"),
    ok = Check("string", "\"Hello\""),
    ok = Check("(string, list(int), option(bool))",
               "(\"Hello\", [1, 2, 3], Some(true))"),
    ok = Check("variant", "Blue({[\"x\"] = 1})"),
    ok = Check("r", "{x = (\"foo\", 0), y = Red}"),
    ok.

encode_decode_sophia_string(SophiaType, String) ->
    io:format("String ~p~n", [String]),
    Code = [ "contract MakeCall =\n"
           , "  type arg_type = ", SophiaType, "\n"
           , "  type an_alias('a) = (string, 'a)\n"
           , "  record r = {x : an_alias(int), y : variant}\n"
           , "  datatype variant = Red | Blue(map(string, int))\n"
           , "  function foo : arg_type => arg_type\n" ],
    case aeso_compiler:check_call(lists:flatten(Code), "foo", [String], []) of
        {ok, _, {[Type], _}, [Arg]} ->
            io:format("Type ~p~n", [Type]),
            Data = encode(Arg),
            case aeso_compiler:to_sophia_value(Code, "foo", ok, Data) of
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

encode_decode(T, D) ->
    ?assertEqual(D, decode(T, encode(D))),
    D.

encode(D) ->
    aeso_heap:to_binary(D).

decode(T,B) ->
    {ok, D} = aeso_heap:from_binary(T, B),
    D.
