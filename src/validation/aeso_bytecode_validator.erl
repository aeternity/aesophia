%%%-------------------------------------------------------------------
%%% Byte code validation split from aeso_compiler
%%%-------------------------------------------------------------------
-module(aeso_bytecode_validator).

-export([ validate_byte_code/3 ]).

%% No macro indirection; write explicit try/catch to avoid unsafe-in-try warnings

%% @doc Validate that `ByteCode` matches the given `Source` by recompiling the
%%      source and comparing the produced FATE code and payable flag.
validate_byte_code(#{ byte_code := ByteCode, payable := Payable }, Source, Options) ->
    Fail = fun(Err) -> {error, [aeso_errors:new(data_error, Err)]} end,
    %% Deserialize provided bytecode
    case (fun() ->
              try
                  F = aeb_fate_code:deserialize(ByteCode),
                  {ok, aeb_fate_code:strip_init_function(F)}
              catch _: _ -> {error, invalid_bytecode}
              end
          end)() of
        {error, invalid_bytecode} ->
            Fail("Invalid byte code");
        {ok, FCode1} ->
            %% Recompile source
            case erlang:apply(aeso_compiler, from_string, [Source, Options]) of
                {error, Errs} -> {error, Errs};
                {ok, Map} ->
                    SrcByteCode = maps:get(byte_code, Map),
                    SrcPayable  = maps:get(payable, Map),
                    F2 = aeb_fate_code:deserialize(SrcByteCode),
                    FCode2 = aeb_fate_code:strip_init_function(F2),
                    case aeso_fate_compare:compare(FCode1, FCode2) of
                        ok when SrcPayable /= Payable ->
                            Not = fun(true) -> ""; (false) -> " not" end,
                            Fail(io_lib:format("Byte code contract is~s payable, but source code contract is~s.\n",
                                               [Not(Payable), Not(SrcPayable)]));
                        ok           -> ok;
                        {error, Why} -> Fail(io_lib:format("Byte code does not match source code.\n~s", [Why]))
                    end
            end
    end.

%% comparison moved to aeso_fate_compare


