-module(aeso_encode_decode_tests).

-compile([export_all, nowarn_export_all]).

-include_lib("eunit/include/eunit.hrl").

-define(EMPTY, "contract C =\n  entrypoint f() = true").

encode_decode_test_() ->
    [ {lists:flatten(io_lib:format("Testing encode-decode roundtrip for ~p : ~p", [Value, {EType, DType}])),
       fun() ->
           {ok, SerRes} = aeso_compiler:encode_value(?EMPTY, EType, Value, []),
           {ok, Expr} = aeso_compiler:decode_value(?EMPTY, DType, SerRes, []),
           Value2 = prettypr:format(aeso_pretty:expr(Expr)),
           ?assertEqual(Value, Value2)
       end} || {Value, EType, DType} <- test_data() ].

test_data() ->
    lists:map(fun({V, T}) -> {V, T, T};
                 ({V, T1, T2}) -> {V, T1, T2} end, data()).

data() ->
    [ {"42", "int"}
    , {"- 42", "int"}
    , {"true", "bool"}
    , {"ak_Ez6MyeTMm17YnTnDdHTSrzMEBKmy7Uz2sXu347bTDPgVH2ifJ", "address"}
    , {"ct_Ez6MyeTMm17YnTnDdHTSrzMEBKmy7Uz2sXu347bTDPgVH2ifJ", "C"}
    , {"Some(42)", "option(int)"}
    , {"None", "option(int)"}
    , {"(true, 42)", "bool * int"}
    , {"{[1] = true, [3] = false}", "map(int, bool)"}
    , {"()", "unit"}
    , {"#000102030405060708090a0b0c0d0e0f000102030405060708090a0b0c0d0e0f", "hash"}
    , {"#000102030405060708090a0b0c0d0e0f000102030405060708090a0b0c0d0e0f", "bytes(32)"}
    , {"sg_MhibzTP1wWzGCTjtPFr1TiPqRJrrJqw7auvEuF5i3FdoALWqXLBDY6xxRRNUSPHK3EQTnTzF12EyspkxrSMxVHKsZeSMj", "signature"}
    , {"sg_MhibzTP1wWzGCTjtPFr1TiPqRJrrJqw7auvEuF5i3FdoALWqXLBDY6xxRRNUSPHK3EQTnTzF12EyspkxrSMxVHKsZeSMj", "bytes(64)", "signature"}
    , {"#0102030405060708090a0b0c0d0e0f101718192021222324252627282930313233343536373839401a1b1c1d1e1f202122232425262728293031323334353637", "bytes(64)"}
    , {"#0102030405060708090a0b0c0d0e0f101718192021222324252627282930313233343536373839401a1b1c1d1e1f202122232425262728293031323334353637", "signature", "bytes(64)"}
    ].

