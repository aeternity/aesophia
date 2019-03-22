-module(exp_aeso_aci_tests).

-include_lib("eunit/include/eunit.hrl").


do_test() ->
    test_contract(1),
    test_contract(2).

test_contract(N) ->
    {Contract,DecACI} = test_cases(N),
    {ok,Enc} = exp_aeso_aci:encode(Contract),
    ?assertEqual(DecACI, jsx:decode(Enc)).

test_cases(1) ->
    Contract = <<"contract C =\n"
		 "  function a(i : int) = i+1\n">>,
    DecodedACI = [{<<"contract">>,
		   [{<<"name">>,<<"C">>},
		    {<<"type_defs">>,[]},
		    {<<"functions">>,
		     [[{<<"name">>,<<"a">>},
		       {<<"arguments">>,
			[[{<<"name">>,<<"i">>},{<<"type">>,[<<"int">>]}]]},
		       {<<"returns">>,<<"int">>},
		       {<<"stateful">>,false}]]}]}],
    {Contract,DecodedACI};

test_cases(2) ->
    Contract = <<"contract C =\n"
		 "  type allan = int\n"
		 "  function a(i : allan) = i+1\n">>,
    DecodedACI = [{<<"contract">>,
		   [{<<"name">>,<<"C">>},
		    {<<"type_defs">>,
		     [[{<<"name">>,<<"allan">>},
		       {<<"vars">>,[]},
		       {<<"typedef">>,<<"int">>}]]},
		    {<<"functions">>,
		     [[{<<"name">>,<<"a">>},
		       {<<"arguments">>,
			[[{<<"name">>,<<"i">>},{<<"type">>,[<<"int">>]}]]},
		       {<<"returns">>,<<"int">>},
		       {<<"stateful">>,false}]]}]}],
    {Contract,DecodedACI}.
