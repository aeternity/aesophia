-module(aeso_aci_tests).

-include_lib("eunit/include/eunit.hrl").


do_test() ->
    test_contract(1),
    test_contract(2),
    test_contract(3).

test_contract(N) ->
    {Contract,MapACI,DecACI} = test_cases(N),
    {ok,JSON} = aeso_aci:encode(Contract),
    ?assertEqual(MapACI, jsx:decode(JSON, [return_maps])),
    ?assertEqual(DecACI, aeso_aci:decode(JSON)).

test_cases(1) ->
    Contract = <<"contract C =\n"
		 "  function a(i : int) = i+1\n">>,
    MapACI = #{<<"contract">> =>
		   #{<<"name">> => <<"C">>,
		     <<"type_defs">> => [],
		     <<"functions">> =>
			 [#{<<"name">> => <<"a">>,
			    <<"arguments">> => 
				[#{<<"name">> => <<"i">>,
				   <<"type">> => <<"int">>}],
			    <<"returns">> => <<"int">>,
			    <<"stateful">> => false}]}},
    DecACI = <<"contract C =\n"
	       "  function a : (int) => int\n">>,
    {Contract,MapACI,DecACI};

test_cases(2) ->
    Contract = <<"contract C =\n"
		 "  type allan = int\n"
		 "  function a(i : allan) = i+1\n">>,
    MapACI = #{<<"contract">> =>
                       #{<<"name">> => <<"C">>,
                         <<"type_defs">> =>
                             [#{<<"name">> => <<"allan">>,
                                <<"typedef">> => <<"int">>,
                                <<"vars">> => []}],
			 <<"functions">> =>
                             [#{<<"arguments">> =>
                                    [#{<<"name">> => <<"i">>,
                                       <<"type">> => <<"int">>}],
                                <<"name">> => <<"a">>,
                                <<"returns">> => <<"int">>,
                                <<"stateful">> => false}]}},
    DecACI = <<"contract C =\n"
	       "  function a : (int) => int\n">>,
    {Contract,MapACI,DecACI};
test_cases(3) ->
    Contract = <<"contract C =\n"
		 "  datatype bert('a) = Bin('a)\n"
		 "  function a(i : bert(string)) = 1\n">>,
    MapACI = #{<<"contract">> =>
		   #{<<"functions">> =>
			 [#{<<"arguments">> =>
				[#{<<"name">> => <<"i">>,
				   <<"type">> =>
				       #{<<"C.bert">> => [<<"string">>]}}],
			    <<"name">> => <<"a">>,<<"returns">> => <<"int">>,
			    <<"stateful">> => false}],
		     <<"name">> => <<"C">>,
		     <<"type_defs">> =>
			 [#{<<"name">> => <<"bert">>,
			    <<"typedef">> =>
				#{<<"variant">> =>
				      [#{<<"Bin">> => [<<"'a">>]}]},
			    <<"vars">> => [#{<<"name">> => <<"'a">>}]}]}},
    DecACI = <<"contract C =\n"
	       "  datatype bert('a) = Bin('a)\n"
	       "  function a : (C.bert(string)) => int\n">>,
    {Contract,MapACI,DecACI}.
