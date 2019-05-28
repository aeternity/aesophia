-module(aeso_aci_tests).

-include_lib("eunit/include/eunit.hrl").

simple_aci_test_() ->
    [{"Test contract " ++ integer_to_list(N),
      fun() -> test_contract(N) end}
     || N <- [1, 2, 3]].

test_contract(N) ->
    {Contract,MapACI,DecACI} = test_cases(N),
    {ok,JSON} = aeso_aci:contract_interface(json, Contract),
    ?assertEqual([MapACI], JSON),
    ?assertEqual({ok, DecACI}, aeso_aci:render_aci_json(JSON)).

test_cases(1) ->
    Contract = <<"contract C =\n"
		 "  function a(i : int) = i+1\n">>,
    MapACI = #{contract =>
		   #{name => <<"C">>,
		     type_defs => [],
                     event => #{variant => [#{<<"NoEventsDefined">> => []}]},
                     state => #{tuple => []},
		     functions =>
			 [#{name => <<"a">>,
			    arguments =>
				[#{name => <<"i">>,
				   type => <<"int">>}],
			    returns => <<"int">>,
			    stateful => false}]}},
    DecACI = <<"contract C =\n"
               "  type state = ()\n"
               "  datatype event = NoEventsDefined\n"
	       "  function a : (int) => int\n">>,
    {Contract,MapACI,DecACI};

test_cases(2) ->
    Contract = <<"contract C =\n"
		 "  type allan = int\n"
		 "  function a(i : allan) = i+1\n">>,
    MapACI = #{contract =>
                       #{name => <<"C">>,
                         type_defs =>
                             [#{name => <<"allan">>,
                                typedef => <<"int">>,
                                vars => []}],
                         event => #{variant => [#{<<"NoEventsDefined">> => []}]},
                         state => #{tuple => []},
			 functions =>
                             [#{arguments =>
                                    [#{name => <<"i">>,
                                       type => <<"C.allan">>}],
                                name => <<"a">>,
                                returns => <<"int">>,
                                stateful => false}]}},
    DecACI = <<"contract C =\n"
               "  type state = ()\n"
               "  datatype event = NoEventsDefined\n"
               "  type allan = int\n"
               "  function a : (C.allan) => int\n">>,
    {Contract,MapACI,DecACI};
test_cases(3) ->
    Contract = <<"contract C =\n"
                 "  type state = ()\n"
                 "  datatype event = SingleEventDefined\n"
		 "  datatype bert('a) = Bin('a)\n"
		 "  function a(i : bert(string)) = 1\n">>,
    MapACI = #{contract =>
		   #{functions =>
			 [#{arguments =>
				[#{name => <<"i">>,
				   type =>
				       #{<<"C.bert">> => [<<"string">>]}}],
			    name => <<"a">>,returns => <<"int">>,
			    stateful => false}],
		     name => <<"C">>,
                     event => #{variant => [#{<<"SingleEventDefined">> => []}]},
                     state => #{tuple => []},
		     type_defs =>
			 [#{name => <<"bert">>,
			    typedef =>
				#{variant =>
				      [#{<<"Bin">> => [<<"'a">>]}]},
			    vars => [#{name => <<"'a">>}]}]}},
    DecACI = <<"contract C =\n"
               "  type state = ()\n"
               "  datatype event = SingleEventDefined\n"
	       "  datatype bert('a) = Bin('a)\n"
	       "  function a : (C.bert(string)) => int\n">>,
    {Contract,MapACI,DecACI}.

%% Rounttrip
aci_test_() ->
    [{"Testing ACI generation for " ++ ContractName,
      fun() -> aci_test_contract(ContractName) end}
     || ContractName <- all_contracts()].

all_contracts() -> aeso_compiler_tests:compilable_contracts().

aci_test_contract(Name) ->
    String = aeso_test_utils:read_contract(Name),
    Opts   = [{include, {file_system, [aeso_test_utils:contract_path()]}}],
    {ok, JSON} = aeso_aci:contract_interface(json, String, Opts),

    io:format("JSON:\n~p\n", [JSON]),
    {ok, ContractStub} = aeso_aci:render_aci_json(JSON),

    io:format("STUB:\n~s\n", [ContractStub]),
    check_stub(ContractStub, [{src_file, Name}]),

    ok.

check_stub(Stub, Options) ->
    case aeso_parser:string(binary_to_list(Stub), Options) of
        {ok, Ast} ->
            try
                %% io:format("AST: ~120p\n", [Ast]),
                aeso_ast_infer_types:infer(Ast, [])
            catch _:{type_errors, TE} ->
                io:format("Type error:\n~s\n", [TE]),
                error(TE);
                  _:R ->
                io:format("Error: ~p\n", [R]),
                error(R)
            end;
        {error, E} ->
            io:format("Error: ~p\n", [E]),
            error({parse_error, E})
    end.

