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
    ?assertEqual({ok, DecACI}, aeso_aci:render_aci_json(JSON)),
    %% Check if the compiler provides correct aci
    {ok,#{aci := JSON2}} = aeso_compiler:from_string(Contract, [{aci, json}]),
    ?assertEqual(JSON, JSON2).

test_cases(1) ->
    Contract = <<"payable contract C =\n"
		 "  payable stateful entrypoint a(i : int) = i+1\n">>,
    MapACI = #{contract =>
		   #{name => <<"C">>,
		     type_defs => [],
                     payable => true,
		     functions =>
			 [#{name => <<"a">>,
			    arguments =>
				[#{name => <<"i">>,
				   type => <<"int">>}],
			    returns => <<"int">>,
			    stateful => true,
                            payable  => true}]}},
    DecACI = <<"payable contract C =\n"
	       "  payable entrypoint a : (int) => int\n">>,
    {Contract,MapACI,DecACI};

test_cases(2) ->
    Contract = <<"contract C =\n"
		 "  type allan = int\n"
		 "  entrypoint a(i : allan) = i+1\n">>,
    MapACI = #{contract =>
                       #{name => <<"C">>, payable => false,
                         type_defs =>
                             [#{name => <<"allan">>,
                                typedef => <<"int">>,
                                vars => []}],
			 functions =>
                             [#{arguments =>
                                    [#{name => <<"i">>,
                                       type => <<"C.allan">>}],
                                name => <<"a">>,
                                returns => <<"int">>,
                                stateful => false,
                                payable  => false}]}},
    DecACI = <<"contract C =\n"
               "  type allan = int\n"
               "  entrypoint a : (C.allan) => int\n">>,
    {Contract,MapACI,DecACI};
test_cases(3) ->
    Contract = <<"contract C =\n"
                 "  type state = unit\n"
                 "  datatype event = SingleEventDefined\n"
		 "  datatype bert('a) = Bin('a)\n"
		 "  entrypoint a(i : bert(string)) = 1\n">>,
    MapACI = #{contract =>
		   #{functions =>
			 [#{arguments =>
				[#{name => <<"i">>,
				   type =>
				       #{<<"C.bert">> => [<<"string">>]}}],
			    name => <<"a">>,returns => <<"int">>,
			    stateful => false, payable  => false}],
		     name => <<"C">>, payable => false,
                     event => #{variant => [#{<<"SingleEventDefined">> => []}]},
                     state => <<"unit">>,
		     type_defs =>
			 [#{name => <<"bert">>,
			    typedef =>
				#{variant =>
				      [#{<<"Bin">> => [<<"'a">>]}]},
			    vars => [#{name => <<"'a">>}]}]}},
    DecACI = <<"contract C =\n"
               "  type state = unit\n"
               "  datatype event = SingleEventDefined\n"
	       "  datatype bert('a) = Bin('a)\n"
	       "  entrypoint a : (C.bert(string)) => int\n">>,
    {Contract,MapACI,DecACI}.

%% Roundtrip
aci_test_() ->
    [{"Testing ACI generation for " ++ ContractName,
      fun() -> aci_test_contract(ContractName) end}
     || ContractName <- all_contracts()].

all_contracts() -> aeso_compiler_tests:compilable_contracts().

aci_test_contract(Name) ->
    String = aeso_test_utils:read_contract(Name),
    Opts   = [{include, {file_system, [aeso_test_utils:contract_path()]}}],
    {ok, JSON} = aeso_aci:contract_interface(json, String, Opts),
    {ok, #{aci := JSON1}} = aeso_compiler:from_string(String, [{aci, json}, {backend, fate} | Opts]),
    ?assertEqual(JSON, JSON1),

    io:format("JSON:\n~p\n", [JSON]),
    {ok, ContractStub} = aeso_aci:render_aci_json(JSON),

    io:format("STUB:\n~s\n", [ContractStub]),
    check_stub(ContractStub, [{src_file, Name}]),

    ok.

check_stub(Stub, Options) ->
    try aeso_parser:string(binary_to_list(Stub), Options) of
        Ast ->
            try
                %% io:format("AST: ~120p\n", [Ast]),
                aeso_ast_infer_types:infer(Ast, [])
            catch throw:{type_errors, TE} ->
                io:format("Type error:\n~s\n", [TE]),
                error(TE);
                  _:R ->
                io:format("Error: ~p\n", [R]),
                error(R)
            end
    catch throw:{error, Errs} ->
        _ = [ io:format("~s\n", [aeso_errors:pp(E)]) || E <- Errs ],
        error({parse_errors, Errs})
    end.
