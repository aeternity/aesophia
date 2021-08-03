%%% -*- erlang-indent-level:4; indent-tabs-mode: nil -*-
%%%-------------------------------------------------------------------
%%% @doc Test Sophia liquid type system.
%%%
%%% @end
%%%-------------------------------------------------------------------

-module(aeso_type_refinement_tests).

-compile([export_all, nowarn_export_all]).

-include_lib("eunit/include/eunit.hrl").
-include("../src/aeso_ast_refine_types.hrl").

-define(nu(), ?nu(?ann())).
-define(nu_op(Op, Rel), ?op(?ann(), ?nu(), Op, Rel)).
-define(id(V), {id, ?ann(), V}).
-define(int(V), {int, ?ann(), V}).
-define(unstate(T), {tuple_t, ?ann(), [T, nope, nope]}).

setup() ->
    erlang:system_flag(backtrace_depth, 100),
    aeso_smt:start_z3(),
    aeso_ast_refine_types:init_refiner(),
    ok.

unsetup(_) ->
    aeso_smt:stop_z3(),
    ok.

hagia_test_() ->
    ?IF(os:find_executable("z3") == false, [], % This turns off hagia tests on machines that don't have Z3
    {timeout, 100000000,
     {inorder,
      {foreach, local, fun setup/0, fun unsetup/1,
       [ {timeout, 5, smt_solver_test_group()}
       , {timeout, 1000000, refiner_test_group()}
       ]
      }
     }}).

smt_solver_test_group() ->
    [ { "x == x"
      , fun() ->
                ?assert(aeso_ast_refine_types:impl_holds(
                          aeso_ast_refine_types:bind_var(
                            ?nu(), ?id("int"),
                            aeso_ast_refine_types:init_env(aeso_ast_infer_types:init_env([]))),
                          [],
                          [?nu_op('==', ?nu())]))
        end
      }
    ].

refiner_test_group() ->
    [ {"Testing type refinement of the " ++ ContractName ++ ".aes contract",
       {timeout, 600,
        fun() ->
                try {run_refine("hagia/" ++ ContractName), Expect} of
                    {{ok, {Env, AST}}, {success, Assertions}} ->
                        check_ast_refinement(Env, AST, Assertions);
                    {{error, {refinement_errors, Errs}}, {error, ExpErrors}} ->
                        check_errors(Errs, ExpErrors);
                    {{error, Err}, _} ->
                        io:format(aeso_ast_refine_types:pp_error(Err)),
                        error(Err)
                catch E:T:S -> io:format("Caught:\n~p: ~p\nstack:\n~p\n", [E, T, S]), error(T)
                end
        end}} || {ContractName, Expect} <- compilable_contracts()].


run_refine(Name) ->
    ContractString = aeso_test_utils:read_contract(Name),
    Ast = aeso_parser:string(ContractString, sets:new(), [{file, Name}]),
    {TEnv, TAst, _} = aeso_ast_infer_types:infer(Ast, [return_env, dont_unfold, {file, Name}]),
    RAst = aeso_ast_refine_types:refine_ast(TEnv, TAst),
    RAst.

check_ast_refinement(Env, AST, Assertions) ->
    [ case maps:get({Name, FName}, Assertions, unchecked) of
          unchecked -> ok;
          {Scope, ExRetType} -> check_type(Env, AST, Scope, ExRetType, Type)
      end
     || {_, _, {con, _, Name}, Defs} <- AST,
        {fun_decl, _, {id, _, FName}, Type} <- Defs
    ].

check_type(Env, AST, Scope, ExRet, Fun = {dep_fun_t, Ann, Args, _}) ->
    put(refiner_errors, []),
    Left  = {subtype, {test, 0}, ?ann(), Env, Fun, {dep_fun_t, Ann, Args, ExRet}},
    Right = {subtype, {test, 0}, ?ann(), Env, {dep_fun_t, Ann, Args, ExRet}, Fun},
    CS = aeso_ast_refine_types:split_constr(
           case Scope of
               iff -> [Left, Right];
               sub -> [Left]
           end),
    aeso_ast_refine_types:solve(Env, AST, CS),
    case get(refiner_errors) of
        [] -> ok;
        Errs -> throw({refinement_errors, Errs})
    end.

check_errors(Errs, ExpErrs) ->
    ?assertEqual(length(ExpErrs), length(Errs)).

compilable_contracts() ->
    [ {"simple",
       {success,
        #{{"C", "f"} => {iff, ?refined(?nu(), ?int_t(?ann()), [?nu_op('==', ?int(123))])}}
       }
      }
    %% , {"len",
    %%    {success,
    %%     #{{"C", "f"} => {iff, ?refined(?nu(), ?int_t(?ann()), [?nu_op('==', ?id("l"))])}}
    %%    }
    %%   }
    %% , {"max",
    %%    {success,
    %%     #{{"C", "max"}  => {iff, ?refined(?nu(), ?int_t(?ann()), [?nu_op('>=', ?id("a")), ?nu_op('>=', ?id("b"))])}
    %%     , {"C", "trim"} => {iff, ?refined(?nu(), ?int_t(?ann()), [?nu_op('>=', ?int(0)), ?nu_op('>=', ?id("x"))])}
    %%     }
    %%    }
    %%   }
    %% , {"switch",
    %%    {success,
    %%     #{{"C", "f"} => {iff, ?refined(?nu(), ?int_t(?ann()), [?nu_op('==', ?id("x"))])}
    %%     , {"C", "g"} => {iff, ?refined(?nu(), ?int_t(?ann()), [?nu_op('==', ?int(2))])}
    %%     }
    %%    }
    %%   }
    %% , {"require",
    %%    {success,
    %%     #{{"C", "f1"} => {iff, ?refined(?nu(), ?int_t(?ann()), [?nu_op('==', ?int(0))])}
    %%     , {"C", "f2"} => {iff, ?refined(?nu(), ?int_t(?ann()),
    %%                               [?nu_op('=<', ?id("x")), ?nu_op('>=', ?int(0)),
    %%                                ?nu_op('=<', ?int(1)),  ?nu_op('!=', ?op(?ann(), ?id("x"), '-', ?int(1)))
    %%                               ])}
    %%     }
    %%    }
    %%   }
    %% , {"balance",
    %%    {success,
    %%     #{{"C", "f1"} => {iff, ?refined(?nu(), ?int_t(?ann()), [?nu_op('==', ?int(0))])}
    %%     , {"C", "f2"} => {sub, ?unstate(?refined(?nu(), ?int_t(?ann()), [?nu_op('==', ?int(0))]))}
    %%     }
    %%    }
    %%   }
    %% , {"types",
    %%    {success,
    %%     #{{"C", "test_i"} => ?refined(?nu(), ?int_t(?ann()), [?nu_op('==', ?int(123))])
    %%     , {"C", "test_ii"} => ?refined(?nu(), ?int_t(?ann()), [?nu_op('==', ?int(123))])
    %%     }
    %%    }
    %%   }
    %% , {"args",
    %%    {success,
    %%     #{{"C", "f"} => {iff, ?refined(?nu(), ?int_t(?ann()), [?nu_op('=<', ?id("n"))])}
    %%     }
    %%    }
    %%   }
    %% , {"state",
    %%   {success,
    %%    #{{"C", "f"} => {iff, ?unstate(?refined(?nu(), ?int_t(?ann()), [?nu_op('==', {proj, [], ?id("$init_state"), ?id("C.state.x")})]))}
    %%    }
    %%   }
    %%  }
    %% , {"failing",
    %%    {error,
    %%     lists:seq(1, 7)
    %%    }
    %%   }
    ].
