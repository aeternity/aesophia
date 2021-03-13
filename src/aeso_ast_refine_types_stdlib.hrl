
-define(IS_STDLIB(NS),
        (NS == "List" orelse
         NS == "ListInternal" orelse
         NS == "Option" orelse
         NS == "Bits" orelse
         NS == "Bytes" orelse
         NS == "Char" orelse
         NS == "Int" orelse
         NS == "Map" orelse
         NS == "Address" orelse
         NS == "Crypto" orelse
         NS == "Auth" orelse
         NS == "Oracle" orelse
         NS == "AENS" orelse
         NS == "Contract" orelse
         NS == "Call" orelse
         NS == "Chain" orelse
         false
        )).

-define(IS_STDLIB_STATEFUL(NS, Fun),
        ((NS == "List" andalso Fun == "map") orelse
         (NS == "List" andalso Fun == "flat_map") orelse
         (NS == "Chain" andalso Fun == "spend") orelse
         false
        )).


-define(CONSTR(NS, Fun, Args, ArgsT, Body),
        constr_expr(Env, {app, Ann, {typed, _, {qid, _, [NS, Fun]}, {fun_t, _, [], ArgsT, _}}, Args}, RetT, S0) ->
               Body;
       ).
-define(CONSTR(NS, Fun, Args, Body),
constr_expr(Env, {app, Ann, {typed, _, {qid, _, [NS, Fun]}, {fun_t, _, [], _, _}}, Args}, RetT, S0) ->
    Body;
    ).

-define(UNSOME(Pat, Constrs), [Pat] =
                   [ ArgT
                     || C <- Constrs,
                        ArgT <- case C of
                                    {dep_constr_t, CAnn, Con = {con, _, "Some"}, [CT]} -> [CT];
                                    _ -> []
                                end
                   ]).

-define(
   STDLIB_CONSTRS,
   ?CONSTR("Chain", "spend", [State, Balance, Addr, Amount],
           begin
               {_, S1} = constr_expr(Env, State, S0),
               {BalanceT, S2} = constr_expr(Env, Balance, S1),
               {_, S3} = constr_expr(Env, Addr, S2),
               {AmountT, S4} = constr_expr(Env, Amount, S3),
               ExprT = {tuple_t, _, [_, _, NewBalanceT]} = fresh_liquid(Env, "spend", RetT),
               {ExprT,
                [ {well_formed, constr_id(chain_spend), Env, ExprT}
                , {subtype, constr_id(chain_spend), Ann, Env,
                   AmountT,
                   ?refined(?int_t(Ann), [ ?op(Ann, ?nu(Ann), '=<', Balance)
                                        , ?op(Ann, ?nu(Ann), '>=', ?int(Ann, 0))])}
                , {subtype, constr_id(chain_spend), Ann, Env,
                   ?refined(?int_t(Ann), [?op(Ann, ?nu(Ann), '==', ?op(Ann, Balance, '-', Amount))]),
                   NewBalanceT
                  }
                | S4
                ]
               }
           end
          )

   ?CONSTR("List", "is_empty", [L],
           begin
               {_, S1} = constr_expr(Env, L, S0),
               ExprT = fresh_liquid(Env, "is_empty", RetT),
               { ExprT
               , [ {well_formed, constr_id(list_is_empty), Env, ExprT}
                 , {subtype, constr_id(is_empty), Ann, Env,
                    ?refined(?bool_t(Ann), [?op(Ann, ?nu(Ann), '==', ?op(Ann, L, '==', ?int(Ann, 0)))]),
                    ExprT}
                 | S1
                 ]
               }
           end
          )

    ?CONSTR("List", "first", [L],
           begin
               {{dep_list_t, _, _, ElemT, _}, S1} = constr_expr(Env, L, S0),
               ExprT = {dep_variant_t, _, Id, _, _, Constrs} = fresh_liquid(Env, "first", RetT),
               ?UNSOME(RetConT, Constrs),
               EnvEmpty = assert(?op(Ann, L, '==', ?int(Ann, 0)), Env),
               EnvCons = assert(?op(Ann, L, '>', ?int(Ann, 0)), Env),
               { ExprT
               , [ {well_formed, constr_id(list_first), Env, ExprT}
                 , {subtype, constr_id(list_first), Ann, EnvEmpty,
                    {dep_variant_t, Ann, Id, RetT, [{is_tag, Ann, Id, {qcon, Ann, ["None"]}, []}], Constrs},
                    ExprT}
                 , {subtype, constr_id(list_first), Ann, EnvCons,
                    {dep_variant_t, Ann, Id, RetT, [{is_tag, Ann, Id, {qcon, Ann, ["Some"]}, [RetConT]}], Constrs},
                    ExprT}
                 , {subtype, constr_id(list_first), Ann, EnvCons, ElemT, RetConT}
                 | S1
                 ]
               }
           end
           )

    ?CONSTR("List", "tail", [L],
           begin
               {{dep_list_t, _, _, ElemT, _}, S1} = constr_expr(Env, L, S0),
               {_, S1} = constr_expr(Env, L, S0),
               ExprT = {dep_variant_t, _, Id, _, _, Constrs} = fresh_liquid(Env, "tail", RetT),
               ?UNSOME(RetConT, Constrs),
               EnvEmpty = assert(?op(Ann, L, '==', ?int(Ann, 0)), Env),
               EnvCons = assert(?op(Ann, L, '>', ?int(Ann, 0)), Env),
               LId = fresh_id(Ann, "tail_l"),
               { ExprT
               , [ {well_formed, constr_id(list_tail), Env, ExprT}
                 , {subtype, constr_id(list_tail), Ann, EnvEmpty,
                    {dep_variant_t, Ann, Id, RetT, [{is_tag, Ann, Id, {qcon, Ann, ["None"]}, []}], Constrs},
                    ExprT}
                 , {subtype, constr_id(list_tail), Ann, EnvCons,
                    {dep_variant_t, Ann, Id, RetT, [{is_tag, Ann, Id, {qcon, Ann, ["Some"]}, [RetConT]}], Constrs},
                    ExprT}
                 , {subtype, constr_id(list_tail), Ann, EnvCons,
                   {dep_list_t, Ann, LId, ElemT, [?op(Ann, LId, '==', ?op(Ann, L, '-', ?int(Ann, 1)))]}, RetConT}
                 | S1
                 ]
               }
           end
           )

    ?CONSTR("List", "last", [L],
           begin
               {{dep_list_t, _, _, ElemT, _}, S1} = constr_expr(Env, L, S0),
               ExprT = {dep_variant_t, _, Id, _, _, Constrs} = fresh_liquid(Env, "last", RetT),
               ?UNSOME(RetConT, Constrs),
               EnvEmpty = assert(?op(Ann, L, '==', ?int(Ann, 0)), Env),
               EnvCons = assert(?op(Ann, L, '>', ?int(Ann, 0)), Env),
               { ExprT
               , [ {well_formed, constr_id(list_last), Env, ExprT}
                 , {subtype, constr_id(list_last), Ann, EnvEmpty,
                    {dep_variant_t, Ann, Id, RetT, [{is_tag, Ann, Id, {qcon, Ann, ["None"]}, []}], Constrs},
                    ExprT}
                 , {subtype, constr_id(list_last), Ann, EnvCons,
                    {dep_variant_t, Ann, Id, RetT, [{is_tag, Ann, Id, {qcon, Ann, ["Some"]}, [RetConT]}], Constrs},
                    ExprT}
                 , {subtype, constr_id(list_last), Ann, EnvCons, ElemT, RetConT}
                 | S1
                 ]
               }
           end
           )

   %% TODO contains – force false if no way to fulfill

   %% TODO find – reduce type to fulfill the predicate

    ?CONSTR("List", "find_indices", [P, L], %% TODO: len == 0 if no way to fulfill
           begin
               {_, S1} = constr_expr(Env, P, S0),
               {_, S2} = constr_expr(Env, L, S1),
               ExprT = {dep_list_t, _, _, ElemT, _} = fresh_liquid(Env, "find_indices", RetT),
               LId = fresh_id(Ann, "find_indices_l"),
               { ExprT
               , [ {well_formed, constr_id(list_find_indices), Env, ExprT}
                 , {subtype, constr_id(list_find_indices), Ann, Env,
                    {dep_list_t, Ann, LId, ElemT, [?op(Ann, LId, '=<', L)]},
                    ExprT
                   }
                 , {subtype, constr_id(list_find_indices), Ann, Env, ?d_nonneg_int(Ann), ElemT}
                 | S2
                 ]
               }
           end
           )

    ?CONSTR("List", "nth", [I, L],
           begin
               {IT, S1} = constr_expr(Env, I, S0),
               {{dep_list_t, _, _, ElemT, _}, S2} = constr_expr(Env, L, S1),
               ExprT = {dep_variant_t, _, Id, _, _, Constrs} = fresh_liquid(Env, "nth", RetT),
               ?UNSOME(RetConT, Constrs),
               EnvEmpty = assert(?op(Ann, L, '==', ?int(Ann, 0)), Env),
               EnvCons = assert(?op(Ann, L, '>', ?int(Ann, 0)), Env),
               { ExprT
               , [ {well_formed, constr_id(list_nth), Env, ExprT}
                 , {subtype, constr_id(list_nth), Ann, EnvEmpty,
                    {dep_variant_t, Ann, Id, RetT, [{is_tag, Ann, Id, {qcon, Ann, ["None"]}, []}], Constrs},
                    ExprT}
                 , {subtype, constr_id(list_nth), Ann, EnvCons,
                    {dep_variant_t, Ann, Id, RetT, [{is_tag, Ann, Id, {qcon, Ann, ["Some"]}, [RetConT]}], Constrs},
                    ExprT}
                 , {subtype, constr_id(list_nth), Ann, EnvCons, ElemT, RetConT}
                 , {subtype, constr_id(list_nth), Ann, Env, IT, ?d_nonneg_int(Ann)}
                 | S2
                 ]
               }
           end
           )

   ?CONSTR("List", "get", [I, L],
           begin
               {IT, S1} = constr_expr(Env, I, S0),
               {{dep_list_t, _, _, ElemT, _}, S2} = constr_expr(Env, L, S1),
               ExprT = fresh_liquid(Env, "get", RetT),
               LId = fresh_id(Ann, "get_l"),
               { ExprT
               , [ {well_formed, constr_id(list_get), Env, ExprT}
                 , {subtype, constr_id(list_get), Ann, Env,
                    IT,
                    {refined_t, Ann, LId, ?int_t(Ann), [?op(Ann, LId, '<', L)]}}
                 , {subtype, constr_id(list_get), Ann, Env, ElemT, ExprT}
                 , {subtype, constr_id(list_get), Ann, Env, IT, ?d_nonneg_int(Ann)}
                 | S2
                 ]
               }
           end
          )

   ?CONSTR("List", "length", [L],
           begin
               {_, S1} = constr_expr(Env, L, S0),
               ExprT = fresh_liquid(Env, "length", RetT),
               LId = fresh_id(Ann, "length_l"),
               { ExprT
               , [ {well_formed, constr_id(list_length), Env, ExprT}
                 , {subtype, constr_id(list_length), Ann, Env,
                   {refined_t, Ann, LId, ?int_t(Ann), [?op(Ann, LId, '==', L)]}
                   , ExprT}
                 | S1
                 ]
               }
           end
           )

   ?CONSTR("List", "from_to", [From, To],
           begin
               {_, S1} = constr_expr(Env, From, S0),
               {_, S2} = constr_expr(Env, To, S1),
               ExprT = fresh_liquid(Env, "from_to", RetT),
               ElemT = ?refined(?int_t(Ann), [?op(Ann, From, '=<', ?nu(Ann)), ?op(Ann, ?nu(Ann), '=<', To)]),
               EnvEmpty = assert(?op(Ann, To, '<', From), Env),
               EnvSome = assert(?op(Ann, To, '>=', From), Env),
               LId = fresh_id(Ann, "from_to_l"),
               { ExprT
               , [ {well_formed, constr_id(list_from_to), Env, ExprT}
                 , {subtype, constr_id(list_from_to), Ann, EnvEmpty,
                    {dep_list_t, Ann, LId, ElemT, [?op(Ann, LId, '==', ?int(Ann, 0))]},
                    ExprT}
                 , {subtype, constr_id(list_from_to), Ann, EnvSome,
                    {dep_list_t, Ann, LId, ElemT, [?op(Ann, LId, '==', ?op(Ann, ?op(Ann, To, '-', From), '+', ?int(Ann, 1)))]},
                    ExprT}
                 | S2
                 ]
               }
           end
          )

   ?CONSTR("List", "from_to_step", [From, To, Step],
           begin
               {_, S1} = constr_expr(Env, From, S0),
               {_, S2} = constr_expr(Env, To, S1),
               {StepT, S3} = constr_expr(Env, Step, S2),
               ExprT = fresh_liquid(Env, "from_to_step", RetT),
               ElemT = ?refined(?int_t(Ann), [?op(Ann, From, '=<', ?nu(Ann)), ?op(Ann, ?nu(Ann), '=<', To)]),
               EnvEmpty = assert(?op(Ann, To, '<', From), Env),
               EnvSome = assert(?op(Ann, To, '>=', From), Env),
               LId = fresh_id(Ann, "from_to_l_step"),
               { ExprT
               , [ {well_formed, constr_id(list_from_to_step), Env, ExprT}
                 , {subtype, constr_id(list_from_to_step), Ann, EnvEmpty,
                    {dep_list_t, Ann, LId, ElemT, [?op(Ann, LId, '==', ?int(Ann, 0))]},
                    ExprT}
                 , {subtype, constr_id(list_from_to_step), Ann, EnvSome,
                    {dep_list_t, Ann, LId, ElemT,
                     [?op(Ann, LId, '==', ?op(Ann, ?op(Ann, ?op(Ann, To, '-', From), '/', Step), '+', ?int(Ann, 1)))]},
                    ExprT}
                 , {subtype, constr_id(list_from_to_step), Ann, Env, StepT, ?refined(?int_t(Ann), [?op(Ann, ?nu(Ann), '>', ?int(Ann, 0))])}
                 | S2
                 ]
               }
           end
          )

   %% TODO insert_at – consider length and update ElemT

   %% TODO insert_by – consider length and update ElemT. skip comparator

   ?CONSTR("List", "reverse", [L],
           begin
               {LT, S1} = constr_expr(Env, L, S0),
               ExprT = fresh_liquid(Env, "reverse", RetT),
               { ExprT
               , [ {well_formed, constr_id(list_reverse), Env, ExprT}
                 , {subtype, constr_id(list_reverse), Ann, Env, LT, ExprT}
                 | S1
                 ]
               }
           end
          )

   ?CONSTR("List", "map", [State = ?typed_p(_, StateT), Balance = ?typed_p(_, BalanceT), F = ?typed_p(UF), L],
           [_, _, {fun_t, _, _, [_, _, _], _}, _],
           begin
               IsStateful = is_stateful(Env, UF),
               {_, S1} = constr_expr(Env, State, S0),
               {_, S2} = constr_expr(Env, Balance, S1),
               NewStateT = fresh_liquid(Env, "map_state", StateT),
               NewBalanceT = fresh_liquid(Env, "map_balance", BalanceT),
               {{dep_list_t, _, LId, ElemT, LenQual}, S3} = constr_expr(Env, L, S2),
               {{dep_fun_t, _,
                 [ {dep_arg_t, _, StateId, StateArgT}
                 , {dep_arg_t, _, BalanceId, BalanceArgT}
                 , {dep_arg_t, _, ArgId, ArgT}
                 ], FunResT}, S4} = constr_expr(Env, F, S3),
               case IsStateful of
                   true  -> {tuple_t, _, [ResT|_]} = FunResT;
                   false -> ResT = FunResT
               end,
               {tuple_t, ExAnn, [ExprT|_]} = fresh_liquid(Env, "map", RetT),
               STExprT = {tuple_t, ExAnn, [ExprT, NewStateT, NewBalanceT]},
               AbstractElem = fresh_id(Ann, "map_list_elem"),
               AppEnv = bind_var(AbstractElem, ElemT, Env),
               AppElemT =
                   apply_subst(
                     [ {StateId, State}
                     , {BalanceId, Balance}
                     , {ArgId, AbstractElem}
                     ], ResT
                    ),
               { STExprT
               , [ {well_formed, constr_id(list_map_wf), Env, STExprT}
                 , {subtype, constr_id(list_map_len_preserve), Ann, AppEnv,
                   {dep_list_t, Ann, LId, AppElemT, LenQual}, ExprT}
                 , {subtype, constr_id(list_map_state), Ann, Env, StateT, StateArgT}
                 , {subtype, constr_id(list_map_balance), Ann, Env, BalanceT, BalanceArgT}
                 | S4
                 ]
               }
           end
          )

   ?CONSTR("List", "flat_map", [State = ?typed_p(_, StateT), Balance = ?typed_p(_, BalanceT), F = ?typed_p(UF), L],
           [_, _, {fun_t, _, _, [_, _, _], _}, _],
           begin
               IsStateful = is_stateful(Env, UF),
               {_, S1} = constr_expr(Env, State, S0),
               {_, S2} = constr_expr(Env, Balance, S1),
               NewStateT = fresh_liquid(Env, "flat_map_state", StateT),
               NewBalanceT = fresh_liquid(Env, "flat_map_balance", BalanceT),
               {{dep_list_t, _, LId, ElemT, _}, S3} = constr_expr(Env, L, S2),
               {QWE = {dep_fun_t, _,
                 [ {dep_arg_t, _, StateId, StateArgT}
                 , {dep_arg_t, _, BalanceId, BalanceArgT}
                 , {dep_arg_t, _, ArgId, ArgT}
                 ], FunResT}, S4} = constr_expr(Env, F, S3),
               case IsStateful of
                   true  -> {tuple_t, _, [ResT|_]} = FunResT;
                   false -> ResT = FunResT
               end,
               {dep_list_t, _, _, ResElemT, _} = ResT,
               {tuple_t, ExAnn, [ExprT|_]} = fresh_liquid(Env, "flat_map", RetT),
               STExprT = {tuple_t, ExAnn, [ExprT, NewStateT, NewBalanceT]},
               AbstractElem = fresh_id(Ann, "flat_map_list_elem"),
               AbstractGen = fresh_id(Ann, "flat_map_gen"),
               ResSubst =
                   [ {StateId, State}
                   , {BalanceId, Balance}
                   , {ArgId, AbstractElem}
                   ],
               AppEnv = bind_vars(
                          [ {AbstractElem, ElemT}
                          , {AbstractGen, apply_subst(ResSubst, ResT)}
                          ], Env),
               AppElemT = apply_subst(ResSubst, ResElemT),
               { STExprT
               , [ {well_formed, constr_id(list_flat_map), Env, STExprT}
                 , {subtype, constr_id(list_flat_map), Ann, AppEnv,
                    {dep_list_t, Ann, LId, AppElemT, [?op(Ann, LId, '>=', ?int(Ann, 0)), ?op(Ann, LId, '=<', ?op(Ann, L, '*', AbstractGen))]},
                    ExprT}
                 , {subtype, constr_id(list_flat_map), Ann, Env, StateT, StateArgT}
                 , {subtype, constr_id(list_flat_map), Ann, Env, BalanceT, BalanceArgT}
                 | S4
                 ]
               }
           end
          )
  ).
