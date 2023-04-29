-module(aeso_tc_pp).

-export([ pp/1
        , pp_type/1
        , pp_type/2
        , pp_typed/3
        , pp_expr/1
        , pp_why_record/1
        , pp_loc/1
        , pp_when/1
        ]).

%% -- Duplicated types -------------------------------------------------------

-type why_record() :: aeso_syntax:field(aeso_syntax:expr())
                    | {var_args, aeso_syntax:ann(), aeso_syntax:expr()}
                    | {proj, aeso_syntax:ann(), aeso_syntax:expr(), aeso_syntax:id()}.

%% -- Moved functions --------------------------------------------------------

pos(A) -> aeso_tc_ann_manip:pos(A).
pos(A, B) -> aeso_tc_ann_manip:pos(A, B).
loc(A) -> aeso_tc_ann_manip:loc(A).

%% ---------------------------------------------------------------------------

-type pos() :: aeso_errors:pos().

if_branches(If = {'if', Ann, _, Then, Else}) ->
    case proplists:get_value(format, Ann) of
        elif -> [Then | if_branches(Else)];
        _    -> [If]
    end;
if_branches(E) -> [E].

pp_when({todo, What}) -> {pos(0, 0), io_lib:format("[TODO] ~p", [What])};
pp_when({at, Ann}) -> {pos(Ann), io_lib:format("at ~s", [pp_loc(Ann)])};
pp_when({check_typesig, Name, Inferred, Given}) ->
    {pos(Given),
     io_lib:format("when checking the definition of `~s`\n"
                   "  inferred type: `~s`\n"
                   "  given type:    `~s`",
         [Name, pp(aeso_tc_type_utils:instantiate(Inferred)), pp(aeso_tc_type_utils:instantiate(Given))])};
pp_when({infer_app, Fun, NamedArgs, Args, Inferred0, ArgTypes0}) ->
    Inferred = aeso_tc_type_utils:instantiate(Inferred0),
    ArgTypes = aeso_tc_type_utils:instantiate(ArgTypes0),
    {pos(Fun),
     io_lib:format("when checking the application of\n"
                   "  `~s`\n"
                   "to arguments~s",
                   [pp_typed("", Fun, Inferred),
                    [ ["\n  ", "`" ++ pp_expr(NamedArg) ++ "`"] || NamedArg <- NamedArgs ] ++
                    [ ["\n  ", "`" ++ pp_typed("", Arg, ArgT) ++ "`"]
                       || {Arg, ArgT} <- lists:zip(Args, ArgTypes) ] ])};
pp_when({field_constraint, FieldType0, InferredType0, Fld}) ->
    FieldType    = aeso_tc_type_utils:instantiate(FieldType0),
    InferredType = aeso_tc_type_utils:instantiate(InferredType0),
    {pos(Fld),
     case Fld of
         {var_args, _Ann, _Fun} ->
             io_lib:format("when checking contract construction of type\n~s (at ~s)\nagainst the expected type\n~s\n",
                          [pp_type("  ", FieldType),
                           pp_loc(Fld),
                           pp_type("  ", InferredType)
                          ]);
         {field, _Ann, LV, Id, E} ->
             io_lib:format("when checking the assignment of the field `~s` to the old value `~s` and the new value `~s`",
                 [pp_typed("", {lvalue, [], LV}, FieldType),
                  pp(Id),
                  pp_typed("", E, InferredType)]);
         {field, _Ann, LV, E} ->
             io_lib:format("when checking the assignment of the field `~s` to the value `~s`",
                 [pp_typed("", {lvalue, [], LV}, FieldType),
                  pp_typed("", E, InferredType)]);
         {proj, _Ann, _Rec, _Fld} ->
             io_lib:format("when checking the record projection `~s` against the expected type `~s`",
                 [pp_typed("  ", Fld, FieldType),
                  pp_type("  ", InferredType)])
     end};
pp_when({record_constraint, RecType0, InferredType0, Fld}) ->
    RecType      = aeso_tc_type_utils:instantiate(RecType0),
    InferredType = aeso_tc_type_utils:instantiate(InferredType0),
    {Pos, WhyRec} = pp_why_record(Fld),
    case Fld of
        {var_args, _Ann, _Fun} ->
            {Pos,
             io_lib:format("when checking that contract construction of type\n~s\n~s\n"
                           "matches the expected type\n~s",
                           [pp_type("  ", RecType), WhyRec, pp_type("  ", InferredType)]
                          )
            };
        {field, _Ann, _LV, _Id, _E} ->
            {Pos,
             io_lib:format("when checking that the record type\n~s\n~s\n"
                           "matches the expected type\n~s",
                 [pp_type("  ", RecType), WhyRec, pp_type("  ", InferredType)])};
        {field, _Ann, _LV, _E} ->
            {Pos,
             io_lib:format("when checking that the record type\n~s\n~s\n"
                           "matches the expected type\n~s",
                 [pp_type("  ", RecType), WhyRec, pp_type("  ", InferredType)])};
        {proj, _Ann, Rec, _FldName} ->
            {pos(Rec),
             io_lib:format("when checking that the expression\n~s (at ~s)\nhas type\n~s\n~s",
                 [pp_typed("  ", Rec, InferredType), pp_loc(Rec),
                  pp_type("  ", RecType), WhyRec])}
    end;
pp_when({if_branches, Then, ThenType0, Else, ElseType0}) ->
    {ThenType, ElseType} = aeso_tc_type_utils:instantiate({ThenType0, ElseType0}),
    Branches = [ {Then, ThenType} | [ {B, ElseType} || B <- if_branches(Else) ] ],
    {pos(element(1, hd(Branches))),
     io_lib:format("when comparing the types of the if-branches\n"
                   "~s", [ [ io_lib:format("~s (at ~s)\n", [pp_typed("  - ", B, BType), pp_loc(B)])
                           || {B, BType} <- Branches ] ])};
pp_when({case_pat, Pat, PatType0, ExprType0}) ->
    {PatType, ExprType} = aeso_tc_type_utils:instantiate({PatType0, ExprType0}),
    {pos(Pat),
     io_lib:format("when checking the type of the pattern `~s` against the expected type `~s`",
                   [pp_typed("", Pat, PatType),
                    pp_type(ExprType)])};
pp_when({check_expr, Expr, Inferred0, Expected0}) ->
    {Inferred, Expected} = aeso_tc_type_utils:instantiate({Inferred0, Expected0}),
    {pos(Expr),
     io_lib:format("when checking the type of the expression `~s` against the expected type `~s`",
                   [pp_typed("", Expr, Inferred), pp_type(Expected)])};
pp_when({checking_init_type, Ann}) ->
    {pos(Ann),
     io_lib:format("when checking that `init` returns a value of type `state`", [])};
pp_when({list_comp, BindExpr, Inferred0, Expected0}) ->
    {Inferred, Expected} = aeso_tc_type_utils:instantiate({Inferred0, Expected0}),
    {pos(BindExpr),
     io_lib:format("when checking rvalue of list comprehension binding `~s` against type `~s`",
                   [pp_typed("", BindExpr, Inferred), pp_type(Expected)])};
pp_when({check_named_arg_constraint, CArgs, CName, CType}) ->
    {id, _, Name} = Arg = CName,
    [Type | _] = [ Type || {named_arg_t, _, {id, _, Name1}, Type, _} <- CArgs, Name1 == Name ],
    Err = io_lib:format("when checking named argument `~s` against inferred type `~s`",
                        [pp_typed("", Arg, Type), pp_type(CType)]),
    {pos(Arg), Err};
pp_when({checking_init_args, Ann, Con0, ArgTypes0}) ->
    Con = aeso_tc_type_utils:instantiate(Con0),
    ArgTypes = aeso_tc_type_utils:instantiate(ArgTypes0),
    {pos(Ann),
     io_lib:format("when checking arguments of `~s`'s init entrypoint to match\n(~s)",
                   [pp_type(Con), string:join([pp_type(A) || A <- ArgTypes], ", ")])
    };
pp_when({return_contract, App, Con0}) ->
    Con = aeso_tc_type_utils:instantiate(Con0),
    {pos(App)
    , io_lib:format("when checking that expression returns contract of type `~s`", [pp_type(Con)])
    };
pp_when({arg_name, Id1, Id2, When}) ->
    {Pos, Ctx} = pp_when(When),
    {Pos
    , io_lib:format("when unifying names of named arguments: `~s` and `~s`\n~s", [pp_expr(Id1), pp_expr(Id2), Ctx])
    };
pp_when({var_args, Ann, Fun}) ->
    {pos(Ann)
    , io_lib:format("when resolving arguments of variadic function `~s`", [pp_expr(Fun)])
    };
pp_when(unknown) -> {pos(0,0), ""}.

-spec pp_why_record(why_record()) -> {pos(), iolist()}.
pp_why_record({var_args, Ann, Fun}) ->
    {pos(Ann),
     io_lib:format("arising from resolution of variadic function `~s`",
                   [pp_expr(Fun)])};
pp_why_record(Fld = {field, _Ann, LV, _E}) ->
    {pos(Fld),
     io_lib:format("arising from an assignment of the field `~s`",
                   [pp_expr({lvalue, [], LV})])};
pp_why_record(Fld = {field, _Ann, LV, _Alias, _E}) ->
    {pos(Fld),
     io_lib:format("arising from an assignment of the field `~s`",
                   [pp_expr({lvalue, [], LV})])};
pp_why_record({proj, _Ann, Rec, FldName}) ->
    {pos(Rec),
     io_lib:format("arising from the projection of the field `~s`",
         [pp(FldName)])}.

pp_typed(Label, E, T = {type_sig, _, _, _, _, _}) -> pp_typed(Label, E, aeso_tc_type_utils:typesig_to_fun_t(T));
pp_typed(Label, {typed, _, Expr, _}, Type) ->
    pp_typed(Label, Expr, Type);
pp_typed(Label, Expr, Type) ->
    pp_expr(Label, {typed, [], Expr, Type}).

pp_expr(Expr) ->
    pp_expr("", Expr).
pp_expr(Label, Expr) ->
    prettypr:format(prettypr:beside(prettypr:text(Label), aeso_pretty:expr(Expr, [show_generated])), 80, 80).

pp_type(Type) ->
    pp_type("", Type).
pp_type(Label, Type) ->
    prettypr:format(prettypr:beside(prettypr:text(Label), aeso_pretty:type(Type, [show_generated])), 80, 80).

pp_loc(T) ->
    {File, IncludeType, Line, Col} = loc(T),
    case {Line, Col} of
        {0, 0} -> "(builtin location)";
        _      -> case IncludeType of
                      none -> io_lib:format("line ~p, column ~p", [Line, Col]);
                      _    -> io_lib:format("line ~p, column ~p in ~s", [Line, Col, File])
                  end
    end.

pp(T = {type_sig, _, _, _, _, _}) ->
    pp(aeso_tc_type_utils:typesig_to_fun_t(T));
pp([]) ->
    "";
pp([T]) ->
    pp(T);
pp([T|Ts]) ->
    [pp(T), ", "|pp(Ts)];
pp({id, _, Name}) ->
    Name;
pp({qid, _, Name}) ->
    string:join(Name, ".");
pp({con, _, Name}) ->
    Name;
pp({qcon, _, Name}) ->
    string:join(Name, ".");
pp({uvar, _, Ref}) ->
    %% Show some unique representation
    ["?u" | integer_to_list(erlang:phash2(Ref, 16384)) ];
pp({tvar, _, Name}) ->
    Name;
pp({if_t, _, Id, Then, Else}) ->
    ["if(", pp([Id, Then, Else]), ")"];
pp({tuple_t, _, []}) ->
    "unit";
pp({tuple_t, _, Cpts}) ->
    ["(", string:join(lists:map(fun pp/1, Cpts), " * "), ")"];
pp({bytes_t, _, any}) -> "bytes(_)";
pp({bytes_t, _, Len}) ->
    ["bytes(", integer_to_list(Len), ")"];
pp({app_t, _, T, []}) ->
    pp(T);
pp({app_t, _, Type, Args}) ->
    [pp(Type), "(", pp(Args), ")"];
pp({named_arg_t, _, Name, Type, _Default}) ->
    [pp(Name), " : ", pp(Type)];
pp({fun_t, _, Named = {uvar, _, _}, As, B}) ->
    ["(", pp(Named), " | ", pp(As), ") => ", pp(B)];
pp({fun_t, _, Named, As, B}) when is_list(Named) ->
    ["(", pp(Named ++ As), ") => ", pp(B)];
pp(Other) ->
    io_lib:format("~p", [Other]).
