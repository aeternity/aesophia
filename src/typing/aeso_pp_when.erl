%%%-------------------------------------------------------------------
%%% @copyright (C) 2018, Aeternity Anstalt
%%% @doc
%%%     Pretty printing for type checking context information (when clauses).
%%%     This module is independent and does not depend on aeso_ast_infer_types.
%%% @end
%%%-------------------------------------------------------------------

-module(aeso_pp_when).

-include("aeso_type_records.hrl").

-export([
    pp_when/1
]).

%% -- Pretty printing for type checking context ------------------------------

pp_when({todo, What}) -> {pos(0, 0), io_lib:format("[TODO] ~p", [What])};
pp_when({at, Ann}) -> {pos(Ann), io_lib:format("at ~s", [pp_loc(Ann)])};
pp_when({check_typesig, Name, Inferred, Given}) ->
    {pos(Given),
     io_lib:format("when checking the definition of `~s`\n"
                   "  inferred type: `~s`\n"
                   "  given type:    `~s`",
         [Name, pp(instantiate(Inferred)), pp(instantiate(Given))])};
pp_when({infer_app, Fun, NamedArgs, Args, Inferred0, ArgTypes0}) ->
    Inferred = instantiate(Inferred0),
    ArgTypes = instantiate(ArgTypes0),
    {pos(Fun),
     io_lib:format("when checking the application of\n"
                   "  `~s`\n"
                   "to arguments~s",
                   [pp_typed("", Fun, Inferred),
                    [ ["\n  ", "`" ++ pp_expr(NamedArg) ++ "`"] || NamedArg <- NamedArgs ] ++
                    [ ["\n  ", "`" ++ pp_typed("", Arg, ArgT) ++ "`"]
                       || {Arg, ArgT} <- lists:zip(Args, ArgTypes) ] ])};
pp_when({field_constraint, FieldType0, InferredType0, Fld}) ->
    FieldType    = instantiate(FieldType0),
    InferredType = instantiate(InferredType0),
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
    RecType      = instantiate(RecType0),
    InferredType = instantiate(InferredType0),
    {Pos, WhyRec} = aeso_type_when_pretty:pp_why_record(Fld),
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
    {ThenType, ElseType} = instantiate({ThenType0, ElseType0}),
    Branches = [ {Then, ThenType} | [ {B, ElseType} || B <- if_branches(Else) ] ],
    {pos(element(1, hd(Branches))),
     io_lib:format("when comparing the types of the if-branches\n"
                   "~s", [string:join([ io_lib:format("~s (at ~s)", [pp_typed("  - ", B, BType), pp_loc(B)])
                                       || {B, BType} <- Branches ], "\n")])};
pp_when({case_pat, Pat, PatType0, ExprType0}) ->
    {PatType, ExprType} = instantiate({PatType0, ExprType0}),
    {pos(Pat),
     io_lib:format("when checking the type of the pattern `~s` against the expected type `~s`",
                   [pp_typed("", Pat, PatType),
                    pp_type(ExprType)])};
pp_when({check_expr, Expr, Inferred0, Expected0}) ->
    {Inferred, Expected} = instantiate({Inferred0, Expected0}),
    {pos(Expr),
     io_lib:format("when checking the type of the expression `~s` against the expected type `~s`",
                   [pp_typed("", Expr, Inferred), pp_type(Expected)])};
pp_when({checking_init_type, Ann}) ->
    {pos(Ann),
     io_lib:format("when checking that `init` returns a value of type `state`", [])};
pp_when({list_comp, BindExpr, Inferred0, Expected0}) ->
    {Inferred, Expected} = instantiate({Inferred0, Expected0}),
    {pos(BindExpr),
     io_lib:format("when checking rvalue of list comprehension binding `~s` against type `~s`",
                   [pp_typed("", BindExpr, Inferred), pp_type(Expected)])};
pp_when({check_named_arg_constraint, C}) ->
    {id, _, Name} = Arg = C#named_argument_constraint.name,
    [Type | _] = [ Type || {named_arg_t, _, {id, _, Name1}, Type, _} <- C#named_argument_constraint.args, Name1 == Name ],
    Err = io_lib:format("when checking named argument `~s` against inferred type `~s`",
                        [pp_typed("", Arg, Type), pp_type(C#named_argument_constraint.type)]),
    {pos(Arg), Err};
pp_when({checking_init_args, Ann, Con0, ArgTypes0}) ->
    Con = instantiate(Con0),
    ArgTypes = instantiate(ArgTypes0),
    {pos(Ann),
     io_lib:format("when checking arguments of `~s`'s init entrypoint to match\n(~s)",
                   [pp_type(Con), string:join([pp_type(A) || A <- ArgTypes], ", ")])
    };
pp_when({return_contract, App, Con0}) ->
    Con = instantiate(Con0),
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
pp_when({implement_interface_fun, Ann, Entrypoint, Interface}) ->
    { pos(Ann)
    , io_lib:format("when implementing the entrypoint `~s` from the interface `~s`", [Entrypoint, Interface])
    };
pp_when(unknown) -> {pos(0,0), ""}.

%% -- Helper functions -------------------------------------------------------

%% Position handling
pos(T) -> aeso_errors:pos(aeso_syntax:get_ann(file, T, no_file),
                          aeso_syntax:get_ann(line, T, 0),
                          aeso_syntax:get_ann(col, T, 0)).
pos(L, C) -> aeso_errors:pos(L, C).

%% If-branch handling
if_branches(If = {'if', Ann, _, Then, Else}) ->
    case proplists:get_value(format, Ann) of
        elif -> [Then | if_branches(Else)];
        _    -> [If]
    end;
if_branches(E) -> [E].

%% -- Delegate functions to avoid circular dependencies ----------------------

%% Pretty printing delegates
pp(T) -> aeso_type_pretty:pp(T).
pp_type(Type) -> aeso_type_pretty:pp_type(Type).
pp_type(Label, Type) -> aeso_type_pretty:pp_type(Label, Type).
pp_loc(T) -> aeso_type_pretty:pp_loc(T).
pp_expr(Expr) -> aeso_type_pretty:pp_expr(Expr).
pp_typed(Label, E, T) -> aeso_type_pretty:pp_typed(Label, E, T).

%% Type system delegates
instantiate(E) -> aeso_type_unify:instantiate(E).
