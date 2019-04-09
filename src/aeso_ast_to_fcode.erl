%%%-------------------------------------------------------------------
%%% @author Ulf Norell
%%% @copyright (C) 2019, Aeternity Anstalt
%%% @doc
%%%     Compiler from Aeterinty Sophia language to Fate intermediate code.
%%% @end
%%% Created : 26 Mar 2019
%%%
%%%-------------------------------------------------------------------
-module(aeso_ast_to_fcode).

-export([ast_to_fcode/2, format_fexpr/1]).
-export_type([fcode/0, fexpr/0, fun_def/0]).

%% -- Type definitions -------------------------------------------------------

-type option() :: term().

-type attribute() :: stateful | pure.

-type fun_name() :: {entrypoint, binary()}
                  | {local_fun, [string()]}
                  | init.
-type var_name() :: string().
-type sophia_name() :: [string()].

-type binop() :: '+' | '-' | '==' | '::'.

-type fexpr() :: {int, integer()}
               | {bool, false | true}
               | nil
               | {var, var_name()}
               | {tuple, [fexpr()]}
               | {binop, ftype(), binop(), fexpr(), fexpr()}
               | {'let', var_name(), fexpr(), fexpr()}
               | {switch, fsplit()}.

-type fsplit() :: {split, ftype(), var_name(), [fcase()]}
                | {nosplit, fexpr()}.

-type fcase() :: {'case', fsplit_pat(), fsplit()}.

-type fsplit_pat()  :: {bool, false | true}
                     | {int, integer()}
                     | {tuple, [var_name()]}
                     | {var, var_name()}.

-type ftype() :: integer
               | boolean
               | {list, ftype()}
               | {map, ftype(), ftype()}
               | {tuple, [ftype()]}
               | address
               | hash
               | signature
               | contract
               | oracle
               | oracle_query
               | name
               | channel
               | bits
               | {variant, [[ftype()]]}.

-type fun_def() :: #{ attrs  := [attribute()],
                      args   := [{var_name(), ftype()}],
                      return := ftype(),
                      body   := fexpr() }.

-type fcode() :: #{ contract_name := string(),
                    state_type    := ftype(),
                    event_type    := ftype() | none,
                    functions     := #{ fun_name() => fun_def() } }.

-type type_env() :: #{ sophia_name() => fun(([ftype()]) -> ftype()) }.
-type fun_env()  :: #{ sophia_name() => fun_name() }.

-type context() :: {main_contract, string()}
                 | {namespace, string()}
                 | {abstract_contract, string()}.

-type env() :: #{ type_env  := type_env(),
                  fun_env   := fun_env(),
                  options   := [option()],
                  context   => context(),
                  functions := #{ fun_name() => fun_def() } }.

%% -- Entrypoint -------------------------------------------------------------

%% Main entrypoint. Takes typed syntax produced by aeso_ast_infer_types:infer/1,2
%% and produces Fate intermediate code.
-spec ast_to_fcode(aeso_syntax:ast(), [option()]) -> fcode().
ast_to_fcode(Code, Options) ->
    to_fcode(init_env(Options), Code).

%% -- Environment ------------------------------------------------------------

-spec init_env([option()]) -> env().
init_env(Options) ->
    #{ type_env  => init_type_env(),
       fun_env   => #{},    %% TODO: builtin functions here?
       options   => Options,
       functions => #{} }.

-define(type(T),       fun([])     -> T end).
-define(type(X, T),    fun([X])    -> T end).
-define(type(X, Y, T), fun([X, Y]) -> T end).

-spec init_type_env() -> type_env().
init_type_env() ->
    #{ ["int"]          => ?type(integer),
       ["bool"]         => ?type(boolean),
       ["bits"]         => ?type(bits),
       ["string"]       => ?type(string),
       ["address"]      => ?type(address),
       ["hash"]         => ?type(hash),
       ["signature"]    => ?type(signature),
       ["oracle"]       => ?type(_, _, oracle),
       ["oracle_query"] => ?type(_, _, oracle_query),    %% TODO: not in Fate
       ["list"]         => ?type(T, {list, T}),
       ["map"]          => ?type(K, V, {map, K, V}),
       ["option"]       => ?type(T, {variant, [[], [T]]}),
       ["Chain", "ttl"] => ?type({variant, [[integer], [integer]]})
     }.

%% -- Compilation ------------------------------------------------------------

-spec to_fcode(env(), aeso_syntax:ast()) -> fcode().
to_fcode(Env, [{contract, _, {con, _, Main}, Decls}]) ->
    #{ functions := Funs } = Env1 =
        decls_to_fcode(Env#{ context => {main_contract, Main} }, Decls),
    StateType = lookup_type(Env1, [Main, "state"], [], {tuple, []}),
    EventType = lookup_type(Env1, [Main, "event"], [], none),
    #{ contract_name => Main,
       state_type    => StateType,
       event_type    => EventType,
       functions     => Funs };
to_fcode(Env, [{contract, _, {con, _, Con}, Decls} | Code]) ->
    Env1 = decls_to_fcode(Env#{ context => {abstract_contract, Con} }, Decls),
    to_fcode(Env1, Code);
to_fcode(Env, [{namespace, _, {con, _, Con}, Decls} | Code]) ->
    Env1 = decls_to_fcode(Env#{ context => {namespace, Con} }, Decls),
    to_fcode(Env1, Code).

-spec decls_to_fcode(env(), [aeso_syntax:decl()]) -> env().
decls_to_fcode(Env, Decls) ->
    %% First compute mapping from Sophia names to fun_names and add it to the
    %% environment.
    Env1 = add_fun_env(Env, Decls),
    lists:foldl(fun(D, E) ->
                    init_fresh_names(),
                    R = decl_to_fcode(E, D),
                    clear_fresh_names(),
                    R
                end, Env1, Decls).

-spec decl_to_fcode(env(), aeso_syntax:decl()) -> env().
decl_to_fcode(Env, {type_decl, _, _, _}) -> Env;
decl_to_fcode(Env, {fun_decl, _, _, _})  -> Env;
decl_to_fcode(Env, Decl = {type_def, _Ann, {id, _, _Name}, _Args, _Def}) ->
    error({todo, Decl}),
    Env;
decl_to_fcode(Env = #{ functions := Funs }, {letfun, Ann, {id, _, Name}, Args, Ret, Body}) ->
    Attrs = get_attributes(Ann),
    FName = lookup_fun(Env, qname(Env, Name)),
    FArgs = args_to_fcode(Env, Args),
    FBody = expr_to_fcode(Env, Body),
    %% io:format("Body of ~s:\n~s\n", [Name, format_fexpr(FBody)]),
    Def   = #{ attrs  => Attrs,
               args   => FArgs,
               return => type_to_fcode(Env, Ret),
               body   => FBody },
    NewFuns = Funs#{ FName => Def },
    Env#{ functions := NewFuns }.

-spec type_to_fcode(env(), aeso_syntax:type()) -> ftype().
type_to_fcode(Env, {app_t, _, T = {Id, _, _}, Types}) when Id == id; Id == qid ->
    lookup_type(Env, T, [type_to_fcode(Env, Type) || Type <- Types]);
type_to_fcode(Env, T = {Id, _, _}) when Id == id; Id == qid ->
    lookup_type(Env, T, []);
type_to_fcode(Env, {tuple_t, _, Types}) ->
    {tuple, [type_to_fcode(Env, T) || T <- Types]};
type_to_fcode(_Env, Type) ->
    error({todo, Type}).

-spec args_to_fcode(env(), [aeso_syntax:arg()]) -> [{var_name(), ftype()}].
args_to_fcode(Env, Args) ->
    [ {Name, type_to_fcode(Env, Type)} || {arg, _, {id, _, Name}, Type} <- Args ].

-spec expr_to_fcode(env(), aeso_syntax:expr()) -> fexpr().
expr_to_fcode(Env, {typed, _, Expr, Type}) ->
    expr_to_fcode(Env, type_to_fcode(Env, Type), Expr);
expr_to_fcode(Env, Expr) ->
    expr_to_fcode(Env, no_type, Expr).

-spec expr_to_fcode(env(), ftype() | no_type, aeso_syntax:expr()) -> fexpr().

%% Literals
expr_to_fcode(_Env, _Type, {int, _, N})  -> {int, N};
expr_to_fcode(_Env, _Type, {bool, _, B}) -> {bool, B};

%% Variables
expr_to_fcode(_Env, _Type, {id, _, X}) -> {var, X};

%% Tuples
expr_to_fcode(Env, _Type, {tuple, _, Es}) ->
    {tuple, [expr_to_fcode(Env, E) || E <- Es]};

%% Lists
expr_to_fcode(Env, Type, {list, _, Es}) ->
    lists:foldr(fun(E, L) -> {binop, Type, '::', expr_to_fcode(Env, E), L} end,
                nil, Es);

%% Conditionals
expr_to_fcode(Env, _Type, {'if', _, Cond, Then, Else}) ->
    Switch = fun(X) ->
                 {switch, {split, boolean, X,
                    [{'case', {bool, false}, {nosplit, expr_to_fcode(Env, Else)}},
                     {'case', {bool, true},  {nosplit, expr_to_fcode(Env, Then)}}]}}
             end,
    case Cond of
        {var, X} -> Switch(X);
        _        ->
            X = fresh_name(),
            {'let', X, expr_to_fcode(Env, Cond), Switch(X)}
    end;

%% Switch
expr_to_fcode(Env, _, {switch, _, Expr = {typed, _, E, Type}, Alts}) ->
    Switch = fun(X) ->
                {switch, alts_to_fcode(Env, type_to_fcode(Env, Type), X, Alts)}
             end,
    case E of
        {id, _, X} -> Switch(X);
        _ ->
            X = fresh_name(),
            {'let', X, expr_to_fcode(Env, Expr),
             Switch(X)}
    end;

%% Blocks
expr_to_fcode(Env, _Type, {block, _, Stmts}) ->
    stmts_to_fcode(Env, Stmts);

%% Binary operator
expr_to_fcode(Env, Type, {app, _Ann, {Op, _}, [A, B]}) when is_atom(Op) ->
    FOp = binop_to_fcode(Op),
    {binop, Type, FOp, expr_to_fcode(Env, A), expr_to_fcode(Env, B)};

expr_to_fcode(_Env, Type, Expr) ->
    {todo, {Expr, ':', Type}}.

binop_to_fcode(Op) when Op == '+'; Op == '-'; Op == '==' -> Op.

-spec alts_to_fcode(env(), ftype(), var_name(), [aeso_syntax:alt()]) -> fsplit().
alts_to_fcode(Env, Type, X, Alts) ->
    FAlts = [alt_to_fcode(Env, Alt) || Alt <- Alts],
    split_tree(Env, [{X, Type}], FAlts).

%% Intermediate format before case trees (fcase() and fsplit()).
-type falt() :: {'case', [fpat()], fexpr()}.
-type fpat() :: {var, var_name()}
              | {bool, false | true}
              | {int, integer()}
              | {tuple, [fpat()]}.

%% %% Invariant: the number of variables matches the number of patterns in each falt.
-spec split_tree(env(), [{var_name(), ftype()}], [falt()]) -> fsplit().
split_tree(_Env, _Vars, []) ->
    error(non_exhaustive_patterns); %% TODO: nice error
split_tree(Env, Vars, Alts = [{'case', Pats, Body} | _]) ->
    case next_split(Pats) of
        false ->
            Xs  = [ X || {X, _} <- Vars ],
            Ys  = [ Y || {var, Y} <- Pats ],
            Ren = [ {Y, X} || {Y, X} <- lists:zip(Ys, Xs), X /= Y, Y /= "_" ],
            %% TODO: Unreachable clauses error
            {nosplit, rename(Ren, Body)};
        I when is_integer(I) ->
            {Vars0, [{X, Type} | Vars1]} = lists:split(I - 1, Vars),
            SAlts = merge_alts(I, X, [ split_alt(I, A) || A <- Alts ]),
            Cases = [ {'case', SPat, split_tree(Env, Vars0 ++ split_vars(SPat, Type) ++ Vars1, FAlts)}
                      || {SPat, FAlts} <- SAlts ],
            {split, Type, X, Cases}
    end.

-spec merge_alts(integer(), var_name(), [{fsplit_pat(), falt()}]) -> [{fsplit_pat(), [falt()]}].
merge_alts(I, X, Alts) ->
    merge_alts(I, X, Alts, []).

merge_alts(I, X, Alts, Alts1) ->
    lists:foldr(fun(A, As) -> merge_alt(I, X, A, As) end,
                Alts1, Alts).

-spec merge_alt(integer(), var_name(), {fsplit_pat(), falt()}, Alts) -> Alts
        when Alts :: [{fsplit_pat(), [falt()]}].
merge_alt(_, _, {P, A}, []) -> [{P, [A]}];
merge_alt(I, X, {P, A}, [{Q, As} | Rest]) ->
    Match = fun({var, _}, {var, _})     -> match;
               ({tuple, _}, {tuple, _}) -> match;
               ({bool, B}, {bool, B})   -> match;
               ({int, N},  {int, N})    -> match;
               ({var, _}, _)            -> expand;
               (_, {var, _})            -> insert;
               (_, _)                   -> mismatch
            end,
    case Match(P, Q) of
        match    -> [{Q, [A | As]} | Rest];
        mismatch -> [{Q, As} | merge_alt(I, X, {P, A}, Rest)];
        expand   ->
            {Before, After} = expand(I, X, P, Q, A),
            merge_alts(I, X, Before, [{Q, As} | merge_alts(I, X, After, Rest)]);
        insert   -> [{P, [A]}, {Q, As} | Rest]
    end.

expand(I, X, P, Q, Case = {'case', Ps, E}) ->
    {Ps0, [{var, Y} | Ps1]} = lists:split(I - 1, Ps),
    {Ps0r, Ren1} = rename_pats([{Y, X} || Y /= X], Ps0),
    {Ps1r, Ren2} = rename_pats(Ren1, Ps1),
    E1 = rename(Ren2, E),
    Splice = fun(Qs) -> Ps0r ++ Qs ++ Ps1r end,
    case Q of
        {tuple, Xs} -> {[{Q,         {'case', Splice([{var, "_"} || _ <- Xs]), E1}}], []};
        {bool, _}   -> {[{{bool, B}, {'case', Splice([]), E1}} || B <- [false, true]], []};
        {int, _}    -> {[{Q,         {'case', Splice([]), E1}}], [{P, Case}]}
    end.

-spec split_alt(integer(), falt()) -> {fsplit_pat(), falt()}.
split_alt(I, {'case', Pats, Body}) ->
    {Pats0, [Pat | Pats1]} = lists:split(I - 1, Pats),
    {SPat, InnerPats} = split_pat(Pat),
    {SPat, {'case', Pats0 ++ InnerPats ++ Pats1, Body}}.

-spec split_pat(fpat()) -> {fsplit_pat(), [fpat()]}.
split_pat(P = {var, _})  -> {{var, fresh_name()}, [P]};
split_pat({bool, B})     -> {{bool, B}, []};
split_pat({int, N})      -> {{int, N}, []};
split_pat({tuple, Pats}) ->
    Xs = [fresh_name() || _ <- Pats],
    {{tuple, Xs}, Pats}.

-spec split_vars(fsplit_pat(), ftype()) -> [{var_name(), ftype()}].
split_vars({bool, _}, boolean) -> [];
split_vars({int, _},  integer) -> [];
split_vars({tuple, Xs}, {tuple, Ts}) ->
    lists:zip(Xs, Ts);
split_vars({var, X}, T) -> [{X, T}].

-spec rename([{var_name(), var_name()}], fexpr()) -> fexpr().
rename(Ren, Expr) ->
    case Expr of
        {int, _}               -> Expr;
        {bool, _}              -> Expr;
        nil                    -> nil;
        {var, X}               -> {var, rename_var(Ren, X)};
        {tuple, Es}            -> {tuple, [rename(Ren, E) || E <- Es]};
        {binop, T, Op, E1, E2} -> {binop, T, Op, rename(Ren, E1), rename(Ren, E2)};
        {'let', X, E, Body}    ->
            {Z, Ren1} = rename_binding(Ren, X),
            {'let', Z, rename(Ren, E), rename(Ren1, Body)};
        {switch, Split} -> {switch, rename_split(Ren, Split)}
    end.

rename_var(Ren, X) -> proplists:get_value(X, Ren, X).
rename_binding(Ren, X) ->
    Ren1 = lists:keydelete(X, 1, Ren),
    case lists:keymember(X, 2, Ren) of
        false -> {X, Ren1};
        true  ->
            Z = fresh_name(),
            {Z, [{X, Z} | Ren1]}
    end.

rename_bindings(Ren, []) -> {[], Ren};
rename_bindings(Ren, [X | Xs]) ->
    {Z, Ren1}  = rename_binding(Ren, X),
    {Zs, Ren2} = rename_bindings(Ren1, Xs),
    {[Z | Zs], Ren2}.

rename_pats(Ren, []) -> {[], Ren};
rename_pats(Ren, [P | Ps]) ->
    {Q, Ren1}  = rename_pat(Ren, P),
    {Qs, Ren2} = rename_pats(Ren1, Ps),
    {[Q | Qs], Ren2}.

rename_pat(Ren, P = {bool, _}) -> {P, Ren};
rename_pat(Ren, P = {int, _})  -> {P, Ren};
rename_pat(Ren, {var, X}) ->
    {Z, Ren1} = rename_binding(Ren, X),
    {{var, Z}, Ren1};
rename_pat(Ren, {tuple, Xs}) ->
    {Zs, Ren1} = rename_bindings(Ren, Xs),
    {{tuple, Zs}, Ren1}.

rename_split(Ren, {split, Type, X, Cases}) ->
    {split, Type, rename_var(Ren, X), [rename_case(Ren, C) || C <- Cases]};
rename_split(Ren, {nosplit, E}) -> {nosplit, rename(Ren, E)}.

rename_case(Ren, {'case', Pat, Split}) ->
    {Pat1, Ren1} = rename_pat(Ren, Pat),
    {'case', Pat1, rename_split(Ren1, Split)}.

-spec next_split([fpat()]) -> integer() | false.
next_split(Pats) ->
    IsVar = fun({var, _}) -> true; (_) -> false end,
    case [ I || {I, P} <- indexed(Pats), not IsVar(P) ] of
        []      -> false;
        [I | _] -> I
    end.

-spec alt_to_fcode(env(), aeso_syntax:alt()) -> falt().
alt_to_fcode(Env, {'case', _, Pat, Expr}) ->
    {'case', [pat_to_fcode(Env, Pat)], expr_to_fcode(Env, Expr)}.

-spec pat_to_fcode(env(), aeso_syntax:pat()) -> fpat().
pat_to_fcode(Env, {typed, _, Pat, Type}) ->
    pat_to_fcode(Env, type_to_fcode(Env, Type), Pat);
pat_to_fcode(Env, Pat) ->
    pat_to_fcode(Env, no_type, Pat).

-spec pat_to_fcode(env(), ftype() | no_type, aeso_syntax:pat()) -> fpat().
pat_to_fcode(_Env, _Type, {id, _, X}) -> {var, X};
pat_to_fcode(Env, _Type, {tuple, _, Pats}) ->
    {tuple, [ pat_to_fcode(Env, Pat) || Pat <- Pats ]};
pat_to_fcode(_Env, _Type, {bool, _, B}) ->
    {bool, B};
pat_to_fcode(_Env, _Type, {int, _, N}) ->
    {int, N};
pat_to_fcode(_Env, Type, Pat) -> {todo, Pat, ':', Type}.

-spec stmts_to_fcode(env(), [aeso_syntax:stmt()]) -> fexpr().
stmts_to_fcode(Env, [{letval, _, {typed, _, {id, _, X}, _}, _, Expr} | Stmts]) ->
    {'let', X, expr_to_fcode(Env, Expr), stmts_to_fcode(Env, Stmts)};

stmts_to_fcode(Env, [Expr]) ->
    expr_to_fcode(Env, Expr).

%% -- Optimisations ----------------------------------------------------------

%% - Translate && and || to ifte
%% - Deadcode elimination
%% - Unused variable analysis (replace by _)
%% - Simplified case trees (FATE has special instructions for shallow matching)
%% - Case specialization
%% - Constant propagation

%% -- Helper functions -------------------------------------------------------

%% -- Types --

-spec lookup_type(env(), aeso_syntax:id() | aeso_syntax:qid() | sophia_name(), [ftype()]) -> ftype().
lookup_type(Env, {id, _, Name}, Args) ->
    lookup_type(Env, [Name], Args);
lookup_type(Env, {qid, _, Name}, Args) ->
    lookup_type(Env, Name, Args);
lookup_type(Env, Name, Args) ->
    case lookup_type(Env, Name, Args, not_found) of
        not_found -> error({unknown_type, Name});
        Type      -> Type
    end.

-spec lookup_type(env(), sophia_name(), [ftype()], ftype() | A) -> ftype() | A.
lookup_type(#{ type_env := TypeEnv }, Name, Args, Default) ->
    case maps:get(Name, TypeEnv, false) of
        false -> Default;
        Fun   -> Fun(Args)
    end.

%% -- Names --

-spec add_fun_env(env(), [aeso_syntax:decl()]) -> env().
add_fun_env(#{ context := {abstract_contract, _} }, _) -> #{};  %% no functions from abstract contracts
add_fun_env(Env = #{ fun_env := FunEnv }, Decls) ->
    Entry = fun({letfun, Ann, {id, _, Name}, _, _, _}) ->
                [{qname(Env, Name), make_fun_name(Env, Ann, Name)}];
               (_) -> [] end,
    FunEnv1 = maps:from_list(lists:flatmap(Entry, Decls)),
    Env#{ fun_env := maps:merge(FunEnv, FunEnv1) }.

make_fun_name(#{ context := Context }, Ann, Name) ->
    Private = proplists:get_value(private, Ann, false) orelse
              proplists:get_value(internal, Ann, false),
    case Context of
        {main_contract, Main} ->
            if Private        -> {local_fun, [Main, Name]};
               Name == "init" -> init;
               true           -> {entrypoint, list_to_binary(Name)}
            end;
        {namespace, Lib} ->
            {local_fun, [Lib, Name]}
    end.

-spec current_namespace(env()) -> string().
current_namespace(#{ context := Cxt }) ->
    case Cxt of
        {abstract_contract, Con} -> Con;
        {main_contract, Con}     -> Con;
        {namespace, NS}          -> NS
    end.

-spec qname(env(), string()) -> sophia_name().
qname(Env, Name) ->
    [current_namespace(Env), Name].

-spec lookup_fun(env(), sophia_name()) -> fun_name().
lookup_fun(#{ fun_env := FunEnv }, Name) ->
    case maps:get(Name, FunEnv, false) of
        false -> error({unbound_name, Name});
        FName -> FName
    end.

init_fresh_names() ->
    put('%fresh', 0).

clear_fresh_names() ->
    erase('%fresh').

-spec fresh_name() -> var_name().
fresh_name() ->
    N = get('%fresh'),
    put('%fresh', N + 1),
    lists:concat(["%", N]).

%% -- Attributes --

get_attributes(Ann) ->
    [stateful || proplists:get_value(stateful, Ann, false)].

%% -- Basic utilities --

indexed(Xs) ->
    lists:zip(lists:seq(1, length(Xs)), Xs).

%% -- Pretty printing --------------------------------------------------------

format_fexpr(E) ->
    prettypr:format(pp_fexpr(E)).

pp_text(S) -> prettypr:text(lists:concat([S])).

pp_beside([])       -> prettypr:empty();
pp_beside([X])      -> X;
pp_beside([X | Xs]) -> pp_beside(X, pp_beside(Xs)).

pp_beside(A, B) -> prettypr:beside(A, B).

pp_above([])       -> prettypr:empty();
pp_above([X])      -> X;
pp_above([X | Xs]) -> pp_above(X, pp_above(Xs)).

pp_above(A, B) -> prettypr:above(A, B).

pp_parens(Doc) ->
    pp_beside([pp_text("("), Doc, pp_text(")")]).

pp_punctuate(_Sep, [])      -> [];
pp_punctuate(_Sep, [X])     -> [X];
pp_punctuate(Sep, [X | Xs]) -> [pp_beside(X, Sep) | pp_punctuate(Sep, Xs)].

pp_fexpr({int, N}) ->
    pp_text(N);
pp_fexpr({bool, B}) ->
    pp_text(B);
pp_fexpr(nil) ->
    pp_text("[]");
pp_fexpr({var, X}) ->
    pp_text(X);
pp_fexpr({tuple, Es}) ->
    pp_parens(prettypr:par(pp_punctuate(pp_text(","), [pp_fexpr(E) || E <- Es])));
pp_fexpr({binop, _Type, Op, A, B}) ->
    pp_parens(prettypr:par([pp_fexpr(A), pp_text(Op), pp_fexpr(B)]));
pp_fexpr({'let', X, A, B}) ->
    prettypr:par([pp_beside([pp_text("let "), pp_text(X), pp_text(" = "), pp_fexpr(A), pp_text(" in")]),
                  pp_fexpr(B)]);
pp_fexpr({switch, Split}) -> pp_split(Split).

pp_ftype(T) when is_atom(T) -> pp_text(T);
pp_ftype({tuple, Ts}) ->
    pp_parens(prettypr:par(pp_punctuate(pp_text(","), [pp_ftype(T) || T <- Ts])));
pp_ftype({list, T}) ->
    pp_beside([pp_text("list("), pp_ftype(T), pp_text(")")]).

pp_split({nosplit, E}) -> pp_fexpr(E);
pp_split({split, Type, X, Alts}) ->
    pp_above([pp_beside([pp_text("switch("), pp_text(X), pp_text(" : "), pp_ftype(Type), pp_text(")")])] ++
             [prettypr:nest(2, pp_case(Alt)) || Alt <- Alts]).

pp_case({'case', Pat, Split}) ->
    pp_above(pp_beside(pp_pat(Pat), pp_text(" =>")),
             prettypr:nest(2, pp_split(Split))).

pp_pat({tuple, Xs}) -> pp_fexpr({tuple, [{var, X} || X <- Xs]});
pp_pat(Pat) -> pp_fexpr(Pat).

