%%% File        : aeso_parser.erl
%%% Author      : Ulf Norell
%%% Description :
%%% Created     : 1 Mar 2018 by Ulf Norell
-module(aeso_parser).

-export([string/1,
         string/2,
         string/3,
         type/1]).

-include("aeso_parse_lib.hrl").

-type parse_result() :: {ok, aeso_syntax:ast()}
                      | {error, {aeso_parse_lib:pos(), atom(), term()}}
                      | {error, {aeso_parse_lib:pos(), atom()}}.

-spec string(string()) -> parse_result().
string(String) ->
    string(String, sets:new(), []).


-spec string(string(), compiler:options()) -> parse_result().
string(String, Opts) -> io:format("STRING WITH OPTS: ~p\n", [Opts]),
    case lists:keyfind(src_file, 1, Opts) of
        {src_file, File} -> string(String, sets:add_element(File, sets:new()), Opts);
        false -> string(String, sets:new(), Opts)
    end.

-spec string(string(), sets:set(string()), aeso_compiler:options()) -> parse_result().
string(String, Included, Opts) ->
    case parse_and_scan(file(), String, Opts) of
        {ok, AST} ->
            STD = case lists:member(no_implicit_stdlib, Opts) of
                      false -> [{ include, [{src_file, File}, {origin, system}]
                                , {string, [{src_file, File}, {origin, system}], File}}
                                || {File, _} <- aeso_stdlib:stdlib_list()
                               ];
                      true -> []
                  end,
            expand_includes(STD ++ AST, Included, Opts);
        Err = {error, _} ->
            Err
    end.

type(String) ->
    parse_and_scan(type(), String, []).

parse_and_scan(P, S, Opts) ->
    set_current_file(proplists:get_value(src_file, Opts, no_file)),
    case aeso_scan:scan(S) of
        {ok, Tokens} -> aeso_parse_lib:parse(P, Tokens);
        Error        -> Error
    end.

%% -- Parsing rules ----------------------------------------------------------

file() -> choice([], block(decl())).

decl() ->
    ?LAZY_P(
    choice(
      %% Contract declaration
    [ ?RULE(keyword(contract),  con(), tok('='), maybe_block(decl()), {contract, _1, _2, _4})
    , ?RULE(keyword(namespace), con(), tok('='), maybe_block(decl()), {namespace, _1, _2, _4})
    , ?RULE(keyword(include),   str(), {include, get_ann(_1), _2})

      %% Type declarations  TODO: format annotation for "type bla" vs "type bla()"
    , ?RULE(keyword(type),     id(),                                          {type_decl, _1, _2, []})
    , ?RULE(keyword(type),     id(), type_vars(),                             {type_decl, _1, _2, _3})
    , ?RULE(keyword(type),     id(),              tok('='), typedef(type),    {type_def, _1, _2, [], _4})
    , ?RULE(keyword(type),     id(), type_vars(), tok('='), typedef(type),    {type_def, _1, _2, _3, _5})
    , ?RULE(keyword(record),   id(),              tok('='), typedef(record),  {type_def, _1, _2, [], _4})
    , ?RULE(keyword(record),   id(), type_vars(), tok('='), typedef(record),  {type_def, _1, _2, _3, _5})
    , ?RULE(keyword(datatype), id(),              tok('='), typedef(variant), {type_def, _1, _2, [], _4})
    , ?RULE(keyword(datatype), id(), type_vars(), tok('='), typedef(variant), {type_def, _1, _2, _3, _5})

      %% Function declarations
    , ?RULE(modifiers(), fun_or_entry(), id(), tok(':'), type(), add_modifiers(_1, _2, {fun_decl, get_ann(_2), _3, _5}))
    , ?RULE(modifiers(), fun_or_entry(), fundef(),               add_modifiers(_1, _2, set_pos(get_pos(get_ann(_2)), _3)))
    , ?RULE(keyword('let'),    valdef(),                         set_pos(get_pos(_1), _2))
    ])).

fun_or_entry() ->
    choice([?RULE(keyword(function), {function, _1}),
            ?RULE(keyword(entrypoint), {entrypoint, _1})]).

modifiers() ->
    many(choice([token(stateful), token(private), token(public)])).

add_modifiers(Mods, Entry = {entrypoint, _}, Node) ->
    add_modifiers(Mods ++ [Entry], Node);
add_modifiers(Mods, {function, _}, Node) ->
    add_modifiers(Mods, Node).

add_modifiers([], Node) -> Node;
add_modifiers(Mods = [Tok | _], Node) ->
    %% Set the position to the position of the first modifier. This is
    %% important for code transformation tools (like what we do in
    %% create_calldata) to be able to get the indentation of the declaration.
    set_pos(get_pos(Tok),
        lists:foldl(fun({Mod, _}, X) -> set_ann(Mod, true, X) end,
                    Node, Mods)).

%% -- Type declarations ------------------------------------------------------

typedef(type)    -> ?RULE(type(),                   {alias_t, _1});
typedef(record)  -> ?RULE(brace_list(field_type()), {record_t, _1});
typedef(variant) -> ?RULE(constructors(),           {variant_t, _1}).

constructors() ->
    sep1(constructor(), tok('|')).

constructor() ->    %% TODO: format for Con() vs Con
    choice(?RULE(con(),             {constr_t, get_ann(_1), _1, []}),
           ?RULE(con(), con_args(), {constr_t, get_ann(_1), _1, _2})).

con_args()   -> paren_list(con_arg()).
type_args()  -> paren_list(type()).
field_type() -> ?RULE(id(), tok(':'), type(), {field_t, get_ann(_1), _1, _3}).

con_arg()    -> choice(type(), ?RULE(keyword(indexed), type(), set_ann(indexed, true, _2))).

%% -- Let declarations -------------------------------------------------------

letdecl() ->
    ?RULE(keyword('let'), letdef(), set_pos(get_pos(_1), _2)).

letdef() -> choice(valdef(), fundef()).

valdef() ->
    choice(
        ?RULE(id(),                   tok('='), body(), {letval, [], _1, type_wildcard(), _3}),
        ?RULE(id(), tok(':'), type(), tok('='), body(), {letval, [], _1, _3, _5})).

fundef() ->
    choice(
    [ ?RULE(id(), args(),                   tok('='), body(), {letfun, [], _1, _2, type_wildcard(), _4})
    , ?RULE(id(), args(), tok(':'), type(), tok('='), body(), {letfun, [], _1, _2, _4, _6})
    ]).

args() -> paren_list(arg()).

arg() -> choice(
    ?RULE(id(),                   {arg, get_ann(_1), _1, type_wildcard()}),
    ?RULE(id(), tok(':'), type(), {arg, get_ann(_1), _1, _3})).

%% -- Types ------------------------------------------------------------------

type_vars() -> paren_list(tvar()).

type() -> ?LAZY_P(type100()).

type100() -> type200().

type200() ->
    ?RULE(many({fun_domain(), keyword('=>')}), type300(), fun_t(_1, _2)).

type300() ->
    ?RULE(sep1(type400(), tok('*')), tuple_t(get_ann(lists:nth(1, _1)), _1)).

type400() ->
    choice(
    [?RULE(typeAtom(), optional(type_args()),
          case _2 of
            none       -> _1;
            {ok, Args} -> {app_t, get_ann(_1), _1, Args}
          end),
     ?RULE(id("bytes"), parens(token(int)),
           {bytes_t, get_ann(_1), element(3, _2)})
    ]).

typeAtom() ->
    ?LAZY_P(choice(
    [ parens(type())
    , id(), token(con), token(qcon), token(qid), tvar()
    ])).

fun_domain() -> ?LAZY_P(choice(
    [ ?RULE(tok('('), tok(')'), [])
      %% Note avoidance of ambiguity: `(int)` can be treated as:
      %% - literally `int`
      %% - list of arguments with just one element – int. This approach is dropped.
    , ?RULE(tok('('), type(), tok(','), sep1(type(), tok(',')), tok(')'), [_2|_4])
    , ?RULE(type300(), [_1])
    ])).

%% -- Statements -------------------------------------------------------------

body() ->
    ?LET_P(Stmts, maybe_block(stmt()), block_e(Stmts)).

stmt() ->
    ?LAZY_P(choice(
    [ expr()
    , letdecl()
    , {switch, keyword(switch), parens(expr()), maybe_block(branch())}
    , {'if', keyword('if'), parens(expr()), body()}
    , {elif, keyword(elif), parens(expr()), body()}
    , {else, keyword(else), body()}
    ])).

branch() ->
    ?RULE(pattern(), keyword('=>'), body(), {'case', _2, _1, _3}).

pattern() ->
    ?LET_P(E, expr500(), parse_pattern(E)).

%% -- Expressions ------------------------------------------------------------

expr() -> expr100().

expr100() ->
    Expr100 = ?LAZY_P(expr100()),
    Expr200 = ?LAZY_P(expr200()),
    choice(
    [ ?RULE(args(), keyword('=>'), body(), {lam, _2, _1, _3})   %% TODO: better location
    , {'if', keyword('if'), parens(Expr100), Expr200, right(tok(else), Expr100)}
    , ?RULE(Expr200, optional(right(tok(':'), type())),
            case _2 of
                none       -> _1;
                {ok, Type} -> {typed, get_ann(_1), _1, Type}
            end)
    ]).

expr200() -> infixr(expr300(), binop('||')).
expr300() -> infixr(expr400(), binop('&&')).
expr400() -> infix(expr500(),  binop(['<', '>', '=<', '>=', '==', '!='])).
expr500() -> infixr(expr600(), binop(['::', '++'])).
expr600() -> infixl(expr650(), binop(['+', '-'])).
expr650() -> ?RULE(many(token('-')), expr700(), prefixes(_1, _2)).
expr700() -> infixl(expr750(), binop(['*', '/', mod])).
expr750() -> infixl(expr800(), binop(['^'])).
expr800() -> ?RULE(many(token('!')), expr900(), prefixes(_1, _2)).
expr900() -> ?RULE(exprAtom(), many(elim()), elim(_1, _2)).

exprAtom() ->
    ?LAZY_P(begin
        Expr = ?LAZY_P(expr()),
        choice(
        [ id_or_addr(), con(), token(qid), token(qcon)
        , token(bytes), token(string), token(char)
        , token(int)
        , ?RULE(token(hex), set_ann(format, hex, setelement(1, _1, int)))
        , {bool, keyword(true), true}
        , {bool, keyword(false), false}
        , ?LET_P(Fs, brace_list(?LAZY_P(field_assignment())), record(Fs))
        , {list, [], bracket_list(Expr)}
        , ?RULE(keyword('['), Expr, token('|'), comma_sep(?LAZY_P(comprehension_bind())), tok(']'), list_comp_e(_1, _2, _4))
        , ?RULE(tok('['), Expr, binop('..'), Expr, tok(']'), _3(_2, _4))
        , ?RULE(keyword('('), comma_sep(Expr), tok(')'), tuple_e(_1, _2))
        ])
    end).

comprehension_bind() ->
    ?RULE(id(), tok('<-'), expr(), {comprehension_bind, _1, _3}).

arg_expr() ->
    ?LAZY_P(
        choice([ ?RULE(id(), tok('='), expr(), {named_arg, [], _1, _3})
               , expr() ])).

elim() ->
    ?LAZY_P(
    choice(
    [ {proj, keyword('.'), id()}
    , ?RULE(paren_list(arg_expr()), {app, [], _1})
    , ?RULE(keyword('{'), comma_sep(field_assignment()), tok('}'), {rec_upd, _1, _2})
    , ?RULE(keyword('['), map_key(), keyword(']'), map_get(_1, _2))
    ])).

map_get(Ann, {map_key, Key})      -> {map_get, Ann, Key};
map_get(Ann, {map_key, Key, Val}) -> {map_get, Ann, Key, Val}.

map_key() ->
    ?RULE(expr(), optional({tok('='), expr()}), map_key(_1, _2)).

map_key(Key, none)           -> {map_key, Key};
map_key(Key, {ok, {_, Val}}) -> {map_key, Key, Val}.

elim(E, [])                              -> E;
elim(E, [{proj, Ann, P} | Es])           -> elim({proj, Ann, E, P}, Es);
elim(E, [{app, Ann, Args} | Es])         -> elim({app, Ann, E, Args}, Es);
elim(E, [{rec_upd, Ann, Flds} | Es])     -> elim(record_update(Ann, E, Flds), Es);
elim(E, [{map_get, Ann, Key} | Es])      -> elim({map_get, Ann, E, Key}, Es);
elim(E, [{map_get, Ann, Key, Val} | Es]) -> elim({map_get, Ann, E, Key, Val}, Es).

record_update(Ann, E, Flds) ->
    {record_or_map(Flds), Ann, E, Flds}.

record([]) -> {map, [], []};
record(Fs) ->
    case record_or_map(Fs) of
        record ->
            Fld = fun({field, _, [_], _} = F) -> F;
                     ({field, Ann, LV, Id, _}) ->
                         bad_expr_err("Cannot use '@' in record construction", infix({lvalue, Ann, LV}, {'@', Ann}, Id));
                     ({field, Ann, LV, _}) ->
                         bad_expr_err("Cannot use nested fields or keys in record construction", {lvalue, Ann, LV}) end,
            {record, get_ann(hd(Fs)), lists:map(Fld, Fs)};
        map    ->
            Ann = get_ann(hd(Fs ++ [{empty, []}])), %% TODO: source location for empty maps
            KV = fun({field, _, [{map_get, _, Key}], Val}) -> {Key, Val};
                    ({field, FAnn, LV, Id, _}) ->
                        bad_expr_err("Cannot use '@' in map construction", infix({lvalue, FAnn, LV}, {'@', Ann}, Id));
                    ({field, FAnn, LV, _}) ->
                        bad_expr_err("Cannot use nested fields or keys in map construction", {lvalue, FAnn, LV}) end,
            {map, Ann, lists:map(KV, Fs)}
    end.

record_or_map(Fields) ->
    Kind = fun(Fld) -> case element(3, Fld) of
                [{proj, _, _}       | _] -> proj;
                [{map_get, _, _}    | _] -> map_get;
                [{map_get, _, _, _} | _] -> map_get
           end end,
    case lists:usort(lists:map(Kind, Fields)) of
        [proj]    -> record;
        [map_get] -> map;
        _         ->
            [{field, Ann, _, _} | _] = Fields,
            bad_expr_err("Mixed record fields and map keys in", {record, Ann, Fields})
    end.

field_assignment() ->
    ?RULE(lvalue(), optional({tok('@'), id()}), tok('='), expr(), field_assignment(get_ann(_3), _1, _2, _4)).

field_assignment(Ann, LV, none, E) ->
    {field, Ann, LV, E};
field_assignment(Ann, LV, {ok, {_, Id}}, E) ->
    {field, Ann, LV, Id, E}.

lvalue() ->
    ?RULE(lvalueAtom(), many(elim()), lvalue(elim(_1, _2))).

lvalueAtom() ->
    ?LAZY_P(choice([ id()
                   , ?RULE(keyword('['), map_key(), keyword(']'), _2)
                   ])).

lvalue(E) -> lvalue(E, []).

lvalue(X = {id, Ann, _}, LV)     -> [{proj, Ann, X} | LV];
lvalue({map_key, K}, LV)         -> [{map_get, get_ann(K), K} | LV];
lvalue({map_key, K, V}, LV)      -> [{map_get, get_ann(K), K, V} | LV];
lvalue({proj, Ann, E, P}, LV)    -> lvalue(E, [{proj, Ann, P} | LV]);
lvalue({map_get, Ann, E, K}, LV) -> lvalue(E, [{map_get, Ann, K} | LV]);
lvalue({map_get, Ann, E, K, V}, LV) -> lvalue(E, [{map_get, Ann, K, V} | LV]);
lvalue(E, _)                     -> bad_expr_err("Not a valid lvalue", E).

infix(E, Op) ->
    ?RULE(E, optional({Op, E}),
    case _2 of
        none -> _1;
        {ok, {F, Arg}} -> F(_1, Arg)
    end).

binop(Op) when is_atom(Op) -> binop([Op]);
binop(Ops) ->
    ?RULE(choice([ token(Op) || Op <- Ops ]), fun(A, B) -> infix(A, _1, B) end).

con()      -> token(con).
id()       -> token(id).
tvar()     -> token(tvar).
str()      -> token(string).

token(Tag) ->
    ?RULE(tok(Tag),
    case _1 of
        {Tok, {Line, Col}}      -> {Tok, pos_ann(Line, Col)};
        {Tok, {Line, Col}, Val} -> {Tok, pos_ann(Line, Col), Val}
    end).

id(Id) ->
    ?LET_P({id, A, X} = Y, id(),
           if X == Id -> Y;
              true    -> fail({A, "expected 'bytes'"})
           end).

id_or_addr() ->
    ?RULE(id(), parse_addr_literal(_1)).

parse_addr_literal(Id = {id, Ann, Name}) ->
    case lists:member(lists:sublist(Name, 3), ["ak_", "ok_", "oq_", "ct_"]) of
        false -> Id;
        true  ->
            try aeser_api_encoder:decode(list_to_binary(Name)) of
                {Type, Bin} -> {Type, Ann, Bin}
            catch _:_ ->
                Id
            end
    end.

%% -- Helpers ----------------------------------------------------------------

keyword(K) -> ann(tok(K)).
ann(P)     -> map(fun get_ann/1, P).

block(P) ->
    between(layout(), sep1(P, tok(vsemi)), tok(vclose)).

maybe_block(P) ->
    choice(block(P), [P]).

parens(P)   -> between(tok('('), P, tok(')')).
braces(P)   -> between(tok('{'), P, tok('}')).
brackets(P) -> between(tok('['), P, tok(']')).
comma_sep(P) -> sep(P, tok(',')).

paren_list(P)   -> parens(comma_sep(P)).
brace_list(P)   -> braces(comma_sep(P)).
bracket_list(P) -> brackets(comma_sep(P)).

%% -- Annotations ------------------------------------------------------------

-type ann()      :: aeso_syntax:ann().
-type ann_line() :: aeso_syntax:ann_line().
-type ann_col()  :: aeso_syntax:ann_col().

-spec pos_ann(ann_line(), ann_col()) -> ann().
pos_ann(Line, Col) -> [{file, current_file()}, {line, Line}, {col, Col}].

current_file() ->
    get('$current_file').

set_current_file(File) ->
    put('$current_file', File).

ann_pos(Ann) ->
    {proplists:get_value(file, Ann),
     proplists:get_value(line, Ann),
     proplists:get_value(col, Ann)}.

get_ann(Ann) when is_list(Ann) -> Ann;
get_ann(Node) ->
    case element(2, Node) of
        {Line, Col} when is_integer(Line), is_integer(Col) -> pos_ann(Line, Col);
        Ann -> Ann
    end.

get_ann(Key, Node) ->
    proplists:get_value(Key, get_ann(Node)).

set_ann(Key, Val, Node) ->
    Ann = get_ann(Node),
    setelement(2, Node, lists:keystore(Key, 1, Ann, {Key, Val})).

get_pos(Node) ->
    {current_file(), get_ann(line, Node), get_ann(col, Node)}.

set_pos({F, L, C}, Node) ->
    set_ann(file, F, set_ann(line, L, set_ann(col, C, Node))).

infix(L, Op, R) -> set_ann(format, infix,  {app, get_ann(L), Op, [L, R]}).

prefixes(Ops, E) -> lists:foldr(fun prefix/2, E, Ops).
prefix(Op, E)    -> set_ann(format, prefix, {app, get_ann(Op), Op, [E]}).

type_wildcard() ->
    {id, [{origin, system}], "_"}.

block_e(Stmts) ->
    group_ifs(Stmts, []).

group_ifs([], [Stmt]) -> return(Stmt);
group_ifs([], Acc) ->
    Stmts = [Stmt | _] = lists:reverse(Acc),
    {block, get_ann(Stmt), Stmts};
group_ifs([{'if', Ann, Cond, Then} | Stmts], Acc) ->
    {Elses, Rest} = else_branches(Stmts, []),
    group_ifs(Rest, [build_if(Ann, Cond, Then, Elses) | Acc]);
group_ifs([{else, Ann, _} | _], _) ->
    fail({Ann, "No matching 'if' for 'else'"});
group_ifs([{elif, Ann, _, _} | _], _) ->
    fail({Ann, "No matching 'if' for 'elif'"});
group_ifs([Stmt | Stmts], Acc) ->
    group_ifs(Stmts, [Stmt | Acc]).

build_if(Ann, Cond, Then, [{elif, Ann1, Cond1, Then1} | Elses]) ->
    {'if', Ann, Cond, Then,
        set_ann(format, elif, build_if(Ann1, Cond1, Then1, Elses))};
build_if(Ann, Cond, Then, [{else, _Ann, Else}]) ->
    {'if', Ann, Cond, Then, Else};
build_if(Ann, Cond, Then, []) ->
    {'if', Ann, Cond, Then, {tuple, [{origin, system}], []}}.

else_branches([Elif = {elif, _, _, _} | Stmts], Acc) ->
    else_branches(Stmts, [Elif | Acc]);
else_branches([Else = {else, _, _} | Stmts], Acc) ->
    {lists:reverse([Else | Acc]), Stmts};
else_branches(Stmts, Acc) ->
    {lists:reverse(Acc), Stmts}.

tuple_t(_Ann, [Type]) -> Type;  %% Not a tuple
tuple_t(Ann, Types)   -> {tuple_t, Ann, Types}.

fun_t(Domains, Type) ->
    lists:foldr(fun({Dom, Ann}, T) -> {fun_t, Ann, [], Dom, T} end,
                Type, Domains).

tuple_e(_Ann, [Expr]) -> Expr;  %% Not a tuple
tuple_e(Ann, Exprs)   -> {tuple, Ann, Exprs}.

list_comp_e(Ann, Expr, Binds) -> {list_comp, Ann, Expr, Binds}.

-spec parse_pattern(aeso_syntax:expr()) -> aeso_parse_lib:parser(aeso_syntax:pat()).
parse_pattern({app, Ann, Con = {'::', _}, Es}) ->
    {app, Ann, Con, lists:map(fun parse_pattern/1, Es)};
parse_pattern({app, Ann, Con = {con, _, _}, Es}) ->
    {app, Ann, Con, lists:map(fun parse_pattern/1, Es)};
parse_pattern({tuple, Ann, Es}) ->
    {tuple, Ann, lists:map(fun parse_pattern/1, Es)};
parse_pattern({list, Ann, Es}) ->
    {list, Ann, lists:map(fun parse_pattern/1, Es)};
parse_pattern({record, Ann, Fs}) ->
    {record, Ann, lists:map(fun parse_field_pattern/1, Fs)};
parse_pattern(E = {con, _, _})    -> E;
parse_pattern(E = {id, _, _})     -> E;
parse_pattern(E = {int, _, _})    -> E;
parse_pattern(E = {bool, _, _})   -> E;
parse_pattern(E = {bytes, _, _})  -> E;
parse_pattern(E = {string, _, _}) -> E;
parse_pattern(E = {char, _, _})   -> E;
parse_pattern(E) -> bad_expr_err("Not a valid pattern", E).

-spec parse_field_pattern(aeso_syntax:field(aeso_syntax:expr())) -> aeso_parse_lib:parser(aeso_syntax:field(aeso_syntax:pat())).
parse_field_pattern({field, Ann, F, E}) ->
    {field, Ann, F, parse_pattern(E)}.

return_error({no_file, L, C}, Err) ->
    fail(io_lib:format("~p:~p:\n~s", [L, C, Err]));
return_error({F, L, C}, Err) ->
    fail(io_lib:format("In ~s at ~p:~p:\n~s", [F, L, C, Err])).

-spec ret_doc_err(ann(), prettypr:document()) -> aeso_parse_lib:parser(none()).
ret_doc_err(Ann, Doc) ->
    return_error(ann_pos(Ann), prettypr:format(Doc)).

-spec bad_expr_err(string(), aeso_syntax:expr()) -> aeso_parse_lib:parser(none()).
bad_expr_err(Reason, E) ->
  ret_doc_err(get_ann(E),
              prettypr:sep([prettypr:text(Reason ++ ":"),
                            prettypr:nest(2, aeso_pretty:expr(E))])).

%% -- Helper functions -------------------------------------------------------
expand_includes(AST, Included, Opts) ->
    expand_includes(AST, Included, [], Opts).

expand_includes([], _Included, Acc, _Opts) ->
    {ok, lists:reverse(Acc)};
expand_includes([{include, Ann, S = {string, _, File}} | AST], Included, Acc, Opts) ->
    case sets:is_element(File, Included) of
        false ->
            Opts1 = lists:keystore(src_file, 1, Opts, {src_file, File}),
            Included1 = sets:add_element(File, Included),
            case {read_file(File, Opts), maps:find(File, aeso_stdlib:stdlib())} of
                {{ok, _}, {ok,_ }} ->
                    return_error(ann_pos(Ann), "Illegal redefinition of standard library " ++ File);
                {_, {ok, Lib}} ->
                    case string(Lib, Included1, [no_implicit_stdlib, Opts1]) of
                        {ok, AST1} ->
                            expand_includes(AST1 ++ AST, Included1, Acc, Opts);
                        Err = {error, _} ->
                            Err
                    end;
                {{ok, Bin}, _} ->
                    case string(binary_to_list(Bin), Included1, Opts1) of
                        {ok, AST1} ->
                            expand_includes(AST1 ++ AST, Included1, Acc, Opts);
                        Err = {error, _} ->
                            Err
                    end;
                {_, _} ->
                    {error, {get_pos(S), include_error, File}}
            end;
        true -> expand_includes(AST, Included, Acc, Opts)
    end;
expand_includes([E | AST], Included, Acc, Opts) ->
    expand_includes(AST, Included, [E | Acc], Opts).

read_file(File, Opts) ->
    case proplists:get_value(include, Opts, {explicit_files, #{}}) of
        {file_system, Paths} ->
            CandidateNames = [ filename:join(Dir, File) || Dir <- Paths ],
            lists:foldr(fun(F, {error, _}) -> file:read_file(F);
                           (_F, OK) -> OK end, {error, not_found}, CandidateNames);
        {explicit_files, Files} ->
            case maps:get(binary_to_list(File), Files, not_found) of
                not_found -> {error, not_found};
                Src       -> {ok, Src}
            end
    end.

