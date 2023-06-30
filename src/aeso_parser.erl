%%% File        : aeso_parser.erl
%%% Author      : Ulf Norell
%%% Description :
%%% Created     : 1 Mar 2018 by Ulf Norell
-module(aeso_parser).
-compile({no_auto_import,[map_get/2]}).

-export([string/1,
         string/2,
         string/3,
         auto_imports/1,
         hash_include/2,
         decl/0,
         type/0,
         body/0,
         maybe_block/1,
         run_parser/2,
         run_parser/3]).

-include("aeso_parse_lib.hrl").
-import(aeso_parse_lib, [current_file/0, set_current_file/1,
                         current_dir/0, set_current_dir/1,
                         current_include_type/0, set_current_include_type/1]).

-type parse_result() :: aeso_syntax:ast() | {aeso_syntax:ast(), sets:set(include_hash())} | none().

-type include_hash() :: {string(), binary()}.


escape_errors({ok, Ok}) ->
    Ok;
escape_errors({error, Err}) ->
    parse_error(Err).

-spec string(string()) -> parse_result().
string(String) ->
    string(String, sets:new(), []).

-spec string(string(), aeso_compiler:options()) -> parse_result().
string(String, Opts) ->
    case lists:keyfind(src_file, 1, Opts) of
        {src_file, File} -> string(String, sets:add_element(File, sets:new()), Opts);
        false -> string(String, sets:new(), Opts)
    end.

-spec string(string(), sets:set(include_hash()), aeso_compiler:options()) -> parse_result().
string(String, Included, Opts) ->
    AST = run_parser(file(), String, Opts),
    case expand_includes(AST, Included, Opts) of
        {ok, AST1}   -> AST1;
        {error, Err} -> parse_error(Err)
    end.


run_parser(P, Inp) ->
    escape_errors(parse_and_scan(P, Inp, [])).
run_parser(P, Inp, Opts) ->
    escape_errors(parse_and_scan(P, Inp, Opts)).

parse_and_scan(P, S, Opts) ->
    set_current_file(proplists:get_value(src_file, Opts, no_file)),
    set_current_dir(proplists:get_value(src_dir, Opts, no_file)),
    set_current_include_type(proplists:get_value(include_type, Opts, none)),
    case aeso_scan:scan(S) of
        {ok, Tokens} -> aeso_parse_lib:parse(P, Tokens);
        {error, {{Input, Pos}, _}} ->
            {error, {Pos, scan_error, Input}}
    end.

-dialyzer({nowarn_function, parse_error/1}).
parse_error(Err) ->
    aeso_errors:throw(mk_error(Err)).

mk_p_err(Pos, Msg) ->
    aeso_errors:new(parse_error, mk_pos(Pos), lists:flatten(Msg)).

mk_error({Pos, scan_error, Input}) ->
    mk_p_err(Pos, io_lib:format("Lexical error on input: ~s\n", [Input]));
mk_error({Pos, parse_error, Err}) ->
    Msg = io_lib:format("~s\n", [Err]),
    mk_p_err(Pos, Msg);
mk_error({Pos, ambiguous_parse, As}) ->
    Msg = io_lib:format("Ambiguous parse result: ~p\n", [As]),
    mk_p_err(Pos, Msg);
mk_error({Pos, include_error, File}) ->
    Msg = io_lib:format("Couldn't find include file '~s'\n", [File]),
    mk_p_err(Pos, Msg).

mk_pos({Line, Col})       -> aeso_errors:pos(Line, Col);
mk_pos({File, Line, Col}) -> aeso_errors:pos(File, Line, Col).

%% -- Parsing rules ----------------------------------------------------------

file() -> choice([], block(decl())).

decl() ->
    ?LAZY_P(
    choice(
      %% Contract declaration
    [ ?RULE(token(main), keyword(contract),
            con(), tok('='), maybe_block(decl()), {contract_main, _2, _3, [], _5})
    , ?RULE(token(main), keyword(contract),
            con(), tok(':'), comma_sep(con()), tok('='), maybe_block(decl()), {contract_main, _2, _3, _5, _7})
    , ?RULE(keyword(contract),
            con(), tok('='), maybe_block(decl()), {contract_child, _1, _2, [], _4})
    , ?RULE(keyword(contract),
            con(), tok(':'), comma_sep(con()), tok('='), maybe_block(decl()), {contract_child, _1, _2, _4, _6})
    , ?RULE(keyword(contract), token(interface),
            con(), tok('='), maybe_block(decl()), {contract_interface, _1, _3, [], _5})
    , ?RULE(keyword(contract), token(interface),
            con(), tok(':'), comma_sep(con()), tok('='), maybe_block(decl()), {contract_interface, _1, _3, _5, _7})
    , ?RULE(token(payable), token(main), keyword(contract),
            con(), tok('='), maybe_block(decl()), add_modifiers([_1], {contract_main, _3, _4, [], _6}))
    , ?RULE(token(payable), token(main), keyword(contract),
            con(), tok(':'), comma_sep(con()), tok('='), maybe_block(decl()), add_modifiers([_1], {contract_main, _3, _4, _6, _8}))
    , ?RULE(token(payable), keyword(contract),
            con(), tok('='), maybe_block(decl()), add_modifiers([_1], {contract_child, _2, _3, [], _5}))
    , ?RULE(token(payable), keyword(contract),
            con(), tok(':'), comma_sep(con()), tok('='), maybe_block(decl()), add_modifiers([_1], {contract_child, _2, _3, _5, _7}))
    , ?RULE(token(payable), keyword(contract), token(interface),
            con(), tok('='), maybe_block(decl()), add_modifiers([_1], {contract_interface, _2, _4, [], _6}))
    , ?RULE(token(payable), keyword(contract), token(interface),
            con(), tok(':'), comma_sep(con()), tok('='), maybe_block(decl()), add_modifiers([_1], {contract_interface, _2, _4, _6, _8}))


    , ?RULE(keyword(namespace), con(), tok('='), maybe_block(decl()), {namespace, _1, _2, _4})
    , ?RULE(keyword(include),   str(), {include, get_ann(_1), _2})
    , using()
    , pragma()

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
    , ?RULE(modifiers(), fun_or_entry(), maybe_block(fundef_or_decl()), fun_block(_1, _2, _3))
    , ?RULE(keyword('let'), valdef(), set_pos(get_pos(_1), _2))
    ])).

fun_block(Mods, Kind, [Decl]) ->
    add_modifiers(Mods, Kind, set_pos(get_pos(Kind), Decl));
fun_block(Mods, Kind, Decls) ->
    {block, get_ann(Kind), [ add_modifiers(Mods, Kind, Decl) || Decl <- Decls ]}.

fundef_or_decl() ->
    choice([?RULE(id(), tok(':'), type(), {fun_decl, get_ann(_1), _1, _3}),
            fundef()]).

using() ->
    Alias = {keyword(as), con()},
    For = ?RULE(keyword(for), bracket_list(id()), {for, _2}),
    Hiding = ?RULE(keyword(hiding), bracket_list(id()), {hiding, _2}),
    ?RULE(keyword(using), con(), optional(Alias), optional(choice(For, Hiding)), using(get_ann(_1), _2, _3, _4)).

using(Ann, Con, none, none) ->
    {using, Ann, Con, none, none};
using(Ann, Con, {ok, {_, Alias}}, none) ->
    {using, Ann, Con, Alias, none};
using(Ann, Con, none, {ok, List}) ->
    {using, Ann, Con, none, List};
using(Ann, Con, {ok, {_, Alias}}, {ok, List}) ->
    {using, Ann, Con, Alias, List}.

pragma() ->
    Op = choice([token(T) || T <- ['<', '=<', '==', '>=', '>']]),
    ?RULE(tok('@'), id("compiler"), Op, version(), {pragma, get_ann(_1), {compiler, element(1, _3), _4}}).

version() ->
    ?RULE(token(int), many({tok('.'), token(int)}), mk_version(_1, _2)).

mk_version({int, _, Maj}, Rest) ->
    [Maj | [N || {_, {int, _, N}} <- Rest]].

fun_or_entry() ->
    choice([?RULE(keyword(function),   {function,   _1}),
            ?RULE(keyword(entrypoint), {entrypoint, _1})]).

modifiers() ->
    many(choice([token(stateful), token(payable), token(private), token(public)])).

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
    ?RULE(pattern(), tok('='), body(), {letval, [], _1, _3}).

guarded_fundefs() ->
    choice(
    [ ?RULE(keyword('='), body(), [{guarded, _1, [], _2}])
    , maybe_block(?RULE(keyword('|'), comma_sep(expr()), tok('='), body(), {guarded, _1, _2, _4}))
    ]).

fundef() ->
    choice(
    [ ?RULE(id(), args(),                   guarded_fundefs(), {letfun, get_ann(_1), _1, _2, type_wildcard(get_ann(_1)), _3})
    , ?RULE(id(), args(), tok(':'), type(), guarded_fundefs(), {letfun, get_ann(_1), _1, _2, _4, _5})
    ]).

args() -> paren_list(pattern()).
lam_args() -> paren_list(arg()).

arg() -> choice(
    ?RULE(id(),                   {arg, get_ann(_1), _1, type_wildcard(get_ann(_1))}),
    ?RULE(id(), tok(':'), type(), {arg, get_ann(_1), _1, _3})).

letpat() ->
    ?RULE(keyword('('), id(), tok('='), pattern(), tok(')'), {letpat, get_ann(_1), _2, _4}).

%% -- Types ------------------------------------------------------------------

type_vars() -> paren_list(tvar()).

type() -> ?LAZY_P(type100()).

type100() -> type200().

type200() ->
    ?RULE(many({type300(), keyword('=>')}), type300(), fun_t(_1, _2)).

type300() ->
    ?RULE(sep1(type400(), tok('*')), tuple_t(get_ann(lists:nth(1, _1)), _1)).

type400() ->
    choice(
    [?RULE(typeAtom(), optional(type_args()),
          any_bytes(
            case _2 of
              none       -> _1;
              {ok, Args} -> {app_t, get_ann(_1), _1, Args}
            end)),
     ?RULE(id("bytes"), parens(token(int)),
           {bytes_t, get_ann(_1), element(3, _2)})
    ]).

typeAtom() ->
    ?LAZY_P(choice(
    [ parens(type())
    , args_t()
    , id(), token(con), token(qcon), token(qid), tvar()
    ])).

args_t() ->
    ?LAZY_P(choice(
    [ ?RULE(tok('('), tok(')'), {args_t, get_ann(_1), []})
      %% Singleton case handled separately
    , ?RULE(tok('('), type(), tok(','), sep1(type(), tok(',')), tok(')'), {args_t, get_ann(_1), [_2|_4]})
    ])).

%% -- Statements -------------------------------------------------------------

body() ->
    ?LET_P(Stmts, maybe_block(stmt()), block_e(Stmts)).

stmt() ->
    ?LAZY_P(choice(
    [ using()
    , expr()
    , letdecl()
    , {switch, keyword(switch), parens(expr()), maybe_block(branch())}
    , {'if', keyword('if'), parens(expr()), body()}
    , {elif, keyword(elif), parens(expr()), body()}
    , {else, keyword(else), body()}
    ])).

branch() ->
    ?RULE(pattern(), guarded_branches(), {'case', get_ann(lists:nth(1, _2)), _1, _2}).

guarded_branches() ->
    choice(
    [ ?RULE(keyword('=>'), body(), [{guarded, _1, [], _2}])
    , maybe_block(?RULE(tok('|'), comma_sep(expr()), keyword('=>'), body(), {guarded, _3, _2, _4}))
    ]).

pattern() ->
    ?LET_P(E, expr(), parse_pattern(E)).

%% -- Expressions ------------------------------------------------------------

expr() -> expr100().

expr100() ->
    Expr100 = ?LAZY_P(expr100()),
    Expr150 = ?LAZY_P(expr150()),
    choice(
    [ ?RULE(lam_args(), keyword('=>'), body(), {lam, _2, _1, _3})   %% TODO: better location
    , {'if', keyword('if'), parens(Expr100), Expr150, right(tok(else), Expr100)}
    , ?RULE(Expr150, optional(right(tok(':'), type())),
            case _2 of
                none       -> _1;
                {ok, Type} -> {typed, get_ann(_1), _1, Type}
            end)
    ]).

expr150() -> infixl(expr200(), binop('|>')).
expr200() -> infixr(expr300(), binop('||')).
expr300() -> infixr(expr325(), binop('&&')).
expr325() -> infixl(expr350(), binop('bor')).
expr350() -> infixl(expr375(), binop('bxor')).
expr375() -> infixl(expr400(), binop('band')).
expr400() -> infix(expr500(),  binop(['<', '>', '=<', '>=', '==', '!='])).
expr500() -> infixr(expr550(), binop(['::', '++'])).
expr550() -> infixl(expr600(), binop(['<<', '>>'])).
expr600() -> infixl(expr650(), binop(['+', '-'])).
expr650() -> ?RULE(many(token('-')), expr700(), prefixes(_1, _2)).
expr700() -> infixl(expr750(), binop(['*', '/', mod])).
expr750() -> infixl(expr800(), binop(['^'])).
expr800() -> ?RULE(many(token('!')), expr850(), prefixes(_1, _2)).
expr850() -> ?RULE(many(token('bnot')), expr900(), prefixes(_1, _2)).
expr900() -> ?RULE(exprAtom(), many(elim()), elim(_1, _2)).

exprAtom() ->
    ?LAZY_P(begin
        Expr = ?LAZY_P(expr()),
        choice(
        [ id_or_addr(), con(), token(qid), token(qcon), binop_as_lam()
        , token(bytes), token(string), token(char)
        , token(int)
        , ?RULE(token(hex), set_ann(format, hex, setelement(1, _1, int)))
        , {bool, keyword(true), true}
        , {bool, keyword(false), false}
        , ?LET_P(Fs, brace_list(?LAZY_P(field_assignment())), record(Fs))
        , {list, [], bracket_list(Expr)}
        , ?RULE(keyword('['), Expr, token('|'), comma_sep(comprehension_exp()), tok(']'), list_comp_e(_1, _2, _4))
        , ?RULE(tok('['), Expr, binop('..'), Expr, tok(']'), _3(_2, _4))
        , ?RULE(keyword('('), comma_sep(Expr), tok(')'), tuple_e(_1, _2))
        , letpat()
        , hole()
        ])
    end).

hole() -> ?RULE(token('???'), {id, get_ann(_1), "???"}).

comprehension_exp() ->
    ?LAZY_P(choice(
      [ comprehension_bind()
      , letdecl()
      , comprehension_if()
      ])).

comprehension_if() ->
    ?RULE(keyword('if'), parens(expr()), {comprehension_if, _1, _2}).

comprehension_bind() ->
    ?RULE(pattern(), tok('<-'), expr(), {comprehension_bind, _1, _3}).

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
elim(E, [{app, _Ann, Args} | Es])        -> elim({app, aeso_syntax:get_ann(E), E, Args}, Es);
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
            {map, Ann, lists:map(KV, Fs)};
        record_or_map_error ->
            {record_or_map_error, get_ann(hd(Fs)), Fs}
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
        _         -> record_or_map_error %% Defer error until type checking
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

binop_as_lam() ->
    BinOps = ['&&', '||',
              '+', '-', '*', '/', '^', 'mod',
              '==', '!=', '<', '>', '<=', '=<', '>=',
              '::', '++', '|>'],
    OpToLam = fun(Op = {_, Ann}) ->
                  IdL = {id, Ann, "l"},
                  IdR = {id, Ann, "r"},
                  Arg = fun(Id) -> {arg, Ann, Id, type_wildcard(Ann)} end,
                  {lam, Ann, [Arg(IdL), Arg(IdR)], infix(IdL, Op, IdR)}
              end,
    ?RULE(parens(choice(lists:map(fun token/1, BinOps))), OpToLam(_1)).

token(Tag) ->
    ?RULE(tok(Tag),
    case _1 of
        {Tok, {Line, Col}}      -> {Tok, pos_ann(Line, Col)};
        {Tok, {Line, Col}, Val} -> {Tok, pos_ann(Line, Col), Val}
    end).

id(Id) ->
    ?LET_P({id, A, X} = Y, id(),
           if X == Id -> Y;
              true    -> fail({A, "expected '" ++ Id ++ "'"})
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
pos_ann(Line, Col) ->
    [ {file, current_file()}
    , {dir, current_dir()}
    , {include_type, current_include_type()}
    , {line, Line}
    , {col, Col} ].

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

type_wildcard(Ann) ->
    {id, [{origin, system} | Ann], "_"}.

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
    lists:foldr(fun({{args_t, _, Dom}, Ann}, T) -> {fun_t, Ann, [], Dom, T};
                    ({Dom, Ann}, T)             -> {fun_t, Ann, [], [Dom], T} end,
                Type, Domains).

tuple_e(_Ann, [Expr]) -> Expr;  %% Not a tuple
tuple_e(Ann, Exprs)   -> {tuple, Ann, Exprs}.

list_comp_e(Ann, Expr, Binds) -> {list_comp, Ann, Expr, Binds}.

-spec parse_pattern(aeso_syntax:expr()) -> aeso_parse_lib:parser(aeso_syntax:pat()).
parse_pattern({letpat, Ann, Id, Pat}) ->
    {letpat, Ann, Id, parse_pattern(Pat)};
parse_pattern({app, Ann, Con = {'::', _}, Es}) ->
    {app, Ann, Con, lists:map(fun parse_pattern/1, Es)};
parse_pattern({app, Ann, {'-', _}, [{int, _, N}]}) ->
    {int, Ann, -N};
parse_pattern({app, Ann, Con = {Tag, _, _}, Es}) when Tag == con; Tag == qcon ->
    {app, Ann, Con, lists:map(fun parse_pattern/1, Es)};
parse_pattern({tuple, Ann, Es}) ->
    {tuple, Ann, lists:map(fun parse_pattern/1, Es)};
parse_pattern({list, Ann, Es}) ->
    {list, Ann, lists:map(fun parse_pattern/1, Es)};
parse_pattern({record, Ann, Fs}) ->
    {record, Ann, lists:map(fun parse_field_pattern/1, Fs)};
parse_pattern({typed, Ann, E, Type}) ->
    {typed, Ann, parse_pattern(E), Type};
parse_pattern(E = {con, _, _})    -> E;
parse_pattern(E = {qcon, _, _})   -> E;
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

-spec ret_doc_err(ann(), prettypr:document()) -> aeso_parse_lib:parser(none()).
ret_doc_err(Ann, Doc) ->
    fail(ann_pos(Ann), prettypr:format(Doc)).

-spec bad_expr_err(string(), aeso_syntax:expr()) -> aeso_parse_lib:parser(none()).
bad_expr_err(Reason, E) ->
  ret_doc_err(get_ann(E),
              prettypr:sep([prettypr:text(Reason ++ ":"),
                            prettypr:nest(2, aeso_pretty:expr(E))])).

%% -- Helper functions -------------------------------------------------------

expand_includes(AST, Included, Opts) ->
    Ann  = [{origin, system}],
    AST1 = [ {include, Ann, {string, Ann, File}}
             || File <- lists:usort(auto_imports(AST)) ] ++ AST,
    expand_includes(AST1, Included, [], Opts).

expand_includes([], Included, Acc, Opts) ->
    case lists:member(keep_included, Opts) of
        false ->
            {ok, lists:reverse(Acc)};
        true ->
            {ok, {lists:reverse(Acc), Included}}
    end;
expand_includes([{include, Ann, {string, _SAnn, File}} | AST], Included, Acc, Opts) ->
    case get_include_code(File, Ann, Opts) of
        {ok, AbsDir, Code} ->
            Hashed = hash_include(File, Code),
            case sets:is_element(Hashed, Included) of
                false ->
                    SrcFile = proplists:get_value(src_file, Opts, no_file),
                    IncludeType = case proplists:get_value(file, Ann) of
                                      SrcFile -> direct;
                                      _       -> indirect
                                  end,
                    Opts1 = lists:keystore(src_file, 1, Opts, {src_file, File}),
                    Opts2 = lists:keystore(src_dir, 1, Opts1, {src_dir, AbsDir}),
                    Opts3 = lists:keystore(include_type, 1, Opts2, {include_type, IncludeType}),
                    Included1 = sets:add_element(Hashed, Included),
                    case parse_and_scan(file(), Code, Opts3) of
                        {ok, AST1} ->
                            expand_includes(AST1 ++ AST, Included1, Acc, Opts);
                        Err = {error, _} ->
                            Err
                    end;
                true ->
                    expand_includes(AST, Included, Acc, Opts)
            end;
        Err = {error, _} ->
            Err
    end;
expand_includes([E | AST], Included, Acc, Opts) ->
    expand_includes(AST, Included, [E | Acc], Opts).

read_file(File, Opts) ->
    case proplists:get_value(include, Opts, {explicit_files, #{}}) of
        {file_system, Paths} ->
            lists:foldr(fun(Path, {error, _}) -> read_file_(Path, File);
                           (_Path, OK)        -> OK end, {error, not_found}, Paths);
        {explicit_files, Files} ->
            case maps:get(binary_to_list(File), Files, not_found) of
                not_found -> {error, not_found};
                Src       -> {ok, File, Src}
            end;
        escript ->
            try
                Escript        = escript:script_name(),
                {ok, Sections} = escript:extract(Escript, []),
                Archive        = proplists:get_value(archive, Sections),
                FileName       = binary_to_list(filename:join([aesophia, priv, stdlib, File])),
                case zip:extract(Archive, [{file_list, [FileName]}, memory]) of
                    {ok, [{_, Src}]} -> {ok, escript, Src};
                    _                -> {error, not_found}
                end
            catch _:_ ->
                {error, not_found}
            end
    end.

read_file_(Path, File) ->
    AbsFile = filename:join(Path, File),
    case file:read_file(AbsFile) of
        {ok, Bin} -> {ok, aeso_utils:canonical_dir(filename:dirname(AbsFile)), Bin};
        Err       -> Err
    end.

stdlib_options() ->
    StdLibDir = aeso_stdlib:stdlib_include_path(),
    case filelib:is_dir(StdLibDir) of
        true  -> [{include, {file_system, [StdLibDir]}}];
        false -> [{include, escript}]
    end.

get_include_code(File, Ann, Opts) ->
    %% Temporarily extend include paths with the directory of the current file
    Opts1 = include_current_file_dir(Opts, Ann),
    case {read_file(File, Opts1), read_file(File, stdlib_options())} of
        {{ok, Dir, Bin}, {ok, _}} ->
            case filename:basename(File) == File of
                true -> { error
                        , fail( ann_pos(Ann)
                              , "Illegal redefinition of standard library " ++ binary_to_list(File))};
                %% If a path is provided then the stdlib takes lower priority
                false -> {ok, Dir, binary_to_list(Bin)}
            end;
        {_, {ok, _, Bin}} ->
            {ok, stdlib, binary_to_list(Bin)};
        {{ok, Dir, Bin}, _} ->
            {ok, Dir, binary_to_list(Bin)};
        {_, _} ->
            {error, {ann_pos(Ann), include_error, File}}
    end.

include_current_file_dir(Opts, Ann) ->
    case {proplists:get_value(dir, Ann, undefined),
          proplists:get_value(include, Opts, undefined)} of
        {undefined, _} -> Opts;
        {CurrDir, {file_system, Paths}} ->
            case lists:member(CurrDir, Paths) of
                false -> [{include, {file_system, [CurrDir | Paths]}} | Opts];
                true  -> Opts
            end;
        {_, _} -> Opts
    end.

-spec hash_include(string() | binary(), string()) -> include_hash().
hash_include(File, Code) when is_binary(File) ->
    hash_include(binary_to_list(File), Code);
hash_include(File, Code) when is_list(File) ->
    {filename:basename(File), crypto:hash(sha256, Code)}.

auto_imports({comprehension_bind, _, _}) -> [<<"ListInternal.aes">>];
auto_imports({'..', _})                  -> [<<"ListInternal.aes">>];
auto_imports(L) when is_list(L) ->
    lists:flatmap(fun auto_imports/1, L);
auto_imports(T) when is_tuple(T) ->
    auto_imports(tuple_to_list(T));
auto_imports(_) -> [].

any_bytes({id, Ann, "bytes"})                 -> {bytes_t, Ann, any};
any_bytes({app_t, _, {id, Ann, "bytes"}, []}) -> {bytes_t, Ann, any};
any_bytes(Type)                               -> Type.
