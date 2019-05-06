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

-type builtin() :: atom().

-type op() :: '+' | '-' | '*' | '/' | mod | '^' | '++' | '::' |
              '<' | '>' | '=<' | '>=' | '==' | '!=' | '!' |
              map_get | map_get_d | map_set | map_from_list | map_to_list |
              map_delete | map_member | map_size | string_length |
              string_concat | bits_set | bits_clear | bits_test | bits_sum |
              bits_intersection | bits_union | bits_difference.

-type fexpr() :: {int, integer()}
               | {string, binary()}
               | {account_pubkey, binary()}
               | {contract_pubkey, binary()}
               | {oracle_pubkey, binary()}
               | {oracle_query_id, binary()}
               | {bool, false | true}
               | nil
               | {var, var_name()}
               | {def, fun_name()}
               | {builtin, builtin(), non_neg_integer() | none} %% Unapplied builtin
               | {builtin, builtin(), [fexpr()]}
               | {con, arities(), tag(), [fexpr()]}
               | {tuple, [fexpr()]}
               | {proj, fexpr(), integer()}
               | {set_proj, fexpr(), integer(), fexpr()}    %% tuple, field, new_value
               | {op, op(), [fexpr()]}
               | {'let', var_name(), fexpr(), fexpr()}
               | {funcall, fexpr(), [fexpr()]}
               | {switch, fsplit()}.

-type fsplit() :: {split, ftype(), var_name(), [fcase()]}
                | {nosplit, fexpr()}.

-type fcase() :: {'case', fsplit_pat(), fsplit()}.

-type fsplit_pat()  :: {var, var_name()}
                     | {bool, false | true}
                     | {int, integer()}
                     | {string, binary()}
                     | nil
                     | {'::', var_name(), var_name()}
                     | {con, arities(), tag(), [var_name()]}
                     | {tuple, [var_name()]}.

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
               | {variant, [[ftype()]]}
               | any.

-type fun_def() :: #{ attrs  := [attribute()],
                      args   := [{var_name(), ftype()}],
                      return := ftype(),
                      body   := fexpr() }.

-type fcode() :: #{ contract_name := string(),
                    state_type    := ftype(),
                    event_type    := ftype() | none,
                    functions     := #{ fun_name() => fun_def() } }.

-type type_def() :: fun(([ftype()]) -> ftype()).

-type tag()     :: non_neg_integer().
-type arities() :: [non_neg_integer()].

-record(con_tag, { tag :: tag(), arities :: arities() }).
-type con_tag() :: #con_tag{}.

-type type_env() :: #{ sophia_name() => type_def() }.
-type fun_env()  :: #{ sophia_name() => fun_name() }.
-type con_env()  :: #{ sophia_name() => con_tag() }.
-type builtins() :: #{ sophia_name() => {builtin(), non_neg_integer() | none} }.

-type context() :: {main_contract, string()}
                 | {namespace, string()}
                 | {abstract_contract, string()}.

-type env() :: #{ type_env  := type_env(),
                  fun_env   := fun_env(),
                  con_env   := con_env(),
                  builtins  := builtins(),
                  options   := [option()],
                  context   => context(),
                  vars      => [var_name()],
                  functions := #{ fun_name() => fun_def() } }.

%% -- Entrypoint -------------------------------------------------------------

%% Main entrypoint. Takes typed syntax produced by aeso_ast_infer_types:infer/1,2
%% and produces Fate intermediate code.
-spec ast_to_fcode(aeso_syntax:ast(), [option()]) -> fcode().
ast_to_fcode(Code, Options) ->
    optimize_fcode(to_fcode(init_env(Options), Code)).

%% -- Environment ------------------------------------------------------------

-spec init_env([option()]) -> env().
init_env(Options) ->
    #{ type_env  => init_type_env(),
       fun_env   => #{},
       builtins  => builtins(),
       con_env   => #{["None"]        => #con_tag{ tag = 0, arities = [0, 1] },
                      ["Some"]        => #con_tag{ tag = 1, arities = [0, 1] },
                      ["RelativeTTL"] => #con_tag{ tag = 0, arities = [1, 1] },
                      ["FixedTTL"]    => #con_tag{ tag = 1, arities = [1, 1] }
                     },
       options   => Options,
       functions => #{} }.

-spec builtins() -> builtins().
builtins() ->
    MkName = fun(NS, Fun) ->
                list_to_atom(string:to_lower(string:join(NS ++ [Fun], "_")))
             end,
    Scopes = [{[],           [{"abort", 1}]},
              {["Chain"],    [{"spend", 2}, {"balance", 1}, {"block_hash", 1}, {"coinbase", none},
                              {"timestamp", none}, {"block_height", none}, {"difficulty", none},
                              {"gas_limit", none}]},
              {["Contract"], [{"address", none}, {"balance", none}]},
              {["Call"],     [{"origin", none}, {"caller", none}, {"value", none}, {"gas_price", none},
                              {"gas_left", 0}]},
              {["Oracle"],   [{"register", 4}, {"query_fee", 1}, {"query", 5}, {"get_question", 2},
                              {"respond", 4}, {"extend", 3}, {"get_answer", 2}]},
              {["AENS"],     [{"resolve", 2}, {"preclaim", 3}, {"claim", 4}, {"transfer", 4},
                              {"revoke", 3}]},
              {["Map"],      [{"from_list", 1}, {"to_list", 1}, {"lookup", 2},
                              {"lookup_default", 3}, {"delete", 2}, {"member", 2}, {"size", 1}]},
              {["Crypto"],   [{"ecverify", 3}, {"ecverify_secp256k1", 3}, {"sha3", 1},
                              {"sha256", 1}, {"blake2b", 1}]},
              {["Auth"],     [{"tx_hash", none}]},
              {["String"],   [{"length", 1}, {"concat", 2}, {"sha3", 1}, {"sha256", 1}, {"blake2b", 1}]},
              {["Bits"],     [{"set", 2}, {"clear", 2}, {"test", 2}, {"sum", 1}, {"intersection", 2},
                              {"union", 2}, {"difference", 2}, {"none", none}, {"all", none}]},
              {["Int"],      [{"to_str", 1}]},
              {["Address"],  [{"to_str", 1}]}
             ],
    maps:from_list([ {NS ++ [Fun], {MkName(NS, Fun), Arity}}
                     || {NS, Funs} <- Scopes,
                        {Fun, Arity} <- Funs ]).

-define(type(T),       fun([])     -> T end).
-define(type(X, T),    fun([X])    -> T end).
-define(type(X, Y, T), fun([X, Y]) -> T end).

-spec init_type_env() -> type_env().
init_type_env() ->
    #{ ["int"]          => ?type(integer),
       ["bool"]         => ?type(boolean),
       ["bits"]         => ?type(bits),
       ["char"]         => ?type(integer),
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
decl_to_fcode(Env, {type_def, _Ann, Name, Args, Def}) ->
    typedef_to_fcode(Env, Name, Args, Def);
decl_to_fcode(Env = #{ functions := Funs }, {letfun, Ann, {id, _, Name}, Args, Ret, Body}) ->
    Attrs = get_attributes(Ann),
    FName = lookup_fun(Env, qname(Env, Name)),
    FArgs = args_to_fcode(Env, Args),
    FBody = expr_to_fcode(Env#{ vars => [X || {X, _} <- FArgs] }, Body),
    %% io:format("Body of ~s:\n~s\n", [Name, format_fexpr(FBody)]),
    Def   = #{ attrs  => Attrs,
               args   => FArgs,
               return => type_to_fcode(Env, Ret),
               body   => FBody },
    NewFuns = Funs#{ FName => Def },
    Env#{ functions := NewFuns }.

-spec typedef_to_fcode(env(), aeso_syntax:id(), [aeso_syntax:tvar()], aeso_syntax:type_def()) -> env().
typedef_to_fcode(Env, {id, _, Name}, Xs, Def) ->
    Q = qname(Env, Name),
    FDef = fun(Args) ->
                Sub = maps:from_list(lists:zip([X || {tvar, _, X} <- Xs], Args)),
                case Def of
                    {record_t, Fields} -> {todo, Xs, Args, record_t, Fields};
                    {variant_t, Cons}  ->
                        FCons = [ begin
                                      {constr_t, _, _, Ts} = Con,
                                      [type_to_fcode(Env, Sub, T) || T <- Ts]
                                  end || Con <- Cons ],
                        {variant, FCons};
                    {alias_t, Type}    -> {todo, Xs, Args, alias_t, Type}
                end end,
    Constructors =
        case Def of
            {variant_t, Cons} ->
                Arities = [ begin
                                {constr_t, _, _, Args} = Con,
                                length(Args)
                            end || Con <- Cons ],
                Tags    = [ #con_tag{ tag = I, arities = Arities } || I <- lists:seq(0, length(Cons) - 1) ],
                GetName = fun({constr_t, _, {con, _, C}, _}) -> C end,
                QName   = fun(Con) -> qname(Env, GetName(Con)) end,
                maps:from_list([ {QName(Con), Tag} || {Tag, Con} <- lists:zip(Tags, Cons) ]);
            _ -> #{}
        end,
    Env1 = bind_constructors(Env, Constructors),
    bind_type(Env1, Q, FDef).

-spec type_to_fcode(env(), aeso_syntax:type()) -> ftype().
type_to_fcode(Env, Type) ->
    type_to_fcode(Env, #{}, Type).

-spec type_to_fcode(env(), #{var_name() => ftype()}, aeso_syntax:type()) -> ftype().
type_to_fcode(Env, Sub, {app_t, _, T = {Id, _, _}, Types}) when Id == id; Id == qid ->
    lookup_type(Env, T, [type_to_fcode(Env, Sub, Type) || Type <- Types]);
type_to_fcode(Env, _Sub, T = {Id, _, _}) when Id == id; Id == qid ->
    lookup_type(Env, T, []);
type_to_fcode(Env, Sub, {tuple_t, _, Types}) ->
    {tuple, [type_to_fcode(Env, Sub, T) || T <- Types]};
type_to_fcode(Env, Sub, {record_t, Fields}) ->
    FieldType = fun({field_t, _, _, Ty}) -> Ty end,
    type_to_fcode(Env, Sub, {tuple_t, [], lists:map(FieldType, Fields)});
type_to_fcode(_Env, _Sub, {bytes_t, _, _N}) ->
    string; %% TODO: add bytes type to FATE?
type_to_fcode(_Env, Sub, {tvar, _, X}) ->
    maps:get(X, Sub, any);
type_to_fcode(_Env, _Sub, Type) ->
    error({todo, Type}).

-spec args_to_fcode(env(), [aeso_syntax:arg()]) -> [{var_name(), ftype()}].
args_to_fcode(Env, Args) ->
    [ {Name, type_to_fcode(Env, Type)} || {arg, _, {id, _, Name}, Type} <- Args ].

-spec expr_to_fcode(env(), aeso_syntax:expr()) -> fexpr().
expr_to_fcode(Env, {typed, _, Expr, Type}) ->
    expr_to_fcode(Env, Type, Expr);
expr_to_fcode(Env, Expr) ->
    expr_to_fcode(Env, no_type, Expr).

-spec expr_to_fcode(env(), aeso_syntax:type() | no_type, aeso_syntax:expr()) -> fexpr().

%% Literals
expr_to_fcode(_Env, _Type, {int,             _, N}) -> {int, N};
expr_to_fcode(_Env, _Type, {char,            _, N}) -> {int, N};
expr_to_fcode(_Env, _Type, {bool,            _, B}) -> {bool, B};
expr_to_fcode(_Env, _Type, {string,          _, S}) -> {string, S};
expr_to_fcode(_Env, _Type, {account_pubkey,  _, K}) -> {account_pubkey, K};
expr_to_fcode(_Env, _Type, {contract_pubkey, _, K}) -> {contract_pubkey, K};
expr_to_fcode(_Env, _Type, {oracle_pubkey,   _, K}) -> {oracle_pubkey, K};
expr_to_fcode(_Env, _Type, {oracle_query_id, _, K}) -> {oracle_query_id, K};

expr_to_fcode(_Env, _Type, {bytes, _, Bin}) -> {string, Bin};

%% Variables
expr_to_fcode(Env, _Type, {id, _, X})  -> resolve_var(Env, [X]);
expr_to_fcode(Env, _Type, {qid, _, X}) -> resolve_var(Env, X);

%% Constructors
expr_to_fcode(Env, Type, {C, _, _} = Con) when C == con; C == qcon ->
    expr_to_fcode(Env, Type, {app, [], {typed, [], Con, Type}, []});
expr_to_fcode(Env, _Type, {app, _, {typed, _, {C, _, _} = Con, _}, Args}) when C == con; C == qcon ->
    #con_tag{ tag = I, arities = Arities } = lookup_con(Env, Con),
    Arity = lists:nth(I + 1, Arities),
    case length(Args) == Arity of
        true  -> {con, Arities, I, [expr_to_fcode(Env, Arg) || Arg <- Args]};
        false -> fcode_error({constructor_arity_mismatch, Con, length(Args), Arity})
    end;

%% Tuples
expr_to_fcode(Env, _Type, {tuple, _, Es}) ->
    {tuple, [expr_to_fcode(Env, E) || E <- Es]};

%% Records
expr_to_fcode(Env, _Type, {proj, _Ann, Rec, X}) ->
    {proj, expr_to_fcode(Env, Rec), field_index(Rec, X)};

expr_to_fcode(Env, {record_t, FieldTypes}, {record, _Ann, Fields}) ->
    FVal = fun(F) ->
             %% All fields are present and no updates
             {set, E} = field_value(F, Fields),
             expr_to_fcode(Env, E)
           end,
    {tuple, lists:map(FVal, FieldTypes)};

expr_to_fcode(Env, {record_t, FieldTypes}, {record, _Ann, Rec, Fields}) ->
    X    = fresh_name(),
    Proj = fun(I) -> {proj, {var, X}, I - 1} end,
    Comp = fun({I, false})       -> Proj(I);
              ({_, {set, E}})    -> expr_to_fcode(Env, E);
              ({I, {upd, Z, E}}) -> {'let', Z, Proj(I), expr_to_fcode(Env, E)}
           end,
    Set  = fun({_, false}, R)       -> R;
              ({I, {set, E}}, R)    -> {set_proj, R, I - 1, expr_to_fcode(Env, E)};
              ({I, {upd, Z, E}}, R) -> {set_proj, R, I - 1,
                                        {'let', Z, Proj(I), expr_to_fcode(bind_var(Env, Z), E)}}
           end,
    Expand  = length(Fields) == length(FieldTypes),
    Updates = [ {I, field_value(FT, Fields)} || {I, FT} <- indexed(FieldTypes) ],
    Body = case Expand of
             true  -> {tuple, lists:map(Comp, Updates)};
             false -> lists:foldr(Set, {var, X}, Updates)
           end,
    {'let', X, expr_to_fcode(Env, Rec), Body};

%% Lists
expr_to_fcode(Env, _Type, {list, _, Es}) ->
    lists:foldr(fun(E, L) -> {op, '::', [expr_to_fcode(Env, E), L]} end,
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
        _          ->
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
expr_to_fcode(Env, _Type, Expr = {app, _, {Op, _}, [_, _]}) when Op == '&&'; Op == '||' ->
    Tree = expr_to_decision_tree(Env, Expr),
    decision_tree_to_fcode(Tree);
expr_to_fcode(Env, _Type, {app, _Ann, {Op, _}, [A, B]}) when is_atom(Op) ->
    {op, Op, [expr_to_fcode(Env, A), expr_to_fcode(Env, B)]};
expr_to_fcode(Env, _Type, {app, _Ann, {Op, _}, [A]}) when is_atom(Op) ->
    case Op of
        '-' -> {op, '-', [{int, 0}, expr_to_fcode(Env, A)]};
        '!' -> {op, '!', [expr_to_fcode(Env, A)]}
    end;

%% Function calls
expr_to_fcode(Env, _Type, {app, _Ann, Fun = {typed, _, _, {fun_t, _, NamedArgsT, _, _}}, Args}) ->
    Args1 = get_named_args(NamedArgsT, Args),
    FArgs = [expr_to_fcode(Env, Arg) || Arg <- Args1],
    case expr_to_fcode(Env, Fun) of
        {builtin, B, Ar} when is_integer(Ar) ->
            case length(FArgs) of
                N when N == Ar -> builtin_to_fcode(B, FArgs);
                N when N < Ar  -> error({todo, eta_expand, B, FArgs})
            end;
        FFun -> {funcall, FFun, FArgs}
    end;

%% Maps
expr_to_fcode(_Env, _Type, {map, _, []}) ->
    {builtin, map_empty, none};
expr_to_fcode(Env, Type, {map, Ann, KVs}) ->
    %% Cheaper to do incremental map_update than building the list and doing
    %% map_from_list (I think).
    Fields = [{field, Ann, [{map_get, Ann, K}], V} || {K, V} <- KVs],
    expr_to_fcode(Env, Type, {map, Ann, {map, Ann, []}, Fields});
expr_to_fcode(Env, _Type, {map, _, Map, KVs}) ->
    X    = fresh_name(),
    Map1 = {var, X},
    {'let', X, expr_to_fcode(Env, Map),
        lists:foldr(fun(Fld, M) ->
                        case Fld of
                            {field, _, [{map_get, _, K}], V} ->
                                {op, map_set, [M, expr_to_fcode(Env, K), expr_to_fcode(Env, V)]};
                            {field_upd, _, [{map_get, _, K}], {typed, _, {lam, _, [{arg, _, {id, _, Z}, _}], V}, _}} ->
                                Y = fresh_name(),
                                {'let', Y, expr_to_fcode(Env, K),
                                {'let', Z, {op, map_get, [Map1, {var, Y}]},
                                {op, map_set, [M, {var, Y}, expr_to_fcode(bind_var(Env, Z), V)]}}}
                        end end, Map1, KVs)};
expr_to_fcode(Env, _Type, {map_get, _, Map, Key}) ->
    {op, map_get, [expr_to_fcode(Env, Map), expr_to_fcode(Env, Key)]};
expr_to_fcode(Env, _Type, {map_get, _, Map, Key, Def}) ->
    {op, map_get_d, [expr_to_fcode(Env, Map), expr_to_fcode(Env, Key), expr_to_fcode(Env, Def)]};

expr_to_fcode(_Env, Type, Expr) ->
    error({todo, {Expr, ':', Type}}).

%% -- Pattern matching --

-spec alts_to_fcode(env(), ftype(), var_name(), [aeso_syntax:alt()]) -> fsplit().
alts_to_fcode(Env, Type, X, Alts) ->
    FAlts = [alt_to_fcode(Env, Alt) || Alt <- Alts],
    split_tree(Env, [{X, Type}], FAlts).

%% Intermediate format before case trees (fcase() and fsplit()).
-type falt() :: {'case', [fpat()], fexpr()}.
-type fpat() :: {var, var_name()}
              | {bool, false | true}
              | {int, integer()}
              | {string, binary()}
              | nil | {'::', fpat(), fpat()}
              | {tuple, [fpat()]}
              | {con, arities(), tag(), [fpat()]}.

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
    Match = fun({var, _}, {var, _})             -> match;
               ({tuple, _}, {tuple, _})         -> match;
               ({bool, B}, {bool, B})           -> match;
               ({int, N},  {int, N})            -> match;
               ({string, S}, {string, S})       -> match;
               (nil,       nil)                 -> match;
               ({'::', _, _}, {'::', _, _})     -> match;
               ({con, _, C, _}, {con, _, C, _}) -> match;
               ({con, _, _, _}, {con, _, _, _}) -> mismatch;
               ({var, _}, _)                    -> expand;
               (_, {var, _})                    -> insert;
               (_, _)                           -> mismatch
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
    {Ps0r, Ren1} = rename_fpats([{Y, X} || Y /= X], Ps0),
    {Ps1r, Ren2} = rename_fpats(Ren1, Ps1),
    E1 = rename(Ren2, E),
    Splice = fun(N) -> Ps0r ++ lists:duplicate(N, {var, "_"}) ++ Ps1r end,
    Type = fun({tuple, Xs})     -> {tuple, length(Xs)};
              ({bool, _})       -> bool;
              ({int, _})        -> int;
              ({string, _})     -> string;
              (nil)             -> list;
              ({'::', _, _})    -> list;
              ({con, As, _, _}) -> {variant, As}
           end,
    MkCase = fun(Pat, Vars) -> {Pat, {'case', Splice(Vars), E1}} end,
    case Type(Q) of
        {tuple, N}    -> {[MkCase(Q, N)], []};
        bool          -> {[MkCase({bool, B}, 0) || B <- [false, true]], []};
        int           -> {[MkCase(Q, 0)], [{P, Case}]};
        string        -> {[MkCase(Q, 0)], [{P, Case}]};
        list          -> {[MkCase(nil, 0), MkCase({'::', fresh_name(), fresh_name()}, 2)], []};
        {variant, As} -> {[MkCase({con, As, C - 1, [fresh_name() || _ <- lists:seq(1, Ar)]}, Ar)
                           || {C, Ar} <- indexed(As)], []}
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
split_pat({string, N})   -> {{string, N}, []};
split_pat(nil) -> {nil, []};
split_pat({'::', P, Q}) -> {{'::', fresh_name(), fresh_name()}, [P, Q]};
split_pat({con, As, I, Pats}) ->
    Xs = [fresh_name() || _ <- Pats],
    {{con, As, I, Xs}, Pats};
split_pat({tuple, Pats}) ->
    Xs = [fresh_name() || _ <- Pats],
    {{tuple, Xs}, Pats}.

-spec split_vars(fsplit_pat(), ftype()) -> [{var_name(), ftype()}].
split_vars({bool, _},   boolean)     -> [];
split_vars({int, _},    integer)     -> [];
split_vars({string, _}, string)      -> [];
split_vars(nil,         {list, _})   -> [];
split_vars({'::', X, Xs}, {list, T}) -> [{X, T}, {Xs, {list, T}}];
split_vars({con, _, I, Xs}, {variant, Cons}) ->
    lists:zip(Xs, lists:nth(I + 1, Cons));
split_vars({tuple, Xs}, {tuple, Ts}) ->
    lists:zip(Xs, Ts);
split_vars({var, X}, T) -> [{X, T}].

-spec next_split([fpat()]) -> integer() | false.
next_split(Pats) ->
    IsVar = fun({var, _}) -> true; (_) -> false end,
    case [ I || {I, P} <- indexed(Pats), not IsVar(P) ] of
        []      -> false;
        [I | _] -> I
    end.

-spec alt_to_fcode(env(), aeso_syntax:alt()) -> falt().
alt_to_fcode(Env, {'case', _, Pat, Expr}) ->
    FPat  = pat_to_fcode(Env, Pat),
    FExpr = expr_to_fcode(bind_vars(Env, pat_vars(FPat)), Expr),
    {'case', [FPat], FExpr}.

-spec pat_to_fcode(env(), aeso_syntax:pat()) -> fpat().
pat_to_fcode(Env, {typed, _, Pat, Type}) ->
    pat_to_fcode(Env, Type, Pat);
pat_to_fcode(Env, Pat) ->
    pat_to_fcode(Env, no_type, Pat).

-spec pat_to_fcode(env(), aeso_syntax:type() | no_type, aeso_syntax:pat()) -> fpat().
pat_to_fcode(_Env, _Type, {id, _, X}) -> {var, X};
pat_to_fcode(Env, Type, {C, _, _} = Con) when C == con; C == qcon ->
    pat_to_fcode(Env, Type, {app, [], {typed, [], Con, Type}, []});
pat_to_fcode(Env, _Type, {app, _, {typed, _, {C, _, _} = Con, _}, Pats}) when C == con; C == qcon ->
    #con_tag{tag = I, arities = As} = lookup_con(Env, Con),
    {con, As, I, [pat_to_fcode(Env, Pat) || Pat <- Pats]};
pat_to_fcode(Env, _Type, {tuple, _, Pats}) ->
    {tuple, [ pat_to_fcode(Env, Pat) || Pat <- Pats ]};
pat_to_fcode(_Env, _Type, {bool, _, B})   -> {bool, B};
pat_to_fcode(_Env, _Type, {int, _, N})    -> {int, N};
pat_to_fcode(_Env, _Type, {char, _, N})   -> {int, N};
pat_to_fcode(_Env, _Type, {string, _, N}) -> {string, N};
pat_to_fcode(Env, _Type, {list, _, Ps}) ->
    lists:foldr(fun(P, Qs) ->
                    {'::', pat_to_fcode(Env, P), Qs}
                end, nil, Ps);
pat_to_fcode(Env, _Type, {app, _, {'::', _}, [P, Q]}) ->
    {'::', pat_to_fcode(Env, P), pat_to_fcode(Env, Q)};
pat_to_fcode(Env, {record_t, Fields}, {record, _, FieldPats}) ->
    FieldPat = fun(F) ->
                    case field_value(F, FieldPats) of
                        false      -> {id, [], "_"};
                        {set, Pat} -> Pat
                        %% {upd, _, _} is impossible in patterns
                    end end,
    {tuple, [pat_to_fcode(Env, FieldPat(Field))
             || Field <- Fields]};

pat_to_fcode(_Env, Type, Pat) ->
    error({todo, Pat, ':', Type}).

%% -- Decision trees for boolean operators --

decision_op('&&', {atom, A}, B) -> {'if', A, B, false};
decision_op('&&', false, _)     -> false;
decision_op('&&', true,  B)     -> B;
decision_op('||', {atom, A}, B) -> {'if', A, true, B};
decision_op('||', false, B)     -> B;
decision_op('||', true,  _)     -> true;
decision_op(Op, {'if', A, Then, Else}, B) ->
    {'if', A, decision_op(Op, Then, B), decision_op(Op, Else, B)}.

expr_to_decision_tree(Env, {app, _Ann, {Op, _}, [A, B]}) when Op == '&&'; Op == '||' ->
    decision_op(Op, expr_to_decision_tree(Env, A), expr_to_decision_tree(Env, B));
expr_to_decision_tree(Env, {typed, _, Expr, _}) -> expr_to_decision_tree(Env, Expr);
expr_to_decision_tree(Env, Expr) ->
    {atom, expr_to_fcode(Env, Expr)}.

decision_tree_to_fcode(false)     -> {bool, false};
decision_tree_to_fcode(true)      -> {bool, true};
decision_tree_to_fcode({atom, B}) -> B;
decision_tree_to_fcode({'if', A, Then, Else}) ->
    X = fresh_name(),
    {'let', X, A,
        {switch, {split, boolean, X, [{'case', {bool, false}, {nosplit, decision_tree_to_fcode(Else)}},
                                      {'case', {bool, true},  {nosplit, decision_tree_to_fcode(Then)}}]}}}.

%% -- Statements --

-spec stmts_to_fcode(env(), [aeso_syntax:stmt()]) -> fexpr().
stmts_to_fcode(Env, [{letval, _, {typed, _, {id, _, X}, _}, _, Expr} | Stmts]) ->
    {'let', X, expr_to_fcode(Env, Expr), stmts_to_fcode(bind_var(Env, X), Stmts)};

stmts_to_fcode(Env, [Expr]) ->
    expr_to_fcode(Env, Expr).

%% -- Builtins --

op_builtins() ->
    [map_from_list, map_to_list, map_delete, map_member, map_size,
     string_length, string_concat, string_sha3, string_sha256, string_blake2b,
     bits_set, bits_clear, bits_test, bits_sum, bits_intersection, bits_union,
     bits_difference, int_to_str, address_to_str].

builtin_to_fcode(map_lookup, [Key, Map]) ->
    {op, map_get, [Map, Key]};
builtin_to_fcode(map_lookup_default, [Key, Map, Def]) ->
    {op, map_get_d, [Map, Key, Def]};
builtin_to_fcode(Builtin, Args) ->
    case lists:member(Builtin, op_builtins()) of
        true  -> {op, Builtin, Args};
        false -> {builtin, Builtin, Args}
    end.

%% -- Optimisations ----------------------------------------------------------

%% - Deadcode elimination
%% - Unused variable analysis (replace by _)
%% - Case specialization
%% - Constant propagation
%% - Inlining

-spec optimize_fcode(fcode()) -> fcode().
optimize_fcode(Code = #{ functions := Funs }) ->
    Code#{ functions := maps:map(fun(Name, Def) -> optimize_fun(Code, Name, Def) end, Funs) }.

-spec optimize_fun(fcode(), fun_name(), fun_def()) -> fun_def().
optimize_fun(_Fcode, _Fun, Def = #{ body := _Body }) ->
    %% io:format("Optimizing ~p =\n~s\n", [_Fun, prettypr:format(pp_fexpr(_Body))]),
    Def.

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

-spec bind_type(env(), sophia_name(), type_def()) -> env().
bind_type(Env = #{type_env := TEnv}, Q, FDef) ->
    Env#{ type_env := TEnv#{ Q => FDef } }.

-spec bind_constructors(env(), con_env()) -> env().
bind_constructors(Env = #{ con_env := ConEnv }, NewCons) ->
    Env#{ con_env := maps:merge(ConEnv, NewCons) }.

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

-spec lookup_con(env(), aeso_syntax:con() | aeso_syntax:qcon() | sophia_name()) -> con_tag().
lookup_con(Env, {con, _, Con})  -> lookup_con(Env, [Con]);
lookup_con(Env, {qcon, _, Con}) -> lookup_con(Env, Con);
lookup_con(#{ con_env := ConEnv }, Con) ->
    case maps:get(Con, ConEnv, false) of
        false -> error({unbound_constructor, Con});
        Tag   -> Tag
    end.

bind_vars(Env, Xs) ->
    lists:foldl(fun(X, E) -> bind_var(E, X) end, Env, Xs).

bind_var(Env = #{ vars := Vars }, X) -> Env#{ vars := [X | Vars] }.

resolve_var(#{ vars := Vars } = Env, [X]) ->
    case lists:member(X, Vars) of
        true  -> {var, X};
        false -> resolve_fun(Env, [X])
    end;
resolve_var(Env, Q) -> resolve_fun(Env, Q).

resolve_fun(#{ fun_env := Funs, builtins := Builtin }, Q) ->
    case {maps:get(Q, Funs, not_found), maps:get(Q, Builtin, not_found)} of
        {not_found, not_found} -> fcode_error({unbound_variable, Q});
        {_, {B, Ar}}           -> {builtin, B, Ar};
        {Fun, _}               -> {def, Fun}
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

-spec pat_vars(fpat()) -> [var_name()].
pat_vars({var, X})            -> [X || X /= "_"];
pat_vars({bool, _})           -> [];
pat_vars({int, _})            -> [];
pat_vars({string, _})         -> [];
pat_vars(nil)                 -> [];
pat_vars({'::', P, Q})        -> pat_vars(P) ++ pat_vars(Q);
pat_vars({tuple, Ps})         -> pat_vars(Ps);
pat_vars({con, _, _, Ps})     -> pat_vars(Ps);
pat_vars(Ps) when is_list(Ps) -> [X || P <- Ps, X <- pat_vars(P)].

get_named_args(NamedArgsT, Args) ->
    IsNamed = fun({named_arg, _, _, _}) -> true;
                 (_) -> false end,
    {Named, NotNamed} = lists:partition(IsNamed, Args),
    NamedArgs = [get_named_arg(NamedArg, Named) || NamedArg <- NamedArgsT],
    NamedArgs ++ NotNamed.

get_named_arg({named_arg_t, _, {id, _, Name}, _, Default}, Args) ->
    case [ Val || {named_arg, _, {id, _, X}, Val} <- Args, X == Name ] of
        [Val] -> Val;
        []    -> Default
    end.

%% -- Renaming --

-spec rename([{var_name(), var_name()}], fexpr()) -> fexpr().
rename(Ren, Expr) ->
    case Expr of
        {int, _}             -> Expr;
        {string, _}          -> Expr;
        {bool, _}            -> Expr;
        {account_pubkey, _}  -> Expr;
        {contract_pubkey, _} -> Expr;
        {oracle_pubkey, _}   -> Expr;
        {oracle_query_id, _} -> Expr;
        nil                 -> nil;
        {var, X}            -> {var, rename_var(Ren, X)};
        {def, _}            -> Expr;
        {con, Ar, I, Es}    -> {con, Ar, I, [rename(Ren, E) || E <- Es]};
        {tuple, Es}         -> {tuple, [rename(Ren, E) || E <- Es]};
        {proj, E, I}        -> {proj, rename(Ren, E), I};
        {set_proj, R, I, E} -> {set_proj, rename(Ren, R), I, rename(Ren, E)};
        {op, Op, Es}        -> {op, Op, [rename(Ren, E) || E <- Es]};
        {funcall, Fun, Es}  -> {funcall, Fun, [rename(Ren, E) || E <- Es]};
        {'let', X, E, Body} ->
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

rename_fpats(Ren, []) -> {[], Ren};
rename_fpats(Ren, [P | Ps]) ->
    {Q, Ren1}  = rename_fpat(Ren, P),
    {Qs, Ren2} = rename_fpats(Ren1, Ps),
    {[Q | Qs], Ren2}.

rename_fpat(Ren, P = {bool, _})   -> {P, Ren};
rename_fpat(Ren, P = {int, _})    -> {P, Ren};
rename_fpat(Ren, P = {string, _}) -> {P, Ren};
rename_fpat(Ren, P = nil)         -> {P, Ren};
rename_fpat(Ren, {'::', P, Q})    ->
    {P1, Ren1} = rename_fpat(Ren, P),
    {Q1, Ren2} = rename_fpat(Ren1, Q),
    {{'::', P1, Q1}, Ren2};
rename_fpat(Ren, {var, X}) ->
    {Z, Ren1} = rename_binding(Ren, X),
    {{var, Z}, Ren1};
rename_fpat(Ren, {con, Ar, C, Ps}) ->
    {Ps1, Ren1} = rename_fpats(Ren, Ps),
    {{con, Ar, C, Ps1}, Ren1};
rename_fpat(Ren, {tuple, Ps}) ->
    {Ps1, Ren1} = rename_fpats(Ren, Ps),
    {{tuple, Ps1}, Ren1}.

rename_spat(Ren, P = {bool, _})   -> {P, Ren};
rename_spat(Ren, P = {int, _})    -> {P, Ren};
rename_spat(Ren, P = {string, _}) -> {P, Ren};
rename_spat(Ren, P = nil)         -> {P, Ren};
rename_spat(Ren, {'::', X, Y}) ->
    {X1, Ren1} = rename_binding(Ren, X),
    {Y1, Ren2} = rename_binding(Ren1, Y),
    {{'::', X1, Y1}, Ren2};
rename_spat(Ren, {var, X}) ->
    {Z, Ren1} = rename_binding(Ren, X),
    {{var, Z}, Ren1};
rename_spat(Ren, {con, Ar, C, Xs}) ->
    {Zs, Ren1} = rename_bindings(Ren, Xs),
    {{con, Ar, C, Zs}, Ren1};
rename_spat(Ren, {tuple, Xs}) ->
    {Zs, Ren1} = rename_bindings(Ren, Xs),
    {{tuple, Zs}, Ren1}.

rename_split(Ren, {split, Type, X, Cases}) ->
    {split, Type, rename_var(Ren, X), [rename_case(Ren, C) || C <- Cases]};
rename_split(Ren, {nosplit, E}) -> {nosplit, rename(Ren, E)}.

rename_case(Ren, {'case', Pat, Split}) ->
    {Pat1, Ren1} = rename_spat(Ren, Pat),
    {'case', Pat1, rename_split(Ren1, Split)}.

%% -- Records --

field_index({typed, _, _, RecTy}, X) ->
    field_index(RecTy, X);
field_index({record_t, Fields}, {id, _, X}) ->
    IsX = fun({field_t, _, {id, _, Y}, _}) -> X == Y end,
    [I] = [ I || {I, Field} <- indexed(Fields), IsX(Field) ],
    I - 1.  %% Tuples are 0-indexed

field_value({field_t, _, {id, _, X}, _}, Fields) ->
    View = fun({field, _, [{proj, _, {id, _, Y}}], E})    -> {Y, {set, E}};
              ({field_upd, _, [{proj, _, {id, _, Y}}],
                {typed, _, {lam, _, [{arg, _, {id, _, Z}, _}], E}, _}}) -> {Y, {upd, Z, E}} end,
    case [Upd || {Y, Upd} <- lists:map(View, Fields), X == Y] of
        [Upd] -> Upd;
        []    -> false
    end.

%% -- Attributes --

get_attributes(Ann) ->
    [stateful || proplists:get_value(stateful, Ann, false)].

%% -- Basic utilities --

indexed(Xs) ->
    lists:zip(lists:seq(1, length(Xs)), Xs).

fcode_error(Err) ->
    error(Err).

%% -- Pretty printing --------------------------------------------------------

format_fexpr(E) ->
    prettypr:format(pp_fexpr(E)).

pp_text(<<>>) -> prettypr:text("\"\"");
pp_text(Bin) when is_binary(Bin) -> prettypr:text(lists:flatten(io_lib:format("~p", [binary_to_list(Bin)])));
pp_text(S) -> prettypr:text(lists:concat([S])).

pp_beside([])       -> prettypr:empty();
pp_beside([X])      -> X;
pp_beside([X | Xs]) -> pp_beside(X, pp_beside(Xs)).

pp_beside(A, B) -> prettypr:beside(A, B).

pp_above([])       -> prettypr:empty();
pp_above([X])      -> X;
pp_above([X | Xs]) -> pp_above(X, pp_above(Xs)).

pp_above(A, B) -> prettypr:above(A, B).

pp_parens(Doc) -> pp_beside([pp_text("("), Doc, pp_text(")")]).
pp_braces(Doc) -> pp_beside([pp_text("{"), Doc, pp_text("}")]).

pp_punctuate(_Sep, [])      -> [];
pp_punctuate(_Sep, [X])     -> [X];
pp_punctuate(Sep, [X | Xs]) -> [pp_beside(X, Sep) | pp_punctuate(Sep, Xs)].

pp_par([]) -> prettypr:empty();
pp_par(Xs) -> prettypr:par(Xs).
pp_fexpr({Tag, Lit}) when Tag == int;
                          Tag == string;
                          Tag == bool;
                          Tag == account_pubkey;
                          Tag == contract_pubkey;
                          Tag == oracle_pubkey;
                          Tag == oracle_query_id ->
    aeso_pretty:expr({Tag, [], Lit});
pp_fexpr(nil) ->
    pp_text("[]");
pp_fexpr({var, X})               -> pp_text(X);
pp_fexpr({def, {entrypoint, E}}) -> pp_text(E);
pp_fexpr({def, {local_fun, Q}})  -> pp_text(string:join(Q, "."));
pp_fexpr({con, _, I, []}) ->
    pp_beside(pp_text("C"), pp_text(I));
pp_fexpr({con, _, I, Es}) ->
    pp_beside(pp_fexpr({con, [], I, []}),
              pp_fexpr({tuple, Es}));
pp_fexpr({tuple, Es}) ->
    pp_parens(pp_par(pp_punctuate(pp_text(","), [pp_fexpr(E) || E <- Es])));
pp_fexpr({proj, E, I}) ->
    pp_beside([pp_fexpr(E), pp_text("."), pp_text(I)]);
pp_fexpr({set_proj, E, I, A}) ->
    pp_beside(pp_fexpr(E), pp_braces(pp_beside([pp_text(I), pp_text(" = "), pp_fexpr(A)])));
pp_fexpr({op, Op, [A, B] = Args}) ->
    case is_infix(Op) of
        false -> pp_call(pp_text(Op), Args);
        true  -> pp_parens(pp_par([pp_fexpr(A), pp_text(Op), pp_fexpr(B)]))
    end;
pp_fexpr({op, Op, [A] = Args}) ->
    case is_infix(Op) of
        false -> pp_call(pp_text(Op), Args);
        true  -> pp_parens(pp_par([pp_text(Op), pp_fexpr(A)]))
    end;
pp_fexpr({op, Op, As}) ->
    pp_beside(pp_text(Op), pp_fexpr({tuple, As}));
pp_fexpr({'let', X, A, B}) ->
    pp_par([pp_beside([pp_text("let "), pp_text(X), pp_text(" = "), pp_fexpr(A), pp_text(" in")]),
            pp_fexpr(B)]);
pp_fexpr({builtin, B, none}) -> pp_text(B);
pp_fexpr({builtin, B, N}) when is_integer(N) ->
    pp_beside([pp_text(B), pp_text("/"), pp_text(N)]);
pp_fexpr({builtin, B, As}) when is_list(As) ->
    pp_call(pp_text(B), As);
pp_fexpr({funcall, Fun, As}) ->
    pp_call(pp_fexpr(Fun), As);
pp_fexpr({switch, Split}) -> pp_split(Split).

pp_call(Fun, Args) ->
    pp_beside(Fun, pp_fexpr({tuple, Args})).

pp_ftype(T) when is_atom(T) -> pp_text(T);
pp_ftype({tuple, Ts}) ->
    pp_parens(pp_par(pp_punctuate(pp_text(","), [pp_ftype(T) || T <- Ts])));
pp_ftype({list, T}) ->
    pp_beside([pp_text("list("), pp_ftype(T), pp_text(")")]);
pp_ftype({variant, Cons}) ->
    pp_par(
    pp_punctuate(pp_text(" |"),
                 [ case Args of
                     [] -> pp_fexpr({con, [], I - 1, []});
                     _  -> pp_beside(pp_fexpr({con, [], I - 1, []}), pp_ftype({tuple, Args}))
                   end || {I, Args} <- indexed(Cons)])).

pp_split({nosplit, E}) -> pp_fexpr(E);
pp_split({split, Type, X, Alts}) ->
    pp_above([pp_beside([pp_text("switch("), pp_text(X), pp_text(" : "), pp_ftype(Type), pp_text(")")])] ++
             [prettypr:nest(2, pp_case(Alt)) || Alt <- Alts]).

pp_case({'case', Pat, Split}) ->
    prettypr:sep([pp_beside(pp_pat(Pat), pp_text(" =>")),
                  prettypr:nest(2, pp_split(Split))]).

pp_pat({tuple, Xs})      -> pp_fexpr({tuple, [{var, X} || X <- Xs]});
pp_pat({'::', X, Xs})    -> pp_fexpr({op, '::', [{var, X}, {var, Xs}]});
pp_pat({con, As, I, Xs}) -> pp_fexpr({con, As, I, [{var, X} || X <- Xs]});
pp_pat({var, X})         -> pp_fexpr({var, X});
pp_pat(Pat)              -> pp_fexpr(Pat).

is_infix(Op) ->
    C = hd(atom_to_list(Op)),
    C < $a orelse C > $z.

