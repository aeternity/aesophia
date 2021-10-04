%%%-------------------------------------------------------------------
%%% @author Robert Virding
%%% @copyright (C) 2019, Aeternity Anstalt
%%% @doc
%%%     ACI interface
%%% @end
%%% Created : 12 Jan 2019
%%%-------------------------------------------------------------------

-module(aeso_aci).

-export([ file/2
        , file/3
        , contract_interface/2
        , contract_interface/3

        , from_typed_ast/2

        , render_aci_json/1

        , json_encode_expr/1
        , json_encode_type/1]).

-include("aeso_utils.hrl").

-type aci_type()  :: json | string.
-type json()      :: jsx:json_term().
-type json_text() :: binary().

-export_type([aci_type/0]).

%% External API
-spec file(aci_type(), string()) -> {ok, json() | string()} | {error, term()}.
file(Type, File) ->
    file(Type, File, []).

file(Type, File, Options0) ->
    Options = aeso_compiler:add_include_path(File, Options0),
    case file:read_file(File) of
        {ok, BinCode} ->
            do_contract_interface(Type, binary_to_list(BinCode), Options);
        {error, _} = Err -> Err
    end.

-spec contract_interface(aci_type(), string()) ->
    {ok, json() | string()} | {error, term()}.
contract_interface(Type, ContractString) ->
    contract_interface(Type, ContractString, []).

-spec contract_interface(aci_type(), string(), [term()]) ->
    {ok, json() | string()} | {error, term()}.
contract_interface(Type, ContractString, CompilerOpts) ->
    do_contract_interface(Type, ContractString, CompilerOpts).

-spec render_aci_json(json() | json_text()) -> {ok, binary()}.
render_aci_json(Json) ->
    do_render_aci_json(Json).

-spec json_encode_expr(aeso_syntax:expr()) -> json().
json_encode_expr(Expr) ->
    encode_expr(Expr).

-spec json_encode_type(aeso_syntax:type()) -> json().
json_encode_type(Type) ->
    encode_type(Type).

%% Internal functions
do_contract_interface(Type, Contract, Options) when is_binary(Contract) ->
    do_contract_interface(Type, binary_to_list(Contract), Options);
do_contract_interface(Type, ContractString, Options) ->
    try
        Ast = aeso_compiler:parse(ContractString, Options),
        {TypedAst, _} = aeso_ast_infer_types:infer(Ast, [dont_unfold | Options]),
        from_typed_ast(Type, TypedAst)
    catch
        throw:{error, Errors} -> {error, Errors}
    end.

from_typed_ast(Type, TypedAst) ->
    JArray = [ encode_contract(C) || C <- TypedAst ],
    case Type of
        json   -> {ok, JArray};
        string -> do_render_aci_json(JArray)
    end.

encode_contract(Contract = {Head, _, {con, _, Name}, _}) when ?IS_CONTRACT_HEAD(Head) ->
    C0 = #{name => encode_name(Name)},

    Tdefs0 = [ encode_typedef(T) || T <- sort_decls(contract_types(Contract)) ],
    FilterT = fun(N) -> fun(#{name := N1}) -> N == N1 end end,
    {Es, Tdefs1} = lists:partition(FilterT(<<"event">>), Tdefs0),
    {Ss, Tdefs}  = lists:partition(FilterT(<<"state">>), Tdefs1),

    C1 = C0#{type_defs => Tdefs},

    C2 = case Es of
             []                 -> C1;
             [#{typedef := ET}] -> C1#{event => ET}
         end,

    C3 = case Ss of
             []                 -> C2;
             [#{typedef := ST}] -> C2#{state => ST}
         end,

    Fdefs  = [ encode_function(F)
               || F <- sort_decls(contract_funcs(Contract)),
                  is_entrypoint(F) ],

    #{contract => C3#{kind => Head, functions => Fdefs, payable => is_payable(Contract)}};
encode_contract(Namespace = {namespace, _, {con, _, Name}, _}) ->
    Tdefs = [ encode_typedef(T) || T <- sort_decls(contract_types(Namespace)) ],
    #{namespace => #{name => encode_name(Name),
                     type_defs => Tdefs}}.

%%  Encode a function definition. Currently we are only interested in
%%  the interface and type.
encode_function(FDef = {letfun, _, {id, _, Name}, Args, Type, _, _}) ->
    #{name      => encode_name(Name),
      arguments => encode_args(Args),
      returns   => encode_type(Type),
      stateful  => is_stateful(FDef),
      payable   => is_payable(FDef)};
encode_function(FDecl = {fun_decl, _, {id, _, Name}, {fun_t, _, _, Args, Type}}) ->
    #{name      => encode_name(Name),
      arguments => encode_anon_args(Args),
      returns   => encode_type(Type),
      stateful  => is_stateful(FDecl),
      payable   => is_payable(FDecl)}.

encode_anon_args(Types) ->
    Anons = [ list_to_binary("_" ++ integer_to_list(X)) || X <- lists:seq(1, length(Types))],
    [ #{name => V, type => encode_type(T)}
      || {V, T} <- lists:zip(Anons, Types) ].

encode_args(Args) -> [ encode_arg(A) || A <- Args ].

encode_arg({typed, _, Id, T}) ->
    #{name => encode_type(Id),
      type => encode_type(T)}.

encode_typedef(Type) ->
    Name = typedef_name(Type),
    Vars = typedef_vars(Type),
    Def  = typedef_def(Type),
    #{name    => encode_name(Name),
      vars    => encode_tvars(Vars),
      typedef => encode_type(Def)}.

encode_tvars(Vars) ->
    [ #{name => encode_type(V)} || V <- Vars ].

%% Encode type
encode_type({tvar, _, N})         -> encode_name(N);
encode_type({id, _, N})           -> encode_name(N);
encode_type({con, _, N})          -> encode_name(N);
encode_type({qid, _, Ns})         -> encode_name(lists:join(".", Ns));
encode_type({qcon, _, Ns})        -> encode_name(lists:join(".", Ns));
encode_type({tuple_t, _, As})     -> #{tuple => encode_types(As)};
encode_type({bytes_t, _, Len})    -> #{bytes => Len};
encode_type({record_t, Fs})       -> #{record => encode_type_fields(Fs)};
encode_type({app_t, _, Id, Fs})   -> #{encode_type(Id) => encode_types(Fs)};
encode_type({variant_t, Cs})      -> #{variant => encode_types(Cs)};
encode_type({constr_t, _, C, As}) -> #{encode_type(C) => encode_types(As)};
encode_type({alias_t, Type})      -> encode_type(Type);
encode_type({fun_t, _, _, As, T}) -> #{function =>
                                         #{arguments => encode_types(As),
                                           returns => encode_type(T)}}.

encode_types(Ts) -> [ encode_type(T) || T <- Ts ].

encode_type_fields(Fs) -> [ encode_type_field(F) || F <- Fs ].

encode_type_field({field_t, _, Id, T}) ->
    #{name => encode_type(Id),
      type => encode_type(T)}.

encode_name(Name) when is_list(Name) ->
    list_to_binary(Name);
encode_name(Name) when is_binary(Name) ->
    Name.

%% Encode Expr
encode_exprs(Es) -> [ encode_expr(E) || E <- Es ].

encode_expr({id, _, N})     -> encode_name(N);
encode_expr({con, _, N})    -> encode_name(N);
encode_expr({qid, _, Ns})   -> encode_name(lists:join(".", Ns));
encode_expr({qcon, _, Ns})  -> encode_name(lists:join(".", Ns));
encode_expr({typed, _, E})  -> encode_expr(E);
encode_expr({bool, _, B})   -> B;
encode_expr({int, _, V})    -> V;
encode_expr({string, _, S}) -> S;
encode_expr({tuple, _, As}) -> encode_exprs(As);
encode_expr({list, _, As})  -> encode_exprs(As);
encode_expr({bytes, _, B})  ->
    Digits = byte_size(B),
    <<N:Digits/unit:8>> = B,
    list_to_binary(lists:flatten(io_lib:format("#~*.16.0b", [Digits*2, N])));
encode_expr({Lit, _, L}) when Lit == oracle_pubkey; Lit == oracle_query_id;
                              Lit == contract_pubkey; Lit == account_pubkey ->
    aeser_api_encoder:encode(Lit, L);
encode_expr({app, _, {'-', _}, [{int, _, N}]}) ->
  encode_expr({int, [], -N});
encode_expr({app, _, F, As}) ->
    Ef = encode_expr(F),
    Eas = encode_exprs(As),
    #{Ef => Eas};
encode_expr({record, _, Flds}) -> maps:from_list(encode_fields(Flds));
encode_expr({map, _, KVs})     -> [ [encode_expr(K), encode_expr(V)] || {K, V} <- KVs ];
encode_expr({Op,_Ann}) ->
    error({encode_expr_todo, Op}).

encode_fields(Flds) -> [ encode_field(F) || F <- Flds ].

encode_field({field, _, [{proj, _, {id, _, Fld}}], Val}) ->
    {encode_name(Fld), encode_expr(Val)}.

do_render_aci_json(Json) ->
    Contracts =
        case Json of
            JArray when is_list(JArray)  -> JArray;
            JObject when is_map(JObject) -> [JObject];
            JText when is_binary(JText)  ->
                case jsx:decode(Json, [{labels, atom}, return_maps]) of
                    JArray when is_list(JArray)  -> JArray;
                    JObject when is_map(JObject) -> [JObject];
                    _                            -> error(bad_aci_json)
                end
        end,
    DecodedContracts = [ decode_contract(C) || C <- Contracts ],
    {ok, list_to_binary(string:join(DecodedContracts, "\n"))}.

decode_contract(#{contract := #{name := Name,
                                kind := Kind,
                                payable := Payable,
                                type_defs := Ts0,
                                functions := Fs} = C}) ->
    MkTDef = fun(N, T) -> #{name => N, vars => [], typedef => T} end,
    Ts = [ MkTDef(<<"state">>, maps:get(state, C)) || maps:is_key(state, C) ] ++
         [ MkTDef(<<"event">>, maps:get(event, C)) || maps:is_key(event, C) ] ++ Ts0,
    [payable(Payable), case Kind of
                           contract_main -> "main contract ";
                           contract_child -> "contract ";
                           contract_interface -> "contract interface "
                       end,
     io_lib:format("~s", [Name])," =\n",
     decode_tdefs(Ts), decode_funcs(Fs)];
decode_contract(#{namespace := #{name := Name, type_defs := Ts}}) when Ts /= [] ->
    ["namespace ", io_lib:format("~s", [Name])," =\n",
     decode_tdefs(Ts)];
decode_contract(_) -> [].

decode_funcs(Fs) -> [ decode_func(F) || F <- Fs ].

%% decode_func(#{name := init}) -> [];
decode_func(#{name := Name, stateful:= Stateful, payable := Payable, arguments := As, returns := T}) ->
    ["  ", payable(Payable), stateful(Stateful), "entrypoint ", io_lib:format("~s", [Name]), " : ",
     decode_args(As), " => ", decode_type(T), $\n].

decode_args(As) ->
    Das = [ decode_arg(A) || A <- As ],
    [$(,lists:join(", ", Das),$)].

decode_arg(#{type := T}) -> decode_type(T).

decode_types(Ets) ->
    [ decode_type(Et) || Et <- Ets ].

decode_type(#{tuple := Ets}) ->
    Ts = decode_types(Ets),
    case Ts of
        [] -> ["unit"];
        _ -> [$(,lists:join(" * ", Ts),$)]
    end;
decode_type(#{record := Efs}) ->
    Fs = decode_fields(Efs),
    [${,lists:join(",", Fs),$}];
decode_type(#{list := [Et]}) ->
    T = decode_type(Et),
    ["list",$(,T,$)];
decode_type(#{map := Ets}) ->
    Ts = decode_types(Ets),
    ["map",$(,lists:join(",", Ts),$)];
decode_type(#{bytes := Len}) ->
    ["bytes(", integer_to_list(Len), ")"];
decode_type(#{variant := Ets}) ->
    Ts = decode_types(Ets),
    lists:join(" | ", Ts);
decode_type(#{function := #{arguments := Args, returns := R}}) ->
    [decode_type(#{tuple => Args}), " => ", decode_type(R)];
decode_type(Econs) when is_map(Econs) ->	%General constructor
    [{Ec,Ets}] = maps:to_list(Econs),
    AppName = decode_name(Ec),
    AppArgs = decode_types(Ets),
    case AppArgs of
        [] -> [AppName];
        _  -> [AppName,$(,lists:join(", ", AppArgs),$)]
    end;
decode_type(T) ->				%Just raw names.
    decode_name(T).

decode_name(En) when is_atom(En)   -> erlang:atom_to_list(En);
decode_name(En) when is_binary(En) -> binary_to_list(En).

decode_fields(Efs) ->
    [ decode_field(Ef) || Ef <- Efs ].

decode_field(#{name := En, type := Et}) ->
    Name = decode_name(En),
    Type = decode_type(Et),
    [Name," : ",Type].

%% decode_tdefs(Json) -> [TypeString].
%%  Here we are only interested in the type definitions and ignore the
%%  aliases. We find them as they always have variants.

decode_tdefs(Ts) -> [ decode_tdef(T) || T <- Ts ].

decode_tdef(#{name := Name, vars := Vs, typedef := T}) ->
    TypeDef = decode_type(T),
    DefType = decode_deftype(T),
    ["  ", DefType, " ", decode_name(Name), decode_tvars(Vs), " = ", TypeDef, $\n].

decode_deftype(#{record := _Efs}) -> "record";
decode_deftype(#{variant := _})   -> "datatype";
decode_deftype(_T)                      -> "type".

decode_tvars([]) -> [];  %No tvars, no parentheses
decode_tvars(Vs) ->
    Dvs = [ decode_tvar(V) || V <- Vs ],
    [$(,lists:join(", ", Dvs),$)].

decode_tvar(#{name := N}) -> io_lib:format("~s", [N]).

payable(true)  -> "payable ";
payable(false) -> "".

stateful(true)  -> "stateful ";
stateful(false) -> "".

%% #contract{Ann, Con, [Declarations]}.

contract_funcs({C, _, _, Decls}) when ?IS_CONTRACT_HEAD(C); C == namespace ->
    [ D || D <- Decls, is_fun(D)].

contract_types({C, _, _, Decls}) when ?IS_CONTRACT_HEAD(C); C == namespace ->
    [ D || D <- Decls, is_type(D) ].

is_fun({letfun, _, _, _, _, _, _}) -> true;
is_fun({fun_decl, _, _, _})        -> true;
is_fun(_)                          -> false.

is_type({type_def, _, _, _, _}) -> true;
is_type(_)                      -> false.

sort_decls(Ds) ->
    Sort = fun (D1, D2) ->
                   aeso_syntax:get_ann(line, D1, 0) =<
                       aeso_syntax:get_ann(line, D2, 0)
           end,
    lists:sort(Sort, Ds).

is_entrypoint(Node) -> aeso_syntax:get_ann(entrypoint, Node, false).
is_stateful(Node) -> aeso_syntax:get_ann(stateful, Node, false).
is_payable(Node) -> aeso_syntax:get_ann(payable, Node, false).

typedef_name({type_def, _, {id, _, Name}, _, _}) -> Name.

typedef_vars({type_def, _, _, Vars, _}) -> Vars.

typedef_def({type_def, _, _, _, Def}) -> Def.
