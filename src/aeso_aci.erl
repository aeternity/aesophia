%%%-------------------------------------------------------------------
%%% @author Robert Virding
%%% @copyright (C) 2019, Aeternity Anstalt
%%% @doc
%%%     ACI interface
%%% @end
%%% Created : 12 Jan 2019
%%%-------------------------------------------------------------------

-module(aeso_aci).

-export([ encode/1
        , encode/2
        , decode/1]).

-export([ encode_type/1
        , encode_expr/1]).

%% encode(ContractString) -> {ok,JSON} | {error,String}.
%% encode(ContractString, Options) -> {ok,JSON} | {error,String}.
%%  Build a JSON structure with lists and tuples, not maps, as this
%%  allows us to order the fields in the contructed JSON string.

encode(ContractString) -> encode(ContractString, []).

encode(ContractString, Options) when is_binary(ContractString) ->
    encode(binary_to_list(ContractString), Options);
encode(ContractString, Options) ->
    try
        Ast = aeso_compiler:parse(ContractString, Options),
        %% io:format("~p\n", [Ast]),
        TypedAst = aeso_ast_infer_types:infer(Ast, [dont_unfold]),
        %% io:format("~p\n", [TypedAst]),
        JList = [ encode_contract(C) || C <- TypedAst ],
        {ok,jsx:encode(JList)}
    catch
        %% The compiler errors.
        error:{parse_errors, Errors} ->
            {error, join_errors("Parse errors", Errors, fun(E) -> E end)};
        error:{type_errors, Errors} ->
            {error, join_errors("Type errors", Errors, fun(E) -> E end)};
        error:{code_errors, Errors} ->
            {error, join_errors("Code errors", Errors,
                                fun (E) -> io_lib:format("~p", [E]) end)}
        %% General programming errors in the compiler just signal error.
    end.

join_errors(Prefix, Errors, Pfun) ->
    Ess = [ Pfun(E) || E <- Errors ],
    list_to_binary(string:join([Prefix|Ess], "\n")).

encode_contract(Contract) ->
    Cname = contract_name(Contract),
    Tdefs = [ encode_typedef(T) ||
                T <- sort_decls(contract_types(Contract)) ],
    Fdefs = [ encode_function(F)
              || F <- sort_decls(contract_funcs(Contract)),
                 not is_private(F) ],
    #{<<"contract">> => #{<<"name">>      => encode_name(Cname),
                          <<"type_defs">> => Tdefs,
                          <<"functions">> => Fdefs}}.

%%  Encode a function definition. Currently we are only interested in
%%  the interface and type.
encode_function(FDef = {letfun, _, {id, _, Name}, Args, Type, _}) ->
    #{<<"name">>      => encode_name(Name),
      <<"arguments">> => encode_args(Args),
      <<"returns">>   => encode_type(Type),
      <<"stateful">>  => is_stateful(FDef)};
encode_function(FDecl = {fun_decl, _, {id, _, Name}, {fun_t, _, _, Args, Type}}) ->
    #{<<"name">>      => encode_name(Name),
      <<"arguments">> => encode_anon_args(Args),
      <<"returns">>   => encode_type(Type),
      <<"stateful">>  => is_stateful(FDecl)}.

encode_anon_args(Types) ->
    Anons = [ list_to_binary("_" ++ integer_to_list(X)) || X <- lists:seq(1, length(Types))],
    [ #{<<"name">> => V, <<"type">> => encode_type(T)}
      || {V, T} <- lists:zip(Anons, Types) ].

encode_args(Args) -> [ encode_arg(A) || A <- Args ].

encode_arg({arg, _, Id, T}) ->
    #{<<"name">> => encode_type(Id),
      <<"type">> => encode_type(T)}.

encode_typedef(Type) ->
    Name = typedef_name(Type),
    Vars = typedef_vars(Type),
    Def  = typedef_def(Type),
    #{<<"name">>    => encode_name(Name),
      <<"vars">>    => encode_tvars(Vars),
      <<"typedef">> => encode_type(Def)}.

encode_tvars(Vars) ->
    [ #{<<"name">> => encode_type(V)} || V <- Vars ].

%% Encode type
encode_type({tvar, _, N})         -> encode_name(N);
encode_type({id, _, N})           -> encode_name(N);
encode_type({con, _, N})          -> encode_name(N);
encode_type({qid, _, Ns})         -> encode_name(lists:join(".", Ns));
encode_type({qcon, _, Ns})        -> encode_name(lists:join(".", Ns));
encode_type({tuple_t, _, As})     -> #{<<"tuple">> => encode_types(As)};
encode_type({bytes_t, _, Len})    -> #{<<"bytes">> => Len};
encode_type({record_t, Fs})       -> #{<<"record">> => encode_type_fields(Fs)};
encode_type({app_t, _, Id, Fs})   -> #{encode_type(Id) => encode_types(Fs)};
encode_type({variant_t, Cs})      -> #{<<"variant">> => encode_types(Cs)};
encode_type({constr_t, _, C, As}) -> #{encode_type(C) => encode_types(As)};
encode_type({alias_t, Type})      -> encode_type(Type);
encode_type({fun_t, _, _, As, T}) -> #{<<"function">> =>
                                         #{<<"arguments">> => encode_types(As),
                                           <<"returns">> => encode_type(T)}}.

encode_types(Ts) -> [ encode_type(T) || T <- Ts ].

encode_type_fields(Fs) -> [ encode_type_field(F) || F <- Fs ].

encode_type_field({field_t, _, Id, T}) ->
    #{<<"name">> => encode_type(Id),
      <<"type">> => encode_type(T)}.

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
encode_expr({app, _, F, As}) ->
    Ef = encode_expr(F),
    Eas = encode_exprs(As),
    #{Ef => Eas};
encode_expr({record, _, Flds}) -> encode_fields(Flds);
encode_expr({map, _, KVs})     -> [ [encode_expr(K), encode_expr(V)] || {K, V} <- KVs ];
encode_expr({Op,_Ann}) ->
    error({encode_expr_todo, Op}).

encode_fields(Flds) -> [ encode_field(F) || F <- Flds ].

encode_field({field, _, [{proj, _, {id, _, Fld}}], Val}) ->
    #{encode_name(Fld) => encode_expr(Val)}.

%% decode(JSON) -> ContractString.
%%  Decode a JSON string and generate a suitable contract string which
%%  can be included in a contract definition. We decode into a map
%%  here as this is easier to work with and order is not important.

decode(Json) ->
    Cs =
        case jsx:decode(Json, [return_maps]) of
            Map when is_map(Map) -> [Map];
            List                 -> List
        end,

    %% io:format("~p\n", [Map]),
    DecCs = [ decode_contract(C) || #{<<"contract">> := C} <- Cs ],
    list_to_binary(string:join(DecCs, "\n")).

decode_contract(#{<<"name">> := Name,
                  <<"type_defs">> := Ts,
                  <<"functions">> := Fs}) ->
    ["contract"," ",io_lib:format("~s", [Name])," =\n",
     decode_tdefs(Ts),
     decode_funcs(Fs)].

decode_funcs(Fs) -> [ decode_func(F) || F <- Fs ].

%% decode_func(#{<<"name">> := <<"init">>}) -> [];
decode_func(#{<<"name">> := Name,<<"arguments">> := As,<<"returns">> := T}) ->
    ["  function"," ",io_lib:format("~s", [Name])," : ",
     decode_args(As)," => ",decode_type(T),$\n].

decode_args(As) ->
    Das = [ decode_arg(A) || A <- As ],
    [$(,lists:join(", ", Das),$)].

decode_arg(#{<<"type">> := T}) -> decode_type(T).

decode_types(Ets) ->
    [ decode_type(Et) || Et <- Ets ].

decode_type(#{<<"tuple">> := Ets}) ->
    Ts = decode_types(Ets),
    [$(,lists:join(",", Ts),$)];
decode_type(#{<<"record">> := Efs}) ->
    Fs = decode_fields(Efs),
    [${,lists:join(",", Fs),$}];
decode_type(#{<<"list">> := [Et]}) ->
    T = decode_type(Et),
    ["list",$(,T,$)];
decode_type(#{<<"map">> := Ets}) ->
    Ts = decode_types(Ets),
    ["map",$(,lists:join(",", Ts),$)];
decode_type(#{<<"bytes">> := Len}) ->
    ["bytes(", integer_to_list(Len), ")"];
decode_type(#{<<"variant">> := Ets}) ->
    Ts = decode_types(Ets),
    lists:join(" | ", Ts);
decode_type(#{<<"function">> := #{<<"arguments">> := Args, <<"returns">> := R}}) ->
    [decode_type(#{<<"tuple">> => Args}), " => ", decode_type(R)];
decode_type(Econs) when is_map(Econs) ->	%General constructor
    [{Ec,Ets}] = maps:to_list(Econs),
    C = decode_name(Ec),
    Ts = decode_types(Ets),
    [C,$(,lists:join(",", Ts),$)];
decode_type(T) ->				%Just raw names.
    decode_name(T).

decode_name(En) ->
    binary_to_list(En).

decode_fields(Efs) ->
    [ decode_field(Ef) || Ef <- Efs ].

decode_field(#{<<"name">> := En,<<"type">> := Et}) ->
    Name = decode_name(En),
    Type = decode_type(Et),
    [Name," : ",Type].

%% decode_tdefs(Json) -> [TypeString].
%%  Here we are only interested in the type definitions and ignore the
%%  aliases. We find them as they always have variants.

decode_tdefs(Ts) -> [ decode_tdef(T) || T <- Ts ].

decode_tdef(#{<<"name">> := Name, <<"vars">> := Vs, <<"typedef">> := T}) ->
    TypeDef = decode_type(T),
    DefType = decode_deftype(T),
    ["  ", DefType, " ", decode_name(Name), decode_tvars(Vs), " = ", TypeDef, $\n].

decode_deftype(#{<<"record">> := _Efs}) -> "record";
decode_deftype(#{<<"variant">> := _})   -> "datatype";
decode_deftype(_T)                      -> "type".

decode_tvars([]) -> [];                         %No tvars, no parentheses
decode_tvars(Vs) ->
    Dvs = [ decode_tvar(V) || V <- Vs ],
    [$(,lists:join(", ", Dvs),$)].

decode_tvar(#{<<"name">> := N}) -> io_lib:format("~s", [N]).

%% #contract{Ann, Con, [Declarations]}.

contract_name({contract, _, {con, _, Name}, _})  -> Name;
contract_name({namespace, _, {con, _, Name}, _}) -> Name.

contract_funcs({C, _, _, Decls}) when C == contract; C == namespace ->
    [ D || D <- Decls, is_fun(D)].

contract_types({C, _, _, Decls}) when C == contract; C == namespace ->
    [ D || D <- Decls, is_type(D) ].

is_fun({letfun, _, _, _, _, _}) -> true;
is_fun({fun_decl, _, _, _})     -> true;
is_fun(_)                       -> false.

is_type({type_def, _, _, _, _}) -> true;
is_type(_)                      -> false.

sort_decls(Ds) ->
    Sort = fun (D1, D2) ->
                   aeso_syntax:get_ann(line, D1, 0) =<
                       aeso_syntax:get_ann(line, D2, 0)
           end,
    lists:sort(Sort, Ds).


is_private(Node) -> aeso_syntax:get_ann(private, Node, false).
is_stateful(Node) -> aeso_syntax:get_ann(stateful, Node, false).

typedef_name({type_def, _, {id, _, Name}, _, _}) -> Name.

typedef_vars({type_def, _, _, Vars, _}) -> Vars.

typedef_def({type_def, _, _, _, Def}) -> Def.
