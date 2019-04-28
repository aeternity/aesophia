%%%-------------------------------------------------------------------
%%% @author Robert Virding
%%% @copyright (C) 2019, Aeternity Anstalt
%%% @doc
%%%     ACI interface
%%% @end
%%% Created : 12 Jan 2019
%%%-------------------------------------------------------------------

-module(aeso_aci).

-export([encode/1,encode/2,decode/1]).

-export([encode_contract/1,encode_contract/2,decode_contract/1]).
-export([encode_func/1,encode_type/1,encode_arg/1,
         encode_stmt/1,encode_expr/1]).

%% Define records for the various typed syntactic forms. These make
%% the code easier but don't seem to exist elsewhere. Unfortunately
%% sometimes the same typename is used with different fields.

%% Top-level
-record(contract, {ann,con,decls}).
%% -record(namespace, {ann,con,decls}).
-record(letfun, {ann,id,args,type,body}).
-record(type_def, {ann,id,vars,typedef}).

%% Types
-record(app_t, {ann,id,fields}).
-record(tuple_t, {ann,args}).
-record(bytes_t, {ann,len}).
-record(record_t, {fields}).
-record(field_t, {ann,id,type}).
-record(alias_t, {type}).
-record(variant_t, {cons}).
-record(constr_t, {ann,con,args}).
-record(fun_t, {ann,named,args,type}).

%% Tokens
-record(arg, {ann,id,type}).
-record(id, {ann,name}).
-record(con, {ann,name}).
-record(qid, {ann,names}).
-record(qcon, {ann,names}).
-record(tvar, {ann,name}).

%% Statements
-record(block, {ann,body}).
-record('if', {ann,test,then,else}).            %Both statement and expression
-record(letval, {ann,pat,type,exp}).
-record(switch, {ann,arg,cases}).
-record('case', {ann,pat,body}).

%% Expressions
-record(bool, {ann,bool}).
-record(int, {ann,value}).
-record(string, {ann,bin}).
-record(bytes, {ann,bin}).
-record(tuple, {ann,args}).
-record(list, {ann,args}).
-record(record, {ann,fields}).                  %Create a record
-record(field, {ann,name,value}).               %A record field
-record(proj, {ann,value}).                     %?
-record(map, {ann,fields}).                     %Create a map
-record(map_get, {ann,field}).
-record(lam, {ann,args,body}).
-record(app, {ann,func,args}).
-record(typed, {ann,expr,type}).

%% The old deprecated interface.

encode(C) -> encode_contract(C).
encode(C, Os) -> encode_contract(C, Os).
decode(J) -> decode_contract(J).

%% encode_contract(ContractString) -> {ok,JSON} | {error,String}.
%% encode_contract(ContractString, Options) -> {ok,JSON} | {error,String}.
%%  Build a JSON structure with lists and tuples, not maps, as this
%%  allows us to order the fields in the contructed JSON string.

encode_contract(ContractString) -> 
    encode_contract(ContractString, []).
encode_contract(ContractString, Options) when is_binary(ContractString) ->
    encode_contract(binary_to_list(ContractString), Options);
encode_contract(ContractString, Options) ->
    try
        Ast = parse(ContractString, Options),
        %% io:format("Ast\n~p\n", [Ast]),
        %% aeso_ast:pp(Ast),
        TypedAst = aeso_ast_infer_types:infer(Ast, Options),
        %% io:format("Typed ast\n~p\n", [TypedAst]),
        %% aeso_ast:pp_typed(TypedAst),
        %% We find and look at the last contract.
        Contract = lists:last(TypedAst),
        Cname = contract_name(Contract),
        Tdefs = [ do_encode_typedef(T) ||
                    T <- sort_decls(contract_types(Contract)) ],
        Fdefs = [ do_encode_func(F) || F <- sort_decls(contract_funcs(Contract)),
                                       not is_private_func(F) ],
        Jmap = [{<<"contract">>, [{<<"name">>, do_encode_name(Cname)},
                                  {<<"type_defs">>, Tdefs},
                                  {<<"functions">>, Fdefs}]}],
        %% io:format("~p\n", [Jmap]),
        {ok,jsx:encode(Jmap)}
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

%% encode_func(TypedAST) -> JSON.
%%  Encode a function AST into a JSON structure.

encode_func(AST) ->
    jsx:encode(do_encode_func(AST)).

%% do_encode_func(Function) -> JSONmap
%%  Encode a function definition. Currently we are only interested in
%%  the interface and type.

do_encode_func(Fdef) ->
    Name = function_name(Fdef),
    Args = function_args(Fdef),
    Type = function_type(Fdef),
    [{<<"name">>, do_encode_name(Name)},
     {<<"arguments">>, do_encode_args(Args)},
     {<<"returns">>, do_encode_type(Type)},
     {<<"stateful">>, is_stateful_func(Fdef)}].

%% encode_arg(TypedAST) -> JSON.
%%  Encode an argument AST into a JSON structure.

encode_arg(AST) ->
    jsx:encode(do_encode_arg(AST)).

%% do_encode_args(ArgASTs) -> [JSONmap].
%% do_encode_arg(ArgAST) -> JSONmap.

do_encode_args(Args) ->
    [ do_encode_arg(A) || A <- Args ].

do_encode_arg(#arg{id=Id,type=T}) ->
    [{<<"name">>,do_encode_type(Id)},
     {<<"type">>,do_encode_type(T)}].

%% encode_type(TypedAST) -> JSON.
%%  Encode a type AST into a JSON structure.

encode_type(AST) ->
    jsx:encode(do_encode_type(AST)).

%% do_encode_types([TypeAST]) -> [JSONmap].
%% do_encode_type(TypeAST) -> JsonMap.

do_encode_types(Types) ->
    [ do_encode_type(T) || T <- Types ].

do_encode_type(#tvar{name=N}) -> do_encode_name(N);
do_encode_type(#id{name=N}) -> do_encode_name(N);
do_encode_type(#con{name=N}) -> do_encode_name(N);
do_encode_type(#qid{names=Ns}) ->
    do_encode_name(lists:join(".", Ns));
do_encode_type(#qcon{names=Ns}) ->
    do_encode_name(lists:join(".", Ns));        %?
do_encode_type(#tuple_t{args=As}) ->
    Eas = do_encode_types(As),
    [{<<"tuple">>,Eas}];
do_encode_type(#bytes_t{len=Len}) ->
    {<<"bytes">>,Len};
do_encode_type(#record_t{fields=Fs}) ->
    Efs = do_encode_type_rec_fields(Fs),
    [{<<"record">>,Efs}];
%% Special case lists and maps as they are built-in types.
do_encode_type(#app_t{id=#id{name="list"},fields=[F]}) ->
    Ef = do_encode_type(F),
    [{<<"list">>,Ef}];
do_encode_type(#app_t{id=#id{name="map"},fields=Fs}) ->
    Ef = do_encode_type_mapo_field(Fs),
    [{<<"map">>,Ef}];
%% Other applications.
do_encode_type(#app_t{id=Id,fields=Fs}) ->
    Name = do_encode_type(Id),
    Efs = do_encode_types(Fs),
    [{Name,Efs}];
do_encode_type(#variant_t{cons=Cs}) ->
    Ecs = do_encode_types(Cs),
    [{<<"variant">>,Ecs}];
do_encode_type(#constr_t{con=C,args=As}) ->
    Ec = do_encode_type(C),
    Eas = do_encode_types(As),
    [{Ec,Eas}];
do_encode_type(#fun_t{args=As,type=T}) ->
    Eas = do_encode_types(As),
    Et = do_encode_type(T),
    [{<<"function">>,[{<<"arguments">>,Eas},{<<"returns">>,Et}]}].

do_encode_name(Name) ->
    list_to_binary(Name).

%% do_encode_type_rec_fields(Fields) -> [JSONmap].
%% do_encode_type_rec_field(Field) -> JSONmap.
%%  Encode a record field type.

do_encode_type_rec_fields(Fs) ->
    [ do_encode_type_rec_field(F) || F <- Fs ].

do_encode_type_rec_field(#field_t{id=Id,type=T}) ->
    [{<<"name">>,do_encode_type(Id)},
     {<<"type">>,do_encode_type(T)}].

%% do_encode_type_mapo_field(Field) -> JSONmap.
%%  Two fields for one map type.

do_encode_type_mapo_field([K,V]) ->
    [{<<"key">>,do_encode_type(K)},
     {<<"value">>,do_encode_type(V)}].

%% do_encode_typedef(TypeDefAST) -> JSON.

do_encode_typedef(Type) ->
    Name = typedef_name(Type),
    Vars = typedef_vars(Type),
    Def = typedef_def(Type),
    [{<<"name">>, do_encode_name(Name)},
     {<<"vars">>, do_encode_tvars(Vars)},
     {<<"typedef">>, do_encode_alias(Def)}].

do_encode_tvars(Vars) ->
    [ do_encode_tvar(V) || V <- Vars ].

do_encode_tvar(#tvar{name=N}) ->
    [{<<"name">>, do_encode_name(N)}].

do_encode_alias(#alias_t{type=T}) ->
    do_encode_type(T);
do_encode_alias(A) -> do_encode_type(A).

%% encode_stmt(StmtAST) -> JSON.
%%  Encode a statement AST into a JSON structure.

encode_stmt(AST) ->
    jsx:encode(do_encode_stmt(AST)).

%% do_encode_stmt(StmtAST) -> JSONmap.

do_encode_stmt(#typed{expr=E}) ->               %Ignore the type
    do_encode_stmt(E);
do_encode_stmt(#block{body=Body}) ->
    Eblock = [ do_encode_stmt(B) || B <- Body ],
    [{<<"block">>,Eblock}];
do_encode_stmt(#'if'{test=Test,then=Then,else=Else}) ->
    %% This is both a statement and en expression.
    Etest = do_encode_expr(Test),
    Ethen = do_encode_stmt(Then),
    Eelse = do_encode_stmt(Else),
    [{<<"if">>,[{<<"test">>,Etest},{<<"then">>,Ethen},{<<"else">>,Eelse}]}];
do_encode_stmt(#letval{pat=Pat,exp=Exp}) ->
    Epat = do_encode_expr(Pat),
    Eexp = do_encode_expr(Exp),
    [{<<"let">>,[{<<"pattern">>,Epat},{<<"expression">>,Eexp}]}];
do_encode_stmt(#switch{arg=Arg,cases=Cases}) ->
    Earg = do_encode_expr(Arg),
    Ecases = [ do_encode_stmt_case(Case) || Case <- Cases ],
    [{<<"switch">>,[{<<"arg">>,Earg},{<<"cases">>,Ecases}]}];
do_encode_stmt(E) ->
    do_encode_expr(E).

do_encode_stmt_case(#'case'{pat=Pat,body=Body}) ->
    Epat = do_encode_expr(Pat),	                %Patterns are expessions
    Ebody = do_encode_stmt(Body),
    [{<<"pattern">>,Epat},{<<"body">>,Ebody}].

%% encode_expr(ExprAST) -> JSON.
%%  Encode an expression AST into a JSON structure.

encode_expr(AST) ->
    jsx:encode(do_encode_expr(AST)).

%% do_encode_exprs(ExprASTs) -> [JSONmap].
%% do_encode_expr(ExprAST) -> JSONmap.

do_encode_exprs(Es) ->
    [ do_encode_expr(E) || E <- Es ].

do_encode_expr(#typed{expr=E}) ->               %Ignore the type
    do_encode_expr(E);
do_encode_expr(#id{name=N}) -> do_encode_name(N);
do_encode_expr(#con{name=N}) -> do_encode_name(N);
do_encode_expr(#qid{names=Ns}) ->
    do_encode_name(lists:join(".", Ns));
do_encode_expr(#qcon{names=Ns}) ->
    do_encode_name(lists:join(".", Ns));        %?
do_encode_expr(#bool{bool=B}) -> B;
do_encode_expr(#int{value=V}) -> V;
do_encode_expr(#string{bin=B}) ->
    [{<<"string">>,B}];
do_encode_expr(#bytes{bin=B}) -> B;
do_encode_expr(#tuple{args=As}) ->
    Eas = do_encode_exprs(As),
    [{<<"tuple">>,Eas}];
do_encode_expr(#list{args=As}) ->
    Eas = do_encode_exprs(As),
    [{<<"list">>,Eas}];
do_encode_expr(#record{fields=Fs}) ->           %Create a record
    Efs = do_encode_expr_rec_fields(Fs),
    [{<<"create_record">>,Efs}];
do_encode_expr({record,_Ann,Rec,Fs}) ->         %Update a record
    Erec = do_encode_expr(Rec),
    Efs = do_encode_expr_rec_fields(Fs),
    [{<<"update_record">>,[Erec,Efs]}];
do_encode_expr(#lam{args=As,body=B}) ->
    Eas = do_encode_args(As),
    Eb = do_encode_stmt(B),
    [{<<"function">>,[{<<"arguments">>,Eas},{<<"body">>,Eb}]}];
do_encode_expr(#map{fields=Fs}) ->              %Create a map
    Efs = do_encode_expr_map_fields(Fs),
    [{<<"create_map">>,Efs}];
do_encode_expr({map,_Ann,Map,Fs}) ->            %Update a map
    Emap = do_encode_expr(Map),
    Efs = do_encode_expr_map_fields(Fs),
    [{<<"update_map">>,[Emap,Efs]}];
do_encode_expr(#map_get{field=F}) ->
    do_encode_expr(F);
do_encode_expr(#proj{value=V}) ->
    do_encode_expr(V);
do_encode_expr(#app{func=F,args=As}) ->
    Ef = do_encode_expr(F),
    Eas = do_encode_exprs(As),
    [{<<"apply">>,[{<<"function">>,Ef},
                   {<<"arguments">>,Eas}]}];
do_encode_expr(#'if'{test=Test,then=Then,else=Else}) ->
    %% This is both a statement and en expression.
    Etest = do_encode_expr(Test),
    Ethen = do_encode_expr(Then),
    Eelse = do_encode_expr(Else),
    [{<<"if">>,[{<<"test">>,Etest},{<<"then">>,Ethen},{<<"else">>,Eelse}]}];
do_encode_expr({Op,_Ann}) ->
    list_to_binary(atom_to_list(Op)).

%% do_encode_expr_rec_fields(Fields) -> [JSON].
%% do_encode_expr_rec_field(Field) -> JSON.
%%  Encode a record field expression.

do_encode_expr_rec_fields(Fs) ->
    [ do_encode_expr_rec_field(F) || F <- Fs ].

do_encode_expr_rec_field(#field{name=[N],value=V}) ->
    [{<<"name">>,do_encode_expr(N)},
     {<<"value">>,do_encode_expr(V)}].

%% do_encode_expr_map_fields(Fields) -> [JSON].
%% do_encode_expr_map_field(Field) -> JSON.
%%  Encode a map field expression.

do_encode_expr_map_fields(Fs) ->
    [ do_encode_expr_map_field(F) || F <- Fs ].

do_encode_expr_map_field({K,V}) ->
    [{<<"key">>,do_encode_expr(K)},
     {<<"value">>,do_encode_expr(V)}];
do_encode_expr_map_field(#field{name=[K],value=V}) ->
    [{<<"key">>,do_encode_expr(K)},
     {<<"value">>,do_encode_expr(V)}].

%% decode_contract(JSON) -> ContractString.
%%  Decode a JSON string and generate a suitable contract string which
%%  can be included in a contract definition. We decode into a map
%%  here as this is easier to work with and order is not important.

decode_contract(Json) ->
    Map = jsx:decode(Json, [return_maps]),
    %% io:format("~p\n", [Map]),
    #{<<"contract">> := C} = Map,
    #{<<"name">> := Name, <<"type_defs">> := Ts, <<"functions">> := Fs} = C,
    CS = ["contract"," ",io_lib:format("~s", [Name])," =\n",
          do_decode_tdefs(Ts),
          do_decode_funcs(Fs)],
    list_to_binary(CS).

do_decode_funcs(Fs) -> [ do_decode_func(F) || F <- Fs ].

do_decode_func(#{<<"name">> := <<"init">>}) -> [];
do_decode_func(#{<<"name">> := Name,<<"arguments">> := As,<<"returns">> := T}) ->
    ["  function"," ",io_lib:format("~s", [Name])," : ",
     do_decode_args(As)," => ",do_decode_type(T),$\n].

do_decode_args(As) ->
    Das = [ do_decode_arg(A) || A <- As ],
    [$(,lists:join(", ", Das),$)].

do_decode_arg(#{<<"type">> := T}) -> do_decode_type(T).

do_decode_types(Ets) ->
    [ do_decode_type(Et) || Et <- Ets ].

do_decode_type(#{<<"tuple">> := Ets}) ->
    Ts = do_decode_types(Ets),
    [$(,lists:join(", ", Ts),$)];
do_decode_type(#{<<"record">> := Efs}) ->
    Fs = do_decode_type_rec_fields(Efs),
    [${,lists:join(", ", Fs),$}];
do_decode_type(#{<<"list">> := Et}) ->
    T = do_decode_type(Et),
    ["list",$(,T,$)];
do_decode_type(#{<<"map">> := Et}) ->
    T = do_decode_type_map(Et),
    ["map",$(,T,$)];
do_decode_type(#{<<"variant">> := Ets}) ->
    Ts = do_decode_types(Ets),
    lists:join(" | ", Ts);
do_decode_type(Econs) when is_map(Econs) ->     %General constructor
    %% io:format("~p\n", [Econs]),
    [{Ec,Ets}] = maps:to_list(Econs),
    C = do_decode_name(Ec),
    Ts = do_decode_types(Ets),
    [C,$(,lists:join(", ", Ts),$)];
do_decode_type(T) ->                            %Just raw names.
    do_decode_name(T).

do_decode_name(En) ->
    binary_to_list(En).

do_decode_type_rec_fields(Efs) ->
    [ do_decode_type_rec_field(Ef) || Ef <- Efs ].

do_decode_type_rec_field(#{<<"name">> := En,<<"type">> := Et}) ->
    Name = do_decode_name(En),
    Type = do_decode_type(Et),
    [Name," : ",Type].

do_decode_type_map(#{<<"key">> := Ek,<<"value">> := Ev}) ->
    Key = do_decode_type(Ek),
    Value = do_decode_type(Ev),
    [Key,", ",Value].

%% do_decode_tdefs(Json) -> [TypeString].
%%  Here we are only interested in the type definitions and ignore the
%%  aliases. We find them as they always have variants.

do_decode_tdefs(Ts) -> [ do_decode_tdef(T) ||
                        #{<<"typedef">> := #{<<"variant">> := _}} = T <- Ts
                    ].

do_decode_tdef(#{<<"name">> := Name,<<"vars">> := Vs,<<"typedef">> := T}) ->
    ["  datatype"," ",do_decode_name(Name),do_decode_tvars(Vs),
     " = ",do_decode_type(T),$\n].

do_decode_tvars([]) -> [];                      %No tvars, no parentheses
do_decode_tvars(Vs) ->
    Dvs = [ do_decode_tvar(V) || V <- Vs ],
    [$(,lists:join(", ", Dvs),$)].

do_decode_tvar(#{<<"name">> := N}) -> io_lib:format("~s", [N]).

%% #contract{Ann, Con, [Declarations]}.

contract_name(#contract{con=#con{name=N}}) -> N.

contract_funcs(#contract{decls=Decls}) ->
    [ D || D <- Decls, is_record(D, letfun) ].

contract_types(#contract{decls=Decls}) ->
    [ D || D <- Decls, is_record(D, type_def) ].

%% To keep dialyzer happy and quiet.
%% namespace_name(#namespace{con=#con{name=N}}) -> N.
%%
%% namespace_funcs(#namespace{decls=Decls}) ->
%%     [ D || D <- Decls, is_record(D, letfun) ].
%%
%% namespace_types(#namespace{decls=Decls}) ->
%%     [ D || D <- Decls, is_record(D, type_def) ].

sort_decls(Ds) ->
    Sort = fun (D1, D2) ->
                   aeso_syntax:get_ann(line, D1, 0) =<
                       aeso_syntax:get_ann(line, D2, 0)
           end,
    lists:sort(Sort, Ds).

%% #letfun{Ann, Id, [Arg], Type, Typedef}.

function_name(#letfun{id=#id{name=N}}) -> N.

function_args(#letfun{args=Args}) -> Args.

function_type(#letfun{type=Type}) -> Type.

is_private_func(#letfun{ann=A}) -> aeso_syntax:get_ann(private, A, false).

is_stateful_func(#letfun{ann=A}) -> aeso_syntax:get_ann(stateful, A, false).

%% #type_def{Ann, Id, [Var], Typedef}.

typedef_name(#type_def{id=#id{name=N}}) -> N.

typedef_vars(#type_def{vars=Vars}) -> Vars.

typedef_def(#type_def{typedef=Def}) -> Def.

%% parse(ContractString, Options) -> {ok,AST}.
%%  Signal errors, the sophia compiler way. Sigh!

parse(Text, Options) ->
    %% Try and return something sensible here!
    case aeso_parser:string(Text, Options) of
        %% Yay, it worked!
        {ok, Contract} -> Contract;
        %% Scan errors.
        {error, {Pos, scan_error}} ->
            parse_error(Pos, "scan error");
        {error, {Pos, scan_error_no_state}} ->
            parse_error(Pos, "scan error");
        %% Parse errors.
        {error, {Pos, parse_error, Error}} ->
            parse_error(Pos, Error);
        {error, {Pos, ambiguous_parse, As}} ->
            ErrorString = io_lib:format("Ambiguous ~p", [As]),
            parse_error(Pos, ErrorString);
        %% Include error
        {error, {Pos, include_error, File}} ->
            parse_error(Pos, io_lib:format("could not find include file '~s'", [File]))
    end.

parse_error(Pos, ErrorString) ->
    %% io:format("Error ~p ~p\n", [Pos,ErrorString]),
    Error = io_lib:format("~s: ~s", [pos_error(Pos), ErrorString]),
    error({parse_errors, [Error]}).

pos_error({Line, Pos}) ->
    io_lib:format("line ~p, column ~p", [Line, Pos]);
pos_error({no_file, Line, Pos}) ->
    pos_error({Line, Pos});
pos_error({File, Line, Pos}) ->
    io_lib:format("file ~s, line ~p, column ~p", [File, Line, Pos]).
