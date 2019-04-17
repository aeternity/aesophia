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
-export([encode_type/1,encode_types/1,
	 encode_stmt/1,encode_expr/1,encode_exprs/1]).

%% Define records for the various typed syntactic forms. These make
%% the code easier but don't seem to exist elsewhere.

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

%% Expressions
-record(bool, {ann,bool}).
-record(int, {ann,value}).
-record(string, {ann,bin}).
-record(bytes, {ann,bin}).
-record(tuple, {ann,args}).
-record(list, {ann,args}).
-record(record, {ann,fields}).
-record(field, {ann,name,value}).		%A record field
-record(proj, {ann,value}).			%?
-record(app, {ann,func,args}).
-record(typed, {ann,expr,type}).

%% encode(ContractString) -> {ok,JSON} | {error,String}.
%% encode(ContractString, Options) -> {ok,JSON} | {error,String}.
%%  Build a JSON structure with lists and tuples, not maps, as this
%%  allows us to order the fields in the contructed JSON string.

encode(ContractString) -> encode(ContractString, []).

encode(ContractString, Options) when is_binary(ContractString) ->
    encode(binary_to_list(ContractString), Options);
encode(ContractString, Options) ->
    try
        Ast = parse(ContractString, Options),
        io:format("Ast\n~p\n", [Ast]),
        %% aeso_ast:pp(Ast),
        TypedAst = aeso_ast_infer_types:infer(Ast, Options),
        io:format("Typed ast\n~p\n", [TypedAst]),
        %% aeso_ast:pp_typed(TypedAst),
        %% We find and look at the last contract.
        Contract = lists:last(TypedAst),
        Cname = contract_name(Contract),
        Tdefs = [ encode_typedef(T) ||
                    T <- sort_decls(contract_types(Contract)) ],
        Fdefs = [ encode_func(F) || F <- sort_decls(contract_funcs(Contract)),
                                    not is_private_func(F) ],
        Jmap = [{<<"contract">>, [{<<"name">>, encode_name(Cname)},
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

%% encode_func(Function) -> JSON
%%  Encode a function definition. Currently we are only interested in
%%  the interface and type.

encode_func(Fdef) ->
    Name = function_name(Fdef),
    Args = function_args(Fdef),
    Type = function_type(Fdef),
    [{<<"name">>, encode_name(Name)},
     {<<"arguments">>, encode_args(Args)},
     {<<"returns">>, encode_type(Type)},
     {<<"stateful">>, is_stateful_func(Fdef)}].

%% encode_args(Args) -> [JSON].
%% encode_arg(Args) -> JSON.

encode_args(Args) ->
    [ encode_arg(A) || A <- Args ].

encode_arg(#arg{id=Id,type=T}) ->
    [{<<"name">>,encode_type(Id)},
     {<<"type">>,[encode_type(T)]}].

%% encode_types(Types) -> [JSON].
%% encode_type(Type) -> JSON.

encode_types(Types) ->
    [ encode_type(T) || T <- Types ].

encode_type(#tvar{name=N}) -> encode_name(N);
encode_type(#id{name=N}) -> encode_name(N);
encode_type(#con{name=N}) -> encode_name(N);
encode_type(#qid{names=Ns}) ->
    encode_name(lists:join(".", Ns));
encode_type(#qcon{names=Ns}) ->
    encode_name(lists:join(".", Ns));           %?
encode_type(#tuple_t{args=As}) ->
    Eas = encode_types(As),
    [{<<"tuple">>,Eas}];
encode_type(#bytes_t{len=Len}) ->
    {<<"bytes">>, Len};
encode_type(#record_t{fields=Fs}) ->
    Efs = encode_field_types(Fs),
    [{<<"record">>,Efs}];
encode_type(#app_t{id=Id,fields=Fs}) ->
    Name = encode_type(Id),
    Efs = encode_types(Fs),
    [{Name,Efs}];
encode_type(#variant_t{cons=Cs}) ->
    Ecs = encode_types(Cs),
    [{<<"variant">>,Ecs}];
encode_type(#constr_t{con=C,args=As}) ->
    Ec = encode_type(C),
    Eas = encode_types(As),
    [{Ec,Eas}];
encode_type(#fun_t{args=As,type=T}) ->
    Eas = encode_types(As),
    Et = encode_type(T),
    [{<<"function">>,[{<<"arguments">>,Eas},{<<"returns">>,Et}]}].

encode_name(Name) ->
    list_to_binary(Name).

%% encode_field_types(Fields) -> [JSON].
%% encode_field_type(Field) -> JSON.
%%  Encode a record field type.

encode_field_types(Fs) ->
    [ encode_field_type(F) || F <- Fs ].

encode_field_type(#field_t{id=Id,type=T}) ->
    [{<<"name">>,encode_type(Id)},
     {<<"type">>,[encode_type(T)]}].

%% encode_typedef(TypeDef) -> JSON.

encode_typedef(Type) ->
    Name = typedef_name(Type),
    Vars = typedef_vars(Type),
    Def = typedef_def(Type),
    [{<<"name">>, encode_name(Name)},
     {<<"vars">>, encode_tvars(Vars)},
     {<<"typedef">>, encode_alias(Def)}].

encode_tvars(Vars) ->
    [ encode_tvar(V) || V <- Vars ].

encode_tvar(#tvar{name=N}) ->
    [{<<"name">>, encode_name(N)}].

encode_alias(#alias_t{type=T}) ->
    encode_type(T);
encode_alias(A) -> encode_type(A).

%% encode_stmt(Stmt) -> JSON.

encode_stmt(E) ->
    encode_expr(E).

%% encode_exprs(Exprs) -> [JSON].
%% encode_expr(Expr) -> JSON.

encode_exprs(Es) ->
    [ encode_expr(E) || E <- Es ].

encode_expr(#id{name=N}) -> encode_name(N);
encode_expr(#con{name=N}) -> encode_name(N);
encode_expr(#qid{names=Ns}) ->
    encode_name(lists:join(".", Ns));
encode_expr(#qcon{names=Ns}) ->
    encode_name(lists:join(".", Ns));           %?
encode_expr(#typed{expr=E}) ->
    encode_expr(E);
encode_expr(#bool{bool=B}) -> B;
encode_expr(#int{value=V}) -> V;
encode_expr(#string{bin=B}) -> B;
encode_expr(#bytes{bin=B}) -> B;
encode_expr(#tuple{args=As}) ->
    Eas = encode_exprs(As),
    [{<<"tuple">>,Eas}];
encode_expr(#list{args=As}) ->
    Eas = encode_exprs(As),
    [{<<"list">>,Eas}];
encode_expr(#record{fields=Fs}) ->
    Efs = encode_field_exprs(Fs),
    [{<<"record">>,Efs}];
encode_expr(#proj{value=V}) ->
    encode_expr(V);
encode_expr(#app{func=F,args=As}) ->
    Ef = encode_expr(F),
    Eas = encode_exprs(As),
    [{<<"apply">>,[{<<"function">>,Ef},
		   {<<"arguments">>,Eas}]}];
encode_expr({Op,_Ann}) ->
    list_to_binary(atom_to_list(Op)).

%% encode_field_exprs(Fields) -> [JSON].
%% encode_field_expr(Field) -> JSON.
%%  Encode a record field expression.

encode_field_exprs(Fs) ->
    [ encode_field_expr(F) || F <- Fs ].

encode_field_expr(#field{name=[N],value=V}) ->
    [{<<"name">>,encode_expr(N)},
     {<<"value">>,[encode_expr(V)]}].

%% decode(JSON) -> ContractString.
%%  Decode a JSON string and generate a suitable contract string which
%%  can be included in a contract definition. We decode into a map
%%  here as this is easier to work with and order is not important.

decode(Json) ->
    Map = jsx:decode(Json, [return_maps]),
    %% io:format("~p\n", [Map]),
    #{<<"contract">> := C} = Map,
    list_to_binary(decode_contract(C)).

decode_contract(#{<<"name">> := Name,
                  <<"type_defs">> := Ts,
                  <<"functions">> := Fs}) ->
    ["contract"," ",io_lib:format("~s", [Name])," =\n",
     decode_tdefs(Ts),
     decode_funcs(Fs)].

decode_funcs(Fs) -> [ decode_func(F) || F <- Fs ].

decode_func(#{<<"name">> := <<"init">>}) -> [];
decode_func(#{<<"name">> := Name,<<"arguments">> := As,<<"returns">> := T}) ->
    ["  function"," ",io_lib:format("~s", [Name])," : ",
     decode_args(As)," => ",decode_type(T),$\n].

decode_args(As) ->
    Das = [ decode_arg(A) || A <- As ],
    [$(,lists:join(", ", Das),$)].

decode_arg(#{<<"type">> := [T]}) -> decode_type(T).

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
decode_type(#{<<"variant">> := Ets}) ->
    Ts = decode_types(Ets),
    lists:join(" | ", Ts);
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

decode_field(#{<<"name">> := En,<<"type">> := [Et]}) ->
    Name = decode_name(En),
    Type = decode_type(Et),
    [Name," : ",Type].

%% decode_tdefs(Json) -> [TypeString].
%%  Here we are only interested in the type definitions and ignore the
%%  aliases. We find them as they always have variants.

decode_tdefs(Ts) -> [ decode_tdef(T) ||
			#{<<"typedef">> := #{<<"variant">> := _}} = T <- Ts
		    ].

decode_tdef(#{<<"name">> := Name,<<"vars">> := Vs,<<"typedef">> := T}) ->
    ["  datatype"," ",decode_name(Name),decode_tvars(Vs),
     " = ",decode_type(T),$\n].

decode_tvars([]) -> [];                         %No tvars, no parentheses
decode_tvars(Vs) ->
    Dvs = [ decode_tvar(V) || V <- Vs ],
    [$(,lists:join(", ", Dvs),$)].

decode_tvar(#{<<"name">> := N}) -> io_lib:format("~s", [N]).

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
