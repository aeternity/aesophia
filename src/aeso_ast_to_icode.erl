%%%-------------------------------------------------------------------
%%% @author Happi (Erik Stenman)
%%% @copyright (C) 2017, Aeternity Anstalt
%%% @doc
%%%     Compiler from Aeterinty Sophia language to the Aeternity VM, aevm.
%%% @end
%%% Created : 21 Dec 2017
%%%
%%%-------------------------------------------------------------------
-module(aeso_ast_to_icode).

-export([ast_typerep/1, ast_typerep/2, type_value/1,
         convert_typed/2, prim_call/5]).

-include_lib("aebytecode/include/aeb_opcodes.hrl").
-include("aeso_icode.hrl").
-include("aeso_utils.hrl").

-spec convert_typed(aeso_syntax:ast(), list()) -> aeso_icode:icode().
convert_typed(TypedTree, Options) ->
    {Payable, Name} =
        case lists:last(TypedTree) of
            {Contr, Attrs, {con, _, Con}, _} when ?IS_CONTRACT_HEAD(Contr) ->
                {proplists:get_value(payable, Attrs, false), Con};
            Decl ->
                gen_error({last_declaration_must_be_contract, Decl})
           end,
    NewIcode = aeso_icode:set_payable(Payable,
                   aeso_icode:set_name(Name, aeso_icode:new(Options))),
    Icode    = code(TypedTree, NewIcode, Options),
    deadcode_elimination(Icode).

code([{Contract, _Attribs, Con, Code}|Rest], Icode, Options)
  when ?IS_CONTRACT_HEAD(Contract) ->
    NewIcode = contract_to_icode(Code, aeso_icode:set_namespace(Con, Icode)),
    code(Rest, NewIcode, Options);
code([{namespace, _Ann, Name, Code}|Rest], Icode, Options) ->
    %% TODO: nested namespaces
    NewIcode = contract_to_icode(Code, aeso_icode:set_namespace(Name, Icode)),
    code(Rest, NewIcode, Options);
code([], Icode, Options) ->
    add_default_init_function(add_builtins(Icode), Options).

%% Generate error on correct format.

-dialyzer({nowarn_function, gen_error/1}).
gen_error(Error) ->
    aeso_errors:throw(aeso_code_errors:format(Error)).

%% Create default init function (only if state is unit).
add_default_init_function(Icode = #{namespace := NS, functions := Funs, state_type := State}, Options) ->
    NoCode        = proplists:get_value(no_code, Options, false),
    {_, _, QInit} = aeso_icode:qualify({id, [], "init"}, Icode),
    case lists:keymember(QInit, 1, Funs) of
        true -> Icode;
        false when NoCode -> Icode;
        false when State /= {tuple, []} ->
            gen_error({missing_init_function, NS});
        false ->
            Type  = {tuple, [typerep, {tuple, []}]},
            Value = #tuple{ cpts = [type_value({tuple, []}), {tuple, []}] },
            DefaultInit = {QInit, [], [], Value, Type},
            Icode#{ functions => [DefaultInit | Funs] }
    end.

-spec contract_to_icode(aeso_syntax:ast(), aeso_icode:icode()) ->
                               aeso_icode:icode().
contract_to_icode([{namespace, _, Name, Defs} | Rest], Icode) ->
    NS = aeso_icode:get_namespace(Icode),
    Icode1 = contract_to_icode(Defs, aeso_icode:enter_namespace(Name, Icode)),
    contract_to_icode(Rest, aeso_icode:set_namespace(NS, Icode1));
contract_to_icode([Decl = {type_def, _Attrib, Id = {id, _, Name}, Args, Def} | Rest],
                  Icode = #{ types := Types, constructors := Constructors }) ->
    TypeDef = make_type_def(Args, Def, Icode),
    NewConstructors =
        case Def of
            {variant_t, Cons} ->
                Tags = lists:seq(0, length(Cons) - 1),
                GetName = fun({constr_t, _, C, _}) -> C end,
                QName = fun(Con) -> {_, _, Xs} = aeso_icode:qualify(GetName(Con), Icode), Xs end,
                maps:from_list([ {QName(Con), Tag} || {Tag, Con} <- lists:zip(Tags, Cons) ]);
            _ -> #{}
        end,
    {_, _, TName} = aeso_icode:qualify(Id, Icode),
    Icode1 = Icode#{ types := Types#{ TName => TypeDef },
                     constructors := maps:merge(Constructors, NewConstructors) },
    Icode2 = case Name of
                "state" when Args == [] ->
                     case is_first_order_type(Def) of
                         true  -> Icode1#{ state_type => ast_typerep(Def, Icode) };
                         false -> gen_error({higher_order_state, Decl})
                     end;
                "state"                 -> gen_error({parameterized_state, Id});
                "event" when Args == [] -> Icode1#{ event_type => Def };
                "event"                 -> gen_error({parameterized_event, Id});
                _                       -> Icode1
             end,
    contract_to_icode(Rest, Icode2);
contract_to_icode([{letfun, Attrib, Name, Args, _What, Body={typed,_,_,T}}|Rest], Icode) ->
    FunAttrs = [ stateful || proplists:get_value(stateful, Attrib, false) ] ++
               [ payable  || proplists:get_value(payable, Attrib, false) ] ++
               [ private  || is_private(Attrib, Icode) ],
    [ check_entrypoint_type(Attrib, Name, Args, T)
      || aeso_syntax:get_ann(entrypoint, Attrib, false) ],
    %% TODO: Handle types
    FunName = ast_id(Name),
    %% TODO: push funname to env
    FunArgs = ast_args(Args, [], Icode),
    %% TODO: push args to env
    {FunBody, TypeRep} =
        case FunName of
            "init" ->
                %% Pair the initial state with a typerep for the state (TODO: until we have the state type in some contract metadata)
                #{ state_type := StateType } = Icode,
                {#tuple{ cpts = [type_value(StateType), ast_body(Body, Icode)] },
                 {tuple, [typerep, ast_typerep(T, Icode)]}};
            _ -> {ast_body(Body, Icode), ast_typerep1(T, Icode)}
        end,
    QName    = aeso_icode:qualify(Name, Icode),
    NewIcode = ast_fun_to_icode(ast_id(QName), FunAttrs, FunArgs, FunBody, TypeRep, Icode),
    contract_to_icode(Rest, NewIcode);
contract_to_icode([], Icode) -> Icode;
contract_to_icode([{fun_decl, _, Id, _} | Code], Icode = #{ options := Options }) ->
    NoCode = proplists:get_value(no_code, Options, false),
    case aeso_icode:in_main_contract(Icode) andalso not NoCode of
        true  -> gen_error({missing_definition, Id});
        false -> contract_to_icode(Code, Icode)
    end;
contract_to_icode([Decl | Code], Icode) ->
    io:format("Unhandled declaration: ~p\n", [Decl]),
    contract_to_icode(Code, Icode).

ast_id({id, _, Id}) -> Id;
ast_id({qid, _, Id}) -> Id.

ast_args([{typed, _, Name, Type}|Rest], Acc, Icode) ->
    ast_args(Rest, [{ast_id(Name), ast_typerep1(Type, Icode)}| Acc], Icode);
ast_args([], Acc, _Icode) -> lists:reverse(Acc).

ast_type(T, Icode) ->
    ast_typerep(T, Icode).

-define(id_app(Fun, Args, ArgTypes, OutType),
    {app, _, {typed, _, {id, _, Fun}, {fun_t, _, _, ArgTypes, OutType}}, Args}).

-define(qid_app(Fun, Args, ArgTypes, OutType),
    {app, _, {typed, _, {qid, _, Fun}, {fun_t, _, _, ArgTypes, OutType}}, Args}).

-define(oracle_t(Q, R), {app_t, _, {id, _, "oracle"}, [Q, R]}).
-define(query_t(Q, R),  {app_t, _, {id, _, "oracle_query"}, [Q, R]}).
-define(option_t(A),    {app_t, _, {id, _, "option"}, [A]}).
-define(map_t(K, V),    {app_t, _, {id, _, "map"}, [K, V]}).

%% Chain environment
ast_body({qid, _, ["Contract", "address"]}, _Icode)      -> prim_contract_address;
ast_body({qid, _, ["Contract", "creator"]}, _Icode)      -> prim_contract_creator;
ast_body({qid, _, ["Contract", "balance"]}, _Icode)      -> #prim_balance{ address = prim_contract_address };
ast_body({qid, _, ["Call",     "origin"]}, _Icode)       -> prim_call_origin;
ast_body({qid, _, ["Call",     "caller"]}, _Icode)       -> prim_caller;
ast_body({qid, _, ["Call",     "value"]}, _Icode)        -> prim_call_value;
ast_body({qid, _, ["Call",     "gas_price"]}, _Icode)    -> prim_gas_price;
ast_body({qid, _, ["Chain",    "coinbase"]}, _Icode)     -> prim_coinbase;
ast_body({qid, _, ["Chain",    "timestamp"]}, _Icode)    -> prim_timestamp;
ast_body({qid, _, ["Chain",    "block_height"]}, _Icode) -> prim_block_height;
ast_body({qid, _, ["Chain",    "difficulty"]}, _Icode)   -> prim_difficulty;
ast_body({qid, _, ["Chain",    "gas_limit"]}, _Icode)    -> prim_gas_limit;

%% State
ast_body({qid, _, [Con, "state"]}, #{ contract_name := Con }) -> prim_state;
ast_body(?qid_app([Con, "put"], [NewState], _, _), Icode = #{ contract_name := Con }) ->
    #prim_put{ state = ast_body(NewState, Icode) };
ast_body({typed, _, Id = {qid, _, [Con, "put"]}, Type}, Icode = #{ contract_name := Con }) ->
    eta_expand(Id, Type, Icode);

%% Authentication
ast_body({qid, _, ["Auth", "tx_hash"]}, _Icode) ->
    prim_call(?PRIM_CALL_AUTH_TX_HASH, #integer{value = 0},
              [], [], aeso_icode:option_typerep(word));

%% Maps

%% -- map lookup  m[k]
ast_body({map_get, _, Map, Key}, Icode) ->
    {_, ValType} = check_monomorphic_map(Map, Icode),
    Fun = {map_get, ast_typerep(ValType, Icode)},
    builtin_call(Fun, [ast_body(Map, Icode), ast_body(Key, Icode)]);
%% -- map lookup_default  m[k = v]
ast_body({map_get, _, Map, Key, Val}, Icode) ->
    {_, ValType} = check_monomorphic_map(Map, Icode),
    Fun = {map_lookup_default, ast_typerep(ValType, Icode)},
    builtin_call(Fun, [ast_body(Map, Icode), ast_body(Key, Icode), ast_body(Val, Icode)]);

%% -- map construction { k1 = v1, k2 = v2 }
ast_body({typed, Ann, {map, _, KVs}, MapType}, Icode) ->
    {KeyType, ValType} = check_monomorphic_map(Ann, MapType, Icode),
    lists:foldr(fun({K, V}, Map) ->
                    builtin_call(map_put, [Map, ast_body(K, Icode), ast_body(V, Icode)])
                end, map_empty(KeyType, ValType, Icode), KVs);

%% -- map update       m { [k] = v } or m { [k] @ x = f(x) } or m { [k = v] @ x = f(x) }
ast_body({map, _, Map, []}, Icode) -> ast_body(Map, Icode);
ast_body({map, _, Map, [Upd]}, Icode) ->
    case Upd of
        {field, _, [{map_get, _, Key}], Val} ->
            map_put(Key, Val, Map, Icode);
        {field_upd, _, [{map_get, _, Key}], ValFun} ->
            map_upd(Key, ValFun, Map, Icode);
        {field_upd, _, [{map_get, _, Key, Val}], ValFun} ->
            map_upd(Key, Val, ValFun, Map, Icode)
    end;
ast_body({map, Ann, Map, [Upd | Upds]}, Icode) ->
    ast_body({map, Ann, {map, Ann, Map, [Upd]}, Upds}, Icode);

%% -- Bits
ast_body({qid, _, ["Bits", "none"]}, _Icode) ->
    #integer{ value = 0 };
ast_body({qid, _, ["Bits", "all"]}, _Icode) ->
    #integer{ value = 1 bsl 256 - 1 };

%% -- Conversion

%% Other terms
ast_body({id, _, Name}, _Icode) ->
    #var_ref{name = Name};
ast_body({typed, _, Id = {qid, _, _}, Type}, Icode) ->
    case is_builtin_fun(Id, Icode) of
        true  -> eta_expand(Id, Type, Icode);
        false -> ast_body(Id, Icode)
    end;
ast_body({qid, _, Name}, _Icode) ->
    #var_ref{name = Name};
ast_body({bool, _, Bool}, _Icode) ->        %BOOL as ints
    Value = if Bool -> 1 ; true -> 0 end,
    #integer{value = Value};
ast_body({int, _, Value}, _Icode) ->
    #integer{value = Value};
ast_body({char, _, Value}, _Icode) ->
    #integer{value = Value};
ast_body({bytes, _, Bin}, _Icode) ->
    case aeb_memory:binary_to_words(Bin) of
        [Word] -> #integer{value = Word};
        Words  -> #tuple{cpts = [#integer{value = W} || W <- Words]}
    end;
ast_body({Key, _, Bin}, _Icode) when Key == account_pubkey;
                                     Key == contract_pubkey;
                                     Key == oracle_pubkey;
                                     Key == oracle_query_id ->
    <<Value:32/unit:8>> = Bin,
    #integer{value = Value};
ast_body({string,_,Bin}, _Icode) ->
    Cpts = [size(Bin) | aeb_memory:binary_to_words(Bin)],
    #tuple{cpts = [#integer{value=X} || X <- Cpts]};
ast_body({tuple,_,Args}, Icode) ->
    #tuple{cpts = [ast_body(A, Icode) || A <- Args]};
ast_body({list,_,Args}, Icode) ->
    #list{elems = [ast_body(A, Icode) || A <- Args]};
%% Typed contract calls
ast_body({proj, _, {typed, _, Addr, {con, _, _}}, {id, _, "address"}}, Icode) ->
    ast_body(Addr, Icode);  %% Values of contract types _are_ addresses.
ast_body({app, _, {typed, _, {proj, _, Addr, {id, _, FunName}},
                             {fun_t, _, NamedT, ArgsT, OutT}}, Args0}, Icode) ->
    NamedArgs = [Arg || Arg = {named_arg, _, _, _} <- Args0],
    Args      = Args0 -- NamedArgs,
    ArgOpts   = [ {Name, ast_body(Value, Icode)}   || {named_arg,   _, {id, _, Name}, Value} <- NamedArgs ],
    Defaults  = [ {Name, ast_body(Default, Icode)} || {named_arg_t, _, {id, _, Name}, _, Default} <- NamedT ],
    ArgsI = [ ast_body(Arg, Icode) || Arg <- Args ],
    ArgType = ast_typerep({tuple_t, [], ArgsT}),
    Gas    = proplists:get_value("gas",   ArgOpts ++ Defaults),
    Value  = proplists:get_value("value", ArgOpts ++ Defaults),
    OutType = ast_typerep(OutT, Icode),
    <<TypeHash:256>> = aeb_aevm_abi:function_type_hash(list_to_binary(FunName), ArgType, OutType),
    %% The function is represented by its type hash (which includes the name)
    Fun    = #integer{value = TypeHash},
    #prim_call_contract{
        address  = ast_body(Addr, Icode),
        gas      = Gas,
        value    = Value,
        arg      = #tuple{cpts = [Fun, #tuple{ cpts = ArgsI }]},
       %% The type check is implicitly done by using the type hash as the
       %% entrypoint on the callee side.
        type_hash= #integer{value = 0}
      };
ast_body({proj, _, Con = {typed, _, _, {con, _, _}}, _Fun}, _Icode) ->
    gen_error({unapplied_contract_call, Con});

ast_body({con, _, Name}, Icode) ->
    Tag = aeso_icode:get_constructor_tag([Name], Icode),
    #tuple{cpts = [#integer{value = Tag}]};
ast_body({qcon, _, Name}, Icode) ->
    Tag = aeso_icode:get_constructor_tag(Name, Icode),
    #tuple{cpts = [#integer{value = Tag}]};
ast_body({app, _, {typed, _, {con, _, Name}, _}, Args}, Icode) ->
    Tag = aeso_icode:get_constructor_tag([Name], Icode),
    #tuple{cpts = [#integer{value = Tag} | [ ast_body(Arg, Icode) || Arg <- Args ]]};
ast_body({app, _, {typed, _, {qcon, _, Name}, _}, Args}, Icode) ->
    Tag = aeso_icode:get_constructor_tag(Name, Icode),
    #tuple{cpts = [#integer{value = Tag} | [ ast_body(Arg, Icode) || Arg <- Args ]]};
ast_body({app, _, {'..', _}, [A, B]}, Icode) ->
    #funcall
    { function = #var_ref{ name = ["ListInternal", "from_to"] }
    , args     = [ast_body(A, Icode), ast_body(B, Icode)] };
ast_body({app, As, Fun, Args}, Icode) ->
    case aeso_syntax:get_ann(format, As) of
        infix  ->
            {typed, _, {Op, _}, _} = Fun,
            [A, B] = Args,
            ast_binop(Op, As, A, B, Icode);
        prefix ->
            {typed, _, {Op, _}, _} = Fun,
            [A] = Args,
            #unop{op = Op, rand = ast_body(A, Icode)};
        _ ->
            {typed, _, Fun1, {fun_t, _, _, ArgsT, RetT}} = Fun,
            case is_builtin_fun(Fun1, Icode) of
                true  -> builtin_code(As, Fun1, Args, ArgsT, RetT, Icode);
                false ->
                    #funcall{function=ast_body(Fun, Icode),
                             args=[ast_body(A, Icode) || A <- Args]}
            end
    end;
ast_body({list_comp, _, Yield, []}, Icode) ->
    #list{elems = [ast_body(Yield, Icode)]};
ast_body({list_comp, As, Yield, [{comprehension_bind, {typed, _, Pat, ArgType}, BindExpr}|Rest]}, Icode) ->
    Arg  = "%lc",
    Body = {switch, As, {typed, As, {id, As, Arg}, ArgType},
                [{'case', As, Pat, {list_comp, As, Yield, Rest}},
                 {'case', As, {id, As, "_"}, {list, As, []}}]},
    #funcall
        { function = #var_ref{ name = ["ListInternal", "flat_map"] }
        , args =
              [ #lambda{ args=[#arg{name = Arg, type = ast_type(ArgType, Icode)}]
                       , body = ast_body(Body, Icode)
                       }
              , ast_body(BindExpr, Icode)
              ]
        };
ast_body({list_comp, As, Yield, [{comprehension_if, AsIF, Cond}|Rest]}, Icode) ->
    ast_body({'if', AsIF, Cond, {list_comp, As, Yield, Rest}, {list, As, []}}, Icode);
ast_body({list_comp, As, Yield, [LV = {letval, _, _, _}|Rest]}, Icode) ->
    ast_body({block, As, [LV, {list_comp, As, Yield, Rest}]}, Icode);
ast_body({list_comp, As, Yield, [LF = {letfun, _, _, _, _, _}|Rest]}, Icode) ->
    ast_body({block, As, [LF, {list_comp, As, Yield, Rest}]}, Icode);
ast_body({'if',_,Dec,Then,Else}, Icode) ->
    #ifte{decision = ast_body(Dec, Icode)
         ,then     = ast_body(Then, Icode)
         ,else     = ast_body(Else, Icode)};
ast_body({switch,_,A,Cases}, Icode) ->
    %% let's assume the parser has already ensured that only valid
    %% patterns appear in cases.
    #switch{expr=ast_body(A, Icode),
            cases=[{ast_body(Pat, Icode),ast_body(Body, Icode)}
              || {'case',_,Pat,Body} <- Cases]};
ast_body({block, As, [{letval, _, Pat, E} | Rest]}, Icode) ->
    E1    = ast_body(E, Icode),
    Pat1  = ast_body(Pat, Icode),
    Rest1 = ast_body({block, As, Rest}, Icode),
    #switch{expr  = E1,
            cases = [{Pat1, Rest1}]};
ast_body({block, As, [{letfun, Ann, F, Args, _Type, Expr} | Rest]}, Icode) ->
    ToArg   = fun({typed, Ann1, Id, T}) -> {arg, Ann1, Id, T} end,    %% Pattern matching has been desugared
    LamArgs = lists:map(ToArg, Args),
    ast_body({block, As, [{letval, Ann, F, {lam, Ann, LamArgs, Expr}} | Rest]}, Icode);
ast_body({block,_,[]}, _Icode) ->
    #tuple{cpts=[]};
ast_body({block,_,[E]}, Icode) ->
    ast_body(E, Icode);
ast_body({block,As,[E|Rest]}, Icode) ->
    #switch{expr=ast_body(E, Icode),
            cases=[{#var_ref{name="_"},ast_body({block,As,Rest}, Icode)}]};
ast_body({lam,_,Args,Body}, Icode) ->
    #lambda{args=[#arg{name = ast_id(P), type = ast_typerep1(T, Icode)} || {arg,_,P,T} <- Args],
            body=ast_body(Body, Icode)};
ast_body({typed,_,{record,Attrs,Fields},{record_t,DefFields}}, Icode) ->
    %% Compile as a tuple with the fields in the order they appear in the definition.
    NamedField = fun({field, _, [{proj, _, {id, _, Name}}], E}) -> {Name, E} end,
    NamedFields = lists:map(NamedField, Fields),
    #tuple{cpts =
               [case proplists:get_value(Name, NamedFields) of
                    undefined ->
                        Line = aeso_syntax:get_ann(line, Attrs),
                        #missing_field{format = "Missing field in record: ~s (on line ~p)\n",
                        args = [Name,Line]};
                    E ->
                        ast_body(E, Icode)
                end
                || {field_t,_,{id,_,Name},_} <- DefFields]};
ast_body({proj,_,{typed,_,Record,{record_t,Fields}},{id,_,FieldName}}, Icode) ->
    [Index] = [I
              || {I,{field_t,_,{id,_,Name},_}} <-
                  lists:zip(lists:seq(1,length(Fields)),Fields),
              Name==FieldName],
    #binop{op = '!', left = #integer{value = 32*(Index-1)}, right = ast_body(Record, Icode)};
ast_body({record, Attrs, {typed, _, Record, RecType={record_t, Fields}}, Update}, Icode) ->
    UpdatedName = fun({field, _,     [{proj, _, {id, _, Name}}], _}) -> Name;
                     ({field_upd, _, [{proj, _, {id, _, Name}}], _}) -> Name
                  end,
    UpdatedNames = lists:map(UpdatedName, Update),
    Rec = {typed, Attrs, {id, Attrs, "_record"}, RecType},
    CompileUpdate =
        fun(Fld={field, _, _, _}) -> Fld;
           ({field_upd, Ann, LV=[{proj, Ann1, P}], Fun}) ->
            {field, Ann, LV, {app, Ann, Fun, [{proj, Ann1, Rec, P}]}}
        end,

    #switch{expr=ast_body(Record, Icode),
            cases=[{#var_ref{name = "_record"},
                ast_body({typed, Attrs,
                      {record, Attrs,
                      lists:map(CompileUpdate, Update) ++
                    [{field, Attrs, [{proj, Attrs, {id, Attrs, Name}}],
                        {proj, Attrs, Rec, {id, Attrs, Name}}}
                        || {field_t, _, {id, _, Name}, _} <- Fields,
                          not lists:member(Name, UpdatedNames)]},
                      RecType}, Icode)}
              ]};
ast_body({typed, _, Body, _}, Icode) ->
    ast_body(Body, Icode).

ast_binop(Op, Ann, {typed, _, A, Type}, B, Icode)
    when Op == '=='; Op == '!=';
         Op == '<';  Op == '>';
         Op == '<='; Op == '=<'; Op == '>=' ->
    [ gen_error({cant_compare_type_aevm, Ann, Op, Type}) || not is_simple_type(Type) ],
    case ast_typerep(Type, Icode) of
        word   -> #binop{op = Op, left = ast_body(A, Icode), right = ast_body(B, Icode)};
        OtherType ->
            Neg = case Op of
                    '==' -> fun(X) -> X end;
                    '!=' -> fun(X) -> #unop{ op = '!', rand = X } end;
                    _    -> gen_error({cant_compare_type_aevm, Ann, Op, Type})
                  end,
            Args = [ast_body(A, Icode), ast_body(B, Icode)],
            Builtin =
                case OtherType of
                    string ->
                        builtin_call(str_equal, Args);
                    {tuple, Types} ->
                        case lists:usort(Types) of
                            [word] ->
                                builtin_call(str_equal_p, [ #integer{value = 32 * length(Types)} | Args]);
                            _ -> gen_error({cant_compare_type_aevm, Ann, Op, Type})
                        end;
                    _ ->
                        gen_error({cant_compare_type_aevm, Ann, Op, Type})
                end,
            Neg(Builtin)
    end;
ast_binop('++', _, A, B, Icode) ->
    builtin_call(list_concat, [ast_body(A, Icode), ast_body(B, Icode)]);
ast_binop(Op, _, A, B, Icode) ->
    #binop{op = Op, left = ast_body(A, Icode), right = ast_body(B, Icode)}.

is_builtin_fun({qid, _, ["Chain","spend"]}, _Icode)                          -> true;
is_builtin_fun({qid, _, [Con, "Chain", "event"]}, #{ contract_name := Con }) -> true;
is_builtin_fun({qid, _, ["Chain", "balance"]}, _Icode)                       -> true;
is_builtin_fun({qid, _, ["Chain", "block_hash"]}, _Icode)                    -> true;
is_builtin_fun({qid, _, ["Call", "gas_left"]}, _Icode)                       -> true;
is_builtin_fun({id, _, "abort"}, _Icode)                                     -> true;
is_builtin_fun({id, _, "require"}, _Icode)                                   -> true;
is_builtin_fun({qid, _, ["Oracle", "register"]}, _Icode)                     -> true;
is_builtin_fun({qid, _, ["Oracle", "query_fee"]}, _Icode)                    -> true;
is_builtin_fun({qid, _, ["Oracle", "query"]}, _Icode)                        -> true;
is_builtin_fun({qid, _, ["Oracle", "extend"]}, _Icode)                       -> true;
is_builtin_fun({qid, _, ["Oracle", "respond"]}, _Icode)                      -> true;
is_builtin_fun({qid, _, ["Oracle", "get_question"]}, _Icode)                 -> true;
is_builtin_fun({qid, _, ["Oracle", "get_answer"]}, _Icode)                   -> true;
is_builtin_fun({qid, _, ["Oracle", "check"]}, _Icode)                        -> true;
is_builtin_fun({qid, _, ["Oracle", "check_query"]}, _Icode)                  -> true;
is_builtin_fun({qid, _, ["AENS", "resolve"]}, _Icode)                        -> true;
is_builtin_fun({qid, _, ["AENS", "preclaim"]}, _Icode)                       -> true;
is_builtin_fun({qid, _, ["AENS", "claim"]}, _Icode)                          -> true;
is_builtin_fun({qid, _, ["AENS", "transfer"]}, _Icode)                       -> true;
is_builtin_fun({qid, _, ["AENS", "revoke"]}, _Icode)                         -> true;
is_builtin_fun({qid, _, ["AENS", "update"]}, _Icode)                         -> true;
is_builtin_fun({qid, _, ["Map", "lookup"]}, _Icode)                          -> true;
is_builtin_fun({qid, _, ["Map", "lookup_default"]}, _Icode)                  -> true;
is_builtin_fun({qid, _, ["Map", "member"]}, _Icode)                          -> true;
is_builtin_fun({qid, _, ["Map", "size"]}, _Icode)                            -> true;
is_builtin_fun({qid, _, ["Map", "delete"]}, _Icode)                          -> true;
is_builtin_fun({qid, _, ["Map", "from_list"]}, _Icode)                       -> true;
is_builtin_fun({qid, _, ["Map", "to_list"]}, _Icode)                         -> true;
is_builtin_fun({qid, _, ["Crypto", "verify_sig"]}, _Icode)                   -> true;
is_builtin_fun({qid, _, ["Crypto", "verify_sig_secp256k1"]}, _Icode)         -> true;
is_builtin_fun({qid, _, ["Crypto", "ecverify_secp256k1"]}, _Icode)           -> true;
is_builtin_fun({qid, _, ["Crypto", "ecrecover_secp256k1"]}, _Icode)          -> true;
is_builtin_fun({qid, _, ["Crypto", "sha3"]}, _Icode)                         -> true;
is_builtin_fun({qid, _, ["Crypto", "sha256"]}, _Icode)                       -> true;
is_builtin_fun({qid, _, ["Crypto", "blake2b"]}, _Icode)                      -> true;
is_builtin_fun({qid, _, ["String", "sha256"]}, _Icode)                       -> true;
is_builtin_fun({qid, _, ["String", "blake2b"]}, _Icode)                      -> true;
is_builtin_fun({qid, _, ["String", "length"]}, _Icode)                       -> true;
is_builtin_fun({qid, _, ["String", "concat"]}, _Icode)                       -> true;
is_builtin_fun({qid, _, ["String", "sha3"]}, _Icode)                         -> true;
is_builtin_fun({qid, _, ["Bits", "test"]}, _Icode)                           -> true;
is_builtin_fun({qid, _, ["Bits", "set"]}, _Icode)                            -> true;
is_builtin_fun({qid, _, ["Bits", "clear"]}, _Icode)                          -> true;
is_builtin_fun({qid, _, ["Bits", "union"]}, _Icode)                          -> true;
is_builtin_fun({qid, _, ["Bits", "intersection"]}, _Icode)                   -> true;
is_builtin_fun({qid, _, ["Bits", "difference"]}, _Icode)                     -> true;
is_builtin_fun({qid, _, ["Bits", "sum"]}, _Icode)                            -> true;
is_builtin_fun({qid, _, ["Int", "to_str"]}, _Icode)                          -> true;
is_builtin_fun({qid, _, ["Address", "to_str"]}, _Icode)                      -> true;
is_builtin_fun({qid, _, ["Address", "is_oracle"]}, _Icode)                   -> true;
is_builtin_fun({qid, _, ["Address", "is_contract"]}, _Icode)                 -> true;
is_builtin_fun({qid, _, ["Address", "is_payable"]}, _Icode)                  -> true;
is_builtin_fun({qid, _, ["Address", "to_contract"]}, _Icode)                 -> true;
is_builtin_fun({qid, _, ["Bytes", "to_int"]}, _Icode)                        -> true;
is_builtin_fun({qid, _, ["Bytes", "to_str"]}, _Icode)                        -> true;
is_builtin_fun({qid, _, ["Bytes", "concat"]}, _Icode)                        -> true;
is_builtin_fun({qid, _, ["Bytes", "split"]}, _Icode)                         -> true;
is_builtin_fun(_, _)                                                         -> false.

%% -- Code generation for builtin functions --

%% Chain operations
builtin_code(_, {qid, _, ["Chain","spend"]}, [To, Amount], _, _, Icode) ->
    prim_call(?PRIM_CALL_SPEND, ast_body(Amount, Icode), [ast_body(To, Icode)], [word], {tuple, []});

builtin_code(_, {qid, _, [Con, "Chain", "event"]}, [Event], _, _, Icode = #{ contract_name := Con }) ->
    aeso_builtins:check_event_type(Icode),
    builtin_call({event, maps:get(event_type, Icode)}, [ast_body(Event, Icode)]);

builtin_code(_, {qid, _, ["Chain", "balance"]}, [Address], _, _, Icode) ->
    #prim_balance{ address = ast_body(Address, Icode) };
builtin_code(_, {qid, _, ["Chain", "block_hash"]}, [Height], _, _, Icode) ->
    builtin_call(block_hash, [ast_body(Height, Icode)]);
builtin_code(_, {qid, _, ["Call", "gas_left"]}, [], _, _, _Icode) ->
    prim_gas_left;

%% Abort
builtin_code(_, {id, _, "abort"}, [String], _, _, Icode) ->
    builtin_call(abort, [ast_body(String, Icode)]);
builtin_code(_, {id, _, "require"}, [Bool, String], _, _, Icode) ->
    builtin_call(require, [ast_body(Bool, Icode), ast_body(String, Icode)]);

%% Oracles
builtin_code(_, {qid, Ann, ["Oracle", "register"]}, Args, _, OracleType = ?oracle_t(QType, RType), Icode) ->
    check_oracle_type(Ann, OracleType),
    {Sign, [Acct, QFee, TTL]} = get_signature_arg(Args),
    prim_call(?PRIM_CALL_ORACLE_REGISTER, #integer{value = 0},
              [ast_body(Acct, Icode), ast_body(Sign, Icode), ast_body(QFee, Icode), ast_body(TTL, Icode),
               ast_type_value(QType, Icode), ast_type_value(RType, Icode)],
              [word, sign_t(), word, ttl_t(Icode), typerep, typerep], word);

builtin_code(_, {qid, _, ["Oracle", "query_fee"]}, [Oracle], [_], _, Icode) ->
    prim_call(?PRIM_CALL_ORACLE_QUERY_FEE, #integer{value = 0},
              [ast_body(Oracle, Icode)], [word], word);

builtin_code(_, {qid, Ann, ["Oracle", "query"]}, [Oracle, Q, QFee, QTTL, RTTL], [OracleType, QType, _, _, _], _, Icode) ->
    check_oracle_type(Ann, OracleType),
    prim_call(?PRIM_CALL_ORACLE_QUERY, ast_body(QFee, Icode),
              [ast_body(Oracle, Icode), ast_body(Q, Icode), ast_body(QTTL, Icode), ast_body(RTTL, Icode)],
              [word, ast_type(QType, Icode), ttl_t(Icode), ttl_t(Icode)], word);

builtin_code(_, {qid, _, ["Oracle", "extend"]}, Args, [_, _], _, Icode) ->
    {Sign, [Oracle, TTL]} = get_signature_arg(Args),
    prim_call(?PRIM_CALL_ORACLE_EXTEND, #integer{value = 0},
              [ast_body(Oracle, Icode), ast_body(Sign, Icode), ast_body(TTL, Icode)],
              [word, sign_t(), ttl_t(Icode)], {tuple, []});

builtin_code(_, {qid, Ann, ["Oracle", "respond"]}, Args, [OracleType, _, RType], _, Icode) ->
    check_oracle_type(Ann, OracleType),
    {Sign, [Oracle, Query, R]} = get_signature_arg(Args),
    prim_call(?PRIM_CALL_ORACLE_RESPOND, #integer{value = 0},
              [ast_body(Oracle, Icode), ast_body(Query, Icode), ast_body(Sign, Icode), ast_body(R, Icode)],
              [word, word, sign_t(), ast_type(RType, Icode)], {tuple, []});

builtin_code(_, {qid, Ann, ["Oracle", "get_question"]}, [Oracle, Q], [OracleType, ?query_t(QType, _)], _, Icode) ->
    check_oracle_type(Ann, OracleType),
    prim_call(?PRIM_CALL_ORACLE_GET_QUESTION, #integer{value = 0},
              [ast_body(Oracle, Icode), ast_body(Q, Icode)], [word, word], ast_type(QType, Icode));

builtin_code(_, {qid, Ann, ["Oracle", "get_answer"]}, [Oracle, Q], [OracleType, ?query_t(_, RType)], _, Icode) ->
    check_oracle_type(Ann, OracleType),
    prim_call(?PRIM_CALL_ORACLE_GET_ANSWER, #integer{value = 0},
              [ast_body(Oracle, Icode), ast_body(Q, Icode)], [word, word], aeso_icode:option_typerep(ast_type(RType, Icode)));

builtin_code(_, {qid, Ann, ["Oracle", "check"]}, [Oracle], [OracleType = ?oracle_t(Q, R)], _, Icode) ->
    check_oracle_type(Ann, OracleType),
    prim_call(?PRIM_CALL_ORACLE_CHECK, #integer{value = 0},
              [ast_body(Oracle, Icode), ast_type_value(Q, Icode), ast_type_value(R, Icode)],
              [word, typerep, typerep], word);

builtin_code(_, {qid, Ann, ["Oracle", "check_query"]}, [Oracle, Query], [OracleType, ?query_t(Q, R)], _, Icode) ->
    check_oracle_type(Ann, OracleType),
    prim_call(?PRIM_CALL_ORACLE_CHECK_QUERY, #integer{value = 0},
              [ast_body(Oracle, Icode), ast_body(Query, Icode),
               ast_type_value(Q, Icode), ast_type_value(R, Icode)],
              [word, typerep, typerep], word);

%% Name service
builtin_code(_, {qid, Ann, ["AENS", "resolve"]}, [Name, Key], _, ?option_t(Type), Icode) ->
    case is_monomorphic(Type) of
        true ->
            case ast_type(Type, Icode) of
                T when T == word; T == string -> ok;
                _ -> gen_error({invalid_aens_resolve_type, Ann, Type})
            end,
            prim_call(?PRIM_CALL_AENS_RESOLVE, #integer{value = 0},
                      [ast_body(Name, Icode), ast_body(Key, Icode), ast_type_value(Type, Icode)],
                      [string, string, typerep], aeso_icode:option_typerep(ast_type(Type, Icode)));
        false ->
            gen_error({invalid_aens_resolve_type, Ann, Type})
    end;

builtin_code(_, {qid, _, ["AENS", "preclaim"]}, Args, _, _, Icode) ->
    {Sign, [Addr, CHash]} = get_signature_arg(Args),
    prim_call(?PRIM_CALL_AENS_PRECLAIM, #integer{value = 0},
              [ast_body(Addr, Icode), ast_body(CHash, Icode), ast_body(Sign, Icode)],
              [word, word, sign_t()], {tuple, []});

builtin_code(_, {qid, _, ["AENS", "claim"]}, Args, _, _, Icode) ->
    {Sign, [Addr, Name, Salt, NameFee]} = get_signature_arg(Args),
    prim_call(?PRIM_CALL_AENS_CLAIM, #integer{value = 0},
              [ast_body(Addr, Icode), ast_body(Name, Icode), ast_body(Salt, Icode), ast_body(NameFee, Icode), ast_body(Sign, Icode)],
              [word, string, word, word, sign_t()], {tuple, []});

builtin_code(_, {qid, _, ["AENS", "transfer"]}, Args, _, _, Icode) ->
    {Sign, [FromAddr, ToAddr, Name]} = get_signature_arg(Args),
    prim_call(?PRIM_CALL_AENS_TRANSFER, #integer{value = 0},
              [ast_body(FromAddr, Icode), ast_body(ToAddr, Icode), ast_body(Name, Icode), ast_body(Sign, Icode)],
              [word, word, word, sign_t()], {tuple, []});

builtin_code(_, {qid, _, ["AENS", "revoke"]}, Args, _, _, Icode) ->
    {Sign, [Addr, Name]} = get_signature_arg(Args),
    prim_call(?PRIM_CALL_AENS_REVOKE, #integer{value = 0},
              [ast_body(Addr, Icode), ast_body(Name, Icode), ast_body(Sign, Icode)],
              [word, word, sign_t()], {tuple, []});

builtin_code(_, {qid, _, ["AENS", "update"]}, Args, _, _, Icode) ->
    {Sign, [Addr, Name, TTL, ClientTTL, Pointers]} = get_signature_arg(Args),
    prim_call(?PRIM_CALL_AENS_UPDATE, #integer{value = 0},
              [ast_body(Addr, Icode), ast_body(Name, Icode), ast_body(TTL, Icode), ast_body(ClientTTL, Icode), ast_body(Pointers, Icode), ast_body(Sign, Icode)],
              [word, string, word, word, word, sign_t()], {tuple, []});

%% -- Maps
%% -- lookup functions
builtin_code(_, {qid, _, ["Map", "lookup"]}, [Key, Map], _, _, Icode) ->
    map_get(Key, Map, Icode);
builtin_code(_, {qid, _, ["Map", "lookup_default"]}, [Key, Map, Val], _, _, Icode) ->
    {_, ValType} = check_monomorphic_map(Map, Icode),
    Fun = {map_lookup_default, ast_typerep(ValType, Icode)},
    builtin_call(Fun, [ast_body(Map, Icode), ast_body(Key, Icode), ast_body(Val, Icode)]);
builtin_code(_, {qid, _, ["Map", "member"]}, [Key, Map], _, _, Icode) ->
    builtin_call(map_member, [ast_body(Map, Icode), ast_body(Key, Icode)]);
builtin_code(_, {qid, _, ["Map", "size"]}, [Map], _, _, Icode) ->
    builtin_call(map_size, [ast_body(Map, Icode)]);
builtin_code(_, {qid, _, ["Map", "delete"]}, [Key, Map], _, _, Icode) ->
    map_del(Key, Map, Icode);

%% -- map conversion to/from list
builtin_code(_, {qid, Ann, ["Map", "from_list"]}, [List], _, MapType, Icode) ->
    {KeyType, ValType} = check_monomorphic_map(Ann, MapType, Icode),
    builtin_call(map_from_list, [ast_body(List, Icode), map_empty(KeyType, ValType, Icode)]);

builtin_code(_, {qid, _, ["Map", "to_list"]}, [Map], _, _, Icode) ->
    map_tolist(Map, Icode);

%% Crypto
builtin_code(_, {qid, _, ["Crypto", "verify_sig"]}, [Msg, PK, Sig], _, _, Icode) ->
    prim_call(?PRIM_CALL_CRYPTO_VERIFY_SIG, #integer{value = 0},
              [ast_body(Msg, Icode), ast_body(PK, Icode), ast_body(Sig, Icode)],
              [word, word, sign_t()], word);

builtin_code(_, {qid, _, ["Crypto", "verify_sig_secp256k1"]}, [Msg, PK, Sig], _, _, Icode) ->
    prim_call(?PRIM_CALL_CRYPTO_VERIFY_SIG_SECP256K1, #integer{value = 0},
              [ast_body(Msg, Icode), ast_body(PK, Icode), ast_body(Sig, Icode)],
              [bytes_t(32), bytes_t(64), bytes_t(64)], word);

builtin_code(_, {qid, _, ["Crypto", "ecverify_secp256k1"]}, [Msg, Addr, Sig], _, _, Icode) ->
    prim_call(?PRIM_CALL_CRYPTO_ECVERIFY_SECP256K1, #integer{value = 0},
              [ast_body(Msg, Icode), ast_body(Addr, Icode), ast_body(Sig, Icode)],
              [word, bytes_t(20), bytes_t(65)], word);

builtin_code(_, {qid, _, ["Crypto", "ecrecover_secp256k1"]}, [Msg, Sig], _, _, Icode) ->
    prim_call(?PRIM_CALL_CRYPTO_ECRECOVER_SECP256K1, #integer{value = 0},
              [ast_body(Msg, Icode), ast_body(Sig, Icode)],
              [word, bytes_t(65)], aeso_icode:option_typerep(bytes_t(20)));

builtin_code(_, {qid, _, ["Crypto", Op]}, [Term], [Type], _, Icode)
        when Op == "sha3"; Op == "sha256"; Op == "blake2b" ->
    generic_hash_primop(list_to_atom(Op), ast_body(Term, Icode), Type, Icode);
builtin_code(_, {qid, _, ["String", Op]}, [String], _, _, Icode)
        when Op == "sha3"; Op == "sha256"; Op == "blake2b" ->
    string_hash_primop(list_to_atom(Op), ast_body(String, Icode));

%% Strings
%% -- String length
builtin_code(_, {qid, _, ["String", "length"]}, [String], _, _, Icode) ->
    builtin_call(string_length, [ast_body(String, Icode)]);

%% -- String concat
builtin_code(_, {qid, _, ["String", "concat"]}, [String1, String2], _, _, Icode) ->
    builtin_call(string_concat, [ast_body(String1, Icode), ast_body(String2, Icode)]);

builtin_code(_, {qid, _, ["Bits", Fun]}, Args, _, _, Icode)
        when Fun == "test"; Fun == "set"; Fun == "clear";
             Fun == "union"; Fun == "intersection"; Fun == "difference" ->
    C  = fun(N) when is_integer(N) -> #integer{ value = N };
            (X) -> X end,
    Bin = fun(O) -> fun(A, B) -> #binop{ op = O, left = C(A), right = C(B) } end end,
    And = Bin('band'),
    Or  = Bin('bor'),
    Bsl = fun(A, B) -> (Bin('bsl'))(B, A) end, %% flipped arguments
    Bsr = fun(A, B) -> (Bin('bsr'))(B, A) end,
    Neg = fun(A) -> #unop{ op = 'bnot', rand = C(A) } end,
    case [Fun | [ ast_body(Arg, Icode) || Arg <- Args ]] of
        ["test", Bits, Ix]     -> And(Bsr(Bits, Ix), 1);
        ["set", Bits, Ix]      -> Or(Bits, Bsl(1, Ix));
        ["clear", Bits, Ix]    -> And(Bits, Neg(Bsl(1, Ix)));
        ["union", A, B]        -> Or(A, B);
        ["intersection", A, B] -> And(A, B);
        ["difference", A, B]   -> And(A, Neg(And(A, B)))
    end;
builtin_code(_, {qid, _, ["Bits", "sum"]}, [Bits], _, _, Icode) ->
    builtin_call(popcount, [ast_body(Bits, Icode), #integer{ value = 0 }]);

builtin_code(_, {qid, _, ["Int", "to_str"]}, [Int], _, _, Icode) ->
    builtin_call(int_to_str, [ast_body(Int, Icode)]);

builtin_code(_, {qid, _, ["Address", "to_str"]}, [Addr], _, _, Icode) ->
    builtin_call(addr_to_str, [ast_body(Addr, Icode)]);
builtin_code(_, {qid, _, ["Address", "is_oracle"]}, [Addr], _, _, Icode) ->
    prim_call(?PRIM_CALL_ADDR_IS_ORACLE, #integer{value = 0},
              [ast_body(Addr, Icode)], [word], word);
builtin_code(_, {qid, _, ["Address", "is_contract"]}, [Addr], _, _, Icode) ->
    prim_call(?PRIM_CALL_ADDR_IS_CONTRACT, #integer{value = 0},
              [ast_body(Addr, Icode)], [word], word);
builtin_code(_, {qid, _, ["Address", "is_payable"]}, [Addr], _, _, Icode) ->
    prim_call(?PRIM_CALL_ADDR_IS_PAYABLE, #integer{value = 0},
              [ast_body(Addr, Icode)], [word], word);
builtin_code(_, {qid, _, ["Address", "to_contract"]}, [Addr], _, _, Icode) ->
    ast_body(Addr, Icode);

builtin_code(_, {qid, _, ["Bytes", "to_int"]}, [Bytes], _, _, Icode) ->
    {typed, _, _, {bytes_t, _, N}} = Bytes,
    builtin_call({bytes_to_int, N}, [ast_body(Bytes, Icode)]);
builtin_code(_, {qid, _, ["Bytes", "to_str"]}, [Bytes], _, _, Icode) ->
    {typed, _, _, {bytes_t, _, N}} = Bytes,
    builtin_call({bytes_to_str, N}, [ast_body(Bytes, Icode)]);
builtin_code(_, {qid, _, ["Bytes", "concat"]}, [A, B], [TypeA, TypeB], _, Icode) ->
    {bytes_t, _, M} = TypeA,
    {bytes_t, _, N} = TypeB,
    builtin_call({bytes_concat, M, N}, [ast_body(A, Icode), ast_body(B, Icode)]);
builtin_code(_, {qid, _, ["Bytes", "split"]}, [A], _, ResType, Icode) ->
    {tuple_t, _, [{bytes_t, _, M}, {bytes_t, _, N}]} = ResType,
    builtin_call({bytes_split, M, N}, [ast_body(A, Icode)]);
builtin_code(_As, Fun, _Args, _ArgsT, _RetT, _Icode) ->
    gen_error({missing_code_for, Fun}).

eta_expand(Id = {_, Ann0, _}, Type = {fun_t, _, [], ArgsT, _}, Icode) ->
    Ann = [{origin, system} | Ann0],
    Xs  = [ {arg, Ann, {id, Ann, "%" ++ integer_to_list(I)}, T} ||
            {I, T} <- lists:zip(lists:seq(1, length(ArgsT)), ArgsT) ],
    Args = [ {typed, Ann, X, T} || {arg, _, X, T} <- Xs ],
    ast_body({lam, Ann, Xs, {app, Ann, {typed, Ann, Id, Type}, Args}}, Icode);
eta_expand(Id, _Type, _Icode) ->
    gen_error({unapplied_builtin, Id}).

check_monomorphic_map({typed, Ann, _, MapType}, Icode) ->
    check_monomorphic_map(Ann, MapType, Icode).

-dialyzer({nowarn_function, check_monomorphic_map/3}).
check_monomorphic_map(Ann, ?map_t(KeyType, ValType), _Icode) ->
    Err = fun(Why) -> gen_error({invalid_map_key_type, Why, Ann, KeyType}) end,
    [ Err(polymorphic) || not is_monomorphic(KeyType) ],
    [ Err(function)    || not is_first_order_type(KeyType) ],
    {KeyType, ValType}.

map_empty(KeyType, ValType, Icode) ->
    prim_call(?PRIM_CALL_MAP_EMPTY, #integer{value = 0},
              [ast_type_value(KeyType, Icode),
               ast_type_value(ValType, Icode)],
              [typerep, typerep], word).

map_get(Key, Map = {typed, _Ann, _, MapType}, Icode) ->
    {_KeyType, ValType} = check_monomorphic_map(aeso_syntax:get_ann(Key), MapType, Icode),
    builtin_call({map_lookup, ast_type(ValType, Icode)}, [ast_body(Map, Icode), ast_body(Key, Icode)]).

map_put(Key, Val, Map, Icode) ->
    builtin_call(map_put, [ast_body(Map, Icode), ast_body(Key, Icode), ast_body(Val, Icode)]).

map_del(Key, Map, Icode) ->
    prim_call(?PRIM_CALL_MAP_DELETE, #integer{value = 0},
              [ast_body(Map, Icode), ast_body(Key, Icode)],
              [word, word], word).

map_tolist(Map, Icode) ->
    {KeyType, ValType} = check_monomorphic_map(Map, Icode),
    prim_call(?PRIM_CALL_MAP_TOLIST, #integer{value = 0},
              [ast_body(Map, Icode)],
              [word], {list, {tuple, [ast_type(KeyType, Icode), ast_type(ValType, Icode)]}}).

map_upd(Key, ValFun, Map = {typed, Ann, _, MapType}, Icode) ->
    {_, ValType} = check_monomorphic_map(Ann, MapType, Icode),
    FunName = {map_upd, ast_type(ValType, Icode)},
    Args    = [ast_body(Map, Icode), ast_body(Key, Icode), ast_body(ValFun, Icode)],
    builtin_call(FunName, Args).

map_upd(Key, Default, ValFun, Map = {typed, Ann, _, MapType}, Icode) ->
    {_, ValType} = check_monomorphic_map(Ann, MapType, Icode),
    FunName = {map_upd_default, ast_type(ValType, Icode)},
    Args    = [ast_body(Map, Icode), ast_body(Key, Icode), ast_body(Default, Icode), ast_body(ValFun, Icode)],
    builtin_call(FunName, Args).

check_entrypoint_type(Ann, Name, Args, Ret) ->
    CheckFirstOrder = fun(T, Err) ->
                case is_first_order_type(T) of
                    false -> gen_error(Err);
                    true  -> ok
                end end,
    CheckMonomorphic = fun(T, Err) ->
                case is_monomorphic(T) of
                    false -> gen_error(Err);
                    true  -> ok
                end end,
    [ CheckFirstOrder(T, {invalid_entrypoint, higher_order, Ann1, Name, {argument, X, T}})
      || {typed, Ann1, X, T} <- Args ],
    CheckFirstOrder(Ret, {invalid_entrypoint, higher_order, Ann, Name, {result, Ret}}),
    [ CheckMonomorphic(T, {invalid_entrypoint, polymorphic, Ann1, Name, {argument, X, T}})
      || {typed, Ann1, X, T} <- Args ],
    CheckMonomorphic(Ret, {invalid_entrypoint, polymorphic, Ann, Name, {result, Ret}}).

check_oracle_type(Ann, Type = ?oracle_t(QType, RType)) ->
    [ gen_error({invalid_oracle_type, Why, Which, Ann, Type})
      || {Why, Check} <- [{polymorphic, fun is_monomorphic/1},
                          {higher_order, fun is_first_order_type/1}],
         {Which, T}   <- [{query, QType}, {response, RType}],
         not Check(T) ].

is_simple_type({tvar, _, _})        -> false;
is_simple_type({fun_t, _, _, _, _}) -> false;
is_simple_type(Ts) when is_list(Ts) -> lists:all(fun is_simple_type/1, Ts);
is_simple_type(T) when is_tuple(T)  -> is_simple_type(tuple_to_list(T));
is_simple_type(_)                   -> true.

is_first_order_type({fun_t, _, _, _, _}) -> false;
is_first_order_type(Ts) when is_list(Ts) -> lists:all(fun is_first_order_type/1, Ts);
is_first_order_type(T) when is_tuple(T)  -> is_first_order_type(tuple_to_list(T));
is_first_order_type(_)                   -> true.

is_monomorphic({tvar, _, _}) -> false;
is_monomorphic([H|T]) ->
  is_monomorphic(H) andalso is_monomorphic(T);
is_monomorphic(T) when is_tuple(T) ->
  is_monomorphic(tuple_to_list(T));
is_monomorphic(_) -> true.

%% Implemented as a contract call to the contract with address 0.
prim_call(Prim, Amount, Args, ArgTypes, OutType) ->
    TypeHash =
        case aeb_primops:op_needs_type_check(Prim) of
            true ->
                PrimBin = binary:encode_unsigned(Prim),
                ArgType = {tuple, ArgTypes},
                <<TH:256>> = aeb_aevm_abi:function_type_hash(PrimBin, ArgType, OutType),
                TH;
            false ->
                0
        end,
    #prim_call_contract{ gas      = prim_gas_left,
                         address  = #integer{ value = ?PRIM_CALLS_CONTRACT },
                         value    = Amount,
                         arg      = #tuple{cpts = [#integer{ value = Prim }| Args]},
                         type_hash= #integer{value = TypeHash}
                       }.

generic_hash_primop(Op, Arg, {bytes_t, _, N}, _Icode) ->
    %% Compile hashing bytes to String.hash. Makes it easier for the user to
    %% predict the result.
    string_hash_primop(Op, aeso_builtins:bytes_to_raw_string(N, Arg));
generic_hash_primop(Op, Arg, Type, Icode) ->
    PrimOp = case Op of
                 sha3    -> ?PRIM_CALL_CRYPTO_SHA3;
                 sha256  -> ?PRIM_CALL_CRYPTO_SHA256;
                 blake2b -> ?PRIM_CALL_CRYPTO_BLAKE2B
             end,
    ArgType   = ast_type(Type, Icode),
    TypeValue = type_value(ArgType),
    prim_call(PrimOp, #integer{value = 0},
              [TypeValue, Arg], [typerep, ArgType], word).

string_hash_primop(sha3, String) ->
    #unop{ op = 'sha3', rand = String };
string_hash_primop(Op, String) ->
    PrimOp = case Op of
                 sha256 -> ?PRIM_CALL_CRYPTO_SHA256_STRING;
                 blake2b -> ?PRIM_CALL_CRYPTO_BLAKE2B_STRING
             end,
    prim_call(PrimOp, #integer{value = 0}, [String], [string], word).

make_type_def(Args, Def, Icode = #{ type_vars := TypeEnv }) ->
    TVars = [ X || {tvar, _, X} <- Args ],
    fun(Types) ->
        TypeEnv1 = maps:from_list(lists:zip(TVars, Types)),
        ast_typerep1(Def, Icode#{ type_vars := maps:merge(TypeEnv, TypeEnv1) })
    end.

-spec ast_typerep(aeso_syntax:type()) -> aeb_aevm_data:type().
ast_typerep(Type) ->
    ast_typerep(Type, aeso_icode:new([])).

ast_typerep(Type, Icode) ->
    case is_simple_type(Type) of
        false -> gen_error({not_a_simple_type, Type});
        true  -> ast_typerep1(Type, Icode)
    end.

ast_typerep1({id, _, Name}, Icode) ->
    lookup_type_id(Name, [], Icode);
ast_typerep1({qid, _, Name}, Icode) ->
    lookup_type_id(Name, [], Icode);
ast_typerep1({con, _, _}, _) ->
    word;   %% Contract type
ast_typerep1({bytes_t, _, Len}, _) ->
    bytes_t(Len);
ast_typerep1({app_t, _, {I, _, Name}, Args}, Icode) when I =:= id; I =:= qid ->
    ArgReps = [ ast_typerep1(Arg, Icode) || Arg <- Args ],
    lookup_type_id(Name, ArgReps, Icode);
ast_typerep1({tvar,_,A}, #{ type_vars := TypeVars }) ->
    case maps:get(A, TypeVars, undefined) of
        undefined -> word; %% We serialize type variables just as addresses in the originating VM.
        Type      -> Type
    end;
ast_typerep1({tuple_t,_,Cpts}, Icode) ->
    {tuple, [ast_typerep1(C, Icode) || C<-Cpts]};
ast_typerep1({record_t,Fields}, Icode) ->
    {tuple, [ begin
                {field_t, _, _, T} = Field,
                ast_typerep1(T, Icode)
              end || Field <- Fields]};
ast_typerep1({fun_t,_,_,_,_}, _Icode) ->
    function;
ast_typerep1({alias_t, T}, Icode) -> ast_typerep1(T, Icode);
ast_typerep1({variant_t, Cons}, Icode) ->
    {variant, [ begin
                  {constr_t, _, _, Args} = Con,
                  [ ast_typerep1(Arg, Icode) || Arg <- Args ]
                end || Con <- Cons ]};
ast_typerep1({if_t, _, _, _, Else}, Icode) ->
    ast_typerep1(Else, Icode). %% protected remote calls are not in AEVM

ttl_t(Icode) ->
    ast_typerep({qid, [], ["Chain", "ttl"]}, Icode).

%% pointee_t(Icode) ->
%%     ast_typerep({qid, [], ["AENS", "pointee"]}, Icode).

sign_t() -> bytes_t(64).
bytes_t(Len) when Len =< 32 -> word;
bytes_t(Len)                -> {tuple, lists:duplicate((31 + Len) div 32, word)}.

get_signature_arg(Args0) ->
    NamedArgs = [Arg || Arg = {named_arg, _, _, _} <- Args0],
    Args      = Args0 -- NamedArgs,

    DefaultVal = {tuple, [], [{int, [], 0}, {int, [], 0}]},
    Sig =
        case NamedArgs of
            []                       -> DefaultVal;
            [{named_arg, _, _, Val}] -> Val
        end,
    {Sig, Args}.

lookup_type_id(Name, Args, #{ types := Types }) ->
    case maps:get(Name, Types, undefined) of
        undefined -> gen_error({undefined_type, Name});
        TDef      -> TDef(Args)
    end.

ast_type_value(T, Icode) ->
    type_value(ast_type(T, Icode)).

type_value(word)   ->
    #tuple{ cpts = [#integer{ value = ?TYPEREP_WORD_TAG }] };
type_value(string) ->
    #tuple{ cpts = [#integer{ value = ?TYPEREP_STRING_TAG }] };
type_value(typerep) ->
    #tuple{ cpts = [#integer{ value = ?TYPEREP_TYPEREP_TAG }] };
type_value({list, A}) ->
    #tuple{ cpts = [#integer{ value = ?TYPEREP_LIST_TAG }, type_value(A)] };
type_value({tuple, As}) ->
    #tuple{ cpts = [#integer{ value = ?TYPEREP_TUPLE_TAG },
                    #list{ elems = [ type_value(A) || A <- As ] }] };
type_value({variant, Cs}) ->
    #tuple{ cpts = [#integer{ value = ?TYPEREP_VARIANT_TAG },
                    #list{ elems = [ #list{ elems = [ type_value(A) || A <- As ] } || As <- Cs ] }] };
type_value({map, K, V}) ->
    #tuple{ cpts = [#integer{ value = ?TYPEREP_MAP_TAG },
                    type_value(K), type_value(V)] }.

ast_fun_to_icode(Name, Attrs, Args, Body, TypeRep, #{functions := Funs} = Icode) ->
    NewFuns = [{Name, Attrs, Args, Body, TypeRep}| Funs],
    aeso_icode:set_functions(NewFuns, Icode).

%% A function is private if not an 'entrypoint', or if it's not defined in the
%% main contract name space. (NOTE: changes when we introduce inheritance).
is_private(Ann, #{ contract_name := MainContract } = Icode) ->
    {_, _, CurrentNamespace} = aeso_icode:get_namespace(Icode),
    not proplists:get_value(entrypoint, Ann, false) orelse
    MainContract /= CurrentNamespace.

%% -------------------------------------------------------------------
%% Builtins
%% -------------------------------------------------------------------

builtin_call(Builtin, Args) ->
    #funcall{ function = #var_ref{ name = {builtin, Builtin} },
              args = Args }.

add_builtins(Icode = #{functions := Funs}) ->
    Builtins = aeso_builtins:used_builtins(Funs),
    Icode#{functions := [ aeso_builtins:builtin_function(B) || B <- Builtins ] ++ Funs}.


%% -------------------------------------------------------------------
%% Deadcode elimination
%% -------------------------------------------------------------------

deadcode_elimination(Icode = #{ functions := Funs }) ->
    PublicNames = [ Name || {Name, Ann, _, _, _} <- Funs, not lists:member(private, Ann) ],
    ArgsToPat   = fun(Args) -> [ #var_ref{ name = X } || {X, _} <- Args ] end,
    Defs        = maps:from_list([ {Name, {binder, ArgsToPat(Args), Body}} || {Name, _, Args, Body, _} <- Funs ]),
    UsedNames   = chase_names(Defs, PublicNames, #{}),
    UsedFuns    = [ Def || Def = {Name, _, _, _, _} <- Funs, maps:is_key(Name, UsedNames) ],
    Icode#{ functions := UsedFuns }.

chase_names(_Defs, [], Used) -> Used;
chase_names(Defs, [X | Xs], Used) ->
                              %% can happen when compiling __call contracts
    case maps:is_key(X, Used) orelse not maps:is_key(X, Defs) of
        true  -> chase_names(Defs, Xs, Used); %% already chased
        false ->
            Def  = maps:get(X, Defs),
            Vars = maps:keys(free_vars(Def)),
            chase_names(Defs, Vars ++ Xs, Used#{ X => true })
    end.

free_vars(#var_ref{ name = X }) -> #{ X => true };
free_vars(#arg{ name = X }) -> #{ X => true };
free_vars({binder, Pat, Body}) ->
    maps:without(maps:keys(free_vars(Pat)), free_vars(Body));
free_vars(#switch{ expr = E, cases = Cases }) ->
    free_vars([E | [{binder, P, B} || {P, B} <- Cases]]);
free_vars(#lambda{ args = Xs, body = E }) ->
    free_vars({binder, Xs, E});
free_vars(T) when is_tuple(T) -> free_vars(tuple_to_list(T));
free_vars([H | T]) -> maps:merge(free_vars(H), free_vars(T));
free_vars(_) -> #{}.
