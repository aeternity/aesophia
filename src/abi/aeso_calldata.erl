%%%-------------------------------------------------------------------
%%% Calldata helpers split from aeso_compiler
%%%-------------------------------------------------------------------
-module(aeso_calldata).

-export([ create_calldata/3
        , create_calldata/4
        , decode_calldata/3
        , decode_calldata/4
        ]).

%% @doc Build calldata for calling `Fun` with textual arguments `Args`.
create_calldata(Code, Fun, Args) ->
    create_calldata(Code, Fun, Args, []).

%% @doc Build calldata with extra compiler `Options` (e.g., include paths).
create_calldata(Code, Fun, Args, Options0) ->
    Options = [no_code | Options0],
    case aeso_call_injector:check_call(Code, Fun, Args, Options) of
        {ok, FunName, FateArgs} ->
            aeb_fate_abi:create_calldata(FunName, FateArgs);
        {error, _} = Err -> Err
    end.

%% @doc Decode calldata back to the argument types and Sophia expressions.
decode_calldata(ContractString, FunName, Calldata) ->
    decode_calldata(ContractString, FunName, Calldata, []).

%% @doc Decode calldata with extra compiler `Options`.
decode_calldata(ContractString, FunName, Calldata, Options0) ->
    Options = [no_code | Options0],
    try
        Code = aeso_compiler:string_to_code(ContractString, Options),
        #{ folded_typed_ast := TypedAst, type_env  := TypeEnv} = Code,

        {ok, Args, _} = aeso_compiler:get_decode_type(FunName, TypedAst),
        GetType       = fun({typed, _, _, T}) -> T; (T) -> T end,
        ArgTypes      = lists:map(GetType, Args),
        Type0         = {tuple_t, [], ArgTypes},
        Type          = aeso_ast_infer_types:unfold_types_in_type(TypeEnv, Type0,
                                                                  [ unfold_record_types
                                                                  , unfold_variant_types
                                                                  , not_unfold_system_alias_types]),
        case aeb_fate_abi:decode_calldata(FunName, Calldata) of
            {ok, FateArgs} ->
                try
                    {tuple_t, [], ArgTypes1} = Type,
                    AstArgs = [ aeso_vm_decode:from_fate(ArgType, FateArg)
                                || {ArgType, FateArg} <- lists:zip(ArgTypes1, FateArgs)],
                    {ok, ArgTypes, AstArgs}
                catch throw:cannot_translate_to_sophia ->
                        Type0Str = prettypr:format(aeso_pretty:type(Type0)),
                        Msg = io_lib:format("Cannot translate FATE value ~p\n  to Sophia type ~s",
                                            [FateArgs, Type0Str]),
                        {error, [aeso_errors:new(data_error, Msg)]}
                end;
            {error, _} ->
                Msg = io_lib:format("Failed to decode calldata binary", []),
                {error, [aeso_errors:new(data_error, Msg)]}
        end
    catch
        throw:{error, Errors} -> {error, Errors}
    end.


