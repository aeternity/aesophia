%%%-------------------------------------------------------------------
%%% Value encode/decode helpers split from aeso_compiler
%%%-------------------------------------------------------------------
-module(aeso_value_codec).

-export([ encode_value/4
        , decode_value/4
        , to_sophia_value/4
        , to_sophia_value/5
        ]).

%% @doc Encode a Sophia `Value` of `Type` to a serialized FATE binary, by
%%      synthesizing a helper call in the contract.
encode_value(Contract0, Type, Value, Options) ->
    case aeso_call_injector:add_extra_call(Contract0, {value, Type, Value}, Options) of
        {ok, CallName, Code} ->
            Body = aeso_call_injector:get_call_body(CallName, Code),
            {ok, aeb_fate_encoding:serialize(aeso_fcode_to_fate:term_to_fate(Body))};
        Err = {error, _} ->
            Err
    end.

%% @doc Decode a FATE value to a Sophia value of a given `Type`.
decode_value(Contract0, Type, FateValue, Options) ->
    case aeso_call_injector:add_extra_call(Contract0, {type, Type}, Options) of
        {ok, CallName, Code} ->
            #{ folded_typed_ast := TypedAst
             , type_env         := TypeEnv} = Code,
            {ok, _, Type0} = aeso_compiler:get_decode_type(CallName, TypedAst),
            Type1 = aeso_ast_infer_types:unfold_types_in_type(TypeEnv, Type0,
                                                              [ unfold_record_types
                                                              , unfold_variant_types
                                                              , not_unfold_system_alias_types ]),
            fate_data_to_sophia_value(Type0, Type1, FateValue);
        Err = {error, _} ->
            Err
    end.

%% @doc Convert a call result to a Sophia expression. Handles ok/error/revert.
to_sophia_value(ContractString, Fun, ResType, Data) ->
    to_sophia_value(ContractString, Fun, ResType, Data, []).

to_sophia_value(_, _, error, Err, _Options) ->
    {ok, {app, [], {id, [], "error"}, [{string, [], Err}]}};
to_sophia_value(_, _, revert, Data, _Options) ->
    try aeso_vm_decode:from_fate({id, [], "string"}, aeb_fate_encoding:deserialize(Data)) of
        Err ->
            {ok, {app, [], {id, [], "abort"}, [Err]}}
    catch _:_ ->
            Msg = "Could not deserialize the revert message",
            {error, [aeso_errors:new(data_error, Msg)]}
    end;
to_sophia_value(ContractString, FunName, ok, Data, Options0) ->
    Options = [no_code | Options0],
    try
        Code = aeso_compiler:string_to_code(ContractString, Options),
        #{ folded_typed_ast := TypedAst, type_env := TypeEnv} = Code,
        {ok, _, Type0} = aeso_compiler:get_decode_type(FunName, TypedAst),
        Type = aeso_ast_infer_types:unfold_types_in_type(TypeEnv, Type0,
                                                         [ unfold_record_types
                                                         , unfold_variant_types
                                                         , not_unfold_system_alias_types]),
        fate_data_to_sophia_value(Type0, Type, Data)
    catch
        throw:{error, Errors} -> {error, Errors}
    end.

fate_data_to_sophia_value(Type, UnfoldedType, FateData) ->
    try
        {ok, aeso_vm_decode:from_fate(UnfoldedType, aeb_fate_encoding:deserialize(FateData))}
    catch throw:cannot_translate_to_sophia ->
            Type1 = prettypr:format(aeso_pretty:type(Type)),
            Msg = io_lib:format("Cannot translate FATE value ~p\n  of Sophia type ~s",
                                [aeb_fate_encoding:deserialize(FateData), Type1]),
            {error, [aeso_errors:new(data_error, Msg)]};
          _:_ ->
            Type1 = prettypr:format(aeso_pretty:type(Type)),
            Msg = io_lib:format("Failed to decode binary as type ~s", [Type1]),
            {error, [aeso_errors:new(data_error, Msg)]}
    end.


