-module(aeso_tc_type_unfolding).

-export([ unfold_types_in_type/2
        , unfold_types_in_type/3
        , unfold_record_types/2
        ]).

%% -- Duplicated macros ------------------------------------------------------

-define(is_type_id(T), element(1, T) =:= id orelse
                       element(1, T) =:= qid orelse
                       element(1, T) =:= con orelse
                       element(1, T) =:= qcon).

%% -- Moved functions --------------------------------------------------------

type_error(A) -> aeso_tc_errors:type_error(A).

%% -------

used_typedef(A, B) -> aeso_tc_warnings:used_typedef(A, B).

%% -------

when_warning(A, B) -> aeso_tc_options:when_warning(A, B).

%% ---------------------------------------------------------------------------

%% During type inference, record types are represented by their
%% names. But, before we pass the typed program to the code generator,
%% we replace record types annotating expressions with their
%% definition. This enables the code generator to see the fields.
unfold_record_types(Env, T) ->
    unfold_types(Env, T, [unfold_record_types]).

unfold_types(Env, {typed, Attr, E, Type}, Options) ->
    Options1 = [{ann, Attr} | lists:keydelete(ann, 1, Options)],
    {typed, Attr, unfold_types(Env, E, Options), unfold_types_in_type(Env, Type, Options1)};
unfold_types(Env, {arg, Attr, Id, Type}, Options) ->
    {arg, Attr, Id, unfold_types_in_type(Env, Type, Options)};
unfold_types(Env, {type_sig, Ann, Constr, NamedArgs, Args, Ret}, Options) ->
    {type_sig, Ann, Constr,
               unfold_types_in_type(Env, NamedArgs, Options),
               unfold_types_in_type(Env, Args, Options),
               unfold_types_in_type(Env, Ret, Options)};
unfold_types(Env, {type_def, Ann, Name, Args, Def}, Options) ->
    {type_def, Ann, Name, Args, unfold_types_in_type(Env, Def, Options)};
unfold_types(Env, {fun_decl, Ann, Name, Type}, Options) ->
    {fun_decl, Ann, Name, unfold_types(Env, Type, Options)};
unfold_types(Env, {letfun, Ann, Name, Args, Type, [{guarded, AnnG, [], Body}]}, Options) ->
    {letfun, Ann, Name, unfold_types(Env, Args, Options), unfold_types_in_type(Env, Type, Options), [{guarded, AnnG, [], unfold_types(Env, Body, Options)}]};
unfold_types(Env, T, Options) when is_tuple(T) ->
    list_to_tuple(unfold_types(Env, tuple_to_list(T), Options));
unfold_types(Env, [H|T], Options) ->
    [unfold_types(Env, H, Options)|unfold_types(Env, T, Options)];
unfold_types(_Env, X, _Options) ->
    X.

unfold_types_in_type(Env, T) ->
    unfold_types_in_type(Env, T, []).

unfold_types_in_type(Env, {app_t, Ann, Id = {id, _, "map"}, Args = [KeyType0, _]}, Options) ->
    Args1 = [KeyType, _] = unfold_types_in_type(Env, Args, Options),
    Ann1 = proplists:get_value(ann, Options, aeso_syntax:get_ann(KeyType0)),
    [ type_error({map_in_map_key, Ann1, KeyType0}) || has_maps(KeyType) ],
    {app_t, Ann, Id, Args1};
unfold_types_in_type(Env, {app_t, Ann, Id, Args}, Options) when ?is_type_id(Id) ->
    when_warning(warn_unused_typedefs, fun() -> used_typedef(Id, length(Args)) end),
    UnfoldRecords  = proplists:get_value(unfold_record_types, Options, false),
    UnfoldVariants = proplists:get_value(unfold_variant_types, Options, false),
    case aeso_tc_env:lookup_type(Env, Id) of
        {_, {_, {Formals, {record_t, Fields}}}} when UnfoldRecords, length(Formals) == length(Args) ->
            {record_t,
             unfold_types_in_type(Env,
               subst_tvars(lists:zip(Formals, Args), Fields), Options)};
        {_, {_, {Formals, {alias_t, Type}}}} when length(Formals) == length(Args) ->
            unfold_types_in_type(Env, subst_tvars(lists:zip(Formals, Args), Type), Options);
        {_, {_, {Formals, {variant_t, Constrs}}}} when UnfoldVariants, length(Formals) == length(Args) ->
            %% TODO: unfolding variant types will not work well if we add recursive types!
            {variant_t,
             unfold_types_in_type(Env,
                subst_tvars(lists:zip(Formals, Args), Constrs), Options)};
        _ ->
            %% Not a record type, or ill-formed record type.
            {app_t, Ann, Id, unfold_types_in_type(Env, Args, Options)}
    end;
unfold_types_in_type(Env, Id, Options) when ?is_type_id(Id) ->
    %% Like the case above, but for types without parameters.
    when_warning(warn_unused_typedefs, fun() -> used_typedef(Id, 0) end),
    UnfoldRecords = proplists:get_value(unfold_record_types, Options, false),
    UnfoldVariants = proplists:get_value(unfold_variant_types, Options, false),
    case aeso_tc_env:lookup_type(Env, Id) of
        {_, {_, {[], {record_t, Fields}}}} when UnfoldRecords ->
            {record_t, unfold_types_in_type(Env, Fields, Options)};
        {_, {_, {[], {variant_t, Constrs}}}} when UnfoldVariants ->
            {variant_t, unfold_types_in_type(Env, Constrs, Options)};
        {_, {_, {[], {alias_t, Type1}}}} ->
            unfold_types_in_type(Env, Type1, Options);
        _ ->
            %% Not a record type, or ill-formed record type
            Id
    end;
unfold_types_in_type(Env, {field_t, Attr, Name, Type}, Options) ->
    {field_t, Attr, Name, unfold_types_in_type(Env, Type, Options)};
unfold_types_in_type(Env, {constr_t, Ann, Con, Types}, Options) ->
    {constr_t, Ann, Con, unfold_types_in_type(Env, Types, Options)};
unfold_types_in_type(Env, {named_arg_t, Ann, Con, Types, Default}, Options) ->
    {named_arg_t, Ann, Con, unfold_types_in_type(Env, Types, Options), Default};
unfold_types_in_type(Env, T, Options) when is_tuple(T) ->
    list_to_tuple(unfold_types_in_type(Env, tuple_to_list(T), Options));
unfold_types_in_type(Env, [H|T], Options) ->
    [unfold_types_in_type(Env, H, Options)|unfold_types_in_type(Env, T, Options)];
unfold_types_in_type(_Env, X, _Options) ->
    X.

has_maps({app_t, _, {id, _, "map"}, _}) ->
    true;
has_maps(L) when is_list(L) ->
    lists:any(fun has_maps/1, L);
has_maps(T) when is_tuple(T) ->
    has_maps(tuple_to_list(T));
has_maps(_) -> false.

subst_tvars(Env, Type) ->
    subst_tvars1([{V, T} || {{tvar, _, V}, T} <- Env], Type).

subst_tvars1(Env, T={tvar, _, Name}) ->
    proplists:get_value(Name, Env, T);
subst_tvars1(Env, [H|T]) ->
    [subst_tvars1(Env, H)|subst_tvars1(Env, T)];
subst_tvars1(Env, Type) when is_tuple(Type) ->
    list_to_tuple(subst_tvars1(Env, tuple_to_list(Type)));
subst_tvars1(_Env, X) ->
    X.
