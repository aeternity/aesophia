%%%-------------------------------------------------------------------
%%% @author Happi (Erik Stenman)
%%% @copyright (C) 2017, Aeternity Anstalt
%%% @doc
%%%     High-level API for compiling Sophia smart contracts to FATE bytecode.
%%%
%%%     For CS bachelor students: this module exposes convenient functions to
%%%     compile Sophia source (from a file or string), inspect intermediate
%%%     results, and work with calldata/value encoding.
%%%
%%%     Compilation overview:
%%%       1) Parse source into an AST
%%%       2) Run type inference to produce a typed AST
%%%       3) Lower to an intermediate representation ("fcode")
%%%       4) Generate FATE and serialize to bytecode
%%%
%%%     See also `aeso_pipeline` for the step-by-step implementation of these
%%%     stages.
%%% @end
%%% Created : 12 Dec 2017
%%%-------------------------------------------------------------------
-module(aeso_compiler).

-export([ file/1
        , file/2
        , from_string/2
        , check_call/4
        , decode_value/4
        , encode_value/4
        , create_calldata/3
        , create_calldata/4
        , version/0
        , numeric_version/0
        , to_sophia_value/4
        , to_sophia_value/5
        , decode_calldata/3
        , decode_calldata/4
        , parse/2
        , add_include_path/2
        , validate_byte_code/3
        , string_to_code/2
        , get_decode_type/2
        ]).

-include_lib("aebytecode/include/aeb_opcodes.hrl").
-include("aeso_utils.hrl").


-type option() :: pp_sophia_code
                | pp_ast
                | pp_types
                | pp_typed_ast
                | pp_assembler
                | no_code
                | keep_included
                | debug_mode
                | {include, {file_system, [string()]}
                            | {explicit_files, #{string() => binary()}}}
                | {src_file, string()}
                | {src_dir, string()}
                | {aci, aeso_aci:aci_type()}.
-type options() :: [option()].

-export_type([ option/0
             , options/0
             ]).

-spec version() -> {ok, binary()} | {error, term()}.
%% @doc Return the compiler semantic version as a binary.
version() ->
    case lists:keyfind(aesophia, 1, application:loaded_applications()) of
        false ->
            case application:load(aesophia) of
                ok ->
                    case application:get_key(aesophia, vsn) of
                        {ok, VsnString} ->
                            {ok, list_to_binary(VsnString)};
                        undefined ->
                            {error, failed_to_load_aesophia}
                    end;
                Err = {error, _} ->
                    Err
            end;
        {_App, _Des, VsnString} ->
            {ok, list_to_binary(VsnString)}
    end.

-spec numeric_version() -> {ok, [non_neg_integer()]} | {error, term()}.
%% @doc Return the compiler version split into integers, e.g. {ok, [1,2,3]}.
numeric_version() ->
    case version() of
        {ok, Bin} ->
            [NoSuf | _] = binary:split(Bin, <<"-">>),
            Numbers     = binary:split(NoSuf, <<".">>, [global]),
            {ok, [binary_to_integer(Num) || Num <- Numbers]};
        {error, _} = Err ->
            Err
    end.

-spec file(string()) -> {ok, map()} | {error, [aeso_errors:error()]}.
%% @doc Compile the Sophia contract stored at `Filename` with default options.
file(Filename) ->
    file(Filename, []).

-spec file(string(), options()) -> {ok, map()} | {error, [aeso_errors:error()]}.
%% @doc Compile the Sophia contract stored at `File` using `Options`.
file(File, Options0) ->
    Options = add_include_path(File, Options0),
    case read_contract(File) of
        {ok, Bin} ->
            SrcDir = aeso_utils:canonical_dir(filename:dirname(File)),
            from_string(Bin, [{src_file, File}, {src_dir, SrcDir} | Options]);
        {error, Error} ->
            Msg = lists:flatten([File,": ",file:format_error(Error)]),
            {error, [aeso_errors:new(file_error, Msg)]}
    end.

add_include_path(File, Options) ->
    case lists:keymember(include, 1, Options) of
        true  -> Options;
        false ->
            Dir = filename:dirname(File),
            {ok, Cwd} = file:get_cwd(),
            [{include, {file_system, [Cwd, aeso_utils:canonical_dir(Dir)]}} | Options]
    end.

-spec from_string(binary() | string(), options()) -> {ok, map()} | {error, [aeso_errors:error()]}.
%% @doc Compile a Sophia contract given as a string or binary using `Options`.
from_string(ContractBin, Options) when is_binary(ContractBin) ->
    from_string(binary_to_list(ContractBin), Options);
from_string(ContractString, Options) ->
    from_string1(ContractString, Options).

-spec from_string1(string(), options()) -> {ok, map()} | {error, [aeso_errors:error()]}.
from_string1(ContractString, Options) ->
    %% Use erlang:apply to avoid Dialyzer over-constraint on success typing
    case erlang:apply(aeso_pipeline, build, [aeso_fcode_to_fate, ContractString, Options]) of
        {error, _} = Err -> Err;
        {ok, Map} ->
            %% Reuse artifacts produced during build/3 instead of recomputing
            %% the entire frontend pipeline a second time.
            #{ folded_typed_ast := FoldedTypedAst,
               warnings := Warnings } = Map,
            Res = Map#{ contract_source => ContractString,
                        type_info => [],
                        warnings => Warnings },
            {ok, maybe_generate_aci(Res, FoldedTypedAst, Options)}
    end.

maybe_generate_aci(Result, FoldedTypedAst, Options) ->
    case proplists:get_value(aci, Options) of
        undefined ->
            Result;
        Type ->
            {ok, Aci} = aeso_aci:from_typed_ast(Type, FoldedTypedAst),
            maps:put(aci, Aci, Result)
    end.

-spec string_to_code(string(), options()) -> map().
%% @doc Convert source text to intermediate representations (ASTs, fcode,
%%      type env, warnings) without producing final bytecode.
string_to_code(ContractString, Options) ->
    aeso_pipeline:string_to_fcode(ContractString, Options).

-define(CALL_NAME,   "__call").

%% Delegate call injection helpers
-spec check_call(string(), string(), [string()], options()) -> {ok, string(), [term()]}
                                                             | {error, [aeso_errors:error()]}.
%% @doc Statically check a call to function `FunName` with textual arguments
%%      `Args` in `Source`. Useful for tools that need to validate calls or
%%      build calldata.
check_call(Source, FunName, Args, Options) ->
    aeso_call_injector:check_call(Source, FunName, Args, Options).

-spec to_sophia_value(string(), string(), ok | error | revert, binary()) ->
          {ok, aeso_syntax:expr()} | {error, [aeso_errors:error()]}.
%% @doc Decode a result value (or error) from on-chain FATE back to a
%%      Sophia expression, based on the called entrypoint and its type.
to_sophia_value(ContractString, Fun, ResType, Data) ->
    to_sophia_value(ContractString, Fun, ResType, Data, []).
-spec to_sophia_value(string(), string(), ok | error | revert, binary(), options()) ->
        {ok, aeso_syntax:expr()} | {error, [aeso_errors:error()]}.
 %% @doc Same as `to_sophia_value/4` but with compiler `Options`.
 to_sophia_value(ContractString, Fun, ResType, Data, Options) ->
    aeso_value_codec:to_sophia_value(ContractString, Fun, ResType, Data, Options).

%% Public API delegations for value encoding/decoding
%% @doc Encode a Sophia `Value` of `Type` to a FATE value.
encode_value(Contract0, Type, Value, Options) ->
    aeso_value_codec:encode_value(Contract0, Type, Value, Options).

%% @doc Decode a FATE value to a Sophia value of the given `Type`.
decode_value(Contract0, Type, FateValue, Options) ->
    aeso_value_codec:decode_value(Contract0, Type, FateValue, Options).

-spec create_calldata(string(), string(), [string()]) ->
          {ok, binary()} | {error, [aeso_errors:error()]}.
%% @doc Build calldata for calling `Fun` with textual arguments `Args`.
create_calldata(Code, Fun, Args) ->
    create_calldata(Code, Fun, Args, []).
-spec create_calldata(string(), string(), [string()], [{atom(), any()}]) ->
                             {ok, binary()} | {error, [aeso_errors:error()]}.
%% @doc Same as `create_calldata/3` but with extra compiler options.
create_calldata(Code, Fun, Args, Options0) ->
    aeso_calldata:create_calldata(Code, Fun, Args, Options0).

-spec decode_calldata(string(), string(), binary()) ->
          {ok, [aeso_syntax:type()], [aeso_syntax:expr()]}
        | {error, [aeso_errors:error()]}.
%% @doc Given a target function name and raw calldata, return the list of
%%      argument types and decoded Sophia expressions.
decode_calldata(ContractString, FunName, Calldata) ->
    decode_calldata(ContractString, FunName, Calldata, []).
-spec decode_calldata(string(), string(), binary(), options()) ->
          {ok, [aeso_syntax:type()], [aeso_syntax:expr()]}
        | {error, [aeso_errors:error()]}.
%% @doc Same as `decode_calldata/3` but with compiler `Options`.
decode_calldata(ContractString, FunName, Calldata, Options0) ->
    aeso_calldata:decode_calldata(ContractString, FunName, Calldata, Options0).

-dialyzer({nowarn_function, get_decode_type/2}).
get_decode_type(FunName, [{Contract, Ann, _, _, Defs}]) when ?IS_CONTRACT_HEAD(Contract) ->
    GetType = fun({letfun, _, {id, _, Name}, Args, Ret, _})               when Name == FunName -> [{Args, Ret}];
                 ({fun_decl, _, {id, _, Name}, {fun_t, _, _, Args, Ret}}) when Name == FunName -> [{Args, Ret}];
                 (_) -> [] end,
    case lists:flatmap(GetType, Defs) of
        [{Args, Ret}] -> {ok, Args, Ret};
        []            ->
            case FunName of
                "init" -> {ok, [], {tuple_t, [], []}};
                 _ ->
                    Msg = io_lib:format("Function '~s' is missing in contract", [FunName]),
                    Pos = aeso_errors:pos(Ann),
                    aeso_errors:throw(aeso_errors:new(data_error, Pos, Msg))
            end
    end;
get_decode_type(FunName, [_ | Contracts]) ->
    %% The __decode should be in the final contract
    get_decode_type(FunName, Contracts).

%% Pretty printers are used directly from aeso_pp within string_to_code/2

%% -- Byte code validation ---------------------------------------------------

-define(protect(Tag, Code), fun() -> try Code catch _:Err1 -> throw({Tag, Err1}) end end()).

-spec validate_byte_code(map(), string(), options()) -> ok | {error, [aeso_errors:error()]}.
%% @doc Re-run validation passes on a compiled `Map` and `Source`.
validate_byte_code(Map, Source, Options) ->
    aeso_bytecode_validator:validate_byte_code(Map, Source, Options).

%% -------------------------------------------------------------------

-spec parse(string(), aeso_compiler:options()) -> none() | aeso_syntax:ast().
%% @doc Parse the given source into an AST, expanding includes.
parse(Text, Options) ->
    parse(Text, sets:new(), Options).

-spec parse(string(), sets:set(), aeso_compiler:options()) -> none() | aeso_syntax:ast().
%% @doc Parse with an explicit set of already `Included` files (to avoid
%%      re-including the same file). Intended for internal use and tooling.
parse(Text, Included, Options) ->
    aeso_parser:string(Text, Included, Options).

read_contract(Name) ->
    file:read_file(Name).
