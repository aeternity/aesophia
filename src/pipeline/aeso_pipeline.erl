%%%-------------------------------------------------------------------
%%% @doc
%%%   High-level compilation pipeline for Sophia contracts.
%%%
%%%   Stages:
%%%     1) Parse: Source text -> AST (`aeso_compiler:parse/2`)
%%%     2) Type inference: AST -> typed AST (`aeso_ast_infer_types:infer/2`)
%%%     3) IR lowering: typed AST -> fcode (`aeso_ast_to_fcode:ast_to_fcode/2`)
%%%     4) Backend: fcode -> FATE -> bytecode (via BackendMod:compile)
%%%
%%%   Returns a map of intermediate artifacts and warnings to aid tools.
%%% @end
%%%-------------------------------------------------------------------
-module(aeso_pipeline).

-export([ string_to_fcode/2
        , build/3
        ]).

-spec string_to_fcode(string(), aeso_compiler:options()) -> map().
%% @doc Run the frontend and IR lowering, returning ASTs, types, fcode, and
%%      warnings without producing bytecode.
string_to_fcode(ContractString, Options) ->
    Ast = aeso_compiler:parse(ContractString, Options),
    aeso_pp:pp_sophia_code(Ast, Options),
    aeso_pp:pp_ast(Ast, Options),
    {TypeEnv, FoldedTypedAst, UnfoldedTypedAst, Warnings} = aeso_ast_infer_types:infer(Ast, [return_env | Options]),
    aeso_pp:pp_typed_ast(UnfoldedTypedAst, Options),
    {Env, Fcode} = aeso_ast_to_fcode:ast_to_fcode(UnfoldedTypedAst, [{original_src, ContractString}|Options]),
    #{ fcode => Fcode
     , fcode_env => Env
     , unfolded_typed_ast => UnfoldedTypedAst
     , folded_typed_ast => FoldedTypedAst
     , type_env  => TypeEnv
     , ast => Ast
     , warnings => Warnings }.

-spec build(module(), string(), aeso_compiler:options()) ->
          {ok, #{ byte_code := binary()
                 , fate_code := term()
                 , compiler_version := binary()
                 , abi_version := term()
                 , payable := boolean()
                 , warnings := [term()] }} | {error, [aeso_errors:error()]}.
%% @doc Full compile from source to FATE and bytecode using the provided
%%      backend module.
build(BackendMod, ContractString, Options) ->
    try
        CodeMap = string_to_fcode(ContractString, Options),
        #{ fcode := FCode, fcode_env := FCodeEnv } = CodeMap,
        #{ child_con_env := ChildContracts } = FCodeEnv,
        SavedFreshNames = maps:get(saved_fresh_names, FCodeEnv, #{}),
        FateCode = BackendMod:compile(ChildContracts, FCode, SavedFreshNames, Options),
        aeso_pp:pp_assembler(FateCode, Options),
        ByteCode = aeb_fate_code:serialize(FateCode, []),
        {ok, Version} = aeso_compiler:version(),
        {ok, CodeMap#{ byte_code => ByteCode,
                       compiler_version => Version,
                       fate_code => FateCode,
                       abi_version => aeb_fate_abi:abi_version(),
                       payable => maps:get(payable, FCode) }}
    catch throw:{error, Errors} -> {error, Errors}
    end.


