%%%-------------------------------------------------------------------
%%% Pretty printing helpers split from aeso_compiler
%%%-------------------------------------------------------------------
-module(aeso_pp).

-export([ pp_sophia_code/2
        , pp_ast/2
        , pp_typed_ast/2
        , pp_assembler/2
        ]).

pp_sophia_code(C, Opts) ->  pp(C, Opts, pp_sophia_code, fun(Code) ->
                                io:format("~s\n", [prettypr:format(aeso_pretty:decls(Code))])
                            end).

pp_ast(C, Opts)      ->  pp(C, Opts, pp_ast, fun aeso_ast:pp/1).
pp_typed_ast(C, Opts)->  pp(C, Opts, pp_typed_ast, fun aeso_ast:pp_typed/1).

pp_assembler(C, Opts) ->  pp(C, Opts, pp_assembler, fun(Asm) -> io:format("~s", [aeb_fate_asm:pp(Asm)]) end).

pp(Code, Options, Option, PPFun) ->
    case proplists:lookup(Option, Options) of
        {Option1, true} when Option1 =:= Option ->
            PPFun(Code);
        none ->
            ok
    end.


