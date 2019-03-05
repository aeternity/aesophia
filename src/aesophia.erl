-module(aesophia).

-export([main/1]).

-define(OPT_SPEC,
    [ {src_file, undefined, undefined, string, "Sophia source code file"}
    , {version, $V, "version", undefined, "Print compiler version"}
    , {verbose, $v, "verbose", undefined, "Verbose output"}
    , {help, $h, "help", undefined, "Show this message"}
    , {outfile, $o, "out", string, "Output file (experimental)"} ]).

usage() ->
    getopt:usage(?OPT_SPEC, "aesophia").

main(Args) ->
    case getopt:parse(?OPT_SPEC, Args) of
        {ok, {Opts, []}} ->
            case Opts of
                [version] ->
                    print_vsn();
                [help] ->
                    usage();
                _ ->
                    compile(Opts)
            end;

        {ok, {_, NonOpts}} ->
            io:format("Can't understand ~p\n\n", [NonOpts]),
            usage();

        {error, {Reason, Data}} ->
            io:format("Error: ~s ~p\n\n", [Reason, Data]),
            usage()
    end.


compile(Opts) ->
    case proplists:get_value(src_file, Opts, undefined) of
        undefined ->
            io:format("Error: no input source file\n\n"),
            usage();
        File ->
            compile(File, Opts)
    end.

compile(File, Opts) ->
    Verbose = proplists:get_value(verbose, Opts, false),
    OutFile = proplists:get_value(outfile, Opts, undefined),

    try
        Res = aeso_compiler:file(File, [pp_ast || Verbose]),
        write_outfile(OutFile, Res),
        io:format("\nCompiled successfully!\n")
    catch
        %% The compiler errors.
        error:{type_errors, Errors} ->
            io:format("\n~s\n", [string:join(["** Type errors\n" | Errors], "\n")]);
        error:{parse_errors, Errors} ->
            io:format("\n~s\n", [string:join(["** Parse errors\n" | Errors], "\n")]);
        error:{code_errors, Errors} ->
            ErrorStrings = [ io_lib:format("~p", [E]) || E <- Errors ],
            io:format("\n~s\n", [string:join(["** Code errors\n" | ErrorStrings], "\n")]);
        %% General programming errors in the compiler.
        error:Error ->
            Where = hd(erlang:get_stacktrace()),
            ErrorString = io_lib:format("Error: ~p in\n   ~p", [Error,Where]),
            io:format("\n~s\n", [ErrorString])
    end.

write_outfile(undefined, _) -> ok;
write_outfile(Out, ResMap)  ->
    %% Lazy approach
    file:write_file(Out, term_to_binary(ResMap)),
    io:format("Output written to: ~s\n", [Out]).

print_vsn() ->
    {ok, Vsn} = aeso_compiler:version(),
    io:format("Compiler version: ~s\n", [Vsn]).
