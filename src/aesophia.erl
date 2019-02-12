-module(aesophia).

-export([main/1]).

-define(OPT_SPEC,
    [ {src_file, undefined, undefined, string, "Sophia source code file"}
    , {verbose, $v, "verbose", undefined, "Verbose output"}
    , {help, $h, "help", undefined, "Show this message"}
    , {create_calldata, $c, "create_calldata", string,
        "Create calldata with respect to (compiled) contract in this file"}
    , {create_calldata_fun, undefined, "calldata_fun", string,
        "Deprecated calldata creation - using function + arguments - function"}
    , {create_calldata_args, undefined, "calldata_args", string,
        "Deprecated calldata creation - using function + arguments - arguments"}
    , {outfile, $o, "out", string, "Output the result to file (experimental)"} ]).

usage() ->
    getopt:usage(?OPT_SPEC, "aesophia").

main(Args) ->
    case getopt:parse(?OPT_SPEC, Args) of
        {ok, {Opts, []}} ->
            IsHelp = proplists:get_value(help, Opts, false),
            CreateCallData = proplists:get_value(create_calldata, Opts, undefined),
            if  IsHelp ->
                    usage();
                CreateCallData /= undefined ->
                    create_calldata(CreateCallData, Opts);
                true ->
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

    Res =
        try aeso_compiler:file(File, [pp_ast || Verbose]) of
            {ok, Map} ->
                io:format("\nCompiled successfully!\n"),
                {ok, Map};
            {error, Reason} ->
                io:format("\nError: ~p\n\n", [Reason]),
                {error, Reason}
        catch
            error:Error ->
                Where = hd(erlang:get_stacktrace()),
                ErrorString = io_lib:format("Error: ~p in\n   ~p", [Error, Where]),
                io:format("~s\n", [ErrorString]),
                {error, list_to_binary(lists:flatten(ErrorString))}
        end,
    write_outfile(OutFile, Res).


create_calldata(ContractFile, Opts) ->
    case file:read_file(ContractFile) of
        {ok, Bin} ->
            try
                Contract = binary_to_term(Bin),
                create_calldata_(Contract, Opts)
            catch _:_ ->
                io:format("Error: Bad contract file ~s\n\n", [ContractFile]), usage()
            end;
        {error, _} ->
            io:format("Error: Could not find file ~s\n\n", [ContractFile]), usage()
    end.


create_calldata_(Contract, Opts) ->
    case proplists:get_value(src_file, Opts, undefined) of
        undefined -> %% Check if old deprecated style is used
            case {proplists:get_value(create_calldata_fun, Opts, undefined),
                  proplists:get_value(create_calldata_args, Opts, undefined)} of
                {undefined, _} ->
                    io:format("Error: not enough create call data input\n\n"), usage();
                {_, undefined} ->
                    io:format("Error: not enough create call data input\n\n"), usage();
                {Fun, Args} ->
                    create_calldata(Contract, Fun, Args, Opts)
            end;
        CallFile ->
            case file:read_file(CallFile) of
                {ok, Bin} ->
                    create_calldata(Contract, "", binary_to_list(Bin), Opts);
                {error, _} ->
                    io:format("Error: Could not find file ~s\n\n", [CallFile]), usage()
            end
    end.

create_calldata(Contract, CallFun, CallArgs, Opts) ->
    OutFile = proplists:get_value(outfile, Opts, undefined),

    Res = try
        case aeso_compiler:create_calldata(Contract, CallFun, CallArgs) of
            {ok, CallData, _CallDataType, _OutputType} ->
                io:format("Call data created successfully!\n"),
                {ok, CallData};
            Err = {error, Reason} ->
                io:format("Error: Create calldata failed: ~p\n\n", [Reason]),
                Err
        end
    catch
        error:Error ->
            Where = hd(erlang:get_stacktrace()),
            ErrorString = io_lib:format("Error: ~p in\n   ~p", [Error, Where]),
            io:format("~s\n", [ErrorString]),
            {error, list_to_binary(lists:flatten(ErrorString))}
    end,
    write_outfile(OutFile, Res).


write_outfile(undefined, _) -> ok;
write_outfile(Out, Res)  ->
    %% Lazy approach
    file:write_file(Out, term_to_binary(Res)),
    io:format("Output written to: ~s\n\n", [Out]).
