%%%-------------------------------------------------------------------
%%% Source loading and stdlib/include path handling extracted from aeso_parser
%%%-------------------------------------------------------------------
-module(aeso_source).

-export([ read_file/2
        , read_file_/2
        , stdlib_options/0
        , get_include_code/3
        , include_current_file_dir/2
        , hash_include/2
        ]).

-include("aeso_utils.hrl").

read_file(File, Opts) ->
    case proplists:get_value(include, Opts, {explicit_files, #{}}) of
        {file_system, Paths} ->
            secure_read_from_paths(Paths, File);
        {explicit_files, Files} ->
            case maps:get(binary_to_list(File), Files, not_found) of
                not_found -> {error, not_found};
                Src       -> {ok, File, Src}
            end;
        escript ->
            try
                Escript        = escript:script_name(),
                {ok, Sections} = escript:extract(Escript, []),
                Archive        = proplists:get_value(archive, Sections),
                FileName       = binary_to_list(filename:join([aesophia, priv, stdlib, File])),
                case zip:extract(Archive, [{file_list, [FileName]}, memory]) of
                    {ok, [{_, Src}]} -> {ok, escript, Src};
                    _                -> {error, not_found}
                end
            catch _:_ ->
                {error, not_found}
            end
    end.

read_file_(Path, File) ->
    %% Legacy helper retained for callers that pass a single Path
    secure_read_from_paths([Path], File).

%% Ensure includes resolve within one of the configured include roots, but
%% allow relative paths like ".." across siblings as long as they remain under
%% any allowed root.
secure_read_from_paths(Paths, File) ->
    FileStr = case File of
                  B when is_binary(B) -> binary_to_list(B);
                  L when is_list(L)   -> L
              end,
    CanonicalRoots = [aeso_utils:canonical_dir(P) || P <- Paths],
    lists:foldl(
      fun(Path, Acc) ->
          case Acc of
              {ok, _, _} -> Acc;
              _ ->
                  AbsFile = filename:absname(filename:join(Path, FileStr)),
                  FileDir = filename:dirname(AbsFile),
                  case is_under_any_root(FileDir, CanonicalRoots) of
                      true ->
                          case file:read_file(AbsFile) of
                              {ok, Bin} -> {ok, aeso_utils:canonical_dir(FileDir), Bin};
                              _Err      -> Acc
                          end;
                      false -> Acc
                  end
          end
      end,
      {error, not_found},
      Paths).

is_under_any_root(FileDir, Roots) ->
    FParts = filename:split(FileDir),
    lists:any(
      fun(Root) ->
          RParts = filename:split(Root),
          RLen = length(RParts),
          length(FParts) >= RLen andalso lists:sublist(FParts, RLen) =:= RParts
      end,
      Roots).

stdlib_options() ->
    StdLibDir = aeso_stdlib:stdlib_include_path(),
    case filelib:is_dir(StdLibDir) of
        true  -> [{include, {file_system, [StdLibDir]}}];
        false -> [{include, escript}]
    end.

get_include_code(File, Ann, Opts) ->
    Opts1 = include_current_file_dir(Opts, Ann),
    case {read_file(File, Opts1), read_file(File, stdlib_options())} of
        {{ok, Dir, Bin}, {ok, _}} ->
            case filename:basename(File) == File of
                true -> { error
                        , { aeso_parser:ann_pos(Ann)
                          , parse_error
                          , "Illegal redefinition of standard library " ++ binary_to_list(File)
                          }};
                false -> {ok, Dir, binary_to_list(Bin)}
            end;
        {_, {ok, _, Bin}} ->
            {ok, stdlib, binary_to_list(Bin)};
        {{ok, Dir, Bin}, _} ->
            {ok, Dir, binary_to_list(Bin)};
        {_, _} ->
            {error, {aeso_parser:ann_pos(Ann), include_error, File}}
    end.

include_current_file_dir(Opts, Ann) ->
    case {proplists:get_value(dir, Ann, undefined),
          proplists:get_value(include, Opts, undefined)} of
        {undefined, _} -> Opts;
        {CurrDir, {file_system, Paths}} ->
            case lists:member(CurrDir, Paths) of
                false -> [{include, {file_system, [CurrDir | Paths]}} | Opts];
                true  -> Opts
            end;
        {_, _} -> Opts
    end.

hash_include(File, Code) when is_binary(File) ->
    hash_include(binary_to_list(File), Code);
hash_include(File, Code) when is_list(File) ->
    {filename:basename(File), crypto:hash(sha256, Code)}.


