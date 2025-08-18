%%%-------------------------------------------------------------------
%%% Options normalization and helpers
%%%-------------------------------------------------------------------
-module(aeso_options).

-export([ normalize/1
        , add_default_include/2
        ]).

-spec normalize(list()) -> list().
normalize(Opts) ->
    %% Keep as proplist for minimal intrusion; later we can migrate to maps
    Opts.

add_default_include(File, Options) ->
    case lists:keymember(include, 1, Options) of
        true  -> Options;
        false ->
            Dir = filename:dirname(File),
            {ok, Cwd} = file:get_cwd(),
            [{include, {file_system, [Cwd, aeso_utils:canonical_dir(Dir)]}} | Options]
    end.


