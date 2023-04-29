-module(aeso_tc_options).

-export([ create_options/1
        , get_option/2
        , when_option/2
        , when_warning/2
        ]).

%% -- Moved functions --------------------------------------------------------

type_error(A) -> aeso_tc_errors:type_error(A).
create_type_errors() -> aeso_tc_errors:create_type_errors().
destroy_and_report_type_errors(A) -> aeso_tc_errors:destroy_and_report_type_errors(A).

%% -------

all_warnings() -> aeso_tc_warnings:all_warnings().

%% ---------------------------------------------------------------------------

create_options(Options) ->
    aeso_tc_ets_manager:ets_new(options, [set]),
    Tup = fun(Opt) when is_atom(Opt) -> {Opt, true};
             (Opt) when is_tuple(Opt) -> Opt end,
    aeso_tc_ets_manager:ets_insert(options, lists:map(Tup, Options)).

get_option(Key, Default) ->
    case aeso_tc_ets_manager:ets_lookup(options, Key) of
        [{_Key, Val}] -> Val;
        _             -> Default
    end.

when_option(Opt, Do) ->
    get_option(Opt, false) andalso Do().

when_warning(Warn, Do) ->
    case lists:member(Warn, all_warnings()) of
        false ->
            create_type_errors(),
            type_error({unknown_warning, Warn}),
            destroy_and_report_type_errors(aeso_tc_env:init_env());
        true ->
            case aeso_tc_ets_manager:ets_tab_exists(warnings) of
                true ->
                    IsEnabled = get_option(Warn, false),
                    IsAll = get_option(warn_all, false) andalso lists:member(Warn, all_warnings()),
                    if
                        IsEnabled orelse IsAll -> Do();
                        true -> ok
                    end;
                false ->
                    ok
            end
    end.
