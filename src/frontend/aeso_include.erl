%%%-------------------------------------------------------------------
%%% Include expansion extracted from aeso_parser
%%%-------------------------------------------------------------------
-module(aeso_include).

-export([ expand_includes/3
        , auto_imports/1
        ]).

-include("aeso_parse_lib.hrl").

%% @doc Expand `include` directives and auto-imports in the parsed AST. Keeps
%%      track of included files to avoid cycles and to annotate include type.
expand_includes(AST, Included, Opts) ->
    Ann  = [{origin, system}],
    AST1 = [ {include, Ann, {string, Ann, File}}
             || File <- lists:usort(auto_imports(AST)) ] ++ AST,
    expand_includes(AST1, Included, [], Opts).

expand_includes([], Included, Acc, Opts) ->
    case lists:member(keep_included, Opts) of
        false -> {ok, lists:reverse(Acc)};
        true  -> {ok, {lists:reverse(Acc), Included}}
    end;
expand_includes([{include, Ann, {string, _SAnn, File}} | AST], Included, Acc, Opts) ->
    case aeso_source:get_include_code(File, Ann, Opts) of
        {ok, AbsDir, Code} ->
            Hashed = aeso_source:hash_include(File, Code),
            case sets:is_element(Hashed, Included) of
                false ->
                    SrcFile = proplists:get_value(src_file, Opts, no_file),
                    IncludeType = case proplists:get_value(file, Ann) of
                                      SrcFile -> direct;
                                      _       -> indirect
                                  end,
                    Opts1 = lists:keystore(src_file, 1, Opts, {src_file, File}),
                    Opts2 = lists:keystore(src_dir, 1, Opts1, {src_dir, AbsDir}),
                    Opts3 = lists:keystore(include_type, 1, Opts2, {include_type, IncludeType}),
                    Included1 = sets:add_element(Hashed, Included),
                    case aeso_parser:parse_and_scan(aeso_parser:file(), Code, Opts3) of
                        {ok, AST1} ->
                            expand_includes(AST1 ++ AST, Included1, Acc, Opts);
                        Err = {error, _} -> Err
                    end;
                true -> expand_includes(AST, Included, Acc, Opts)
            end;
        Err = {error, _} -> Err
    end;
expand_includes([E | AST], Included, Acc, Opts) ->
    expand_includes(AST, Included, [E | Acc], Opts).

%% @doc Detect standard library files that should be auto-included based on
%%      language constructs used in the AST.
auto_imports({comprehension_bind, _, _}) -> [<<"ListInternal.aes">>];
auto_imports({'..', _})                  -> [<<"ListInternal.aes">>];
auto_imports(L) when is_list(L) ->
    lists:flatmap(fun auto_imports/1, L);
auto_imports(T) when is_tuple(T) ->
    auto_imports(tuple_to_list(T));
auto_imports(_) -> [].


