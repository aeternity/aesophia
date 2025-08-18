%%%-------------------------------------------------------------------
%%% @doc Utilities to compare two FATE codes for semantic equivalence
%%%-------------------------------------------------------------------
-module(aeso_fate_compare).

-export([compare/2]).

-spec compare(term(), term()) -> ok | {error, [iolist()] }.
compare(FCode1, FCode2) ->
    Funs1 = aeb_fate_code:functions(FCode1),
    Funs2 = aeb_fate_code:functions(FCode2),
    Syms1 = aeb_fate_code:symbols(FCode1),
    Syms2 = aeb_fate_code:symbols(FCode2),
    FunHashes1 = maps:keys(Funs1),
    FunHashes2 = maps:keys(Funs2),
    case FunHashes1 == FunHashes2 of
        false ->
            InByteCode   = [ binary_to_list(maps:get(H, Syms1)) || H <- FunHashes1 -- FunHashes2 ],
            InSourceCode = [ binary_to_list(maps:get(H, Syms2)) || H <- FunHashes2 -- FunHashes1 ],
            Msg = [ io_lib:format("- Functions in the byte code but not in the source code:\n    ~s\n", [string:join(InByteCode, ", ")]) || InByteCode /= [] ] ++
                  [ io_lib:format("- Functions in the source code but not in the byte code:\n    ~s\n", [string:join(InSourceCode, ", ")]) || InSourceCode /= [] ],
            {error, Msg};
        true ->
            case lists:append([ compare_fun(maps:get(H, Syms1), Fun1, Fun2)
                                || {{H, Fun1}, {_, Fun2}} <- lists:zip(maps:to_list(Funs1),
                                                                       maps:to_list(Funs2)) ]) of
                [] -> ok;
                Errs -> {error, Errs}
            end
    end.

compare_fun(_Name, Fun, Fun) -> [];
compare_fun(Name, {Attr, Type, _}, {Attr, Type, _}) ->
    [io_lib:format("- The implementation of the function ~s is different.\n", [Name])];
compare_fun(Name, {Attr1, Type, _}, {Attr2, Type, _}) ->
    [io_lib:format("- The attributes of the function ~s differ:\n    Byte code:   ~s\n    Source code: ~s\n",
                   [Name, string:join([ atom_to_list(A) || A <- Attr1 ], ", "),
                          string:join([ atom_to_list(A) || A <- Attr2 ], ", ")])];
compare_fun(Name, {_, Type1, _}, {_, Type2, _}) ->
    [io_lib:format("- The type of the function ~s differs:\n    Byte code:   ~s\n    Source code: ~s\n",
                   [Name, pp_sig(Type1), pp_sig(Type2)])].

pp_sig({[Arg], Res}) ->
    io_lib:format("~s => ~s", [pp_type(Arg), pp_type(Res)]);
pp_sig({Args, Res}) ->
    io_lib:format("(~s) => ~s", [string:join([pp_type(Arg) || Arg <- Args], ", "), pp_type(Res)]).

pp_type(T) -> io_lib:format("~w", [T]).


