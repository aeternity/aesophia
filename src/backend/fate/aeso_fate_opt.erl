%%%-------------------------------------------------------------------
%%% @doc Structured code (scode) optimizer for FATE backend
%%%-------------------------------------------------------------------
-module(aeso_fate_opt).

-export([
    optimize_scode/2,
    optimize_fun/4,
    flatten/1,
    desugar/1,
    unannotate/1
]).

-include("aeso_fate_env.hrl").

%% Pull in debug helpers (module exists later in refactor; for now keep local shim)
-define(debug(Tag, Options, Fun), aeso_fcode_to_fate:debug(Tag, Options, Fun)).

%% Public API
optimize_scode(Funs, Options) ->
    maps:map(fun(Name, Def) -> optimize_fun(Funs, Name, Def, Options) end, Funs).

-define(MAX_SIMPL_ITERATIONS, 10).

optimize_fun(_Funs, Name, {Attrs, Sig, Code}, Options) ->
    Code0 = flatten(Code),
    ?debug(opt, Options, fun() -> io:format("Optimizing ~s\n", [Name]) end),
    Code1 = simpl_loop(0, Code0, Options),
    Code2 = desugar(Code1),
    {Attrs, Sig, Code2}.

flatten(missing) -> missing;
flatten(Code)    -> lists:map(fun flatten_s/1, lists:flatten(Code)).

flatten_s({switch, Arg, Type, Alts, Catch}) ->
    {switch, Arg, Type, [flatten(Alt) || Alt <- Alts], flatten(Catch)};
flatten_s(I) -> I.

%% Simplification loop and helpers (lifted 1:1)
simpl_loop(N, Code, Options) when N >= ?MAX_SIMPL_ITERATIONS ->
    ?debug(opt, Options, fun() -> io:format("  No simpl_loop fixed_point after ~p iterations.\n\n", [N]) end),
    Code;
simpl_loop(N, Code, Options) ->
    ACode = annotate_code(Code),
    Code1 = simplify(ACode, Options),
    Code2 = unannotate(Code1),
    case Code == Code2 of
        true  -> Code2;
        false -> simpl_loop(N + 1, Code2, Options)
    end.

%% Pretty printing functions removed in refactor (not used outside debug)

%% Analysis, attributes, rules, and helpers are copied from original module.
%% For brevity in this initial step, we temporarily proxy to original functions.

annotate_code(Code) -> aeso_fcode_to_fate:annotate_code(Code).
simplify(Code, Options) -> aeso_fcode_to_fate:simplify(Code, Options).
unannotate({switch, Arg, Type, Alts, Def}) ->
    [{switch, Arg, Type, [unannotate(A) || A <- Alts], unannotate(Def)}];
unannotate(missing) -> missing;
unannotate(Code) when is_list(Code) ->
    lists:flatmap(fun unannotate/1, Code);
unannotate({i, _Ann, I}) -> [I].

desugar({'ADD', ?a, ?i(1), ?a}) -> [aeb_fate_ops:inc()];
desugar({'ADD', A,  ?i(1), A})  -> [aeb_fate_ops:inc(desugar_arg(A))];
desugar({'ADD', ?a, ?a, ?i(1)}) -> [aeb_fate_ops:inc()];
desugar({'ADD', A,  A,  ?i(1)}) -> [aeb_fate_ops:inc(desugar_arg(A))];
desugar({'SUB', ?a, ?a, ?i(1)}) -> [aeb_fate_ops:dec()];
desugar({'SUB', A, A, ?i(1)})   -> [aeb_fate_ops:dec(desugar_arg(A))];
desugar({'STORE', ?a, A})       -> [aeb_fate_ops:push(desugar_arg(A))];
desugar({'STORE', R, ?a})       -> [aeb_fate_ops:pop(desugar_arg(R))];
desugar({switch, Arg, Type, Alts, Def}) ->
    [{switch, desugar_arg(Arg), Type, [desugar(A) || A <- Alts], desugar(Def)}];
desugar(missing) -> missing;
desugar(Code) when is_list(Code) ->
    lists:flatmap(fun desugar/1, Code);
desugar(I) -> [desugar_args(I)].

desugar_args(I) when is_tuple(I) ->
    [Op | Args] = tuple_to_list(I),
    list_to_tuple([Op | lists:map(fun desugar_arg/1, Args)]);
desugar_args(I) -> I.

desugar_arg(?s(N)) -> {var, -N};
desugar_arg(A) -> A.


