%%%-------------------------------------------------------------------
%%% Shared FATE env macros, types and records
%%%-------------------------------------------------------------------

-ifndef(AESO_FATE_ENV_HRL).
-define(AESO_FATE_ENV_HRL, true).

%% Macros used across FATE backend
-define(i(X), {immediate, X}).
-define(a,    {stack, 0}).
-define(s(N), {store, N}).
-define(void, {var, 9999}).

%% Types for structured code (scode)
-type scode()  :: [sinstr()].
-type sinstr() :: {switch, arg(), stype(), [maybe_scode()], maybe_scode()}  %% last arg is catch-all
                | switch_body
                | loop
                | tuple() | atom().    %% FATE instruction

-type arg() :: tuple(). %% Not exported: aeb_fate_ops:fate_arg().

%% Annotated scode
-type scode_a()  :: [sinstr_a()].
-type sinstr_a() :: {switch, arg(), stype(), [maybe_scode_a()], maybe_scode_a()}  %% last arg is catch-all
                  | {i, ann(), tuple()}.    %% FATE instruction with annotation

-type ann() :: #{ live_in := vars(), live_out := vars() }.
-type var() :: {var, integer()}.
-type vars() :: ordsets:ordset(var()).

-type stype()         :: tuple | boolean | {variant, [non_neg_integer()]}.
-type maybe_scode()   :: missing | scode().
-type maybe_scode_a() :: missing | scode_a().

%% Environment record for code generation
-record(env, { contract,
               vars              = [],
               locals            = [],
               current_function,
               tailpos           = true,
               child_contracts   = #{},
               saved_fresh_names = #{},
               options           = [],
               debug_info        = false }).

-endif.


