%%%-------------------------------------------------------------------
%%% @doc Behaviour for Sophia backends (IR -> VM code)
%%% Implementations must compile a single contract's FCode to target VM code.
%%%-------------------------------------------------------------------
-module(aeso_backend).

-export_type([child_contracts/0]).

-type child_contracts() :: #{binary() => map()}.

-callback compile(child_contracts(), map(), map(), list()) -> term().
%% @doc
%%  compile(ChildContracts, FCode, SavedFreshNames, Options) -> Target VM code term.
%%  - ChildContracts contains compiled fcode for nested contracts
%%  - FCode is the IR for the current contract
%%  - SavedFreshNames is a map from fresh variable names
%%  - Options is the compiler option proplist


