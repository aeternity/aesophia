%%%-------------------------------------------------------------------
%%% @copyright (C) 2018, Aeternity Anstalt
%%% @doc
%%%     Shared type definition for why_record().
%%%     This header file contains the why_record type used across
%%%     multiple typing modules.
%%% @end
%%%-------------------------------------------------------------------

%% Type definition for record context information
-type why_record() :: aeso_syntax:field(aeso_syntax:expr())
                    | {var_args, aeso_syntax:ann(), aeso_syntax:expr()}
                    | {proj, aeso_syntax:ann(), aeso_syntax:expr(), aeso_syntax:id()}.
