%%% -*- erlang-indent-level:4; indent-tabs-mode: nil -*-
%%%-------------------------------------------------------------------
%%% @copyright (C) 2017, Aeternity Anstalt
%%% @doc Sophia abstract syntax types.
%%%
%%% @end
%%%-------------------------------------------------------------------

-module(aeso_syntax).

-export([get_ann/1, get_ann/2, get_ann/3, set_ann/2, qualify/2]).

-export_type([ann_line/0, ann_col/0, ann_origin/0, ann_format/0, ann/0]).
-export_type([name/0, id/0, con/0, qid/0, qcon/0, tvar/0, op/0]).
-export_type([bin_op/0, un_op/0]).
-export_type([decl/0, letbind/0, typedef/0]).
-export_type([arg/0, field_t/0, constructor_t/0, named_arg_t/0]).
-export_type([type/0, constant/0, expr/0, arg_expr/0, field/1, stmt/0, alt/0, lvalue/0, elim/0, pat/0]).
-export_type([ast/0]).

-type ast() :: [decl()].

-type ann_line()   :: integer().
-type ann_col()    :: integer().
-type ann_origin() :: system | user.
-type ann_format() :: '?:' | hex | infix | prefix | elif.

-type ann() :: [{line, ann_line()} | {col, ann_col()} | {format, ann_format()} | {origin, ann_origin()}].

-type name() :: string().
-type id()   :: {id,   ann(), name()}.
-type con()  :: {con,  ann(), name()}.
-type qid()  :: {qid,  ann(), [name()]}.
-type qcon() :: {qcon, ann(), [name()]}.
-type tvar() :: {tvar, ann(), name()}.

-type decl() :: {contract, ann(), con(), [decl()]}
              | {namespace, ann(), con(), [decl()]}
              | {type_decl, ann(), id(), [tvar()]}
              | {type_def, ann(), id(), [tvar()], typedef()}
              | {fun_decl, ann(), id(), type()}
              | letbind().

-type letbind()
    :: {letval, ann(), id(), type(), expr()}
     | {letfun, ann(), id(), [arg()], type(), expr()}
     | {letrec, ann(), [letbind()]}.

-type arg() :: {arg, ann(), id(), type()}.

-type typedef()
    :: {alias_t, type()}
     | {record_t, [field_t()]}
     | {variant_t, [constructor_t()]}.

-type field_t() :: {field_t, ann(), id(), type()}.

-type constructor_t() :: {constr_t, ann(), con(), [type()]}.

-type type() :: {fun_t, ann(), [named_arg_t()], [type()], type()}
              | {app_t, ann(), type(), [type()]}
              | {tuple_t, ann(), [type()]}
              | {bytes_t, ann(), integer()}
              | id()  | qid()
              | con() | qcon()  %% contracts
              | tvar().

-type named_arg_t() :: {named_arg_t, ann(), id(), type(), expr()}.

-type constant()
    :: {int, ann(), integer()}
     | {bool, ann(), true | false}
     | {hash, ann(), binary()}
     | {account_pubkey, binary()}
     | {contract_pubkey, binary()}
     | {oracle_pubkey, binary()}
     | {oracle_query_id, binary()}
     | {string, ann(), binary()}
     | {char, ann(), integer()}.

-type op() :: bin_op() | un_op().

-type bin_op() :: '+' | '-' | '*' | '/' | mod | '^'
                | '++' | '::' | '<' | '>' | '=<' | '>=' | '==' | '!='
                | '||' | '&&' | '..'.
-type un_op() :: '-' | '!'.

-type expr()
    :: {lam, ann(), [arg()], expr()}
     | {'if', ann(), expr(), expr(), expr()}
     | {switch, ann(), expr(), [alt()]}
     | {app, ann(), expr(), [arg_expr()]}
     | {proj, ann(), expr(), id()}
     | {tuple, ann(), [expr()]}
     | {list, ann(), [expr()]}
     | {typed, ann(), expr(), type()}
     | {record, ann(), [field(expr())]}
     | {record, ann(), expr(), [field(expr())]} %% record update
     | {map, ann(), expr(), [field(expr())]}    %% map update
     | {map, ann(), [{expr(), expr()}]}
     | {map_get, ann(), expr(), expr()}
     | {map_get, ann(), expr(), expr(), expr()}
     | {block, ann(), [stmt()]}
     | {op(), ann()}
     | id() | qid() | con() | qcon()
     | constant().

-type arg_expr() :: expr() | {named_arg, ann(), id(), expr()}.

%% When lvalue is a projection this is sugar for accessing fields in nested
%% records. For instance,
%%    r { x.y: 5 }
%% is the same as
%%    r { x: r.x { y: 5 } }
-type field(E) :: {field, ann(), lvalue(), E}
                | {field, ann(), lvalue(), id(), E}.  %% modifying a field (id is previous value)

-type stmt() :: letbind()
              | expr().

-type alt() :: {'case', ann(), pat(), expr()}.

-type lvalue() :: nonempty_list(elim()).

-type elim() :: {proj, ann(), id()}
              | {map_get, ann(), expr()}
              | {map_get, ann(), expr(), expr()}.

-type pat() :: {app, ann(), con() | op(), [pat()]}
             | {tuple, ann(), [pat()]}
             | {list, ann(), [pat()]}
             | {record, ann(), [field(pat())]}
             | constant()
             | con()
             | id().

get_ann(Node) when is_tuple(Node) -> element(2, Node);
get_ann(Ann)  when is_list(Ann)   -> Ann.

set_ann(Ann1, Node) when is_tuple(Node) -> setelement(2, Node, Ann1);
set_ann(Ann1, Ann) when is_list(Ann) -> Ann1.

get_ann(Key, Node) ->
    proplists:get_value(Key, get_ann(Node)).

get_ann(Key, Node, Default) ->
    proplists:get_value(Key, get_ann(Node), Default).

qualify({con, Ann, N}, X)             -> qualify({qcon, Ann, [N]}, X);
qualify({qcon, _, NS}, {con, Ann, C}) -> {qcon, Ann, NS ++ [C]};
qualify({qcon, _, NS}, {id, Ann, X})  -> {qid, Ann, NS ++ [X]}.

