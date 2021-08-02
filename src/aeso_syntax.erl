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
-export_type([decl/0, letbind/0, typedef/0, pragma/0]).
-export_type([arg/0, field_t/0, constructor_t/0, named_arg_t/0]).
-export_type([type/0, constant/0, expr/0, arg_expr/0, field/1, stmt/0, alt/0, lvalue/0, elim/0, pat/0]).
-export_type([letfun/0, letval/0, fundecl/0]).
-export_type([ast/0]).
-export_type([predicate/0, liquid_type/0, dep_type/1, dep_arg_t/1]).

-type ast() :: [decl()].

-type ann_line()   :: integer().
-type ann_col()    :: integer().
-type ann_origin() :: system | user.
-type ann_format() :: '?:' | hex | infix | prefix | elif.

-type ann() :: [ {line, ann_line()} | {col, ann_col()} | {format, ann_format()} | {origin, ann_origin()}
               | stateful | private | payable | main | interface].

-type name() :: string().
-type id()   :: {id,   ann(), name()}.
-type con()  :: {con,  ann(), name()}.
-type qid()  :: {qid,  ann(), [name()]}.
-type qcon() :: {qcon, ann(), [name()]}.
-type tvar() :: {tvar, ann(), name()}.

-type decl() :: {contract_main, ann(), con(), [decl()]}
              | {contract_child, ann(), con(), [decl()]}
              | {contract_interface, ann(), con(), [decl()]}
              | {namespace, ann(), con(), [decl()]}
              | {pragma, ann(), pragma()}
              | {type_decl, ann(), id(), [tvar()]} % Only for error msgs
              | {type_def, ann(), id(), [tvar()], typedef()}
              | {fun_clauses, ann(), id(), type(), [letfun() | fundecl()]}
              | {block, ann(), [decl()]}
              | fundecl()
              | letfun()
              | letval(). % Only for error msgs

-type compiler_version() :: [non_neg_integer()].

-type pragma() :: {compiler, '==' | '<' | '>' | '=<' | '>=', compiler_version()}.


-type letval()  :: {letval, ann(), pat(), expr()}.
-type letfun()  :: {letfun, ann(), id(), [pat()], type(), expr()}.
-type fundecl() :: {fun_decl, ann(), id(), type()}.

-type letbind()
    :: letfun()
     | letval().

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
              | {args_t, ann(), [type()]}   %% old tuple syntax, old for error messages
              | {bytes_t, ann(), integer() | any}
              | {named_t, ann(), id(), type()}
              | id()  | qid()
              | con() | qcon()  %% contracts
              | tvar().

%% Predicate for a liquid type
-type predicate() :: [expr()].

%% Dependent type
%% FIXME it is very inconsistent with the reality...
-type dep_type(Qual)
    :: {refined_t, ann(), id(), type(), Qual}
     | {dep_fun_t, ann(), [dep_arg_t(Qual)], dep_type(Qual)}
     | {dep_record_t, ann(), type(), [dep_field_t(Qual)]}
     | {dep_variant_t, ann(), id(), type(), Qual | undefined, [dep_constr_t(Qual)]}
     | {dep_list_t, ann(), id(), dep_type(Qual), Qual}
     | tvar().
-type liquid_type() :: dep_type(predicate()).

-type dep_constr_t(Qual) :: {constr_t, ann(), con(), [dep_type(Qual)]}.

-type dep_arg_t(Qual) :: {dep_arg_t, ann(), id(), dep_type(Qual)}.

-type dep_field_t(Qual) :: {field_t, ann(), id(), dep_type(Qual)}.

-type named_arg_t() :: {named_arg_t, ann(), id(), type(), expr()}.

-type constant()
    :: {int, ann(), integer()}
     | {bool, ann(), true | false}
     | {bytes, ann(), binary()}
     | {account_pubkey, ann(), binary()}
     | {contract_pubkey, ann(), binary()}
     | {oracle_pubkey, ann(), binary()}
     | {oracle_query_id, ann(), binary()}
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
     | {list_comp, ann(), expr(), [comprehension_exp()]}
     | {typed, ann(), expr(), type()}
     | {record_or_map(), ann(), [field(expr())]}
     | {record_or_map(), ann(), expr(), [field(expr())]} %% record/map update
     | {map, ann(), [{expr(), expr()}]}
     | {map_get, ann(), expr(), expr()}
     | {map_get, ann(), expr(), expr(), expr()}
     | {block, ann(), [stmt()]}
     | {op(), ann()}
     | id() | qid() | con() | qcon()
     | constant().

-type record_or_map() :: record | map | record_or_map_error.

-type comprehension_exp() :: [ {comprehension_bind, pat(), expr()}
                             | {comprehension_if, ann(), expr()}
                             | letbind() ].

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
             | {typed, ann(), pat(), type()}
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
