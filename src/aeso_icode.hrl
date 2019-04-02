
-include_lib("aebytecode/include/aeb_typerep_def.hrl").

-record(arg, {name::string(), type::?Type()}).

-type expr() :: term().
-type arg() :: #arg{name::string(), type::?Type()}.
-type arg_list() :: [arg()].

-record(fun_dec, { name :: string()
                 , args :: arg_list()
                 , body :: expr()}).

-record(var_ref, { name :: string() | list(string()) | {builtin, atom() | tuple()}}).

-record(prim_call_contract,
    { gas      :: expr()
    , address  :: expr()
    , value    :: expr()
    , arg      :: expr()
    , type_hash:: expr()
    }).

-record(prim_balance,    { address :: expr() }).
-record(prim_block_hash, { height :: expr() }).
-record(prim_put,        { state :: expr() }).

-record(integer, {value :: integer()}).

-record(tuple,   {cpts  :: [expr()]}).

-record(list,    {elems :: [expr()]}).

-record(unop,    { op   :: term()
                 , rand :: expr()}).

-record(binop,   { op   :: term()
                 , left :: expr()
                 , right :: expr()}).

-record(ifte,    { decision :: expr()
                 , then :: expr()
                 , else :: expr()}).

-record(switch,  { expr  :: expr()
                 , cases :: [{expr(),expr()}]}).

-record(funcall, { function :: expr()
                 , args     :: [expr()]}).

-record(lambda,  { args :: arg_list(),
                   body :: expr()}).

-record(missing_field, { format :: string()
                       , args   :: [term()]}).

-record(seq, {exprs :: [expr()]}).

-record(event, {topics :: [expr()], payload :: expr()}).
