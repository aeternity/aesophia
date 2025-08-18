-ifndef(AESO_TYPING_HRL).
-define(AESO_TYPING_HRL, true).

%% Shared types and records for typing/inference modules

-type utype() :: {fun_t, aeso_syntax:ann(), named_args_t(), [utype()] | var_args, utype()}
               | {app_t, aeso_syntax:ann(), utype(), [utype()]}
               | {tuple_t, aeso_syntax:ann(), [utype()]}
               | {bytes_t, aeso_syntax:ann(), non_neg_integer() | any}
               | aeso_syntax:id()  | aeso_syntax:qid()
               | aeso_syntax:con() | aeso_syntax:qcon()
               | aeso_syntax:tvar()
               | {if_t, aeso_syntax:ann(), aeso_syntax:id(), utype(), utype()}
               | uvar().

-type uvar() :: {uvar, aeso_syntax:ann(), reference()}.

-type named_args_t() :: uvar() | [{named_arg_t, aeso_syntax:ann(), aeso_syntax:id(), utype(), aeso_syntax:expr()}].

-type type_id() :: aeso_syntax:id() | aeso_syntax:qid() | aeso_syntax:con() | aeso_syntax:qcon().

-define(is_type_id(T), element(1, T) =:= id orelse
                       element(1, T) =:= qid orelse
                       element(1, T) =:= con orelse
                       element(1, T) =:= qcon).

-type why_record() :: aeso_syntax:field(aeso_syntax:expr())
                    | {var_args, aeso_syntax:ann(), aeso_syntax:expr()}
                    | {proj, aeso_syntax:ann(), aeso_syntax:expr(), aeso_syntax:id()}.

-type pos() :: aeso_errors:pos().

-record(named_argument_constraint,
    {args :: named_args_t(),
     name :: aeso_syntax:id(),
     type :: utype()}).

-record(dependent_type_constraint,
    { named_args_t     :: named_args_t()
    , named_args       :: [aeso_syntax:arg_expr()]
    , general_type     :: utype()
    , specialized_type :: utype()
    , context          :: term() }).

-type named_argument_constraint() :: #named_argument_constraint{} | #dependent_type_constraint{}.

-record(field_constraint,
    { record_t :: utype()
    , field    :: aeso_syntax:id()
    , field_t  :: utype()
    , kind     :: project | create | update
    , context  :: why_record() }).

%% Constraint checking that 'record_t' has precisely 'fields'.
-record(record_create_constraint,
    { record_t :: utype()
    , fields   :: [aeso_syntax:id()]
    , context  :: why_record() }).

-record(is_contract_constraint,
    { contract_t :: utype(),
      context    :: {contract_literal, aeso_syntax:expr()} |
                    {address_to_contract, aeso_syntax:ann()} |
                    {bytecode_hash, aeso_syntax:ann()} |
                    {var_args, aeso_syntax:ann(), aeso_syntax:expr()},
      force_def = false :: boolean()
    }).

-type field_constraint() :: #field_constraint{} | #record_create_constraint{} | #is_contract_constraint{}.

-type byte_constraint() :: {is_bytes, term(), utype()}
                         | {is_fixed_bytes, term(), utype()}
                         | {add_bytes, aeso_syntax:ann(), concat | split | split_any, utype(), utype(), utype()}.

-type aens_resolve_constraint() :: {aens_resolve_type, utype()}.
-type oracle_type_constraint() :: {oracle_type, aeso_syntax:ann(), utype()}.

-type constraint() :: named_argument_constraint() | field_constraint() | byte_constraint()
                    | aens_resolve_constraint() | oracle_type_constraint().

-record(field_info,
    { ann      :: aeso_syntax:ann()
    , field_t  :: utype()
    , record_t :: utype()
    , kind     :: contract | record }).

-type field_info() :: #field_info{}.

-type access() :: public | private | internal.

-type typedef() :: {[aeso_syntax:tvar()], aeso_syntax:typedef() | {contract_t, [aeso_syntax:field_t()]}}
                 | {builtin, non_neg_integer()}.

-type type() :: aeso_syntax:type().
-type name() :: string().
-type qname() :: [string()].
-type typesig() :: {type_sig, aeso_syntax:ann(), type_constraints(), [aeso_syntax:named_arg_t()], [type()], type()}.

-type namespace_alias() :: none | name().
-type namespace_parts() :: none | {for, [name()]} | {hiding, [name()]}.
-type used_namespaces() :: [{qname(), namespace_alias(), namespace_parts()}].

-type type_constraints() :: none | bytes_concat | bytes_split | address_to_contract | bytecode_hash.

-type variance() :: invariant | covariant | contravariant | bivariant.

-type fun_info()   :: {aeso_syntax:ann(), typesig() | type()}.
-type type_info()  :: {aeso_syntax:ann(), typedef()}.
-type const_info() :: {aeso_syntax:ann(), type()}.
-type var_info()   :: {aeso_syntax:ann(), utype()}.

-type fun_env()   :: [{name(), fun_info()}].
-type type_env()  :: [{name(), type_info()}].
-type const_env() :: [{name(), const_info()}].

-record(scope, { funs   = [] :: fun_env()
               , types  = [] :: type_env()
               , consts = [] :: const_env()
               , access = public :: access()
               , kind   = namespace :: namespace | contract
               , ann    = [{origin, system}] :: aeso_syntax:ann()
               }).

-type scope() :: #scope{}.

-record(env,
    { scopes           = #{ [] => #scope{}} :: #{ qname() => scope() }
    , vars             = []                 :: [{name(), var_info()}]
    , typevars         = unrestricted       :: unrestricted | [name()]
    , fields           = #{}                :: #{ name() => [field_info()] }
    , contract_parents = #{}                :: #{ name() => [name()] }
    , namespace        = []                 :: qname()
    , used_namespaces  = []                 :: used_namespaces()
    , in_pattern       = false              :: boolean()
    , in_guard         = false              :: boolean()
    , stateful         = false              :: boolean()
    , current_const    = none               :: none | aeso_syntax:id()
    , current_function = none               :: none | aeso_syntax:id()
    , what             = top                :: top | namespace | contract | contract_interface
    }).

-type env() :: #env{}.

-type option() :: return_env | dont_unfold | no_code | debug_mode | term().

-endif.

