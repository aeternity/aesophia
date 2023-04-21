-module(aeso_tc_name_manip).

-export([ name/1
        , qname/1
        , qid/2
        , qcon/2
        , set_qname/2
        ]).

%% TODO: types are duplicated
-type name() :: string().
-type qname() :: [string()].
-type type_id() :: aeso_syntax:id() | aeso_syntax:qid() | aeso_syntax:con() | aeso_syntax:qcon().

-spec qname(type_id()) -> qname().
qname({id,   _, X})  -> [X];
qname({qid,  _, Xs}) -> Xs;
qname({con,  _, X})  -> [X];
qname({qcon, _, Xs}) -> Xs.

-spec name(Named | {typed, _, Named, _}) -> name() when
      Named :: aeso_syntax:id() | aeso_syntax:con().
name({typed, _, X, _}) -> name(X);
name({id, _, X}) -> X;
name({con, _, X}) -> X.

-spec qid(aeso_syntax:ann(), qname()) -> aeso_syntax:id() | aeso_syntax:qid().
qid(Ann, [X]) -> {id, Ann, X};
qid(Ann, Xs)  -> {qid, Ann, Xs}.

-spec qcon(aeso_syntax:ann(), qname()) -> aeso_syntax:con() | aeso_syntax:qcon().
qcon(Ann, [X]) -> {con, Ann, X};
qcon(Ann, Xs)  -> {qcon, Ann, Xs}.

-spec set_qname(qname(), type_id()) -> type_id().
set_qname(Xs, {id,   Ann, _}) -> qid(Ann, Xs);
set_qname(Xs, {qid,  Ann, _}) -> qid(Ann, Xs);
set_qname(Xs, {con,  Ann, _}) -> qcon(Ann, Xs);
set_qname(Xs, {qcon, Ann, _}) -> qcon(Ann, Xs).
