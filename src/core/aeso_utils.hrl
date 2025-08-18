-define(IS_CONTRACT_HEAD(X),
        (X =:= contract_main orelse
         X =:= contract_interface orelse
         X =:= contract_child
        )
       ).
