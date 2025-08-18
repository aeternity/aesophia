%%%-------------------------------------------------------------------
%%% @doc Mapping from high-level ops to FATE operations
%%%-------------------------------------------------------------------
-module(aeso_fate_opmap).

-export([op_to_scode/1]).

op_to_scode('+')               -> aeb_fate_ops:add({stack,0}, {stack,0}, {stack,0});
op_to_scode('-')               -> aeb_fate_ops:sub({stack,0}, {stack,0}, {stack,0});
op_to_scode('*')               -> aeb_fate_ops:mul({stack,0}, {stack,0}, {stack,0});
op_to_scode('/')               -> aeb_fate_ops:divide({stack,0}, {stack,0}, {stack,0});
op_to_scode(mod)               -> aeb_fate_ops:modulo({stack,0}, {stack,0}, {stack,0});
op_to_scode('^')               -> aeb_fate_ops:pow({stack,0}, {stack,0}, {stack,0});
op_to_scode('++')              -> aeb_fate_ops:append({stack,0}, {stack,0}, {stack,0});
op_to_scode('::')              -> aeb_fate_ops:cons({stack,0}, {stack,0}, {stack,0});
op_to_scode('<')               -> aeb_fate_ops:lt({stack,0}, {stack,0}, {stack,0});
op_to_scode('>')               -> aeb_fate_ops:gt({stack,0}, {stack,0}, {stack,0});
op_to_scode('=<')              -> aeb_fate_ops:elt({stack,0}, {stack,0}, {stack,0});
op_to_scode('>=')              -> aeb_fate_ops:egt({stack,0}, {stack,0}, {stack,0});
op_to_scode('==')              -> aeb_fate_ops:eq({stack,0}, {stack,0}, {stack,0});
op_to_scode('!=')              -> aeb_fate_ops:neq({stack,0}, {stack,0}, {stack,0});
op_to_scode('!')               -> aeb_fate_ops:not_op({stack,0}, {stack,0});
op_to_scode('bnot')            -> aeb_fate_ops:bin_not({stack,0}, {stack,0});
op_to_scode('band')            -> aeb_fate_ops:bin_and({stack,0}, {stack,0}, {stack,0});
op_to_scode('bor')             -> aeb_fate_ops:bin_or({stack,0}, {stack,0}, {stack,0});
op_to_scode('bxor')            -> aeb_fate_ops:bin_xor({stack,0}, {stack,0}, {stack,0});
op_to_scode('<<')              -> aeb_fate_ops:bin_sl({stack,0}, {stack,0}, {stack,0});
op_to_scode('>>')              -> aeb_fate_ops:bin_sr({stack,0}, {stack,0}, {stack,0});
op_to_scode(map_get)           -> aeb_fate_ops:map_lookup({stack,0}, {stack,0}, {stack,0});
op_to_scode(map_get_d)         -> aeb_fate_ops:map_lookup({stack,0}, {stack,0}, {stack,0}, {stack,0});
op_to_scode(map_set)           -> aeb_fate_ops:map_update({stack,0}, {stack,0}, {stack,0}, {stack,0});
op_to_scode(map_from_list)     -> aeb_fate_ops:map_from_list({stack,0}, {stack,0});
op_to_scode(map_to_list)       -> aeb_fate_ops:map_to_list({stack,0}, {stack,0});
op_to_scode(map_delete)        -> aeb_fate_ops:map_delete({stack,0}, {stack,0}, {stack,0});
op_to_scode(map_member)        -> aeb_fate_ops:map_member({stack,0}, {stack,0}, {stack,0});
op_to_scode(map_size)          -> aeb_fate_ops:map_size_({stack,0}, {stack,0});
op_to_scode(stringinternal_length)    -> aeb_fate_ops:str_length({stack,0}, {stack,0});
op_to_scode(stringinternal_concat)    -> aeb_fate_ops:str_join({stack,0}, {stack,0}, {stack,0});
op_to_scode(stringinternal_to_bytes)  -> aeb_fate_ops:str_to_bytes({stack,0}, {stack,0});
op_to_scode(stringinternal_to_list)   -> aeb_fate_ops:str_to_list({stack,0}, {stack,0});
op_to_scode(stringinternal_from_list) -> aeb_fate_ops:str_from_list({stack,0}, {stack,0});
op_to_scode(stringinternal_to_lower)  -> aeb_fate_ops:str_to_lower({stack,0}, {stack,0});
op_to_scode(stringinternal_to_upper)  -> aeb_fate_ops:str_to_upper({stack,0}, {stack,0});
op_to_scode(char_to_int)       -> aeb_fate_ops:char_to_int({stack,0}, {stack,0});
op_to_scode(char_from_int)     -> aeb_fate_ops:char_from_int({stack,0}, {stack,0});
op_to_scode(bits_set)          -> aeb_fate_ops:bits_set({stack,0}, {stack,0}, {stack,0});
op_to_scode(bits_clear)        -> aeb_fate_ops:bits_clear({stack,0}, {stack,0}, {stack,0});
op_to_scode(bits_test)         -> aeb_fate_ops:bits_test({stack,0}, {stack,0}, {stack,0});
op_to_scode(bits_sum)          -> aeb_fate_ops:bits_sum({stack,0}, {stack,0});
op_to_scode(bits_intersection) -> aeb_fate_ops:bits_and({stack,0}, {stack,0}, {stack,0});
op_to_scode(bits_union)        -> aeb_fate_ops:bits_or({stack,0}, {stack,0}, {stack,0});
op_to_scode(bits_difference)   -> aeb_fate_ops:bits_diff({stack,0}, {stack,0}, {stack,0});
op_to_scode(address_to_str)    -> aeb_fate_ops:addr_to_str({stack,0}, {stack,0});
op_to_scode(address_to_bytes)  -> aeb_fate_ops:addr_to_bytes({stack,0}, {stack,0});
op_to_scode(int_to_str)        -> aeb_fate_ops:int_to_str({stack,0}, {stack,0});
op_to_scode(int_to_bytes)      -> aeb_fate_ops:int_to_bytes({stack,0}, {stack,0}, {stack,0});
op_to_scode(int_mulmod)        -> aeb_fate_ops:mulmod({stack,0}, {stack,0}, {stack,0}, {stack,0});
op_to_scode(contract_to_address)         -> aeb_fate_ops:contract_to_address({stack,0}, {stack,0});
op_to_scode(address_to_contract)         -> aeb_fate_ops:address_to_contract({stack,0}, {stack,0});
op_to_scode(crypto_verify_sig)           -> aeb_fate_ops:verify_sig({stack,0}, {stack,0}, {stack,0}, {stack,0});
op_to_scode(crypto_verify_sig_secp256k1) -> aeb_fate_ops:verify_sig_secp256k1({stack,0}, {stack,0}, {stack,0}, {stack,0});
op_to_scode(crypto_ecverify_secp256k1)   -> aeb_fate_ops:ecverify_secp256k1({stack,0}, {stack,0}, {stack,0}, {stack,0});
op_to_scode(crypto_ecrecover_secp256k1)  -> aeb_fate_ops:ecrecover_secp256k1({stack,0}, {stack,0}, {stack,0});
op_to_scode(crypto_sha3)                 -> aeb_fate_ops:sha3({stack,0}, {stack,0});
op_to_scode(crypto_sha256)               -> aeb_fate_ops:sha256({stack,0}, {stack,0});
op_to_scode(crypto_blake2b)              -> aeb_fate_ops:blake2b({stack,0}, {stack,0});
op_to_scode(crypto_poseidon)             -> aeb_fate_ops:poseidon({stack,0}, {stack,0}, {stack,0});
op_to_scode(stringinternal_sha3)         -> aeb_fate_ops:sha3({stack,0}, {stack,0});
op_to_scode(stringinternal_sha256)       -> aeb_fate_ops:sha256({stack,0}, {stack,0});
op_to_scode(stringinternal_blake2b)      -> aeb_fate_ops:blake2b({stack,0}, {stack,0});
op_to_scode(mcl_bls12_381_g1_neg)        -> aeb_fate_ops:bls12_381_g1_neg({stack,0}, {stack,0});
op_to_scode(mcl_bls12_381_g1_norm)       -> aeb_fate_ops:bls12_381_g1_norm({stack,0}, {stack,0});
op_to_scode(mcl_bls12_381_g1_valid)      -> aeb_fate_ops:bls12_381_g1_valid({stack,0}, {stack,0});
op_to_scode(mcl_bls12_381_g1_is_zero)    -> aeb_fate_ops:bls12_381_g1_is_zero({stack,0}, {stack,0});
op_to_scode(mcl_bls12_381_g1_add)        -> aeb_fate_ops:bls12_381_g1_add({stack,0}, {stack,0}, {stack,0});
op_to_scode(mcl_bls12_381_g1_mul)        -> aeb_fate_ops:bls12_381_g1_mul({stack,0}, {stack,0}, {stack,0});
op_to_scode(mcl_bls12_381_g2_neg)        -> aeb_fate_ops:bls12_381_g2_neg({stack,0}, {stack,0});
op_to_scode(mcl_bls12_381_g2_norm)       -> aeb_fate_ops:bls12_381_g2_norm({stack,0}, {stack,0});
op_to_scode(mcl_bls12_381_g2_valid)      -> aeb_fate_ops:bls12_381_g2_valid({stack,0}, {stack,0});
op_to_scode(mcl_bls12_381_g2_is_zero)    -> aeb_fate_ops:bls12_381_g2_is_zero({stack,0}, {stack,0});
op_to_scode(mcl_bls12_381_g2_add)        -> aeb_fate_ops:bls12_381_g2_add({stack,0}, {stack,0}, {stack,0});
op_to_scode(mcl_bls12_381_g2_mul)        -> aeb_fate_ops:bls12_381_g2_mul({stack,0}, {stack,0}, {stack,0});
op_to_scode(mcl_bls12_381_gt_inv)        -> aeb_fate_ops:bls12_381_gt_inv({stack,0}, {stack,0});
op_to_scode(mcl_bls12_381_gt_add)        -> aeb_fate_ops:bls12_381_gt_add({stack,0}, {stack,0}, {stack,0});
op_to_scode(mcl_bls12_381_gt_mul)        -> aeb_fate_ops:bls12_381_gt_mul({stack,0}, {stack,0}, {stack,0});
op_to_scode(mcl_bls12_381_gt_pow)        -> aeb_fate_ops:bls12_381_gt_pow({stack,0}, {stack,0}, {stack,0});
op_to_scode(mcl_bls12_381_gt_is_one)     -> aeb_fate_ops:bls12_381_gt_is_one({stack,0}, {stack,0});
op_to_scode(mcl_bls12_381_pairing)       -> aeb_fate_ops:bls12_381_pairing({stack,0}, {stack,0}, {stack,0});
op_to_scode(mcl_bls12_381_miller_loop)   -> aeb_fate_ops:bls12_381_miller_loop({stack,0}, {stack,0}, {stack,0});
op_to_scode(mcl_bls12_381_final_exp)     -> aeb_fate_ops:bls12_381_final_exp({stack,0}, {stack,0});
op_to_scode(mcl_bls12_381_int_to_fr)     -> aeb_fate_ops:bls12_381_int_to_fr({stack,0}, {stack,0});
op_to_scode(mcl_bls12_381_int_to_fp)     -> aeb_fate_ops:bls12_381_int_to_fp({stack,0}, {stack,0});
op_to_scode(mcl_bls12_381_fr_to_int)     -> aeb_fate_ops:bls12_381_fr_to_int({stack,0}, {stack,0});
op_to_scode(mcl_bls12_381_fp_to_int)     -> aeb_fate_ops:bls12_381_fp_to_int({stack,0}, {stack,0}).


