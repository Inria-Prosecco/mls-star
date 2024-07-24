module MLS.TreeSync.Symbolic.AuthServiceCache

open Comparse
open DY.Core
open DY.Lib
open MLS.NetworkTypes
open MLS.TreeSync.NetworkTypes
open MLS.Symbolic

#set-options "--fuel 0 --ifuel 0"

(*** AS cache types & invariants ***)

[@@ with_bytes dy_bytes]
type as_cache_key = {
  verification_key: signature_public_key_nt bytes;
  credential: credential_nt bytes;
}

%splice [ps_as_cache_key] (gen_parser (`as_cache_key))
%splice [ps_as_cache_key_is_well_formed] (gen_is_well_formed_lemma (`as_cache_key))

[@@ with_bytes dy_bytes]
type as_cache_value = {
  who: principal;
  [@@@ with_parser #bytes ps_string]
  usg: string;
  time: nat;
}

%splice [ps_as_cache_value] (gen_parser (`as_cache_value))
%splice [ps_as_cache_value_is_well_formed] (gen_is_well_formed_lemma (`as_cache_value))

instance as_cache_types: map_types as_cache_key as_cache_value = {
  tag = "MLS.TreeSync.AuthServiceCache";
  ps_key_t = ps_as_cache_key;
  ps_value_t = ps_as_cache_value;
}

val as_cache_pred: {|crypto_invariants|} -> map_predicate as_cache_key as_cache_value #_
let as_cache_pred #ci = {
  pred = (fun tr prin state_id key value ->
    value.time <= DY.Core.Trace.Type.length tr /\
    is_publishable (prefix tr value.time) key.verification_key /\
    get_signkey_label key.verification_key == principal_label value.who /\
    get_signkey_usage key.verification_key == SigKey value.usg empty /\
    is_well_formed_whole (ps_prefix_to_ps_whole ps_credential_nt) (is_publishable (prefix tr value.time)) key.credential
  );
  pred_later = (fun tr1 tr2 prin state_id key value -> ());
  pred_knowable = (fun tr prin state_id key value ->
    assert(is_well_formed_whole (ps_prefix_to_ps_whole ps_credential_nt) (is_knowable_by (principal_state_label prin state_id) tr) key.credential)
  );
}

val has_as_cache_invariant: protocol_invariants -> prop
let has_as_cache_invariant invs =
  has_map_session_invariant invs as_cache_pred

val as_cache_tag_and_invariant: {|crypto_invariants|} -> string & local_bytes_state_predicate
let as_cache_tag_and_invariant #ci = (as_cache_types.tag, local_state_predicate_to_local_bytes_state_predicate (map_session_invariant as_cache_pred))

(*** AS cache API ***)

let initialize_as_cache = initialize_map as_cache_key as_cache_value
let add_verified_credential = add_key_value #as_cache_key #as_cache_value
let find_verified_credential = find_value #as_cache_key #as_cache_value
