module MLS.TreeSync.Symbolic.AuthServiceCache

open Comparse
open MLS.NetworkTypes
open MLS.TreeSync.NetworkTypes
open ComparseGlue
open GlobalRuntimeLib
open LabeledRuntimeAPI
open MLS.Symbolic
open MLS.Symbolic.MapSession

#set-options "--fuel 0 --ifuel 0"

(*** AS cache types & invariants ***)

type as_cache_key (bytes:Type0) {|bytes_like bytes|} = {
  verification_key: signature_public_key_nt bytes;
  credential: credential_nt bytes;
}

%splice [ps_as_cache_key] (gen_parser (`as_cache_key))
%splice [ps_as_cache_key_is_well_formed] (gen_is_well_formed_lemma (`as_cache_key))

type as_cache_value (bytes:Type0) {|bytes_like bytes|} = {
  who: principal;
  [@@@ with_parser #bytes ps_string]
  usg: string;
  time: timestamp;
}

%splice [ps_as_cache_value] (gen_parser (`as_cache_value))
%splice [ps_as_cache_value_is_well_formed] (gen_is_well_formed_lemma (`as_cache_value))

val as_cache_types: map_types dy_bytes
let as_cache_types = {
  key = as_cache_key dy_bytes;
  ps_key = ps_as_cache_key;
  value = as_cache_value dy_bytes;
  ps_value = ps_as_cache_value;
}

val as_cache_pred: map_predicate as_cache_types
let as_cache_pred = {
  pred = (fun gu time (key:as_cache_types.key) value ->
    value.time <$ time /\
    is_verification_key gu value.usg (readers [(p_id value.who)]) value.time key.verification_key /\
    is_well_formed_whole (ps_prefix_to_ps_whole ps_credential_nt) (is_publishable gu value.time) key.credential
  );
  pred_later = (fun gu time0 time1 key value -> ());
  pred_is_msg = (fun gu time key value ->
    assert(is_well_formed_whole (ps_prefix_to_ps_whole ps_credential_nt) (is_publishable gu time) key.credential)
  );
}

val as_cache_label: string
let as_cache_label = "MLS.TreeSync.AuthServiceCache"

val has_as_cache_invariant: preds -> prop
let has_as_cache_invariant pr =
  has_map_session_invariant as_cache_types as_cache_pred as_cache_label pr

(*** AS cache API ***)

let initialize_as_cache = initialize_map as_cache_types as_cache_pred as_cache_label
let add_verified_credential = add_key_value as_cache_types as_cache_pred as_cache_label
let find_verified_credential = find_value as_cache_types as_cache_pred as_cache_label
