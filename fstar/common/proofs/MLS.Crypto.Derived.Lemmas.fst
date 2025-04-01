module MLS.Crypto.Derived.Lemmas

open Comparse
open MLS.NetworkTypes
open MLS.Crypto
open MLS.Result

#set-options "--fuel 0 --ifuel 0"

val get_mls_label_inj:
  l1:valid_label -> l2:valid_label ->
  Lemma
  (requires get_mls_label l1 == get_mls_label l2)
  (ensures l1 == l2)
let get_mls_label_inj l1 l2 =
  String.concat_injective "MLS 1.0 " "MLS 1.0 " l1 l2


val ref_hash_inj:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  label1:mls_ascii_string -> value1:bytes ->
  label2:mls_ascii_string -> value2:bytes ->
  Pure (bytes & bytes)
  (requires
    Success? (ref_hash label1 value1) /\
    Success? (ref_hash label2 value2) /\
    ref_hash label1 value1 == ref_hash label2 value2
  )
  (ensures fun (b1, b2) ->
    (
      label1 == label2 /\
      value1 == value2
    ) \/
    is_hash_collision b1 b2
  )
let ref_hash_inj #bytes #cb label1 value1 label2 value2 =
  bytes_hasEq #bytes;
  let Success h1 = ref_hash label1 value1 in
  let Success h2 = ref_hash label2 value2 in
  if label1 = label2 && value1 = value2 then
    (empty, empty)
  else (
    let hash_content_1: ref_hash_input_nt bytes = { label = label1; value = value1; } in
    let hash_content_2: ref_hash_input_nt bytes = { label = label2; value = value2; } in
    parse_serialize_inv_lemma #bytes _ hash_content_1;
    parse_serialize_inv_lemma #bytes _ hash_content_2;
    (serialize _ hash_content_1, serialize _ hash_content_2)
  )

val make_proposal_ref_inj:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  proposal1:bytes -> proposal2:bytes ->
  Pure (bytes & bytes)
  (requires
    Success? (make_proposal_ref proposal1) /\
    Success? (make_proposal_ref proposal2) /\
    make_proposal_ref proposal1 == make_proposal_ref proposal2
  )
  (ensures fun (b1, b2) ->
    proposal1 == proposal2 \/
    is_hash_collision b1 b2
  )
let make_proposal_ref_inj #bytes #cb proposal1 proposal2 =
  normalize_term_spec (String.strlen "MLS 1.0 Proposal Reference");
  ref_hash_inj "MLS 1.0 Proposal Reference" proposal1 "MLS 1.0 Proposal Reference" proposal2
