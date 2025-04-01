module MLS.Crypto.Derived.Symbolic.RefHash

open Comparse
open DY.Core
open DY.Lib
open MLS.NetworkTypes
open MLS.Crypto
open MLS.Crypto.Derived.Lemmas
open MLS.Symbolic
open MLS.Result

val ref_hash_is_knowable_by:
  {|crypto_invariants|} ->
  tr:trace -> l:label ->
  label:mls_ascii_string -> value:bytes ->
  Lemma
  (requires is_knowable_by l tr value)
  (ensures (
    match ref_hash label value with
    | Success res ->
      is_knowable_by l tr res
    | _ -> True
  ))
let ref_hash_is_knowable_by #cinvs tr l label value =
  match ref_hash label value with
  | Success res -> (
    let Success value = mk_mls_bytes value "ref_hash" "value" in
    serialize_wf_lemma _ (is_knowable_by l tr) {label; value}
  )
  | _ -> ()

val make_keypackage_ref_is_knowable_by:
  {|crypto_invariants|} ->
  tr:trace -> l:label ->
  buf:bytes ->
  Lemma
  (requires is_knowable_by l tr buf)
  (ensures (
    match make_keypackage_ref buf with
    | Success res ->
      is_knowable_by l tr res
    | _ -> True
  ))
let make_keypackage_ref_is_knowable_by #cinvs tr l buf =
  normalize_term_spec (String.strlen "MLS 1.0 KeyPackage Reference");
  ref_hash_is_knowable_by tr l "MLS 1.0 KeyPackage Reference" buf

val make_proposal_ref_is_knowable_by:
  {|crypto_invariants|} ->
  tr:trace -> l:label ->
  buf:bytes ->
  Lemma
  (requires is_knowable_by l tr buf)
  (ensures (
    match make_proposal_ref buf with
    | Success res ->
      is_knowable_by l tr res
    | _ -> True
  ))
let make_proposal_ref_is_knowable_by #cinvs tr l buf =
  normalize_term_spec (String.strlen "MLS 1.0 Proposal Reference");
  ref_hash_is_knowable_by tr l "MLS 1.0 Proposal Reference" buf
