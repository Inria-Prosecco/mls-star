module MLS.Bootstrap.Symbolic.KeyPackageRef

open DY.Core
open DY.Lib
open Comparse
open MLS.TreeKEM.NetworkTypes
open MLS.Bootstrap.NetworkTypes
open MLS.Bootstrap.KeyPackageRef
open MLS.Crypto
open MLS.Symbolic
open MLS.Crypto.Derived.Symbolic.RefHash
open MLS.Result

val compute_key_package_ref_is_knowable_by:
  {|crypto_invariants|} ->
  tr:trace -> l:label ->
  key_package:key_package_nt bytes tkt ->
  Lemma
  (requires is_well_formed _ (is_knowable_by l tr) key_package)
  (ensures (
    match compute_key_package_ref key_package with
    | Success res ->
      is_knowable_by l tr res
    | _ -> True
  ))
let compute_key_package_ref_is_knowable_by #cinvs tr l key_package =
  serialize_wf_lemma _ (is_knowable_by l tr) key_package;
  make_keypackage_ref_is_knowable_by #cinvs tr l (serialize _ key_package)
