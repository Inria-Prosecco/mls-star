module MLS.TreeSync.Symbolic.State.KeyPackageManager

open Comparse
open DY.Core
open DY.Lib
open MLS.TreeSync.NetworkTypes
open MLS.Bootstrap.NetworkTypes
open MLS.Symbolic
open MLS.TreeSync.Symbolic.IsWellFormed

(*** KeyPackage manager types & invariants ***)

[@@ with_bytes bytes]
type key_package_manager_value = {
  si_private: state_id;
}

%splice [ps_key_package_manager_value] (gen_parser (`key_package_manager_value))
%splice [ps_key_package_manager_value_is_well_formed] (gen_is_well_formed_lemma (`key_package_manager_value))

instance key_package_manager_types (tkt:treekem_types bytes): map_types (key_package_nt bytes tkt) key_package_manager_value = {
  tag = "MLS.TreeSync.KeyPackageManager";
  ps_key_t = ps_key_package_nt tkt;
  ps_value_t = ps_key_package_manager_value;
}

val key_package_manager_pred: {|crypto_invariants|} -> tkt:treekem_types bytes -> map_predicate (key_package_nt bytes tkt) key_package_manager_value #_
let key_package_manager_pred #ci tkt = {
  pred = (fun tr prin state_id key_package value ->
    is_well_formed _ (is_publishable tr) key_package
  );
  pred_later = (fun tr1 tr2 prin state_id key_package value -> ());
  pred_knowable = (fun tr prin state_id key_package value ->
    assert(is_well_formed _ (is_knowable_by (principal_tag_state_label prin (key_package_manager_types tkt).tag state_id) tr) key_package)
  );
}

val has_key_package_manager_invariant: treekem_types bytes -> {|protocol_invariants|} -> prop
let has_key_package_manager_invariant tkt #invs =
  has_map_session_invariant (key_package_manager_pred tkt)

val key_package_manager_tag_and_invariant: {|crypto_invariants|} -> treekem_types bytes -> dtuple2 string local_bytes_state_predicate
let key_package_manager_tag_and_invariant #ci tkt = (|(key_package_manager_types tkt).tag, local_state_predicate_to_local_bytes_state_predicate (map_session_invariant (key_package_manager_pred tkt))|)

(*** KeyPackage manager API ***)

let initialize_key_package_manager (tkt:treekem_types bytes) = initialize_map (key_package_nt bytes tkt) key_package_manager_value
let add_new_key_package_secret_session (tkt:treekem_types bytes) = add_key_value #(key_package_nt bytes tkt) #key_package_manager_value
let find_key_package_secret_session (tkt:treekem_types bytes) = find_value #(key_package_nt bytes tkt) #key_package_manager_value
