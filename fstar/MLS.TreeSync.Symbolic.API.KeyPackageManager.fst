module MLS.TreeSync.Symbolic.API.KeyPackageManager

open Comparse
open MLS.TreeSync.NetworkTypes
open LabeledRuntimeAPI
open MLS.Symbolic
open MLS.Symbolic.MapSession
open MLS.TreeSync.Symbolic.IsWellFormed

(*** KeyPackage manager types & invariants ***)

type key_package_manager_value (bytes:Type0) {|bytes_like bytes|} = {
  [@@@ with_parser #bytes ps_nat]
  si_private: nat;
}

%splice [ps_key_package_manager_value] (gen_parser (`key_package_manager_value))
%splice [ps_key_package_manager_value_is_well_formed] (gen_is_well_formed_lemma (`key_package_manager_value))

val key_package_manager_types: treekem_types dy_bytes -> map_types dy_bytes
let key_package_manager_types tkt = {
  key = key_package_nt dy_bytes tkt;
  ps_key = ps_key_package_nt tkt;
  value = key_package_manager_value dy_bytes;
  ps_value = ps_key_package_manager_value;
}

val key_package_manager_pred: tkt:treekem_types dy_bytes -> map_predicate (key_package_manager_types tkt)
let key_package_manager_pred tkt = {
  pred = (fun gu time (key_package:(key_package_manager_types tkt).key) value ->
    is_well_formed _ (is_publishable gu time) key_package
  );
  pred_later = (fun gu time0 time1 key_package value -> ());
  pred_is_msg = (fun gu time key_package value -> ());
}

val key_package_manager_label: string
let key_package_manager_label = "MLS.TreeSync.KeyPackageManager"

val has_key_package_manager_invariant: treekem_types dy_bytes -> preds -> prop
let has_key_package_manager_invariant tkt pr =
  has_map_session_invariant (key_package_manager_types tkt) (key_package_manager_pred tkt) key_package_manager_label pr

(*** KeyPackage manager API ***)

let initialize_key_package_manager (tkt:treekem_types dy_bytes) = initialize_map (key_package_manager_types tkt) (key_package_manager_pred tkt) key_package_manager_label
let add_new_key_package_secret_session (tkt:treekem_types dy_bytes) = add_key_value (key_package_manager_types tkt) (key_package_manager_pred tkt) key_package_manager_label
let find_key_package_secret_session (tkt:treekem_types dy_bytes) = find_value (key_package_manager_types tkt) (key_package_manager_pred tkt) key_package_manager_label
