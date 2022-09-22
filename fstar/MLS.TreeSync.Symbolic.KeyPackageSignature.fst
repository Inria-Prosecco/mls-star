module MLS.TreeSync.Symbolic.KeyPackageSignature

open Comparse
open MLS.TreeSync.NetworkTypes
open MLS.Symbolic

val key_package_label: string
let key_package_label = "KeyPackageTBS"

val key_package_spred: treekem_types dy_bytes -> sign_pred
let key_package_spred tkt usg time vk kp_tbs_bytes =
  match parse (key_package_tbs_nt dy_bytes tkt) kp_tbs_bytes with
  | None -> False
  | Some kp_tbs -> True //TODO: say something about the init key

val has_key_package_tbs_invariant: treekem_types dy_bytes -> global_usage -> prop
let has_key_package_tbs_invariant tkt gu =
  has_sign_pred gu key_package_label (key_package_spred tkt)
