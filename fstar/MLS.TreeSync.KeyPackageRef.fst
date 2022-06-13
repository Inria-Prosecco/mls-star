module MLS.TreeSync.KeyPackageRef

open Comparse
open MLS.Utils
open MLS.Tree
open MLS.TreeSync.Types
open MLS.NetworkTypes
open MLS.NetworkBinder
open MLS.Crypto
open MLS.Result

val leaf_package_to_kp_ref: #bytes:Type0 -> {|crypto_bytes bytes|} -> leaf_package_t bytes -> result (key_package_ref_nt bytes)
let leaf_package_to_kp_ref #bytes #cb lp =
  kp <-- treesync_to_keypackage lp;
  let kp_bytes: bytes = serialize (key_package_nt bytes) kp in
  make_keypackage_ref kp_bytes

val key_package_ref_to_index: #bytes:Type0 -> {|crypto_bytes bytes|} -> #l:nat -> #n:tree_size l -> treesync bytes l n -> key_package_ref_nt bytes -> result (option (leaf_index n))
let key_package_ref_to_index #bytes #cb #l #n t kp_ref =
  let leaves = get_leaf_list t in
  kp_refs <-- mapM (fun olp ->
    match olp with
    | Some lp -> (
        kp_ref <-- leaf_package_to_kp_ref lp;
        return (Some kp_ref)
    )
    | None -> return None
  ) leaves;
  let opt_res = (find_first (fun x -> x = Some kp_ref) kp_refs) in
  return #(option (leaf_index n)) opt_res
