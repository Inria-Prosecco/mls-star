module MLS.TreeSync.KeyPackageRef

open Comparse
open MLS.Utils
open MLS.Tree
open MLS.TreeSync.Types
open MLS.NetworkTypes
open MLS.NetworkBinder
open MLS.Crypto
open MLS.Result

val compute_key_package_ref: #bytes:Type0 -> {|crypto_bytes bytes|} -> key_package_nt bytes -> result (key_package_ref_nt bytes)
let compute_key_package_ref #bytes #cb kp =
  let kp_bytes: bytes = serialize (key_package_nt bytes) kp in
  make_keypackage_ref kp_bytes

val compute_leaf_node_ref: #bytes:Type0 -> {|crypto_bytes bytes|} -> leaf_package_t bytes -> result (leaf_node_ref_nt bytes)
let compute_leaf_node_ref #bytes #cb lp =
  leaf <-- leaf_package_to_network lp;
  let leaf_bytes: bytes = serialize (leaf_node_nt bytes) leaf in
  make_leafnode_ref leaf_bytes

val leaf_node_ref_to_index: #bytes:Type0 -> {|crypto_bytes bytes|} -> #l:nat -> #n:tree_size l -> treesync bytes l n -> leaf_node_ref_nt bytes -> result (option (leaf_index n))
let leaf_node_ref_to_index #bytes #cb #l #n t ln_ref =
  let leaves = get_leaf_list t in
  ln_refs <-- mapM (fun olp ->
    match olp with
    | Some lp -> (
        kp_ref <-- compute_leaf_node_ref #bytes #cb lp;
        return (Some kp_ref)
    )
    | None -> return None
  ) leaves;
  let opt_res = (find_first (fun x -> x = Some ln_ref) ln_refs) in
  return #(option (leaf_index n)) opt_res
