module MLS.TreeSync.KeyPackageRef

open MLS.Utils
open MLS.Tree
open MLS.TreeSync.Types
open MLS.NetworkTypes
open MLS.NetworkBinder
open MLS.Crypto
open MLS.Parser
open MLS.Result

val leaf_package_to_kp_ref: cs:ciphersuite -> leaf_package_t -> result (key_package_ref_nt)
let leaf_package_to_kp_ref cs lp =
  kp <-- treesync_to_keypackage cs lp;
  let kp_bytes = ps_key_package.serialize kp in
  make_hash_ref cs kp_bytes

val key_package_ref_to_index: #l:nat -> #n:tree_size l -> ciphersuite -> treesync l n -> key_package_ref_nt -> result (option (leaf_index n))
let key_package_ref_to_index #l #n cs t kp_ref =
  let leaves = get_leaf_list t in
  kp_refs <-- mapM (fun (_, olp) ->
    match olp with
    | Some lp -> (
        kp_ref <-- leaf_package_to_kp_ref cs lp;
        return (Some kp_ref)
    )
    | None -> return None
  ) leaves;
  let opt_res = (find_first (fun x -> x = Some kp_ref) kp_refs) in
  return #(option (leaf_index n)) opt_res
