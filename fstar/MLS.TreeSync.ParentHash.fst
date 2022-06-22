module MLS.TreeSync.ParentHash

open Comparse
open MLS.TreeSync.Types
open MLS.TreeSync.Hash
open MLS.Crypto
open MLS.Tree
open MLS.NetworkTypes
open MLS.Result

#set-options "--ifuel 1 --fuel 1"

noeq type parent_hash_input_nt (bytes:Type0) {|bytes_like bytes|} = {
  encryption_key: hpke_public_key_nt bytes;
  parent_hash: mls_bytes bytes;
  original_sibling_tree_hash: mls_bytes bytes;
}

%splice [ps_parent_hash_input_nt] (gen_parser (`parent_hash_input_nt))

instance parseable_serializeable_parent_hash_input_nt (bytes:Type0) {|bytes_like bytes|}: parseable_serializeable bytes (parent_hash_input_nt bytes) =
  mk_parseable_serializeable ps_parent_hash_input_nt

val get_encryption_key_from_content: #bytes:Type0 -> {|bytes_like bytes|} -> bytes -> result (hpke_public_key_nt bytes)
let get_encryption_key_from_content #bytes #bl content =
  let open MLS.NetworkBinder in
  content <-- from_option "get_encryption_key_from_content: Couldn't parse node content"
    (parse (treekem_content_nt bytes) content);
  return content.encryption_key

val un_add: #bytes:Type0 -> {|bytes_like bytes|} -> #l:nat -> #i:tree_index l -> treesync bytes l i -> list nat -> treesync bytes l i
let rec un_add #bytes #bl #l #i t leaves =
  match t with
  | TLeaf olp -> (
    if List.Tot.mem i leaves then
      TLeaf None
    else
      TLeaf olp
  )
  | TNode onp left right ->
    let new_onp =
      match onp with
      | None -> None
      | Some np -> (
        let new_unmerged_leaves = List.Tot.filter (fun l -> not (List.Tot.mem l leaves)) np.unmerged_leaves in
        Some ({ np with unmerged_leaves = new_unmerged_leaves } <: node_package_t bytes)
      )
    in
    let new_left = un_add left leaves in
    let new_right = un_add right leaves in
    TNode new_onp new_left new_right

val compute_parent_hash: #bytes:Type0 -> {|crypto_bytes bytes|} -> #l:nat -> #i:tree_index l -> node_package_t bytes -> treesync bytes l i -> result (lbytes bytes (hash_length #bytes))
let compute_parent_hash #bytes #cb #l #i root_np sibling =
  encryption_key <-- get_encryption_key_from_content root_np.content.content;
  original_sibling_tree_hash <-- tree_hash (un_add sibling root_np.unmerged_leaves);
  if not (length root_np.parent_hash < pow2 30) then
    internal_failure "compute_parent_hash_from_sibling: parent_hash too long"
  else (
    hash_hash (serialize (parent_hash_input_nt bytes) ({
      encryption_key;
      parent_hash = root_np.parent_hash;
      original_sibling_tree_hash;
    }))
  )

