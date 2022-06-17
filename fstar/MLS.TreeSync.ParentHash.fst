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
  public_key: hpke_public_key_nt bytes;
  parent_hash: mls_bytes bytes;
  original_sibling_tree_hash: mls_bytes bytes;
}

%splice [ps_parent_hash_input_nt] (gen_parser (`parent_hash_input_nt))

instance parseable_serializeable_parent_hash_input_nt (bytes:Type0) {|bytes_like bytes|}: parseable_serializeable bytes (parent_hash_input_nt bytes) =
  mk_parseable_serializeable ps_parent_hash_input_nt

val get_public_key_from_content: #bytes:Type0 -> {|bytes_like bytes|} -> bytes -> result (hpke_public_key_nt bytes)
let get_public_key_from_content #bytes #bl content =
  let open MLS.NetworkBinder in
  content <-- from_option "get_public_key_from_content: Couldn't parse node content"
    (parse (treekem_content_nt bytes) content);
  return content.public_key

val mk_full_blank_tree: #bytes:Type0 -> {|bytes_like bytes|} -> l:nat -> treesync bytes l (pow2 l)
let rec mk_full_blank_tree #bytes #bl l =
  if l = 0 then
    TLeaf None
  else
    TNode None (mk_full_blank_tree (l-1)) (mk_full_blank_tree (l-1))

val fully_extend: #bytes:Type0 -> {|bytes_like bytes|} -> #l:nat -> #n:tree_size l -> treesync bytes l n -> treesync bytes l (pow2 l)
let rec fully_extend #bytes #bl #l #n t =
  match t with
  | TLeaf olp ->
    TLeaf olp
  | TSkip _ t' ->
    TNode None (fully_extend t') (mk_full_blank_tree _)
  | TNode onp left right ->
    TNode onp left (fully_extend right)

val un_add: #bytes:Type0 -> {|bytes_like bytes|} -> #l:nat -> #n:tree_size l -> treesync bytes l n -> list nat -> nat -> treesync bytes l n
let rec un_add #bytes #bl #l #n t leaves nb_left_leaves =
  match t with
  | TLeaf olp -> (
    if List.Tot.mem nb_left_leaves leaves then
      TLeaf None
    else
      TLeaf olp
  )
  | TSkip _ t' ->
    TSkip _ (un_add t' leaves nb_left_leaves)
  | TNode onp left right ->
    let new_onp =
      match onp with
      | None -> None
      | Some np -> (
        let new_unmerged_leaves = List.Tot.filter (fun l -> not (List.Tot.mem l leaves)) np.unmerged_leaves in
        Some ({ np with unmerged_leaves = new_unmerged_leaves } <: node_package_t bytes)
      )
    in
    let new_left = un_add left leaves nb_left_leaves in
    let new_right = un_add right leaves (nb_left_leaves + pow2 (l-1)) in
    TNode new_onp new_left new_right

val compute_parent_hash_from_sibling: #bytes:Type0 -> {|crypto_bytes bytes|} -> #ls:nat -> #ns:tree_size ls -> node_package_t bytes -> nat -> treesync bytes ls ns -> result (lbytes bytes (hash_length #bytes))
let compute_parent_hash_from_sibling #bytes #cb #ls #ns root_np nb_left_leaves_sibling sibling =
  public_key <-- get_public_key_from_content root_np.content.content;
  original_sibling_tree_hash <-- tree_hash (fully_extend (un_add sibling root_np.unmerged_leaves nb_left_leaves_sibling));
  if not (length root_np.parent_hash < pow2 30) then
    internal_failure "compute_parent_hash_from_sibling: parent_hash too long"
  else (
    hash_hash (serialize (parent_hash_input_nt bytes) ({
      public_key;
      parent_hash = root_np.parent_hash;
      original_sibling_tree_hash;
    }))
  )

val compute_parent_hash_from_dir: #bytes:Type0 -> {|crypto_bytes bytes|} -> #l:nat -> #n:tree_size l -> nat -> treesync bytes l n -> direction -> result (lbytes bytes (hash_length #bytes))
let compute_parent_hash_from_dir #bytes #cb #l #n nb_left_leaves root dir =
  match root with
  | TNode (Some root_np) left right ->
    let (_, sibling) = order_subtrees dir (left, right) in
    let nb_left_leaves_sibling =
      if dir = Left then
        nb_left_leaves + (pow2 (l-1))
      else
        nb_left_leaves
    in
    compute_parent_hash_from_sibling root_np nb_left_leaves_sibling sibling
  | _ -> internal_failure "compute_parent_hash_from_dir: `root` must be a non-blank internal node"
