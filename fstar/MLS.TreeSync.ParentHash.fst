module MLS.TreeSync.ParentHash

open Comparse
open MLS.TreeSync.Types
open MLS.TreeKEM.Types
open MLS.TreeKEM
open MLS.TreeSyncTreeKEMBinder
open MLS.Crypto
open MLS.Tree
open MLS.NetworkTypes
open MLS.Result

#set-options "--ifuel 1 --fuel 1"

noeq type parent_hash_input_nt (bytes:Type0) {|bytes_like bytes|} = {
  public_key: hpke_public_key_nt bytes;
  parent_hash: mls_bytes bytes;
  original_child_resolution: mls_seq bytes ps_hpke_public_key_nt;
}

%splice [ps_parent_hash_input_nt] (gen_parser (`parent_hash_input_nt))

instance parseable_serializeable_parent_hash_input_nt (bytes:Type0) {|bytes_like bytes|}: parseable_serializeable bytes (parent_hash_input_nt bytes) =
  mk_parseable_serializeable ps_parent_hash_input_nt

val compute_parent_hash_treekem: #bytes:Type0 -> {|crypto_bytes bytes|} -> #l:nat -> #n:tree_size l -> hpke_public_key_nt bytes -> bytes -> treekem bytes l n -> list nat -> result (lbytes bytes (hash_length #bytes))
let compute_parent_hash_treekem #bytes #cb #l #n public_key parent_hash sibling forbidden_leaves =
  let original_child_resolution = original_tree_resolution forbidden_leaves sibling in
  let original_child_resolution_nt = List.Tot.map (fun (x:hpke_public_key bytes) -> x <: hpke_public_key_nt bytes) original_child_resolution in
  if not (length parent_hash < pow2 30) then
    internal_failure "compute_parent_hash: parent_hash too long"
  else if not (bytes_length ps_hpke_public_key_nt original_child_resolution_nt < pow2 30) then
    internal_failure "compute_parent_hash: original_child_resolution too big"
  else (
    Seq.lemma_list_seq_bij original_child_resolution_nt;
    hash_hash (serialize (parent_hash_input_nt bytes) ({
      public_key = public_key;
      parent_hash = parent_hash;
      original_child_resolution = Seq.seq_of_list original_child_resolution_nt;
    }))
  )

val get_public_key_from_content: #bytes:Type0 -> {|bytes_like bytes|} -> bytes -> result (hpke_public_key_nt bytes)
let get_public_key_from_content #bytes #bl content =
  let open MLS.NetworkBinder in
  content <-- from_option "get_public_key_from_content: Couldn't parse node content"
    (parse (treekem_content_nt bytes) content);
  return content.public_key

//TODO possible performance optimisation: no need to convert root from treesync to treekem: we only need to convert its content
val compute_parent_hash_from_sibling: #bytes:Type0 -> {|crypto_bytes bytes|} -> #l:nat -> #ls:nat -> #n:tree_size l -> #ns:tree_size ls -> content:bytes -> parent_parent_hash:bytes -> nat -> treesync bytes l n -> nat -> treesync bytes ls ns -> result (lbytes bytes (hash_length #bytes))
let compute_parent_hash_from_sibling #bytes #cb #l #ls #n #ns content parent_parent_hash nb_left_leaves_root root nb_left_leaves_sibling sibling =
  root_kem <-- treesync_to_treekem_aux nb_left_leaves_root root;
  sibling_kem <-- treesync_to_treekem_aux nb_left_leaves_sibling sibling;
  public_key <-- get_public_key_from_content content;
  root_kem_onp <-- (
    match root_kem with
    | TNode root_onp _ _ ->
      return root_onp
    | _ ->
      internal_failure "compute_parent_hash_from_sibling: `root` must be an internal node"
  );
  let forbidden_keys =
    match root_kem_onp with
    | None -> []
    | Some root_np ->
      (root_np <: key_package bytes).unmerged_leaves
  in
  compute_parent_hash_treekem public_key parent_parent_hash sibling_kem forbidden_keys

val compute_parent_hash_from_dir: #bytes:Type0 -> {|crypto_bytes bytes|} -> #l:nat -> #n:tree_size l -> content:bytes -> parent_parent_hash:bytes -> nat -> treesync bytes l n -> direction -> result (lbytes bytes (hash_length #bytes))
let compute_parent_hash_from_dir #bytes #cb #l #n content parent_parent_hash nb_left_leaves root dir =
  match root with
  | TNode _ left right ->
    let (_, sibling) = order_subtrees dir (left, right) in
    let nb_left_leaves_sibling =
      if dir = Left then
        nb_left_leaves + (pow2 (l-1))
      else
        nb_left_leaves
    in
    compute_parent_hash_from_sibling content parent_parent_hash nb_left_leaves root nb_left_leaves_sibling sibling
  | _ -> internal_failure "compute_parent_hash_from_dir: `root` must be an internal node"
