module MLS.TreeSync.ParentHash

open Lib.ByteSequence
open MLS.TreeSync.Types
open MLS.TreeKEM.Types
open MLS.TreeKEM
open MLS.TreeSyncTreeKEMBinder
open MLS.Crypto
open MLS.Tree
open MLS.NetworkTypes
open MLS.Parser
open MLS.Result

#set-options "--ifuel 1 --fuel 1"

noeq type parent_hash_input_nt = {
  public_key: hpke_public_key_nt;
  parent_hash: blbytes ({min=0;max=255});
  original_child_resolution: blseq hpke_public_key_nt ps_hpke_public_key ({min=0; max=(pow2 32)-1});
}

val ps_parent_hash_input: parser_serializer parent_hash_input_nt
let ps_parent_hash_input =
  let open MLS.Parser in
  isomorphism parent_hash_input_nt
    (
      _ <-- ps_hpke_public_key;
      _ <-- ps_bytes _;
      ps_seq _ ps_hpke_public_key
    )
  (fun (|public_key, (|parent_hash, original_child_resolution|)|) -> {
    public_key = public_key;
    parent_hash = parent_hash;
    original_child_resolution = original_child_resolution;
  })
  (fun x -> (|x.public_key, (|x.parent_hash, x.original_child_resolution|)|))

val compute_parent_hash_treekem: #cs:ciphersuite -> #l:nat -> #n:tree_size l -> hpke_public_key_nt -> bytes -> treekem cs l n -> list (hpke_public_key cs) -> result (lbytes (hash_length cs))
let compute_parent_hash_treekem #cs #l #n public_key parent_hash sibling forbidden_public_keys =
  let sibling_resolution = tree_resolution sibling in
  let original_child_resolution = List.Tot.filter (fun pk ->
    //TODO: this should break secret independance?
    not (List.Tot.mem pk forbidden_public_keys)
  ) sibling_resolution in
  let original_child_resolution_nt = List.Tot.map (fun (x:hpke_public_key cs) -> x <: hpke_public_key_nt) original_child_resolution in
  if not (Seq.length parent_hash < 256) then
    internal_failure "compute_parent_hash: parent_hash too long"
  else if not (byte_length ps_hpke_public_key original_child_resolution_nt < pow2 32) then
    internal_failure "compute_parent_hash: original_child_resolution too big"
  else (
    Seq.lemma_list_seq_bij original_child_resolution_nt;
    hash_hash cs (ps_parent_hash_input.serialize ({
      public_key = public_key;
      parent_hash = parent_hash;
      original_child_resolution = Seq.seq_of_list original_child_resolution_nt;
    }))
  )

val get_public_key_from_content: bytes -> result hpke_public_key_nt
let get_public_key_from_content content =
  let open MLS.NetworkBinder in
  content <-- from_option "get_public_key_from_content: Couldn't parse node content"
    ((ps_to_pse ps_node_package_content).parse_exact content);
  return content.public_key

//TODO possible performance optimisation: no need to convert root from treesync to treekem: we only need to convert its content
val compute_parent_hash_from_sibling: #l:nat -> #ls:nat -> #n:tree_size l -> #ns:tree_size ls -> cs:ciphersuite -> content:bytes -> parent_parent_hash:bytes -> nat -> treesync l n -> nat -> treesync ls ns -> result (lbytes (hash_length cs))
let compute_parent_hash_from_sibling #l #ls #n #ns cs content parent_parent_hash nb_left_leaves_root root nb_left_leaves_sibling sibling =
  root_kem <-- treesync_to_treekem_aux cs nb_left_leaves_root root;
  sibling_kem <-- treesync_to_treekem_aux cs nb_left_leaves_sibling sibling;
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
      unmerged_leafs_resolution root_kem root_np.unmerged_leafs
  in
  compute_parent_hash_treekem public_key parent_parent_hash sibling_kem forbidden_keys

val compute_parent_hash_from_dir: #l:nat -> #n:tree_size l -> cs:ciphersuite -> content:bytes -> parent_parent_hash:bytes -> nat -> treesync l n -> direction -> result (lbytes (hash_length cs))
let compute_parent_hash_from_dir #l #n cs content parent_parent_hash nb_left_leaves root dir =
  match root with
  | TNode _ left right ->
    let (_, sibling) = order_subtrees dir (left, right) in
    let nb_left_leaves_sibling =
      if dir = Left then
        nb_left_leaves + (pow2 (l-1))
      else
        nb_left_leaves
    in
    compute_parent_hash_from_sibling cs content parent_parent_hash nb_left_leaves root nb_left_leaves_sibling sibling
  | _ -> internal_failure "compute_parent_hash_from_dir: `root` must be an internal node"

