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
  phin_public_key: hpke_public_key_nt;
  phin_parent_hash: blbytes ({min=0;max=255});
  phin_original_child_resolution: blseq hpke_public_key_nt ps_hpke_public_key ({min=0; max=(pow2 32)-1});
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
    phin_public_key = public_key;
    phin_parent_hash = parent_hash;
    phin_original_child_resolution = original_child_resolution;
  })
  (fun x -> (|x.phin_public_key, (|x.phin_parent_hash, x.phin_original_child_resolution|)|))

val compute_parent_hash_treekem: #cs:ciphersuite -> #l:nat -> #n:tree_size l -> hpke_public_key cs -> bytes -> treekem cs l n -> list (hpke_public_key cs) -> result (lbytes (hash_length cs))
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
      phin_public_key = public_key;
      phin_parent_hash = parent_hash;
      phin_original_child_resolution = Seq.seq_of_list original_child_resolution_nt;
    }))
  )

//TODO possible performance optimisation: no need to convert root from treesync to treekem: we only need to convert its content
val compute_parent_hash_from_sibling: #l:nat -> #ls:nat -> #n:tree_size l -> #ns:tree_size ls -> cs:ciphersuite -> hpke_public_key cs -> bytes -> nat -> treesync l n -> nat -> treesync ls ns -> result (lbytes (hash_length cs))
let compute_parent_hash_from_sibling #l #ls #n #ns cs public_key parent_parent_hash nb_left_leaves_root root nb_left_leaves_sibling sibling =
  root_kem <-- treesync_to_treekem_aux cs nb_left_leaves_root root;
  sibling_kem <-- treesync_to_treekem_aux cs nb_left_leaves_sibling sibling;
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
      unmerged_leafs_resolution root_kem root_np.kp_unmerged_leafs
  in
  compute_parent_hash_treekem public_key parent_parent_hash sibling_kem forbidden_keys

val compute_parent_hash_from_dir: #l:nat -> #n:tree_size l -> cs:ciphersuite -> hpke_public_key cs -> bytes -> nat -> treesync l n -> direction -> result (lbytes (hash_length cs))
let compute_parent_hash_from_dir #l #n cs public_key parent_parent_hash nb_left_leaves root dir =
  match root with
  | TNode _ left right ->
    let (_, sibling) = order_subtrees dir (left, right) in
    let nb_left_leaves_sibling =
      if dir = Left then
        nb_left_leaves + (pow2 (l-1))
      else
        nb_left_leaves
    in
    compute_parent_hash_from_sibling cs public_key parent_parent_hash nb_left_leaves root nb_left_leaves_sibling sibling
  | _ -> internal_failure "compute_parent_hash_from_dir: `root` must be an internal node"


//TODO: this function has bad complexity (because some subtrees are converted a lot of time)
//Do we care?
val external_pathsync_to_pathsync_aux: #l:nat -> #n:tree_size l -> #i:leaf_index n -> cs:ciphersuite -> bytes -> nat -> treesync l n -> external_pathsync l n i -> result (pathsync l n i)
let rec external_pathsync_to_pathsync_aux #l #n #i cs parent_parent_hash nb_left_leaves t p =
  match t, p with
  | _, PLeaf lp ->
    //TODO check that the parent hash in lp is correct
    return (PLeaf (Some lp))
  | TSkip _ t', PSkip _ p' ->
    result <-- external_pathsync_to_pathsync_aux cs parent_parent_hash nb_left_leaves t' p';
    return (PSkip _ result)
  | TNode _ left right, PNode np p_next ->
    let (|dir, next_i|) = child_index l i in
    let (child, sibling) = order_subtrees dir (left, right) in
    let child_nb_left_leaves = if dir = Left then nb_left_leaves else nb_left_leaves + (pow2 (l-1)) in
    public_key <-- (
      kem_node_package <-- treesync_to_treekem_node_package cs nb_left_leaves np;
      return kem_node_package.kp_public_key
    );
    parent_hash <-- compute_parent_hash_from_dir cs public_key parent_parent_hash nb_left_leaves t dir;
    result_p_next <-- external_pathsync_to_pathsync_aux cs parent_hash child_nb_left_leaves child p_next;
    return (PNode (Some ({np with np_parent_hash = parent_parent_hash;})) result_p_next)

val external_pathsync_to_pathsync: #l:nat -> #n:tree_size l -> #i:leaf_index n -> cs:ciphersuite -> treesync l n -> external_pathsync l n i -> result (pathsync l n i)
let external_pathsync_to_pathsync #l #n #i cs t p =
  external_pathsync_to_pathsync_aux cs bytes_empty 0 t p
