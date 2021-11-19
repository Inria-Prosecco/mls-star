module MLS.TreeSyncTreeKEMBinder

open Lib.ByteSequence
open MLS.Crypto
open MLS.Parser
open MLS.NetworkTypes
open MLS.Tree
open MLS.NetworkBinder
open MLS.TreeSync.Types
open MLS.TreeKEM.Types
open MLS.Result

#set-options "--fuel 1 --ifuel 1"

//TODO I guess this is somewhere in the standard library
val pub_to_secret: pb:pub_bytes -> b:bytes{Seq.length b == Seq.length pb}
let pub_to_secret pb =
  let open Lib.IntTypes in
  Seq.seq_of_list (List.Tot.map (fun x -> u8 (v x)) (Seq.seq_to_list pb))

//TODO this shouldn't exist if the rest of the code (parsers, treekem) was written correctly
val secret_to_pub: b:bytes -> pb:pub_bytes{Seq.length b == Seq.length pb}
let secret_to_pub b =
  let open Lib.IntTypes in
  Seq.seq_of_list (List.Tot.map (fun x -> byte (v x)) (Seq.seq_to_list b))

let encrypted_path_secret_nt_to_tk (cs:ciphersuite) (x:hpke_ciphertext_nt): result (path_secret_ciphertext cs) =
  if not (Seq.length x.kem_output = hpke_kem_output_length cs) then
    internal_failure "encrypted_path_secret_nt_to_tk: kem_output has wrong length"
  else
    return ({
      kem_output = x.kem_output;
      ciphertext = x.ciphertext;
    })

val treesync_to_treekem_node_package: cs:ciphersuite -> nat -> node_package_t -> result (key_package cs)
let treesync_to_treekem_node_package cs nb_left_leaves np =
  content <-- from_option "treesync_to_treekem_node_package: Couldn't parse node content"
    ((ps_to_pse ps_node_package_content).parse_exact (pub_to_secret np.content));
  path_secret_ciphertext <-- mapM (encrypted_path_secret_nt_to_tk cs) (Seq.seq_to_list content.encrypted_path_secret);
  unmerged_leaves <-- mapM (fun (unmerged_leaf:nat) ->
    if not (nb_left_leaves <= unmerged_leaf) then
      error "treesync_to_treekem_node_package: unmerged_leaf index too small"
    else
      return ((unmerged_leaf - nb_left_leaves) <: nat)
  ) np.unmerged_leaves;
  if not (Seq.length content.public_key = hpke_public_key_length cs) then
    error "treesync_to_treekem_node_package: public key has wrong length"
  else (
    return ({
      public_key = content.public_key;
      version = np.version;
      last_group_context = content.last_group_context;
      unmerged_leaves = unmerged_leaves;
      path_secret_from = (np.content_dir);
      path_secret_ciphertext = path_secret_ciphertext;
    })
  )

val treesync_to_treekem_aux: #l:nat -> #n:tree_size l -> cs:ciphersuite -> nat -> treesync l n -> result (treekem cs l n)
let rec treesync_to_treekem_aux #l #n cs nb_left_leaves t =
  match t with
  | TLeaf (_, None) ->
    return (TLeaf None)
  | TLeaf (_, (Some lp)) ->
    lpc <-- from_option "treesync_to_treekem: Couldn't parse leaf content"
      ((ps_to_pse ps_leaf_package_content).parse_exact (pub_to_secret lp.content));
    if Seq.length lpc.public_key = hpke_public_key_length cs then
      return (TLeaf (Some ({public_key = lpc.public_key; version = lp.version} <: member_info cs)))
    else
      error "treesync_to_treekem: public key has wrong length"
  | TSkip _ t' ->
    result <-- treesync_to_treekem_aux cs nb_left_leaves t';
    return (TSkip _ result)
  | TNode (_, onp) left right -> begin
    tk_left <-- treesync_to_treekem_aux cs nb_left_leaves left;
    tk_right <-- treesync_to_treekem_aux cs (nb_left_leaves + pow2 (l-1)) right;
    match onp with
    | None ->
      return (TNode None tk_left tk_right)
    | Some np ->
      kp <-- treesync_to_treekem_node_package cs nb_left_leaves np;
      return (TNode (Some kp) tk_left tk_right)
  end

val treesync_to_treekem: #l:nat -> #n:tree_size l -> cs:ciphersuite -> treesync l n -> result (treekem cs l n)
let treesync_to_treekem #l #n cs t =
  treesync_to_treekem_aux cs 0 t

let encrypted_path_secret_tk_to_nt (#cs:ciphersuite) (x:path_secret_ciphertext cs): result (hpke_ciphertext_nt) =
  if not (Seq.length x.kem_output < pow2 16) then
    internal_failure "encrypted_path_secret_tk_to_nt: kem_output too long"
  else if not (Seq.length x.ciphertext < pow2 16) then
    internal_failure "encrypted_path_secret_tk_to_nt: ciphertext too long"
  else
    return ({
      kem_output = x.kem_output;
      ciphertext = x.ciphertext;
    } <: hpke_ciphertext_nt)

val treekem_to_treesync_node_package: #cs:ciphersuite -> nat -> key_package cs -> result external_node_package_t
let treekem_to_treesync_node_package #cs nb_left_leaves kp =
  ciphertexts <-- mapM encrypted_path_secret_tk_to_nt kp.path_secret_ciphertext;
  if not (byte_length ps_hpke_ciphertext ciphertexts < pow2 16) then
    internal_failure "treekem_to_treesync: ciphertexts too long"
  else if not (Seq.length kp.last_group_context < pow2 64) then
    internal_failure "treekem_to_treesync: last group context too long (internal error)"
  else begin
    Seq.lemma_list_seq_bij ciphertexts;
    let np_content = ps_node_package_content.serialize ({
      public_key = kp.public_key;
      encrypted_path_secret = Seq.seq_of_list ciphertexts;
      last_group_context = kp.last_group_context;
    } <: node_package_content_nt) in
    return (({
      version = kp.version;
      content_dir = kp.path_secret_from;
      unmerged_leaves = List.Tot.map (fun (x:nat) -> (x + nb_left_leaves <: nat)) kp.unmerged_leaves;
      parent_hash = Seq.empty;
      content = secret_to_pub np_content;
    } <: node_package_t) <: external_node_package_t)
  end

// Some remarks about the `new_leaf_package` argument
// This function is used in two cases:
// - By processing an update path coming from the network. In that case, the update path provided a new leaf package to use, which will go in this `new_leaf_package` argument.
//   Why change its public key in that case? Well it doesn't really change, because the public key in `PLeaf` and the public key of `new_leaf_package` will be the same.
//   This is because the `PLeaf` content is equal to `key_package_to_treekem kp` and `new_leaf_package` is equal to `key_package_to_treesync kp` for the same kp
//   The parent hash extension and the signature will be checked when converting the external_pathsync to a pathsync
// - When we generate an updatepath, and convert it to treesync before converting it to an update_path_nt.
//   In that case, `new_leaf_package` need to be equal to our previous leaf package. The HPKE public key will be updated here.
//   The parent hash and signature need to be updated, but this will be done in the external_pathsync -> pathsync conversion.
val treekem_to_treesync_aux: #l:nat -> #n:tree_size l -> #i:leaf_index n -> #cs:ciphersuite -> nat -> leaf_package_t -> pathkem cs l n i -> result (external_pathsync l n i)
let rec treekem_to_treesync_aux #l #n #i #cs nb_left_leaves new_leaf_package pk =
  match pk with
  | PLeaf mi ->
    return (PLeaf ({
      credential = new_leaf_package.credential;
      version = (mi <: member_info cs).version;
      content = secret_to_pub (ps_leaf_package_content.serialize ({
        public_key = (mi <: member_info cs).public_key;
      }));
      extensions = new_leaf_package.extensions;
      signature = new_leaf_package.signature;
    }))
  | PSkip _ pk' ->
    result <-- treekem_to_treesync_aux nb_left_leaves new_leaf_package pk';
    return (PSkip _ result)
  | PNode kp pk_next ->
    let (|dir, _|) = child_index l i in
    let new_left_leaves = (if dir = Left then nb_left_leaves else nb_left_leaves + pow2 (l-1)) in
    next <-- treekem_to_treesync_aux new_left_leaves new_leaf_package pk_next;
    np <-- treekem_to_treesync_node_package nb_left_leaves kp;
    return (PNode np next)

val treekem_to_treesync: #l:nat -> #n:tree_size l -> #i:leaf_index n -> #cs:ciphersuite -> leaf_package_t -> pathkem cs l n i -> result (external_pathsync l n i)
let treekem_to_treesync #l #n #i #cs new_leaf_package pk =
  treekem_to_treesync_aux 0 new_leaf_package pk

