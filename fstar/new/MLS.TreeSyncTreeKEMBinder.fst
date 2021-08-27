module MLS.TreeSyncTreeKEMBinder

open Lib.ByteSequence
open MLS.Crypto
open MLS.Parser
open MLS.NetworkTypes
open MLS.Tree
open MLS.NetworkBinder
module TS = MLS.TreeSync.Types
module TK = MLS.TreeKEM.Types
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

let encrypted_path_secret_nt_to_tk (cs:ciphersuite) (x:hpke_ciphertext_nt): result (TK.path_secret_ciphertext cs) =
  if not (Seq.length x.hcn_kem_output = hpke_kem_output_length cs) then
    internal_failure "encrypted_path_secret_nt_to_tk: kem_output has wrong length"
  else
    return ({
      TK.kem_output = x.hcn_kem_output;
      TK.ciphertext = x.hcn_ciphertext;
    })

val treesync_to_treekem_node_package: cs:ciphersuite -> nat -> TS.node_package_t -> result (TK.key_package cs)
let treesync_to_treekem_node_package cs nb_left_leaves np =
  content <-- from_option "treesync_to_treekem_node_package: Couldn't parse node content"
    ((ps_to_pse ps_node_package_content).parse_exact (pub_to_secret np.TS.np_content));
  path_secret_ciphertext <-- mapM (encrypted_path_secret_nt_to_tk cs) (Seq.seq_to_list content.npc_encrypted_path_secret);
  unmerged_leaves <-- mapM (fun (unmerged_leaf:nat) ->
    if not (nb_left_leaves <= unmerged_leaf) then
      error "treesync_to_treekem_node_package: unmerged_leaf index too small"
    else
      return ((unmerged_leaf - nb_left_leaves) <: nat)
  ) np.TS.np_unmerged_leafs;
  if not (Seq.length content.npc_public_key = hpke_public_key_length cs) then
    error "treesync_to_treekem_node_package: public key has wrong length"
  else (
    return ({
      TK.kp_public_key = content.npc_public_key;
      TK.kp_version = np.TS.np_version;
      TK.kp_last_group_context = content.npc_last_group_context;
      TK.kp_unmerged_leafs = unmerged_leaves;
      TK.kp_path_secret_from = (np.TS.np_content_dir);
      TK.kp_path_secret_ciphertext = path_secret_ciphertext;
    })
  )

val treesync_to_treekem_aux: #l:nat -> #n:tree_size l -> cs:ciphersuite -> nat -> TS.treesync l n -> result (TK.treekem cs l n)
let rec treesync_to_treekem_aux #l #n cs nb_left_leaves t =
  match t with
  | TLeaf (_, None) ->
    return (TLeaf None)
  | TLeaf (_, (Some lp)) ->
    lpc <-- from_option "treesync_to_treekem: Couldn't parse leaf content"
      ((ps_to_pse ps_leaf_package_content).parse_exact (pub_to_secret lp.TS.lp_content));
    if Seq.length lpc.lpc_public_key = hpke_public_key_length cs then
      return (TLeaf (Some ({TK.mi_public_key = lpc.lpc_public_key; TK.mi_version = lp.TS.lp_version})))
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

val treesync_to_treekem: #l:nat -> #n:tree_size l -> cs:ciphersuite -> TS.treesync l n -> result (TK.treekem cs l n)
let treesync_to_treekem #l #n cs t =
  treesync_to_treekem_aux cs 0 t

let encrypted_path_secret_tk_to_nt (#cs:ciphersuite) (x:TK.path_secret_ciphertext cs): result (hpke_ciphertext_nt) =
  if not (Seq.length x.TK.kem_output < pow2 16) then
    internal_failure "encrypted_path_secret_tk_to_nt: kem_output too long"
  else if not (Seq.length x.TK.ciphertext < pow2 16) then
    internal_failure "encrypted_path_secret_tk_to_nt: ciphertext too long"
  else
    return ({
      hcn_kem_output = x.TK.kem_output;
      hcn_ciphertext = x.TK.ciphertext;
    })

val treekem_to_treesync_node_package: #cs:ciphersuite -> nat -> TK.key_package cs -> result TS.external_node_package_t
let treekem_to_treesync_node_package #cs nb_left_leaves kp =
  ciphertexts <-- mapM encrypted_path_secret_tk_to_nt kp.TK.kp_path_secret_ciphertext;
  if not (byte_length ps_hpke_ciphertext ciphertexts < pow2 16) then
    internal_failure "treekem_to_treesync: ciphertexts too long"
  else if not (Seq.length kp.TK.kp_last_group_context < pow2 64) then
    internal_failure "treekem_to_treesync: last group context too long (internal error)"
  else begin
    Seq.lemma_list_seq_bij ciphertexts;
    let np_content = ps_node_package_content.serialize ({
      npc_public_key = kp.TK.kp_public_key;
      npc_encrypted_path_secret = Seq.seq_of_list ciphertexts;
      npc_last_group_context = kp.TK.kp_last_group_context;
    }) in
    return ({
      TS.np_version = kp.TK.kp_version;
      TS.np_content_dir = kp.TK.kp_path_secret_from;
      TS.np_unmerged_leafs = List.Tot.map (fun (x:nat) -> (x + nb_left_leaves <: nat)) kp.TK.kp_unmerged_leafs;
      TS.np_parent_hash = Seq.empty;
      TS.np_content = secret_to_pub np_content;
    } <: TS.external_node_package_t)
  end

val treekem_to_treesync_aux: #l:nat -> #n:tree_size l -> #i:leaf_index n -> #cs:ciphersuite -> nat -> TS.leaf_package_t -> TK.pathkem cs l n i -> result (TS.external_pathsync l n i)
let rec treekem_to_treesync_aux #l #n #i #cs nb_left_leaves old_leaf_package pk =
  match pk with
  | PLeaf mi ->
    return (PLeaf ({
      TS.lp_credential = old_leaf_package.TS.lp_credential;
      TS.lp_version = mi.TK.mi_version;
      TS.lp_content = secret_to_pub (ps_leaf_package_content.serialize ({
        lpc_public_key = mi.TK.mi_public_key;
      }));
      TS.lp_extensions = old_leaf_package.TS.lp_extensions; //TODO probably the parent hash should change?
      TS.lp_signature = old_leaf_package.TS.lp_signature; //TODO the signature definitely has to change
    }))
  | PSkip _ pk' ->
    result <-- treekem_to_treesync_aux nb_left_leaves old_leaf_package pk';
    return (PSkip _ result)
  | PNode kp pk_next ->
    let (|dir, _|) = child_index l i in
    let new_left_leaves = (if dir = Left then nb_left_leaves else nb_left_leaves + pow2 (l-1)) in
    next <-- treekem_to_treesync_aux new_left_leaves old_leaf_package pk_next;
    np <-- treekem_to_treesync_node_package nb_left_leaves kp;
    return (PNode np next)

val treekem_to_treesync: #l:nat -> #n:tree_size l -> #i:leaf_index n -> #cs:ciphersuite -> TS.leaf_package_t -> TK.pathkem cs l n i -> result (TS.external_pathsync l n i)
let treekem_to_treesync #l #n #i #cs old_leaf_package pk =
  treekem_to_treesync_aux 0 old_leaf_package pk

