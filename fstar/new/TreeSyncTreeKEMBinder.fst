module TreeSyncTreeKEMBinder

open Lib.ByteSequence
open Crypto
open NetworkTypes
open Parser
open Tree
module TS = TreeSync
module TK = TreeKEM
open Lib.Result

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
    fail "encrypted_path_secret_nt_to_tk: kem_output has wrong length"
  else
    return ({
      TK.kem_output = x.hcn_kem_output;
      TK.ciphertext = x.hcn_ciphertext;
    })

noeq type leaf_package_content_nt = {
  lpc_public_key: hpke_public_key_nt;
}

val ps_leaf_package_content: parser_serializer leaf_package_content_nt
let ps_leaf_package_content =
  isomorphism leaf_package_content_nt
    ps_hpke_public_key
    (fun public_key -> ({lpc_public_key = public_key}))
    (fun x -> x.lpc_public_key)

noeq type node_package_content_nt = {
  npc_public_key: hpke_public_key_nt;
  npc_encrypted_path_secret: blseq hpke_ciphertext_nt ps_hpke_ciphertext ({min=0; max=(pow2 32)-1});
  npc_last_group_context: blbytes ({min=0; max=(pow2 64) - 1});
}

val ps_node_package_content: parser_serializer node_package_content_nt
let ps_node_package_content =
  let open Parser in
  isomorphism node_package_content_nt
    (
      _ <-- ps_hpke_public_key;
      _ <-- ps_seq _ ps_hpke_ciphertext;
      ps_bytes _
    )
    (fun (|public_key, (|encrypted_path_secret, last_group_context|)|) -> ({npc_public_key = public_key; npc_encrypted_path_secret = encrypted_path_secret; npc_last_group_context = last_group_context;}))
    (fun x -> (|x.npc_public_key, (|x.npc_encrypted_path_secret, x.npc_last_group_context|)|))

val treesync_to_treekem: #l:nat -> #n:tree_size l -> cs:ciphersuite -> TS.treesync l n -> result (TK.treekem cs l n)
let rec treesync_to_treekem #l #n cs t =
  match t with
  | TLeaf (_, None) ->
    return (TLeaf None)
  | TLeaf (_, (Some lp)) ->
    lpc <-- from_option "treesync_to_treekem: Couldn't parse leaf content"
      ((ps_to_pse ps_leaf_package_content).parse_exact (pub_to_secret lp.TS.lp_content));
    if Seq.length lpc.lpc_public_key = hpke_public_key_length cs then
      return (TLeaf (Some ({TK.mi_public_key = lpc.lpc_public_key; TK.mi_version = lp.TS.lp_version})))
    else
      fail "treesync_to_treekem: public key has wrong length"
  | TSkip _ t' ->
    result <-- treesync_to_treekem cs t';
    return (TSkip _ result)
  | TNode (_, onp) left right -> begin
    tk_left <-- treesync_to_treekem cs left;
    tk_right <-- treesync_to_treekem cs right;
    match onp with
    | None ->
      return (TNode None tk_left tk_right)
    | Some np ->
      content <-- from_option "treesync_to_treekem: Couldn't parse node content"
        ((ps_to_pse ps_node_package_content).parse_exact (pub_to_secret np.TS.np_content));
      path_secret_ciphertext <-- mapM (encrypted_path_secret_nt_to_tk cs) (Seq.seq_to_list content.npc_encrypted_path_secret);
      if not (Seq.length content.npc_public_key = hpke_public_key_length cs) then
        fail ""
      else (
        let kp: TK.key_package cs = {
          TK.kp_public_key = content.npc_public_key;
          TK.kp_version = np.TS.np_version;
          TK.kp_last_group_context = content.npc_last_group_context;
          TK.kp_unmerged_leafs = np.TS.np_unmerged_leafs;
          TK.kp_path_secret_from = (np.TS.np_content_dir);
          TK.kp_path_secret_ciphertext = path_secret_ciphertext;
        } in
        return (TNode (Some kp) tk_left tk_right)
      )
  end

let encrypted_path_secret_tk_to_nt (#cs:ciphersuite) (x:TK.path_secret_ciphertext cs): result (hpke_ciphertext_nt) =
  if not (Seq.length x.TK.kem_output < pow2 16) then
    fail "encrypted_path_secret_tk_to_nt: kem_output too long"
  else if not (Seq.length x.TK.ciphertext < pow2 16) then
    fail "encrypted_path_secret_tk_to_nt: ciphertext too long"
  else
    return ({
      hcn_kem_output = x.TK.kem_output;
      hcn_ciphertext = x.TK.ciphertext;
    })


val treekem_to_treesync: #l:nat -> #n:tree_size l -> #i:leaf_index n -> #cs:ciphersuite -> TS.leaf_package_t -> TK.pathkem cs l n i -> result (TS.pathsync l n i)
let rec treekem_to_treesync #l #cs old_leaf_package p =
  match p with
  | PLeaf mi ->
    return (PLeaf (Some ({
      TS.lp_credential = old_leaf_package.TS.lp_credential;
      TS.lp_version = mi.TK.mi_version;
      TS.lp_content = secret_to_pub (ps_leaf_package_content.serialize ({
        lpc_public_key = mi.TK.mi_public_key;
      }));
      TS.lp_extensions = old_leaf_package.TS.lp_extensions; //TODO probably the parent hash should change?
      TS.lp_signature = old_leaf_package.TS.lp_signature; //TODO the signature definitely has to change
    })))
  | PSkip _ p' ->
    result <-- treekem_to_treesync old_leaf_package p';
    return (PSkip _ result)
  | PNode kp p_next ->
    next <-- treekem_to_treesync old_leaf_package p_next;
    ciphertexts <-- mapM encrypted_path_secret_tk_to_nt kp.TK.kp_path_secret_ciphertext;
    if not (byte_length ps_hpke_ciphertext ciphertexts < pow2 16) then
      fail "treekem_to_treesync: ciphertexts too long"
    else if not (Seq.length kp.TK.kp_last_group_context < pow2 64) then
      fail "treekem_to_treesync: last group context too long (internal error)"
    else begin
      Seq.lemma_list_seq_bij ciphertexts;
      let np_content = ps_node_package_content.serialize ({
        npc_public_key = kp.TK.kp_public_key;
        npc_encrypted_path_secret = Seq.seq_of_list ciphertexts;
        npc_last_group_context = kp.TK.kp_last_group_context;
      }) in
      let np = ({
        TS.np_version = kp.TK.kp_version;
        TS.np_content_dir = kp.TK.kp_path_secret_from;
        TS.np_unmerged_leafs = kp.TK.kp_unmerged_leafs;
        TS.np_parent_hash = bytes_empty; //The parent hash needs to be recomputed
        TS.np_content = secret_to_pub np_content;
      }) in
      return (PNode (Some np) next)
    end

(*** NetworkTreeSyncBinder ***)
//TODO move this in an other file

val key_package_to_treesync: key_package_nt -> result TS.leaf_package_t
let key_package_to_treesync kp =
  match kp.kpn_credential with
  | C_basic cred ->
    return ({
      TS.lp_credential = {
        TS.cred_version = 0;
        TS.cred_identity = cred.bcn_identity;
        TS.cred_signature_key = cred.bcn_signature_key;
      };
      TS.lp_version = 0;
      TS.lp_content = ps_leaf_package_content.serialize ({lpc_public_key = kp.kpn_public_key});
      TS.lp_extensions = (ps_seq _ ps_extension).serialize (kp.kpn_extensions);
      TS.lp_signature = kp.kpn_signature;
    })
  | _ -> fail "key_package_to_treesync: credential type not supported"

val treesync_to_keypackage: ciphersuite -> TS.leaf_package_t -> result key_package_nt
let treesync_to_keypackage cs lp =
  if not (Seq.length lp.TS.lp_credential.TS.cred_identity < pow2 16) then
    fail "treesync_to_keypackage: cred_identity too long"
  else if not (Seq.length lp.TS.lp_credential.TS.cred_signature_key < pow2 16) then
    fail "treesync_to_keypackage: cred_signature_key too long"
  else if not (Seq.length lp.TS.lp_signature < pow2 16) then
    fail "treesync_to_keypackage: signature too long"
  else (
    leaf_content <-- from_option "treesync_to_keypackage: can't parse leaf content" ((ps_to_pse ps_leaf_package_content).parse_exact lp.TS.lp_content);
    extensions <-- from_option "treesync_to_keypackage: can't parse extensions" ((ps_to_pse (ps_seq _ ps_extension)).parse_exact lp.TS.lp_extensions);
    cipher_suite <-- ciphersuite_to_nt cs;
    return ({
      kpn_version = PV_mls10;
      kpn_cipher_suite = cipher_suite;
      kpn_public_key = leaf_content.lpc_public_key;
      kpn_credential = C_basic ({
        bcn_identity = lp.TS.lp_credential.TS.cred_identity;
        bcn_signature_scheme = SA_ed25519; //TODO
        bcn_signature_key = lp.TS.lp_credential.TS.cred_signature_key;
      });
      kpn_extensions = extensions;
      kpn_signature = lp.TS.lp_signature;
    })
  )

val treesync_to_parent_node: TS.node_package_t -> result parent_node_nt
let treesync_to_parent_node np =
  unmerged_leaves <-- mapM (fun (x:nat) -> if x < pow2 32 then return (Lib.IntTypes.u32 x) else fail "") np.TS.np_unmerged_leafs;
  if not (Seq.length np.TS.np_parent_hash < 256) then
    fail "treesync_to_parent_node: parent_hash too long"
  else if not ((byte_length ps_u32 unmerged_leaves) < pow2 32) then
    fail "treesync_to_parent_node: unmerged_leaves too long"
  else (
    Seq.lemma_list_seq_bij unmerged_leaves;
    node_content <-- from_option "treesync_to_parent_node: can't parse np_content" ((ps_to_pse ps_node_package_content).parse_exact np.TS.np_content);
    return ({
      pnn_public_key = node_content.npc_public_key;
      pnn_parent_hash = np.TS.np_parent_hash;
      pnn_unmerged_leaves = Seq.seq_of_list unmerged_leaves;
    })
  )

(*** ratchet_tree extension (11.3) ***)

val dumb_credential: TS.credential_t
let dumb_credential = {
  TS.cred_version = 0;
  TS.cred_identity = Seq.empty;
  TS.cred_signature_key = Seq.empty;
}

val ratchet_tree_l_n: nodes:ratchet_tree_nt -> result (l:nat & n:tree_size l{Seq.length nodes == n+n-1})
let ratchet_tree_l_n nodes =
  let n_nodes = Seq.length nodes in
  if n_nodes%2 = 0 then
    fail "ratchet_tree_l_n: length must be odd"
  else
    let n = (n_nodes+1)/2 in
    let l = (TreeMath.Internal.log2 n) + 1 in
    return (|l, n|)

val ratchet_tree_to_treesync: l:nat -> n:tree_size l -> nodes:Seq.seq (option_nt node_nt){Seq.length nodes = (n+n-1)} -> result (TS.treesync l n)
let rec ratchet_tree_to_treesync l n nodes =
  if l = 0 then (
    assert (Seq.length nodes == 1);
    match (Seq.index nodes 0) with
    | Some_nt (N_leaf kp) ->
      kp <-- key_package_to_treesync kp;
      return (TLeaf (dumb_credential, Some kp))
    | Some_nt _ -> fail "ratchet_tree_to_treesync_aux: node must be a leaf!"
    | None_nt ->
      return (TLeaf (dumb_credential, None))
    | _ -> fail "ratchet_tree_to_treesync_aux: option is invalid"
  ) else if n <= pow2 (l-1) then (
    res <-- ratchet_tree_to_treesync (l-1) n nodes;
    return (TSkip _ res)
  ) else (
    let left_nodes = Seq.slice nodes 0 ((pow2 l) - 1) in
    let my_node = Seq.index nodes ((pow2 l) - 1) in
    let right_nodes = Seq.slice nodes (pow2 l) (n+n-1) in
    left_res <-- ratchet_tree_to_treesync (l-1) (pow2 (l-1)) left_nodes;
    right_res <-- ratchet_tree_to_treesync (l-1) (n-pow2 (l-1)) right_nodes;
    match my_node with
    | Some_nt (N_parent pn) ->
      let np = {
        TS.np_version = 0;
        TS.np_content_dir = Left; //We don't care I guess
        TS.np_unmerged_leafs = List.Tot.map (fun x -> let open Lib.IntTypes in (v x <: nat)) (Seq.seq_to_list pn.pnn_unmerged_leaves);
        TS.np_parent_hash = pn.pnn_parent_hash;
        TS.np_content = ps_node_package_content.serialize ({
          npc_public_key = pn.pnn_public_key;
          npc_encrypted_path_secret = Seq.empty;
          npc_last_group_context = bytes_empty;
        });
      } in
      return (TNode (dumb_credential, Some np) left_res right_res)
    | Some_nt _ -> fail "ratchet_tree_to_treesync_aux: node must be a parent!"
    | None_nt ->
      return (TNode (dumb_credential, None) left_res right_res)
    | _ -> fail "ratchet_tree_to_treesync_aux: option is invalid"
  )
