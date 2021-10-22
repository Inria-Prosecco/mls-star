module MLS.NetworkBinder

open Lib.ByteSequence
open MLS.NetworkTypes
open MLS.Crypto
open MLS.Parser
open MLS.Result
open MLS.Tree
module TS = MLS.TreeSync.Types
module TK = MLS.TreeKEM.Types

val network_to_option: #a:Type -> option_nt a -> result (option a)
let network_to_option #a opt =
  match opt with
  | None_nt -> return None
  | Some_nt x -> return (Some x)
  | _ -> error "network_to_option: not a valid option"

val option_to_network: #a:Type -> option a -> option_nt a
let option_to_network #a opt =
  match opt with
  | None -> None_nt
  | Some x -> Some_nt x


noeq type leaf_package_content_nt = {
  public_key: hpke_public_key_nt;
}

val ps_leaf_package_content: parser_serializer leaf_package_content_nt
let ps_leaf_package_content =
  isomorphism leaf_package_content_nt
    ps_hpke_public_key
    (fun public_key -> ({public_key = public_key}))
    (fun x -> x.public_key)

noeq type node_package_content_nt = {
  public_key: hpke_public_key_nt;
  encrypted_path_secret: blseq hpke_ciphertext_nt ps_hpke_ciphertext ({min=0; max=(pow2 32)-1});
  last_group_context: blbytes ({min=0; max=(pow2 64) - 1});
}

val ps_node_package_content: parser_serializer node_package_content_nt
let ps_node_package_content =
  let open MLS.Parser in
  isomorphism node_package_content_nt
    (
      _ <-- ps_hpke_public_key;
      _ <-- ps_seq _ ps_hpke_ciphertext;
      ps_bytes _
    )
    (fun (|public_key, (|encrypted_path_secret, last_group_context|)|) -> ({public_key = public_key; encrypted_path_secret = encrypted_path_secret; last_group_context = last_group_context;}))
    (fun x -> (|x.public_key, (|x.encrypted_path_secret, x.last_group_context|)|))


(*** NetworkTreeSyncBinder ***)

val key_package_to_treesync: key_package_nt -> result TS.leaf_package_t
let key_package_to_treesync kp =
  match kp.credential with
  | C_basic cred ->
    return ({
      TS.credential = {
        TS.version = 0;
        TS.identity = cred.identity;
        TS.signature_key = cred.signature_key;
      };
      TS.version = 0;
      TS.content = ps_leaf_package_content.serialize ({public_key = kp.public_key});
      TS.extensions = (ps_seq _ ps_extension).serialize (kp.extensions);
      TS.signature = kp.signature;
    })
  | _ -> error "key_package_to_treesync: credential type not supported"

val treesync_to_keypackage: ciphersuite -> TS.leaf_package_t -> result key_package_nt
let treesync_to_keypackage cs lp =
  if not (Seq.length lp.TS.credential.TS.identity < pow2 16) then
    error "treesync_to_keypackage: identity too long"
  else if not (Seq.length lp.TS.credential.TS.signature_key < pow2 16) then
    error "treesync_to_keypackage: signature_key too long"
  else if not (Seq.length lp.TS.signature < pow2 16) then
    error "treesync_to_keypackage: signature too long"
  else (
    leaf_content <-- from_option "treesync_to_keypackage: can't parse leaf content" ((ps_to_pse ps_leaf_package_content).parse_exact lp.TS.content);
    extensions <-- from_option "treesync_to_keypackage: can't parse extensions" ((ps_to_pse (ps_seq _ ps_extension)).parse_exact lp.TS.extensions);
    cipher_suite <-- ciphersuite_to_nt cs;
    return ({
      version = PV_mls10;
      cipher_suite = cipher_suite;
      public_key = leaf_content.public_key;
      credential = C_basic ({
        identity = lp.TS.credential.TS.identity;
        signature_scheme = SA_ed25519; //TODO
        signature_key = lp.TS.credential.TS.signature_key;
      });
      extensions = extensions;
      signature = lp.TS.signature;
    } <: key_package_nt)
  )

val treesync_to_parent_node: TS.node_package_t -> result parent_node_nt
let treesync_to_parent_node np =
  unmerged_leaves <-- mapM (fun (x:nat) -> if x < pow2 32 then return (Lib.IntTypes.u32 x) else internal_failure "") np.TS.unmerged_leafs;
  if not (Seq.length np.TS.parent_hash < 256) then
    internal_failure "treesync_to_parent_node: parent_hash too long"
  else if not ((byte_length ps_u32 unmerged_leaves) < pow2 32) then
    internal_failure "treesync_to_parent_node: unmerged_leaves too long"
  else (
    Seq.lemma_list_seq_bij unmerged_leaves;
    node_content <-- from_option "treesync_to_parent_node: can't parse content" ((ps_to_pse ps_node_package_content).parse_exact np.TS.content);
    return ({
      public_key = node_content.public_key;
      parent_hash = np.TS.parent_hash;
      unmerged_leaves = Seq.seq_of_list unmerged_leaves;
    } <: parent_node_nt)
  )

val parent_node_to_treesync: parent_node_nt -> result TS.node_package_t
let parent_node_to_treesync pn =
  return ({
        TS.version = 0;
        TS.content_dir = Left; //We don't care I guess
        TS.unmerged_leafs = List.Tot.map (fun x -> let open Lib.IntTypes in (v x <: nat)) (Seq.seq_to_list pn.unmerged_leaves);
        TS.parent_hash = pn.parent_hash;
        TS.content = ps_node_package_content.serialize ({
          public_key = pn.public_key;
          encrypted_path_secret = Seq.empty;
          last_group_context = bytes_empty;
        });
      } <: TS.node_package_t)

//TODO: this function should be equivalent to key_package_to_treesync followed by leaf_package_sync_to_kem (non-existant at this time)
//Refactor?
val key_package_to_treekem: cs:ciphersuite -> key_package_nt -> result (TK.member_info cs)
let key_package_to_treekem cs kp =
  if not (Seq.length kp.public_key = hpke_public_key_length cs) then
    error "key_package_to_treekem: public key has wrong length"
  else
    return ({
      TK.public_key = kp.public_key;
      TK.version = 0;
    } <: TK.member_info cs)

val update_path_node_to_treekem: cs:ciphersuite -> bytes -> direction -> update_path_node_nt -> result (TK.key_package cs)
let update_path_node_to_treekem cs group_context dir update_path_node =
  if not (Seq.length update_path_node.public_key = hpke_public_key_length cs) then
    error "update_path_node_to_treekem: public key has wrong length"
  else (
    path_secret_ciphertext <-- mapM (fun (hpke_ciphertext: hpke_ciphertext_nt) ->
      if not (Seq.length hpke_ciphertext.kem_output = hpke_kem_output_length cs) then
        error "update_path_node_to_treekem: kem output has wrong length"
      else
        return ({
          TK.kem_output = hpke_ciphertext.kem_output;
          TK.ciphertext = hpke_ciphertext.ciphertext;
        })
    ) (Seq.seq_to_list update_path_node.encrypted_path_secret);
    return ({
      TK.public_key = update_path_node.public_key;
      TK.version = 0;
      TK.last_group_context = group_context;
      TK.unmerged_leafs = [];
      TK.path_secret_from = dir;
      TK.path_secret_ciphertext = path_secret_ciphertext;
    })
  )

#push-options "--z3rlimit 30"
val update_path_to_treekem: cs:ciphersuite -> l:nat -> n:tree_size l -> i:leaf_index n -> bytes -> update_path:update_path_nt -> result (TK.pathkem cs l n i)
let rec update_path_to_treekem cs l n i group_context update_path =
  if l = 0 then (
    if not (Seq.length update_path.nodes = 0) then
      internal_failure "update_path_to_treekem: update_path.nodes is too long"
    else (
      leaf_package <-- key_package_to_treekem cs update_path.leaf_key_package;
      return (PLeaf leaf_package)
    )
  ) else if (n <= pow2 (l-1)) then (
    path_next <-- update_path_to_treekem cs (l-1) n i group_context update_path;
    return (PSkip _ path_next)
  ) else (
    if not (Seq.length update_path.nodes > 0) then
      internal_failure "update_path_to_treekem: update_path.nodes is too short"
    else (
      let update_path_length = (Seq.length update_path.nodes) in
      let head_update_path_nodes = Seq.index update_path.nodes (update_path_length-1) in
      let tail_update_path_nodes = Seq.slice update_path.nodes 0 (update_path_length-1) in
      //TODO this is an easy lemma
      assume (byte_length ps_update_path_node (Seq.seq_to_list tail_update_path_nodes) <= byte_length ps_update_path_node (Seq.seq_to_list update_path.nodes));
      let next_update_path = { update_path with nodes = tail_update_path_nodes } in
      let (|dir, next_i|) = child_index l i in
      path_next <-- update_path_to_treekem cs (l-1) (if dir = Left then pow2 (l-1) else n - (pow2 (l-1))) next_i group_context next_update_path;
      path_data <-- update_path_node_to_treekem cs group_context dir head_update_path_nodes;
      return (PNode path_data path_next)
    )
  )
#pop-options

val treesync_to_update_path_node: TS.node_package_t -> result update_path_node_nt
let treesync_to_update_path_node np =
  node_content <-- from_option "treesync_to_update_path_node: can't parse content" ((ps_to_pse ps_node_package_content).parse_exact np.TS.content);
  return ({
    public_key = node_content.public_key;
    encrypted_path_secret = node_content.encrypted_path_secret;
  } <: update_path_node_nt)

val treesync_to_update_path_aux: #l:nat -> #n:tree_size l -> #i:leaf_index n -> ciphersuite -> TS.pathsync l n i -> result (key_package_nt & list update_path_node_nt)
let rec treesync_to_update_path_aux #l #n #i cs p =
  match p with
  | PLeaf (Some lp) ->
    kp <-- treesync_to_keypackage cs lp;
    return (kp, [])
  | PLeaf None ->
    internal_failure "treesync_to_update_path: the path must not contain any blank node"
  | PSkip _ p_next ->
    treesync_to_update_path_aux cs p_next
  | PNode (Some np) p_next ->
    upn <-- treesync_to_update_path_node np;
    tmp <-- treesync_to_update_path_aux cs p_next;
    let (kp, upns) = tmp in
    return (kp, upn::upns)
  | PNode None p_next ->
    internal_failure "treesync_to_update_path: the path must not contain any blank node"

val treesync_to_update_path: #l:nat -> #n:tree_size l -> #i:leaf_index n -> ciphersuite -> TS.pathsync l n i -> result update_path_nt
let treesync_to_update_path #l #n #i cs p =
  tmp <-- treesync_to_update_path_aux cs p;
  let (kp, upns) = tmp in
  let upns = List.rev upns in
  Seq.lemma_list_seq_bij upns;
  if not (byte_length ps_update_path_node upns < pow2 32) then
    error "treesync_to_update_path: nodes too long"
  else
    return ({
      leaf_key_package = kp;
      nodes = Seq.seq_of_list upns;
    })

(*** ratchet_tree extension (11.3) ***)

val dumb_credential: TS.credential_t
let dumb_credential = {
  TS.version = 0;
  TS.identity = Seq.empty;
  TS.signature_key = Seq.empty;
}

val ratchet_tree_l_n: nodes:ratchet_tree_nt -> result (l:nat & n:tree_size l{Seq.length nodes == n+n-1})
let ratchet_tree_l_n nodes =
  let n_nodes = Seq.length nodes in
  if n_nodes%2 = 0 then
    error "ratchet_tree_l_n: length must be odd"
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
    | Some_nt _ -> error "ratchet_tree_to_treesync_aux: node must be a leaf!"
    | None_nt ->
      return (TLeaf (dumb_credential, None))
    | _ -> error "ratchet_tree_to_treesync_aux: option is invalid"
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
      np <-- parent_node_to_treesync pn;
      return (TNode (dumb_credential, Some np) left_res right_res)
    | Some_nt _ -> error "ratchet_tree_to_treesync_aux: node must be a parent!"
    | None_nt ->
      return (TNode (dumb_credential, None) left_res right_res)
    | _ -> error "ratchet_tree_to_treesync_aux: option is invalid"
  )

val treesync_to_ratchet_tree: #l:nat -> #n:tree_size l -> cs:ciphersuite -> TS.treesync l n -> result (Seq.seq (option_nt node_nt))
let rec treesync_to_ratchet_tree #l #n cs t =
  match t with
  | TLeaf (_, None) ->
    return (Seq.create 1 None_nt)
  | TLeaf (_, Some lp) ->
    key_package <-- treesync_to_keypackage cs lp;
    return (Seq.create 1 (Some_nt (N_leaf (key_package))))
  | TSkip _ t' ->
    treesync_to_ratchet_tree cs t'
  | TNode (_, onp) left right ->
    parent_node <-- (
      match onp with
      | None -> return None_nt
      | Some np ->
        result <-- treesync_to_parent_node np;
        return (Some_nt (N_parent result))
    );
    left_ratchet <-- treesync_to_ratchet_tree cs left;
    right_ratchet <-- treesync_to_ratchet_tree cs right;
    return (Seq.append left_ratchet (Seq.append (Seq.create 1 parent_node) right_ratchet))
