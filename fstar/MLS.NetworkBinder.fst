module MLS.NetworkBinder

open Comparse
open MLS.NetworkTypes
open MLS.Crypto
open MLS.Result
open MLS.Tree
module TS = MLS.TreeSync.Types
module TK = MLS.TreeKEM.Types

noeq type leaf_package_content_nt (bytes:Type0) {|bytes_like bytes|} = {
  public_key: hpke_public_key_nt bytes;
}

%splice [ps_leaf_package_content_nt] (gen_parser (`leaf_package_content_nt))

instance parseable_serializeable_leaf_package_content_nt (bytes:Type0) {|bytes_like bytes|}: parseable_serializeable bytes (leaf_package_content_nt bytes) =
  mk_parseable_serializeable ps_leaf_package_content_nt

noeq type node_package_content_nt (bytes:Type0) {|bytes_like bytes|} = {
  public_key: hpke_public_key_nt bytes;
  encrypted_path_secret: tls_seq bytes ps_hpke_ciphertext_nt ({min=0; max=(pow2 32)-1});
  last_group_context: tls_bytes bytes ({min=0; max=(pow2 64) - 1});
}

%splice [ps_node_package_content_nt] (gen_parser (`node_package_content_nt))

instance parseable_serializeable_node_package_content_nt (bytes:Type0) {|bytes_like bytes|}: parseable_serializeable bytes (node_package_content_nt bytes) =
  mk_parseable_serializeable ps_node_package_content_nt

(*** NetworkTreeSyncBinder ***)

val key_package_to_treesync: #bytes:Type0 -> {|bytes_like bytes|} -> key_package_nt bytes -> result (TS.leaf_package_t bytes)
let key_package_to_treesync #bytes #bl kp =
  match kp.tbs.credential with
  | C_basic cred ->
    return ({
      TS.credential = {
        TS.version = 0;
        TS.identity = cred.identity;
        TS.signature_key = cred.signature_key;
      };
      TS.endpoint_id = kp.tbs.endpoint_id;
      TS.version = 0;
      TS.content = serialize (leaf_package_content_nt bytes) ({public_key = kp.tbs.public_key});
      TS.extensions = (ps_to_pse (ps_tls_seq ps_extension_nt _)).serialize_exact (kp.tbs.extensions);
      TS.signature = kp.signature;
    })
  | _ -> error "key_package_to_treesync: credential type not supported"

val treesync_to_keypackage: #bytes:Type0 -> {|crypto_bytes bytes|} -> TS.leaf_package_t bytes -> result (key_package_nt bytes)
let treesync_to_keypackage #bytes #cb lp =
  if not (length lp.TS.credential.TS.identity < pow2 16) then
    error "treesync_to_keypackage: identity too long"
  else if not (length lp.TS.endpoint_id < 256) then
    error "treesync_to_keypackage: identity too long"
  else if not (length lp.TS.credential.TS.signature_key < pow2 16) then
    error "treesync_to_keypackage: signature_key too long"
  else if not (length lp.TS.signature < pow2 16) then
    error "treesync_to_keypackage: signature too long"
  else (
    leaf_content <-- from_option "treesync_to_keypackage: can't parse leaf content" (parse (leaf_package_content_nt bytes) lp.TS.content);
    extensions <-- from_option "treesync_to_keypackage: can't parse extensions" ((ps_to_pse (ps_tls_seq ps_extension_nt _)).parse_exact lp.TS.extensions);
    let cipher_suite = available_ciphersuite_to_network (ciphersuite #bytes) in
    return ({
      tbs = {
        version = PV_mls10 ();
        cipher_suite = cipher_suite;
        public_key = leaf_content.public_key;
        endpoint_id = lp.TS.endpoint_id;
        credential = C_basic ({
          identity = lp.TS.credential.TS.identity;
          signature_scheme = SA_ed25519 (); //TODO
          signature_key = lp.TS.credential.TS.signature_key;
        });
        extensions = extensions;
      };
      signature = lp.TS.signature;
    } <: key_package_nt bytes)
  )

val treesync_to_parent_node: #bytes:Type0 -> {|bytes_like bytes|} -> TS.node_package_t bytes -> result (parent_node_nt bytes)
let treesync_to_parent_node #bytes #bl np =
  unmerged_leaves <-- mapM (fun (x:nat) -> if x < pow2 32 then return (x <: nat_lbytes 4) else internal_failure "") np.TS.unmerged_leaves;
  if not (length np.TS.parent_hash < 256) then
    internal_failure "treesync_to_parent_node: parent_hash too long"
  else if not ((bytes_length #bytes (ps_nat_lbytes 4) unmerged_leaves) < pow2 32) then
    internal_failure "treesync_to_parent_node: unmerged_leaves too long"
  else (
    Seq.lemma_list_seq_bij unmerged_leaves;
    node_content <-- from_option "treesync_to_parent_node: can't parse content" (parse (node_package_content_nt bytes) np.TS.content);
    return ({
      public_key = node_content.public_key;
      parent_hash = np.TS.parent_hash;
      unmerged_leaves = Seq.seq_of_list unmerged_leaves;
    } <: parent_node_nt bytes)
  )

val parent_node_to_treesync: #bytes:Type0 -> {|bytes_like bytes|} -> parent_node_nt bytes -> result (TS.node_package_t bytes)
let parent_node_to_treesync #bytes #bl pn =
  bytes_length_nil #bytes ps_hpke_ciphertext_nt;
  return ({
        TS.version = 0;
        TS.content_dir = Left; //We don't care I guess
        TS.unmerged_leaves = List.Tot.map (fun (x:nat_lbytes 4) -> x <: nat) (Seq.seq_to_list pn.unmerged_leaves);
        TS.parent_hash = pn.parent_hash;
        TS.content = serialize (node_package_content_nt bytes) ({
          public_key = pn.public_key;
          encrypted_path_secret = Seq.empty;
          last_group_context = empty #bytes;
        });
      } <: TS.node_package_t bytes)

//TODO: this function should be equivalent to key_package_to_treesync followed by leaf_package_sync_to_kem (non-existant at this time)
//Refactor?
val key_package_to_treekem: #bytes:Type0 -> {|crypto_bytes bytes|} -> key_package_nt bytes -> result (TK.member_info bytes)
let key_package_to_treekem #bytes #cb kp =
  if not (length (kp.tbs.public_key <: bytes) = hpke_public_key_length #bytes) then
    error "key_package_to_treekem: public key has wrong length"
  else
    return ({
      TK.public_key = kp.tbs.public_key;
      TK.version = 0;
    } <: TK.member_info bytes)

val update_path_node_to_treekem: #bytes:Type0 -> {|crypto_bytes bytes|} -> bytes -> direction -> update_path_node_nt bytes -> result (TK.key_package bytes)
let update_path_node_to_treekem #bytes #cb group_context dir update_path_node =
  if not (length (update_path_node.public_key <: bytes) = hpke_public_key_length #bytes) then
    error "update_path_node_to_treekem: public key has wrong length"
  else (
    path_secret_ciphertext <-- mapM (fun (hpke_ciphertext: hpke_ciphertext_nt bytes) ->
      if not (length (hpke_ciphertext.kem_output <: bytes) = hpke_kem_output_length #bytes) then
        error "update_path_node_to_treekem: kem output has wrong length"
      else
        return ({
          TK.kem_output = hpke_ciphertext.kem_output;
          TK.ciphertext = hpke_ciphertext.ciphertext;
        } <: TK.path_secret_ciphertext bytes)
    ) (Seq.seq_to_list update_path_node.encrypted_path_secret);
    return ({
      TK.public_key = update_path_node.public_key;
      TK.version = 0;
      TK.last_group_context = group_context;
      TK.unmerged_leaves = [];
      TK.path_secret_from = dir;
      TK.path_secret_ciphertext = path_secret_ciphertext;
    })
  )

#push-options "--z3rlimit 30"
val update_path_to_treekem: #bytes:Type0 -> {|crypto_bytes bytes|} -> l:nat -> n:tree_size l -> i:leaf_index n -> bytes -> update_path:update_path_nt bytes -> result (TK.pathkem bytes l n i)
let rec update_path_to_treekem #bytes #cb l n i group_context update_path =
  if l = 0 then (
    if not (Seq.length update_path.nodes = 0) then
      internal_failure "update_path_to_treekem: update_path.nodes is too long"
    else (
      leaf_package <-- key_package_to_treekem update_path.leaf_key_package;
      return (PLeaf leaf_package)
    )
  ) else if (n <= pow2 (l-1)) then (
    path_next <-- update_path_to_treekem (l-1) n i group_context update_path;
    return (PSkip _ path_next)
  ) else (
    if not (Seq.length update_path.nodes > 0) then
      internal_failure "update_path_to_treekem: update_path.nodes is too short"
    else (
      let update_path_length = (Seq.length update_path.nodes) in
      let head_update_path_nodes = Seq.index update_path.nodes (update_path_length-1) in
      let tail_update_path_nodes = Seq.slice update_path.nodes 0 (update_path_length-1) in
      //TODO this is an easy lemma
      assume (bytes_length ps_update_path_node_nt (Seq.seq_to_list tail_update_path_nodes) <= bytes_length ps_update_path_node_nt (Seq.seq_to_list update_path.nodes));
      let next_update_path = { update_path with nodes = tail_update_path_nodes } in
      let (|dir, next_i|) = child_index l i in
      path_next <-- update_path_to_treekem (l-1) (if dir = Left then pow2 (l-1) else n - (pow2 (l-1))) next_i group_context next_update_path;
      path_data <-- update_path_node_to_treekem group_context dir head_update_path_nodes;
      return (PNode path_data path_next)
    )
  )
#pop-options

val treesync_to_update_path_node: #bytes:Type0 -> {|bytes_like bytes|} -> TS.node_package_t bytes -> result (update_path_node_nt bytes)
let treesync_to_update_path_node #bytes #bl np =
  node_content <-- from_option "treesync_to_update_path_node: can't parse content" (parse (node_package_content_nt bytes) np.TS.content);
  return ({
    public_key = node_content.public_key;
    encrypted_path_secret = node_content.encrypted_path_secret;
  } <: update_path_node_nt bytes)

val treesync_to_update_path_aux: #bytes:Type0 -> {|crypto_bytes bytes|} -> #l:nat -> #n:tree_size l -> #i:leaf_index n -> TS.pathsync bytes l n i -> result (key_package_nt bytes & list (update_path_node_nt bytes))
let rec treesync_to_update_path_aux #bytes #cb #l #n #i p =
  match p with
  | PLeaf (Some lp) ->
    kp <-- treesync_to_keypackage lp;
    return (kp, [])
  | PLeaf None ->
    internal_failure "treesync_to_update_path: the path must not contain any blank node"
  | PSkip _ p_next ->
    treesync_to_update_path_aux p_next
  | PNode (Some np) p_next ->
    upn <-- treesync_to_update_path_node np;
    tmp <-- treesync_to_update_path_aux p_next;
    let (kp, upns) = tmp in
    return (kp, upn::upns)
  | PNode None p_next ->
    internal_failure "treesync_to_update_path: the path must not contain any blank node"

val treesync_to_update_path: #bytes:Type0 -> {|crypto_bytes bytes|} -> #l:nat -> #n:tree_size l -> #i:leaf_index n -> TS.pathsync bytes l n i -> result (update_path_nt bytes)
let treesync_to_update_path #bytes #cb #l #n #i p =
  tmp <-- treesync_to_update_path_aux p;
  let (kp, upns) = tmp in
  let upns = List.rev upns in
  Seq.lemma_list_seq_bij upns;
  if not (bytes_length ps_update_path_node_nt upns < pow2 32) then
    error "treesync_to_update_path: nodes too long"
  else
    return ({
      leaf_key_package = kp;
      nodes = Seq.seq_of_list upns;
    })

(*** ratchet_tree extension (11.3) ***)

val dumb_credential: #bytes:Type0 -> {|bytes_like bytes|} -> TS.credential_t bytes
let dumb_credential #bytes #bl = {
  TS.version = 0;
  TS.identity = empty;
  TS.signature_key = empty;
}

val ratchet_tree_l_n: #bytes:Type0 -> {|bytes_like bytes|} -> nodes:ratchet_tree_nt bytes -> result (l:nat & n:tree_size l{Seq.length nodes == n+n-1})
let ratchet_tree_l_n #bytes #bl nodes =
  let n_nodes = Seq.length nodes in
  if n_nodes%2 = 0 then
    error "ratchet_tree_l_n: length must be odd"
  else
    let n = (n_nodes+1)/2 in
    let l = (TreeMath.Internal.log2 n) + 1 in
    return (|l, n|)

val ratchet_tree_to_treesync: #bytes:Type0 -> {|bytes_like bytes|} -> l:nat -> n:tree_size l -> nodes:Seq.seq (option (node_nt bytes)){Seq.length nodes = (n+n-1)} -> result (TS.treesync bytes l n)
let rec ratchet_tree_to_treesync #bytes #bl l n nodes =
  if l = 0 then (
    assert (Seq.length nodes == 1);
    match (Seq.index nodes 0) with
    | Some (N_leaf kp) ->
      kp <-- key_package_to_treesync kp;
      return (TLeaf (dumb_credential, Some kp))
    | Some _ -> error "ratchet_tree_to_treesync_aux: node must be a leaf!"
    | None ->
      return (TLeaf (dumb_credential, None))
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
    | Some (N_parent pn) ->
      np <-- parent_node_to_treesync pn;
      return (TNode (dumb_credential, Some np) left_res right_res)
    | Some _ -> error "ratchet_tree_to_treesync_aux: node must be a parent!"
    | None ->
      return (TNode (dumb_credential, None) left_res right_res)
  )

val treesync_to_ratchet_tree: #bytes:Type0 -> {|crypto_bytes bytes|} -> #l:nat -> #n:tree_size l -> TS.treesync bytes l n -> result (Seq.seq (option (node_nt bytes)))
let rec treesync_to_ratchet_tree #bytes #cb #l #n t =
  match t with
  | TLeaf (_, None) ->
    return (Seq.create 1 None)
  | TLeaf (_, Some lp) ->
    key_package <-- treesync_to_keypackage lp;
    return (Seq.create 1 (Some (N_leaf (key_package))))
  | TSkip _ t' ->
    treesync_to_ratchet_tree t'
  | TNode (_, onp) left right ->
    parent_node <-- (
      match onp with
      | None -> return None
      | Some np ->
        result <-- treesync_to_parent_node np;
        return (Some (N_parent result))
    );
    left_ratchet <-- treesync_to_ratchet_tree left;
    right_ratchet <-- treesync_to_ratchet_tree right;
    return (Seq.append left_ratchet (Seq.append (Seq.create 1 parent_node) right_ratchet))
