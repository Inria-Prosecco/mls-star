module MLS.NetworkBinder

open Comparse
open MLS.NetworkTypes
open MLS.Crypto
open MLS.Result
open MLS.Tree
module TS = MLS.TreeSync.Types
module TK = MLS.TreeKEM.Types

noeq type treekem_content_nt (bytes:Type0) {|bytes_like bytes|} = {
  public_key: hpke_public_key_nt bytes;
}

%splice [ps_treekem_content_nt] (gen_parser (`treekem_content_nt))

instance parseable_serializeable_treekem_content_nt (bytes:Type0) {|bytes_like bytes|}: parseable_serializeable bytes (treekem_content_nt bytes) =
  mk_parseable_serializeable ps_treekem_content_nt

[@@ is_parser; is_parser_for (`%direction)]
val ps_direction: #bytes:Type0 -> {|bytes_like bytes|} -> parser_serializer bytes direction
let ps_direction #bytes #bl =
  let pred (x:nat_lbytes 1) = x < 2 in
  mk_isomorphism direction (refine (ps_nat_lbytes 1) pred)
    (fun x -> match x with | 0 -> Left | 1 -> Right)
    (fun x -> match x with | Left -> 0 | Right -> 1)

noeq type treekem_impl_data_nt (bytes:Type0) {|bytes_like bytes|} = {
  content_dir: direction;
  encrypted_path_secret: tls_seq bytes ps_hpke_ciphertext_nt ({min=0; max=(pow2 32)-1});
  last_group_context: tls_bytes bytes ({min=0; max=(pow2 64) - 1});
}

%splice [ps_treekem_impl_data_nt] (gen_parser (`treekem_impl_data_nt))

instance parseable_serializeable_treekem_impl_data_nt (bytes:Type0) {|bytes_like bytes|}: parseable_serializeable bytes (treekem_impl_data_nt bytes) =
  mk_parseable_serializeable ps_treekem_impl_data_nt

(*** NetworkTreeSyncBinder ***)

val network_to_leaf_package: #bytes:Type0 -> {|bytes_like bytes|} -> leaf_node_nt bytes -> result (TS.leaf_package_t bytes)
let network_to_leaf_package #bytes #bl ln =
  match ln.data.credential with
  | C_basic cred ->
    return ({
      TS.version = 0;
      TS.content = {
        TS.content = serialize (treekem_content_nt bytes) ({public_key = ln.data.public_key});
        TS.impl_data = empty;
      };
      TS.credential = {
        TS.version = 0;
        TS.identity = cred.identity;
        TS.signature_key = cred.signature_key;
      };
      TS.capabilities = ln.data.capabilities;
      TS.source = ln.data.source;
      TS.lifetime = ln.data.lifetime;
      TS.parent_hash = ln.data.parent_hash;
      TS.extensions = (ps_to_pse (ps_tls_seq ps_extension_nt _)).serialize_exact (ln.data.extensions);
      TS.signature = ln.signature;
    } <: TS.leaf_package_t bytes)
  | _ -> error "network_to_leaf_package: credential type not supported"

val leaf_package_to_network: #bytes:Type0 -> {|bytes_like bytes|} -> TS.leaf_package_t bytes -> result (leaf_node_nt bytes)
let leaf_package_to_network #bytes #bl lp =
  if not (length lp.TS.credential.TS.identity < pow2 16) then
    error "leaf_package_to_network: identity too long"
  else if not (length lp.TS.credential.TS.signature_key < pow2 16) then
    error "leaf_package_to_network: signature_key too long"
  else if not (length lp.TS.signature < pow2 16) then
    error "leaf_package_to_network: signature too long"
  else (
    content <-- from_option "leaf_package_to_network: can't parse leaf content" (parse (treekem_content_nt bytes) lp.TS.content.content);
    extensions <-- from_option "leaf_package_to_network: can't parse extensions" ((ps_to_pse (ps_tls_seq ps_extension_nt _)).parse_exact lp.TS.extensions);
    return ({
      data = {
        public_key = content.public_key;
        credential = C_basic ({
          identity = lp.TS.credential.TS.identity;
          signature_scheme = SA_ed25519 (); //TODO
          signature_key = lp.TS.credential.TS.signature_key;
        });
        capabilities = lp.TS.capabilities;
        source = lp.TS.source;
        lifetime = lp.TS.lifetime;
        parent_hash = lp.TS.parent_hash;
        extensions = extensions;
      };
      signature = lp.TS.signature;
    } <: leaf_node_nt bytes)
  )

val node_package_to_network: #bytes:Type0 -> {|bytes_like bytes|} -> TS.node_package_t bytes -> result (parent_node_nt bytes)
let node_package_to_network #bytes #bl np =
  unmerged_leaves <-- mapM (fun (x:nat) -> if x < pow2 32 then return (x <: nat_lbytes 4) else internal_failure "") np.TS.unmerged_leaves;
  if not (length np.TS.parent_hash < 256) then
    internal_failure "node_package_to_network: parent_hash too long"
  else if not ((bytes_length #bytes (ps_nat_lbytes 4) unmerged_leaves) < pow2 32) then
    internal_failure "node_package_to_network: unmerged_leaves too long"
  else (
    Seq.lemma_list_seq_bij unmerged_leaves;
    node_content <-- from_option "node_package_to_network: can't parse content" (parse (treekem_content_nt bytes) np.TS.content.content);
    return ({
      public_key = node_content.public_key;
      parent_hash = np.TS.parent_hash;
      unmerged_leaves = Seq.seq_of_list unmerged_leaves;
    } <: parent_node_nt bytes)
  )

val network_to_node_package: #bytes:Type0 -> {|bytes_like bytes|} -> parent_node_nt bytes -> result (TS.node_package_t bytes)
let network_to_node_package #bytes #bl pn =
  bytes_length_nil #bytes ps_hpke_ciphertext_nt;
  return ({
        TS.version = 0;
        TS.unmerged_leaves = List.Tot.map (fun (x:nat_lbytes 4) -> x <: nat) (Seq.seq_to_list pn.unmerged_leaves);
        TS.parent_hash = pn.parent_hash;
        TS.content = {
          TS.content = serialize (treekem_content_nt bytes) ({
            public_key = pn.public_key;
          });
          TS.impl_data = serialize (treekem_impl_data_nt bytes) ({
            content_dir = Left; //We don't care
            encrypted_path_secret = Seq.empty;
            last_group_context = empty #bytes;
          });
        }
      } <: TS.node_package_t bytes)

//TODO: this function should be equivalent to key_package_to_treesync followed by leaf_package_sync_to_kem (non-existant at this time)
//Refactor?
val leaf_node_to_treekem: #bytes:Type0 -> {|crypto_bytes bytes|} -> leaf_node_nt bytes -> result (TK.member_info bytes)
let leaf_node_to_treekem #bytes #cb ln =
  if not (length (ln.data.public_key <: bytes) = hpke_public_key_length #bytes) then
    error "leaf_node_to_treekem: public key has wrong length"
  else
    return ({
      TK.public_key = ln.data.public_key;
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
      leaf_package <-- leaf_node_to_treekem update_path.leaf_node;
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

//TODO this function has really bad encapsulation and should not exist in a reasonable implementation
val treesync_to_update_path_node: #bytes:Type0 -> {|bytes_like bytes|} -> TS.node_package_t bytes -> result (update_path_node_nt bytes)
let treesync_to_update_path_node #bytes #bl np =
  content <-- from_option "treesync_to_update_path_node: can't parse content" (parse (treekem_content_nt bytes) np.TS.content.content);
  impl_data <-- from_option "treesync_to_update_path_node: can't parse impl data" (parse (treekem_impl_data_nt bytes) np.TS.content.impl_data);
  return ({
    public_key = content.public_key;
    encrypted_path_secret = impl_data.encrypted_path_secret;
  } <: update_path_node_nt bytes)

//TODO same
val treesync_to_update_path_aux: #bytes:Type0 -> {|bytes_like bytes|} -> #l:nat -> #n:tree_size l -> #i:leaf_index n -> TS.pathsync bytes l n i -> result (leaf_node_nt bytes & list (update_path_node_nt bytes))
let rec treesync_to_update_path_aux #bytes #bl #l #n #i p =
  match p with
  | PLeaf (Some lp) ->
    kp <-- leaf_package_to_network lp;
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

//TODO same
val treesync_to_update_path: #bytes:Type0 -> {|bytes_like bytes|} -> #l:nat -> #n:tree_size l -> #i:leaf_index n -> TS.pathsync bytes l n i -> result (update_path_nt bytes)
let treesync_to_update_path #bytes #bl #l #n #i p =
  tmp <-- treesync_to_update_path_aux p;
  let (kp, upns) = tmp in
  let upns = List.rev upns in
  Seq.lemma_list_seq_bij upns;
  if not (bytes_length ps_update_path_node_nt upns < pow2 32) then
    error "treesync_to_update_path: nodes too long"
  else
    return ({
      leaf_node = kp;
      nodes = Seq.seq_of_list upns;
    } <: update_path_nt bytes)

(*** ratchet_tree extension (11.3) ***)

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
      kp <-- network_to_leaf_package kp;
      return (TLeaf (Some kp))
    | Some _ -> error "ratchet_tree_to_treesync_aux: node must be a leaf!"
    | None ->
      return (TLeaf None)
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
      np <-- network_to_node_package pn;
      return (TNode (Some np) left_res right_res)
    | Some _ -> error "ratchet_tree_to_treesync_aux: node must be a parent!"
    | None ->
      return (TNode None left_res right_res)
  )

val treesync_to_ratchet_tree: #bytes:Type0 -> {|bytes_like bytes|} -> #l:nat -> #n:tree_size l -> TS.treesync bytes l n -> result (Seq.seq (option (node_nt bytes)))
let rec treesync_to_ratchet_tree #bytes #bl #l #n t =
  match t with
  | TLeaf None ->
    return (Seq.create 1 None)
  | TLeaf (Some lp) ->
    key_package <-- leaf_package_to_network lp;
    return (Seq.create 1 (Some (N_leaf (key_package))))
  | TSkip _ t' ->
    treesync_to_ratchet_tree t'
  | TNode onp left right ->
    parent_node <-- (
      match onp with
      | None -> return None
      | Some np ->
        result <-- node_package_to_network np;
        return (Some (N_parent result))
    );
    left_ratchet <-- treesync_to_ratchet_tree left;
    right_ratchet <-- treesync_to_ratchet_tree right;
    return (Seq.append left_ratchet (Seq.append (Seq.create 1 parent_node) right_ratchet))
