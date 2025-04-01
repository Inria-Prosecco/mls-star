module MLS.TreeKEM.Symbolic.API.Tree

open Comparse
open DY.Core
open DY.Lib
open MLS.Crypto
open MLS.Tree
open MLS.NetworkTypes
open MLS.TreeSync.NetworkTypes
open MLS.TreeSync.Types
open MLS.TreeSync.Operations
open MLS.TreeSync.Invariants.ParentHash { node_not_blank }
open MLS.TreeSync.Symbolic.LeafNodeSignature
open MLS.TreeSync.Symbolic.Event.LeafNodeHasBeenVerified
// open MLS.TreeSync.Invariants.AuthService { as_tokens }
// open MLS.TreeSync.Symbolic.LeafNodeSignature
// open MLS.TreeSync.Symbolic.AuthService.CredentialInterpretation
// open MLS.TreeSync.Symbolic.AuthService
// open MLS.TreeSync.Symbolic.State.SignatureKey
open MLS.TreeKEM.NetworkTypes
open MLS.TreeKEM.Types
open MLS.TreeKEM.Operations
open MLS.TreeKEM.Invariants.Proofs
open MLS.TreeKEM.API.Tree.Types
open MLS.TreeKEM.API.Tree
open MLS.TreeSync.API.Types
open MLS.TreeSync.API
open MLS.NetworkBinder
open MLS.NetworkBinder.Properties
open MLS.NetworkBinder.Properties.Proofs
open MLS.Symbolic
open MLS.Symbolic.Randomness
open MLS.Symbolic.MyMkRand
// open MLS.Symbolic.Lemmas
// open MLS.Symbolic.Labels.Guard
// open MLS.Symbolic.Labels.Event
// open MLS.Symbolic.Labels.Big
//open MLS.Crypto.Derived.Symbolic.SignWithLabel
open MLS.TreeKEM.Symbolic.State.NodeKey
open MLS.TreeKEM.Symbolic.Tree.Operations
open MLS.TreeSync.Symbolic.AuthService
open MLS.TreeSync.Proofs.ParentHashGuarantees { canonicalize_unmerged_leaves }

// open MLS.TreeSync.Proofs.ParentHashGuarantees
// open MLS.TreeSync.Invariants.UnmergedLeaves
// open MLS.TreeSync.Invariants.ParentHash
// open MLS.TreeSync.Invariants.ParentHash.Proofs
// open MLS.TreeSync.Invariants.AuthService
// open MLS.TreeSync.Invariants.ValidLeaves
// open MLS.TreeSync.Operations
open MLS.MiscLemmas
open MLS.TreeCommon
open MLS.Tree.Lemmas
open MLS.TreeKEM.Symbolic.Tree.Labels
open MLS.TreeKEM.Invariants
open MLS.TreeSync.Symbolic.Parsers
open MLS.TreeSyncTreeKEMBinder
open MLS.TreeSyncTreeKEMBinder.Properties
open MLS.TreeSyncTreeKEMBinder.Proofs
open MLS.Result

module TS=MLS.TreeSync.API
module TK=MLS.TreeKEM.API.Tree
module TST=MLS.TreeSync.API.Types
module TKT=MLS.TreeKEM.API.Tree.Types

#set-options "--fuel 0 --ifuel 0"

val treekem_tree_state_invariant:
  {|crypto_invariants|} ->
  #leaf_ind:nat ->
  tr:trace -> me:principal ->
  treekem_tree_state bytes leaf_ind ->
  prop
let treekem_tree_state_invariant #cinvs #leaf_ind tr me st_tk =
  treekem_priv_state_pred tr me st_tk.priv

//TODO move
val extended_treesync_invariant:
  {|crypto_invariants|} ->
  #group_id:mls_bytes bytes ->
  tr:trace -> me:principal ->
  treesync_state bytes tkt dy_as_token group_id ->
  prop
let extended_treesync_invariant #cinvs #group_id tr me st_ts =
  treesync_state_valid (dy_asp tr) st_ts /\
  i_have_verified_every_leaf_node tr me st_ts.tree group_id /\
  is_well_formed (treesync bytes tkt _ _) (bytes_invariant tr) st_ts.tree

val treekem_tree_state_invariant_later:
  {|crypto_invariants|} ->
  #leaf_ind:nat ->
  tr1:trace -> tr2:trace -> me:principal ->
  tk:treekem_tree_state bytes leaf_ind ->
  Lemma
  (requires
    treekem_tree_state_invariant tr1 me tk /\
    tr1 <$ tr2
  )
  (ensures
    treekem_tree_state_invariant tr2 me tk
  )
  [SMTPat (treekem_tree_state_invariant tr1 me tk); SMTPat (tr1 <$ tr2)]
let treekem_tree_state_invariant_later #cinvs #leaf_ind tr1 tr2 me st_tk =
  treekem_priv_state_pred_later tr1 tr2 me st_tk.priv

(*** Create ***)

#push-options "--fuel 1 --ifuel 0"
val create_proof:
  {|crypto_invariants|} ->
  tr:trace -> me:principal ->
  leaf_private_key:hpke_private_key bytes -> leaf_public_key:bytes ->
  Lemma
  (requires is_node_sk_for_leaf_pk tr me (hpke_pk leaf_private_key) leaf_private_key)
  (ensures treekem_tree_state_invariant tr me (TK.create leaf_private_key leaf_public_key))
let create_proof #cinvs tr me leaf_private_key leaf_public_key =
  reveal_opaque (`%TK.create) (TK.create leaf_private_key leaf_public_key)
#pop-options

(*** Welcome ***)

#push-options "--fuel 1 --ifuel 0"
val create_empty_priv_proof:
  {|crypto_invariants|} ->
  tr:trace -> me:principal ->
  l:nat -> i:tree_index l -> li:leaf_index l i ->
  leaf_private_key:hpke_private_key bytes ->
  Lemma
  (requires is_node_sk_for_leaf_pk tr me (hpke_pk leaf_private_key) leaf_private_key)
  (ensures
    treekem_priv_state_pred tr me (create_empty_priv leaf_private_key <: treekem_priv bytes l i li) /\
    get_path_leaf (create_empty_priv leaf_private_key <: treekem_priv bytes l i li) == leaf_private_key
  )
let rec create_empty_priv_proof #cinvs tr me l i li leaf_private_key =
  if l = 0 then ()
  else create_empty_priv_proof tr me (l-1) (if is_left_leaf li then left_index i else right_index i) li leaf_private_key
#pop-options

val welcome_proof:
  {|crypto_invariants|} ->
  tr:trace -> me:principal ->
  #l:nat ->
  tk:treekem bytes l 0 -> leaf_decryption_key:hpke_private_key bytes -> opt_path_secret_and_inviter_ind:option (bytes & nat) -> leaf_ind:nat{leaf_ind < pow2 l /\ Some? (leaf_at tk leaf_ind)} ->
  Lemma
  (requires
    is_node_sk_for_leaf_pk tr me (hpke_pk leaf_decryption_key) leaf_decryption_key /\
    (
      match opt_path_secret_and_inviter_ind with
      | None -> True
      | Some (path_secret, inviter_ind) ->
        decoded_path_secret_good me (hpke_pk leaf_decryption_key) path_secret tr
    ) /\
    MLS.TreeKEM.Invariants.treekem_invariant tk /\
    has_mls_treekem_invariants
  )
  (ensures (
    match TK.welcome tk leaf_decryption_key opt_path_secret_and_inviter_ind leaf_ind with
    | Success res_k ->
      treekem_tree_state_invariant tr me res_k /\
      res_k.levels == l /\
      res_k.tree == tk
    | _ -> True
  ))
let welcome_proof #cinvs tr me #l tk leaf_decryption_key opt_path_secret_and_inviter_ind leaf_ind =
  reveal_opaque (`%TK.welcome) (TK.welcome tk leaf_decryption_key opt_path_secret_and_inviter_ind leaf_ind);
  create_empty_priv_proof tr me l 0 leaf_ind leaf_decryption_key;
  let priv: treekem_priv bytes l 0 leaf_ind = create_empty_priv leaf_decryption_key in
  match opt_path_secret_and_inviter_ind with
  | None -> ()
  | Some (path_secret, inviter_ind) -> (
    if not (Success? (TK.welcome tk leaf_decryption_key opt_path_secret_and_inviter_ind leaf_ind)) then ()
    else (
      let path_secret_level = compute_least_common_ancestor_level priv inviter_ind in
      path_apply_path_proof me tk priv path_secret path_secret_level tr
    )
  )

(*** Add ***)

#push-options "--fuel 1 --ifuel 0"
val add_proof:
  {|crypto_invariants|} ->
  tr:trace -> me:principal ->
  #leaf_ind:nat ->
  st_tk:treekem_tree_state bytes leaf_ind -> ln_k:treekem_leaf bytes ->
  Lemma
  (requires treekem_tree_state_invariant tr me st_tk)
  (ensures (
    let (res_k, li_k) =  TK.add st_tk ln_k in
    treekem_tree_state_invariant tr me res_k
  ))
let add_proof #cinvs tr me #leaf_ind st_tk ln_k =
  reveal_opaque (`%TK.add) (TK.add st_tk ln_k)
#pop-options

(*** Update ***)

#push-options "--fuel 1 --ifuel 1"
val path_blank_proof:
  {|crypto_invariants|} ->
  tr:trace -> me:principal ->
  #l:nat -> #i:tree_index l -> #li:leaf_index l i ->
  priv:treekem_priv bytes l i li -> blank_li:leaf_index l i{blank_li <> li} ->
  Lemma
  (requires treekem_priv_state_pred tr me priv)
  (ensures treekem_priv_state_pred tr me (path_blank priv blank_li))
let rec path_blank_proof #cinvs tr me #l #i #li priv blank_li =
  match priv with
  | PNode _ priv_next -> (
    if is_left_leaf li = is_left_leaf blank_li then
      path_blank_proof tr me priv_next blank_li
    else ()
  )
#pop-options

val update_myself_proof:
  {|crypto_invariants|} ->
  tr:trace -> me:principal ->
  #leaf_ind:nat ->
  st_tk:treekem_tree_state bytes leaf_ind -> ln_k:treekem_leaf bytes -> leaf_decryption_key:hpke_private_key bytes ->
  Lemma
  (requires
    is_node_sk_for_leaf_pk tr me (hpke_pk leaf_decryption_key) leaf_decryption_key /\
    treekem_tree_state_invariant tr me st_tk
  )
  (ensures treekem_tree_state_invariant tr me (TK.update_myself st_tk ln_k leaf_decryption_key))
let update_myself_proof #cinvs tr me #leaf_ind st_tk ln_k leaf_decryption_key =
  reveal_opaque (`%TK.update_myself) (TK.update_myself st_tk ln_k leaf_decryption_key);
  create_empty_priv_proof tr me st_tk.levels 0 leaf_ind leaf_decryption_key

val update_other_proof:
  {|crypto_invariants|} ->
  tr:trace -> me:principal ->
  #leaf_ind:nat ->
  st_tk:treekem_tree_state bytes leaf_ind -> ln_k:treekem_leaf bytes -> i:treekem_index st_tk{i <> leaf_ind} ->
  Lemma
  (requires treekem_tree_state_invariant tr me st_tk)
  (ensures treekem_tree_state_invariant tr me (TK.update_other st_tk ln_k i))
let update_other_proof #cinvs tr me #leaf_ind st_tk ln_k i =
  reveal_opaque (`%TK.update_other) (TK.update_other st_tk ln_k i);
  path_blank_proof tr me st_tk.priv i

(*** Remove ***)

#push-options "--fuel 1 --ifuel 1"
val fully_truncate_proof:
  {|crypto_invariants|} ->
  tr:trace -> me:principal ->
  #leaf_ind:nat ->
  st_tk:treekem_tree_state bytes leaf_ind ->
  Lemma
  (requires treekem_tree_state_invariant tr me st_tk)
  (ensures treekem_tree_state_invariant tr me (TK.fully_truncate st_tk))
  (decreases st_tk.levels)
let rec fully_truncate_proof #cinvs tr me #leaf_ind st_tk =
  if 1 <= st_tk.levels && is_tree_empty (TNode?.right st_tk.tree) then (
    fully_truncate_proof tr me (truncate_one st_tk)
  ) else ()
#pop-options

val remove_proof:
  {|crypto_invariants|} ->
  tr:trace -> me:principal ->
  #leaf_ind:nat ->
  st_tk:treekem_tree_state bytes leaf_ind -> i:treekem_index st_tk{i <> leaf_ind} ->
  Lemma
  (requires treekem_tree_state_invariant tr me st_tk)
  (ensures treekem_tree_state_invariant tr me (TK.remove st_tk i))
let remove_proof #cinvs tr me #leaf_ind st_tk i =
  reveal_opaque (`%TK.remove) (TK.remove st_tk i);
  path_blank_proof tr me st_tk.priv i;
  fully_truncate_proof tr me (remove_aux st_tk i)

(*** Commit ***)

#push-options "--fuel 0 --ifuel 1 --z3rlimit 25"
val process_commit_proof:
  {|protocol_invariants|} ->
  #group_id:mls_bytes bytes -> #leaf_ind:nat ->
  tr:trace -> me:principal ->
  st_ts:treesync_state bytes tkt dy_as_token group_id -> st_tk:treekem_tree_state bytes leaf_ind ->
  #li:treekem_index st_tk{li <> leaf_ind} ->
  p:sparse_update_path bytes st_tk.levels 0 li{st_ts.levels == st_tk.levels /\ path_filtering_ok st_ts.tree p} ->
  excluded_leaves:list nat{~(List.Tot.memP leaf_ind excluded_leaves)} -> group_context:group_context_nt bytes ->
  pend:TS.pending_commit st_ts (update_path_to_treesync p) -> token:dy_as_token ->
  Lemma
  (requires
    treesync_treekem_state_rel st_ts st_tk /\
    treekem_tree_state_invariant tr me st_tk /\
    path_filtering_ok st_ts.tree p /\

    Success? (TS.finalize_commit pend token) /\
    extended_treesync_invariant tr me (Success?.v (TS.finalize_commit pend token)) /\

    // the two below should be combined
    pathkem_good_weak (update_path_to_treekem p) tr /\
    is_well_formed _ (bytes_invariant tr) group_context /\
    bytes_invariant tr group_id /\

    trace_invariant tr /\
    has_mls_treekem_invariants /\
    has_treesync_treekem_link_invariants
  )
  (ensures (
    path_filtering_ok_update_path_to_treekem st_ts.tree p;
    path_filtering_ok_treesync_to_treekem st_ts.tree (update_path_to_treekem p);
    match TS.finalize_commit pend token, TK.commit st_tk (update_path_to_treekem p) excluded_leaves group_context with
    | Success new_st_ts, Success (new_st_tk, commit_secret) -> (
      treekem_tree_state_invariant tr me new_st_tk /\
      bytes_invariant tr commit_secret /\
      node_sk_label new_st_ts.tree group_id `can_flow tr` get_label tr commit_secret
    )
    | _, _ -> True
  ))
let process_commit_proof #invs #group_id #leaf_ind tr me st_ts st_tk #li p excluded_leaves group_context pend token =
  path_filtering_ok_update_path_to_treekem st_ts.tree p;
  path_filtering_ok_treesync_to_treekem st_ts.tree (update_path_to_treekem p);
  reveal_opaque (`%TK.commit) (TK.commit st_tk (update_path_to_treekem p) excluded_leaves group_context);
  match TS.finalize_commit pend token, TK.commit st_tk (update_path_to_treekem p) excluded_leaves group_context with
  | Success new_st_ts, Success (new_st_tk, commit_secret) -> (
    pend.can_commit_proof;
    assert(new_st_ts.tree == Success?.v (MLS.TreeSync.Operations.apply_path st_ts.tree (update_path_to_treesync p)));
    assert(new_st_tk.TKT.tree == (MLS.TreeKEM.Operations.tree_apply_path st_tk.tree (update_path_to_treekem p)));
    pathsync_pathkem_rel_update_path_to_treeX p;
    apply_path_treesync_treekem_rel st_ts.tree st_tk.tree (update_path_to_treesync p) (update_path_to_treekem p);
    let un_added_tree = un_add st_tk.tree excluded_leaves in
    treekem_invariant_un_add st_tk.tree excluded_leaves;
    treekem_priv_invariant_un_add st_tk.tree st_tk.priv excluded_leaves;
    weaken_path_filtering_ok st_tk.tree (update_path_to_treekem p);
    path_filtering_weak_ok_un_add st_tk.tree (update_path_to_treekem p) excluded_leaves;
    get_path_secret_proof me un_added_tree st_tk.priv (update_path_to_treekem p) group_context tr;

    let Success (path_secret, least_common_ancestor_level) = get_path_secret un_added_tree st_tk.priv (update_path_to_treekem p) group_context in
    let new_tree = tree_apply_path st_tk.tree (update_path_to_treekem p) in
    path_apply_path_proof me new_tree st_tk.priv path_secret least_common_ancestor_level tr;

    path_filtering_ok_update_path_to_treesync st_ts.tree p;
    is_above_treesync_root_apply_path st_ts.tree (update_path_to_treesync p);
    committer_exists_tree_apply_path st_tk.tree (update_path_to_treekem p);
    prove_all_tree_keys_good tr me new_st_ts.tree new_st_ts.tokens group_id;
    get_path_secret_find_lca_eq un_added_tree st_tk.priv (update_path_to_treekem p) group_context;
    path_apply_path_commit_secret_proof me new_st_ts.tree new_tree st_tk.priv path_secret li group_id tr;
    ()
  )
  | _, _ -> ()
#pop-options

val prepare_create_commit_rand_good:
  {|crypto_invariants|} ->
  trace -> principal ->
  randomness bytes (prepare_create_commit_entropy_lengths bytes) -> path_secret_usage ->
  prop
let prepare_create_commit_rand_good tr me rand_prepare path_usages =
  let leaf_sk, rand_prepare = dest_randomness rand_prepare in
  let path_secret_0, rand_prepare = dest_randomness rand_prepare in
  bytes_invariant tr leaf_sk /\
  get_label tr leaf_sk `equivalent tr` (node_key_label me (hpke_pk leaf_sk)) /\
  leaf_sk `has_usage tr` (node_key_usage) /\
  bytes_invariant tr path_secret_0 /\
  get_label tr path_secret_0 `equivalent tr` join (node_key_label me (hpke_pk leaf_sk)) (if Cons? path_usages then one_path_secret_usage_to_path_secret_label (List.Tot.hd path_usages) else secret) /\
  path_secret_0 `has_usage tr` (KdfExpandKey "MLS.PathSecret" (serialize _ (if Cons? path_usages then List.Tot.tl path_usages else [])))

val generate_prepare_create_commit_rand:
  principal -> path_secret_usage ->
  traceful (randomness bytes (prepare_create_commit_entropy_lengths bytes))
let generate_prepare_create_commit_rand me path_usages =
  let* leaf_sk = my_mk_rand (const (node_key_usage)) (leaf_sk_my_mk_rand_label me) (hpke_private_key_length #bytes) in
  let* path_secret_0 = mk_rand (KdfExpandKey "MLS.PathSecret" (serialize _ (if Cons? path_usages then List.Tot.tl path_usages else []))) (join (node_key_label me (hpke_pk leaf_sk)) (if Cons? path_usages then one_path_secret_usage_to_path_secret_label (List.Tot.hd path_usages) else secret)) (kdf_length #bytes) in
  assume(length leaf_sk == (hpke_private_key_length #bytes));
  assume(length path_secret_0 == (kdf_length #bytes));
  DY.Core.return (mk_randomness (leaf_sk, (mk_randomness (path_secret_0, mk_empty_randomness bytes))))

val generate_prepare_create_commit_rand_good:
  {|protocol_invariants|} ->
  me:principal -> path_usages:path_secret_usage ->
  tr:trace ->
  Lemma
  (requires trace_invariant tr)
  (ensures (
    let (rand_prepare, tr_out) = generate_prepare_create_commit_rand me path_usages tr in
    trace_invariant tr_out /\
    prepare_create_commit_rand_good tr_out me rand_prepare path_usages
  ))
let generate_prepare_create_commit_rand_good #invs me path_usages tr =
  let (leaf_sk, tr) = my_mk_rand (const (node_key_usage)) (leaf_sk_my_mk_rand_label me) (hpke_private_key_length #bytes) tr in
  let (path_secret_0, tr) = mk_rand (KdfExpandKey "MLS.PathSecret" (serialize _ (if Cons? path_usages then List.Tot.tl path_usages else []))) (join (node_key_label me (hpke_pk leaf_sk)) (if Cons? path_usages then one_path_secret_usage_to_path_secret_label (List.Tot.hd path_usages) else secret)) (kdf_length #bytes) tr in
  assume(length leaf_sk == (hpke_private_key_length #bytes));
  assume(length path_secret_0 == (kdf_length #bytes));
  dest_mk_randomness #bytes #_ #(hpke_private_key_length #bytes) #[kdf_length #bytes] (leaf_sk, (mk_randomness (path_secret_0, mk_empty_randomness bytes)));
  dest_mk_randomness #bytes #_ #(kdf_length #bytes) #[] ((path_secret_0, mk_empty_randomness bytes));
  ()

#push-options "--fuel 1 --ifuel 1"
val node_sk_label_apply_path_aux_eq:
  #l:nat -> #i:tree_index l -> #li:leaf_index l i ->
  t_before:treesync bytes tkt l i -> t_after:treesync bytes tkt l i ->
  p:pathsync bytes tkt l i li -> parent_parent_hash:bytes ->
  me:principal -> group_id:mls_bytes bytes ->
  Lemma
  (requires
    (get_path_leaf p).data.source == LNS_commit /\
    Some me == MLS.TreeSync.Symbolic.AuthService.CredentialInterpretation.credential_to_principal (get_path_leaf p).data.credential /\
    Success t_after = MLS.TreeSync.Operations.apply_path_aux t_before p parent_parent_hash
  )
  (ensures
    (join (node_key_label me ((get_path_leaf p).data.content)) (node_sk_label_nocommitter t_before group_id li)) == (node_sk_label_nosig t_after group_id li)
  )
let rec node_sk_label_apply_path_aux_eq #l #i #li t_before t_after p parent_parent_hash me group_id =
  match t_before, p with
  | TLeaf _, PLeaf _ -> ()
  | TNode _ left right, PNode opt_ext_content p_next -> (
    let (child, sibling) = get_child_sibling t_before li in
    let Success (_, new_parent_parent_hash) = MLS.TreeSync.Operations.compute_new_np_and_ph opt_ext_content sibling parent_parent_hash in
    let Success child_after = MLS.TreeSync.Operations.apply_path_aux child p_next new_parent_parent_hash in
    node_sk_label_apply_path_aux_eq child child_after p_next new_parent_parent_hash me group_id;

    let l1 = (node_key_label me ((get_path_leaf p).data.content)) in
    let l2 = (node_sk_label_nocommitter left group_id li) in
    let l3 = (node_sk_label_nocommitter right group_id li) in
    if is_left_leaf li then (
      node_sk_label_noX_eq_node_sk_label right group_id li;
      join_associative l1 l2 l3
    ) else (
      node_sk_label_noX_eq_node_sk_label left group_id li;
      join_commutes l2 l3;
      join_associative l1 l3 l2;
      join_commutes (join l1 l3) l2
    )
  )
#pop-options

val node_sk_label_apply_path_eq:
  #l:nat -> #li:leaf_index l 0 ->
  t_before:treesync bytes tkt l 0 -> t_after:treesync bytes tkt l 0 ->
  p:pathsync bytes tkt l 0 li ->
  me:principal -> group_id:mls_bytes bytes ->
  Lemma
  (requires
    (get_path_leaf p).data.source == LNS_commit /\
    Some me == MLS.TreeSync.Symbolic.AuthService.CredentialInterpretation.credential_to_principal (get_path_leaf p).data.credential /\
    Success t_after = MLS.TreeSync.Operations.apply_path t_before p
  )
  (ensures
    (join (node_key_label me ((get_path_leaf p).data.content)) (node_sk_label_nocommitter t_before group_id li)) == (node_sk_label_nosig t_after group_id li)
  )
let node_sk_label_apply_path_eq #l #li t_before t_after p me group_id =
  node_sk_label_apply_path_aux_eq t_before t_after p empty me group_id

#push-options "--fuel 0 --ifuel 1"
val pre_pathkem_correct_implies_treesync_invariants_aux:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l ->
  opt_ext_content:option (tkt.node_content) -> sibling:treesync bytes tkt l i -> parent_parent_hash:bytes ->
  Lemma
  (
    match compute_new_np_and_ph opt_ext_content sibling parent_parent_hash with
    | Success (_, new_parent_parent_hash) ->
      (new_parent_parent_hash = MLS.TreeSync.ParentHash.root_parent_hash #bytes)
      <==>
      ((parent_parent_hash = MLS.TreeSync.ParentHash.root_parent_hash #bytes) /\ opt_ext_content == None)
    | _ -> True
  )
let pre_pathkem_correct_implies_treesync_invariants_aux #bytes #cb #tkt #l #i opt_ext_content sibling parent_parent_hash =
  FStar.Classical.forall_intro (hash_output_length_bound #bytes)
#pop-options

#push-options "--fuel 1 --ifuel 1 --z3rlimit 100"
val pre_pathkem_correct_implies_treesync_invariants_aux_one_tree:
  {|crypto_invariants|} ->
  #l:pos -> #i:tree_index l -> #li:leaf_index l i ->
  me:principal -> ts:treesync bytes tkt l i -> ps:pathsync bytes tkt l i li -> pre_path:pre_pathkem bytes l i li -> group_id:mls_bytes bytes ->
  parent_parent_hash:bytes ->
  tr:trace ->
  Lemma
  (requires (
    Some? (PNode?.data pre_path) /\
    pathsync_pre_pathkem_rel ps pre_path /\
    pre_pathkem_correct me (parent_parent_hash = MLS.TreeSync.ParentHash.root_parent_hash #bytes) ts pre_path group_id tr /\
    (Success? (apply_path_aux ts ps parent_parent_hash)) /\
    MLS.TreeSync.Symbolic.AuthService.CredentialInterpretation.credential_to_principal (get_path_leaf ps).data.credential == Some me /\
    (get_path_leaf ps).data.source == LNS_commit
  ))
  (ensures
    MLS.TreeSync.Symbolic.API.tree_event_pre tr group_has_tree_event_pred me group_id li (|l, i, (Success?.v (apply_path_aux ts ps parent_parent_hash))|)
  )
let pre_pathkem_correct_implies_treesync_invariants_aux_one_tree #cinvs #l #i #li me ts ps pre_path group_id parent_parent_hash tr =
  node_sk_label_apply_path_aux_eq ts (Success?.v (apply_path_aux ts ps parent_parent_hash)) ps parent_parent_hash me group_id;
  get_path_leaf_pathsync_pre_pathkem_rel ps pre_path;
  MLS.TreeSync.Invariants.ParentHash.Proofs.un_add_empty (Success?.v (apply_path_aux ts ps parent_parent_hash))
#pop-options

#push-options "--fuel 1 --ifuel 1 --z3rlimit 200"
val pre_pathkem_correct_implies_treesync_invariants:
  {|crypto_invariants|} ->
  #l:nat -> #i:tree_index l -> #li:leaf_index l i ->
  me:principal -> ts:treesync bytes tkt l i -> ps:pathsync bytes tkt l i li -> pre_path:pre_pathkem bytes l i li -> group_id:mls_bytes bytes ->
  parent_parent_hash:bytes ->
  tr:trace ->
  Lemma
  (requires
    pathsync_pre_pathkem_rel ps pre_path /\
    pre_pathkem_correct me (parent_parent_hash = MLS.TreeSync.ParentHash.root_parent_hash #bytes) ts pre_path group_id tr /\
    (Success? (apply_path_aux ts ps parent_parent_hash)) /\
    MLS.TreeSync.Symbolic.AuthService.CredentialInterpretation.credential_to_principal (get_path_leaf ps).data.credential == Some me /\
    (get_path_leaf ps).data.source == LNS_commit
  )
  (ensures (
    MLS.TreeSync.Proofs.ParentHashGuarantees.path_to_tree_list_pre_aux (MLS.TreeSync.Symbolic.API.tree_event_pre tr group_has_tree_event_pred me group_id li) ts ps parent_parent_hash ()
  ))
let rec pre_pathkem_correct_implies_treesync_invariants #cinvs #l #i #li me ts ps pre_path group_id parent_parent_hash tr =
  if l = 0 then ()
  else (
    let PNode opt_ext_content ps_next = ps in
    let PNode _ pre_next = pre_path in
    let (child, sibling) = get_child_sibling ts li in
    let Success (_, new_parent_parent_hash) = compute_new_np_and_ph opt_ext_content sibling parent_parent_hash in

    pre_pathkem_correct_implies_treesync_invariants_aux opt_ext_content sibling parent_parent_hash;
    pre_pathkem_correct_implies_treesync_invariants me child ps_next pre_next group_id new_parent_parent_hash tr;
    FStar.Pure.BreakVC.break_vc ();
    match opt_ext_content with
    | None -> ()
    | Some node_pk -> (
      pre_pathkem_correct_implies_treesync_invariants_aux_one_tree me ts ps pre_path group_id parent_parent_hash tr
    )
  )
#pop-options

val pathsync_pre_pathkem_rel_external_path_to_path_nosig:
  #l:nat -> #i:tree_index l -> #li:leaf_index l i ->
  t:treesync bytes tkt l i -> ps:external_pathsync bytes tkt l i li{(get_path_leaf ps).source == LNS_update} -> pk:pre_pathkem bytes l i li ->
  Lemma
  (requires external_pathsync_pre_pathkem_rel ps pk)
  (ensures (
    match external_path_to_path_nosig t ps with
    | Success res -> pathsync_pre_pathkem_rel res pk
    | _ -> True
  ))
let pathsync_pre_pathkem_rel_external_path_to_path_nosig #l #i #li t ps pk =
  match external_path_to_path_aux_nosig t ps with
  | Success ln -> (
    get_path_leaf_external_pathsync_pre_pathkem_rel ps pk;
    pathsync_pre_pathkem_rel_external_path_to_path_aux ln ps pk
  )
  | _ -> ()

val credential_get_path_leaf_external_path_to_path_nosig:
  #l:nat -> #i:tree_index l -> #li:leaf_index l i ->
  t:treesync bytes tkt l i -> p:external_pathsync bytes tkt l i li{(get_path_leaf p).source == LNS_update} ->
  Lemma (
    match external_path_to_path_nosig t p with
    | Success res -> (get_path_leaf res).data.credential == (get_path_leaf p).credential
    | _ -> True
  )
let credential_get_path_leaf_external_path_to_path_nosig #l #i #li t p =
  match external_path_to_path_aux_nosig t p with
  | Success ln -> (
    get_path_leaf_set_path_leaf p ln
  )
  | _ -> ()

val external_path_to_path_succeeds_implies:
  #l:nat -> #i:tree_index l -> #li:leaf_index l i ->
  t:treesync bytes tkt l i -> p:external_pathsync bytes tkt l i li{(get_path_leaf p).source == LNS_update} -> group_id:mls_bytes bytes -> sign_key:bytes -> nonce:sign_nonce bytes ->
  Lemma
  (requires Success? (external_path_to_path t p group_id sign_key nonce))
  (ensures Success? (external_path_to_path_nosig t p) /\ li < pow2 32)
let external_path_to_path_succeeds_implies #l #i #li t p group_id sign_key nonce = ()

#push-options "--fuel 1 --ifuel 1 --z3rlimit 50"
val treekem_to_treesync_lemmas_bis:
  {|crypto_invariants|} ->
  #l:nat -> #i:tree_index l -> #li:leaf_index l i ->
  me:principal -> is_at_root:bool -> t:treesync bytes tkt l i ->
  ln_data:leaf_node_data_nt bytes tkt -> p:pre_pathkem bytes l i li ->
  group_id:mls_bytes bytes ->
  tr:trace ->
  Lemma
  (requires
    is_well_formed_prefix (ps_leaf_node_data_nt tkt) (is_publishable tr) ln_data /\
    pre_pathkem_correct me is_at_root t p group_id tr
  )
  (ensures (
    match treekem_to_treesync ln_data p with
    | Success external_path ->
      MLS.TreeSync.Operations.path_is_filter_valid t external_path /\
      is_well_formed _ (is_publishable tr) external_path
    | _ -> True
  ))
let rec treekem_to_treesync_lemmas_bis #cinvs #l #i #li me is_at_root t ln_data p group_id tr =
  match p with
  | PLeaf _ -> ()
  | PNode opt_ps p_next -> (
    let (child, sibling) = get_child_sibling t li in
    treekem_to_treesync_lemmas_bis me (is_at_root && opt_ps = None) child ln_data p_next group_id tr
  )
#pop-options

val pending_commit_good:
  {|crypto_invariants|} ->
  #group_id:mls_bytes bytes -> #leaf_ind:nat ->
  tr:trace -> me:principal ->
  st_ts:treesync_state bytes tkt dy_as_token group_id -> st_tk:treekem_tree_state bytes leaf_ind ->
  tk_pend:TK.pending_commit st_tk ->
  prop
let pending_commit_good #cinvs #group_id #leaf_ind tr me st_ts st_tk tk_pend =
  st_ts.levels == st_tk.levels /\
  path_secrets_are_correct me true st_ts.tree group_id tk_pend.path_secrets tr /\
  bytes_invariant tr tk_pend.commit_secret /\
  get_label tr tk_pend.commit_secret `equivalent tr` join (node_key_label me (hpke_pk (get_path_leaf tk_pend.path_secrets))) ((node_sk_label_nocommitter st_ts.tree group_id leaf_ind))

#push-options "--z3rlimit 25"
val prepare_create_commit_proof:
  {|protocol_invariants|} ->
  #group_id:mls_bytes bytes -> #leaf_ind:nat ->
  tr:trace -> me:principal ->
  st_ts:treesync_state bytes tkt dy_as_token group_id -> st_tk:treekem_tree_state bytes leaf_ind{st_ts.levels == st_tk.levels} ->
  rand_prepare:randomness bytes (prepare_create_commit_entropy_lengths bytes) ->
  ln_data:leaf_node_data_nt bytes tkt ->
  Lemma
  (requires
    ln_data.source == LNS_update /\
    MLS.TreeSync.Symbolic.AuthService.CredentialInterpretation.credential_to_principal ln_data.credential == Some me /\
    is_well_formed_prefix (ps_leaf_node_data_nt tkt) (is_publishable tr) ln_data /\

    //// various treesync / treekem invariants
    treesync_treekem_state_rel st_ts st_tk /\
    treekem_tree_state_invariant tr me st_tk /\

    //// post-conditions from random generation
    prepare_create_commit_rand_good tr me rand_prepare (compute_path_secret_usage st_ts.tree group_id leaf_ind []) /\

    trace_invariant tr /\
    has_mls_treekem_invariants /\
    has_treesync_treekem_link_invariants
  )
  (ensures (
    match TK.prepare_create_commit st_tk rand_prepare with
    | Success (pend, pre_path) -> (
      pending_commit_good tr me st_ts st_tk pend /\ (
        match treekem_to_treesync ln_data pre_path with
        | Success external_path -> (
          (get_path_leaf external_path) == ({ ln_data with content = (get_path_leaf external_path).content } <: leaf_node_data_nt bytes tkt) /\
          MLS.TreeSync.Symbolic.API.external_path_has_event_pre leaf_node_signed_event_pred group_has_tree_event_pred tr me st_ts.tree external_path group_id /\
          MLS.TreeSync.Operations.path_is_filter_valid st_ts.tree external_path /\
          is_well_formed _ (is_publishable tr) external_path /\
          external_pathsync_path_secrets_rel external_path pend.path_secrets
        )
        | _ -> True
      )
    )
    | _ -> True
  ))
let prepare_create_commit_proof #invs #group_id #leaf_ind tr me st_ts st_tk rand_prepare ln_data =
  match TK.prepare_create_commit st_tk rand_prepare with
  | Success (pend, pre_path) -> (
    reveal_opaque (`%TK.prepare_create_commit) (TK.prepare_create_commit st_tk rand_prepare);
    let leaf_sk, rand_prepare = dest_randomness rand_prepare in
    let path_secret_0, rand_prepare = dest_randomness rand_prepare in
    let Success (path_secrets, commit_secret) = generate_path_secrets st_tk.tree leaf_sk path_secret_0 leaf_ind in
    generate_path_secrets_proof me st_ts.tree st_tk.tree leaf_sk path_secret_0 leaf_ind group_id tr [];
    path_secrets_to_pre_pathkem_proof me true st_ts.tree path_secrets group_id tr;

    match treekem_to_treesync ln_data pre_path with
    | Success external_path -> (
      treekem_to_treesync_lemmas ln_data pre_path;
      treekem_to_treesync_lemmas_bis me true st_ts.tree ln_data pre_path group_id tr;
      if not (Success? (external_path_to_path_nosig st_ts.tree external_path) && leaf_ind < pow2 32) then ()
      else (
        let Success auth_p = external_path_to_path_nosig st_ts.tree external_path in
        let auth_ln = get_path_leaf auth_p in

        path_is_parent_hash_valid_external_path_to_path_nosig st_ts.tree external_path;
        apply_path_aux_compute_leaf_parent_hash_from_path_both_succeed st_ts.tree auth_p (MLS.TreeSync.ParentHash.root_parent_hash #bytes);
        assert(leaf_node_signed_event_pred tr me ({ln_tbs = {data = auth_ln.data; group_id; leaf_index = leaf_ind;}}));
        pathsync_pre_pathkem_rel_external_path_to_path_nosig st_ts.tree external_path pre_path;
        credential_get_path_leaf_external_path_to_path_nosig st_ts.tree external_path;
        pre_pathkem_correct_implies_treesync_invariants me st_ts.tree auth_p pre_path group_id (MLS.TreeSync.ParentHash.root_parent_hash #bytes) tr;
        assert(MLS.TreeSync.Proofs.ParentHashGuarantees.path_to_tree_list_pre (MLS.TreeSync.Symbolic.API.tree_event_pre tr group_has_tree_event_pred me group_id leaf_ind) st_ts.tree auth_p ());
        ()
      )
    )
    | _ -> ()
  )
  | _ -> ()
#pop-options

#push-options "--z3rlimit 25"
val create_commit_proof:
  {|protocol_invariants|} ->
  #group_id:mls_bytes bytes -> #leaf_ind:nat ->
  tr:trace -> me:principal ->
  st_ts:treesync_state bytes tkt dy_as_token group_id -> st_tk:treekem_tree_state bytes leaf_ind{st_ts.levels == st_tk.levels} ->
  tk_pend:TK.pending_commit st_tk ->
  added_leaves:list nat -> group_context:group_context_nt bytes ->
  rand_finalize:randomness bytes (finalize_create_commit_entropy_lengths st_tk added_leaves) ->
  auth_path:pathsync bytes tkt st_ts.levels 0 leaf_ind ->
  ts_pend:TS.pending_commit st_ts auth_path -> token:dy_as_token ->
  Lemma
  (requires
    (get_path_leaf auth_path).data.source == LNS_commit /\
    Some me == MLS.TreeSync.Symbolic.AuthService.CredentialInterpretation.credential_to_principal (get_path_leaf auth_path).data.credential /\

    // post-condition of prepare_create_commit_proof
    pending_commit_good tr me st_ts st_tk tk_pend /\
    (hpke_pk (get_path_leaf tk_pend.path_secrets)) == (get_path_leaf auth_path).data.content /\

    // various treesync / treekem invariants
    extended_treesync_invariant tr me st_ts /\
    treesync_treekem_state_rel st_ts st_tk /\

    // easy bytes invariants
    is_well_formed _ (bytes_invariant tr) group_context /\
    bytes_invariant tr group_id /\

    // post-condition from random generation
    rand_finalize `randomness_has_ghost_data tr` (encrypt_path_secrets_entropy_ghost_data st_ts.tree st_tk.tree (forget_path_secrets tk_pend.path_secrets) group_id (excluded_pre added_leaves)) /\

    trace_invariant tr /\
    has_mls_treekem_invariants /\
    has_treesync_treekem_link_invariants
  )
  (ensures (
    match TS.finalize_commit ts_pend token, TK.finalize_create_commit tk_pend added_leaves group_context rand_finalize with
    | Success ts_res, Success tk_res -> (
      pathkem_good tk_res.update_path tr /\
      treekem_tree_state_invariant tr me tk_res.new_state /\
      bytes_invariant tr tk_res.commit_secret /\
      (get_label tr tk_res.commit_secret) `equivalent tr` (node_sk_label_nosig ts_res.tree group_id leaf_ind) /\
      (path_secrets_good_for_joiners tr st_ts.tree group_id added_leaves tk_res.added_leaves_path_secrets)
    )
    | _ -> True
  ))
let create_commit_proof #invs #group_id #leaf_ind tr me st_ts st_tk tk_pend added_leaves group_context rand_finalize auth_path ts_pend token =
  reveal_opaque (`%TK.finalize_create_commit) (TK.finalize_create_commit tk_pend added_leaves group_context rand_finalize);
  match TS.finalize_commit ts_pend token, TK.finalize_create_commit tk_pend added_leaves group_context rand_finalize with
  | Success ts_res, Success tk_res -> (
    prove_all_tree_keys_good tr me st_ts.tree st_ts.tokens group_id;
    treekem_invariant_un_add st_tk.tree added_leaves;
    encrypt_path_secrets_pub_proof me true st_ts.tree st_tk.tree tk_pend.path_secrets group_context group_id (excluded_pre added_leaves) rand_finalize tr;
    encrypt_path_secrets_priv_proof me true st_ts.tree (un_add st_tk.tree added_leaves) tk_pend.path_secrets group_context group_id rand_finalize tr;
    assert(get_label tr tk_pend.commit_secret `equivalent tr` (join (node_key_label me (hpke_pk (get_path_leaf tk_res.new_state.priv))) (node_sk_label_nocommitter st_ts.tree group_id leaf_ind)));
    assert(ts_res.tree == Success?.v (MLS.TreeSync.Operations.apply_path st_ts.tree auth_path));
    assert(tk_res.new_state.TKT.tree == (MLS.TreeKEM.Operations.tree_apply_path st_tk.tree tk_res.update_path));
    assert( Success ts_res.tree = MLS.TreeSync.Operations.apply_path st_ts.tree auth_path) by (let open FStar.Tactics in set_ifuel 1);
    node_sk_label_apply_path_eq st_ts.tree ts_res.tree auth_path me group_id;
    get_path_secret_of_added_leaves_proof me st_ts.tree tk_pend.path_secrets added_leaves group_id tr
  )
  | _ -> ()
#pop-options
