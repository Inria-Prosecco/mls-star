module MLS.TreeSyncTreeKEMBinder.Proofs

open Comparse
open MLS.TreeSyncTreeKEMBinder
open MLS.TreeSyncTreeKEMBinder.Properties
open MLS.Crypto
open MLS.NetworkTypes
open MLS.TreeSync.NetworkTypes
open MLS.TreeKEM.NetworkTypes
open MLS.TreeSync.API.Types
open MLS.TreeKEM.API.Tree.Types
open MLS.NetworkBinder
open MLS.NetworkBinder.Properties
open MLS.Tree
open MLS.TreeCommon
open MLS.TreeSync.Types
open MLS.TreeKEM.Types
open MLS.TreeSync.Symbolic.Parsers
open MLS.TreeKEM.Parsers
open MLS.Result

module TS_ops = MLS.TreeSync.Operations
module TK_ops = MLS.TreeKEM.Operations
module TS_API = MLS.TreeSync.API
module TK_API = MLS.TreeKEM.API.Tree

#set-options "--fuel 1 --ifuel 1"

val is_tree_empty_treesync_to_treekem:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #l:nat -> #i:tree_index l ->
  t:treesync bytes tkt l i ->
  Lemma
  (ensures is_tree_empty t <==> is_tree_empty (treesync_to_treekem t))
let rec is_tree_empty_treesync_to_treekem #l #i t =
  match t with
  | TLeaf _ -> ()
  | TNode _ left right ->
    is_tree_empty_treesync_to_treekem left;
    is_tree_empty_treesync_to_treekem right

val treesync_treekem_rel_is_tree_empty:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #l:nat -> #i:tree_index l ->
  ts:treesync bytes tkt l i -> tk:treekem bytes l i ->
  Lemma
  (requires ts `treesync_treekem_rel` tk)
  (ensures is_tree_empty ts <==> is_tree_empty tk)
let treesync_treekem_rel_is_tree_empty #l #i ts tk =
  is_tree_empty_treesync_to_treekem ts

val path_filtering_ok_treesync_to_treekem:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #l:nat -> #i:tree_index l -> #li:leaf_index l i ->
  #path_leaf_t:Type -> #path_node_t:Type ->
  t:treesync bytes tkt l i ->
  p:path path_leaf_t (option path_node_t) l i li ->
  Lemma
  (path_filtering_ok t p <==> path_filtering_ok (treesync_to_treekem t) p)
let rec path_filtering_ok_treesync_to_treekem #bytes #cb #l #i #li t p =
  match t, p with
  | TLeaf _, PLeaf _ -> ()
  | TNode _ _ _, PNode _ p_next ->
    let (child, sibling) = get_child_sibling t li in
    path_filtering_ok_treesync_to_treekem child p_next;
    is_tree_empty_treesync_to_treekem sibling

val get_path_leaf_external_pathsync_pre_pathkem_rel:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #l:nat -> #i:tree_index l -> #li:leaf_index l i ->
  ps:external_pathsync bytes tkt l i li -> pk:pre_pathkem bytes l i li ->
  Lemma
  (requires external_pathsync_pre_pathkem_rel ps pk)
  (ensures (get_path_leaf ps).content == (get_path_leaf pk).public_key)
let rec get_path_leaf_external_pathsync_pre_pathkem_rel #bytes #cb #l #i #li ps pk =
  match ps, pk with
  | PLeaf lns, PLeaf lnk -> ()
  | PNode opt_pns ps_next, PNode opt_pnk pk_next ->
    get_path_leaf_external_pathsync_pre_pathkem_rel ps_next pk_next

val get_path_leaf_pathsync_pre_pathkem_rel:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #l:nat -> #i:tree_index l -> #li:leaf_index l i ->
  ps:pathsync bytes tkt l i li -> pk:pre_pathkem bytes l i li ->
  Lemma
  (requires pathsync_pre_pathkem_rel ps pk)
  (ensures (get_path_leaf ps).data.content == (get_path_leaf pk).public_key)
let rec get_path_leaf_pathsync_pre_pathkem_rel #bytes #cb #l #i #li ps pk =
  match ps, pk with
  | PLeaf lns, PLeaf lnk -> ()
  | PNode opt_pns ps_next, PNode opt_pnk pk_next ->
    get_path_leaf_pathsync_pre_pathkem_rel ps_next pk_next

val pathsync_pathkem_rel_update_path_to_treeX:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #l:nat -> #i:tree_index l -> #li:leaf_index l i ->
  p:sparse_update_path bytes l i li ->
  Lemma
  (pathsync_pathkem_rel (update_path_to_treesync p) (update_path_to_treekem p))
let rec pathsync_pathkem_rel_update_path_to_treeX #l #i #li p =
  match p with
  | PLeaf _ -> ()
  | PNode _ p_next -> pathsync_pathkem_rel_update_path_to_treeX p_next

val treekem_to_treesync_lemmas:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #l:nat -> #i:tree_index l -> #li:leaf_index l i ->
  ln_data:leaf_node_data_nt bytes tkt -> p:pre_pathkem bytes l i li ->
  Lemma (
    match treekem_to_treesync ln_data p with
    | Success res ->
      length (get_path_leaf p).public_key < pow2 30 /\
      get_path_leaf res == ({ ln_data with content = (get_path_leaf p).public_key }  <: leaf_node_data_nt bytes tkt) /\
      external_pathsync_pre_pathkem_rel res p
    | _ -> True
  )
let rec treekem_to_treesync_lemmas #bytes #cb #l #i #li ln_data p =
  match p with
  | PLeaf _ -> ()
  | PNode _ p_next -> treekem_to_treesync_lemmas ln_data p_next

(*** treesync_treekem_rel preservation lemmas ***)

val tree_create_treesync_treekem_rel:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  ln_s:leaf_node_nt bytes tkt -> ln_k:treekem_leaf bytes ->
  Lemma
  (requires ln_s.data.content == ln_k.public_key)
  (ensures tree_create ln_s `treesync_treekem_rel` tree_create ln_k)
let tree_create_treesync_treekem_rel #bytes #cb ln_s ln_k = ()

val tree_add_treesync_treekem_rel_aux:
  li:nat_lbytes 4 -> l:list (nat_lbytes 4) ->
  Lemma
  (List.Tot.map nat_lbytes_to_nat (insert_sorted li l) == insert_sorted li (List.Tot.map nat_lbytes_to_nat l))
let rec tree_add_treesync_treekem_rel_aux li l =
  match l with
  | [] -> ()
  | h::t -> tree_add_treesync_treekem_rel_aux li t

#push-options "--z3rlimit 25"
val tree_add_treesync_treekem_rel:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #l:nat -> #i:tree_index l ->
  ts:treesync bytes tkt l i -> li:leaf_index l i -> ln_s:leaf_node_nt bytes tkt ->
  tk:treekem bytes l i -> ln_k:treekem_leaf bytes ->
  Lemma
  (requires
    ts `treesync_treekem_rel` tk /\
    ln_s.data.content == ln_k.public_key
  )
  (ensures (
    match TS_ops.tree_add ts li ln_s, TK_ops.tree_add tk li ln_k with
    | Success res_s, res_k ->
      res_s `treesync_treekem_rel` res_k
    | _, _ -> True
  ))
let rec tree_add_treesync_treekem_rel #bytes #cb #l #i ts li ln_s tk ln_k =
  if l = 0 then ()
  else (
    let (child_s, sibling_s) = get_child_sibling ts li in
    let (child_k, sibling_k) = get_child_sibling tk li in
    tree_add_treesync_treekem_rel child_s li ln_s child_k ln_k;
    match TNode?.data ts with
    | None -> ()
    | Some pn -> (
      if not (Success? (TS_ops.tree_add ts li ln_s)) then ()
      else (
        tree_add_treesync_treekem_rel_aux li pn.unmerged_leaves
      )
    )
  )
#pop-options

val tree_update_treesync_treekem_rel:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #l:nat -> #i:tree_index l ->
  ts:treesync bytes tkt l i -> tk:treekem bytes l i ->
  ln_s:leaf_node_nt bytes tkt -> ln_k:treekem_leaf bytes ->
  li:leaf_index l i ->
  Lemma
  (requires
    ln_s.data.content == ln_k.public_key /\
    ts `treesync_treekem_rel` tk
  )
  (ensures (tree_update ts li ln_s) `treesync_treekem_rel` (tree_update tk li ln_k))
let rec tree_update_treesync_treekem_rel #bytes #cb #l #i ts tk ln_s ln_k li =
  if l = 0 then ()
  else (
    let (child_s, _) = get_child_sibling ts li in
    let (child_k, _) = get_child_sibling tk li in
    tree_update_treesync_treekem_rel child_s child_k ln_s ln_k li
  )

val tree_remove_treesync_treekem_rel:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #l:nat -> #i:tree_index l ->
  ts:treesync bytes tkt l i -> tk:treekem bytes l i ->
  li:leaf_index l i ->
  Lemma
  (requires ts `treesync_treekem_rel` tk)
  (ensures (tree_remove ts li) `treesync_treekem_rel` (tree_remove tk li))
let rec tree_remove_treesync_treekem_rel #bytes #cb #l #i ts tk li =
  if l = 0 then ()
  else (
    let (child_s, _) = get_child_sibling ts li in
    let (child_k, _) = get_child_sibling tk li in
    tree_remove_treesync_treekem_rel child_s child_k li
  )

#push-options "--z3rlimit 50"
val apply_path_aux_treesync_treekem_rel:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #l:nat -> #i:tree_index l -> #li:leaf_index l i ->
  ts:treesync bytes tkt l i -> tk:treekem bytes l i ->
  ps:pathsync bytes tkt l i li -> pk:pathkem bytes l i li ->
  parent_parent_hash:bytes ->
  Lemma
  (requires
    treesync_treekem_rel ts tk /\
    pathsync_pathkem_rel ps pk
  )
  (ensures (
    match TS_ops.apply_path_aux ts ps parent_parent_hash, TK_ops.tree_apply_path tk pk with
    | Success res_ts, res_tk -> treesync_treekem_rel res_ts res_tk
    | _, _ -> True
  ))
let rec apply_path_aux_treesync_treekem_rel #bytes #cb #l #i #li ts tk ps pk parent_parent_hash =
  if l = 0 then ()
  else (
    if Success? (MLS.TreeSync.Operations.apply_path_aux ts ps parent_parent_hash) then
      let (child_s, sibling_s) = get_child_sibling ts li in
      let (child_k, _) = get_child_sibling tk li in
      let Success (_, new_parent_parent_hash) = MLS.TreeSync.Operations.compute_new_np_and_ph (PNode?.data ps) sibling_s parent_parent_hash in
      apply_path_aux_treesync_treekem_rel child_s child_k (PNode?.next ps) (PNode?.next pk) new_parent_parent_hash
  )
#pop-options

val apply_path_treesync_treekem_rel:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #l:nat -> #li:leaf_index l 0 ->
  ts:treesync bytes tkt l 0 -> tk:treekem bytes l 0 ->
  ps:pathsync bytes tkt l 0 li -> pk:pathkem bytes l 0 li ->
  Lemma
  (requires
    treesync_treekem_rel ts tk /\
    pathsync_pathkem_rel ps pk
  )
  (ensures (
    match TS_ops.apply_path ts ps, TK_ops.tree_apply_path tk pk with
    | Success res_ts, res_tk -> treesync_treekem_rel res_ts res_tk
    | _, _ -> True
  ))
let apply_path_treesync_treekem_rel #bytes #cb #l #li ts tk ps pk =
  apply_path_aux_treesync_treekem_rel ts tk ps pk (MLS.TreeSync.ParentHash.root_parent_hash #bytes)

val mk_blank_tree_treesync_treekem_rel:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  l:nat -> i:tree_index l ->
  Lemma
  (treesync_treekem_rel (mk_blank_tree l i <: treesync bytes tkt l i) (mk_blank_tree l i <: treekem bytes l i))
let rec mk_blank_tree_treesync_treekem_rel #bytes #cb l i =
   if l = 0 then ()
   else (
     mk_blank_tree_treesync_treekem_rel #bytes (l-1) (left_index i);
     mk_blank_tree_treesync_treekem_rel #bytes (l-1) (right_index i)
   )

val tree_extend_treesync_treekem_rel:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #l:nat ->
  ts:treesync bytes tkt l 0 -> tk:treekem bytes l 0 ->
  Lemma
  (requires treesync_treekem_rel ts tk)
  (ensures treesync_treekem_rel (tree_extend ts) (tree_extend tk))
let tree_extend_treesync_treekem_rel #bytes #cb #l ts tk =
  mk_blank_tree_treesync_treekem_rel #bytes l (right_index (0 <: tree_index (l+1)))

#push-options "--fuel 1 --ifuel 1"
val pathsync_pre_pathkem_rel_external_path_to_path_aux:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #l:nat -> #i:tree_index l -> #li:leaf_index l i ->
  ln:leaf_node_nt bytes tkt -> ps:external_pathsync bytes tkt l i li{(get_path_leaf ps).source == LNS_update} -> pk:pre_pathkem bytes l i li ->
  Lemma
  (requires
    ln.data.content == (get_path_leaf pk).public_key /\
    external_pathsync_pre_pathkem_rel ps pk
  )
  (ensures pathsync_pre_pathkem_rel (set_path_leaf ps ln) pk)
let rec pathsync_pre_pathkem_rel_external_path_to_path_aux #bytes #cb #l #i #li ln ps pk =
  match ps, pk with
  | PLeaf _, PLeaf _ -> ()
  | PNode _ ps_next, PNode _ pk_next -> (
    pathsync_pre_pathkem_rel_external_path_to_path_aux ln ps_next pk_next
  )
#pop-options

val pathsync_pre_pathkem_rel_external_path_to_path:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #l:nat -> #i:tree_index l -> #li:leaf_index l i ->
  t:treesync bytes tkt l i -> ps:external_pathsync bytes tkt l i li{(get_path_leaf ps).source == LNS_update} -> pk:pre_pathkem bytes l i li ->
  group_id:mls_bytes bytes -> sign_key:bytes -> sign_nonce:sign_nonce bytes ->
  Lemma
  (requires external_pathsync_pre_pathkem_rel ps pk)
  (ensures (
    match TS_ops.external_path_to_path t ps group_id sign_key sign_nonce with
    | Success res -> pathsync_pre_pathkem_rel res pk
    | _ -> True
  ))
let pathsync_pre_pathkem_rel_external_path_to_path #l #i #li t ps pk group_id sign_key sign_nonce =
  match TS_ops.external_path_to_path_aux t ps group_id sign_key sign_nonce with
  | Success ln -> (
    get_path_leaf_external_pathsync_pre_pathkem_rel ps pk;
    pathsync_pre_pathkem_rel_external_path_to_path_aux ln ps pk
  )
  | _ -> ()

val leaf_at_treesync_to_treekem:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #l:nat -> #i:tree_index l ->
  t:treesync bytes tkt l i -> li:leaf_index l i ->
  Lemma (
    match leaf_at t li, leaf_at (treesync_to_treekem t) li with
    | Some lns, Some lnk -> lnk == ({public_key = (lns <: leaf_node_nt bytes tkt).data.content} <: treekem_leaf bytes)
    | None, None -> True
    | _, _ -> False
  )
let rec leaf_at_treesync_to_treekem #bytes #cb #l #i t li =
  if l = 0 then ()
  else (
    let (child, sibling) = get_child_sibling t li in
    leaf_at_treesync_to_treekem child li
  )

val treesync_to_treekem_invariant:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #l:nat -> #i:tree_index l ->
  t:treesync bytes tkt l i ->
  Lemma
  (requires MLS.TreeSync.Invariants.UnmergedLeaves.unmerged_leaves_ok t)
  (ensures MLS.TreeKEM.Invariants.treekem_invariant (treesync_to_treekem t))
let rec treesync_to_treekem_invariant #bytes #cb #l #i t =
  match t with
  | TLeaf _ -> ()
  | TNode opt_pn left right -> (
    treesync_to_treekem_invariant left;
    treesync_to_treekem_invariant right;
    match opt_pn with
    | None -> ()
    | Some pn -> (
      List.Tot.for_all_mem (MLS.TreeSync.Invariants.UnmergedLeaves.unmerged_leaf_exists t) pn.unmerged_leaves;
      for_allP_eq (MLS.TreeKEM.Invariants.unmerged_leaf_exists (treesync_to_treekem t)) (List.Tot.map nat_lbytes_to_nat pn.unmerged_leaves);
      introduce forall li. List.Tot.memP li (List.Tot.map nat_lbytes_to_nat pn.unmerged_leaves) ==> (MLS.TreeKEM.Invariants.unmerged_leaf_exists (treesync_to_treekem t)) li with (
        introduce _ ==> _ with _. (
          List.Tot.memP_map_elim nat_lbytes_to_nat li pn.unmerged_leaves;
          leaf_at_treesync_to_treekem t li
        )
      )
    )
  )

#push-options "--z3rlimit 25"
val is_well_formed_treesync_to_treekem:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #l:nat -> #i:tree_index l ->
  pre:bytes_compatible_pre bytes -> t:treesync bytes tkt l i ->
  Lemma
  (requires is_well_formed _ pre t)
  (ensures is_well_formed_prefix (ps_treekem l i) pre (treesync_to_treekem t))
let rec is_well_formed_treesync_to_treekem #bytes #cb #l #i pre t =
  match t with
  | TLeaf _ -> ()
  | TNode opt_pn left right -> (
    is_well_formed_treesync_to_treekem pre left;
    is_well_formed_treesync_to_treekem pre right;
    match opt_pn with
    | None -> ()
    | Some pn ->
      for_allP_eq (is_well_formed_prefix ps_nat pre) (List.Tot.map nat_lbytes_to_nat pn.unmerged_leaves);
      assert(is_well_formed_prefix ps_treekem_node pre (treesync_to_treekem_node pn))
  )
#pop-options

(*** treesync_treekem_state_rel preservation lemmas ***)

val create_state_rel:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #token_t:Type0 ->
  #group_id:mls_bytes bytes -> #ln:leaf_node_nt bytes tkt ->
  pend:TS_API.pending_create group_id ln -> token:token_t ->
  leaf_private_key:hpke_private_key bytes -> leaf_public_key:bytes ->
  Lemma
  (requires ln.data.content == leaf_public_key)
  (ensures treesync_treekem_state_rel (TS_API.finalize_create pend token) (TK_API.create leaf_private_key leaf_public_key))
let create_state_rel #bytes #cb #token_t #group_id #ln pend token leaf_private_key leaf_public_key =
  reveal_opaque (`%TK_API.create) (TK_API.create leaf_private_key leaf_public_key);
  tree_create_treesync_treekem_rel ln {public_key = leaf_public_key}

val welcome_state_rel:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #token_t:Type0 ->
  #l:nat -> #group_id:mls_bytes bytes -> #ts:treesync bytes tkt l 0 ->
  pend:TS_API.pending_welcome group_id ts -> tokens:list (option token_t){List.Tot.length tokens == pow2 l} ->
  tk:treekem bytes l 0 -> leaf_decryption_key:hpke_private_key bytes -> opt_path_secret_and_inviter_ind:option (bytes & nat) -> leaf_ind:nat{leaf_ind < pow2 l /\ Some? (leaf_at tk leaf_ind)} ->
  Lemma
  (requires ts `treesync_treekem_rel` tk)
  (ensures
    MLS.TreeKEM.Invariants.treekem_invariant tk /\ (
    match TS_API.finalize_welcome pend tokens, TK_API.welcome tk leaf_decryption_key opt_path_secret_and_inviter_ind leaf_ind with
    | res_s, Success res_k ->
      res_s `treesync_treekem_state_rel` res_k
    | _, _ -> True
  ))
let welcome_state_rel #bytes #cb #token_t #l #group_id #ts pend tokens tk leaf_decryption_key opt_path_secret_and_inviter_ind leaf_ind =
  treesync_to_treekem_invariant ts;
  reveal_opaque (`%TK_API.welcome) (TK_API.welcome tk leaf_decryption_key opt_path_secret_and_inviter_ind leaf_ind)

val find_empty_leaf_treesync_treekem_rel:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #l:nat -> #i:tree_index l ->
  ts:treesync bytes tkt l i -> tk:treekem bytes l i ->
  Lemma
  (requires ts `treesync_treekem_rel` tk)
  (ensures (
    // can't say `==` directly because of refinement inside option
    match find_empty_leaf ts, find_empty_leaf tk with
    | Some li_s, Some li_k -> li_s == li_k
    | None, None -> True
    | _, _ -> False
  ))
let rec find_empty_leaf_treesync_treekem_rel #bytes #cb #l #i ts tk =
  match ts, tk with
  | TLeaf _, TLeaf _ -> ()
  | TNode _ left_s right_s, TNode _ left_k right_k ->
    find_empty_leaf_treesync_treekem_rel left_s left_k;
    find_empty_leaf_treesync_treekem_rel right_s right_k

#push-options "--fuel 0 --ifuel 1"
val add_state_rel:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #token_t:Type0 -> #group_id:mls_bytes bytes -> #leaf_ind:nat ->
  #st_ts:treesync_state bytes tkt token_t group_id -> #ln_s:leaf_node_nt bytes tkt ->
  pend:TS_API.pending_add st_ts ln_s -> token:token_t ->
  st_tk:treekem_tree_state bytes leaf_ind -> ln_k:treekem_leaf bytes ->
  Lemma
  (requires
    st_ts `treesync_treekem_state_rel` st_tk /\
    ln_s.data.content == ln_k.public_key
  )
  (ensures (
    match TS_API.finalize_add pend token, TK_API.add st_tk ln_k with
    | Success (res_s, li_s), (res_k, li_k) ->
      res_s `treesync_treekem_state_rel` res_k /\
      li_s == li_k
    | _, _ -> True
  ))
let add_state_rel #bytes #cb #token_t #group_id #leaf_ind #st_ts #ln_s pend token st_tk ln_k =
  reveal_opaque (`%TK_API.add) (TK_API.add st_tk ln_k);
  find_empty_leaf_treesync_treekem_rel st_ts.tree st_tk.tree;
  match find_empty_leaf st_ts.tree with
  | Some li -> (
    tree_add_treesync_treekem_rel st_ts.tree li ln_s st_tk.tree ln_k
  )
  | None -> (
    let extended_ts = tree_extend st_ts.tree in
    let extended_tk = tree_extend st_tk.tree in
    MLS.TreeCommon.Lemmas.find_empty_leaf_tree_extend st_ts.tree;
    tree_extend_treesync_treekem_rel st_ts.tree st_tk.tree;
    find_empty_leaf_treesync_treekem_rel extended_ts extended_tk;
    let li = Some?.v (find_empty_leaf extended_ts) in
    tree_add_treesync_treekem_rel extended_ts li ln_s extended_tk ln_k
  )
#pop-options

val update_myself_state_rel:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #token_t:Type0 -> #group_id:mls_bytes bytes -> #leaf_ind:nat ->
  #st_ts:treesync_state bytes tkt token_t group_id -> #ln_s:leaf_node_nt bytes tkt -> #li:treesync_index st_ts ->
  pend:TS_API.pending_update st_ts ln_s li -> token:token_t ->
  st_tk:treekem_tree_state bytes leaf_ind -> ln_k:treekem_leaf bytes -> leaf_decryption_key:hpke_private_key bytes ->
  Lemma
  (requires
    leaf_ind == li /\
    st_ts `treesync_treekem_state_rel` st_tk /\
    ln_s.data.content == ln_k.public_key
  )
  (ensures
    TS_API.finalize_update pend token
    `treesync_treekem_state_rel`
    TK_API.update_myself st_tk ln_k leaf_decryption_key
  )
let update_myself_state_rel #bytes #cb #token_t #group_id #leaf_ind #st_ts #ln_s #li pend token st_tk ln_k leaf_decryption_key =
  reveal_opaque (`%TK_API.update_myself) (TK_API.update_myself st_tk ln_k leaf_decryption_key);
  tree_update_treesync_treekem_rel st_ts.tree st_tk.tree ln_s ln_k li

val update_other_state_rel:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #token_t:Type0 -> #group_id:mls_bytes bytes -> #leaf_ind:nat ->
  #st_ts:treesync_state bytes tkt token_t group_id -> #ln_s:leaf_node_nt bytes tkt -> #li:treesync_index st_ts ->
  pend:TS_API.pending_update st_ts ln_s li -> token:token_t ->
  st_tk:treekem_tree_state bytes leaf_ind -> ln_k:treekem_leaf bytes -> i:treekem_index st_tk{i <> leaf_ind} ->
  Lemma
  (requires
    i == li /\
    st_ts `treesync_treekem_state_rel` st_tk /\
    ln_s.data.content == ln_k.public_key
  )
  (ensures
    TS_API.finalize_update pend token
    `treesync_treekem_state_rel`
    TK_API.update_other st_tk ln_k i
  )
let update_other_state_rel #bytes #cb #token_t #group_id #leaf_ind #st_ts #ln_s #li pend token st_tk ln_k i =
  reveal_opaque (`%TK_API.update_other) (TK_API.update_other st_tk ln_k i);
  tree_update_treesync_treekem_rel st_ts.tree st_tk.tree ln_s ln_k li

val fully_truncate_state_rel:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #token_t:Type0 ->
  #group_id:mls_bytes bytes -> #leaf_ind:nat ->
  st_ts:treesync_state bytes tkt token_t group_id -> st_tk:treekem_tree_state bytes leaf_ind ->
  Lemma
  (requires st_ts `treesync_treekem_state_rel` st_tk)
  (ensures TS_API.fully_truncate_state st_ts `treesync_treekem_state_rel` TK_API.fully_truncate st_tk)
  (decreases st_tk.levels)
let rec fully_truncate_state_rel #bytes #cb #token_t #group_id #leaf_ind st_ts st_tk =
  if st_ts.levels = 0 then ()
  else (
    treesync_treekem_rel_is_tree_empty (TNode?.right st_ts.tree) (TNode?.right st_tk.tree);
    if is_tree_empty (TNode?.right st_ts.tree) then (
      let st_ts_mid: treesync_state bytes tkt token_t group_id = {
        levels = st_ts.levels-1;
        tree = tree_truncate st_ts.tree;
        tokens = MLS.TreeSync.Invariants.AuthService.as_truncate st_ts.tokens;
      } in
      let st_tk_mid = TK_API.truncate_one st_tk in
      fully_truncate_state_rel st_ts_mid st_tk_mid
    ) else ()
  )

val remove_state_rel:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #token_t:Type0 -> #group_id:mls_bytes bytes -> #leaf_ind:nat ->
  #st_ts:treesync_state bytes tkt token_t group_id -> #li:treesync_index st_ts ->
  pend:TS_API.pending_remove st_ts li ->
  st_tk:treekem_tree_state bytes leaf_ind -> i:treekem_index st_tk{i <> leaf_ind} ->
  Lemma
  (requires
    li == i /\
    st_ts `treesync_treekem_state_rel` st_tk
  )
  (ensures
    TS_API.finalize_remove pend
    `treesync_treekem_state_rel`
    TK_API.remove st_tk i
  )
let remove_state_rel #bytes #cb #token_t #group_id #leaf_ind #st_ts #li pend st_tk i =
  reveal_opaque (`%TK_API.remove) (TK_API.remove st_tk i);
  tree_remove_treesync_treekem_rel st_ts.tree st_tk.tree li;
  let st_ts_mid: treesync_state bytes tkt token_t group_id = { st_ts with
    tree = MLS.TreeSync.Refined.Operations.tree_remove st_ts.tree li;
    tokens = MLS.TreeSync.Invariants.AuthService.as_remove st_ts.tokens li;
  } in
  let st_tk_mid = TK_API.remove_aux st_tk li in
  fully_truncate_state_rel st_ts_mid st_tk_mid

#push-options "--fuel 0 --ifuel 1"
val process_commit_state_rel:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #token_t:Type0 ->
  #group_id:mls_bytes bytes -> #leaf_ind:nat ->
  #st_ts:treesync_state bytes tkt token_t group_id -> #li_ts:treesync_index st_ts -> #p_ts:pathsync bytes tkt st_ts.levels 0 li_ts ->
  pend:TS_API.pending_commit st_ts p_ts -> token:token_t ->
  st_tk:treekem_tree_state bytes leaf_ind -> #li_tk:treekem_index st_tk{li_tk <> leaf_ind} -> p_tk:pathkem bytes st_tk.levels 0 li_tk{path_filtering_ok st_tk.tree p_tk} -> excluded_leaves:list nat{~(List.Tot.memP leaf_ind excluded_leaves)} -> group_context:group_context_nt bytes ->
  Lemma
  (requires
    li_ts == li_tk /\
    st_ts `treesync_treekem_state_rel` st_tk /\
    // the following is proved using the lemma `pathsync_pathkem_rel_update_path_to_treeX`
    p_ts `pathsync_pathkem_rel` p_tk
  )
  (ensures (
    match TS_API.finalize_commit pend token, TK_API.commit st_tk p_tk excluded_leaves group_context with
    | Success res_ts, Success (res_tk, _) ->
      res_ts `treesync_treekem_state_rel` res_tk
    | _, _ -> True
  ))
let process_commit_state_rel #bytes #cb #token_t #group_id #leaf_ind #st_ts #li_ts #p_ts pend token st_tk #li_tk p_tk  excluded_leaves group_context =
  reveal_opaque (`%TK_API.commit) (TK_API.commit st_tk p_tk excluded_leaves group_context);
  apply_path_treesync_treekem_rel st_ts.tree st_tk.tree p_ts p_tk
#pop-options

#push-options "--fuel 1 --ifuel 1 --z3rlimit 25"
val pathsync_pre_pathkem_rel_to_pathsync_pathkem_rel:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #l:nat -> #i:tree_index l -> #li:leaf_index l i ->
  ps:pathsync bytes tkt l i li -> p:path_secrets bytes l i li -> pk:pathkem bytes l i li ->
  tk:treekem bytes l i{MLS.TreeKEM.Invariants.treekem_invariant tk} -> group_context:group_context_nt bytes ->
  rand:randomness bytes (TK_ops.encrypt_path_secrets_entropy_lengths tk (TK_ops.forget_path_secrets p)) ->
  Lemma
  (requires
    ps `pathsync_path_secrets_rel` p /\
    (exists priv_st. Success (pk, priv_st) == TK_ops.encrypt_path_secrets tk p group_context rand)
  )
  (ensures pathsync_pathkem_rel ps pk)
let rec pathsync_pre_pathkem_rel_to_pathsync_pathkem_rel #bytes #cb #l #i #li ps p pk tk group_context rand =
  let open TK_ops in
  if l = 0 then ()
  else (
    let (child, sibling) = get_child_sibling tk li in
    let rand_cur, rand_next = split_randomness (rand <: randomness bytes ((if Some? (PNode?.data p) then multi_encrypt_with_label_entropy_lengths (tree_resolution sibling) else []) `List.Tot.append` (encrypt_path_secrets_entropy_lengths child (PNode?.next (forget_path_secrets p))))) in
    pathsync_pre_pathkem_rel_to_pathsync_pathkem_rel (PNode?.next ps) (PNode?.next p) (PNode?.next pk) child group_context rand_next
  )
#pop-options

#push-options "--fuel 0 --ifuel 1"
val create_commit_state_rel:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #token_t:Type0 ->
  #group_id:mls_bytes bytes -> #leaf_ind:nat ->
  #st_ts:treesync_state bytes tkt token_t group_id -> #li_ts:treesync_index st_ts -> #p_ts:pathsync bytes tkt st_ts.levels 0 li_ts ->
  ts_pend:TS_API.pending_commit st_ts p_ts -> token:token_t ->
  st_tk:treekem_tree_state bytes leaf_ind ->
  tk_pend:TK_API.pending_commit st_tk ->
  added_leaves:list nat -> group_context:group_context_nt bytes ->
  rand_finalize:randomness bytes (TK_API.finalize_create_commit_entropy_lengths st_tk added_leaves) ->
  Lemma
  (requires
    li_ts == leaf_ind /\
    st_ts `treesync_treekem_state_rel` st_tk /\
    p_ts `pathsync_path_secrets_rel` tk_pend.path_secrets
  )
  (ensures (
    match TS_API.finalize_commit ts_pend token, TK_API.finalize_create_commit tk_pend added_leaves group_context rand_finalize with
    | Success res_ts, Success res_tk -> (
      res_ts `treesync_treekem_state_rel` res_tk.TK_API.new_state
    )
    | _, _ -> True
  ))
let create_commit_state_rel #bytes #cb #token_t #group_id #leaf_ind #st_ts #li_st #p_ts ts_pend token st_tk tk_pend added_leaves group_context rand_finalize =
  reveal_opaque (`%TK_API.finalize_create_commit) (TK_API.finalize_create_commit tk_pend added_leaves group_context rand_finalize);
  match TS_API.finalize_commit ts_pend token, TK_API.finalize_create_commit tk_pend added_leaves group_context rand_finalize with
  | Success res_ts, Success res_tk -> (
    MLS.TreeKEM.Invariants.Proofs.treekem_invariant_un_add st_tk.tree added_leaves;
    assert((Success ((res_tk.TK_API.update_path <: pathkem bytes _ _ _), res_tk.TK_API.new_state.priv) == TK_ops.encrypt_path_secrets (TK_ops.un_add st_tk.tree added_leaves) tk_pend.path_secrets group_context rand_finalize));
    pathsync_pre_pathkem_rel_to_pathsync_pathkem_rel p_ts tk_pend.path_secrets res_tk.TK_API.update_path (TK_ops.un_add st_tk.tree added_leaves) group_context rand_finalize;
    apply_path_treesync_treekem_rel st_ts.tree st_tk.tree p_ts res_tk.TK_API.update_path
  )
  | _, _ -> ()
#pop-options

#push-options "--ifuel 1 --fuel 1"
val pathsync_external_pathsync_path_secrets_rel_lemma:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #l:nat -> #i:tree_index l -> #li:leaf_index l i ->
  psync:pathsync bytes tkt l i li -> epsync:external_pathsync bytes tkt l i li -> ps:path_secrets bytes l i li ->
  Lemma
  (requires
    external_pathsync_path_secrets_rel epsync ps /\
    external_pathsync_pathsync_rel epsync psync
  )
  (ensures pathsync_path_secrets_rel psync ps)
let rec pathsync_external_pathsync_path_secrets_rel_lemma #bytes #cb #l #i #li psync epsync ps =
  match psync, epsync, ps with
  | PLeaf ln1, PLeaf ln2, PLeaf ln3 -> ()
  | PNode x1 pnext1, PNode x2 pnext2, PNode x3 pnext3 ->
    pathsync_external_pathsync_path_secrets_rel_lemma pnext1 pnext2 pnext3
#pop-options

#push-options "--ifuel 1 --fuel 1"
val external_path_to_path_external_pathsync_pathsync_rel_aux:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l -> #li:leaf_index l i ->
  p:external_pathsync bytes tkt l i li -> ln:leaf_node_nt bytes tkt ->
  Lemma
  (requires ln.data.content == (get_path_leaf p).content)
  (ensures MLS.TreeSyncTreeKEMBinder.Properties.external_pathsync_pathsync_rel p (set_path_leaf p ln))
let rec external_path_to_path_external_pathsync_pathsync_rel_aux #bytes #cb #tkt #l #i #li p ln =
  match p with
  | PLeaf _ -> ()
  | PNode _ p_next -> external_path_to_path_external_pathsync_pathsync_rel_aux p_next ln
#pop-options

// TODO move
val get_path_leaf_set_path_leaf:
  #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l -> #li:leaf_index l i ->
  p:external_pathsync bytes tkt l i li -> ln:leaf_node_nt bytes tkt ->
  Lemma
  (get_path_leaf (set_path_leaf p ln) == ln)
let rec get_path_leaf_set_path_leaf #bytes #bl #tkt #l #i #li p ln =
  match p with
  | PLeaf _ -> ()
  | PNode _ p_next -> get_path_leaf_set_path_leaf p_next ln

val external_path_to_path_external_pathsync_pathsync_rel:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l -> #li:leaf_index l i ->
  t:treesync bytes tkt l i -> p:external_pathsync bytes tkt l i li{(get_path_leaf p).source == LNS_update} -> group_id:mls_bytes bytes -> signature_key:bytes -> signature_nonce:sign_nonce bytes ->
  Lemma (
    match TS_ops.external_path_to_path t p group_id signature_key signature_nonce with
    | Success pathsync -> (
      MLS.TreeSyncTreeKEMBinder.Properties.external_pathsync_pathsync_rel p pathsync /\
      (get_path_leaf pathsync).data.source = LNS_commit /\
      (get_path_leaf pathsync).data == { get_path_leaf p with source = LNS_commit; parent_hash = (get_path_leaf pathsync).data.parent_hash }
    )
    | _ -> True
  )
let external_path_to_path_external_pathsync_pathsync_rel #bytes #cb #tkt #l #i #li t p group_id signature_key signature_nonce =
  match TS_ops.external_path_to_path_aux t p group_id signature_key signature_nonce with
  | Success ln ->
    external_path_to_path_external_pathsync_pathsync_rel_aux p ln;
    get_path_leaf_set_path_leaf p ln
  | _ -> ()

val authenticate_external_path_external_pathsync_pathsync_rel:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes -> #token_t:Type0 -> #group_id:mls_bytes bytes ->
  st:treesync_state bytes tkt token_t group_id ->
  #li:treesync_index st ->
  p:external_pathsync bytes tkt st.levels 0 li{(get_path_leaf p).source == LNS_update} ->
  signature_key:bytes -> signature_nonce:sign_nonce bytes ->
  Lemma (
    match TS_API.authenticate_external_path #bytes st p signature_key signature_nonce with
    | Success pathsync -> (
      MLS.TreeSyncTreeKEMBinder.Properties.external_pathsync_pathsync_rel p pathsync /\
      (get_path_leaf pathsync).data.source = LNS_commit /\
      (get_path_leaf pathsync).data == { get_path_leaf p with source = LNS_commit; parent_hash = (get_path_leaf pathsync).data.parent_hash }
    )
    | _ -> True
  )
let authenticate_external_path_external_pathsync_pathsync_rel #bytes #cb #tkt #token_t #group_id st #li p signature_key signature_nonce =
  external_path_to_path_external_pathsync_pathsync_rel st.tree p group_id signature_key signature_nonce

#push-options "--ifuel 1 --fuel 1"
val get_path_leaf_pathsync_path_secrets_rel:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #l:nat -> #i:tree_index l -> #li:leaf_index l i ->
  psync:pathsync bytes tkt l i li -> ps:path_secrets bytes l i li ->
  Lemma
  (requires pathsync_path_secrets_rel psync ps)
  (ensures (
    match hpke_gen_keypair (get_path_leaf ps <: bytes) with
    | Success (sk, pk) -> pk == (get_path_leaf psync).data.content
    | _ -> False
  ))
let rec get_path_leaf_pathsync_path_secrets_rel #bytes #cb #l #i #li psync ps =
  match psync, ps with
  | PLeaf _, PLeaf _ -> ()
  | PNode _ psync_next, PNode _ ps_next -> get_path_leaf_pathsync_path_secrets_rel psync_next ps_next
#pop-options
