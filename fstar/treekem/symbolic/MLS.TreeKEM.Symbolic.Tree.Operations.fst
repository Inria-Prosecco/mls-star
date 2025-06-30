module MLS.TreeKEM.Symbolic.Tree.Operations

open FStar.List.Tot { for_allP, for_allP_eq }
open Comparse
open DY.Core
open DY.Lib
open MLS.Crypto
open MLS.Tree
open MLS.NetworkTypes
open MLS.TreeSync.NetworkTypes
open MLS.TreeSync.Types
open MLS.TreeSync.Invariants.ParentHash { node_not_blank }
open MLS.TreeKEM.NetworkTypes
open MLS.TreeKEM.Types
open MLS.TreeKEM.Operations
open MLS.Symbolic
open MLS.Symbolic.Randomness
open MLS.TreeKEM.Symbolic.State.NodeKey
open MLS.MiscLemmas
open MLS.TreeCommon
open MLS.Tree.Lemmas
open MLS.TreeKEM.Symbolic.Tree.Labels
open MLS.TreeKEM.Invariants
open MLS.TreeSyncTreeKEMBinder
open MLS.TreeSyncTreeKEMBinder.Properties
open MLS.TreeSyncTreeKEMBinder.Proofs
open MLS.Crypto.Derived.Symbolic.EncryptWithLabel
open MLS.Crypto.Derived.Symbolic.ExpandWithLabel
open MLS.TreeSync.Symbolic.Parsers
open MLS.Result
open FStar.Mul

#set-options "--fuel 1 --ifuel 1"

val one_path_secret_usage_to_path_secret_label: one_path_secret_usage -> label
let one_path_secret_usage_to_path_secret_label x =
  node_sk_label_nosig x.t x.group_id x.committer_leaf_index

#push-options "--fuel 0 --ifuel 2"
val expand_usage_path_secret_path: expandwithlabel_crypto_usage
let expand_usage_path_secret_path = {
  get_usage = (fun prk_usage context length ->
    let usage_data = KdfExpandKey?.data prk_usage in
    match parse path_secret_usage usage_data with
    | None -> KdfExpandKey "MLS.PathSecret" empty
    | Some [] -> KdfExpandKey "MLS.PathSecret" (serialize _ ([] <: path_secret_usage))
    | Some (h::t) ->
      KdfExpandKey "MLS.PathSecret" (serialize _ t)
  );
  get_label = (fun prk_usage prk_label context length ->
    let usage_data = KdfExpandKey?.data prk_usage in
    match parse path_secret_usage usage_data with
    | None -> prk_label
    | Some [] -> prk_label
    | Some (h::t) -> prk_label `join` one_path_secret_usage_to_path_secret_label h
  );
  get_label_lemma = (fun tr prk_usage prk_label context length -> ());
}
#pop-options

#push-options "--fuel 0 --ifuel 3"
val expand_usage_path_secret_node: expandwithlabel_crypto_usage
let expand_usage_path_secret_node = {
  get_usage = (fun prk_usage context length ->
    node_key_usage
  );
  get_label = (fun prk_usage prk_label context length -> prk_label);
  get_label_lemma = (fun tr prk_usage prk_label context length -> ());
}
#pop-options

val mls_hpke_updatepathnode_pred: {|crypto_usages|} -> encryptwithlabel_crypto_pred
let mls_hpke_updatepathnode_pred #cusgs = {
  pred = (fun tr _ msg context ->
    exists data. msg `has_usage tr` (KdfExpandKey "MLS.PathSecret" data)
  );
  pred_later = (fun tr1 tr2 _ msg context -> ());
}

val has_mls_treekem_invariants: {|crypto_invariants|} -> prop
let has_mls_treekem_invariants #cusgs =
  has_mls_expandwithlabel_usage ("MLS.PathSecret", "path", expand_usage_path_secret_path) /\
  has_mls_expandwithlabel_usage ("MLS.PathSecret", "node", expand_usage_path_secret_node) /\
  has_mls_encryptwithlabel_pred ("MLS.NodeHpkeKey", "UpdatePathNode", mls_hpke_updatepathnode_pred)

val compute_path_secret_usage:
  #l:nat -> #i:tree_index l ->
  treesync bytes tkt l i -> mls_bytes bytes -> leaf_index l i ->
  path_secret_usage ->
  path_secret_usage
let rec compute_path_secret_usage #l #i t group_id li acc =
  match t with
  | TLeaf _ -> acc
  | TNode _ _ _ ->
    let (child, sibling) = get_child_sibling t li in
    if not (is_tree_empty sibling) then (
      compute_path_secret_usage child group_id li ({l=_; i=_; t=sibling; group_id; committer_leaf_index = li;}::acc)
    ) else (
      compute_path_secret_usage child group_id li acc
    )

val leaf_sk_is_correct:
  {|crypto_invariants|} ->
  bytes -> principal -> mls_bytes bytes ->
  tr:trace ->
  prop
let leaf_sk_is_correct #cinvs leaf_sk me group_id tr =
  bytes_invariant tr leaf_sk /\
  get_label tr leaf_sk `equivalent tr` (node_key_label me (hpke_pk leaf_sk)) /\
  leaf_sk `has_usage tr` (node_key_usage)

val leaf_pk_is_correct:
  {|crypto_invariants|} ->
  bytes -> principal -> mls_bytes bytes ->
  tr:trace ->
  prop
let leaf_pk_is_correct #cinvs leaf_pk me group_id tr =
  is_publishable tr leaf_pk /\
  get_hpke_sk_label tr leaf_pk `equivalent tr` (node_key_label me leaf_pk) /\
  leaf_pk `has_hpke_sk_usage tr` (node_key_usage)

val path_secret_is_correct:
  {|crypto_invariants|} ->
  #l:nat -> #i:tree_index l ->
  principal -> bytes -> bool ->
  bytes -> treesync bytes tkt l i -> mls_bytes bytes -> li:leaf_index l i ->
  tr:trace ->
  prop
let path_secret_is_correct #cinvs #l #i committer committer_leaf_pk is_at_root path_secret t group_id li tr =
  bytes_invariant tr path_secret /\
  get_label tr path_secret `equivalent tr` join (node_key_label committer committer_leaf_pk) (node_sk_label_nocommitter t group_id li) /\
  (exists data. path_secret `has_usage tr` (KdfExpandKey "MLS.PathSecret" data)) /\
  (is_at_root ==> path_secret `has_usage tr` (KdfExpandKey "MLS.PathSecret" (serialize path_secret_usage [])))

val path_secrets_are_correct:
  {|crypto_invariants|} ->
  #l:nat -> #i:tree_index l -> #li:leaf_index l i ->
  principal -> bool ->
  treesync bytes tkt l i -> mls_bytes bytes -> path_secrets bytes l i li ->
  tr:trace ->
  prop
let rec path_secrets_are_correct #cinvs #l #i #li me is_at_root t group_id p tr =
  match p with
  | PLeaf leaf_sk ->
    leaf_sk_is_correct leaf_sk me group_id tr
  | PNode opt_ps p_next -> (
    let (child, sibling) = get_child_sibling t li in
    let (opt_ps_ok, is_at_root_next) =
      match opt_ps with
      | None -> (
        ((is_tree_empty sibling <: prop), is_at_root)
      )
      | Some ps -> (
        (path_secret_is_correct me (hpke_pk (get_path_leaf p)) is_at_root ps t group_id li tr, false)
      )
    in
    opt_ps_ok /\ path_secrets_are_correct me is_at_root_next child group_id p_next tr
  )

#push-options "--z3rlimit 25"
val path_secrets_are_correct_later:
  {|crypto_invariants|} ->
  #l:nat -> #i:tree_index l -> #li:leaf_index l i ->
  me:principal -> is_at_root:bool ->
  t:treesync bytes tkt l i -> group_id:mls_bytes bytes -> p:path_secrets bytes l i li ->
  tr1:trace -> tr2:trace ->
  Lemma
  (requires
    path_secrets_are_correct me is_at_root t group_id p tr1 /\
    tr1 <$ tr2
  )
  (ensures path_secrets_are_correct me is_at_root t group_id p tr2)
  [SMTPat (path_secrets_are_correct me is_at_root t group_id p tr1); SMTPat (tr1 <$ tr2)]
let rec path_secrets_are_correct_later #cinvs #l #i #li me is_at_root t group_id p tr1 tr2 =
  match p with
  | PLeaf leaf_sk ->
    ()
  | PNode opt_ps p_next -> (
    let (child, sibling) = get_child_sibling t li in
    path_secrets_are_correct_later me (is_at_root && opt_ps = None) child group_id p_next tr1 tr2
  )
#pop-options

val generate_path_secrets_correct_join_lemma:
  l1:label -> l1':label -> l2:label -> l3:label ->
  tr:trace ->
  Lemma
  (requires
    l1 `equivalent tr` l1' /\
    l3 `equivalent tr` (l1 `join` l2)
  )
  (ensures l3 `equivalent tr` (l1' `join` l2))
let generate_path_secrets_correct_join_lemma l1 l1' l2 l3 tr =
  join_eq tr l1 l2 (join l1' l2)

#push-options "--z3rlimit 25 --ifuel 0"
val generate_path_secrets_proof:
  {|crypto_invariants|} ->
  #l:nat -> #i:tree_index l ->
  me:principal ->
  ts:treesync bytes tkt l i -> tk:treekem bytes l i ->
  leaf_sk:hpke_private_key bytes -> path_secret_0:bytes -> li:leaf_index l i ->
  group_id:mls_bytes bytes -> tr:trace ->
  acc:path_secret_usage ->
  Lemma
  (requires (
    let path_usages = compute_path_secret_usage ts group_id li acc in
    ts `treesync_treekem_rel` tk /\

    bytes_invariant tr leaf_sk /\
    get_label tr leaf_sk `equivalent tr` (node_key_label me (hpke_pk leaf_sk)) /\
    leaf_sk `has_usage tr` (node_key_usage) /\

    bytes_invariant tr path_secret_0 /\
    get_label tr path_secret_0 `equivalent tr` join (node_key_label me (hpke_pk leaf_sk)) (if Cons? path_usages then one_path_secret_usage_to_path_secret_label (List.Tot.hd path_usages) else secret) /\
    path_secret_0 `has_usage tr` (KdfExpandKey "MLS.PathSecret" (serialize _ (if Cons? path_usages then List.Tot.tl path_usages else []))) /\

    has_mls_treekem_invariants
  ))
  (ensures (
    match generate_path_secrets tk leaf_sk path_secret_0 li with
    | Success (p, path_secret_n) ->
      path_secrets_are_correct me (acc = []) ts group_id p tr /\
      bytes_invariant tr path_secret_n /\
      path_secret_n `has_usage tr` (KdfExpandKey "MLS.PathSecret" (serialize _ (if Cons? acc then List.Tot.tl acc else []))) /\
      get_label tr path_secret_n `equivalent tr` join (node_key_label me (hpke_pk leaf_sk)) (join (node_sk_label_nocommitter ts group_id li) (if Cons? acc then (one_path_secret_usage_to_path_secret_label (List.Tot.hd acc)) else secret)) /\
      get_path_leaf p == leaf_sk
    | _ -> True
  ))
let rec generate_path_secrets_proof #cinvs #l #i me ts tk leaf_sk path_secret_0 li group_id tr acc =
  match tk with
  | TLeaf _ -> ()
  | TNode _ _ _ -> (
    if not (Success? (generate_path_secrets tk leaf_sk path_secret_0 li)) then ()
    else (
      let (child_k, sibling_k) = get_child_sibling tk li in
      let (child_s, sibling_s) = get_child_sibling ts li in
      treesync_treekem_rel_is_tree_empty sibling_s sibling_k;
      let Success (p_next, my_path_secret) = generate_path_secrets child_k leaf_sk path_secret_0 li in
      if not (is_tree_empty sibling_k) then (
        generate_path_secrets_proof me child_s child_k leaf_sk path_secret_0 li group_id tr ({l=_; i=_; t = sibling_s; group_id; committer_leaf_index = li;}::acc);
        expand_with_label_lemma tr "MLS.PathSecret" expand_usage_path_secret_path my_path_secret ((KdfExpandKey "MLS.PathSecret" (serialize _ acc))) "path" empty (kdf_length #bytes);
        let Success path_secret_n = derive_next_path_secret my_path_secret in
        node_sk_label_nosig_join_node_sk_label_nocommitter_eq ts group_id li tr;
        join_associative (node_key_label me (hpke_pk leaf_sk)) (node_sk_label_nocommitter ts group_id li) (if Cons? acc then (one_path_secret_usage_to_path_secret_label (List.Tot.hd acc)) else secret);
        generate_path_secrets_correct_join_lemma (get_label tr my_path_secret) (join (node_key_label me (hpke_pk leaf_sk)) (node_sk_label_nocommitter ts group_id li)) (if Cons? acc then (one_path_secret_usage_to_path_secret_label (List.Tot.hd acc)) else secret) (get_label tr path_secret_n) tr
      ) else (
        node_sk_label_nocommitter_empty sibling_s group_id li tr;
        generate_path_secrets_proof me child_s child_k leaf_sk path_secret_0 li group_id tr acc
      )
    )
  )
#pop-options

val node_sk_is_correct:
  {|crypto_invariants|} ->
  #l:nat -> #i:tree_index l ->
  principal -> bytes ->
  bytes -> treesync bytes tkt l i -> mls_bytes bytes -> leaf_index l i ->
  trace ->
  prop
let node_sk_is_correct #cinvs #l #i committer committer_leaf_pk node_sk t group_id li tr =
  bytes_invariant tr node_sk /\
  join (node_key_label committer committer_leaf_pk) (node_sk_label_nocommitter t group_id li) `equivalent tr` (get_label tr node_sk) /\
  node_sk `has_usage tr` node_key_usage

val node_pk_is_correct:
  {|crypto_invariants|} ->
  #l:nat -> #i:tree_index l ->
  principal -> bytes -> bool ->
  bytes -> treesync bytes tkt l i -> mls_bytes bytes -> leaf_index l i ->
  trace ->
  prop
let node_pk_is_correct #cinvs #l #i committer committer_leaf_pk is_at_root node_pk t group_id li tr =
  is_publishable tr node_pk /\
  join (node_key_label committer committer_leaf_pk) (node_sk_label_nocommitter t group_id li) `can_flow tr` (get_hpke_sk_label tr node_pk) /\
  node_pk `has_hpke_sk_usage tr` node_key_usage /\
  (is_at_root ==> is_root_node_pk tr node_pk)

val pre_pathkem_correct:
  {|crypto_invariants|} ->
  #l:nat -> #i:tree_index l -> #li:leaf_index l i ->
  principal -> bool -> treesync bytes tkt l i -> pre_pathkem bytes l i li -> mls_bytes bytes ->
  tr:trace ->
  prop
let rec pre_pathkem_correct #cinvs #l #i #li committer is_at_root t p group_id tr =
  match p with
  | PLeaf { public_key } ->
    leaf_pk_is_correct public_key committer group_id tr
  | PNode opt_ps p_next -> (
    let (child, sibling) = get_child_sibling t li in
    let (opt_ps_ok, is_at_root_next) =
      match opt_ps with
      | None -> (
        ((is_tree_empty sibling <: prop), is_at_root)
      )
      | Some node_pk -> (
        (node_pk_is_correct committer (get_path_leaf p).public_key is_at_root node_pk t group_id li tr, false)
      )
    in
    opt_ps_ok /\ pre_pathkem_correct committer is_at_root_next child p_next group_id tr
  )

val derive_keypair_from_path_secret_proof:
  {|crypto_invariants|} ->
  #l:nat -> #i:tree_index l ->
  committer:principal -> committer_leaf_pk:bytes -> is_at_root:bool ->
  path_secret:bytes ->
  t:treesync bytes tkt l i -> group_id:mls_bytes bytes -> li:leaf_index l i ->
  tr:trace ->
  Lemma
  (requires
    path_secret_is_correct committer committer_leaf_pk is_at_root path_secret t group_id li tr /\
    has_mls_treekem_invariants
  )
  (ensures (
    match derive_keypair_from_path_secret path_secret with
    | Success (sk, pk) -> (
      node_sk_is_correct committer committer_leaf_pk sk t group_id li tr /\
      node_pk_is_correct committer committer_leaf_pk is_at_root pk t group_id li tr
    )
    | _ -> True
  ))
let derive_keypair_from_path_secret_proof #cinvs #l #i committer committer_leaf_pk is_at_root path_secret t group_id li tr =
  match derive_keypair_from_path_secret path_secret with
  | Success (sk, pk) -> (
    eliminate exists data. path_secret `has_usage tr` (KdfExpandKey "MLS.PathSecret" data)
    returns node_sk_is_correct committer committer_leaf_pk sk t group_id li tr /\ node_pk_is_correct committer committer_leaf_pk is_at_root pk t group_id li tr
    with _. (
      expand_with_label_lemma tr "MLS.PathSecret" expand_usage_path_secret_node path_secret (KdfExpandKey "MLS.PathSecret" data) "node" empty (kdf_length #bytes)
    )
  )
  | _ -> ()

#push-options "--z3rlimit 25"
val path_secrets_to_pre_pathkem_proof:
  {|crypto_invariants|} ->
  #l:nat -> #i:tree_index l -> #li:leaf_index l i ->
  me:principal -> is_at_root:bool -> t:treesync bytes tkt l i -> p:path_secrets bytes l i li -> group_id:mls_bytes bytes ->
  tr:trace ->
  Lemma
  (requires
    path_secrets_are_correct me is_at_root t group_id p tr /\
    has_mls_treekem_invariants
  )
  (ensures (
    match path_secrets_to_pre_pathkem p with
    | Success res -> (
      pre_pathkem_correct me is_at_root t res group_id tr /\
      (get_path_leaf res).public_key == hpke_pk (get_path_leaf p)
    )
    | _ -> True
  ))
let rec path_secrets_to_pre_pathkem_proof #cinvs #l #i #li me is_at_root t p group_id tr =
  match p with
  | PLeaf _ -> ()
  | PNode opt_ps p_next -> (
    if not (Success? (path_secrets_to_pre_pathkem p)) then ()
    else (
      let Success res = path_secrets_to_pre_pathkem p in
      let (child, sibling) = get_child_sibling t li in
      path_secrets_to_pre_pathkem_proof me (opt_ps = None && is_at_root) child p_next group_id tr;
      match opt_ps with
      | None -> ()
      | Some ps -> (
        derive_keypair_from_path_secret_proof me (hpke_pk (get_path_leaf p)) is_at_root ps t group_id li tr
      )
    )
  )
#pop-options

val multi_encrypt_with_label_pre_weak:
  {|crypto_invariants|} -> encryptwithlabel_crypto_pred ->
  pks:list bytes -> bytes -> bytes -> randomness bytes (multi_encrypt_with_label_entropy_lengths pks) ->
  trace ->
  prop
let rec multi_encrypt_with_label_pre_weak #cinvs lpred pks context plaintext rand tr =
  match pks with
  | [] -> True
  | pk::pks -> (
    let (r, rand) = dest_randomness #bytes #_ #(hpke_private_key_length #bytes) rand in
    multi_encrypt_with_label_pre_weak lpred pks context plaintext rand tr /\
    bytes_invariant tr pk /\
    bytes_invariant tr r /\
    bytes_invariant tr context /\
    bytes_invariant tr plaintext /\
    (get_label tr plaintext) `can_flow tr` (get_label tr r) /\
    (get_label tr r) `can_flow tr` (get_hpke_sk_label tr pk) /\
    r `has_usage tr` entropy_usage_for_node_key /\
    (
      (
        pk `has_hpke_sk_usage tr` node_key_usage /\
        lpred.pred tr empty plaintext context
      ) \/ (
        get_label tr r `can_flow tr` public
      )
    )
  )

val hpke_ciphertext_is_publishable:
  {|crypto_invariants|} ->
  trace ->
  (hpke_ciphertext_nt bytes -> prop)
let hpke_ciphertext_is_publishable #cinvs tr =
  is_well_formed_prefix ps_hpke_ciphertext_nt (is_publishable tr)

#push-options "--z3rlimit 25"
val multi_encrypt_with_label_proof:
  {|crypto_invariants|} -> lpred:encryptwithlabel_crypto_pred ->
  pks:list bytes -> label:valid_label -> context:bytes -> plaintext:bytes -> rand:randomness bytes (multi_encrypt_with_label_entropy_lengths pks) ->
  tr:trace ->
  Lemma
  (requires
    multi_encrypt_with_label_pre_weak lpred pks context plaintext rand tr /\
    has_mls_encryptwithlabel_pred ("MLS.NodeHpkeKey", label, lpred)
  )
  (ensures (
    match multi_encrypt_with_label pks label context plaintext rand with
    | Success res -> (
      for_allP (hpke_ciphertext_is_publishable tr) res
    )
    | _ -> True
  ))
let rec multi_encrypt_with_label_proof #cinvs lpred pks label context plaintext rand tr =
  if not (Success? (multi_encrypt_with_label pks label context plaintext rand)) then ()
  else (
    match pks with
    | [] -> ()
    | pk::pks -> (
      let (r, rand) = dest_randomness #bytes #_ #(hpke_private_key_length #bytes) rand in
      bytes_invariant_encrypt_with_label lpred "MLS.NodeHpkeKey" empty tr pk label context plaintext r;
      multi_encrypt_with_label_proof lpred pks label context plaintext rand tr
    )
  )
#pop-options

val multi_encrypt_with_label_entropy_ghost_data:
  pks:list bytes -> label ->
  Pure randomness_ghost_data
  (requires True)
  (ensures fun res ->
    List.Tot.length res == List.Tot.length (multi_encrypt_with_label_entropy_lengths pks)
  )
let rec multi_encrypt_with_label_entropy_ghost_data pks rand_label =
  match pks with
  | [] -> []
  | h::t ->
    (entropy_usage_for_node_key, rand_label)::(multi_encrypt_with_label_entropy_ghost_data t rand_label)

val multi_encrypt_with_label_pre_strong_one:
  {|crypto_invariants|} ->
  trace -> label -> bytes ->
  prop
let multi_encrypt_with_label_pre_strong_one #cinvs tr rand_label pk =
  bytes_invariant tr pk /\
  rand_label `can_flow tr` (get_hpke_sk_label tr pk) /\
  (
    (
      pk `has_hpke_sk_usage tr` node_key_usage
    ) \/ (
      rand_label `can_flow tr` public
    )
  )

val multi_encrypt_with_label_pre_strong:
  {|crypto_invariants|} ->
  pks:list bytes -> bytes -> bytes -> randomness bytes (multi_encrypt_with_label_entropy_lengths pks) ->
  label -> trace ->
  prop
let multi_encrypt_with_label_pre_strong #cinvs pks context plaintext rand rand_label tr =
    for_allP (multi_encrypt_with_label_pre_strong_one tr rand_label) pks /\
    rand `randomness_has_ghost_data tr` (multi_encrypt_with_label_entropy_ghost_data pks rand_label) /\
    bytes_invariant tr context /\
    bytes_invariant tr plaintext /\
    (get_label tr plaintext) `can_flow tr` rand_label /\
    mls_hpke_updatepathnode_pred.pred tr empty plaintext context

val multi_encrypt_with_label_pre_strong_implies_weak:
  {|crypto_invariants|} ->
  pks:list bytes -> context:bytes -> plaintext:bytes -> rand:randomness bytes (multi_encrypt_with_label_entropy_lengths pks) ->
  rand_label:label -> tr:trace ->
  Lemma
  (requires multi_encrypt_with_label_pre_strong pks context plaintext rand rand_label tr)
  (ensures multi_encrypt_with_label_pre_weak mls_hpke_updatepathnode_pred pks context plaintext rand tr)
let rec multi_encrypt_with_label_pre_strong_implies_weak #cinvs pks context plaintext rand rand_label tr =
  match pks with
  | [] -> ()
  | pk::pks -> (
    let (r, rand) = dest_randomness #bytes #_ #(hpke_private_key_length #bytes) rand in
    multi_encrypt_with_label_pre_strong_implies_weak pks context plaintext rand rand_label tr
  )

#push-options "--z3rlimit 25"
val multi_encrypt_with_label_weak_proof:
  {|crypto_invariants|} ->
  pks:list bytes -> context:bytes -> plaintext:bytes -> rand:randomness bytes (multi_encrypt_with_label_entropy_lengths pks) ->
  rand_label:label -> tr:trace ->
  Lemma
  (requires
    multi_encrypt_with_label_pre_strong pks context plaintext rand rand_label tr /\
    has_mls_encryptwithlabel_pred ("MLS.NodeHpkeKey", "UpdatePathNode", mls_hpke_updatepathnode_pred)
  )
  (ensures (
    match multi_encrypt_with_label pks "UpdatePathNode" context plaintext rand with
    | Success res -> (
      for_allP (hpke_ciphertext_is_publishable tr) res
    )
    | _ -> True
  ))
let multi_encrypt_with_label_weak_proof #cinvs pks context plaintext rand rand_label tr =
  multi_encrypt_with_label_pre_strong_implies_weak pks context plaintext rand rand_label tr;
  multi_encrypt_with_label_proof mls_hpke_updatepathnode_pred pks "UpdatePathNode" context plaintext rand tr
#pop-options

val node_key_good_weak:
  {|crypto_invariants|} ->
  #l:nat -> #i:tree_index l ->
  tr:trace ->
  treesync bytes tkt l i -> mls_bytes bytes -> bytes ->
  prop
let node_key_good_weak #cinvs #l #i tr t group_id =
  multi_encrypt_with_label_pre_strong_one tr (node_sk_label t group_id)

#push-options "--z3rlimit 25"
val path_secret_flows_to_leaf_at:
  {|crypto_invariants|} ->
  #l:nat -> #i:tree_index l ->
  ts:treesync bytes tkt l i -> tk:treekem bytes l i ->
  li:leaf_index l i ->
  group_id:mls_bytes bytes -> tr:trace ->
  Lemma
  (requires
    all_tree_keys_good ts group_id tr /\
    Some? (leaf_at tk li) /\
    ts `treesync_treekem_rel` tk
  )
  (ensures (
    let pk = (Some?.v (leaf_at tk li)).public_key in
    node_key_good_weak tr ts group_id pk
  ))
let rec path_secret_flows_to_leaf_at #cinvs #l #i ts tk li group_id tr =
  match ts with
  | TLeaf (Some ln) -> ()
  | TNode _ _ _ -> (
    let (child_s, _) = get_child_sibling ts li in
    let (child_k, _) = get_child_sibling tk li in
    path_secret_flows_to_leaf_at child_s child_k li group_id tr;
    ()
  )
#pop-options

#push-options "--fuel 2 --ifuel 2 --z3rlimit 25"
val path_secret_flows_to_unmerged_leaves_resolution:
  {|crypto_invariants|} ->
  #l:nat -> #i:tree_index l ->
  ts:treesync bytes tkt l i -> tk:treekem bytes l i ->
  unmerged_leaves:list nat ->
  group_id:mls_bytes bytes -> tr:trace ->
  Lemma
  (requires
    all_tree_keys_good ts group_id tr /\
    for_allP (unmerged_leaf_exists tk) unmerged_leaves /\
    ts `treesync_treekem_rel` tk
  )
  (ensures
    for_allP (node_key_good_weak tr ts group_id) (unmerged_leaves_resolution tk unmerged_leaves)
  )
let rec path_secret_flows_to_unmerged_leaves_resolution #cinvs #l #i ts tk unmerged_leaves group_id tr =
  match unmerged_leaves with
  | [] -> ()
  | h::t ->
    path_secret_flows_to_leaf_at ts tk h group_id tr;
    path_secret_flows_to_unmerged_leaves_resolution ts tk t group_id tr
#pop-options

#push-options "--fuel 2 --ifuel 2 --z3rlimit 50"
val path_secret_flows_to_tree_resolution:
  {|crypto_invariants|} ->
  #l:nat -> #i:tree_index l ->
  ts:treesync bytes tkt l i -> tk:treekem bytes l i ->
  group_id:mls_bytes bytes -> tr:trace ->
  Lemma
  (requires
    all_tree_keys_good ts group_id tr /\
    treekem_invariant tk /\
    ts `treesync_treekem_rel` tk
  )
  (ensures
    for_allP (node_key_good_weak tr ts group_id) (tree_resolution tk)
  )
let rec path_secret_flows_to_tree_resolution #cinvs #l #i ts tk group_id tr =
  match ts, tk with
  | TLeaf None, _-> ()
  | TLeaf (Some ln), _ -> ()
  | TNode None left_s right_s, TNode _ left_k right_k  -> (
    path_secret_flows_to_tree_resolution left_s left_k group_id tr;
    path_secret_flows_to_tree_resolution right_s right_k group_id tr;
    for_allP_eq (node_key_good_weak tr ts group_id) (tree_resolution tk);
    for_allP_eq (node_key_good_weak tr left_s group_id) (tree_resolution left_k);
    for_allP_eq (node_key_good_weak tr right_s group_id) (tree_resolution right_k);
    FStar.Classical.forall_intro (List.Tot.append_mem (tree_resolution left_k) (tree_resolution right_k))
  )
  | TNode (Some _) _ _, TNode (Some pn) _ _ -> (
    path_secret_flows_to_unmerged_leaves_resolution ts tk pn.unmerged_leaves group_id tr;
    node_sk_label_flows_to_node_sk_label_canon ts group_id tr
  )
#pop-options

val leaf_at_un_addP:
  #l:nat -> #i:tree_index l ->
  t:treekem bytes l i -> pre:(nat -> bool) ->
  li:nat ->
  Lemma
  (requires
    pre li /\
    unmerged_leaf_exists t li
  )
  (ensures leaf_at t li == leaf_at (un_addP t pre) li)
let rec leaf_at_un_addP #l #i t pre li =
  match t with
  | TLeaf _ -> ()
  | TNode _ _ _ ->
    let (child, sibling) = get_child_sibling t li in
    leaf_at_un_addP child pre li

val for_allP_unmerged_leaves_resolution_un_addP:
  #l:nat -> #i:tree_index l ->
  p:(bytes -> prop) ->
  t:treekem bytes l i -> unmerged_leaves:list nat{for_allP (unmerged_leaf_exists t) unmerged_leaves} ->
  pre:(nat -> bool) ->
  Lemma
  (requires
    treekem_invariant t /\
    for_allP p (unmerged_leaves_resolution t unmerged_leaves) /\
    treekem_invariant (un_addP t pre)
  )
  (ensures
    for_allP (unmerged_leaf_exists (un_addP t pre)) (List.Tot.filter pre unmerged_leaves) /\
    for_allP p (unmerged_leaves_resolution (un_addP t pre) (List.Tot.filter pre unmerged_leaves))
  )
let rec for_allP_unmerged_leaves_resolution_un_addP #l #i p t ul pre =
  match ul with
  | [] -> ()
  | uh::ut ->
    for_allP_unmerged_leaves_resolution_un_addP #l #i p t ut pre;
    if pre uh then (
      leaf_at_un_addP t pre uh
    ) else ()

val for_allP_tree_resolution_un_addP_subset:
  #l:nat -> #i:tree_index l ->
  p:(bytes -> prop) ->
  t:treekem bytes l i -> pre:(nat -> bool) ->
  Lemma
  (requires
    treekem_invariant t /\
    for_allP p (tree_resolution t) /\
    treekem_invariant (un_addP t pre)
  )
  (ensures for_allP p (tree_resolution (un_addP t pre)))
let rec for_allP_tree_resolution_un_addP_subset #l #i p t pre  =
  match t with
  | TLeaf _ -> ()
  | TNode None left right ->
    FStar.Classical.forall_intro (List.Tot.append_mem (tree_resolution (un_addP left pre)) (tree_resolution (un_addP right pre)));
    FStar.Classical.forall_intro (List.Tot.append_mem (tree_resolution left) (tree_resolution right));
    for_allP_eq p (tree_resolution t);
    for_allP_eq p (tree_resolution left);
    for_allP_eq p (tree_resolution right);
    for_allP_tree_resolution_un_addP_subset p left pre;
    for_allP_tree_resolution_un_addP_subset p right pre;
    for_allP_eq p (tree_resolution (un_addP t pre));
    for_allP_eq p (tree_resolution (un_addP left pre));
    for_allP_eq p (tree_resolution (un_addP right pre))
  | TNode (Some pn) left right ->
    for_allP_unmerged_leaves_resolution_un_addP p t pn.unmerged_leaves pre

open MLS.Symbolic.Parsers
open MLS.TreeKEM.Parsers

val pathkem_good:
  {|crypto_invariants|} ->
  #l:nat -> #i:tree_index l -> #li:leaf_index l i ->
  pathkem bytes l i li ->
  trace ->
  prop
let pathkem_good #cinvs #l #i #li p tr =
  is_well_formed_prefix (ps_path (ps_treekem_leaf) (ps_option ps_update_path_node_nt) l i li) (is_publishable tr) p

val encrypt_path_secrets_entropy_ghost_data:
  #l:nat -> #i:tree_index l -> #li:leaf_index l i ->
  ts:treesync bytes tkt l i ->
  tk:treekem bytes l i -> path_secrets:path unit bool l i li ->
  mls_bytes bytes ->
  pre:(nat -> bool) ->
  Pure randomness_ghost_data
  (requires treekem_invariant tk)
  (ensures fun res ->
    MLS.TreeKEM.Invariants.Proofs.treekem_invariant_un_addP tk pre;
    List.Tot.length res == List.Tot.length (encrypt_path_secrets_entropy_lengths (un_addP tk pre) path_secrets)
  )
let rec encrypt_path_secrets_entropy_ghost_data #l #i #li ts tk p group_id pre =
  match p with
  | PLeaf _ -> []
  | PNode is_not_filtered p_next -> (
    let (child_s, sibling_s) = get_child_sibling ts li in
    let (child_k, sibling_k) = get_child_sibling tk li in
    let my_randomness =
      if is_not_filtered then (
        MLS.TreeKEM.Invariants.Proofs.treekem_invariant_un_addP sibling_k pre;
        multi_encrypt_with_label_entropy_ghost_data (tree_resolution (un_addP sibling_k pre)) (node_sk_label sibling_s group_id)
      ) else []
    in
    let next_randomness = encrypt_path_secrets_entropy_ghost_data child_s child_k p_next group_id pre in
    MLS.TreeKEM.Invariants.Proofs.treekem_invariant_un_addP tk pre;
    List.Tot.Properties.append_length my_randomness next_randomness;
    List.Tot.append my_randomness next_randomness
  )

val path_secret_good_for_joiner:
  {|crypto_invariants|} ->
  #l:nat -> #i:tree_index l ->
  trace ->
  treesync bytes tkt l i -> mls_bytes bytes -> nat -> bytes ->
  prop
let path_secret_good_for_joiner #cinvs #l #i tr tree group_id leaf_ind path_secret =
  leaf_index_inside l i leaf_ind /\
  is_knowable_by (
    match (leaf_at tree leaf_ind) with
    | None -> secret
    | Some ln -> node_sk_label_aux_leaf ln group_id YesCommitter leaf_ind
  ) tr path_secret /\
  (exists data. path_secret `has_usage tr` (KdfExpandKey "MLS.PathSecret" data))

#push-options "--fuel 1 --ifuel 1"
val path_secrets_good_for_joiners:
  {|crypto_invariants|} ->
  #l:nat -> #i:tree_index l ->
  trace ->
  treesync bytes tkt l i -> mls_bytes bytes -> list nat -> list bytes ->
  prop
let rec path_secrets_good_for_joiners #cinvs #l #i tr tree group_id leaf_indices path_secrets =
  match leaf_indices, path_secrets with
  | [], [] -> True
  | h_li::t_li, h_ps::t_ps ->
    path_secret_good_for_joiner tr tree group_id h_li h_ps /\
    path_secrets_good_for_joiners tr tree group_id t_li t_ps
  | _, _ -> False
#pop-options

#push-options "--z3rlimit 25"
val get_path_secret_of_added_leaf_proof:
  {|crypto_invariants|} ->
  #l:nat -> #i:tree_index l -> #li:leaf_index l i ->
  me:principal -> is_at_root:bool ->
  ts:treesync bytes tkt l i ->
  p:path_secrets bytes l i li ->
  leaf_li:nat ->
  group_id:mls_bytes bytes -> tr:trace ->
  Lemma
  (requires
    path_secrets_are_correct me is_at_root ts group_id p tr
  )
  (ensures (
    match get_path_secret_of_added_leaf p leaf_li with
    | Success path_secret ->
      path_secret_good_for_joiner tr ts group_id leaf_li path_secret
    | _ -> True
  ))
let rec get_path_secret_of_added_leaf_proof #cinvs #l #i #li me is_at_root ts p leaf_li group_id tr =
  if not (Success? (get_path_secret_of_added_leaf p leaf_li)) then ()
  else (
    let PNode opt_path_secret p_next = p in
    if is_left_leaf li = is_left_leaf #l #i leaf_li then (
      let (child, sibling) = get_child_sibling ts li in
      get_path_secret_of_added_leaf_proof me (is_at_root && opt_path_secret = None) child p_next leaf_li group_id tr
    ) else (
      node_sk_label_aux_flows_to_node_sk_label_aux_leaf ts group_id (NoCommitter li) leaf_li tr
    )
  )
#pop-options

#push-options "--fuel 1 --ifuel 1"
val get_path_secret_of_added_leaves_proof:
  {|crypto_invariants|} ->
  #l:nat -> #li:leaf_index l 0 ->
  me:principal ->
  ts:treesync bytes tkt l 0 ->
  p:path_secrets bytes l 0 li ->
  leaf_indices:list nat ->
  group_id:mls_bytes bytes -> tr:trace ->
  Lemma
  (requires
    path_secrets_are_correct me true ts group_id p tr
  )
  (ensures (
    match get_path_secret_of_added_leaves p leaf_indices with
    | Success path_secrets ->
      path_secrets_good_for_joiners tr ts group_id leaf_indices path_secrets
    | _ -> True
  ))
let rec get_path_secret_of_added_leaves_proof #cinvs #l #li me ts p leaf_indices group_id tr =
  match leaf_indices with
  | [] -> ()
  | h::t -> (
    get_path_secret_of_added_leaf_proof me true ts p h group_id tr;
    get_path_secret_of_added_leaves_proof me ts p t group_id tr
  )
#pop-options

#push-options "--z3rlimit 500"
val encrypt_path_secrets_pub_proof:
  {|crypto_invariants|} ->
  #l:nat -> #i:tree_index l -> #li:leaf_index l i ->
  me:principal -> is_at_root:bool ->
  ts:treesync bytes tkt l i -> tk:treekem bytes l i{treekem_invariant tk} -> p:path_secrets bytes l i li ->
  group_context:group_context_nt bytes ->
  group_id:mls_bytes bytes ->
  pre:(nat -> bool){treekem_invariant (un_addP tk pre)} ->
  rand:randomness bytes (encrypt_path_secrets_entropy_lengths (un_addP tk pre) (forget_path_secrets p)) ->
  tr:trace ->
  Lemma
  (requires
    ts `treesync_treekem_rel` tk /\
    path_secrets_are_correct me is_at_root ts group_id p tr /\
    all_tree_keys_good ts group_id tr /\
    is_well_formed _ (bytes_invariant tr) group_context /\
    rand `randomness_has_ghost_data tr` (encrypt_path_secrets_entropy_ghost_data ts tk (forget_path_secrets p) group_id pre) /\
    has_mls_treekem_invariants
  )
  (ensures (
    match encrypt_path_secrets (un_addP tk pre) p group_context rand with
    | Success (update_path, _) ->
      pathkem_good update_path tr
    | _ -> True
  ))
let rec encrypt_path_secrets_pub_proof #cinvs #l #i #li me is_at_root ts tk p group_context group_id pre rand tr =
  match p with
  | PLeaf leaf_sk -> ()
  | PNode opt_ps p_next -> (
    if not (Success? (encrypt_path_secrets (un_addP tk pre) p group_context rand)) then ()
    else (
      let (child_s, sibling_s) = get_child_sibling ts li in
      let (child_k, sibling_k) = get_child_sibling tk li in
      match opt_ps with
      | None -> (
        encrypt_path_secrets_pub_proof me is_at_root child_s child_k p_next group_context group_id pre rand tr;
        let Success (res_p_next, res_p_priv_next)= encrypt_path_secrets (un_addP child_k pre) p_next group_context rand in
        ()
      )
      | Some path_secret -> (
        let rand_cur, rand_next = split_randomness rand in
        let rand_label = (node_sk_label sibling_s group_id) in
        serialize_wf_lemma _ (bytes_invariant tr) group_context;
        path_secret_flows_to_tree_resolution sibling_s sibling_k group_id tr;
        node_sk_label_noX_eq_node_sk_label sibling_s group_id li;
        assert(mls_hpke_updatepathnode_pred.pred tr empty path_secret (serialize _ group_context));
        split_randomness_ghost_data_lemma tr rand rand_cur rand_next (multi_encrypt_with_label_entropy_ghost_data (tree_resolution (un_addP sibling_k pre)) rand_label) (encrypt_path_secrets_entropy_ghost_data child_s child_k (forget_path_secrets p_next) group_id pre);
        encrypt_path_secrets_pub_proof me false child_s child_k p_next group_context group_id pre rand_next tr;
        for_allP_tree_resolution_un_addP_subset (node_key_good_weak tr sibling_s group_id) sibling_k pre;
        assert_norm((node_key_good_weak tr sibling_s group_id) == (multi_encrypt_with_label_pre_strong_one tr (node_sk_label sibling_s group_id)));
        multi_encrypt_with_label_weak_proof (tree_resolution (un_addP sibling_k pre)) (serialize _ group_context) path_secret rand_cur (node_sk_label sibling_s group_id) tr;
        derive_keypair_from_path_secret_proof me (hpke_pk (get_path_leaf p)) is_at_root path_secret ts group_id li tr;

        let Success (res_p_next, res_p_priv_next) = encrypt_path_secrets (un_addP child_k pre) p_next group_context rand_next in
        let Success ciphertexts = multi_encrypt_with_label (tree_resolution (un_addP sibling_k pre)) "UpdatePathNode" (serialize _ group_context) path_secret rand_cur in
        let Success (sk, pk) = derive_keypair_from_path_secret path_secret in
        ()
      )
    )
  )
#pop-options

#push-options "--z3rlimit 100 --fuel 1 --ifuel 2"
val encrypt_path_secrets_priv_proof:
  {|crypto_invariants|} ->
  #l:nat -> #i:tree_index l -> #li:leaf_index l i ->
  me:principal -> is_at_root:bool ->
  ts:treesync bytes tkt l i -> tk:treekem bytes l i{treekem_invariant tk} -> p:path_secrets bytes l i li ->
  group_context:group_context_nt bytes ->
  group_id:mls_bytes bytes ->
  rand:randomness bytes (encrypt_path_secrets_entropy_lengths tk (forget_path_secrets p)) ->
  tr:trace ->
  Lemma
  (requires
    path_secrets_are_correct me is_at_root ts group_id p tr /\
    has_mls_treekem_invariants
  )
  (ensures (
    match encrypt_path_secrets tk p group_context rand with
    | Success (_, st_priv) ->
      treekem_priv_state_pred tr me st_priv /\
      get_path_leaf st_priv == get_path_leaf p
    | _ -> True
  ))
let rec encrypt_path_secrets_priv_proof #cinvs #l #i #li me is_at_root ts tk p group_context group_id rand tr =
  match p with
  | PLeaf leaf_sk -> ()
  | PNode opt_ps p_next -> (
    if not (Success? (encrypt_path_secrets tk p group_context rand)) then ()
    else (
      let (child_s, sibling_s) = get_child_sibling ts li in
      let (child_k, sibling_k) = get_child_sibling tk li in
      match opt_ps with
      | None -> (
        encrypt_path_secrets_priv_proof me is_at_root child_s child_k p_next group_context group_id rand tr;
        ()
      )
      | Some path_secret -> (
        let (child_k, sibling_k) = get_child_sibling tk li in
        let _, rand_next = split_randomness #bytes #_ #(multi_encrypt_with_label_entropy_lengths (tree_resolution sibling_k)) #(encrypt_path_secrets_entropy_lengths child_k (forget_path_secrets p_next)) rand in
        derive_keypair_from_path_secret_proof me (hpke_pk (get_path_leaf p)) is_at_root path_secret ts group_id li tr;
        encrypt_path_secrets_priv_proof me false child_s child_k p_next group_context group_id rand_next tr;
        let Success (res_p_next, res_p_priv_next) = encrypt_path_secrets child_k p_next group_context rand_next in
        let Success (sk, pk) = derive_keypair_from_path_secret path_secret in
        assert(node_sk_is_correct me (hpke_pk (get_path_leaf p)) sk ts group_id li tr);
        assert(get_label tr sk `can_flow tr` join (node_key_label me (hpke_pk (get_path_leaf p))) (node_sk_label_nocommitter ts group_id li));
        assert(get_path_leaf p == get_path_leaf res_p_priv_next);
        assert(get_label tr sk `can_flow tr` node_key_label me (hpke_pk (get_path_leaf res_p_priv_next)));
        ()
      )
    )
  )
#pop-options

val decoded_path_secret_good:
  {|crypto_invariants|} ->
  principal -> bytes -> bytes -> trace ->
  prop
let decoded_path_secret_good #cinvs me my_leaf_pk path_secret tr =
  bytes_invariant tr path_secret /\
  get_label tr path_secret `can_flow tr` node_key_label me my_leaf_pk /\
  (exists data. path_secret `has_usage tr` (KdfExpandKey "MLS.PathSecret" data))

val treekem_priv_state_pred_leaf:
  {|crypto_invariants|} ->
  #l:nat -> #i:tree_index l -> #li:leaf_index l i ->
  me:principal ->
  p_priv:treekem_priv bytes l i li ->
  tr:trace ->
  Lemma
  (requires treekem_priv_state_pred tr me p_priv)
  (ensures is_node_sk_for_leaf_pk tr me (hpke_pk (get_path_leaf p_priv)) (get_path_leaf p_priv))
let rec treekem_priv_state_pred_leaf #cinvs #l #i #li me p_priv tr =
  match p_priv with
  | PLeaf _ -> ()
  | PNode _ p_next -> treekem_priv_state_pred_leaf me p_next tr

val get_private_key_proof:
  {|crypto_invariants|} ->
  #l:nat -> #i:tree_index l -> #li:leaf_index l i ->
  me:principal ->
  t:treekem bytes l i{treekem_invariant t} -> p_priv:treekem_priv bytes l i li{treekem_priv_invariant t p_priv} ->
  tr:trace ->
  Lemma
  (requires treekem_priv_state_pred tr me p_priv)
  (ensures (
    match get_private_key t p_priv with
    | Success node_sk ->
      is_node_sk_for_leaf_pk tr me (hpke_pk (get_path_leaf p_priv)) node_sk
    | _ -> True
  ))
let rec get_private_key_proof #cinvs #l #i #li me t p_priv tr =
  match t, p_priv with
  | TLeaf (Some _), PLeaf sk ->
    ()
  | TNode (Some pn) _ _, PNode opt_sk _ ->
    if li < pow2 32 && List.Tot.mem li pn.unmerged_leaves then (
      treekem_priv_state_pred_leaf me p_priv tr
    ) else ()
  | TNode None left right, PNode _ p_next ->
    let (child, _) = get_child_sibling t li in
    get_private_key_proof me child p_next tr

val pathkem_good_weak:
  {|crypto_invariants|} ->
  #l:nat -> #i:tree_index l -> #li:leaf_index l i ->
  pathkem bytes l i li ->
  trace ->
  prop
let pathkem_good_weak #cinvs #l #i #li p tr =
  is_well_formed_prefix (ps_path (ps_treekem_leaf) (ps_option ps_update_path_node_nt) l i li) (bytes_invariant tr) p

#push-options "--z3rlimit 100"
val get_path_secret_proof:
  {|crypto_invariants|} ->
  #l:nat -> #i:tree_index l -> #my_li:leaf_index l i -> #li:leaf_index l i{my_li <> li} ->
  me:principal ->
  t:treekem bytes l i{treekem_invariant t} -> p_priv:treekem_priv bytes l i my_li{treekem_priv_invariant t p_priv} ->
  p_upd:pathkem bytes l i li{check_update_path_ciphertexts_lengthes t p_upd /\ path_filtering_weak_ok t p_upd} -> group_context:group_context_nt bytes ->
  tr:trace ->
  Lemma
  (requires
    is_well_formed _ (bytes_invariant tr) group_context /\
    treekem_priv_state_pred tr me p_priv /\
    pathkem_good_weak p_upd tr /\
    has_mls_treekem_invariants
  )
  (ensures (
    match get_path_secret t p_priv p_upd group_context with
    | Success (path_secret, _) -> (
      decoded_path_secret_good me (hpke_pk (get_path_leaf p_priv)) path_secret tr
    )
    | _ -> True
  ))
let rec get_path_secret_proof #cinvs #l #i #my_li #li me t p_priv p_upd group_context tr =
  match t, p_priv, p_upd with
  | TNode _ _ _, PNode _ p_priv_next, PNode opt_upn p_upd_next ->
    if is_left_leaf my_li = is_left_leaf li then (
      let (child, _) = get_child_sibling t li in
      get_path_secret_proof me child (p_priv_next <: treekem_priv bytes (l-1) _ my_li) (p_upd_next <: pathkem bytes (l-1) _ li) group_context tr
    ) else (
      match opt_upn with
      | Some upn -> (
        if not (Success? (get_path_secret t p_priv p_upd group_context)) then ()
        else (
          let (_, sibling) = get_child_sibling t li in
          let my_index = resolution_index sibling my_li in
          let my_ciphertext = List.Tot.index upn.encrypted_path_secret my_index in
          let Success my_private_key = get_private_key sibling (PNode?.next p_priv) in
          let Success path_secret = decrypt_with_label #bytes my_private_key "UpdatePathNode" (serialize _ group_context) my_ciphertext.kem_output my_ciphertext.ciphertext in
          get_private_key_proof me sibling (PNode?.next p_priv) tr;
          List.Tot.lemma_index_memP upn.encrypted_path_secret my_index;
          for_allP_eq (is_well_formed_prefix (ps_hpke_ciphertext_nt) (bytes_invariant tr)) upn.encrypted_path_secret;
          serialize_wf_lemma _ (bytes_invariant tr) group_context;
          bytes_invariant_decrypt_with_label mls_hpke_updatepathnode_pred "MLS.NodeHpkeKey" empty tr my_private_key "UpdatePathNode" (serialize _ group_context) my_ciphertext.kem_output my_ciphertext.ciphertext;
          FStar.Classical.move_requires_3 has_usage_publishable tr path_secret (KdfExpandKey "MLS.PathSecret" empty)
        )
      )
      | None -> (
        let (_, sibling) = get_child_sibling t li in
        MLS.TreeCommon.Lemmas.is_tree_empty_leaf_at sibling my_li;
        assert(False)
      )
    )
#pop-options

val derive_next_path_secret_proof_weak:
  {|crypto_invariants|} ->
  me:principal -> my_leaf_pk:bytes ->
  path_secret:bytes ->
  tr:trace ->
  Lemma
  (requires
    decoded_path_secret_good me my_leaf_pk path_secret tr /\
    has_mls_treekem_invariants
  )
  (ensures (
    match derive_next_path_secret path_secret with
    | Success next_path_secret -> (
      decoded_path_secret_good me my_leaf_pk next_path_secret tr
    )
    | _ -> True
  ))
let derive_next_path_secret_proof_weak #cinvs me my_leaf_pk path_secret tr =
  match derive_next_path_secret path_secret with
  | Success next_path_secret -> (
    eliminate exists data. path_secret `has_usage tr` (KdfExpandKey "MLS.PathSecret" data)
    returns decoded_path_secret_good me my_leaf_pk next_path_secret tr
    with _. (
      expand_with_label_lemma tr "MLS.PathSecret" expand_usage_path_secret_path path_secret (KdfExpandKey "MLS.PathSecret" data) "path" empty (kdf_length #bytes);
      expand_usage_path_secret_path.get_label_lemma tr (KdfExpandKey "MLS.PathSecret" data) (get_label tr path_secret) empty (kdf_length #bytes)
    )
  )
  | _ -> ()

val derive_keypair_from_path_secret_proof_weak:
  {|crypto_invariants|} ->
  me:principal -> my_leaf_pk:bytes ->
  path_secret:bytes ->
  tr:trace ->
  Lemma
  (requires
    decoded_path_secret_good me my_leaf_pk path_secret tr /\
    has_mls_treekem_invariants
  )
  (ensures (
    match derive_keypair_from_path_secret path_secret with
    | Success (sk, pk) -> (
      is_node_sk_for_leaf_pk tr me my_leaf_pk sk
    )
    | _ -> True
  ))
let derive_keypair_from_path_secret_proof_weak #cinvs me my_leaf_pk path_secret tr =
  match derive_keypair_from_path_secret path_secret with
  | Success (sk, pk) -> (
    eliminate exists data. path_secret `has_usage tr` (KdfExpandKey "MLS.PathSecret" data)
    returns is_node_sk_for_leaf_pk tr me my_leaf_pk sk
    with _. (
      expand_with_label_lemma tr "MLS.PathSecret" expand_usage_path_secret_node path_secret (KdfExpandKey "MLS.PathSecret" data) "node" empty (kdf_length #bytes)
    )
  )
  | _ -> ()

#push-options "--z3rlimit 25"
val path_apply_path_proof:
  {|crypto_invariants|} ->
  #l:nat -> #i:tree_index l -> #li:leaf_index l i ->
  me:principal ->
  t:treekem bytes l i -> p_priv:treekem_priv bytes l i li ->
  path_secret:bytes -> path_node_level:path_secret_level l ->
  tr:trace ->
  Lemma
  (requires
    treekem_priv_state_pred tr me p_priv /\
    decoded_path_secret_good me (hpke_pk (get_path_leaf p_priv)) path_secret tr /\
    has_mls_treekem_invariants
  )
  (ensures (
    match path_apply_path t p_priv path_secret path_node_level with
    | Success (res_p_priv, path_secret_n) -> (
      treekem_priv_state_pred tr me res_p_priv /\
      decoded_path_secret_good me (hpke_pk (get_path_leaf p_priv)) path_secret_n tr /\
      get_path_leaf res_p_priv == get_path_leaf p_priv
    )
    | _ -> True
  ))
let rec path_apply_path_proof #cinvs #l #i #li me t p_priv path_secret path_node_level tr =
  let TNode opt_pn _ _, PNode _ p_priv_next = t, p_priv in
  if not (Success? (path_apply_path t p_priv path_secret path_node_level)) then ()
  else (
    let (child, sibling) = get_child_sibling t li in
    let Success (new_p_priv_next, path_secret) = (
      if path_node_level = l  then (
        return (p_priv_next, path_secret)
      ) else (
        path_apply_path_proof me child p_priv_next path_secret path_node_level tr;
        path_apply_path child p_priv_next path_secret path_node_level
      )
    ) in
    assert(treekem_priv_state_pred tr me new_p_priv_next);
    if not (is_tree_empty sibling) then (
      let Success (sk, pk) = derive_keypair_from_path_secret path_secret in
      let Success new_path_secret = derive_next_path_secret path_secret in
      derive_keypair_from_path_secret_proof_weak me (hpke_pk (get_path_leaf p_priv)) path_secret tr;
      derive_next_path_secret_proof_weak me (hpke_pk (get_path_leaf p_priv)) path_secret tr
    ) else ()
  )
#pop-options

val is_above_treesync_root:
  #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l ->
  treesync bytes tkt l i -> leaf_index l i ->
  prop
let rec is_above_treesync_root #bytes #bl #tkt #l #i t li =
  match t with
  | TLeaf _ -> True
  | TNode (Some pn) _ _ ->
    let (child, sibling) = get_child_sibling t li in
    pn.unmerged_leaves = [] /\
    pn.parent_hash == MLS.TreeSync.ParentHash.root_parent_hash #bytes /\
    ~(is_tree_empty sibling)
  | TNode None _ _ ->
    let (child, sibling) = get_child_sibling t li in
    is_above_treesync_root child li

#push-options "--fuel 1 --ifuel 1"
val find_lca:
  #l:nat -> #i:tree_index l ->
  li1:leaf_index l i -> li2:leaf_index l i{li1 =!= li2} ->
  path_secret_level l
let rec find_lca #l #i li1 li2 =
  match is_left_leaf li1, is_left_leaf li2 with
  | true, true ->
    find_lca #(l-1) #(left_index i) li1 li2
  | false, false ->
    find_lca #(l-1) #(right_index i) li1 li2
  | _ -> l
#pop-options

#push-options "--z3rlimit 25"
val get_path_secret_find_lca_eq:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #l:nat -> #i:tree_index l -> #my_li:leaf_index l i -> #li:leaf_index l i{my_li <> li} ->
  t:treekem bytes l i{treekem_invariant t} -> p_priv:treekem_priv bytes l i my_li{treekem_priv_invariant t p_priv} ->
  p_upd:pathkem bytes l i li{check_update_path_ciphertexts_lengthes t p_upd /\ path_filtering_weak_ok t p_upd} -> group_context:group_context_nt bytes ->
  Lemma
  (ensures (
    match get_path_secret t p_priv p_upd group_context with
    | Success (_, level) -> level == find_lca my_li li
    | _ -> True
  ))
let rec get_path_secret_find_lca_eq #bytes #cb #l #i #my_li #li t p_priv p_upd group_context =
  let PNode _ p_priv_next, PNode opt_upn p_upd_next = p_priv, p_upd in
  if is_left_leaf my_li = is_left_leaf li then (
    let (child, _) = get_child_sibling t li in
    get_path_secret_find_lca_eq child (p_priv_next <: treekem_priv bytes (l-1) _ my_li) (p_upd_next <: pathkem bytes (l-1) _ li) group_context;
    ()
  ) else (
    match opt_upn with
    | Some _ -> ()
    | None -> (
      let (_, sibling) = get_child_sibling t li in
      MLS.TreeCommon.Lemmas.is_tree_empty_leaf_at sibling my_li;
      assert(False)
    )
  )
#pop-options

#push-options "--fuel 0 --ifuel 0"
val path_apply_path_commit_secret_proof_aux:
  {|crypto_invariants|} ->
  #l:nat -> #i:tree_index l ->
  ts:treesync bytes tkt l i ->
  path_secret:bytes -> sk:hpke_private_key bytes -> pk:hpke_public_key bytes ->
  group_id:mls_bytes bytes ->
  tr:trace ->
  Lemma
  (requires
    node_sk_label ts group_id `can_flow tr` (get_hpke_sk_label tr pk) /\
    derive_keypair_from_path_secret path_secret == Success (sk, pk) /\
    is_root_node_pk tr pk /\
    has_mls_treekem_invariants
  )
  (ensures (
    match derive_next_path_secret path_secret with
    | Success commit_secret ->
      node_sk_label ts group_id `can_flow tr` (get_label tr commit_secret)
    | _ -> True
  ))
let path_apply_path_commit_secret_proof_aux #cinvs #l #i ts path_secret sk pk group_id tr =
  match derive_next_path_secret path_secret with
  | Success commit_secret -> (
      eliminate exists path_secret' sk'.
        length pk == hpke_public_key_length #bytes /\
        MLS.TreeKEM.Operations.derive_keypair_from_path_secret path_secret' == MLS.Result.Success (sk', pk) /\
        bytes_invariant tr path_secret' /\
        path_secret' `has_usage tr` (KdfExpandKey "MLS.PathSecret" (serialize path_secret_usage []))
      returns
        bytes_invariant tr commit_secret /\
        node_sk_label ts group_id `can_flow tr` (get_label tr commit_secret)
      with _. (
        reveal_opaque (`%kem_pk) (kem_pk);
        reveal_opaque (`%DY.Core.kdf_expand) (DY.Core.kdf_expand);
        assert(path_secret == path_secret');
        expand_with_label_lemma tr "MLS.PathSecret" expand_usage_path_secret_path path_secret (KdfExpandKey "MLS.PathSecret" (serialize path_secret_usage [])) "path" empty (kdf_length #bytes);
        expand_with_label_lemma tr "MLS.PathSecret" expand_usage_path_secret_node path_secret (KdfExpandKey "MLS.PathSecret" (serialize path_secret_usage [])) "node" empty (kdf_length #bytes)
      )
  )
  | _ -> ()
#pop-options

val is_above_treesync_root_apply_path:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l -> #li:leaf_index l i ->
  t:treesync bytes tkt l i -> p:pathsync bytes tkt l i li ->
  Lemma
  (requires MLS.NetworkBinder.Properties.path_filtering_ok t p)
  (ensures (
    match MLS.TreeSync.Operations.apply_path_aux t p (MLS.TreeSync.ParentHash.root_parent_hash #bytes) with
    | Success res -> is_above_treesync_root res li
    | _ -> True
  ))
let rec is_above_treesync_root_apply_path #bytes #cb #tkt #l #i #li t p =
  match t, p with
  | TLeaf _, PLeaf lp -> ()
  | TNode _ left right, PNode opt_ext_content p_next -> (
    let (child, sibling) = get_child_sibling t li in
    match opt_ext_content with
    | Some _ -> ()
    | None -> is_above_treesync_root_apply_path child p_next
  )

val committer_exists_tree_apply_path:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #l:nat -> #i:tree_index l -> #li:leaf_index l i ->
  t:treekem bytes l i -> p:pathkem bytes l i li ->
  Lemma (leaf_at (tree_apply_path t p) li == Some (get_path_leaf p))
let rec committer_exists_tree_apply_path #bytes #cb #l #i #li t p =
  if l = 0 then ()
  else (
    let (child, sibling) = get_child_sibling t li in
    let PNode _ p_next = p in
    committer_exists_tree_apply_path child p_next
  )

#push-options "--z3rlimit 200"
#restart-solver
val path_apply_path_commit_secret_proof:
  {|crypto_invariants|} ->
  #l:nat -> #i:tree_index l -> #li:leaf_index l i ->
  me:principal ->
  ts:treesync bytes tkt l i -> tk:treekem bytes l i -> p_priv:treekem_priv bytes l i li ->
  path_secret_0:bytes ->
  committer_li:leaf_index l i -> group_id:mls_bytes bytes ->
  tr:trace ->
  Lemma
  (requires
    treekem_priv_state_pred tr me p_priv /\
    decoded_path_secret_good me (hpke_pk (get_path_leaf p_priv)) path_secret_0 tr /\
    li =!= committer_li /\
    is_above_treesync_root ts committer_li /\
    Some? (leaf_at tk committer_li) /\
    treesync_treekem_rel ts tk /\
    all_tree_keys_good ts group_id tr /\
    decoded_path_secret_good me (hpke_pk (get_path_leaf p_priv)) path_secret_0 tr /\
    has_mls_treekem_invariants
  )
  (ensures (
    match path_apply_path tk p_priv path_secret_0 (find_lca li committer_li) with
    | Success (res_p_priv, commit_secret) -> (
      node_sk_label ts group_id `can_flow tr` get_label tr commit_secret
    )
    | _ -> True
  ))
let rec path_apply_path_commit_secret_proof #cinvs #l #i #li me ts tk p_priv path_secret_0 committer_li group_id tr =
  let TNode opt_pn _ _, PNode _ p_priv_next = tk, p_priv in
  if not (Success? (path_apply_path tk p_priv path_secret_0 (find_lca li committer_li))) then ()
  else (
    let (child_s, sibling_s) = get_child_sibling ts li in
    let (child_k, sibling_k) = get_child_sibling tk li in
    if is_tree_empty sibling_k then (
      if find_lca li committer_li = l then (
        MLS.TreeCommon.Lemmas.is_tree_empty_leaf_at sibling_k committer_li;
        assert(False)
      ) else (
        treesync_treekem_rel_is_tree_empty sibling_s sibling_k;
        path_apply_path_commit_secret_proof me child_s child_k p_priv_next path_secret_0 committer_li group_id tr;
        node_sk_label_aux_empty sibling_s group_id YesCommitter tr
      )
    ) else (
      let Success (_, path_secret) = (
        if find_lca li committer_li = l  then (
          return (p_priv_next, path_secret_0)
        ) else (
          path_apply_path child_k p_priv_next path_secret_0 (find_lca li committer_li)
        )
      ) in
      let _: squash (decoded_path_secret_good me (hpke_pk (get_path_leaf p_priv)) path_secret tr) = (
        if find_lca li committer_li = l  then ()
        else (
          path_apply_path_proof me child_k p_priv_next path_secret_0 (find_lca li committer_li) tr
        )
      ) in
      let Success (sk, pk) = derive_keypair_from_path_secret path_secret in
      assert(MLS.TreeSync.Invariants.ParentHash.get_parent_hash_of ts == MLS.TreeSync.ParentHash.root_parent_hash #bytes);
      MLS.TreeSync.Proofs.ParentHashGuarantees.canonicalize_unmerged_leaves_idempotent ts;
      assert(is_root_node_pk tr pk \/ node_sk_label ts group_id `can_flow tr` public);
      FStar.Classical.move_requires (path_apply_path_commit_secret_proof_aux ts path_secret sk pk group_id) tr
    )
  )
#pop-options
