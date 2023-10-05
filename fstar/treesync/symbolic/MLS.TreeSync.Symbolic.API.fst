module MLS.TreeSync.Symbolic.API

open Comparse
open MLS.Result
open MLS.Crypto
open GlobalRuntimeLib
open LabeledRuntimeAPI
open MLS.Tree
open MLS.NetworkTypes
open MLS.TreeSync.NetworkTypes
open MLS.TreeSync.Types
open MLS.TreeSync.Operations
open MLS.TreeSync.Invariants.UnmergedLeaves
open MLS.TreeSync.Invariants.AuthService
open MLS.TreeSync.Proofs.ParentHashGuarantees
open MLS.TreeSync.API
open MLS.Symbolic
open MLS.TreeSync.Symbolic.API.GroupManager
open MLS.TreeSync.Symbolic.API.KeyPackageManager
open MLS.TreeSync.Symbolic.API.Sessions
open MLS.TreeSync.Symbolic.API.IsWellFormedInvariant
open MLS.TreeSync.Symbolic.LeafNodeSignature
open MLS.TreeSync.Symbolic.AuthServiceCache
open MLS.TreeSync.Symbolic.IsWellFormed

#set-options "--fuel 0 --ifuel 0"

(*** Utility functions ***)

val guard: pr:preds -> b:bool -> LCrypto unit pr
  (requires fun t0 -> True)
  (ensures fun t0 _ t1 -> t1 == t0 /\ b)
let guard pr b =
  if b then ()
  else error "guard failed"

#push-options "--ifuel 1"
val extract_result: #a:Type -> pr:preds -> x:MLS.Result.result a -> LCrypto a pr
  (requires fun t0 -> True)
  (ensures fun t0 res t1 -> t1 == t0 /\ x == Success res)
let extract_result #a pr x =
  match x with
  | MLS.Result.Success y -> y
  | MLS.Result.InternalError s -> error "extract_result: internal error '" ^ s ^ "'"
  | MLS.Result.ProtocolError s -> error "extract_result: protocol error '" ^ s ^ "'"
#pop-options

val has_treesync_invariants: treekem_types dy_bytes -> preds -> prop
let has_treesync_invariants tkt pr =
  has_treesync_public_state_invariant tkt pr /\
  has_treesync_private_state_invariant pr /\
  has_group_manager_invariant pr /\
  has_key_package_manager_invariant tkt pr /\
  has_as_cache_invariant pr /\
  has_leaf_node_tbs_invariant tkt pr.global_usage

val get_token_for:
  pr:preds -> p:principal -> as_session:nat ->
  inp:as_input dy_bytes ->
  LCrypto dy_as_token pr
  (requires fun t0 -> has_as_cache_invariant pr)
  (ensures fun t0 token t1 ->
    (dy_asp pr.global_usage (trace_len t0)).credential_ok inp token /\
    t1 == t0
  )
let get_token_for pr p as_session (verification_key, credential) =
  let now = global_timestamp () in
  let { who; usg; time; } = find_verified_credential pr p as_session ({ verification_key; credential; }) in
  guard pr (usg = "MLS.LeafSignKey");
  { who; time; }

#push-options "--fuel 1 --ifuel 1"
val get_tokens_for:
  pr:preds -> p:principal -> as_session:nat ->
  inps:list (option (as_input dy_bytes)) ->
  LCrypto (list (option dy_as_token)) pr
  (requires fun t0 -> has_as_cache_invariant pr)
  (ensures fun t0 tokens t1 ->
    List.Tot.length tokens == List.Tot.length inps /\
    (forall i.
      match (List.Tot.index inps i), (List.Tot.index tokens i) with
      | None, None -> True
      | Some inp, Some token -> (dy_asp pr.global_usage (trace_len t0)).credential_ok inp token
      | _, _ -> False
    ) /\
    t1 == t0
  )
let rec get_tokens_for pr p as_session inps =
  let now = global_timestamp () in
  match inps with
  | [] -> []
  | inp_head::inps_tail ->
    let token_head =
      match inp_head with
      | Some inp -> Some (get_token_for pr p as_session inp)
      | None -> None
    in
    let tokens_tail = get_tokens_for pr p as_session inps_tail in
    let tokens = token_head::tokens_tail in
    // An assert is needed to trigger the `forall`
    assert(forall i. i <> 0 ==> List.Tot.index inps i == List.Tot.index inps_tail (i-1));
    tokens
#pop-options

(*** Process proposals ***)

val create:
  #tkt:treekem_types dy_bytes ->
  pr:preds -> p:principal -> as_session:nat -> gmgr_session:nat ->
  group_id:mls_bytes dy_bytes -> ln:leaf_node_nt dy_bytes tkt -> secret_session:nat ->
  LCrypto unit pr
  (requires fun t0 ->
    is_publishable pr.global_usage (trace_len t0) group_id /\
    is_well_formed _ (is_publishable pr.global_usage (trace_len t0)) ln /\
    has_treesync_invariants tkt pr
  )
  (ensures fun t0 () t1 -> trace_len t1 == trace_len t0 + 2)
let create #tkt pr p as_session gmgr_session group_id ln secret_session =
  let now = global_timestamp () in
  let create_pend = extract_result pr (prepare_create #dy_bytes #crypto_dy_bytes group_id ln) in
  let token = get_token_for pr p as_session create_pend.as_input in
  let token: as_token_for (dy_asp pr.global_usage now) create_pend.as_input = token in
  let st = finalize_create create_pend token in
  is_well_formed_finalize_create (is_publishable pr.global_usage now) create_pend token;
  let si_public = new_public_treesync_state pr p now _ st in
  let group_sessions = { si_public; si_private = secret_session; } in
  add_new_group_sessions pr p gmgr_session group_id group_sessions

val welcome:
  #tkt:treekem_types dy_bytes ->
  pr:preds -> p:principal -> as_session:nat -> gmgr_session:nat -> kpmgr_session:nat ->
  my_key_package:key_package_nt dy_bytes tkt ->
  group_id:mls_bytes dy_bytes -> l:nat -> t:treesync dy_bytes tkt l 0 ->
  LCrypto unit pr
  (requires fun t0 ->
    is_publishable pr.global_usage (trace_len t0) group_id /\
    is_well_formed _ (is_publishable pr.global_usage (trace_len t0)) t /\
    has_treesync_invariants tkt pr
  )
  (ensures fun t0 () t1 -> trace_len t1 == trace_len t0 + 2)
let welcome #tkt pr p as_session gmgr_session kpmgr_session my_key_package group_id l t =
  let now = global_timestamp () in
  let welcome_pend = extract_result pr (prepare_welcome #dy_bytes #crypto_dy_bytes group_id t) in
  welcome_pend.as_inputs_proof;
  let tokens = get_tokens_for pr p as_session welcome_pend.as_inputs in
  let tokens: tokens_for_welcome (dy_asp pr.global_usage now) welcome_pend = tokens in
  let st = finalize_welcome welcome_pend tokens in
  is_well_formed_finalize_welcome (is_publishable pr.global_usage now) welcome_pend tokens;
  let si_public = new_public_treesync_state pr p now _ st in
  let si_private = (find_key_package_secret_session tkt pr p kpmgr_session my_key_package).si_private in
  let group_sessions = { si_public; si_private; } in
  add_new_group_sessions pr p gmgr_session group_id group_sessions

val add:
  #tkt:treekem_types dy_bytes ->
  pr:preds -> p:principal -> as_session:nat -> gmgr_session:nat ->
  group_id:mls_bytes dy_bytes -> ln:leaf_node_nt dy_bytes tkt ->
  LCrypto nat pr
  (requires fun t0 ->
    is_well_formed _ (is_publishable pr.global_usage (trace_len t0)) ln /\
    has_treesync_invariants tkt pr
  )
  (ensures fun t0 _ t1 -> trace_len t1 == trace_len t0 + 1)
let add #tkt pr p as_session gmgr_session group_id ln =
  let now = global_timestamp () in
  let group_session = find_group_sessions pr p gmgr_session group_id in
  let (|group_id, st|) = get_public_treesync_state #tkt pr p group_session.si_public now in

  let add_pend = extract_result pr (prepare_add st ln) in
  let token = get_token_for pr p as_session add_pend.as_input in
  let (new_st, new_leaf_index) = extract_result pr (finalize_add add_pend token) in
  is_well_formed_finalize_add (is_publishable pr.global_usage now) add_pend token;
  set_public_treesync_state pr p group_session.si_public now _ new_st;
  new_leaf_index

val update:
  #tkt:treekem_types dy_bytes ->
  pr:preds -> p:principal -> as_session:nat -> gmgr_session:nat ->
  group_id:mls_bytes dy_bytes -> ln:leaf_node_nt dy_bytes tkt -> li:nat ->
  LCrypto unit pr
  (requires fun t0 ->
    is_well_formed _ (is_publishable pr.global_usage (trace_len t0)) ln /\
    has_treesync_invariants tkt pr
  )
  (ensures fun t0 () t1 -> trace_len t1 == trace_len t0 + 1)
let update #tkt pr p as_session gmgr_session group_id ln li =
  let now = global_timestamp () in
  let group_session = find_group_sessions pr p gmgr_session group_id in
  let (|group_id, st|) = get_public_treesync_state #tkt pr p group_session.si_public now in
  guard pr (li < pow2 st.levels);
  let update_pend = extract_result pr (prepare_update st ln li) in
  let token = get_token_for pr p as_session update_pend.as_input in
  let new_st = finalize_update update_pend token in
  is_well_formed_finalize_update (is_publishable pr.global_usage now) update_pend token;
  set_public_treesync_state pr p group_session.si_public now _ new_st

val remove:
  #tkt:treekem_types dy_bytes ->
  pr:preds -> p:principal -> as_session:nat -> gmgr_session:nat ->
  group_id:mls_bytes dy_bytes -> li:nat ->
  LCrypto unit pr
  (requires fun t0 ->
    has_treesync_invariants tkt pr
  )
  (ensures fun t0 () t1 -> trace_len t1 == trace_len t0 + 1)
let remove #tkt pr p as_session gmgr_session group_id li =
  let now = global_timestamp () in
  let group_session = find_group_sessions pr p gmgr_session group_id in
  let (|group_id, st|) = get_public_treesync_state #tkt pr p group_session.si_public now in
  guard pr (li < pow2 st.levels);
  let remove_pend = extract_result pr (prepare_remove st li) in
  let new_st = finalize_remove remove_pend in
  is_well_formed_finalize_remove (is_publishable pr.global_usage now) remove_pend;
  set_public_treesync_state pr p group_session.si_public now _ new_st

#push-options "--z3rlimit 25"
val commit:
  #tkt:treekem_types dy_bytes -> #l:nat -> #li:leaf_index l 0 ->
  pr:preds -> p:principal -> as_session:nat -> gmgr_session:nat ->
  group_id:mls_bytes dy_bytes -> path:pathsync dy_bytes tkt l 0 li ->
  LCrypto unit pr
  (requires fun t0 ->
    is_well_formed _ (is_publishable pr.global_usage (trace_len t0)) path /\
    has_treesync_invariants tkt pr
  )
  (ensures fun t0 () t1 -> trace_len t1 == trace_len t0 + 1)
let commit #tkt #l #li pr p as_session gmgr_session group_id path =
  let now = global_timestamp () in
  let group_session = find_group_sessions pr p gmgr_session group_id in
  let (|group_id, st|) = get_public_treesync_state #tkt pr p group_session.si_public now in
  guard pr (l = st.levels);
  let commit_pend = extract_result pr (prepare_commit st path) in
  let token = get_token_for pr p as_session commit_pend.as_input in
  let new_st = extract_result pr (finalize_commit commit_pend token) in
  is_well_formed_finalize_commit (is_publishable pr.global_usage now) commit_pend token;
  set_public_treesync_state pr p group_session.si_public now _ new_st
#pop-options

(*** Create signature keypair ***)

val create_signature_keypair:
  pr:preds -> p:principal ->
  LCrypto (nat & signature_public_key_nt dy_bytes) pr
  (requires fun t0 ->
    has_treesync_private_state_invariant pr
  )
  (ensures fun t0 (private_si, verification_key) t1 ->
    is_verification_key pr.global_usage "MLS.LeafSignKey" (readers [p_id p]) (trace_len t0) verification_key /\
    trace_len t1 == trace_len t0 + 2
  )
let create_signature_keypair pr p =
  let (|now, signature_key|) = rand_gen #pr (readers [p_id p]) (sig_usage "MLS.LeafSignKey") in
  let verification_key = LabeledCryptoAPI.vk #pr.global_usage #now #(readers [p_id p]) signature_key in
  guard pr (length (signature_key <: dy_bytes) < pow2 30);
  guard pr (length (verification_key <: dy_bytes) < pow2 30);
  let private_state: treesync_private_state = {signature_key;} in
  let private_si = new_private_treesync_state pr p private_state in
  (private_si, verification_key)

(*** Sign stuff ***)

val external_path_has_event_later:
  #tkt:treekem_types dy_bytes ->
  #l:nat -> #li:leaf_index l 0 ->
  prin:principal -> time0:timestamp -> time1:timestamp ->
  t:treesync dy_bytes tkt l 0 -> p:external_pathsync dy_bytes tkt l 0 li -> group_id:mls_bytes dy_bytes ->
  Lemma
  (requires
    external_path_has_event prin time0 t p group_id /\
    time0 <$ time1
  )
  (ensures external_path_has_event prin time1 t p group_id)
let external_path_has_event_later #tkt #l #li prin time0 time1 t p group_id =
  let Success auth_p = external_path_to_path_nosig #dy_bytes #crypto_dy_bytes t p group_id in
  path_is_parent_hash_valid_external_path_to_path_nosig #dy_bytes #crypto_dy_bytes t p group_id;
  apply_path_aux_compute_leaf_parent_hash_from_path_both_succeed #dy_bytes #crypto_dy_bytes t auth_p (MLS.TreeSync.ParentHash.root_parent_hash #dy_bytes);
  for_allP_eq (tree_has_event prin time0 group_id) (path_to_tree_list #dy_bytes #crypto_dy_bytes t auth_p);
  for_allP_eq (tree_has_event prin time1 group_id) (path_to_tree_list #dy_bytes #crypto_dy_bytes t auth_p)

#push-options "--z3rlimit 25"
val authenticate_path:
  #tkt:treekem_types dy_bytes -> #l:nat -> #li:leaf_index l 0 ->
  pr:preds -> p:principal -> gmgr_session:nat ->
  group_id:mls_bytes dy_bytes -> tree:treesync dy_bytes tkt l 0 -> path:external_pathsync dy_bytes tkt l 0 li ->
  LCrypto (pathsync dy_bytes tkt l 0 li) pr
  (requires fun t0 ->
    external_path_has_event p (trace_len t0) tree path group_id /\
    is_well_formed _ (is_publishable pr.global_usage (trace_len t0)) path /\
    has_treesync_invariants tkt pr
  )
  (ensures fun t0 auth_path t1 ->
    is_well_formed _ (is_publishable pr.global_usage (trace_len t1)) auth_path /\
    trace_len t1 == trace_len t0 + 1
  )
let authenticate_path #tkt #l pr p gmgr_session group_id tree path =
  let (|now0, signature_nonce|) = rand_gen #pr (readers [p_id p]) (sig_usage "???") in
  let now1 = global_timestamp () in
  let group_session = find_group_sessions pr p gmgr_session group_id in
  let (|group_id', st|) = get_public_treesync_state #tkt pr p group_session.si_public now1 in
  let private_st = get_private_treesync_state pr p group_session.si_private in
  guard pr (
    (group_id = group_id') &&
    (l = st.levels) &&
    (tree = st.tree) &&
    length (signature_nonce <: dy_bytes) >= sign_sign_min_entropy_length #dy_bytes &&
    (path_is_filter_valid #dy_bytes #crypto_dy_bytes tree path)
  );
  let auth_path = extract_result pr (external_path_to_path #dy_bytes #crypto_dy_bytes tree path group_id private_st.signature_key signature_nonce) in
  wf_weaken_lemma _ (is_publishable pr.global_usage now0) (is_publishable pr.global_usage now1) path;
  external_path_has_event_later p now0 now1 tree path group_id;
  is_msg_external_path_to_path pr.global_usage p SecrecyLabels.public now1 tree path group_id private_st.signature_key signature_nonce;
  auth_path
#pop-options

val authenticate_leaf_node_data_from_key_package:
  #tkt:treekem_types dy_bytes ->
  pr:preds -> p:principal ->
  si_private:nat ->
  ln_data:leaf_node_data_nt dy_bytes tkt ->
  LCrypto (leaf_node_nt dy_bytes tkt) pr
  (requires fun t0 ->
    ln_data.source == LNS_key_package /\
    is_well_formed_prefix (ps_leaf_node_data_nt tkt) (is_publishable pr.global_usage (trace_len t0)) ln_data /\
    leaf_node_has_event p (trace_len t0) ({data = ln_data; group_id = (); leaf_index = ();}) /\
    has_treesync_invariants tkt pr
  )
  (ensures fun t0 ln t1 ->
    is_well_formed _ (is_publishable pr.global_usage (trace_len t1)) ln /\
    trace_len t1 == trace_len t0 + 1
  )
let authenticate_leaf_node_data_from_key_package #tkt pr p si_private ln_data =
  let (|now0, signature_nonce|) = rand_gen #pr (readers [p_id p]) (sig_usage "???") in
  let now1 = global_timestamp () in
  let private_st = get_private_treesync_state pr p si_private in
  guard pr (
    (length (signature_nonce <: dy_bytes) = sign_sign_min_entropy_length #dy_bytes)
  );
  is_well_formed_prefix_weaken (ps_leaf_node_data_nt tkt) (is_publishable pr.global_usage now0) (is_publishable pr.global_usage now1) ln_data;
  let res = extract_result pr (sign_leaf_node_data_key_package #dy_bytes #crypto_dy_bytes ln_data private_st.signature_key signature_nonce) in
  is_msg_sign_leaf_node_data_key_package pr.global_usage p SecrecyLabels.public now1 ln_data private_st.signature_key signature_nonce;
  res

val authenticate_leaf_node_data_from_update:
  #tkt:treekem_types dy_bytes ->
  pr:preds -> p:principal ->
  si_private:nat ->
  ln_data:leaf_node_data_nt dy_bytes tkt -> group_id:mls_bytes dy_bytes -> leaf_index:nat_lbytes 4 ->
  LCrypto (leaf_node_nt dy_bytes tkt) pr
  (requires fun t0 ->
    ln_data.source == LNS_update /\
    is_well_formed_prefix (ps_leaf_node_data_nt tkt) (is_publishable pr.global_usage (trace_len t0)) ln_data /\
    is_publishable pr.global_usage (trace_len t0) group_id /\
    leaf_node_has_event p (trace_len t0) ({data = ln_data; group_id; leaf_index;}) /\
    tree_has_event p (trace_len t0) group_id (|0, leaf_index, TLeaf (Some ({data = ln_data; signature = empty #dy_bytes;} <: leaf_node_nt dy_bytes tkt))|) /\
    has_treesync_invariants tkt pr
  )
  (ensures fun t0 ln t1 ->
    is_well_formed _ (is_publishable pr.global_usage (trace_len t1)) ln /\
    trace_len t1 == trace_len t0 + 1
  )
let authenticate_leaf_node_data_from_update #tkt pr p si_private ln_data group_id leaf_index =
  let (|now0, signature_nonce|) = rand_gen #pr (readers [p_id p]) (sig_usage "???") in
  let now1 = global_timestamp () in
  let private_st = get_private_treesync_state pr p si_private in
  guard pr (
    (length (signature_nonce <: dy_bytes) >= sign_sign_min_entropy_length #dy_bytes)
  );
  is_well_formed_prefix_weaken (ps_leaf_node_data_nt tkt) (is_publishable pr.global_usage now0) (is_publishable pr.global_usage now1) ln_data;
  let res = extract_result pr (sign_leaf_node_data_update #dy_bytes #crypto_dy_bytes ln_data group_id leaf_index private_st.signature_key signature_nonce) in
  is_msg_sign_leaf_node_data_update pr.global_usage p SecrecyLabels.public now1 ln_data group_id leaf_index private_st.signature_key signature_nonce;
  res

(*** Trigger events ***)

val tree_event_triggerable: #tkt:treekem_types dy_bytes -> pr:preds -> p:principal -> time:timestamp -> group_id:mls_bytes dy_bytes -> (l:nat & i:tree_index l & treesync dy_bytes tkt l i) -> prop
let tree_event_triggerable pr p time group_id t =
  event_pred_at pr p time (tree_to_event group_id t)

val trigger_one_tree_event:
  #tkt:treekem_types dy_bytes ->
  pr:preds -> p:principal -> now:timestamp ->
  group_id:mls_bytes dy_bytes -> t:(l:nat & i:tree_index l & treesync dy_bytes tkt l i) ->
  squash (tree_event_triggerable pr p now group_id t) ->
  LCrypto unit pr
  (requires fun t0 -> now == trace_len t0)
  (ensures fun t0 () t1 ->
    did_event_occur_before p (trace_len t1) (tree_to_event group_id t) /\
    trace_len t1 == trace_len t0 + 1
  )
let trigger_one_tree_event #tkt pr p now group_id t proof =
  trigger_event #pr p (tree_to_event group_id t)

val trigger_tree_list_event_lemma:
  #tkt:treekem_types dy_bytes ->
  p:principal -> now:timestamp ->
  group_id:mls_bytes dy_bytes -> h:(l:nat & i:tree_index l & treesync dy_bytes tkt l i) -> t:tree_list dy_bytes tkt ->
  Lemma(tree_list_has_event p now group_id (h::t) <==> (tree_has_event p now group_id h /\ tree_list_has_event p now group_id t))
let trigger_tree_list_event_lemma #tkt p now group_id h t =
  let open FStar.Tactics in
  assert(tree_list_has_event p now group_id (h::t) == (
    tree_has_event p now group_id h /\
    tree_list_has_event p now group_id t
  )) by (
    norm [delta_only [`%tree_list_has_event; `%for_allP]; zeta; iota];
    trefl()
  )

#push-options "--fuel 1 --ifuel 1 --z3rlimit 25"
val trigger_tree_list_event:
  #tkt:treekem_types dy_bytes ->
  pr:preds -> p:principal -> now:timestamp ->
  group_id:mls_bytes dy_bytes -> tl:tree_list dy_bytes tkt ->
  proof_list:(i:nat{i < List.Tot.length tl} -> squash (tree_event_triggerable pr p (now+i) group_id (List.Tot.index tl i))) ->
  LCrypto unit pr
  (requires fun t0 -> now == trace_len t0)
  (ensures fun t0 () t1 ->
    tree_list_has_event p (trace_len t1) group_id tl /\
    trace_len t1 == trace_len t0 + (List.Tot.length tl)
  )
  (decreases tl)
let rec trigger_tree_list_event #tkt pr p now group_id tl event_tl_proof =
  match tl with
  | [] -> (
    normalize_term_spec (tree_list_has_event p now group_id tl)
  )
  | h::t -> (
    // I lost so much time finding that F* needs the following assert
    // WTF??? There is definitely a problem in SMT encoding
    assert(Cons?.tl tl == t);
    trigger_one_tree_event pr p now group_id h (event_tl_proof 0);
    trigger_tree_list_event pr p (now+1) group_id t (fun i -> event_tl_proof (i+1));
    let now_end = now + List.Tot.length tl in
    trigger_tree_list_event_lemma p now_end group_id h t
  )
#pop-options

val trigger_leaf_node_event:
  #tkt:treekem_types dy_bytes ->
  pr:preds -> p:principal ->
  ln_tbs:leaf_node_tbs_nt dy_bytes tkt ->
  LCrypto unit pr
  (requires fun t0 -> event_pred_at pr p (trace_len t0) (leaf_node_to_event ln_tbs))
  (ensures fun t0 () t1 ->
    leaf_node_has_event p (trace_len t1) ln_tbs /\
    trace_len t1 == trace_len t0 + 1
  )
let trigger_leaf_node_event #tkt pr p ln_tbs =
  trigger_event #pr p (leaf_node_to_event ln_tbs)
