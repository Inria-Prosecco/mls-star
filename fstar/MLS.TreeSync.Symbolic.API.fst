module MLS.TreeSync.Symbolic.API

open Comparse
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
open MLS.TreeSync.Symbolic.API.HasPreInvariant
open MLS.TreeSync.Symbolic.LeafNodeSignature
open MLS.TreeSync.Symbolic.AuthServiceCache
open MLS.TreeSync.Symbolic.IsValid

#set-options "--fuel 0 --ifuel 0"

(*** Utility functions ***)

val guard: pr:preds -> b:bool -> LCrypto unit pr
  (requires fun t0 -> True)
  (ensures fun t0 _ t1 -> t1 == t0 /\ b)
let guard pr b =
  if b then ()
  else error "guard failed"

#push-options "--ifuel 1"
val extract_result: #a:Type -> pr:preds -> MLS.Result.result a -> LCrypto a pr
  (requires fun t0 -> True)
  (ensures fun t0 _ t1 -> t1 == t0)
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
    value_has_pre (is_publishable pr.global_usage (trace_len t0)) ln /\
    has_treesync_invariants tkt pr
  )
  (ensures fun t0 () t1 -> trace_len t1 == trace_len t0 + 2)
let create #tkt pr p as_session gmgr_session group_id ln secret_session =
  let now = global_timestamp () in
  let create_pend = extract_result pr (prepare_create group_id ln) in
  let token = get_token_for pr p as_session create_pend.as_input in
  let token: as_token_for (dy_asp pr.global_usage now) create_pend.as_input = token in
  let st = finalize_create create_pend token in
  finalize_create_has_pre (is_publishable pr.global_usage now) create_pend token;
  let si_public = new_public_treesync_state pr p now st in
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
    treesync_has_pre (is_publishable pr.global_usage (trace_len t0)) t /\
    has_treesync_invariants tkt pr
  )
  (ensures fun t0 () t1 -> trace_len t1 == trace_len t0 + 2)
let welcome #tkt pr p as_session gmgr_session kpmgr_session my_key_package group_id l t =
  let now = global_timestamp () in
  let welcome_pend = extract_result pr (prepare_welcome group_id t) in
  welcome_pend.as_inputs_proof;
  let tokens = get_tokens_for pr p as_session welcome_pend.as_inputs in
  let tokens: tokens_for_welcome (dy_asp pr.global_usage now) welcome_pend = tokens in
  let st = finalize_welcome welcome_pend tokens in
  finalize_welcome_has_pre (is_publishable pr.global_usage now) welcome_pend tokens;
  let si_public = new_public_treesync_state pr p now st in
  let si_private = (find_key_package_secret_session tkt pr p kpmgr_session my_key_package).si_private in
  let group_sessions = { si_public; si_private; } in
  add_new_group_sessions pr p gmgr_session group_id group_sessions

val add:
  #tkt:treekem_types dy_bytes ->
  pr:preds -> p:principal -> as_session:nat -> gmgr_session:nat ->
  group_id:mls_bytes dy_bytes -> ln:leaf_node_nt dy_bytes tkt ->
  LCrypto nat pr
  (requires fun t0 ->
    value_has_pre (is_publishable pr.global_usage (trace_len t0)) ln /\
    has_treesync_invariants tkt pr
  )
  (ensures fun t0 _ t1 -> trace_len t1 == trace_len t0 + 1)
let add #tkt pr p as_session gmgr_session group_id ln =
  let now = global_timestamp () in
  let group_session = find_group_sessions pr p gmgr_session group_id in
  let st = get_public_treesync_state #tkt pr p group_session.si_public now in

  let add_pend = extract_result pr (prepare_add st ln) in
  let token = get_token_for pr p as_session add_pend.as_input in
  let (new_st, new_leaf_index) = finalize_add add_pend token in
  finalize_add_has_pre (is_publishable pr.global_usage now) add_pend token;
  set_public_treesync_state pr p group_session.si_public now new_st;
  new_leaf_index

val update:
  #tkt:treekem_types dy_bytes ->
  pr:preds -> p:principal -> as_session:nat -> gmgr_session:nat ->
  group_id:mls_bytes dy_bytes -> ln:leaf_node_nt dy_bytes tkt -> li:nat ->
  LCrypto unit pr
  (requires fun t0 ->
    value_has_pre (is_publishable pr.global_usage (trace_len t0)) ln /\
    has_treesync_invariants tkt pr
  )
  (ensures fun t0 () t1 -> trace_len t1 == trace_len t0 + 1)
let update #tkt pr p as_session gmgr_session group_id ln li =
  let now = global_timestamp () in
  let group_session = find_group_sessions pr p gmgr_session group_id in
  let st = get_public_treesync_state #tkt pr p group_session.si_public now in
  guard pr (li < pow2 st.levels);
  let update_pend = extract_result pr (prepare_update st ln li) in
  let token = get_token_for pr p as_session update_pend.as_input in
  let new_st = finalize_update update_pend token in
  finalize_update_has_pre (is_publishable pr.global_usage now) update_pend token;
  set_public_treesync_state pr p group_session.si_public now new_st

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
  let st = get_public_treesync_state #tkt pr p group_session.si_public now in
  guard pr (li < pow2 st.levels);
  let remove_pend = extract_result pr (prepare_remove st li) in
  let new_st = finalize_remove remove_pend in
  finalize_remove_has_pre (is_publishable pr.global_usage now) remove_pend;
  set_public_treesync_state pr p group_session.si_public now new_st

#push-options "--z3rlimit 25"
val commit:
  #tkt:treekem_types dy_bytes -> #l:nat -> #li:leaf_index l 0 ->
  pr:preds -> p:principal -> as_session:nat -> gmgr_session:nat ->
  group_id:mls_bytes dy_bytes -> path:pathsync dy_bytes tkt l 0 li ->
  LCrypto unit pr
  (requires fun t0 ->
    pathsync_has_pre (is_publishable pr.global_usage (trace_len t0)) path /\
    has_treesync_invariants tkt pr
  )
  (ensures fun t0 () t1 -> trace_len t1 == trace_len t0 + 1)
let commit #tkt #l #li pr p as_session gmgr_session group_id path =
  let now = global_timestamp () in
  let group_session = find_group_sessions pr p gmgr_session group_id in
  let st = get_public_treesync_state #tkt pr p group_session.si_public now in
  guard pr (l = st.levels);
  let commit_pend = extract_result pr (prepare_commit st path) in
  let token = get_token_for pr p as_session commit_pend.as_input in
  let new_st = finalize_commit commit_pend token in
  finalize_commit_has_pre (is_publishable pr.global_usage now) commit_pend token;
  set_public_treesync_state pr p group_session.si_public now new_st
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

val external_path_has_pred_later:
  #tkt:treekem_types dy_bytes ->
  #l:nat -> #li:leaf_index l 0 ->
  prin:principal -> time0:timestamp -> time1:timestamp ->
  t:treesync dy_bytes tkt l 0 -> p:external_pathsync dy_bytes tkt l 0 li -> group_id:mls_bytes dy_bytes ->
  Lemma
  (requires
    external_path_to_path_pre t p group_id /\
    external_path_has_pred prin time0 t p group_id /\
    time0 <$ time1
  )
  (ensures external_path_has_pred prin time1 t p group_id)
let external_path_has_pred_later #tkt #l #li prin time0 time1 t p group_id =
  let auth_p = external_path_to_path_nosig t p group_id in
  path_is_parent_hash_valid_external_path_to_path_nosig t p group_id;
  for_allP_eq (tree_has_event prin time0 group_id) (path_to_tree_list t auth_p);
  for_allP_eq (tree_has_event prin time1 group_id) (path_to_tree_list t auth_p)

#push-options "--z3rlimit 25"
val authenticate_path:
  #tkt:treekem_types dy_bytes -> #l:nat -> #li:leaf_index l 0 ->
  pr:preds -> p:principal -> gmgr_session:nat ->
  group_id:mls_bytes dy_bytes -> tree:treesync dy_bytes tkt l 0 -> path:external_pathsync dy_bytes tkt l 0 li ->
  LCrypto (pathsync dy_bytes tkt l 0 li) pr
  (requires fun t0 ->
    external_path_to_path_pre tree path group_id /\
    external_path_has_pred p (trace_len t0) tree path group_id /\
    external_pathsync_has_pre (is_publishable pr.global_usage (trace_len t0)) path /\
    has_treesync_invariants tkt pr
  )
  (ensures fun t0 auth_path t1 ->
    pathsync_has_pre (is_publishable pr.global_usage (trace_len t1)) auth_path /\
    trace_len t1 == trace_len t0 + 1
  )
let authenticate_path #tkt #l pr p gmgr_session group_id tree path =
  let (|now0, signature_nonce|) = rand_gen #pr (readers [p_id p]) (sig_usage "???") in
  let now1 = global_timestamp () in
  let group_session = find_group_sessions pr p gmgr_session group_id in
  let st = get_public_treesync_state #tkt pr p group_session.si_public now1 in
  let private_st = get_private_treesync_state pr p group_session.si_private in
  guard pr (
    (group_id = st.group_id) &&
    (l = st.levels) &&
    (tree = st.tree) &&
    (external_path_to_path_pre tree path group_id) &&
    (path_is_filter_valid tree path) &&
    (length (private_st.signature_key <: dy_bytes) = sign_private_key_length #dy_bytes) &&
    (length (signature_nonce <: dy_bytes) = sign_nonce_length #dy_bytes)
  );
  let auth_path = external_path_to_path tree path group_id private_st.signature_key signature_nonce in
  external_pathsync_has_pre_weaken (is_publishable pr.global_usage now0) (is_publishable pr.global_usage now1) path;
  external_path_has_pred_later p now0 now1 tree path group_id;
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
    ln_data.source == LNS_key_package () /\
    (ps_leaf_node_data_nt tkt).is_valid (is_publishable pr.global_usage (trace_len t0)) ln_data /\
    leaf_node_has_event p (trace_len t0) ({data = ln_data; group_id = (); leaf_index = ();}) /\
    has_treesync_invariants tkt pr
  )
  (ensures fun t0 ln t1 ->
    value_has_pre (is_publishable pr.global_usage (trace_len t1)) ln /\
    trace_len t1 == trace_len t0 + 1
  )
let authenticate_leaf_node_data_from_key_package #tkt pr p si_private ln_data =
  let (|now0, signature_nonce|) = rand_gen #pr (readers [p_id p]) (sig_usage "???") in
  let now1 = global_timestamp () in
  let private_st = get_private_treesync_state pr p si_private in
  guard pr (
    sign_leaf_node_data_key_package_pre ln_data &&
    (length (private_st.signature_key <: dy_bytes) = sign_private_key_length #dy_bytes) &&
    (length (signature_nonce <: dy_bytes) = sign_nonce_length #dy_bytes)
  );
  MLS.MiscLemmas.comparse_is_valid_weaken (ps_leaf_node_data_nt tkt) (is_publishable pr.global_usage now0) (is_publishable pr.global_usage now1) ln_data;
  is_msg_sign_leaf_node_data_key_package pr.global_usage p SecrecyLabels.public now1 ln_data private_st.signature_key signature_nonce;
  sign_leaf_node_data_key_package ln_data private_st.signature_key signature_nonce

val authenticate_leaf_node_data_from_update:
  #tkt:treekem_types dy_bytes ->
  pr:preds -> p:principal ->
  si_private:nat ->
  ln_data:leaf_node_data_nt dy_bytes tkt -> group_id:mls_bytes dy_bytes -> leaf_index:nat_lbytes 4 ->
  LCrypto (leaf_node_nt dy_bytes tkt) pr
  (requires fun t0 ->
    ln_data.source == LNS_update () /\
    (ps_leaf_node_data_nt tkt).is_valid (is_publishable pr.global_usage (trace_len t0)) ln_data /\
    is_publishable pr.global_usage (trace_len t0) group_id /\
    leaf_node_has_event p (trace_len t0) ({data = ln_data; group_id; leaf_index;}) /\
    tree_has_event p (trace_len t0) group_id (|0, leaf_index, TLeaf (Some ({data = ln_data; signature = empty #dy_bytes;} <: leaf_node_nt dy_bytes tkt))|) /\
    has_treesync_invariants tkt pr
  )
  (ensures fun t0 ln t1 ->
    value_has_pre (is_publishable pr.global_usage (trace_len t1)) ln /\
    trace_len t1 == trace_len t0 + 1
  )
let authenticate_leaf_node_data_from_update #tkt pr p si_private ln_data group_id leaf_index =
  let (|now0, signature_nonce|) = rand_gen #pr (readers [p_id p]) (sig_usage "???") in
  let now1 = global_timestamp () in
  let private_st = get_private_treesync_state pr p si_private in
  guard pr (
    sign_leaf_node_data_update_pre ln_data group_id &&
    (length (private_st.signature_key <: dy_bytes) = sign_private_key_length #dy_bytes) &&
    (length (signature_nonce <: dy_bytes) = sign_nonce_length #dy_bytes)
  );
  MLS.MiscLemmas.comparse_is_valid_weaken (ps_leaf_node_data_nt tkt) (is_publishable pr.global_usage now0) (is_publishable pr.global_usage now1) ln_data;
  is_msg_sign_leaf_node_data_update pr.global_usage p SecrecyLabels.public now1 ln_data group_id leaf_index private_st.signature_key signature_nonce;
  sign_leaf_node_data_update ln_data group_id leaf_index private_st.signature_key signature_nonce

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

#push-options "--fuel 1 --ifuel 1"
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
    assert_norm(tree_list_has_event p now_end group_id tl <==> (
      tree_has_event p now_end group_id h /\
      tree_list_has_event p now_end group_id t
    ))
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
