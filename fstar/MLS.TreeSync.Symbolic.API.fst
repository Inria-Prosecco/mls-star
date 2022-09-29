module MLS.TreeSync.Symbolic.API

open GlobalRuntimeLib
open LabeledRuntimeAPI
open MLS.Tree
open MLS.NetworkTypes
open MLS.TreeSync.NetworkTypes
open MLS.TreeSync.Types
open MLS.TreeSync.Invariants.AuthService
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
  has_as_cache_invariant pr

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
  group_id:mls_bytes dy_bytes -> kp:key_package_nt dy_bytes tkt ->
  LCrypto nat pr
  (requires fun t0 ->
    value_has_pre (is_publishable pr.global_usage (trace_len t0)) kp.tbs.leaf_node /\
    has_treesync_invariants tkt pr
  )
  (ensures fun t0 _ t1 -> trace_len t1 == trace_len t0 + 1)
let add #tkt pr p as_session gmgr_session group_id kp =
  let now = global_timestamp () in
  let group_session = find_group_sessions pr p gmgr_session group_id in
  let st = get_public_treesync_state #tkt pr p group_session.si_public now in

  let add_pend = extract_result pr (prepare_add st kp) in
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

//TODO: validate external path
