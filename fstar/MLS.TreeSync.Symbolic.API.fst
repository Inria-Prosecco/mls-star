module MLS.TreeSync.Symbolic.API

open GlobalRuntimeLib
open LabeledRuntimeAPI
open MLS.NetworkTypes
open MLS.TreeSync.NetworkTypes
open MLS.TreeSync.Invariants.AuthService
open MLS.TreeSync.API
open MLS.Symbolic
open MLS.TreeSync.Symbolic.API.GroupManager
open MLS.TreeSync.Symbolic.API.Sessions
open MLS.TreeSync.Symbolic.API.HasPreInvariant
open MLS.TreeSync.Symbolic.SignatureGuarantees
open MLS.TreeSync.Symbolic.AuthServiceCache
open MLS.TreeSync.Symbolic.IsValid

val guard: pr:preds -> b:bool -> LCrypto unit pr
  (requires fun t0 -> True)
  (ensures fun t0 _ t1 -> t1 == t0 /\ b)
let guard pr b =
  if b then ()
  else error "guard failed"

val extract_result: #a:Type -> pr:preds -> MLS.Result.result a -> LCrypto a pr
  (requires fun t0 -> True)
  (ensures fun t0 _ t1 -> t1 == t0)
let extract_result #a pr x =
  match x with
  | MLS.Result.Success y -> y
  | MLS.Result.InternalError s -> error "extract_result: internal error '" ^ s ^ "'"
  | MLS.Result.ProtocolError s -> error "extract_result: protocol error '" ^ s ^ "'"

val has_treesync_invariants: treekem_types dy_bytes -> preds -> prop
let has_treesync_invariants tkt pr =
  has_treesync_public_state_invariant tkt pr /\
  has_treesync_private_state_invariant pr /\
  has_group_manager_invariant pr /\
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

//TODO create

//TODO welcome

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

//TODO: commit

//TODO: validate external path
