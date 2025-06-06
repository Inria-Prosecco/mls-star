module MLS.TreeSync.Symbolic.API

open FStar.List.Tot { for_allP, for_allP_eq }
open Comparse
open MLS.Result
open MLS.Crypto
open MLS.Tree
open MLS.NetworkTypes
open MLS.Bootstrap.NetworkTypes
open MLS.TreeSync.NetworkTypes
open MLS.TreeSync.Types
open MLS.TreeSync.Operations
open MLS.TreeSync.Invariants.UnmergedLeaves
open MLS.TreeSync.Invariants.AuthService
open MLS.TreeSync.Proofs.ParentHashGuarantees
open MLS.TreeSync.API
open MLS.Symbolic
open MLS.TreeSync.Symbolic.State.GroupManager
open MLS.TreeSync.Symbolic.State.KeyPackageManager
open MLS.TreeSync.Symbolic.State.Tree
open MLS.TreeSync.Symbolic.State.SignatureKey
open MLS.TreeSync.Symbolic.State.AuthServiceCache
open MLS.TreeSync.Symbolic.API.IsWellFormedInvariant
open MLS.TreeSync.Symbolic.AuthService
open MLS.TreeSync.Symbolic.LeafNodeSignature
open MLS.TreeSync.Symbolic.IsWellFormed
open DY.Core
open DY.Lib

#set-options "--fuel 0 --ifuel 0 --z3cliopt 'smt.qi.eager_threshold=100'"

(*** Utility functions ***)

val guard: b:bool -> traceful (option (squash b))
let guard b =
  if b then
    return (Some ())
  else
    return None

val has_treesync_invariants: treekem_types bytes -> {|protocol_invariants|} -> prop
let has_treesync_invariants tkt #invs =
  has_treesync_public_state_invariant tkt /\
  has_treesync_signature_key_state_invariant /\
  has_group_manager_invariant /\
  has_key_package_manager_invariant tkt /\
  has_as_cache_invariant /\
  has_leaf_node_tbs_invariant tkt

val get_token_for:
  p:principal -> as_session:state_id ->
  inp:as_input bytes ->
  traceful (option dy_as_token)
let get_token_for p as_session (verification_key, credential) =
  let*? { token } = find_verified_credential p as_session ({ verification_key; credential; }) in
  return (Some token)

val get_token_for_proof:
  {|protocol_invariants|} ->
  p:principal -> as_session:state_id ->
  inp:as_input bytes ->
  tr:trace ->
  Lemma
  (requires
    trace_invariant tr /\
    has_as_cache_invariant
  )
  (ensures (
    let (opt_token, tr_out) = get_token_for p as_session inp tr in
    tr_out == tr /\ (
      match opt_token with
      | None -> True
      | Some token -> (
        (dy_asp tr_out).credential_ok inp token
      )
    )
  ))
  [SMTPat (get_token_for p as_session inp tr);
   SMTPat (has_as_cache_invariant)]
let get_token_for_proof #invs p as_session (verification_key, credential) tr = ()

#push-options "--fuel 1 --ifuel 1"
val get_tokens_for:
  p:principal -> as_session:state_id ->
  inps:list (option (as_input bytes)) ->
  traceful (option (l:list (option dy_as_token){List.Tot.length l == List.Tot.length inps}))
let rec get_tokens_for p as_session inps =
  match inps with
  | [] -> return (Some [])
  | inp_head::inps_tail ->
    let*? token_head =
      match inp_head with
      | Some inp ->
        let*? token = get_token_for p as_session inp in
        return (Some (Some token))
      | None -> return (Some None)
    in
    let*? tokens_tail = get_tokens_for p as_session inps_tail in
    let tokens = token_head::tokens_tail in
    return (Some (tokens <: l:list (option dy_as_token){List.Tot.length l == List.Tot.length inps}))
#pop-options

#push-options "--fuel 1 --ifuel 1"
val get_tokens_for_proof:
  {|protocol_invariants|} ->
  p:principal -> as_session:state_id ->
  inps:list (option (as_input bytes)) ->
  tr:trace ->
  Lemma
  (requires
    trace_invariant tr /\
    has_as_cache_invariant
  )
  (ensures (
    let (opt_tokens, tr_out) = get_tokens_for p as_session inps tr in
    tr_out == tr /\ (
      match opt_tokens with
      | None -> True
      | Some tokens -> (
        List.Tot.length tokens == List.Tot.length inps /\
        (forall i.
          match (List.Tot.index inps i), (List.Tot.index tokens i) with
          | None, None -> True
          | Some inp, Some token -> (dy_asp tr_out).credential_ok inp token
          | _, _ -> False
        )
      )
    )
  ))
  [SMTPat (get_tokens_for p as_session inps tr);
   SMTPat (has_as_cache_invariant)]
let rec get_tokens_for_proof #invs p as_session inps tr =
  match inps with
  | [] -> ()
  | inp_head::inps_tail ->
    get_tokens_for_proof p as_session inps_tail tr;
    assert(forall i. i <> 0 ==> List.Tot.index inps i == List.Tot.index inps_tail (i-1))
#pop-options

(*** Process proposals ***)

val create:
  #tkt:treekem_types bytes ->
  p:principal -> as_session:state_id -> gmgr_session:state_id ->
  group_id:mls_bytes bytes -> ln:leaf_node_nt bytes tkt -> secret_session:state_id ->
  traceful (option unit)
let create #tkt p as_session gmgr_session group_id ln secret_session =
  let*? create_pend = extract_result (prepare_create #bytes #crypto_bytes_bytes group_id ln) in
  let*? token = get_token_for p as_session (create_pend.as_input) in
  let st = finalize_create create_pend token in
  let* si_public = new_public_treesync_state p st in
  let group_sessions = { si_public; si_private = secret_session; } in
  add_new_group_sessions p gmgr_session { group_id } group_sessions;*?
  return (Some ())

#push-options "--z3rlimit 25"
val create_proof:
  {|protocol_invariants|} ->
  #tkt:treekem_types bytes ->
  p:principal -> as_session:state_id -> gmgr_session:state_id ->
  group_id:mls_bytes bytes -> ln:leaf_node_nt bytes tkt -> secret_session:state_id ->
  tr:trace ->
  Lemma
  (requires
    is_publishable tr group_id /\
    is_well_formed _ (is_publishable tr) ln /\
    trace_invariant tr /\
    has_treesync_invariants tkt
  )
  (ensures (
    let (_, tr_out) = create p as_session gmgr_session group_id ln secret_session tr in
    trace_invariant tr_out
  ))
let create_proof #invs #tkt p as_session gmgr_session group_id ln secret_session tr =
  let (opt_create_pend, tr) = extract_result (prepare_create #bytes #crypto_bytes_bytes group_id ln) tr in
  match opt_create_pend with
  | None -> ()
  | Some create_pend -> (
    let (opt_token, tr) = get_token_for p as_session create_pend.as_input tr in
    match opt_token with
    | None -> ()
    | Some token -> (
      is_well_formed_finalize_create (is_publishable tr) create_pend token;
      finalize_create_valid #bytes #crypto_bytes_bytes #_ #(dy_asp tr) create_pend token
    )
  )
#pop-options

val welcome:
  #tkt:treekem_types bytes ->
  p:principal -> as_session:state_id -> gmgr_session:state_id -> kpmgr_session:state_id ->
  my_key_package:key_package_nt bytes tkt ->
  group_id:mls_bytes bytes -> l:nat -> t:treesync bytes tkt l 0 ->
  traceful (option unit)
let welcome #tkt p as_session gmgr_session kpmgr_session my_key_package group_id l t =
  let*? welcome_pend = extract_result (prepare_welcome #bytes #crypto_bytes_bytes group_id t) in
  welcome_pend.as_inputs_proof;
  let*? tokens = get_tokens_for p as_session welcome_pend.as_inputs in
  let st = finalize_welcome welcome_pend tokens in
  let* si_public = new_public_treesync_state p st in
  let*? { si_private } = find_key_package_secret_session tkt p kpmgr_session my_key_package in
  let group_sessions = { si_public; si_private; } in
  add_new_group_sessions p gmgr_session { group_id } group_sessions

val welcome_proof:
  {|protocol_invariants|} ->
  #tkt:treekem_types bytes ->
  p:principal -> as_session:state_id -> gmgr_session:state_id -> kpmgr_session:state_id ->
  my_key_package:key_package_nt bytes tkt ->
  group_id:mls_bytes bytes -> l:nat -> t:treesync bytes tkt l 0 ->
  tr:trace ->
  Lemma
  (requires
    is_publishable tr group_id /\
    is_well_formed _ (is_publishable tr) t /\
    trace_invariant tr /\
    has_treesync_invariants tkt
  )
  (ensures (
    let (_, tr_out) = welcome p as_session gmgr_session kpmgr_session my_key_package group_id l t tr in
    trace_invariant tr_out
  ))
let welcome_proof #invs #tkt p as_session gmgr_session kpmgr_session my_key_package group_id l t tr =
  let (opt_welcome_pend, tr) = extract_result (prepare_welcome #bytes #crypto_bytes_bytes group_id t) tr in
  match opt_welcome_pend with
  | None -> ()
  | Some welcome_pend -> (
    welcome_pend.as_inputs_proof;
    get_tokens_for_proof p as_session welcome_pend.as_inputs tr;
    let (opt_tokens, tr) = get_tokens_for p as_session welcome_pend.as_inputs tr in
    match opt_tokens with
    | None -> ()
    | Some tokens -> (
      is_well_formed_finalize_welcome (is_publishable tr) welcome_pend tokens;
      finalize_welcome_valid #bytes #crypto_bytes_bytes #_ #(dy_asp tr) welcome_pend tokens;
      // not sure why F* needs the following lines
      // similar to FStarLang/FStar#3093 ?
      let st = finalize_welcome welcome_pend tokens in
      let (si_public, tr) = new_public_treesync_state p st tr in
      let (opt_si_private, tr) = find_key_package_secret_session tkt p kpmgr_session my_key_package tr in
      match opt_si_private with
      | None -> ()
      | Some { si_private } -> ()
    )
  )

val add:
  #tkt:treekem_types bytes ->
  p:principal -> as_session:state_id -> gmgr_session:state_id ->
  group_id:mls_bytes bytes -> ln:leaf_node_nt bytes tkt ->
  traceful (option nat)
let add #tkt p as_session gmgr_session group_id ln =
  let*? group_session = find_group_sessions p gmgr_session { group_id } in
  let*? (|group_id, st|) = get_public_treesync_state #tkt p group_session.si_public in
  let*? add_pend = extract_result (prepare_add st ln) in
  let*? token = get_token_for p as_session add_pend.as_input in
  let*? (new_st, new_leaf_index) = extract_result (finalize_add add_pend token) in
  set_public_treesync_state p group_session.si_public new_st;*
  return (Some new_leaf_index)

val add_proof:
  {|protocol_invariants|} ->
  #tkt:treekem_types bytes ->
  p:principal -> as_session:state_id -> gmgr_session:state_id ->
  group_id:mls_bytes bytes -> ln:leaf_node_nt bytes tkt ->
  tr:trace ->
  Lemma
  (requires
    is_well_formed _ (is_publishable tr) ln /\
    trace_invariant tr /\
    has_treesync_invariants tkt
  )
  (ensures (
    let (_, tr_out) = add p as_session gmgr_session group_id ln tr in
    trace_invariant tr_out
  ))
let add_proof #invs #tkt p as_session gmgr_session group_id ln tr =
  let (opt_group_session, tr) = find_group_sessions p gmgr_session { group_id } tr in
  match opt_group_session with
  | None -> ()
  | Some group_session -> (
    let (opt_st, tr) = get_public_treesync_state #tkt p group_session.si_public tr in
    match opt_st with
    | None -> ()
    | Some (|group_id, st|) -> (
      let (opt_add_pend, tr) = extract_result (prepare_add st ln) tr in
      match opt_add_pend with
      | None -> ()
      | Some add_pend -> (
        let (opt_token, tr) = get_token_for p as_session add_pend.as_input tr in
        match opt_token with
        | None -> ()
        | Some token -> (
          let (opt_new_st, tr) = extract_result (finalize_add add_pend token) tr in
          match opt_new_st with
          | None -> ()
          | Some (new_st, _) -> (
            is_well_formed_finalize_add (is_publishable tr) add_pend token;
            finalize_add_valid #bytes #crypto_bytes_bytes #_ #(dy_asp tr) add_pend token
          )
        )
      )
    )
  )

val update:
  #tkt:treekem_types bytes ->
  p:principal -> as_session:state_id -> gmgr_session:state_id ->
  group_id:mls_bytes bytes -> ln:leaf_node_nt bytes tkt -> li:nat ->
  traceful (option unit)
let update #tkt p as_session gmgr_session group_id ln li =
  let*? group_session = find_group_sessions p gmgr_session { group_id } in
  let*? (|group_id, st|) = get_public_treesync_state #tkt p group_session.si_public in
  guard (li < pow2 st.levels);*?
  let*? update_pend = extract_result (prepare_update st ln li) in
  let*? token = get_token_for p as_session update_pend.as_input in
  let new_st = finalize_update update_pend token in
  set_public_treesync_state p group_session.si_public new_st;*
  return (Some ())

val update_proof:
  {|protocol_invariants|} ->
  #tkt:treekem_types bytes ->
  p:principal -> as_session:state_id -> gmgr_session:state_id ->
  group_id:mls_bytes bytes -> ln:leaf_node_nt bytes tkt -> li:nat ->
  tr:trace ->
  Lemma
  (requires
    is_well_formed _ (is_publishable tr) ln /\
    trace_invariant tr /\
    has_treesync_invariants tkt
  )
  (ensures (
    let (_, tr_out) = update p as_session gmgr_session group_id ln li tr in
    trace_invariant tr_out
  ))
let update_proof #invs #tkt p as_session gmgr_session group_id ln li tr =
  let (opt_group_session, tr) = find_group_sessions p gmgr_session { group_id } tr in
  match opt_group_session with
  | None -> ()
  | Some group_session -> (
    let (opt_st, tr) = get_public_treesync_state #tkt p group_session.si_public tr in
    match opt_st with
    | None -> ()
    | Some (|group_id, st|) -> (
      if not (li < pow2 st.levels) then ()
      else (
        let (opt_update_pend, tr) = extract_result (prepare_update st ln li) tr in
        match opt_update_pend with
        | None -> ()
        | Some update_pend -> (
          let (opt_token, tr) = get_token_for p as_session update_pend.as_input tr in
          match opt_token with
          | None -> ()
          | Some token -> (
            is_well_formed_finalize_update (is_publishable tr) update_pend token;
            finalize_update_valid #bytes #crypto_bytes_bytes #_ #(dy_asp tr) update_pend token
          )
        )
      )
    )
  )

val remove:
  #tkt:treekem_types bytes ->
  p:principal -> as_session:state_id -> gmgr_session:state_id ->
  group_id:mls_bytes bytes -> li:nat ->
  traceful (option unit)
let remove #tkt p as_session gmgr_session group_id li =
  let*? group_session = find_group_sessions p gmgr_session { group_id } in
  let*? (|group_id, st|) = get_public_treesync_state #tkt p group_session.si_public in
  guard (li < pow2 st.levels);*?
  let*? remove_pend = extract_result (prepare_remove st li) in
  let new_st = finalize_remove remove_pend in
  set_public_treesync_state p group_session.si_public new_st;*
  return (Some ())

val remove_proof:
  {|protocol_invariants|} ->
  #tkt:treekem_types bytes ->
  p:principal -> as_session:state_id -> gmgr_session:state_id ->
  group_id:mls_bytes bytes -> li:nat ->
  tr:trace ->
  Lemma
  (requires
    trace_invariant tr /\
    has_treesync_invariants tkt
  )
  (ensures (
    let (_, tr_out) = remove #tkt p as_session gmgr_session group_id li tr in
    trace_invariant tr_out
  ))
let remove_proof #invs #tkt p as_session gmgr_session group_id li tr =
  let (opt_group_session, tr) = find_group_sessions p gmgr_session { group_id } tr in
  match opt_group_session with
  | None -> ()
  | Some group_session -> (
    let (opt_st, tr) = get_public_treesync_state #tkt p group_session.si_public tr in
    match opt_st with
    | None -> ()
    | Some (|group_id, st|) -> (
      if not (li < pow2 st.levels) then ()
      else (
        let (opt_remove_pend, tr) = extract_result (prepare_remove st li) tr in
        match opt_remove_pend with
        | None -> ()
        | Some remove_pend -> (
          is_well_formed_finalize_remove (is_publishable tr) remove_pend;
          finalize_remove_valid #bytes #crypto_bytes_bytes #_ #(dy_asp tr) remove_pend
        )
      )
    )
  )

val commit:
  #tkt:treekem_types bytes -> #l:nat -> #li:leaf_index l 0 ->
  p:principal -> as_session:state_id -> gmgr_session:state_id ->
  group_id:mls_bytes bytes -> path:pathsync bytes tkt l 0 li ->
  traceful (option unit)
let commit #tkt #l #li p as_session gmgr_session group_id path =
  let*? group_session = find_group_sessions p gmgr_session { group_id } in
  let*? (|group_id, st|) = get_public_treesync_state #tkt p group_session.si_public in
  guard (l = st.levels);*?
  let*? commit_pend = extract_result (prepare_commit st path) in
  let*? token = get_token_for p as_session commit_pend.as_input in
  let*? new_st = extract_result (finalize_commit commit_pend token) in
  set_public_treesync_state p group_session.si_public new_st;*
  return (Some ())

#push-options "--z3rlimit 50"
val commit_proof:
  {|protocol_invariants|} ->
  #tkt:treekem_types bytes -> #l:nat -> #li:leaf_index l 0 ->
  p:principal -> as_session:state_id -> gmgr_session:state_id ->
  group_id:mls_bytes bytes -> path:pathsync bytes tkt l 0 li ->
  tr:trace ->
  Lemma
  (requires
    is_well_formed _ (is_publishable tr) path /\
    trace_invariant tr /\
    has_treesync_invariants tkt
  )
  (ensures (
    let (_, tr_out) = commit p as_session gmgr_session group_id path tr in
    trace_invariant tr_out
  ))
let commit_proof #invs #tkt #l #li p as_session gmgr_session group_id path tr =
  let (opt_group_session, tr) = find_group_sessions p gmgr_session { group_id } tr in
  match opt_group_session with
  | None -> ()
  | Some group_session -> (
    let (opt_st, tr) = get_public_treesync_state #tkt p group_session.si_public tr in
    match opt_st with
    | None -> ()
    | Some (|group_id, st|) -> (
      if not (l = st.levels) then ()
      else (
        let (opt_commit_pend, tr) = extract_result (prepare_commit st path) tr in
        match opt_commit_pend with
        | None -> ()
        | Some commit_pend -> (
          let (opt_token, tr) = get_token_for p as_session commit_pend.as_input tr in
          match opt_token with
          | None -> ()
          | Some token -> (
            let (opt_new_st, tr) = extract_result (finalize_commit commit_pend token) tr in
            assert((dy_asp tr).credential_ok commit_pend.as_input token);
            match opt_new_st with
            | None -> ()
            | Some new_st -> (
              is_well_formed_finalize_commit (is_publishable tr) commit_pend token;
              finalize_commit_valid #_ #_ #_ #(dy_asp tr) commit_pend token;
              ()
            )
          )
        )
      )
    )
  )
#pop-options

(*** Create signature keypair ***)

val create_signature_keypair:
  p:principal ->
  traceful (option (state_id & signature_public_key_nt bytes))
let create_signature_keypair p =
  let* private_si = mk_signature_key p in
  let*? verification_key = get_signature_key_vk p private_si in
  guard (length (verification_key <: bytes) < pow2 30);*?
  return (Some (private_si, (verification_key <: signature_public_key_nt bytes)))

val create_signature_keypair_proof:
  {|protocol_invariants|} ->
  p:principal ->
  tr:trace ->
  Lemma
  (requires
    trace_invariant tr /\
    has_treesync_signature_key_state_invariant
  )
  (ensures (
    let (opt_res, tr_out) = create_signature_keypair p tr in
    trace_invariant tr_out /\ (
      match opt_res with
      | None -> True
      | Some (private_si, verification_key) ->
        is_signature_key_vk tr_out p verification_key
    )
  ))
let create_signature_keypair_proof #invs p tr = ()

(*** Sign stuff ***)

val external_path_has_event_later:
  #tkt:treekem_types bytes ->
  #l:nat -> #li:leaf_index l 0 ->
  prin:principal -> tr1:trace -> tr2:trace ->
  t:treesync bytes tkt l 0 -> p:external_pathsync bytes tkt l 0 li -> group_id:mls_bytes bytes ->
  Lemma
  (requires
    external_path_has_event prin tr1 t p group_id /\
    tr1 <$ tr2
  )
  (ensures external_path_has_event prin tr2 t p group_id)
let external_path_has_event_later #tkt #l #li prin tr1 tr2 t p group_id =
  let Success auth_p = external_path_to_path_nosig #bytes #crypto_bytes_bytes t p  in
  path_is_parent_hash_valid_external_path_to_path_nosig #bytes #crypto_bytes_bytes t p ;
  apply_path_aux_compute_leaf_parent_hash_from_path_both_succeed #bytes #crypto_bytes_bytes t auth_p (MLS.TreeSync.ParentHash.root_parent_hash #bytes);
  path_to_tree_list_pre_weaken (tree_has_event prin tr1 group_id li) (tree_has_event prin tr2 group_id li) t auth_p

#push-options "--z3rlimit 25"
val authenticate_path:
  #tkt:treekem_types bytes -> #l:nat -> #li:leaf_index l 0 ->
  p:principal -> gmgr_session:state_id ->
  group_id:mls_bytes bytes -> tree:treesync bytes tkt l 0 -> path:external_pathsync bytes tkt l 0 li{(get_path_leaf path).source == LNS_update} ->
  traceful (option (pathsync bytes tkt l 0 li))
let authenticate_path #tkt #l p gmgr_session group_id tree path =
  let* signature_nonce = mk_rand SigNonce secret 32 in
  let*? group_session = find_group_sessions p gmgr_session { group_id } in
  let*? (|group_id', st|) = get_public_treesync_state #tkt p group_session.si_public in
  let*? signature_key = get_signature_key_sk p group_session.si_private in
  guard (group_id = group_id');*?
  guard (l = st.levels);*?
  guard (tree = st.tree);*?
  guard (length (signature_nonce <: bytes) >= sign_sign_min_entropy_length #bytes);*?
  guard (path_is_filter_valid #bytes #crypto_bytes_bytes tree path);*?
  let*? auth_path = extract_result (external_path_to_path #bytes #crypto_bytes_bytes tree path group_id signature_key signature_nonce) in
  return (Some auth_path)
#pop-options

#push-options "--z3rlimit 50"
val authenticate_path_proof:
  {|protocol_invariants|} ->
  #tkt:treekem_types bytes -> #l:nat -> #li:leaf_index l 0 ->
  p:principal -> gmgr_session:state_id ->
  group_id:mls_bytes bytes -> tree:treesync bytes tkt l 0 -> path:external_pathsync bytes tkt l 0 li ->
  tr:trace ->
  Lemma
  (requires
    external_path_has_event p tr tree path group_id /\
    is_well_formed _ (is_publishable tr) path /\
    trace_invariant tr /\
    has_treesync_invariants tkt
  )
  (ensures (
    let (opt_auth_path, tr_out) = authenticate_path p gmgr_session group_id tree path tr in
    trace_invariant tr_out /\ (
      match opt_auth_path with
      | None -> True
      | Some auth_path ->
        is_well_formed _ (is_publishable tr_out) auth_path
    )
  ))
let authenticate_path_proof #invs #tkt #l p gmgr_session group_id tree path tr =
  let tr_in = tr in
  let (signature_nonce, tr) = mk_rand SigNonce secret 32 tr in
  let (opt_group_session, tr) = find_group_sessions p gmgr_session { group_id } tr in
  match opt_group_session with
  | None -> ()
  | Some group_session -> (
    let (opt_st, tr) = get_public_treesync_state #tkt p group_session.si_public tr in
    match opt_st with
    | None -> ()
    | Some(|group_id', st|) -> (
      let (opt_signature_key, tr) = get_signature_key_sk p group_session.si_private tr in
      match opt_signature_key with
      | None -> ()
      | Some signature_key -> (
        if not (group_id = group_id') then ()
        else if not (l = st.levels) then ()
        else if not (tree = st.tree) then ()
        else if not (length (signature_nonce <: bytes) >= sign_sign_min_entropy_length #bytes) then ()
        else if not (path_is_filter_valid #bytes #crypto_bytes_bytes tree path) then ()
        else if not (length (signature_nonce <: bytes) >= sign_sign_min_entropy_length #bytes) then ()
        else (
          let (opt_auth_path, tr) = extract_result (external_path_to_path #bytes #crypto_bytes_bytes tree path group_id signature_key signature_nonce) tr in
          match opt_auth_path with
          | None -> ()
          | Some auth_path -> (
            let tr_out = tr in
            wf_weaken_lemma _ (is_publishable tr_in) (is_publishable tr_out) path;
            external_path_has_event_later p tr_in tr_out tree path group_id;
            is_msg_external_path_to_path p public tr_out tree path group_id signature_key signature_nonce
          )
        )
      )
    )
  )
#pop-options

val authenticate_leaf_node_data_from_key_package:
  #tkt:treekem_types bytes ->
  p:principal ->
  si_private:state_id ->
  ln_data:leaf_node_data_nt bytes tkt{ln_data.source == LNS_key_package} ->
  traceful (option (leaf_node_nt bytes tkt))
let authenticate_leaf_node_data_from_key_package #tkt p si_private ln_data =
  let* signature_nonce = mk_rand SigNonce secret 32 in
  let*? signature_key = get_signature_key_sk p si_private in
  guard (length (signature_nonce <: bytes) = sign_sign_min_entropy_length #bytes);*?
  extract_result (sign_leaf_node_data_key_package #bytes #crypto_bytes_bytes ln_data signature_key signature_nonce)

#push-options "--z3rlimit 25"
val authenticate_leaf_node_data_from_key_package_proof:
  {|protocol_invariants|} ->
  #tkt:treekem_types bytes ->
  p:principal ->
  si_private:state_id ->
  ln_data:leaf_node_data_nt bytes tkt{ln_data.source == LNS_key_package} ->
  tr:trace ->
  Lemma
  (requires
    is_well_formed_prefix (ps_leaf_node_data_nt tkt) (is_publishable tr) ln_data /\
    leaf_node_has_event p tr ({data = ln_data; group_id = (); leaf_index = ();}) /\
    trace_invariant tr /\
    has_treesync_invariants tkt
  )
  (ensures (
    let (opt_ln, tr_out) = authenticate_leaf_node_data_from_key_package p si_private ln_data tr in
    trace_invariant tr_out /\ (
      match opt_ln with
      | None -> True
      | Some ln ->
        is_well_formed _ (is_publishable tr_out) ln /\
        ln.data == ln_data
    )
  ))
let authenticate_leaf_node_data_from_key_package_proof  #invs #tkt p si_private ln_data tr =
  let tr_in = tr in
  let (signature_nonce, tr) = mk_rand SigNonce secret 32 tr in
  let (opt_signature_key, tr) = get_signature_key_sk p si_private tr in
  match opt_signature_key with
  | None -> ()
  | Some signature_key -> (
    if not (length (signature_nonce <: bytes) = sign_sign_min_entropy_length #bytes) then ()
    else (
      let (opt_res, tr) = extract_result (sign_leaf_node_data_key_package #bytes #crypto_bytes_bytes ln_data signature_key signature_nonce) tr in
      match opt_res with
      | None -> ()
      | Some res -> (
        is_well_formed_prefix_weaken (ps_leaf_node_data_nt tkt) (is_publishable tr_in) (is_knowable_by public tr) ln_data;
        is_msg_sign_leaf_node_data_key_package p public tr ln_data signature_key signature_nonce
      )
    )
  )
#pop-options

val authenticate_leaf_node_data_from_update:
  #tkt:treekem_types bytes ->
  p:principal ->
  si_private:state_id ->
  ln_data:leaf_node_data_nt bytes tkt{ln_data.source == LNS_update} -> group_id:mls_bytes bytes -> leaf_index:nat_lbytes 4 ->
  traceful (option (leaf_node_nt bytes tkt))
let authenticate_leaf_node_data_from_update #tkt p si_private ln_data group_id leaf_index =
  let* signature_nonce = mk_rand SigNonce secret 32 in
  let*? signature_key = get_signature_key_sk p si_private in
  guard (length (signature_nonce <: bytes) >= sign_sign_min_entropy_length #bytes);*?
  extract_result (sign_leaf_node_data_update #bytes #crypto_bytes_bytes ln_data group_id leaf_index signature_key signature_nonce)

#push-options "--z3rlimit 25"
val authenticate_leaf_node_data_from_update_proof:
  {|protocol_invariants|} ->
  #tkt:treekem_types bytes ->
  p:principal ->
  si_private:state_id ->
  ln_data:leaf_node_data_nt bytes tkt{ln_data.source == LNS_update} -> group_id:mls_bytes bytes -> leaf_index:nat_lbytes 4 ->
  tr:trace ->
  Lemma
  (requires
    is_well_formed_prefix (ps_leaf_node_data_nt tkt) (is_publishable tr) ln_data /\
    is_publishable tr group_id /\
    leaf_node_has_event p tr ({data = ln_data; group_id; leaf_index;}) /\
    tree_has_event p tr group_id leaf_index (|0, leaf_index, TLeaf (Some ({data = ln_data; signature = empty #bytes;} <: leaf_node_nt bytes tkt))|) /\
    trace_invariant tr /\
    has_treesync_invariants tkt
  )
  (ensures (
    let (opt_ln, tr_out) = authenticate_leaf_node_data_from_update p si_private ln_data group_id leaf_index tr in
    trace_invariant tr_out /\ (
      match opt_ln with
      | None -> True
      | Some ln ->
        is_well_formed _ (is_publishable tr_out) ln /\
        ln.data == ln_data
    )
  ))
let authenticate_leaf_node_data_from_update_proof #invs #tkt p si_private ln_data group_id leaf_index tr =
  let tr_in = tr in
  let (signature_nonce, tr) = mk_rand SigNonce secret 32 tr in
  let (opt_signature_key, tr) = get_signature_key_sk p si_private tr in
  match opt_signature_key with
  | None -> ()
  | Some signature_key -> (
    if not (length (signature_nonce <: bytes) >= sign_sign_min_entropy_length #bytes) then ()
    else (
      let (opt_res, tr) = extract_result (sign_leaf_node_data_update #bytes #crypto_bytes_bytes ln_data group_id leaf_index signature_key signature_nonce) tr in
      match opt_res with
      | None -> ()
      | Some res -> (
        is_well_formed_prefix_weaken (ps_leaf_node_data_nt tkt) (is_publishable tr_in) (is_knowable_by public tr) ln_data;
        is_msg_sign_leaf_node_data_update p public tr ln_data group_id leaf_index signature_key signature_nonce
      )
    )
  )
#pop-options

(*** Trigger events ***)

val tree_event_pre:
  #tkt:treekem_types bytes ->
  tr:trace ->
  group_has_event_pred: event_predicate (group_has_tree_event bytes tkt) ->
  p:principal ->
  group_id:mls_bytes bytes -> authentifier_leaf_index:nat -> t:(one_tree bytes tkt) ->
  prop
let tree_event_pre #tkt tr group_has_event_pred p group_id authentifier_leaf_index t =
  forall tr'. tr <$ tr' ==> group_has_event_pred tr' p (mk_group_has_tree_event group_id authentifier_leaf_index t)

#push-options "--ifuel 1"
val trigger_tree_event:
  #tkt:treekem_types bytes ->
  p:principal ->
  group_id:mls_bytes bytes -> authentifier_leaf_index:nat -> t:(one_tree bytes tkt) ->
  traceful unit
let trigger_tree_event #tkt p group_id authentifier_leaf_index t =
  trigger_event p (mk_group_has_tree_event group_id authentifier_leaf_index t)
#pop-options

#push-options "--ifuel 1 --fuel 1 --z3rlimit 10"
val trigger_tree_event_proof:
  {|protocol_invariants|} ->
  #tkt:treekem_types bytes ->
  group_has_event_pred: event_predicate (group_has_tree_event bytes tkt) ->
  p:principal ->
  group_id:mls_bytes bytes -> authentifier_leaf_index:nat -> t:(one_tree bytes tkt) ->
  tr:trace ->
  Lemma
  (requires
    tree_event_pre tr group_has_event_pred p group_id authentifier_leaf_index t /\
    trace_invariant tr /\
    has_event_pred group_has_event_pred
  )
  (ensures (
    let ((), tr_out) = trigger_tree_event p group_id authentifier_leaf_index t tr in
    trace_invariant tr_out /\
    tree_has_event p tr_out group_id authentifier_leaf_index t
  ))
let trigger_tree_event_proof #invs #tkt group_has_event_pred p group_id authentifier_leaf_index t tr =
  ()
#pop-options

#push-options "--ifuel 1"
val trigger_tree_list_event:
  #tkt:treekem_types bytes ->
  p:principal ->
  group_id:mls_bytes bytes -> authentifier_leaf_index:nat -> tl:tree_list bytes tkt ->
  traceful unit
let rec trigger_tree_list_event #tkt p group_id authentifier_leaf_index tl =
  match tl with
  | [] -> return ()
  | h::t -> (
    trigger_tree_event p group_id authentifier_leaf_index h;*
    trigger_tree_list_event p group_id authentifier_leaf_index t
  )
#pop-options

val trigger_tree_list_event_lemma:
  #tkt:treekem_types bytes ->
  p:principal -> tr:trace ->
  group_id:mls_bytes bytes -> authentifier_leaf_index:nat -> h:(one_tree bytes tkt) -> t:tree_list bytes tkt ->
  Lemma(tree_list_has_event p tr group_id authentifier_leaf_index (h::t) <==> (tree_has_event p tr group_id authentifier_leaf_index h /\ tree_list_has_event p tr group_id authentifier_leaf_index t))
let trigger_tree_list_event_lemma #tkt p tr group_id authentifier_leaf_index h t =
  let open FStar.Tactics in
  assert(tree_list_has_event p tr group_id authentifier_leaf_index (h::t) == (
    tree_has_event p tr group_id authentifier_leaf_index h /\
    tree_list_has_event p tr group_id authentifier_leaf_index t
  )) by (
    norm [delta_only [`%tree_list_has_event; `%for_allP]; zeta; iota];
    trefl()
  )

#push-options "--ifuel 1 --fuel 1 --z3rlimit 10"
val trigger_tree_list_event_proof:
  {|protocol_invariants|} ->
  #tkt:treekem_types bytes ->
  group_has_event_pred: event_predicate (group_has_tree_event bytes tkt) ->
  p:principal ->
  group_id:mls_bytes bytes -> authentifier_leaf_index:nat -> tl:tree_list bytes tkt ->
  tr:trace ->
  Lemma
  (requires
    (forall t. List.Tot.memP t tl ==> tree_event_pre tr group_has_event_pred p group_id authentifier_leaf_index t) /\
    trace_invariant tr /\
    has_event_pred group_has_event_pred
  )
  (ensures (
    let ((), tr_out) = trigger_tree_list_event p group_id authentifier_leaf_index tl tr in
    trace_invariant tr_out /\
    tree_list_has_event p tr_out group_id authentifier_leaf_index tl
  ))
let rec trigger_tree_list_event_proof #invs #tkt group_has_event_pred p group_id authentifier_leaf_index tl tr =
  let tr_in = tr in
  match tl with
  | [] -> normalize_term_spec (tree_list_has_event p tr group_id authentifier_leaf_index tl)
  | tl_head::tl_tail -> (
    trigger_tree_event_proof group_has_event_pred p group_id authentifier_leaf_index tl_head tr;
    let ((), tr) = trigger_tree_event p group_id authentifier_leaf_index tl_head tr in
    trigger_tree_list_event_proof group_has_event_pred p group_id authentifier_leaf_index tl_tail tr;
    let ((), tr) = trigger_tree_list_event p group_id authentifier_leaf_index tl_tail tr in
    trigger_tree_list_event_lemma p tr group_id authentifier_leaf_index tl_head tl_tail
  )
#pop-options

val trigger_leaf_node_event:
  #tkt:treekem_types bytes ->
  p:principal ->
  ln_tbs:leaf_node_tbs_nt bytes tkt ->
  traceful unit
let trigger_leaf_node_event #tkt p ln_tbs =
  trigger_event p { ln_tbs }

val trigger_leaf_node_event_proof:
  {|protocol_invariants|} ->
  #tkt:treekem_types bytes ->
  leaf_node_has_event_pred: event_predicate (leaf_node_signed_event tkt) ->
  p:principal ->
  ln_tbs:leaf_node_tbs_nt bytes tkt ->
  tr:trace ->
  Lemma
  (requires
    leaf_node_has_event_pred tr p { ln_tbs } /\
    trace_invariant tr /\
    has_event_pred leaf_node_has_event_pred
  )
  (ensures (
    let ((), tr_out) = trigger_leaf_node_event p ln_tbs tr in
    trace_invariant tr_out /\
    leaf_node_has_event p tr_out ln_tbs
  ))
let trigger_leaf_node_event_proof #invs #tkt leaf_node_has_event_pred p ln_tbs tr = ()

val external_path_has_event_pre:
  #tkt:treekem_types bytes ->
  #l:nat -> #li:leaf_index l 0 ->
  event_predicate (leaf_node_signed_event tkt) ->
  event_predicate (group_has_tree_event bytes tkt) ->
  trace -> principal -> treesync bytes tkt l 0 -> external_pathsync bytes tkt l 0 li -> mls_bytes bytes ->
  prop
let external_path_has_event_pre #tkt #l #li leaf_node_has_event_pred group_has_event_pred tr prin t p group_id =
  (
    (get_path_leaf p).source == LNS_update /\
    li < pow2 32 /\
    Success? (external_path_to_path_nosig t p)
  ) ==> (
    path_is_parent_hash_valid_external_path_to_path_nosig t p ;
    let Success auth_p = external_path_to_path_nosig t p in
    let auth_ln = get_path_leaf auth_p in
    compute_leaf_parent_hash_from_path_set_path_leaf t p auth_ln (MLS.TreeSync.ParentHash.root_parent_hash #bytes);
    apply_path_aux_compute_leaf_parent_hash_from_path_both_succeed t auth_p (MLS.TreeSync.ParentHash.root_parent_hash #bytes);
    leaf_node_has_event_pred tr prin ({ln_tbs = {data = auth_ln.data; group_id; leaf_index = li;}}) /\
    path_to_tree_list_pre #bytes #crypto_bytes_bytes (tree_event_pre tr group_has_event_pred prin group_id li) t auth_p ()
  )

val trigger_external_path_events:
  #tkt:treekem_types bytes ->
  #l:nat -> #li:leaf_index l 0 ->
  principal -> treesync bytes tkt l 0 -> external_pathsync bytes tkt l 0 li -> mls_bytes bytes ->
  traceful (option unit)
let trigger_external_path_events #tkt #l #li prin t p group_id =
  guard ((get_path_leaf p).source = LNS_update);*?
  guard (li < pow2 32);*?
  guard (Success? (external_path_to_path_nosig #bytes #crypto_bytes_bytes t p));*?

  path_is_parent_hash_valid_external_path_to_path_nosig #bytes #crypto_bytes_bytes t p;
  let Success auth_p = external_path_to_path_nosig #bytes #crypto_bytes_bytes t p in
  let auth_ln = get_path_leaf auth_p in
  compute_leaf_parent_hash_from_path_set_path_leaf #bytes #crypto_bytes_bytes t p auth_ln (MLS.TreeSync.ParentHash.root_parent_hash #bytes);
  apply_path_aux_compute_leaf_parent_hash_from_path_both_succeed #bytes #crypto_bytes_bytes t auth_p (MLS.TreeSync.ParentHash.root_parent_hash #bytes);

  trigger_leaf_node_event prin {data = auth_ln.data; group_id; leaf_index = li;};*
  trigger_tree_list_event prin group_id li (path_to_tree_list #bytes #crypto_bytes_bytes t auth_p);*
  return (Some ())

val trigger_external_path_events_proof:
  {|protocol_invariants|} ->
  #tkt:treekem_types bytes ->
  #l:nat -> #li:leaf_index l 0 ->
  leaf_node_has_event_pred: event_predicate (leaf_node_signed_event tkt) ->
  group_has_event_pred: event_predicate (group_has_tree_event bytes tkt) ->
  prin:principal -> t:treesync bytes tkt l 0 -> p:external_pathsync bytes tkt l 0 li -> group_id:mls_bytes bytes ->
  tr:trace ->
  Lemma
  (requires
    external_path_has_event_pre leaf_node_has_event_pred group_has_event_pred tr prin t p group_id /\
    trace_invariant tr /\
    has_event_pred leaf_node_has_event_pred /\
    has_event_pred group_has_event_pred
  )
  (ensures (
    let (res, tr_out) = trigger_external_path_events prin t p group_id tr in
    trace_invariant tr_out /\ (
      match res with
      | None -> True
      | Some () ->
        external_path_has_event prin tr_out t p group_id
    )
  ))
let trigger_external_path_events_proof #invs #tkt #l #li leaf_node_has_event_pred group_has_event_pred prin t p group_id tr =
  let tr_in = tr in
  if not (
    ((get_path_leaf p).source = LNS_update) &&
    (li < pow2 32) &&
    (Success? (external_path_to_path_nosig #bytes #crypto_bytes_bytes t p))
  ) then ()
  else (
    path_is_parent_hash_valid_external_path_to_path_nosig t p;
    let Success auth_p = external_path_to_path_nosig t p in
    let auth_ln = get_path_leaf auth_p in
    compute_leaf_parent_hash_from_path_set_path_leaf t p auth_ln (MLS.TreeSync.ParentHash.root_parent_hash #bytes);
    apply_path_aux_compute_leaf_parent_hash_from_path_both_succeed t auth_p (MLS.TreeSync.ParentHash.root_parent_hash #bytes);

    trigger_leaf_node_event_proof leaf_node_has_event_pred prin {data = auth_ln.data; group_id; leaf_index = li;} tr;
    let ((), tr) = trigger_leaf_node_event prin {data = auth_ln.data; group_id; leaf_index = li;} tr in
    path_to_tree_list_pre_weaken #bytes #crypto_bytes_bytes (tree_event_pre tr_in group_has_event_pred prin group_id li) (tree_event_pre tr group_has_event_pred prin group_id li) t auth_p;
    path_to_tree_list_pre_lemma #bytes #crypto_bytes_bytes (tree_event_pre tr group_has_event_pred prin group_id li) t auth_p;
    trigger_tree_list_event_proof group_has_event_pred prin group_id li (path_to_tree_list t auth_p) tr;
    let ((), tr) = trigger_tree_list_event prin group_id li (path_to_tree_list t auth_p) tr in
    for_allP_eq (tree_has_event prin tr group_id li) (path_to_tree_list t auth_p);
    path_to_tree_list_pre_lemma (tree_has_event prin tr group_id li) t auth_p
  )
