module MLS.TreeKEM.Symbolic.API.KeySchedule

open Comparse
open DY.Core
open DY.Lib
open MLS.NetworkTypes
open MLS.Bootstrap.NetworkTypes
open MLS.TreeKEM.NetworkTypes
open MLS.TreeKEM.API.KeySchedule.Types
open MLS.TreeKEM.KeySchedule
open MLS.TreeKEM.API.KeySchedule
open MLS.TreeKEM.Symbolic.KeySchedule
open MLS.TreeKEM.Symbolic.State.EpochSecrets
open MLS.TreeKEM.Symbolic.ConfirmationTag
open MLS.TreeKEM.Symbolic.PSK
open MLS.TreeDEM.NetworkTypes
open MLS.Bootstrap.Symbolic.KeyPackage
open MLS.Symbolic
open MLS.Result

#set-options "--fuel 0 --ifuel 0 --z3cliopt 'smt.qi.eager_threshold=100'"

[@"opaque_to_smt"]
val treekem_keyschedule_state_good:
  {|crypto_invariants|} ->
  trace ->
  treekem_keyschedule_state bytes -> group_context_nt bytes ->
  prop
let treekem_keyschedule_state_good #cinvs tr st group_context =
  is_epoch_secret tr SenderDataSecret group_context st.epoch_keys.sender_data_secret /\
  is_epoch_secret tr ExporterSecret group_context st.epoch_keys.exporter_secret /\
  is_epoch_secret tr ExternalSecret group_context st.epoch_keys.external_secret /\
  is_epoch_secret tr MembershipKey group_context st.epoch_keys.membership_key /\
  is_epoch_secret tr ResumptionPSK group_context st.epoch_keys.resumption_psk /\
  is_epoch_secret tr EpochAuthenticator group_context st.epoch_keys.epoch_authenticator /\
  is_epoch_secret tr InitSecret group_context st.init_secret /\
  is_publishable tr st.epoch_keys.confirmation_tag

val treekem_keyschedule_state_label_good_aux:
  {|crypto_invariants|} ->
  trace -> label ->
  treekem_keyschedule_state bytes -> group_context_nt bytes ->
  prop
let treekem_keyschedule_state_label_good_aux #cinvs tr epoch_secret_label st group_context =
  join epoch_secret_label (mk_epoch_secret_label SenderDataSecret group_context) `can_flow tr` get_label tr st.epoch_keys.sender_data_secret /\
  join epoch_secret_label (mk_epoch_secret_label ExporterSecret group_context) `can_flow tr` get_label tr st.epoch_keys.exporter_secret /\
  join epoch_secret_label (mk_epoch_secret_label ExternalSecret group_context) `can_flow tr` get_label tr st.epoch_keys.external_secret /\
  join epoch_secret_label (mk_epoch_secret_label MembershipKey group_context) `can_flow tr` get_label tr st.epoch_keys.membership_key /\
  join epoch_secret_label (mk_epoch_secret_label ResumptionPSK group_context) `can_flow tr` get_label tr st.epoch_keys.resumption_psk /\
  join epoch_secret_label (mk_epoch_secret_label EpochAuthenticator group_context) `can_flow tr` get_label tr st.epoch_keys.epoch_authenticator /\
  join epoch_secret_label (mk_epoch_secret_label InitSecret group_context) `can_flow tr` get_label tr st.init_secret /\
  // The following is useful to store resumption PSK in the PSK store
  // we cannot put it in `treekem_keyschedule_state_good`
  // because in `MLS.TreeKEM.Symbolic.State.API.get_treesync_treekem_state_proof`
  // we cannot prove things about the PSK store label.
  // Probably the resumption PSK shouldn't be stored in the TreeKEM epoch keys state (similarly to encryption secret).
  get_label tr st.epoch_keys.resumption_psk `can_flow tr` (mk_epoch_secret_label ResumptionPSK group_context)

val compute_epoch_secret_label:
  {|crypto_usages|} ->
  tr:trace ->
  bytes -> label -> list (key_package_nt bytes tkt) -> list (pre_shared_key_id_nt bytes & bytes) ->
  label
let compute_epoch_secret_label #cusgs tr init_secret commit_secret_label joiners psks =
  let init_secret_label = get_label tr init_secret in
  let joiners_label = List.Tot.fold_right join (List.Tot.map key_package_to_init_label joiners) secret in
  let psk_secret_label = psks_label tr psks in
  meet
    (join
      (meet
        init_secret_label
        commit_secret_label
      )
      joiners_label
    )
    psk_secret_label

val compute_commit_secret_label:
  {|crypto_usages|} ->
  trace -> option bytes ->
  label
let compute_commit_secret_label #cusgs tr opt_commit_secret =
  match opt_commit_secret with
  | None -> public
  | Some commit_secret -> get_label tr commit_secret

[@"opaque_to_smt"]
val treekem_keyschedule_state_label_good:
  {|crypto_invariants|} ->
  trace ->
  bytes -> label -> list (key_package_nt bytes tkt) -> list (pre_shared_key_id_nt bytes & bytes) ->
  treekem_keyschedule_state bytes -> group_context_nt bytes ->
  prop
let treekem_keyschedule_state_label_good #cinvs tr init_secret commit_secret_label joiners psks st group_context =
  treekem_keyschedule_state_label_good_aux tr (compute_epoch_secret_label tr init_secret commit_secret_label joiners psks) st group_context

val treekem_keyschedule_state_label_good_later:
  {|crypto_invariants|} ->
  tr1:trace -> tr2:trace ->
  init_secret:bytes -> commit_secret_label:label -> joiners:list (key_package_nt bytes tkt) -> psks:list (pre_shared_key_id_nt bytes & bytes) ->
  st:treekem_keyschedule_state bytes -> group_context:group_context_nt bytes ->
  Lemma
  (requires
    bytes_invariant tr1 init_secret /\
    psks_bytes_invariant tr1 psks /\
    treekem_keyschedule_state_good tr1 st group_context /\
    treekem_keyschedule_state_label_good tr1 init_secret commit_secret_label joiners psks st group_context /\
    tr1 <$ tr2
  )
  (ensures treekem_keyschedule_state_label_good tr2 init_secret commit_secret_label joiners psks st group_context)
  [SMTPat (treekem_keyschedule_state_label_good tr1 init_secret commit_secret_label joiners psks st group_context); SMTPat (tr1 <$ tr2)]
let treekem_keyschedule_state_label_good_later #cinvs tr1 tr2 init_secret commit_secret_label joiners psks st group_context =
  reveal_opaque (`%treekem_keyschedule_state_good) (treekem_keyschedule_state_good);
  reveal_opaque (`%treekem_keyschedule_state_label_good) (treekem_keyschedule_state_label_good)

val treekem_keyschedule_state_label_good_aux_can_flow:
  {|crypto_invariants|} ->
  tr:trace -> epoch_label1:label -> epoch_label2:label ->
  st:treekem_keyschedule_state bytes -> group_context:group_context_nt bytes ->
  Lemma
  (requires
    treekem_keyschedule_state_label_good_aux tr epoch_label1 st group_context /\
    epoch_label2 `can_flow tr` epoch_label1
  )
  (ensures
    treekem_keyschedule_state_label_good_aux tr epoch_label2 st group_context
  )
let treekem_keyschedule_state_label_good_aux_can_flow #cinvs tr epoch_label1 epoch_label2 st group_context =
  assert(forall ty. join epoch_label2 (mk_epoch_secret_label ty group_context) `can_flow tr` join epoch_label1 (mk_epoch_secret_label ty group_context))

#push-options "--z3rlimit 25"
val treekem_keyschedule_state_label_good_can_flow:
  {|crypto_invariants|} ->
  tr:trace ->
  init_secret:bytes -> commit_secret_label1:label -> commit_secret_label2:label -> joiners:list (key_package_nt bytes tkt) -> psks:list (pre_shared_key_id_nt bytes & bytes) ->
  st:treekem_keyschedule_state bytes -> group_context:group_context_nt bytes ->
  Lemma
  (requires
    treekem_keyschedule_state_label_good tr init_secret commit_secret_label1 joiners psks st group_context /\
    commit_secret_label2 `can_flow tr` commit_secret_label1
  )
  (ensures
    treekem_keyschedule_state_label_good tr init_secret commit_secret_label2 joiners psks st group_context
  )
let treekem_keyschedule_state_label_good_can_flow #cinvs tr init_secret commit_secret_label1 commit_secret_label2 joiners psks st group_context =
  reveal_opaque (`%treekem_keyschedule_state_label_good) (treekem_keyschedule_state_label_good);
  let epoch_label1 = (compute_epoch_secret_label tr init_secret commit_secret_label1 joiners psks) in
  let epoch_label2 = (compute_epoch_secret_label tr init_secret commit_secret_label2 joiners psks) in
  treekem_keyschedule_state_label_good_aux_can_flow tr epoch_label1 epoch_label2 st group_context
#pop-options

#push-options "--z3rlimit 25"
val create_from_epoch_secret_proof:
  {|crypto_invariants|} ->
  tr:trace ->
  epoch_secret:bytes -> group_context:group_context_nt bytes ->
  Lemma
  (requires
    bytes_invariant tr epoch_secret /\
    is_well_formed _ (is_publishable tr) group_context /\
    epoch_secret `has_usage tr` KdfExpandKey "MLS.TreeKEM.EpochSecret" (serialize _ group_context) /\
    has_mls_keyschedule_invariants
  )
  (ensures (
    match create_from_epoch_secret epoch_secret group_context with
    | Success (st, _) -> (
      treekem_keyschedule_state_good tr st group_context /\
      treekem_keyschedule_state_label_good_aux tr (get_label tr epoch_secret) st group_context /\
      treekem_keyschedule_state_auth_weak st epoch_secret group_context
    )
    | _ -> True
  ))
let create_from_epoch_secret_proof #cinvs tr epoch_secret group_context =
  reveal_opaque (`%create_from_epoch_secret) (create_from_epoch_secret #bytes);
  reveal_opaque (`%treekem_keyschedule_state_good) (treekem_keyschedule_state_good);
  match create_from_epoch_secret epoch_secret group_context with
  | Success (st, _) -> (
    secret_epoch_to_X_proof tr SenderDataSecret epoch_secret group_context;
    secret_epoch_to_X_proof tr EncryptionSecret epoch_secret group_context;
    secret_epoch_to_X_proof tr ExporterSecret epoch_secret group_context;
    secret_epoch_to_X_proof tr ExternalSecret epoch_secret group_context;
    secret_epoch_to_X_proof tr ConfirmationKey epoch_secret group_context;
    secret_epoch_to_X_proof tr MembershipKey epoch_secret group_context;
    secret_epoch_to_X_proof tr ResumptionPSK epoch_secret group_context;
    secret_epoch_to_X_proof tr EpochAuthenticator epoch_secret group_context;
    secret_epoch_to_X_proof tr InitSecret epoch_secret group_context;
    let Success confirmation_key = secret_epoch_to_confirmation epoch_secret in
    compute_confirmation_tag_proof tr confirmation_key group_context.confirmed_transcript_hash
  )
  | _ -> ()
#pop-options

val create_from_joiner_secret_proof:
  {|crypto_invariants|} ->
  tr:trace ->
  joiner_secret:bytes -> psks:list (pre_shared_key_id_nt bytes & bytes) -> group_context:group_context_nt bytes ->
  Lemma
  (requires
    bytes_invariant tr joiner_secret /\
    psks_bytes_invariant tr psks /\
    is_well_formed _ (is_publishable tr) group_context /\
    has_mls_keyschedule_invariants
  )
  (ensures (
    match create_from_joiner_secret joiner_secret psks group_context with
    | Success (st, _) -> (
      treekem_keyschedule_state_good tr st group_context /\
      treekem_keyschedule_state_auth_strong st joiner_secret psks group_context
    )
    | _ -> True
  ))
let create_from_joiner_secret_proof #cinvs tr joiner_secret psks group_context =
  reveal_opaque (`%create_from_joiner_secret) (create_from_joiner_secret #bytes);
  match create_from_joiner_secret joiner_secret psks group_context with
  | Success (st, _) -> (
    secret_joiner_to_epoch_proof tr joiner_secret psks group_context;
    let Success epoch_secret = secret_joiner_to_epoch joiner_secret psks group_context in
    create_from_epoch_secret_proof tr epoch_secret group_context
  )
  | _ -> ()

#push-options "--z3rlimit 50"
val commit_proof:
  {|crypto_invariants|} ->
  tr:trace ->
  st:treekem_keyschedule_state bytes -> opt_commit_secret:option bytes -> psks:list (pre_shared_key_id_nt bytes & bytes) -> group_context:group_context_nt bytes ->
  joiners:list (key_package_nt bytes tkt) -> // de-hash of confirmed transcript hash
  Lemma
  (requires
    tx_hash_contains_joiners group_context.confirmed_transcript_hash joiners /\
    bytes_invariant tr st.init_secret /\
    (
      match opt_commit_secret with
      | None -> True
      | Some commit_secret -> bytes_invariant tr commit_secret
    ) /\
    psks_bytes_invariant tr psks /\
    is_well_formed _ (is_publishable tr) group_context /\
    has_mls_keyschedule_invariants
  )
  (ensures (
    match commit st opt_commit_secret psks group_context with
    | Success (new_st, _, welcome_secrets) -> (
      treekem_keyschedule_state_good tr new_st group_context /\
      treekem_keyschedule_state_label_good tr st.init_secret (compute_commit_secret_label tr opt_commit_secret) joiners psks new_st group_context /\
      treekem_keyschedule_state_auth_strong new_st welcome_secrets.joiner_secret psks group_context /\
      treekem_keyschedule_state_auth_strong_exists new_st /\
      is_knowable_by (List.Tot.fold_right join (List.Tot.map key_package_to_init_label joiners) secret) tr welcome_secrets.joiner_secret
    )
    | _ -> True
  ))
let commit_proof #cinvs tr st opt_commit_secret psks group_context joiners =
  reveal_opaque (`%treekem_keyschedule_state_good) (treekem_keyschedule_state_good);
  reveal_opaque (`%treekem_keyschedule_state_label_good) (treekem_keyschedule_state_label_good);
  reveal_opaque (`%commit) (commit #bytes);
  match commit st opt_commit_secret psks group_context with
  | Success (new_st, _, welcome_secrets) -> (
    secret_init_to_joiner_proof tr st.init_secret opt_commit_secret group_context joiners;
    let Success joiner_secret = secret_init_to_joiner st.init_secret opt_commit_secret group_context in
    secret_joiner_to_epoch_proof tr joiner_secret psks group_context;
    let Success epoch_secret = secret_joiner_to_epoch joiner_secret psks group_context in
    create_from_epoch_secret_proof tr epoch_secret group_context;
    assert(
      treekem_keyschedule_state_good tr new_st group_context /\
      treekem_keyschedule_state_auth_strong new_st welcome_secrets.joiner_secret psks group_context
    );

    let epoch_secret_label = compute_epoch_secret_label tr st.init_secret (compute_commit_secret_label tr opt_commit_secret) joiners psks in
    treekem_keyschedule_state_label_good_aux_can_flow tr (get_label tr epoch_secret) epoch_secret_label new_st group_context
  )
  | _ -> ()
#pop-options
