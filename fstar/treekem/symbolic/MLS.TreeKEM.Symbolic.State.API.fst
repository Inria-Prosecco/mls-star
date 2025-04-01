module MLS.TreeKEM.Symbolic.State.API

open Comparse
open DY.Core
open DY.Lib
open MLS.Crypto
open MLS.Tree
open MLS.NetworkTypes
open MLS.TreeSyncTreeKEMBinder.Properties
open MLS.TreeSync.API.Types
open MLS.TreeSync.TreeHash.Proofs
open MLS.TreeSync.Symbolic.State.Tree
open MLS.TreeSync.Symbolic.AuthService
open MLS.TreeSync.Symbolic.Event.LeafNodeHasBeenVerified
open MLS.TreeSync.Symbolic.AuthService.CredentialInterpretation
open MLS.TreeKEM.NetworkTypes
open MLS.TreeKEM.Types
open MLS.TreeKEM.API.KeySchedule.Types
open MLS.TreeKEM.API.Tree.Types
open MLS.TreeKEM.API.Types
open MLS.TreeKEM.Symbolic.ConfirmationTag
open MLS.TreeKEM.Symbolic.Tree.Labels
open MLS.TreeKEM.Symbolic.State.EpochSecrets
open MLS.TreeKEM.Symbolic.State.NodeKey
open MLS.TreeKEM.Symbolic.API.KeySchedule
open MLS.TreeKEM.Symbolic.EpochEvent
open MLS.TreeKEM.Parsers
open MLS.Symbolic

#set-options "--fuel 0 --ifuel 0 --z3cliopt 'smt.qi.eager_threshold=100'"

[@@ with_bytes bytes]
type bare_treekem_state = {
  // tree state
  levels: nat;
  [@@@ with_parser #bytes (ps_treekem levels 0)]
  tree: treekem bytes levels 0;
  priv_sid: state_id;
  // key schedule state
  sender_data_secret_sid: state_id;
  exporter_secret_sid: state_id;
  external_secret_sid: state_id;
  membership_key_sid: state_id;
  resumption_psk_sid: state_id;
  epoch_authenticator_sid: state_id;
  confirmation_tag: bytes;
  init_secret_sid: state_id;
}

%splice [ps_bare_treekem_state] (gen_parser (`bare_treekem_state))
%splice [ps_bare_treekem_state_is_well_formed] (gen_is_well_formed_lemma (`bare_treekem_state))

[@@ with_bytes bytes]
noeq
type bare_treesync_treekem_state = {
  leaf_index: nat;
  group_context: group_context_nt bytes;
  my_signature_key_sid: state_id;
  treesync: bare_treesync_state tkt;
  treekem: bare_treekem_state;
}

%splice [ps_bare_treesync_treekem_state] (gen_parser (`bare_treesync_treekem_state))
%splice [ps_bare_treesync_treekem_state_is_well_formed] (gen_is_well_formed_lemma (`bare_treesync_treekem_state))

instance local_state_treesync_treekem_state: local_state bare_treesync_treekem_state = {
  tag = "MLS.TreeKEM.TreeSyncTreeKEMState";
  format = mk_parseable_serializeable ps_bare_treesync_treekem_state;
}

#push-options "--z3rlimit 25"
val treesync_treekem_state_pred: {|crypto_invariants|} -> local_state_predicate bare_treesync_treekem_state
let treesync_treekem_state_pred #cinvs = {
  pred = (fun tr me sid st ->
    (treesync_public_state_pred tkt).pred tr me sid st.treesync /\
    tree_has_hash st.treesync.tree st.group_context.tree_hash /\

    st.treesync.group_id == st.group_context.group_id /\
    st.treesync.levels == st.treekem.levels /\
    MLS.TreeSyncTreeKEMBinder.treesync_to_treekem st.treesync.tree == st.treekem.tree /\
    st.leaf_index < pow2 st.treekem.levels /\
    Some? (leaf_at st.treekem.tree st.leaf_index) /\
    i_am_in_tree_at me st.treesync.tree st.leaf_index /\

    is_well_formed _ (is_publishable tr) st.group_context /\
    is_publishable tr st.treekem.confirmation_tag /\

    (exists init_secret.
      key_is_authenticated_by_confirmation_tag InitSecret st.treekem.confirmation_tag init_secret /\
      i_have_previous_epoch_event tr me st.group_context init_secret st.treesync.tree
    ) /\
    i_have_verified_every_leaf_node tr me st.treesync.tree st.group_context.group_id
  );
  pred_later = (fun tr1 tr2 me sid st ->
    (treesync_public_state_pred tkt).pred_later tr1 tr2 me sid st.treesync
  );
  pred_knowable = (fun tr me sid st ->
    let pre = is_knowable_by (principal_typed_state_content_label me local_state_treesync_treekem_state.tag sid st) tr in
    wf_weaken_lemma _ (is_publishable tr) pre st.treesync.tree;
    ps_dy_as_tokens_is_well_formed pre st.treesync.tokens;
    assert(is_well_formed _ pre st.treesync.tree);
    assert(is_well_formed _ pre st.treesync);

    assert(is_well_formed_prefix ps_nat pre st.treekem.levels);
    MLS.TreeSyncTreeKEMBinder.Proofs.is_well_formed_treesync_to_treekem pre st.treesync.tree;
    assert(is_well_formed_prefix ps_state_id pre st.treekem.priv_sid);
    assert(is_well_formed_prefix ps_state_id pre st.treekem.sender_data_secret_sid);
    assert(is_well_formed_prefix ps_state_id pre st.treekem.exporter_secret_sid);
    assert(is_well_formed_prefix ps_state_id pre st.treekem.external_secret_sid);
    assert(is_well_formed_prefix ps_state_id pre st.treekem.membership_key_sid);
    assert(is_well_formed_prefix ps_state_id pre st.treekem.resumption_psk_sid);
    assert(is_well_formed_prefix ps_bytes pre st.treekem.confirmation_tag);
    assert(is_well_formed_prefix ps_state_id pre st.treekem.epoch_authenticator_sid);
    assert(is_well_formed_prefix ps_state_id pre st.treekem.init_secret_sid);
    assert(is_well_formed_prefix (ps_bare_treekem_state) pre st.treekem);
    assert(is_well_formed _ pre st.group_context);
    assert(is_well_formed_prefix ps_nat pre st.leaf_index);
    assert(is_well_formed_prefix ps_state_id pre st.my_signature_key_sid);
    assert(is_well_formed _ pre st)
  );
}
#pop-options

val has_treesync_treekem_state_invariant: {|protocol_invariants|} -> prop
let has_treesync_treekem_state_invariant #invs =
  has_local_state_predicate treesync_treekem_state_pred

val treesync_treekem_state_tag_and_invariant: {|crypto_invariants|} -> dtuple2 string local_bytes_state_predicate
let treesync_treekem_state_tag_and_invariant #ci = (|local_state_treesync_treekem_state.tag, local_state_predicate_to_local_bytes_state_predicate treesync_treekem_state_pred|)

noeq
type treesync_treekem_state = {
  leaf_index: nat;
  group_context: group_context_nt bytes;
  my_signature_key_sid: state_id;
  treesync: treesync_state bytes tkt dy_as_token group_context.group_id;
  treekem: treekem_state bytes leaf_index;
}

[@@"opaque_to_smt"]
val store_treesync_treekem_state:
  principal -> treesync_treekem_state ->
  traceful state_id
let store_treesync_treekem_state me st =
  let* sid = new_session_id me in
  let confirmation_tag = st.treekem.keyschedule_state.epoch_keys.confirmation_tag in
  let* sender_data_secret_sid = store_epoch_secret me SenderDataSecret st.group_context confirmation_tag st.treekem.keyschedule_state.epoch_keys.sender_data_secret in
  let* exporter_secret_sid = store_epoch_secret me ExporterSecret st.group_context confirmation_tag st.treekem.keyschedule_state.epoch_keys.exporter_secret in
  let* external_secret_sid = store_epoch_secret me ExternalSecret st.group_context confirmation_tag st.treekem.keyschedule_state.epoch_keys.external_secret in
  let* membership_key_sid = store_epoch_secret me MembershipKey st.group_context confirmation_tag st.treekem.keyschedule_state.epoch_keys.membership_key in
  let* resumption_psk_sid = store_epoch_secret me ResumptionPSK st.group_context confirmation_tag st.treekem.keyschedule_state.epoch_keys.resumption_psk in
  let* epoch_authenticator_sid = store_epoch_secret me EpochAuthenticator st.group_context confirmation_tag st.treekem.keyschedule_state.epoch_keys.epoch_authenticator in
  let* init_secret_sid = store_epoch_secret me InitSecret st.group_context confirmation_tag st.treekem.keyschedule_state.init_secret in
  let* priv_sid = store_node_keys me st.treekem.tree_state.priv in
  let bare_st: bare_treesync_treekem_state = {
    leaf_index = st.leaf_index;
    group_context = st.group_context;
    my_signature_key_sid = st.my_signature_key_sid;
    treesync = {
      group_id = st.group_context.group_id;
      levels = _;
      tree = st.treesync.tree;
      tokens = st.treesync.tokens;
    };
    treekem = {
      levels = _;
      tree = st.treekem.tree_state.tree;
      priv_sid;
      sender_data_secret_sid;
      exporter_secret_sid;
      external_secret_sid;
      membership_key_sid;
      resumption_psk_sid;
      epoch_authenticator_sid;
      confirmation_tag;
      init_secret_sid;
    }
  } in
  set_state me sid bare_st;*
  return sid

[@@"opaque_to_smt"]
val get_treesync_treekem_state:
  principal -> state_id ->
  traceful (option (treesync_treekem_state))
let get_treesync_treekem_state me sid =
  let*? (bare_st:bare_treesync_treekem_state) = get_state me sid in
  let confirmation_tag = bare_st.treekem.confirmation_tag in
  let*? sender_data_secret = get_epoch_secret me bare_st.treekem.sender_data_secret_sid SenderDataSecret bare_st.group_context confirmation_tag in
  let*? exporter_secret = get_epoch_secret me bare_st.treekem.exporter_secret_sid ExporterSecret bare_st.group_context confirmation_tag in
  let*? external_secret = get_epoch_secret me bare_st.treekem.external_secret_sid ExternalSecret bare_st.group_context confirmation_tag in
  let*? membership_key = get_epoch_secret me bare_st.treekem.membership_key_sid MembershipKey bare_st.group_context confirmation_tag in
  let*? resumption_psk = get_epoch_secret me bare_st.treekem.resumption_psk_sid ResumptionPSK bare_st.group_context confirmation_tag in
  let*? epoch_authenticator = get_epoch_secret me bare_st.treekem.epoch_authenticator_sid EpochAuthenticator bare_st.group_context confirmation_tag in
  let*? init_secret = get_epoch_secret me bare_st.treekem.init_secret_sid InitSecret bare_st.group_context confirmation_tag in

  guard_tr (bare_st.leaf_index < pow2 bare_st.treekem.levels);*?
  guard_tr (MLS.TreeSync.Invariants.UnmergedLeaves.unmerged_leaves_ok bare_st.treesync.tree);*?
  guard_tr (MLS.TreeSync.Invariants.ParentHash.parent_hash_invariant bare_st.treesync.tree);*?
  guard_tr (MLS.TreeSync.Invariants.ValidLeaves.valid_leaves_invariant bare_st.treesync.group_id bare_st.treesync.tree);*?
  guard_tr (bare_st.treesync.group_id = bare_st.group_context.group_id);*?
  guard_tr (bare_st.treekem.levels = bare_st.treesync.levels);*?
  guard_tr (bare_st.treekem.tree = MLS.TreeSyncTreeKEMBinder.treesync_to_treekem bare_st.treesync.tree);*?
  MLS.TreeSyncTreeKEMBinder.Proofs.treesync_to_treekem_invariant bare_st.treesync.tree;

  let*? priv = get_node_keys me bare_st.treekem.priv_sid in
  guard_tr (Some? (leaf_at bare_st.treekem.tree bare_st.leaf_index));*?

  let st: treesync_treekem_state = {
    leaf_index = bare_st.leaf_index;
    group_context = bare_st.group_context;
    my_signature_key_sid = bare_st.my_signature_key_sid;
    treesync = {
      levels = _;
      tree = bare_st.treesync.tree;
      tokens = bare_st.treesync.tokens;
    };
    treekem = {
      tree_state = {
        levels = bare_st.treekem.levels;
        tree = bare_st.treekem.tree;
        priv;
      };
      keyschedule_state = {
        epoch_keys = {
          sender_data_secret;
          exporter_secret;
          external_secret;
          membership_key;
          resumption_psk;
          epoch_authenticator;
          confirmation_tag;
        };
        init_secret;
      }
    }
  } in
  return (Some st)

[@@"opaque_to_smt"]
val treesync_treekem_state_invariant_aux:
  {|crypto_invariants|} ->
  #leaf_index:nat ->
  trace -> principal ->
  group_context:group_context_nt bytes ->
  treesync_state bytes tkt dy_as_token group_context.group_id ->
  treekem_tree_state bytes leaf_index ->
  prop
let treesync_treekem_state_invariant_aux #cinvs #leaf_index tr me group_context treesync treekem =
  treesync_treekem_state_rel treesync treekem /\

  i_am_in_tree_at me treesync.tree leaf_index /\
  is_well_formed _ (is_publishable tr) group_context /\

  is_well_formed _ (is_publishable tr) (treesync.tree <: MLS.TreeSync.Types.treesync _ _ _ _) /\
  treesync_state_valid (dy_asp tr) treesync /\
  i_have_verified_every_leaf_node tr me treesync.tree group_context.group_id /\

  treekem_priv_state_pred tr me treekem.priv

[@@"opaque_to_smt"]
val treesync_treekem_state_invariant:
  {|crypto_invariants|} ->
  trace -> principal -> treesync_treekem_state ->
  prop
let treesync_treekem_state_invariant #cinvs tr me st =
  treesync_treekem_state_invariant_aux tr me st.group_context st.treesync st.treekem.tree_state

[@@"opaque_to_smt"]
val treesync_treekem_state_coarse_invariant:
  {|crypto_invariants|} ->
  trace -> principal -> treesync_treekem_state ->
  prop
let treesync_treekem_state_coarse_invariant #cinvs tr me st =
  treekem_keyschedule_state_good tr st.treekem.keyschedule_state st.group_context /\
  treekem_keyschedule_state_auth_weak_exists st.treekem.keyschedule_state /\
  tree_has_hash st.treesync.tree st.group_context.tree_hash

[@@"opaque_to_smt"]
val treesync_treekem_state_very_coarse_invariant:
  {|crypto_invariants|} ->
  trace -> principal -> treesync_treekem_state ->
  prop
let treesync_treekem_state_very_coarse_invariant #cinvs tr me st =
  i_have_previous_epoch_event tr me st.group_context st.treekem.keyschedule_state.init_secret st.treesync.tree

val treesync_treekem_state_all_invariants:
  {|crypto_invariants|} ->
  trace -> principal -> treesync_treekem_state ->
  prop
let treesync_treekem_state_all_invariants #cinvs tr me st =
  treesync_treekem_state_invariant tr me st /\
  treesync_treekem_state_coarse_invariant tr me st /\
  treesync_treekem_state_very_coarse_invariant tr me st

val treesync_treekem_state_invariant_later:
  {|crypto_invariants|} ->
  tr1:trace -> tr2:trace -> me:principal -> st:treesync_treekem_state ->
  Lemma
  (requires
    treesync_treekem_state_invariant tr1 me st /\
    tr1 <$ tr2
  )
  (ensures treesync_treekem_state_invariant tr2 me st)
  [SMTPat (treesync_treekem_state_invariant tr1 me st); SMTPat (tr1 <$ tr2)]
let treesync_treekem_state_invariant_later #cinvs tr1 tr2 me st =
  reveal_opaque (`%treesync_treekem_state_invariant) (treesync_treekem_state_invariant);
  reveal_opaque (`%treesync_treekem_state_invariant_aux) (treesync_treekem_state_invariant_aux #_ #st.leaf_index)

val treesync_treekem_state_coarse_invariant_later:
  {|crypto_invariants|} ->
  tr1:trace -> tr2:trace -> me:principal -> st:treesync_treekem_state ->
  Lemma
  (requires
    treesync_treekem_state_coarse_invariant tr1 me st /\
    tr1 <$ tr2
  )
  (ensures treesync_treekem_state_coarse_invariant tr2 me st)
  [SMTPat (treesync_treekem_state_coarse_invariant tr1 me st); SMTPat (tr1 <$ tr2)]
let treesync_treekem_state_coarse_invariant_later #cinvs tr1 tr2 me st =
  reveal_opaque (`%treesync_treekem_state_coarse_invariant) (treesync_treekem_state_coarse_invariant);
  reveal_opaque (`%treekem_keyschedule_state_good) (treekem_keyschedule_state_good)

val treesync_treekem_state_very_coarse_invariant_later:
  {|crypto_invariants|} ->
  tr1:trace -> tr2:trace -> me:principal -> st:treesync_treekem_state ->
  Lemma
  (requires
    treesync_treekem_state_very_coarse_invariant tr1 me st /\
    tr1 <$ tr2
  )
  (ensures treesync_treekem_state_very_coarse_invariant tr2 me st)
  [SMTPat (treesync_treekem_state_very_coarse_invariant tr1 me st); SMTPat (tr1 <$ tr2)]
let treesync_treekem_state_very_coarse_invariant_later #cinvs tr1 tr2 me st =
  reveal_opaque (`%treesync_treekem_state_very_coarse_invariant) (treesync_treekem_state_very_coarse_invariant)

val treekem_keyschedule_state_auth_weak_exists_implies_key_is_authenticated_by_confirmation_tag:
  st:treekem_keyschedule_state bytes ->
  Lemma
  (requires treekem_keyschedule_state_auth_weak_exists st)
  (ensures
    key_is_authenticated_by_confirmation_tag SenderDataSecret st.epoch_keys.confirmation_tag st.epoch_keys.sender_data_secret /\
    key_is_authenticated_by_confirmation_tag ExporterSecret st.epoch_keys.confirmation_tag st.epoch_keys.exporter_secret /\
    key_is_authenticated_by_confirmation_tag ExternalSecret st.epoch_keys.confirmation_tag st.epoch_keys.external_secret /\
    key_is_authenticated_by_confirmation_tag MembershipKey st.epoch_keys.confirmation_tag st.epoch_keys.membership_key /\
    key_is_authenticated_by_confirmation_tag ResumptionPSK st.epoch_keys.confirmation_tag st.epoch_keys.resumption_psk /\
    key_is_authenticated_by_confirmation_tag EpochAuthenticator st.epoch_keys.confirmation_tag st.epoch_keys.epoch_authenticator /\
    key_is_authenticated_by_confirmation_tag InitSecret st.epoch_keys.confirmation_tag st.init_secret
  )
let treekem_keyschedule_state_auth_weak_exists_implies_key_is_authenticated_by_confirmation_tag st = ()

val key_is_authenticated_by_confirmation_tag_implies_treekem_keyschedule_state_auth_weak_exists:
  st:treekem_keyschedule_state bytes ->
  Lemma
  (requires
    key_is_authenticated_by_confirmation_tag SenderDataSecret st.epoch_keys.confirmation_tag st.epoch_keys.sender_data_secret /\
    key_is_authenticated_by_confirmation_tag ExporterSecret st.epoch_keys.confirmation_tag st.epoch_keys.exporter_secret /\
    key_is_authenticated_by_confirmation_tag ExternalSecret st.epoch_keys.confirmation_tag st.epoch_keys.external_secret /\
    key_is_authenticated_by_confirmation_tag MembershipKey st.epoch_keys.confirmation_tag st.epoch_keys.membership_key /\
    key_is_authenticated_by_confirmation_tag ResumptionPSK st.epoch_keys.confirmation_tag st.epoch_keys.resumption_psk /\
    key_is_authenticated_by_confirmation_tag EpochAuthenticator st.epoch_keys.confirmation_tag st.epoch_keys.epoch_authenticator /\
    key_is_authenticated_by_confirmation_tag InitSecret st.epoch_keys.confirmation_tag st.init_secret
  )
  (ensures treekem_keyschedule_state_auth_weak_exists st)
let key_is_authenticated_by_confirmation_tag_implies_treekem_keyschedule_state_auth_weak_exists st =
  FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 (treekem_keyschedule_state_auth_weak_exists_inj))

#push-options "--z3rlimit 25"
val store_treesync_treekem_state_proof:
  {|protocol_invariants|} ->
  tr:trace ->
  me:principal -> st:treesync_treekem_state ->
  Lemma
  (requires
    treesync_treekem_state_all_invariants tr me st /\
    trace_invariant tr /\
    has_treesync_treekem_state_invariant /\
    has_treekem_epoch_secret_state_invariant /\
    has_treekem_node_keys_state_invariant
  )
  (ensures (
    let (_, tr_out) = store_treesync_treekem_state me st tr in
    trace_invariant tr_out
  ))
let store_treesync_treekem_state_proof #invs tr me st =
  reveal_opaque (`%store_treesync_treekem_state) (store_treesync_treekem_state);
  reveal_opaque (`%treesync_treekem_state_invariant) (treesync_treekem_state_invariant);
  reveal_opaque (`%treesync_treekem_state_invariant_aux) (treesync_treekem_state_invariant_aux #_ #st.leaf_index);
  reveal_opaque (`%treesync_treekem_state_coarse_invariant) (treesync_treekem_state_coarse_invariant);
  reveal_opaque (`%treesync_treekem_state_very_coarse_invariant) (treesync_treekem_state_very_coarse_invariant);
  reveal_opaque (`%treekem_keyschedule_state_good) (treekem_keyschedule_state_good);
  intro_i_am_in_group_context me st.group_context st.treesync.tree st.leaf_index;
  let sid, tr = new_session_id me tr in
  let confirmation_tag = st.treekem.keyschedule_state.epoch_keys.confirmation_tag in
  treekem_keyschedule_state_auth_weak_exists_implies_key_is_authenticated_by_confirmation_tag st.treekem.keyschedule_state;
  store_epoch_secret_proof tr me SenderDataSecret st.group_context confirmation_tag st.treekem.keyschedule_state.epoch_keys.sender_data_secret;
  let sender_data_secret_sid, tr = store_epoch_secret me SenderDataSecret st.group_context confirmation_tag st.treekem.keyschedule_state.epoch_keys.sender_data_secret tr in
  store_epoch_secret_proof tr me ExporterSecret st.group_context confirmation_tag st.treekem.keyschedule_state.epoch_keys.exporter_secret;
  let exporter_secret_sid, tr = store_epoch_secret me ExporterSecret st.group_context confirmation_tag st.treekem.keyschedule_state.epoch_keys.exporter_secret tr in
  store_epoch_secret_proof tr me ExternalSecret st.group_context confirmation_tag st.treekem.keyschedule_state.epoch_keys.external_secret;
  let external_secret_sid, tr = store_epoch_secret me ExternalSecret st.group_context confirmation_tag st.treekem.keyschedule_state.epoch_keys.external_secret tr in
  store_epoch_secret_proof tr me MembershipKey st.group_context confirmation_tag st.treekem.keyschedule_state.epoch_keys.membership_key;
  let membership_key_sid, tr = store_epoch_secret me MembershipKey st.group_context confirmation_tag st.treekem.keyschedule_state.epoch_keys.membership_key tr in
  store_epoch_secret_proof tr me ResumptionPSK st.group_context confirmation_tag st.treekem.keyschedule_state.epoch_keys.resumption_psk;
  let resumption_psk_sid, tr = store_epoch_secret me ResumptionPSK st.group_context confirmation_tag st.treekem.keyschedule_state.epoch_keys.resumption_psk tr in
  store_epoch_secret_proof tr me EpochAuthenticator st.group_context confirmation_tag st.treekem.keyschedule_state.epoch_keys.epoch_authenticator;
  let epoch_authenticator_sid, tr = store_epoch_secret me EpochAuthenticator st.group_context confirmation_tag st.treekem.keyschedule_state.epoch_keys.epoch_authenticator tr in
  store_epoch_secret_proof tr me InitSecret st.group_context confirmation_tag st.treekem.keyschedule_state.init_secret;
  let init_secret_sid, tr = store_epoch_secret me InitSecret st.group_context confirmation_tag st.treekem.keyschedule_state.init_secret tr in
  store_node_keys_proof tr me st.treekem.tree_state.priv;
  let priv_sid, tr = store_node_keys me st.treekem.tree_state.priv tr in
  let bare_st: bare_treesync_treekem_state = {
    leaf_index = st.leaf_index;
    group_context = st.group_context;
    my_signature_key_sid = st.my_signature_key_sid;
    treesync = {
      group_id = st.group_context.group_id;
      levels = _;
      tree = st.treesync.tree;
      tokens = st.treesync.tokens;
    };
    treekem = {
      levels = _;
      tree = st.treekem.tree_state.tree;
      priv_sid;
      sender_data_secret_sid;
      exporter_secret_sid;
      external_secret_sid;
      membership_key_sid;
      resumption_psk_sid;
      epoch_authenticator_sid;
      confirmation_tag;
      init_secret_sid;
    }
  } in
  assert(treesync_treekem_state_pred.pred tr me sid bare_st)
#pop-options

#push-options "--z3rlimit 25"
val get_treesync_treekem_state_proof:
  {|protocol_invariants|} ->
  tr:trace ->
  me:principal -> sid:state_id ->
  Lemma
  (requires
    trace_invariant tr /\
    has_treesync_treekem_state_invariant /\
    has_treekem_epoch_secret_state_invariant /\
    has_treekem_node_keys_state_invariant
  )
  (ensures (
    let (opt_st, tr_out) = get_treesync_treekem_state me sid tr in
    tr_out == tr /\ (
      match opt_st with
      | Some st ->
        treesync_treekem_state_all_invariants tr_out me st
      | None -> True
    )
  ))
let get_treesync_treekem_state_proof #invs tr me sid =
  let tr0 = tr in
  reveal_opaque (`%get_treesync_treekem_state) (get_treesync_treekem_state);
  reveal_opaque (`%treesync_treekem_state_invariant) (treesync_treekem_state_invariant);
  reveal_opaque (`%treesync_treekem_state_coarse_invariant) (treesync_treekem_state_coarse_invariant);
  reveal_opaque (`%treesync_treekem_state_very_coarse_invariant) (treesync_treekem_state_very_coarse_invariant);
  reveal_opaque (`%treekem_keyschedule_state_good) (treekem_keyschedule_state_good);
  let opt_bare_st, tr = get_state #(bare_treesync_treekem_state) me sid tr in
  match opt_bare_st with
  | None -> ()
  | Some bare_st -> (
    reveal_opaque (`%treesync_treekem_state_invariant_aux) (treesync_treekem_state_invariant_aux #_ #bare_st.leaf_index);
    let confirmation_tag = bare_st.treekem.confirmation_tag in
    get_epoch_secret_proof tr me bare_st.treekem.sender_data_secret_sid SenderDataSecret bare_st.group_context confirmation_tag;
    get_epoch_secret_proof tr me bare_st.treekem.exporter_secret_sid ExporterSecret bare_st.group_context confirmation_tag;
    get_epoch_secret_proof tr me bare_st.treekem.external_secret_sid ExternalSecret bare_st.group_context confirmation_tag;
    get_epoch_secret_proof tr me bare_st.treekem.membership_key_sid MembershipKey bare_st.group_context confirmation_tag;
    get_epoch_secret_proof tr me bare_st.treekem.resumption_psk_sid ResumptionPSK bare_st.group_context confirmation_tag;
    get_epoch_secret_proof tr me bare_st.treekem.epoch_authenticator_sid EpochAuthenticator bare_st.group_context confirmation_tag;
    get_epoch_secret_proof tr me bare_st.treekem.init_secret_sid InitSecret bare_st.group_context confirmation_tag;
    get_node_keys_proof #_ #bare_st.treekem.levels #0 #bare_st.leaf_index tr me bare_st.treekem.priv_sid;
    let (opt_st, tr_out) = get_treesync_treekem_state me sid tr0 in
    match opt_st with
    | None -> ()
    | Some st -> (
      reveal_opaque (`%treesync_treekem_state_invariant_aux) (treesync_treekem_state_invariant_aux #_ #st.leaf_index);
      FStar.Classical.forall_intro (FStar.Classical.move_requires (key_is_authenticated_by_confirmation_tag_inj InitSecret bare_st.treekem.confirmation_tag st.treekem.keyschedule_state.init_secret));
      key_is_authenticated_by_confirmation_tag_implies_treekem_keyschedule_state_auth_weak_exists st.treekem.keyschedule_state
    )
  )
#pop-options
