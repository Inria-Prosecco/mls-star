module MLS.TreeKEM.Symbolic.State.EpochSecrets

open Comparse
open DY.Core
open DY.Lib
open MLS.NetworkTypes
open MLS.Tree
open MLS.TreeSync.NetworkTypes
open MLS.TreeSync.Types
open MLS.TreeKEM.NetworkTypes
open MLS.TreeKEM.API.KeySchedule.Types
open MLS.TreeSync.TreeHash
open MLS.TreeSync.TreeHash.Proofs
open MLS.Symbolic
open MLS.TreeSync.Symbolic.AuthService.CredentialInterpretation
open MLS.TreeKEM.Symbolic.ConfirmationTag

#set-options "--fuel 0 --ifuel 0"

(*** Local state ***)

type epoch_secret_type =
  | InitSecret: epoch_secret_type
  | SenderDataSecret: epoch_secret_type
  // The encryption secret should be managed by TreeDEM (once it is proved)
  | EncryptionSecret: epoch_secret_type
  | ExporterSecret: epoch_secret_type
  | ExternalSecret: epoch_secret_type
  | ConfirmationKey: epoch_secret_type
  | MembershipKey: epoch_secret_type
  | ResumptionPSK: epoch_secret_type
  | EpochAuthenticator: epoch_secret_type

#push-options "--fuel 1 --ifuel 1"
%splice [ps_epoch_secret_type] (gen_parser (`epoch_secret_type))
%splice [ps_epoch_secret_type_is_well_formed] (gen_is_well_formed_lemma (`epoch_secret_type))
#pop-options

[@@ with_bytes bytes]
type treekem_epoch_secret = {
  ty: epoch_secret_type;
  context: group_context_nt bytes;
  confirmation_tag: bytes;
  secret: bytes;
}

%splice [ps_treekem_epoch_secret] (gen_parser (`treekem_epoch_secret))
%splice [ps_treekem_epoch_secret_is_well_formed] (gen_is_well_formed_lemma (`treekem_epoch_secret))

instance local_state_treekem_epoch_secret: local_state treekem_epoch_secret = {
  tag = "MLS.TreeKEM.EpochSecrets";
  format = mk_parseable_serializeable ps_treekem_epoch_secret;
}

(*** Usage and labels ***)

[@@ with_bytes bytes]
type epoch_secret_usage_data = {
  group_context: group_context_nt bytes;
}

%splice [ps_epoch_secret_usage_data] (gen_parser (`epoch_secret_usage_data))

instance parseable_serializeable_bytes_epoch_secret_usage_data: parseable_serializeable bytes epoch_secret_usage_data =
  mk_parseable_serializeable ps_epoch_secret_usage_data

#push-options "--ifuel 1"
val mk_epoch_secret_usage:
  epoch_secret_type -> group_context_nt bytes ->
  usage
let mk_epoch_secret_usage ty group_context =
  match ty with
  | InitSecret ->
    KdfExpandKey "MLS.TreeKEM.InitSecret" (serialize _ {group_context})
  | SenderDataSecret ->
    KdfExpandKey "MLS.TreeDEM.SenderDataSecret" (serialize _ {group_context})
  | EncryptionSecret ->
    KdfExpandKey "MLS.TreeDEM.EncryptionSecret" (serialize _ {group_context})
  | ExporterSecret ->
    KdfExpandKey "MLS.TreeKEM.ExporterSecret" (serialize _ {group_context})
  | ExternalSecret ->
    NoUsage
  | ConfirmationKey ->
    MacKey "MLS.TreeKEM.ConfirmationKey" (serialize _ {group_context})
  | MembershipKey ->
    NoUsage
  | ResumptionPSK ->
    NoUsage
  | EpochAuthenticator ->
    NoUsage
#pop-options

val mk_principal_epoch_secret_label_pred:
  principal -> epoch_secret_type -> group_context_nt bytes ->
  principal -> string -> state_id -> treekem_epoch_secret -> prop
let mk_principal_epoch_secret_label_pred prin1 ty group_context =
  fun prin2 tag sid st ->
    prin1 == prin2 /\
    tag == "MLS.TreeKEM.EpochSecrets" /\
    st.ty == ty /\
    st.context == group_context

val mk_principal_epoch_secret_label:
  epoch_secret_type -> principal -> group_context_nt bytes ->
  label
let mk_principal_epoch_secret_label ty prin group_context =
  typed_state_pred_label (mk_principal_epoch_secret_label_pred prin ty group_context)

val mk_tree_secret_label_aux:
  #l:nat ->
  (principal -> group_context_nt bytes -> label) ->
  group_context_nt bytes -> treesync bytes tkt l 0 ->
  leaf_index l 0 ->
  label
let mk_tree_secret_label_aux #l mk_label group_context t li =
  match leaf_at t li with
  | None -> secret
  | Some leaf_node -> (
    match credential_to_principal leaf_node.data.credential with
    | None -> DY.Core.Label.Unknown.unknown_label
    | Some prin -> (
      mk_label prin group_context
    )
  )

val mk_tree_secret_label:
  #l:nat ->
  (principal -> group_context_nt bytes -> label) ->
  group_context_nt bytes -> treesync bytes tkt l 0 ->
  label
let mk_tree_secret_label #l mk_label group_context t =
  big_join (mk_tree_secret_label_aux mk_label group_context t)

type full_tree = l:nat & treesync bytes tkt l 0

val tree_hash_full_tree_rel:
  bytes -> full_tree ->
  prop
let tree_hash_full_tree_rel t_hash (|l, t|) =
  tree_has_hash t t_hash

val mk_group_secret_label_aux:
  (principal -> group_context_nt bytes -> label) ->
  group_context_nt bytes -> full_tree ->
  label
let mk_group_secret_label_aux mk_label group_context (|l, t|) =
  meet
    (prop_to_label (tree_hash_full_tree_rel group_context.tree_hash (|l, t|)))
    (mk_tree_secret_label mk_label group_context t)

val mk_group_secret_label:
  (principal -> group_context_nt bytes -> label) -> group_context_nt bytes ->
  label
let mk_group_secret_label mk_label group_context =
  big_join (mk_group_secret_label_aux mk_label group_context)

val mk_group_secret_label_eq:
  #l:nat ->
  mk_label:(principal -> group_context_nt bytes -> label) -> group_context:group_context_nt bytes ->
  t:treesync bytes tkt l 0 ->
  Lemma
  (requires tree_has_hash t group_context.tree_hash)
  (ensures
    mk_group_secret_label mk_label group_context == mk_tree_secret_label mk_label group_context t
  )
let mk_group_secret_label_eq #l mk_label group_context t =
  intro_label_equal
    (mk_group_secret_label mk_label group_context)
    (mk_tree_secret_label mk_label group_context t)
    (fun tr ->
      // ->
      big_join_flow_to_component tr (mk_group_secret_label_aux mk_label group_context) (|l, t|);
      prop_to_label_true (tree_hash_full_tree_rel group_context.tree_hash (|l, t|));

      // <-
      introduce forall ft2. mk_tree_secret_label mk_label group_context t  `can_flow tr` mk_group_secret_label_aux mk_label group_context ft2 with (
        let (|l2, t2|) = ft2 in
        let p = tree_hash_full_tree_rel group_context.tree_hash ft2 in
        eliminate p \/ ~p
        returns _
        with _. (
          let (b1, b2) = tree_hash_inj t t2 in
          FStar.Classical.move_requires_2 hash_injective b1 b2
        )
        and _. (
          prop_to_label_false p
        )
      )
    )

val mk_tree_secret_label_is_corrupt:
  #l:nat ->
  tr:trace ->
  mk_label:(principal -> group_context_nt bytes -> label) -> group_context:group_context_nt bytes -> t:treesync bytes tkt l 0 ->
  Lemma
  (requires
    (forall leaf_index. Some? (leaf_at t leaf_index) ==> (Some? (credential_to_principal (Some?.v (leaf_at t leaf_index)).data.credential))) /\
    is_corrupt tr (mk_tree_secret_label mk_label group_context t)
  )
  (ensures (
    exists leaf_index.
      Some? (leaf_at t leaf_index) /\
      is_corrupt tr (mk_label (Some?.v (credential_to_principal (Some?.v (leaf_at t leaf_index)).data.credential)) group_context)
  ))
let mk_tree_secret_label_is_corrupt #l tr mk_label group_context t =
  normalize_term_spec (is_corrupt tr secret)

val i_am_in_tree_at:
  #l:nat ->
  principal -> treesync bytes tkt l 0 -> leaf_index l 0 ->
  prop
let i_am_in_tree_at #l me tree leaf_ind =
  Some? (leaf_at tree leaf_ind) /\
  credential_to_principal ((Some?.v (leaf_at tree leaf_ind)).data.credential) == Some me

val i_am_in_group_context_with_witness:
  #l:nat ->
  principal -> group_context_nt bytes -> treesync bytes tkt l 0 -> leaf_index l 0 ->
  prop
let i_am_in_group_context_with_witness #l me group_context tree leaf_ind =
  tree_hash_full_tree_rel group_context.tree_hash (|l, tree|) /\
  i_am_in_tree_at #l me tree leaf_ind

val i_am_in_group_context:
  principal -> group_context_nt bytes ->
  prop
let i_am_in_group_context me group_context =
  exists (l:nat) (tree:treesync bytes tkt l 0) (leaf_ind:leaf_index l 0).
    i_am_in_group_context_with_witness me group_context tree leaf_ind

val intro_i_am_in_group_context:
  #l:nat ->
  me:principal -> group_context:group_context_nt bytes -> tree:treesync bytes tkt l 0 -> leaf_ind:leaf_index l 0 ->
  Lemma
  (requires i_am_in_group_context_with_witness me group_context tree leaf_ind)
  (ensures i_am_in_group_context me group_context)
let intro_i_am_in_group_context #l me group_context tree leaf_ind = ()

val mk_group_secret_label_can_flow_my_label:
  tr:trace ->
  me:principal -> mk_label:(principal -> group_context_nt bytes -> label) -> group_context:group_context_nt bytes ->
  Lemma
  (requires i_am_in_group_context me group_context)
  (ensures
    mk_group_secret_label mk_label group_context `can_flow tr` mk_label me group_context
  )
let mk_group_secret_label_can_flow_my_label tr me mk_label group_context =
  eliminate exists (l:nat) (tree:treesync bytes tkt l 0) (leaf_ind:leaf_index l 0). i_am_in_group_context_with_witness me group_context tree leaf_ind
  returns mk_group_secret_label mk_label group_context `can_flow tr` mk_label me group_context
  with _. (
    mk_group_secret_label_eq mk_label group_context tree;
    big_join_flow_to_component tr (mk_tree_secret_label_aux mk_label group_context tree) leaf_ind
  )

#push-options "--ifuel 1"
val keyschedule_state_to_key:
  treekem_keyschedule_state bytes -> epoch_secret_type ->
  bytes
let keyschedule_state_to_key st ty =
  match ty with
  | InitSecret ->
    st.init_secret
  | SenderDataSecret ->
    st.epoch_keys.sender_data_secret
  | EncryptionSecret ->
    empty
  | ExporterSecret ->
    st.epoch_keys.exporter_secret
  | ExternalSecret ->
    st.epoch_keys.external_secret
  | ConfirmationKey ->
    empty
  | MembershipKey ->
    st.epoch_keys.membership_key
  | ResumptionPSK ->
    st.epoch_keys.resumption_psk
  | EpochAuthenticator ->
    st.epoch_keys.epoch_authenticator
#pop-options

val key_is_authenticated_by_confirmation_tag_with_witness:
  treekem_keyschedule_state bytes -> epoch_secret_type -> bytes -> bytes ->
  prop
let key_is_authenticated_by_confirmation_tag_with_witness st ty confirmation_tag secret =
  treekem_keyschedule_state_auth_weak_exists st /\
  st.epoch_keys.confirmation_tag == confirmation_tag /\
  keyschedule_state_to_key st ty == secret

val key_is_authenticated_by_confirmation_tag:
  epoch_secret_type -> bytes -> bytes ->
  prop
let key_is_authenticated_by_confirmation_tag ty confirmation_tag secret =
  exists (st:treekem_keyschedule_state bytes).
    key_is_authenticated_by_confirmation_tag_with_witness st ty confirmation_tag secret

val key_is_authenticated_by_confirmation_tag_inj:
  ty:epoch_secret_type -> confirmation_tag:bytes -> secret1:bytes -> secret2:bytes ->
  Lemma
  (requires
    key_is_authenticated_by_confirmation_tag ty confirmation_tag secret1 /\
    key_is_authenticated_by_confirmation_tag ty confirmation_tag secret2
  )
  (ensures secret1 == secret2)
let key_is_authenticated_by_confirmation_tag_inj ty confirmation_tag secret1 secret2 =
  eliminate exists st1 st2.
    treekem_keyschedule_state_auth_weak_exists st1 /\
    st1.epoch_keys.confirmation_tag == confirmation_tag /\
    keyschedule_state_to_key st1 ty == secret1 /\
    treekem_keyschedule_state_auth_weak_exists st2 /\
    st2.epoch_keys.confirmation_tag == confirmation_tag /\
    keyschedule_state_to_key st2 ty == secret2
  returns secret1 == secret2
  with _. (
    treekem_keyschedule_state_auth_weak_exists_inj st1 st2
  )

(*** Local state invariant ***)

val is_epoch_secret:
  {|crypto_invariants|} ->
  trace -> epoch_secret_type -> group_context_nt bytes -> bytes ->
  prop
let is_epoch_secret #cinvs tr ty group_context secret =
  bytes_invariant tr secret /\
  get_label tr secret `can_flow tr` mk_group_secret_label (mk_principal_epoch_secret_label ty) group_context /\
  secret `has_usage tr` mk_epoch_secret_usage ty group_context

val treekem_epoch_secret_state_pred: {|crypto_invariants|} -> local_state_predicate treekem_epoch_secret
let treekem_epoch_secret_state_pred #cinvs = {
  pred = (fun tr prin sid content ->
    i_am_in_group_context prin content.context /\
    is_well_formed _ (is_publishable tr) content.context /\
    is_publishable tr content.confirmation_tag /\
    is_epoch_secret tr content.ty content.context content.secret /\
    key_is_authenticated_by_confirmation_tag content.ty content.confirmation_tag content.secret
  );
  pred_later = (fun tr1 tr2 prin sid content -> ());
  pred_knowable = (fun tr prin sid content ->
    mk_group_secret_label_can_flow_my_label tr prin (mk_principal_epoch_secret_label content.ty) content.context;
    assert(is_well_formed _ (is_knowable_by (mk_principal_epoch_secret_label content.ty prin content.context) tr) content.context);
    assert(is_well_formed _ (is_knowable_by (mk_principal_epoch_secret_label content.ty prin content.context) tr) content)
  );
}

val has_treekem_epoch_secret_state_invariant: {|protocol_invariants|} -> prop
let has_treekem_epoch_secret_state_invariant #invs =
  has_local_state_predicate treekem_epoch_secret_state_pred

val treekem_epoch_secret_state_tag_and_invariant: {|crypto_invariants|} -> dtuple2 string local_bytes_state_predicate
let treekem_epoch_secret_state_tag_and_invariant #ci = (|local_state_treekem_epoch_secret.tag, local_state_predicate_to_local_bytes_state_predicate treekem_epoch_secret_state_pred|)

(*** Traceful API ***)

[@"opaque_to_smt"]
val store_epoch_secret:
  principal ->
  epoch_secret_type -> group_context_nt bytes -> bytes -> bytes ->
  traceful state_id
let store_epoch_secret me ty context confirmation_tag secret =
  let* sid = new_session_id me in
  set_state me sid {
    ty;
    context;
    confirmation_tag;
    secret;
  };*
  return sid

[@"opaque_to_smt"]
val get_epoch_secret:
  principal ->
  state_id -> epoch_secret_type -> group_context_nt bytes -> bytes ->
  traceful (option bytes)
let get_epoch_secret me sid ty context confirmation_tag =
  let*? st = get_state me sid in
  guard_tr (st.ty = ty);*?
  guard_tr (st.context = context);*?
  guard_tr (st.confirmation_tag = confirmation_tag);*?
  return (Some st.secret)

(*** Traceful API proof ***)

val store_epoch_secret_proof:
  {|protocol_invariants|} ->
  tr:trace ->
  me:principal ->
  ty:epoch_secret_type -> context:group_context_nt bytes -> confirmation_tag:bytes -> secret:bytes ->
  Lemma
  (requires
    i_am_in_group_context me context /\
    is_well_formed _ (is_publishable tr) context /\
    is_publishable tr confirmation_tag /\
    is_epoch_secret tr ty context secret /\
    key_is_authenticated_by_confirmation_tag ty confirmation_tag secret /\
    trace_invariant tr /\
    has_treekem_epoch_secret_state_invariant
  )
  (ensures (
    let (_, tr_out) = store_epoch_secret me ty context confirmation_tag secret tr in
    trace_invariant tr_out
  ))
let store_epoch_secret_proof #invs tr me ty context confirmation_tag secret =
  reveal_opaque (`%store_epoch_secret) (store_epoch_secret)

val get_epoch_secret_proof:
  {|protocol_invariants|} ->
  tr:trace ->
  me:principal -> sid:state_id ->
  ty:epoch_secret_type -> context:group_context_nt bytes -> confirmation_tag:bytes ->
  Lemma
  (requires
    trace_invariant tr /\
    has_treekem_epoch_secret_state_invariant
  )
  (ensures (
    let (opt_secret, tr_out) = get_epoch_secret me sid ty context confirmation_tag tr in
    tr_out == tr /\ (
      match opt_secret with
      | None -> True
      | Some secret -> (
        is_epoch_secret tr ty context secret /\
        key_is_authenticated_by_confirmation_tag ty confirmation_tag secret
      )
    )
  ))
let get_epoch_secret_proof #invs tr me sid ty context confirmation_tag =
  reveal_opaque (`%get_epoch_secret) (get_epoch_secret)
