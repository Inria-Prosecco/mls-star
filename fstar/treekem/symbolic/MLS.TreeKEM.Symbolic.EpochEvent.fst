module MLS.TreeKEM.Symbolic.EpochEvent

open FStar.List.Tot { for_allP }
open Comparse
open DY.Core
open DY.Lib
open MLS.Tree
open MLS.Crypto
open MLS.NetworkTypes
open MLS.TreeSync.NetworkTypes
open MLS.TreeSync.Types
open MLS.TreeKEM.NetworkTypes
open MLS.TreeKEM.KeySchedule
open MLS.TreeKEM.API.KeySchedule.Types
open MLS.TreeSync.API.LeafAt { tree_add_only_rel }
open MLS.Bootstrap.NetworkTypes
open MLS.Symbolic
open MLS.TreeSync.Symbolic.State.SignatureKey
open MLS.TreeSync.Symbolic.Parsers
open MLS.TreeSync.Symbolic.AuthService.CredentialInterpretation
open MLS.TreeSync.Symbolic.Event.LeafNodeHasBeenVerified
open MLS.TreeKEM.Symbolic.Tree.Labels
open MLS.TreeKEM.Symbolic.State.EpochSecrets
open MLS.TreeKEM.Symbolic.PSK
open MLS.TreeKEM.Symbolic.API.KeySchedule
open MLS.Bootstrap.Symbolic.KeyPackage
open MLS.Result

#set-options "--fuel 1 --ifuel 1"

val ps_psks:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  parser_serializer bytes (list (pre_shared_key_id_nt bytes & bytes))
let ps_psks #bytes #bl =
  ps_list (
    mk_isomorphism
      (pre_shared_key_id_nt bytes & bytes)
      (Comparse.bind ps_pre_shared_key_id_nt (fun _ -> ps_bytes))
      (fun (|x,y|) -> (x,y))
      (fun (x,y) -> (|x,y|))
  )

type all_keyschedule_keys (bytes:Type0) {|bytes_like bytes|} = {
  sender_data_secret: bytes;
  exporter_secret: bytes;
  external_secret: bytes;
  membership_key: bytes;
  resumption_psk: bytes;
  epoch_authenticator: bytes;
  confirmation_tag: bytes;
  init_secret: bytes;
}

%splice [ps_all_keyschedule_keys] (gen_parser (`all_keyschedule_keys))

val ps_treekem_keyschedule_state:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  parser_serializer bytes (treekem_keyschedule_state bytes)
let ps_treekem_keyschedule_state #bytes #bl =
  mk_isomorphism (treekem_keyschedule_state bytes) ps_all_keyschedule_keys
    (fun {sender_data_secret; exporter_secret; external_secret; membership_key; resumption_psk; epoch_authenticator; confirmation_tag; init_secret} ->
      {epoch_keys = {sender_data_secret; exporter_secret; external_secret; membership_key; resumption_psk; epoch_authenticator; confirmation_tag} ; init_secret}
    )
    (fun {epoch_keys = {sender_data_secret; exporter_secret; external_secret; membership_key; resumption_psk; epoch_authenticator; confirmation_tag} ; init_secret} ->
      {sender_data_secret; exporter_secret; external_secret; membership_key; resumption_psk; epoch_authenticator; confirmation_tag; init_secret}
    )

type i_just_joined_group = {
  inviter: nat;
}

%splice [ps_i_just_joined_group] (gen_parser (`i_just_joined_group))

type commit_type =
  | AddOnlyCommit
  | FullCommit

%splice [ps_commit_type] (gen_parser (`commit_type))

[@@ with_bytes bytes]
type i_processed_commit_group = {
  previous_init_secret: bytes;
  previous_group_context: group_context_nt bytes;
  previous_tree_height: nat;
  [@@@ with_parser #bytes (ps_treesync tkt previous_tree_height 0)]
  previous_tree: treesync bytes tkt previous_tree_height 0;
  commit_ty: commit_type;
  [@@@ with_parser #bytes (ps_list (ps_key_package_nt tkt))]
  joiners: list (key_package_nt bytes tkt);
}

%splice [ps_i_processed_commit_group] (gen_parser (`i_processed_commit_group))

[@@ with_bytes bytes]
type how_am_i_in_group =
  | JustCreated: how_am_i_in_group
  | JustJoined: i_just_joined_group -> how_am_i_in_group
  | ProcessedCommit: i_processed_commit_group -> how_am_i_in_group

%splice [ps_how_am_i_in_group] (gen_parser (`how_am_i_in_group))

[@@ with_bytes bytes]
type i_am_in_group = {
  how: how_am_i_in_group;
  group_context: group_context_nt bytes;
  tree_height: nat;
  [@@@ with_parser #bytes (ps_treesync tkt tree_height 0)]
  tree: treesync bytes tkt tree_height 0;
  [@@@ with_parser #bytes ps_psks]
  psks: list (pre_shared_key_id_nt bytes & bytes);
  [@@@ with_parser #bytes (ps_treekem_keyschedule_state #bytes)]
  epoch_keys: treekem_keyschedule_state bytes;
}

%splice [ps_i_am_in_group] (gen_parser (`i_am_in_group))

instance event_i_am_in_group: event i_am_in_group = {
  tag = "MLS.TreeKEM.IAmInGroup";
  format = mk_parseable_serializeable ps_i_am_in_group;
}

val joiner_is_stale_participant:
  #l:nat ->
  treesync bytes tkt l 0 -> key_package_nt bytes tkt ->
  prop
let joiner_is_stale_participant #l tree joiner =
  exists li.
    Some? (leaf_at tree li) /\
    (Some?.v (leaf_at tree li)) == joiner.tbs.leaf_node /\
    (Some?.v (leaf_at tree li)).data.source == LNS_key_package

val joiners_are_stale_participants:
  #l:nat ->
  treesync bytes tkt l 0 -> list (key_package_nt bytes tkt) ->
  prop
let joiners_are_stale_participants #l tree joiners =
  for_allP (joiner_is_stale_participant tree) joiners

val has_same_event_as_me:
  i_am_in_group ->
  group_context_nt bytes -> list (pre_shared_key_id_nt bytes & bytes) -> treekem_keyschedule_state bytes ->
  prop
let has_same_event_as_me inviter_ev group_context psks epoch_keys =
  inviter_ev.group_context == group_context /\
  inviter_ev.epoch_keys == epoch_keys /\
  inviter_ev.psks == psks /\
  ProcessedCommit? inviter_ev.how /\
  joiners_are_stale_participants inviter_ev.tree (ProcessedCommit?._0 inviter_ev.how).joiners

val inviter_has_same_event_as_me:
  trace -> principal ->
  group_context_nt bytes -> list (pre_shared_key_id_nt bytes & bytes) -> treekem_keyschedule_state bytes ->
  prop
let inviter_has_same_event_as_me tr inviter_id group_context psks epoch_keys =
  exists inviter_ev.
    has_same_event_as_me inviter_ev group_context psks epoch_keys /\
    event_triggered tr inviter_id inviter_ev

val i_have_previous_epoch_event_with_witness:
  #previous_tree_height:nat ->
  trace -> principal ->
  group_context_nt bytes -> bytes -> treesync bytes tkt previous_tree_height 0 ->
  i_am_in_group ->
  prop
let i_have_previous_epoch_event_with_witness #previous_tree_height tr me previous_group_context previous_init_secret previous_tree previous_ev =
  event_triggered tr me previous_ev /\
  previous_ev.group_context == previous_group_context /\
  previous_ev.tree_height == previous_tree_height /\
  previous_ev.tree == previous_tree /\
  previous_ev.epoch_keys.init_secret == previous_init_secret

val i_have_previous_epoch_event:
  #previous_tree_height:nat ->
  trace -> principal ->
  group_context_nt bytes -> bytes -> treesync bytes tkt previous_tree_height 0 ->
  prop
let i_have_previous_epoch_event tr me previous_group_context previous_init_secret previous_tree =
  exists (previous_ev:i_am_in_group).
    i_have_previous_epoch_event_with_witness tr me previous_group_context previous_init_secret previous_tree previous_ev

val i_am_in_group_pred: {|crypto_invariants|} -> event_predicate i_am_in_group
let i_am_in_group_pred #cinvs tr me ev =
  MLS.TreeSync.TreeHash.Proofs.tree_has_hash ev.tree ev.group_context.tree_hash /\
  i_have_verified_every_leaf_node tr me ev.tree ev.group_context.group_id /\
  (
    match ev.how with
    | JustCreated -> (
      ev.group_context.epoch == 0 /\
      ev.tree_height == 0 /\
      Some? (leaf_at ev.tree 0) /\
      credential_to_principal (Some?.v (leaf_at ev.tree 0)).data.credential == Some me /\
      treekem_keyschedule_state_good tr ev.epoch_keys ev.group_context /\
      treekem_keyschedule_state_label_good_aux tr secret ev.epoch_keys ev.group_context
    )
    | JustJoined { inviter } -> (
      inviter < pow2 ev.tree_height /\
      Some? (leaf_at ev.tree inviter) /\
      Some? (credential_to_principal (Some?.v (leaf_at ev.tree inviter)).data.credential) /\ (
        let Some inviter_leaf_node = leaf_at ev.tree inviter in
        let Some inviter_id = credential_to_principal inviter_leaf_node.data.credential in
        (
          is_corrupt tr (signature_key_label inviter_id inviter_leaf_node.data.signature_key)
        ) \/ (
          inviter_has_same_event_as_me tr inviter_id ev.group_context ev.psks ev.epoch_keys
        )
      )
    )
    | ProcessedCommit last_epoch_link -> (
      bytes_invariant tr last_epoch_link.previous_init_secret /\
      last_epoch_link.previous_group_context.group_id == ev.group_context.group_id /\
      last_epoch_link.previous_group_context.epoch+1 == ev.group_context.epoch /\
      (last_epoch_link.commit_ty == AddOnlyCommit ==> tree_add_only_rel last_epoch_link.previous_tree ev.tree) /\
      psks_bytes_invariant tr ev.psks /\
      i_have_verified_every_key_package tr me last_epoch_link.joiners /\
      i_have_previous_epoch_event tr me last_epoch_link.previous_group_context last_epoch_link.previous_init_secret last_epoch_link.previous_tree /\
      (
        let commit_secret_label =
          match last_epoch_link.commit_ty with
          | AddOnlyCommit -> public
          | FullCommit -> node_sk_label ev.tree ev.group_context.group_id
        in
        treekem_keyschedule_state_good tr ev.epoch_keys ev.group_context /\
        treekem_keyschedule_state_label_good tr last_epoch_link.previous_init_secret commit_secret_label last_epoch_link.joiners ev.psks ev.epoch_keys ev.group_context
      )
    )
  )

val has_i_am_in_group_invariant:
  {|protocol_invariants|} ->
  prop
let has_i_am_in_group_invariant #invs =
  has_event_pred i_am_in_group_pred

val i_am_in_group_tag_and_invariant: {|crypto_invariants|} -> (string & compiled_event_predicate)
let i_am_in_group_tag_and_invariant #cinvs =
  (event_i_am_in_group.tag, compile_event_pred i_am_in_group_pred)

val has_treekem_invariants:
  {|protocol_invariants|} ->
  prop
let has_treekem_invariants #invs =
  has_key_package_has_been_verified_invariant /\
  has_leaf_node_has_been_verified_invariant tkt /\
  has_i_am_in_group_invariant
