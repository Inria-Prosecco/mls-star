module MLS.TreeKEM.Symbolic.SecurityTheorem

open Comparse
open DY.Core
open DY.Lib
open MLS.Tree
open MLS.NetworkTypes
open MLS.TreeKEM.NetworkTypes
open MLS.TreeSync.NetworkTypes
open MLS.TreeSync.Types
open MLS.Bootstrap.NetworkTypes
open MLS.TreeSync.Symbolic.Event.LeafNodeHasBeenVerified
open MLS.TreeSync.Symbolic.State.SignatureKey
open MLS.TreeSync.Symbolic.AuthService.CredentialInterpretation
open MLS.TreeKEM.Symbolic.State.NodeKey
open MLS.TreeKEM.Symbolic.Tree.Labels
open MLS.TreeKEM.Symbolic.EpochEvent
open MLS.TreeKEM.Symbolic.State.EpochSecrets
open MLS.TreeKEM.Symbolic.KeySchedule
open MLS.TreeKEM.Symbolic.PSK
open MLS.TreeKEM.Symbolic.API.KeySchedule
open MLS.Bootstrap.Symbolic.State.InitKey
open MLS.Bootstrap.Symbolic.KeyPackage

#set-options "--fuel 0 --ifuel 0"

(*** Helper predicates for security theorem ***)

val participant_init_key_is_compromised:
  trace -> principal -> group_context_nt bytes ->
  prop
let participant_init_key_is_compromised tr participant group_context =
  is_corrupt tr (mk_principal_epoch_secret_label InitSecret participant group_context)

val init_key_is_compromised:
  #l:nat ->
  trace -> group_context_nt bytes -> treesync bytes tkt l 0 ->
  prop
let init_key_is_compromised #l tr group_context tree =
  exists leaf_index.
    Some? (leaf_at tree leaf_index) /\
    Some? (credential_to_principal (Some?.v (leaf_at tree leaf_index)).data.credential) /\ (
      let participant = Some?.v (credential_to_principal (Some?.v (leaf_at tree leaf_index)).data.credential) in
      participant_init_key_is_compromised tr participant group_context
    )

val joiners_init_key_is_compromised:
  trace ->
  key_package_nt bytes tkt ->
  prop
let joiners_init_key_is_compromised tr joiner =
  Some? (key_package_to_principal joiner) /\
  is_corrupt tr (init_key_label (Some?.v (key_package_to_principal joiner)) joiner.tbs.init_key)

val joiners_signature_key_is_compromised_before_i_checked_it:
  trace ->
  principal -> key_package_nt bytes tkt ->
  prop
let joiners_signature_key_is_compromised_before_i_checked_it tr me joiner =
  Some? (key_package_to_principal joiner) /\
  i_have_verified_key_package tr me joiner /\ (
    let joiner_id = (Some?.v (key_package_to_principal joiner)) in
    let tr_before_check = prefix tr (find_event_triggered_at_timestamp tr me {key_package=joiner}) in
    is_corrupt tr_before_check (signature_key_label joiner_id joiner.tbs.leaf_node.data.signature_key)
  )

val node_key_is_compromised:
  trace ->
  leaf_node_nt bytes tkt ->
  prop
let node_key_is_compromised tr leaf_node =
  Some? (credential_to_principal leaf_node.data.credential) /\
  is_corrupt tr (node_key_label (Some?.v (credential_to_principal leaf_node.data.credential)) leaf_node.data.content)

val signature_key_is_compromised_before_i_checked_leaf_node:
  trace ->
  principal -> leaf_node_nt bytes tkt -> mls_bytes bytes -> nat ->
  prop
let signature_key_is_compromised_before_i_checked_leaf_node tr me leaf_node group_id leaf_index =
  Some? (credential_to_principal leaf_node.data.credential) /\
  i_have_verified_leaf_node tr me leaf_node group_id leaf_index /\ (
    let leaf_node_id = (Some?.v (credential_to_principal leaf_node.data.credential)) in
    let tr_before_check = prefix tr (find_event_triggered_at_timestamp tr me {leaf_node; group_id; leaf_index}) in
    is_corrupt tr_before_check (signature_key_label leaf_node_id leaf_node.data.signature_key)
  )

val corresponding_init_key_is_compromised:
  trace ->
  leaf_node_nt bytes tkt ->
  prop
let corresponding_init_key_is_compromised tr leaf_node =
  Some? (credential_to_principal leaf_node.data.credential) /\
  exists (verifier:principal) (key_package:key_package_nt bytes tkt).
    key_package.tbs.leaf_node == leaf_node /\
    i_have_verified_key_package tr verifier key_package /\ (
      is_corrupt tr (init_key_label (Some?.v (credential_to_principal leaf_node.data.credential)) key_package.tbs.init_key) \/ (
        let tr_before_check = prefix tr (find_event_triggered_at_timestamp tr verifier {key_package}) in
        is_corrupt tr_before_check (signature_key_label (Some?.v (credential_to_principal leaf_node.data.credential)) leaf_node.data.signature_key)
      )
    )

val inviter_signature_key_is_compromised_before_i_joined:
  tr:trace ->
  me:principal -> leaf_node_nt bytes tkt -> ev:i_am_in_group ->
  #squash (event_triggered tr me ev) ->
  prop
let inviter_signature_key_is_compromised_before_i_joined tr me inviter_leaf_node ev #_ =
  Some? (credential_to_principal inviter_leaf_node.data.credential) /\ (
    let inviter_id = (Some?.v (credential_to_principal inviter_leaf_node.data.credential)) in
    let tr_before_check = prefix tr (find_event_triggered_at_timestamp tr me ev) in
    is_corrupt tr_before_check (signature_key_label inviter_id inviter_leaf_node.data.signature_key)
  )

val inviter_was_in_same_group_as_me:
  tr:trace ->
  leaf_node_nt bytes tkt -> ev:i_am_in_group ->
  prop
let inviter_was_in_same_group_as_me tr inviter_leaf_node ev =
  Some? (credential_to_principal inviter_leaf_node.data.credential) /\ (
    let inviter_id = (Some?.v (credential_to_principal inviter_leaf_node.data.credential)) in
    exists (inviter_ev:i_am_in_group).
      inviter_ev.group_context == ev.group_context /\
      inviter_ev.tree_height == ev.tree_height /\
      inviter_ev.tree == ev.tree /\
      inviter_ev.epoch_keys.init_secret == ev.epoch_keys.init_secret /\
      inviter_ev.psks == ev.psks /\
      ProcessedCommit? inviter_ev.how /\
      joiners_are_stale_participants ev.tree (ProcessedCommit?._0 inviter_ev.how).joiners /\
      event_triggered tr inviter_id inviter_ev
  )

val all_psks_are_publishable:
  {|crypto_invariants|} ->
  tr:trace ->
  list (pre_shared_key_id_nt bytes & bytes) ->
  prop
let all_psks_are_publishable #cinvs tr psks =
  forall psk_id psk.
    List.Tot.memP (psk_id, psk) psks ==>
    is_publishable tr psk

(*** Helper lemmas for security theorem ***)

#push-options "--fuel 1 --ifuel 1"
val psk_secret_label_corrupt_implies_all_psks_are_publishable:
  {|crypto_invariants|} ->
  tr:trace ->
  psks:list (pre_shared_key_id_nt bytes & bytes) ->
  Lemma
  (requires
    psks_bytes_invariant tr psks /\
    is_corrupt tr (psks_label tr psks)
  )
  (ensures all_psks_are_publishable tr psks)
let rec psk_secret_label_corrupt_implies_all_psks_are_publishable #cinvs tr psks =
  match psks with
  | [] -> ()
  | h::t -> psk_secret_label_corrupt_implies_all_psks_are_publishable tr t
#pop-options

#push-options "--fuel 1 --ifuel 1"
val is_corrupt_joiners_label_implies_exists:
  tr:trace ->
  joiners:list (key_package_nt bytes tkt) ->
  Lemma
  (requires
    is_corrupt tr (List.Tot.fold_right join (List.Tot.map key_package_to_init_label joiners) secret)
  )
  (ensures
    exists (joiner:key_package_nt bytes tkt).
      List.Tot.memP joiner joiners /\
      is_corrupt tr (key_package_to_init_label joiner)
  )
let rec is_corrupt_joiners_label_implies_exists tr joiners =
  match joiners with
  | [] ->
    assert(is_corrupt tr secret);
    normalize_term_spec (is_corrupt tr secret);
    assert(False)
  | h::t ->
    let post =
      exists (joiner:key_package_nt bytes tkt).
        List.Tot.memP joiner joiners /\
        is_corrupt tr (key_package_to_init_label joiner)
    in
    eliminate is_corrupt tr (key_package_to_init_label h) \/ is_corrupt tr (List.Tot.fold_right join (List.Tot.map key_package_to_init_label t) secret)
    returns post
    with _. (
      ()
    )
    and _. (
      is_corrupt_joiners_label_implies_exists tr t
    )
#pop-options

val is_corrupt_key_package_to_init_label_implies:
  {|protocol_invariants|} ->
  tr:trace -> me:principal ->
  joiner:key_package_nt bytes tkt ->
  Lemma
  (requires
    is_corrupt tr (key_package_to_init_label joiner) /\
    i_have_verified_key_package tr me joiner /\
    trace_invariant tr /\
    has_treekem_invariants
  )
  (ensures
    joiners_init_key_is_compromised tr joiner \/
    joiners_signature_key_is_compromised_before_i_checked_it tr me joiner
  )
let is_corrupt_key_package_to_init_label_implies #invs tr me joiner =
  key_package_to_init_label_is_corrupt tr me joiner

#push-options "--fuel 1 --ifuel 1"
val is_corrupt_commit_secret_implies_exists_leaf:
  #l:nat -> #i:tree_index l ->
  tr:trace ->
  t:treesync bytes tkt l i -> group_id:mls_bytes bytes ->
  Lemma
  (requires
    is_corrupt tr (node_sk_label t group_id)
  )
  (ensures
    exists (li:leaf_index l i).
      Some? (leaf_at t li) /\
      is_corrupt tr (node_sk_label_aux_leaf (Some?.v (leaf_at t li)) group_id YesCommitter li)
  )
let rec is_corrupt_commit_secret_implies_exists_leaf #l #i tr t group_id =
  match t with
  | TLeaf None ->
    assert(is_corrupt tr secret);
    normalize_term_spec (is_corrupt tr secret);
    assert(False)
  | TLeaf (Some _) ->
    let li: leaf_index l i = i in
    assert(Some? (leaf_at t li))
  | TNode _ left right ->
    let post =
      exists (li:leaf_index l i).
        Some? (leaf_at t li) /\
        is_corrupt tr (node_sk_label_aux_leaf (Some?.v (leaf_at t li)) group_id YesCommitter li)
    in
    eliminate is_corrupt tr (node_sk_label left group_id) \/ is_corrupt tr (node_sk_label right group_id)
    returns post
    with _. (
      is_corrupt_commit_secret_implies_exists_leaf tr left group_id;
      assert(forall (li:leaf_index (l-1) (left_index i)).
        Some? (leaf_at left li) <==> Some? (leaf_at t li)
      )
    )
    and _. (
      is_corrupt_commit_secret_implies_exists_leaf tr right group_id;
      assert(forall (li:leaf_index (l-1) (right_index i)).
        Some? (leaf_at right li) <==> Some? (leaf_at t li)
      )
    )
#pop-options

val is_corrupt_leaf_label_implies:
  {|protocol_invariants|} ->
  tr:trace -> me:principal ->
  group_id:mls_bytes bytes -> leaf_node:leaf_node_nt bytes tkt -> leaf_index:nat ->
  Lemma
  (requires
    is_corrupt tr (node_sk_label_aux_leaf leaf_node group_id YesCommitter leaf_index) /\
    i_have_verified_leaf_node tr me leaf_node group_id leaf_index /\
    trace_invariant tr /\
    has_leaf_node_has_been_verified_invariant tkt
  )
  (ensures
    node_key_is_compromised tr leaf_node \/
    signature_key_is_compromised_before_i_checked_leaf_node tr me leaf_node group_id leaf_index \/ (
      leaf_node.data.source == LNS_key_package /\
      corresponding_init_key_is_compromised tr leaf_node
    )
  )
let is_corrupt_leaf_label_implies #invs tr me group_id leaf_node leaf_index =
  let Some leaf_node_id = credential_to_principal leaf_node.data.credential in
  assert(is_corrupt tr (node_key_label leaf_node_id leaf_node.data.content) ==> node_key_is_compromised tr leaf_node);
  introduce is_corrupt tr (guarded_signature_key_label leaf_node group_id leaf_index) ==> signature_key_is_compromised_before_i_checked_leaf_node tr me leaf_node group_id leaf_index with _. (
    guarded_signature_key_label_is_corrupt tr me leaf_node group_id leaf_index
  );
  introduce is_corrupt tr (init_key_associated_with leaf_node) ==> corresponding_init_key_is_compromised tr leaf_node with _. (
    init_key_associated_with_is_corrupt tr leaf_node;
    eliminate
      exists (key_package:key_package_nt bytes tkt) verifier.
        i_have_verified_key_package tr verifier key_package /\
        key_package.tbs.leaf_node == leaf_node /\
        is_corrupt tr (key_package_to_init_label key_package)
    returns _
    with _. (
      key_package_to_init_label_is_corrupt tr verifier key_package
    )
  )

(*** Security theorem ***)

#push-options "--ifuel 1 --z3rlimit 200"
val treekem_security_theorem:
  {|protocol_invariants|} ->
  tr:trace ->
  me:principal -> ev:i_am_in_group ->
  Lemma
  (requires
    event_triggered tr me ev /\
    is_publishable tr ev.epoch_keys.init_secret /\
    trace_invariant tr /\
    has_treekem_invariants
  )
  (ensures (
    match ev.how with
    | ProcessedCommit last_epoch_link -> (
      // (1) the attacker compromised the epoch secret state
      (
        init_key_is_compromised tr ev.group_context ev.tree
      ) \/
      // (2) the attacker compromised a joiner's initialization key
      (
        (exists (joiner: key_package_nt bytes tkt).
          List.Tot.memP joiner last_epoch_link.joiners /\
          joiners_init_key_is_compromised tr joiner
        ) /\
        all_psks_are_publishable tr ev.psks
      ) \/
      // (3) the attacker compromised a joiner's signature key
      (
        (exists (joiner: key_package_nt bytes tkt).
          List.Tot.memP joiner last_epoch_link.joiners /\
          joiners_signature_key_is_compromised_before_i_checked_it tr me joiner
        ) /\
        all_psks_are_publishable tr ev.psks
      ) \/
      // (4)-(7): the attacker knows the previous init secret, pre-shared keys and...
      // (4) ... the commit is add-only
      (
        last_epoch_link.commit_ty == AddOnlyCommit /\
        all_psks_are_publishable tr ev.psks /\
        is_publishable tr last_epoch_link.previous_init_secret
      ) \/
      // (5) ... the attacker compromised the node keys stored by a participant
      (
        (exists leaf_index.
          Some? (leaf_at ev.tree leaf_index) /\
          node_key_is_compromised tr (Some?.v (leaf_at ev.tree leaf_index))
        ) /\
        last_epoch_link.commit_ty == FullCommit /\
        all_psks_are_publishable tr ev.psks /\
        is_publishable tr last_epoch_link.previous_init_secret
      ) \/
      // (6) ... the attacker compromised the signature keys of a participant
      (
        (exists leaf_index.
          Some? (leaf_at ev.tree leaf_index) /\
          signature_key_is_compromised_before_i_checked_leaf_node tr me (Some?.v (leaf_at ev.tree leaf_index)) ev.group_context.group_id leaf_index
        ) /\
        last_epoch_link.commit_ty == FullCommit /\
        all_psks_are_publishable tr ev.psks /\
        is_publishable tr last_epoch_link.previous_init_secret
      ) \/
      // (7) ... the attacker compromised the initialization key of a stale participant
      (
        (exists leaf_index.
          Some? (leaf_at ev.tree leaf_index) /\
          (Some?.v (leaf_at ev.tree leaf_index)).data.source == LNS_key_package /\
          corresponding_init_key_is_compromised tr (Some?.v (leaf_at ev.tree leaf_index))
        ) /\
        last_epoch_link.commit_ty == FullCommit /\
        all_psks_are_publishable tr ev.psks /\
        is_publishable tr last_epoch_link.previous_init_secret
      )
    )
    | JustJoined { inviter } -> (
      // (8) the attacker compromised the inviter signature key
      (
        inviter < pow2 ev.tree_height /\
        Some? (leaf_at ev.tree inviter) /\
        inviter_signature_key_is_compromised_before_i_joined tr me (Some?.v (leaf_at ev.tree inviter)) ev
      ) \/
      // (9) the inviter belong to the same group as us
      (
        inviter < pow2 ev.tree_height /\
        Some? (leaf_at ev.tree inviter) /\
        inviter_was_in_same_group_as_me tr (Some?.v (leaf_at ev.tree inviter)) ev
      )
    )
    | JustCreated -> (
      // (10) the attacker compromised the my epoch secret state
      participant_init_key_is_compromised tr me ev.group_context
    )
  ))
let treekem_security_theorem #invs tr me ev =
  let tr_at_event = prefix tr (find_event_triggered_at_timestamp tr me ev) in
  reveal_opaque (`%i_am_in_group_pred) (i_am_in_group_pred tr_at_event me ev);
  allow_inversion how_am_i_in_group;
  match ev.how with
  | ProcessedCommit last_epoch_link -> (
    let commit_secret_label =
      match last_epoch_link.commit_ty with
      | AddOnlyCommit -> public
      | FullCommit -> node_sk_label ev.tree ev.group_context.group_id
    in
    let psk_secret_label = psks_label tr ev.psks in
    let joiners_label = List.Tot.fold_right join (List.Tot.map key_package_to_init_label last_epoch_link.joiners) secret in
    let epoch_secret_label =
      meet
        (join
          (meet
            (get_label tr last_epoch_link.previous_init_secret)
            commit_secret_label
          )
          joiners_label
        )
        psk_secret_label
    in
    let init_secret_state_label = mk_epoch_secret_label InitSecret ev.group_context in
    let init_secret_label = join epoch_secret_label init_secret_state_label in
    reveal_opaque (`%treekem_keyschedule_state_good) (treekem_keyschedule_state_good);
    reveal_opaque (`%treekem_keyschedule_state_label_good) (treekem_keyschedule_state_label_good);
    assert(is_corrupt tr init_secret_label);
    assert(
      (
        is_publishable tr (last_epoch_link.previous_init_secret) /\
        is_corrupt tr commit_secret_label /\
        is_corrupt tr psk_secret_label
      ) \/ (
        is_corrupt tr joiners_label /\
        is_corrupt tr psk_secret_label
      ) \/ (
        is_corrupt tr init_secret_state_label
      )
    );
    FStar.Classical.move_requires (psk_secret_label_corrupt_implies_all_psks_are_publishable tr) ev.psks;
    introduce
      is_corrupt tr joiners_label ==>
      exists joiner.
        List.Tot.memP joiner last_epoch_link.joiners /\ (
          joiners_init_key_is_compromised tr joiner \/
          joiners_signature_key_is_compromised_before_i_checked_it tr me joiner
        )
    with _. (
      for_allP_eq (i_have_verified_key_package tr_at_event me) last_epoch_link.joiners;
      is_corrupt_joiners_label_implies_exists tr last_epoch_link.joiners;
      FStar.Classical.forall_intro (FStar.Classical.move_requires (is_corrupt_key_package_to_init_label_implies tr me))
    );
    introduce
      (last_epoch_link.commit_ty == FullCommit /\ is_corrupt tr commit_secret_label) ==>
        exists leaf_index.
          Some? (leaf_at ev.tree leaf_index) /\ (
            node_key_is_compromised tr (Some?.v (leaf_at ev.tree leaf_index)) \/
            signature_key_is_compromised_before_i_checked_leaf_node tr me (Some?.v (leaf_at ev.tree leaf_index)) ev.group_context.group_id leaf_index \/ (
              (Some?.v (leaf_at ev.tree leaf_index)).data.source == LNS_key_package /\
              corresponding_init_key_is_compromised tr (Some?.v (leaf_at ev.tree leaf_index))
            )
          )
    with _. (
      is_corrupt_commit_secret_implies_exists_leaf tr ev.tree ev.group_context.group_id;
      FStar.Classical.forall_intro (FStar.Classical.move_requires (leaf_at_i_have_verified_every_leaf_node tr_at_event me ev.tree ev.group_context.group_id));
      FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 (is_corrupt_leaf_label_implies tr me ev.group_context.group_id))
    );
    introduce is_corrupt tr (mk_epoch_secret_label InitSecret ev.group_context) ==> init_key_is_compromised tr ev.group_context ev.tree with _. (
      mk_group_secret_label_eq (mk_principal_epoch_secret_label InitSecret) ev.group_context ev.tree;
      FStar.Classical.forall_intro (FStar.Classical.move_requires (leaf_at_i_have_verified_every_leaf_node tr_at_event me ev.tree ev.group_context.group_id));
      mk_tree_secret_label_is_corrupt tr (mk_principal_epoch_secret_label InitSecret) ev.group_context ev.tree
    )
  )
  | JustJoined { inviter } -> (
    let Some inviter_leaf_node = leaf_at ev.tree inviter in
    let Some inviter_id = credential_to_principal inviter_leaf_node.data.credential in
    introduce forall (inviter_ev:i_am_in_group). (event_triggered tr inviter_id inviter_ev /\ ev.group_context == inviter_ev.group_context) ==> (ev.tree_height == inviter_ev.tree_height /\ ev.tree == inviter_ev.tree) with (
      introduce _ ==> _ with _. (
        let tr_at_inviter_event = prefix tr (find_event_triggered_at_timestamp tr inviter_id inviter_ev) in
        reveal_opaque (`%i_am_in_group_pred) (i_am_in_group_pred tr_at_inviter_event inviter_id inviter_ev);
        let (b1, b2) = MLS.TreeSync.TreeHash.Proofs.tree_hash_inj ev.tree inviter_ev.tree in
        FStar.Classical.move_requires_2 hash_injective b1 b2
      )
    )
  )
  | JustCreated -> (
    let init_secret_state_label = mk_epoch_secret_label InitSecret ev.group_context in
    reveal_opaque (`%treekem_keyschedule_state_good) (treekem_keyschedule_state_good);
    reveal_opaque (`%treekem_keyschedule_state_label_good_aux) (treekem_keyschedule_state_label_good_aux);
    assert(is_corrupt tr init_secret_state_label);
    mk_group_secret_label_eq (mk_principal_epoch_secret_label InitSecret) ev.group_context ev.tree
  )
#pop-options
