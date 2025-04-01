module MLS.TreeKEM.Symbolic.Traceful.ProcessCommit.Proof

open Comparse
open DY.Core
open DY.Lib
open MLS.Crypto
open MLS.Tree
open MLS.Symbolic
open MLS.NetworkTypes
open MLS.TreeDEM.NetworkTypes
open MLS.TreeKEM.NetworkTypes
open MLS.TreeKEM.API.Types
open MLS.TreeKEM.API
open MLS.Bootstrap.NetworkTypes
open MLS.TreeSync.NetworkTypes
open MLS.TreeSync.API.Types
open MLS.TreeSync.API.LeafAt
open MLS.TreeSync.Symbolic.API
open MLS.TreeSync.Symbolic.AuthService.CredentialInterpretation
open MLS.TreeSync.Symbolic.State.SignatureKey
open MLS.TreeSync.Symbolic.AuthService
open MLS.TreeSync.Symbolic.Event.LeafNodeHasBeenVerified
open MLS.TreeSync.Symbolic.Event.LeafNodeHasBeenVerified.Invariant
open MLS.Bootstrap.Symbolic.State.KeyPackageStore
open MLS.Bootstrap.Symbolic.KeyPackage
open MLS.Bootstrap.Symbolic.Welcome
open MLS.TreeKEM.Symbolic.State.EpochSecrets
open MLS.TreeKEM.Symbolic.State.NodeKey
open MLS.TreeKEM.Symbolic.State.ProposalCache
open MLS.TreeKEM.Symbolic.State.UpdateCache
open MLS.TreeKEM.Symbolic.State.OnePSKStore
open MLS.TreeKEM.Symbolic.State.PSKStore
open MLS.TreeKEM.Symbolic.State.API
open MLS.TreeKEM.Symbolic.ConfirmationTag
open MLS.TreeKEM.Symbolic.PSK
open MLS.TreeKEM.Symbolic.Tree.Labels
open MLS.TreeKEM.Symbolic.Tree.Operations
open MLS.TreeKEM.Symbolic.EpochEvent
open MLS.TreeKEM.Symbolic.KeySchedule
open MLS.TreeKEM.Symbolic.API.KeySchedule
open MLS.TreeSync.TreeHash.Proofs { tree_has_hash }
open MLS.TreeKEM.Symbolic.Traceful.AllInvariants
open MLS.TreeKEM.Symbolic.Traceful.ProcessCommit

#set-options "--fuel 0 --ifuel 0 --z3cliopt 'smt.qi.eager_threshold=100'"

val _process_group_context_extensions_proposal_proof:
  {|protocol_invariants|} ->
  me:principal ->
  st:treesync_treekem_state -> proposal:proposal_nt bytes{P_group_context_extensions? proposal} ->
  tr:trace ->
  Lemma
  (requires
    is_well_formed_prefix (ps_proposal_nt) (is_publishable tr) proposal /\
    treesync_treekem_state_invariant tr me st /\
    trace_invariant tr /\
    has_treesync_and_treekem_invariants
  )
  (ensures (
    let opt_st_out, tr_out = _process_group_context_extensions_proposal st proposal tr in
    trace_invariant tr_out /\ (
      match opt_st_out with
      | None -> True
      | Some st_out -> (
        st_out.treekem.keyschedule_state == st.treekem.keyschedule_state /\
        st_out.group_context == ({ st.group_context with extensions = st_out.group_context.extensions } <: group_context_nt bytes) /\
        treesync_treekem_state_invariant tr_out me st_out
      )
    )
  ))
let _process_group_context_extensions_proposal_proof #invs me st proposal tr =
  reveal_opaque (`%_process_group_context_extensions_proposal) (_process_group_context_extensions_proposal st proposal tr);
  reveal_opaque (`%treesync_treekem_state_invariant) (treesync_treekem_state_invariant tr me st);
  reveal_opaque (`%treesync_treekem_state_invariant_aux) (treesync_treekem_state_invariant_aux tr me st.group_context st.treesync st.treekem.tree_state);
  let P_group_context_extensions {extensions} = proposal in
  let new_group_context = { st.group_context with extensions } in
  let st_out: treesync_treekem_state = { st with group_context = new_group_context } in
  reveal_opaque (`%treesync_treekem_state_invariant) (treesync_treekem_state_invariant tr me st_out);
  reveal_opaque (`%treesync_treekem_state_invariant_aux) (treesync_treekem_state_invariant_aux tr me new_group_context st.treesync st.treekem.tree_state)

val joiner_is_in_tree:
  #group_id:mls_bytes bytes ->
  treesync_state bytes tkt dy_as_token group_id -> (key_package_nt bytes tkt & nat) ->
  prop
let joiner_is_in_tree #group_id st (joiner, leaf_ind) =
  leaf_ind < pow2 st.levels /\
  leaf_at st.tree leaf_ind == Some joiner.tbs.leaf_node

val joiners_are_in_tree:
  #group_id:mls_bytes bytes ->
  treesync_state bytes tkt dy_as_token group_id -> list (key_package_nt bytes tkt & nat) ->
  prop
let joiners_are_in_tree #group_id st joiners =
  for_allP (joiner_is_in_tree st) joiners

val i_am_not_a_joiner:
  nat -> list nat ->
  prop
let i_am_not_a_joiner leaf_index joiner_indices =
  ~(List.Tot.memP leaf_index joiner_indices)

#push-options "--z3rlimit 25"
val _process_add_proposal_aux_proof:
  {|protocol_invariants|} ->
  me:principal -> auth_service_sid:state_id ->
  st:treesync_treekem_state -> proposal:proposal_nt bytes{P_add? proposal} ->
  tr:trace ->
  Lemma
  (requires
    is_well_formed_prefix (ps_proposal_nt) (is_publishable tr) proposal /\
    treesync_treekem_state_invariant tr me st /\
    trace_invariant tr /\
    has_treesync_and_treekem_invariants
  )
  (ensures (
    let opt_res, tr_out = _process_add_proposal_aux me auth_service_sid st proposal tr in
    trace_invariant tr_out /\ (
      match opt_res with
      | None -> True
      | Some (joiner, joiner_index, st_out) -> (
        st_out.treekem.keyschedule_state == st.treekem.keyschedule_state /\
        st_out.group_context == st.group_context /\
        tree_add_only_rel st.treesync.tree st_out.treesync.tree /\
        treesync_treekem_state_invariant tr_out me st_out /\
        joiner == (P_add?._0 proposal).key_package /\
        i_have_verified_key_package tr_out me joiner /\
        st_out.leaf_index = st.leaf_index /\
        st.leaf_index <> joiner_index /\
        leaf_at_nat st.treesync.tree joiner_index == None /\
        (forall (li:nat). leaf_at_nat st_out.treesync.tree li == (
          if li = joiner_index then Some joiner.tbs.leaf_node
          else leaf_at_nat st.treesync.tree li
        ))
      )
    )
  ))
let _process_add_proposal_aux_proof #invs me auth_service_sid st proposal tr =
  reveal_opaque (`%_process_add_proposal_aux) (_process_add_proposal_aux me auth_service_sid st proposal tr);
  reveal_opaque (`%treesync_treekem_state_invariant) (treesync_treekem_state_invariant tr me st);
  reveal_opaque (`%treesync_treekem_state_invariant_aux) (treesync_treekem_state_invariant_aux tr me st.group_context st.treesync st.treekem.tree_state);
  let tr0 = tr in
  let P_add {key_package} = proposal in
  let leaf_node = key_package.tbs.leaf_node in
  if not (
    let tbs: bytes = (ps_prefix_to_ps_whole (ps_key_package_tbs_nt _)).serialize key_package.tbs in
    verify_with_label leaf_node.data.signature_key "KeyPackageTBS" tbs key_package.signature
  ) then ()
  else (
    let opt_add_pend, tr = extract_result (MLS.TreeSync.API.prepare_add st.treesync leaf_node) tr in
    match opt_add_pend with
    | None -> ()
    | Some add_pend -> (
      get_token_for_proof me auth_service_sid add_pend.as_input tr;
      let opt_token, tr = get_token_for me auth_service_sid add_pend.as_input tr in
      match opt_token with
      | None -> ()
      | Some token -> (
        let opt_treesync_res, tr = extract_result (MLS.TreeSync.API.finalize_add add_pend token) tr in
        match opt_treesync_res with
        | None -> ()
        | Some (treesync, add_index) -> (
          assert(is_well_formed _ (is_publishable tr0) key_package);
          trigger_event_trace_invariant key_package_has_been_verified_pred me ({ key_package } <: key_package_has_been_verified) tr;
          let (), tr = trigger_event me ({ key_package } <: key_package_has_been_verified) tr in
          assert(is_well_formed _ (is_publishable tr0) leaf_node);
          log_leaf_node_verification_event_proof tr me leaf_node token st.group_context.group_id add_index;
          let (), tr = log_leaf_node_verification_event me leaf_node st.group_context.group_id add_index tr in
          let treekem_leaf_node: MLS.TreeKEM.Types.treekem_leaf bytes = ({public_key = key_package.tbs.leaf_node.data.content;}) in
          let (treekem, _) = MLS.TreeKEM.API.add st.treekem treekem_leaf_node in
          let st_out = ({ st with treesync; treekem } <: treesync_treekem_state) in
          reveal_opaque (`%treesync_treekem_state_invariant) (treesync_treekem_state_invariant tr me st_out);
          reveal_opaque (`%treesync_treekem_state_invariant_aux) (treesync_treekem_state_invariant_aux tr me st_out.group_context st_out.treesync st_out.treekem.tree_state);
          reveal_opaque (`%MLS.TreeKEM.API.add) (MLS.TreeKEM.API.add st.treekem treekem_leaf_node);
          MLS.TreeSyncTreeKEMBinder.Proofs.add_state_rel add_pend token st.treekem.tree_state treekem_leaf_node;
          MLS.TreeSync.API.finalize_add_valid #_ #_ #_ #(dy_asp tr0) add_pend token;
          MLS.TreeSync.Symbolic.API.IsWellFormedInvariant.is_well_formed_finalize_add (is_publishable tr0) add_pend token;
          MLS.TreeKEM.Symbolic.API.Tree.add_proof tr0 me st.treekem.tree_state treekem_leaf_node;
          assert(i_am_in_tree_at me st.treesync.tree st.leaf_index);
          leaf_at_finalize_add add_pend token st.leaf_index;
          tree_add_only_rel_finalize_add add_pend token;
          introduce forall (li:nat). leaf_at_nat st_out.treesync.tree li == (if li = add_index then Some key_package.tbs.leaf_node else leaf_at_nat st.treesync.tree li) with (
            leaf_at_finalize_add add_pend token li
          );
          i_have_verified_every_leaf_node_finalize_add tr me add_pend token
        )
      )
    )
  )
#pop-options

#push-options "--fuel 1 --ifuel 1"
val joiners_are_in_tree_ind:
  st_old:treesync_treekem_state -> st_new:treesync_treekem_state ->
  joiners:list (key_package_nt bytes tkt & nat) ->
  joiner:key_package_nt bytes tkt -> joiner_index:nat ->
  Lemma
  (requires
    joiners_are_in_tree st_old.treesync joiners /\
    leaf_at_nat st_old.treesync.tree joiner_index == None /\
    (forall (li:nat). leaf_at_nat st_new.treesync.tree li == (
      if li = joiner_index then Some joiner.tbs.leaf_node
      else leaf_at_nat st_old.treesync.tree li
    ))
  )
  (ensures
    joiners_are_in_tree st_new.treesync ((joiner,joiner_index)::joiners)
  )
let joiners_are_in_tree_ind st_old st_new joiners joiner joiner_index =
  for_allP_eq (joiner_is_in_tree st_old.treesync) joiners;
  for_allP_eq (joiner_is_in_tree st_new.treesync) ((joiner,joiner_index)::joiners)
#pop-options

#push-options "--fuel 1 --ifuel 1 --z3rlimit 25"
val _process_add_proposal_proof:
  {|protocol_invariants|} ->
  me:principal -> auth_service_sid:state_id ->
  l_st:(list (key_package_nt bytes tkt & nat) & treesync_treekem_state) -> proposal:proposal_nt bytes{P_add? proposal} ->
  tr:trace ->
  Lemma
  (requires
    is_well_formed_prefix (ps_proposal_nt) (is_publishable tr) proposal /\
    treesync_treekem_state_invariant tr me (snd l_st) /\
    i_have_verified_every_key_package tr me (List.Tot.map fst (fst l_st)) /\
    joiners_are_in_tree (snd l_st).treesync (fst l_st) /\
    i_am_not_a_joiner (snd l_st).leaf_index (List.Tot.map snd (fst l_st)) /\
    trace_invariant tr /\
    has_treesync_and_treekem_invariants
  )
  (ensures (
    let opt_l_st_out, tr_out = _process_add_proposal me auth_service_sid l_st proposal tr in
    trace_invariant tr_out /\ (
      match opt_l_st_out with
      | None -> True
      | Some l_st_out -> (
        (snd l_st_out).treekem.keyschedule_state == (snd l_st).treekem.keyschedule_state /\
        (snd l_st_out).group_context == (snd l_st).group_context /\
        tree_add_only_rel (snd l_st).treesync.tree (snd l_st_out).treesync.tree /\
        treesync_treekem_state_invariant tr_out me (snd l_st_out) /\
        List.Tot.map fst (fst l_st_out) == (P_add?._0 proposal).key_package::(List.Tot.map fst (fst l_st)) /\
        i_have_verified_every_key_package tr_out me (List.Tot.map fst (fst l_st_out)) /\
        joiners_are_in_tree (snd l_st_out).treesync (fst l_st_out) /\
        i_am_not_a_joiner (snd l_st_out).leaf_index (List.Tot.map snd (fst l_st_out))
      )
    )
  ))
let _process_add_proposal_proof #invs me auth_service_sid (joiners, st) proposal tr =
  reveal_opaque (`%_process_add_proposal) (_process_add_proposal me auth_service_sid (joiners, st) proposal tr);
  _process_add_proposal_aux_proof me auth_service_sid st proposal tr;
  let opt_res, tr = _process_add_proposal_aux me auth_service_sid st proposal tr in
  match opt_res with
  | None -> ()
  | Some (key_package, add_index, st_out) -> (
    let joiners_out = (key_package, add_index)::joiners in
    assert((List.Tot.map fst joiners_out) == key_package::(List.Tot.map fst joiners));
    joiners_are_in_tree_ind st st_out joiners key_package add_index
  )
#pop-options

val proposal_and_sender_is_publishable:
  {|crypto_invariants|} ->
  trace -> proposal_and_sender ->
  prop
let proposal_and_sender_is_publishable #cinvs tr p =
  is_well_formed_prefix (ps_proposal_nt) (is_publishable tr) p.proposal

val proposal_and_sender_is_publishable_later:
  {|crypto_invariants|} ->
  tr1:trace -> tr2:trace -> p:proposal_and_sender ->
  Lemma
  (requires proposal_and_sender_is_publishable tr1 p /\ tr1 <$ tr2)
  (ensures proposal_and_sender_is_publishable tr2 p)
let proposal_and_sender_is_publishable_later #cinvs tr1 tr2 p =
  is_well_formed_prefix_weaken (ps_proposal_nt) (is_publishable tr1) (is_publishable tr2) p.proposal

#push-options "--z3rlimit 25"
val _process_update_proposal_proof:
  {|protocol_invariants|} ->
  me:principal -> auth_service_sid:state_id -> update_cache_sid:state_id ->
  st:treesync_treekem_state -> proposal:proposal_and_sender{P_update? proposal.proposal} ->
  tr:trace ->
  Lemma
  (requires
    proposal_and_sender_is_publishable tr proposal /\
    treesync_treekem_state_invariant tr me st /\
    trace_invariant tr /\
    has_treesync_and_treekem_invariants
  )
  (ensures (
    let opt_st_out, tr_out = _process_update_proposal me auth_service_sid update_cache_sid st proposal tr in
    trace_invariant tr_out /\ (
      match opt_st_out with
      | None -> True
      | Some st_out -> (
        st_out.treekem.keyschedule_state == st.treekem.keyschedule_state /\
        st_out.group_context == st.group_context /\
        treesync_treekem_state_invariant tr_out me st_out
      )
    )
  ))
let _process_update_proposal_proof #invs me auth_service_sid update_cache_sid st proposal tr =
  reveal_opaque (`%_process_update_proposal) (_process_update_proposal me auth_service_sid update_cache_sid st proposal tr);
  reveal_opaque (`%treesync_treekem_state_invariant) (treesync_treekem_state_invariant tr me st);
  reveal_opaque (`%treesync_treekem_state_invariant_aux) (treesync_treekem_state_invariant_aux tr me st.group_context st.treesync st.treekem.tree_state);
  let tr0 = tr in
  let P_update {leaf_node} = proposal.proposal in
  if not (proposal.sender < pow2 st.treesync.levels) then ()
  else (
    let sender_index:MLS.Tree.leaf_index st.treesync.levels 0 = proposal.sender in
    let opt_pend_update, tr = extract_result (MLS.TreeSync.API.prepare_update st.treesync leaf_node sender_index) tr in
    match opt_pend_update with
    | None -> ()
    | Some pend_update -> (
      get_token_for_proof me auth_service_sid pend_update.as_input tr;
      let opt_token, tr = get_token_for me auth_service_sid pend_update.as_input tr in
      match opt_token with
      | None -> ()
      | Some token -> (
        let treesync = MLS.TreeSync.API.finalize_update pend_update token in
        assert(is_well_formed (leaf_node_nt bytes tkt) (is_publishable tr0) leaf_node);
        log_leaf_node_verification_event_proof tr me leaf_node token st.group_context.group_id sender_index;
        let (), tr = log_leaf_node_verification_event me leaf_node st.group_context.group_id sender_index tr in
        if not (st.treesync.levels = st.treekem.tree_state.levels) then ()
        else (
          if sender_index = st.leaf_index then (
            find_update_leaf_sk_proof me update_cache_sid leaf_node tr;
            let opt_leaf_sk_sid, tr = find_update_leaf_sk me update_cache_sid leaf_node tr in
            match opt_leaf_sk_sid with
            | None -> ()
            | Some leaf_sk_sid -> (
              get_leaf_node_key_proof tr me leaf_sk_sid;
              let opt_leaf_sk, tr = get_leaf_node_key me leaf_sk_sid tr in
              match opt_leaf_sk with
              | None -> ()
              | Some leaf_sk -> (
                let treekem_leaf_node: MLS.TreeKEM.Types.treekem_leaf  bytes = ({public_key = leaf_node.data.content}) in
                let treekem = MLS.TreeKEM.API.update_myself st.treekem ({public_key = leaf_node.data.content}) leaf_sk in
                let st_out = { st with treesync; treekem } <: treesync_treekem_state in

                reveal_opaque (`%treesync_treekem_state_invariant) (treesync_treekem_state_invariant tr me st_out);
                reveal_opaque (`%treesync_treekem_state_invariant_aux) (treesync_treekem_state_invariant_aux tr me st_out.group_context st_out.treesync st_out.treekem.tree_state);
                reveal_opaque (`%MLS.TreeKEM.API.update_myself) (MLS.TreeKEM.API.update_myself st.treekem ({public_key = leaf_node.data.content}) leaf_sk);
                MLS.TreeSyncTreeKEMBinder.Proofs.update_myself_state_rel pend_update token st.treekem.tree_state treekem_leaf_node leaf_sk;
                MLS.TreeSync.API.finalize_update_valid #_ #_ #_ #(dy_asp tr0) pend_update token;
                MLS.TreeSync.Symbolic.API.IsWellFormedInvariant.is_well_formed_finalize_update (is_publishable tr0) pend_update token;
                MLS.TreeKEM.Symbolic.API.Tree.update_myself_proof tr me st.treekem.tree_state treekem_leaf_node leaf_sk;
                leaf_at_finalize_update pend_update token st.leaf_index;
                i_have_verified_every_leaf_node_finalize_update tr me pend_update token
              )
            )
          ) else (
            let treekem_leaf_node: MLS.TreeKEM.Types.treekem_leaf  bytes = ({public_key = leaf_node.data.content}) in
            let treekem = MLS.TreeKEM.API.update_other st.treekem treekem_leaf_node sender_index in
            let st_out = { st with treesync; treekem } <: treesync_treekem_state in

            reveal_opaque (`%treesync_treekem_state_invariant) (treesync_treekem_state_invariant tr me st_out);
            reveal_opaque (`%treesync_treekem_state_invariant_aux) (treesync_treekem_state_invariant_aux tr me st_out.group_context st_out.treesync st_out.treekem.tree_state);
            reveal_opaque (`%MLS.TreeKEM.API.update_other) (MLS.TreeKEM.API.update_other st.treekem treekem_leaf_node sender_index);
            MLS.TreeSyncTreeKEMBinder.Proofs.update_other_state_rel pend_update token st.treekem.tree_state treekem_leaf_node sender_index;
            MLS.TreeSync.API.finalize_update_valid #_ #_ #_ #(dy_asp tr0) pend_update token;
            MLS.TreeSync.Symbolic.API.IsWellFormedInvariant.is_well_formed_finalize_update (is_publishable tr0) pend_update token;
            MLS.TreeKEM.Symbolic.API.Tree.update_other_proof tr0 me st.treekem.tree_state treekem_leaf_node sender_index;
            leaf_at_finalize_update pend_update token st.leaf_index;
            i_have_verified_every_leaf_node_finalize_update tr me pend_update token
          )
        )
      )
    )
  )
#pop-options

val _process_remove_proposal_proof:
  {|protocol_invariants|} ->
  me:principal ->
  st:treesync_treekem_state -> proposal:proposal_nt bytes{P_remove? proposal} ->
  tr:trace ->
  Lemma
  (requires
    is_well_formed_prefix (ps_proposal_nt) (is_publishable tr) proposal /\
    treesync_treekem_state_invariant tr me st /\
    trace_invariant tr /\
    has_treesync_and_treekem_invariants
  )
  (ensures (
    let opt_st_out, tr_out = _process_remove_proposal st proposal tr in
    trace_invariant tr_out /\ (
      match opt_st_out with
      | None -> True
      | Some st_out -> (
        st_out.treekem.keyschedule_state == st.treekem.keyschedule_state /\
        st_out.group_context == st.group_context /\
        treesync_treekem_state_invariant tr_out me st_out
      )
    )
  ))
let _process_remove_proposal_proof #invs me st proposal tr =
  reveal_opaque (`%_process_remove_proposal) (_process_remove_proposal st proposal tr);
  let tr0 = tr in
  reveal_opaque (`%treesync_treekem_state_invariant) (treesync_treekem_state_invariant tr me st);
  reveal_opaque (`%treesync_treekem_state_invariant_aux) (treesync_treekem_state_invariant_aux tr me st.group_context st.treesync st.treekem.tree_state);
  let P_remove {removed} = proposal in
  if not ((removed < pow2 st.treesync.levels) && (removed <> st.leaf_index) && (st.treesync.levels = st.treekem.tree_state.levels)) then ()
  else (
    let opt_remove_pend, tr = extract_result (MLS.TreeSync.API.prepare_remove st.treesync removed) tr in
    match opt_remove_pend with
    | None -> ()
    | Some remove_pend -> (
      let treesync = MLS.TreeSync.API.finalize_remove remove_pend in
      let treekem = MLS.TreeKEM.API.remove st.treekem removed in
      let st_out: treesync_treekem_state = { st with treesync; treekem } in
      reveal_opaque (`%treesync_treekem_state_invariant) (treesync_treekem_state_invariant tr me st_out);
      reveal_opaque (`%treesync_treekem_state_invariant_aux) (treesync_treekem_state_invariant_aux tr me st_out.group_context st_out.treesync st_out.treekem.tree_state);
      MLS.TreeSyncTreeKEMBinder.Proofs.remove_state_rel remove_pend st.treekem.tree_state removed;
      MLS.TreeSync.API.finalize_remove_valid #_ #_ #_ #(dy_asp tr0) remove_pend;
      MLS.TreeSync.Symbolic.API.IsWellFormedInvariant.is_well_formed_finalize_remove (is_publishable tr0) remove_pend;
      MLS.TreeKEM.Symbolic.API.Tree.remove_proof tr0 me st.treekem.tree_state removed;
      reveal_opaque (`%MLS.TreeKEM.API.remove) (MLS.TreeKEM.API.remove st.treekem removed);
      leaf_at_finalize_remove remove_pend st.leaf_index;
      i_have_verified_every_leaf_node_finalize_remove tr me remove_pend
    )
  )

#push-options "--fuel 1 --ifuel 1"
val add_proposals_to_key_packages:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  list (proposal:proposal_nt bytes{P_add? proposal}) ->
  list (key_package_nt bytes tkt)
let rec add_proposals_to_key_packages #bytes #bl l =
  match l with
  | [] -> []
  | (P_add {key_package})::t -> key_package::add_proposals_to_key_packages t
#pop-options

#push-options "--fuel 1 --ifuel 1"
val _sort_proposals_proof:
  {|crypto_invariants|} ->
  tr:trace -> proposals:list proposal_and_sender ->
  Lemma
  (requires
    for_allP (is_well_formed_prefix ps_proposal_nt (is_publishable tr)) (List.Tot.map Mkproposal_and_sender?.proposal proposals)
  )
  (ensures (
    ((proposals_to_key_packages (List.Tot.Base.map Mkproposal_and_sender?.proposal proposals)) == (add_proposals_to_key_packages (_sort_proposals proposals).adds)) /\
    for_allP (is_well_formed_prefix ps_proposal_nt (is_publishable tr)) (_sort_proposals proposals).group_context_extensions /\
    for_allP (is_well_formed_prefix ps_proposal_nt (is_publishable tr)) (_sort_proposals proposals).adds /\
    for_allP (proposal_and_sender_is_publishable tr) ((_sort_proposals proposals).updates) /\
    for_allP (is_well_formed_prefix ps_proposal_nt (is_publishable tr)) (_sort_proposals proposals).removes /\
    psk_ids_good tr (_sort_proposals proposals).psks /\
    for_allP (is_well_formed_prefix ps_proposal_nt (is_publishable tr)) (_sort_proposals proposals).other
  ))
let rec _sort_proposals_proof #cinvs tr proposals =
  reveal_opaque (`%_sort_proposals) (_sort_proposals proposals);
  match proposals with
  | [] ->
    assert_norm(add_proposals_to_key_packages #bytes [] == [])
  | h::t -> (
    match h.proposal with
    | P_add { key_package } -> (
      assert_norm(add_proposals_to_key_packages #bytes ((P_add { key_package })::((_sort_proposals t).adds)) == key_package::(add_proposals_to_key_packages (_sort_proposals t).adds));
      _sort_proposals_proof tr t
    )
    | _ -> _sort_proposals_proof tr t
  )
#pop-options

#push-options "--ifuel 1 --fuel 1"
val fold_leftM_proof:
  {|protocol_invariants|} ->
  #a:Type -> #b:Type ->
  f:(a -> b -> traceful (option a)) ->
  l_invariant:(trace -> b -> prop) ->
  l_invariant_later:(
    tr1:trace -> tr2:trace -> x:b ->
    Lemma
    (requires l_invariant tr1 x /\ tr1 <$ tr2)
    (ensures l_invariant tr2 x)
  ) ->
  acc_invariant:(trace -> a -> list b -> prop) ->
  f_proof:(
    acc:a -> h:b -> t:list b ->
    tr:trace ->
    Lemma
    (requires
      l_invariant tr h /\
      acc_invariant tr acc (h::t) /\
      trace_invariant tr
    )
    (ensures (
      let opt_res, tr_out = f acc h tr in
      trace_invariant tr_out /\ (
        match opt_res with
        | None -> True
        | Some res -> acc_invariant tr_out res t
      )
    ))
  ) ->
  acc:a -> l:list b -> tr0:trace -> tr:trace ->
  Lemma
  (requires
    for_allP (l_invariant tr0) l /\
    acc_invariant tr acc l /\
    tr0 <$ tr /\
    trace_invariant tr
  )
  (ensures (
    let opt_res, tr_out = fold_leftM f acc l tr in
    trace_invariant tr_out /\ (
      match opt_res with
      | None -> True
      | Some res -> acc_invariant tr_out res []
    )
  ))
  (decreases l)
let rec fold_leftM_proof #invs #a #b f l_invariant l_invariant_later acc_invariant f_proof acc l tr0 tr =
  reveal_opaque (`%fold_leftM) (fold_leftM f acc l tr);
  match l with
  | [] -> ()
  | h::t -> (
    l_invariant_later tr0 tr h;
    f_proof acc h t tr;
    let opt_new_acc, tr = f acc h tr in
    match opt_new_acc with
    | None -> ()
    | Some new_acc -> (
      for_allP_eq (l_invariant tr0) t;
      FStar.Classical.forall_intro (FStar.Classical.move_requires (l_invariant_later tr0 tr));
      for_allP_eq (l_invariant tr) t;
      fold_leftM_proof f l_invariant l_invariant_later acc_invariant f_proof new_acc t tr0 tr
    )
  )
#pop-options

#push-options "--fuel 1 --ifuel 1"
val _rev_acc_lemma:
  proposal:proposal_nt bytes{P_add? proposal} ->
  proposals:list (proposal:proposal_nt bytes{P_add? proposal}) ->
  joiners:list (key_package_nt bytes tkt) ->
  Lemma (
    List.Tot.rev_acc (add_proposals_to_key_packages (proposal::proposals)) joiners
    ==
    List.Tot.rev_acc (add_proposals_to_key_packages proposals) (((P_add?._0 proposal).key_package)::joiners)
  )
let _rev_acc_lemma proposal proposals joiners =
  let P_add { key_package } = proposal in
  assert_norm((add_proposals_to_key_packages ((P_add { key_package })::proposals)) == (key_package::(add_proposals_to_key_packages proposals)));
  ()
#pop-options

#push-options "--fuel 1 --ifuel 1"
val _process_proposals_proof_rev_acc_lemma:
  tr:trace -> me:principal ->
  joiners:list (key_package_nt bytes tkt & nat) ->
  joiners_acc:list (key_package_nt bytes tkt & nat) ->
  Lemma
  (requires
    i_have_verified_every_key_package tr me (List.Tot.map fst joiners) /\
    i_have_verified_every_key_package tr me (List.Tot.map fst joiners_acc)
  )
  (ensures
    (List.Tot.map fst (List.Tot.rev_acc joiners joiners_acc)) == List.Tot.rev_acc (List.Tot.map fst joiners) (List.Tot.map fst joiners_acc) /\
    i_have_verified_every_key_package tr me (List.Tot.map fst (List.Tot.rev_acc joiners joiners_acc))
  )
let rec _process_proposals_proof_rev_acc_lemma tr me joiners joiners_acc =
  match joiners with
  | [] -> ()
  | h::t -> (
    _process_proposals_proof_rev_acc_lemma tr me t (h::joiners_acc)
  )
#pop-options

#push-options "--fuel 1 --ifuel 1"
val _process_proposals_proof_rev_lemma:
  tr:trace -> me:principal ->
  joiners:list (key_package_nt bytes tkt & nat) ->
  Lemma
  (requires i_have_verified_every_key_package tr me (List.Tot.map fst joiners))
  (ensures
    (List.Tot.map fst (List.Tot.rev joiners)) == List.Tot.rev (List.Tot.map fst joiners) /\
    i_have_verified_every_key_package tr me (List.Tot.map fst (List.Tot.rev joiners))
  )
let _process_proposals_proof_rev_lemma tr me joiners =
  _process_proposals_proof_rev_acc_lemma tr me joiners []
#pop-options

#push-options "--fuel 1 --ifuel 1"
val joiners_are_in_tree_rev_acc:
  #group_id:mls_bytes bytes ->
  st:treesync_state bytes tkt dy_as_token group_id -> l1:list (key_package_nt bytes tkt & nat) -> l2:list (key_package_nt bytes tkt & nat) ->
  Lemma
  (requires
    joiners_are_in_tree st l1 /\
    joiners_are_in_tree st l2
  )
  (ensures joiners_are_in_tree st (List.Tot.rev_acc l1 l2))
let rec joiners_are_in_tree_rev_acc #group_id st l1 l2 =
  match l1 with
  | [] -> ()
  | h::t -> joiners_are_in_tree_rev_acc st t (h::l2)
#pop-options

#push-options "--fuel 1 --ifuel 1"
val i_am_not_a_joiner_rev_acc:
  my_leaf_index:nat -> l1:list (key_package_nt bytes tkt & nat) -> l2:list (key_package_nt bytes tkt & nat) ->
  Lemma
  (requires
    i_am_not_a_joiner my_leaf_index (List.Tot.map snd l1) /\
    i_am_not_a_joiner my_leaf_index (List.Tot.map snd l2)
  )
  (ensures i_am_not_a_joiner my_leaf_index (List.Tot.map snd (List.Tot.rev_acc l1 l2)))
let rec i_am_not_a_joiner_rev_acc my_leaf_index l1 l2 =
  match l1 with
  | [] -> ()
  | h::t -> i_am_not_a_joiner_rev_acc my_leaf_index t (h::l2)
#pop-options

val _process_proposals_proof:
  {|protocol_invariants|} ->
  tr:trace ->
  me:principal -> auth_service_sid:state_id -> update_cache_sid:state_id ->
  st:treesync_treekem_state -> proposals:list proposal_and_sender ->
  Lemma
  (requires
    for_allP (is_well_formed_prefix ps_proposal_nt (is_publishable tr)) (List.Tot.map Mkproposal_and_sender?.proposal proposals) /\
    treesync_treekem_state_invariant tr me st /\
    trace_invariant tr /\
    has_treesync_and_treekem_invariants
  )
  (ensures (
    let (opt_res, tr_out) = _process_proposals me auth_service_sid update_cache_sid st proposals tr in
    trace_invariant tr_out /\ (
      match opt_res with
      | None -> True
      | Some (new_st, joiners, psk_ids, other_proposals, can_add_only) -> (
        treesync_treekem_state_invariant tr_out me new_st /\
        (proposals_to_key_packages (List.Tot.Base.map Mkproposal_and_sender?.proposal proposals)) == List.Tot.map fst joiners /\
        i_have_verified_every_key_package tr_out me (List.Tot.map fst joiners) /\
        new_st.treekem.keyschedule_state == st.treekem.keyschedule_state /\
        joiners_are_in_tree new_st.treesync joiners /\
        i_am_not_a_joiner new_st.leaf_index (List.Tot.map snd joiners) /\
        psk_ids_good tr_out psk_ids /\
        new_st.group_context == ({ st.group_context with extensions = new_st.group_context.extensions } <: group_context_nt bytes) /\
        (can_add_only ==> tree_add_only_rel st.treesync.tree new_st.treesync.tree)
      )
    )
 ))
let _process_proposals_proof #invs tr me auth_service_sid update_cache_sid st proposals =
  reveal_opaque (`%_process_proposals) (_process_proposals me auth_service_sid update_cache_sid st proposals tr);
  let tr0 = tr in
  let st0 = st in
  _sort_proposals_proof tr proposals;
  let sorted_proposals = _sort_proposals proposals in
  let acc_inv (#a:Type) (tr:trace) (st:treesync_treekem_state) (_:list a): prop =
    treesync_treekem_state_invariant tr me st /\
    st.treekem.keyschedule_state == st0.treekem.keyschedule_state /\
    st.group_context == ({ st0.group_context with extensions = st.group_context.extensions } <: group_context_nt bytes)
  in
  let proposal_inv (tr:trace): proposal_nt bytes -> prop = is_well_formed_prefix ps_proposal_nt (is_publishable tr) in
  let proposal_inv_later (tr1:trace) (tr2:trace) (proposal:proposal_nt bytes): Lemma (requires proposal_inv tr1 proposal /\ tr1 <$ tr2) (ensures proposal_inv tr2 proposal) =
    is_well_formed_prefix_weaken ps_proposal_nt (is_publishable tr1) (is_publishable tr2) proposal
  in
  fold_leftM_proof _process_group_context_extensions_proposal proposal_inv proposal_inv_later acc_inv (fun st proposal _ tr -> _process_group_context_extensions_proposal_proof me st proposal tr) st sorted_proposals.group_context_extensions tr0 tr;
  let opt_st, tr = fold_leftM _process_group_context_extensions_proposal st sorted_proposals.group_context_extensions tr in
  match opt_st with
  | None -> ()
  | Some st -> (
    fold_leftM_proof (_process_update_proposal me auth_service_sid update_cache_sid) proposal_and_sender_is_publishable proposal_and_sender_is_publishable_later acc_inv (fun st proposal _ tr -> _process_update_proposal_proof me auth_service_sid update_cache_sid st proposal tr) st sorted_proposals.updates tr0 tr;
    let opt_st, tr = fold_leftM (_process_update_proposal me auth_service_sid update_cache_sid) st sorted_proposals.updates tr in
    match opt_st with
    | None -> ()
    | Some st -> (
      fold_leftM_proof _process_remove_proposal proposal_inv proposal_inv_later acc_inv (fun st proposal _ tr -> _process_remove_proposal_proof me st proposal tr) st sorted_proposals.removes tr0 tr;
      let opt_st, tr = fold_leftM _process_remove_proposal st sorted_proposals.removes tr in
      match opt_st with
      | None -> ()
      | Some st -> (
        let st_before_add = st in
        assert(treesync_treekem_state_invariant tr me st);
        let add_acc_inv (tr:trace) (l_st:(list (key_package_nt bytes tkt & nat) & treesync_treekem_state)) (proposals:list (proposal:proposal_nt bytes{P_add? proposal})): prop =
          let (joiners, st) = l_st in
          treesync_treekem_state_invariant tr me st /\
          st.treekem.keyschedule_state == st0.treekem.keyschedule_state /\
          st.group_context == ({ st0.group_context with extensions = st.group_context.extensions } <: group_context_nt bytes) /\
          i_have_verified_every_key_package tr me (List.Tot.map fst joiners) /\
          List.Tot.rev (add_proposals_to_key_packages sorted_proposals.adds) == List.Tot.rev_acc (add_proposals_to_key_packages proposals) (List.Tot.map fst joiners) /\
          joiners_are_in_tree st.treesync joiners /\
          i_am_not_a_joiner st.leaf_index (List.Tot.map snd joiners) /\
          tree_add_only_rel st_before_add.treesync.tree st.treesync.tree
        in
        assert(
          i_have_verified_every_key_package tr me (List.Tot.map fst ([] <: list (key_package_nt bytes tkt & nat))) /\
          joiners_are_in_tree st.treesync ([] <: list (key_package_nt bytes tkt & nat)) /\
          i_am_not_a_joiner st.leaf_index (List.Tot.map snd ([] <: list (key_package_nt bytes tkt & nat)))
        ) by (let open FStar.Tactics in set_fuel 1; set_ifuel 1);
        assert(List.Tot.rev (add_proposals_to_key_packages sorted_proposals.adds) == List.Tot.rev_acc (add_proposals_to_key_packages sorted_proposals.adds) (List.Tot.map fst ([] <: list (key_package_nt bytes tkt & nat))))
          by (let open FStar.Tactics in set_fuel 1; set_ifuel 1);
        tree_add_only_rel_reflexive st_before_add.treesync.tree;
        fold_leftM_proof (_process_add_proposal me auth_service_sid) proposal_inv proposal_inv_later add_acc_inv (fun (joiners, st) proposal proposals tr ->
          _process_add_proposal_proof me auth_service_sid (joiners, st) proposal tr;
          _rev_acc_lemma proposal proposals (List.Tot.map fst joiners);
          let opt_res, _ = _process_add_proposal me auth_service_sid (joiners, st) proposal tr in
          match opt_res with
          | None -> ()
          | Some (_, new_st) -> (
            tree_add_only_rel_transitive st_before_add.treesync.tree st.treesync.tree new_st.treesync.tree
          )
        ) ([], st) sorted_proposals.adds tr0 tr;
        let opt_res, tr = fold_leftM (_process_add_proposal me auth_service_sid) ([], st) sorted_proposals.adds tr in
        match opt_res with
        | None -> ()
        | Some (adds, st) -> (
          let can_add_only = proposals <> [] && sorted_proposals.group_context_extensions = [] && sorted_proposals.updates = [] && sorted_proposals.removes = [] in
          let pf (): squash (can_add_only ==> st0 == st_before_add) = (
            reveal_opaque (`%fold_leftM) (fold_leftM _process_group_context_extensions_proposal);
            reveal_opaque (`%fold_leftM) (fold_leftM (_process_update_proposal me auth_service_sid update_cache_sid));
            reveal_opaque (`%fold_leftM) (fold_leftM _process_remove_proposal);
            assert(can_add_only ==> st0 == st_before_add) by (let open FStar.Tactics in set_fuel 1; set_ifuel 1)
          ) in pf ();
          assert_norm(List.Tot.rev_acc (add_proposals_to_key_packages []) (List.Tot.map fst adds) == (List.Tot.map fst adds));
          List.Tot.Properties.rev_involutive (add_proposals_to_key_packages sorted_proposals.adds);
          _process_proposals_proof_rev_lemma tr me adds;
          assert(
            joiners_are_in_tree st.treesync ([] <: list (key_package_nt bytes tkt & nat)) /\
            i_am_not_a_joiner st.leaf_index (List.Tot.map snd ([] <: list (key_package_nt bytes tkt & nat)))
          ) by (let open FStar.Tactics in set_fuel 1; set_ifuel 1);
          joiners_are_in_tree_rev_acc st.treesync adds [];
          i_am_not_a_joiner_rev_acc st.leaf_index adds []
        )
      )
    )
  )

#push-options "--z3rlimit 50"
val _make_provisional_group_context_proof:
  {|crypto_invariants|} ->
  #group_id:mls_bytes bytes ->
  tr:trace ->
  group_context:group_context_nt bytes -> treesync_st:treesync_state bytes tkt dy_as_token group_id ->
  Lemma
  (requires
    is_well_formed _ (is_publishable tr) group_context /\
    is_well_formed _ (is_publishable tr) (treesync_st.tree <: MLS.TreeSync.Types.treesync _ _ _ _)
  )
  (ensures (
    let opt_provisional_group_context, tr_out = _make_provisional_group_context group_context treesync_st tr in
    tr_out == tr /\ (
      match opt_provisional_group_context with
      | None -> True
      | Some provisional_group_context -> (
        is_well_formed _ (is_publishable tr_out) provisional_group_context /\
        tree_has_hash treesync_st.tree provisional_group_context.tree_hash /\
        provisional_group_context.group_id == group_context.group_id /\
        provisional_group_context.epoch == group_context.epoch+1
      )
    )
 ))
let _make_provisional_group_context_proof #cinvs #group_id tr group_context treesync_st =
  reveal_opaque (`%_make_provisional_group_context) (_make_provisional_group_context group_context treesync_st tr);
  let opt_provisional_group_context, tr_out = _make_provisional_group_context group_context treesync_st tr in
  match opt_provisional_group_context with
  | None -> ()
  | Some provisional_group_context -> (
    let MLS.Result.Success tree_hash = MLS.TreeSync.API.compute_tree_hash treesync_st in
    MLS.TreeSync.Symbolic.IsWellFormed.pre_tree_hash (is_publishable tr) treesync_st.tree
  )
#pop-options

val treesync_treekem_state_invariant_aux_change_group_context:
  {|crypto_invariants|} ->
  #leaf_index:nat ->
  tr:trace -> me:principal ->
  group_context1:group_context_nt bytes -> group_context2:group_context_nt bytes ->
  treesync:treesync_state bytes tkt dy_as_token group_context1.group_id ->
  treekem:MLS.TreeKEM.API.Tree.Types.treekem_tree_state bytes leaf_index ->
  Lemma
  (requires
    treesync_treekem_state_invariant_aux tr me group_context1 treesync treekem /\
    group_context1.group_id == group_context2.group_id /\
    is_well_formed _ (is_publishable tr) group_context2
  )
  (ensures treesync_treekem_state_invariant_aux tr me group_context2 treesync treekem)
let treesync_treekem_state_invariant_aux_change_group_context #cinvs #leaf_index tr me group_context1 group_context2 treesync treekem =
  reveal_opaque (`%treesync_treekem_state_invariant_aux) (treesync_treekem_state_invariant_aux #cinvs #leaf_index)

#push-options "--z3rlimit 100"
#restart-solver
val _process_update_path_proof:
  {|protocol_invariants|} ->
  tr:trace ->
  me:principal -> auth_service_sid:state_id ->
  st:treesync_treekem_state ->
  sender_index:nat -> path:update_path_nt bytes ->
  joiners:list (key_package_nt bytes tkt & nat) ->
  Lemma
  (requires
    treesync_treekem_state_invariant tr me st /\
    is_well_formed_prefix ps_update_path_nt (is_publishable tr) path /\
    trace_invariant tr /\
    has_treesync_and_treekem_invariants
  )
  (ensures (
    let (opt_res, tr_out) = _process_update_path me auth_service_sid st sender_index path joiners tr in
    trace_invariant tr_out /\ (
      match opt_res with
      | None -> True
      | Some (new_treesync, pending_treekem, provisional_group_context) -> (
        provisional_group_context.group_id == st.group_context.group_id /\
        provisional_group_context.epoch == st.group_context.epoch+1 /\
        treesync_treekem_state_invariant_aux tr_out me provisional_group_context new_treesync pending_treekem.next_tree_state /\
        tree_has_hash new_treesync.tree provisional_group_context.tree_hash /\
        Some? (pending_treekem.opt_commit_secret) /\
        bytes_invariant tr_out (Some?.v (pending_treekem.opt_commit_secret)) /\
        (node_sk_label new_treesync.tree provisional_group_context.group_id) `can_flow tr_out` (get_label tr_out (Some?.v (pending_treekem.opt_commit_secret)))
      )
    )
 ))
let _process_update_path_proof #invs tr me auth_service_sid st sender_index path joiners =
  reveal_opaque (`%_process_update_path) (_process_update_path me auth_service_sid st sender_index path joiners tr);
  let tr0 = tr in
  if not (sender_index < pow2 st.treesync.levels && sender_index <> st.leaf_index) then ()
  else (
    MLS.NetworkBinder.Properties.Proofs.path_filtering_ok_uncompress_update_path sender_index st.treesync.tree path;
    let opt_uncompressed_path, tr = extract_result (MLS.NetworkBinder.uncompress_update_path sender_index st.treesync.tree path) tr in
    match opt_uncompressed_path with
    | None -> ()
    | Some uncompressed_path -> (
      let treesync_path = MLS.NetworkBinder.update_path_to_treesync uncompressed_path in
      let opt_commit_pend, tr = extract_result (MLS.TreeSync.API.prepare_commit st.treesync treesync_path) tr in
      match opt_commit_pend with
      | None -> ()
      | Some commit_pend -> (
        get_token_for_proof me auth_service_sid commit_pend.as_input tr;
        let opt_token, tr = get_token_for me auth_service_sid commit_pend.as_input tr in
        match opt_token with
        | None -> ()
        | Some token -> (
          let opt_treesync, tr = extract_result (MLS.TreeSync.API.finalize_commit commit_pend token) tr in
          match opt_treesync with
          | None -> ()
          | Some treesync -> (
            FStar.Pure.BreakVC.break_vc ();
            let pf (): squash (
              bytes_invariant tr st.group_context.group_id /\
              is_well_formed (leaf_node_nt bytes tkt) (bytes_invariant tr) (get_path_leaf treesync_path)
            ) = (
              reveal_opaque (`%treesync_treekem_state_invariant) (treesync_treekem_state_invariant tr me st);
              reveal_opaque (`%treesync_treekem_state_invariant_aux) (treesync_treekem_state_invariant_aux tr me st.group_context st.treesync st.treekem.tree_state);
              is_well_formed_prefix_weaken ps_update_path_nt (is_publishable tr0) (bytes_invariant tr) path;
              MLS.NetworkBinder.Properties.Proofs.uncompress_update_path_pre (bytes_invariant tr) sender_index st.treesync.tree path;
              MLS.NetworkBinder.Properties.Proofs.update_path_to_treesync_pre (bytes_invariant tr) uncompressed_path;
              MLS.NetworkBinder.Properties.Proofs.get_path_leaf_pre (ps_leaf_node_nt tkt) (ps_option ps_hpke_public_key_nt) (bytes_invariant tr) treesync_path
            ) in pf ();
            log_leaf_node_verification_event_proof tr me (get_path_leaf treesync_path) token st.group_context.group_id sender_index;
            let (), tr = log_leaf_node_verification_event me (get_path_leaf treesync_path) st.group_context.group_id sender_index tr in
            FStar.Pure.BreakVC.break_vc ();
            let pf (): squash (is_well_formed _ (is_publishable tr) st.group_context) = (
              reveal_opaque (`%treesync_treekem_state_invariant) (treesync_treekem_state_invariant tr me st);
              reveal_opaque (`%treesync_treekem_state_invariant_aux) (treesync_treekem_state_invariant_aux tr me st.group_context st.treesync st.treekem.tree_state)
              ) in pf ();
            let pf (): squash (is_well_formed _ (is_publishable tr) (treesync.tree <: MLS.TreeSync.Types.treesync _ _ _ _)) = (
              reveal_opaque (`%treesync_treekem_state_invariant) (treesync_treekem_state_invariant tr me st);
              reveal_opaque (`%treesync_treekem_state_invariant_aux) (treesync_treekem_state_invariant_aux tr me st.group_context st.treesync st.treekem.tree_state);
              MLS.NetworkBinder.Properties.Proofs.uncompress_update_path_pre (is_publishable tr0) sender_index st.treesync.tree path;
              MLS.NetworkBinder.Properties.Proofs.update_path_to_treesync_pre (is_publishable tr0) uncompressed_path;
              MLS.TreeSync.Symbolic.API.IsWellFormedInvariant.is_well_formed_finalize_commit (is_publishable tr) commit_pend token
              ) in pf ();
            _make_provisional_group_context_proof tr st.group_context treesync;
            FStar.Pure.BreakVC.break_vc ();
            let opt_provisional_group_context, tr = _make_provisional_group_context st.group_context treesync tr in
            match opt_provisional_group_context with
            | None -> ()
            | Some provisional_group_context -> (
              let treekem_path = MLS.NetworkBinder.update_path_to_treekem uncompressed_path in
              if not ((st.treesync.levels = st.treekem.tree_state.levels) && (MLS.NetworkBinder.Properties.path_filtering_ok st.treekem.tree_state.tree treekem_path) && (not (List.Tot.mem st.leaf_index (List.Tot.map snd joiners)))) then ()
              else (
                reveal_opaque (`%MLS.TreeKEM.API.prepare_process_full_commit) (MLS.TreeKEM.API.prepare_process_full_commit st.treekem);
                let excluded_leaves = List.Tot.map snd joiners in
                let pf (): squash (
                  MLS.TreeSyncTreeKEMBinder.Properties.treesync_treekem_state_rel st.treesync st.treekem.tree_state /\
                  MLS.TreeKEM.Symbolic.API.Tree.treekem_tree_state_invariant tr me st.treekem.tree_state
                ) = (
                  reveal_opaque (`%treesync_treekem_state_invariant) (treesync_treekem_state_invariant tr0 me st);
                  reveal_opaque (`%treesync_treekem_state_invariant_aux) (treesync_treekem_state_invariant_aux tr0 me st.group_context st.treesync st.treekem.tree_state)
                ) in pf ();
                FStar.Pure.BreakVC.break_vc ();
                let pf (): squash (
                  treesync_state_valid (dy_asp tr) treesync /\
                  i_have_verified_every_leaf_node tr me treesync.tree st.group_context.group_id /\
                  is_well_formed (MLS.TreeSync.Types.treesync bytes tkt _ _) (bytes_invariant tr) treesync.tree /\
                  pathkem_good_weak (MLS.NetworkBinder.update_path_to_treekem uncompressed_path) tr
                ) = (
                  reveal_opaque (`%treesync_treekem_state_invariant) (treesync_treekem_state_invariant tr0 me st);
                  reveal_opaque (`%treesync_treekem_state_invariant_aux) (treesync_treekem_state_invariant_aux tr0 me st.group_context st.treesync st.treekem.tree_state);
                  MLS.TreeSync.API.finalize_commit_valid commit_pend (token <: (dy_asp tr).token_t);
                  is_well_formed_prefix_weaken ps_update_path_nt (is_publishable tr0) (bytes_invariant tr) path;
                  MLS.NetworkBinder.Properties.Proofs.uncompress_update_path_pre (bytes_invariant tr) sender_index st.treesync.tree path;
                  MLS.NetworkBinder.Properties.Proofs.update_path_to_treekem_pre (bytes_invariant tr) uncompressed_path;
                  i_have_verified_every_leaf_node_finalize_commit tr me commit_pend token
                ) in pf ();
                MLS.TreeKEM.Symbolic.API.Tree.process_commit_proof tr me st.treesync st.treekem.tree_state uncompressed_path excluded_leaves provisional_group_context commit_pend token;
                let opt_pending_treekem, tr = extract_result (
                  let open MLS.TreeKEM.API in
                  MLS.TreeKEM.API.prepare_process_full_commit st.treekem ({
                    commit_leaf_ind = _;
                    path = treekem_path;
                    excluded_leaves = (List.Tot.map snd joiners);
                    provisional_group_context;
                  })
                ) tr in
                match opt_pending_treekem with
                | None -> ()
                | Some pending_treekem -> (
                  let pf (): squash (treesync_treekem_state_invariant_aux tr me provisional_group_context treesync pending_treekem.next_tree_state) = (
                    reveal_opaque (`%treesync_treekem_state_invariant) (treesync_treekem_state_invariant tr0 me st);
                    reveal_opaque (`%treesync_treekem_state_invariant_aux) (treesync_treekem_state_invariant_aux tr0 me st.group_context st.treesync st.treekem.tree_state);
                    reveal_opaque (`%treesync_treekem_state_invariant_aux) (treesync_treekem_state_invariant_aux tr me provisional_group_context treesync pending_treekem.next_tree_state);
                    MLS.TreeSyncTreeKEMBinder.Proofs.pathsync_pathkem_rel_update_path_to_treeX uncompressed_path;
                    MLS.TreeSyncTreeKEMBinder.Proofs.process_commit_state_rel commit_pend token st.treekem.tree_state treekem_path excluded_leaves provisional_group_context;
                    leaf_at_finalize_commit commit_pend token st.leaf_index
                  ) in pf ()
                )
              )
            )
          )
        )
      )
    )
  )
#pop-options

val _process_no_update_path_proof:
  {|protocol_invariants|} ->
  tr:trace -> me:principal ->
  st:treesync_treekem_state ->
  Lemma
  (requires
    treesync_treekem_state_invariant tr me st /\
    trace_invariant tr /\
    has_treesync_and_treekem_invariants
  )
  (ensures (
    let (opt_res, tr_out) = _process_no_update_path st tr in
    trace_invariant tr_out /\ (
      match opt_res with
      | None -> True
      | Some (new_treesync, pending_treekem, provisional_group_context) -> (
        provisional_group_context.group_id == st.group_context.group_id /\
        provisional_group_context.epoch == st.group_context.epoch+1 /\
        new_treesync == st.treesync /\
        treesync_treekem_state_invariant_aux tr_out me provisional_group_context new_treesync pending_treekem.next_tree_state /\
        tree_has_hash new_treesync.tree provisional_group_context.tree_hash /\
        None? (pending_treekem.opt_commit_secret)
      )
    )
  ))
let _process_no_update_path_proof #invs tr me st =
  reveal_opaque (`%_process_no_update_path) (_process_no_update_path st tr);
  reveal_opaque (`%treesync_treekem_state_invariant) (treesync_treekem_state_invariant tr me st);
  reveal_opaque (`%treesync_treekem_state_invariant_aux) (treesync_treekem_state_invariant_aux tr me st.group_context st.treesync st.treekem.tree_state);
  _make_provisional_group_context_proof tr st.group_context st.treesync;
  let opt_provisional_group_context, tr = _make_provisional_group_context st.group_context st.treesync tr in
  match opt_provisional_group_context with
  | None -> ()
  | Some provisional_group_context -> (
    let opt_pending_treekem, tr = extract_result (MLS.TreeKEM.API.prepare_process_add_only_commit st.treekem) tr in
    match opt_pending_treekem with
    | None -> ()
    | Some pending_treekem -> (
      reveal_opaque (`%MLS.TreeKEM.API.prepare_process_add_only_commit) (MLS.TreeKEM.API.prepare_process_add_only_commit st.treekem);
      treesync_treekem_state_invariant_aux_change_group_context tr me st.group_context provisional_group_context st.treesync st.treekem.tree_state
    )
  )

val compute_expected_commit_secret_label:
  #l:nat ->
  bool ->
  MLS.TreeSync.Types.treesync bytes tkt l 0 -> mls_bytes bytes ->
  label
let compute_expected_commit_secret_label #cusgs is_full_commit tree group_id =
  if is_full_commit then
    node_sk_label tree group_id
  else
    public

#push-options "--z3rlimit 25"
val _process_opt_update_path_proof_aux:
  {|protocol_invariants|} ->
  tr:trace ->
  me:principal -> auth_service_sid:state_id ->
  st:treesync_treekem_state ->
  sender_index:nat -> opt_path:option (update_path_nt bytes) ->
  joiners:list (key_package_nt bytes tkt & nat) ->
  Lemma
  (requires
    is_well_formed_prefix (ps_option ps_update_path_nt) (is_publishable tr) opt_path /\
    treesync_treekem_state_invariant tr me st /\
    trace_invariant tr /\
    has_treesync_and_treekem_invariants
  )
  (ensures (
    let (opt_res, tr_out) = (
      match opt_path with
      | Some path -> _process_update_path me auth_service_sid st sender_index path joiners
      | None -> _process_no_update_path st
    ) tr in
    trace_invariant tr_out /\ (
      match opt_res with
      | None -> True
      | Some (new_treesync, pending_treekem, provisional_group_context) -> (
        (provisional_group_context <: group_context_nt bytes).group_id == st.group_context.group_id /\
        (provisional_group_context <: group_context_nt bytes).epoch == st.group_context.epoch+1 /\
        treesync_treekem_state_invariant_aux tr_out me provisional_group_context new_treesync pending_treekem.next_tree_state /\
        tree_has_hash (new_treesync <: treesync_state _ _ _ _).tree provisional_group_context.tree_hash /\
        compute_expected_commit_secret_label (Some? opt_path) (new_treesync <: treesync_state _ _ _ _).tree (provisional_group_context <: group_context_nt bytes).group_id `can_flow tr_out` compute_commit_secret_label tr_out pending_treekem.opt_commit_secret /\ (
          match pending_treekem.opt_commit_secret with
          | None -> (
            opt_path == None /\
            new_treesync == st.treesync
          )
          | Some commit_secret -> (
            Some? opt_path /\
            bytes_invariant tr_out commit_secret
          )
        )
      )
    )
  ))
let _process_opt_update_path_proof_aux #invs tr me auth_service_sid st sender_index opt_path joiners =
  match opt_path with
  | Some path -> _process_update_path_proof tr me auth_service_sid st sender_index path joiners
  | None -> _process_no_update_path_proof tr me st
#pop-options

#push-options "--z3rlimit 50"
#restart-solver
val _process_opt_update_path_proof:
  {|protocol_invariants|} ->
  tr:trace ->
  me:principal -> auth_service_sid:state_id ->
  st:treesync_treekem_state ->
  sender_index:nat -> opt_path:option (update_path_nt bytes) ->
  joiners:list (key_package_nt bytes tkt & nat) ->
  new_confirmed_transcript_hash:mls_bytes bytes ->
  psks:list (pre_shared_key_id_nt bytes & bytes) ->
  Lemma
  (requires
    is_well_formed_prefix (ps_option ps_update_path_nt) (is_publishable tr) opt_path /\
    bytes_invariant tr st.treekem.keyschedule_state.init_secret /\
    is_publishable tr new_confirmed_transcript_hash /\
    tx_hash_contains_joiners new_confirmed_transcript_hash (List.Tot.map fst joiners) /\
    treesync_treekem_state_invariant tr me st /\
    psks_bytes_invariant tr psks /\
    trace_invariant tr /\
    has_treesync_and_treekem_invariants
  )
  (ensures (
    let (opt_new_st, tr_out) = _process_opt_update_path me auth_service_sid st sender_index opt_path joiners new_confirmed_transcript_hash psks tr in
    trace_invariant tr_out /\ (
      match opt_new_st with
      | None -> True
      | Some new_st -> (
        new_st.group_context.group_id == st.group_context.group_id /\
        new_st.group_context.epoch == st.group_context.epoch+1 /\
        treesync_treekem_state_invariant tr_out me new_st /\
        treesync_treekem_state_coarse_invariant tr_out me new_st /\
        treekem_keyschedule_state_label_good tr_out st.treekem.keyschedule_state.init_secret (compute_expected_commit_secret_label (Some? opt_path) new_st.treesync.tree new_st.group_context.group_id) (List.Tot.map fst joiners) psks new_st.treekem.keyschedule_state new_st.group_context /\
        (opt_path == None ==> new_st.treesync == st.treesync)
      )
    )
  ))
let _process_opt_update_path_proof #invs tr me auth_service_sid st sender_index opt_path joiners new_confirmed_transcript_hash psks =
  reveal_opaque (`%_process_opt_update_path) (_process_opt_update_path me auth_service_sid st sender_index opt_path joiners new_confirmed_transcript_hash psks tr);
  let tr0 = tr in
  _process_opt_update_path_proof_aux tr me auth_service_sid st sender_index opt_path joiners;
  let (opt_res, tr) =
    match opt_path with
    | Some path -> _process_update_path me auth_service_sid st sender_index path joiners tr
    | None -> _process_no_update_path st tr
  in
  assert(trace_invariant tr);
  match opt_res with
  | None -> ()
  | Some (new_treesync, pending_treekem, provisional_group_context) -> (
    assert(
      (provisional_group_context <: group_context_nt bytes).group_id == st.group_context.group_id /\
      treesync_treekem_state_invariant_aux tr me provisional_group_context new_treesync (pending_treekem <: MLS.TreeKEM.API.pending_process_commit _).next_tree_state /\
      tree_has_hash (new_treesync <: treesync_state _ _ _ _).tree provisional_group_context.tree_hash
    );
    let new_group_context: group_context_nt bytes = {
      provisional_group_context with
      group_id = st.group_context.group_id;
      confirmed_transcript_hash = new_confirmed_transcript_hash;
    } in

    match MLS.TreeKEM.API.finalize_process_commit pending_treekem psks new_group_context with
    | MLS.Result.Success (new_treekem, encryption_secret) -> (

      reveal_opaque (`%MLS.TreeKEM.API.finalize_process_commit) (MLS.TreeKEM.API.finalize_process_commit pending_treekem psks new_group_context);

      let pf (): squash (is_publishable tr st.group_context.group_id) = (
        reveal_opaque (`%treesync_treekem_state_invariant) (treesync_treekem_state_invariant tr0 me st);
        reveal_opaque (`%treesync_treekem_state_invariant_aux) (treesync_treekem_state_invariant_aux tr0 me st.group_context st.treesync st.treekem.tree_state)
      ) in pf ();
      let pf (): squash (is_well_formed _ (is_publishable tr) new_group_context) = (
        reveal_opaque (`%treesync_treekem_state_invariant_aux) (treesync_treekem_state_invariant_aux #_ #st.leaf_index tr me provisional_group_context)
      ) in pf();
      wf_weaken_lemma _ (is_publishable tr) (bytes_invariant tr) new_group_context;

      MLS.TreeKEM.Symbolic.API.KeySchedule.commit_proof tr st.treekem.keyschedule_state ((pending_treekem <: MLS.TreeKEM.API.pending_process_commit _).opt_commit_secret) psks new_group_context (List.Tot.map fst joiners);
      assert(Some? opt_path <==> Some? (((pending_treekem <: MLS.TreeKEM.API.pending_process_commit _).opt_commit_secret)));
      let commit_secret_label1 = (compute_commit_secret_label tr pending_treekem.opt_commit_secret) in
      let commit_secret_label2 = (compute_expected_commit_secret_label (Some? opt_path) (new_treesync <: treesync_state _ _ _ _).tree (provisional_group_context <: group_context_nt bytes).group_id) in
      assert(treekem_keyschedule_state_label_good tr st.treekem.keyschedule_state.init_secret commit_secret_label1 (List.Tot.map fst joiners) psks new_treekem.keyschedule_state new_group_context);
      treekem_keyschedule_state_label_good_can_flow tr st.treekem.keyschedule_state.init_secret commit_secret_label1 commit_secret_label2 (List.Tot.map fst joiners) psks new_treekem.keyschedule_state new_group_context;
      assert((new_treekem <: treekem_state _ _).tree_state == (pending_treekem <: MLS.TreeKEM.API.pending_process_commit _).next_tree_state);
      assert( treesync_treekem_state_invariant_aux tr me provisional_group_context new_treesync new_treekem.tree_state);
      treesync_treekem_state_invariant_aux_change_group_context tr me provisional_group_context new_group_context new_treesync new_treekem.tree_state;
      let new_st = ({
        leaf_index = st.leaf_index;
        group_context = new_group_context;
        my_signature_key_sid = st.my_signature_key_sid;
        treesync = new_treesync;
        treekem = new_treekem;
      } <: treesync_treekem_state)
      in

      reveal_opaque (`%treesync_treekem_state_invariant) (treesync_treekem_state_invariant tr me new_st);
      assert(treesync_treekem_state_invariant tr me new_st);
      reveal_opaque (`%treesync_treekem_state_coarse_invariant) (treesync_treekem_state_coarse_invariant tr me new_st);
      treekem_keyschedule_state_auth_exists_strong_to_weak new_st.treekem.keyschedule_state;
      assert(treesync_treekem_state_coarse_invariant tr me new_st);
      let tr_out = tr in
      assert(trace_invariant tr);
      assert((Some new_st, tr_out) == _process_opt_update_path me auth_service_sid st sender_index opt_path joiners new_confirmed_transcript_hash psks tr0);
      ()
    )
    | _ -> ()
  )
#pop-options

#push-options "--z3rlimit 25"
val _compute_confirmed_transcript_hash_proof:
  {|crypto_invariants|} ->
  tr:trace ->
  st:treesync_treekem_state -> tx_hash_input:confirmed_transcript_hash_input_nt bytes{tx_hash_input.content.content.content_type == CT_commit} ->
  Lemma
  (requires
    is_publishable tr st.treekem.keyschedule_state.epoch_keys.confirmation_tag /\
    is_publishable tr st.group_context.confirmed_transcript_hash /\
    is_well_formed _ (is_publishable tr) tx_hash_input
  )
  (ensures (
    match _compute_confirmed_transcript_hash st tx_hash_input with
    | MLS.Result.Success confirmed_transcript_hash ->
      commit_is_last_in_tx_hash tx_hash_input.content.content.content (confirmed_transcript_hash <: bytes) /\
      is_publishable tr confirmed_transcript_hash
    | _ -> True
  ))
let _compute_confirmed_transcript_hash_proof #cinvs tr st tx_hash_input =
  reveal_opaque (`%_compute_confirmed_transcript_hash) (_compute_confirmed_transcript_hash st tx_hash_input);
  let open MLS.Result in
  match _compute_confirmed_transcript_hash st tx_hash_input with
  | Success confirmed_transcript_hash -> (
    assert(is_well_formed _ (is_publishable tr) ({ confirmation_tag = st.treekem.keyschedule_state.epoch_keys.confirmation_tag; } <: interim_transcript_hash_input_nt bytes));
    let Success interim_transcript_hash = MLS.TreeDEM.Message.Transcript.compute_interim_transcript_hash #bytes st.treekem.keyschedule_state.epoch_keys.confirmation_tag st.group_context.confirmed_transcript_hash in
    FStar.Classical.forall_intro (FStar.Classical.move_requires (hash_output_length_lemma #bytes));
    let witness: commit_is_last_in_tx_hash_aux_witness bytes = (tx_hash_input, interim_transcript_hash) in
    assert(commit_is_last_in_tx_hash_aux tx_hash_input.content.content.content confirmed_transcript_hash witness)
  )
  | _ -> ()
#pop-options

#push-options "--z3rlimit 100"
#restart-solver
val _process_commit_proof:
  {|protocol_invariants|} ->
  tr:trace ->
  me:principal -> auth_service_sid:state_id -> proposal_cache_sid:state_id -> update_cache_sid:state_id -> psk_store_sid:state_id ->
  st:treesync_treekem_state ->
  tx_hash_input:confirmed_transcript_hash_input_nt bytes{tx_hash_input.content.content.content_type == CT_commit} ->
  Lemma
  (requires
    is_well_formed _ (is_publishable tr) tx_hash_input /\
    treesync_treekem_state_all_invariants tr me st /\
    trace_invariant tr /\
    has_treesync_and_treekem_invariants
  )
  (ensures (
    let (opt_new_st, tr_out) = _process_commit me auth_service_sid proposal_cache_sid update_cache_sid psk_store_sid st tx_hash_input tr in
    trace_invariant tr_out /\ (
      match opt_new_st with
      | None -> True
      | Some new_st -> (
        treesync_treekem_state_all_invariants tr_out me new_st
      )
    )
  ))
let _process_commit_proof #invs tr me auth_service_sid proposal_cache_sid update_cache_sid psk_store_sid st tx_hash_input =
  reveal_opaque (`%_process_commit) (_process_commit me auth_service_sid proposal_cache_sid update_cache_sid psk_store_sid st tx_hash_input tr);
  let pf (): squash (bytes_invariant tr st.treekem.keyschedule_state.init_secret) = (
    reveal_opaque (`%treesync_treekem_state_coarse_invariant) (treesync_treekem_state_coarse_invariant tr me st);
    reveal_opaque (`%treekem_keyschedule_state_good) (treekem_keyschedule_state_good tr st.treekem.keyschedule_state st.group_context)
  ) in pf();
  let tr0 = tr in
  let original_st = st in
  let framed_commit = tx_hash_input.content in
  let commit: commit_nt bytes = framed_commit.content.content in

  let opt_sender_index =
    match framed_commit.sender with
    | S_member sender_index -> Some sender_index
    | _ -> None
  in
  match opt_sender_index with
  | None -> ()
  | Some sender_index -> (
    let pf (): squash (
      is_publishable tr st.treekem.keyschedule_state.epoch_keys.confirmation_tag /\
      is_publishable tr st.group_context.confirmed_transcript_hash
    ) = (
      reveal_opaque (`%treesync_treekem_state_invariant) (treesync_treekem_state_invariant tr me st);
      reveal_opaque (`%treesync_treekem_state_invariant_aux) (treesync_treekem_state_invariant_aux tr me st.group_context st.treesync st.treekem.tree_state);
      reveal_opaque (`%treesync_treekem_state_coarse_invariant) (treesync_treekem_state_coarse_invariant tr me st);
      reveal_opaque (`%treekem_keyschedule_state_good) (treekem_keyschedule_state_good tr st.treekem.keyschedule_state st.group_context)
    ) in pf();
    _compute_confirmed_transcript_hash_proof tr st tx_hash_input;
    match _compute_confirmed_transcript_hash st tx_hash_input with
    | MLS.Result.Success new_confirmed_transcript_hash -> (
      let proposals_or_refs = commit.proposals in
      retrieve_proposals_proof tr me proposal_cache_sid sender_index proposals_or_refs;
      let opt_proposals, tr = retrieve_proposals me proposal_cache_sid sender_index proposals_or_refs tr in
      match opt_proposals with
      | None -> ()
      | Some proposals -> (
        assert(
          commit_is_last_in_tx_hash commit (new_confirmed_transcript_hash <: bytes) /\
          proposal_or_refs_rel commit.proposals (List.Tot.Base.map Mkproposal_and_sender?.proposal proposals)
        );

        _process_proposals_proof tr me auth_service_sid update_cache_sid st proposals;
        let opt_process_proposals_res, tr = _process_proposals me auth_service_sid update_cache_sid st proposals tr in
        match opt_process_proposals_res with
        | None -> ()
        | Some (st, joiners, psk_ids, other_proposals, can_add_only) -> (
          if not (can_add_only || Some? commit.path) then ()
          else (
            retrieve_psks_proof me psk_store_sid psk_ids tr;
            let opt_psks, tr = retrieve_psks me psk_store_sid psk_ids tr in
            match opt_psks with
            | None -> ()
            | Some psks -> (
              intro_tx_hash_contains_joiners new_confirmed_transcript_hash (List.Tot.map fst joiners) commit (List.Tot.Base.map Mkproposal_and_sender?.proposal proposals);
              assert(is_well_formed _ (is_publishable tr) tx_hash_input);
              _process_opt_update_path_proof tr me auth_service_sid st sender_index commit.path joiners new_confirmed_transcript_hash psks;
              let opt_st, tr = _process_opt_update_path me auth_service_sid st sender_index commit.path joiners new_confirmed_transcript_hash psks tr in
              match opt_st with
              | None -> ()
              | Some st -> (
                // precondition for treekem_keyschedule_state_label_good_later
                let pf (): squash (treekem_keyschedule_state_good tr st.treekem.keyschedule_state st.group_context) = (
                  reveal_opaque (`%treesync_treekem_state_coarse_invariant) (treesync_treekem_state_coarse_invariant tr me st)
                ) in pf();
                let pf (): squash (
                  is_well_formed_prefix ps_pre_shared_key_id_short (is_publishable tr) (PSKID_ResumptionPSK st.group_context.group_id st.group_context.epoch) /\
                  is_knowable_by (psk_label me (PSKID_ResumptionPSK st.group_context.group_id st.group_context.epoch)) tr (get_epoch_keys st.treekem).resumption_psk
                ) = (
                  reveal_opaque (`%treesync_treekem_state_invariant) (treesync_treekem_state_invariant tr me st);
                  reveal_opaque (`%treesync_treekem_state_invariant_aux) (treesync_treekem_state_invariant_aux tr me st.group_context st.treesync st.treekem.tree_state);
                  reveal_opaque (`%treesync_treekem_state_coarse_invariant) (treesync_treekem_state_coarse_invariant tr me st);
                  reveal_opaque (`%treekem_keyschedule_state_label_good) (treekem_keyschedule_state_label_good);
                  reveal_opaque (`%treekem_keyschedule_state_good) (treekem_keyschedule_state_good);
                  intro_i_am_in_group_context me st.group_context st.treesync.tree st.leaf_index;
                  mk_group_secret_label_can_flow_my_label tr me mk_resumption_psk_label st.group_context
                ) in pf ();
                remember_psk_proof me psk_store_sid (PSKID_ResumptionPSK st.group_context.group_id st.group_context.epoch) (get_epoch_keys st.treekem).resumption_psk tr;
                let opt_unit, tr = remember_psk me psk_store_sid (PSKID_ResumptionPSK st.group_context.group_id st.group_context.epoch) (get_epoch_keys st.treekem).resumption_psk tr in
                match opt_unit with
                | None -> ()
                | Some () -> (
                  let ev = {
                    how = ProcessedCommit {
                      previous_init_secret = original_st.treekem.keyschedule_state.init_secret;
                      previous_group_context = original_st.group_context;
                      previous_tree_height = original_st.treesync.levels;
                      previous_tree = original_st.treesync.tree;
                      commit_ty = if Some? (commit.path <: option (update_path_nt bytes)) then FullCommit else AddOnlyCommit;
                      joiners = List.Tot.map fst joiners;
                    };
                    group_context = st.group_context;
                    tree_height = _;
                    tree = st.treesync.tree;
                    psks = psks;
                    epoch_keys = st.treekem.keyschedule_state;
                  } in

                  assert(psks_bytes_invariant tr ev.psks);

                  let pf (): squash (i_have_verified_every_leaf_node tr me st.treesync.tree st.group_context.group_id) = (
                    reveal_opaque (`%treesync_treekem_state_invariant) (treesync_treekem_state_invariant tr me st);
                    reveal_opaque (`%treesync_treekem_state_invariant_aux) (treesync_treekem_state_invariant_aux tr me st.group_context st.treesync st.treekem.tree_state)
                  ) in pf ();
                  assert(trace_invariant tr);
                  reveal_opaque (`%i_am_in_group_pred) (i_am_in_group_pred tr me ev);
                  reveal_opaque (`%treesync_treekem_state_very_coarse_invariant) (treesync_treekem_state_very_coarse_invariant tr0 me original_st);
                  let pf (): squash (
                    MLS.TreeSync.TreeHash.Proofs.tree_has_hash st.treesync.tree st.group_context.tree_hash /\
                    treekem_keyschedule_state_good tr st.treekem.keyschedule_state st.group_context
                  ) = (
                    reveal_opaque (`%treesync_treekem_state_coarse_invariant) (treesync_treekem_state_coarse_invariant tr me st)
                  ) in pf ();
                  assert(None? commit.path <==> commit.path == None) by (let open FStar.Tactics in set_fuel 1; set_ifuel 1); //?
                  assert(i_am_in_group_pred tr me ev);
                  trigger_event_trace_invariant i_am_in_group_pred me ev tr;
                  let (), tr = trigger_event me ev tr in
                  assert(trace_invariant tr);

                  assert((Some st, tr) == _process_commit me auth_service_sid proposal_cache_sid update_cache_sid psk_store_sid original_st tx_hash_input tr0);

                  assert(treesync_treekem_state_invariant tr me st);
                  assert(i_have_previous_epoch_event_with_witness tr me st.group_context st.treekem.keyschedule_state.init_secret st.treesync.tree ev);
                  assert(i_have_previous_epoch_event tr me st.group_context st.treekem.keyschedule_state.init_secret st.treesync.tree);
                  reveal_opaque (`%treesync_treekem_state_very_coarse_invariant) (treesync_treekem_state_very_coarse_invariant tr me st);
                  ()
                )
              )
            )
          )
        )
      )
    )
    | _ -> ()
  )
#pop-options

val process_commit_proof:
  {|protocol_invariants|} ->
  tr:trace ->
  me:principal -> auth_service_sid:state_id -> proposal_cache_sid:state_id -> update_cache_sid:state_id -> psk_store_sid:state_id ->
  group_state_sid:state_id ->
  commit_ts:timestamp ->
  Lemma
  (requires
    trace_invariant tr /\
    has_treesync_and_treekem_invariants
  )
  (ensures (
    let (_, tr_out) = process_commit me auth_service_sid proposal_cache_sid update_cache_sid psk_store_sid group_state_sid commit_ts tr in
    trace_invariant tr_out
  ))
let process_commit_proof #invs tr me auth_service_sid proposal_cache_sid update_cache_sid psk_store_sid group_state_sid commit_ts =
  reveal_opaque (`%process_commit) (process_commit me auth_service_sid proposal_cache_sid update_cache_sid psk_store_sid group_state_sid commit_ts tr);
  get_treesync_treekem_state_proof tr me group_state_sid;
  let opt_st, tr = get_treesync_treekem_state me group_state_sid tr in
  match opt_st with
  | None -> ()
  | Some st -> (
    let opt_commit_bytes, tr = recv_msg commit_ts tr in
    match opt_commit_bytes with
    | None -> ()
    | Some commit_bytes -> (
      parse_wf_lemma (confirmed_transcript_hash_input_nt bytes) (is_publishable tr) commit_bytes;
      match parse (confirmed_transcript_hash_input_nt bytes) commit_bytes with
      | None -> ()
      | Some commit -> (
        if not (commit.content.content.content_type = CT_commit) then ()
        else (
          _process_commit_proof tr me auth_service_sid proposal_cache_sid update_cache_sid psk_store_sid st commit;
          let opt_st, tr = _process_commit me auth_service_sid proposal_cache_sid update_cache_sid psk_store_sid st commit tr in
          match opt_st with
          | None -> ()
          | Some st -> (
            store_treesync_treekem_state_proof tr me st
          )
        )
      )
    )
  )
