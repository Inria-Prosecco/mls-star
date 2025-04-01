module MLS.TreeSync.Symbolic.Event.LeafNodeHasBeenVerified

open Comparse
open DY.Core
open DY.Lib
open MLS.Tree
open MLS.NetworkTypes
open MLS.TreeSync.NetworkTypes
open MLS.TreeSync.Types
open MLS.TreeSync.Operations { leaf_is_valid }
open MLS.TreeSync.Symbolic.AuthService
open MLS.TreeSync.Proofs.ParentHashGuarantees
open MLS.TreeSync.Invariants.UnmergedLeaves
open MLS.TreeSync.Invariants.AuthService
open MLS.TreeSync.Invariants.ValidLeaves
open MLS.Symbolic
open MLS.TreeSync.Symbolic.Parsers

#set-options "--fuel 0 --ifuel 0"

(*** Leaf node verification event ***)

[@@ with_bytes bytes]
type leaf_node_has_been_verified (tkt:treekem_types bytes) = {
  leaf_node: leaf_node_nt bytes tkt;
  group_id: mls_bytes bytes;
  leaf_index: nat;
}

%splice [ps_leaf_node_has_been_verified] (gen_parser (`leaf_node_has_been_verified))

instance event_leaf_node_has_been_verified (tkt:treekem_types bytes): event (leaf_node_has_been_verified tkt) = {
  tag = "MLS.TreeSync.LeafNodeHasBeenVerified";
  format = mk_parseable_serializeable (ps_leaf_node_has_been_verified tkt);
}

val leaf_node_has_been_verified_pred: {|crypto_invariants|} -> #tkt:treekem_types bytes -> event_predicate (leaf_node_has_been_verified tkt)
let leaf_node_has_been_verified_pred #cinvs #tkt =
  fun tr prin {leaf_node; group_id; leaf_index} ->
    // preconditions of `bytes_invariant_verify_with_label`
    bytes_invariant tr group_id /\
    is_well_formed (leaf_node_nt bytes tkt) (bytes_invariant tr) leaf_node /\
    (exists as_token. (dy_asp tr).credential_ok (leaf_node_to_as_input leaf_node) as_token) /\
    // verification succeeded
    leaf_is_valid leaf_node group_id leaf_index

val has_leaf_node_has_been_verified_invariant:
  {|protocol_invariants|} -> tkt:treekem_types bytes ->
  prop
let has_leaf_node_has_been_verified_invariant #invs tkt =
  has_event_pred (leaf_node_has_been_verified_pred #_ #tkt)

val leaf_node_has_been_verified_tag_and_invariant: {|crypto_invariants|} -> treekem_types bytes -> (string & compiled_event_predicate)
let leaf_node_has_been_verified_tag_and_invariant #cinvs tkt =
  ((event_leaf_node_has_been_verified tkt).tag, compile_event_pred (leaf_node_has_been_verified_pred #_ #tkt))

val i_have_verified_leaf_node:
  #tkt:treekem_types bytes ->
  trace -> principal ->
  leaf_node_nt bytes tkt -> mls_bytes bytes -> nat ->
  prop
let i_have_verified_leaf_node #tkt tr me leaf_node group_id leaf_index =
  event_triggered tr me {leaf_node; group_id; leaf_index}

#push-options "--fuel 1 --ifuel 1"
val i_have_verified_every_leaf_node:
  #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l ->
  trace -> principal ->
  treesync bytes tkt l i -> mls_bytes bytes ->
  prop
let rec i_have_verified_every_leaf_node #tkt #l #i tr me t group_id =
  match t with
  | TLeaf None -> True
  | TLeaf (Some ln) ->
    i_have_verified_leaf_node tr me ln group_id i
  | TNode _ left right ->
    i_have_verified_every_leaf_node tr me left group_id /\
    i_have_verified_every_leaf_node tr me right group_id
#pop-options

#push-options "--fuel 1 --ifuel 1"
val leaf_at_i_have_verified_every_leaf_node:
  #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l ->
  tr:trace -> me:principal ->
  t:treesync bytes tkt l i -> group_id:mls_bytes bytes ->
  li:leaf_index l i ->
  Lemma
  (requires i_have_verified_every_leaf_node tr me t group_id)
  (ensures (
    match leaf_at t li with
    | None -> True
    | Some ln -> i_have_verified_leaf_node tr me ln group_id li
  ))
let rec leaf_at_i_have_verified_every_leaf_node #tkt #l #i tr me t group_id li =
  if l = 0 then ()
  else (
    let (child, _) = get_child_sibling t li in
    leaf_at_i_have_verified_every_leaf_node tr me child group_id li
  )
#pop-options

#push-options "--fuel 1 --ifuel 1"
val intro_i_have_verified_every_leaf_node:
  #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l ->
  tr:trace -> me:principal ->
  t:treesync bytes tkt l i -> group_id:mls_bytes bytes ->
  (li:leaf_index l i -> Lemma (
    match leaf_at t li with
    | None -> True
    | Some ln -> i_have_verified_leaf_node tr me ln group_id li
  )) ->
  Lemma (i_have_verified_every_leaf_node tr me t group_id)
let rec intro_i_have_verified_every_leaf_node #tkt #l #i tr me t group_id pf =
  match t with
  | TLeaf x -> (
    pf i
  )
  | TNode _ left right ->
    intro_i_have_verified_every_leaf_node tr me left group_id (fun li -> pf li);
    intro_i_have_verified_every_leaf_node tr me right group_id (fun li -> pf li)
#pop-options

#push-options "--fuel 1 --ifuel 1"
val i_have_verified_every_leaf_node_later:
  #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l ->
  tr1:trace -> tr2:trace -> me:principal ->
  t:treesync bytes tkt l i -> group_id:mls_bytes bytes ->
  Lemma
  (requires
    i_have_verified_every_leaf_node tr1 me t group_id /\
    tr1 <$ tr2
  )
  (ensures i_have_verified_every_leaf_node tr2 me t group_id)
  [SMTPat (i_have_verified_every_leaf_node tr1 me t group_id); SMTPat (tr1 <$ tr2)]
let rec i_have_verified_every_leaf_node_later #tkt #l #i tr1 tr2 me t group_id =
  match t with
  | TLeaf _ -> ()
  | TNode _ left right -> (
    i_have_verified_every_leaf_node_later tr1 tr2 me left group_id;
    i_have_verified_every_leaf_node_later tr1 tr2 me right group_id
  )
#pop-options

[@"opaque_to_smt"]
val log_leaf_node_verification_event:
  #tkt:treekem_types bytes ->
  principal ->
  leaf_node_nt bytes tkt -> mls_bytes bytes -> nat ->
  traceful unit
let log_leaf_node_verification_event #tkt me leaf_node group_id leaf_index =
  trigger_event me {leaf_node; group_id; leaf_index}

val log_leaf_node_verification_event_proof:
  {|protocol_invariants|} ->
  #tkt:treekem_types bytes ->
  tr:trace ->
  me:principal ->
  leaf_node:leaf_node_nt bytes tkt -> token:dy_as_token -> group_id:mls_bytes bytes -> leaf_index:nat ->
  Lemma
  (requires
    bytes_invariant tr group_id /\
    is_well_formed (leaf_node_nt bytes tkt) (bytes_invariant tr) leaf_node /\
    (dy_asp tr).credential_ok (leaf_node_to_as_input leaf_node) token /\
    leaf_is_valid leaf_node group_id leaf_index /\
    trace_invariant tr /\
    has_leaf_node_has_been_verified_invariant tkt
  )
  (ensures (
    let ((), tr_out) = log_leaf_node_verification_event me leaf_node group_id leaf_index tr in
    i_have_verified_leaf_node tr_out me leaf_node group_id leaf_index /\
    trace_invariant tr_out
  ))
let log_leaf_node_verification_event_proof #invs #tkt tr me leaf_node token group_id leaf_index =
  reveal_opaque (`%log_leaf_node_verification_event) (log_leaf_node_verification_event #tkt)

#push-options "--fuel 1 --ifuel 1"
[@"opaque_to_smt"]
val log_leaf_node_verification_events:
  #tkt:treekem_types bytes ->
  #l:nat -> #i:MLS.Tree.tree_index l ->
  me:principal ->
  MLS.TreeSync.Types.treesync bytes tkt l i -> mls_bytes bytes ->
  traceful unit
let rec log_leaf_node_verification_events #tkt #l #i me t group_id =
  match t with
  | TLeaf None -> return ()
  | TLeaf (Some ln) ->
    log_leaf_node_verification_event me ln group_id i
  | TNode _ left right ->
    log_leaf_node_verification_events me left group_id;*
    log_leaf_node_verification_events me right group_id
#pop-options

#push-options "--fuel 1 --ifuel 1"
val log_leaf_node_verification_events_proof:
  {|protocol_invariants|} ->
  #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l ->
  tr:trace -> me:principal ->
  tree:treesync bytes tkt l i -> tokens:as_tokens bytes dy_as_token l i -> group_id:mls_bytes bytes ->
  Lemma
  (requires
    bytes_invariant tr group_id /\
    is_well_formed _ (bytes_invariant tr) tree /\
    all_credentials_ok tree (tokens <: as_tokens bytes (dy_asp tr).token_t l i) /\
    valid_leaves_invariant group_id tree /\
    trace_invariant tr /\
    has_leaf_node_has_been_verified_invariant tkt
  )
  (ensures (
    let ((), tr_out) = log_leaf_node_verification_events me tree group_id tr in
    i_have_verified_every_leaf_node tr_out me tree group_id /\
    trace_invariant tr_out
  ))
let rec log_leaf_node_verification_events_proof #invs #tkt #l #i tr me tree tokens group_id =
  reveal_opaque (`%log_leaf_node_verification_events) (log_leaf_node_verification_events me tree group_id);
  match tree, tokens with
  | TLeaf None, _ -> ()
  | TLeaf (Some ln), TLeaf (Some token) ->
    log_leaf_node_verification_event_proof tr me ln token group_id i
  | TNode _ left right, TNode _ left_tokens right_tokens ->
    log_leaf_node_verification_events_proof tr me left left_tokens group_id;
    let (), tr = log_leaf_node_verification_events me left group_id tr in
    assert(is_well_formed _ (bytes_invariant tr) tree);
    log_leaf_node_verification_events_proof tr me right right_tokens group_id
  | _, _ -> assert(False)
#pop-options
