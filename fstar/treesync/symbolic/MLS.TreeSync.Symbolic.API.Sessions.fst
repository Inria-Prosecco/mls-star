module MLS.TreeSync.Symbolic.API.Sessions

open Comparse
open DY.Core
open DY.Lib
open MLS.Tree
open MLS.NetworkTypes
open MLS.TreeSync.NetworkTypes
open MLS.TreeSync.Types
open MLS.TreeSync.Invariants.UnmergedLeaves
open MLS.TreeSync.Invariants.ParentHash
open MLS.TreeSync.Invariants.ValidLeaves
open MLS.TreeSync.Invariants.AuthService
open MLS.TreeSync.API.Types
open MLS.Symbolic
open MLS.TreeSync.Symbolic.Parsers
open MLS.TreeSync.Symbolic.IsWellFormed
open MLS.TreeSync.Symbolic.LeafNodeSignature

#set-options "--fuel 1 --ifuel 1"

(*** Session predicate for public state ***)

val ps_dy_as_tokens: l:nat -> i:tree_index l -> parser_serializer dy_bytes (as_tokens dy_bytes dy_as_token l i)
let ps_dy_as_tokens l i =
  ps_as_tokens ps_dy_as_token l i

#push-options "--z3rlimit 25"
val ps_dy_as_tokens_is_well_formed:
  #l:nat -> #i:tree_index l ->
  pre:bytes_compatible_pre dy_bytes -> tokens:as_tokens dy_bytes dy_as_token l i ->
  Lemma
  (is_well_formed_prefix (ps_dy_as_tokens l i) pre tokens)
let rec ps_dy_as_tokens_is_well_formed #l #i pre tokens =
  match tokens with
  | TLeaf x -> (
    match x with
    | None -> ()
    | Some y -> ()
  )
  | TNode _ left right ->
    ps_dy_as_tokens_is_well_formed pre left;
    ps_dy_as_tokens_is_well_formed pre right
#pop-options

noeq
type bare_treesync_state_ (bytes:Type0) {|bytes_like bytes|} (tkt:treekem_types bytes) (as_token:Type0) (ps_token:parser_serializer bytes as_token) = {
  group_id: mls_bytes bytes;
  [@@@ with_parser #bytes ps_nat]
  levels: nat;
  [@@@ with_parser #bytes (ps_treesync tkt levels 0)]
  tree: treesync bytes tkt levels 0;
  [@@@ with_parser #bytes (ps_as_tokens ps_token levels 0)]
  tokens: as_tokens bytes as_token levels 0;
}

%splice [ps_bare_treesync_state_] (gen_parser (`bare_treesync_state_))
#push-options "--z3rlimit 20"
%splice [ps_bare_treesync_state__is_well_formed] (gen_is_well_formed_lemma (`bare_treesync_state_))
#pop-options

type bare_treesync_state (tkt:treekem_types dy_bytes) =
  bare_treesync_state_ dy_bytes tkt dy_as_token ps_dy_as_token

instance parseable_serializeable_bare_treesync_state (tkt:treekem_types dy_bytes): parseable_serializeable dy_bytes (bare_treesync_state tkt) = mk_parseable_serializeable (ps_bare_treesync_state_ tkt dy_as_token ps_dy_as_token)

#push-options "--fuel 1 --ifuel 1 --z3rlimit 25"
val treesync_public_state_pred: {|crypto_invariants|} -> tkt:treekem_types dy_bytes -> local_state_predicate (bare_treesync_state tkt)
let treesync_public_state_pred #ci tkt = {
  pred = (fun tr prin state_id st ->
    is_publishable tr st.group_id /\
    is_well_formed _ (is_publishable tr) st.tree /\
    unmerged_leaves_ok st.tree /\
    parent_hash_invariant st.tree /\
    valid_leaves_invariant st.group_id st.tree /\
    all_credentials_ok st.tree ((st.tokens <: as_tokens dy_bytes dy_as_token st.levels 0) <: as_tokens dy_bytes (dy_asp tr).token_t st.levels 0)
  );
  pred_later = (fun tr1 tr2 prin state_id st ->
    wf_weaken_lemma _ (is_publishable tr1) (is_publishable tr2) st.tree
  );
  pred_knowable = (fun tr prin state_id st ->
    let pre = is_knowable_by (principal_state_label prin state_id) tr in
    wf_weaken_lemma _ (is_publishable tr) pre st.tree;
    ps_dy_as_tokens_is_well_formed pre st.tokens
  );
}
#pop-options

instance local_state_bare_treesync_state (tkt:treekem_types dy_bytes): local_state (bare_treesync_state tkt) =
  mk_local_state_instance "MLS.TreeSync.PublicState"

val has_treesync_public_state_invariant: treekem_types dy_bytes -> protocol_invariants -> prop
let has_treesync_public_state_invariant tkt invs =
  has_local_state_predicate invs (treesync_public_state_pred tkt)

val treesync_public_state_tag_and_invariant: {|crypto_invariants|} -> treekem_types dy_bytes -> string & local_bytes_state_predicate
let treesync_public_state_tag_and_invariant #ci tkt = ((local_state_bare_treesync_state tkt).tag, local_state_predicate_to_local_bytes_state_predicate (treesync_public_state_pred tkt))

(*** Traceful API for public state ***)

val treesync_state_to_bare_treesync_state:
  #tkt:treekem_types dy_bytes ->
  #group_id:mls_bytes dy_bytes -> st:treesync_state dy_bytes tkt dy_as_token group_id ->
  bare_treesync_state tkt
let treesync_state_to_bare_treesync_state #tkt #group_id st = {
    group_id = group_id;
    levels = st.levels;
    tree = st.tree;
    tokens = st.tokens;
  }

val new_public_treesync_state:
  #tkt:treekem_types dy_bytes -> #group_id:mls_bytes dy_bytes -> 
  principal ->
  st:treesync_state dy_bytes tkt dy_as_token group_id ->
  traceful state_id
let new_public_treesync_state #tkt #group_id prin st =
  let* state_id = new_session_id prin in
  set_state prin state_id (treesync_state_to_bare_treesync_state st);*
  return state_id

val new_public_treesync_state_proof:
  {|invs:protocol_invariants|} ->
  #tkt:treekem_types dy_bytes -> #group_id:mls_bytes dy_bytes -> 
  prin:principal ->
  st:treesync_state dy_bytes tkt dy_as_token group_id ->
  tr:trace ->
  Lemma
  (requires
    is_publishable tr group_id /\
    is_well_formed _ (is_publishable tr) (st.tree <: treesync _ _ _ _) /\
    treesync_state_valid (dy_asp tr) st /\
    trace_invariant tr /\
    has_treesync_public_state_invariant tkt invs
  )
  (ensures (
    let (_, tr_out) = new_public_treesync_state prin st tr in
    trace_invariant tr_out
  ))
let new_public_treesync_state_proof #invs #tkt #group_id prin st tr = ()

val set_public_treesync_state:
  #tkt:treekem_types dy_bytes -> #group_id:mls_bytes dy_bytes ->
  prin:principal -> state_id:state_id ->
  st:treesync_state dy_bytes tkt dy_as_token group_id ->
  traceful unit
let set_public_treesync_state #tkt #group_id prin state_id st =
  set_state prin state_id (treesync_state_to_bare_treesync_state st)

val set_public_treesync_state_proof:
  {|invs:protocol_invariants|} ->
  #tkt:treekem_types dy_bytes -> #group_id:mls_bytes dy_bytes ->
  prin:principal -> state_id:state_id ->
  st:treesync_state dy_bytes tkt dy_as_token group_id ->
  tr:trace ->
  Lemma
  (requires
    is_publishable tr group_id /\
    is_well_formed _ (is_publishable tr) (st.tree <: treesync _ _ _ _) /\
    treesync_state_valid (dy_asp tr) st /\
    trace_invariant tr /\
    has_treesync_public_state_invariant tkt invs
  )
  (ensures (
    let ((), tr_out) = set_public_treesync_state prin state_id st tr in
    trace_invariant tr_out
  ))
let set_public_treesync_state_proof #invs #tkt #group_id prin state_id st tr = ()

val get_public_treesync_state:
  #tkt:treekem_types dy_bytes ->
  prin:principal -> state_id:state_id ->
  traceful (option (dtuple2 (mls_bytes dy_bytes) (treesync_state dy_bytes tkt dy_as_token)))
let get_public_treesync_state #tkt prin state_id =
  let*? bare_st: bare_treesync_state tkt = get_state prin state_id in
  // TODO: Dynamic could be removed with REPROSEC/dolev-yao-star-extrinsic#24
  if not (unmerged_leaves_ok bare_st.tree && parent_hash_invariant bare_st.tree && valid_leaves_invariant bare_st.group_id bare_st.tree) then
    return None
  else
  return (Some (|bare_st.group_id, ({
    levels = bare_st.levels;
    tree = bare_st.tree;
    tokens = bare_st.tokens;
  } <: treesync_state dy_bytes tkt dy_as_token bare_st.group_id)|))

val get_public_treesync_state_proof:
  {|invs:protocol_invariants|} ->
  #tkt:treekem_types dy_bytes ->
  prin:principal -> state_id:state_id ->
  tr:trace ->
  Lemma
  (requires
    trace_invariant tr /\
    has_treesync_public_state_invariant tkt invs
  )
  (ensures (
    let (opt_result, tr_out) = get_public_treesync_state prin state_id tr in
    tr_out == tr /\ (
      match opt_result with
      | None -> True
      | Some (|group_id, st|) -> (
        is_publishable tr_out group_id /\
        is_well_formed _ (is_publishable tr_out) (st.tree <: treesync dy_bytes tkt _ _)
      )
    )
  ))
let get_public_treesync_state_proof #invs #tkt prin state_id tr = ()

(*** Session predicate for private state ***)

type treesync_private_state_ (bytes:Type0) {|bytes_like bytes|} = {
  signature_key: mls_bytes bytes;
}

%splice [ps_treesync_private_state_] (gen_parser (`treesync_private_state_))
%splice [ps_treesync_private_state__is_well_formed] (gen_is_well_formed_lemma (`treesync_private_state_))

type treesync_private_state = treesync_private_state_ dy_bytes

instance parseable_serializeable_treesync_private_state: parseable_serializeable dy_bytes treesync_private_state = mk_parseable_serializeable ps_treesync_private_state_

val treesync_private_state_pred: {|crypto_invariants|} -> local_state_predicate treesync_private_state
let treesync_private_state_pred #ci = {
  pred = (fun tr prin state_id st ->
    is_signature_key (SigKey "MLS.LeafSignKey" empty) (principal_label prin) tr st.signature_key
  );
  pred_later = (fun tr1 tr2 prin state_id st -> ());
  pred_knowable = (fun tr prin state_id st -> ());
}

instance local_state_treesync_private_state: local_state treesync_private_state =
  mk_local_state_instance "MLS.TreeSync.PrivateState"

val has_treesync_private_state_invariant: protocol_invariants -> prop
let has_treesync_private_state_invariant invs =
  has_local_state_predicate invs treesync_private_state_pred

val treesync_private_state_tag_and_invariant: {|crypto_invariants|} -> string & local_bytes_state_predicate
let treesync_private_state_tag_and_invariant #ci = (local_state_treesync_private_state.tag, local_state_predicate_to_local_bytes_state_predicate treesync_private_state_pred)

(*** Traceful API for private state ***)

val new_private_treesync_state:
  principal -> treesync_private_state ->
  traceful state_id
let new_private_treesync_state prin st =
  let* state_id = new_session_id prin in
  set_state prin state_id st;*
  return state_id

val new_private_treesync_state_proof:
  {|invs:protocol_invariants|} ->
  prin:principal -> st:treesync_private_state ->
  tr:trace ->
  Lemma
  (requires
    is_signature_key (SigKey "MLS.LeafSignKey" empty) (principal_label prin) tr st.signature_key /\
    trace_invariant tr /\
    has_treesync_private_state_invariant invs
  )
  (ensures (
    let (_, tr_out) = new_private_treesync_state prin st tr in
    trace_invariant tr_out
  ))
let new_private_treesync_state_proof #invs prin st tr = ()

val set_private_treesync_state:
  principal -> state_id -> treesync_private_state ->
  traceful unit
let set_private_treesync_state prin state_id st =
  set_state prin state_id st

val set_private_treesync_state_proof:
  {|invs:protocol_invariants|} ->
  prin:principal -> state_id:state_id -> st:treesync_private_state ->
  tr:trace ->
  Lemma
  (requires
    is_signature_key (SigKey "MLS.LeafSignKey" empty) (principal_label prin) tr st.signature_key /\
    trace_invariant tr /\
    has_treesync_private_state_invariant invs
  )
  (ensures (
    let ((), tr_out) = set_private_treesync_state prin state_id st tr in
    trace_invariant tr_out
  ))
let set_private_treesync_state_proof #invs prin state_id st tr = ()

val get_private_treesync_state:
  principal -> state_id ->
  traceful (option treesync_private_state)
let get_private_treesync_state prin state_id =
  get_state prin state_id

val get_private_treesync_state_proof:
  {|invs:protocol_invariants|} ->
  prin:principal -> state_id:state_id ->
  tr:trace ->
  Lemma
  (requires
    trace_invariant tr /\
    has_treesync_private_state_invariant invs
  )
  (ensures (
    let (opt_result, tr_out) = get_private_treesync_state prin state_id tr in
    tr_out == tr /\ (
      match opt_result with
      | None -> True
      | Some st ->
        is_signature_key (SigKey "MLS.LeafSignKey" empty) (principal_label prin) tr st.signature_key
    )
  ))
let get_private_treesync_state_proof #invs prin state_id tr = ()
