module MLS.TreeSync.Symbolic.State.Tree

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
open MLS.TreeSync.Symbolic.AuthService
open MLS.TreeSync.Symbolic.LeafNodeSignature

#set-options "--fuel 1 --ifuel 1"

(*** Session predicate for public state ***)

val ps_dy_as_tokens: l:nat -> i:tree_index l -> parser_serializer bytes (as_tokens bytes dy_as_token l i)
let ps_dy_as_tokens l i =
  ps_as_tokens ps_dy_as_token l i

#push-options "--z3rlimit 25"
val ps_dy_as_tokens_is_well_formed:
  #l:nat -> #i:tree_index l ->
  pre:bytes_compatible_pre bytes -> tokens:as_tokens bytes dy_as_token l i ->
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

// define type for tokens to work around F* bug
type tokens_type (levels:nat) = as_tokens bytes dy_as_token levels 0
let ps_tokens_type (levels:nat): parser_serializer bytes (tokens_type levels) =
  ps_as_tokens ps_dy_as_token levels 0

[@@ with_bytes bytes]
noeq
type bare_treesync_state (tkt:treekem_types bytes) = {
  group_id: mls_bytes bytes;
  [@@@ with_parser #bytes ps_nat]
  levels: nat;
  [@@@ with_parser #bytes (ps_treesync tkt levels 0)]
  tree: treesync bytes tkt levels 0;
  // [@@@ with_parser #bytes (ps_as_tokens ps_dy_as_token levels 0)]
  // tokens: as_tokens bytes dy_as_token levels 0;
  tokens: tokens_type levels;
}

%splice [ps_bare_treesync_state] (gen_parser (`bare_treesync_state))
#push-options "--z3rlimit 20"
%splice [ps_bare_treesync_state_is_well_formed] (gen_is_well_formed_lemma (`bare_treesync_state))
#pop-options

instance parseable_serializeable_bare_treesync_state (tkt:treekem_types bytes): parseable_serializeable bytes (bare_treesync_state tkt) = mk_parseable_serializeable (ps_bare_treesync_state tkt)

instance local_state_bare_treesync_state (tkt:treekem_types bytes): local_state (bare_treesync_state tkt) =
  mk_local_state_instance "MLS.TreeSync.PublicState"

#push-options "--fuel 1 --ifuel 1 --z3rlimit 25"
val treesync_public_state_pred: {|crypto_invariants|} -> tkt:treekem_types bytes -> local_state_predicate (bare_treesync_state tkt)
let treesync_public_state_pred #ci tkt = {
  pred = (fun tr prin state_id st ->
    is_publishable tr st.group_id /\
    is_well_formed _ (is_publishable tr) st.tree /\
    unmerged_leaves_ok st.tree /\
    parent_hash_invariant st.tree /\
    valid_leaves_invariant st.group_id st.tree /\
    all_credentials_ok st.tree ((st.tokens <: as_tokens bytes dy_as_token st.levels 0) <: as_tokens bytes (dy_asp tr).token_t st.levels 0)
  );
  pred_later = (fun tr1 tr2 prin state_id st ->
    wf_weaken_lemma _ (is_publishable tr1) (is_publishable tr2) st.tree
  );
  pred_knowable = (fun tr prin state_id st ->
    let pre = is_knowable_by (principal_typed_state_content_label prin (local_state_bare_treesync_state tkt).tag state_id st) tr in
    ps_dy_as_tokens_is_well_formed pre st.tokens;
    assert(is_well_formed _ pre st.tree);
    assert(is_well_formed _ pre st)
  );
}
#pop-options

val has_treesync_public_state_invariant: treekem_types bytes -> {|protocol_invariants|} -> prop
let has_treesync_public_state_invariant tkt #invs =
  has_local_state_predicate (treesync_public_state_pred tkt)

val treesync_public_state_tag_and_invariant: {|crypto_invariants|} -> treekem_types bytes -> dtuple2 string local_bytes_state_predicate
let treesync_public_state_tag_and_invariant #ci tkt = (|(local_state_bare_treesync_state tkt).tag, local_state_predicate_to_local_bytes_state_predicate (treesync_public_state_pred tkt)|)

(*** Traceful API for public state ***)

val treesync_state_to_bare_treesync_state:
  #tkt:treekem_types bytes ->
  #group_id:mls_bytes bytes -> st:treesync_state bytes tkt dy_as_token group_id ->
  bare_treesync_state tkt
let treesync_state_to_bare_treesync_state #tkt #group_id st = {
    group_id = group_id;
    levels = st.levels;
    tree = st.tree;
    tokens = st.tokens;
  }

[@"opaque_to_smt"]
val new_public_treesync_state:
  #tkt:treekem_types bytes -> #group_id:mls_bytes bytes -> 
  principal ->
  st:treesync_state bytes tkt dy_as_token group_id ->
  traceful state_id
let new_public_treesync_state #tkt #group_id prin st =
  let* state_id = new_session_id prin in
  set_state prin state_id (treesync_state_to_bare_treesync_state st);*
  return state_id

[@"opaque_to_smt"]
val new_public_treesync_state_proof:
  {|protocol_invariants|} ->
  #tkt:treekem_types bytes -> #group_id:mls_bytes bytes -> 
  prin:principal ->
  st:treesync_state bytes tkt dy_as_token group_id ->
  tr:trace ->
  Lemma
  (requires
    is_publishable tr group_id /\
    is_well_formed _ (is_publishable tr) (st.tree <: treesync _ _ _ _) /\
    treesync_state_valid #bytes #crypto_bytes_bytes (dy_asp tr) st /\
    trace_invariant tr /\
    has_treesync_public_state_invariant tkt
  )
  (ensures (
    let (_, tr_out) = new_public_treesync_state prin st tr in
    trace_invariant tr_out
  ))
  [SMTPat (new_public_treesync_state prin st tr); SMTPat (trace_invariant tr)]
let new_public_treesync_state_proof #invs #tkt #group_id prin st tr =
  reveal_opaque (`%new_public_treesync_state) (new_public_treesync_state #tkt #group_id)

[@"opaque_to_smt"]
val set_public_treesync_state:
  #tkt:treekem_types bytes -> #group_id:mls_bytes bytes ->
  prin:principal -> state_id:state_id ->
  st:treesync_state bytes tkt dy_as_token group_id ->
  traceful unit
let set_public_treesync_state #tkt #group_id prin state_id st =
  set_state prin state_id (treesync_state_to_bare_treesync_state st)

val set_public_treesync_state_proof:
  {|protocol_invariants|} ->
  #tkt:treekem_types bytes -> #group_id:mls_bytes bytes ->
  prin:principal -> state_id:state_id ->
  st:treesync_state bytes tkt dy_as_token group_id ->
  tr:trace ->
  Lemma
  (requires
    is_publishable tr group_id /\
    is_well_formed _ (is_publishable tr) (st.tree <: treesync _ _ _ _) /\
    treesync_state_valid #bytes #crypto_bytes_bytes (dy_asp tr) st /\
    trace_invariant tr /\
    has_treesync_public_state_invariant tkt
  )
  (ensures (
    let ((), tr_out) = set_public_treesync_state prin state_id st tr in
    trace_invariant tr_out
  ))
  [SMTPat (set_public_treesync_state prin state_id st tr); SMTPat (trace_invariant tr)]
let set_public_treesync_state_proof #invs #tkt #group_id prin state_id st tr =
  reveal_opaque (`%set_public_treesync_state) (set_public_treesync_state #tkt #group_id)

[@"opaque_to_smt"]
val get_public_treesync_state:
  #tkt:treekem_types bytes ->
  prin:principal -> state_id:state_id ->
  traceful (option (dtuple2 (mls_bytes bytes) (treesync_state bytes tkt dy_as_token)))
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
  } <: treesync_state bytes tkt dy_as_token bare_st.group_id)|))

#push-options "--fuel 0 --ifuel 0"
val get_public_treesync_state_proof:
  {|protocol_invariants|} ->
  #tkt:treekem_types bytes ->
  prin:principal -> state_id:state_id ->
  tr:trace ->
  Lemma
  (requires
    trace_invariant tr /\
    has_treesync_public_state_invariant tkt
  )
  (ensures (
    let (opt_result, tr_out) = get_public_treesync_state prin state_id tr in
    tr_out == tr /\ (
      match opt_result with
      | None -> True
      | Some (|group_id, st|) -> (
        is_publishable tr_out group_id /\
        is_well_formed _ (is_publishable tr_out) (st.tree <: treesync bytes tkt _ _) /\
        treesync_state_valid #bytes #crypto_bytes_bytes (dy_asp tr) st
      )
    )
  ))
  [SMTPat (get_public_treesync_state #tkt prin state_id tr); SMTPat (trace_invariant tr)]
let get_public_treesync_state_proof #invs #tkt prin state_id tr =
  reveal_opaque (`%get_public_treesync_state) (get_public_treesync_state #tkt)
#pop-options
