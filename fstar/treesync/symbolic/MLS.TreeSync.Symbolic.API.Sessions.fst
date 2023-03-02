module MLS.TreeSync.Symbolic.API.Sessions

open Comparse
open GlobalRuntimeLib
open LabeledRuntimeAPI
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
open MLS.Symbolic.Session
open MLS.Symbolic.TypedSession
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

val treesync_public_state_label: string
let treesync_public_state_label = "MLS.TreeSync.PublicState"

// The `fun` is a workaround for FStarLang/FStar#2694
val bare_treesync_public_state_pred: tkt:treekem_types dy_bytes -> bare_typed_session_pred (bare_treesync_state tkt)
let bare_treesync_public_state_pred tkt = fun gu p time si vi st ->
  is_publishable gu time st.group_id /\
  is_well_formed _ (is_publishable gu time) st.tree /\
  unmerged_leaves_ok st.tree /\
  parent_hash_invariant st.tree /\
  valid_leaves_invariant st.group_id st.tree /\
  all_credentials_ok st.tree (st.tokens <: as_tokens dy_bytes (dy_asp gu time).token_t st.levels 0)

#push-options "--fuel 0 --ifuel 0"
val treesync_public_state_pred: treekem_types dy_bytes -> session_pred
let treesync_public_state_pred tkt =
  typed_session_pred_to_session_pred (
    mk_typed_session_pred (bare_treesync_public_state_pred tkt)
      (fun gu p time0 time1 si vi st ->
        // Prove publishability of treesync in the future
        wf_weaken_lemma _ (is_publishable gu time0) (is_publishable gu time1) st.tree
      )
      (fun gu p time si vi st ->
        let pre = is_msg gu (readers [psv_id p si vi]) time in
        wf_weaken_lemma _ (is_publishable gu time) pre st.tree;
        ps_dy_as_tokens_is_well_formed pre st.tokens
      )
  )
#pop-options

val has_treesync_public_state_invariant: treekem_types dy_bytes -> preds -> prop
let has_treesync_public_state_invariant tkt pr =
  has_session_pred pr treesync_public_state_label (treesync_public_state_pred tkt)

(*** LCrypto API for public state ***)

val treesync_state_to_session_bytes:
  #tkt:treekem_types dy_bytes ->
  pr:preds -> p:principal -> time:timestamp -> si:nat -> vi:nat ->
  st:treesync_state dy_bytes tkt (dy_asp pr.global_usage time) ->
  Pure dy_bytes
  (requires
    is_publishable pr.global_usage time st.group_id /\
    is_well_formed _ (is_publishable pr.global_usage time) (st.tree <: treesync _ _ _ _) /\
    has_treesync_public_state_invariant tkt pr
  )
  (ensures fun res -> treesync_public_state_pred tkt pr.global_usage p time si vi res)
let treesync_state_to_session_bytes #tkt pr p time si vi st =
  let bare_st: bare_treesync_state tkt = {
    group_id = st.group_id;
    levels = st.levels;
    tree = st.tree;
    tokens = st.tokens;
  } in
  parse_serialize_inv_lemma #dy_bytes (bare_treesync_state tkt) bare_st;
  serialize (bare_treesync_state tkt) bare_st

val new_public_treesync_state:
  #tkt:treekem_types dy_bytes ->
  pr:preds -> p:principal -> time:timestamp ->
  st:treesync_state dy_bytes tkt (dy_asp pr.global_usage time) ->
  LCrypto nat pr
  (requires fun t0 ->
    time == trace_len t0 /\
    is_publishable pr.global_usage time st.group_id /\
    is_well_formed _ (is_publishable pr.global_usage time) (st.tree <: treesync _ _ _ _) /\
    has_treesync_public_state_invariant tkt pr
  )
  (ensures fun t0 si t1 -> trace_len t1 == trace_len t0 + 1)
let new_public_treesync_state #tkt pr p time st =
  let si = new_session_number pr p in
  let bare_st_bytes = treesync_state_to_session_bytes pr p time si 0 st in
  new_session pr treesync_public_state_label (treesync_public_state_pred tkt) p si 0 bare_st_bytes;
  si

val set_public_treesync_state:
  #tkt:treekem_types dy_bytes ->
  pr:preds -> p:principal -> si:nat -> time:timestamp ->
  st:treesync_state dy_bytes tkt (dy_asp pr.global_usage time) ->
  LCrypto unit pr
  (requires fun t0 ->
    time == trace_len t0 /\
    is_publishable pr.global_usage time st.group_id /\
    is_well_formed _ (is_publishable pr.global_usage time) (st.tree <: treesync _ _ _ _) /\
    has_treesync_public_state_invariant tkt pr
  )
  (ensures fun t0 r t1 -> trace_len t1 == trace_len t0 + 1)
let set_public_treesync_state #tkt pr p si time st =
  let bare_st_bytes = treesync_state_to_session_bytes pr p time si 0 st in
  update_session pr treesync_public_state_label (treesync_public_state_pred tkt) p si 0 bare_st_bytes

val get_public_treesync_state:
  #tkt:treekem_types dy_bytes ->
  pr:preds -> p:principal -> si:nat -> time:timestamp ->
  LCrypto (treesync_state dy_bytes tkt (dy_asp pr.global_usage time)) pr
  (requires fun t0 ->
    time == trace_len t0 /\
    has_treesync_public_state_invariant tkt pr
  )
  (ensures fun t0 st t1 ->
    is_publishable pr.global_usage time st.group_id /\
    is_well_formed _ (is_publishable pr.global_usage time) (st.tree <: treesync _ _ _ _) /\
    t1 == t0
  )
let get_public_treesync_state #tkt pr p si time =
  let (_, st_bytes) = get_session pr treesync_public_state_label (treesync_public_state_pred tkt) p si in
  let st = Some?.v (parse (bare_treesync_state tkt) st_bytes) in
  {
    group_id = st.group_id;
    levels = st.levels;
    tree = st.tree;
    tokens = st.tokens;
  }

(*** Session predicate for private state ***)

type treesync_private_state_ (bytes:Type0) {|bytes_like bytes|} = {
  signature_key: mls_bytes bytes;
}

%splice [ps_treesync_private_state_] (gen_parser (`treesync_private_state_))
%splice [ps_treesync_private_state__is_well_formed] (gen_is_well_formed_lemma (`treesync_private_state_))

type treesync_private_state = treesync_private_state_ dy_bytes

instance parseable_serializeable_treesync_private_state: parseable_serializeable dy_bytes treesync_private_state = mk_parseable_serializeable ps_treesync_private_state_

val treesync_private_state_label: string
let treesync_private_state_label = "MLS.TreeSync.PrivateState"

val bare_treesync_private_state_pred: bare_typed_session_pred treesync_private_state
let bare_treesync_private_state_pred gu p time si vi st =
  is_signature_key gu "MLS.LeafSignKey" (readers [p_id p]) time st.signature_key

val treesync_private_state_pred: session_pred
let treesync_private_state_pred =
  typed_session_pred_to_session_pred bare_treesync_private_state_pred

val has_treesync_private_state_invariant: preds -> prop
let has_treesync_private_state_invariant pr =
  has_session_pred pr treesync_private_state_label treesync_private_state_pred

(*** LCrypto API for private state ***)

val new_private_treesync_state:
  pr:preds -> p:principal ->
  st:treesync_private_state ->
  LCrypto nat pr
  (requires fun t0 ->
    is_signature_key pr.global_usage "MLS.LeafSignKey" (readers [p_id p]) (trace_len t0) st.signature_key /\
    has_treesync_private_state_invariant pr
  )
  (ensures fun t0 si t1 -> trace_len t1 == trace_len t0 + 1)
let new_private_treesync_state pr p st =
  let si = new_session_number pr p in
  let st_bytes = serialize treesync_private_state st in
  parse_serialize_inv_lemma #dy_bytes treesync_private_state st;
  new_session pr treesync_private_state_label treesync_private_state_pred p si 0 st_bytes;
  si

val set_private_treesync_state:
  pr:preds -> p:principal -> si:nat ->
  st:treesync_private_state ->
  LCrypto unit pr
  (requires fun t0 ->
    is_signature_key pr.global_usage "MLS.LeafSignKey" (readers [p_id p]) (trace_len t0) st.signature_key /\
    has_treesync_private_state_invariant pr
  )
  (ensures fun t0 r t1 -> trace_len t1 == trace_len t0 + 1)
let set_private_treesync_state pr p si st =
  let st_bytes = serialize treesync_private_state st in
  parse_serialize_inv_lemma #dy_bytes treesync_private_state st;
  new_session pr treesync_private_state_label treesync_private_state_pred p si 0 st_bytes

val get_private_treesync_state:
  pr:preds -> p:principal -> si:nat ->
  LCrypto treesync_private_state pr
  (requires fun t0 -> has_treesync_private_state_invariant pr)
  (ensures fun t0 st t1 ->
    is_signature_key pr.global_usage "MLS.LeafSignKey" (readers [p_id p]) (trace_len t0) st.signature_key /\
    t1 == t0
  )
let get_private_treesync_state pr p si =
  let (_, st_bytes) = get_session pr treesync_private_state_label treesync_private_state_pred p si in
  let st = Some?.v (parse treesync_private_state st_bytes) in
  st
