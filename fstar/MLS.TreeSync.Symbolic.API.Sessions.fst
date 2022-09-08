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
open MLS.Symbolic.Sessions
open MLS.Symbolic.Parsers
open MLS.TreeSync.Symbolic.IsValid
open MLS.TreeSync.Symbolic.SignatureGuarantees

#set-options "--fuel 1 --ifuel 1"

(*** Session predicate for public state ***)

val ps_treesync: #bytes:Type0 -> {|bytes_like bytes|} -> tkt:treekem_types bytes -> l:nat -> i:tree_index l -> parser_serializer bytes (treesync bytes tkt l i)
let ps_treesync #bytes tkt l i =
  ps_tree (ps_option (ps_leaf_node_nt tkt)) (ps_option (ps_parent_node_nt tkt)) l i

val ps_treesync_is_valid: #bytes:Type0 -> {|bytes_like bytes|} -> tkt:treekem_types bytes -> l:nat -> i:tree_index l -> pre:bytes_compatible_pre bytes -> x:treesync bytes tkt l i -> Lemma
  ((ps_treesync tkt l i).is_valid pre x <==> treesync_has_pre pre x)
let rec ps_treesync_is_valid #bytes #bl tkt l i pre x =
  match x with
  | TLeaf _ -> ()
  | TNode data left right ->
    ps_treesync_is_valid tkt (l-1) (left_index i) pre left;
    ps_treesync_is_valid tkt (l-1) (right_index i) pre right

val ps_as_tokens: #bytes:Type0 -> {|bytes_like bytes|} -> #as_token:Type0 -> parser_serializer bytes as_token -> l:nat -> i:tree_index l -> parser_serializer bytes (as_tokens bytes as_token l i)
let ps_as_tokens #bytes #bl #as_token ps_token l i =
  ps_tree (ps_option ps_token) ps_unit l i

val ps_dy_as_tokens: l:nat -> i:tree_index l -> parser_serializer dy_bytes (as_tokens dy_bytes dy_as_token l i)
let ps_dy_as_tokens l i =
  ps_as_tokens ps_dy_as_token l i

#push-options "--z3rlimit 25"
val ps_dy_as_tokens_is_valid: #l:nat -> #i:tree_index l -> pre:bytes_compatible_pre dy_bytes -> tokens:as_tokens dy_bytes dy_as_token l i ->
  Lemma ((ps_dy_as_tokens l i).is_valid pre tokens)
let rec ps_dy_as_tokens_is_valid #l #i pre tokens =
  match tokens with
  | TLeaf x -> (
    match x with
    | None -> ()
    | Some y -> ()
  )
  | TNode _ left right ->
    ps_dy_as_tokens_is_valid pre left;
    ps_dy_as_tokens_is_valid pre right
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
%splice [ps_bare_treesync_state__is_valid] (gen_is_valid_lemma (`bare_treesync_state_))

type bare_treesync_state (tkt:treekem_types dy_bytes) =
  bare_treesync_state_ dy_bytes tkt dy_as_token ps_dy_as_token

instance parseable_serializeable_bare_treesync_state (tkt:treekem_types dy_bytes): parseable_serializeable dy_bytes (bare_treesync_state tkt) = mk_parseable_serializeable (ps_bare_treesync_state_ tkt dy_as_token ps_dy_as_token)

val treesync_public_state_label: string
let treesync_public_state_label = "MLS.TreeSync.PublicState"

val bare_treesync_public_state_invariant: tkt:treekem_types dy_bytes -> bare_session_pred
let bare_treesync_public_state_invariant tkt gu p time si vi session =
  match parse (bare_treesync_state tkt) session with
  | None -> False
  | Some st -> (
    is_publishable gu time st.group_id /\
    treesync_has_pre (is_publishable gu time) st.tree /\
    unmerged_leaves_ok st.tree /\
    parent_hash_invariant st.tree /\
    valid_leaves_invariant st.group_id st.tree /\
    all_credentials_ok st.tree (st.tokens <: as_tokens dy_bytes (dy_asp gu time).token_t st.levels 0)
  )

#push-options "--fuel 0 --ifuel 0"
val treesync_public_state_invariant: treekem_types dy_bytes -> session_pred
let treesync_public_state_invariant tkt =
  mk_session_pred (bare_treesync_public_state_invariant tkt)
    (fun gu p time0 time1 si vi session ->
      let st = Some?.v (parse (bare_treesync_state tkt) session) in
      // Prove publishability of treesync in the future
      ps_treesync_is_valid tkt st.levels 0 (is_publishable gu time0) st.tree;
      ps_treesync_is_valid tkt st.levels 0 (is_publishable gu time1) st.tree;
      MLS.MiscLemmas.comparse_is_valid_weaken (ps_treesync tkt st.levels 0) (is_publishable gu time0) (is_publishable gu time1) st.tree
    )
    (fun gu p time si vi session ->
      let st = Some?.v (parse (bare_treesync_state tkt) session) in
      let pre = is_msg gu (readers [psv_id p si vi]) time in
      ps_treesync_is_valid tkt st.levels 0 (is_publishable gu time) st.tree;
      MLS.MiscLemmas.comparse_is_valid_weaken (ps_treesync tkt st.levels 0) (is_publishable gu time) pre st.tree;
      ps_dy_as_tokens_is_valid pre st.tokens;
      serialize_parse_inv_lemma (bare_treesync_state tkt) session;
      serialize_pre_lemma (bare_treesync_state tkt) pre st
    )
#pop-options

val has_treesync_public_state_invariant: treekem_types dy_bytes -> preds -> prop
let has_treesync_public_state_invariant tkt pr =
  has_session_pred pr treesync_public_state_label (treesync_public_state_invariant tkt)

(*** LCrypto API for public state ***)

val treesync_state_to_session_bytes:
  #tkt:treekem_types dy_bytes ->
  pr:preds -> p:principal -> time:timestamp -> si:nat -> vi:nat ->
  st:treesync_state dy_bytes tkt (dy_asp pr.global_usage time) ->
  Pure dy_bytes
  (requires
    is_publishable pr.global_usage time st.group_id /\
    treesync_has_pre (is_publishable pr.global_usage time) st.tree /\
    (ps_dy_as_tokens st.levels 0).is_valid (is_publishable pr.global_usage time) st.tokens /\
    has_treesync_public_state_invariant tkt pr
  )
  (ensures fun res -> treesync_public_state_invariant tkt pr.global_usage p time si vi res)
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
    treesync_has_pre (is_publishable pr.global_usage time) st.tree /\
    (ps_dy_as_tokens st.levels 0).is_valid (is_publishable pr.global_usage time) st.tokens /\
    has_treesync_public_state_invariant tkt pr
  )
  (ensures fun t0 si t1 -> trace_len t1 == trace_len t0 + 1)
let new_public_treesync_state #tkt pr p time st =
  let si = new_session_number pr p in
  let bare_st_bytes = treesync_state_to_session_bytes pr p time si 0 st in
  new_session pr treesync_public_state_label (treesync_public_state_invariant tkt) p si 0 bare_st_bytes;
  si

val set_public_treesync_state:
  #tkt:treekem_types dy_bytes ->
  pr:preds -> p:principal -> si:nat -> time:timestamp ->
  st:treesync_state dy_bytes tkt (dy_asp pr.global_usage time) ->
  LCrypto unit pr
  (requires fun t0 ->
    time == trace_len t0 /\
    is_publishable pr.global_usage time st.group_id /\
    treesync_has_pre (is_publishable pr.global_usage time) st.tree /\
    (ps_dy_as_tokens st.levels 0).is_valid (is_publishable pr.global_usage time) st.tokens /\
    has_treesync_public_state_invariant tkt pr
  )
  (ensures fun t0 r t1 -> trace_len t1 == trace_len t0 + 1)
let set_public_treesync_state #tkt pr p si time st =
  let bare_st_bytes = treesync_state_to_session_bytes pr p time si 0 st in
  update_session pr treesync_public_state_label (treesync_public_state_invariant tkt) p si 0 bare_st_bytes

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
    treesync_has_pre (is_publishable pr.global_usage time) st.tree /\
    t1 == t0
  )
let get_public_treesync_state #tkt pr p si time =
  let (_, st_bytes) = get_session pr treesync_public_state_label (treesync_public_state_invariant tkt) p si in
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
%splice [ps_treesync_private_state__is_valid] (gen_is_valid_lemma (`treesync_private_state_))

type treesync_private_state = treesync_private_state_ dy_bytes

instance parseable_serializeable_treesync_private_state: parseable_serializeable dy_bytes treesync_private_state = mk_parseable_serializeable ps_treesync_private_state_

val treesync_private_state_label: string
let treesync_private_state_label = "MLS.TreeSync.PrivateState"

val bare_treesync_private_state_invariant: bare_session_pred
let bare_treesync_private_state_invariant gu p time si vi session =
  match parse treesync_private_state session with
  | None -> False
  | Some st ->
    is_signature_key gu "MLS.LeafSignKey" (readers [p_id p]) time st.signature_key

val treesync_private_state_invariant: session_pred
let treesync_private_state_invariant =
  mk_session_pred bare_treesync_private_state_invariant
    (fun gu p time0 time1 si vi session -> ())
    (fun gu p time si vi session ->
      let st = Some?.v (parse treesync_private_state session) in
      let pre = is_msg gu (readers [psv_id p si vi]) time in
      serialize_parse_inv_lemma treesync_private_state session;
      serialize_pre_lemma treesync_private_state pre st
    )

val has_treesync_private_state_invariant: preds -> prop
let has_treesync_private_state_invariant pr =
  has_session_pred pr treesync_private_state_label treesync_private_state_invariant

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
  new_session pr treesync_private_state_label treesync_private_state_invariant p si 0 st_bytes;
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
  new_session pr treesync_private_state_label treesync_private_state_invariant p si 0 st_bytes

val get_private_treesync_state:
  pr:preds -> p:principal -> si:nat ->
  LCrypto treesync_private_state pr
  (requires fun t0 -> has_treesync_private_state_invariant pr)
  (ensures fun t0 st t1 ->
    is_signature_key pr.global_usage "MLS.LeafSignKey" (readers [p_id p]) (trace_len t0) st.signature_key /\
    t1 == t0
  )
let get_private_treesync_state pr p si =
  let (_, st_bytes) = get_session pr treesync_private_state_label treesync_private_state_invariant p si in
  let st = Some?.v (parse treesync_private_state st_bytes) in
  st
