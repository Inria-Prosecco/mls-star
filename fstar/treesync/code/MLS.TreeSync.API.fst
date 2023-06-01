module MLS.TreeSync.API

open Comparse
open MLS.Crypto
open MLS.MiscLemmas
open MLS.NetworkTypes
open MLS.TreeSync.NetworkTypes
open MLS.Tree
open MLS.Tree.Lemmas
open MLS.TreeCommon
open MLS.TreeCommon.Lemmas
open MLS.TreeSync.Types
open MLS.TreeSync.Operations
open MLS.TreeSync.Refined.Types
open MLS.TreeSync.Refined.Operations
open MLS.TreeSync.API.Types
open MLS.TreeSync.Invariants.UnmergedLeaves
open MLS.TreeSync.Invariants.ParentHash
open MLS.TreeSync.Invariants.ValidLeaves
open MLS.TreeSync.Invariants.AuthService
open MLS.TreeSync.Invariants.AuthService.Proofs
open MLS.Result

#set-options "--fuel 0 --ifuel 0"

let as_input_for
  (#bytes:Type0) {|bytes_like bytes|} (#tkt:treekem_types bytes)
  (ln:leaf_node_nt bytes tkt) =
  x:as_input bytes{ x == leaf_node_to_as_input ln }

let as_token_for
  (#bytes:Type0) {|bytes_like bytes|}
  (asp:as_parameters bytes) (inp:as_input bytes) =
  token:asp.token_t{ asp.credential_ok inp token }

val state_leaf_at:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes -> #asp:as_parameters bytes ->
  st:treesync_state bytes tkt asp -> li:treesync_index st{Some? (leaf_at st.tree li)} ->
  leaf_node_nt bytes tkt
let state_leaf_at #bytes #cb #tkt #asp st li =
  Some?.v (leaf_at st.tree li)

val state_update_tree:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes -> #asp:as_parameters bytes ->
  #l:nat ->
  st:treesync_state bytes tkt asp -> new_tree:treesync_valid bytes tkt l 0 st.group_id -> new_tokens:as_tokens bytes asp.token_t l 0{all_credentials_ok new_tree new_tokens} ->
  treesync_state bytes tkt asp
let state_update_tree #bytes #cb #tkt #asp #l st new_tree new_tokens =
  ({ st with
    levels = l;
    tree = new_tree;
    tokens = new_tokens;
  })

(*** Create ***)

let pending_create_proof
  (#bytes:Type0) {|crypto_bytes bytes|} (#tkt:treekem_types bytes)
  (group_id:mls_bytes bytes) (ln:leaf_node_nt bytes tkt) =
  squash (
    leaf_is_valid ln group_id 0
  )

type pending_create
  (#bytes:Type0) {|crypto_bytes bytes|} (#tkt:treekem_types bytes)
  (group_id:mls_bytes bytes) (ln:leaf_node_nt bytes tkt) =
  {
  can_create_proof: pending_create_proof group_id ln;
  as_input: as_input_for ln;
}

type token_for_create
  (#bytes:Type0) {|crypto_bytes bytes|} (#tkt:treekem_types bytes)
  (#group_id:mls_bytes bytes) (#ln:leaf_node_nt bytes tkt)
  (asp:as_parameters bytes) (pend:pending_create group_id ln) =
  as_token_for asp pend.as_input

val prepare_create:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes ->
  group_id:mls_bytes bytes -> ln:leaf_node_nt bytes tkt ->
  result (pending_create group_id ln)
let prepare_create #bytes #cb #tkt group_id ln =
  if not (leaf_is_valid ln group_id 0) then
    error "prepare_create: leaf node is not valid"
  else (
    return ({
      can_create_proof = ();
      as_input = leaf_node_to_as_input ln;
    })
  )

val finalize_create:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes -> #asp:as_parameters bytes ->
  #group_id:mls_bytes bytes -> #ln:leaf_node_nt bytes tkt ->
  pend:pending_create group_id ln -> token:token_for_create asp pend ->
  treesync_state bytes tkt asp
let finalize_create #bytes #cb #tkt #asp #group_id #ln pend token =
  pend.can_create_proof;
  all_credentials_ok_tree_create ln token;
  ({
    group_id;
    levels = 0;
    tree = tree_create ln;
    tokens = MLS.TreeCommon.tree_create (Some token);
  })

(*** Welcome ***)

let pending_welcome_proof
  (#bytes:Type0) {|crypto_bytes bytes|} (#tkt:treekem_types bytes)
  (#l:nat) (group_id:mls_bytes bytes) (t:treesync bytes tkt l 0) =
  squash (
    unmerged_leaves_ok t /\
    parent_hash_invariant t /\
    valid_leaves_invariant group_id t
  )

#push-options "--fuel 0 --ifuel 1"
type pending_welcome
  (#bytes:Type0) {|crypto_bytes bytes|} (#tkt:treekem_types bytes) (#l:nat)
  (group_id:mls_bytes bytes) (t:treesync bytes tkt l 0) =
  {
  can_welcome_proof: pending_welcome_proof group_id t;
  as_inputs: list (option (as_input bytes));
  as_inputs_proof: squash (
    List.Tot.length as_inputs == pow2 l /\ (
      forall (li:nat{li < pow2 l}). List.Tot.index as_inputs li == Option.mapTot leaf_node_to_as_input (leaf_at t li)
    )
  );
}
#pop-options

type tokens_for_welcome
  (#bytes:Type0) {|crypto_bytes bytes|} (#tkt:treekem_types bytes) (#l:nat)
  (#group_id:mls_bytes bytes) (#t:treesync bytes tkt l 0)
  (asp:as_parameters bytes) (pend:pending_welcome group_id t) =
  tokens:list (option asp.token_t){
    List.Tot.length tokens == pow2 l /\ (
      forall li. match List.Tot.index pend.as_inputs li, List.Tot.index tokens li with
      | Some as_inp, Some token -> asp.credential_ok as_inp token
      | None, None -> True
      | _, _ -> False
    )
  }

val prepare_welcome:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes ->
  #l:nat ->
  group_id:mls_bytes bytes -> t:treesync bytes tkt l 0 ->
  result (pending_welcome group_id t)
let prepare_welcome #bytes #cb #tkt #l group_id t =
  if not (unmerged_leaves_ok t) then
    error "prepare_welcome: malformed unmerged leaves"
  else if not (parent_hash_invariant t) then
    error "prepare_welcome: bad parent hash"
  else if not (valid_leaves_invariant group_id t) then
    error "prepare_welcome: invalid leaves"
  else (
    let as_inputs = List.Tot.map (Option.mapTot leaf_node_to_as_input) (get_leaf_list t) in
    introduce forall (li:nat{li < pow2 l}). List.Tot.index as_inputs li == Option.mapTot leaf_node_to_as_input (leaf_at t li)
    with (
      index_get_leaf_list t li;
      index_map (Option.mapTot leaf_node_to_as_input) (get_leaf_list t) li
    );
    return ({
      can_welcome_proof = ();
      as_inputs;
      as_inputs_proof = ();
    })
  )

#push-options "--fuel 2 --ifuel 2"
val tokens_from_list:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  asp:as_parameters bytes -> l:nat -> i:tree_index l -> tokens:list (option asp.token_t){List.Tot.length tokens == pow2 l} ->
  as_tokens bytes asp.token_t l i
let rec tokens_from_list #bytes #bl asp l i tokens =
  if l = 0 then (
    let [token] = tokens in
    TLeaf token
  ) else (
    let tokens_left, tokens_right = List.Tot.splitAt (pow2 (l-1)) tokens in
    List.Pure.splitAt_length (pow2 (l-1)) tokens;
    TNode () (tokens_from_list asp _ _ tokens_left) (tokens_from_list asp _ _ tokens_right)
  )
#pop-options

#push-options "--fuel 2 --ifuel 2"
val leaf_at_token_from_list:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  asp:as_parameters bytes -> l:nat -> i:tree_index l -> tokens:list (option asp.token_t){List.Tot.length tokens == pow2 l} -> li:leaf_index l i ->
  Lemma
  (leaf_at (tokens_from_list asp l i tokens) li == List.Tot.index tokens (li-i))
let rec leaf_at_token_from_list #bytes #bl asp l i tokens li =
  if l = 0 then ()
  else (
    let tokens_left, tokens_right = List.Tot.splitAt (pow2 (l-1)) tokens in
    List.Pure.lemma_splitAt tokens tokens_left tokens_right (pow2 (l-1));
    index_append tokens_left tokens_right (li-i);
    if is_left_leaf li then
      leaf_at_token_from_list asp (l-1) (left_index i) tokens_left li
    else
      leaf_at_token_from_list asp (l-1) (right_index i) tokens_right li
  )
#pop-options

val finalize_welcome:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes -> #asp:as_parameters bytes ->
  #l:nat -> #group_id:mls_bytes bytes -> #t:treesync bytes tkt l 0 ->
  pend:pending_welcome group_id t -> tokens:tokens_for_welcome asp pend ->
  treesync_state bytes tkt asp
let finalize_welcome #bytes #cb #tkt #asp #l #group_id #t pend tokens =
  pend.can_welcome_proof;
  let tokens_tree = tokens_from_list asp l 0 tokens in
  intro_all_credentials_ok t tokens_tree (fun li ->
    pend.as_inputs_proof;
    leaf_at_token_from_list asp l 0 tokens li
  );
  ({
    group_id;
    levels = l;
    tree = t;
    tokens = tokens_tree;
  })

(*** Add ***)

let pending_add_proof
  (#bytes:Type0) {|crypto_bytes bytes|} (#tkt:treekem_types bytes) (#asp:as_parameters bytes)
  (st:treesync_state bytes tkt asp) (ln:leaf_node_nt bytes tkt) =
  squash (
    ln.data.source == LNS_key_package /\ ( //TODO: check key package signature
      match find_empty_leaf st.tree with
      | Some li ->
        tree_add_pre st.tree li /\
        leaf_is_valid ln st.group_id li
      | None ->
        find_empty_leaf_tree_extend st.tree;
        let extended_tree = tree_extend st.tree in
        let li = Some?.v (find_empty_leaf extended_tree) in
        tree_add_pre extended_tree li /\
        leaf_is_valid ln st.group_id li
    )
  )

type pending_add
  (#bytes:Type0) {|crypto_bytes bytes|} (#tkt:treekem_types bytes) (#asp:as_parameters bytes)
  (st:treesync_state bytes tkt asp) (ln:leaf_node_nt bytes tkt) =
  {
  can_add_proof: pending_add_proof st ln;
  as_input: as_input_for ln;
}

type token_for_add
  (#bytes:Type0) {|crypto_bytes bytes|} (#tkt:treekem_types bytes) (#asp:as_parameters bytes)
  (#st:treesync_state bytes tkt asp) (#ln:leaf_node_nt bytes tkt)
  (pend:pending_add st ln) =
  as_token_for asp pend.as_input

val prepare_add:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes -> #asp:as_parameters bytes ->
  st:treesync_state bytes tkt asp -> ln:leaf_node_nt bytes tkt ->
  result (pending_add st ln)
let prepare_add #bytes #cb #tkt #asp st ln =
  if not (ln.data.source = LNS_key_package) then
    error "prepare_add: source is not key_package"
  else (
    match find_empty_leaf st.tree with
    | Some li ->
      if not (tree_add_pre st.tree li) then
        error "prepare_add: tree_add_pre is false"
      else if not (leaf_is_valid ln st.group_id li) then
        error "prepare_add: invalid leaf node"
      else (
        return ({
          can_add_proof = ();
          as_input = leaf_node_to_as_input ln;
        })
      )
    | None ->
      find_empty_leaf_tree_extend st.tree;
      let extended_tree = tree_extend st.tree in
      let li = Some?.v (find_empty_leaf extended_tree) in
      if not (tree_add_pre extended_tree li) then
        error "prepare_add: tree_add_pre is false (after extension)"
      else if not (leaf_is_valid ln st.group_id li) then
        error "prepare_add: invalid leaf node"
      else (
        return ({
          can_add_proof = ();
          as_input = leaf_node_to_as_input ln;
        })
      )
  )

val finalize_add:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes -> #asp:as_parameters bytes ->
  #st:treesync_state bytes tkt asp -> #ln:leaf_node_nt bytes tkt ->
  pend:pending_add st ln -> token:token_for_add pend ->
  treesync_state bytes tkt asp & nat
let finalize_add #bytes #cb #tkt #asp #st #ln pend token =
  pend.can_add_proof;
  match find_empty_leaf st.tree with
  | Some li -> (
    all_credentials_ok_tree_add st.tree st.tokens li ln token;
    (state_update_tree st (tree_add st.tree li ln) (as_add_update st.tokens li token), (li <: nat))
  )
  | None -> (
    find_empty_leaf_tree_extend st.tree;
    let extended_tree = tree_extend st.tree in
    let extended_tokens = as_extend st.tokens in
    let li = Some?.v (find_empty_leaf extended_tree) in
    all_credentials_ok_tree_extend st.tree st.tokens;
    all_credentials_ok_tree_add extended_tree extended_tokens li ln token;
    (state_update_tree st (tree_add extended_tree li ln) (as_add_update extended_tokens li token), (li <: nat))
)

(*** Update ***)

let pending_update_proof
  (#bytes:Type0) {|crypto_bytes bytes|} (#tkt:treekem_types bytes) (#asp:as_parameters bytes)
  (st:treesync_state bytes tkt asp) (ln:leaf_node_nt bytes tkt) (li:treesync_index st) =
  squash (
    ln.data.source == LNS_update /\
    leaf_is_valid ln st.group_id li /\
    Some? (leaf_at st.tree li)
  )

type pending_update
  (#bytes:Type0) {|crypto_bytes bytes|} (#tkt:treekem_types bytes) (#asp:as_parameters bytes)
  (st:treesync_state bytes tkt asp) (ln:leaf_node_nt bytes tkt) (li:treesync_index st) =
  {
  can_update_proof: pending_update_proof st ln li;
  as_input_before: (can_update_proof; as_input_for (state_leaf_at st li));
  as_input: as_input_for ln;
}

type token_for_update
  (#bytes:Type0) {|crypto_bytes bytes|} (#tkt:treekem_types bytes) (#asp:as_parameters bytes)
  (#st:treesync_state bytes tkt asp) (#ln:leaf_node_nt bytes tkt) (#li:treesync_index st)
  (pend:pending_update st ln li) =
  token:as_token_for asp pend.as_input{asp.valid_successor pend.as_input_before pend.as_input}

val prepare_update:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes -> #asp:as_parameters bytes ->
  st:treesync_state bytes tkt asp -> ln:leaf_node_nt bytes tkt -> li:treesync_index st ->
  result (pending_update st ln li)
let prepare_update #bytes #cb #tkt #asp st ln li =
  if not (ln.data.source = LNS_update) then
    error "prepare_update: leaf node has invalid source"
  else if not (leaf_is_valid ln st.group_id li) then
    error "prepare_update: leaf node is not valid"
  else if not (Some? (leaf_at st.tree li)) then
    error "prepare_update: leaf node doesn't exists"
  else (
    return ({
      can_update_proof = ();
      as_input_before = leaf_node_to_as_input (state_leaf_at st li);
      as_input = leaf_node_to_as_input ln;
    })
  )

val finalize_update:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes -> #asp:as_parameters bytes ->
  #st:treesync_state bytes tkt asp -> #ln:leaf_node_nt bytes tkt -> #li:treesync_index st ->
  pend:pending_update st ln li -> token:token_for_update pend ->
  treesync_state bytes tkt asp
let finalize_update #bytes #cb #tkt #asp #st #ln #li pend token =
  pend.can_update_proof;
  all_credentials_ok_tree_update st.tree st.tokens li ln token;
  (state_update_tree st (tree_update st.tree li ln) (as_add_update st.tokens li token))

(*** Remove ***)

let pending_remove_proof
  (#bytes:Type0) {|crypto_bytes bytes|} (#tkt:treekem_types bytes) (#asp:as_parameters bytes)
  (st:treesync_state bytes tkt asp) (li:treesync_index st) =
  squash (
    Some? (leaf_at st.tree li)
  )

type pending_remove
  (#bytes:Type0) {|crypto_bytes bytes|} (#tkt:treekem_types bytes) (#asp:as_parameters bytes)
  (st:treesync_state bytes tkt asp) (li:treesync_index st) =
  {
  can_remove_proof: pending_remove_proof st li;
}

val prepare_remove:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes -> #asp:as_parameters bytes ->
  st:treesync_state bytes tkt asp -> li:treesync_index st ->
  result (pending_remove st li)
let prepare_remove #bytes #cb #tkt st li =
  if not (Some? (leaf_at st.tree li)) then
    error "prepare_remove: removed leaf is already blank"
  else (
    return ({
      can_remove_proof = ();
    })
  )

#push-options "--fuel 0 --ifuel 1"
val finalize_remove:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes -> #asp:as_parameters bytes ->
  #st:treesync_state bytes tkt asp -> #li:treesync_index st ->
  pend:pending_remove st li ->
  treesync_state bytes tkt asp
let finalize_remove #bytes #cb #tkt #asp #st #li pend =
  let blanked_tree = tree_remove st.tree li in
  let blanked_tokens = as_remove st.tokens li in
  all_credentials_ok_tree_remove st.tree st.tokens li;
  if TNode? blanked_tree && is_tree_empty (TNode?.right blanked_tree) then (
    all_credentials_ok_tree_truncate blanked_tree blanked_tokens;
    state_update_tree st (tree_truncate blanked_tree) (as_truncate blanked_tokens)
  ) else (
    state_update_tree st blanked_tree blanked_tokens
  )
#pop-options

(*** Commit ***)

let pending_commit_proof
  (#bytes:Type0) {|crypto_bytes bytes|} (#tkt:treekem_types bytes) (#asp:as_parameters bytes)
  (st:treesync_state bytes tkt asp) (#li:treesync_index st) (p:pathsync bytes tkt st.levels 0 li) =
  squash (
    apply_path_pre st.tree p /\
    path_is_valid st.group_id st.tree p /\
    Some? (leaf_at st.tree li)
  )

#push-options "--fuel 0 --ifuel 1 --z3rlimit 25"
type pending_commit
  (#bytes:Type0) {|crypto_bytes bytes|} (#tkt:treekem_types bytes) (#asp:as_parameters bytes)
  (st:treesync_state bytes tkt asp) (#li:treesync_index st) (p:pathsync bytes tkt st.levels 0 li) =
  {
  can_commit_proof: pending_commit_proof st p;
  as_input_before: (can_commit_proof; as_input_for (state_leaf_at st li));
  as_input: as_input_for (get_path_leaf p);
}
#pop-options

type token_for_commit
  (#bytes:Type0) {|crypto_bytes bytes|} (#tkt:treekem_types bytes) (#asp:as_parameters bytes)
  (#st:treesync_state bytes tkt asp) (#li:treesync_index st) (#p:pathsync bytes tkt st.levels 0 li)
  (pend:pending_commit st p) =
  token:as_token_for asp pend.as_input{asp.valid_successor pend.as_input_before pend.as_input}

val prepare_commit:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes -> #asp:as_parameters bytes ->
  st:treesync_state bytes tkt asp -> #li:treesync_index st -> p:pathsync bytes tkt st.levels 0 li ->
  result (pending_commit st p)
let prepare_commit #bytes #cb #tkt #asp st #li p =
  if not (apply_path_pre st.tree p) then
    error "prepare_commit: bad precondition"
  else if not (path_is_valid st.group_id st.tree p) then
    error "prepare_commit: invalid path"
  else if not (Some? (leaf_at st.tree li)) then
    error "prepare_commit: comitter is blank"
  else (
    return ({
      can_commit_proof = ();
      as_input_before = leaf_node_to_as_input (state_leaf_at st li);
      as_input = leaf_node_to_as_input (get_path_leaf p);
    })
  )

#push-options "--fuel 0 --ifuel 1"
val finalize_commit:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes -> #asp:as_parameters bytes ->
  #st:treesync_state bytes tkt asp -> #li:treesync_index st -> #p:pathsync bytes tkt st.levels 0 li ->
  pend:pending_commit st p -> token:token_for_commit pend ->
  treesync_state bytes tkt asp
let finalize_commit #bytes #cb #tkt #asp #st #li #p pend token =
  pend.can_commit_proof;
  all_credentials_ok_apply_path st.tree st.tokens p token;
  state_update_tree st (apply_path st.tree p) (as_add_update st.tokens li token)
#pop-options

(*** Weaken ***)

val weaken_asp:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes -> #asp:as_parameters bytes ->
  asp_weak:as_parameters bytes{as_parameters_weaker asp asp_weak} -> treesync_state bytes tkt asp ->
  treesync_state bytes tkt asp_weak
let weaken_asp #bytes #cb #tkt #asp asp_weak st =
  { st with
    tokens = all_credentials_ok_weaken asp_weak st.tree st.tokens;
  }
