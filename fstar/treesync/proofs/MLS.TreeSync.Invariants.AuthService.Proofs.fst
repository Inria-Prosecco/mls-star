module MLS.TreeSync.Invariants.AuthService.Proofs

open Comparse
open MLS.Crypto
open MLS.Tree
open MLS.TreeCommon
open MLS.TreeCommon.Lemmas
open MLS.TreeSync.NetworkTypes
open MLS.TreeSync.Types
open MLS.TreeSync.Operations
open MLS.TreeSync.Operations.Lemmas
open MLS.TreeSync.Invariants.AuthService

#set-options "--fuel 1 --ifuel 1"

val intro_all_credentials_ok:
  #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes -> #asp:as_parameters bytes ->
  #l:nat -> #i:tree_index l ->
  ts:treesync bytes tkt l i -> ast:as_tokens bytes asp.token_t l i -> (li:leaf_index l i -> squash (one_credential_ok ts ast li)) ->
  squash (all_credentials_ok ts ast)
let intro_all_credentials_ok #bytes #bl #tkt #asp #l #i ts ast one_proof =
  introduce forall li. one_credential_ok ts ast li
  with one_proof li

(*** Invariant theorems ***)

val all_credentials_ok_tree_create:
  #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes -> #asp:as_parameters bytes ->
  ln:leaf_node_nt bytes tkt -> token:asp.token_t ->
  Lemma
  (requires asp.credential_ok (ln.data.signature_key, ln.data.credential) token)
  (ensures all_credentials_ok (tree_create (Some ln)) (tree_create (Some token)))
let all_credentials_ok_tree_create #bytes #bl #tkt ln token = ()

val all_credentials_ok_tree_add:
  #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes -> #asp:as_parameters bytes ->
  #l:nat -> #i:tree_index l ->
  ts:treesync bytes tkt l i -> ast:as_tokens bytes asp.token_t l i -> li:leaf_index l i -> ln:leaf_node_nt bytes tkt -> token:asp.token_t ->
  Lemma
  (requires
    asp.credential_ok (ln.data.signature_key, ln.data.credential) token /\
    all_credentials_ok ts ast /\
    tree_add_pre ts li
  )
  (ensures all_credentials_ok (tree_add ts li ln) (as_add_update ast li token))
let all_credentials_ok_tree_add #bytes #bl #tkt #asp #l #i ts ast li ln token =
  intro_all_credentials_ok (tree_add ts li ln) (as_add_update ast li token) (fun li' ->
    leaf_at_tree_add ts li ln li';
    leaf_at_tree_change_path ast li (Some token) () li'
  )

val all_credentials_ok_tree_update:
  #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes -> #asp:as_parameters bytes ->
  #l:nat -> #i:tree_index l ->
  ts:treesync bytes tkt l i -> ast:as_tokens bytes asp.token_t l i -> li:leaf_index l i -> ln:leaf_node_nt bytes tkt -> token:asp.token_t ->
  Lemma
  (requires
    asp.credential_ok (ln.data.signature_key, ln.data.credential) token /\
    all_credentials_ok ts ast
  )
  (ensures all_credentials_ok (tree_update ts li ln) (as_add_update ast li token))
let all_credentials_ok_tree_update #bytes #bl #tkt #asp #l #i ts ast li ln token =
  intro_all_credentials_ok (tree_update ts li ln) (as_add_update ast li token) (fun li' ->
    leaf_at_tree_update ts li ln li';
    leaf_at_tree_change_path ast li (Some token) () li'
  )

val all_credentials_ok_tree_remove:
  #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes -> #asp:as_parameters bytes ->
  #l:nat -> #i:tree_index l ->
  ts:treesync bytes tkt l i -> ast:as_tokens bytes asp.token_t l i -> li:leaf_index l i ->
  Lemma
  (requires all_credentials_ok ts ast)
  (ensures all_credentials_ok (tree_remove ts li) (as_remove ast li))
let all_credentials_ok_tree_remove #bytes #bl #tkt #asp #l #i ts ast li =
  intro_all_credentials_ok (tree_remove ts li) (as_remove ast li) (fun li' ->
    leaf_at_tree_remove ts li li';
    leaf_at_tree_change_path ast li None () li'
  )

val all_credentials_ok_apply_path:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes -> #asp:as_parameters bytes ->
  #l:nat -> #li:leaf_index l 0 ->
  ts:treesync bytes tkt l 0 -> ast:as_tokens bytes asp.token_t l 0 -> p:pathsync bytes tkt l 0 li -> token:asp.token_t ->
  Lemma
  (requires
    asp.credential_ok ((get_path_leaf p).data.signature_key, (get_path_leaf p).data.credential) token /\
    all_credentials_ok ts ast /\
    apply_path_pre ts p
  )
  (ensures all_credentials_ok (apply_path ts p) (as_add_update ast li token))
let all_credentials_ok_apply_path #bytes #cb #tkt #asp #l #li ts ast p token =
  intro_all_credentials_ok (apply_path ts p) (as_add_update ast li token) (fun li' ->
    leaf_at_apply_path ts p li';
    leaf_at_tree_change_path ast li (Some token) () li'
  )

val all_credentials_ok_left_right:
  #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes -> #asp:as_parameters bytes ->
  #l:pos -> #i:tree_index l ->
  ts:treesync bytes tkt l i -> ast:as_tokens bytes asp.token_t l i ->
  Lemma
  (requires all_credentials_ok ts ast)
  (ensures (
    let TNode _ ts_left ts_right, TNode _ ast_left ast_right = ts, ast in
    all_credentials_ok ts_left ast_left /\ all_credentials_ok ts_right ast_right
  ))
let all_credentials_ok_left_right #bytes #bl #tkt #asp #l #i ts ast =
  let TNode _ ts_left ts_right, TNode _ ast_left ast_right = ts, ast in
  intro_all_credentials_ok ts_left ast_left (fun li ->
    assert(one_credential_ok ts ast li);
    assert(leaf_at ts_left li == leaf_at ts li);
    assert(leaf_at ast_left li == leaf_at ast li)
  );
  intro_all_credentials_ok ts_right ast_right (fun li ->
    assert(one_credential_ok ts ast li);
    assert(leaf_at ts_right li == leaf_at ts li);
    assert(leaf_at ast_right li == leaf_at ast li)
  )

val all_credentials_ok_tree_truncate:
  #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes -> #asp:as_parameters bytes ->
  #l:pos ->
  ts:treesync bytes tkt l 0 -> ast:as_tokens bytes asp.token_t l 0 ->
  Lemma
  (requires all_credentials_ok ts ast /\ is_tree_empty (TNode?.right ts))
  (ensures all_credentials_ok (tree_truncate ts) (as_truncate ast))
let all_credentials_ok_tree_truncate #bytes #bl #tkt #asp #l ts ast =
  all_credentials_ok_left_right ts ast

val all_credentials_ok_tree_extend:
  #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes -> #asp:as_parameters bytes ->
  #l:nat ->
  ts:treesync bytes tkt l 0 -> ast:as_tokens bytes asp.token_t l 0 ->
  Lemma
  (requires all_credentials_ok ts ast)
  (ensures all_credentials_ok (tree_extend ts) (as_extend ast))
let all_credentials_ok_tree_extend #bytes #bl #tkt #asp #l ts ast =
  intro_all_credentials_ok (tree_extend ts) (as_extend ast) (fun li ->
    leaf_at_tree_extend ts li;
    if li < pow2 l then (
      let li: leaf_index l 0 = li in //helps with forall instantiation in `all_credentials_ok`
      assert(leaf_at (tree_extend ts) li == leaf_at ts li);
      assert(leaf_at (as_extend ast) li == leaf_at ast li)
    ) else (
      leaf_at_mk_blank_tree_general l (right_index #(l+1) 0) (None <: option asp.token_t) () li
    )
  )

(*** Weakening theorem ***)

val as_parameters_weaker:
  #bytes:Type0 -> {|bytes_like bytes|} ->
  as_parameters bytes -> as_parameters bytes ->
  prop
let as_parameters_weaker #bytes #bl as_strong as_weak =
  as_strong.token_t == as_weak.token_t /\
  (forall vk cred token. as_strong.credential_ok (vk, cred) token ==> as_weak.credential_ok (vk, cred) token)

val all_credentials_ok_weaken:
  #bytes:Type0 -> {|bytes_like bytes|} -> #tkt:treekem_types bytes -> #asp_strong:as_parameters bytes ->
  #l:nat -> #i:tree_index l ->
  asp_weak:as_parameters bytes -> ts:treesync bytes tkt l i -> ast:as_tokens bytes asp_strong.token_t l i ->
  Pure (as_tokens bytes asp_weak.token_t l i)
  (requires all_credentials_ok ts ast /\ as_parameters_weaker asp_strong asp_weak)
  (ensures fun res -> all_credentials_ok ts res)
let all_credentials_ok_weaken #bytes #bl #tkt #asp_strong #l #i asp_weak ts ast =
  ast
