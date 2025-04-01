module MLS.TreeKEM.Symbolic.Tree.Labels

open Comparse
open DY.Core
open DY.Lib
open MLS.Crypto
open MLS.Tree
open MLS.TreeCommon
open MLS.NetworkTypes
open MLS.TreeSync.NetworkTypes
open MLS.TreeSync.Types
open MLS.TreeSync.Operations { leaf_is_valid }
open MLS.TreeSync.Invariants.ParentHash { node_not_blank }
open MLS.TreeSync.Invariants.AuthService { as_tokens }
open MLS.TreeSync.Symbolic.LeafNodeSignature
open MLS.TreeSync.Symbolic.AuthService.CredentialInterpretation
open MLS.TreeSync.Symbolic.AuthService
open MLS.TreeSync.Symbolic.State.SignatureKey
open MLS.TreeKEM.NetworkTypes
open MLS.Symbolic
open MLS.Symbolic.Lemmas
open MLS.Symbolic.Labels.Guard
open MLS.Symbolic.Labels.Event
open MLS.Symbolic.Labels.Big
open MLS.Bootstrap.Symbolic.KeyPackage
open MLS.TreeKEM.Symbolic.State.NodeKey
open MLS.TreeSync.Proofs.ParentHashGuarantees { canonicalize_unmerged_leaves }

open MLS.TreeSync.Symbolic.Event.LeafNodeHasBeenVerified
open MLS.TreeSync.Proofs.ParentHashGuarantees
open MLS.TreeSync.Invariants.UnmergedLeaves
open MLS.TreeSync.Invariants.ParentHash
open MLS.TreeSync.Invariants.ParentHash.Proofs
open MLS.TreeSync.Invariants.AuthService
open MLS.TreeSync.Invariants.ValidLeaves
open MLS.TreeSync.Operations
open MLS.MiscLemmas
open MLS.Tree.Lemmas

#set-options "--fuel 1 --ifuel 1"

(*** Path secret stuff ***)

[@@ with_bytes bytes]
type one_path_secret_usage = {
  l: nat;
  i: tree_index l;
  [@@@ with_parser #bytes (MLS.TreeSync.Symbolic.Parsers.ps_treesync tkt l i)]
  t: treesync bytes tkt l i;
  group_id: mls_bytes bytes;
  committer_leaf_index: nat;
}

%splice [ps_one_path_secret_usage] (gen_parser (`one_path_secret_usage))

type path_secret_usage = list one_path_secret_usage

instance parseable_serializeable_path_secret_usage: parseable_serializeable bytes path_secret_usage =
  mk_parseable_serializeable_from_whole (ps_whole_list ps_one_path_secret_usage)

val is_root_node_pk: {|crypto_invariants|} -> trace -> bytes -> prop
let is_root_node_pk #cinvs tr node_pk =
  exists path_secret node_sk.
    length node_pk == hpke_public_key_length #bytes /\
    MLS.TreeKEM.Operations.derive_keypair_from_path_secret path_secret == MLS.Result.Success (node_sk, node_pk) /\
    bytes_invariant tr path_secret /\
    path_secret `has_usage tr` (KdfExpandKey "MLS.PathSecret" (serialize path_secret_usage []))

(*** Leaf node verification event label ***)

val principal_leaf_node_has_been_verified_label:
  leaf_node_nt bytes tkt -> mls_bytes bytes -> nat ->
  principal ->
  label
let principal_leaf_node_has_been_verified_label leaf_node group_id leaf_index prin =
  event_triggered_label prin {leaf_node; group_id; leaf_index}

val leaf_node_has_been_verified_label:
  leaf_node_nt bytes tkt -> mls_bytes bytes -> nat ->
  label
let leaf_node_has_been_verified_label leaf_node group_id leaf_index =
  big_join (principal_leaf_node_has_been_verified_label leaf_node group_id leaf_index)

val guarded_signature_key_label:
  leaf_node_nt bytes tkt -> mls_bytes bytes -> nat ->
  label
let guarded_signature_key_label leaf_node group_id leaf_index =
  match credential_to_principal leaf_node.data.credential with
  | None -> DY.Core.Label.Unknown.unknown_label
  | Some prin ->
    guard
      (signature_key_label prin leaf_node.data.signature_key)
      (leaf_node_has_been_verified_label leaf_node group_id leaf_index)

val get_node_content:
  #l:nat -> #i:tree_index l ->
  t:treesync bytes tkt l i{node_not_blank t} ->
  hpke_public_key_nt bytes
let get_node_content #l #i t =
  match t with
  | TLeaf (Some ln) -> ln.data.content
  | TNode (Some pn) _ _ -> pn.content

type node_label_type =
  | NoCommitter: nat -> node_label_type
  | NoCommitterSignature: nat -> node_label_type
  | YesCommitter: node_label_type

val node_sk_label_aux_leaf:
  leaf_node_nt bytes tkt -> mls_bytes bytes -> node_label_type -> nat ->
  label
let node_sk_label_aux_leaf ln group_id ty i =
  if ty = NoCommitter i then secret
  else (
    let sig_label =
      if ty = NoCommitterSignature i then secret
      else (guarded_signature_key_label ln group_id i)
    in
    match credential_to_principal ln.data.credential with
    | None -> DY.Core.Label.Unknown.unknown_label
    | Some prin -> (
      match ln.data.source with
      | LNS_key_package ->
        join
          sig_label
          (join
            (node_key_label prin ln.data.content)
            (init_key_associated_with ln)
          )
      | LNS_update
      | LNS_commit ->
        join
          sig_label
          (node_key_label prin ln.data.content)
    )
  )

val node_sk_label_aux:
  #l:nat -> #i:tree_index l ->
  treesync bytes tkt l i -> mls_bytes bytes -> node_label_type ->
  label
let rec node_sk_label_aux #l #i t group_id ty =
  match t with
  | TLeaf None -> secret
  | TLeaf (Some ln) -> node_sk_label_aux_leaf ln group_id ty i
  | TNode opt_pn left right ->
    join
      (node_sk_label_aux left group_id ty)
      (node_sk_label_aux right group_id ty)

val node_sk_label_nocommitter:
  #l:nat -> #i:tree_index l ->
  treesync bytes tkt l i -> mls_bytes bytes -> nat ->
  label
let node_sk_label_nocommitter #l #i t group_id li =
  node_sk_label_aux t group_id (NoCommitter li)

val node_sk_label_nosig:
  #l:nat -> #i:tree_index l ->
  treesync bytes tkt l i -> mls_bytes bytes -> nat ->
  label
let node_sk_label_nosig #l #i t group_id li =
  node_sk_label_aux t group_id (NoCommitterSignature li)

val node_sk_label:
  #l:nat -> #i:tree_index l ->
  treesync bytes tkt l i -> mls_bytes bytes ->
  label
let node_sk_label #l #i t group_id =
  node_sk_label_aux t group_id YesCommitter

val node_sk_label_canon_nosig:
  #l:nat -> #i:tree_index l ->
  treesync bytes tkt l i -> mls_bytes bytes -> nat ->
  label
let node_sk_label_canon_nosig #l #i t group_id li =
  node_sk_label_aux (canonicalize_unmerged_leaves t) group_id (NoCommitterSignature li)

val node_sk_label_canon:
  #l:nat -> #i:tree_index l ->
  treesync bytes tkt l i -> mls_bytes bytes ->
  label
let node_sk_label_canon #l #i t group_id =
  node_sk_label_aux (canonicalize_unmerged_leaves t) group_id YesCommitter

(*** Corruption lemmas ***)

val guarded_signature_key_label_is_corrupt:
  tr:trace -> me:principal ->
  leaf_node:leaf_node_nt bytes tkt -> group_id:mls_bytes bytes -> leaf_index:nat ->
  Lemma
  (requires
    is_corrupt tr (guarded_signature_key_label leaf_node group_id leaf_index) /\
    Some? (credential_to_principal leaf_node.data.credential) /\
    i_have_verified_leaf_node tr me leaf_node group_id leaf_index
  )
  (ensures (
    let Some prin = (credential_to_principal leaf_node.data.credential) in
    is_corrupt (prefix tr (find_event_triggered_at_timestamp tr me {leaf_node; group_id; leaf_index})) (signature_key_label prin leaf_node.data.signature_key)
  ))
let guarded_signature_key_label_is_corrupt tr me leaf_node group_id leaf_index =
  let Some prin = (credential_to_principal leaf_node.data.credential) in
  introduce forall tr. (leaf_node_has_been_verified_label leaf_node group_id leaf_index) `can_flow tr` (principal_leaf_node_has_been_verified_label leaf_node group_id leaf_index me) with (
    big_join_flow_to_component tr (principal_leaf_node_has_been_verified_label leaf_node group_id leaf_index) me
  );
  guard_can_flow tr (signature_key_label prin leaf_node.data.signature_key) (signature_key_label prin leaf_node.data.signature_key) (principal_leaf_node_has_been_verified_label leaf_node group_id leaf_index me) (leaf_node_has_been_verified_label leaf_node group_id leaf_index);
  is_corrupt_guard_event tr (signature_key_label prin leaf_node.data.signature_key) me {leaf_node; group_id; leaf_index}

(*** Event invariants (link with TreeSync) ***)

val group_has_tree_event_pred: {|crypto_invariants|} -> event_predicate (group_has_tree_event bytes tkt)
let group_has_tree_event_pred #cinvs =
  fun tr prin {group_id; authentifier_leaf_index; l; i; t} ->
    node_not_blank t /\
    bytes_invariant tr (get_node_content t) /\
    node_sk_label_canon_nosig t group_id authentifier_leaf_index `can_flow tr` (get_hpke_sk_label tr (get_node_content t)) /\
    (get_node_content t) `has_hpke_sk_usage tr` node_key_usage /\
    ((1 <= l /\ get_parent_hash_of t == MLS.TreeSync.ParentHash.root_parent_hash #bytes) ==> is_root_node_pk tr (get_node_content t))

val has_group_has_tree_event_invariant:
  {|protocol_invariants|} ->
  prop
let has_group_has_tree_event_invariant #invs =
  has_event_pred group_has_tree_event_pred

val group_has_tree_event_tag_and_invariant: {|crypto_invariants|} -> (string & compiled_event_predicate)
let group_has_tree_event_tag_and_invariant #cinvs =
  ((event_group_has_tree_event tkt).tag, compile_event_pred group_has_tree_event_pred)

val leaf_node_signed_event_pred: {|crypto_invariants|} -> event_predicate (leaf_node_signed_event tkt)
let leaf_node_signed_event_pred #cinvs =
  fun tr prin { ln_tbs } ->
    match ln_tbs.data.source with
    | LNS_key_package -> (
      bytes_invariant tr ln_tbs.data.content /\
      (node_key_label prin ln_tbs.data.content) `can_flow tr` (get_hpke_sk_label tr ln_tbs.data.content) /\
      ln_tbs.data.content `has_hpke_sk_usage tr` node_key_usage
    )
    | _ -> True

val has_leaf_node_signed_event_invariant:
  {|protocol_invariants|} ->
  prop
let has_leaf_node_signed_event_invariant #invs =
  has_event_pred leaf_node_signed_event_pred

val leaf_node_signed_event_tag_and_invariant: {|crypto_invariants|} -> (string & compiled_event_predicate)
let leaf_node_signed_event_tag_and_invariant #cinvs =
  ((event_leaf_node_signed_event tkt).tag, compile_event_pred leaf_node_signed_event_pred)

val has_treesync_treekem_link_invariants:
  {|protocol_invariants|} ->
  prop
let has_treesync_treekem_link_invariants #invs =
  has_leaf_node_tbs_invariant tkt /\
  has_leaf_node_has_been_verified_invariant tkt /\
  has_group_has_tree_event_invariant /\
  has_leaf_node_signed_event_invariant

(*** Main property established by this module ***)

val node_key_good:
  {|crypto_invariants|} ->
  #l:nat -> #i:tree_index l ->
  tr:trace ->
  t:treesync bytes tkt l i{node_not_blank t} -> group_id:mls_bytes bytes ->
  prop
let node_key_good #cinvs #l #i tr t group_id =
  bytes_invariant tr (get_node_content t) /\
  node_sk_label_canon t group_id `can_flow tr` (get_hpke_sk_label tr (get_node_content t)) /\ (
    (
      (get_node_content t) `has_hpke_sk_usage tr` node_key_usage /\
      ((1 <= l /\ get_parent_hash_of t == MLS.TreeSync.ParentHash.root_parent_hash #bytes) ==> is_root_node_pk tr (get_node_content t))
    ) \/ (
      node_sk_label_canon t group_id `can_flow tr` public
    )
  )

val all_tree_keys_good:
  {|crypto_invariants|} ->
  #l:nat -> #i:tree_index l ->
  treesync bytes tkt l i ->
  mls_bytes bytes -> trace ->
  prop
let rec all_tree_keys_good #cinvs #l #i t group_id tr =
  match t with
  | TLeaf None -> True
  | TLeaf (Some ln) ->
    node_key_good tr t group_id
  | TNode opt_pn left right ->
    let opt_pn_ok =
      match opt_pn with
      | None -> True
      | Some pn -> (
        node_key_good tr t group_id
      )
    in
    opt_pn_ok /\ all_tree_keys_good left group_id tr /\ all_tree_keys_good right group_id tr

(*** Proofs ***)

#push-options "--fuel 1 --ifuel 2"
val tree_list_is_parent_hash_linkedP_unmerged_leaves_eq:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes ->
  tl:tree_list bytes tkt ->
  x:nat ->
  Lemma
  (requires
    Cons? tl /\
    tree_list_is_parent_hash_linkedP tl /\ (
    let (|_, _, last|) = List.Tot.last tl in
    unmerged_leaves_ok last
  ))
  (ensures (
    let (|_, _, first|) = List.Tot.hd tl in
    let (|_, _, last|) = List.Tot.last tl in
    (mem_ul x (unmerged_leaves_of first) <==> (mem_ul x (unmerged_leaves_of last) /\ leaf_index_inside_tree first x)) /\
    is_subtree_of first last
  ))
let rec tree_list_is_parent_hash_linkedP_unmerged_leaves_eq #bytes #cb #tkt tl x =
  match tl with
  | [(|l, i, t|)] -> (
    mem_ul_eq x (unmerged_leaves_of t);
    list_for_all_eq (unmerged_leaf_exists t) (unmerged_leaves_of t)
  )
  | (|l1, i1, first|)::(|l2, i2, second|)::t -> (
    tree_list_is_parent_hash_linkedP_unmerged_leaves_eq ((|_, _, second|)::t) x;
    last_update_unmerged_leaves_eq first second x;
    introduce leaf_index_inside l1 i1 x ==> leaf_index_inside l2 i2 x with _. (
      leaf_index_inside_subtree l1 l2 i1 i2 x
    );
    let (|_, _, last|) = List.Tot.last tl in
    is_subtree_of_transitive first second last
  )
#pop-options

val authentifier_index_is_not_unmerged:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l ->
  t:treesync bytes tkt l i ->
  Lemma
  (requires
    unmerged_leaves_ok t /\
    parent_hash_invariant t /\
    node_has_parent_hash t
  )
  (ensures (
    let authentifier_leaf_index = get_authentifier_index t in
    ~(mem_ul (get_authentifier_index t) (unmerged_leaves_of t)) /\
    (Some?.v (leaf_at t authentifier_leaf_index)).data.source == LNS_commit
  ))
let authentifier_index_is_not_unmerged #bytes #cb #tkt #l #i t =
  let tl = parent_hash_invariant_to_tree_list t in
  tree_list_is_parent_hash_linkedP_unmerged_leaves_eq tl (get_authentifier_index t);
  let (|_, li, first|) = List.Tot.hd tl in
  let (|_, _, last|) = List.Tot.last tl in
  leaf_at_subtree_leaf first last

val unmerged_leaf_exists_un_add:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l ->
  t:treesync bytes tkt l i -> excluded_leaves:list (nat_lbytes 4) ->
  x:leaf_index l i ->
  Lemma
  (requires
    ~(mem_ul x excluded_leaves)
  )
  (ensures
    leaf_at (un_add t excluded_leaves) x == leaf_at t x
  )
let rec unmerged_leaf_exists_un_add #bytes #cb #tkt #l #i t excluded_leaves x =
  match t with
  | TLeaf _ -> ()
  | TNode _ left right -> (
    let x: leaf_index l i = x in
    if is_left_leaf x then (
      unmerged_leaf_exists_un_add left excluded_leaves x
    ) else (
      unmerged_leaf_exists_un_add right excluded_leaves x
    )
  )

val authentifier_index_is_in_canonicalization:
  #bytes:Type0 -> {|crypto_bytes bytes|} -> #tkt:treekem_types bytes ->
  #l:nat -> #i:tree_index l ->
  t:treesync bytes tkt l i ->
  Lemma
  (requires
    unmerged_leaves_ok t /\
    parent_hash_invariant t /\
    node_has_parent_hash t
  )
  (ensures (
    let authentifier_leaf_index = get_authentifier_index t in
    leaf_at (canonicalize_unmerged_leaves t) authentifier_leaf_index == leaf_at t authentifier_leaf_index /\
    (Some?.v (leaf_at t authentifier_leaf_index)).data.source == LNS_commit
  ))
let authentifier_index_is_in_canonicalization #bytes #cb #tkt #l #i t =
  let authentifier_leaf_index = get_authentifier_index t in
  match t with
  | TLeaf _ -> ()
  | TNode None _ _ -> ()
  | TNode (Some content) _ _ -> (
    authentifier_index_is_not_unmerged t;
    unmerged_leaf_exists_un_add t (unmerged_leaves_of t) authentifier_leaf_index
  )

val node_sk_label_aux_flows_to_node_sk_label_aux_leaf:
  #l:nat -> #i:tree_index l ->
  t:treesync bytes tkt l i -> group_id:mls_bytes bytes -> ty:node_label_type ->
  li:leaf_index l i ->
  tr:trace ->
  Lemma (
    node_sk_label_aux t group_id ty `can_flow tr` (
      match leaf_at t li with
      | None -> secret
      | Some ln -> node_sk_label_aux_leaf ln group_id ty li
    )
  )
let rec node_sk_label_aux_flows_to_node_sk_label_aux_leaf #l #i t group_id ty li tr =
  if l = 0 then ()
  else (
    let (child, _) = get_child_sibling t li in
    node_sk_label_aux_flows_to_node_sk_label_aux_leaf child group_id ty li tr
  )

val node_sk_label_flows_to_node_sk_label_nosig:
  #l:nat -> #i:tree_index l ->
  t:treesync bytes tkt l i -> group_id:mls_bytes bytes ->
  committer_leaf_index:nat ->
  tr:trace ->
  Lemma (
    node_sk_label t group_id `can_flow tr` node_sk_label_nosig t group_id committer_leaf_index
  )
let rec node_sk_label_flows_to_node_sk_label_nosig #l #i t group_id committer_leaf_index tr =
  match t with
  | TLeaf None -> ()
  | TLeaf (Some ln) -> ()
  | TNode _ left right ->
    node_sk_label_flows_to_node_sk_label_nosig left group_id committer_leaf_index tr;
    node_sk_label_flows_to_node_sk_label_nosig right group_id committer_leaf_index tr

val node_sk_label_flows_to_node_sk_label_without_committer:
  #l:nat -> #i:tree_index l ->
  t:treesync bytes tkt l i -> group_id:mls_bytes bytes ->
  committer_leaf_index:nat ->
  tr:trace ->
  Lemma (
    node_sk_label_canon t group_id `can_flow tr` node_sk_label_canon_nosig t group_id committer_leaf_index
  )
let node_sk_label_flows_to_node_sk_label_without_committer #l #i t group_id committer_leaf_index tr =
  node_sk_label_flows_to_node_sk_label_nosig (canonicalize_unmerged_leaves t) group_id committer_leaf_index tr

val canonicalize_preserves_node_content:
  #l:nat -> #i:tree_index l ->
  t:treesync bytes tkt l i -> li:leaf_index l i ->
  Lemma
  (requires
    node_not_blank t
  )
  (ensures (
    let ct = canonicalize t li in
    node_not_blank ct /\
    get_node_content ct == get_node_content t
  ))
let canonicalize_preserves_node_content #l #i t li =
  match t with
  | TLeaf (Some _) -> ()
  | TNode (Some _) _ _ -> ()

val canonicalize_preserves_node_sk_label_nosig:
  #l:nat -> #i:tree_index l ->
  t:treesync bytes tkt l i -> group_id:mls_bytes bytes ->
  committer_leaf_index:leaf_index l i ->
  Lemma
  (requires
    Some? (leaf_at t committer_leaf_index) /\
    (Some?.v (leaf_at t committer_leaf_index)).data.source == LNS_commit
  )
  (ensures
    node_sk_label_nosig (canonicalize_leaf_signature t committer_leaf_index) group_id committer_leaf_index == node_sk_label_nosig t group_id committer_leaf_index
  )
let rec canonicalize_preserves_node_sk_label_nosig #l #i t group_id committer_leaf_index =
  match t with
  | TLeaf _ -> ()
  | TNode opt_pn left right -> (
    let (child, _) = get_child_sibling t committer_leaf_index in
    canonicalize_preserves_node_sk_label_nosig child group_id committer_leaf_index
  )

val canonicalize_preserves_node_sk_label_without_committer:
  #l:nat -> #i:tree_index l ->
  t:treesync bytes tkt l i -> group_id:mls_bytes bytes ->
  li:leaf_index l i ->
  Lemma
  (requires
    Some? (leaf_at (canonicalize_unmerged_leaves t) li) /\
    (Some?.v (leaf_at (canonicalize_unmerged_leaves t) li)).data.source == LNS_commit
  )
  (ensures
    node_sk_label_canon_nosig (canonicalize t li) group_id li == node_sk_label_canon_nosig t group_id li
  )
let canonicalize_preserves_node_sk_label_without_committer #l #i t group_id li =
  un_add_myself (unmerged_leaves_of t);
  canonicalize_unmerged_leaves_idempotent (canonicalize t li);
  canonicalize_preserves_node_sk_label_nosig (canonicalize_unmerged_leaves t) group_id li

#push-options "--fuel 0 --ifuel 0 --z3rlimit 25"
val all_tree_keys_good_parent_hash_case:
  {|protocol_invariants|} ->
  #l:nat -> #i:tree_index l ->
  tr:trace -> me:principal ->
  t:treesync bytes tkt l i -> ast:as_tokens bytes (dy_asp tr).token_t l i -> group_id:mls_bytes bytes ->
  Lemma
  (requires
    i_have_verified_every_leaf_node tr me t group_id /\
    node_has_parent_hash t /\
    unmerged_leaves_ok t /\
    parent_hash_invariant t /\
    MLS.TreeSync.Invariants.ValidLeaves.valid_leaves_invariant group_id t /\
    MLS.TreeSync.Invariants.AuthService.all_credentials_ok t ast /\
    is_well_formed _ (bytes_invariant tr) (Some?.v (leaf_at t (get_authentifier_index t))) /\
    bytes_invariant tr group_id /\
    trace_invariant tr /\
    has_treesync_treekem_link_invariants
  )
  (ensures
    node_sk_label_canon t group_id `can_flow tr` (get_hpke_sk_label tr (get_node_content t)) /\ (
      (
        (get_node_content t) `has_hpke_sk_usage tr` node_key_usage /\
        ((1 <= l /\ get_parent_hash_of t == MLS.TreeSync.ParentHash.root_parent_hash #bytes) ==> is_root_node_pk tr (get_node_content t))
      ) \/ (
        node_sk_label_canon t group_id `can_flow tr` public
      )
    )
  )
let all_tree_keys_good_parent_hash_case #invs #l #i tr me t ast group_id =
  let authentifier_leaf_index = get_authentifier_index t in
  MLS.TreeSync.Invariants.AuthService.Proofs.elim_all_credentials_ok t ast authentifier_leaf_index;
  let authentifier_leaf_node = Some?.v (leaf_at t authentifier_leaf_index) in
  let authentifier = Some?.v (credential_to_principal authentifier_leaf_node.data.credential) in
  let authentifier_has_been_verified_event = {leaf_node = authentifier_leaf_node; group_id; leaf_index = authentifier_leaf_index} in
  let li = get_authentifier_index t in
  is_corrupt_event_triggered_label tr me authentifier_has_been_verified_event;
  big_join_flow_to_component tr (principal_leaf_node_has_been_verified_label authentifier_leaf_node group_id authentifier_leaf_index) me;
  leaf_at_i_have_verified_every_leaf_node tr me t group_id authentifier_leaf_index;
  assert(is_corrupt tr (leaf_node_has_been_verified_label authentifier_leaf_node group_id authentifier_leaf_index));

  node_sk_label_flows_to_node_sk_label_without_committer t group_id authentifier_leaf_index tr;
  authentifier_index_is_in_canonicalization t;
  node_sk_label_aux_flows_to_node_sk_label_aux_leaf (canonicalize_unmerged_leaves t) group_id YesCommitter authentifier_leaf_index tr;
  guard_authentication_lemma tr (signature_key_label authentifier authentifier_leaf_node.data.signature_key) (leaf_node_has_been_verified_label authentifier_leaf_node group_id authentifier_leaf_index)
    (fun tr_ev -> exists p. leaf_node_has_been_verified_pred tr_ev p authentifier_has_been_verified_event)
    (fun tr_ev ->
      trace_invariant_before tr_ev tr
    )
    (fun tr_before_ev ->
      bytes_well_formed tr_before_ev (get_node_content t) /\
      node_sk_label_canon_nosig t group_id authentifier_leaf_index `can_flow tr_before_ev` (get_hpke_sk_label tr_before_ev (get_node_content t)) /\
      (get_node_content t) `has_hpke_sk_usage tr_before_ev` node_key_usage /\
      ((1 <= l /\ get_parent_hash_of t == MLS.TreeSync.ParentHash.root_parent_hash #bytes) ==> is_root_node_pk tr (get_node_content t))
    )
    (fun tr_before_ev ->
      trace_invariant_before tr_before_ev tr;
      eliminate exists as_token. (dy_asp tr_before_ev).credential_ok (leaf_node_to_as_input authentifier_leaf_node) as_token
      returns _
      with _. (
        parent_hash_implies_event tr_before_ev group_id t as_token;
        canonicalize_preserves_node_content t authentifier_leaf_index;
        canonicalize_preserves_node_sk_label_without_committer t group_id authentifier_leaf_index;
        assert((get_node_content t) == (get_node_content (canonicalize t authentifier_leaf_index)));
        assert(1 <= l ==> (node_has_parent_hash t == node_has_parent_hash (canonicalize t authentifier_leaf_index)) /\ (get_parent_hash_of t) == (get_parent_hash_of (canonicalize t authentifier_leaf_index)))
        by (let open FStar.Tactics in set_fuel 1; set_ifuel 0);
        ()
      )
    )
#pop-options

#push-options "--z3rlimit 50"
val all_tree_keys_good_leaf_node_update_case:
  {|protocol_invariants|} ->
  tr:trace -> me:principal ->
  ln:leaf_node_nt bytes tkt -> group_id:mls_bytes bytes -> li:nat ->
  Lemma
  (requires
    ln.data.source == LNS_update /\
    i_have_verified_leaf_node tr me ln group_id li /\
    is_well_formed _ (bytes_invariant tr) ln /\
    bytes_invariant tr group_id /\
    trace_invariant tr /\
    has_treesync_treekem_link_invariants
  )
  (ensures
    node_sk_label_canon (TLeaf (Some ln) <: treesync bytes tkt 0 li) group_id `can_flow tr` (get_hpke_sk_label tr ln.data.content) /\ (
      ln.data.content `has_hpke_sk_usage tr` node_key_usage
      \/
      node_sk_label_canon (TLeaf (Some ln) <: treesync bytes tkt 0 li) group_id `can_flow tr` public
    )
  )
let all_tree_keys_good_leaf_node_update_case #invs tr me ln group_id li =
  let prin = Some?.v (credential_to_principal ln.data.credential) in
  let leaf_node_has_been_verified_event = {leaf_node = ln; group_id; leaf_index = li} in
  is_corrupt_event_triggered_label tr me leaf_node_has_been_verified_event;
  big_join_flow_to_component tr (principal_leaf_node_has_been_verified_label ln group_id li) me;
  assert(is_corrupt tr (leaf_node_has_been_verified_label ln group_id li));

  let t = (TLeaf (Some ln) <: treesync bytes tkt 0 li) in
  node_sk_label_flows_to_node_sk_label_without_committer t group_id li tr;
  node_sk_label_aux_flows_to_node_sk_label_aux_leaf (canonicalize_unmerged_leaves t) group_id YesCommitter li tr;
  guard_authentication_lemma tr (signature_key_label prin ln.data.signature_key) (leaf_node_has_been_verified_label ln group_id li)
    (fun tr_ev -> exists p. leaf_node_has_been_verified_pred tr_ev p leaf_node_has_been_verified_event)
    (fun tr_ev ->
      trace_invariant_before tr_ev tr
    )
    (fun tr_before_ev ->
      bytes_well_formed tr_before_ev ln.data.content /\
      node_sk_label_canon_nosig t group_id li `can_flow tr_before_ev` (get_hpke_sk_label tr_before_ev ln.data.content) /\
      (get_node_content t) `has_hpke_sk_usage tr_before_ev` node_key_usage
    )
    (fun tr_before_ev ->
      trace_invariant_before tr_before_ev tr;
      eliminate exists as_token. (dy_asp tr_before_ev).credential_ok (leaf_node_to_as_input ln) as_token
      returns _
      with _. (
        leaf_node_source_update_implies_event tr_before_ev ln group_id li as_token
      )
    )
#pop-options

#push-options "--z3rlimit 25"
val all_tree_keys_good_leaf_node_key_package_case:
  {|protocol_invariants|} ->
  tr:trace -> me:principal ->
  ln:leaf_node_nt bytes tkt -> group_id:mls_bytes bytes -> li:nat ->
  Lemma
  (requires
    ln.data.source == LNS_key_package /\
    i_have_verified_leaf_node tr me ln group_id li /\
    is_well_formed _ (bytes_invariant tr) ln /\
    bytes_invariant tr group_id /\
    trace_invariant tr /\
    has_treesync_treekem_link_invariants
  )
  (ensures
    node_sk_label_canon (TLeaf (Some ln) <: treesync bytes tkt 0 li) group_id `can_flow tr` (get_hpke_sk_label tr ln.data.content) /\ (
      ln.data.content `has_hpke_sk_usage tr` node_key_usage
      \/
      node_sk_label_canon (TLeaf (Some ln) <: treesync bytes tkt 0 li) group_id `can_flow tr` public
    )
  )
let all_tree_keys_good_leaf_node_key_package_case #invs tr me ln group_id li =
  let prin = Some?.v (credential_to_principal ln.data.credential) in
  let leaf_node_has_been_verified_event = {leaf_node = ln; group_id; leaf_index = li} in
  is_corrupt_event_triggered_label tr me leaf_node_has_been_verified_event;
  big_join_flow_to_component tr (principal_leaf_node_has_been_verified_label ln group_id li) me;
  assert(is_corrupt tr (leaf_node_has_been_verified_label ln group_id li));

  let t = (TLeaf (Some ln) <: treesync bytes tkt 0 li) in
  node_sk_label_flows_to_node_sk_label_without_committer t group_id li tr;
  node_sk_label_aux_flows_to_node_sk_label_aux_leaf (canonicalize_unmerged_leaves t) group_id YesCommitter li tr;
  guard_authentication_lemma tr (signature_key_label prin ln.data.signature_key) (leaf_node_has_been_verified_label ln group_id li)
    (fun tr_ev -> exists p. leaf_node_has_been_verified_pred tr_ev p leaf_node_has_been_verified_event)
    (fun tr_ev ->
      trace_invariant_before tr_ev tr
    )
    (fun tr_before_ev ->
      bytes_well_formed tr_before_ev ln.data.content /\
      node_sk_label_canon_nosig t group_id li `can_flow tr_before_ev` (get_hpke_sk_label tr_before_ev ln.data.content) /\
      (get_node_content t) `has_hpke_sk_usage tr_before_ev` node_key_usage
    )
    (fun tr_before_ev ->
      trace_invariant_before tr_before_ev tr;
      eliminate exists as_token. (dy_asp tr_before_ev).credential_ok (leaf_node_to_as_input ln) as_token
      returns _
      with _. (
        leaf_node_source_key_package_implies_event tr_before_ev ln group_id li as_token
      )
    )
#pop-options

val node_sk_label_flows_to_un_addP:
  #l:nat -> #i:tree_index l ->
  t:treesync bytes tkt l i -> group_id:mls_bytes bytes -> p:(nat -> bool) ->
  tr:trace ->
  Lemma (
    node_sk_label t group_id `can_flow tr` node_sk_label (un_addP t p) group_id
  )
let rec node_sk_label_flows_to_un_addP #l #i t group_id p tr =
  match t with
  | TLeaf _ -> ()
  | TNode opt_pn left right -> (
    node_sk_label_flows_to_un_addP left group_id p tr;
    node_sk_label_flows_to_un_addP right group_id p tr
  )

val node_sk_label_flows_to_node_sk_label_canon:
  #l:nat -> #i:tree_index l ->
  t:treesync bytes tkt l i -> group_id:mls_bytes bytes ->
  tr:trace ->
  Lemma (
    node_sk_label t group_id `can_flow tr` node_sk_label_canon t group_id
  )
let node_sk_label_flows_to_node_sk_label_canon #l #i t group_id tr =
  node_sk_label_flows_to_un_addP t group_id (un_add_unmerged_leaf (unmerged_leaves_of t)) tr

val node_sk_label_noX_eq_node_sk_label:
  #l:nat -> #i:tree_index l ->
  t:treesync bytes tkt l i -> group_id:mls_bytes bytes -> li:nat ->
  Lemma
  (requires ~(leaf_index_inside l i li))
  (ensures
    node_sk_label t group_id == node_sk_label_nosig t group_id li /\
    node_sk_label t group_id == node_sk_label_nocommitter t group_id li
  )
let rec node_sk_label_noX_eq_node_sk_label #l #i t group_id li =
  match t with
  | TLeaf None -> ()
  | TLeaf (Some _) -> ()
  | TNode opt_pn left right -> (
    node_sk_label_noX_eq_node_sk_label left group_id li;
    node_sk_label_noX_eq_node_sk_label right group_id li
  )

#push-options "--z3rlimit 25"
val prove_all_tree_keys_good:
  {|protocol_invariants|} ->
  #l:nat -> #i:tree_index l ->
  tr:trace -> me:principal ->
  t:treesync bytes tkt l i -> ast:as_tokens bytes (dy_asp tr).token_t l i -> group_id:mls_bytes bytes ->
  Lemma
  (requires
    i_have_verified_every_leaf_node tr me t group_id /\
    unmerged_leaves_ok t /\
    parent_hash_invariant t /\
    MLS.TreeSync.Invariants.ValidLeaves.valid_leaves_invariant group_id t /\
    MLS.TreeSync.Invariants.AuthService.all_credentials_ok t ast /\
    is_well_formed _ (bytes_invariant tr) t /\
    bytes_invariant tr group_id /\
    trace_invariant tr /\
    has_treesync_treekem_link_invariants
  )
  (ensures all_tree_keys_good t group_id tr)
let rec prove_all_tree_keys_good #invs #l #i tr me t ast group_id =
  match t, ast with
  | TLeaf None, _ -> ()
  | TLeaf (Some ln), _ -> (
    assert(leaf_at t i == Some ln);
    match (ln <: leaf_node_nt bytes tkt).data.source with
    | LNS_commit -> all_tree_keys_good_parent_hash_case tr me t ast group_id
    | LNS_update -> all_tree_keys_good_leaf_node_update_case tr me ln group_id i
    | LNS_key_package -> all_tree_keys_good_leaf_node_key_package_case tr me ln group_id i
  )
  | TNode opt_pn left right, TNode _ aleft aright -> (
    prove_all_tree_keys_good tr me left aleft group_id;
    prove_all_tree_keys_good tr me right aright group_id;
    match opt_pn with
    | None -> ()
    | Some pn -> (
      leaf_at_i_have_verified_every_leaf_node tr me t group_id (get_authentifier_index t);
      all_tree_keys_good_parent_hash_case tr me t ast group_id
    )
  )
#pop-options

val node_sk_label_aux_empty:
  #l:nat -> #i:tree_index l ->
  t:treesync bytes tkt l i -> group_id:mls_bytes bytes -> ty:node_label_type ->
  tr:trace ->
  Lemma
  (requires is_tree_empty t)
  (ensures node_sk_label_aux t group_id ty == secret)
let rec node_sk_label_aux_empty #l #i t group_id ty tr =
  match t with
  | TLeaf _ -> ()
  | TNode _ left right ->
    node_sk_label_aux_empty left group_id ty tr;
    node_sk_label_aux_empty right group_id ty tr

val node_sk_label_nocommitter_empty:
  #l:nat -> #i:tree_index l ->
  t:treesync bytes tkt l i -> group_id:mls_bytes bytes -> li:nat ->
  tr:trace ->
  Lemma
  (requires is_tree_empty t)
  (ensures node_sk_label_nocommitter t group_id li == secret)
let node_sk_label_nocommitter_empty #l #i t group_id li tr =
  node_sk_label_aux_empty t group_id (NoCommitter li) tr

val node_sk_label_nosig_join_node_sk_label_nocommitter_eq:
  #l:pos -> #i:tree_index l ->
  t:treesync bytes tkt l i -> group_id:mls_bytes bytes -> li:leaf_index l i ->
  tr:trace ->
  Lemma (
    let (child, sibling) = get_child_sibling t li in
    (join (node_sk_label_nocommitter child group_id li) (node_sk_label_nosig sibling group_id li)) == node_sk_label_nocommitter t group_id li
  )
let node_sk_label_nosig_join_node_sk_label_nocommitter_eq #l #i t group_id li tr =
  let (child, sibling) = get_child_sibling t li in
  node_sk_label_noX_eq_node_sk_label sibling group_id li;
  join_commutes (node_sk_label_nocommitter child group_id li) (node_sk_label_nosig sibling group_id li)
