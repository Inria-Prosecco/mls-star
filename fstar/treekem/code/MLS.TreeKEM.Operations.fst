module MLS.TreeKEM.Operations

open FStar.List.Tot
open Comparse
open MLS.Crypto
open MLS.Utils
open MLS.Tree
open MLS.TreeCommon
open MLS.TreeKEM.Types
open MLS.NetworkTypes
open MLS.TreeKEM.NetworkTypes
open MLS.TreeKEM.Invariants
open MLS.Result

#set-options "--fuel 1 --ifuel 1 --z3rlimit 50"

val tree_add:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #l:nat -> #i:tree_index l ->
  treekem bytes l i -> li:leaf_index l i -> treekem_leaf bytes ->
  treekem bytes l i
let rec tree_add #bytes #cb #l #i t li lp =
  match t with
  | TLeaf _ -> TLeaf (Some lp)
  | TNode opt_content left right -> (
    let new_opt_content = (
      match opt_content with
      | None -> None
      | Some content -> (
          Some ({content with unmerged_leaves = insert_sorted li content.unmerged_leaves})
      )
    ) in
    if is_left_leaf li then (
      TNode new_opt_content (tree_add left li lp) right
    ) else (
      TNode new_opt_content left (tree_add right li lp)
    )
  )

val tree_apply_path:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #l:nat -> #i:tree_index l -> #li:leaf_index l i ->
  treekem bytes l i -> pathkem bytes l i li ->
  treekem bytes l i
let rec tree_apply_path #bytes #cb #l #i #li t p =
  match t, p with
  | TLeaf _, PLeaf mi -> TLeaf (Some mi)
  | TNode _ left right, PNode oupn p_next -> (
    let new_opt_content = (
      match oupn with
      | None -> None
      | Some upn -> Some {
        public_key = upn.encryption_key;
        unmerged_leaves = [];
      }
    ) in
    if is_left_leaf li then
      TNode new_opt_content (tree_apply_path left p_next) right
    else
      TNode new_opt_content left (tree_apply_path right p_next)
  )

val path_blank:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #l:nat -> #i:tree_index l -> #li:leaf_index l i ->
  treekem_priv bytes l i li -> blank_li:leaf_index l i{blank_li <> li} ->
  treekem_priv bytes l i li
let rec path_blank #bytes #cb #l #i #li p blank_li =
  match p with
  | PNode _ p_next -> (
    if is_left_leaf li = is_left_leaf blank_li then
      let new_p_next = path_blank p_next blank_li in
      PNode None new_p_next
    else
      PNode None p_next
  )

val path_extend:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #l:nat -> #li:leaf_index l 0 ->
  treekem_priv bytes l 0 li ->
  treekem_priv bytes (l+1) 0 li
let path_extend #bytes #cb #l #i p =
  PNode None p

val path_truncate:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #l:pos -> #li:leaf_index (l-1) 0 ->
  treekem_priv bytes l 0 li ->
  treekem_priv bytes (l-1) 0 li
let path_truncate #bytes #cb #l #i p =
  let PNode _ p_next = p in
  p_next

val derive_keypair_from_path_secret:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  bytes ->
  result (hpke_private_key bytes & hpke_public_key bytes)
let derive_keypair_from_path_secret #bytes #cb path_secret =
  let? node_secret = derive_secret path_secret "node" in
  hpke_gen_keypair (node_secret <: bytes)

val derive_next_path_secret:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  bytes ->
  result bytes
let derive_next_path_secret #bytes #cb path_secret =
  let? res = derive_secret path_secret "path" in
  return (res <: bytes)

val un_addP:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #l:nat -> #i:tree_index l ->
  treekem bytes l i -> (nat -> bool) ->
  treekem bytes l i
let rec un_addP #bytes #cb #l #i t pre =
  match t with
  | TLeaf _ -> if pre i then t else TLeaf None
  | TNode okp left right -> (
    let new_okp =
      match okp with
      | None -> None
      | Some kp -> Some ({ kp with unmerged_leaves = List.Tot.filter pre kp.unmerged_leaves })
    in
    TNode new_okp (un_addP left pre) (un_addP right pre)
  )

val excluded_pre: list nat -> nat -> bool
let excluded_pre l i =
  not (List.Tot.mem i l)

val un_add:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #l:nat -> #i:tree_index l ->
  treekem bytes l i -> list nat ->
  treekem bytes l i
let un_add #bytes #cb #l #i t excluded_leaves =
  un_addP t (excluded_pre excluded_leaves)

val unmerged_leaves_resolution:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #l:nat -> #i:tree_index l ->
  t:treekem bytes l i -> unmerged_leaves:list nat{for_allP (unmerged_leaf_exists t) unmerged_leaves}  ->
  res:list bytes{List.Tot.length res == List.Tot.length unmerged_leaves}
let rec unmerged_leaves_resolution #bytes #cb #l #i t unmerged_leaves =
  match unmerged_leaves with
  | [] -> []
  | h_ul::t_ul -> (Some?.v (leaf_at t h_ul)).public_key::(unmerged_leaves_resolution t t_ul)

val tree_resolution:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #l:nat -> #i:tree_index l ->
  t:treekem bytes l i{treekem_invariant t} ->
  list bytes
let rec tree_resolution #bytes #cb #l #i t =
  match t with
  | TLeaf None -> []
  | TLeaf (Some mi) -> [mi.public_key]
  | TNode (Some kp) left right -> (kp.public_key)::(unmerged_leaves_resolution t kp.unmerged_leaves)
  | TNode None left right -> (tree_resolution left)@(tree_resolution right)

val find_index:
  #a:eqtype -> #b:eqtype{b `subtype_of` a} -> #c:eqtype{c `subtype_of` a} ->
  b -> l:list c ->
  option (nat_less (List.Tot.length l))
let rec find_index #a #b #c x l =
  match l with
  | [] -> None
  | h::t ->
    if (x <: a) = (h <: a) then (
      Some 0
    ) else (
      match find_index #a x t with
      | Some res -> Some (res+1)
      | None -> None
    )

val resolution_index:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #l:nat -> #i:tree_index l ->
  t:treekem bytes l i{treekem_invariant t} -> li:leaf_index l i{Some? (leaf_at t li)} ->
  nat_less (List.Tot.length (tree_resolution t))
let rec resolution_index #bytes #cb #l t leaf_index =
  match t with
  | TLeaf (Some _) -> 0
  | TNode (Some kp) left right -> (
    match find_index #nat leaf_index kp.unmerged_leaves with
    | None -> 0
    | Some res -> 1+res
  )
  | TNode None left right ->
    let (child, _) = get_child_sibling t leaf_index in
    let child_resolution_index = resolution_index child leaf_index in
    List.Tot.Properties.append_length (tree_resolution left) (tree_resolution right);
    if is_left_leaf leaf_index then
      child_resolution_index
    else
      (List.Tot.length (tree_resolution left)) + child_resolution_index

val get_private_key:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #l:nat -> #i:tree_index l -> #li:leaf_index l i ->
  t:treekem bytes l i{treekem_invariant t} -> p_priv:treekem_priv bytes l i li{treekem_priv_invariant t p_priv} ->
  result (hpke_private_key bytes)
let rec get_private_key #bytes #cb #l #i #li t p_priv =
  match t, p_priv with
  | TLeaf (Some _), PLeaf sk ->
    return sk
  | TNode (Some pn) _ _, PNode opt_sk _ ->
    if li < pow2 32 && List.Tot.mem li pn.unmerged_leaves then (
      return (get_path_leaf p_priv)
    ) else (
      match opt_sk with
      | None -> error "get_private_key: private key not in private state"
      | Some sk ->
        return sk
    )
  | TNode None left right, PNode _ p_next ->
    let (child, _) = get_child_sibling t li in
    get_private_key child p_next

val check_update_path_ciphertexts_lengthes:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #l:nat -> #i:tree_index l -> #li:leaf_index l i ->
  t:treekem bytes l i{treekem_invariant t} -> p_upd:pathkem bytes l i li ->
  bool
let rec check_update_path_ciphertexts_lengthes #bytes #cb #l #i #li t p =
  match t, p with
  | TLeaf _, PLeaf _ -> true
  | TNode _ _ _, PNode opt_upn p_next ->
    let cur_ok =
      match opt_upn with
      | None -> true
      | Some upn ->
        let (_, sibling) = get_child_sibling t li in
        List.Tot.length (tree_resolution sibling) = List.Tot.length upn.encrypted_path_secret
    in
    let (child, _) = get_child_sibling t li in
    cur_ok && check_update_path_ciphertexts_lengthes child p_next

type path_secret_level (l:nat) =
  x:nat{0 < x /\ x <= l}

// Obtain a path secret from a Commit
val get_path_secret:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #l:nat -> #i:tree_index l -> #my_li:leaf_index l i -> #li:leaf_index l i{my_li <> li} ->
  t:treekem bytes l i{treekem_invariant t} -> p_priv:treekem_priv bytes l i my_li{treekem_priv_invariant t p_priv} ->
  p_upd:pathkem bytes l i li{check_update_path_ciphertexts_lengthes t p_upd /\ path_filtering_weak_ok t p_upd} -> group_context_nt bytes ->
  result (bytes & path_secret_level l)
let rec get_path_secret #bytes #cb #l #i #my_li #li t p_priv p_upd group_context =
  match t, p_priv, p_upd with
  | TNode _ _ _, PNode _ p_priv_next, PNode opt_upn p_upd_next ->
    if is_left_leaf my_li = is_left_leaf li then (
      // The update path and the path to our leaf continue to the same node, recurse
      let (child, _) = get_child_sibling t li in
      let? (path_secret, path_level) = get_path_secret child (p_priv_next <: treekem_priv bytes (l-1) _ my_li) (p_upd_next <: pathkem bytes (l-1) _ li) group_context in
      return ((path_secret, path_level) <: bytes & path_secret_level l)
    ) else (
      // We are at a branching point
      match opt_upn with
      | Some upn -> (
        // Obtain the node secret by decryption
        let (_, sibling) = get_child_sibling t li in
        let my_index = resolution_index sibling my_li in
        let my_ciphertext = List.Tot.index upn.encrypted_path_secret my_index in
        let? my_private_key = get_private_key sibling (PNode?.next p_priv) in
        let? kem_output = mk_hpke_kem_output #bytes my_ciphertext.kem_output "get_path_secret" "kem_output" in
        let? path_secret = decrypt_with_label #bytes my_private_key "UpdatePathNode" (serialize _ group_context) kem_output my_ciphertext.ciphertext in
        return ((path_secret, l) <: bytes & path_secret_level l)
      )
      | None -> (
        // Impossible
        let (_, sibling) = get_child_sibling t li in
        MLS.TreeCommon.Lemmas.is_tree_empty_leaf_at sibling my_li;
        false_elim ()
      )
    )

// This function can be used in two situations:
// - when processing a Commit
// - when processing a Welcome
// When processing a Commit,
// the tree `t` shoud already have the UpdatePath applied.
val path_apply_path:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #l:nat -> #i:tree_index l -> #li:leaf_index l i ->
  t:treekem bytes l i -> p_priv:treekem_priv bytes l i li ->
  path_secret:bytes -> path_node_level:path_secret_level l ->
  result (treekem_priv bytes l i li & bytes)
let rec path_apply_path #bytes #cb #l #i #li t p_priv path_secret path_node_level =
  match t, p_priv with
  | TNode opt_pn _ _, PNode _ p_priv_next -> (
    let (child, sibling) = get_child_sibling t li in
    let? (new_p_priv_next, path_secret) = (
      if path_node_level = l  then (
        return (p_priv_next, path_secret)
      ) else (
        path_apply_path child p_priv_next path_secret path_node_level
      )
    ) in
    if not (is_tree_empty sibling) then (
      let? (sk, pk) = derive_keypair_from_path_secret path_secret in
      let? new_path_secret = derive_next_path_secret path_secret in
      if not (Some? opt_pn && (pk <: bytes) = (Some?.v opt_pn).public_key) then
        error "path_apply_path: wrong public key"
      else
        return (PNode (Some sk) new_p_priv_next, new_path_secret)
    ) else (
      // The node was filtered, transfer the path secret up in the tree
      return (PNode None new_p_priv_next, path_secret)
    )
  )

val forget_path_secrets:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #l:nat -> #i:tree_index l -> #li:leaf_index l i ->
  path_secrets bytes l i li ->
  path unit bool l i li
let rec forget_path_secrets #bytes #cb #l #i #li p =
  match p with
  | PLeaf _ -> PLeaf ()
  | PNode (Some _) p_next -> PNode true (forget_path_secrets p_next)
  | PNode None p_next -> PNode false (forget_path_secrets p_next)

val generate_forgotten_path_secrets:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #l:nat -> #i:tree_index l ->
  t:treekem bytes l i -> li:leaf_index l i ->
  path unit bool l i li
let rec generate_forgotten_path_secrets #bytes #cb #l #i t li =
  match t with
  | TLeaf _ -> PLeaf ()
  | TNode _ _ _ -> (
    let (child, sibling) = get_child_sibling t li in
    if not (is_tree_empty sibling) then (
      PNode true (generate_forgotten_path_secrets child li)
    ) else (
      PNode false (generate_forgotten_path_secrets child li)
    )
  )

val generate_path_secrets:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #l:nat -> #i:tree_index l ->
  t:treekem bytes l i ->
  hpke_private_key bytes -> path_secret_0:bytes -> li:leaf_index l i ->
  result (p:path_secrets bytes l i li{forget_path_secrets p == generate_forgotten_path_secrets t li} * bytes)
let rec generate_path_secrets #bytes #cb #l #i t leaf_sk path_secret_0 li =
  match t with
  | TLeaf _ -> return (PLeaf leaf_sk, path_secret_0)
  | TNode _ _ _ -> (
    let (child, sibling) = get_child_sibling t li in
    let? (p_next, my_path_secret) = generate_path_secrets child leaf_sk path_secret_0 li in
    if not (is_tree_empty sibling) then (
      let? next_path_secret = derive_next_path_secret my_path_secret in
      return #((p:path_secrets bytes l i li{forget_path_secrets p == generate_forgotten_path_secrets t li} * bytes)) (PNode (Some (my_path_secret)) p_next, next_path_secret)
    ) else (
      // The node was filtered, transfer the path secret up in the tree
      return #((p:path_secrets bytes l i li{forget_path_secrets p == generate_forgotten_path_secrets t li} * bytes)) ((PNode None p_next), (my_path_secret <: bytes))
    )
  )

val multi_encrypt_with_label_entropy_lengths:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  list bytes ->
  list nat
let rec multi_encrypt_with_label_entropy_lengths #bytes #cb pks =
  match pks with
  | [] -> []
  | h::t -> (hpke_private_key_length #bytes)::(multi_encrypt_with_label_entropy_lengths t)

val multi_encrypt_with_label:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  pks:list bytes -> label:valid_label -> context:bytes -> plaintext:bytes -> randomness bytes (multi_encrypt_with_label_entropy_lengths pks) ->
  result (list (hpke_ciphertext_nt bytes))
let rec multi_encrypt_with_label #bytes #cb public_keys label context plaintext rand =
  match public_keys with
  | [] -> return []
  | pk::pks ->
    let (rand_cur, rand_next) = dest_randomness rand in
    let? pk = mk_hpke_public_key #bytes pk "multi_encrypt_with_label" "pk" in
    let? (kem_output, ciphertext) = encrypt_with_label pk label context plaintext rand_cur in
    let? kem_output = mk_mls_bytes #bytes kem_output "multi_encrypt_with_label" "kem_output" in
    let? ciphertext = mk_mls_bytes #bytes ciphertext "multi_encrypt_with_label" "ciphertext" in
    let? res_tl = multi_encrypt_with_label pks label context plaintext rand_next in
    return (({kem_output; ciphertext;} <: hpke_ciphertext_nt bytes)::res_tl)

val encrypt_path_secrets_entropy_lengths:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #l:nat -> #i:tree_index l -> #li:leaf_index l i ->
  t:treekem bytes l i{treekem_invariant t} -> path unit bool l i li ->
  list nat
let rec encrypt_path_secrets_entropy_lengths #bytes #cb #l #i #li t p =
  match t, p with
  | TLeaf _, PLeaf _ -> []
  | TNode _ _ _, PNode is_not_filtered p_next -> (
    let (child, sibling) = get_child_sibling t li in
    let my_randomness =
      if is_not_filtered then
        multi_encrypt_with_label_entropy_lengths (tree_resolution sibling)
      else
        []
    in
    let next_randomness = encrypt_path_secrets_entropy_lengths child p_next in
    my_randomness@next_randomness
  )

val encrypt_path_secrets:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #l:nat -> #i:tree_index l -> #li:leaf_index l i ->
  t:treekem bytes l i{treekem_invariant t} -> p:path_secrets bytes l i li ->
  group_context_nt bytes ->
  randomness bytes (encrypt_path_secrets_entropy_lengths t (forget_path_secrets p)) ->
  result (pathkem bytes l i li & treekem_priv bytes l i li)
let rec encrypt_path_secrets #bytes #cb #l #i #li t p group_context rand =
  match t, p with
  | TLeaf _, PLeaf leaf_ikm -> (
    let? (sk, pk) = hpke_gen_keypair (leaf_ikm <: bytes) in
    return (PLeaf ({public_key = pk;} <: treekem_leaf bytes), PLeaf sk)
  )
  | TNode _ _ _, PNode None p_next -> (
    let (child, _) = get_child_sibling t li in
    let? (res_p_next, res_p_priv_next)= encrypt_path_secrets child p_next group_context rand in
    return (PNode None res_p_next, PNode None res_p_priv_next)
  )
  | TNode _ _ _, PNode (Some path_secret) p_next -> (
    let (child, sibling) = get_child_sibling t li in
    let rand_cur, rand_next = split_randomness rand in
    let? (res_p_next, res_p_priv_next) = encrypt_path_secrets child p_next group_context rand_next in
    let? ciphertexts = multi_encrypt_with_label (tree_resolution sibling) "UpdatePathNode" (serialize _ group_context) path_secret rand_cur in
    let? ciphertexts = mk_mls_list #bytes ciphertexts "multi_encrypt_with_label" "ciphertexts" in
    let? (sk, pk) = derive_keypair_from_path_secret path_secret in
    return (PNode (Some {encryption_key = pk; encrypted_path_secret = ciphertexts;}) res_p_next, PNode (Some sk) res_p_priv_next)
  )

// TODO: this function could have more preconditions and not fail
// leaf_li <> li
// leaf_li is a leaf index
// some property about p, that is it filtered correctly
val get_path_secret_of_added_leaf:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #l:nat -> #i:tree_index l -> #li:leaf_index l i ->
  p:path_secrets bytes l i li ->
  leaf_li:nat ->
  result bytes
let rec get_path_secret_of_added_leaf #bytes #cb #l #i #li p leaf_li =
  match p with
  | PLeaf _ -> internal_failure "get_path_secret_of_added_leaf: leaf case"
  | PNode opt_path_secret p_next ->
    if not (leaf_index_inside l i leaf_li) then
      internal_failure "get_path_secret_of_added_leaf: bad leaf index"
    else if is_left_leaf li = is_left_leaf #l #i leaf_li then
      get_path_secret_of_added_leaf p_next leaf_li
    else
      match opt_path_secret with
      | None -> internal_failure "get_path_secret_of_added_leaf: no path secret"
      | Some path_secret -> return path_secret

// TODO: same for this function
val get_path_secret_of_added_leaves:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #l:nat -> #i:tree_index l -> #li:leaf_index l i ->
  p:path_secrets bytes l i li ->
  leaves_li:list nat ->
  result (list bytes)
let get_path_secret_of_added_leaves #bytes #cb #l #i #li p leaves_li =
  let? res = mapM (get_path_secret_of_added_leaf p) leaves_li in
  return (res <: list bytes)

// TODO: do some computations also done by encrypt_path_secrets
val path_secrets_to_pre_pathkem:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #l:nat -> #i:tree_index l -> #li:leaf_index l i ->
  path_secrets bytes l i li ->
  result (pre_pathkem bytes l i li)
let rec path_secrets_to_pre_pathkem #bytes #cb #l #i #li p =
  match p with
  | PLeaf leaf_sk -> (
    let? (sk, pk) = hpke_gen_keypair (leaf_sk <: bytes) in
    return (PLeaf ({public_key = pk;} <: treekem_leaf bytes))
  )
  | PNode None p_next -> (
    let? res_p_next =  path_secrets_to_pre_pathkem p_next in
    return (PNode None res_p_next)
  )
  | PNode (Some path_secret) p_next -> (
    let? res_p_next = path_secrets_to_pre_pathkem p_next in
    let? (sk, pk) = derive_keypair_from_path_secret path_secret in
    return (PNode (Some pk) res_p_next)
  )

val create_empty_priv:
  #bytes:Type0 -> {|crypto_bytes bytes|} ->
  #l:nat -> #i:tree_index l -> #li:leaf_index l i ->
  hpke_private_key bytes ->
  treekem_priv bytes l i li
let rec create_empty_priv #bytes #cb #l #i #li leaf_private_key =
  if l = 0 then
    PLeaf leaf_private_key
  else
    PNode None (create_empty_priv leaf_private_key)

val compute_least_common_ancestor_level:
  #leaf_t:Type -> #node_t:Type ->
  #l:nat -> #i:tree_index l -> #li:leaf_index l i ->
  path leaf_t node_t l i li -> leaf_ind:leaf_index l i{leaf_ind <> li} ->
  path_secret_level l
let rec compute_least_common_ancestor_level #leaf_t #node_t #l #i #li p leaf_ind =
  match p with
  | PNode _ p_next ->
    if is_left_leaf li = is_left_leaf leaf_ind then
      compute_least_common_ancestor_level p_next leaf_ind
    else
      l
