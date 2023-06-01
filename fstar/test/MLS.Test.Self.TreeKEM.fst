module MLS.Test.Self.TreeKEM

open FStar.All
open Comparse
open MLS.Crypto
open MLS.NetworkTypes
open MLS.Tree
open MLS.TreeKEM.API.Types
open MLS.TreeKEM.API
open MLS.TreeKEM.Types
open MLS.TreeKEM.Operations
open MLS.Test.Utils
open MLS.StringUtils
open MLS.Result

#set-options "--fuel 0 --ifuel 0"

type participant_secrets (bytes:Type0) {|crypto_bytes bytes|} = {
  leaf_secret: lbytes bytes (hpke_private_key_length #bytes);
}

type mls_state (bytes:Type0) {|crypto_bytes bytes|} = {
  public: treekem_state bytes;
  epoch: nat;
  secrets: list (nat & participant_secrets bytes);
}

type test_state = {
  n_add: nat;
  n_update: nat;
  n_remove: nat;
}

type state (bytes:Type0) {|crypto_bytes bytes|} = {
  rng: rand_state;
  mls: mls_state bytes;
  test: test_state;
}

type op_type = | Add | Update | Remove

val get_secret: #a:Type -> list (nat & a) -> nat -> ML a
let get_secret #a l x =
  extract_result (from_option "" (List.Tot.assoc x l))

#push-options "--fuel 1 --ifuel 1"
val update_secret: #a:Type -> list (nat & a) -> (nat & a) -> ML (list (nat & a))
let rec update_secret #a l (x, s) =
  match l with
  | [] -> failwith "remove_secret: couldn't find index"
  | (hx, hs)::t ->
    if hx = x then
      (x,s)::t
    else
      (hx,hs)::(update_secret t (x,s))
#pop-options

#push-options "--fuel 1 --ifuel 1"
val remove_secret: #a:Type -> list (nat & a) -> nat -> ML (list (nat & a))
let rec remove_secret #a l x =
  match l with
  | [] -> failwith "remove_secret: couldn't find index"
  | (hx, hs)::t ->
    if hx = x then
      t
    else
      (hx,hs)::(remove_secret t x)
#pop-options

val create_participant: #bytes:Type0 -> {|crypto_bytes bytes|} -> rand_state -> ML (rand_state & member_info bytes & participant_secrets bytes)
let create_participant #bytes #cb rng =
  let (rng, leaf_secret) = gen_rand_bytes rng (hpke_private_key_length #bytes) in
  let (hpke_sk, hpke_pk) = extract_result (derive_keypair_from_path_secret leaf_secret) in
  let my_secrets = {leaf_secret} in
  let leaf_package: member_info bytes = {public_key = hpke_pk} in
  (rng, leaf_package, my_secrets)

#push-options "--fuel 1 --ifuel 1"
val add_rand: #bytes:Type0 -> {|crypto_bytes bytes|} -> rand_state -> mls_state bytes -> ML (rand_state & mls_state bytes)
let add_rand #bytes #cb rng st =
  let (rng, leaf_package, my_secrets) = create_participant #bytes #cb rng in
  let (new_public_state, leaf_index) = MLS.TreeKEM.API.add st.public leaf_package in
  (rng, {
    public = new_public_state;
    epoch = st.epoch+1;
    secrets = (leaf_index, my_secrets) :: st.secrets;
  })
#pop-options

//TODO: the group context is replaced with only the tree hash
#push-options "--z3rlimit 50 --ifuel 1 --fuel 0"
val update_leaf: #bytes:Type0 -> {|crypto_bytes bytes|} -> rand_state -> mls_state bytes -> nat -> ML (rand_state & mls_state bytes)
let update_leaf #bytes #cb rng st leaf_index =
  let leaf_secrets = get_secret st.secrets leaf_index in
  if not (leaf_index < pow2 st.public.levels) then failwith "" else
  let (rng, new_leaf_secret) = gen_rand_bytes rng (hpke_private_key_length #bytes) in
  let ad = (ps_prefix_to_ps_whole ps_nat).serialize st.epoch in
  let rand_length = (update_path_entropy_lengths st.public.tree leaf_index) in
  let (rng, rand) = gen_rand_randomness rng rand_length in
  let (path_tk, _) = extract_result (update_path st.public.tree leaf_index new_leaf_secret ad rand) in
  let new_public = commit st.public path_tk in
  (rng, {
    public = new_public;
    epoch = st.epoch+1;
    secrets = update_secret st.secrets (leaf_index, {leaf_secrets with leaf_secret = new_leaf_secret});
  })
#pop-options

val update_rand: #bytes:Type0 -> {|crypto_bytes bytes|} -> rand_state -> mls_state bytes -> ML (rand_state & mls_state bytes)
let update_rand #bytes #cb rng st =
  let (rng, i) = gen_rand_num_ml rng (List.Tot.length st.secrets) in
  let (leaf_index, _) = List.Tot.index st.secrets i in
  update_leaf rng st leaf_index

val remove_leaf: #bytes:Type0 -> {|crypto_bytes bytes|} -> rand_state -> mls_state bytes -> nat -> ML (rand_state & mls_state bytes)
let remove_leaf #bytes #cb rng st leaf_index =
  if not (leaf_index < pow2 st.public.levels) then failwith "" else
  (rng, {
    public = remove st.public leaf_index;
    epoch = st.epoch+1;
    secrets = List.Tot.filter (fun (x, _) -> x <> leaf_index) st.secrets;
  })

val remove_rand: #bytes:Type0 -> {|crypto_bytes bytes|} -> rand_state -> mls_state bytes -> ML (rand_state & mls_state bytes)
let remove_rand #bytes #cb rng st =
  let (rng, i) = gen_rand_num_ml rng (List.Tot.length st.secrets) in
  let (leaf_index, _) = List.Tot.index st.secrets i in
  remove_leaf rng st leaf_index

#push-options "--fuel 0 --ifuel 1"
val apply_random_operation: #bytes:Type0 -> {|crypto_bytes bytes|} -> state bytes -> ML (state bytes & bool)
let apply_random_operation #bytes #cb st =
  let rng = st.rng in
  let (rng, op) =
    if 2 <= List.Tot.length st.mls.secrets then (
      let (rng, choice) = gen_rand_num_ml rng (st.test.n_add + st.test.n_update + st.test.n_remove) in
      (rng, (
        if choice < st.test.n_add then Add
        else if choice < st.test.n_add + st.test.n_update then Update
        else Remove
      ))
    ) else (
      let (rng, choice) = gen_rand_num_ml rng (st.test.n_add + st.test.n_update) in
      (rng, (
        if choice < st.test.n_add then Add
        else Update
      ))
    )
  in
  //assert (op == Add ==> 0 < st.test.n_add);
  //assert (op == Update ==> 0 < st.test.n_update);
  //assert (op == Remove ==> 0 < st.test.n_remove);
  match op with
  | Add -> (
    let (rng, mls) = add_rand rng st.mls in
    ({rng; mls; test={st.test with n_add = st.test.n_add - 1}}, false)
  )
  | Update -> (
    let (rng, mls) = update_rand rng st.mls in
    ({rng; mls; test={st.test with n_update = st.test.n_update - 1}}, true)
  )
  | Remove -> (
    let (rng, mls) = remove_rand rng st.mls in
    ({rng; mls; test={st.test with n_remove = st.test.n_remove - 1}}, false)
  )
#pop-options

#push-options "--fuel 0 --ifuel 1"
val check_root_secret: {|crypto_bytes bytes|} -> mls_state bytes -> ML unit
let check_root_secret #cb st =
  let open MLS.TreeKEM.Types in
  let (first_index, first_secret) = List.hd st.secrets in
  //IO.print_string (
  //  print_tree
  //    (fun leaf -> match leaf with
  //      | None -> "_"
  //      | Some _ -> "L")
  //    (fun node -> match node with
  //      | None -> "_"
  //      | Some np -> "N[" ^ list_to_string nat_to_string np.unmerged_leaves ^ ", " ^ (if np.path_secret_from = Left then "Left" else "Right") ^ ", " ^ nat_to_string (List.Tot.length np.path_secret_ciphertext) ^ "]")
  //    tree_tk
  //);
  //IO.print_string "\n";
  if not (first_index < pow2 st.public.levels) then failwith "" else
  let first_root_secret = extract_result (root_secret st.public.tree first_index first_secret.leaf_secret) in
  List.iter #(nat & participant_secrets bytes) (fun (index, secret) ->
    if not (index < pow2 st.public.levels) then failwith "" else
    let cur_root_secret = extract_result (root_secret st.public.tree index secret.leaf_secret) in
    if not (first_root_secret = cur_root_secret) then
      failwith ("check_root_secret: " ^ nat_to_string first_index ^ " has " ^ bytes_to_hex_string first_root_secret ^ ", " ^ nat_to_string index ^ " has " ^ bytes_to_hex_string cur_root_secret)
    else
      ()
  ) (List.tail st.secrets)
#pop-options

#push-options "--fuel 1 --ifuel 1"
val foldn: #a:Type -> nat -> (a -> ML a) -> a -> ML a
let rec foldn nb f x =
  if nb = 0 then (
    x)
  else (
    foldn (nb-1) f (f x)
  )
#pop-options

#push-options "--fuel 0 --ifuel 1"
val create_init_state: #bytes:Type0 -> {|crypto_bytes bytes|} -> nat -> ML (rand_state & mls_state bytes)
let create_init_state #bytes #cb seed =
  let rng = init_rand_state seed in
  let (rng, _) = gen_rand_bytes #bytes rng 64 in // Avoid the first bad number generation (might not be useful, but doesn't hurt)
  let (rng, group_id) = gen_rand_bytes #bytes rng 16 in
  let (rng, first_leaf_package, first_secrets) = create_participant rng in
  (rng, ({
    public = {
      levels = 0;
      tree = TLeaf (Some first_leaf_package);
    };
    epoch = 0;
    secrets = [(0, first_secrets)];
  }))
#pop-options

#push-options "--fuel 0 --ifuel 1"
val run_one_self_treekem_test: {|crypto_bytes bytes|} -> nat -> nat -> nat -> nat -> ML unit
let run_one_self_treekem_test #cb seed avg_n_participant n_remove n_update =
  IO.print_string ("Running treekem tests with parameters " ^
    "seed=" ^ (nat_to_string seed) ^ ", " ^
    "avg_n_participant=" ^ (nat_to_string avg_n_participant) ^ ", " ^
    "n_remove=" ^ (nat_to_string n_remove) ^ ", " ^
    "n_update=" ^ (nat_to_string n_update) ^ "\n"
  );
  let (rng, mls) = create_init_state seed in
  let init_state = {
    rng;
    mls;
    test = {
      n_add = avg_n_participant + n_remove;
      n_update;
      n_remove;
    };
  } in
  let (_: state bytes) = foldn (avg_n_participant + n_remove + n_update + n_remove) (fun st ->
    let (st, check) = apply_random_operation st in
    (if check then check_root_secret st.mls else ());
    st
  ) init_state in
  ()
#pop-options

val custom_test_1: {|crypto_bytes bytes|} -> ML unit
let custom_test_1 #cb =
  let (rng, st) = create_init_state 0 in
  let (rng, st) = add_rand rng st in
  let (rng, st) = add_rand rng st in
  let (rng, st) = add_rand rng st in
  let (rng, st) = add_rand rng st in
  let (rng, st) = update_leaf rng st 1 in
  let (rng, st) = update_leaf rng st 2 in
  let (rng, st) = update_leaf rng st 3 in
  let (rng, st) = update_leaf rng st 4 in
  let (rng, st) = remove_leaf rng st 2 in
  let (rng, st) = update_leaf rng st 1 in
  let (rng, st) = add_rand rng st in
  let (rng, st) = update_leaf rng st 4 in
  check_root_secret st

val run_self_treekem_test: unit -> ML unit
let run_self_treekem_test () =
  let cb = mk_concrete_crypto_bytes AC_mls_128_dhkemx25519_chacha20poly1305_sha256_ed25519 in
  custom_test_1 #cb;
  //                           seed add remove update
  run_one_self_treekem_test #cb 0    5   5      5   ;
  run_one_self_treekem_test #cb 1    5   20     20  ;
  run_one_self_treekem_test #cb 2    5   50     25  ;
  run_one_self_treekem_test #cb 3    10  10     10  ;
  run_one_self_treekem_test #cb 4    10  25     25   ;
  run_one_self_treekem_test #cb 5    10  50     25  ;
  run_one_self_treekem_test #cb 6    25  25     25  ;
  run_one_self_treekem_test #cb 7    50  20     100 ;
  ()
