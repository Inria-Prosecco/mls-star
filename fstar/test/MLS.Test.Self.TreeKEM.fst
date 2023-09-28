module MLS.Test.Self.TreeKEM

open FStar.All
open Comparse
open MLS.Crypto
open MLS.NetworkTypes
open MLS.Tree
open MLS.TreeKEM.API.Tree.Types
open MLS.TreeKEM.API.Tree
open MLS.TreeKEM.Types
open MLS.TreeKEM.Operations
open MLS.Test.Utils
open MLS.StringUtils
open MLS.Result

#set-options "--fuel 0 --ifuel 0"

type mls_state (bytes:Type0) {|crypto_bytes bytes|} = {
  states: list (leaf_ind:nat & treekem_tree_state bytes leaf_ind);
  epoch: nat;
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

#push-options "--fuel 0 --ifuel 1"
val add_rand: #bytes:Type0 -> {|crypto_bytes bytes|} -> rand_state -> mls_state bytes -> ML (rand_state & mls_state bytes)
let add_rand #bytes #cb rng st =
  let (rng, leaf_secret) = gen_rand_bytes #bytes rng (hpke_private_key_length #bytes) in
  let (hpke_sk, hpke_pk) = extract_result (hpke_gen_keypair #bytes leaf_secret) in
  let leaf: treekem_leaf bytes = { public_key = hpke_pk } in
  let (add_indices, new_states) = List.Tot.unzip (List.Tot.map (fun (|leaf_ind, state|) ->
    let (new_state, add_index) = MLS.TreeKEM.API.Tree.add state leaf in
    (add_index, (|leaf_ind, new_state|))
  ) st.states) in
  let (add_index, (|tree_levels, tree|)): nat & (l:nat & treekem bytes l 0) =
    match add_indices, new_states with
    | i::_, (|leaf_ind, st|)::_ -> (i, (|st.levels, st.tree|))
    | _, _ -> failwith "add_rand: no add index?"
  in
  if not (List.Tot.for_all ((=) add_index) add_indices) then failwith "add_rand: inconsistent add indices";
  if not (List.Tot.for_all ((=) ((|tree_levels, tree|) <: (l:nat & treekem bytes l 0))) (List.Tot.map #_ #(l:nat & treekem bytes l 0) (fun (|_, st|) -> (|st.levels, st.tree|)) new_states)) then failwith "add_rand: inconsistent trees";
  if not (add_index < pow2 tree_levels && Some? (leaf_at tree add_index)) then failwith "add_rand: bad add index";
  let new_state = extract_result(MLS.TreeKEM.API.Tree.welcome tree hpke_sk None add_index) in
  (rng, {
    states = (|_, new_state|)::new_states;
    epoch = st.epoch+1;
  })
#pop-options

#push-options "--fuel 1 --ifuel 1"
val get_state: #bytes:Type0 -> {|crypto_bytes bytes|} -> list (leaf_ind:nat & treekem_tree_state bytes leaf_ind) -> leaf_ind:nat -> ML (treekem_tree_state bytes leaf_ind)
let rec get_state #bytes #cb l leaf_ind =
  match l with
  | [] -> failwith "get_state: no corresponding state"
  | (|li, st|)::t ->
    if leaf_ind = li then st
    else get_state t leaf_ind
#pop-options

#push-options "--fuel 1 --ifuel 1"
val process_update: #bytes:Type0 -> {|crypto_bytes bytes|} -> #leaf_ind:nat -> #commiter_st:treekem_tree_state bytes leaf_ind -> list (leaf_ind:nat & treekem_tree_state bytes leaf_ind) -> create_commit_result commiter_st -> group_context_nt bytes -> ML (list (bytes & (leaf_ind:nat & treekem_tree_state bytes leaf_ind)))
let rec process_update #bytes #cb #leaf_ind #commiter_st l commit_res group_context =
  match l with
  | [] -> []
  | (|li, tk_state|)::t ->
    let new_tail = process_update t commit_res group_context in
    let new_head =
      if not (leaf_ind < pow2 tk_state.levels) then failwith "process_update: bad leaf index" else
      if not (commiter_st.levels = tk_state.levels) then failwith "process_update: levels" else
      if leaf_ind = li then
        (commit_res.commit_secret, (|leaf_ind, commit_res.new_state|))
      else (
        assume(MLS.NetworkBinder.Properties.path_filtering_ok tk_state.tree commit_res.update_path);
        let (new_state, commit_secret) = extract_result (MLS.TreeKEM.API.Tree.commit tk_state commit_res.update_path [] group_context) in
        (commit_secret, (|li, new_state|))
      )
    in
    new_head::new_tail
#pop-options

#push-options " --ifuel 1 --fuel 1"
val update_leaf: #bytes:Type0 -> {|crypto_bytes bytes|} -> rand_state -> mls_state bytes -> nat -> ML (rand_state & mls_state bytes)
let update_leaf #bytes #cb rng st leaf_index =
  let commiter_state = get_state st.states leaf_index in
  let (rng, prepare_rand) = gen_rand_randomness rng (prepare_create_commit_entropy_lengths bytes) in
  let (rng, finalize_rand) = gen_rand_randomness rng (finalize_create_commit_entropy_lengths commiter_state []) in
  let group_context: group_context_nt bytes =
    if not (st.epoch < pow2 64) then failwith "update_leaf: epoch too big" else {
    version = PV_mls10;
    cipher_suite = available_ciphersuite_to_network (ciphersuite #bytes);
    group_id = empty #bytes;
    epoch = st.epoch;
    tree_hash = empty #bytes;
    confirmed_transcript_hash = empty #bytes;
    extensions = [];
  } in
  let commit_result =
    let (pending, _) = extract_result (prepare_create_commit commiter_state prepare_rand) in
    extract_result (finalize_create_commit pending [] group_context finalize_rand)
  in
  let commit_secrets, new_states = List.Tot.unzip (process_update st.states commit_result group_context) in
  let first_commit_secret = List.hd commit_secrets in
  if not (List.Tot.for_all ((=) first_commit_secret) commit_secrets) then
    failwith "update_leaf: inconsistent commit_secrets"
  ;
  (rng, {
    epoch = st.epoch+1;
    states = new_states;
  })
#pop-options

val update_rand: #bytes:Type0 -> {|crypto_bytes bytes|} -> rand_state -> mls_state bytes -> ML (rand_state & mls_state bytes)
let update_rand #bytes #cb rng st =
  let (rng, i) = gen_rand_num_ml rng (List.Tot.length st.states) in
  let (|leaf_index, _|) = List.Tot.index st.states i in
  update_leaf rng st leaf_index

#push-options " --ifuel 1 --fuel 1"
val do_remove_leaf: #bytes:Type0 -> {|crypto_bytes bytes|} -> nat -> list (leaf_ind:nat & treekem_tree_state bytes leaf_ind) -> ML (list (leaf_ind:nat & treekem_tree_state bytes leaf_ind))
let rec do_remove_leaf #bytes #cb removed_ind l =
  match l with
  | [] -> []
  | (|leaf_ind, tk_state|)::t ->
    let new_tail = do_remove_leaf removed_ind t in
    if not (removed_ind < pow2 tk_state.levels) then failwith "do_remove_leaf: bad remove index" else
    if leaf_ind = removed_ind then
      new_tail
    else
      (|leaf_ind, MLS.TreeKEM.API.Tree.remove tk_state removed_ind|)::new_tail
#pop-options

#push-options " --ifuel 1"
val remove_leaf: #bytes:Type0 -> {|crypto_bytes bytes|} -> mls_state bytes -> nat -> ML (mls_state bytes)
let remove_leaf #bytes #cb st leaf_index =
  {
    epoch = st.epoch+1;
    states = do_remove_leaf leaf_index st.states;
  }
#pop-options

val remove_rand: #bytes:Type0 -> {|crypto_bytes bytes|} -> rand_state -> mls_state bytes -> ML (rand_state & mls_state bytes)
let remove_rand #bytes #cb rng st =
  let (rng, i) = gen_rand_num_ml rng (List.Tot.length st.states) in
  let (|leaf_index, _|) = List.Tot.index st.states i in
  (rng, remove_leaf st leaf_index)

#push-options "--fuel 0 --ifuel 1"
val apply_random_operation: #bytes:Type0 -> {|crypto_bytes bytes|} -> state bytes -> ML (state bytes)
let apply_random_operation #bytes #cb st =
  let rng = st.rng in
  let (rng, op) =
    if 2 <= List.Tot.length st.mls.states then (
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
    {rng; mls; test={st.test with n_add = st.test.n_add - 1}}
  )
  | Update -> (
    let (rng, mls) = update_rand rng st.mls in
    {rng; mls; test={st.test with n_update = st.test.n_update - 1}}
  )
  | Remove -> (
    let (rng, mls) = remove_rand rng st.mls in
    {rng; mls; test={st.test with n_remove = st.test.n_remove - 1}}
  )
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
  let (rng, leaf_secret) = gen_rand_bytes #bytes rng (hpke_private_key_length #bytes) in
  let (hpke_sk, hpke_pk) = extract_result (hpke_gen_keypair #bytes leaf_secret) in
  (rng, ({
    epoch = 0;
    states = [(|0, MLS.TreeKEM.API.Tree.create hpke_sk hpke_pk|)]
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
  let (_: state bytes) = foldn (avg_n_participant + n_remove + n_update + n_remove) apply_random_operation init_state in
  ()
#pop-options

val custom_test_1: {|crypto_bytes bytes|} -> ML unit
let custom_test_1 #cb =
  let (rng, st) = create_init_state #bytes 0 in
  let (rng, st) = add_rand rng st in
  let (rng, st) = add_rand rng st in
  let (rng, st) = add_rand rng st in
  let (rng, st) = add_rand rng st in
  let (rng, st) = update_leaf rng st 1 in
  let (rng, st) = update_leaf rng st 2 in
  let (rng, st) = update_leaf rng st 3 in
  let (rng, st) = update_leaf rng st 4 in
  let st = remove_leaf st 2 in
  let (rng, st) = update_leaf rng st 1 in
  let (rng, st) = add_rand rng st in
  let (rng, st) = update_leaf rng st 4 in
  ()

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
