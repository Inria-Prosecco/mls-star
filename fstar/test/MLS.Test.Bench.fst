module MLS.Test.Bench

open FStar.All
open Comparse
open MLS.Crypto
open MLS.Test.Bench.Time
open MLS.Test.Utils
open MLS.NetworkTypes
open MLS.StringUtils
open MLS

#set-options "--fuel 1 --ifuel 1"

type bench_config = {
  name: string;
  n_message_rounds: nat;
  max_n_members: nat;
  do_removes: bool;
}

val guard: b:bool -> ML (squash b)
let guard b =
  if b then ()
  else failwith "guard failed"

type ident = {
  key_package: bytes;
  key_package_hash: bytes;
  leaf_secret: bytes;
  cred: credential;
  sign_pub: bytes;
  sign_priv: bytes;
}

val mk_mls_bytes: bytes -> ML (mls_bytes bytes)
let mk_mls_bytes b =
  if length b < pow2 30 then b
  else failwith "mk_mls_bytes: too long"

val mk_id: nat -> ML identity
let mk_id i =
  let id_string = "Alice" ^ nat_to_string i in
  guard (string_is_ascii id_string);
  mk_mls_bytes (string_to_bytes #bytes id_string)

val gen_key_package: rand_state -> nat -> ML (rand_state & ident)
let gen_key_package rng i =
  let (rng, e_sign) = gen_rand_bytes #bytes rng 32 in
  let (rng, e_kp) = gen_rand_bytes #bytes rng 64 in
  assume(forall b. length #bytes b == Seq.length b);
  assume(sign_public_key_length #bytes < pow2 30);
  let (sign_pub, sign_priv) = extract_result (fresh_key_pair e_sign) in
  assume(string_is_ascii (nat_to_string i));
  let cred = {signature_key = sign_pub; identity = mk_id i} in
  let (key_package, key_package_hash, leaf_secret) = extract_result (fresh_key_package e_kp cred sign_priv) in
  let id = {key_package; key_package_hash; leaf_secret; cred; sign_pub; sign_priv;} in
  (rng, id)

val receive_message: (outcome -> bool) -> list state -> bytes -> ML (list state)
let rec receive_message check l msg =
  match l with
  | [] -> []
  | st::t ->
    let (st, outcome) = extract_result (process_group_message st msg) in
    if check outcome then
      st::(receive_message check t msg)
    else
      failwith "receive_message: bad outcome"

val update: #a:Type0 -> l:list a -> i:nat{i < List.Tot.length l} -> a -> list a
let rec update #a l i x =
  match l with
  | h::t ->
    if i = 0 then x::t
    else h::(update t (i-1) x)

val delete: #a:Type0 -> l:list a -> i:nat{i < List.Tot.length l} -> list a
let rec delete #a l i =
  match l with
  | h::t ->
    if i = 0 then t
    else h::(delete t (i-1))

val send_one_message: rand_state -> list state -> nat -> ML (rand_state & list state)
let send_one_message rng l i =
  assume(forall b. length #bytes b == Seq.length b);
  if not (i < List.Tot.length l) then failwith ""
  else (
    let sender_state = List.Tot.index l i in
    let (rng, e) = gen_rand_bytes #bytes rng 4 in
    let (new_sender_state, (_, msg)) = extract_result (send sender_state e (string_to_bytes #bytes "Lorem ipsum dolor sit amet.")) in
    let l = update l i new_sender_state in
    let l = receive_message (MsgData?) l msg in
    (rng, l)
  )

val send_one_message_round: rand_state -> list state -> nat -> ML (rand_state & list state)
let rec send_one_message_round rng l i =
  if i >= List.Tot.length l then (rng, l)
  else (
    let (rng, l) = send_one_message rng l i in
    let (rng, l) = send_one_message_round rng l (i+1) in
    (rng, l)
  )

val send_n_messages_round: bench_config -> rand_state -> list state -> nat -> ML (rand_state & list state)
let rec send_n_messages_round conf rng l i =
  if i >= conf.n_message_rounds then (rng, l)
  else (
    let (rng, l) = send_one_message_round rng l 0 in
    let (rng, l) = send_n_messages_round conf rng l (i+1) in
    (rng, l)
  )

val add_one: rand_state -> list state -> ML (rand_state & list state)
let add_one rng l =
  assume(forall b. length #bytes b == Seq.length b);
  let (rng, new_id) = gen_key_package rng (List.Tot.length l) in
  guard (Cons? l);
  let last_st = List.Tot.last l in
  let (rng, e) = gen_rand_bytes #bytes rng (4+256) in
  let (last_st, ((_, msg), welcome_msg)) = extract_result (add last_st new_id.key_package e) in
  let l = update l (List.Tot.length l - 1) last_st in
  let l = receive_message (MsgAdd?) l msg in
  guard (length new_id.sign_pub = sign_public_key_length #bytes);
  guard (length new_id.sign_priv = sign_private_key_length #bytes);
  let (_, new_st) = extract_result (process_welcome_message welcome_msg (new_id.sign_pub, new_id.sign_priv) (fun _ -> Some (new_id.leaf_secret))) in
  let l = l@[new_st] in
  (rng, l)

val one_bench_round: bench_config -> rand_state -> list state -> ML (rand_state & list state)
let one_bench_round conf rng l =
  let (rng, l) = send_n_messages_round conf rng l 0 in
  let (rng, l) = add_one rng l in
  (rng, l)

val n_bench_rounds: bench_config -> rand_state -> list state -> ML (rand_state & list state)
let rec n_bench_rounds conf rng l =
  if List.Tot.length l >= conf.max_n_members then (rng, l)
  else (
    let (rng, l) = one_bench_round conf rng l in
    let (rng, l) = n_bench_rounds conf rng l in
    (rng, l)
  )

val remove_one_odd: rand_state -> nat -> list state -> ML (rand_state & list state)
let remove_one_odd rng i l =
  guard (i%2 = 1);
  guard (Cons? l);
  let first_st::_ = l in
  let (rng, e) = gen_rand_bytes #bytes rng (4+256) in
  let (first_st, (_, msg)) = extract_result (remove first_st (mk_id i) e) in
  let l = update l 0 first_st in
  guard (i < List.Tot.length l);
  let l = delete l i in
  let l = receive_message (MsgRemove?) l msg in
  (rng, l)

val remove_odds_aux: bench_config -> rand_state -> nat -> list state -> ML (rand_state & list state)
let rec remove_odds_aux conf rng i l =
  if i = 0 then (rng, l)
  else if i%2 = 0 then
    remove_odds_aux conf rng (i-1) l
  else (
    let (rng, l) = send_n_messages_round conf rng l 0 in
    let (rng, l) = remove_one_odd rng i l in
    remove_odds_aux conf rng (i-1) l
  )

val remove_odds: bench_config -> rand_state -> list state -> ML (rand_state & list state)
let remove_odds conf rng l =
  guard (Cons? l);
  remove_odds_aux conf rng (List.Tot.length l - 1) l

val bench: bench_config -> ML unit
let bench conf =
  let t = tic () in
  assume(forall b. length #bytes b == Seq.length b);
  assume(group_id == bytes);
  let rng = init_rand_state 0xFEEDC0FFEE in
  let (rng, e) = gen_rand_bytes #bytes rng 96 in
  let (rng, gid) = gen_rand_bytes #bytes rng 16 in
  let (rng, id) = gen_key_package rng 0 in
  guard (length id.sign_priv = sign_private_key_length #bytes);
  let init_state = extract_result (create e id.cred id.sign_priv gid) in
  let (rng, l) = n_bench_rounds conf rng [init_state] in
  let (rng, l) =
    if conf.do_removes then (
      let (rng, l) = remove_odds conf rng l in
      let (rng, l) = n_bench_rounds conf rng l in
      (rng, l)
    ) else (rng, l)
  in
  let elapsed = tac t in
  FStar.IO.print_string ("Benchmark (" ^ conf.name ^ "): " ^ elapsed ^ "\n")
