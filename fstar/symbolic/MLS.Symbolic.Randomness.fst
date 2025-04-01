module MLS.Symbolic.Randomness

open FStar.List
open Comparse
open DY.Core
open MLS.Crypto
open MLS.Symbolic

type randomness_ghost_data = list (usage & label)

#push-options "--ifuel 1"
val randomness_has_ghost_data:
  {|crypto_invariants|} ->
  #l:list nat ->
  trace ->
  randomness bytes l -> ldata:randomness_ghost_data ->
  Tot prop
let rec randomness_has_ghost_data #cinvs #l tr rand ldata =
  match l, ldata with
  | [], [] -> True
  | h::t, (usg,lab)::tdata -> (
    let (rand_cur, rand_next) = dest_randomness (rand <: randomness bytes (h::t)) in
    bytes_invariant tr rand_cur /\
    rand_cur `has_usage tr` usg /\
    get_label tr rand_cur == lab /\
    randomness_has_ghost_data tr rand_next tdata
  )
  | _, _ -> False
#pop-options

#push-options "--ifuel 1 --fuel 1"
val split_randomness_ghost_data_lemma:
  {|crypto_invariants|} ->
  #l1:list nat -> #l2:list nat ->
  tr:trace ->
  rand:randomness bytes (l1@l2) ->
  rand1:randomness bytes l1 -> rand2:randomness bytes l2 ->
  ldata1:randomness_ghost_data -> ldata2:randomness_ghost_data ->
  Lemma
  (requires
    rand `randomness_has_ghost_data tr` (ldata1@ldata2) /\
    List.Tot.length ldata1 == List.Tot.length l1 /\
    (rand1, rand2) == split_randomness rand
  )
  (ensures (
    rand1 `randomness_has_ghost_data tr` ldata1 /\
    rand2 `randomness_has_ghost_data tr` ldata2
  ))
let rec split_randomness_ghost_data_lemma #cinvs #l1 #l2 tr rand rand1 rand2 ldata1 ldata2 =
  match l1, ldata1 with
  | [], [] -> ()
  | h1::t1, hdata::tdata -> (
    let (rh, rt) = dest_randomness (rand <: randomness bytes (h1::(t1@l2))) in
    let (rt1, rl2) = split_randomness rt in
    split_randomness_ghost_data_lemma tr rt rt1 rl2 tdata ldata2;
    dest_mk_randomness (rh, rt1)
  )
#pop-options

val generate_randomness:
  #l:list nat ->
  ldata:randomness_ghost_data{List.Tot.length ldata == List.Tot.length l} ->
  traceful (randomness bytes l)
let rec generate_randomness #l ldata =
  match l, ldata with
  | [], [] -> return (mk_empty_randomness bytes)
  | h::t, (usg, lab)::tdata -> (
    assume(h <> 0);
    let* rand_cur = mk_rand usg lab h in
    let* rand_next = generate_randomness #t tdata in
    assume(length rand_cur == h);
    return (mk_randomness ((rand_cur <: lbytes bytes h), rand_next))
  )

#push-options "--ifuel 1 --fuel 1"
val generate_randomness_proof:
  {|protocol_invariants|} ->
  #l:list nat ->
  ldata:randomness_ghost_data{List.Tot.length ldata == List.Tot.length l} ->
  tr:trace ->
  Lemma
  (requires trace_invariant tr)
  (ensures (
    let (rand, tr_out) = generate_randomness #l ldata tr in
    rand `randomness_has_ghost_data tr_out` ldata /\
    trace_invariant tr_out
  ))
let rec generate_randomness_proof #invs #l ldata tr =
  match l, ldata with
  | [], [] -> ()
  | h::t, (usg, lab)::tdata -> (
    assume(h <> 0);
    let (rand_cur, tr) = mk_rand usg lab h tr in
    generate_randomness_proof #_ #t tdata tr;
    let (rand_next, tr) = generate_randomness #t tdata tr in
    assume(length rand_cur == h);
    dest_mk_randomness ((rand_cur <: lbytes bytes h), rand_next)
  )
#pop-options
