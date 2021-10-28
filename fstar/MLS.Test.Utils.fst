module MLS.Test.Utils

open FStar.IO
open FStar.All
open Lib.IntTypes
open Lib.ByteSequence
open MLS.Result
open FStar.String
open MLS.Crypto
open MLS.StringUtils

val check_equal: #a:eqtype -> string -> (a -> string) -> a -> a -> ML bool
let check_equal #a name to_str x y =
  if x = y then (
    true
  ) else (
    IO.print_string "check_equal ";
    IO.print_string name;
    IO.print_string ": expected '";
    IO.print_string (to_str x);
    IO.print_string "', got '";
    IO.print_string (to_str y);
    IO.print_string "'\n";
    false
  )

val test_list_aux: #a:Type -> string -> (a -> ML bool) -> nat -> list a -> ML bool
let rec test_list_aux #a test_name test n l =
  match l with
  | [] -> true
  | h::t ->
    if test h then (
      test_list_aux test_name test (n+1) t
    ) else (
      IO.print_string test_name;
      IO.print_string ": failed test ";
      IO.print_string (nat_to_string n);
      IO.print_newline ();
      false
    )

val test_list: #a:Type -> string -> (a -> ML bool) -> list a -> ML bool
let test_list #a test_name test l =
  test_list_aux test_name test 0 l

val hex_string_to_hex_digit: s:string{strlen s == 1} -> ML (n:nat{n<16})
let hex_string_to_hex_digit s =
  if s = "0" then 0
  else if s = "1" then 1
  else if s = "2" then 2
  else if s = "3" then 3
  else if s = "4" then 4
  else if s = "5" then 5
  else if s = "6" then 6
  else if s = "7" then 7
  else if s = "8" then 8
  else if s = "9" then 9
  else if s = "A" then 10
  else if s = "B" then 11
  else if s = "C" then 12
  else if s = "D" then 13
  else if s = "E" then 14
  else if s = "F" then 15
  else failwith "string_to_hex_digit: digit is not in [0-9A-F]"

val hex_string_to_byte: s:string{strlen s == 2} -> ML (n:nat{n<256})
let hex_string_to_byte s =
  let open FStar.Mul in
  let d1 = hex_string_to_hex_digit (String.sub s 0 1) in
  let d2 = hex_string_to_hex_digit (String.sub s 1 1) in
  16*d1 + d2

//We do recursion on lists, because recursing on a string is slow
val hex_list_char_to_list_u8: list char -> ML (list Lib.IntTypes.uint8)
let rec hex_list_char_to_list_u8 l =
  let open Lib.IntTypes in
  match l with
  | [] -> []
  | [h] -> failwith "string_to_bytes: size is not a multiple of two"
  | h1::h2::t ->
    list_of_string_of_list [h1; h2];
    let cur_digit = hex_string_to_byte (string_of_list [h1; h2]) in
    let b0 = u8 cur_digit in
    let bs = hex_list_char_to_list_u8 t in
    b0::bs

val hex_string_to_bytes: string -> ML bytes
let hex_string_to_bytes s =
  //For some reason, introducing this let helps F*'s type system
  let res = hex_list_char_to_list_u8 (list_of_string s) in
  Seq.seq_of_list res

val extract_option: #a:Type -> string -> option a -> ML a
let extract_option s x =
  match x with
  | Some y -> y
  | None -> failwith s

val extract_result: #a:Type -> result a -> ML a
let extract_result x =
  match x with
  | Success y -> y
  | ProtocolError s -> failwith ("Protocol error: " ^ s)
  | InternalError s -> failwith ("Internal error (this shouldn't be possible!): " ^ s)

val uint16_to_ciphersuite: UInt16.t -> ML (result ciphersuite)
let uint16_to_ciphersuite x =
  let open Lib.IntTypes in
  let open MLS.Parser in
  let open MLS.NetworkTypes in
  let cs_bytes = (ps_u16.serialize (u16 (FStar.UInt16.v x))) in
  let o_cs_nt = (ps_to_pse ps_cipher_suite).parse_exact cs_bytes in
  match o_cs_nt with
  | None -> failwith "couldn't parse ciphersuite"
  | Some cs_nt -> ciphersuite_from_nt cs_nt

val find_first: #a:Type -> (a -> bool) -> l:list a -> option (n:nat{n < List.Tot.length l})
let rec find_first #a p l =
  match l with
  | [] -> None
  | h::t ->
    if p h then (
      Some 0
    ) else (
      match find_first p t with
      | Some v -> Some (v+1)
      | None -> None
    )

type rand_state = {
  internal_state: (x:nat{x < pow2 64});
}

// Stupid linear congruential generator
val init_rand_state: seed:nat -> rand_state
let init_rand_state seed =
  { internal_state = (seed % (pow2 64)) }

#push-options "--z3rlimit 10"
val gen_rand_bits: rand_state -> n_bits:pos{n_bits <= 64} -> rand_state & (x:nat{x<pow2 n_bits})
let gen_rand_bits st n_bits =
  let open FStar.Mul in
  let res = (6364136223846793005 * st.internal_state + 1442695040888963407)%(pow2 64) in
  FStar.Math.Lemmas.lemma_div_lt res 64 (64 - n_bits);
  ({internal_state = res}, res / (pow2 (64 - n_bits)))
#pop-options

val gen_rand_bytes_aux: rand_state -> size:nat -> Tot (rand_state & res:list uint8{List.Tot.length res == size}) (decreases size)
let rec gen_rand_bytes_aux rng size =
  if size = 0 then
    (rng, [])
  else (
    let (rng, head) = gen_rand_bits rng 8 in
    let (rng, tail) = gen_rand_bytes_aux rng (size-1) in
    (rng, (u8 head)::tail)
  )

val gen_rand_bytes: rand_state -> size:nat -> rand_state & res:bytes{Seq.length res == size}
let gen_rand_bytes rng size =
  let (rng, l) = gen_rand_bytes_aux rng size in
  (rng, Seq.seq_of_list l)

val get_n_bits_aux: x:nat{x<=pow2 64} -> cur:nat{pow2 cur < x /\ cur < 64} -> Tot (res:nat{res <= 64 /\ x <= pow2 res}) (decreases 64-cur)
let rec get_n_bits_aux x cur =
  if x <= pow2 (cur+1) then
    cur+1
  else
    get_n_bits_aux x (cur+1)

val get_n_bits: x:nat{2 <= x /\ x <= pow2 64} -> res:nat{res <= 64 /\ x <= pow2 res}
let get_n_bits x =
  get_n_bits_aux x 0

val gen_rand_num: rand_state -> upper_bound:pos{upper_bound < pow2 64} -> Dv (rand_state & (x:nat{x < upper_bound}))
let rec gen_rand_num st upper_bound =
  if upper_bound = 1 then
    (st, 0)
  else
    let n_bits = get_n_bits upper_bound in
    let (st, res) = gen_rand_bits st n_bits in
    if res < upper_bound then
      (st, res)
    else
      gen_rand_num st upper_bound

val gen_rand_num_ml: rand_state -> upper_bound:nat -> ML (rand_state & (x:nat{x < upper_bound}))
let gen_rand_num_ml st upper_bound =
  if not (1 <= upper_bound) then failwith "gen_rand_num_ml: upper_bound = 0" else
  if not (upper_bound < pow2 64) then failwith "gen_rand_num_ml: upper_bound >= pow2 64" else
  gen_rand_num st upper_bound
