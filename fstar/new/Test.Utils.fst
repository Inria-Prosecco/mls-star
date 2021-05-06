module Test.Utils

open FStar.IO
open FStar.All
open Lib.ByteSequence
open Lib.Result
open FStar.String
open Crypto

val digit_to_string: n:nat{n<10} -> string
let digit_to_string n =
  match n with
  | 0 -> "0"
  | 1 -> "1"
  | 2 -> "2"
  | 3 -> "3"
  | 4 -> "4"
  | 5 -> "5"
  | 6 -> "6"
  | 7 -> "7"
  | 8 -> "8"
  | 9 -> "9"

val nat_to_string: nat -> string
let rec nat_to_string n =
  if n < 10 then
    digit_to_string n
  else
    nat_to_string (n/10) ^ digit_to_string (n % 10)

val option_to_string: #a:Type -> (a -> string) -> option a -> string
let option_to_string #a to_str x =
  match x with
  | Some y -> "Some (" ^ (to_str y) ^ ")"
  | None -> "None"

val list_to_string: #a:Type -> (a -> string) -> list a -> string
let list_to_string #a to_str l =
  let rec aux l =
    match l with
    | [] -> ""
    | [x] -> to_str x
    | h::t -> to_str h ^ "; " ^ aux t
  in
  "[" ^ aux l ^ "]"

val string_to_string: string -> string
let string_to_string s = s

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

val hex_digit_to_hex_string: n:nat{n<16} -> string
let hex_digit_to_hex_string n =
  match n with
  | 0 -> "0"
  | 1 -> "1"
  | 2 -> "2"
  | 3 -> "3"
  | 4 -> "4"
  | 5 -> "5"
  | 6 -> "6"
  | 7 -> "7"
  | 8 -> "8"
  | 9 -> "9"
  | 10 -> "A"
  | 11 -> "B"
  | 12 -> "C"
  | 13 -> "D"
  | 14 -> "E"
  | 15 -> "F"

val byte_to_hex_string: n:nat{n<256} -> string
let byte_to_hex_string n =
  (hex_digit_to_hex_string (n/16)) ^ (hex_digit_to_hex_string (n%16))

val bytes_to_hex_string: bytes -> string
let bytes_to_hex_string b =
  let open Lib.IntTypes in
  FStar.String.concat "" (List.Tot.map (fun x -> byte_to_hex_string (v x)) (FStar.Seq.seq_to_list b))

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

val hex_string_to_bytes: string -> ML bytes
let rec hex_string_to_bytes s =
  let open Lib.IntTypes in
  if strlen s = 0 then
    Seq.empty
  else if strlen s = 1 then
    failwith "string_to_bytes: size is not a multiple of two"
  else (
    let s0 = String.sub s 0 2 in
    let ss = String.sub s 2 (strlen s - 2) in
    let cur_digit = hex_string_to_byte s0 in
    let b0 = u8 cur_digit in
    let bs = hex_string_to_bytes ss in
    Seq.append (Seq.create 1 b0) bs
  )

val extract_option: #a:Type -> string -> option a -> ML a
let extract_option s x =
  match x with
  | Some y -> y
  | None -> failwith s

val extract_result: #a:Type -> result a -> ML a
let extract_result x =
  match x with
  | Success y -> y
  | Error s -> failwith s

val uint16_to_ciphersuite: UInt16.t -> ML (result ciphersuite)
let uint16_to_ciphersuite x =
  let open Lib.IntTypes in
  let open Parser in
  let open NetworkTypes in
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
