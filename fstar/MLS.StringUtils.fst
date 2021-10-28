module MLS.StringUtils

open Lib.ByteSequence

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
