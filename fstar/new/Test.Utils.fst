module Test.Utils

open FStar.IO
open FStar.All

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
