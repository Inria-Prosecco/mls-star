module Lib.Result
open Lib.Sequence


#set-options "--z3rlimit_factor 2"

type result 'a =
  | Success: v:'a -> result 'a
  | Error: string -> result 'a

let return (a:'a) : result 'a = Success a

let bind (a:result 'a) (f:'a -> result 'b) : result 'b =
  match a with
  | Error x -> Error x
  | Success x -> f x

let failure (e:string) : FStar.All.ML unit =
  IO.print_newline ();
  IO.print_string "Failure ! ";
  IO.print_string e
