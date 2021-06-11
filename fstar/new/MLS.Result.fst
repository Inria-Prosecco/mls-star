module MLS.Result
open Lib.Sequence


#set-options "--z3rlimit_factor 2"

type result 'a =
  | Success: v:'a -> result 'a
  | Error: string -> result 'a

let return (a:'a) : result 'a = Success a
let fail (#a:Type) (s:string): result a = Error s

let bind (a:result 'a) (f:'a -> result 'b) : result 'b =
  match a with
  | Error x -> Error x
  | Success x -> f x

let from_option (s:string) (x:option 'a): result 'a =
  match x with
  | None -> Error s
  | Some x -> Success x

let rec mapM (f:('a -> result 'b)) (l:list 'a): result (list 'b) =
  match l with
  | [] -> Success []
  | h::t ->
    fh <-- f h;
    ft <-- mapM f t;
    return (fh::ft)

let failure (e:string) : FStar.All.ML unit =
  IO.print_newline ();
  IO.print_string "Failure ! ";
  IO.print_string e
