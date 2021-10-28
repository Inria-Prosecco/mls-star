module MLS.Result
open Lib.Sequence


#set-options "--z3rlimit_factor 2"

type result 'a =
  | Success: v:'a -> result 'a
  | InternalError: string -> result 'a
  | ProtocolError: string -> result 'a

let return (a:'a) : result 'a = Success a
let internal_failure (#a:Type) (s:string): result a = InternalError s
let error (#a:Type) (s:string): result a = ProtocolError s

//TODO unfold? (to remove all the lambdas in the spec and in the generated code)
let bind (a:result 'a) (f:'a -> result 'b) : result 'b =
  match a with
  | Success x -> f x
  | InternalError x -> InternalError x
  | ProtocolError x -> ProtocolError x

let from_option (s:string) (x:option 'a): result 'a =
  match x with
  | None -> ProtocolError s
  | Some x -> Success x

let rec mapM (f:('a -> result 'b)) (l:list 'a): result (list 'b) =
  match l with
  | [] -> return []
  | h::t ->
    fh <-- f h;
    ft <-- mapM f t;
    return (fh::ft)

let rec fold_leftM (f:'a -> 'b -> result 'a) (x:'a) (l:list 'b): Tot (result 'a) (decreases l) =
  match l with
  | [] -> return x
  | h::t ->
    new_x <-- f x h;
    fold_leftM f new_x t
