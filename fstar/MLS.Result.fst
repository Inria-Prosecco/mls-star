module MLS.Result

#set-options "--fuel 0 --ifuel 0"

type result 'a =
  | Success: v:'a -> result 'a
  | InternalError: string -> result 'a
  | ProtocolError: string -> result 'a

let return (a:'a) : result 'a = Success a
let internal_failure (#a:Type) (s:string): result a = InternalError s
let error (#a:Type) (s:string): result a = ProtocolError s

#push-options "--ifuel 1"
//TODO unfold? (to remove all the lambdas in the spec and in the generated code)
let bind (a:result 'a) (f:'a -> result 'b) : result 'b =
  match a with
  | Success x -> f x
  | InternalError x -> InternalError x
  | ProtocolError x -> ProtocolError x
#pop-options

let from_option (s:string) (x:option 'a): result 'a =
  match x with
  | None -> ProtocolError s
  | Some x -> Success x

#push-options "--ifuel 1 --fuel 1"
let rec mapM (f:('a -> result 'b)) (l:list 'a): result (res:list 'b{List.Tot.length res == List.Tot.length l}) =
  match l with
  | [] -> return []
  | h::t ->
    fh <-- f h;
    ft <-- mapM f t;
    return #(res:list 'b{List.Tot.length res == List.Tot.length l}) (fh::ft)
#pop-options

#push-options "--ifuel 1 --fuel 1"
let rec fold_leftM (f:'a -> 'b -> result 'a) (x:'a) (l:list 'b): Tot (result 'a) (decreases l) =
  match l with
  | [] -> return x
  | h::t ->
    new_x <-- f x h;
    fold_leftM f new_x t
#pop-options
