module MLS.Result

#set-options "--fuel 0 --ifuel 0"

type result (a:Type) =
  | Success: v:a -> result a
  | InternalError: string -> result a
  | ProtocolError: string -> result a

val return: #a:Type -> a -> result a
let return #a x = Success x

val internal_failure: #a:Type -> s:string -> result a
let internal_failure #a s = InternalError s

val error: #a:Type -> s:string -> result a
let error #a s = ProtocolError s

#push-options "--ifuel 1"
//TODO unfold? (to remove all the lambdas in the spec and in the generated code)
val (let?): #a:Type -> #b:Type -> result a -> (a -> result b) -> result b
let (let?) #a #b rx f =
  match rx with
  | Success x -> f x
  | InternalError x -> InternalError x
  | ProtocolError x -> ProtocolError x
#pop-options

val from_option: #a:Type -> string -> option a -> result a
let from_option #a s x =
  match x with
  | None -> ProtocolError s
  | Some x -> Success x

#push-options "--ifuel 1 --fuel 1"
val mapM: #a:Type -> #b:Type -> (a -> result b) -> l:list a -> result (res:list b{List.Tot.length res == List.Tot.length l})
let rec mapM #a #b f l =
  match l with
  | [] -> return []
  | h::t ->
    let? fh = f h in
    let? ft = mapM f t in
    return #(res:list b{List.Tot.length res == List.Tot.length l}) (fh::ft)
#pop-options

#push-options "--ifuel 1 --fuel 1"
val fold_leftM: #a:Type -> #b:Type -> (a -> b -> result a) -> a -> list b -> result a
let rec fold_leftM #a #b f x l: Tot (result a) (decreases l) =
  match l with
  | [] -> return x
  | h::t ->
    let? new_x = f x h in
    fold_leftM f new_x t
#pop-options
