module MLS.Utils

type nat_less (m:nat) = n:nat{n<m}

val find_index:
  #a:eqtype ->
  skips:list a -> a -> l:list a ->
  option (nat_less (List.Tot.length l))
let rec find_index #a skips x l =
  match l with
  | [] -> None
  | h::t ->
    if List.Tot.mem h skips then
      match find_index skips x t with
      | Some res -> Some res
      | None -> None
    else if x=h then (
      Some 0
    ) else (
      match find_index skips x t with
      | Some res -> Some (res+1)
      | None -> None
    )

#push-options "--fuel 1 --ifuel 1"
val find_first:
  #a:Type ->
  (a -> bool) -> l:list a ->
  option (n:nat{n < List.Tot.length l})
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
#pop-options
