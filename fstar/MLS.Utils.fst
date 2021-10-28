module MLS.Utils

type nat_less (m:nat) = n:nat{n<m}

val find_index: #a:eqtype -> skips:list a -> a -> l:list a -> option (nat_less (List.Tot.length l))
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

val insert_sorted: nat -> list nat -> list nat
let rec insert_sorted x l =
  match l with
  | [] -> [x]
  | h::t ->
    if x < h then
      x::l
    else if x = h then
      l
    else
      h::(insert_sorted x t)

#push-options "--fuel 1 --ifuel 1"
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
#pop-options
