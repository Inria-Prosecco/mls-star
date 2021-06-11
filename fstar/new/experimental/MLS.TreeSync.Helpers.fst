module MLS.TreeSync.Helpers

open MLS.Lib.Array
open MLS.Lib.Maths
open MLS.TreeSync

///
/// Auxiliary
///
let rec mk_path_aux (l:nat) (i:index_n l) (sonp:Seq.seq (option node_package_t){l <= length sonp+1})
                    (olp:option leaf_package_t): path_t l =
   if l = 0 then PLeaf olp
   else
     let (j,dir) = child_index l i in
     PNode None (mk_path_aux (l-1) j sonp olp)


///
/// Helpers
///

(** Definition of an array of leaf packages *)
type leaf_array_t (sz:nat) = a:array (option leaf_package_t){length a = sz}

(** Retreives the array of leaf packages from the tree *)
let rec tree_leaf_packages (l:nat) (t:tree_t l): leaf_array_t (pow2 l) =
  match t with
  | Leaf _ olp ->
    (match olp with
    | None -> singleton None
    | Some lp -> singleton (Some lp))
  | Node _ _ left right -> append (tree_leaf_packages (l-1) left)
				 (tree_leaf_packages (l-1) right)

(** Retreives the array of leaf packages from the state *)
val leaf_packages: st:state_t -> leaf_array_t (max_size st)
let leaf_packages st = tree_leaf_packages st.st_levels st.st_tree


(** Create a path for from a sequence of node packages *)
val mk_path: l:nat -> Seq.seq (option node_package_t) -> option leaf_package_t
  -> Tot (option (path_t l))

let rec mk_path l sonp olp =
  if l = 0 || length sonp + 1 <> l then None
  else Some (mk_path_aux l 0 sonp olp)
