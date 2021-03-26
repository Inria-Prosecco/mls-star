module TreeSync.Helpers

open Lib.Array
open Lib.Maths
open TreeSync

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

(* Create a path for from a sequence of node packages *)
val mk_path: l:nat -> Seq.seq (option node_package_t) -> option leaf_package_t
  -> Tot (option (path_t l))

let rec mk_path l sonp olp =
  if l = 0 || length sonp + 1 <> l then None
  else Some (mk_path_aux l 0 sonp olp)

