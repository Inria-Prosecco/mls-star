open Prims
(* Following FStarLang/FStar#3637 FStar_Range is reserved for plugins *)
(* However it is used by the HACL* snapshot for some reason *)
(* Emulating the minimal interface here *)
type ('a, 'b, 'c) labeled = unit
type range = unit
let mk_range (s:string) (i1:int) (i2:int) (i3:int) (i4:int): range = ()
