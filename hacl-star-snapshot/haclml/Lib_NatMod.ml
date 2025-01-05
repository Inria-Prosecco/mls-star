open Prims
let (mk_nat_comm_monoid :
  Prims.int Lib_Exponentiation_Definition.comm_monoid) =
  {
    Lib_Exponentiation_Definition.one = Prims.int_one;
    Lib_Exponentiation_Definition.mul = ( * );
    Lib_Exponentiation_Definition.lemma_one = ();
    Lib_Exponentiation_Definition.lemma_mul_assoc = ();
    Lib_Exponentiation_Definition.lemma_mul_comm = ()
  }
let rec (pow : Prims.int -> Prims.nat -> Prims.int) =
  fun x ->
    fun n ->
      if n = Prims.int_zero
      then Prims.int_one
      else x * (pow x (n - Prims.int_one))
type 'm nat_mod = Prims.nat
let (one_mod : Prims.pos -> unit nat_mod) = fun m -> Prims.int_one mod m
let (mul_mod : Prims.pos -> unit nat_mod -> unit nat_mod -> unit nat_mod) =
  fun m -> fun a -> fun b -> (a * b) mod m
let (add_mod : Prims.pos -> unit nat_mod -> unit nat_mod -> unit nat_mod) =
  fun m -> fun a -> fun b -> (a + b) mod m
let (sub_mod : Prims.pos -> unit nat_mod -> unit nat_mod -> unit nat_mod) =
  fun m -> fun a -> fun b -> (a - b) mod m
let (mk_nat_mod_comm_monoid :
  Prims.pos -> unit nat_mod Lib_Exponentiation_Definition.comm_monoid) =
  fun m ->
    {
      Lib_Exponentiation_Definition.one = (one_mod m);
      Lib_Exponentiation_Definition.mul = (mul_mod m);
      Lib_Exponentiation_Definition.lemma_one = ();
      Lib_Exponentiation_Definition.lemma_mul_assoc = ();
      Lib_Exponentiation_Definition.lemma_mul_comm = ()
    }
let rec (pow_mod_ : Prims.pos -> unit nat_mod -> Prims.nat -> unit nat_mod) =
  fun m ->
    fun a ->
      fun b ->
        if b = Prims.int_zero
        then Prims.int_one
        else
          if (b mod (Prims.of_int (2))) = Prims.int_zero
          then pow_mod_ m (mul_mod m a a) (b / (Prims.of_int (2)))
          else
            mul_mod m a (pow_mod_ m (mul_mod m a a) (b / (Prims.of_int (2))))
let (pow_mod : Prims.pos -> unit nat_mod -> Prims.nat -> unit nat_mod) =
  fun m -> fun a -> fun b -> pow_mod_ m a b
type prime = Prims.pos
let (inv_mod : Prims.pos -> unit nat_mod -> unit nat_mod) =
  fun m -> fun a -> pow_mod m a (m - (Prims.of_int (2)))
let (div_mod : Prims.pos -> unit nat_mod -> unit nat_mod -> unit nat_mod) =
  fun m -> fun a -> fun b -> mul_mod m a (inv_mod m b)