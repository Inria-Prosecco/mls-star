open Prims
let (for1 :
  FStar_UInt32.t ->
    FStar_UInt32.t -> unit -> (FStar_UInt32.t -> unit) -> unit)
  =
  fun start ->
    fun finish ->
      fun inv -> fun f -> C_Loops.for1 start finish () (fun i -> f i)
let while1 : 'inv . unit -> (unit -> Prims.bool) -> (unit -> unit) -> unit =
  fun guard ->
    fun test -> fun body -> let test1 = test in C_Loops.while1 test1 body
let (square_while : unit -> FStar_UInt32.t) =
  fun uu___ ->
    FStar_HyperStack_ST.push_frame ();
    (let l =
       [FStar_UInt32.uint_to_t Prims.int_one;
       FStar_UInt32.uint_to_t (Prims.of_int (2));
       FStar_UInt32.uint_to_t (Prims.of_int (3))] in
     let b = LowStar_Monotonic_Buffer.malloca_of_list l in
     let r =
       LowStar_Monotonic_Buffer.malloca
         (FStar_UInt32.uint_to_t Prims.int_zero)
         (FStar_UInt32.uint_to_t Prims.int_one) in
     let h = FStar_HyperStack_ST.get () in
     let h0 = FStar_HyperStack_ST.get () in
     Obj.magic (fun h1 -> ());
     Obj.magic
       (fun h1 ->
          FStar_UInt32.lt (Obj.magic ())
            (FStar_UInt32.uint_to_t (Prims.of_int (3))));
     (let test uu___3 =
        let uu___4 = LowStar_BufferOps.op_Bang_Star r in
        FStar_UInt32.lt uu___4 (FStar_UInt32.uint_to_t (Prims.of_int (3))) in
      C_Loops.while1 test
        (fun uu___3 ->
           (let uu___5 = LowStar_BufferOps.op_Bang_Star r in
            let uu___6 =
              let uu___7 =
                let uu___8 = LowStar_BufferOps.op_Bang_Star r in
                LowStar_Monotonic_Buffer.index b uu___8 in
              let uu___8 =
                let uu___9 = LowStar_BufferOps.op_Bang_Star r in
                LowStar_Monotonic_Buffer.index b uu___9 in
              FStar_UInt32.mul uu___7 uu___8 in
            let h1 = FStar_HyperStack_ST.get () in
            LowStar_Monotonic_Buffer.upd' b uu___5 uu___6);
           (let uu___5 =
              let uu___6 = LowStar_BufferOps.op_Bang_Star r in
              FStar_UInt32.add uu___6 (FStar_UInt32.uint_to_t Prims.int_one) in
            let h1 = FStar_HyperStack_ST.get () in
            LowStar_Monotonic_Buffer.upd' r
              (FStar_UInt32.uint_to_t Prims.int_zero) uu___5)));
     (let x =
        LowStar_Monotonic_Buffer.index b
          (FStar_UInt32.uint_to_t (Prims.of_int (2))) in
      FStar_HyperStack_ST.pop_frame (); x))