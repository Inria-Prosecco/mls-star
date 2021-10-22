open Prims
type buftype =
  | MUT 
  | IMMUT 
  | CONST 
let (uu___is_MUT : buftype -> Prims.bool) =
  fun projectee -> match projectee with | MUT -> true | uu___ -> false
let (uu___is_IMMUT : buftype -> Prims.bool) =
  fun projectee -> match projectee with | IMMUT -> true | uu___ -> false
let (uu___is_CONST : buftype -> Prims.bool) =
  fun projectee -> match projectee with | CONST -> true | uu___ -> false
type ('ty, 'a) buffer_t = Obj.t
type 'a buffer = 'a LowStar_Buffer.buffer
type 'a ibuffer = 'a LowStar_ImmutableBuffer.ibuffer
type 'a cbuffer = 'a LowStar_ConstBuffer.const_buffer
type 'a gbuffer = 'a LowStar_ConstBuffer.const_buffer

let to_const : 'a . buftype -> Obj.t -> 'a LowStar_ConstBuffer.const_buffer =
  fun uu___1 ->
    fun uu___ ->
      (fun t ->
         fun b ->
           match t with
           | MUT ->
               Obj.magic
                 (Obj.repr (LowStar_ConstBuffer.of_buffer (Obj.magic b)))
           | IMMUT ->
               Obj.magic
                 (Obj.repr (LowStar_ConstBuffer.of_ibuffer (Obj.magic b)))
           | CONST -> Obj.magic (Obj.repr b)) uu___1 uu___
let const_to_buffer :
  'a . 'a LowStar_ConstBuffer.const_buffer -> 'a LowStar_Buffer.buffer =
  fun b -> LowStar_ConstBuffer.to_buffer b
let const_to_ibuffer :
  'a .
    'a LowStar_ConstBuffer.const_buffer -> 'a LowStar_ImmutableBuffer.ibuffer
  = fun b -> LowStar_ConstBuffer.to_ibuffer b
type ('ty, 'a, 'len) lbuffer_t = Obj.t
type ('a, 'len) lbuffer = 'a LowStar_Buffer.buffer
type ('a, 'len) ilbuffer = 'a LowStar_ImmutableBuffer.ibuffer
type ('a, 'len) clbuffer = 'a LowStar_ConstBuffer.const_buffer
type ('a, 'len) glbuffer = 'a LowStar_ConstBuffer.const_buffer
let const_to_lbuffer :
  'a .
    FStar_UInt32.t ->
      'a LowStar_ConstBuffer.const_buffer -> 'a LowStar_Buffer.buffer
  = fun len -> fun b -> const_to_buffer b
let const_to_ilbuffer :
  'a .
    FStar_UInt32.t ->
      'a LowStar_ConstBuffer.const_buffer ->
        'a LowStar_ImmutableBuffer.ibuffer
  = fun len -> fun b -> const_to_ibuffer b
let null : 'a . unit -> 'a LowStar_Buffer.buffer =
  fun uu___ -> LowStar_Monotonic_Buffer.mnull ()
type ('t, 'a, 'h, 'b) live = Obj.t



type ('s, 'h1, 'h2) modifies =
  (unit, unit, unit) LowStar_Monotonic_Buffer.modifies
type ('t1, 't2, 'a1, 'a2, 'b1, 'b2) disjoint =
  (unit, unit) LowStar_Monotonic_Buffer.loc_disjoint


type ('h1, 'h2) modifies0 = (unit, unit, unit) modifies
type ('a, 'b, 'h1, 'h2) modifies1 = (unit, unit, unit) modifies
type ('a0, 'a1, 'b0, 'b1, 'h1, 'h2) modifies2 = (unit, unit, unit) modifies
type ('a0, 'a1, 'a2, 'b0, 'b1, 'b2, 'h1, 'h2) modifies3 =
  (unit, unit, unit) modifies
type ('a0, 'a1, 'a2, 'a3, 'b0, 'b1, 'b2, 'b3, 'h1, 'h2) modifies4 =
  (unit, unit, unit) modifies
type ('a0, 'a1, 'a2, 'a3, 'a4, 'b0, 'b1, 'b2, 'b3, 'b4, 'h1, 'h2) modifies5 =
  (unit, unit, unit) modifies
type ('a0, 'a1, 'a2, 'a3, 'a4, 'a5, 'b0, 'b1, 'b2, 'b3, 'b4, 'b5, 'h1,
  'h2) modifies6 = (unit, unit, unit) modifies







let (sub :
  buftype ->
    unit ->
      FStar_UInt32.t -> Obj.t -> FStar_UInt32.t -> FStar_UInt32.t -> Obj.t)
  =
  fun t ->
    fun a ->
      fun len ->
        fun b ->
          fun start ->
            fun n ->
              match t with
              | MUT ->
                  Obj.repr
                    (LowStar_Monotonic_Buffer.msub (Obj.magic b) start ())
              | IMMUT ->
                  Obj.repr
                    (LowStar_Monotonic_Buffer.msub (Obj.magic b) start ())
              | CONST ->
                  Obj.repr (LowStar_ConstBuffer.sub (Obj.magic b) start ())
let (index :
  buftype -> unit -> FStar_UInt32.t -> Obj.t -> FStar_UInt32.t -> Obj.t) =
  fun t ->
    fun a ->
      fun len ->
        fun b ->
          fun i ->
            match t with
            | MUT -> LowStar_Monotonic_Buffer.index (Obj.magic b) i
            | IMMUT -> LowStar_Monotonic_Buffer.index (Obj.magic b) i
            | CONST -> LowStar_ConstBuffer.index (Obj.magic b) i
let upd :
  'a .
    FStar_UInt32.t ->
      'a LowStar_Buffer.buffer -> FStar_UInt32.t -> 'a -> unit
  =
  fun len ->
    fun b ->
      fun i ->
        fun v ->
          let h0 = FStar_HyperStack_ST.get () in
          (let h = FStar_HyperStack_ST.get () in
           LowStar_Monotonic_Buffer.upd' b i v);
          (let h1 = FStar_HyperStack_ST.get () in ())
let op_Array_Assignment :
  'a .
    FStar_UInt32.t ->
      'a LowStar_Buffer.buffer -> FStar_UInt32.t -> 'a -> unit
  =
  fun len ->
    fun b ->
      fun i ->
        fun v ->
          let h0 = FStar_HyperStack_ST.get () in
          (let h = FStar_HyperStack_ST.get () in
           LowStar_Monotonic_Buffer.upd' b i v);
          (let h1 = FStar_HyperStack_ST.get () in ())
let (op_Array_Access :
  buftype -> unit -> FStar_UInt32.t -> Obj.t -> FStar_UInt32.t -> Obj.t) =
  fun t ->
    fun a ->
      fun len ->
        fun b ->
          fun i ->
            match t with
            | MUT -> LowStar_Monotonic_Buffer.index (Obj.magic b) i
            | IMMUT -> LowStar_Monotonic_Buffer.index (Obj.magic b) i
            | CONST -> LowStar_ConstBuffer.index (Obj.magic b) i



type ('a, 'len, 'b, 'h0, 'h1, 's) stack_allocated = unit
type ('a, 'len, 'b, 'h0, 'h1, 's) global_allocated = unit
type ('t, 'a, 'len, 'b) recallable = Obj.t
let (recall : buftype -> unit -> FStar_UInt32.t -> Obj.t -> unit) =
  fun t ->
    fun a ->
      fun len ->
        fun b ->
          match t with
          | IMMUT -> LowStar_Monotonic_Buffer.recall (Obj.magic b)
          | MUT -> LowStar_Monotonic_Buffer.recall (Obj.magic b)
          | CONST ->
              LowStar_Monotonic_Buffer.recall
                (LowStar_ConstBuffer.cast (Obj.magic b))
type ('a, 's, 's1) cpred = unit
type ('a, 'len, 'b, 's) witnessed =
  ('a, Obj.t, Obj.t, unit, unit) LowStar_Monotonic_Buffer.witnessed
let create : 'a . FStar_UInt32.t -> 'a -> 'a LowStar_Buffer.buffer =
  fun clen -> fun init -> LowStar_Monotonic_Buffer.malloca init clen
let createL : 'a . 'a Prims.list -> 'a LowStar_Buffer.buffer =
  fun init -> LowStar_Monotonic_Buffer.malloca_of_list init
let createL_global :
  'a . 'a Prims.list -> 'a LowStar_ConstBuffer.const_buffer =
  fun init ->
    let uu___ = LowStar_ImmutableBuffer.igcmalloc_of_list () init in
    LowStar_ConstBuffer.of_ibuffer uu___
let recall_contents :
  'a .
    FStar_UInt32.t ->
      'a LowStar_ConstBuffer.const_buffer ->
        ('a, unit) Lib_Sequence.lseq -> unit
  =
  fun len ->
    fun b ->
      fun s ->
        LowStar_Monotonic_Buffer.recall_p (LowStar_ConstBuffer.to_ibuffer b)
          ()
let (copy :
  buftype ->
    unit -> FStar_UInt32.t -> Obj.t LowStar_Buffer.buffer -> Obj.t -> unit)
  =
  fun t ->
    fun a ->
      fun len ->
        fun o ->
          fun i ->
            match t with
            | MUT ->
                let h0 = FStar_HyperStack_ST.get () in
                (LowStar_Monotonic_Buffer.blit (Obj.magic i)
                   (FStar_UInt32.uint_to_t Prims.int_zero) o
                   (FStar_UInt32.uint_to_t Prims.int_zero) len;
                 (let h1 = FStar_HyperStack_ST.get () in ()))
            | IMMUT ->
                let h0 = FStar_HyperStack_ST.get () in
                (LowStar_Monotonic_Buffer.blit (Obj.magic i)
                   (FStar_UInt32.uint_to_t Prims.int_zero) o
                   (FStar_UInt32.uint_to_t Prims.int_zero) len;
                 (let h1 = FStar_HyperStack_ST.get () in ()))
            | CONST ->
                let h0 = FStar_HyperStack_ST.get () in
                (LowStar_Monotonic_Buffer.blit
                   (LowStar_ConstBuffer.cast (Obj.magic i))
                   (FStar_UInt32.uint_to_t Prims.int_zero) o
                   (FStar_UInt32.uint_to_t Prims.int_zero) len;
                 (let h1 = FStar_HyperStack_ST.get () in ()))
let memset :
  'a .
    FStar_UInt32.t ->
      'a LowStar_Buffer.buffer -> 'a -> FStar_UInt32.t -> unit
  =
  fun blen ->
    fun b -> fun init -> fun len -> LowStar_Monotonic_Buffer.fill b init len
let (update_sub :
  buftype ->
    unit ->
      FStar_UInt32.t ->
        Obj.t LowStar_Buffer.buffer ->
          FStar_UInt32.t -> FStar_UInt32.t -> Obj.t -> unit)
  =
  fun t ->
    fun a ->
      fun len ->
        fun dst ->
          fun start ->
            fun n ->
              fun src ->
                match t with
                | MUT ->
                    let h0 = FStar_HyperStack_ST.get () in
                    (LowStar_Monotonic_Buffer.blit (Obj.magic src)
                       (FStar_UInt32.uint_to_t Prims.int_zero) dst start n;
                     (let h1 = FStar_HyperStack_ST.get () in ()))
                | IMMUT ->
                    let h0 = FStar_HyperStack_ST.get () in
                    (LowStar_Monotonic_Buffer.blit (Obj.magic src)
                       (FStar_UInt32.uint_to_t Prims.int_zero) dst start n;
                     (let h1 = FStar_HyperStack_ST.get () in ()))
                | CONST ->
                    let h0 = FStar_HyperStack_ST.get () in
                    (LowStar_Monotonic_Buffer.blit
                       (LowStar_ConstBuffer.cast (Obj.magic src))
                       (FStar_UInt32.uint_to_t Prims.int_zero) dst start n;
                     (let h1 = FStar_HyperStack_ST.get () in ()))
let update_sub_f :
  'a .
    FStar_UInt32.t ->
      FStar_Monotonic_HyperStack.mem ->
        'a LowStar_Buffer.buffer ->
          FStar_UInt32.t -> FStar_UInt32.t -> unit -> (unit -> unit) -> unit
  =
  fun len ->
    fun h0 ->
      fun buf ->
        fun start ->
          fun n ->
            fun spec ->
              fun f ->
                let tmp = LowStar_Monotonic_Buffer.msub buf start () in
                let h01 = FStar_HyperStack_ST.get () in
                f (); (let h1 = FStar_HyperStack_ST.get () in ())
let (concat2 :
  buftype ->
    buftype ->
      unit ->
        FStar_UInt32.t ->
          Obj.t ->
            FStar_UInt32.t -> Obj.t -> Obj.t LowStar_Buffer.buffer -> unit)
  =
  fun a ->
    fun t0 ->
      fun t1 ->
        fun len0 ->
          fun s0 ->
            fun len1 ->
              fun s1 ->
                fun s ->
                  let h0 = FStar_HyperStack_ST.get () in
                  (match a with
                   | MUT ->
                       let h01 = FStar_HyperStack_ST.get () in
                       (LowStar_Monotonic_Buffer.blit (Obj.magic s0)
                          (FStar_UInt32.uint_to_t Prims.int_zero) s
                          (FStar_UInt32.uint_to_t Prims.int_zero) len0;
                        (let h1 = FStar_HyperStack_ST.get () in ()))
                   | IMMUT ->
                       let h01 = FStar_HyperStack_ST.get () in
                       (LowStar_Monotonic_Buffer.blit (Obj.magic s0)
                          (FStar_UInt32.uint_to_t Prims.int_zero) s
                          (FStar_UInt32.uint_to_t Prims.int_zero) len0;
                        (let h1 = FStar_HyperStack_ST.get () in ()))
                   | CONST ->
                       let h01 = FStar_HyperStack_ST.get () in
                       (LowStar_Monotonic_Buffer.blit
                          (LowStar_ConstBuffer.cast (Obj.magic s0))
                          (FStar_UInt32.uint_to_t Prims.int_zero) s
                          (FStar_UInt32.uint_to_t Prims.int_zero) len0;
                        (let h1 = FStar_HyperStack_ST.get () in ())));
                  (match t0 with
                   | MUT ->
                       let h01 = FStar_HyperStack_ST.get () in
                       (LowStar_Monotonic_Buffer.blit (Obj.magic s1)
                          (FStar_UInt32.uint_to_t Prims.int_zero) s len0 len1;
                        (let h1 = FStar_HyperStack_ST.get () in ()))
                   | IMMUT ->
                       let h01 = FStar_HyperStack_ST.get () in
                       (LowStar_Monotonic_Buffer.blit (Obj.magic s1)
                          (FStar_UInt32.uint_to_t Prims.int_zero) s len0 len1;
                        (let h1 = FStar_HyperStack_ST.get () in ()))
                   | CONST ->
                       let h01 = FStar_HyperStack_ST.get () in
                       (LowStar_Monotonic_Buffer.blit
                          (LowStar_ConstBuffer.cast (Obj.magic s1))
                          (FStar_UInt32.uint_to_t Prims.int_zero) s len0 len1;
                        (let h1 = FStar_HyperStack_ST.get () in ())));
                  (let h1 = FStar_HyperStack_ST.get () in ())
let (concat3 :
  buftype ->
    buftype ->
      buftype ->
        unit ->
          FStar_UInt32.t ->
            Obj.t ->
              FStar_UInt32.t ->
                Obj.t ->
                  FStar_UInt32.t ->
                    Obj.t -> Obj.t LowStar_Buffer.buffer -> unit)
  =
  fun a ->
    fun t0 ->
      fun t1 ->
        fun t2 ->
          fun len0 ->
            fun s0 ->
              fun len1 ->
                fun s1 ->
                  fun len2 ->
                    fun s2 ->
                      fun s ->
                        let h0 = FStar_HyperStack_ST.get () in
                        (match a with
                         | MUT ->
                             let h01 = FStar_HyperStack_ST.get () in
                             (LowStar_Monotonic_Buffer.blit (Obj.magic s0)
                                (FStar_UInt32.uint_to_t Prims.int_zero) s
                                (FStar_UInt32.uint_to_t Prims.int_zero) len0;
                              (let h1 = FStar_HyperStack_ST.get () in ()))
                         | IMMUT ->
                             let h01 = FStar_HyperStack_ST.get () in
                             (LowStar_Monotonic_Buffer.blit (Obj.magic s0)
                                (FStar_UInt32.uint_to_t Prims.int_zero) s
                                (FStar_UInt32.uint_to_t Prims.int_zero) len0;
                              (let h1 = FStar_HyperStack_ST.get () in ()))
                         | CONST ->
                             let h01 = FStar_HyperStack_ST.get () in
                             (LowStar_Monotonic_Buffer.blit
                                (LowStar_ConstBuffer.cast (Obj.magic s0))
                                (FStar_UInt32.uint_to_t Prims.int_zero) s
                                (FStar_UInt32.uint_to_t Prims.int_zero) len0;
                              (let h1 = FStar_HyperStack_ST.get () in ())));
                        (match t0 with
                         | MUT ->
                             let h01 = FStar_HyperStack_ST.get () in
                             (LowStar_Monotonic_Buffer.blit (Obj.magic s1)
                                (FStar_UInt32.uint_to_t Prims.int_zero) s
                                len0 len1;
                              (let h1 = FStar_HyperStack_ST.get () in ()))
                         | IMMUT ->
                             let h01 = FStar_HyperStack_ST.get () in
                             (LowStar_Monotonic_Buffer.blit (Obj.magic s1)
                                (FStar_UInt32.uint_to_t Prims.int_zero) s
                                len0 len1;
                              (let h1 = FStar_HyperStack_ST.get () in ()))
                         | CONST ->
                             let h01 = FStar_HyperStack_ST.get () in
                             (LowStar_Monotonic_Buffer.blit
                                (LowStar_ConstBuffer.cast (Obj.magic s1))
                                (FStar_UInt32.uint_to_t Prims.int_zero) s
                                len0 len1;
                              (let h1 = FStar_HyperStack_ST.get () in ())));
                        (let h1 = FStar_HyperStack_ST.get () in
                         (match t1 with
                          | MUT ->
                              let h01 = FStar_HyperStack_ST.get () in
                              (LowStar_Monotonic_Buffer.blit (Obj.magic s2)
                                 (FStar_UInt32.uint_to_t Prims.int_zero) s
                                 (FStar_UInt32.add len0 len1) len2;
                               (let h11 = FStar_HyperStack_ST.get () in ()))
                          | IMMUT ->
                              let h01 = FStar_HyperStack_ST.get () in
                              (LowStar_Monotonic_Buffer.blit (Obj.magic s2)
                                 (FStar_UInt32.uint_to_t Prims.int_zero) s
                                 (FStar_UInt32.add len0 len1) len2;
                               (let h11 = FStar_HyperStack_ST.get () in ()))
                          | CONST ->
                              let h01 = FStar_HyperStack_ST.get () in
                              (LowStar_Monotonic_Buffer.blit
                                 (LowStar_ConstBuffer.cast (Obj.magic s2))
                                 (FStar_UInt32.uint_to_t Prims.int_zero) s
                                 (FStar_UInt32.add len0 len1) len2;
                               (let h11 = FStar_HyperStack_ST.get () in ())));
                         (let h2 = FStar_HyperStack_ST.get () in ()))
let (loop_nospec :
  FStar_Monotonic_HyperStack.mem ->
    unit ->
      FStar_UInt32.t ->
        FStar_UInt32.t ->
          Obj.t LowStar_Buffer.buffer -> (FStar_UInt32.t -> unit) -> unit)
  =
  fun h0 ->
    fun a ->
      fun len ->
        fun n ->
          fun buf ->
            fun impl ->
              Obj.magic (fun h1 -> fun j -> ());
              C_Loops.for1 (FStar_UInt32.uint_to_t Prims.int_zero) n ()
                (fun i -> impl i)
let (loop_nospec2 :
  FStar_Monotonic_HyperStack.mem ->
    unit ->
      unit ->
        FStar_UInt32.t ->
          FStar_UInt32.t ->
            FStar_UInt32.t ->
              Obj.t LowStar_Buffer.buffer ->
                Obj.t LowStar_Buffer.buffer ->
                  (FStar_UInt32.t -> unit) -> unit)
  =
  fun h0 ->
    fun a1 ->
      fun a2 ->
        fun len1 ->
          fun len2 ->
            fun n ->
              fun buf1 ->
                fun buf2 ->
                  fun impl ->
                    Obj.magic (fun h1 -> fun j -> ());
                    C_Loops.for1 (FStar_UInt32.uint_to_t Prims.int_zero) n ()
                      (fun i -> impl i)
let (loop_nospec3 :
  FStar_Monotonic_HyperStack.mem ->
    unit ->
      unit ->
        unit ->
          FStar_UInt32.t ->
            FStar_UInt32.t ->
              FStar_UInt32.t ->
                FStar_UInt32.t ->
                  Obj.t LowStar_Buffer.buffer ->
                    Obj.t LowStar_Buffer.buffer ->
                      Obj.t LowStar_Buffer.buffer ->
                        (FStar_UInt32.t -> unit) -> unit)
  =
  fun h0 ->
    fun a1 ->
      fun a2 ->
        fun a3 ->
          fun len1 ->
            fun len2 ->
              fun len3 ->
                fun n ->
                  fun buf1 ->
                    fun buf2 ->
                      fun buf3 ->
                        fun impl ->
                          Obj.magic (fun h1 -> fun j -> ());
                          C_Loops.for1
                            (FStar_UInt32.uint_to_t Prims.int_zero) n ()
                            (fun i -> impl i)
let (loop_range_nospec :
  FStar_Monotonic_HyperStack.mem ->
    unit ->
      FStar_UInt32.t ->
        FStar_UInt32.t ->
          FStar_UInt32.t ->
            Obj.t LowStar_Buffer.buffer -> (FStar_UInt32.t -> unit) -> unit)
  =
  fun h0 ->
    fun a ->
      fun len ->
        fun start ->
          fun n ->
            fun buf ->
              fun impl ->
                Obj.magic (fun h1 -> fun j -> ());
                C_Loops.for1 start (FStar_UInt32.add_mod start n) ()
                  (fun i -> impl i)
type ('h0, 'n, 'auspec, 'refl, 'footprint, 'spec, 'i, 'h) loop_inv = unit
let (loop :
  FStar_Monotonic_HyperStack.mem ->
    FStar_UInt32.t ->
      unit -> unit -> unit -> unit -> (FStar_UInt32.t -> unit) -> unit)
  =
  fun h0 ->
    fun n ->
      fun a_spec ->
        fun refl ->
          fun footprint ->
            fun spec ->
              fun impl ->
                Obj.magic (fun h -> fun i -> ());
                C_Loops.for1 (FStar_UInt32.uint_to_t Prims.int_zero) n ()
                  (fun i -> impl i)
type ('h0, 'n, 'auspec, 'refl, 'footprint, 'spec, 'i, 'h) loop_refl_inv =
  unit
let (loop_refl :
  FStar_Monotonic_HyperStack.mem ->
    FStar_UInt32.t ->
      unit -> unit -> unit -> unit -> (FStar_UInt32.t -> unit) -> unit)
  =
  fun h0 ->
    fun n ->
      fun a_spec ->
        fun refl ->
          fun footprint ->
            fun spec ->
              fun impl ->
                Obj.magic (fun h -> fun i -> ());
                C_Loops.for1 (FStar_UInt32.uint_to_t Prims.int_zero) n ()
                  (fun i -> impl i)
type ('h0, 'n, 'b, 'blen, 'write, 'spec, 'i, 'h) loop1_inv = unit
let loop1 :
  'b .
    FStar_UInt32.t ->
      FStar_Monotonic_HyperStack.mem ->
        FStar_UInt32.t ->
          'b LowStar_Buffer.buffer ->
            unit -> (FStar_UInt32.t -> unit) -> unit
  =
  fun blen ->
    fun h0 ->
      fun n ->
        fun acc ->
          fun spec ->
            fun impl ->
              Obj.magic (fun h -> fun i -> ());
              C_Loops.for1 (FStar_UInt32.uint_to_t Prims.int_zero) n ()
                (fun i -> impl i)
type ('b0, 'blen0, 'b1, 'blen1, 'h0, 'n, 'write0, 'write1, 'spec, 'i,
  'h) loop2_inv = unit
let loop2 :
  'b0 .
    FStar_UInt32.t ->
      unit ->
        FStar_UInt32.t ->
          FStar_Monotonic_HyperStack.mem ->
            FStar_UInt32.t ->
              'b0 LowStar_Buffer.buffer ->
                Obj.t LowStar_Buffer.buffer ->
                  unit -> (FStar_UInt32.t -> unit) -> unit
  =
  fun blen0 ->
    fun b1 ->
      fun blen1 ->
        fun h0 ->
          fun n ->
            fun acc0 ->
              fun acc1 ->
                fun spec ->
                  fun impl ->
                    Obj.magic (fun h -> fun i -> ());
                    C_Loops.for1 (FStar_UInt32.uint_to_t Prims.int_zero) n ()
                      (fun i -> impl i)
let salloc1_with_inv :
  'a 'res .
    FStar_Monotonic_HyperStack.mem ->
      FStar_UInt32.t ->
        'a ->
          unit -> unit -> unit -> ('a LowStar_Buffer.buffer -> 'res) -> 'res
  =
  fun h ->
    fun len ->
      fun x ->
        fun footprint ->
          fun spec ->
            fun spec_inv ->
              fun impl ->
                let h0 = FStar_HyperStack_ST.get () in
                FStar_HyperStack_ST.push_frame ();
                (let h1 = FStar_HyperStack_ST.get () in
                 let b = LowStar_Monotonic_Buffer.malloca x len in
                 let h2 = FStar_HyperStack_ST.get () in
                 let r = impl b in
                 let h3 = FStar_HyperStack_ST.get () in
                 Lib_Memzero0.memzero b len;
                 (let h4 = FStar_HyperStack_ST.get () in
                  FStar_HyperStack_ST.pop_frame ();
                  (let h5 = FStar_HyperStack_ST.get () in r)))
let salloc1 :
  'a 'res .
    FStar_Monotonic_HyperStack.mem ->
      FStar_UInt32.t ->
        'a -> unit -> unit -> ('a LowStar_Buffer.buffer -> 'res) -> 'res
  =
  fun h ->
    fun len ->
      fun x ->
        fun footprint ->
          fun spec ->
            fun impl ->
              let h0 = FStar_HyperStack_ST.get () in
              FStar_HyperStack_ST.push_frame ();
              (let h1 = FStar_HyperStack_ST.get () in
               let b = LowStar_Monotonic_Buffer.malloca x len in
               let h2 = FStar_HyperStack_ST.get () in
               let r = impl b in
               let h3 = FStar_HyperStack_ST.get () in
               Lib_Memzero0.memzero b len;
               (let h4 = FStar_HyperStack_ST.get () in
                FStar_HyperStack_ST.pop_frame ();
                (let h5 = FStar_HyperStack_ST.get () in r)))
let salloc_nospec :
  'a 'res .
    FStar_Monotonic_HyperStack.mem ->
      FStar_UInt32.t ->
        'a -> unit -> ('a LowStar_Buffer.buffer -> 'res) -> 'res
  =
  fun h ->
    fun len ->
      fun x ->
        fun footprint ->
          fun impl ->
            let h0 = FStar_HyperStack_ST.get () in
            FStar_HyperStack_ST.push_frame ();
            (let h1 = FStar_HyperStack_ST.get () in
             let b = LowStar_Monotonic_Buffer.malloca x len in
             let h2 = FStar_HyperStack_ST.get () in
             let r = impl b in
             let h3 = FStar_HyperStack_ST.get () in
             Lib_Memzero0.memzero b len;
             (let h4 = FStar_HyperStack_ST.get () in
              FStar_HyperStack_ST.pop_frame ();
              (let h5 = FStar_HyperStack_ST.get () in r)))
let loopi_blocks_f :
  'a 'b .
    FStar_UInt32.t ->
      FStar_UInt32.t ->
        FStar_UInt32.t ->
          'a LowStar_Buffer.buffer ->
            (Prims.nat ->
               ('a, unit) Lib_Sequence.lseq ->
                 ('b, unit) Lib_Sequence.lseq -> ('b, unit) Lib_Sequence.lseq)
              ->
              (FStar_UInt32.t ->
                 'a LowStar_Buffer.buffer -> 'b LowStar_Buffer.buffer -> unit)
                ->
                FStar_UInt32.t ->
                  FStar_UInt32.t -> 'b LowStar_Buffer.buffer -> unit
  =
  fun blen ->
    fun bs ->
      fun inpLen ->
        fun inp ->
          fun spec_f ->
            fun f ->
              fun nb ->
                fun i ->
                  fun w ->
                    let block =
                      LowStar_Monotonic_Buffer.msub inp
                        (FStar_UInt32.mul i bs) () in
                    f i block w
let loopi_blocks_f_nospec :
  'a 'b .
    FStar_UInt32.t ->
      FStar_UInt32.t ->
        FStar_UInt32.t ->
          'a LowStar_Buffer.buffer ->
            (FStar_UInt32.t ->
               'a LowStar_Buffer.buffer -> 'b LowStar_Buffer.buffer -> unit)
              ->
              FStar_UInt32.t ->
                FStar_UInt32.t -> 'b LowStar_Buffer.buffer -> unit
  =
  fun blen ->
    fun bs ->
      fun inpLen ->
        fun inp ->
          fun f ->
            fun nb ->
              fun i ->
                fun w ->
                  let block =
                    LowStar_Monotonic_Buffer.msub inp (FStar_UInt32.mul i bs)
                      () in
                  f i block w
let loopi_blocks :
  'a 'b .
    FStar_UInt32.t ->
      FStar_UInt32.t ->
        FStar_UInt32.t ->
          'a LowStar_Buffer.buffer ->
            (Prims.nat ->
               ('a, unit) Lib_Sequence.lseq ->
                 ('b, unit) Lib_Sequence.lseq -> ('b, unit) Lib_Sequence.lseq)
              ->
              (Prims.nat ->
                 Prims.nat ->
                   ('a, unit) Lib_Sequence.lseq ->
                     ('b, unit) Lib_Sequence.lseq ->
                       ('b, unit) Lib_Sequence.lseq)
                ->
                (FStar_UInt32.t ->
                   'a LowStar_Buffer.buffer ->
                     'b LowStar_Buffer.buffer -> unit)
                  ->
                  (FStar_UInt32.t ->
                     FStar_UInt32.t ->
                       'a LowStar_Buffer.buffer ->
                         'b LowStar_Buffer.buffer -> unit)
                    -> 'b LowStar_Buffer.buffer -> unit
  =
  fun blen ->
    fun bs ->
      fun inpLen ->
        fun inp ->
          fun spec_f ->
            fun spec_l ->
              fun f ->
                fun l ->
                  fun w ->
                    let nb = FStar_UInt32.div inpLen bs in
                    let rem = FStar_UInt32.rem inpLen bs in
                    let h0 = FStar_HyperStack_ST.get () in
                    Obj.magic (fun h -> fun i -> ());
                    C_Loops.for1 (FStar_UInt32.uint_to_t Prims.int_zero) nb
                      ()
                      (fun i ->
                         let block =
                           LowStar_Monotonic_Buffer.msub inp
                             (FStar_UInt32.mul i bs) () in
                         f i block w);
                    (let last =
                       LowStar_Monotonic_Buffer.msub inp
                         (FStar_UInt32.mul nb bs) () in
                     l nb rem last w)
let loopi_blocks_nospec :
  'a 'b .
    FStar_UInt32.t ->
      FStar_UInt32.t ->
        FStar_UInt32.t ->
          'a LowStar_Buffer.buffer ->
            (FStar_UInt32.t ->
               'a LowStar_Buffer.buffer -> 'b LowStar_Buffer.buffer -> unit)
              ->
              (FStar_UInt32.t ->
                 FStar_UInt32.t ->
                   'a LowStar_Buffer.buffer ->
                     'b LowStar_Buffer.buffer -> unit)
                -> 'b LowStar_Buffer.buffer -> unit
  =
  fun blen ->
    fun bs ->
      fun inpLen ->
        fun inp ->
          fun f ->
            fun l ->
              fun w ->
                let nb = FStar_UInt32.div inpLen bs in
                let rem = FStar_UInt32.rem inpLen bs in
                let h0 = FStar_HyperStack_ST.get () in
                Obj.magic (fun h1 -> fun j -> ());
                C_Loops.for1 (FStar_UInt32.uint_to_t Prims.int_zero) nb ()
                  (fun i ->
                     let block =
                       LowStar_Monotonic_Buffer.msub inp
                         (FStar_UInt32.mul i bs) () in
                     f i block w);
                (let last =
                   LowStar_Monotonic_Buffer.msub inp
                     (FStar_UInt32.mul_mod nb bs) () in
                 l nb rem last w)
let loop_blocks_f :
  'a 'b .
    FStar_UInt32.t ->
      FStar_UInt32.t ->
        FStar_UInt32.t ->
          'a LowStar_Buffer.buffer ->
            (('a, unit) Lib_Sequence.lseq ->
               ('b, unit) Lib_Sequence.lseq -> ('b, unit) Lib_Sequence.lseq)
              ->
              ('a LowStar_Buffer.buffer -> 'b LowStar_Buffer.buffer -> unit)
                ->
                FStar_UInt32.t ->
                  FStar_UInt32.t -> 'b LowStar_Buffer.buffer -> unit
  =
  fun blen ->
    fun bs ->
      fun inpLen ->
        fun inp ->
          fun spec_f ->
            fun f ->
              fun nb ->
                fun i ->
                  fun w ->
                    let block =
                      LowStar_Monotonic_Buffer.msub inp
                        (FStar_UInt32.mul i bs) () in
                    f block w
let loop_blocks :
  'a 'b .
    FStar_UInt32.t ->
      FStar_UInt32.t ->
        FStar_UInt32.t ->
          'a LowStar_Buffer.buffer ->
            (('a, unit) Lib_Sequence.lseq ->
               ('b, unit) Lib_Sequence.lseq -> ('b, unit) Lib_Sequence.lseq)
              ->
              (Prims.nat ->
                 ('a, unit) Lib_Sequence.lseq ->
                   ('b, unit) Lib_Sequence.lseq ->
                     ('b, unit) Lib_Sequence.lseq)
                ->
                ('a LowStar_Buffer.buffer -> 'b LowStar_Buffer.buffer -> unit)
                  ->
                  (FStar_UInt32.t ->
                     'a LowStar_Buffer.buffer ->
                       'b LowStar_Buffer.buffer -> unit)
                    -> 'b LowStar_Buffer.buffer -> unit
  =
  fun blen ->
    fun bs ->
      fun inpLen ->
        fun inp ->
          fun spec_f ->
            fun spec_l ->
              fun f ->
                fun l ->
                  fun w ->
                    let nb = FStar_UInt32.div inpLen bs in
                    let rem = FStar_UInt32.rem inpLen bs in
                    let h0 = FStar_HyperStack_ST.get () in
                    Obj.magic (fun h -> fun i -> ());
                    C_Loops.for1 (FStar_UInt32.uint_to_t Prims.int_zero) nb
                      ()
                      (fun i ->
                         let block =
                           LowStar_Monotonic_Buffer.msub inp
                             (FStar_UInt32.mul i bs) () in
                         f block w);
                    (let last =
                       LowStar_Monotonic_Buffer.msub inp
                         (FStar_UInt32.mul nb bs) () in
                     l rem last w)
let fill_blocks :
  't .
    FStar_Monotonic_HyperStack.mem ->
      FStar_UInt32.t ->
        FStar_UInt32.t ->
          't LowStar_Buffer.buffer ->
            unit -> unit -> unit -> unit -> (FStar_UInt32.t -> unit) -> unit
  =
  fun h0 ->
    fun len ->
      fun n ->
        fun output ->
          fun a_spec ->
            fun refl ->
              fun footprint ->
                fun spec ->
                  fun impl ->
                    let h01 = FStar_HyperStack_ST.get () in
                    Obj.magic (fun h -> fun i -> ());
                    C_Loops.for1 (FStar_UInt32.uint_to_t Prims.int_zero) n ()
                      (fun i ->
                         let block =
                           LowStar_Monotonic_Buffer.msub output
                             (FStar_UInt32.mul i len) () in
                         let h0_ = FStar_HyperStack_ST.get () in
                         impl i; (let h = FStar_HyperStack_ST.get () in ()));
                    (let h1 = FStar_HyperStack_ST.get () in ())
let fill_blocks_simple :
  'a .
    FStar_Monotonic_HyperStack.mem ->
      FStar_UInt32.t ->
        FStar_UInt32.t ->
          'a LowStar_Buffer.buffer ->
            unit -> (FStar_UInt32.t -> unit) -> unit
  =
  fun h0 ->
    fun bs ->
      fun n ->
        fun output ->
          fun spec_f ->
            fun impl_f ->
              let h01 = FStar_HyperStack_ST.get () in
              Obj.magic (fun h -> fun i -> ());
              C_Loops.for1 (FStar_UInt32.uint_to_t Prims.int_zero) n ()
                (fun i ->
                   let block =
                     LowStar_Monotonic_Buffer.msub output
                       (FStar_UInt32.mul i bs) () in
                   let h0_ = FStar_HyperStack_ST.get () in
                   impl_f i; (let h = FStar_HyperStack_ST.get () in ()))
let fillT :
  'a .
    FStar_UInt32.t ->
      'a LowStar_Buffer.buffer ->
        (Prims.nat -> 'a) -> (FStar_UInt32.t -> 'a) -> unit
  =
  fun clen ->
    fun o ->
      fun spec_f ->
        fun f ->
          let h0 = FStar_HyperStack_ST.get () in
          Obj.magic (fun h -> fun i -> ());
          C_Loops.for1 (FStar_UInt32.uint_to_t Prims.int_zero) clen ()
            (fun i ->
               (let h01 = FStar_HyperStack_ST.get () in
                (let h = FStar_HyperStack_ST.get () in
                 LowStar_Monotonic_Buffer.upd' o i (f i));
                (let h1 = FStar_HyperStack_ST.get () in ()));
               (let h' = FStar_HyperStack_ST.get () in ()))
let fill :
  'a .
    FStar_Monotonic_HyperStack.mem ->
      FStar_UInt32.t ->
        'a LowStar_Buffer.buffer -> unit -> (FStar_UInt32.t -> 'a) -> unit
  =
  fun h0 ->
    fun clen ->
      fun out ->
        fun spec ->
          fun impl ->
            let h01 = FStar_HyperStack_ST.get () in
            Obj.magic (fun h -> fun i -> ());
            C_Loops.for1 (FStar_UInt32.uint_to_t Prims.int_zero) clen ()
              (fun i ->
                 let os =
                   LowStar_Monotonic_Buffer.msub out
                     (FStar_UInt32.uint_to_t Prims.int_zero) () in
                 let h = FStar_HyperStack_ST.get () in
                 let x = impl i in
                 (let h02 = FStar_HyperStack_ST.get () in
                  (let h1 = FStar_HyperStack_ST.get () in
                   LowStar_Monotonic_Buffer.upd' os i x);
                  (let h1 = FStar_HyperStack_ST.get () in ()));
                 (let h' = FStar_HyperStack_ST.get () in ()))
type ('t1, 't2, 'a1, 'a2, 'clen1, 'clen2, 'b1, 'b2) eq_or_disjoint = unit

let (mapT :
  buftype ->
    unit ->
      unit ->
        FStar_UInt32.t ->
          Obj.t LowStar_Buffer.buffer -> (Obj.t -> Obj.t) -> Obj.t -> unit)
  =
  fun t ->
    fun a ->
      fun b ->
        fun clen ->
          fun out ->
            fun f ->
              fun inp ->
                let h0 = FStar_HyperStack_ST.get () in
                let h01 = FStar_HyperStack_ST.get () in
                Obj.magic (fun h -> fun i -> ());
                C_Loops.for1 (FStar_UInt32.uint_to_t Prims.int_zero) clen ()
                  (fun i ->
                     let os =
                       LowStar_Monotonic_Buffer.msub out
                         (FStar_UInt32.uint_to_t Prims.int_zero) () in
                     let h = FStar_HyperStack_ST.get () in
                     let x =
                       let x1 =
                         match t with
                         | MUT ->
                             LowStar_Monotonic_Buffer.index (Obj.magic inp) i
                         | IMMUT ->
                             LowStar_Monotonic_Buffer.index (Obj.magic inp) i
                         | CONST ->
                             LowStar_ConstBuffer.index (Obj.magic inp) i in
                       let h1 = FStar_HyperStack_ST.get () in f x1 in
                     (let h02 = FStar_HyperStack_ST.get () in
                      (let h1 = FStar_HyperStack_ST.get () in
                       LowStar_Monotonic_Buffer.upd' os i x);
                      (let h1 = FStar_HyperStack_ST.get () in ()));
                     (let h' = FStar_HyperStack_ST.get () in ()))
let (map2T :
  buftype ->
    unit ->
      unit ->
        unit ->
          FStar_UInt32.t ->
            Obj.t LowStar_Buffer.buffer ->
              (Obj.t -> Obj.t -> Obj.t) -> Obj.t -> Obj.t -> unit)
  =
  fun t ->
    fun a1 ->
      fun a2 ->
        fun b ->
          fun clen ->
            fun out ->
              fun f ->
                fun inp1 ->
                  fun inp2 ->
                    let h0 = FStar_HyperStack_ST.get () in
                    let h01 = FStar_HyperStack_ST.get () in
                    Obj.magic (fun h -> fun i -> ());
                    C_Loops.for1 (FStar_UInt32.uint_to_t Prims.int_zero) clen
                      ()
                      (fun i ->
                         let os =
                           LowStar_Monotonic_Buffer.msub out
                             (FStar_UInt32.uint_to_t Prims.int_zero) () in
                         let h = FStar_HyperStack_ST.get () in
                         let x =
                           let h1 = FStar_HyperStack_ST.get () in
                           let uu___ =
                             match t with
                             | MUT ->
                                 LowStar_Monotonic_Buffer.index
                                   (Obj.magic inp1) i
                             | IMMUT ->
                                 LowStar_Monotonic_Buffer.index
                                   (Obj.magic inp1) i
                             | CONST ->
                                 LowStar_ConstBuffer.index (Obj.magic inp1) i in
                           let uu___1 =
                             match t with
                             | MUT ->
                                 LowStar_Monotonic_Buffer.index
                                   (Obj.magic inp2) i
                             | IMMUT ->
                                 LowStar_Monotonic_Buffer.index
                                   (Obj.magic inp2) i
                             | CONST ->
                                 LowStar_ConstBuffer.index (Obj.magic inp2) i in
                           f uu___ uu___1 in
                         (let h02 = FStar_HyperStack_ST.get () in
                          (let h1 = FStar_HyperStack_ST.get () in
                           LowStar_Monotonic_Buffer.upd' os i x);
                          (let h1 = FStar_HyperStack_ST.get () in ()));
                         (let h' = FStar_HyperStack_ST.get () in ()))
let (mapiT :
  buftype ->
    unit ->
      unit ->
        FStar_UInt32.t ->
          Obj.t LowStar_Buffer.buffer ->
            (FStar_UInt32.t -> Obj.t -> Obj.t) -> Obj.t -> unit)
  =
  fun t ->
    fun a ->
      fun b ->
        fun clen ->
          fun out ->
            fun f ->
              fun inp ->
                let h0 = FStar_HyperStack_ST.get () in
                let h01 = FStar_HyperStack_ST.get () in
                Obj.magic (fun h -> fun i -> ());
                C_Loops.for1 (FStar_UInt32.uint_to_t Prims.int_zero) clen ()
                  (fun i ->
                     let os =
                       LowStar_Monotonic_Buffer.msub out
                         (FStar_UInt32.uint_to_t Prims.int_zero) () in
                     let h = FStar_HyperStack_ST.get () in
                     let x =
                       let h1 = FStar_HyperStack_ST.get () in
                       let xi =
                         match t with
                         | MUT ->
                             LowStar_Monotonic_Buffer.index (Obj.magic inp) i
                         | IMMUT ->
                             LowStar_Monotonic_Buffer.index (Obj.magic inp) i
                         | CONST ->
                             LowStar_ConstBuffer.index (Obj.magic inp) i in
                       f i xi in
                     (let h02 = FStar_HyperStack_ST.get () in
                      (let h1 = FStar_HyperStack_ST.get () in
                       LowStar_Monotonic_Buffer.upd' os i x);
                      (let h1 = FStar_HyperStack_ST.get () in ()));
                     (let h' = FStar_HyperStack_ST.get () in ()))
let mapi :
  'a 'b .
    FStar_Monotonic_HyperStack.mem ->
      FStar_UInt32.t ->
        'b LowStar_Buffer.buffer ->
          unit ->
            (FStar_UInt32.t -> 'a -> 'b) -> 'a LowStar_Buffer.buffer -> unit
  =
  fun h0 ->
    fun clen ->
      fun out ->
        fun spec_f ->
          fun f ->
            fun inp ->
              let h01 = FStar_HyperStack_ST.get () in
              let h02 = FStar_HyperStack_ST.get () in
              Obj.magic (fun h -> fun i -> ());
              C_Loops.for1 (FStar_UInt32.uint_to_t Prims.int_zero) clen ()
                (fun i ->
                   let os =
                     LowStar_Monotonic_Buffer.msub out
                       (FStar_UInt32.uint_to_t Prims.int_zero) () in
                   let h = FStar_HyperStack_ST.get () in
                   let x =
                     let h1 = FStar_HyperStack_ST.get () in
                     let xi = LowStar_Monotonic_Buffer.index inp i in f i xi in
                   (let h03 = FStar_HyperStack_ST.get () in
                    (let h1 = FStar_HyperStack_ST.get () in
                     LowStar_Monotonic_Buffer.upd' os i x);
                    (let h1 = FStar_HyperStack_ST.get () in ()));
                   (let h' = FStar_HyperStack_ST.get () in ()))
let (map_blocks_multi :
  buftype ->
    unit ->
      FStar_Monotonic_HyperStack.mem ->
        FStar_UInt32.t ->
          FStar_UInt32.t ->
            Obj.t ->
              Obj.t LowStar_Buffer.buffer ->
                unit -> (FStar_UInt32.t -> unit) -> unit)
  =
  fun t ->
    fun a ->
      fun h0 ->
        fun bs ->
          fun nb ->
            fun inp ->
              fun output ->
                fun spec_f ->
                  fun impl_f ->
                    let h01 = FStar_HyperStack_ST.get () in
                    Obj.magic (fun h -> fun i -> ());
                    C_Loops.for1 (FStar_UInt32.uint_to_t Prims.int_zero) nb
                      ()
                      (fun i ->
                         let block =
                           LowStar_Monotonic_Buffer.msub output
                             (FStar_UInt32.mul i bs) () in
                         let h0_ = FStar_HyperStack_ST.get () in
                         impl_f i; (let h = FStar_HyperStack_ST.get () in ()))

let (map_blocks :
  buftype ->
    unit ->
      FStar_Monotonic_HyperStack.mem ->
        FStar_UInt32.t ->
          FStar_UInt32.t ->
            Obj.t ->
              Obj.t LowStar_Buffer.buffer ->
                unit ->
                  unit ->
                    (FStar_UInt32.t -> unit) ->
                      (FStar_UInt32.t -> unit) -> unit)
  =
  fun t ->
    fun a ->
      fun h0 ->
        fun len ->
          fun blocksize ->
            fun inp ->
              fun output ->
                fun spec_f ->
                  fun spec_l ->
                    fun impl_f ->
                      fun impl_l ->
                        let nb = FStar_UInt32.div len blocksize in
                        let rem = FStar_UInt32.rem len blocksize in
                        let blen = FStar_UInt32.mul nb blocksize in
                        let ib =
                          match t with
                          | MUT ->
                              Obj.repr
                                (LowStar_Monotonic_Buffer.msub
                                   (Obj.magic inp)
                                   (FStar_UInt32.uint_to_t Prims.int_zero) ())
                          | IMMUT ->
                              Obj.repr
                                (LowStar_Monotonic_Buffer.msub
                                   (Obj.magic inp)
                                   (FStar_UInt32.uint_to_t Prims.int_zero) ())
                          | CONST ->
                              Obj.repr
                                (LowStar_ConstBuffer.sub (Obj.magic inp)
                                   (FStar_UInt32.uint_to_t Prims.int_zero) ()) in
                        let ob =
                          LowStar_Monotonic_Buffer.msub output
                            (FStar_UInt32.uint_to_t Prims.int_zero) () in
                        let il =
                          match t with
                          | MUT ->
                              Obj.repr
                                (LowStar_Monotonic_Buffer.msub
                                   (Obj.magic inp) blen ())
                          | IMMUT ->
                              Obj.repr
                                (LowStar_Monotonic_Buffer.msub
                                   (Obj.magic inp) blen ())
                          | CONST ->
                              Obj.repr
                                (LowStar_ConstBuffer.sub (Obj.magic inp) blen
                                   ()) in
                        let ol =
                          match t with
                          | MUT ->
                              Obj.repr
                                (LowStar_Monotonic_Buffer.msub
                                   (Obj.magic inp) blen ())
                          | IMMUT ->
                              Obj.repr
                                (LowStar_Monotonic_Buffer.msub
                                   (Obj.magic inp) blen ())
                          | CONST ->
                              Obj.repr
                                (LowStar_ConstBuffer.sub (Obj.magic inp) blen
                                   ()) in
                        (let h01 = FStar_HyperStack_ST.get () in
                         Obj.magic (fun h -> fun i -> ());
                         C_Loops.for1 (FStar_UInt32.uint_to_t Prims.int_zero)
                           nb ()
                           (fun i ->
                              let block =
                                LowStar_Monotonic_Buffer.msub ob
                                  (FStar_UInt32.mul i blocksize) () in
                              let h0_ = FStar_HyperStack_ST.get () in
                              impl_f i;
                              (let h = FStar_HyperStack_ST.get () in ())));
                        if
                          FStar_UInt32.gt rem
                            (FStar_UInt32.uint_to_t Prims.int_zero)
                        then
                          (impl_l nb;
                           (let h1 = FStar_HyperStack_ST.get () in ()))
                        else ()