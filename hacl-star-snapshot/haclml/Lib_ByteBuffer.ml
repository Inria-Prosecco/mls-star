open Prims
let (uint_to_be :
  Lib_IntTypes.inttype -> Lib_IntTypes.secrecy_level -> Obj.t -> Obj.t) =
  fun t ->
    fun l ->
      fun u ->
        match (t, l) with
        | (Lib_IntTypes.U1, uu___) -> Obj.repr u
        | (Lib_IntTypes.U8, uu___) -> Obj.repr u
        | (Lib_IntTypes.U16, Lib_IntTypes.PUB) ->
            Obj.repr (LowStar_Endianness.htobe16 (Obj.magic u))
        | (Lib_IntTypes.U16, Lib_IntTypes.SEC) ->
            Obj.repr (LowStar_Endianness.htobe16 (Obj.magic u))
        | (Lib_IntTypes.U32, Lib_IntTypes.PUB) ->
            Obj.repr (LowStar_Endianness.htobe32 (Obj.magic u))
        | (Lib_IntTypes.U32, Lib_IntTypes.SEC) ->
            Obj.repr (LowStar_Endianness.htobe32 (Obj.magic u))
        | (Lib_IntTypes.U64, Lib_IntTypes.PUB) ->
            Obj.repr (LowStar_Endianness.htobe64 (Obj.magic u))
        | (Lib_IntTypes.U64, Lib_IntTypes.SEC) ->
            Obj.repr (LowStar_Endianness.htobe64 (Obj.magic u))
let (uint_to_le :
  Lib_IntTypes.inttype -> Lib_IntTypes.secrecy_level -> Obj.t -> Obj.t) =
  fun t ->
    fun l ->
      fun u ->
        match (t, l) with
        | (Lib_IntTypes.U1, uu___) -> Obj.repr u
        | (Lib_IntTypes.U8, uu___) -> Obj.repr u
        | (Lib_IntTypes.U16, Lib_IntTypes.PUB) ->
            Obj.repr (LowStar_Endianness.htole16 (Obj.magic u))
        | (Lib_IntTypes.U16, Lib_IntTypes.SEC) ->
            Obj.repr (LowStar_Endianness.htole16 (Obj.magic u))
        | (Lib_IntTypes.U32, Lib_IntTypes.PUB) ->
            Obj.repr (LowStar_Endianness.htole32 (Obj.magic u))
        | (Lib_IntTypes.U32, Lib_IntTypes.SEC) ->
            Obj.repr (LowStar_Endianness.htole32 (Obj.magic u))
        | (Lib_IntTypes.U64, Lib_IntTypes.PUB) ->
            Obj.repr (LowStar_Endianness.htole64 (Obj.magic u))
        | (Lib_IntTypes.U64, Lib_IntTypes.SEC) ->
            Obj.repr (LowStar_Endianness.htole64 (Obj.magic u))
let (uint_from_be :
  Lib_IntTypes.inttype -> Lib_IntTypes.secrecy_level -> Obj.t -> Obj.t) =
  fun t ->
    fun l ->
      fun u ->
        match (t, l) with
        | (Lib_IntTypes.U1, uu___) -> Obj.repr u
        | (Lib_IntTypes.U8, uu___) -> Obj.repr u
        | (Lib_IntTypes.U16, Lib_IntTypes.PUB) ->
            Obj.repr (LowStar_Endianness.be16toh (Obj.magic u))
        | (Lib_IntTypes.U16, Lib_IntTypes.SEC) ->
            Obj.repr (LowStar_Endianness.be16toh (Obj.magic u))
        | (Lib_IntTypes.U32, Lib_IntTypes.PUB) ->
            Obj.repr (LowStar_Endianness.be32toh (Obj.magic u))
        | (Lib_IntTypes.U32, Lib_IntTypes.SEC) ->
            Obj.repr (LowStar_Endianness.be32toh (Obj.magic u))
        | (Lib_IntTypes.U64, Lib_IntTypes.PUB) ->
            Obj.repr (LowStar_Endianness.be64toh (Obj.magic u))
        | (Lib_IntTypes.U64, Lib_IntTypes.SEC) ->
            Obj.repr (LowStar_Endianness.be64toh (Obj.magic u))
let (uint_from_le :
  Lib_IntTypes.inttype -> Lib_IntTypes.secrecy_level -> Obj.t -> Obj.t) =
  fun t ->
    fun l ->
      fun u ->
        match (t, l) with
        | (Lib_IntTypes.U1, uu___) -> Obj.repr u
        | (Lib_IntTypes.U8, uu___) -> Obj.repr u
        | (Lib_IntTypes.U16, Lib_IntTypes.PUB) ->
            Obj.repr (LowStar_Endianness.le16toh (Obj.magic u))
        | (Lib_IntTypes.U16, Lib_IntTypes.SEC) ->
            Obj.repr (LowStar_Endianness.le16toh (Obj.magic u))
        | (Lib_IntTypes.U32, Lib_IntTypes.PUB) ->
            Obj.repr (LowStar_Endianness.le32toh (Obj.magic u))
        | (Lib_IntTypes.U32, Lib_IntTypes.SEC) ->
            Obj.repr (LowStar_Endianness.le32toh (Obj.magic u))
        | (Lib_IntTypes.U64, Lib_IntTypes.PUB) ->
            Obj.repr (LowStar_Endianness.le64toh (Obj.magic u))
        | (Lib_IntTypes.U64, Lib_IntTypes.SEC) ->
            Obj.repr (LowStar_Endianness.le64toh (Obj.magic u))
let (buf_eq_mask :
  Lib_IntTypes.inttype ->
    FStar_UInt32.t ->
      FStar_UInt32.t ->
        Obj.t LowStar_Buffer.buffer ->
          Obj.t LowStar_Buffer.buffer ->
            FStar_UInt32.t -> Obj.t LowStar_Buffer.buffer -> Obj.t)
  =
  fun t ->
    fun len1 ->
      fun len2 ->
        fun b1 ->
          fun b2 ->
            fun len ->
              fun res ->
                let h0 = FStar_HyperStack_ST.get () in
                Obj.magic (fun h -> fun i -> ());
                C_Loops.for1 (FStar_UInt32.uint_to_t Prims.int_zero) len ()
                  (fun i ->
                     let z0 =
                       LowStar_Monotonic_Buffer.index res
                         (FStar_UInt32.uint_to_t Prims.int_zero) in
                     (let uu___2 =
                        let uu___3 =
                          let uu___4 = LowStar_Monotonic_Buffer.index b1 i in
                          let uu___5 = LowStar_Monotonic_Buffer.index b2 i in
                          Lib_IntTypes.eq_mask t uu___4 uu___5 in
                        let uu___4 =
                          LowStar_Monotonic_Buffer.index res
                            (FStar_UInt32.uint_to_t Prims.int_zero) in
                        Lib_IntTypes.logand t Lib_IntTypes.SEC uu___3 uu___4 in
                      let h01 = FStar_HyperStack_ST.get () in
                      (let h = FStar_HyperStack_ST.get () in
                       LowStar_Monotonic_Buffer.upd' res
                         (FStar_UInt32.uint_to_t Prims.int_zero) uu___2);
                      (let h1 = FStar_HyperStack_ST.get () in ()));
                     (let z =
                        LowStar_Monotonic_Buffer.index res
                          (FStar_UInt32.uint_to_t Prims.int_zero) in
                      ()));
                LowStar_Monotonic_Buffer.index res
                  (FStar_UInt32.uint_to_t Prims.int_zero)
let (lbytes_eq :
  FStar_UInt32.t ->
    FStar_UInt8.t LowStar_Buffer.buffer ->
      FStar_UInt8.t LowStar_Buffer.buffer -> Prims.bool)
  =
  fun len ->
    fun b1 ->
      fun b2 ->
        FStar_HyperStack_ST.push_frame ();
        (let res =
           LowStar_Monotonic_Buffer.malloca
             (FStar_UInt8.uint_to_t (Prims.of_int (255)))
             (FStar_UInt32.uint_to_t Prims.int_one) in
         let z =
           let h0 = FStar_HyperStack_ST.get () in
           Obj.magic (fun h -> fun i -> ());
           C_Loops.for1 (FStar_UInt32.uint_to_t Prims.int_zero) len ()
             (fun i ->
                let z0 =
                  LowStar_Monotonic_Buffer.index res
                    (FStar_UInt32.uint_to_t Prims.int_zero) in
                (let uu___3 =
                   let uu___4 =
                     let uu___5 = LowStar_Monotonic_Buffer.index b1 i in
                     let uu___6 = LowStar_Monotonic_Buffer.index b2 i in
                     FStar_UInt8.eq_mask uu___5 uu___6 in
                   let uu___5 =
                     LowStar_Monotonic_Buffer.index res
                       (FStar_UInt32.uint_to_t Prims.int_zero) in
                   FStar_UInt8.logand uu___4 uu___5 in
                 let h01 = FStar_HyperStack_ST.get () in
                 (let h = FStar_HyperStack_ST.get () in
                  LowStar_Monotonic_Buffer.upd' res
                    (FStar_UInt32.uint_to_t Prims.int_zero) uu___3);
                 (let h1 = FStar_HyperStack_ST.get () in ()));
                (let z1 =
                   LowStar_Monotonic_Buffer.index res
                     (FStar_UInt32.uint_to_t Prims.int_zero) in
                 ()));
           LowStar_Monotonic_Buffer.index res
             (FStar_UInt32.uint_to_t Prims.int_zero) in
         FStar_HyperStack_ST.pop_frame ();
         z = (FStar_UInt8.uint_to_t (Prims.of_int (255))))
let (buf_mask_select :
  Lib_IntTypes.inttype ->
    FStar_UInt32.t ->
      Obj.t LowStar_Buffer.buffer ->
        Obj.t LowStar_Buffer.buffer ->
          Obj.t -> Obj.t LowStar_Buffer.buffer -> unit)
  =
  fun t ->
    fun len ->
      fun b1 ->
        fun b2 ->
          fun mask ->
            fun res ->
              let h0 = FStar_HyperStack_ST.get () in
              let h01 = FStar_HyperStack_ST.get () in
              Obj.magic (fun h -> fun i -> ());
              C_Loops.for1 (FStar_UInt32.uint_to_t Prims.int_zero) len ()
                (fun i ->
                   let os =
                     LowStar_Monotonic_Buffer.msub res
                       (FStar_UInt32.uint_to_t Prims.int_zero) () in
                   let h = FStar_HyperStack_ST.get () in
                   let x =
                     let h1 = FStar_HyperStack_ST.get () in
                     let uu___ = LowStar_Monotonic_Buffer.index b1 i in
                     let uu___1 = LowStar_Monotonic_Buffer.index b2 i in
                     Lib_IntTypes.logxor t Lib_IntTypes.SEC uu___1
                       (Lib_IntTypes.logand t Lib_IntTypes.SEC mask
                          (Lib_IntTypes.logxor t Lib_IntTypes.SEC uu___
                             uu___1)) in
                   (let h02 = FStar_HyperStack_ST.get () in
                    (let h1 = FStar_HyperStack_ST.get () in
                     LowStar_Monotonic_Buffer.upd' os i x);
                    (let h1 = FStar_HyperStack_ST.get () in ()));
                   (let h' = FStar_HyperStack_ST.get () in ()))


let (uint_from_bytes_le :
  Lib_IntTypes.inttype ->
    Lib_IntTypes.secrecy_level -> Obj.t LowStar_Buffer.buffer -> Obj.t)
  =
  fun t ->
    fun l ->
      fun i ->
        let h0 = FStar_HyperStack_ST.get () in
        match t with
        | Lib_IntTypes.U8 ->
            LowStar_Monotonic_Buffer.index i
              (FStar_UInt32.uint_to_t Prims.int_zero)
        | Lib_IntTypes.U16 ->
            let u = LowStar_Endianness.load16_le (Obj.magic i) in
            Lib_IntTypes.cast t l Lib_IntTypes.U16 l (Obj.magic u)
        | Lib_IntTypes.U32 ->
            let u = LowStar_Endianness.load32_le (Obj.magic i) in
            Lib_IntTypes.cast t l Lib_IntTypes.U32 l (Obj.magic u)
        | Lib_IntTypes.U64 ->
            let u = LowStar_Endianness.load64_le (Obj.magic i) in
            Lib_IntTypes.cast t l Lib_IntTypes.U64 l (Obj.magic u)
        | Lib_IntTypes.U128 ->
            let u = LowStar_Endianness.load128_le (Obj.magic i) in
            Lib_IntTypes.cast t l Lib_IntTypes.U128 l (Obj.magic u)
let (uint_from_bytes_be :
  Lib_IntTypes.inttype ->
    Lib_IntTypes.secrecy_level -> Obj.t LowStar_Buffer.buffer -> Obj.t)
  =
  fun t ->
    fun l ->
      fun i ->
        let h0 = FStar_HyperStack_ST.get () in
        match t with
        | Lib_IntTypes.U8 ->
            LowStar_Monotonic_Buffer.index i
              (FStar_UInt32.uint_to_t Prims.int_zero)
        | Lib_IntTypes.U16 ->
            let u = LowStar_Endianness.load16_be (Obj.magic i) in
            Lib_IntTypes.cast t l Lib_IntTypes.U16 l (Obj.magic u)
        | Lib_IntTypes.U32 ->
            let u = LowStar_Endianness.load32_be (Obj.magic i) in
            Lib_IntTypes.cast t l Lib_IntTypes.U32 l (Obj.magic u)
        | Lib_IntTypes.U64 ->
            let u = LowStar_Endianness.load64_be (Obj.magic i) in
            Lib_IntTypes.cast t l Lib_IntTypes.U64 l (Obj.magic u)
        | Lib_IntTypes.U128 ->
            let u = LowStar_Endianness.load128_be (Obj.magic i) in
            Lib_IntTypes.cast t l Lib_IntTypes.U128 l (Obj.magic u)


let (uint_to_bytes_le :
  Lib_IntTypes.inttype ->
    Lib_IntTypes.secrecy_level ->
      Obj.t LowStar_Buffer.buffer -> Obj.t -> unit)
  =
  fun t ->
    fun l ->
      fun o ->
        fun i ->
          match t with
          | Lib_IntTypes.U1 ->
              ((let h0 = FStar_HyperStack_ST.get () in
                (let h = FStar_HyperStack_ST.get () in
                 LowStar_Monotonic_Buffer.upd' o
                   (FStar_UInt32.uint_to_t Prims.int_zero) i);
                (let h1 = FStar_HyperStack_ST.get () in ()));
               (let h1 = FStar_HyperStack_ST.get () in ()))
          | Lib_IntTypes.U8 ->
              ((let h0 = FStar_HyperStack_ST.get () in
                (let h = FStar_HyperStack_ST.get () in
                 LowStar_Monotonic_Buffer.upd' o
                   (FStar_UInt32.uint_to_t Prims.int_zero) i);
                (let h1 = FStar_HyperStack_ST.get () in ()));
               (let h1 = FStar_HyperStack_ST.get () in ()))
          | Lib_IntTypes.U16 ->
              (LowStar_Endianness.store16_le (Obj.magic o) (Obj.magic i);
               (let h1 = FStar_HyperStack_ST.get () in ()))
          | Lib_IntTypes.U32 ->
              (LowStar_Endianness.store32_le (Obj.magic o) (Obj.magic i);
               (let h1 = FStar_HyperStack_ST.get () in ()))
          | Lib_IntTypes.U64 ->
              (LowStar_Endianness.store64_le (Obj.magic o) (Obj.magic i);
               (let h1 = FStar_HyperStack_ST.get () in ()))
          | Lib_IntTypes.U128 ->
              (LowStar_Endianness.store128_le (Obj.magic o) (Obj.magic i);
               (let h1 = FStar_HyperStack_ST.get () in ()))
let (uint_to_bytes_be :
  Lib_IntTypes.inttype ->
    Lib_IntTypes.secrecy_level ->
      Obj.t LowStar_Buffer.buffer -> Obj.t -> unit)
  =
  fun t ->
    fun l ->
      fun o ->
        fun i ->
          match t with
          | Lib_IntTypes.U1 ->
              ((let h0 = FStar_HyperStack_ST.get () in
                (let h = FStar_HyperStack_ST.get () in
                 LowStar_Monotonic_Buffer.upd' o
                   (FStar_UInt32.uint_to_t Prims.int_zero) i);
                (let h1 = FStar_HyperStack_ST.get () in ()));
               (let h1 = FStar_HyperStack_ST.get () in ()))
          | Lib_IntTypes.U8 ->
              ((let h0 = FStar_HyperStack_ST.get () in
                (let h = FStar_HyperStack_ST.get () in
                 LowStar_Monotonic_Buffer.upd' o
                   (FStar_UInt32.uint_to_t Prims.int_zero) i);
                (let h1 = FStar_HyperStack_ST.get () in ()));
               (let h1 = FStar_HyperStack_ST.get () in ()))
          | Lib_IntTypes.U16 ->
              (LowStar_Endianness.store16_be (Obj.magic o) (Obj.magic i);
               (let h1 = FStar_HyperStack_ST.get () in ()))
          | Lib_IntTypes.U32 ->
              (LowStar_Endianness.store32_be (Obj.magic o) (Obj.magic i);
               (let h1 = FStar_HyperStack_ST.get () in ()))
          | Lib_IntTypes.U64 ->
              (LowStar_Endianness.store64_be (Obj.magic o) (Obj.magic i);
               (let h1 = FStar_HyperStack_ST.get () in ()))
          | Lib_IntTypes.U128 ->
              (LowStar_Endianness.store128_be (Obj.magic o) (Obj.magic i);
               (let h1 = FStar_HyperStack_ST.get () in ()))
let (uints_from_bytes_le :
  Lib_IntTypes.inttype ->
    Lib_IntTypes.secrecy_level ->
      FStar_UInt32.t ->
        Obj.t LowStar_Buffer.buffer -> Obj.t LowStar_Buffer.buffer -> unit)
  =
  fun t ->
    fun l ->
      fun len ->
        fun o ->
          fun i ->
            let h0 = FStar_HyperStack_ST.get () in
            (let h01 = FStar_HyperStack_ST.get () in
             Obj.magic (fun h -> fun i1 -> ());
             C_Loops.for1 (FStar_UInt32.uint_to_t Prims.int_zero) len ()
               (fun i1 ->
                  let os =
                    LowStar_Monotonic_Buffer.msub o
                      (FStar_UInt32.uint_to_t Prims.int_zero) () in
                  let h = FStar_HyperStack_ST.get () in
                  let x =
                    let h1 = FStar_HyperStack_ST.get () in
                    let bj =
                      LowStar_Monotonic_Buffer.msub i
                        (FStar_UInt32.mul i1
                           (FStar_UInt32.uint_to_t (Lib_IntTypes.numbytes t)))
                        () in
                    let r =
                      let h02 = FStar_HyperStack_ST.get () in
                      match t with
                      | Lib_IntTypes.U8 ->
                          LowStar_Monotonic_Buffer.index bj
                            (FStar_UInt32.uint_to_t Prims.int_zero)
                      | Lib_IntTypes.U16 ->
                          let u = LowStar_Endianness.load16_le (Obj.magic bj) in
                          Lib_IntTypes.cast t l Lib_IntTypes.U16 l
                            (Obj.magic u)
                      | Lib_IntTypes.U32 ->
                          let u = LowStar_Endianness.load32_le (Obj.magic bj) in
                          Lib_IntTypes.cast t l Lib_IntTypes.U32 l
                            (Obj.magic u)
                      | Lib_IntTypes.U64 ->
                          let u = LowStar_Endianness.load64_le (Obj.magic bj) in
                          Lib_IntTypes.cast t l Lib_IntTypes.U64 l
                            (Obj.magic u)
                      | Lib_IntTypes.U128 ->
                          let u =
                            LowStar_Endianness.load128_le (Obj.magic bj) in
                          Lib_IntTypes.cast t l Lib_IntTypes.U128 l
                            (Obj.magic u) in
                    r in
                  (let h02 = FStar_HyperStack_ST.get () in
                   (let h1 = FStar_HyperStack_ST.get () in
                    LowStar_Monotonic_Buffer.upd' os i1 x);
                   (let h1 = FStar_HyperStack_ST.get () in ()));
                  (let h' = FStar_HyperStack_ST.get () in ())));
            (let h1 = FStar_HyperStack_ST.get () in ())
let (uints_from_bytes_be :
  Lib_IntTypes.inttype ->
    Lib_IntTypes.secrecy_level ->
      FStar_UInt32.t ->
        Obj.t LowStar_Buffer.buffer -> Obj.t LowStar_Buffer.buffer -> unit)
  =
  fun t ->
    fun l ->
      fun len ->
        fun o ->
          fun i ->
            let h0 = FStar_HyperStack_ST.get () in
            (let h01 = FStar_HyperStack_ST.get () in
             Obj.magic (fun h -> fun i1 -> ());
             C_Loops.for1 (FStar_UInt32.uint_to_t Prims.int_zero) len ()
               (fun i1 ->
                  let os =
                    LowStar_Monotonic_Buffer.msub o
                      (FStar_UInt32.uint_to_t Prims.int_zero) () in
                  let h = FStar_HyperStack_ST.get () in
                  let x =
                    let h1 = FStar_HyperStack_ST.get () in
                    let bj =
                      LowStar_Monotonic_Buffer.msub i
                        (FStar_UInt32.mul i1
                           (FStar_UInt32.uint_to_t (Lib_IntTypes.numbytes t)))
                        () in
                    let r =
                      let h02 = FStar_HyperStack_ST.get () in
                      match t with
                      | Lib_IntTypes.U8 ->
                          LowStar_Monotonic_Buffer.index bj
                            (FStar_UInt32.uint_to_t Prims.int_zero)
                      | Lib_IntTypes.U16 ->
                          let u = LowStar_Endianness.load16_be (Obj.magic bj) in
                          Lib_IntTypes.cast t l Lib_IntTypes.U16 l
                            (Obj.magic u)
                      | Lib_IntTypes.U32 ->
                          let u = LowStar_Endianness.load32_be (Obj.magic bj) in
                          Lib_IntTypes.cast t l Lib_IntTypes.U32 l
                            (Obj.magic u)
                      | Lib_IntTypes.U64 ->
                          let u = LowStar_Endianness.load64_be (Obj.magic bj) in
                          Lib_IntTypes.cast t l Lib_IntTypes.U64 l
                            (Obj.magic u)
                      | Lib_IntTypes.U128 ->
                          let u =
                            LowStar_Endianness.load128_be (Obj.magic bj) in
                          Lib_IntTypes.cast t l Lib_IntTypes.U128 l
                            (Obj.magic u) in
                    r in
                  (let h02 = FStar_HyperStack_ST.get () in
                   (let h1 = FStar_HyperStack_ST.get () in
                    LowStar_Monotonic_Buffer.upd' os i1 x);
                   (let h1 = FStar_HyperStack_ST.get () in ()));
                  (let h' = FStar_HyperStack_ST.get () in ())));
            (let h1 = FStar_HyperStack_ST.get () in ())
let (uints_to_bytes_le :
  Lib_IntTypes.inttype ->
    Lib_IntTypes.secrecy_level ->
      FStar_UInt32.t ->
        Obj.t LowStar_Buffer.buffer -> Obj.t LowStar_Buffer.buffer -> unit)
  =
  fun t ->
    fun l ->
      fun len ->
        fun o ->
          fun i ->
            let h0 = FStar_HyperStack_ST.get () in
            let h01 = FStar_HyperStack_ST.get () in
            Obj.magic (fun h -> fun i1 -> ());
            C_Loops.for1 (FStar_UInt32.uint_to_t Prims.int_zero) len ()
              (fun i1 ->
                 let block =
                   LowStar_Monotonic_Buffer.msub o
                     (FStar_UInt32.mul i1
                        (FStar_UInt32.uint_to_t (Lib_IntTypes.numbytes t)))
                     () in
                 let h0_ = FStar_HyperStack_ST.get () in
                 (let uu___3 =
                    LowStar_Monotonic_Buffer.msub o
                      (FStar_UInt32.mul_mod i1
                         (FStar_UInt32.uint_to_t (Lib_IntTypes.numbytes t)))
                      () in
                  let uu___4 = LowStar_Monotonic_Buffer.index i i1 in
                  match t with
                  | Lib_IntTypes.U1 ->
                      ((let h02 = FStar_HyperStack_ST.get () in
                        (let h = FStar_HyperStack_ST.get () in
                         LowStar_Monotonic_Buffer.upd' uu___3
                           (FStar_UInt32.uint_to_t Prims.int_zero) uu___4);
                        (let h1 = FStar_HyperStack_ST.get () in ()));
                       (let h1 = FStar_HyperStack_ST.get () in ()))
                  | Lib_IntTypes.U8 ->
                      ((let h02 = FStar_HyperStack_ST.get () in
                        (let h = FStar_HyperStack_ST.get () in
                         LowStar_Monotonic_Buffer.upd' uu___3
                           (FStar_UInt32.uint_to_t Prims.int_zero) uu___4);
                        (let h1 = FStar_HyperStack_ST.get () in ()));
                       (let h1 = FStar_HyperStack_ST.get () in ()))
                  | Lib_IntTypes.U16 ->
                      (LowStar_Endianness.store16_le (Obj.magic uu___3)
                         (Obj.magic uu___4);
                       (let h1 = FStar_HyperStack_ST.get () in ()))
                  | Lib_IntTypes.U32 ->
                      (LowStar_Endianness.store32_le (Obj.magic uu___3)
                         (Obj.magic uu___4);
                       (let h1 = FStar_HyperStack_ST.get () in ()))
                  | Lib_IntTypes.U64 ->
                      (LowStar_Endianness.store64_le (Obj.magic uu___3)
                         (Obj.magic uu___4);
                       (let h1 = FStar_HyperStack_ST.get () in ()))
                  | Lib_IntTypes.U128 ->
                      (LowStar_Endianness.store128_le (Obj.magic uu___3)
                         (Obj.magic uu___4);
                       (let h1 = FStar_HyperStack_ST.get () in ())));
                 (let h = FStar_HyperStack_ST.get () in ()));
            (let h1 = FStar_HyperStack_ST.get () in ())
let (uints_to_bytes_be :
  Lib_IntTypes.inttype ->
    Lib_IntTypes.secrecy_level ->
      FStar_UInt32.t ->
        Obj.t LowStar_Buffer.buffer -> Obj.t LowStar_Buffer.buffer -> unit)
  =
  fun t ->
    fun l ->
      fun len ->
        fun o ->
          fun i ->
            let h0 = FStar_HyperStack_ST.get () in
            let h01 = FStar_HyperStack_ST.get () in
            Obj.magic (fun h -> fun i1 -> ());
            C_Loops.for1 (FStar_UInt32.uint_to_t Prims.int_zero) len ()
              (fun i1 ->
                 let block =
                   LowStar_Monotonic_Buffer.msub o
                     (FStar_UInt32.mul i1
                        (FStar_UInt32.uint_to_t (Lib_IntTypes.numbytes t)))
                     () in
                 let h0_ = FStar_HyperStack_ST.get () in
                 (let uu___3 =
                    LowStar_Monotonic_Buffer.msub o
                      (FStar_UInt32.mul_mod i1
                         (FStar_UInt32.uint_to_t (Lib_IntTypes.numbytes t)))
                      () in
                  let uu___4 = LowStar_Monotonic_Buffer.index i i1 in
                  match t with
                  | Lib_IntTypes.U1 ->
                      ((let h02 = FStar_HyperStack_ST.get () in
                        (let h = FStar_HyperStack_ST.get () in
                         LowStar_Monotonic_Buffer.upd' uu___3
                           (FStar_UInt32.uint_to_t Prims.int_zero) uu___4);
                        (let h1 = FStar_HyperStack_ST.get () in ()));
                       (let h1 = FStar_HyperStack_ST.get () in ()))
                  | Lib_IntTypes.U8 ->
                      ((let h02 = FStar_HyperStack_ST.get () in
                        (let h = FStar_HyperStack_ST.get () in
                         LowStar_Monotonic_Buffer.upd' uu___3
                           (FStar_UInt32.uint_to_t Prims.int_zero) uu___4);
                        (let h1 = FStar_HyperStack_ST.get () in ()));
                       (let h1 = FStar_HyperStack_ST.get () in ()))
                  | Lib_IntTypes.U16 ->
                      (LowStar_Endianness.store16_be (Obj.magic uu___3)
                         (Obj.magic uu___4);
                       (let h1 = FStar_HyperStack_ST.get () in ()))
                  | Lib_IntTypes.U32 ->
                      (LowStar_Endianness.store32_be (Obj.magic uu___3)
                         (Obj.magic uu___4);
                       (let h1 = FStar_HyperStack_ST.get () in ()))
                  | Lib_IntTypes.U64 ->
                      (LowStar_Endianness.store64_be (Obj.magic uu___3)
                         (Obj.magic uu___4);
                       (let h1 = FStar_HyperStack_ST.get () in ()))
                  | Lib_IntTypes.U128 ->
                      (LowStar_Endianness.store128_be (Obj.magic uu___3)
                         (Obj.magic uu___4);
                       (let h1 = FStar_HyperStack_ST.get () in ())));
                 (let h = FStar_HyperStack_ST.get () in ()));
            (let h1 = FStar_HyperStack_ST.get () in ())
let (uint32s_to_bytes_le :
  FStar_UInt32.t ->
    FStar_UInt8.t LowStar_Buffer.buffer ->
      FStar_UInt32.t LowStar_Buffer.buffer -> unit)
  =
  fun len ->
    fun o ->
      fun i ->
        let h0 = FStar_HyperStack_ST.get () in
        let h01 = FStar_HyperStack_ST.get () in
        Obj.magic (fun h -> fun i1 -> ());
        C_Loops.for1 (FStar_UInt32.uint_to_t Prims.int_zero) len ()
          (fun i1 ->
             let block =
               LowStar_Monotonic_Buffer.msub o
                 (FStar_UInt32.mul i1
                    (FStar_UInt32.uint_to_t (Prims.of_int (4)))) () in
             let h0_ = FStar_HyperStack_ST.get () in
             (let uu___3 =
                LowStar_Monotonic_Buffer.msub o
                  (FStar_UInt32.mul_mod i1
                     (FStar_UInt32.uint_to_t (Prims.of_int (4)))) () in
              let uu___4 = LowStar_Monotonic_Buffer.index i i1 in
              LowStar_Endianness.store32_le uu___3 uu___4;
              (let h1 = FStar_HyperStack_ST.get () in ()));
             (let h = FStar_HyperStack_ST.get () in ()));
        (let h1 = FStar_HyperStack_ST.get () in ())
let (uint32s_from_bytes_le :
  FStar_UInt32.t ->
    FStar_UInt32.t LowStar_Buffer.buffer ->
      FStar_UInt8.t LowStar_Buffer.buffer -> unit)
  =
  fun len ->
    fun o ->
      fun i ->
        let h0 = FStar_HyperStack_ST.get () in
        (let h01 = FStar_HyperStack_ST.get () in
         Obj.magic (fun h -> fun i1 -> ());
         C_Loops.for1 (FStar_UInt32.uint_to_t Prims.int_zero) len ()
           (fun i1 ->
              let os =
                LowStar_Monotonic_Buffer.msub o
                  (FStar_UInt32.uint_to_t Prims.int_zero) () in
              let h = FStar_HyperStack_ST.get () in
              let x =
                let h1 = FStar_HyperStack_ST.get () in
                let bj =
                  LowStar_Monotonic_Buffer.msub i
                    (FStar_UInt32.mul i1
                       (FStar_UInt32.uint_to_t (Prims.of_int (4)))) () in
                let r =
                  let h02 = FStar_HyperStack_ST.get () in
                  let u = LowStar_Endianness.load32_le bj in u in
                r in
              (let h02 = FStar_HyperStack_ST.get () in
               (let h1 = FStar_HyperStack_ST.get () in
                LowStar_Monotonic_Buffer.upd' os i1 x);
               (let h1 = FStar_HyperStack_ST.get () in ()));
              (let h' = FStar_HyperStack_ST.get () in ())));
        (let h1 = FStar_HyperStack_ST.get () in ())
let (uint_at_index_le :
  Lib_IntTypes.inttype ->
    Lib_IntTypes.secrecy_level ->
      FStar_UInt32.t ->
        Obj.t LowStar_Buffer.buffer -> FStar_UInt32.t -> Obj.t)
  =
  fun t ->
    fun l ->
      fun len ->
        fun i ->
          fun idx ->
            let b =
              LowStar_Monotonic_Buffer.msub i
                (FStar_UInt32.mul idx
                   (FStar_UInt32.uint_to_t (Lib_IntTypes.numbytes t))) () in
            let h0 = FStar_HyperStack_ST.get () in
            match t with
            | Lib_IntTypes.U8 ->
                LowStar_Monotonic_Buffer.index b
                  (FStar_UInt32.uint_to_t Prims.int_zero)
            | Lib_IntTypes.U16 ->
                let u = LowStar_Endianness.load16_le (Obj.magic b) in
                Lib_IntTypes.cast t l Lib_IntTypes.U16 l (Obj.magic u)
            | Lib_IntTypes.U32 ->
                let u = LowStar_Endianness.load32_le (Obj.magic b) in
                Lib_IntTypes.cast t l Lib_IntTypes.U32 l (Obj.magic u)
            | Lib_IntTypes.U64 ->
                let u = LowStar_Endianness.load64_le (Obj.magic b) in
                Lib_IntTypes.cast t l Lib_IntTypes.U64 l (Obj.magic u)
            | Lib_IntTypes.U128 ->
                let u = LowStar_Endianness.load128_le (Obj.magic b) in
                Lib_IntTypes.cast t l Lib_IntTypes.U128 l (Obj.magic u)
let (uint_at_index_be :
  Lib_IntTypes.inttype ->
    Lib_IntTypes.secrecy_level ->
      FStar_UInt32.t ->
        Obj.t LowStar_Buffer.buffer -> FStar_UInt32.t -> Obj.t)
  =
  fun t ->
    fun l ->
      fun len ->
        fun i ->
          fun idx ->
            let b =
              LowStar_Monotonic_Buffer.msub i
                (FStar_UInt32.mul idx
                   (FStar_UInt32.uint_to_t (Lib_IntTypes.numbytes t))) () in
            let h0 = FStar_HyperStack_ST.get () in
            match t with
            | Lib_IntTypes.U8 ->
                LowStar_Monotonic_Buffer.index b
                  (FStar_UInt32.uint_to_t Prims.int_zero)
            | Lib_IntTypes.U16 ->
                let u = LowStar_Endianness.load16_be (Obj.magic b) in
                Lib_IntTypes.cast t l Lib_IntTypes.U16 l (Obj.magic u)
            | Lib_IntTypes.U32 ->
                let u = LowStar_Endianness.load32_be (Obj.magic b) in
                Lib_IntTypes.cast t l Lib_IntTypes.U32 l (Obj.magic u)
            | Lib_IntTypes.U64 ->
                let u = LowStar_Endianness.load64_be (Obj.magic b) in
                Lib_IntTypes.cast t l Lib_IntTypes.U64 l (Obj.magic u)
            | Lib_IntTypes.U128 ->
                let u = LowStar_Endianness.load128_be (Obj.magic b) in
                Lib_IntTypes.cast t l Lib_IntTypes.U128 l (Obj.magic u)