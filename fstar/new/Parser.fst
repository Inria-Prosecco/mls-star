module Parser

module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module IT = Lib.IntTypes
module E = FStar.Endianness
open Lib.ByteSequence

#set-options "--fuel 0 --ifuel 2"

(*** Basic definitions ***)

type non_empty_bytes = b:bytes{0 < Seq.length b}
type consumed_length (b:bytes) = n:nat{1 <= n /\ n <= Seq.length b}
type bare_parser (a:Type) = b:bytes -> option (a & consumed_length b)
type bare_serializer (a:Type) = a -> non_empty_bytes

let delete_prefix (b:bytes) (i:consumed_length b) : bytes =
  Seq.slice b i (Seq.length b)

val delete_prefix_length: b:bytes -> i:consumed_length b -> Lemma
  (Seq.length (delete_prefix b i) == (Seq.length b) - i)
  [SMTPat (Seq.length (delete_prefix b i))]
let delete_prefix_length b i = ()

val delete_prefix_index: b:bytes -> i:consumed_length b -> j:nat{j < Seq.length (delete_prefix b i)} -> Lemma
  (Seq.index (delete_prefix b i) j == Seq.index b (j+i))
  [SMTPat (Seq.index (delete_prefix b i) j)]
let delete_prefix_index b i j = ()

noeq type parser_serializer (a:Type) = {
  parse: bare_parser a;
  serialize: bare_serializer a;
  parse_serialize_inv: x:a -> Lemma (
    parse (serialize x) == Some (x, Seq.length (serialize x))
  );
  serialize_parse_inv: buf:bytes -> Lemma (
    match parse buf with
    | Some (x, l) ->  serialize x == (Seq.slice buf 0 l)
    | None -> True
  );
  parse_no_lookahead: b1:bytes -> b2:bytes -> Lemma
    (requires (
      match parse b1 with
      | Some (_, l) -> l <= Seq.length b2 /\ (forall (i:nat). i < l ==> Seq.index b1 i == Seq.index b2 i)
      | None -> True
    ))
    (ensures (
      match parse b1 with
      | Some (x1, l1) -> begin
        match parse b2 with
        | Some (x2, l2) -> x1 == x2 /\ l1 == l2
        | None -> False
      end
      | None -> True
    ))
}

(*** Parser combinators ***)

let bind (#a:Type) (#b:a -> Type) (ps_a:parser_serializer a) (ps_b:(xa:a -> parser_serializer (b xa))): parser_serializer (xa:a&(b xa)) =
  let parse_ab (buf:bytes): option ((xa:a&(b xa)) & consumed_length buf) =
    match ps_a.parse buf with
    | None -> None
    | Some (xa, la) -> begin
      match (ps_b xa).parse (delete_prefix buf la) with
      | None -> None
      | Some (xb, lb) ->
        Some ((|xa, xb|), la+lb)
    end
  in
  let serialize_ab (x:(xa:a&(b xa))): non_empty_bytes =
    let (|xa, xb|) = x in
    Seq.append (ps_a.serialize xa) ((ps_b xa).serialize xb)
  in
  {
    parse = parse_ab;
    serialize = serialize_ab;
    parse_serialize_inv = (fun (x:(xa:a&(b xa))) ->
      let (|xa, xb|) = x in
      ps_a.parse_no_lookahead (ps_a.serialize xa) (serialize_ab x);
      ps_a.parse_serialize_inv xa;
      (ps_b xa).parse_serialize_inv xb;
      assert (Seq.equal (delete_prefix (serialize_ab x) (Seq.length (ps_a.serialize xa))) ((ps_b xa).serialize xb))
    );
    serialize_parse_inv = (fun (buf:bytes) ->
      match parse_ab buf with
      | None -> ()
      | Some (xab, l) ->
        let (xa, la) = Some?.v (ps_a.parse buf) in
        let (xb, lb) = Some?.v ((ps_b xa).parse (delete_prefix buf la)) in
        ps_a.serialize_parse_inv buf;
        (ps_b xa).serialize_parse_inv (delete_prefix buf la);
        assert (Seq.equal (Seq.slice buf 0 (la+lb)) (serialize_ab xab))
    );
    parse_no_lookahead = (fun (b1 b2:bytes) ->
      match parse_ab b1 with
      | None -> ()
      | Some (xab, l) ->
        let (|xa, xb|) = xab in
        ps_a.parse_no_lookahead b1 b2;
        let (_, la1) = Some?.v (ps_a.parse b1) in
        let (_, la2) = Some?.v (ps_a.parse b2) in
        (ps_b xa).parse_no_lookahead (delete_prefix b1 la1) (delete_prefix b2 la2)
    )
  }

val isomorphism: #a:Type -> b:Type -> parser_serializer a -> f:(a -> b) -> g:(b -> a) -> Pure (parser_serializer b)
  (requires (forall xa. g (f xa) == xa) /\ (forall xb. f (g xb) == xb))
  (ensures fun _ -> True)
let isomorphism #a b ps_a f g =
  let parse_b buf =
    match ps_a.parse buf with
    | Some (xa, l) -> Some (f xa, l)
    | None -> None
  in
  let serialize_b xb =
    ps_a.serialize (g xb)
  in
  {
    parse = parse_b;
    serialize = serialize_b;
    parse_serialize_inv = (fun (x:b) ->
      ps_a.parse_serialize_inv (g x)
    );
    serialize_parse_inv = (fun (buf:bytes) ->
      ps_a.serialize_parse_inv buf
    );
    parse_no_lookahead = (fun (b1 b2:bytes) ->
      ps_a.parse_no_lookahead b1 b2
    )
  }

(*** Parser for basic types ***)

val hacl_u8_to_fstar_u8: IT.uint8 -> U8.t
let hacl_u8_to_fstar_u8 x =
  U8.uint_to_t (IT.v x)

val fstar_u8_to_hacl_u8: U8.t -> IT.uint8
let fstar_u8_to_hacl_u8 x =
  IT.u8 (U8.v x)

val seq_map: #a:Type -> #b:Type -> (a -> b) -> Seq.seq a -> Seq.seq b
let seq_map #a #b f s =
  Seq.init (Seq.length s) (fun i -> f (Seq.index s i))

val hacl_bytes_to_fstar_bytes: bytes -> E.bytes
let hacl_bytes_to_fstar_bytes b =
  seq_map hacl_u8_to_fstar_u8 b

val fstar_bytes_to_hacl_bytes: E.bytes -> bytes
let fstar_bytes_to_hacl_bytes b =
  seq_map fstar_u8_to_hacl_u8 b

val fstar_hacl_fstar_bytes_lemma: x:E.bytes -> Lemma
  (hacl_bytes_to_fstar_bytes (fstar_bytes_to_hacl_bytes x) == x)
  [SMTPat (hacl_bytes_to_fstar_bytes (fstar_bytes_to_hacl_bytes x))]
let fstar_hacl_fstar_bytes_lemma x =
  assert(Seq.equal (hacl_bytes_to_fstar_bytes (fstar_bytes_to_hacl_bytes x)) x)

val hacl_fstar_hacl_bytes_lemma: x:bytes -> Lemma
  (fstar_bytes_to_hacl_bytes (hacl_bytes_to_fstar_bytes x) == x)
  [SMTPat (fstar_bytes_to_hacl_bytes (hacl_bytes_to_fstar_bytes x))]
let hacl_fstar_hacl_bytes_lemma x =
  assert(Seq.equal (fstar_bytes_to_hacl_bytes (hacl_bytes_to_fstar_bytes x)) x)

val ps_uint:
  nbytes:pos ->
  hacl_uint:Type -> fstar_uint:Type ->
  hacl_to_fstar_uint:(hacl_uint -> fstar_uint) -> fstar_to_hacl_uint:(fstar_uint -> hacl_uint) ->
  fstar_uint_to_be:(fstar_uint -> (b:E.bytes{Seq.length b == nbytes})) -> be_to_fstar_uint:((b:E.bytes{Seq.length b == nbytes}) -> fstar_uint) ->
  Pure (parser_serializer hacl_uint)
  (requires
    (forall x. hacl_to_fstar_uint (fstar_to_hacl_uint x) == x) /\
    (forall x. fstar_to_hacl_uint (hacl_to_fstar_uint x) == x) /\
    (forall x. fstar_uint_to_be (be_to_fstar_uint x) == x) /\
    (forall x. be_to_fstar_uint (fstar_uint_to_be x) == x)
  )
  (ensures fun _ -> True)
let ps_uint nbytes hacl_uint fstar_uint hacl_to_fstar_uint fstar_to_hacl_uint fstar_uint_to_be be_to_fstar_uint =
  let parse_uint (buf:bytes) =
    if Seq.length buf < nbytes then
      None
    else
      let b = Seq.slice buf 0 nbytes in
      let x = be_to_fstar_uint (hacl_bytes_to_fstar_bytes b) in
      Some (fstar_to_hacl_uint x, (nbytes <: consumed_length buf))
  in
  let serialize_uint (x:hacl_uint): non_empty_bytes =
    fstar_bytes_to_hacl_bytes (fstar_uint_to_be (hacl_to_fstar_uint x))
  in
  {
    parse = parse_uint;
    serialize = serialize_uint;
    parse_serialize_inv = (fun x -> ());
    serialize_parse_inv = (fun (buf:bytes) -> ());
    parse_no_lookahead = (fun (b1 b2:bytes) ->
      match parse_uint b1 with
      | None -> ()
      | Some _ -> assert(Seq.equal (Seq.slice b1 0 nbytes) (Seq.slice b2 0 nbytes))
    )
  }

val e_n_to_be_be_to_n_forall: len:nat -> Lemma (
  let open FStar.Mul in
  forall s. Seq.length s == len ==> (
    E.be_to_n s < pow2 (8 * len) /\
    E.n_to_be len (E.be_to_n s) == s
  ))
let e_n_to_be_be_to_n_forall len =
  //Equivalent to E.n_to_be_be_to_n without the `requires` clause
  let lemma (s:E.bytes): Lemma (
    let open FStar.Mul in
    Seq.length s == len ==> (
      E.be_to_n s < pow2 (8 * len) /\
      E.n_to_be len (E.be_to_n s) == s
    )) =
      if Seq.length s = len then E.n_to_be_be_to_n len s else () in
  FStar.Classical.forall_intro lemma

//Functions missing in FStar.Endianness, copy-pasted and modified from uint32_of_be
let uint8_of_be (b: E.bytes { Seq.length b = 1 }) =
  let n = E.be_to_n b in
  E.lemma_be_to_n_is_bounded b;
  U8.uint_to_t n

let be_of_uint8 (x: U8.t): b:E.bytes{ Seq.length b = 1 } =
  E.n_to_be 1 (U8.v x)

let uint16_of_be (b: E.bytes { Seq.length b = 2 }) =
  let n = E.be_to_n b in
  E.lemma_be_to_n_is_bounded b;
  U16.uint_to_t n

let be_of_uint16 (x: U16.t): b:E.bytes{ Seq.length b = 2 } =
  E.n_to_be 2 (U16.v x)


val ps_u8: parser_serializer IT.uint8
let ps_u8 =
  e_n_to_be_be_to_n_forall 1;
  ps_uint 1 IT.uint8 U8.t (fun x -> U8.uint_to_t (IT.v x)) (fun x -> IT.u8 (U8.v x)) be_of_uint8 uint8_of_be

val ps_u16: parser_serializer IT.uint16
let ps_u16 =
  e_n_to_be_be_to_n_forall 2;
  ps_uint 2 IT.uint16 U16.t (fun x -> U16.uint_to_t (IT.v x)) (fun x -> IT.u16 (U16.v x)) be_of_uint16 uint16_of_be

val ps_u32: parser_serializer IT.uint32
let ps_u32 =
  e_n_to_be_be_to_n_forall 4;
  ps_uint 4 IT.uint32 U32.t (fun x -> U32.uint_to_t (IT.v x)) (fun x -> IT.u32 (U32.v x)) E.be_of_uint32 E.uint32_of_be

val ps_u64: parser_serializer IT.uint64
let ps_u64 =
  e_n_to_be_be_to_n_forall 8;
  ps_uint 8 IT.uint64 U64.t (fun x -> U64.uint_to_t (IT.v x)) (fun x -> IT.u64 (U64.v x)) E.be_of_uint64 E.uint64_of_be



(*** Parser for variable-length lists ***)

type bare_parser_exact (a:Type) = b:bytes -> option a
type bare_serializer_exact (a:Type) = a -> bytes
noeq type parser_serializer_exact (a:Type) = {
  parse_exact: bare_parser_exact a;
  serialize_exact: bare_serializer_exact a;
  parse_serialize_inv_exact: x:a -> Lemma (
    parse_exact (serialize_exact x) == Some x
  );
  serialize_parse_inv_exact: buf:bytes -> Lemma (
    match parse_exact buf with
    | Some x -> serialize_exact x == buf
    | None -> True
  );
}

//The two following functions are defined here because F* can't reason on recursive functions defined inside a function
private val _parse_la: #a:Type -> parser_serializer a -> buf:bytes -> Tot (option (list a)) (decreases (Seq.length buf))
private let rec _parse_la #a ps_a buf =
  if Seq.length buf = 0 then (
    Some []
  ) else (
    match ps_a.parse buf with
    | None -> None
    | Some (h, l) -> begin
      match _parse_la ps_a (delete_prefix buf l) with
      | None -> None
      | Some t -> Some (h::t)
    end
  )

private val _serialize_la: #a:Type -> parser_serializer a -> l:list a -> bytes
private let rec _serialize_la #a ps_a l =
  match l with
  | [] -> bytes_empty
  | h::t ->
    Seq.append (ps_a.serialize h) (_serialize_la ps_a t)

#push-options "--fuel 1"
val pse_list: #a:Type -> parser_serializer a -> parser_serializer_exact (list a)
let pse_list #a ps_a =
  let parse_la (buf:bytes) = _parse_la ps_a buf in
  let serialize_la (l:list a) = _serialize_la ps_a l in
  let rec parse_serialize_inv_la (l:list a): Lemma (parse_la (serialize_la l) == Some l) =
    match l with
    | [] -> ()
    | h::t ->
      ps_a.parse_no_lookahead (ps_a.serialize h) (serialize_la (h::t));
      ps_a.parse_serialize_inv h;
      parse_serialize_inv_la t;
      assert (Seq.equal (delete_prefix (serialize_la (h::t)) (Seq.length (ps_a.serialize h))) (serialize_la t))
  in
  let rec serialize_parse_inv_la (buf:bytes): Lemma (ensures (match parse_la buf with | None -> True | Some l -> serialize_la l == buf)) (decreases (Seq.length buf)) =
    if Seq.length buf = 0 then (
      assert (Seq.equal buf bytes_empty)
    ) else (
      match parse_la buf with
      | None -> ()
      | Some l ->
        let (h, len) = Some?.v (ps_a.parse buf) in
        let t = Some?.v (parse_la (delete_prefix buf len)) in
        ps_a.serialize_parse_inv buf;
        serialize_parse_inv_la (delete_prefix buf len);
        assert (Seq.equal buf (serialize_la l))
    )
  in
  {
    parse_exact = parse_la;
    serialize_exact = serialize_la;
    parse_serialize_inv_exact = parse_serialize_inv_la;
    serialize_parse_inv_exact = serialize_parse_inv_la;
  }
#pop-options


type size_range = {
  min: nat;
  max: max:nat{min <= max /\ max < pow2 64};
}

let in_range (r:size_range) (x:nat) =
  r.min <= x && x <= r.max

type nat_in_range (r:size_range) = n:nat{in_range r n}

val ps_nat_in_range: r:size_range -> parser_serializer (nat_in_range r)
let ps_nat_in_range r =
  let size_int_type =
    if r.max < pow2 8 then IT.uint8
    else if r.max < pow2 16 then IT.uint16
    else if r.max < pow2 32 then IT.uint32
    else IT.uint64
  in
  let ps_it: parser_serializer size_int_type =
    if r.max < pow2 8 then ps_u8
    else if r.max < pow2 16 then ps_u16
    else if r.max < pow2 32 then ps_u32
    else ps_u64
  in
  let nat_to_it (n:nat_in_range r): size_int_type =
    if r.max < pow2 8 then IT.u8 n
    else if r.max < pow2 16 then IT.u16 n
    else if r.max < pow2 32 then IT.u32 n
    else IT.u64 n
  in
  let it_to_nat (n:size_int_type): nat =
    if r.max < pow2 8 then IT.v #IT.U8 #IT.SEC n
    else if r.max < pow2 16 then IT.v #IT.U16 #IT.SEC n
    else if r.max < pow2 32 then IT.v #IT.U32 #IT.SEC n
    else IT.v #IT.U64 #IT.SEC n
  in
  let parse (buf:bytes): option (nat_in_range r & consumed_length buf) =
    match ps_it.parse buf with
    | None -> None
    | Some (n_it, len) ->
      let n_nat = it_to_nat n_it in
      if in_range r n_nat then
        Some (n_nat, len)
      else
        None
  in
  let serialize (n:nat_in_range r): non_empty_bytes =
    ps_it.serialize (nat_to_it n)
  in
  {
    parse = parse;
    serialize = serialize;
    parse_serialize_inv = (fun x ->
      ps_it.parse_serialize_inv (nat_to_it x)
    );
    serialize_parse_inv = (fun (buf:bytes) ->
      ps_it.serialize_parse_inv buf
    );
    parse_no_lookahead = (fun (b1 b2:bytes) ->
      match parse b1 with
      | None -> ()
      | Some _ -> ps_it.parse_no_lookahead b1 b2
    )
  }

#push-options "--z3rlimit 20"
val parser_serializer_exact_to_parser_serializer: #a:Type -> r:size_range -> pse_a:parser_serializer_exact a{forall x. in_range r (Seq.length (pse_a.serialize_exact x))} -> parser_serializer a
let parser_serializer_exact_to_parser_serializer #a r pse_a =
  let ps_nat = ps_nat_in_range r in
  let parse_a (buf:bytes) =
    match ps_nat.parse buf with
    | None -> None
    | Some (sz, l) -> begin
      let buf2 = delete_prefix buf l in
      if Seq.length buf2 < sz then (
        None
      ) else (
        match pse_a.parse_exact (Seq.slice buf2 0 sz) with
        | None -> None
        | Some x -> Some (x, ((l + sz) <: consumed_length buf))
      )
    end
  in
  let serialize_a (x_a:a): non_empty_bytes =
    let x_serialized = pse_a.serialize_exact x_a in
    Seq.append (ps_nat.serialize (Seq.length x_serialized)) x_serialized
  in
  {
    parse = parse_a;
    serialize = serialize_a;
    parse_serialize_inv = (fun x ->
      let x_serialized = pse_a.serialize_exact x in
      let x_sz = Seq.length (x_serialized) in
      let l = Seq.length (ps_nat.serialize x_sz) in
      ps_nat.parse_no_lookahead (ps_nat.serialize x_sz) (serialize_a x);
      ps_nat.parse_serialize_inv x_sz;
      pse_a.parse_serialize_inv_exact x;
      assert (Seq.equal (Seq.slice (delete_prefix (serialize_a x) l) 0 (Seq.length x_serialized)) x_serialized)
    );
    serialize_parse_inv = (fun (buf:bytes) ->
      match parse_a buf with
      | None -> ()
      | Some (x, l) ->
        let (sz, l) = Some?.v (ps_nat.parse buf) in
        ps_nat.serialize_parse_inv buf;
        pse_a.serialize_parse_inv_exact (Seq.slice (delete_prefix buf l) 0 sz);
        assert (Seq.equal (Seq.slice buf 0 (l+sz)) (serialize_a x))
    );
    parse_no_lookahead = (fun (b1 b2:bytes) ->
      match parse_a b1 with
      | None -> ()
      | Some (x, len) ->
        ps_nat.parse_no_lookahead b1 b2;
        let (sz, l) = Some?.v (ps_nat.parse b1) in
        assert (Seq.equal (Seq.slice (delete_prefix b1 l) 0 sz) (Seq.slice (delete_prefix b2 l) 0 sz))
    )
  }
#pop-options

let rec byte_length (#a:Type) (ps_a:parser_serializer a) (l:list a) : nat =
  match l with
  | [] -> 0
  | h::t -> Seq.length (ps_a.serialize h) + byte_length ps_a t

type bllist (a:Type) (ps_a:parser_serializer a) (r:size_range) = l:list a{in_range r (byte_length ps_a l)}

#push-options "--fuel 1"
val byte_length_lemma: #a:Type -> ps_a:parser_serializer a -> l:list a -> Lemma
  (byte_length ps_a l == Seq.length ((pse_list ps_a).serialize_exact l))
  [SMTPat (Seq.length ((pse_list ps_a).serialize_exact l))]
let rec byte_length_lemma #a ps_a l =
  //Why is this needed?
  assert_norm(forall x. (pse_list ps_a).serialize_exact x == _serialize_la ps_a x);
  match l with
  | [] -> ()
  | h::t -> byte_length_lemma ps_a t
#pop-options

val ps_list: #a:Type -> r:size_range -> ps_a:parser_serializer a -> parser_serializer (bllist a ps_a r)
let ps_list #a r ps_a =
  let pse_la = pse_list ps_a in
  let pse_bllist_a: parser_serializer_exact (bllist a ps_a r) =
    {
      parse_exact = (fun buf ->
        if in_range r (Seq.length buf) then
          match pse_la.parse_exact buf with
          | Some x ->
            byte_length_lemma ps_a x;
            pse_la.serialize_parse_inv_exact buf;
            Some (x <: bllist a ps_a r)
          | None -> None
        else
          None
      );
      serialize_exact = (fun x ->
        (pse_list ps_a).serialize_exact x
      );
      parse_serialize_inv_exact = (fun x ->
        pse_la.parse_serialize_inv_exact x;
        byte_length_lemma ps_a x
      );
      serialize_parse_inv_exact = (fun buf -> pse_la.serialize_parse_inv_exact buf);
    }
  in
  parser_serializer_exact_to_parser_serializer r pse_bllist_a
