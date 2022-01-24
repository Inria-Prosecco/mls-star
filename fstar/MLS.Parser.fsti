module MLS.Parser

open Lib.ByteSequence
open Lib.IntTypes

(*** Basic definitions ***)

type consumed_length (b:bytes) = n:nat{n <= Seq.length b}
type bare_parser (a:Type) = b:bytes -> option (a & consumed_length b)
type bare_serializer (a:Type) = a -> bytes

/// What is the reason behind `parser_serializer_unit` and `parser_serializer`?
/// In some functions (such as `pse_list` which is used to build `ps_seq` or `ps_bytes`),
/// it is useful to know that `parse` will never consume 0 bytes, and `serialize` will never return `bytes_empty`.
/// Such types only have one element, hence are isomorphic to `unit`. They are (anti-)recognized by the `is_not_unit` predicate.
/// Thus they depend on a `parser_serializer` which doesn't serialize/parse a unit type.
/// It is however very useful to be able to parse a unit type, in the example of an optional:
///   struct {
///       uint8 present;
///       select (present) {
///           case 0: struct{}; //<-- parsed with ps_unit!
///           case 1: T value;
///       }
///   } optional<T>;
/// In this interface, we tried to use `parser_serializer` for return types when possible,
/// and to use `parser_serializer_unit` for argument types when possible.
/// They are named `parser_serializer_unit` / `parser_serializer` and not `parser_serializer` / `parser_serializer_nonempty`
/// because `parser_serializer_nonempty` is ugly, and it's the type that is the most used by the user.

noeq type parser_serializer_unit (a:Type) = {
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

let is_not_unit (#a:Type) (ps_a:parser_serializer_unit a) = ps_a.parse bytes_empty == None
let parser_serializer (a:Type) = ps_a:parser_serializer_unit a{is_not_unit ps_a}

(*** Parser combinators ***)

val bind: #a:Type -> #b:(a -> Type) -> ps_a:parser_serializer_unit a -> ps_b:(xa:a -> parser_serializer_unit (b xa)) -> Pure (parser_serializer_unit (xa:a&(b xa)))
  (requires True)
  (ensures fun res -> is_not_unit res <==> is_not_unit ps_a \/ (forall xa. is_not_unit (ps_b xa)))
val isomorphism_explicit:
  #a:Type -> b:Type -> ps_a:parser_serializer_unit a -> f:(a -> b) -> g:(b -> a) ->
  g_f_inv:(xa:a -> Lemma (g (f xa) == xa)) -> f_g_inv:(xb:b -> Lemma (f (g xb) == xb)) ->
  Pure (parser_serializer_unit b) (requires True) (ensures fun res -> is_not_unit res <==> is_not_unit ps_a)
val isomorphism: #a:Type -> b:Type -> ps_a:parser_serializer_unit a -> f:(a -> b) -> g:(b -> a) -> Pure (parser_serializer_unit b)
  (requires (forall xa. g (f xa) == xa) /\ (forall xb. f (g xb) == xb))
  (ensures fun res -> is_not_unit res <==> is_not_unit ps_a)

(*** Parser for basic types ***)

val ps_unit: parser_serializer_unit unit

val ps_lbytes: n:size_nat{1 <= n} -> parser_serializer (lbytes n)

val ps_u8: parser_serializer uint8
val ps_u16: parser_serializer uint16
val ps_u32: parser_serializer uint32
val ps_u64: parser_serializer uint64
val ps_u128: parser_serializer uint128

(*** Exact parsers ***)

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

val ps_to_pse: #a:Type -> parser_serializer_unit a -> parser_serializer_exact a
val pse_list: #a:Type -> ps_a:parser_serializer a -> parser_serializer_exact (list a)

(*** Parser for variable-length lists ***)

type size_range = {
  min: nat;
  max: max:nat{min <= max /\ max < pow2 64};
}

let in_range (r:size_range) (x:nat) =
  r.min <= x && x <= r.max

let rec byte_length (#a:Type) (ps_a:parser_serializer a) (l:list a) : nat =
  match l with
  | [] -> 0
  | h::t -> Seq.length (ps_a.serialize h) + byte_length ps_a t

type blseq (a:Type) (ps_a:parser_serializer a) (r:size_range) = s:Seq.seq a{in_range r (byte_length ps_a (Seq.seq_to_list s))}
type blbytes (r:size_range) = b:bytes{in_range r (Seq.length b)}
val ps_seq: #a:Type -> r:size_range -> ps_a:parser_serializer a -> parser_serializer (blseq a ps_a r)
val ps_bytes: r:size_range -> parser_serializer (blbytes r)
