//Provides: caml_thread_initialize const
function caml_thread_initialize() {}

//Provides: caml_mutex_new const
function caml_mutex_new() {
    return 0;
}

//Provides: caml_condition_new const
function caml_condition_new() {
    return 0;
}

/* Based on https://github.com/andrenth/ocaml-stdint/blob/master/lib/stdint.ml:
 *
 * These types implemented via interop based on js_of_ocaml's implementation of
 * Int64.T:
 *   type int40 = Int64.t
 *   type int48 = Int64.t
 *   type int56 = Int64.t
 *   type int64 = Int64.t
 * These types are abstract: we can pick whatever we want.
 *   type int128, uint32, uint64, uint128
 * These types are derived:
 *   type uint40 = uint64
 *   type uint48 = uint64
 *   type uint56 = uint64
 */

////////////////////////////////////////////////////////////////////////////////

//Provides: int40_of_int
//Requires: caml_int64_of_int32
function int40_of_int(x) {
  return caml_int64_of_int32(x);
}

//Provides: int40_max_int
//Requires: caml_int64_create_lo_mi_hi, caml_int64_and
function int40_max_int() {
  var mask = caml_int64_create_lo_mi_hi(0x0000, 0xffff00, 0xffffff);
  var max = caml_int64_create_lo_mi_hi(0xffff, 0xffffff, 0xffffff);
  return caml_int64_and(mask, max);
}

//Provides: int40_min_int
//Requires: caml_int64_create_lo_mi_hi, caml_int64_and, caml_int64_add, caml_int64_of_int32
function int40_min_int() {
  var mask = caml_int64_create_lo_mi_hi(0x0000, 0xffff00, 0xffffff);
  var min = caml_int64_add(caml_int64_create_lo_mi_hi(0xffff, 0xffffff, 0xffffff),
    caml_int64_of_int32(1));
  return caml_int64_and(mask, min);
}

//Provides: int40_mul
//Requires: caml_int64_mul, caml_int64_shift_right
function int40_mul(x, y) {
  return caml_int64_mul(caml_int64_shift_right(x, 24), y);
}

//Provides: int40_div
//Requires: caml_int64_div, caml_int64_shift_left
function int40_div(x, y) {
  return caml_int64_shift_left(caml_int64_div(x, y), 24);
}

//Provides: int_of_int40
//Requires: caml_int64_shift_right, caml_int64_to_int32
function int_of_int40(x) {
  return caml_int64_to_int32(caml_int64_shift_right(x, 24));
}

////////////////////////////////////////////////////////////////////////////////

//Provides: int48_of_int
//Requires: caml_int64_of_int32
function int48_of_int(x) {
  return caml_int64_of_int32(x);
}

//Provides: int48_max_int
//Requires: caml_int64_create_lo_mi_hi, caml_int64_and
function int48_max_int() {
  var mask = caml_int64_create_lo_mi_hi(0x0000, 0xffffff, 0xffffff);
  var max = caml_int64_create_lo_mi_hi(0xffff, 0xffffff, 0xffffff);
  return caml_int64_and(mask, max);
}

//Provides: int48_min_int
//Requires: caml_int64_create_lo_mi_hi, caml_int64_and, caml_int64_add, caml_int64_of_int32
function int48_min_int() {
  var mask = caml_int64_create_lo_mi_hi(0x0000, 0xffffff, 0xffffff);
  var min = caml_int64_add(caml_int64_create_lo_mi_hi(0xffff, 0xffffff, 0xffffff),
    caml_int64_of_int32(1));
  return caml_int64_and(mask, min);
}

//Provides: int48_mul
//Requires: caml_int64_mul, caml_int64_shift_right
function int48_mul(x, y) {
  return caml_int64_mul(caml_int64_shift_right(x, 16), y);
}

//Provides: int48_div
//Requires: caml_int64_div, caml_int64_shift_left
function int48_div(x, y) {
  return caml_int64_shift_left(caml_int64_div(x, y), 16);
}

//Provides: int_of_int48
//Requires: caml_int64_shift_right, caml_int64_to_int32
function int_of_int48(x) {
  return caml_int64_to_int32(caml_int64_shift_right(x, 16));
}

////////////////////////////////////////////////////////////////////////////////

//Provides: int56_of_int
//Requires: caml_int64_of_int32
function int56_of_int(x) {
  return caml_int64_of_int32(x);
}

//Provides: int56_max_int
//Requires: caml_int64_create_lo_mi_hi, caml_int64_and
function int56_max_int() {
  var mask = caml_int64_create_lo_mi_hi(0x00ff, 0xffffff, 0xffffff);
  var max = caml_int64_create_lo_mi_hi(0xffff, 0xffffff, 0xffffff);
  return caml_int64_and(mask, max);
}

//Provides: int56_min_int
//Requires: caml_int64_create_lo_mi_hi, caml_int64_and, caml_int64_add, caml_int64_of_int32
function int56_min_int() {
  var mask = caml_int64_create_lo_mi_hi(0x00ff, 0xffffff, 0xffffff);
  var min = caml_int64_add(caml_int64_create_lo_mi_hi(0xffff, 0xffffff, 0xffffff),
    caml_int64_of_int32(1));
  return caml_int64_and(mask, min);
}

//Provides: int56_mul
//Requires: caml_int64_mul, caml_int64_shift_right
function int56_mul(x, y) {
  return caml_int64_mul(caml_int64_shift_right(x, 8), y);
}

//Provides: int56_div
//Requires: caml_int64_div, caml_int64_shift_left
function int56_div(x, y) {
  return caml_int64_shift_left(caml_int64_div(x, y), 8);
}

//Provides: int_of_int56
//Requires: caml_int64_shift_right, caml_int64_to_int32
function int_of_int56(x) {
  return caml_int64_to_int32(caml_int64_shift_right(x, 8));
}


////////////////////////////////////////////////////////////////////////////////

//Provides: int128_add
function int128_add(x, y) {
  return BigInt.asIntN(128, x + y);
}

//Provides: int128_div
function int128_div(x, y) {
  return BigInt.asIntN(128, x / y);
}

//Provides: int128_init_custom_ops
function int128_init_custom_ops() {
}

//Provides: int128_max_int
function int128_max_int() {
  // return 2n**127n-1n;
  return BigInt("170141183460469231731687303715884105727");
}

//Provides: int128_min_int
function int128_min_int() {
  // return ~(2n**127n-1n);
  return BigInt("-170141183460469231731687303715884105728");
}

//Provides: int128_mod
function int128_mod(x, y) {
  return BigInt.asIntN(128, x % y);
}

//Provides: int128_mul
function int128_mul(x, y) {
  return BigInt.asIntN(128, x * y);
}

//Provides: int128_of_int
function int128_of_int(x) {
  return BigInt(x);
}

//Provides: int128_sub
function int128_sub(x, y) {
  return BigInt.asIntN(128, x - y);
}

//Provides: int_of_int128
function int_of_int128(x) {
  return Number(BigInt.asIntN(32));
}

////////////////////////////////////////////////////////////////////////////////

//Provides: uint32_add
function uint32_add(x, y) {
  return BigInt.asUintN(32, x + y);
}

//Provides: uint32_div
function uint32_div(x, y) {
  return BigInt.asUintN(32, x / y);
}

//Provides: uint32_init_custom_ops
function uint32_init_custom_ops() {
}

//Provides: uint32_max_int
function uint32_max_int() {
  return BigInt("0xffffffff");
}

//Provides: uint32_mod
function uint32_mod(x, y) {
  return BigInt.asUintN(32, x % y);
}

//Provides: uint32_mul
function uint32_mul(x, y) {
  return BigInt.asUintN(32, x * y);
}

//Provides: uint32_of_int
function uint32_of_int(x) {
  return BigInt(x);
}

//Provides: uint32_sub
function uint32_sub(x, y) {
  return BigInt.asUintN(32, x - y);
}

//Provides: int_of_uint32
function int_of_uint32(x) {
  return Number(BigInt.asUintN(32));
}

//Provides: uint32_and
function uint32_and(x, y) {
  return BigInt.asUintN(32, x & y);
}

//Provides: uint32_or
function uint32_or(x, y) {
  return BigInt.asUintN(32, x | y);
}

//Provides: uint32_shift_left
function uint32_shift_left(x, y) {
  return BigInt.asUintN(32, x << y);
}

//Provides: uint32_shift_right
function uint32_shift_right(x, y) {
  return BigInt.asUintN(32, x >> y);
}

//Provides: uint32_xor
function uint32_xor(x, y) {
  return BigInt.asUintN(32, x ^ y);
}


////////////////////////////////////////////////////////////////////////////////

//Provides: uint40_add
function uint40_add(x, y) {
  return BigInt.asUintN(40, x + y);
}

//Provides: uint40_div
function uint40_div(x, y) {
  return BigInt.asUintN(40, x / y);
}

//Provides: uint40_init_custom_ops
function uint40_init_custom_ops() {
}

//Provides: uint40_max_int
function uint40_max_int() {
  return BigInt("0xffffffffff");
}

//Provides: uint40_mod
function uint40_mod(x, y) {
  return BigInt.asUintN(40, x % y);
}

//Provides: uint40_mul
function uint40_mul(x, y) {
  return BigInt.asUintN(40, x * y);
}

//Provides: uint40_of_int
function uint40_of_int(x) {
  return BigInt(x);
}

//Provides: uint40_sub
function uint40_sub(x, y) {
  return BigInt.asUintN(40, x - y);
}

//Provides: int_of_uint40
function int_of_uint40(x) {
  return Number(BigInt.asUintN(40));
}

////////////////////////////////////////////////////////////////////////////////

//Provides: uint48_add
function uint48_add(x, y) {
  return BigInt.asUintN(48, x + y);
}

//Provides: uint48_div
function uint48_div(x, y) {
  return BigInt.asUintN(48, x / y);
}

//Provides: uint48_init_custom_ops
function uint48_init_custom_ops() {
}

//Provides: uint48_max_int
function uint48_max_int() {
  return BigInt("0xffffffffffff");
}

//Provides: uint48_mod
function uint48_mod(x, y) {
  return BigInt.asUintN(48, x % y);
}

//Provides: uint48_mul
function uint48_mul(x, y) {
  return BigInt.asUintN(48, x * y);
}

//Provides: uint48_of_int
function uint48_of_int(x) {
  return BigInt(x);
}

//Provides: uint48_sub
function uint48_sub(x, y) {
  return BigInt.asUintN(48, x - y);
}

//Provides: int_of_uint48
function int_of_uint48(x) {
  return Number(BigInt.asUintN(48));
}

////////////////////////////////////////////////////////////////////////////////

//Provides: uint56_add
function uint56_add(x, y) {
  return BigInt.asUintN(56, x + y);
}

//Provides: uint56_div
function uint56_div(x, y) {
  return BigInt.asUintN(56, x / y);
}

//Provides: uint56_init_custom_ops
function uint56_init_custom_ops() {
}

//Provides: uint56_max_int
function uint56_max_int() {
  return BigInt("0xffffffffffffff");
}

//Provides: uint56_mod
function uint56_mod(x, y) {
  return BigInt.asUintN(56, x % y);
}

//Provides: uint56_mul
function uint56_mul(x, y) {
  return BigInt.asUintN(56, x * y);
}

//Provides: uint56_of_int
function uint56_of_int(x) {
  return BigInt(x);
}

//Provides: uint56_sub
function uint56_sub(x, y) {
  return BigInt.asUintN(56, x - y);
}

//Provides: int_of_uint56
function int_of_uint56(x) {
  return Number(BigInt.asUintN(56));
}

////////////////////////////////////////////////////////////////////////////////

//Provides: uint64_add
function uint64_add(x, y) {
  return BigInt.asUintN(64, x + y);
}

//Provides: uint64_div
function uint64_div(x, y) {
  return BigInt.asUintN(64, x / y);
}

//Provides: uint64_init_custom_ops
function uint64_init_custom_ops() {
}

//Provides: uint64_max_int
function uint64_max_int() {
  return BigInt("0xffffffffffffffff");
}

//Provides: uint64_mod
function uint64_mod(x, y) {
  return BigInt.asUintN(64, x % y);
}

//Provides: uint64_mul
function uint64_mul(x, y) {
  return BigInt.asUintN(64, x * y);
}

//Provides: uint64_of_int
function uint64_of_int(x) {
  return BigInt(x);
}

//Provides: uint64_sub
function uint64_sub(x, y) {
  return BigInt.asUintN(64, x - y);
}

//Provides: int_of_uint64
function int_of_uint64(x) {
  return Number(BigInt.asUintN(64));
}

//Provides: uint64_and
function uint64_and(x, y) {
  return BigInt.asUintN(64, x & y);
}

//Provides: uint64_or
function uint64_or(x, y) {
  return BigInt.asUintN(64, x | y);
}

//Provides: uint64_shift_left
function uint64_shift_left(x, y) {
  return BigInt.asUintN(64, x << y);
}

//Provides: uint64_shift_right
function uint64_shift_right(x, y) {
  return BigInt.asUintN(64, x >> y);
}

//Provides: uint64_xor
function uint64_xor(x, y) {
  return BigInt.asUintN(64, x ^ y);
}

////////////////////////////////////////////////////////////////////////////////

//Provides: uint128_add
function uint128_add(x, y) {
  return BigInt.asUintN(128, x + y);
}

//Provides: uint128_div
function uint128_div(x, y) {
  return BigInt.asUintN(128, x / y);
}

//Provides: uint128_init_custom_ops
function uint128_init_custom_ops() {
}

//Provides: uint128_max_int
function uint128_max_int() {
  return BigInt("0xffffffffffffffffffffffffffffffff");
}

//Provides: uint128_mod
function uint128_mod(x, y) {
  return BigInt.asUintN(128, x % y);
}

//Provides: uint128_mul
function uint128_mul(x, y) {
  return BigInt.asUintN(128, x * y);
}

//Provides: uint128_of_int
function uint128_of_int(x) {
  return BigInt(x);
}

//Provides: uint128_sub
function uint128_sub(x, y) {
  return BigInt.asUintN(128, x - y);
}

//Provides: int_of_uint128
function int_of_uint128(x) {
  return Number(BigInt.asUintN(128));
}
