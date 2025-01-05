open Prims
type erange = unit
type code =
  (Vale_X64_Decls.ins, Vale_X64_Decls.ocmp) Vale_X64_Machine_s.precode
type codes =
  (Vale_X64_Decls.ins, Vale_X64_Decls.ocmp) Vale_X64_Machine_s.precode
    Prims.list
type fuel = Vale_X64_Decls.va_fuel
type ('c, 's0, 'f0, 'sN) eval =
  (unit, unit, unit, unit) Vale_X64_Decls.eval_code
type ('r, 'msg, 'p) label = Obj.t
type ('a, 'x, 'y) precedes_wrap = ('a, 'a, unit, unit) Prims.precedes
let rec (mods_contains1 :
  Vale_X64_QuickCode.mod_t Prims.list ->
    Vale_X64_QuickCode.mod_t -> Prims.bool)
  =
  fun allowed ->
    fun found ->
      match allowed with
      | [] -> Vale_X64_QuickCode.mod_eq Vale_X64_QuickCode.Mod_None found
      | h::t ->
          (Vale_X64_QuickCode.mod_eq h found) || (mods_contains1 t found)
let rec (mods_contains :
  Vale_X64_QuickCode.mod_t Prims.list ->
    Vale_X64_QuickCode.mod_t Prims.list -> Prims.bool)
  =
  fun allowed ->
    fun found ->
      match found with
      | [] -> true
      | h::t -> (mods_contains1 allowed h) && (mods_contains allowed t)
let (if_code :
  Prims.bool ->
    (Vale_X64_Decls.ins, Vale_X64_Decls.ocmp) Vale_X64_Machine_s.precode ->
      (Vale_X64_Decls.ins, Vale_X64_Decls.ocmp) Vale_X64_Machine_s.precode ->
        (Vale_X64_Decls.ins, Vale_X64_Decls.ocmp) Vale_X64_Machine_s.precode)
  = fun b -> fun c1 -> fun c2 -> if b then c1 else c2
type ('a, 'c, 'qc, 's0, 'k) wp_proc = Obj.t
type 'a wp_Seq_t = unit
type 'a wp_Bind_t = unit
type ('p, 'uuuuu, 'uuuuu1) k_AssertBy = 'p

type ('a, 'cs, 'qcs, 'mods, 'k, 's0) wp = Obj.t
type ('a, 'b, 'cs, 'qcs, 'mods, 'k) wp_Seq = Obj.t
type ('a, 'b, 'cs, 'qcs, 'mods, 'k) wp_Bind = Obj.t
type ('m, 's1, 's2) state_mod_eq = Obj.t
let (block :
  (Vale_X64_Decls.ins, Vale_X64_Decls.ocmp) Vale_X64_Machine_s.precode
    Prims.list ->
    (Vale_X64_Decls.ins, Vale_X64_Decls.ocmp) Vale_X64_Machine_s.precode)
  = fun block1 -> Vale_X64_Machine_s.Block block1
type ('a, 'cs, 'qcs, 'mods, 's0, 'k) wp_block = Obj.t
type ('a, 'c1, 'c2, 'b, 'qc1, 'qc2, 'mods, 's0, 'k) wp_InlineIf = unit
type cmp =
  | Cmp_eq of Vale_X64_Machine_s.operand64 * Vale_X64_Machine_s.operand64 
  | Cmp_ne of Vale_X64_Machine_s.operand64 * Vale_X64_Machine_s.operand64 
  | Cmp_le of Vale_X64_Machine_s.operand64 * Vale_X64_Machine_s.operand64 
  | Cmp_ge of Vale_X64_Machine_s.operand64 * Vale_X64_Machine_s.operand64 
  | Cmp_lt of Vale_X64_Machine_s.operand64 * Vale_X64_Machine_s.operand64 
  | Cmp_gt of Vale_X64_Machine_s.operand64 * Vale_X64_Machine_s.operand64 
let (uu___is_Cmp_eq : cmp -> Prims.bool) =
  fun projectee ->
    match projectee with | Cmp_eq (o1, o2) -> true | uu___ -> false
let (__proj__Cmp_eq__item__o1 : cmp -> Vale_X64_Machine_s.operand64) =
  fun projectee -> match projectee with | Cmp_eq (o1, o2) -> o1
let (__proj__Cmp_eq__item__o2 : cmp -> Vale_X64_Machine_s.operand64) =
  fun projectee -> match projectee with | Cmp_eq (o1, o2) -> o2
let (uu___is_Cmp_ne : cmp -> Prims.bool) =
  fun projectee ->
    match projectee with | Cmp_ne (o1, o2) -> true | uu___ -> false
let (__proj__Cmp_ne__item__o1 : cmp -> Vale_X64_Machine_s.operand64) =
  fun projectee -> match projectee with | Cmp_ne (o1, o2) -> o1
let (__proj__Cmp_ne__item__o2 : cmp -> Vale_X64_Machine_s.operand64) =
  fun projectee -> match projectee with | Cmp_ne (o1, o2) -> o2
let (uu___is_Cmp_le : cmp -> Prims.bool) =
  fun projectee ->
    match projectee with | Cmp_le (o1, o2) -> true | uu___ -> false
let (__proj__Cmp_le__item__o1 : cmp -> Vale_X64_Machine_s.operand64) =
  fun projectee -> match projectee with | Cmp_le (o1, o2) -> o1
let (__proj__Cmp_le__item__o2 : cmp -> Vale_X64_Machine_s.operand64) =
  fun projectee -> match projectee with | Cmp_le (o1, o2) -> o2
let (uu___is_Cmp_ge : cmp -> Prims.bool) =
  fun projectee ->
    match projectee with | Cmp_ge (o1, o2) -> true | uu___ -> false
let (__proj__Cmp_ge__item__o1 : cmp -> Vale_X64_Machine_s.operand64) =
  fun projectee -> match projectee with | Cmp_ge (o1, o2) -> o1
let (__proj__Cmp_ge__item__o2 : cmp -> Vale_X64_Machine_s.operand64) =
  fun projectee -> match projectee with | Cmp_ge (o1, o2) -> o2
let (uu___is_Cmp_lt : cmp -> Prims.bool) =
  fun projectee ->
    match projectee with | Cmp_lt (o1, o2) -> true | uu___ -> false
let (__proj__Cmp_lt__item__o1 : cmp -> Vale_X64_Machine_s.operand64) =
  fun projectee -> match projectee with | Cmp_lt (o1, o2) -> o1
let (__proj__Cmp_lt__item__o2 : cmp -> Vale_X64_Machine_s.operand64) =
  fun projectee -> match projectee with | Cmp_lt (o1, o2) -> o2
let (uu___is_Cmp_gt : cmp -> Prims.bool) =
  fun projectee ->
    match projectee with | Cmp_gt (o1, o2) -> true | uu___ -> false
let (__proj__Cmp_gt__item__o1 : cmp -> Vale_X64_Machine_s.operand64) =
  fun projectee -> match projectee with | Cmp_gt (o1, o2) -> o1
let (__proj__Cmp_gt__item__o2 : cmp -> Vale_X64_Machine_s.operand64) =
  fun projectee -> match projectee with | Cmp_gt (o1, o2) -> o2
let (cmp_to_ocmp : cmp -> Vale_X64_Decls.ocmp) =
  fun c ->
    match c with
    | Cmp_eq (o1, o2) -> Vale_X64_Decls.va_cmp_eq o1 o2
    | Cmp_ne (o1, o2) -> Vale_X64_Decls.va_cmp_ne o1 o2
    | Cmp_le (o1, o2) -> Vale_X64_Decls.va_cmp_le o1 o2
    | Cmp_ge (o1, o2) -> Vale_X64_Decls.va_cmp_ge o1 o2
    | Cmp_lt (o1, o2) -> Vale_X64_Decls.va_cmp_lt o1 o2
    | Cmp_gt (o1, o2) -> Vale_X64_Decls.va_cmp_gt o1 o2
type ('c, 's) valid_cmp = Obj.t
type ('a, 'c1, 'c2, 'b, 'qc1, 'qc2, 'mods, 's0, 'k) wp_If = unit
type ('a, 'd, 'c, 'qc, 'mods, 'inv, 'dec, 's1, 'g1, 's2, 'g2) wp_While_inv =
  unit
type ('a, 'd, 'c, 'b, 'qc, 'mods, 'inv, 'dec, 'g1, 's1, 'k) wp_While_body =
  unit
type ('a, 'd, 'c, 'b, 'qc, 'mods, 'inv, 'dec, 'g0, 's0, 'k) wp_While = unit
type 'p tAssertLemma = unit

type 'p tAssumeLemma = unit

type 'p tAssertSquashLemma = unit

type ('r0, 'r1, 'rf, 'k) regs_match_file = Obj.t
type ('r0, 'r1, 'k) regs_match = Obj.t
type ('r0, 'r1) all_regs_match = unit
type ('s0, 's1) state_match = unit
type ('s0, 's1) va_state_match = unit
type ('a, 'c, 'qc, 's0, 'k) wp_sound_code_pre = unit
type ('a, 'c, 'qc, 's0, 'k, 'uuuuu) wp_sound_code_post = Obj.t
type 'x normal = 'x