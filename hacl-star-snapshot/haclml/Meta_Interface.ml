open Fstar_pluginlib
open Prims
let assoc :
  'a 'b .
    'a -> ('a * 'b) Prims.list -> ('b, unit) FStar_Tactics_Effect.tac_repr
  =
  fun uu___1 ->
    fun uu___ ->
      (fun x ->
         fun l ->
           match FStar_List_Tot_Base.assoc x l with
           | FStar_Pervasives_Native.Some x1 ->
               Obj.magic
                 (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> x1))
           | FStar_Pervasives_Native.None ->
               Obj.magic (FStar_Tactics_V1_Derived.fail "failure: assoc"))
        uu___1 uu___
let rec zip :
  'a 'b .
    'a Prims.list ->
      'b Prims.list ->
        (('a * 'b) Prims.list, unit) FStar_Tactics_Effect.tac_repr
  =
  fun uu___1 ->
    fun uu___ ->
      (fun xs ->
         fun ys ->
           match (xs, ys) with
           | (x::xs1, y::ys1) ->
               Obj.magic
                 (Obj.repr
                    (let uu___ = zip xs1 ys1 in
                     FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Meta.Interface.fst"
                                (Prims.of_int (17)) (Prims.of_int (34))
                                (Prims.of_int (17)) (Prims.of_int (43)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Meta.Interface.fst"
                                (Prims.of_int (17)) (Prims.of_int (24))
                                (Prims.of_int (17)) (Prims.of_int (43)))))
                       (Obj.magic uu___)
                       (fun uu___1 ->
                          FStar_Tactics_Effect.lift_div_tac
                            (fun uu___2 -> (x, y) :: uu___1))))
           | ([], []) ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> [])))
           | uu___ ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_V1_Derived.fail "invalid argument: zip")))
        uu___1 uu___
type mapping =
  | Inline of Fstarcompiler.FStarC_Reflection_Types.name 
  | Specialize 
let (uu___is_Inline : mapping -> Prims.bool) =
  fun projectee ->
    match projectee with | Inline new_name -> true | uu___ -> false
let (__proj__Inline__item__new_name :
  mapping -> Fstarcompiler.FStarC_Reflection_Types.name) =
  fun projectee -> match projectee with | Inline new_name -> new_name
let (uu___is_Specialize : mapping -> Prims.bool) =
  fun projectee -> match projectee with | Specialize -> true | uu___ -> false
type state =
  {
  seen:
    (Fstarcompiler.FStarC_Reflection_Types.name * (Prims.bool *
      Fstarcompiler.FStarC_Reflection_Types.term * mapping *
      Fstarcompiler.FStarC_Reflection_Types.name Prims.list)) Prims.list
    ;
  indent: Prims.string }
let (__proj__Mkstate__item__seen :
  state ->
    (Fstarcompiler.FStarC_Reflection_Types.name * (Prims.bool *
      Fstarcompiler.FStarC_Reflection_Types.term * mapping *
      Fstarcompiler.FStarC_Reflection_Types.name Prims.list)) Prims.list)
  = fun projectee -> match projectee with | { seen; indent;_} -> seen
let (__proj__Mkstate__item__indent : state -> Prims.string) =
  fun projectee -> match projectee with | { seen; indent;_} -> indent
let (string_of_mapping : mapping -> Prims.string) =
  fun uu___ ->
    match uu___ with | Inline uu___1 -> "inline" | Specialize -> "specialize"
let rec (string_of_name :
  Fstarcompiler.FStarC_Reflection_Types.name ->
    (Prims.string, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___ ->
    (fun n ->
       match n with
       | n1::[] ->
           Obj.magic
             (Obj.repr (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> n1)))
       | n1::ns ->
           Obj.magic
             (Obj.repr
                (let uu___ =
                   let uu___1 = string_of_name ns in
                   FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Meta.Interface.fst"
                              (Prims.of_int (80)) (Prims.of_int (25))
                              (Prims.of_int (80)) (Prims.of_int (42)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Prims.fst"
                              (Prims.of_int (611)) (Prims.of_int (19))
                              (Prims.of_int (611)) (Prims.of_int (31)))))
                     (Obj.magic uu___1)
                     (fun uu___2 ->
                        FStar_Tactics_Effect.lift_div_tac
                          (fun uu___3 -> Prims.strcat "_" uu___2)) in
                 FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Meta.Interface.fst"
                            (Prims.of_int (80)) (Prims.of_int (19))
                            (Prims.of_int (80)) (Prims.of_int (42)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Prims.fst"
                            (Prims.of_int (611)) (Prims.of_int (19))
                            (Prims.of_int (611)) (Prims.of_int (31)))))
                   (Obj.magic uu___)
                   (fun uu___1 ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___2 -> Prims.strcat n1 uu___1))))
       | [] ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_V1_Derived.fail "impossible: empty name")))
      uu___
let rec (suffix_name :
  Fstarcompiler.FStarC_Reflection_Types.name ->
    Prims.string ->
      (Fstarcompiler.FStarC_Reflection_Types.name, unit)
        FStar_Tactics_Effect.tac_repr)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun n ->
         fun s ->
           match n with
           | m::n1::[] ->
               Obj.magic
                 (Obj.repr
                    (let uu___ = FStar_Tactics_V1_Derived.cur_module () in
                     FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Meta.Interface.fst"
                                (Prims.of_int (85)) (Prims.of_int (16))
                                (Prims.of_int (85)) (Prims.of_int (29)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Meta.Interface.fst"
                                (Prims.of_int (85)) (Prims.of_int (16))
                                (Prims.of_int (85)) (Prims.of_int (68)))))
                       (Obj.magic uu___)
                       (fun uu___1 ->
                          FStar_Tactics_Effect.lift_div_tac
                            (fun uu___2 ->
                               FStar_List_Tot_Base.op_At uu___1
                                 [Prims.strcat (FStar_String.lowercase m)
                                    (Prims.strcat "_" (Prims.strcat n1 s))]))))
           | n1::ns -> Obj.magic (Obj.repr (suffix_name ns s))
           | uu___::[] ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_V1_Derived.fail "impossible: empty name"))
           | [] ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_V1_Derived.fail "impossible: empty name")))
        uu___1 uu___
let (has_attr :
  Fstarcompiler.FStarC_Reflection_Types.sigelt ->
    Fstarcompiler.FStarC_Reflection_Types.term -> Prims.bool)
  =
  fun s ->
    fun x ->
      FStar_List_Tot_Base.existsb
        (fun t -> Fstarcompiler.FStarC_Reflection_V1_Builtins.term_eq t x)
        (Fstarcompiler.FStarC_Reflection_V1_Builtins.sigelt_attrs s)
let (has_inline_for_extraction :
  Fstarcompiler.FStarC_Reflection_Types.sigelt -> Prims.bool) =
  fun s ->
    FStar_List_Tot_Base.existsb
      (fun uu___ ->
         match uu___ with
         | Fstarcompiler.FStarC_Reflection_V1_Data.Inline_for_extraction ->
             true
         | uu___1 -> false)
      (Fstarcompiler.FStarC_Reflection_V1_Builtins.sigelt_quals s)
let (is_implicit :
  Fstarcompiler.FStarC_Reflection_V1_Data.aqualv -> Prims.bool) =
  fun uu___ ->
    match uu___ with
    | Fstarcompiler.FStarC_Reflection_V1_Data.Q_Implicit -> true
    | uu___1 -> false
let rec (push_pre :
  state ->
    Fstarcompiler.FStarC_Reflection_Types.bv ->
      Fstarcompiler.FStarC_Reflection_Types.term ->
        (Fstarcompiler.FStarC_Reflection_Types.term, unit)
          FStar_Tactics_Effect.tac_repr)
  =
  fun st ->
    fun inv_bv ->
      fun t ->
        let uu___ = FStarC_Tactics_V1_Builtins.inspect t in
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Meta.Interface.fst"
                   (Prims.of_int (101)) (Prims.of_int (8))
                   (Prims.of_int (101)) (Prims.of_int (17)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Meta.Interface.fst"
                   (Prims.of_int (101)) (Prims.of_int (2))
                   (Prims.of_int (134)) (Prims.of_int (7)))))
          (Obj.magic uu___)
          (fun uu___1 ->
             (fun uu___1 ->
                match uu___1 with
                | Fstarcompiler.FStarC_Reflection_V1_Data.Tv_Arrow (bv, c) ->
                    let uu___2 =
                      match Fstarcompiler.FStarC_Reflection_V1_Builtins.inspect_comp
                              c
                      with
                      | Fstarcompiler.FStarC_Reflection_V1_Data.C_Eff
                          (us, e, a, args, decrs) ->
                          let uu___3 =
                            let uu___4 = string_of_name e in
                            FStar_Tactics_Effect.tac_bind
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Meta.Interface.fst"
                                       (Prims.of_int (106))
                                       (Prims.of_int (15))
                                       (Prims.of_int (106))
                                       (Prims.of_int (31)))))
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Meta.Interface.fst"
                                       (Prims.of_int (106))
                                       (Prims.of_int (15))
                                       (Prims.of_int (106))
                                       (Prims.of_int (61)))))
                              (Obj.magic uu___4)
                              (fun uu___5 ->
                                 FStar_Tactics_Effect.lift_div_tac
                                   (fun uu___6 ->
                                      uu___5 = "FStar_HyperStack_ST_Stack")) in
                          FStar_Tactics_Effect.tac_bind
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range "Meta.Interface.fst"
                                     (Prims.of_int (106)) (Prims.of_int (15))
                                     (Prims.of_int (106)) (Prims.of_int (61)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range "Meta.Interface.fst"
                                     (Prims.of_int (106)) (Prims.of_int (12))
                                     (Prims.of_int (124)) (Prims.of_int (84)))))
                            (Obj.magic uu___3)
                            (fun uu___4 ->
                               (fun uu___4 ->
                                  if uu___4
                                  then
                                    let uu___5 =
                                      match args with
                                      | (pre, qual)::rest ->
                                          let uu___6 =
                                            let uu___7 =
                                              FStarC_Tactics_V1_Builtins.inspect
                                                pre in
                                            FStar_Tactics_Effect.tac_bind
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "Meta.Interface.fst"
                                                       (Prims.of_int (111))
                                                       (Prims.of_int (28))
                                                       (Prims.of_int (111))
                                                       (Prims.of_int (39)))))
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "Meta.Interface.fst"
                                                       (Prims.of_int (111))
                                                       (Prims.of_int (22))
                                                       (Prims.of_int (116))
                                                       (Prims.of_int (75)))))
                                              (Obj.magic uu___7)
                                              (fun uu___8 ->
                                                 (fun uu___8 ->
                                                    match uu___8 with
                                                    | Fstarcompiler.FStarC_Reflection_V1_Data.Tv_Abs
                                                        (h, body) ->
                                                        Obj.magic
                                                          (Obj.repr
                                                             (let uu___9 =
                                                                let uu___10 =
                                                                  let uu___11
                                                                    =
                                                                    let uu___12
                                                                    =
                                                                    FStarC_Tactics_V1_Builtins.pack
                                                                    (Fstarcompiler.FStarC_Reflection_V1_Data.Tv_Var
                                                                    inv_bv) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (113))
                                                                    (Prims.of_int (56))
                                                                    (Prims.of_int (113))
                                                                    (Prims.of_int (76)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (113))
                                                                    (Prims.of_int (56))
                                                                    (Prims.of_int (113))
                                                                    (Prims.of_int (88)))))
                                                                    (Obj.magic
                                                                    uu___12)
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    (uu___13,
                                                                    Fstarcompiler.FStarC_Reflection_V1_Data.Q_Explicit))) in
                                                                  FStar_Tactics_Effect.tac_bind
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (113))
                                                                    (Prims.of_int (56))
                                                                    (Prims.of_int (113))
                                                                    (Prims.of_int (88)))))
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (113))
                                                                    (Prims.of_int (54))
                                                                    (Prims.of_int (113))
                                                                    (Prims.of_int (108)))))
                                                                    (
                                                                    Obj.magic
                                                                    uu___11)
                                                                    (
                                                                    fun
                                                                    uu___12
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    [uu___12;
                                                                    (body,
                                                                    Fstarcompiler.FStarC_Reflection_V1_Data.Q_Explicit)])) in
                                                                FStar_Tactics_Effect.tac_bind
                                                                  (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (113))
                                                                    (Prims.of_int (54))
                                                                    (Prims.of_int (113))
                                                                    (Prims.of_int (108)))))
                                                                  (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (113))
                                                                    (Prims.of_int (37))
                                                                    (Prims.of_int (113))
                                                                    (Prims.of_int (108)))))
                                                                  (Obj.magic
                                                                    uu___10)
                                                                  (fun
                                                                    uu___11
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    FStar_Reflection_V1_Derived.mk_app
                                                                    (Fstarcompiler.FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (Fstarcompiler.FStarC_Reflection_V2_Data.Tv_FVar
                                                                    (Fstarcompiler.FStarC_Reflection_V2_Builtins.pack_fv
                                                                    ["Prims";
                                                                    "l_and"])))
                                                                    uu___11)) in
                                                              FStar_Tactics_Effect.tac_bind
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (113))
                                                                    (Prims.of_int (37))
                                                                    (Prims.of_int (113))
                                                                    (Prims.of_int (108)))))
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (114))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (114))
                                                                    (Prims.of_int (46)))))
                                                                (Obj.magic
                                                                   uu___9)
                                                                (fun uu___10
                                                                   ->
                                                                   (fun body1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStarC_Tactics_V1_Builtins.pack
                                                                    (Fstarcompiler.FStarC_Reflection_V1_Data.Tv_Abs
                                                                    (h,
                                                                    body1))))
                                                                    uu___10)))
                                                    | uu___9 ->
                                                        Obj.magic
                                                          (Obj.repr
                                                             (FStar_Tactics_V1_Derived.fail
                                                                "impossible: argument to ST.Stack not a fun")))
                                                   uu___8) in
                                          FStar_Tactics_Effect.tac_bind
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Meta.Interface.fst"
                                                     (Prims.of_int (111))
                                                     (Prims.of_int (22))
                                                     (Prims.of_int (116))
                                                     (Prims.of_int (75)))))
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Meta.Interface.fst"
                                                     (Prims.of_int (118))
                                                     (Prims.of_int (20))
                                                     (Prims.of_int (118))
                                                     (Prims.of_int (39)))))
                                            (Obj.magic uu___6)
                                            (fun pre1 ->
                                               FStar_Tactics_Effect.lift_div_tac
                                                 (fun uu___7 -> (pre1, qual)
                                                    :: rest))
                                      | uu___6 ->
                                          let uu___7 =
                                            let uu___8 = string_of_name e in
                                            FStar_Tactics_Effect.tac_bind
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "Meta.Interface.fst"
                                                       (Prims.of_int (120))
                                                       (Prims.of_int (68))
                                                       (Prims.of_int (120))
                                                       (Prims.of_int (84)))))
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "Prims.fst"
                                                       (Prims.of_int (611))
                                                       (Prims.of_int (19))
                                                       (Prims.of_int (611))
                                                       (Prims.of_int (31)))))
                                              (Obj.magic uu___8)
                                              (fun uu___9 ->
                                                 FStar_Tactics_Effect.lift_div_tac
                                                   (fun uu___10 ->
                                                      Prims.strcat
                                                        "impossible: effect not fully applied "
                                                        uu___9)) in
                                          FStar_Tactics_Effect.tac_bind
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Meta.Interface.fst"
                                                     (Prims.of_int (120))
                                                     (Prims.of_int (25))
                                                     (Prims.of_int (120))
                                                     (Prims.of_int (85)))))
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Meta.Interface.fst"
                                                     (Prims.of_int (120))
                                                     (Prims.of_int (20))
                                                     (Prims.of_int (120))
                                                     (Prims.of_int (85)))))
                                            (Obj.magic uu___7)
                                            (fun uu___8 ->
                                               FStar_Tactics_V1_Derived.fail
                                                 uu___8) in
                                    Obj.magic
                                      (FStar_Tactics_Effect.tac_bind
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "Meta.Interface.fst"
                                                  (Prims.of_int (108))
                                                  (Prims.of_int (16))
                                                  (Prims.of_int (120))
                                                  (Prims.of_int (85)))))
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "Meta.Interface.fst"
                                                  (Prims.of_int (122))
                                                  (Prims.of_int (14))
                                                  (Prims.of_int (122))
                                                  (Prims.of_int (37)))))
                                         (Obj.magic uu___5)
                                         (fun args1 ->
                                            FStar_Tactics_Effect.lift_div_tac
                                              (fun uu___6 ->
                                                 Fstarcompiler.FStarC_Reflection_V1_Data.C_Eff
                                                   (us, e, a, args1, decrs))))
                                  else
                                    (let uu___6 =
                                       let uu___7 = string_of_name e in
                                       FStar_Tactics_Effect.tac_bind
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "Meta.Interface.fst"
                                                  (Prims.of_int (124))
                                                  (Prims.of_int (67))
                                                  (Prims.of_int (124))
                                                  (Prims.of_int (83)))))
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "Prims.fst"
                                                  (Prims.of_int (611))
                                                  (Prims.of_int (19))
                                                  (Prims.of_int (611))
                                                  (Prims.of_int (31)))))
                                         (Obj.magic uu___7)
                                         (fun uu___8 ->
                                            FStar_Tactics_Effect.lift_div_tac
                                              (fun uu___9 ->
                                                 Prims.strcat
                                                   "rewritten function has an unknown effect: "
                                                   uu___8)) in
                                     Obj.magic
                                       (FStar_Tactics_Effect.tac_bind
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Meta.Interface.fst"
                                                   (Prims.of_int (124))
                                                   (Prims.of_int (19))
                                                   (Prims.of_int (124))
                                                   (Prims.of_int (84)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Meta.Interface.fst"
                                                   (Prims.of_int (124))
                                                   (Prims.of_int (14))
                                                   (Prims.of_int (124))
                                                   (Prims.of_int (84)))))
                                          (Obj.magic uu___6)
                                          (fun uu___7 ->
                                             FStar_Tactics_V1_Derived.fail
                                               uu___7)))) uu___4)
                      | Fstarcompiler.FStarC_Reflection_V1_Data.C_Total t1 ->
                          let uu___3 = push_pre st inv_bv t1 in
                          FStar_Tactics_Effect.tac_bind
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range "Meta.Interface.fst"
                                     (Prims.of_int (126)) (Prims.of_int (20))
                                     (Prims.of_int (126)) (Prims.of_int (42)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range "Meta.Interface.fst"
                                     (Prims.of_int (126)) (Prims.of_int (12))
                                     (Prims.of_int (126)) (Prims.of_int (42)))))
                            (Obj.magic uu___3)
                            (fun uu___4 ->
                               FStar_Tactics_Effect.lift_div_tac
                                 (fun uu___5 ->
                                    Fstarcompiler.FStarC_Reflection_V1_Data.C_Total
                                      uu___4))
                      | uu___3 ->
                          let uu___4 =
                            let uu___5 =
                              FStarC_Tactics_V1_Builtins.term_to_string t in
                            FStar_Tactics_Effect.tac_bind
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Meta.Interface.fst"
                                       (Prims.of_int (128))
                                       (Prims.of_int (76))
                                       (Prims.of_int (128))
                                       (Prims.of_int (92)))))
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range "Prims.fst"
                                       (Prims.of_int (611))
                                       (Prims.of_int (19))
                                       (Prims.of_int (611))
                                       (Prims.of_int (31)))))
                              (Obj.magic uu___5)
                              (fun uu___6 ->
                                 FStar_Tactics_Effect.lift_div_tac
                                   (fun uu___7 ->
                                      Prims.strcat
                                        "rewritten type is neither a Tot or a stateful arrow: "
                                        uu___6)) in
                          FStar_Tactics_Effect.tac_bind
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range "Meta.Interface.fst"
                                     (Prims.of_int (128)) (Prims.of_int (17))
                                     (Prims.of_int (128)) (Prims.of_int (93)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range "Meta.Interface.fst"
                                     (Prims.of_int (128)) (Prims.of_int (12))
                                     (Prims.of_int (128)) (Prims.of_int (93)))))
                            (Obj.magic uu___4)
                            (fun uu___5 ->
                               FStar_Tactics_V1_Derived.fail uu___5) in
                    Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range "Meta.Interface.fst"
                                  (Prims.of_int (104)) (Prims.of_int (8))
                                  (Prims.of_int (128)) (Prims.of_int (93)))))
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range "Meta.Interface.fst"
                                  (Prims.of_int (129)) (Prims.of_int (8))
                                  (Prims.of_int (131)) (Prims.of_int (26)))))
                         (Obj.magic uu___2)
                         (fun uu___3 ->
                            (fun c1 ->
                               let uu___3 =
                                 Obj.magic
                                   (FStar_Tactics_Effect.lift_div_tac
                                      (fun uu___4 ->
                                         Fstarcompiler.FStarC_Reflection_V1_Builtins.pack_comp
                                           c1)) in
                               Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "Meta.Interface.fst"
                                             (Prims.of_int (130))
                                             (Prims.of_int (14))
                                             (Prims.of_int (130))
                                             (Prims.of_int (25)))))
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "Meta.Interface.fst"
                                             (Prims.of_int (131))
                                             (Prims.of_int (6))
                                             (Prims.of_int (131))
                                             (Prims.of_int (26)))))
                                    (Obj.magic uu___3)
                                    (fun uu___4 ->
                                       (fun c2 ->
                                          Obj.magic
                                            (FStarC_Tactics_V1_Builtins.pack
                                               (Fstarcompiler.FStarC_Reflection_V1_Data.Tv_Arrow
                                                  (bv, c2)))) uu___4)))
                              uu___3))
                | uu___2 ->
                    let uu___3 =
                      FStarC_Tactics_V1_Builtins.print
                        (Prims.strcat st.indent
                           "  WARN: no effect found, are you using the specialize tactic on pure code?") in
                    Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range "Meta.Interface.fst"
                                  (Prims.of_int (133)) (Prims.of_int (6))
                                  (Prims.of_int (133)) (Prims.of_int (102)))))
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range "Meta.Interface.fst"
                                  (Prims.of_int (100)) (Prims.of_int (43))
                                  (Prims.of_int (100)) (Prims.of_int (44)))))
                         (Obj.magic uu___3)
                         (fun uu___4 ->
                            FStar_Tactics_Effect.lift_div_tac
                              (fun uu___5 -> t)))) uu___1)
let rec (to_reduce :
  Fstarcompiler.FStarC_Reflection_Types.term ->
    (Prims.string Prims.list, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    let uu___ =
      let uu___1 =
        let uu___2 = FStar_Tactics_V1_SyntaxHelpers.collect_app t in
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Meta.Interface.fst"
                   (Prims.of_int (137)) (Prims.of_int (12))
                   (Prims.of_int (137)) (Prims.of_int (27)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Meta.Interface.fst"
                   (Prims.of_int (137)) (Prims.of_int (8))
                   (Prims.of_int (137)) (Prims.of_int (27)))))
          (Obj.magic uu___2)
          (fun uu___3 ->
             FStar_Tactics_Effect.lift_div_tac
               (fun uu___4 -> FStar_Pervasives_Native.fst uu___3)) in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Meta.Interface.fst" (Prims.of_int (137))
                 (Prims.of_int (8)) (Prims.of_int (137)) (Prims.of_int (27)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Meta.Interface.fst" (Prims.of_int (137))
                 (Prims.of_int (8)) (Prims.of_int (137)) (Prims.of_int (27)))))
        (Obj.magic uu___1)
        (fun uu___2 ->
           (fun uu___2 ->
              Obj.magic (FStarC_Tactics_V1_Builtins.inspect uu___2)) uu___2) in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Meta.Interface.fst" (Prims.of_int (137))
               (Prims.of_int (8)) (Prims.of_int (137)) (Prims.of_int (27)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Meta.Interface.fst" (Prims.of_int (137))
               (Prims.of_int (2)) (Prims.of_int (148)) (Prims.of_int (8)))))
      (Obj.magic uu___)
      (fun uu___1 ->
         (fun uu___1 ->
            match uu___1 with
            | Fstarcompiler.FStarC_Reflection_V1_Data.Tv_UInst (fv, uu___2)
                ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.lift_div_tac
                        (fun uu___3 ->
                           [FStar_Reflection_V1_Derived.fv_to_string fv])))
            | Fstarcompiler.FStarC_Reflection_V1_Data.Tv_FVar fv ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.lift_div_tac
                        (fun uu___2 ->
                           [FStar_Reflection_V1_Derived.fv_to_string fv])))
            | Fstarcompiler.FStarC_Reflection_V1_Data.Tv_Arrow (bv, c) ->
                Obj.magic
                  (Obj.repr
                     (match Fstarcompiler.FStarC_Reflection_V1_Builtins.inspect_comp
                              c
                      with
                      | Fstarcompiler.FStarC_Reflection_V1_Data.C_Total t1 ->
                          Obj.repr (to_reduce t1)
                      | uu___2 ->
                          Obj.repr
                            (FStar_Tactics_Effect.lift_div_tac
                               (fun uu___3 -> []))))
            | uu___2 ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.lift_div_tac (fun uu___3 -> []))))
           uu___1)
let (lambda_over_p :
  Fstarcompiler.FStarC_Reflection_Types.bv ->
    Fstarcompiler.FStarC_Reflection_Types.typ ->
      Fstarcompiler.FStarC_Reflection_Types.term ->
        (Fstarcompiler.FStarC_Reflection_Types.term, unit)
          FStar_Tactics_Effect.tac_repr)
  =
  fun inv_bv ->
    fun sort ->
      fun t ->
        FStarC_Tactics_V1_Builtins.pack
          (Fstarcompiler.FStarC_Reflection_V1_Data.Tv_Abs
             ((FStar_Reflection_V1_Derived.mk_binder inv_bv sort), t))
let (lambda_over_only_p :
  state ->
    Fstarcompiler.FStarC_Reflection_Types.bv ->
      Fstarcompiler.FStarC_Reflection_Types.typ ->
        Fstarcompiler.FStarC_Reflection_Types.term ->
          (Fstarcompiler.FStarC_Reflection_Types.term, unit)
            FStar_Tactics_Effect.tac_repr)
  =
  fun st ->
    fun inv_bv ->
      fun sort ->
        fun f_typ ->
          let uu___ = to_reduce f_typ in
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Meta.Interface.fst"
                     (Prims.of_int (154)) (Prims.of_int (12))
                     (Prims.of_int (154)) (Prims.of_int (27)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Meta.Interface.fst"
                     (Prims.of_int (155)) (Prims.of_int (2))
                     (Prims.of_int (157)) (Prims.of_int (54)))))
            (Obj.magic uu___)
            (fun uu___1 ->
               (fun fvs ->
                  let uu___1 =
                    let uu___2 =
                      let uu___3 =
                        let uu___4 =
                          FStarC_Tactics_V1_Builtins.term_to_string f_typ in
                        FStar_Tactics_Effect.tac_bind
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range "Meta.Interface.fst"
                                   (Prims.of_int (155)) (Prims.of_int (35))
                                   (Prims.of_int (155)) (Prims.of_int (55)))))
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range "Prims.fst"
                                   (Prims.of_int (611)) (Prims.of_int (19))
                                   (Prims.of_int (611)) (Prims.of_int (31)))))
                          (Obj.magic uu___4)
                          (fun uu___5 ->
                             FStar_Tactics_Effect.lift_div_tac
                               (fun uu___6 ->
                                  Prims.strcat uu___5
                                    (Prims.strcat ": "
                                       (FStar_String.concat ", " fvs)))) in
                      FStar_Tactics_Effect.tac_bind
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range "Meta.Interface.fst"
                                 (Prims.of_int (155)) (Prims.of_int (35))
                                 (Prims.of_int (155)) (Prims.of_int (87)))))
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range "Prims.fst"
                                 (Prims.of_int (611)) (Prims.of_int (19))
                                 (Prims.of_int (611)) (Prims.of_int (31)))))
                        (Obj.magic uu___3)
                        (fun uu___4 ->
                           FStar_Tactics_Effect.lift_div_tac
                             (fun uu___5 ->
                                Prims.strcat "  Names to reduce in " uu___4)) in
                    FStar_Tactics_Effect.tac_bind
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range "Meta.Interface.fst"
                               (Prims.of_int (155)) (Prims.of_int (8))
                               (Prims.of_int (155)) (Prims.of_int (88)))))
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range "Meta.Interface.fst"
                               (Prims.of_int (155)) (Prims.of_int (2))
                               (Prims.of_int (155)) (Prims.of_int (88)))))
                      (Obj.magic uu___2)
                      (fun uu___3 ->
                         (fun uu___3 ->
                            Obj.magic
                              (FStarC_Tactics_V1_Builtins.print uu___3))
                           uu___3) in
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Meta.Interface.fst"
                                (Prims.of_int (155)) (Prims.of_int (2))
                                (Prims.of_int (155)) (Prims.of_int (88)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Meta.Interface.fst"
                                (Prims.of_int (155)) (Prims.of_int (89))
                                (Prims.of_int (157)) (Prims.of_int (54)))))
                       (Obj.magic uu___1)
                       (fun uu___2 ->
                          (fun uu___2 ->
                             let uu___3 =
                               let uu___4 =
                                 FStarC_Tactics_V1_Builtins.top_env () in
                               FStar_Tactics_Effect.tac_bind
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "Meta.Interface.fst"
                                          (Prims.of_int (156))
                                          (Prims.of_int (28))
                                          (Prims.of_int (156))
                                          (Prims.of_int (40)))))
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "Meta.Interface.fst"
                                          (Prims.of_int (156))
                                          (Prims.of_int (14))
                                          (Prims.of_int (156))
                                          (Prims.of_int (79)))))
                                 (Obj.magic uu___4)
                                 (fun uu___5 ->
                                    (fun uu___5 ->
                                       let uu___6 =
                                         let uu___7 =
                                           let uu___8 = to_reduce f_typ in
                                           FStar_Tactics_Effect.tac_bind
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "Meta.Interface.fst"
                                                      (Prims.of_int (156))
                                                      (Prims.of_int (54))
                                                      (Prims.of_int (156))
                                                      (Prims.of_int (71)))))
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "Meta.Interface.fst"
                                                      (Prims.of_int (156))
                                                      (Prims.of_int (43))
                                                      (Prims.of_int (156))
                                                      (Prims.of_int (71)))))
                                             (Obj.magic uu___8)
                                             (fun uu___9 ->
                                                FStar_Tactics_Effect.lift_div_tac
                                                  (fun uu___10 ->
                                                     Fstarcompiler.FStar_Pervasives.delta_only
                                                       uu___9)) in
                                         FStar_Tactics_Effect.tac_bind
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Meta.Interface.fst"
                                                    (Prims.of_int (156))
                                                    (Prims.of_int (43))
                                                    (Prims.of_int (156))
                                                    (Prims.of_int (71)))))
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Meta.Interface.fst"
                                                    (Prims.of_int (156))
                                                    (Prims.of_int (41))
                                                    (Prims.of_int (156))
                                                    (Prims.of_int (73)))))
                                           (Obj.magic uu___7)
                                           (fun uu___8 ->
                                              FStar_Tactics_Effect.lift_div_tac
                                                (fun uu___9 -> [uu___8])) in
                                       Obj.magic
                                         (FStar_Tactics_Effect.tac_bind
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Meta.Interface.fst"
                                                     (Prims.of_int (156))
                                                     (Prims.of_int (41))
                                                     (Prims.of_int (156))
                                                     (Prims.of_int (73)))))
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Meta.Interface.fst"
                                                     (Prims.of_int (156))
                                                     (Prims.of_int (14))
                                                     (Prims.of_int (156))
                                                     (Prims.of_int (79)))))
                                            (Obj.magic uu___6)
                                            (fun uu___7 ->
                                               (fun uu___7 ->
                                                  Obj.magic
                                                    (FStarC_Tactics_V1_Builtins.norm_term_env
                                                       uu___5 uu___7 f_typ))
                                                 uu___7))) uu___5) in
                             Obj.magic
                               (FStar_Tactics_Effect.tac_bind
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Meta.Interface.fst"
                                           (Prims.of_int (156))
                                           (Prims.of_int (14))
                                           (Prims.of_int (156))
                                           (Prims.of_int (79)))))
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Meta.Interface.fst"
                                           (Prims.of_int (157))
                                           (Prims.of_int (2))
                                           (Prims.of_int (157))
                                           (Prims.of_int (54)))))
                                  (Obj.magic uu___3)
                                  (fun uu___4 ->
                                     (fun f_typ1 ->
                                        let uu___4 =
                                          push_pre st inv_bv f_typ1 in
                                        Obj.magic
                                          (FStar_Tactics_Effect.tac_bind
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "Meta.Interface.fst"
                                                      (Prims.of_int (157))
                                                      (Prims.of_int (28))
                                                      (Prims.of_int (157))
                                                      (Prims.of_int (54)))))
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "Meta.Interface.fst"
                                                      (Prims.of_int (157))
                                                      (Prims.of_int (2))
                                                      (Prims.of_int (157))
                                                      (Prims.of_int (54)))))
                                             (Obj.magic uu___4)
                                             (fun uu___5 ->
                                                (fun uu___5 ->
                                                   Obj.magic
                                                     (lambda_over_p inv_bv
                                                        sort uu___5)) uu___5)))
                                       uu___4))) uu___2))) uu___1)
let (lambda_over_index_and_p :
  state ->
    Fstarcompiler.FStarC_Reflection_Types.name ->
      Fstarcompiler.FStarC_Reflection_Types.term ->
        Fstarcompiler.FStarC_Reflection_Types.bv ->
          Fstarcompiler.FStarC_Reflection_Types.typ ->
            (Fstarcompiler.FStarC_Reflection_Types.term, unit)
              FStar_Tactics_Effect.tac_repr)
  =
  fun st ->
    fun f_name ->
      fun f_typ ->
        fun inv_bv ->
          fun inv_bv_sort ->
            let uu___ = to_reduce f_typ in
            FStar_Tactics_Effect.tac_bind
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "Meta.Interface.fst"
                       (Prims.of_int (163)) (Prims.of_int (12))
                       (Prims.of_int (163)) (Prims.of_int (27)))))
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "Meta.Interface.fst"
                       (Prims.of_int (164)) (Prims.of_int (2))
                       (Prims.of_int (189)) (Prims.of_int (50)))))
              (Obj.magic uu___)
              (fun uu___1 ->
                 (fun fvs ->
                    let uu___1 =
                      let uu___2 =
                        let uu___3 =
                          let uu___4 =
                            let uu___5 =
                              FStarC_Tactics_V1_Builtins.term_to_string f_typ in
                            FStar_Tactics_Effect.tac_bind
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Meta.Interface.fst"
                                       (Prims.of_int (164))
                                       (Prims.of_int (45))
                                       (Prims.of_int (164))
                                       (Prims.of_int (65)))))
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range "Prims.fst"
                                       (Prims.of_int (611))
                                       (Prims.of_int (19))
                                       (Prims.of_int (611))
                                       (Prims.of_int (31)))))
                              (Obj.magic uu___5)
                              (fun uu___6 ->
                                 FStar_Tactics_Effect.lift_div_tac
                                   (fun uu___7 ->
                                      Prims.strcat uu___6
                                        (Prims.strcat ": "
                                           (FStar_String.concat ", " fvs)))) in
                          FStar_Tactics_Effect.tac_bind
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range "Meta.Interface.fst"
                                     (Prims.of_int (164)) (Prims.of_int (45))
                                     (Prims.of_int (164)) (Prims.of_int (97)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range "Prims.fst"
                                     (Prims.of_int (611)) (Prims.of_int (19))
                                     (Prims.of_int (611)) (Prims.of_int (31)))))
                            (Obj.magic uu___4)
                            (fun uu___5 ->
                               FStar_Tactics_Effect.lift_div_tac
                                 (fun uu___6 ->
                                    Prims.strcat "Names to reduce in " uu___5)) in
                        FStar_Tactics_Effect.tac_bind
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range "Meta.Interface.fst"
                                   (Prims.of_int (164)) (Prims.of_int (21))
                                   (Prims.of_int (164)) (Prims.of_int (97)))))
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range "Prims.fst"
                                   (Prims.of_int (611)) (Prims.of_int (19))
                                   (Prims.of_int (611)) (Prims.of_int (31)))))
                          (Obj.magic uu___3)
                          (fun uu___4 ->
                             FStar_Tactics_Effect.lift_div_tac
                               (fun uu___5 -> Prims.strcat st.indent uu___4)) in
                      FStar_Tactics_Effect.tac_bind
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range "Meta.Interface.fst"
                                 (Prims.of_int (164)) (Prims.of_int (8))
                                 (Prims.of_int (164)) (Prims.of_int (98)))))
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range "Meta.Interface.fst"
                                 (Prims.of_int (164)) (Prims.of_int (2))
                                 (Prims.of_int (164)) (Prims.of_int (98)))))
                        (Obj.magic uu___2)
                        (fun uu___3 ->
                           (fun uu___3 ->
                              Obj.magic
                                (FStarC_Tactics_V1_Builtins.print uu___3))
                             uu___3) in
                    Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range "Meta.Interface.fst"
                                  (Prims.of_int (164)) (Prims.of_int (2))
                                  (Prims.of_int (164)) (Prims.of_int (98)))))
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range "Meta.Interface.fst"
                                  (Prims.of_int (164)) (Prims.of_int (99))
                                  (Prims.of_int (189)) (Prims.of_int (50)))))
                         (Obj.magic uu___1)
                         (fun uu___2 ->
                            (fun uu___2 ->
                               let uu___3 =
                                 let uu___4 =
                                   FStarC_Tactics_V1_Builtins.top_env () in
                                 FStar_Tactics_Effect.tac_bind
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "Meta.Interface.fst"
                                            (Prims.of_int (165))
                                            (Prims.of_int (28))
                                            (Prims.of_int (165))
                                            (Prims.of_int (40)))))
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "Meta.Interface.fst"
                                            (Prims.of_int (165))
                                            (Prims.of_int (14))
                                            (Prims.of_int (165))
                                            (Prims.of_int (79)))))
                                   (Obj.magic uu___4)
                                   (fun uu___5 ->
                                      (fun uu___5 ->
                                         let uu___6 =
                                           let uu___7 =
                                             let uu___8 = to_reduce f_typ in
                                             FStar_Tactics_Effect.tac_bind
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "Meta.Interface.fst"
                                                        (Prims.of_int (165))
                                                        (Prims.of_int (54))
                                                        (Prims.of_int (165))
                                                        (Prims.of_int (71)))))
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "Meta.Interface.fst"
                                                        (Prims.of_int (165))
                                                        (Prims.of_int (43))
                                                        (Prims.of_int (165))
                                                        (Prims.of_int (71)))))
                                               (Obj.magic uu___8)
                                               (fun uu___9 ->
                                                  FStar_Tactics_Effect.lift_div_tac
                                                    (fun uu___10 ->
                                                       Fstarcompiler.FStar_Pervasives.delta_only
                                                         uu___9)) in
                                           FStar_Tactics_Effect.tac_bind
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "Meta.Interface.fst"
                                                      (Prims.of_int (165))
                                                      (Prims.of_int (43))
                                                      (Prims.of_int (165))
                                                      (Prims.of_int (71)))))
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "Meta.Interface.fst"
                                                      (Prims.of_int (165))
                                                      (Prims.of_int (41))
                                                      (Prims.of_int (165))
                                                      (Prims.of_int (73)))))
                                             (Obj.magic uu___7)
                                             (fun uu___8 ->
                                                FStar_Tactics_Effect.lift_div_tac
                                                  (fun uu___9 -> [uu___8])) in
                                         Obj.magic
                                           (FStar_Tactics_Effect.tac_bind
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "Meta.Interface.fst"
                                                       (Prims.of_int (165))
                                                       (Prims.of_int (41))
                                                       (Prims.of_int (165))
                                                       (Prims.of_int (73)))))
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "Meta.Interface.fst"
                                                       (Prims.of_int (165))
                                                       (Prims.of_int (14))
                                                       (Prims.of_int (165))
                                                       (Prims.of_int (79)))))
                                              (Obj.magic uu___6)
                                              (fun uu___7 ->
                                                 (fun uu___7 ->
                                                    Obj.magic
                                                      (FStarC_Tactics_V1_Builtins.norm_term_env
                                                         uu___5 uu___7 f_typ))
                                                   uu___7))) uu___5) in
                               Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "Meta.Interface.fst"
                                             (Prims.of_int (165))
                                             (Prims.of_int (14))
                                             (Prims.of_int (165))
                                             (Prims.of_int (79)))))
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "Meta.Interface.fst"
                                             (Prims.of_int (166))
                                             (Prims.of_int (2))
                                             (Prims.of_int (189))
                                             (Prims.of_int (50)))))
                                    (Obj.magic uu___3)
                                    (fun uu___4 ->
                                       (fun f_typ1 ->
                                          let uu___4 =
                                            let uu___5 =
                                              let uu___6 =
                                                let uu___7 =
                                                  let uu___8 =
                                                    FStarC_Tactics_V1_Builtins.term_to_string
                                                      f_typ1 in
                                                  FStar_Tactics_Effect.tac_bind
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "Meta.Interface.fst"
                                                             (Prims.of_int (166))
                                                             (Prims.of_int (45))
                                                             (Prims.of_int (166))
                                                             (Prims.of_int (65)))))
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "Prims.fst"
                                                             (Prims.of_int (611))
                                                             (Prims.of_int (19))
                                                             (Prims.of_int (611))
                                                             (Prims.of_int (31)))))
                                                    (Obj.magic uu___8)
                                                    (fun uu___9 ->
                                                       FStar_Tactics_Effect.lift_div_tac
                                                         (fun uu___10 ->
                                                            Prims.strcat
                                                              uu___9
                                                              (Prims.strcat
                                                                 ": "
                                                                 (FStar_String.concat
                                                                    ", " fvs)))) in
                                                FStar_Tactics_Effect.tac_bind
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "Meta.Interface.fst"
                                                           (Prims.of_int (166))
                                                           (Prims.of_int (45))
                                                           (Prims.of_int (166))
                                                           (Prims.of_int (97)))))
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "Prims.fst"
                                                           (Prims.of_int (611))
                                                           (Prims.of_int (19))
                                                           (Prims.of_int (611))
                                                           (Prims.of_int (31)))))
                                                  (Obj.magic uu___7)
                                                  (fun uu___8 ->
                                                     FStar_Tactics_Effect.lift_div_tac
                                                       (fun uu___9 ->
                                                          Prims.strcat
                                                            "After reduction in "
                                                            uu___8)) in
                                              FStar_Tactics_Effect.tac_bind
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "Meta.Interface.fst"
                                                         (Prims.of_int (166))
                                                         (Prims.of_int (21))
                                                         (Prims.of_int (166))
                                                         (Prims.of_int (97)))))
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "Prims.fst"
                                                         (Prims.of_int (611))
                                                         (Prims.of_int (19))
                                                         (Prims.of_int (611))
                                                         (Prims.of_int (31)))))
                                                (Obj.magic uu___6)
                                                (fun uu___7 ->
                                                   FStar_Tactics_Effect.lift_div_tac
                                                     (fun uu___8 ->
                                                        Prims.strcat
                                                          st.indent uu___7)) in
                                            FStar_Tactics_Effect.tac_bind
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "Meta.Interface.fst"
                                                       (Prims.of_int (166))
                                                       (Prims.of_int (8))
                                                       (Prims.of_int (166))
                                                       (Prims.of_int (98)))))
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "Meta.Interface.fst"
                                                       (Prims.of_int (166))
                                                       (Prims.of_int (2))
                                                       (Prims.of_int (166))
                                                       (Prims.of_int (98)))))
                                              (Obj.magic uu___5)
                                              (fun uu___6 ->
                                                 (fun uu___6 ->
                                                    Obj.magic
                                                      (FStarC_Tactics_V1_Builtins.print
                                                         uu___6)) uu___6) in
                                          Obj.magic
                                            (FStar_Tactics_Effect.tac_bind
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "Meta.Interface.fst"
                                                        (Prims.of_int (166))
                                                        (Prims.of_int (2))
                                                        (Prims.of_int (166))
                                                        (Prims.of_int (98)))))
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "Meta.Interface.fst"
                                                        (Prims.of_int (167))
                                                        (Prims.of_int (2))
                                                        (Prims.of_int (189))
                                                        (Prims.of_int (50)))))
                                               (Obj.magic uu___4)
                                               (fun uu___5 ->
                                                  (fun uu___5 ->
                                                     let uu___6 =
                                                       FStarC_Tactics_V1_Builtins.inspect
                                                         f_typ1 in
                                                     Obj.magic
                                                       (FStar_Tactics_Effect.tac_bind
                                                          (FStar_Sealed.seal
                                                             (Obj.magic
                                                                (FStar_Range.mk_range
                                                                   "Meta.Interface.fst"
                                                                   (Prims.of_int (167))
                                                                   (Prims.of_int (8))
                                                                   (Prims.of_int (167))
                                                                   (Prims.of_int (21)))))
                                                          (FStar_Sealed.seal
                                                             (Obj.magic
                                                                (FStar_Range.mk_range
                                                                   "Meta.Interface.fst"
                                                                   (Prims.of_int (167))
                                                                   (Prims.of_int (2))
                                                                   (Prims.of_int (189))
                                                                   (Prims.of_int (50)))))
                                                          (Obj.magic uu___6)
                                                          (fun uu___7 ->
                                                             (fun uu___7 ->
                                                                match uu___7
                                                                with
                                                                | Fstarcompiler.FStarC_Reflection_V1_Data.Tv_Arrow
                                                                    (bv, c)
                                                                    ->
                                                                    let uu___8
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    Fstarcompiler.FStarC_Reflection_V1_Builtins.inspect_binder
                                                                    bv)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (169))
                                                                    (Prims.of_int (71))
                                                                    (Prims.of_int (169))
                                                                    (Prims.of_int (88)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (168))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (186))
                                                                    (Prims.of_int (11)))))
                                                                    (Obj.magic
                                                                    uu___8)
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    uu___9 ->
                                                                    match uu___9
                                                                    with
                                                                    | 
                                                                    {
                                                                    Fstarcompiler.FStarC_Reflection_V1_Data.binder_bv
                                                                    = bv1;
                                                                    Fstarcompiler.FStarC_Reflection_V1_Data.binder_qual
                                                                    = qual;
                                                                    Fstarcompiler.FStarC_Reflection_V1_Data.binder_attrs
                                                                    = uu___10;
                                                                    Fstarcompiler.FStarC_Reflection_V1_Data.binder_sort
                                                                    = sort;_}
                                                                    ->
                                                                    let uu___11
                                                                    =
                                                                    if
                                                                    Prims.op_Negation
                                                                    (is_implicit
                                                                    qual)
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (let uu___12
                                                                    =
                                                                    let uu___13
                                                                    =
                                                                    let uu___14
                                                                    =
                                                                    string_of_name
                                                                    f_name in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (171))
                                                                    (Prims.of_int (54))
                                                                    (Prims.of_int (171))
                                                                    (Prims.of_int (75)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___14)
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    Prims.strcat
                                                                    uu___15
                                                                    " is not implicit")) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (171))
                                                                    (Prims.of_int (54))
                                                                    (Prims.of_int (171))
                                                                    (Prims.of_int (96)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___13)
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    Prims.strcat
                                                                    "The first parameter in the type of "
                                                                    uu___14)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (171))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (171))
                                                                    (Prims.of_int (97)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (171))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (171))
                                                                    (Prims.of_int (97)))))
                                                                    (Obj.magic
                                                                    uu___12)
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    FStar_Tactics_V1_Derived.fail
                                                                    uu___13)))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___13
                                                                    -> ()))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (170))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (171))
                                                                    (Prims.of_int (97)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (172))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (186))
                                                                    (Prims.of_int (11)))))
                                                                    (Obj.magic
                                                                    uu___11)
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    let uu___13
                                                                    =
                                                                    let uu___14
                                                                    =
                                                                    let uu___15
                                                                    =
                                                                    let uu___16
                                                                    =
                                                                    FStarC_Tactics_V1_Builtins.term_to_string
                                                                    sort in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (172))
                                                                    (Prims.of_int (52))
                                                                    (Prims.of_int (172))
                                                                    (Prims.of_int (71)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___16)
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___18
                                                                    ->
                                                                    Prims.strcat
                                                                    "  Found index of type "
                                                                    uu___17)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (172))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (172))
                                                                    (Prims.of_int (71)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___15)
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    Prims.strcat
                                                                    st.indent
                                                                    uu___16)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (172))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (172))
                                                                    (Prims.of_int (72)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (172))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (172))
                                                                    (Prims.of_int (72)))))
                                                                    (Obj.magic
                                                                    uu___14)
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    Obj.magic
                                                                    (FStarC_Tactics_V1_Builtins.print
                                                                    uu___15))
                                                                    uu___15) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (172))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (172))
                                                                    (Prims.of_int (72)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (172))
                                                                    (Prims.of_int (73))
                                                                    (Prims.of_int (186))
                                                                    (Prims.of_int (11)))))
                                                                    (Obj.magic
                                                                    uu___13)
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    let uu___15
                                                                    =
                                                                    match 
                                                                    Fstarcompiler.FStarC_Reflection_V1_Builtins.inspect_comp
                                                                    c
                                                                    with
                                                                    | 
                                                                    Fstarcompiler.FStarC_Reflection_V1_Data.C_Total
                                                                    t ->
                                                                    let uu___16
                                                                    =
                                                                    let uu___17
                                                                    =
                                                                    let uu___18
                                                                    =
                                                                    let uu___19
                                                                    =
                                                                    FStarC_Tactics_V1_Builtins.term_to_string
                                                                    t in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (176))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (176))
                                                                    (Prims.of_int (47)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___19)
                                                                    (fun
                                                                    uu___20
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___21
                                                                    ->
                                                                    Prims.strcat
                                                                    uu___20
                                                                    "\n")) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (176))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (176))
                                                                    (Prims.of_int (54)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___18)
                                                                    (fun
                                                                    uu___19
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___20
                                                                    ->
                                                                    Prims.strcat
                                                                    st.indent
                                                                    uu___19)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (176))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (176))
                                                                    (Prims.of_int (55)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (176))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (176))
                                                                    (Prims.of_int (55)))))
                                                                    (Obj.magic
                                                                    uu___17)
                                                                    (fun
                                                                    uu___18
                                                                    ->
                                                                    (fun
                                                                    uu___18
                                                                    ->
                                                                    Obj.magic
                                                                    (FStarC_Tactics_V1_Builtins.print
                                                                    uu___18))
                                                                    uu___18) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (176))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (176))
                                                                    (Prims.of_int (55)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (176))
                                                                    (Prims.of_int (56))
                                                                    (Prims.of_int (182))
                                                                    (Prims.of_int (56)))))
                                                                    (Obj.magic
                                                                    uu___16)
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    let uu___18
                                                                    =
                                                                    push_pre
                                                                    st inv_bv
                                                                    t in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (178))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (178))
                                                                    (Prims.of_int (40)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (178))
                                                                    (Prims.of_int (43))
                                                                    (Prims.of_int (182))
                                                                    (Prims.of_int (56)))))
                                                                    (Obj.magic
                                                                    uu___18)
                                                                    (fun
                                                                    uu___19
                                                                    ->
                                                                    (fun t1
                                                                    ->
                                                                    let uu___19
                                                                    =
                                                                    lambda_over_p
                                                                    inv_bv
                                                                    inv_bv_sort
                                                                    t1 in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (180))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (180))
                                                                    (Prims.of_int (54)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (182))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (182))
                                                                    (Prims.of_int (56)))))
                                                                    (Obj.magic
                                                                    uu___19)
                                                                    (fun
                                                                    uu___20
                                                                    ->
                                                                    (fun t2
                                                                    ->
                                                                    Obj.magic
                                                                    (FStarC_Tactics_V1_Builtins.pack
                                                                    (Fstarcompiler.FStarC_Reflection_V1_Data.Tv_Abs
                                                                    ((FStar_Reflection_V1_Derived.mk_implicit_binder
                                                                    bv1 sort),
                                                                    t2))))
                                                                    uu___20)))
                                                                    uu___19)))
                                                                    uu___17)
                                                                    | 
                                                                    uu___16
                                                                    ->
                                                                    let uu___17
                                                                    =
                                                                    let uu___18
                                                                    =
                                                                    let uu___19
                                                                    =
                                                                    string_of_name
                                                                    f_name in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (184))
                                                                    (Prims.of_int (42))
                                                                    (Prims.of_int (184))
                                                                    (Prims.of_int (63)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___19)
                                                                    (fun
                                                                    uu___20
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___21
                                                                    ->
                                                                    Prims.strcat
                                                                    uu___20
                                                                    " is impure")) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (184))
                                                                    (Prims.of_int (42))
                                                                    (Prims.of_int (184))
                                                                    (Prims.of_int (78)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___18)
                                                                    (fun
                                                                    uu___19
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___20
                                                                    ->
                                                                    Prims.strcat
                                                                    "The first arrow of "
                                                                    uu___19)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (184))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (184))
                                                                    (Prims.of_int (79)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (184))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (184))
                                                                    (Prims.of_int (79)))))
                                                                    (Obj.magic
                                                                    uu___17)
                                                                    (fun
                                                                    uu___18
                                                                    ->
                                                                    FStar_Tactics_V1_Derived.fail
                                                                    uu___18) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (174))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (184))
                                                                    (Prims.of_int (79)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (173))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (173))
                                                                    (Prims.of_int (15)))))
                                                                    (Obj.magic
                                                                    uu___15)
                                                                    (fun
                                                                    f_typ2 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___16
                                                                    -> f_typ2))))
                                                                    uu___14)))
                                                                    uu___12)))
                                                                    uu___9))
                                                                | uu___8 ->
                                                                    let uu___9
                                                                    =
                                                                    let uu___10
                                                                    =
                                                                    string_of_name
                                                                    f_name in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (188))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (188))
                                                                    (Prims.of_int (33)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___10)
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    Prims.strcat
                                                                    uu___11
                                                                    "is expected to have an arrow type with the index as a first argument")) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (188))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (189))
                                                                    (Prims.of_int (50)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (188))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (189))
                                                                    (Prims.of_int (50)))))
                                                                    (Obj.magic
                                                                    uu___9)
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    FStar_Tactics_V1_Derived.fail
                                                                    uu___10)))
                                                               uu___7)))
                                                    uu___5))) uu___4)))
                              uu___2))) uu___1)
let must :
  'uuuuu .
    'uuuuu FStar_Pervasives_Native.option ->
      ('uuuuu, unit) FStar_Tactics_Effect.tac_repr
  =
  fun uu___ ->
    (fun uu___ ->
       match uu___ with
       | FStar_Pervasives_Native.Some x ->
           Obj.magic (FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> x))
       | FStar_Pervasives_Native.None ->
           Obj.magic (FStar_Tactics_V1_Derived.fail "Invalid argument: must"))
      uu___
let (tm_unit : Fstarcompiler.FStarC_Reflection_Types.term) =
  Fstarcompiler.FStarC_Reflection_V2_Builtins.pack_ln
    (Fstarcompiler.FStarC_Reflection_V2_Data.Tv_Const
       Fstarcompiler.FStarC_Reflection_V2_Data.C_Unit)
let (binder_is_legit :
  Fstarcompiler.FStarC_Reflection_Types.name ->
    Fstarcompiler.FStarC_Reflection_Types.term ->
      Fstarcompiler.FStarC_Reflection_Types.binder ->
        (Prims.bool, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun f_name ->
    fun t_i ->
      fun binder ->
        let uu___ =
          Obj.magic
            (FStar_Tactics_Effect.lift_div_tac
               (fun uu___1 ->
                  Fstarcompiler.FStarC_Reflection_V1_Builtins.inspect_binder
                    binder)) in
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Meta.Interface.fst"
                   (Prims.of_int (201)) (Prims.of_int (67))
                   (Prims.of_int (201)) (Prims.of_int (88)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Meta.Interface.fst"
                   (Prims.of_int (200)) (Prims.of_int (49))
                   (Prims.of_int (212)) (Prims.of_int (24)))))
          (Obj.magic uu___)
          (fun uu___1 ->
             (fun uu___1 ->
                match uu___1 with
                | { Fstarcompiler.FStarC_Reflection_V1_Data.binder_bv = bv;
                    Fstarcompiler.FStarC_Reflection_V1_Data.binder_qual =
                      qual;
                    Fstarcompiler.FStarC_Reflection_V1_Data.binder_attrs =
                      uu___2;
                    Fstarcompiler.FStarC_Reflection_V1_Data.binder_sort =
                      sort;_}
                    ->
                    let uu___3 =
                      Obj.magic
                        (FStar_Tactics_Effect.lift_div_tac
                           (fun uu___4 ->
                              Fstarcompiler.FStarC_Reflection_V1_Builtins.inspect_bv
                                bv)) in
                    Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range "Meta.Interface.fst"
                                  (Prims.of_int (202)) (Prims.of_int (29))
                                  (Prims.of_int (202)) (Prims.of_int (42)))))
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range "Meta.Interface.fst"
                                  (Prims.of_int (201)) (Prims.of_int (91))
                                  (Prims.of_int (212)) (Prims.of_int (24)))))
                         (Obj.magic uu___3)
                         (fun uu___4 ->
                            (fun uu___4 ->
                               match uu___4 with
                               | {
                                   Fstarcompiler.FStarC_Reflection_V1_Data.bv_ppname
                                     = name;
                                   Fstarcompiler.FStarC_Reflection_V1_Data.bv_index
                                     = uu___5;_}
                                   ->
                                   let uu___6 =
                                     Obj.magic
                                       (FStar_Tactics_Effect.lift_div_tac
                                          (fun uu___7 -> is_implicit qual)) in
                                   Obj.magic
                                     (FStar_Tactics_Effect.tac_bind
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Meta.Interface.fst"
                                                 (Prims.of_int (203))
                                                 (Prims.of_int (17))
                                                 (Prims.of_int (203))
                                                 (Prims.of_int (33)))))
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Meta.Interface.fst"
                                                 (Prims.of_int (203))
                                                 (Prims.of_int (36))
                                                 (Prims.of_int (212))
                                                 (Prims.of_int (24)))))
                                        (Obj.magic uu___6)
                                        (fun uu___7 ->
                                           (fun implicit ->
                                              let uu___7 =
                                                Obj.magic
                                                  (FStar_Tactics_Effect.lift_div_tac
                                                     (fun uu___8 ->
                                                        Fstarcompiler.FStarC_Reflection_V1_Builtins.term_eq
                                                          t_i sort)) in
                                              Obj.magic
                                                (FStar_Tactics_Effect.tac_bind
                                                   (FStar_Sealed.seal
                                                      (Obj.magic
                                                         (FStar_Range.mk_range
                                                            "Meta.Interface.fst"
                                                            (Prims.of_int (204))
                                                            (Prims.of_int (19))
                                                            (Prims.of_int (204))
                                                            (Prims.of_int (35)))))
                                                   (FStar_Sealed.seal
                                                      (Obj.magic
                                                         (FStar_Range.mk_range
                                                            "Meta.Interface.fst"
                                                            (Prims.of_int (205))
                                                            (Prims.of_int (2))
                                                            (Prims.of_int (212))
                                                            (Prims.of_int (24)))))
                                                   (Obj.magic uu___7)
                                                   (fun uu___8 ->
                                                      (fun right_type ->
                                                         let uu___8 =
                                                           if
                                                             implicit &&
                                                               (Prims.op_Negation
                                                                  right_type)
                                                           then
                                                             Obj.magic
                                                               (Obj.repr
                                                                  (let uu___9
                                                                    =
                                                                    let uu___10
                                                                    =
                                                                    let uu___11
                                                                    =
                                                                    string_of_name
                                                                    f_name in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (206))
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (206))
                                                                    (Prims.of_int (69)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___11)
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    Prims.strcat
                                                                    uu___12
                                                                    " is implicit but not of the index type")) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (206))
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (207))
                                                                    (Prims.of_int (35)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___10)
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    Prims.strcat
                                                                    "WARNING: the first parameter of "
                                                                    uu___11)) in
                                                                   FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (206))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (207))
                                                                    (Prims.of_int (36)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (206))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (207))
                                                                    (Prims.of_int (36)))))
                                                                    (Obj.magic
                                                                    uu___9)
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    Obj.magic
                                                                    (FStarC_Tactics_V1_Builtins.print
                                                                    uu___10))
                                                                    uu___10)))
                                                           else
                                                             Obj.magic
                                                               (Obj.repr
                                                                  (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    -> ()))) in
                                                         Obj.magic
                                                           (FStar_Tactics_Effect.tac_bind
                                                              (FStar_Sealed.seal
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (205))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (207))
                                                                    (Prims.of_int (36)))))
                                                              (FStar_Sealed.seal
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (209))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (212))
                                                                    (Prims.of_int (24)))))
                                                              (Obj.magic
                                                                 uu___8)
                                                              (fun uu___9 ->
                                                                 (fun uu___9
                                                                    ->
                                                                    let uu___10
                                                                    =
                                                                    if
                                                                    right_type
                                                                    &&
                                                                    (Prims.op_Negation
                                                                    implicit)
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (let uu___11
                                                                    =
                                                                    let uu___12
                                                                    =
                                                                    let uu___13
                                                                    =
                                                                    string_of_name
                                                                    f_name in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (210))
                                                                    (Prims.of_int (38))
                                                                    (Prims.of_int (210))
                                                                    (Prims.of_int (59)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___13)
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    Prims.strcat
                                                                    uu___14
                                                                    " is not implicit but has the index type")) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (210))
                                                                    (Prims.of_int (38))
                                                                    (Prims.of_int (211))
                                                                    (Prims.of_int (36)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___12)
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    Prims.strcat
                                                                    "the first parameter of "
                                                                    uu___13)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (210))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (211))
                                                                    (Prims.of_int (37)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (210))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (211))
                                                                    (Prims.of_int (37)))))
                                                                    (Obj.magic
                                                                    uu___11)
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    FStar_Tactics_V1_Derived.fail
                                                                    uu___12)))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___12
                                                                    -> ()))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (209))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (211))
                                                                    (Prims.of_int (37)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (212))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (212))
                                                                    (Prims.of_int (24)))))
                                                                    (Obj.magic
                                                                    uu___10)
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    right_type
                                                                    &&
                                                                    implicit))))
                                                                   uu___9)))
                                                        uu___8))) uu___7)))
                              uu___4))) uu___1)
let rec (visit_function :
  Fstarcompiler.FStarC_Reflection_Types.term ->
    state ->
      Fstarcompiler.FStarC_Reflection_Types.name ->
        ((state * Fstarcompiler.FStarC_Reflection_Types.sigelt Prims.list),
          unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t_i ->
    fun st ->
      fun f_name ->
        if
          FStar_List_Tot_Base.existsb
            (fun uu___ -> match uu___ with | (name, uu___1) -> name = f_name)
            st.seen
        then
          let uu___ =
            let uu___1 =
              let uu___2 =
                let uu___3 = string_of_name f_name in
                FStar_Tactics_Effect.tac_bind
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "Meta.Interface.fst"
                           (Prims.of_int (217)) (Prims.of_int (52))
                           (Prims.of_int (217)) (Prims.of_int (73)))))
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "Prims.fst"
                           (Prims.of_int (611)) (Prims.of_int (19))
                           (Prims.of_int (611)) (Prims.of_int (31)))))
                  (Obj.magic uu___3)
                  (fun uu___4 ->
                     FStar_Tactics_Effect.lift_div_tac
                       (fun uu___5 -> Prims.strcat "Already visited " uu___4)) in
              FStar_Tactics_Effect.tac_bind
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Meta.Interface.fst"
                         (Prims.of_int (217)) (Prims.of_int (31))
                         (Prims.of_int (217)) (Prims.of_int (73)))))
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Prims.fst" (Prims.of_int (611))
                         (Prims.of_int (19)) (Prims.of_int (611))
                         (Prims.of_int (31))))) (Obj.magic uu___2)
                (fun uu___3 ->
                   FStar_Tactics_Effect.lift_div_tac
                     (fun uu___4 -> Prims.strcat st.indent uu___3)) in
            FStar_Tactics_Effect.tac_bind
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "Meta.Interface.fst"
                       (Prims.of_int (217)) (Prims.of_int (18))
                       (Prims.of_int (217)) (Prims.of_int (74)))))
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "Meta.Interface.fst"
                       (Prims.of_int (217)) (Prims.of_int (12))
                       (Prims.of_int (217)) (Prims.of_int (74)))))
              (Obj.magic uu___1)
              (fun uu___2 ->
                 (fun uu___2 ->
                    Obj.magic (FStarC_Tactics_V1_Builtins.print uu___2))
                   uu___2) in
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Meta.Interface.fst"
                     (Prims.of_int (217)) (Prims.of_int (12))
                     (Prims.of_int (217)) (Prims.of_int (74)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Meta.Interface.fst"
                     (Prims.of_int (220)) (Prims.of_int (4))
                     (Prims.of_int (220)) (Prims.of_int (10)))))
            (Obj.magic uu___)
            (fun uu___1 ->
               FStar_Tactics_Effect.lift_div_tac (fun uu___2 -> (st, [])))
        else
          (let uu___1 =
             let uu___2 = FStarC_Tactics_V1_Builtins.top_env () in
             FStar_Tactics_Effect.tac_bind
               (FStar_Sealed.seal
                  (Obj.magic
                     (FStar_Range.mk_range "Meta.Interface.fst"
                        (Prims.of_int (224)) (Prims.of_int (23))
                        (Prims.of_int (224)) (Prims.of_int (35)))))
               (FStar_Sealed.seal
                  (Obj.magic
                     (FStar_Range.mk_range "Meta.Interface.fst"
                        (Prims.of_int (224)) (Prims.of_int (12))
                        (Prims.of_int (224)) (Prims.of_int (42)))))
               (Obj.magic uu___2)
               (fun uu___3 ->
                  FStar_Tactics_Effect.lift_div_tac
                    (fun uu___4 ->
                       Fstarcompiler.FStarC_Reflection_V1_Builtins.lookup_typ
                         uu___3 f_name)) in
           FStar_Tactics_Effect.tac_bind
             (FStar_Sealed.seal
                (Obj.magic
                   (FStar_Range.mk_range "Meta.Interface.fst"
                      (Prims.of_int (224)) (Prims.of_int (12))
                      (Prims.of_int (224)) (Prims.of_int (42)))))
             (FStar_Sealed.seal
                (Obj.magic
                   (FStar_Range.mk_range "Meta.Interface.fst"
                      (Prims.of_int (224)) (Prims.of_int (45))
                      (Prims.of_int (433)) (Prims.of_int (18)))))
             (Obj.magic uu___1)
             (fun uu___2 ->
                (fun f ->
                   let uu___2 =
                     match f with
                     | FStar_Pervasives_Native.Some f1 ->
                         Obj.magic
                           (FStar_Tactics_Effect.lift_div_tac
                              (fun uu___3 -> f1))
                     | FStar_Pervasives_Native.None ->
                         Obj.magic
                           (FStar_Tactics_V1_Derived.fail
                              "unexpected: name not in the environment") in
                   Obj.magic
                     (FStar_Tactics_Effect.tac_bind
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range "Meta.Interface.fst"
                                 (Prims.of_int (225)) (Prims.of_int (12))
                                 (Prims.of_int (225)) (Prims.of_int (93)))))
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range "Meta.Interface.fst"
                                 (Prims.of_int (226)) (Prims.of_int (4))
                                 (Prims.of_int (433)) (Prims.of_int (18)))))
                        (Obj.magic uu___2)
                        (fun uu___3 ->
                           (fun f1 ->
                              if
                                Prims.op_Negation
                                  ((has_attr f1
                                      (Fstarcompiler.FStarC_Reflection_V2_Builtins.pack_ln
                                         (Fstarcompiler.FStarC_Reflection_V2_Data.Tv_FVar
                                            (Fstarcompiler.FStarC_Reflection_V2_Builtins.pack_fv
                                               ["Meta";
                                               "Attribute";
                                               "specialize"]))))
                                     ||
                                     (has_attr f1
                                        (Fstarcompiler.FStarC_Reflection_V2_Builtins.pack_ln
                                           (Fstarcompiler.FStarC_Reflection_V2_Data.Tv_FVar
                                              (Fstarcompiler.FStarC_Reflection_V2_Builtins.pack_fv
                                                 ["Meta";
                                                 "Attribute";
                                                 "inline_"])))))
                              then
                                let uu___3 =
                                  let uu___4 =
                                    let uu___5 =
                                      let uu___6 = string_of_name f_name in
                                      FStar_Tactics_Effect.tac_bind
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Meta.Interface.fst"
                                                 (Prims.of_int (227))
                                                 (Prims.of_int (51))
                                                 (Prims.of_int (227))
                                                 (Prims.of_int (72)))))
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Prims.fst"
                                                 (Prims.of_int (611))
                                                 (Prims.of_int (19))
                                                 (Prims.of_int (611))
                                                 (Prims.of_int (31)))))
                                        (Obj.magic uu___6)
                                        (fun uu___7 ->
                                           FStar_Tactics_Effect.lift_div_tac
                                             (fun uu___8 ->
                                                Prims.strcat "Not visiting "
                                                  uu___7)) in
                                    FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Meta.Interface.fst"
                                               (Prims.of_int (227))
                                               (Prims.of_int (33))
                                               (Prims.of_int (227))
                                               (Prims.of_int (72)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range "Prims.fst"
                                               (Prims.of_int (611))
                                               (Prims.of_int (19))
                                               (Prims.of_int (611))
                                               (Prims.of_int (31)))))
                                      (Obj.magic uu___5)
                                      (fun uu___6 ->
                                         FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___7 ->
                                              Prims.strcat st.indent uu___6)) in
                                  FStar_Tactics_Effect.tac_bind
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "Meta.Interface.fst"
                                             (Prims.of_int (227))
                                             (Prims.of_int (20))
                                             (Prims.of_int (227))
                                             (Prims.of_int (73)))))
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "Meta.Interface.fst"
                                             (Prims.of_int (227))
                                             (Prims.of_int (14))
                                             (Prims.of_int (227))
                                             (Prims.of_int (73)))))
                                    (Obj.magic uu___4)
                                    (fun uu___5 ->
                                       (fun uu___5 ->
                                          Obj.magic
                                            (FStarC_Tactics_V1_Builtins.print
                                               uu___5)) uu___5) in
                                Obj.magic
                                  (FStar_Tactics_Effect.tac_bind
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "Meta.Interface.fst"
                                              (Prims.of_int (227))
                                              (Prims.of_int (14))
                                              (Prims.of_int (227))
                                              (Prims.of_int (73)))))
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "Meta.Interface.fst"
                                              (Prims.of_int (230))
                                              (Prims.of_int (6))
                                              (Prims.of_int (230))
                                              (Prims.of_int (12)))))
                                     (Obj.magic uu___3)
                                     (fun uu___4 ->
                                        FStar_Tactics_Effect.lift_div_tac
                                          (fun uu___5 -> (st, []))))
                              else
                                (let uu___4 =
                                   let uu___5 =
                                     let uu___6 =
                                       let uu___7 = string_of_name f_name in
                                       FStar_Tactics_Effect.tac_bind
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "Meta.Interface.fst"
                                                  (Prims.of_int (232))
                                                  (Prims.of_int (47))
                                                  (Prims.of_int (232))
                                                  (Prims.of_int (68)))))
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "Prims.fst"
                                                  (Prims.of_int (611))
                                                  (Prims.of_int (19))
                                                  (Prims.of_int (611))
                                                  (Prims.of_int (31)))))
                                         (Obj.magic uu___7)
                                         (fun uu___8 ->
                                            FStar_Tactics_Effect.lift_div_tac
                                              (fun uu___9 ->
                                                 Prims.strcat "Visiting "
                                                   uu___8)) in
                                     FStar_Tactics_Effect.tac_bind
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "Meta.Interface.fst"
                                                (Prims.of_int (232))
                                                (Prims.of_int (33))
                                                (Prims.of_int (232))
                                                (Prims.of_int (68)))))
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "Prims.fst"
                                                (Prims.of_int (611))
                                                (Prims.of_int (19))
                                                (Prims.of_int (611))
                                                (Prims.of_int (31)))))
                                       (Obj.magic uu___6)
                                       (fun uu___7 ->
                                          FStar_Tactics_Effect.lift_div_tac
                                            (fun uu___8 ->
                                               Prims.strcat st.indent uu___7)) in
                                   FStar_Tactics_Effect.tac_bind
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "Meta.Interface.fst"
                                              (Prims.of_int (232))
                                              (Prims.of_int (20))
                                              (Prims.of_int (232))
                                              (Prims.of_int (69)))))
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "Meta.Interface.fst"
                                              (Prims.of_int (232))
                                              (Prims.of_int (14))
                                              (Prims.of_int (232))
                                              (Prims.of_int (69)))))
                                     (Obj.magic uu___5)
                                     (fun uu___6 ->
                                        (fun uu___6 ->
                                           Obj.magic
                                             (FStarC_Tactics_V1_Builtins.print
                                                uu___6)) uu___6) in
                                 Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Meta.Interface.fst"
                                               (Prims.of_int (232))
                                               (Prims.of_int (14))
                                               (Prims.of_int (232))
                                               (Prims.of_int (69)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Meta.Interface.fst"
                                               (Prims.of_int (233))
                                               (Prims.of_int (6))
                                               (Prims.of_int (433))
                                               (Prims.of_int (18)))))
                                      (Obj.magic uu___4)
                                      (fun uu___5 ->
                                         (fun uu___5 ->
                                            match Fstarcompiler.FStarC_Reflection_V1_Builtins.inspect_sigelt
                                                    f1
                                            with
                                            | Fstarcompiler.FStarC_Reflection_V1_Data.Sg_Let
                                                (r, lbs) ->
                                                Obj.magic
                                                  (Obj.repr
                                                     (let uu___6 =
                                                        if r
                                                        then
                                                          Obj.magic
                                                            (Obj.repr
                                                               (let uu___7 =
                                                                  let uu___8
                                                                    =
                                                                    let uu___9
                                                                    =
                                                                    string_of_name
                                                                    f_name in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (236))
                                                                    (Prims.of_int (34))
                                                                    (Prims.of_int (236))
                                                                    (Prims.of_int (55)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___9)
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    Prims.strcat
                                                                    uu___10
                                                                    " is recursive")) in
                                                                  FStar_Tactics_Effect.tac_bind
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (236))
                                                                    (Prims.of_int (34))
                                                                    (Prims.of_int (236))
                                                                    (Prims.of_int (73)))))
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (
                                                                    Obj.magic
                                                                    uu___8)
                                                                    (
                                                                    fun
                                                                    uu___9 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    Prims.strcat
                                                                    "user error: "
                                                                    uu___9)) in
                                                                FStar_Tactics_Effect.tac_bind
                                                                  (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (236))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (236))
                                                                    (Prims.of_int (74)))))
                                                                  (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (236))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (236))
                                                                    (Prims.of_int (74)))))
                                                                  (Obj.magic
                                                                    uu___7)
                                                                  (fun uu___8
                                                                    ->
                                                                    FStar_Tactics_V1_Derived.fail
                                                                    uu___8)))
                                                        else
                                                          Obj.magic
                                                            (Obj.repr
                                                               (FStar_Tactics_Effect.lift_div_tac
                                                                  (fun uu___8
                                                                    -> ()))) in
                                                      FStar_Tactics_Effect.tac_bind
                                                        (FStar_Sealed.seal
                                                           (Obj.magic
                                                              (FStar_Range.mk_range
                                                                 "Meta.Interface.fst"
                                                                 (Prims.of_int (235))
                                                                 (Prims.of_int (8))
                                                                 (Prims.of_int (236))
                                                                 (Prims.of_int (74)))))
                                                        (FStar_Sealed.seal
                                                           (Obj.magic
                                                              (FStar_Range.mk_range
                                                                 "Meta.Interface.fst"
                                                                 (Prims.of_int (236))
                                                                 (Prims.of_int (75))
                                                                 (Prims.of_int (406))
                                                                 (Prims.of_int (11)))))
                                                        (Obj.magic uu___6)
                                                        (fun uu___7 ->
                                                           (fun uu___7 ->
                                                              let uu___8 =
                                                                FStar_Tactics_V1_SyntaxHelpers.lookup_lb_view
                                                                  lbs f_name in
                                                              Obj.magic
                                                                (FStar_Tactics_Effect.tac_bind
                                                                   (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (237))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (237))
                                                                    (Prims.of_int (43)))))
                                                                   (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (237))
                                                                    (Prims.of_int (46))
                                                                    (Prims.of_int (406))
                                                                    (Prims.of_int (11)))))
                                                                   (Obj.magic
                                                                    uu___8)
                                                                   (fun
                                                                    uu___9 ->
                                                                    (fun lbv
                                                                    ->
                                                                    let uu___9
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    lbv.Fstarcompiler.FStarC_Reflection_V1_Data.lb_def)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (238))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (238))
                                                                    (Prims.of_int (31)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (238))
                                                                    (Prims.of_int (34))
                                                                    (Prims.of_int (406))
                                                                    (Prims.of_int (11)))))
                                                                    (Obj.magic
                                                                    uu___9)
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun
                                                                    f_body ->
                                                                    let uu___10
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    lbv.Fstarcompiler.FStarC_Reflection_V1_Data.lb_typ)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (239))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (239))
                                                                    (Prims.of_int (30)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (239))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (406))
                                                                    (Prims.of_int (11)))))
                                                                    (Obj.magic
                                                                    uu___10)
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    (fun
                                                                    f_typ ->
                                                                    let uu___11
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    Fstarcompiler.FStarC_Reflection_V1_Builtins.sigelt_opts
                                                                    f1)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (240))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (240))
                                                                    (Prims.of_int (41)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (240))
                                                                    (Prims.of_int (44))
                                                                    (Prims.of_int (406))
                                                                    (Prims.of_int (11)))))
                                                                    (Obj.magic
                                                                    uu___11)
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    (fun
                                                                    original_opts
                                                                    ->
                                                                    let uu___12
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    st.indent)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (243))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (243))
                                                                    (Prims.of_int (34)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (243))
                                                                    (Prims.of_int (37))
                                                                    (Prims.of_int (406))
                                                                    (Prims.of_int (11)))))
                                                                    (Obj.magic
                                                                    uu___12)
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    (fun
                                                                    old_indent
                                                                    ->
                                                                    let uu___13
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    {
                                                                    seen =
                                                                    (st.seen);
                                                                    indent =
                                                                    (Prims.strcat
                                                                    st.indent
                                                                    "  ")
                                                                    })) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (244))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (244))
                                                                    (Prims.of_int (52)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (244))
                                                                    (Prims.of_int (57))
                                                                    (Prims.of_int (406))
                                                                    (Prims.of_int (11)))))
                                                                    (Obj.magic
                                                                    uu___13)
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    (fun st1
                                                                    ->
                                                                    let uu___14
                                                                    =
                                                                    suffix_name
                                                                    f_name
                                                                    "_higher" in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (245))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (245))
                                                                    (Prims.of_int (51)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (245))
                                                                    (Prims.of_int (54))
                                                                    (Prims.of_int (406))
                                                                    (Prims.of_int (11)))))
                                                                    (Obj.magic
                                                                    uu___14)
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    (fun
                                                                    new_name
                                                                    ->
                                                                    let uu___15
                                                                    =
                                                                    let uu___16
                                                                    =
                                                                    FStarC_Tactics_V1_Builtins.inspect
                                                                    f_body in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (250))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (250))
                                                                    (Prims.of_int (30)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (250))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (268))
                                                                    (Prims.of_int (76)))))
                                                                    (Obj.magic
                                                                    uu___16)
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    match uu___17
                                                                    with
                                                                    | 
                                                                    Fstarcompiler.FStarC_Reflection_V1_Data.Tv_Abs
                                                                    (binder,
                                                                    f_body')
                                                                    ->
                                                                    let uu___18
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___19
                                                                    ->
                                                                    Fstarcompiler.FStarC_Reflection_V1_Builtins.inspect_binder
                                                                    binder)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (252))
                                                                    (Prims.of_int (56))
                                                                    (Prims.of_int (252))
                                                                    (Prims.of_int (77)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (251))
                                                                    (Prims.of_int (36))
                                                                    (Prims.of_int (266))
                                                                    (Prims.of_int (32)))))
                                                                    (Obj.magic
                                                                    uu___18)
                                                                    (fun
                                                                    uu___19
                                                                    ->
                                                                    (fun
                                                                    uu___19
                                                                    ->
                                                                    match uu___19
                                                                    with
                                                                    | 
                                                                    {
                                                                    Fstarcompiler.FStarC_Reflection_V1_Data.binder_bv
                                                                    = bv;
                                                                    Fstarcompiler.FStarC_Reflection_V1_Data.binder_qual
                                                                    = uu___20;
                                                                    Fstarcompiler.FStarC_Reflection_V1_Data.binder_attrs
                                                                    = uu___21;
                                                                    Fstarcompiler.FStarC_Reflection_V1_Data.binder_sort
                                                                    = t;_} ->
                                                                    let uu___22
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___23
                                                                    ->
                                                                    Fstarcompiler.FStarC_Reflection_V1_Builtins.inspect_bv
                                                                    bv)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (253))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (253))
                                                                    (Prims.of_int (54)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (252))
                                                                    (Prims.of_int (80))
                                                                    (Prims.of_int (266))
                                                                    (Prims.of_int (32)))))
                                                                    (Obj.magic
                                                                    uu___22)
                                                                    (fun
                                                                    uu___23
                                                                    ->
                                                                    (fun
                                                                    uu___23
                                                                    ->
                                                                    match uu___23
                                                                    with
                                                                    | 
                                                                    {
                                                                    Fstarcompiler.FStarC_Reflection_V1_Data.bv_ppname
                                                                    = name;
                                                                    Fstarcompiler.FStarC_Reflection_V1_Data.bv_index
                                                                    = uu___24;_}
                                                                    ->
                                                                    let uu___25
                                                                    =
                                                                    FStarC_Tactics_Unseal.unseal
                                                                    name in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (254))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (254))
                                                                    (Prims.of_int (36)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (255))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (266))
                                                                    (Prims.of_int (32)))))
                                                                    (Obj.magic
                                                                    uu___25)
                                                                    (fun
                                                                    uu___26
                                                                    ->
                                                                    (fun
                                                                    name1 ->
                                                                    let uu___26
                                                                    =
                                                                    let uu___27
                                                                    =
                                                                    let uu___28
                                                                    =
                                                                    let uu___29
                                                                    =
                                                                    let uu___30
                                                                    =
                                                                    let uu___31
                                                                    =
                                                                    let uu___32
                                                                    =
                                                                    let uu___33
                                                                    =
                                                                    binder_is_legit
                                                                    f_name
                                                                    t_i
                                                                    binder in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (256))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (256))
                                                                    (Prims.of_int (53)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (256))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (256))
                                                                    (Prims.of_int (74)))))
                                                                    (Obj.magic
                                                                    uu___33)
                                                                    (fun
                                                                    uu___34
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___35
                                                                    ->
                                                                    if
                                                                    uu___34
                                                                    then ""
                                                                    else
                                                                    "NOT ")) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (256))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (256))
                                                                    (Prims.of_int (74)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (256))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (257))
                                                                    (Prims.of_int (54)))))
                                                                    (Obj.magic
                                                                    uu___32)
                                                                    (fun
                                                                    uu___33
                                                                    ->
                                                                    (fun
                                                                    uu___33
                                                                    ->
                                                                    let uu___34
                                                                    =
                                                                    let uu___35
                                                                    =
                                                                    FStarC_Tactics_V1_Builtins.term_to_string
                                                                    t in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (257))
                                                                    (Prims.of_int (38))
                                                                    (Prims.of_int (257))
                                                                    (Prims.of_int (54)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___35)
                                                                    (fun
                                                                    uu___36
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___37
                                                                    ->
                                                                    Prims.strcat
                                                                    "an index of type "
                                                                    uu___36)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (257))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (257))
                                                                    (Prims.of_int (54)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___34)
                                                                    (fun
                                                                    uu___35
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___36
                                                                    ->
                                                                    Prims.strcat
                                                                    uu___33
                                                                    uu___35))))
                                                                    uu___33) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (256))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (257))
                                                                    (Prims.of_int (54)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___31)
                                                                    (fun
                                                                    uu___32
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___33
                                                                    ->
                                                                    Prims.strcat
                                                                    ", which is "
                                                                    uu___32)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (255))
                                                                    (Prims.of_int (51))
                                                                    (Prims.of_int (257))
                                                                    (Prims.of_int (54)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___30)
                                                                    (fun
                                                                    uu___31
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___32
                                                                    ->
                                                                    Prims.strcat
                                                                    name1
                                                                    uu___31)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (255))
                                                                    (Prims.of_int (44))
                                                                    (Prims.of_int (257))
                                                                    (Prims.of_int (54)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___29)
                                                                    (fun
                                                                    uu___30
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___31
                                                                    ->
                                                                    Prims.strcat
                                                                    "Found "
                                                                    uu___30)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (255))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (257))
                                                                    (Prims.of_int (54)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___28)
                                                                    (fun
                                                                    uu___29
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___30
                                                                    ->
                                                                    Prims.strcat
                                                                    st1.indent
                                                                    uu___29)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (255))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (257))
                                                                    (Prims.of_int (55)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (255))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (257))
                                                                    (Prims.of_int (55)))))
                                                                    (Obj.magic
                                                                    uu___27)
                                                                    (fun
                                                                    uu___28
                                                                    ->
                                                                    (fun
                                                                    uu___28
                                                                    ->
                                                                    Obj.magic
                                                                    (FStarC_Tactics_V1_Builtins.print
                                                                    uu___28))
                                                                    uu___28) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (255))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (257))
                                                                    (Prims.of_int (55)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (258))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (266))
                                                                    (Prims.of_int (32)))))
                                                                    (Obj.magic
                                                                    uu___26)
                                                                    (fun
                                                                    uu___27
                                                                    ->
                                                                    (fun
                                                                    uu___27
                                                                    ->
                                                                    let uu___28
                                                                    =
                                                                    binder_is_legit
                                                                    f_name
                                                                    t_i
                                                                    binder in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (258))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (258))
                                                                    (Prims.of_int (50)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (258))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (266))
                                                                    (Prims.of_int (32)))))
                                                                    (Obj.magic
                                                                    uu___28)
                                                                    (fun
                                                                    uu___29
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___30
                                                                    ->
                                                                    if
                                                                    uu___29
                                                                    then
                                                                    ((FStar_Pervasives_Native.Some
                                                                    (bv, t)),
                                                                    name1,
                                                                    f_body')
                                                                    else
                                                                    (FStar_Pervasives_Native.None,
                                                                    "",
                                                                    f_body)))))
                                                                    uu___27)))
                                                                    uu___26)))
                                                                    uu___23)))
                                                                    uu___19))
                                                                    | 
                                                                    uu___18
                                                                    ->
                                                                    let uu___19
                                                                    =
                                                                    let uu___20
                                                                    =
                                                                    string_of_name
                                                                    f_name in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (268))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (268))
                                                                    (Prims.of_int (41)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___20)
                                                                    (fun
                                                                    uu___21
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___22
                                                                    ->
                                                                    Prims.strcat
                                                                    uu___21
                                                                    "is expected to be a function!")) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (268))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (268))
                                                                    (Prims.of_int (76)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (268))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (268))
                                                                    (Prims.of_int (76)))))
                                                                    (Obj.magic
                                                                    uu___19)
                                                                    (fun
                                                                    uu___20
                                                                    ->
                                                                    FStar_Tactics_V1_Derived.fail
                                                                    uu___20)))
                                                                    uu___17) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (250))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (268))
                                                                    (Prims.of_int (76)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (245))
                                                                    (Prims.of_int (54))
                                                                    (Prims.of_int (406))
                                                                    (Prims.of_int (11)))))
                                                                    (Obj.magic
                                                                    uu___15)
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    match uu___16
                                                                    with
                                                                    | 
                                                                    (index_bvty,
                                                                    index_name,
                                                                    f_body1)
                                                                    ->
                                                                    let uu___17
                                                                    =
                                                                    FStarC_Tactics_V1_Builtins.fresh_bv_named
                                                                    "p" in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (271))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (271))
                                                                    (Prims.of_int (43)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (271))
                                                                    (Prims.of_int (46))
                                                                    (Prims.of_int (406))
                                                                    (Prims.of_int (11)))))
                                                                    (Obj.magic
                                                                    uu___17)
                                                                    (fun
                                                                    uu___18
                                                                    ->
                                                                    (fun
                                                                    inv_bv ->
                                                                    let uu___18
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___19
                                                                    ->
                                                                    Fstarcompiler.FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (Fstarcompiler.FStarC_Reflection_V2_Data.Tv_Type
                                                                    (Fstarcompiler.FStarC_Reflection_V2_Builtins.pack_universe
                                                                    Fstarcompiler.FStarC_Reflection_V2_Data.Uv_Zero)))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (272))
                                                                    (Prims.of_int (32))
                                                                    (Prims.of_int (272))
                                                                    (Prims.of_int (38)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (272))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (406))
                                                                    (Prims.of_int (11)))))
                                                                    (Obj.magic
                                                                    uu___18)
                                                                    (fun
                                                                    uu___19
                                                                    ->
                                                                    (fun
                                                                    inv_bv_sort
                                                                    ->
                                                                    let uu___19
                                                                    =
                                                                    let uu___20
                                                                    =
                                                                    match index_bvty
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (index_bv,
                                                                    _sort) ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (let uu___21
                                                                    =
                                                                    FStarC_Tactics_V1_Builtins.pack
                                                                    (Fstarcompiler.FStarC_Reflection_V1_Data.Tv_Var
                                                                    index_bv) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (277))
                                                                    (Prims.of_int (45))
                                                                    (Prims.of_int (277))
                                                                    (Prims.of_int (69)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (277))
                                                                    (Prims.of_int (40))
                                                                    (Prims.of_int (277))
                                                                    (Prims.of_int (69)))))
                                                                    (Obj.magic
                                                                    uu___21)
                                                                    (fun
                                                                    uu___22
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___23
                                                                    ->
                                                                    FStar_Pervasives_Native.Some
                                                                    uu___22))))
                                                                    | 
                                                                    uu___21
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___22
                                                                    ->
                                                                    FStar_Pervasives_Native.None))) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (276))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (278))
                                                                    (Prims.of_int (23)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (280))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (280))
                                                                    (Prims.of_int (76)))))
                                                                    (Obj.magic
                                                                    uu___20)
                                                                    (fun
                                                                    uu___21
                                                                    ->
                                                                    (fun
                                                                    index_bv_tm_opt
                                                                    ->
                                                                    let uu___21
                                                                    =
                                                                    FStarC_Tactics_V1_Builtins.pack
                                                                    (Fstarcompiler.FStarC_Reflection_V1_Data.Tv_Var
                                                                    inv_bv) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (280))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (280))
                                                                    (Prims.of_int (63)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (280))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (280))
                                                                    (Prims.of_int (76)))))
                                                                    (Obj.magic
                                                                    uu___21)
                                                                    (fun
                                                                    uu___22
                                                                    ->
                                                                    (fun
                                                                    uu___22
                                                                    ->
                                                                    Obj.magic
                                                                    (visit_body
                                                                    t_i
                                                                    index_bv_tm_opt
                                                                    uu___22
                                                                    st1 []
                                                                    f_body1))
                                                                    uu___22)))
                                                                    uu___21) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (274))
                                                                    (Prims.of_int (49))
                                                                    (Prims.of_int (280))
                                                                    (Prims.of_int (76)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (272))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (406))
                                                                    (Prims.of_int (11)))))
                                                                    (Obj.magic
                                                                    uu___19)
                                                                    (fun
                                                                    uu___20
                                                                    ->
                                                                    (fun
                                                                    uu___20
                                                                    ->
                                                                    match uu___20
                                                                    with
                                                                    | 
                                                                    (st2,
                                                                    new_body,
                                                                    new_args,
                                                                    new_sigelts)
                                                                    ->
                                                                    let uu___21
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___22
                                                                    ->
                                                                    {
                                                                    seen =
                                                                    (st2.seen);
                                                                    indent =
                                                                    old_indent
                                                                    })) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (282))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (282))
                                                                    (Prims.of_int (46)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (282))
                                                                    (Prims.of_int (51))
                                                                    (Prims.of_int (406))
                                                                    (Prims.of_int (11)))))
                                                                    (Obj.magic
                                                                    uu___21)
                                                                    (fun
                                                                    uu___22
                                                                    ->
                                                                    (fun st3
                                                                    ->
                                                                    let uu___22
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___23
                                                                    ->
                                                                    if
                                                                    has_attr
                                                                    f1
                                                                    (Fstarcompiler.FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (Fstarcompiler.FStarC_Reflection_V2_Data.Tv_FVar
                                                                    (Fstarcompiler.FStarC_Reflection_V2_Builtins.pack_fv
                                                                    ["Meta";
                                                                    "Attribute";
                                                                    "specialize"])))
                                                                    then
                                                                    Specialize
                                                                    else
                                                                    Inline
                                                                    new_name)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (288))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (288))
                                                                    (Prims.of_int (95)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (288))
                                                                    (Prims.of_int (98))
                                                                    (Prims.of_int (406))
                                                                    (Prims.of_int (11)))))
                                                                    (Obj.magic
                                                                    uu___22)
                                                                    (fun
                                                                    uu___23
                                                                    ->
                                                                    (fun m ->
                                                                    let uu___23
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___24
                                                                    ->
                                                                    FStar_List_Tot_Base.split
                                                                    new_args)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (289))
                                                                    (Prims.of_int (32))
                                                                    (Prims.of_int (289))
                                                                    (Prims.of_int (55)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (288))
                                                                    (Prims.of_int (98))
                                                                    (Prims.of_int (406))
                                                                    (Prims.of_int (11)))))
                                                                    (Obj.magic
                                                                    uu___23)
                                                                    (fun
                                                                    uu___24
                                                                    ->
                                                                    (fun
                                                                    uu___24
                                                                    ->
                                                                    match uu___24
                                                                    with
                                                                    | 
                                                                    (new_args1,
                                                                    new_bvs)
                                                                    ->
                                                                    let uu___25
                                                                    =
                                                                    suffix_name
                                                                    f_name
                                                                    "_higher_t" in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (292))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (292))
                                                                    (Prims.of_int (55)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (292))
                                                                    (Prims.of_int (58))
                                                                    (Prims.of_int (406))
                                                                    (Prims.of_int (11)))))
                                                                    (Obj.magic
                                                                    uu___25)
                                                                    (fun
                                                                    uu___26
                                                                    ->
                                                                    (fun
                                                                    f_typ_name
                                                                    ->
                                                                    let uu___26
                                                                    =
                                                                    match index_bvty
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (index_bv,
                                                                    index_bv_sort)
                                                                    ->
                                                                    let uu___27
                                                                    =
                                                                    lambda_over_index_and_p
                                                                    st3
                                                                    f_name
                                                                    f_typ
                                                                    inv_bv
                                                                    inv_bv_sort in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (296))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (296))
                                                                    (Prims.of_int (72)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (296))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (299))
                                                                    (Prims.of_int (18)))))
                                                                    (Obj.magic
                                                                    uu___27)
                                                                    (fun
                                                                    uu___28
                                                                    ->
                                                                    (fun
                                                                    uu___28
                                                                    ->
                                                                    let uu___29
                                                                    =
                                                                    let uu___30
                                                                    =
                                                                    FStar_Tactics_V1_SyntaxHelpers.mk_tot_arr
                                                                    [
                                                                    FStar_Reflection_V1_Derived.mk_binder
                                                                    inv_bv
                                                                    inv_bv_sort]
                                                                    (Fstarcompiler.FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (Fstarcompiler.FStarC_Reflection_V2_Data.Tv_Type
                                                                    (Fstarcompiler.FStarC_Reflection_V2_Builtins.pack_universe
                                                                    Fstarcompiler.FStarC_Reflection_V2_Data.Uv_Zero))) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (297))
                                                                    (Prims.of_int (71))
                                                                    (Prims.of_int (298))
                                                                    (Prims.of_int (69)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (297))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (298))
                                                                    (Prims.of_int (69)))))
                                                                    (Obj.magic
                                                                    uu___30)
                                                                    (fun
                                                                    uu___31
                                                                    ->
                                                                    (fun
                                                                    uu___31
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_V1_SyntaxHelpers.mk_tot_arr
                                                                    [
                                                                    FStar_Reflection_V1_Derived.mk_implicit_binder
                                                                    index_bv
                                                                    index_bv_sort]
                                                                    uu___31))
                                                                    uu___31) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (297))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (298))
                                                                    (Prims.of_int (69)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (296))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (299))
                                                                    (Prims.of_int (18)))))
                                                                    (Obj.magic
                                                                    uu___29)
                                                                    (fun
                                                                    uu___30
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___31
                                                                    ->
                                                                    (uu___28,
                                                                    uu___30,
                                                                    true)))))
                                                                    uu___28)
                                                                    | 
                                                                    uu___27
                                                                    ->
                                                                    let uu___28
                                                                    =
                                                                    lambda_over_only_p
                                                                    st3
                                                                    inv_bv
                                                                    inv_bv_sort
                                                                    f_typ in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (301))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (301))
                                                                    (Prims.of_int (60)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (301))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (303))
                                                                    (Prims.of_int (19)))))
                                                                    (Obj.magic
                                                                    uu___28)
                                                                    (fun
                                                                    uu___29
                                                                    ->
                                                                    (fun
                                                                    uu___29
                                                                    ->
                                                                    let uu___30
                                                                    =
                                                                    FStar_Tactics_V1_SyntaxHelpers.mk_tot_arr
                                                                    [
                                                                    FStar_Reflection_V1_Derived.mk_binder
                                                                    inv_bv
                                                                    inv_bv_sort]
                                                                    (Fstarcompiler.FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (Fstarcompiler.FStarC_Reflection_V2_Data.Tv_Type
                                                                    (Fstarcompiler.FStarC_Reflection_V2_Builtins.pack_universe
                                                                    Fstarcompiler.FStarC_Reflection_V2_Data.Uv_Zero))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (302))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (302))
                                                                    (Prims.of_int (66)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (301))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (303))
                                                                    (Prims.of_int (19)))))
                                                                    (Obj.magic
                                                                    uu___30)
                                                                    (fun
                                                                    uu___31
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___32
                                                                    ->
                                                                    (uu___29,
                                                                    uu___31,
                                                                    false)))))
                                                                    uu___29) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (294))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (303))
                                                                    (Prims.of_int (19)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (292))
                                                                    (Prims.of_int (58))
                                                                    (Prims.of_int (406))
                                                                    (Prims.of_int (11)))))
                                                                    (Obj.magic
                                                                    uu___26)
                                                                    (fun
                                                                    uu___27
                                                                    ->
                                                                    (fun
                                                                    uu___27
                                                                    ->
                                                                    match uu___27
                                                                    with
                                                                    | 
                                                                    (f_typ1,
                                                                    f_typ_typ,
                                                                    has_index)
                                                                    ->
                                                                    let uu___28
                                                                    =
                                                                    let uu___29
                                                                    =
                                                                    let uu___30
                                                                    =
                                                                    let uu___31
                                                                    =
                                                                    let uu___32
                                                                    =
                                                                    string_of_name
                                                                    f_typ_name in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (305))
                                                                    (Prims.of_int (38))
                                                                    (Prims.of_int (305))
                                                                    (Prims.of_int (63)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (305))
                                                                    (Prims.of_int (38))
                                                                    (Prims.of_int (307))
                                                                    (Prims.of_int (30)))))
                                                                    (Obj.magic
                                                                    uu___32)
                                                                    (fun
                                                                    uu___33
                                                                    ->
                                                                    (fun
                                                                    uu___33
                                                                    ->
                                                                    let uu___34
                                                                    =
                                                                    let uu___35
                                                                    =
                                                                    let uu___36
                                                                    =
                                                                    FStarC_Tactics_V1_Builtins.term_to_string
                                                                    f_typ_typ in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (306))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (306))
                                                                    (Prims.of_int (34)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (306))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (307))
                                                                    (Prims.of_int (30)))))
                                                                    (Obj.magic
                                                                    uu___36)
                                                                    (fun
                                                                    uu___37
                                                                    ->
                                                                    (fun
                                                                    uu___37
                                                                    ->
                                                                    let uu___38
                                                                    =
                                                                    let uu___39
                                                                    =
                                                                    FStarC_Tactics_V1_Builtins.term_to_string
                                                                    f_typ1 in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (307))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (307))
                                                                    (Prims.of_int (30)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___39)
                                                                    (fun
                                                                    uu___40
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___41
                                                                    ->
                                                                    Prims.strcat
                                                                    " = "
                                                                    uu___40)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (306))
                                                                    (Prims.of_int (37))
                                                                    (Prims.of_int (307))
                                                                    (Prims.of_int (30)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___38)
                                                                    (fun
                                                                    uu___39
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___40
                                                                    ->
                                                                    Prims.strcat
                                                                    uu___37
                                                                    uu___39))))
                                                                    uu___37) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (306))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (307))
                                                                    (Prims.of_int (30)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___35)
                                                                    (fun
                                                                    uu___36
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___37
                                                                    ->
                                                                    Prims.strcat
                                                                    ": "
                                                                    uu___36)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (305))
                                                                    (Prims.of_int (66))
                                                                    (Prims.of_int (307))
                                                                    (Prims.of_int (30)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___34)
                                                                    (fun
                                                                    uu___35
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___36
                                                                    ->
                                                                    Prims.strcat
                                                                    uu___33
                                                                    uu___35))))
                                                                    uu___33) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (305))
                                                                    (Prims.of_int (38))
                                                                    (Prims.of_int (307))
                                                                    (Prims.of_int (30)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___31)
                                                                    (fun
                                                                    uu___32
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___33
                                                                    ->
                                                                    Prims.strcat
                                                                    "  let "
                                                                    uu___32)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (305))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (307))
                                                                    (Prims.of_int (30)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___30)
                                                                    (fun
                                                                    uu___31
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___32
                                                                    ->
                                                                    Prims.strcat
                                                                    st3.indent
                                                                    uu___31)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (305))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (307))
                                                                    (Prims.of_int (31)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (305))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (307))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___29)
                                                                    (fun
                                                                    uu___30
                                                                    ->
                                                                    (fun
                                                                    uu___30
                                                                    ->
                                                                    Obj.magic
                                                                    (FStarC_Tactics_V1_Builtins.print
                                                                    uu___30))
                                                                    uu___30) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (305))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (307))
                                                                    (Prims.of_int (31)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (307))
                                                                    (Prims.of_int (32))
                                                                    (Prims.of_int (406))
                                                                    (Prims.of_int (11)))))
                                                                    (Obj.magic
                                                                    uu___28)
                                                                    (fun
                                                                    uu___29
                                                                    ->
                                                                    (fun
                                                                    uu___29
                                                                    ->
                                                                    let uu___30
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___31
                                                                    ->
                                                                    Fstarcompiler.FStarC_Reflection_V1_Builtins.pack_lb
                                                                    {
                                                                    Fstarcompiler.FStarC_Reflection_V1_Data.lb_fv
                                                                    =
                                                                    (Fstarcompiler.FStarC_Reflection_V1_Builtins.pack_fv
                                                                    f_typ_name);
                                                                    Fstarcompiler.FStarC_Reflection_V1_Data.lb_us
                                                                    = [];
                                                                    Fstarcompiler.FStarC_Reflection_V1_Data.lb_typ
                                                                    =
                                                                    f_typ_typ;
                                                                    Fstarcompiler.FStarC_Reflection_V1_Data.lb_def
                                                                    = f_typ1
                                                                    })) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (308))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (311))
                                                                    (Prims.of_int (43)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (311))
                                                                    (Prims.of_int (46))
                                                                    (Prims.of_int (406))
                                                                    (Prims.of_int (11)))))
                                                                    (Obj.magic
                                                                    uu___30)
                                                                    (fun
                                                                    uu___31
                                                                    ->
                                                                    (fun lb
                                                                    ->
                                                                    let uu___31
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___32
                                                                    ->
                                                                    Fstarcompiler.FStarC_Reflection_V1_Builtins.pack_sigelt
                                                                    (Fstarcompiler.FStarC_Reflection_V1_Data.Sg_Let
                                                                    (false,
                                                                    [lb])))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (312))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (312))
                                                                    (Prims.of_int (50)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (312))
                                                                    (Prims.of_int (53))
                                                                    (Prims.of_int (406))
                                                                    (Prims.of_int (11)))))
                                                                    (Obj.magic
                                                                    uu___31)
                                                                    (fun
                                                                    uu___32
                                                                    ->
                                                                    (fun se_t
                                                                    ->
                                                                    let uu___32
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___33
                                                                    ->
                                                                    Fstarcompiler.FStarC_Reflection_V1_Builtins.set_sigelt_quals
                                                                    [Fstarcompiler.FStarC_Reflection_V1_Data.NoExtract;
                                                                    Fstarcompiler.FStarC_Reflection_V1_Data.Inline_for_extraction]
                                                                    se_t)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (313))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (313))
                                                                    (Prims.of_int (77)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (313))
                                                                    (Prims.of_int (80))
                                                                    (Prims.of_int (406))
                                                                    (Prims.of_int (11)))))
                                                                    (Obj.magic
                                                                    uu___32)
                                                                    (fun
                                                                    uu___33
                                                                    ->
                                                                    (fun
                                                                    se_t1 ->
                                                                    let uu___33
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___34
                                                                    ->
                                                                    match original_opts
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    original_opts1
                                                                    ->
                                                                    FStar_Reflection_V1_Derived.add_check_with
                                                                    original_opts1
                                                                    se_t1
                                                                    | 
                                                                    uu___35
                                                                    -> se_t1)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (314))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (316))
                                                                    (Prims.of_int (21)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (317))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (406))
                                                                    (Prims.of_int (11)))))
                                                                    (Obj.magic
                                                                    uu___33)
                                                                    (fun
                                                                    uu___34
                                                                    ->
                                                                    (fun
                                                                    se_t2 ->
                                                                    let uu___34
                                                                    =
                                                                    FStarC_Tactics_V1_Builtins.pack
                                                                    (Fstarcompiler.FStarC_Reflection_V1_Data.Tv_FVar
                                                                    (Fstarcompiler.FStarC_Reflection_V1_Builtins.pack_fv
                                                                    f_typ_name)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (318))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (318))
                                                                    (Prims.of_int (55)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (318))
                                                                    (Prims.of_int (58))
                                                                    (Prims.of_int (406))
                                                                    (Prims.of_int (11)))))
                                                                    (Obj.magic
                                                                    uu___34)
                                                                    (fun
                                                                    uu___35
                                                                    ->
                                                                    (fun
                                                                    f_typ2 ->
                                                                    let uu___35
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___36
                                                                    ->
                                                                    {
                                                                    seen =
                                                                    ((f_name,
                                                                    (has_index,
                                                                    f_typ2,
                                                                    m,
                                                                    new_args1))
                                                                    ::
                                                                    (st3.seen));
                                                                    indent =
                                                                    (st3.indent)
                                                                    })) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (319))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (319))
                                                                    (Prims.of_int (86)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (319))
                                                                    (Prims.of_int (91))
                                                                    (Prims.of_int (406))
                                                                    (Prims.of_int (11)))))
                                                                    (Obj.magic
                                                                    uu___35)
                                                                    (fun
                                                                    uu___36
                                                                    ->
                                                                    (fun st4
                                                                    ->
                                                                    let uu___36
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___37
                                                                    ->
                                                                    fun msg
                                                                    ->
                                                                    let uu___38
                                                                    =
                                                                    FStar_Tactics_Util.map
                                                                    string_of_name
                                                                    new_args1 in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (323))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (323))
                                                                    (Prims.of_int (48)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (323))
                                                                    (Prims.of_int (51))
                                                                    (Prims.of_int (343))
                                                                    (Prims.of_int (41)))))
                                                                    (Obj.magic
                                                                    uu___38)
                                                                    (fun
                                                                    uu___39
                                                                    ->
                                                                    (fun deps
                                                                    ->
                                                                    let uu___39
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___40
                                                                    ->
                                                                    match deps
                                                                    with
                                                                    | 
                                                                    uu___41::uu___42
                                                                    ->
                                                                    Prims.strcat
                                                                    " (needs: "
                                                                    (Prims.strcat
                                                                    (FStar_String.concat
                                                                    ", " deps)
                                                                    ")")
                                                                    | 
                                                                    uu___41
                                                                    -> "")) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (325))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (327))
                                                                    (Prims.of_int (21)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (328))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (343))
                                                                    (Prims.of_int (41)))))
                                                                    (Obj.magic
                                                                    uu___39)
                                                                    (fun
                                                                    uu___40
                                                                    ->
                                                                    (fun
                                                                    deps1 ->
                                                                    let uu___40
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___41
                                                                    ->
                                                                    fun s ->
                                                                    FStarC_Tactics_V1_Builtins.pack
                                                                    (Fstarcompiler.FStarC_Reflection_V1_Data.Tv_Const
                                                                    (Fstarcompiler.FStarC_Reflection_V1_Data.C_String
                                                                    s)))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (329))
                                                                    (Prims.of_int (42))
                                                                    (Prims.of_int (329))
                                                                    (Prims.of_int (70)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (329))
                                                                    (Prims.of_int (73))
                                                                    (Prims.of_int (343))
                                                                    (Prims.of_int (41)))))
                                                                    (Obj.magic
                                                                    uu___40)
                                                                    (fun
                                                                    uu___41
                                                                    ->
                                                                    (fun
                                                                    quote_string
                                                                    ->
                                                                    let uu___41
                                                                    =
                                                                    let uu___42
                                                                    =
                                                                    let uu___43
                                                                    =
                                                                    let uu___44
                                                                    =
                                                                    suffix_name
                                                                    f_name
                                                                    "_higher_debug_print" in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (331))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (331))
                                                                    (Prims.of_int (63)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (331))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (331))
                                                                    (Prims.of_int (63)))))
                                                                    (Obj.magic
                                                                    uu___44)
                                                                    (fun
                                                                    uu___45
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___46
                                                                    ->
                                                                    Fstarcompiler.FStarC_Reflection_V1_Builtins.pack_fv
                                                                    uu___45)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (331))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (331))
                                                                    (Prims.of_int (63)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (330))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (341))
                                                                    (Prims.of_int (19)))))
                                                                    (Obj.magic
                                                                    uu___43)
                                                                    (fun
                                                                    uu___44
                                                                    ->
                                                                    (fun
                                                                    uu___44
                                                                    ->
                                                                    let uu___45
                                                                    =
                                                                    let uu___46
                                                                    =
                                                                    quote_string
                                                                    deps1 in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (339))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (339))
                                                                    (Prims.of_int (44)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (335))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (341))
                                                                    (Prims.of_int (17)))))
                                                                    (Obj.magic
                                                                    uu___46)
                                                                    (fun
                                                                    uu___47
                                                                    ->
                                                                    (fun
                                                                    uu___47
                                                                    ->
                                                                    let uu___48
                                                                    =
                                                                    let uu___49
                                                                    =
                                                                    string_of_name
                                                                    new_name in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (338))
                                                                    (Prims.of_int (40))
                                                                    (Prims.of_int (338))
                                                                    (Prims.of_int (65)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (338))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (338))
                                                                    (Prims.of_int (66)))))
                                                                    (Obj.magic
                                                                    uu___49)
                                                                    (fun
                                                                    uu___50
                                                                    ->
                                                                    (fun
                                                                    uu___50
                                                                    ->
                                                                    Obj.magic
                                                                    (quote_string
                                                                    uu___50))
                                                                    uu___50) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (338))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (338))
                                                                    (Prims.of_int (66)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (335))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (341))
                                                                    (Prims.of_int (17)))))
                                                                    (Obj.magic
                                                                    uu___48)
                                                                    (fun
                                                                    uu___49
                                                                    ->
                                                                    (fun
                                                                    uu___49
                                                                    ->
                                                                    let uu___50
                                                                    =
                                                                    quote_string
                                                                    msg in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (337))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (337))
                                                                    (Prims.of_int (43)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (335))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (341))
                                                                    (Prims.of_int (17)))))
                                                                    (Obj.magic
                                                                    uu___50)
                                                                    (fun
                                                                    uu___51
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___52
                                                                    ->
                                                                    Fstarcompiler.FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (Fstarcompiler.FStarC_Reflection_V2_Data.Tv_Let
                                                                    (false,
                                                                    [],
                                                                    (Fstarcompiler.FStarC_Reflection_V2_Builtins.pack_binder
                                                                    {
                                                                    Fstarcompiler.FStarC_Reflection_V2_Data.sort2
                                                                    =
                                                                    (Fstarcompiler.FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (Fstarcompiler.FStarC_Reflection_V2_Data.Tv_FVar
                                                                    (Fstarcompiler.FStarC_Reflection_V2_Builtins.pack_fv
                                                                    ["Prims";
                                                                    "unit"])));
                                                                    Fstarcompiler.FStarC_Reflection_V2_Data.qual
                                                                    =
                                                                    Fstarcompiler.FStarC_Reflection_V2_Data.Q_Explicit;
                                                                    Fstarcompiler.FStarC_Reflection_V2_Data.attrs
                                                                    = [];
                                                                    Fstarcompiler.FStarC_Reflection_V2_Data.ppname2
                                                                    =
                                                                    (FStar_Sealed.seal
                                                                    "x")
                                                                    }),
                                                                    (Fstarcompiler.FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (Fstarcompiler.FStarC_Reflection_V2_Data.Tv_App
                                                                    ((Fstarcompiler.FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (Fstarcompiler.FStarC_Reflection_V2_Data.Tv_FVar
                                                                    (Fstarcompiler.FStarC_Reflection_V2_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "Effect";
                                                                    "synth_by_tactic"]))),
                                                                    ((Fstarcompiler.FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (Fstarcompiler.FStarC_Reflection_V2_Data.Tv_Abs
                                                                    ((Fstarcompiler.FStarC_Reflection_V2_Builtins.pack_binder
                                                                    {
                                                                    Fstarcompiler.FStarC_Reflection_V2_Data.sort2
                                                                    =
                                                                    (Fstarcompiler.FStarC_Reflection_V2_Builtins.pack_ln
                                                                    Fstarcompiler.FStarC_Reflection_V2_Data.Tv_Unknown);
                                                                    Fstarcompiler.FStarC_Reflection_V2_Data.qual
                                                                    =
                                                                    Fstarcompiler.FStarC_Reflection_V2_Data.Q_Explicit;
                                                                    Fstarcompiler.FStarC_Reflection_V2_Data.attrs
                                                                    = [];
                                                                    Fstarcompiler.FStarC_Reflection_V2_Data.ppname2
                                                                    =
                                                                    (FStar_Sealed.seal
                                                                    "uu___")
                                                                    }),
                                                                    (Fstarcompiler.FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (Fstarcompiler.FStarC_Reflection_V2_Data.Tv_Let
                                                                    (false,
                                                                    [],
                                                                    (Fstarcompiler.FStarC_Reflection_V2_Builtins.pack_binder
                                                                    {
                                                                    Fstarcompiler.FStarC_Reflection_V2_Data.sort2
                                                                    =
                                                                    (Fstarcompiler.FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (Fstarcompiler.FStarC_Reflection_V2_Data.Tv_FVar
                                                                    (Fstarcompiler.FStarC_Reflection_V2_Builtins.pack_fv
                                                                    ["Prims";
                                                                    "unit"])));
                                                                    Fstarcompiler.FStarC_Reflection_V2_Data.qual
                                                                    =
                                                                    Fstarcompiler.FStarC_Reflection_V2_Data.Q_Explicit;
                                                                    Fstarcompiler.FStarC_Reflection_V2_Data.attrs
                                                                    = [];
                                                                    Fstarcompiler.FStarC_Reflection_V2_Data.ppname2
                                                                    =
                                                                    (FStar_Sealed.seal
                                                                    "uu___")
                                                                    }),
                                                                    (Fstarcompiler.FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (Fstarcompiler.FStarC_Reflection_V2_Data.Tv_App
                                                                    ((Fstarcompiler.FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (Fstarcompiler.FStarC_Reflection_V2_Data.Tv_FVar
                                                                    (Fstarcompiler.FStarC_Reflection_V2_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Stubs";
                                                                    "Tactics";
                                                                    "V1";
                                                                    "Builtins";
                                                                    "print"]))),
                                                                    ((Fstarcompiler.FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (Fstarcompiler.FStarC_Reflection_V2_Data.Tv_App
                                                                    ((Fstarcompiler.FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (Fstarcompiler.FStarC_Reflection_V2_Data.Tv_App
                                                                    ((Fstarcompiler.FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (Fstarcompiler.FStarC_Reflection_V2_Data.Tv_FVar
                                                                    (Fstarcompiler.FStarC_Reflection_V2_Builtins.pack_fv
                                                                    ["Prims";
                                                                    "op_Hat"]))),
                                                                    (uu___51,
                                                                    Fstarcompiler.FStarC_Reflection_V2_Data.Q_Explicit)))),
                                                                    ((Fstarcompiler.FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (Fstarcompiler.FStarC_Reflection_V2_Data.Tv_App
                                                                    ((Fstarcompiler.FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (Fstarcompiler.FStarC_Reflection_V2_Data.Tv_App
                                                                    ((Fstarcompiler.FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (Fstarcompiler.FStarC_Reflection_V2_Data.Tv_FVar
                                                                    (Fstarcompiler.FStarC_Reflection_V2_Builtins.pack_fv
                                                                    ["Prims";
                                                                    "op_Hat"]))),
                                                                    ((Fstarcompiler.FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (Fstarcompiler.FStarC_Reflection_V2_Data.Tv_Const
                                                                    (Fstarcompiler.FStarC_Reflection_V2_Data.C_String
                                                                    " "))),
                                                                    Fstarcompiler.FStarC_Reflection_V2_Data.Q_Explicit)))),
                                                                    ((Fstarcompiler.FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (Fstarcompiler.FStarC_Reflection_V2_Data.Tv_App
                                                                    ((Fstarcompiler.FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (Fstarcompiler.FStarC_Reflection_V2_Data.Tv_App
                                                                    ((Fstarcompiler.FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (Fstarcompiler.FStarC_Reflection_V2_Data.Tv_FVar
                                                                    (Fstarcompiler.FStarC_Reflection_V2_Builtins.pack_fv
                                                                    ["Prims";
                                                                    "op_Hat"]))),
                                                                    (uu___49,
                                                                    Fstarcompiler.FStarC_Reflection_V2_Data.Q_Explicit)))),
                                                                    (uu___47,
                                                                    Fstarcompiler.FStarC_Reflection_V2_Data.Q_Explicit)))),
                                                                    Fstarcompiler.FStarC_Reflection_V2_Data.Q_Explicit)))),
                                                                    Fstarcompiler.FStarC_Reflection_V2_Data.Q_Explicit)))),
                                                                    Fstarcompiler.FStarC_Reflection_V2_Data.Q_Explicit)))),
                                                                    (Fstarcompiler.FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (Fstarcompiler.FStarC_Reflection_V2_Data.Tv_App
                                                                    ((Fstarcompiler.FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (Fstarcompiler.FStarC_Reflection_V2_Data.Tv_FVar
                                                                    (Fstarcompiler.FStarC_Reflection_V2_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "V1";
                                                                    "Derived";
                                                                    "exact"]))),
                                                                    ((Fstarcompiler.FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (Fstarcompiler.FStarC_Reflection_V2_Data.Tv_FVar
                                                                    (Fstarcompiler.FStarC_Reflection_V2_Builtins.pack_fv
                                                                    ["Meta";
                                                                    "Interface";
                                                                    "tm_unit"]))),
                                                                    Fstarcompiler.FStarC_Reflection_V2_Data.Q_Explicit)))))))))),
                                                                    Fstarcompiler.FStarC_Reflection_V2_Data.Q_Explicit)))),
                                                                    (Fstarcompiler.FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (Fstarcompiler.FStarC_Reflection_V2_Data.Tv_BVar
                                                                    (Fstarcompiler.FStarC_Reflection_V2_Builtins.pack_bv
                                                                    {
                                                                    Fstarcompiler.FStarC_Reflection_V2_Data.index
                                                                    =
                                                                    Fstarcompiler.Prims.int_zero;
                                                                    Fstarcompiler.FStarC_Reflection_V2_Data.sort1
                                                                    =
                                                                    (FStar_Sealed.seal
                                                                    (Fstarcompiler.FStarC_Reflection_V2_Builtins.pack_ln
                                                                    Fstarcompiler.FStarC_Reflection_V2_Data.Tv_Unknown));
                                                                    Fstarcompiler.FStarC_Reflection_V2_Data.ppname1
                                                                    =
                                                                    (FStar_Sealed.seal
                                                                    "x")
                                                                    })))))))))
                                                                    uu___49)))
                                                                    uu___47) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (335))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (341))
                                                                    (Prims.of_int (17)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (330))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (341))
                                                                    (Prims.of_int (19)))))
                                                                    (Obj.magic
                                                                    uu___45)
                                                                    (fun
                                                                    uu___46
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___47
                                                                    ->
                                                                    {
                                                                    Fstarcompiler.FStarC_Reflection_V1_Data.lb_fv
                                                                    = uu___44;
                                                                    Fstarcompiler.FStarC_Reflection_V1_Data.lb_us
                                                                    = [];
                                                                    Fstarcompiler.FStarC_Reflection_V1_Data.lb_typ
                                                                    =
                                                                    (Fstarcompiler.FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (Fstarcompiler.FStarC_Reflection_V2_Data.Tv_FVar
                                                                    (Fstarcompiler.FStarC_Reflection_V2_Builtins.pack_fv
                                                                    ["Prims";
                                                                    "unit"])));
                                                                    Fstarcompiler.FStarC_Reflection_V1_Data.lb_def
                                                                    = uu___46
                                                                    }))))
                                                                    uu___44) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (330))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (341))
                                                                    (Prims.of_int (19)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (330))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (341))
                                                                    (Prims.of_int (19)))))
                                                                    (Obj.magic
                                                                    uu___42)
                                                                    (fun
                                                                    uu___43
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___44
                                                                    ->
                                                                    Fstarcompiler.FStarC_Reflection_V1_Builtins.pack_lb
                                                                    uu___43)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (330))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (341))
                                                                    (Prims.of_int (19)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (343))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (343))
                                                                    (Prims.of_int (41)))))
                                                                    (Obj.magic
                                                                    uu___41)
                                                                    (fun lb1
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___42
                                                                    ->
                                                                    Fstarcompiler.FStarC_Reflection_V1_Builtins.pack_sigelt
                                                                    (Fstarcompiler.FStarC_Reflection_V1_Data.Sg_Let
                                                                    (false,
                                                                    [lb1]))))))
                                                                    uu___41)))
                                                                    uu___40)))
                                                                    uu___39))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (322))
                                                                    (Prims.of_int (38))
                                                                    (Prims.of_int (343))
                                                                    (Prims.of_int (41)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (358))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (406))
                                                                    (Prims.of_int (11)))))
                                                                    (Obj.magic
                                                                    uu___36)
                                                                    (fun
                                                                    uu___37
                                                                    ->
                                                                    (fun
                                                                    se_debug
                                                                    ->
                                                                    let uu___37
                                                                    =
                                                                    let uu___38
                                                                    =
                                                                    zip
                                                                    new_args1
                                                                    new_bvs in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (365))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (365))
                                                                    (Prims.of_int (36)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (363))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (365))
                                                                    (Prims.of_int (45)))))
                                                                    (Obj.magic
                                                                    uu___38)
                                                                    (fun
                                                                    uu___39
                                                                    ->
                                                                    (fun
                                                                    uu___39
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Util.fold_right
                                                                    (fun
                                                                    uu___40
                                                                    ->
                                                                    fun acc
                                                                    ->
                                                                    match uu___40
                                                                    with
                                                                    | 
                                                                    (uu___41,
                                                                    (bv,
                                                                    sort)) ->
                                                                    FStarC_Tactics_V1_Builtins.pack
                                                                    (Fstarcompiler.FStarC_Reflection_V1_Data.Tv_Abs
                                                                    ((FStar_Reflection_V1_Derived.mk_binder
                                                                    bv sort),
                                                                    acc)))
                                                                    uu___39
                                                                    new_body))
                                                                    uu___39) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (363))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (365))
                                                                    (Prims.of_int (45)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (366))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (406))
                                                                    (Prims.of_int (11)))))
                                                                    (Obj.magic
                                                                    uu___37)
                                                                    (fun
                                                                    uu___38
                                                                    ->
                                                                    (fun
                                                                    new_body1
                                                                    ->
                                                                    let uu___38
                                                                    =
                                                                    FStarC_Tactics_V1_Builtins.pack
                                                                    (Fstarcompiler.FStarC_Reflection_V1_Data.Tv_Abs
                                                                    ((FStar_Reflection_V1_Derived.mk_binder
                                                                    inv_bv
                                                                    inv_bv_sort),
                                                                    new_body1)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (371))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (371))
                                                                    (Prims.of_int (78)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (371))
                                                                    (Prims.of_int (81))
                                                                    (Prims.of_int (406))
                                                                    (Prims.of_int (11)))))
                                                                    (Obj.magic
                                                                    uu___38)
                                                                    (fun
                                                                    uu___39
                                                                    ->
                                                                    (fun
                                                                    new_body2
                                                                    ->
                                                                    let uu___39
                                                                    =
                                                                    match index_bvty
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (index_bv,
                                                                    index_bv_sort)
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStarC_Tactics_V1_Builtins.pack
                                                                    (Fstarcompiler.FStarC_Reflection_V1_Data.Tv_Abs
                                                                    ((FStar_Reflection_V1_Derived.mk_implicit_binder
                                                                    index_bv
                                                                    index_bv_sort),
                                                                    new_body2))))
                                                                    | 
                                                                    uu___40
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___41
                                                                    ->
                                                                    new_body2))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (373))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (375))
                                                                    (Prims.of_int (27)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (376))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (406))
                                                                    (Prims.of_int (11)))))
                                                                    (Obj.magic
                                                                    uu___39)
                                                                    (fun
                                                                    uu___40
                                                                    ->
                                                                    (fun
                                                                    new_body3
                                                                    ->
                                                                    let uu___40
                                                                    =
                                                                    let uu___41
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___42
                                                                    ->
                                                                    FStar_List_Tot_Base.map
                                                                    (fun
                                                                    uu___43
                                                                    ->
                                                                    match uu___43
                                                                    with
                                                                    | 
                                                                    (bv,
                                                                    sort) ->
                                                                    FStar_Reflection_V1_Derived.mk_binder
                                                                    bv sort)
                                                                    new_bvs)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (378))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (378))
                                                                    (Prims.of_int (88)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (378))
                                                                    (Prims.of_int (91))
                                                                    (Prims.of_int (387))
                                                                    (Prims.of_int (54)))))
                                                                    (Obj.magic
                                                                    uu___41)
                                                                    (fun
                                                                    uu___42
                                                                    ->
                                                                    (fun
                                                                    new_binders
                                                                    ->
                                                                    let uu___42
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___43
                                                                    ->
                                                                    (FStar_Reflection_V1_Derived.mk_binder
                                                                    inv_bv
                                                                    inv_bv_sort)
                                                                    ::
                                                                    new_binders)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (379))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (379))
                                                                    (Prims.of_int (73)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (379))
                                                                    (Prims.of_int (76))
                                                                    (Prims.of_int (387))
                                                                    (Prims.of_int (54)))))
                                                                    (Obj.magic
                                                                    uu___42)
                                                                    (fun
                                                                    uu___43
                                                                    ->
                                                                    (fun
                                                                    new_binders1
                                                                    ->
                                                                    let uu___43
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___44
                                                                    ->
                                                                    fun t ->
                                                                    let uu___45
                                                                    =
                                                                    let uu___46
                                                                    =
                                                                    let uu___47
                                                                    =
                                                                    FStarC_Tactics_V1_Builtins.pack
                                                                    (Fstarcompiler.FStarC_Reflection_V1_Data.Tv_Var
                                                                    inv_bv) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (380))
                                                                    (Prims.of_int (62))
                                                                    (Prims.of_int (380))
                                                                    (Prims.of_int (82)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (380))
                                                                    (Prims.of_int (61))
                                                                    (Prims.of_int (380))
                                                                    (Prims.of_int (95)))))
                                                                    (Obj.magic
                                                                    uu___47)
                                                                    (fun
                                                                    uu___48
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___49
                                                                    ->
                                                                    (uu___48,
                                                                    Fstarcompiler.FStarC_Reflection_V1_Data.Q_Explicit))) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (380))
                                                                    (Prims.of_int (61))
                                                                    (Prims.of_int (380))
                                                                    (Prims.of_int (95)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (380))
                                                                    (Prims.of_int (51))
                                                                    (Prims.of_int (380))
                                                                    (Prims.of_int (96)))))
                                                                    (Obj.magic
                                                                    uu___46)
                                                                    (fun
                                                                    uu___47
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___48
                                                                    ->
                                                                    Fstarcompiler.FStarC_Reflection_V1_Data.Tv_App
                                                                    (t,
                                                                    uu___47))) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (380))
                                                                    (Prims.of_int (51))
                                                                    (Prims.of_int (380))
                                                                    (Prims.of_int (96)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (380))
                                                                    (Prims.of_int (46))
                                                                    (Prims.of_int (380))
                                                                    (Prims.of_int (96)))))
                                                                    (Obj.magic
                                                                    uu___45)
                                                                    (fun
                                                                    uu___46
                                                                    ->
                                                                    (fun
                                                                    uu___46
                                                                    ->
                                                                    Obj.magic
                                                                    (FStarC_Tactics_V1_Builtins.pack
                                                                    uu___46))
                                                                    uu___46))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (380))
                                                                    (Prims.of_int (46))
                                                                    (Prims.of_int (380))
                                                                    (Prims.of_int (96)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (381))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (387))
                                                                    (Prims.of_int (54)))))
                                                                    (Obj.magic
                                                                    uu___43)
                                                                    (fun
                                                                    uu___44
                                                                    ->
                                                                    (fun
                                                                    app_inv
                                                                    ->
                                                                    match index_bvty
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (index_bv,
                                                                    index_bv_sort)
                                                                    ->
                                                                    let uu___44
                                                                    =
                                                                    let uu___45
                                                                    =
                                                                    let uu___46
                                                                    =
                                                                    let uu___47
                                                                    =
                                                                    let uu___48
                                                                    =
                                                                    FStarC_Tactics_V1_Builtins.pack
                                                                    (Fstarcompiler.FStarC_Reflection_V1_Data.Tv_Var
                                                                    index_bv) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (385))
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (385))
                                                                    (Prims.of_int (70)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (385))
                                                                    (Prims.of_int (47))
                                                                    (Prims.of_int (385))
                                                                    (Prims.of_int (83)))))
                                                                    (Obj.magic
                                                                    uu___48)
                                                                    (fun
                                                                    uu___49
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___50
                                                                    ->
                                                                    (uu___49,
                                                                    Fstarcompiler.FStarC_Reflection_V1_Data.Q_Implicit))) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (385))
                                                                    (Prims.of_int (47))
                                                                    (Prims.of_int (385))
                                                                    (Prims.of_int (83)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (385))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (385))
                                                                    (Prims.of_int (84)))))
                                                                    (Obj.magic
                                                                    uu___47)
                                                                    (fun
                                                                    uu___48
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___49
                                                                    ->
                                                                    Fstarcompiler.FStarC_Reflection_V1_Data.Tv_App
                                                                    (f_typ2,
                                                                    uu___48))) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (385))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (385))
                                                                    (Prims.of_int (84)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (385))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (385))
                                                                    (Prims.of_int (85)))))
                                                                    (Obj.magic
                                                                    uu___46)
                                                                    (fun
                                                                    uu___47
                                                                    ->
                                                                    (fun
                                                                    uu___47
                                                                    ->
                                                                    Obj.magic
                                                                    (FStarC_Tactics_V1_Builtins.pack
                                                                    uu___47))
                                                                    uu___47) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (385))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (385))
                                                                    (Prims.of_int (85)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (385))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (385))
                                                                    (Prims.of_int (86)))))
                                                                    (Obj.magic
                                                                    uu___45)
                                                                    (fun
                                                                    uu___46
                                                                    ->
                                                                    (fun
                                                                    uu___46
                                                                    ->
                                                                    Obj.magic
                                                                    (app_inv
                                                                    uu___46))
                                                                    uu___46) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (385))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (385))
                                                                    (Prims.of_int (86)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (383))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (385))
                                                                    (Prims.of_int (86)))))
                                                                    (Obj.magic
                                                                    uu___44)
                                                                    (fun
                                                                    uu___45
                                                                    ->
                                                                    (fun
                                                                    uu___45
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_V1_SyntaxHelpers.mk_tot_arr
                                                                    ((FStar_Reflection_V1_Derived.mk_implicit_binder
                                                                    index_bv
                                                                    index_bv_sort)
                                                                    ::
                                                                    new_binders1)
                                                                    uu___45))
                                                                    uu___45))
                                                                    | 
                                                                    uu___44
                                                                    ->
                                                                    let uu___45
                                                                    =
                                                                    app_inv
                                                                    f_typ2 in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (387))
                                                                    (Prims.of_int (39))
                                                                    (Prims.of_int (387))
                                                                    (Prims.of_int (54)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (387))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (387))
                                                                    (Prims.of_int (54)))))
                                                                    (Obj.magic
                                                                    uu___45)
                                                                    (fun
                                                                    uu___46
                                                                    ->
                                                                    (fun
                                                                    uu___46
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_V1_SyntaxHelpers.mk_tot_arr
                                                                    new_binders1
                                                                    uu___46))
                                                                    uu___46)))
                                                                    uu___44)))
                                                                    uu___43)))
                                                                    uu___42) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (377))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (387))
                                                                    (Prims.of_int (54)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (388))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (406))
                                                                    (Prims.of_int (11)))))
                                                                    (Obj.magic
                                                                    uu___40)
                                                                    (fun
                                                                    uu___41
                                                                    ->
                                                                    (fun
                                                                    new_typ
                                                                    ->
                                                                    let uu___41
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___42
                                                                    ->
                                                                    Fstarcompiler.FStarC_Reflection_V1_Builtins.pack_lb
                                                                    {
                                                                    Fstarcompiler.FStarC_Reflection_V1_Data.lb_fv
                                                                    =
                                                                    (Fstarcompiler.FStarC_Reflection_V1_Builtins.pack_fv
                                                                    new_name);
                                                                    Fstarcompiler.FStarC_Reflection_V1_Data.lb_us
                                                                    = [];
                                                                    Fstarcompiler.FStarC_Reflection_V1_Data.lb_typ
                                                                    = new_typ;
                                                                    Fstarcompiler.FStarC_Reflection_V1_Data.lb_def
                                                                    =
                                                                    new_body3
                                                                    })) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (389))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (392))
                                                                    (Prims.of_int (46)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (392))
                                                                    (Prims.of_int (49))
                                                                    (Prims.of_int (406))
                                                                    (Prims.of_int (11)))))
                                                                    (Obj.magic
                                                                    uu___41)
                                                                    (fun
                                                                    uu___42
                                                                    ->
                                                                    (fun lb1
                                                                    ->
                                                                    let uu___42
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___43
                                                                    ->
                                                                    Fstarcompiler.FStarC_Reflection_V1_Builtins.pack_sigelt
                                                                    (Fstarcompiler.FStarC_Reflection_V1_Data.Sg_Let
                                                                    (false,
                                                                    [lb1])))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (393))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (393))
                                                                    (Prims.of_int (50)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (393))
                                                                    (Prims.of_int (53))
                                                                    (Prims.of_int (406))
                                                                    (Prims.of_int (11)))))
                                                                    (Obj.magic
                                                                    uu___42)
                                                                    (fun
                                                                    uu___43
                                                                    ->
                                                                    (fun se
                                                                    ->
                                                                    let uu___43
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___44
                                                                    ->
                                                                    Fstarcompiler.FStarC_Reflection_V1_Builtins.set_sigelt_quals
                                                                    [Fstarcompiler.FStarC_Reflection_V1_Data.NoExtract;
                                                                    Fstarcompiler.FStarC_Reflection_V1_Data.Inline_for_extraction]
                                                                    se)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (394))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (394))
                                                                    (Prims.of_int (75)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (394))
                                                                    (Prims.of_int (78))
                                                                    (Prims.of_int (406))
                                                                    (Prims.of_int (11)))))
                                                                    (Obj.magic
                                                                    uu___43)
                                                                    (fun
                                                                    uu___44
                                                                    ->
                                                                    (fun se1
                                                                    ->
                                                                    let uu___44
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___45
                                                                    ->
                                                                    match original_opts
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    original_opts1
                                                                    ->
                                                                    FStar_Reflection_V1_Derived.add_check_with
                                                                    original_opts1
                                                                    se1
                                                                    | 
                                                                    uu___46
                                                                    -> se1)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (395))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (397))
                                                                    (Prims.of_int (21)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (399))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (406))
                                                                    (Prims.of_int (11)))))
                                                                    (Obj.magic
                                                                    uu___44)
                                                                    (fun
                                                                    uu___45
                                                                    ->
                                                                    (fun se2
                                                                    ->
                                                                    let uu___45
                                                                    =
                                                                    let uu___46
                                                                    =
                                                                    let uu___47
                                                                    =
                                                                    let uu___48
                                                                    =
                                                                    let uu___49
                                                                    =
                                                                    string_of_name
                                                                    new_name in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (399))
                                                                    (Prims.of_int (40))
                                                                    (Prims.of_int (399))
                                                                    (Prims.of_int (63)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (399))
                                                                    (Prims.of_int (40))
                                                                    (Prims.of_int (402))
                                                                    (Prims.of_int (47)))))
                                                                    (Obj.magic
                                                                    uu___49)
                                                                    (fun
                                                                    uu___50
                                                                    ->
                                                                    (fun
                                                                    uu___50
                                                                    ->
                                                                    let uu___51
                                                                    =
                                                                    let uu___52
                                                                    =
                                                                    let uu___53
                                                                    =
                                                                    let uu___54
                                                                    =
                                                                    FStarC_Tactics_V1_Builtins.term_to_string
                                                                    new_typ in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (400))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (400))
                                                                    (Prims.of_int (46)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (400))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (402))
                                                                    (Prims.of_int (47)))))
                                                                    (Obj.magic
                                                                    uu___54)
                                                                    (fun
                                                                    uu___55
                                                                    ->
                                                                    (fun
                                                                    uu___55
                                                                    ->
                                                                    let uu___56
                                                                    =
                                                                    let uu___57
                                                                    =
                                                                    let uu___58
                                                                    =
                                                                    let uu___59
                                                                    =
                                                                    let uu___60
                                                                    =
                                                                    FStarC_Tactics_V1_Builtins.term_to_string
                                                                    new_body3 in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (402))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (402))
                                                                    (Prims.of_int (47)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___60)
                                                                    (fun
                                                                    uu___61
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___62
                                                                    ->
                                                                    Prims.strcat
                                                                    st4.indent
                                                                    uu___61)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (402))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (402))
                                                                    (Prims.of_int (47)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___59)
                                                                    (fun
                                                                    uu___60
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___61
                                                                    ->
                                                                    Prims.strcat
                                                                    "=\n"
                                                                    uu___60)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (401))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (402))
                                                                    (Prims.of_int (47)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___58)
                                                                    (fun
                                                                    uu___59
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___60
                                                                    ->
                                                                    Prims.strcat
                                                                    st4.indent
                                                                    uu___59)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (401))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (402))
                                                                    (Prims.of_int (47)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___57)
                                                                    (fun
                                                                    uu___58
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___59
                                                                    ->
                                                                    Prims.strcat
                                                                    "\n"
                                                                    uu___58)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (400))
                                                                    (Prims.of_int (49))
                                                                    (Prims.of_int (402))
                                                                    (Prims.of_int (47)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___56)
                                                                    (fun
                                                                    uu___57
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___58
                                                                    ->
                                                                    Prims.strcat
                                                                    uu___55
                                                                    uu___57))))
                                                                    uu___55) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (400))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (402))
                                                                    (Prims.of_int (47)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___53)
                                                                    (fun
                                                                    uu___54
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___55
                                                                    ->
                                                                    Prims.strcat
                                                                    st4.indent
                                                                    uu___54)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (400))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (402))
                                                                    (Prims.of_int (47)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___52)
                                                                    (fun
                                                                    uu___53
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___54
                                                                    ->
                                                                    Prims.strcat
                                                                    ":\n"
                                                                    uu___53)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (399))
                                                                    (Prims.of_int (66))
                                                                    (Prims.of_int (402))
                                                                    (Prims.of_int (47)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___51)
                                                                    (fun
                                                                    uu___52
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___53
                                                                    ->
                                                                    Prims.strcat
                                                                    uu___50
                                                                    uu___52))))
                                                                    uu___50) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (399))
                                                                    (Prims.of_int (40))
                                                                    (Prims.of_int (402))
                                                                    (Prims.of_int (47)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___48)
                                                                    (fun
                                                                    uu___49
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___50
                                                                    ->
                                                                    Prims.strcat
                                                                    "  let "
                                                                    uu___49)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (399))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (402))
                                                                    (Prims.of_int (47)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___47)
                                                                    (fun
                                                                    uu___48
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___49
                                                                    ->
                                                                    Prims.strcat
                                                                    st4.indent
                                                                    uu___48)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (399))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (402))
                                                                    (Prims.of_int (48)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (399))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (402))
                                                                    (Prims.of_int (48)))))
                                                                    (Obj.magic
                                                                    uu___46)
                                                                    (fun
                                                                    uu___47
                                                                    ->
                                                                    (fun
                                                                    uu___47
                                                                    ->
                                                                    Obj.magic
                                                                    (FStarC_Tactics_V1_Builtins.print
                                                                    uu___47))
                                                                    uu___47) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (399))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (402))
                                                                    (Prims.of_int (48)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (404))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (406))
                                                                    (Prims.of_int (11)))))
                                                                    (Obj.magic
                                                                    uu___45)
                                                                    (fun
                                                                    uu___46
                                                                    ->
                                                                    (fun
                                                                    uu___46
                                                                    ->
                                                                    let uu___47
                                                                    =
                                                                    let uu___48
                                                                    =
                                                                    let uu___49
                                                                    =
                                                                    se_debug
                                                                    (Prims.strcat
                                                                    "Checking type and definition ["
                                                                    (Prims.strcat
                                                                    (string_of_mapping
                                                                    m) "]:")) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (405))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (405))
                                                                    (Prims.of_int (84)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (404))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (406))
                                                                    (Prims.of_int (11)))))
                                                                    (Obj.magic
                                                                    uu___49)
                                                                    (fun
                                                                    uu___50
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___51
                                                                    ->
                                                                    [uu___50;
                                                                    se_t2;
                                                                    se2])) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (404))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (406))
                                                                    (Prims.of_int (11)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (404))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (406))
                                                                    (Prims.of_int (11)))))
                                                                    (Obj.magic
                                                                    uu___48)
                                                                    (fun
                                                                    uu___49
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___50
                                                                    ->
                                                                    FStar_List_Tot_Base.op_At
                                                                    new_sigelts
                                                                    uu___49)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (404))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (406))
                                                                    (Prims.of_int (11)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (404))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (406))
                                                                    (Prims.of_int (11)))))
                                                                    (Obj.magic
                                                                    uu___47)
                                                                    (fun
                                                                    uu___48
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___49
                                                                    ->
                                                                    (st4,
                                                                    uu___48)))))
                                                                    uu___46)))
                                                                    uu___45)))
                                                                    uu___44)))
                                                                    uu___43)))
                                                                    uu___42)))
                                                                    uu___41)))
                                                                    uu___40)))
                                                                    uu___39)))
                                                                    uu___38)))
                                                                    uu___37)))
                                                                    uu___36)))
                                                                    uu___35)))
                                                                    uu___34)))
                                                                    uu___33)))
                                                                    uu___32)))
                                                                    uu___31)))
                                                                    uu___29)))
                                                                    uu___27)))
                                                                    uu___26)))
                                                                    uu___24)))
                                                                    uu___23)))
                                                                    uu___22)))
                                                                    uu___20)))
                                                                    uu___19)))
                                                                    uu___18)))
                                                                    uu___16)))
                                                                    uu___15)))
                                                                    uu___14)))
                                                                    uu___13)))
                                                                    uu___12)))
                                                                    uu___11)))
                                                                    uu___10)))
                                                                    uu___9)))
                                                             uu___7)))
                                            | uu___6 ->
                                                Obj.magic
                                                  (Obj.repr
                                                     (if
                                                        has_attr f1
                                                          (Fstarcompiler.FStarC_Reflection_V2_Builtins.pack_ln
                                                             (Fstarcompiler.FStarC_Reflection_V2_Data.Tv_FVar
                                                                (Fstarcompiler.FStarC_Reflection_V2_Builtins.pack_fv
                                                                   ["Meta";
                                                                   "Attribute";
                                                                   "specialize"])))
                                                      then
                                                        Obj.repr
                                                          (let uu___7 =
                                                             FStarC_Tactics_V1_Builtins.fresh_bv_named
                                                               "p" in
                                                           FStar_Tactics_Effect.tac_bind
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (410))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (410))
                                                                    (Prims.of_int (47)))))
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (410))
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (431))
                                                                    (Prims.of_int (18)))))
                                                             (Obj.magic
                                                                uu___7)
                                                             (fun uu___8 ->
                                                                (fun inv_bv
                                                                   ->
                                                                   let uu___8
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    Fstarcompiler.FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (Fstarcompiler.FStarC_Reflection_V2_Data.Tv_Type
                                                                    (Fstarcompiler.FStarC_Reflection_V2_Builtins.pack_universe
                                                                    Fstarcompiler.FStarC_Reflection_V2_Data.Uv_Zero)))) in
                                                                   Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (411))
                                                                    (Prims.of_int (36))
                                                                    (Prims.of_int (411))
                                                                    (Prims.of_int (42)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (411))
                                                                    (Prims.of_int (45))
                                                                    (Prims.of_int (431))
                                                                    (Prims.of_int (18)))))
                                                                    (Obj.magic
                                                                    uu___8)
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    inv_bv_sort
                                                                    ->
                                                                    let uu___9
                                                                    =
                                                                    FStarC_Tactics_V1_Builtins.pack
                                                                    (Fstarcompiler.FStarC_Reflection_V1_Data.Tv_FVar
                                                                    (Fstarcompiler.FStarC_Reflection_V1_Builtins.pack_fv
                                                                    f_name)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (414))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (414))
                                                                    (Prims.of_int (51)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (414))
                                                                    (Prims.of_int (54))
                                                                    (Prims.of_int (431))
                                                                    (Prims.of_int (18)))))
                                                                    (Obj.magic
                                                                    uu___9)
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun t ->
                                                                    let uu___10
                                                                    =
                                                                    let uu___11
                                                                    =
                                                                    FStarC_Tactics_V1_Builtins.top_env
                                                                    () in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (415))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (415))
                                                                    (Prims.of_int (39)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (415))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (415))
                                                                    (Prims.of_int (41)))))
                                                                    (Obj.magic
                                                                    uu___11)
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    Obj.magic
                                                                    (FStarC_Tactics_V1_Builtins.tc
                                                                    uu___12 t))
                                                                    uu___12) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (415))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (415))
                                                                    (Prims.of_int (41)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (416))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (431))
                                                                    (Prims.of_int (18)))))
                                                                    (Obj.magic
                                                                    uu___10)
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    (fun
                                                                    f_typ ->
                                                                    let uu___11
                                                                    =
                                                                    let uu___12
                                                                    =
                                                                    let uu___13
                                                                    =
                                                                    let uu___14
                                                                    =
                                                                    let uu___15
                                                                    =
                                                                    string_of_name
                                                                    f_name in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (416))
                                                                    (Prims.of_int (47))
                                                                    (Prims.of_int (416))
                                                                    (Prims.of_int (68)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (416))
                                                                    (Prims.of_int (47))
                                                                    (Prims.of_int (417))
                                                                    (Prims.of_int (50)))))
                                                                    (Obj.magic
                                                                    uu___15)
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    let uu___17
                                                                    =
                                                                    let uu___18
                                                                    =
                                                                    let uu___19
                                                                    =
                                                                    FStarC_Tactics_V1_Builtins.term_to_string
                                                                    f_typ in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (417))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (417))
                                                                    (Prims.of_int (34)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___19)
                                                                    (fun
                                                                    uu___20
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___21
                                                                    ->
                                                                    Prims.strcat
                                                                    uu___20
                                                                    " is a val\n")) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (417))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (417))
                                                                    (Prims.of_int (50)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___18)
                                                                    (fun
                                                                    uu___19
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___20
                                                                    ->
                                                                    Prims.strcat
                                                                    ": "
                                                                    uu___19)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (416))
                                                                    (Prims.of_int (71))
                                                                    (Prims.of_int (417))
                                                                    (Prims.of_int (50)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___17)
                                                                    (fun
                                                                    uu___18
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___19
                                                                    ->
                                                                    Prims.strcat
                                                                    uu___16
                                                                    uu___18))))
                                                                    uu___16) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (416))
                                                                    (Prims.of_int (47))
                                                                    (Prims.of_int (417))
                                                                    (Prims.of_int (50)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___14)
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    Prims.strcat
                                                                    "  Assuming "
                                                                    uu___15)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (416))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (417))
                                                                    (Prims.of_int (50)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___13)
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    Prims.strcat
                                                                    st.indent
                                                                    uu___14)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (416))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (417))
                                                                    (Prims.of_int (51)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (416))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (417))
                                                                    (Prims.of_int (51)))))
                                                                    (Obj.magic
                                                                    uu___12)
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    Obj.magic
                                                                    (FStarC_Tactics_V1_Builtins.print
                                                                    uu___13))
                                                                    uu___13) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (416))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (417))
                                                                    (Prims.of_int (51)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (417))
                                                                    (Prims.of_int (52))
                                                                    (Prims.of_int (431))
                                                                    (Prims.of_int (18)))))
                                                                    (Obj.magic
                                                                    uu___11)
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    let uu___13
                                                                    =
                                                                    let uu___14
                                                                    =
                                                                    FStarC_Tactics_V1_Builtins.inspect
                                                                    f_typ in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (419))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (419))
                                                                    (Prims.of_int (33)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (419))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (426))
                                                                    (Prims.of_int (71)))))
                                                                    (Obj.magic
                                                                    uu___14)
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    match uu___15
                                                                    with
                                                                    | 
                                                                    Fstarcompiler.FStarC_Reflection_V1_Data.Tv_Arrow
                                                                    (bv,
                                                                    uu___16)
                                                                    ->
                                                                    let uu___17
                                                                    =
                                                                    binder_is_legit
                                                                    f_name
                                                                    t_i bv in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (421))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (421))
                                                                    (Prims.of_int (50)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (421))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (424))
                                                                    (Prims.of_int (73)))))
                                                                    (Obj.magic
                                                                    uu___17)
                                                                    (fun
                                                                    uu___18
                                                                    ->
                                                                    (fun
                                                                    uu___18
                                                                    ->
                                                                    if
                                                                    uu___18
                                                                    then
                                                                    let uu___19
                                                                    =
                                                                    lambda_over_index_and_p
                                                                    st f_name
                                                                    f_typ
                                                                    inv_bv
                                                                    inv_bv_sort in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (422))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (422))
                                                                    (Prims.of_int (78)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (422))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (422))
                                                                    (Prims.of_int (84)))))
                                                                    (Obj.magic
                                                                    uu___19)
                                                                    (fun
                                                                    uu___20
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___21
                                                                    ->
                                                                    (uu___20,
                                                                    true))))
                                                                    else
                                                                    (let uu___20
                                                                    =
                                                                    lambda_over_only_p
                                                                    st inv_bv
                                                                    inv_bv_sort
                                                                    f_typ in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (424))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (424))
                                                                    (Prims.of_int (66)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (424))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (424))
                                                                    (Prims.of_int (73)))))
                                                                    (Obj.magic
                                                                    uu___20)
                                                                    (fun
                                                                    uu___21
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___22
                                                                    ->
                                                                    (uu___21,
                                                                    false))))))
                                                                    uu___18))
                                                                    | 
                                                                    uu___16
                                                                    ->
                                                                    let uu___17
                                                                    =
                                                                    lambda_over_only_p
                                                                    st inv_bv
                                                                    inv_bv_sort
                                                                    f_typ in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (426))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (426))
                                                                    (Prims.of_int (64)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (426))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (426))
                                                                    (Prims.of_int (71)))))
                                                                    (Obj.magic
                                                                    uu___17)
                                                                    (fun
                                                                    uu___18
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___19
                                                                    ->
                                                                    (uu___18,
                                                                    false)))))
                                                                    uu___15) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (419))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (426))
                                                                    (Prims.of_int (71)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (417))
                                                                    (Prims.of_int (52))
                                                                    (Prims.of_int (431))
                                                                    (Prims.of_int (18)))))
                                                                    (Obj.magic
                                                                    uu___13)
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    match uu___14
                                                                    with
                                                                    | 
                                                                    (f_typ1,
                                                                    has_index)
                                                                    ->
                                                                    let uu___15
                                                                    =
                                                                    let uu___16
                                                                    =
                                                                    let uu___17
                                                                    =
                                                                    let uu___18
                                                                    =
                                                                    let uu___19
                                                                    =
                                                                    string_of_name
                                                                    f_name in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (428))
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (428))
                                                                    (Prims.of_int (71)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (428))
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (429))
                                                                    (Prims.of_int (34)))))
                                                                    (Obj.magic
                                                                    uu___19)
                                                                    (fun
                                                                    uu___20
                                                                    ->
                                                                    (fun
                                                                    uu___20
                                                                    ->
                                                                    let uu___21
                                                                    =
                                                                    let uu___22
                                                                    =
                                                                    FStarC_Tactics_V1_Builtins.term_to_string
                                                                    f_typ1 in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (429))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (429))
                                                                    (Prims.of_int (34)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___22)
                                                                    (fun
                                                                    uu___23
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___24
                                                                    ->
                                                                    Prims.strcat
                                                                    " with type "
                                                                    uu___23)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (428))
                                                                    (Prims.of_int (74))
                                                                    (Prims.of_int (429))
                                                                    (Prims.of_int (34)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___21)
                                                                    (fun
                                                                    uu___22
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___23
                                                                    ->
                                                                    Prims.strcat
                                                                    uu___20
                                                                    uu___22))))
                                                                    uu___20) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (428))
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (429))
                                                                    (Prims.of_int (34)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___18)
                                                                    (fun
                                                                    uu___19
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___20
                                                                    ->
                                                                    Prims.strcat
                                                                    "  Registering "
                                                                    uu___19)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (428))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (429))
                                                                    (Prims.of_int (34)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___17)
                                                                    (fun
                                                                    uu___18
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___19
                                                                    ->
                                                                    Prims.strcat
                                                                    st.indent
                                                                    uu___18)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (428))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (429))
                                                                    (Prims.of_int (35)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (428))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (429))
                                                                    (Prims.of_int (35)))))
                                                                    (Obj.magic
                                                                    uu___16)
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    Obj.magic
                                                                    (FStarC_Tactics_V1_Builtins.print
                                                                    uu___17))
                                                                    uu___17) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (428))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (429))
                                                                    (Prims.of_int (35)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (431))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (431))
                                                                    (Prims.of_int (18)))))
                                                                    (Obj.magic
                                                                    uu___15)
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    ({
                                                                    seen =
                                                                    ((f_name,
                                                                    (has_index,
                                                                    f_typ1,
                                                                    Specialize,
                                                                    [])) ::
                                                                    (st.seen));
                                                                    indent =
                                                                    (st.indent)
                                                                    }, [])))))
                                                                    uu___14)))
                                                                    uu___12)))
                                                                    uu___11)))
                                                                    uu___10)))
                                                                    uu___9)))
                                                                  uu___8))
                                                      else
                                                        Obj.repr
                                                          (FStar_Tactics_Effect.lift_div_tac
                                                             (fun uu___8 ->
                                                                (st, []))))))
                                           uu___5)))) uu___3))) uu___2))
and (visit_many :
  Fstarcompiler.FStarC_Reflection_Types.term ->
    Fstarcompiler.FStarC_Reflection_Types.term FStar_Pervasives_Native.option
      ->
      Fstarcompiler.FStarC_Reflection_Types.term ->
        state ->
          (Fstarcompiler.FStarC_Reflection_Types.name *
            (Fstarcompiler.FStarC_Reflection_Types.bv *
            Fstarcompiler.FStarC_Reflection_Types.typ)) Prims.list ->
            Fstarcompiler.FStarC_Reflection_Types.term Prims.list ->
              ((state * Fstarcompiler.FStarC_Reflection_Types.term Prims.list
                 * (Fstarcompiler.FStarC_Reflection_Types.name *
                 (Fstarcompiler.FStarC_Reflection_Types.bv *
                 Fstarcompiler.FStarC_Reflection_Types.typ)) Prims.list *
                 Fstarcompiler.FStarC_Reflection_Types.sigelt Prims.list),
                unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t_i ->
    fun index_bv ->
      fun inv_bv ->
        fun st ->
          fun bvs ->
            fun es ->
              let uu___ =
                FStar_Tactics_Util.fold_left
                  (fun uu___1 ->
                     fun e ->
                       match uu___1 with
                       | (st1, es1, bvs1, ses) ->
                           let uu___2 =
                             visit_body t_i index_bv inv_bv st1 bvs1 e in
                           FStar_Tactics_Effect.tac_bind
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range "Meta.Interface.fst"
                                      (Prims.of_int (444))
                                      (Prims.of_int (27))
                                      (Prims.of_int (444))
                                      (Prims.of_int (66)))))
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range "Meta.Interface.fst"
                                      (Prims.of_int (443))
                                      (Prims.of_int (63))
                                      (Prims.of_int (445))
                                      (Prims.of_int (32)))))
                             (Obj.magic uu___2)
                             (fun uu___3 ->
                                FStar_Tactics_Effect.lift_div_tac
                                  (fun uu___4 ->
                                     match uu___3 with
                                     | (st2, e1, bvs2, ses') ->
                                         (st2, (e1 :: es1), bvs2,
                                           (FStar_List_Tot_Base.op_At ses
                                              ses'))))) (st, [], bvs, []) es in
              FStar_Tactics_Effect.tac_bind
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Meta.Interface.fst"
                         (Prims.of_int (443)) (Prims.of_int (25))
                         (Prims.of_int (446)) (Prims.of_int (24)))))
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Meta.Interface.fst"
                         (Prims.of_int (442)) Fstarcompiler.Prims.int_one
                         (Prims.of_int (448)) (Prims.of_int (18)))))
                (Obj.magic uu___)
                (fun uu___1 ->
                   FStar_Tactics_Effect.lift_div_tac
                     (fun uu___2 ->
                        match uu___1 with
                        | (st1, es1, bvs1, ses) ->
                            (st1, (FStar_List_Tot_Base.rev es1), bvs1, ses)))
and (visit_body :
  Fstarcompiler.FStarC_Reflection_Types.term ->
    Fstarcompiler.FStarC_Reflection_Types.term FStar_Pervasives_Native.option
      ->
      Fstarcompiler.FStarC_Reflection_Types.term ->
        state ->
          (Fstarcompiler.FStarC_Reflection_Types.name *
            (Fstarcompiler.FStarC_Reflection_Types.bv *
            Fstarcompiler.FStarC_Reflection_Types.typ)) Prims.list ->
            Fstarcompiler.FStarC_Reflection_Types.term ->
              ((state * Fstarcompiler.FStarC_Reflection_Types.term *
                 (Fstarcompiler.FStarC_Reflection_Types.name *
                 (Fstarcompiler.FStarC_Reflection_Types.bv *
                 Fstarcompiler.FStarC_Reflection_Types.typ)) Prims.list *
                 Fstarcompiler.FStarC_Reflection_Types.sigelt Prims.list),
                unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t_i ->
    fun index_bv ->
      fun inv_bv ->
        fun st ->
          fun bvs ->
            fun e ->
              let uu___ = FStarC_Tactics_V1_Builtins.inspect e in
              FStar_Tactics_Effect.tac_bind
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Meta.Interface.fst"
                         (Prims.of_int (462)) (Prims.of_int (8))
                         (Prims.of_int (462)) (Prims.of_int (17)))))
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Meta.Interface.fst"
                         (Prims.of_int (462)) (Prims.of_int (2))
                         (Prims.of_int (602)) (Prims.of_int (20)))))
                (Obj.magic uu___)
                (fun uu___1 ->
                   (fun uu___1 ->
                      match uu___1 with
                      | Fstarcompiler.FStarC_Reflection_V1_Data.Tv_App
                          (uu___2, uu___3) ->
                          Obj.magic
                            (Obj.repr
                               (let uu___4 =
                                  FStar_Tactics_V1_SyntaxHelpers.collect_app
                                    e in
                                FStar_Tactics_Effect.tac_bind
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Meta.Interface.fst"
                                           (Prims.of_int (464))
                                           (Prims.of_int (18))
                                           (Prims.of_int (464))
                                           (Prims.of_int (31)))))
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Meta.Interface.fst"
                                           (Prims.of_int (463))
                                           (Prims.of_int (17))
                                           (Prims.of_int (559))
                                           (Prims.of_int (9)))))
                                  (Obj.magic uu___4)
                                  (fun uu___5 ->
                                     (fun uu___5 ->
                                        match uu___5 with
                                        | (e1, es) ->
                                            let uu___6 =
                                              Obj.magic
                                                (FStar_Tactics_Effect.lift_div_tac
                                                   (fun uu___7 ->
                                                      FStar_List_Tot_Base.split
                                                        es)) in
                                            Obj.magic
                                              (FStar_Tactics_Effect.tac_bind
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Meta.Interface.fst"
                                                          (Prims.of_int (467))
                                                          (Prims.of_int (19))
                                                          (Prims.of_int (467))
                                                          (Prims.of_int (37)))))
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Meta.Interface.fst"
                                                          (Prims.of_int (464))
                                                          (Prims.of_int (34))
                                                          (Prims.of_int (559))
                                                          (Prims.of_int (9)))))
                                                 (Obj.magic uu___6)
                                                 (fun uu___7 ->
                                                    (fun uu___7 ->
                                                       match uu___7 with
                                                       | (es1, qs) ->
                                                           let uu___8 =
                                                             visit_many t_i
                                                               index_bv
                                                               inv_bv st bvs
                                                               es1 in
                                                           Obj.magic
                                                             (FStar_Tactics_Effect.tac_bind
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (468))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (468))
                                                                    (Prims.of_int (69)))))
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (467))
                                                                    (Prims.of_int (40))
                                                                    (Prims.of_int (559))
                                                                    (Prims.of_int (9)))))
                                                                (Obj.magic
                                                                   uu___8)
                                                                (fun uu___9
                                                                   ->
                                                                   (fun
                                                                    uu___9 ->
                                                                    match uu___9
                                                                    with
                                                                    | 
                                                                    (st1,
                                                                    es2,
                                                                    bvs1,
                                                                    ses) ->
                                                                    let uu___10
                                                                    =
                                                                    zip es2
                                                                    qs in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (469))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (469))
                                                                    (Prims.of_int (24)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (472))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (558))
                                                                    (Prims.of_int (25)))))
                                                                    (Obj.magic
                                                                    uu___10)
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    (fun es3
                                                                    ->
                                                                    let uu___11
                                                                    =
                                                                    FStarC_Tactics_V1_Builtins.inspect
                                                                    e1 in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (472))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (472))
                                                                    (Prims.of_int (27)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (472))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (558))
                                                                    (Prims.of_int (25)))))
                                                                    (Obj.magic
                                                                    uu___11)
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    match uu___12
                                                                    with
                                                                    | 
                                                                    Fstarcompiler.FStarC_Reflection_V1_Data.Tv_UInst
                                                                    (fv,
                                                                    uu___13)
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (let uu___14
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    Fstarcompiler.FStarC_Reflection_V1_Builtins.inspect_fv
                                                                    fv)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (476))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (476))
                                                                    (Prims.of_int (32)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (476))
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (555))
                                                                    (Prims.of_int (13)))))
                                                                    (Obj.magic
                                                                    uu___14)
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    (fun fv1
                                                                    ->
                                                                    let uu___15
                                                                    =
                                                                    visit_function
                                                                    t_i st1
                                                                    fv1 in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (477))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (477))
                                                                    (Prims.of_int (49)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (476))
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (555))
                                                                    (Prims.of_int (13)))))
                                                                    (Obj.magic
                                                                    uu___15)
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    match uu___16
                                                                    with
                                                                    | 
                                                                    (st2,
                                                                    ses') ->
                                                                    let uu___17
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___18
                                                                    ->
                                                                    FStar_List_Tot_Base.op_At
                                                                    ses ses')) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (478))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (478))
                                                                    (Prims.of_int (30)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (481))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (554))
                                                                    (Prims.of_int (29)))))
                                                                    (Obj.magic
                                                                    uu___17)
                                                                    (fun
                                                                    uu___18
                                                                    ->
                                                                    (fun ses1
                                                                    ->
                                                                    match 
                                                                    FStar_List_Tot_Base.assoc
                                                                    fv1
                                                                    st2.seen
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (has_index,
                                                                    uu___18,
                                                                    map, fns)
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (let uu___19
                                                                    =
                                                                    let uu___20
                                                                    =
                                                                    let uu___21
                                                                    =
                                                                    let uu___22
                                                                    =
                                                                    string_of_name
                                                                    fv1 in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (483))
                                                                    (Prims.of_int (63))
                                                                    (Prims.of_int (483))
                                                                    (Prims.of_int (80)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___22)
                                                                    (fun
                                                                    uu___23
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___24
                                                                    ->
                                                                    Prims.strcat
                                                                    "Rewriting application of "
                                                                    uu___23)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (483))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (483))
                                                                    (Prims.of_int (80)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___21)
                                                                    (fun
                                                                    uu___22
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___23
                                                                    ->
                                                                    Prims.strcat
                                                                    st2.indent
                                                                    uu___22)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (483))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (483))
                                                                    (Prims.of_int (81)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (483))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (483))
                                                                    (Prims.of_int (81)))))
                                                                    (Obj.magic
                                                                    uu___20)
                                                                    (fun
                                                                    uu___21
                                                                    ->
                                                                    (fun
                                                                    uu___21
                                                                    ->
                                                                    Obj.magic
                                                                    (FStarC_Tactics_V1_Builtins.print
                                                                    uu___21))
                                                                    uu___21) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (483))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (483))
                                                                    (Prims.of_int (81)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (483))
                                                                    (Prims.of_int (82))
                                                                    (Prims.of_int (550))
                                                                    (Prims.of_int (17)))))
                                                                    (Obj.magic
                                                                    uu___19)
                                                                    (fun
                                                                    uu___20
                                                                    ->
                                                                    (fun
                                                                    uu___20
                                                                    ->
                                                                    let uu___21
                                                                    =
                                                                    if
                                                                    has_index
                                                                    then
                                                                    match es3
                                                                    with
                                                                    | 
                                                                    (e2,
                                                                    Fstarcompiler.FStarC_Reflection_V1_Data.Q_Implicit)::es4
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___22
                                                                    ->
                                                                    ((FStar_Pervasives_Native.Some
                                                                    e2), es4)))
                                                                    | 
                                                                    uu___22
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_V1_Derived.fail
                                                                    "this application does not seem to start with an index")
                                                                    else
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___23
                                                                    ->
                                                                    (FStar_Pervasives_Native.None,
                                                                    es3))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (486))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (493))
                                                                    (Prims.of_int (26)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (483))
                                                                    (Prims.of_int (82))
                                                                    (Prims.of_int (550))
                                                                    (Prims.of_int (17)))))
                                                                    (Obj.magic
                                                                    uu___21)
                                                                    (fun
                                                                    uu___22
                                                                    ->
                                                                    (fun
                                                                    uu___22
                                                                    ->
                                                                    match uu___22
                                                                    with
                                                                    | 
                                                                    (index_arg,
                                                                    es4) ->
                                                                    let uu___23
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___24
                                                                    ->
                                                                    fun name
                                                                    ->
                                                                    fun bvs2
                                                                    ->
                                                                    match 
                                                                    FStar_List_Tot_Base.assoc
                                                                    name bvs2
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (bv,
                                                                    sort) ->
                                                                    let uu___25
                                                                    =
                                                                    let uu___26
                                                                    =
                                                                    let uu___27
                                                                    =
                                                                    let uu___28
                                                                    =
                                                                    string_of_name
                                                                    name in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (502))
                                                                    (Prims.of_int (39))
                                                                    (Prims.of_int (502))
                                                                    (Prims.of_int (58)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___28)
                                                                    (fun
                                                                    uu___29
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___30
                                                                    ->
                                                                    Prims.strcat
                                                                    uu___29
                                                                    " already has a bv")) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (502))
                                                                    (Prims.of_int (39))
                                                                    (Prims.of_int (502))
                                                                    (Prims.of_int (80)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___27)
                                                                    (fun
                                                                    uu___28
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___29
                                                                    ->
                                                                    Prims.strcat
                                                                    st2.indent
                                                                    uu___28)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (502))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (502))
                                                                    (Prims.of_int (81)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (502))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (502))
                                                                    (Prims.of_int (81)))))
                                                                    (Obj.magic
                                                                    uu___26)
                                                                    (fun
                                                                    uu___27
                                                                    ->
                                                                    (fun
                                                                    uu___27
                                                                    ->
                                                                    Obj.magic
                                                                    (FStarC_Tactics_V1_Builtins.print
                                                                    uu___27))
                                                                    uu___27) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (502))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (502))
                                                                    (Prims.of_int (81)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (505))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (505))
                                                                    (Prims.of_int (55)))))
                                                                    (Obj.magic
                                                                    uu___25)
                                                                    (fun
                                                                    uu___26
                                                                    ->
                                                                    (fun
                                                                    uu___26
                                                                    ->
                                                                    let uu___27
                                                                    =
                                                                    let uu___28
                                                                    =
                                                                    FStarC_Tactics_V1_Builtins.pack
                                                                    (Fstarcompiler.FStarC_Reflection_V1_Data.Tv_Var
                                                                    bv) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (505))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (505))
                                                                    (Prims.of_int (37)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (505))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (505))
                                                                    (Prims.of_int (50)))))
                                                                    (Obj.magic
                                                                    uu___28)
                                                                    (fun
                                                                    uu___29
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___30
                                                                    ->
                                                                    (uu___29,
                                                                    Fstarcompiler.FStarC_Reflection_V1_Data.Q_Explicit))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (505))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (505))
                                                                    (Prims.of_int (50)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (505))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (505))
                                                                    (Prims.of_int (55)))))
                                                                    (Obj.magic
                                                                    uu___27)
                                                                    (fun
                                                                    uu___28
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___29
                                                                    ->
                                                                    (uu___28,
                                                                    bvs2)))))
                                                                    uu___26)
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    let uu___25
                                                                    =
                                                                    assoc
                                                                    name
                                                                    st2.seen in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (510))
                                                                    (Prims.of_int (49))
                                                                    (Prims.of_int (510))
                                                                    (Prims.of_int (67)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (506))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (523))
                                                                    (Prims.of_int (76)))))
                                                                    (Obj.magic
                                                                    uu___25)
                                                                    (fun
                                                                    uu___26
                                                                    ->
                                                                    (fun
                                                                    uu___26
                                                                    ->
                                                                    match uu___26
                                                                    with
                                                                    | 
                                                                    (needs_index,
                                                                    typ,
                                                                    uu___27,
                                                                    uu___28)
                                                                    ->
                                                                    let uu___29
                                                                    =
                                                                    if
                                                                    needs_index
                                                                    &&
                                                                    (Prims.op_Negation
                                                                    (FStar_Pervasives_Native.uu___is_Some
                                                                    index_arg))
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (let uu___30
                                                                    =
                                                                    let uu___31
                                                                    =
                                                                    string_of_name
                                                                    name in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (512))
                                                                    (Prims.of_int (63))
                                                                    (Prims.of_int (512))
                                                                    (Prims.of_int (82)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___31)
                                                                    (fun
                                                                    uu___32
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___33
                                                                    ->
                                                                    Prims.strcat
                                                                    "Index inconsistency in bv for "
                                                                    uu___32)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (512))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (512))
                                                                    (Prims.of_int (83)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (512))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (512))
                                                                    (Prims.of_int (83)))))
                                                                    (Obj.magic
                                                                    uu___30)
                                                                    (fun
                                                                    uu___31
                                                                    ->
                                                                    FStar_Tactics_V1_Derived.fail
                                                                    uu___31)))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___31
                                                                    -> ()))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (511))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (512))
                                                                    (Prims.of_int (83)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (514))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (523))
                                                                    (Prims.of_int (76)))))
                                                                    (Obj.magic
                                                                    uu___29)
                                                                    (fun
                                                                    uu___30
                                                                    ->
                                                                    (fun
                                                                    uu___30
                                                                    ->
                                                                    let uu___31
                                                                    =
                                                                    let uu___32
                                                                    =
                                                                    let uu___33
                                                                    =
                                                                    let uu___34
                                                                    =
                                                                    let uu___35
                                                                    =
                                                                    string_of_name
                                                                    name in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (514))
                                                                    (Prims.of_int (62))
                                                                    (Prims.of_int (514))
                                                                    (Prims.of_int (81)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (514))
                                                                    (Prims.of_int (62))
                                                                    (Prims.of_int (516))
                                                                    (Prims.of_int (97)))))
                                                                    (Obj.magic
                                                                    uu___35)
                                                                    (fun
                                                                    uu___36
                                                                    ->
                                                                    (fun
                                                                    uu___36
                                                                    ->
                                                                    let uu___37
                                                                    =
                                                                    let uu___38
                                                                    =
                                                                    let uu___39
                                                                    =
                                                                    let uu___40
                                                                    =
                                                                    FStarC_Tactics_V1_Builtins.term_to_string
                                                                    typ in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (515))
                                                                    (Prims.of_int (32))
                                                                    (Prims.of_int (515))
                                                                    (Prims.of_int (50)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (515))
                                                                    (Prims.of_int (32))
                                                                    (Prims.of_int (516))
                                                                    (Prims.of_int (97)))))
                                                                    (Obj.magic
                                                                    uu___40)
                                                                    (fun
                                                                    uu___41
                                                                    ->
                                                                    (fun
                                                                    uu___41
                                                                    ->
                                                                    let uu___42
                                                                    =
                                                                    let uu___43
                                                                    =
                                                                    let uu___44
                                                                    =
                                                                    if
                                                                    needs_index
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (let uu___45
                                                                    =
                                                                    must
                                                                    index_arg in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (516))
                                                                    (Prims.of_int (58))
                                                                    (Prims.of_int (516))
                                                                    (Prims.of_int (74)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (516))
                                                                    (Prims.of_int (43))
                                                                    (Prims.of_int (516))
                                                                    (Prims.of_int (74)))))
                                                                    (Obj.magic
                                                                    uu___45)
                                                                    (fun
                                                                    uu___46
                                                                    ->
                                                                    (fun
                                                                    uu___46
                                                                    ->
                                                                    Obj.magic
                                                                    (FStarC_Tactics_V1_Builtins.term_to_string
                                                                    uu___46))
                                                                    uu___46)))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___46
                                                                    ->
                                                                    "no-index"))) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (516))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (516))
                                                                    (Prims.of_int (91)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___44)
                                                                    (fun
                                                                    uu___45
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___46
                                                                    ->
                                                                    Prims.strcat
                                                                    uu___45
                                                                    ">")) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (516))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (516))
                                                                    (Prims.of_int (97)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___43)
                                                                    (fun
                                                                    uu___44
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___45
                                                                    ->
                                                                    Prims.strcat
                                                                    "> <"
                                                                    uu___44)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (515))
                                                                    (Prims.of_int (53))
                                                                    (Prims.of_int (516))
                                                                    (Prims.of_int (97)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___42)
                                                                    (fun
                                                                    uu___43
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___44
                                                                    ->
                                                                    Prims.strcat
                                                                    uu___41
                                                                    uu___43))))
                                                                    uu___41) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (515))
                                                                    (Prims.of_int (32))
                                                                    (Prims.of_int (516))
                                                                    (Prims.of_int (97)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___39)
                                                                    (fun
                                                                    uu___40
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___41
                                                                    ->
                                                                    Prims.strcat
                                                                    "app <"
                                                                    uu___40)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (515))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (516))
                                                                    (Prims.of_int (97)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___38)
                                                                    (fun
                                                                    uu___39
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___40
                                                                    ->
                                                                    Prims.strcat
                                                                    " at type "
                                                                    uu___39)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (514))
                                                                    (Prims.of_int (84))
                                                                    (Prims.of_int (516))
                                                                    (Prims.of_int (97)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___37)
                                                                    (fun
                                                                    uu___38
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___39
                                                                    ->
                                                                    Prims.strcat
                                                                    uu___36
                                                                    uu___38))))
                                                                    uu___36) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (514))
                                                                    (Prims.of_int (62))
                                                                    (Prims.of_int (516))
                                                                    (Prims.of_int (97)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___34)
                                                                    (fun
                                                                    uu___35
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___36
                                                                    ->
                                                                    Prims.strcat
                                                                    "Allocating bv for "
                                                                    uu___35)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (514))
                                                                    (Prims.of_int (39))
                                                                    (Prims.of_int (516))
                                                                    (Prims.of_int (97)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___33)
                                                                    (fun
                                                                    uu___34
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___35
                                                                    ->
                                                                    Prims.strcat
                                                                    st2.indent
                                                                    uu___34)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (514))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (516))
                                                                    (Prims.of_int (98)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (514))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (516))
                                                                    (Prims.of_int (98)))))
                                                                    (Obj.magic
                                                                    uu___32)
                                                                    (fun
                                                                    uu___33
                                                                    ->
                                                                    (fun
                                                                    uu___33
                                                                    ->
                                                                    Obj.magic
                                                                    (FStarC_Tactics_V1_Builtins.print
                                                                    uu___33))
                                                                    uu___33) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (514))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (516))
                                                                    (Prims.of_int (98)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (516))
                                                                    (Prims.of_int (99))
                                                                    (Prims.of_int (523))
                                                                    (Prims.of_int (76)))))
                                                                    (Obj.magic
                                                                    uu___31)
                                                                    (fun
                                                                    uu___32
                                                                    ->
                                                                    (fun
                                                                    uu___32
                                                                    ->
                                                                    let uu___33
                                                                    =
                                                                    if
                                                                    needs_index
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (let uu___34
                                                                    =
                                                                    let uu___35
                                                                    =
                                                                    let uu___36
                                                                    =
                                                                    must
                                                                    index_arg in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (519))
                                                                    (Prims.of_int (60))
                                                                    (Prims.of_int (519))
                                                                    (Prims.of_int (74)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (519))
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (519))
                                                                    (Prims.of_int (87)))))
                                                                    (Obj.magic
                                                                    uu___36)
                                                                    (fun
                                                                    uu___37
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___38
                                                                    ->
                                                                    (uu___37,
                                                                    Fstarcompiler.FStarC_Reflection_V1_Data.Q_Implicit))) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (519))
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (519))
                                                                    (Prims.of_int (87)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (519))
                                                                    (Prims.of_int (47))
                                                                    (Prims.of_int (519))
                                                                    (Prims.of_int (88)))))
                                                                    (Obj.magic
                                                                    uu___35)
                                                                    (fun
                                                                    uu___36
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___37
                                                                    ->
                                                                    Fstarcompiler.FStarC_Reflection_V1_Data.Tv_App
                                                                    (typ,
                                                                    uu___36))) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (519))
                                                                    (Prims.of_int (47))
                                                                    (Prims.of_int (519))
                                                                    (Prims.of_int (88)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (519))
                                                                    (Prims.of_int (42))
                                                                    (Prims.of_int (519))
                                                                    (Prims.of_int (88)))))
                                                                    (Obj.magic
                                                                    uu___34)
                                                                    (fun
                                                                    uu___35
                                                                    ->
                                                                    (fun
                                                                    uu___35
                                                                    ->
                                                                    Obj.magic
                                                                    (FStarC_Tactics_V1_Builtins.pack
                                                                    uu___35))
                                                                    uu___35)))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___35
                                                                    -> typ))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (519))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (519))
                                                                    (Prims.of_int (97)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (520))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (523))
                                                                    (Prims.of_int (76)))))
                                                                    (Obj.magic
                                                                    uu___33)
                                                                    (fun
                                                                    uu___34
                                                                    ->
                                                                    (fun typ1
                                                                    ->
                                                                    let uu___34
                                                                    =
                                                                    FStarC_Tactics_V1_Builtins.pack
                                                                    (Fstarcompiler.FStarC_Reflection_V1_Data.Tv_App
                                                                    (typ1,
                                                                    (inv_bv,
                                                                    Fstarcompiler.FStarC_Reflection_V1_Data.Q_Explicit))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (521))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (521))
                                                                    (Prims.of_int (68)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (521))
                                                                    (Prims.of_int (71))
                                                                    (Prims.of_int (523))
                                                                    (Prims.of_int (76)))))
                                                                    (Obj.magic
                                                                    uu___34)
                                                                    (fun
                                                                    uu___35
                                                                    ->
                                                                    (fun typ2
                                                                    ->
                                                                    let uu___35
                                                                    =
                                                                    let uu___36
                                                                    =
                                                                    let uu___37
                                                                    =
                                                                    string_of_name
                                                                    name in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (522))
                                                                    (Prims.of_int (58))
                                                                    (Prims.of_int (522))
                                                                    (Prims.of_int (77)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___37)
                                                                    (fun
                                                                    uu___38
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___39
                                                                    ->
                                                                    Prims.strcat
                                                                    "arg_"
                                                                    uu___38)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (522))
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (522))
                                                                    (Prims.of_int (78)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (522))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (522))
                                                                    (Prims.of_int (78)))))
                                                                    (Obj.magic
                                                                    uu___36)
                                                                    (fun
                                                                    uu___37
                                                                    ->
                                                                    (fun
                                                                    uu___37
                                                                    ->
                                                                    Obj.magic
                                                                    (FStarC_Tactics_V1_Builtins.fresh_bv_named
                                                                    uu___37))
                                                                    uu___37) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (522))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (522))
                                                                    (Prims.of_int (78)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (523))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (523))
                                                                    (Prims.of_int (76)))))
                                                                    (Obj.magic
                                                                    uu___35)
                                                                    (fun
                                                                    uu___36
                                                                    ->
                                                                    (fun bv
                                                                    ->
                                                                    let uu___36
                                                                    =
                                                                    let uu___37
                                                                    =
                                                                    FStarC_Tactics_V1_Builtins.pack
                                                                    (Fstarcompiler.FStarC_Reflection_V1_Data.Tv_Var
                                                                    bv) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (523))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (523))
                                                                    (Prims.of_int (37)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (523))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (523))
                                                                    (Prims.of_int (50)))))
                                                                    (Obj.magic
                                                                    uu___37)
                                                                    (fun
                                                                    uu___38
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___39
                                                                    ->
                                                                    (uu___38,
                                                                    Fstarcompiler.FStarC_Reflection_V1_Data.Q_Explicit))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (523))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (523))
                                                                    (Prims.of_int (50)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (523))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (523))
                                                                    (Prims.of_int (76)))))
                                                                    (Obj.magic
                                                                    uu___36)
                                                                    (fun
                                                                    uu___37
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___38
                                                                    ->
                                                                    (uu___37,
                                                                    ((name,
                                                                    (bv,
                                                                    typ2)) ::
                                                                    bvs2))))))
                                                                    uu___36)))
                                                                    uu___35)))
                                                                    uu___34)))
                                                                    uu___32)))
                                                                    uu___30)))
                                                                    uu___26))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (500))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (523))
                                                                    (Prims.of_int (76)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (526))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (549))
                                                                    (Prims.of_int (33)))))
                                                                    (Obj.magic
                                                                    uu___23)
                                                                    (fun
                                                                    uu___24
                                                                    ->
                                                                    (fun
                                                                    allocate_bv_for
                                                                    ->
                                                                    match map
                                                                    with
                                                                    | 
                                                                    Inline
                                                                    fv2 ->
                                                                    let uu___24
                                                                    =
                                                                    FStar_Tactics_Util.fold_left
                                                                    (fun
                                                                    uu___25
                                                                    ->
                                                                    fun name
                                                                    ->
                                                                    match uu___25
                                                                    with
                                                                    | 
                                                                    (extra_args,
                                                                    bvs2) ->
                                                                    let uu___26
                                                                    =
                                                                    allocate_bv_for
                                                                    name bvs2 in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (532))
                                                                    (Prims.of_int (36))
                                                                    (Prims.of_int (532))
                                                                    (Prims.of_int (60)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (531))
                                                                    (Prims.of_int (80))
                                                                    (Prims.of_int (533))
                                                                    (Prims.of_int (43)))))
                                                                    (Obj.magic
                                                                    uu___26)
                                                                    (fun
                                                                    uu___27
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___28
                                                                    ->
                                                                    match uu___27
                                                                    with
                                                                    | 
                                                                    (term,
                                                                    bvs3) ->
                                                                    ((term ::
                                                                    extra_args),
                                                                    bvs3))))
                                                                    ([],
                                                                    bvs1) fns in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (531))
                                                                    (Prims.of_int (40))
                                                                    (Prims.of_int (534))
                                                                    (Prims.of_int (33)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (527))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (543))
                                                                    (Prims.of_int (33)))))
                                                                    (Obj.magic
                                                                    uu___24)
                                                                    (fun
                                                                    uu___25
                                                                    ->
                                                                    (fun
                                                                    uu___25
                                                                    ->
                                                                    match uu___25
                                                                    with
                                                                    | 
                                                                    (extra_args,
                                                                    bvs2) ->
                                                                    let uu___26
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___27
                                                                    ->
                                                                    FStar_List_Tot_Base.rev
                                                                    extra_args)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (535))
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (535))
                                                                    (Prims.of_int (54)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (535))
                                                                    (Prims.of_int (57))
                                                                    (Prims.of_int (543))
                                                                    (Prims.of_int (33)))))
                                                                    (Obj.magic
                                                                    uu___26)
                                                                    (fun
                                                                    uu___27
                                                                    ->
                                                                    (fun
                                                                    extra_args1
                                                                    ->
                                                                    let uu___27
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___28
                                                                    ->
                                                                    (inv_bv,
                                                                    Fstarcompiler.FStarC_Reflection_V1_Data.Q_Explicit)
                                                                    ::
                                                                    extra_args1)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (536))
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (536))
                                                                    (Prims.of_int (69)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (536))
                                                                    (Prims.of_int (72))
                                                                    (Prims.of_int (543))
                                                                    (Prims.of_int (33)))))
                                                                    (Obj.magic
                                                                    uu___27)
                                                                    (fun
                                                                    uu___28
                                                                    ->
                                                                    (fun
                                                                    extra_args2
                                                                    ->
                                                                    let uu___28
                                                                    =
                                                                    if
                                                                    has_index
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (let uu___29
                                                                    =
                                                                    let uu___30
                                                                    =
                                                                    must
                                                                    index_bv in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (539))
                                                                    (Prims.of_int (39))
                                                                    (Prims.of_int (539))
                                                                    (Prims.of_int (52)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (539))
                                                                    (Prims.of_int (38))
                                                                    (Prims.of_int (539))
                                                                    (Prims.of_int (65)))))
                                                                    (Obj.magic
                                                                    uu___30)
                                                                    (fun
                                                                    uu___31
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___32
                                                                    ->
                                                                    (uu___31,
                                                                    Fstarcompiler.FStarC_Reflection_V1_Data.Q_Implicit))) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (539))
                                                                    (Prims.of_int (38))
                                                                    (Prims.of_int (539))
                                                                    (Prims.of_int (65)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (539))
                                                                    (Prims.of_int (38))
                                                                    (Prims.of_int (539))
                                                                    (Prims.of_int (79)))))
                                                                    (Obj.magic
                                                                    uu___29)
                                                                    (fun
                                                                    uu___30
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___31
                                                                    ->
                                                                    uu___30
                                                                    ::
                                                                    extra_args2))))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___30
                                                                    ->
                                                                    extra_args2))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (539))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (539))
                                                                    (Prims.of_int (95)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (540))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (543))
                                                                    (Prims.of_int (33)))))
                                                                    (Obj.magic
                                                                    uu___28)
                                                                    (fun
                                                                    uu___29
                                                                    ->
                                                                    (fun
                                                                    extra_args3
                                                                    ->
                                                                    let uu___29
                                                                    =
                                                                    let uu___30
                                                                    =
                                                                    FStarC_Tactics_V1_Builtins.pack
                                                                    (Fstarcompiler.FStarC_Reflection_V1_Data.Tv_FVar
                                                                    (Fstarcompiler.FStarC_Reflection_V1_Builtins.pack_fv
                                                                    fv2)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (542))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (542))
                                                                    (Prims.of_int (62)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (542))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (542))
                                                                    (Prims.of_int (80)))))
                                                                    (Obj.magic
                                                                    uu___30)
                                                                    (fun
                                                                    uu___31
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___32
                                                                    ->
                                                                    FStar_Reflection_V1_Derived.mk_app
                                                                    uu___31
                                                                    (FStar_List_Tot_Base.op_At
                                                                    extra_args3
                                                                    es4))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (542))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (542))
                                                                    (Prims.of_int (80)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (543))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (543))
                                                                    (Prims.of_int (33)))))
                                                                    (Obj.magic
                                                                    uu___29)
                                                                    (fun e2
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___30
                                                                    ->
                                                                    (st2, e2,
                                                                    bvs2,
                                                                    ses1)))))
                                                                    uu___29)))
                                                                    uu___28)))
                                                                    uu___27)))
                                                                    uu___25))
                                                                    | 
                                                                    Specialize
                                                                    ->
                                                                    let uu___24
                                                                    =
                                                                    allocate_bv_for
                                                                    fv1 bvs1 in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (547))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (547))
                                                                    (Prims.of_int (53)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (545))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (549))
                                                                    (Prims.of_int (33)))))
                                                                    (Obj.magic
                                                                    uu___24)
                                                                    (fun
                                                                    uu___25
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___26
                                                                    ->
                                                                    match uu___25
                                                                    with
                                                                    | 
                                                                    (e2,
                                                                    bvs2) ->
                                                                    (st2,
                                                                    (FStar_Reflection_V1_Derived.mk_app
                                                                    (FStar_Pervasives_Native.fst
                                                                    e2) es4),
                                                                    bvs2,
                                                                    ses1)))))
                                                                    uu___24)))
                                                                    uu___22)))
                                                                    uu___20)))
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___18
                                                                    ->
                                                                    (st2,
                                                                    (FStar_Reflection_V1_Derived.mk_app
                                                                    e1 es3),
                                                                    bvs1,
                                                                    ses1)))))
                                                                    uu___18)))
                                                                    uu___16)))
                                                                    uu___15)))
                                                                    | 
                                                                    Fstarcompiler.FStarC_Reflection_V1_Data.Tv_FVar
                                                                    fv ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (let uu___13
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    Fstarcompiler.FStarC_Reflection_V1_Builtins.inspect_fv
                                                                    fv)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (476))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (476))
                                                                    (Prims.of_int (32)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (476))
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (555))
                                                                    (Prims.of_int (13)))))
                                                                    (Obj.magic
                                                                    uu___13)
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    (fun fv1
                                                                    ->
                                                                    let uu___14
                                                                    =
                                                                    visit_function
                                                                    t_i st1
                                                                    fv1 in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (477))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (477))
                                                                    (Prims.of_int (49)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (476))
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (555))
                                                                    (Prims.of_int (13)))))
                                                                    (Obj.magic
                                                                    uu___14)
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    match uu___15
                                                                    with
                                                                    | 
                                                                    (st2,
                                                                    ses') ->
                                                                    let uu___16
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    FStar_List_Tot_Base.op_At
                                                                    ses ses')) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (478))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (478))
                                                                    (Prims.of_int (30)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (481))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (554))
                                                                    (Prims.of_int (29)))))
                                                                    (Obj.magic
                                                                    uu___16)
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    (fun ses1
                                                                    ->
                                                                    match 
                                                                    FStar_List_Tot_Base.assoc
                                                                    fv1
                                                                    st2.seen
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (has_index,
                                                                    uu___17,
                                                                    map, fns)
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (let uu___18
                                                                    =
                                                                    let uu___19
                                                                    =
                                                                    let uu___20
                                                                    =
                                                                    let uu___21
                                                                    =
                                                                    string_of_name
                                                                    fv1 in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (483))
                                                                    (Prims.of_int (63))
                                                                    (Prims.of_int (483))
                                                                    (Prims.of_int (80)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___21)
                                                                    (fun
                                                                    uu___22
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___23
                                                                    ->
                                                                    Prims.strcat
                                                                    "Rewriting application of "
                                                                    uu___22)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (483))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (483))
                                                                    (Prims.of_int (80)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___20)
                                                                    (fun
                                                                    uu___21
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___22
                                                                    ->
                                                                    Prims.strcat
                                                                    st2.indent
                                                                    uu___21)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (483))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (483))
                                                                    (Prims.of_int (81)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (483))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (483))
                                                                    (Prims.of_int (81)))))
                                                                    (Obj.magic
                                                                    uu___19)
                                                                    (fun
                                                                    uu___20
                                                                    ->
                                                                    (fun
                                                                    uu___20
                                                                    ->
                                                                    Obj.magic
                                                                    (FStarC_Tactics_V1_Builtins.print
                                                                    uu___20))
                                                                    uu___20) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (483))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (483))
                                                                    (Prims.of_int (81)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (483))
                                                                    (Prims.of_int (82))
                                                                    (Prims.of_int (550))
                                                                    (Prims.of_int (17)))))
                                                                    (Obj.magic
                                                                    uu___18)
                                                                    (fun
                                                                    uu___19
                                                                    ->
                                                                    (fun
                                                                    uu___19
                                                                    ->
                                                                    let uu___20
                                                                    =
                                                                    if
                                                                    has_index
                                                                    then
                                                                    match es3
                                                                    with
                                                                    | 
                                                                    (e2,
                                                                    Fstarcompiler.FStarC_Reflection_V1_Data.Q_Implicit)::es4
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___21
                                                                    ->
                                                                    ((FStar_Pervasives_Native.Some
                                                                    e2), es4)))
                                                                    | 
                                                                    uu___21
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_V1_Derived.fail
                                                                    "this application does not seem to start with an index")
                                                                    else
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___22
                                                                    ->
                                                                    (FStar_Pervasives_Native.None,
                                                                    es3))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (486))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (493))
                                                                    (Prims.of_int (26)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (483))
                                                                    (Prims.of_int (82))
                                                                    (Prims.of_int (550))
                                                                    (Prims.of_int (17)))))
                                                                    (Obj.magic
                                                                    uu___20)
                                                                    (fun
                                                                    uu___21
                                                                    ->
                                                                    (fun
                                                                    uu___21
                                                                    ->
                                                                    match uu___21
                                                                    with
                                                                    | 
                                                                    (index_arg,
                                                                    es4) ->
                                                                    let uu___22
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___23
                                                                    ->
                                                                    fun name
                                                                    ->
                                                                    fun bvs2
                                                                    ->
                                                                    match 
                                                                    FStar_List_Tot_Base.assoc
                                                                    name bvs2
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (bv,
                                                                    sort) ->
                                                                    let uu___24
                                                                    =
                                                                    let uu___25
                                                                    =
                                                                    let uu___26
                                                                    =
                                                                    let uu___27
                                                                    =
                                                                    string_of_name
                                                                    name in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (502))
                                                                    (Prims.of_int (39))
                                                                    (Prims.of_int (502))
                                                                    (Prims.of_int (58)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___27)
                                                                    (fun
                                                                    uu___28
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___29
                                                                    ->
                                                                    Prims.strcat
                                                                    uu___28
                                                                    " already has a bv")) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (502))
                                                                    (Prims.of_int (39))
                                                                    (Prims.of_int (502))
                                                                    (Prims.of_int (80)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___26)
                                                                    (fun
                                                                    uu___27
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___28
                                                                    ->
                                                                    Prims.strcat
                                                                    st2.indent
                                                                    uu___27)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (502))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (502))
                                                                    (Prims.of_int (81)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (502))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (502))
                                                                    (Prims.of_int (81)))))
                                                                    (Obj.magic
                                                                    uu___25)
                                                                    (fun
                                                                    uu___26
                                                                    ->
                                                                    (fun
                                                                    uu___26
                                                                    ->
                                                                    Obj.magic
                                                                    (FStarC_Tactics_V1_Builtins.print
                                                                    uu___26))
                                                                    uu___26) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (502))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (502))
                                                                    (Prims.of_int (81)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (505))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (505))
                                                                    (Prims.of_int (55)))))
                                                                    (Obj.magic
                                                                    uu___24)
                                                                    (fun
                                                                    uu___25
                                                                    ->
                                                                    (fun
                                                                    uu___25
                                                                    ->
                                                                    let uu___26
                                                                    =
                                                                    let uu___27
                                                                    =
                                                                    FStarC_Tactics_V1_Builtins.pack
                                                                    (Fstarcompiler.FStarC_Reflection_V1_Data.Tv_Var
                                                                    bv) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (505))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (505))
                                                                    (Prims.of_int (37)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (505))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (505))
                                                                    (Prims.of_int (50)))))
                                                                    (Obj.magic
                                                                    uu___27)
                                                                    (fun
                                                                    uu___28
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___29
                                                                    ->
                                                                    (uu___28,
                                                                    Fstarcompiler.FStarC_Reflection_V1_Data.Q_Explicit))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (505))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (505))
                                                                    (Prims.of_int (50)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (505))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (505))
                                                                    (Prims.of_int (55)))))
                                                                    (Obj.magic
                                                                    uu___26)
                                                                    (fun
                                                                    uu___27
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___28
                                                                    ->
                                                                    (uu___27,
                                                                    bvs2)))))
                                                                    uu___25)
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    let uu___24
                                                                    =
                                                                    assoc
                                                                    name
                                                                    st2.seen in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (510))
                                                                    (Prims.of_int (49))
                                                                    (Prims.of_int (510))
                                                                    (Prims.of_int (67)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (506))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (523))
                                                                    (Prims.of_int (76)))))
                                                                    (Obj.magic
                                                                    uu___24)
                                                                    (fun
                                                                    uu___25
                                                                    ->
                                                                    (fun
                                                                    uu___25
                                                                    ->
                                                                    match uu___25
                                                                    with
                                                                    | 
                                                                    (needs_index,
                                                                    typ,
                                                                    uu___26,
                                                                    uu___27)
                                                                    ->
                                                                    let uu___28
                                                                    =
                                                                    if
                                                                    needs_index
                                                                    &&
                                                                    (Prims.op_Negation
                                                                    (FStar_Pervasives_Native.uu___is_Some
                                                                    index_arg))
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (let uu___29
                                                                    =
                                                                    let uu___30
                                                                    =
                                                                    string_of_name
                                                                    name in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (512))
                                                                    (Prims.of_int (63))
                                                                    (Prims.of_int (512))
                                                                    (Prims.of_int (82)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___30)
                                                                    (fun
                                                                    uu___31
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___32
                                                                    ->
                                                                    Prims.strcat
                                                                    "Index inconsistency in bv for "
                                                                    uu___31)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (512))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (512))
                                                                    (Prims.of_int (83)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (512))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (512))
                                                                    (Prims.of_int (83)))))
                                                                    (Obj.magic
                                                                    uu___29)
                                                                    (fun
                                                                    uu___30
                                                                    ->
                                                                    FStar_Tactics_V1_Derived.fail
                                                                    uu___30)))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___30
                                                                    -> ()))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (511))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (512))
                                                                    (Prims.of_int (83)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (514))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (523))
                                                                    (Prims.of_int (76)))))
                                                                    (Obj.magic
                                                                    uu___28)
                                                                    (fun
                                                                    uu___29
                                                                    ->
                                                                    (fun
                                                                    uu___29
                                                                    ->
                                                                    let uu___30
                                                                    =
                                                                    let uu___31
                                                                    =
                                                                    let uu___32
                                                                    =
                                                                    let uu___33
                                                                    =
                                                                    let uu___34
                                                                    =
                                                                    string_of_name
                                                                    name in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (514))
                                                                    (Prims.of_int (62))
                                                                    (Prims.of_int (514))
                                                                    (Prims.of_int (81)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (514))
                                                                    (Prims.of_int (62))
                                                                    (Prims.of_int (516))
                                                                    (Prims.of_int (97)))))
                                                                    (Obj.magic
                                                                    uu___34)
                                                                    (fun
                                                                    uu___35
                                                                    ->
                                                                    (fun
                                                                    uu___35
                                                                    ->
                                                                    let uu___36
                                                                    =
                                                                    let uu___37
                                                                    =
                                                                    let uu___38
                                                                    =
                                                                    let uu___39
                                                                    =
                                                                    FStarC_Tactics_V1_Builtins.term_to_string
                                                                    typ in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (515))
                                                                    (Prims.of_int (32))
                                                                    (Prims.of_int (515))
                                                                    (Prims.of_int (50)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (515))
                                                                    (Prims.of_int (32))
                                                                    (Prims.of_int (516))
                                                                    (Prims.of_int (97)))))
                                                                    (Obj.magic
                                                                    uu___39)
                                                                    (fun
                                                                    uu___40
                                                                    ->
                                                                    (fun
                                                                    uu___40
                                                                    ->
                                                                    let uu___41
                                                                    =
                                                                    let uu___42
                                                                    =
                                                                    let uu___43
                                                                    =
                                                                    if
                                                                    needs_index
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (let uu___44
                                                                    =
                                                                    must
                                                                    index_arg in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (516))
                                                                    (Prims.of_int (58))
                                                                    (Prims.of_int (516))
                                                                    (Prims.of_int (74)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (516))
                                                                    (Prims.of_int (43))
                                                                    (Prims.of_int (516))
                                                                    (Prims.of_int (74)))))
                                                                    (Obj.magic
                                                                    uu___44)
                                                                    (fun
                                                                    uu___45
                                                                    ->
                                                                    (fun
                                                                    uu___45
                                                                    ->
                                                                    Obj.magic
                                                                    (FStarC_Tactics_V1_Builtins.term_to_string
                                                                    uu___45))
                                                                    uu___45)))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___45
                                                                    ->
                                                                    "no-index"))) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (516))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (516))
                                                                    (Prims.of_int (91)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___43)
                                                                    (fun
                                                                    uu___44
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___45
                                                                    ->
                                                                    Prims.strcat
                                                                    uu___44
                                                                    ">")) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (516))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (516))
                                                                    (Prims.of_int (97)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___42)
                                                                    (fun
                                                                    uu___43
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___44
                                                                    ->
                                                                    Prims.strcat
                                                                    "> <"
                                                                    uu___43)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (515))
                                                                    (Prims.of_int (53))
                                                                    (Prims.of_int (516))
                                                                    (Prims.of_int (97)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___41)
                                                                    (fun
                                                                    uu___42
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___43
                                                                    ->
                                                                    Prims.strcat
                                                                    uu___40
                                                                    uu___42))))
                                                                    uu___40) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (515))
                                                                    (Prims.of_int (32))
                                                                    (Prims.of_int (516))
                                                                    (Prims.of_int (97)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___38)
                                                                    (fun
                                                                    uu___39
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___40
                                                                    ->
                                                                    Prims.strcat
                                                                    "app <"
                                                                    uu___39)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (515))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (516))
                                                                    (Prims.of_int (97)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___37)
                                                                    (fun
                                                                    uu___38
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___39
                                                                    ->
                                                                    Prims.strcat
                                                                    " at type "
                                                                    uu___38)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (514))
                                                                    (Prims.of_int (84))
                                                                    (Prims.of_int (516))
                                                                    (Prims.of_int (97)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___36)
                                                                    (fun
                                                                    uu___37
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___38
                                                                    ->
                                                                    Prims.strcat
                                                                    uu___35
                                                                    uu___37))))
                                                                    uu___35) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (514))
                                                                    (Prims.of_int (62))
                                                                    (Prims.of_int (516))
                                                                    (Prims.of_int (97)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___33)
                                                                    (fun
                                                                    uu___34
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___35
                                                                    ->
                                                                    Prims.strcat
                                                                    "Allocating bv for "
                                                                    uu___34)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (514))
                                                                    (Prims.of_int (39))
                                                                    (Prims.of_int (516))
                                                                    (Prims.of_int (97)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___32)
                                                                    (fun
                                                                    uu___33
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___34
                                                                    ->
                                                                    Prims.strcat
                                                                    st2.indent
                                                                    uu___33)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (514))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (516))
                                                                    (Prims.of_int (98)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (514))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (516))
                                                                    (Prims.of_int (98)))))
                                                                    (Obj.magic
                                                                    uu___31)
                                                                    (fun
                                                                    uu___32
                                                                    ->
                                                                    (fun
                                                                    uu___32
                                                                    ->
                                                                    Obj.magic
                                                                    (FStarC_Tactics_V1_Builtins.print
                                                                    uu___32))
                                                                    uu___32) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (514))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (516))
                                                                    (Prims.of_int (98)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (516))
                                                                    (Prims.of_int (99))
                                                                    (Prims.of_int (523))
                                                                    (Prims.of_int (76)))))
                                                                    (Obj.magic
                                                                    uu___30)
                                                                    (fun
                                                                    uu___31
                                                                    ->
                                                                    (fun
                                                                    uu___31
                                                                    ->
                                                                    let uu___32
                                                                    =
                                                                    if
                                                                    needs_index
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (let uu___33
                                                                    =
                                                                    let uu___34
                                                                    =
                                                                    let uu___35
                                                                    =
                                                                    must
                                                                    index_arg in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (519))
                                                                    (Prims.of_int (60))
                                                                    (Prims.of_int (519))
                                                                    (Prims.of_int (74)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (519))
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (519))
                                                                    (Prims.of_int (87)))))
                                                                    (Obj.magic
                                                                    uu___35)
                                                                    (fun
                                                                    uu___36
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___37
                                                                    ->
                                                                    (uu___36,
                                                                    Fstarcompiler.FStarC_Reflection_V1_Data.Q_Implicit))) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (519))
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (519))
                                                                    (Prims.of_int (87)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (519))
                                                                    (Prims.of_int (47))
                                                                    (Prims.of_int (519))
                                                                    (Prims.of_int (88)))))
                                                                    (Obj.magic
                                                                    uu___34)
                                                                    (fun
                                                                    uu___35
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___36
                                                                    ->
                                                                    Fstarcompiler.FStarC_Reflection_V1_Data.Tv_App
                                                                    (typ,
                                                                    uu___35))) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (519))
                                                                    (Prims.of_int (47))
                                                                    (Prims.of_int (519))
                                                                    (Prims.of_int (88)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (519))
                                                                    (Prims.of_int (42))
                                                                    (Prims.of_int (519))
                                                                    (Prims.of_int (88)))))
                                                                    (Obj.magic
                                                                    uu___33)
                                                                    (fun
                                                                    uu___34
                                                                    ->
                                                                    (fun
                                                                    uu___34
                                                                    ->
                                                                    Obj.magic
                                                                    (FStarC_Tactics_V1_Builtins.pack
                                                                    uu___34))
                                                                    uu___34)))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___34
                                                                    -> typ))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (519))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (519))
                                                                    (Prims.of_int (97)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (520))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (523))
                                                                    (Prims.of_int (76)))))
                                                                    (Obj.magic
                                                                    uu___32)
                                                                    (fun
                                                                    uu___33
                                                                    ->
                                                                    (fun typ1
                                                                    ->
                                                                    let uu___33
                                                                    =
                                                                    FStarC_Tactics_V1_Builtins.pack
                                                                    (Fstarcompiler.FStarC_Reflection_V1_Data.Tv_App
                                                                    (typ1,
                                                                    (inv_bv,
                                                                    Fstarcompiler.FStarC_Reflection_V1_Data.Q_Explicit))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (521))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (521))
                                                                    (Prims.of_int (68)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (521))
                                                                    (Prims.of_int (71))
                                                                    (Prims.of_int (523))
                                                                    (Prims.of_int (76)))))
                                                                    (Obj.magic
                                                                    uu___33)
                                                                    (fun
                                                                    uu___34
                                                                    ->
                                                                    (fun typ2
                                                                    ->
                                                                    let uu___34
                                                                    =
                                                                    let uu___35
                                                                    =
                                                                    let uu___36
                                                                    =
                                                                    string_of_name
                                                                    name in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (522))
                                                                    (Prims.of_int (58))
                                                                    (Prims.of_int (522))
                                                                    (Prims.of_int (77)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___36)
                                                                    (fun
                                                                    uu___37
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___38
                                                                    ->
                                                                    Prims.strcat
                                                                    "arg_"
                                                                    uu___37)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (522))
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (522))
                                                                    (Prims.of_int (78)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (522))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (522))
                                                                    (Prims.of_int (78)))))
                                                                    (Obj.magic
                                                                    uu___35)
                                                                    (fun
                                                                    uu___36
                                                                    ->
                                                                    (fun
                                                                    uu___36
                                                                    ->
                                                                    Obj.magic
                                                                    (FStarC_Tactics_V1_Builtins.fresh_bv_named
                                                                    uu___36))
                                                                    uu___36) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (522))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (522))
                                                                    (Prims.of_int (78)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (523))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (523))
                                                                    (Prims.of_int (76)))))
                                                                    (Obj.magic
                                                                    uu___34)
                                                                    (fun
                                                                    uu___35
                                                                    ->
                                                                    (fun bv
                                                                    ->
                                                                    let uu___35
                                                                    =
                                                                    let uu___36
                                                                    =
                                                                    FStarC_Tactics_V1_Builtins.pack
                                                                    (Fstarcompiler.FStarC_Reflection_V1_Data.Tv_Var
                                                                    bv) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (523))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (523))
                                                                    (Prims.of_int (37)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (523))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (523))
                                                                    (Prims.of_int (50)))))
                                                                    (Obj.magic
                                                                    uu___36)
                                                                    (fun
                                                                    uu___37
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___38
                                                                    ->
                                                                    (uu___37,
                                                                    Fstarcompiler.FStarC_Reflection_V1_Data.Q_Explicit))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (523))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (523))
                                                                    (Prims.of_int (50)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (523))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (523))
                                                                    (Prims.of_int (76)))))
                                                                    (Obj.magic
                                                                    uu___35)
                                                                    (fun
                                                                    uu___36
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___37
                                                                    ->
                                                                    (uu___36,
                                                                    ((name,
                                                                    (bv,
                                                                    typ2)) ::
                                                                    bvs2))))))
                                                                    uu___35)))
                                                                    uu___34)))
                                                                    uu___33)))
                                                                    uu___31)))
                                                                    uu___29)))
                                                                    uu___25))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (500))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (523))
                                                                    (Prims.of_int (76)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (526))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (549))
                                                                    (Prims.of_int (33)))))
                                                                    (Obj.magic
                                                                    uu___22)
                                                                    (fun
                                                                    uu___23
                                                                    ->
                                                                    (fun
                                                                    allocate_bv_for
                                                                    ->
                                                                    match map
                                                                    with
                                                                    | 
                                                                    Inline
                                                                    fv2 ->
                                                                    let uu___23
                                                                    =
                                                                    FStar_Tactics_Util.fold_left
                                                                    (fun
                                                                    uu___24
                                                                    ->
                                                                    fun name
                                                                    ->
                                                                    match uu___24
                                                                    with
                                                                    | 
                                                                    (extra_args,
                                                                    bvs2) ->
                                                                    let uu___25
                                                                    =
                                                                    allocate_bv_for
                                                                    name bvs2 in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (532))
                                                                    (Prims.of_int (36))
                                                                    (Prims.of_int (532))
                                                                    (Prims.of_int (60)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (531))
                                                                    (Prims.of_int (80))
                                                                    (Prims.of_int (533))
                                                                    (Prims.of_int (43)))))
                                                                    (Obj.magic
                                                                    uu___25)
                                                                    (fun
                                                                    uu___26
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___27
                                                                    ->
                                                                    match uu___26
                                                                    with
                                                                    | 
                                                                    (term,
                                                                    bvs3) ->
                                                                    ((term ::
                                                                    extra_args),
                                                                    bvs3))))
                                                                    ([],
                                                                    bvs1) fns in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (531))
                                                                    (Prims.of_int (40))
                                                                    (Prims.of_int (534))
                                                                    (Prims.of_int (33)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (527))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (543))
                                                                    (Prims.of_int (33)))))
                                                                    (Obj.magic
                                                                    uu___23)
                                                                    (fun
                                                                    uu___24
                                                                    ->
                                                                    (fun
                                                                    uu___24
                                                                    ->
                                                                    match uu___24
                                                                    with
                                                                    | 
                                                                    (extra_args,
                                                                    bvs2) ->
                                                                    let uu___25
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___26
                                                                    ->
                                                                    FStar_List_Tot_Base.rev
                                                                    extra_args)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (535))
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (535))
                                                                    (Prims.of_int (54)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (535))
                                                                    (Prims.of_int (57))
                                                                    (Prims.of_int (543))
                                                                    (Prims.of_int (33)))))
                                                                    (Obj.magic
                                                                    uu___25)
                                                                    (fun
                                                                    uu___26
                                                                    ->
                                                                    (fun
                                                                    extra_args1
                                                                    ->
                                                                    let uu___26
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___27
                                                                    ->
                                                                    (inv_bv,
                                                                    Fstarcompiler.FStarC_Reflection_V1_Data.Q_Explicit)
                                                                    ::
                                                                    extra_args1)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (536))
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (536))
                                                                    (Prims.of_int (69)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (536))
                                                                    (Prims.of_int (72))
                                                                    (Prims.of_int (543))
                                                                    (Prims.of_int (33)))))
                                                                    (Obj.magic
                                                                    uu___26)
                                                                    (fun
                                                                    uu___27
                                                                    ->
                                                                    (fun
                                                                    extra_args2
                                                                    ->
                                                                    let uu___27
                                                                    =
                                                                    if
                                                                    has_index
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (let uu___28
                                                                    =
                                                                    let uu___29
                                                                    =
                                                                    must
                                                                    index_bv in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (539))
                                                                    (Prims.of_int (39))
                                                                    (Prims.of_int (539))
                                                                    (Prims.of_int (52)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (539))
                                                                    (Prims.of_int (38))
                                                                    (Prims.of_int (539))
                                                                    (Prims.of_int (65)))))
                                                                    (Obj.magic
                                                                    uu___29)
                                                                    (fun
                                                                    uu___30
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___31
                                                                    ->
                                                                    (uu___30,
                                                                    Fstarcompiler.FStarC_Reflection_V1_Data.Q_Implicit))) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (539))
                                                                    (Prims.of_int (38))
                                                                    (Prims.of_int (539))
                                                                    (Prims.of_int (65)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (539))
                                                                    (Prims.of_int (38))
                                                                    (Prims.of_int (539))
                                                                    (Prims.of_int (79)))))
                                                                    (Obj.magic
                                                                    uu___28)
                                                                    (fun
                                                                    uu___29
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___30
                                                                    ->
                                                                    uu___29
                                                                    ::
                                                                    extra_args2))))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___29
                                                                    ->
                                                                    extra_args2))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (539))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (539))
                                                                    (Prims.of_int (95)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (540))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (543))
                                                                    (Prims.of_int (33)))))
                                                                    (Obj.magic
                                                                    uu___27)
                                                                    (fun
                                                                    uu___28
                                                                    ->
                                                                    (fun
                                                                    extra_args3
                                                                    ->
                                                                    let uu___28
                                                                    =
                                                                    let uu___29
                                                                    =
                                                                    FStarC_Tactics_V1_Builtins.pack
                                                                    (Fstarcompiler.FStarC_Reflection_V1_Data.Tv_FVar
                                                                    (Fstarcompiler.FStarC_Reflection_V1_Builtins.pack_fv
                                                                    fv2)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (542))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (542))
                                                                    (Prims.of_int (62)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (542))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (542))
                                                                    (Prims.of_int (80)))))
                                                                    (Obj.magic
                                                                    uu___29)
                                                                    (fun
                                                                    uu___30
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___31
                                                                    ->
                                                                    FStar_Reflection_V1_Derived.mk_app
                                                                    uu___30
                                                                    (FStar_List_Tot_Base.op_At
                                                                    extra_args3
                                                                    es4))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (542))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (542))
                                                                    (Prims.of_int (80)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (543))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (543))
                                                                    (Prims.of_int (33)))))
                                                                    (Obj.magic
                                                                    uu___28)
                                                                    (fun e2
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___29
                                                                    ->
                                                                    (st2, e2,
                                                                    bvs2,
                                                                    ses1)))))
                                                                    uu___28)))
                                                                    uu___27)))
                                                                    uu___26)))
                                                                    uu___24))
                                                                    | 
                                                                    Specialize
                                                                    ->
                                                                    let uu___23
                                                                    =
                                                                    allocate_bv_for
                                                                    fv1 bvs1 in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (547))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (547))
                                                                    (Prims.of_int (53)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (545))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (549))
                                                                    (Prims.of_int (33)))))
                                                                    (Obj.magic
                                                                    uu___23)
                                                                    (fun
                                                                    uu___24
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___25
                                                                    ->
                                                                    match uu___24
                                                                    with
                                                                    | 
                                                                    (e2,
                                                                    bvs2) ->
                                                                    (st2,
                                                                    (FStar_Reflection_V1_Derived.mk_app
                                                                    (FStar_Pervasives_Native.fst
                                                                    e2) es4),
                                                                    bvs2,
                                                                    ses1)))))
                                                                    uu___23)))
                                                                    uu___21)))
                                                                    uu___19)))
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    (st2,
                                                                    (FStar_Reflection_V1_Derived.mk_app
                                                                    e1 es3),
                                                                    bvs1,
                                                                    ses1)))))
                                                                    uu___17)))
                                                                    uu___15)))
                                                                    uu___14)))
                                                                    | 
                                                                    uu___13
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    (st1,
                                                                    (FStar_Reflection_V1_Derived.mk_app
                                                                    e1 es3),
                                                                    bvs1,
                                                                    ses)))))
                                                                    uu___12)))
                                                                    uu___11)))
                                                                    uu___9)))
                                                      uu___7))) uu___5)))
                      | Fstarcompiler.FStarC_Reflection_V1_Data.Tv_Var uu___2
                          ->
                          Obj.magic
                            (Obj.repr
                               (FStar_Tactics_Effect.lift_div_tac
                                  (fun uu___3 -> (st, e, bvs, []))))
                      | Fstarcompiler.FStarC_Reflection_V1_Data.Tv_BVar
                          uu___2 ->
                          Obj.magic
                            (Obj.repr
                               (FStar_Tactics_Effect.lift_div_tac
                                  (fun uu___3 -> (st, e, bvs, []))))
                      | Fstarcompiler.FStarC_Reflection_V1_Data.Tv_UInst
                          (uu___2, uu___3) ->
                          Obj.magic
                            (Obj.repr
                               (FStar_Tactics_Effect.lift_div_tac
                                  (fun uu___4 -> (st, e, bvs, []))))
                      | Fstarcompiler.FStarC_Reflection_V1_Data.Tv_FVar
                          uu___2 ->
                          Obj.magic
                            (Obj.repr
                               (FStar_Tactics_Effect.lift_div_tac
                                  (fun uu___3 -> (st, e, bvs, []))))
                      | Fstarcompiler.FStarC_Reflection_V1_Data.Tv_Const
                          uu___2 ->
                          Obj.magic
                            (Obj.repr
                               (FStar_Tactics_Effect.lift_div_tac
                                  (fun uu___3 -> (st, e, bvs, []))))
                      | Fstarcompiler.FStarC_Reflection_V1_Data.Tv_Abs
                          (b, e1) ->
                          Obj.magic
                            (Obj.repr
                               (let uu___2 =
                                  visit_body t_i index_bv inv_bv st bvs e1 in
                                FStar_Tactics_Effect.tac_bind
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Meta.Interface.fst"
                                           (Prims.of_int (566))
                                           (Prims.of_int (28))
                                           (Prims.of_int (566))
                                           (Prims.of_int (67)))))
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Meta.Interface.fst"
                                           (Prims.of_int (565))
                                           (Prims.of_int (17))
                                           (Prims.of_int (568))
                                           (Prims.of_int (21)))))
                                  (Obj.magic uu___2)
                                  (fun uu___3 ->
                                     (fun uu___3 ->
                                        match uu___3 with
                                        | (st1, e2, bvs1, ses) ->
                                            let uu___4 =
                                              FStarC_Tactics_V1_Builtins.pack
                                                (Fstarcompiler.FStarC_Reflection_V1_Data.Tv_Abs
                                                   (b, e2)) in
                                            Obj.magic
                                              (FStar_Tactics_Effect.tac_bind
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Meta.Interface.fst"
                                                          (Prims.of_int (567))
                                                          (Prims.of_int (14))
                                                          (Prims.of_int (567))
                                                          (Prims.of_int (31)))))
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Meta.Interface.fst"
                                                          (Prims.of_int (568))
                                                          (Prims.of_int (6))
                                                          (Prims.of_int (568))
                                                          (Prims.of_int (21)))))
                                                 (Obj.magic uu___4)
                                                 (fun e3 ->
                                                    FStar_Tactics_Effect.lift_div_tac
                                                      (fun uu___5 ->
                                                         (st1, e3, bvs1, ses)))))
                                       uu___3)))
                      | Fstarcompiler.FStarC_Reflection_V1_Data.Tv_Match
                          (scrut, _returns, branches) ->
                          Obj.magic
                            (Obj.repr
                               (let uu___2 =
                                  visit_body t_i index_bv inv_bv st bvs scrut in
                                FStar_Tactics_Effect.tac_bind
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Meta.Interface.fst"
                                           (Prims.of_int (571))
                                           (Prims.of_int (32))
                                           (Prims.of_int (571))
                                           (Prims.of_int (75)))))
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Meta.Interface.fst"
                                           (Prims.of_int (570))
                                           (Prims.of_int (39))
                                           (Prims.of_int (575))
                                           (Prims.of_int (66)))))
                                  (Obj.magic uu___2)
                                  (fun uu___3 ->
                                     (fun uu___3 ->
                                        match uu___3 with
                                        | (st1, scrut1, bvs1, ses) ->
                                            let uu___4 =
                                              Obj.magic
                                                (FStar_Tactics_Effect.lift_div_tac
                                                   (fun uu___5 ->
                                                      FStar_List_Tot_Base.split
                                                        branches)) in
                                            Obj.magic
                                              (FStar_Tactics_Effect.tac_bind
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Meta.Interface.fst"
                                                          (Prims.of_int (572))
                                                          (Prims.of_int (21))
                                                          (Prims.of_int (572))
                                                          (Prims.of_int (44)))))
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Meta.Interface.fst"
                                                          (Prims.of_int (571))
                                                          (Prims.of_int (78))
                                                          (Prims.of_int (575))
                                                          (Prims.of_int (66)))))
                                                 (Obj.magic uu___4)
                                                 (fun uu___5 ->
                                                    (fun uu___5 ->
                                                       match uu___5 with
                                                       | (pats, es) ->
                                                           let uu___6 =
                                                             visit_many t_i
                                                               index_bv
                                                               inv_bv st1
                                                               bvs1 es in
                                                           Obj.magic
                                                             (FStar_Tactics_Effect.tac_bind
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (573))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (573))
                                                                    (Prims.of_int (70)))))
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (572))
                                                                    (Prims.of_int (47))
                                                                    (Prims.of_int (575))
                                                                    (Prims.of_int (66)))))
                                                                (Obj.magic
                                                                   uu___6)
                                                                (fun uu___7
                                                                   ->
                                                                   (fun
                                                                    uu___7 ->
                                                                    match uu___7
                                                                    with
                                                                    | 
                                                                    (st2,
                                                                    es1,
                                                                    bvs2,
                                                                    ses') ->
                                                                    let uu___8
                                                                    =
                                                                    zip pats
                                                                    es1 in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (574))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (574))
                                                                    (Prims.of_int (32)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (575))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (575))
                                                                    (Prims.of_int (66)))))
                                                                    (Obj.magic
                                                                    uu___8)
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    branches1
                                                                    ->
                                                                    let uu___9
                                                                    =
                                                                    FStarC_Tactics_V1_Builtins.pack
                                                                    (Fstarcompiler.FStarC_Reflection_V1_Data.Tv_Match
                                                                    (scrut1,
                                                                    _returns,
                                                                    branches1)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (575))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (575))
                                                                    (Prims.of_int (49)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (575))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (575))
                                                                    (Prims.of_int (66)))))
                                                                    (Obj.magic
                                                                    uu___9)
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    (st2,
                                                                    uu___10,
                                                                    bvs2,
                                                                    (FStar_List_Tot_Base.op_At
                                                                    ses ses'))))))
                                                                    uu___9)))
                                                                    uu___7)))
                                                      uu___5))) uu___3)))
                      | Fstarcompiler.FStarC_Reflection_V1_Data.Tv_Let
                          (r, attrs, bv, ty, e1, e2) ->
                          Obj.magic
                            (Obj.repr
                               (let uu___2 =
                                  visit_body t_i index_bv inv_bv st bvs e1 in
                                FStar_Tactics_Effect.tac_bind
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Meta.Interface.fst"
                                           (Prims.of_int (578))
                                           (Prims.of_int (29))
                                           (Prims.of_int (578))
                                           (Prims.of_int (69)))))
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Meta.Interface.fst"
                                           (Prims.of_int (577))
                                           (Prims.of_int (33))
                                           (Prims.of_int (581))
                                           (Prims.of_int (28)))))
                                  (Obj.magic uu___2)
                                  (fun uu___3 ->
                                     (fun uu___3 ->
                                        match uu___3 with
                                        | (st1, e11, bvs1, ses) ->
                                            let uu___4 =
                                              visit_body t_i index_bv inv_bv
                                                st1 bvs1 e2 in
                                            Obj.magic
                                              (FStar_Tactics_Effect.tac_bind
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Meta.Interface.fst"
                                                          (Prims.of_int (579))
                                                          (Prims.of_int (30))
                                                          (Prims.of_int (579))
                                                          (Prims.of_int (70)))))
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Meta.Interface.fst"
                                                          (Prims.of_int (578))
                                                          (Prims.of_int (72))
                                                          (Prims.of_int (581))
                                                          (Prims.of_int (28)))))
                                                 (Obj.magic uu___4)
                                                 (fun uu___5 ->
                                                    (fun uu___5 ->
                                                       match uu___5 with
                                                       | (st2, e21, bvs2,
                                                          ses') ->
                                                           let uu___6 =
                                                             FStarC_Tactics_V1_Builtins.pack
                                                               (Fstarcompiler.FStarC_Reflection_V1_Data.Tv_Let
                                                                  (r, attrs,
                                                                    bv, ty,
                                                                    e11, e21)) in
                                                           Obj.magic
                                                             (FStar_Tactics_Effect.tac_bind
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (580))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (580))
                                                                    (Prims.of_int (47)))))
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Meta.Interface.fst"
                                                                    (Prims.of_int (581))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (581))
                                                                    (Prims.of_int (28)))))
                                                                (Obj.magic
                                                                   uu___6)
                                                                (fun e3 ->
                                                                   FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    (st2, e3,
                                                                    bvs2,
                                                                    (FStar_List_Tot_Base.op_At
                                                                    ses ses'))))))
                                                      uu___5))) uu___3)))
                      | Fstarcompiler.FStarC_Reflection_V1_Data.Tv_AscribedT
                          (e1, t, tac, use_eq) ->
                          Obj.magic
                            (Obj.repr
                               (let uu___2 =
                                  visit_body t_i index_bv inv_bv st bvs e1 in
                                FStar_Tactics_Effect.tac_bind
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Meta.Interface.fst"
                                           (Prims.of_int (584))
                                           (Prims.of_int (28))
                                           (Prims.of_int (584))
                                           (Prims.of_int (67)))))
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Meta.Interface.fst"
                                           (Prims.of_int (583))
                                           (Prims.of_int (34))
                                           (Prims.of_int (586))
                                           (Prims.of_int (21)))))
                                  (Obj.magic uu___2)
                                  (fun uu___3 ->
                                     (fun uu___3 ->
                                        match uu___3 with
                                        | (st1, e2, bvs1, ses) ->
                                            let uu___4 =
                                              FStarC_Tactics_V1_Builtins.pack
                                                (Fstarcompiler.FStarC_Reflection_V1_Data.Tv_AscribedT
                                                   (e2, t, tac, use_eq)) in
                                            Obj.magic
                                              (FStar_Tactics_Effect.tac_bind
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Meta.Interface.fst"
                                                          (Prims.of_int (585))
                                                          (Prims.of_int (14))
                                                          (Prims.of_int (585))
                                                          (Prims.of_int (48)))))
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Meta.Interface.fst"
                                                          (Prims.of_int (586))
                                                          (Prims.of_int (6))
                                                          (Prims.of_int (586))
                                                          (Prims.of_int (21)))))
                                                 (Obj.magic uu___4)
                                                 (fun e3 ->
                                                    FStar_Tactics_Effect.lift_div_tac
                                                      (fun uu___5 ->
                                                         (st1, e3, bvs1, ses)))))
                                       uu___3)))
                      | Fstarcompiler.FStarC_Reflection_V1_Data.Tv_AscribedC
                          (e1, c, tac, use_eq) ->
                          Obj.magic
                            (Obj.repr
                               (let uu___2 =
                                  visit_body t_i index_bv inv_bv st bvs e1 in
                                FStar_Tactics_Effect.tac_bind
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Meta.Interface.fst"
                                           (Prims.of_int (589))
                                           (Prims.of_int (28))
                                           (Prims.of_int (589))
                                           (Prims.of_int (67)))))
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Meta.Interface.fst"
                                           (Prims.of_int (588))
                                           (Prims.of_int (34))
                                           (Prims.of_int (591))
                                           (Prims.of_int (21)))))
                                  (Obj.magic uu___2)
                                  (fun uu___3 ->
                                     (fun uu___3 ->
                                        match uu___3 with
                                        | (st1, e2, bvs1, ses) ->
                                            let uu___4 =
                                              FStarC_Tactics_V1_Builtins.pack
                                                (Fstarcompiler.FStarC_Reflection_V1_Data.Tv_AscribedC
                                                   (e2, c, tac, use_eq)) in
                                            Obj.magic
                                              (FStar_Tactics_Effect.tac_bind
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Meta.Interface.fst"
                                                          (Prims.of_int (590))
                                                          (Prims.of_int (14))
                                                          (Prims.of_int (590))
                                                          (Prims.of_int (48)))))
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Meta.Interface.fst"
                                                          (Prims.of_int (591))
                                                          (Prims.of_int (6))
                                                          (Prims.of_int (591))
                                                          (Prims.of_int (21)))))
                                                 (Obj.magic uu___4)
                                                 (fun e3 ->
                                                    FStar_Tactics_Effect.lift_div_tac
                                                      (fun uu___5 ->
                                                         (st1, e3, bvs1, ses)))))
                                       uu___3)))
                      | Fstarcompiler.FStarC_Reflection_V1_Data.Tv_Arrow
                          (uu___2, uu___3) ->
                          Obj.magic
                            (Obj.repr
                               (FStar_Tactics_Effect.lift_div_tac
                                  (fun uu___4 -> (st, e, bvs, []))))
                      | Fstarcompiler.FStarC_Reflection_V1_Data.Tv_Type
                          uu___2 ->
                          Obj.magic
                            (Obj.repr
                               (FStar_Tactics_Effect.lift_div_tac
                                  (fun uu___3 -> (st, e, bvs, []))))
                      | Fstarcompiler.FStarC_Reflection_V1_Data.Tv_Uvar
                          (uu___2, uu___3) ->
                          Obj.magic
                            (Obj.repr
                               (FStar_Tactics_Effect.lift_div_tac
                                  (fun uu___4 -> (st, e, bvs, []))))
                      | Fstarcompiler.FStarC_Reflection_V1_Data.Tv_Refine
                          (uu___2, uu___3, uu___4) ->
                          Obj.magic
                            (Obj.repr
                               (FStar_Tactics_Effect.lift_div_tac
                                  (fun uu___5 -> (st, e, bvs, []))))
                      | Fstarcompiler.FStarC_Reflection_V1_Data.Tv_Unknown ->
                          Obj.magic
                            (Obj.repr
                               (FStar_Tactics_Effect.lift_div_tac
                                  (fun uu___2 -> (st, e, bvs, []))))
                      | uu___2 ->
                          Obj.magic
                            (Obj.repr
                               (FStar_Tactics_Effect.lift_div_tac
                                  (fun uu___3 -> (st, e, bvs, []))))) uu___1)
let (specialize :
  Fstarcompiler.FStarC_Reflection_Types.term ->
    Fstarcompiler.FStarC_Reflection_Types.term Prims.list ->
      (Fstarcompiler.FStarC_Reflection_Types.decls, unit)
        FStar_Tactics_Effect.tac_repr)
  =
  fun t_i ->
    fun names ->
      let uu___ =
        FStar_Tactics_Util.map
          (fun name ->
             let uu___1 = FStarC_Tactics_V1_Builtins.inspect name in
             FStar_Tactics_Effect.tac_bind
               (FStar_Sealed.seal
                  (Obj.magic
                     (FStar_Range.mk_range "Meta.Interface.fst"
                        (Prims.of_int (607)) (Prims.of_int (10))
                        (Prims.of_int (607)) (Prims.of_int (22)))))
               (FStar_Sealed.seal
                  (Obj.magic
                     (FStar_Range.mk_range "Meta.Interface.fst"
                        (Prims.of_int (607)) (Prims.of_int (4))
                        (Prims.of_int (610)) (Prims.of_int (71)))))
               (Obj.magic uu___1)
               (fun uu___2 ->
                  match uu___2 with
                  | Fstarcompiler.FStarC_Reflection_V1_Data.Tv_UInst
                      (fv, uu___3) ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___4 ->
                           Fstarcompiler.FStarC_Reflection_V1_Builtins.inspect_fv
                             fv)
                  | Fstarcompiler.FStarC_Reflection_V1_Data.Tv_FVar fv ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___3 ->
                           Fstarcompiler.FStarC_Reflection_V1_Builtins.inspect_fv
                             fv)
                  | uu___3 ->
                      FStar_Tactics_V1_Derived.fail
                        "error: argument to specialize is not a top-level name"))
          names in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Meta.Interface.fst" (Prims.of_int (606))
                 (Prims.of_int (14)) (Prims.of_int (611)) (Prims.of_int (9)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Meta.Interface.fst" (Prims.of_int (611))
                 (Prims.of_int (12)) (Prims.of_int (618)) (Prims.of_int (5)))))
        (Obj.magic uu___)
        (fun uu___1 ->
           (fun names1 ->
              let uu___1 =
                Obj.magic
                  (FStar_Tactics_Effect.lift_div_tac
                     (fun uu___2 -> { seen = []; indent = "" })) in
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Meta.Interface.fst"
                            (Prims.of_int (612)) (Prims.of_int (13))
                            (Prims.of_int (612)) (Prims.of_int (35)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Meta.Interface.fst"
                            (Prims.of_int (612)) (Prims.of_int (40))
                            (Prims.of_int (618)) (Prims.of_int (5)))))
                   (Obj.magic uu___1)
                   (fun uu___2 ->
                      (fun st ->
                         let uu___2 =
                           FStar_Tactics_Util.fold_left
                             (fun uu___3 ->
                                fun name ->
                                  match uu___3 with
                                  | (st1, ses) ->
                                      let uu___4 =
                                        visit_function t_i st1 name in
                                      FStar_Tactics_Effect.tac_bind
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Meta.Interface.fst"
                                                 (Prims.of_int (614))
                                                 (Prims.of_int (19))
                                                 (Prims.of_int (614))
                                                 (Prims.of_int (45)))))
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Meta.Interface.fst"
                                                 (Prims.of_int (613))
                                                 (Prims.of_int (47))
                                                 (Prims.of_int (616))
                                                 (Prims.of_int (18)))))
                                        (Obj.magic uu___4)
                                        (fun uu___5 ->
                                           (fun uu___5 ->
                                              match uu___5 with
                                              | (st2, ses') ->
                                                  let uu___6 =
                                                    FStarC_Tactics_V1_Builtins.print
                                                      (Prims.strcat
                                                         (Prims.string_of_int
                                                            (FStar_List_Tot_Base.length
                                                               ses'))
                                                         " declarations generated") in
                                                  Obj.magic
                                                    (FStar_Tactics_Effect.tac_bind
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Meta.Interface.fst"
                                                                (Prims.of_int (615))
                                                                (Prims.of_int (4))
                                                                (Prims.of_int (615))
                                                                (Prims.of_int (72)))))
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Meta.Interface.fst"
                                                                (Prims.of_int (616))
                                                                (Prims.of_int (4))
                                                                (Prims.of_int (616))
                                                                (Prims.of_int (18)))))
                                                       (Obj.magic uu___6)
                                                       (fun uu___7 ->
                                                          FStar_Tactics_Effect.lift_div_tac
                                                            (fun uu___8 ->
                                                               (st2,
                                                                 (FStar_List_Tot_Base.op_At
                                                                    ses ses'))))))
                                             uu___5)) (st, []) names1 in
                         Obj.magic
                           (FStar_Tactics_Effect.tac_bind
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Meta.Interface.fst"
                                       (Prims.of_int (613))
                                       (Prims.of_int (15))
                                       (Prims.of_int (617))
                                       (Prims.of_int (18)))))
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Meta.Interface.fst"
                                       (Prims.of_int (612))
                                       (Prims.of_int (40))
                                       (Prims.of_int (618))
                                       (Prims.of_int (5)))))
                              (Obj.magic uu___2)
                              (fun uu___3 ->
                                 FStar_Tactics_Effect.lift_div_tac
                                   (fun uu___4 ->
                                      match uu___3 with
                                      | (uu___5, ses) -> ses)))) uu___2)))
             uu___1)
let _ =
  Fstarcompiler.FStarC_Tactics_Native.register_tactic
    "Meta.Interface.specialize" (Prims.of_int (3))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             Fstarcompiler.FStarC_Tactics_InterpFuns.mk_tactic_interpretation_2
               "Meta.Interface.specialize (plugin)"
               (Fstarcompiler.FStarC_Tactics_Native.from_tactic_2 specialize)
               Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_term
               (Fstarcompiler.FStarC_Syntax_Embeddings.e_list
                  Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_term)
               (Fstarcompiler.FStarC_Syntax_Embeddings.e_list
                  Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_sigelt) psc
               ncb us args)