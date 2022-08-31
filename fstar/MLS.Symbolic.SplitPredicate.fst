module MLS.Symbolic.SplitPredicate

#set-options "--fuel 1 --ifuel 1"

// Some kind of cheap module functor like ocaml but in F*
noeq type split_predicate_input_values = {
  label_t: Type;
  encoded_label_t: Type;
  raw_data_t: Type;
  labeled_data_t: Type;
  other_values_t: Type;

  decode_labeled_data: labeled_data_t -> option (encoded_label_t & raw_data_t);

  encode_label: label_t -> encoded_label_t;
  encode_label_inj: l1:label_t -> l2:label_t -> Lemma
    (requires encode_label l1 == encode_label l2)
    (ensures l1 == l2)
  ;
}

// Can probably be generalized to handle kdf usage too?
type global_pred (func:split_predicate_input_values) =
  func.labeled_data_t -> func.other_values_t -> prop
type local_pred (func:split_predicate_input_values) =
  func.raw_data_t -> func.other_values_t -> prop

type label_decoder (func:split_predicate_input_values) =
  func.labeled_data_t -> option (func.encoded_label_t & func.raw_data_t)

val has_local_pred: func:split_predicate_input_values -> global_pred func -> func.label_t -> local_pred func -> prop
let has_local_pred func gpred the_label lpred =
  forall labeled_data other_values.
    match func.decode_labeled_data labeled_data with
    | Some (label, raw_data) ->
      label == func.encode_label the_label ==> (gpred labeled_data other_values <==> lpred raw_data other_values)
    | None -> True

val mk_global_pred: func:split_predicate_input_values -> list (func.label_t & local_pred func) -> global_pred func
let rec mk_global_pred func l labeled_data other_values =
  match l with
  | [] -> False
  | (the_label, lpred)::t ->
    let cur_prop =
      match func.decode_labeled_data labeled_data with
      | Some (label, raw_data) ->
        label == func.encode_label the_label /\ lpred raw_data other_values
      | None -> False
    in
    cur_prop \/ mk_global_pred func t labeled_data other_values

val mk_global_pred_wrong_label: func:split_predicate_input_values -> the_label:func.label_t -> l:list (func.label_t & local_pred func) -> labeled_data:func.labeled_data_t -> other_values:func.other_values_t -> Lemma
  (requires ~(List.Tot.memP the_label (List.Tot.map fst l)))
  (ensures (
    match func.decode_labeled_data labeled_data with
    | Some (label, raw_data) ->
      label == func.encode_label the_label ==> ~(mk_global_pred func l labeled_data other_values)
    | None -> ~(mk_global_pred func l labeled_data other_values)
  ))
let rec mk_global_pred_wrong_label func the_label l labeled_data other_values =
  match l with
  | [] -> ()
  | (label, _)::t -> (
    FStar.Classical.move_requires_2 func.encode_label_inj the_label label;
    mk_global_pred_wrong_label func the_label t labeled_data other_values
  )

val disjointP: #a:Type -> list a -> list a -> prop
let rec disjointP #a l1 l2 =
  match l1 with
  | [] -> True
  | h1::t1 ->
    ~(List.Tot.memP h1 l2) /\ disjointP t1 l2

val disjointP_cons: #a:Type -> x:a -> l1:list a -> l2:list a -> Lemma
  (requires disjointP l1 l2 /\ ~(List.Tot.memP x l1))
  (ensures disjointP l1 (x::l2))
let rec disjointP_cons #a x l1 l2 =
  match l1 with
  | [] -> ()
  | h1::t1 -> disjointP_cons x t1 l2

val memP_map: #a:Type -> #b:Type -> x:a -> f:(a -> b) -> l:list a -> Lemma
  (requires List.Tot.memP x l)
  (ensures List.Tot.memP (f x) (List.Tot.map f l))
let rec memP_map #a #b x f l =
  match l with
  | [] -> ()
  | h::t ->
    introduce x =!= h ==> List.Tot.memP (f x) (List.Tot.map f t)
    with _. memP_map x f t

val mk_global_pred_correct_aux: func:split_predicate_input_values -> gpred:global_pred func -> lpreds1:list (func.label_t & local_pred func) -> lpreds2:list (func.label_t & local_pred func) -> the_label:func.label_t -> lpred:local_pred func -> Lemma
  (requires
    (forall labeled_data other_values. (mk_global_pred func lpreds1 labeled_data other_values \/ mk_global_pred func lpreds2 labeled_data other_values) <==> gpred labeled_data other_values) /\
    List.Tot.no_repeats_p (List.Tot.map fst lpreds1) /\
    disjointP (List.Tot.map fst lpreds1) (List.Tot.map fst lpreds2) /\
    List.Tot.memP (the_label, lpred) lpreds1
  )
  (ensures has_local_pred func gpred the_label lpred)
let rec mk_global_pred_correct_aux func gpred lpreds1 lpreds2 the_label lpred =
  match lpreds1 with
  | [] -> ()
  | (h_lab, h_spred)::t -> (
    eliminate h_lab == the_label \/ h_lab =!= the_label returns _ with _. (
      introduce forall labeled_data other_values. (
        match func.decode_labeled_data labeled_data with
        | Some (label, raw_data) ->
          label == func.encode_label the_label ==> (gpred labeled_data other_values <==> lpred raw_data other_values)
        | None -> True
      ) with (
        match func.decode_labeled_data labeled_data with
        | Some (label, raw_data) -> (
          eliminate label == func.encode_label the_label \/ label =!= func.encode_label the_label returns _ with _. (
            func.encode_label_inj the_label h_lab;
            mk_global_pred_wrong_label func the_label t labeled_data other_values;
            mk_global_pred_wrong_label func the_label lpreds2 labeled_data other_values;
            FStar.Classical.move_requires_3 memP_map (the_label, lpred) fst t
          ) and _. ()
        )
        | None -> ()
      )
    ) and _. (
      disjointP_cons h_lab (List.Tot.map fst t) (List.Tot.map fst lpreds2);
      mk_global_pred_correct_aux func gpred t ((h_lab, h_spred)::lpreds2) the_label lpred
    )
  )

val disjointP_nil: #a:Type -> l:list a -> Lemma (disjointP l [])
let rec disjointP_nil #a l =
  match l with
  | [] -> ()
  | _::t -> disjointP_nil t

val mk_global_pred_correct: func:split_predicate_input_values -> lpreds:list (func.label_t & local_pred func) -> the_label:func.label_t -> lpred:local_pred func -> Lemma
  (requires
    List.Tot.no_repeats_p (List.Tot.map fst lpreds) /\
    List.Tot.memP (the_label, lpred) lpreds
  )
  (ensures has_local_pred func (mk_global_pred func lpreds) the_label lpred)
let mk_global_pred_correct func lpreds the_label lpred =
  disjointP_nil (List.Tot.map fst lpreds);
  mk_global_pred_correct_aux func (mk_global_pred func lpreds) lpreds [] the_label lpred
