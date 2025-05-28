module MLS.Crypto.Derived.Symbolic.ExpandWithLabel

open FStar.List.Tot { for_allP, for_allP_eq }
open Comparse
open DY.Core
open DY.Lib
open MLS.NetworkTypes
open MLS.Crypto
open MLS.Crypto.Derived.Lemmas
open MLS.Symbolic
open MLS.Result

#set-options "--fuel 0 --ifuel 0"

(*** Split usage for ExpandWithLabel ***)

noeq
type expandwithlabel_crypto_usage = {
  get_usage:
    prk_usage:usage{KdfExpandKey? prk_usage} ->
    context:bytes ->
    length:nat ->
    usage;

  get_label:
    prk_usage:usage{KdfExpandKey? prk_usage} -> prk_label:label ->
    context:bytes ->
    length:nat ->
    label;

  get_label_lemma:
    tr:trace ->
    prk_usage:usage{KdfExpandKey? prk_usage} -> prk_label:label ->
    context:bytes ->
    length:nat ->
    Lemma ((get_label prk_usage prk_label context length) `can_flow tr` prk_label)
  ;
}

val default_expandwithlabel_crypto_usage: expandwithlabel_crypto_usage
let default_expandwithlabel_crypto_usage = {
  get_usage = (fun prk_usage context length -> NoUsage);
  get_label = (fun prk_usage prk_label context length -> prk_label);
  get_label_lemma = (fun tr prk_usage prk_label context length -> ());
}

let split_expandwithlabel_get_usage_params: split_function_parameters = {
  tag_set_t = valid_label;
  tag_t = MLS.NetworkTypes.mls_ascii_string;
  is_disjoint = unequal;
  tag_belong_to = (fun tag tag_set ->
    tag = get_mls_label tag_set
  );
  cant_belong_to_disjoint_sets = (fun tag tag_set_1 tag_set_2 ->
    FStar.Classical.move_requires_2 get_mls_label_inj tag_set_1 tag_set_2
  );

  tagged_data_t = (prk_usage:usage{KdfExpandKey? prk_usage}) & bytes;
  raw_data_t = (prk_usage:usage{KdfExpandKey? prk_usage}) & bytes & nat;
  output_t = usage;

  decode_tagged_data = (fun (prk_usage, info) ->
    match parse (kdf_label_nt bytes) info with
    | Some {label; context; length} -> Some (label, (prk_usage, context, length))
    | None -> None
  );

  local_fun_t = mk_dependent_type expandwithlabel_crypto_usage;
  global_fun_t = prk_usage:usage{KdfExpandKey? prk_usage} -> info:bytes -> usage;

  default_global_fun = (fun prk_usage info -> NoUsage);

  apply_local_fun = (fun lfun (prk_usage, context, length) ->
    lfun.get_usage prk_usage context length
  );
  apply_global_fun = (fun gfun (prk_usage, info) ->
    gfun prk_usage info
  );
  mk_global_fun = (fun gfun prk_usage info ->
    gfun (prk_usage, info)
  );
  apply_mk_global_fun = (fun bare x -> ());
}

let split_expandwithlabel_get_label_params = {
  tag_set_t = valid_label;
  tag_t = MLS.NetworkTypes.mls_ascii_string;
  is_disjoint = unequal;
  tag_belong_to = (fun tag tag_set ->
    tag = get_mls_label tag_set
  );
  cant_belong_to_disjoint_sets = (fun tag tag_set_1 tag_set_2 ->
    FStar.Classical.move_requires_2 get_mls_label_inj tag_set_1 tag_set_2
  );

  tagged_data_t = (prk_usage:usage{KdfExpandKey? prk_usage}) & label & bytes;
  raw_data_t = (prk_usage:usage{KdfExpandKey? prk_usage}) & label & bytes & nat;
  output_t = label;

  decode_tagged_data = (fun (prk_usage, prk_label, info) ->
    match parse (kdf_label_nt bytes) info with
    | Some {label; context; length} -> Some (label, (prk_usage, prk_label, context, length))
    | None -> None
  );

  local_fun_t = mk_dependent_type expandwithlabel_crypto_usage;
  global_fun_t = prk_usage:usage{KdfExpandKey? prk_usage} -> prk_label:label -> info:bytes -> label;

  default_global_fun = (fun prk_usage prk_label info -> prk_label);

  apply_local_fun = (fun lfun (prk_usage, prk_label, context, length) ->
    lfun.get_label prk_usage prk_label context length
  );
  apply_global_fun = (fun gfun (prk_usage, prk_label, info) ->
    gfun prk_usage prk_label info
  );
  mk_global_fun = (fun gfun prk_usage prk_label info ->
    gfun (prk_usage, prk_label, info)
  );
  apply_mk_global_fun = (fun bare x -> ());
}

val has_expandwithlabel_usage_get_usage: kdf_expand_crypto_usage -> (valid_label & expandwithlabel_crypto_usage) -> prop
let has_expandwithlabel_usage_get_usage kdf_expand_usage (lab, local_fun) =
  forall prk_usage info.
    {:pattern kdf_expand_usage.get_usage prk_usage info}
    match parse (kdf_label_nt bytes) info with
    | Some {label; context; length} -> (
      label == get_mls_label lab ==> (
        kdf_expand_usage.get_usage prk_usage info == local_fun.get_usage prk_usage context length
      )
    )
    | _ -> True

val has_expandwithlabel_usage_get_label: kdf_expand_crypto_usage -> (valid_label & expandwithlabel_crypto_usage) -> prop
let has_expandwithlabel_usage_get_label kdf_expand_usage (lab, local_fun) =
  forall prk_usage prk_label info.
    {:pattern kdf_expand_usage.get_label prk_usage prk_label info}
    match parse (kdf_label_nt bytes) info with
    | Some {label; context; length} -> (
      label == get_mls_label lab ==> (
        kdf_expand_usage.get_label prk_usage prk_label info == local_fun.get_label prk_usage prk_label context length
      )
    )
    | _ -> True

val has_expandwithlabel_usage: kdf_expand_crypto_usage -> (valid_label & expandwithlabel_crypto_usage) -> prop
let has_expandwithlabel_usage kdf_expand_usage (lab, local_fun) =
  has_expandwithlabel_usage_get_usage kdf_expand_usage (lab, local_fun) /\
  has_expandwithlabel_usage_get_label kdf_expand_usage (lab, local_fun)

// F* is extremely slow on this one, even with --lax?
val intro_has_expandwithlabel_usage_get_usage:
  kdf_expand_usage:kdf_expand_crypto_usage -> tag:valid_label -> local_fun:expandwithlabel_crypto_usage ->
  Lemma
  (requires has_local_fun split_expandwithlabel_get_usage_params kdf_expand_usage.get_usage (|tag, local_fun|))
  (ensures has_expandwithlabel_usage_get_usage kdf_expand_usage (tag, local_fun))
let intro_has_expandwithlabel_usage_get_usage kdf_expand_usage tag local_fun =
  introduce
    forall prk_usage info.
      match parse (kdf_label_nt bytes) info with
      | Some {label; context; length} -> (
        label == get_mls_label tag ==> (
          kdf_expand_usage.get_usage prk_usage info == local_fun.get_usage prk_usage context length
        )
      )
      | _ -> True
  with (
    has_local_fun_elim split_expandwithlabel_get_usage_params kdf_expand_usage.get_usage tag local_fun (prk_usage, info)
  )

// F* is extremely slow on this one, even with --lax?
val intro_has_expandwithlabel_usage_get_label:
  kdf_expand_usage:kdf_expand_crypto_usage -> tag:valid_label -> local_fun:expandwithlabel_crypto_usage ->
  Lemma
  (requires has_local_fun split_expandwithlabel_get_label_params kdf_expand_usage.get_label (|tag, local_fun|))
  (ensures has_expandwithlabel_usage_get_label kdf_expand_usage (tag, local_fun))
let intro_has_expandwithlabel_usage_get_label kdf_expand_usage tag local_fun =
  introduce
    forall prk_usage prk_label info.
      match parse (kdf_label_nt bytes) info with
      | Some {label; context; length} -> (
        label == get_mls_label tag ==> (
          kdf_expand_usage.get_label prk_usage prk_label info == local_fun.get_label prk_usage prk_label context length
        )
      )
      | _ -> True
  with (
    has_local_fun_elim split_expandwithlabel_get_label_params kdf_expand_usage.get_label tag local_fun (prk_usage, prk_label, info)
  )

val mk_global_kdf_expand_usage_get_usage:
  list (valid_label & expandwithlabel_crypto_usage) ->
  prk_usage:usage{KdfExpandKey? prk_usage} -> bytes -> usage
let mk_global_kdf_expand_usage_get_usage tagged_local_usages =
  mk_global_fun split_expandwithlabel_get_usage_params (mk_dependent_tagged_local_funs tagged_local_usages)

val mk_global_kdf_expand_usage_get_label:
  list (valid_label & expandwithlabel_crypto_usage) ->
  prk_usage:usage{KdfExpandKey? prk_usage} -> label -> bytes -> label
let mk_global_kdf_expand_usage_get_label tagged_local_usages =
  mk_global_fun split_expandwithlabel_get_label_params (mk_dependent_tagged_local_funs tagged_local_usages)

#push-options "--ifuel 2 --z3rlimit 15"
val mk_global_kdf_expand_usage_get_label_lemma:
  tagged_local_usages:list (valid_label & expandwithlabel_crypto_usage) ->
  tr:trace ->
  prk_usage:usage{KdfExpandKey? prk_usage} -> prk_label:label -> info:bytes ->
  Lemma (mk_global_kdf_expand_usage_get_label tagged_local_usages prk_usage prk_label info `can_flow tr` prk_label)
let mk_global_kdf_expand_usage_get_label_lemma tagged_local_usages tr prk_usage prk_label info =
  let params = split_expandwithlabel_get_label_params in
  mk_global_fun_eq params (mk_dependent_tagged_local_funs tagged_local_usages) (prk_usage, prk_label, info);
  match parse (kdf_label_nt bytes) info with
  | Some {label; context; length} -> (
    introduce forall tag_set local_usage. params.apply_local_fun #tag_set local_usage (prk_usage, prk_label, (context <: bytes), (length <: nat)) `can_flow tr` prk_label with (
      local_usage.get_label_lemma tr prk_usage prk_label context length
    )
  )
  | None -> ()
#pop-options

val mk_kdf_expand_mls_usage:
  list (valid_label & expandwithlabel_crypto_usage) ->
  kdf_expand_crypto_usage
let mk_kdf_expand_mls_usage tagged_local_usages = {
  get_usage = mk_global_kdf_expand_usage_get_usage tagged_local_usages;
  get_label = mk_global_kdf_expand_usage_get_label tagged_local_usages;
  get_label_lemma = mk_global_kdf_expand_usage_get_label_lemma tagged_local_usages;
}

#push-options "--ifuel 1"
val mk_kdf_expand_mls_usage_correct:
  kdf_expand_usage:kdf_expand_crypto_usage -> tagged_local_usages:list (valid_label & expandwithlabel_crypto_usage) ->
  Lemma
  (requires
    kdf_expand_usage == mk_kdf_expand_mls_usage tagged_local_usages /\
    List.Tot.no_repeats_p (List.Tot.map fst tagged_local_usages)
  )
  (ensures for_allP (has_expandwithlabel_usage kdf_expand_usage) tagged_local_usages)
let mk_kdf_expand_mls_usage_correct kdf_expand_usage tagged_local_usages =
  no_repeats_p_implies_for_all_pairsP_unequal (List.Tot.map fst tagged_local_usages);
  map_dfst_mk_dependent_tagged_local_funs tagged_local_usages;
  for_allP_eq (has_expandwithlabel_usage kdf_expand_usage) tagged_local_usages;
  FStar.Classical.forall_intro_2 (memP_mk_dependent_tagged_local_funs tagged_local_usages);
  FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 (mk_global_fun_correct split_expandwithlabel_get_usage_params (mk_dependent_tagged_local_funs tagged_local_usages)));
  FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 (mk_global_fun_correct split_expandwithlabel_get_label_params (mk_dependent_tagged_local_funs tagged_local_usages)));
  FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 (intro_has_expandwithlabel_usage_get_usage kdf_expand_usage));
  FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 (intro_has_expandwithlabel_usage_get_label kdf_expand_usage))
#pop-options

val has_mls_expandwithlabel_usage: {|crypto_usages|} -> (string & valid_label & expandwithlabel_crypto_usage) -> prop
let has_mls_expandwithlabel_usage #cusgs (usage_tag, lab, local_usage) =
  exists kdf_expand_usage.
    has_kdf_expand_usage (usage_tag, kdf_expand_usage) /\
    has_expandwithlabel_usage kdf_expand_usage (lab, local_usage)

(*** Modular lemmas on ExpandWithLabel ***)

val bytes_invariant_expand_with_label:
  {|crypto_invariants|} ->
  tr:trace ->
  secret:bytes -> secret_usage:usage -> label:valid_label -> context:bytes -> len:nat ->
  Lemma
  (requires
    bytes_invariant tr secret /\
    bytes_invariant tr context /\
    secret `has_usage tr` secret_usage /\
    KdfExpandKey? secret_usage
  )
  (ensures (
    match expand_with_label secret label context len with
    | Success res -> bytes_invariant tr res
    | _ -> True
  ))
let bytes_invariant_expand_with_label #cinvs tr secret secret_usage label context length =
  match expand_with_label secret label context length with
  | Success res -> (
    serialize_wf_lemma (kdf_label_nt bytes) (bytes_invariant tr) {
      length;
      label = get_mls_label label;
      context;
    }
  )
  | _ -> ()

val get_label_expand_with_label:
  {|crypto_usages|} ->
  tr:trace ->
  usage_tag:string -> local_usage:expandwithlabel_crypto_usage ->
  secret:bytes -> secret_usage:usage -> label:valid_label -> context:bytes -> len:nat ->
  Lemma
  (requires (
    secret `has_usage tr` secret_usage /\
    (exists usage_data. secret_usage == KdfExpandKey usage_tag usage_data) /\
    has_mls_expandwithlabel_usage (usage_tag, label, local_usage)
  ))
  (ensures (
    match expand_with_label secret label context len with
    | Success res -> (
      get_label tr res `equivalent tr` local_usage.get_label secret_usage (get_label tr secret) context len
    )
    | _ -> True
  ))
let get_label_expand_with_label #cinvs tr usage_tag local_usage secret secret_usage label context length =
  match expand_with_label secret label context length with
  | Success res -> (
    let info = {
      length;
      label = get_mls_label label;
      context;
    } in
    assert(parse (kdf_label_nt bytes) (serialize _ info <: bytes) == Some info)
  )
  | _ -> ()

val get_label_expand_with_label_can_flow:
  {|crypto_usages|} ->
  tr:trace ->
  secret:bytes -> label:valid_label -> context:bytes -> len:nat ->
  Lemma
  (ensures (
    match expand_with_label secret label context len with
    | Success res -> (
      get_label tr res `can_flow tr` get_label tr secret
    )
    | _ -> True
  ))
let get_label_expand_with_label_can_flow #cinvs tr secret label context length =
  match expand_with_label secret label context length with
  | Success res -> ()
  | _ -> ()

val has_usage_expand_with_label:
  {|crypto_usages|} ->
  tr:trace ->
  usage_tag:string -> local_usage:expandwithlabel_crypto_usage ->
  secret:bytes -> secret_usage:usage -> label:valid_label -> context:bytes -> len:nat ->
  Lemma
  (requires (
    secret `has_usage tr` secret_usage /\
    (exists usage_data. secret_usage == KdfExpandKey usage_tag usage_data) /\
    has_mls_expandwithlabel_usage (usage_tag, label, local_usage)
  ))
  (ensures (
    match expand_with_label secret label context len with
    | Success res -> (
      res `has_usage tr` local_usage.get_usage secret_usage context len
    )
    | _ -> True
  ))
let has_usage_expand_with_label #cinvs tr usage_tag local_usage secret secret_usage label context length =
  match expand_with_label secret label context length with
  | Success res -> (
    let info = {
      length;
      label = get_mls_label label;
      context;
    } in
    assert(parse (kdf_label_nt bytes) (serialize _ info <: bytes) == Some info)
  )
  | _ -> ()

// This combined lemma is useful

val expand_with_label_lemma:
  {|crypto_invariants|} ->
  tr:trace ->
  usage_tag:string -> local_usage:expandwithlabel_crypto_usage ->
  secret:bytes -> secret_usage:usage -> label:valid_label -> context:bytes -> len:nat ->
  Lemma
  (requires (
    bytes_invariant tr secret /\
    bytes_invariant tr context /\
    secret `has_usage tr` secret_usage /\
    (exists usage_data. secret_usage == KdfExpandKey usage_tag usage_data) /\
    has_mls_expandwithlabel_usage (usage_tag, label, local_usage)
  ))
  (ensures (
    match expand_with_label secret label context len with
    | Success res -> (
      bytes_invariant tr res /\
      res `has_usage tr` local_usage.get_usage secret_usage context len /\
      get_label tr res `equivalent tr` local_usage.get_label secret_usage (get_label tr secret) context len
    )
    | _ -> True
  ))
let expand_with_label_lemma #cinvs tr usage_tag local_usage secret secret_usage label context length =
  match expand_with_label secret label context length with
  | Success res -> (
    bytes_invariant_expand_with_label tr secret secret_usage label context length;
    has_usage_expand_with_label tr usage_tag local_usage secret secret_usage label context length;
    get_label_expand_with_label tr usage_tag local_usage secret secret_usage label context length
  )
  | _ -> ()

val mk_secret_expandwithlabel_usage:
  usage ->
  expandwithlabel_crypto_usage
let mk_secret_expandwithlabel_usage usg = {
  get_usage = (fun prk_usage context length -> usg);
  get_label = (fun prk_usage prk_label context length -> prk_label);
  get_label_lemma = (fun tr prk_usage prk_label context length -> ());
}

val mk_public_expandwithlabel_usage:
  usage ->
  expandwithlabel_crypto_usage
let mk_public_expandwithlabel_usage usg = {
  get_usage = (fun prk_usage context length -> usg);
  get_label = (fun prk_usage prk_label context length -> public);
  get_label_lemma = (fun tr prk_usage prk_label context length -> ());
}
