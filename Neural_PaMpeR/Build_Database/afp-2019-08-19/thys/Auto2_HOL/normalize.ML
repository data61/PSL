(*
  File: normalize.ML
  Author: Bohua Zhan

  Normalization procedure for facts obtained during a proof.
*)

type normalizer = Proof.context -> raw_item -> raw_item list

signature NORMALIZER =
sig
  val add_normalizer: string * normalizer -> theory -> theory
  val add_th_normalizer:
      string * (Proof.context -> thm -> thm list) -> theory -> theory
  val add_rewr_normalizer: string * thm -> theory -> theory
  val get_normalizers: theory -> (string * normalizer) list
  val normalize: Proof.context -> raw_item -> raw_item list
  val normalize_keep: Proof.context -> raw_item -> raw_item list

  (* Normalization of definition of variable *)
  val add_inj_struct_data: thm -> theory -> theory

  val is_def_eq: theory -> term -> bool
  val swap_eq_to_front: conv
  val meta_use_vardef: thm -> (term * term) list * thm
  val meta_use_vardefs: thm -> (term * term) list * thm
  val def_subst: (term * term) list -> term -> term
end;

structure Normalizer : NORMALIZER =
struct

(* Keeps list of normalizers. *)
structure Data = Theory_Data (
  type T = normalizer Symtab.table;
  val empty = Symtab.empty;
  val extend = I;
  val merge = Symtab.merge pointer_eq
)

fun add_normalizer (norm_name, norm_fun) =
    Data.map (Symtab.update_new (norm_name, norm_fun))

(* Apply norm_fun: thm -> thm list to any PROP item. *)
fun th_normalizer norm_fun ctxt ritem =
    case ritem of
        Handler _ => [ritem]
      | Fact (ty_str, _, th) =>
        if ty_str = TY_PROP then
          map Update.thm_to_ritem (norm_fun ctxt th)
        else [ritem]

fun add_th_normalizer (norm_name, norm_fun) =
    add_normalizer (norm_name, th_normalizer norm_fun)

(* eq_th is a meta equality. *)
fun rewr_normalizer eq_th ctxt ritem =
    let
      val cv = (Conv.top_conv (K (Conv.try_conv (Conv.rewr_conv eq_th))) ctxt)
                   then_conv (Thm.beta_conversion true)
    in
      case ritem of
          Handler _ => [ritem]
        | Fact (ty_str, _, th) =>
          if ty_str = TY_PROP then
            [Update.thm_to_ritem (apply_to_thm cv th)]
          else if ty_str = TY_EQ then
            if Util.is_meta_eq (Thm.prop_of th) then
              (* Equality between lambda terms *)
              [ritem]
            else let
              (* Apply to right side *)
              val th' = apply_to_thm' (Conv.arg_conv cv) th
              val (lhs, rhs) = dest_eq (prop_of' th')
            in
              [Fact (TY_EQ, [lhs, rhs], th')]
            end
          else [ritem]
    end

fun add_rewr_normalizer (norm_name, eq_th) =
    add_normalizer (norm_name, rewr_normalizer eq_th)

fun get_normalizers thy = Symtab.dest (Data.get thy)

fun normalize ctxt ritem =
    let
      val norms = get_normalizers (Proof_Context.theory_of ctxt)
      fun apply_norm (_, norm_fun) ritems = maps (norm_fun ctxt) ritems
      val norm_once = fold apply_norm norms [ritem]
    in
      case norm_once of
          [ritem'] => if BoxItem.eq_ritem (ritem, ritem') then [ritem']
                      else normalize ctxt ritem'
        | _ => maps (normalize ctxt) norm_once
    end

(* Perform normalization, but keep the original ritem. *)
fun normalize_keep ctxt ritem =
    let
      val norm_ritems = normalize ctxt ritem
    in
      if length norm_ritems = 1 then norm_ritems
      else ritem :: norm_ritems
    end

(* Normalization of variable definition *)

structure InjStructData = Theory_Data (
  type T = thm Symtab.table;
  val empty = Symtab.empty;
  val extend = I;
  val merge = Symtab.merge pointer_eq
)

fun add_inj_struct_data th thy =
    let
      val (lhs, _) = th |> prop_of' |> dest_eq |> fst |> dest_eq
      val (f, _) = Term.strip_comb lhs
    in
      case f of
          Const (nm, _) =>
          InjStructData.map (Symtab.update_new (nm, th)) thy
        | _ => raise Fail "add_inj_struct_data"
    end

(* Check whether t is of the form ?A = t, where t does not contain ?A. *)

fun inj_args thy t =
    if Term.is_Var t then [t]
    else let
      val (f, args) = Term.strip_comb t
    in
      if Term.is_Const f andalso
         Symtab.defined (InjStructData.get thy) (Util.get_head_name f) then
        maps (inj_args thy) args
      else
        [t]
    end

fun is_def_eq thy t =
    if not (is_eq_term t) then false
    else let
      val (lhs, rhs) = dest_eq t
      val (l_args, r_args) = apply2 (inj_args thy) (lhs, rhs)
    in
      forall Term.is_Var l_args andalso
      not (forall Term.is_Var r_args) andalso
      forall (fn t => not (Util.is_subterm t rhs)) l_args
    end

fun is_def_eq' thy t =
    is_Trueprop t andalso is_def_eq thy (dest_Trueprop t)

fun is_neg_def_eq thy t =
    is_neg t andalso is_def_eq thy (dest_not t)

(* Given t of the form A_1 ==> ... ==> A_n ==> C, swap all A_i of the
   form ?A = t to the front.
 *)
fun swap_eq_to_front ct =
    let
      val t = Thm.term_of ct
      val thy = Thm.theory_of_cterm ct
    in
      if Util.is_implies t then
        if is_def_eq' thy (dest_arg1 t) then
          Conv.all_conv ct
        else
          Conv.every_conv [Conv.arg_conv swap_eq_to_front,
                           Conv.rewr_conv Drule.swap_prems_eq] ct
      else
        Conv.no_conv ct
    end

(* Given th where the first premise is in the form ?A = t, or f ?A_1
   ... ?A_n = t, where f is injective, replace ?A or each ?A_i in the
   rest of th, and remove the first premise.
 *)
fun meta_use_vardef th =
    if not (Util.is_implies (Thm.prop_of th)) then
      ([], th)
    else let
      val cprem = th |> Thm.cprop_of |> Thm.dest_arg1 |> Thm.dest_arg
      val prem = Thm.term_of cprem
      val thy = Thm.theory_of_thm th
    in
      if is_conj prem then
        th |> apply_to_thm (Conv.rewr_conv (meta_sym @{thm atomize_conjL}))
           |> meta_use_vardef
      else if is_def_eq thy prem then
        let
          val (c_lhs, c_rhs) = cdest_eq cprem
          val (lhs, rhs) = dest_eq prem
        in
          if Term.is_Var lhs then
            let
              val (pairs, th') =
                  th |> Util.subst_thm_atomic [(c_lhs, c_rhs)]
                     |> apply_to_thm (Conv.arg1_conv UtilBase.to_meta_eq_cv)
                     |> Thm.elim_implies (Thm.reflexive c_rhs)
                     |> meta_use_vardef
            in
              ((lhs, rhs) :: pairs, th')
            end
          else
            let
              val nm = Util.get_head_name lhs
              val data = InjStructData.get thy
              val inj_th = the (Symtab.lookup data nm)
                           handle Option.Option => raise Fail "meta_use_vardef"
            in
              th |> apply_to_thm (
                Conv.arg1_conv (Conv.arg_conv (rewr_obj_eq inj_th)))
                 |> meta_use_vardef
            end
        end
      else
        ([], th)
    end

fun disj_ts t =
    if is_disj t then dest_arg1 t :: disj_ts (dest_arg t)
    else [t]

fun swap_disj ct =
    Conv.every_conv [rewr_obj_eq (obj_sym UtilBase.disj_assoc_th),
                     Conv.arg1_conv (rewr_obj_eq UtilBase.disj_commute_th),
                     rewr_obj_eq UtilBase.disj_assoc_th] ct

fun disj_swap_eq_to_front' ct =
    let
      val t = Thm.term_of ct
      val thy = Thm.theory_of_cterm ct
    in
      if is_disj t then
        if is_neg_def_eq thy (dest_arg1 t) then
          Conv.all_conv ct
        else if is_disj (dest_arg t) then
          Conv.every_conv [Conv.arg_conv disj_swap_eq_to_front',
                           swap_disj] ct
        else if is_neg_def_eq thy (dest_arg t) then
          rewr_obj_eq UtilBase.disj_commute_th ct
        else
          Conv.no_conv ct
      else
        Conv.no_conv ct
    end

fun disj_swap_eq_to_front ct =
    Conv.every_conv [
      Trueprop_conv disj_swap_eq_to_front',
      Trueprop_conv (rewr_obj_eq (obj_sym UtilBase.imp_conv_disj_th)),
      Conv.rewr_conv (meta_sym UtilBase.atomize_imp_th)
    ] ct

fun meta_use_vardefs th =
    let
      val thy = Thm.theory_of_thm th
    in
      if exists (is_def_eq' thy) (Thm.prems_of th) then
        let
          val (pairs, th') = th |> apply_to_thm swap_eq_to_front
                                |> meta_use_vardef
          val (pairs', th'') = meta_use_vardefs th'
        in
          (pairs @ pairs', th'')
        end
      else if is_Trueprop (Thm.prop_of th) then
        let
          val ts = disj_ts (prop_of' th)
        in
          if length ts > 1 andalso exists (is_neg_def_eq thy) ts then
            let
              val (pairs, th') = th |> apply_to_thm disj_swap_eq_to_front
                                    |> meta_use_vardef
              val (pairs', th'') = meta_use_vardefs th'
            in
              (pairs @ pairs', th'')
            end
          else
            ([], th)
        end
      else
        ([], th)
    end

fun def_subst pairs t =
    fold (fn p => Term.subst_atomic [p]) pairs t

end  (* structure Normalizer. *)
