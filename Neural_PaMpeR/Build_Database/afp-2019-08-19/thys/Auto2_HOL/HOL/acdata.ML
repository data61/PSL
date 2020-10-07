(*
  File: acdata.ML
  Author: Bohua Zhan

  Dealing with associative-commutative operations.
*)

(* Data for an AC function. *)
type ac_info = {
  cfhead: cterm,
  unit: cterm option,
  assoc_th: thm,  (* (a . b) . c = a . (b . c) *)
  comm_th: thm,   (* a . b = b . a *)
  unitl_th: thm,  (* e . a = a *)
  unitr_th: thm   (* a . e = a *)
}

signature ACUTIL =
sig
  val inst_ac_info: theory -> typ -> ac_info -> ac_info option
  val head_agrees: ac_info -> term -> bool
  val eq_unit: ac_info -> term -> bool
  val add_ac_data: ac_info -> theory -> theory
  val get_head_ac_info: theory -> term -> ac_info option

  val has_assoc_th: ac_info -> bool
  val has_comm_th: ac_info -> bool
  val has_unit_th: ac_info -> bool
  val comm_cv: ac_info -> conv
  val assoc_cv: ac_info -> conv
  val assoc_sym_cv: ac_info -> conv
  val swap_cv: ac_info -> conv
  val swap_r_cv: ac_info -> conv

  val dest_ac: ac_info -> term -> term list
  val cdest_ac: ac_info -> cterm -> cterm list
  val comb_ac_equiv: ac_info -> thm list -> thm
  val normalize_assoc: ac_info -> conv
  val move_outmost: ac_info -> term -> conv
  val normalize_unit: ac_info -> conv
  val normalize_comm_gen: ac_info -> (term * term -> bool) -> conv
  val normalize_comm: ac_info -> conv
  val normalize_au: ac_info -> conv
  val normalize_all_ac: ac_info -> conv
  val ac_last_conv: ac_info -> conv -> conv
  val norm_combine: ac_info -> (term -> bool) -> conv -> conv
end;

structure ACUtil : ACUTIL =
struct

(* Register of generators of ac_inst_info. *)
structure Data = Theory_Data (
  type T = ac_info Symtab.table;
  val empty = Symtab.empty;
  val extend = I;
  val merge = Symtab.merge (fn (info1, info2) => #cfhead info1 aconvc #cfhead info2)
)

(* Instantiate an ac_info for a specific type T. *)
fun inst_ac_info thy T {assoc_th, comm_th, unitl_th, unitr_th, ...} =
    let
      (* Instantiate th to having argument of type T. If not possible,
         change th to true_th.
       *)
      fun inst_th th =
          if is_true_th th then true_th else
          let
            (* Extract the first argument of th, then the body type of
               that argument.
             *)
            val arg_type = th |> prop_of' |> Util.dest_args |> hd
                              |> Term.type_of |> Term.body_type
          in
            if arg_type = T then th else
            let
              val tenv = Sign.typ_match thy (arg_type, T) Vartab.empty
            in
              Util.subst_thm_thy thy (tenv, Vartab.empty) th
            end
            handle Type.TYPE_MATCH => true_th
          end

      val assoc_th' = inst_th assoc_th
      val unitl_th' = inst_th unitl_th
    in
      if is_true_th assoc_th' then NONE else
      SOME {cfhead = assoc_th' |> cprop_of' |> Thm.dest_arg1 |> Thm.dest_fun2,
            unit = if is_true_th unitl_th' then NONE
                   else SOME (unitl_th' |>  cprop_of' |> Thm.dest_arg1 |> Thm.dest_arg1),
            assoc_th = assoc_th',
            comm_th = inst_th comm_th,
            unitl_th = unitl_th',
            unitr_th = inst_th unitr_th}
    end

fun head_agrees {cfhead, ...} t = Util.is_head (Thm.term_of cfhead) t

fun eq_unit {unit, ...} t =
    case unit of NONE => false | SOME ct' => t aconv (Thm.term_of ct')

(* Add the given ac_info under the given name. *)
fun add_ac_data info thy =
    let
      val {assoc_th, ...} = info
      val f = assoc_th |> prop_of' |> dest_eq |> snd |> Term.head_of
    in
      case f of
          Const (c, _) =>
          let
            val _ = tracing ("Add ac data for function " ^ c)
          in
            Data.map (Symtab.update_new (c, info)) thy
          end
        | _ => error "Add AC data: invalid assoc_th"
    end
    handle Symtab.DUP _ => error "Add AC data: info already exists."

fun get_head_ac_info thy t =
    case t of
        Const (c, _) $ _ $ _ =>
        (case Symtab.lookup (Data.get thy) c of
             NONE => NONE
           | SOME ac_info => inst_ac_info thy (fastype_of t) ac_info)
      | _ => NONE

fun has_assoc_th {assoc_th, ...} = not (is_true_th assoc_th)
fun has_comm_th {comm_th, ...} = not (is_true_th comm_th)
fun has_unit_th {unitl_th, ...} = not (is_true_th unitl_th)
fun comm_cv {comm_th, ...} = rewr_obj_eq comm_th
fun assoc_cv {assoc_th, ...} = rewr_obj_eq assoc_th
fun assoc_sym_cv {assoc_th, ...} = rewr_obj_eq (obj_sym assoc_th)

(* (a . b) . c = (a . c) . b *)
fun swap_cv (ac_info as {assoc_th, comm_th, ...}) ct =
    if head_agrees ac_info (dest_arg1 (Thm.term_of ct)) then
      Conv.every_conv [rewr_obj_eq assoc_th,
                       Conv.arg_conv (rewr_obj_eq comm_th),
                       rewr_obj_eq (obj_sym assoc_th)] ct
    else
      rewr_obj_eq comm_th ct

(* a . (b . c) = b . (a . c) *)
fun swap_r_cv (ac_info as {assoc_th, comm_th, ...}) ct =
    if head_agrees ac_info (dest_arg (Thm.term_of ct)) then
      Conv.every_conv [rewr_obj_eq (obj_sym assoc_th),
                       Conv.arg1_conv (rewr_obj_eq comm_th),
                       rewr_obj_eq assoc_th] ct
    else
      rewr_obj_eq comm_th ct

(* Destruct t, assuming it is associated to the left. *)
fun dest_ac ac_info t =
    let
      fun dest t =
          if head_agrees ac_info t then
            let val (a1, a2) = Util.dest_binop_args t in a2 :: dest a1 end
          else [t]
    in
      rev (dest t)
    end

fun cdest_ac ac_info ct =
    let
      fun dest ct =
          if head_agrees ac_info (Thm.term_of ct) then
            let val (a1, a2) = Util.dest_binop_cargs ct in a2 :: dest a1 end
          else [ct]
    in
      rev (dest ct)
    end

(* Given ths: [A1 == B1, ..., An == Bn], get theorem A1...An ==
   B1...Bn. Associate to the left only.
 *)
fun comb_ac_equiv {cfhead, ...} ths =
    let
      fun binop_comb th1 th2 =
          Thm.combination (Thm.combination (Thm.reflexive cfhead) th1) th2

      (* Combine in the reverse order. *)
      fun comb ths =
          case ths of
              [] => raise Fail "comb_ac_equiv: empty list"
            | [th] => th
            | [th1, th2] => binop_comb th2 th1
            | th :: ths' => binop_comb (comb ths') th
    in
      comb (rev ths)
    end

(* Normalize association with the given direction. *)
fun normalize_assoc ac_info ct =
    if not (has_assoc_th ac_info) then Conv.all_conv ct
    else let
      val {assoc_th, ...} = ac_info

      (* First rewrite into form (...) * a, then rewrite the remaining
         parts.
       *)
      fun normalize ct =
          if head_agrees ac_info (Thm.term_of ct) then
            Conv.every_conv [Conv.repeat_conv (rewr_obj_eq (obj_sym assoc_th)),
                             Conv.arg1_conv normalize] ct
          else
            Conv.all_conv ct
    in
      normalize ct
    end

(* Move the given u within ct to the rightmost position. Assume
   associate to the left.
 *)
fun move_outmost (ac_info as {comm_th, ...}) u ct =
    if not (has_assoc_th ac_info andalso has_comm_th ac_info) then
      raise Fail "move_outmost: commutativity is not available."
    else if u aconv (Thm.term_of ct) then Conv.all_conv ct else
    if not (head_agrees ac_info (Thm.term_of ct)) then
      raise Fail "move_outmost: u not found in ct."
    else let
      val (a, b) = Util.dest_binop_args (Thm.term_of ct)
    in
      if u aconv b then Conv.all_conv ct
      else if head_agrees ac_info a then
        ((Conv.arg1_conv (move_outmost ac_info u))
             then_conv (swap_cv ac_info)) ct
      else if u aconv a then
        rewr_obj_eq comm_th ct
      else
        raise Fail "move_outmost: u not found in ct."
    end

(* In a product of a_1, a_2, ..., remove any a_i that is a unit. *)
fun normalize_unit (ac_info as {unitl_th, unitr_th, ...}) ct =
    if not (has_unit_th ac_info) then Conv.all_conv ct
    else let
      fun normalize ct =
          if head_agrees ac_info (Thm.term_of ct) then
            Conv.every_conv [Conv.binop_conv normalize,
                             Conv.try_conv (rewr_obj_eq unitl_th),
                             Conv.try_conv (rewr_obj_eq unitr_th)] ct
          else
            Conv.all_conv ct
    in
      normalize ct
    end

(* Rearrange subterms of ct according to the given term
   ordering. Returns theorem ct == ct'.
 *)
fun normalize_comm_gen (ac_info as {comm_th, ...}) termless ct =
    if not (has_comm_th ac_info) then Conv.all_conv ct
    else let
      (* If there are two terms a.b, swap if a > b. If there are at
         least three terms, in the left associate case this is
         (a.b).c, swap b and c if b > c. If there is a swap,
         recursively call swap_last until the original outside term is
         swapped into position.
       *)
      fun swap_last ct =
          if head_agrees ac_info (Thm.term_of ct) then
            let
              val (a1, a2) = Util.dest_binop_args (Thm.term_of ct)
            in
              if head_agrees ac_info a1 then
                (* Structure of t is a1 . a2 = (_ . b2) . a2. *)
                if termless (a2, dest_arg a1) then
                  ((swap_cv ac_info) then_conv (Conv.arg1_conv swap_last)) ct
                else Conv.all_conv ct
              else
                (* Structure of t is a1 . a2. *)
                if termless (a2, a1) then rewr_obj_eq comm_th ct
                else Conv.all_conv ct
            end
          else
            Conv.all_conv ct

      (* Full ordering. Recursively perform full ordering on all but
         the outermost, then swap outermost into position.
       *)
      fun normalize ct =
          if head_agrees ac_info (Thm.term_of ct) then
            ((Conv.arg1_conv normalize) then_conv swap_last) ct
          else
            Conv.all_conv ct
    in
      normalize ct
    end

fun normalize_comm ac_info = normalize_comm_gen ac_info (fn (s, t) => Term_Ord.term_ord (s, t) = LESS)

(* Normalize all except comm. *)
fun normalize_au ac_info =
    Conv.every_conv [normalize_unit ac_info, normalize_assoc ac_info]

(* Normalize everything. *)
fun normalize_all_ac ac_info =
    Conv.every_conv [normalize_au ac_info, normalize_comm ac_info]

(* Rewrite the last term in ct using cv. Assume associative to left. *)
fun ac_last_conv ac_info cv ct =
    if head_agrees ac_info (Thm.term_of ct) then
      Conv.arg_conv cv ct
    else cv ct

(* Given ct in the form x_1 * ... * x_n, where some sequence of x_i
   satisfies predicate pred. Combine these x_i into a single term
   using the binary combinator cv.
 *)
fun norm_combine ac_info pred cv ct =
    let
      val t = Thm.term_of ct
    in
      if head_agrees ac_info t then
        let
          val (a, b) = Util.dest_binop_args t
        in
          if pred b then
            if pred a then
              cv ct
            else if head_agrees ac_info a andalso pred (dest_arg a) then
              Conv.every_conv [assoc_cv ac_info,
                               Conv.arg_conv cv,
                               norm_combine ac_info pred cv] ct
            else
              Conv.all_conv ct
          else
            Conv.arg1_conv (norm_combine ac_info pred cv) ct
        end
      else
        Conv.all_conv ct
    end

end  (* structure ACUtil. *)
