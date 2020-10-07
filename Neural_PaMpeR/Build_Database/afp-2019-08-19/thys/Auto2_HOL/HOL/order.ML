(*
  File: order.ML
  Author: Bohua Zhan

  Ordering on natural numbers. We implement something like a decision
  procedure for difference logic using proof steps.
*)

val TY_NAT_ORDER = "NAT_ORDER"

signature NAT_ORDER =
sig
  val is_order: term -> bool
  val is_plus_const: term -> bool
  val is_minus_const: term -> bool
  val is_standard_ineq: term -> bool
  val dest_ineq: term -> term * term * int
  val dest_ineq_th: thm -> term * term * int

  val fold_double_plus: conv
  val norm_ineq_th': thm -> thm
  val convert_const_x: thm -> thm
  val convert_const_y: thm -> thm
  val norm_ineq_th: thm -> thm
  val norm_ineq_minus_th': thm -> thm option
  val norm_ineq_minus_th: thm -> thm option

  datatype order_type =
           LESS | LESS_LMINUS | LESS_LPLUS | LESS_RMINUS | LESS_RPLUS |
           LE | LE_LMINUS | LE_LPLUS | LE_RMINUS | LE_RPLUS
  type order_info
  val to_normal_th: order_type -> thm -> thm
  val th_to_ritem: thm -> raw_item
  val th_to_normed_ritems: thm -> raw_item list
  val nat_order_normalizer: normalizer
  val nat_eq_diff_prfstep: proofstep

  val get_nat_order_info: box_item -> order_info
  val nat_order_typed_matcher: item_matcher
  val transitive: proofstep
  val transitive_resolve: proofstep
  val single_resolve: proofstep
  val single_resolve_zero: proofstep

  val nat_order_match: term -> box_item -> Proof.context -> id_inst ->
                       id_inst_th list
  val nat_order_matcher: item_matcher
  val nat_order_noteq_matcher: item_matcher
  val nat_order_single_match: term -> box_item -> Proof.context -> id_inst ->
                              id_inst_th list
  val nat_order_single_matcher: item_matcher

  val shadow_nat_order_prfstep: proofstep
  val shadow_nat_order_single: proofstep

  val string_of_nat_order: Proof.context -> term * term * int * thm -> string
  val output_nat_order: Proof.context -> term list * thm -> string
  val shadow_nat_order: Proof.context -> box_id -> term list * cterm list -> bool
  val add_nat_order_proofsteps: theory -> theory
end;

structure Nat_Order : NAT_ORDER =
struct

val is_numc = UtilArith.is_numc
val dest_numc = UtilArith.dest_numc
val nat0 = Nat_Util.nat0
val nat_less_th = Nat_Util.nat_less_th

val nat_fold_conv0_right =
    Conv.try_conv (rewr_obj_eq @{thm Nat.add_0_right})

val nat_fold_conv0_left =
    Conv.try_conv (rewr_obj_eq @{thm Nat.plus_nat.add_0})

(* Whether the given term is < or <= on natural numbers. *)
fun is_less t =
    case t of Const (@{const_name less}, _) $ _ $ _ => true
            | _ => false

fun is_less_eq t =
    case t of Const (@{const_name less_eq}, _) $ _ $ _ => true
            | _ => false

fun is_order t = is_less t orelse is_less_eq t

datatype order_type =
         LESS_LMINUS | LESS_LPLUS | LESS_RMINUS | LESS_RPLUS | LESS |
         LE_LMINUS | LE_LPLUS | LE_RMINUS | LE_RPLUS | LE

(* Check whether t is in the form a + n, where n is a constant. *)
fun is_plus_const t =
    UtilArith.is_plus t andalso UtilArith.is_numc (dest_arg t)

(* Check whether t is in the form a - n, where n is a constant. *)
fun is_minus_const t =
    UtilArith.is_minus t andalso UtilArith.is_numc (dest_arg t)

(* Check whether t is an inequality in the standard form. This means t
   is either a + n <= b with n > 0, or a <= b + n with n >= 0.
 *)
fun is_standard_ineq t =
    if is_less_eq t then
      let
        val (lhs, rhs) = Util.dest_binop_args t
      in
        fastype_of lhs = natT andalso
        ((is_plus_const lhs andalso not (is_plus_const rhs) andalso
          UtilArith.dest_numc (dest_arg lhs) > 0) orelse
         (is_plus_const rhs andalso not (is_plus_const lhs)))
      end
    else false

(* Assume t is in the form x + n <= y or x <= y + n, deconstruct into
   the triple (x, y, d), where d = -n in the first case and n in the
   second case.
 *)
fun dest_ineq t =
    let
      val _ = assert (is_standard_ineq t) "dest_ineq"
      val (lhs, rhs) = Util.dest_binop_args t
    in
      if is_plus_const lhs then
        (dest_arg1 lhs, rhs, ~ (UtilArith.dest_numc (dest_arg lhs)))
      else
        (lhs, dest_arg1 rhs, UtilArith.dest_numc (dest_arg rhs))
    end

fun dest_ineq_th th =
    if UtilLogic.is_Trueprop (Thm.prop_of th) andalso
       is_standard_ineq (prop_of' th) then
      dest_ineq (prop_of' th)
    else let
      val _ = trace_thm_global "th:" th
    in
      raise Fail "dest_ineq_th"
    end

(* In expression x + n < y, fold n. *)
val fold_const_left =
    apply_to_thm' (Conv.arg1_conv (Conv.arg_conv Nat_Util.nat_fold_conv))

(* In expression x < y + n, fold n. *)
val fold_const_right =
    apply_to_thm' (Conv.arg_conv (Conv.arg_conv Nat_Util.nat_fold_conv))

(* In expression (x + c1) + c2, fold c1 + c2. *)
fun fold_double_plus ct =
    let
      val t = Thm.term_of ct
    in
      if is_plus_const t andalso is_plus_const (dest_arg1 t) then
        Conv.every_conv [rewr_obj_eq @{thm add_ac(1)},
                         Conv.arg_conv Nat_Util.nat_fold_conv,
                         fold_double_plus] ct
      else
        Conv.all_conv ct
    end

(* Normalize inequality to standard form. This function is able to
   process any theorem of the form a </<= b.
 *)
fun norm_ineq_th' th =
    let
      val t = prop_of' th
      val _ = assert (is_less_eq t orelse is_less t) "norm_ineq_th"
      val (lhs, rhs) = Util.dest_binop_args t
      val try_fold0 = Conv.try_conv (Conv.arg_conv nat_fold_conv0_right)
    in
      if is_less_eq t then
        if is_plus_const lhs andalso is_plus_const rhs then
          let
            val (lhs, rhs) = Util.dest_binop_args t
            val (n1, n2) = apply2 (UtilArith.dest_numc o dest_arg) (lhs, rhs)
          in
            if n1 <= n2 then
              (th RS @{thm reduce_le_plus_consts}) |> fold_const_right
            else
              ([Nat_Util.nat_le_th n2 n1, th]
                   MRS @{thm reduce_le_plus_consts'}) |> fold_const_left
          end
        else if is_plus_const lhs then
          if UtilArith.dest_numc (dest_arg lhs) = 0 then
            th RS @{thm norm_le_lplus0}
          else th
        else if is_plus_const rhs then th
        else if is_minus_const lhs then
          th RS @{thm norm_le_lminus}
        else if is_minus_const rhs then
          th RS @{thm norm_le_rminus}
        else
          th RS @{thm norm_le}
      else  (* is_less t *)
        if is_plus_const lhs andalso is_plus_const rhs then
          let
            val (lhs, rhs) = Util.dest_binop_args t
            val (n1, n2) = apply2 (UtilArith.dest_numc o dest_arg) (lhs, rhs)
          in
            if n1 <= n2 then
              (th RS @{thm reduce_less_plus_consts}) |> fold_const_right
                                                     |> apply_to_thm' try_fold0
                                                     |> norm_ineq_th'
            else
              ([Nat_Util.nat_le_th n2 n1, th]
                   MRS @{thm reduce_less_plus_consts'}) |> fold_const_left
                                                        |> norm_ineq_th'
          end
        else if is_plus_const lhs then
          (th RS @{thm norm_less_lplus}) |> fold_const_left
        else if is_plus_const rhs then
          (th RS @{thm norm_less_rplus}) |> fold_const_right
        else if is_minus_const lhs then
          (th RS @{thm norm_less_lminus}) |> fold_const_right
        else if is_minus_const rhs then
          (th RS @{thm norm_less_rminus}) |> fold_const_left
        else
          th RS @{thm norm_less}
    end

(* Handle the case of x </<= y where x is itself a constant. Reduce to
   the case where x = 0.
 *)
fun convert_const_x th =
    let
      val (x, _, d) = dest_ineq_th th
    in
      if UtilArith.is_numc x then
        let
          val xn = UtilArith.dest_numc x
        in
          if xn = 0 then th
          else if d < 0 then
            (th RS @{thm cv_const1}) |> fold_const_left
          else if d - xn < 0 then
            (th RS @{thm cv_const4}) |> fold_const_left
          else
            (th RS @{thm cv_const5}) |> fold_const_right
        end
      else th
    end

(* Handle the case of x </<= y where y is itself a constant. Reduce to
   the case where y = 0.
 *)
fun convert_const_y th =
    let
      val (_, y, d) = dest_ineq_th th
    in
      if UtilArith.is_numc y then
        let
          val yn = UtilArith.dest_numc y
        in
          if yn = 0 then th
          else if d < 0 andalso yn + d >= 0 then
            (th RS @{thm cv_const2}) |> fold_const_right
          else if d < 0 andalso yn + d < 0 then
            ([Nat_Util.nat_less_th yn (~d), th] MRS @{thm cv_const3})
                |> fold_const_left
          else
            (th RS @{thm cv_const6}) |> fold_const_right
        end
      else th
    end

(* Overall normalization function. *)
fun norm_ineq_th th =
    let
      val th' =
          th |> apply_to_thm' (Conv.arg1_conv fold_double_plus)
             |> apply_to_thm' (Conv.arg_conv fold_double_plus)
             |> norm_ineq_th' |> convert_const_x |> convert_const_y
    in
      if is_standard_ineq (prop_of' th') then th'
      else let
        val _ = trace_thm_global "th':" th'
      in
        raise Fail "norm_ineq_th: invalid output."
      end
    end

(* Normalization function that does not consider the minus case. *)
fun norm_ineq_minus_th' th =
    let
      val t = prop_of' th
      val _ = assert (is_less_eq t orelse is_less t) "norm_ineq_minus_th"
      val (lhs, rhs) = Util.dest_binop_args t
    in
      if is_less_eq t then
        if is_minus_const lhs andalso not (is_plus_const rhs) then
          SOME (th RS @{thm norm_le})
        else if is_minus_const rhs andalso not (is_plus_const lhs) then
          SOME (th RS @{thm norm_le})
        else NONE
      else  (* is_less t *)
        if is_minus_const lhs andalso not (is_plus_const rhs) then
          SOME (th RS @{thm norm_less})
        else if is_minus_const rhs andalso not (is_plus_const lhs) then
          SOME (th RS @{thm norm_less})
        else NONE
    end

fun norm_ineq_minus_th th =
    case norm_ineq_minus_th' th of
        NONE => NONE
      | SOME th' =>
        let
          val th'' = th' |> convert_const_x |> convert_const_y
        in
          if is_standard_ineq (prop_of' th'') then SOME th''
          else let
            val _ = trace_thm_global "th'':" th''
          in
            raise Fail "norm_ineq_minus_th: invalid output."
          end
        end

(* The first three values (x, y, n) specify a NAT_ORDER item, and the
   last value provides theorem justifying it. If n >= 0, then the
   theorem is x <= y + n. Otherwise, the theorem is x + (~n) <= y.
 *)
type order_info = cterm * cterm * int * thm

(* Conversion from a theorem to its normal form. *)
fun to_normal_th order_ty th =
    case order_ty of
        LESS_LMINUS => (th RS @{thm norm_less_lminus}) |> fold_const_right
      | LESS_LPLUS => (th RS @{thm norm_less_lplus}) |> fold_const_left
      | LESS_RMINUS => (th RS @{thm norm_less_rminus}) |> fold_const_left
      | LESS_RPLUS => (th RS @{thm norm_less_rplus}) |> fold_const_right
      | LESS => th RS @{thm norm_less}
      | LE_LMINUS => th RS @{thm norm_le_lminus}
      | LE_RMINUS => th RS @{thm norm_le_rminus}
      | LE => th RS @{thm norm_le}
      | LE_LPLUS =>
        if UtilArith.dest_numc (dest_arg (dest_arg1 (prop_of' th))) = 0 then
          th RS @{thm norm_le_lplus0}
        else th
      | _ => th

(* eq_x is a meta equality. Use it to rewrite x in an order info. *)
fun rewrite_info_x eq_x (cx, cy, diff, th) =
    let
      val _ = assert (Thm.lhs_of eq_x aconvc cx)
                     "rewrite_info_x: invalid equality."
      val th' =
          if diff >= 0 then  (* rewrite x in x <= y + n. *)
            th |> apply_to_thm' (Conv.arg1_conv (Conv.rewr_conv eq_x))
          else  (* rewrite x in x + n <= y. *)
            th |> apply_to_thm' (Conv.arg1_conv (
                                    Conv.arg1_conv (Conv.rewr_conv eq_x)))
    in
      (Thm.rhs_of eq_x, cy, diff, th')
    end

(* eq_y is a meta equality. Use it to rewrite y in an order info. *)
fun rewrite_info_y eq_y (cx, cy, diff, th) =
    let
      val _ = assert (Thm.lhs_of eq_y aconvc cy)
                     "rewrite_info_y: invalid equality."
      val th' =
          if diff >= 0 then  (* rewrite y in x <= y + n. *)
            th |> apply_to_thm' (Conv.arg_conv (
                                   Conv.arg1_conv (Conv.rewr_conv eq_y)))
          else  (* rewrite y in x + n <= y. *)
            th |> apply_to_thm' (Conv.arg_conv (Conv.rewr_conv eq_y))
    in
      (cx, Thm.rhs_of eq_y, diff, th')
    end

(* Conversion from a normalized order theorem to an raw item. *)
fun th_to_ritem th =
    let
      val (x, y, n) = dest_ineq_th th
    in
      Fact (TY_NAT_ORDER, [x, y, mk_int n], th)
    end

(* Overall normalization function. Include both strategies (with and
   without considering the minus case).
 *)
fun th_to_normed_ritems th =
    let
      val th' = norm_ineq_th th
      val minus_th = the_list (norm_ineq_minus_th th)
    in
      map th_to_ritem (th' :: minus_th)
    end

fun nat_order_normalizer _ ritem =
    case ritem of
        Handler _ => [ritem]
      | Fact (ty_str, _, th) =>
        if ty_str <> TY_PROP then [ritem]
        else if is_order (prop_of' th) andalso
                fastype_of (dest_arg (prop_of' th)) = natT then
          th_to_normed_ritems th
        else [ritem]

(* Given an equality such as x + n = y, produce inequalities x + n <=
   y and x + n >= y. Applies also when one side of the inequality is a
   constant.
 *)
val nat_eq_diff_prfstep =
    ProofStep.prfstep_custom
      "nat_eq_diff"
      [WithItem (TY_EQ, @{term_pat "(?x::nat) = ?y"})]
      (fn ((id, _), _) => fn items => fn _ =>
          let
            val {prop, ...} = the_single items
            val (lhs, rhs) = prop |> prop_of' |> Util.dest_binop_args
          in
            if is_plus_const lhs orelse is_plus_const rhs orelse
               is_numc lhs orelse is_numc rhs then
              let
                val prop' = to_meta_eq prop
                val ths = (prop' RS @{thm eq_to_ineqs})
                              |> UtilLogic.split_conj_th
              in
                [AddItems {id = id, sc = NONE,
                           raw_items = maps th_to_normed_ritems ths}]
              end
            else []
          end)

(* Obtain quadruple x, y, diff, and theorem from item. *)
fun get_nat_order_info {tname, prop, ...} =
    let
      val (cx, cy, cdiff_t) = the_triple tname
    in
      (cx, cy, dest_numc (Thm.term_of cdiff_t), prop)
    end

(* Matching function for retrieving a NAT_ORDER item. The pattern
   should be a triple (?x, ?y, ?m).
 *)
val nat_order_typed_matcher =
    let
      fun pre_match pat {tname, ...} ctxt =
          Matcher.pre_match_head
              ctxt (pat, Thm.cterm_of ctxt (HOLogic.mk_tuple (map Thm.term_of tname)))

      fun match pat (item as {tname = cts, ...}) ctxt (id, inst) =
          let
            val pats = HOLogic.strip_tuple pat
            val insts' = Matcher.rewrite_match_list
                             ctxt (map (pair false) (pats ~~ cts)) (id, inst)
            fun process_inst (inst, ths) =
                let
                  (* eq_x: pat_x(env) == x, eq_y: pat_y(env) = y *)
                  val (eq_x, eq_y, eq_n) = the_triple ths
                in
                  if Thm.is_reflexive eq_n then
                    let
                      val (_, _, _, prop) =
                          item |> get_nat_order_info
                               |> rewrite_info_x (meta_sym eq_x)
                               |> rewrite_info_y (meta_sym eq_y)
                    in
                      [(inst, prop)]
                    end
                  else []
                end
          in
            maps process_inst insts'
          end
    in
      {pre_match = pre_match, match = match}
    end

(* Helper function for transitivity of two inequalities. *)
fun order_trans th1 th2 =
    let
      val (_, y1, d1) = dest_ineq_th th1
      val (x2, _, d2) = dest_ineq_th th2
      val _ = assert (y1 aconv x2) "order_trans"
    in
      if d1 < 0 andalso d2 < 0 then
        ([th1, th2] MRS @{thm trans1}) |> fold_const_left
      else if d1 >= 0 andalso d2 >= 0 then
        ([th1, th2] MRS @{thm trans2}) |> fold_const_right
      else if d1 < 0 andalso d2 >= 0 then
        if d2 >= (~d1) then
          ([th1, th2] MRS @{thm trans3}) |> fold_const_right
        else  (* d2 < (~d1) *)
          ([Nat_Util.nat_less_th d2 (~d1), th1, th2] MRS @{thm trans4})
              |> fold_const_left
      else  (* d1 >= 0 andalso d2 < 0 *)
        if d1 >= (~d2) then
          ([th1, th2] MRS @{thm trans5}) |> fold_const_right
        else
          ([Nat_Util.nat_less_th d1 (~d2), th1, th2] MRS @{thm trans6})
              |> fold_const_left
    end

(* Apply transitivity to two NAT_ORDER infos. *)
val transitive =
    ProofStep.prfstep_custom
        "nat_order_transitive"
        [WithItem (TY_NAT_ORDER, @{term_pat "(?x, ?y, ?m)"}),
         WithItem (TY_NAT_ORDER, @{term_pat "(?y, ?z, ?n)"}),
         Filter (neq_filter @{term_pat "?x ~= ?y"}),
         Filter (neq_filter @{term_pat "?y ~= ?z"}),
         Filter (neq_filter @{term_pat "?x ~= ?z"})]
        (fn ((id, _), ths) => fn _ => fn _ =>
            let
              val (th1, th2) = the_pair ths
              val item' = th_to_ritem (order_trans th1 th2)
            in
              [AddItems {id = id, sc = NONE, raw_items = [item']}]
            end)

(* Helper function for obtaining a contradiction from two inequalities. *)
fun order_trans_resolve th1 th2 =
    let
      val (_, _, d1) = dest_ineq_th th1
      val (_, _, d2) = dest_ineq_th th2
    in
      if d1 < 0 andalso d2 < 0 then
        [nat_less_th 0 (~d1), th1, th2] MRS @{thm trans_resolve1}
      else if d1 < 0 andalso d2 >= 0 then
        [nat_less_th d2 (~d1), th1, th2] MRS @{thm trans_resolve2}
      else (* d1 >= 0 andalso d2 < 0 *)
        [nat_less_th d1 (~d2), th2, th1] MRS @{thm trans_resolve2}
    end

(* Try to derive a contradiction from two NAT_ORDER items. *)
val transitive_resolve =
    ProofStep.prfstep_custom
        "nat_order_transitive_resolve"
        [WithItem (TY_NAT_ORDER, @{term_pat "(?x, ?y, ?m)"}),
         WithItem (TY_NAT_ORDER, @{term_pat "(?y, ?x, ?n)"})]
        (fn ((id, inst), ths) => fn _ => fn _ =>
            let
              val m = dest_numc (lookup_inst inst "m")
              val n = dest_numc (lookup_inst inst "n")
              val (th1, th2) = the_pair ths
              (* Fold x <= y + 0 to x <= y. *)
              val fold0 = apply_to_thm' (Conv.arg_conv nat_fold_conv0_right)
              val try_fold0l = Conv.try_conv nat_fold_conv0_left
              val res_ths =
                  if m + n < 0 then [order_trans_resolve th1 th2]
                  else if m = 0 andalso n = 0 then
                    [(map fold0 [th1, th2]) MRS @{thm Orderings.order_antisym}]
                  else if m + n = 0 then
                    (* Fold 0 at left in case x or y is zero. *)
                    [([th1, th2] MRS @{thm Orderings.order_antisym})
                         |> apply_to_thm' (Conv.arg_conv try_fold0l)
                         |> apply_to_thm' (Conv.arg1_conv try_fold0l)]
                  else []
            in
              map (fn th => Update.thm_update (id, th)) res_ths
            end)

(* Try to derive a contradiction from a single NAT_ORDER item. There
   are two types of resolves: when two sides are equal, and when the
   right side is zero (both with negative diff).
 *)
val single_resolve =
    ProofStep.prfstep_custom
        "nat_order_single_resolve"
        [WithItem (TY_NAT_ORDER, @{term_pat "(?x, ?x, ?n)"})]
        (fn ((id, inst), ths) => fn _ => fn _ =>
            let
              val n = dest_numc (lookup_inst inst "n")
              val th = the_single ths
            in
              if n < 0 then
                [Update.thm_update (
                    id, [nat_less_th 0 (~n), th] MRS @{thm single_resolve})]
              else []
            end)

val single_resolve_zero =
    ProofStep.prfstep_custom
        "nat_order_single_resolve_zero"
        [WithItem (TY_NAT_ORDER, @{term_pat "(?x, 0, ?n)"})]
        (fn ((id, inst), ths) => fn _ => fn _ =>
            let
              val n = dest_numc (lookup_inst inst "n")
              val th = the_single ths
            in
              if n < 0 then
                [Update.thm_update (id, [nat_less_th 0 (~n), th]
                                            MRS @{thm single_resolve_const})]
              else []
            end)

(* Returns true if ty is either natT or a schematic type of sort
   linorder.
 *)
fun valid_type ctxt ty =
    case ty of
        TVar _ => Sign.of_sort (Proof_Context.theory_of ctxt)
                               (ty, ["Orderings.linorder"])
      | _ => (ty = natT)

(* Given t in inequality form, return whether the type of the argument
   is appropriate for nat_order_match: that is, either natT or a
   schematic type of sort linorder.
 *)
fun valid_arg_type ctxt t =
    valid_type ctxt (fastype_of (dest_arg t))

fun is_order_pat ctxt pat =
    (is_order pat andalso valid_arg_type ctxt pat) orelse
    (is_order (get_neg pat) andalso valid_arg_type ctxt (get_neg pat))

val less_nat = @{term "(<)::nat => nat => bool"}
val le_nat = @{term "(<=)::nat => nat => bool"}

(* Assuming t is an order. Return the simplified form of the negation of t. *)
fun get_neg_order t =
    if is_neg t then dest_not t
    else if is_less t then le_nat $ dest_arg t $ dest_arg1 t
    else if is_less_eq t then less_nat $ dest_arg t $ dest_arg1 t
    else raise Fail "get_neg_order"

fun is_plus_const_gen t =
    is_plus_const t orelse (is_numc t andalso not (t aconv nat0))

fun plus_const_of_gen t =
    if is_plus_const t then dest_arg1 t else nat0

fun rewr_side eq_th ct =
    if Thm.lhs_of eq_th aconvc ct then
      Conv.rewr_conv eq_th ct
    else if is_numc (Thm.term_of ct) then
      Conv.every_conv [rewr_obj_eq (obj_sym @{thm Nat.plus_nat.add_0}),
                       Conv.arg1_conv (Conv.rewr_conv eq_th)] ct
    else
      Conv.arg1_conv (Conv.rewr_conv eq_th) ct

(* Return a pair of terms to be matched. *)
fun analyze_pattern t =
    let
      val (lhs, rhs) = Util.dest_binop_args t
    in
      if is_plus_const_gen lhs then
        (plus_const_of_gen lhs, rhs,
         if is_less t then LESS_LPLUS else LE_LPLUS)
      else if is_plus_const_gen rhs then
        (lhs, plus_const_of_gen rhs,
         if is_less t then LESS_RPLUS else LE_RPLUS)
      else if is_minus_const lhs then
        (dest_arg1 lhs, rhs,
         if is_less t then LESS_LMINUS else LE_LMINUS)
      else if is_minus_const rhs then
        (lhs, dest_arg1 rhs,
         if is_less t then LESS_RMINUS else LE_RMINUS)
      else
        (lhs, rhs, if is_less t then LESS else LE)
    end

fun analyze_pattern2 t =
    let
      val (lhs, rhs) = Util.dest_binop_args t
    in
      if is_minus_const lhs andalso not (is_plus_const_gen rhs) then
        SOME (lhs, rhs, if is_less t then LESS else LE)
      else if is_minus_const rhs andalso not (is_plus_const_gen lhs) then
        SOME (lhs, rhs, if is_less t then LESS else LE)
      else NONE
    end

(* Matching function. *)
fun find_contradiction_item pat item ctxt (id, inst) =
    let
      val (x, y, d1, th1) = get_nat_order_info item

      fun process_pattern (pat_l, pat_r, order_ty) =
          let
            val pairs = [(false, (pat_l, y)), (false, (pat_r, x))]
          in
            map (pair order_ty)
                (Matcher.rewrite_match_list ctxt pairs (id, inst))
          end

      val insts = process_pattern (analyze_pattern pat)
      val insts2 = case analyze_pattern2 pat of
                       NONE => [] | SOME pattern => process_pattern pattern

      fun process_inst (order_ty, ((id', inst'), eq_ths)) =
          let
            val (eq_th1, eq_th2) = the_pair eq_ths
            val assum = pat |> Util.subst_term_norm inst'
                            |> mk_Trueprop |> Thm.cterm_of ctxt
            val th2 = assum |> Thm.assume
                            |> apply_to_thm' (Conv.arg1_conv (rewr_side eq_th1))
                            |> apply_to_thm' (Conv.arg_conv (rewr_side eq_th2))
                            |> to_normal_th order_ty
            val (_, _, d2) = dest_ineq_th th2
          in
            if d1 + d2 < 0 then
              [((id', inst'),
                (order_trans_resolve th1 th2)
                    |> Thm.implies_intr assum
                    |> apply_to_thm UtilLogic.rewrite_from_contra_form)]
            else []
          end
    in
      maps process_inst (insts @ insts2)
    end

fun nat_order_match pat item ctxt (id, inst) =
    if not (is_order_pat ctxt pat) then [] else
    let
      val is_neg = is_neg pat
      val neg_pat = get_neg_order pat
      val res = find_contradiction_item neg_pat item ctxt (id, inst)
    in
      if is_neg then res
      else res |> map (apsnd (apply_to_thm' UtilArith.neg_ineq_cv))
    end

fun nat_order_pre_match pat item ctxt =
    if not (is_order_pat ctxt pat) then false else
    let
      val neg_pat = get_neg_order pat
      val (x, y, _, _) = get_nat_order_info item

      fun process_pattern (pat_l, pat_r, _) =
          Matcher.pre_match ctxt (pat_l, y) andalso
          Matcher.pre_match ctxt (pat_r, x)

      val match1 = process_pattern (analyze_pattern neg_pat)
      val match2 = case analyze_pattern2 neg_pat of
                       NONE => false | SOME pattern => process_pattern pattern
    in
      match1 orelse match2
    end

(* Prop-matching with a NAT_ORDER item. *)
val nat_order_matcher =
    {pre_match = nat_order_pre_match, match = nat_order_match}

(* Use x < y to match x ~= y. *)
val nat_order_noteq_matcher =
    let
      fun get_insts pat item ctxt (id, inst) =
          if not (is_neg pat andalso is_eq_term (dest_not pat)) then ([], [])
          else let
            val (A, B) = pat |> dest_not |> dest_eq
            val (cx, cy, n, _) = get_nat_order_info item
          in
            if n >= 0 then ([], [])
            else (Matcher.rewrite_match_list
                      ctxt [(false, (A, cx)), (false, (B, cy))] (id, inst),
                  Matcher.rewrite_match_list
                      ctxt [(false, (B, cx)), (false, (A, cy))] (id, inst))
          end

      fun pre_match pat item ctxt =
          if not (is_neg pat andalso is_eq_term (dest_not pat)) then false
          else let
            val (A, B) = pat |> dest_not |> dest_eq
            val (cx, cy, n, _) = get_nat_order_info item
          in
            n < 0 andalso ((Matcher.pre_match ctxt (A, cx) andalso
                            Matcher.pre_match ctxt (B, cy)) orelse
                           (Matcher.pre_match ctxt (A, cy) andalso
                            Matcher.pre_match ctxt (A, cx)))
          end

      fun match pat item ctxt (id, inst) =
          if Util.has_vars pat then [] else
          let
            val (instAB, instBA) = get_insts pat item ctxt (id, inst)
            fun process_inst (inst', ths) =
                let
                  (* eq_x: (A/B) = x, eq_y: (B/A) = y *)
                  val (eq_x, eq_y) = the_pair ths
                  val (_, _, n, prop) = item |> get_nat_order_info
                                             |> rewrite_info_x (meta_sym eq_x)
                                             |> rewrite_info_y (meta_sym eq_y)
                in
                  (inst', [prop, nat_less_th 0 (~n)]
                              MRS @{thm nat_ineq_impl_not_eq})
                end
            fun switch_ineq (inst', th) = (inst', th RS @{thm HOL.not_sym})
          in
            map process_inst instAB @ (map (switch_ineq o process_inst) instBA)
          end
    in
      {pre_match = pre_match, match = match}
    end

(* Given pattern pat, find substitutions of pat that give rise to a
   contradiction.
 *)
fun find_contradiction pat ctxt (id, inst) =
    let
      fun process_pattern (pat_l, pat_r, order_ty) =
          map (fn (id', eq_th) =>
                  (order_ty,
                   (id', eq_th, Thm.reflexive (Thm.cterm_of ctxt pat_r))))
              (RewriteTable.equiv_info_t ctxt id (pat_l, pat_r))

      val insts = process_pattern (analyze_pattern pat)
      val insts2 = case analyze_pattern2 pat of
                       NONE => [] | SOME pattern => process_pattern pattern

      fun process_inst (order_ty, (id', eq_th1, eq_th2)) =
          let
            val assum = pat |> Util.subst_term_norm inst
                            |> mk_Trueprop |> Thm.cterm_of ctxt
            val norm_th =
                assum |> Thm.assume
                      |> apply_to_thm' (Conv.arg1_conv (rewr_side eq_th1))
                      |> apply_to_thm' (Conv.arg_conv (rewr_side eq_th2))
                      |> to_normal_th order_ty
            val (lhs, rhs) = Util.dest_binop_args (prop_of' norm_th)
          in
            if is_plus_const lhs andalso dest_arg1 lhs aconv rhs then
              let
                val d = dest_numc (dest_arg lhs)
              in
                if d = 0 then [] else
                [((id', inst),
                  ([nat_less_th 0 d, norm_th] MRS @{thm single_resolve})
                      |> Thm.implies_intr assum
                      |> apply_to_thm UtilLogic.rewrite_from_contra_form)]
              end
            else []
          end
    in
      maps process_inst (insts @ insts2)
    end

(* For patterns in the form m < n, where m and n are constants. *)
fun find_contradiction_trivial pat ctxt (id, inst) =
    let
      val (A, B) = Util.dest_binop_args pat
    in
      if not (is_numc A andalso is_numc B) then [] else
      if not (is_less pat andalso dest_numc A >= dest_numc B) andalso
         not (is_less_eq pat andalso dest_numc A > dest_numc B) then []
      else let
        val assum = pat |> mk_Trueprop |> Thm.cterm_of ctxt
      in
        [((id, inst),
          (UtilArith.contra_by_arith ctxt [Thm.assume assum])
              |> Thm.implies_intr assum
              |> apply_to_thm UtilLogic.rewrite_from_contra_form)]
      end
    end

(* For patterns in the form x < 0. *)
fun find_contradiction_trivial2 pat ctxt (id, inst) =
    let
      val (_, B) = Util.dest_binop_args pat
    in
      if is_less pat andalso B aconv nat0 then
        let
          val assum = pat |> mk_Trueprop |> Thm.cterm_of ctxt
        in
          [((id, inst),
            ([@{thm Nat.not_less0}, Thm.assume assum] MRS UtilBase.contra_triv_th)
                |> Thm.implies_intr assum
                |> apply_to_thm UtilLogic.rewrite_from_contra_form)]
        end
      else []
    end

(* Using term x to justify propositions of the form x <= x + n, where
   n >= 0. This follows the same general outline as nat_order_match.
 *)
fun nat_order_single_match pat _ ctxt (id, inst) =
    if not (is_order_pat ctxt pat) orelse Util.has_vars pat then [] else
    let
      val is_neg = is_neg pat
      val neg_pat = get_neg_order pat
      val (A, B) = Util.dest_binop_args neg_pat
      val res =
          if is_less neg_pat andalso B aconv nat0 then
            find_contradiction_trivial2 neg_pat ctxt (id, inst)
          else if is_numc A andalso is_numc B then
            find_contradiction_trivial neg_pat ctxt (id, inst)
          else
            find_contradiction neg_pat ctxt (id, inst)
    in
      if is_neg then res
      else res |> map (apsnd (apply_to_thm' UtilArith.neg_ineq_cv))
    end

val nat_order_single_matcher =
    {pre_match = (fn pat => fn _ => fn ctxt => is_order_pat ctxt pat),
     match = nat_order_single_match}

(* Shadow the second item if it is looser than the first (same x and
   y, but larger diff.
 *)
val shadow_nat_order_prfstep =
    ProofStep.gen_prfstep
        "shadow_nat_order"
        [WithItem (TY_NAT_ORDER, @{term_pat "(?x, ?y, ?m)"}),
         WithItem (TY_NAT_ORDER, @{term_pat "(?x, ?y, ?n)"}),
         Filter (fn _ => fn (_, inst) =>
                    dest_numc (lookup_inst inst "m") <=
                    dest_numc (lookup_inst inst "n")),
         ShadowSecond]

(* Shadow the given item if it is trivial. There are two cases: when
   two sides are equal, and when the left side is zero (both with
   nonnegative diff).
 *)
val shadow_nat_order_single =
    ProofStep.gen_prfstep
        "shadow_nat_order_single"
        [WithItem (TY_NAT_ORDER, @{term_pat "(?x, ?x, ?n)"}),
         Filter (fn _ => fn (_, inst) => dest_numc (lookup_inst inst "n") >= 0),
         ShadowFirst]

val shadow_nat_order_single_zero =
    ProofStep.gen_prfstep
        "shadow_nat_order_single_zero"
        [WithItem (TY_NAT_ORDER, @{term_pat "(0, ?x, ?n)"}),
         Filter (fn _ => fn (_, inst) => dest_numc (lookup_inst inst "n") >= 0),
         ShadowFirst]

fun string_of_nat_order ctxt (x, y, diff, th) =
    if x aconv nat0 andalso diff < 0 then  (* 0 + n <= y *)
      th |> apply_to_thm' (Conv.arg1_conv nat_fold_conv0_left)
         |> Thm.prop_of |> Syntax.string_of_term ctxt
    else if y aconv nat0 andalso diff >= 0 then  (* x <= 0 + n *)
      th |> apply_to_thm' (Conv.arg_conv nat_fold_conv0_left)
         |> Thm.prop_of |> Syntax.string_of_term ctxt
    else if diff = 0 then  (* x <= y + 0 *)
      th |> apply_to_thm' (Conv.arg_conv nat_fold_conv0_right)
         |> Thm.prop_of |> Syntax.string_of_term ctxt
    else
      th |> Thm.prop_of |> Syntax.string_of_term ctxt

fun output_nat_order ctxt (ts, th) =
    let
      val (x, y, diff_t) = the_triple ts
      val diff = dest_numc diff_t
    in
      "ORDER " ^ string_of_nat_order ctxt (x, y, diff, th)
    end

fun shadow_nat_order _ _ (ts1, cts2) =
    let
      val (x1, y1, m) = the_triple ts1
      val (cx2, cy2, n) = the_triple cts2
      val m = dest_numc m
      val n = dest_numc (Thm.term_of n)
    in
      if m < n then false else
      x1 aconv Thm.term_of cx2 andalso y1 aconv Thm.term_of cy2
    end

val add_nat_order_proofsteps =
    ItemIO.add_item_type (
      TY_NAT_ORDER, SOME (take 2), SOME output_nat_order, SOME shadow_nat_order

    ) #> ItemIO.add_typed_matcher (
      TY_NAT_ORDER, nat_order_typed_matcher

    ) #> fold ItemIO.add_prop_matcher [
      (TY_NAT_ORDER, nat_order_matcher),
      (TY_NAT_ORDER, nat_order_noteq_matcher),
      (TY_NULL, nat_order_single_matcher)

    ] #> Normalizer.add_normalizer (
      ("nat_order", nat_order_normalizer)

    ) #> fold add_prfstep [
      nat_eq_diff_prfstep,
      transitive, transitive_resolve, single_resolve, single_resolve_zero,
      shadow_nat_order_prfstep, shadow_nat_order_single,
      shadow_nat_order_single_zero
    ]

end

val _ = Theory.setup (Nat_Order.add_nat_order_proofsteps)
