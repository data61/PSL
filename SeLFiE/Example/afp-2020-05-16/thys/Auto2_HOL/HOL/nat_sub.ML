(*
  File: nat_sub.ML
  Author: Bohua Zhan

  Normalization of expressions involving subtraction on natural numbers.
*)

signature NAT_SUB =
sig
  val fheads: term list
  val norm_plus1: wfconv
  val norm_plus: wfconv
  val norm_minus': wfconv
  val move_outmost: term -> wfconv
  val cancel_terms: wfconv
  val norm_minus: wfconv
  type monomial = cterm list * int
  val reduce_monomial_list: monomial list -> monomial list
  val add_polynomial_list: monomial list * monomial list -> monomial list
  val norm_minus_ct: cterm -> monomial list
  val norm_ring_term: cterm -> term

  val get_sub_head_equiv:
      Proof.context -> box_id * cterm -> (box_id * (wfterm * thm)) list
  val nat_sub_expand_once:
      Proof.context -> box_id * wfterm -> (box_id * (wfterm * thm)) list
  val nat_sub_expand:
      Proof.context -> box_id * cterm -> (box_id * (wfterm * thm)) list

  val nat_sub_expand_equiv: proofstep
  val nat_sub_expand_unit: proofstep

  val add_nat_sub_proofsteps: theory -> theory
end;

structure NatSub : NAT_SUB =
struct

val fheads = [@{term "(+) :: (nat => nat => nat)"},
              @{term "(-) :: (nat => nat => nat)"},
              @{term "(*) :: (nat => nat => nat)"}]

val plus_info = Nat_Util.plus_ac_on_typ @{theory} natT
val is_numc = UtilArith.is_numc
val dest_numc = UtilArith.dest_numc
val is_plus = UtilArith.is_plus
val is_minus = UtilArith.is_minus
val is_times = UtilArith.is_times
val is_zero = UtilArith.is_zero
val is_one = UtilArith.is_one
val wf_rewr_obj_eq = WfTerm.rewr_obj_eq fheads
val nat0 = Nat_Util.nat0

val mult_1 = @{thm mult_1}  (* 1 * a = a *)
val mult_1_right = @{thm mult_1_right}  (* a * 1 = a *)
val mult_0 = @{thm mult_0}  (* 0 * a = 0 *)
val mult_0_right = @{thm mult_0_right}  (* a * 0 = 0 *)
val add_0 = @{thm add_0}  (* 0 + a = a *)
val add_0_right = @{thm add_0_right}  (* a + 0 = a *)

val add_assoc = wf_rewr_obj_eq @{thm add_ac(1)}
val add_assoc_sym = wf_rewr_obj_eq (obj_sym @{thm add_ac(1)})
val add_comm = wf_rewr_obj_eq @{thm add_ac(2)}
val swap_add = WfTerm.every_conv [add_assoc, WfTerm.arg_conv add_comm,
                                  add_assoc_sym]
val times_assoc = wf_rewr_obj_eq @{thm mult_ac(1)}
val times_assoc_sym = wf_rewr_obj_eq (obj_sym @{thm mult_ac(1)})
val times_comm = wf_rewr_obj_eq @{thm mult_ac(2)}
val swap_times = WfTerm.every_conv [times_assoc, WfTerm.arg_conv times_comm,
                                    times_assoc_sym]

val distrib_r_th = @{thm nat_distrib(1)}
val distrib_l_th = @{thm nat_distrib(2)}

val nat_fold_wfconv = WfTerm.conv_of Nat_Util.nat_fold_conv
val cancel_0_left = WfTerm.try_conv (wf_rewr_obj_eq @{thm add_0_left})
val append_0_left = wf_rewr_obj_eq (obj_sym @{thm add_0_left})

(* When comparing atoms, constants are greater than non-constants. *)
fun compare_atom (t1, t2) =
    if is_numc t1 andalso is_numc t2 then EQUAL
    else if is_numc t1 then GREATER
    else if is_numc t2 then LESS
    else Term_Ord.term_ord (t1, t2)

(* Multiply a monomial with an atom. *)
fun norm_mult_atom wft =
    let
      val t = WfTerm.term_of wft
      val (arg1, arg2) = Util.dest_binop_args t
    in
      if is_one arg1 then wf_rewr_obj_eq mult_1 wft
      else if is_one arg2 then wf_rewr_obj_eq mult_1_right wft
      else if is_zero arg1 then wf_rewr_obj_eq mult_0 wft
      else if is_zero arg2 then wf_rewr_obj_eq mult_0_right wft
      else if is_times arg1 then
        case compare_atom (dest_arg arg1, arg2) of
            GREATER =>
            WfTerm.every_conv [swap_times,
                               WfTerm.arg1_conv norm_mult_atom] wft
          | EQUAL =>
            if is_numc (dest_arg arg1) andalso is_numc arg2 then
              WfTerm.every_conv [times_assoc,
                                 WfTerm.arg_conv nat_fold_wfconv] wft
            else
              WfTerm.all_conv wft
          | _ => WfTerm.all_conv wft
      else
        case compare_atom (arg1, arg2) of
            GREATER => times_comm wft
          | EQUAL =>
            if is_numc arg1 andalso is_numc arg2 then
              nat_fold_wfconv wft
            else
              WfTerm.all_conv wft
          | _ => WfTerm.all_conv wft
    end

(* Multiply two monomials. *)
fun norm_mult_monomial wft =
    let
      val t = WfTerm.term_of wft
      val (_, arg2) = Util.dest_binop_args t
    in
      if is_times arg2 then
        WfTerm.every_conv [times_assoc_sym,
                           WfTerm.arg1_conv norm_mult_monomial,
                           norm_mult_atom] wft
      else
        norm_mult_atom wft
    end

(* Destruct t into the form arg * coeff, where coeff is a constant. *)
fun dest_monomial t =
    if is_times t andalso is_numc (dest_arg t) then
      (dest_arg1 t, UtilArith.dest_numc (dest_arg t))
    else if is_numc t then
      (Nat_Util.mk_nat 1, UtilArith.dest_numc t)
    else
      (t, 1)

(* Normalize ct into the form arg * coeff.

   Example: a * 4 == a * 4, a == a * 1, 4 == 1 * 4.
 *)
fun norm_monomial wft =
    let
      val t = WfTerm.term_of wft
    in
      if is_times t andalso is_numc (dest_arg t) then
        WfTerm.all_conv wft
      else if is_numc t then
        wf_rewr_obj_eq (obj_sym @{thm mult_1}) wft
      else
        wf_rewr_obj_eq (obj_sym @{thm mult_1_right}) wft
    end

(* Compare two monomials by removing coefficient. *)
fun compare_monomial (t1, t2) =
    let
      val (arg1, _) = dest_monomial t1
      val (arg2, _) = dest_monomial t2
    in
      if is_one arg1 andalso is_one arg2 then EQUAL
      else if is_one arg1 then GREATER
      else if is_one arg2 then LESS
      else Term_Ord.term_ord (arg1, arg2)
    end

(* Combine two monomials. *)
fun combine_monomial wft =
    WfTerm.every_conv [WfTerm.binop_conv norm_monomial,
                       wf_rewr_obj_eq (obj_sym distrib_l_th),
                       WfTerm.arg_conv nat_fold_wfconv] wft

(* Normalize a + b, where a is a sum and b is an atom. If b is a
   constant, add it to the end of a. Otherwise, insert b into sorted
   position.
 *)
fun norm_plus1 wft =
    let
      val (a, b) = wft |> WfTerm.term_of |> Util.dest_binop_args
    in
      if is_zero a then wf_rewr_obj_eq add_0 wft
      else if is_zero b then wf_rewr_obj_eq add_0_right wft
      else if is_plus a then
        case compare_monomial (dest_arg a, b) of
            LESS => WfTerm.all_conv wft
          | EQUAL =>
            if is_numc (dest_arg a) andalso is_numc b then
              WfTerm.every_conv [add_assoc,
                                 WfTerm.arg_conv nat_fold_wfconv] wft
            else
              WfTerm.every_conv [add_assoc,
                                 WfTerm.arg_conv combine_monomial] wft
          | GREATER =>
            WfTerm.every_conv [swap_add, WfTerm.arg1_conv norm_plus1] wft
      else
        case compare_monomial (a, b) of
            LESS => WfTerm.all_conv wft
          | EQUAL => if is_numc a andalso is_numc b then
                       nat_fold_wfconv wft
                     else
                       combine_monomial wft
          | GREATER => wf_rewr_obj_eq @{thm add_ac(2)} wft
    end

(* Normalize a + b, where a and b are both sums. *)
fun norm_plus wft =
    let
      val (_, b) = wft |> WfTerm.term_of |> Util.dest_binop_args
    in
      if is_plus b then
        WfTerm.every_conv [
          add_assoc_sym, WfTerm.arg1_conv norm_plus, norm_plus1] wft
      else
        norm_plus1 wft
    end

(* Assume wft is a sum containing u. Move u into the outermost position. *)
fun move_outmost u wft =
    if u aconv (WfTerm.term_of wft) then WfTerm.all_conv wft
    else if not (is_plus (WfTerm.term_of wft)) then
      raise Fail "move_outmost: u not found in wft."
    else let
      val (a, b) = wft |> WfTerm.term_of |> Util.dest_binop_args
    in
      if u aconv b then WfTerm.all_conv wft
      else if is_plus a then
        WfTerm.every_conv [WfTerm.arg1_conv (move_outmost u), swap_add] wft
      else if u aconv a then
        add_comm wft
      else
        raise Fail "move_outmost: u not found in wft."
    end

(* Cancel terms with the same argument from the two sides. *)
fun cancel_terms wft =
    let
      val (a, b) = wft |> WfTerm.term_of |> Util.dest_binop_args
      val (ts1, ts2) = apply2 (ACUtil.dest_ac plus_info) (a, b)

      fun find_same_arg (t1, t2) =
          case compare_monomial (t1, t2) of
              EQUAL => if t1 aconv nat0 orelse t2 aconv nat0 then NONE
                       else SOME (t1, t2)
            | _ => NONE

      fun prepare_left t1 =
          if length ts1 = 1 then WfTerm.arg1_conv append_0_left
          else WfTerm.arg1_conv (move_outmost t1)

      fun prepare_right t2 =
          if length ts2 = 1 then WfTerm.arg_conv append_0_left
          else WfTerm.arg_conv (move_outmost t2)

      fun apply_th (t1, t2) wft =
          let
            val (_, n1) = dest_monomial t1
            val (_, n2) = dest_monomial t2
            val fold_cv =
                WfTerm.every_conv [
                  WfTerm.arg_conv nat_fold_wfconv,
                  WfTerm.try_conv (wf_rewr_obj_eq mult_1),
                  WfTerm.try_conv (wf_rewr_obj_eq mult_1_right)]
            val le_th = if n1 >= n2 then Nat_Util.nat_le_th n2 n1
                        else Nat_Util.nat_le_th n1 n2
          in
            if n1 = n2 then
              wf_rewr_obj_eq @{thm nat_sub_combine} wft
            else if n1 > n2 then
              WfTerm.every_conv [
                WfTerm.binop_conv (WfTerm.arg_conv norm_monomial),
                wf_rewr_obj_eq (le_th RS @{thm nat_sub_combine2}),
                WfTerm.arg1_conv (WfTerm.arg_conv fold_cv),
                WfTerm.arg1_conv norm_plus] wft
            else
              WfTerm.every_conv [
                WfTerm.binop_conv (WfTerm.arg_conv norm_monomial),
                wf_rewr_obj_eq (le_th RS @{thm nat_sub_combine3}),
                WfTerm.arg_conv (WfTerm.arg_conv fold_cv),
                WfTerm.arg_conv norm_plus] wft
          end
    in
      case get_first find_same_arg (Util.all_pairs (ts1, ts2)) of
          NONE => WfTerm.all_conv wft
        | SOME (t1, t2) =>
          WfTerm.every_conv [prepare_left t1, prepare_right t2,
                             apply_th (t1, t2),
                             WfTerm.arg1_conv cancel_0_left,
                             WfTerm.arg_conv cancel_0_left,
                             cancel_terms] wft
    end

fun norm_mult_poly_monomial wft =
    let
      val t = WfTerm.term_of wft
      val (arg1, _) = Util.dest_binop_args t
    in
      if is_plus arg1 then
        WfTerm.every_conv [wf_rewr_obj_eq distrib_r_th,
                           WfTerm.arg1_conv norm_mult_poly_monomial,
                           WfTerm.arg_conv norm_mult_monomial,
                           norm_plus] wft
      else
        norm_mult_monomial wft
    end

fun norm_mult_polynomials wft =
    let
      val t = WfTerm.term_of wft
      val (_, arg2) = Util.dest_binop_args t
    in
      if is_plus arg2 then
        WfTerm.every_conv [wf_rewr_obj_eq distrib_l_th,
                           WfTerm.arg1_conv norm_mult_polynomials,
                           WfTerm.arg_conv norm_mult_poly_monomial,
                           norm_plus] wft
      else
        norm_mult_poly_monomial wft
    end

(* First step, put wft into the form a - b, where a and b are
   normalized sums.
 *)
fun norm_minus' wft =
    let
      val t = WfTerm.term_of wft
    in
      if is_plus t then
        (* (a - b) + (c - d) = (a + c) - (b + d) *)
        WfTerm.every_conv [WfTerm.binop_conv norm_minus',
                           wf_rewr_obj_eq @{thm nat_sub1},
                           WfTerm.binop_conv norm_plus,
                           cancel_terms] wft
      else if is_minus t then
        (* (a - b) - (c - d) = (a + d) - (b + c) *)
        WfTerm.every_conv [WfTerm.binop_conv norm_minus',
                           wf_rewr_obj_eq @{thm nat_sub2},
                           WfTerm.binop_conv norm_plus,
                           cancel_terms] wft
      else if is_times t then
        (* (a - b) * (c - d) = (ac + bd) - (ad + bc) *)
        WfTerm.every_conv [
          WfTerm.binop_conv norm_minus',
          wf_rewr_obj_eq @{thm nat_sub3},
          WfTerm.binop_conv (WfTerm.binop_conv norm_mult_polynomials),
          WfTerm.binop_conv norm_plus,
          cancel_terms] wft
      else
        (* Normalize a into a - 0. *)
        wf_rewr_obj_eq @{thm nat_sub_norm} wft
    end

fun norm_minus wft =
    WfTerm.every_conv [
      norm_minus',
      WfTerm.try_conv (wf_rewr_obj_eq @{thm diff_zero})] wft

(* Fast computation of the expected normalization. Return a list of
   monomials.
 *)
type monomial = cterm list * int

fun mk_plus (t1, t2) =
    Const (@{const_name plus}, natT --> natT --> natT) $ t1 $ t2

fun list_plus ts =
    let
      fun list_rev ts =
          case ts of
              [] => Nat_Util.mk_nat 0
            | [t] => t
            | t :: ts' => mk_plus (list_rev ts', t)
    in
      list_rev (rev ts)
    end

fun mk_times (t1, t2) =
    Const (@{const_name times}, natT --> natT --> natT) $ t1 $ t2

fun list_times ts =
    let
      fun list_rev ts =
          case ts of
              [] => Nat_Util.mk_nat 1
            | [t] => t
            | t :: ts' => mk_times (list_rev ts', t)
    in
      list_rev (rev ts)
    end

(* Compare two monomials *)
fun compare_monomial_list ((l1, _), (l2, _)) =
    if null l1 andalso null l2 then EQUAL
    else if null l1 then GREATER
    else if null l2 then LESS
    else Term_Ord.term_ord (list_times (map Thm.term_of l1),
                            list_times (map Thm.term_of l2))

(* Reduce a list of monomials: combine monomials of the same body. *)
fun reduce_monomial_list ls =
    if null ls then []
    else let
      val ((l1, c1), rest) = (hd ls, reduce_monomial_list (tl ls))
    in
      case rest of
          [] => [(l1, c1)]
        | [(_, 0)] => [(l1, c1)]
        | (l2, c2) :: rest' =>
          if eq_list (op aconvc) (l1, l2) then
            if c1 + c2 = 0 then rest'
            else (l1, c1 + c2) :: rest'
          else (l1, c1) :: (l2, c2) :: rest'
    end

(* Multiply two monomials. *)
fun mult_monomial ((l1, c1), (l2, c2)) =
    ((l1 @ l2) |> sort (compare_atom o apply2 Thm.term_of), c1 * c2)

(* Multiply two such lists: take the pairwise product, sort within
   each monomial, then sort the list of monomials.
 *)
fun mult_polynomial_term (ls1, ls2) =
    (Util.all_pairs (ls1, ls2))
        |> map mult_monomial
        |> sort compare_monomial_list
        |> reduce_monomial_list

fun add_polynomial_list (ls1, ls2) =
    (ls1 @ ls2) |> sort compare_monomial_list |> reduce_monomial_list

fun negate_polynomial_list ls =
    map (fn (ls, n) => (ls, ~n)) ls

fun norm_minus_ct ct =
    let
      val t = Thm.term_of ct
    in
      if is_plus t then
        add_polynomial_list (norm_minus_ct (Thm.dest_arg1 ct),
                             norm_minus_ct (Thm.dest_arg ct))
      else if is_minus t then
        add_polynomial_list (
          norm_minus_ct (Thm.dest_arg1 ct),
          negate_polynomial_list (norm_minus_ct (Thm.dest_arg ct)))
      else if is_times t then
        mult_polynomial_term (norm_minus_ct (Thm.dest_arg1 ct),
                              norm_minus_ct (Thm.dest_arg ct))
      else if is_numc t then
        [([], dest_numc t)]
      else
        [([ct], 1)]
    end

fun subterms_of ct =
    ct |> norm_minus_ct |> map fst |> flat

fun to_monomial (l, c) =
    if null l then mk_nat c
    else if c = 1 then list_times (map Thm.term_of l)
    else mk_times (list_times (map Thm.term_of l), mk_nat c)

fun norm_ring_term ct =
    let
      val dest_ring = norm_minus_ct ct
      val (ps, ms) = filter_split (fn (_, n) => n >= 0) dest_ring
    in
      if length ms > 0 then
        Const (@{const_name minus}, natT --> natT --> natT) $
              list_plus (map to_monomial ps) $
              list_plus (map to_monomial (negate_polynomial_list ms))
      else
        list_plus (map to_monomial ps)
    end

(* Obtain head equivalences of cu, normalized to a - b form, and where
   each term is simplified.
 *)
fun get_sub_head_equiv ctxt (id, ct) =
    let
      fun process_wf_head_equiv (id', (wft, eq_th)) =
          let
            val cts = subterms_of (Thm.rhs_of eq_th)
            val simps = WellformData.simplify ctxt fheads cts (id', wft)

            fun process_simp (id'', (wft', eq_th')) =
                (BoxID.merge_boxes ctxt (id', id''),
                 (wft', Util.transitive_list [eq_th, eq_th']))
          in
            map process_simp simps
          end
    in
      (id, ct) |> WellformData.get_head_equiv ctxt fheads
               |> maps process_wf_head_equiv
               |> filter_out (Thm.is_reflexive o snd o snd)
    end

(* Given wft in normalized form a - b, expand one of the subterms
   once. Calls the corresponding function in ac_steps on a and b, then
   combine the results.
 *)
fun nat_sub_expand_once ctxt (id, wft) =
    let
      val ct = WfTerm.cterm_of wft
      val subt = subterms_of ct
      fun get_equiv cu = get_sub_head_equiv ctxt (id, cu)

      fun process_info (id', wf_eq) =
          (id', WfTerm.rewrite_on_eqs fheads [wf_eq] wft)
    in
      map process_info (maps get_equiv subt)
    end

(* Find all ways to write ct, up to a certain limit. *)
fun nat_sub_expand ctxt (id, ct) =
    let
      val max_ac = Config.get ctxt AC_ProofSteps.max_ac

      fun ac_equiv_eq_better (id, (_, th)) (id', (_, th')) =
          let
            val seq1 = subterms_of (Thm.rhs_of th)
            val seq2 = subterms_of (Thm.rhs_of th')
          in
            Util.is_subseq (op aconvc) (seq1, seq2) andalso
            BoxID.is_eq_ancestor ctxt id id'
          end

      fun has_ac_equiv_eq_better infos info' =
          exists (fn info => ac_equiv_eq_better info info') infos

      fun helper (old, new) =
          case new of
              [] => old
            | (id', (wft, eq_th)) :: rest =>
              if length old + length new > max_ac then
                old @ take (max_ac - length old) new
              else let
                val old' = ((id', (wft, eq_th)) :: old)

                fun merge_info (id'', (wft', eq_th')) =
                    (BoxID.merge_boxes ctxt (id', id''),
                     (wft', Util.transitive_list [eq_th, eq_th']))

                val rhs_expand =
                    (nat_sub_expand_once ctxt (id', wft))
                        |> Util.max_partial ac_equiv_eq_better
                        |> map merge_info
                        |> filter_out (has_ac_equiv_eq_better (old' @ rest))
              in
                helper (old', rest @ rhs_expand)
              end

      (* Start term *)
      val ts = subterms_of ct
      val start = (WellformData.cterm_to_wfterm ctxt fheads (id, ct))
                      |> maps (WellformData.simplify ctxt fheads ts)
    in
      helper ([], start)
    end

fun is_nat_sub_form t =
    if is_plus t orelse is_minus t orelse is_times t then
      fastype_of (dest_arg t) = natT
    else false

fun nat_sub_expand_equiv_fn ctxt item1 item2 =
    let
      val {id = id1, tname = tname1, ...} = item1
      val {id = id2, tname = tname2, ...} = item2
      val (ct1, ct2) = (the_single tname1, the_single tname2)
      val (t1, t2) = (Thm.term_of ct1, Thm.term_of ct2)
      val id = BoxID.merge_boxes ctxt (id1, id2)
    in
      if not (is_nat_sub_form t1) orelse not (is_nat_sub_form t2) then []
      else if Term_Ord.term_ord (t2, t1) = LESS then []
      else if RewriteTable.is_equiv id ctxt (ct1, ct2) then []
      else let
        val expand1 = nat_sub_expand ctxt (id, ct1)
        val expand2 = nat_sub_expand ctxt (id, ct2)

        fun get_equiv ((id1, (wft1, eq_th1)), (id2, (wft2, eq_th2))) =
            let
              val ct1 = Thm.rhs_of eq_th1
              val ct2 = Thm.rhs_of eq_th2
              val ts1 = norm_minus_ct ct1
              val ts2 = norm_minus_ct ct2
            in
              if eq_list (eq_pair (eq_list (op aconvc)) (op =)) (ts1, ts2) then
                let
                  val (wft1', eq1) = norm_minus wft1
                  val (wft2', eq2) = norm_minus wft2
                  val _ = assert (WfTerm.term_of wft1' aconv WfTerm.term_of wft2')
                                 "nat_sub_expand_equiv_fn"
                  val id' = BoxID.merge_boxes ctxt (id1, id2)
                  val eq = Util.transitive_list [
                        eq_th1, eq1, meta_sym eq2, meta_sym eq_th2]
                in
                  [(id', to_obj_eq eq)]
                end
              else []
            end
      in
        (maps get_equiv (Util.all_pairs (expand1, expand2)))
            |> filter (BoxID.has_incr_id o fst)
            |> Util.max_partial (BoxID.id_is_eq_ancestor ctxt)
            |> map (fn (id, th) => Update.thm_update_sc 1 (id, th))
      end
    end

val nat_sub_expand_equiv =
    {name = "nat_sub_expand_equiv",
     args = [TypedMatch (TY_TERM, @{term_pat "?A::nat"}),
             TypedMatch (TY_TERM, @{term_pat "?B::nat"})],
     func = TwoStep nat_sub_expand_equiv_fn}

fun nat_sub_expand_unit_fn ctxt item =
    let
      val {id, tname, ...} = item
      val ct = the_single tname
      val t = Thm.term_of ct
    in
      if not (is_nat_sub_form t) then []
      else let
        val expand = nat_sub_expand ctxt (id, ct)

        fun process_expand (id', (wft, eq_th)) =
            let
              val ct = Thm.rhs_of eq_th
              val ts = norm_minus_ct ct
            in
              if length ts = 0 orelse
                 (length ts = 1 andalso snd (the_single ts) = 1) then
                let
                  val (_, eq') = norm_minus wft
                  val eq = Util.transitive_list [eq_th, eq']
                in
                  [(id', to_obj_eq eq)]
                end
              else []
            end
      in
        (maps process_expand expand)
            |> filter (BoxID.has_incr_id o fst)
            |> map (fn (id, th) => Update.thm_update_sc 1 (id, th))
      end
    end

val nat_sub_expand_unit =
    {name = "nat_sub_expand_unit",
     args = [TypedMatch (TY_TERM, @{term_pat "?A::nat"})],
     func = OneStep nat_sub_expand_unit_fn}

val add_nat_sub_proofsteps =
    fold add_prfstep [
      nat_sub_expand_equiv, nat_sub_expand_unit
    ]

end  (* NatSub *)

val _ = Theory.setup NatSub.add_nat_sub_proofsteps
