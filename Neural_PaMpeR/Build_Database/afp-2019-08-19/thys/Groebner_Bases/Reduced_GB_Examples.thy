(* Author: Alexander Maletzky *)

section \<open>Sample Computations of Reduced Gr\"obner Bases\<close>

theory Reduced_GB_Examples
  imports Buchberger Reduced_GB Polynomials.MPoly_Type_Class_OAlist Code_Target_Rat
begin

context gd_term
begin

definition rgb :: "('t \<Rightarrow>\<^sub>0 'b) list \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b::field) list"
  where "rgb bs = comp_red_monic_basis (map fst (gb (map (\<lambda>b. (b, ())) bs) ()))"

definition rgb_punit :: "('a \<Rightarrow>\<^sub>0 'b) list \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b::field) list"
  where "rgb_punit bs = punit.comp_red_monic_basis (map fst (gb_punit (map (\<lambda>b. (b, ())) bs) ()))"

lemma compute_trd_aux [code]:
  "trd_aux fs p r =
    (if is_zero p then
      r
    else
      case find_adds fs (lt p) of
        None   \<Rightarrow> trd_aux fs (tail p) (plus_monomial_less r (lc p) (lt p))
      | Some f \<Rightarrow> trd_aux fs (tail p - monom_mult (lc p / lc f) (lp p - lp f) (tail f)) r
    )"
  by (simp only: trd_aux.simps[of fs p r] plus_monomial_less_def is_zero_def)

end

text \<open>We only consider scalar polynomials here, but vector-polynomials could be handled, too.\<close>

global_interpretation punit': gd_powerprod "ord_pp_punit cmp_term" "ord_pp_strict_punit cmp_term"
  rewrites "punit.adds_term = (adds)"
  and "punit.pp_of_term = (\<lambda>x. x)"
  and "punit.component_of_term = (\<lambda>_. ())"
  and "punit.monom_mult = monom_mult_punit"
  and "punit.mult_scalar = mult_scalar_punit"
  and "punit'.punit.min_term = min_term_punit"
  and "punit'.punit.lt = lt_punit cmp_term"
  and "punit'.punit.lc = lc_punit cmp_term"
  and "punit'.punit.tail = tail_punit cmp_term"
  and "punit'.punit.ord_p = ord_p_punit cmp_term"
  and "punit'.punit.ord_strict_p = ord_strict_p_punit cmp_term"
  for cmp_term :: "('a::nat, 'b::{nat,add_wellorder}) pp nat_term_order"

  defines find_adds_punit = punit'.punit.find_adds
  and trd_aux_punit = punit'.punit.trd_aux
  and trd_punit = punit'.punit.trd
  and spoly_punit = punit'.punit.spoly
  and count_const_lt_components_punit = punit'.punit.count_const_lt_components
  and count_rem_components_punit = punit'.punit.count_rem_components
  and const_lt_component_punit = punit'.punit.const_lt_component
  and full_gb_punit = punit'.punit.full_gb
  and add_pairs_single_sorted_punit = punit'.punit.add_pairs_single_sorted
  and add_pairs_punit = punit'.punit.add_pairs
  and canon_pair_order_aux_punit = punit'.punit.canon_pair_order_aux
  and canon_basis_order_punit = punit'.punit.canon_basis_order
  and new_pairs_sorted_punit = punit'.punit.new_pairs_sorted
  and product_crit_punit = punit'.punit.product_crit
  and chain_ncrit_punit = punit'.punit.chain_ncrit
  and chain_ocrit_punit = punit'.punit.chain_ocrit
  and apply_icrit_punit = punit'.punit.apply_icrit
  and apply_ncrit_punit = punit'.punit.apply_ncrit
  and apply_ocrit_punit = punit'.punit.apply_ocrit
  and trdsp_punit = punit'.punit.trdsp
  and gb_sel_punit = punit'.punit.gb_sel
  and gb_red_aux_punit = punit'.punit.gb_red_aux
  and gb_red_punit = punit'.punit.gb_red
  and gb_aux_punit = punit'.punit.gb_aux_punit
  and gb_punit = punit'.punit.gb_punit \<comment>\<open>Faster, because incorporates product criterion.\<close>
  and comp_min_basis_punit = punit'.punit.comp_min_basis
  and comp_red_basis_aux_punit = punit'.punit.comp_red_basis_aux
  and comp_red_basis_punit = punit'.punit.comp_red_basis
  and monic_punit = punit'.punit.monic
  and comp_red_monic_basis_punit = punit'.punit.comp_red_monic_basis
  and rgb_punit = punit'.punit.rgb_punit
  subgoal by (fact gd_powerprod_ord_pp_punit)
  subgoal by (fact punit_adds_term)
  subgoal by (simp add: id_def)
  subgoal by (fact punit_component_of_term)
  subgoal by (simp only: monom_mult_punit_def)
  subgoal by (simp only: mult_scalar_punit_def)
  subgoal using min_term_punit_def by fastforce
  subgoal by (simp only: lt_punit_def ord_pp_punit_alt)
  subgoal by (simp only: lc_punit_def ord_pp_punit_alt)
  subgoal by (simp only: tail_punit_def ord_pp_punit_alt)
  subgoal by (simp only: ord_p_punit_def ord_pp_strict_punit_alt)
  subgoal by (simp only: ord_strict_p_punit_def ord_pp_strict_punit_alt)
  done

lemma compute_spoly_punit [code]:
  "spoly_punit to p q = (let t1 = lt_punit to p; t2 = lt_punit to q; l = lcs t1 t2 in
         (monom_mult_punit (1 / lc_punit to p) (l - t1) p) - (monom_mult_punit (1 / lc_punit to q) (l - t2) q))"
  by (simp add: punit'.punit.spoly_def Let_def punit'.punit.lc_def)

lemma compute_trd_punit [code]: "trd_punit to fs p = trd_aux_punit to fs p (change_ord to 0)"
  by (simp only: punit'.punit.trd_def change_ord_def)

experiment begin interpretation trivariate\<^sub>0_rat .

lemma
  "rgb_punit DRLEX
    [
     X ^ 3 - X * Y * Z\<^sup>2,
     Y\<^sup>2 * Z - 1
    ] =
    [
     X ^ 3 * Y - X * Z,
     - (X ^ 3) + X * Y * Z\<^sup>2,
     Y\<^sup>2 * Z - 1,
     - (X * Z ^ 3) + X ^ 5
    ]"
  by eval

lemma
  "rgb_punit DRLEX
    [
     X\<^sup>2 + Y\<^sup>2 + Z\<^sup>2 - 1,
     X * Y - Z - 1,
     Y\<^sup>2 + X,
     Z\<^sup>2 + X
    ] =
    [
     1
    ]"
  by eval

text \<open>Note: The above computations have been cross-checked with Mathematica 11.1.\<close>

end

end (* theory *)
