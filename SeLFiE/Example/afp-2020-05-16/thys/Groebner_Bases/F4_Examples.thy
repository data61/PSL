(* Author: Alexander Maletzky *)

section \<open>Sample Computations with the F4 Algorithm\<close>

theory F4_Examples
  imports F4 Algorithm_Schema_Impl Jordan_Normal_Form.Gauss_Jordan_IArray_Impl Code_Target_Rat
begin

text \<open>We only consider scalar polynomials here, but vector-polynomials could be handled, too.\<close>

subsection \<open>Preparations\<close>

primrec remdups_wrt_rev :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> 'b list \<Rightarrow> 'a list" where
  "remdups_wrt_rev f [] vs = []" |
  "remdups_wrt_rev f (x # xs) vs =
    (let fx = f x in if List.member vs fx then remdups_wrt_rev f xs vs else x # (remdups_wrt_rev f xs (fx # vs)))"

lemma remdups_wrt_rev_notin: "v \<in> set vs \<Longrightarrow> v \<notin> f ` set (remdups_wrt_rev f xs vs)"
proof (induct xs arbitrary: vs)
  case Nil
  show ?case by simp
next
  case (Cons x xs)
  from Cons(2) have 1: "v \<notin> f ` set (remdups_wrt_rev f xs vs)" by (rule Cons(1))
  from Cons(2) have "v \<in> set (f x # vs)" by simp
  hence 2: "v \<notin> f ` set (remdups_wrt_rev f xs (f x # vs))" by (rule Cons(1))
  from Cons(2) show ?case by (auto simp: Let_def 1 2 List.member_def)
qed

lemma distinct_remdups_wrt_rev: "distinct (map f (remdups_wrt_rev f xs vs))"
proof (induct xs arbitrary: vs)
  case Nil
  show ?case by simp
next
  case (Cons x xs)
  show ?case by (simp add: Let_def Cons(1) remdups_wrt_rev_notin)
qed

lemma map_of_remdups_wrt_rev':
  "map_of (remdups_wrt_rev fst xs vs) k = map_of (filter (\<lambda>x. fst x \<notin> set vs) xs) k"
proof (induct xs arbitrary: vs)
  case Nil
  show ?case by simp
next
  case (Cons x xs)
  show ?case
  proof (simp add: Let_def List.member_def Cons, intro impI)
    assume "k \<noteq> fst x"
    have "map_of (filter (\<lambda>y. fst y \<noteq> fst x \<and> fst y \<notin> set vs) xs) =
          map_of (filter (\<lambda>y. fst y \<noteq> fst x) (filter (\<lambda>y. fst y \<notin> set vs) xs))"
      by (simp only: filter_filter conj_commute)
    also have "... = map_of (filter (\<lambda>y. fst y \<notin> set vs) xs) |` {y. y \<noteq> fst x}" by (rule map_of_filter)
    finally show "map_of (filter (\<lambda>y. fst y \<noteq> fst x \<and> fst y \<notin> set vs) xs) k =
                  map_of (filter (\<lambda>y. fst y \<notin> set vs) xs) k"
      by (simp add: restrict_map_def \<open>k \<noteq> fst x\<close>)
  qed
qed

corollary map_of_remdups_wrt_rev: "map_of (remdups_wrt_rev fst xs []) = map_of xs"
  by (rule ext, simp add: map_of_remdups_wrt_rev')

lemma (in term_powerprod) compute_list_to_poly [code]:
  "list_to_poly ts cs = distr\<^sub>0 DRLEX (remdups_wrt_rev fst (zip ts cs) [])"
  by (rule poly_mapping_eqI,
      simp add: lookup_list_to_poly list_to_fun_def distr\<^sub>0_def oalist_of_list_ntm_def
        oa_ntm.lookup_oalist_of_list distinct_remdups_wrt_rev lookup_dflt_def map_of_remdups_wrt_rev)

lemma (in ordered_term) compute_Macaulay_list [code]:
  "Macaulay_list ps =
     (let ts = Keys_to_list ps in
      filter (\<lambda>p. p \<noteq> 0) (mat_to_polys ts (row_echelon (polys_to_mat ts ps)))
     )"
  by (simp add: Macaulay_list_def Macaulay_mat_def Let_def)

declare conversep_iff [code]

derive (eq) ceq poly_mapping
derive (no) ccompare poly_mapping
derive (dlist) set_impl poly_mapping
derive (no) cenum poly_mapping

derive (eq) ceq rat
derive (no) ccompare rat
derive (dlist) set_impl rat
derive (no) cenum rat

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
  and "punit'.punit.keys_to_list = keys_to_list_punit cmp_term"
  for cmp_term :: "('a::nat, 'b::{nat,add_wellorder}) pp nat_term_order"

  defines max_punit = punit'.ordered_powerprod_lin.max
  and max_list_punit = punit'.ordered_powerprod_lin.max_list
  and find_adds_punit = punit'.punit.find_adds
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
  and Keys_to_list_punit = punit'.punit.Keys_to_list
  and sym_preproc_addnew_punit = punit'.punit.sym_preproc_addnew
  and sym_preproc_aux_punit = punit'.punit.sym_preproc_aux
  and sym_preproc_punit = punit'.punit.sym_preproc
  and Macaulay_mat_punit = punit'.punit.Macaulay_mat
  and Macaulay_list_punit = punit'.punit.Macaulay_list
  and pdata_pairs_to_list_punit = punit'.punit.pdata_pairs_to_list
  and Macaulay_red_punit = punit'.punit.Macaulay_red
  and f4_sel_aux_punit = punit'.punit.f4_sel_aux
  and f4_sel_punit = punit'.punit.f4_sel
  and f4_red_aux_punit = punit'.punit.f4_red_aux
  and f4_red_punit = punit'.punit.f4_red
  and f4_aux_punit = punit'.punit.f4_aux_punit
  and f4_punit = punit'.punit.f4_punit
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
  subgoal by (simp only: keys_to_list_punit_def ord_pp_punit_alt) 
  done

subsection \<open>Computations\<close>

experiment begin interpretation trivariate\<^sub>0_rat .

lemma
  "lt_punit DRLEX (X\<^sup>2 * Z ^ 3 + 3 * X\<^sup>2 * Y) = sparse\<^sub>0 [(0, 2), (2, 3)]"
  by eval

lemma
  "lc_punit DRLEX (X\<^sup>2 * Z ^ 3 + 3 * X\<^sup>2 * Y) = 1"
  by eval

lemma
  "tail_punit DRLEX (X\<^sup>2 * Z ^ 3 + 3 * X\<^sup>2 * Y) = 3 * X\<^sup>2 * Y"
  by eval

lemma
  "ord_strict_p_punit DRLEX (X\<^sup>2 * Z ^ 4 - 2 * Y ^ 3 * Z\<^sup>2) (X\<^sup>2 * Z ^ 7 + 2 * Y ^ 3 * Z\<^sup>2)"
  by eval

lemma
  "f4_punit DRLEX
    [
     (X\<^sup>2 * Z ^ 4 - 2 * Y ^ 3 * Z\<^sup>2, ()),
     (Y\<^sup>2 * Z + 2 * Z ^ 3, ())
    ] () =
    [
     (X\<^sup>2 * Y\<^sup>2 * Z\<^sup>2 + 4 * Y ^ 3 * Z\<^sup>2, ()),
     (X\<^sup>2 * Z ^ 4 - 2 * Y ^ 3 * Z\<^sup>2, ()),
     (Y\<^sup>2 * Z + 2 * Z ^ 3, ()),
     (X\<^sup>2 * Y ^ 4 * Z + 4 * Y ^ 5 * Z, ())
    ]"
  by eval

lemma
  "f4_punit DRLEX
    [
     (X\<^sup>2 + Y\<^sup>2 + Z\<^sup>2 - 1, ()),
     (X * Y - Z - 1, ()),
     (Y\<^sup>2 + X, ()),
     (Z\<^sup>2 + X, ())
    ] () =
    [
     (1, ())
    ]"
  by eval

end

value [code] "length (f4_punit DRLEX (map (\<lambda>p. (p, ())) ((cyclic DRLEX 4)::(_ \<Rightarrow>\<^sub>0 rat) list)) ())"

value [code] "length (f4_punit DRLEX (map (\<lambda>p. (p, ())) ((katsura DRLEX 2)::(_ \<Rightarrow>\<^sub>0 rat) list)) ())"

end (* theory *)
