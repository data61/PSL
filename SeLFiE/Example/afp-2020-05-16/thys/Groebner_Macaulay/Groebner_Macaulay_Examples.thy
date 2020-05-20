(* Author: Alexander Maletzky *)

section \<open>Sample Computations of Gr\"obner Bases via Macaulay Matrices\<close>

theory Groebner_Macaulay_Examples
  imports
    Groebner_Macaulay
    Dube_Bound
    Groebner_Bases.Benchmarks
    Jordan_Normal_Form.Gauss_Jordan_IArray_Impl
    Groebner_Bases.Code_Target_Rat
begin

subsection \<open>Combining @{theory Groebner_Macaulay.Groebner_Macaulay} and
  @{theory Groebner_Macaulay.Dube_Bound}\<close>

context extended_ord_pm_powerprod
begin

theorem thm_2_3_6_Dube:
  assumes "finite X" and "set fs \<subseteq> P[X]"
  shows "punit.is_Groebner_basis (set (punit.Macaulay_list
                                        (deg_shifts X (Dube (Suc (card X)) (maxdeg (set fs))) fs)))"
  using assms Dube_is_GB_cofactor_bound by (rule thm_2_3_6) (simp_all add: assms)

theorem thm_2_3_7_Dube:
  assumes "finite X" and "set fs \<subseteq> P[X]"
  shows "1 \<in> ideal (set fs) \<longleftrightarrow>
          1 \<in> set (punit.Macaulay_list (deg_shifts X (Dube (Suc (card X)) (maxdeg (set fs))) fs))"
  using assms Dube_is_GB_cofactor_bound by (rule thm_2_3_7) (simp_all add: assms)

theorem thm_2_3_6_indets_Dube:
  fixes fs
  defines "X \<equiv> \<Union>(indets ` set fs)"
  shows "punit.is_Groebner_basis (set (punit.Macaulay_list
                                        (deg_shifts X (Dube (Suc (card X)) (maxdeg (set fs))) fs)))"
  unfolding X_def using Dube_is_GB_cofactor_bound_indets by (rule thm_2_3_6_indets) (fact finite_set)

theorem thm_2_3_7_indets_Dube:
  fixes fs
  defines "X \<equiv> \<Union>(indets ` set fs)"
  shows "1 \<in> ideal (set fs) \<longleftrightarrow>
          1 \<in> set (punit.Macaulay_list (deg_shifts X (Dube (Suc (card X)) (maxdeg (set fs))) fs))"
  unfolding X_def using Dube_is_GB_cofactor_bound_indets by (rule thm_2_3_7_indets) (fact finite_set)

end (* extended_ord_pm_powerprod *)

subsection \<open>Preparations\<close>

(* This is exactly the same as in "Groebner_Bases.F4_Examples". Pull out into common ancestor? *)

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

subsubsection \<open>Connection between @{typ "('x \<Rightarrow>\<^sub>0 'a) \<Rightarrow>\<^sub>0 'b"} and @{typ "('x, 'a) pp \<Rightarrow>\<^sub>0 'b"}\<close>

(* Move into "Polynomials.PP_Type"? *)

definition keys_pp_to_list :: "('x::linorder, 'a::zero) pp \<Rightarrow> 'x list"
  where "keys_pp_to_list t = sorted_list_of_set (keys_pp t)"

lemma inj_PP: "inj PP"
  by (simp add: PP_inject inj_def)

lemma inj_mapping_of: "inj mapping_of"
  by (simp add: mapping_of_inject inj_def)

lemma mapping_of_comp_PP [simp]:
  "mapping_of \<circ> PP = (\<lambda>x. x)"
  "PP \<circ> mapping_of = (\<lambda>x. x)"
  by (simp_all add: comp_def PP_inverse mapping_of_inverse)

lemma map_key_PP_mapping_of [simp]: "Poly_Mapping.map_key PP (Poly_Mapping.map_key mapping_of p) = p"
  by (simp add: map_key_compose[OF inj_PP inj_mapping_of] comp_def PP_inverse map_key_id)

lemma map_key_mapping_of_PP [simp]: "Poly_Mapping.map_key mapping_of (Poly_Mapping.map_key PP p) = p"
  by (simp add: map_key_compose[OF inj_mapping_of inj_PP] comp_def mapping_of_inverse map_key_id)

lemmas map_key_PP_plus = map_key_plus[OF inj_PP]
lemmas map_key_PP_zero [simp] = map_key_zero[OF inj_PP]

lemma lookup_map_key_PP: "lookup (Poly_Mapping.map_key PP p) t = lookup p (PP t)"
  by (simp add: map_key.rep_eq inj_PP)

lemma keys_map_key_PP: "keys (Poly_Mapping.map_key PP p) = mapping_of ` keys p"
  by (simp add: keys_map_key inj_PP)
     (smt Collect_cong PP_inverse UNIV_I image_def pp.mapping_of_inverse vimage_def)

lemma map_key_PP_zero_iff [iff]: "Poly_Mapping.map_key PP p = 0 \<longleftrightarrow> p = 0"
  by (metis map_key_PP_zero map_key_mapping_of_PP)

lemma map_key_PP_uminus [simp]: "Poly_Mapping.map_key PP (- p) = - Poly_Mapping.map_key PP p"
  by (rule poly_mapping_eqI) (simp add: lookup_map_key_PP)

lemma map_key_PP_minus:
  "Poly_Mapping.map_key PP (p - q) = Poly_Mapping.map_key PP p - Poly_Mapping.map_key PP q"
  by (rule poly_mapping_eqI) (simp add: lookup_map_key_PP lookup_minus)

lemma map_key_PP_monomial [simp]: "Poly_Mapping.map_key PP (monomial c t) = monomial c (mapping_of t)"
proof -
  have "Poly_Mapping.map_key PP (monomial c t) = Poly_Mapping.map_key PP (monomial c (PP (mapping_of t)))"
    by (simp only: mapping_of_inverse)
  also from inj_PP have "\<dots> = monomial c (mapping_of t)" by (fact map_key_single)
  finally show ?thesis .
qed

lemma map_key_PP_one [simp]: "Poly_Mapping.map_key PP 1 = 1"
  by (simp add: zero_pp.rep_eq flip: single_one)

lemma map_key_PP_monom_mult_punit:
  "Poly_Mapping.map_key PP (monom_mult_punit c t p) =
    monom_mult_punit c (mapping_of t) (Poly_Mapping.map_key PP p)"
  by (rule poly_mapping_eqI)
     (simp add: punit.lookup_monom_mult monom_mult_punit_def adds_pp_iff PP_inverse lookup_map_key_PP
          mapping_of_inverse flip: minus_pp.abs_eq)

lemma map_key_PP_times:
  "Poly_Mapping.map_key PP (p * q) =
    Poly_Mapping.map_key PP p * Poly_Mapping.map_key PP (q::(_, _::add_linorder) pp \<Rightarrow>\<^sub>0 _)"
  by (induct p rule: poly_mapping_plus_induct)
     (simp_all add: distrib_right map_key_PP_plus times_monomial_left map_key_PP_monom_mult_punit
        flip: monom_mult_punit_def)

lemma map_key_PP_sum: "Poly_Mapping.map_key PP (sum f A) = (\<Sum>a\<in>A. Poly_Mapping.map_key PP (f a))"
  by (induct A rule: infinite_finite_induct) (simp_all add: map_key_PP_plus)

lemma map_key_PP_ideal:
  "Poly_Mapping.map_key PP ` ideal F = ideal (Poly_Mapping.map_key PP ` (F::((_, _::add_linorder) pp \<Rightarrow>\<^sub>0 _) set))"
proof -
  from map_key_PP_mapping_of have "surj (Poly_Mapping.map_key PP)" by (rule surjI)
  with map_key_PP_plus map_key_PP_times show ?thesis by (rule image_ideal_eq_surj)
qed

subsubsection \<open>Locale \<open>pp_powerprod\<close>\<close>

text \<open>We have to introduce a new locale analogous to @{locale pm_powerprod}, but this time for
  power-products represented by @{type pp} rather than @{type poly_mapping}. This apparently leads
  to some (more-or-less) duplicate definitions and lemmas, but seems to be the only feasible way to
  get both
  \<^item> the convenient representation by @{type poly_mapping} for theory development, and
  \<^item> the executable representation by @{type pp} for code generation.\<close>

locale pp_powerprod =
  ordered_powerprod ord ord_strict
  for ord::"('x::{countable,linorder}, nat) pp \<Rightarrow> ('x, nat) pp \<Rightarrow> bool"
  and ord_strict
begin

sublocale gd_powerprod ..

sublocale pp_pm: extended_ord_pm_powerprod "\<lambda>s t. ord (PP s) (PP t)" "\<lambda>s t. ord_strict (PP s) (PP t)"
  by standard (auto simp: zero_min plus_monotone simp flip: zero_pp_def plus_pp.abs_eq PP_inject)

definition poly_deg_pp :: "(('x, nat) pp \<Rightarrow>\<^sub>0 'a::zero) \<Rightarrow> nat"
  where "poly_deg_pp p = (if p = 0 then 0 else max_list (map deg_pp (punit.keys_to_list p)))"

primrec deg_le_sect_pp_aux :: "'x list \<Rightarrow> nat \<Rightarrow> ('x, nat) pp \<Rightarrow>\<^sub>0 nat" where
  "deg_le_sect_pp_aux xs 0 = 1" |
  "deg_le_sect_pp_aux xs (Suc n) =
    (let p = deg_le_sect_pp_aux xs n in p + foldr (\<lambda>x. (+) (monom_mult_punit 1 (single_pp x 1) p)) xs 0)"

definition deg_le_sect_pp  :: "'x list \<Rightarrow> nat \<Rightarrow> ('x, nat) pp list"
  where "deg_le_sect_pp xs d = punit.keys_to_list (deg_le_sect_pp_aux xs d)"

definition deg_shifts_pp :: "'x list \<Rightarrow> nat \<Rightarrow>
                                (('x, nat) pp \<Rightarrow>\<^sub>0 'b) list \<Rightarrow> (('x, nat) pp \<Rightarrow>\<^sub>0 'b::semiring_1) list"
  where "deg_shifts_pp xs d fs = concat (map (\<lambda>f. (map (\<lambda>t. monom_mult_punit 1 t f)
                                          (deg_le_sect_pp xs (d - poly_deg_pp f)))) fs)"

definition indets_pp :: "(('x, nat) pp \<Rightarrow>\<^sub>0 'b::zero) \<Rightarrow> 'x list"
  where "indets_pp p = remdups (concat (map keys_pp_to_list (punit.keys_to_list p)))"

definition Indets_pp :: "(('x, nat) pp \<Rightarrow>\<^sub>0 'b::zero) list \<Rightarrow> 'x list"
  where "Indets_pp ps = remdups (concat (map indets_pp ps))"

lemma map_PP_insort:
  "map PP (pp_pm.ordered_powerprod_lin.insort x xs) = ordered_powerprod_lin.insort (PP x) (map PP xs)"
  by (induct xs) simp_all

lemma map_PP_sorted_list_of_set:
  "map PP (pp_pm.ordered_powerprod_lin.sorted_list_of_set T) =
    ordered_powerprod_lin.sorted_list_of_set (PP ` T)"
proof (induct T rule: infinite_finite_induct)
  case (infinite T)
  moreover from inj_PP subset_UNIV have "inj_on PP T" by (rule inj_on_subset)
  ultimately show ?case by (simp add: inj_PP finite_image_iff)
next
  case empty
  show ?case by simp
next
  case (insert t T)
  moreover from insert(2) have "PP t \<notin> PP ` T" by (simp add: PP_inject image_iff)
  ultimately show ?case by (simp add: map_PP_insort)
qed

lemma map_PP_pps_to_list: "map PP (pp_pm.punit.pps_to_list T) = punit.pps_to_list (PP ` T)"
  by (simp add: pp_pm.punit.pps_to_list_def punit.pps_to_list_def map_PP_sorted_list_of_set flip: rev_map)

lemma map_mapping_of_pps_to_list:
  "map mapping_of (punit.pps_to_list T) = pp_pm.punit.pps_to_list (mapping_of ` T)"
proof -
  have "map mapping_of (punit.pps_to_list T) = map mapping_of (punit.pps_to_list (PP ` mapping_of ` T))"
    by (simp add: image_comp)
  also have "\<dots> = map mapping_of (map PP (pp_pm.punit.pps_to_list (mapping_of ` T)))"
    by (simp only: map_PP_pps_to_list)
  also have "\<dots> = pp_pm.punit.pps_to_list (mapping_of ` T)" by simp
  finally show ?thesis .
qed

lemma keys_to_list_map_key_PP:
  "pp_pm.punit.keys_to_list (Poly_Mapping.map_key PP p) = map mapping_of (punit.keys_to_list p)"
  by (simp add: pp_pm.punit.keys_to_list_def punit.keys_to_list_def keys_map_key_PP map_mapping_of_pps_to_list)

lemma Keys_to_list_map_key_PP:
  "pp_pm.punit.Keys_to_list (map (Poly_Mapping.map_key PP) fs) = map mapping_of (punit.Keys_to_list fs)"
  by (simp add: punit.Keys_to_list_eq_pps_to_list pp_pm.punit.Keys_to_list_eq_pps_to_list
          map_mapping_of_pps_to_list Keys_def image_UN keys_map_key_PP)

lemma poly_deg_map_key_PP: "poly_deg (Poly_Mapping.map_key PP p) = poly_deg_pp p"
proof -
  {
    assume "p \<noteq> 0"
    hence "map deg_pp (punit.keys_to_list p) \<noteq> []"
      by (simp add: punit.keys_to_list_def punit.pps_to_list_def)
    hence "Max (deg_pp ` keys p) = max_list (map deg_pp (punit.keys_to_list p))"
      by (simp add: max_list_Max punit.set_keys_to_list)
  }
  thus ?thesis
    by (simp add: poly_deg_def poly_deg_pp_def keys_map_key_PP image_image flip: deg_pp.rep_eq)
qed

lemma deg_le_sect_pp_aux_1:
  assumes "t \<in> keys (deg_le_sect_pp_aux xs n)"
  shows "deg_pp t \<le> n" and "keys_pp t \<subseteq> set xs"
proof -
  from assms have "deg_pp t \<le> n \<and> keys_pp t \<subseteq> set xs"
  proof (induct n arbitrary: t)
    case 0
    thus ?case by (simp_all add: keys_pp.rep_eq zero_pp.rep_eq)
  next
    case (Suc n)
    define X where "X = set xs"
    define q where "q = deg_le_sect_pp_aux xs n"
    have 1: "s \<in> keys q \<Longrightarrow> deg_pp s \<le> n \<and> keys_pp s \<subseteq> X" for s unfolding q_def X_def by (fact Suc.hyps)
    note Suc.prems
    also have "keys (deg_le_sect_pp_aux xs (Suc n)) \<subseteq> keys q \<union>
                    keys (foldr (\<lambda>x. (+) (monom_mult_punit 1 (single_pp x 1) q)) xs 0)"
      (is "_ \<subseteq> _ \<union> keys (foldr ?r xs 0)") by (simp add: Let_def Poly_Mapping.keys_add flip: q_def)
    finally show ?case
    proof
      assume "t \<in> keys q"
      hence "deg_pp t \<le> n \<and> keys_pp t \<subseteq> set xs" unfolding q_def by (rule Suc.hyps)
      thus ?thesis by simp
    next
      assume "t \<in> keys (foldr ?r xs 0)"
      moreover have "set xs \<subseteq> X" by (simp add: X_def)
      ultimately have "deg_pp t \<le> Suc n \<and> keys_pp t \<subseteq> X"
      proof (induct xs arbitrary: t)
        case Nil
        thus ?case by simp
      next
        case (Cons x xs)
        from Cons.prems(2) have "x \<in> X" and "set xs \<subseteq> X" by simp_all
        note Cons.prems(1)
        also have "keys (foldr ?r (x # xs) 0) \<subseteq> keys (?r x 0) \<union> keys (foldr ?r xs 0)"
          by (simp add: Poly_Mapping.keys_add)
        finally show ?case
        proof
          assume "t \<in> keys (?r x 0)"
          also have "\<dots> = (+) (single_pp x 1) ` keys q"
            by (simp add: monom_mult_punit_def punit.keys_monom_mult)
          finally obtain s where "s \<in> keys q" and t: "t = single_pp x 1 + s" ..
          from this(1) have "deg_pp s \<le> n \<and> keys_pp s \<subseteq> X" by (rule 1)
          with \<open>x \<in> X\<close> show ?thesis
            by (simp add: t deg_pp_plus deg_pp_single keys_pp.rep_eq plus_pp.rep_eq
                keys_plus_ninv_comm_monoid_add single_pp.rep_eq)
        next
          assume "t \<in> keys (foldr ?r xs 0)"
          thus "deg_pp t \<le> Suc n \<and> keys_pp t \<subseteq> X" using \<open>set xs \<subseteq> X\<close> by (rule Cons.hyps)
        qed
      qed
      thus ?thesis by (simp only: X_def)
    qed
  qed
  thus "deg_pp t \<le> n" and "keys_pp t \<subseteq> set xs" by simp_all
qed

lemma deg_le_sect_pp_aux_2:
  assumes "deg_pp t \<le> n" and "keys_pp t \<subseteq> set xs"
  shows "t \<in> keys (deg_le_sect_pp_aux xs n)"
  using assms
proof (induct n arbitrary: t)
  case 0
  thus ?case by simp
next
  case (Suc n)
  have foldr: "foldr (\<lambda>x. (+) (f x)) ys 0 + y = foldr (\<lambda>x. (+) (f x)) ys y"
    for f ys and y::"'z::monoid_add" by (induct ys) (simp_all add: ac_simps)
  define q where "q = deg_le_sect_pp_aux xs n"
  from Suc.prems(1) have "deg_pp t \<le> n \<or> deg_pp t = Suc n" by auto
  thus ?case
  proof
    assume "deg_pp t \<le> n"
    hence "t \<in> keys q" unfolding q_def using Suc.prems(2) by (rule Suc.hyps)
    hence "0 < lookup q t" by (simp add: in_keys_iff)
    also have "\<dots> \<le> lookup (deg_le_sect_pp_aux xs (Suc n)) t"
      by (simp add: Let_def lookup_add flip: q_def)
    finally show ?thesis by (simp add: in_keys_iff)
  next
    assume eq: "deg_pp t = Suc n"
    hence "keys_pp t \<noteq> {}" by (auto simp: keys_pp.rep_eq deg_pp.rep_eq)
    then obtain x where "x \<in> keys_pp t" by blast
    with Suc.prems(2) have "x \<in> set xs" ..
    then obtain xs1 xs2 where xs: "xs = xs1 @ x # xs2" by (meson split_list)
    define s where "s = t - single_pp x 1"
    from \<open>x \<in> keys_pp t\<close> have "single_pp x 1 adds t"
      by (simp add: adds_pp_iff single_pp.rep_eq keys_pp.rep_eq adds_poly_mapping le_fun_def
          lookup_single when_def in_keys_iff)
    hence "s + single_pp x 1 = (t + single_pp x 1) - single_pp x 1"
      unfolding s_def by (rule minus_plus)
    hence t: "t = single_pp x 1 + s" by (simp add: add.commute)
    with eq have "deg_pp s \<le> n" by (simp add: deg_pp_plus deg_pp_single)
    moreover have "keys_pp s \<subseteq> set xs"
    proof (rule subset_trans)
      from Suc.prems(2) \<open>x \<in> set xs\<close> show "keys_pp t \<union> keys_pp (single_pp x (Suc 0)) \<subseteq> set xs"
        by (simp add: keys_pp.rep_eq single_pp.rep_eq)
    qed (simp add: s_def keys_pp.rep_eq minus_pp.rep_eq keys_diff)
    ultimately have "s \<in> keys q" unfolding q_def by (rule Suc.hyps)
    hence "t \<in> keys (monom_mult_punit 1 (single_pp x 1) q)"
      by (simp add: monom_mult_punit_def punit.keys_monom_mult t)
    hence "0 < lookup (monom_mult_punit 1 (single_pp x 1) q) t" by (simp add: in_keys_iff)
    also have "\<dots> \<le> lookup (q + (foldr (\<lambda>x. (+) (monom_mult_punit 1 (single_pp x 1) q)) xs1 0 +
                      (monom_mult_punit 1 (single_pp x 1) q +
                        foldr (\<lambda>x. (+) (monom_mult_punit 1 (single_pp x 1) q)) xs2 0))) t"
      by (simp add: lookup_add)
    also have "\<dots> = lookup (deg_le_sect_pp_aux xs (Suc n)) t"
      by (simp add: Let_def foldr flip: q_def, simp add: xs)
    finally show ?thesis by (simp add: in_keys_iff)
  qed
qed

lemma keys_deg_le_sect_pp_aux:
  "keys (deg_le_sect_pp_aux xs n) = {t. deg_pp t \<le> n \<and> keys_pp t \<subseteq> set xs}"
  by (auto dest: deg_le_sect_pp_aux_1 deg_le_sect_pp_aux_2)

lemma deg_le_sect_deg_le_sect_pp:
  "map PP (pp_pm.punit.pps_to_list (deg_le_sect (set xs) d)) = deg_le_sect_pp xs d"
proof -
  have "PP ` {t. deg_pm t \<le> d \<and> keys t \<subseteq> set xs} = PP ` {t. deg_pp (PP t) \<le> d \<and> keys_pp (PP t) \<subseteq> set xs}"
    by (simp only: keys_pp.abs_eq deg_pp.abs_eq)
  also have "\<dots> = {t. deg_pp t \<le> d \<and> keys_pp t \<subseteq> set xs}"
  proof (intro subset_antisym subsetI)
    fix t
    assume "t \<in> {t. deg_pp t \<le> d \<and> keys_pp t \<subseteq> set xs}"
    moreover have "t = PP (mapping_of t)" by (simp only: mapping_of_inverse)
    ultimately show "t \<in> PP ` {t. deg_pp (PP t) \<le> d \<and> keys_pp (PP t) \<subseteq> set xs}" by auto
  qed auto
  finally show ?thesis
    by (simp add: deg_le_sect_pp_def punit.keys_to_list_def keys_deg_le_sect_pp_aux deg_le_sect_alt
      PPs_def conj_commute map_PP_pps_to_list flip: Collect_conj_eq)
qed

lemma deg_shifts_deg_shifts_pp:
  "pp_pm.deg_shifts (set xs) d (map (Poly_Mapping.map_key PP) fs) =
        map (Poly_Mapping.map_key PP) (deg_shifts_pp xs d fs)"
  by (simp add: pp_pm.deg_shifts_def deg_shifts_pp_def map_concat comp_def poly_deg_map_key_PP
         map_key_PP_monom_mult_punit PP_inverse flip: deg_le_sect_deg_le_sect_pp monom_mult_punit_def)

lemma ideal_deg_shifts_pp: "ideal (set (deg_shifts_pp xs d fs)) = ideal (set fs)"
proof -
  have "ideal (set (deg_shifts_pp xs d fs)) =
        Poly_Mapping.map_key mapping_of ` Poly_Mapping.map_key PP ` ideal (set (deg_shifts_pp xs d fs))"
    by (simp add: image_comp)
  also have "\<dots> = Poly_Mapping.map_key mapping_of ` ideal
                    (set (map (Poly_Mapping.map_key PP) (deg_shifts_pp xs d fs)))"
    by (simp add: map_key_PP_ideal)
  also have "\<dots> = Poly_Mapping.map_key mapping_of ` ideal (Poly_Mapping.map_key PP ` set fs)"
    by (simp flip: deg_shifts_deg_shifts_pp)
  also have "\<dots> = Poly_Mapping.map_key mapping_of ` Poly_Mapping.map_key PP ` ideal (set fs)"
    by (simp only: map_key_PP_ideal)
  also have "\<dots> = ideal (set fs)" by (simp add: image_comp)
  finally show ?thesis .
qed

lemma set_indets_pp: "set (indets_pp p) = indets (Poly_Mapping.map_key PP p)"
  by (simp add: indets_pp_def indets_def keys_pp_to_list_def keys_pp.rep_eq punit.set_keys_to_list
        keys_map_key_PP)

lemma poly_to_row_map_key_PP:
  "poly_to_row (map pp.mapping_of xs) (Poly_Mapping.map_key PP p) = poly_to_row xs p"
  by (simp add: poly_to_row_def comp_def lookup_map_key_PP mapping_of_inverse)

lemma Macaulay_mat_map_key_PP:
  "pp_pm.punit.Macaulay_mat (map (Poly_Mapping.map_key PP) fs) = punit.Macaulay_mat fs"
  by (simp add: punit.Macaulay_mat_def pp_pm.punit.Macaulay_mat_def Keys_to_list_map_key_PP
          polys_to_mat_def comp_def poly_to_row_map_key_PP)

lemma row_to_poly_mapping_of:
  assumes "distinct ts" and "dim_vec r = length ts"
  shows "row_to_poly (map pp.mapping_of ts) r = Poly_Mapping.map_key PP (row_to_poly ts r)"
proof (rule poly_mapping_eqI, simp only: lookup_map_key_PP)
  fix t
  let ?ts = "map mapping_of ts"
  from inj_mapping_of subset_UNIV have "inj_on mapping_of (set ts)" by (rule inj_on_subset)
  with assms(1) have 1: "distinct ?ts" by (simp add: distinct_map)
  from assms(2) have 2: "dim_vec r = length ?ts" by simp
  show "lookup (row_to_poly ?ts r) t = lookup (row_to_poly ts r) (PP t)"
  proof (cases "t \<in> set ?ts")
    case True
    then obtain i where i1: "i < length ?ts" and t1: "t = ?ts ! i" by (metis in_set_conv_nth)
    hence i2: "i < length ts" and t2: "PP t = ts ! i" by (simp_all add: mapping_of_inverse)
    have "lookup (row_to_poly ?ts r) t = r $ i"
      unfolding t1 using 1 2 i1 by (rule punit.lookup_row_to_poly)
    moreover have "lookup (row_to_poly ts r) (PP t) = r $ i"
      unfolding t2 using assms i2 by (rule punit.lookup_row_to_poly)
    ultimately show ?thesis by simp
  next
    case False
    have "PP t \<notin> set ts"
    proof
      assume "PP t \<in> set ts"
      hence "mapping_of (PP t) \<in> mapping_of ` set ts" by (rule imageI)
      with False show False by (simp add: PP_inverse)
    qed
    with punit.keys_row_to_poly have "lookup (row_to_poly ts r) (PP t) = 0"
      by (metis in_keys_iff in_mono)
    moreover from False punit.keys_row_to_poly have "lookup (row_to_poly ?ts r) t = 0"
      by (metis in_keys_iff in_mono)
    ultimately show ?thesis by simp
  qed
qed

lemma mat_to_polys_mapping_of:
  assumes "distinct ts" and "dim_col m = length ts"
  shows "mat_to_polys (map pp.mapping_of ts) m = map (Poly_Mapping.map_key PP) (mat_to_polys ts m)"
proof -
  {
    fix r
    assume "r \<in> set (rows m)"
    then obtain i where "r = row m i" by (auto simp: rows_def)
    hence "dim_vec r = length ts" by (simp add: assms(2))
    with assms(1) have "row_to_poly (map pp.mapping_of ts) r = Poly_Mapping.map_key PP (row_to_poly ts r)"
      by (rule row_to_poly_mapping_of)
  }
  thus ?thesis using assms by (simp add: mat_to_polys_def)
qed

lemma map_key_PP_Macaulay_list:
  "map (Poly_Mapping.map_key PP) (punit.Macaulay_list fs) =
      pp_pm.punit.Macaulay_list (map (Poly_Mapping.map_key PP) fs)"
  by (simp add: punit.Macaulay_list_def pp_pm.punit.Macaulay_list_def Macaulay_mat_map_key_PP
          Keys_to_list_map_key_PP mat_to_polys_mapping_of filter_map comp_def
          punit.distinct_Keys_to_list punit.length_Keys_to_list)

lemma lpp_map_key_PP: "pp_pm.lpp (Poly_Mapping.map_key PP p) = mapping_of (lpp p)"
proof (cases "p = 0")
  case True
  thus ?thesis by (simp add: zero_pp.rep_eq)
next
  case False
  show ?thesis
  proof (rule pp_pm.punit.lt_eqI_keys)
    show "pp.mapping_of (lpp p) \<in> keys (Poly_Mapping.map_key PP p)" unfolding keys_map_key_PP
      by (intro imageI punit.lt_in_keys False)
  next
    fix s
    assume "s \<in> keys (Poly_Mapping.map_key PP p)"
    then obtain t where "t \<in> keys p" and s: "s = mapping_of t" unfolding keys_map_key_PP ..
    thus "ord (PP s) (PP (pp.mapping_of (lpp p)))" by (simp add: mapping_of_inverse punit.lt_max_keys)
  qed
qed

lemma is_GB_map_key_PP:
  "finite G \<Longrightarrow> pp_pm.punit.is_Groebner_basis (Poly_Mapping.map_key PP ` G) \<longleftrightarrow> punit.is_Groebner_basis G"
  by (simp add: punit.GB_alt_3_finite pp_pm.punit.GB_alt_3_finite lpp_map_key_PP adds_pp_iff
        flip: map_key_PP_ideal)

lemma thm_2_3_6_pp:
  assumes "pp_pm.is_GB_cofactor_bound (Poly_Mapping.map_key PP ` set fs) b"
  shows "punit.is_Groebner_basis (set (punit.Macaulay_list (deg_shifts_pp (Indets_pp fs) b fs)))"
proof -
  let ?fs = "map (Poly_Mapping.map_key PP) fs"
  from assms have "pp_pm.is_GB_cofactor_bound (set ?fs) b" by simp
  hence "pp_pm.punit.is_Groebner_basis
                (set (pp_pm.punit.Macaulay_list (pp_pm.deg_shifts (\<Union> (indets ` set ?fs)) b ?fs)))"
    by (rule pp_pm.thm_2_3_6_indets)
  also have "(\<Union> (indets ` set ?fs)) = set (Indets_pp fs)" by (simp add: Indets_pp_def set_indets_pp)
  finally show ?thesis
    by (simp add: deg_shifts_deg_shifts_pp map_key_PP_Macaulay_list flip: set_map is_GB_map_key_PP)
qed

lemma Dube_is_GB_cofactor_bound_pp:
  "pp_pm.is_GB_cofactor_bound (Poly_Mapping.map_key PP ` set fs)
            (Dube (Suc (length (Indets_pp fs))) (max_list (map poly_deg_pp fs)))"
proof (cases "fs = []")
  case True
  show ?thesis by (rule pp_pm.is_GB_cofactor_boundI_subset_zero) (simp add: True)
next
  case False
  let ?F = "Poly_Mapping.map_key PP ` set fs"
  have "pp_pm.is_GB_cofactor_bound ?F (Dube (Suc (card (\<Union> (indets ` ?F)))) (maxdeg ?F))"
    by (intro pp_pm.Dube_is_GB_cofactor_bound_indets finite_imageI finite_set)
  moreover have "card (\<Union> (indets ` ?F)) = length (Indets_pp fs)"
    by (simp add: Indets_pp_def length_remdups_card_conv set_indets_pp)
  moreover from False have "maxdeg ?F = max_list (map poly_deg_pp fs)"
    by (simp add: max_list_Max maxdeg_def image_image poly_deg_map_key_PP)
  ultimately show ?thesis by simp
qed

definition GB_Macaulay_Dube :: "(('x, nat) pp \<Rightarrow>\<^sub>0 'a) list \<Rightarrow> (('x, nat) pp \<Rightarrow>\<^sub>0 'a::field) list"
  where "GB_Macaulay_Dube fs = punit.Macaulay_list (deg_shifts_pp (Indets_pp fs)
                            (Dube (Suc (length (Indets_pp fs))) (max_list (map poly_deg_pp fs))) fs)"

lemma GB_Macaulay_Dube_is_GB: "punit.is_Groebner_basis (set (GB_Macaulay_Dube fs))"
  unfolding GB_Macaulay_Dube_def using Dube_is_GB_cofactor_bound_pp by (rule thm_2_3_6_pp)

lemma ideal_GB_Macaulay_Dube: "ideal (set (GB_Macaulay_Dube fs)) = ideal (set fs)"
  by (simp add: GB_Macaulay_Dube_def punit.pmdl_Macaulay_list[simplified] ideal_deg_shifts_pp)

end

global_interpretation punit': pp_powerprod "ord_pp_punit cmp_term" "ord_pp_strict_punit cmp_term"
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
  and "punit'.punit.keys_to_list = keys_to_list_punit cmp_term"
  for cmp_term :: "('a::nat, nat) pp nat_term_order"

  defines max_punit = punit'.ordered_powerprod_lin.max
  and max_list_punit = punit'.ordered_powerprod_lin.max_list
  and Keys_to_list_punit = punit'.punit.Keys_to_list
  and Macaulay_mat_punit = punit'.punit.Macaulay_mat
  and Macaulay_list_punit = punit'.punit.Macaulay_list
  and poly_deg_pp_punit = punit'.poly_deg_pp
  and deg_le_sect_pp_aux_punit = punit'.deg_le_sect_pp_aux
  and deg_le_sect_pp_punit = punit'.deg_le_sect_pp
  and deg_shifts_pp_punit = punit'.deg_shifts_pp
  and indets_pp_punit = punit'.indets_pp
  and Indets_pp_punit = punit'.Indets_pp
  and GB_Macaulay_Dube_punit = punit'.GB_Macaulay_Dube

  (* Only needed for auto-reduction: *)
  and find_adds_punit = punit'.punit.find_adds
  and trd_aux_punit = punit'.punit.trd_aux
  and trd_punit = punit'.punit.trd
  and comp_min_basis_punit = punit'.punit.comp_min_basis
  and comp_red_basis_aux_punit = punit'.punit.comp_red_basis_aux
  and comp_red_basis_punit = punit'.punit.comp_red_basis
  subgoal unfolding punit0.ord_pp_def punit0.ord_pp_strict_def ..
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
  subgoal by (simp only: keys_to_list_punit_def ord_pp_punit_alt) 
  done

subsection \<open>Computations\<close>

experiment begin interpretation trivariate\<^sub>0_rat .

lemma
  "comp_red_basis_punit DRLEX (GB_Macaulay_Dube_punit DRLEX [X * Y\<^sup>2 + 3 * X\<^sup>2 * Y, Y ^ 3 - X ^ 3]) =
    [X ^ 5, X ^ 3 * Y - C\<^sub>0 (1 / 9) * X ^ 4, Y ^ 3 - X ^ 3, X * Y\<^sup>2 + 3 * X\<^sup>2 * Y]"
  by eval

end

end (* theory *)
