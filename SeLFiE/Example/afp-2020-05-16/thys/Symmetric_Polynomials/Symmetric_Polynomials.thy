(*
  File:     Symmetric_Polynomials.thy
  Author:   Manuel Eberl (TU München)

  The definition of symmetric polynomials and the elementary symmetric polynomials.
  Proof of the fundamental theorem of symmetric polynomials and its corollaries.
*)
section \<open>Symmetric Polynomials\<close>
theory Symmetric_Polynomials
imports
  Vieta
  "Polynomials.More_MPoly_Type"
  "HOL-Library.Permutations"
begin

subsection \<open>Auxiliary facts\<close>

(*
  TODO: Many of these facts and definitions should be moved elsewhere, especially
  the ones on polynomials (leading monomial, mapping, insertion etc.)
*)

text \<open>
  An infinite set has infinitely many infinite subsets.
\<close>
lemma infinite_infinite_subsets:
  assumes "infinite A"
  shows   "infinite {X. X \<subseteq> A \<and> infinite X}"
proof -
  have "\<forall>k. \<exists>X. X \<subseteq> A \<and> infinite X \<and> card (A - X) = k" for k :: nat
  proof
    fix k :: nat obtain Y where "finite Y" "card Y = k" "Y \<subseteq> A"
      using infinite_arbitrarily_large[of A k] assms by auto
    moreover from this have "A - (A - Y) = Y" by auto
    ultimately show "\<exists>X. X \<subseteq> A \<and> infinite X \<and> card (A - X) = k"
      using assms by (intro exI[of _ "A - Y"]) auto
  qed
  from choice[OF this] obtain f
    where f: "\<And>k. f k \<subseteq> A \<and> infinite (f k) \<and> card (A - f k) = k" by blast
  have "k = l" if "f k = f l" for k l
  proof (rule ccontr)
    assume "k \<noteq> l"
    hence "card (A - f k) \<noteq> card (A - f l)"
      using f[of k] f[of l] by auto
    with \<open>f k = f l\<close> show False by simp
  qed
  hence "inj f" by (auto intro: injI)
  moreover have "range f \<subseteq> {X. X \<subseteq> A \<and> infinite X}"
    using f by auto
  ultimately show ?thesis
    by (subst infinite_iff_countable_subset) auto
qed

text \<open>
  An infinite set contains infinitely many finite subsets of any fixed nonzero cardinality.
\<close>
lemma infinite_card_subsets:
  assumes "infinite A" "k > 0"
  shows   "infinite {X. X \<subseteq> A \<and> finite X \<and> card X = k}"
proof -
  obtain B where B: "B \<subseteq> A" "finite B" "card B = k - 1"
    using infinite_arbitrarily_large[OF assms(1), of "k - 1"] by blast
  define f where "f = (\<lambda>x. insert x B)"
  have "f ` (A - B) \<subseteq> {X. X \<subseteq> A \<and> finite X \<and> card X = k}"
    using assms B by (auto simp: f_def)
  moreover have "inj_on f (A - B)"
    by (auto intro!: inj_onI simp: f_def)
  hence "infinite (f ` (A - B))"
    using assms B by (subst finite_image_iff) auto
  ultimately show ?thesis
    by (rule infinite_super)
qed

lemma comp_bij_eq_iff:
  assumes "bij f"
  shows   "g \<circ> f = h \<circ> f \<longleftrightarrow> g = h"
proof
  assume *: "g \<circ> f = h \<circ> f"
  show "g = h"
  proof
    fix x
    obtain y where [simp]: "x = f y" using bij_is_surj[OF assms] by auto
    have "(g \<circ> f) y = (h \<circ> f) y" by (simp only: *)
    thus "g x = h x" by simp
  qed
qed auto

lemma sum_list_replicate [simp]:
  "sum_list (replicate n x) = of_nat n * (x :: 'a :: semiring_1)"
  by (induction n) (auto simp: algebra_simps)

lemma ex_subset_of_card:
  assumes "finite A" "card A \<ge> k"
  shows   "\<exists>B. B \<subseteq> A \<and> card B = k"
  using assms
proof (induction arbitrary: k rule: finite_induct)
  case empty
  thus ?case by auto
next
  case (insert x A k)
  show ?case
  proof (cases "k = 0")
    case True
    thus ?thesis by (intro exI[of _ "{}"]) auto
  next
    case False
    from insert have "\<exists>B\<subseteq>A. card B = k - 1" by (intro insert.IH) auto
    then obtain B where B: "B \<subseteq> A" "card B = k - 1" by auto
    with insert have [simp]: "x \<notin> B" by auto
    have "insert x B \<subseteq> insert x A"
      using B insert by auto
    moreover have "card (insert x B) = k"
      using insert B finite_subset[of B A] False by (subst card_insert) auto
    ultimately show ?thesis by blast
  qed
qed

lemma length_sorted_list_of_set [simp]: "length (sorted_list_of_set A) = card A"
  using distinct_card[of "sorted_list_of_set A"] by (cases "finite A") simp_all

lemma upt_add_eq_append': "i \<le> j \<Longrightarrow> j \<le> k \<Longrightarrow> [i..<k] = [i..<j] @ [j..<k]"
  using upt_add_eq_append[of i j "k - j"] by simp


subsection \<open>Subrings and ring homomorphisms\<close>

locale ring_closed =
  fixes A :: "'a :: comm_ring_1 set"
  assumes zero_closed [simp]: "0 \<in> A"
  assumes one_closed [simp]: "1 \<in> A"
  assumes add_closed [simp]: "x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> (x + y) \<in> A"
  assumes mult_closed [simp]: "x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> (x * y) \<in> A"
  assumes uminus_closed [simp]: "x \<in> A \<Longrightarrow> -x \<in> A"
begin

lemma minus_closed [simp]: "x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> x - y \<in> A"
  using add_closed[of x "-y"] uminus_closed[of y] by auto

lemma sum_closed [intro]: "(\<And>x. x \<in> X \<Longrightarrow> f x \<in> A) \<Longrightarrow> sum f X \<in> A"
  by (induction X rule: infinite_finite_induct) auto

lemma power_closed [intro]: "x \<in> A \<Longrightarrow> x ^ n \<in> A"
  by (induction n) auto

lemma Sum_any_closed [intro]: "(\<And>x. f x \<in> A) \<Longrightarrow> Sum_any f \<in> A"
  unfolding Sum_any.expand_set by (rule sum_closed)

lemma prod_closed [intro]: "(\<And>x. x \<in> X \<Longrightarrow> f x \<in> A) \<Longrightarrow> prod f X \<in> A"
  by (induction X rule: infinite_finite_induct) auto

lemma Prod_any_closed [intro]: "(\<And>x. f x \<in> A) \<Longrightarrow> Prod_any f \<in> A"
  unfolding Prod_any.expand_set by (rule prod_closed)

lemma prod_fun_closed [intro]: "(\<And>x. f x \<in> A) \<Longrightarrow> (\<And>x. g x \<in> A) \<Longrightarrow> prod_fun f g x \<in> A"
  by (auto simp: prod_fun_def when_def intro!: Sum_any_closed mult_closed)

lemma of_nat_closed [simp, intro]: "of_nat n \<in> A"
  by (induction n) auto

lemma of_int_closed [simp, intro]: "of_int n \<in> A"
  by (induction n) auto

end

locale ring_homomorphism =
  fixes f :: "'a :: comm_ring_1 \<Rightarrow> 'b :: comm_ring_1"
  assumes add[simp]: "f (x + y) = f x + f y"
  assumes uminus[simp]: "f (-x) = -f x"
  assumes mult[simp]: "f (x * y) = f x * f y"
  assumes zero[simp]: "f 0 = 0"
  assumes one [simp]: "f 1 = 1"
begin

lemma diff [simp]: "f (x - y) = f x - f y"
  using add[of x "-y"] by (simp del: add)

lemma power [simp]: "f (x ^ n) = f x ^ n"
  by (induction n) auto

lemma sum [simp]: "f (sum g A) = (\<Sum>x\<in>A. f (g x))"
  by (induction A rule: infinite_finite_induct) auto

lemma prod [simp]: "f (prod g A) = (\<Prod>x\<in>A. f (g x))"
  by (induction A rule: infinite_finite_induct) auto

end

lemma ring_homomorphism_id [intro]: "ring_homomorphism id"
  by standard auto

lemma ring_homomorphism_id' [intro]: "ring_homomorphism (\<lambda>x. x)"
  by standard auto

lemma ring_homomorphism_of_int [intro]: "ring_homomorphism of_int"
  by standard auto


subsection \<open>Various facts about multivariate polynomials\<close>

lemma poly_mapping_nat_ge_0 [simp]: "(m :: nat \<Rightarrow>\<^sub>0 nat) \<ge> 0"
proof (cases "m = 0")
  case False
  hence "Poly_Mapping.lookup m \<noteq> Poly_Mapping.lookup 0" by transfer auto
  hence "\<exists>k. Poly_Mapping.lookup m k \<noteq> 0" by (auto simp: fun_eq_iff)
  from LeastI_ex[OF this] Least_le[of "\<lambda>k. Poly_Mapping.lookup m k \<noteq> 0"] show ?thesis
    by (force simp: less_eq_poly_mapping_def less_fun_def)
qed auto

lemma poly_mapping_nat_le_0 [simp]: "(m :: nat \<Rightarrow>\<^sub>0 nat) \<le> 0 \<longleftrightarrow> m = 0"
  unfolding less_eq_poly_mapping_def poly_mapping_eq_iff less_fun_def by auto

lemma of_nat_diff_poly_mapping_nat:
  assumes "m \<ge> n"
  shows   "of_nat (m - n) = (of_nat m - of_nat n :: 'a :: monoid_add \<Rightarrow>\<^sub>0 nat)"
  by (auto intro!: poly_mapping_eqI simp: lookup_of_nat lookup_minus when_def)

lemma mpoly_coeff_transfer [transfer_rule]:
  "rel_fun cr_mpoly (=) poly_mapping.lookup MPoly_Type.coeff"
  unfolding MPoly_Type.coeff_def by transfer_prover

lemma mapping_of_sum: "(\<Sum>x\<in>A. mapping_of (f x)) = mapping_of (sum f A)"
  by (induction A rule: infinite_finite_induct) (auto simp: plus_mpoly.rep_eq zero_mpoly.rep_eq)

lemma mapping_of_eq_0_iff [simp]: "mapping_of p = 0 \<longleftrightarrow> p = 0"
  by transfer auto

lemma Sum_any_mapping_of: "Sum_any (\<lambda>x. mapping_of (f x)) = mapping_of (Sum_any f)"
  by (simp add: Sum_any.expand_set mapping_of_sum)

lemma Sum_any_parametric_cr_mpoly [transfer_rule]:
  "(rel_fun (rel_fun (=) cr_mpoly) cr_mpoly) Sum_any Sum_any"
  by (auto simp: rel_fun_def cr_mpoly_def Sum_any_mapping_of)

lemma lookup_mult_of_nat [simp]: "lookup (of_nat n * m) k = n * lookup m k"
proof -
  have "of_nat n * m = (\<Sum>i<n. m)" by simp
  also have "lookup \<dots> k = (\<Sum>i<n. lookup m k)"
    by (simp only: lookup_sum)
  also have "\<dots> = n * lookup m k"
    by simp
  finally show ?thesis .
qed

lemma mpoly_eqI:
  assumes "\<And>mon. MPoly_Type.coeff p mon = MPoly_Type.coeff q mon"
  shows   "p = q"
  using assms by (transfer, transfer) (auto simp: fun_eq_iff)

lemma coeff_mpoly_times:
  "MPoly_Type.coeff (p * q) mon = prod_fun (MPoly_Type.coeff p) (MPoly_Type.coeff q) mon"
  by (transfer', transfer') auto

lemma (in ring_closed) coeff_mult_closed [intro]:
  "(\<And>x. coeff p x \<in> A) \<Longrightarrow> (\<And>x. coeff q x \<in> A) \<Longrightarrow> coeff (p * q) x \<in> A"
  by (auto simp: coeff_mpoly_times prod_fun_closed)

lemma coeff_notin_vars:
  assumes "\<not>(keys m \<subseteq> vars p)"
  shows   "coeff p m = 0"
  using assms unfolding vars_def by transfer' (auto simp: in_keys_iff)

lemma finite_coeff_support [intro]: "finite {m. coeff p m \<noteq> 0}"
  by transfer simp

lemma insertion_altdef:
  "insertion f p = Sum_any (\<lambda>m. coeff p m * Prod_any (\<lambda>i. f i ^ lookup m i))"
  by (transfer', transfer') (simp add: insertion_fun_def)

lemma mpoly_coeff_uminus [simp]: "coeff (-p) m = -coeff p m"
  by transfer auto

lemma Sum_any_uminus: "Sum_any (\<lambda>x. -f x :: 'a :: ab_group_add) = -Sum_any f"
  by (simp add: Sum_any.expand_set sum_negf)

lemma insertion_uminus [simp]: "insertion f (-p :: 'a :: comm_ring_1 mpoly) = -insertion f p"
  by (simp add: insertion_altdef Sum_any_uminus)

lemma Sum_any_lookup: "finite {x. g x \<noteq> 0} \<Longrightarrow> Sum_any (\<lambda>x. lookup (g x) y) = lookup (Sum_any g) y"
  by (auto simp: Sum_any.expand_set lookup_sum intro!: sum.mono_neutral_left)

lemma Sum_any_diff:
  assumes "finite {x. f x \<noteq> 0}"
  assumes "finite {x. g x \<noteq> 0}"
  shows   "Sum_any (\<lambda>x. f x - g x :: 'a :: ab_group_add) = Sum_any f - Sum_any g"
proof -
  have "{x. f x - g x \<noteq> 0} \<subseteq> {x. f x \<noteq> 0} \<union> {x. g x \<noteq> 0}" by auto
  moreover have "finite ({x. f x \<noteq> 0} \<union> {x. g x \<noteq> 0})"
    by (subst finite_Un) (insert assms, auto)
  ultimately have "finite {x. f x - g x \<noteq> 0}"
    by (rule finite_subset)
  with assms show ?thesis
    by (simp add: algebra_simps Sum_any.distrib [symmetric])
qed

lemma insertion_diff:
  "insertion f (p - q :: 'a :: comm_ring_1 mpoly) = insertion f p - insertion f q"
proof (transfer, transfer)
  fix f :: "nat \<Rightarrow> 'a" and p q :: "(nat \<Rightarrow>\<^sub>0 nat) \<Rightarrow> 'a"
  assume fin: "finite {x. p x \<noteq> 0}" "finite {x. q x \<noteq> 0}"
  have "insertion_fun f (\<lambda>x. p x - q x) =
          (\<Sum>m. p m * (\<Prod>v. f v ^ lookup m v) - q m * (\<Prod>v. f v ^ lookup m v))"
    by (simp add: insertion_fun_def algebra_simps Sum_any_diff)
  also have "\<dots> = (\<Sum>m. p m * (\<Prod>v. f v ^ lookup m v)) - (\<Sum>m. q m * (\<Prod>v. f v ^ lookup m v))"
    by (subst Sum_any_diff) (auto intro: finite_subset[OF _ fin(1)] finite_subset[OF _ fin(2)])
  also have "\<dots> = insertion_fun f p - insertion_fun f q"
    by (simp add: insertion_fun_def)
  finally show "insertion_fun f (\<lambda>x. p x - q x) = \<dots>" .
qed

lemma insertion_power: "insertion f (p ^ n) = insertion f p ^ n"
  by (induction n) (simp_all add: insertion_mult)

lemma insertion_sum: "insertion f (sum g A) = (\<Sum>x\<in>A. insertion f (g x))"
  by (induction A rule: infinite_finite_induct) (auto simp: insertion_add)

lemma insertion_prod: "insertion f (prod g A) = (\<Prod>x\<in>A. insertion f (g x))"
  by (induction A rule: infinite_finite_induct) (auto simp: insertion_mult)

lemma coeff_Var: "coeff (Var i) m = (1 when m = Poly_Mapping.single i 1)"
  by transfer' (auto simp: Var\<^sub>0_def lookup_single when_def)

lemma vars_Var: "vars (Var i :: 'a :: {one,zero} mpoly) = (if (0::'a) = 1 then {} else {i})"
  unfolding vars_def by (auto simp: Var.rep_eq Var\<^sub>0_def)

lemma insertion_Var [simp]: "insertion f (Var i) = f i"
proof -
  have "insertion f (Var i) = (\<Sum>m. (1 when m = Poly_Mapping.single i 1) *
                                       (\<Prod>i. f i ^ lookup m i))"
    by (simp add: insertion_altdef coeff_Var)
  also have "\<dots> = (\<Prod>j. f j ^ lookup (Poly_Mapping.single i 1) j)"
    by (subst Sum_any.expand_superset[of "{Poly_Mapping.single i 1}"]) (auto simp: when_def)
  also have "\<dots> = f i"
    by (subst Prod_any.expand_superset[of "{i}"]) (auto simp: when_def lookup_single)
  finally show ?thesis .
qed

lemma insertion_Sum_any:
  assumes "finite {x. g x \<noteq> 0}"
  shows   "insertion f (Sum_any g) = Sum_any (\<lambda>x. insertion f (g x))"
  unfolding Sum_any.expand_set insertion_sum
  by (intro sum.mono_neutral_right) (auto intro!: finite_subset[OF _ assms])

lemma keys_diff_subset:
  "keys (f - g) \<subseteq> keys f \<union> keys g"
  by transfer auto

lemma keys_empty_iff [simp]: "keys p = {} \<longleftrightarrow> p = 0"
  by transfer auto

lemma mpoly_coeff_0 [simp]: "MPoly_Type.coeff 0 m = 0"
  by transfer auto

lemma lookup_1: "lookup 1 m = (if m = 0 then 1 else 0)"
  by transfer (simp add: when_def)

lemma mpoly_coeff_1: "MPoly_Type.coeff 1 m = (if m = 0 then 1 else 0)"
  by (simp add: MPoly_Type.coeff_def one_mpoly.rep_eq lookup_1)

lemma lookup_Const\<^sub>0: "lookup (Const\<^sub>0 c) m = (if m = 0 then c else 0)"
  unfolding Const\<^sub>0_def by (simp add: lookup_single when_def)

lemma mpoly_coeff_Const: "MPoly_Type.coeff (Const c) m = (if m = 0 then c else 0)"
  by (simp add: MPoly_Type.coeff_def Const.rep_eq lookup_Const\<^sub>0)

lemma coeff_smult [simp]: "coeff (smult c p) m = (c :: 'a :: mult_zero) * coeff p m"
  by transfer (auto simp: map_lookup)

lemma in_keys_mapI: "x \<in> keys m \<Longrightarrow> f (lookup m x) \<noteq> 0 \<Longrightarrow> x \<in> keys (Poly_Mapping.map f m)"
  by transfer auto

lemma keys_uminus [simp]: "keys (-m) = keys m"
  by transfer auto

lemma vars_uminus [simp]: "vars (-p) = vars p"
  unfolding vars_def by transfer' auto

lemma vars_smult: "vars (smult c p) \<subseteq> vars p"
  unfolding vars_def by (transfer', transfer') auto

lemma vars_0 [simp]: "vars 0 = {}"
  unfolding vars_def by transfer' simp

lemma vars_1 [simp]: "vars 1 = {}"
  unfolding vars_def by transfer' simp

lemma vars_sum: "vars (sum f A) \<subseteq> (\<Union>x\<in>A. vars (f x))"
  using vars_add by (induction A rule: infinite_finite_induct) auto

lemma vars_prod: "vars (prod f A) \<subseteq> (\<Union>x\<in>A. vars (f x))"
  using vars_mult by (induction A rule: infinite_finite_induct) auto

lemma vars_Sum_any: "vars (Sum_any h) \<subseteq> (\<Union>i. vars (h i))"
  unfolding Sum_any.expand_set by (intro order.trans[OF vars_sum]) auto

lemma vars_Prod_any: "vars (Prod_any h) \<subseteq> (\<Union>i. vars (h i))"
  unfolding Prod_any.expand_set by (intro order.trans[OF vars_prod]) auto

lemma vars_power: "vars (p ^ n) \<subseteq> vars p"
  using vars_mult by (induction n) auto

lemma vars_diff: "vars (p1 - p2) \<subseteq> vars p1 \<union> vars p2"
  unfolding vars_def
proof transfer'
  fix p1 p2 :: "(nat \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a"
  show "\<Union> (keys ` keys (p1 - p2)) \<subseteq> \<Union>(keys ` (keys p1)) \<union> \<Union>(keys ` (keys p2))"
    using keys_diff_subset[of p1 p2] by (auto simp flip: not_in_keys_iff_lookup_eq_zero)
qed

lemma insertion_smult [simp]: "insertion f (smult c p) = c * insertion f p"
  unfolding insertion_altdef
  by (subst Sum_any_right_distrib)
     (auto intro: finite_subset[OF _ finite_coeff_support[of p]] simp: mult.assoc)

lemma coeff_add [simp]: "coeff (p + q) m = coeff p m + coeff q m"
  by transfer' (simp add: lookup_add)

lemma coeff_diff [simp]: "coeff (p - q) m = coeff p m - coeff q m"
  by transfer' (simp add: lookup_minus)

lemma insertion_monom [simp]:
  "insertion f (monom m c) = c * Prod_any (\<lambda>x. f x ^ lookup m x)"
proof -
  have "insertion f (monom m c) =
          (\<Sum>m'. (c when m = m') * (\<Prod>v. f v ^ lookup m' v))"
    by (simp add: insertion_def insertion_aux_def insertion_fun_def lookup_single)
  also have "\<dots> = c * (\<Prod>v. f v ^ lookup m v)"
    by (subst Sum_any.expand_superset[of "{m}"]) (auto simp: when_def)
  finally show ?thesis .
qed

lemma insertion_aux_Const\<^sub>0 [simp]: "insertion_aux f (Const\<^sub>0 c) = c"
proof -
  have "insertion_aux f (Const\<^sub>0 c) = (\<Sum>m. (c when m = 0) * (\<Prod>v. f v ^ lookup m v))"
    by (simp add: Const\<^sub>0_def insertion_aux_def insertion_fun_def lookup_single)
  also have "\<dots> = (\<Sum>m\<in>{0}. (c when m = 0) * (\<Prod>v. f v ^ lookup m v))"
    by (intro Sum_any.expand_superset) (auto simp: when_def)
  also have "\<dots> = c" by simp
  finally show ?thesis .
qed

lemma insertion_Const [simp]: "insertion f (Const c) = c"
  by (simp add: insertion_def Const.rep_eq)

lemma coeffs_0 [simp]: "coeffs 0 = {}"
  by transfer auto

lemma coeffs_1 [simp]: "coeffs 1 = {1}"
  by transfer auto

lemma coeffs_Const: "coeffs (Const c) = (if c = 0 then {} else {c})"
  unfolding Const_def Const\<^sub>0_def by transfer' auto

lemma coeffs_subset: "coeffs (Const c) \<subseteq> {c}"
  by (auto simp: coeffs_Const)

lemma keys_Const\<^sub>0: "keys (Const\<^sub>0 c) = (if c = 0 then {} else {0})"
  unfolding Const\<^sub>0_def by transfer' auto

lemma vars_Const [simp]: "vars (Const c) = {}"
  unfolding vars_def by transfer' (auto simp: keys_Const\<^sub>0)

lemma prod_fun_compose_bij:
  assumes "bij f" and f: "\<And>x y. f (x + y) = f x + f y"
  shows   "prod_fun m1 m2 (f x) = prod_fun (m1 \<circ> f) (m2 \<circ> f) x"
proof -
  have [simp]: "f x = f y \<longleftrightarrow> x = y" for x y
    using \<open>bij f\<close> by (auto dest!: bij_is_inj inj_onD)
  have "prod_fun (m1 \<circ> f) (m2 \<circ> f) x =
          Sum_any ((\<lambda>l. m1 l * Sum_any ((\<lambda>q. m2 q when f x = l + q) \<circ> f)) \<circ> f)"
    by (simp add: prod_fun_def f(1) [symmetric] o_def)
  also have "\<dots> = Sum_any ((\<lambda>l. m1 l * Sum_any ((\<lambda>q. m2 q when f x = l + q))))"
    by (simp only: Sum_any.reindex_cong[OF assms(1) refl, symmetric])
  also have "\<dots> = prod_fun m1 m2 (f x)"
    by (simp add: prod_fun_def)
  finally show ?thesis ..
qed

lemma add_nat_poly_mapping_zero_iff [simp]:
  "(a + b :: 'a \<Rightarrow>\<^sub>0 nat) = 0 \<longleftrightarrow> a = 0 \<and> b = 0"
  by transfer (auto simp: fun_eq_iff)

lemma prod_fun_nat_0:
  fixes f g :: "('a \<Rightarrow>\<^sub>0 nat) \<Rightarrow> 'b::semiring_0"
  shows   "prod_fun f g 0 = f 0 * g 0"
proof -
  have "prod_fun f g 0 = (\<Sum>l. f l * (\<Sum>q. g q when 0 = l + q))"
    unfolding prod_fun_def ..
  also have "(\<lambda>l. \<Sum>q. g q when 0 = l + q) = (\<lambda>l. \<Sum>q\<in>{0}. g q when 0 = l + q)"
    by (intro ext Sum_any.expand_superset) (auto simp: when_def)
  also have "(\<Sum>l. f l * \<dots> l) = (\<Sum>l\<in>{0}. f l * \<dots> l)"
    by (intro ext Sum_any.expand_superset) (auto simp: when_def)
  finally show ?thesis by simp
qed

lemma mpoly_coeff_times_0: "coeff (p * q) 0 = coeff p 0 * coeff q 0"
  by (simp add: coeff_mpoly_times prod_fun_nat_0)

lemma mpoly_coeff_prod_0: "coeff (\<Prod>x\<in>A. f x) 0 = (\<Prod>x\<in>A. coeff (f x) 0)"
  by (induction A rule: infinite_finite_induct) (auto simp: mpoly_coeff_times_0 mpoly_coeff_1)

lemma mpoly_coeff_power_0: "coeff (p ^ n) 0 = coeff p 0 ^ n"
  by (induction n) (auto simp: mpoly_coeff_times_0 mpoly_coeff_1)

lemma prod_fun_max:
  fixes f g :: "'a::{linorder, ordered_cancel_comm_monoid_add} \<Rightarrow> 'b::semiring_0"
  assumes zero: "\<And>m. m > a \<Longrightarrow> f m = 0" "\<And>m. m > b \<Longrightarrow> g m = 0"
  assumes fin: "finite {m. f m \<noteq> 0}" "finite {m. g m \<noteq> 0}"
  shows   "prod_fun f g (a + b) = f a * g b"
proof -
  note fin' = finite_subset[OF _ fin(1)] finite_subset[OF _ fin(2)]
  have "prod_fun f g (a + b) = (\<Sum>l. f l * (\<Sum>q. g q when a + b = l + q))"
    by (simp add: prod_fun_def Sum_any_right_distrib)
  also have "\<dots> = (\<Sum>l. \<Sum>q. f l * g q when a + b = l + q)"
    by (subst Sum_any_right_distrib) (auto intro!: Sum_any.cong fin'(2) simp: when_def)
  also {
    fix l q assume lq: "a + b = l + q" "(a, b) \<noteq> (l, q)" and nz: "f l * g q \<noteq> 0"
    from nz and zero have "l \<le> a" "q \<le> b" by (auto intro: leI)
    moreover from this and lq(2) have "l < a \<or> q < b" by auto
    ultimately have "l + q < a + b"
      by (auto intro: add_less_le_mono add_le_less_mono)
    with lq(1) have False by simp
  }
  hence "(\<Sum>l. \<Sum>q. f l * g q when a + b = l + q) = (\<Sum>l. \<Sum>q. f l * g q when (a, b) = (l, q))"
    by (intro Sum_any.cong refl) (auto simp: when_def)
  also have "\<dots> = (\<Sum>(l,q). f l * g q when (a, b) = (l, q))"
    by (intro Sum_any.cartesian_product[of "{(a, b)}"]) auto
  also have "\<dots> = (\<Sum>(l,q)\<in>{(a,b)}. f l * g q when (a, b) = (l, q))"
    by (intro Sum_any.expand_superset) auto
  also have "\<dots> = f a * g b" by simp
  finally show ?thesis .
qed

lemma prod_fun_gt_max_eq_zero:
  fixes f g :: "'a::{linorder, ordered_cancel_comm_monoid_add} \<Rightarrow> 'b::semiring_0"
  assumes "m > a + b"
  assumes zero: "\<And>m. m > a \<Longrightarrow> f m = 0" "\<And>m. m > b \<Longrightarrow> g m = 0"
  assumes fin: "finite {m. f m \<noteq> 0}" "finite {m. g m \<noteq> 0}"
  shows   "prod_fun f g m = 0"
proof -
  note fin' = finite_subset[OF _ fin(1)] finite_subset[OF _ fin(2)]
  have "prod_fun f g m = (\<Sum>l. f l * (\<Sum>q. g q when m = l + q))"
    by (simp add: prod_fun_def Sum_any_right_distrib)
  also have "\<dots> = (\<Sum>l. \<Sum>q. f l * g q when m = l + q)"
    by (subst Sum_any_right_distrib) (auto intro!: Sum_any.cong fin'(2) simp: when_def)
  also {
    fix l q assume lq: "m = l + q" and nz: "f l * g q \<noteq> 0"
    from nz and zero have "l \<le> a" "q \<le> b" by (auto intro: leI)
    hence "l + q \<le> a + b" by (intro add_mono)
    also have "\<dots> < m" by fact
    finally have "l + q < m" .
  }
  hence "(\<Sum>l. \<Sum>q. f l * g q when m = l + q) = (\<Sum>l. \<Sum>q. f l * g q when False)"
    by (intro Sum_any.cong refl) (auto simp: when_def)
  also have "\<dots> = 0" by simp
  finally show ?thesis .
qed


subsection \<open>Restricting a monomial to a subset of variables\<close>

lift_definition restrictpm :: "'a set \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b :: zero) \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b)" is
  "\<lambda>A f x. if x \<in> A then f x else 0"
  by (erule finite_subset[rotated]) auto

lemma lookup_restrictpm: "lookup (restrictpm A m) x = (if x \<in> A then lookup m x else 0)"
  by transfer auto

lemma lookup_restrictpm_in [simp]: "x \<in> A \<Longrightarrow> lookup (restrictpm A m) x = lookup m x"
  and lookup_restrict_pm_not_in [simp]: "x \<notin> A \<Longrightarrow> lookup (restrictpm A m) x = 0"
  by (simp_all add: lookup_restrictpm)

lemma keys_restrictpm [simp]: "keys (restrictpm A m) = keys m \<inter> A"
  by transfer auto

lemma restrictpm_add: "restrictpm X (m1 + m2) = restrictpm X m1 + restrictpm X m2"
  by transfer auto

lemma restrictpm_id [simp]: "keys m \<subseteq> X \<Longrightarrow> restrictpm X m = m"
  by transfer (auto simp: fun_eq_iff)

lemma restrictpm_orthogonal [simp]: "keys m \<subseteq> -X \<Longrightarrow> restrictpm X m = 0"
  by transfer (auto simp: fun_eq_iff)

lemma restrictpm_add_disjoint:
  "X \<inter> Y = {} \<Longrightarrow> restrictpm X m + restrictpm Y m = restrictpm (X \<union> Y) m"
  by transfer (auto simp: fun_eq_iff)

lemma restrictpm_add_complements:
  "restrictpm X m + restrictpm (-X) m = m" "restrictpm (-X) m + restrictpm X m = m"
   by (subst restrictpm_add_disjoint; force)+



subsection \<open>Mapping over a polynomial\<close>

lift_definition map_mpoly :: "('a :: zero \<Rightarrow> 'b :: zero) \<Rightarrow> 'a mpoly \<Rightarrow> 'b mpoly" is
  "\<lambda>(f :: 'a \<Rightarrow> 'b) (p :: (nat \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a). Poly_Mapping.map f p" .

lift_definition mapm_mpoly :: "((nat \<Rightarrow>\<^sub>0 nat) \<Rightarrow> 'a :: zero \<Rightarrow> 'b :: zero) \<Rightarrow> 'a mpoly \<Rightarrow> 'b mpoly" is
  "\<lambda>(f :: (nat \<Rightarrow>\<^sub>0 nat) \<Rightarrow> 'a \<Rightarrow> 'b) (p :: (nat \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a).
     Poly_Mapping.mapp f p" .

lemma poly_mapping_map_conv_mapp: "Poly_Mapping.map f = Poly_Mapping.mapp (\<lambda>_. f)"
  by (auto simp: Poly_Mapping.mapp_def Poly_Mapping.map_def map_fun_def
                 o_def fun_eq_iff when_def in_keys_iff cong: if_cong)

lemma map_mpoly_conv_mapm_mpoly: "map_mpoly f = mapm_mpoly (\<lambda>_. f)"
  by transfer' (auto simp: poly_mapping_map_conv_mapp)

lemma map_mpoly_comp: "f 0 = 0 \<Longrightarrow> map_mpoly f (map_mpoly g p) = map_mpoly (f \<circ> g) p"
  by (transfer', transfer') (auto simp: when_def fun_eq_iff)

lemma mapp_mapp:
  "(\<And>x. f x 0 = 0) \<Longrightarrow> Poly_Mapping.mapp f (Poly_Mapping.mapp g m) =
                          Poly_Mapping.mapp (\<lambda>x y. f x (g x y)) m"
  by transfer' (auto simp: fun_eq_iff lookup_mapp in_keys_iff)

lemma mapm_mpoly_comp:
  "(\<And>x. f x 0 = 0) \<Longrightarrow> mapm_mpoly f (mapm_mpoly g p) = mapm_mpoly (\<lambda>m c. f m (g m c)) p"
  by transfer' (simp add: mapp_mapp)

lemma coeff_map_mpoly:
  "coeff (map_mpoly f p) m = (if coeff p m = 0 then 0 else f (coeff p m))"
  by (transfer, transfer) auto

lemma coeff_map_mpoly' [simp]: "f 0 = 0 \<Longrightarrow> coeff (map_mpoly f p) m = f (coeff p m)"
  by (subst coeff_map_mpoly) auto

lemma coeff_mapm_mpoly: "coeff (mapm_mpoly f p) m = (if coeff p m = 0 then 0 else f m (coeff p m))"
  by (transfer, transfer') (auto simp: in_keys_iff)

lemma coeff_mapm_mpoly' [simp]: "(\<And>m. f m 0 = 0) \<Longrightarrow> coeff (mapm_mpoly f p) m = f m (coeff p m)"
  by (subst coeff_mapm_mpoly) auto

lemma vars_map_mpoly_subset: "vars (map_mpoly f p) \<subseteq> vars p"
  unfolding vars_def by (transfer', transfer') (auto simp: map_mpoly.rep_eq)

lemma coeff_sum [simp]: "coeff (sum f A) m = (\<Sum>x\<in>A. coeff (f x) m)"
  by (induction A rule: infinite_finite_induct) auto

lemma coeff_Sum_any: "finite {x. f x \<noteq> 0} \<Longrightarrow> coeff (Sum_any f) m = Sum_any (\<lambda>x. coeff (f x) m)"
  by (auto simp add: Sum_any.expand_set intro!: sum.mono_neutral_right)

lemma Sum_any_zeroI: "(\<And>x. f x = 0) \<Longrightarrow> Sum_any f = 0"
  by (auto simp: Sum_any.expand_set)

lemma insertion_Prod_any:
  "finite {x. g x \<noteq> 1} \<Longrightarrow> insertion f (Prod_any g) = Prod_any (\<lambda>x. insertion f (g x))"
  by (auto simp: Prod_any.expand_set insertion_prod intro!: prod.mono_neutral_right)

lemma insertion_insertion:
  "insertion g (insertion k p) =
     insertion (\<lambda>x. insertion g (k x)) (map_mpoly (insertion g) p)" (is "?lhs = ?rhs")
proof -
  have "insertion g (insertion k p) =
          (\<Sum>x. insertion g (coeff p x) * insertion g (\<Prod>i. k i ^ lookup x i))"
    unfolding insertion_altdef[of k p]
    by (subst insertion_Sum_any)
       (auto intro: finite_subset[OF _ finite_coeff_support[of p]] simp: insertion_mult)
  also have "\<dots> = (\<Sum>x. insertion g (coeff p x) * (\<Prod>i. insertion g (k i) ^ lookup x i))"
  proof (intro Sum_any.cong)
    fix x show "insertion g (coeff p x) * insertion g (\<Prod>i. k i ^ lookup x i) =
                  insertion g (coeff p x) * (\<Prod>i. insertion g (k i) ^ lookup x i)"
      by (subst insertion_Prod_any)
         (auto simp: insertion_power intro!: finite_subset[OF _ finite_lookup[of x]] Nat.gr0I)
  qed
  also have "\<dots> = insertion (\<lambda>x. insertion g (k x)) (map_mpoly (insertion g) p)"
    unfolding insertion_altdef[of _ "map_mpoly f p" for f] by auto
  finally show ?thesis .
qed

lemma insertion_substitute_linear:
  "insertion (\<lambda>i. c i * f i) p =
     insertion f (mapm_mpoly (\<lambda>m d. Prod_any (\<lambda>i. c i ^ lookup m i) * d) p)"
  unfolding insertion_altdef
proof (intro Sum_any.cong, goal_cases)
  case (1 m)
  have "coeff (mapm_mpoly (\<lambda>m. (*) (\<Prod>i. c i ^ lookup m i)) p) m * (\<Prod>i. f i ^ lookup m i) =
          MPoly_Type.coeff p m * ((\<Prod>i. c i ^ lookup m i) * (\<Prod>i. f i ^ lookup m i))"
    by (simp add: mult_ac)
  also have "(\<Prod>i. c i ^ lookup m i) * (\<Prod>i. f i ^ lookup m i) =
               (\<Prod>i. (c i * f i) ^ lookup m i)"
    by (subst Prod_any.distrib [symmetric])
       (auto simp: power_mult_distrib intro!: finite_subset[OF _ finite_lookup[of m]] Nat.gr0I)
  finally show ?case by simp
qed

lemma vars_mapm_mpoly_subset: "vars (mapm_mpoly f p) \<subseteq> vars p"
  unfolding vars_def using keys_mapp_subset[of f] by (auto simp: mapm_mpoly.rep_eq)

lemma map_mpoly_cong:
  assumes "\<And>m. f (coeff p m) = g (coeff p m)" "p = q"
  shows   "map_mpoly f p = map_mpoly g q"
  using assms by (intro mpoly_eqI) (auto simp: coeff_map_mpoly)



subsection \<open>The leading monomial and leading coefficient\<close>

text \<open>
  The leading monomial of a multivariate polynomial is the one with the largest monomial
  w.\,r.\,t.\ the monomial ordering induced by the standard variable ordering. The
  leading coefficient is the coefficient of the leading monomial.

  As a convention, the leading monomial of the zero polynomial is defined to be the same as
  that of any non-constant zero polynomial, i.\,e.\ the monomial $X_1^0 \ldots X_n^0$.
\<close>

lift_definition lead_monom :: "'a :: zero mpoly \<Rightarrow> (nat \<Rightarrow>\<^sub>0 nat)" is
  "\<lambda>f :: (nat \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a. Max (insert 0 (keys f))" .

lemma lead_monom_geI [intro]:
  assumes "coeff p m \<noteq> 0"
  shows   "m \<le> lead_monom p"
  using assms by (auto simp: lead_monom_def coeff_def in_keys_iff)

lemma coeff_gt_lead_monom_zero [simp]:
  assumes "m > lead_monom p"
  shows   "coeff p m = 0"
  using lead_monom_geI[of p m] assms by force

lemma lead_monom_nonzero_eq:
  assumes "p \<noteq> 0"
  shows   "lead_monom p = Max (keys (mapping_of p))"
  using assms by transfer (simp add: max_def)

lemma lead_monom_0 [simp]: "lead_monom 0 = 0"
  by (simp add: lead_monom_def zero_mpoly.rep_eq)

lemma lead_monom_1 [simp]: "lead_monom 1 = 0"
  by (simp add: lead_monom_def one_mpoly.rep_eq)

lemma lead_monom_Const [simp]: "lead_monom (Const c) = 0"
  by (simp add: lead_monom_def Const.rep_eq Const\<^sub>0_def)

lemma lead_monom_uminus [simp]: "lead_monom (-p) = lead_monom p"
  by (simp add: lead_monom_def uminus_mpoly.rep_eq)

lemma keys_mult_const [simp]:
  fixes c :: "'a :: {semiring_0, semiring_no_zero_divisors}"
  assumes "c \<noteq> 0"
  shows "keys (Poly_Mapping.map ((*) c) p) = keys p"
  using assms by transfer auto

lemma lead_monom_eq_0_iff: "lead_monom p = 0 \<longleftrightarrow> vars p = {}"
  unfolding vars_def by transfer' (auto simp: Max_eq_iff)

lemma lead_monom_monom: "lead_monom (monom m c) = (if c = 0 then 0 else m)"
  by (auto simp add: lead_monom_def monom.rep_eq Const\<^sub>0_def max_def )

lemma lead_monom_monom' [simp]: "c \<noteq> 0 \<Longrightarrow> lead_monom (monom m c) = m"
  by (simp add: lead_monom_monom)

lemma lead_monom_numeral [simp]: "lead_monom (numeral n) = 0"
  unfolding monom_numeral[symmetric] by (subst lead_monom_monom) auto

lemma lead_monom_add: "lead_monom (p + q) \<le> max (lead_monom p) (lead_monom q)"
proof transfer
  fix p q :: "(nat \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a"
  show "Max (insert 0 (keys (p + q))) \<le> max (Max (insert 0 (keys p))) (Max (insert 0 (keys q)))"
  proof (rule Max.boundedI)
    fix m assume m: "m \<in> insert 0 (keys (p + q))"
    thus "m \<le> max (Max (insert 0 (keys p))) (Max (insert 0 (keys q)))"
    proof
      assume "m \<in> keys (p + q)"
      with keys_add[of p q] have "m \<in> keys p \<or> m \<in> keys q"
        by (auto simp: in_keys_iff plus_poly_mapping.rep_eq)
      thus ?thesis by (auto simp: le_max_iff_disj)
    qed auto
  qed auto
qed

lemma lead_monom_diff: "lead_monom (p - q) \<le> max (lead_monom p) (lead_monom q)"
proof transfer
  fix p q :: "(nat \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a"
  show "Max (insert 0 (keys (p - q))) \<le> max (Max (insert 0 (keys p))) (Max (insert 0 (keys q)))"
  proof (rule Max.boundedI)
    fix m assume m: "m \<in> insert 0 (keys (p - q))"
    thus "m \<le> max (Max (insert 0 (keys p))) (Max (insert 0 (keys q)))"
    proof
      assume "m \<in> keys (p - q)"
      with keys_diff_subset[of p q] have "m \<in> keys p \<or> m \<in> keys q" by auto
      thus ?thesis by (auto simp: le_max_iff_disj)
    qed auto
  qed auto
qed


definition lead_coeff where "lead_coeff p = coeff p (lead_monom p)"

lemma vars_empty_iff: "vars p = {} \<longleftrightarrow> p = Const (lead_coeff p)"
proof
  assume "vars p = {}"
  hence [simp]: "lead_monom p = 0"
    by (simp add: lead_monom_eq_0_iff)
  have [simp]: "mon \<noteq> 0 \<longleftrightarrow> (mon > (0 :: nat \<Rightarrow>\<^sub>0 nat))" for mon
    by (auto simp: order.strict_iff_order)
  thus "p = Const (lead_coeff p)"
    by (intro mpoly_eqI) (auto simp: mpoly_coeff_Const lead_coeff_def)
next
  assume "p = Const (lead_coeff p)"
  also have "vars \<dots> = {}" by simp
  finally show "vars p = {}" .
qed

lemma lead_coeff_0 [simp]: "lead_coeff 0 = 0"
  by (simp add: lead_coeff_def)

lemma lead_coeff_1 [simp]: "lead_coeff 1 = 1"
  by (simp add: lead_coeff_def mpoly_coeff_1)

lemma lead_coeff_Const [simp]: "lead_coeff (Const c) = c"
  by (simp add: lead_coeff_def mpoly_coeff_Const)

lemma lead_coeff_monom [simp]: "lead_coeff (monom p c) = c"
  by (simp add: lead_coeff_def coeff_monom when_def lead_monom_monom)

lemma lead_coeff_nonzero [simp]: "p \<noteq> 0 \<Longrightarrow> lead_coeff p \<noteq> 0"
  unfolding lead_coeff_def lead_monom_def
  by (cases "keys (mapping_of p) = {}") (auto simp: coeff_def max_def)

lemma
  fixes c :: "'a :: semiring_0"
  assumes "c * lead_coeff p \<noteq> 0"
  shows lead_monom_smult [simp]: "lead_monom (smult c p) = lead_monom p"
    and lead_coeff_smult [simp]: "lead_coeff (smult c p) = c * lead_coeff p"
proof -
  from assms have *: "keys (mapping_of p) \<noteq> {}"
    by auto
  from assms have "coeff (MPoly_Type.smult c p) (lead_monom p) \<noteq> 0"
    by (simp add: lead_coeff_def)
  hence smult_nz: "MPoly_Type.smult c p \<noteq> 0" by (auto simp del: coeff_smult)
  with assms have **: "keys (mapping_of (smult c p)) \<noteq> {}"
    by simp

  have "Max (keys (mapping_of (smult c p))) = Max (keys (mapping_of p))"
  proof (safe intro!: antisym Max.coboundedI)
    have "lookup (mapping_of p) (Max (keys (mapping_of p))) = lead_coeff p"
      using * by (simp add: lead_coeff_def lead_monom_def max_def coeff_def)
    with assms show "Max (keys (mapping_of p)) \<in> keys (mapping_of (smult c p))"
      using * by (auto simp: smult.rep_eq intro!: in_keys_mapI)
    from smult_nz have "lead_coeff (smult c p) \<noteq> 0"
      by (intro lead_coeff_nonzero) auto
    hence "coeff p (Max (keys (mapping_of (smult c p)))) \<noteq> 0"
      using assms * ** by (auto simp: lead_coeff_def lead_monom_def max_def)
    thus "Max (keys (mapping_of (smult c p))) \<in> keys (mapping_of p)"
      by (auto simp: smult.rep_eq coeff_def in_keys_iff)
  qed auto
  with * ** show "lead_monom (smult c p) = lead_monom p"
    by (simp add: lead_monom_def max_def)
  thus "lead_coeff (smult c p) = c * lead_coeff p"
    by (simp add: lead_coeff_def)
qed

lemma lead_coeff_mult_aux:
  "coeff (p * q) (lead_monom p + lead_monom q) = lead_coeff p * lead_coeff q"
proof (cases "p = 0 \<or> q = 0")
  case False
  define a b where "a = lead_monom p" and "b = lead_monom q"
  have "coeff (p * q) (a + b) = coeff p a * coeff q b"
    unfolding coeff_mpoly_times
    by (rule prod_fun_max) (insert False, auto simp: a_def b_def)
  thus ?thesis by (simp add: a_def b_def lead_coeff_def)
qed auto

lemma lead_monom_mult_le: "lead_monom (p * q) \<le> lead_monom p + lead_monom q"
proof (cases "p * q = 0")
  case False
  show ?thesis
  proof (intro leI notI)
    assume "lead_monom p + lead_monom q < lead_monom (p * q)"
    hence "lead_coeff (p * q) = 0"
      unfolding lead_coeff_def coeff_mpoly_times by (rule prod_fun_gt_max_eq_zero) auto
    with False show False by simp
  qed
qed auto

lemma lead_monom_mult:
  assumes "lead_coeff p * lead_coeff q \<noteq> 0"
  shows   "lead_monom (p * q) = lead_monom p + lead_monom q"
  by (intro antisym lead_monom_mult_le lead_monom_geI)
     (insert assms, auto simp: lead_coeff_mult_aux)

lemma lead_coeff_mult:
  assumes "lead_coeff p * lead_coeff q \<noteq> 0"
  shows   "lead_coeff (p * q) = lead_coeff p * lead_coeff q"
  using assms by (simp add: lead_monom_mult lead_coeff_mult_aux lead_coeff_def)

lemma keys_lead_monom_subset: "keys (lead_monom p) \<subseteq> vars p"
proof (cases "p = 0")
  case False
  hence "lead_coeff p \<noteq> 0" by simp
  hence "coeff p (lead_monom p) \<noteq> 0" unfolding lead_coeff_def .
  thus ?thesis unfolding vars_def by transfer' (auto simp: max_def in_keys_iff)
qed auto

lemma
  assumes "(\<Prod>i\<in>A. lead_coeff (f i)) \<noteq> 0"
    shows lead_monom_prod: "lead_monom (\<Prod>i\<in>A. f i) = (\<Sum>i\<in>A. lead_monom (f i))" (is ?th1)
      and lead_coeff_prod: "lead_coeff (\<Prod>i\<in>A. f i) = (\<Prod>i\<in>A. lead_coeff (f i))" (is ?th2)
proof -
  have "?th1 \<and> ?th2" using assms
  proof (induction A rule: infinite_finite_induct)
    case (insert x A)
    from insert have nz: "lead_coeff (f x) \<noteq> 0" "(\<Prod>i\<in>A. lead_coeff (f i)) \<noteq> 0" by auto
    note IH = insert.IH[OF this(2)]
    from insert have nz': "lead_coeff (f x) * lead_coeff (\<Prod>i\<in>A. f i) \<noteq> 0"
      by (subst IH) auto
    from insert.prems insert.hyps nz nz' show ?case
      by (auto simp: lead_monom_mult lead_coeff_mult IH)
  qed auto
  thus ?th1 ?th2 by blast+
qed

lemma lead_monom_sum_le: "(\<And>x. x \<in> X \<Longrightarrow> lead_monom (h x) \<le> ub) \<Longrightarrow> lead_monom (sum h X) \<le> ub"
  by (induction X rule: infinite_finite_induct) (auto intro!: order.trans[OF lead_monom_add])

text \<open>
  The leading monomial of a sum where the leading monomial the summands are distinct is
  simply the maximum of the leading monomials.
\<close>
lemma lead_monom_sum:
  assumes "inj_on (lead_monom \<circ> h) X" and "finite X" and "X \<noteq> {}" and "\<And>x. x \<in> X \<Longrightarrow> h x \<noteq> 0"
  defines "m \<equiv> Max ((lead_monom \<circ> h) ` X)"
  shows   "lead_monom (\<Sum>x\<in>X. h x) = m"
proof (rule antisym)
  show "lead_monom (sum h X) \<le> m" unfolding m_def using assms
    by (intro lead_monom_sum_le Max_ge finite_imageI) auto
next
  from assms have "m \<in> (lead_monom \<circ> h) ` X"
    unfolding m_def by (intro Max_in finite_imageI) auto
  then obtain x where x: "x \<in> X" "m = lead_monom (h x)" by auto
  have "coeff (\<Sum>x\<in>X. h x) m = (\<Sum>x\<in>X. coeff (h x) m)"
    by simp
  also have "\<dots> = (\<Sum>x\<in>{x}. coeff (h x) m)"
  proof (intro sum.mono_neutral_right ballI)
    fix y assume y: "y \<in> X - {x}"
    hence "(lead_monom \<circ> h) y \<le> m"
      using assms unfolding m_def by (intro Max_ge finite_imageI) auto
    moreover have "(lead_monom \<circ> h) y \<noteq> (lead_monom \<circ> h) x"
      using \<open>x \<in> X\<close> y inj_onD[OF assms(1), of x y] by auto
    ultimately have "lead_monom (h y) < m"
      using x by auto
    thus "coeff (h y) m = 0" by simp
  qed (insert x assms, auto)
  also have "\<dots> = coeff (h x) m" by simp
  also have "\<dots> = lead_coeff (h x)" using x by (simp add: lead_coeff_def)
  also have "\<dots> \<noteq> 0" using assms x by auto
  finally show "lead_monom (sum h X) \<ge> m" by (intro lead_monom_geI)
qed

lemma lead_coeff_eq_0_iff [simp]: "lead_coeff p = 0 \<longleftrightarrow> p = 0"
  by (cases "p = 0") auto

lemma
  fixes f :: "_ \<Rightarrow> 'a :: semidom mpoly"
  assumes "\<And>i. i \<in> A \<Longrightarrow> f i \<noteq> 0"
    shows lead_monom_prod' [simp]: "lead_monom (\<Prod>i\<in>A. f i) = (\<Sum>i\<in>A. lead_monom (f i))" (is ?th1)
      and lead_coeff_prod' [simp]: "lead_coeff (\<Prod>i\<in>A. f i) = (\<Prod>i\<in>A. lead_coeff (f i))" (is ?th2)
proof -
  from assms have "(\<Prod>i\<in>A. lead_coeff (f i)) \<noteq> 0"
    by (cases "finite A") auto
  thus ?th1 ?th2 by (simp_all add: lead_monom_prod lead_coeff_prod)
qed

lemma
  fixes p :: "'a :: comm_semiring_1 mpoly"
  assumes "lead_coeff p ^ n \<noteq> 0"
  shows   lead_monom_power: "lead_monom (p ^ n) = of_nat n * lead_monom p"
  and     lead_coeff_power: "lead_coeff (p ^ n) = lead_coeff p ^ n"
  using assms lead_monom_prod[of "\<lambda>_. p" "{..<n}"] lead_coeff_prod[of "\<lambda>_. p" "{..<n}"]
  by simp_all

lemma
  fixes p :: "'a :: semidom mpoly"
  assumes "p \<noteq> 0"
  shows   lead_monom_power' [simp]: "lead_monom (p ^ n) = of_nat n * lead_monom p"
  and     lead_coeff_power' [simp]: "lead_coeff (p ^ n) = lead_coeff p ^ n"
  using assms lead_monom_prod'[of "{..<n}" "\<lambda>_. p"] lead_coeff_prod'[of "{..<n}" "\<lambda>_. p"]
  by simp_all


subsection \<open>Turning a set of variables into a monomial\<close>

text \<open>
  Given a finite set $\{X_1,\ldots,X_n\}$ of variables, the following is the monomial
  $X_1\ldots X_n$:
\<close>
lift_definition monom_of_set :: "nat set \<Rightarrow> (nat \<Rightarrow>\<^sub>0 nat)" is
  "\<lambda>X x. if finite X \<and> x \<in> X then 1 else 0"
  by auto

lemma lookup_monom_of_set:
  "Poly_Mapping.lookup (monom_of_set X) i = (if finite X \<and> i \<in> X then 1 else 0)"
  by transfer auto

lemma lookup_monom_of_set_1 [simp]:
        "finite X \<Longrightarrow> i \<in> X \<Longrightarrow> Poly_Mapping.lookup (monom_of_set X) i = 1"
  and lookup_monom_of_set_0 [simp]:
        "i \<notin> X \<Longrightarrow> Poly_Mapping.lookup (monom_of_set X) i = 0"
  by (simp_all add: lookup_monom_of_set)

lemma keys_monom_of_set: "keys (monom_of_set X) = (if finite X then X else {})"
  by transfer auto

lemma keys_monom_of_set_finite [simp]: "finite X \<Longrightarrow> keys (monom_of_set X) = X"
  by (simp add: keys_monom_of_set)

lemma monom_of_set_eq_iff [simp]: "finite X \<Longrightarrow> finite Y \<Longrightarrow> monom_of_set X = monom_of_set Y \<longleftrightarrow> X = Y"
  by transfer (auto simp: fun_eq_iff)

lemma monom_of_set_empty [simp]: "monom_of_set {} = 0"
  by transfer auto

lemma monom_of_set_eq_zero_iff [simp]: "monom_of_set X = 0 \<longleftrightarrow> infinite X \<or> X = {}"
  by transfer (auto simp: fun_eq_iff)

lemma zero_eq_monom_of_set_iff [simp]: "0 = monom_of_set X \<longleftrightarrow> infinite X \<or> X = {}"
  by transfer (auto simp: fun_eq_iff)



subsection \<open>Permuting the variables of a polynomial\<close>

text \<open>
  Next, we define the operation of permuting the variables of a monomial and polynomial.
\<close>

lift_definition permutep :: "('a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b) \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b :: zero)" is
  "\<lambda>f p. if bij f then p \<circ> f else p"
proof -
  fix f :: "'a \<Rightarrow> 'a" and g :: "'a \<Rightarrow> 'b"
  assume *: "finite {x. g x \<noteq> 0}"
  show "finite {x. (if bij f then g \<circ> f else g) x \<noteq> 0}"
  proof (cases "bij f")
    case True
    with * have "finite (f -` {x. g x \<noteq> 0})"
      by (intro finite_vimageI) (auto dest: bij_is_inj)
    with True show ?thesis by auto
  qed (use * in auto)
qed

lift_definition mpoly_map_vars :: "(nat \<Rightarrow> nat) \<Rightarrow> 'a :: zero mpoly \<Rightarrow> 'a mpoly" is
  "\<lambda>f p. permutep (permutep f) p" .

lemma keys_permutep: "bij f \<Longrightarrow> keys (permutep f m) = f -` keys m"
  by transfer auto

lemma permutep_id'' [simp]: "permutep id = id"
  by transfer' (auto simp: fun_eq_iff)

lemma permutep_id''' [simp]: "permutep (\<lambda>x. x) = id"
  by transfer' (auto simp: fun_eq_iff)

lemma permutep_0 [simp]: "permutep f 0 = 0"
  by transfer auto

lemma permutep_single:
  "bij f \<Longrightarrow> permutep f (Poly_Mapping.single a b) = Poly_Mapping.single (inv_into UNIV f a) b"
  by transfer (auto simp: fun_eq_iff when_def inv_f_f surj_f_inv_f bij_is_inj bij_is_surj)

lemma mpoly_map_vars_id [simp]: "mpoly_map_vars id = id"
  by transfer auto

lemma mpoly_map_vars_id' [simp]: "mpoly_map_vars (\<lambda>x. x) = id"
  by transfer auto

lemma lookup_permutep:
  "Poly_Mapping.lookup (permutep f m) x = (if bij f then Poly_Mapping.lookup m (f x) else Poly_Mapping.lookup m x)"
  by transfer auto

lemma inj_permutep [intro]: "inj (permutep (f :: 'a \<Rightarrow> 'a) :: _ \<Rightarrow> 'a \<Rightarrow>\<^sub>0 'b :: zero)"
  unfolding inj_def
proof (transfer, safe)
  fix f :: "'a \<Rightarrow> 'a" and x y :: "'a \<Rightarrow> 'b"
  assume eq: "(if bij f then x \<circ> f else x) = (if bij f then y \<circ> f else y)"
  show "x = y"
  proof (cases "bij f")
    case True
    show ?thesis
    proof
      fix t :: 'a
      from \<open>bij f\<close> obtain s where "t = f s"
        by (auto dest!: bij_is_surj)
      with eq and True show "x t = y t"
        by (auto simp: fun_eq_iff)
    qed
  qed (use eq in auto)
qed

lemma surj_permutep [intro]: "surj (permutep (f :: 'a \<Rightarrow> 'a) :: _ \<Rightarrow> 'a \<Rightarrow>\<^sub>0 'b :: zero)"
  unfolding surj_def
proof (transfer, safe)
  fix f :: "'a \<Rightarrow> 'a" and y :: "'a \<Rightarrow> 'b"
  assume fin: "finite {t. y t \<noteq> 0}"
  show "\<exists>x\<in>{f. finite {x. f x \<noteq> 0}}. y = (if bij f then x \<circ> f else x)"
  proof (cases "bij f")
    case True
    with fin have "finite (the_inv f -` {t. y t \<noteq> 0})"
      by (intro finite_vimageI) (auto simp: bij_is_inj bij_betw_the_inv_into)
    moreover have "y \<circ> the_inv f \<circ> f = y"
      using True by (simp add: fun_eq_iff the_inv_f_f bij_is_inj)
    ultimately show ?thesis by (intro bexI[of _ "y \<circ> the_inv f"]) (auto simp: True)
  qed (use fin in auto)
qed

lemma bij_permutep [intro]: "bij (permutep f)"
  using inj_permutep[of f] surj_permutep[of f] by (simp add: bij_def)

lemma mpoly_map_vars_map_mpoly:
  "mpoly_map_vars f (map_mpoly g p) = map_mpoly g (mpoly_map_vars f p)"
  by (transfer', transfer') (auto simp: fun_eq_iff)

lemma coeff_mpoly_map_vars:
  fixes f :: "nat \<Rightarrow> nat" and p :: "'a :: zero mpoly"
  assumes "bij f"
  shows   "MPoly_Type.coeff (mpoly_map_vars f p) mon =
             MPoly_Type.coeff p (permutep f mon)"
  using assms by transfer' (simp add: lookup_permutep bij_permutep)

lemma permutep_monom_of_set:
  assumes "bij f"
  shows   "permutep f (monom_of_set A) = monom_of_set (f -` A)"
  using assms by transfer (auto simp: fun_eq_iff bij_is_inj finite_vimage_iff)

lemma permutep_comp: "bij f \<Longrightarrow> bij g \<Longrightarrow> permutep (f \<circ> g) = permutep g \<circ> permutep f"
  by transfer' (auto simp: fun_eq_iff bij_comp)

lemma permutep_comp': "bij f \<Longrightarrow> bij g \<Longrightarrow> permutep (f \<circ> g) mon = permutep g (permutep f mon)"
  by transfer (auto simp: fun_eq_iff bij_comp)

lemma mpoly_map_vars_comp:
  "bij f \<Longrightarrow> bij g \<Longrightarrow> mpoly_map_vars f (mpoly_map_vars g p) = mpoly_map_vars (f \<circ> g) p"
  by transfer (auto simp: bij_permutep permutep_comp)

lemma permutep_id [simp]: "permutep id mon = mon"
  by transfer auto

lemma permutep_id' [simp]: "permutep (\<lambda>x. x) mon = mon"
  by transfer auto

lemma inv_permutep [simp]:
  fixes f :: "'a \<Rightarrow> 'a"
  assumes "bij f"
  shows   "inv_into UNIV (permutep f) = permutep (inv_into UNIV f)"
proof
  fix m :: "'a \<Rightarrow>\<^sub>0 'b"
  show "inv_into UNIV (permutep f) m = permutep (inv_into UNIV f) m"
    using permutep_comp'[of "inv_into UNIV f" f m] assms inj_iff[of f]
    by (intro inv_f_eq) (auto simp: bij_imp_bij_inv bij_is_inj)
qed

lemma mpoly_map_vars_monom:
  "bij f \<Longrightarrow> mpoly_map_vars f (monom m c) = monom (permutep (inv_into UNIV f) m) c"
  by transfer' (simp add: permutep_single bij_permutep)

lemma vars_mpoly_map_vars:
  fixes f :: "nat \<Rightarrow> nat" and p :: "'a :: zero mpoly"
  assumes "bij f"
  shows   "vars (mpoly_map_vars f p) = f ` vars p"
  using assms unfolding vars_def
proof transfer'
  fix f :: "nat \<Rightarrow> nat" and p :: "(nat \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a"
  assume f: "bij f"
  have eq: "f (inv_into UNIV f x) = x" for x
    using f by (subst surj_f_inv_f[of f]) (auto simp: bij_is_surj)
  show "\<Union> (keys ` keys (permutep (permutep f) p)) = f ` \<Union> (keys ` keys p)"
  proof safe
    fix m x assume mx: "m \<in> keys (permutep (permutep f) p)" "x \<in> keys m"
    from mx have "permutep f m \<in> keys p"
      by (auto simp: keys_permutep bij_permutep f)
    with mx have "f (inv_into UNIV f x) \<in> f ` (\<Union>m\<in>keys p. keys m)"
      by (intro imageI) (auto intro!: bexI[of _ "permutep f m"] simp: keys_permutep f eq)
    with eq show "x \<in> f ` (\<Union>m\<in>keys p. keys m)" by simp
  next
    fix m x assume mx: "m \<in> keys p" "x \<in> keys m"
    from mx have "permutep id m \<in> keys p" by simp
    also have "id = inv_into UNIV f \<circ> f" using f by (intro ext) (auto simp: bij_is_inj inv_f_f)
    also have "permutep \<dots> m = permutep f (permutep (inv_into UNIV f) m)"
      by (simp add: permutep_comp f bij_imp_bij_inv)
    finally have **: "permutep f (permutep (inv_into UNIV f) m) \<in> keys p" .
    moreover from f mx have "f x \<in> keys (permutep (inv_into UNIV f) m)"
      by (auto simp: keys_permutep bij_imp_bij_inv inv_f_f bij_is_inj)
    ultimately show "f x \<in> \<Union> (keys ` keys (permutep (permutep f) p))" using f
      by (auto simp: keys_permutep bij_permutep)
  qed
qed

lemma permutep_eq_monom_of_set_iff [simp]:
  assumes "bij f"
  shows   "permutep f mon = monom_of_set A \<longleftrightarrow> mon = monom_of_set (f ` A)"
proof
  assume eq: "permutep f mon = monom_of_set A"
  have "permutep (inv_into UNIV f) (permutep f mon) = monom_of_set (inv_into UNIV f -` A)"
    using assms by (simp add: eq bij_imp_bij_inv assms permutep_monom_of_set)
  also have "inv_into UNIV f -` A = f ` A"
    using assms by (force simp: bij_is_surj image_iff inv_f_f bij_is_inj surj_f_inv_f)
  also have "permutep (inv_into UNIV f) (permutep f mon) = permutep (f \<circ> inv_into UNIV f) mon"
    using assms by (simp add: permutep_comp bij_imp_bij_inv)
  also have "f \<circ> inv_into UNIV f = id"
    by (subst surj_iff [symmetric]) (insert assms, auto simp: bij_is_surj)
  finally show "mon = monom_of_set (f ` A)" by simp
qed (insert assms, auto simp: permutep_monom_of_set inj_vimage_image_eq bij_is_inj)

lemma permutep_monom_of_set_permutes [simp]:
  assumes "\<pi> permutes A"
  shows   "permutep \<pi> (monom_of_set A) = monom_of_set A"
  using assms
  by transfer (auto simp: if_splits fun_eq_iff permutes_in_image)

lemma mpoly_map_vars_0 [simp]: "mpoly_map_vars f 0 = 0"
  by (transfer, transfer') (simp add: o_def)

lemma permutep_eq_0_iff [simp]: "permutep f m = 0 \<longleftrightarrow> m = 0"
proof transfer
  fix f :: "'a \<Rightarrow> 'a" and m :: "'a \<Rightarrow> 'b" assume "finite {x. m x \<noteq> 0}"
  show "((if bij f then m \<circ> f else m) = (\<lambda>k. 0)) = (m = (\<lambda>k. 0))"
  proof (cases "bij f")
    case True
    hence "(\<forall>x. m (f x) = 0) \<longleftrightarrow> (\<forall>x. m x = 0)"
      using bij_iff[of f] by metis
    with True show ?thesis by (auto simp: fun_eq_iff)
  qed (auto simp: fun_eq_iff)
qed

lemma mpoly_map_vars_1 [simp]: "mpoly_map_vars f 1 = 1"
  by (transfer, transfer') (auto simp: o_def fun_eq_iff when_def)

lemma permutep_Const\<^sub>0 [simp]: "(\<And>x. f x = 0 \<longleftrightarrow> x = 0) \<Longrightarrow> permutep f (Const\<^sub>0 c) = Const\<^sub>0 c"
  unfolding Const\<^sub>0_def by transfer' (auto simp: when_def fun_eq_iff)

lemma permutep_add [simp]: "permutep f (m1 + m2) = permutep f m1 + permutep f m2"
  unfolding Const\<^sub>0_def by transfer' (auto simp: when_def fun_eq_iff)

lemma permutep_diff [simp]: "permutep f (m1 - m2) = permutep f m1 - permutep f m2"
  unfolding Const\<^sub>0_def by transfer' (auto simp: when_def fun_eq_iff)

lemma permutep_uminus [simp]: "permutep f (-m) = -permutep f m"
  unfolding Const\<^sub>0_def by transfer' (auto simp: when_def fun_eq_iff)

lemma permutep_mult [simp]:
  "(\<And>x y. f (x + y) = f x + f y) \<Longrightarrow> permutep f (m1 * m2) = permutep f m1 * permutep f m2"
  unfolding Const\<^sub>0_def by transfer' (auto simp: when_def fun_eq_iff prod_fun_compose_bij)

lemma mpoly_map_vars_Const [simp]: "mpoly_map_vars f (Const c) = Const c"
  by transfer (auto simp: o_def fun_eq_iff when_def)

lemma mpoly_map_vars_add [simp]: "mpoly_map_vars f (p + q) = mpoly_map_vars f p + mpoly_map_vars f q"
  by transfer simp

lemma mpoly_map_vars_diff [simp]: "mpoly_map_vars f (p - q) = mpoly_map_vars f p - mpoly_map_vars f q"
  by transfer simp

lemma mpoly_map_vars_uminus [simp]: "mpoly_map_vars f (-p) = -mpoly_map_vars f p"
  by transfer simp

lemma permutep_smult:
  "permutep (permutep f) (Poly_Mapping.map ((*) c) p) =
     Poly_Mapping.map ((*) c) (permutep (permutep f) p)"
  by transfer' (auto split: if_splits simp: fun_eq_iff)

lemma mpoly_map_vars_smult [simp]: "mpoly_map_vars f (smult c p) = smult c (mpoly_map_vars f p)"
  by transfer (simp add: permutep_smult)

lemma mpoly_map_vars_mult [simp]: "mpoly_map_vars f (p * q) = mpoly_map_vars f p * mpoly_map_vars f q"
  by transfer simp

lemma mpoly_map_vars_sum [simp]: "mpoly_map_vars f (sum g A) = (\<Sum>x\<in>A. mpoly_map_vars f (g x))"
  by (induction A rule: infinite_finite_induct) auto

lemma mpoly_map_vars_prod [simp]: "mpoly_map_vars f (prod g A) = (\<Prod>x\<in>A. mpoly_map_vars f (g x))"
  by (induction A rule: infinite_finite_induct) auto

lemma mpoly_map_vars_eq_0_iff [simp]: "mpoly_map_vars f p = 0 \<longleftrightarrow> p = 0"
  by transfer auto

lemma permutep_eq_iff [simp]: "permutep f p = permutep f q \<longleftrightarrow> p = q"
  by transfer (auto simp: comp_bij_eq_iff)

lemma mpoly_map_vars_Sum_any [simp]:
  "mpoly_map_vars f (Sum_any g) = Sum_any (\<lambda>x. mpoly_map_vars f (g x))"
  by (simp add: Sum_any.expand_set)

lemma mpoly_map_vars_power [simp]: "mpoly_map_vars f (p ^ n) = mpoly_map_vars f p ^ n"
  by (induction n) auto

lemma mpoly_map_vars_monom_single [simp]:
  assumes "bij f"
  shows   "mpoly_map_vars f (monom (Poly_Mapping.single i n) c) =
             monom (Poly_Mapping.single (f i) n) c"
  using assms by (simp add: mpoly_map_vars_monom permutep_single bij_imp_bij_inv inv_inv_eq)

lemma insertion_mpoly_map_vars:
  assumes "bij f"
  shows   "insertion g (mpoly_map_vars f p) = insertion (g \<circ> f) p"
proof -
  have "insertion g (mpoly_map_vars f p) =
          (\<Sum>m. coeff p (permutep f m) * (\<Prod>i. g i ^ lookup m i))"
    using assms by (simp add: insertion_altdef coeff_mpoly_map_vars)
  also have "\<dots> = Sum_any (\<lambda>m. coeff p (permutep f m) *
                    Prod_any (\<lambda>i. g (f i) ^ lookup m (f i)))"
    by (intro Sum_any.cong arg_cong[where ?f = "\<lambda>y. x * y" for x]
          Prod_any.reindex_cong[OF assms]) (auto simp: o_def)
  also have "\<dots> = Sum_any (\<lambda>m. coeff p m * (\<Prod>i. g (f i) ^ lookup m i))"
    by (intro Sum_any.reindex_cong [OF bij_permutep[of f], symmetric])
       (auto simp: o_def lookup_permutep assms)
  also have "\<dots> = insertion (g \<circ> f) p"
    by (simp add: insertion_altdef)
  finally show ?thesis .
qed

lemma permutep_cong:
  assumes "f permutes (-keys p)" "g permutes (-keys p)" "p = q"
  shows   "permutep f p = permutep g q"
proof (intro poly_mapping_eqI)
  fix k :: 'a
  show "lookup (permutep f p) k = lookup (permutep g q) k"
  proof (cases "k \<in> keys p")
    case False
    with assms have "f k \<notin> keys p" "g k \<notin> keys p"
      using permutes_in_image[of _ "-keys p" k] by auto
    thus ?thesis using assms by (auto simp: lookup_permutep permutes_bij in_keys_iff)
  qed (insert assms, auto simp: lookup_permutep permutes_bij permutes_not_in)
qed

lemma mpoly_map_vars_cong:
  assumes "f permutes (-vars p)" "g permutes (-vars q)" "p = q"
  shows   "mpoly_map_vars f p = mpoly_map_vars g (q :: 'a :: zero mpoly)"
proof (intro mpoly_eqI)
  fix mon :: "nat \<Rightarrow>\<^sub>0 nat"
  show "coeff (mpoly_map_vars f p) mon = coeff (mpoly_map_vars g q) mon"
  proof (cases "keys mon \<subseteq> vars p")
    case True
    with assms have "permutep f mon = permutep g mon"
      by (intro permutep_cong assms(1,2)[THEN permutes_subset]) auto
    thus ?thesis using assms by (simp add: coeff_mpoly_map_vars permutes_bij)
  next
    case False
    hence "\<not>(keys mon \<subseteq> f ` vars q)" "\<not>(keys mon \<subseteq> g ` vars q)"
      using assms by (auto simp: subset_iff permutes_not_in)
    thus ?thesis using assms
      by (subst (1 2) coeff_notin_vars)
         (auto simp: coeff_notin_vars vars_mpoly_map_vars permutes_bij)
  qed
qed



subsection \<open>Symmetric polynomials\<close>

text \<open>
  A polynomial is symmetric on a set of variables if it is invariant under
  any permutation of that set.
\<close>
definition symmetric_mpoly :: "nat set \<Rightarrow> 'a :: zero mpoly \<Rightarrow> bool" where
  "symmetric_mpoly A p = (\<forall>\<pi>. \<pi> permutes A \<longrightarrow> mpoly_map_vars \<pi> p = p)"

lemma symmetric_mpoly_empty [simp, intro]: "symmetric_mpoly {} p"
  by (simp add: symmetric_mpoly_def)

text \<open>
  A polynomial is trivially symmetric on any set of variables that do not occur in it.
\<close>
lemma symmetric_mpoly_orthogonal:
  assumes "vars p \<inter> A = {}"
  shows   "symmetric_mpoly A p"
  unfolding symmetric_mpoly_def
proof safe
  fix \<pi> assume \<pi>: "\<pi> permutes A"
  with assms have "\<pi> x = x" if "x \<in> vars p" for x
    using that permutes_not_in[of \<pi> A x] by auto
  from assms have "mpoly_map_vars \<pi> p = mpoly_map_vars id p"
    by (intro mpoly_map_vars_cong permutes_subset[OF \<pi>] permutes_id) auto
  also have "\<dots> = p" by simp
  finally show "mpoly_map_vars \<pi> p = p" .
qed

lemma symmetric_mpoly_monom [intro]:
  assumes "keys m \<inter> A = {}"
  shows   "symmetric_mpoly A (monom m c)"
  using assms vars_monom_subset[of m c] by (intro symmetric_mpoly_orthogonal) auto

lemma symmetric_mpoly_subset:
  assumes "symmetric_mpoly A p" "B \<subseteq> A"
  shows   "symmetric_mpoly B p"
  unfolding symmetric_mpoly_def
proof safe
  fix \<pi> assume "\<pi> permutes B"
  with assms have "\<pi> permutes A" using permutes_subset by blast
  with assms show "mpoly_map_vars \<pi> p = p"
    by (auto simp: symmetric_mpoly_def)
qed

text \<open>
  If a polynomial is symmetric over some set of variables, that set must either be a subset
  of the variables occurring in the polynomial or disjoint from it.
\<close>
lemma symmetric_mpoly_imp_orthogonal_or_subset:
  assumes "symmetric_mpoly A p"
  shows   "vars p \<inter> A = {} \<or> A \<subseteq> vars p"
proof (rule ccontr)
  assume "\<not>(vars p \<inter> A = {} \<or> A \<subseteq> vars p)"
  then obtain x y where xy: "x \<in> vars p \<inter> A" "y \<in> A - vars p" by auto
  define \<pi> where "\<pi> = Fun.swap x y id"
  from xy have \<pi>: "\<pi> permutes A"
    unfolding \<pi>_def by (intro permutes_swap_id) auto
  from xy have "y \<in> \<pi> ` vars p" by (auto simp: \<pi>_def Fun.swap_def)
  also from \<pi> have "\<pi> ` vars p = vars (mpoly_map_vars \<pi> p)"
    by (auto simp: vars_mpoly_map_vars permutes_bij)
  also have "mpoly_map_vars \<pi> p = p"
    using assms \<pi> by (simp add: symmetric_mpoly_def)
  finally show False using xy by auto
qed

text \<open>
  Symmetric polynomials are closed under ring operations.
\<close>
lemma symmetric_mpoly_add [intro]:
  "symmetric_mpoly A p \<Longrightarrow> symmetric_mpoly A q \<Longrightarrow> symmetric_mpoly A (p + q)"
  unfolding symmetric_mpoly_def by simp

lemma symmetric_mpoly_diff [intro]:
  "symmetric_mpoly A p \<Longrightarrow> symmetric_mpoly A q \<Longrightarrow> symmetric_mpoly A (p - q)"
  unfolding symmetric_mpoly_def by simp

lemma symmetric_mpoly_uminus [intro]: "symmetric_mpoly A p \<Longrightarrow> symmetric_mpoly A (-p)"
  unfolding symmetric_mpoly_def by simp

lemma symmetric_mpoly_uminus_iff [simp]: "symmetric_mpoly A (-p) \<longleftrightarrow> symmetric_mpoly A p"
  unfolding symmetric_mpoly_def by simp

lemma symmetric_mpoly_smult [intro]: "symmetric_mpoly A p \<Longrightarrow> symmetric_mpoly A (smult c p)"
  unfolding symmetric_mpoly_def by simp

lemma symmetric_mpoly_mult [intro]:
  "symmetric_mpoly A p \<Longrightarrow> symmetric_mpoly A q \<Longrightarrow> symmetric_mpoly A (p * q)"
  unfolding symmetric_mpoly_def by simp

lemma symmetric_mpoly_0 [simp, intro]: "symmetric_mpoly A 0"
  and symmetric_mpoly_1 [simp, intro]: "symmetric_mpoly A 1"
  and symmetric_mpoly_Const [simp, intro]: "symmetric_mpoly A (Const c)"
  by (simp_all add: symmetric_mpoly_def)

lemma symmetric_mpoly_power [intro]:
  "symmetric_mpoly A p \<Longrightarrow> symmetric_mpoly A (p ^ n)"
  by (induction n) (auto intro!: symmetric_mpoly_mult)

lemma symmetric_mpoly_sum [intro]:
  "(\<And>i. i \<in> B \<Longrightarrow> symmetric_mpoly A (f i)) \<Longrightarrow> symmetric_mpoly A (sum f B)"
  by (induction B rule: infinite_finite_induct) (auto intro!: symmetric_mpoly_add)

lemma symmetric_mpoly_prod [intro]:
  "(\<And>i. i \<in> B \<Longrightarrow> symmetric_mpoly A (f i)) \<Longrightarrow> symmetric_mpoly A (prod f B)"
  by (induction B rule: infinite_finite_induct) (auto intro!: symmetric_mpoly_mult)

text \<open>
  An symmetric sum or product over polynomials yields a symmetric polynomial:
\<close>
lemma symmetric_mpoly_symmetric_sum:
  assumes "g permutes X"
  assumes "\<And>x \<pi>. x \<in> X \<Longrightarrow> \<pi> permutes A \<Longrightarrow> mpoly_map_vars \<pi> (f x) = f (g x)"
  shows "symmetric_mpoly A (\<Sum>x\<in>X. f x)"
  unfolding symmetric_mpoly_def
proof safe
  fix \<pi> assume \<pi>: "\<pi> permutes A"
  have "mpoly_map_vars \<pi> (sum f X) = (\<Sum>x\<in>X. mpoly_map_vars \<pi> (f x))"
    by simp
  also have "\<dots> = (\<Sum>x\<in>X. f (g x))"
    by (intro sum.cong assms \<pi> refl)
  also have "\<dots> = (\<Sum>x\<in>g`X. f x)"
    using assms by (subst sum.reindex) (auto simp: permutes_inj_on)
  also have "g ` X = X"
    using assms by (simp add: permutes_image)
  finally show "mpoly_map_vars \<pi> (sum f X) = sum f X" .
qed

lemma symmetric_mpoly_symmetric_prod:
  assumes "g permutes X"
  assumes "\<And>x \<pi>. x \<in> X \<Longrightarrow> \<pi> permutes A \<Longrightarrow> mpoly_map_vars \<pi> (f x) = f (g x)"
  shows "symmetric_mpoly A (\<Prod>x\<in>X. f x)"
  unfolding symmetric_mpoly_def
proof safe
  fix \<pi> assume \<pi>: "\<pi> permutes A"
  have "mpoly_map_vars \<pi> (prod f X) = (\<Prod>x\<in>X. mpoly_map_vars \<pi> (f x))"
    by simp
  also have "\<dots> = (\<Prod>x\<in>X. f (g x))"
    by (intro prod.cong assms \<pi> refl)
  also have "\<dots> = (\<Prod>x\<in>g`X. f x)"
    using assms by (subst prod.reindex) (auto simp: permutes_inj_on)
  also have "g ` X = X"
    using assms by (simp add: permutes_image)
  finally show "mpoly_map_vars \<pi> (prod f X) = prod f X" .
qed

text \<open>
  If $p$ is a polynomial that is symmetric on some subset of variables $A$, then for the leading
  monomial of $p$, the exponents of these variables are decreasing w.\,r.\,t.\ the variable
  ordering.
\<close>
theorem lookup_lead_monom_decreasing:
  assumes "symmetric_mpoly A p"
  defines "m \<equiv> lead_monom p"
  assumes "i \<in> A" "j \<in> A" "i \<le> j"
  shows   "lookup m i \<ge> lookup m j"
proof (cases "p = 0")
  case [simp]: False
  show ?thesis
  proof (intro leI notI)
    assume less: "lookup m i < lookup m j"
    define \<pi> where "\<pi> = Fun.swap i j id"
    from assms have \<pi>: "\<pi> permutes A"
      unfolding \<pi>_def by (intro permutes_swap_id) auto
    have [simp]: "\<pi> \<circ> \<pi> = id" "\<pi> i = j" "\<pi> j = i" "\<And>k. k \<noteq> i \<Longrightarrow> k \<noteq> j \<Longrightarrow> \<pi> k = k"
      by (auto simp: \<pi>_def Fun.swap_def fun_eq_iff)

    have "0 \<noteq> lead_coeff p" by simp
    also have "lead_coeff p = MPoly_Type.coeff (mpoly_map_vars \<pi> p) (permutep \<pi> m)"
      using \<pi> by (simp add: lead_coeff_def m_def coeff_mpoly_map_vars
                            permutes_bij permutep_comp' [symmetric])
    also have "mpoly_map_vars \<pi> p = p"
      using \<pi> assms by (simp add: symmetric_mpoly_def)
    finally have "permutep \<pi> m \<le> m" by (auto simp: m_def)

    moreover have "lookup m i < lookup (permutep \<pi> m) i"
              and "(\<forall>k<i. lookup m k = lookup (permutep \<pi> m) k)"
      using assms \<pi> less by (auto simp: lookup_permutep permutes_bij)
    hence "m < permutep \<pi> m"
      by (auto simp: less_poly_mapping_def less_fun_def)
    ultimately show False by simp
  qed
qed (auto simp: m_def)



subsection \<open>The elementary symmetric polynomials\<close>

text \<open>
  The $k$-th elementary symmetric polynomial for a finite set of variables $A$, with $k$ ranging
  between 1 and $|A|$, is the sum of the product of all subsets of $A$ with cardinality $k$:
\<close>
lift_definition sym_mpoly_aux :: "nat set \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a :: {zero_neq_one}" is
  "\<lambda>X k mon. if finite X \<and> (\<exists>Y. Y \<subseteq> X \<and> card Y = k \<and> mon = monom_of_set Y) then 1 else 0"
proof -
  fix k :: nat and X :: "nat set"
  show "finite {x. (if finite X \<and> (\<exists>Y\<subseteq>X. card Y = k \<and> x = monom_of_set Y) then 1 else 0) \<noteq>
           (0::'a)}" (is "finite ?A")
  proof (cases "finite X")
    case True
    have "?A \<subseteq> monom_of_set ` Pow X" by auto
    moreover from True have "finite (monom_of_set ` Pow X)" by simp
    ultimately show ?thesis by (rule finite_subset)
  qed auto
qed

lemma lookup_sym_mpoly_aux:
  "Poly_Mapping.lookup (sym_mpoly_aux X k) mon =
     (if finite X \<and> (\<exists>Y. Y \<subseteq> X \<and> card Y = k \<and> mon = monom_of_set Y) then 1 else 0)"
  by transfer' simp

lemma lookup_sym_mpoly_aux_monom_of_set [simp]:
  assumes "finite X" "Y \<subseteq> X" "card Y = k"
  shows   "Poly_Mapping.lookup (sym_mpoly_aux X k) (monom_of_set Y) = 1"
  using assms by (auto simp: lookup_sym_mpoly_aux)

lemma keys_sym_mpoly_aux: "m \<in> keys (sym_mpoly_aux A k) \<Longrightarrow> keys m \<subseteq> A"
  by transfer' (auto split: if_splits simp: keys_monom_of_set)

lift_definition sym_mpoly :: "nat set \<Rightarrow> nat \<Rightarrow> 'a :: {zero_neq_one} mpoly" is
  "sym_mpoly_aux" .

lemma vars_sym_mpoly_subset: "vars (sym_mpoly A k) \<subseteq> A"
  using keys_sym_mpoly_aux by (auto simp: vars_def sym_mpoly.rep_eq)

lemma coeff_sym_mpoly:
  "MPoly_Type.coeff (sym_mpoly X k) mon =
     (if finite X \<and> (\<exists>Y. Y \<subseteq> X \<and> card Y = k \<and> mon = monom_of_set Y) then 1 else 0)"
  by transfer' (simp add: lookup_sym_mpoly_aux)

lemma sym_mpoly_infinite: "\<not>finite A \<Longrightarrow> sym_mpoly A k = 0"
  by (transfer, transfer) auto

lemma sym_mpoly_altdef: "sym_mpoly A k = (\<Sum>X | X \<subseteq> A \<and> card X = k. monom (monom_of_set X) 1)"
proof (cases "finite A")
  case False
  hence *: "infinite {X. X \<subseteq> A \<and> infinite X}"
    by (rule infinite_infinite_subsets)
  have "infinite {X. X \<subseteq> A \<and> card X = 0}"
    by (rule infinite_super[OF _ *]) auto
  moreover have **: "infinite {X. X \<subseteq> A \<and> finite X \<and> card X = k}" if "k \<noteq> 0"
    using that infinite_card_subsets[of A k] False by auto
  have "infinite {X. X \<subseteq> A \<and> card X = k}" if "k \<noteq> 0"
    by (rule infinite_super[OF _ **[OF that]]) auto
  ultimately show ?thesis using False
    by (cases "k = 0") (simp_all add: sym_mpoly_infinite)
next
  case True
  show ?thesis
  proof (intro mpoly_eqI, goal_cases)
    case (1 m)
    show ?case
    proof (cases "\<exists>X. X \<subseteq> A \<and> card X = k \<and> m = monom_of_set X")
      case False
      thus ?thesis by (auto simp: coeff_sym_mpoly coeff_sum coeff_monom)
    next
      case True
      then obtain X where X: "X \<subseteq> A" "card X = k" "m = monom_of_set X"
        by blast
      have "coeff (\<Sum>X | X \<subseteq> A \<and> card X = k.
               monom (monom_of_set X) 1) m = (\<Sum>X\<in>{X}. 1)" unfolding coeff_sum
      proof (intro sum.mono_neutral_cong_right ballI)
        fix Y assume Y: "Y \<in> {X. X \<subseteq> A \<and> card X = k} - {X}"
        hence "X = Y" if "monom_of_set X = monom_of_set Y"
          using that finite_subset[OF X(1)] finite_subset[of Y A] \<open>finite A\<close> by auto
        thus "coeff (monom (monom_of_set Y) 1) m = 0"
          using X Y by (auto simp: coeff_monom when_def )
      qed (insert X \<open>finite A\<close>, auto simp: coeff_monom)
      thus ?thesis using \<open>finite A\<close> by (auto simp: coeff_sym_mpoly coeff_sum coeff_monom)
    qed
  qed
qed

lemma coeff_sym_mpoly_monom_of_set [simp]:
  assumes "finite X" "Y \<subseteq> X" "card Y = k"
  shows   "MPoly_Type.coeff (sym_mpoly X k) (monom_of_set Y) = 1"
  using assms by (auto simp: coeff_sym_mpoly)

lemma coeff_sym_mpoly_0: "coeff (sym_mpoly X k) 0 = (if finite X \<and> k = 0 then 1 else 0)"
proof -
  consider "finite X" "k = 0" | "finite X" "k \<noteq> 0" | "infinite X" by blast
  thus ?thesis
  proof cases
    assume "finite X" "k = 0"
    hence "coeff (sym_mpoly X k) (monom_of_set {}) = 1"
      by (subst coeff_sym_mpoly_monom_of_set) auto
    thus ?thesis unfolding monom_of_set_empty using \<open>finite X\<close> \<open>k = 0\<close> by simp
  next
    assume "finite X" "k \<noteq> 0"
    hence "\<not>(\<exists>Y. finite Y \<and> Y \<subseteq> X \<and> card Y = k \<and> monom_of_set Y = 0)"
      by auto
    thus ?thesis using \<open>k \<noteq> 0\<close>
      by (auto simp: coeff_sym_mpoly)
  next
    assume "infinite X"
    thus ?thesis by (simp add: coeff_sym_mpoly)
  qed
qed

lemma symmetric_sym_mpoly [intro]:
  assumes "A \<subseteq> B"
  shows   "symmetric_mpoly A (sym_mpoly B k :: 'a :: zero_neq_one mpoly)"
  unfolding symmetric_mpoly_def
proof (safe intro!: mpoly_eqI)
  fix \<pi> and mon :: "nat \<Rightarrow>\<^sub>0 nat" assume \<pi>: "\<pi> permutes A"
  from \<pi> have \<pi>': "\<pi> permutes B" by (rule permutes_subset) fact
  from \<pi> have "MPoly_Type.coeff (mpoly_map_vars \<pi> (sym_mpoly B k :: 'a mpoly)) mon =
                 MPoly_Type.coeff (sym_mpoly B k :: 'a mpoly) (permutep \<pi> mon)"
    by (simp add: coeff_mpoly_map_vars permutes_bij)
  also have "\<dots> = 1 \<longleftrightarrow> MPoly_Type.coeff (sym_mpoly B k :: 'a mpoly) mon = 1"
    (is "?lhs = 1 \<longleftrightarrow> ?rhs = 1")
  proof
    assume "?rhs = 1"
    then obtain Y where "finite B" and Y: "Y \<subseteq> B" "card Y = k" "mon = monom_of_set Y"
      by (auto simp: coeff_sym_mpoly split: if_splits)
    with \<pi>' have "\<pi> -` Y \<subseteq> B" "card (\<pi> -` Y) = k" "permutep \<pi> mon = monom_of_set (\<pi> -` Y)"
      by (auto simp: permutes_in_image card_vimage_inj permutep_monom_of_set
                     permutes_bij permutes_inj permutes_surj)
    thus "?lhs = 1" using \<open>finite B\<close> by (auto simp: coeff_sym_mpoly)
  next
    assume "?lhs = 1"
    then obtain Y where "finite B" and Y: "Y \<subseteq> B" "card Y = k" "permutep \<pi> mon = monom_of_set Y"
      by (auto simp: coeff_sym_mpoly split: if_splits)
    from Y(1) have "inj_on \<pi> Y" using inj_on_subset[of \<pi> UNIV Y] \<pi>'
      by (auto simp: permutes_inj)
    with Y \<pi>' have "\<pi> ` Y \<subseteq> B" "card (\<pi> ` Y) = k" "mon = monom_of_set (\<pi> ` Y)"
      by (auto simp: permutes_in_image card_image permutep_monom_of_set
               permutes_bij permutes_inj permutes_surj)
    thus "?rhs = 1" using \<open>finite B\<close> by (auto simp: coeff_sym_mpoly)
  qed
  hence "?lhs = ?rhs"
    by (auto simp: coeff_sym_mpoly split: if_splits)
  finally show "MPoly_Type.coeff (mpoly_map_vars \<pi> (sym_mpoly B k :: 'a mpoly)) mon =
                  MPoly_Type.coeff (sym_mpoly B k :: 'a mpoly) mon" .
qed

lemma insertion_sym_mpoly:
  assumes "finite X"
  shows   "insertion f (sym_mpoly X k) = (\<Sum>Y | Y \<subseteq> X \<and> card Y = k. prod f Y)"
  using assms
proof (transfer, transfer)
  fix f :: "nat \<Rightarrow> 'a" and k :: nat and X :: "nat set"
  assume X: "finite X"
  have "insertion_fun f (\<lambda>mon.
            if finite X \<and> (\<exists>Y\<subseteq>X. card Y = k \<and> mon = monom_of_set Y) then 1 else 0) =
        (\<Sum>m. (\<Prod>v. f v ^ poly_mapping.lookup m v) when (\<exists>Y\<subseteq>X. card Y = k \<and> m = monom_of_set Y))"
    by (auto simp add: insertion_fun_def X when_def intro!: Sum_any.cong)
  also have "\<dots> = (\<Sum>m | \<exists>Y\<in>Pow X. card Y = k \<and> m = monom_of_set Y. (\<Prod>v. f v ^ poly_mapping.lookup m v) when (\<exists>Y\<subseteq>X. card Y = k \<and> m = monom_of_set Y))"
    by (rule Sum_any.expand_superset) (use X in auto)
  also have "\<dots> = (\<Sum>m | \<exists>Y\<in>Pow X. card Y = k \<and> m = monom_of_set Y. (\<Prod>v. f v ^ poly_mapping.lookup m v))"
    by (intro sum.cong) (auto simp: when_def)
  also have "\<dots> = (\<Sum>Y | Y \<subseteq> X \<and> card Y = k. (\<Prod>v. f v ^ poly_mapping.lookup (monom_of_set Y) v))"
    by (rule sum.reindex_bij_witness[of _ monom_of_set keys]) (auto simp: finite_subset[OF _ X])
  also have "\<dots> = (\<Sum>Y | Y \<subseteq> X \<and> card Y = k. \<Prod>v\<in>Y. f v)"
  proof (intro sum.cong when_cong refl, goal_cases)
    case (1 Y)
    hence "finite Y" by (auto dest: finite_subset[OF _ X])
    with 1 have "(\<Prod>v. f v ^ poly_mapping.lookup (monom_of_set Y) v) =
                   (\<Prod>v::nat. if v \<in> Y then f v else 1)"
      by (intro Prod_any.cong) (auto simp: lookup_monom_of_set)
    also have "\<dots> = (\<Prod>v\<in>Y. f v)"
      by (rule Prod_any.conditionalize [symmetric]) fact+
    finally show ?case .
  qed
  finally show "insertion_fun f
                   (\<lambda>mon. if finite X \<and> (\<exists>Y\<subseteq>X. card Y = k \<and> mon = monom_of_set Y) then 1 else 0) =
                 (\<Sum>Y | Y \<subseteq> X \<and> card Y = k. prod f Y)" .
qed

lemma sym_mpoly_nz [simp]:
  assumes "finite A" "k \<le> card A"
  shows   "sym_mpoly A k \<noteq> (0 :: 'a :: zero_neq_one mpoly)"
proof -
  from assms obtain B where B: "B \<subseteq> A" "card B = k"
    using ex_subset_of_card by blast
  with assms have "coeff (sym_mpoly A k :: 'a mpoly) (monom_of_set B) = 1"
    by (intro coeff_sym_mpoly_monom_of_set)
  thus ?thesis by auto
qed

lemma coeff_sym_mpoly_0_or_1: "coeff (sym_mpoly A k) m \<in> {0, 1}"
  by (transfer, transfer) auto

lemma lead_coeff_sym_mpoly [simp]:
  assumes "finite A" "k \<le> card A"
  shows   "lead_coeff (sym_mpoly A k) = 1"
proof -
  from assms have "lead_coeff (sym_mpoly A k) \<noteq> 0" by simp
  thus ?thesis using coeff_sym_mpoly_0_or_1[of A k "lead_monom (sym_mpoly A k)"]
    unfolding lead_coeff_def by blast
qed

lemma lead_monom_sym_mpoly:
  assumes "sorted xs" "distinct xs" "k \<le> length xs"
  shows   "lead_monom (sym_mpoly (set xs) k :: 'a :: zero_neq_one mpoly) =
             monom_of_set (set (take k xs))" (is "lead_monom ?p = _")
proof -
  let ?m = "lead_monom ?p"
  have sym: "symmetric_mpoly (set xs) (sym_mpoly (set xs) k)"
    by (intro symmetric_sym_mpoly) auto
  from assms have [simp]: "card (set xs) = length xs"
    by (subst distinct_card) auto
  from assms have "lead_coeff ?p = 1"
    by (subst lead_coeff_sym_mpoly) auto
  then obtain X where X: "X \<subseteq> set xs" "card X = k" "?m = monom_of_set X"
    unfolding lead_coeff_def by (subst (asm) coeff_sym_mpoly) (auto split: if_splits)
  define ys where "ys = map (\<lambda>x. if x \<in> X then 1 else 0 :: nat) xs"
  have [simp]: "length ys = length xs" by (simp add: ys_def)

  have ys_altdef: "ys = map (lookup ?m) xs"
    unfolding ys_def using X finite_subset[OF X(1)]
    by (intro map_cong) (auto simp: lookup_monom_of_set)

  define i where "i = Min (insert (length xs) {i. i < length xs \<and> ys ! i = 0})"
  have "i \<le> length xs" by (auto simp: i_def)
  have in_X: "xs ! j \<in> X" if "j < i" for j
    using that unfolding i_def by (auto simp: ys_def)
  have not_in_X: "xs ! j \<notin> X" if "i \<le> j" "j < length xs" for j
  proof -
    have ne: "{i. i < length xs \<and> ys ! i = 0} \<noteq> {}"
    proof
      assume [simp]: "{i. i < length xs \<and> ys ! i = 0} = {}"
      from that show False by (simp add: i_def)
    qed
    hence "Min {i. i < length xs \<and> ys ! i = 0} \<in> {i. i < length xs \<and> ys ! i = 0}"
      using that by (intro Min_in) auto
    also have "Min {i. i < length xs \<and> ys ! i = 0} = i"
      unfolding i_def using ne by (subst Min_insert) (auto simp: min_def)
    finally have i: "ys ! i = 0" "i < length xs" by simp_all

    have "lookup ?m (xs ! j) \<le> lookup ?m (xs ! i)" using that assms
      by (intro lookup_lead_monom_decreasing[OF sym])
         (auto intro!: sorted_nth_mono simp: set_conv_nth)
    also have "\<dots> = 0" using i by (simp add: ys_altdef)
    finally show ?thesis using that X finite_subset[OF X(1)] by (auto simp: lookup_monom_of_set)
  qed

  from X have "k = card X"
    by simp
  also have "X = (\<lambda>i. xs ! i) ` {i. i < length xs \<and> xs ! i \<in> X}"
    using X by (auto simp: set_conv_nth)
  also have "card \<dots> = (\<Sum>i | i < length xs \<and> xs ! i \<in> X. 1)"
    using assms by (subst card_image) (auto intro!: inj_on_nth)
  also have "\<dots> = (\<Sum>i | i < length xs. if xs ! i \<in> X then 1 else 0)"
    by (intro sum.mono_neutral_cong_left) auto
  also have "\<dots> = sum_list ys"
    by (auto simp: sum_list_sum_nth ys_def intro!: sum.cong)
  also have "ys = take i ys @ drop i ys" by simp
  also have "sum_list \<dots> = sum_list (take i ys) + sum_list (drop i ys)"
    by (subst sum_list_append) auto
  also have "take i ys = replicate i 1" using \<open>i \<le> length xs\<close> in_X
    by (intro replicate_eqI) (auto simp: ys_def set_conv_nth)
  also have "sum_list \<dots> = i" by simp
  also have "drop i ys = replicate (length ys - i) 0" using \<open>i \<le> length xs\<close> not_in_X
    by (intro replicate_eqI) (auto simp: ys_def set_conv_nth)
  also have "sum_list \<dots> = 0" by simp
  finally have "i = k" by simp

  have "X = set (filter (\<lambda>x. x \<in> X) xs)"
    using X by auto
  also have "xs = take i xs @ drop i xs" by simp
  also note filter_append
  also have "filter (\<lambda>x. x \<in> X) (take i xs) = take i xs"
    using in_X by (intro filter_True) (auto simp: set_conv_nth)
  also have "filter (\<lambda>x. x \<in> X) (drop i xs) = []"
    using not_in_X by (intro filter_False) (auto simp: set_conv_nth)
  finally have "X = set (take i xs)" by simp
  with \<open>i = k\<close> and X show ?thesis by simp
qed


subsection \<open>Induction on the leading monomial\<close>

text \<open>
  We show that the monomial ordering for a fixed set of variables is well-founded,
  so we can perform induction on the leading monomial of a polynomial.
\<close>
definition monom_less_on where
  "monom_less_on A = {(m1, m2). m1 < m2 \<and> keys m1 \<subseteq> A \<and> keys m2 \<subseteq> A}"

lemma wf_monom_less_on:
  assumes "finite A"
  shows   "wf (monom_less_on A :: ((nat \<Rightarrow>\<^sub>0 'b :: {zero, wellorder}) \<times> _) set)"
proof (rule wf_subset)
  define n where "n = Suc (Max (insert 0 A))"
  have less_n: "k < n" if "k \<in> A" for k
    using that assms by (auto simp: n_def less_Suc_eq_le Max_ge_iff)

  define f :: "(nat \<Rightarrow>\<^sub>0 'b) \<Rightarrow> 'b list" where "f = (\<lambda>m. map (lookup m) [0..<n])"

  show "wf (inv_image (lexn {(x,y). x < y} n) f)"
    by (intro wf_inv_image wf_lexn wellorder_class.wf)
  show "monom_less_on A \<subseteq> inv_image (lexn {(x, y). x < y} n) f"
  proof safe
    fix m1 m2 :: "nat \<Rightarrow>\<^sub>0 'b" assume "(m1, m2) \<in> monom_less_on A"
    hence m12: "m1 < m2" "keys m1 \<subseteq> A" "keys m2 \<subseteq> A"
      by (auto simp: monom_less_on_def)
    then obtain k where k: "lookup m1 k < lookup m2 k" "\<forall>i<k. lookup m1 i = lookup m2 i"
      by (auto simp: less_poly_mapping_def less_fun_def)
    have "\<not>(lookup m1 k = 0 \<and> lookup m2 k = 0)"
    proof (intro notI)
      assume "lookup m1 k = 0 \<and> lookup m2 k = 0"
      hence [simp]: "lookup m1 k = 0" "lookup m2 k = 0" by blast+
      from k(1) show False by simp
    qed
    hence "k \<in> A" using m12 by (auto simp: in_keys_iff)
    hence "k < n" by (simp add: less_n)

    define as where "as = map (lookup m1) [0..<k]"
    define bs1 where "bs1 = map (lookup m1) [Suc k..<n]"
    define bs2 where "bs2 = map (lookup m2) [Suc k..<n]"
    have decomp: "[0..<n] = [0..<k] @ [k] @ drop (Suc k) [0..<n]"
      using \<open>k < n\<close> by (simp flip: upt_conv_Cons upt_add_eq_append')
    have [simp]: "length as = k" "length bs1 = n - Suc k" "length bs2 = n - Suc k"
      by (simp_all add: as_def bs1_def bs2_def)

    have "f m1 = as @ [lookup m1 k] @ bs1" unfolding f_def
      by (subst decomp) (simp add: as_def bs1_def)
    moreover have "f m2 = as @ [lookup m2 k] @ bs2" unfolding f_def
      using k by (subst decomp) (simp add: as_def bs2_def)
    ultimately show "(m1, m2) \<in> inv_image (lexn {(x,y). x < y} n) f"
      using k(1) \<open>k < n\<close> unfolding lexn_conv by auto
  qed
qed

lemma lead_monom_induct [consumes 2, case_names less]:
  fixes p :: "'a :: zero mpoly"
  assumes fin: "finite A" and vars: "vars p \<subseteq> A"
  assumes IH: "\<And>p. vars p \<subseteq> A \<Longrightarrow>
                 (\<And>p'. vars p' \<subseteq> A \<Longrightarrow> lead_monom p' < lead_monom p \<Longrightarrow> P p') \<Longrightarrow> P p"
  shows   "P p"
  using assms(2)
proof (induct m \<equiv> "lead_monom p" arbitrary: p rule: wf_induct_rule[OF wf_monom_less_on[OF fin]])
  case (1 p)
  show ?case
  proof (rule IH)
    fix p' :: "'a mpoly" assume *: "vars p' \<subseteq> A" "lead_monom p' < lead_monom p"
    show "P p'"
      by (rule 1) (insert * "1.prems" keys_lead_monom_subset, auto simp: monom_less_on_def)
  qed (insert 1, auto)
qed

lemma lead_monom_induct' [case_names less]:
  fixes p :: "'a :: zero mpoly"
  assumes IH: "\<And>p. (\<And>p'. vars p' \<subseteq> vars p \<Longrightarrow> lead_monom p' < lead_monom p \<Longrightarrow> P p') \<Longrightarrow> P p"
  shows   "P p"
proof -
  have "finite (vars p)" "vars p \<subseteq> vars p" by (auto simp: vars_finite)
  thus ?thesis
    by (induction rule: lead_monom_induct) (use IH in blast)
qed



subsection \<open>The fundamental theorem of symmetric polynomials\<close>

lemma lead_coeff_sym_mpoly_powerprod:
  assumes "finite A" "\<And>x. x \<in> X \<Longrightarrow> f x \<in> {1..card A}"
  shows   "lead_coeff (\<Prod>x\<in>X. sym_mpoly A (f (x::'a)) ^ g x) = 1"
proof -
  have eq: "lead_coeff (sym_mpoly A (f x) ^ g x :: 'b mpoly) = 1" if "x \<in> X" for x
    using that assms by (subst lead_coeff_power) (auto simp: lead_coeff_sym_mpoly assms)
  hence "(\<Prod>x\<in>X. lead_coeff (sym_mpoly A (f x) ^ g x :: 'b mpoly)) = (\<Prod>x\<in>X. 1)"
    by (intro prod.cong eq refl)
  also have "\<dots> = 1" by simp
  finally have eq': "(\<Prod>x\<in>X. lead_coeff (sym_mpoly A (f x) ^ g x :: 'b mpoly)) = 1" .
  show ?thesis by (subst lead_coeff_prod) (auto simp: eq eq')
qed

context
  fixes A :: "nat set" and xs n f and decr :: "'a :: comm_ring_1 mpoly \<Rightarrow> bool"
  defines "xs \<equiv> sorted_list_of_set A"
  defines "n \<equiv> card A"
  defines "f \<equiv> (\<lambda>i. if i < n then xs ! i else 0)"
  defines "decr \<equiv> (\<lambda>p. \<forall>i\<in>A. \<forall>j\<in>A. i \<le> j \<longrightarrow>
                   lookup (lead_monom p) i \<ge> lookup (lead_monom p) j)"
begin

text \<open>
  The computation of the witness for the fundamental theorem works like this:
  Given some polynomial $p$ (that is assumed to be symmetric in the variables in $A$),
  we inspect its leading monomial, which is of the form $c X_1^{i_1}\ldots X_n{i_n}$ where
  the $A = \{X_1,\ldots, X_n\}$, $c$ contains only variables not in $A$, and the sequence $i_j$
  is decreasing. The latter holds because $p$ is symmetric.

  Now, we form the polynomial $q := c e_1^{i_1 - i_2} e_2^{i_2 - i_3} \ldots e_n^{i_n}$, which
  has the same leading term as $p$. Then $p - q$ has a smaller leading monomial, so by induction,
  we can assume it to be of the required form and obtain a witness for $p - q$.

  Now, we only need to add $c Y_1^{i_1 - i_2} \ldots Y_n^{i_n}$ to that witness and we
  obtain a witness for $p$.
\<close>
definition fund_sym_step_coeff :: "'a mpoly \<Rightarrow> 'a mpoly" where
  "fund_sym_step_coeff p = monom (restrictpm (-A) (lead_monom p)) (lead_coeff p)"

definition fund_sym_step_monom :: "'a mpoly \<Rightarrow> (nat \<Rightarrow>\<^sub>0 nat)" where
  "fund_sym_step_monom p = (
     let g = (\<lambda>i. if i < n then lookup (lead_monom p) (f i) else 0)
     in  (\<Sum>i<n. Poly_Mapping.single (Suc i) (g i - g (Suc i))))"

definition fund_sym_step_poly :: "'a mpoly \<Rightarrow> 'a mpoly" where
  "fund_sym_step_poly p = (
      let g = (\<lambda>i. if i < n then lookup (lead_monom p) (f i) else 0)
      in  fund_sym_step_coeff p * (\<Prod>i<n. sym_mpoly A (Suc i) ^ (g i - g (Suc i))))"

text \<open>
  The following function computes the witness, with the convention that it returns a constant
  polynomial if the input was not symmetric:
\<close>
function (domintros) fund_sym_poly_wit :: "'a :: comm_ring_1 mpoly \<Rightarrow> 'a mpoly mpoly" where
  "fund_sym_poly_wit p =
     (if \<not>symmetric_mpoly A p \<or> lead_monom p = 0 \<or> vars p \<inter> A = {} then Const p else
        fund_sym_poly_wit (p - fund_sym_step_poly p) +
        monom (fund_sym_step_monom p) (fund_sym_step_coeff p))"
  by auto

lemma coeff_fund_sym_step_coeff: "coeff (fund_sym_step_coeff p) m \<in> {lead_coeff p, 0}"
  by (auto simp: fund_sym_step_coeff_def coeff_monom when_def)

lemma vars_fund_sym_step_coeff: "vars (fund_sym_step_coeff p) \<subseteq> vars p - A"
  unfolding fund_sym_step_coeff_def using keys_lead_monom_subset[of p]
  by (intro order.trans[OF vars_monom_subset]) auto

lemma keys_fund_sym_step_monom: "keys (fund_sym_step_monom p) \<subseteq> {1..n}"
  unfolding fund_sym_step_monom_def Let_def
  by (intro order.trans[OF keys_sum] UN_least, subst keys_single) auto

lemma coeff_fund_sym_step_poly:
  assumes C: "\<forall>m. coeff p m \<in> C" and "ring_closed C"
  shows   "coeff (fund_sym_step_poly p) m \<in> C"
proof -
  interpret ring_closed C by fact
  have *: "\<And>m. coeff (p ^ x) m \<in> C" if "\<And>m. coeff p m \<in> C"  for p x
    using that by (induction x)
                  (auto simp: coeff_mpoly_times mpoly_coeff_1 intro!: prod_fun_closed)
  have **: "\<And>m. coeff (prod f X) m \<in> C" if "\<And>i m. i \<in> X \<Longrightarrow> coeff (f i) m \<in> C"
    for X and f :: "nat \<Rightarrow> _"
    using that by (induction X rule: infinite_finite_induct)
                  (auto simp: coeff_mpoly_times mpoly_coeff_1 intro!: prod_fun_closed)
  show ?thesis using C
    unfolding fund_sym_step_poly_def Let_def fund_sym_step_coeff_def coeff_mpoly_times
    by (intro prod_fun_closed)
       (auto simp: coeff_monom when_def lead_coeff_def coeff_sym_mpoly intro!: * **)
qed

text \<open>
  We now show various relevant properties of the subtracted polynomial:

    \<^enum> Its leading term is the same as that of the input polynomial.

    \<^enum> It contains now new variables.

    \<^enum> It is symmetric in the variables in \<open>A\<close>.
\<close>
lemma fund_sym_step_poly:
  shows   "finite A \<Longrightarrow> p \<noteq> 0 \<Longrightarrow> decr p \<Longrightarrow> lead_monom (fund_sym_step_poly p) = lead_monom p"
    and   "finite A \<Longrightarrow> p \<noteq> 0 \<Longrightarrow> decr p \<Longrightarrow> lead_coeff (fund_sym_step_poly p) = lead_coeff p"
    and   "finite A \<Longrightarrow> p \<noteq> 0 \<Longrightarrow> decr p \<Longrightarrow> fund_sym_step_poly p =
             fund_sym_step_coeff p * (\<Prod>x. sym_mpoly A x ^ lookup (fund_sym_step_monom p) x)"
    and   "vars (fund_sym_step_poly p) \<subseteq> vars p \<union> A"
    and   "symmetric_mpoly A (fund_sym_step_poly p)"
proof -
  define g where "g = (\<lambda>i. if i < n then lookup (lead_monom p) (f i) else 0)"
  define q where "q = (\<Prod>i<n. sym_mpoly A (Suc i) ^ (g i - g (Suc i)) :: 'a mpoly)"
  define c where "c = monom (restrictpm (-A) (lead_monom p)) (lead_coeff p)"
  have [simp]: "fund_sym_step_poly p = c * q"
    by (simp add: fund_sym_step_poly_def fund_sym_step_coeff_def c_def q_def f_def g_def)

  have "vars (c * q) \<subseteq> vars p \<union> A"
    using keys_lead_monom_subset[of p]
          vars_monom_subset[of "restrictpm (-A) (lead_monom p)" "lead_coeff p"]
    unfolding c_def q_def
    by (intro order.trans[OF vars_mult] order.trans[OF vars_prod] order.trans[OF vars_power]
              Un_least UN_least order.trans[OF vars_sym_mpoly_subset]) auto
  thus "vars (fund_sym_step_poly p) \<subseteq> vars p \<union> A"
    by simp
  have "symmetric_mpoly A (c * q)" unfolding c_def q_def
    by (intro symmetric_mpoly_mult symmetric_mpoly_monom symmetric_mpoly_prod
              symmetric_mpoly_power symmetric_sym_mpoly) auto
  thus "symmetric_mpoly A (fund_sym_step_poly p)" by simp

  assume finite: "finite A" and [simp]: "p \<noteq> 0" and "decr p"
  have "set xs = A" "distinct xs" and [simp]: "length xs = n"
    using finite by (auto simp: xs_def n_def)
  have [simp]: "lead_coeff c = lead_coeff p" "lead_monom c = restrictpm (- A) (lead_monom p)"
    by (simp_all add: c_def lead_monom_monom)
  hence f_range [simp]: "f i \<in> A" if "i < n" for i
    using that \<open>set xs = A\<close> by (auto simp: f_def set_conv_nth)
  have "sorted xs" by (simp add: xs_def)
  hence f_mono: "f i \<le> f j" if "i \<le> j" "j < n" for i j using that
    by (auto simp: f_def n_def intro: sorted_nth_mono)
  hence g_mono: "g i \<ge> g j" if "i \<le> j" for i j
    unfolding g_def using that using \<open>decr p\<close> by (auto simp: decr_def)

  have *: "(\<Prod>i<n. lead_coeff (sym_mpoly A (Suc i) ^ (g i - g (Suc i)) :: 'a mpoly)) =
              (\<Prod>i<card A. 1)"
    using \<open>finite A\<close> by (intro prod.cong) (auto simp: n_def lead_coeff_power)
  hence "lead_coeff q = (\<Prod>i<n. lead_coeff (sym_mpoly A (Suc i) ^ (g i - g (Suc i)) :: 'a mpoly))"
    by (simp add: lead_coeff_prod lead_coeff_power n_def q_def)
  also have "\<dots> = (\<Prod>i<n. 1)"
    using \<open>finite A\<close> by (intro prod.cong) (auto simp: lead_coeff_power n_def)
  finally have [simp]: "lead_coeff q = 1" by simp

  have "lead_monom q = (\<Sum>i<n. lead_monom (sym_mpoly A (Suc i) ^ (g i - g (Suc i)) :: 'a mpoly))"
    using * by (simp add: q_def lead_monom_prod lead_coeff_power n_def)
  also have "\<dots> = (\<Sum>i<n. of_nat (g i - g (Suc i)) * lead_monom (sym_mpoly A (Suc i) :: 'a mpoly))"
    using \<open>finite A\<close> by (intro sum.cong) (auto simp: lead_monom_power n_def)
  also have "\<dots> = (\<Sum>i<n. of_nat (g i - g (Suc i)) * monom_of_set (set (take (Suc i) xs)))"
  proof (intro sum.cong refl, goal_cases)
    case (1 i)
    have "lead_monom (sym_mpoly A (Suc i) :: 'a mpoly) =
            lead_monom (sym_mpoly (set xs) (Suc i) :: 'a mpoly)"
      by (simp add: \<open>set xs = A\<close>)
    also from 1 have "\<dots> = monom_of_set (set (take (Suc i) xs))"
      by (subst lead_monom_sym_mpoly) (auto simp: xs_def n_def)
    finally show ?case by simp
  qed
  finally have lead_monom_q:
    "lead_monom q = (\<Sum>i<n. of_nat (g i - g (Suc i)) * monom_of_set (set (take (Suc i) xs)))" .

  have "lead_monom (c * q) = lead_monom c + lead_monom q"
    by (simp add: lead_monom_mult)
  also have "\<dots> = lead_monom p" (is "?S = _")
  proof (intro poly_mapping_eqI)
    fix i :: nat
    show "lookup (lead_monom c + lead_monom q) i = lookup (lead_monom p) i"
    proof (cases "i \<in> A")
      case False
      hence "lookup (lead_monom c + lead_monom q) i = lookup (lead_monom p) i +
               (\<Sum>j<n. (g j - g (Suc j)) * lookup (monom_of_set (set (take (Suc j) xs))) i)"
        (is "_ = _ + ?S") by (simp add: lookup_add lead_monom_q lookup_sum)
      also from False have "?S = 0"
        by (intro sum.neutral) (auto simp: lookup_monom_of_set \<open>set xs = A\<close> dest!: in_set_takeD)
      finally show ?thesis by simp
    next
      case True
      with \<open>set xs = A\<close> obtain m where m: "i = xs ! m" "m < n"
        by (auto simp: set_conv_nth)
      have "lookup (lead_monom c + lead_monom q) i =
              (\<Sum>j<n. (g j - g (Suc j)) * lookup (monom_of_set (set (take (Suc j) xs))) i)"
        using True by (simp add: lookup_add lookup_sum lead_monom_q)
      also have "\<dots> = (\<Sum>j | j < n \<and> i \<in> set (take (Suc j) xs). g j - g (Suc j))"
        by (intro sum.mono_neutral_cong_right) auto
      also have "{j. j < n \<and> i \<in> set (take (Suc j) xs)} = {m..<n}"
        using m \<open>distinct xs\<close> by (force simp: set_conv_nth nth_eq_iff_index_eq)
      also have "(\<Sum>j\<in>\<dots>. g j - g (Suc j)) = (\<Sum>j\<in>\<dots>. g j) - (\<Sum>j\<in>\<dots>. g (Suc j))"
        by (subst sum_subtractf_nat) (auto intro!: g_mono)
      also have "(\<Sum>j\<in>{m..<n}. g (Suc j)) = (\<Sum>j\<in>{m<..n}. g j)"
        by (intro sum.reindex_bij_witness[of _ "\<lambda>j. j - 1" Suc]) auto
      also have "\<dots> = (\<Sum>j\<in>{m<..<n}. g j)"
        by (intro sum.mono_neutral_right) (auto simp: g_def)
      also have "(\<Sum>j\<in>{m..<n}. g j) - \<dots> = (\<Sum>j\<in>{m..<n}-{m<..<n}. g j)"
        by (intro sum_diff_nat [symmetric]) auto
      also have "{m..<n}-{m<..<n} = {m}" using m by auto
      also have "(\<Sum>j\<in>\<dots>. g j) = lookup (lead_monom p) i"
        using m by (auto simp: g_def not_less le_Suc_eq f_def)
      finally show ?thesis .
    qed
  qed
  finally show "lead_monom (fund_sym_step_poly p) = lead_monom p" by simp
  show "lead_coeff (fund_sym_step_poly p) = lead_coeff p"
    by (simp add: lead_coeff_mult)

  have *: "lookup (fund_sym_step_monom p) k = (if k \<in> {1..n} then g (k - 1) - g k else 0)" for k
  proof -
    have "lookup (fund_sym_step_monom p) k =
            (\<Sum>x\<in>(if k \<in> {1..n} then {k - 1} else {}). g (k - 1) - g k)"
      unfolding fund_sym_step_monom_def lookup_sum Let_def
      by (intro sum.mono_neutral_cong_right)
         (auto simp: g_def lookup_single when_def split: if_splits)
    thus ?thesis by simp
  qed
  hence "(\<Prod>x. sym_mpoly A x ^ lookup (fund_sym_step_monom p) x :: 'a mpoly) =
           (\<Prod>x\<in>{1..n}. sym_mpoly A x ^ lookup (fund_sym_step_monom p) x)"
    by (intro Prod_any.expand_superset) auto
  also have "\<dots> = (\<Prod>x<n. sym_mpoly A (Suc x) ^ lookup (fund_sym_step_monom p) (Suc x))"
    by (intro prod.reindex_bij_witness[of _ Suc "\<lambda>i. i - 1"]) auto
  also have "\<dots> = q"
    unfolding q_def by (intro prod.cong) (auto simp: *)
  finally show "fund_sym_step_poly p =
                  fund_sym_step_coeff p * (\<Prod>x. sym_mpoly A x ^ lookup (fund_sym_step_monom p) x)"
    by (simp add: c_def q_def f_def g_def fund_sym_step_monom_def fund_sym_step_coeff_def)
qed

text \<open>
  If the input is well-formed, a single step of the procedure always decreases the leading
  monomial.
\<close>
lemma lead_monom_fund_sym_step_poly_less:
  assumes "finite A" and "lead_monom p \<noteq> 0" and "decr p"
  shows   "lead_monom (p - fund_sym_step_poly p) < lead_monom p"
proof (cases "p = fund_sym_step_poly p")
  case True
  thus ?thesis using assms by (auto simp: order.strict_iff_order)
next
  case False
  from assms have [simp]: "p \<noteq> 0" by auto
  let ?q = "fund_sym_step_poly p" and ?m = "lead_monom p"
  have "coeff (p - ?q) ?m = 0"
    using fund_sym_step_poly[of p] assms by (simp add: lead_coeff_def)
  moreover have "lead_coeff (p - ?q) \<noteq> 0" using False by auto
  ultimately have "lead_monom (p - ?q) \<noteq> ?m"
    unfolding lead_coeff_def by auto
  moreover have "lead_monom (p - ?q) \<le> ?m"
    using fund_sym_step_poly[of p] assms
    by (intro order.trans[OF lead_monom_diff] max.boundedI) auto
  ultimately show ?thesis by (auto simp: order.strict_iff_order)
qed

text \<open>
  Finally, we prove that the witness is indeed well-defined for all inputs.
\<close>
lemma fund_sym_poly_wit_dom_aux:
  assumes "finite B" "vars p \<subseteq> B" "A \<subseteq> B"
  shows   "fund_sym_poly_wit_dom p"
  using assms(1-3)
proof (induction p rule: lead_monom_induct)
  case (less p)
  have [simp]: "finite A"  by (rule finite_subset[of _ B]) fact+
  show ?case
  proof (cases "lead_monom p = 0 \<or> \<not>symmetric_mpoly A p")
    case False
    hence [simp]: "p \<noteq> 0" by auto
    note decr = lookup_lead_monom_decreasing[of A p]
    have "vars (p - fund_sym_step_poly p) \<subseteq> B"
      using fund_sym_step_poly[of p] decr False less.prems less.hyps \<open>A \<subseteq> B\<close>
      by (intro order.trans[OF vars_diff]) auto
    hence "fund_sym_poly_wit_dom (p - local.fund_sym_step_poly p)"
      using False less.prems less.hyps decr
      by (intro less.IH fund_sym_step_poly symmetric_mpoly_diff
                lead_monom_fund_sym_step_poly_less) (auto simp: decr_def)
    thus ?thesis using fund_sym_poly_wit.domintros by blast
  qed (auto intro: fund_sym_poly_wit.domintros)
qed

lemma fund_sym_poly_wit_dom [intro]: "fund_sym_poly_wit_dom p"
proof -
  consider "\<not>symmetric_mpoly A p" | "vars p \<inter> A = {}"  | "symmetric_mpoly A p" "A \<subseteq> vars p"
    using symmetric_mpoly_imp_orthogonal_or_subset[of A p] by blast
  thus ?thesis
  proof cases
    assume "symmetric_mpoly A p" "A \<subseteq> vars p"
    thus ?thesis using fund_sym_poly_wit_dom_aux[of "vars p" p] by (auto simp: vars_finite)
  qed (auto intro: fund_sym_poly_wit.domintros)
qed

termination fund_sym_poly_wit
  by (intro allI fund_sym_poly_wit_dom)

(*<*)
lemmas [simp del] = fund_sym_poly_wit.simps
(*>*)

text \<open>
  Next, we prove that our witness indeed fulfils all the properties stated by the fundamental
  theorem:
    \<^enum> If the original polynomial was in $R[X_1,\ldots,X_n,\ldots, X_m]$ where the $X_1$ to
      $X_n$ are the symmetric variables, then the witness is a polynomial in
      $R[X_{n+1},\ldots,X_m][Y_1,\ldots,Y_n]$. This means that its coefficients are polynomials
      in the variables of the original polynomial, minus the symmetric ones, and
      the (new and independent) variables of the witness polynomial range from $1$ to $n$.
    \<^enum> Substituting the \<open>i\<close>-th symmetric polynomial $e_i(X_1,\ldots,X_n)$ for the $Y_i$
      variable for every \<open>i\<close> yields the original polynomial.
    \<^enum> The coefficient ring $R$ need not be the entire type; if the coefficients of the original
      polynomial are in some subring, then the coefficients of the coefficients of the witness
      also do.
\<close>
lemma fund_sym_poly_wit_coeffs_aux:
  assumes "finite B" "vars p \<subseteq> B" "symmetric_mpoly A p" "A \<subseteq> B"
  shows   "vars (coeff (fund_sym_poly_wit p) m) \<subseteq> B - A"
  using assms
proof (induction p rule: fund_sym_poly_wit.induct)
  case (1 p)
  show ?case
  proof (cases "lead_monom p = 0 \<or> vars p \<inter> A = {}")
    case False
    have "vars (p - fund_sym_step_poly p) \<subseteq> B"
      using "1.prems" fund_sym_step_poly[of p] by (intro order.trans[OF vars_diff]) auto
    with 1 False have "vars (coeff (fund_sym_poly_wit (p - fund_sym_step_poly p)) m) \<subseteq> B - A"
      by (intro 1 symmetric_mpoly_diff fund_sym_step_poly) auto
    hence "vars (coeff (fund_sym_poly_wit (p - fund_sym_step_poly p) +
                monom (fund_sym_step_monom p) (fund_sym_step_coeff p)) m) \<subseteq> B - A"
      unfolding coeff_add coeff_monom using vars_fund_sym_step_coeff[of p] "1.prems"
      by (intro order.trans[OF vars_add] Un_least order.trans[OF vars_monom_subset])
         (auto simp: when_def)
    thus ?thesis using "1.prems" False unfolding fund_sym_poly_wit.simps[of p] by simp
  qed (insert "1.prems",
       auto simp: fund_sym_poly_wit.simps[of p] mpoly_coeff_Const lead_monom_eq_0_iff)
qed

lemma fund_sym_poly_wit_coeffs:
  assumes "symmetric_mpoly A p"
  shows   "vars (coeff (fund_sym_poly_wit p) m) \<subseteq> vars p - A"
proof (cases "A \<subseteq> vars p")
  case True
  with fund_sym_poly_wit_coeffs_aux[of "vars p" p m] assms
    show ?thesis by (auto simp: vars_finite)
next
  case False
  hence "vars p \<inter> A = {}"
    using symmetric_mpoly_imp_orthogonal_or_subset[OF assms] by auto
  thus ?thesis by (auto simp: fund_sym_poly_wit.simps[of p] mpoly_coeff_Const)
qed

lemma fund_sym_poly_wit_vars: "vars (fund_sym_poly_wit p) \<subseteq> {1..n}"
proof (cases "symmetric_mpoly A p \<and> A \<subseteq> vars p")
  case True
  define B where "B = vars p"
  have "finite B" "vars p \<subseteq> B" "symmetric_mpoly A p" "A \<subseteq> B"
    using True unfolding B_def by (auto simp: vars_finite)
  thus ?thesis
  proof (induction p rule: fund_sym_poly_wit.induct)
    case (1 p)
    show ?case
    proof (cases "lead_monom p = 0 \<or> vars p \<inter> A = {}")
      case False
      have "vars (p - fund_sym_step_poly p) \<subseteq> B"
        using "1.prems" fund_sym_step_poly[of p] by (intro order.trans[OF vars_diff]) auto
      hence "vars (local.fund_sym_poly_wit (p - local.fund_sym_step_poly p)) \<subseteq> {1..n}"
        using False "1.prems"
        by (intro 1 symmetric_mpoly_diff fund_sym_step_poly) (auto simp: lead_monom_eq_0_iff)
      hence "vars (fund_sym_poly_wit (p - fund_sym_step_poly p) +
              monom (fund_sym_step_monom p) (local.fund_sym_step_coeff p)) \<subseteq> {1..n}"
        by (intro order.trans[OF vars_add] Un_least order.trans[OF vars_monom_subset]
                  keys_fund_sym_step_monom) auto
      thus ?thesis using "1.prems" False unfolding fund_sym_poly_wit.simps[of p] by simp
    qed (insert "1.prems",
         auto simp: fund_sym_poly_wit.simps[of p] mpoly_coeff_Const lead_monom_eq_0_iff)
  qed
next
  case False
  then consider "\<not>symmetric_mpoly A p" | "symmetric_mpoly A p" "vars p \<inter> A = {}"
    using symmetric_mpoly_imp_orthogonal_or_subset[of A p] by auto
  thus ?thesis
    by cases (auto simp: fund_sym_poly_wit.simps[of p])
qed

lemma fund_sym_poly_wit_insertion_aux:
  assumes "finite B" "vars p \<subseteq> B" "symmetric_mpoly A p" "A \<subseteq> B"
  shows   "insertion (sym_mpoly A) (fund_sym_poly_wit p) = p"
  using assms
proof (induction p rule: fund_sym_poly_wit.induct)
  case (1 p)
  from "1.prems" have "decr p"
    using lookup_lead_monom_decreasing[of A p] by (auto simp: decr_def)
  show ?case
  proof (cases "lead_monom p = 0 \<or> vars p \<inter> A = {}")
    case False
    have "vars (p - fund_sym_step_poly p) \<subseteq> B"
      using "1.prems" fund_sym_step_poly[of p] by (intro order.trans[OF vars_diff]) auto
    hence "insertion (sym_mpoly A) (fund_sym_poly_wit (p - fund_sym_step_poly p)) =
            p - fund_sym_step_poly p" using 1 False
      by (intro 1 symmetric_mpoly_diff fund_sym_step_poly) auto
    moreover have "fund_sym_step_poly p =
                    fund_sym_step_coeff p * (\<Prod>x. sym_mpoly A x ^ lookup (fund_sym_step_monom p) x)"
      using "1.prems" finite_subset[of A B] False \<open>decr p\<close> by (intro fund_sym_step_poly) auto
    ultimately show ?thesis
      unfolding fund_sym_poly_wit.simps[of p] by (auto simp: insertion_add)
  qed (auto simp: fund_sym_poly_wit.simps[of p])
qed

lemma fund_sym_poly_wit_insertion:
  assumes "symmetric_mpoly A p"
  shows   "insertion (sym_mpoly A) (fund_sym_poly_wit p) = p"
proof (cases "A \<subseteq> vars p")
  case False
  hence "vars p \<inter> A = {}"
    using symmetric_mpoly_imp_orthogonal_or_subset[OF assms] by auto
  thus ?thesis
    by (auto simp: fund_sym_poly_wit.simps[of p])
next
  case True
  with fund_sym_poly_wit_insertion_aux[of "vars p" p] assms show ?thesis
    by (auto simp: vars_finite)
qed

lemma fund_sym_poly_wit_coeff:
  assumes "\<forall>m. coeff p m \<in> C" "ring_closed C"
  shows   "\<forall>m m'. coeff (coeff (fund_sym_poly_wit p) m) m' \<in> C"
  using assms(1)
proof (induction p rule: fund_sym_poly_wit.induct)
  case (1 p)
  interpret ring_closed C by fact
  show ?case
  proof (cases "\<not>symmetric_mpoly A p \<or> lead_monom p = 0 \<or> vars p \<inter> A = {}")
    case True
    thus ?thesis using "1.prems"
      by (auto simp: fund_sym_poly_wit.simps[of p] mpoly_coeff_Const)
  next
    case False
    have *: "\<forall>m m'. coeff (coeff (fund_sym_poly_wit (p - fund_sym_step_poly p)) m) m' \<in> C"
      using False "1.prems" assms coeff_fund_sym_step_poly [of p] by (intro 1) auto
    show ?thesis
    proof (intro allI, goal_cases)
      case (1 m m')
      thus ?case using * False coeff_fund_sym_step_coeff[of p m'] "1.prems"
        by (auto simp: fund_sym_poly_wit.simps[of p] coeff_monom lead_coeff_def when_def)
    qed
  qed
qed


subsection \<open>Uniqueness\<close>

text \<open>
  Next, we show that the polynomial representation of a symmetric polynomial in terms of the
  elementary symmetric polynomials not only exists, but is unique.

  The key property here is that products of powers of elementary symmetric polynomials uniquely
  determine the exponent vectors, i.\,e.\ if $e_1, \ldots, e_n$ are the elementary symmetric
  polynomials, $a = (a_1,\ldots, a_n)$ and $b = (b_1,\ldots,b_n)$ are vectors of natural numbers,
  then:
  \[e_1^{a_1}\ldots e_n^{a_n} = e_1^{b_1}\ldots  e_n^{b_n} \longleftrightarrow a = b\]
  We show this now.
\<close>
lemma lead_monom_sym_mpoly_prod:
  assumes "finite A"
  shows   "lead_monom (\<Prod>i = 1..n. sym_mpoly A i ^ h i :: 'a mpoly) =
             (\<Sum>i = 1..n. of_nat (h i) * lead_monom (sym_mpoly A i :: 'a mpoly))"
proof -
  have "(\<Prod>i=1..n. lead_coeff (sym_mpoly A i ^ h i :: 'a mpoly)) = 1"
    using assms unfolding n_def by (intro prod.neutral allI) (auto simp: lead_coeff_power)
  hence "lead_monom (\<Prod>i=1..n. sym_mpoly A i ^ h i :: 'a mpoly) =
           (\<Sum>i=1..n. lead_monom (sym_mpoly A i ^ h i :: 'a mpoly))"
    by (subst lead_monom_prod) auto
  also have "\<dots> = (\<Sum>i=1..n. of_nat (h i) * lead_monom (sym_mpoly A i :: 'a mpoly))"
    by (intro sum.cong refl, subst lead_monom_power)
       (auto simp: lead_coeff_power assms n_def)
  finally show ?thesis .
qed

lemma lead_monom_sym_mpoly_prod_notin:
  assumes "finite A" "k \<notin> A"
  shows   "lookup (lead_monom (\<Prod>i=1..n. sym_mpoly A i ^ h i :: 'a mpoly)) k = 0"
proof -
  have xs: "set xs = A" "distinct xs" "sorted xs" and [simp]: "length xs = n"
    using assms by (auto simp: xs_def n_def)
  have "lead_monom (\<Prod>i = 1..n. sym_mpoly A i ^ h i :: 'a mpoly) =
          (\<Sum>i = 1..n. of_nat (h i) * lead_monom (sym_mpoly (set xs) i :: 'a mpoly))"
    by (subst lead_monom_sym_mpoly_prod) (use xs assms in auto)
  also have "lookup \<dots> k = 0" unfolding lookup_sum
    by (intro sum.neutral ballI, subst lead_monom_sym_mpoly)
      (insert xs assms, auto simp: xs lead_monom_sym_mpoly lookup_monom_of_set set_conv_nth)
  finally show ?thesis .
qed

lemma lead_monom_sym_mpoly_prod_in:
  assumes "finite A" "k < n"
  shows   "lookup (lead_monom (\<Prod>i=1..n. sym_mpoly A i ^ h i :: 'a mpoly)) (xs ! k) =
             (\<Sum>i=k+1..n. h i)"
proof -
  have xs: "set xs = A" "distinct xs" "sorted xs" and [simp]: "length xs = n"
    using assms by (auto simp: xs_def n_def)
  have "lead_monom (\<Prod>i = 1..n. sym_mpoly A i ^ h i :: 'a mpoly) =
             (\<Sum>i = 1..n. of_nat (h i) * lead_monom (sym_mpoly (set xs) i :: 'a mpoly))"
    by (subst lead_monom_sym_mpoly_prod) (use xs assms in simp_all)
  also have "\<dots> = (\<Sum>i=1..n. of_nat (h i) * monom_of_set (set (take i xs)))"
    using xs by (intro sum.cong refl, subst lead_monom_sym_mpoly) auto
  also have "lookup \<dots> (xs ! k) = (\<Sum>i | i \<in> {1..n} \<and> xs ! k \<in> set (take i xs). h i)"
    unfolding lookup_sum lookup_monom_of_set by (intro sum.mono_neutral_cong_right) auto
  also have "{i. i \<in> {1..n} \<and> xs ! k \<in> set (take i xs)} = {k+1..n}"
  proof (intro equalityI subsetI)
    fix i assume i: "i \<in> {k+1..n}"
    hence "take i xs ! k = xs ! k" "k < n" "k < i" using assms
      by auto
    with i show "i \<in> {i. i \<in> {1..n} \<and> xs ! k \<in> set (take i xs)}"
      by (force simp: set_conv_nth)
  qed (insert assms xs, auto simp: set_conv_nth Suc_le_eq nth_eq_iff_index_eq)
  finally show ?thesis .
qed

lemma lead_monom_sym_poly_powerprod_inj:
  assumes "lead_monom (\<Prod>i. sym_mpoly A i ^ lookup m1 i :: 'a mpoly) =
             lead_monom (\<Prod>i. sym_mpoly A i ^ lookup m2 i :: 'a mpoly)"
  assumes "finite A" "keys m1 \<subseteq> {1..n}" "keys m2 \<subseteq> {1..n}"
  shows   "m1 = m2"
proof (rule poly_mapping_eqI)
  fix k :: nat
  have xs: "set xs = A" "distinct xs" "sorted xs" and [simp]: "length xs = n"
    using assms by (auto simp: xs_def n_def)

  from assms(3,4) have *: "i \<in> {1..n}" if "lookup m1 i \<noteq> 0 \<or> lookup m2 i \<noteq> 0" for i
    using that by (auto simp: subset_iff in_keys_iff)
  have **: "(\<Prod>i. sym_mpoly A i ^ lookup m i :: 'a mpoly) =
              (\<Prod>i=1..n. sym_mpoly A i ^ lookup m i :: 'a mpoly)" if "m \<in> {m1, m2}" for m
    using that * by (intro Prod_any.expand_superset subsetI * ) (auto intro!: Nat.gr0I)
  have ***: "lead_monom (\<Prod>i=1..n. sym_mpoly A i ^ lookup m1 i :: 'a mpoly) =
               lead_monom (\<Prod>i=1..n. sym_mpoly A i ^ lookup m2 i :: 'a mpoly)"
    using assms by (simp add: ** )

  have sum_eq: "sum (lookup m1) {Suc k..n} = sum (lookup m2) {Suc k..n}" if "k < n" for k
    using arg_cong[OF ***, of "\<lambda>m. lookup m (xs ! k)"] \<open>finite A\<close> that
    by (subst (asm) (1 2) lead_monom_sym_mpoly_prod_in) auto

  show "lookup m1 k = lookup m2 k"
  proof (cases "k \<in> {1..n}")
    case False
    hence "lookup m1 k = 0" "lookup m2 k = 0" using assms by (auto simp: in_keys_iff)
    thus ?thesis by simp
  next
    case True
    thus ?thesis
    proof (induction "n - k" arbitrary: k rule: less_induct)
      case (less l)
      have "sum (lookup m1) {Suc (l - 1)..n} = sum (lookup m2) {Suc (l - 1)..n}"
        using less by (intro sum_eq) auto
      also have "{Suc (l - 1)..n} = insert l {Suc l..n}"
        using less by auto
      also have "sum (lookup m1) \<dots> = lookup m1 l + (\<Sum>i=Suc l..n. lookup m1 i)"
        by (subst sum.insert) auto
      also have "(\<Sum>i=Suc l..n. lookup m1 i) = (\<Sum>i=Suc l..n. lookup m2 i)"
        by (intro sum.cong less) auto
      also have "sum (lookup m2) (insert l {Suc l..n}) = lookup m2 l + (\<Sum>i=Suc l..n. lookup m2 i)"
        by (subst sum.insert) auto
      finally show "lookup m1 l = lookup m2 l" by simp
    qed
  qed
qed

text \<open>
  We now show uniqueness by first showing that the zero polynomial has a unique representation.
  We fix some polynomial $p$ with $p(e_1,\ldots, e_n) = 0$ and then show, by contradiction,
  that $p = 0$.

  We have
  \[p(e_1,\ldots,e_n) = \sum c_{a_1,\ldots,a_n} e_1^{a_1}\ldots e_n^{a_n}\]
  and due to the injectivity of products of powers of elementary symmetric polynomials,
  the leading term of that sum is precisely the leading term of the summand with the biggest
  leading monomial, since summands cannot cancel each other.

  However, we also know that $p(e_1,\ldots,e_n) = 0$, so it follows that all summands
  must have leading term 0, and it is then easy to see that they must all be identically 0.
\<close>
lemma sym_mpoly_representation_unique_aux:
  fixes p :: "'a mpoly mpoly"
  assumes "finite A" "insertion (sym_mpoly A) p = 0"
          "\<And>m. vars (coeff p m) \<inter> A = {}" "vars p \<subseteq> {1..n}"
  shows   "p = 0"
proof (rule ccontr)
  assume p: "p \<noteq> 0"
  have xs: "set xs = A" "distinct xs" "sorted xs" and [simp]: "length xs = n"
    using assms by (auto simp: xs_def n_def)
  define h where "h = (\<lambda>m. coeff p m * (\<Prod>i. sym_mpoly A i ^ lookup m i))"
  define M where "M = {m. coeff p m \<noteq> 0}"
  define maxm where "maxm = Max ((lead_monom \<circ> h) ` M)"
  have "finite M"
    by (auto intro!: finite_subset[OF _ finite_coeff_support[of p]] simp: h_def M_def)
  have keys_subset: "keys m \<subseteq> {1..n}" if "coeff p m \<noteq> 0" for m
    using that assms coeff_notin_vars[of m p] by blast

  have lead_coeff: "lead_coeff (h m) = lead_coeff (coeff p m)" (is ?th1)
   and lead_monom: "lead_monom (h m) = lead_monom (coeff p m) +
                      lead_monom (\<Prod>i. sym_mpoly A i ^ lookup m i :: 'a mpoly)" (is ?th2)
   if [simp]: "coeff p m \<noteq> 0" for m
  proof -
    have "(\<Prod>i. sym_mpoly A i ^ lookup m i :: 'a mpoly) =
            (\<Prod>i | lookup m i \<noteq> 0. sym_mpoly A i ^ lookup m i :: 'a mpoly)"
      by (intro Prod_any.expand_superset) (auto intro!: Nat.gr0I)
    also have "lead_coeff \<dots> = 1"
      using assms keys_subset[of m]
      by (intro lead_coeff_sym_mpoly_powerprod) (auto simp: in_keys_iff subset_iff n_def)
    finally have eq: "lead_coeff (\<Prod>i. sym_mpoly A i ^ lookup m i :: 'a mpoly) = 1" .
    thus ?th1 unfolding h_def using \<open>coeff p m \<noteq> 0\<close> by (subst lead_coeff_mult) auto
    show ?th2 unfolding h_def by (subst lead_monom_mult) (auto simp: eq)
  qed

  have "insertion (sym_mpoly A) p = (\<Sum>m\<in>M. h m)"
    unfolding insertion_altdef h_def M_def by (intro Sum_any.expand_superset) auto
  also have "lead_monom \<dots> = maxm"
    unfolding maxm_def
  proof (rule lead_monom_sum)
    from p obtain m where "coeff p m \<noteq> 0"
      using mpoly_eqI[of p 0] by auto
    hence "m \<in> M"
      using \<open>coeff p m \<noteq> 0\<close> lead_coeff[of m] by (auto simp: M_def)
    thus "M \<noteq> {}" by auto
  next
    have restrict_lead_monom:
           "restrictpm A (lead_monom (h m)) =
             lead_monom (\<Prod>i. sym_mpoly A i ^ lookup m i :: 'a mpoly)"
      if [simp]: "coeff p m \<noteq> 0" for m
    proof -
      have "restrictpm A (lead_monom (h m)) =
              restrictpm A (lead_monom (coeff p m)) +
              restrictpm A (lead_monom (\<Prod>i. sym_mpoly A i ^ lookup m i :: 'a mpoly))"
        by (auto simp: lead_monom restrictpm_add)
      also have "restrictpm A (lead_monom (coeff p m)) = 0"
        using assms by (intro restrictpm_orthogonal order.trans[OF keys_lead_monom_subset]) auto
      also have "restrictpm A (lead_monom (\<Prod>i. sym_mpoly A i ^ lookup m i :: 'a mpoly)) =
                   lead_monom (\<Prod>i. sym_mpoly A i ^ lookup m i :: 'a mpoly)"
        by (intro restrictpm_id order.trans[OF keys_lead_monom_subset]
                  order.trans[OF vars_Prod_any] UN_least order.trans[OF vars_power]
                  vars_sym_mpoly_subset)
      finally show ?thesis by simp
    qed
    show "inj_on (lead_monom \<circ> h) M"
    proof
      fix m1 m2 assume m12: "m1 \<in> M" "m2 \<in> M" "(lead_monom \<circ> h) m1 = (lead_monom \<circ> h) m2"
      hence [simp]: "coeff p m1 \<noteq> 0" "coeff p m2 \<noteq> 0" by (auto simp: M_def h_def)
      have "restrictpm A (lead_monom (h m1)) = restrictpm A (lead_monom (h m2))"
        using m12 by simp
      hence "lead_monom (\<Prod>i. sym_mpoly A i ^ lookup m1 i :: 'a mpoly) =
               lead_monom (\<Prod>i. sym_mpoly A i ^ lookup m2 i :: 'a mpoly)"
        by (simp add: restrict_lead_monom)
      thus "m1 = m2"
        by (rule lead_monom_sym_poly_powerprod_inj)
           (use \<open>finite A\<close> keys_subset[of m1] keys_subset[of m2] in auto)
    qed
  next
    fix m assume "m \<in> M"
    hence "lead_coeff (h m) = lead_coeff (coeff p m)"
      by (simp add: lead_coeff M_def)
    with \<open>m \<in> M\<close> show "h m \<noteq> 0" by (auto simp: M_def)
  qed fact+
  finally have "maxm = 0" by (simp add: assms)

  have only_zero: "m = 0" if "m \<in> M" for m
  proof -
    from that have nz [simp]: "coeff p m \<noteq> 0" by (auto simp: M_def h_def)
    from that have "(lead_monom \<circ> h) m \<le> maxm"
      using \<open>finite M\<close> unfolding maxm_def by (intro Max_ge imageI finite_imageI)
    with \<open>maxm = 0\<close> have [simp]: "lead_monom (h m) = 0" by simp
    have lookup_nzD: "k \<in> {1..n}" if "lookup m k \<noteq> 0" for k
      using keys_subset[of m] that by (auto simp: in_keys_iff subset_iff)

    have "lead_monom (coeff p m) + 0 \<le> lead_monom (h m)"
      unfolding lead_monom[OF nz] by (intro add_left_mono) auto
    also have "\<dots> = 0" by simp
    finally have lead_monom_0: "lead_monom (coeff p m) = 0" by simp

    have "sum (lookup m) {1..n} = 0"
    proof (rule ccontr)
      assume "sum (lookup m) {1..n} \<noteq> 0"
      hence "sum (lookup m) {1..n} > 0" by presburger
      have "0 \<noteq> lead_coeff (MPoly_Type.coeff p m)"
        by auto
      also have "lead_coeff (MPoly_Type.coeff p m) = lead_coeff (h m)"
        by (simp add: lead_coeff)
      also have "lead_coeff (h m) = coeff (h m) 0"
        by (simp add: lead_coeff_def)
      also have "\<dots> = coeff (coeff p m) 0 * coeff (\<Prod>i. sym_mpoly A i ^ lookup m i) 0"
        by (simp add: h_def mpoly_coeff_times_0)
      also have "(\<Prod>i. sym_mpoly A i ^ lookup m i) = (\<Prod>i=1..n. sym_mpoly A i ^ lookup m i)"
        by (intro Prod_any.expand_superset subsetI lookup_nzD) (auto intro!: Nat.gr0I)
      also have "coeff \<dots> 0 = (\<Prod>i=1..n. 0 ^ lookup m i)"
        unfolding mpoly_coeff_prod_0 mpoly_coeff_power_0
        by (intro prod.cong) (auto simp: coeff_sym_mpoly_0)
      also have "\<dots> = 0 ^ (\<Sum>i=1..n. lookup m i)"
        by (simp add: power_sum)
      also have "\<dots> = 0"
        using zero_power[OF \<open>sum (lookup m) {1..n} > 0\<close>] by simp
      finally show False by auto
    qed
    hence "lookup m k = 0" for k
      using keys_subset[of m] by (cases "k \<in> {1..n}") (auto simp: in_keys_iff)
    thus "m = 0" by (intro poly_mapping_eqI) auto
  qed

  have "0 = insertion (sym_mpoly A) p"
    using assms by simp
  also have "insertion (sym_mpoly A) p = (\<Sum>m\<in>M. h m)"
    by fact
  also have "\<dots> = (\<Sum>m\<in>{0}. h m)"
    using only_zero by (intro sum.mono_neutral_left) (auto simp: h_def M_def)
  also have "\<dots> = coeff p 0"
    by (simp add: h_def)
  finally have "0 \<notin> M" by (auto simp: M_def)
  with only_zero have "M = {}" by auto
  hence "p = 0" by (intro mpoly_eqI) (auto simp: M_def)
  with \<open>p \<noteq> 0\<close> show False by contradiction
qed

text \<open>
  The general uniqueness theorem now follows easily. This essentially shows that
  the substitution $Y_i \mapsto e_i(X_1,\ldots,X_n)$ is an isomorphism between the
  ring $R[Y_1,\ldots, Y_n]$ and the ring $R[X_1,\ldots,X_n]^{S_n}$ of symmetric polynomials.
\<close>
theorem sym_mpoly_representation_unique:
  fixes p :: "'a mpoly mpoly"
  assumes "finite A"
          "insertion (sym_mpoly A) p = insertion (sym_mpoly A) q"
          "\<And>m. vars (coeff p m) \<inter> A = {}" "\<And>m. vars (coeff q m) \<inter> A = {}"
          "vars p \<subseteq> {1..n}" "vars q \<subseteq> {1..n}"
  shows   "p = q"
proof -
  have "p - q = 0"
  proof (rule sym_mpoly_representation_unique_aux)
    fix m show "vars (coeff (p - q) m) \<inter> A = {}"
      using vars_diff[of "coeff p m" "coeff q m"] assms(3,4)[of m] by auto
  qed (insert assms vars_diff[of p q], auto simp: insertion_diff)
  thus ?thesis by simp
qed

theorem eq_fund_sym_poly_witI:
  fixes p :: "'a mpoly" and q :: "'a mpoly mpoly"
  assumes "finite A" "symmetric_mpoly A p"
          "insertion (sym_mpoly A) q = p"
          "\<And>m. vars (coeff q m) \<inter> A = {}"
          "vars q \<subseteq> {1..n}"
  shows   "q = fund_sym_poly_wit p"
  using fund_sym_poly_wit_insertion[of p] fund_sym_poly_wit_vars[of p]
        fund_sym_poly_wit_coeffs[of p]
  by (intro sym_mpoly_representation_unique)
     (insert assms, auto simp: fund_sym_poly_wit_insertion)



subsection \<open>A recursive characterisation of symmetry\<close>

text \<open>
  In a similar spirit to the proof of the fundamental theorem, we obtain a nice
  recursive and executable characterisation of symmetry.
\<close>

(*<*)
lemmas [fundef_cong] = disj_cong conj_cong
(*>*)

function (domintros) check_symmetric_mpoly where
  "check_symmetric_mpoly p \<longleftrightarrow>
     (vars p \<inter> A = {} \<or>
      A \<subseteq> vars p \<and> decr p \<and> check_symmetric_mpoly (p - fund_sym_step_poly p))"
  by auto

lemma check_symmetric_mpoly_dom_aux:
  assumes "finite B" "vars p \<subseteq> B" "A \<subseteq> B"
  shows   "check_symmetric_mpoly_dom p"
  using assms(1-3)
proof (induction p rule: lead_monom_induct)
  case (less p)
  have [simp]: "finite A" by (rule finite_subset[of _ B]) fact+
  show ?case
  proof (cases "lead_monom p = 0 \<or> \<not>decr p")
    case False
    hence [simp]: "p \<noteq> 0" by auto
    have "vars (p - fund_sym_step_poly p) \<subseteq> B"
      using fund_sym_step_poly[of p] False less.prems less.hyps \<open>A \<subseteq> B\<close>
      by (intro order.trans[OF vars_diff]) auto
    hence "check_symmetric_mpoly_dom (p - local.fund_sym_step_poly p)"
      using False less.prems less.hyps
      by (intro less.IH fund_sym_step_poly symmetric_mpoly_diff
                lead_monom_fund_sym_step_poly_less) (auto simp: decr_def)
    thus ?thesis using check_symmetric_mpoly.domintros by blast
  qed (auto intro: check_symmetric_mpoly.domintros simp: lead_monom_eq_0_iff)
qed

lemma check_symmetric_mpoly_dom [intro]: "check_symmetric_mpoly_dom p"
proof -
  show ?thesis
  proof (cases "A \<subseteq> vars p")
    assume "A \<subseteq> vars p"
    thus ?thesis using check_symmetric_mpoly_dom_aux[of "vars p" p] by (auto simp: vars_finite)
  qed (auto intro: check_symmetric_mpoly.domintros)
qed

termination check_symmetric_mpoly
  by (intro allI check_symmetric_mpoly_dom)

lemmas [simp del] = check_symmetric_mpoly.simps

lemma check_symmetric_mpoly_correct: "check_symmetric_mpoly p \<longleftrightarrow> symmetric_mpoly A p"
proof (induction p rule: check_symmetric_mpoly.induct)
  case (1 p)
  have "symmetric_mpoly A (p - fund_sym_step_poly p) \<longleftrightarrow> symmetric_mpoly A p" (is "?lhs = ?rhs")
  proof
    assume ?rhs
    thus ?lhs by (intro symmetric_mpoly_diff fund_sym_step_poly)
  next
    assume ?lhs
    hence "symmetric_mpoly A (p - fund_sym_step_poly p + fund_sym_step_poly p)"
      by (intro symmetric_mpoly_add fund_sym_step_poly)
    thus ?rhs by simp
  qed
  moreover have "decr p" if "symmetric_mpoly A p"
    using lookup_lead_monom_decreasing[of A p] that by (auto simp: decr_def)
  ultimately show "check_symmetric_mpoly p \<longleftrightarrow> symmetric_mpoly A p"
    using 1 symmetric_mpoly_imp_orthogonal_or_subset[of A p]
    by (auto simp: Let_def check_symmetric_mpoly.simps[of p] intro: symmetric_mpoly_orthogonal)
qed

end


subsection \<open>Symmetric functions of roots of a univariate polynomial\<close>

text \<open>
  Consider a factored polynomial
  \[p(X) = c_n X^n + c_{n-1} X^{n-1} + \ldots + c_1X + c_0 = (X - x_1)\ldots(X - x_n)\ .\]
  where $c_n$ is a unit.

  Then any symmetric polynomial expression $q(x_1, \ldots, x_n)$ in the roots $x_i$ can
  be written as a polynomial expression $q'(c_0,\ldots, c_{n-1})$ in the $c_i$.

  Moreover, if the coefficients of $q$ and the inverse of $c_n$ all lie in some
  subring, the coefficients of $q'$ do as well.
\<close>

context
  fixes C :: "'b :: comm_ring_1 set"
    and A :: "nat set"
    and root :: "nat \<Rightarrow> 'a :: comm_ring_1"
    and l :: "'a \<Rightarrow> 'b"
    and q :: "'b mpoly"
    and n :: nat
  defines "n \<equiv> card A"
  assumes C: "ring_closed C" "\<forall>m. coeff q m \<in> C"
  assumes l: "ring_homomorphism l"
  assumes finite: "finite A"
  assumes sym: "symmetric_mpoly A q" and vars: "vars q \<subseteq> A"
begin

interpretation ring_closed C by fact
interpretation ring_homomorphism l by fact

theorem symmetric_poly_of_roots_conv_poly_of_coeffs:
  assumes c: "cinv * l c = 1" "cinv \<in> C"
  assumes "p = Polynomial.smult c (\<Prod>i\<in>A. [:-root i, 1:])"
  obtains q' where "vars q' \<subseteq> {0..<n}"
               and "\<And>m. coeff q' m \<in> C"
               and "insertion (l \<circ> poly.coeff p) q' = insertion (l \<circ> root) q"
proof -
  define q' where "q' = fund_sym_poly_wit A q"
  define q'' where "q'' =
     mapm_mpoly (\<lambda>m x. (\<Prod>i. (cinv * l (- 1) ^ i) ^ lookup m i) * insertion (\<lambda>_. 0) x) q'"
  define reindex where "reindex = (\<lambda>i. if i \<le> n then n - i else i)"
  have "bij reindex"
    by (intro bij_betwI[of reindex _ _ reindex]) (auto simp: reindex_def)
  have "vars q' \<subseteq> {1..n}" unfolding q'_def n_def by (intro fund_sym_poly_wit_vars)
  hence "vars q'' \<subseteq> {1..n}"
    unfolding q''_def using vars_mapm_mpoly_subset by auto

  have "insertion (l \<circ> root) (insertion (sym_mpoly A) q') =
          insertion (\<lambda>n. insertion (l \<circ> root) (sym_mpoly A n))
            (map_mpoly (insertion (l \<circ> root)) q')"
    by (rule insertion_insertion)
  also have "insertion (sym_mpoly A) q' = q"
    unfolding q'_def by (intro fund_sym_poly_wit_insertion sym)
  also have "insertion (\<lambda>i. insertion (l \<circ> root) (sym_mpoly A i))
               (map_mpoly (insertion (l \<circ> root)) q') =
             insertion (\<lambda>i. cinv * l ((- 1) ^ i) * l (poly.coeff p (n - i)))
               (map_mpoly (insertion (l \<circ> root)) q')"
  proof (intro insertion_irrelevant_vars, goal_cases)
    case (1 i)
    hence "i \<in> vars q'" using vars_map_mpoly_subset by auto
    also have "\<dots> \<subseteq> {1..n}" unfolding q'_def n_def
      by (intro fund_sym_poly_wit_vars)
    finally have i: "i \<in> {1..n}" .
    have "insertion (l \<circ> root) (sym_mpoly A i) =
             l (\<Sum>Y | Y \<subseteq> A \<and> card Y = i. prod root Y)"
      using \<open>finite A\<close> by (simp add: insertion_sym_mpoly)
    also have "\<dots> = cinv * l (c * (\<Sum>Y | Y \<subseteq> A \<and> card Y = i. prod root Y))"
      unfolding mult mult.assoc[symmetric] \<open>cinv * l c = 1\<close> by simp
    also have "c * (\<Sum>Y | Y \<subseteq> A \<and> card Y = i. prod root Y) = ((-1) ^ i * poly.coeff p (n - i))"
      using coeff_poly_from_roots[of A "n - i" root] i assms finite
      by (auto simp: n_def minus_one_power_iff)
    finally show ?case by (simp add: o_def)
  qed
  also have "map_mpoly (insertion (l \<circ> root)) q' = map_mpoly (insertion (\<lambda>_. 0)) q'"
    using fund_sym_poly_wit_coeffs[OF sym] vars
    by (intro map_mpoly_cong insertion_irrelevant_vars) (auto simp: q'_def)
  also have "insertion (\<lambda>i. cinv * l ((- 1) ^ i) * l (poly.coeff p (n - i))) \<dots> =
               insertion (\<lambda>i. l (poly.coeff p (n - i))) q''"
    unfolding insertion_substitute_linear map_mpoly_conv_mapm_mpoly q''_def
    by (subst mapm_mpoly_comp) auto
  also have "\<dots> = insertion (l \<circ> poly.coeff p) (mpoly_map_vars reindex q'')"
    using \<open>bij reindex\<close> and \<open>vars q'' \<subseteq> {1..n}\<close>
    by (subst insertion_mpoly_map_vars)
       (auto simp: o_def reindex_def intro!: insertion_irrelevant_vars)
  finally have "insertion (l \<circ> root) q =
                  insertion (l \<circ> poly.coeff p) (mpoly_map_vars reindex q'')" .

  moreover have "coeff (mpoly_map_vars reindex q'') m \<in> C" for m
    unfolding q''_def q'_def using \<open>bij reindex\<close> fund_sym_poly_wit_coeff[of q C A] C \<open>cinv \<in> C\<close>
    by (auto simp: coeff_mpoly_map_vars
             intro!: mult_closed Prod_any_closed power_closed Sum_any_closed)
  moreover have "vars (mpoly_map_vars reindex q'') \<subseteq> {0..<n}"
    using \<open>bij reindex\<close> and \<open>vars q'' \<subseteq> {1..n}\<close>
    by (subst vars_mpoly_map_vars) (auto simp: reindex_def subset_iff)+
  ultimately show ?thesis using that[of "mpoly_map_vars reindex q''"] by auto
qed

corollary symmetric_poly_of_roots_conv_poly_of_coeffs_monic:
  assumes "p = (\<Prod>i\<in>A. [:-root i, 1:])"
  obtains q' where "vars q' \<subseteq> {0..<n}"
               and "\<And>m. coeff q' m \<in> C"
               and "insertion (l \<circ> poly.coeff p) q' = insertion (l \<circ> root) q"
proof -
  obtain q' where "vars q' \<subseteq> {0..<n}"
              and "\<And>m. coeff q' m \<in> C"
              and "insertion (l \<circ> poly.coeff p) q' = insertion (l \<circ> root) q"
    by (rule symmetric_poly_of_roots_conv_poly_of_coeffs[of 1 1 p])
       (use assms in auto)
  thus ?thesis by (intro that[of q']) auto
qed

text \<open>
  As a corollary, we obtain the following: Let $R, S$ be rings with $R\subseteq S$.
  Consider a polynomial $p\in R[X]$ whose leading coefficient $c$ is a unit in $R$ and
  that has a full set of roots $x_1,\ldots, x_n \in S$,
  i.\,e.\ $p(X) = c(X - x_1) \ldots (X - x_n)$. Let $q \in R[X_1,\ldots, X_n]$ be some
  symmetric polynomial expression in the roots. Then $q(x_1, \ldots, x_n) \in R$.

  A typical use case is $R = \mathbb{Q}$ and $S = \mathbb{C}$, i.\,e.\ any symmetric
  polynomial expression with rational coefficients in the roots of a rational polynomial is
  again rational. Similarly, any symmetric polynomial expression with integer coefficients
  in the roots of a monic integer polynomial is agan an integer.

  This is remarkable, since the roots themselves are usually not rational (possibly not
  even real). This particular fact is a key ingredient used in the standard proof
  that $\pi$ is transcendental.
\<close>
corollary symmetric_poly_of_roots_in_subring:
  assumes "cinv * l c = 1" "cinv \<in> C"
  assumes "p = Polynomial.smult c (\<Prod>i\<in>A. [:-root i, 1:])"
  assumes "\<forall>i. l (poly.coeff p i) \<in> C"
  shows   "insertion (\<lambda>x. l (root x)) q \<in> C"
proof -
  obtain q'
    where q': "vars q' \<subseteq> {0..<n}" "\<And>m. coeff q' m \<in> C"
              "insertion (l \<circ> poly.coeff p) q' = insertion (l \<circ> root) q"
    by (rule symmetric_poly_of_roots_conv_poly_of_coeffs[of cinv c p])
       (use assms in simp_all)
  have "insertion (l \<circ> poly.coeff p) q' \<in> C" using C assms unfolding insertion_altdef
    by (intro Sum_any_closed mult_closed q' Prod_any_closed power_closed) auto
  also have "insertion (l \<circ> poly.coeff p) q' = insertion (l \<circ> root) q" by fact
  finally show ?thesis by (simp add: o_def)
qed

corollary symmetric_poly_of_roots_in_subring_monic:
  assumes "p = (\<Prod>i\<in>A. [:-root i, 1:])"
  assumes "\<forall>i. l (poly.coeff p i) \<in> C"
  shows   "insertion (\<lambda>x. l (root x)) q \<in> C"
proof -
  interpret ring_closed C by fact
  interpret ring_homomorphism l by fact
  show ?thesis
    by (rule symmetric_poly_of_roots_in_subring[of 1 1 p]) (use assms in auto)
qed

end

end