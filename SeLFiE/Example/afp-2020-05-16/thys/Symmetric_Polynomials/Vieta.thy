(*
  File:     Vieta.thy
  Author:   Manuel Eberl (TU München)

  Vieta's formulas expressing the coefficients of a factored univariate polynomial in
  terms of its roots.
*)
section \<open>Vieta's Formulas\<close>
theory Vieta
imports
  "HOL-Library.FuncSet"
  "HOL-Computational_Algebra.Computational_Algebra"
begin

subsection \<open>Auxiliary material\<close>

lemma card_vimage_inter:
  assumes inj: "inj_on f A" and subset: "X \<subseteq> f ` A"
  shows   "card (f -` X \<inter> A) = card X"
proof -
  have "card (f -` X \<inter> A) = card (f ` (f -` X \<inter> A))"
    by (subst card_image) (auto intro!: inj_on_subset[OF inj])
  also have "f ` (f -` X \<inter> A) = X"
    using assms by auto
  finally show ?thesis .
qed

lemma bij_betw_image_fixed_card_subset:
  assumes "inj_on f A"
  shows   "bij_betw (\<lambda>X. f ` X) {X. X \<subseteq> A \<and> card X = k} {X. X \<subseteq> f ` A \<and> card X = k}"
  using assms inj_on_subset[OF assms]
  by (intro bij_betwI[of _ _ _ "\<lambda>X. f -` X \<inter> A"]) (auto simp: card_image card_vimage_inter)

lemma image_image_fixed_card_subset:
  assumes "inj_on f A"
  shows   "(\<lambda>X. f ` X) ` {X. X \<subseteq> A \<and> card X = k} = {X. X \<subseteq> f ` A \<and> card X = k}"
  using bij_betw_imp_surj_on[OF bij_betw_image_fixed_card_subset[OF assms, of k]] .

lemma prod_uminus: "(\<Prod>x\<in>A. -f x :: 'a :: comm_ring_1) = (-1) ^ card A * (\<Prod>x\<in>A. f x)"
  by (induction A rule: infinite_finite_induct) (auto simp: algebra_simps)

theorem prod_sum_PiE:
  fixes f :: "'a \<Rightarrow> 'b \<Rightarrow> 'c :: comm_semiring_1"
  assumes finite: "finite A" and finite: "\<And>x. x \<in> A \<Longrightarrow> finite (B x)"
  shows   "(\<Prod>x\<in>A. \<Sum>y\<in>B x. f x y) = (\<Sum>g\<in>PiE A B. \<Prod>x\<in>A. f x (g x))"
  using assms
proof (induction A rule: finite_induct)
  case empty
  thus ?case by auto
next
  case (insert x A)
  have "(\<Sum>g\<in>Pi\<^sub>E (insert x A) B. \<Prod>x\<in>insert x A. f x (g x)) =
          (\<Sum>g\<in>Pi\<^sub>E (insert x A) B. f x (g x) * (\<Prod>x'\<in>A. f x' (g x')))"
    using insert by simp
  also have "(\<lambda>g. \<Prod>x'\<in>A. f x' (g x')) = (\<lambda>g. \<Prod>x'\<in>A. f x' (if x' = x then undefined else g x'))"
    using insert by (intro ext prod.cong) auto
  also have "(\<Sum>g\<in>Pi\<^sub>E (insert x A) B. f x (g x) * \<dots> g) =
               (\<Sum>(y,g)\<in>B x \<times> Pi\<^sub>E A B. f x y * (\<Prod>x'\<in>A. f x' (g x')))"
    using insert.prems insert.hyps
    by (intro sum.reindex_bij_witness[of _ "\<lambda>(y,g). g(x := y)" "\<lambda>g. (g x, g(x := undefined))"])
       (auto simp: PiE_def extensional_def)
  also have "\<dots> = (\<Sum>y\<in>B x. \<Sum>g\<in>Pi\<^sub>E A B. f x y * (\<Prod>x'\<in>A. f x' (g x')))"
    by (subst sum.cartesian_product) auto
  also have "\<dots> = (\<Sum>y\<in>B x. f x y) * (\<Sum>g\<in>Pi\<^sub>E A B. \<Prod>x'\<in>A. f x' (g x'))"
    using insert by (subst sum.swap) (simp add: sum_distrib_left sum_distrib_right)
  also have "(\<Sum>g\<in>Pi\<^sub>E A B. \<Prod>x'\<in>A. f x' (g x')) = (\<Prod>x\<in>A. \<Sum>y\<in>B x. f x y)"
    using insert.prems by (intro insert.IH [symmetric]) auto
  also have "(\<Sum>y\<in>B x. f x y) * \<dots> = (\<Prod>x\<in>insert x A. \<Sum>y\<in>B x. f x y)"
    using insert.hyps by simp
  finally show ?case ..
qed

corollary prod_add:
  fixes f1 f2 :: "'a \<Rightarrow> 'c :: comm_semiring_1"
  assumes finite: "finite A"
  shows   "(\<Prod>x\<in>A. f1 x + f2 x) = (\<Sum>X\<in>Pow A. (\<Prod>x\<in>X. f1 x) * (\<Prod>x\<in>A-X. f2 x))"
proof -
  have "(\<Prod>x\<in>A. f1 x + f2 x) = (\<Sum>g\<in>A \<rightarrow>\<^sub>E UNIV. \<Prod>x\<in>A. if g x then f1 x else f2 x)"
    using prod_sum_PiE[of A "\<lambda>_. UNIV :: bool set" "\<lambda>x y. if y then f1 x else f2 x"] assms
    by (simp_all add: UNIV_bool add_ac)
  also have "\<dots> = (\<Sum>X\<in>Pow A. \<Prod>x\<in>A. if x \<in> X then f1 x else f2 x)"
    by (intro sum.reindex_bij_witness
          [of _ "\<lambda>X x. if x \<in> A then x \<in> X else undefined" "\<lambda>P. {x\<in>A. P x}"]) auto
  also have "\<dots> = (\<Sum>X\<in>Pow A. (\<Prod>x\<in>X. f1 x) * (\<Prod>x\<in>A-X. f2 x))"
  proof (intro sum.cong refl, goal_cases)
    case (1 X)
    let ?f = "\<lambda>x. if x \<in> X then f1 x else f2 x"
    have "prod f1 X * prod f2 (A - X) = prod ?f X * prod ?f (A - X)"
      by (intro arg_cong2[of _ _ _ _ "(*)"] prod.cong) auto
    also have "\<dots> = prod ?f (X \<union> (A - X))"
      using 1 by (subst prod.union_disjoint) (auto intro: finite_subset[OF _ finite])
    also have "X \<union> (A - X) = A" using 1 by auto
    finally show ?case ..
  qed
  finally show ?thesis .
qed

corollary prod_diff1:
  fixes f1 f2 :: "'a \<Rightarrow> 'c :: comm_ring_1"
  assumes finite: "finite A"
  shows   "(\<Prod>x\<in>A. f1 x - f2 x) = (\<Sum>X\<in>Pow A. (-1) ^ card X * (\<Prod>x\<in>X. f2 x) * (\<Prod>x\<in>A-X. f1 x))"
proof -
  have "(\<Prod>x\<in>A. f1 x - f2 x) = (\<Prod>x\<in>A. -f2 x + f1 x)"
    by simp
  also have "\<dots> = (\<Sum>X\<in>Pow A. (\<Prod>x\<in>X. - f2 x) * prod f1 (A - X))"
    by (rule prod_add) fact+
  also have "\<dots> = (\<Sum>X\<in>Pow A. (-1) ^ card X * (\<Prod>x\<in>X. f2 x) * prod f1 (A - X))"
    by (simp add: prod_uminus)
  finally show ?thesis .
qed

corollary prod_diff2:
  fixes f1 f2 :: "'a \<Rightarrow> 'c :: comm_ring_1"
  assumes finite: "finite A"
  shows   "(\<Prod>x\<in>A. f1 x - f2 x) = (\<Sum>X\<in>Pow A. (-1) ^ (card A - card X) * (\<Prod>x\<in>X. f1 x) * (\<Prod>x\<in>A-X. f2 x))"
proof -
  have "(\<Prod>x\<in>A. f1 x - f2 x) = (\<Prod>x\<in>A. f1 x + (-f2 x))"
    by simp
  also have "\<dots> = (\<Sum>X\<in>Pow A. (\<Prod>x\<in>X. f1 x) * (\<Prod>x\<in>A-X. -f2 x))"
    by (rule prod_add) fact+
  also have "\<dots> = (\<Sum>X\<in>Pow A. (-1) ^ card (A - X) * (\<Prod>x\<in>X. f1 x) * (\<Prod>x\<in>A-X. f2 x))"
    by (simp add: prod_uminus mult_ac)
  also have "\<dots> = (\<Sum>X\<in>Pow A. (-1) ^ (card A - card X) * (\<Prod>x\<in>X. f1 x) * (\<Prod>x\<in>A-X. f2 x))"
    using finite_subset[OF _ assms] by (intro sum.cong refl, subst card_Diff_subset) auto
  finally show ?thesis .
qed


subsection \<open>Main proofs\<close>

text \<open>
  Our goal is to determine the coefficients of some fully factored polynomial
  $p(X) = c (X - x_1) \ldots (X - x_n)$ in terms of the $x_i$. It is clear that it is
  sufficient to consider monic polynomials (i.e. $c = 1$), since the general case follows
  easily from this one.

  We start off by expanding the product over the linear factors:
\<close>
lemma poly_from_roots:
  fixes f :: "'a \<Rightarrow> 'b :: comm_ring_1" assumes fin: "finite A"
  shows "(\<Prod>x\<in>A. [:-f x, 1:]) = (\<Sum>X\<in>Pow A. monom ((-1) ^ card X * (\<Prod>x\<in>X. f x)) (card (A - X)))"
proof -
  have "(\<Prod>x\<in>A. [:-f x, 1:]) = (\<Prod>x\<in>A. [:0, 1:] - [:f x:])"
    by simp
  also have "\<dots> = (\<Sum>X\<in>Pow A. (-1) ^ card X * (\<Prod>x\<in>X. [:f x:]) * monom 1 (card (A - X)))"
    using fin by (subst prod_diff1) (auto simp: monom_altdef mult_ac)
  also have "\<dots> = (\<Sum>X\<in>Pow A. monom ((-1) ^ card X * (\<Prod>x\<in>X. f x)) (card (A - X)))"
  proof (intro sum.cong refl, goal_cases)
    case (1 X)
    have "(-1 :: 'b poly) ^ card X = [:(-1) ^ card X:]"
      by (induction X rule: infinite_finite_induct) (auto simp: one_pCons algebra_simps)
    moreover have "(\<Prod>x\<in>X. [:f x:]) = [:\<Prod>x\<in>X. f x:]"
      by (induction X rule: infinite_finite_induct) auto
    ultimately show ?case by (simp add: smult_monom)
  qed
  finally show ?thesis .
qed

text \<open>
  Comparing coefficients yields Vieta's formula:
\<close>
theorem coeff_poly_from_roots:
  fixes f :: "'a \<Rightarrow> 'b :: comm_ring_1"
  assumes fin: "finite A" and k: "k \<le> card A"
  shows   "coeff (\<Prod>x\<in>A. [:-f x, 1:]) k =
             (-1) ^ (card A - k) * (\<Sum>X | X \<subseteq> A \<and> card X = card A - k. (\<Prod>x\<in>X. f x))"
proof -
  have "(\<Prod>x\<in>A. [:-f x, 1:]) = (\<Sum>X\<in>Pow A. monom ((-1) ^ card X * (\<Prod>x\<in>X. f x)) (card (A - X)))"
    by (intro poly_from_roots fin)
  also have "coeff \<dots> k = (\<Sum>X | X \<subseteq> A \<and> card X = card A - k. (-1) ^ (card A - k) * (\<Prod>x\<in>X. f x))"
    unfolding coeff_sum coeff_monom using finite_subset[OF _ fin] k card_mono[OF fin]
    by (intro sum.mono_neutral_cong_right) (auto simp: card_Diff_subset)
  also have "\<dots> = (-1) ^ (card A - k) * (\<Sum>X | X \<subseteq> A \<and> card X = card A - k. (\<Prod>x\<in>X. f x))"
    by (simp add: sum_distrib_left)
  finally show ?thesis .
qed

text \<open>
  If the roots are all distinct, we can get the following alternative representation:
\<close>
corollary coeff_poly_from_roots':
  fixes f :: "'a \<Rightarrow> 'b :: comm_ring_1"
  assumes fin: "finite A" and inj: "inj_on f A" and k: "k \<le> card A"
  shows   "coeff (\<Prod>x\<in>A. [:-f x, 1:]) k =
             (-1) ^ (card A - k) * (\<Sum>X | X \<subseteq> f ` A \<and> card X = card A - k. \<Prod>X)"
proof -
  have "coeff (\<Prod>x\<in>A. [:-f x, 1:]) k =
          (-1) ^ (card A - k) * (\<Sum>X | X \<subseteq> A \<and> card X = card A - k. (\<Prod>x\<in>X. f x))"
    by (intro coeff_poly_from_roots assms)
  also have "(\<Sum>X | X \<subseteq> A \<and> card X = card A - k. (\<Prod>x\<in>X. f x)) =
               (\<Sum>X | X \<subseteq> A \<and> card X = card A - k. \<Prod>(f`X))"
    by (intro sum.cong refl, subst prod.reindex) (auto intro: inj_on_subset[OF inj])
  also have "\<dots> = (\<Sum>X \<in> (\<lambda>X. f`X) ` {X. X \<subseteq> A \<and> card X = card A - k}. \<Prod>X)"
    by (subst sum.reindex) (auto intro!: inj_on_image inj_on_subset[OF inj])
  also have "(\<lambda>X. f ` X) ` {X. X \<subseteq> A \<and> card X = card A - k} = {X. X \<subseteq> f ` A \<and> card X = card A - k}"
    by (intro image_image_fixed_card_subset inj)
  finally show ?thesis .
qed

end