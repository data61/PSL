(* Author: Andreas Lochbihler, ETH Zurich *)

theory Rel_PMF_Characterisation imports
  Matrix_For_Marginals
begin

section \<open>Characterisation of @{const rel_pmf}\<close>

proposition rel_pmf_measureI:
  fixes p :: "'a pmf" and q :: "'b pmf"
  assumes le: "\<And>A. measure (measure_pmf p) A \<le> measure (measure_pmf q) {y. \<exists>x\<in>A. R x y}"
  shows "rel_pmf R p q"
proof -
  let ?A = "set_pmf p" and ?f = "\<lambda>x. ennreal (pmf p x)"
    and ?B = "set_pmf q" and ?g = "\<lambda>y. ennreal (pmf q y)"
  define R' where "R' = {(x, y)\<in>?A \<times> ?B. R x y}"

  have "(\<Sum>\<^sup>+ x\<in>?A. ?f x) = (\<Sum>\<^sup>+ y\<in>?B. ?g y)" (is "?lhs = ?rhs")
    and "(\<Sum>\<^sup>+ y\<in>?B. ?g y) \<noteq> \<top>" (is ?bounded)
  proof -
    have "?lhs = (\<Sum>\<^sup>+ x. ?f x)" "?rhs = (\<Sum>\<^sup>+ y. ?g y)"
      by(auto simp add: nn_integral_count_space_indicator pmf_eq_0_set_pmf intro!: nn_integral_cong split: split_indicator)
    then show "?lhs = ?rhs" ?bounded by(simp_all add: nn_integral_pmf_eq_1)
  qed
  moreover
  have "(\<Sum>\<^sup>+ x\<in>X. ?f x) \<le> (\<Sum>\<^sup>+ y\<in>R' `` X. ?g y)" (is "?lhs \<le> ?rhs") if "X \<subseteq> set_pmf p" for X
  proof -
    have "?lhs = measure (measure_pmf p) X" 
      by(simp add: nn_integral_pmf measure_pmf.emeasure_eq_measure)
    also have "\<dots> \<le> measure (measure_pmf q) {y. \<exists>x\<in>X. R x y}" by(simp add: le)
    also have "\<dots> = measure (measure_pmf q) (R' `` X)" using that
      by(auto 4 3 simp add: R'_def AE_measure_pmf_iff intro!: measure_eq_AE)
    also have "\<dots> = ?rhs" by(simp add: nn_integral_pmf measure_pmf.emeasure_eq_measure)
    finally show ?thesis .
  qed
  moreover have "countable ?A" "countable ?B" by simp_all
  moreover have "R' \<subseteq> ?A \<times> ?B" by(auto simp add: R'_def)
  ultimately obtain h
    where supp: "\<And>x y. 0 < h x y \<Longrightarrow> (x, y) \<in> R'"
    and bound: "\<And>x y. h x y \<noteq> \<top>"
    and p: "\<And>x. x \<in> ?A \<Longrightarrow> (\<Sum>\<^sup>+ y\<in>?B. h x y) = ?f x"
    and q: "\<And>y. y \<in> ?B \<Longrightarrow> (\<Sum>\<^sup>+ x\<in>?A. h x y) = ?g y"
    by(rule bounded_matrix_for_marginals_ennreal) blast+

  let ?z = "\<lambda>(x, y). enn2real (h x y)"
  define z where "z = embed_pmf ?z"
  have nonneg: "\<And>xy. 0 \<le> ?z xy" by clarsimp
  have outside: "h x y = 0" if "x \<notin> set_pmf p \<or> y \<notin> set_pmf q \<or> \<not> R x y" for x y
    using supp[of x y] that by(cases "h x y > 0")(auto simp add: R'_def)
  have prob: "(\<Sum>\<^sup>+ xy. ?z xy) = 1"
  proof -
    have "(\<Sum>\<^sup>+ xy. ?z xy) = (\<Sum>\<^sup>+ x. \<Sum>\<^sup>+ y. (ennreal \<circ> ?z) (x, y))"
      unfolding nn_integral_fst_count_space by(simp add: split_def o_def)
    also have "\<dots> = (\<Sum>\<^sup>+ x. (\<Sum>\<^sup>+y. h x y))" using bound
      by(simp add: nn_integral_count_space_reindex ennreal_enn2real_if)
    also have "\<dots> = (\<Sum>\<^sup>+ x\<in>?A. (\<Sum>\<^sup>+y\<in>?B. h x y))"
      by(auto intro!: nn_integral_cong nn_integral_zero' simp add: nn_integral_count_space_indicator outside split: split_indicator)
    also have "\<dots> = (\<Sum>\<^sup>+ x\<in>?A. ?f x)" by(auto simp add: p intro!: nn_integral_cong)
    also have "\<dots> = (\<Sum>\<^sup>+ x. ?f x)"
      by(auto simp add: nn_integral_count_space_indicator pmf_eq_0_set_pmf intro!: nn_integral_cong split: split_indicator)
    finally show ?thesis by(simp add: nn_integral_pmf_eq_1)
  qed
  note z = nonneg prob
  have z_sel [simp]: "pmf z (x, y) = enn2real (h x y)" for x y
    by(simp add: z_def pmf_embed_pmf[OF z])

  show ?thesis
  proof
    show "R x y" if "(x, y) \<in> set_pmf z" for x y using that
      using that outside[of x y] unfolding set_pmf_iff
      by(auto simp add: enn2real_eq_0_iff)

    show "map_pmf fst z = p"
    proof(rule pmf_eqI)
      fix x
      have "pmf (map_pmf fst z) x = (\<Sum>\<^sup>+ e\<in>range (Pair x). pmf z e)"
        by(auto simp add: ennreal_pmf_map nn_integral_measure_pmf nn_integral_count_space_indicator intro!: nn_integral_cong split: split_indicator)
      also have "\<dots> = (\<Sum>\<^sup>+ y. h x y)"
        using bound by(simp add: nn_integral_count_space_reindex ennreal_enn2real_if)
      also have "\<dots> = (\<Sum>\<^sup>+y\<in>?B. h x y)" using outside
        by(auto simp add: nn_integral_count_space_indicator intro!: nn_integral_cong split: split_indicator)
      also have "\<dots> = ?f x" using p[of x] apply(cases "x \<in> set_pmf p")
        by(auto simp add: set_pmf_iff AE_count_space outside intro!: nn_integral_zero')
      finally show "pmf (map_pmf fst z) x = pmf p x" by simp
    qed

    show "map_pmf snd z = q"
    proof(rule pmf_eqI)
      fix y
      have "pmf (map_pmf snd z) y = (\<Sum>\<^sup>+ e\<in>range (\<lambda>x. (x, y)). pmf z e)"
        by(auto simp add: ennreal_pmf_map nn_integral_measure_pmf nn_integral_count_space_indicator intro!: nn_integral_cong split: split_indicator)
      also have "\<dots> = (\<Sum>\<^sup>+ x. h x y)"
        using bound by(simp add: nn_integral_count_space_reindex ennreal_enn2real_if)
      also have "\<dots> = (\<Sum>\<^sup>+x\<in>?A. h x y)" using outside
        by(auto simp add: nn_integral_count_space_indicator intro!: nn_integral_cong split: split_indicator)
      also have "\<dots> = ?g y" using q[of y] apply(cases "y \<in> set_pmf q")
        by(auto simp add: set_pmf_iff AE_count_space outside intro!: nn_integral_zero')
      finally show "pmf (map_pmf snd z) y = pmf q y" by simp
    qed
  qed
qed

corollary rel_pmf_distr_mono: "rel_pmf R OO rel_pmf S \<le> rel_pmf (R OO S)"
\<comment> \<open>This fact has already been proven for the registration of @{typ "'a pmf"} as a BNF,
  but this proof is much shorter and more elegant. See @{cite HoelzlLochbihlerTraytel2015ITP} for a
  comparison of formalisations.\<close>
proof(intro le_funI le_boolI rel_pmf_measureI, elim relcomppE)
  fix p q r A
  assume pq: "rel_pmf R p q" and qr: "rel_pmf S q r"
  have "measure (measure_pmf p) A \<le> measure (measure_pmf q) {y. \<exists>x\<in>A. R x y}"
    (is "_ \<le> measure _ ?B") using pq by(rule rel_pmf_measureD)
  also have "\<dots> \<le> measure (measure_pmf r) {z. \<exists>y\<in>?B. S y z}"
    using qr by(rule rel_pmf_measureD)
  also have "{z. \<exists>y\<in>?B. S y z} = {z. \<exists>x\<in>A. (R OO S) x z}" by auto
  finally show "measure (measure_pmf p) A \<le> measure (measure_pmf r) \<dots>" .
qed

subsection \<open>Code generation for @{const rel_pmf}\<close>

proposition rel_pmf_measureI':
  fixes p :: "'a pmf" and q :: "'b pmf"
  assumes le: "\<And>A. A \<subseteq> set_pmf p \<Longrightarrow> measure_pmf.prob p A \<le> measure_pmf.prob q {y \<in> set_pmf q. \<exists>x\<in>A. R x y}"
  shows "rel_pmf R p q"
proof(rule rel_pmf_measureI)
  fix A
  let ?A = "A \<inter> set_pmf p"
  have "measure_pmf.prob p A = measure_pmf.prob p ?A" by(simp add: measure_Int_set_pmf)
  also have "\<dots> \<le> measure_pmf.prob q {y \<in> set_pmf q. \<exists>x\<in>?A. R x y}" by(rule le) simp
  also have "\<dots> \<le> measure_pmf.prob q {y. \<exists>x\<in>A. R x y}"
    by(rule measure_pmf.finite_measure_mono) auto
  finally show "measure_pmf.prob p A \<le> \<dots>" .
qed

lemma rel_pmf_code [code]:
  "rel_pmf R p q \<longleftrightarrow>
   (let B = set_pmf q in
    \<forall>A\<in>Pow (set_pmf p). measure_pmf.prob p A \<le> measure_pmf.prob q (snd ` Set.filter (case_prod R) (A \<times> B)))"
  unfolding Let_def
proof(intro iffI strip)
  have eq: "snd ` Set.filter (case_prod R) (A \<times> set_pmf q) = {y. \<exists>x\<in>A. R x y} \<inter> set_pmf q" for A
    by(auto intro: rev_image_eqI simp add: Set.filter_def)
  show "measure_pmf.prob p A \<le> measure_pmf.prob q (snd ` Set.filter (case_prod R) (A \<times> set_pmf q))"
    if "rel_pmf R p q" and "A \<in> Pow (set_pmf p)" for A
    using that by(auto dest: rel_pmf_measureD simp add: eq measure_Int_set_pmf)
  show "rel_pmf R p q" if "\<forall>A\<in>Pow (set_pmf p). measure_pmf.prob p A \<le> measure_pmf.prob q (snd ` Set.filter (case_prod R) (A \<times> set_pmf q))"
    using that by(intro rel_pmf_measureI')(auto intro: ord_le_eq_trans arg_cong2[where f=measure] simp add: eq)
qed

end
