(* Author: R. Thiemann *)

subsection \<open>Perron-Frobenius theorem via Brouwer's fixpoint theorem.\<close>

theory Perron_Frobenius
imports
  "HOL-Analysis.Brouwer_Fixpoint"
  Perron_Frobenius_Aux
begin

text \<open>We follow the textbook proof of Serre \cite[Theorem 5.2.1]{SerreMatrices}.\<close>

context
  fixes A :: "complex ^ 'n ^ 'n :: finite"
  assumes rnnA: "real_non_neg_mat A"
begin

private abbreviation(input) sr where "sr \<equiv> spectral_radius A"

private definition max_v_ev :: "(complex^'n) \<times> complex" where
  "max_v_ev = (SOME v_ev. eigen_vector A (fst v_ev) (snd v_ev)
  \<and> norm (snd v_ev) = sr)"

private definition "max_v = (1 / norm1 (fst max_v_ev)) *\<^sub>R fst max_v_ev"
private definition "max_ev = snd max_v_ev"

private lemma max_v_ev:
  "eigen_vector A max_v max_ev"
  "norm max_ev = sr"
  "norm1 max_v = 1"
proof -
  obtain v ev where id: "max_v_ev = (v,ev)" by force
  from spectral_radius_ev[of A] someI_ex[of "\<lambda> v_ev. eigen_vector A (fst v_ev) (snd v_ev)
  \<and> norm (snd v_ev) = sr", folded max_v_ev_def, unfolded id]
  have v: "eigen_vector A v ev" and ev: "norm ev = sr" by auto
  from normalize_eigen_vector[OF v] ev
  show "eigen_vector A max_v max_ev" "norm max_ev = sr" "norm1 max_v = 1"
    unfolding max_v_def max_ev_def id by auto
qed

text \<open>In the definition of S, we use the linear norm instead of the
  default euclidean norm which is defined via the type-class.
  The reason is that S is not convex if one uses the euclidean norm.\<close>

private definition B :: "real ^ 'n ^ 'n" where "B \<equiv> \<chi> i j. Re (A $ i $ j)"
private definition S where "S = {v :: real ^ 'n . norm1 v = 1 \<and> (\<forall> i. v $ i \<ge> 0) \<and>
  (\<forall> i. (B *v v) $ i \<ge> sr * (v $ i))}"
private definition f :: "real ^ 'n \<Rightarrow> real ^ 'n" where
  "f v = (1 / norm1 (B *v v)) *\<^sub>R (B *v v)"

private lemma closedS: "closed S"
  unfolding S_def matrix_vector_mult_def[abs_def]
proof (intro closed_Collect_conj closed_Collect_all closed_Collect_le closed_Collect_eq)
  show "continuous_on UNIV norm1"
    by (simp add: continuous_at_imp_continuous_on)
qed (auto intro!: continuous_intros continuous_on_component)

private lemma boundedS: "bounded S"
proof -
  {
    fix v :: "real ^ 'n"
    from norm1_ge_norm[of v] have "norm1 v = 1 \<Longrightarrow> norm v \<le> 1" by auto
  }
  thus ?thesis
  unfolding S_def bounded_iff
  by (auto intro!: exI[of _ 1])
qed

private lemma compactS: "compact S"
  using boundedS closedS
  by (simp add: compact_eq_bounded_closed)

private lemmas rnn = real_non_neg_matD[OF rnnA]

lemma B_norm: "B $ i $ j = norm (A $ i $ j)"
  using rnn[of i j]
  by (cases "A $ i $ j", auto simp: B_def)

lemma mult_B_mono: assumes "\<And> i. v $ i \<ge> w $ i"
  shows "(B *v v) $ i \<ge> (B *v w) $ i" unfolding matrix_vector_mult_def vec_lambda_beta
  by (rule sum_mono, rule mult_left_mono[OF assms], unfold B_norm, auto)


private lemma non_emptyS: "S \<noteq> {}"
proof -
  let ?v = "(\<chi> i. norm (max_v $ i)) :: real ^ 'n"
  have "norm1 max_v = 1" by (rule max_v_ev(3))
  hence nv: "norm1 ?v = 1" unfolding norm1_def by auto
  {
    fix i
    have "sr * (?v $ i) = sr * norm (max_v $ i)" by auto
    also have "\<dots> = (norm max_ev) * norm (max_v $ i)" using max_v_ev by auto
    also have "\<dots> = norm ((max_ev *s max_v) $ i)" by (auto simp: norm_mult)
    also have "max_ev *s max_v = A *v max_v" using max_v_ev(1)[unfolded eigen_vector_def] by auto
    also have "norm ((A *v max_v) $ i) \<le> (B *v ?v) $ i"
      unfolding matrix_vector_mult_def vec_lambda_beta
      by (rule sum_norm_le, auto simp: norm_mult B_norm)
    finally have "sr * (?v $ i) \<le> (B *v ?v) $ i" .
  } note le = this
  have "?v \<in> S" unfolding S_def using nv le by auto
  thus ?thesis by blast
qed

private lemma convexS: "convex S"
proof (rule convexI)
  fix v w a b
  assume *: "v \<in> S" "w \<in> S" "0 \<le> a" "0 \<le> b" "a + b = (1 :: real)"
  let ?lin = "a *\<^sub>R v + b *\<^sub>R w"
  from * have 1: "norm1 v = 1" "norm1 w = 1" unfolding S_def by auto
  have "norm1 ?lin = a * norm1 v + b * norm1 w"
    unfolding norm1_def sum_distrib_left sum.distrib[symmetric]
  proof (rule sum.cong)
    fix i :: 'n
    from * have "v $ i \<ge> 0" "w $ i \<ge> 0" unfolding S_def by auto
    thus "norm (?lin $ i) = a * norm (v $ i) + b * norm (w $ i)"
      using *(3-4) by auto
  qed simp
  also have "\<dots> = 1" using *(5) 1 by auto
  finally have norm1: "norm1 ?lin = 1" .
  {
    fix i
    from * have "0 \<le> v $ i" "sr * v $ i \<le> (B *v v) $ i" unfolding S_def by auto
    with \<open>a \<ge> 0\<close> have a: "a * (sr * v $ i) \<le> a * (B *v v) $ i" by (intro mult_left_mono)
    from * have "0 \<le> w $ i" "sr * w $ i \<le> (B *v w) $ i" unfolding S_def by auto
    with \<open>b \<ge> 0\<close> have b: "b * (sr * w $ i) \<le> b * (B *v w) $ i" by (intro mult_left_mono)
    from a b have "a * (sr * v $ i) + b * (sr * w $ i) \<le> a * (B *v v) $ i + b * (B *v w) $ i" by auto
  } note le = this
  have switch[simp]: "\<And> x y. x * a * y = a * x * y"  "\<And> x y. x * b * y = b * x * y" by auto
  have [simp]: "x \<in> {v,w} \<Longrightarrow> a * (r * x $h i) = r * (a * x $h i)" for a r i x by auto
  show "a *\<^sub>R v + b *\<^sub>R w \<in> S" using * norm1 le unfolding S_def
    by (auto simp: matrix_vect_scaleR matrix_vector_right_distrib ring_distribs)
qed

private abbreviation (input) r :: "real \<Rightarrow> complex" where
  "r \<equiv> of_real"

private abbreviation rv :: "real ^'n \<Rightarrow> complex ^'n" where
  "rv v \<equiv> \<chi> i. r (v $ i)"

private lemma rv_0: "(rv v = 0) = (v = 0)"
  by (simp add: of_real_hom.map_vector_0 map_vector_def vec_eq_iff)

private lemma rv_mult: "A *v rv v = rv (B *v v)"
proof -
  have "map_matrix r B = A"
    using rnnA unfolding map_matrix_def B_def real_non_neg_mat_def map_vector_def elements_mat_h_def
    by vector
  thus ?thesis
    using of_real_hom.matrix_vector_mult_hom[of B, where 'a = complex]
    unfolding map_vector_def by auto
qed

context
  assumes zero_no_ev: "\<And> v. v \<in> S \<Longrightarrow> A *v rv v \<noteq> 0"
begin
private lemma normB_S: assumes v: "v \<in> S"
  shows "norm1 (B *v v) \<noteq> 0"
proof -
  from zero_no_ev[OF v, unfolded rv_mult rv_0]
  show ?thesis by auto
qed

private lemma image_f: "f ` S \<subseteq> S"
proof -
  {
    fix v
    assume v: "v \<in> S"
    hence norm: "norm1 v = 1" and ge: "\<And> i. v $ i \<ge> 0" "\<And> i. sr * v $ i \<le> (B *v v) $ i" unfolding S_def by auto
    from normB_S[OF v] have normB: "norm1 (B *v v) > 0" using norm1_nonzero by auto
    have fv: "f v = (1 / norm1 (B *v v)) *\<^sub>R (B *v v)" unfolding f_def by auto
    from normB have Bv0: "B *v v \<noteq> 0" unfolding norm1_0_iff[symmetric] by linarith
    have norm: "norm1 (f v) = 1" unfolding fv using normB Bv0 by simp
    define c where "c = (1 / norm1 (B *v v))"
    have c: "c > 0" unfolding c_def using normB by auto
    {
      fix i
      have 1: "f v $ i \<ge> 0" unfolding fv c_def[symmetric] using c ge
        by (auto simp: matrix_vector_mult_def sum_distrib_left B_norm intro!: sum_nonneg)
      have id1: "\<And> i. (B *v f v) $ i = c * ((B *v (B *v v)) $ i)"
        unfolding f_def c_def matrix_vect_scaleR by simp
      have id3: "\<And> i. sr * f v $ i = c * ((B *v (sr *\<^sub>R v)) $ i)"
        unfolding f_def c_def[symmetric] matrix_vect_scaleR by auto
      have 2: "sr * f v $ i \<le> (B *v f v) $ i" unfolding id1 id3
        unfolding real_mult_le_cancel_iff2[OF \<open>c > 0\<close>]
        by (rule mult_B_mono, insert ge(2), auto)
      note 1 2
    }
    with norm have "f v \<in> S" unfolding S_def by auto
  }
  thus ?thesis by blast
qed

private lemma cont_f: "continuous_on S f"
  unfolding f_def[abs_def] continuous_on using normB_S
  unfolding norm1_def
  by (auto intro!: tendsto_eq_intros)

qualified lemma perron_frobenius_positive_ev:
  "\<exists> v. eigen_vector A v (r sr) \<and> real_non_neg_vec v"
proof -
  from brouwer[OF compactS convexS non_emptyS cont_f image_f]
    obtain v where v: "v \<in> S" and fv: "f v = v" by auto
  define ev where "ev = norm1 (B *v v)"
  from normB_S[OF v] have "ev \<noteq> 0" unfolding ev_def by auto
  with norm1_ge_0[of "B *v v", folded ev_def] have norm: "ev > 0" by auto
  from arg_cong[OF fv[unfolded f_def], of "\<lambda> (w :: real ^ 'n). ev *\<^sub>R w"] norm
  have ev: "B *v v = ev *s v" unfolding ev_def[symmetric] scalar_mult_eq_scaleR by simp
  with v[unfolded S_def] have ge: "\<And> i. sr * v $ i \<le> ev * v $ i" by auto
  have "A *v rv v = rv (B *v v)" unfolding rv_mult ..
  also have "\<dots> = ev *s rv v" unfolding ev vec_eq_iff
    by (simp add: scaleR_conv_of_real scaleR_vec_def)
  finally have ev: "A *v rv v = ev *s rv v" .
  from v have v0: "v \<noteq> 0" unfolding S_def by auto
  hence "rv v \<noteq> 0" unfolding rv_0 .
  with ev have ev: "eigen_vector A (rv v) ev" unfolding eigen_vector_def by auto
  hence "eigen_value A ev" unfolding eigen_value_def by auto
  from spectral_radius_max[OF this] have le: "norm (r ev) \<le> sr" .
  from v0 obtain i where "v $ i \<noteq> 0" unfolding vec_eq_iff by auto
  from v have "v $ i \<ge> 0" unfolding S_def by auto
  with \<open>v $ i \<noteq> 0\<close> have "v $ i > 0" by auto
  with ge[of i] have ge: "sr \<le> ev" by auto
  with le have sr: "r sr = ev" by auto
  from v have *: "real_non_neg_vec (rv v)" unfolding S_def real_non_neg_vec_def vec_elements_h_def by auto
  show ?thesis unfolding sr
    by (rule exI[of _ "rv v"], insert * ev norm, auto)
qed
end

qualified lemma perron_frobenius_both:
  "\<exists> v. eigen_vector A v (r sr) \<and> real_non_neg_vec v"
proof (cases "\<forall> v \<in> S. A *v rv v \<noteq> 0")
  case True
  show ?thesis
    by (rule Perron_Frobenius.perron_frobenius_positive_ev[OF rnnA], insert True, auto)
next
  case False
  then obtain v where v: "v \<in> S" and A0: "A *v rv v = 0" by auto
  hence id: "A *v rv v = 0 *s rv v" and v0: "v \<noteq> 0" unfolding S_def by auto
  from v0 have "rv v \<noteq> 0" unfolding rv_0 .
  with id have ev: "eigen_vector A (rv v) 0" unfolding eigen_vector_def by auto
  hence "eigen_value A 0" unfolding eigen_value_def ..
  from spectral_radius_max[OF this] have 0: "0 \<le> sr" by auto
  from v[unfolded S_def] have ge: "\<And> i. sr * v $ i \<le> (B *v v) $ i" by auto
  from v[unfolded S_def] have rnn: "real_non_neg_vec (rv v)"
    unfolding real_non_neg_vec_def vec_elements_h_def by auto
  from v0 obtain i where "v $ i \<noteq> 0" unfolding vec_eq_iff by auto
  from v have "v $ i \<ge> 0" unfolding S_def by auto
  with \<open>v $ i \<noteq> 0\<close> have vi: "v $ i > 0" by auto
  from rv_mult[of v, unfolded A0] have "rv (B *v v) = 0" by simp
  hence "B *v v = 0" unfolding rv_0 .
  from ge[of i, unfolded this] vi have ge: "sr \<le> 0" by (simp add: mult_le_0_iff)
  with \<open>0 \<le> sr\<close> have "sr = 0" by auto
  show ?thesis unfolding \<open>sr = 0\<close> using rnn ev by auto
qed
end

text \<open>Perron Frobenius: The largest complex eigenvalue of a real-valued non-negative matrix
  is a real one, and it has a real-valued non-negative eigenvector.\<close>

lemma perron_frobenius:
  assumes "real_non_neg_mat A"
  shows "\<exists>v. eigen_vector A v (of_real (spectral_radius A)) \<and> real_non_neg_vec v"
  by (rule Perron_Frobenius.perron_frobenius_both[OF assms])

text \<open>And a version which ignores the eigenvector.\<close>

lemma perron_frobenius_eigen_value:
  assumes "real_non_neg_mat A"
  shows "eigen_value A (of_real (spectral_radius A))"
  using perron_frobenius[OF assms] unfolding eigen_value_def by blast

end
