(*
  Theory: Density_Predicates.thy
  Authors: Manuel Eberl
*)

section \<open>Density Predicates\<close>

theory Density_Predicates
imports "HOL-Probability.Probability"
begin

subsection \<open>Probability Densities\<close>

definition is_subprob_density :: "'a measure \<Rightarrow> ('a \<Rightarrow> ennreal) \<Rightarrow> bool" where
  "is_subprob_density M f \<equiv> (f \<in> borel_measurable M) \<and> space M \<noteq> {} \<and>
                           (\<forall>x\<in>space M. f x \<ge> 0) \<and> (\<integral>\<^sup>+x. f x \<partial>M) \<le> 1"

lemma is_subprob_densityI[intro]:
    "\<lbrakk>f \<in> borel_measurable M; \<And>x. x \<in> space M \<Longrightarrow> f x \<ge> 0; space M \<noteq> {}; (\<integral>\<^sup>+x. f x \<partial>M) \<le> 1\<rbrakk>
        \<Longrightarrow> is_subprob_density M f"
  unfolding is_subprob_density_def by simp

lemma is_subprob_densityD[dest]:
  "is_subprob_density M f \<Longrightarrow> f \<in> borel_measurable M"
  "is_subprob_density M f \<Longrightarrow> x \<in> space M \<Longrightarrow> f x \<ge> 0"
  "is_subprob_density M f \<Longrightarrow> space M \<noteq> {}"
  "is_subprob_density M f \<Longrightarrow> (\<integral>\<^sup>+x. f x \<partial>M) \<le> 1"
  unfolding is_subprob_density_def by simp_all

subsection \<open>Measure spaces with densities\<close>

definition has_density :: "'a measure \<Rightarrow> 'a measure \<Rightarrow> ('a \<Rightarrow> ennreal) \<Rightarrow> bool" where
  "has_density M N f \<longleftrightarrow> (f \<in> borel_measurable N) \<and> space N \<noteq> {} \<and> M = density N f"

lemma has_densityI[intro]:
  "\<lbrakk>f \<in> borel_measurable N; M = density N f; space N \<noteq> {}\<rbrakk> \<Longrightarrow> has_density M N f"
  unfolding has_density_def by blast

lemma has_densityD:
  assumes "has_density M N f"
  shows "f \<in> borel_measurable N" "M = density N f" "space N \<noteq> {}"
using assms unfolding has_density_def by simp_all


lemma has_density_sets: "has_density M N f \<Longrightarrow> sets M = sets N"
  unfolding has_density_def by simp

lemma has_density_space: "has_density M N f \<Longrightarrow> space M = space N"
  unfolding has_density_def by simp

lemma has_density_emeasure:
    "has_density M N f \<Longrightarrow> X \<in> sets M \<Longrightarrow> emeasure M X = \<integral>\<^sup>+x. f x * indicator X x \<partial>N"
  unfolding has_density_def by (simp_all add: emeasure_density)

lemma nn_integral_cong': "(\<And>x. x \<in> space N =simp=> f x = g x) \<Longrightarrow> (\<integral>\<^sup>+x. f x \<partial>N) = (\<integral>\<^sup>+x. g x \<partial>N)"
  by (simp add: simp_implies_def cong: nn_integral_cong)

lemma has_density_emeasure_space:
    "has_density M N f \<Longrightarrow> emeasure M (space M) = (\<integral>\<^sup>+x. f x \<partial>N)"
  by (simp add: has_density_emeasure) (simp add: has_density_space cong: nn_integral_cong')

lemma has_density_emeasure_space':
    "has_density M N f \<Longrightarrow> emeasure (density N f) (space (density N f)) = \<integral>\<^sup>+x. f x \<partial>N"
  by (frule has_densityD(2)[symmetric]) (simp add: has_density_emeasure_space)

lemma has_density_imp_is_subprob_density:
    "\<lbrakk>has_density M N f; (\<integral>\<^sup>+x. f x \<partial>N) = 1\<rbrakk> \<Longrightarrow> is_subprob_density N f"
  by (auto dest: has_densityD)

lemma has_density_imp_is_subprob_density':
    "\<lbrakk>has_density M N f; prob_space M\<rbrakk> \<Longrightarrow> is_subprob_density N f"
  by (auto intro!: has_density_imp_is_subprob_density dest: prob_space.emeasure_space_1
           simp: has_density_emeasure_space)

lemma has_density_equal_on_space:
  assumes "has_density M N f" "\<And>x. x \<in> space N \<Longrightarrow> f x = g x"
  shows "has_density M N g"
proof
  from assms show "g \<in> borel_measurable N"
    by (subst measurable_cong[of _ _ f]) (auto dest: has_densityD)
  with assms show "M = density N g"
    by (subst density_cong[of _ _ f]) (auto dest: has_densityD)
  from assms(1) show "space N \<noteq> {}" by (rule has_densityD)
qed

lemma has_density_cong:
  assumes "\<And>x. x \<in> space N \<Longrightarrow> f x = g x"
  shows "has_density M N f = has_density M N g"
using assms by (intro iffI) (erule has_density_equal_on_space, simp)+

lemma has_density_dens_AE:
    "\<lbrakk>AE y in N. f y = f' y; f' \<in> borel_measurable N;
      \<And>x. x \<in> space M \<Longrightarrow> f' x \<ge> 0; has_density M N f\<rbrakk>
        \<Longrightarrow> has_density M N f'"
  unfolding has_density_def by (simp cong: density_cong)


subsection \<open>Probability spaces with densities\<close>

lemma is_subprob_density_imp_has_density:
    "\<lbrakk>is_subprob_density N f; M = density N f\<rbrakk> \<Longrightarrow> has_density M N f"
  by (rule has_densityI) auto

lemma has_subprob_density_imp_subprob_space':
    "\<lbrakk>has_density M N f; is_subprob_density N f\<rbrakk> \<Longrightarrow> subprob_space M"
proof (rule subprob_spaceI)
  assume "has_density M N f"
  hence "M = density N f" by (simp add: has_density_def)
  also from \<open>has_density M N f\<close> have "space ... \<noteq> {}" by (simp add: has_density_def)
  finally show "space M \<noteq> {}" .
qed (auto simp add: has_density_emeasure_space dest: has_densityD)

lemma has_subprob_density_imp_subprob_space[dest]:
    "is_subprob_density M f \<Longrightarrow> subprob_space (density M f)"
  by (rule has_subprob_density_imp_subprob_space') auto

definition "has_subprob_density M N f \<equiv> has_density M N f \<and> subprob_space M"

(* TODO: Move *)
lemma subprob_space_density_not_empty: "subprob_space (density M f) \<Longrightarrow> space M \<noteq> {}"
  by (subst space_density[symmetric], subst subprob_space.subprob_not_empty, assumption) simp

lemma has_subprob_densityI:
  "\<lbrakk>f \<in> borel_measurable N; M = density N f; subprob_space M\<rbrakk> \<Longrightarrow> has_subprob_density M N f"
  unfolding has_subprob_density_def by (auto simp: subprob_space_density_not_empty)

lemma has_subprob_densityI':
  assumes "f \<in> borel_measurable N" "space N \<noteq> {}"
          "M = density N f" "(\<integral>\<^sup>+x. f x \<partial>N) \<le> 1"
  shows "has_subprob_density M N f"
proof-
  from assms have D: "has_density M N f" by blast
  moreover from D and assms have "subprob_space M"
    by (auto intro!: subprob_spaceI simp: has_density_emeasure_space emeasure_density
             cong: nn_integral_cong')
  ultimately show ?thesis unfolding has_subprob_density_def by simp
qed

lemma has_subprob_densityD:
  assumes "has_subprob_density M N f"
  shows "f \<in> borel_measurable N" "\<And>x. x \<in> space N \<Longrightarrow> f x \<ge> 0" "M = density N f" "subprob_space M"
using assms unfolding has_subprob_density_def by (auto dest: has_densityD)

lemma has_subprob_density_measurable[measurable_dest]:
  "has_subprob_density M N f \<Longrightarrow> f \<in> N \<rightarrow>\<^sub>M borel"
  by (auto dest: has_subprob_densityD)

lemma has_subprob_density_imp_has_density:
  "has_subprob_density M N f \<Longrightarrow> has_density M N f" by (simp add: has_subprob_density_def)

lemma has_subprob_density_equal_on_space:
  assumes "has_subprob_density M N f" "\<And>x. x \<in> space N \<Longrightarrow> f x = g x"
  shows "has_subprob_density M N g"
using assms unfolding has_subprob_density_def by (auto dest: has_density_equal_on_space)

lemma has_subprob_density_cong:
  assumes "\<And>x. x \<in> space N \<Longrightarrow> f x = g x"
  shows "has_subprob_density M N f = has_subprob_density M N g"
using assms by (intro iffI) (erule has_subprob_density_equal_on_space, simp)+

lemma has_subprob_density_dens_AE:
    "\<lbrakk>AE y in N. f y = f' y; f' \<in> borel_measurable N;
      \<And>x. x \<in> space M \<Longrightarrow> f' x \<ge> 0; has_subprob_density M N f\<rbrakk>
      \<Longrightarrow> has_subprob_density M N f'"
  unfolding has_subprob_density_def by (simp add: has_density_dens_AE)


subsection \<open>Parametrized probability densities\<close>

definition
  "has_parametrized_subprob_density M N R f \<equiv>
       (\<forall>x \<in> space M. has_subprob_density (N x) R (f x)) \<and> case_prod f \<in> borel_measurable (M \<Otimes>\<^sub>M R)"

lemma has_parametrized_subprob_densityI:
  assumes "\<And>x. x \<in> space M \<Longrightarrow> N x = density R (f x)"
  assumes "\<And>x. x \<in> space M \<Longrightarrow> subprob_space (N x)"
  assumes "case_prod f \<in> borel_measurable (M \<Otimes>\<^sub>M R)"
  shows "has_parametrized_subprob_density M N R f"
  unfolding has_parametrized_subprob_density_def using assms
  by (intro ballI conjI has_subprob_densityI) simp_all

lemma has_parametrized_subprob_densityD:
  assumes "has_parametrized_subprob_density M N R f"
  shows "\<And>x. x \<in> space M \<Longrightarrow> N x = density R (f x)"
    and "\<And>x. x \<in> space M \<Longrightarrow> subprob_space (N x)"
    and [measurable_dest]: "case_prod f \<in> borel_measurable (M \<Otimes>\<^sub>M R)"
  using assms unfolding has_parametrized_subprob_density_def
  by (auto dest: has_subprob_densityD)

lemma has_parametrized_subprob_density_integral:
  assumes "has_parametrized_subprob_density M N R f" "x \<in> space M"
  shows "(\<integral>\<^sup>+y. f x y \<partial>R) \<le> 1"
proof-
  have "(\<integral>\<^sup>+y. f x y \<partial>R) = emeasure (density R (f x)) (space (density R (f x)))" using assms
    by (auto simp: emeasure_density cong: nn_integral_cong' dest: has_parametrized_subprob_densityD)
  also have "density R (f x) = (N x)" using assms by (auto dest: has_parametrized_subprob_densityD)
  also have "emeasure ... (space ...) \<le> 1" using assms
    by (subst subprob_space.emeasure_space_le_1) (auto dest: has_parametrized_subprob_densityD)
  finally show ?thesis .
qed

lemma has_parametrized_subprob_density_cong:
  assumes "\<And>x. x \<in> space M \<Longrightarrow> N x = N' x"
  shows "has_parametrized_subprob_density M N R f = has_parametrized_subprob_density M N' R f"
using assms unfolding has_parametrized_subprob_density_def by auto

lemma has_parametrized_subprob_density_dens_AE:
  assumes "\<And>x. x \<in> space M \<Longrightarrow> AE y in R. f x y = f' x y"
          "case_prod f' \<in> borel_measurable (M \<Otimes>\<^sub>M R)"
          "has_parametrized_subprob_density M N R f"
  shows   "has_parametrized_subprob_density M N R f'"
unfolding has_parametrized_subprob_density_def
proof (intro conjI ballI)
  fix x assume x: "x \<in> space M"
  with assms(3) have "space (N x) = space R"
    by (auto dest!: has_parametrized_subprob_densityD(1))
  with assms and x show "has_subprob_density (N x) R (f' x)"
    by (rule_tac has_subprob_density_dens_AE[of "f x"])
       (auto simp: has_parametrized_subprob_density_def)
qed fact


subsection \<open>Density in the Giry monad\<close>

lemma emeasure_bind_density:
  assumes "space M \<noteq> {}" "\<And>x. x \<in> space M \<Longrightarrow> has_density (f x) N (g x)"
          "f \<in> measurable M (subprob_algebra N)" "X \<in> sets N"
  shows "emeasure (M \<bind> f) X = \<integral>\<^sup>+x. \<integral>\<^sup>+y. g x y * indicator X y \<partial>N \<partial>M"
proof-
  from assms have "emeasure (M \<bind> f) X = \<integral>\<^sup>+x. emeasure (f x) X \<partial>M"
    by (intro emeasure_bind)
  also have "... = \<integral>\<^sup>+x. \<integral>\<^sup>+y. g x y * indicator X y \<partial>N \<partial>M" using assms
    by (intro nn_integral_cong) (simp add: has_density_emeasure sets_kernel)
  finally show ?thesis .
qed

lemma bind_density:
  assumes "sigma_finite_measure M" "sigma_finite_measure N"
          "space M \<noteq> {}" "\<And>x. x \<in> space M \<Longrightarrow> has_density (f x) N (g x)"
     and [measurable]: "case_prod g \<in> borel_measurable (M \<Otimes>\<^sub>M N)" "f \<in> measurable M (subprob_algebra N)"
  shows "(M \<bind> f) = density N (\<lambda>y. \<integral>\<^sup>+x. g x y \<partial>M)"
proof (rule measure_eqI)
  interpret sfN: sigma_finite_measure N by fact
  interpret sfNM: pair_sigma_finite N M unfolding pair_sigma_finite_def using assms by simp
  show eq: "sets (M \<bind> f) = sets (density N (\<lambda>y. \<integral>\<^sup>+x. g x y \<partial>M))"
    using sets_bind[OF sets_kernel[OF assms(6)] assms(3)] by auto
  fix X assume "X \<in> sets (M \<bind> f)"
  with eq have [measurable]: "X \<in> sets N" by auto
  with assms have "emeasure (M \<bind> f) X = \<integral>\<^sup>+x. \<integral>\<^sup>+y. g x y * indicator X y \<partial>N \<partial>M"
    by (intro emeasure_bind_density) simp_all
  also from \<open>X \<in> sets N\<close> have "... = \<integral>\<^sup>+y. \<integral>\<^sup>+x. g x y * indicator X y \<partial>M \<partial>N"
    by (intro sfNM.Fubini') measurable
  also {
    fix y assume "y \<in> space N"
    have "(\<lambda>x. g x y) = case_prod g \<circ> (\<lambda>x. (x, y))" by (rule ext) simp
    also from \<open>y \<in> space N\<close> have "... \<in> borel_measurable M"
      by (intro measurable_comp[OF _ assms(5)] measurable_Pair2')
    finally have "(\<lambda>x. g x y) \<in> borel_measurable M" .
  }
  hence "... = \<integral>\<^sup>+y. (\<integral>\<^sup>+x. g x y \<partial>M) * indicator X y \<partial>N"
    by (intro nn_integral_cong nn_integral_multc)  simp_all
  also from \<open>X \<in> sets N\<close> and assms have "... = emeasure (density N (\<lambda>y. \<integral>\<^sup>+x. g x y \<partial>M)) X"
    by (subst emeasure_density) (simp_all add: sfN.borel_measurable_nn_integral)
  finally show "emeasure (M \<bind> f) X = emeasure (density N (\<lambda>y. \<integral>\<^sup>+x. g x y \<partial>M)) X" .
qed


lemma bind_has_density:
  assumes "sigma_finite_measure M" "sigma_finite_measure N"
          "space M \<noteq> {}" "\<And>x. x \<in> space M \<Longrightarrow> has_density (f x) N (g x)"
          "case_prod g \<in> borel_measurable (M \<Otimes>\<^sub>M N)"
          "f \<in> measurable M (subprob_algebra N)"
  shows "has_density (M \<bind> f) N (\<lambda>y. \<integral>\<^sup>+x. g x y \<partial>M)"
proof
  interpret sigma_finite_measure M by fact
  show "(\<lambda>y. \<integral>\<^sup>+ x. g x y \<partial>M) \<in> borel_measurable N" using assms
    by (intro borel_measurable_nn_integral, subst measurable_pair_swap_iff) simp
  show "M \<bind> f = density N (\<lambda>y. \<integral>\<^sup>+ x. g x y \<partial>M)"
    by (intro bind_density) (simp_all add: assms)
  from \<open>space M \<noteq> {}\<close> obtain x where "x \<in> space M" by blast
  with assms have "has_density (f x) N (g x)" by simp
  thus "space N \<noteq> {}" by (rule has_densityD)
qed

lemma bind_has_density':
  assumes sfM: "sigma_finite_measure M"
      and sfR: "sigma_finite_measure R"
      and not_empty: "space M \<noteq> {}" and dens_M: "has_density M N \<delta>M"
      and dens_f: "\<And>x. x \<in> space M \<Longrightarrow> has_density (f x) R (\<delta>f x)"
      and M\<delta>f: "case_prod \<delta>f \<in> borel_measurable (N \<Otimes>\<^sub>M R)"
      and Mf: "f \<in> measurable N (subprob_algebra R)"
  shows "has_density (M \<bind> f) R (\<lambda>y. \<integral>\<^sup>+x. \<delta>M x * \<delta>f x y \<partial>N)"
proof-
  from dens_M have M_M: "measurable M = measurable N"
    by (intro ext measurable_cong_sets) (auto dest: has_densityD)
  from dens_M have M_MR: "measurable (M \<Otimes>\<^sub>M R) = measurable (N \<Otimes>\<^sub>M R)"
    by (intro ext measurable_cong_sets sets_pair_measure_cong) (auto dest: has_densityD)
  have "has_density (M \<bind> f) R (\<lambda>y. \<integral>\<^sup>+x. \<delta>f x y \<partial>M)"
    by (rule bind_has_density) (auto simp: assms M_MR M_M)
  moreover {
    fix y assume A: "y \<in> space R"
    have "(\<lambda>x. \<delta>f x y) = case_prod \<delta>f \<circ> (\<lambda>x. (x,y))" by (rule ext) (simp add: o_def)
    also have "... \<in> borel_measurable N" by (intro measurable_comp[OF _ M\<delta>f] measurable_Pair2' A)
    finally have M_\<delta>f': "(\<lambda>x. \<delta>f x y) \<in> borel_measurable N" .

    from dens_M have "M = density N \<delta>M" by (auto dest: has_densityD)
    also from dens_M have "(\<integral>\<^sup>+x. \<delta>f x y \<partial>...) = \<integral>\<^sup>+x. \<delta>M x * \<delta>f x y \<partial>N"
      by (subst nn_integral_density) (auto dest: has_densityD simp: M_\<delta>f')
    finally have "(\<integral>\<^sup>+x. \<delta>f x y \<partial>M) = \<integral>\<^sup>+x. \<delta>M x * \<delta>f x y \<partial>N" .
  }
  ultimately show "has_density (M \<bind> f) R (\<lambda>y. \<integral>\<^sup>+x. \<delta>M x * \<delta>f x y \<partial>N)"
    by (rule has_density_equal_on_space) simp_all
qed

lemma bind_has_subprob_density:
  assumes "subprob_space M" "sigma_finite_measure N"
          "space M \<noteq> {}" "\<And>x. x \<in> space M \<Longrightarrow> has_density (f x) N (g x)"
          "case_prod g \<in> borel_measurable (M \<Otimes>\<^sub>M N)"
          "f \<in> measurable M (subprob_algebra N)"
  shows "has_subprob_density (M \<bind> f) N (\<lambda>y. \<integral>\<^sup>+x. g x y \<partial>M)"
proof (unfold has_subprob_density_def, intro conjI)
  from assms show "has_density (M \<bind> f) N (\<lambda>y. \<integral>\<^sup>+x. g x y \<partial>M)"
    by (intro bind_has_density) (auto simp: subprob_space_imp_sigma_finite)
  from assms show "subprob_space (M \<bind> f)" by (intro subprob_space_bind)
qed

lemma bind_has_subprob_density':
  assumes "has_subprob_density M N \<delta>M" "space R \<noteq> {}" "sigma_finite_measure R"
          "\<And>x. x \<in> space M \<Longrightarrow> has_subprob_density (f x) R (\<delta>f x)"
          "case_prod \<delta>f \<in> borel_measurable (N \<Otimes>\<^sub>M R)" "f \<in> measurable N (subprob_algebra R)"
  shows "has_subprob_density (M \<bind> f) R (\<lambda>y. \<integral>\<^sup>+x. \<delta>M x * \<delta>f x y \<partial>N)"
proof (unfold has_subprob_density_def, intro conjI)
  from assms(1) have "space M \<noteq> {}" by (intro subprob_space.subprob_not_empty has_subprob_densityD)
  with assms show "has_density (M \<bind> f) R (\<lambda>y. \<integral>\<^sup>+x. \<delta>M x * \<delta>f x y \<partial>N)"
    by (intro bind_has_density' has_densityI)
       (auto simp: subprob_space_imp_sigma_finite dest: has_subprob_densityD)
  from assms show "subprob_space (M \<bind> f)"
    by (intro subprob_space_bind) (auto dest: has_subprob_densityD)
qed

lemma null_measure_has_subprob_density:
  "space M \<noteq> {} \<Longrightarrow> has_subprob_density (null_measure M) M (\<lambda>_. 0)"
  by (intro has_subprob_densityI)
     (auto intro: null_measure_eq_density simp: subprob_space_null_measure_iff)

lemma emeasure_has_parametrized_subprob_density:
  assumes "has_parametrized_subprob_density M N R f"
  assumes "x \<in> space M" "X \<in> sets R"
  shows "emeasure (N x) X = \<integral>\<^sup>+y. f x y * indicator X y \<partial>R"
proof-
  from has_parametrized_subprob_densityD(3)[OF assms(1)] and assms(2)
    have Mf: "f x \<in> borel_measurable R" by simp
  have "N x = density R (f x)"
    by (rule has_parametrized_subprob_densityD(1)[OF assms(1,2)])
  also from Mf and assms(3) have "emeasure ... X = \<integral>\<^sup>+y. f x y * indicator X y \<partial>R"
    by (rule emeasure_density)
  finally show ?thesis .
qed

lemma emeasure_count_space_density_singleton:
  assumes "x \<in> A" "has_density M (count_space A) f"
  shows "emeasure M {x} = f x"
proof-
  from has_densityD[OF assms(2)] have nonneg: "\<And>x. x \<in> A \<Longrightarrow> f x \<ge> 0" by simp
  from assms have M: "M = density (count_space A) f" by (intro has_densityD)
  from assms have "emeasure M {x} = \<integral>\<^sup>+y. f y * indicator {x} y \<partial>count_space A"
    by (simp add: M emeasure_density)
  also from assms and nonneg have "... = f x"
    by (subst nn_integral_indicator_singleton) auto
  finally show ?thesis .
qed

lemma subprob_count_space_density_le_1:
  assumes "has_subprob_density M (count_space A) f" "x \<in> A"
  shows "f x \<le> 1"
proof (cases "f x > 0")
  assume "f x > 0"
  from assms interpret subprob_space M by (intro has_subprob_densityD)
  from assms have M: "M = density (count_space A) f" by (intro has_subprob_densityD)
  from assms have "f x = emeasure M {x}"
    by (intro emeasure_count_space_density_singleton[symmetric])
       (auto simp: has_subprob_density_def)
  also have "... \<le> 1" by (rule subprob_emeasure_le_1)
  finally show ?thesis .
qed (auto simp: not_less intro: order.trans[of _ 0 1])

lemma has_density_embed_measure:
  assumes inj: "inj f" and inv: "\<And>x. x \<in> space N \<Longrightarrow> f' (f x) = x"
  shows "has_density (embed_measure M f) (embed_measure N f) (\<delta> \<circ> f') \<longleftrightarrow> has_density M N \<delta>"
        (is "has_density ?M' ?N' ?\<delta>' \<longleftrightarrow> has_density M N \<delta>")
proof
  assume dens: "has_density ?M' ?N' ?\<delta>'"
  show "has_density M N \<delta>"
  proof
    from dens show "space N \<noteq> {}" by (auto simp: space_embed_measure dest: has_densityD)
    from dens have M\<delta>f': "\<delta> \<circ> f' \<in> borel_measurable ?N'" by (rule has_densityD)
    hence M\<delta>f'f: "\<delta> \<circ> f' \<circ> f \<in> borel_measurable N"
      by (rule_tac measurable_comp, rule_tac measurable_embed_measure2[OF inj])
    thus M\<delta>: "\<delta> \<in> borel_measurable N" by (simp cong: measurable_cong add: inv)
    from dens have "embed_measure M f = density (embed_measure N f) (\<delta> \<circ> f')" by (rule has_densityD)
    also have "... = embed_measure (density N (\<delta> \<circ> f' \<circ> f)) f"
      by (simp only: density_embed_measure[OF inj M\<delta>f'])
    also have "density N (\<delta> \<circ> f' \<circ> f) = density N \<delta>"
      by (intro density_cong[OF M\<delta>f'f M\<delta>]) (simp_all add: inv)
    finally show "M = density N \<delta>" by (simp add: embed_measure_eq_iff[OF inj])
  qed
next
  assume dens: "has_density M N \<delta>"
  show "has_density ?M' ?N' ?\<delta>'"
  proof
    from dens show "space ?N' \<noteq> {}" by (auto simp: space_embed_measure dest: has_densityD)
    have Mf'f: "(\<lambda>x. f' (f x)) \<in> measurable N N" by (subst measurable_cong[OF inv]) simp_all
    from dens have M\<delta>: "\<delta> \<in> borel_measurable N" by (auto dest: has_densityD)
    from Mf'f and dens show M\<delta>f': "\<delta> \<circ> f' \<in> borel_measurable (embed_measure N f)"
      by (intro measurable_comp) (erule measurable_embed_measure1, rule has_densityD)
    have "embed_measure M f = embed_measure (density N \<delta>) f"
      by (simp only: has_densityD[OF dens])
    also from inv and dens and measurable_comp[OF Mf'f M\<delta>]
      have "density N \<delta> = density N (?\<delta>' \<circ> f)"
      by (intro density_cong[OF M\<delta>]) (simp add: o_def, simp add: inv o_def)
    also have "embed_measure (density N (?\<delta>' \<circ> f)) f = density (embed_measure N f) (\<delta> \<circ> f')"
      by (simp only: density_embed_measure[OF inj M\<delta>f', symmetric])
    finally show "embed_measure M f = density (embed_measure N f) (\<delta> \<circ> f')" .
  qed
qed

lemma has_density_embed_measure':
  assumes inj: "inj f" and inv: "\<And>x. x \<in> space N \<Longrightarrow> f' (f x) = x" and
          sets_M: "sets M = sets (embed_measure N f)"
  shows "has_density (distr M N f') N (\<delta> \<circ> f) \<longleftrightarrow> has_density M (embed_measure N f) \<delta>"
proof-
  have sets': "sets (embed_measure (distr M N f') f) = sets (embed_measure N f)"
    by (simp add: sets_embed_measure[OF inj])
  have Mff': "(\<lambda>x. f' (f x)) \<in> measurable N N" by (subst measurable_cong[OF inv]) simp_all
  have inv': "\<And>x. x \<in> space M \<Longrightarrow> f (f' x) = x"
    by (subst (asm) sets_eq_imp_space_eq[OF sets_M]) (auto simp: space_embed_measure inv)
  have "M = distr M (embed_measure (distr M N f') f) (\<lambda>x. f (f' x))"
    by (subst distr_cong[OF refl _ inv', of _ M]) (simp_all add: sets_embed_measure inj sets_M)
  also have "... = embed_measure (distr M N f') f"
    apply (subst (2) embed_measure_eq_distr[OF inj], subst distr_distr)
    apply (subst measurable_cong_sets[OF refl sets'], rule measurable_embed_measure2[OF inj])
    apply (subst measurable_cong_sets[OF sets_M refl], rule measurable_embed_measure1, rule Mff')
    apply (simp cong: distr_cong add: inv)
    done
  finally have M: "M = embed_measure (distr M N f') f" .
  show ?thesis by (subst (2) M, subst has_density_embed_measure[OF inj inv, symmetric])
                  (auto simp: space_embed_measure inv intro!: has_density_cong)
qed

lemma has_density_embed_measure'':
  assumes inj: "inj f" and inv: "\<And>x. x \<in> space N \<Longrightarrow> f' (f x) = x" and
          "has_density M (embed_measure N f) \<delta>"
  shows "has_density (distr M N f') N (\<delta> \<circ> f)"
proof (subst has_density_embed_measure')
  from assms(3) show "sets M = sets (embed_measure N f)" by (auto dest: has_densityD)
qed (insert assms)

lemma has_subprob_density_embed_measure'':
  assumes inj: "inj f" and inv: "\<And>x. x \<in> space N \<Longrightarrow> f' (f x) = x" and
          "has_subprob_density M (embed_measure N f) \<delta>"
  shows "has_subprob_density (distr M N f') N (\<delta> \<circ> f)"
proof (unfold has_subprob_density_def, intro conjI)
  from assms show "has_density (distr M N f') N (\<delta> \<circ> f)"
    by (intro has_density_embed_measure'' has_subprob_density_imp_has_density)
  from assms(3) have "sets M = sets (embed_measure N f)" by (auto dest: has_subprob_densityD)
  hence M: "measurable M = measurable (embed_measure N f)"
    by (intro ext measurable_cong_sets) simp_all
  have "(\<lambda>x. f' (f x)) \<in> measurable N N" by (simp cong: measurable_cong add: inv)
  moreover from assms have "space (embed_measure N f) \<noteq> {}"
    unfolding has_subprob_density_def has_density_def by simp
  ultimately show "subprob_space (distr M N f')" using assms
    by (intro subprob_space.subprob_space_distr has_subprob_densityD)
       (auto simp: M space_embed_measure intro!: measurable_embed_measure1 dest: has_subprob_densityD)
qed (insert assms)

end
