(*  Title:      Martingale.thy
    Author:     Mnacho Echenim, Univ. Grenoble Alpes
*)

section \<open>Martingales\<close>

theory Martingale imports Filtration
begin

definition martingale  where
  "martingale M F X  \<longleftrightarrow>
    (filtration M F) \<and> (\<forall>t. integrable M (X t)) \<and> (borel_adapt_stoch_proc F X) \<and>
    (\<forall>t s. t \<le> s \<longrightarrow> (AE w in M. real_cond_exp M (F t) (X s) w = X t w))"

lemma martingaleAE:
  assumes "martingale M F X"
  and "t \<le> s"
shows "AE w in M. real_cond_exp M (F t) (X s) w = (X t) w" using assms unfolding martingale_def by simp




lemma martingale_add:
  assumes "martingale M F X"
  and "martingale M F Y"
  and "\<forall>m. sigma_finite_subalgebra M (F m)"
shows "martingale M F (\<lambda>n w. X n w + Y n w)" unfolding martingale_def
proof (intro conjI)
  let ?sum = "\<lambda>n w. X n w + Y n w"
  show "\<forall>n. integrable M (\<lambda>w. X n w + Y n w)"
  proof
    fix n
    show "integrable M (\<lambda>w. X n w + Y n w)"
      by (metis Bochner_Integration.integrable_add assms(1) assms(2) martingale_def)
  qed
  show "\<forall>n m. n \<le> m \<longrightarrow> (AE w in M. real_cond_exp M (F n) (\<lambda>w. X m w + Y m w) w = X n w + Y n w)"
  proof (intro allI impI)
    fix n::'b
    fix m
    assume "n \<le> m"
    show "AE w in M. real_cond_exp M (F n) (\<lambda>w. X m w + Y m w) w = X n w + Y n w"
    proof -
      have "integrable M (X m)" using assms unfolding martingale_def by simp
      moreover have "integrable M (Y m)" using assms unfolding martingale_def by simp
      moreover have " sigma_finite_subalgebra M (F n)" using assms by simp
      ultimately have "AE w in M. real_cond_exp M (F n) (\<lambda>w. X m w + Y m w) w =
        real_cond_exp M (F n) (X m) w + real_cond_exp M (F n) (Y m) w"
        using sigma_finite_subalgebra.real_cond_exp_add[of M "F n" "X m" "Y m"] by simp
      moreover have "AE w in M. real_cond_exp M (F n) (X m) w = X n w" using \<open>n\<le> m\<close> assms
        unfolding martingale_def by simp
      moreover have "AE w in M. real_cond_exp M (F n) (Y m) w = Y n w" using \<open>n\<le> m\<close> assms
        unfolding martingale_def by simp
      ultimately show ?thesis by auto
    qed
  qed
  show "filtration M F" using assms unfolding martingale_def by simp
  show "borel_adapt_stoch_proc F (\<lambda>n w. X n w + Y n w)" unfolding adapt_stoch_proc_def
  proof
    fix n
    show "(\<lambda>w. X n w + Y n w) \<in> borel_measurable (F n)" using assms unfolding martingale_def adapt_stoch_proc_def
      by (simp add: borel_measurable_add)
  qed
qed

lemma  disc_martingale_charact:
  assumes "(\<forall>n. integrable M (X n))"
  and "filtration M F"
  and "\<forall>m. sigma_finite_subalgebra M (F m)"
  and "\<forall>m. X m \<in> borel_measurable (F m)"
  and "(\<forall>n. AE w in M. real_cond_exp M (F n) (X (Suc n)) w = (X n) w)"
shows "martingale M F X " unfolding martingale_def
proof (intro conjI)
  have "\<forall> k m. k \<le> m \<longrightarrow> (AE w in M. real_cond_exp M (F (m-k)) (X m) w = X (m-k) w)"
  proof (intro allI impI)
    fix m
    fix k::nat
    show "k\<le>m \<Longrightarrow> AE w in M. real_cond_exp M (F (m-k)) (X m) w = X (m-k) w"
    proof (induct k)
      case 0
      have "X m \<in> borel_measurable (F m)" using assms by simp
      moreover have "integrable M (X m)" using assms by simp
      moreover have "sigma_finite_subalgebra M (F m)" using assms by simp
      ultimately have "AE w in M. real_cond_exp M (F m) (X m) w = X m w"
        using sigma_finite_subalgebra.real_cond_exp_F_meas[of M "F m" "X m"] by simp
      thus ?case using 0 by simp
    next
      case (Suc k)
      have "Suc (m - (Suc k)) = m - k" using Suc by simp
      hence "AE w in M. real_cond_exp M (F (m - (Suc k))) (X (Suc (m - (Suc k)))) w = (X (m - (Suc k))) w"
        using assms by blast
      hence "AE w in M. real_cond_exp M (F (m - (Suc k))) (X ((m - k))) w = (X (m - (Suc k))) w"
        using assms(3) \<open>Suc (m - (Suc k)) = m - k\<close> by simp
      moreover have "AE w in M. real_cond_exp M (F (m - (Suc k))) (real_cond_exp M (F (m - k)) (X m)) w =
        real_cond_exp M (F (m - (Suc k))) (X m) w"
        using  sigma_finite_subalgebra.real_cond_exp_nested_subalg[of M "F (m- (Suc k))" "F (m-k)"  "X m"]
        by (metis Filtration.filtration_def Suc_n_not_le_n \<open>Suc (m - Suc k) = m - k\<close> assms(1) assms(2) assms(3)
            filtrationE1 nat_le_linear)
      moreover have "AE w in M. real_cond_exp M (F (m - (Suc k))) (real_cond_exp M (F (m - k)) (X m)) w =
        real_cond_exp M (F (m - (Suc k))) (X (m-k)) w" using Suc
        sigma_finite_subalgebra.real_cond_exp_cong[of M "F (m - (Suc k))" "real_cond_exp M (F (m - k)) (X m)" "X (m - k)"]
        borel_measurable_cond_exp[of M "F (m-k)" "X m"]
        using Suc_leD assms(1) assms(3) borel_measurable_cond_exp2 by blast
      ultimately show ?case by auto
    qed
  qed
  thus "\<forall> n m. n \<le> m \<longrightarrow> (AE w in M. real_cond_exp M (F n) (X m) w = X n w)"
    by (metis diff_diff_cancel diff_le_self)
  show "\<forall>t. integrable M (X t)" using assms by simp
  show "filtration M F" using assms by simp
  show "borel_adapt_stoch_proc F X" using assms unfolding adapt_stoch_proc_def by simp
qed


lemma (in finite_measure) constant_martingale:
  assumes "\<forall>t. sigma_finite_subalgebra M (F t)"
and "filtration M F"
shows "martingale M F (\<lambda>n w. c)" unfolding martingale_def
proof (intro allI conjI impI)
  show "filtration M F" using assms by simp
  {
    fix t
    show "integrable M (\<lambda>w. c)" by simp
  }
  {
    fix t::'b
    fix s
    assume "t \<le> s"
    show "AE w in M. real_cond_exp M (F t) (\<lambda>w. c) w = c"
      by (intro sigma_finite_subalgebra.real_cond_exp_F_meas, (auto simp add: assms))
  }
  show "borel_adapt_stoch_proc F (\<lambda>n w. c)" unfolding adapt_stoch_proc_def by simp
qed



end