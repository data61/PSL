(*
  File:     Lambert_W_MacLaurin_Series
  Author:   Manuel Eberl, TU München

  The MacLaurin series of the Lambert W function at x = 0
  This file is kept separate from the main Lambert_W file because it requires significantly
  more library material, including HOL-Analysis.
*)
theory Lambert_W_MacLaurin_Series
imports
  "HOL-Computational_Algebra.Formal_Power_Series"
  "Bernoulli.Bernoulli_FPS" (* TODO only for Stirling number identities; should be moved! *)
  "Stirling_Formula.Stirling_Formula"
  Lambert_W
begin

subsection \<open>The MacLaurin series of $W_0(x)$ at $x = 0$\<close>

text \<open>
  In this section, we derive the MacLaurin series of $W_0(x)$ as a formal power series
  at $x = 0$ and prove that its radius of convergenge is $e^{-1}$.

  We do not actually show that this series evaluates to 1 since Isabelle's library does not 
  contain the required theorems about convergence of the composition of two power series yet.
  If it did, however, this last remaining step would be trivial since we did all the real work
  here.
\<close>

(* TODO Move *)
lemma Stirling_Suc_n_n: "Stirling (Suc n) n = (Suc n choose 2)"
  by (induction n) (auto simp: choose_two)

lemma Stirling_n_n_minus_1: "n > 0 \<Longrightarrow> Stirling n (n - 1) = (n choose 2)"
  using Stirling_Suc_n_n[of "n - 1"] by (cases n) auto

text \<open>
  The following defines the power series $W(X)$ as the formal inverse of the
  formal power series $X e^X$:
\<close>
definition fps_Lambert_W :: "real fps" where
  "fps_Lambert_W = fps_inv (fps_X * fps_exp 1)"

text \<open>
  The formal composition of $W(X)$ and $X e^X$ is, in fact, the identity (in both directions).
\<close>
lemma fps_compose_Lambert_W: "fps_compose fps_Lambert_W (fps_X * fps_exp 1) = fps_X"
  unfolding fps_Lambert_W_def by (rule fps_inv) auto 

lemma fps_compose_Lambert_W': "fps_compose (fps_X * fps_exp 1) fps_Lambert_W  = fps_X"
  unfolding fps_Lambert_W_def by (rule fps_inv_right) auto

text \<open>
  We have $W(0) = 0$, which shows that $W(X)$ indeed represents the branch $W_0$.
\<close>
lemma fps_nth_Lambert_W_0 [simp]: "fps_nth fps_Lambert_W 0 = 0"
  by (simp add: fps_Lambert_W_def fps_inv_def)

lemma fps_nth_Lambert_W_1 [simp]: "fps_nth fps_Lambert_W 1 = 1"
  by (simp add: fps_Lambert_W_def fps_inv_def)

text \<open>
  All the equalities that hold for the analytic Lambert $W$ function in a neighbourhood of 0
  also hold formally for the formal power series, e.g. $W(X) = X e^{-W(X)}$:  
\<close>
lemma fps_Lambert_W_over_X:
  "fps_Lambert_W = fps_X * fps_compose (fps_exp (-1)) fps_Lambert_W"
proof -
  have "fps_nth (fps_exp 1 oo fps_Lambert_W) 0 = 1"
    by simp
  hence nz: "fps_exp 1 oo fps_Lambert_W \<noteq> 0"
    by force    
  have "fps_Lambert_W * fps_compose (fps_exp 1) fps_Lambert_W =
          fps_compose (fps_X * fps_exp 1) fps_Lambert_W"
    by (simp add: fps_compose_mult_distrib)
  also have "\<dots> = fps_X * fps_compose 1 fps_Lambert_W"
    by (simp add: fps_compose_Lambert_W')
  also have "1 = fps_exp (-1) * fps_exp (1 :: real)"
    by (simp flip: fps_exp_add_mult)
  also have "fps_X * fps_compose \<dots> fps_Lambert_W =
               fps_X * fps_compose (fps_exp (-1)) fps_Lambert_W *
                 fps_compose (fps_exp 1) fps_Lambert_W"
    by (simp add: fps_compose_mult_distrib mult_ac)
  finally show ?thesis
    using nz by simp
qed
    
text \<open>
  We now derive the closed-form expression
  \[W(X) = \sum_{n=1}^\infty \frac{(-n)^{n-1}}{n!} X^n\ .\]
\<close>
lemma fps_nth_Lambert_W: "fps_nth fps_Lambert_W n = (if n = 0 then 0 else ((-n)^(n-1) / fact n))"
proof -
  define F :: "real fps" where "F = fps_X * fps_exp 1"
  have fps_nth_eq: "fps_nth F n = 1 / fact (n - 1)" if "n > 0" for n
    using that unfolding F_def by simp
  have F_power: "F ^ n = fps_X ^ n * fps_exp (of_nat n)" for n
    by (simp add: F_def power_mult_distrib fps_exp_power_mult)

  have "fps_nth (fps_inv F) n = (if n = 0 then 0 else ((-n)^(n-1) / fact n))" for n
  proof (induction n rule: less_induct)
    case (less n)
    consider "n = 0" | "n = 1" | "n > 1" by force
    thus ?case
    proof cases
      case 3
      hence "fps_nth (fps_inv F) n = -(\<Sum>i=0..n-1. fps_nth (fps_inv F) i * fps_nth (F ^ i) n)"
        (is "_ = -?S") by (cases n) (auto simp: fps_inv_def F_def)
      also have "?S = (\<Sum>i=1..<n. fps_nth (fps_inv F) i * fps_nth (F ^ i) n)"
        using less[of 1] 3 by (intro sum.mono_neutral_right) (auto simp: not_le)
      also have "\<dots> = (-1) ^ (n+1) / fact n *
                        (\<Sum>i=1..<n. ((-1)^(n - i) * real (n choose i) * real i ^ (n - 1)))"
        unfolding sum_divide_distrib sum_distrib_left
      proof (intro sum.cong, goal_cases)
        case (2 i)
        hence "fps_nth (fps_inv F) i * fps_nth (F ^ i) n =
                 (-1) ^ (i - 1) * real (i ^ (i - 1) * i ^ (n - i)) *
                 (fact n / (fact i * fact (n - i)) / fact n)"
          using less.IH[of i] by (simp add: F_power less fps_X_power_mult_nth power_minus')
        also have "(fact n / (fact i * fact (n - i))) = real (n choose i)"
          using 2 by (subst binomial_fact) auto
        also have "i ^ (i - 1) * i ^ (n - i) = i ^ (n - 1)"
          using 2 by (subst power_add [symmetric]) auto
        also have "(-1) ^ (i - 1) = ((-1) ^ (n+1) * (-1)^(n-i) :: real)"
          using 2 by (subst power_add [symmetric]) (auto simp: minus_one_power_iff)
        finally show ?case by simp
      qed auto
      also have "(\<Sum>i=1..<n. ((-1)^(n - i) * real (n choose i) * real i ^ (n - 1))) =
                 (\<Sum>i\<in>{..n}-{n}. ((-1)^(n - i) * real (n choose i) * real i ^ (n - 1)))"
        using 3 by (intro sum.mono_neutral_left) auto
      also have "\<dots> = (\<Sum>i\<le>n. ((-1)^(n - i) * real (n choose i) * real i ^ (n - 1))) -
                      real n ^ (n - 1)"
        by (subst (2) sum.remove[of _ n]) auto
      also have "(\<Sum>i\<le>n. ((-1)^(n - i) * real (n choose i) * real i ^ (n - 1))) =
                   real (Stirling (n - 1) n) * fact n"
        by (subst Stirling_closed_form) auto
      also have "Stirling (n - 1) n = 0"
        using 3 by (subst Stirling_less) auto
      finally have "fps_nth (fps_inv F) n = -((-1) ^ n * real n ^ (n - 1) / fact n)"
        by simp
      also have "\<dots> = (-real n) ^ (n - 1) / fact n"
        using 3 by (subst power_minus) (auto simp: minus_one_power_iff)
      finally show ?thesis
        using 3 by simp
    qed (auto simp: fps_inv_def F_def)
  qed
  thus ?thesis by (simp add: F_def fps_Lambert_W_def)
qed

(* TODO: Move *)
text \<open>
  Next, we need a few auxiliary lemmas about summability and convergence radii that should
  go into Isabelle's standard library at some point:
\<close>
lemma summable_comparison_test_bigo:
  fixes f :: "nat \<Rightarrow> real"
  assumes "summable (\<lambda>n. norm (g n))" "f \<in> O(g)"
  shows   "summable f"
proof -
  from \<open>f \<in> O(g)\<close> obtain C where C: "eventually (\<lambda>x. norm (f x) \<le> C * norm (g x)) at_top"
    by (auto elim: landau_o.bigE)
  thus ?thesis
    by (rule summable_comparison_test_ev) (insert assms, auto intro: summable_mult)
qed

lemma summable_comparison_test_bigo':
  assumes "summable (\<lambda>n. norm (g n))"
  assumes "(\<lambda>n. norm (f n :: 'a :: banach)) \<in> O(\<lambda>n. norm (g n))"
  shows   "summable f"
proof (rule summable_norm_cancel, rule summable_comparison_test_bigo)
  show "summable (\<lambda>n. norm (norm (g n)))"
    using assms by simp
qed fact+

lemma conv_radius_conv_Sup':
  fixes f :: "nat \<Rightarrow> 'a :: {banach, real_normed_div_algebra}"
  shows "conv_radius f = Sup {r. \<forall>z. ereal (norm z) < r \<longrightarrow> summable (\<lambda>n. norm (f n * z ^ n))}"
proof (rule Sup_eqI [symmetric], goal_cases)
  case (1 r)
  show ?case
  proof (rule conv_radius_geI_ex')
    fix r' :: real assume r': "r' > 0" "ereal r' < r"
    show "summable (\<lambda>n. f n * of_real r' ^ n)"
      by (rule summable_norm_cancel) (use 1 r' in auto)
  qed
next
  case (2 r)
  from 2[of 0] have r: "r \<ge> 0" by auto
  show ?case
  proof (intro conv_radius_leI_ex' r)
    fix R assume R: "R > 0" "ereal R > r"
    with r obtain r' where [simp]: "r = ereal r'" by (cases r) auto
    show "\<not>summable (\<lambda>n. f n * of_real R ^ n)"
    proof
      assume *: "summable (\<lambda>n. f n * of_real R ^ n)"
      define R' where "R' = (R + r') / 2"
      from R have R': "R' > r'" "R' < R" by (simp_all add: R'_def)
      hence "\<forall>z. norm z < R' \<longrightarrow> summable (\<lambda>n. norm (f n * z ^ n))"
        using powser_insidea[OF *] by auto
      from 2[of R'] and this have "R' \<le> r'" by auto
      with \<open>R' > r'\<close> show False by simp
    qed
  qed
qed

lemma bigo_imp_conv_radius_ge:
  fixes f g :: "nat \<Rightarrow> 'a :: {banach, real_normed_field}"
  assumes "f \<in> O(g)"
  shows   "conv_radius f \<ge> conv_radius g"
proof -
  have "conv_radius g = Sup {r. \<forall>z. ereal (norm z) < r \<longrightarrow> summable (\<lambda>n. norm (g n * z ^ n))}"
    by (simp add: conv_radius_conv_Sup')
  also have "\<dots> \<le> Sup {r. \<forall>z. ereal (norm z) < r \<longrightarrow> summable (\<lambda>n. f n * z ^ n)}"
  proof (rule Sup_subset_mono, safe)
    fix r :: ereal and z :: 'a
    assume g: "\<forall>z. ereal (norm z) < r \<longrightarrow> summable (\<lambda>n. norm (g n * z ^ n))"
    assume z: "ereal (norm z) < r"
    from g z have "summable (\<lambda>n. norm (g n * z ^ n))"
      by blast
    moreover have "(\<lambda>n. norm (f n * z ^ n)) \<in> O(\<lambda>n. norm (g n * z ^ n))"
      unfolding landau_o.big.norm_iff by (intro landau_o.big.mult assms) auto
    ultimately show "summable (\<lambda>n. f n * z ^ n)"
      by (rule summable_comparison_test_bigo')
  qed
  also have "\<dots> = conv_radius f"
    by (simp add: conv_radius_conv_Sup)
  finally show ?thesis .
qed

lemma conv_radius_cong_bigtheta:
  assumes "f \<in> \<Theta>(g)"
  shows   "conv_radius f = conv_radius g"
  using assms
  by (intro antisym bigo_imp_conv_radius_ge) (auto simp: bigtheta_def bigomega_iff_bigo)

lemma conv_radius_eqI_smallomega_smallo:
  fixes f :: "nat \<Rightarrow> 'a :: {real_normed_div_algebra, banach}"
  assumes "\<And>\<epsilon>. \<epsilon> > l \<Longrightarrow> \<epsilon> < inverse C \<Longrightarrow> (\<lambda>n. norm (f n)) \<in> \<omega>(\<lambda>n. \<epsilon> ^ n)"
  assumes "\<And>\<epsilon>. \<epsilon> < u \<Longrightarrow> \<epsilon> > inverse C \<Longrightarrow> (\<lambda>n. norm (f n)) \<in> o(\<lambda>n. \<epsilon> ^ n)"
  assumes C: "C > 0" and lu: "l > 0" "l < inverse C" "u > inverse C"
  shows   "conv_radius f = ereal C"
proof (intro antisym)
  have "0 < inverse C"
    using assms by (auto simp: field_simps)
  also have "\<dots> < u"
    by fact
  finally have "u > 0" by simp
  show "conv_radius f \<ge> C"
    unfolding conv_radius_altdef le_Liminf_iff
  proof safe
    fix c :: ereal assume c: "c < C"
    hence "max c (inverse u) < ereal C"
      using lu C \<open>u > 0\<close> by (auto simp: field_simps)
    from ereal_dense2[OF this] obtain c' where c': "c < ereal c'" "inverse u < c'" "c' < C"
      by auto
    have "inverse u > 0"
      using \<open>u > 0\<close> by simp
    also have "\<dots> < c'" by fact
    finally have "c' > 0" .
    
    have "\<forall>\<^sub>F x in sequentially. norm (norm (f x)) \<le> 1/2 * norm (inverse c' ^ x)"
      using landau_o.smallD[OF assms(2)[of "inverse c'"], of "1/2"] c' C lu \<open>c' > 0\<close> c
      by (simp add: field_simps)
    thus "\<forall>\<^sub>F n in sequentially. c < inverse (ereal (root n (norm (f n))))"
      using eventually_gt_at_top[of 0]
    proof eventually_elim
      case (elim n)
      have "norm (f n) \<le> 1/2 * norm (inverse c' ^ n)"
        using c' using elim by (simp add: field_simps)
      also have "\<dots> < norm (inverse c' ^ n)"
        using \<open>c' > 0\<close> by simp
      finally have "root n (norm (f n)) < root n (norm (inverse c' ^ n))"
        using \<open>n > 0\<close> c' by (intro real_root_less_mono) auto
      also have "root n (norm (inverse c' ^ n)) = inverse c'"
        using \<open>n > 0\<close> \<open>c' > 0\<close> by (simp add: norm_power real_root_power)
      finally have "ereal (root n (norm (f n))) < ereal (inverse c')"
        by simp
      also have "\<dots> = inverse (ereal c')"
        using \<open>c' > 0\<close> by auto
      finally have "inverse (inverse (ereal c')) < inverse (ereal (root n (norm (f n))))"
        using c' \<open>n > 0\<close> by (intro ereal_inverse_antimono_strict) auto
      also have "inverse (inverse (ereal c')) = ereal c'"
        using c' by simp
      finally show ?case
        using \<open>c < c'\<close> by simp
    qed
  qed
next
  show "conv_radius f \<le> C"
  proof (rule ccontr)
    assume "\<not>(conv_radius f \<le> C)"
    hence "conv_radius f > C" by auto
    hence "min (conv_radius f) (inverse l) > ereal C"
      using lu C \<open>l > 0\<close> by (auto simp: field_simps)
    from ereal_dense2[OF this] obtain c where c: "C < ereal c" "inverse l > c" "c < conv_radius f"
      by auto
    hence "c > 0" using lu C
      by (simp add: field_simps)

    have "\<forall>\<^sub>F n in sequentially. ereal c < inverse (ereal (root n (norm (f n))))"
      using less_LiminfD[OF c(3)[unfolded conv_radius_altdef]] by simp
    moreover have "\<forall>\<^sub>F n in sequentially. norm (f n) \<ge> 2 * norm (inverse c ^ n)"
      using landau_omega.smallD[OF assms(1)[of "inverse c"], of 2] c C \<open>c > 0\<close> lu
      by (simp add: field_simps)
    ultimately have "eventually (\<lambda>n. False) sequentially"
      using eventually_gt_at_top[of 0]
    proof eventually_elim
      case (elim n)
      have "norm (inverse c ^ n) < 2 * norm (inverse c ^ n)"
        using c \<open>n > 0\<close> C by simp
      also have "\<dots> \<le> norm (f n)"
        using elim by simp
      finally have "root n (inverse c ^ n) < root n (norm (f n))"
        using \<open>n > 0\<close> by (intro real_root_less_mono) auto
      also have "root n (inverse c ^ n) = inverse c"
        using \<open>n > 0\<close> c C by (subst real_root_power) auto
      finally have "ereal (inverse c) < ereal (root n (norm (f n)))"
        by simp
      also have "ereal (inverse c) = inverse (ereal c)"
        using c C by auto
      finally have "inverse (ereal (root n (norm (f n)))) < inverse (inverse (ereal c))"
        using c C
        by (intro ereal_inverse_antimono_strict) auto
      also have "\<dots> = ereal c"
        using c C by auto
      also have "\<dots> < inverse (ereal (root n (norm (f n))))"
        using elim by simp
      finally show False .
    qed
    thus False by simp
  qed
qed

text \<open>
  Finally, we show that the radius of convergence of $W(X)$ is $e^{-1}$ by directly computing
  \[\lim\limits_{n\to\infty} \sqrt[n]{|[X^n]\,W(X)|} = e\]
  using Stirling's formula for $n!$:
\<close>
lemma fps_conv_radius_Lambert_W: "fps_conv_radius fps_Lambert_W = exp (-1)"
proof -
  have "conv_radius (fps_nth fps_Lambert_W) = conv_radius (\<lambda>n. exp 1 ^ n * n powr (-3/2) :: real)"
  proof (rule conv_radius_cong_bigtheta)
    have "fps_nth fps_Lambert_W \<in> \<Theta>(\<lambda>n. (-real n) ^ (n - 1) / fact n)"
      by (intro bigthetaI_cong eventually_mono[OF eventually_gt_at_top[of 0]])
         (auto simp: fps_nth_Lambert_W)
    also have "(\<lambda>n. (-real n) ^ (n - 1) / fact n) \<in> \<Theta>(\<lambda>n. real n ^ (n - 1) / fact n)"
      by (subst landau_theta.norm_iff [symmetric], subst norm_divide) auto
    also have "(\<lambda>n. (real n) ^ (n - 1) / fact n) \<in>
                 \<Theta>(\<lambda>n. (real n) ^ (n - 1) / (sqrt (2 * pi * real n) * (real n / exp 1) ^ n))"
      by (intro asymp_equiv_imp_bigtheta asymp_equiv_intros fact_asymp_equiv)
    also have "(\<lambda>n. (real n) ^ (n - 1) / (sqrt (2 * pi * real n) * (real n / exp 1) ^ n)) \<in>
                 \<Theta>(\<lambda>n. exp 1 ^ n * n powr (-3/2))"
      by (real_asymp simp: ln_inverse)
    finally show "fps_nth fps_Lambert_W \<in> \<Theta>(\<lambda>n. exp 1 ^ n * n powr (-3/2) :: real)" .
  qed
  also have "\<dots> = inverse (limsup (\<lambda>n. ereal (root n (exp 1 ^ n * real n powr - (3 / 2)))))"
    by (simp add: conv_radius_def)
  also have "limsup (\<lambda>n. ereal (root n (exp 1 ^ n * real n powr - (3 / 2)))) = exp 1"
  proof (intro lim_imp_Limsup tendsto_intros)
    \<comment> \<open>real\_asymp does not support \<^const>\<open>root\<close> for a variable basis natively, so
        we need to convert it to \<^const>\<open>powr\<close> first.\<close>
    (* TODO add better "root" support to real_asymp *)
    have "(\<lambda>n. (exp 1 ^ n * real n powr -(3/2)) powr (1 / real n)) \<longlonglongrightarrow> exp 1"
      by real_asymp
    also have "?this \<longleftrightarrow> (\<lambda>x. root x (exp 1 ^ x * real x powr - (3 / 2))) \<longlonglongrightarrow> exp 1"
      by (intro filterlim_cong eventually_mono[OF eventually_gt_at_top[of 0]])
         (auto simp: root_powr_inverse)
    finally show \<dots> .
  qed auto
  finally show ?thesis
    by (simp add: fps_conv_radius_def exp_minus)
qed

end