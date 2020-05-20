(*
    File:      Euler_Products.thy
    Author:    Manuel Eberl, TU München
*)
section \<open>Euler product expansions\<close>
theory Euler_Products
imports 
  "HOL-Analysis.Analysis"
  Multiplicative_Function
begin

lemma prime_factors_power_subset:
  "prime_factors (x ^ n) \<subseteq> prime_factors x"
  by (cases "n = 0") (auto simp: prime_factors_power)

lemma prime_power_product_in_Pi:
  "(\<lambda>g. \<Prod>p\<in>{p. p \<le> (n::nat) \<and> prime p}. p ^ g p)
    \<in> ({p. p \<le> n \<and> prime p} \<rightarrow>\<^sub>E UNIV) \<rightarrow>
       {m. 0 < m \<and> prime_factors m \<subseteq> {..n}}"
proof (safe, goal_cases)
  case (2 f p)
  have "prime_factors (\<Prod>p\<in>{p. p \<le> n \<and> prime p}. p ^ f p) = 
          (\<Union>p\<in>{p. p \<le> n \<and> prime p}. prime_factors (p ^ f p))"
    by (subst prime_factors_prod) auto
  also have "\<dots> \<subseteq> (\<Union>p\<in>{p. p \<le> n \<and> prime p}. prime_factors p)"
    using prime_factors_power_subset by blast
  also have "\<dots> \<subseteq> (\<Union>p\<in>{p. p \<le> n \<and> prime p}. {p})"
    by (auto simp: prime_factors_dvd prime_gt_0_nat dest!: dvd_imp_le)
  also have "\<dots> \<subseteq> {..n}" by auto
  finally show ?case using 2 by auto
qed (auto simp: prime_gt_0_nat)

lemma inj_prime_power: "inj_on (\<lambda>x. fst x ^ snd x :: nat) ({a. prime a} \<times> {0<..})"
proof (intro inj_onI, clarify, goal_cases)
  case (1 p m q n)
  with prime_power_eq_imp_eq[of p q m n] and 1 
    have "p = q" by auto
  moreover from this have "m = n"
    using prime_gt_1_nat 1 by auto
  ultimately show ?case by simp
qed

lemma bij_betw_prime_powers:
  "bij_betw (\<lambda>g. \<Prod>p\<in>{p. p \<le> n \<and> prime p}. p ^ g p) ({p. p \<le> n \<and> prime p} \<rightarrow>\<^sub>E UNIV)
     {m. 0 < m \<and> prime_factors m \<subseteq> {..(n::nat)}}"
proof (rule bij_betwI[of _ _ _ "(\<lambda>m p. if p \<le> n \<and> prime p then multiplicity p m else undefined)"], 
         goal_cases)
  case 1
  show ?case by (rule prime_power_product_in_Pi)
next
  case 2
  show ?case
    by (auto split: if_splits)
next
  case (3 f)
  show ?case
  proof (rule ext, goal_cases)
    case (1 q)
    show ?case
    proof (cases "q \<le> n \<and> prime q")
      case True
      hence "multiplicity q (\<Prod>p\<in>{p. p \<le> n \<and> prime p}. p ^ f p) = 
               (\<Sum>x\<in>{p. p \<le> n \<and> prime p}. multiplicity q (x ^ f x))"
        by (subst prime_elem_multiplicity_prod_distrib) auto
      also have "\<dots> = (\<Sum>x\<in>{p. p \<le> n \<and> prime p}. if x = q then f q else 0)"
        using True by (intro sum.cong refl) (auto simp: multiplicity_distinct_prime_power)
      also have "\<dots> = f q" using True by auto
      finally show ?thesis using True by simp
    qed (insert 3, force+)
  qed
next
  case (4 m)
  have "(\<Prod>p | p \<le> n \<and> prime p. p ^ (if p \<le> n \<and> prime p then multiplicity p m else undefined)) =
          (\<Prod>p\<in>prime_factors m. p ^ multiplicity p m)"
  proof (rule prod.mono_neutral_cong)
    show "finite (prime_factors m)" by simp
  qed (insert 4, auto simp: prime_factors_multiplicity)
  also from 4 have "\<dots> = m"
    by (intro prime_factorization_nat [symmetric]) auto
  finally show ?case .
qed
      
lemma
  fixes f :: "nat \<Rightarrow> 'a :: {real_normed_field,banach,second_countable_topology}"
  assumes summable: "summable (\<lambda>n. norm (f n))"
  assumes "multiplicative_function f"
  shows   abs_convergent_euler_product:
            "abs_convergent_prod (\<lambda>p. if prime p then \<Sum>n. f (p ^ n) else 1)"
    and   euler_product_LIMSEQ:
            "(\<lambda>n. (\<Prod>p\<le>n. if prime p then \<Sum>n. f (p ^ n) else 1)) \<longlonglongrightarrow> (\<Sum>n. f n)"
proof -
  interpret f: multiplicative_function f by fact
  define N where "N = (\<Sum>n. norm (f n))"

  have summable': "f abs_summable_on A" for A
    by (rule abs_summable_on_subset[of _ UNIV])
       (insert summable, auto simp: abs_summable_on_nat_iff')

  have summable'': "(\<lambda>x. f (p ^ x)) abs_summable_on A" if "prime p" for A p
  proof (subst abs_summable_on_reindex_iff[of _ _ f])
    from \<open>prime p\<close> have "p > 1" 
      by (rule prime_gt_1_nat)
    thus "inj_on (\<lambda>i. p ^ i) A"
      by (auto simp: inj_on_def)
  qed (intro summable')

  have "(\<lambda>n. norm ((\<Sum>m. f m) - (\<Prod>p\<in>{p. p \<le> n \<and> prime p}. \<Sum>i. f (p ^ i)))) \<longlonglongrightarrow> 0"
          (is "filterlim ?h _ _")
  proof (rule tendsto_sandwich)
    show "eventually (\<lambda>n. ?h n \<le> N - (\<Sum>m\<le>n. norm (f m))) at_top"
    proof (intro always_eventually allI)
      fix n :: nat
      interpret product_sigma_finite "\<lambda>_::nat. count_space (UNIV :: nat set)"
        by (intro product_sigma_finite.intro sigma_finite_measure_count_space)

      have "(\<Prod>p | p \<le> n \<and> prime p. \<Sum>i. f (p ^ i)) =
              (\<Prod>p | p \<le> n \<and> prime p. \<Sum>\<^sub>a i\<in>UNIV. f (p ^ i))"
        by (intro prod.cong refl infsetsum_nat' [symmetric] summable'') auto
      also have "\<dots> = (\<Sum>\<^sub>ag\<in>{p. p \<le> n \<and> prime p} \<rightarrow>\<^sub>E UNIV.
                         \<Prod>x\<in>{p. p \<le> n \<and> prime p}. f (x ^ g x))"
        by (subst infsetsum_prod_PiE [symmetric])
           (auto simp: prime_gt_Suc_0_nat summable'')
      also have "\<dots> = (\<Sum>\<^sub>ag\<in>{p. p \<le> n \<and> prime p} \<rightarrow>\<^sub>E UNIV.
                         f (\<Prod>x\<in>{p. p \<le> n \<and> prime p}. x ^ g x))"
        by (subst f.prod_coprime) (auto simp add: primes_coprime)
      also have "\<dots> = (\<Sum>\<^sub>am | m > 0 \<and> prime_factors m \<subseteq> {..n}. f m)"
        by (intro infsetsum_reindex_bij_betw bij_betw_prime_powers)
      also have "(\<Sum>\<^sub>am\<in>UNIV. f m) - \<dots> = (\<Sum>\<^sub>am\<in>UNIV - {m. m > 0 \<and> prime_factors m \<subseteq> {..n}}. f m)"
        by (intro infsetsum_Diff [symmetric] summable') auto
      also have "(\<Sum>\<^sub>am\<in>UNIV. f m) = (\<Sum>m. f m)"
        by (intro infsetsum_nat' summable')
      also have "UNIV - {m. m > 0 \<and> prime_factors m \<subseteq> {..n}} = 
                   insert 0 {m. \<not>prime_factors m \<subseteq> {..n}}"
        by auto
      also have "(\<Sum>\<^sub>am\<in>\<dots>. f m) = (\<Sum>\<^sub>am | \<not>prime_factors m \<subseteq> {..n}. f m)"
        by (intro infsetsum_cong_neutral) auto
      also have "norm \<dots> \<le> (\<Sum>\<^sub>am | \<not>prime_factors m \<subseteq> {..n}. norm (f m))"
        by (rule norm_infsetsum_bound)
      also have "\<dots> \<le> (\<Sum>\<^sub>am\<in>{n<..}. norm (f m))" 
      proof (intro infsetsum_mono_neutral_left summable' abs_summable_on_normI)
        show "{m. \<not> prime_factors m \<subseteq> {..n}} \<subseteq> {n<..}"
        proof safe
          fix m k assume "\<not>m > n" and "k \<in> prime_factors m"
          thus "k \<le> n" by (cases "m = 0") (auto simp: prime_factors_dvd dest: dvd_imp_le)
        qed
      qed auto
      also have "{n<..} = UNIV - {..n}" 
        by auto
      also have "(\<Sum>\<^sub>am\<in>\<dots>. norm (f m)) = (\<Sum>\<^sub>am\<in>UNIV. norm (f m)) - (\<Sum>\<^sub>am\<in>{..n}. norm (f m))"
        using summable by (intro infsetsum_Diff) (auto simp: abs_summable_on_nat_iff')
      also have "(\<Sum>\<^sub>am\<in>UNIV. norm (f m)) = N"
        unfolding N_def using summable 
        by (intro infsetsum_nat') (auto simp: abs_summable_on_nat_iff')
      also have "(\<Sum>\<^sub>am\<in>{..n}. norm (f m)) = (\<Sum>m\<le>n. norm (f m))"
        by (simp add: suminf_finite)
      finally show "?h n \<le> N - (\<Sum>m\<le>n. norm (f m))" .
   qed
  next
    show "eventually (\<lambda>n. ?h n \<ge> 0) at_top" by simp
  next
    show "(\<lambda>n. N - (\<Sum>m\<le>n. norm (f m))) \<longlonglongrightarrow> 0" unfolding N_def
      by (rule tendsto_eq_intros refl summable_LIMSEQ' summable)+ simp_all
  qed simp_all
  hence "(\<lambda>n. (\<Sum>m. f m) - (\<Prod>p\<in>{p. p \<le> n \<and> prime p}. \<Sum>i. f (p ^ i))) \<longlonglongrightarrow> 0"
    by (simp add: tendsto_norm_zero_iff)
  from tendsto_diff[OF tendsto_const[of "\<Sum>m. f m"] this]
    have "(\<lambda>n. \<Prod>p | p \<le> n \<and> prime p. \<Sum>i. f (p ^ i)) \<longlonglongrightarrow> (\<Sum>m. f m)" by simp
  also have "(\<lambda>n. \<Prod>p | p \<le> n \<and> prime p. \<Sum>i. f (p ^ i)) = 
                 (\<lambda>n. \<Prod>p\<le>n. if prime p then (\<Sum>i. f (p ^ i)) else 1)"
    by (intro ext prod.mono_neutral_cong_left) auto
  finally show "\<dots> \<longlonglongrightarrow> (\<Sum>m. f m)" .

  show "abs_convergent_prod (\<lambda>p. if prime p then (\<Sum>i. f (p ^ i)) else 1)"
  proof (rule summable_imp_abs_convergent_prod)
    have "(\<lambda>(p,i). f (p ^ i)) abs_summable_on {p. prime p} \<times> {0<..}"
      unfolding case_prod_unfold 
      by (subst abs_summable_on_reindex_iff[OF inj_prime_power]) fact
    hence "(\<lambda>p. \<Sum>\<^sub>ai\<in>{0<..}. f (p ^ i)) abs_summable_on {p. prime p}"
      by (rule abs_summable_on_Sigma_project1') simp_all
    also have "?this \<longleftrightarrow> (\<lambda>p. (\<Sum>i. f (p ^ i)) - 1) abs_summable_on {p. prime p}"
    proof (intro abs_summable_on_cong refl)
      fix p :: nat assume p: "p \<in> {p. prime p}"
      have "{0<..} = UNIV - {0::nat}" by auto
      also have "(\<Sum>\<^sub>ai\<in>\<dots>. f (p ^ i)) = (\<Sum>i. f (p ^ i)) - 1"
        using p by (subst infsetsum_Diff) (simp_all add: infsetsum_nat' summable'')
      finally show "(\<Sum>\<^sub>ai\<in>{0<..}. f (p ^ i)) = (\<Sum>i. f (p ^ i)) - 1" .
    qed
    finally have "summable (\<lambda>p. if prime p then norm ((\<Sum>i. f (p ^ i)) - 1) else 0)"
      (is "summable ?T") by (simp add: abs_summable_on_nat_iff)
    also have "?T = (\<lambda>p. norm ((if prime p then \<Sum>i. f (p ^ i) else 1) - 1))"
      by (rule ext) (simp add: if_splits)
    finally show "summable \<dots>" .
  qed
qed

lemma
  fixes f :: "nat \<Rightarrow> 'a :: {real_normed_field,banach,second_countable_topology}"
  assumes summable: "summable (\<lambda>n. norm (f n))"
  assumes "completely_multiplicative_function f"
  shows   abs_convergent_euler_product':
            "abs_convergent_prod (\<lambda>p. if prime p then inverse (1 - f p) else 1)"
    and   completely_multiplicative_summable_norm: 
            "\<And>p. prime p \<Longrightarrow> norm (f p) < 1"
    and   euler_product_LIMSEQ':
            "(\<lambda>n. (\<Prod>p\<le>n. if prime p then inverse (1 - f p) else 1)) \<longlonglongrightarrow> (\<Sum>n. f n)"
proof -
  interpret f: completely_multiplicative_function f by fact
  {
    fix p :: nat assume "prime p"
    hence "inj (\<lambda>i. p ^ i)" 
      by (auto simp: inj_on_def dest: prime_gt_1_nat)
    from summable_reindex[OF summable this] 
      have *: "summable (\<lambda>i. norm (f (p ^ i)))" by (auto simp: o_def)
    also have "(\<lambda>i. norm (f (p ^ i))) = (\<lambda>i. norm (f p) ^ i)"
      by (simp add: f.power norm_power)
    finally show "norm (f p) < 1"
      by (subst (asm) summable_geometric_iff) simp_all
    note * and this
  } note summable' = this

  have eq: "(\<lambda>p. if prime p then (\<Sum>i. f (p ^ i)) else 1) = 
              (\<lambda>p. if prime p then inverse (1 - f p) else 1)"
  proof (rule ext, goal_cases)
    case (1 p)
    show ?case
    proof (cases "prime p")
      case True
      hence "norm (f p) < 1" by (rule summable')
      from suminf_geometric[OF this] and True show ?thesis
        by (simp add: field_simps f.power)
    qed simp_all
  qed
  hence eq': "(\<lambda>n. \<Prod>p\<le>n. if prime p then \<Sum>n. f (p ^ n) else 1) =
                (\<lambda>n. \<Prod>p\<le>n. if prime p then inverse (1 - f p) else 1)"
    by (auto simp: fun_eq_iff)

  have f: "multiplicative_function f" ..
  from abs_convergent_euler_product[OF assms(1) f] and euler_product_LIMSEQ[OF assms(1) f]
    show "abs_convergent_prod (\<lambda>p. if prime p then inverse (1 - f p) else 1)"
       and "(\<lambda>n. \<Prod>p\<le>n. if prime p then inverse (1 - f p) else 1) \<longlonglongrightarrow> (\<Sum>n. f n)"
      by (simp_all only: eq eq')
qed

end
