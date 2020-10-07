(*  
  Title:    SD_Efficiency.thy
  Author:   Manuel Eberl, TU München

  Characterisation of SD-efficiency.
*)

theory SD_Efficiency
imports Complex_Main Preference_Profiles Lotteries Stochastic_Dominance
begin

(* 
  TODO: Perhaps a general concept of "efficiency" can be introduced, 
  parametrised over the way in which two lotteries are compared.
*)

context pref_profile_wf
begin

lemma SD_inefficient_support_subset:
  assumes inefficient: "\<not>SD_efficient R p'"
  assumes support: "set_pmf p' \<subseteq> set_pmf p"
  assumes lotteries: "p \<in> lotteries_on alts"
  shows   "\<not>SD_efficient R p"
proof -
  from assms have p'_wf: "p' \<in> lotteries_on alts" by (simp add: lotteries_on_def)
  from inefficient obtain q' i where q': "q' \<in> lotteries_on alts" "i \<in> agents"
    "\<And>i. i \<in> agents \<Longrightarrow> q' \<succeq>[SD(R i)] p'" "q' \<succ>[SD(R i)] p'" 
    unfolding SD_efficient_def' by blast

  have subset: "{x. pmf p' x > pmf q' x} \<subseteq> set_pmf p'" by (auto simp: set_pmf_eq)
  also have "\<dots> \<subseteq> set_pmf p" by fact
  also have "\<dots> \<subseteq> alts" using lotteries by (simp add: lotteries_on_def)
  finally have finite: "finite {x. pmf p' x > pmf q' x}" 
    using finite_alts by (rule finite_subset)

  define \<epsilon> where "\<epsilon> = Min (insert 1 {pmf p x / (pmf p' x - pmf q' x) |x. pmf p' x > pmf q' x})"
  define supp where "supp = set_pmf p \<union> set_pmf q'"
  from lotteries finite_alts q'(1) have finite_supp: "finite supp"
    by (auto simp: lotteries_on_def supp_def dest: finite_subset)
  from support have [simp]: "pmf p x = 0" "pmf p' x = 0" "pmf q' x = 0" if "x \<notin> supp" for x
    using that by (auto simp: supp_def set_pmf_eq)

  from finite support subset have \<epsilon>: "\<epsilon> > 0" unfolding \<epsilon>_def 
    by (auto simp: field_simps set_pmf_eq')
  have nonneg: "pmf p x + \<epsilon> * (pmf q' x - pmf p' x) \<ge> 0" for x
  proof (cases "pmf p' x > pmf q' x")
    case True
    with finite have "\<epsilon> \<le> pmf p x / (pmf p' x - pmf q' x)"
      unfolding \<epsilon>_def by (intro Min_le) auto
    with True show ?thesis by (simp add: field_simps)
  next
    case False
    with pmf_nonneg[of p x] \<epsilon> show ?thesis by simp
  qed

  define q where "q = embed_pmf (\<lambda>x. pmf p x + \<epsilon> * (pmf q' x - pmf p' x))"
  have "(\<integral>\<^sup>+ x. ennreal (pmf p x + \<epsilon> * (pmf q' x - pmf p' x)) \<partial>count_space UNIV) = 1"
  proof (subst nn_integral_count_space')
    have "(\<Sum>x\<in>supp. ennreal (pmf p x + \<epsilon> * (pmf q' x - pmf p' x))) = 
            ennreal ((\<Sum>x\<in>supp. pmf p x) + \<epsilon> * ((\<Sum>x\<in>supp. pmf q' x) - (\<Sum>x\<in>supp. pmf p' x)))"
     by (subst sum_ennreal[OF nonneg], rule ennreal_cong)
        (auto simp: sum_subtractf ring_distribs sum.distrib sum_distrib_left)
    also from finite_supp support have "\<dots> = 1"
      by (subst (1 2 3) sum_pmf_eq_1) (auto simp: supp_def)
    finally show "(\<Sum>x\<in>supp. ennreal (pmf p x + \<epsilon> * (pmf q' x - pmf p' x))) = 1" .
  qed (insert nonneg finite_supp, simp_all)
  with nonneg have pmf_q: "pmf q x = pmf p x + \<epsilon> * (pmf q' x - pmf p' x)" for x
    unfolding q_def by (intro pmf_embed_pmf) simp_all
  with support have support_q: "set_pmf q \<subseteq> supp" 
    unfolding supp_def by (auto simp: set_pmf_eq)
  with lotteries support q'(1) have q_wf: "q \<in> lotteries_on alts"
    by (auto simp add: lotteries_on_def supp_def)
  
  from support_q support have expected_utility:
    "measure_pmf.expectation q u = measure_pmf.expectation p u + 
         \<epsilon> * (measure_pmf.expectation q' u - measure_pmf.expectation p' u)" for u
    by (subst (1 2 3 4) integral_measure_pmf[OF finite_supp])
       (auto simp: pmf_q supp_def sum.distrib sum_distrib_left 
                   sum_distrib_right sum_subtractf algebra_simps)
  
  have "q \<succeq>[SD(R i)] p" if i: "i \<in> agents" for i
  proof -
    from i interpret finite_total_preorder_on alts "R i" by simp
    from i lotteries q'(1) q'(3)[OF i] q_wf p'_wf \<epsilon> show ?thesis
      by (fastforce simp: SD_iff_expected_utilities_le expected_utility)
  qed
  moreover from \<open>i \<in> agents\<close> interpret finite_total_preorder_on alts "R i" by simp
    from lotteries q'(1,4) q_wf p'_wf \<epsilon> have "q \<succ>[SD(R i)] p"
    by (force simp: SD_iff_expected_utilities_le expected_utility not_le strongly_preferred_def)
  ultimately show ?thesis using q_wf \<open>i \<in> agents\<close> unfolding SD_efficient_def' by blast
qed

lemma SD_efficient_support_subset:
  assumes "SD_efficient R p" "set_pmf p' \<subseteq> set_pmf p" "p \<in> lotteries_on alts"
  shows   "SD_efficient R p'"
  using SD_inefficient_support_subset[OF _ assms(2,3)] assms(1) by blast

lemma SD_efficient_same_support:
  assumes "set_pmf p = set_pmf p'" "p \<in> lotteries_on alts"
  shows   "SD_efficient R p \<longleftrightarrow> SD_efficient R p'"
  using SD_inefficient_support_subset[of p p'] SD_inefficient_support_subset[of p' p] assms
  by (auto simp: lotteries_on_def)  

lemma SD_efficient_iff:
  assumes "p \<in> lotteries_on alts"
  shows   "SD_efficient R p \<longleftrightarrow> SD_efficient R (pmf_of_set (set_pmf p))"
  using assms finite_alts
  by (intro SD_efficient_same_support)
     (simp, subst set_pmf_of_set,
      auto simp: set_pmf_not_empty lotteries_on_def intro: finite_subset[OF _ finite_alts])

lemma SD_efficient_no_pareto_loser:
  assumes efficient: "SD_efficient R p" and p_wf: "p \<in> lotteries_on alts"
  shows   "set_pmf p \<inter> pareto_losers R = {}"
proof -
  have "x \<notin> pareto_losers R" if x: "x \<in> set_pmf p" for x
  proof -
    from x have "set_pmf (return_pmf x) \<subseteq> set_pmf p" by auto
    from efficient this p_wf have "SD_efficient R (return_pmf x)"
      by (rule SD_efficient_support_subset)
    moreover from assms x have "x \<in> alts" by (auto simp: lotteries_on_def)
    ultimately show "x \<notin> pareto_losers R" by (simp add: SD_efficient_singleton_iff)
  qed
  thus ?thesis by blast
qed

text \<open>
  Given two lotteries with the same support where one is strictly Pareto-SD-preferred to 
  the other, one can construct a third lottery that is weakly Pareto-SD-preferred to the 
  better lottery (and therefore strictly Pareto-SD-preferred to the worse lottery) and
  whose support is a strict subset of the original supports.
\<close>
lemma improve_lottery_support_subset:
  assumes "p \<in> lotteries_on alts" "q \<in> lotteries_on alts" "q \<succ>[Pareto(SD \<circ> R)] p"
          "set_pmf p = set_pmf q"
  obtains r where "r \<in> lotteries_on alts" "r \<succeq>[Pareto(SD \<circ> R)] q" "set_pmf r \<subset> set_pmf p"
proof -
  have subset: "{x. pmf p x > pmf q x} \<subseteq> set_pmf p" by (auto simp: set_pmf_eq)
  also have "\<dots> \<subseteq> alts" using assms by (simp add: lotteries_on_def)
  finally have finite: "finite {x. pmf p x > pmf q x}" 
    using finite_alts by (rule finite_subset)

  from assms have "q \<noteq> p" by (auto simp: strongly_preferred_def)
  hence ex_less: "\<exists>x. pmf p x > pmf q x" by (rule pmf_neq_exists_less)

  define \<epsilon> where "\<epsilon> = Min {pmf p x / (pmf p x - pmf q x) |x. pmf p x > pmf q x}"
  define supp where "supp = set_pmf p"
  from assms finite_alts have finite_supp: "finite supp"
    by (auto simp: lotteries_on_def supp_def dest: finite_subset)
  from assms have [simp]: "pmf p x = 0" "pmf q x = 0" if "x \<notin> supp" for x
    using that by (auto simp: supp_def set_pmf_eq)

  from finite subset ex_less have \<epsilon>: "\<epsilon> \<ge> 1" unfolding \<epsilon>_def 
    by (intro Min.boundedI) (auto simp: field_simps pmf_nonneg)
  have nonneg: "pmf p x + \<epsilon> * (pmf q x - pmf p x) \<ge> 0" for x
  proof (cases "pmf p x > pmf q x")
    case True
    with finite have "\<epsilon> \<le> pmf p x / (pmf p x - pmf q x)"
      unfolding \<epsilon>_def by (intro Min_le) auto
    with True show ?thesis by (simp add: field_simps)
  next
    case False
    with pmf_nonneg[of p x] \<epsilon> show ?thesis by simp
  qed

  define r where "r = embed_pmf (\<lambda>x. pmf p x + \<epsilon> * (pmf q x - pmf p x))"
  have "(\<integral>\<^sup>+ x. ennreal (pmf p x + \<epsilon> * (pmf q x - pmf p x)) \<partial>count_space UNIV) = 1"
  proof (subst nn_integral_count_space')
    have "(\<Sum>x\<in>supp. ennreal (pmf p x + \<epsilon> * (pmf q x - pmf p x))) = 
            ennreal ((\<Sum>x\<in>supp. pmf p x) + \<epsilon> * ((\<Sum>x\<in>supp. pmf q x) - (\<Sum>x\<in>supp. pmf p x)))"
     by (subst sum_ennreal[OF nonneg], rule ennreal_cong)
        (auto simp: sum_subtractf ring_distribs sum.distrib sum_distrib_left)
    also from finite_supp  have "\<dots> = 1"
      by (subst (1 2 3) sum_pmf_eq_1) (auto simp: supp_def assms)
    finally show "(\<Sum>x\<in>supp. ennreal (pmf p x + \<epsilon> * (pmf q x - pmf p x))) = 1" .
  qed (insert nonneg finite_supp, simp_all)
  with nonneg have pmf_r: "pmf r x = pmf p x + \<epsilon> * (pmf q x - pmf p x)" for x
    unfolding r_def by (intro pmf_embed_pmf) simp_all

  with assms have "set_pmf r \<subseteq> supp" 
    unfolding supp_def by (auto simp: set_pmf_eq)
  from finite ex_less have "\<epsilon> \<in> {pmf p x / (pmf p x - pmf q x) |x. pmf p x > pmf q x}"
     unfolding \<epsilon>_def by (intro Min_in) auto
  then obtain x where "\<epsilon> = pmf p x / (pmf p x - pmf q x)" "pmf p x > pmf q x" by blast
  hence "pmf r x = 0" by (simp add: pmf_r field_simps)
  moreover from \<open>pmf p x > pmf q x\<close> pmf_nonneg[of q x] 
    have "pmf p x > 0" by linarith
  ultimately have "x \<in> set_pmf p - set_pmf r" by (auto simp: set_pmf_iff)
  with \<open>set_pmf r \<subseteq> supp\<close> have support_r: "set_pmf r \<subset> set_pmf p" unfolding supp_def by blast
  from this assms have r_wf: "r \<in> lotteries_on alts" by (simp add: lotteries_on_def)

  have "r \<succeq>[Pareto(SD\<circ>R)] q" unfolding SD.Pareto_iff unfolding o_def
  proof 
    fix i assume i: "i \<in> agents"
    then interpret finite_total_preorder_on alts "R i" by simp
    show "r \<succeq>[SD(R i)] q"
    proof (subst SD_iff_expected_utilities_le; safe?)
      fix u assume u: "is_vnm_utility u"
      from support_r have expected_utility_r:
        "measure_pmf.expectation r u = measure_pmf.expectation p u + 
             \<epsilon> * (measure_pmf.expectation q u - measure_pmf.expectation p u)"
        by (subst (1 2 3 4) integral_measure_pmf[OF finite_supp])
           (auto simp: supp_def assms pmf_r sum.distrib sum_distrib_left
            sum_distrib_right sum_subtractf algebra_simps)
      from assms i have "q \<succeq>[SD(R i)] p" by (simp add: SD.Pareto_strict_iff)
      with assms u have "measure_pmf.expectation q u \<ge> measure_pmf.expectation p u"
        by (simp add: SD_iff_expected_utilities_le r_wf)
      hence "(\<epsilon> - 1) * measure_pmf.expectation p u \<le> (\<epsilon> - 1) * measure_pmf.expectation q u"
        using \<epsilon> by (intro mult_left_mono) simp_all
      thus "measure_pmf.expectation q u \<le> measure_pmf.expectation r u" 
        by (simp add: algebra_simps expected_utility_r)
    qed fact+
  qed
  from that[OF r_wf this support_r] show ?thesis .
qed

subsection \<open>Existence of SD-efficient lotteries\<close>

text \<open>
  In this section, we will show that any lottery can be `improved' to an SD-efficient lottery,
  i.e. for any lottery, there exists an SD-efficient lottery that is weakly SD-preferred to 
  the original one by all agents.
\<close>

context
  fixes p :: "'alt lottery"
  assumes lott: "p \<in> lotteries_on alts"
begin

private definition improve_lottery :: "'alt lottery \<Rightarrow> 'alt lottery" where
  "improve_lottery q = (let A = {r\<in>lotteries_on alts. r \<succ>[Pareto(SD\<circ>R)] q} in
     (SOME r. r \<in> A \<and> \<not>(\<exists>r'\<in>A. set_pmf r' \<subset> set_pmf r)))" 

private lemma improve_lottery:
  assumes "\<not>SD_efficient R q"
  defines "r \<equiv> improve_lottery q"
  shows   "r \<in> lotteries_on alts" "r \<succ>[Pareto(SD\<circ>R)] q"
          "\<And>r'. r' \<in> lotteries_on alts \<Longrightarrow> r' \<succ>[Pareto(SD\<circ>R)] q \<Longrightarrow> \<not>(set_pmf r' \<subset> set_pmf r)"
proof -
  define A where "A = {r\<in>lotteries_on alts. r \<succ>[Pareto(SD\<circ>R)] q}"
  have subset_alts: "X \<subseteq> alts" if "X \<in> set_pmf`A" for X using that 
    by (auto simp: A_def lotteries_on_def)
  have r_altdef: "r = (SOME r. r \<in> A \<and> \<not>(\<exists>r'\<in>A. set_pmf r' \<subset> set_pmf r))"
    unfolding r_def improve_lottery_def Let_def A_def by simp
  from assms have nonempty: "A \<noteq> {}" by (auto simp: A_def SD_efficient_def)
  hence nonempty': "set_pmf`A \<noteq> {}" by simp
  have "set_pmf ` A \<subseteq> Pow alts" by (auto simp: A_def lotteries_on_def)

  from finite_alts have wf: "wf {(X,Y). X \<subset> Y \<and> Y \<subseteq> alts}"
    by (rule finite_subset_wf)
  obtain X 
    where "X \<in> set_pmf`A" "\<And>Y. Y \<subset> X \<and> X \<subseteq> alts \<Longrightarrow> Y \<notin> set_pmf ` A" 
    by (rule wfE_min'[OF wf nonempty']) simp_all
  hence "\<exists>r. r \<in> A \<and> \<not>(\<exists>r'\<in>A. set_pmf r' \<subset> set_pmf r)"
    by (auto simp: subset_alts[of X])
  from someI_ex[OF this, folded r_altdef] 
    show "r \<in> lotteries_on alts" "r \<succ>[Pareto(SD\<circ>R)] q"
          "\<And>r'. r' \<in> lotteries_on alts \<Longrightarrow> r' \<succ>[Pareto(SD\<circ>R)] q \<Longrightarrow> \<not>(set_pmf r' \<subset> set_pmf r)"
    unfolding A_def by blast+
qed

private fun sd_chain :: "nat \<Rightarrow> 'alt lottery option" where
  "sd_chain 0 = Some p"
| "sd_chain (Suc n) = 
     (case sd_chain n of
        None \<Rightarrow> None
      | Some p \<Rightarrow> if SD_efficient R p then None else Some (improve_lottery p))"

private lemma sd_chain_None_propagate:
  "m \<ge> n \<Longrightarrow> sd_chain n = None \<Longrightarrow> sd_chain m = None"
  by (induction rule: inc_induct) simp_all

private lemma sd_chain_Some_propagate:
  "m \<ge> n \<Longrightarrow> sd_chain m = Some q \<Longrightarrow> \<exists>q'. sd_chain n = Some q'"
  by (cases "sd_chain n") (auto simp: sd_chain_None_propagate)

private lemma sd_chain_NoneD:
  "sd_chain n = None \<Longrightarrow> \<exists>n p. sd_chain n = Some p \<and> SD_efficient R p"
  by (induction n) (auto split: option.splits if_splits)

private lemma sd_chain_lottery: "sd_chain n = Some q \<Longrightarrow> q \<in> lotteries_on alts"
  by (induction n) (insert lott, auto split: option.splits if_splits simp: improve_lottery)

private lemma sd_chain_Suc:
  assumes "sd_chain m = Some q"
  assumes "sd_chain (Suc m) = Some r"
  shows   "q \<prec>[Pareto(SD\<circ>R)] r"
  using assms by (auto split: if_splits simp: improve_lottery)

private lemma sd_chain_strictly_preferred:
  assumes "m < n"
  assumes "sd_chain m = Some q"
  assumes "sd_chain n = Some s"
  shows   "q \<prec>[Pareto(SD\<circ>R)] s"
  using assms
proof (induction arbitrary: q rule: strict_inc_induct)
  case (base k q)
  with sd_chain_Suc[of k q s] show ?case by (simp del: sd_chain.simps add: o_def)
next
  case (step k q)
  from step.hyps have "Suc k \<le> n" by simp
  from sd_chain_Some_propagate[OF this, of s] step.prems obtain r 
    where r: "sd_chain (Suc k) = Some r" by (auto simp del: sd_chain.simps)
  with step.prems have "q \<prec>[Pareto (SD \<circ> R)] r" by (intro sd_chain_Suc)
  moreover from r step.prems have "r \<prec>[Pareto (SD \<circ> R)] s" by (intro step.IH) simp_all
  ultimately show ?case by (rule SD.Pareto.strict_trans)
qed

private lemma sd_chain_preferred:
  assumes "m \<le> n"
  assumes "sd_chain m = Some q"
  assumes "sd_chain n = Some s"
  shows   "q \<preceq>[Pareto(SD\<circ>R)] s"
proof (cases "m < n")
  case True
  from sd_chain_strictly_preferred[OF this assms(2,3)] show ?thesis
    by (simp add: strongly_preferred_def)
next
  case False
  with assms show ?thesis by (auto intro: SD.Pareto.refl sd_chain_lottery)
qed

lemma SD_efficient_lottery_exists: 
  obtains q where "q \<in> lotteries_on alts" "q \<succeq>[Pareto(SD\<circ>R)] p" "SD_efficient R q"
proof -
  consider "\<exists>n. sd_chain n = None" | "\<forall>n. \<exists>q. sd_chain n = Some q" 
    using option.exhaust by metis
  thus ?thesis
  proof cases
    case 1
    define m where "m = (LEAST m. sd_chain m = None)"
    define k where "k = m - 1"
    from LeastI_ex[OF 1] have m: "sd_chain m = None" by (simp add: m_def)
    from m have nz: "m \<noteq> 0" by (intro notI) simp_all
    from nz have m_altdef: "m = Suc k" by (simp add: k_def)
    from nz Least_le[of "\<lambda>m. sd_chain m = None" "m - 1", folded m_def]
      obtain q where q: "sd_chain k = Some q" by (cases "sd_chain (m - 1)") (auto simp: k_def)
    from sd_chain_preferred[OF _ sd_chain.simps(1) this] have "q \<succeq>[Pareto(SD\<circ>R)] p" by simp
    moreover from q have "q \<in> lotteries_on alts" by (simp add: sd_chain_lottery)
    moreover from q m have "SD_efficient R q" by (auto split: if_splits simp: m_altdef)
    ultimately show ?thesis using that[of q] by blast
  next
    case 2
    have "range (set_pmf \<circ> the \<circ> sd_chain) \<subseteq> Pow alts" unfolding o_def
    proof safe
      fix n x assume A: "x \<in> set_pmf (the (sd_chain n))"
      from 2 obtain q where "sd_chain n = Some q" by auto
      with sd_chain_lottery[of n q] have "set_pmf (the (sd_chain n)) \<subseteq> alts"
        by (simp add: lotteries_on_def)
      with A show "x \<in> alts" by blast
    qed
    hence "finite (range (set_pmf \<circ> the \<circ> sd_chain))" by (rule finite_subset) simp_all
    from pigeonhole_infinite[OF infinite_UNIV_nat this]
      obtain m where "infinite {n. set_pmf (the (sd_chain n)) = set_pmf (the (sd_chain m))}"
      by auto
    hence "infinite ({n. set_pmf (the (sd_chain n)) = set_pmf (the (sd_chain m))} - {k. \<not>(k > m)})"
      by (simp add: not_less)
    hence "({n. set_pmf (the (sd_chain n)) = set_pmf (the (sd_chain m))} - {k. \<not>(k > m)}) \<noteq> {}"
      by (intro notI) simp_all
    then obtain n where mn: "n > m" "set_pmf (the (sd_chain n)) = set_pmf (the (sd_chain m))"
      by blast
    from 2 obtain p q where pq: "sd_chain m = Some p" "sd_chain n = Some q" by blast
    from mn pq have supp_eq: "set_pmf p = set_pmf q" by simp
    from mn(1) pq have less: "p \<prec>[Pareto(SD\<circ>R)] q" by (rule sd_chain_strictly_preferred)

    from \<open>m < n\<close> have "n > 0" by simp
    with \<open>sd_chain n = Some q\<close> sd_chain.simps(2)[of "n - 1"]
      obtain r where r: "\<not>SD_efficient R r" "q = improve_lottery r"
      by (auto simp del: sd_chain.simps split: if_splits option.splits)

    from pq have "p \<in> lotteries_on alts" "q \<in> lotteries_on alts" 
      by (simp_all add: sd_chain_lottery)
    from improve_lottery_support_subset[OF this less supp_eq] guess s . note s = this
    from improve_lottery(2)[of r] r s have "s \<succ>[Pareto(SD\<circ>R)] r"
      by (auto intro: SD.Pareto.strict_weak_trans)
    from improve_lottery(3)[OF r(1) s(1) this] supp_eq r 
      have "\<not>set_pmf s \<subset> set_pmf p" by simp
    with s(3) show ?thesis by contradiction
  qed
qed

end
 
lemma 
  assumes "p \<in> lotteries_on alts"
  shows   "\<exists>q\<in>lotteries_on alts. q \<succeq>[Pareto(SD\<circ>R)] p \<and> SD_efficient R q"
  using SD_efficient_lottery_exists[OF assms] by blast

end

end
