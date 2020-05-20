section \<open>Stochastic Vectors and Probability Mass Functions\<close>

text \<open>We prove that over a finite type, stochastic vectors and probability
  mass functions are essentially the same thing: one can convert between both
  representations.\<close>

theory Stochastic_Vector_PMF
  imports Stochastic_Matrix
  "HOL-Probability.Probability_Mass_Function" 
begin

lemma sigma_algebra_UNIV_finite[simp]: "sigma_algebra (UNIV :: 'a :: finite set) UNIV"
proof (unfold_locales, goal_cases)
  case (4 a b)
  show ?case by (intro exI[of _ "{a-b}"], auto)
qed auto

definition measure_of_st_vec' :: "'a st_vec \<Rightarrow> 'a :: finite set \<Rightarrow> ennreal" where
  "measure_of_st_vec' x I = sum (\<lambda> i. st_vec x $ i) I" 

lemma positive_measure_of_st_vec'[simp]: "positive A (measure_of_st_vec' x)" 
  unfolding measure_of_st_vec'_def positive_def by auto

lemma measure_space_measure_of_st_vec': "measure_space UNIV UNIV (measure_of_st_vec' x)" 
  unfolding measure_space_def 
proof (simp, simp add: countably_additive_def measure_of_st_vec'_def disjoint_family_on_def,
  clarify, goal_cases)
  case (1 A)
  let ?x = "st_vec x" 
  define N where "N = {i. A i \<noteq> {}}" 
  let ?A = "\<Union>(A ` N)" 
  have "finite B \<Longrightarrow> B \<subseteq> ?A \<Longrightarrow> \<exists> K. finite K \<and> K \<subseteq> N \<and> B \<subseteq> \<Union>(A ` K)" for B
  proof (induct rule: finite_induct)
    case (insert b B)
    from insert(3-4) obtain K where K: "finite K" "K \<subseteq> N" "B \<subseteq> \<Union>(A ` K)" by auto
    from insert(4) obtain a where a: "a \<in> N" "b \<in> A a" by auto
    show ?case by (intro exI[of _ "insert a K"], insert a K, auto)
  qed auto
  from this[OF _ subset_refl] obtain K where *: "finite K" "K \<subseteq> N" "\<Union>(A ` K) = ?A" by auto
  {
    assume "K \<subset> N" 
    then obtain n where **: "n \<in> N" "n \<notin> K" by auto
    from this[unfolded N_def] obtain a where a: "a \<in> A n" by auto
    with ** * obtain k where ***: "k \<in> K" "a \<in> A k" by force
    from ** *** have "n \<noteq> k" by auto
    from 1[rule_format, OF this] have "A n \<inter> A k = {}" by auto
    with *** a have False by auto
  }
  with * have fin: "finite N" by auto
  have id: "\<Union>(A ` UNIV) = ?A" unfolding N_def by auto
  show "(\<Sum>i. ennreal (sum (($h) ?x) (A i))) =
    ennreal (sum (($h) ?x) (\<Union>(A ` UNIV)))" unfolding id
    apply (subst suminf_finite[OF fin], (auto simp: N_def)[1])
    apply (subst sum_ennreal, (insert non_neg_vec_st_vec[of x], auto simp: non_neg_vec_def intro!: sum_nonneg)[1])
    apply (rule arg_cong[of _ _ ennreal])
    apply (subst sum.UNION_disjoint[OF fin], insert 1, auto)
    done
qed

context begin
setup_lifting type_definition_measure

lift_definition measure_of_st_vec :: "'a st_vec \<Rightarrow> 'a :: finite measure" is
  "\<lambda> x. (UNIV, UNIV, measure_of_st_vec' x)" 
  by (auto simp: measure_space_measure_of_st_vec')

lemma sets_measure_of_st_vec[simp]: "sets (measure_of_st_vec x) = UNIV"
  unfolding sets_def by (transfer, auto)

lemma space_measure_of_st_vec[simp]: "space (measure_of_st_vec x) = UNIV"
  unfolding space_def by (transfer, auto)

lemma emeasure_measure_of_st_vec[simp]: "emeasure (measure_of_st_vec x) I = 
  sum (\<lambda> i. st_vec x $ i) I" 
  unfolding emeasure_def by (transfer', auto simp: measure_of_st_vec'_def)

lemma prob_space_measure_of_st_vec: "prob_space (measure_of_st_vec x)" 
  by (unfold_locales, intro exI[of _ UNIV], auto, transfer, auto simp: stoch_vec_def)
end

lift_definition st_vec_of_pmf :: "'i :: finite pmf \<Rightarrow> 'i st_vec" is
  "\<lambda> pmF. vec_lambda (pmf pmF)" 
proof (intro conjI, goal_cases)
  case (2 pmF)
  show "stoch_vec (vec_lambda (pmf pmF))" 
    unfolding stoch_vec_def 
    apply auto
    apply (unfold measure_pmf_UNIV[of pmF, symmetric]) 
    by (simp add: measure_pmf_conv_infsetsum)
qed (auto simp: non_neg_vec_def stoch_vec_def)

context pmf_as_measure
begin
lift_definition pmf_of_st_vec :: "'a :: finite st_vec \<Rightarrow> 'a pmf" is measure_of_st_vec
proof (goal_cases)
  case (1 x)
  show ?case
    by (auto simp: prob_space_measure_of_st_vec measure_def)
      (rule AE_I[where N = "{i. st_vec x $ i = 0}"], auto)
qed

lemma st_vec_st_vec_of_pmf[simp]:
  "st_vec (st_vec_of_pmf x) $ i = pmf x i" 
  by (simp add: st_vec_of_pmf.rep_eq)

lemma pmf_pmf_of_st_vec[simp]: "pmf (pmf_of_st_vec x) i = st_vec x $ i" 
  by (transfer, auto simp: measure_def)

lemma st_vec_of_pmf_pmf_of_st_vec[simp]: "st_vec_of_pmf (pmf_of_st_vec x) = x" 
proof -
  have "st_vec (st_vec_of_pmf (pmf_of_st_vec x)) = st_vec x"
    unfolding vec_eq_iff by auto
  thus ?thesis using st_vec_inject by blast
qed

lemma pmf_of_st_vec_inj: "(pmf_of_st_vec x = pmf_of_st_vec y) = (x = y)" 
  by (metis st_vec_of_pmf_pmf_of_st_vec)
end  
end