(*
  File:      Probability_Misc.thy
  Authors:   Max Haslbeck, Manuel Eberl

  Miscellaneous facts about measures and probability that are missing from the library and
  should perhaps be moved there at some point.
*)
section \<open>Auxiliary material\<close>
theory Probability_Misc
  imports "HOL-Probability.Probability"
begin

lemma measure_eqI_countable_AE':
  assumes [simp]: "sets M = Pow B" "sets N = Pow B" and subset: "\<Omega> \<subseteq> B"
  assumes ae: "AE x in M. x \<in> \<Omega>" "AE x in N. x \<in> \<Omega>" and [simp]: "countable \<Omega>"
  assumes eq: "\<And>x. x \<in> \<Omega> \<Longrightarrow> emeasure M {x} = emeasure N {x}"
  shows "M = N"
proof (rule measure_eqI)
  fix A assume A: "A \<in> sets M"
  have "emeasure N A = emeasure N {x\<in>\<Omega>. x \<in> A}"
    using ae subset A by (intro emeasure_eq_AE) auto
  also have "\<dots> = (\<integral>\<^sup>+x. emeasure N {x} \<partial>count_space {x\<in>\<Omega>. x \<in> A})"
    using A subset by (intro emeasure_countable_singleton) auto
  also have "\<dots> = (\<integral>\<^sup>+x. emeasure M {x} \<partial>count_space {x\<in>\<Omega>. x \<in> A})"
    by (intro nn_integral_cong eq[symmetric]) auto
  also have "\<dots> = emeasure M {x\<in>\<Omega>. x \<in> A}"
    using A subset by (intro emeasure_countable_singleton[symmetric]) auto
  also have "\<dots> = emeasure M A"
    using ae A subset by (intro emeasure_eq_AE) auto
  finally show "emeasure M A = emeasure N A" ..
qed simp

lemma measurable_le[measurable (raw)]:
  fixes f :: "'a \<Rightarrow> 'b::{second_countable_topology, linorder_topology}"
  assumes "f \<in> borel_measurable M" "g \<in> borel_measurable M"
  shows "Measurable.pred M (\<lambda>x. f x \<le> g x)"
  unfolding pred_def by (intro borel_measurable_le assms)

lemma measurable_eq[measurable (raw)]:
  fixes f :: "'a \<Rightarrow> 'b::{second_countable_topology, linorder_topology}"
  assumes "f \<in> borel_measurable M" "g \<in> borel_measurable M"
  shows "Measurable.pred M (\<lambda>x. f x = g x)"
  unfolding pred_def by (intro borel_measurable_eq assms)

context
  fixes M :: "'a measure"
  assumes singleton_null_set: "x \<in> space M \<Longrightarrow> {x} \<in> null_sets M"
begin

lemma countable_null_set:
  assumes "countable A" "A \<subseteq> space M"
  shows   "A \<in> null_sets M"
proof -
  have "(\<Union>x\<in>A. {x}) \<in> null_sets M" using assms 
    by (intro null_sets_UN' assms singleton_null_set) auto
  also have "(\<Union>x\<in>A. {x}) = A" by simp
  finally show ?thesis .
qed

lemma finite_null_set:
  assumes "finite A" "A \<subseteq> space M"
  shows   "A \<in> null_sets M"
  using countable_finite[OF assms(1)] countable_null_set[OF _ assms(2)] by simp
    
end

lemma measurable_inj_on_finite:
  assumes fin [measurable]: "finite I"
  assumes [measurable]: "\<And>i j. Measurable.pred (M i \<Otimes>\<^sub>M M j) (\<lambda>(x,y). x = y)"
  shows   "Measurable.pred (Pi\<^sub>M I M) (\<lambda>x. inj_on x I)" unfolding inj_on_def
  by measurable
    
lemma almost_everywhere_not_in_countable_set:
  assumes "countable A"
  assumes [measurable]: "Measurable.pred (M \<Otimes>\<^sub>M M) (\<lambda>(x,y). x = y)"
  assumes null: "\<And>x. x \<in> space M \<Longrightarrow> {x} \<in> null_sets M"
  shows   "AE x in M. x \<notin> A"
proof -
  have "A \<inter> space M \<in> null_sets M"
    by (rule countable_null_set) (insert assms(1), auto intro: null)
  hence "AE x in M. \<forall>y\<in>A. x \<noteq> y" by (rule AE_I') auto
  also have "?this \<longleftrightarrow> ?thesis" by (intro AE_cong) auto
  finally show ?thesis .
qed
    
lemma almost_everywhere_inj_on_PiM:
  assumes fin: "finite I" and prob_space: "\<And>i. i \<in> I \<Longrightarrow> prob_space (M i)"
  assumes [measurable]: "\<And>i j. Measurable.pred (M i \<Otimes>\<^sub>M M j) (\<lambda>(x,y). x = y)"
  assumes null: "\<And>i x. i \<in> I \<Longrightarrow> x \<in> space (M i) \<Longrightarrow> {x} \<in> null_sets (M i)"
  shows   "AE f in (\<Pi>\<^sub>M i\<in>I. M i). inj_on f I"
proof -
  note [measurable] = measurable_inj_on_finite
  define I' where "I' = I"
  hence "I \<subseteq> I'" by simp
  from fin and this show ?thesis
  proof (induction I rule: finite_induct)
    case (insert i I)
    interpret pair_sigma_finite "M i" "PiM I M"
      unfolding pair_sigma_finite_def using insert.prems
      by (auto intro!: prob_space_imp_sigma_finite prob_space prob_space_PiM simp: I'_def)
    from insert.hyps have [measurable]: "finite (insert i I)" by simp
    have "PiM (insert i I) M = distr (M i \<Otimes>\<^sub>M Pi\<^sub>M I M) (Pi\<^sub>M (insert i I) M) (\<lambda>(x, X). X(i := x))"
      using insert.prems 
      by (intro distr_pair_PiM_eq_PiM [symmetric] prob_space) (auto simp: I'_def)
    also have "(AE f in \<dots>. inj_on f (insert i I)) \<longleftrightarrow> 
                 (AE x in M i \<Otimes>\<^sub>M Pi\<^sub>M I M. inj_on ((snd x)(i := fst x)) (insert i I))"
      by (subst AE_distr_iff; measurable) (simp add: case_prod_unfold)?
    also have "\<dots> = (AE x in M i. AE y in Pi\<^sub>M I M. inj_on (y(i := x)) (insert i I))"
      by (rule AE_pair_iff [symmetric]) measurable
    also have "\<dots> \<longleftrightarrow> (AE x in M i. AE y in Pi\<^sub>M I M. inj_on (y(i := x)) I) \<and>
                      (AE x in M i. AE y in Pi\<^sub>M I M. x \<notin> y(i := x) ` (I - {i}))" by simp
    also have \<dots>
    proof (rule conjI, goal_cases)
      case 1
      from insert.prems have "AE f in Pi\<^sub>M I M. inj_on f I" by (intro insert.IH) auto
      hence "AE f in Pi\<^sub>M I M. inj_on (f(i := x)) I" for x
        by eventually_elim (insert insert.hyps, auto simp: inj_on_def)
      thus ?case by blast
    next
      note [measurable] = \<open>finite I\<close>
      {
        fix f
        have "f ` I \<inter> space (M i) \<in> null_sets (M i)"
          by (rule finite_null_set) 
             (insert insert.hyps insert.prems, auto intro!: null simp: I'_def)
        hence "AE x in M i. x \<notin> f(i := x) ` I"
          by (rule AE_I') (insert insert.hyps, auto split: if_splits)
        also have "(AE x in M i. x \<notin> f(i := x) ` I) \<longleftrightarrow> (AE x in M i. \<forall>y\<in>I. f y \<noteq> x)"
          using insert.hyps by (intro AE_cong) (auto split: if_splits)
        finally have "\<dots>" .
      }
      hence "AE f in Pi\<^sub>M I M. AE x in M i. \<forall>y\<in>I. f y \<noteq> x" by blast
      hence "AE x in M i. AE f in Pi\<^sub>M I M. \<forall>y\<in>I. f y \<noteq> x"
        by (subst AE_commute) simp_all
      also have "?this \<longleftrightarrow> (AE x in M i. AE y in Pi\<^sub>M I M. x \<notin> y(i := x) ` (I - {i}))"
        using insert.hyps by (intro AE_cong) (auto split: if_splits)
      finally show \<dots> .
    qed
    finally show ?case .
  qed auto
qed
  

lemma null_sets_uniform_measure:
  assumes "A \<in> sets M" "emeasure M A \<noteq> \<infinity>"
  shows   "null_sets (uniform_measure M A) = (\<lambda>B. A \<inter> B) -` null_sets M \<inter> sets M"
  using assms by (auto simp: null_sets_def)

lemma almost_everywhere_avoid_finite:
  assumes fin: "finite I"
  shows   "AE f in (\<Pi>\<^sub>M i\<in>I. uniform_measure lborel {(0::real)..1}). inj_on f I"
proof (intro almost_everywhere_inj_on_PiM fin prob_space_uniform_measure)
  fix x :: real
  show "{x} \<in> null_sets (uniform_measure lborel {0..1})"
    by (cases "x \<in> {0..1}") (auto simp: null_sets_uniform_measure)
qed auto
  
lemma almost_everywhere_avoid_countable:
  assumes "countable A"
  shows   "AE x in uniform_measure lborel {(0::real)..1}. x \<notin> A"
proof (intro almost_everywhere_not_in_countable_set assms prob_space_uniform_measure)
  fix x :: real
  show "{x} \<in> null_sets (uniform_measure lborel {0..1})"
    by (cases "x \<in> {0..1}") (auto simp: null_sets_uniform_measure)
qed auto

lemma measure_pmf_of_set:
  assumes "A \<noteq> {}" and "finite A" 
  shows   "measure_pmf (pmf_of_set A) = uniform_measure (count_space UNIV) A"
    using assms
  by (intro measure_eqI)
     (auto simp: emeasure_pmf_of_set divide_ennreal [symmetric] card_gt_0_iff
                  ennreal_of_nat_eq_real_of_nat)

lemma emeasure_distr_restrict:
  assumes "f \<in> M \<rightarrow>\<^sub>M N" "f \<in> M' \<rightarrow>\<^sub>M N'" "A \<in> sets N'" "sets M' \<subseteq> sets M" "sets N' \<subseteq> sets N"
  assumes "\<And>X. X \<in> sets M' \<Longrightarrow> emeasure M X = emeasure M' X"
  assumes "\<And>X. X \<in> sets M \<Longrightarrow> X \<subseteq> space M - space M' \<Longrightarrow> emeasure M X = 0"
  shows   "emeasure (distr M N f) A= emeasure (distr M' N' f) A"
proof -
  have space_subset: "space M' \<subseteq> space M"
    using \<open>sets M' \<subseteq> sets M\<close> by (simp add: sets_le_imp_space_le)
  have "emeasure (distr M N f) A = emeasure M (f -` A \<inter> space M)"
    using assms by (subst emeasure_distr) auto
  also have "f -` A \<inter> space M = f -` A \<inter> space M' \<union> f -` A \<inter> (space M - space M')"
    using space_subset by blast
  also have "emeasure M \<dots> = emeasure M (f -` A \<inter> space M')"
  proof (intro emeasure_Un_null_set)
    show "f -` A \<inter> space M' \<in> sets M"
      using assms by auto
    have "f -` A \<inter> (space M - space M') \<in> sets M"
      using assms by (metis Int_Diff measurable_sets sets.Diff sets.top subsetCE)
    moreover from this have "emeasure M (f -` A \<inter> (space M - space M')) = 0"
      by (intro assms) auto
    ultimately show "f -` A \<inter> (space M - space M') \<in> null_sets M"
      unfolding null_sets_def by blast
  qed
  also have "\<dots> = emeasure M' (f -` A \<inter> space M')"
    using assms by (intro assms) auto
  also have "\<dots> = emeasure (distr M' N' f) A"
    using assms by (subst emeasure_distr) auto
  finally show ?thesis .
qed

lemma distr_uniform_measure_count_space_inj:
  assumes "inj_on f A'" "A' \<subseteq> A" "f ` A \<subseteq> B" "finite A'"
  shows   "distr (uniform_measure (count_space A) A') (count_space B) f =
             uniform_measure (count_space B) (f ` A')" (is "?lhs = ?rhs")
proof (rule measure_eqI, goal_cases)
  case (2 X)
  hence X_subset: "X \<subseteq> B" by simp
  from assms have eq: "f ` A' \<inter> X = f ` (A' \<inter> (f -` X \<inter> A))"
    by auto
  from assms have [measurable]: "f \<in> count_space A \<rightarrow>\<^sub>M count_space B"
    by (subst measurable_count_space_eq1) auto
  from X_subset have "emeasure ?lhs X = 
                        emeasure (uniform_measure (count_space A) A') (f -` X \<inter> A)"
    by (subst emeasure_distr) auto
  also from assms X_subset 
    have "\<dots> = emeasure (count_space A) (A' \<inter> (f -` X \<inter> A)) / emeasure (count_space A) A'"
    by (intro emeasure_uniform_measure) auto
  also from assms have "\<dots> = of_nat (card (A' \<inter> (f -` X \<inter> A))) / of_nat (card A')"
    by (subst (1 2) emeasure_count_space) auto
  also have "card (A' \<inter> (f -` X \<inter> A)) = card (f ` (A' \<inter> (f -` X \<inter> A)))"
    using assms by (intro card_image [symmetric]) (auto simp: inj_on_def)
  also have "f ` (A' \<inter> (f -` X \<inter> A)) = f ` A' \<inter> X"
    using assms by auto
  also have "of_nat (card A') = of_nat (card (f ` A'))"
    using assms by (subst card_image) auto
  also have "of_nat (card (f ` A' \<inter> X)) / \<dots> = 
               emeasure (count_space B) (f ` A' \<inter> X) / emeasure (count_space B) (f ` A')"
    using assms by (subst (1 2) emeasure_count_space) auto
  also from assms X_subset have "\<dots> = emeasure ?rhs X" 
    by (intro emeasure_uniform_measure [symmetric]) auto
  finally show ?case .
qed simp_all

lemma (in pair_prob_space) pair_measure_bind:
  assumes [measurable]: "f \<in> M1 \<Otimes>\<^sub>M M2 \<rightarrow>\<^sub>M subprob_algebra N"
  shows "(M1 \<Otimes>\<^sub>M M2) \<bind> f = do {x \<leftarrow> M1; y \<leftarrow> M2; f (x, y)}"
proof -
  note M1 = M1.prob_space_axioms and M2 = M2.prob_space_axioms
  have [measurable]: "M1 \<in> space (subprob_algebra M1)"
    by (rule M1.M_in_subprob)
  have [measurable]: "M2 \<in> space (subprob_algebra M2)"
    by (rule M2.M_in_subprob)
  have "(M1 \<Otimes>\<^sub>M M2) = M1 \<bind> (\<lambda>x. M2 \<bind> (\<lambda>y. return (M1 \<Otimes>\<^sub>M M2) (x, y)))"
    by (subst pair_measure_eq_bind) simp_all
  also have "\<dots> \<bind> f = M1 \<bind> (\<lambda>x. (M2 \<bind> (\<lambda>y. return (M1 \<Otimes>\<^sub>M M2) (x, y))) \<bind> f)"
    by (rule bind_assoc) measurable
  also have "\<dots> = M1 \<bind> (\<lambda>x. M2 \<bind> (\<lambda>xa. return (M1 \<Otimes>\<^sub>M M2) (x, xa) \<bind> f))"
    by (intro bind_cong refl bind_assoc) measurable
  also have "\<dots> = do {x \<leftarrow> M1; y \<leftarrow> M2; f (x, y)}"
    by (intro bind_cong refl bind_return)
       (measurable, simp_all add: space_pair_measure)
  finally show ?thesis .
qed

lemma count_space_singleton_conv_return: 
  "count_space {x} = return (count_space {x}) x"
proof (rule measure_eqI)
  fix A assume "A \<in> sets (count_space {x})"
  hence "A \<subseteq> {x}" by auto
  hence "A = {} \<or> A = {x}" by (cases "x \<in> A") auto
  thus "emeasure (count_space {x}) A = emeasure (return (count_space {x}) x) A"
    by auto
qed auto
  
lemma distr_count_space_singleton [simp]:
    "f x \<in> space M \<Longrightarrow> distr (count_space {x}) M f = return M (f x)"
  by (subst count_space_singleton_conv_return, subst distr_return) simp_all

lemma uniform_measure_count_space_singleton [simp]:
  assumes "{x} \<in> sets M" "emeasure M {x} \<noteq> 0" "emeasure M {x} < \<infinity>"
  shows   "uniform_measure M {x} = return M x"
proof (rule measure_eqI)
  fix A assume A: "A \<in> sets (uniform_measure M {x})"
  show "emeasure (uniform_measure M {x}) A = emeasure (return M x) A"
    by (cases "x \<in> A") (insert assms A, auto)
qed simp_all

lemma PiM_uniform_measure_permute:
  fixes a b :: real
  assumes "g permutes A" "a < b"
  shows   "distr (PiM A (\<lambda>_. uniform_measure lborel {a..b})) (PiM A (\<lambda>_. lborel)) (\<lambda>f. f \<circ> g) =
             PiM A (\<lambda>_. uniform_measure lborel {a..b})"
proof -
  have "distr (PiM A (\<lambda>_. uniform_measure lborel {a..b})) (PiM A (\<lambda>_. lborel)) (\<lambda>f. f \<circ> g) =
          distr (PiM A (\<lambda>_. uniform_measure lborel {a..b})) 
            (PiM A (\<lambda>_. uniform_measure lborel {a..b})) (\<lambda>f. \<lambda>x\<in>A. f (g x))" using assms
    by (intro distr_cong sets_PiM_cong refl) 
       (auto simp: fun_eq_iff space_PiM PiE_def extensional_def permutes_in_image[of g A])  
  also from assms have "\<dots> = Pi\<^sub>M A (\<lambda>i. uniform_measure lborel {a..b})"
    by (intro distr_PiM_reindex)
       (auto simp: permutes_inj_on permutes_in_image[of g A] intro!: prob_space_uniform_measure)
  finally show ?thesis .
qed

lemma ennreal_fact [simp]: "ennreal (fact n) = fact n"
  by (induction n) (auto simp: algebra_simps ennreal_mult' ennreal_of_nat_eq_real_of_nat)

lemma inverse_ennreal_unique:
  assumes "a * (b :: ennreal) = 1"
  shows   "b = inverse a"
  using assms
  by (metis divide_ennreal_def ennreal_inverse_1 ennreal_top_eq_mult_iff mult.comm_neutral 
        mult_divide_eq_ennreal mult_eq_0_iff semiring_normalization_rules(7))

end