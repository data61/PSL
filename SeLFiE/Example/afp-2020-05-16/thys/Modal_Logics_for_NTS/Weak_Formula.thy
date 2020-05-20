theory Weak_Formula
imports
  Weak_Transition_System
  Disjunction
begin

section \<open>Weak Formulas\<close>

subsection \<open>Lemmas about \texorpdfstring{$\alpha$}{alpha}-equivalence involving \texorpdfstring{$\tau$}{tau}\<close>

context weak_nominal_ts
begin

  lemma Act_tau_eq_iff [simp]:
    "Act \<tau> x1 = Act \<alpha> x2 \<longleftrightarrow> \<alpha> = \<tau> \<and> x2 = x1"
    (is "?l \<longleftrightarrow> ?r")
  proof
    assume "?l"
    then obtain p where p_\<alpha>: "p \<bullet> \<tau> = \<alpha>" and p_x: "p \<bullet> x1 = x2" and fresh: "(supp x1 - bn \<tau>) \<sharp>* p"
      by (metis Act_eq_iff_perm)
    from p_\<alpha> have "\<alpha> = \<tau>"
      by (metis tau_eqvt)
    moreover from fresh and p_x have "x2 = x1"
      by (simp add: supp_perm_eq)
    ultimately show "?r" ..
  next
    assume "?r" then show "?l"
      by simp
  qed

end


subsection \<open>Weak action modality\<close>

text \<open>The definition of (strong) formulas is parametric in the index type, but from now on we
want to work with a fixed (sufficiently large) index type.

Also, we use~@{term \<tau>} in our definition of weak formulas.\<close>

locale indexed_weak_nominal_ts = weak_nominal_ts satisfies transition
  for satisfies :: "'state::fs \<Rightarrow> 'pred::fs \<Rightarrow> bool" (infix "\<turnstile>" 70)
  and transition :: "'state \<Rightarrow> ('act::bn,'state) residual \<Rightarrow> bool" (infix "\<rightarrow>" 70) +
  assumes card_idx_perm: "|UNIV::perm set| <o |UNIV::'idx set|"
      and card_idx_state: "|UNIV::'state set| <o |UNIV::'idx set|"
      and card_idx_nat: "|UNIV::nat set| <o |UNIV::'idx set|"
begin

  text \<open>The assumption @{thm card_idx_nat} is redundant: it is already implied by
  @{thm card_idx_perm}.  A formal proof of this fact is left for future work.\<close>

  lemma card_idx_nat' [simp]:
    "|UNIV::nat set| <o natLeq +c |UNIV::'idx set|"
  proof -
    note card_idx_nat
    also have "|UNIV :: 'idx set| \<le>o natLeq +c |UNIV :: 'idx set|"
      by (metis Cnotzero_UNIV ordLeq_csum2)
    finally show ?thesis .
  qed

  primrec tau_steps :: "('idx,'pred::fs,'act::bn) formula \<Rightarrow> nat \<Rightarrow> ('idx,'pred,'act) formula"
    where
      "tau_steps x 0       = x"
    | "tau_steps x (Suc n) = Act \<tau> (tau_steps x n)"

  lemma tau_steps_eqvt (*[eqvt]*) [simp]:
    "p \<bullet> tau_steps x n = tau_steps (p \<bullet> x) (p \<bullet> n)"
    by (induct n) (simp_all add: permute_nat_def tau_eqvt)

  lemma tau_steps_eqvt' [simp]:
    "p \<bullet> tau_steps x = tau_steps (p \<bullet> x)"
    by (simp add: permute_fun_def)

  lemma tau_steps_eqvt_raw [simp]:
    "p \<bullet> tau_steps = tau_steps"
    by (simp add: permute_fun_def)

  lemma tau_steps_add [simp]:
    "tau_steps (tau_steps x m) n = tau_steps x (m + n)"
    by (induct n) auto

  lemma tau_steps_not_self:
    "x = tau_steps x n \<longleftrightarrow> n = 0"
  proof
    assume "x = tau_steps x n" then show "n = 0"
      proof (induct n arbitrary: x)
        case 0 show ?case ..
      next
        case (Suc n)
        then have "x = Act \<tau> (tau_steps x n)"
          by simp
        then show "Suc n = 0"
          proof (induct x)
            case (Act \<alpha> x)
            then have "x = tau_steps (Act \<tau> x) n"
              by (metis Act_tau_eq_iff)
            with Act.hyps show ?thesis
              by (metis add_Suc tau_steps.simps(2) tau_steps_add)
          qed simp_all
      qed
  next
    assume "n = 0" then show "x = tau_steps x n"
      by simp
  qed

  definition weak_tau_modality :: "('idx,'pred::fs,'act::bn) formula \<Rightarrow> ('idx,'pred,'act) formula"
    where
      "weak_tau_modality x \<equiv> Disj (map_bset (tau_steps x) (Abs_bset UNIV))"

  lemma finite_supp_map_bset_tau_steps [simp]:
    "finite (supp (map_bset (tau_steps x) (Abs_bset UNIV :: nat set['idx])))"
  proof -
    have "eqvt map_bset" and "eqvt tau_steps"
      by (simp add: eqvtI)+
    then have "supp (map_bset (tau_steps x)) \<subseteq> supp x"
      using supp_fun_eqvt supp_fun_app supp_fun_app_eqvt by blast
    moreover have "supp (Abs_bset UNIV :: nat set['idx]) = {}"
      by (simp add: eqvtI supp_fun_eqvt)
    ultimately have "supp (map_bset (tau_steps x) (Abs_bset UNIV :: nat set['idx])) \<subseteq> supp x"
      using supp_fun_app by blast
    then show ?thesis
      by (metis finite_subset finite_supp)
  qed

  lemma weak_tau_modality_eqvt (*[eqvt]*) [simp]:
    "p \<bullet> weak_tau_modality x = weak_tau_modality (p \<bullet> x)"
    unfolding weak_tau_modality_def by (simp add: map_bset_eqvt)

  lemma weak_tau_modality_eq_iff [simp]:
    "weak_tau_modality x = weak_tau_modality y \<longleftrightarrow> x = y"
  proof
    assume "weak_tau_modality x = weak_tau_modality y"
    then have "map_bset (tau_steps x) (Abs_bset UNIV :: _ set['idx]) = map_bset (tau_steps y) (Abs_bset UNIV)"
      unfolding weak_tau_modality_def by simp
    with card_idx_nat' have "range (tau_steps x) = range (tau_steps y)"
      (is "?X = ?Y")
      by (metis Abs_bset_inverse' map_bset.rep_eq)
    then have "x \<in> range (tau_steps y)" and "y \<in> range (tau_steps x)"
      by (metis range_eqI tau_steps.simps(1))+
    then obtain nx ny where x: "x = tau_steps y nx" and y: "y = tau_steps x ny"
      by blast
    then have "ny + nx = 0"
      by (simp add: tau_steps_not_self)
    with x and y show "x = y"
      by simp
  next
    assume "x = y" then show "weak_tau_modality x = weak_tau_modality y"
      by simp
  qed

  lemma supp_weak_tau_modality [simp]:
    "supp (weak_tau_modality x) = supp x"
    unfolding supp_def by simp

  lemma Act_weak_tau_modality_eq_iff [simp]:
    "Act \<alpha>1 (weak_tau_modality x1) = Act \<alpha>2 (weak_tau_modality x2) \<longleftrightarrow> Act \<alpha>1 x1 = Act \<alpha>2 x2"
    by (simp add: Act_eq_iff_perm)

  definition weak_action_modality :: "'act \<Rightarrow> ('idx,'pred::fs,'act::bn) formula \<Rightarrow> ('idx,'pred,'act) formula" ("\<langle>\<langle>_\<rangle>\<rangle>_")
    where
      "\<langle>\<langle>\<alpha>\<rangle>\<rangle>x \<equiv> if \<alpha> = \<tau> then weak_tau_modality x else weak_tau_modality (Act \<alpha> (weak_tau_modality x))"

  lemma weak_action_modality_eqvt (*[eqvt]*) [simp]:
    "p \<bullet> (\<langle>\<langle>\<alpha>\<rangle>\<rangle>x) = \<langle>\<langle>p \<bullet> \<alpha>\<rangle>\<rangle>(p \<bullet> x)"
    using tau_eqvt weak_action_modality_def by fastforce

  lemma weak_action_modality_tau:
    "(\<langle>\<langle>\<tau>\<rangle>\<rangle>x) = weak_tau_modality x"
    unfolding weak_action_modality_def by simp

  lemma weak_action_modality_not_tau:
    assumes "\<alpha> \<noteq> \<tau>"
    shows "(\<langle>\<langle>\<alpha>\<rangle>\<rangle>x) = weak_tau_modality (Act \<alpha> (weak_tau_modality x))"
    using assms unfolding weak_action_modality_def by simp

  text \<open>Equality is modulo $\alpha$-equivalence.\<close>
    
  text \<open>Note that the converse of the following lemma does not hold. For instance,
  for~@{prop "\<alpha> \<noteq> \<tau>"} we have @{prop "(\<langle>\<langle>\<tau>\<rangle>\<rangle>(Act \<alpha> (weak_tau_modality x))) = \<langle>\<langle>\<alpha>\<rangle>\<rangle>x"} by definition,
  but clearly not @{prop "Act \<tau> (Act \<alpha> (weak_tau_modality x)) = Act \<alpha> x"}.\<close>

  lemma weak_action_modality_eq:
    assumes "Act \<alpha>1 x1 = Act \<alpha>2 x2"
    shows "(\<langle>\<langle>\<alpha>1\<rangle>\<rangle>x1) = (\<langle>\<langle>\<alpha>2\<rangle>\<rangle>x2)"
  proof (cases "\<alpha>1 = \<tau>")
    case True
    with assms have "\<alpha>2 = \<alpha>1 \<and> x2 = x1"
      by (metis Act_tau_eq_iff)
    then show ?thesis
      by simp
  next
    case False
    from assms obtain p where 1: "supp x1 - bn \<alpha>1 = supp x2 - bn \<alpha>2" and 2: "(supp x1 - bn \<alpha>1) \<sharp>* p"
      and 3: "p \<bullet> x1 = x2" and 4: "supp \<alpha>1 - bn \<alpha>1 = supp \<alpha>2 - bn \<alpha>2" and 5: "(supp \<alpha>1 - bn \<alpha>1) \<sharp>* p"
      and 6: "p \<bullet> \<alpha>1 = \<alpha>2"
      by (metis Act_eq_iff_perm)
    from 1 have "supp (weak_tau_modality x1) - bn \<alpha>1 = supp (weak_tau_modality x2) - bn \<alpha>2"
      by (metis supp_weak_tau_modality)
    moreover from 2 have "(supp (weak_tau_modality x1) - bn \<alpha>1) \<sharp>* p"
      by (metis supp_weak_tau_modality)
    moreover from 3 have "p \<bullet> weak_tau_modality x1 = weak_tau_modality x2"
      by (metis weak_tau_modality_eqvt)
    ultimately have "Act \<alpha>1 (weak_tau_modality x1) = Act \<alpha>2 (weak_tau_modality x2)"
      using 4 and 5 and 6 and Act_eq_iff_perm by blast
    moreover from \<open>\<alpha>1 \<noteq> \<tau>\<close> and assms have "\<alpha>2 \<noteq> \<tau>"
      by (metis Act_tau_eq_iff)
    ultimately show ?thesis
      using \<open>\<alpha>1 \<noteq> \<tau>\<close> by (simp add: weak_action_modality_not_tau)
  qed


  subsection \<open>Weak formulas\<close>

  inductive weak_formula :: "('idx,'pred::fs,'act::bn) formula \<Rightarrow> bool"
    where
      wf_Conj: "finite (supp xset) \<Longrightarrow> (\<And>x. x \<in> set_bset xset \<Longrightarrow> weak_formula x) \<Longrightarrow> weak_formula (Conj xset)"
    | wf_Not: "weak_formula x \<Longrightarrow> weak_formula (Not x)"
    | wf_Act: "weak_formula x \<Longrightarrow> weak_formula (\<langle>\<langle>\<alpha>\<rangle>\<rangle>x)"
    | wf_Pred: "weak_formula x \<Longrightarrow> weak_formula (\<langle>\<langle>\<tau>\<rangle>\<rangle>(Conj (binsert (Pred \<phi>) (bsingleton x))))"

  lemma finite_supp_wf_Pred [simp]: "finite (supp (binsert (Pred \<phi>) (bsingleton x)))"
  proof -
    have "supp (bsingleton x) \<subseteq> supp x"
      by (simp add: eqvtI supp_fun_app_eqvt)
    moreover have "eqvt binsert"
      by (simp add: eqvtI)
    ultimately have "supp (binsert (Pred \<phi>) (bsingleton x)) \<subseteq> supp \<phi> \<union> supp x"
      using supp_fun_app supp_fun_app_eqvt by fastforce
    then show ?thesis
      by (metis finite_UnI finite_supp rev_finite_subset)
  qed

  text \<open>@{const weak_formula} is equivariant.\<close>

  lemma weak_formula_eqvt (*[eqvt]*) [simp]: "weak_formula x \<Longrightarrow> weak_formula (p \<bullet> x)"
  proof (induct rule: weak_formula.induct)
    case (wf_Conj xset) then show ?case
      by simp (metis (no_types, lifting) imageE permute_finite permute_set_eq_image set_bset_eqvt supp_eqvt weak_formula.wf_Conj)
  next
    case (wf_Not x) then show ?case
      by (simp add: weak_formula.wf_Not)
  next
    case (wf_Act x \<alpha>) then show ?case
      by (simp add: weak_formula.wf_Act)
  next
    case (wf_Pred x \<phi>) then show ?case
      by (simp add: tau_eqvt weak_formula.wf_Pred)
  qed

end

end
