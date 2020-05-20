(*
    Author:   Benedikt Seidl
    License:  BSD
*)

section \<open>The ``after''-Function\<close>

theory After
imports
  LTL.LTL LTL.Equivalence_Relations Syntactic_Fragments_and_Stability
begin

subsection \<open>Definition of af\<close>

primrec af_letter :: "'a ltln \<Rightarrow> 'a set \<Rightarrow> 'a ltln"
where
  "af_letter true\<^sub>n \<nu> = true\<^sub>n"
| "af_letter false\<^sub>n \<nu> = false\<^sub>n"
| "af_letter prop\<^sub>n(a) \<nu> = (if a \<in> \<nu> then true\<^sub>n else false\<^sub>n)"
| "af_letter nprop\<^sub>n(a) \<nu>  = (if a \<notin> \<nu> then true\<^sub>n else false\<^sub>n)"
| "af_letter (\<phi> and\<^sub>n \<psi>) \<nu> = (af_letter \<phi> \<nu>) and\<^sub>n (af_letter \<psi> \<nu>)"
| "af_letter (\<phi> or\<^sub>n \<psi>) \<nu> = (af_letter \<phi> \<nu>) or\<^sub>n (af_letter \<psi> \<nu>)"
| "af_letter (X\<^sub>n \<phi>) \<nu> = \<phi>"
| "af_letter (\<phi> U\<^sub>n \<psi>) \<nu> = (af_letter \<psi> \<nu>) or\<^sub>n ((af_letter \<phi> \<nu>) and\<^sub>n (\<phi> U\<^sub>n \<psi>))"
| "af_letter (\<phi> R\<^sub>n \<psi>) \<nu> = (af_letter \<psi> \<nu>) and\<^sub>n ((af_letter \<phi> \<nu>) or\<^sub>n (\<phi> R\<^sub>n \<psi>))"
| "af_letter (\<phi> W\<^sub>n \<psi>) \<nu> = (af_letter \<psi> \<nu>) or\<^sub>n ((af_letter \<phi> \<nu>) and\<^sub>n (\<phi> W\<^sub>n \<psi>))"
| "af_letter (\<phi> M\<^sub>n \<psi>) \<nu> = (af_letter \<psi> \<nu>) and\<^sub>n ((af_letter \<phi> \<nu>) or\<^sub>n (\<phi> M\<^sub>n \<psi>))"

abbreviation af :: "'a ltln \<Rightarrow> 'a set list \<Rightarrow> 'a ltln"
where
  "af \<phi> w \<equiv> foldl af_letter \<phi> w"


lemma af_decompose:
  "af (\<phi> and\<^sub>n \<psi>) w = (af \<phi> w) and\<^sub>n (af \<psi> w)"
  "af (\<phi> or\<^sub>n \<psi>) w = (af \<phi> w) or\<^sub>n (af \<psi> w)"
  by (induction w rule: rev_induct) simp_all

lemma af_simps[simp]:
  "af true\<^sub>n w = true\<^sub>n"
  "af false\<^sub>n w = false\<^sub>n"
  "af (X\<^sub>n \<phi>) (x # xs) = af \<phi> xs"
  by (induction w) simp_all

lemma af_ite_simps[simp]:
  "af (if P then true\<^sub>n else false\<^sub>n) w = (if P then true\<^sub>n else false\<^sub>n)"
  "af (if P then false\<^sub>n else true\<^sub>n) w = (if P then false\<^sub>n else true\<^sub>n)"
  by simp_all

lemma af_subsequence_append:
  "i \<le> j \<Longrightarrow> j \<le> k \<Longrightarrow> af (af \<phi> (w [i \<rightarrow> j])) (w [j \<rightarrow> k]) = af \<phi> (w [i \<rightarrow> k])"
  by (metis foldl_append le_Suc_ex map_append subsequence_def upt_add_eq_append)

lemma af_subsequence_U:
  "af (\<phi> U\<^sub>n \<psi>) (w [0 \<rightarrow> Suc n]) = (af \<psi> (w [0 \<rightarrow> Suc n])) or\<^sub>n ((af \<phi> (w [0 \<rightarrow> Suc n])) and\<^sub>n af (\<phi> U\<^sub>n \<psi>) (w [1 \<rightarrow> Suc n]))"
  by (induction n) fastforce+

lemma af_subsequence_U':
  "af (\<phi> U\<^sub>n \<psi>) (a # xs) = (af \<psi> (a # xs)) or\<^sub>n ((af \<phi> (a # xs)) and\<^sub>n af (\<phi> U\<^sub>n \<psi>) xs)"
  by (simp add: af_decompose)

lemma af_subsequence_R:
  "af (\<phi> R\<^sub>n \<psi>) (w [0 \<rightarrow> Suc n]) = (af \<psi> (w [0 \<rightarrow> Suc n])) and\<^sub>n ((af \<phi> (w [0 \<rightarrow> Suc n])) or\<^sub>n af (\<phi> R\<^sub>n \<psi>) (w [1 \<rightarrow> Suc n]))"
  by (induction n) fastforce+

lemma af_subsequence_R':
  "af (\<phi> R\<^sub>n \<psi>) (a # xs) = (af \<psi> (a # xs)) and\<^sub>n ((af \<phi> (a # xs)) or\<^sub>n af (\<phi> R\<^sub>n \<psi>) xs)"
  by (simp add: af_decompose)

lemma af_subsequence_W:
  "af (\<phi> W\<^sub>n \<psi>) (w [0 \<rightarrow> Suc n]) = (af \<psi> (w [0 \<rightarrow> Suc n])) or\<^sub>n ((af \<phi> (w [0 \<rightarrow> Suc n])) and\<^sub>n af (\<phi> W\<^sub>n \<psi>) (w [1 \<rightarrow> Suc n]))"
  by (induction n) fastforce+

lemma af_subsequence_W':
  "af (\<phi> W\<^sub>n \<psi>) (a # xs) = (af \<psi> (a # xs)) or\<^sub>n ((af \<phi> (a # xs)) and\<^sub>n af (\<phi> W\<^sub>n \<psi>) xs)"
  by (simp add: af_decompose)

lemma af_subsequence_M:
  "af (\<phi> M\<^sub>n \<psi>) (w [0 \<rightarrow> Suc n]) = (af \<psi> (w [0 \<rightarrow> Suc n])) and\<^sub>n ((af \<phi> (w [0 \<rightarrow> Suc n])) or\<^sub>n af (\<phi> M\<^sub>n \<psi>) (w [1 \<rightarrow> Suc n]))"
  by (induction n) fastforce+

lemma af_subsequence_M':
  "af (\<phi> M\<^sub>n \<psi>) (a # xs) = (af \<psi> (a # xs)) and\<^sub>n ((af \<phi> (a # xs)) or\<^sub>n af (\<phi> M\<^sub>n \<psi>) xs)"
  by (simp add: af_decompose)

lemma suffix_build[simp]:
  "suffix (Suc n) (x ## xs) = suffix n xs"
  by fastforce

lemma af_letter_build:
  "(x ## w) \<Turnstile>\<^sub>n \<phi> \<longleftrightarrow> w \<Turnstile>\<^sub>n af_letter \<phi> x"
proof (induction \<phi> arbitrary: x w)
  case (Until_ltln \<phi> \<psi>)
  then show ?case
    unfolding ltln_expand_Until by force
next
  case (Release_ltln \<phi> \<psi>)
  then show ?case
    unfolding ltln_expand_Release by force
next
  case (WeakUntil_ltln \<phi> \<psi>)
  then show ?case
    unfolding ltln_expand_WeakUntil by force
next
  case (StrongRelease_ltln \<phi> \<psi>)
  then show ?case
    unfolding ltln_expand_StrongRelease by force
qed simp+

lemma af_ltl_continuation:
  "(w \<frown> w') \<Turnstile>\<^sub>n \<phi> \<longleftrightarrow> w' \<Turnstile>\<^sub>n af \<phi> w"
proof (induction w arbitrary: \<phi> w')
  case (Cons x xs)
  then show ?case
    using af_letter_build by fastforce
qed simp



subsection \<open>Range of the after function\<close>

lemma af_letter_atoms:
  "atoms_ltln (af_letter \<phi> \<nu>) \<subseteq> atoms_ltln \<phi>"
  by (induction \<phi>) auto

lemma af_atoms:
  "atoms_ltln (af \<phi> w) \<subseteq> atoms_ltln \<phi>"
  by (induction w rule: rev_induct) (simp, insert af_letter_atoms, fastforce)

lemma af_letter_nested_prop_atoms:
  "nested_prop_atoms (af_letter \<phi> \<nu>) \<subseteq> nested_prop_atoms \<phi>"
  by (induction \<phi>) auto

lemma af_nested_prop_atoms:
  "nested_prop_atoms (af \<phi> w) \<subseteq> nested_prop_atoms \<phi>"
  by (induction w rule: rev_induct) (auto, insert af_letter_nested_prop_atoms, blast)

lemma af_letter_range:
  "range (af_letter \<phi>) \<subseteq> {\<psi>. nested_prop_atoms \<psi> \<subseteq> nested_prop_atoms \<phi>}"
  using af_letter_nested_prop_atoms by blast

lemma af_range:
  "range (af \<phi>) \<subseteq> {\<psi>. nested_prop_atoms \<psi> \<subseteq> nested_prop_atoms \<phi>}"
  using af_nested_prop_atoms by blast



subsection \<open>Subformulas of the after function\<close>

lemma af_letter_subformulas\<^sub>\<mu>:
  "subformulas\<^sub>\<mu> (af_letter \<phi> \<xi>) = subformulas\<^sub>\<mu> \<phi>"
  by (induction \<phi>) auto

lemma af_subformulas\<^sub>\<mu>:
  "subformulas\<^sub>\<mu> (af \<phi> w) = subformulas\<^sub>\<mu> \<phi>"
  using af_letter_subformulas\<^sub>\<mu>
  by (induction w arbitrary: \<phi> rule: rev_induct) (simp, fastforce)

lemma af_letter_subformulas\<^sub>\<nu>:
  "subformulas\<^sub>\<nu> (af_letter \<phi> \<xi>) = subformulas\<^sub>\<nu> \<phi>"
  by (induction \<phi>) auto

lemma af_subformulas\<^sub>\<nu>:
  "subformulas\<^sub>\<nu> (af \<phi> w) = subformulas\<^sub>\<nu> \<phi>"
  using af_letter_subformulas\<^sub>\<nu>
  by (induction w arbitrary: \<phi> rule: rev_induct) (simp, fastforce)



subsection \<open>Stability and the after function\<close>

lemma \<G>\<F>_af:
  "\<G>\<F> (af \<phi> (prefix i w)) (suffix i w) = \<G>\<F> \<phi> (suffix i w)"
  unfolding \<G>\<F>_semantics' af_subformulas\<^sub>\<mu> by blast

lemma \<F>_af:
  "\<F> (af \<phi> (prefix i w)) (suffix i w) = \<F> \<phi> (suffix i w)"
  unfolding \<F>_semantics' af_subformulas\<^sub>\<mu> by blast

lemma \<F>\<G>_af:
  "\<F>\<G> (af \<phi> (prefix i w)) (suffix i w) = \<F>\<G> \<phi> (suffix i w)"
  unfolding \<F>\<G>_semantics' af_subformulas\<^sub>\<nu> by blast

lemma \<G>_af:
  "\<G> (af \<phi> (prefix i w)) (suffix i w) = \<G> \<phi> (suffix i w)"
  unfolding \<G>_semantics' af_subformulas\<^sub>\<nu> by blast



subsection \<open>Congruence\<close>

lemma af_letter_lang_congruent:
  "\<phi> \<sim>\<^sub>L \<psi> \<Longrightarrow> af_letter \<phi> \<nu> \<sim>\<^sub>L af_letter \<psi> \<nu>"
  unfolding ltl_lang_equiv_def
  using af_letter_build by blast

lemma af_lang_congruent:
  "\<phi> \<sim>\<^sub>L \<psi> \<Longrightarrow> af \<phi> w \<sim>\<^sub>L af \<psi> w"
  unfolding ltl_lang_equiv_def using af_ltl_continuation
  by (induction \<phi>) blast+



lemma af_letter_subst:
  "af_letter \<phi> \<nu> = subst \<phi> (\<lambda>\<psi>. Some (af_letter \<psi> \<nu>))"
  by (induction \<phi>) auto

lemma af_letter_prop_congruent:
  "\<phi> \<longrightarrow>\<^sub>P \<psi> \<Longrightarrow> af_letter \<phi> \<nu> \<longrightarrow>\<^sub>P af_letter \<psi> \<nu>"
  "\<phi> \<sim>\<^sub>P \<psi> \<Longrightarrow> af_letter \<phi> \<nu> \<sim>\<^sub>P af_letter \<psi> \<nu>"
  by (metis af_letter_subst subst_respects_ltl_prop_entailment)+

lemma af_prop_congruent:
  "\<phi> \<longrightarrow>\<^sub>P \<psi> \<Longrightarrow> af \<phi> w \<longrightarrow>\<^sub>P af \<psi> w"
  "\<phi> \<sim>\<^sub>P \<psi> \<Longrightarrow> af \<phi> w \<sim>\<^sub>P af \<psi> w"
  by (induction w arbitrary: \<phi> \<psi>) (insert af_letter_prop_congruent, fastforce+)


lemma af_letter_const_congruent:
  "\<phi> \<sim>\<^sub>C \<psi> \<Longrightarrow> af_letter \<phi> \<nu> \<sim>\<^sub>C af_letter \<psi> \<nu>"
  by (metis af_letter_subst subst_respects_ltl_const_entailment)

lemma af_const_congruent:
  "\<phi> \<sim>\<^sub>C \<psi> \<Longrightarrow> af \<phi> w \<sim>\<^sub>C af \<psi> w"
  by (induction w arbitrary: \<phi> \<psi>) (insert af_letter_const_congruent, fastforce+)


lemma af_letter_one_step_back:
  "{x. \<A> \<Turnstile>\<^sub>P af_letter x \<sigma>} \<Turnstile>\<^sub>P \<phi> \<longleftrightarrow> \<A> \<Turnstile>\<^sub>P af_letter \<phi> \<sigma>"
  by (induction \<phi>) simp_all


subsection \<open>Implications\<close>

lemma af_F_prefix_prop:
  "af (F\<^sub>n \<phi>) w \<longrightarrow>\<^sub>P af (F\<^sub>n \<phi>) (w' @ w)"
  by (induction w') (simp add: ltl_prop_implies_def af_decompose(1,2))+

lemma af_G_prefix_prop:
  "af (G\<^sub>n \<phi>) (w' @ w) \<longrightarrow>\<^sub>P af (G\<^sub>n \<phi>) w"
  by (induction w') (simp add: ltl_prop_implies_def af_decompose(1,2))+


lemma af_F_prefix_lang:
  "w \<Turnstile>\<^sub>n af (F\<^sub>n \<phi>) ys \<Longrightarrow> w \<Turnstile>\<^sub>n af (F\<^sub>n \<phi>) (xs @ ys)"
  using af_F_prefix_prop ltl_prop_implication_implies_ltl_implication by blast

lemma af_G_prefix_lang:
  "w \<Turnstile>\<^sub>n af (G\<^sub>n \<phi>) (xs @ ys) \<Longrightarrow> w \<Turnstile>\<^sub>n af (G\<^sub>n \<phi>) ys"
  using af_G_prefix_prop ltl_prop_implication_implies_ltl_implication by blast


lemma af_F_prefix_const_equiv_true:
  "af (F\<^sub>n \<phi>) w \<sim>\<^sub>C true\<^sub>n \<Longrightarrow> af (F\<^sub>n \<phi>) (w' @ w) \<sim>\<^sub>C true\<^sub>n"
  using af_F_prefix_prop ltl_const_equiv_implies_prop_equiv(1) ltl_prop_equiv_true_implies_true by blast

lemma af_G_prefix_const_equiv_false:
  "af (G\<^sub>n \<phi>) w \<sim>\<^sub>C false\<^sub>n \<Longrightarrow> af (G\<^sub>n \<phi>) (w' @ w) \<sim>\<^sub>C false\<^sub>n"
  using af_G_prefix_prop ltl_const_equiv_implies_prop_equiv(2) ltl_prop_equiv_false_implied_by_false by blast


lemma af_F_prefix_lang_equiv_true:
  "af (F\<^sub>n \<phi>) w \<sim>\<^sub>L true\<^sub>n \<Longrightarrow> af (F\<^sub>n \<phi>) (w' @ w) \<sim>\<^sub>L true\<^sub>n"
  unfolding ltl_lang_equiv_def
  using af_F_prefix_lang by fastforce

lemma af_G_prefix_lang_equiv_false:
  "af (G\<^sub>n \<phi>) w \<sim>\<^sub>L false\<^sub>n \<Longrightarrow> af (G\<^sub>n \<phi>) (w' @ w) \<sim>\<^sub>L false\<^sub>n"
  unfolding ltl_lang_equiv_def
  using af_G_prefix_lang by fastforce



locale af_congruent = ltl_equivalence +
  assumes
    af_letter_congruent: "\<phi> \<sim> \<psi> \<Longrightarrow> af_letter \<phi> \<nu> \<sim> af_letter \<psi> \<nu>"
begin

lemma af_congruentness:
  "\<phi> \<sim> \<psi> \<Longrightarrow> af \<phi> xs \<sim> af \<psi> xs"
  by (induction xs arbitrary: \<phi> \<psi>) (insert af_letter_congruent, fastforce+)

lemma af_append_congruent:
  "af \<phi> w \<sim> af \<psi> w \<Longrightarrow> af \<phi> (w @ w') \<sim> af \<psi> (w @ w')"
  by (simp add: af_congruentness)

lemma af_append_true:
  "af \<phi> w \<sim> true\<^sub>n \<Longrightarrow> af \<phi> (w @ w') \<sim> true\<^sub>n"
  using af_congruentness by fastforce

lemma af_append_false:
  "af \<phi> w \<sim> false\<^sub>n \<Longrightarrow> af \<phi> (w @ w') \<sim> false\<^sub>n"
  using af_congruentness by fastforce

lemma prefix_append_subsequence:
  "i \<le> j \<Longrightarrow> (prefix i w) @ (w [i \<rightarrow> j]) = prefix j w"
  by (metis le_add_diff_inverse subsequence_append)

lemma af_prefix_congruent:
  "i \<le> j \<Longrightarrow> af \<phi> (prefix i w) \<sim> af \<psi> (prefix i w) \<Longrightarrow> af \<phi> (prefix j w) \<sim> af \<psi> (prefix j w)"
  by (metis af_congruentness foldl_append prefix_append_subsequence)+

lemma af_prefix_true:
  "i \<le> j \<Longrightarrow> af \<phi> (prefix i w) \<sim> true\<^sub>n \<Longrightarrow> af \<phi> (prefix j w) \<sim> true\<^sub>n"
  by (metis af_append_true prefix_append_subsequence)

lemma af_prefix_false:
  "i \<le> j \<Longrightarrow> af \<phi> (prefix i w) \<sim> false\<^sub>n \<Longrightarrow> af \<phi> (prefix j w) \<sim> false\<^sub>n"
  by (metis af_append_false prefix_append_subsequence)

end




interpretation lang_af_congruent: af_congruent "(\<sim>\<^sub>L)"
  by unfold_locales (rule af_letter_lang_congruent)

interpretation prop_af_congruent: af_congruent "(\<sim>\<^sub>P)"
  by unfold_locales (rule af_letter_prop_congruent)

interpretation const_af_congruent: af_congruent "(\<sim>\<^sub>C)"
  by unfold_locales (rule af_letter_const_congruent)



subsection \<open>After in @{term \<mu>LTL} and @{term \<nu>LTL}\<close>

lemma valid_prefix_implies_ltl:
  "af \<phi> (prefix i w) \<sim>\<^sub>L true\<^sub>n \<Longrightarrow> w \<Turnstile>\<^sub>n \<phi>"
proof -
  assume "af \<phi> (prefix i w) \<sim>\<^sub>L true\<^sub>n"

  then have "suffix i w \<Turnstile>\<^sub>n af \<phi> (prefix i w)"
    unfolding ltl_lang_equiv_def using semantics_ltln.simps(1) by blast

  then show "w \<Turnstile>\<^sub>n \<phi>"
    using af_ltl_continuation by force
qed

lemma ltl_implies_satisfiable_prefix:
  "w \<Turnstile>\<^sub>n \<phi> \<Longrightarrow> \<not> (af \<phi> (prefix i w) \<sim>\<^sub>L false\<^sub>n)"
proof -
  assume "w \<Turnstile>\<^sub>n \<phi>"

  then have "suffix i w \<Turnstile>\<^sub>n af \<phi> (prefix i w)"
    using af_ltl_continuation by fastforce

  then show "\<not> (af \<phi> (prefix i w) \<sim>\<^sub>L false\<^sub>n)"
    unfolding ltl_lang_equiv_def using semantics_ltln.simps(2) by blast
qed

lemma \<mu>LTL_implies_valid_prefix:
  "\<phi> \<in> \<mu>LTL \<Longrightarrow> w \<Turnstile>\<^sub>n \<phi> \<Longrightarrow> \<exists>i. af \<phi> (prefix i w) \<sim>\<^sub>C true\<^sub>n"
proof (induction \<phi> arbitrary: w)
  case True_ltln
  then show ?case
    using ltl_const_equiv_equivp equivp_reflp by fastforce
next
  case (Prop_ltln x)
  then show ?case
    by (metis af_letter.simps(3) foldl_Cons foldl_Nil ltl_const_equiv_equivp equivp_reflp semantics_ltln.simps(3) subsequence_singleton)
next
  case (Nprop_ltln x)
  then show ?case
    by (metis af_letter.simps(4) foldl_Cons foldl_Nil ltl_const_equiv_equivp equivp_reflp semantics_ltln.simps(4) subsequence_singleton)
next
  case (And_ltln \<phi>1 \<phi>2)

  then obtain i1 i2 where "af \<phi>1 (prefix i1 w) \<sim>\<^sub>C true\<^sub>n" and "af \<phi>2 (prefix i2 w) \<sim>\<^sub>C true\<^sub>n"
    by fastforce

  then have "af \<phi>1 (prefix (i1 + i2) w) \<sim>\<^sub>C true\<^sub>n" and "af \<phi>2 (prefix (i2 + i1) w) \<sim>\<^sub>C true\<^sub>n"
    using const_af_congruent.af_prefix_true le_add1 by blast+

  then have "af (\<phi>1 and\<^sub>n \<phi>2) (prefix (i1 + i2) w) \<sim>\<^sub>C true\<^sub>n"
    unfolding af_decompose by (simp add: add.commute)

  then show ?case
    by blast
next
  case (Or_ltln \<phi>1 \<phi>2)

  then obtain i where "af \<phi>1 (prefix i w) \<sim>\<^sub>C true\<^sub>n \<or> af \<phi>2 (prefix i w) \<sim>\<^sub>C true\<^sub>n"
    by auto

  then show ?case
    unfolding af_decompose by auto
next
  case (Next_ltln \<phi>)

  then obtain i where "af \<phi> (prefix i (suffix 1 w)) \<sim>\<^sub>C true\<^sub>n"
    by fastforce

  then show ?case
    by (metis (no_types, lifting) One_nat_def add.right_neutral af_simps(3) foldl_Nil foldl_append subsequence_append subsequence_shift subsequence_singleton)
next
  case (Until_ltln \<phi>1 \<phi>2)

  then obtain k where "suffix k w \<Turnstile>\<^sub>n \<phi>2" and "\<forall>j<k. suffix j w \<Turnstile>\<^sub>n \<phi>1"
    by fastforce

  then show ?case
  proof (induction k arbitrary: w)
    case 0

    then obtain i where "af \<phi>2 (prefix i w) \<sim>\<^sub>C true\<^sub>n"
      using Until_ltln by fastforce

    then have "af \<phi>2 (prefix (Suc i) w) \<sim>\<^sub>C true\<^sub>n"
      using const_af_congruent.af_prefix_true le_SucI by blast

    then have "af (\<phi>1 U\<^sub>n \<phi>2) (prefix (Suc i) w) \<sim>\<^sub>C true\<^sub>n"
      unfolding af_subsequence_U by simp

    then show ?case
      by blast
  next
    case (Suc k)

    then have "suffix k (suffix 1 w) \<Turnstile>\<^sub>n \<phi>2" and "\<forall>j<k. suffix j (suffix 1 w) \<Turnstile>\<^sub>n \<phi>1"
      by (simp add: Suc.prems)+

    then obtain i where i_def: "af (\<phi>1 U\<^sub>n \<phi>2) (prefix i (suffix 1 w)) \<sim>\<^sub>C true\<^sub>n"
      using Suc.IH by blast

    obtain j where "af \<phi>1 (prefix j w) \<sim>\<^sub>C true\<^sub>n"
      using Until_ltln Suc by fastforce

    then have "af \<phi>1 (prefix (Suc (j + i)) w) \<sim>\<^sub>C true\<^sub>n"
      using const_af_congruent.af_prefix_true le_SucI le_add1 by blast

    moreover

    from i_def have "af (\<phi>1 U\<^sub>n \<phi>2) (w [1 \<rightarrow> Suc (j + i)]) \<sim>\<^sub>C true\<^sub>n"
      by (metis One_nat_def const_af_congruent.af_prefix_true le_add2 plus_1_eq_Suc subsequence_shift)

    ultimately

    have "af (\<phi>1 U\<^sub>n \<phi>2) (prefix (Suc (j + i)) w) \<sim>\<^sub>C true\<^sub>n"
      unfolding af_subsequence_U by simp

    then show ?case
      by blast
  qed
next
  case (StrongRelease_ltln \<phi>1 \<phi>2)

  then obtain k where "suffix k w \<Turnstile>\<^sub>n \<phi>1" and "\<forall>j\<le>k. suffix j w \<Turnstile>\<^sub>n \<phi>2"
    by fastforce

  then show ?case
  proof (induction k arbitrary: w)
    case 0

    then obtain i1 i2 where "af \<phi>1 (prefix i1 w) \<sim>\<^sub>C true\<^sub>n" and "af \<phi>2 (prefix i2 w) \<sim>\<^sub>C true\<^sub>n"
      using StrongRelease_ltln by fastforce

    then have "af \<phi>1 (prefix (Suc (i1 + i2)) w) \<sim>\<^sub>C true\<^sub>n" and "af \<phi>2 (prefix (Suc (i2 + i1)) w) \<sim>\<^sub>C true\<^sub>n"
      using const_af_congruent.af_prefix_true le_SucI le_add1 by blast+

    then have "af (\<phi>1 M\<^sub>n \<phi>2) (prefix (Suc (i1 + i2)) w) \<sim>\<^sub>C true\<^sub>n"
      unfolding af_subsequence_M by (simp add: add.commute)

    then show ?case
      by blast
  next
    case (Suc k)

    then have "suffix k (suffix 1 w) \<Turnstile>\<^sub>n \<phi>1" and "\<forall>j\<le>k. suffix j (suffix 1 w) \<Turnstile>\<^sub>n \<phi>2"
      by (simp add: Suc.prems)+

    then obtain i where i_def: "af (\<phi>1 M\<^sub>n \<phi>2) (prefix i (suffix 1 w)) \<sim>\<^sub>C true\<^sub>n"
      using Suc.IH by blast

    obtain j where "af \<phi>2 (prefix j w) \<sim>\<^sub>C true\<^sub>n"
      using StrongRelease_ltln Suc by fastforce

    then have "af \<phi>2 (prefix (Suc (j + i)) w) \<sim>\<^sub>C true\<^sub>n"
      using const_af_congruent.af_prefix_true le_SucI le_add1 by blast

    moreover

    from i_def have "af (\<phi>1 M\<^sub>n \<phi>2) (w [1 \<rightarrow> Suc (j + i)]) \<sim>\<^sub>C true\<^sub>n"
      by (metis One_nat_def const_af_congruent.af_prefix_true le_add2 plus_1_eq_Suc subsequence_shift)

    ultimately

    have "af (\<phi>1 M\<^sub>n \<phi>2) (prefix (Suc (j + i)) w) \<sim>\<^sub>C true\<^sub>n"
      unfolding af_subsequence_M by simp

    then show ?case
      by blast
  qed
qed force+

lemma satisfiable_prefix_implies_\<nu>LTL:
  "\<phi> \<in> \<nu>LTL \<Longrightarrow> \<nexists>i. af \<phi> (prefix i w) \<sim>\<^sub>C false\<^sub>n \<Longrightarrow> w \<Turnstile>\<^sub>n \<phi>"
proof (erule contrapos_np, induction \<phi> arbitrary: w)
  case False_ltln
  then show ?case
    using ltl_const_equiv_equivp equivp_reflp by fastforce
next
  case (Prop_ltln x)
  then show ?case
    by (metis af_letter.simps(3) foldl_Cons foldl_Nil ltl_const_equiv_equivp equivp_reflp semantics_ltln.simps(3) subsequence_singleton)
next
  case (Nprop_ltln x)
  then show ?case
    by (metis af_letter.simps(4) foldl_Cons foldl_Nil ltl_const_equiv_equivp equivp_reflp semantics_ltln.simps(4) subsequence_singleton)
next
  case (And_ltln \<phi>1 \<phi>2)

  then obtain i where "af \<phi>1 (prefix i w) \<sim>\<^sub>C false\<^sub>n \<or> af \<phi>2 (prefix i w) \<sim>\<^sub>C false\<^sub>n"
    by auto

  then show ?case
    unfolding af_decompose by auto
next
  case (Or_ltln \<phi>1 \<phi>2)

  then obtain i1 i2 where "af \<phi>1 (prefix i1 w) \<sim>\<^sub>C false\<^sub>n" and "af \<phi>2 (prefix i2 w) \<sim>\<^sub>C false\<^sub>n"
    by fastforce

  then have "af \<phi>1 (prefix (i1 + i2) w) \<sim>\<^sub>C false\<^sub>n" and "af \<phi>2 (prefix (i2 + i1) w) \<sim>\<^sub>C false\<^sub>n"
    using const_af_congruent.af_prefix_false le_add1 by blast+

  then have "af (\<phi>1 or\<^sub>n \<phi>2) (prefix (i1 + i2) w) \<sim>\<^sub>C false\<^sub>n"
    unfolding af_decompose by (simp add: add.commute)

  then show ?case
    by blast
next
  case (Next_ltln \<phi>)

  then obtain i where "af \<phi> (prefix i (suffix 1 w)) \<sim>\<^sub>C false\<^sub>n"
    by fastforce

  then show ?case
    by (metis (no_types, lifting) One_nat_def add.right_neutral af_simps(3) foldl_Nil foldl_append subsequence_append subsequence_shift subsequence_singleton)
next
  case (Release_ltln \<phi>1 \<phi>2)

  then obtain k where "\<not> suffix k w \<Turnstile>\<^sub>n \<phi>2" and "\<forall>j<k. \<not> suffix j w \<Turnstile>\<^sub>n \<phi>1"
    by fastforce

  then show ?case
  proof (induction k arbitrary: w)
    case 0

    then obtain i where "af \<phi>2 (prefix i w) \<sim>\<^sub>C false\<^sub>n"
      using Release_ltln by fastforce

    then have "af \<phi>2 (prefix (Suc i) w) \<sim>\<^sub>C false\<^sub>n"
      using const_af_congruent.af_prefix_false le_SucI by blast

    then have "af (\<phi>1 R\<^sub>n \<phi>2) (prefix (Suc i) w) \<sim>\<^sub>C false\<^sub>n"
      unfolding af_subsequence_R by simp

    then show ?case
      by blast
  next
    case (Suc k)

    then have "\<not> suffix k (suffix 1 w) \<Turnstile>\<^sub>n \<phi>2" and "\<forall>j<k. \<not> suffix j (suffix 1 w) \<Turnstile>\<^sub>n \<phi>1"
      by (simp add: Suc.prems)+

    then obtain i where i_def: "af (\<phi>1 R\<^sub>n \<phi>2) (prefix i (suffix 1 w)) \<sim>\<^sub>C false\<^sub>n"
      using Suc.IH by blast

    obtain j where "af \<phi>1 (prefix j w) \<sim>\<^sub>C false\<^sub>n"
      using Release_ltln Suc by fastforce

    then have "af \<phi>1 (prefix (Suc (j + i)) w) \<sim>\<^sub>C false\<^sub>n"
      using const_af_congruent.af_prefix_false le_SucI le_add1 by blast

    moreover

    from i_def have "af (\<phi>1 R\<^sub>n \<phi>2) (w [1 \<rightarrow> Suc (j + i)]) \<sim>\<^sub>C false\<^sub>n"
      by (metis One_nat_def const_af_congruent.af_prefix_false le_add2 plus_1_eq_Suc subsequence_shift)

    ultimately

    have "af (\<phi>1 R\<^sub>n \<phi>2) (prefix (Suc (j + i)) w) \<sim>\<^sub>C false\<^sub>n"
      unfolding af_subsequence_R by auto

    then show ?case
      by blast
  qed
next
  case (WeakUntil_ltln \<phi>1 \<phi>2)

  then obtain k where "\<not> suffix k w \<Turnstile>\<^sub>n \<phi>1" and "\<forall>j\<le>k. \<not> suffix j w \<Turnstile>\<^sub>n \<phi>2"
    by fastforce

  then show ?case
  proof (induction k arbitrary: w)
    case 0

    then obtain i1 i2 where "af \<phi>1 (prefix i1 w) \<sim>\<^sub>C false\<^sub>n" and "af \<phi>2 (prefix i2 w) \<sim>\<^sub>C false\<^sub>n"
      using WeakUntil_ltln by fastforce

    then have "af \<phi>1 (prefix (Suc (i1 + i2)) w) \<sim>\<^sub>C false\<^sub>n" and "af \<phi>2 (prefix (Suc (i2 + i1)) w) \<sim>\<^sub>C false\<^sub>n"
      using const_af_congruent.af_prefix_false le_SucI le_add1 by blast+

    then have "af (\<phi>1 W\<^sub>n \<phi>2) (prefix (Suc (i1 + i2)) w) \<sim>\<^sub>C false\<^sub>n"
      unfolding af_subsequence_W by (simp add: add.commute)

    then show ?case
      by blast
  next
    case (Suc k)

    then have "\<not> suffix k (suffix 1 w) \<Turnstile>\<^sub>n \<phi>1" and "\<forall>j\<le>k. \<not> suffix j (suffix 1 w) \<Turnstile>\<^sub>n \<phi>2"
      by (simp add: Suc.prems)+

    then obtain i where i_def: "af (\<phi>1 W\<^sub>n \<phi>2) (prefix i (suffix 1 w)) \<sim>\<^sub>C false\<^sub>n"
      using Suc.IH by blast

    obtain j where "af \<phi>2 (prefix j w) \<sim>\<^sub>C false\<^sub>n"
      using WeakUntil_ltln Suc by fastforce

    then have "af \<phi>2 (prefix (Suc (j + i)) w) \<sim>\<^sub>C false\<^sub>n"
      using const_af_congruent.af_prefix_false le_SucI le_add1 by blast

    moreover

    from i_def have "af (\<phi>1 W\<^sub>n \<phi>2) (w [1 \<rightarrow> Suc (j + i)]) \<sim>\<^sub>C false\<^sub>n"
      by (metis One_nat_def const_af_congruent.af_prefix_false le_add2 plus_1_eq_Suc subsequence_shift)

    ultimately

    have "af (\<phi>1 W\<^sub>n \<phi>2) (prefix (Suc (j + i)) w) \<sim>\<^sub>C false\<^sub>n"
      unfolding af_subsequence_W by simp

    then show ?case
      by blast
  qed
qed force+


context ltl_equivalence
begin

lemma valid_prefix_implies_ltl:
  "af \<phi> (prefix i w) \<sim> true\<^sub>n \<Longrightarrow> w \<Turnstile>\<^sub>n \<phi>"
  using valid_prefix_implies_ltl eq_implies_lang by blast

lemma ltl_implies_satisfiable_prefix:
  "w \<Turnstile>\<^sub>n \<phi> \<Longrightarrow> \<not> (af \<phi> (prefix i w) \<sim> false\<^sub>n)"
  using ltl_implies_satisfiable_prefix eq_implies_lang by blast


lemma \<mu>LTL_implies_valid_prefix:
  "\<phi> \<in> \<mu>LTL \<Longrightarrow> w \<Turnstile>\<^sub>n \<phi> \<Longrightarrow> \<exists>i. af \<phi> (prefix i w) \<sim> true\<^sub>n"
  using \<mu>LTL_implies_valid_prefix const_implies_eq by blast

lemma satisfiable_prefix_implies_\<nu>LTL:
  "\<phi> \<in> \<nu>LTL \<Longrightarrow> \<nexists>i. af \<phi> (prefix i w) \<sim> false\<^sub>n \<Longrightarrow> w \<Turnstile>\<^sub>n \<phi>"
  using satisfiable_prefix_implies_\<nu>LTL const_implies_eq by blast


lemma af_\<mu>LTL:
  "\<phi> \<in> \<mu>LTL \<Longrightarrow> w \<Turnstile>\<^sub>n \<phi> \<longleftrightarrow> (\<exists>i. af \<phi> (prefix i w) \<sim> true\<^sub>n)"
  using valid_prefix_implies_ltl \<mu>LTL_implies_valid_prefix by blast

lemma af_\<nu>LTL:
  "\<phi> \<in> \<nu>LTL \<Longrightarrow> w \<Turnstile>\<^sub>n \<phi> \<longleftrightarrow> (\<forall>i. \<not> (af \<phi> (prefix i w) \<sim> false\<^sub>n))"
  using ltl_implies_satisfiable_prefix satisfiable_prefix_implies_\<nu>LTL by blast


lemma af_\<mu>LTL_GF:
  "\<phi> \<in> \<mu>LTL \<Longrightarrow> w \<Turnstile>\<^sub>n G\<^sub>n (F\<^sub>n \<phi>) \<longleftrightarrow> (\<forall>i. \<exists>j. af (F\<^sub>n \<phi>) (w[i \<rightarrow> j]) \<sim> true\<^sub>n)"
proof -
  assume "\<phi> \<in> \<mu>LTL"

  then have "F\<^sub>n \<phi> \<in> \<mu>LTL"
    by simp

  have "w \<Turnstile>\<^sub>n G\<^sub>n (F\<^sub>n \<phi>) \<longleftrightarrow> (\<forall>i. suffix i w \<Turnstile>\<^sub>n F\<^sub>n \<phi>)"
    by simp
  also have "\<dots> \<longleftrightarrow> (\<forall>i. \<exists>j. af (F\<^sub>n \<phi>) (prefix j (suffix i w)) \<sim> true\<^sub>n)"
    using af_\<mu>LTL[OF `F\<^sub>n \<phi> \<in> \<mu>LTL`] by blast
  also have "\<dots> \<longleftrightarrow> (\<forall>i. \<exists>j. af (F\<^sub>n \<phi>) (prefix (j - i) (suffix i w)) \<sim> true\<^sub>n)"
    by (metis diff_add_inverse)
  also have "\<dots> \<longleftrightarrow> (\<forall>i. \<exists>j. af (F\<^sub>n \<phi>) (w[i \<rightarrow> j]) \<sim> true\<^sub>n)"
    unfolding subsequence_prefix_suffix ..
  finally show ?thesis
    by blast
qed

lemma af_\<nu>LTL_FG:
  "\<phi> \<in> \<nu>LTL \<Longrightarrow> w \<Turnstile>\<^sub>n F\<^sub>n (G\<^sub>n \<phi>) \<longleftrightarrow> (\<exists>i. \<forall>j. \<not> (af (G\<^sub>n \<phi>) (w[i \<rightarrow> j]) \<sim> false\<^sub>n))"
proof -
  assume "\<phi> \<in> \<nu>LTL"

  then have "G\<^sub>n \<phi> \<in> \<nu>LTL"
    by simp

  have "w \<Turnstile>\<^sub>n F\<^sub>n (G\<^sub>n \<phi>) \<longleftrightarrow> (\<exists>i. suffix i w \<Turnstile>\<^sub>n G\<^sub>n \<phi>)"
    by force
  also have "\<dots> \<longleftrightarrow> (\<exists>i. \<forall>j. \<not> (af (G\<^sub>n \<phi>) (prefix j (suffix i w)) \<sim> false\<^sub>n))"
    using af_\<nu>LTL[OF `G\<^sub>n \<phi> \<in> \<nu>LTL`] by blast
  also have "\<dots> \<longleftrightarrow> (\<exists>i. \<forall>j. \<not> (af (G\<^sub>n \<phi>) (prefix (j - i) (suffix i w)) \<sim> false\<^sub>n))"
    by (metis diff_add_inverse)
  also have "\<dots> \<longleftrightarrow> (\<exists>i. \<forall>j. \<not> (af (G\<^sub>n \<phi>) (w[i \<rightarrow> j]) \<sim> false\<^sub>n))"
    unfolding subsequence_prefix_suffix ..
  finally show ?thesis
    by blast
qed

end

text \<open>Bring Propositional Equivalence into scope\<close>

interpretation af_congruent "(\<sim>\<^sub>P)"
  by unfold_locales (rule af_letter_prop_congruent)

end
