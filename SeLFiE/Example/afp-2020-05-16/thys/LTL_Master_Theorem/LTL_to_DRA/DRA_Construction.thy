(*
    Author:   Benedikt Seidl
    License:  BSD
*)

section \<open>Constructing DRAs for LTL Formulas\<close>

theory DRA_Construction
  imports
    Transition_Functions

    "../Quotient_Type"
    "../Omega_Words_Fun_Stream"

    "HOL-Library.Log_Nat"

    "../Logical_Characterization/Master_Theorem"
    "../Logical_Characterization/Restricted_Master_Theorem"

    Transition_Systems_and_Automata.DBA_Combine
    Transition_Systems_and_Automata.DCA_Combine
    Transition_Systems_and_Automata.DRA_Combine
begin

\<comment> \<open>We use prefix and suffix on infinite words.\<close>
hide_const Sublist.prefix Sublist.suffix

locale dra_construction = transition_functions eq normalise + quotient eq Rep Abs
  for
    eq :: "'a ltln \<Rightarrow> 'a ltln \<Rightarrow> bool" (infix "\<sim>" 75)
  and
    normalise :: "'a ltln \<Rightarrow> 'a ltln"
  and
    Rep :: "'ltlq \<Rightarrow> 'a ltln"
  and
    Abs :: "'a ltln \<Rightarrow> 'ltlq"
begin

subsection \<open>Lifting Setup\<close>

abbreviation true\<^sub>n_lifted :: "'ltlq" ("\<up>true\<^sub>n") where
  "\<up>true\<^sub>n \<equiv> Abs true\<^sub>n"

abbreviation false\<^sub>n_lifted :: "'ltlq" ("\<up>false\<^sub>n") where
  "\<up>false\<^sub>n \<equiv> Abs false\<^sub>n"

abbreviation af_letter_lifted :: "'a set \<Rightarrow> 'ltlq \<Rightarrow> 'ltlq" ("\<up>afletter") where
  "\<up>afletter \<nu> \<phi> \<equiv> Abs (af_letter (Rep \<phi>) \<nu>)"

abbreviation af_lifted :: "'ltlq \<Rightarrow> 'a set list \<Rightarrow> 'ltlq" ("\<up>af") where
  "\<up>af \<phi> w \<equiv> fold \<up>afletter w \<phi>"

abbreviation GF_advice_lifted :: "'ltlq \<Rightarrow> 'a ltln set \<Rightarrow> 'ltlq" ("_\<up>[_]\<^sub>\<nu>" [90,60] 89) where
  "\<phi>\<up>[X]\<^sub>\<nu> \<equiv> Abs ((Rep \<phi>)[X]\<^sub>\<nu>)"


lemma af_letter_lifted_semantics:
  "\<up>afletter \<nu> (Abs \<phi>) = Abs (af_letter \<phi> \<nu>)"
  by (metis Rep_Abs_eq af_letter_congruent Abs_eq)

lemma af_lifted_semantics:
  "\<up>af (Abs \<phi>) w = Abs (af \<phi> w)"
  by (induction w rule: rev_induct) (auto simp: Abs_eq, insert Rep_Abs_eq af_letter_congruent eq_sym, blast)

lemma af_lifted_range:
  "range (\<up>af (Abs \<phi>)) \<subseteq> {Abs \<psi> | \<psi>. nested_prop_atoms \<psi> \<subseteq> nested_prop_atoms \<phi>}"
  using af_lifted_semantics af_nested_prop_atoms by blast


definition af_letter\<^sub>F_lifted :: "'a ltln \<Rightarrow> 'a set \<Rightarrow> 'ltlq \<Rightarrow> 'ltlq" ("\<up>afletter\<^sub>F")
where
  "\<up>afletter\<^sub>F \<phi> \<nu> \<psi> \<equiv> Abs (af_letter\<^sub>F \<phi> (Rep \<psi>) \<nu>)"

definition af_letter\<^sub>G_lifted :: "'a ltln \<Rightarrow> 'a set \<Rightarrow> 'ltlq \<Rightarrow> 'ltlq" ("\<up>afletter\<^sub>G")
where
  "\<up>afletter\<^sub>G \<phi> \<nu> \<psi> \<equiv> Abs (af_letter\<^sub>G \<phi> (Rep \<psi>) \<nu>)"

lemma af_letter\<^sub>F_lifted_semantics:
  "\<up>afletter\<^sub>F \<phi> \<nu> (Abs \<psi>) = Abs (af_letter\<^sub>F \<phi> \<psi> \<nu>)"
  by (metis af_letter\<^sub>F_lifted_def Rep_inverse af_letter\<^sub>F_def af_letter_congruent Abs_eq)

lemma af_letter\<^sub>G_lifted_semantics:
  "\<up>afletter\<^sub>G \<phi> \<nu> (Abs \<psi>) = Abs (af_letter\<^sub>G \<phi> \<psi> \<nu>)"
  by (metis af_letter\<^sub>G_lifted_def Rep_inverse af_letter\<^sub>G_def af_letter_congruent Abs_eq)

abbreviation af\<^sub>F_lifted :: "'a ltln \<Rightarrow> 'ltlq \<Rightarrow> 'a set list \<Rightarrow> 'ltlq" ("\<up>af\<^sub>F")
where
  "\<up>af\<^sub>F \<phi> \<psi> w \<equiv> fold (\<up>afletter\<^sub>F \<phi>) w \<psi>"

abbreviation af\<^sub>G_lifted :: "'a ltln \<Rightarrow> 'ltlq \<Rightarrow> 'a set list \<Rightarrow> 'ltlq" ("\<up>af\<^sub>G")
where
  "\<up>af\<^sub>G \<phi> \<psi> w \<equiv> fold (\<up>afletter\<^sub>G \<phi>) w \<psi>"

lemma af\<^sub>F_lifted_semantics:
  "\<up>af\<^sub>F \<phi> (Abs \<psi>) w = Abs (af\<^sub>F \<phi> \<psi> w)"
  by (induction w rule: rev_induct) (auto simp: af_letter\<^sub>F_lifted_semantics)

lemma af\<^sub>G_lifted_semantics:
  "\<up>af\<^sub>G \<phi> (Abs \<psi>) w = Abs (af\<^sub>G \<phi> \<psi> w)"
  by (induction w rule: rev_induct) (auto simp: af_letter\<^sub>G_lifted_semantics)


definition af_letter\<^sub>\<nu>_lifted :: "'a ltln set \<Rightarrow> 'a set \<Rightarrow> 'ltlq \<times> 'ltlq \<Rightarrow> 'ltlq \<times> 'ltlq" ("\<up>afletter\<^sub>\<nu>")
where
  "\<up>afletter\<^sub>\<nu> X \<nu> p \<equiv>
    (Abs (fst (af_letter\<^sub>\<nu> X (Rep (fst p), Rep (snd p)) \<nu>)),
     Abs (snd (af_letter\<^sub>\<nu> X (Rep (fst p), Rep (snd p)) \<nu>)))"

abbreviation af\<^sub>\<nu>_lifted :: "'a ltln set \<Rightarrow> 'ltlq \<times> 'ltlq \<Rightarrow> 'a set list \<Rightarrow> 'ltlq \<times> 'ltlq" ("\<up>af\<^sub>\<nu>")
where
  "\<up>af\<^sub>\<nu> X p w \<equiv> fold (\<up>afletter\<^sub>\<nu> X) w p"

lemma af_letter\<^sub>\<nu>_lifted_semantics:
  "\<up>afletter\<^sub>\<nu> X \<nu> (Abs x, Abs y) = (Abs (fst (af_letter\<^sub>\<nu> X (x, y) \<nu>)), Abs (snd (af_letter\<^sub>\<nu> X (x, y) \<nu>)))"
  by (simp add: af_letter\<^sub>\<nu>_def af_letter\<^sub>\<nu>_lifted_def) (insert GF_advice_congruent Rep_Abs_eq Rep_inverse af_letter_lifted_semantics eq_trans Abs_eq, blast)

lemma af\<^sub>\<nu>_lifted_semantics:
  "\<up>af\<^sub>\<nu> X (Abs \<xi>, Abs \<zeta>) w = (Abs (fst (af\<^sub>\<nu> X (\<xi>, \<zeta>) w)), Abs (snd (af\<^sub>\<nu> X (\<xi>, \<zeta>) w)))"
  apply (induction w rule: rev_induct) 
   apply (auto simp: af_letter\<^sub>\<nu>_lifted_def af_letter\<^sub>\<nu>_lifted_semantics af_letter_lifted_semantics)
  by (metis (no_types, hide_lams) af_letter\<^sub>\<nu>_lifted_def af\<^sub>\<nu>_fst af_letter\<^sub>\<nu>_lifted_semantics eq_fst_iff prod.sel(2))



subsection \<open>Büchi automata for basic languages\<close>

definition \<AA>\<^sub>\<mu> :: "'a ltln \<Rightarrow> ('a set, 'ltlq) dba" where
  "\<AA>\<^sub>\<mu> \<phi> = dba UNIV (Abs \<phi>) \<up>afletter (\<lambda>\<psi>. \<psi> = \<up>true\<^sub>n)"

definition \<AA>\<^sub>\<mu>_GF :: "'a ltln \<Rightarrow> ('a set, 'ltlq) dba" where
  "\<AA>\<^sub>\<mu>_GF \<phi> = dba UNIV (Abs (F\<^sub>n \<phi>)) (\<up>afletter\<^sub>F \<phi>) (\<lambda>\<psi>. \<psi> = \<up>true\<^sub>n)"

definition \<AA>\<^sub>\<nu> :: "'a ltln \<Rightarrow> ('a set, 'ltlq) dca" where
  "\<AA>\<^sub>\<nu> \<phi> = dca UNIV (Abs \<phi>) \<up>afletter (\<lambda>\<psi>. \<psi> = \<up>false\<^sub>n)"

definition \<AA>\<^sub>\<nu>_FG :: "'a ltln \<Rightarrow> ('a set, 'ltlq) dca" where
  "\<AA>\<^sub>\<nu>_FG \<phi> = dca UNIV (Abs (G\<^sub>n \<phi>)) (\<up>afletter\<^sub>G \<phi>) (\<lambda>\<psi>. \<psi> = \<up>false\<^sub>n)"


lemma dba_run:
  "DBA.run (dba UNIV p \<delta> \<alpha>) (to_stream w) p" unfolding dba.run_alt_def by simp

lemma dca_run:
  "DCA.run (dca UNIV p \<delta> \<alpha>) (to_stream w) p" unfolding dca.run_alt_def by simp


lemma \<AA>\<^sub>\<mu>_language:
  "\<phi> \<in> \<mu>LTL \<Longrightarrow> to_stream w \<in> DBA.language (\<AA>\<^sub>\<mu> \<phi>) \<longleftrightarrow> w \<Turnstile>\<^sub>n \<phi>"
proof -
  assume "\<phi> \<in> \<mu>LTL"

  then have "w \<Turnstile>\<^sub>n \<phi> \<longleftrightarrow> (\<forall>n. \<exists>k\<ge>n. af \<phi> (w[0 \<rightarrow> k]) \<sim> true\<^sub>n)"
    by (meson af_\<mu>LTL af_prefix_true le_cases)

  also have "\<dots> \<longleftrightarrow> (\<forall>n. \<exists>k\<ge>n. af \<phi> (w[0 \<rightarrow> Suc k]) \<sim> true\<^sub>n)"
    by (meson af_prefix_true le_SucI order_refl)

  also have "\<dots> \<longleftrightarrow> infs (\<lambda>\<psi>. \<psi> = \<up>true\<^sub>n) (DBA.trace (\<AA>\<^sub>\<mu> \<phi>) (to_stream w) (Abs \<phi>))"
    by (simp add: infs_snth \<AA>\<^sub>\<mu>_def DBA.transition_def af_lifted_semantics Abs_eq[symmetric] af_letter_lifted_semantics)

  also have "\<dots> \<longleftrightarrow> to_stream w \<in> DBA.language (\<AA>\<^sub>\<mu> \<phi>)"
    unfolding \<AA>\<^sub>\<mu>_def dba.initial_def dba.accepting_def by (auto simp: dba_run)

  finally show ?thesis
    by simp
qed

lemma \<AA>\<^sub>\<mu>_GF_language:
  "\<phi> \<in> \<mu>LTL \<Longrightarrow> to_stream w \<in> DBA.language (\<AA>\<^sub>\<mu>_GF \<phi>) \<longleftrightarrow> w \<Turnstile>\<^sub>n G\<^sub>n (F\<^sub>n \<phi>)"
proof -
  assume "\<phi> \<in> \<mu>LTL"

  then have "w \<Turnstile>\<^sub>n G\<^sub>n (F\<^sub>n \<phi>) \<longleftrightarrow> (\<forall>n. \<exists>k. af (F\<^sub>n \<phi>) (w[n \<rightarrow> k]) \<sim>\<^sub>L true\<^sub>n)"
    using ltl_lang_equivalence.af_\<mu>LTL_GF by blast

  also have "\<dots> \<longleftrightarrow> (\<forall>n. \<exists>k>n. af\<^sub>F \<phi> (F\<^sub>n \<phi>) (w[0 \<rightarrow> k]) \<sim> true\<^sub>n)"
    using af\<^sub>F_semantics_ltr af\<^sub>F_semantics_rtl
    using \<open>\<phi> \<in> \<mu>LTL\<close> af_\<mu>LTL_GF calculation by blast

  also have "\<dots> \<longleftrightarrow> (\<forall>n. \<exists>k\<ge>n. af\<^sub>F \<phi> (F\<^sub>n \<phi>) (w[0 \<rightarrow> Suc k]) \<sim> true\<^sub>n)"
    by (metis less_Suc_eq_le less_imp_Suc_add)

  also have "\<dots> \<longleftrightarrow> infs (\<lambda>\<psi>. \<psi> = \<up>true\<^sub>n) (DBA.trace (\<AA>\<^sub>\<mu>_GF \<phi>) (to_stream w) (Abs (F\<^sub>n \<phi>)))"
    by (simp add: infs_snth \<AA>\<^sub>\<mu>_GF_def DBA.transition_def af\<^sub>F_lifted_semantics Abs_eq[symmetric] af_letter\<^sub>F_lifted_semantics)

  also have "\<dots> \<longleftrightarrow> to_stream w \<in> DBA.language (\<AA>\<^sub>\<mu>_GF \<phi>)"
    unfolding \<AA>\<^sub>\<mu>_GF_def dba.initial_def dba.accepting_def by (auto simp: dba_run)

  finally show ?thesis
    by simp
qed

lemma \<AA>\<^sub>\<nu>_language:
  "\<phi> \<in> \<nu>LTL \<Longrightarrow> to_stream w \<in> DCA.language (\<AA>\<^sub>\<nu> \<phi>) \<longleftrightarrow> w \<Turnstile>\<^sub>n \<phi>"
proof -
  assume "\<phi> \<in> \<nu>LTL"

  then have "w \<Turnstile>\<^sub>n \<phi> \<longleftrightarrow> (\<exists>n. \<forall>k\<ge>n. \<not> af \<phi> (w[0 \<rightarrow> k]) \<sim> false\<^sub>n)"
    by (meson af_\<nu>LTL af_prefix_false le_cases order_refl)

  also have "\<dots> \<longleftrightarrow> (\<exists>n. \<forall>k\<ge>n. \<not> af \<phi> (w[0 \<rightarrow> Suc k]) \<sim> false\<^sub>n)"
    by (meson af_prefix_false le_SucI order_refl)

  also have "\<dots> \<longleftrightarrow> fins (\<lambda>\<psi>. \<psi> = \<up>false\<^sub>n) (DCA.trace (\<AA>\<^sub>\<nu> \<phi>) (to_stream w) (Abs \<phi>))"
    by (simp add: infs_snth \<AA>\<^sub>\<nu>_def DBA.transition_def af_lifted_semantics Abs_eq[symmetric] af_letter_lifted_semantics)

  also have "\<dots> \<longleftrightarrow> to_stream w \<in> DCA.language (\<AA>\<^sub>\<nu> \<phi>)"
    unfolding \<AA>\<^sub>\<nu>_def dca.initial_def dca.rejecting_def by (auto simp: dca_run)

  finally show ?thesis
    by simp
qed

lemma \<AA>\<^sub>\<nu>_FG_language:
  "\<phi> \<in> \<nu>LTL \<Longrightarrow> to_stream w \<in> DCA.language (\<AA>\<^sub>\<nu>_FG \<phi>) \<longleftrightarrow> w \<Turnstile>\<^sub>n F\<^sub>n (G\<^sub>n \<phi>)"
proof -
  assume "\<phi> \<in> \<nu>LTL"

  then have "w \<Turnstile>\<^sub>n F\<^sub>n (G\<^sub>n \<phi>) \<longleftrightarrow> (\<exists>k. \<forall>j. \<not> af (G\<^sub>n \<phi>) (w[k \<rightarrow> j]) \<sim>\<^sub>L false\<^sub>n)"
    using ltl_lang_equivalence.af_\<nu>LTL_FG by blast

  also have "\<dots> \<longleftrightarrow> (\<exists>n. \<forall>k>n. \<not> af\<^sub>G \<phi> (G\<^sub>n \<phi>) (w[0 \<rightarrow> k]) \<sim> false\<^sub>n)"
    using af\<^sub>G_semantics_ltr af\<^sub>G_semantics_rtl
    using \<open>\<phi> \<in> \<nu>LTL\<close> af_\<nu>LTL_FG calculation by blast

  also have "\<dots> \<longleftrightarrow> (\<exists>n. \<forall>k\<ge>n. \<not> af\<^sub>G \<phi> (G\<^sub>n \<phi>) (w[0 \<rightarrow> Suc k]) \<sim> false\<^sub>n)"
    by (metis less_Suc_eq_le less_imp_Suc_add)

  also have "\<dots> \<longleftrightarrow> fins (\<lambda>\<psi>. \<psi> = \<up>false\<^sub>n) (DCA.trace (\<AA>\<^sub>\<nu>_FG \<phi>) (to_stream w) (Abs (G\<^sub>n \<phi>)))"
    by (simp add: infs_snth \<AA>\<^sub>\<nu>_FG_def DBA.transition_def af\<^sub>G_lifted_semantics Abs_eq[symmetric] af_letter\<^sub>G_lifted_semantics)

  also have "\<dots> \<longleftrightarrow> to_stream w \<in> DCA.language (\<AA>\<^sub>\<nu>_FG \<phi>)"
    unfolding \<AA>\<^sub>\<nu>_FG_def dca.initial_def dca.rejecting_def by (auto simp: dca_run)

  finally show ?thesis
    by simp
qed


subsection \<open>A DCA checking the GF-advice Function\<close>

definition \<CC> :: "'a ltln \<Rightarrow> 'a ltln set \<Rightarrow> ('a set, 'ltlq \<times> 'ltlq) dca" where
  "\<CC> \<phi> X = dca UNIV (Abs \<phi>, Abs ((normalise \<phi>)[X]\<^sub>\<nu>)) (\<up>afletter\<^sub>\<nu> X) (\<lambda>p. snd p = \<up>false\<^sub>n)"

lemma \<CC>_language:
  "to_stream w \<in> DCA.language (\<CC> \<phi> X) \<longleftrightarrow> (\<exists>i. suffix i w \<Turnstile>\<^sub>n af \<phi> (prefix i w)[X]\<^sub>\<nu>)"
proof -

  have "(\<exists>i. suffix i w \<Turnstile>\<^sub>n af \<phi> (prefix i w)[X]\<^sub>\<nu>)
        \<longleftrightarrow> (\<exists>m. \<forall>k\<ge>m. \<not> snd (af\<^sub>\<nu> X (\<phi>, (normalise \<phi>)[X]\<^sub>\<nu>) (prefix (Suc k) w)) \<sim> false\<^sub>n)"
    using af\<^sub>\<nu>_semantics_ltr af\<^sub>\<nu>_semantics_rtl by blast

  also have "\<dots> \<longleftrightarrow> fins (\<lambda>p. snd p = \<up>false\<^sub>n) (DCA.trace (\<CC> \<phi> X) (to_stream w) (Abs \<phi>, Abs ((normalise \<phi>)[X]\<^sub>\<nu>)))"
    by(simp add: infs_snth \<CC>_def DCA.transition_def af\<^sub>\<nu>_lifted_semantics af_letter\<^sub>\<nu>_lifted_semantics Abs_eq)

  also have "\<dots> \<longleftrightarrow> to_stream w \<in> DCA.language (\<CC> \<phi> X)"
    by (simp add: \<CC>_def dca.initial_def dca.rejecting_def dca.language_def dca_run)

  finally show ?thesis
    by blast
qed


subsection \<open>A DRA for each combination of sets X and Y\<close>

lemma dba_language:
  "(\<And>w. to_stream w \<in> DBA.language \<AA> \<longleftrightarrow> w \<Turnstile>\<^sub>n \<phi>) \<Longrightarrow> DBA.language \<AA> = {w. to_omega w \<Turnstile>\<^sub>n \<phi>}"
  by (metis (mono_tags, lifting) Collect_cong dba.language_def mem_Collect_eq to_stream_to_omega)

lemma dca_language:
  "(\<And>w. to_stream w \<in> DCA.language \<AA> \<longleftrightarrow> w \<Turnstile>\<^sub>n \<phi>) \<Longrightarrow> DCA.language \<AA> = {w. to_omega w \<Turnstile>\<^sub>n \<phi>}"
  by (metis (mono_tags, lifting) Collect_cong dca.language_def mem_Collect_eq to_stream_to_omega)


definition \<AA>\<^sub>1 :: "'a ltln \<Rightarrow> 'a ltln list \<Rightarrow> ('a set, 'ltlq \<times> 'ltlq) dca" where
  "\<AA>\<^sub>1 \<phi> xs = \<CC> \<phi> (set xs)"

lemma \<AA>\<^sub>1_language:
  "to_omega ` DCA.language (\<AA>\<^sub>1 \<phi> xs) = L\<^sub>1 \<phi> (set xs)"
  by (simp add: \<AA>\<^sub>1_def L\<^sub>1_def set_eq_iff \<CC>_language)

lemma \<AA>\<^sub>1_alphabet:
  "DCA.alphabet (\<AA>\<^sub>1 \<phi> xs) = UNIV"
  unfolding \<AA>\<^sub>1_def \<CC>_def by simp


definition \<AA>\<^sub>2 :: "'a ltln list \<Rightarrow> 'a ltln list \<Rightarrow> ('a set, 'ltlq list degen) dba" where
  "\<AA>\<^sub>2 xs ys = DBA_Combine.intersect_list (map (\<lambda>\<psi>. \<AA>\<^sub>\<mu>_GF (\<psi>[set ys]\<^sub>\<mu>)) xs)"

lemma \<AA>\<^sub>2_language:
  "to_omega ` DBA.language (\<AA>\<^sub>2 xs ys) = L\<^sub>2 (set xs) (set ys)"
  by (simp add: \<AA>\<^sub>2_def L\<^sub>2_def set_eq_iff dba_language[OF \<AA>\<^sub>\<mu>_GF_language[OF FG_advice_\<mu>LTL(1)]])

lemma \<AA>\<^sub>2_alphabet:
  "DBA.alphabet (\<AA>\<^sub>2 xs ys) = UNIV"
  by (simp add: \<AA>\<^sub>2_def \<AA>\<^sub>\<mu>_GF_def)


definition \<AA>\<^sub>3 :: "'a ltln list \<Rightarrow> 'a ltln list \<Rightarrow> ('a set, 'ltlq list) dca" where
  "\<AA>\<^sub>3 xs ys = DCA_Combine.intersect_list (map (\<lambda>\<psi>. \<AA>\<^sub>\<nu>_FG (\<psi>[set xs]\<^sub>\<nu>)) ys)"

lemma \<AA>\<^sub>3_language:
  "to_omega ` DCA.language (\<AA>\<^sub>3 xs ys) = L\<^sub>3 (set xs) (set ys)"
  by (simp add: \<AA>\<^sub>3_def L\<^sub>3_def set_eq_iff dca_language[OF \<AA>\<^sub>\<nu>_FG_language[OF GF_advice_\<nu>LTL(1)]])

lemma \<AA>\<^sub>3_alphabet:
  "DCA.alphabet (\<AA>\<^sub>3 xs ys) = UNIV"
  by (simp add: \<AA>\<^sub>3_def \<AA>\<^sub>\<nu>_FG_def)


definition "\<AA>' \<phi> xs ys = intersect_bc (\<AA>\<^sub>2 xs ys) (DCA_Combine.intersect (\<AA>\<^sub>1 \<phi> xs) (\<AA>\<^sub>3 xs ys))"

lemma \<AA>'_language:
  "to_omega ` DRA.language (\<AA>' \<phi> xs ys) = (L\<^sub>1 \<phi> (set xs) \<inter> L\<^sub>2 (set xs) (set ys) \<inter> L\<^sub>3 (set xs) (set ys))"
  by (simp add: \<AA>'_def \<AA>\<^sub>1_language \<AA>\<^sub>2_language \<AA>\<^sub>3_language) fastforce

lemma \<AA>'_alphabet:
  "DRA.alphabet (\<AA>' \<phi> xs ys) = UNIV"
  by (simp add: \<AA>'_def \<AA>\<^sub>1_alphabet \<AA>\<^sub>2_alphabet \<AA>\<^sub>3_alphabet)



subsection \<open>A DRA for @{term "L(\<phi>)"}\<close>

text \<open>
  This is the final constant constructing a deterministic Rabin automaton
  using the pure version of the  @{thm master_theorem}.
\<close>

definition "ltl_to_dra \<phi> = DRA_Combine.union_list (map (\<lambda>(xs, ys). \<AA>' \<phi> xs ys) (advice_sets \<phi>))"

lemma ltl_to_dra_language:
  "to_omega ` DRA.language (ltl_to_dra \<phi>) = language_ltln \<phi>"
proof -
  have "(\<Inter>(a, b)\<in>set (advice_sets \<phi>). dra.alphabet (\<AA>' \<phi> a b)) =
    (\<Union>(a, b)\<in>set (advice_sets \<phi>). dra.alphabet (\<AA>' \<phi> a b))"
    using advice_sets_not_empty by (simp add: \<AA>'_alphabet)
  then have *: "DRA.language (DRA_Combine.union_list (map (\<lambda>(x, y). \<AA>' \<phi> x y) (advice_sets \<phi>))) =
    \<Union> (DRA.language ` set (map (\<lambda>(x, y). \<AA>' \<phi> x y) (advice_sets \<phi>)))"
    by (simp add: split_def)
  have "language_ltln \<phi> = \<Union> {(L\<^sub>1 \<phi> X \<inter> L\<^sub>2 X Y \<inter> L\<^sub>3 X Y) | X Y. X \<subseteq> subformulas\<^sub>\<mu> \<phi> \<and> Y \<subseteq> subformulas\<^sub>\<nu> \<phi>}"
    unfolding master_theorem_language by auto
  also have "\<dots> = \<Union> {L\<^sub>1 \<phi> (set xs) \<inter> L\<^sub>2 (set xs) (set ys) \<inter> L\<^sub>3 (set xs) (set ys) | xs ys. (xs, ys) \<in> set (advice_sets \<phi>)}"
    unfolding advice_sets_subformulas by (metis (no_types, lifting))
  also have "\<dots> = \<Union> {to_omega ` DRA.language (\<AA>' \<phi> xs ys) | xs ys. (xs, ys) \<in> set (advice_sets \<phi>)}"
    by (simp add: \<AA>'_language)
  finally show ?thesis
    using * by (auto simp add: ltl_to_dra_def)
qed

lemma ltl_to_dra_alphabet:
  "alphabet (ltl_to_dra \<phi>) = UNIV"
  by (auto simp: ltl_to_dra_def \<AA>'_alphabet)


subsection \<open>A DRA for @{term "L(\<phi>)"} with Restricted Advice Sets\<close>

text \<open>
  The following constant uses the @{thm master_theorem_restricted} to reduce
  the size of the resulting automaton.
\<close>

definition "ltl_to_dra_restricted \<phi> = DRA_Combine.union_list (map (\<lambda>(xs, ys). \<AA>' \<phi> xs ys) (restricted_advice_sets \<phi>))"

lemma ltl_to_dra_restricted_language:
  "to_omega ` DRA.language (ltl_to_dra_restricted \<phi>) = language_ltln \<phi>"
proof -
  have "(\<Inter>(a, b)\<in>set (restricted_advice_sets \<phi>). dra.alphabet (\<AA>' \<phi> a b)) =
    (\<Union>(a, b)\<in>set (restricted_advice_sets \<phi>). dra.alphabet (\<AA>' \<phi> a b))"
    using restricted_advice_sets_not_empty by (simp add: \<AA>'_alphabet)
  then have *: "DRA.language (DRA_Combine.union_list (map (\<lambda>(x, y). \<AA>' \<phi> x y) (restricted_advice_sets \<phi>))) =
    \<Union> (DRA.language ` set (map (\<lambda>(x, y). \<AA>' \<phi> x y) (restricted_advice_sets \<phi>)))"
    by (simp add: split_def)
  have "language_ltln \<phi> = \<Union> {(L\<^sub>1 \<phi> X \<inter> L\<^sub>2 X Y \<inter> L\<^sub>3 X Y) | X Y. X \<subseteq> subformulas\<^sub>\<mu> \<phi> \<inter> restricted_subformulas \<phi> \<and> Y \<subseteq> subformulas\<^sub>\<nu> \<phi> \<inter> restricted_subformulas \<phi>}"
    unfolding master_theorem_restricted_language by auto
  also have "\<dots> = \<Union> {L\<^sub>1 \<phi> (set xs) \<inter> L\<^sub>2 (set xs) (set ys) \<inter> L\<^sub>3 (set xs) (set ys) | xs ys. (xs, ys) \<in> set (restricted_advice_sets \<phi>)}"
    unfolding restricted_advice_sets_subformulas by (metis (no_types, lifting))
  also have "\<dots> = \<Union> {to_omega ` DRA.language (\<AA>' \<phi> xs ys) | xs ys. (xs, ys) \<in> set (restricted_advice_sets \<phi>)}"
    by (simp add: \<AA>'_language)
  finally show ?thesis
    using * by (auto simp add: ltl_to_dra_restricted_def)
qed

lemma ltl_to_dra_restricted_alphabet:
  "alphabet (ltl_to_dra_restricted \<phi>) = UNIV"
  by (auto simp: ltl_to_dra_restricted_def \<AA>'_alphabet)


subsection \<open>A DRA for @{term "L(\<phi>)"} with a finite alphabet\<close>

text \<open>
  Until this point, we use @{term UNIV} as the alphabet in all places.
  To explore the automaton, however, we need a way to fix the alphabet
  to some finite set.
\<close>

definition dra_set_alphabet :: "('a set, 'b) dra \<Rightarrow> 'a set set \<Rightarrow> ('a set, 'b) dra"
where
  "dra_set_alphabet \<AA> \<Sigma> = dra \<Sigma> (initial \<AA>) (transition \<AA>) (condition \<AA>)"

lemma dra_set_alphabet_language:
  "\<Sigma> \<subseteq> alphabet \<AA> \<Longrightarrow> language (dra_set_alphabet \<AA> \<Sigma>) = language \<AA> \<inter> {s. sset s \<subseteq> \<Sigma>}"
  by (auto simp add: dra_set_alphabet_def dra.language_def set_eq_iff dra.run_alt_def streams_iff_sset)

lemma dra_set_alphabet_alphabet[simp]:
  "alphabet (dra_set_alphabet \<AA> \<Sigma>) = \<Sigma>"
  unfolding dra_set_alphabet_def by simp

lemma dra_set_alphabet_nodes:
  "\<Sigma> \<subseteq> alphabet \<AA> \<Longrightarrow> DRA.nodes (dra_set_alphabet \<AA> \<Sigma>) \<subseteq> DRA.nodes \<AA>"
  unfolding dra_set_alphabet_def dra.nodes_alt_def dra.reachable_alt_def dra.path_alt_def
  by auto


definition "ltl_to_dra_alphabet \<phi> Ap = dra_set_alphabet (ltl_to_dra_restricted \<phi>) (Pow Ap)"

lemma ltl_to_dra_alphabet_language:
  assumes
    "atoms_ltln \<phi> \<subseteq> Ap"
  shows
    "to_omega ` language (ltl_to_dra_alphabet \<phi> Ap) = language_ltln \<phi> \<inter> {w. range w \<subseteq> Pow Ap}"
proof -
  have 1: "Pow Ap \<subseteq> alphabet (ltl_to_dra_restricted \<phi>)"
    unfolding ltl_to_dra_restricted_alphabet by simp

  show ?thesis
    unfolding ltl_to_dra_alphabet_def dra_set_alphabet_language[OF 1]
    by (simp add: ltl_to_dra_restricted_language sset_range) force
qed

lemma ltl_to_dra_alphabet_alphabet[simp]:
  "alphabet (ltl_to_dra_alphabet \<phi> Ap) = Pow Ap"
  unfolding ltl_to_dra_alphabet_def by simp

lemma ltl_to_dra_alphabet_nodes:
  "DRA.nodes (ltl_to_dra_alphabet \<phi> Ap) \<subseteq> DRA.nodes (ltl_to_dra_restricted \<phi>)"
  unfolding ltl_to_dra_alphabet_def
  by (rule dra_set_alphabet_nodes) (simp add: ltl_to_dra_restricted_alphabet)

end


subsection \<open>Verified Bounds for Number of Nodes\<close>

text \<open>
  Using two additional assumptions, we can show a double-exponential size bound
  for the constructed automaton.
\<close>

(* TODO add to HOL/Groups_List.thy *)
lemma list_prod_mono:
  "f \<le> g \<Longrightarrow> (\<Prod>x\<leftarrow>xs. f x) \<le> (\<Prod>x\<leftarrow>xs. g x)" for f g :: "'a \<Rightarrow> nat"
  by (induction xs) (auto simp: le_funD mult_le_mono)

(* TODO add to HOL/Groups_List.thy *)
lemma list_prod_const:
  "(\<And>x. x \<in> set xs \<Longrightarrow> f x \<le> c) \<Longrightarrow> (\<Prod>x\<leftarrow>xs. f x) \<le> c ^ length xs" for f :: "'a \<Rightarrow> nat"
  by (induction xs) (auto simp: mult_le_mono)

(* TODO add to HOL/Finite_Set.thy *)
lemma card_insert_Suc:
  "card (insert x S) \<le> Suc (card S)"
  by (metis Suc_n_not_le_n card.infinite card_insert_if finite_insert linear)

(* TODO add to HOL/Power.thy *)
lemma nat_power_le_imp_le:
  "0 < a \<Longrightarrow> a \<le> b \<Longrightarrow> x ^ a \<le> x ^ b" for x :: nat
  by (metis leD linorder_le_less_linear nat_power_less_imp_less neq0_conv power_eq_0_iff)

(* TODO add to HOL/Power.thy *)
lemma const_less_power:
  "n < x ^ n" if "x > 1"
  using that by (induction n) (auto simp: less_trans_Suc)

(* TODO add to HOL-Library/Log_Nat.thy *)
lemma floorlog_le_const:
  "floorlog x n \<le> n"
  by (induction n) (simp add: floorlog_eq_zero_iff, metis Suc_lessI floorlog_le_iff le_SucI power_inject_exp)


locale dra_construction_size = dra_construction + transition_functions_size +
  assumes
    equiv_finite: "finite P \<Longrightarrow> finite {Abs \<psi> | \<psi>. prop_atoms \<psi> \<subseteq> P}"
  assumes
    equiv_card: "finite P \<Longrightarrow> card {Abs \<psi> | \<psi>. prop_atoms \<psi> \<subseteq> P} \<le> 2 ^ 2 ^ card P"
begin

lemma af\<^sub>F_lifted_range:
  "nested_prop_atoms \<psi> \<subseteq> nested_prop_atoms (F\<^sub>n \<phi>) \<Longrightarrow> range (\<up>af\<^sub>F \<phi> (Abs \<psi>)) \<subseteq>  {Abs \<psi> | \<psi>. nested_prop_atoms \<psi> \<subseteq> nested_prop_atoms (F\<^sub>n \<phi>)}"
  using af\<^sub>F_lifted_semantics af\<^sub>F_nested_prop_atoms by blast

lemma af\<^sub>G_lifted_range:
  "nested_prop_atoms \<psi> \<subseteq> nested_prop_atoms (G\<^sub>n \<phi>) \<Longrightarrow> range (\<up>af\<^sub>G \<phi> (Abs \<psi>)) \<subseteq>  {Abs \<psi> | \<psi>. nested_prop_atoms \<psi> \<subseteq> nested_prop_atoms (G\<^sub>n \<phi>)}"
  using af\<^sub>G_lifted_semantics af\<^sub>G_nested_prop_atoms by blast


lemma \<AA>\<^sub>\<mu>_nodes:
  "DBA.nodes (\<AA>\<^sub>\<mu> \<phi>) \<subseteq> {Abs \<psi> | \<psi>. nested_prop_atoms \<psi> \<subseteq> nested_prop_atoms \<phi>}"
  unfolding \<AA>\<^sub>\<mu>_def
  using af_lifted_semantics af_nested_prop_atoms by fastforce

lemma \<AA>\<^sub>\<mu>_GF_nodes:
  "DBA.nodes (\<AA>\<^sub>\<mu>_GF \<phi>) \<subseteq> {Abs \<psi> | \<psi>. nested_prop_atoms \<psi> \<subseteq> nested_prop_atoms (F\<^sub>n \<phi>)}"
  unfolding \<AA>\<^sub>\<mu>_GF_def dba.nodes_alt_def dba.reachable_alt_def
  using af\<^sub>F_nested_prop_atoms[of "F\<^sub>n \<phi>"] by (auto simp: af\<^sub>F_lifted_semantics)

lemma \<AA>\<^sub>\<nu>_nodes:
  "DCA.nodes (\<AA>\<^sub>\<nu> \<phi>) \<subseteq> {Abs \<psi> | \<psi>. nested_prop_atoms \<psi> \<subseteq> nested_prop_atoms \<phi>}"
  unfolding \<AA>\<^sub>\<nu>_def
  using af_lifted_semantics af_nested_prop_atoms by fastforce

lemma \<AA>\<^sub>\<nu>_FG_nodes:
  "DCA.nodes (\<AA>\<^sub>\<nu>_FG \<phi>) \<subseteq> {Abs \<psi> | \<psi>. nested_prop_atoms \<psi> \<subseteq> nested_prop_atoms (G\<^sub>n \<phi>)}"
  unfolding \<AA>\<^sub>\<nu>_FG_def dca.nodes_alt_def dca.reachable_alt_def
  using af\<^sub>G_nested_prop_atoms[of "G\<^sub>n \<phi>"] by (auto simp: af\<^sub>G_lifted_semantics)

lemma \<CC>_nodes_normalise:
  "DCA.nodes (\<CC> \<phi> X) \<subseteq> {Abs \<psi> | \<psi>. nested_prop_atoms \<psi> \<subseteq> nested_prop_atoms \<phi>} \<times> {Abs \<psi> | \<psi>. nested_prop_atoms \<psi> \<subseteq> nested_prop_atoms\<^sub>\<nu> (normalise \<phi>) X}"
  unfolding \<CC>_def dca.nodes_alt_def dca.reachable_alt_def
  apply (auto simp add: af\<^sub>\<nu>_lifted_semantics af_letter\<^sub>\<nu>_lifted_semantics)
  using af\<^sub>\<nu>_fst_nested_prop_atoms apply force
  by (metis GF_advice_nested_prop_atoms\<^sub>\<nu> af\<^sub>\<nu>_snd_nested_prop_atoms Abs_eq af\<^sub>\<nu>_lifted_semantics fst_conv normalise_eq snd_conv sup.absorb_iff1)

lemma \<CC>_nodes:
  "DCA.nodes (\<CC> \<phi> X) \<subseteq> {Abs \<psi> | \<psi>. nested_prop_atoms \<psi> \<subseteq> nested_prop_atoms \<phi>} \<times> {Abs \<psi> | \<psi>. nested_prop_atoms \<psi> \<subseteq> nested_prop_atoms\<^sub>\<nu> \<phi> X}"
  unfolding \<CC>_def dca.nodes_alt_def dca.reachable_alt_def
  apply (auto simp add: af\<^sub>\<nu>_lifted_semantics af_letter\<^sub>\<nu>_lifted_semantics)
  using af\<^sub>\<nu>_fst_nested_prop_atoms apply force
  by (metis (no_types, hide_lams) GF_advice_nested_prop_atoms\<^sub>\<nu> af\<^sub>\<nu>_snd_nested_prop_atoms fst_eqD nested_prop_atoms\<^sub>\<nu>_subset normalise_nested_propos order_refl order_trans snd_eqD sup.order_iff)



lemma equiv_subset:
  "{Abs \<psi> |\<psi>. nested_prop_atoms \<psi> \<subseteq> P} \<subseteq> {Abs \<psi> |\<psi>. prop_atoms \<psi> \<subseteq> P}"
  using prop_atoms_nested_prop_atoms by blast

lemma equiv_finite':
  "finite P \<Longrightarrow> finite {Abs \<psi> | \<psi>. nested_prop_atoms \<psi> \<subseteq> P}"
  using equiv_finite equiv_subset finite_subset by fast

lemma equiv_card':
  "finite P \<Longrightarrow> card {Abs \<psi> | \<psi>. nested_prop_atoms \<psi> \<subseteq> P} \<le> 2 ^ 2 ^ card P"
  by (metis (mono_tags, lifting) equiv_card equiv_subset equiv_finite card_mono le_trans)


lemma nested_prop_atoms_finite:
  "finite {Abs \<psi> | \<psi>. nested_prop_atoms \<psi> \<subseteq> nested_prop_atoms \<phi>}"
  using equiv_finite'[OF Equivalence_Relations.nested_prop_atoms_finite] .

lemma nested_prop_atoms_card:
  "card {Abs \<psi> | \<psi>. nested_prop_atoms \<psi> \<subseteq> nested_prop_atoms \<phi>} \<le> 2 ^ 2 ^ card (nested_prop_atoms \<phi>)"
  using equiv_card'[OF Equivalence_Relations.nested_prop_atoms_finite] .

lemma nested_prop_atoms\<^sub>\<nu>_finite:
  "finite {Abs \<psi> | \<psi>. nested_prop_atoms \<psi> \<subseteq> nested_prop_atoms\<^sub>\<nu> \<phi> X}"
  using equiv_finite'[OF nested_prop_atoms\<^sub>\<nu>_finite] by fast

lemma nested_prop_atoms\<^sub>\<nu>_card:
  "card {Abs \<psi> | \<psi>. nested_prop_atoms \<psi> \<subseteq> nested_prop_atoms\<^sub>\<nu> \<phi> X} \<le> 2 ^ 2 ^ card (nested_prop_atoms \<phi>)" (is "?lhs \<le> ?rhs")
proof -
  have "finite {Abs \<psi> | \<psi>. prop_atoms \<psi> \<subseteq> nested_prop_atoms\<^sub>\<nu> \<phi> X}"
    by (simp add: nested_prop_atoms\<^sub>\<nu>_finite Advice.nested_prop_atoms\<^sub>\<nu>_finite equiv_finite)

  then have "?lhs \<le> card {Abs \<psi> | \<psi>. prop_atoms \<psi> \<subseteq> (nested_prop_atoms\<^sub>\<nu> \<phi> X)}"
    using card_mono equiv_subset by blast

  also have "\<dots> \<le> 2 ^ 2 ^ card (nested_prop_atoms\<^sub>\<nu> \<phi> X)"
    using equiv_card[OF Advice.nested_prop_atoms\<^sub>\<nu>_finite] by fast

  also have "\<dots> \<le> ?rhs"
    using nested_prop_atoms\<^sub>\<nu>_card by auto

  finally show ?thesis .
qed


lemma \<AA>\<^sub>\<mu>_GF_nodes_finite:
  "finite (DBA.nodes (\<AA>\<^sub>\<mu>_GF \<phi>))"
  using finite_subset[OF \<AA>\<^sub>\<mu>_GF_nodes nested_prop_atoms_finite] .

lemma \<AA>\<^sub>\<nu>_FG_nodes_finite:
  "finite (DCA.nodes (\<AA>\<^sub>\<nu>_FG \<phi>))"
  using finite_subset[OF \<AA>\<^sub>\<nu>_FG_nodes nested_prop_atoms_finite] .

lemma \<AA>\<^sub>\<mu>_GF_nodes_card:
  "card (DBA.nodes (\<AA>\<^sub>\<mu>_GF \<phi>)) \<le> 2 ^ 2 ^ card (nested_prop_atoms (F\<^sub>n \<phi>))"
  using le_trans[OF card_mono[OF nested_prop_atoms_finite \<AA>\<^sub>\<mu>_GF_nodes] nested_prop_atoms_card] .

lemma \<AA>\<^sub>\<nu>_FG_nodes_card:
  "card (DCA.nodes (\<AA>\<^sub>\<nu>_FG \<phi>)) \<le> 2 ^ 2 ^ card (nested_prop_atoms (G\<^sub>n \<phi>))"
  using le_trans[OF card_mono[OF nested_prop_atoms_finite \<AA>\<^sub>\<nu>_FG_nodes] nested_prop_atoms_card] .


lemma \<AA>\<^sub>2_nodes_finite_helper:
  "list_all (finite \<circ> DBA.nodes) (map (\<lambda>\<psi>. \<AA>\<^sub>\<mu>_GF (\<psi>[set ys]\<^sub>\<mu>)) xs)"
  by (auto simp: list.pred_map list_all_iff \<AA>\<^sub>\<mu>_GF_nodes_finite)

lemma \<AA>\<^sub>2_nodes_finite:
  "finite (DBA.nodes (\<AA>\<^sub>2 xs ys))"
  unfolding \<AA>\<^sub>2_def using DBA_Combine.intersect_list_nodes_finite \<AA>\<^sub>2_nodes_finite_helper .

lemma \<AA>\<^sub>3_nodes_finite_helper:
  "list_all (finite \<circ> DCA.nodes) (map (\<lambda>\<psi>. \<AA>\<^sub>\<nu>_FG (\<psi>[set xs]\<^sub>\<nu>)) ys)"
  by (auto simp: list.pred_map list_all_iff \<AA>\<^sub>\<nu>_FG_nodes_finite)

lemma \<AA>\<^sub>3_nodes_finite:
  "finite (DCA.nodes (\<AA>\<^sub>3 xs ys))"
  unfolding \<AA>\<^sub>3_def using DCA_Combine.intersect_list_nodes_finite \<AA>\<^sub>3_nodes_finite_helper .

lemma \<AA>\<^sub>2_nodes_card:
  assumes
    "length xs \<le> n"
  and
    "\<And>\<psi>. \<psi> \<in> set xs \<Longrightarrow> card (nested_prop_atoms \<psi>) \<le> n"
  shows
    "card (DBA.nodes (\<AA>\<^sub>2 xs ys)) \<le> 2 ^ 2 ^ (n + floorlog 2 n + 2)"
proof -
  have 1: "\<And>\<psi>. \<psi> \<in> set xs \<Longrightarrow> card (nested_prop_atoms (F\<^sub>n \<psi>[set ys]\<^sub>\<mu>)) \<le> Suc n"
  proof -
    fix \<psi>
    assume "\<psi> \<in> set xs"

    have "card (nested_prop_atoms (F\<^sub>n (\<psi>[set ys]\<^sub>\<mu>)))
          \<le> Suc (card (nested_prop_atoms (\<psi>[set ys]\<^sub>\<mu>)))"
      by (simp add: card_insert_Suc)

    also have "\<dots> \<le> Suc (card (nested_prop_atoms \<psi>))"
      by (simp add: FG_advice_nested_prop_atoms_card)

    also have "\<dots> \<le> Suc n"
      by (simp add: assms(2) \<open>\<psi> \<in> set xs\<close>)

    finally show "card (nested_prop_atoms (F\<^sub>n (\<psi>[set ys]\<^sub>\<mu>))) \<le> Suc n" .
  qed

  have "(\<Prod>\<psi>\<leftarrow>xs. card (DBA.nodes (\<AA>\<^sub>\<mu>_GF (\<psi>[set ys]\<^sub>\<mu>))))
        \<le> (\<Prod>\<psi>\<leftarrow>xs. 2 ^ 2 ^ card (nested_prop_atoms (F\<^sub>n (\<psi>[set ys]\<^sub>\<mu>))))"
    by (rule list_prod_mono) (insert \<AA>\<^sub>\<mu>_GF_nodes_card le_fun_def, blast)

  also have "\<dots> \<le> (2 ^ 2 ^ Suc n) ^ length xs"
    by (rule list_prod_const) (metis 1 Suc_leI nat_power_le_imp_le nat_power_eq_Suc_0_iff neq0_conv pos2 zero_less_power)

  also have "\<dots> \<le> (2 ^ 2 ^ Suc n) ^ n"
    using assms(1) nat_power_le_imp_le by fastforce

  also have "\<dots> = 2 ^ (n * 2 ^ Suc n)"
    by (metis Groups.mult_ac(2) power_mult)

  also have "\<dots> \<le> 2 ^ (2 ^ floorlog 2 n * 2 ^ Suc n)"
    by (cases "n = 0") (auto simp: floorlog_bounds less_imp_le_nat)

  also have "\<dots> = 2 ^ 2 ^ (Suc n + floorlog 2 n)"
    by (simp add: power_add)

  finally have 2: "(\<Prod>\<psi>\<leftarrow>xs. card (DBA.nodes (\<AA>\<^sub>\<mu>_GF (\<psi>[set ys]\<^sub>\<mu>)))) \<le> 2 ^ 2 ^ (Suc n + floorlog 2 n)" .

  have "card (DBA.nodes (\<AA>\<^sub>2 xs ys)) \<le> max 1 (length xs) * (\<Prod>\<psi>\<leftarrow>xs. card (DBA.nodes (\<AA>\<^sub>\<mu>_GF (\<psi>[set ys]\<^sub>\<mu>))))"
    using DBA_Combine.intersect_list_nodes_card[OF \<AA>\<^sub>2_nodes_finite_helper]
    by (auto simp: \<AA>\<^sub>2_def comp_def)

  also have "\<dots> \<le> max 1 n * 2 ^ 2 ^ (Suc n + floorlog 2 n)"
    using assms(1) 2 by (simp add: mult_le_mono)

  also have "\<dots> \<le> 2 ^ (floorlog 2 n) * 2 ^ 2 ^ (Suc n + floorlog 2 n)"
    by (cases "n = 0") (auto simp: floorlog_bounds less_imp_le_nat)

  also have "\<dots> = 2 ^ (floorlog 2 n + 2 ^ (Suc n + floorlog 2 n))"
    by (simp add: power_add)

  also have "\<dots> \<le> 2 ^ (n + 2 ^ (Suc n + floorlog 2 n))"
    by (simp add: floorlog_le_const)

  also have "\<dots> \<le> 2 ^ 2 ^ (n + floorlog 2 n + 2)"
    by simp (metis const_less_power Suc_1 add_Suc_right add_leE lessI less_imp_le_nat power_Suc)

  finally show ?thesis .
qed


lemma \<AA>\<^sub>3_nodes_card:
  assumes
    "length ys \<le> n"
  and
    "\<And>\<psi>. \<psi> \<in> set ys \<Longrightarrow> card (nested_prop_atoms \<psi>) \<le> n"
  shows
    "card (DCA.nodes (\<AA>\<^sub>3 xs ys)) \<le> 2 ^ 2 ^ (n + floorlog 2 n + 1)"
proof -
  have 1: "\<And>\<psi>. \<psi> \<in> set ys \<Longrightarrow> card (DCA.nodes (\<AA>\<^sub>\<nu>_FG (\<psi>[set xs]\<^sub>\<nu>))) \<le> 2 ^ 2 ^ Suc n"
  proof -
    fix \<psi>
    assume "\<psi> \<in> set ys"

    have "card (nested_prop_atoms (G\<^sub>n \<psi>[set xs]\<^sub>\<nu>))
          \<le> Suc (card (nested_prop_atoms (\<psi>[set xs]\<^sub>\<nu>)))"
      by (simp add: card_insert_Suc)

    also have "\<dots> \<le> Suc (card (nested_prop_atoms \<psi>))"
      by (simp add: GF_advice_nested_prop_atoms_card)

    also have "\<dots> \<le> Suc n"
      by (simp add: assms(2) \<open>\<psi> \<in> set ys\<close>)

    finally have 2: "card (nested_prop_atoms (G\<^sub>n \<psi>[set xs]\<^sub>\<nu>)) \<le> Suc n" .

    then show "?thesis \<psi>"
      by (intro le_trans[OF \<AA>\<^sub>\<nu>_FG_nodes_card]) (meson one_le_numeral power_increasing)
  qed


  have "card (DCA.nodes (\<AA>\<^sub>3 xs ys)) \<le> (\<Prod>\<psi>\<leftarrow>ys. card (DCA.nodes (\<AA>\<^sub>\<nu>_FG (\<psi>[set xs]\<^sub>\<nu>))))"
    unfolding \<AA>\<^sub>3_def using DCA_Combine.intersect_list_nodes_card[OF \<AA>\<^sub>3_nodes_finite_helper]
    by (auto simp: comp_def)

  also have "\<dots> \<le> (2 ^ 2 ^ Suc n) ^ length ys"
    by (rule list_prod_const) (rule 1)

  also have "\<dots> \<le> (2 ^ 2 ^ Suc n) ^ n"
    by (simp add: assms(1) power_increasing)

  also have "\<dots> \<le> 2 ^ (n * 2 ^ Suc n)"
    by (metis le_refl mult.commute power_mult)

  also have "\<dots> \<le> 2 ^ (2 ^ floorlog 2 n * 2 ^ Suc n)"
    by (cases \<open>n > 0\<close>) (simp_all add: floorlog_bounds less_imp_le_nat)

  also have "\<dots> = 2 ^ 2 ^ (n + floorlog 2 n + 1)"
    by (simp add: power_add)

  finally show ?thesis .
qed


lemma \<AA>\<^sub>1_nodes_finite:
  "finite (DCA.nodes (\<AA>\<^sub>1 \<phi> xs))"
  unfolding \<AA>\<^sub>1_def
  by (metis (no_types, lifting) finite_subset \<CC>_nodes finite_SigmaI nested_prop_atoms\<^sub>\<nu>_finite nested_prop_atoms_finite)

lemma \<AA>\<^sub>1_nodes_card:
  assumes
    "card (subfrmlsn \<phi>) \<le> n"
  shows
    "card (DCA.nodes (\<AA>\<^sub>1 \<phi> xs)) \<le> 2 ^ 2 ^ (n + 1)"
proof -
  let ?fst = "{Abs \<psi> | \<psi>. nested_prop_atoms \<psi> \<subseteq> nested_prop_atoms \<phi>}"
  let ?snd = "{Abs \<psi> | \<psi>. nested_prop_atoms \<psi> \<subseteq> nested_prop_atoms\<^sub>\<nu> \<phi> (set xs)}"

  have 1: "card (nested_prop_atoms \<phi>) \<le> n"
    by (meson card_mono[OF subfrmlsn_finite nested_prop_atoms_subfrmlsn] assms le_trans)


  have "card (DCA.nodes (\<AA>\<^sub>1 \<phi> xs)) \<le> card (?fst \<times> ?snd)"
    unfolding \<AA>\<^sub>1_def
    by (rule card_mono) (simp_all add: \<CC>_nodes nested_prop_atoms\<^sub>\<nu>_finite nested_prop_atoms_finite)

  also have "\<dots> = card ?fst * card ?snd"
    using nested_prop_atoms\<^sub>\<nu>_finite card_cartesian_product by blast

  also have "\<dots> \<le> 2 ^ 2 ^ card (nested_prop_atoms \<phi>) * 2 ^ 2 ^ card (nested_prop_atoms \<phi>)"
    using nested_prop_atoms\<^sub>\<nu>_card nested_prop_atoms_card mult_le_mono by blast

  also have "\<dots> = 2 ^ 2 ^ (card (nested_prop_atoms \<phi>) + 1)"
    by (simp add: semiring_normalization_rules(36))

  also have "\<dots> \<le> 2 ^ 2 ^ (n + 1)"
    using assms 1 by simp

  finally show ?thesis .
qed


lemma \<AA>'_nodes_finite:
  "finite (DRA.nodes (\<AA>' \<phi> xs ys))"
  unfolding \<AA>'_def
  using intersect_nodes_finite intersect_bc_nodes_finite
  using \<AA>\<^sub>1_nodes_finite \<AA>\<^sub>2_nodes_finite \<AA>\<^sub>3_nodes_finite
  by fast

lemma \<AA>'_nodes_card:
  assumes
    "length xs \<le> n"
  and
    "\<And>\<psi>. \<psi> \<in> set xs \<Longrightarrow> card (nested_prop_atoms \<psi>) \<le> n"
  and
    "length ys \<le> n"
  and
    "\<And>\<psi>. \<psi> \<in> set ys \<Longrightarrow> card (nested_prop_atoms \<psi>) \<le> n"
  and
    "card (subfrmlsn \<phi>) \<le> n"
  shows
    "card (DRA.nodes (\<AA>' \<phi> xs ys)) \<le> 2 ^ 2 ^ (n + floorlog 2 n + 4)"
proof -
  have "n + 1 \<le> n + floorlog 2 n + 2"
    by auto

  then have 1: "(2::nat) ^ (n + 1) \<le> 2 ^ (n + floorlog 2 n + 2)"
    using one_le_numeral power_increasing by blast


  have "card (DRA.nodes (\<AA>' \<phi> xs ys)) \<le> card (DCA.nodes (\<AA>\<^sub>1 \<phi> xs)) * card (DBA.nodes (\<AA>\<^sub>2 xs ys)) * card (DCA.nodes (\<AA>\<^sub>3 xs ys))" (is "?lhs \<le> ?rhs")
  proof (unfold \<AA>'_def)
    have "card (DBA.nodes (\<AA>\<^sub>2 xs ys)) * card (DCA.nodes (DCA_Combine.intersect (\<AA>\<^sub>1 \<phi> xs) (\<AA>\<^sub>3 xs ys))) \<le> ?rhs"
      by (simp add: intersect_nodes_card[OF \<AA>\<^sub>1_nodes_finite \<AA>\<^sub>3_nodes_finite])
    then show "card (DRA.nodes (intersect_bc (\<AA>\<^sub>2 xs ys) (DCA_Combine.intersect (\<AA>\<^sub>1 \<phi> xs) (\<AA>\<^sub>3 xs ys)))) \<le> ?rhs"
      by (meson intersect_bc_nodes_card[OF \<AA>\<^sub>2_nodes_finite intersect_nodes_finite[OF \<AA>\<^sub>1_nodes_finite \<AA>\<^sub>3_nodes_finite]] basic_trans_rules(23))
  qed

  also have "\<dots> \<le> 2 ^ 2 ^ (n + 1) * 2 ^ 2 ^ (n + floorlog 2 n + 2) * 2 ^ 2 ^ (n + floorlog 2 n + 1)"
    using \<AA>\<^sub>1_nodes_card[OF assms(5)] \<AA>\<^sub>2_nodes_card[OF assms(1,2)] \<AA>\<^sub>3_nodes_card[OF assms(3,4)]
    by (metis mult_le_mono)

  also have "\<dots> = 2 ^ (2 ^ (n + 1) + 2 ^ (n + floorlog 2 n + 2) + 2 ^ (n + floorlog 2 n + 1))"
    by (metis power_add)

  also have "\<dots> \<le> 2 ^ (4 * 2 ^ (n + floorlog 2 n + 2))"
    using 1 by auto

  finally show ?thesis
    by (simp add: numeral.simps(2) power_add)
qed

lemma subformula_nested_prop_atoms_subfrmlsn:
  "\<psi> \<in> subfrmlsn \<phi> \<Longrightarrow> nested_prop_atoms \<psi> \<subseteq> subfrmlsn \<phi>"
  using nested_prop_atoms_subfrmlsn subfrmlsn_subset by blast


lemma ltl_to_dra_nodes_finite:
  "finite (DRA.nodes (ltl_to_dra \<phi>))"
  unfolding ltl_to_dra_def
  apply (rule DRA_Combine.union_list_nodes_finite)
  apply (simp add: split_def \<AA>'_alphabet advice_sets_not_empty)
  apply (simp add: list.pred_set split_def \<AA>'_nodes_finite)
  done

lemma ltl_to_dra_restricted_nodes_finite:
  "finite (DRA.nodes (ltl_to_dra_restricted \<phi>))"
  unfolding ltl_to_dra_restricted_def
  apply (rule DRA_Combine.union_list_nodes_finite)
  apply (simp add: split_def \<AA>'_alphabet advice_sets_not_empty)
  apply (simp add: list.pred_set split_def \<AA>'_nodes_finite)
  done

lemma ltl_to_dra_alphabet_nodes_finite:
  "finite (DRA.nodes (ltl_to_dra_alphabet \<phi> AP))"
  using ltl_to_dra_alphabet_nodes ltl_to_dra_restricted_nodes_finite finite_subset by fast


lemma ltl_to_dra_nodes_card:
  assumes
    "card (subfrmlsn \<phi>) \<le> n"
  shows
    "card (DRA.nodes (ltl_to_dra \<phi>)) \<le> 2 ^ 2 ^ (2 * n + floorlog 2 n + 4)"
proof -
  let ?map = "map (\<lambda>(x, y). \<AA>' \<phi> x y) (advice_sets \<phi>)"

  have 1: "\<And>x::nat. x > 0 \<Longrightarrow> x ^ length (advice_sets \<phi>) \<le> x ^ 2 ^ card (subfrmlsn \<phi>)"
    by (metis advice_sets_length linorder_not_less nat_power_less_imp_less)

  have "card (DRA.nodes (ltl_to_dra \<phi>)) \<le> prod_list (map (card \<circ> DRA.nodes) ?map)"
    unfolding ltl_to_dra_def
    apply (rule DRA_Combine.union_list_nodes_card)
    unfolding list.pred_set using \<AA>'_nodes_finite by auto

  also have "\<dots> = (\<Prod>(x, y)\<leftarrow>advice_sets \<phi>. card (DRA.nodes (\<AA>' \<phi> x y)))"
    by (induction "advice_sets \<phi>") (auto, metis (no_types, lifting) comp_apply split_def)

  also have "\<dots> \<le> (2 ^ 2 ^ (n + floorlog 2 n + 4)) ^ length (advice_sets \<phi>)"
  proof (rule list_prod_const, unfold split_def, rule \<AA>'_nodes_card)
    show "\<And>x. x \<in> set (advice_sets \<phi>) \<Longrightarrow> length (fst x) \<le> n"
      using advice_sets_element_length assms by fastforce

    show "\<And>x \<psi>. \<lbrakk>x \<in> set (advice_sets \<phi>); \<psi> \<in> set (fst x)\<rbrakk> \<Longrightarrow> card (nested_prop_atoms \<psi>) \<le> n"
      using advice_sets_element_subfrmlsn(1) assms subformula_nested_prop_atoms_subfrmlsn subformulas\<^sub>\<mu>_subfrmlsn
      by (metis (no_types, lifting) card_mono subfrmlsn_finite subset_iff sup.absorb_iff2 sup.coboundedI1 surjective_pairing)

    show "\<And>x. x \<in> set (advice_sets \<phi>) \<Longrightarrow> length (snd x) \<le> n"
      using advice_sets_element_length assms by fastforce

    show "\<And>x \<psi>. \<lbrakk>x \<in> set (advice_sets \<phi>); \<psi> \<in> set (snd x)\<rbrakk> \<Longrightarrow> card (nested_prop_atoms \<psi>) \<le> n"
      using advice_sets_element_subfrmlsn(2) assms subformula_nested_prop_atoms_subfrmlsn subformulas\<^sub>\<nu>_subfrmlsn
      by (metis (no_types, lifting) card_mono subfrmlsn_finite subset_iff sup.absorb_iff2 sup.coboundedI1 surjective_pairing)
  qed (insert assms, blast)

  also have "\<dots> \<le> (2 ^ 2 ^ (n + floorlog 2 n + 4)) ^ (2 ^ card (subfrmlsn \<phi>))"
    by (simp add: 1)

  also have "\<dots> \<le> (2 ^ 2 ^ (n + floorlog 2 n + 4)) ^ (2 ^ n)"
    by (simp add: assms power_increasing)

  also have "\<dots> = 2 ^ (2 ^ n * 2 ^ (n + floorlog 2 n + 4))"
    by (simp add: ac_simps power_mult [symmetric])

  also have "\<dots> = 2 ^ 2 ^ (2 * n + floorlog 2 n + 4)"
    by (simp add: power_add) (simp add: mult_2 power_add)

  finally show ?thesis .
qed

text \<open>We verify the size bound of the automaton to be double exponential.\<close>

theorem ltl_to_dra_size:
  "card (DRA.nodes (ltl_to_dra \<phi>)) \<le> 2 ^ 2 ^ (2 * size \<phi> + floorlog 2 (size \<phi>) + 4)"
  using ltl_to_dra_nodes_card subfrmlsn_card by blast

end

end
