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

    "../Logical_Characterization/Master_Theorem"

    Transition_Systems_and_Automata.DBA_Combine
    Transition_Systems_and_Automata.DCA_Combine
    Transition_Systems_and_Automata.DRA_Combine
begin

\<comment> \<open>We use prefix and suffix on infinite words.\<close>
hide_const Sublist.prefix Sublist.suffix

locale dra_construction = transition_functions eq + quotient eq Rep Abs
  for
    eq :: "'a ltln \<Rightarrow> 'a ltln \<Rightarrow> bool" (infix "\<sim>" 75)
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

lemma af\<^sub>F_lifted_range:
  "nested_prop_atoms \<psi> \<subseteq> nested_prop_atoms (F\<^sub>n \<phi>) \<Longrightarrow> range (\<up>af\<^sub>F \<phi> (Abs \<psi>)) \<subseteq>  {Abs \<psi> | \<psi>. nested_prop_atoms \<psi> \<subseteq> nested_prop_atoms (F\<^sub>n \<phi>)}"
  using af\<^sub>F_lifted_semantics af\<^sub>F_nested_prop_atoms by blast

lemma af\<^sub>G_lifted_range:
  "nested_prop_atoms \<psi> \<subseteq> nested_prop_atoms (G\<^sub>n \<phi>) \<Longrightarrow> range (\<up>af\<^sub>G \<phi> (Abs \<psi>)) \<subseteq>  {Abs \<psi> | \<psi>. nested_prop_atoms \<psi> \<subseteq> nested_prop_atoms (G\<^sub>n \<phi>)}"
  using af\<^sub>G_lifted_semantics af\<^sub>G_nested_prop_atoms by blast


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
  "DBA.run (dba UNIV p \<delta> \<alpha>) (to_stream w) p"
  unfolding DBA.run_def by (rule transition_system.snth_run) fastforce

lemma dca_run:
  "DCA.run (dca UNIV p \<delta> \<alpha>) (to_stream w) p"
  unfolding DCA.run_def by (rule transition_system.snth_run) fastforce


lemma \<AA>\<^sub>\<mu>_language:
  "\<phi> \<in> \<mu>LTL \<Longrightarrow> to_stream w \<in> DBA.language (\<AA>\<^sub>\<mu> \<phi>) \<longleftrightarrow> w \<Turnstile>\<^sub>n \<phi>"
proof -
  assume "\<phi> \<in> \<mu>LTL"

  then have "w \<Turnstile>\<^sub>n \<phi> \<longleftrightarrow> (\<forall>n. \<exists>k\<ge>n. af \<phi> (w[0 \<rightarrow> k]) \<sim> true\<^sub>n)"
    by (meson af_\<mu>LTL af_prefix_true le_cases)

  also have "\<dots> \<longleftrightarrow> (\<forall>n. \<exists>k\<ge>n. af \<phi> (w[0 \<rightarrow> Suc k]) \<sim> true\<^sub>n)"
    by (meson af_prefix_true le_SucI order_refl)

  also have "\<dots> \<longleftrightarrow> infs (\<lambda>\<psi>. \<psi> = \<up>true\<^sub>n) (DBA.trace (\<AA>\<^sub>\<mu> \<phi>) (to_stream w) (Abs \<phi>))"
    by (simp add: infs_snth \<AA>\<^sub>\<mu>_def DBA.succ_def af_lifted_semantics Abs_eq[symmetric] af_letter_lifted_semantics)

  also have "\<dots> \<longleftrightarrow> to_stream w \<in> DBA.language (\<AA>\<^sub>\<mu> \<phi>)"
    unfolding \<AA>\<^sub>\<mu>_def dba.initial_def dba.accepting_def
    by (metis dba_run DBA.language DBA.language_elim dba.sel(2) dba.sel(4))

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
    by (simp add: infs_snth \<AA>\<^sub>\<mu>_GF_def DBA.succ_def af\<^sub>F_lifted_semantics Abs_eq[symmetric] af_letter\<^sub>F_lifted_semantics)

  also have "\<dots> \<longleftrightarrow> to_stream w \<in> DBA.language (\<AA>\<^sub>\<mu>_GF \<phi>)"
    unfolding \<AA>\<^sub>\<mu>_GF_def dba.initial_def dba.accepting_def
    by (metis dba_run DBA.language DBA.language_elim dba.sel(2) dba.sel(4))

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

  also have "\<dots> \<longleftrightarrow> \<not> infs (\<lambda>\<psi>. \<psi> = \<up>false\<^sub>n) (DCA.trace (\<AA>\<^sub>\<nu> \<phi>) (to_stream w) (Abs \<phi>))"
    by (simp add: infs_snth \<AA>\<^sub>\<nu>_def DBA.succ_def af_lifted_semantics Abs_eq[symmetric] af_letter_lifted_semantics)

  also have "\<dots> \<longleftrightarrow> to_stream w \<in> DCA.language (\<AA>\<^sub>\<nu> \<phi>)"
    unfolding \<AA>\<^sub>\<nu>_def dca.initial_def dca.rejecting_def
    by (metis dca_run DCA.language DCA.language_elim dca.sel(2) dca.sel(4))

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

  also have "\<dots> \<longleftrightarrow> \<not> infs (\<lambda>\<psi>. \<psi> = \<up>false\<^sub>n) (DCA.trace (\<AA>\<^sub>\<nu>_FG \<phi>) (to_stream w) (Abs (G\<^sub>n \<phi>)))"
    by (simp add: infs_snth \<AA>\<^sub>\<nu>_FG_def DBA.succ_def af\<^sub>G_lifted_semantics Abs_eq[symmetric] af_letter\<^sub>G_lifted_semantics)

  also have "\<dots> \<longleftrightarrow> to_stream w \<in> DCA.language (\<AA>\<^sub>\<nu>_FG \<phi>)"
    unfolding \<AA>\<^sub>\<nu>_FG_def dca.initial_def dca.rejecting_def
    by (metis dca_run DCA.language DCA.language_elim dca.sel(2) dca.sel(4))

  finally show ?thesis
    by simp
qed


lemma \<AA>\<^sub>\<mu>_nodes:
  "DBA.nodes (\<AA>\<^sub>\<mu> \<phi>) \<subseteq> {Abs \<psi> | \<psi>. nested_prop_atoms \<psi> \<subseteq> nested_prop_atoms \<phi>}"
  unfolding \<AA>\<^sub>\<mu>_def transition_system_initial.nodes_alt_def
  using af_lifted_semantics af_nested_prop_atoms by fastforce

lemma \<AA>\<^sub>\<mu>_GF_nodes:
  "DBA.nodes (\<AA>\<^sub>\<mu>_GF \<phi>) \<subseteq> {Abs \<psi> | \<psi>. nested_prop_atoms \<psi> \<subseteq> nested_prop_atoms (F\<^sub>n \<phi>)}"
  unfolding \<AA>\<^sub>\<mu>_GF_def DBA.nodes_def transition_system_initial.nodes_alt_def transition_system.reachable_alt_def
  using af\<^sub>F_nested_prop_atoms[of "F\<^sub>n \<phi>"] by (auto simp: af\<^sub>F_lifted_semantics)

lemma \<AA>\<^sub>\<nu>_nodes:
  "DCA.nodes (\<AA>\<^sub>\<nu> \<phi>) \<subseteq> {Abs \<psi> | \<psi>. nested_prop_atoms \<psi> \<subseteq> nested_prop_atoms \<phi>}"
  unfolding \<AA>\<^sub>\<nu>_def transition_system_initial.nodes_alt_def
  using af_lifted_semantics af_nested_prop_atoms by fastforce

lemma \<AA>\<^sub>\<nu>_FG_nodes:
  "DCA.nodes (\<AA>\<^sub>\<nu>_FG \<phi>) \<subseteq> {Abs \<psi> | \<psi>. nested_prop_atoms \<psi> \<subseteq> nested_prop_atoms (G\<^sub>n \<phi>)}"
  unfolding \<AA>\<^sub>\<nu>_FG_def DCA.nodes_def transition_system_initial.nodes_alt_def transition_system.reachable_alt_def
  using af\<^sub>G_nested_prop_atoms[of "G\<^sub>n \<phi>"] by (auto simp: af\<^sub>G_lifted_semantics)



subsection \<open>A DCA checking the GF-advice Function\<close>

definition \<CC> :: "'a ltln \<Rightarrow> 'a ltln set \<Rightarrow> ('a set, 'ltlq \<times> 'ltlq) dca" where
  "\<CC> \<phi> X = dca UNIV (Abs \<phi>, Abs (\<phi>[X]\<^sub>\<nu>)) (\<up>afletter\<^sub>\<nu> X) (\<lambda>p. snd p = \<up>false\<^sub>n)"

lemma \<CC>_language:
  "to_stream w \<in> DCA.language (\<CC> \<phi> X) \<longleftrightarrow> (\<exists>i. suffix i w \<Turnstile>\<^sub>n af \<phi> (prefix i w)[X]\<^sub>\<nu>)"
proof -

  have "(\<exists>i. suffix i w \<Turnstile>\<^sub>n af \<phi> (prefix i w)[X]\<^sub>\<nu>)
        \<longleftrightarrow> (\<exists>m. \<forall>k\<ge>m. \<not> snd (af\<^sub>\<nu> X (\<phi>, \<phi>[X]\<^sub>\<nu>) (prefix (Suc k) w)) \<sim> false\<^sub>n)"
    using af\<^sub>\<nu>_semantics_ltr af\<^sub>\<nu>_semantics_rtl by blast

  also have "\<dots> \<longleftrightarrow> \<not> infs (\<lambda>p. snd p = \<up>false\<^sub>n) (DCA.trace (\<CC> \<phi> X) (to_stream w) (Abs \<phi>, Abs (\<phi>[X]\<^sub>\<nu>)))"
    by(simp add: infs_snth \<CC>_def DCA.succ_def af\<^sub>\<nu>_lifted_semantics af_letter\<^sub>\<nu>_lifted_semantics Abs_eq)

  also have "\<dots> \<longleftrightarrow> to_stream w \<in> DCA.language (\<CC> \<phi> X)"
    by (simp add: \<CC>_def dca.initial_def dca.rejecting_def DCA.language_def dca_run)

  finally show ?thesis
    by blast
qed


lemma \<CC>_nodes:
  "DCA.nodes (\<CC> \<phi> X) \<subseteq> {Abs \<psi> | \<psi>. nested_prop_atoms \<psi> \<subseteq> nested_prop_atoms \<phi>} \<times> {Abs \<psi> | \<psi>. nested_prop_atoms \<psi> \<subseteq> nested_prop_atoms\<^sub>\<nu> \<phi> X}"
  unfolding \<CC>_def DCA.nodes_def transition_system_initial.nodes_alt_def transition_system.reachable_alt_def
  apply (auto simp add: af\<^sub>\<nu>_lifted_semantics af_letter\<^sub>\<nu>_lifted_semantics)
  using af\<^sub>\<nu>_fst_nested_prop_atoms apply force
  using GF_advice_nested_prop_atoms\<^sub>\<nu> af\<^sub>\<nu>_snd_nested_prop_atoms dra_construction_axioms by fastforce



subsection \<open>A DRA for each combination of sets X and Y\<close>

lemma dba_language:
  "(\<And>w. to_stream w \<in> DBA.language \<AA> \<longleftrightarrow> w \<Turnstile>\<^sub>n \<phi>) \<Longrightarrow> DBA.language \<AA> = {w. to_omega w \<Turnstile>\<^sub>n \<phi>}"
  by (metis (mono_tags, lifting) Collect_cong DBA.language_def mem_Collect_eq to_stream_to_omega)

lemma dca_language:
  "(\<And>w. to_stream w \<in> DCA.language \<AA> \<longleftrightarrow> w \<Turnstile>\<^sub>n \<phi>) \<Longrightarrow> DCA.language \<AA> = {w. to_omega w \<Turnstile>\<^sub>n \<phi>}"
  by (metis (mono_tags, lifting) Collect_cong DCA.language_def mem_Collect_eq to_stream_to_omega)


definition \<AA>\<^sub>1 :: "'a ltln \<Rightarrow> 'a ltln list \<Rightarrow> ('a set, 'ltlq \<times> 'ltlq) dca" where
  "\<AA>\<^sub>1 \<phi> xs = \<CC> \<phi> (set xs)"

lemma \<AA>\<^sub>1_language:
  "to_omega ` DCA.language (\<AA>\<^sub>1 \<phi> xs) = L\<^sub>1 \<phi> (set xs)"
  by (simp add: \<AA>\<^sub>1_def L\<^sub>1_def set_eq_iff \<CC>_language)

lemma \<AA>\<^sub>1_alphabet:
  "DCA.alphabet (\<AA>\<^sub>1 \<phi> xs) = UNIV"
  unfolding \<AA>\<^sub>1_def \<CC>_def by simp


definition \<AA>\<^sub>2 :: "'a ltln list \<Rightarrow> 'a ltln list \<Rightarrow> ('a set, 'ltlq list degen) dba" where
  "\<AA>\<^sub>2 xs ys = dbail (map (\<lambda>\<psi>. \<AA>\<^sub>\<mu>_GF (\<psi>[set ys]\<^sub>\<mu>)) xs)"

lemma \<AA>\<^sub>2_language:
  "to_omega ` DBA.language (\<AA>\<^sub>2 xs ys) = L\<^sub>2 (set xs) (set ys)"
  by (simp add: \<AA>\<^sub>2_def L\<^sub>2_def set_eq_iff dba_language[OF \<AA>\<^sub>\<mu>_GF_language[OF FG_advice_\<mu>LTL(1)]])

lemma \<AA>\<^sub>2_alphabet:
  "DBA.alphabet (\<AA>\<^sub>2 xs ys) = UNIV"
  by (simp add: \<AA>\<^sub>2_def \<AA>\<^sub>\<mu>_GF_def dbail_def dbgail_def DGBA.degen_def)


definition \<AA>\<^sub>3 :: "'a ltln list \<Rightarrow> 'a ltln list \<Rightarrow> ('a set, 'ltlq list) dca" where
  "\<AA>\<^sub>3 xs ys = dcail (map (\<lambda>\<psi>. \<AA>\<^sub>\<nu>_FG (\<psi>[set xs]\<^sub>\<nu>)) ys)"

lemma \<AA>\<^sub>3_language:
  "to_omega ` DCA.language (\<AA>\<^sub>3 xs ys) = L\<^sub>3 (set xs) (set ys)"
  by (simp add: \<AA>\<^sub>3_def L\<^sub>3_def set_eq_iff dca_language[OF \<AA>\<^sub>\<nu>_FG_language[OF GF_advice_\<nu>LTL(1)]])

lemma \<AA>\<^sub>3_alphabet:
  "DCA.alphabet (\<AA>\<^sub>3 xs ys) = UNIV"
  by (simp add: \<AA>\<^sub>3_def \<AA>\<^sub>\<nu>_FG_def dcail_def)


definition "\<AA>' \<phi> xs ys = dbcrai (\<AA>\<^sub>2 xs ys) (dcai (\<AA>\<^sub>1 \<phi> xs) (\<AA>\<^sub>3 xs ys))"

lemma \<AA>'_language:
  "to_omega ` DRA.language (\<AA>' \<phi> xs ys) = (L\<^sub>1 \<phi> (set xs) \<inter> L\<^sub>2 (set xs) (set ys) \<inter> L\<^sub>3 (set xs) (set ys))"
  by (simp add: \<AA>'_def \<AA>\<^sub>1_language \<AA>\<^sub>2_language \<AA>\<^sub>3_language) fastforce

lemma \<AA>'_alphabet:
  "DRA.alphabet (\<AA>' \<phi> xs ys) = UNIV"
  by (simp add: \<AA>'_def dbcrai_def dcai_def \<AA>\<^sub>1_alphabet \<AA>\<^sub>2_alphabet \<AA>\<^sub>3_alphabet)



subsection \<open>A DRA for @{term "L(\<phi>)"}\<close>

definition "ltl_to_dra \<phi> = draul (map (\<lambda>(xs, ys). \<AA>' \<phi> xs ys) (advice_sets \<phi>))"

lemma ltl_to_dra_language:
  "to_omega ` DRA.language (ltl_to_dra \<phi>) = language_ltln \<phi>"
proof -
  have 1: "INTER (set (map (\<lambda>(x, y). \<AA>' \<phi> x y) (advice_sets \<phi>))) dra.alphabet = UNION (set (map (\<lambda>(x, y). \<AA>' \<phi> x y) (advice_sets \<phi>))) dra.alphabet"
    by (induction "advice_sets \<phi>") (metis advice_sets_not_empty, simp add: \<AA>'_alphabet split_def advice_sets_not_empty)

  have "language_ltln \<phi> = \<Union> {(L\<^sub>1 \<phi> X \<inter> L\<^sub>2 X Y \<inter> L\<^sub>3 X Y) | X Y. X \<subseteq> subformulas\<^sub>\<mu> \<phi> \<and> Y \<subseteq> subformulas\<^sub>\<nu> \<phi>}"
    unfolding master_theorem_language by auto
  also have "\<dots> = \<Union> {L\<^sub>1 \<phi> (set xs) \<inter> L\<^sub>2 (set xs) (set ys) \<inter> L\<^sub>3 (set xs) (set ys) | xs ys. (xs, ys) \<in> set (advice_sets \<phi>)}"
    unfolding advice_sets_subformulas by (metis (no_types, lifting))
  also have "\<dots> = \<Union> {to_omega ` DRA.language (\<AA>' \<phi> xs ys) | xs ys. (xs, ys) \<in> set (advice_sets \<phi>)}"
    by (simp add: \<AA>'_language)
  finally show ?thesis
    unfolding ltl_to_dra_def draul_language[OF 1] by auto
qed

lemma ltl_to_dra_alphabet:
  "alphabet (ltl_to_dra \<phi>) = UNIV"
  by (auto simp: ltl_to_dra_def draul_def \<AA>'_alphabet split: prod.split)
     (insert advice_sets_subformulas, blast)



subsection \<open>Setting the Alphabet of a DRA\<close>

definition dra_set_alphabet :: "('a set, 'b) dra \<Rightarrow> 'a set set \<Rightarrow> ('a set, 'b) dra"
where
  "dra_set_alphabet \<AA> \<Sigma> = dra \<Sigma> (initial \<AA>) (succ \<AA>) (accepting \<AA>)"

lemma dra_set_alphabet_language:
  "\<Sigma> \<subseteq> alphabet \<AA> \<Longrightarrow> language (dra_set_alphabet \<AA> \<Sigma>) = language \<AA> \<inter> {s. sset s \<subseteq> \<Sigma>}"
  by (auto simp add: dra_set_alphabet_def language_def set_eq_iff DRA.run_alt_def)

lemma dra_set_alphabet_alphabet[simp]:
  "alphabet (dra_set_alphabet \<AA> \<Sigma>) = \<Sigma>"
  unfolding dra_set_alphabet_def by simp

lemma dra_set_alphabet_nodes:
  "\<Sigma> \<subseteq> alphabet \<AA> \<Longrightarrow> DRA.nodes (dra_set_alphabet \<AA> \<Sigma>) \<subseteq> DRA.nodes \<AA>"
  unfolding dra_set_alphabet_def DRA.nodes_def transition_system_initial.nodes_alt_def transition_system.reachable_alt_def
  by auto (metis DRA.path_alt_def DRA.path_def dra.sel(1) dra.sel(3) subset_trans)



subsection \<open>A DRA for @{term "L(\<phi>)"} with a finite alphabet\<close>

definition "ltl_to_dra_alphabet \<phi> Ap = dra_set_alphabet (ltl_to_dra \<phi>) (Pow Ap)"

lemma ltl_to_dra_alphabet_language:
  assumes
    "atoms_ltln \<phi> \<subseteq> Ap"
  shows
    "to_omega ` language (ltl_to_dra_alphabet \<phi> Ap) = language_ltln \<phi> \<inter> {w. range w \<subseteq> Pow Ap}"
proof -
  have 1: "Pow Ap \<subseteq> alphabet (ltl_to_dra \<phi>)"
    unfolding ltl_to_dra_alphabet by simp

  show ?thesis
    unfolding ltl_to_dra_alphabet_def dra_set_alphabet_language[OF 1]
    by (simp add: ltl_to_dra_language sset_range) force
qed

lemma ltl_to_dra_alphabet_alphabet[simp]:
  "alphabet (ltl_to_dra_alphabet \<phi> Ap) = Pow Ap"
  unfolding ltl_to_dra_alphabet_def by simp

lemma ltl_to_dra_alphabet_nodes:
  "DRA.nodes (ltl_to_dra_alphabet \<phi> Ap) \<subseteq> DRA.nodes (ltl_to_dra \<phi>)"
  unfolding ltl_to_dra_alphabet_def
  by (rule dra_set_alphabet_nodes) (simp add: ltl_to_dra_alphabet)

end

end
