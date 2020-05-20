(*
    Author:   Salomon Sickert
    License:  BSD
*)

section \<open>Code Export\<close>

theory Normal_Form_Code_Export imports
  LTL.Code_Equations
  LTL.Rewriting
  LTL.Disjunctive_Normal_Form
  HOL.String
  Normal_Form
begin

fun flatten_pi_1_list :: "String.literal ltln \<Rightarrow> String.literal ltln list \<Rightarrow> String.literal ltln"
  where
  "flatten_pi_1_list (\<psi>\<^sub>1 U\<^sub>n \<psi>\<^sub>2) M = (if (\<psi>\<^sub>1 U\<^sub>n \<psi>\<^sub>2) \<in> set M then (flatten_pi_1_list \<psi>\<^sub>1 M) W\<^sub>n (flatten_pi_1_list \<psi>\<^sub>2 M) else false\<^sub>n)"
| "flatten_pi_1_list (\<psi>\<^sub>1 W\<^sub>n \<psi>\<^sub>2) M = (flatten_pi_1_list \<psi>\<^sub>1 M) W\<^sub>n (flatten_pi_1_list \<psi>\<^sub>2 M)"
| "flatten_pi_1_list (\<psi>\<^sub>1 M\<^sub>n \<psi>\<^sub>2) M = (if (\<psi>\<^sub>1 M\<^sub>n \<psi>\<^sub>2) \<in> set M then (flatten_pi_1_list \<psi>\<^sub>1 M) R\<^sub>n (flatten_pi_1_list \<psi>\<^sub>2 M) else false\<^sub>n)"
| "flatten_pi_1_list (\<psi>\<^sub>1 R\<^sub>n \<psi>\<^sub>2) M = (flatten_pi_1_list \<psi>\<^sub>1 M) R\<^sub>n (flatten_pi_1_list \<psi>\<^sub>2 M)"
| "flatten_pi_1_list (\<psi>\<^sub>1 and\<^sub>n \<psi>\<^sub>2) M = (flatten_pi_1_list \<psi>\<^sub>1 M) and\<^sub>n (flatten_pi_1_list \<psi>\<^sub>2 M)"
| "flatten_pi_1_list (\<psi>\<^sub>1 or\<^sub>n \<psi>\<^sub>2) M = (flatten_pi_1_list \<psi>\<^sub>1 M) or\<^sub>n (flatten_pi_1_list \<psi>\<^sub>2 M)"
| "flatten_pi_1_list (X\<^sub>n \<psi>) M = X\<^sub>n (flatten_pi_1_list \<psi> M)"
| "flatten_pi_1_list \<phi> _ = \<phi>"

fun flatten_sigma_1_list :: "String.literal ltln \<Rightarrow> String.literal ltln list \<Rightarrow> String.literal ltln"
where
  "flatten_sigma_1_list (\<psi>\<^sub>1 U\<^sub>n \<psi>\<^sub>2) N = (flatten_sigma_1_list \<psi>\<^sub>1 N) U\<^sub>n (flatten_sigma_1_list \<psi>\<^sub>2 N)"
| "flatten_sigma_1_list (\<psi>\<^sub>1 W\<^sub>n \<psi>\<^sub>2) N = (if (\<psi>\<^sub>1 W\<^sub>n \<psi>\<^sub>2) \<in> set N then true\<^sub>n else (flatten_sigma_1_list \<psi>\<^sub>1 N) U\<^sub>n (flatten_sigma_1_list \<psi>\<^sub>2 N))"
| "flatten_sigma_1_list (\<psi>\<^sub>1 M\<^sub>n \<psi>\<^sub>2) N = (flatten_sigma_1_list \<psi>\<^sub>1 N) M\<^sub>n (flatten_sigma_1_list \<psi>\<^sub>2 N)"
| "flatten_sigma_1_list (\<psi>\<^sub>1 R\<^sub>n \<psi>\<^sub>2) N = (if (\<psi>\<^sub>1 R\<^sub>n \<psi>\<^sub>2) \<in> set N then true\<^sub>n else (flatten_sigma_1_list \<psi>\<^sub>1 N) M\<^sub>n (flatten_sigma_1_list \<psi>\<^sub>2 N))"
| "flatten_sigma_1_list (\<psi>\<^sub>1 and\<^sub>n \<psi>\<^sub>2) N = (flatten_sigma_1_list \<psi>\<^sub>1 N) and\<^sub>n (flatten_sigma_1_list \<psi>\<^sub>2 N)"
| "flatten_sigma_1_list (\<psi>\<^sub>1 or\<^sub>n \<psi>\<^sub>2) N = (flatten_sigma_1_list \<psi>\<^sub>1 N) or\<^sub>n (flatten_sigma_1_list \<psi>\<^sub>2 N)"
| "flatten_sigma_1_list (X\<^sub>n \<psi>) N = X\<^sub>n (flatten_sigma_1_list \<psi> N)"
| "flatten_sigma_1_list \<phi> _ = \<phi>"

fun flatten_sigma_2_list :: "String.literal ltln \<Rightarrow> String.literal ltln list \<Rightarrow> String.literal ltln"
where
  "flatten_sigma_2_list (\<phi> U\<^sub>n \<psi>) M = (flatten_sigma_2_list \<phi> M) U\<^sub>n (flatten_sigma_2_list \<psi> M)"
| "flatten_sigma_2_list (\<phi> W\<^sub>n \<psi>) M = (flatten_sigma_2_list \<phi> M) U\<^sub>n ((flatten_sigma_2_list \<psi> M) or\<^sub>n (G\<^sub>n (flatten_pi_1_list \<phi> M)))"
| "flatten_sigma_2_list (\<phi> M\<^sub>n \<psi>) M = (flatten_sigma_2_list \<phi> M) M\<^sub>n (flatten_sigma_2_list \<psi> M)"
| "flatten_sigma_2_list (\<phi> R\<^sub>n \<psi>) M = ((flatten_sigma_2_list \<phi> M) or\<^sub>n (G\<^sub>n (flatten_pi_1_list \<psi> M))) M\<^sub>n (flatten_sigma_2_list \<psi> M)"
| "flatten_sigma_2_list (\<phi> and\<^sub>n \<psi>) M = (flatten_sigma_2_list \<phi> M) and\<^sub>n (flatten_sigma_2_list \<psi> M)"
| "flatten_sigma_2_list (\<phi> or\<^sub>n \<psi>) M = (flatten_sigma_2_list \<phi> M) or\<^sub>n (flatten_sigma_2_list \<psi> M)"
| "flatten_sigma_2_list (X\<^sub>n \<phi>) M = X\<^sub>n (flatten_sigma_2_list \<phi> M)"
| "flatten_sigma_2_list \<phi> _ = \<phi>"

lemma flatten_code_equations[simp]:
  "\<phi>[set M]\<^sub>\<Pi>\<^sub>1 = flatten_pi_1_list \<phi> M"
  "\<phi>[set M]\<^sub>\<Sigma>\<^sub>1 = flatten_sigma_1_list \<phi> M"
  "\<phi>[set M]\<^sub>\<Sigma>\<^sub>2 = flatten_sigma_2_list \<phi> M"
  by (induction \<phi>) auto

abbreviation "and_list \<equiv> foldl And_ltln true\<^sub>n"

abbreviation "or_list \<equiv> foldl Or_ltln false\<^sub>n"

definition "normal_form_disjunct (\<phi> :: String.literal ltln) M N 
  \<equiv> (flatten_sigma_2_list \<phi> M)
      and\<^sub>n (and_list (map (\<lambda>\<psi>. G\<^sub>n (F\<^sub>n (flatten_sigma_1_list \<psi> N))) M) 
      and\<^sub>n (and_list (map (\<lambda>\<psi>. F\<^sub>n (G\<^sub>n (flatten_pi_1_list    \<psi> M))) N)))"

definition "normal_form (\<phi> :: String.literal ltln) 
  \<equiv> or_list (map (\<lambda>(M, N). normal_form_disjunct \<phi> M N) (advice_sets \<phi>))" 

lemma and_list_semantic: "w \<Turnstile>\<^sub>n and_list xs \<longleftrightarrow> (\<forall>x \<in> set xs. w \<Turnstile>\<^sub>n x)"
  by (induction xs rule: rev_induct) auto 

lemma or_list_semantic: "w \<Turnstile>\<^sub>n or_list xs \<longleftrightarrow> (\<exists>x \<in> set xs. w \<Turnstile>\<^sub>n x)"
  by (induction xs rule: rev_induct) auto

theorem normal_form_correct:
  "w \<Turnstile>\<^sub>n \<phi> \<longleftrightarrow> w \<Turnstile>\<^sub>n normal_form \<phi>"
proof 
  assume "w \<Turnstile>\<^sub>n \<phi>"
  then obtain M N where "M \<subseteq> subformulas\<^sub>\<mu> \<phi>" and "N \<subseteq> subformulas\<^sub>\<nu> \<phi>"
    and c1: "w \<Turnstile>\<^sub>n \<phi>[M]\<^sub>\<Sigma>\<^sub>2" and c2: "\<forall>\<psi> \<in> M. w \<Turnstile>\<^sub>n G\<^sub>n (F\<^sub>n \<psi>[N]\<^sub>\<Sigma>\<^sub>1)" and c3: "\<forall>\<psi> \<in> N. w \<Turnstile>\<^sub>n F\<^sub>n (G\<^sub>n \<psi>[M]\<^sub>\<Pi>\<^sub>1)"
    using normal_form_with_flatten_sigma_2 by metis
  then obtain ms ns where "M = set ms" and "N = set ns" and ms_ns_in: "(ms, ns) \<in> set (advice_sets \<phi>)" 
    by (meson advice_sets_subformulas)
  then have "w \<Turnstile>\<^sub>n normal_form_disjunct \<phi> ms ns"
    using c1 c2 c3 by (simp add: and_list_semantic normal_form_disjunct_def)
  then show "w \<Turnstile>\<^sub>n normal_form \<phi>"
    using normal_form_def or_list_semantic ms_ns_in by fastforce
next
  assume "w \<Turnstile>\<^sub>n normal_form \<phi>"
  then obtain ms ns where "(ms, ns) \<in> set (advice_sets \<phi>)" 
    and "w \<Turnstile>\<^sub>n normal_form_disjunct \<phi> ms ns"
    unfolding normal_form_def or_list_semantic by force
  then have "set ms \<subseteq> subformulas\<^sub>\<mu> \<phi>" and "set ns \<subseteq> subformulas\<^sub>\<nu> \<phi>"
    and c1: "w \<Turnstile>\<^sub>n \<phi>[set ms]\<^sub>\<Sigma>\<^sub>2" and c2: "\<forall>\<psi> \<in> set ms. w \<Turnstile>\<^sub>n G\<^sub>n (F\<^sub>n \<psi>[set ns]\<^sub>\<Sigma>\<^sub>1)" and c3: "\<forall>\<psi> \<in> set ns. w \<Turnstile>\<^sub>n F\<^sub>n (G\<^sub>n \<psi>[set ms]\<^sub>\<Pi>\<^sub>1)"  
    using advice_sets_element_subfrmlsn 
    by (auto simp: and_list_semantic normal_form_disjunct_def) blast
  then show "w \<Turnstile>\<^sub>n \<phi>"
    using normal_form_with_flatten_sigma_2 by metis
qed

definition "normal_form_with_simplifier (\<phi> :: String.literal ltln) 
  \<equiv> min_dnf (simplify Slow (normal_form (simplify Slow \<phi>)))" 

lemma ltl_semantics_min_dnf:
  "w \<Turnstile>\<^sub>n \<phi> \<longleftrightarrow> (\<exists>C \<in> min_dnf \<phi>. \<forall>\<psi>. \<psi> |\<in>| C \<longrightarrow> w \<Turnstile>\<^sub>n \<psi>)" (is "?lhs \<longleftrightarrow> ?rhs")
proof 
  let ?M = "{\<psi>. w \<Turnstile>\<^sub>n \<psi>}"
  assume ?lhs
  hence "?M \<Turnstile>\<^sub>P \<phi>"
    using ltl_models_equiv_prop_entailment by blast
  then obtain M' where "fset M' \<subseteq> ?M" and "M' \<in> min_dnf \<phi>"
    using min_dnf_iff_prop_assignment_subset by blast
  thus ?rhs
    by (meson in_mono mem_Collect_eq notin_fset)
next 
  let ?M = "{\<psi>. w \<Turnstile>\<^sub>n \<psi>}"
  assume ?rhs
  then obtain M' where "fset M' \<subseteq> ?M" and "M' \<in> min_dnf \<phi>"
    using notin_fset by fastforce
  hence "?M \<Turnstile>\<^sub>P \<phi>"
    using min_dnf_iff_prop_assignment_subset by blast
  thus ?lhs
    using ltl_models_equiv_prop_entailment by blast
qed

theorem 
  "w \<Turnstile>\<^sub>n \<phi> \<longleftrightarrow> (\<exists>C \<in> (normal_form_with_simplifier \<phi>). \<forall>\<psi>. \<psi> |\<in>| C \<longrightarrow> w \<Turnstile>\<^sub>n \<psi>)" (is "?lhs \<longleftrightarrow> ?rhs")
  unfolding normal_form_with_simplifier_def ltl_semantics_min_dnf[symmetric] 
  using normal_form_correct by simp

text \<open>In order to export the code run \texttt{isabelle build -D [PATH] -e}.\<close>

export_code normal_form in SML
export_code normal_form_with_simplifier in SML

end