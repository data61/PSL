section \<open>Setup\<close>

theory Dict_Construction
imports Automatic_Refinement.Refine_Util
keywords "declassify" :: thy_decl
begin

definition set_of :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<times> 'b) set" where
"set_of P = {(x, y). P x y}"

lemma wfP_implies_wf_set_of: "wfP P \<Longrightarrow> wf (set_of P)"
unfolding wfP_def set_of_def .

lemma wf_set_of_implies_wfP: "wf (set_of P) \<Longrightarrow> wfP P"
unfolding wfP_def set_of_def .

lemma wf_simulate_simple:
  assumes "wf r"
  assumes "\<And>x y. (x, y) \<in> r' \<Longrightarrow> (g x, g y) \<in> r"
  shows "wf r'"
using assms
by (metis in_inv_image wf_eq_minimal wf_inv_image)

lemma set_ofI: "P x y \<Longrightarrow> (x, y) \<in> set_of P"
unfolding set_of_def by simp

lemma set_ofD: "(x, y) \<in> set_of P \<Longrightarrow> P x y"
unfolding set_of_def by simp

lemma wfP_simulate_simple:
  assumes "wfP r"
  assumes "\<And>x y. r' x y \<Longrightarrow> r (g x) (g y)"
  shows "wfP r'"
apply (rule wf_set_of_implies_wfP)
apply (rule wf_simulate_simple[where g = g])
apply (rule wfP_implies_wf_set_of)
apply (fact assms)
using assms(2) by (auto intro: set_ofI dest: set_ofD)

lemma wf_implies_dom: "wf (set_of R) \<Longrightarrow> All (Wellfounded.accp R)"
apply (rule allI)
apply (rule accp_wfPD)
apply (rule wf_set_of_implies_wfP) .

lemma wfP_implies_dom: "wfP R \<Longrightarrow> All (Wellfounded.accp R)"
by (metis wfP_implies_wf_set_of wf_implies_dom)

named_theorems dict_construction_specs

ML_file \<open>dict_construction_util.ML\<close>
ML_file \<open>transfer_termination.ML\<close>
ML_file \<open>congruences.ML\<close>
ML_file \<open>side_conditions.ML\<close>
ML_file \<open>class_graph.ML\<close>
ML_file \<open>dict_construction.ML\<close>

method_setup fo_cong_rule = \<open>
  Attrib.thm >> (fn thm => fn ctxt => SIMPLE_METHOD' (Dict_Construction_Util.fo_cong_tac ctxt thm))
\<close> "resolve congruence rule using first-order matching"

declare [[code drop: "(\<and>)"]]
lemma [code]: "True \<and> p \<longleftrightarrow> p" "False \<and> p \<longleftrightarrow> False" by auto

declare [[code drop: "(\<or>)"]]
lemma [code]: "True \<or> p \<longleftrightarrow> True" "False \<or> p \<longleftrightarrow> p" by auto

declare comp_cong[fundef_cong del]
declare fun.map_cong[fundef_cong]

end