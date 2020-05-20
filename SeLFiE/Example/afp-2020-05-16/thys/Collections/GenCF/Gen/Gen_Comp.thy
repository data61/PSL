section \<open>\isaheader{Generic Compare Algorithms}\<close>
theory Gen_Comp
imports 
  "../Intf/Intf_Comp"
  Automatic_Refinement.Automatic_Refinement
  "HOL-Library.Product_Lexorder"
begin

subsection \<open>Order for Product\<close>
(* TODO: Optimization? Or only go via prod_cmp? *)
lemma autoref_prod_cmp_dflt_id[autoref_rules_raw]: 
  "(dflt_cmp (\<le>) (<), dflt_cmp (\<le>) (<)) \<in>
    \<langle>Id,Id\<rangle>prod_rel \<rightarrow> \<langle>Id,Id\<rangle>prod_rel \<rightarrow> Id"
  by auto

lemma gen_prod_cmp_dflt[autoref_rules_raw]:
  assumes PRIO_TAG_GEN_ALGO
  assumes "GEN_OP cmp1 (dflt_cmp (\<le>) (<)) (R1 \<rightarrow> R1 \<rightarrow> Id)"
  assumes "GEN_OP cmp2 (dflt_cmp (\<le>) (<)) (R2 \<rightarrow> R2 \<rightarrow> Id)"
  shows "(cmp_prod cmp1 cmp2, dflt_cmp (\<le>) (<)) \<in>
    \<langle>R1,R2\<rangle>prod_rel \<rightarrow> \<langle>R1,R2\<rangle>prod_rel \<rightarrow> Id"
proof -
  have E: "dflt_cmp (\<le>) (<) 
    = cmp_prod (dflt_cmp (\<le>) (<)) (dflt_cmp (\<le>) (<))"
    by (auto simp: dflt_cmp_def prod_less_def prod_le_def intro!: ext)

  show ?thesis
    using assms
    unfolding autoref_tag_defs E
    by parametricity
qed


end
