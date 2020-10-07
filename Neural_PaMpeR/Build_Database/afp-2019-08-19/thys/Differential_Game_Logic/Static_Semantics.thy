theory "Static_Semantics"
imports
  "Syntax"
  "Denotational_Semantics"
begin
section \<open>Static Semantics\<close>

subsection \<open>Semantically-defined Static Semantics\<close>
paragraph \<open>Auxiliary notions of projection of winning conditions\<close>

text\<open>upward projection: \<open>restrictto X V\<close> is extends X to the states that agree on V with some state in X,
so variables outside V can assume arbitrary values.\<close>
definition restrictto :: "state set \<Rightarrow> variable set \<Rightarrow> state set"
where
  "restrictto X V = {\<nu>. \<exists>\<omega>. \<omega>\<in>X \<and> Vagree \<omega> \<nu> V}"

text\<open>downward projection: \<open>selectlike X \<nu> V\<close> selects state \<open>\<nu>\<close> on V in X,
so all variables of V are required to remain constant\<close>
definition selectlike :: "state set \<Rightarrow> state \<Rightarrow> variable set \<Rightarrow> state set"
  where
  "selectlike X \<nu> V = {\<omega>\<in>X. Vagree \<omega> \<nu> V}"

paragraph \<open>Free variables, semantically characterized.\<close>
text\<open>Free variables of a term\<close>
definition FVT :: "trm \<Rightarrow> variable set"
where
  "FVT t = {x. \<exists>I.\<exists>\<nu>.\<exists>\<omega>. Vagree \<nu> \<omega> (-{x}) \<and> \<not>(term_sem I t \<nu> = term_sem I t \<omega>)}"

text\<open>Free variables of a formula\<close>
definition FVF :: "fml \<Rightarrow> variable set"
where
  "FVF \<phi> = {x. \<exists>I.\<exists>\<nu>.\<exists>\<omega>. Vagree \<nu> \<omega> (-{x}) \<and> \<nu> \<in> fml_sem I \<phi> \<and> \<omega> \<notin> fml_sem I \<phi>}"

text\<open>Free variables of a hybrid game\<close>
definition FVG :: "game \<Rightarrow> variable set"
where
  "FVG \<alpha> = {x. \<exists>I.\<exists>\<nu>.\<exists>\<omega>.\<exists>X. Vagree \<nu> \<omega> (-{x}) \<and> \<nu> \<in> game_sem I \<alpha> (restrictto X (-{x})) \<and> \<omega> \<notin> game_sem I \<alpha> (restrictto X (-{x}))}"
  
paragraph \<open>Bound variables, semantically characterized.\<close>
text\<open>Bound variables of a hybrid game\<close>
definition BVG :: "game \<Rightarrow> variable set"
where
  "BVG \<alpha> = {x. \<exists>I.\<exists>\<omega>.\<exists>X. \<omega> \<in> game_sem I \<alpha> X \<and> \<omega> \<notin> game_sem I \<alpha> (selectlike X \<omega> {x})}"


subsection \<open>Simple Observations\<close>
  
lemma BVG_elem [simp] :"(x\<in>BVG \<alpha>) = (\<exists>I \<omega> X. \<omega> \<in> game_sem I \<alpha> X \<and> \<omega> \<notin> game_sem I \<alpha> (selectlike X \<omega> {x}))"
  unfolding BVG_def by simp

lemma nonBVG_rule: "(\<And>I \<omega> X. (\<omega> \<in> game_sem I \<alpha> X) = (\<omega> \<in> game_sem I \<alpha> (selectlike X \<omega> {x})))
  \<Longrightarrow> x\<notin>BVG \<alpha>"
  using BVG_elem by simp

lemma nonBVG_inc_rule: "(\<And>I \<omega> X. (\<omega> \<in> game_sem I \<alpha> X) \<Longrightarrow> (\<omega> \<in> game_sem I \<alpha> (selectlike X \<omega> {x})))
  \<Longrightarrow> x\<notin>BVG \<alpha>"
  using BVG_elem by simp
  
lemma FVT_finite: "finite(FVT t)"
  using allvars_finite by (metis finite_subset mem_Collect_eq subsetI)
lemma FVF_finite: "finite(FVF e)"
  using allvars_finite by (metis finite_subset mem_Collect_eq subsetI)
lemma FVG_finite: "finite(FVG a)"
  using allvars_finite by (metis finite_subset mem_Collect_eq subsetI)

end
