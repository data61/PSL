theory Incredible_Signatures
imports
  Main 
  "HOL-Library.FSet"
  "HOL-Library.Stream"
  Abstract_Formula
begin

text \<open>This theory contains the definition for proof graph signatures, in the variants
\<^item> Plain port graph
\<^item> Port graph with local hypotheses
\<^item> Labeled port graph
\<^item> Port graph with local constants
\<close>

locale Port_Graph_Signature =
  fixes nodes :: "'node stream"
  fixes inPorts :: "'node \<Rightarrow> 'inPort fset"
  fixes outPorts :: "'node \<Rightarrow> 'outPort fset"

locale Port_Graph_Signature_Scoped =
  Port_Graph_Signature +
  fixes hyps :: "'node \<Rightarrow> 'outPort \<rightharpoonup> 'inPort"
  assumes hyps_correct: "hyps n p1 = Some p2 \<Longrightarrow> p1 |\<in>| outPorts n \<and> p2 |\<in>| inPorts n"
begin
  inductive_set hyps_for' :: "'node \<Rightarrow> 'inPort \<Rightarrow> 'outPort set" for n p
    where "hyps n h = Some p \<Longrightarrow> h \<in> hyps_for' n p"

  lemma hyps_for'_subset: "hyps_for' n p \<subseteq> fset (outPorts n)"
    using hyps_correct by (meson hyps_for'.cases notin_fset subsetI)
 
  context includes fset.lifting
  begin
  lift_definition hyps_for  :: "'node \<Rightarrow> 'inPort \<Rightarrow> 'outPort fset" is hyps_for'
    by (meson finite_fset hyps_for'_subset rev_finite_subset)
  lemma hyps_for_simp[simp]: "h |\<in>| hyps_for n p \<longleftrightarrow> hyps n h = Some p"
    by transfer (simp add: hyps_for'.simps)
  lemma hyps_for_simp'[simp]: "h \<in> fset (hyps_for n p) \<longleftrightarrow> hyps n h = Some p"
    by transfer (simp add: hyps_for'.simps)
  lemma hyps_for_collect: "fset (hyps_for n p) = {h . hyps n h = Some p}"
    by auto
  end
  lemma hyps_for_subset: "hyps_for n p |\<subseteq>| outPorts n"
    using hyps_for'_subset
    by (fastforce simp add: fmember.rep_eq hyps_for.rep_eq simp del: hyps_for_simp hyps_for_simp')
end

locale Labeled_Signature = 
  Port_Graph_Signature_Scoped +
  fixes labelsIn :: "'node \<Rightarrow> 'inPort \<Rightarrow> 'form" 
  fixes labelsOut :: "'node \<Rightarrow> 'outPort \<Rightarrow> 'form" 


locale Port_Graph_Signature_Scoped_Vars =
  Port_Graph_Signature nodes inPorts outPorts +
  Abstract_Formulas freshenLC renameLCs lconsts closed subst subst_lconsts subst_renameLCs anyP
  for nodes :: "'node stream" and inPorts :: "'node \<Rightarrow> 'inPort fset"  and outPorts :: "'node \<Rightarrow> 'outPort fset"
  and  freshenLC :: "nat \<Rightarrow> 'var \<Rightarrow> 'var" 
    and renameLCs :: "('var \<Rightarrow> 'var) \<Rightarrow> 'form \<Rightarrow> 'form" 
    and lconsts :: "'form \<Rightarrow> 'var set" 
    and closed :: "'form \<Rightarrow> bool"
    and subst :: "'subst \<Rightarrow> 'form \<Rightarrow> 'form" 
    and subst_lconsts :: "'subst \<Rightarrow> 'var set" 
    and subst_renameLCs :: "('var \<Rightarrow> 'var) \<Rightarrow> ('subst \<Rightarrow> 'subst)"
    and anyP :: "'form" +

  fixes local_vars :: "'node \<Rightarrow> 'inPort \<Rightarrow> 'var set"

end
