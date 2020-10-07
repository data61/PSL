theory Abstract_Rules_To_Incredible
imports
  Main 
  "HOL-Library.FSet"
  "HOL-Library.Stream"
  Incredible_Deduction
  Abstract_Rules
begin

text \<open>In this theory, the abstract rules given in @{theory Incredible_Proof_Machine.Abstract_Rules} are used to
create a proper signature.\<close>

text \<open>Besides the rules given there, we have nodes for assumptions, conclusions, and the helper
block.\<close>

datatype ('form, 'rule) graph_node = Assumption 'form | Conclusion 'form | Rule 'rule | Helper

type_synonym ('form, 'var) in_port = "('form, 'var) antecedent"
type_synonym 'form reg_out_port = "'form"
type_synonym 'form hyp = "'form"
datatype ('form, 'var) out_port = Reg "'form reg_out_port" | Hyp "'form hyp" "('form, 'var) in_port"
type_synonym ('v, 'form, 'var) edge' = "(('v \<times> ('form, 'var) out_port) \<times> ('v \<times> ('form, 'var) in_port))"

context Abstract_Task
begin
  definition nodes :: "('form, 'rule) graph_node stream" where
    "nodes = Helper ## shift (map Assumption assumptions) (shift (map Conclusion conclusions) (smap Rule rules))"

  lemma Helper_in_nodes[simp]:
    "Helper \<in> sset nodes" by (simp add: nodes_def)
  lemma Assumption_in_nodes[simp]:
    "Assumption a \<in> sset nodes \<longleftrightarrow> a \<in> set assumptions" by (auto simp add: nodes_def stream.set_map)
  lemma Conclusion_in_nodes[simp]:
    "Conclusion c \<in> sset nodes \<longleftrightarrow> c \<in> set conclusions" by (auto simp add: nodes_def stream.set_map)
  lemma Rule_in_nodes[simp]:
    "Rule r \<in> sset nodes \<longleftrightarrow> r \<in> sset rules" by (auto simp add: nodes_def stream.set_map)

  fun inPorts' :: "('form, 'rule) graph_node \<Rightarrow> ('form, 'var) in_port list"  where
    "inPorts' (Rule r) = antecedent r"
   |"inPorts' (Assumption r) = []"
   |"inPorts' (Conclusion r) = [ plain_ant r ]"
   |"inPorts' Helper  = [ plain_ant anyP ]"

  fun inPorts :: "('form, 'rule) graph_node \<Rightarrow> ('form, 'var) in_port fset"  where
    "inPorts (Rule r) = f_antecedent r"
   |"inPorts (Assumption r) = {||}"
   |"inPorts (Conclusion r) = {| plain_ant r |}"
   |"inPorts Helper  = {| plain_ant anyP |}"

  lemma inPorts_fset_of:
    "inPorts n = fset_from_list (inPorts' n)"
    by (cases n rule: inPorts.cases) (auto simp: fmember.rep_eq f_antecedent_def)

  definition outPortsRule where
    "outPortsRule r = ffUnion ((\<lambda> a. (\<lambda> h. Hyp h a) |`| a_hyps a) |`| f_antecedent r) |\<union>| Reg |`| f_consequent r"

  lemma Reg_in_outPortsRule[simp]:  "Reg c |\<in>| outPortsRule r \<longleftrightarrow> c |\<in>| f_consequent r"
    by (auto simp add: outPortsRule_def fmember.rep_eq ffUnion.rep_eq)
  lemma Hyp_in_outPortsRule[simp]:  "Hyp h c |\<in>| outPortsRule r \<longleftrightarrow> c |\<in>| f_antecedent r \<and> h |\<in>| a_hyps c"
    by (auto simp add: outPortsRule_def fmember.rep_eq ffUnion.rep_eq)

  fun outPorts where
    "outPorts (Rule r) = outPortsRule r"
   |"outPorts (Assumption r) = {|Reg r|}"
   |"outPorts (Conclusion r) = {||}"
   |"outPorts Helper  = {| Reg anyP |}"

  fun labelsIn where
    "labelsIn _ p = a_conc p"

  fun labelsOut where
    "labelsOut _ (Reg p) = p"
   | "labelsOut _ (Hyp h c) = h"

  fun hyps where 
     "hyps (Rule r) (Hyp h a) = (if a |\<in>| f_antecedent r \<and> h |\<in>| a_hyps a then Some a else None)"
   | "hyps _ _ = None"

  fun local_vars :: "('form, 'rule) graph_node \<Rightarrow> ('form, 'var) in_port \<Rightarrow> 'var set"  where
     "local_vars _ a = a_fresh a"


  sublocale Labeled_Signature nodes inPorts outPorts hyps labelsIn labelsOut
  proof(standard,goal_cases)
    case (1 n p1 p2)
    thus ?case by(induction n p1 rule: hyps.induct) (auto  split: if_splits)
  qed

  lemma hyps_for_conclusion[simp]: "hyps_for (Conclusion n) p = {||}"
    using hyps_for_subset by auto
  lemma hyps_for_Helper[simp]: "hyps_for Helper p = {||}"
    using hyps_for_subset by auto
  lemma hyps_for_Rule[simp]: "ip |\<in>| f_antecedent r \<Longrightarrow> hyps_for (Rule r) ip = (\<lambda> h. Hyp h ip) |`| a_hyps ip"
    by (auto elim!: hyps.elims split: if_splits)
end

text \<open>Finally, a given proof graph solves the task at hand if all the given conclusions are present
as conclusion blocks in the graph.\<close>

locale Tasked_Proof_Graph =
  Abstract_Task freshenLC renameLCs lconsts closed subst subst_lconsts subst_renameLCs anyP  antecedent consequent rules assumptions conclusions  +
  Scoped_Proof_Graph freshenLC renameLCs lconsts closed subst subst_lconsts subst_renameLCs anyP  inPorts outPorts nodeOf hyps nodes vertices labelsIn labelsOut vidx inst edges local_vars
   for freshenLC :: "nat \<Rightarrow> 'var \<Rightarrow> 'var" 
    and renameLCs :: "('var \<Rightarrow> 'var) \<Rightarrow> 'form \<Rightarrow> 'form" 
    and lconsts :: "'form \<Rightarrow> 'var set" 
    and closed :: "'form \<Rightarrow> bool"
    and subst :: "'subst \<Rightarrow> 'form \<Rightarrow> 'form" 
    and subst_lconsts :: "'subst \<Rightarrow> 'var set" 
    and subst_renameLCs :: "('var \<Rightarrow> 'var) \<Rightarrow> ('subst \<Rightarrow> 'subst)"
    and anyP :: "'form"

    and antecedent :: "'rule \<Rightarrow> ('form, 'var) antecedent list" 
    and consequent :: "'rule \<Rightarrow> 'form list" 
    and rules :: "'rule stream" 

    and assumptions :: "'form list" 
    and conclusions :: "'form list" 

    and vertices :: "'vertex fset" 
    and nodeOf :: "'vertex \<Rightarrow> ('form, 'rule) graph_node" 
    and edges :: "('vertex, 'form, 'var) edge' set" 
    and vidx :: "'vertex \<Rightarrow> nat"
    and inst :: "'vertex \<Rightarrow> 'subst"  +
  assumes conclusions_present: "set (map Conclusion conclusions) \<subseteq> nodeOf ` fset vertices"

end
