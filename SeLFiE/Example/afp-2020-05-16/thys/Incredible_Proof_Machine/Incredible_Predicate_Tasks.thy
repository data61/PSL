theory Incredible_Predicate_Tasks
imports
  Incredible_Completeness
  Incredible_Predicate
  "HOL-Eisbach.Eisbach"
begin

declare One_nat_def [simp del]

context ND_Rules_Inst begin
lemma eff_NatRuleI:
  "nat_rule rule c ants
    \<Longrightarrow> entail = (\<Gamma> \<turnstile> subst s (freshen a c))
    \<Longrightarrow> hyps = ((\<lambda>ant. ((\<lambda>p. subst s (freshen a p)) |`| a_hyps ant |\<union>| \<Gamma> \<turnstile> subst s (freshen a (a_conc ant)))) |`| ants)
    \<Longrightarrow> (\<And> ant f. ant |\<in>| ants \<Longrightarrow> f |\<in>| \<Gamma> \<Longrightarrow> freshenLC a ` (a_fresh ant) \<inter> lconsts f = {})
    \<Longrightarrow> (\<And> ant. ant |\<in>| ants \<Longrightarrow> freshenLC a ` (a_fresh ant) \<inter> subst_lconsts s = {})
    \<Longrightarrow> eff (NatRule rule) entail hyps"
  by (drule eff.intros(2)) simp_all
end

context Abstract_Task begin
lemma  natEff_InstI:
  "rule = (r,c)
  \<Longrightarrow> c \<in> set (consequent r)
  \<Longrightarrow> antec = f_antecedent r
  \<Longrightarrow> natEff_Inst rule c antec"
  by (metis natEff_Inst.intros)
end

context begin

text \<open>A typical task with local constants:: \<open>\<forall>x. Q x \<longrightarrow> Q x\<close>\<close>

text \<open>First the task is defined as an @{term Abstract_Task}.\<close>

interpretation task: Abstract_Task
  "curry to_nat :: nat \<Rightarrow> var \<Rightarrow> var"
  map_lc
  lc
  "closed"
  subst
  lc_subst
  map_lc_subst
  "Var 0 []"
  antecedent
  consequent
  prop_rules
  "[]"
  "[ForallX (imp (Q x) (Q x))]"
by unfold_locales auto

text \<open>Then we show, that this task has a proof within our formalization of natural deduction
  by giving a concrete proof tree.\<close>

abbreviation lx :: "nat" where "lx \<equiv> to_nat (1::nat,0::nat)"

abbreviation base_tree :: "((form fset \<times> form) \<times> (prop_rule \<times> form) NatRule) tree" where
  "base_tree \<equiv> Node ({|Q (LC lx)|} \<turnstile> Q (LC lx), Axiom) {||}"

abbreviation imp_tree :: "((form fset \<times> form) \<times> (prop_rule \<times> form) NatRule) tree" where
  "imp_tree \<equiv> Node ({||} \<turnstile> imp (Q (LC lx)) (Q (LC lx)), NatRule (impI, imp X Y)) {|base_tree|}"

abbreviation solution_tree :: "((form fset \<times> form) \<times> (prop_rule \<times> form) NatRule) tree" where
  "solution_tree \<equiv> Node ({||} \<turnstile> ForallX (imp (Q x) (Q x)), NatRule (allI, ForallX (P x))) {|imp_tree|}"

abbreviation s1 where "s1 \<equiv> [(12, ([9], imp (Q x) (Q x)))] "
abbreviation s2 where "s2 \<equiv> [(10, ([], Q (LC lx))), (11, ([], Q (LC lx)))] "

lemma fv_subst_s1[simp]: "fv_subst s1 = {}"
  by (simp add: fv_subst_def)

lemma subst1_simps[simp]:
  "subst s1 (P (LC n)) = imp (Q (LC n)) (Q (LC n))"
  "subst s1 (ForallX (P x)) = ForallX (imp (Q x) (Q x))"
  by simp_all

lemma subst2_simps[simp]:
    "subst s2 X = Q (LC lx)" 
    "subst s2 Y = Q (LC lx)"
    "subst s2 (imp X Y) = imp (subst s2 X) (subst s2 Y)"
  by simp_all

lemma substI1: "ForallX (imp (Q x) (Q x)) = subst s1 (predicate.freshen 1 (ForallX (P x)))"
  by (auto simp add: predicate.freshen_def Let_def)

lemma substI2: "imp (Q (LC lx)) (Q (LC lx)) = subst s2 (predicate.freshen 2 (imp X Y))"
  by (auto simp add: predicate.freshen_def Let_def)

declare subst.simps[simp del]

lemma "task.solved"
  unfolding task.solved_def
apply clarsimp
apply (rule_tac x="{||}" in exI)
apply clarsimp
apply (rule_tac x="solution_tree" in exI)
apply clarsimp
apply (rule conjI)

 apply (rule task.wf)
   apply (solves \<open>(auto simp add: stream.set_map task.n_rules_def)[1]\<close>)
  apply clarsimp
  apply (rule task.eff_NatRuleI)
      apply (solves \<open>rule task.natEff_Inst.intros;simp\<close>)
     apply clarsimp     
     apply (rule conjI)
      apply (solves \<open>simp\<close>)
     apply (solves \<open>rule substI1\<close>)
    apply (simp add: predicate.f_antecedent_def predicate.freshen_def)
    apply (subst antecedent.sel(2))
    apply (solves \<open>simp\<close>)
   apply (solves \<open>simp\<close>)
  apply (solves \<open>simp\<close>)
 apply simp

 apply (rule task.wf)
   apply (solves \<open>(auto simp add: stream.set_map task.n_rules_def)[1]\<close>)
  apply clarsimp
  apply (rule task.eff_NatRuleI)
      apply (solves \<open>rule task.natEff_Inst.intros; simp\<close>)
     apply clarsimp     
     apply (rule conjI)
      apply (solves \<open>simp\<close>)
     apply (solves \<open>rule substI2\<close>)
    apply (solves \<open>simp add: predicate.f_antecedent_def predicate.freshen_def\<close>)
   apply (solves \<open>simp\<close>)
  apply (solves \<open>simp add: predicate.f_antecedent_def\<close>)
 apply simp

 apply (solves \<open>(auto intro: task.wf intro!: task.eff.intros(1))[1]\<close>)
apply (solves \<open>(rule tfinite.intros, simp)+\<close>)
done

abbreviation vertices where "vertices \<equiv> {|0::nat,1,2 |}"
fun nodeOf  where 
    "nodeOf n = [Conclusion (ForallX (imp (Q x) (Q x))), 
                 Rule allI, 
                 Rule impI] ! n "

fun inst  where 
    "inst n = [[],s1,s2] ! n"


interpretation task: Vertex_Graph task.nodes task.inPorts task.outPorts vertices nodeOf.

abbreviation e1 :: "(nat, form, nat) edge'"
  where "e1 \<equiv> ((1,Reg (ForallX (P x))), (0,plain_ant (ForallX (imp (Q x) (Q x)))))"
abbreviation e2  :: "(nat, form, nat) edge'"
  where "e2 \<equiv> ((2,Reg (imp X Y)), (1,allI_input))"
abbreviation e3  :: "(nat, form, nat) edge'"
  where "e3 \<equiv> ((2,Hyp X (impI_input)), (2,impI_input))"
abbreviation task_edges :: "(nat, form, nat) edge' set" where "task_edges \<equiv> {e1, e2, e3}"


interpretation task: Scoped_Graph task.nodes task.inPorts task.outPorts vertices nodeOf task_edges task.hyps
  by standard (auto simp add: predicate.f_consequent_def predicate.f_antecedent_def)

interpretation task: Instantiation
  task.inPorts
  task.outPorts
  nodeOf
  task.hyps
  task.nodes
  task_edges
  vertices
  task.labelsIn
  task.labelsOut
  "curry to_nat :: nat \<Rightarrow> var \<Rightarrow> var"
  map_lc
  lc
  "closed"
  subst
  lc_subst
  map_lc_subst
  "Var 0 []"
  "id"
  "inst"
by unfold_locales simp

text \<open>Finally we can also show that there is a proof graph for this task.\<close>

interpretation Well_Scoped_Graph
  task.nodes
  task.inPorts
  task.outPorts
  vertices
  nodeOf
  task_edges
  task.hyps
by standard (auto split: if_splits)

lemma no_path_01[simp]: "task.path 0 v pth \<longleftrightarrow> (pth = [] \<and> v = 0)"
  by (cases pth) (auto simp add: task.path_cons_simp)
lemma no_path_12[simp]: "\<not> task.path 1 2 pth"
  by (cases pth) (auto simp add: task.path_cons_simp)

interpretation Acyclic_Graph
  task.nodes
  task.inPorts
  task.outPorts
  vertices
  nodeOf
  task_edges
  task.hyps
proof
  fix v pth 
  assume "task.path v v pth" and "task.hyps_free pth"
  thus "pth = []"
    by (cases pth) (auto simp add: task.path_cons_simp predicate.f_antecedent_def)
qed

interpretation Saturated_Graph
  task.nodes
  task.inPorts
  task.outPorts
  vertices
  nodeOf
  task_edges
by standard
   (auto simp add: predicate.f_consequent_def predicate.f_antecedent_def) 

interpretation Pruned_Port_Graph
  task.nodes
  task.inPorts
  task.outPorts
  vertices
  nodeOf
  task_edges
proof
  fix v
  assume "v |\<in>| vertices"
  hence "\<exists> pth. task.path v 0 pth"
    apply auto
    apply (rule exI[where x = "[e1]"], auto simp add: task.path_cons_simp)
    apply (rule exI[where x = "[e2,e1]"], auto simp add: task.path_cons_simp)
    done
  moreover
  have "task.terminal_vertex 0" by auto
  ultimately
  show "\<exists>pth v'. task.path v v' pth \<and> task.terminal_vertex v'" by blast
qed

interpretation Well_Shaped_Graph
  task.nodes
  task.inPorts
  task.outPorts
  vertices
  nodeOf task_edges
  task.hyps
..

interpretation Solution
  task.inPorts
  task.outPorts
  nodeOf
  task.hyps
  task.nodes
  vertices
  task.labelsIn
  task.labelsOut
  "curry to_nat :: nat \<Rightarrow> var \<Rightarrow> var"
  map_lc
  lc
  "closed"
  subst
  lc_subst
  map_lc_subst
  "Var 0 []"
  id
  inst
  task_edges
by standard
   (auto simp add: task.labelAtOut_def task.labelAtIn_def predicate.freshen_def, subst antecedent.sel, simp)

interpretation Proof_Graph
  task.nodes
  task.inPorts
  task.outPorts
  vertices
  nodeOf
  task_edges
  task.hyps
  task.labelsIn
  task.labelsOut
  "curry to_nat :: nat \<Rightarrow> var \<Rightarrow> var"
  map_lc
  lc
  "closed"
  subst
  lc_subst
  map_lc_subst
  "Var 0 []"
  id
  inst
..

lemma path_20:
  assumes "task.path 2 0 pth"
  shows "(1, allI_input) \<in> snd ` set pth"
proof-
  { fix v
    assume "task.path v 0 pth"
    hence "v = 0 \<or> v = 1 \<or> (1, allI_input) \<in> snd ` set pth"
    by (induction v "0::nat" pth rule: task.path.induct) auto
  }
  from this[OF assms]
  show ?thesis by auto
qed

lemma scope_21: "2 \<in> task.scope (1, allI_input)"
  by (auto intro!: task.scope.intros elim: path_20 simp add: task.outPortsRule_def predicate.f_antecedent_def predicate.f_consequent_def)

interpretation Scoped_Proof_Graph
  "curry to_nat :: nat \<Rightarrow> var \<Rightarrow> var"
  map_lc
  lc
  "closed"
  subst
  lc_subst
  map_lc_subst
  "Var 0 []"
  task.inPorts
  task.outPorts
  nodeOf
  task.hyps
  task.nodes
  vertices
  task.labelsIn
  task.labelsOut
  id
  inst
  task_edges
  task.local_vars
by standard (auto simp add: predicate.f_antecedent_def scope_21)

interpretation Tasked_Proof_Graph
  "curry to_nat :: nat \<Rightarrow> var \<Rightarrow> var"
  map_lc
  lc
  "closed"
  subst
  lc_subst
  map_lc_subst
  "Var 0 []"
  antecedent
  consequent
  prop_rules
  "[]"
  "[ForallX (imp (Q x) (Q x))]"
  vertices
  nodeOf
  task_edges
  id
  inst
by unfold_locales auto

end

end
