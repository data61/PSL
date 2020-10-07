theory Incredible_Propositional_Tasks
imports
  Incredible_Completeness
  Incredible_Propositional
begin

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

subsubsection \<open>Task 1.1\<close>

text \<open>This is the very first task of the Incredible Proof Machine: @{term "A \<longrightarrow> A"}\<close>

abbreviation A :: "(string,prop_funs) pform"
  where "A \<equiv> Fun (Const ''A'') []"

text \<open>First the task is defined as an @{term Abstract_Task}.\<close>

interpretation task1_1: Abstract_Task
  "curry (SOME f. bij f):: nat \<Rightarrow> string \<Rightarrow> string"
  "\<lambda>_. id"
  "\<lambda>_. {}"
  "closed :: (string, prop_funs) pform \<Rightarrow> bool"
  subst
  "\<lambda>_. {}"
  "\<lambda>_. id"
  "Var undefined"
  antecedent
  consequent
  prop_rules
  "[A]"
  "[A]"
by unfold_locales simp

text \<open>Then we show, that this task has a proof within our formalization of natural deduction
  by giving a concrete proof tree.\<close>

lemma "task1_1.solved"
  unfolding task1_1.solved_def
apply clarsimp
apply (rule_tac x="{|A|}" in exI)
apply clarsimp
apply (rule_tac x="Node ({|A|} \<turnstile> A, Axiom) {||}" in exI)
apply clarsimp
apply (rule conjI)
 apply (rule task1_1.wf)
   apply (solves clarsimp)
  apply clarsimp
  apply (rule task1_1.eff.intros(1))
  apply (solves simp)
 apply (solves clarsimp)
by (auto intro: tfinite.intros)


print_locale Vertex_Graph
interpretation task1_1: Vertex_Graph task1_1.nodes task1_1.inPorts task1_1.outPorts "{|0::nat,1|}"
  "undefined(0 := Assumption A, 1 := Conclusion A)"
.

print_locale Pre_Port_Graph
interpretation task1_1: Pre_Port_Graph task1_1.nodes task1_1.inPorts task1_1.outPorts "{|0::nat,1|}"
  "undefined(0 := Assumption A, 1 := Conclusion A)"
  "{((0,Reg A),(1,plain_ant A))}"
.

print_locale Instantiation
interpretation task1_1: Instantiation
  task1_1.inPorts
  task1_1.outPorts
  "undefined(0 := Assumption A, 1 := Conclusion A)"
  task1_1.hyps
  task1_1.nodes
  "{((0,Reg A),(1,plain_ant A))}"
  "{|0::nat,1|}"
  task1_1.labelsIn
  task1_1.labelsOut
  "curry (SOME f. bij f):: nat \<Rightarrow> string \<Rightarrow> string"
  "\<lambda>_. id"
  "\<lambda>_. {}"
  "closed :: (string, prop_funs) pform \<Rightarrow> bool"
  subst
  "\<lambda>_. {}"
  "\<lambda>_. id"
  "Var undefined"
  "id"
  "undefined"
by unfold_locales simp

declare One_nat_def [simp del]

lemma path_one_edge[simp]:
  "task1_1.path v1 v2 pth \<longleftrightarrow>
    (v1 = 0 \<and> v2 = 1 \<and> pth = [((0,Reg A),(1,plain_ant A))] \<or>
    pth = [] \<and> v1 = v2)"
  apply (cases pth)
  apply (auto simp add: task1_1.path_cons_simp')
  apply (rename_tac list, case_tac list, auto simp add: task1_1.path_cons_simp')+
  done

text \<open>Finally we can also show that there is a proof graph for this task.\<close>

interpretation Tasked_Proof_Graph
  "curry (SOME f. bij f):: nat \<Rightarrow> string \<Rightarrow> string"
  "\<lambda>_. id"
  "\<lambda>_. {}"
  "closed :: (string, prop_funs) pform \<Rightarrow> bool"
  subst
  "\<lambda>_. {}"
  "\<lambda>_. id"
  "Var undefined"
  antecedent
  consequent
  prop_rules
  "[A]"
  "[A]"
  "{|0::nat,1|}"
  "undefined(0 := Assumption A, 1 := Conclusion A)"
  "{((0,Reg A),(1,plain_ant A))}"
  "id"
  "undefined"
apply unfold_locales
        apply (solves simp)
       apply (solves clarsimp)
      apply (solves clarsimp)
     apply (solves clarsimp)
    apply (solves fastforce)
   apply (solves fastforce)
  apply (solves \<open>clarsimp simp add: task1_1.labelAtOut_def task1_1.labelAtIn_def\<close>)
 apply (solves clarsimp)
apply (solves clarsimp)
done

subsubsection \<open>Task 2.11\<close>

text \<open>This is a slightly more interesting task as it involves both our connectives: @{term "P \<and> Q \<longrightarrow> R \<Longrightarrow> P \<longrightarrow> (Q \<longrightarrow> R)"}\<close>

abbreviation B :: "(string,prop_funs) pform"
  where "B \<equiv> Fun (Const ''B'') []"
abbreviation C :: "(string,prop_funs) pform"
  where "C \<equiv> Fun (Const ''C'') []"

interpretation task2_11: Abstract_Task
  "curry (SOME f. bij f):: nat \<Rightarrow> string \<Rightarrow> string"
  "\<lambda>_. id"
  "\<lambda>_. {}"
  "closed :: (string, prop_funs) pform \<Rightarrow> bool"
  subst
  "\<lambda>_. {}"
  "\<lambda>_. id"
  "Var undefined"
  antecedent
  consequent
  prop_rules
  "[Fun imp [Fun and [A,B],C]]"
  "[Fun imp [A,Fun imp [B,C]]]"
by unfold_locales simp_all

abbreviation "n_andI \<equiv> task2_11.n_rules !! 0"
abbreviation "n_andE1 \<equiv> task2_11.n_rules !! 1"
abbreviation "n_andE2 \<equiv> task2_11.n_rules !! 2"
abbreviation "n_impI \<equiv> task2_11.n_rules !! 3"
abbreviation "n_impE \<equiv> task2_11.n_rules !! 4"

lemma n_andI [simp]: "n_andI = (andI, Fun and [X,Y])"
  unfolding task2_11.n_rules_def by (simp add: prop_rules_def)
lemma n_andE1 [simp]: "n_andE1 = (andE, X)"
  unfolding task2_11.n_rules_def One_nat_def by (simp add: prop_rules_def)
lemma n_andE2 [simp]: "n_andE2 = (andE, Y)"
  unfolding task2_11.n_rules_def numeral_2_eq_2 by (simp add: prop_rules_def)
lemma n_impI [simp]: "n_impI = (impI, Fun imp [X,Y])"
  unfolding task2_11.n_rules_def numeral_3_eq_3 by (simp add: prop_rules_def)
lemma n_impE [simp]: "n_impE = (impE, Y)"
proof -
  have "n_impE = task2_11.n_rules !! Suc 3" by simp
  also have "... = (impE, Y)"
  unfolding task2_11.n_rules_def numeral_3_eq_3 by (simp add: prop_rules_def)
  finally show ?thesis .
qed


lemma subst_Var_eq_id [simp]: "subst Var = id"
  by (rule ext) (induct_tac x; auto simp: map_idI)

lemma xy_update: "f = undefined(''X'' := x, ''Y'' := y) \<Longrightarrow> x = f ''X'' \<and> y = f ''Y''" by force
lemma y_update: "f = undefined(''Y'':=y) \<Longrightarrow> y = f ''Y''" by force

declare snth.simps(1) [simp del]

text \<open>By interpreting @{term Solved_Task} we show that there is a proof tree for the task.
  We get the existence of the proof graph for free by using the completeness theorem.\<close>

interpretation task2_11: Solved_Task
  "curry (SOME f. bij f):: nat \<Rightarrow> string \<Rightarrow> string"
  "\<lambda>_. id"
  "\<lambda>_. {}"
  "closed :: (string, prop_funs) pform \<Rightarrow> bool"
  subst
  "\<lambda>_. {}"
  "\<lambda>_. id"
  "Var undefined"
  antecedent
  consequent
  prop_rules
  "[Fun imp [Fun and [A,B],C]]"
  "[Fun imp [A,Fun imp [B,C]]]"
apply unfold_locales
  unfolding task2_11.solved_def
apply clarsimp
apply (rule_tac x="{|Fun imp [Fun and [A,B],C]|}" in exI)
apply clarsimp
\<comment> \<open>The actual proof tree for this task.\<close>
apply (rule_tac x="Node ({|Fun imp [Fun and [A, B], C]|} \<turnstile> Fun imp [A, Fun imp [B, C]],NatRule n_impI)
  {|Node ({|Fun imp [Fun and [A, B], C], A|} \<turnstile> Fun imp [B,C],NatRule n_impI)
    {|Node ({|Fun imp [Fun and [A, B], C], A, B|} \<turnstile> C,NatRule n_impE)
      {|Node ({|Fun imp [Fun and [A, B], C], A, B|} \<turnstile> Fun imp [Fun and [A,B], C],Axiom) {||},
        Node ({|Fun imp [Fun and [A, B], C], A, B|} \<turnstile> Fun and [A,B],NatRule n_andI) 
          {|Node ({|Fun imp [Fun and [A, B], C], A, B|} \<turnstile> A,Axiom) {||},
            Node ({|Fun imp [Fun and [A, B], C], A, B|} \<turnstile> B,Axiom) {||}
          |}
      |}
    |}
  |}" in exI)
apply clarsimp
apply (rule conjI)

 apply (rule task1_1.wf)
   apply (solves \<open>clarsimp; metis n_impI snth_smap snth_sset\<close>)
  apply clarsimp
  apply (rule task1_1.eff_NatRuleI [unfolded propositional.freshen_def, simplified]) apply simp_all[4]
    apply (rule task2_11.natEff_InstI)
      apply (solves simp)
     apply (solves simp)
    apply (solves simp)
   apply (intro conjI; simp; rule xy_update)
   apply (solves simp)
  apply (solves \<open>fastforce simp: propositional.f_antecedent_def\<close>)
 apply clarsimp

 apply (rule task1_1.wf)
   apply (solves \<open>clarsimp; metis n_impI snth_smap snth_sset\<close>)
  apply clarsimp
  apply (rule task1_1.eff_NatRuleI [unfolded propositional.freshen_def, simplified]) apply simp_all[4]
    apply (rule task2_11.natEff_InstI)
      apply (solves simp)
     apply (solves simp)
    apply (solves simp)
   apply (intro conjI; simp; rule xy_update)
   apply (solves simp)
  apply (solves \<open>fastforce simp: propositional.f_antecedent_def\<close>)
 apply clarsimp

 apply (rule task1_1.wf)
   apply (solves \<open>clarsimp; metis n_impE snth_smap snth_sset\<close>)
  apply clarsimp
  apply (rule task1_1.eff_NatRuleI [unfolded propositional.freshen_def, simplified, where s="undefined(''Y'':=C,''X'':=Fun and [A,B])"]) apply simp_all[4]
    apply (rule task2_11.natEff_InstI)
      apply (solves simp)
     apply (solves simp)
    apply (solves simp)
   apply (solves \<open>intro conjI; simp\<close>)
  apply (solves \<open>simp add: propositional.f_antecedent_def\<close>)
 apply (erule disjE)

  apply (auto intro: task1_1.wf intro!: task1_1.eff.intros(1))[1]

 apply (rule task1_1.wf)
   apply (solves \<open>clarsimp; metis n_andI snth_smap snth_sset\<close>)
  apply clarsimp
  apply (rule task1_1.eff_NatRuleI [unfolded propositional.freshen_def, simplified]) apply simp_all[4]
    apply (rule task2_11.natEff_InstI)
      apply (solves simp)
     apply (solves simp)
    apply (solves simp)
   apply (intro conjI; simp; rule xy_update)
   apply (solves simp)
  apply (solves \<open>simp add: propositional.f_antecedent_def\<close>)
 apply clarsimp

 apply (erule disjE)
  apply (solves \<open>rule task1_1.wf; auto intro: task1_1.eff.intros(1)\<close>)
 apply (solves \<open>rule task1_1.wf; auto intro: task1_1.eff.intros(1)\<close>)
  
by (rule tfinite.intros; auto)+


interpretation Tasked_Proof_Graph
  "curry (SOME f. bij f):: nat \<Rightarrow> string \<Rightarrow> string"
  "\<lambda>_. id"
  "\<lambda>_. {}"
  "closed :: (string, prop_funs) pform \<Rightarrow> bool"
  subst
  "\<lambda>_. {}"
  "\<lambda>_. id"
  "Var undefined"
  antecedent
  consequent
  prop_rules
  "[Fun imp [Fun and [A,B],C]]"
  "[Fun imp [A,Fun imp [B,C]]]"
  task2_11.vertices 
  task2_11.nodeOf 
  task2_11.edges
  task2_11.vidx
  task2_11.inst
by unfold_locales

end

end
