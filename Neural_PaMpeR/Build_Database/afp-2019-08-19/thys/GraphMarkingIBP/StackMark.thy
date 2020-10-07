section \<open>Marking Using a Stack\<close>

theory StackMark
imports SetMark DataRefinementIBP.DataRefinement
begin

text\<open>
In this theory we refine the set marking diagram to a diagram in which the
set is replaced by a list (stack). Iniatially the list contains the root element
and as long as the list is nonempty and the top of the list has an unmarked
successor $y$, then $y$ is added to the top of the list. If the top does not
have unmarked sucessors, it is removed from the list. The diagram terminates when
the list is empty.

The data refinement relation of the two diagrams is true if the list
has distinct elements and the elements of the list and the set are the same.
\<close>

subsection \<open>Transitions\<close>

definition (in graph)
  "Q1'_a \<equiv> [:\<lambda> (stk::('node list), mrk::('node set)) . {(stk'::('node list), mrk') . 
             root = nil \<and> stk' = [] \<and> mrk' = mrk}:]"

definition (in graph)
  "Q2'_a \<equiv> [:\<lambda> (stk::('node list), mrk::('node set)) . {(stk', mrk') . 
         root \<noteq> nil \<and> stk' = [root] \<and> mrk' = mrk \<union> {root}}:]"

definition (in graph)
  "Q3'_a \<equiv> [:\<lambda> (stk, mrk) . {(stk', mrk') .  stk \<noteq> [] \<and> (\<exists> y . (hd stk, y) \<in> next \<and> 
         y \<notin> mrk \<and> stk' = y # stk \<and> mrk' = mrk \<union> {y})}:]"

definition (in graph)
  "Q4'_a \<equiv> [:\<lambda> (stk, mrk) . {(stk', mrk') . stk \<noteq> [] \<and> 
        (\<forall> y . (hd stk, y) \<in> next \<longrightarrow> y \<in> mrk) \<and> stk' = tl stk \<and> mrk' = mrk}:]"

definition
  "Q5'_a \<equiv> [:\<lambda> (stk, mrk) . {(stk', mrk') . stk = [] \<and> mrk' = mrk}:]"

subsection \<open>Invariants\<close>

definition
  "Init' \<equiv> UNIV"

definition
  "Loop' \<equiv> { (stk, mrk) . distinct stk}"

definition
  "Final' \<equiv> UNIV"

definition [simp]:
  "StackMarkInv i = (case i of
      I.init  \<Rightarrow> Init' |
      I.loop  \<Rightarrow> Loop' |
      I.final \<Rightarrow> Final')"

subsection \<open>Data refinement relations\<close>

definition
  "R1_a \<equiv> {: stk, mrk \<leadsto> X, mrk' . mrk' = mrk :}"

definition
  "R2_a \<equiv> {: stk, mrk \<leadsto> X, mrk' . X = set stk \<and> (stk, mrk) \<in> Loop' \<and> mrk' = mrk :}"

lemma [simp]: "R1_a \<in> Apply.Disjunctive"
       by (simp add: R1_a_def)

lemma [simp]: "R2_a \<in> Apply.Disjunctive" by (simp add: R2_a_def)

definition [simp]:
  "R_a i = (case i of
      I.init  \<Rightarrow> R1_a |
      I.loop  \<Rightarrow> R2_a |
      I.final \<Rightarrow> R1_a)"

lemma [simp]: "Disjunctive_fun R_a" by (simp add: Disjunctive_fun_def)

definition
  "angelic_fun r = (\<lambda> i . {:r i:})"

definition (in graph)
  "StackMark_a = (\<lambda> (i, j) . (case (i, j) of
      (I.init, I.loop)  \<Rightarrow> Q1'_a \<sqinter> Q2'_a |
      (I.loop, I.loop)  \<Rightarrow> Q3'_a \<sqinter> Q4'_a |
      (I.loop, I.final) \<Rightarrow> Q5'_a |
       _ \<Rightarrow> \<top>))"

subsection \<open>Data refinement of the transitions\<close>

theorem (in graph) init_nil [simp]:
  "DataRefinement ({.Init.} o Q1_a) R1_a R2_a Q1'_a"
   by (simp add: data_refinement_hoare hoare_demonic Q1'_a_def Init_def 
     Loop'_def R1_a_def R2_a_def Q1_a_def angelic_def subset_eq)

theorem (in graph) init_root [simp]:
  "DataRefinement ({.Init.} o Q2_a) R1_a R2_a Q2'_a"
   by (simp add: data_refinement_hoare hoare_demonic Q2'_a_def Init_def 
     Loop'_def R1_a_def R2_a_def Q2_a_def angelic_def subset_eq)
   
theorem (in graph) step1 [simp]:
  "DataRefinement ({.Loop.} o Q3_a) R2_a R2_a Q3'_a"
  apply (simp add: data_refinement_hoare hoare_demonic Loop_def 
    Loop'_def R2_a_def Q3_a_def Q3'_a_def angelic_def subset_eq)
  apply (simp add: simp_eq_emptyset)
  by (metis List.set_simps(2) hd_in_set distinct.simps(2))

theorem (in graph) step2 [simp]:
  "DataRefinement ({.Loop.} o Q4_a) R2_a R2_a Q4'_a"
  apply (simp add: data_refinement_hoare hoare_demonic Loop_def 
    Loop'_def R2_a_def Q4_a_def Q4'_a_def angelic_def subset_eq)
  apply (simp add: simp_eq_emptyset)
  apply clarify
  apply (case_tac a)
  by auto

theorem (in graph) final [simp]:
  "DataRefinement ({.Loop.} o Q5_a)  R2_a R1_a Q5'_a"
  apply (simp add: data_refinement_hoare hoare_demonic Loop_def 
    Loop'_def R2_a_def R1_a_def Q5_a_def Q5'_a_def angelic_def subset_eq)
  by (simp add: simp_eq_emptyset)

subsection \<open>Diagram data refinement\<close>

lemma assert_comp_choice: "{.p.} o (S \<sqinter> T) = ({.p.} o S) \<sqinter> ({.p.} o T)"
  apply (rule antisym)
  apply (simp_all add: fun_eq_iff assert_def le_fun_def inf_fun_def inf_assoc)
  apply safe
  apply (rule_tac y = "S x \<sqinter> T x" in order_trans)
  apply (rule inf_le2)
  apply simp
  apply (rule_tac y = "S x \<sqinter> T x" in order_trans)
  apply (rule inf_le2)
  apply simp
  apply (rule_tac y = "S x \<sqinter> (p \<sqinter> T x)" in order_trans)
  apply (rule inf_le2)
  apply simp
  apply (rule_tac y = "S x \<sqinter> (p \<sqinter> T x)" in order_trans)
  apply (rule inf_le2)
  apply (rule_tac y = "p \<sqinter> T x" in order_trans)
  apply (rule inf_le2)
  by simp

theorem (in graph) StackMark_DataRefinement [simp]:
 "DgrDataRefinement2 SetMarkInv SetMark R_a StackMark_a"
  by (simp add: DgrDataRefinement2_def  StackMark_a_def SetMark_def demonic_sup_inf 
    SetMarkInv_def data_refinement_choice2 assert_comp_choice)

subsection \<open>Diagram correctness\<close>

theorem (in graph) StackMark_correct:
  "Hoare_dgr (R_a .. SetMarkInv) StackMark_a ((R_a .. SetMarkInv) \<sqinter> (- grd (step (StackMark_a))))"
  apply (rule_tac D = "SetMark" in Diagram_DataRefinement2)
  apply auto
  by (rule SetMark_correct1)

end
