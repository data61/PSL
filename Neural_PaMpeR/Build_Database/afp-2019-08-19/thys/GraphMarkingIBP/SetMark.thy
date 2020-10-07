
section \<open>Marking Using a Set\<close>

theory SetMark
imports Graph DataRefinementIBP.DataRefinement
begin

text\<open>
We construct in this theory a diagram which computes all reachable nodes
from a given root node in a graph. The graph is defined in the theory
Graph and is given by a relation $next$ on the nodes of the graph.

The diagram has only three ordered situation 
($\mathit{init} > \mathit{loop} > \mathit{final}$). The termination
variant is a pair of a situation and a natural number with the lexicographic
ordering. The idea of this ordering is that we can go from a bigger situation
to a smaller one, however if we stay in the same situation the second
component of the variant must decrease.

The idea of the algorithm is that it starts with a set $X$ containing the
root element and the root is marked. As long as $X$ is not empty, if $x\in X$ 
and $y$ is an unmarked sucessor of $x$ we add $y$ to $X$. If $x\in X$ has
no unmarked sucessors it is removed from $X$. 
The algorithm terminates when $X$ is empty.  
\<close>

datatype I = init | loop | final

declare I.split [split]


instantiation I :: well_founded_transitive
begin

definition
  less_I_def: "i < j \<equiv>  (j = init \<and> (i = loop \<or> i = final)) \<or> (j = loop \<and> i = final)"

definition
  less_eq_I_def:  "(i::I) \<le> (j::I) \<equiv> i = j \<or> i < j"

instance
proof
  fix x y z :: I
  assume "x < y" and "y < z" then  show  "x < z"
    apply (simp add: less_I_def)
    by auto
next
  fix x y :: I
  show  "x \<le> y \<longleftrightarrow> x = y \<or> x < y"
    by (simp add: less_eq_I_def)
next
  fix P fix a::I
  show "P a" when "\<forall>x. (\<forall> y. y < x \<longrightarrow> P y) \<longrightarrow> P x"
    apply (insert that)
    apply (case_tac "P final")
    apply (case_tac "P loop")
    apply (simp_all add: less_I_def)
    by blast
qed (simp)

end


text\<open>
The set $\mathit{path}\ S \ \mathit{mrk}$ contains all reachable nodes from S along paths with
unmarked nodes.
\<close>

lemma trascl_less: "x \<noteq> y \<Longrightarrow> (a, x) \<in> R\<^sup>* \<Longrightarrow> 
    ((a,x) \<in> (R \<inter> (-{y})\<times>(-{y}))\<^sup>* \<or>  (y,x) \<in> R O (R \<inter> (-{y})\<times>(-{y}))\<^sup>* )"
  apply (drule_tac 
    b = x and a = a and r = R and 
    P = "\<lambda> x. (x \<noteq> y \<longrightarrow>((a,x) \<in> (R \<inter> (-{y})\<times>(-{y}))\<^sup>* \<or> (y,x) \<in> R O (R \<inter> (-{y})\<times>(-{y}))\<^sup>* ))"
    in rtrancl_induct)
  apply (auto simp: Compl_insert)
  apply (case_tac "ya = y")
  apply auto
  apply (rule_tac x = a and y = ya and z = z and r = "R \<inter> ((UNIV - {y}) \<times> (UNIV - {y}))" in rtrancl_trans)
  apply auto
  apply (case_tac "za = y")
  apply auto
  apply (drule_tac x = ya and y = za and z = z and r = "(R \<inter> (UNIV - {y}) \<times> (UNIV - {y}))" in rtrancl_trans)
  by auto

lemma (in graph) add_set [simp]: "x \<noteq> y \<Longrightarrow> x \<in> path S mrk \<Longrightarrow> x \<in> path (insert y S) (insert y mrk)"
  apply (simp add: path_def)
  apply clarify
  apply (drule_tac x = x and y = y and a = ya and R = "next \<inter> (- mrk) \<times> (- mrk)" in trascl_less)
  apply simp_all
  apply (case_tac "(ya, x) \<in> (next \<inter> (- mrk) \<times> - mrk \<inter> (- {y}) \<times> - {y})\<^sup>*")
  apply (rule_tac x = xa in exI)
  apply simp_all
  apply (simp add: relcomp_unfold)
  apply (rule_tac x = ya in exI)
  apply simp
  apply (case_tac "(next \<inter> (- mrk) \<times> - mrk \<inter> (- {y}) \<times> - {y}) = (next \<inter> (- insert y mrk) \<times> - insert y mrk)")
  apply simp_all
  apply safe
  apply simp_all
  apply (rule_tac x = y in exI)
  apply simp  
  apply (simp add: relcomp_unfold)
  apply (rule_tac x = yaa in exI)
  apply simp
  apply (case_tac "(next \<inter> (- mrk) \<times> - mrk \<inter> (- {y}) \<times> - {y}) = (next \<inter> (- insert y mrk) \<times> - insert y mrk)")
  apply simp_all
  by auto

lemma (in graph) add_set2: "x \<in> path S mrk \<Longrightarrow> x \<notin> path (insert y S) (insert y mrk) \<Longrightarrow> x = y"
  apply (case_tac "x \<noteq> y")
  apply (frule add_set)
  by simp_all

lemma (in graph) del_stack [simp]: "(\<forall> y . (t, y) \<in> next \<longrightarrow> y \<in> mrk) \<Longrightarrow> x \<notin>  mrk \<Longrightarrow> x \<in> path S mrk \<Longrightarrow> x \<in> path (S - {t}) mrk"
  apply (simp add: path_def)
  apply clarify
  apply (rule_tac x = xa in exI)
  apply (case_tac "x = y")
  apply auto
  apply (drule_tac a = y and b = x and R = "(next \<inter> (- mrk) \<times> - mrk)" in rtranclD)
  apply safe
  apply (drule_tac x = y and y = x in tranclD)
  by auto

lemma (in graph) init_set [simp]: "x \<in> reach root \<Longrightarrow> x \<noteq> root \<Longrightarrow> x \<in> path {root} {root}"
  apply (simp add: reach_def path_def)
  apply (case_tac "root \<noteq> x")
  apply (drule_tac a = root and x = x and y = root and R = "next" in trascl_less)
  apply (simp_all add: Compl_insert)
  apply safe
  apply (drule_tac a = root and b = x and R = "(next \<inter> (UNIV - {root}) \<times> (UNIV - {root}))" in rtranclD)
  apply safe
  apply (drule_tac x = root and y = x in tranclD)
  by auto

lemma (in graph)  init_set2: "x \<in> reach root \<Longrightarrow> x \<notin> path {root} {root} \<Longrightarrow> x = root"
  apply (case_tac "root \<noteq> x")
  apply (drule init_set)
  by simp_all

subsection \<open>Transitions\<close>

definition (in graph)
  "Q1_a \<equiv> [: X, mrk \<leadsto> X', mrk'. (root::'node) = nil \<and> X' = {} \<and> mrk' = mrk :]"

definition (in graph)
  "Q2_a \<equiv> [: X, mrk \<leadsto> X', mrk' . 
       (root::'node) \<noteq> nil \<and> X' = {root::'node} \<and> mrk' = {root::'node} :]"

definition (in graph)
  "Q3_a \<equiv> [: X, mrk \<leadsto> X', mrk' . 
        (\<exists> x \<in> X . \<exists> y . (x, y) \<in> next \<and> y \<notin> mrk \<and> X' = X \<union> {y} \<and> mrk' = mrk \<union> {y}):]"

definition (in graph)
  "Q4_a \<equiv> [: X, mrk \<leadsto> X', mrk' .  
        (\<exists> x \<in> X . (\<forall> y . (x, y) \<in> next \<longrightarrow> y \<in> mrk) \<and> X' = X - {x} \<and> mrk' = mrk):]"

definition (in graph)
  "Q5_a \<equiv> [: X, mrk \<leadsto> X', mrk' . X = {} \<and> mrk = mrk' :]"

subsection \<open>Invariants\<close>

definition (in graph) 
  "Loop \<equiv> { (X, mrk) .
      finite (-mrk) \<and> finite X \<and> X \<subseteq> mrk \<and> 
      mrk \<subseteq> reach root \<and> reach root \<inter> -mrk \<subseteq> path X mrk}"

definition
  "trm \<equiv> \<lambda> (X, mrk) . 2 * card (-mrk) + card X"

definition
  "term_eq t w = {s . t s = w}"
  
definition
  "term_less t w = {s . t s < w}"

lemma union_term_eq [simp]:  "(\<Union> w . term_eq t w) = UNIV"
  apply (simp add: term_eq_def)
  by auto

lemma union_less_term_eq [simp]: "(\<Union>v\<in>{v. v < w}. term_eq t v) = term_less t w"
  apply (simp add: term_eq_def term_less_def)
  by auto

definition (in graph) 
  "Init \<equiv> { (X::('node set), mrk::('node set)) . finite (-mrk) \<and> mrk = {}}"

definition (in graph) 
  "Final \<equiv> { (X::('node set), mrk::('node set)) . mrk = reach root}"

definition (in graph) 
  "SetMarkInv i = (case i of
      I.init  \<Rightarrow> Init |
      I.loop  \<Rightarrow> Loop |
      I.final \<Rightarrow> Final)"

definition (in graph) 
  "SetMarkInvFinal i = (case i of
      I.final  \<Rightarrow> Final |
      _  \<Rightarrow> {})"

definition  (in graph) [simp]:
  "SetMarkInvTerm w i = (case i of
      I.init  \<Rightarrow> Init |
      I.loop  \<Rightarrow> Loop \<inter> {s . trm s = w} |
      I.final \<Rightarrow> Final)"

subsection \<open>Diagram\<close>

definition (in graph) 
  "SetMark \<equiv> \<lambda> (i, j) . (case (i, j) of
      (I.init, I.loop)  \<Rightarrow> Q1_a \<sqinter> Q2_a |
      (I.loop, I.loop)  \<Rightarrow> Q3_a \<sqinter> Q4_a |
      (I.loop, I.final) \<Rightarrow> Q5_a |
       _ \<Rightarrow> top)"

lemma (in graph)  SetMark_dmono [simp]:
  "dmono SetMark"
  apply (unfold dmono_def SetMark_def Q1_a_def Q2_a_def Q3_a_def Q4_a_def Q5_a_def)
  by simp

subsection \<open>Correctness of the transitions\<close>


lemma  (in graph) init_loop_1_a[simp]: "\<Turnstile> Init {| Q1_a |} Loop"
  apply (unfold hoare_demonic Init_def Q1_a_def Loop_def)
  by auto

lemma  (in graph) init_loop_2_a[simp]: "\<Turnstile> Init {| Q2_a |} Loop"
  apply (simp add: hoare_demonic Init_def Q2_a_def Loop_def)
  apply auto
  apply (simp_all add: reach_def)
  apply (rule init_set2)
  by (simp_all add: reach_def)

lemma  (in graph) loop_loop_1_a [simp]: "\<Turnstile> (Loop \<inter>  {s . trm s = w}) {| Q3_a |} (Loop \<inter> {s. trm s < w})"
  apply (simp add: hoare_demonic Q3_a_def Loop_def trm_def)
  apply safe
  apply (simp_all)
  apply (simp_all add: reach_def subset_eq)
  apply safe
  apply (simp_all add: Compl_insert)
  apply (rule rtrancl_into_rtrancl)
  apply (simp_all add: Int_def)
  apply (rule add_set2)
  apply simp_all
  apply (case_tac "card (-b) > 0")
  by auto

 lemma  (in graph) loop_loop_2_a[simp]: "\<Turnstile> (Loop \<inter>  {s . trm s = w}) {| Q4_a |} (Loop \<inter> {s. trm s < w})"
  apply (simp add: hoare_demonic Q4_a_def Loop_def trm_def)
  apply auto
  apply (case_tac "card a > 0")
  by auto

 lemma  (in graph) loop_final_a [simp]: "\<Turnstile> (Loop \<inter> {s . trm s = w}) {| Q5_a |} Final"
  apply (simp add: hoare_demonic Q5_a_def Loop_def Final_def subset_eq Int_def path_def)
  by auto

lemma union_term_w[simp]:  "(\<Union>w. {s. t s = w}) = UNIV"
  by auto

lemma union_less_term_w[simp]: "(\<Union>v\<in>{v. v < w}. {s. t s = v}) = {s . t s < w}"
  by auto

lemma sup_union[simp]: "Sup (range A) i =  (\<Union> w . A w i)"
  by (simp_all add: Sup_fun_def)

lemma forall_simp [simp]: "(\<forall>a b. \<forall>x\<in>A. (a = (t x)) \<longrightarrow> (h x) \<or> b \<noteq> u x) = (\<forall>x\<in> A . h x)"
  by auto

lemma forall_simp2 [simp]: "(\<forall>a b. \<forall>x\<in>A. \<forall>y. (a  = t x y) \<longrightarrow> (h x y) \<longrightarrow> (g x y) \<or> b \<noteq> u x y) = (\<forall>x\<in>A. \<forall>y. h x y \<longrightarrow> g x y)"
  by auto

subsection \<open>Diagram correctness\<close>

text\<open>
The termination ordering for the $\mathit{SetMark}$ diagram is the lexicographic
ordering on pairs $(i,\, n)$ where $i\in I$ and $n\in \mathit{nat}$.
\<close>

interpretation  DiagramTermination "\<lambda> (n::nat) (i :: I) . (i, n)"
  done

theorem (in graph) SetMark_correct:
  "\<Turnstile> SetMarkInv {|pt SetMark|} SetMarkInvFinal"
proof (rule_tac X = "SetMarkInvTerm" in hoare_diagram3)
  show "dmono SetMark" by simp
  show "\<forall>u i j. \<Turnstile> SetMarkInvTerm u i{| SetMark (i, j) |}
    DiagramTermination.SUP_L_P (\<lambda>n i. (i, n)) SetMarkInvTerm (i, u) j"
    by (auto simp add: SUP_L_P_def  less_pair_def less_I_def hoare_choice SetMark_def)
  show "SetMarkInv \<le> Sup (range SetMarkInvTerm)"
    apply (simp add: le_fun_def, safe)
    apply (simp_all add: SetMarkInv_def)
    apply (case_tac x)
    apply auto
    done
  show "Sup (range SetMarkInvTerm) \<sqinter> - grd (step SetMark) \<le> SetMarkInvFinal"
    apply (simp add: le_fun_def inf_fun_def SetMarkInvFinal_def)
    apply safe
    apply simp_all
    apply (drule_tac x="I.loop" in spec)
    apply (simp add: SetMark_def)
    apply (simp add: Q1_a_def Q2_a_def)
    apply (frule_tac x="I.loop" in spec)
    apply (drule_tac x="I.final" in spec)
    apply (simp add: SetMark_def)
    apply (simp add: Q3_a_def Q4_a_def Q5_a_def)
    apply (auto)
    done
qed

theorem (in graph) SetMark_correct1 [simp]:
  "Hoare_dgr SetMarkInv SetMark (SetMarkInv \<sqinter> (- grd (step SetMark)))"
  apply (simp add: Hoare_dgr_def)
  apply (rule_tac x = SetMarkInvTerm in exI)
  apply (subgoal_tac "SetMarkInv = \<Squnion>range SetMarkInvTerm")
  apply simp
  apply safe
  apply (simp_all add: SetMark_def SUP_L_P_def
       less_pair_def less_I_def hoare_choice)
  apply (simp_all add: fun_eq_iff)
  apply safe
  apply (unfold SetMarkInv_def)
  by auto

theorem (in graph) stack_not_nil [simp]:
  "(mrk, S) \<in> Loop \<Longrightarrow> x \<in> S \<Longrightarrow> x \<noteq> nil"
  apply (simp add: Loop_def reach_def)
  by auto

end
