section \<open>Data Refinement of Diagrams\<close>

theory DataRefinement
imports Diagram
begin

text\<open>
Next definition introduces the concept of data refinement of $S1$
to $S2$ using the data abstractions $R$ and $R'$.
\<close>

definition
  DataRefinement :: "('a::type \<Rightarrow> 'b::type)
     \<Rightarrow> ('b::type \<Rightarrow> 'c::ord) \<Rightarrow> ('a::type \<Rightarrow> 'd::type) 
     \<Rightarrow> ('d::type \<Rightarrow> 'c::ord) \<Rightarrow> bool" where
  "DataRefinement S1 R R' S2 = ((R o S1) \<le> (S2 o R'))"

text\<open>
If $\mathit{demonic}\ Q$ is correct with respect to $p$ and $q$, and 
$(\mathit{assert} \ p)\circ (\mathit{demonic}\  Q)$ is data refined
by $S$, then $S$ is correct with respect to $\mathit{angelic}\  R\  p$ and 
$\mathit{angelic} \ R' \ q$.
\<close>

theorem data_refinement:
  "mono R \<Longrightarrow> \<Turnstile> p {| S |} q \<Longrightarrow>  DataRefinement S R R' S' \<Longrightarrow> 
         \<Turnstile> (R p) {| S' |} (R' q)"
  apply (simp add:  DataRefinement_def Hoare_def le_fun_def)
  apply (drule_tac x = q in spec)
  apply (rule_tac y = "R (S q)" in order_trans)
  apply (drule_tac x = p and y = "S q" in monoD)
  by simp_all

theorem data_refinement2:
  "mono R \<Longrightarrow> \<Turnstile> p {| S |} q \<Longrightarrow>  DataRefinement ({.p.} o S) R R' S' \<Longrightarrow> 
         \<Turnstile> (R p) {| S' |} (R' q)"
  apply (simp add:  DataRefinement_def Hoare_def le_fun_def assert_def)
  apply (drule_tac x = q in spec)
  apply (subgoal_tac "p \<sqinter> S q = p")
  apply simp
  apply (rule antisym)
  by simp_all

theorem data_refinement_hoare:
  "mono S \<Longrightarrow> mono D \<Longrightarrow> DataRefinement ({.p.} o [:Q:]) {:R:} D S = 
         (\<forall> s . \<Turnstile> {s' . s \<in> R s' \<and> s \<in> p} {| S |} (D ((Q s)::'a::order)))"
  apply (simp add: le_fun_def assert_def angelic_def demonic_def Hoare_def DataRefinement_def)
  apply safe
  apply (simp_all)
  apply (drule_tac x = "Q s" in spec)
  apply auto [1]
  apply (drule_tac x = "xb" in spec)
  apply simp
  apply (simp add: less_eq_set_def le_fun_def)
  apply (drule_tac x = xa in spec)
  apply (simp_all add: mono_def)
  by auto

theorem data_refinement_choice1:
  "DataRefinement S1 D D' S2 \<Longrightarrow> DataRefinement S1 D D' S2' \<Longrightarrow> DataRefinement S1 D D' ( S2 \<sqinter> S2') "
  by (simp add: DataRefinement_def hoare_choice le_fun_def inf_fun_def)


theorem data_refinement_choice2:
  "mono D \<Longrightarrow> DataRefinement S1 D D' S2 \<Longrightarrow> DataRefinement S1' D D' S2' \<Longrightarrow> 
     DataRefinement (S1 \<sqinter> S1') D D' (S2 \<sqinter> S2')"
  apply (simp add: DataRefinement_def inf_fun_def le_fun_def)
  apply safe
  apply (rule_tac y = "D (S1 x)" in order_trans)
  apply (drule_tac x = "S1 x \<sqinter> S1' x" and y = "S1 x" in monoD)
  apply simp_all
  apply (rule_tac y = "D (S1' x)" in order_trans)
  apply (drule_tac x = "S1 x \<sqinter> S1' x" and y = "S1' x" in monoD)
  by simp_all


theorem data_refinement_top [simp]:
  "DataRefinement S1 D D' (\<top>::_::order_top)"
  by (simp add: DataRefinement_def le_fun_def top_fun_def)

definition apply_fun::"('a\<Rightarrow>'b\<Rightarrow>'c)\<Rightarrow>('a\<Rightarrow>'b)\<Rightarrow>'a\<Rightarrow>'c" (infixl ".." 5) where
  "(A .. B) = (\<lambda> x . (A x) (B x))"

definition
  "Disjunctive_fun R = (\<forall> i . (R i) \<in> Apply.Disjunctive)"

lemma Disjunctive_Sup:
  "Disjunctive_fun R \<Longrightarrow> (R .. (Sup X)) =  Sup {y . \<exists> x \<in> X . y = (R .. x)}"
  apply (subst fun_eq_iff)
  apply (simp add: apply_fun_def)
  apply safe
  apply (subst (asm) Disjunctive_fun_def)
  apply (drule_tac x = x in spec)
  apply (simp add: Apply.Disjunctive_def)
  apply (subgoal_tac "(R x ` (\<lambda>f. f x) ` X) =((\<lambda>f. f x) ` {y. \<exists>x\<in>X. y = (\<lambda>xa. R xa (x xa))})")
  apply (auto simp add: image_image cong del: SUP_cong_simp)
  done

lemma (in DiagramTermination) disjunctive_SUP_L_P:
  "Disjunctive_fun R \<Longrightarrow> (R .. (SUP_L_P P (pair u i))) =  (SUP_L_P (\<lambda> w . (R .. (P w)))) (pair u i)"
  by (simp add: SUP_L_P_def apply_fun_def Disjunctive_fun_def Apply.Disjunctive_def fun_eq_iff image_comp)

lemma apply_fun_range: "{y. \<exists>x. y = (R .. P x)} = range (\<lambda> x . R .. P x)"
  by (fact full_SetCompr_eq)

lemma [simp]: "Disjunctive_fun R \<Longrightarrow> mono ((R i)::'a::complete_lattice \<Rightarrow> 'b::complete_lattice)"
  by (simp add: Disjunctive_fun_def)

theorem (in DiagramTermination) dgr_data_refinement_1:
  "dmono D' \<Longrightarrow> Disjunctive_fun R \<Longrightarrow>
   (\<forall> w i j . \<Turnstile> P w i  {| D(i,j) |} SUP_L_P P (pair w i) j) \<Longrightarrow>
   (\<forall> w i j . DataRefinement ((assert (P w i)) o (D (i,j))) (R i) (R j) (D' (i, j))) \<Longrightarrow>
   
   \<Turnstile> (R .. (Sup (range P))) {| pt D' |} ((R .. (Sup (range P))) \<sqinter> (-(grd (step D'))))"
  apply (simp add: Disjunctive_Sup apply_fun_range)
  apply (rule hoare_diagram2)
  apply simp_all
  apply safe
  apply (simp add: disjunctive_SUP_L_P [THEN sym])
  apply (simp add: apply_fun_def)
  apply (rule_tac S = "D (i, j)" in data_refinement2)
  by auto

definition
  "DgrDataRefinement1 D R D' = (\<forall> i j . DataRefinement (D (i , j)) (R i) (R j) (D' (i, j)))"

definition
  "DgrDataRefinement2 P D R D' = (\<forall> i j . DataRefinement ({.P i.} o D (i , j)) (R i) (R j) (D' (i, j)))"

theorem DataRefinement_mono:
  "T \<le> S \<Longrightarrow> mono R \<Longrightarrow> DataRefinement S R R' S' \<Longrightarrow> DataRefinement T R R' S' "
  apply (simp add: DataRefinement_def mono_def)
  apply (subst le_fun_def)
  apply (simp add: le_fun_def)
  apply safe
  apply (rule_tac y = "R (S x)" in order_trans)
  by simp_all

definition
  "mono_fun R = (\<forall> i . mono (R i))"

theorem DgrDataRefinement_mono:
  "Q \<le> P \<Longrightarrow> mono_fun R \<Longrightarrow> DgrDataRefinement2 P D R D' \<Longrightarrow> DgrDataRefinement2 Q D R D'"
  apply (simp add: DgrDataRefinement2_def)
  apply auto
  apply (rule_tac S = "{.P i.} o D(i, j)" in DataRefinement_mono)
  apply (simp_all add: le_fun_def assert_def)
  apply safe
  apply (rule_tac y = "Q i" in order_trans)
  by (simp_all add: mono_fun_def)


text\<open>
Next theorem is the diagram version of the data refinement theorem. If the
diagram demonic choice $T$ is correct, and it is refined by $D$, then
$D$ is also correct. One important point in this theorem is that 
if the diagram demonic choice $T$ terminates, then $D$ also terminates.
\<close>
  

theorem (in DiagramTermination) Diagram_DataRefinement1:
  "dmono D \<Longrightarrow> Disjunctive_fun R \<Longrightarrow> \<turnstile> P {| D |} Q \<Longrightarrow> DgrDataRefinement1 D R D' \<Longrightarrow>
      \<turnstile> (R .. P) {| D' |} ((R .. P) \<sqinter> (-(grd (step D'))))"
  apply (unfold Hoare_dgr_def DgrDataRefinement1_def dgr_demonic_def)
  apply safe
  apply (rule_tac x="\<lambda> w . R .. (X w)" in exI)
  apply safe
  apply (unfold disjunctive_SUP_L_P [THEN sym])
  apply (simp add: apply_fun_def)
  apply (rule_tac S = "D (i,j)" and R = "R i" and R' = "R j" in data_refinement)
  by (simp_all add: Disjunctive_Sup apply_fun_range)


lemma comp_left_mono [simp]: "S \<le> S' \<Longrightarrow> S o T \<le> S' o T"
  by (simp add: le_fun_def)

lemma assert_pred_mono [simp]: "p \<le> q \<Longrightarrow> {.p.} \<le> {.q.}"
  apply (simp add: le_fun_def assert_def)
  apply safe
  apply (rule_tac y = p in order_trans)
  by simp_all

theorem (in DiagramTermination) Diagram_DataRefinement2:
  "dmono D \<Longrightarrow> Disjunctive_fun R \<Longrightarrow> \<turnstile> P {| D |} Q \<Longrightarrow> DgrDataRefinement2 P D R D' \<Longrightarrow>
      \<turnstile> (R .. P) {| D' |} ((R .. P) \<sqinter> (-(grd (step D'))))"
  apply (unfold Hoare_dgr_def DgrDataRefinement2_def dgr_demonic_def)
  apply auto
  apply (rule_tac x="\<lambda> w . R .. (X w)" in exI)
  apply safe
  apply (unfold disjunctive_SUP_L_P [THEN sym])
  apply (simp add: apply_fun_def)
  apply (rule_tac S = "D (i,j)" and R = "R i" and R' = "R j" in data_refinement2)
  apply (simp_all add: Disjunctive_Sup)
  apply (rule_tac S = "{.Sup (range X) i.} \<circ> D (i, j)" in DataRefinement_mono)
  apply (rule comp_left_mono)
  apply (rule assert_pred_mono)
  apply (simp add: Sup_fun_def comp_def)
  apply (rule SUP_upper)
  apply (auto simp add: apply_fun_def apply_fun_range image_image fun_eq_iff)
  apply (auto intro!: arg_cong [where f = Sup] arg_cong2 [where f = inf])
  done

lemma "(R'::'a::complete_lattice \<Rightarrow> 'b::complete_lattice) \<in> Apply.Disjunctive \<Longrightarrow>
   DataRefinement S R R' S' \<Longrightarrow> R (- grd S) \<le> - grd S'"
  apply (simp add: DataRefinement_def grd_def le_fun_def)
  apply (drule_tac x = "\<bottom>" in spec)
  by simp

end
