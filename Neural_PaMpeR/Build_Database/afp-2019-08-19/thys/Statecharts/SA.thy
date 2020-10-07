(*  Title:      statecharts/SA/SA.thy

    Author:     Steffen Helke and Florian Kammüller, Software Engineering Group
    Copyright   2010 Technische Universitaet Berlin
*)

section \<open>Sequential Automata\<close>
theory SA
imports Expr
begin

definition
  SeqAuto :: "['s set,
               's,
               (('s,'e,'d)label) set,
               (('s,'e,'d)trans) set]
              => bool" where
  "SeqAuto S I L D =  (I \<in> S \<and> S \<noteq> {} \<and>  finite S \<and> finite D \<and> 
                       (\<forall> (s,l,t) \<in> D. s \<in> S \<and> t \<in> S \<and> l \<in> L))"

lemma SeqAuto_EmptySet:
 "({@x .True}, (@x .True), {}, {}) \<in> {(S,I,L,D) | S I L D. SeqAuto S I L D}"
by (unfold SeqAuto_def, auto)

definition
  "seqauto =
    { (S,I,L,D) |
              (S::'s set)
              (I::'s)
              (L::(('s,'e,'d)label) set)
              (D::(('s,'e,'d)trans) set).
             SeqAuto S I L D}"

typedef ('s,'e,'d) seqauto =
    "seqauto :: ('s set * 's * (('s,'e,'d)label) set * (('s,'e,'d)trans) set) set"
  unfolding seqauto_def
  apply (rule exI)
  apply (rule SeqAuto_EmptySet)
  done

definition
 States :: "(('s,'e,'d)seqauto) => 's set" where
 "States = fst o Rep_seqauto"

definition
 InitState :: "(('s,'e,'d)seqauto) => 's" where
 "InitState = fst o snd o Rep_seqauto"

definition
 Labels :: "(('s,'e,'d)seqauto) => (('s,'e,'d)label) set" where
 "Labels = fst o snd o snd o Rep_seqauto"

definition
 Delta :: "(('s,'e,'d)seqauto) => (('s,'e,'d)trans) set" where
 "Delta = snd o snd o snd o Rep_seqauto"

definition
 SAEvents :: "(('s,'e,'d)seqauto) => 'e set" where
 "SAEvents SA = (\<Union> l \<in> Label (Delta SA). (fst (action l)) \<union> (ExprEvents (expr l)))"

lemma Rep_seqauto_tuple:
  "Rep_seqauto SA = (States SA, InitState SA, Labels SA, Delta SA)"
by (unfold States_def InitState_def Labels_def Delta_def, auto)

lemma Rep_seqauto_select:
  "(States SA,InitState SA,Labels SA,Delta SA) \<in>  seqauto"
by (rule Rep_seqauto_tuple [THEN subst], rule Rep_seqauto)

lemma SeqAuto_select:
  "SeqAuto (States SA) (InitState SA) (Labels SA) (Delta SA)"
by (cut_tac SA=SA in Rep_seqauto_select, unfold seqauto_def, auto)

lemma neq_States [simp]:
  "States SA \<noteq> {}"
apply (cut_tac Rep_seqauto_select)
apply auto
apply (unfold seqauto_def SeqAuto_def)
apply auto
done

lemma SA_States_disjunct :
 "(States A) \<inter> (States A') = {} \<Longrightarrow> A' \<noteq> A"
by auto

lemma SA_States_disjunct2 : 
 "\<lbrakk> (States A) \<inter> C = {}; States B \<subseteq> C \<rbrakk> \<Longrightarrow> B \<noteq> A"
apply (rule SA_States_disjunct)
apply auto
done

lemma SA_States_disjunct3 : 
 "\<lbrakk> C \<inter> States A = {}; States B \<subseteq> C \<rbrakk> \<Longrightarrow>  States A \<inter> States B = {}"
apply (cut_tac SA=B in neq_States)
apply fast
done

lemma EX_State_SA [simp]:
  "\<exists> S. S \<in> States SA"
apply (cut_tac Rep_seqauto_select)
apply (unfold seqauto_def SeqAuto_def)
apply auto
done

lemma finite_States [simp]:
  "finite (States A)"
apply (cut_tac Rep_seqauto_select) 
apply (unfold seqauto_def SeqAuto_def)
apply auto
done

lemma finite_Delta [simp]: 
  "finite (Delta A)"
apply (cut_tac Rep_seqauto_select) 
apply (unfold seqauto_def SeqAuto_def)
apply auto
done

lemma InitState_States [simp]:
  "InitState A \<in> States A"
apply (cut_tac Rep_seqauto_select)
apply (unfold seqauto_def SeqAuto_def)
apply auto
done

lemma SeqAuto_EmptySet_States [simp]:
 "(States (Abs_seqauto ({@x. True}, (@x. True), {}, {}))) = {(@x. True)}"
apply (unfold States_def)
apply (simp)
apply (subst Abs_seqauto_inverse)
apply (unfold seqauto_def)
apply (rule SeqAuto_EmptySet)
apply auto
done

lemma SeqAuto_EmptySet_SAEvents [simp]:
 "(SAEvents (Abs_seqauto ({@x. True}, (@x. True), {}, {}))) = {}"
apply (unfold SAEvents_def Delta_def) 
apply simp
apply (subst Abs_seqauto_inverse)
apply (unfold seqauto_def)
apply (rule SeqAuto_EmptySet)
apply auto
done

lemma Label_Delta_subset [simp]:
  "(Label (Delta SA)) \<subseteq> Labels SA"
apply (unfold Label_def label_def)
apply auto
apply (cut_tac SA=SA in SeqAuto_select)
apply (unfold SeqAuto_def)
apply auto
done

lemma Target_SAs_Delta_States:
  "Target (\<Union>(Delta ` (SAs HA))) \<subseteq> \<Union>(States ` (SAs HA))"
apply (unfold image_def Target_def target_def)
apply auto
apply (rename_tac SA Source Trigger Guard Action Update Target)
apply (cut_tac SA=SA in SeqAuto_select)
apply (unfold SeqAuto_def)
apply auto
done

lemma States_Int_not_mem:
 "(\<Union>(States ` F) Int States SA) = {} \<Longrightarrow> SA \<notin> F"
apply (unfold Int_def)
apply auto
apply (subgoal_tac "\<exists> S. S \<in> States SA")
prefer 2
apply (rule EX_State_SA)
apply (erule exE)
apply (rename_tac T)
apply (erule_tac x=T in allE)
apply auto
done

lemma Delta_target_States [simp]:
  "\<lbrakk> T \<in> Delta A\<rbrakk> \<Longrightarrow> target T \<in> States A"
apply (cut_tac SA=A in SeqAuto_select)
apply (unfold SeqAuto_def source_def target_def)
apply auto
done

lemma Delta_source_States [simp]:
  "\<lbrakk> T \<in> Delta A \<rbrakk> \<Longrightarrow> source T \<in> States A"
apply (cut_tac SA=A in SeqAuto_select)
apply (unfold SeqAuto_def source_def target_def)
apply auto
done

end
