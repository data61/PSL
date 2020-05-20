(*File: MutiStep.thy
  Author: L Beringer & M Hofmann, LMU Munich
  Date: 05/12/2008
  Purpose: Transitive closure of the Language.Step relation
*)
(*<*)
theory MultiStep imports Language begin
(*>*)

section\<open>Auxiliary operational judgements\<close>

text\<open>Beside the basic operational judgements \<open>Step\<close> and \<open>Exec\<close>, the interpretation of judgements refers to two multi-step
relations which we now define.\<close>

subsection\<open>Multistep execution\<close> 

text\<open>The first additional operational judgement is the reflexive and
transitive closure of \<open>Step\<close>. It relates states $s$ and $t$ if
the latter can be reached from the former by a chain if single steps,
all in the same frame. Note that $t$ does not need to be a terminal
state. As was the case in the definition of \<open>Step\<close>, we first
define a relation with an explicit derivation height index (\<open>MStep\<close>).\<close>

inductive_set 
MStep::"(Mbody \<times> Label \<times> State \<times> nat \<times> Label \<times> State) set" 
where
MS_zero: "\<lbrakk>k=0; t=s; ll=l\<rbrakk> \<Longrightarrow> (M,l,s,k,ll,t):MStep"
|
MS_step: "\<lbrakk>(M,l,s,n,l1,r):Step; (M,l1,r,k,l2,t):MStep; m=Suc k+n\<rbrakk>
         \<Longrightarrow> (M,l,s,m,l2,t) : MStep"

text\<open>The following properties of \<open>MStep\<close> are useful to
notice.\<close>

(*<*)
lemma ZeroHeightMultiElimAux[rule_format]:
  "(M, l, s, k, ll, r) \<in> MStep \<Longrightarrow> 0=k \<longrightarrow> (r=s \<and> ll=l)"
by (erule MStep.induct, simp_all) 
(*>*) 
lemma ZeroHeightMultiElim: "(M,l,s,0,ll,r) \<in> MStep \<Longrightarrow> r=s \<and> ll=l"
(*<*)
by (erule ZeroHeightMultiElimAux, simp)
(*>*)
(*<*)
lemma MultiSplitAux[rule_format]:
  "(M, l, s, k, ll, t) \<in> MStep \<Longrightarrow> 
    1 \<le> k \<longrightarrow> (\<exists> n m r l1. (M,l,s,n,l1,r):Step \<and> 
                        (M,l1,r,m,ll,t):MStep \<and> Suc m +n =k)"
apply (erule MStep.induct, simp_all)
apply clarsimp
  apply (case_tac k, clarsimp) 
    apply (drule ZeroHeightMultiElim[simplified], clarsimp) 
      apply (rule, rule,rule, rule,rule, rule, rule, assumption) 
      apply (rule,rule MS_zero) apply simp apply simp apply simp
  apply clarsimp
    apply (rule, rule,rule, rule,rule, rule,rule,assumption) apply (rule,assumption)
    apply simp
done
(*>*)

lemma MultiSplit:
  "\<lbrakk>(M, l, s, k, ll, t) \<in> MStep; 1 \<le> k\<rbrakk> \<Longrightarrow>
  \<exists> n m r l1. (M,l,s,n,l1,r):Step \<and> (M,l1,r,m,ll,t):MStep \<and> Suc m + n =k"
(*<*)by (erule MultiSplitAux, assumption)(*>*)

(*<*)
lemma MStep_returnElimAux[rule_format]:
"(M,l,s,k,ll,t) \<in> MStep \<Longrightarrow> 
 (get_ins M l = Some vreturn \<longrightarrow> t=s \<and> ll=l)"
apply (erule MStep.induct)
apply clarsimp
apply clarsimp apply (drule RetElim1) apply simp apply clarsimp
done
(*>*)

lemma MStep_returnElim:
  "\<lbrakk>(M,l,s,k,ll,t) \<in> MStep; get_ins M l = Some vreturn\<rbrakk> \<Longrightarrow> t=s \<and> ll = l"
(*<*)
by (erule MStep_returnElimAux, assumption)
(*>*)

(*<*)
lemma MultiAppAux[rule_format]:
"(M,l,s,k,l1,r):MStep \<Longrightarrow> 
  (\<forall> n t l2. (M,l1,r,n,l2,t):Step \<longrightarrow> (M,l,s,Suc k+n,l2,t):MStep)"
apply (erule MStep.induct)
apply clarsimp apply (erule MS_step) apply (rule MS_zero) apply (simp,simp, simp, simp) 
apply (rule, rule, rule, rule)
apply (erule MS_step) 
  apply (erule_tac x=na in allE, erule_tac x=ta in allE)
  apply (erule_tac x=l2a in allE , erule impE) apply assumption 
    apply assumption
    apply simp
done
(*>*)

lemma MultiApp:
  "\<lbrakk>(M,l,s,k,l1,r):MStep; (M,l1,r,n,l2,t):Step\<rbrakk> \<Longrightarrow> (M,l,s,Suc k+n,l2,t):MStep"
(*<*)
by (erule MultiAppAux, assumption)
(*>*)

(*<*)
lemma MStep_Compose_Aux:"(M,l,s,n,l1,r):MStep \<Longrightarrow> (\<forall> k t l2. (M,l1,r,k,l2,t):MStep \<longrightarrow> (M,l,s,n + k,l2,t):MStep)"
apply (erule MStep.induct)
apply clarsimp
apply (rule, rule, rule, rule)
  apply (erule_tac x=ka in allE, erule_tac x=ta in allE)
  apply (erule_tac x=l2a in allE, erule impE, assumption)
  apply (erule MS_step, assumption)
  apply simp
done
(*>*)

lemma MStep_Compose:
  "\<lbrakk>(M,l,s,n,l1,r):MStep; (M,l1,r,k,l2,t):MStep; nk=n+k\<rbrakk> 
  \<Longrightarrow> (M,l,s,nk,l2,t):MStep"
(*<*)
by (drule MStep_Compose_Aux, fastforce)
(*>*)

text\<open>Here are two simple lemmas relating the operational judgements.\<close>

(*<*)
lemma MStep_Exec1_Aux[rule_format]:
"(M, l, s, kb, l1, t) \<in> MStep \<Longrightarrow> 
 (\<forall> hh v . (\<exists> k . (M, l, s, k, hh, v) \<in> Exec) \<longrightarrow> (\<exists> n. (M, l1, t, n, hh, v) \<in> Exec))"
apply (erule MStep.induct)
apply clarsimp
apply (rule, rule, rule)  
  apply (erule exE)
  apply (erule_tac x=hh in allE, erule_tac x=v in allE, erule mp)
  apply (case_tac s, clarify)
  apply (drule ExecElim1, clarsimp)
  apply (erule disjE) apply clarsimp apply (drule RetElim1, simp,simp)
  apply clarsimp
  apply (drule Step_determ, assumption, clarsimp)
  apply (rule, assumption)
done
(*>*)
lemma MStep_Exec1:
  "\<lbrakk>(M, l, s, kb, l1, t) \<in> MStep; (M, l, s, k, hh, v) \<in> Exec\<rbrakk> 
  \<Longrightarrow> \<exists> n. (M, l1, t, n, hh, v) \<in> Exec"
(*<*)
by (erule MStep_Exec1_Aux, fast)
(*>*)

(*<*)
lemma MStep_Exec2_Aux[rule_format]:
"(M, l, s, kb, l1, t) \<in> MStep \<Longrightarrow> 
 (\<forall> hh v . (\<exists> k . (M, l1, t, k, hh, v) \<in> Exec) \<longrightarrow> (\<exists> n. (M, l, s, n, hh, v) \<in> Exec))"
apply (erule MStep.induct)
apply clarsimp
apply (rule, rule, rule)  
  apply (erule exE)
  apply (erule_tac x=hh in allE, erule_tac x=v in allE, erule impE)
    apply (rule, assumption)
  apply (erule exE)
  apply (rule, rule Run) apply assumption+ apply simp
done
(*>*)

lemma MStep_Exec2:
  "\<lbrakk> (M, l, s, kb, l1, t) \<in> MStep; (M, l1, t, k, hh, v) \<in> Exec\<rbrakk> 
  \<Longrightarrow> \<exists> n. (M, l, s, n, hh, v) \<in> Exec"
(*<*)
by (erule MStep_Exec2_Aux, fast)
(*>*)

text\<open>Finally, the definition of the non-height-indexed relation.\<close>

definition MS::"Mbody \<Rightarrow> Label \<Rightarrow> State \<Rightarrow> Label \<Rightarrow> State \<Rightarrow> bool"
where "MS M l s ll t = (\<exists> k . (M,l,s,k,ll,t):MStep)"

(*<*)  
end
(*>*)
