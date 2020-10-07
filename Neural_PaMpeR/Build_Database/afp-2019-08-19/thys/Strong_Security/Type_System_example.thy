(*
Title: Strong-Security
Authors: Sylvia Grewe, Alexander Lux, Heiko Mantel, Jens Sauer
*)
theory Type_System_example
imports Type_System Expr Domain_example 
begin

\<comment> \<open>When interpreting, we have to instantiate the type for domains.\<close> 
\<comment> \<open>As an example, we take a type containing 'low' and 'high' as domains.\<close>


consts DA :: "('id,Dom) DomainAssignment"
consts BMap :: "'val \<Rightarrow> bool"

abbreviation d_indistinguishable' :: "('id,'val) Expr \<Rightarrow> Dom
  \<Rightarrow> ('id,'val) Expr \<Rightarrow> bool"
( "(_ \<equiv>\<^bsub>_\<^esub> _)" )
where 
"e1 \<equiv>\<^bsub>d\<^esub> e2 
  \<equiv> Strongly_Secure_Programs.d_indistinguishable ExprEval DA d e1 e2"

abbreviation relatedbyUSdB' :: "(('id,'val) Expr, 'id) MWLfCom list 
  \<Rightarrow> Dom \<Rightarrow> (('id,'val) Expr, 'id) MWLfCom list \<Rightarrow> bool" (infixr "\<approx>\<^bsub>_\<^esub>" 65)
where "V \<approx>\<^bsub>d\<^esub> V' \<equiv> (V,V') \<in> Strong_Security.USdB 
  (MWLf_semantics.MWLfSteps_det ExprEval BMap) DA d"

\<comment> \<open>Security typing rules for expressions - will be part of a side condition\<close>
inductive 
ExprSecTyping :: "('id, 'val) Expr \<Rightarrow> Dom set \<Rightarrow> bool"
("\<turnstile>\<^bsub>\<E>\<^esub> _ : _")
where 
Consts: "\<turnstile>\<^bsub>\<E>\<^esub> (Const v) : {d}" |
Vars: "\<turnstile>\<^bsub>\<E>\<^esub> (Var x) : {DA x}" |
Ops: "\<forall>i < length arglist. \<turnstile>\<^bsub>\<E>\<^esub> (arglist!i) : (dl!i)
  \<Longrightarrow> \<turnstile>\<^bsub>\<E>\<^esub> (Op f arglist) : (\<Union>{d. (\<exists>i < length arglist. d = (dl!i))})"

definition synAssignSC :: "'id \<Rightarrow> ('id, 'val) Expr \<Rightarrow> bool"
where
"synAssignSC x e \<equiv> \<exists>D. (\<turnstile>\<^bsub>\<E>\<^esub> e : D \<and> (\<forall>d \<in> D. (d \<le> DA x)))"

definition synWhileSC :: "('id, 'val) Expr \<Rightarrow> bool"
where
"synWhileSC e \<equiv> \<exists>D. (\<turnstile>\<^bsub>\<E>\<^esub> e : D \<and> (\<forall>d\<in>D. \<forall>d'. d \<le> d'))"

definition synIfSC :: "('id, 'val) Expr \<Rightarrow> (('id, 'val) Expr, 'id) MWLfCom 
  \<Rightarrow> (('id, 'val) Expr, 'id) MWLfCom \<Rightarrow> bool" 
where
"synIfSC e c1 c2 \<equiv> 
 \<forall>d. (\<not> (e \<equiv>\<^bsub>d\<^esub> e) \<longrightarrow> [c1] \<approx>\<^bsub>d\<^esub> [c2])"

lemma ExprTypable_with_smallerD_implies_d_indistinguishable:
"\<lbrakk> \<turnstile>\<^bsub>\<E>\<^esub> e : D'; \<forall>d' \<in> D'. d' \<le> d \<rbrakk> \<Longrightarrow> e \<equiv>\<^bsub>d\<^esub> e" 
proof (induct rule: ExprSecTyping.induct, 
    simp_all add: Strongly_Secure_Programs.d_indistinguishable_def 
    Strong_Security.d_equal_def, auto)
  fix dl and arglist::"(('id, 'val) Expr) list" and f::"'val list \<Rightarrow> 'val" 
    and m1::"('id,'val) State" and m2::"('id,'val) State"
  assume main: "\<forall>i < length arglist. \<turnstile>\<^bsub>\<E>\<^esub> arglist!i : dl!i \<and>
    ((\<forall>d' \<in> (dl!i). d' \<le> d) \<longrightarrow> 
    (\<forall>m m'. (\<forall>x. DA x \<le> d \<longrightarrow> m x = m' x) 
    \<longrightarrow> ExprEval (arglist!i) m = ExprEval (arglist!i) m'))"
  assume smaller: "\<forall>D. (\<exists>i < length arglist. D = (dl!i)) 
    \<longrightarrow> (\<forall>d'\<in>D. d' \<le> d)"
  assume eqstate: "\<forall>x. DA x \<le> d \<longrightarrow> m1 x = m2 x"
  
  from smaller have irangesubst: 
    "\<forall>i < length arglist. \<forall>d' \<in> (dl!i). d' \<le> d"
    by auto
        
  with eqstate main have 
    "\<forall>i < length arglist. ExprEval (arglist!i) m1 
    = ExprEval (arglist!i) m2"
    by force
 
  hence substmap: "(ExprEvalL arglist m1) = (ExprEvalL arglist m2)" 
    by (induct arglist, auto, force)
    
  show "f (ExprEvalL arglist m1) = f (ExprEvalL arglist m2)"
    by (subst substmap, auto)
qed

interpretation Type_System_example: Type_System ExprEval BMap DA
  synAssignSC synWhileSC synIfSC
by (unfold_locales, simp add: synAssignSC_def,
  metis ExprTypable_with_smallerD_implies_d_indistinguishable,
  simp add: synWhileSC_def,
  metis ExprTypable_with_smallerD_implies_d_indistinguishable,
  simp add: synIfSC_def, metis)

end
