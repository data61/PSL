subsection\<open>Contextual typing\<close>

theory ContextFacts
imports
    Reduction
    Types
begin

text\<open>Naturally, we may wonder when instantiating the hole in a context is type-preserving.
    To assess this, we define a typing judgement for contexts.\<close>

inductive typing_ctxt :: "(nat \<Rightarrow> type) \<Rightarrow> (nat \<Rightarrow> type) \<Rightarrow> ctxt \<Rightarrow> type \<Rightarrow> type \<Rightarrow> bool"
                         ("_ , _ \<turnstile>\<^sub>c\<^sub>t\<^sub>x\<^sub>t _ : _ \<Leftarrow> _" [50, 50, 50, 50, 50] 50)
where
  type_ctxtEmpty [intro!]: "\<Gamma>, \<Delta> \<turnstile>\<^sub>c\<^sub>t\<^sub>x\<^sub>t \<diamond> : T \<Leftarrow> T" |
  type_ctxtApp   [intro!]: "\<lbrakk> \<Gamma>, \<Delta> \<turnstile>\<^sub>c\<^sub>t\<^sub>x\<^sub>t E : (T1\<rightarrow>T2) \<Leftarrow> U; \<Gamma>, \<Delta> \<turnstile>\<^sub>T t : T1 \<rbrakk> \<Longrightarrow> \<Gamma>, \<Delta> \<turnstile>\<^sub>c\<^sub>t\<^sub>x\<^sub>t (E \<^sup>\<bullet> t) : T2 \<Leftarrow> U"

inductive_cases typing_ctxt_elims [elim!]:
  "\<Gamma>, \<Delta> \<turnstile>\<^sub>c\<^sub>t\<^sub>x\<^sub>t \<diamond> : T \<Leftarrow> T"
  "\<Gamma>, \<Delta> \<turnstile>\<^sub>c\<^sub>t\<^sub>x\<^sub>t (E \<^sup>\<bullet> t) : T \<Leftarrow> U"

lemma typing_ctxt_correct1:
  shows "\<Gamma>, \<Delta> \<turnstile>\<^sub>T (ctxt_subst E r) : T  \<Longrightarrow> \<exists>U. (\<Gamma>, \<Delta> \<turnstile>\<^sub>T r : U \<and> \<Gamma>, \<Delta> \<turnstile>\<^sub>c\<^sub>t\<^sub>x\<^sub>t E : T \<Leftarrow> U)"
  by(induction E arbitrary: \<Gamma> \<Delta> T r; force)

lemma typing_ctxt_correct2:
  shows "\<Gamma>, \<Delta> \<turnstile>\<^sub>c\<^sub>t\<^sub>x\<^sub>t E : T \<Leftarrow> U \<Longrightarrow> \<Gamma>, \<Delta> \<turnstile>\<^sub>T r : U  \<Longrightarrow> \<Gamma>, \<Delta> \<turnstile>\<^sub>T (ctxt_subst E r) : T"
  by(induction arbitrary: r rule: typing_ctxt.induct) auto

lemma ctxt_subst_basecase: 
  "\<forall>n. c[n = n \<diamond>]\<^sup>C =  c"
  "\<forall>n. t[n = n \<diamond>]\<^sup>T =  t"
  by(induct c and t) (auto) 

lemma ctxt_subst_caseApp:
  "\<forall>n E s. (c[n=n (liftM_ctxt E n)]\<^sup>C)[n=n (\<diamond> \<^sup>\<bullet> (liftM_trm s n))]\<^sup>C = c[n=n ((liftM_ctxt E n) \<^sup>\<bullet> (liftM_trm s n))]\<^sup>C"
  "\<forall>n E s. (t[n=n (liftM_ctxt E n)]\<^sup>T)[n=n (\<diamond> \<^sup>\<bullet> (liftM_trm s n))]\<^sup>T = t[n=n ((liftM_ctxt E n) \<^sup>\<bullet> (liftM_trm s n))]\<^sup>T"
  by (induction c and t) (auto simp add: liftLM_comm_ctxt liftLM_comm liftMM_comm_ctxt  liftMM_comm liftM_ctxt_struct_subst)

lemma ctxt_subst:
  assumes "\<Gamma>, \<Delta> \<turnstile>\<^sub>c\<^sub>t\<^sub>x\<^sub>t E : U \<Leftarrow> T"
  shows   "(ctxt_subst E (\<mu> T : c)) \<longlonglongrightarrow>\<^sup>* \<mu> U : (c[0 = 0 (liftM_ctxt E 0)]\<^sup>C)"
using assms proof(induct E arbitrary: U T \<Gamma> \<Delta> c)
  case ContextEmpty
  have ctxtEmpty_inv: "\<Gamma>, \<Delta> \<turnstile>\<^sub>c\<^sub>t\<^sub>x\<^sub>t \<diamond> : U \<Leftarrow> T \<Longrightarrow> U = T"
    by(cases \<Gamma> \<Delta> "\<diamond>" rule: typing_ctxt.cases, fastforce, simp)
  show ?case
    using ContextEmpty by (clarsimp dest!: ctxtEmpty_inv simp: ctxt_subst_basecase)
next
  case (ContextApp E x)
  then show ?case
    by clarsimp (rule rtc_term_trans, rule rtc_appL, assumption, rule step_term, force, clarsimp simp add: ctxt_subst_caseApp(1))
qed
  
end
