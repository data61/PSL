subsection\<open>Type preservation\<close>

theory TypePreservation
imports
    ContextFacts
begin

text\<open>Shifting lambda variables preserves well-typedness.\<close>
  
lemma liftL_type: 
  "\<Gamma>, \<Delta> \<turnstile>\<^sub>T t : T \<Longrightarrow> \<forall>k. \<Gamma>\<langle>k:U\<rangle>, \<Delta> \<turnstile>\<^sub>T (liftL_trm t k) : T"
  "\<Gamma>, \<Delta> \<turnstile>\<^sub>C c \<Longrightarrow> \<forall>k. \<Gamma>\<langle>k:U\<rangle>, \<Delta> \<turnstile>\<^sub>C (liftL_cmd c k)"
  by (induct rule: typing_trm_typing_cmd.inducts) auto

text\<open>Shifting mu variables preserves well-typedness.\<close>
  
lemma liftM_type: 
  "\<Gamma>, \<Delta> \<turnstile>\<^sub>T t : T \<Longrightarrow> \<forall>k. \<Gamma>, \<Delta>\<langle>k:U\<rangle> \<turnstile>\<^sub>T (liftM_trm t k) : T"
  "\<Gamma>, \<Delta> \<turnstile>\<^sub>C c \<Longrightarrow> \<forall>k. \<Gamma>, \<Delta>\<langle>k:U\<rangle> \<turnstile>\<^sub>C (liftM_cmd c k)"
  by(induct rule: typing_trm_typing_cmd.inducts) auto
    
lemma dropM_type:
  "\<Gamma> , \<Delta>1 \<turnstile>\<^sub>T t : T \<Longrightarrow> k \<notin> fmv_trm t 0 \<Longrightarrow> (\<forall>x. x<k \<longrightarrow> \<Delta>1 x = \<Delta> x) 
    \<Longrightarrow> (\<forall>x. x>k \<longrightarrow> \<Delta>1 x = \<Delta> (x-1)) \<Longrightarrow> \<Gamma> , \<Delta> \<turnstile>\<^sub>T dropM_trm t k : T"
  "\<Gamma> , \<Delta>1 \<turnstile>\<^sub>C c \<Longrightarrow> k \<notin> fmv_cmd c 0 \<Longrightarrow> (\<forall>x. x<k \<longrightarrow> \<Delta>1 x = \<Delta> x) 
    \<Longrightarrow> (\<forall>x. x>k \<longrightarrow> \<Delta>1 x = \<Delta> (x-1)) \<Longrightarrow> \<Gamma> , \<Delta> \<turnstile>\<^sub>C dropM_cmd c k"
proof (induct arbitrary: k \<Delta> and k \<Delta> rule: typing_trm_typing_cmd.inducts)
  case (activate \<Gamma> \<Delta> T c)
  then show ?case
    apply(erule_tac x = "Suc k" in meta_allE)
    apply(insert fmv_suc(1))
    apply(clarsimp simp add: shift_def)
    done
qed fastforce+

  
text\<open>Lifting $\lambda$ and $\mu$-variables in contexts preserves contextual typing judgements.\<close>
  
lemma liftL_ctxt_type:
  assumes "\<Gamma>, \<Delta> \<turnstile>\<^sub>c\<^sub>t\<^sub>x\<^sub>t E : T \<Leftarrow> U"
  shows   "\<forall>k. \<Gamma>\<langle>k:T1\<rangle>, \<Delta> \<turnstile>\<^sub>c\<^sub>t\<^sub>x\<^sub>t (liftL_ctxt E k) : T \<Leftarrow> U"
using assms by (induct rule: typing_ctxt.induct) (auto simp add: liftL_type)

lemma liftM_ctxt_type:
  assumes "\<Gamma>, \<Delta> \<turnstile>\<^sub>c\<^sub>t\<^sub>x\<^sub>t E : T \<Leftarrow> U"
  shows   "\<Gamma>, \<Delta>\<langle>k:T1\<rangle> \<turnstile>\<^sub>c\<^sub>t\<^sub>x\<^sub>t (liftM_ctxt E k) : T \<Leftarrow> U"
using assms by(induct rule: typing_ctxt.induct) (auto simp add: liftM_type)

text\<open>Substitution lemma for logical substitution.\<close>
  
theorem subst_type:
  "\<Gamma>1, \<Delta> \<turnstile>\<^sub>T t : T \<Longrightarrow> \<Gamma>, \<Delta> \<turnstile>\<^sub>T r : T1 \<Longrightarrow> \<Gamma>1 = \<Gamma>\<langle>k:T1\<rangle> \<Longrightarrow> \<Gamma>, \<Delta> \<turnstile>\<^sub>T t[r/k]\<^sup>T : T"
  "\<Gamma>1, \<Delta> \<turnstile>\<^sub>C c \<Longrightarrow> \<Gamma>, \<Delta> \<turnstile>\<^sub>T r : T1 \<Longrightarrow> \<Gamma>1 = \<Gamma>\<langle>k:T1\<rangle> \<Longrightarrow> \<Gamma>, \<Delta> \<turnstile>\<^sub>C c[r/k]\<^sup>C "
proof(induct arbitrary: \<Gamma> k T1 r and \<Gamma> k r T1 rule: typing_trm_typing_cmd.inducts)
  case (lambda \<Gamma> T1 \<Delta> t T2)
  then show ?case
    by -(rotate_tac 2, drule liftL_type(1), fastforce)
next
  case (activate \<Gamma> \<Delta> T c)
  then show ?case
    by -(rotate_tac 2, drule liftM_type(1), fastforce)
qed force+

text\<open>Substitution lemma for structural substitution. The proof is by induction on the first typing judgement.\<close>
  
lemma struct_subst_command:
  assumes "\<Gamma>, \<Delta> \<turnstile>\<^sub>T t : T" "\<Delta> x = T" "\<Gamma> , \<Delta>' \<turnstile>\<^sub>c\<^sub>t\<^sub>x\<^sub>t E : U \<Leftarrow> T1" "\<Delta> = \<Delta>'\<langle>\<alpha>:T1\<rangle>"
          "(\<Gamma> , \<Delta>' \<turnstile>\<^sub>c\<^sub>t\<^sub>x\<^sub>t E : U \<Leftarrow> T1 \<Longrightarrow> \<Delta> = \<Delta>'\<langle>\<alpha>:T1\<rangle> \<Longrightarrow> \<Gamma> , \<Delta>'\<langle>\<beta>:U\<rangle> \<turnstile>\<^sub>T t[\<alpha>=\<beta> (liftM_ctxt E \<beta>)]\<^sup>T : T)"
  shows   "\<Gamma>,( \<Delta>'\<langle>\<beta>:U\<rangle>) \<turnstile>\<^sub>C (<x> t)[\<alpha>=\<beta> (liftM_ctxt E \<beta>)]\<^sup>C"
  using assms apply clarsimp
  apply (rule conjI, force, clarsimp)+
  apply (rule conjI)
   apply (metis liftM_ctxt_type passivate shift_eq typing_ctxt_correct2)
  apply force
  done

theorem struct_subst_type:
  "\<Gamma>, \<Delta>1 \<turnstile>\<^sub>T t : T \<Longrightarrow> \<Gamma>, \<Delta> \<turnstile>\<^sub>c\<^sub>t\<^sub>x\<^sub>t E : U \<Leftarrow> T1 \<Longrightarrow> \<Delta>1 = \<Delta>\<langle>\<alpha>:T1\<rangle> \<Longrightarrow> \<Gamma>, \<Delta>\<langle>\<beta>:U\<rangle> \<turnstile>\<^sub>T t[\<alpha>=\<beta> (liftM_ctxt E \<beta>)]\<^sup>T : T"
  "\<Gamma>, \<Delta>1 \<turnstile>\<^sub>C c \<Longrightarrow> \<Gamma>, \<Delta> \<turnstile>\<^sub>c\<^sub>t\<^sub>x\<^sub>t E : U \<Leftarrow> T1  \<Longrightarrow> \<Delta>1 = \<Delta>\<langle>\<alpha>:T1\<rangle> \<Longrightarrow> \<Gamma>, \<Delta>\<langle>\<beta>:U\<rangle> \<turnstile>\<^sub>C c[\<alpha>=\<beta> (liftM_ctxt E \<beta>)]\<^sup>C"
proof (induct arbitrary: \<Delta> T1 E U \<beta> \<alpha> and \<Delta> T1 E U \<beta> \<alpha> rule: typing_trm_typing_cmd.inducts)
  case (lambda \<Gamma> T1 \<Delta> t T2)
  then show ?case
    by -(drule liftL_ctxt_type, fastforce simp: liftLM_comm_ctxt)
next
  case (activate \<Gamma> \<Delta> T c)
  then show ?case
    by -(drule liftM_ctxt_type, fastforce simp: liftMM_comm_ctxt)
next
  case (passivate \<Gamma> \<Delta> t T x)
  then show ?case
    using struct_subst_command by force
qed fastforce+

lemma struct_subst_type_command:  "\<Gamma>, \<Delta>1 \<turnstile>\<^sub>C c \<Longrightarrow> \<Gamma>, \<Delta> \<turnstile>\<^sub>c\<^sub>t\<^sub>x\<^sub>t E : U \<Leftarrow> T1 
    \<Longrightarrow> \<Delta>1 = \<Delta>\<langle>\<alpha>:T1\<rangle>
    \<Longrightarrow> \<Gamma>, \<Delta>\<langle>\<beta>:U\<rangle> \<turnstile>\<^sub>C c[\<alpha>=\<beta> (liftM_ctxt E \<beta>)]\<^sup>C"
using struct_subst_type by force
  

lemma dropM_env:
  "\<Gamma>, \<Delta>1 \<turnstile>\<^sub>T t[k=x \<diamond>]\<^sup>T : T \<Longrightarrow> \<Delta>1 = \<Delta>\<langle>x:(\<Delta> x)\<rangle> \<Longrightarrow> \<Gamma> , \<Delta> \<turnstile>\<^sub>T dropM_trm (t[k=x \<diamond>]\<^sup>T) x : T" 
  "\<Gamma>, \<Delta>1 \<turnstile>\<^sub>C c[k=x \<diamond>]\<^sup>C \<Longrightarrow> \<Delta>1 = \<Delta>\<langle>x:(\<Delta> x)\<rangle> \<Longrightarrow> \<Gamma> , \<Delta> \<turnstile>\<^sub>C dropM_cmd (c[k=x \<diamond>]\<^sup>C) x"
  by (induct t and c arbitrary: \<Gamma> T \<Delta>1 x k \<Delta> and \<Gamma> T \<Delta>1 x k \<Delta>) fastforce+
    
theorem type_preservation:
  "\<Gamma>, \<Delta> \<turnstile>\<^sub>T t : T \<Longrightarrow> t \<longlonglongrightarrow> s \<Longrightarrow> \<Gamma>, \<Delta> \<turnstile>\<^sub>T s : T"
  "\<Gamma>, \<Delta> \<turnstile>\<^sub>C c \<Longrightarrow> c \<^sub>C\<longlonglongrightarrow> d \<Longrightarrow> \<Gamma>, \<Delta> \<turnstile>\<^sub>C d"
proof(induct arbitrary: s and d rule: typing_trm_typing_cmd.inducts)
  case (app \<Gamma> \<Delta> t T1 T2 s s')
  then show ?case
    apply -
    apply (erule redE; clarsimp simp: subst_type(1))
      apply (subgoal_tac "\<Gamma> , \<Delta> \<turnstile>\<^sub>T ctxt_subst (\<diamond> \<^sup>\<bullet> s) (\<mu>(T1\<rightarrow>T2) : c) : T2")
       apply (drule typing_ctxt_correct1, clarsimp)
       apply (subgoal_tac "\<Gamma> , \<Delta>\<langle>0:T2\<rangle> \<turnstile>\<^sub>C c[0=0 (liftM_ctxt (\<diamond> \<^sup>\<bullet> s) 0)]\<^sup>C")
        apply (clarsimp, rule struct_subst_type_command)
         apply force+
    done
next
  case (passivate \<Gamma> \<Delta> t T x)
  then show ?case
    apply clarsimp
    apply (erule redE, clarsimp)
     apply (drule struct_subst_type_command [where \<beta> = x])
       apply (fastforce simp: dropM_env(2))+                  
    done
qed (force simp: dropM_type)+

end
