subsection\<open>Progress\<close>

theory Progress
  imports TypePreservation
begin
  
text\<open>We say that a term $t$ is in \emph{weak-head-normal} form when one of the following conditions are met:
  \begin{enumerate}
    \item $t$ is a value,
    \item there exists $\alpha$ and $v$ such that $t = \mu:\tau.[\alpha]\ v$ with $\alpha \in fcv(v)$
          whenever $\alpha = 0$.
  \end{enumerate}\<close>
  
fun (sequential) is_nf :: "trm \<Rightarrow> bool" where
  "is_nf (\<mu> U: (<\<beta>> v)) = (is_val v \<and> (\<beta> = 0 \<longrightarrow> 0 \<in> fmv_trm v 0))" |
  "is_nf v = is_val v"
  
lemma progress':
  "\<Gamma>, \<Delta> \<turnstile>\<^sub>T t : T \<Longrightarrow> lambda_closed t \<Longrightarrow> (\<forall> s. \<not>(t \<longlonglongrightarrow> s)) \<Longrightarrow> is_nf t"
  "\<Gamma>, \<Delta> \<turnstile>\<^sub>C c \<Longrightarrow> lambda_closedC c  \<Longrightarrow> (\<forall> \<beta> t. c = (<\<beta>> t) \<longrightarrow> (\<forall> d. \<not>(t \<longlonglongrightarrow> d)) \<longrightarrow> is_nf t)"                            
proof (induct rule: typing_trm_typing_cmd.inducts)
  case (app \<Gamma> \<Delta> t T1 T2 s)
  then show ?case
    by -(erule type_arrow_elim; force)  
next
  case (activate \<Gamma> \<Delta> T c)
  then show ?case
    proof(cases c)
      case (MVar \<alpha> t)
      then show ?thesis
        using activate by (case_tac t; force)
    qed
qed force+

theorem progress:
  assumes "\<Gamma>, \<Delta> \<turnstile>\<^sub>T t : T" "lambda_closed t"
  shows   "is_nf t \<or> (\<exists> s. t \<longlonglongrightarrow> s)"
using assms by (fastforce intro: progress')
    
end
