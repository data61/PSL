theory "Denotational-Related"
imports Denotational ResourcedDenotational ValueSimilarity
begin

text \<open>
Given the similarity relation it is straight-forward to prove that the standard
and the resourced denotational semantics produce similar results. (Theorem 10 in
|cite{functionspaces}).
\<close>

theorem denotational_semantics_similar: 
  assumes "\<rho> \<triangleleft>\<triangleright>\<^sup>* \<sigma>"
  shows "\<lbrakk>e\<rbrakk>\<^bsub>\<rho>\<^esub> \<triangleleft>\<triangleright> (\<N>\<lbrakk>e\<rbrakk>\<^bsub>\<sigma>\<^esub>)\<cdot>C\<^sup>\<infinity>"
using assms
proof(induct e arbitrary: \<rho> \<sigma> rule:exp_induct)
  case (Var v)
  from Var have "\<rho> v \<triangleleft>\<triangleright> (\<sigma> v)\<cdot>C\<^sup>\<infinity>" by cases auto
  thus ?case by simp
next
  case (Lam v e)
  { fix x y
    assume "x \<triangleleft>\<triangleright> y\<cdot>C\<^sup>\<infinity>"
    with \<open>\<rho> \<triangleleft>\<triangleright>\<^sup>* \<sigma>\<close>
    have "\<rho>(v := x) \<triangleleft>\<triangleright>\<^sup>* \<sigma>(v := y)"
      by (auto 1 4)
    hence "\<lbrakk>e\<rbrakk>\<^bsub>\<rho>(v := x)\<^esub> \<triangleleft>\<triangleright> (\<N>\<lbrakk>e\<rbrakk>\<^bsub>\<sigma>(v := y)\<^esub>)\<cdot>C\<^sup>\<infinity>"
      by (rule Lam.hyps)
  }
  thus ?case by auto
next
  case (App e v \<rho> \<sigma>)
  hence App': "\<lbrakk>e\<rbrakk>\<^bsub>\<rho>\<^esub> \<triangleleft>\<triangleright> (\<N>\<lbrakk>e\<rbrakk>\<^bsub>\<sigma>\<^esub>)\<cdot>C\<^sup>\<infinity>" by auto
  thus ?case
  proof (cases rule: slimilar_bot_cases)
    case (Fn f g)
    from \<open>\<rho> \<triangleleft>\<triangleright>\<^sup>* \<sigma>\<close>
    have "\<rho> v \<triangleleft>\<triangleright> (\<sigma> v)\<cdot>C\<^sup>\<infinity>"  by auto
    thus ?thesis using Fn App' by auto
  qed auto
next
  case (Bool b)
  thus "\<lbrakk>Bool b\<rbrakk>\<^bsub>\<rho>\<^esub> \<triangleleft>\<triangleright> (\<N>\<lbrakk>Bool b\<rbrakk>\<^bsub>\<sigma>\<^esub>)\<cdot>C\<^sup>\<infinity>" by auto
next
  case (IfThenElse scrut e\<^sub>1 e\<^sub>2)
  hence IfThenElse':
    "\<lbrakk> scrut \<rbrakk>\<^bsub>\<rho>\<^esub> \<triangleleft>\<triangleright> (\<N>\<lbrakk> scrut \<rbrakk>\<^bsub>\<sigma>\<^esub>)\<cdot>C\<^sup>\<infinity>"
    "\<lbrakk> e\<^sub>1 \<rbrakk>\<^bsub>\<rho>\<^esub> \<triangleleft>\<triangleright> (\<N>\<lbrakk> e\<^sub>1 \<rbrakk>\<^bsub>\<sigma>\<^esub>)\<cdot>C\<^sup>\<infinity>"
    "\<lbrakk> e\<^sub>2 \<rbrakk>\<^bsub>\<rho>\<^esub> \<triangleleft>\<triangleright> (\<N>\<lbrakk> e\<^sub>2 \<rbrakk>\<^bsub>\<sigma>\<^esub>)\<cdot>C\<^sup>\<infinity>" by auto
  from IfThenElse'(1)
  show ?case
  proof (cases rule: slimilar_bot_cases)
    case (bool b)
    thus ?thesis using IfThenElse' by auto
  qed auto
next
  case (Let as e \<rho> \<sigma>)
  have "\<lbrace>as\<rbrace>\<rho> \<triangleleft>\<triangleright>\<^sup>* \<N>\<lbrace>as\<rbrace>\<sigma>"
  proof (rule parallel_HSem_ind_different_ESem[OF pointwise_adm[OF similar_admI] fun_similar_fmap_bottom])
    fix \<rho>' :: "var \<Rightarrow> Value" and \<sigma>' :: "var \<Rightarrow> C \<rightarrow> CValue"
    assume "\<rho>' \<triangleleft>\<triangleright>\<^sup>* \<sigma>'"
    show "\<rho> ++\<^bsub>domA as\<^esub> \<^bold>\<lbrakk> as \<^bold>\<rbrakk>\<^bsub>\<rho>'\<^esub> \<triangleleft>\<triangleright>\<^sup>* \<sigma> ++\<^bsub>domA as\<^esub> evalHeap as (\<lambda>e. \<N>\<lbrakk> e \<rbrakk>\<^bsub>\<sigma>'\<^esub>)"
    proof(rule pointwiseI, goal_cases)
      case (1 x)
      show ?case using \<open>\<rho> \<triangleleft>\<triangleright>\<^sup>* \<sigma>\<close>
        by (auto simp add: lookup_override_on_eq lookupEvalHeap elim: Let(1)[OF _  \<open>\<rho>' \<triangleleft>\<triangleright>\<^sup>* \<sigma>'\<close>] )
    qed
  qed auto
  hence "\<lbrakk>e\<rbrakk>\<^bsub>\<lbrace>as\<rbrace>\<rho>\<^esub> \<triangleleft>\<triangleright> (\<N>\<lbrakk>e\<rbrakk>\<^bsub>\<N>\<lbrace>as\<rbrace>\<sigma>\<^esub>)\<cdot>C\<^sup>\<infinity>" by (rule Let(2))
  thus ?case by simp
qed

corollary evalHeap_similar:
  "\<And>y z. y \<triangleleft>\<triangleright>\<^sup>* z \<Longrightarrow> \<^bold>\<lbrakk> \<Gamma> \<^bold>\<rbrakk>\<^bsub>y\<^esub> \<triangleleft>\<triangleright>\<^sup>* \<^bold>\<N>\<lbrakk> \<Gamma> \<^bold>\<rbrakk>\<^bsub>z\<^esub>"
  by (rule pointwiseI)
     (case_tac "x \<in> domA \<Gamma>", auto simp add: lookupEvalHeap denotational_semantics_similar)

theorem heaps_similar: "\<lbrace>\<Gamma>\<rbrace> \<triangleleft>\<triangleright>\<^sup>* \<N>\<lbrace>\<Gamma>\<rbrace>"
  by (rule parallel_HSem_ind_different_ESem[OF pointwise_adm[OF similar_admI]])
     (auto simp add: evalHeap_similar)

end
