theory "Abstract-Denotational-Props"
  imports AbstractDenotational Substitution
begin

context semantic_domain
begin

subsubsection \<open>The semantics ignores fresh variables\<close>

lemma ESem_considers_fv': "\<lbrakk> e \<rbrakk>\<^bsub>\<rho>\<^esub> = \<lbrakk> e \<rbrakk>\<^bsub>\<rho> f|` (fv e)\<^esub>"
proof (induct e arbitrary: \<rho> rule:exp_induct)
  case Var
  show ?case by simp
next
  have [simp]: "\<And> S x. S \<inter> insert x S = S" by auto
  case App
  show ?case
    by (simp, subst (1 2) App, simp)
next
  case (Lam x e)
  show ?case by simp
next
  case (IfThenElse scrut e\<^sub>1 e\<^sub>2)
  have [simp]: "(fv scrut \<inter> (fv scrut \<union> fv e\<^sub>1 \<union> fv e\<^sub>2)) = fv scrut" by auto
  have [simp]: "(fv e\<^sub>1 \<inter> (fv scrut \<union> fv e\<^sub>1 \<union> fv e\<^sub>2)) = fv e\<^sub>1" by auto
  have [simp]: "(fv e\<^sub>2 \<inter> (fv scrut \<union> fv e\<^sub>1 \<union> fv e\<^sub>2)) = fv e\<^sub>2" by auto
  show ?case
    apply simp
    apply (subst (1 2) IfThenElse(1))
    apply (subst (1 2) IfThenElse(2))
    apply (subst (1 2) IfThenElse(3))
    apply (simp)
    done
next
  case (Let as e)

  have "\<lbrakk>e\<rbrakk>\<^bsub>\<lbrace>as\<rbrace>\<rho>\<^esub> = \<lbrakk>e\<rbrakk>\<^bsub>(\<lbrace>as\<rbrace>\<rho>) f|` (fv as \<union> fv e)\<^esub>"
    apply (subst (1 2) Let(2))
    apply simp
    apply (metis inf_sup_absorb sup_commute)
    done
  also
  have "fv as \<subseteq> fv as \<union> fv e" by (rule inf_sup_ord(3))
  hence "(\<lbrace>as\<rbrace>\<rho>) f|` (fv as \<union> fv e) = \<lbrace>as\<rbrace>(\<rho> f|` (fv as \<union> fv e))"
     by (rule HSem_ignores_fresh_restr'[OF _ Let(1)])
  also
  have "\<lbrace>as\<rbrace>(\<rho> f|` (fv as \<union> fv e)) = \<lbrace>as\<rbrace>\<rho> f|` (fv as \<union> fv e - domA as)"
    by (rule HSem_restr_cong) (auto simp add: lookup_env_restr_eq)
  finally
  show ?case by simp
qed auto

sublocale has_ignore_fresh_ESem ESem
  by standard (rule fv_supp_exp, rule ESem_considers_fv')

subsubsection \<open>Nicer equations for ESem, without freshness requirements\<close>

lemma ESem_Lam[simp]: "\<lbrakk> Lam [x]. e \<rbrakk>\<^bsub>\<rho>\<^esub> = tick \<cdot> (Fn \<cdot> (\<Lambda> v. \<lbrakk> e \<rbrakk>\<^bsub>\<rho>(x := v)\<^esub>))"
proof-
  have *: "\<And> v. ((\<rho> f|` (fv e - {x}))(x := v)) f|` fv e = (\<rho>(x := v)) f|` fv e"
    by (rule ext) (auto simp add: lookup_env_restr_eq)

  have "\<lbrakk> Lam [x]. e \<rbrakk>\<^bsub>\<rho>\<^esub> = \<lbrakk> Lam [x]. e \<rbrakk>\<^bsub>env_delete x \<rho>\<^esub>"
    by (rule ESem_fresh_cong) simp
  also have "\<dots> = tick \<cdot> (Fn \<cdot> (\<Lambda> v. \<lbrakk> e \<rbrakk>\<^bsub>(\<rho> f|` (fv e - {x}))(x := v)\<^esub>))"
    by simp
  also have "\<dots> = tick \<cdot> (Fn \<cdot> (\<Lambda> v. \<lbrakk> e \<rbrakk>\<^bsub>((\<rho> f|` (fv e - {x}))(x := v)) f|` fv e\<^esub>))"
    by (subst  ESem_considers_fv, rule)
  also have "\<dots> = tick \<cdot> (Fn \<cdot> (\<Lambda> v. \<lbrakk> e \<rbrakk>\<^bsub>\<rho>(x := v) f|` fv e\<^esub>))"
    unfolding *..
  also have "\<dots> = tick \<cdot> (Fn \<cdot> (\<Lambda> v. \<lbrakk> e \<rbrakk>\<^bsub>\<rho>(x := v)\<^esub>))"
    unfolding  ESem_considers_fv[symmetric]..
  finally show ?thesis.
qed
declare ESem.simps(1)[simp del]

lemma ESem_Let[simp]: "\<lbrakk>Let as body\<rbrakk>\<^bsub>\<rho>\<^esub> = tick \<cdot> (\<lbrakk>body\<rbrakk>\<^bsub>\<lbrace>as\<rbrace>\<rho>\<^esub>)"
proof-
  have "\<lbrakk> Let as body \<rbrakk>\<^bsub>\<rho>\<^esub> = tick \<cdot> (\<lbrakk>body\<rbrakk>\<^bsub>\<lbrace>as\<rbrace>(\<rho> f|` fv (Let as body))\<^esub>)" 
    by simp
  also have "\<lbrace>as\<rbrace>(\<rho> f|` fv(Let as body)) = \<lbrace>as\<rbrace>(\<rho> f|` (fv as \<union> fv body))" 
    by (rule HSem_restr_cong) (auto simp add: lookup_env_restr_eq)
  also have "\<dots> = (\<lbrace>as\<rbrace>\<rho>) f|` (fv as \<union> fv body)"
    by (rule HSem_ignores_fresh_restr'[symmetric, OF _ ESem_considers_fv]) simp
  also have "\<lbrakk>body\<rbrakk>\<^bsub>\<dots>\<^esub> = \<lbrakk>body\<rbrakk>\<^bsub>\<lbrace>as\<rbrace>\<rho>\<^esub>"
    by (rule ESem_fresh_cong) (auto simp add: lookup_env_restr_eq)
  finally show ?thesis.
qed
declare ESem.simps(4)[simp del]


subsubsection \<open>Denotation of Substitution\<close>

lemma ESem_subst_same: "\<rho> x = \<rho> y \<Longrightarrow>  \<lbrakk> e \<rbrakk>\<^bsub>\<rho>\<^esub> = \<lbrakk> e[x::= y] \<rbrakk>\<^bsub>\<rho>\<^esub>"
  and 
  "\<rho> x = \<rho> y  \<Longrightarrow>  (\<^bold>\<lbrakk> as \<^bold>\<rbrakk>\<^bsub>\<rho>\<^esub>) = \<^bold>\<lbrakk> as[x::h=y] \<^bold>\<rbrakk>\<^bsub>\<rho>\<^esub>"
proof (nominal_induct e and as avoiding: x y arbitrary: \<rho> and \<rho> rule:exp_heap_strong_induct)
case Var thus ?case by auto
next
case App
  from App(1)[OF App(2)] App(2)
  show ?case by auto
next
case (Let as exp x y \<rho>)
  from \<open>atom ` domA as \<sharp>* x\<close> \<open>atom ` domA as  \<sharp>* y\<close> 
  have "x \<notin> domA as" "y \<notin> domA as"
    by (metis fresh_star_at_base imageI)+
  hence [simp]:"domA (as[x::h=y]) = domA as" 
    by (metis bn_subst)

  from \<open>\<rho> x = \<rho> y\<close>
  have "(\<lbrace>as\<rbrace>\<rho>) x = (\<lbrace>as\<rbrace>\<rho>) y"
    using \<open>x \<notin> domA as\<close> \<open>y \<notin> domA as\<close>
    by (simp add: lookup_HSem_other)
  hence "\<lbrakk>exp\<rbrakk>\<^bsub>\<lbrace>as\<rbrace>\<rho>\<^esub> = \<lbrakk>exp[x::=y]\<rbrakk>\<^bsub>\<lbrace>as\<rbrace>\<rho>\<^esub>"
    by (rule Let)
  moreover
  from \<open>\<rho> x = \<rho> y\<close>
  have "\<lbrace>as\<rbrace>\<rho> = \<lbrace>as[x::h=y]\<rbrace>\<rho>" and "(\<lbrace>as\<rbrace>\<rho>) x = (\<lbrace>as[x::h=y]\<rbrace>\<rho>) y"
    apply (induction rule: parallel_HSem_ind)
    apply (intro adm_lemmas cont2cont cont2cont_fun)
    apply simp
    apply simp
    apply simp
    apply (erule arg_cong[OF Let(3)])
    using \<open>x \<notin> domA as\<close> \<open>y \<notin> domA as\<close>
    apply simp
    done
  ultimately
  show ?case using Let(1,2,3) by (simp add: fresh_star_Pair)
next
case (Lam var exp x y \<rho>)
  from \<open>\<rho> x = \<rho> y\<close>
  have "\<And>v. (\<rho>(var := v)) x = (\<rho>(var := v)) y"
    using Lam(1,2) by (simp add: fresh_at_base)
  hence "\<And> v. \<lbrakk>exp\<rbrakk>\<^bsub>\<rho>(var := v)\<^esub> = \<lbrakk>exp[x::=y]\<rbrakk>\<^bsub>\<rho>(var := v)\<^esub>"
    by (rule Lam)
  thus ?case using Lam(1,2) by simp
next
case IfThenElse
  from IfThenElse(1)[OF IfThenElse(4)] IfThenElse(2)[OF IfThenElse(4)] IfThenElse(3)[OF IfThenElse(4)]
  show ?case
    by simp
next
case Nil thus ?case by auto
next
case Cons
  from Cons(1,2)[OF Cons(3)] Cons(3)
  show ?case by auto
qed auto

lemma ESem_subst:
  shows "\<lbrakk> e \<rbrakk>\<^bsub>\<sigma>(x := \<sigma> y)\<^esub> = \<lbrakk> e[x::= y] \<rbrakk>\<^bsub>\<sigma>\<^esub>"
proof(cases "x = y")
  case False
  hence [simp]: "x \<notin> fv e[x::=y]" by (auto simp add: fv_def supp_subst supp_at_base dest: subsetD[OF supp_subst]) 

  have "\<lbrakk> e \<rbrakk>\<^bsub>\<sigma>(x := \<sigma> y)\<^esub> = \<lbrakk> e[x::= y] \<rbrakk>\<^bsub>\<sigma>(x := \<sigma> y)\<^esub>"
    by (rule ESem_subst_same) simp
  also have "\<dots> = \<lbrakk> e[x::= y] \<rbrakk>\<^bsub>\<sigma>\<^esub>"
    by (rule ESem_fresh_cong) simp
  finally
  show ?thesis.
next
  case True
  thus ?thesis by simp
qed

end

end
