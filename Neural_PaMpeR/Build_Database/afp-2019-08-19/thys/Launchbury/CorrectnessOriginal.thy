theory CorrectnessOriginal
imports Denotational Launchbury
begin

text \<open>
This is the main correctness theorem, Theorem 2 from \cite{launchbury}.
\<close>

(* Another possible invariant seems to be: "edom \<rho> - domA \<Gamma> \<subseteq> set L" *)

theorem correctness:
  assumes "\<Gamma> : e \<Down>\<^bsub>L\<^esub> \<Delta> : v"
  and     "fv (\<Gamma>, e) \<subseteq> set L \<union> domA \<Gamma>"
  shows   "\<lbrakk>e\<rbrakk>\<^bsub>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub> = \<lbrakk>v\<rbrakk>\<^bsub>\<lbrace>\<Delta>\<rbrace>\<rho>\<^esub>"
  and     "(\<lbrace>\<Gamma>\<rbrace>\<rho>) f|` domA \<Gamma> = (\<lbrace>\<Delta>\<rbrace>\<rho>) f|` domA \<Gamma>"
  using assms
proof(nominal_induct arbitrary: \<rho> rule:reds.strong_induct)
case Lambda
  case 1 show ?case..
  case 2 show ?case..
next
case (Application y \<Gamma> e x L \<Delta> \<Theta> v e')
  have Gamma_subset: "domA \<Gamma> \<subseteq> domA \<Delta>"
    by (rule reds_doesnt_forget[OF Application.hyps(8)])

  case 1
  hence prem1: "fv (\<Gamma>, e) \<subseteq> set L \<union> domA \<Gamma>" and  "x \<in> set L \<union> domA \<Gamma>" by auto
  moreover
  note reds_pres_closed[OF Application.hyps(8) prem1]
  moreover
  note reds_doesnt_forget[OF Application.hyps(8)] 
  moreover
  have "fv (e'[y::=x]) \<subseteq> fv (Lam [y]. e') \<union> {x}"
    by (auto simp add: fv_subst_eq)
  ultimately
  have prem2: "fv (\<Delta>, e'[y::=x]) \<subseteq> set L \<union> domA \<Delta>" by auto
  
  have *: "(\<lbrace>\<Gamma>\<rbrace>\<rho>) x = (\<lbrace>\<Delta>\<rbrace>\<rho>) x"
  proof(cases "x \<in> domA \<Gamma>")
    case True
    from Application.hyps(10)[OF prem1, where \<rho> = \<rho>]
    have "((\<lbrace>\<Gamma>\<rbrace>\<rho>) f|` domA \<Gamma>) x  = ((\<lbrace>\<Delta>\<rbrace>\<rho>) f|` domA \<Gamma>) x" by simp
    with True show ?thesis by simp
  next
    case False
    from False \<open>x \<in> set L \<union> domA \<Gamma>\<close> reds_avoids_live[OF Application.hyps(8)] 
    show ?thesis by (auto simp add: lookup_HSem_other)
  qed

  text_raw \<open>% nice proof start\<close>
  have "\<lbrakk> App e x \<rbrakk>\<^bsub>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub> = (\<lbrakk> e \<rbrakk>\<^bsub>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub>) \<down>Fn (\<lbrace>\<Gamma>\<rbrace>\<rho>) x"
    by simp
  also have "\<dots> = (\<lbrakk> Lam [y]. e' \<rbrakk>\<^bsub>\<lbrace>\<Delta>\<rbrace>\<rho>\<^esub>) \<down>Fn (\<lbrace>\<Gamma>\<rbrace>\<rho>) x"
    using Application.hyps(9)[OF prem1] by simp
  also have "\<dots> = (\<lbrakk> Lam [y]. e' \<rbrakk>\<^bsub>\<lbrace>\<Delta>\<rbrace>\<rho>\<^esub>) \<down>Fn (\<lbrace>\<Delta>\<rbrace>\<rho>) x"
    unfolding *..
  also have "\<dots> = (Fn\<cdot>(\<Lambda> z. \<lbrakk> e' \<rbrakk>\<^bsub>(\<lbrace>\<Delta>\<rbrace>\<rho>)(y := z)\<^esub>)) \<down>Fn (\<lbrace>\<Delta>\<rbrace>\<rho>) x"
    by simp
  also have "\<dots> = \<lbrakk> e' \<rbrakk>\<^bsub>(\<lbrace>\<Delta>\<rbrace>\<rho>)(y := (\<lbrace>\<Delta>\<rbrace>\<rho>) x)\<^esub>"
    by simp
  also have "\<dots> = \<lbrakk> e'[y ::= x] \<rbrakk>\<^bsub>\<lbrace>\<Delta>\<rbrace>\<rho>\<^esub>"
    unfolding ESem_subst..
  also have "\<dots> = \<lbrakk> v \<rbrakk>\<^bsub>\<lbrace>\<Theta>\<rbrace>\<rho>\<^esub>"
    by (rule Application.hyps(12)[OF prem2])
  finally
  show "\<lbrakk> App e x \<rbrakk>\<^bsub>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub> = \<lbrakk> v \<rbrakk>\<^bsub>\<lbrace>\<Theta>\<rbrace>\<rho>\<^esub>".
  text_raw \<open>% nice proof end\<close>
  
  show "(\<lbrace>\<Gamma>\<rbrace>\<rho>) f|` domA \<Gamma> = (\<lbrace>\<Theta>\<rbrace>\<rho>) f|` domA \<Gamma>"
    using Application.hyps(10)[OF prem1]
          env_restr_eq_subset[OF Gamma_subset Application.hyps(13)[OF prem2]]
    by (rule trans)
next
case (Variable \<Gamma> x e L \<Delta> v)
  hence [simp]:"x \<in> domA \<Gamma>" by (metis domA_from_set map_of_SomeD)

  let ?\<Gamma> = "delete x \<Gamma>"

  case 2
  have "x \<notin> domA \<Delta>"
    by (rule reds_avoids_live[OF Variable.hyps(2)], simp_all)

  have subset: "domA ?\<Gamma> \<subseteq> domA \<Delta>"
    by (rule reds_doesnt_forget[OF Variable.hyps(2)])

  let "?new" = "domA \<Delta> - domA \<Gamma>"
  have "fv (?\<Gamma>, e) \<union> {x} \<subseteq> fv (\<Gamma>, Var x)"
    by (rule fv_delete_heap[OF \<open>map_of \<Gamma> x = Some e\<close>])
  hence prem: "fv (?\<Gamma>, e) \<subseteq> set (x # L) \<union> domA ?\<Gamma>" using 2 by auto
  hence fv_subset: "fv (?\<Gamma>, e) - domA ?\<Gamma> \<subseteq> - ?new"
    using reds_avoids_live'[OF Variable.hyps(2)] by auto

  have "domA \<Gamma> \<subseteq> (-?new)" by auto

  have "\<lbrace>\<Gamma>\<rbrace>\<rho> = \<lbrace>(x,e) # ?\<Gamma>\<rbrace>\<rho>"
    by (rule HSem_reorder[OF map_of_delete_insert[symmetric, OF Variable(1)]])
  also have "\<dots> = (\<mu> \<rho>'. (\<rho> ++\<^bsub>(domA ?\<Gamma>)\<^esub> (\<lbrace>?\<Gamma>\<rbrace>\<rho>'))( x := \<lbrakk> e \<rbrakk>\<^bsub>\<rho>'\<^esub>))"
    by (rule iterative_HSem, simp)
  also have "\<dots> = (\<mu> \<rho>'. (\<rho> ++\<^bsub>(domA ?\<Gamma>)\<^esub> (\<lbrace>?\<Gamma>\<rbrace>\<rho>'))( x := \<lbrakk> e \<rbrakk>\<^bsub>\<lbrace>?\<Gamma>\<rbrace>\<rho>'\<^esub>))"
    by (rule iterative_HSem', simp)
  finally
  have "(\<lbrace>\<Gamma>\<rbrace>\<rho>)f|` (- ?new) = (...) f|` (- ?new)" by simp
  also have "\<dots> = (\<mu> \<rho>'. (\<rho> ++\<^bsub>domA \<Delta>\<^esub> (\<lbrace>\<Delta>\<rbrace>\<rho>'))( x := \<lbrakk> v \<rbrakk>\<^bsub>\<lbrace>\<Delta>\<rbrace>\<rho>'\<^esub>)) f|` (- ?new)"
  proof (induction rule: parallel_fix_ind[where P ="\<lambda> x y. x f|` (- ?new) = y f|` (- ?new)"])
    case 1 show ?case by simp
  next
    case 2 show ?case ..
  next
    case (3 \<sigma> \<sigma>')
    hence "\<lbrakk> e \<rbrakk>\<^bsub>\<lbrace>?\<Gamma>\<rbrace>\<sigma>\<^esub> = \<lbrakk> e \<rbrakk>\<^bsub>\<lbrace>?\<Gamma>\<rbrace>\<sigma>'\<^esub>"
      and "(\<lbrace>?\<Gamma>\<rbrace>\<sigma>) f|` domA ?\<Gamma> = (\<lbrace>?\<Gamma>\<rbrace>\<sigma>') f|` domA ?\<Gamma>"
      using fv_subset by (auto intro: ESem_fresh_cong HSem_fresh_cong  env_restr_eq_subset[OF _ 3])
    from trans[OF this(1) Variable(3)[OF prem]] trans[OF this(2) Variable(4)[OF prem]]
    have  "\<lbrakk> e \<rbrakk>\<^bsub>\<lbrace>?\<Gamma>\<rbrace>\<sigma>\<^esub> = \<lbrakk> v \<rbrakk>\<^bsub>\<lbrace>\<Delta>\<rbrace>\<sigma>'\<^esub>"
       and "(\<lbrace>?\<Gamma>\<rbrace>\<sigma>) f|` domA ?\<Gamma> = (\<lbrace>\<Delta>\<rbrace>\<sigma>') f|` domA ?\<Gamma>".
    thus ?case
      using subset
      by (fastforce simp add: lookup_override_on_eq  lookup_env_restr_eq dest: env_restr_eqD )
  qed
  also have "\<dots> = (\<mu> \<rho>'. (\<rho> ++\<^bsub>domA \<Delta>\<^esub> (\<lbrace>\<Delta>\<rbrace>\<rho>'))( x := \<lbrakk> v \<rbrakk>\<^bsub>\<rho>'\<^esub>)) f|` (-?new)"
    by (rule arg_cong[OF iterative_HSem'[symmetric], OF \<open>x \<notin> domA \<Delta>\<close>])
  also have "\<dots> = (\<lbrace>(x,v) # \<Delta>\<rbrace>\<rho>)  f|` (-?new)"
    by (rule arg_cong[OF iterative_HSem[symmetric], OF \<open>x \<notin> domA \<Delta>\<close>])
  finally
  show le: ?case by (rule env_restr_eq_subset[OF \<open>domA \<Gamma> \<subseteq> (-?new)\<close>])

  have "\<lbrakk> Var x \<rbrakk>\<^bsub>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub> = \<lbrakk> Var x \<rbrakk>\<^bsub>\<lbrace>(x, v) # \<Delta>\<rbrace>\<rho>\<^esub>"
    using env_restr_eqD[OF le, where x = x]
    by simp
  also have "\<dots> = \<lbrakk> v \<rbrakk>\<^bsub>\<lbrace>(x, v) # \<Delta>\<rbrace>\<rho>\<^esub>"
    by (auto simp add: lookup_HSem_heap)
  finally
  show "\<lbrakk> Var x \<rbrakk>\<^bsub>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub> = \<lbrakk> v \<rbrakk>\<^bsub>\<lbrace>(x, v) # \<Delta>\<rbrace>\<rho>\<^esub>".
next
case (Bool b)
  case 1
  show ?case by simp
  case 2
  show ?case by simp
next
case (IfThenElse \<Gamma> scrut L \<Delta> b e\<^sub>1 e\<^sub>2 \<Theta> v)
  have Gamma_subset: "domA \<Gamma> \<subseteq> domA \<Delta>"
    by (rule reds_doesnt_forget[OF IfThenElse.hyps(1)])

  let ?e = "if b then e\<^sub>1 else e\<^sub>2"

  case 1

  hence prem1: "fv (\<Gamma>, scrut) \<subseteq> set L \<union> domA \<Gamma>"
    and prem2: "fv (\<Delta>, ?e) \<subseteq> set L \<union> domA \<Delta>"
    and "fv ?e \<subseteq> domA \<Gamma> \<union> set L"
    using new_free_vars_on_heap[OF IfThenElse.hyps(1)] Gamma_subset by auto

  have "\<lbrakk> (scrut ? e\<^sub>1 : e\<^sub>2) \<rbrakk>\<^bsub>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub> = B_project\<cdot>(\<lbrakk> scrut \<rbrakk>\<^bsub>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub>)\<cdot>(\<lbrakk> e\<^sub>1 \<rbrakk>\<^bsub>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub>)\<cdot>(\<lbrakk> e\<^sub>2 \<rbrakk>\<^bsub>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub>)" by simp
  also have "\<dots> = B_project\<cdot>(\<lbrakk> Bool b \<rbrakk>\<^bsub>\<lbrace>\<Delta>\<rbrace>\<rho>\<^esub>)\<cdot>(\<lbrakk> e\<^sub>1 \<rbrakk>\<^bsub>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub>)\<cdot>(\<lbrakk> e\<^sub>2 \<rbrakk>\<^bsub>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub>)"
    unfolding IfThenElse.hyps(2)[OF prem1]..
  also have "\<dots> = \<lbrakk> ?e \<rbrakk>\<^bsub>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub>" by simp
  also have "\<dots> = \<lbrakk> ?e \<rbrakk>\<^bsub>\<lbrace>\<Delta>\<rbrace>\<rho>\<^esub>"
    proof(rule ESem_fresh_cong_subset[OF  \<open>fv ?e \<subseteq> domA \<Gamma> \<union> set L\<close> env_restr_eqI])
      fix x
      assume "x \<in> domA \<Gamma> \<union> set L"
      thus "(\<lbrace>\<Gamma>\<rbrace>\<rho>) x = (\<lbrace>\<Delta>\<rbrace>\<rho>) x"
      proof(cases "x \<in> domA \<Gamma>")
        assume "x \<in> domA \<Gamma>"
        from IfThenElse.hyps(3)[OF prem1]
        have "((\<lbrace>\<Gamma>\<rbrace>\<rho>) f|` domA \<Gamma>) x  = ((\<lbrace>\<Delta>\<rbrace>\<rho>) f|` domA \<Gamma>) x" by simp
        with \<open>x \<in> domA \<Gamma>\<close> show ?thesis by simp
      next
        assume "x \<notin> domA \<Gamma>"
        from this \<open>x \<in> domA \<Gamma> \<union> set L\<close> reds_avoids_live[OF IfThenElse.hyps(1)]
        show ?thesis
          by (simp add: lookup_HSem_other)
      qed
    qed
  also have "\<dots> = \<lbrakk> v \<rbrakk>\<^bsub>\<lbrace>\<Theta>\<rbrace>\<rho>\<^esub>"
    unfolding IfThenElse.hyps(5)[OF prem2]..
  finally
  show ?case.
  thm env_restr_eq_subset
  show "(\<lbrace>\<Gamma>\<rbrace>\<rho>) f|` domA \<Gamma> = (\<lbrace>\<Theta>\<rbrace>\<rho>) f|` domA \<Gamma>"
    using IfThenElse.hyps(3)[OF prem1]
          env_restr_eq_subset[OF Gamma_subset IfThenElse.hyps(6)[OF prem2]]
    by (rule trans)
next
case (Let as \<Gamma> L body \<Delta> v)
  case 1
  { fix a
    assume a: "a \<in> domA  as"
    have "atom a \<sharp> \<Gamma>" 
      by (rule Let(1)[unfolded fresh_star_def, rule_format, OF imageI[OF a]])
    hence "a \<notin> domA \<Gamma>"
      by (metis domA_not_fresh)
  }
  note * = this

  
  have "fv (as @ \<Gamma>, body) - domA (as @ \<Gamma>) \<subseteq>  fv (\<Gamma>, Let as body) - domA \<Gamma>"
    by auto
  with 1 have prem: "fv (as @ \<Gamma>, body) \<subseteq> set L \<union> domA (as @ \<Gamma>)" by auto
  
  have f1: "atom ` domA as \<sharp>* \<Gamma>"
    using Let(1) by (simp add: set_bn_to_atom_domA)

  have "\<lbrakk> Let as body \<rbrakk>\<^bsub>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub> = \<lbrakk> body \<rbrakk>\<^bsub>\<lbrace>as\<rbrace>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub>"
    by (simp)
  also have "\<dots> = \<lbrakk> body \<rbrakk>\<^bsub>\<lbrace>as @ \<Gamma>\<rbrace>\<rho>\<^esub>"
    by (rule arg_cong[OF HSem_merge[OF f1]])
  also have "\<dots> = \<lbrakk> v \<rbrakk>\<^bsub>\<lbrace>\<Delta>\<rbrace>\<rho>\<^esub>"
    by (rule Let.hyps(4)[OF prem])
  finally
  show ?case.

  have "(\<lbrace>\<Gamma>\<rbrace>\<rho>) f|` (domA \<Gamma>) = (\<lbrace>as\<rbrace>(\<lbrace>\<Gamma>\<rbrace>\<rho>)) f|` (domA \<Gamma>)"
    apply (rule ext)
    apply (case_tac "x \<in> domA as")
    apply (auto simp add: lookup_HSem_other lookup_env_restr_eq *)
    done
  also have "\<dots> = (\<lbrace>as @ \<Gamma>\<rbrace>\<rho>) f|` (domA \<Gamma>)"
    by (rule arg_cong[OF HSem_merge[OF f1]])
  also have "\<dots> = (\<lbrace>\<Delta>\<rbrace>\<rho>) f|` (domA \<Gamma>)"
    by (rule env_restr_eq_subset[OF _ Let.hyps(5)[OF prem]]) simp
  finally
  show "(\<lbrace>\<Gamma>\<rbrace>\<rho>) f|` domA \<Gamma> = (\<lbrace>\<Delta>\<rbrace>\<rho>) f|` domA \<Gamma>".
qed

end
