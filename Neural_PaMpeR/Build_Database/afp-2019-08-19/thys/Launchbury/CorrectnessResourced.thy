theory CorrectnessResourced
  imports ResourcedDenotational Launchbury
begin

theorem correctness:
  assumes "\<Gamma> : e \<Down>\<^bsub>L\<^esub> \<Delta> : z"
  and     "fv (\<Gamma>, e) \<subseteq> set L \<union> domA \<Gamma>"
  shows   "\<N>\<lbrakk>e\<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub> \<sqsubseteq> \<N>\<lbrakk>z\<rbrakk>\<^bsub>\<N>\<lbrace>\<Delta>\<rbrace>\<rho>\<^esub>" and "(\<N>\<lbrace>\<Gamma>\<rbrace>\<rho>) f|` domA \<Gamma> \<sqsubseteq> (\<N>\<lbrace>\<Delta>\<rbrace>\<rho>) f|` domA \<Gamma>"
  using assms
proof(nominal_induct arbitrary: \<rho> rule:reds.strong_induct)
case Lambda
  case 1 show ?case..
  case 2 show ?case..
next
case (Application y \<Gamma> e x L \<Delta> \<Theta> z e')
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

  
  have *: "(\<N>\<lbrace>\<Gamma>\<rbrace>\<rho>) x \<sqsubseteq> (\<N>\<lbrace>\<Delta>\<rbrace>\<rho>) x"
  proof(cases "x \<in> domA \<Gamma>")
    case True
    thus ?thesis
      using fun_belowD[OF Application.hyps(10)[OF prem1], where \<rho>1 = \<rho> and x = x]
      by simp
  next
    case False
    from False \<open>x \<in> set L \<union> domA \<Gamma>\<close> reds_avoids_live[OF Application.hyps(8)] 
    show ?thesis by (auto simp add: lookup_HSem_other)
  qed

  {
  fix r
  have "(\<N>\<lbrakk> App e x \<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub>)\<cdot>r \<sqsubseteq> ((\<N>\<lbrakk> e \<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub>)\<cdot>r \<down>CFn (\<N>\<lbrace>\<Gamma>\<rbrace>\<rho>) x)\<cdot>r"
    by (rule CEApp_no_restr)
  also have "((\<N>\<lbrakk> e \<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub>)) \<sqsubseteq> ((\<N>\<lbrakk> Lam [y]. e' \<rbrakk>\<^bsub>\<N>\<lbrace>\<Delta>\<rbrace>\<rho>\<^esub>))"
    using Application.hyps(9)[OF prem1].
  also note \<open>((\<N>\<lbrace>\<Gamma>\<rbrace>\<rho>) x) \<sqsubseteq> (\<N>\<lbrace>\<Delta>\<rbrace>\<rho>) x\<close>
  also have "(\<N>\<lbrakk> Lam [y]. e' \<rbrakk>\<^bsub>\<N>\<lbrace>\<Delta>\<rbrace>\<rho>\<^esub>)\<cdot>r \<sqsubseteq> (CFn\<cdot>(\<Lambda> v. (\<N>\<lbrakk> e' \<rbrakk>\<^bsub>(\<N>\<lbrace>\<Delta>\<rbrace>\<rho>)(y := v)\<^esub>)))"
    by (rule CELam_no_restr)
  also have "CFn\<cdot>(\<Lambda> v. (\<N>\<lbrakk> e' \<rbrakk>\<^bsub>(\<N>\<lbrace>\<Delta>\<rbrace>\<rho>)(y := v)\<^esub>)) \<down>CFn ((\<N>\<lbrace>\<Delta>\<rbrace>\<rho>) x) = (\<N>\<lbrakk> e' \<rbrakk>\<^bsub>(\<N>\<lbrace>\<Delta>\<rbrace>\<rho>)(y := (\<N>\<lbrace>\<Delta>\<rbrace>\<rho>) x)\<^esub>)"
    by simp
  also have "\<dots> = (\<N>\<lbrakk> e'[y ::= x] \<rbrakk>\<^bsub>(\<N>\<lbrace>\<Delta>\<rbrace>\<rho>)\<^esub>)"
    unfolding ESem_subst..
  also have "\<dots> \<sqsubseteq> \<N>\<lbrakk> z \<rbrakk>\<^bsub>\<N>\<lbrace>\<Theta>\<rbrace>\<rho>\<^esub>"
    using Application.hyps(12)[OF prem2].
  finally
  have "(\<N>\<lbrakk> App e x \<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub>)\<cdot>r \<sqsubseteq> (\<N>\<lbrakk> z \<rbrakk>\<^bsub>\<N>\<lbrace>\<Theta>\<rbrace>\<rho>\<^esub>)\<cdot>r" by this (intro cont2cont)+
  }
  thus ?case by (rule cfun_belowI)
  
  show "(\<N>\<lbrace>\<Gamma>\<rbrace>\<rho>) f|` (domA \<Gamma>) \<sqsubseteq> (\<N>\<lbrace>\<Theta>\<rbrace>\<rho>)  f|` (domA \<Gamma>)"
    using Application.hyps(10)[OF prem1]
          env_restr_below_subset[OF Gamma_subset Application.hyps(13)[OF prem2]]
    by (rule below_trans)
next
case (Variable \<Gamma> x e L \<Delta> z)
  hence [simp]:"x \<in> domA \<Gamma>"
    by (metis domA_from_set map_of_SomeD)

  case 2

  have "x \<notin> domA \<Delta>"
    by (rule reds_avoids_live[OF Variable.hyps(2)], simp_all)

  have subset: "domA (delete x \<Gamma>) \<subseteq> domA \<Delta>"
    by (rule reds_doesnt_forget[OF Variable.hyps(2)])

  let "?new" = "domA \<Delta> - domA \<Gamma>"
  have "fv (delete x \<Gamma>, e) \<union> {x} \<subseteq> fv (\<Gamma>, Var x)"
    by (rule fv_delete_heap[OF \<open>map_of \<Gamma> x = Some e\<close>])
  hence prem: "fv (delete x \<Gamma>, e) \<subseteq> set (x # L) \<union> domA (delete x \<Gamma>)" using 2 by auto
  hence fv_subset: "fv (delete x \<Gamma>, e) - domA (delete x \<Gamma>) \<subseteq> - ?new"
    using reds_avoids_live'[OF Variable.hyps(2)] by auto



  have "domA \<Gamma> \<subseteq> (-?new)" by auto


  have "\<N>\<lbrace>\<Gamma>\<rbrace>\<rho> = \<N>\<lbrace>(x,e) # delete x \<Gamma>\<rbrace>\<rho>"
    by (rule HSem_reorder[OF map_of_delete_insert[symmetric, OF Variable(1)]])
  also have "\<dots> = (\<mu> \<rho>'. (\<rho> ++\<^bsub>(domA (delete x \<Gamma>))\<^esub> (\<N>\<lbrace>delete x \<Gamma>\<rbrace>\<rho>'))( x := \<N>\<lbrakk> e \<rbrakk>\<^bsub>\<rho>'\<^esub>))"
    by (rule iterative_HSem, simp)
  also have "\<dots> = (\<mu> \<rho>'. (\<rho> ++\<^bsub>(domA (delete x \<Gamma>))\<^esub> (\<N>\<lbrace>delete x \<Gamma>\<rbrace>\<rho>'))( x := \<N>\<lbrakk> e \<rbrakk>\<^bsub>\<N>\<lbrace>delete x \<Gamma>\<rbrace>\<rho>'\<^esub>))"
    by (rule iterative_HSem', simp)
  finally
  have "(\<N>\<lbrace>\<Gamma>\<rbrace>\<rho>)f|` (- ?new) \<sqsubseteq> (...) f|` (- ?new)" by (rule ssubst) (rule below_refl)
  also have "\<dots> \<sqsubseteq> (\<mu> \<rho>'. (\<rho> ++\<^bsub>domA \<Delta>\<^esub> (\<N>\<lbrace>\<Delta>\<rbrace>\<rho>'))( x := \<N>\<lbrakk> z \<rbrakk>\<^bsub>\<N>\<lbrace>\<Delta>\<rbrace>\<rho>'\<^esub>)) f|` (- ?new)"
  proof (induction rule: parallel_fix_ind[where P ="\<lambda> x y. x f|` (- ?new) \<sqsubseteq> y f|` (- ?new)"])
    case 1 show ?case by simp
  next
    case 2 show ?case ..
  next
    case (3 \<sigma> \<sigma>')
    hence "\<N>\<lbrakk> e \<rbrakk>\<^bsub>\<N>\<lbrace>delete x \<Gamma>\<rbrace>\<sigma>\<^esub> \<sqsubseteq> \<N>\<lbrakk> e \<rbrakk>\<^bsub>\<N>\<lbrace>delete x \<Gamma>\<rbrace>\<sigma>'\<^esub>"
      and "(\<N>\<lbrace>delete x \<Gamma>\<rbrace>\<sigma>) f|` domA (delete x \<Gamma>) \<sqsubseteq> (\<N>\<lbrace>delete x \<Gamma>\<rbrace>\<sigma>') f|` domA (delete x \<Gamma>)"
      using fv_subset by (auto intro: ESem_fresh_cong_below HSem_fresh_cong_below  env_restr_below_subset[OF _ 3])
    from below_trans[OF this(1) Variable(3)[OF prem]] below_trans[OF this(2) Variable(4)[OF prem]]
    have  "\<N>\<lbrakk> e \<rbrakk>\<^bsub>\<N>\<lbrace>delete x \<Gamma>\<rbrace>\<sigma>\<^esub> \<sqsubseteq> \<N>\<lbrakk> z \<rbrakk>\<^bsub>\<N>\<lbrace>\<Delta>\<rbrace>\<sigma>'\<^esub>"
       and "(\<N>\<lbrace>delete x \<Gamma>\<rbrace>\<sigma>) f|` domA (delete x \<Gamma>) \<sqsubseteq> (\<N>\<lbrace>\<Delta>\<rbrace>\<sigma>') f|` domA (delete x \<Gamma>)".
    thus ?case
      using subset
      by (auto intro!: fun_belowI simp add: lookup_override_on_eq  lookup_env_restr_eq elim: env_restr_belowD)
  qed
  also have "\<dots> = (\<mu> \<rho>'. (\<rho> ++\<^bsub>domA \<Delta>\<^esub> (\<N>\<lbrace>\<Delta>\<rbrace>\<rho>'))( x := \<N>\<lbrakk> z \<rbrakk>\<^bsub>\<rho>'\<^esub>)) f|` (-?new)"
    by (rule arg_cong[OF iterative_HSem'[symmetric], OF \<open>x \<notin> domA \<Delta>\<close>])
  also have "\<dots> = (\<N>\<lbrace>(x,z) # \<Delta>\<rbrace>\<rho>)  f|` (-?new)"
    by (rule arg_cong[OF iterative_HSem[symmetric], OF \<open>x \<notin> domA \<Delta>\<close>])
  finally
  show le: ?case by (rule env_restr_below_subset[OF \<open>domA \<Gamma> \<subseteq> (-?new)\<close>]) (intro cont2cont)+

  have "\<N>\<lbrakk> Var x \<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub> \<sqsubseteq> (\<N>\<lbrace>\<Gamma>\<rbrace>\<rho>) x" by (rule CESem_simps_no_tick)
  also have "\<dots> \<sqsubseteq> (\<N>\<lbrace>(x, z) # \<Delta>\<rbrace>\<rho>) x"
    using fun_belowD[OF le, where x = x] by simp
  also have "\<dots> = \<N>\<lbrakk> z \<rbrakk>\<^bsub>\<N>\<lbrace>(x, z) # \<Delta>\<rbrace>\<rho>\<^esub>"
    by (simp add: lookup_HSem_heap)
  finally
  show "\<N>\<lbrakk> Var x \<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub> \<sqsubseteq> \<N>\<lbrakk> z \<rbrakk>\<^bsub>\<N>\<lbrace>(x, z) # \<Delta>\<rbrace>\<rho>\<^esub>"  by this (intro cont2cont)+
next
case (Bool b)
  case 1
  show ?case by simp
  case 2
  show ?case by simp
next
case (IfThenElse \<Gamma> scrut L \<Delta> b e\<^sub>1 e\<^sub>2 \<Theta> z)
  have Gamma_subset: "domA \<Gamma> \<subseteq> domA \<Delta>"
    by (rule reds_doesnt_forget[OF IfThenElse.hyps(1)])

  let ?e = "if b then e\<^sub>1 else e\<^sub>2"

  case 1

  hence prem1: "fv (\<Gamma>, scrut) \<subseteq> set L \<union> domA \<Gamma>"
    and prem2: "fv (\<Delta>, ?e) \<subseteq> set L \<union> domA \<Delta>"
    and "fv ?e \<subseteq> domA \<Gamma> \<union> set L"
    using new_free_vars_on_heap[OF IfThenElse.hyps(1)] Gamma_subset by auto

  {
  fix r
  have "(\<N>\<lbrakk> (scrut ? e\<^sub>1 : e\<^sub>2) \<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub>)\<cdot>r \<sqsubseteq> CB_project\<cdot>((\<N>\<lbrakk> scrut \<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub>)\<cdot>r)\<cdot>((\<N>\<lbrakk> e\<^sub>1 \<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub>)\<cdot>r)\<cdot>((\<N>\<lbrakk> e\<^sub>2 \<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub>)\<cdot>r)"
    by (rule CESem_simps_no_tick)
  also have "\<dots> \<sqsubseteq> CB_project\<cdot>((\<N>\<lbrakk> Bool b \<rbrakk>\<^bsub>\<N>\<lbrace>\<Delta>\<rbrace>\<rho>\<^esub>)\<cdot>r)\<cdot>((\<N>\<lbrakk> e\<^sub>1 \<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub>)\<cdot>r)\<cdot>((\<N>\<lbrakk> e\<^sub>2 \<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub>)\<cdot>r)"
    by (intro monofun_cfun_fun monofun_cfun_arg  IfThenElse.hyps(2)[OF prem1])
  also have "\<dots> = (\<N>\<lbrakk> ?e \<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub>)\<cdot>r" by (cases r) simp_all
  also have "\<dots> \<sqsubseteq> (\<N>\<lbrakk> ?e \<rbrakk>\<^bsub>\<N>\<lbrace>\<Delta>\<rbrace>\<rho>\<^esub>)\<cdot>r"
    proof(rule monofun_cfun_fun[OF ESem_fresh_cong_below_subset[OF  \<open>fv ?e \<subseteq> domA \<Gamma> \<union> set L\<close> Env.env_restr_belowI]])
      fix x
      assume "x \<in> domA \<Gamma> \<union> set L"
      thus "(\<N>\<lbrace>\<Gamma>\<rbrace>\<rho>) x \<sqsubseteq> (\<N>\<lbrace>\<Delta>\<rbrace>\<rho>) x"
      proof(cases "x \<in> domA \<Gamma>")
        assume "x \<in> domA \<Gamma>"
        from IfThenElse.hyps(3)[OF prem1]
        have "((\<N>\<lbrace>\<Gamma>\<rbrace>\<rho>) f|` domA \<Gamma>) x \<sqsubseteq> ((\<N>\<lbrace>\<Delta>\<rbrace>\<rho>) f|` domA \<Gamma>) x" by (rule fun_belowD)
        with \<open>x \<in> domA \<Gamma>\<close> show ?thesis by simp
      next
        assume "x \<notin> domA \<Gamma>"
        from this \<open>x \<in> domA \<Gamma> \<union> set L\<close> reds_avoids_live[OF IfThenElse.hyps(1)]
        show ?thesis
          by (simp add: lookup_HSem_other)
      qed
    qed
  also have "\<dots> \<sqsubseteq> (\<N>\<lbrakk> z \<rbrakk>\<^bsub>\<N>\<lbrace>\<Theta>\<rbrace>\<rho>\<^esub>)\<cdot>r"
    by (intro monofun_cfun_fun monofun_cfun_arg IfThenElse.hyps(5)[OF prem2])
  finally
  have "(\<N>\<lbrakk> (scrut ? e\<^sub>1 : e\<^sub>2) \<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub>)\<cdot>r \<sqsubseteq> (\<N>\<lbrakk> z \<rbrakk>\<^bsub>\<N>\<lbrace>\<Theta>\<rbrace>\<rho>\<^esub>)\<cdot>r" by this (intro cont2cont)+
  }
  thus ?case  by (rule cfun_belowI)

  show "(\<N>\<lbrace>\<Gamma>\<rbrace>\<rho>) f|` (domA \<Gamma>) \<sqsubseteq> (\<N>\<lbrace>\<Theta>\<rbrace>\<rho>)  f|` (domA \<Gamma>)"
    using IfThenElse.hyps(3)[OF prem1]
          env_restr_below_subset[OF Gamma_subset IfThenElse.hyps(6)[OF prem2]]
    by (rule below_trans)
next
case (Let as \<Gamma> L body \<Delta> z)
  case 1
  have *: "domA as \<inter> domA \<Gamma> = {}" by (metis Let.hyps(1) fresh_distinct)
  
  have "fv (as @ \<Gamma>, body) - domA (as @ \<Gamma>) \<subseteq> fv (\<Gamma>, Let as body) - domA \<Gamma>"
    by auto
  with 1 have prem: "fv (as @ \<Gamma>, body)  \<subseteq> set L \<union>  domA (as @ \<Gamma>)" by auto
  
  have f1: "atom ` domA as \<sharp>* \<Gamma>"
    using Let(1) by (simp add: set_bn_to_atom_domA)

  have "\<N>\<lbrakk> Let as body \<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub> \<sqsubseteq> \<N>\<lbrakk> body \<rbrakk>\<^bsub>\<N>\<lbrace>as\<rbrace>\<N>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub>"
     by (rule CESem_simps_no_tick)
  also have "\<dots> =  \<N>\<lbrakk> body \<rbrakk>\<^bsub>\<N>\<lbrace>as @ \<Gamma>\<rbrace>\<rho>\<^esub>"
    by (rule arg_cong[OF HSem_merge[OF f1]])
  also have "\<dots> \<sqsubseteq>  \<N>\<lbrakk> z \<rbrakk>\<^bsub>\<N>\<lbrace>\<Delta>\<rbrace>\<rho>\<^esub>"
    by (rule Let.hyps(4)[OF prem])
  finally
  show ?case  by this (intro cont2cont)+

  have "(\<N>\<lbrace>\<Gamma>\<rbrace>\<rho>) f|` (domA \<Gamma>) = (\<N>\<lbrace>as\<rbrace>(\<N>\<lbrace>\<Gamma>\<rbrace>\<rho>)) f|` (domA \<Gamma>)"
    unfolding env_restr_HSem[OF *]..
  also have "\<N>\<lbrace>as\<rbrace>(\<N>\<lbrace>\<Gamma>\<rbrace>\<rho>) = (\<N>\<lbrace>as @ \<Gamma>\<rbrace>\<rho>)"
    by (rule HSem_merge[OF f1])
  also have "\<dots> f|` domA \<Gamma> \<sqsubseteq> (\<N>\<lbrace>\<Delta>\<rbrace>\<rho>) f|` domA \<Gamma>"
    by (rule env_restr_below_subset[OF _ Let.hyps(5)[OF prem]]) simp
  finally
  show "(\<N>\<lbrace>\<Gamma>\<rbrace>\<rho>) f|` domA \<Gamma> \<sqsubseteq> (\<N>\<lbrace>\<Delta>\<rbrace>\<rho>) f|` domA \<Gamma>".
qed


corollary correctness_empty_env:
  assumes "\<Gamma> : e \<Down>\<^bsub>L\<^esub> \<Delta> : z"
  and     "fv (\<Gamma>, e) \<subseteq> set L"
  shows   "\<N>\<lbrakk>e\<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<^esub> \<sqsubseteq> \<N>\<lbrakk>z\<rbrakk>\<^bsub>\<N>\<lbrace>\<Delta>\<rbrace>\<^esub>" and "\<N>\<lbrace>\<Gamma>\<rbrace> \<sqsubseteq> \<N>\<lbrace>\<Delta>\<rbrace>"
proof-
  from assms(2) have "fv (\<Gamma>, e) \<subseteq> set L \<union>  domA \<Gamma>" by auto
  note corr = correctness[OF assms(1) this, where \<rho> = "\<bottom>"]

  show "\<N>\<lbrakk> e \<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<^esub> \<sqsubseteq> \<N>\<lbrakk> z \<rbrakk>\<^bsub>\<N>\<lbrace>\<Delta>\<rbrace>\<^esub>" using corr(1).

  have "\<N>\<lbrace>\<Gamma>\<rbrace> = (\<N>\<lbrace>\<Gamma>\<rbrace>) f|` domA \<Gamma> "
    using env_restr_useless[OF HSem_edom_subset, where \<rho>1 = "\<bottom>"] by simp
  also have "\<dots> \<sqsubseteq> (\<N>\<lbrace>\<Delta>\<rbrace>) f|` domA \<Gamma>" using corr(2).
  also have "\<dots> \<sqsubseteq> \<N>\<lbrace>\<Delta>\<rbrace>" by (rule env_restr_below_itself)
  finally show "\<N>\<lbrace>\<Gamma>\<rbrace> \<sqsubseteq> \<N>\<lbrace>\<Delta>\<rbrace>" by this (intro cont2cont)+
qed

end
