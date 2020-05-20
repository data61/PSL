theory ResourcedAdequacy
imports ResourcedDenotational Launchbury "AList-Utils" CorrectnessResourced
begin

lemma demand_not_0: "demand (\<N>\<lbrakk>e\<rbrakk>\<^bsub>\<rho>\<^esub>) \<noteq> \<bottom>"
proof
  assume "demand (\<N>\<lbrakk>e\<rbrakk>\<^bsub>\<rho>\<^esub>) = \<bottom>"
  with demand_suffices'[where n = 0, simplified, OF this]
  have "(\<N>\<lbrakk>e\<rbrakk>\<^bsub>\<rho>\<^esub>)\<cdot>\<bottom> \<noteq> \<bottom>" by simp
  thus False by simp
qed

text \<open>
The semantics of an expression, given only @{term r} resources, will only use values from the
environment with less resources.
\<close>

lemma restr_can_restrict_env: "(\<N>\<lbrakk> e \<rbrakk>\<^bsub>\<rho>\<^esub>)|\<^bsub>C\<cdot>r\<^esub> = (\<N>\<lbrakk> e \<rbrakk>\<^bsub>\<rho>|\<^sup>\<circ>\<^bsub>r\<^esub>\<^esub>)|\<^bsub>C\<cdot>r\<^esub>"
proof(induction e arbitrary: \<rho> r rule: exp_induct)
  case (Var x)
  show ?case
  proof (rule C_restr_C_cong)
    fix r'
    assume "r' \<sqsubseteq> r"
    have "(\<N>\<lbrakk> Var x \<rbrakk>\<^bsub>\<rho>\<^esub>)\<cdot>(C\<cdot>r') = \<rho> x\<cdot>r'" by simp
    also have "\<dots> = ((\<rho> x)|\<^bsub>r\<^esub>)\<cdot>r'" using \<open>r' \<sqsubseteq> r\<close> by simp
    also have "\<dots> =  (\<N>\<lbrakk> Var x \<rbrakk>\<^bsub>\<rho>|\<^sup>\<circ>\<^bsub>r\<^esub>\<^esub>)\<cdot>(C\<cdot>r')" by simp
    finally show "(\<N>\<lbrakk> Var x \<rbrakk>\<^bsub>\<rho>\<^esub>)\<cdot>(C\<cdot>r') = (\<N>\<lbrakk> Var x \<rbrakk>\<^bsub>\<rho>|\<^sup>\<circ>\<^bsub>r\<^esub>\<^esub>)\<cdot>(C\<cdot>r')".
  qed simp
next
  case (Lam x e)
  show ?case
  proof(rule C_restr_C_cong)
    fix r'
    assume "r' \<sqsubseteq> r"
    hence "r' \<sqsubseteq> C\<cdot>r" by (metis below_C below_trans)
    {
      fix v
      have "\<rho>(x := v)|\<^sup>\<circ>\<^bsub>r\<^esub> = (\<rho>|\<^sup>\<circ>\<^bsub>r\<^esub>)(x := v)|\<^sup>\<circ>\<^bsub>r\<^esub>"
        by simp
      hence "(\<N>\<lbrakk> e \<rbrakk>\<^bsub>\<rho>(x := v)\<^esub>)|\<^bsub>r'\<^esub> = (\<N>\<lbrakk> e \<rbrakk>\<^bsub>(\<rho>|\<^sup>\<circ>\<^bsub>r\<^esub>)(x := v)\<^esub>)|\<^bsub>r'\<^esub>"
        by  (subst (1 2) C_restr_eq_lower[OF Lam \<open>r' \<sqsubseteq> C\<cdot>r\<close> ]) simp
    }
    thus "(\<N>\<lbrakk> Lam [x]. e \<rbrakk>\<^bsub>\<rho>\<^esub>)\<cdot>(C\<cdot>r') = (\<N>\<lbrakk> Lam [x]. e \<rbrakk>\<^bsub>\<rho>|\<^sup>\<circ>\<^bsub>r\<^esub>\<^esub>)\<cdot>(C\<cdot>r')"
      by simp
  qed simp
next
  case (App e x)
  show ?case
  proof (rule C_restr_C_cong)
    fix r'
    assume "r' \<sqsubseteq> r"
    hence "r' \<sqsubseteq> C\<cdot>r" by (metis below_C below_trans)
    hence "(\<N>\<lbrakk> e \<rbrakk>\<^bsub>\<rho>\<^esub>)\<cdot>r' = (\<N>\<lbrakk> e \<rbrakk>\<^bsub>\<rho>|\<^sup>\<circ>\<^bsub>r\<^esub>\<^esub>)\<cdot>r'"
        by (rule C_restr_eqD[OF App])
    thus "(\<N>\<lbrakk> App e x \<rbrakk>\<^bsub>\<rho>\<^esub>)\<cdot>(C\<cdot>r') = (\<N>\<lbrakk> App e x \<rbrakk>\<^bsub>\<rho>|\<^sup>\<circ>\<^bsub>r\<^esub>\<^esub>)\<cdot>(C\<cdot>r')"
      using \<open>r' \<sqsubseteq> r\<close> by simp
  qed simp
next
  case (Bool b)
  show ?case by simp
next
  case (IfThenElse scrut e\<^sub>1 e\<^sub>2)
  show ?case
  proof (rule C_restr_C_cong)
    fix r'
    assume "r' \<sqsubseteq> r"
    hence "r' \<sqsubseteq> C\<cdot>r" by (metis below_C below_trans)

    have "(\<N>\<lbrakk> scrut \<rbrakk>\<^bsub>\<rho>\<^esub>)\<cdot>r' = (\<N>\<lbrakk> scrut \<rbrakk>\<^bsub>\<rho>|\<^sup>\<circ>\<^bsub>r\<^esub>\<^esub>)\<cdot>r'"
      using \<open>r' \<sqsubseteq> C\<cdot>r\<close> by (rule C_restr_eqD[OF IfThenElse(1)])
    moreover
    have "(\<N>\<lbrakk> e\<^sub>1 \<rbrakk>\<^bsub>\<rho>\<^esub>)\<cdot>r' = (\<N>\<lbrakk> e\<^sub>1 \<rbrakk>\<^bsub>\<rho>|\<^sup>\<circ>\<^bsub>r\<^esub>\<^esub>)\<cdot>r'"
      using \<open>r' \<sqsubseteq> C\<cdot>r\<close> by (rule C_restr_eqD[OF IfThenElse(2)])
    moreover
    have "(\<N>\<lbrakk> e\<^sub>2 \<rbrakk>\<^bsub>\<rho>\<^esub>)\<cdot>r' = (\<N>\<lbrakk> e\<^sub>2 \<rbrakk>\<^bsub>\<rho>|\<^sup>\<circ>\<^bsub>r\<^esub>\<^esub>)\<cdot>r'"
      using \<open>r' \<sqsubseteq> C\<cdot>r\<close> by (rule C_restr_eqD[OF IfThenElse(3)])
    ultimately
    show "(\<N>\<lbrakk> (scrut ? e\<^sub>1 : e\<^sub>2) \<rbrakk>\<^bsub>\<rho>\<^esub>)\<cdot>(C\<cdot>r') = (\<N>\<lbrakk> (scrut ? e\<^sub>1 : e\<^sub>2) \<rbrakk>\<^bsub>\<rho>|\<^sup>\<circ>\<^bsub>r\<^esub>\<^esub>)\<cdot>(C\<cdot>r')"
      using \<open>r' \<sqsubseteq> r\<close> by simp
  qed simp
next
  case (Let \<Gamma> e)

  txt \<open>The lemma, lifted to heaps\<close>
  have restr_can_restrict_env_heap : "\<And> r. (\<N>\<lbrace>\<Gamma>\<rbrace>\<rho>)|\<^sup>\<circ>\<^bsub>r\<^esub> = (\<N>\<lbrace>\<Gamma>\<rbrace>\<rho>|\<^sup>\<circ>\<^bsub>r\<^esub>)|\<^sup>\<circ>\<^bsub>r\<^esub>"
  proof(rule has_ESem.parallel_HSem_ind)
    fix \<rho>\<^sub>1 \<rho>\<^sub>2 :: CEnv and r :: C
    assume "\<rho>\<^sub>1|\<^sup>\<circ>\<^bsub>r\<^esub> = \<rho>\<^sub>2|\<^sup>\<circ>\<^bsub>r\<^esub>"

    show " (\<rho> ++\<^bsub>domA \<Gamma>\<^esub> \<^bold>\<N>\<lbrakk> \<Gamma> \<^bold>\<rbrakk>\<^bsub>\<rho>\<^sub>1\<^esub>)|\<^sup>\<circ>\<^bsub>r\<^esub> = (\<rho>|\<^sup>\<circ>\<^bsub>r\<^esub> ++\<^bsub>domA \<Gamma>\<^esub> \<^bold>\<N>\<lbrakk> \<Gamma> \<^bold>\<rbrakk>\<^bsub>\<rho>\<^sub>2\<^esub>)|\<^sup>\<circ>\<^bsub>r\<^esub>"
    proof(rule env_C_restr_cong)
      fix x and r'
      assume "r' \<sqsubseteq> r"
      hence "r' \<sqsubseteq> C\<cdot>r" by (metis below_C below_trans)

      show "(\<rho> ++\<^bsub>domA \<Gamma>\<^esub> \<^bold>\<N>\<lbrakk> \<Gamma> \<^bold>\<rbrakk>\<^bsub>\<rho>\<^sub>1\<^esub>) x\<cdot>r' = (\<rho>|\<^sup>\<circ>\<^bsub>r\<^esub> ++\<^bsub>domA \<Gamma>\<^esub> \<^bold>\<N>\<lbrakk> \<Gamma> \<^bold>\<rbrakk>\<^bsub>\<rho>\<^sub>2\<^esub>) x\<cdot>r'"
      proof(cases "x \<in> domA \<Gamma>")
        case True
        have "(\<N>\<lbrakk> the (map_of \<Gamma> x) \<rbrakk>\<^bsub>\<rho>\<^sub>1\<^esub>)\<cdot>r' = (\<N>\<lbrakk> the (map_of \<Gamma> x) \<rbrakk>\<^bsub>\<rho>\<^sub>1|\<^sup>\<circ>\<^bsub>r\<^esub>\<^esub>)\<cdot>r'"
         by (rule C_restr_eqD[OF Let(1)[OF True] \<open>r' \<sqsubseteq> C\<cdot>r\<close>])
        also have "\<dots> = (\<N>\<lbrakk> the (map_of \<Gamma> x) \<rbrakk>\<^bsub>\<rho>\<^sub>2|\<^sup>\<circ>\<^bsub>r\<^esub>\<^esub>)\<cdot>r'"
          unfolding \<open>\<rho>\<^sub>1|\<^sup>\<circ>\<^bsub>r\<^esub> = \<rho>\<^sub>2|\<^sup>\<circ>\<^bsub>r\<^esub>\<close>..
        also have "\<dots>   = (\<N>\<lbrakk> the (map_of \<Gamma> x) \<rbrakk>\<^bsub>\<rho>\<^sub>2\<^esub>)\<cdot>r'"
          by (rule C_restr_eqD[OF Let(1)[OF True] \<open>r' \<sqsubseteq> C\<cdot>r\<close>, symmetric])
        finally
        show ?thesis using True by (simp add: lookupEvalHeap)
      next
        case False
        with \<open>r' \<sqsubseteq> r\<close>
        show ?thesis by simp
      qed
    qed
  qed simp_all

  show ?case
  proof (rule C_restr_C_cong)
    fix r'
    assume "r' \<sqsubseteq> r"
    hence "r' \<sqsubseteq> C\<cdot>r" by (metis below_C below_trans)

    have "(\<N>\<lbrace>\<Gamma>\<rbrace>\<rho>)|\<^sup>\<circ>\<^bsub>r\<^esub> = (\<N>\<lbrace>\<Gamma>\<rbrace>(\<rho>|\<^sup>\<circ>\<^bsub>r\<^esub>))|\<^sup>\<circ>\<^bsub>r\<^esub>"
      by (rule restr_can_restrict_env_heap)
    hence "(\<N>\<lbrakk> e \<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub>)\<cdot>r' = (\<N>\<lbrakk> e \<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<rho>|\<^sup>\<circ>\<^bsub>r\<^esub>\<^esub>)\<cdot>r'"
      by (subst (1 2) C_restr_eqD[OF Let(2) \<open>r' \<sqsubseteq> C\<cdot>r\<close>]) simp

    thus "(\<N>\<lbrakk> Let \<Gamma> e \<rbrakk>\<^bsub>\<rho>\<^esub>)\<cdot>(C\<cdot>r') = (\<N>\<lbrakk> Let \<Gamma> e \<rbrakk>\<^bsub>\<rho>|\<^sup>\<circ>\<^bsub>r\<^esub>\<^esub>)\<cdot>(C\<cdot>r')"
      using \<open>r' \<sqsubseteq> r\<close> by simp
  qed simp
qed

lemma can_restrict_env:
  "(\<N>\<lbrakk>e\<rbrakk>\<^bsub>\<rho>\<^esub>)\<cdot>(C\<cdot>r) = (\<N>\<lbrakk> e \<rbrakk>\<^bsub>\<rho>|\<^sup>\<circ>\<^bsub>r\<^esub>\<^esub>)\<cdot>(C\<cdot>r)"
  by (rule C_restr_eqD[OF restr_can_restrict_env below_refl])

text \<open>
When an expression @{term e} terminates, then we can remove such an expression from the heap and it
still terminates. This is the crucial trick to handle black-holing in the resourced semantics.
\<close>

lemma add_BH:
  assumes "map_of \<Gamma> x = Some e"
  assumes  "(\<N>\<lbrakk>e\<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<^esub>)\<cdot>r' \<noteq> \<bottom>"
  shows "(\<N>\<lbrakk>e\<rbrakk>\<^bsub>\<N>\<lbrace>delete x \<Gamma>\<rbrace>\<^esub>)\<cdot>r' \<noteq> \<bottom>"
proof-
  obtain r where r: "C\<cdot>r = demand (\<N>\<lbrakk>e\<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<^esub>)"
    using demand_not_0 by (cases "demand (\<N>\<lbrakk> e \<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<^esub>)") auto

  from  assms(2)
  have "C\<cdot>r \<sqsubseteq> r'" unfolding r not_bot_demand by simp

  from assms(1)
  have [simp]: "the (map_of \<Gamma> x) = e" by (metis option.sel)

  from assms(1)
  have [simp]: "x \<in> domA \<Gamma>" by (metis domIff dom_map_of_conv_domA not_Some_eq)

  define ub where "ub = \<N>\<lbrace>\<Gamma>\<rbrace>" \<comment> \<open>An upper bound for the induction\<close>

  have heaps: "(\<N>\<lbrace>\<Gamma>\<rbrace>)|\<^sup>\<circ>\<^bsub>r\<^esub> \<sqsubseteq> \<N>\<lbrace>delete x \<Gamma>\<rbrace>" and "\<N>\<lbrace>\<Gamma>\<rbrace> \<sqsubseteq> ub"
  proof (induction rule: HSem_bot_ind) 
    fix \<rho>
    assume "\<rho>|\<^sup>\<circ>\<^bsub>r\<^esub> \<sqsubseteq> \<N>\<lbrace>delete x \<Gamma>\<rbrace>"
    assume "\<rho> \<sqsubseteq> ub"

    show "(\<^bold>\<N>\<lbrakk> \<Gamma> \<^bold>\<rbrakk>\<^bsub>\<rho>\<^esub>)|\<^sup>\<circ>\<^bsub>r\<^esub> \<sqsubseteq> \<N>\<lbrace>delete x \<Gamma>\<rbrace>"
    proof (rule fun_belowI)
      fix y
      show "((\<^bold>\<N>\<lbrakk> \<Gamma> \<^bold>\<rbrakk>\<^bsub>\<rho>\<^esub>)|\<^sup>\<circ>\<^bsub>r\<^esub>) y \<sqsubseteq> (\<N>\<lbrace>delete x \<Gamma>\<rbrace>) y"
      proof (cases "y = x")
        case True
        have "((\<^bold>\<N>\<lbrakk> \<Gamma> \<^bold>\<rbrakk>\<^bsub>\<rho>\<^esub>)|\<^sup>\<circ>\<^bsub>r\<^esub>) x = (\<N>\<lbrakk> e \<rbrakk>\<^bsub>\<rho>\<^esub>)|\<^bsub>r\<^esub>"
          by (simp add: lookupEvalHeap)
        also have "\<dots> \<sqsubseteq> (\<N>\<lbrakk> e \<rbrakk>\<^bsub>ub\<^esub>)|\<^bsub>r\<^esub>"
          using \<open>\<rho> \<sqsubseteq> ub\<close> by (intro monofun_cfun_arg)
        also have "\<dots> = (\<N>\<lbrakk> e \<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<^esub>)|\<^bsub>r\<^esub>"
          unfolding ub_def..
        also have "\<dots> = \<bottom>"
          using r by (rule  C_restr_bot_demand[OF eq_imp_below])
        also have "\<dots> = (\<N>\<lbrace>delete x \<Gamma>\<rbrace>) x"
          by (simp add: lookup_HSem_other)
        finally
        show ?thesis unfolding True.
      next
        case False
        show ?thesis
        proof (cases "y \<in> domA \<Gamma>")
          case True
          have "(\<N>\<lbrakk> the (map_of \<Gamma> y) \<rbrakk>\<^bsub>\<rho>\<^esub>)|\<^bsub>r\<^esub> = (\<N>\<lbrakk> the (map_of \<Gamma> y) \<rbrakk>\<^bsub>\<rho>|\<^sup>\<circ>\<^bsub>r\<^esub>\<^esub>)|\<^bsub>r\<^esub>"
            by (rule C_restr_eq_lower[OF restr_can_restrict_env below_C])
          also have "\<dots> \<sqsubseteq> \<N>\<lbrakk> the (map_of \<Gamma> y) \<rbrakk>\<^bsub>\<rho>|\<^sup>\<circ>\<^bsub>r\<^esub>\<^esub>"
            by (rule C_restr_below)
          also note \<open>\<rho>|\<^sup>\<circ>\<^bsub>r\<^esub> \<sqsubseteq> \<N>\<lbrace>delete x \<Gamma>\<rbrace>\<close>
          finally
          show ?thesis
            using \<open>y \<in> domA \<Gamma>\<close> \<open>y \<noteq> x\<close>
            by (simp add: lookupEvalHeap lookup_HSem_heap)
        next
          case False
          thus ?thesis by simp
        qed
      qed
    qed

    from \<open>\<rho> \<sqsubseteq> ub\<close>
    have "(\<^bold>\<N>\<lbrakk> \<Gamma> \<^bold>\<rbrakk>\<^bsub>\<rho>\<^esub>) \<sqsubseteq> (\<^bold>\<N>\<lbrakk> \<Gamma> \<^bold>\<rbrakk>\<^bsub>ub\<^esub>)" 
      by (rule cont2monofunE[rotated]) simp
    also have "\<dots> = ub"
      unfolding ub_def HSem_bot_eq[symmetric]..
    finally     
    show "(\<^bold>\<N>\<lbrakk> \<Gamma> \<^bold>\<rbrakk>\<^bsub>\<rho>\<^esub>) \<sqsubseteq> ub".
  qed simp_all

  from assms(2)
  have "(\<N>\<lbrakk>e\<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<^esub>)\<cdot>(C\<cdot>r) \<noteq> \<bottom>"
    unfolding r
    by (rule demand_suffices[OF infinite_resources_suffice])
  also
  have "(\<N>\<lbrakk>e\<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<^esub>)\<cdot>(C\<cdot>r) = (\<N>\<lbrakk>e\<rbrakk>\<^bsub>(\<N>\<lbrace>\<Gamma>\<rbrace>)|\<^sup>\<circ>\<^bsub>r\<^esub>\<^esub>)\<cdot>(C\<cdot>r)"
    by (rule can_restrict_env)
  also
  have "\<dots> \<sqsubseteq> (\<N>\<lbrakk>e\<rbrakk>\<^bsub>\<N>\<lbrace>delete x \<Gamma>\<rbrace>\<^esub>)\<cdot>(C\<cdot>r)"
    by (intro monofun_cfun_arg monofun_cfun_fun heaps )
  also
  have "\<dots> \<sqsubseteq> (\<N>\<lbrakk>e\<rbrakk>\<^bsub>\<N>\<lbrace>delete x \<Gamma>\<rbrace>\<^esub>)\<cdot>r'"
    using \<open>C\<cdot>r \<sqsubseteq> r'\<close> by (rule monofun_cfun_arg)
  finally
  show ?thesis by this (intro cont2cont)+
qed

text \<open>
The semantics is continuous, so we can apply induction here:
\<close>

lemma resourced_adequacy:
  assumes "(\<N>\<lbrakk>e\<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<^esub>)\<cdot>r \<noteq> \<bottom>"
  shows "\<exists> \<Delta> v. \<Gamma> : e \<Down>\<^bsub>S\<^esub> \<Delta> : v"
using assms
proof(induction r arbitrary: \<Gamma> e S rule: C.induct[case_names adm bot step])
  case adm show ?case by simp
next
  case bot
  hence False by auto
  thus ?case..
next
  case (step r)
  show ?case
  proof(cases e rule:exp_strong_exhaust(1)[where c = "(\<Gamma>,S)", case_names Var App Let Lam Bool IfThenElse])
  case (Var x)
    let ?e = "the (map_of \<Gamma> x)"
    from step.prems[unfolded Var]
    have "x \<in> domA \<Gamma>" 
      by (auto intro: ccontr simp add: lookup_HSem_other)
    hence "map_of \<Gamma> x = Some ?e" by (rule domA_map_of_Some_the)
    moreover
    from step.prems[unfolded Var] \<open>map_of \<Gamma> x = Some ?e\<close> \<open>x \<in> domA \<Gamma>\<close>
    have "(\<N>\<lbrakk>?e\<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<^esub>)\<cdot>r \<noteq> \<bottom>" by (auto simp add: lookup_HSem_heap  simp del: app_strict)
    hence "(\<N>\<lbrakk>?e\<rbrakk>\<^bsub>\<N>\<lbrace>delete x \<Gamma>\<rbrace>\<^esub>)\<cdot>r \<noteq> \<bottom>" by (rule add_BH[OF \<open>map_of \<Gamma> x = Some ?e\<close>])
    from step.IH[OF this]
    obtain \<Delta> v where "delete x \<Gamma> : ?e \<Down>\<^bsub>x # S\<^esub> \<Delta> : v" by blast
    ultimately
    have "\<Gamma> : (Var x) \<Down>\<^bsub>S\<^esub> (x,v) #  \<Delta> : v" by (rule Variable)
    thus ?thesis using Var by auto
  next
  case (App e' x)
    have "finite (set S \<union> fv (\<Gamma>, e'))" by simp
    from finite_list[OF this]
    obtain S' where S': "set S' = set S \<union> fv (\<Gamma>, e')"..

    from step.prems[unfolded App]
    have prem: "((\<N>\<lbrakk> e' \<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<^esub>)\<cdot>r \<down>CFn (\<N>\<lbrace>\<Gamma>\<rbrace>) x|\<^bsub>r\<^esub>)\<cdot>r \<noteq> \<bottom>" by (auto simp del: app_strict)
    hence "(\<N>\<lbrakk>e'\<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<^esub>)\<cdot>r \<noteq> \<bottom>" by auto
    from step.IH[OF this]
    obtain \<Delta> v where lhs': "\<Gamma> : e' \<Down>\<^bsub>S'\<^esub> \<Delta> : v" by blast 

    have "fv (\<Gamma>, e') \<subseteq> set S'" using S' by auto
    from correctness_empty_env[OF lhs' this]
    have correct1: "\<N>\<lbrakk>e'\<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<^esub> \<sqsubseteq> \<N>\<lbrakk>v\<rbrakk>\<^bsub>\<N>\<lbrace>\<Delta>\<rbrace>\<^esub>" and "\<N>\<lbrace>\<Gamma>\<rbrace> \<sqsubseteq> \<N>\<lbrace>\<Delta>\<rbrace>" by auto

    from prem
    have "((\<N>\<lbrakk> v \<rbrakk>\<^bsub>\<N>\<lbrace>\<Delta>\<rbrace>\<^esub>)\<cdot>r \<down>CFn (\<N>\<lbrace>\<Gamma>\<rbrace>) x|\<^bsub>r\<^esub>)\<cdot>r \<noteq> \<bottom>"
      by (rule not_bot_below_trans)(intro correct1 monofun_cfun_fun  monofun_cfun_arg)
    with result_evaluated[OF lhs']
    have "isLam v" by (cases r, auto, cases v rule: isVal.cases, auto)
    then obtain y e'' where n': "v = (Lam [y]. e'')" by (rule isLam_obtain_fresh)
    with lhs'
    have lhs: "\<Gamma> : e' \<Down>\<^bsub>S'\<^esub> \<Delta> : Lam [y]. e''" by simp

    have "((\<N>\<lbrakk> v \<rbrakk>\<^bsub>\<N>\<lbrace>\<Delta>\<rbrace>\<^esub>)\<cdot>r \<down>CFn (\<N>\<lbrace>\<Gamma>\<rbrace>) x|\<^bsub>r\<^esub>)\<cdot>r \<noteq> \<bottom>" by fact
    also have "(\<N>\<lbrace>\<Gamma>\<rbrace>) x|\<^bsub>r\<^esub> \<sqsubseteq> (\<N>\<lbrace>\<Gamma>\<rbrace>) x" by (rule C_restr_below)
    also note \<open>v = _\<close>
    also note \<open>(\<N>\<lbrace>\<Gamma>\<rbrace>) \<sqsubseteq> (\<N>\<lbrace>\<Delta>\<rbrace>)\<close>
    also have "(\<N>\<lbrakk> Lam [y]. e'' \<rbrakk>\<^bsub>\<N>\<lbrace>\<Delta>\<rbrace>\<^esub>)\<cdot>r \<sqsubseteq> CFn\<cdot>(\<Lambda> v. \<N>\<lbrakk>e''\<rbrakk>\<^bsub>(\<N>\<lbrace>\<Delta>\<rbrace>)(y := v)\<^esub>)"
      by (rule CELam_no_restr)
    also have "(\<dots> \<down>CFn (\<N>\<lbrace>\<Delta>\<rbrace>) x)\<cdot>r = (\<N>\<lbrakk>e''\<rbrakk>\<^bsub>(\<N>\<lbrace>\<Delta>\<rbrace>)(y := ((\<N>\<lbrace>\<Delta>\<rbrace>) x))\<^esub>)\<cdot>r" by simp
    also have "\<dots> = (\<N>\<lbrakk>e''[y::=x]\<rbrakk>\<^bsub>\<N>\<lbrace>\<Delta>\<rbrace>\<^esub>)\<cdot>r"
      unfolding ESem_subst..
    finally
    have "\<dots> \<noteq> \<bottom>" by this (intro cont2cont cont_fun)+
    then
    obtain \<Theta> v' where rhs: "\<Delta> : e''[y::=x] \<Down>\<^bsub>S'\<^esub> \<Theta> : v'" using step.IH by blast

    have "\<Gamma> : App e' x \<Down>\<^bsub>S'\<^esub> \<Theta> : v'"
      by (rule reds_ApplicationI[OF lhs rhs])
    hence "\<Gamma> : App e' x \<Down>\<^bsub>S\<^esub> \<Theta> : v'"
      apply (rule reds_smaller_L) using S' by auto
    thus ?thesis using App by auto
  next
  case (Lam v e')
    have "\<Gamma> : Lam [v]. e' \<Down>\<^bsub>S\<^esub> \<Gamma> : Lam [v]. e'" ..
    thus ?thesis using Lam by blast
  next
  case (Bool b)
    have "\<Gamma> : Bool b \<Down>\<^bsub>S\<^esub> \<Gamma> : Bool b" by rule
    thus ?thesis using Bool by blast
  next
  case (IfThenElse scrut e\<^sub>1 e\<^sub>2)

    from step.prems[unfolded IfThenElse]
    have prem: "CB_project\<cdot>((\<N>\<lbrakk> scrut \<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<^esub>)\<cdot>r)\<cdot>((\<N>\<lbrakk> e\<^sub>1 \<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<^esub>)\<cdot>r)\<cdot>((\<N>\<lbrakk> e\<^sub>2 \<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<^esub>)\<cdot>r) \<noteq> \<bottom>" by (auto simp del: app_strict)
    then obtain b where
      is_CB: "(\<N>\<lbrakk> scrut \<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<^esub>)\<cdot>r = CB\<cdot>(Discr b)"
      and not_bot2: "((\<N>\<lbrakk> (if b then e\<^sub>1 else e\<^sub>2) \<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<^esub>)\<cdot>r) \<noteq> \<bottom>"
    unfolding CB_project_not_bot by (auto split: if_splits)

    have "finite (set S \<union> fv (\<Gamma>, scrut))" by simp
    from finite_list[OF this]
    obtain S' where S': "set S' = set S \<union> fv (\<Gamma>, scrut)"..


    from is_CB have "(\<N>\<lbrakk> scrut \<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<^esub>)\<cdot>r \<noteq> \<bottom>" by simp
    from step.IH[OF this]
    obtain \<Delta> v where lhs': "\<Gamma> : scrut \<Down>\<^bsub>S'\<^esub> \<Delta> : v" by blast
    then have "isVal v" by (rule result_evaluated)

    have "fv (\<Gamma>, scrut) \<subseteq> set S'" using S' by simp
    from correctness_empty_env[OF lhs' this]
    have correct1: "\<N>\<lbrakk>scrut\<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<^esub> \<sqsubseteq> \<N>\<lbrakk>v\<rbrakk>\<^bsub>\<N>\<lbrace>\<Delta>\<rbrace>\<^esub>" and correct2: "\<N>\<lbrace>\<Gamma>\<rbrace> \<sqsubseteq> \<N>\<lbrace>\<Delta>\<rbrace>" by auto

    from correct1
    have "(\<N>\<lbrakk> scrut \<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<^esub>)\<cdot>r \<sqsubseteq> (\<N>\<lbrakk> v \<rbrakk>\<^bsub>\<N>\<lbrace>\<Delta>\<rbrace>\<^esub>)\<cdot>r" by (rule monofun_cfun_fun)
    with is_CB
    have "(\<N>\<lbrakk> v \<rbrakk>\<^bsub>\<N>\<lbrace>\<Delta>\<rbrace>\<^esub>)\<cdot>r = CB\<cdot>(Discr b)" by simp
    with \<open>isVal v\<close>
    have "v = Bool b" by (cases v rule: isVal.cases) (case_tac r, auto)+

    from not_bot2 \<open>\<N>\<lbrace>\<Gamma>\<rbrace> \<sqsubseteq> \<N>\<lbrace>\<Delta>\<rbrace>\<close>
    have "(\<N>\<lbrakk> (if b then e\<^sub>1 else e\<^sub>2) \<rbrakk>\<^bsub>\<N>\<lbrace>\<Delta>\<rbrace>\<^esub>)\<cdot>r \<noteq> \<bottom>"
      by (rule not_bot_below_trans[OF _ monofun_cfun_fun[OF monofun_cfun_arg]])
    from step.IH[OF this]
    obtain \<Theta> v' where rhs: "\<Delta> : (if b then e\<^sub>1 else e\<^sub>2) \<Down>\<^bsub>S'\<^esub> \<Theta> : v'" by blast

    from lhs'[unfolded \<open>v = _\<close>] rhs
    have "\<Gamma> : (scrut ? e\<^sub>1 : e\<^sub>2) \<Down>\<^bsub>S'\<^esub> \<Theta> : v'" by rule
    hence "\<Gamma> : (scrut ? e\<^sub>1 : e\<^sub>2) \<Down>\<^bsub>S\<^esub> \<Theta> : v'"
      apply (rule reds_smaller_L) using S' by auto
    thus ?thesis unfolding IfThenElse by blast
  next
  case (Let \<Delta> e')
    from step.prems[unfolded Let(2)]
    have prem: "(\<N>\<lbrakk>e'\<rbrakk>\<^bsub>\<N>\<lbrace>\<Delta>\<rbrace>\<N>\<lbrace>\<Gamma>\<rbrace>\<^esub>)\<cdot>r \<noteq> \<bottom>" 
      by (simp  del: app_strict)
    also
      have "atom ` domA \<Delta> \<sharp>* \<Gamma>" using Let(1) by (simp add: fresh_star_Pair)
      hence "\<N>\<lbrace>\<Delta>\<rbrace>\<N>\<lbrace>\<Gamma>\<rbrace> = \<N>\<lbrace>\<Delta> @ \<Gamma>\<rbrace>" by (rule HSem_merge)
    finally 
    have "(\<N>\<lbrakk>e'\<rbrakk>\<^bsub>\<N>\<lbrace>\<Delta> @ \<Gamma>\<rbrace>\<^esub>)\<cdot>r \<noteq> \<bottom>".
    then
    obtain \<Theta> v where "\<Delta> @ \<Gamma> : e' \<Down>\<^bsub>S\<^esub> \<Theta> : v" using step.IH by blast
    hence "\<Gamma> : Let \<Delta> e' \<Down>\<^bsub>S\<^esub> \<Theta> : v"
      by (rule reds.Let[OF Let(1)])
    thus ?thesis using Let by auto
  qed
qed

end
