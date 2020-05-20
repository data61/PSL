theory ArityAnalysisCorrDenotational
imports ArityAnalysisSpec Launchbury.Denotational ArityTransform
begin

context ArityAnalysisLetSafe
begin

inductive eq :: "Arity \<Rightarrow> Value \<Rightarrow> Value \<Rightarrow> bool" where
   "eq 0 v v"
 |  "(\<And> v. eq n (v1 \<down>Fn v) (v2 \<down>Fn v)) \<Longrightarrow> eq (inc\<cdot>n) v1 v2"

lemma [simp]: "eq 0 v v' \<longleftrightarrow> v = v'"
  by (auto elim: eq.cases intro: eq.intros)

lemma eq_inc_simp:
  "eq (inc\<cdot>n) v1 v2 \<longleftrightarrow> (\<forall> v . eq n (v1 \<down>Fn v) (v2 \<down>Fn v))"
  by (auto elim: eq.cases intro: eq.intros)

lemma eq_FnI:
  "(\<And> v. eq (pred\<cdot>n) (f1\<cdot>v) (f2\<cdot>v)) \<Longrightarrow> eq n (Fn\<cdot>f1) (Fn\<cdot>f2)"
  by (induction n rule: Arity_ind) (auto intro: eq.intros cfun_eqI)

lemma eq_refl[simp]: "eq a v v"
  by (induction a arbitrary: v rule: Arity_ind) (auto intro!: eq.intros)

lemma eq_trans[trans]: "eq a v1 v2 \<Longrightarrow> eq a v2 v3 \<Longrightarrow> eq a v1 v3"
  apply (induction a arbitrary: v1 v2 v3 rule: Arity_ind)
  apply (auto elim!: eq.cases intro!: eq.intros)
  apply blast
  done

lemma eq_Fn: "eq a v1 v2 \<Longrightarrow> eq (pred\<cdot>a) (v1 \<down>Fn v) (v2 \<down>Fn v)"
apply (induction a  rule: Arity_ind[case_names 0 inc])
apply (auto simp add: eq_inc_simp)
done

lemma eq_inc_same: "eq a v1 v2 \<Longrightarrow> eq (inc\<cdot>a) v1 v2"
by (induction a  arbitrary: v1 v2 rule: Arity_ind[case_names 0 inc])  (auto simp add: eq_inc_simp)

lemma eq_mono: "a \<sqsubseteq> a' \<Longrightarrow> eq a' v1 v2 \<Longrightarrow> eq a v1 v2"
proof (induction a  rule: Arity_ind[case_names 0 inc])
  case 0 thus ?case by auto
next
  case (inc a)
  show "eq (inc\<cdot>a) v1 v2"
  proof (cases "inc\<cdot>a = a'")
    case True with inc show ?thesis by simp
  next
    case False with \<open>inc\<cdot>a \<sqsubseteq> a'\<close> have "a \<sqsubseteq> a'" 
      by (simp add: inc_def)(transfer, simp)
    from this inc.prems(2)
    have "eq a v1 v2" by (rule inc.IH)
    thus ?thesis by (rule eq_inc_same)
  qed
qed

lemma eq_join[simp]: "eq (a \<squnion> a') v1 v2 \<longleftrightarrow> eq a v1 v2 \<and> eq a' v1 v2"
  using Arity_total[of a a']
  apply (auto elim!: eq_mono[OF join_above1] eq_mono[OF join_above2])
  apply (metis join_self_below(2))
  apply (metis join_self_below(1))
  done

lemma eq_adm: "cont f \<Longrightarrow> cont g \<Longrightarrow> adm (\<lambda> x. eq a (f x) (g x))"
proof (induction a arbitrary: f g rule: Arity_ind[case_names 0 inc])
  case 0 thus ?case by simp
next
  case inc
  show ?case
  apply (subst eq_inc_simp)
  apply (rule adm_all)
  apply (rule inc)
  apply (intro cont2cont inc(2,3))+
  done
qed

inductive eq\<rho> :: "AEnv \<Rightarrow> (var \<Rightarrow> Value) \<Rightarrow> (var \<Rightarrow> Value) \<Rightarrow> bool" where
 eq\<rho>I: "(\<And> x a. ae x = up\<cdot>a \<Longrightarrow> eq a (\<rho>1 x) (\<rho>2 x)) \<Longrightarrow> eq\<rho> ae \<rho>1 \<rho>2"

lemma eq\<rho>E: "eq\<rho> ae \<rho>1 \<rho>2 \<Longrightarrow> ae x = up\<cdot>a \<Longrightarrow> eq a (\<rho>1 x) (\<rho>2 x)"
  by (auto simp add: eq\<rho>.simps) 

lemma eq\<rho>_refl[simp]: "eq\<rho> ae \<rho> \<rho>"
  by (simp add: eq\<rho>.simps) 

lemma eq_esing_up[simp]: "eq\<rho> (esing x\<cdot>(up\<cdot>a)) \<rho>1 \<rho>2 \<longleftrightarrow> eq a (\<rho>1 x) (\<rho>2 x)"
  by (auto simp add: eq\<rho>.simps) 
 
lemma eq\<rho>_mono:
  assumes "ae \<sqsubseteq> ae'"
  assumes "eq\<rho> ae' \<rho>1 \<rho>2"
  shows "eq\<rho> ae \<rho>1 \<rho>2"
proof (rule eq\<rho>I)
  fix x a
  assume "ae x = up\<cdot>a"
  with \<open>ae \<sqsubseteq> ae'\<close> have "up\<cdot>a \<sqsubseteq> ae' x" by (metis fun_belowD)
  then obtain a' where "ae' x = up\<cdot>a'" by (metis Exh_Up below_antisym minimal)
  with \<open>eq\<rho> ae' \<rho>1 \<rho>2\<close>
  have "eq a' (\<rho>1 x) (\<rho>2 x)" by (auto simp add: eq\<rho>.simps)
  with \<open>up\<cdot>a \<sqsubseteq> ae' x\<close> and \<open>ae' x = up\<cdot>a'\<close>
  show "eq a (\<rho>1 x) (\<rho>2 x)" by (metis eq_mono up_below)
qed

lemma eq\<rho>_adm: "cont f \<Longrightarrow> cont g \<Longrightarrow> adm (\<lambda> x. eq\<rho> a (f x) (g x))"
  apply (simp add: eq\<rho>.simps)
  apply (intro adm_lemmas eq_adm)
  apply (erule cont2cont_fun)+
  done
 
lemma up_join_eq_up[simp]: "up\<cdot>(n::'a::Finite_Join_cpo) \<squnion> up\<cdot>n' = up\<cdot>(n \<squnion> n')"
  apply (rule lub_is_join)
  apply (auto simp add: is_lub_def )
  apply (case_tac u)
  apply auto
  done
 
lemma eq\<rho>_join[simp]: "eq\<rho> (ae \<squnion> ae') \<rho>1 \<rho>2 \<longleftrightarrow> eq\<rho> ae \<rho>1 \<rho>2 \<and> eq\<rho> ae' \<rho>1 \<rho>2"
  apply (auto elim!: eq\<rho>_mono[OF join_above1] eq\<rho>_mono[OF join_above2])
  apply (auto intro!: eq\<rho>I)
  apply (case_tac "ae x", auto elim: eq\<rho>E)
  apply (case_tac "ae' x", auto elim: eq\<rho>E)
  done

lemma eq\<rho>_override[simp]:
  "eq\<rho> ae (\<rho>1 ++\<^bsub>S\<^esub> \<rho>2) (\<rho>1' ++\<^bsub>S\<^esub>\<rho>2') \<longleftrightarrow> eq\<rho> ae (\<rho>1 f|` (- S)) (\<rho>1' f|` (- S)) \<and>  eq\<rho> ae (\<rho>2 f|` S) (\<rho>2' f|` S)"
  by (auto simp add: lookup_env_restr_eq eq\<rho>.simps lookup_override_on_eq)

lemma Aexp_heap_below_Aheap:
  assumes "(Aheap \<Gamma> e\<cdot>a) x = up\<cdot>a'"
  assumes "map_of \<Gamma> x = Some e'"
  shows "Aexp e'\<cdot>a' \<sqsubseteq> Aheap \<Gamma> e\<cdot>a \<squnion> Aexp (Let \<Gamma> e)\<cdot>a"
proof-
  from assms(1)
  have "Aexp e'\<cdot>a' = ABind x e'\<cdot>(Aheap \<Gamma> e\<cdot>a)"
    by (simp del: join_comm fun_meet_simp)
  also have "\<dots> \<sqsubseteq> ABinds \<Gamma>\<cdot>(Aheap \<Gamma> e\<cdot>a)"
    by (rule monofun_cfun_fun[OF ABind_below_ABinds[OF \<open>map_of _ _ = _\<close>]])
  also have "\<dots> \<sqsubseteq> ABinds \<Gamma>\<cdot>(Aheap \<Gamma> e\<cdot>a) \<squnion>  Aexp e\<cdot>a"
    by simp
  also note Aexp_Let
  finally
  show ?thesis by this simp_all
qed

lemma Aexp_body_below_Aheap:
  shows "Aexp e\<cdot>a \<sqsubseteq> Aheap \<Gamma> e\<cdot>a \<squnion> Aexp (Let \<Gamma> e)\<cdot>a"
  by (rule below_trans[OF join_above2 Aexp_Let])


lemma Aexp_correct: "eq\<rho> (Aexp e\<cdot>a) \<rho>1 \<rho>2 \<Longrightarrow> eq a (\<lbrakk>e\<rbrakk>\<^bsub>\<rho>1\<^esub>) (\<lbrakk>e\<rbrakk>\<^bsub>\<rho>2\<^esub>)"
proof(induction a e arbitrary: \<rho>1 \<rho>2 rule: transform.induct[case_names App Lam Var Let Bool IfThenElse])
  case (Var a x)
  from \<open>eq\<rho> (Aexp (Var x)\<cdot>a) \<rho>1 \<rho>2\<close> 
  have "eq\<rho> (esing x\<cdot>(up\<cdot>a)) \<rho>1 \<rho>2" by (rule eq\<rho>_mono[OF Aexp_Var_singleton])
  thus ?case by simp
next
  case (App a e x)
  from \<open>eq\<rho> (Aexp (App e x)\<cdot>a) \<rho>1 \<rho>2\<close> 
  have "eq\<rho> (Aexp e\<cdot>(inc\<cdot>a) \<squnion> esing x\<cdot>(up\<cdot>0)) \<rho>1 \<rho>2" by (rule eq\<rho>_mono[OF Aexp_App])
  hence "eq\<rho> (Aexp e\<cdot>(inc\<cdot>a)) \<rho>1 \<rho>2" and "\<rho>1 x = \<rho>2 x" by simp_all
  from App(1)[OF this(1)] this(2)
  show ?case by (auto elim: eq.cases)
next
  case (Lam a x e)
  from  \<open>eq\<rho> (Aexp (Lam [x]. e)\<cdot>a) \<rho>1 \<rho>2\<close>
  have "eq\<rho> (env_delete x (Aexp e\<cdot>(pred\<cdot>a))) \<rho>1 \<rho>2" by (rule eq\<rho>_mono[OF Aexp_Lam])
  hence "\<And> v. eq\<rho> (Aexp e\<cdot>(pred\<cdot>a)) (\<rho>1(x := v)) (\<rho>2(x := v))"  by (auto intro!: eq\<rho>I elim!: eq\<rho>E)
  from Lam(1)[OF this]
  show ?case by (auto intro: eq_FnI simp del: fun_upd_apply)
next
  case (Bool b)
  show ?case by simp
next
  case (IfThenElse a scrut e\<^sub>1 e\<^sub>2)
  from \<open>eq\<rho> (Aexp (scrut ? e\<^sub>1 : e\<^sub>2)\<cdot>a) \<rho>1 \<rho>2\<close>
  have "eq\<rho> (Aexp scrut\<cdot>0 \<squnion> Aexp e\<^sub>1\<cdot>a \<squnion> Aexp e\<^sub>2\<cdot>a) \<rho>1 \<rho>2" by (rule eq\<rho>_mono[OF Aexp_IfThenElse])
  hence "eq\<rho> (Aexp scrut\<cdot>0) \<rho>1 \<rho>2"
  and   "eq\<rho> (Aexp e\<^sub>1\<cdot>a) \<rho>1 \<rho>2"
  and   "eq\<rho> (Aexp e\<^sub>2\<cdot>a) \<rho>1 \<rho>2" by simp_all
  from IfThenElse(1)[OF this(1)] IfThenElse(2)[OF this(2)] IfThenElse(3)[OF this(3)]
  show ?case
    by (cases "\<lbrakk> scrut \<rbrakk>\<^bsub>\<rho>2\<^esub>") auto
next
  case (Let a \<Gamma> e)

  have "eq\<rho> (Aheap \<Gamma> e\<cdot>a \<squnion> Aexp (Let \<Gamma> e)\<cdot>a) (\<lbrace>\<Gamma>\<rbrace>\<rho>1) (\<lbrace>\<Gamma>\<rbrace>\<rho>2)"
  proof(induction rule: parallel_HSem_ind[case_names adm bottom step])
    case adm thus ?case by (intro eq\<rho>_adm cont2cont)
  next
    case bottom show ?case by simp
  next
    case (step \<rho>1' \<rho>2')
    show ?case
    proof (rule eq\<rho>I)
      fix x a'
      assume ass: "(Aheap \<Gamma> e\<cdot>a \<squnion> Aexp (Let \<Gamma> e)\<cdot>a) x = up\<cdot>a'"
      show "eq a' ((\<rho>1 ++\<^bsub>domA \<Gamma>\<^esub> \<^bold>\<lbrakk> \<Gamma> \<^bold>\<rbrakk>\<^bsub>\<rho>1'\<^esub>) x) ((\<rho>2 ++\<^bsub>domA \<Gamma>\<^esub> \<^bold>\<lbrakk> \<Gamma> \<^bold>\<rbrakk>\<^bsub>\<rho>2'\<^esub>) x)"
      proof(cases "x \<in> domA \<Gamma>")
        case [simp]: True
        then obtain e' where [simp]: "map_of \<Gamma> x = Some e'" by (metis domA_map_of_Some_the)
        have "(Aheap \<Gamma> e\<cdot>a) x = up\<cdot>a'" using ass by simp
        hence "Aexp e'\<cdot>a' \<sqsubseteq> Aheap \<Gamma> e\<cdot>a \<squnion> Aexp (Let \<Gamma> e)\<cdot>a" using \<open>map_of _ _ = _\<close> by (rule Aexp_heap_below_Aheap)
        hence "eq\<rho> (Aexp e'\<cdot>a') \<rho>1' \<rho>2'" using step(1) by (rule eq\<rho>_mono)
        hence "eq a' (\<lbrakk> e' \<rbrakk>\<^bsub>\<rho>1'\<^esub>) (\<lbrakk> e' \<rbrakk>\<^bsub>\<rho>2'\<^esub>)"
          by (rule Let(1)[OF map_of_SomeD[OF \<open>map_of _ _ = _\<close>]])
        thus ?thesis by (simp add: lookupEvalHeap')
      next
        case [simp]: False
        with edom_Aheap have "x \<notin> edom (Aheap \<Gamma> e\<cdot>a)" by blast
        hence "(Aexp (Let \<Gamma> e)\<cdot>a) x = up\<cdot>a'" using ass by (simp add: edomIff)
        with \<open>eq\<rho> (Aexp (Let \<Gamma> e)\<cdot>a) \<rho>1 \<rho>2\<close>
        have "eq a' (\<rho>1 x) (\<rho>2 x)" by (auto elim: eq\<rho>E)
        thus ?thesis by simp
      qed
    qed
  qed
  hence "eq\<rho> (Aexp e\<cdot>a) (\<lbrace>\<Gamma>\<rbrace>\<rho>1) (\<lbrace>\<Gamma>\<rbrace>\<rho>2)" by (rule eq\<rho>_mono[OF Aexp_body_below_Aheap])
  hence "eq a (\<lbrakk> e \<rbrakk>\<^bsub>\<lbrace>\<Gamma>\<rbrace>\<rho>1\<^esub>) (\<lbrakk> e \<rbrakk>\<^bsub>\<lbrace>\<Gamma>\<rbrace>\<rho>2\<^esub>)" by (rule Let(2)[simplified])
  thus ?case by simp
qed

lemma ESem_ignores_fresh[simp]: "\<lbrakk> e \<rbrakk>\<^bsub>\<rho>(fresh_var e := v)\<^esub> = \<lbrakk> e \<rbrakk>\<^bsub>\<rho>\<^esub>"
  by (metis ESem_fresh_cong env_restr_fun_upd_other fresh_var_not_free)

lemma eq_Aeta_expand: "eq a (\<lbrakk> Aeta_expand a e \<rbrakk>\<^bsub>\<rho>\<^esub>) (\<lbrakk>e\<rbrakk>\<^bsub>\<rho>\<^esub>)"
  apply (induction a arbitrary: e \<rho>  rule: Arity_ind[case_names 0 inc])
  apply simp
  apply (fastforce simp add: eq_inc_simp elim: eq_trans)
  done

lemma Arity_transformation_correct: "eq a (\<lbrakk> \<T>\<^bsub>a\<^esub> e \<rbrakk>\<^bsub>\<rho>\<^esub>) (\<lbrakk> e \<rbrakk>\<^bsub>\<rho>\<^esub>)"
proof(induction a e arbitrary: \<rho> rule: transform.induct[case_names App Lam Var Let Bool IfThenElse])
  case Var
  show ?case by simp
next
  case (App a e x)
  from this[where \<rho> =\<rho> ]
  show ?case
    by (auto elim: eq.cases)
next
  case (Lam x e)
  thus ?case
    by (auto intro: eq_FnI)
next
  case (Bool b)
  show ?case by simp
next
  case (IfThenElse a e e\<^sub>1 e\<^sub>2)
  thus ?case by (cases "\<lbrakk> e \<rbrakk>\<^bsub>\<rho>\<^esub>") auto
next
  case (Let a \<Gamma> e)

  have "eq a (\<lbrakk> transform a (Let \<Gamma> e) \<rbrakk>\<^bsub>\<rho>\<^esub>) (\<lbrakk> transform a e \<rbrakk>\<^bsub>\<lbrace>map_transform Aeta_expand (Aheap \<Gamma> e\<cdot>a) (map_transform transform (Aheap \<Gamma> e\<cdot>a) \<Gamma>)\<rbrace>\<rho>\<^esub>)"
    by simp
  also have "eq a \<dots> (\<lbrakk> e \<rbrakk>\<^bsub>\<lbrace>map_transform Aeta_expand (Aheap \<Gamma> e\<cdot>a) (map_transform transform (Aheap \<Gamma> e\<cdot>a) \<Gamma>)\<rbrace>\<rho>\<^esub>)"
    using Let(2) by simp
  also have "eq a \<dots> (\<lbrakk> e \<rbrakk>\<^bsub>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub>)"
  proof (rule Aexp_correct)
    have "eq\<rho> (Aheap \<Gamma> e\<cdot>a \<squnion> Aexp (Let \<Gamma> e)\<cdot>a) (\<lbrace>map_transform Aeta_expand (Aheap \<Gamma> e\<cdot>a) (map_transform transform (Aheap \<Gamma> e\<cdot>a) \<Gamma>)\<rbrace>\<rho>) (\<lbrace>\<Gamma>\<rbrace>\<rho>)"
    proof(induction rule: parallel_HSem_ind[case_names adm bottom step])
      case adm thus ?case by (intro eq\<rho>_adm cont2cont)
    next
      case bottom show ?case by simp
    next
      case (step \<rho>1 \<rho>2)
      have "eq\<rho> (Aheap \<Gamma> e\<cdot>a \<squnion> Aexp (Let \<Gamma> e)\<cdot>a) (\<^bold>\<lbrakk> map_transform Aeta_expand (Aheap \<Gamma> e\<cdot>a) (map_transform transform (Aheap \<Gamma> e\<cdot>a) \<Gamma>) \<^bold>\<rbrakk>\<^bsub>\<rho>1\<^esub>) (\<^bold>\<lbrakk>\<Gamma>\<^bold>\<rbrakk>\<^bsub>\<rho>2\<^esub>)"
      proof(rule eq\<rho>I)
        fix x a'
        assume ass: "(Aheap \<Gamma> e\<cdot>a \<squnion> Aexp (Let \<Gamma> e)\<cdot>a) x = up\<cdot>a'"
        show "eq a' ((\<^bold>\<lbrakk> map_transform Aeta_expand (Aheap \<Gamma> e\<cdot>a) (map_transform transform (Aheap \<Gamma> e\<cdot>a) \<Gamma>) \<^bold>\<rbrakk>\<^bsub>\<rho>1\<^esub>) x) ((\<^bold>\<lbrakk>\<Gamma>\<^bold>\<rbrakk>\<^bsub>\<rho>2\<^esub>) x)"
        proof(cases "x \<in> domA \<Gamma>")
          case [simp]: True
          then obtain e' where [simp]: "map_of \<Gamma> x = Some e'" by (metis domA_map_of_Some_the)
          from ass have ass': "(Aheap \<Gamma> e\<cdot>a) x = up\<cdot>a'" by simp

          have "(\<^bold>\<lbrakk> map_transform Aeta_expand (Aheap \<Gamma> e\<cdot>a) (map_transform transform (Aheap \<Gamma> e\<cdot>a) \<Gamma>) \<^bold>\<rbrakk>\<^bsub>\<rho>1\<^esub>) x =
            \<lbrakk>Aeta_expand a' (transform a' e')\<rbrakk>\<^bsub>\<rho>1\<^esub>"
           by (simp add: lookupEvalHeap' map_of_map_transform ass')
          also have "eq a' \<dots> (\<lbrakk>transform a' e'\<rbrakk>\<^bsub>\<rho>1\<^esub>)"
            by (rule eq_Aeta_expand)
          also have "eq a' \<dots> (\<lbrakk>e'\<rbrakk>\<^bsub>\<rho>1\<^esub>)"
            by (rule Let(1)[OF map_of_SomeD[OF \<open>map_of _ _ = _\<close>]])
          also have "eq a' \<dots> (\<lbrakk>e'\<rbrakk>\<^bsub>\<rho>2\<^esub>)"
          proof (rule Aexp_correct)
            from ass' \<open>map_of _ _ = _\<close>
            have "Aexp e'\<cdot>a' \<sqsubseteq> Aheap \<Gamma> e\<cdot>a \<squnion> Aexp (Let \<Gamma> e)\<cdot>a" by (rule Aexp_heap_below_Aheap)
            thus "eq\<rho> (Aexp e'\<cdot>a') \<rho>1 \<rho>2" using step by (rule eq\<rho>_mono)
          qed
          also have "\<dots> = (\<^bold>\<lbrakk>\<Gamma>\<^bold>\<rbrakk>\<^bsub>\<rho>2\<^esub>) x"
           by (simp add: lookupEvalHeap')
          finally
          show ?thesis.
        next
          case False thus ?thesis by simp
        qed
      qed
      thus ?case
        by (simp add: env_restr_useless  order_trans[OF  edom_evalHeap_subset] del: fun_meet_simp eq\<rho>_join)
    qed
    thus "eq\<rho> (Aexp e\<cdot>a) (\<lbrace>map_transform Aeta_expand (Aheap \<Gamma> e\<cdot>a) (map_transform transform (Aheap \<Gamma> e\<cdot>a) \<Gamma>)\<rbrace>\<rho>) (\<lbrace>\<Gamma>\<rbrace>\<rho>)" 
        by (rule eq\<rho>_mono[OF Aexp_body_below_Aheap])
  qed
  also have "\<dots> = \<lbrakk> Let \<Gamma> e \<rbrakk>\<^bsub>\<rho>\<^esub>"
    by simp
  finally show ?case.
qed

corollary Arity_transformation_correct':
  "\<lbrakk> \<T>\<^bsub>0\<^esub> e \<rbrakk>\<^bsub>\<rho>\<^esub> = \<lbrakk> e \<rbrakk>\<^bsub>\<rho>\<^esub>"
  using Arity_transformation_correct[where a = 0] by simp

end
end
