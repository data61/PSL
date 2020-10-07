theory CoCallImplSafe
imports CoCallAnalysisImpl CoCallAnalysisSpec ArityAnalysisFixProps
begin

locale CoCallImplSafe
begin
sublocale CoCallAnalysisImpl.

lemma ccNeighbors_Int_ccrestr: "(ccNeighbors x G \<inter> S) = ccNeighbors x (cc_restr (insert x S) G) \<inter> S"
  by transfer auto
  
lemma 
  assumes "x \<notin> S" and "y \<notin> S"
  shows CCexp_subst: "cc_restr S (CCexp e[y::=x]\<cdot>a) = cc_restr S (CCexp e\<cdot>a)"
    and Aexp_restr_subst: "(Aexp e[y::=x]\<cdot>a) f|` S = (Aexp e\<cdot>a) f|` S"
using assms
proof (nominal_induct e avoiding: x y  arbitrary: a  S rule: exp_strong_induct_rec_set)
  case (Var b v) 
  case 1 show ?case by auto
  case 2 thus ?case by auto
next
  case (App e v)
  case 1
    with App show ?case
    by (auto simp add: Int_insert_left fv_subst_int simp del: join_comm intro: join_mono)
  case 2
    with App show ?case
     by (auto simp add: env_restr_join simp del: fun_meet_simp)
next
  case (Lam v e)
  case 1
    with Lam
    show ?case
      by (auto simp add: CCexp_pre_simps cc_restr_predCC  Diff_Int_distrib2 fv_subst_int env_restr_join env_delete_env_restr_swap[symmetric] simp del: CCexp_simps)
  case 2
    with Lam
    show ?case
      by (auto simp add: env_restr_join env_delete_env_restr_swap[symmetric]  simp del: fun_meet_simp)
next
  case (Let \<Gamma> e x y)
  hence [simp]: "x \<notin> domA \<Gamma> " "y \<notin> domA \<Gamma>"
    by (metis (erased, hide_lams) bn_subst domA_not_fresh fresh_def fresh_star_at_base fresh_star_def obtain_fresh subst_is_fresh(2))+

  note Let(1,2)[simp]

  from Let(3)
  have "\<not> nonrec (\<Gamma>[y::h=x])"  by (simp add: nonrec_subst)

  case [simp]: 1
  have "cc_restr (S \<union> domA \<Gamma>) (CCfix \<Gamma>[y::h=x]\<cdot>(Afix \<Gamma>[y::h=x]\<cdot>(Aexp e[y::=x]\<cdot>a \<squnion> (\<lambda>_. up\<cdot>0) f|` thunks \<Gamma>), CCexp e[y::=x]\<cdot>a)) =
        cc_restr (S \<union> domA \<Gamma>) (CCfix \<Gamma>\<cdot>        (Afix \<Gamma>\<cdot>        (Aexp e\<cdot>       a \<squnion> (\<lambda>_. up\<cdot>0) f|` thunks \<Gamma>), CCexp e\<cdot>       a))"
    apply (subst CCfix_restr_subst')
      apply (erule Let(4))
      apply auto[5]
    apply (subst CCfix_restr) back
      apply simp
    apply (subst Afix_restr_subst')
      apply (erule Let(5))
      apply auto[5]
    apply (subst Afix_restr) back
      apply simp
    apply (simp only: env_restr_join)
    apply (subst Let(7))
      apply auto[2]
    apply (subst Let(6))
      apply auto[2]
    apply rule
    done
  thus ?case using Let(1,2) \<open>\<not> nonrec \<Gamma>\<close> \<open>\<not> nonrec (\<Gamma>[y::h=x])\<close>
    by (auto simp add: fresh_star_Pair  elim: cc_restr_eq_subset[rotated] )

  case [simp]: 2
  have "Afix \<Gamma>[y::h=x]\<cdot>(Aexp e[y::=x]\<cdot>a \<squnion> (\<lambda>_. up\<cdot>0) f|` (thunks \<Gamma>)) f|` (S \<union> domA \<Gamma>) = Afix \<Gamma>\<cdot>(Aexp e\<cdot>a \<squnion> (\<lambda>_. up\<cdot>0) f|` (thunks \<Gamma>)) f|` (S \<union> domA \<Gamma>)"
    apply (subst Afix_restr_subst')
      apply (erule Let(5))
      apply auto[5]
    apply (subst Afix_restr) back
      apply auto[1]
    apply (simp only: env_restr_join)
    apply (subst Let(7))
      apply auto[2]
    apply rule
    done
  thus ?case using Let(1,2)
    using \<open>\<not> nonrec \<Gamma>\<close> \<open>\<not> nonrec (\<Gamma>[y::h=x])\<close>
    by (auto simp add: fresh_star_Pair elim:env_restr_eq_subset[rotated])
next
  case (Let_nonrec x' e exp x y)

  from Let_nonrec(1,2)
  have  "x \<noteq> x'" "y \<noteq> x'" by (simp_all add: fresh_at_base)

  note Let_nonrec(1,2)[simp]
  
  from \<open>x' \<notin> fv e\<close> \<open>y \<noteq> x'\<close> \<open>x \<noteq> x'\<close>
  have [simp]: "x' \<notin> fv (e[y::=x])"
    by (auto simp add: fv_subst_eq)

  note \<open>x' \<notin> fv e\<close>[simp] \<open>y \<noteq> x'\<close> [simp]\<open>x \<noteq> x'\<close>  [simp]

  case [simp]: 1

  have "\<And> a. cc_restr {x'} (CCexp exp[y::=x]\<cdot>a) = cc_restr {x'} (CCexp exp\<cdot>a)"
   by (rule Let_nonrec(6)) auto
  from arg_cong[where f = "\<lambda>x.  x'--x'\<in>x", OF this]
  have [simp]: "x'--x'\<in>CCexp  exp[y::=x]\<cdot>a \<longleftrightarrow> x'--x'\<in>CCexp exp\<cdot>a" by auto

  have [simp]: "\<And> a. Aexp e[y::=x]\<cdot>a f|` S = Aexp e\<cdot>a f|` S"
    by (rule Let_nonrec(5)) auto

  have [simp]: "\<And> a. fup\<cdot>(Aexp e[y::=x])\<cdot>a f|` S = fup\<cdot>(Aexp e)\<cdot>a f|` S"
    by (case_tac a) auto

  have [simp]: "Aexp  exp[y::=x]\<cdot>a f|` S = Aexp exp\<cdot>a f|` S"
    by (rule Let_nonrec(7)) auto

  have "Aexp exp[y::=x]\<cdot>a f|` {x'} = Aexp exp\<cdot>a f|` {x'}"
    by (rule Let_nonrec(7)) auto
  from fun_cong[OF this, where x = x']
  have [simp]: "(Aexp exp[y::=x]\<cdot>a) x' = (Aexp exp\<cdot>a) x'" by auto

  have [simp]:  "\<And> a. cc_restr S (CCexp exp[y::=x]\<cdot>a) = cc_restr S (CCexp exp\<cdot>a)"
    by (rule Let_nonrec(6)) auto

  have [simp]:  "\<And> a. cc_restr S (CCexp e[y::=x]\<cdot>a) = cc_restr S (CCexp e\<cdot>a)"
    by (rule Let_nonrec(4)) auto

  have [simp]: "\<And> a. cc_restr S (fup\<cdot>(CCexp e[y::=x])\<cdot>a) = cc_restr S (fup\<cdot>(CCexp e)\<cdot>a)"
    by (rule fup_ccExp_restr_subst') simp

  have [simp]: "fv e[y::=x] \<inter> S = fv e \<inter> S"
    by (auto simp add: fv_subst_eq)

  have [simp]:
    "ccNeighbors x' (CCexp exp[y::=x]\<cdot>a) \<inter> - {x'} \<inter> S = ccNeighbors x' (CCexp exp\<cdot>a)  \<inter> - {x'} \<inter> S"
    apply (simp only: Int_assoc)
    apply (subst (1 2) ccNeighbors_Int_ccrestr)
    apply (subst Let_nonrec(6))
      apply auto[2]
    apply rule
    done

  have [simp]:
    "ccNeighbors x' (CCexp exp[y::=x]\<cdot>a) \<inter> S = ccNeighbors x' (CCexp exp\<cdot>a) \<inter> S"
    apply (subst (1 2) ccNeighbors_Int_ccrestr)
    apply (subst Let_nonrec(6))
      apply auto[2]
    apply rule
    done

  show "cc_restr S (CCexp (let x' be e in exp )[y::=x]\<cdot>a) = cc_restr S (CCexp (let x' be e in exp )\<cdot>a)"
    apply (subst subst_let_be)
      apply auto[2]
    apply (subst (1 2) CCexp_simps(6))
      apply fact+
    apply (simp only: cc_restr_cc_delete_twist)
    apply (rule arg_cong) back
    apply (simp add:  Diff_eq ccBind_eq ABind_nonrec_eq)
    done

  show "Aexp (let x' be e in exp )[y::=x]\<cdot>a f|` S = Aexp (let x' be e in exp )\<cdot>a f|` S"
    by (simp add: env_restr_join env_delete_env_restr_swap[symmetric] ABind_nonrec_eq)
next
  case (IfThenElse scrut e1 e2)
  case [simp]: 2
    from IfThenElse
    show "cc_restr S (CCexp (scrut ? e1 : e2)[y::=x]\<cdot>a) = cc_restr S (CCexp (scrut ? e1 : e2)\<cdot>a)"
      by (auto simp del: edom_env env_restr_empty env_restr_empty_iff simp  add: edom_env[symmetric])

    from IfThenElse(2,4,6)
    show "Aexp (scrut ? e1 : e2)[y::=x]\<cdot>a f|` S = Aexp (scrut ? e1 : e2)\<cdot>a f|` S"
       by (auto simp add: env_restr_join simp del: fun_meet_simp)
qed auto
   
sublocale ArityAnalysisSafe Aexp
  by standard (simp_all add:Aexp_restr_subst)


sublocale ArityAnalysisLetSafe Aexp Aheap
proof
  fix \<Gamma> e a
  show "edom (Aheap \<Gamma> e\<cdot>a) \<subseteq> domA \<Gamma>"
    by (cases "nonrec \<Gamma>")
       (auto simp add: Aheap_nonrec_simp dest: subsetD[OF edom_esing_subset] elim!: nonrecE)
next
  fix x y :: var and \<Gamma> :: heap and e :: exp
  assume assms: "x \<notin> domA \<Gamma>"  "y \<notin> domA \<Gamma>"

  from Aexp_restr_subst[OF assms(2,1)]
  have **: "\<And> a. Aexp e[x::=y]\<cdot>a f|` domA \<Gamma> = Aexp e\<cdot>a f|` domA \<Gamma>".

  show "Aheap \<Gamma>[x::h=y] e[x::=y] = Aheap \<Gamma> e"
  proof(cases "nonrec \<Gamma>")
    case [simp]: False

    from assms
    have "atom ` domA \<Gamma> \<sharp>* x" and "atom ` domA \<Gamma> \<sharp>* y"
      by (auto simp add: fresh_star_at_base image_iff)
    hence [simp]: "\<not> nonrec (\<Gamma>[x::h=y])"
      by (simp add: nonrec_subst)

    show ?thesis
    apply (rule cfun_eqI)
    apply simp
    apply (subst Afix_restr_subst[OF assms subset_refl])
    apply (subst Afix_restr[OF  subset_refl]) back
    apply (simp add: env_restr_join)
    apply (subst **)
    apply simp
    done
  next
    case True
    
    from assms
    have "atom ` domA \<Gamma> \<sharp>* x" and "atom ` domA \<Gamma> \<sharp>* y"
      by (auto simp add: fresh_star_at_base image_iff)
    with True
    have *: "nonrec (\<Gamma>[x::h=y])" by (simp add: nonrec_subst)

    from True
    obtain x' e' where [simp]: "\<Gamma> = [(x',e')]" "x' \<notin> fv e'" by (auto elim: nonrecE)

    from * have [simp]: "x' \<notin> fv (e'[x::=y])"
      by (auto simp add: nonrec_def)

    from fun_cong[OF **, where x = x']
    have [simp]: "\<And> a. (Aexp e[x::=y]\<cdot>a) x' = (Aexp e\<cdot>a) x'" by simp

    from CCexp_subst[OF assms(2,1)]
    have "\<And> a.  cc_restr {x'} (CCexp e[x::=y]\<cdot>a) = cc_restr {x'} (CCexp e\<cdot>a)" by simp
    from arg_cong[where f = "\<lambda>x.  x'--x'\<in>x", OF this]
    have [simp]: "\<And> a. x'--x'\<in>(CCexp e[x::=y]\<cdot>a) \<longleftrightarrow> x'--x'\<in>(CCexp e\<cdot>a)" by simp
    
    show ?thesis
      apply -
      apply (rule cfun_eqI)
      apply (auto simp add: Aheap_nonrec_simp ABind_nonrec_eq)
      done
  qed
next
  fix \<Gamma> e a
  show "ABinds \<Gamma>\<cdot>(Aheap \<Gamma> e\<cdot>a) \<squnion> Aexp e\<cdot>a \<sqsubseteq> Aheap \<Gamma> e\<cdot>a \<squnion> Aexp (Let \<Gamma> e)\<cdot>a"
  proof(cases "nonrec \<Gamma>")
    case False
    thus ?thesis
      by (auto simp add: Aheap_def join_below_iff env_restr_join2 Compl_partition intro:  below_trans[OF _ Afix_above_arg])
  next
    case True
    then obtain x e' where [simp]: "\<Gamma> = [(x,e')]" "x \<notin> fv e'" by (auto elim: nonrecE)

    hence "\<And> a. x \<notin> edom (fup\<cdot>(Aexp e')\<cdot>a)"
      by (auto dest:subsetD[OF fup_Aexp_edom])
    hence [simp]: "\<And> a. (fup\<cdot>(Aexp e')\<cdot>a) x = \<bottom>" by (simp add: edomIff)

    show ?thesis
      apply (rule env_restr_below_split[where S = "{x}"])
      apply (rule env_restr_belowI2)
      apply (auto simp add:  Aheap_nonrec_simp  join_below_iff env_restr_join env_delete_restr)
      apply (rule ABind_nonrec_above_arg)
      apply (rule below_trans[OF _ join_above2])
      apply (rule below_trans[OF _ join_above2])
      apply (rule below_refl)
      done
  qed
qed

definition ccHeap_nonrec
  where "ccHeap_nonrec x e exp = (\<Lambda> n. CCfix_nonrec x e\<cdot>(Aexp exp\<cdot>n, CCexp exp\<cdot>n))"

lemma ccHeap_nonrec_eq:
   "ccHeap_nonrec x e exp\<cdot>n = CCfix_nonrec x e\<cdot>(Aexp exp\<cdot>n, CCexp exp\<cdot>n)"
unfolding ccHeap_nonrec_def by (rule beta_cfun) (intro cont2cont)

definition ccHeap_rec :: "heap \<Rightarrow> exp \<Rightarrow> Arity \<rightarrow> CoCalls"
  where "ccHeap_rec \<Gamma> e  = (\<Lambda> a. CCfix \<Gamma>\<cdot>(Afix \<Gamma>\<cdot>(Aexp e\<cdot>a \<squnion> (\<lambda>_.up\<cdot>0) f|` (thunks \<Gamma>)), CCexp e\<cdot>a))"

lemma ccHeap_rec_eq:
  "ccHeap_rec \<Gamma> e\<cdot>a = CCfix \<Gamma>\<cdot>(Afix \<Gamma>\<cdot>(Aexp e\<cdot>a \<squnion> (\<lambda>_.up\<cdot>0) f|` (thunks \<Gamma>)), CCexp e\<cdot>a)"
unfolding ccHeap_rec_def by simp

definition ccHeap :: "heap \<Rightarrow> exp \<Rightarrow> Arity \<rightarrow> CoCalls"
  where "ccHeap \<Gamma>  = (if nonrec \<Gamma> then case_prod ccHeap_nonrec (hd \<Gamma>) else ccHeap_rec \<Gamma>)"

lemma ccHeap_simp1:
  "\<not> nonrec \<Gamma> \<Longrightarrow> ccHeap \<Gamma> e\<cdot>a = CCfix \<Gamma>\<cdot>(Afix \<Gamma>\<cdot>(Aexp e\<cdot>a \<squnion> (\<lambda>_.up\<cdot>0) f|` (thunks \<Gamma>)), CCexp e\<cdot>a)"
  by (simp add: ccHeap_def ccHeap_rec_eq)

lemma ccHeap_simp2:
  "x \<notin> fv e \<Longrightarrow> ccHeap [(x,e)] exp\<cdot>n = CCfix_nonrec x e\<cdot>(Aexp exp\<cdot>n, CCexp exp\<cdot>n)"
  by (simp add: ccHeap_def ccHeap_nonrec_eq nonrec_def)


sublocale CoCallAritySafe CCexp Aexp ccHeap Aheap
proof
  fix e a x
  show "CCexp e\<cdot>(inc\<cdot>a) \<squnion> ccProd {x} (insert x (fv e)) \<sqsubseteq> CCexp (App e x)\<cdot>a"
    by simp
next
  fix y e n
  show "cc_restr (fv (Lam [y]. e)) (CCexp e\<cdot>(pred\<cdot>n)) \<sqsubseteq> CCexp (Lam [y]. e)\<cdot>n"
    by (auto simp add: CCexp_pre_simps predCC_eq dest!: subsetD[OF ccField_cc_restr] simp del: CCexp_simps)
next
  fix x y :: var and S e a
  assume "x \<notin> S"  and "y \<notin> S"
  thus "cc_restr S (CCexp e[y::=x]\<cdot>a) \<sqsubseteq> cc_restr S (CCexp e\<cdot>a)"
    by (rule eq_imp_below[OF CCexp_subst])
next
  fix e
  assume "isVal e"
  thus "CCexp e\<cdot>0 = ccSquare (fv e)"
    by (induction e rule: isVal.induct) (auto simp add: predCC_eq)
next
  fix \<Gamma> e a
  show "cc_restr (- domA \<Gamma>) (ccHeap \<Gamma> e\<cdot>a) \<sqsubseteq> CCexp (Let \<Gamma> e)\<cdot>a"
  proof(cases "nonrec \<Gamma>")
    case False
    thus "cc_restr (- domA \<Gamma>) (ccHeap \<Gamma> e\<cdot>a) \<sqsubseteq> CCexp (Let \<Gamma> e)\<cdot>a"
      by (simp add: ccHeap_simp1[OF False, symmetric] del: cc_restr_join)
  next
    case True
    thus ?thesis
      by (auto simp add: ccHeap_simp2 Diff_eq elim!: nonrecE simp del: cc_restr_join)
  qed
next
  fix \<Delta> :: heap and e a

  show "CCexp e\<cdot>a \<sqsubseteq> ccHeap \<Delta> e\<cdot>a"
    by (cases "nonrec \<Delta>")
       (auto simp add: ccHeap_simp1 ccHeap_simp2 arg_cong[OF CCfix_unroll, where f = "(\<sqsubseteq>) x" for x ] elim!: nonrecE)

  fix x e' a'
  assume "map_of \<Delta> x = Some e'"
  hence [simp]: "x \<in> domA \<Delta>" by (metis domI dom_map_of_conv_domA) 
  assume "(Aheap \<Delta> e\<cdot>a) x = up\<cdot>a'"
  show "CCexp e'\<cdot>a' \<sqsubseteq> ccHeap \<Delta> e\<cdot>a"
  proof(cases "nonrec \<Delta>")
    case False

    from \<open>(Aheap \<Delta> e\<cdot>a) x = up\<cdot>a'\<close> False
    have "(Afix \<Delta>\<cdot>(Aexp e\<cdot>a \<squnion> (\<lambda>_.up\<cdot>0)f|` (thunks \<Delta>))) x = up\<cdot>a'" 
      by (simp add: Aheap_def)
    hence "CCexp e'\<cdot>a' \<sqsubseteq> ccBind x e'\<cdot>(Afix \<Delta>\<cdot>(Aexp e\<cdot>a \<squnion> (\<lambda>_.up\<cdot>0)f|` (thunks \<Delta>)), CCfix \<Delta>\<cdot>(Afix \<Delta>\<cdot>(Aexp e\<cdot>a \<squnion> (\<lambda>_.up\<cdot>0)f|` (thunks \<Delta>)), CCexp e\<cdot>a))"
      by (auto simp add: ccBind_eq dest: subsetD[OF ccField_CCexp])
    also
    have "ccBind x e'\<cdot>(Afix \<Delta>\<cdot>(Aexp e\<cdot>a \<squnion> (\<lambda>_.up\<cdot>0)f|` (thunks \<Delta>)), CCfix \<Delta>\<cdot>(Afix \<Delta>\<cdot>(Aexp e\<cdot>a \<squnion> (\<lambda>_.up\<cdot>0)f|` (thunks \<Delta>)), CCexp e\<cdot>a)) \<sqsubseteq>  ccHeap \<Delta> e\<cdot>a"
      using \<open>map_of \<Delta> x = Some e'\<close> False
      by (fastforce simp add: ccHeap_simp1 ccHeap_rec_eq ccBindsExtra_simp  ccBinds_eq  arg_cong[OF CCfix_unroll, where f = "(\<sqsubseteq>) x" for x ]
                  intro: below_trans[OF _ join_above2])
    finally
    show "CCexp e'\<cdot>a' \<sqsubseteq> ccHeap \<Delta> e\<cdot>a" by this simp_all
  next
    case True
    with \<open>map_of \<Delta> x = Some e'\<close>
    have [simp]: "\<Delta> = [(x,e')]" "x \<notin> fv e'" by (auto elim!: nonrecE split: if_splits)

    show ?thesis
    proof(cases "x--x\<notin>CCexp e\<cdot>a \<or> isVal e'")
      case True
      with \<open>(Aheap \<Delta> e\<cdot>a) x = up\<cdot>a'\<close>
      have [simp]: "(CoCallArityAnalysis.Aexp cCCexp e\<cdot>a) x = up\<cdot>a'"
        by (auto simp add: Aheap_nonrec_simp ABind_nonrec_eq split: if_splits)

      have "CCexp e'\<cdot>a' \<sqsubseteq> ccSquare (fv e')"
        unfolding below_ccSquare
        by (rule ccField_CCexp)
      then
      show ?thesis using True
        by (auto simp add: ccHeap_simp2 ccBind_eq Aheap_nonrec_simp ABind_nonrec_eq below_trans[OF _ join_above2] simp del: below_ccSquare )
    next
      case False

      from \<open>(Aheap \<Delta> e\<cdot>a) x = up\<cdot>a'\<close>
      have [simp]: "a' = 0" using  False
        by (auto simp add: Aheap_nonrec_simp ABind_nonrec_eq split: if_splits)

      show ?thesis using False
        by (auto simp add: ccHeap_simp2 ccBind_eq Aheap_nonrec_simp ABind_nonrec_eq simp del: below_ccSquare )
    qed
  qed

  show "ccProd (fv e') (ccNeighbors x (ccHeap \<Delta> e\<cdot>a) - {x} \<inter> thunks \<Delta>) \<sqsubseteq> ccHeap \<Delta> e\<cdot>a" 
  proof (cases "nonrec \<Delta>")
    case [simp]: False

    have "ccProd (fv e') (ccNeighbors x (ccHeap \<Delta> e\<cdot>a) - {x} \<inter> thunks \<Delta>) \<sqsubseteq> ccProd (fv e') (ccNeighbors x (ccHeap \<Delta> e\<cdot>a))"
      by (rule ccProd_mono2) auto
    also have "\<dots> \<sqsubseteq> (\<Squnion>x\<mapsto>e'\<in>map_of \<Delta>. ccProd (fv e') (ccNeighbors x (ccHeap \<Delta> e\<cdot>a)))" 
      using \<open>map_of \<Delta> x = Some e'\<close> by (rule below_lubmapI)
    also have "\<dots> \<sqsubseteq> ccBindsExtra \<Delta>\<cdot>(Afix \<Delta>\<cdot>(Aexp e\<cdot>a \<squnion> (\<lambda>_.up\<cdot>0)f|` (thunks \<Delta>)), ccHeap \<Delta> e\<cdot>a)"
      by (simp add: ccBindsExtra_simp  below_trans[OF _ join_above2])
    also have "\<dots> \<sqsubseteq> ccHeap \<Delta> e\<cdot>a"
      by (simp add: ccHeap_simp1  arg_cong[OF CCfix_unroll, where f = "(\<sqsubseteq>) x" for x])
    finally
    show ?thesis by this simp_all
  next
    case True
    with \<open>map_of \<Delta> x = Some e'\<close>
    have [simp]: "\<Delta> = [(x,e')]" "x \<notin> fv e'" by (auto elim!: nonrecE split: if_splits)

    have [simp]: "(ccNeighbors x (ccBind x e'\<cdot>(Aexp e\<cdot>a, CCexp e\<cdot>a))) = {}"
     by (auto simp add: ccBind_eq dest!: subsetD[OF ccField_cc_restr] subsetD[OF ccField_fup_CCexp])

    show ?thesis
    proof(cases "isVal e' \<and> x--x\<in>CCexp e\<cdot>a")
    case True

    have "ccNeighbors x (ccHeap \<Delta> e\<cdot>a) =
        ccNeighbors x (ccBind x e'\<cdot>(Aheap_nonrec x e'\<cdot>(Aexp e\<cdot>a, CCexp e\<cdot>a), CCexp e\<cdot>a)) \<union>
        ccNeighbors x (ccProd (fv e') (ccNeighbors x (CCexp e\<cdot>a) - (if isVal e' then {} else {x}))) \<union>
        ccNeighbors x (CCexp e\<cdot>a)" by (auto simp add: ccHeap_simp2 )
    also have "ccNeighbors x (ccBind  x e'\<cdot>(Aheap_nonrec x e'\<cdot>(Aexp e\<cdot>a, CCexp e\<cdot>a), CCexp e\<cdot>a)) = {}"
       by (auto simp add: ccBind_eq dest!: subsetD[OF ccField_cc_restr] subsetD[OF ccField_fup_CCexp])
    also have "ccNeighbors x (ccProd (fv e') (ccNeighbors x (CCexp e\<cdot>a) - (if isVal e' then {} else {x})))
      \<subseteq> ccNeighbors x (ccProd (fv e') (ccNeighbors x (CCexp e\<cdot>a)))" by (simp add: ccNeighbors_ccProd)
    also have "\<dots> \<subseteq> fv e'" by (simp add: ccNeighbors_ccProd)
    finally
    have "ccNeighbors x (ccHeap \<Delta> e\<cdot>a) - {x} \<inter> thunks \<Delta> \<subseteq> ccNeighbors x (CCexp e\<cdot>a) \<union> fv e'" by auto
    hence "ccProd (fv e') (ccNeighbors x (ccHeap \<Delta> e\<cdot>a) - {x} \<inter> thunks \<Delta>) \<sqsubseteq> ccProd (fv e') (ccNeighbors x (CCexp e\<cdot>a) \<union> fv e')" by (rule ccProd_mono2)
    also have "\<dots> \<sqsubseteq> ccProd (fv e') (ccNeighbors x (CCexp e\<cdot>a)) \<squnion> ccProd (fv e') (fv e')" by simp
    also have "ccProd (fv e') (ccNeighbors x (CCexp e\<cdot>a)) \<sqsubseteq> ccHeap \<Delta> e\<cdot>a"
      using \<open>map_of \<Delta> x = Some e'\<close> \<open>(Aheap \<Delta> e\<cdot>a) x = up\<cdot>a'\<close> True
      by (auto simp add: ccHeap_simp2  below_trans[OF _ join_above2])
    also have "ccProd (fv e') (fv e') = ccSquare (fv e')" by (simp add: ccSquare_def)
    also have "\<dots> \<sqsubseteq> ccHeap \<Delta> e\<cdot>a"
      using \<open>map_of \<Delta> x = Some e'\<close> \<open>(Aheap \<Delta> e\<cdot>a) x = up\<cdot>a'\<close> True
      by (auto simp add: ccHeap_simp2  ccBind_eq below_trans[OF _ join_above2])
    also note join_self
    finally show ?thesis by this simp_all
  next
    case False
    have "ccNeighbors x (ccHeap \<Delta> e\<cdot>a) =
        ccNeighbors x (ccBind x e'\<cdot>(Aheap_nonrec x e'\<cdot>(Aexp e\<cdot>a, CCexp e\<cdot>a), CCexp e\<cdot>a)) \<union>
        ccNeighbors x (ccProd (fv e') (ccNeighbors x (CCexp e\<cdot>a) - (if isVal e' then {} else {x}))) \<union>
        ccNeighbors x (CCexp e\<cdot>a)" by (auto simp add: ccHeap_simp2 )
    also have "ccNeighbors x (ccBind  x e'\<cdot>(Aheap_nonrec x e'\<cdot>(Aexp e\<cdot>a, CCexp e\<cdot>a), CCexp e\<cdot>a)) = {}"
       by (auto simp add: ccBind_eq dest!: subsetD[OF ccField_cc_restr] subsetD[OF ccField_fup_CCexp])
    also have  "ccNeighbors x (ccProd (fv e') (ccNeighbors x (CCexp e\<cdot>a) - (if isVal e' then {} else {x}) )) 
      = {}" using False by (auto simp add: ccNeighbors_ccProd)
    finally
    have "ccNeighbors x (ccHeap \<Delta> e\<cdot>a) \<subseteq> ccNeighbors x (CCexp e\<cdot>a)" by auto
    hence"ccNeighbors x (ccHeap \<Delta> e\<cdot>a)  - {x} \<inter> thunks \<Delta> \<subseteq> ccNeighbors x (CCexp e\<cdot>a)   - {x} \<inter> thunks \<Delta>" by auto
    hence "ccProd (fv e') (ccNeighbors x (ccHeap \<Delta> e\<cdot>a) - {x} \<inter> thunks \<Delta> ) \<sqsubseteq> ccProd (fv e') (ccNeighbors x (CCexp e\<cdot>a)  - {x} \<inter> thunks \<Delta> )" by (rule ccProd_mono2)
    also have "\<dots> \<sqsubseteq> ccHeap \<Delta> e\<cdot>a"
      using \<open>map_of \<Delta> x = Some e'\<close> \<open>(Aheap \<Delta> e\<cdot>a) x = up\<cdot>a'\<close> False
      by (auto simp add: ccHeap_simp2  thunks_Cons below_trans[OF _ join_above2])
    finally show ?thesis by this simp_all
   qed
  qed

next
  fix x \<Gamma> e a
  assume [simp]: "\<not> nonrec \<Gamma>"
  assume "x \<in> thunks \<Gamma>"
  hence [simp]: "x \<in> domA \<Gamma>" by (rule subsetD[OF thunks_domA])
  assume "x \<in> edom (Aheap \<Gamma> e\<cdot>a)"

  from \<open>x \<in> thunks \<Gamma>\<close>
  have "(Afix \<Gamma>\<cdot>(Aexp e\<cdot>a \<squnion> (\<lambda>_.up\<cdot>0)f|` (thunks \<Gamma>))) x = up\<cdot>0" 
    by (subst Afix_unroll) simp

  thus "(Aheap \<Gamma> e\<cdot>a) x = up\<cdot>0" by simp
next
  fix x \<Gamma> e a
  assume "nonrec \<Gamma>"
  then obtain x' e' where [simp]: "\<Gamma> = [(x',e')]" "x' \<notin> fv e'" by (auto elim: nonrecE)
  assume "x \<in> thunks \<Gamma>"
  hence [simp]: "x = x'" "\<not> isVal e'" by (auto simp add: thunks_Cons split: if_splits)

  assume "x--x \<in> CCexp e\<cdot>a"
  hence [simp]: "x'--x'\<in> CCexp  e\<cdot>a" by simp

  from \<open>x \<in> thunks \<Gamma>\<close>
  have "(Afix \<Gamma>\<cdot>(Aexp e\<cdot>a \<squnion> (\<lambda>_.up\<cdot>0)f|` (thunks \<Gamma>))) x = up\<cdot>0" 
    by (subst Afix_unroll) simp

  show "(Aheap \<Gamma> e\<cdot>a) x = up\<cdot>0" by (auto simp add: Aheap_nonrec_simp ABind_nonrec_eq)
next
  fix scrut e1 a e2
  show "CCexp scrut\<cdot>0 \<squnion> (CCexp e1\<cdot>a \<squnion> CCexp e2\<cdot>a) \<squnion> ccProd (edom (Aexp scrut\<cdot>0)) (edom (Aexp e1\<cdot>a) \<union> edom (Aexp e2\<cdot>a)) \<sqsubseteq> CCexp (scrut ? e1 : e2)\<cdot>a"
    by simp
qed
end

end
