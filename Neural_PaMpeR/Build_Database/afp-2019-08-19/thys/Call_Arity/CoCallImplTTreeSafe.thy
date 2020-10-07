theory CoCallImplTTreeSafe
imports CoCallImplTTree CoCallAnalysisSpec TTreeAnalysisSpec
begin

lemma valid_lists_many_calls:
  assumes "\<not> one_call_in_path x p"
  assumes "p \<in> valid_lists S G"
  shows "x--x \<in> G"
using assms(2,1)
proof(induction rule:valid_lists.induct[case_names Nil Cons])
  case Nil thus ?case by simp
next
  case (Cons xs x')
  show ?case
  proof(cases "one_call_in_path x xs")
    case False
    from Cons.IH[OF this]
    show ?thesis.
  next
    case True
    with \<open>\<not> one_call_in_path x (x' # xs)\<close>
    have [simp]: "x' = x" by (auto split: if_splits)

    have "x \<in> set xs"
    proof(rule ccontr)
      assume "x \<notin> set xs"
      hence "no_call_in_path x xs" by (metis no_call_in_path_set_conv)
      hence "one_call_in_path x (x # xs)" by simp
      with Cons show False by simp
    qed
    with \<open>set xs \<subseteq> ccNeighbors x' G\<close>
    have "x \<in> ccNeighbors x G" by auto
    thus ?thesis by simp
  qed
qed

context CoCallArityEdom
begin
 lemma carrier_Fexp': "carrier (Texp e\<cdot>a) \<subseteq> fv e"
    unfolding Texp_simp carrier_ccTTree
    by (rule Aexp_edom)

end


context CoCallAritySafe
begin

lemma carrier_AnalBinds_below:
  "carrier ((Texp.AnalBinds  \<Delta>\<cdot>(Aheap \<Delta> e\<cdot>a)) x) \<subseteq> edom ((ABinds \<Delta>)\<cdot>(Aheap \<Delta> e\<cdot>a))"
by (auto simp add: Texp.AnalBinds_lookup Texp_def split: option.splits 
         elim!: subsetD[OF edom_mono[OF monofun_cfun_fun[OF ABind_below_ABinds]]])

sublocale TTreeAnalysisCarrier Texp
  apply standard
  unfolding Texp_simp carrier_ccTTree
  apply standard
  done

sublocale TTreeAnalysisSafe Texp
proof
  fix x e a

  from edom_mono[OF Aexp_App]
  have "{x} \<union> edom (Aexp e\<cdot>(inc\<cdot>a)) \<subseteq> edom (Aexp (App e x)\<cdot>a)" by auto
  moreover
  {
  have "ccApprox (many_calls x \<otimes>\<otimes> ccTTree (edom (Aexp e\<cdot>(inc\<cdot>a))) (ccExp e\<cdot>(inc\<cdot>a))) 
    = cc_restr (edom (Aexp e\<cdot>(inc\<cdot>a))) (ccExp e\<cdot>(inc\<cdot>a)) \<squnion> ccProd {x} (insert x (edom (Aexp e\<cdot>(inc\<cdot>a))))"
    by (simp add: ccApprox_both ccProd_insert2[where S' = "edom e" for e])
  also
  have "edom (Aexp e\<cdot>(inc\<cdot>a)) \<subseteq> fv e"
    by (rule Aexp_edom)
  also(below_trans[OF eq_imp_below join_mono[OF below_refl ccProd_mono2[OF insert_mono] ]])
  have "cc_restr (edom (Aexp e\<cdot>(inc\<cdot>a))) (ccExp e\<cdot>(inc\<cdot>a)) \<sqsubseteq> ccExp e\<cdot>(inc\<cdot>a)"
    by (rule cc_restr_below_arg)
  also
  have "ccExp e\<cdot>(inc\<cdot>a) \<squnion> ccProd {x} (insert x (fv e)) \<sqsubseteq> ccExp (App e x)\<cdot>a" 
    by (rule ccExp_App)
  finally
  have "ccApprox (many_calls x \<otimes>\<otimes> ccTTree (edom (Aexp e\<cdot>(inc\<cdot>a))) (ccExp e\<cdot>(inc\<cdot>a))) \<sqsubseteq> ccExp (App e x)\<cdot>a" by this simp_all
  }
  ultimately
  show "many_calls x \<otimes>\<otimes> Texp e\<cdot>(inc\<cdot>a) \<sqsubseteq> Texp (App e x)\<cdot>a"
    unfolding Texp_simp by (auto intro!: below_ccTTreeI)
next
  fix y e n
  show "without y (Texp e\<cdot>(pred\<cdot>n)) \<sqsubseteq> Texp (Lam [y]. e)\<cdot>n"
    unfolding Texp_simp
    by (auto dest: subsetD[OF Aexp_edom]
             intro!: below_ccTTreeI  below_trans[OF _ ccExp_Lam] cc_restr_mono1 subsetD[OF edom_mono[OF Aexp_Lam]])
next
  fix e y x a

  from edom_mono[OF Aexp_subst]
  have *: "edom (Aexp e[y::=x]\<cdot>a) \<subseteq> insert x (edom (Aexp e\<cdot>a) - {y})" by simp

  have "Texp e[y::=x]\<cdot>a = ccTTree (edom (Aexp e[y::=x]\<cdot>a)) (ccExp e[y::=x]\<cdot>a)"
    unfolding Texp_simp..
  also have "\<dots> \<sqsubseteq> ccTTree (insert x (edom (Aexp e\<cdot>a) - {y})) (ccExp e[y::=x]\<cdot>a)"
    by (rule ccTTree_mono1[OF *])
  also have "\<dots> \<sqsubseteq> many_calls x \<otimes>\<otimes> without x (\<dots>)"
    by (rule paths_many_calls_subset)
  also have "without x (ccTTree (insert x (edom (Aexp e\<cdot>a) - {y})) (ccExp e[y::=x]\<cdot>a))
    = ccTTree (edom (Aexp e\<cdot>a) - {y} - {x}) (ccExp e[y::=x]\<cdot>a)"
    by simp
  also have "\<dots> \<sqsubseteq> ccTTree (edom (Aexp e\<cdot>a) - {y} - {x}) (ccExp e\<cdot>a)"
    by (rule ccTTree_cong_below[OF ccExp_subst]) auto
  also have "\<dots> = without y (ccTTree (edom (Aexp e\<cdot>a) - {x}) (ccExp e\<cdot>a))"
    by simp (metis Diff_insert Diff_insert2)
  also have "ccTTree (edom (Aexp e\<cdot>a) - {x}) (ccExp e\<cdot>a) \<sqsubseteq> ccTTree (edom (Aexp e\<cdot>a)) (ccExp e\<cdot>a)"
    by (rule ccTTree_mono1) auto
  also have "\<dots> = Texp e\<cdot>a"
    unfolding Texp_simp..
  finally
  show "Texp e[y::=x]\<cdot>a \<sqsubseteq> many_calls x \<otimes>\<otimes> without y (Texp e\<cdot>a)"
    by this simp_all
next
  fix v a
  have "up\<cdot>a \<sqsubseteq> (Aexp (Var v)\<cdot>a) v" by (rule Aexp_Var)
  hence "v \<in> edom (Aexp (Var v)\<cdot>a)" by (auto simp add: edom_def)
  thus "single v \<sqsubseteq> Texp (Var v)\<cdot>a"
    unfolding Texp_simp
    by (auto intro: below_ccTTreeI)
next
  fix scrut e1 a e2
  have "ccTTree (edom (Aexp e1\<cdot>a)) (ccExp e1\<cdot>a) \<oplus>\<oplus> ccTTree (edom (Aexp e2\<cdot>a)) (ccExp e2\<cdot>a)
    \<sqsubseteq> ccTTree (edom (Aexp e1\<cdot>a) \<union> edom (Aexp e2\<cdot>a)) (ccExp e1\<cdot>a \<squnion> ccExp e2\<cdot>a)"
      by (rule either_ccTTree)
  note both_mono2'[OF this]
  also
  have "ccTTree (edom (Aexp scrut\<cdot>0)) (ccExp scrut\<cdot>0) \<otimes>\<otimes> ccTTree (edom (Aexp e1\<cdot>a) \<union> edom (Aexp e2\<cdot>a)) (ccExp e1\<cdot>a \<squnion> ccExp e2\<cdot>a)
    \<sqsubseteq> ccTTree (edom (Aexp scrut\<cdot>0) \<union> (edom (Aexp e1\<cdot>a) \<union> edom (Aexp e2\<cdot>a))) (ccExp scrut\<cdot>0 \<squnion> (ccExp e1\<cdot>a \<squnion> ccExp e2\<cdot>a) \<squnion> ccProd (edom (Aexp scrut\<cdot>0)) (edom (Aexp e1\<cdot>a) \<union> edom (Aexp e2\<cdot>a)))"
    by (rule interleave_ccTTree)
  also
  have "edom (Aexp scrut\<cdot>0) \<union> (edom (Aexp e1\<cdot>a) \<union> edom (Aexp e2\<cdot>a)) = edom (Aexp scrut\<cdot>0 \<squnion> Aexp e1\<cdot>a \<squnion> Aexp e2\<cdot>a)" by auto
  also
  have "Aexp scrut\<cdot>0 \<squnion> Aexp e1\<cdot>a \<squnion> Aexp e2\<cdot>a \<sqsubseteq> Aexp (scrut ? e1 : e2)\<cdot>a"
    by (rule Aexp_IfThenElse)
  also
  have "ccExp scrut\<cdot>0 \<squnion> (ccExp e1\<cdot>a \<squnion> ccExp e2\<cdot>a) \<squnion> ccProd (edom (Aexp scrut\<cdot>0)) (edom (Aexp e1\<cdot>a) \<union> edom (Aexp e2\<cdot>a)) \<sqsubseteq>
        ccExp (scrut ? e1 : e2)\<cdot>a"
    by (rule ccExp_IfThenElse)
  
  show "Texp scrut\<cdot>0 \<otimes>\<otimes> (Texp e1\<cdot>a \<oplus>\<oplus> Texp e2\<cdot>a) \<sqsubseteq> Texp (scrut ? e1 : e2)\<cdot>a"
    unfolding Texp_simp
    by (auto simp add: ccApprox_both join_below_iff  below_trans[OF _ join_above2]
             intro!: below_ccTTreeI below_trans[OF cc_restr_below_arg]
                     below_trans[OF _ ccExp_IfThenElse]  subsetD[OF edom_mono[OF Aexp_IfThenElse]])
next
  fix e
  assume "isVal e"
  hence [simp]: "ccExp e\<cdot>0 = ccSquare (fv e)" by (rule ccExp_pap)
  thus "repeatable (Texp e\<cdot>0)"
    unfolding Texp_simp by (auto intro: repeatable_ccTTree_ccSquare[OF Aexp_edom])
qed

definition Theap :: "heap \<Rightarrow> exp \<Rightarrow> Arity \<rightarrow> var ttree"
  where "Theap \<Gamma> e = (\<Lambda> a. if nonrec \<Gamma> then ccTTree (edom (Aheap \<Gamma> e\<cdot>a)) (ccExp e\<cdot>a) else ttree_restr (edom (Aheap \<Gamma> e\<cdot>a)) anything)"

lemma Theap_simp: "Theap \<Gamma> e\<cdot>a = (if nonrec \<Gamma> then ccTTree (edom (Aheap \<Gamma> e\<cdot>a)) (ccExp e\<cdot>a) else ttree_restr (edom (Aheap \<Gamma> e\<cdot>a)) anything)"
  unfolding Theap_def by simp

lemma carrier_Fheap':"carrier (Theap \<Gamma> e\<cdot>a) = edom (Aheap \<Gamma> e\<cdot>a)"
    unfolding Theap_simp carrier_ccTTree by simp

sublocale TTreeAnalysisCardinalityHeap Texp Aexp Aheap Theap
proof
  fix \<Gamma> e a
  show "carrier (Theap \<Gamma> e\<cdot>a) = edom (Aheap \<Gamma> e\<cdot>a)"
    by (rule carrier_Fheap')
next
  fix x \<Gamma> p e a
  assume "x \<in> thunks \<Gamma>"
  
  assume "\<not> one_call_in_path x p"
  hence "x \<in> set p" by (rule more_than_one_setD)
  
  assume "p \<in> paths (Theap \<Gamma> e\<cdot>a)" with \<open>x \<in> set p\<close>
  have "x \<in> carrier (Theap \<Gamma> e\<cdot>a)" by (auto simp add: Union_paths_carrier[symmetric])
  hence "x \<in> edom (Aheap \<Gamma> e\<cdot>a)"
    unfolding Theap_simp by (auto split: if_splits)
  
  show "(Aheap \<Gamma> e\<cdot>a) x = up\<cdot>0"
  proof(cases "nonrec \<Gamma>")
    case False
    from False \<open>x \<in> thunks \<Gamma>\<close>  \<open>x \<in> edom (Aheap \<Gamma> e\<cdot>a)\<close>
    show ?thesis  by (rule aHeap_thunks_rec)
  next
    case True
    with \<open>p \<in> paths (Theap \<Gamma> e\<cdot>a)\<close>
    have "p \<in> valid_lists (edom (Aheap \<Gamma> e\<cdot>a)) (ccExp e\<cdot>a)" by (simp add: Theap_simp)

    with \<open>\<not> one_call_in_path x p\<close>
    have "x--x\<in> (ccExp e\<cdot>a)" by (rule valid_lists_many_calls)
  
    from True \<open>x \<in> thunks \<Gamma>\<close> this
    show ?thesis by (rule aHeap_thunks_nonrec)
  qed
next
  fix \<Delta> e a

  have carrier: "carrier (substitute (Texp.AnalBinds \<Delta>\<cdot>(Aheap \<Delta> e\<cdot>a)) (thunks \<Delta>) (Texp e\<cdot>a)) \<subseteq> edom (Aheap \<Delta> e\<cdot>a) \<union> edom (Aexp (Let \<Delta> e)\<cdot>a)"
  proof(rule carrier_substitute_below)
    from edom_mono[OF Aexp_Let[of \<Delta> e a]]
    show "carrier (Texp e\<cdot>a) \<subseteq> edom (Aheap \<Delta> e\<cdot>a) \<union> edom (Aexp (Let \<Delta> e)\<cdot>a)"  by (simp add: Texp_def)
  next
    fix x
    assume "x \<in> edom (Aheap \<Delta> e\<cdot>a) \<union> edom (Aexp (Let \<Delta> e)\<cdot>a)"
    hence "x \<in> edom (Aheap \<Delta> e\<cdot>a) \<or> x : (edom (Aexp (Let \<Delta> e)\<cdot>a))" by simp
    thus "carrier ((Texp.AnalBinds  \<Delta>\<cdot>(Aheap \<Delta> e\<cdot>a)) x) \<subseteq> edom (Aheap \<Delta> e\<cdot>a) \<union> edom (Aexp (Let \<Delta> e)\<cdot>a)"
    proof
      assume "x \<in> edom (Aheap \<Delta> e\<cdot>a)"
      
      have "carrier ((Texp.AnalBinds  \<Delta>\<cdot>(Aheap \<Delta> e\<cdot>a)) x) \<subseteq> edom (ABinds \<Delta>\<cdot>(Aheap \<Delta> e\<cdot>a))"
        by (rule carrier_AnalBinds_below)
      also have "\<dots> \<subseteq> edom (Aheap \<Delta> e\<cdot>a \<squnion> Aexp (Terms.Let \<Delta> e)\<cdot>a)"
        using edom_mono[OF Aexp_Let[of \<Delta> e a]] by simp
      finally show ?thesis by simp
    next
      assume "x \<in> edom (Aexp (Terms.Let \<Delta> e)\<cdot>a)"
      hence "x \<notin> domA \<Delta>" by (auto  dest: subsetD[OF Aexp_edom])
      hence "(Texp.AnalBinds  \<Delta>\<cdot>(Aheap \<Delta> e\<cdot>a)) x = \<bottom>"
        by (rule Texp.AnalBinds_not_there)
      thus ?thesis by simp
    qed
  qed

  show "ttree_restr (- domA \<Delta>) (substitute (Texp.AnalBinds \<Delta>\<cdot>(Aheap \<Delta> e\<cdot>a)) (thunks \<Delta>) (Texp e\<cdot>a)) \<sqsubseteq> Texp (Let \<Delta> e)\<cdot>a"
  proof (rule below_trans[OF _ eq_imp_below[OF Texp_simp[symmetric]]], rule below_ccTTreeI)
    have "carrier (ttree_restr (- domA \<Delta>) (substitute (Texp.AnalBinds \<Delta>\<cdot>(Aheap \<Delta> e\<cdot>a)) (thunks \<Delta>) (Texp e\<cdot>a)))
       = carrier (substitute (Texp.AnalBinds \<Delta>\<cdot>(Aheap \<Delta> e\<cdot>a)) (thunks \<Delta>) (Texp e\<cdot>a)) - domA \<Delta>" by auto
    also note carrier
    also have "edom (Aheap \<Delta> e\<cdot>a) \<union> edom (Aexp (Terms.Let \<Delta> e)\<cdot>a) - domA \<Delta> = edom (Aexp (Let \<Delta> e)\<cdot>a)"
      by (auto dest: subsetD[OF edom_Aheap] subsetD[OF Aexp_edom])
    finally
    show "carrier (ttree_restr (- domA \<Delta>) (substitute (Texp.AnalBinds \<Delta>\<cdot>(Aheap \<Delta> e\<cdot>a)) (thunks \<Delta>)(Texp e\<cdot>a)))
          \<subseteq> edom (Aexp (Terms.Let \<Delta> e)\<cdot>a)" by this auto
  next
    let ?x = "ccApprox (ttree_restr (- domA \<Delta>) (substitute (Texp.AnalBinds \<Delta>\<cdot>(Aheap \<Delta> e\<cdot>a)) (thunks \<Delta>) (Texp e\<cdot>a)))"
  
    have "?x = cc_restr (- domA \<Delta>) ?x"  by simp
    also have "\<dots> \<sqsubseteq> cc_restr (- domA \<Delta>) (ccHeap \<Delta> e\<cdot>a)"
    proof(rule cc_restr_mono2[OF wild_recursion_thunked])
      have "ccExp e\<cdot>a \<sqsubseteq> ccHeap \<Delta> e\<cdot>a" by (rule ccHeap_Exp)
      thus "ccApprox (Texp e\<cdot>a) \<sqsubseteq> ccHeap \<Delta> e\<cdot>a"
        by (auto simp add: Texp_simp intro: below_trans[OF cc_restr_below_arg])
    next
      fix x
      assume "x \<notin> domA \<Delta>"
      thus "(Texp.AnalBinds \<Delta>\<cdot>(Aheap \<Delta> e\<cdot>a)) x = empty"
        by (metis Texp.AnalBinds_not_there empty_is_bottom)
    next
      fix x
      assume "x \<in> domA \<Delta>"
      then obtain e' where e': "map_of \<Delta> x = Some e'" by (metis domA_map_of_Some_the)
      
      show "ccApprox ((Texp.AnalBinds \<Delta>\<cdot>(Aheap \<Delta> e\<cdot>a)) x) \<sqsubseteq> ccHeap \<Delta> e\<cdot>a"
      proof(cases "(Aheap \<Delta> e\<cdot>a) x")
        case bottom thus ?thesis using e' by (simp add: Texp.AnalBinds_lookup)
      next
        case (up a')
        with e'
        have "ccExp e'\<cdot>a' \<sqsubseteq> ccHeap \<Delta> e\<cdot>a" by (rule ccHeap_Heap)
        thus ?thesis using up e'
          by (auto simp add: Texp.AnalBinds_lookup Texp_simp  intro: below_trans[OF cc_restr_below_arg])
      qed

      show "ccProd (ccNeighbors x (ccHeap \<Delta> e\<cdot>a)- {x} \<inter> thunks \<Delta>) (carrier ((Texp.AnalBinds  \<Delta>\<cdot>(Aheap \<Delta> e\<cdot>a)) x)) \<sqsubseteq> ccHeap \<Delta> e\<cdot>a"
      proof(cases "(Aheap \<Delta> e\<cdot>a) x")
        case bottom thus ?thesis using e' by (simp add: Texp.AnalBinds_lookup)
      next
        case (up a')
        have subset: "(carrier (fup\<cdot>(Texp e')\<cdot>((Aheap \<Delta> e\<cdot>a) x))) \<subseteq> fv e'"
          using up e' by (auto simp add: Texp.AnalBinds_lookup carrier_Fexp dest!: subsetD[OF Aexp_edom])
        
        from e' up
        have "ccProd (fv e') (ccNeighbors x (ccHeap \<Delta> e\<cdot>a) - {x} \<inter> thunks \<Delta>) \<sqsubseteq> ccHeap \<Delta> e\<cdot>a"
          by (rule ccHeap_Extra_Edges)
        then
        show ?thesis using e'
          by (simp add: Texp.AnalBinds_lookup  Texp_simp ccProd_comm  below_trans[OF ccProd_mono2[OF subset]])
      qed
    qed
    also have "\<dots> \<sqsubseteq> ccExp (Let \<Delta> e)\<cdot>a"
      by (rule ccExp_Let)
    finally
    show "ccApprox (ttree_restr (- domA \<Delta>) (substitute (Texp.AnalBinds \<Delta>\<cdot>(Aheap \<Delta> e\<cdot>a)) (thunks \<Delta>) (Texp e\<cdot>a)))
        \<sqsubseteq> ccExp (Terms.Let \<Delta> e)\<cdot>a" by this simp_all
  qed

  note carrier
  hence "carrier (substitute (ExpAnalysis.AnalBinds Texp \<Delta>\<cdot>(Aheap \<Delta> e\<cdot>a)) (thunks \<Delta>) (Texp e\<cdot>a)) \<subseteq> edom (Aheap \<Delta> e\<cdot>a) \<union> - domA \<Delta>"
    by (rule order_trans) (auto dest: subsetD[OF Aexp_edom])
  hence "ttree_restr (domA \<Delta>)            (substitute (Texp.AnalBinds \<Delta>\<cdot>(Aheap \<Delta> e\<cdot>a)) (thunks \<Delta>) (Texp e\<cdot>a))
      = ttree_restr (edom (Aheap \<Delta> e\<cdot>a)) (ttree_restr (domA \<Delta>) (substitute (Texp.AnalBinds  \<Delta>\<cdot>(Aheap \<Delta> e\<cdot>a)) (thunks \<Delta>) (Texp e\<cdot>a)))"
    by -(rule ttree_restr_noop[symmetric], auto)
  also
  have "\<dots> = ttree_restr (edom (Aheap \<Delta> e\<cdot>a)) (substitute (Texp.AnalBinds  \<Delta>\<cdot>(Aheap \<Delta> e\<cdot>a)) (thunks \<Delta>) (Texp e\<cdot>a))"
    by (simp add: inf.absorb2[OF edom_Aheap ])
  also
  have "\<dots> \<sqsubseteq> Theap \<Delta> e \<cdot>a"
  proof(cases "nonrec \<Delta>")
    case False
    have "ttree_restr (edom (Aheap \<Delta> e\<cdot>a)) (substitute (Texp.AnalBinds \<Delta>\<cdot>(Aheap \<Delta> e\<cdot>a)) (thunks \<Delta>) (Texp e\<cdot>a))
      \<sqsubseteq> ttree_restr (edom (Aheap \<Delta> e\<cdot>a)) anything"
      by (rule ttree_restr_mono) simp
    also have "\<dots> = Theap \<Delta> e\<cdot>a"
      by (simp add: Theap_simp False)
    finally show ?thesis.
  next
    case [simp]: True

    from True
    have "ttree_restr (edom (Aheap \<Delta> e\<cdot>a)) (substitute (Texp.AnalBinds \<Delta>\<cdot>(Aheap \<Delta> e\<cdot>a)) (thunks \<Delta>) (Texp e\<cdot>a))
       = ttree_restr (edom (Aheap \<Delta> e\<cdot>a)) (Texp e\<cdot>a)"
      by (rule nonrecE) (rule ttree_rest_substitute, auto simp add: carrier_Fexp fv_def fresh_def dest!: subsetD[OF edom_Aheap] subsetD[OF Aexp_edom])
    also have "\<dots> = ccTTree (edom (Aexp e\<cdot>a) \<inter> edom (Aheap \<Delta> e\<cdot>a)) (ccExp e\<cdot>a)"
      by (simp add: Texp_simp)
    also have "\<dots> \<sqsubseteq> ccTTree (edom (Aexp e\<cdot>a) \<inter> domA \<Delta>) (ccExp e\<cdot>a)"
      by (rule ccTTree_mono1[OF Int_mono[OF order_refl edom_Aheap]])
    also have "\<dots> \<sqsubseteq> ccTTree (edom (Aheap \<Delta> e\<cdot>a)) (ccExp e\<cdot>a)"
      by (rule ccTTree_mono1[OF edom_mono[OF Aheap_nonrec[OF True], simplified]])
    also have "\<dots> \<sqsubseteq> Theap \<Delta> e\<cdot>a"
      by (simp add: Theap_simp)
    finally
    show ?thesis by this simp_all
  qed
  finally
  show "ttree_restr (domA \<Delta>) (substitute (ExpAnalysis.AnalBinds Texp \<Delta>\<cdot>(Aheap \<Delta> e\<cdot>a)) (thunks \<Delta>) (Texp e\<cdot>a)) \<sqsubseteq> Theap \<Delta> e\<cdot>a".

qed
end

(* TODO: Unused stuff from here, mostly about singles. Might be useful later. *)


lemma paths_singles: "xs \<in> paths (singles S) \<longleftrightarrow> (\<forall>x \<in> S. one_call_in_path x xs)"
  by transfer (auto simp add: one_call_in_path_filter_conv)

lemma paths_singles': "xs \<in> paths (singles S) \<longleftrightarrow> (\<forall>x \<in> (set xs \<inter> S). one_call_in_path x xs)"
  apply transfer
  apply (auto simp add: one_call_in_path_filter_conv)
  apply (erule_tac x = x in ballE)
  apply auto
  by (metis (poly_guards_query) filter_empty_conv le0 length_0_conv)

lemma both_below_singles1:
  assumes "t \<sqsubseteq> singles S"
  assumes "carrier t' \<inter> S = {}"
  shows "t \<otimes>\<otimes> t' \<sqsubseteq> singles S"
proof (rule ttree_belowI)
  fix xs
  assume "xs \<in> paths (t \<otimes>\<otimes> t')"
  then obtain ys zs where "ys \<in> paths t" and "zs \<in> paths t'" and "xs \<in> ys \<otimes> zs" by (auto simp add: paths_both)
  with assms 
  have "ys \<in> paths (singles S)" and "set zs \<inter> S = {}"
    by (metis below_ttree.rep_eq contra_subsetD paths.rep_eq, auto simp add: Union_paths_carrier[symmetric])
  with \<open>xs \<in> ys \<otimes> zs\<close>
  show "xs \<in> paths (singles S)"
    by (induction) (auto simp add: paths_singles no_call_in_path_set_conv interleave_set dest: more_than_one_setD split: if_splits)
qed


lemma paths_ttree_restr_singles: "xs \<in> paths (ttree_restr S' (singles S)) \<longleftrightarrow> set xs \<subseteq> S' \<and> (\<forall>x \<in> S. one_call_in_path x xs)"
proof
  show "xs \<in> paths (ttree_restr S' (singles S)) \<Longrightarrow>  set xs \<subseteq> S' \<and> (\<forall>x \<in> S. one_call_in_path x xs)"
    by (auto simp add: filter_paths_conv_free_restr[symmetric] paths_singles)
next
  assume *: "set xs \<subseteq> S' \<and> (\<forall>x\<in>S. one_call_in_path x xs)"
  hence "set xs \<subseteq> S'" by auto
  hence [simp]: "filter (\<lambda> x'. x' \<in> S') xs = xs" by (auto simp add: filter_id_conv)
  
  from *
  have "xs \<in> paths (singles S)"
     by (auto simp add: paths_singles')
  hence "filter (\<lambda> x'. x' \<in> S') xs \<in> filter (\<lambda>x'. x' \<in> S') ` paths (singles S)"
    by (rule imageI)
  thus "xs \<in> paths (ttree_restr S' (singles S))"
    by (auto simp add: filter_paths_conv_free_restr[symmetric] )
qed



(* TODO: unused *)
lemma substitute_not_carrier:
  assumes "x \<notin> carrier t"
  assumes "\<And> x'. x \<notin> carrier (f x')"
  shows "x \<notin>  carrier (substitute f T t)"
proof-
  have "ttree_restr ({x}) (substitute f T t) = ttree_restr ({x}) t"
  proof(rule ttree_rest_substitute)
    fix x'
    from \<open>x \<notin> carrier (f x')\<close>
    show "carrier (f x') \<inter> {x} = {}" by auto
  qed
  hence "x \<notin> carrier (ttree_restr ({x}) (substitute f T t)) \<longleftrightarrow> x \<notin> carrier (ttree_restr ({x}) t)" by metis
  with assms(1)
  show ?thesis by simp
qed

(* TODO: unused *)
lemma substitute_below_singlesI:
  assumes "t \<sqsubseteq> singles S"
  assumes "\<And> x. carrier (f x) \<inter> S = {}"
  shows "substitute f T t \<sqsubseteq> singles S"
proof(rule ttree_belowI)
  fix xs
  assume "xs \<in> paths (substitute f T t)"
  thus "xs \<in> paths (singles S)"
  using assms
  proof(induction f T t xs arbitrary: S rule: substitute_induct)
    case Nil
    thus ?case by simp
  next
    case (Cons f T t x xs)

    from \<open>x#xs \<in> _\<close>
    have xs: "xs \<in> paths (substitute (f_nxt f T x) T (nxt t x \<otimes>\<otimes> f x))" by auto
    moreover

    from \<open>t \<sqsubseteq> singles S\<close>
    have "nxt t x \<sqsubseteq> singles S" 
      by (metis "TTree-HOLCF.nxt_mono" below_trans nxt_singles_below_singles)
    from this \<open>carrier (f x) \<inter> S = {}\<close>
    have "nxt t x \<otimes>\<otimes> f x \<sqsubseteq> singles S"
      by (rule both_below_singles1)
    moreover
    { fix x'
      from  \<open>carrier (f x') \<inter> S = {}\<close>
      have "carrier (f_nxt f T x x') \<inter> S = {}"
        by (auto simp add: f_nxt_def)
    }
    ultimately
    have IH: "xs \<in> paths (singles S)"
      by (rule Cons.IH) 
  
  show ?case
    proof(cases "x \<in> S")
      case True
      with \<open>carrier (f x) \<inter> S = {}\<close>
      have "x \<notin> carrier (f x)" by auto
      moreover
      from \<open>t \<sqsubseteq> singles S\<close>
      have "nxt t x \<sqsubseteq> nxt (singles S) x" by (rule nxt_mono)
      hence "carrier (nxt t x) \<subseteq> carrier (nxt (singles S) x)" by (rule carrier_mono)
      from subsetD[OF this] True
      have "x \<notin> carrier (nxt t x)" by auto
      ultimately
      have "x \<notin> carrier (nxt t x \<otimes>\<otimes> f x)" by simp
      hence "x \<notin> carrier (substitute (f_nxt f T x) T (nxt t x \<otimes>\<otimes> f x))"
      proof(rule substitute_not_carrier)
        fix x'  
        from \<open>carrier (f x') \<inter> S = {}\<close> \<open>x \<in> S\<close>
        show "x \<notin> carrier (f_nxt f T x x')" by (auto simp add: f_nxt_def)
      qed
      with xs
      have "x \<notin> set xs" by (auto simp add: Union_paths_carrier[symmetric])
      with IH
      have "xs \<in> paths (without x (singles S))" by (rule paths_withoutI)
      thus ?thesis using True by (simp add: Cons_path)
    next
      case False
      with IH
      show ?thesis by (simp add: Cons_path)
    qed
  qed
qed

end

