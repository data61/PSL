theory TTreeImplCardinalitySafe
imports TTreeImplCardinality TTreeAnalysisSpec CardinalityAnalysisSpec
begin

lemma pathsCard_paths_nxt:  "pathsCard (paths (nxt f x)) \<sqsubseteq> record_call x\<cdot>(pathsCard (paths f))"
  apply transfer
  apply (rule pathsCard_below)
  apply auto
  apply (erule below_trans[OF _ monofun_cfun_arg[OF paths_Card_above], rotated]) back
  apply (auto intro: fun_belowI simp add: record_call_simp two_pred_two_add_once)
  done

lemma pathsCards_none: "pathsCard (paths t) x = none \<Longrightarrow> x \<notin> carrier t"
  by transfer (auto dest: pathCards_noneD)

lemma const_on_edom_disj: "const_on f S empty \<longleftrightarrow> edom f \<inter> S = {}"
  by (auto simp add: empty_is_bottom edom_def)

context TTreeAnalysisCarrier
begin
  lemma carrier_Fstack: "carrier (Fstack as S) \<subseteq> fv S"
    by (induction S rule: Fstack.induct)
       (auto simp add: empty_is_bottom[symmetric] carrier_Fexp dest!: subsetD[OF Aexp_edom])

  lemma carrier_FBinds: "carrier ((FBinds \<Gamma>\<cdot>ae) x) \<subseteq> fv \<Gamma>"
  apply (simp add: Texp.AnalBinds_lookup)
  apply (auto split: option.split simp add: empty_is_bottom[symmetric] )
  apply (case_tac "ae x")
  apply (auto simp add: empty_is_bottom[symmetric] carrier_Fexp dest!: subsetD[OF Aexp_edom])
  by (metis (poly_guards_query) contra_subsetD domA_from_set map_of_fv_subset map_of_SomeD option.sel)
end

context TTreeAnalysisSafe
begin

  sublocale CardinalityPrognosisShape prognosis
  proof
    fix \<Gamma> :: heap and ae ae' :: AEnv and u e S as
    assume "ae f|` domA \<Gamma> = ae' f|` domA \<Gamma>"
    from Texp.AnalBinds_cong[OF this]
    show "prognosis ae as u (\<Gamma>, e, S) = prognosis ae' as u (\<Gamma>, e, S)" by simp
  next
    fix ae as a \<Gamma> e S
    show "const_on (prognosis ae as a (\<Gamma>, e, S)) (ap S) many"
    proof
      fix x
      assume "x \<in> ap S"
      hence "[x,x] \<in> paths (Fstack as S)"
        by (induction S rule: Fstack.induct)
           (auto 4 4 intro: subsetD[OF both_contains_arg1] subsetD[OF both_contains_arg2] paths_Cons_nxt)
      hence "[x,x] \<in> paths (Texp e\<cdot>a \<otimes>\<otimes> Fstack as S)"
        by (rule subsetD[OF both_contains_arg2])
      hence "[x,x] \<in> paths (substitute (FBinds \<Gamma>\<cdot>ae) (thunks \<Gamma>) (Texp e\<cdot>a \<otimes>\<otimes> Fstack as S))" 
        by (rule subsetD[OF substitute_contains_arg])
      hence "pathCard [x,x] x \<sqsubseteq> pathsCard (paths (substitute (FBinds \<Gamma>\<cdot>ae) (thunks \<Gamma>) (Texp e\<cdot>a \<otimes>\<otimes> Fstack as S))) x"
        by (metis fun_belowD paths_Card_above)
      also have "pathCard [x,x] x = many"  by (auto simp add: pathCard_def)
      finally
      show "prognosis ae as a (\<Gamma>, e, S) x = many"
        by (auto intro: below_antisym)
    qed
  next
    fix \<Gamma> \<Delta> :: heap and e :: exp and ae :: AEnv and as u S
    assume "map_of \<Gamma> = map_of \<Delta>"
    hence "FBinds \<Gamma> = FBinds \<Delta>" and "thunks \<Gamma> = thunks \<Delta>" by (auto intro!: cfun_eqI  thunks_cong simp add: Texp.AnalBinds_lookup)
    thus "prognosis ae as u (\<Gamma>, e, S) = prognosis ae as u (\<Delta>, e, S)"  by simp
  next
    fix \<Gamma> :: heap and e :: exp and ae :: AEnv and as u S x
    show "prognosis ae as u (\<Gamma>, e, S) \<sqsubseteq> prognosis ae as u (\<Gamma>, e, Upd x # S)" by simp
  next
  fix \<Gamma> :: heap and e :: exp and ae :: AEnv and as a S x
  assume "ae x = \<bottom>"

  hence "FBinds (delete x \<Gamma>)\<cdot>ae = FBinds \<Gamma>\<cdot>ae" by (rule Texp.AnalBinds_delete_bot)
  moreover
  hence "((FBinds \<Gamma>\<cdot>ae) x) = \<bottom>" by (metis Texp.AnalBinds_delete_lookup)
  ultimately
  show "prognosis ae as a (\<Gamma>, e, S) \<sqsubseteq> prognosis ae as a (delete x \<Gamma>, e, S)"
    by (simp add: substitute_T_delete empty_is_bottom)
  next
    fix ae as a \<Gamma> x S
    have "once \<sqsubseteq> (pathCard [x]) x" by (simp add: two_add_simp)
    also have "pathCard [x] \<sqsubseteq> pathsCard ({[],[x]})"
      by (rule paths_Card_above) simp
    also have "\<dots> = pathsCard (paths (single x))" by simp
    also have "single x \<sqsubseteq> (Texp (Var x)\<cdot>a)" by (rule Texp_Var)
    also have "\<dots> \<sqsubseteq> Texp (Var x)\<cdot>a \<otimes>\<otimes> Fstack as S" by (rule both_above_arg1)
    also have "\<dots> \<sqsubseteq> substitute  (FBinds \<Gamma>\<cdot>ae) (thunks \<Gamma>) (Texp (Var x)\<cdot>a \<otimes>\<otimes> Fstack as S)" by (rule substitute_above_arg)
    also have "pathsCard (paths \<dots>) x = prognosis ae as a (\<Gamma>, Var x, S) x" by simp
    finally
    show "once \<sqsubseteq> prognosis ae as a (\<Gamma>, Var x, S) x"
      by this (rule cont2cont_fun, intro cont2cont)+
  qed

  sublocale CardinalityPrognosisApp prognosis
  proof
    fix ae as a \<Gamma> e x S
    have "Texp e\<cdot>(inc\<cdot>a)  \<otimes>\<otimes> many_calls x \<otimes>\<otimes> Fstack as S = many_calls x  \<otimes>\<otimes> (Texp e)\<cdot>(inc\<cdot>a) \<otimes>\<otimes> Fstack as S"
      by (metis both_assoc both_comm)
    thus "prognosis ae as (inc\<cdot>a) (\<Gamma>, e, Arg x # S) \<sqsubseteq> prognosis ae as a (\<Gamma>, App e x, S)"
      by simp (intro pathsCard_mono' paths_mono substitute_mono2' both_mono1' Texp_App)
  qed

  sublocale CardinalityPrognosisLam prognosis
  proof
    fix ae as a \<Gamma> e y x S
    have "Texp e[y::=x]\<cdot>(pred\<cdot>a) \<sqsubseteq> many_calls x  \<otimes>\<otimes> Texp (Lam [y]. e)\<cdot>a"
      by (rule below_trans[OF Texp_subst both_mono2'[OF Texp_Lam]])
    moreover have "Texp (Lam [y]. e)\<cdot>a \<otimes>\<otimes> many_calls x \<otimes>\<otimes> Fstack as S = many_calls x  \<otimes>\<otimes> Texp (Lam [y]. e)\<cdot>a \<otimes>\<otimes> Fstack as S"
      by (metis both_assoc both_comm)
    ultimately  
    show "prognosis ae as (pred\<cdot>a) (\<Gamma>, e[y::=x], S) \<sqsubseteq> prognosis ae as a (\<Gamma>, Lam [y]. e, Arg x # S)"
      by simp (intro pathsCard_mono' paths_mono substitute_mono2' both_mono1')
  qed

  sublocale CardinalityPrognosisVar prognosis
  proof
    fix \<Gamma> :: heap and e :: exp and x :: var and ae :: AEnv and as u a S
    assume "map_of \<Gamma> x = Some e"
    assume "ae x = up\<cdot>u"

    assume "isVal e"
    hence "x \<notin> thunks \<Gamma>" using \<open>map_of \<Gamma> x = Some e\<close> by (metis thunksE)
    hence [simp]: "f_nxt (FBinds \<Gamma>\<cdot>ae) (thunks \<Gamma>) x = FBinds \<Gamma>\<cdot>ae" by (auto simp add: f_nxt_def)

    have "prognosis ae as u (\<Gamma>, e, S) = pathsCard (paths (substitute (FBinds \<Gamma>\<cdot>ae) (thunks \<Gamma>) (Texp e\<cdot>u \<otimes>\<otimes> Fstack as S)))"
      by simp
    also have "\<dots> = pathsCard (paths (substitute (FBinds \<Gamma>\<cdot>ae) (thunks \<Gamma>) (nxt (single x) x \<otimes>\<otimes> Texp e\<cdot>u  \<otimes>\<otimes> Fstack as S)))"
      by simp
    also have "\<dots> = pathsCard (paths (substitute (FBinds \<Gamma>\<cdot>ae) (thunks \<Gamma>) ((nxt (single x) x \<otimes>\<otimes> Fstack as S) \<otimes>\<otimes> Texp e\<cdot>u )))"
      by (metis both_assoc both_comm)
    also have "\<dots> \<sqsubseteq> pathsCard (paths (substitute (FBinds \<Gamma>\<cdot>ae) (thunks \<Gamma>) (nxt (single x \<otimes>\<otimes> Fstack as S) x \<otimes>\<otimes> Texp e\<cdot>u)))"
      by (intro pathsCard_mono' paths_mono substitute_mono2' both_mono1'  nxt_both_left) simp
    also have "\<dots> = pathsCard (paths (nxt (substitute (FBinds \<Gamma>\<cdot>ae) (thunks \<Gamma>) (single x \<otimes>\<otimes> Fstack as S)) x))"
      using \<open>map_of \<Gamma> x = Some e\<close> \<open>ae x = up\<cdot>u\<close> by (simp add: Texp.AnalBinds_lookup)
    also have "\<dots> \<sqsubseteq> record_call x \<cdot>(pathsCard (paths (substitute (FBinds \<Gamma>\<cdot>ae) (thunks \<Gamma>) (single x \<otimes>\<otimes> Fstack as S))))"
      by (rule pathsCard_paths_nxt)
    also have "\<dots> \<sqsubseteq> record_call x \<cdot>(pathsCard (paths (substitute (FBinds \<Gamma>\<cdot>ae) (thunks \<Gamma>) ((Texp (Var x)\<cdot>a) \<otimes>\<otimes> Fstack as S))))"
      by (intro monofun_cfun_arg pathsCard_mono' paths_mono substitute_mono2' both_mono1' Texp_Var)
    also have "\<dots> = record_call x \<cdot>(prognosis ae as a (\<Gamma>, Var x, S))"
      by simp
    finally
    show "prognosis ae as u (\<Gamma>, e, S) \<sqsubseteq> record_call x\<cdot>(prognosis ae as a (\<Gamma>, Var x, S))" by this simp_all
  next
    fix \<Gamma> :: heap and e :: exp and x :: var and ae :: AEnv and as u a S
    assume "map_of \<Gamma> x = Some e"
    assume "ae x = up\<cdot>u"
    assume "\<not> isVal e"
    hence "x \<in> thunks \<Gamma>" using \<open>map_of \<Gamma> x = Some e\<close> by (metis thunksI)
    hence [simp]: "f_nxt (FBinds \<Gamma>\<cdot>ae) (thunks \<Gamma>) x = FBinds (delete x \<Gamma>)\<cdot>ae" 
      by (auto simp add: f_nxt_def Texp.AnalBinds_delete_to_fun_upd empty_is_bottom)

    have "prognosis ae as u (delete x \<Gamma>, e, Upd x # S) = pathsCard (paths (substitute (FBinds (delete x \<Gamma>)\<cdot>ae) (thunks (delete x \<Gamma>)) (Texp e\<cdot>u \<otimes>\<otimes> Fstack as S)))"
      by simp
    also have "\<dots> = pathsCard (paths (substitute (FBinds (delete x \<Gamma>)\<cdot>ae) (thunks \<Gamma>) (Texp e\<cdot>u \<otimes>\<otimes> Fstack as S)))"
       by (rule arg_cong[OF substitute_cong_T]) (auto simp add: empty_is_bottom)
    also have "\<dots> = pathsCard (paths (substitute (FBinds (delete x \<Gamma>)\<cdot>ae) (thunks \<Gamma>) (nxt (single x) x \<otimes>\<otimes> Texp e\<cdot>u  \<otimes>\<otimes> Fstack as S)))"
      by simp
    also have "\<dots> = pathsCard (paths (substitute (FBinds (delete x \<Gamma>)\<cdot>ae) (thunks \<Gamma>) ((nxt (single x) x \<otimes>\<otimes> Fstack as S) \<otimes>\<otimes> Texp e\<cdot>u )))"
      by (metis both_assoc both_comm)
    also have "\<dots> \<sqsubseteq> pathsCard (paths (substitute (FBinds (delete x \<Gamma>)\<cdot>ae) (thunks \<Gamma>) (nxt (single x \<otimes>\<otimes> Fstack as S) x  \<otimes>\<otimes> Texp e\<cdot>u)))"
      by (intro pathsCard_mono' paths_mono substitute_mono2' both_mono1'  nxt_both_left) simp
    also have "\<dots> = pathsCard (paths (nxt (substitute (FBinds \<Gamma>\<cdot>ae) (thunks \<Gamma>) (single x \<otimes>\<otimes> Fstack as S)) x))"
      using \<open>map_of \<Gamma> x = Some e\<close> \<open>ae x = up\<cdot>u\<close> by (simp add: Texp.AnalBinds_lookup)
    also have "\<dots> \<sqsubseteq> record_call x \<cdot>(pathsCard (paths (substitute (FBinds \<Gamma>\<cdot>ae) (thunks \<Gamma>) (single x \<otimes>\<otimes> Fstack as S))))"
      by (rule pathsCard_paths_nxt)
    also have "\<dots> \<sqsubseteq> record_call x \<cdot>(pathsCard (paths (substitute (FBinds \<Gamma>\<cdot>ae) (thunks \<Gamma>) ((Texp (Var x)\<cdot>a) \<otimes>\<otimes> Fstack as S))))"
      by (intro monofun_cfun_arg pathsCard_mono' paths_mono substitute_mono2' both_mono1' Texp_Var)
    also have "\<dots> = record_call x \<cdot>(prognosis ae as a (\<Gamma>, Var x, S))"
      by simp
    finally
    show "prognosis ae as u (delete x \<Gamma>, e, Upd x # S) \<sqsubseteq> record_call x\<cdot>(prognosis ae as a (\<Gamma>, Var x, S))" by this simp_all
  next
    fix \<Gamma> :: heap and e :: exp and ae :: AEnv and  x :: var and as S
    assume "isVal e"
    hence "repeatable (Texp e\<cdot>0)" by (rule Fun_repeatable)

    assume [simp]: "x \<notin> domA \<Gamma>"

    have [simp]: "thunks ((x, e) # \<Gamma>) = thunks \<Gamma>" 
      using \<open>isVal e\<close>
      by (auto simp add: thunks_Cons dest: subsetD[OF thunks_domA])

    have "fup\<cdot>(Texp e)\<cdot>(ae x) \<sqsubseteq> Texp e\<cdot>0" by (metis fup2 monofun_cfun_arg up_zero_top)
    hence "substitute ((FBinds \<Gamma>\<cdot>ae)(x := fup\<cdot>(Texp e)\<cdot>(ae x))) (thunks \<Gamma>) (Texp e\<cdot>0 \<otimes>\<otimes> Fstack as S) \<sqsubseteq> substitute ((FBinds \<Gamma>\<cdot>ae)(x := Texp e\<cdot>0)) (thunks \<Gamma>) (Texp e\<cdot>0 \<otimes>\<otimes> Fstack as S)"
      by (intro substitute_mono1' fun_upd_mono below_refl monofun_cfun_arg)
    also have "\<dots> = substitute (((FBinds \<Gamma>\<cdot>ae)(x := Texp e\<cdot>0))(x := empty)) (thunks \<Gamma>) (Texp e\<cdot>0 \<otimes>\<otimes> Fstack as S)"
      using \<open>repeatable (Texp e\<cdot>0)\<close> by (rule substitute_remove_anyways, simp)
    also have "((FBinds \<Gamma>\<cdot>ae)(x := Texp e\<cdot>0))(x := empty) = FBinds \<Gamma>\<cdot>ae"
      by (simp add: fun_upd_idem Texp.AnalBinds_not_there empty_is_bottom)
    finally
    show "prognosis ae as 0 ((x, e) # \<Gamma>, e, S) \<sqsubseteq> prognosis ae as 0 (\<Gamma>, e, Upd x # S)"
      by (simp, intro pathsCard_mono' paths_mono)
  qed

  sublocale CardinalityPrognosisIfThenElse prognosis
  proof
    fix ae as \<Gamma> scrut e1 e2 S a
    have "Texp scrut\<cdot>0 \<otimes>\<otimes> (Texp e1\<cdot>a \<oplus>\<oplus> Texp e2\<cdot>a) \<sqsubseteq> Texp (scrut ? e1 : e2)\<cdot>a"
      by (rule Texp_IfThenElse)
    hence "substitute (FBinds \<Gamma>\<cdot>ae) (thunks \<Gamma>) (Texp scrut\<cdot>0 \<otimes>\<otimes> (Texp e1\<cdot>a \<oplus>\<oplus> Texp e2\<cdot>a) \<otimes>\<otimes> Fstack as S) \<sqsubseteq> substitute (FBinds \<Gamma>\<cdot>ae) (thunks \<Gamma>) (Texp (scrut ? e1 : e2)\<cdot>a \<otimes>\<otimes> Fstack as S)"
      by (rule substitute_mono2'[OF both_mono1'])
    thus "prognosis ae (a#as) 0 (\<Gamma>, scrut, Alts e1 e2 # S) \<sqsubseteq> prognosis ae as a (\<Gamma>, scrut ? e1 : e2, S)"
      by (simp, intro pathsCard_mono' paths_mono)
  next
    fix ae as a \<Gamma> b e1 e2 S
    have "Texp (if b then e1 else e2)\<cdot>a \<sqsubseteq> Texp e1\<cdot>a \<oplus>\<oplus> Texp e2\<cdot>a"
      by (auto simp add: either_above_arg1 either_above_arg2)
    hence "substitute (FBinds \<Gamma>\<cdot>ae) (thunks \<Gamma>) (Texp (if b then e1 else e2)\<cdot>a \<otimes>\<otimes> Fstack as S) \<sqsubseteq> substitute (FBinds \<Gamma>\<cdot>ae) (thunks \<Gamma>) (Texp (Bool b)\<cdot>0 \<otimes>\<otimes> (Texp e1\<cdot>a \<oplus>\<oplus> Texp e2\<cdot>a) \<otimes>\<otimes> Fstack as S)"
      by (rule substitute_mono2'[OF both_mono1'[OF below_trans[OF _ both_above_arg2]]])
    thus "prognosis ae as a (\<Gamma>, if b then e1 else e2, S) \<sqsubseteq> prognosis ae (a#as) 0 (\<Gamma>, Bool b, Alts e1 e2 # S)"
      by (auto intro!: pathsCard_mono' paths_mono)
  qed

end

context TTreeAnalysisCardinalityHeap
begin

  definition cHeap where
    "cHeap \<Gamma> e = (\<Lambda> a. pathsCard (paths (Theap \<Gamma> e\<cdot>a)))"

  lemma cHeap_simp: "(cHeap \<Gamma> e)\<cdot>a = pathsCard (paths (Theap \<Gamma> e\<cdot>a))"
    unfolding cHeap_def  by (rule beta_cfun) (intro cont2cont)
  
  sublocale CardinalityHeap cHeap.
 
  sublocale CardinalityHeapSafe cHeap Aheap
  proof
    fix x \<Gamma> e a
    assume "x \<in> thunks \<Gamma>"
    moreover
    assume "many \<sqsubseteq> (cHeap \<Gamma> e\<cdot>a) x"
    hence "many \<sqsubseteq> pathsCard (paths (Theap \<Gamma> e \<cdot>a)) x" unfolding cHeap_def by simp
    hence "\<exists>p\<in> (paths (Theap \<Gamma> e\<cdot>a)). \<not> (one_call_in_path x p)" unfolding pathsCard_def
      by (auto split: if_splits)
    ultimately
    show "(Aheap \<Gamma> e\<cdot>a) x = up\<cdot>0"
      by (metis Theap_thunk)
  next
    fix \<Gamma> e a
    show "edom (cHeap \<Gamma> e\<cdot>a) = edom (Aheap \<Gamma> e\<cdot>a)"
    by (simp add: cHeap_def Union_paths_carrier carrier_Fheap)
  qed

  sublocale CardinalityPrognosisEdom prognosis 
  proof
    fix ae as a \<Gamma> e S
    show "edom (prognosis ae as a (\<Gamma>, e, S)) \<subseteq> fv \<Gamma> \<union> fv e \<union> fv S"
      apply (simp add: Union_paths_carrier)
      apply (rule carrier_substitute_below)
      apply (auto simp add: carrier_Fexp dest: subsetD[OF Aexp_edom] subsetD[OF carrier_Fstack] subsetD[OF ap_fv_subset] subsetD[OF carrier_FBinds])
      done
  qed
  
  sublocale CardinalityPrognosisLet prognosis cHeap
  proof
    fix \<Delta> \<Gamma> :: heap and e :: exp and S :: stack and  ae :: AEnv and a :: Arity and as
    assume "atom ` domA \<Delta> \<sharp>* \<Gamma>"
    assume "atom ` domA \<Delta> \<sharp>* S"
    assume "edom ae \<subseteq> domA \<Gamma> \<union> upds S"

    have "domA \<Delta> \<inter> edom ae = {}"
      using fresh_distinct[OF \<open>atom ` domA \<Delta> \<sharp>* \<Gamma>\<close>] fresh_distinct_fv[OF \<open>atom ` domA \<Delta> \<sharp>* S\<close>] 
            \<open>edom ae \<subseteq> domA \<Gamma> \<union> upds S\<close> ups_fv_subset[of S]
      by auto

    have const_on1:  "\<And> x. const_on (FBinds \<Delta>\<cdot>(Aheap \<Delta> e\<cdot>a)) (carrier ((FBinds \<Gamma>\<cdot>ae) x)) empty"
      unfolding const_on_edom_disj using fresh_distinct_fv[OF \<open>atom ` domA \<Delta> \<sharp>* \<Gamma>\<close>]
      by (auto dest!: subsetD[OF carrier_FBinds] subsetD[OF Texp.edom_AnalBinds])
    have const_on2:  "const_on (FBinds \<Delta>\<cdot>(Aheap \<Delta> e\<cdot>a)) (carrier (Fstack as S)) empty"
      unfolding const_on_edom_disj using fresh_distinct_fv[OF \<open>atom ` domA \<Delta> \<sharp>* S\<close>]
      by (auto dest!: subsetD[OF carrier_FBinds] subsetD[OF carrier_Fstack] subsetD[OF Texp.edom_AnalBinds] subsetD[OF ap_fv_subset ])
    have  const_on3: "const_on (FBinds \<Gamma>\<cdot>ae) (- (- domA \<Delta>)) TTree.empty"
      and const_on4: "const_on (FBinds \<Delta>\<cdot>(Aheap \<Delta> e\<cdot>a)) (domA \<Gamma>) TTree.empty"
      unfolding const_on_edom_disj using fresh_distinct[OF \<open>atom ` domA \<Delta> \<sharp>* \<Gamma>\<close>]
      by (auto dest!:  subsetD[OF Texp.edom_AnalBinds])

    have disj1: "\<And> x. carrier ((FBinds \<Gamma>\<cdot>ae) x) \<inter> domA \<Delta> = {}"
      using fresh_distinct_fv[OF \<open>atom ` domA \<Delta> \<sharp>* \<Gamma>\<close>]
      by (auto dest: subsetD[OF carrier_FBinds])
    hence disj1': "\<And> x. carrier ((FBinds \<Gamma>\<cdot>ae) x) \<subseteq> - domA \<Delta>" by auto
    have disj2: "\<And> x. carrier (Fstack as S) \<inter> domA \<Delta> = {}"
      using fresh_distinct_fv[OF \<open>atom ` domA \<Delta> \<sharp>* S\<close>] by (auto dest!: subsetD[OF carrier_Fstack])
    hence disj2': "carrier (Fstack as S) \<subseteq> - domA \<Delta>" by auto
    

    {
    fix x
    have "(FBinds (\<Delta> @ \<Gamma>)\<cdot>(ae \<squnion> Aheap \<Delta> e\<cdot>a)) x = (FBinds \<Gamma>\<cdot>ae) x \<otimes>\<otimes> (FBinds \<Delta>\<cdot>(Aheap \<Delta> e\<cdot>a)) x"
    proof (cases "x \<in> domA \<Delta>")
      case True
      have "map_of \<Gamma> x = None" using True fresh_distinct[OF \<open>atom ` domA \<Delta> \<sharp>* \<Gamma>\<close>] by (metis disjoint_iff_not_equal domA_def map_of_eq_None_iff)
      moreover
      have "ae x = \<bottom>" using True \<open>domA \<Delta> \<inter> edom ae = {}\<close> by auto
      ultimately
      show ?thesis using True 
          by (auto simp add: Texp.AnalBinds_lookup empty_is_bottom[symmetric] cong: option.case_cong)
    next
      case False
      have "map_of \<Delta> x = None" using False by (metis domA_def map_of_eq_None_iff)
      moreover
      have "(Aheap \<Delta> e\<cdot>a) x = \<bottom>" using False using edom_Aheap by (metis contra_subsetD edomIff)
      ultimately
      show ?thesis using False
         by (auto simp add: Texp.AnalBinds_lookup empty_is_bottom[symmetric] cong: option.case_cong)
    qed
    }
    note FBinds = ext[OF this]
    
    {
    have "pathsCard (paths (substitute (FBinds (\<Delta> @ \<Gamma>)\<cdot>(Aheap \<Delta> e\<cdot>a \<squnion> ae)) (thunks (\<Delta> @ \<Gamma>)) (Texp e\<cdot>a \<otimes>\<otimes> Fstack as S)))
      = pathsCard (paths (substitute (FBinds \<Gamma>\<cdot>ae) (thunks (\<Delta> @ \<Gamma>)) (substitute (FBinds \<Delta>\<cdot>(Aheap \<Delta> e\<cdot>a))  (thunks (\<Delta> @ \<Gamma>))  (Texp e\<cdot>a \<otimes>\<otimes> Fstack as S))))"
       by (simp add: substitute_substitute[OF const_on1] FBinds)
    also have "substitute (FBinds \<Gamma>\<cdot>ae) (thunks (\<Delta> @ \<Gamma>)) = substitute (FBinds \<Gamma>\<cdot>ae) (thunks \<Gamma>)"
      apply (rule substitute_cong_T)
      using const_on3
      by (auto dest: subsetD[OF thunks_domA])
    also have "substitute (FBinds \<Delta>\<cdot>(Aheap \<Delta> e\<cdot>a)) (thunks (\<Delta> @ \<Gamma>)) = substitute (FBinds \<Delta>\<cdot>(Aheap \<Delta> e\<cdot>a)) (thunks \<Delta>)"
      apply (rule substitute_cong_T)
      using const_on4
      by (auto dest: subsetD[OF thunks_domA])
    also have "substitute (FBinds \<Delta>\<cdot>(Aheap \<Delta> e\<cdot>a)) (thunks \<Delta>) (Texp e\<cdot>a \<otimes>\<otimes> Fstack as S) = substitute (FBinds \<Delta>\<cdot>(Aheap \<Delta> e\<cdot>a)) (thunks \<Delta>) (Texp e\<cdot>a) \<otimes>\<otimes> Fstack as S"
      by (rule substitute_only_empty_both[OF const_on2])
    also note calculation
    }
    note eq_imp_below[OF this]
    also
    note env_restr_split[where S = "domA \<Delta>"]
    also
    have "pathsCard (paths (substitute (FBinds \<Gamma>\<cdot>ae) (thunks \<Gamma>) (substitute (FBinds \<Delta>\<cdot>(Aheap \<Delta> e\<cdot>a)) (thunks \<Delta>) (Texp e\<cdot>a) \<otimes>\<otimes> Fstack as S))) f|` domA \<Delta> 
        = pathsCard (paths (ttree_restr (domA \<Delta>) (substitute (FBinds \<Delta>\<cdot>(Aheap \<Delta> e\<cdot>a)) (thunks \<Delta>) (Texp e\<cdot>a))))"
          by (simp add: filter_paths_conv_free_restr ttree_restr_both ttree_rest_substitute[OF disj1]  ttree_restr_is_empty[OF disj2])
    also
    have "ttree_restr (domA \<Delta>) (substitute (FBinds \<Delta>\<cdot>(Aheap \<Delta> e\<cdot>a)) (thunks \<Delta>) (Texp e\<cdot>a)) \<sqsubseteq> Theap \<Delta> e\<cdot>a"  by (rule Theap_substitute)
    also
    have "pathsCard (paths (substitute (FBinds \<Gamma>\<cdot>ae) (thunks \<Gamma>) (substitute (FBinds \<Delta>\<cdot>(Aheap \<Delta> e\<cdot>a)) (thunks \<Delta>) (Texp e\<cdot>a) \<otimes>\<otimes> Fstack as S))) f|` (- domA \<Delta>) =
          pathsCard (paths (substitute (FBinds \<Gamma>\<cdot>ae) (thunks \<Gamma>) (ttree_restr (- domA \<Delta>) (substitute (FBinds \<Delta>\<cdot>(Aheap \<Delta> e\<cdot>a)) (thunks \<Delta>) (Texp e\<cdot>a)) \<otimes>\<otimes> Fstack as S)))"
          by (simp add: filter_paths_conv_free_restr2 ttree_rest_substitute2[OF disj1' const_on3] ttree_restr_both  ttree_restr_noop[OF disj2'])
    also have "ttree_restr (- domA \<Delta>) (substitute (FBinds \<Delta>\<cdot>(Aheap \<Delta> e\<cdot>a))  (thunks \<Delta>)  (Texp e\<cdot>a)) \<sqsubseteq> Texp (Terms.Let \<Delta> e)\<cdot>a" by (rule Texp_Let)
    finally
    show "prognosis (Aheap \<Delta> e\<cdot>a \<squnion> ae) as a (\<Delta> @ \<Gamma>, e, S) \<sqsubseteq> cHeap \<Delta> e\<cdot>a \<squnion> prognosis ae as a (\<Gamma>, Terms.Let \<Delta> e, S)"
      by (simp add: cHeap_def del: fun_meet_simp) 
  qed

  sublocale CardinalityPrognosisSafe prognosis cHeap Aheap Aexp ..
end


end
