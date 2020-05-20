theory CoCallFix
imports CoCallAnalysisSig CoCallAnalysisBinds ArityAnalysisSig "Launchbury.Env-Nominal"  ArityAnalysisFix
begin


locale CoCallArityAnalysis =
  fixes cccExp :: "exp \<Rightarrow> (Arity \<rightarrow> AEnv \<times> CoCalls)"
begin

definition Aexp :: "exp \<Rightarrow> (Arity \<rightarrow> AEnv)"
  where "Aexp e = (\<Lambda> a. fst (cccExp e \<cdot> a))"

sublocale ArityAnalysis Aexp.

abbreviation Aexp_syn' ("\<A>\<^bsub>_\<^esub>") where "\<A>\<^bsub>a\<^esub> \<equiv> (\<lambda>e. Aexp e\<cdot>a)"
abbreviation Aexp_bot_syn' ("\<A>\<^sup>\<bottom>\<^bsub>_\<^esub>") where "\<A>\<^sup>\<bottom>\<^bsub>a\<^esub> \<equiv> (\<lambda>e. fup\<cdot>(Aexp e)\<cdot>a)"

lemma Aexp_eq:
  "\<A>\<^bsub>a\<^esub> e = fst (cccExp e \<cdot> a)"
  unfolding Aexp_def by (rule beta_cfun) (intro cont2cont)

lemma fup_Aexp_eq:
  "fup\<cdot>(Aexp e)\<cdot>a = fst (fup\<cdot>(cccExp e)\<cdot>a)"
  by (cases a)(simp_all add: Aexp_eq)


definition CCexp :: "exp \<Rightarrow> (Arity \<rightarrow> CoCalls)" where "CCexp \<Gamma> = (\<Lambda> a. snd (cccExp \<Gamma>\<cdot>a))"
lemma CCexp_eq:
  "CCexp e\<cdot>a = snd (cccExp e \<cdot> a)"
  unfolding CCexp_def by (rule beta_cfun) (intro cont2cont)

lemma fup_CCexp_eq:
  "fup\<cdot>(CCexp e)\<cdot>a = snd (fup\<cdot>(cccExp e)\<cdot>a)"
  by (cases a)(simp_all add: CCexp_eq)

sublocale CoCallAnalysis CCexp.

definition CCfix :: "heap \<Rightarrow> (AEnv \<times> CoCalls) \<rightarrow> CoCalls"
  where "CCfix \<Gamma> = (\<Lambda> aeG. (\<mu> G'. ccBindsExtra \<Gamma>\<cdot>(fst aeG , G') \<squnion> snd aeG))"

lemma CCfix_eq:
  "CCfix \<Gamma>\<cdot>(ae,G) = (\<mu> G'. ccBindsExtra \<Gamma>\<cdot>(ae, G') \<squnion> G)"
  unfolding CCfix_def
  by simp

lemma CCfix_unroll: "CCfix \<Gamma>\<cdot>(ae,G) = ccBindsExtra \<Gamma>\<cdot>(ae, CCfix \<Gamma>\<cdot>(ae,G)) \<squnion> G"
  unfolding  CCfix_eq
  apply (subst fix_eq)
  apply simp
  done

lemma fup_ccExp_restr_subst': 
  assumes "\<And> a. cc_restr S (CCexp e[x::=y]\<cdot>a) = cc_restr S (CCexp e\<cdot>a)"
  shows "cc_restr S (fup\<cdot>(CCexp e[x::=y])\<cdot>a) = cc_restr S (fup\<cdot>(CCexp e)\<cdot>a)"
  using assms
  by (cases a) (auto simp del: cc_restr_cc_restr simp add: cc_restr_cc_restr[symmetric])

lemma ccBindsExtra_restr_subst': 
  assumes "\<And> x' e a. (x',e) \<in> set \<Gamma> \<Longrightarrow> cc_restr S (CCexp e[x::=y]\<cdot>a) = cc_restr S (CCexp e\<cdot>a)"
  assumes "x \<notin> S"
  assumes "y \<notin> S"
  assumes "domA \<Gamma> \<subseteq> S"
  shows  "cc_restr S (ccBindsExtra  \<Gamma>[x::h=y]\<cdot>(ae, G)) 
       = cc_restr S (ccBindsExtra  \<Gamma>\<cdot>(ae f|` S , cc_restr S G))"
  apply (simp add: ccBindsExtra_simp ccBinds_eq ccBind_eq Int_absorb2[OF assms(4)] fv_subst_int[OF assms(3,2)])
  apply (intro arg_cong2[where f = "(\<squnion>)"] refl  arg_cong[OF mapCollect_cong])
  apply (subgoal_tac "k \<in> S")
  apply (auto intro: fup_ccExp_restr_subst'[OF assms(1)[OF map_of_SomeD]] simp add: fv_subst_int[OF assms(3,2)]   fv_subst_int2[OF assms(3,2)] ccSquare_def)[1]
  apply (metis assms(4) contra_subsetD domI dom_map_of_conv_domA)
  apply (subgoal_tac "k \<in> S")
  apply (auto intro: fup_ccExp_restr_subst'[OF assms(1)[OF map_of_SomeD]]
              simp add: fv_subst_int[OF assms(3,2)]   fv_subst_int2[OF assms(3,2)] ccSquare_def cc_restr_twist[where S = S] simp del: cc_restr_cc_restr)[1]
  apply (subst fup_ccExp_restr_subst'[OF assms(1)[OF map_of_SomeD]], assumption)
  apply (simp add: fv_subst_int[OF assms(3,2)]   fv_subst_int2[OF assms(3,2)] )
  apply (subst fup_ccExp_restr_subst'[OF assms(1)[OF map_of_SomeD]], assumption)
  apply (simp add: fv_subst_int[OF assms(3,2)]   fv_subst_int2[OF assms(3,2)] )
  apply (metis assms(4) contra_subsetD domI dom_map_of_conv_domA)
  done

lemma ccBindsExtra_restr:
  assumes "domA \<Gamma> \<subseteq> S"
  shows "cc_restr S (ccBindsExtra \<Gamma>\<cdot>(ae, G)) = cc_restr S (ccBindsExtra \<Gamma>\<cdot>(ae f|` S, cc_restr S G))"
  using assms
  apply (simp add: ccBindsExtra_simp ccBinds_eq ccBind_eq Int_absorb2)
  apply (intro arg_cong2[where f = "(\<squnion>)"] refl arg_cong[OF mapCollect_cong])
  apply (subgoal_tac "k \<in> S")
  apply simp
  apply (metis contra_subsetD domI dom_map_of_conv_domA)
  apply (subgoal_tac "k \<in> S")
  apply simp
  apply (metis contra_subsetD domI dom_map_of_conv_domA)
  done

lemma CCfix_restr:
  assumes "domA \<Gamma> \<subseteq> S"
  shows "cc_restr S (CCfix \<Gamma>\<cdot>(ae, G)) = cc_restr S (CCfix \<Gamma>\<cdot>(ae f|` S, cc_restr S G))"
  unfolding CCfix_def
  apply simp
  apply (rule parallel_fix_ind[where P = "\<lambda> x y . cc_restr S x = cc_restr S y"])
  apply simp
  apply rule
  apply simp
  apply (subst (1 2) ccBindsExtra_restr[OF assms])
  apply (auto)
  done

lemma ccField_CCfix:
  shows "ccField (CCfix \<Gamma>\<cdot>(ae, G)) \<subseteq> fv \<Gamma> \<union> ccField G"
  unfolding CCfix_def
  apply simp
  apply (rule fix_ind[where P = "\<lambda> x . ccField x \<subseteq> fv \<Gamma> \<union> ccField G"])
  apply (auto dest!: subsetD[OF ccField_ccBindsExtra])
  done


lemma CCfix_restr_subst':
  assumes "\<And> x' e a. (x',e) \<in> set \<Gamma> \<Longrightarrow> cc_restr S (CCexp e[x::=y]\<cdot>a) = cc_restr S (CCexp e\<cdot>a)"
  assumes "x \<notin> S"
  assumes "y \<notin> S"
  assumes "domA \<Gamma> \<subseteq> S"
  shows "cc_restr S (CCfix \<Gamma>[x::h=y]\<cdot>(ae, G)) = cc_restr S (CCfix \<Gamma>\<cdot>(ae f|` S, cc_restr S G))"
  unfolding CCfix_def
  apply simp
  apply (rule parallel_fix_ind[where P = "\<lambda> x y . cc_restr S x = cc_restr S y"])
  apply simp
  apply rule
  apply simp
  apply (subst  ccBindsExtra_restr_subst'[OF assms], assumption)
  apply (subst ccBindsExtra_restr[OF assms(4)]) back 
  apply (auto)
  done


end

lemma Aexp_eqvt[eqvt]:  "\<pi> \<bullet> (CoCallArityAnalysis.Aexp cccExp e) = CoCallArityAnalysis.Aexp (\<pi> \<bullet> cccExp) (\<pi> \<bullet> e)"
  apply (rule cfun_eqvtI) unfolding CoCallArityAnalysis.Aexp_eq by perm_simp rule

lemma CCexp_eqvt[eqvt]:  "\<pi> \<bullet> (CoCallArityAnalysis.CCexp cccExp e) = CoCallArityAnalysis.CCexp (\<pi> \<bullet> cccExp) (\<pi> \<bullet> e)"
  apply (rule cfun_eqvtI) unfolding CoCallArityAnalysis.CCexp_eq by perm_simp rule

lemma CCfix_eqvt[eqvt]: "\<pi> \<bullet> (CoCallArityAnalysis.CCfix cccExp \<Gamma>) = CoCallArityAnalysis.CCfix (\<pi> \<bullet> cccExp) (\<pi> \<bullet> \<Gamma>)"
  unfolding CoCallArityAnalysis.CCfix_def by perm_simp (simp_all add: Abs_cfun_eqvt)

lemma ccFix_cong[fundef_cong]:
  "\<lbrakk> (\<And> e. e \<in> snd ` set heap2 \<Longrightarrow> cccexp1 e = cccexp2 e); heap1 = heap2 \<rbrakk>
      \<Longrightarrow> CoCallArityAnalysis.CCfix cccexp1 heap1 = CoCallArityAnalysis.CCfix cccexp2 heap2"
   unfolding CoCallArityAnalysis.CCfix_def
   apply (rule arg_cong) back
   apply (rule ccBindsExtra_cong)
   apply (auto simp add: CoCallArityAnalysis.CCexp_def)
   done


context CoCallArityAnalysis
begin
definition cccFix ::  "heap \<Rightarrow> ((AEnv \<times> CoCalls) \<rightarrow> (AEnv \<times> CoCalls))"
  where "cccFix \<Gamma> = (\<Lambda> i. (Afix \<Gamma>\<cdot>(fst i \<squnion> (\<lambda>_.up\<cdot>0) f|` thunks \<Gamma>), CCfix \<Gamma>\<cdot>(Afix \<Gamma>\<cdot>(fst i  \<squnion> (\<lambda>_.up\<cdot>0) f|` (thunks \<Gamma>)), snd i)))"

lemma cccFix_eq:
  "cccFix \<Gamma>\<cdot>i = (Afix \<Gamma>\<cdot>(fst i \<squnion> (\<lambda>_.up\<cdot>0) f|` thunks \<Gamma>), CCfix \<Gamma>\<cdot>(Afix \<Gamma>\<cdot>(fst i  \<squnion> (\<lambda>_.up\<cdot>0) f|` (thunks \<Gamma>)), snd i))"
  unfolding cccFix_def
  by (rule beta_cfun)(intro cont2cont)
end

lemma cccFix_eqvt[eqvt]: "\<pi> \<bullet> (CoCallArityAnalysis.cccFix cccExp \<Gamma>) = CoCallArityAnalysis.cccFix  (\<pi> \<bullet> cccExp) (\<pi> \<bullet> \<Gamma>)"
  apply (rule cfun_eqvtI) unfolding CoCallArityAnalysis.cccFix_eq by perm_simp rule

lemma cccFix_cong[fundef_cong]:
  "\<lbrakk> (\<And> e. e \<in> snd ` set heap2 \<Longrightarrow> cccexp1 e = cccexp2 e); heap1 = heap2 \<rbrakk>
      \<Longrightarrow> CoCallArityAnalysis.cccFix cccexp1 heap1 = CoCallArityAnalysis.cccFix cccexp2 heap2"
   unfolding CoCallArityAnalysis.cccFix_def
   apply (rule cfun_eqI)
   apply auto
   apply (rule arg_cong[OF Afix_cong], auto simp add: CoCallArityAnalysis.Aexp_def)[1]
   apply (rule arg_cong2[OF ccFix_cong Afix_cong ])
   apply (auto simp add: CoCallArityAnalysis.Aexp_def)
   done


subsubsection \<open>The non-recursive case\<close>

definition ABind_nonrec :: "var \<Rightarrow> exp \<Rightarrow> AEnv \<times> CoCalls \<rightarrow> Arity\<^sub>\<bottom>"
where
  "ABind_nonrec x e = (\<Lambda> i. (if isVal e \<or> x--x\<notin>(snd i) then fst i x else up\<cdot>0))"

lemma ABind_nonrec_eq:
  "ABind_nonrec x e\<cdot>(ae,G) = (if isVal e \<or> x--x\<notin>G then ae x else up\<cdot>0)"
  unfolding ABind_nonrec_def
  apply (subst beta_cfun)
  apply (rule cont_if_else_above)
  apply auto
  by (metis in_join join_self_below(4))

lemma ABind_nonrec_eqvt[eqvt]: "\<pi> \<bullet> (ABind_nonrec x e) = ABind_nonrec (\<pi> \<bullet> x) (\<pi> \<bullet> e)"
  apply (rule cfun_eqvtI)
  apply (case_tac xa, simp)
  unfolding ABind_nonrec_eq
  by perm_simp rule

lemma ABind_nonrec_above_arg:
  "ae x \<sqsubseteq> ABind_nonrec x e \<cdot> (ae, G)"
unfolding ABind_nonrec_eq by auto

definition Aheap_nonrec where
  "Aheap_nonrec x e = (\<Lambda> i. esing x\<cdot>(ABind_nonrec x e\<cdot>i))"

lemma Aheap_nonrec_simp:
  "Aheap_nonrec x e\<cdot>i = esing x\<cdot>(ABind_nonrec x e\<cdot>i)"
  unfolding Aheap_nonrec_def by simp

lemma Aheap_nonrec_lookup[simp]:
  "(Aheap_nonrec x e\<cdot>i) x = ABind_nonrec x e\<cdot>i"
  unfolding Aheap_nonrec_simp by simp

lemma Aheap_nonrec_eqvt'[eqvt]:
  "\<pi> \<bullet> (Aheap_nonrec x e) = Aheap_nonrec (\<pi> \<bullet> x) (\<pi> \<bullet> e)"
  apply (rule cfun_eqvtI)
  unfolding Aheap_nonrec_simp
  by (perm_simp, rule)


context CoCallArityAnalysis
begin

  definition Afix_nonrec
   where "Afix_nonrec x e = (\<Lambda> i. fup\<cdot>(Aexp e)\<cdot>(ABind_nonrec x e \<cdot> i) \<squnion> fst i)"

  lemma Afix_nonrec_eq[simp]:
    "Afix_nonrec x e \<cdot> i = fup\<cdot>(Aexp e)\<cdot>(ABind_nonrec x e \<cdot> i) \<squnion> fst i"
    unfolding Afix_nonrec_def
    by (rule beta_cfun) simp

  definition CCfix_nonrec
   where "CCfix_nonrec x e = (\<Lambda> i. ccBind x e \<cdot> (Aheap_nonrec x e\<cdot>i, snd i)  \<squnion> ccProd (fv e) (ccNeighbors x (snd i) - (if isVal e then {} else {x})) \<squnion> snd i)"

  lemma CCfix_nonrec_eq[simp]:
    "CCfix_nonrec x e \<cdot> i = ccBind x e\<cdot>(Aheap_nonrec x e\<cdot>i, snd i)  \<squnion> ccProd (fv e) (ccNeighbors x (snd i) - (if isVal e then {} else {x})) \<squnion> snd i"
    unfolding CCfix_nonrec_def
    by (rule beta_cfun) (intro cont2cont)

  definition cccFix_nonrec ::  "var \<Rightarrow> exp \<Rightarrow> ((AEnv \<times> CoCalls) \<rightarrow> (AEnv \<times> CoCalls))"
    where "cccFix_nonrec x e = (\<Lambda> i. (Afix_nonrec x e \<cdot>i , CCfix_nonrec x e \<cdot>i))"

  lemma cccFix_nonrec_eq[simp]:
    "cccFix_nonrec x e\<cdot>i = (Afix_nonrec x e \<cdot>i , CCfix_nonrec x e \<cdot>i)"
    unfolding cccFix_nonrec_def
    by (rule beta_cfun) (intro cont2cont)

end


lemma AFix_nonrec_eqvt[eqvt]: "\<pi> \<bullet> (CoCallArityAnalysis.Afix_nonrec cccExp x e) = CoCallArityAnalysis.Afix_nonrec (\<pi> \<bullet> cccExp) (\<pi> \<bullet> x) (\<pi> \<bullet> e)"
  apply (rule cfun_eqvtI)
  unfolding CoCallArityAnalysis.Afix_nonrec_eq
  by perm_simp rule


lemma CCFix_nonrec_eqvt[eqvt]: "\<pi> \<bullet> (CoCallArityAnalysis.CCfix_nonrec cccExp x e) = CoCallArityAnalysis.CCfix_nonrec (\<pi> \<bullet> cccExp) (\<pi> \<bullet> x) (\<pi> \<bullet> e)"
  apply (rule cfun_eqvtI)
  unfolding CoCallArityAnalysis.CCfix_nonrec_eq
  by perm_simp rule

lemma cccFix_nonrec_eqvt[eqvt]: "\<pi> \<bullet> (CoCallArityAnalysis.cccFix_nonrec cccExp x e) = CoCallArityAnalysis.cccFix_nonrec (\<pi> \<bullet> cccExp) (\<pi> \<bullet> x) (\<pi> \<bullet> e)"
  apply (rule cfun_eqvtI)
  unfolding CoCallArityAnalysis.cccFix_nonrec_eq
  by perm_simp rule

subsubsection \<open>Combining the cases\<close>

context CoCallArityAnalysis
begin
  definition cccFix_choose ::  "heap \<Rightarrow> ((AEnv \<times> CoCalls) \<rightarrow> (AEnv \<times> CoCalls))"
    where "cccFix_choose \<Gamma> = (if nonrec \<Gamma> then case_prod cccFix_nonrec (hd \<Gamma>) else cccFix \<Gamma>)"

  lemma cccFix_choose_simp1[simp]:
    "\<not> nonrec \<Gamma> \<Longrightarrow> cccFix_choose \<Gamma> = cccFix \<Gamma>"
  unfolding cccFix_choose_def by simp

  lemma cccFix_choose_simp2[simp]:
    "x \<notin> fv e \<Longrightarrow> cccFix_choose [(x,e)] = cccFix_nonrec x e"
  unfolding cccFix_choose_def nonrec_def by auto

end

lemma cccFix_choose_eqvt[eqvt]: "\<pi> \<bullet> (CoCallArityAnalysis.cccFix_choose cccExp \<Gamma>) = CoCallArityAnalysis.cccFix_choose (\<pi> \<bullet> cccExp) (\<pi> \<bullet> \<Gamma>)"
  unfolding CoCallArityAnalysis.cccFix_choose_def 
  apply (cases nonrec \<pi>  rule: eqvt_cases[where x = \<Gamma>])
  apply (perm_simp, rule)
  apply simp
  apply (erule nonrecE)
  apply (simp )

  apply simp
  done

lemma cccFix_nonrec_cong[fundef_cong]:
  "cccexp1 e = cccexp2 e  \<Longrightarrow> CoCallArityAnalysis.cccFix_nonrec cccexp1 x e = CoCallArityAnalysis.cccFix_nonrec cccexp2 x e"
   apply (rule cfun_eqI)
   unfolding CoCallArityAnalysis.cccFix_nonrec_eq
   unfolding CoCallArityAnalysis.Afix_nonrec_eq
   unfolding CoCallArityAnalysis.CCfix_nonrec_eq
   unfolding CoCallArityAnalysis.fup_Aexp_eq
   apply (simp only: )
   apply (rule arg_cong[OF ccBind_cong])
   apply simp
   unfolding CoCallArityAnalysis.CCexp_def
   apply simp
   done

lemma cccFix_choose_cong[fundef_cong]:
  "\<lbrakk> (\<And> e. e \<in> snd ` set heap2 \<Longrightarrow> cccexp1 e = cccexp2 e); heap1 = heap2 \<rbrakk>
      \<Longrightarrow> CoCallArityAnalysis.cccFix_choose cccexp1 heap1 = CoCallArityAnalysis.cccFix_choose cccexp2 heap2"
   unfolding CoCallArityAnalysis.cccFix_choose_def
   apply (rule cfun_eqI)
   apply (auto elim!: nonrecE)
   apply (rule arg_cong[OF cccFix_nonrec_cong], auto)
   apply (rule arg_cong[OF cccFix_cong], auto)[1]
   done

end
