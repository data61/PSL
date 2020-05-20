theory FmapUtils
  imports "HOL-Library.Finite_Map" FactoredSystemLib
begin

\<comment> \<open>TODO
  A lemma 'fmrestrict\_set\_twice\_eq'
    'fmrestrict\_set ?vs (fmrestrict\_set ?vs ?f) = fmrestrict\_set ?vs ?f'
to replace the recurring proofs steps using 'by (simp add: fmfilter\_alt\_defs(4))' would make sense.\<close>


\<comment> \<open>NOTE hide the '++' operator from 'Map' to prevent warnings.\<close>
hide_const (open) Map.map_add
no_notation Map.map_add (infixl "++" 100)

\<comment> \<open>TODO more explicit proof.\<close>
lemma IN_FDOM_DRESTRICT_DIFF:
  fixes vs v f
  assumes "\<not>(v \<in> vs)" "fmdom' f \<subseteq> fdom" "v \<in> fmdom' f"
  shows "v \<in> fmdom' (fmrestrict_set (fdom - vs) f)"
  using assms
  by (metis DiffI Int_def Int_iff Set.filter_def fmdom'_filter fmfilter_alt_defs(4) inf.order_iff)

lemma disj_dom_drest_fupdate_eq: "
  disjnt (fmdom' x) vs \<Longrightarrow> (fmrestrict_set vs s = fmrestrict_set vs (x ++ s))
"
proof -
  fix vs s x
  assume P: "disjnt (fmdom' x) vs"
  moreover have 1: "\<forall>x''. (x'' \<in> vs) \<longrightarrow> (fmlookup (x ++ s) x'' = fmlookup s  x'')"
    by (metis calculation disjnt_iff fmap_add_ltr_def fmdom'_notD fmdom_notI fmlookup_add)
  moreover
  {
    fix x''
    have "fmlookup (fmrestrict_set vs s) x'' = fmlookup (fmrestrict_set vs (x ++ s)) x''"
      apply(cases "x'' \<notin> fmdom' x")
       apply(cases "x'' \<notin> vs")
        apply(auto simp add: "1")
      done
  }
  ultimately show "(fmrestrict_set vs s = fmrestrict_set vs (x ++ s))"
    using fmap_ext by blast
qed

\<comment> \<open>TODO refactor into 'FmapUtils.thy'.\<close>
lemma graph_plan_card_state_set:
  fixes PROB vs
  assumes "finite vs"
  shows "card (fmdom' (fmrestrict_set vs s)) \<le> card vs"
proof -
  let ?vs' = "fmdom' (fmrestrict_set vs s)"
  have "?vs' \<subseteq> vs"
    using fmdom'_restrict_set
    by metis
  moreover have "card ?vs' \<le> card vs"
    using assms calculation card_mono
    by blast
  ultimately show ?thesis by blast
qed

lemma exec_drest_5:
  fixes x vs
  assumes "fmdom' x \<subseteq> vs"
  shows "(fmrestrict_set vs x = x)"
proof -
  \<comment> \<open>TODO refactor and make into ISAR proof.\<close>
  {
    fix v
    have "fmlookup (fmrestrict_set vs x) v = fmlookup x v"
      apply(cases "v \<in> fmdom' x")
      subgoal using assms by auto
      subgoal by (simp add: fmdom'_notD)
      done
    then have "fmlookup (fmrestrict_set vs x) v = fmlookup x v"
      by fast
  }
  moreover have "fmlookup (fmrestrict_set vs x) = fmlookup x"
    using calculation fmap_ext
    by auto
  ultimately show ?thesis
    using fmlookup_inject
    by blast
qed

lemma graph_plan_lemma_5:
  fixes s s' vs
  assumes "(fmrestrict_set (fmdom' s - vs) s = fmrestrict_set (fmdom' s' - vs) s')"
    "(fmrestrict_set vs s = fmrestrict_set vs s')"
  shows "(s = s')"
proof -
  have "\<forall>x. fmlookup s x = fmlookup s' x"
    using assms(1, 2) fmdom'_notD fminusI fmlookup_restrict_set Diff_iff
    by metis
  then show ?thesis using fmap_ext
    by blast
qed

lemma drest_smap_drest_smap_drest:
  fixes x s vs
  shows "fmrestrict_set vs x \<subseteq>\<^sub>f s \<longleftrightarrow> fmrestrict_set vs x \<subseteq>\<^sub>f fmrestrict_set vs s"
proof -
  \<comment> \<open>TODO this could be refactored into standalone lemma since it's very common in proofs.\<close>
  have 1: "fmlookup (fmrestrict_set vs s) \<subseteq>\<^sub>m fmlookup s"
    by (metis fmdom'.rep_eq fmdom'_notI fmlookup_restrict_set map_le_def)
  moreover
  {
    assume P1: "fmrestrict_set vs x \<subseteq>\<^sub>f s"
    moreover have 2: "fmlookup (fmrestrict_set vs x) \<subseteq>\<^sub>m fmlookup s"
      using P1 fmsubset.rep_eq by blast
    {
      fix v
      assume "v \<in> fmdom' (fmrestrict_set vs x)"
      then have "fmlookup (fmrestrict_set vs x) v = fmlookup (fmrestrict_set vs s) v"
        by (metis (full_types) "2" domIff fmdom'_notI fmlookup_restrict_set map_le_def)
    }
    ultimately have "fmrestrict_set vs x \<subseteq>\<^sub>f fmrestrict_set vs s"
      unfolding fmsubset.rep_eq
      by (simp add: map_le_def)
  }
  moreover
  {
    assume P2: "fmrestrict_set vs x \<subseteq>\<^sub>f fmrestrict_set vs s"
    moreover have "fmrestrict_set vs s \<subseteq>\<^sub>f s"
      using 1 fmsubset.rep_eq
      by blast
    ultimately have "fmrestrict_set vs x \<subseteq>\<^sub>f s"
      using fmsubset.rep_eq map_le_trans
      by blast
  }
  ultimately show ?thesis by blast
qed

lemma sat_precond_as_proj_1:
  fixes s s' vs x
  assumes "fmrestrict_set vs s = fmrestrict_set vs s'"
  shows "fmrestrict_set vs x \<subseteq>\<^sub>f s \<longleftrightarrow> fmrestrict_set vs x \<subseteq>\<^sub>f s'"
  using assms drest_smap_drest_smap_drest
  by metis

lemma sat_precond_as_proj_4:
  fixes fm1 fm2 vs
  assumes "fm2 \<subseteq>\<^sub>f fm1"
  shows "(fmrestrict_set vs fm2 \<subseteq>\<^sub>f fm1)"
  using assms fmpred_restrict_set fmsubset_alt_def
  by metis

lemma sublist_as_proj_eq_as_1:
  fixes x s vs
  assumes "(x \<subseteq>\<^sub>f fmrestrict_set vs s)"
  shows "(x \<subseteq>\<^sub>f s)"
  using assms
  by (meson fmsubset.rep_eq fmsubset_alt_def fmsubset_pred drest_smap_drest_smap_drest map_le_refl)

lemma limited_dom_neq_restricted_neq:
  assumes "fmdom' f1 \<subseteq> vs" "f1 ++ f2 \<noteq> f2"
  shows "fmrestrict_set vs (f1 ++ f2) \<noteq> fmrestrict_set vs f2"
proof -
  {
    assume C: "fmrestrict_set vs (f1 ++ f2) = fmrestrict_set vs f2"
    then have "\<forall>x \<in> fmdom' (fmrestrict_set vs (f1 ++ f2)).
      fmlookup (fmrestrict_set vs (f1 ++ f2)) x
      = fmlookup (fmrestrict_set vs f2) x"
      by simp
    obtain v where a: "v \<in> fmdom' f1" "fmlookup (f1 ++ f2) v \<noteq> fmlookup f2 v"
      using assms(2)
      by (metis fmap_add_ltr_def fmap_ext fmdom'_notD fmdom_notI fmlookup_add)
    then have b: "v \<in> vs"
      using assms(1)
      by blast
    moreover {
      have "fmdom' (fmrestrict_set vs (f1 ++ f2)) = vs \<inter> fmdom' (f1 ++ f2)"
        by (simp add: fmdom'_alt_def fmfilter_alt_defs(4))
      then have "v \<in> fmdom' (fmrestrict_set vs (f1 ++ f2))"
        using C a b
        by fastforce
    }
    then have False
      by (metis C a(2) calculation fmlookup_restrict_set)
  }
  then show ?thesis
    by auto
qed

lemma fmlookup_fmrestrict_set_dom: "\<And>vs s. dom (fmlookup (fmrestrict_set vs s)) = vs \<inter> (fmdom' s)"
by (auto simp add: fmdom'_restrict_set_precise)

end