(* Author: Alexander Maletzky *)

theory Groebner_PM
  imports Polynomials.MPoly_PM Reduced_GB
begin

text \<open>We prove results that hold specifically for Gr\"obner bases in polynomial rings, where the
  polynomials really have @{emph \<open>indeterminates\<close>}.\<close>

context pm_powerprod
begin

lemmas finite_reduced_GB_Polys =
  punit.finite_reduced_GB_dgrad_p_set[simplified, OF dickson_grading_varnum, where m=0, simplified dgrad_p_set_varnum]
lemmas reduced_GB_is_reduced_GB_Polys =
  punit.reduced_GB_is_reduced_GB_dgrad_p_set[simplified, OF dickson_grading_varnum, where m=0, simplified dgrad_p_set_varnum]
lemmas reduced_GB_is_GB_Polys =
  punit.reduced_GB_is_GB_dgrad_p_set[simplified, OF dickson_grading_varnum, where m=0, simplified dgrad_p_set_varnum]
lemmas reduced_GB_is_auto_reduced_Polys =
  punit.reduced_GB_is_auto_reduced_dgrad_p_set[simplified, OF dickson_grading_varnum, where m=0, simplified dgrad_p_set_varnum]
lemmas reduced_GB_is_monic_set_Polys =
  punit.reduced_GB_is_monic_set_dgrad_p_set[simplified, OF dickson_grading_varnum, where m=0, simplified dgrad_p_set_varnum]
lemmas reduced_GB_nonzero_Polys =
  punit.reduced_GB_nonzero_dgrad_p_set[simplified, OF dickson_grading_varnum, where m=0, simplified dgrad_p_set_varnum]
lemmas reduced_GB_ideal_Polys =
  punit.reduced_GB_pmdl_dgrad_p_set[simplified, OF dickson_grading_varnum, where m=0, simplified dgrad_p_set_varnum]
lemmas reduced_GB_unique_Polys =
  punit.reduced_GB_unique_dgrad_p_set[simplified, OF dickson_grading_varnum, where m=0, simplified dgrad_p_set_varnum]
lemmas reduced_GB_Polys =
  punit.reduced_GB_dgrad_p_set[simplified, OF dickson_grading_varnum, where m=0, simplified dgrad_p_set_varnum]
lemmas ideal_eq_UNIV_iff_reduced_GB_eq_one_Polys =
  ideal_eq_UNIV_iff_reduced_GB_eq_one_dgrad_p_set[simplified, OF dickson_grading_varnum, where m=0, simplified dgrad_p_set_varnum]

subsection \<open>Univariate Polynomials\<close>

lemma (in -) adds_univariate_linear:
  assumes "finite X" and "card X \<le> 1" and "s \<in> .[X]" and "t \<in> .[X]"
  obtains "s adds t" | "t adds s"
proof (cases "s adds t")
  case True
  thus ?thesis ..
next
  case False
  then obtain x where 1: "lookup t x < lookup s x" by (auto simp: adds_poly_mapping le_fun_def not_le)
  hence "x \<in> keys s" by (simp add: in_keys_iff)
  also from assms(3) have "\<dots> \<subseteq> X" by (rule PPsD)
  finally have "x \<in> X" .
  have "t adds s" unfolding adds_poly_mapping le_fun_def
  proof
    fix y
    show "lookup t y \<le> lookup s y"
    proof (cases "y \<in> keys t")
      case True
      also from assms(4) have "keys t \<subseteq> X" by (rule PPsD)
      finally have "y \<in> X" .
      with assms(1, 2) \<open>x \<in> X\<close> have "x = y" by (simp add: card_le_Suc0_iff_eq)
      with 1 show ?thesis by simp
    next
      case False
      thus ?thesis by (simp add: in_keys_iff)
    qed
  qed
  thus ?thesis ..
qed

context
  fixes X :: "'x set"
  assumes fin_X: "finite X" and card_X: "card X \<le> 1"
begin

lemma ord_iff_adds_univariate:
  assumes "s \<in> .[X]" and "t \<in> .[X]"
  shows "s \<preceq> t \<longleftrightarrow> s adds t"
proof
  assume "s \<preceq> t"
  from fin_X card_X assms show "s adds t"
  proof (rule adds_univariate_linear)
    assume "t adds s"
    hence "t \<preceq> s" by (rule ord_adds)
    with \<open>s \<preceq> t\<close> have "s = t" by (rule ordered_powerprod_lin.antisym)
    thus ?thesis by simp
  qed
qed (rule ord_adds)

lemma adds_iff_deg_le_univariate:
  assumes "s \<in> .[X]" and "t \<in> .[X]"
  shows "s adds t \<longleftrightarrow> deg_pm s \<le> deg_pm t"
proof
  assume *: "deg_pm s \<le> deg_pm t"
  from fin_X card_X assms show "s adds t"
  proof (rule adds_univariate_linear)
    assume "t adds s"
    hence "t = s" using * by (rule adds_deg_pm_antisym)
    thus ?thesis by simp
  qed
qed (rule deg_pm_mono)

corollary ord_iff_deg_le_univariate: "s \<in> .[X] \<Longrightarrow> t \<in> .[X] \<Longrightarrow> s \<preceq> t \<longleftrightarrow> deg_pm s \<le> deg_pm t"
  by (simp only: ord_iff_adds_univariate adds_iff_deg_le_univariate)

lemma poly_deg_univariate:
  assumes "p \<in> P[X]"
  shows "poly_deg p = deg_pm (lpp p)"
proof (cases "p = 0")
  case True
  thus ?thesis by simp
next
  case False
  hence lp_in: "lpp p \<in> keys p" by (rule punit.lt_in_keys)
  also from assms have "\<dots> \<subseteq> .[X]" by (rule PolysD)
  finally have "lpp p \<in> .[X]" .
  show ?thesis
  proof (intro antisym poly_deg_leI)
    fix t
    assume "t \<in> keys p"
    hence "t \<preceq> lpp p" by (rule punit.lt_max_keys)
    moreover from \<open>t \<in> keys p\<close> \<open>keys p \<subseteq> .[X]\<close> have "t \<in> .[X]" ..
    ultimately show "deg_pm t \<le> deg_pm (lpp p)" using \<open>lpp p \<in> .[X]\<close>
      by (simp only: ord_iff_deg_le_univariate)
  next
    from lp_in show "deg_pm (lpp p) \<le> poly_deg p" by (rule poly_deg_max_keys)
  qed
qed

lemma reduced_GB_univariate_cases:
  assumes "F \<subseteq> P[X]"
  obtains g where "g \<in> P[X]" and "g \<noteq> 0" and "lcf g = 1" and "punit.reduced_GB F = {g}" |
    "punit.reduced_GB F = {}"
proof (cases "punit.reduced_GB F = {}")
  case True
  thus ?thesis ..
next
  case False
  let ?G = "punit.reduced_GB F"
  from fin_X assms have ar: "punit.is_auto_reduced ?G" and "0 \<notin> ?G" and "?G \<subseteq> P[X]"
    and m: "punit.is_monic_set ?G"
    by (rule reduced_GB_is_auto_reduced_Polys, rule reduced_GB_nonzero_Polys, rule reduced_GB_Polys,
        rule reduced_GB_is_monic_set_Polys)
  from False obtain g where "g \<in> ?G" by blast
  with \<open>0 \<notin> ?G\<close> \<open>?G \<subseteq> P[X]\<close> have "g \<noteq> 0" and "g \<in> P[X]" by blast+
  from this(1) have lp_g: "lpp g \<in> keys g" by (rule punit.lt_in_keys)
  also from \<open>g \<in> P[X]\<close> have "\<dots> \<subseteq> .[X]" by (rule PolysD)
  finally have "lpp g \<in> .[X]" .
  note \<open>g \<in> P[X]\<close> \<open>g \<noteq> 0\<close>
  moreover from m \<open>g \<in> ?G\<close> \<open>g \<noteq> 0\<close> have "lcf g = 1" by (rule punit.is_monic_setD)
  moreover have "?G = {g}"
  proof
    show "?G \<subseteq> {g}"
    proof
      fix g'
      assume "g' \<in> ?G"
      with \<open>0 \<notin> ?G\<close> \<open>?G \<subseteq> P[X]\<close> have "g' \<noteq> 0" and "g' \<in> P[X]" by blast+
      from this(1) have lp_g': "lpp g' \<in> keys g'" by (rule punit.lt_in_keys)
      also from \<open>g' \<in> P[X]\<close> have "\<dots> \<subseteq> .[X]" by (rule PolysD)
      finally have "lpp g' \<in> .[X]" .
      have "g' = g"
      proof (rule ccontr)
        assume "g' \<noteq> g"
        with \<open>g \<in> ?G\<close> \<open>g' \<in> ?G\<close> have g: "g \<in> ?G - {g'}" and g': "g' \<in> ?G - {g}" by blast+
        from fin_X card_X \<open>lpp g \<in> .[X]\<close> \<open>lpp g' \<in> .[X]\<close> show False
        proof (rule adds_univariate_linear)
          assume *: "lpp g adds lpp g'"
          from ar \<open>g' \<in> ?G\<close> have "\<not> punit.is_red (?G - {g'}) g'" by (rule punit.is_auto_reducedD)
          moreover from g \<open>g \<noteq> 0\<close> lp_g' * have "punit.is_red (?G - {g'}) g'"
            by (rule punit.is_red_addsI[simplified])
          ultimately show ?thesis ..
        next
          assume *: "lpp g' adds lpp g"
          from ar \<open>g \<in> ?G\<close> have "\<not> punit.is_red (?G - {g}) g" by (rule punit.is_auto_reducedD)
          moreover from g' \<open>g' \<noteq> 0\<close> lp_g * have "punit.is_red (?G - {g}) g"
            by (rule punit.is_red_addsI[simplified])
          ultimately show ?thesis ..
        qed
      qed
      thus "g' \<in> {g}" by simp
    qed
  next
    from \<open>g \<in> ?G\<close> show "{g} \<subseteq> ?G" by simp
  qed
  ultimately show ?thesis ..
qed

corollary deg_reduced_GB_univariate_le:
  assumes "F \<subseteq> P[X]" and "f \<in> ideal F" and "f \<noteq> 0" and "g \<in> punit.reduced_GB F"
  shows "poly_deg g \<le> poly_deg f"
  using assms(1)
proof (rule reduced_GB_univariate_cases)
  let ?G = "punit.reduced_GB F"
  fix g'
  assume "g' \<in> P[X]" and "g' \<noteq> 0" and G: "?G = {g'}"
  from fin_X assms(1) have gb: "punit.is_Groebner_basis ?G" and "ideal ?G = ideal F"
    and "?G \<subseteq> P[X]"
    by (rule reduced_GB_is_GB_Polys, rule reduced_GB_ideal_Polys, rule reduced_GB_Polys)
  from assms(2) this(2) have "f \<in> ideal ?G" by simp
  with gb obtain g'' where "g'' \<in> ?G" and "lpp g'' adds lpp f"
    using assms(3) by (rule punit.GB_adds_lt[simplified])
  with assms(4) have "lpp g adds lpp f" by (simp add: G)
  hence "deg_pm (lpp g) \<le> deg_pm (lpp f)" by (rule deg_pm_mono)
  moreover from assms(4) \<open>?G \<subseteq> P[X]\<close> have "g \<in> P[X]" ..
  ultimately have "poly_deg g \<le> deg_pm (lpp f)" by (simp only: poly_deg_univariate)
  also from punit.lt_in_keys have "\<dots> \<le> poly_deg f" by (rule poly_deg_max_keys) fact
  finally show ?thesis .
next
  assume "punit.reduced_GB F = {}"
  with assms(4) show ?thesis by simp
qed

end

subsection \<open>Homogeneity\<close>

lemma is_reduced_GB_homogeneous:
  assumes "\<And>f. f \<in> F \<Longrightarrow> homogeneous f" and "punit.is_reduced_GB G" and "ideal G = ideal F"
    and "g \<in> G"
  shows "homogeneous g"
proof (rule homogeneousI)
  fix s t
  have 1: "deg_pm u = deg_pm (lpp g)" if "u \<in> keys g" for u
  proof -
    from assms(4) have "g \<in> ideal G" by (rule ideal.span_base)
    hence "g \<in> ideal F" by (simp only: assms(3))
    from that have "u \<in> Keys (hom_components g)" by (simp only: Keys_hom_components)
    then obtain q where q: "q \<in> hom_components g" and "u \<in> keys q" by (rule in_KeysE)
    from assms(1) \<open>g \<in> ideal F\<close> q have "q \<in> ideal F" by (rule homogeneous_ideal')
    from assms(2) have "punit.is_Groebner_basis G" by (rule punit.reduced_GB_D1)
    moreover from \<open>q \<in> ideal F\<close> have "q \<in> ideal G" by (simp only: assms(3))
    moreover from q have "q \<noteq> 0" by (rule hom_components_nonzero)
    ultimately obtain g' where "g' \<in> G" and "g' \<noteq> 0" and adds: "lpp g' adds lpp q"
      by (rule punit.GB_adds_lt[simplified])
    from \<open>q \<noteq> 0\<close> have "lpp q \<in> keys q" by (rule punit.lt_in_keys)
    also from q have "\<dots> \<subseteq> Keys (hom_components g)" by (rule keys_subset_Keys)
    finally have "lpp q \<in> keys g" by (simp only: Keys_hom_components)
    with _ \<open>g' \<noteq> 0\<close> have red: "punit.is_red {g'} g"
      using adds by (rule punit.is_red_addsI[simplified]) simp
    from assms(2) have "punit.is_auto_reduced G" by (rule punit.reduced_GB_D2)
    hence "\<not> punit.is_red (G - {g}) g" using assms(4) by (rule punit.is_auto_reducedD)
    with red have "\<not> {g'} \<subseteq> G - {g}" using punit.is_red_subset by blast
    with \<open>g' \<in> G\<close> have "g' = g" by simp
    from \<open>lpp q \<in> keys g\<close> have "lpp q \<preceq> lpp g" by (rule punit.lt_max_keys)
    moreover from adds have "lpp g \<preceq> lpp q"
      unfolding \<open>g' = g\<close> by (rule punit.ord_adds_term[simplified])
    ultimately have eq: "lpp q = lpp g" by (rule ordered_powerprod_lin.antisym)
    from q have "homogeneous q" by (rule hom_components_homogeneous)
    hence "deg_pm u = deg_pm (lpp q)"
      using \<open>u \<in> keys q\<close> \<open>lpp q \<in> keys q\<close> by (rule homogeneousD)
    thus ?thesis by (simp only: eq)
  qed
  assume "s \<in> keys g"
  hence 2: "deg_pm s = deg_pm (lpp g)" by (rule 1)
  assume "t \<in> keys g"
  hence "deg_pm t = deg_pm (lpp g)" by (rule 1)
  with 2 show "deg_pm s = deg_pm t" by simp
qed

lemma lp_dehomogenize:
  assumes "is_hom_ord x" and "homogeneous p"
  shows "lpp (dehomogenize x p) = except (lpp p) {x}"
proof (cases "p = 0")
  case True
  thus ?thesis by simp
next
  case False
  hence "lpp p \<in> keys p" by (rule punit.lt_in_keys)
  with assms(2) have "except (lpp p) {x} \<in> keys (dehomogenize x p)"
    by (rule keys_dehomogenizeI)
  thus ?thesis
  proof (rule punit.lt_eqI_keys)
    fix t
    assume "t \<in> keys (dehomogenize x p)"
    then obtain s where "s \<in> keys p" and t: "t = except s {x}" by (rule keys_dehomogenizeE)
    from this(1) have "s \<preceq> lpp p" by (rule punit.lt_max_keys)
    moreover from assms(2) \<open>s \<in> keys p\<close> \<open>lpp p \<in> keys p\<close> have "deg_pm s = deg_pm (lpp p)"
      by (rule homogeneousD)
    ultimately show "t \<preceq> except (lpp p) {x}" using assms(1) by (simp add: t is_hom_ordD)
  qed
qed

lemma isGB_dehomogenize:
  assumes "is_hom_ord x" and "finite X" and "G \<subseteq> P[X]" and "punit.is_Groebner_basis G"
    and "\<And>g. g \<in> G \<Longrightarrow> homogeneous g"
  shows "punit.is_Groebner_basis (dehomogenize x ` G)"
  using dickson_grading_varnum
proof (rule punit.isGB_I_adds_lt[simplified])
  from assms(2) show "finite (X - {x})" by simp
next
  have "dehomogenize x ` G \<subseteq> P[X - {x}]"
  proof
    fix g
    assume "g \<in> dehomogenize x ` G"
    then obtain g' where "g' \<in> G" and g: "g = dehomogenize x g'" ..
    from this(1) assms(3) have "g' \<in> P[X]" ..
    hence "indets g' \<subseteq> X" by (rule PolysD)
    have "indets g \<subseteq> indets g' - {x}" by (simp only: g indets_dehomogenize)
    also from \<open>indets g' \<subseteq> X\<close> subset_refl have "\<dots> \<subseteq> X - {x}" by (rule Diff_mono)
    finally show "g \<in> P[X - {x}]" by (rule PolysI_alt)
  qed
  thus "dehomogenize x ` G \<subseteq> punit.dgrad_p_set (varnum (X - {x})) 0"
    by (simp only: dgrad_p_set_varnum)
next
  fix p
  assume "p \<in> ideal (dehomogenize x ` G)"
  then obtain G0 q where "G0 \<subseteq> dehomogenize x ` G" and "finite G0" and p: "p = (\<Sum>g\<in>G0. q g * g)"
    by (rule ideal.spanE)
  from this(1) obtain G' where "G' \<subseteq> G" and G0: "G0 = dehomogenize x ` G'"
    and inj: "inj_on (dehomogenize x) G'" by (rule subset_imageE_inj)
  define p' where "p' = (\<Sum>g\<in>G'. q (dehomogenize x g) * g)"
  have "p' \<in> ideal G'" unfolding p'_def by (rule ideal.sum_in_spanI)
  also from \<open>G' \<subseteq> G\<close> have "\<dots> \<subseteq> ideal G" by (rule ideal.span_mono)
  finally have "p' \<in> ideal G" .
  with assms(5) have "homogenize x p' \<in> ideal G" (is "?p \<in> _") by (rule homogeneous_ideal_homogenize)

  assume "p \<in> punit.dgrad_p_set (varnum (X - {x})) 0"
  hence "p \<in> P[X - {x}]" by (simp only: dgrad_p_set_varnum)
  hence "indets p \<subseteq> X - {x}" by (rule PolysD)
  hence "x \<notin> indets p" by blast
  have "p = dehomogenize x p" by (rule sym) (simp add: \<open>x \<notin> indets p\<close>)
  also from inj have "\<dots> = dehomogenize x (\<Sum>g\<in>G'. q (dehomogenize x g) * dehomogenize x g)"
    by (simp add: p G0 sum.reindex)
  also have "\<dots> = dehomogenize x ?p"
    by (simp add: dehomogenize_sum dehomogenize_times p'_def)
  finally have p: "p = dehomogenize x ?p" .
  moreover assume "p \<noteq> 0"
  ultimately have "?p \<noteq> 0" by (auto simp del: dehomogenize_homogenize)
  with assms(4) \<open>?p \<in> ideal G\<close> obtain g where "g \<in> G" and "g \<noteq> 0" and adds: "lpp g adds lpp ?p"
    by (rule punit.GB_adds_lt[simplified])
  from this(1) have "homogeneous g" by (rule assms(5))
  show "\<exists>g\<in>dehomogenize x ` G. g \<noteq> 0 \<and> lpp g adds lpp p"
  proof (intro bexI conjI notI)
    assume "dehomogenize x g = 0"
    hence "g = 0" using \<open>homogeneous g\<close> by (rule dehomogenize_zeroD)
    with \<open>g \<noteq> 0\<close> show False ..
  next
    from assms(1) \<open>homogeneous g\<close> have "lpp (dehomogenize x g) = except (lpp g) {x}"
      by (rule lp_dehomogenize)
    also from adds have "\<dots> adds except (lpp ?p) {x}"
      by (simp add: adds_poly_mapping le_fun_def lookup_except)
    also from assms(1) homogeneous_homogenize have "\<dots> = lpp (dehomogenize x ?p)"
      by (rule lp_dehomogenize[symmetric])
    finally show "lpp (dehomogenize x g) adds lpp p" by (simp only: p)
  next
    from \<open>g \<in> G\<close> show "dehomogenize x g \<in> dehomogenize x ` G" by (rule imageI)
  qed
qed

end (* pm_powerprod *)

context extended_ord_pm_powerprod
begin

lemma extended_ord_lp:
  assumes "None \<notin> indets p"
  shows "restrict_indets_pp (extended_ord.lpp p) = lpp (restrict_indets p)"
proof (cases "p = 0")
  case True
  thus ?thesis by simp
next
  case False
  hence "extended_ord.lpp p \<in> keys p" by (rule extended_ord.punit.lt_in_keys)
  hence "restrict_indets_pp (extended_ord.lpp p) \<in> restrict_indets_pp ` keys p" by (rule imageI)
  also from assms have eq: "\<dots> = keys (restrict_indets p)" by (rule keys_restrict_indets[symmetric])
  finally show ?thesis
  proof (rule punit.lt_eqI_keys[symmetric])
    fix t
    assume "t \<in> keys (restrict_indets p)"
    then obtain s where "s \<in> keys p" and t: "t = restrict_indets_pp s" unfolding eq[symmetric] ..
    from this(1) have "extended_ord s (extended_ord.lpp p)" by (rule extended_ord.punit.lt_max_keys)
    thus "t \<preceq> restrict_indets_pp (extended_ord.lpp p)" by (auto simp: t extended_ord_def)
  qed
qed

lemma restrict_indets_reduced_GB:
  assumes "finite X" and "F \<subseteq> P[X]"
  shows "punit.is_Groebner_basis (restrict_indets ` extended_ord.punit.reduced_GB (homogenize None ` extend_indets ` F))"
          (is ?thesis1)
    and "ideal (restrict_indets ` extended_ord.punit.reduced_GB (homogenize None ` extend_indets ` F)) = ideal F"
          (is ?thesis2)
    and "restrict_indets ` extended_ord.punit.reduced_GB (homogenize None ` extend_indets ` F) \<subseteq> P[X]"
          (is ?thesis3)
proof -
  let ?F = "homogenize None ` extend_indets ` F"
  let ?G = "extended_ord.punit.reduced_GB ?F"
  from assms(1) have "finite (insert None (Some ` X))" by simp
  moreover have "?F \<subseteq> P[insert None (Some ` X)]"
  proof
    fix hf
    assume "hf \<in> ?F"
    then obtain f where "f \<in> F" and hf: "hf = homogenize None (extend_indets f)" by auto
    from this(1) assms(2) have "f \<in> P[X]" ..
    hence "indets f \<subseteq> X" by (rule PolysD)
    hence "Some ` indets f \<subseteq> Some ` X" by (rule image_mono)
    with indets_extend_indets[of f] have "indets (extend_indets f) \<subseteq> Some ` X" by blast
    hence "insert None (indets (extend_indets f)) \<subseteq> insert None (Some ` X)" by blast
    with indets_homogenize_subset have "indets hf \<subseteq> insert None (Some ` X)"
      unfolding hf by (rule subset_trans)
    thus "hf \<in> P[insert None (Some ` X)]" by (rule PolysI_alt)
  qed
  ultimately have G_sub: "?G \<subseteq> P[insert None (Some ` X)]"
    and ideal_G: "ideal ?G = ideal ?F"
    and GB_G: "extended_ord.punit.is_reduced_GB ?G"
    by (rule extended_ord.reduced_GB_Polys, rule extended_ord.reduced_GB_ideal_Polys,
        rule extended_ord.reduced_GB_is_reduced_GB_Polys)

  show ?thesis3
  proof
    fix g
    assume "g \<in> restrict_indets ` ?G"
    then obtain g' where "g' \<in> ?G" and g: "g = restrict_indets g'" ..
    from this(1) G_sub have "g' \<in> P[insert None (Some ` X)]" ..
    hence "indets g' \<subseteq> insert None (Some ` X)" by (rule PolysD)
    have "indets g \<subseteq> the ` (indets g' - {None})" by (simp only: g indets_restrict_indets_subset)
    also from \<open>indets g' \<subseteq> insert None (Some ` X)\<close> have "\<dots> \<subseteq> X" by auto
    finally show "g \<in> P[X]" by (rule PolysI_alt)
  qed

  from dickson_grading_varnum show ?thesis1
  proof (rule punit.isGB_I_adds_lt[simplified])
    from \<open>?thesis3\<close> show "restrict_indets ` ?G \<subseteq> punit.dgrad_p_set (varnum X) 0"
      by (simp only: dgrad_p_set_varnum)
  next
    fix p :: "('a \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'b"
    assume "p \<noteq> 0"
    assume "p \<in> ideal (restrict_indets ` ?G)"
    hence "extend_indets p \<in> extend_indets ` ideal (restrict_indets ` ?G)" by (rule imageI)
    also have "\<dots> \<subseteq> ideal (extend_indets ` restrict_indets ` ?G)" by (fact extend_indets_ideal_subset)
    also have "\<dots> = ideal (dehomogenize None ` ?G)"
      by (simp only: image_comp extend_indets_comp_restrict_indets)
    finally have p_in_ideal: "extend_indets p \<in> ideal (dehomogenize None ` ?G)" .
    assume "p \<in> punit.dgrad_p_set (varnum X) 0"
    hence "p \<in> P[X]" by (simp only: dgrad_p_set_varnum)
    have "extended_ord.punit.is_Groebner_basis (dehomogenize None ` ?G)"
      using extended_ord_is_hom_ord \<open>finite (insert None (Some ` X))\<close> G_sub
    proof (rule extended_ord.isGB_dehomogenize)
      from GB_G show "extended_ord.punit.is_Groebner_basis ?G"
        by (rule extended_ord.punit.reduced_GB_D1)
    next
      fix g
      assume "g \<in> ?G"
      with _ GB_G ideal_G show "homogeneous g"
      proof (rule extended_ord.is_reduced_GB_homogeneous)
        fix hf
        assume "hf \<in> ?F"
        then obtain f where "hf = homogenize None f" ..
        thus "homogeneous hf" by (simp only: homogeneous_homogenize)
      qed
    qed
    moreover note p_in_ideal
    moreover from \<open>p \<noteq> 0\<close> have "extend_indets p \<noteq> 0" by simp
    ultimately obtain g where g_in: "g \<in> dehomogenize None ` ?G" and "g \<noteq> 0"
      and adds: "extended_ord.lpp g adds extended_ord.lpp (extend_indets p)"
      by (rule extended_ord.punit.GB_adds_lt[simplified])
    have "None \<notin> indets g"
    proof
      assume "None \<in> indets g"
      moreover from g_in obtain g0 where "g = dehomogenize None g0" ..
      ultimately show False using indets_dehomogenize[of None g0] by blast
    qed
    show "\<exists>g\<in>restrict_indets ` ?G. g \<noteq> 0 \<and> lpp g adds lpp p"
    proof (intro bexI conjI notI)
      have "lpp (restrict_indets g) = restrict_indets_pp (extended_ord.lpp g)"
        by (rule sym, intro extended_ord_lp \<open>None \<notin> indets g\<close>)
      also from adds have "\<dots> adds restrict_indets_pp (extended_ord.lpp (extend_indets p))"
        by (simp add: adds_poly_mapping le_fun_def lookup_restrict_indets_pp)
      also have "\<dots> = lpp (restrict_indets (extend_indets p))"
      proof (intro extended_ord_lp notI)
        assume "None \<in> indets (extend_indets p)"
        thus False by (simp add: indets_extend_indets)
      qed
      also have "\<dots> = lpp p" by simp
      finally show "lpp (restrict_indets g) adds lpp p" .
    next
      from g_in have "restrict_indets g \<in> restrict_indets ` dehomogenize None ` ?G" by (rule imageI)
      also have "\<dots> = restrict_indets ` ?G" by (simp only: image_comp restrict_indets_comp_dehomogenize)
      finally show "restrict_indets g \<in> restrict_indets ` ?G" .
    next
      assume "restrict_indets g = 0"
      with \<open>None \<notin> indets g\<close> extend_restrict_indets have "g = 0" by fastforce
      with \<open>g \<noteq> 0\<close> show False ..
    qed
  qed (fact assms(1))

  from ideal_G show ?thesis2 by (rule ideal_restrict_indets)
qed

end

end (* theory *)
