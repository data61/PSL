(* Author: Alexander Maletzky *)

section \<open>Utility Definitions and Lemmas about Degree Bounds for Gr\"obner Bases\<close>

theory Degree_Bound_Utils
  imports Groebner_Bases.Groebner_PM
begin

context pm_powerprod
begin

definition is_GB_cofactor_bound :: "(('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'b::field) set \<Rightarrow> nat \<Rightarrow> bool"
  where "is_GB_cofactor_bound F b \<longleftrightarrow>
    (\<exists>G. punit.is_Groebner_basis G \<and> ideal G = ideal F \<and> (UN g:G. indets g) \<subseteq> (UN f:F. indets f) \<and>
      (\<forall>g\<in>G. \<exists>F' q. finite F' \<and> F' \<subseteq> F \<and> g = (\<Sum>f\<in>F'. q f * f) \<and> (\<forall>f\<in>F'. poly_deg (q f * f) \<le> b)))"

definition is_hom_GB_bound :: "(('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'b::field) set \<Rightarrow> nat \<Rightarrow> bool"
  where "is_hom_GB_bound F b \<longleftrightarrow> ((\<forall>f\<in>F. homogeneous f) \<longrightarrow> (\<forall>g\<in>punit.reduced_GB F. poly_deg g \<le> b))"

lemma is_GB_cofactor_boundI:
  assumes "punit.is_Groebner_basis G" and "ideal G = ideal F" and "\<Union>(indets ` G) \<subseteq> \<Union>(indets ` F)"
    and "\<And>g. g \<in> G \<Longrightarrow> \<exists>F' q. finite F' \<and> F' \<subseteq> F \<and> g = (\<Sum>f\<in>F'. q f * f) \<and> (\<forall>f\<in>F'. poly_deg (q f * f) \<le> b)"
  shows "is_GB_cofactor_bound F b"
  unfolding is_GB_cofactor_bound_def using assms by blast

lemma is_GB_cofactor_boundE:
  fixes F :: "(('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'b::field) set"
  assumes "is_GB_cofactor_bound F b"
  obtains G where "punit.is_Groebner_basis G" and "ideal G = ideal F" and "\<Union>(indets ` G) \<subseteq> \<Union>(indets ` F)"
    and "\<And>g. g \<in> G \<Longrightarrow> \<exists>F' q. finite F' \<and> F' \<subseteq> F \<and> g = (\<Sum>f\<in>F'. q f * f) \<and>
                          (\<forall>f. indets (q f) \<subseteq> \<Union>(indets ` F) \<and> poly_deg (q f * f) \<le> b \<and> (f \<notin> F' \<longrightarrow> q f = 0))"
proof -
  let ?X = "\<Union>(indets ` F)"
  from assms obtain G where "punit.is_Groebner_basis G" and "ideal G = ideal F" and "\<Union>(indets ` G) \<subseteq> ?X"
    and 1: "\<And>g. g \<in> G \<Longrightarrow> \<exists>F' q. finite F' \<and> F' \<subseteq> F \<and> g = (\<Sum>f\<in>F'. q f * f) \<and> (\<forall>f\<in>F'. poly_deg (q f * f) \<le> b)"
    by (auto simp: is_GB_cofactor_bound_def)
  from this(1, 2, 3) show ?thesis
  proof
    fix g
    assume "g \<in> G"
    show "\<exists>F' q. finite F' \<and> F' \<subseteq> F \<and> g = (\<Sum>f\<in>F'. q f * f) \<and>
                (\<forall>f. indets (q f) \<subseteq> ?X \<and> poly_deg (q f * f) \<le> b \<and> (f \<notin> F' \<longrightarrow> q f = 0))"
    proof (cases "g = 0")
      case True
      define q where "q = (\<lambda>f::('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'b. 0::('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'b)"
      show ?thesis
      proof (intro exI conjI allI)
        show "g = (\<Sum>f\<in>{}. q f * f)" by (simp add: True q_def)
      qed (simp_all add: q_def)
    next
      case False
      let ?X = "\<Union>(indets ` F)"
      from \<open>g \<in> G\<close> have "\<exists>F' q. finite F' \<and> F' \<subseteq> F \<and> g = (\<Sum>f\<in>F'. q f * f) \<and> (\<forall>f\<in>F'. poly_deg (q f * f) \<le> b)"
        by (rule 1)
      then obtain F' q0 where "finite F'" and "F' \<subseteq> F" and g: "g = (\<Sum>f\<in>F'. q0 f * f)"
        and q0: "\<And>f. f \<in> F' \<Longrightarrow> poly_deg (q0 f * f) \<le> b" by blast
      define sub where "sub = (\<lambda>x::'x. if x \<in> ?X then
                                         monomial (1::'b) (Poly_Mapping.single x (1::nat))
                                       else 1)"
      have 1: "sub x = monomial 1 (monomial 1 x)" if "x \<in> indets g" for x
      proof (simp add: sub_def, rule)
        from that \<open>g \<in> G\<close> have "x \<in> \<Union>(indets ` G)" by blast
        also have "\<dots> \<subseteq> ?X" by fact
        finally obtain f where "f \<in> F" and "x \<in> indets f" ..
        assume "\<forall>f\<in>F. x \<notin> indets f"
        hence "x \<notin> indets f" using \<open>f \<in> F\<close> ..
        thus "monomial 1 (monomial (Suc 0) x) = 1" using \<open>x \<in> indets f\<close> ..
      qed
      have 2: "sub x = monomial 1 (monomial 1 x)" if "f \<in> F'" and "x \<in> indets f" for f x
      proof (simp add: sub_def, rule)
        assume "\<forall>f\<in>F. x \<notin> indets f"
        moreover from that(1) \<open>F' \<subseteq> F\<close> have "f \<in> F" ..
        ultimately have "x \<notin> indets f" ..
        thus "monomial 1 (monomial (Suc 0) x) = 1" using that(2) ..
      qed
      have 3: "poly_subst sub f = f" if "f \<in> F'" for f by (rule poly_subst_id, rule 2, rule that)
      define q where "q = (\<lambda>f. if f \<in> F' then poly_subst sub (q0 f) else 0)"
      show ?thesis
      proof (intro exI allI conjI impI)
        from 1 have "g = poly_subst sub g" by (rule poly_subst_id[symmetric])
        also have "\<dots> = (\<Sum>f\<in>F'. q f * (poly_subst sub f))"
          by (simp add: g poly_subst_sum poly_subst_times q_def cong: sum.cong)
        also from refl have "\<dots> = (\<Sum>f\<in>F'. q f * f)"
        proof (rule sum.cong)
          fix f
          assume "f \<in> F'"
          hence "poly_subst sub f = f" by (rule 3)
          thus "q f * poly_subst sub f = q f * f" by simp
        qed
        finally show "g = (\<Sum>f\<in>F'. q f * f)" .
      next
        fix f
        have "indets (q f) \<subseteq> ?X \<and> poly_deg (q f * f) \<le> b"
        proof (cases "f \<in> F'")
          case True
          hence qf: "q f = poly_subst sub (q0 f)" by (simp add: q_def)
          show ?thesis
          proof
            show "indets (q f) \<subseteq> ?X"
            proof
              fix x
              assume "x \<in> indets (q f)"
              then obtain y where "x \<in> indets (sub y)" unfolding qf by (rule in_indets_poly_substE)
              hence y: "y \<in> ?X" and "x \<in> indets (monomial (1::'b) (monomial (1::nat) y))"
                by (simp_all add: sub_def split: if_splits)
              from this(2) have "x = y" by (simp add: indets_monomial)
              with y show "x \<in> ?X" by (simp only:)
            qed
          next
            from \<open>f \<in> F'\<close> have "poly_subst sub f = f" by (rule 3)
            hence "poly_deg (q f * f) = poly_deg (q f * poly_subst sub f)" by (simp only:)
            also have "\<dots> = poly_deg (poly_subst sub (q0 f * f))" by (simp only: qf poly_subst_times)
            also have "\<dots> \<le> poly_deg (q0 f * f)"
            proof (rule poly_deg_poly_subst_le)
              fix x
              show "poly_deg (sub x) \<le> 1" by (simp add: sub_def poly_deg_monomial deg_pm_single)
            qed
            also from \<open>f \<in> F'\<close> have "\<dots> \<le> b" by (rule q0)
            finally show "poly_deg (q f * f) \<le> b" .
          qed
        next
          case False
          thus ?thesis by (simp add: q_def)
        qed
        thus "indets (q f) \<subseteq> ?X" and "poly_deg (q f * f) \<le> b" by simp_all

        assume "f \<notin> F'"
        thus "q f = 0" by (simp add: q_def)
      qed fact+
    qed
  qed
qed

lemma is_GB_cofactor_boundE_Polys:
  fixes F :: "(('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'b::field) set"
  assumes "is_GB_cofactor_bound F b" and "F \<subseteq> P[X]"
  obtains G where "punit.is_Groebner_basis G" and "ideal G = ideal F" and "G \<subseteq> P[X]"
    and "\<And>g. g \<in> G \<Longrightarrow> \<exists>F' q. finite F' \<and> F' \<subseteq> F \<and> g = (\<Sum>f\<in>F'. q f * f) \<and>
                            (\<forall>f. q f \<in> P[X] \<and> poly_deg (q f * f) \<le> b \<and> (f \<notin> F' \<longrightarrow> q f = 0))"
proof -
  let ?X = "\<Union>(indets ` F)"
  have "?X \<subseteq> X"
  proof
    fix x
    assume "x \<in> ?X"
    then obtain f where "f \<in> F" and "x \<in> indets f" ..
    from this(1) assms(2) have "f \<in> P[X]" ..
    hence "indets f \<subseteq> X" by (rule PolysD)
    with \<open>x \<in> indets f\<close> show "x \<in> X" ..
  qed
  from assms(1) obtain G where "punit.is_Groebner_basis G" and "ideal G = ideal F"
    and 1: "\<Union>(indets ` G) \<subseteq> ?X"
    and 2: "\<And>g. g \<in> G \<Longrightarrow> \<exists>F' q. finite F' \<and> F' \<subseteq> F \<and> g = (\<Sum>f\<in>F'. q f * f) \<and>
                            (\<forall>f. indets (q f) \<subseteq> ?X \<and> poly_deg (q f * f) \<le> b \<and> (f \<notin> F' \<longrightarrow> q f = 0))"
    by (rule is_GB_cofactor_boundE) blast
  from this(1, 2) show ?thesis
  proof
    show "G \<subseteq> P[X]"
    proof
      fix g
      assume "g \<in> G"
      hence "indets g \<subseteq> \<Union>(indets ` G)" by blast
      also have "\<dots> \<subseteq> ?X" by fact
      also have "\<dots> \<subseteq> X" by fact
      finally show "g \<in> P[X]" by (rule PolysI_alt)
    qed
  next
    fix g
    assume "g \<in> G"
    hence "\<exists>F' q. finite F' \<and> F' \<subseteq> F \<and> g = (\<Sum>f\<in>F'. q f * f) \<and>
                  (\<forall>f. indets (q f) \<subseteq> ?X \<and> poly_deg (q f * f) \<le> b \<and> (f \<notin> F' \<longrightarrow> q f = 0))"
      by (rule 2)
    then obtain F' q where "finite F'" and "F' \<subseteq> F" and "g = (\<Sum>f\<in>F'. q f * f)"
      and "\<And>f. indets (q f) \<subseteq> ?X" and "\<And>f. poly_deg (q f * f) \<le> b" and "\<And>f. f \<notin> F' \<Longrightarrow> q f = 0"
      by blast
    show "\<exists>F' q. finite F' \<and> F' \<subseteq> F \<and> g = (\<Sum>f\<in>F'. q f * f) \<and>
                  (\<forall>f. q f \<in> P[X] \<and> poly_deg (q f * f) \<le> b \<and> (f \<notin> F' \<longrightarrow> q f = 0))"
    proof (intro exI allI conjI impI)
      fix f
      from \<open>indets (q f) \<subseteq> ?X\<close> \<open>?X \<subseteq> X\<close> have "indets (q f) \<subseteq> X" by (rule subset_trans)
      thus "q f \<in> P[X]" by (rule PolysI_alt)
    qed fact+
  qed
qed

lemma is_GB_cofactor_boundE_finite_Polys:
  fixes F :: "(('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'b::field) set"
  assumes "is_GB_cofactor_bound F b" and "finite F" and "F \<subseteq> P[X]"
  obtains G where "punit.is_Groebner_basis G" and "ideal G = ideal F" and "G \<subseteq> P[X]"
    and "\<And>g. g \<in> G \<Longrightarrow> \<exists>q. g = (\<Sum>f\<in>F. q f * f) \<and> (\<forall>f. q f \<in> P[X] \<and> poly_deg (q f * f) \<le> b)"
proof -
  from assms(1, 3) obtain G where "punit.is_Groebner_basis G" and "ideal G = ideal F" and "G \<subseteq> P[X]"
    and 1: "\<And>g. g \<in> G \<Longrightarrow> \<exists>F' q. finite F' \<and> F' \<subseteq> F \<and> g = (\<Sum>f\<in>F'. q f * f) \<and>
                            (\<forall>f. q f \<in> P[X] \<and> poly_deg (q f * f) \<le> b \<and> (f \<notin> F' \<longrightarrow> q f = 0))"
    by (rule is_GB_cofactor_boundE_Polys) blast
  from this(1, 2, 3) show ?thesis
  proof
    fix g
    assume "g \<in> G"
    hence "\<exists>F' q. finite F' \<and> F' \<subseteq> F \<and> g = (\<Sum>f\<in>F'. q f * f) \<and>
                            (\<forall>f. q f \<in> P[X] \<and> poly_deg (q f * f) \<le> b \<and> (f \<notin> F' \<longrightarrow> q f = 0))"
      by (rule 1)
    then obtain F' q where "F' \<subseteq> F" and g: "g = (\<Sum>f\<in>F'. q f * f)"
      and "\<And>f. q f \<in> P[X]" and "\<And>f. poly_deg (q f * f) \<le> b" and 2: "\<And>f. f \<notin> F' \<Longrightarrow> q f = 0" by blast
    show "\<exists>q. g = (\<Sum>f\<in>F. q f * f) \<and> (\<forall>f. q f \<in> P[X] \<and> poly_deg (q f * f) \<le> b)"
    proof (intro exI conjI impI allI)
      from assms(2) \<open>F' \<subseteq> F\<close> have "(\<Sum>f\<in>F'. q f * f) = (\<Sum>f\<in>F. q f * f)"
      proof (intro sum.mono_neutral_left ballI)
        fix f
        assume "f \<in> F - F'"
        hence "f \<notin> F'" by simp
        hence "q f = 0" by (rule 2)
        thus "q f * f = 0" by simp
      qed
      thus "g = (\<Sum>f\<in>F. q f * f)" by (simp only: g)
    qed fact+
  qed
qed

lemma is_GB_cofactor_boundI_subset_zero:
  assumes "F \<subseteq> {0}"
  shows "is_GB_cofactor_bound F b"
  using punit.is_Groebner_basis_empty
proof (rule is_GB_cofactor_boundI)
  from assms show "ideal {} = ideal F" by (metis ideal.span_empty ideal_eq_zero_iff)
qed simp_all

lemma is_hom_GB_boundI:
  "(\<And>g. (\<And>f. f \<in> F \<Longrightarrow> homogeneous f) \<Longrightarrow> g \<in> punit.reduced_GB F \<Longrightarrow> poly_deg g \<le> b) \<Longrightarrow> is_hom_GB_bound F b"
  unfolding is_hom_GB_bound_def by blast

lemma is_hom_GB_boundD:
  "is_hom_GB_bound F b \<Longrightarrow> (\<And>f. f \<in> F \<Longrightarrow> homogeneous f) \<Longrightarrow> g \<in> punit.reduced_GB F \<Longrightarrow> poly_deg g \<le> b"
  unfolding is_hom_GB_bound_def by blast

text \<open>The following is the main theorem in this theory. It shows that a bound for Gr\"obner bases of
  homogenized input sets is always also a cofactor bound for the original input sets.\<close>

lemma (in extended_ord_pm_powerprod) hom_GB_bound_is_GB_cofactor_bound:
  assumes "finite X" and "F \<subseteq> P[X]" and "extended_ord.is_hom_GB_bound (homogenize None ` extend_indets ` F) b"
  shows "is_GB_cofactor_bound F b"
proof -
  let ?F = "homogenize None ` extend_indets ` F"
  define Y where "Y = \<Union> (indets ` F)"
  define G where "G = restrict_indets ` (extended_ord.punit.reduced_GB ?F)"
  have "Y \<subseteq> X"
  proof
    fix x
    assume "x \<in> Y"
    then obtain f where "f \<in> F" and "x \<in> indets f" unfolding Y_def ..
    from this(1) assms(2) have "f \<in> P[X]" ..
    hence "indets f \<subseteq> X" by (rule PolysD)
    with \<open>x \<in> indets f\<close> show "x \<in> X" ..
  qed
  hence "finite Y" using assms(1) by (rule finite_subset)
  moreover have "F \<subseteq> P[Y]" by (auto simp: Y_def Polys_alt)
  ultimately have "punit.is_Groebner_basis G" and "ideal G = ideal F" and "G \<subseteq> P[Y]"
    unfolding G_def by (rule restrict_indets_reduced_GB)+
  from this(1, 2) show ?thesis
  proof (rule is_GB_cofactor_boundI)
    from \<open>G \<subseteq> P[Y]\<close> show "\<Union> (indets ` G) \<subseteq> \<Union> (indets ` F)" by (auto simp: Y_def Polys_alt)
  next
    fix g
    assume "g \<in> G"
    then obtain g' where g': "g' \<in> extended_ord.punit.reduced_GB ?F"
      and g: "g = restrict_indets g'" unfolding G_def ..
    have "f \<in> ?F \<Longrightarrow> homogeneous f" for f by (auto simp: homogeneous_homogenize)
    with assms(3) have "poly_deg g' \<le> b" using g' by (rule extended_ord.is_hom_GB_boundD)
    from g' have "g' \<in> ideal (extended_ord.punit.reduced_GB ?F)" by (rule ideal.span_base)
    also have "\<dots> = ideal ?F"
    proof (rule extended_ord.reduced_GB_ideal_Polys)
      from \<open>finite Y\<close> show "finite (insert None (Some ` Y))" by simp
    next
      show "?F \<subseteq> P[insert None (Some ` Y)]"
      proof
        fix f0
        assume "f0 \<in> ?F"
        then obtain f where "f \<in> F" and f0: "f0 = homogenize None (extend_indets f)" by blast
        from this(1) \<open>F \<subseteq> P[Y]\<close> have "f \<in> P[Y]" ..
        hence "extend_indets f \<in> P[Some ` Y]" by (auto simp: indets_extend_indets Polys_alt)
        thus "f0 \<in> P[insert None (Some ` Y)]" unfolding f0 by (rule homogenize_in_Polys)
      qed
    qed
    finally have "g' \<in> ideal ?F" .
    with \<open>\<And>f. f \<in> ?F \<Longrightarrow> homogeneous f\<close> obtain F0 q where "finite F0" and "F0 \<subseteq> ?F"
      and g': "g' = (\<Sum>f\<in>F0. q f * f)" and deg_le: "\<And>f. poly_deg (q f * f) \<le> poly_deg g'"
      by (rule homogeneous_idealE) blast+
    from this(2) obtain F' where "F' \<subseteq> F" and F0: "F0 = homogenize None ` extend_indets ` F'"
      and inj_on: "inj_on (homogenize None \<circ> extend_indets) F'"
      unfolding image_comp by (rule subset_imageE_inj)
    show "\<exists>F' q. finite F' \<and> F' \<subseteq> F \<and> g = (\<Sum>f\<in>F'. q f * f) \<and> (\<forall>f\<in>F'. poly_deg (q f * f) \<le> b)"
    proof (intro exI conjI ballI)
      from inj_on \<open>finite F0\<close> show "finite F'" by (simp only: finite_image_iff F0 image_comp)
    next
      from inj_on show "g = (\<Sum>f\<in>F'. (restrict_indets \<circ> q \<circ> homogenize None \<circ> extend_indets) f * f)"
        by (simp add: g g' F0 restrict_indets_sum restrict_indets_times sum.reindex image_comp o_def)
    next
      fix f
      assume "f \<in> F'"
      have "poly_deg ((restrict_indets \<circ> q \<circ> homogenize None \<circ> extend_indets) f * f) =
              poly_deg (restrict_indets (q (homogenize None (extend_indets f)) * homogenize None (extend_indets f)))"
        by (simp add: restrict_indets_times)
      also have "\<dots> \<le> poly_deg (q (homogenize None (extend_indets f)) * homogenize None (extend_indets f))"
        by (rule poly_deg_restrict_indets_le)
      also have "\<dots> \<le> poly_deg g'" by (rule deg_le)
      also have "\<dots> \<le> b" by fact
      finally show "poly_deg ((restrict_indets \<circ> q \<circ> homogenize None \<circ> extend_indets) f * f) \<le> b" .
    qed fact
  qed
qed

end (* pm_powerprod *)

end (* theory *)
