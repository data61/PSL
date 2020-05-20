(* Author: Alexander Maletzky *)

section \<open>Computing Gr\"obner Bases by Triangularizing Macaulay Matrices\<close>

theory Groebner_Macaulay
  imports Groebner_Bases.Macaulay_Matrix Groebner_Bases.Groebner_PM Degree_Section Degree_Bound_Utils
begin

text \<open>Relationship between Gr\"obner bases and Macaulay matrices, following
  @{cite "Wiesinger-Widi2015"}.\<close>

subsection \<open>Gr\"obner Bases\<close>

lemma (in gd_term) Macaulay_list_is_GB:
  assumes "is_Groebner_basis G" and "pmdl (set ps) = pmdl G" and "G \<subseteq> phull (set ps)"
  shows "is_Groebner_basis (set (Macaulay_list ps))"
proof (simp only: GB_alt_3_finite[OF finite_set] pmdl_Macaulay_list, intro ballI impI)
  fix f
  assume "f \<in> pmdl (set ps)"
  also from assms(2) have "\<dots> = pmdl G" .
  finally have "f \<in> pmdl G" .
  assume "f \<noteq> 0"
  with assms(1) \<open>f \<in> pmdl G\<close> obtain g where "g \<in> G" and "g \<noteq> 0" and "lt g adds\<^sub>t lt f"
    by (rule GB_adds_lt)
  from assms(3) \<open>g \<in> G\<close> have "g \<in> phull (set ps)" ..
  from this \<open>g \<noteq> 0\<close> obtain g' where "g' \<in> set (Macaulay_list ps)" and "g' \<noteq> 0" and "lt g = lt g'"
    by (rule Macaulay_list_lt)
  show "\<exists>g\<in>set (Macaulay_list ps). g \<noteq> 0 \<and> lt g adds\<^sub>t lt f"
  proof (rule, rule)
    from \<open>lt g adds\<^sub>t lt f\<close> show "lt g' adds\<^sub>t lt f" by (simp only: \<open>lt g = lt g'\<close>)
  qed fact+
qed

subsection \<open>Bounds\<close>

context pm_powerprod
begin

context
  fixes X :: "'x set"
  assumes fin_X: "finite X"
begin

definition deg_shifts :: "nat \<Rightarrow> (('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'b) list \<Rightarrow> (('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'b::semiring_1) list"
  where "deg_shifts d fs = concat (map (\<lambda>f. (map (\<lambda>t. punit.monom_mult 1 t f)
                                        (punit.pps_to_list (deg_le_sect X (d - poly_deg f))))) fs)"

lemma set_deg_shifts:
  "set (deg_shifts d fs) = (\<Union>f\<in>set fs. (\<lambda>t. punit.monom_mult 1 t f) ` (deg_le_sect X (d - poly_deg f)))"
proof -
  from fin_X have "finite (deg_le_sect X d0)" for d0 by (rule finite_deg_le_sect)
  thus ?thesis by (simp add: deg_shifts_def punit.set_pps_to_list)
qed

corollary set_deg_shifts_singleton:
  "set (deg_shifts d [f]) = (\<lambda>t. punit.monom_mult 1 t f) ` (deg_le_sect X (d - poly_deg f))"
  by (simp add: set_deg_shifts)

lemma deg_shifts_superset: "set fs \<subseteq> set (deg_shifts d fs)"
proof -
  have "set fs = (\<Union>f\<in>set fs. {punit.monom_mult 1 0 f})" by simp
  also have "\<dots> \<subseteq> set (deg_shifts d fs)" unfolding set_deg_shifts using subset_refl
  proof (rule UN_mono)
    fix f
    assume "f \<in> set fs"
    have "punit.monom_mult 1 0 f \<in> (\<lambda>t. punit.monom_mult 1 t f) ` deg_le_sect X (d - poly_deg f)"
      using zero_in_deg_le_sect by (rule imageI)
    thus "{punit.monom_mult 1 0 f} \<subseteq> (\<lambda>t. punit.monom_mult 1 t f) ` deg_le_sect X (d - poly_deg f)"
      by simp
  qed
  finally show ?thesis .
qed

lemma deg_shifts_mono:
  assumes "set fs \<subseteq> set gs"
  shows "set (deg_shifts d fs) \<subseteq> set (deg_shifts d gs)"
  using assms by (auto simp add: set_deg_shifts)

lemma ideal_deg_shifts [simp]: "ideal (set (deg_shifts d fs)) = ideal (set fs)"
proof
  show "ideal (set (deg_shifts d fs)) \<subseteq> ideal (set fs)"
    by (rule ideal.span_subset_spanI, simp add: set_deg_shifts UN_subset_iff,
        intro ballI image_subsetI) (metis ideal.span_scale times_monomial_left ideal.span_base)
next
  from deg_shifts_superset show "ideal (set fs) \<subseteq> ideal (set (deg_shifts d fs))"
    by (rule ideal.span_mono)
qed

lemma thm_2_3_6:
  assumes "set fs \<subseteq> P[X]" and "is_GB_cofactor_bound (set fs) b"
  shows "punit.is_Groebner_basis (set (punit.Macaulay_list (deg_shifts b fs)))"
proof -
  from assms(2) finite_set assms(1) obtain G where "punit.is_Groebner_basis G"
    and ideal_G: "ideal G = ideal (set fs)" and G_sub: "G \<subseteq> P[X]"
    and 1: "\<And>g. g \<in> G \<Longrightarrow> \<exists>q. g = (\<Sum>f\<in>set fs. q f * f) \<and> (\<forall>f. q f \<in> P[X] \<and> poly_deg (q f * f) \<le> b)"
    by (rule is_GB_cofactor_boundE_finite_Polys) blast
  from this(1) show ?thesis
  proof (rule punit.Macaulay_list_is_GB)
    show "G \<subseteq> phull (set (deg_shifts b fs))" (is "_ \<subseteq> ?H")
    proof
      fix g
      assume "g \<in> G"
      hence "\<exists>q. g = (\<Sum>f\<in>set fs. q f * f) \<and> (\<forall>f. q f \<in> P[X] \<and> poly_deg (q f * f) \<le> b)" by (rule 1)
      then obtain q where g: "g = (\<Sum>f\<in>set fs. q f * f)" and "\<And>f. q f \<in> P[X]"
        and "\<And>f. poly_deg (q f * f) \<le> b" by blast
      show "g \<in> ?H" unfolding g
      proof (rule phull.span_sum)
        fix f
        assume "f \<in> set fs"
        have "1 \<noteq> (0::'a)" by simp
        show "q f * f \<in> ?H"
        proof (cases "f = 0 \<or> q f = 0")
          case True
          thus ?thesis by (auto simp add: phull.span_zero)
        next
          case False
          hence "q f \<noteq> 0" and "f \<noteq> 0" by simp_all
          with \<open>poly_deg (q f * f) \<le> b\<close> have "poly_deg (q f) \<le> b - poly_deg f"
            by (simp add: poly_deg_times)
          with \<open>q f \<in> P[X]\<close> have "keys (q f) \<subseteq> deg_le_sect X (b - poly_deg f)"
            by (rule keys_subset_deg_le_sectI)
          with finite_deg_le_sect[OF fin_X]
          have "q f * f = (\<Sum>t\<in>deg_le_sect X (b - poly_deg f). punit.monom_mult (lookup (q f) t) t f)"
            unfolding punit.mult_scalar_sum_monomials[simplified]
            by (rule sum.mono_neutral_left) (simp add: in_keys_iff)
          also have "\<dots> = (\<Sum>t\<in>deg_le_sect X (b - poly_deg f).
                              (lookup (q f) t) \<cdot> (punit.monom_mult 1 t f))"
            by (simp add: punit.monom_mult_assoc punit.map_scale_eq_monom_mult)
          also have "\<dots> = (\<Sum>t\<in>deg_le_sect X (b - poly_deg f).
                          ((\<lambda>f0. (lookup (q f) (punit.lp f0 - punit.lp f)) \<cdot> f0) \<circ>
                          (\<lambda>t. punit.monom_mult 1 t f)) t)"
            using refl by (rule sum.cong) (simp add: punit.lt_monom_mult[OF \<open>1 \<noteq> 0\<close> \<open>f \<noteq> 0\<close>])
          also have "\<dots> = (\<Sum>f0\<in>set (deg_shifts b [f]). (lookup (q f) (punit.lp f0 - punit.lp f)) \<cdot> f0)"
            unfolding set_deg_shifts_singleton
          proof (intro sum.reindex[symmetric] inj_onI)
            fix s t
            assume "punit.monom_mult 1 s f = punit.monom_mult 1 t f"
            thus "s = t" using \<open>1 \<noteq> 0\<close> \<open>f \<noteq> 0\<close> by (rule punit.monom_mult_inj_2)
          qed
          finally have "q f * f \<in> phull (set (deg_shifts b [f]))"
            by (simp add: phull.sum_in_spanI)
          also have "\<dots> \<subseteq> ?H" by (rule phull.span_mono, rule deg_shifts_mono, simp add: \<open>f \<in> set fs\<close>)
          finally show ?thesis .
        qed
      qed
    qed
  qed (simp add: ideal_G)
qed

lemma thm_2_3_7:
  assumes "set fs \<subseteq> P[X]" and "is_GB_cofactor_bound (set fs) b"
  shows "1 \<in> ideal (set fs) \<longleftrightarrow> 1 \<in> set (punit.Macaulay_list (deg_shifts b fs))" (is "?L \<longleftrightarrow> ?R")
proof
  assume ?L
  let ?G = "set (punit.Macaulay_list (deg_shifts b fs))"
  from assms have "punit.is_Groebner_basis ?G" by (rule thm_2_3_6)
  moreover from \<open>?L\<close> have "1 \<in> ideal ?G" by (simp add: punit.pmdl_Macaulay_list[simplified])
  moreover have "1 \<noteq> (0::_ \<Rightarrow>\<^sub>0 'a)" by simp
  ultimately obtain g where "g \<in> ?G" and "g \<noteq> 0" and "punit.lt g adds punit.lt (1::_ \<Rightarrow>\<^sub>0 'a)"
    by (rule punit.GB_adds_lt[simplified])
  from this(3) have lp_g: "punit.lt g = 0" by (simp add: punit.lt_monomial adds_zero flip: single_one)
  from punit.Macaulay_list_is_monic_set \<open>g \<in> ?G\<close> \<open>g \<noteq> 0\<close> have lc_g: "punit.lc g = 1"
    by (rule punit.is_monic_setD)
  have "g = 1"
  proof (rule poly_mapping_eqI)
    fix t
    show "lookup g t = lookup 1 t"
    proof (cases "t = 0")
      case True
      thus ?thesis using lc_g by (simp add: lookup_one punit.lc_def lp_g)
    next
      case False
      with zero_min[of t] have "\<not> t \<preceq> punit.lt g" by (simp add: lp_g)
      with punit.lt_max_keys have "t \<notin> keys g" by blast
      with False show ?thesis by (simp add: lookup_one in_keys_iff)
    qed
  qed
  with \<open>g \<in> ?G\<close> show "1 \<in> ?G" by simp
next
  assume ?R
  also have "\<dots> \<subseteq> phull (set (punit.Macaulay_list (deg_shifts b fs)))"
    by (rule phull.span_superset)
  also have "\<dots> = phull (set (deg_shifts b fs))" by (fact punit.phull_Macaulay_list)
  also have "\<dots> \<subseteq> ideal (set (deg_shifts b fs))" using punit.phull_subset_module by force
  finally show ?L by simp
qed

end

lemma thm_2_3_6_indets:
  assumes "is_GB_cofactor_bound (set fs) b"
  shows "punit.is_Groebner_basis (set (punit.Macaulay_list (deg_shifts (\<Union>(indets ` (set fs))) b fs)))"
  using _ _ assms
proof (rule thm_2_3_6)
  from finite_set show "finite (\<Union>(indets ` (set fs)))" by (simp add: finite_indets)
next
  show "set fs \<subseteq> P[\<Union>(indets ` (set fs))]" by (auto simp: Polys_alt)
qed

lemma thm_2_3_7_indets:
  assumes "is_GB_cofactor_bound (set fs) b"
  shows "1 \<in> ideal (set fs) \<longleftrightarrow> 1 \<in> set (punit.Macaulay_list (deg_shifts (\<Union>(indets ` (set fs))) b fs))"
  using _ _ assms
proof (rule thm_2_3_7)
  from finite_set show "finite (\<Union>(indets ` (set fs)))" by (simp add: finite_indets)
next
  show "set fs \<subseteq> P[\<Union>(indets ` (set fs))]" by (auto simp: Polys_alt)
qed

end (* pm_powerprod *)

end (* theory *)
