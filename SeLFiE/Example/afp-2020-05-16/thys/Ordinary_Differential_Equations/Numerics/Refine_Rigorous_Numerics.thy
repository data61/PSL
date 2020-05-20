theory Refine_Rigorous_Numerics
  imports
    Abstract_Rigorous_Numerics
begin

context approximate_sets begin

lemma ivl_rep_of_set_nres[le, refine_vcg]:
  fixes X::"'a::executable_euclidean_space set"
  shows "op_ivl_rep_of_set X \<le> ivl_rep_of_set X"
  unfolding ivl_rep_of_set_def Inf_spec_def Sup_spec_def op_ivl_rep_of_set_def
  by (refine_vcg) (auto simp: inf.coboundedI1)

lemma ivl_rep_of_sets_nres[le, refine_vcg]:
  "op_ivl_rep_of_sets XS \<le> ivl_rep_of_sets XS"
proof cases
  assume ne: "XS \<noteq> {}"
  have "op_ivl_rep_of_sets XS \<le> SPEC (\<lambda>(i, s). (\<forall>X\<in>XS. X \<subseteq> {i..s} \<and> i \<le> s))"
    unfolding op_ivl_rep_of_sets_def ivl_rep_of_sets_def split_beta
    by (refine_vcg FORWEAK_elementwise_rule)
      (auto simp: subset_iff le_infI1 le_infI2 le_supI1 le_supI2 ivl_rep_of_set_def split_beta'
        intro!: FORWEAK_elementwise_rule)
  also have "\<dots> = ivl_rep_of_sets XS" unfolding ivl_rep_of_sets_def
    using ne
    by (auto simp add: ivl_rep_of_sets_def)
  finally show ?thesis .
qed (auto simp: op_ivl_rep_of_sets_def ivl_rep_of_sets_def)

lemma ivl_rep_of_set_coll[unfolded ivl_rep_of_set_def, refine_vcg]:
  "ivl_rep_of_set_coll X \<le> ivl_rep_of_set X"
  unfolding ivl_rep_of_set_coll_def ivl_rep_of_set_def
  by refine_vcg auto

lemma ivls_of_set_FORWEAK[le, refine_vcg]:
  "ivls_of_sets X \<le> SPEC (\<lambda>R. X \<subseteq> R)"
  unfolding ivls_of_sets_def autoref_tag_defs
  by (refine_vcg FORWEAK_mono_rule[where I="\<lambda>XS U. \<Union>XS \<subseteq> U"]) auto

lemma intersects_nres[unfolded intersects_spec_def, le, refine_vcg]:
  shows "op_intersects X sctn \<le> intersects_spec X sctn"
  unfolding intersects_spec_def Inf_inner_def Sup_inner_def op_intersects_def
  by refine_vcg (force simp: plane_of_def)

lemma sbelow_sctns_coll_refine[unfolded sbelow_sctns_def, le, refine_vcg]:
  "sbelow_sctns_coll XS sctns \<le> sbelow_sctns XS sctns"
  unfolding sbelow_sctns_def autoref_tag_defs sbelow_sctns_coll_def
  by (refine_vcg FORWEAK_mono_rule[where I="\<lambda>X b. b \<longrightarrow> (\<Union>X \<subseteq> sbelow_halfspaces sctns)"]) auto

lemma below_sctn_coll_refine[unfolded below_sctn_def, le, refine_vcg]:
  "below_sctn_coll XS sctn \<le> below_sctn XS sctn"
  unfolding below_sctn_def autoref_tag_defs below_sctn_coll_def
  by (refine_vcg FORWEAK_mono_rule[where I="\<lambda>X b. b \<longrightarrow> (\<Union>X \<subseteq> below_halfspace sctn)"]) auto

lemma intersects_clw[unfolded intersects_spec_def, le, refine_vcg]:
  shows "intersects_clw X sctn \<le> intersects_spec X sctn"
  unfolding intersects_spec_def intersects_clw_def
  by (refine_vcg FORWEAK_mono_rule[where I="\<lambda>XS b. b \<or> \<Union>XS \<inter> plane_of sctn = {}"]) auto

lemma subset_spec_ivl_impl[unfolded subset_spec_def, le, refine_vcg]: "op_subset X ivl \<le> subset_spec X ivl"
  unfolding subset_spec_def autoref_tag_defs op_subset_def
  by (refine_vcg) force

lemma subset_spec_ivl_coll_impl[unfolded subset_spec_def, le, refine_vcg]: "subset_spec_coll X ivl  \<le> subset_spec X ivl"
  unfolding autoref_tag_defs subset_spec_def subset_spec_coll_def
  by (refine_vcg FORWEAK_mono_rule[where I="\<lambda>x b. b \<longrightarrow> \<Union>x \<subseteq> ivl"])
     (auto simp: subset_iff set_of_ivl_def)

lemma project_set_appr_le[unfolded project_set_def, le, refine_vcg]:
  "op_project_set X b y \<le> project_set X b y"
  unfolding project_set_def op_project_set_def
  by (refine_vcg) (force simp: plane_of_def)+

lemma project_set_clw_le[unfolded project_set_def, le, refine_vcg]: "project_set_clw X b y \<le> project_set X b y"
  unfolding autoref_tag_defs project_set_def project_set_clw_def
  by (refine_vcg FORWEAK_mono_rule[where I="\<lambda>X P. \<Union>X \<inter> {x. x \<bullet> b = y} \<subseteq> P \<and> P \<subseteq> {x. x \<bullet> b = y}"])
      auto

lemma subset_spec_ivls[unfolded subset_spec_def, le, refine_vcg]:
  "subset_spec_ivls X Y \<le> subset_spec X Y"
  unfolding subset_spec_ivls_def subset_spec_def
  by (refine_vcg FORWEAK_mono_rule'[where I="\<lambda>Ys b. b \<longrightarrow> X - \<Union>Ys \<subseteq> Y"]) auto

lemma split_along_ivls2[le, refine_vcg]:"split_along_ivls2 M X IS \<le> SPEC (\<lambda>R. R = X)"
  unfolding split_along_ivls2_def
  by (refine_vcg FORWEAK_mono_rule[where I="\<lambda>x xi. \<Union>x \<subseteq> xi \<and> xi \<subseteq> X"]) auto

end

context includes autoref_syntax begin

lemma length_slp_of_fas_le: "length fas \<le> length (slp_of_fas fas)"
  by (auto simp: slp_of_fas_def split: prod.splits)

lemma list_of_eucl_eqD: "list_of_eucl x = xs \<Longrightarrow> x = eucl_of_list xs"
  by auto

lemma slp_of_fasI:
  "d = (length fas) \<Longrightarrow>
    take d (interpret_slp (slp_of_fas fas) xs) =
    interpret_floatariths fas xs"
  using slp_of_fas by force


end

context approximate_sets begin

lemma approx_fas[le, refine_vcg]:
  "approx_slp_appr fas slp X \<le> SPEC (\<lambda>R. \<forall>x \<in> X. einterpret fas x \<in> (R::'a set))"
  if "slp_of_fas fas = slp" "length fas = DIM('a::executable_euclidean_space)"
  unfolding approx_slp_appr_def
  by (refine_vcg that)

lemma mig_set[le, refine_vcg]: "mig_set D X \<le> SPEC (\<lambda>m. \<forall>x \<in> X. m \<le> norm x)"
  unfolding mig_set_def
  apply refine_vcg
  apply (auto simp: dest!: bspec)
  apply (rule order_trans, assumption)
  apply (rule norm_mig_componentwise_le)
  by auto

end

end