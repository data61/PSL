theory Nominal_Wellfounded
imports
  Nominal2.Nominal2
begin

section \<open>Lemmas about Well-Foundedness and Permutations\<close>

definition less_bool_rel :: "bool rel" where
  "less_bool_rel \<equiv> {(x,y). x<y}"

lemma less_bool_rel_iff [simp]:
  "(a,b) \<in> less_bool_rel \<longleftrightarrow> \<not> a \<and> b"
by (metis less_bool_def less_bool_rel_def mem_Collect_eq split_conv)

lemma wf_less_bool_rel: "wf less_bool_rel"
by (metis less_bool_rel_iff wfUNIVI)


subsection \<open>Hull and well-foundedness\<close>

inductive_set hull_rel where
  "(p \<bullet> x, x) \<in> hull_rel"

lemma hull_relp_reflp: "reflp hull_relp"
by (metis hull_relp.intros permute_zero reflpI)

lemma hull_relp_symp: "symp hull_relp"
by (metis (poly_guards_query) hull_relp.simps permute_minus_cancel(2) sympI)

lemma hull_relp_transp: "transp hull_relp"
by (metis (full_types) hull_relp.simps permute_plus transpI)

lemma hull_relp_equivp: "equivp hull_relp"
by (metis equivpI hull_relp_reflp hull_relp_symp hull_relp_transp)

lemma hull_rel_relcomp_subset:
  assumes "eqvt R"
  shows "R O hull_rel \<subseteq> hull_rel O R"
proof
  fix x
  assume "x \<in> R O hull_rel"
  then obtain x1 x2 y where x: "x = (x1,x2)" and R: "(x1,y) \<in> R" and "(y,x2) \<in> hull_rel"
    by auto
  then obtain p where "y = p \<bullet> x2"
    by (metis hull_rel.simps)
  then have "-p \<bullet> y = x2"
    by (metis permute_minus_cancel(2))
  then have "(-p \<bullet> x1, x2) \<in> R"
    using R assms by (metis Pair_eqvt eqvt_def mem_permute_iff)
  moreover have "(x1, -p \<bullet> x1) \<in> hull_rel"
    by (metis hull_rel.intros permute_minus_cancel(2))
  ultimately show "x \<in> hull_rel O R"
    using x by auto
qed

lemma wf_hull_rel_relcomp:
  assumes "wf R" and "eqvt R"
  shows "wf (hull_rel O R)"
using assms by (metis hull_rel_relcomp_subset wf_relcomp_compatible)

lemma hull_rel_relcompI [simp]:
  assumes "(x, y) \<in> R"
  shows "(p \<bullet> x, y) \<in> hull_rel O R"
using assms by (metis hull_rel.intros relcomp.relcompI)

lemma hull_rel_relcomp_trivialI [simp]:
  assumes "(x, y) \<in> R"
  shows "(x, y) \<in> hull_rel O R"
using assms by (metis hull_rel_relcompI permute_zero)

end
