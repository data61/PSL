(*  Title:       IsomorphismClass
    Author:      Eugene W. Stark <stark@cs.stonybrook.edu>, 2019
    Maintainer:  Eugene W. Stark <stark@cs.stonybrook.edu>
*)

section "Isomorphism Classes"

text \<open>
  The following is a small theory that facilitates working with isomorphism classes of objects
  in a category.
\<close>

theory IsomorphismClass
imports Category3.EpiMonoIso Category3.NaturalTransformation
begin

  context category
  begin

    notation isomorphic (infix "\<cong>" 50)

    definition iso_class ("\<lbrakk>_\<rbrakk>")
    where "iso_class f \<equiv> {f'. f \<cong> f'}"

    definition is_iso_class
    where "is_iso_class F \<equiv> \<exists>f. f \<in> F \<and> F = iso_class f"

    definition iso_class_rep
    where "iso_class_rep F \<equiv> SOME f. f \<in> F"

    lemmas isomorphic_transitive [trans]
    lemmas naturally_isomorphic_transitive [trans]

    lemma inv_in_homI [intro]:
    assumes "iso f" and "\<guillemotleft>f : a \<rightarrow> b\<guillemotright>"
    shows "\<guillemotleft>inv f : b \<rightarrow> a\<guillemotright>"
      using assms inv_is_inverse seqE inverse_arrowsE
      by (metis ide_compE in_homE in_homI)

    lemma iso_class_is_nonempty:
    assumes "is_iso_class F"
    shows "F \<noteq> {}"
      using assms is_iso_class_def iso_class_def by auto

    lemma iso_class_memb_is_ide:
    assumes "is_iso_class F" and "f \<in> F"
    shows "ide f"
      using assms is_iso_class_def iso_class_def isomorphic_def by auto

    lemma ide_in_iso_class:
    assumes "ide f"
    shows "f \<in> \<lbrakk>f\<rbrakk>"
      using assms iso_class_def is_iso_class_def isomorphic_reflexive by simp

    lemma rep_in_iso_class:
    assumes "is_iso_class F"
    shows "iso_class_rep F \<in> F"
      using assms is_iso_class_def iso_class_rep_def someI_ex [of "\<lambda>f. f \<in> F"]
            ide_in_iso_class
      by metis

    lemma is_iso_classI:
    assumes "ide f"
    shows "is_iso_class \<lbrakk>f\<rbrakk>"
      using assms iso_class_def is_iso_class_def isomorphic_reflexive by blast

    lemma rep_iso_class:
    assumes "ide f"
    shows "iso_class_rep \<lbrakk>f\<rbrakk> \<cong> f"
      using assms is_iso_classI rep_in_iso_class iso_class_def isomorphic_symmetric
      by blast

    lemma iso_class_elems_isomorphic:
    assumes "is_iso_class F" and "f \<in> F" and "f' \<in> F"
    shows "f \<cong> f'"
      using assms iso_class_def
      by (metis is_iso_class_def isomorphic_symmetric isomorphic_transitive mem_Collect_eq)

    lemma iso_class_eqI [intro]:
    assumes "f \<cong> g"
    shows "\<lbrakk>f\<rbrakk> = \<lbrakk>g\<rbrakk>"
    proof -
      have f: "ide f"
        using assms isomorphic_def by auto
      have g: "ide g"
        using assms isomorphic_def by auto
      have "f \<in> \<lbrakk>g\<rbrakk>"
        using assms iso_class_def isomorphic_symmetric by simp
      moreover have "g \<in> \<lbrakk>g\<rbrakk>"
        using assms g iso_class_def isomorphic_reflexive isomorphic_def by simp
      ultimately have "\<And>h. (h \<in> \<lbrakk>f\<rbrakk>) = (h \<in> \<lbrakk>g\<rbrakk>)"
        using assms g iso_class_def [of f] iso_class_def [of g]
              isomorphic_reflexive isomorphic_symmetric isomorphic_transitive
        by blast
      thus ?thesis by auto
    qed

    lemma iso_class_eq:
    assumes "is_iso_class F" and "is_iso_class G" and "F \<inter> G \<noteq> {}"
    shows "F = G"
    proof -
      obtain h where h: "h \<in> F \<and> h \<in> G"
        using assms by auto
      show ?thesis
        using assms h
        by (metis is_iso_class_def iso_class_elems_isomorphic iso_class_eqI)
    qed

    lemma iso_class_rep [simp]:
    assumes "is_iso_class F"
    shows "\<lbrakk>iso_class_rep F\<rbrakk> = F"
    proof (intro iso_class_eq)
      show "is_iso_class \<lbrakk>iso_class_rep F\<rbrakk>"
        using assms is_iso_classI iso_class_memb_is_ide rep_in_iso_class by blast
      show "is_iso_class F"
        using assms by simp
      show "\<lbrakk>iso_class_rep F\<rbrakk> \<inter> F \<noteq> {}"
        using assms rep_in_iso_class
        by (meson disjoint_iff_not_equal ide_in_iso_class iso_class_memb_is_ide)
    qed

  end

end
