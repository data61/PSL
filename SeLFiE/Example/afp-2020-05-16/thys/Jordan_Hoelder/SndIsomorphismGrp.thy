(*  Title:      The Second Isomorphism Theorem for Groups
    Author:     Jakob von Raumer, Karlsruhe Institute of Technology
    Maintainer: Jakob von Raumer <jakob.raumer@student.kit.edu>
*)

theory SndIsomorphismGrp
imports
    "HOL-Algebra.Coset"
    Secondary_Sylow.SubgroupConjugation
begin

section \<open>The Second Isomorphism Theorem for Groups\<close>

subsection \<open>Preliminaries\<close>

lemma (in group) triv_subgroup:
  shows "subgroup {\<one>} G"
unfolding subgroup_def by auto

lemma (in group) triv_normal_subgroup:
  shows "{\<one>} \<lhd> G"
unfolding normal_def normal_axioms_def l_coset_def r_coset_def
using is_group triv_subgroup by auto

lemma (in group) normal_restrict_supergroup:
  assumes SsubG:"subgroup S G"
  assumes Nnormal:"N \<lhd> G"
  assumes "N \<subseteq> S"
  shows "N \<lhd> (G\<lparr>carrier := S\<rparr>)"
proof -
  interpret Sgrp: group "G\<lparr>carrier := S\<rparr>" using SsubG by (rule subgroup_imp_group)
  show ?thesis
  proof(rule Sgrp.normalI)
    show "subgroup N (G\<lparr>carrier := S\<rparr>)" using assms is_group by (metis subgroup.subgroup_of_subset normal_inv_iff)
  next
    from SsubG have "S \<subseteq> carrier G" by (rule subgroup.subset)
    thus "\<forall>x\<in>carrier (G\<lparr>carrier := S\<rparr>). N #>\<^bsub>G\<lparr>carrier := S\<rparr>\<^esub> x = x <#\<^bsub>G\<lparr>carrier := S\<rparr>\<^esub> N"
      using Nnormal unfolding normal_def normal_axioms_def l_coset_def r_coset_def by fastforce
  qed
qed

text \<open>As this is maybe the best place this fits in: Factorizing by the trivial subgroup
is an isomorphism.\<close>

lemma (in group) trivial_factor_iso:
  shows "the_elem \<in> iso (G Mod {\<one>}) G"
proof -
  have "group_hom G G (\<lambda>x. x)" unfolding group_hom_def group_hom_axioms_def hom_def using is_group by simp
  moreover have "(\<lambda>x. x) ` carrier G = carrier G" by simp
  moreover have "kernel G G (\<lambda>x. x) = {\<one>}" unfolding kernel_def by auto
  ultimately show ?thesis using group_hom.FactGroup_iso_set by force
qed

text \<open>And the dual theorem to the previous one: Factorizing by the group itself gives the trivial group\<close>

lemma (in group) self_factor_iso:
  shows "(\<lambda>X. the_elem ((\<lambda>x. \<one>) ` X)) \<in> iso (G Mod (carrier G)) (G\<lparr> carrier := {\<one>} \<rparr>)"
proof -
  have "group (G\<lparr>carrier := {\<one>}\<rparr>)" by (metis subgroup_imp_group triv_subgroup)
  hence "group_hom G (G\<lparr>carrier := {\<one>}\<rparr>) (\<lambda>x. \<one>)" unfolding group_hom_def group_hom_axioms_def hom_def using is_group by auto
  moreover have "(\<lambda>x. \<one>) ` carrier G = carrier (G\<lparr>carrier := {\<one>}\<rparr>)" by auto
  moreover have "kernel G (G\<lparr>carrier := {\<one>}\<rparr>) (\<lambda>x. \<one>) = carrier G" unfolding kernel_def by auto
  ultimately show ?thesis using group_hom.FactGroup_iso_set by force
qed

text \<open>This theory provides a proof of the second isomorphism theorems for groups. 
The theorems consist of several facts about normal subgroups.\<close>

text \<open>The first lemma states that whenever we have a subgroup @{term S} and
a normal subgroup @{term H} of a group @{term G}, their intersection is normal
in @{term G}\<close>

locale second_isomorphism_grp = normal +
  fixes S::"'a set"
  assumes subgrpS:"subgroup S G"

context second_isomorphism_grp
begin

interpretation groupS: group "G\<lparr>carrier := S\<rparr>"
using subgrpS by (metis subgroup_imp_group)

lemma normal_subgrp_intersection_normal:
  shows "S \<inter> H \<lhd> (G\<lparr>carrier := S\<rparr>)"
proof(auto simp: groupS.normal_inv_iff)
  from subgrpS is_subgroup have "\<And>x. x \<in> {S, H} \<Longrightarrow> subgroup x G" by auto
  hence "subgroup (\<Inter> {S, H}) G" using subgroups_Inter by blast
  hence "subgroup (S \<inter> H) G" by auto
  moreover have "S \<inter> H \<subseteq> S" by simp
  ultimately show "subgroup (S \<inter> H) (G\<lparr>carrier := S\<rparr>)" using is_group subgroup.subgroup_of_subset subgrpS by metis
next
  fix g h
  assume g:"g \<in> S" and hH:"h \<in> H" and hS:"h \<in> S" {
    from g hH subgrpS show "g \<otimes> h \<otimes> inv\<^bsub>G\<lparr>carrier := S\<rparr>\<^esub> g \<in> H" by (metis inv_op_closed2 subgroup.mem_carrier m_inv_consistent)
  } {
    from g hS subgrpS show "g \<otimes> h \<otimes> inv\<^bsub>G\<lparr>carrier := S\<rparr>\<^esub> g \<in> S" by (metis subgroup.m_closed subgroup.m_inv_closed m_inv_consistent)
  }
qed

lemma normal_set_mult_subgroup:
  shows "subgroup (H <#> S) G"
proof(rule subgroupI)
  show "H <#> S \<subseteq> carrier G" by (metis setmult_subset_G subgroup.subset subgrpS subset)
next
  have "\<one> \<in> H" "\<one> \<in> S" using is_subgroup subgrpS subgroup.one_closed by auto
  hence "\<one> \<otimes> \<one> \<in> H <#> S" unfolding set_mult_def by blast
  thus "H <#> S \<noteq> {}" by auto
next
  fix g
  assume g:"g \<in> H <#> S"
  then obtain h s where h:"h \<in> H" and s:"s \<in> S" and ghs:"g = h \<otimes> s" unfolding set_mult_def by auto
  hence "s \<in> carrier G" by (metis subgroup.mem_carrier subgrpS)
  with h ghs obtain h' where h':"h' \<in> H" and "g = s \<otimes> h'" using coset_eq unfolding r_coset_def l_coset_def by auto
  with s have "inv g = (inv h') \<otimes> (inv s)" by (metis inv_mult_group mem_carrier subgroup.mem_carrier subgrpS)
  moreover from h' s subgrpS have "inv h' \<in> H" "inv s \<in> S" using subgroup.m_inv_closed m_inv_closed by auto
  ultimately show "inv g \<in> H <#> S" unfolding set_mult_def by auto
next
  fix g g'
  assume g:"g \<in> H <#> S" and h:"g' \<in> H <#> S"
  then obtain h h' s s' where hh'ss':"h \<in> H" "h' \<in> H" "s \<in> S" "s' \<in> S" and "g = h \<otimes> s" and "g' = h' \<otimes> s'" unfolding set_mult_def by auto
  hence "g \<otimes> g' = (h \<otimes> s) \<otimes> (h' \<otimes> s')" by metis
  also from hh'ss' have inG:"h \<in> carrier G" "h' \<in> carrier G" "s \<in> carrier G" "s' \<in> carrier G" using subgrpS mem_carrier subgroup.mem_carrier by force+
  hence "(h \<otimes> s) \<otimes> (h' \<otimes> s') = h \<otimes> (s \<otimes> h') \<otimes> s'" using m_assoc by auto
  also from hh'ss' inG obtain h'' where h'':"h'' \<in> H" and "s \<otimes> h' = h'' \<otimes> s"using coset_eq unfolding r_coset_def l_coset_def by fastforce
  hence "h \<otimes> (s \<otimes> h') \<otimes> s' = h \<otimes> (h'' \<otimes> s) \<otimes> s'" by simp
  also from h'' inG have "... = (h \<otimes> h'') \<otimes> (s \<otimes> s')" using m_assoc mem_carrier by auto
  finally have "g \<otimes> g' = h \<otimes> h'' \<otimes> (s \<otimes> s')".
  moreover with h'' hh'ss' have "... \<in> H <#> S" unfolding set_mult_def using subgrpS subgroup.m_closed by fastforce
  ultimately show "g \<otimes> g' \<in> H <#> S" by simp
qed

lemma oneH:"\<one> \<in> H" by (metis is_subgroup subgroup.one_closed)

lemma H_contained_in_set_mult:
  shows "H \<subseteq> H <#> S"
proof auto
  have "\<one> \<in> S" by (metis subgroup.one_closed subgrpS)
  fix x
  assume x:"x \<in> H"
  with \<open>\<one> \<in> S\<close> have "x \<otimes> \<one> \<in> H <#> S" unfolding set_mult_def by force
  with x show  "x \<in> H <#> S" by (metis mem_carrier r_one)
qed

lemma S_contained_in_set_mult:
  shows "S \<subseteq> H <#> S"
proof auto
  fix s
  assume s:"s \<in> S"
  with oneH have "\<one> \<otimes> s \<in> H <#> S" unfolding set_mult_def by force
  with s show "s \<in> H <#> S" using subgrpS subgroup.mem_carrier l_one by force
qed

lemma normal_intersection_hom:
  shows "group_hom (G\<lparr>carrier := S\<rparr>) ((G\<lparr>carrier := H <#> S\<rparr>) Mod H) (\<lambda>g. H #> g)"
proof (auto del: equalityI simp: group_hom_def group_hom_axioms_def hom_def groupS.is_group)
  have  gr:"group (G\<lparr>carrier := H <#> S\<rparr>)" by (metis normal_set_mult_subgroup subgroup_imp_group)
  moreover have "H \<subseteq> H <#> S" by (rule H_contained_in_set_mult)
  moreover have "subgroup (H <#> S) G" by (metis normal_set_mult_subgroup)
  ultimately have "H \<lhd> (G\<lparr>carrier := H <#> S\<rparr>)" using normal_restrict_supergroup by (metis inv_op_closed2 is_subgroup normal_inv_iff)
  with gr show "group ((G\<lparr>carrier := H <#> S\<rparr>) Mod H)" by (metis normal.factorgroup_is_group)
next
  fix g
  assume g: "g \<in> S"
  with subgrpS have "\<one> \<otimes> g \<in> H <#> S" unfolding set_mult_def by fastforce
  with g have "g \<in> H <#> S" by (metis l_one subgroup.mem_carrier subgrpS)
  thus "H #> g \<in> carrier ((G\<lparr>carrier := H <#> S\<rparr>) Mod H)" unfolding FactGroup_def RCOSETS_def r_coset_def by auto
next
  show "\<And>x y. \<lbrakk>x \<in> S; y \<in> S\<rbrakk> \<Longrightarrow> H #> x \<otimes> y = H #> x <#> (H #> y)"
    using normal.rcos_sum normal_axioms subgroup.mem_carrier subgrpS by fastforce
qed

lemma normal_intersection_hom_kernel:
  shows "kernel (G\<lparr>carrier := S\<rparr>) ((G\<lparr>carrier := H <#> S\<rparr>) Mod H) (\<lambda>g. H #> g) = H \<inter> S"
proof -
  have "kernel (G\<lparr>carrier := S\<rparr>) ((G\<lparr>carrier := H <#> S\<rparr>) Mod H) (\<lambda>g. H #> g)
                 = {g \<in> S. H #> g = \<one>\<^bsub>(G\<lparr>carrier := H <#> S\<rparr>) Mod H\<^esub>}" unfolding kernel_def by auto
  also have "... = {g \<in> S. H #> g = H}" unfolding FactGroup_def by auto
  also have "... = {g \<in> S. g \<in> H}" by (metis coset_eq is_subgroup lcoset_join2 rcos_self subgroup.mem_carrier subgrpS)
  also have "... = H \<inter> S" by auto
  finally show ?thesis.
qed

lemma normal_intersection_hom_surj:
  shows "(\<lambda>g. H #> g) ` carrier (G\<lparr>carrier := S\<rparr>) = carrier ((G\<lparr>carrier := H <#> S\<rparr>) Mod H)"
proof auto
  fix g
  assume "g \<in> S"
  hence "g \<in> H <#> S" using S_contained_in_set_mult by auto
  thus "H #> g \<in> carrier ((G\<lparr>carrier := H <#> S\<rparr>) Mod H)" unfolding FactGroup_def RCOSETS_def r_coset_def by auto
next
  fix x
  assume "x \<in> carrier (G\<lparr>carrier := H <#> S\<rparr> Mod H)"
  then obtain h s where h:"h \<in> H" and s:"s \<in> S" and "x = H #> (h \<otimes> s)"
    unfolding FactGroup_def RCOSETS_def r_coset_def set_mult_def by auto
  hence "x = (H #> h) #> s" by (metis h s coset_mult_assoc mem_carrier subgroup.mem_carrier subgrpS subset)
  also have "... = H #> s" by (metis h is_group rcos_const)
  finally have "x = H #> s".
  with s show "x \<in> (#>) H ` S" by simp
qed

text \<open>Finally we can prove the actual isomorphism theorem:\<close>

theorem normal_intersection_quotient_isom:
  shows "(\<lambda>X. the_elem ((\<lambda>g. H #> g) ` X)) \<in> iso ((G\<lparr>carrier := S\<rparr>) Mod (H \<inter> S)) (((G\<lparr>carrier := H <#> S\<rparr>)) Mod H)"
using normal_intersection_hom_kernel[symmetric] normal_intersection_hom normal_intersection_hom_surj
by (metis group_hom.FactGroup_iso_set)

end

end
