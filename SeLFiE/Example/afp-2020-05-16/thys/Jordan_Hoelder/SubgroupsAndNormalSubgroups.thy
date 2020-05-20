(*  Title:      Additional Facts about Subgroups and Normal Subgroups
    Author:     Jakob von Raumer, Karlsruhe Institute of Technology
    Maintainer: Jakob von Raumer <jakob.raumer@student.kit.edu>
*)

theory SubgroupsAndNormalSubgroups
  imports
  Secondary_Sylow.SndSylow
  SndIsomorphismGrp
  "HOL-Algebra.Coset"
begin

section \<open>Preliminary lemmas\<close>

text \<open>A group of order 1 is always the trivial group.\<close>


lemma (in group) order_one_triv_iff:
  shows "(order G = 1) = (carrier G = {\<one>})"
proof
  assume order:"order G = 1"
  then obtain x where x:"carrier G = {x}" unfolding order_def by (auto simp add: card_Suc_eq)
  hence "\<one> = x" using one_closed by auto
  with x show "carrier G = {\<one>}" by simp
next
  assume "carrier G = {\<one>}"
  thus "order G = 1" unfolding order_def by auto
qed

lemma (in group) finite_pos_order:
  assumes finite:"finite (carrier G)"
  shows "0 < order G"
proof -
  from one_closed finite show ?thesis unfolding order_def by (metis card_gt_0_iff subgroup_nonempty subgroup_self)
qed

lemma iso_order_closed:
  assumes "\<phi> \<in> iso G H"
  shows "order G = order H"
using assms
unfolding order_def iso_def by (metis (no_types) bij_betw_same_card mem_Collect_eq)

section \<open>More Facts about Subgroups\<close>

lemma (in subgroup) subgroup_of_restricted_group:
  assumes "subgroup U (G\<lparr> carrier := H\<rparr>)"
  shows "U \<subseteq> H"
using assms subgroup.subset by force

lemma (in subgroup) subgroup_of_subgroup:
  assumes "group G"
  assumes "subgroup U (G\<lparr> carrier := H\<rparr>)"
  shows "subgroup U G"
proof
  from assms(2) have "U \<subseteq> H" by (rule subgroup_of_restricted_group)
  thus "U \<subseteq> carrier G" by (auto simp:subset)
next
  fix x y
  have a:"x \<otimes> y = x \<otimes>\<^bsub>G\<lparr> carrier := H\<rparr>\<^esub> y" by simp
  assume "x \<in> U" "y \<in> U"
  with assms a show " x \<otimes> y \<in> U" by (metis subgroup.m_closed)
next
  have "\<one>\<^bsub>G\<lparr> carrier := H\<rparr>\<^esub> = \<one>" by simp
  with assms show "\<one> \<in> U" by (metis subgroup.one_closed)
next
  have "subgroup H G"..
  fix x
  assume "x \<in> U"
  with assms(2) have "inv\<^bsub>G\<lparr> carrier := H\<rparr>\<^esub> x \<in> U" by (rule subgroup.m_inv_closed)
  moreover from assms \<open>x \<in> U\<close> have "x \<in> H" by (metis in_mono subgroup_of_restricted_group)
  with assms(1) \<open>subgroup H G\<close> have "inv\<^bsub>G\<lparr> carrier := H\<rparr>\<^esub> x = inv x" by (rule group.m_inv_consistent)
  ultimately show "inv x \<in> U" by simp
qed

text \<open>Being a subgroup is preserved by surjective homomorphisms\<close>

lemma (in subgroup) surj_hom_subgroup:
  assumes \<phi>:"group_hom G F \<phi>"
  assumes \<phi>surj:"\<phi> ` (carrier G) = carrier F"
  shows "subgroup (\<phi> ` H) F"
proof
  from \<phi>surj show img_subset:"\<phi> ` H \<subseteq> carrier F" unfolding iso_def bij_betw_def by auto
next
  fix f f'
  assume h:"f \<in> \<phi> ` H" and h':"f' \<in> \<phi> ` H"
  with \<phi>surj obtain g g' where g:"g \<in> H" "f = \<phi> g" and g':"g' \<in> H" "f' = \<phi> g'" by auto
  hence "g \<otimes>\<^bsub>G\<^esub> g' \<in> H" by (metis m_closed)
  hence "\<phi> (g \<otimes>\<^bsub>G\<^esub> g') \<in> \<phi> ` H" by simp
  with g g' \<phi> show "f \<otimes>\<^bsub>F\<^esub> f' \<in> \<phi> ` H"  using group_hom.hom_mult by fastforce
next
  have "\<phi> \<one> \<in> \<phi> ` H" by auto
  with \<phi> show  "\<one>\<^bsub>F\<^esub> \<in> \<phi> ` H" by (metis group_hom.hom_one)
next
  fix f
  assume f:"f \<in> \<phi> ` H"
  then obtain g where g:"g \<in> H" "f = \<phi> g" by auto
  hence "inv g \<in> H" by auto
  hence "\<phi> (inv g) \<in> \<phi> ` H" by auto
  with \<phi> g subset show "inv\<^bsub>F\<^esub> f \<in> \<phi> ` H" using group_hom.hom_inv by fastforce
qed

text \<open>... and thus of course by isomorphisms of groups.\<close>

lemma iso_subgroup:
  assumes groups:"group G" "group F"
  assumes HG:"subgroup H G"
  assumes \<phi>:"\<phi> \<in> iso G F"
  shows "subgroup (\<phi> ` H) F"
proof -
  from groups \<phi> have "group_hom G F \<phi>" unfolding group_hom_def group_hom_axioms_def iso_def by auto
  moreover from \<phi> have "\<phi> ` (carrier G) = carrier F" unfolding iso_def bij_betw_def by simp
  moreover note HG
  ultimately show ?thesis by (metis subgroup.surj_hom_subgroup)
qed

text \<open>An isomorphism restricts to an isomorphism of subgroups.\<close>

lemma iso_restrict:
  assumes groups:"group G" "group F"
  assumes HG:"subgroup H G"
  assumes \<phi>:"\<phi> \<in> iso G F"
  shows "(restrict \<phi> H) \<in> iso (G\<lparr>carrier := H\<rparr>) (F\<lparr>carrier := \<phi> ` H\<rparr>)"
unfolding iso_def hom_def bij_betw_def inj_on_def
proof auto
  fix g h
  assume "g \<in> H" "h \<in> H"
  hence "g \<in> carrier G" "h \<in> carrier G" by (metis HG subgroup.mem_carrier)+
  thus "\<phi> (g \<otimes>\<^bsub>G\<^esub> h) = \<phi> g \<otimes>\<^bsub>F\<^esub> \<phi> h" using \<phi> unfolding iso_def hom_def by auto
next
  fix g h
  assume "g \<in> H" "h \<in> H" "g \<otimes>\<^bsub>G\<^esub> h \<notin> H"
  hence "False" using HG unfolding subgroup_def by auto
  thus "undefined = \<phi> g \<otimes>\<^bsub>F\<^esub> \<phi> h" by auto
next
  fix g h
  assume g:"g \<in> H" and h:"h \<in> H" and eq:"\<phi> g = \<phi> h"
  hence "g \<in> carrier G" "h \<in> carrier G" by (metis HG subgroup.mem_carrier)+
  with eq show "g = h" using \<phi> unfolding iso_def bij_betw_def inj_on_def by auto
qed

text \<open>The intersection of two subgroups is, again, a subgroup\<close>

lemma (in group) subgroup_intersect:
  assumes "subgroup H G"
  assumes "subgroup H' G"
  shows "subgroup (H \<inter> H') G"
using assms unfolding subgroup_def by auto

section \<open>Facts about Normal Subgroups\<close>

lemma (in normal) is_normal:
  shows "H \<lhd> G"
by (metis coset_eq is_subgroup normalI)

text \<open>Being a normal subgroup is preserved by surjective homomorphisms.\<close>

lemma (in normal) surj_hom_normal_subgroup:
  assumes \<phi>:"group_hom G F \<phi>"
  assumes \<phi>surj:"\<phi> ` (carrier G) = carrier F"
  shows "(\<phi> ` H) \<lhd> F"
proof (rule group.normalI)
  from \<phi> show "group F" unfolding group_hom_def group_hom_axioms_def by simp
next
  from \<phi> \<phi>surj show "subgroup (\<phi> ` H) F" by (rule surj_hom_subgroup)
next
  show "\<forall>x\<in>carrier F. \<phi> ` H #>\<^bsub>F\<^esub> x = x <#\<^bsub>F\<^esub> \<phi> ` H"
  proof
    fix f
    assume f:"f \<in> carrier F"
    with \<phi>surj obtain g where g:"g \<in> carrier G" "f = \<phi> g" by auto
    hence "\<phi> ` H #>\<^bsub>F\<^esub> f = \<phi> ` H #>\<^bsub>F\<^esub> \<phi> g" by simp
    also have "... = (\<lambda>x. (\<phi> x) \<otimes>\<^bsub>F\<^esub> (\<phi> g)) ` H" unfolding r_coset_def image_def by auto
    also have "... = (\<lambda>x. \<phi> (x \<otimes> g)) ` H" using subset g \<phi> group_hom.hom_mult unfolding image_def by fastforce
    also have "... = \<phi> ` (H #> g)" using \<phi> unfolding r_coset_def by auto
    also have "... = \<phi> ` (g <# H)" by (metis coset_eq g(1))
    also have "... = (\<lambda>x. \<phi> (g \<otimes> x)) ` H" using \<phi> unfolding l_coset_def by auto
    also have "... = (\<lambda>x. (\<phi> g) \<otimes>\<^bsub>F\<^esub> (\<phi> x)) ` H" using subset g \<phi> group_hom.hom_mult by fastforce
    also have "... = \<phi> g <#\<^bsub>F\<^esub> \<phi> ` H" unfolding l_coset_def image_def by auto
    also have "... = f <#\<^bsub>F\<^esub> \<phi> ` H" using g by simp
    finally show "\<phi> ` H #>\<^bsub>F\<^esub> f = f <#\<^bsub>F\<^esub> \<phi> ` H".
  qed
qed

text \<open>Being a normal subgroup is preserved by group isomorphisms.\<close>

lemma iso_normal_subgroup:
  assumes groups:"group G" "group F"
  assumes HG:"H \<lhd> G"
  assumes \<phi>:"\<phi> \<in> iso G F"
  shows "(\<phi> ` H) \<lhd> F"
proof -
  from groups \<phi> have "group_hom G F \<phi>" unfolding group_hom_def group_hom_axioms_def iso_def by auto
  moreover from \<phi> have "\<phi> ` (carrier G) = carrier F" unfolding iso_def bij_betw_def by simp
  moreover note HG
  ultimately show ?thesis using normal.surj_hom_normal_subgroup by metis
qed

text \<open>The trivial subgroup is a subgroup:\<close>

lemma (in group) triv_subgroup:
  shows "subgroup {\<one>} G"
unfolding subgroup_def by auto

text \<open>The cardinality of the right cosets of the trivial subgroup is the cardinality of the group itself:\<close>

lemma (in group) card_rcosets_triv:
  assumes "finite (carrier G)"
  shows "card (rcosets {\<one>}) = order G"
proof -
  have "subgroup {\<one>} G" by (rule triv_subgroup)
  with assms have "card (rcosets {\<one>}) * card {\<one>} = order G"
    using lagrange by blast
  thus ?thesis by (auto simp:card_Suc_eq)
qed

text \<open>The intersection of two normal subgroups is, again, a normal subgroup.\<close>

lemma (in group) normal_subgroup_intersect:
  assumes "M \<lhd> G" and "N \<lhd> G"
  shows "M \<inter> N \<lhd> G"
using assms subgroup_intersect is_group normal_inv_iff by simp

text \<open>The set product of two normal subgroups is a normal subgroup.\<close>

lemma (in group) setmult_lcos_assoc:
     "\<lbrakk>H \<subseteq> carrier G; K \<subseteq> carrier G; x \<in> carrier G\<rbrakk>
      \<Longrightarrow> (x <# H) <#> K = x <# (H <#> K)"
by (force simp add: l_coset_def set_mult_def m_assoc)

lemma (in group) normal_subgroup_set_mult_closed:
  assumes "M \<lhd> G" and "N \<lhd> G"
  shows "M <#> N \<lhd> G"
proof (rule normalI)
  from assms show "subgroup (M <#> N) G"
    using second_isomorphism_grp.normal_set_mult_subgroup normal_imp_subgroup
    unfolding second_isomorphism_grp_def second_isomorphism_grp_axioms_def by force
next
  show "\<forall>x\<in>carrier G. M <#> N #> x = x <# (M <#> N)"
  proof
    fix x
    assume x:"x \<in> carrier G"
    have "M <#> N #> x = M <#> (N #> x)" by (metis assms(1,2) normal_inv_iff setmult_rcos_assoc subgroup.subset x)
    also have "\<dots> = M <#> (x <# N)" by (metis assms(2) normal.coset_eq x)
    also have "\<dots> = (M #> x) <#> N" by (metis assms(1,2) normal_imp_subgroup rcos_assoc_lcos subgroup.subset x)
    also have "\<dots> = (x <# M) <#> N" by (metis assms(1) normal.coset_eq x)
    also have "\<dots> = x <# (M <#> N)" by (metis assms(1,2) normal_imp_subgroup setmult_lcos_assoc subgroup.subset x)
    finally show "M <#> N #> x = x <# (M <#> N)".
  qed
qed

text \<open>The following is a very basic lemma about subgroups: If restricting the carrier of
  a group yields a group it's a subgroup of the group we've started with.\<close>

lemma (in group) restrict_group_imp_subgroup:
  assumes "H \<subseteq> carrier G" "group (G\<lparr>carrier := H\<rparr>)"
  shows "subgroup H G"
proof
  from assms(1) show "H \<subseteq> carrier G" .
next
  fix x y
  assume "x \<in> H" "y \<in> H"
  hence "x \<in> carrier (G\<lparr>carrier := H\<rparr>)" "y \<in> carrier (G\<lparr>carrier := H\<rparr>)" by auto
  with assms(2) show "x \<otimes> y \<in> H" using assms(2) group.is_monoid monoid.m_closed by fastforce
next
  show "\<one> \<in> H" using assms(2) group.is_monoid monoid.one_closed by fastforce
next
  fix x
  assume "x \<in> H"
  hence x:"x \<in> carrier (G\<lparr>carrier := H\<rparr>)" by auto
  hence "inv\<^bsub>G\<lparr>carrier := H\<rparr>\<^esub> x \<in> carrier (G\<lparr>carrier := H\<rparr>)" using assms(2) group.inv_closed by fastforce
  hence "inv\<^bsub>G\<lparr>carrier := H\<rparr>\<^esub> x \<in> carrier G" using x assms(1) by auto
  moreover have "inv\<^bsub>G\<lparr>carrier := H\<rparr>\<^esub> x \<otimes> x = \<one>" using assms(2) group.l_inv x by fastforce
  moreover have "x \<in> carrier G" using x assms(1) by auto
  ultimately have "inv\<^bsub>G\<lparr>carrier := H\<rparr>\<^esub> x = inv x" using inv_equality[symmetric] by auto
  thus "inv x \<in> H" using assms(2) group.inv_closed x by fastforce
qed

text \<open>A subgroup relation survives factoring by a normal subgroup.\<close>

lemma (in group) normal_subgroup_factorize:
  assumes "N \<lhd> G" and "N \<subseteq> H" and "subgroup H G"
  shows "subgroup (rcosets\<^bsub>G\<lparr>carrier := H\<rparr>\<^esub> N) (G Mod N)"
proof -
  interpret GModN: group "G Mod N" using assms(1) by (rule normal.factorgroup_is_group)
  have "N \<lhd> G\<lparr>carrier := H\<rparr>" using assms by (metis normal_restrict_supergroup)
  hence grpHN:"group (G\<lparr>carrier := H\<rparr> Mod N)" by (rule normal.factorgroup_is_group)
  have "(<#>\<^bsub>G\<lparr>carrier:=H\<rparr>\<^esub>) = (\<lambda>U K. (\<Union>h\<in>U. \<Union>k\<in>K. {h \<otimes>\<^bsub>G\<lparr>carrier := H\<rparr>\<^esub> k}))" using set_mult_def by metis
  moreover have "\<dots> = (\<lambda>U K. (\<Union>h\<in>U. \<Union>k\<in>K. {h \<otimes>\<^bsub>G\<^esub> k}))" by auto
  moreover have "(<#>) = (\<lambda>U K. (\<Union>h\<in>U. \<Union>k\<in>K. {h \<otimes> k}))" using set_mult_def by metis
  ultimately have "(<#>\<^bsub>G\<lparr>carrier:=H\<rparr>\<^esub>) = (<#>\<^bsub>G\<^esub>)" by simp
  with grpHN have "group ((G Mod N)\<lparr>carrier := (rcosets\<^bsub>G\<lparr>carrier := H\<rparr>\<^esub> N)\<rparr>)" unfolding FactGroup_def by auto
  moreover have "rcosets\<^bsub>G\<lparr>carrier := H\<rparr>\<^esub> N \<subseteq> carrier (G Mod N)" unfolding FactGroup_def RCOSETS_def r_coset_def
    using assms(3) subgroup.subset by fastforce
  ultimately show ?thesis using GModN.is_group group.restrict_group_imp_subgroup by auto
qed

text \<open>A normality relation survives factoring by a normal subgroup.\<close>

lemma (in group) normality_factorization:
  assumes NG:"N \<lhd> G" and NH:"N \<subseteq> H" and HG:"H \<lhd> G"
  shows "(rcosets\<^bsub>G\<lparr>carrier := H\<rparr>\<^esub> N) \<lhd> (G Mod N)"
proof -
  from assms(1) interpret GModN: group "G Mod N" by (metis normal.factorgroup_is_group)
  show ?thesis
  proof (auto simp: GModN.normal_inv_iff)
    from assms show "subgroup (rcosets\<^bsub>G\<lparr>carrier := H\<rparr>\<^esub> N) (G Mod N)" using normal_imp_subgroup normal_subgroup_factorize by force
  next
    fix U V
    assume U:"U \<in> carrier (G Mod N)" and V:"V \<in> rcosets\<^bsub>G\<lparr>carrier := H\<rparr>\<^esub> N"
    then obtain g where g:"g \<in> carrier G" "U = N #> g" unfolding FactGroup_def RCOSETS_def by auto
    from V obtain h where h:"h \<in> H" "V = N #> h" unfolding FactGroup_def RCOSETS_def r_coset_def by auto
    hence hG:"h \<in> carrier G" using HG normal_imp_subgroup subgroup.mem_carrier by force
    hence ghG:"g \<otimes> h \<in> carrier G" using g m_closed by auto
    from g h have "g \<otimes> h \<otimes> inv g \<in> H" using HG normal_inv_iff by auto
    moreover have "U <#> V <#> inv\<^bsub>G Mod N\<^esub> U = N #> (g \<otimes> h \<otimes> inv g)"
    proof -
      from g U have "inv\<^bsub>G Mod N\<^esub> U = N #> inv g" using NG normal.inv_FactGroup normal.rcos_inv by fastforce
      hence "U <#> V <#> inv\<^bsub>G Mod N\<^esub> U = (N #> g) <#> (N #> h) <#> (N #> inv g)" using g h by simp
      also have "\<dots> = N #> (g \<otimes> h) <#> (N #> inv g)" using g hG NG normal.rcos_sum by force
      also have "\<dots> = N #> (g \<otimes> h \<otimes> inv g)" using g inv_closed ghG NG normal.rcos_sum by force
      finally show ?thesis .
    qed
    ultimately show "U <#> V <#> inv\<^bsub>G Mod N\<^esub> U \<in> rcosets\<^bsub>G\<lparr>carrier := H\<rparr>\<^esub> N" unfolding RCOSETS_def r_coset_def by auto
  qed
qed

text \<open>Factoring by a normal subgroups yields the trivial group iff the subgroup is the whole group.\<close>

lemma (in normal) fact_group_trivial_iff:
  assumes "finite (carrier G)"
  shows "(carrier (G Mod H) = {\<one>\<^bsub>G Mod H\<^esub>}) = (H = carrier G)"
proof
  assume "carrier (G Mod H) = {\<one>\<^bsub>G Mod H\<^esub>}"
  moreover with assms lagrange have "order (G Mod H) * card H = order G" unfolding FactGroup_def order_def using is_subgroup by force
  ultimately have "card H = order G" unfolding order_def by auto
  thus "H = carrier G" using subgroup.subset is_subgroup assms card_subset_eq unfolding order_def
    by metis
next
  from assms have ordergt0:"order G > 0" unfolding order_def by (metis subgroup.finite_imp_card_positive subgroup_self)
  assume "H = carrier G"
  hence "card H = order G" unfolding order_def by simp
  with assms is_subgroup lagrange have "card (rcosets H) * order G = order G" by metis
  with ordergt0 have "card (rcosets H) = 1" by (metis mult_eq_self_implies_10 mult.commute neq0_conv)
  hence "order (G Mod H) = 1" unfolding order_def FactGroup_def by auto
  thus "carrier (G Mod H) = {\<one>\<^bsub>G Mod H\<^esub>}" using factorgroup_is_group by (metis group.order_one_triv_iff)
qed

text \<open>Finite groups have finite quotients.\<close>

lemma (in normal) factgroup_finite:
  assumes "finite (carrier G)"
  shows "finite (rcosets H)"
using assms unfolding RCOSETS_def by auto

text \<open>The union of all the cosets contained in a subgroup of a quotient group acts as a represenation for that subgroup.\<close>

lemma (in normal) factgroup_subgroup_union_char:
  assumes "subgroup A (G Mod H)"
  shows "(\<Union>A) = {x \<in> carrier G. H #> x \<in> A}"
proof
  show "\<Union>A \<subseteq> {x \<in> carrier G. H #> x \<in> A}"
  proof
    fix x
    assume x:"x \<in> \<Union>A"
    then obtain a where a:"a \<in> A" "x \<in> a" by auto
    with assms have xx:"x \<in> carrier G" using subgroup.subset unfolding FactGroup_def RCOSETS_def r_coset_def by force
    from assms a obtain y where y:"y \<in> carrier G" "a = H #> y" using subgroup.subset unfolding FactGroup_def RCOSETS_def by force
    with a have "x \<in> H #> y" by simp
    hence "H #> y = H #> x" using y is_subgroup repr_independence by auto
    with y(2) a(1) have "H #> x \<in> A" by auto
    with xx show "x \<in> {x \<in> carrier G. H #> x \<in> A}" by simp
  qed
next
  show "{x \<in> carrier G. H #> x \<in> A} \<subseteq> \<Union>A"
  proof
    fix x
    assume x:"x \<in> {x \<in> carrier G. H #> x \<in> A}"
    hence xx:"x \<in> carrier G" "H #> x \<in> A" by auto
    moreover have "x \<in> H #> x" by (metis is_subgroup rcos_self xx(1))
    ultimately show "x \<in> \<Union>A" by auto
  qed
qed

lemma (in normal) factgroup_subgroup_union_subgroup:
  assumes "subgroup A (G Mod H)"
  shows "subgroup (\<Union>A) G"
proof -
  have "subgroup {x \<in> carrier G. H #> x \<in> A} G"
  proof
    show "{x \<in> carrier G. H #> x \<in> A} \<subseteq> carrier G" by auto
  next
    fix x y
    assume "x \<in> {x \<in> carrier G. H #> x \<in> A}" and "y \<in> {x \<in> carrier G. H #> x \<in> A}"
    hence x:"x \<in> carrier G" "H #> x \<in> A" and y:"y \<in> carrier G" "H #> y \<in> A" by auto
    hence xyG:"x \<otimes> y \<in> carrier G" by (metis m_closed)
    from assms x y have "(H #> x) <#> (H #> y) \<in> A" using subgroup.m_closed unfolding FactGroup_def by fastforce
    hence "H #> (x \<otimes> y) \<in> A" by (metis rcos_sum x(1) y(1))
    with xyG show "x \<otimes> y \<in> {x \<in> carrier G. H #> x \<in> A}" by simp
  next
    have "H #> \<one> \<in> A" using assms subgroup.one_closed unfolding FactGroup_def by (metis coset_mult_one monoid.select_convs(2) subset)
    with assms one_closed show "\<one> \<in> {x \<in> carrier G. H #> x \<in> A}" by simp
  next
    fix x
    assume "x \<in> {x \<in> carrier G. H #> x \<in> A}"
    hence x:"x \<in> carrier G" "H #> x \<in> A" by auto
    hence invx:"inv x \<in> carrier G" using inv_closed by simp
    from assms x have "set_inv (H #> x) \<in> A" using subgroup.m_inv_closed by (metis inv_FactGroup subgroup.mem_carrier)
    hence "H #> (inv x) \<in> A" by (metis rcos_inv x(1))
    with invx show "inv x \<in> {x \<in> carrier G. H #> x \<in> A}" by simp
  qed
  with assms factgroup_subgroup_union_char show ?thesis by auto
qed

lemma (in normal) factgroup_subgroup_union_normal:
  assumes "A \<lhd> (G Mod H)"
  shows "\<Union>A \<lhd> G"
proof - 
  have "{x \<in> carrier G. H #> x \<in> A} \<lhd> G"
  unfolding normal_def normal_axioms_def
  proof auto (*(auto del: equalityI)*)
    from assms show "subgroup {x \<in> carrier G. H #> x \<in> A} G"
      by (metis (full_types) factgroup_subgroup_union_char factgroup_subgroup_union_subgroup normal_imp_subgroup)
  next
    interpret Anormal: normal A "(G Mod H)" using assms by simp
    fix x y
    assume x:"x \<in> carrier G" "y \<in> {x \<in> carrier G. H #> x \<in> A} #> x"
    then obtain x' where "x' \<in> {x \<in> carrier G. H #> x \<in> A}" "y = x' \<otimes> x" unfolding r_coset_def by auto
    hence x':"x' \<in> carrier G" "H #> x' \<in> A" by auto
    from x(1) have Hx:"H #> x \<in> carrier (G Mod H)" unfolding FactGroup_def RCOSETS_def by force
    with x' have "(inv\<^bsub>G Mod H\<^esub> (H #> x)) \<otimes>\<^bsub>G Mod H\<^esub> (H #> x') \<otimes>\<^bsub>G Mod H\<^esub> (H #> x) \<in> A" using Anormal.inv_op_closed1 by auto
    hence "(set_inv (H #> x)) <#> (H #> x') <#> (H #> x) \<in> A" using inv_FactGroup Hx unfolding FactGroup_def by auto
    hence "(H #> (inv x)) <#> (H #> x') <#> (H #> x) \<in> A" using x(1) by (metis rcos_inv)
    hence "(H #> (inv x \<otimes> x')) <#> (H #> x) \<in> A" by (metis inv_closed rcos_sum x'(1) x(1))
    hence "H #> (inv x \<otimes> x' \<otimes> x) \<in> A" by (metis inv_closed m_closed rcos_sum x'(1) x(1))
    moreover have "inv x \<otimes> x' \<otimes> x \<in> carrier G" using x x' by (metis inv_closed m_closed)
    ultimately have "inv x \<otimes> x' \<otimes> x \<in> {x \<in> carrier G. H #> x \<in> A}" by auto
    hence xcoset:"x \<otimes> (inv x \<otimes> x' \<otimes> x) \<in> x <# {x \<in> carrier G. H #> x \<in> A}" unfolding l_coset_def using x(1) by auto
    have "x \<otimes> (inv x \<otimes> x' \<otimes> x) = (x \<otimes> inv x) \<otimes> x' \<otimes> x" by (metis Units_eq Units_inv_Units m_assoc m_closed x'(1) x(1))
    also have "\<dots> = x' \<otimes> x" by (metis l_one r_inv x'(1) x(1))
    also have "\<dots> = y" by (metis \<open>y = x' \<otimes> x\<close>)
    finally have "x \<otimes> (inv x \<otimes> x' \<otimes> x) = y".
    with xcoset show "y \<in> x <# {x \<in> carrier G. H #> x \<in> A}" by auto
  next
    interpret Anormal: normal A "(G Mod H)" using assms by simp
    fix x y
    assume x:"x \<in> carrier G" "y \<in> x <# {x \<in> carrier G. H #> x \<in> A}"
    then obtain x' where "x' \<in> {x \<in> carrier G. H #> x \<in> A}" "y = x \<otimes> x'" unfolding l_coset_def by auto
    hence x':"x' \<in> carrier G" "H #> x' \<in> A" by auto
    from x(1) have invx:"inv x \<in> carrier G" by (rule inv_closed)
    hence Hinvx:"H #> (inv x) \<in> carrier (G Mod H)" unfolding FactGroup_def RCOSETS_def by force
    with x' have "(inv\<^bsub>G Mod H\<^esub> (H #> inv x)) \<otimes>\<^bsub>G Mod H\<^esub> (H #> x') \<otimes>\<^bsub>G Mod H\<^esub> (H #> inv x) \<in> A" using invx Anormal.inv_op_closed1 by auto
    hence "(set_inv (H #> inv x)) <#> (H #> x') <#> (H #> inv x) \<in> A" using inv_FactGroup Hinvx unfolding FactGroup_def by auto
    hence "(H #> inv (inv x)) <#> (H #> x') <#> (H #> inv x) \<in> A" using invx by (metis rcos_inv)
    hence "(H #> x) <#> (H #> x') <#> (H #> inv x) \<in> A" by (metis inv_inv x(1))
    hence "(H #> (x \<otimes> x')) <#> (H #> inv x) \<in> A" by (metis rcos_sum x'(1) x(1))
    hence "H #> (x \<otimes> x' \<otimes> inv x) \<in> A" by (metis inv_closed m_closed rcos_sum x'(1) x(1))
    moreover have "x \<otimes> x' \<otimes> inv x \<in> carrier G" using x x' by (metis inv_closed m_closed)
    ultimately have "x \<otimes> x' \<otimes> inv x \<in> {x \<in> carrier G. H #> x \<in> A}" by auto
    hence xcoset:"(x \<otimes> x' \<otimes> inv x) \<otimes> x \<in> {x \<in> carrier G. H #> x \<in> A} #> x" unfolding r_coset_def using invx by auto
    have "(x \<otimes> x' \<otimes> inv x) \<otimes> x = (x \<otimes> x') \<otimes> (inv x \<otimes> x)" by (metis Units_eq Units_inv_Units m_assoc m_closed x'(1) x(1))
    also have "\<dots> = x \<otimes> x'" using x(1) l_inv x'(1) m_closed r_one by auto
    also have "\<dots> = y" by (metis \<open>y = x \<otimes> x'\<close>)
    finally have "x \<otimes> x' \<otimes> inv x \<otimes> x = y".
    with xcoset show "y \<in> {x \<in> carrier G. H #> x \<in> A} #> x" by auto
  qed
  with assms show ?thesis by (metis (full_types) factgroup_subgroup_union_char normal_imp_subgroup)
qed

lemma (in normal) factgroup_subgroup_union_factor:
  assumes "subgroup A (G Mod H)"
  shows "A = rcosets\<^bsub>G\<lparr>carrier := \<Union>A\<rparr>\<^esub> H"
proof -
  have "A = rcosets\<^bsub>G\<lparr>carrier := {x \<in> carrier G. H #> x \<in> A}\<rparr>\<^esub> H"
  proof auto
    fix U
    assume U:"U \<in> A"
    then obtain x' where x':"x' \<in> carrier G" "U = H #> x'" using assms subgroup.subset unfolding FactGroup_def RCOSETS_def by force
    with U have "H #> x' \<in> A" by simp
    with x' show "U \<in> rcosets\<^bsub>G\<lparr>carrier := {x \<in> carrier G. H #> x \<in> A}\<rparr>\<^esub> H" unfolding RCOSETS_def r_coset_def by auto
  next
    fix U
    assume U:"U \<in> rcosets\<^bsub>G\<lparr>carrier := {x \<in> carrier G. H #> x \<in> A}\<rparr>\<^esub> H"
    then obtain x' where x':"x' \<in> {x \<in> carrier G. H #> x \<in> A}" "U = H #> x'" unfolding RCOSETS_def r_coset_def by auto
    hence "x' \<in> carrier G" "H #> x' \<in> A" by auto
    with x' show "U \<in> A" by simp
  qed
  with assms show ?thesis using factgroup_subgroup_union_char by auto
qed


section  \<open>Flattening the type of group carriers\<close>

text \<open>Flattening here means to convert the type of group elements from 'a set to 'a.
This is possible whenever the empty set is not an element of the group.\<close>


definition flatten where
  "flatten (G::('a set, 'b) monoid_scheme) rep = \<lparr>carrier=(rep ` (carrier G)),
      monoid.mult=(\<lambda> x y. rep ((the_inv_into (carrier G) rep x) \<otimes>\<^bsub>G\<^esub> (the_inv_into (carrier G) rep y))), 
      one=rep \<one>\<^bsub>G\<^esub> \<rparr>"

lemma flatten_set_group_hom:
  assumes group:"group G"
  assumes inj:"inj_on rep (carrier G)"
  shows "rep \<in> hom G (flatten G rep)"
unfolding hom_def
proof auto
  fix g
  assume g:"g \<in> carrier G"
  thus "rep g \<in> carrier (flatten G rep)" unfolding flatten_def by auto
next
  fix g h
  assume g:"g \<in> carrier G" and h:"h \<in> carrier G"
  hence "rep g \<in> carrier (flatten G rep)" "rep h \<in> carrier (flatten G rep)" unfolding flatten_def by auto
  hence "rep g \<otimes>\<^bsub>flatten G rep\<^esub> rep h
    = rep (the_inv_into (carrier G) rep (rep g) \<otimes>\<^bsub>G\<^esub> the_inv_into (carrier G) rep (rep h))" unfolding flatten_def by auto
  also have "\<dots> = rep (g \<otimes>\<^bsub>G\<^esub> h)" using inj g h by (metis the_inv_into_f_f)
  finally show "rep (g \<otimes>\<^bsub>G\<^esub> h) = rep g \<otimes>\<^bsub>flatten G rep\<^esub> rep h"..
qed

lemma flatten_set_group:
  assumes group:"group G"
  assumes inj:"inj_on rep (carrier G)"
  shows "group (flatten G rep)"
proof (rule groupI)
  fix x y
  assume x:"x \<in> carrier (flatten G rep)" and y:"y \<in> carrier (flatten G rep)"
  define g h
    where "g = the_inv_into (carrier G) rep x"
      and "h = the_inv_into (carrier G) rep y"
  hence "x \<otimes>\<^bsub>flatten G rep\<^esub> y = rep (g \<otimes>\<^bsub>G\<^esub> h)" unfolding flatten_def by auto
  moreover from g_def h_def have "g \<in> carrier G" "h \<in> carrier G" 
    using inj x y the_inv_into_into unfolding flatten_def by (metis partial_object.select_convs(1) subset_refl)+
  hence "g \<otimes>\<^bsub>G\<^esub> h \<in> carrier G" by (metis group group.is_monoid monoid.m_closed)
  hence "rep (g \<otimes>\<^bsub>G\<^esub> h) \<in> carrier (flatten G rep)" unfolding flatten_def by simp
  ultimately show "x \<otimes>\<^bsub>flatten G rep\<^esub> y \<in> carrier (flatten G rep)" by simp
next
  show "\<one>\<^bsub>flatten G rep\<^esub> \<in> carrier (flatten G rep)" unfolding flatten_def by (simp add: group group.is_monoid)
next
  fix x y z
  assume x:"x \<in> carrier (flatten G rep)" and y:"y \<in> carrier (flatten G rep)" and z:"z \<in> carrier (flatten G rep)"
  define g h k
    where "g = the_inv_into (carrier G) rep x"
      and "h = the_inv_into (carrier G) rep y"
      and "k = the_inv_into (carrier G) rep z"
  hence "x \<otimes>\<^bsub>flatten G rep\<^esub> y \<otimes>\<^bsub>flatten G rep\<^esub> z = (rep (g \<otimes>\<^bsub>G\<^esub> h)) \<otimes> \<^bsub>flatten G rep\<^esub> z" unfolding flatten_def by auto
  also have "\<dots> = rep (the_inv_into (carrier G) rep (rep (g \<otimes>\<^bsub>G\<^esub> h)) \<otimes>\<^bsub>G\<^esub> k)" using k_def unfolding flatten_def by auto
  also from g_def h_def k_def have ghkG:"g \<in> carrier G" "h \<in> carrier G" "k \<in> carrier G"
    using inj x y z the_inv_into_into unfolding flatten_def by fastforce+
  hence gh:"g \<otimes>\<^bsub>G\<^esub> h \<in> carrier G" and hk:"h \<otimes>\<^bsub>G\<^esub> k \<in> carrier G" by (metis group group.is_monoid monoid.m_closed)+
  hence "rep (the_inv_into (carrier G) rep (rep (g \<otimes>\<^bsub>G\<^esub> h)) \<otimes>\<^bsub>G\<^esub> k) = rep ((g \<otimes>\<^bsub>G\<^esub> h) \<otimes>\<^bsub>G\<^esub> k)"
    unfolding flatten_def using inj the_inv_into_f_f by fastforce
  also have "\<dots> = rep (g \<otimes>\<^bsub>G\<^esub> (h \<otimes>\<^bsub>G\<^esub> k))" using group group.is_monoid ghkG monoid.m_assoc by fastforce
  also have "\<dots> = x \<otimes>\<^bsub>flatten G rep\<^esub> (rep (h \<otimes>\<^bsub>G\<^esub> k))" unfolding g_def flatten_def using hk inj the_inv_into_f_f by fastforce
  also have "\<dots> = x \<otimes>\<^bsub>flatten G rep\<^esub> (y \<otimes>\<^bsub>flatten G rep\<^esub> z)" unfolding h_def k_def flatten_def using x y by force
  finally show "x \<otimes>\<^bsub>flatten G rep\<^esub> y \<otimes>\<^bsub>flatten G rep\<^esub> z = x \<otimes>\<^bsub>flatten G rep\<^esub> (y \<otimes>\<^bsub>flatten G rep\<^esub> z)".
next
  fix x
  assume x:"x \<in> carrier (flatten G rep)"
  define g where "g = the_inv_into (carrier G) rep x"
  hence gG:"g \<in> carrier G" using inj x unfolding flatten_def using the_inv_into_into by force
  have "\<one>\<^bsub>G\<^esub> \<in> (carrier G)" by (simp add: group group.is_monoid)
  hence "the_inv_into (carrier G) rep (\<one>\<^bsub>flatten G rep\<^esub>) = \<one>\<^bsub>G\<^esub>" unfolding flatten_def using the_inv_into_f_f inj by force
  hence "\<one>\<^bsub>flatten G rep\<^esub> \<otimes>\<^bsub>flatten G rep\<^esub> x = rep (\<one>\<^bsub>G\<^esub> \<otimes>\<^bsub>G\<^esub> g)" unfolding flatten_def g_def by simp
  also have "\<dots> = rep g" using gG group by (metis group.is_monoid monoid.l_one)
  also have "\<dots> = x" unfolding g_def using inj x f_the_inv_into_f unfolding flatten_def by force
  finally show "\<one>\<^bsub>flatten G rep\<^esub> \<otimes>\<^bsub>flatten G rep\<^esub> x = x".
next
  from group inj have hom:"rep \<in> hom G (flatten G rep)" using flatten_set_group_hom by auto
  fix x
  assume x:"x \<in> carrier (flatten G rep)"
  define g where "g = the_inv_into (carrier G) rep x"
  hence gG:"g \<in> carrier G" using inj x unfolding flatten_def using the_inv_into_into by force
  hence invG:"inv\<^bsub>G\<^esub> g \<in> carrier G" by (metis group group.inv_closed)
  hence "rep (inv\<^bsub>G\<^esub> g) \<in> carrier (flatten G rep)" unfolding flatten_def by auto
  moreover have "rep (inv\<^bsub>G\<^esub> g) \<otimes>\<^bsub>flatten G rep\<^esub> x = rep (inv\<^bsub>G\<^esub> g) \<otimes>\<^bsub>flatten G rep\<^esub> (rep g)"
    unfolding g_def using f_the_inv_into_f inj x unfolding flatten_def by fastforce
  hence "rep (inv\<^bsub>G\<^esub> g) \<otimes>\<^bsub>flatten G rep\<^esub> x = rep (inv\<^bsub>G\<^esub> g \<otimes>\<^bsub>G\<^esub> g)"
    using hom unfolding hom_def using gG invG hom_def by auto
  hence "rep (inv\<^bsub>G\<^esub> g) \<otimes>\<^bsub>flatten G rep\<^esub> x = rep \<one>\<^bsub>G\<^esub>" using invG gG by (metis group group.l_inv)
  hence "rep (inv\<^bsub>G\<^esub> g) \<otimes>\<^bsub>flatten G rep\<^esub> x = \<one>\<^bsub>flatten G rep\<^esub>" unfolding flatten_def by auto
  ultimately show "\<exists>y\<in>carrier (flatten G rep). y \<otimes>\<^bsub>flatten G rep\<^esub> x = \<one>\<^bsub>flatten G rep\<^esub>" by auto
qed

lemma (in normal) flatten_set_group_mod_inj:
  shows "inj_on (\<lambda>U. SOME g. g \<in> U) (carrier (G Mod H))"
proof (rule inj_onI)
  fix U V
  assume U:"U \<in> carrier (G Mod H)" and V:"V \<in> carrier (G Mod H)"
  then obtain g h where g:"U = H #> g" "g \<in> carrier G" and h:"V = H #> h" "h \<in> carrier G"
    unfolding FactGroup_def RCOSETS_def by auto
  hence notempty:"U \<noteq> {}" "V \<noteq> {}" by (metis empty_iff is_subgroup rcos_self)+
  assume "(SOME g. g \<in> U) = (SOME g. g \<in> V)"
  with notempty have "(SOME g. g \<in> U) \<in> U \<inter> V" by (metis IntI ex_in_conv someI)
  thus "U = V" by (metis Int_iff g h is_subgroup repr_independence)
qed

lemma (in normal) flatten_set_group_mod:
  shows "group (flatten (G Mod H) (\<lambda>U. SOME g. g \<in> U))"
using factorgroup_is_group flatten_set_group_mod_inj by (rule flatten_set_group)

lemma (in normal) flatten_set_group_mod_iso:
  shows "(\<lambda>U. SOME g. g \<in> U) \<in> iso (G Mod H) (flatten (G Mod H) (\<lambda>U. SOME g. g \<in> U))"
unfolding iso_def bij_betw_def
apply (auto)
 apply (metis flatten_set_group_mod_inj factorgroup_is_group flatten_set_group_hom)
 apply (rule flatten_set_group_mod_inj)
 unfolding flatten_def apply (auto)
done

end
