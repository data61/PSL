(*  Title:      Simple Groups
    Author:     Jakob von Raumer, Karlsruhe Institute of Technology
    Maintainer: Jakob von Raumer <jakob.raumer@student.kit.edu>
*)

theory SimpleGroups
imports
  SubgroupsAndNormalSubgroups
  Secondary_Sylow.SndSylow
  SndIsomorphismGrp
begin

section \<open>Simple Groups\<close>

locale simple_group = group +
  assumes order_gt_one:"order G > 1"
  assumes no_real_normal_subgroup:"\<And>H. H \<lhd> G \<Longrightarrow> (H = carrier G \<or> H = {\<one>})"

lemma (in simple_group) is_simple_group: "simple_group G" by (rule simple_group_axioms)

text \<open>Simple groups are non-trivial.\<close>

lemma (in simple_group) simple_not_triv: "carrier G \<noteq> {\<one>}" using order_gt_one unfolding order_def by auto

text \<open>Every group of prime order is simple\<close>

lemma (in group) prime_order_simple:
  assumes prime:"prime (order G)"
  shows "simple_group G"
proof
  from prime show "1 < order G" unfolding prime_nat_iff by auto
next
  fix H
  assume "H \<lhd> G"
  hence HG:"subgroup H G" unfolding normal_def by simp
  hence "card H dvd order G" by (rule card_subgrp_dvd)
  with prime have "card H = 1 \<or> card H = order G" unfolding prime_nat_iff by simp
  thus "H = carrier G \<or> H = {\<one>}"
  proof
    assume "card H = 1"
    moreover from HG have "\<one> \<in> H" by (metis subgroup.one_closed)
    ultimately show ?thesis by (auto simp: card_Suc_eq)
  next
    assume "card H = order G"
    moreover from HG have "H \<subseteq> carrier G" unfolding subgroup_def by simp
    moreover from prime have "card (carrier G) > 1" unfolding order_def prime_nat_iff ..
    hence "finite (carrier G)" by (auto simp:card_ge_0_finite)
    ultimately show ?thesis unfolding order_def by (metis card_subset_eq)
  qed
qed

text \<open>Being simple is a property that is preserved by isomorphisms.\<close>

lemma (in simple_group) iso_simple:
  assumes H:"group H"
  assumes iso:"\<phi> \<in> iso G H"
  shows "simple_group H"
unfolding simple_group_def simple_group_axioms_def using assms(1)
proof (auto del: equalityI)
  from iso have "order G = order H" unfolding iso_def order_def using bij_betw_same_card by auto
  with order_gt_one show "Suc 0 < order H" by simp
next
  have inv_iso:"(inv_into (carrier G) \<phi>) \<in> iso H G" using iso
    by (simp add: iso_set_sym)    
  fix N
  assume NH:"N \<lhd> H" and Nneq1:"N \<noteq> {\<one>\<^bsub>H\<^esub>}"
  then interpret Nnormal: normal N H by simp
  define M where "M = (inv_into (carrier G) \<phi>) ` N"
  hence MG:"M \<lhd> G" using inv_iso NH H by (metis is_group iso_normal_subgroup)
  have surj:"\<phi> ` carrier G = carrier H" using iso unfolding iso_def bij_betw_def by simp
  hence MN:"\<phi> ` M = N" unfolding M_def using Nnormal.subset image_inv_into_cancel by metis
  moreover have "M \<noteq> {\<one>}"
  proof(rule notI)
    assume "M = {\<one>}"
    hence "\<phi> ` M = {\<phi> \<one>}" by (metis (full_types) image_empty image_insert)
    hence "\<phi> ` M = {\<one>\<^bsub>H\<^esub>}" by (metis (lifting) Nnormal.is_subgroup MN calculation singleton_iff subgroup.one_closed)
    thus False using Nneq1 MN by simp
  qed
  hence "M = carrier G" using no_real_normal_subgroup MG by auto
  ultimately show "N = carrier H" using surj by simp
qed

text \<open>As a corollary of this: Factorizing a group by itself does not result in a simple group!\<close>

lemma (in group) self_factor_not_simple:"\<not> simple_group (G Mod (carrier G))"
proof
  assume assm:"simple_group (G Mod (carrier G))"
  have "group (G\<lparr>carrier :=  {\<one>}\<rparr>)" by (metis subgroup_imp_group triv_subgroup)
  with assm self_factor_iso simple_group.iso_simple have "simple_group (G\<lparr>carrier := {\<one>}\<rparr>)" by auto
  thus "False" using simple_group.simple_not_triv by force
qed

end
