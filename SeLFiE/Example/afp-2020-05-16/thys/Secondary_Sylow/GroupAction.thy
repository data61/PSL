(*  Title:      Group Actions
    Author:     Jakob von Raumer, Karlsruhe Institute of Technology
    Maintainer: Jakob von Raumer <jakob.raumer at student.kit.edu>
*)

theory GroupAction
imports
  "HOL-Algebra.Bij"
  "HOL-Algebra.Sylow"
begin

section \<open>Group Actions\<close>

text \<open>This is an implemention of group actions based on the group
implementation of HOL-Algebra. An action a group $G$ on a set $M$ is
represented by a group homomorphism between $G$ and the group of bijections
on $M$\<close>

subsection \<open>Preliminaries and Definition\<close>

text \<open>First, we need two theorems about singletons and sets of singletons
which unfortunately are not included in the library.\<close>

theorem singleton_intersection:
  assumes A:"card A = 1"
  assumes B:"card B = 1"
  assumes noteq:"A \<noteq> B"
  shows "A \<inter> B = {}"
using assms by(auto simp:card_Suc_eq)

theorem card_singleton_set:
  assumes cardOne:"\<forall>x \<in> A.(card x = 1)"
  shows "card (\<Union>A) = card A"
proof -
  have "card (\<Union>A) = (\<Sum>x\<in>A. card x)"
  proof(rule card_Union_disjoint)
    from cardOne show "\<And>a. a\<in>A \<Longrightarrow> finite a" by (auto intro: card_ge_0_finite)
  next
    show "pairwise disjnt A"
      unfolding pairwise_def disjnt_def
    proof(clarify)
      fix x y
      assume x:"x \<in> A" and y:"y \<in> A" and "x \<noteq> y"
      with cardOne have "card x = 1" "card y = 1" by auto
      with \<open>x \<noteq> y\<close> show "x \<inter> y = {}" by (metis singleton_intersection)
    qed
  qed
  also from cardOne have "... = card A" by simp
  finally show ?thesis.
qed

text \<open>Intersecting Cosets are equal:\<close>

lemma (in subgroup) repr_independence2:
  assumes group:"group G"
  assumes U:"U \<in> rcosets\<^bsub>G\<^esub> H"
  assumes g:"g \<in> U"
  shows "U = H #> g"
proof -
  from U obtain h where h:"h \<in> carrier G" "U = H #> h" unfolding RCOSETS_def by auto
  with g have "g \<in> H #> h" by simp
  with group h show "U = H #> g" by (metis group.repr_independence is_subgroup)
qed

locale group_action = group +
  fixes \<phi> M
  assumes grouphom:"group_hom G (BijGroup M) \<phi>"

context group_action
begin

lemma is_group_action:"group_action G \<phi> M"..

text \<open>The action of @{term "\<one>\<^bsub>G\<^esub>"} has no effect:\<close>

lemma one_is_id:
  assumes "m \<in> M"
  shows "(\<phi> \<one>) m = m"
proof -
  from grouphom have "(\<phi> \<one>) m = \<one>\<^bsub>(BijGroup M)\<^esub> m" by (metis group_hom.hom_one)
  also have "... = (\<lambda>x\<in>M. x) m" unfolding BijGroup_def by (metis monoid.select_convs(2))
  also from assms have "... = m" by simp
  finally show ?thesis.
qed

lemma action_closed:
  assumes m:"m \<in> M"
  assumes g:"g \<in> carrier G"
  shows "\<phi> g m \<in> M"
using assms grouphom group_hom.hom_closed unfolding BijGroup_def Bij_def bij_betw_def by fastforce

lemma img_in_bij:
  assumes "g \<in> carrier G"
  shows "(\<phi> g) \<in> Bij M"
using assms grouphom unfolding BijGroup_def by (auto dest: group_hom.hom_closed)

text \<open>The action of @{term "inv g"} reverts the action of @{term g}\<close>

lemma group_inv_rel:
  assumes g:"g \<in> carrier G"
  assumes mn:"m \<in> M" "n \<in> M"
  assumes phi:"(\<phi> g) n = m"
  shows "(\<phi> (inv g)) m = n"
proof -
  from g have bij:"(\<phi> g) \<in> Bij M" unfolding BijGroup_def by (metis img_in_bij)
  with g grouphom have "\<phi> (inv g) = restrict (inv_into M (\<phi> g)) M" by(metis inv_BijGroup group_hom.hom_inv)
  hence "\<phi> (inv g) m = (restrict (inv_into M (\<phi> g)) M) m" by simp
  also from mn have "... = (inv_into M (\<phi> g)) m" by (metis restrict_def)
  also from g phi have "... = (inv_into M (\<phi> g)) ((\<phi> g) n)" by simp
  also from \<open>\<phi> g \<in> Bij M\<close> Bij_def have "bij_betw (\<phi> g) M M" by auto
  hence "inj_on (\<phi> g) M" by (metis bij_betw_imp_inj_on)
  with g mn have "(inv_into M (\<phi> g)) ((\<phi> g) n) = n" by (metis inv_into_f_f)
  finally show "\<phi> (inv g) m = n".
qed

lemma images_are_bij:
  assumes g:"g \<in> carrier G"
  shows "bij_betw (\<phi> g) M M"
proof -
  from g have bij:"(\<phi> g) \<in> Bij M" unfolding BijGroup_def by (metis img_in_bij)
  with Bij_def show "bij_betw (\<phi> g) M M" by auto
qed

lemma action_mult:
  assumes g:"g \<in> carrier G"
  assumes h:"h \<in> carrier G"
  assumes m:"m \<in> M"
  shows "(\<phi> g) ((\<phi> h) m) = (\<phi> (g \<otimes> h)) m"
proof -
  from g have \<phi>g:"(\<phi> g) \<in> Bij M" unfolding BijGroup_def by (rule img_in_bij)
  from h have \<phi>h:"(\<phi> h) \<in> Bij M" unfolding BijGroup_def by (rule img_in_bij)
  from h have "bij_betw (\<phi> h) M M" by (rule images_are_bij)
  hence "(\<phi> h) ` M = M" by (metis bij_betw_def)
  with m have hm:"(\<phi> h) m \<in> M" by (metis imageI)
  from grouphom g h have "(\<phi> (g \<otimes> h)) = ((\<phi> g) \<otimes>\<^bsub>(BijGroup M)\<^esub> (\<phi> h))" by (rule group_hom.hom_mult)
  hence "\<phi> (g \<otimes> h) m = ((\<phi> g) \<otimes>\<^bsub>(BijGroup M)\<^esub> (\<phi> h)) m" by simp
  also from \<phi>g \<phi>h have "... = (compose M (\<phi> g) (\<phi> h)) m" unfolding BijGroup_def by simp
  also from \<phi>g \<phi>h hm have "... = (\<phi> g) ((\<phi> h) m)" by (metis compose_eq m)
  finally show "(\<phi> g) ((\<phi> h) m) = (\<phi> (g \<otimes> h)) m"..
qed

subsection \<open>The orbit relation\<close>

text \<open>The following describes the relation containing the information
whether two elements of @{term M} lie in the same orbit of the action\<close>

definition same_orbit_rel
  where "same_orbit_rel = {p \<in> M \<times> M. \<exists>g \<in> carrier G. (\<phi> g) (snd p) = (fst p)}"

text \<open>Use the library about equivalence relations to define the set of
orbits and the map assigning to each element of @{term M} its orbit\<close>

definition orbits
 where "orbits = M // same_orbit_rel"

definition orbit :: "'c \<Rightarrow> 'c set"
  where "orbit m = same_orbit_rel `` {m}"

text \<open>Next, we define a more easy-to-use characterization of an orbit.\<close>

lemma orbit_char:
  assumes m:"m \<in> M"
  shows "orbit m = {n. \<exists>g. g \<in> carrier G \<and> (\<phi> g) m = n}"
using assms unfolding orbit_def Image_def same_orbit_rel_def
proof(auto)
  fix x g
  assume g:"g \<in> carrier G" and "\<phi> g x \<in> M" "x \<in> M"
  hence "\<phi> (inv g) (\<phi> g x) = x" by (metis group_inv_rel)
  moreover from g have "inv g \<in> carrier G" by (rule inv_closed)
  ultimately show "\<exists>h. h \<in> carrier G \<and> \<phi> h (\<phi> g x) = x" by auto
next
  fix g
  assume g:"g \<in> carrier G"
  with m show "\<phi> g m \<in> M" by (metis action_closed)
  with m g have "\<phi> (inv g) (\<phi> g m) = m" by (metis group_inv_rel)
  moreover from g have "inv g \<in> carrier G" by (rule inv_closed)
  ultimately show "\<exists>h\<in>carrier G. \<phi> h (\<phi> g m) = m" by auto
qed

lemma same_orbit_char:
  assumes "m \<in> M" "n \<in> M"
  shows "(m, n) \<in> same_orbit_rel = (\<exists>g \<in> carrier G. ((\<phi> g) n = m))"
unfolding same_orbit_rel_def using assms by auto

text \<open>Now we show that the relation we've defined is, indeed, an
equivalence relation:\<close>

lemma same_orbit_is_equiv:
  shows "equiv M same_orbit_rel"
proof(rule equivI)
  show "refl_on M same_orbit_rel"
  proof(rule refl_onI)
    show "same_orbit_rel \<subseteq> M \<times> M" unfolding same_orbit_rel_def by auto
  next
    fix m
    assume "m \<in> M"
    hence "(\<phi> \<one>) m = m" by(rule one_is_id)
    with \<open>m \<in> M\<close> show  "(m, m) \<in> same_orbit_rel" unfolding same_orbit_rel_def by (auto simp:same_orbit_char)
  qed
next
  show "sym same_orbit_rel"
  proof(rule symI)
    fix m n
    assume mn:"(m, n) \<in> same_orbit_rel"
    then obtain g where g:"g \<in> carrier G" "\<phi> g n = m" unfolding same_orbit_rel_def by auto
    hence invg:"inv g \<in> carrier G" by (metis inv_closed)
    from mn have "(m, n) \<in> M \<times> M" unfolding same_orbit_rel_def by simp
    hence mn2:"m \<in> M" "n \<in> M" by auto
    from g mn2 have "\<phi> (inv g) m = n" by (metis group_inv_rel)
    with invg mn2 show "(n, m) \<in> same_orbit_rel" unfolding same_orbit_rel_def by auto
  qed
next
  show "trans same_orbit_rel"
  proof(rule transI)
    fix x y z
    assume xy:"(x, y) \<in> same_orbit_rel"
    then obtain g where g:"g \<in> carrier G" and grel:"(\<phi> g) y = x" unfolding same_orbit_rel_def by auto
    assume yz:"(y, z) \<in> same_orbit_rel"
    then obtain h where h:"h \<in> carrier G" and hrel:"(\<phi> h) z = y" unfolding same_orbit_rel_def by auto
    from g h have gh:"g \<otimes> h \<in> carrier G" by simp
    from xy yz have "x \<in> M" "z \<in> M" unfolding same_orbit_rel_def by auto
    with g h have "\<phi> (g \<otimes> h) z = (\<phi> g) ((\<phi> h) z)" by (metis action_mult)
    also from hrel grel have "... = x" by simp
    finally have "\<phi> (g \<otimes> h) z = x".
    with gh \<open>x \<in> M\<close> \<open>z \<in> M\<close> show "(x, z) \<in> same_orbit_rel" unfolding same_orbit_rel_def by auto
  qed
qed

subsection \<open>Stabilizer and fixed points\<close>

text \<open>The following definition models the stabilizer of a group action:\<close>

definition stabilizer :: "'c \<Rightarrow> _"
  where "stabilizer m = {g \<in> carrier G. (\<phi> g) m = m}"

text \<open>This shows that the stabilizer of @{term m} is a subgroup of @{term G}.\<close>

lemma stabilizer_is_subgroup:
  assumes m:"m \<in> M"
  shows "subgroup (stabilizer m) G"
proof(rule subgroupI)
  show "stabilizer m \<subseteq> carrier G" unfolding stabilizer_def by auto
next
  from m have "(\<phi> \<one>) m = m" by (rule one_is_id)
  hence "\<one> \<in> stabilizer m" unfolding stabilizer_def by simp
  thus "stabilizer m \<noteq> {}" by auto
next
  fix g
  assume g:"g \<in> stabilizer m"
  hence "g \<in> carrier G" "(\<phi> g) m = m" unfolding stabilizer_def by simp+
  with m have ginv:"(\<phi> (inv g)) m = m" by (metis group_inv_rel)
  from \<open>g \<in> carrier G\<close> have "inv g \<in> carrier G" by (metis inv_closed)
  with ginv show "(inv g) \<in>  stabilizer m" unfolding stabilizer_def by simp
next
  fix g h
  assume g:"g \<in> stabilizer m"
  hence g2:"g \<in> carrier G" unfolding stabilizer_def by simp
  assume h:"h \<in> stabilizer m"
  hence h2:"h \<in> carrier G" unfolding stabilizer_def by simp
  with g2 have gh:"g \<otimes> h \<in> carrier G" by (rule m_closed)
  from g2 h2 m have "\<phi> (g \<otimes> h) m = (\<phi> g) ((\<phi> h) m)" by (metis action_mult)
  also from g h have "... = m" unfolding stabilizer_def by simp
  finally have "\<phi> (g \<otimes> h) m = m".
  with gh show "g \<otimes> h \<in> stabilizer m" unfolding stabilizer_def by simp
qed

text \<open>Next, we define and characterize the fixed points of a group action.\<close>

definition fixed_points :: "'c set"
  where "fixed_points = {m \<in> M. carrier G \<subseteq> stabilizer m}"

lemma fixed_point_char:
  assumes "m \<in> M"
  shows "(m \<in> fixed_points) = (\<forall>g\<in>carrier G. \<phi> g m = m)"
using assms unfolding fixed_points_def stabilizer_def by force

lemma orbit_contains_rep:
  assumes m:"m \<in> M"
  shows "m \<in> orbit m"
unfolding orbit_def using assms by (metis equiv_class_self same_orbit_is_equiv)

lemma singleton_orbit_eq_fixed_point:
  assumes m:"m \<in> M"
  shows "(card (orbit m) = 1) = (m \<in> fixed_points)"
proof
  assume card:"card (orbit m) = 1"
  from m have "m \<in> orbit m" by (rule orbit_contains_rep)
  from m show "m \<in> fixed_points" unfolding fixed_points_def
  proof(auto)
    fix g
    assume gG:"g \<in> carrier G"
    with m have "\<phi> g m \<in> orbit m" by (auto dest:orbit_char)
    with \<open>m \<in> orbit m\<close> card have "\<phi> g m = m" by (auto simp add: card_Suc_eq)
    with gG show "g \<in> stabilizer m" unfolding stabilizer_def by simp
  qed
next
  assume "m \<in> fixed_points"
  hence fixed:"carrier G \<subseteq> stabilizer m" unfolding fixed_points_def by simp
  from m have "orbit m = {m}"
  proof(auto simp add: orbit_contains_rep)
    fix n
    assume "n \<in> orbit m"
    with m obtain g where g:"g \<in> carrier G" "\<phi> g m = n"  by (auto dest: orbit_char)
    moreover with fixed have "\<phi> g m = m" unfolding stabilizer_def by auto
    ultimately show "n = m" by simp
  qed
  thus "card (orbit m) = 1" by simp
qed

subsection \<open>The Orbit-Stabilizer Theorem\<close>

text \<open>This section contains some theorems about orbits and their quotient
groups. The first one is the well-known orbit-stabilizer theorem which
establishes a bijection between the the quotient group of the an element's
stabilizer and its orbit.\<close>

theorem orbit_thm:
  assumes m:"m \<in> M"
  assumes rep:"\<And>U. U \<in> (carrier (G Mod (stabilizer m))) \<Longrightarrow> rep U \<in> U"
  shows "bij_betw (\<lambda>H. (\<phi> (inv (rep H)) m)) (carrier (G Mod (stabilizer m))) (orbit m)"
proof(auto simp add:bij_betw_def)
  show "inj_on (\<lambda>H. \<phi> (inv (rep H)) m) (carrier (G Mod stabilizer m))"
  proof(rule inj_onI)
    fix U V
    assume U:"U \<in> carrier (G Mod (stabilizer m))"
    assume V:"V \<in> carrier (G Mod (stabilizer m))"
    define h where "h = rep V"
    define g where "g = rep U"
    have stabSubset:"(stabilizer m) \<subseteq> carrier G" unfolding stabilizer_def by auto
    from m have stabSubgroup: "subgroup (stabilizer m) G" by (metis stabilizer_is_subgroup)
    from V rep have hV:"h \<in> V" unfolding h_def by simp
    from V stabSubset have "V \<subseteq> carrier G" unfolding FactGroup_def RCOSETS_def r_coset_def by auto
    with hV have hG:"h \<in> carrier G" by auto
    hence hinvG:"inv h \<in> carrier G" by (metis inv_closed)
    from U rep have gU:"g \<in> U" unfolding g_def by simp
    from U stabSubset have "U \<subseteq> carrier G" unfolding FactGroup_def RCOSETS_def r_coset_def by auto
    with gU have gG:"g \<in> carrier G" by auto
    hence ginvG:"inv g \<in> carrier G" by (metis inv_closed)
    from gG hinvG have ginvhG: "g \<otimes> inv h \<in> carrier G" by (metis m_closed)
    assume reps:"\<phi> (inv rep U) m = \<phi> (inv rep V) m"
    hence gh:"\<phi> (inv g) m = \<phi> (inv h) m" unfolding g_def h_def.
    from gG hinvG m have "\<phi> (g \<otimes> (inv h)) m = \<phi> g (\<phi> (inv h) m)" by (metis action_mult)
    also from gh ginvG gG m have "... = \<phi> (g \<otimes> inv g) m" by (metis action_mult)
    also from m gG have "... = m" by (auto simp: one_is_id)
    finally have "\<phi> (g \<otimes> inv h) m = m".
    with ginvhG have "(g \<otimes> inv h) \<in> stabilizer m"
      unfolding stabilizer_def by simp
    hence "(stabilizer m) #> (g \<otimes> inv h) = (stabilizer m) #> \<one>"
      by (metis coset_join2 coset_mult_one m stabSubset stabilizer_is_subgroup subgroup.mem_carrier)
    with hinvG hG gG stabSubset have  stabgstabh:"(stabilizer m) #> g = (stabilizer m) #> h"
      by (metis coset_mult_inv1 group.coset_mult_one is_group)
    from stabSubgroup is_group U gU have "U = (stabilizer m) #> g"
      unfolding FactGroup_def by (simp add:subgroup.repr_independence2)
    also from stabgstabh is_group stabSubgroup V hV subgroup.repr_independence2 have "... = V"
      unfolding FactGroup_def by force
    finally show "U = V".
  qed
next
  have stabSubset:"stabilizer m \<subseteq> carrier G" unfolding stabilizer_def by auto
  fix H
  assume H:"H \<in> carrier (G Mod stabilizer m)"
  with rep have "rep H \<in> H" by simp
  moreover with H stabSubset have "H \<subseteq> carrier G" unfolding FactGroup_def RCOSETS_def r_coset_def by auto
  ultimately have "rep H \<in> carrier G"..
  hence "inv rep H \<in> carrier G" by (rule inv_closed)
  with m show "\<phi> (inv rep H) m \<in> orbit m" by (auto dest:orbit_char)
next
  fix n
  assume "n \<in> orbit m"
  with m obtain g where g:"g \<in> carrier G" "\<phi> g m = n" by (auto dest:orbit_char)
  hence invg:"inv g \<in> carrier G" by simp
  hence stabinvg:"((stabilizer m) #> (inv g)) \<in> carrier (G Mod stabilizer m)" unfolding FactGroup_def RCOSETS_def by auto
  hence "rep ((stabilizer m) #> (inv g)) \<in> (stabilizer m) #> (inv g)" by (metis rep)
  then obtain h where h:"h \<in> stabilizer m" "rep ((stabilizer m) #> (inv g)) = h \<otimes> (inv g)" unfolding r_coset_def by auto
  with g have "\<phi> (inv rep ((stabilizer m) #> (inv g))) m =  \<phi> (inv (h \<otimes> (inv g))) m" by simp
  also from h have hG:"h \<in> carrier G" unfolding stabilizer_def by simp
  with g have "\<phi> (inv (h \<otimes> (inv g))) m = \<phi> (g \<otimes> (inv h)) m" by (metis inv_closed inv_inv inv_mult_group)
  also from g hG m have "... = \<phi> g (\<phi> (inv h) m)" by (metis action_mult inv_closed)
  also from h m have "inv h \<in> stabilizer m" by (metis stabilizer_is_subgroup subgroup.m_inv_closed)
  hence "\<phi> g (\<phi> (inv h) m) = \<phi> g m" unfolding stabilizer_def by simp
  also from g have "... = n" by simp
  finally have "n = \<phi> (inv rep ((stabilizer m) #> (inv g))) m"..
  with stabinvg show "n \<in> (\<lambda>H. \<phi> (inv rep H) m) ` carrier (G Mod stabilizer m)" by simp
qed

text \<open>In the case of @{term G} being finite, the last theorem can be reduced
to a statement about the cardinality of orbit and stabilizer:\<close>

corollary orbit_size:
  assumes fin:"finite (carrier G)"
  assumes m:"m \<in> M"
  shows "order G = card (orbit m) * card (stabilizer m)"
proof -
  define rep where "rep = (\<lambda>U \<in> (carrier (G Mod (stabilizer m))). SOME x. x \<in> U)"
  have "\<And>U. U \<in> (carrier (G Mod (stabilizer m))) \<Longrightarrow> rep U \<in> U"
  proof -
    fix U
    assume U:"U \<in> carrier (G Mod stabilizer m)"
    then obtain g where "g \<in> carrier G" " U = (stabilizer m) #> g" unfolding FactGroup_def RCOSETS_def by auto
    with m have "(SOME x. x \<in> U) \<in> U" by (metis rcos_self stabilizer_is_subgroup someI_ex)
    with U show "rep U \<in> U" unfolding rep_def by simp
  qed
  with m have  bij:"card (carrier (G Mod (stabilizer m))) = card (orbit m)" by (metis bij_betw_same_card orbit_thm)
  from fin m have "card (carrier (G Mod (stabilizer m))) * card (stabilizer m)  = order G" unfolding FactGroup_def by (simp add: stabilizer_is_subgroup lagrange)
  with bij show ?thesis by simp
qed

lemma orbit_not_empty:
  assumes fin:"finite M"
  assumes A:"A \<in> orbits"
  shows "card A > 0"
proof -
  from A obtain m where "m \<in> M" "A = orbit m" unfolding orbits_def quotient_def orbit_def by auto
  hence "m \<in> A" by (metis orbit_contains_rep)
  hence "A \<noteq> {}" unfolding orbits_def by auto
  moreover from fin A have "finite A" unfolding orbits_def quotient_def Image_def same_orbit_rel_def by auto
  ultimately show ?thesis by auto
qed

lemma fin_set_imp_fin_orbits:
  assumes finM:"finite M"
  shows "finite orbits"
using assms unfolding orbits_def quotient_def by simp

(*One-Element-Orbits are Fixed Points*)
lemma singleton_orbits:
  shows "\<Union>{N\<in>orbits. card N = 1} = fixed_points"
proof
  show "\<Union>{N \<in> orbits. card N = 1} \<subseteq> fixed_points"
  proof
    fix x
    assume a:"x \<in> \<Union>{N \<in> orbits. card N = 1}"
    hence "x \<in> M" unfolding orbits_def quotient_def Image_def same_orbit_rel_def by auto
    from a obtain N where N:"N \<in> orbits" "card N = 1" "x \<in> N" by auto
    then obtain y where Norbit:"N = orbit y" "y \<in> M" unfolding orbits_def quotient_def orbit_def by auto
    hence "y \<in> N" by (metis orbit_contains_rep)
    with N have Nsing:"N = {x}" "N = {y}" by (auto simp: card_Suc_eq)
    hence "x = y" by simp
    with Norbit have Norbit2:"N = orbit x" by simp
    have "{g \<in> carrier G. \<phi> g x = x} = carrier G"
    proof(auto)
      fix g
      assume "g \<in> carrier G"
      with \<open>x \<in> M\<close> have "\<phi> g x \<in> orbit x" by (auto dest:orbit_char)
      with Nsing show "\<phi> g x = x" by (metis Norbit2 singleton_iff)
    qed
    with \<open>x \<in> M\<close> show "x \<in> fixed_points" unfolding fixed_points_def stabilizer_def by simp
  qed
next
  show "fixed_points \<subseteq> \<Union>{N \<in> orbits. card N = 1}"
  proof
    fix m
    assume m:"m \<in> fixed_points"
    hence mM:"m \<in> M" unfolding fixed_points_def by simp
    hence orbit:"orbit m \<in> orbits" unfolding orbits_def quotient_def orbit_def by auto
    from mM m have "card (orbit m) = 1" by (metis singleton_orbit_eq_fixed_point)
    with orbit have "orbit m \<in> {N \<in> orbits. card N = 1}" by simp
    with mM show "m \<in> \<Union>{N \<in> orbits. card N = 1}" by (auto dest: orbit_contains_rep)
  qed
qed

text \<open>If @{term G} is a @{term p}-group acting on a finite set, a given orbit is
either a singleton or @{term p} divides its cardinality.\<close>

lemma p_dvd_orbit_size:
  assumes orderG:"order G = p ^ a"
  assumes prime:"prime p"
  assumes finM:"finite M"
  assumes Norbit:"N \<in> orbits"
  assumes "card N > 1"
  shows "p dvd card N"
proof -
  from Norbit obtain m where m:"m \<in> M" "N = orbit m"  unfolding orbits_def quotient_def orbit_def by auto
  from prime have "0 < p ^ a" by (simp add: prime_gt_0_nat) 
  with orderG have "finite (carrier G)" unfolding order_def by (metis card_infinite less_nat_zero_code)
  with m have "order G = card (orbit m) * card (stabilizer m)" by (metis orbit_size)
  with orderG m have "p ^ a = card N * card (stabilizer m)" by simp
  with \<open>card N > 1\<close> show ?thesis
    by (metis dvd_mult2 dvd_mult_cancel1 nat_dvd_not_less nat_mult_1 prime 
          prime_dvd_power_nat prime_factor_nat prime_nat_iff zero_less_one) 
qed

text \<open>As a result of the last lemma the only orbits that count modulo
@{term p} are the fixed points\<close>

lemma fixed_point_congruence:
  assumes "order G = p ^ a"
  assumes "prime p"
  assumes finM:"finite M"
  shows "card M mod p = card fixed_points mod p"
proof -
  define big_orbits where "big_orbits = {N\<in>orbits. card N > 1}"
  from finM have orbit_part:"orbits = big_orbits \<union> {N\<in>orbits. card N = 1}" unfolding big_orbits_def by (auto dest:orbit_not_empty)
  have orbit_disj:"big_orbits \<inter> {N\<in>orbits. card N = 1} = {}" unfolding big_orbits_def by auto
  from finM have orbits_fin:"finite orbits" by (rule fin_set_imp_fin_orbits)
  hence fin_parts:"finite big_orbits" "finite {N\<in>orbits. card N = 1}" unfolding big_orbits_def by simp+
  from assms have "\<And>N. N \<in> big_orbits \<Longrightarrow> p dvd card N" unfolding big_orbits_def by (auto simp: p_dvd_orbit_size)
  hence orbit_div:"\<And>N. N \<in> big_orbits \<Longrightarrow> card N = (card N div p) * p" by (metis dvd_mult_div_cancel mult.commute)
  have "card M = card (\<Union> orbits)" unfolding orbits_def by (metis Union_quotient same_orbit_is_equiv)
  also  have "card (\<Union> orbits) = (\<Sum>N\<in>orbits. card N)" unfolding orbits_def
  proof (rule card_Union_disjoint)
    show "pairwise disjnt (M // same_orbit_rel)"
      unfolding pairwise_def disjnt_def by(metis same_orbit_is_equiv quotient_disj)
    show "\<And>A. A \<in> M // same_orbit_rel \<Longrightarrow> finite A"
      using finM same_orbit_rel_def by (auto dest:finite_equiv_class)
  qed
  also from orbit_part orbit_disj fin_parts have "... = (\<Sum>N\<in>big_orbits. card N) + (\<Sum>N\<in>{N'\<in>orbits. card N' = 1}. card N)" by (metis (lifting) sum.union_disjoint)
  also from assms orbit_div fin_parts have "... = (\<Sum>N\<in>big_orbits. (card N div p) * p) + card (\<Union>{N'\<in>orbits. card N' = 1})" by (auto simp: card_singleton_set)
  also have "... = (\<Sum>N\<in>big_orbits. card N div p) * p + card fixed_points" using singleton_orbits by (auto simp:sum_distrib_right)
  finally have "card M = (\<Sum>N\<in>big_orbits. card N div p) * p + card fixed_points".
  hence "card M mod p = ((\<Sum>N\<in>big_orbits. card N div p) * p + card fixed_points) mod p" by simp
  also have "... = (card fixed_points) mod p" by (metis mod_mult_self3)
  finally show ?thesis.  
qed

text \<open>We can restrict any group action to the action of a subgroup:\<close>

lemma subgroup_action:
  assumes H:"subgroup H G"
  shows "group_action (G\<lparr>carrier := H\<rparr>) \<phi> M"
unfolding group_action_def group_action_axioms_def group_hom_def group_hom_axioms_def hom_def
using assms
proof (auto simp add: is_group subgroup.subgroup_is_group group_BijGroup)
  fix x
  assume "x \<in> H"
  with H have "x \<in> carrier G" by (metis subgroup.mem_carrier)
  with grouphom show "\<phi> x \<in> carrier (BijGroup M)" by (metis group_hom.hom_closed)
next
  fix x y
  assume x:"x \<in> H" and y:"y \<in> H"
  with H have "x \<in> carrier G" "y \<in> carrier G" by (metis subgroup.mem_carrier)+
  with grouphom show "\<phi> (x \<otimes> y) = \<phi> x \<otimes>\<^bsub>BijGroup M\<^esub> \<phi> y" by (simp add: group_hom.hom_mult)
qed

end

subsection \<open>Some Examples for Group Actions\<close>

lemma (in group) right_mult_is_bij:
  assumes h:"h \<in> carrier G"
  shows "(\<lambda>g \<in> carrier G. h \<otimes> g) \<in> Bij (carrier G)"
proof(auto simp add:Bij_def bij_betw_def inj_on_def)
  fix x y
  assume x:"x \<in> carrier G" and y:"y \<in> carrier G" and "h \<otimes> x = h \<otimes> y"
  with h show "x = y"
    by simp
next
  fix x
  assume x:"x \<in> carrier G"
  with h show "h \<otimes> x \<in> carrier G" by (metis m_closed)
  from x h have "inv h \<otimes> x \<in> carrier G" by (metis m_closed inv_closed)
  moreover from x h have "h \<otimes> (inv h \<otimes> x)  = x" by (metis inv_closed r_inv m_assoc l_one)
  ultimately show "x \<in> (\<otimes>) h ` carrier G" by force
qed

lemma (in group) right_mult_group_action:
  shows "group_action G (\<lambda>h. \<lambda>g \<in> carrier G. h \<otimes> g) (carrier G)"
unfolding group_action_def group_action_axioms_def group_hom_def group_hom_axioms_def hom_def
proof(auto simp add:is_group group_BijGroup)
  fix h
  assume "h \<in> carrier G"
  thus "(\<lambda>g \<in> carrier G. h \<otimes> g) \<in> carrier (BijGroup (carrier G))" unfolding BijGroup_def by (auto simp:right_mult_is_bij)
next
  fix x y
  assume x:"x \<in> carrier G" and y:"y \<in> carrier G"
  define multx multy
    where "multx = (\<lambda>g\<in>carrier G. x \<otimes> g)"
      and "multy = (\<lambda>g\<in>carrier G. y \<otimes> g)"
  with x y have "multx \<in> (Bij (carrier G))" "multy \<in> (Bij (carrier G))" by (metis right_mult_is_bij)+
  hence "multx \<otimes>\<^bsub>BijGroup (carrier G)\<^esub> multy = (\<lambda>g\<in>carrier G. multx (multy g))" unfolding BijGroup_def by (auto simp: compose_def)
  also have "... = (\<lambda>g\<in>carrier G. (x \<otimes> y) \<otimes> g)" unfolding multx_def multy_def
  proof(rule restrict_ext)
    fix g
    assume g:"g \<in> carrier G"
    with x y have "x \<otimes> y \<in> carrier G" "y \<otimes> g \<in> carrier G" by simp+
    with x y g show "(\<lambda>g\<in>carrier G. x \<otimes> g) ((\<lambda>g\<in>carrier G. y \<otimes> g) g) = x \<otimes> y \<otimes> g" by (auto simp:m_assoc)
  qed
  finally show "(\<lambda>g\<in>carrier G. (x \<otimes> y) \<otimes> g) = (\<lambda>g\<in>carrier G. x \<otimes> g) \<otimes>\<^bsub>BijGroup (carrier G)\<^esub> (\<lambda>g\<in>carrier G. y \<otimes> g)" unfolding multx_def multy_def by simp
qed

lemma (in group) rcosets_closed:
  assumes HG:"subgroup H G"
  assumes g:"g \<in> carrier G"
  assumes M:"M \<in> rcosets H"
  shows "M #> g \<in> rcosets H"
proof -
  from M obtain h where h:"h \<in> carrier G" "M = H #> h" unfolding RCOSETS_def by auto
  with g HG have "M #> g = H #> (h \<otimes> g)" by (metis coset_mult_assoc subgroup.subset)
  with HG g h show "M #> g \<in> rcosets H" by (metis rcosetsI subgroup.m_closed subgroup.subset subgroup_self)
qed

lemma (in group) inv_mult_on_rcosets_is_bij:
  assumes HG:"subgroup H G"
  assumes g:"g \<in> carrier G"
  shows "(\<lambda>U \<in> rcosets H. U #> inv g) \<in> Bij (rcosets H)"
proof(auto simp add:Bij_def bij_betw_def inj_on_def)
  fix M
  assume "M \<in> rcosets H"
  with HG g show "M #> inv g \<in> rcosets H" by (metis inv_closed rcosets_closed)
next
  fix M
  assume M:"M \<in> rcosets H"
  with HG g have "M #> g \<in> rcosets H" by (rule rcosets_closed)
  moreover from M HG g have "M #> g #> inv g = M" by (metis coset_mult_assoc coset_mult_inv2 inv_closed is_group subgroup.rcosets_carrier)
  ultimately show " M \<in> (\<lambda>U. U #> inv g) ` (rcosets H)" by auto
next
  fix M N x
  assume M:"M \<in> rcosets H" and N:"N \<in> rcosets H" and "M #> inv g = N #> inv g"
  hence "(M #> inv g) #> g = (N #> inv g) #> g" by simp
  with HG M N g have "M #> (inv g \<otimes> g) = N #> (inv g \<otimes> g)" by (metis coset_mult_assoc is_group subgroup.m_inv_closed subgroup.rcosets_carrier subgroup_self)
  with HG M N g have a1:"M = N" by (metis l_inv coset_mult_one is_group subgroup.rcosets_carrier)
  {
    assume "x \<in> M"
    with a1 show "x \<in> N" by simp
  }
  {
    assume "x \<in> N"
    with a1 show "x \<in> M" by simp
  }
qed


lemma (in group) inv_mult_on_rcosets_action:
  assumes HG:"subgroup H G"
  shows "group_action G (\<lambda>g. \<lambda>U \<in> rcosets H. U #> inv g) (rcosets H)"
unfolding group_action_def group_action_axioms_def group_hom_def group_hom_axioms_def hom_def
proof(auto simp add:is_group group_BijGroup)
  fix h
  assume "h \<in> carrier G"
  with HG show "(\<lambda>U \<in> rcosets H. U #> inv h) \<in> carrier (BijGroup (rcosets H))"
    unfolding BijGroup_def by (auto simp:inv_mult_on_rcosets_is_bij)
next
  fix x y
  assume x:"x \<in> carrier G" and y:"y \<in> carrier G"
  define cosx cosy
    where "cosx = (\<lambda>U\<in>rcosets H. U #> inv x)"
      and "cosy = (\<lambda>U\<in>rcosets H. U #> inv y)"
  with x y HG have "cosx \<in> (Bij (rcosets H))" "cosy \<in> (Bij (rcosets H))"
    by (metis inv_mult_on_rcosets_is_bij)+
  hence "cosx \<otimes>\<^bsub>BijGroup (rcosets H)\<^esub> cosy = (\<lambda>U\<in>rcosets H. cosx (cosy U))"
    unfolding BijGroup_def by (auto simp: compose_def)
  also have "... = (\<lambda>U\<in>rcosets H. U #> inv (x \<otimes> y))" unfolding cosx_def cosy_def
  proof(rule restrict_ext)
    fix U
    assume U:"U \<in> rcosets H"
    with HG y have "U #> inv y \<in> rcosets H" by (metis inv_closed rcosets_closed)
    with x y HG U have "(\<lambda>U\<in>rcosets H. U #> inv x) ((\<lambda>U\<in>rcosets H. U #> inv y) U) = U #> inv y #> inv x"
      by auto
    also from x y U HG have "... = U #> inv (x \<otimes> y)"
      by (metis inv_mult_group coset_mult_assoc inv_closed is_group subgroup.rcosets_carrier)
    finally show "(\<lambda>U\<in>rcosets H. U #> inv x) ((\<lambda>U\<in>rcosets H. U #> inv y) U) = U #> inv (x \<otimes> y)".
  qed
  finally show "(\<lambda>U\<in>rcosets H. U #> inv (x \<otimes> y)) = (\<lambda>U\<in>rcosets H. U #> inv x) \<otimes>\<^bsub>BijGroup (rcosets H)\<^esub> (\<lambda>U\<in>rcosets H. U #> inv y)"
    unfolding cosx_def cosy_def by simp
qed

end
