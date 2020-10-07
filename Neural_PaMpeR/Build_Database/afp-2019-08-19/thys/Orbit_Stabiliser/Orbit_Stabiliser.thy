chapter "Orbit-Stabiliser Theorem"
text \<open>
In this Theory we will prove the orbit-stabiliser theorem, a basic result in the algebra of groups.

\<close>

theory Orbit_Stabiliser
  imports
    Left_Coset

begin

section "Imports"
text \<open>
  /HOL/Algebra/Group.thy is used for the definitions of groups and subgroups
\<close>

text \<open>
  Left\_Coset.thy is a copy of /HOL/Algebra/Coset.thy that includes additional theorems about left cosets.

  The version of Coset.thy in the Isabelle library is missing some theorems about left cosets
  that are available for right cosets, so these had to be added by simply replacing the definitions
  of right cosets with those of left cosets.

  Coset.thy is used for definitions of group order, quotient groups (operator LMod), and Lagranges theorem.
\<close>

text \<open>
  /HOL/Fun.thy is used for function composition and the identity function.
\<close>


section "Group Actions"

text \<open>
  We begin by augmenting the existing definition of a group with a group action.

  The group action was defined according to @{cite groupaction}.
\<close>

locale orbit_stabiliser = group +
  fixes action :: "'a \<Rightarrow> 'b \<Rightarrow> 'b" (infixl "\<odot>" 51)
  assumes id_act [simp]: "\<one> \<odot> x = x"
    and compat_act:
    "g \<in> carrier G \<and> h \<in> carrier G \<longrightarrow> g \<odot> (h \<odot> x) = (g \<otimes> h) \<odot> x"

section "Orbit and stabiliser"

text \<open>
Next, we define orbit and stabiliser, according to the same Wikipedia article.
\<close>

context orbit_stabiliser
begin

definition orbit :: "'b \<Rightarrow> 'b set" where
  "orbit x = {y. (\<exists> g \<in> carrier G. y = g \<odot> x)}"

definition stabiliser :: "'b \<Rightarrow> 'a set"
  where "stabiliser x = {g \<in> carrier G. g \<odot> x = x}"


section "Stabiliser Theorems"

text \<open>
We begin our proofs by showing that the stabiliser forms a subgroup.

This proof follows the template from  @{cite stabsub}.
\<close>

theorem stabiliser_subgroup: "subgroup (stabiliser x) G"
proof(rule subgroupI)
  show "stabiliser x \<subseteq> carrier G" using stabiliser_def by auto
next
  fix x
  from id_act have "\<one> \<odot> x = x" by simp
  then have "\<one> \<in> stabiliser x" using stabiliser_def by auto
  then show "stabiliser x \<noteq> {}" by auto
next
  fix g x
  assume gStab:"g \<in> stabiliser x"
  then have g_car:"g \<in> carrier G" using stabiliser_def by simp
  then have invg_car:"inv g \<in> carrier G" using inv_closed by simp
  have "g \<odot> x = x" using stabiliser_def gStab by simp
  then have "inv g \<odot> (g \<odot> x) = inv g \<odot> x" by simp
  then have "(inv g \<otimes> g) \<odot> x = inv g \<odot> x" using compat_act g_car invg_car by simp
  then have "x = (inv g) \<odot> x" using g_car l_inv by simp
  then show "inv g \<in> stabiliser x" using invg_car stabiliser_def by simp
next
  fix g h x
  assume g_stab: "g \<in> stabiliser x" and h_stab: "h \<in> stabiliser x"
  then have g_car: "g \<in> carrier G" and h_car: "h \<in> carrier G" using stabiliser_def by auto
  then have "g \<odot> x = x" "h \<odot> x = x"
    using stabiliser_def g_stab h_stab by auto
  then have "g \<odot> (h \<odot> x) = x" by simp
  then have "(g \<otimes> h) \<odot> x = x" using compat_act g_car h_car by simp
  then show "(g \<otimes> h) \<in> stabiliser x"
    using g_stab h_stab stabiliser_def by auto
qed

text \<open>
As an intermediate step we formulate a lemma about the relationship between the group action
and the stabiliser.

This proof follows the template from @{cite stabsubcor}.
\<close>

corollary stabiliser_subgroup_corollary:
  assumes g_car: "g \<in> carrier G" and
    h_car: "h \<in> carrier G"
  shows "(g \<odot> x) = (h \<odot> x) \<longleftrightarrow> ((inv g) \<otimes> h) \<in> stabiliser x"
proof
  from g_car have invg_car: "(inv g) \<in> carrier G" by auto
  show "(g \<odot> x) = (h \<odot> x) \<Longrightarrow> inv g \<otimes> h \<in> stabiliser x"
  proof -
    assume gh: "(g \<odot> x) = (h \<odot> x)"
    have "((inv g) \<otimes> h) \<odot> x = (inv g) \<odot> (h \<odot> x)" using assms compat_act by simp
    moreover have "(inv g) \<odot> (h \<odot> x) = (inv g) \<odot> (g \<odot> x)" using gh by simp
    moreover have "(inv g) \<odot> (g \<odot> x) = ((inv g) \<otimes> g) \<odot> x" using invg_car g_car compat_act by simp
    moreover have "((inv g) \<otimes> g) \<odot> x = x" using g_car by simp
    ultimately have "((inv g) \<otimes> h) \<odot> x = x" by simp
    then show ?thesis using stabiliser_def assms by simp
  qed

  show "inv g \<otimes> h \<in> stabiliser x \<Longrightarrow> g \<odot> x = h \<odot> x"
  proof -
    assume gh_stab: "inv g \<otimes> h \<in> stabiliser x"
    with stabiliser_def have "x = ((inv g) \<otimes> h) \<odot> x" by simp
    then have "\<one> \<odot> x = ((inv g) \<otimes> h) \<odot> x"  by simp
    then have "((inv g) \<otimes> g) \<odot> x = ((inv g) \<otimes> h) \<odot> x" using invg_car g_car by simp
    then have "x = (inv g) \<odot> (h \<odot> x)" using compat_act g_car h_car by simp
    then have "g \<odot> x = (g \<otimes> (inv g)) \<odot> (h \<odot> x)" using compat_act g_car invg_car by metis
    then have "g \<odot> x = h \<odot> x" using compat_act g_car id_act invg_car r_inv by simp
    then show ?thesis by simp
  qed
qed

text \<open>
Using the previous lemma and our proof that the stabiliser forms a subgroup, we can now
show that the elements of the orbit map to left cosets of the stabiliser.

This will later form the basis of showing a bijection between the orbit and those cosets.
\<close>

lemma stabiliser_cosets_equivalent:
  assumes g_car: "g \<in> carrier G" and
    h_car: "h \<in> carrier G"
  shows "(g \<odot> x) = (h \<odot> x) \<longleftrightarrow> (g <# stabiliser x) = (h <# stabiliser x)"
proof
  show "g \<odot> x = h \<odot> x \<Longrightarrow> g <# stabiliser x = h <# stabiliser x"
  proof -
    assume "g \<odot> x = h \<odot> x"
    then have stab_elem: "((inv g) \<otimes> h) \<in> stabiliser x"
      using assms stabiliser_subgroup_corollary by simp
    with subgroup.lcos_module_rev[OF stabiliser_subgroup] have "h \<in> g <# (stabiliser x)"
      using assms is_group by simp
    with l_repr_independence have  "g <# (stabiliser x) = h <# (stabiliser x)"
      using assms  stab_elem stabiliser_subgroup by auto
    then show ?thesis by simp
  qed
  show "g <# stabiliser x = h <# stabiliser x \<Longrightarrow> g \<odot> x = h \<odot> x"
  proof -
    assume "g <# stabiliser x = h <# stabiliser x"
    with subgroup.lcos_module_rev[OF stabiliser_subgroup] have "h \<in> g <# (stabiliser x)"
      using assms is_group l_inv stabiliser_subgroup subgroup_def by metis
    with subgroup.lcos_module_imp[OF stabiliser_subgroup] have "((inv g) \<otimes> h) \<in> stabiliser x"
      using assms is_group by blast
    with stabiliser_subgroup_corollary have "g \<odot> x = h \<odot> x" using assms by simp
    then show ?thesis by simp
  qed
qed

section "Picking representatives from cosets"

text \<open>
Before we can prove the bijection, we need a few lemmas about representatives from sets.

First we define rep to be an arbitrary element from a left coset of the stabiliser.
\<close>
definition rep :: "'a set \<Rightarrow> 'a" where
  "(H \<in> carrier (G LMod (stabiliser x))) \<Longrightarrow> rep H = (SOME y. y \<in> H)"

text \<open>
  The next lemma shows that the representative is always an element of its coset.
\<close>
lemma quotient_rep_ex  : "H \<in> (carrier (G LMod (stabiliser x))) \<Longrightarrow> rep H \<in> H"
proof -
  fix H
  assume H:"H \<in> carrier (G LMod stabiliser x)"
  then obtain g where "g \<in> carrier G" "H = g <# (stabiliser x)"
    unfolding LFactGroup_def LCOSETS_def by auto
  then have "(SOME x. x \<in> H) \<in> H" using lcos_self stabiliser_subgroup someI_ex by fast
  then show "rep H \<in> H" using H rep_def by auto
qed

text \<open>
The final lemma about representatives shows that it does not matter which element of the coset
is picked, i.e. all representatives are equivalent.
\<close>
lemma rep_equivalent:
  assumes H:"H \<in> carrier (G LMod stabiliser x)" and
    gH:"g \<in> H"
  shows "H = g <# (stabiliser x)"
proof -
  fix h
  from H obtain h where hG:"h \<in> carrier G" and H2:"H = h <# (stabiliser x)"
    unfolding LFactGroup_def LCOSETS_def by auto
  with H gH have gh:"g \<in> h <# (stabiliser x)" by simp
  from l_repr_independence have "h <# stabiliser x = g <# stabiliser x"
    using hG gh stabiliser_subgroup by simp
  with H2 have "H = g <# (stabiliser x)" by simp
  then show ?thesis by simp
qed

section "Orbit-Stabiliser Theorem"

text \<open>
  We can now establish the bijection between orbit(x) and the quotient group G/(stabiliser(x))

  The idea for this bijection is from @{cite orbitstab}
\<close>
theorem orbit_stabiliser_bij:
  "bij_betw (\<lambda>H. rep H \<odot> x) (carrier (G LMod (stabiliser x))) (orbit x) "
proof (rule bij_betw_imageI)
  (* show the function is injective *)
  show "inj_on (\<lambda>H. rep H \<odot> x) (carrier (G LMod stabiliser x))"
  proof(rule inj_onI)
    fix H H'
    assume H:"H \<in> carrier (G LMod (stabiliser x))"
    assume H':"H' \<in> carrier (G LMod (stabiliser x))"
    obtain h h' where  h:"h = rep H" and h': "h' = rep H'" by simp
    assume act_equal: "(rep H) \<odot> x = (rep H') \<odot> x"
    from H h quotient_rep_ex have hH: "h \<in> H" by simp
    from H' h' quotient_rep_ex have hH': "h' \<in> H'" by simp
    from subgroup.lcosets_carrier[OF stabiliser_subgroup is_group] H have "H \<subseteq> carrier G"
      unfolding LFactGroup_def by simp
    then have hG: "h \<in> carrier G" using hH by auto
    from subgroup.lcosets_carrier[OF stabiliser_subgroup is_group] H' have "H' \<subseteq> carrier G"
      unfolding LFactGroup_def by simp
    then have h'G: "h' \<in> carrier G" using hH' by auto

        (* Apply lemma about equivalent cosets *)
    have hh'_equiv:"h <# (stabiliser x) = h' <# (stabiliser x)"
      using hG h'G h h' act_equal stabiliser_cosets_equivalent by simp

    from hh'_equiv have H2:"H = h <# (stabiliser x)"
      using H hH rep_equivalent by blast
    moreover from hh'_equiv have H3:"H' = h <# (stabiliser x)"
      using H' hH' rep_equivalent by blast
    then show "H = H'" using H2 H3 by simp
  qed
next
  show "(\<lambda>H. rep H \<odot> x) ` carrier (G LMod stabiliser x) = orbit x"
  proof(auto)
    show "\<And>H. H \<in> carrier (G LMod stabiliser x) \<Longrightarrow> rep H \<odot> x \<in> orbit x"
    proof -
      fix H
      assume H:"H \<in> carrier (G LMod (stabiliser x))"
      obtain h where h:"h = rep H" by simp
      from H h quotient_rep_ex have hH: "h \<in> H" by simp
      have stab_sub: "(stabiliser x) \<subseteq> carrier G" using stabiliser_def by auto
      from subgroup.lcosets_carrier[OF stabiliser_subgroup is_group] H have "H \<subseteq> carrier G"
        unfolding LFactGroup_def by simp
      with hH have "h \<in> carrier G" by auto
      then show "(rep H) \<odot> x \<in> orbit x" using h orbit_def mem_Collect_eq by blast
    qed
    show "\<And>y. y \<in> orbit x \<Longrightarrow> y \<in> (\<lambda>H. rep H \<odot> x) ` carrier (G LMod stabiliser x)"
    proof -
      fix y
      assume y:"y \<in> orbit x"
      obtain g  where gG:"g \<in> carrier G" and "y = g \<odot> x" using y orbit_def by auto
      obtain H where H:"H = g <# (stabiliser x)" by auto
      with gG have H_carr:"H \<in> carrier (G LMod stabiliser x)"
        unfolding LFactGroup_def LCOSETS_def by auto
      then have "rep H \<in> H" using quotient_rep_ex by auto
      then obtain h where h_stab:"h \<in> stabiliser x" and gh:"rep H = g \<otimes> h"
        unfolding H l_coset_def by auto
      have hG:"h \<in> carrier G" using h_stab stabiliser_def by auto
      from stabiliser_def h_stab have "h \<odot> x = x" by auto
      with \<open>y = g \<odot> x\<close> have "y = g \<odot> (h \<odot> x)" by simp
      then have "y = (g \<otimes> h) \<odot> x" using gG hG compat_act by auto
      then have "y = (rep H) \<odot> x" using gh by simp
      then show "y \<in> (\<lambda>H. rep H \<odot> x) ` carrier (G LMod stabiliser x)"
        using H_carr by simp
    qed
  qed
qed


text\<open>
  The actual orbit-stabiliser theorem is a consequence of the bijection
   we established in the previous theorem and of Lagrange's theorem
\<close>
theorem orbit_stabiliser:
  assumes finite: "finite (carrier G)"
  shows "order G = card (orbit x) * card (stabiliser x)"
proof -
  have "card (carrier (G LMod (stabiliser x))) = card (orbit x)"
    using bij_betw_same_card orbit_stabiliser_bij by auto
  moreover have "card (carrier (G LMod (stabiliser x))) * card (stabiliser x)  = order G"
    using finite stabiliser_subgroup l_lagrange unfolding LFactGroup_def by simp
  ultimately show ?thesis by simp
qed
end

end
