section \<open>Sets of maps\<close>
theory MapSets
imports SetMap Utils
begin

text \<open>
In the section about the finiteness of the argument space, we need the fact that the set of maps from a finite domain to a finite range is finite, and the same for the set-valued maps defined in @{theory "Shivers-CFA.SetMap"}. Both these sets are defined (\<open>maps_over\<close>, \<open>smaps_over\<close>) and the finiteness is shown.
\<close>

definition maps_over :: "'a::type set \<Rightarrow> 'b::type set \<Rightarrow> ('a \<rightharpoonup> 'b) set"
  where "maps_over A B = {m. dom m \<subseteq> A \<and> ran m \<subseteq> B}"

lemma maps_over_empty[simp]:
  "Map.empty \<in> maps_over A B"
unfolding maps_over_def by simp

lemma maps_over_upd:
  assumes "m \<in> maps_over A B"
  and "v \<in> A" and "k \<in> B"
shows "m(v \<mapsto> k) \<in> maps_over A B"
  using assms unfolding maps_over_def
  by (auto dest: subsetD[OF ran_upd])

lemma maps_over_finite[intro]:
  assumes "finite A" and "finite B" shows "finite (maps_over A B)"
proof-
  have inj_map_graph: "inj (\<lambda>f. {(x, y). Some y = f x})"
  proof (induct rule: inj_onI)
    case (1 x y)
    from "1.hyps"(3) have hyp: "\<And> a b. (Some b = x a) \<longleftrightarrow> (Some b = y a)"
      by (simp add: set_eq_iff)
    show ?case
    proof (rule ext)
    fix z show "x z = y z"
      using hyp[of _ z]
      by (cases "x z", cases "y z", auto)
    qed
  qed

  have "(\<lambda>f. {(x, y). Some y = f x}) ` maps_over A B \<subseteq> Pow( A \<times> B )" (is "?graph \<subseteq> _")
    unfolding maps_over_def
    by (auto dest!:subsetD[of _ A] subsetD[of _ B] intro:ranI)
  moreover
  have "finite (Pow( A \<times> B ))" using assms by auto
  ultimately
  have "finite ?graph" by (rule finite_subset)
  thus ?thesis
    by (rule finite_imageD[OF _ subset_inj_on[OF inj_map_graph subset_UNIV]])
qed

definition smaps_over :: "'a::type set \<Rightarrow> 'b::type set \<Rightarrow> ('a \<Rightarrow> 'b set) set"
  where "smaps_over A B = {m. sdom m \<subseteq> A \<and> sran m \<subseteq> B}"

lemma smaps_over_empty[simp]:
  "{}. \<in> smaps_over A B"
unfolding smaps_over_def by simp

lemma smaps_over_singleton:
  assumes "k \<in> A" and "vs \<subseteq> B"
shows "{k := vs}. \<in> smaps_over A B"
  using assms unfolding smaps_over_def
  by(auto dest: subsetD[OF sdom_singleton])

lemma smaps_over_un:
  assumes "m1 \<in> smaps_over A B" and "m2 \<in> smaps_over A B"
  shows "m1 \<union>. m2 \<in> smaps_over A B"
using assms unfolding smaps_over_def
by (auto simp add:smap_union_def)

lemma smaps_over_Union:
  assumes "set ms \<subseteq> smaps_over A B"
  shows "\<Union>.ms \<in> smaps_over A B"
using assms
by (induct ms)(auto intro: smaps_over_un)

lemma smaps_over_im:
 "\<lbrakk> f \<in> m a ; m \<in> smaps_over A B \<rbrakk> \<Longrightarrow> f \<in> B"
unfolding smaps_over_def by (auto simp add:sran_def)

lemma smaps_over_finite[intro]: 
  assumes "finite A" and "finite B" shows "finite (smaps_over A B)"
proof-
  have inj_smap_graph: "inj (\<lambda>f. {(x, y). y = f x \<and> y \<noteq> {}})" (is "inj ?gr")
  proof (induct rule: inj_onI)
    case (1 x y)
    from "1.hyps"(3) have hyp: "\<And> a b. (b = x a \<and> b \<noteq> {}) = (b = y a \<and> b \<noteq> {})"
      by -(subst (asm) (3) set_eq_iff, simp)
    show ?case
    proof (rule ext)
    fix z show "x z = y z"
      using hyp[of _ z]
      by (cases "x z \<noteq> {}", cases "y z \<noteq> {}", auto)
    qed
  qed

  have "?gr ` smaps_over A B \<subseteq> Pow( A \<times> Pow  B )" (is "?graph \<subseteq> _")
    unfolding smaps_over_def
    by (auto dest!:subsetD[of _ A] subsetD[of _ "Pow B"] sdom_not_mem intro:sranI)
  moreover
  have "finite (Pow( A \<times> Pow B ))" using assms by auto
  ultimately
  have "finite ?graph" by (rule finite_subset)
  thus ?thesis
    by (rule finite_imageD[OF _ subset_inj_on[OF inj_smap_graph subset_UNIV]])
qed

end
