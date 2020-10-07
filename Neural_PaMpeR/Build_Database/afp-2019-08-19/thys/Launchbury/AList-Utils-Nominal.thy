theory "AList-Utils-Nominal"
imports "AList-Utils" "Nominal-Utils"
begin

subsubsection \<open>Freshness lemmas related to associative lists\<close>

lemma domA_not_fresh:
  "x \<in> domA \<Gamma> \<Longrightarrow> \<not>(atom x \<sharp> \<Gamma>)"
  by (induct \<Gamma>, auto simp add: fresh_Cons fresh_Pair)

lemma fresh_delete:
  assumes "a \<sharp> \<Gamma>"
  shows "a \<sharp> delete v \<Gamma>"
using assms
by(induct \<Gamma>)(auto simp add: fresh_Cons)

lemma fresh_star_delete:
  assumes "S \<sharp>* \<Gamma>"
  shows "S \<sharp>* delete v \<Gamma>"
  using assms fresh_delete unfolding fresh_star_def by fastforce

lemma fv_delete_subset:
  "fv (delete v \<Gamma>) \<subseteq> fv \<Gamma>"
  using fresh_delete unfolding fresh_def fv_def by auto

lemma fresh_heap_expr:
  assumes "a \<sharp> \<Gamma>"
  and "(x,e) \<in> set \<Gamma>"
  shows "a \<sharp> e"
  using assms
  by (metis fresh_list_elem fresh_Pair)

lemma fresh_heap_expr':
  assumes "a \<sharp> \<Gamma>"
  and "e \<in> snd ` set \<Gamma>"
  shows "a \<sharp> e"
  using assms
  by (induct \<Gamma>, auto simp add: fresh_Cons fresh_Pair)

lemma fresh_star_heap_expr':
  assumes "S \<sharp>* \<Gamma>"
  and "e \<in> snd ` set \<Gamma>"
  shows "S \<sharp>* e"
  using assms
  by (metis fresh_star_def fresh_heap_expr')

lemma fresh_map_of:
  assumes "x \<in> domA \<Gamma>"
  assumes "a \<sharp> \<Gamma>"
  shows "a \<sharp> the (map_of \<Gamma> x)"
  using assms
  by (induct \<Gamma>)(auto simp add: fresh_Cons fresh_Pair)

lemma fresh_star_map_of:
  assumes "x \<in> domA \<Gamma>"
  assumes "a \<sharp>* \<Gamma>"
  shows "a \<sharp>* the (map_of \<Gamma> x)"
  using assms by (simp add: fresh_star_def fresh_map_of)

lemma domA_fv_subset: "domA \<Gamma> \<subseteq> fv \<Gamma>"
  by (induction \<Gamma>) auto

lemma map_of_fv_subset: "x \<in> domA \<Gamma> \<Longrightarrow> fv (the (map_of \<Gamma> x)) \<subseteq> fv \<Gamma>"
  by (induction \<Gamma>) auto

lemma map_of_Some_fv_subset: "map_of \<Gamma> x = Some e \<Longrightarrow> fv e \<subseteq> fv \<Gamma>"
  by (metis domA_from_set map_of_fv_subset map_of_SomeD option.sel)

subsubsection \<open>Equivariance lemmas\<close>

lemma domA[eqvt]:
  "\<pi> \<bullet> domA \<Gamma> = domA (\<pi> \<bullet> \<Gamma>)"
  by (simp add: domA_def)

lemma mapCollect[eqvt]:
  "\<pi> \<bullet> mapCollect f m = mapCollect (\<pi> \<bullet> f) (\<pi> \<bullet> m)"
unfolding mapCollect_def
by perm_simp rule

subsubsection \<open>Freshness and distinctness\<close>

lemma fresh_distinct:
 assumes "atom ` S \<sharp>* \<Gamma>"
 shows "S \<inter> domA \<Gamma> = {}"
proof-
  { fix x
    assume "x \<in> S"
    moreover
    assume "x \<in> domA \<Gamma>"
    hence "atom x \<in> supp \<Gamma>"
      by (induct \<Gamma>)(auto simp add: supp_Cons domA_def supp_Pair supp_at_base)
    ultimately
    have False
      using assms
      by (simp add: fresh_star_def fresh_def)
  }
  thus "S \<inter> domA \<Gamma> = {}" by auto
qed

lemma fresh_distinct_list:
 assumes "atom ` S \<sharp>* l"
 shows "S \<inter> set l = {}"
 using assms
 by (metis disjoint_iff_not_equal fresh_list_elem fresh_star_def image_eqI not_self_fresh)

lemma fresh_distinct_fv:
 assumes "atom ` S \<sharp>* l"
 shows "S \<inter> fv l = {}"
 using assms
 by (metis disjoint_iff_not_equal fresh_star_def fv_not_fresh image_eqI)

subsubsection \<open>Pure codomains\<close>

lemma domA_fv_pure:
  fixes \<Gamma> :: "('a::at_base \<times> 'b::pure) list"
  shows  "fv \<Gamma> = domA \<Gamma>"
  apply (induct \<Gamma>)
  apply simp
  apply (case_tac a)
  apply (simp)
  done

lemma domA_fresh_pure:
  fixes \<Gamma> :: "('a::at_base \<times> 'b::pure) list"
  shows  "x \<in> domA \<Gamma> \<longleftrightarrow> \<not>(atom x \<sharp> \<Gamma>)"
  unfolding domA_fv_pure[symmetric]
  by (auto simp add: fv_def fresh_def)

end
