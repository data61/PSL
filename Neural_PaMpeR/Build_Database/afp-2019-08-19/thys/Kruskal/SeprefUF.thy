section \<open>Union Find in Sepref\<close>

theory SeprefUF
imports Refine_Imperative_HOL.Sepref "Separation_Logic_Imperative_HOL.Union_Find"
begin

(* TODO:  move to sepref/IICF *)

  type_synonym 'a per = "('a\<times>'a) set"


  definition "per_init D \<equiv> {(i,i) | i. i\<in>D}"
  definition [simp]: "per_compare R a b \<equiv> (a,b)\<in>R"

  definition per_init' :: "nat \<Rightarrow> nat per" where "per_init' n \<equiv> {(i,i) |i. i<n}"

  lemma per_init_of_nat_range: "per_init {i. i<N} = per_init' N"
    by (auto simp: per_init_def per_init'_def)

  lemma per_init_per[simp, intro!]:
    "part_equiv (per_init D)"
    unfolding per_init_def
    by (auto simp: part_equiv_def sym_def trans_def)

  lemma per_init_self: "(a,b)\<in>per_init D \<Longrightarrow> a=b"
    unfolding per_init_def by simp

  lemma per_union_impl: "(i,j)\<in>R \<Longrightarrow> (i,j)\<in>per_union R a b"
    by (auto simp: per_union_def)

  lemma per_union_related:
    "part_equiv R \<Longrightarrow> a\<in>Domain R \<Longrightarrow> b\<in>Domain  R \<Longrightarrow> (a,b)\<in>per_union R a b"
    unfolding per_union_def
    by (auto simp: part_equiv_refl)

  lemma part_equiv_refl':
    "part_equiv R \<Longrightarrow> x\<in>Domain R \<Longrightarrow> (x,x)\<in>R"
    using part_equiv_refl[of R x] by blast


  definition per_supset_rel :: "('a per \<times> 'a per) set" where
    "per_supset_rel
      \<equiv> {(p1,p2). p1 \<inter> Domain p2 \<times> Domain p2 = p2 \<and> p1 - (Domain p2 \<times> Domain p2) \<subseteq> Id}"

  lemma per_supset_rel_dom: "(p1, p2) \<in> per_supset_rel \<Longrightarrow> Domain p1 \<supseteq> Domain p2"
    by (auto simp: per_supset_rel_def)
  
  lemma per_supset_compare:
    "(p1, p2) \<in> per_supset_rel \<Longrightarrow> x1\<in>Domain p2 \<Longrightarrow> x2\<in>Domain p2 \<Longrightarrow> per_compare p1 x1 x2 \<longleftrightarrow> per_compare p2 x1 x2"
    by (auto simp: per_supset_rel_def)
  
  lemma per_supset_union: "(p1, p2) \<in> per_supset_rel \<Longrightarrow> x1\<in>Domain p2 \<Longrightarrow> x2\<in>Domain p2 \<Longrightarrow>
    (per_union p1 x1 x2, per_union p2 x1 x2) \<in> per_supset_rel"
    apply (clarsimp simp: per_supset_rel_def per_union_def Domain_unfold )
    apply (intro subsetI conjI)
     apply blast
    apply force
    done


  sepref_register per_init per_init' per_compare per_union

  lemma per_init_Domain[simp]: "Domain (per_init D) = D"
    by (auto simp: per_init_def)

  lemma per_init'_Domain[simp]: "Domain (per_init' N) = {i. i<N}"
    by (auto simp: per_init'_def)


  lemma per_init'_sepref_rule[sepref_fr_rules]: "(uf_init,RETURN o per_init') \<in> nat_assn\<^sup>k \<rightarrow>\<^sub>a is_uf"
    unfolding per_init'_def
    apply sepref_to_hoare
    by sep_auto

  lemma per_compare_sepref_rule[sepref_fr_rules]: "(uncurry2 uf_cmp, uncurry2 (RETURN ooo per_compare)) \<in>
    is_uf\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn"
    unfolding per_compare_def
    apply sepref_to_hoare
    by sep_auto

  lemma per_union_sepref_rule[sepref_fr_rules]: "(uncurry2 uf_union, uncurry2 (RETURN ooo per_union)) \<in>
    [\<lambda>((R,i),j). i\<in>Domain R \<and> j\<in>Domain R ]\<^sub>a is_uf\<^sup>d *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> is_uf"
    unfolding per_compare_def
    apply sepref_to_hoare
    by sep_auto



  definition "abs_test \<equiv> do {
    let u = per_init' (5::nat);
    let u = per_union u 1 2;
    let u = per_union u 2 3;
    RETURN (per_compare u 1 3)
  }"

  sepref_definition abs_test_impl is "uncurry0 abs_test" :: "unit_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn"
    unfolding abs_test_def
    by sepref

end
