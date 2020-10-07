theory Refine_Intersection
imports Refine_Unions
begin

consts i_inter::"interface \<Rightarrow> interface \<Rightarrow> interface"
hide_const (open) Impl_Uv_Set.inter_rel

definition inter_rel_internal: "inter_rel AA BB = {((a, b), A \<inter> B)|a b A B. (a, A) \<in> AA \<and> (b, B) \<in> BB}"
lemma inter_rel_def: "\<langle>AA, BB\<rangle>inter_rel = {((a, b), A \<inter> B)|a b A B. (a, A) \<in> AA \<and> (b, B) \<in> BB}"
  by (auto simp: inter_rel_internal relAPP_def)
lemmas [autoref_rel_intf] = REL_INTFI[of inter_rel i_inter]

lemma inter_rel_br: "\<langle>(br a I), (br b J)\<rangle>inter_rel = br (\<lambda>(x, y). a x \<inter> b y) (\<lambda>x. I (fst x) \<and> J (snd x))"
  by (auto simp: inter_rel_def br_def)

definition mk_inter::"'a set \<Rightarrow> 'a set \<Rightarrow> 'a set"
  where [simp]: "mk_inter \<equiv> \<lambda>X Y. X \<inter> Y"

definition mk_inter_coll::"'a set \<Rightarrow> 'a set \<Rightarrow> 'a set"
where [simp]: "mk_inter_coll \<equiv> \<lambda>X Y. X \<inter> Y"

context includes autoref_syntax begin
lemma [autoref_op_pat]: "mk_inter \<equiv> OP (mk_inter)"
  by simp
lemma [autoref_op_pat]: "mk_inter \<equiv> OP (mk_inter_coll)"
  by simp
end

lemma inter_plane_clw_autoref[autoref_rules]:
  assumes "PREFER single_valued A"
  assumes "PREFER single_valued B"
  shows "(\<lambda>xs sctni. map (\<lambda>x. (x, sctni)) xs, mk_inter_coll) \<in> clw_rel A \<rightarrow> B \<rightarrow> clw_rel (\<langle>A,B\<rangle>inter_rel)"
  using assms
  by (fastforce
      intro!: nres_relI RETURN_SPEC_refine brI
      dest!: brD
      elim!: single_valued_as_brE
      simp: RETURN_RES_refine_iff inter_rel_br Union_rel_br lw_rel_def)

lemma inter_plane_autoref[autoref_rules]:
  assumes "PREFER single_valued A"
  assumes "PREFER single_valued B"
  shows "(\<lambda>x sctn. (x, sctn), mk_inter) \<in> A \<rightarrow> B \<rightarrow> \<langle>A,B\<rangle>inter_rel"
  using assms
  by (fastforce
      intro!: nres_relI RETURN_SPEC_refine brI
      dest!: brD
      elim!: single_valued_as_brE
      simp: RETURN_RES_refine_iff inter_rel_br Union_rel_br lw_rel_def)

definition unintersect::"'a set \<Rightarrow> 'a set nres"
  where [refine_vcg_def]: "unintersect X = SPEC (\<lambda>R. X \<subseteq> R)"

definition unintersect_coll::"'a set \<Rightarrow> 'a set nres"
  where [refine_vcg_def]: "unintersect_coll X = SPEC (\<lambda>R. X \<subseteq> R)"

definition unintersect2::"'a set \<Rightarrow> 'a set nres"
  where [refine_vcg_def]: "unintersect2 X = SPEC (\<lambda>R. X \<subseteq> R)"

definition unintersect_coll2::"'a set \<Rightarrow> 'a set nres"
  where [refine_vcg_def]: "unintersect_coll2 X = SPEC (\<lambda>R. X \<subseteq> R)"

lemma unintersect_clw_impl[autoref_rules]:
  assumes "PREFER single_valued A"
  assumes "PREFER single_valued B"
  shows "(\<lambda>xs. RETURN ((map fst) xs), unintersect_coll) \<in> clw_rel (\<langle>A,B\<rangle>inter_rel) \<rightarrow> \<langle>clw_rel A\<rangle>nres_rel"
  using assms
  by (auto intro!: nres_relI RETURN_SPEC_refine elim!: single_valued_as_brE
      simp: unintersect_coll_def inter_rel_br Union_rel_br lw_rel_def)
    (auto simp: br_def)

lemma unintersect_impl[autoref_rules]:
  assumes "PREFER single_valued A"
  assumes "PREFER single_valued B"
  shows "(\<lambda>x. RETURN (fst x), unintersect) \<in> (\<langle>A,B\<rangle>inter_rel) \<rightarrow> \<langle>A\<rangle>nres_rel"
  using assms
  by (auto intro!: nres_relI RETURN_SPEC_refine elim!: single_valued_as_brE
      simp: unintersect_def inter_rel_br Union_rel_br lw_rel_def)
    (auto simp: br_def)

lemma unintersect_clw2_impl[autoref_rules]:
  assumes "PREFER single_valued A"
  assumes "PREFER single_valued B"
  shows "(\<lambda>xs. RETURN ((map snd) xs), unintersect_coll2) \<in> clw_rel (\<langle>A,B\<rangle>inter_rel) \<rightarrow> \<langle>clw_rel B\<rangle>nres_rel"
  using assms
  by (auto intro!: nres_relI RETURN_SPEC_refine elim!: single_valued_as_brE
      simp: unintersect_coll2_def inter_rel_br Union_rel_br lw_rel_def)
    (auto simp: br_def)

lemma unintersect2_impl[autoref_rules]:
  assumes "PREFER single_valued A"
  assumes "PREFER single_valued B"
  shows "(\<lambda>x. RETURN (snd x), unintersect2) \<in> (\<langle>A,B\<rangle>inter_rel) \<rightarrow> \<langle>B\<rangle>nres_rel"
  using assms
  by (auto intro!: nres_relI RETURN_SPEC_refine elim!: single_valued_as_brE
      simp: unintersect2_def inter_rel_br Union_rel_br lw_rel_def)
    (auto simp: br_def)

definition get_inter::"'a set \<Rightarrow> ('a set \<times> 'a set) nres"
  where [refine_vcg_def]: "get_inter X = SPEC (\<lambda>(Y, Z). X = Y \<inter> Z)"

lemma get_inter_autoref[autoref_rules]:
  "(\<lambda>x. RETURN x, get_inter) \<in> \<langle>X,S\<rangle>inter_rel \<rightarrow> \<langle>X \<times>\<^sub>r S\<rangle>nres_rel"
  by (force simp: get_inter_def inter_rel_def nres_rel_def intro!: RETURN_SPEC_refine)

definition split_by_inter::"'a set \<Rightarrow> ('a set \<times> 'a set) nres"
  where [refine_vcg_def]: "split_by_inter X = SPEC (\<lambda>(Y, YS). X = Y \<union> YS)"

context includes autoref_syntax begin
lemma split_by_inter_appr_plane_autoref[autoref_rules]:
  assumes "PREFER single_valued A"
  assumes "PREFER single_valued S"
  assumes "(xs, X) \<in> clw_rel (\<langle>A,S\<rangle>inter_rel)"
  shows
    "(let (a, b) = List.partition (\<lambda>(_, sctn). sctn = snd (hd xs)) xs in RETURN (a, b),
    split_by_inter $ X) \<in>
    \<langle>clw_rel (\<langle>A, S\<rangle>inter_rel) \<times>\<^sub>r clw_rel (\<langle>A, S\<rangle>inter_rel)\<rangle>nres_rel"
  using assms
  by (fastforce simp: Let_def split_by_inter_def split_beta'
      lw_rel_def Union_rel_br inter_rel_br ex_br_conj_iff Id_br[where 'a="'a sctn"]
      elim!: single_valued_as_brE
      intro!: nres_relI RETURN_SPEC_refine
      dest!: brD)

end

end