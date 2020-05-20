theory Refine_Invar
  imports
    Refine_Unions
    Refine_Intersection
begin

consts i_invar::"interface \<Rightarrow> interface \<Rightarrow> interface"

definition [simp]: "uninvar X = X"

definition with_invar::"'invar \<Rightarrow> 'a set \<Rightarrow> 'a set"
  where [simp]: "with_invar i X = X"

definition get_invar::"('invar \<Rightarrow> 'a set) \<Rightarrow> 'a set \<Rightarrow> ('a set \<times> 'invar) nres"
  where [refine_vcg_def]: "get_invar a X = SPEC (\<lambda>(Y, invar). Y = X \<and> Y \<subseteq> a invar)"
lemma get_invar_pat[autoref_op_pat_def]: "get_invar i \<equiv> Autoref_Tagging.OP (get_invar i)"
  by auto

definition split_with_invar::"('c \<Rightarrow> 'a set) \<Rightarrow> 'a set \<Rightarrow> (('a set \<times> 'c) \<times> 'a set) nres"
  where [refine_vcg_def]: "split_with_invar i X = SPEC (\<lambda>((Y, sctn), YS). X = Y \<union> YS \<and> Y \<subseteq> i sctn)"
lemma split_with_invar_pat[autoref_op_pat_def]:
  "split_with_invar i \<equiv> Autoref_Tagging.OP (split_with_invar i)"
  by auto

context includes autoref_syntax begin

definition invar_rel_internal:
  "invar_rel a X S = {((x, s'), y). \<exists>s. (s', s) \<in> X \<and> (x, y) \<in> S \<and> y \<subseteq> a s}"
lemma invar_rel_def: "\<langle>X, S\<rangle>invar_rel a = {((x, s'), y). \<exists>s. (s', s) \<in> X \<and> (x, y) \<in> S \<and> y \<subseteq> a s}"
  by (auto simp: invar_rel_internal relAPP_def)
lemmas [autoref_rel_intf] = REL_INTFI[of "invar_rel a" i_invar for a]

lemma invar_rel_br: "\<langle>(br a' I'), (br a I)\<rangle>invar_rel b =
  br (\<lambda>(x, s). a x) (\<lambda>(x, s). I x \<and> I' s \<and> (a x \<subseteq> b (a' s)))"
  by (auto simp: invar_rel_def br_def)

lemma sv_appr_invar_rel[relator_props]: "single_valued S \<Longrightarrow> single_valued (\<langle>X, S\<rangle>invar_rel a)"
  and sv_inter_rel[relator_props]: "single_valued S \<Longrightarrow> single_valued T \<Longrightarrow> single_valued (\<langle>T, S\<rangle>inter_rel)"
  unfolding relAPP_def
   apply (auto simp: invar_rel_internal inter_rel_internal single_valued_def set_rel_def)
     apply blast
    apply blast
  done

lemma with_invar_impl[autoref_rules]:
  assumes "(sctni, sctn) \<in> S"
  assumes "(Xi, X) \<in> clw_rel A"
  assumes "PREFER single_valued A"
  assumes "SIDE_PRECOND (X \<subseteq> a sctn)"
  shows "(map (\<lambda>x. (x, sctni)) Xi, with_invar $ sctn $ X) \<in> clw_rel (\<langle>S,A\<rangle>invar_rel a)"
  unfolding autoref_tag_defs
  using assms
  apply (auto simp: clw_rel_def elim!: single_valued_as_brE)
  subgoal for a i Y Z
    apply (rule relcompI)
    apply (force simp: lw_rel_def br_def)
    apply (rule relcompI[where b=Z])
    apply (auto simp: set_rel_def lw_rel_def invar_rel_def br_def)
    apply (metis Sup_le_iff)
    apply (metis Sup_le_iff)
    done
  done

lemma get_invar_autoref[autoref_rules]:
  "(\<lambda>x. RETURN x, get_invar a) \<in> \<langle>X, S\<rangle>invar_rel a \<rightarrow> \<langle>S \<times>\<^sub>r X\<rangle>nres_rel"
  by (force simp: get_invar_def invar_rel_def nres_rel_def intro!: RETURN_SPEC_refine)

lemma uninvar_autoref[autoref_rules]:
  assumes "PREFER single_valued A"
  assumes "PREFER single_valued X"
  shows "(map fst, uninvar) \<in> clw_rel (\<langle>X, A\<rangle>invar_rel b) \<rightarrow> clw_rel A"
  using assms
  by (force simp: lw_rel_def Union_rel_br invar_rel_br elim!: single_valued_as_brE
      dest!: brD
      intro!: brI)

abbreviation "splitbysndimpl xs \<equiv> do {
  let s = snd (hd xs);
  let (ys, zs) = List.partition (\<lambda>(_, sctn). sctn = s) xs;
  RETURN ((map fst ys, s), zs)
}"

lemma split_with_invar_autoref[autoref_rules]:
  assumes "PREFER single_valued A"
  assumes "PREFER single_valued S"
  assumes "(xs, X) \<in> clw_rel (\<langle>S, A\<rangle>invar_rel a)"
  shows
    "(if xs \<noteq> [] then do { ((xs, sctn), ys) \<leftarrow> splitbysndimpl xs; RETURN ((xs, sctn), ys) } else SUCCEED,
    split_with_invar a $ X) \<in>
    \<langle>(clw_rel A \<times>\<^sub>r S) \<times>\<^sub>r clw_rel (\<langle>S, A\<rangle>invar_rel a)\<rangle>nres_rel"
  using assms
  by (fastforce simp: Let_def split_with_invar_def split_beta'
      lw_rel_def Union_rel_br ex_br_conj_iff invar_rel_br
      elim!: single_valued_as_brE
      intro!: nres_relI RETURN_SPEC_refine
      dest!: brD)

end

definition
  "explicit_sctn_set po X0 =
    do {
      e \<leftarrow> isEmpty_spec X0;
      (_, _, Xis) \<leftarrow> WHILE\<^bsup>\<lambda>(e, X, Y).
          (e \<longrightarrow> X = {}) \<and>
          X0 = X \<union> (\<Union>(sctn, IS)\<in>Y. IS) \<and>
          (\<forall>(sctn, IS) \<in> Y. IS \<subseteq> po sctn)\<^esup>
        (\<lambda>(e, X, Y). \<not>e)
        (\<lambda>(e, X, Y).
          do {
            ((S, sctn), X') \<leftarrow> split_with_invar po X;
            e \<leftarrow> isEmpty_spec X';
            RETURN (e, X', insert (sctn, S) Y)
          }
        )
        (e,
          X0,
          {});
      RETURN Xis
    }"
lemma explicit_sctn_set_pat[autoref_op_pat_def]: "explicit_sctn_set po \<equiv> Autoref_Tagging.OP (explicit_sctn_set po)"
  by auto

context includes autoref_syntax begin

lemma pfi: "PREFER single_valued R \<Longrightarrow> ((#), OP insert ::: R \<rightarrow> \<langle>R\<rangle>list_wset_rel \<rightarrow> \<langle>R\<rangle>list_wset_rel) \<in> R \<rightarrow> \<langle>R\<rangle>list_wset_rel \<rightarrow> \<langle>R\<rangle>list_wset_rel"
  using list_set_autoref_insert[of R]
  by auto

schematic_goal explicit_sctn_setc:
  fixes po :: "'d \<Rightarrow> 'a::executable_euclidean_space set"
  assumes [THEN PREFER_sv_D, relator_props]: "PREFER single_valued A"
  assumes [THEN PREFER_sv_D, relator_props]: "PREFER single_valued S"
  assumes [autoref_rules]: "(XSi, XS) \<in> clw_rel (\<langle>S, A\<rangle>invar_rel po)"
  shows "(nres_of ?f, explicit_sctn_set po $ XS) \<in> \<langle>\<langle>S \<times>\<^sub>r clw_rel A\<rangle>list_wset_rel\<rangle>nres_rel"
  unfolding autoref_tag_defs
  unfolding explicit_sctn_set_def
  by autoref_monadic

concrete_definition explicit_sctn_setc for XSi uses explicit_sctn_setc
lemmas [autoref_rules] = explicit_sctn_setc.refine

lemma explicit_sctn_set[THEN order_trans, refine_vcg]:
  "explicit_sctn_set po X \<le> SPEC (\<lambda>R. X = (\<Union>(sctn, IS) \<in> R. IS) \<and> (\<forall>(sctn, IS) \<in> R. IS \<subseteq> po sctn))"
  unfolding explicit_sctn_set_def
  by (refine_vcg) (auto simp: split_beta' subset_iff)
end

end