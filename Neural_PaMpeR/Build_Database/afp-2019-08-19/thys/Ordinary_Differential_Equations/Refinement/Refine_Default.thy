theory Refine_Default
  imports
    Enclosure_Operations
    Weak_Set
begin

consts i_default::"interface \<Rightarrow> interface"

definition default_rel_internal: "default_rel d X = insert (None, d) ((\<lambda>(x, y). (Some x, y)) ` X)"
lemma default_rel_def: "\<langle>X\<rangle>default_rel d = insert (None, d) ((\<lambda>(x, y). (Some x, y)) ` X)"
  by (auto simp: relAPP_def default_rel_internal)
lemmas [autoref_rel_intf] = REL_INTFI[of "default_rel d" i_default for d]

lemma single_valued_default_rel[relator_props]:
  "single_valued R \<Longrightarrow> single_valued (\<langle>R\<rangle>default_rel d)"
  by (auto simp: default_rel_def intro!: relator_props) (auto simp: single_valued_def)

lemma
  mem_default_relI:
  assumes "a = None \<Longrightarrow> b = d"
  assumes "\<And>x. a = Some x \<Longrightarrow> (x, b) \<in> R"
  shows "(a, b) \<in> \<langle>R\<rangle>default_rel d"
  using assms image_iff
  by (force simp: default_rel_def)

lemma Some_mem_default_rel: "(Some x, y) \<in> \<langle>X\<rangle>default_rel d\<longleftrightarrow> (x, y) \<in> X"
  by (auto simp: default_rel_def)

lemma option_rel_inverse[simp]: "(\<langle>R\<rangle>option_rel)\<inverse> = \<langle>R\<inverse>\<rangle>option_rel"
  by (auto simp: option_rel_def)

lemma default_rel_split[autoref_rules]:
  assumes split_impl: "(split_impl, split_spec) \<in> A \<rightarrow> \<langle>B \<times>\<^sub>r A\<rangle>nres_rel"
  shows "(\<lambda>xs.
    case xs of None \<Rightarrow> SUCCEED
    | Some x \<Rightarrow> do {(r, s) \<leftarrow> split_impl x; RETURN (r, Some s)},
    split_spec) \<in>
    \<langle>A\<rangle>default_rel d \<rightarrow> \<langle>B \<times>\<^sub>r \<langle>A\<rangle>default_rel d\<rangle>nres_rel"
proof -
  have "split_impl a \<bind> (\<lambda>(r, s). RETURN (r, Some s))
    \<le> \<Down> (B \<times>\<^sub>r insert (None, d) ((\<lambda>(x, y). (Some x, y)) ` A)) (SPEC (\<lambda>(A, B). b \<subseteq> A \<union> B))"
    if "(a, b) \<in> A"
    for a b
  proof -
    have split_inresD:
      "\<exists>a. (c, a) \<in> B \<and> (\<exists>bb. (Some d, bb) \<in> (\<lambda>(x, y). (Some x, y)) ` A \<and> b \<subseteq> a \<union> bb)"
      if "inres (split_impl a) (c, d)"
      for c d
    proof -
      have "RETURN (c, d) \<le> \<Down> (B \<times>\<^sub>r A) (split_spec b)"
        using \<open>(a, b) \<in> A\<close> that split_impl
        by (auto simp: inres_def nres_rel_def dest!: fun_relD)
      then show ?thesis
        using \<open>(a, b) \<in> A\<close> that split_impl
        by (fastforce simp: split_spec_def elim!: RETURN_ref_SPECD)
    qed
    have "nofail (split_impl a)"
      using split_impl[param_fo, OF \<open>(a, b) \<in> A\<close>] le_RES_nofailI
      by (auto simp: split_spec_def nres_rel_def conc_fun_def)
    then show ?thesis
      using that split_impl
      by (fastforce simp: refine_pw_simps dest!: split_inresD intro!: pw_leI)
  qed
  then show ?thesis
    by (auto simp: split_spec_def default_rel_def
        intro!: nres_relI)
qed

lemma br_Some_O_default_rel_eq: "br Some top O \<langle>A\<rangle>default_rel d = A"
  by (auto simp: br_def default_rel_def)

definition [simp]: "op_Union_default = Union"

context includes autoref_syntax begin
lemma [autoref_op_pat]: "Union \<equiv> OP op_Union_default"
  by simp

lemma default_rel_Union[autoref_rules]:
  assumes sv: "PREFER single_valued A"
  assumes safe: "SIDE_PRECOND (\<forall>x \<in> X. x \<subseteq> d)"
  assumes xs: "(xs, X) \<in> \<langle>\<langle>A\<rangle>default_rel d\<rangle>list_wset_rel"
  assumes Union_A: "(concat, Union) \<in> \<langle>A\<rangle>list_wset_rel \<rightarrow> A"
  shows "(map_option concat (those xs), op_Union_default $ X) \<in> \<langle>A\<rangle>default_rel d"
  using xs
  apply (safe dest!: list_wset_relD intro!: mem_default_relI)
  subgoal using safe by (auto simp: default_rel_def)
  subgoal by (auto simp: default_rel_def those_eq_None_set_iff dest!: set_relD)[]
  subgoal
    by (auto simp: those_eq_Some_map_Some_iff image_mem_set_rel_iff br_Some_O_default_rel_eq list_wset_rel_def
        intro!: relcompI brI Union_A[param_fo])
  done

definition [simp]: "op_empty_default = {}"
lemma default_rel_empty[autoref_rules]:
  assumes "GEN_OP ei {} A"
  shows "(Some ei, op_empty_default) \<in> \<langle>A\<rangle>default_rel d"
  using assms by (auto simp: default_rel_def)

definition mk_default::"'a set \<Rightarrow> 'a set" where [refine_vcg_def, simp]: "mk_default x = x"

lemma mk_default[autoref_rules]:
  "(Some, mk_default) \<in> R \<rightarrow> \<langle>R\<rangle>default_rel d"
  by (auto simp: default_rel_def)

definition [refine_vcg_def]: "default_rep d X = SPEC (\<lambda>x. case x of None \<Rightarrow> X = d | Some r \<Rightarrow> X = r)"

lemma default_rep_op_pat[autoref_op_pat_def]: "default_rep d \<equiv> OP (default_rep d)"
  by (auto simp: )

lemma default_rep[autoref_rules]:
  "(\<lambda>x. RETURN x, default_rep d) \<in> (\<langle>R\<rangle>(default_rel d)) \<rightarrow> \<langle>\<langle>R\<rangle>option_rel\<rangle>nres_rel"
  by (force simp: default_rep_def nres_rel_def default_rel_def
      split: option.splits intro!: RETURN_SPEC_refine )

end

end