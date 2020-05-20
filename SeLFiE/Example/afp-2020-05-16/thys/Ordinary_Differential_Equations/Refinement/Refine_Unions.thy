theory
  Refine_Unions
  imports
    Enclosure_Operations
    Weak_Set
begin

consts i_coll :: "interface \<Rightarrow> interface \<Rightarrow> interface" \<comment> \<open>collection of reachable sets\<close>

subsection \<open>composed set relations\<close>

definition Union_rel::"('l \<times> 'a set) set \<Rightarrow> ('a \<times> 'b set) set \<Rightarrow> ('l \<times> 'b set) set"
  where Union_rel_internal: "Union_rel L S = L O \<langle>S\<rangle>set_rel O br Union top"
lemmas [autoref_rel_intf] = REL_INTFI[of "Union_rel" "i_coll" for L S R]

lemma Union_rel_def: "\<langle>L, S\<rangle>Union_rel = L O \<langle>S\<rangle>set_rel O br Union top"
  unfolding relAPP_def Union_rel_internal ..

lemma single_valued_Union_rel[relator_props]:
  "single_valued L \<Longrightarrow> single_valued R \<Longrightarrow> single_valued (\<langle>L, R\<rangle>Union_rel)"
  unfolding relAPP_def
  by (auto simp: Union_rel_internal intro!: relator_props intro: single_valuedI)

lemma Union_rel_br: "\<langle>(br l lI), (br s sI)\<rangle>Union_rel = br (\<lambda>a. \<Union>(s ` (l a))) (\<lambda>a. lI a \<and> (\<forall>c \<in> l a. sI c))"
  unfolding Union_rel_def br_def
  apply (safe)
  subgoal by (force simp: set_rel_def)
  subgoal by (fastforce simp: set_rel_def)
  subgoal by (force simp: set_rel_def)
  subgoal for a
    by (auto intro!: relcompI[where b="l a"] relcompI[where b="s ` l a"] simp: set_rel_def)
  done

subsubsection \<open>Implementation of set as union of sets\<close>

context includes autoref_syntax begin

definition [simp]: "op_union_coll = (\<union>)"
lemma [autoref_op_pat]: "(\<union>) \<equiv> OP op_union_coll"
  by simp
lemma coll_union12[autoref_rules]:
  assumes unI[unfolded autoref_tag_defs]: "GEN_OP uni (\<union>) (L \<rightarrow> L \<rightarrow> L)"
  shows "(uni, op_union_coll) \<in> \<langle>L, S\<rangle>Union_rel \<rightarrow> \<langle>L, S\<rangle>Union_rel \<rightarrow> \<langle>L, S\<rangle>Union_rel"
  unfolding Union_rel_def
  by (auto simp: br_def intro!: relcompI[OF unI[param_fo]]
      relcompI[OF param_union[param_fo]])

definition "Id_arbitrary_interface = Id"
abbreviation "lw_rel \<equiv> \<langle>Id_arbitrary_interface\<rangle>list_wset_rel"
lemmas [autoref_rel_intf] = REL_INTFI[of Id_arbitrary_interface S for S::interface]
lemma single_valued_Id_arbitrary_interface[relator_props]: "single_valued Id_arbitrary_interface"
  by (auto simp: Id_arbitrary_interface_def)

lemma lw_rel_def: "lw_rel = br set top"
  by (simp add: list_wset_rel_def Id_arbitrary_interface_def)

abbreviation "clw_rel A \<equiv> \<langle>lw_rel, A\<rangle>Union_rel"

lemma clw_rel_def: "clw_rel A = lw_rel O \<langle>A\<rangle>set_rel O br Union top"
  unfolding Union_rel_def
  by simp

lemma op_wset_isEmpty_clw_rel[autoref_rules]:
  "(\<lambda>x. RETURN (x = []), isEmpty_spec) \<in> clw_rel A \<rightarrow> \<langle>bool_rel\<rangle>nres_rel"
  by (auto simp: nres_rel_def lw_rel_def Union_rel_def br_def set_rel_def)

lemma lift_clw_rel_map:
  assumes "single_valued A"
  assumes "single_valued B"
  assumes "(fi, f) \<in> A \<rightarrow> B"
  assumes f_distrib: "\<And>X. X \<subseteq> Range A \<Longrightarrow> f (\<Union>X) = \<Union>(f ` X)"
  shows "(map fi, f) \<in> clw_rel A \<rightarrow> clw_rel B"
  using assms(1-2)
  apply (auto simp: clw_rel_def)
  subgoal for xs X YY Z
    apply (rule relcompI[where b="fi ` X"])
     apply (force simp: lw_rel_def br_def)
    apply (rule relcompI[where b="f `  YY"])
     prefer 2
     apply (rule brI)
      apply (subst f_distrib[symmetric])
      apply (force simp: br_def set_rel_def)
      apply (force simp add: br_def)
    apply force
    using assms(3)
    apply parametricity
    done
  done

lemma list_rel_comp_Union_rel:
  "single_valued R \<Longrightarrow> (\<langle>R\<rangle>list_rel O \<langle>(\<langle>Id\<rangle>list_wset_rel), S\<rangle>Union_rel) =
    \<langle>(\<langle>Id\<rangle>list_wset_rel), (R O S)\<rangle>Union_rel"
  unfolding Union_rel_def
  unfolding O_assoc[symmetric]
  apply (subst list_rel_comp_list_wset_rel) apply simp apply (simp)
  by (simp add: O_assoc list_wset_rel_def set_rel_compp)

lemma Cons_mem_clw_rel_iff:
  assumes "single_valued A"
  shows "(x # xs, X) \<in> clw_rel A \<longleftrightarrow> (\<exists>Y YS. (x, Y) \<in> A \<and> (set xs, YS) \<in> \<langle>A\<rangle>set_rel \<and> X = Y \<union> \<Union>YS)"
  using assms
  unfolding clw_rel_def
  apply safe
  subgoal by (force simp add: br_def lw_rel_def insert_mem_set_rel_iff[OF assms])
  subgoal for Y YS
    apply (auto intro!: relcompI[where b="insert x (set xs)"] relcompI[where b="insert Y YS"]
        param_insert[param_fo]
        simp: lw_rel_def br_def)
    done
  done

lemma split_spec_exact_with_stepsize_autoref[autoref_rules]:
  assumes "PREFER single_valued A"
  shows "(\<lambda>xs. case xs of [] \<Rightarrow> SUCCEED | (x # xs) \<Rightarrow> RETURN (x, xs), split_spec_exact) \<in>
    clw_rel A \<rightarrow> \<langle>A \<times>\<^sub>r clw_rel A\<rangle>nres_rel"
proof -
  have "\<exists>a. (x, a) \<in> A \<and> (\<exists>b. (y, b) \<in> clw_rel A \<and> xs \<union> \<Union>YS = a \<union> b)"
    if "(x, xs) \<in> A" "(set y, YS) \<in> \<langle>A\<rangle>set_rel"
    for x y xs YS
    using that
    by (auto intro: exI[where x=xs] exI[where x="\<Union>YS"] simp: Union_rel_def lw_rel_def br_def)
  then show ?thesis
    using assms
    by (auto simp: split_spec_exact_def Cons_mem_clw_rel_iff
        intro!: nres_relI RETURN_SPEC_refine
        split: list.splits)
qed


definition "split_spec_coll = split_spec"
lemma clw_rel_split[autoref_rules]:
  assumes "PREFER single_valued A"
  shows "(\<lambda>xs. case xs of [] \<Rightarrow> SUCCEED | (x # xs) \<Rightarrow> RETURN (x, xs), split_spec_coll) \<in>
    clw_rel A \<rightarrow> \<langle>A \<times>\<^sub>r clw_rel A\<rangle>nres_rel"
proof -
  have "\<exists>a. (x, a) \<in> A \<and> (\<exists>b. (y, b) \<in> clw_rel A \<and> xs \<subseteq> a \<union> b \<and> \<Union>YS \<subseteq> a \<union> b)"
    if "(x, xs) \<in> A" "(set y, YS) \<in> \<langle>A\<rangle>set_rel"
    for x y xs YS
    using that
    by (auto intro: exI[where x=xs] exI[where x="\<Union>YS"] simp: Union_rel_def lw_rel_def br_def)
  then show ?thesis
    using assms
    by (auto simp: split_spec_coll_def split_spec_def Cons_mem_clw_rel_iff
        intro!: nres_relI RETURN_SPEC_refine
        split: list.splits)
qed

definition [simp]: "op_Union_coll = Union"
lemma [autoref_op_pat]: "Union \<equiv> OP op_Union_coll"
  by simp
lemma clw_rel_Union[autoref_rules]:
  includes autoref_syntax
  assumes [unfolded autoref_tag_defs, relator_props]: "PREFER single_valued A"
  shows "(concat, op_Union_coll) \<in> \<langle>clw_rel A\<rangle>list_wset_rel \<rightarrow> clw_rel A"
proof -
  have "(concat, concat) \<in> \<langle>\<langle>A\<rangle>list_rel\<rangle>list_rel \<rightarrow> \<langle>A\<rangle>list_rel" (is "_ \<in> ?L1 \<rightarrow> ?L2")
    by parametricity
  moreover have "(concat, op_Union_coll) \<in> \<langle>clw_rel Id\<rangle>list_wset_rel \<rightarrow> clw_rel Id"  (is "_ \<in> ?R1 \<rightarrow> ?R2")
    apply (auto simp: list_wset_rel_def Id_arbitrary_interface_def Union_rel_def
        br_chain o_def)
    apply (auto simp: br_def set_rel_def)
    apply force
    done
  ultimately have "(concat, op_Union_coll) \<in> (?L1 \<rightarrow> ?L2) O (?R1 \<rightarrow> ?R2)"
    by auto
  also have "\<dots> \<subseteq> (?L1 O ?R1) \<rightarrow> (?L2 O ?R2)" by (rule fun_rel_comp_dist)
  also have "?L1 O ?R1 = \<langle>clw_rel A\<rangle>list_wset_rel"
    apply (subst list_rel_comp_list_wset_rel)
    subgoal by (simp add: relator_props)
    subgoal using assms by (simp add: list_rel_comp_Union_rel Id_arbitrary_interface_def)
    done
  also have "?L2 O ?R2 = clw_rel A" using assms
    unfolding Id_arbitrary_interface_def
    by (subst list_rel_comp_Union_rel) simp_all
  finally show ?thesis .
qed

definition [simp]: "op_coll_is_empty \<equiv> is_empty"
lemma [autoref_op_pat]:  "is_empty \<equiv> OP op_coll_is_empty"
  by simp


lemma op_set_isEmpty_Union_rel[autoref_rules]:
  assumes "GEN_OP is_empty_i is_empty (A \<rightarrow> bool_rel)"
  shows "(\<lambda>xs. xs = [] \<or> list_all is_empty_i xs, op_coll_is_empty) \<in> clw_rel A \<rightarrow> bool_rel"
  using assms
  apply (auto simp: Union_rel_def lw_rel_def br_def set_rel_def op_set_isEmpty_def[abs_def]
      op_coll_is_empty_def
    list_all_iff dest: fun_relD)
  apply (fastforce dest: fun_relD)
  using fun_relD by fastforce

definition [simp]: "op_empty_coll = {}"
lemma Union_rel_empty[autoref_rules]:
  shows "([], op_empty_coll) \<in> clw_rel R"
  by (auto simp: br_def Union_rel_def
      intro!: relcompI[OF param_empty] relcompI[OF list_wset_autoref_empty])


definition mk_coll::"'a set \<Rightarrow> 'a set" where [refine_vcg_def, simp]: "mk_coll x = x"
lemma mk_coll[autoref_rules]:
  "PREFER single_valued R \<Longrightarrow> (\<lambda>x. [x], mk_coll) \<in> R \<rightarrow> clw_rel R"
  apply (rule fun_relI)
  subgoal for x x'
    by (auto simp: Union_rel_def list_wset_rel_def br_def set_rel_def single_valued_def
      Id_arbitrary_interface_def
      intro!: relcompI[where b="{xa. (x, xa) \<in> R}"] relcompI[where b="{x}"])
  done

lemma map_mem_clw_rel_br:
  assumes "\<Union>((\<lambda>x. a (f x)) ` set xs) = X"
  assumes "\<And>x. x \<in> set xs \<Longrightarrow> I (f x)"
  shows "(map f xs, X) \<in> clw_rel (br a I)"
  using assms
  by (auto simp: lw_rel_def Union_rel_br intro!: brI)

lemma clw_rel_br: "clw_rel (br a I) = br (\<lambda>xs. \<Union>(a ` (set xs))) (\<lambda>xs. Ball (set xs) I)"
  unfolding lw_rel_def Union_rel_br by simp

lemma sets_of_coll_autoref[autoref_rules]:
  shows "(\<lambda>x. RETURN x, sets_of_coll) \<in> clw_rel R \<rightarrow> \<langle>\<langle>R\<rangle>list_wset_rel\<rangle>nres_rel"
  by (auto simp: lw_rel_def Union_rel_def br_def set_rel_def list_wset_rel_def sets_of_coll_def
    Id_arbitrary_interface_def
      elim!: single_valued_as_brE
      intro!: nres_relI RETURN_SPEC_refine)
    auto

lemma Nil_mem_clw_rel_iff[simp]: "([], X) \<in> clw_rel W \<longleftrightarrow> X = {}"
  by (auto simp: Union_rel_def br_def set_rel_def lw_rel_def)

end

end