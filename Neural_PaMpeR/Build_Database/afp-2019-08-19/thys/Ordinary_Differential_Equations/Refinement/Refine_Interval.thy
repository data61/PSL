theory
  Refine_Interval
imports
  Refine_Unions
  Refine_Vector_List
  Refine_Hyperplane
  Refine_Invar
begin

subsubsection \<open>interval approximation of many\<close>

definition ivl_rep_of_sets::"'a::lattice set set \<Rightarrow> ('a \<times> 'a) nres" where
  "ivl_rep_of_sets (XS::'a set set) = SPEC (\<lambda>(i, s). i \<le> s \<and> (\<forall>X\<in>XS. X \<subseteq> {i..s}))"
lemmas [refine_vcg] = ivl_rep_of_sets_def[THEN eq_refl, THEN order.trans]

subsection \<open>Interval representation\<close>

consts i_ivl::"interface \<Rightarrow> interface"

context includes autoref_syntax begin

definition "set_of_ivl x = {fst x .. snd x}"

definition "set_of_lvivl ivl = (set_of_ivl (map_prod eucl_of_list eucl_of_list ivl)::'a::executable_euclidean_space set)"

definition ivl_rel::"('a \<times> 'b::ordered_euclidean_space) set \<Rightarrow> (('a \<times> 'a) \<times> 'b set) set" where
  ivl_rel_internal: "ivl_rel S = (S \<times>\<^sub>r S) O br set_of_ivl top"
lemma ivl_rel_def: "\<langle>S\<rangle>ivl_rel = (S \<times>\<^sub>r S) O br set_of_ivl top"
  unfolding relAPP_def ivl_rel_internal ..

lemmas [autoref_rel_intf] = REL_INTFI[of "ivl_rel" "i_ivl"]

lemma ivl_rel_sv[relator_props]: "single_valued R \<Longrightarrow> single_valued (\<langle>R\<rangle>ivl_rel)"
  unfolding relAPP_def
  by (auto simp: ivl_rel_internal intro!: relator_props)

definition [simp]: "op_atLeastAtMost_ivl = atLeastAtMost"
lemma [autoref_op_pat]: "atLeastAtMost \<equiv> OP op_atLeastAtMost_ivl"
  by simp

lemma atLeastAtMost_ivlrel[autoref_rules]:
  "(Pair, op_atLeastAtMost_ivl) \<in> A \<rightarrow> A \<rightarrow> \<langle>A\<rangle>ivl_rel"
  by (auto simp: br_def set_of_ivl_def ivl_rel_def intro!: prod_relI)

definition [refine_vcg_def]: "ivl_rep X = SPEC (\<lambda>(l, u). X = {l .. u})"

lemma ivl_rep_autoref[autoref_rules]: "(RETURN, ivl_rep) \<in> \<langle>A\<rangle>ivl_rel \<rightarrow> \<langle>A \<times>\<^sub>r A\<rangle>nres_rel"
  by (force intro!: nres_relI RETURN_SPEC_refine simp: ivl_rep_def ivl_rel_def br_def set_of_ivl_def)

lemma Inf_ivl_rel[autoref_rules]:
  fixes X::"'a::ordered_euclidean_space set"
  assumes "SIDE_PRECOND (X \<noteq> {})"
  assumes "(Xi, X) \<in> \<langle>A\<rangle>ivl_rel"
  shows "(fst Xi, Inf $ X) \<in> A"
  using assms
  by (auto simp: ivl_rel_def br_def set_of_ivl_def)

lemma Sup_ivl_rel[autoref_rules]:
  fixes X::"'a::ordered_euclidean_space set"
  assumes "SIDE_PRECOND (X \<noteq> {})"
  assumes "(Xi, X) \<in> \<langle>A\<rangle>ivl_rel"
  shows "(snd Xi, Sup $ X) \<in> A"
  using assms
  by (auto simp: ivl_rel_def br_def set_of_ivl_def)

definition "filter_empty_ivls_impl le ivls = [(i, s) \<leftarrow> ivls. le i s]"

lemma filter_empty_ivls_impl_simps[simp]:
  shows
    "filter_empty_ivls_impl le [] = []"
    "filter_empty_ivls_impl le (a # xs) =
      (if le (fst a) (snd a) then a#filter_empty_ivls_impl le xs else filter_empty_ivls_impl le xs)"
  by (auto simp: filter_empty_ivls_impl_def)

definition [simp]: "filter_empty_ivls X = X"

lemma clw_rel_empty_iff:
  assumes "single_valued A"
  assumes "(x, {}) \<in> A" "(xs, X) \<in> clw_rel A"
  shows "(x#xs, X) \<in> clw_rel A"
  using assms
  by (auto simp: lw_rel_def Union_rel_br elim!: single_valued_as_brE) (auto simp: br_def)

lemma
  empty_ivl_relD:
  "(a, Y) \<in> \<langle>A\<rangle>ivl_rel \<Longrightarrow> single_valued A \<Longrightarrow> (le, (\<le>)) \<in> A \<rightarrow> A \<rightarrow> bool_rel \<Longrightarrow> \<not> le (fst a) (snd a) \<Longrightarrow> Y = {}"
  by (fastforce simp: ivl_rel_def br_def set_of_ivl_def dest: fun_relD )

lemma union_clw_relI: "(set xs, YS) \<in> \<langle>A\<rangle>set_rel \<Longrightarrow> (xs, \<Union>YS) \<in> clw_rel (A)"
  apply (auto simp: clw_rel_def br_def )
  apply (auto simp: lw_rel_def Union_rel_br set_rel_def )
  apply (auto simp: br_def)
  done

lemma filter_empty_ivls_impl_mem_clw_rel_ivl_rel_iff:
  "(filter_empty_ivls_impl (\<le>) xs, X) \<in> clw_rel (\<langle>rnv_rel\<rangle>ivl_rel) \<longleftrightarrow> (xs, X) \<in> clw_rel (\<langle>rnv_rel\<rangle>ivl_rel)"
  by (force simp: lw_rel_def ivl_rel_def Union_rel_br filter_empty_ivls_impl_def
      set_of_ivl_def dest!: brD intro!: brI)

lemma filter_empty_ivls_eucl:
  "(filter_empty_ivls_impl (\<le>), filter_empty_ivls) \<in> clw_rel (\<langle>rnv_rel\<rangle>ivl_rel) \<rightarrow> clw_rel (\<langle>rnv_rel\<rangle>ivl_rel)"
  by (auto simp: filter_empty_ivls_impl_mem_clw_rel_ivl_rel_iff)

lemma filter_param[param]:
  "(filter, filter) \<in> (A \<rightarrow> bool_rel) \<rightarrow> \<langle>A\<rangle>list_rel \<rightarrow> \<langle>A\<rangle>list_rel"
  unfolding List.filter_def[abs_def]
  by parametricity

lemma prod_rel_comp_ivl_rel:
  assumes "single_valued A" "single_valued B"
  shows "(A \<times>\<^sub>r A) O \<langle>B\<rangle>ivl_rel = \<langle>A O B\<rangle>ivl_rel"
  using assms
  by (auto simp: ivl_rel_def set_of_ivl_def br_chain br_rel_prod
      elim!: single_valued_as_brE
      intro!:brI dest!: brD)

lemma filter_empty_ivls[autoref_rules]:
  assumes [THEN PREFER_sv_D, relator_props]: "PREFER single_valued A"
  assumes [THEN GEN_OP_D, param]: "GEN_OP le (\<le>) (A \<rightarrow> A \<rightarrow> bool_rel)"
  assumes xs: "(xs, X) \<in> clw_rel (\<langle>A\<rangle>ivl_rel)"
  shows "(filter_empty_ivls_impl le xs, filter_empty_ivls $ X) \<in> clw_rel (\<langle>A\<rangle>ivl_rel)"
proof -
  have "(filter_empty_ivls_impl le, filter_empty_ivls_impl (\<le>)) \<in> \<langle>A\<times>\<^sub>rA\<rangle>list_rel \<rightarrow> \<langle>A\<times>\<^sub>rA\<rangle>list_rel"
    unfolding filter_empty_ivls_impl_def
    by parametricity
  moreover
  have "(filter_empty_ivls_impl (\<le>), filter_empty_ivls) \<in> clw_rel (\<langle>rnv_rel\<rangle>ivl_rel) \<rightarrow> clw_rel (\<langle>rnv_rel\<rangle>ivl_rel)"
    by (rule filter_empty_ivls_eucl)
  ultimately have "(filter_empty_ivls_impl le, filter_empty_ivls) \<in>
    (\<langle>A \<times>\<^sub>r A\<rangle>list_rel \<rightarrow> \<langle>A \<times>\<^sub>r A\<rangle>list_rel) O (clw_rel (\<langle>rnv_rel\<rangle>ivl_rel) \<rightarrow> clw_rel (\<langle>rnv_rel\<rangle>ivl_rel))" ..
  also have "\<dots> \<subseteq> (\<langle>A \<times>\<^sub>r A\<rangle>list_rel O clw_rel (\<langle>rnv_rel\<rangle>ivl_rel)) \<rightarrow> (\<langle>A \<times>\<^sub>r A\<rangle>list_rel O clw_rel (\<langle>rnv_rel\<rangle>ivl_rel))"
    by (rule fun_rel_comp_dist)
  also have "(\<langle>A \<times>\<^sub>r A\<rangle>list_rel O clw_rel (\<langle>rnv_rel\<rangle>ivl_rel)) = clw_rel (\<langle>A\<rangle>ivl_rel)"
    unfolding Id_arbitrary_interface_def
    apply (subst list_rel_comp_Union_rel)
     apply (intro relator_props)
    apply (subst prod_rel_comp_ivl_rel)
     apply (intro relator_props)
     apply (intro relator_props)
    apply simp
    done
  finally show ?thesis using xs by (auto dest: fun_relD)
qed

definition [simp]: "op_inter_ivl = (\<inter>)"
lemma [autoref_op_pat]: "(\<inter>) \<equiv> OP op_inter_ivl"
  by simp
lemma inter_ivl_rel[autoref_rules]:
  assumes infi[THEN GEN_OP_D, param_fo]: "GEN_OP infi inf (A \<rightarrow> A \<rightarrow> A)"
  assumes supi[THEN GEN_OP_D, param_fo]:"GEN_OP supi sup (A \<rightarrow> A \<rightarrow> A)"
  shows "(\<lambda>(i, s). \<lambda>(i', s'). (supi i i', infi s s'), op_inter_ivl) \<in> \<langle>A\<rangle>ivl_rel \<rightarrow> \<langle>A\<rangle>ivl_rel \<rightarrow> \<langle>A\<rangle>ivl_rel"
  using assms
  by (fastforce simp: ivl_rel_def br_def set_of_ivl_def intro!: infi supi prod_relI)

definition [simp]: "op_inter_ivl_coll = (\<inter>)"
lemma [autoref_op_pat]: "(\<inter>) \<equiv> OP op_inter_ivl_coll"
  by simp
lemma inter_ivl_clw_aux:
  assumes sv: "single_valued A"
  assumes intr: "(intr, (\<inter>)) \<in> (\<langle>A\<rangle>ivl_rel \<rightarrow> \<langle>A\<rangle>ivl_rel \<rightarrow> \<langle>A\<rangle>ivl_rel)"
  shows "(\<lambda>xs y. map (intr y) xs, (\<inter>)) \<in> clw_rel (\<langle>A\<rangle>ivl_rel) \<rightarrow>  \<langle>A\<rangle>ivl_rel \<rightarrow> clw_rel (\<langle>A\<rangle>ivl_rel)"
  apply (rule fun_relI)
  apply (rule fun_relI)
  using sv
  apply (rule single_valued_as_brE)
  apply simp
  unfolding ivl_rel_def br_rel_prod br_chain prod_rel_id_simp Id_O_R
  apply (rule map_mem_clw_rel_br)
   apply (auto simp: set_of_ivl_def)
  subgoal for a b c d e f g h i j
    using intr[param_fo, of "(c, d)" "{f c .. f d}" "(i, j)" "{f i .. f j}"]
    apply (auto simp: lw_rel_def Union_rel_br ivl_rel_def set_of_ivl_def br_rel_prod br_chain)
    apply (auto simp: br_def set_of_ivl_def split_beta')
    apply (rule bexI) prefer 2 apply assumption
    apply simp
    by (metis (mono_tags, lifting) Int_iff atLeastAtMost_iff fst_conv snd_conv)
  subgoal for a b c d e f g h i j
    using intr[param_fo, of "(c, d)" "{f c .. f d}" "(i, j)" "{f i .. f j}"]
    apply (auto simp: lw_rel_def Union_rel_br ivl_rel_def set_of_ivl_def br_rel_prod br_chain)
    apply (auto simp: br_def set_of_ivl_def split_beta')
    by (metis (mono_tags, lifting) Int_iff atLeastAtMost_iff fst_conv snd_conv)+
  subgoal for a b c d e f g h
    using intr[param_fo, of "(c, d)" "{f c .. f d}" ]
    apply (auto simp: lw_rel_def Union_rel_br ivl_rel_def set_of_ivl_def br_rel_prod br_chain)
    apply (auto simp: br_def set_of_ivl_def split_beta')
    apply (rule bexI) prefer 2 apply assumption
    by (metis (mono_tags, lifting) Int_iff atLeastAtMost_iff fst_conv snd_conv)
  subgoal for a b c d e f g h
    using intr[param_fo, of "(c, d)" "{f c .. f d}" ]
    apply (auto simp: lw_rel_def Union_rel_br ivl_rel_def set_of_ivl_def br_rel_prod br_chain)
    apply (auto simp: br_def set_of_ivl_def split_beta')
    by (metis (mono_tags, lifting) fst_conv snd_conv)
  subgoal for a b c d e f g h
    using intr[param_fo, of "(c, d)" "{f c .. f d}" ]
    apply (auto simp: lw_rel_def Union_rel_br ivl_rel_def set_of_ivl_def br_rel_prod br_chain)
    apply (auto simp: br_def set_of_ivl_def split_beta')
    by (metis (mono_tags, lifting) fst_conv snd_conv)
  done

lemma inter_ivl_clw[autoref_rules]:
  assumes sv[THEN PREFER_sv_D]: "PREFER single_valued A"
  assumes intr[THEN GEN_OP_D]: "GEN_OP intr op_inter_ivl (\<langle>A\<rangle>ivl_rel \<rightarrow> \<langle>A\<rangle>ivl_rel \<rightarrow> \<langle>A\<rangle>ivl_rel)"
  assumes "GEN_OP le (\<le>) (A \<rightarrow> A \<rightarrow> bool_rel)"
  shows "(\<lambda>xs y. filter_empty_ivls_impl le (map (intr y) xs), op_inter_ivl_coll) \<in> clw_rel (\<langle>A\<rangle>ivl_rel) \<rightarrow> (\<langle>A\<rangle>ivl_rel) \<rightarrow> clw_rel (\<langle>A\<rangle>ivl_rel)"
  apply safe
  subgoal premises prems
    using filter_empty_ivls[OF assms(1,3), param_fo, OF inter_ivl_clw_aux[OF sv intr[unfolded op_inter_ivl_def], param_fo, OF prems]]
    by simp
  done

lemma ivl_rel_br: "\<langle>br a I\<rangle>ivl_rel = br (\<lambda>(x, y). set_of_ivl (a x, a y)) (\<lambda>(x, y). I x \<and> I y)"
  unfolding ivl_rel_def br_rel_prod br_chain
  by (simp add: split_beta' o_def)

lemma Inf_spec_ivl_rel[autoref_rules]:
  "(\<lambda>x. RETURN (fst x), Inf_spec) \<in> \<langle>A\<rangle>ivl_rel \<rightarrow> \<langle>A\<rangle>nres_rel"
  and Sup_spec_ivl_rel[autoref_rules]:
  "(\<lambda>x. RETURN (snd x), Sup_spec) \<in> \<langle>A\<rangle>ivl_rel \<rightarrow> \<langle>A\<rangle>nres_rel"
  by (force simp: Inf_spec_def Sup_spec_def nres_rel_def ivl_rel_def br_def set_of_ivl_def
      intro!: RETURN_SPEC_refine)+

abbreviation "lvivl_rel \<equiv> \<langle>lv_rel\<rangle>ivl_rel"

lemma set_of_lvivl: "length (l) = DIM('a::executable_euclidean_space) \<Longrightarrow>
    length u = DIM('a) \<Longrightarrow>
    ((l, u), set_of_lvivl (l, u)::'a set) \<in> lvivl_rel"
  by (force simp: set_of_lvivl_def ivl_rel_br ivl_rel_def lv_rel_def br_def)

lemma lvivl_rel_br: "lvivl_rel = br (\<lambda>(x, y). set_of_ivl (eucl_of_list x, eucl_of_list y::'a)) (\<lambda>(x, y). length x = DIM('a::executable_euclidean_space) \<and> length y = DIM('a))"
  unfolding lv_rel_def ivl_rel_br by (simp add: split_beta')


lemma disjoint_sets_nres:
  fixes X Y::"'a::executable_euclidean_space set"
  shows "do {
    (iX, sX) \<leftarrow> ivl_rep X;
    (iY, sY) \<leftarrow> ivl_rep Y;
    RETURN (list_ex (\<lambda>i. sX \<bullet> i < iY \<bullet> i \<or> sY \<bullet> i < iX \<bullet> i) Basis_list)
  } \<le> disjoint_sets X Y"
  by (force simp: Inf_spec_def Sup_spec_def disjoint_sets_def list_ex_iff eucl_le[where 'a='a]
    intro!: refine_vcg)

schematic_goal disjoint_sets_impl:
  fixes A::"(_ * 'a::executable_euclidean_space set) set"
  assumes [autoref_rules_raw]: "DIM_precond (TYPE('a)) n"
  assumes [autoref_rules]: "(ai, a::'a set) \<in> lvivl_rel"
  assumes [autoref_rules]: "(bi, b) \<in> lvivl_rel"
  shows "(nres_of (?f::?'r dres), disjoint_sets $ a $ b) \<in> ?R"
  unfolding autoref_tag_defs
  by (rule disjoint_sets_nres[THEN nres_rel_trans2]) autoref_monadic

concrete_definition disjoint_sets_impl for n ai bi uses disjoint_sets_impl
lemma disjoint_sets_impl_refine[autoref_rules]:
  "DIM_precond (TYPE('a::executable_euclidean_space)) n \<Longrightarrow>
  (\<lambda>ai bi. nres_of (disjoint_sets_impl n ai bi), disjoint_sets::'a set \<Rightarrow> _) \<in> lvivl_rel \<rightarrow> lvivl_rel \<rightarrow> \<langle>bool_rel\<rangle>nres_rel"
  using disjoint_sets_impl.refine by force

definition [simp]: "project_set_ivl X b y = do {
    CHECK (\<lambda>_. ()) (b \<in> set Basis_list \<or> -b \<in> set Basis_list);
    (i, s) \<leftarrow> ivl_rep X;
    RETURN (op_atLeastAtMost_ivl (i + (y - i \<bullet> b) *\<^sub>R b) (s + (y - s \<bullet> b) *\<^sub>R b):::\<langle>lv_rel\<rangle>ivl_rel)
  }"

schematic_goal project_set_ivl:
  fixes b::"'a::executable_euclidean_space" and y
  assumes [autoref_rules_raw]: "DIM_precond (TYPE('a)) n"
  assumes [autoref_rules]: "(Xi, X) \<in> \<langle>lv_rel\<rangle>ivl_rel"
  assumes [autoref_rules]: "(bi, b) \<in> lv_rel"
  assumes [autoref_rules]: "(yi, y) \<in> rnv_rel"
  shows "(nres_of (?f::?'r dres), project_set_ivl X b y) \<in> ?R"
  unfolding project_set_ivl_def
  by autoref_monadic
concrete_definition project_set_ivl_impl for n Xi bi yi uses project_set_ivl
lemma project_set_ivl_refine[autoref_rules]:
  "DIM_precond (TYPE('a)) n \<Longrightarrow>
    (\<lambda>Xi bi yi. nres_of (project_set_ivl_impl n Xi bi yi), project_set_ivl) \<in>
    \<langle>lv_rel\<rangle>ivl_rel \<rightarrow> (lv_rel::(_\<times>'a::executable_euclidean_space) set) \<rightarrow> rnv_rel \<rightarrow> \<langle>\<langle>lv_rel\<rangle>ivl_rel\<rangle>nres_rel"
  using project_set_ivl_impl.refine by force

lemma project_set_ivl_spec[le, refine_vcg]: "project_set_ivl X b y \<le>
  SPEC (\<lambda>R. abs b \<in> Basis \<and> (\<exists>i s. X = {i .. s} \<and> R = {i + (y - i \<bullet> b) *\<^sub>R b .. s + (y - s \<bullet> b) *\<^sub>R b}))"
proof -
  define b' where "b' \<equiv> abs b"
  then have "b \<in> Basis \<Longrightarrow> b' \<in> Basis"
    "- b \<in> Basis \<Longrightarrow> b' \<in> Basis"
    "b \<in> Basis \<Longrightarrow> b = b'"
    "-b \<in> Basis \<Longrightarrow> b = - b'"
    using Basis_nonneg by (fastforce)+
  then show ?thesis
    unfolding project_set_ivl_def
    by refine_vcg
      (auto 0 4 simp: subset_iff eucl_le[where 'a='a] algebra_simps inner_Basis)
qed

lemma projection_notempty:
  fixes b::"'a::executable_euclidean_space"
  assumes "b \<in> Basis \<or> -b \<in> Basis"
  assumes "x \<le> z"
  shows "x + (y - x \<bullet> b) *\<^sub>R b \<le> z + (y - z \<bullet> b) *\<^sub>R b"
proof -
  define b' where "b' \<equiv> - b"
  then have b_dest: "-b \<in> Basis \<Longrightarrow> b = -b' \<and> b' \<in> Basis"
    by simp
  show ?thesis using assms
    by (auto simp: eucl_le[where 'a='a] algebra_simps inner_Basis dest!: b_dest)
qed

end

definition restrict_to_halfspace::"'a::executable_euclidean_space sctn \<Rightarrow> 'a set \<Rightarrow> 'a set nres"
where
  "restrict_to_halfspace sctn X = do {
    CHECK (\<lambda>_. ()) (normal sctn \<in> set Basis_list \<or> - normal sctn \<in> set Basis_list);
    let y = pstn sctn;
    let b = normal sctn;
    (i, s) \<leftarrow> ivl_rep X;
    let i' = (if b \<le> 0 then (i + (min (y - i \<bullet> b) 0) *\<^sub>R b) else i);
    let s' = (if b \<ge> 0 then (s + (min (y - s \<bullet> b) 0) *\<^sub>R b) else s);
    RETURN ({i' .. s'}:::\<^sub>i\<langle>i_rnv\<rangle>\<^sub>ii_ivl)
  }"

context includes autoref_syntax begin

schematic_goal restrict_to_halfspace_impl:
  fixes b y
  assumes [autoref_rules_raw]: "DIM_precond (TYPE('a::executable_euclidean_space)) n"
  assumes [autoref_rules]: "(Xi, X) \<in> \<langle>lv_rel\<rangle>ivl_rel"
  assumes [autoref_rules]: "(sctni, sctn::'a sctn) \<in> \<langle>lv_rel\<rangle>sctn_rel"
  shows "(nres_of (?f::?'r dres), restrict_to_halfspace sctn X) \<in> ?R"
  unfolding restrict_to_halfspace_def[abs_def]
  by (autoref_monadic)
concrete_definition restrict_to_halfspace_impl for n sctni Xi uses restrict_to_halfspace_impl
lemma restrict_to_halfspace_impl_refine[autoref_rules]:
  "DIM_precond (TYPE('a::executable_euclidean_space)) n \<Longrightarrow>
    (\<lambda>sctni Xi. nres_of (restrict_to_halfspace_impl n sctni Xi), restrict_to_halfspace::'a sctn\<Rightarrow>_) \<in>
      \<langle>lv_rel\<rangle>sctn_rel \<rightarrow> \<langle>lv_rel\<rangle>ivl_rel \<rightarrow> \<langle>\<langle>lv_rel\<rangle>ivl_rel\<rangle>nres_rel"
  using restrict_to_halfspace_impl.refine by force
lemma restrict_to_halfspace[THEN order_trans, refine_vcg]:
  "restrict_to_halfspace sctn X \<le> SPEC (\<lambda>R. R = X \<inter> below_halfspace sctn)"
  unfolding restrict_to_halfspace_def
  apply (refine_vcg)
  subgoal premises prems for x a b
  proof -
    from prems obtain i where i: "i \<in> Basis" and disj: "normal sctn = i \<or> normal sctn = - i"
      by (auto simp: )
    note nn = Basis_nonneg[OF i]
    note nz = nonzero_Basis[OF i]
    have ne: "- i \<noteq> i" using nn nz
      by (metis antisym neg_le_0_iff_le)
    have nn_iff: "0 \<le> normal sctn \<longleftrightarrow> normal sctn = i"
      using disj nn
      by (auto)
    from prems have X: "X = {a .. b}" by auto
    from disj show ?thesis
      unfolding nn_iff
      apply (rule disjE)
      using nn nz ne
       apply (simp_all add: below_halfspace_def le_halfspace_def[abs_def])
      unfolding X using i
      by (auto simp: eucl_le[where 'a='a] min_def algebra_simps inner_Basis
          split: if_splits)
        (auto simp: algebra_simps not_le)
  qed
  done

lemma restrict_to_halfspaces_impl:
  "do {
    ASSUME (finite sctns);
    FOREACH\<^bsup>\<lambda>sctns' Y. Y = X \<inter> below_halfspaces (sctns - sctns')\<^esup> sctns restrict_to_halfspace X
  } \<le> restrict_to_halfspaces sctns X"
  unfolding restrict_to_halfspaces_def
  by (refine_vcg) (auto simp: halfspace_simps)

schematic_goal restrict_to_halfspaces_ivl:
  assumes [autoref_rules_raw]: "DIM_precond (TYPE('a::executable_euclidean_space)) n"
  assumes [autoref_rules]: "(Xi, X) \<in> \<langle>lv_rel\<rangle>ivl_rel"
  assumes sctns[autoref_rules]: "(sctnsi, sctns) \<in> sctns_rel"
  notes [simp] = list_set_rel_finiteD[OF sctns]
  shows "(nres_of (?f::?'r dres), restrict_to_halfspaces sctns X::'a set nres) \<in> ?R"
  by (rule nres_rel_trans2[OF restrict_to_halfspaces_impl]) autoref_monadic
concrete_definition restrict_to_halfspaces_ivl for n sctnsi Xi uses restrict_to_halfspaces_ivl
lemma restrict_to_halfspaces_impl_refine[autoref_rules]:
  "DIM_precond (TYPE('a::executable_euclidean_space)) n \<Longrightarrow>
  (\<lambda>sctni Xi. nres_of (restrict_to_halfspaces_ivl n sctni Xi), restrict_to_halfspaces) \<in>
      sctns_rel \<rightarrow> \<langle>(lv_rel::(_\<times>'a) set)\<rangle>ivl_rel \<rightarrow> \<langle>\<langle>lv_rel\<rangle>ivl_rel\<rangle>nres_rel"
  using restrict_to_halfspaces_ivl.refine[of n] by force

definition [simp]: "restrict_to_halfspaces_clw = restrict_to_halfspaces"
lemma restrict_to_halfspaces_clw:
  "do {
    XS \<leftarrow> sets_of_coll X;
    FORWEAK XS (RETURN op_empty_coll) (\<lambda>X. do {R \<leftarrow> restrict_to_halfspaces sctns X; RETURN (filter_empty_ivls (mk_coll R))})
      (\<lambda>X Y. RETURN (Y \<union> X))
  } \<le> restrict_to_halfspaces_clw sctns X"
  unfolding restrict_to_halfspaces_def restrict_to_halfspaces_clw_def
  by (refine_vcg FORWEAK_mono_rule[where
        I="\<lambda>XS R. \<Union>XS \<inter> below_halfspaces sctns \<subseteq> R \<and> R \<subseteq> X \<inter> below_halfspaces sctns"])
    auto
schematic_goal restrict_to_halfspaces_clw_rel:
  fixes X::"'a::executable_euclidean_space set"
  assumes [autoref_rules_raw]: "DIM_precond (TYPE('a)) n"
  assumes [autoref_rules]: "(Xi, X) \<in> clw_rel (\<langle>lv_rel\<rangle>ivl_rel)"
  assumes sctns[autoref_rules]: "(sctnsi, sctns) \<in> sctns_rel"
  notes [simp] = list_set_rel_finiteD[OF sctns]
  shows "(nres_of (?f::?'r dres), restrict_to_halfspaces_clw sctns X) \<in> ?R"
  by (rule nres_rel_trans2[OF restrict_to_halfspaces_clw]) autoref_monadic
concrete_definition restrict_to_halfspaces_clw_rel for n sctnsi Xi uses restrict_to_halfspaces_clw_rel
lemma restrict_to_halfspaces_clw_rel_refine[autoref_rules]:
  "DIM_precond (TYPE('a::executable_euclidean_space)) n \<Longrightarrow>
    (\<lambda>sctni Xi. nres_of (restrict_to_halfspaces_clw_rel n sctni Xi), restrict_to_halfspaces_clw) \<in>
      sctns_rel \<rightarrow> clw_rel (\<langle>lv_rel\<rangle>ivl_rel) \<rightarrow> \<langle>clw_rel (\<langle>(lv_rel::(_\<times>'a) set)\<rangle>ivl_rel)\<rangle>nres_rel"
  using restrict_to_halfspaces_clw_rel.refine by force

definition [simp]: "restrict_to_halfspaces_invar_clw = restrict_to_halfspaces"
lemma restrict_to_halfspaces_invar_clw_ref:
  "do {
    XS \<leftarrow> (sets_of_coll X);
    FORWEAK XS (RETURN op_empty_coll) (\<lambda>X. do {
        (X, i) \<leftarrow> get_invar a X;
        R \<leftarrow> restrict_to_halfspaces sctns X;
        ASSERT (R \<subseteq> a i);
        RETURN (with_invar i (filter_empty_ivls (mk_coll R)):::clw_rel (\<langle>I, lvivl_rel\<rangle>invar_rel a))
      }) (\<lambda>X Y. RETURN (Y \<union> X))
  } \<le> restrict_to_halfspaces_invar_clw sctns X"
  unfolding restrict_to_halfspaces_def restrict_to_halfspaces_invar_clw_def
  by (refine_vcg FORWEAK_mono_rule[where
        I="\<lambda>XS R. \<Union>XS \<inter> below_halfspaces sctns \<subseteq> R \<and> R \<subseteq> X \<inter> below_halfspaces sctns"])
    auto

schematic_goal restrict_to_halfspaces_invar_clw_impl:
  fixes X::"'a::executable_euclidean_space set"
  assumes [autoref_rules_raw]: "DIM_precond (TYPE('a)) n"
  assumes [autoref_rules]: "(Xi, X) \<in> clw_rel (\<langle>I, lvivl_rel\<rangle>invar_rel a)"
  assumes sctns[autoref_rules]: "(sctnsi, sctns) \<in> sctns_rel"
  notes [simp] = list_set_rel_finiteD[OF sctns]
  shows "(nres_of (?f::?'r dres), restrict_to_halfspaces_invar_clw sctns X) \<in> ?R"
  including art
  by (rule nres_rel_trans2[OF restrict_to_halfspaces_invar_clw_ref[where a=a and I=I]])
    (autoref_monadic)

concrete_definition restrict_to_halfspaces_invar_clw_impl for n sctnsi Xi uses restrict_to_halfspaces_invar_clw_impl
lemma restrict_to_halfspaces_invar_clw_refine[autoref_rules]:
  "DIM_precond (TYPE('a::executable_euclidean_space)) n \<Longrightarrow>
    (\<lambda>sctnsi Xi. nres_of (restrict_to_halfspaces_invar_clw_impl n sctnsi Xi), restrict_to_halfspaces_invar_clw::'a sctn set \<Rightarrow> _) \<in>
      sctns_rel \<rightarrow> clw_rel (\<langle>I, lvivl_rel\<rangle>invar_rel a) \<rightarrow> \<langle>clw_rel (\<langle>I, lvivl_rel\<rangle>invar_rel a)\<rangle>nres_rel"
  using restrict_to_halfspaces_invar_clw_impl.refine[of n _ _ a I] by force

abbreviation "below_invar_rel \<equiv> \<lambda>A. \<langle>\<langle>lv_rel\<rangle>sctn_rel, A\<rangle>invar_rel below_halfspace"
abbreviation "sbelow_invar_rel \<equiv> \<lambda>A. \<langle>\<langle>lv_rel\<rangle>sctn_rel, A\<rangle>invar_rel sbelow_halfspace"
abbreviation "plane_invar_rel \<equiv> \<lambda>A. \<langle>\<langle>lv_rel\<rangle>sctn_rel, A\<rangle>invar_rel plane_of"
abbreviation "belows_invar_rel \<equiv> \<lambda>A. \<langle>sctns_rel, A\<rangle>invar_rel below_halfspaces"
abbreviation "sbelows_invar_rel \<equiv> \<lambda>A. \<langle>sctns_rel, A\<rangle>invar_rel sbelow_halfspaces"

definition [simp]: "with_invar_on_invar = with_invar"
lemma with_invar_on_invar_impl[autoref_rules]:
  assumes "PREFER single_valued S"
  assumes "PREFER single_valued A"
  assumes "(sctni, sctn) \<in> S"
  assumes "GEN_OP uni (\<union>) (S \<rightarrow> S \<rightarrow> S)"
  assumes "(Xi, X) \<in> clw_rel (\<langle>S, A\<rangle>invar_rel a)"
  assumes "SIDE_PRECOND (X \<subseteq> a sctn)"
  assumes a_distrib: "SIDE_PRECOND (\<forall>x y. a (x \<union> y) = a x \<inter> a y)"
  shows "(map (\<lambda>(x, y). (x, uni sctni y)) Xi, with_invar_on_invar $ sctn $ X) \<in> clw_rel (\<langle>S, A\<rangle>invar_rel a)"
  using assms(1-6) a_distrib[unfolded autoref_tag_defs, rule_format]
  apply (auto simp: invar_rel_br intro!: map_mem_clw_rel_br elim!: single_valued_as_brE)
      apply (auto simp: lw_rel_def Union_rel_br)
      apply (auto simp: br_def)
    apply (metis (no_types, lifting) case_prod_conv)
   apply (drule_tac x=sctni and x' = sctn in fun_relD, force)
   apply (drule_tac x=b and x' = "\<alpha> b" in fun_relD, force)
   apply force
  apply (drule_tac x=sctni and x' = sctn in fun_relD, force)
  apply (drule_tac x=b and x' = "\<alpha> b" in fun_relD, force)
  apply safe
proof -
  fix \<alpha> :: "'a \<Rightarrow> 'b set" and invar :: "'a \<Rightarrow> bool" and \<alpha>' :: "'c \<Rightarrow> 'd set" and invara :: "'c \<Rightarrow> bool" and aa :: 'c and b :: 'a and x :: 'd
  assume a1: "x \<in> \<alpha>' aa"
  assume a2: "(aa, b) \<in> set Xi"
  assume a3: "(\<Union>x\<in>set Xi. case x of (x, s) \<Rightarrow> \<alpha>' x) \<subseteq> a (\<alpha> sctni)"
  assume a4: "\<forall>x\<in>set Xi. case x of (x, s) \<Rightarrow> invara x \<and> invar s \<and> \<alpha>' x \<subseteq> a (\<alpha> s)"
  assume a5: "\<And>x y. a (x \<union> y) = a x \<inter> a y"
  assume a6: "\<alpha> sctni \<union> \<alpha> b = \<alpha> (uni sctni b)"
  have f7: "invara aa \<and> invar b \<and> \<alpha>' aa \<subseteq> a (\<alpha> b)"
    using a4 a2 by fastforce
  have "x \<in> a (\<alpha> sctni)"
    using a3 a2 a1 by blast
  then show "x \<in> a (\<alpha> (uni sctni b))"
    using f7 a6 a5 a1 by (metis (full_types) Int_iff subsetCE)
qed

lemma
  set_of_ivl_union:
  fixes i1 i2 s1 s2::"'a::executable_euclidean_space"
  shows "set_of_ivl (i1, s1) \<union> set_of_ivl (i2, s2) \<subseteq> set_of_ivl (inf i1 i2, sup s1 s2)"
  by (auto simp: set_of_ivl_def)

lemma fold_set_of_ivl:
  fixes i s::"'a::executable_euclidean_space"
  assumes "\<And>i s. (i, s) \<in> set xs \<Longrightarrow> i \<le> s"
  assumes "i \<le> s"
  shows "\<Union> (set_of_ivl ` insert (i, s) (set xs)) \<subseteq>
      set_of_ivl (fold (\<lambda>(i1, s1) (i2, s2). (inf i1 i2, sup s1 s2)) xs (i, s))"
  using assms
proof (induction xs arbitrary: i s)
  case (Cons x xs i s)
  then show ?case
    apply (auto simp: set_of_ivl_def
        simp: split_beta' le_infI2 le_supI2 le_infI1 le_supI1)
    apply (metis (no_types, lifting) inf.absorb_iff2 inf_sup_ord(2) le_infE le_supI2)
    apply (metis (no_types, lifting) inf.absorb_iff2 inf_sup_ord(2) le_infE le_supI2)
     apply (metis (no_types, lifting) inf.absorb_iff2 inf_sup_ord(2) le_infE le_supI2)
    by (metis (no_types, lifting) inf_sup_absorb le_infI2 le_supI2)
qed simp

lemma fold_infsup_le:
  fixes i s::"'a::executable_euclidean_space"
  assumes "\<And>i s. (i, s) \<in> set xs \<Longrightarrow> i \<le> s"
  assumes "i \<le> s"
  shows "case (fold (\<lambda>(i1, s1) (i2, s2). (inf i1 i2, sup s1 s2)) xs (i, s)) of (i, s) \<Rightarrow> i \<le> s"
  using assms
proof (induction xs arbitrary: i s)
  case (Cons x xs i s)
  then show ?case
    by (auto simp: set_of_ivl_def
        simp: split_beta' le_infI2 le_supI2 le_infI1 le_supI1)
qed simp

definition "max_coord M (x::'a::executable_euclidean_space) =
  snd (fold (\<lambda>a (b, c). let d = abs x \<bullet> a in if d \<ge> b then (d, a) else (b, c)) (take M Basis_list) (0, 0))"

schematic_goal max_coord_autoref:
  assumes [autoref_rules_raw]: "DIM_precond TYPE('a::executable_euclidean_space) n"
  assumes [autoref_rules]: "(Xi, X::'a) \<in> lv_rel"
  assumes [autoref_rules]: "(Mi, M) \<in> nat_rel"
  shows "(?r, max_coord M X) \<in> lv_rel"
  unfolding max_coord_def
  by autoref
concrete_definition max_coord_lv_rel for n Mi Xi uses max_coord_autoref
lemma max_coord_lv_rel_refine[autoref_rules]:
  "DIM_precond TYPE('a::executable_euclidean_space) n \<Longrightarrow> (\<lambda>Mi Xi. max_coord_lv_rel n Mi Xi, max_coord::nat\<Rightarrow>'a\<Rightarrow>_) \<in> nat_rel \<rightarrow> lv_rel \<rightarrow> lv_rel"
  using max_coord_lv_rel.refine by force

definition "split_ivl_at_halfspace sctn1 x =
  do {
    (i, s) \<leftarrow> ivl_rep x;
    let sctn2 = Sctn (- normal sctn1) (- pstn sctn1);
    x1 \<leftarrow> restrict_to_halfspace sctn1 x;
    x2 \<leftarrow> restrict_to_halfspace sctn2 x;
    RETURN (x1, x2)
  }"

lemma split_ivl_at_halfspace[THEN order_trans, refine_vcg]:
  "split_ivl_at_halfspace sctn x \<le> split_spec_exact x"
  unfolding split_ivl_at_halfspace_def split_spec_exact_def
  by refine_vcg (auto simp: halfspace_simps)

schematic_goal split_ivl_at_halfspace_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE('a::executable_euclidean_space) n"
  assumes [autoref_rules]: "(Xi, X) \<in> lvivl_rel"
  assumes [autoref_rules]: "(sctni, sctn) \<in> \<langle>lv_rel\<rangle>sctn_rel"
  shows "(nres_of ?X, split_ivl_at_halfspace sctn (X::'a set)) \<in> \<langle>lvivl_rel \<times>\<^sub>r lvivl_rel\<rangle>nres_rel"
  unfolding split_ivl_at_halfspace_def
  by (autoref_monadic)
concrete_definition split_ivl_at_halfspace_impl for n sctni Xi uses split_ivl_at_halfspace_impl
lemma split_ivl_at_halfspace_impl_refine[autoref_rules]:
  "DIM_precond TYPE('a::executable_euclidean_space) n \<Longrightarrow>
    (\<lambda>sctni Xi. nres_of (split_ivl_at_halfspace_impl n sctni Xi), split_ivl_at_halfspace::_ \<Rightarrow> 'a set \<Rightarrow> _) \<in>
    \<langle>lv_rel\<rangle>sctn_rel \<rightarrow> lvivl_rel \<rightarrow> \<langle>lvivl_rel \<times>\<^sub>r lvivl_rel\<rangle>nres_rel"
  using split_ivl_at_halfspace_impl.refine
  by force

definition "split_spec_ivl M x =
  do {
    (i, s) \<leftarrow> ivl_rep x;
    let d = s - i;
    let b = max_coord M d;
    let m = (i \<bullet> b + s \<bullet> b)/2;
    split_ivl_at_halfspace (Sctn b m) x
  }"

lemma split_spec_ivl_split_spec_exact[THEN order_trans, refine_vcg]:
  "split_spec_ivl M x \<le> split_spec_exact x"
  unfolding split_spec_ivl_def split_spec_exact_def
  by refine_vcg

schematic_goal split_spec_exact_ivl_rel:
  assumes [autoref_rules_raw]: "DIM_precond TYPE('a::executable_euclidean_space) n"
  assumes [autoref_rules]: "(Xi, X) \<in> lvivl_rel"
  assumes [autoref_rules]: "(Mi, M) \<in> nat_rel"
  shows "(nres_of ?X, split_spec_ivl M (X::'a set)) \<in> \<langle>lvivl_rel \<times>\<^sub>r lvivl_rel\<rangle>nres_rel"
  unfolding split_spec_ivl_def
  by (autoref_monadic)
concrete_definition split_spec_exact_ivl_rel for n Mi Xi uses split_spec_exact_ivl_rel
lemma split_spec_exact_ivl_rel_refine[autoref_rules]:
  "DIM_precond TYPE('a::executable_euclidean_space) n \<Longrightarrow>
    (\<lambda>Mi Xi. nres_of (split_spec_exact_ivl_rel n Mi Xi), split_spec_ivl::nat \<Rightarrow> 'a set \<Rightarrow> _) \<in>
    nat_rel \<rightarrow> lvivl_rel \<rightarrow> \<langle>lvivl_rel \<times>\<^sub>r lvivl_rel\<rangle>nres_rel"
  using split_spec_exact_ivl_rel.refine
  by force

lemma [autoref_itype]: "op_set_isEmpty ::\<^sub>i \<langle>L, \<langle>A\<rangle>\<^sub>ii_ivl\<rangle>\<^sub>ii_coll \<rightarrow>\<^sub>i i_bool"
  by simp

lemma op_set_isEmpty_clw_rel_ivl_rel[autoref_rules]:
  assumes sv[THEN PREFER_sv_D, relator_props]: "PREFER single_valued A"
  assumes le[THEN GEN_OP_D, param_fo]: "GEN_OP le (\<le>) (A \<rightarrow> A \<rightarrow> bool_rel)"
  shows "(\<lambda>xs. filter_empty_ivls_impl le xs = [], op_set_isEmpty) \<in> clw_rel (\<langle>A\<rangle>ivl_rel) \<rightarrow> bool_rel"
  apply (rule fun_relI)
  subgoal premises prems for a b
    using filter_empty_ivls[OF assms prems] sv
    apply (auto simp: list_wset_rel_def ivl_rel_br Union_rel_br filter_empty_ivls_impl_def filter_empty_conv
        set_of_ivl_def split_beta' Id_arbitrary_interface_def
        dest!: brD elim!: single_valued_as_brE)
    subgoal for \<alpha> I x y
      using le[of x "\<alpha> x"  y "\<alpha> y"]
      apply (auto simp: br_def)
      done
    done
  done

lemma project_sets_FOREACH_refine:
  "do {
    Xs \<leftarrow> (sets_of_coll X ::: \<langle>\<langle>A\<rangle>list_wset_rel\<rangle>nres_rel);
    FORWEAK Xs (RETURN {}) (\<lambda>X. do { ivl \<leftarrow> project_set X b y; RETURN (mk_coll ivl)}) (\<lambda>a b. RETURN (a \<union> b))
  } \<le> project_sets X b y"
  unfolding project_sets_def autoref_tag_defs
  by (refine_vcg FORWEAK_mono_rule'[where I="\<lambda>S s. \<Union>S \<inter> {x. x \<bullet> b = y} \<subseteq> s \<and> s \<subseteq> {x. x \<bullet> b = y}"])
    auto


definition split_intersecting
  where [refine_vcg_def]: "split_intersecting X Y = SPEC (\<lambda>(R, S). X = R \<union> S \<and> X \<inter> Y \<subseteq> R \<and> S \<inter> Y = {})"

definition intersecting_sets where
  "intersecting_sets X Z = do {
    ZS \<leftarrow> sets_of_coll (Z);
    XS \<leftarrow> sets_of_coll (X);
    FORWEAK XS (RETURN (op_empty_coll, op_empty_coll)) (\<lambda>X. do {
      d \<leftarrow> FORWEAK ZS (RETURN True) (disjoint_sets X) (\<lambda>a b. RETURN (a \<and> b));
      RETURN (if d then (op_empty_coll, mk_coll X) else (mk_coll X, op_empty_coll))
    }) (\<lambda>(R, S). \<lambda>(R', S'). RETURN (R' \<union> R, S' \<union> S))
  }"

lemma intersecting_sets_spec:
  shows "intersecting_sets X Y \<le> split_intersecting X Y"
  unfolding intersecting_sets_def split_intersecting_def
    autoref_tag_defs
  apply (refine_vcg)
  apply (rule FORWEAK_mono_rule[where I="\<lambda>XS. \<lambda>(R, S). 
        R \<union> S \<subseteq> X \<and> \<Union>XS \<subseteq> R \<union> S \<and> \<Union>XS \<inter> Y \<subseteq> R \<and> S \<inter> Y = {}"])
  subgoal by (refine_vcg)
  subgoal for a b c
    by (refine_vcg FORWEAK_mono_rule[where I="\<lambda>ZS d. d \<longrightarrow> \<Union>ZS \<inter> c = {}"]) (auto split: if_splits)
  subgoal by (auto; blast)
  subgoal for a b c d e
    by (refine_vcg FORWEAK_mono_rule[where I="\<lambda>ZS d. d \<longrightarrow> \<Union>ZS \<inter> c = {}"]) (auto split: if_splits)
  subgoal by auto
  done

schematic_goal split_intersecting_impl:
  fixes A::"(_ \<times> 'a::executable_euclidean_space set) set"
  assumes [autoref_rules_raw]: "DIM_precond (TYPE('a)) n"
  assumes [autoref_rules]: "(Xi,X::'a set)\<in>clw_rel lvivl_rel"
  assumes [autoref_rules]: "(Zi,Z)\<in>clw_rel lvivl_rel"
  shows "(nres_of ?f, split_intersecting $ X $ Z)\<in>\<langle>clw_rel lvivl_rel \<times>\<^sub>r clw_rel lvivl_rel\<rangle>nres_rel"
  unfolding autoref_tag_defs
  apply (rule nres_rel_trans2[OF intersecting_sets_spec])
  unfolding intersecting_sets_def
  by autoref_monadic

concrete_definition split_intersecting_impl for Xi Zi uses split_intersecting_impl
lemmas [autoref_rules] = split_intersecting_impl.refine

definition inter_overappr where [refine_vcg_def]: "inter_overappr X Y = SPEC (\<lambda>R. X \<inter> Y \<subseteq> R \<and> R \<subseteq> X)"

lemma inter_overappr_impl: "do {(X, _) \<leftarrow> split_intersecting X Y; RETURN X} \<le> inter_overappr X Y"
  unfolding split_intersecting_def inter_overappr_def autoref_tag_defs
  by (refine_vcg) auto

schematic_goal inter_overappr_autoref:
  assumes [autoref_rules_raw]: "DIM_precond (TYPE('a::executable_euclidean_space)) n"
  assumes [autoref_rules]: "(Xi,X)\<in>clw_rel lvivl_rel"
  assumes [autoref_rules]: "(Zi,Z)\<in>clw_rel lvivl_rel"
  shows "(nres_of ?f, inter_overappr X Z::'a set nres)\<in>\<langle>clw_rel lvivl_rel\<rangle>nres_rel"
  unfolding autoref_tag_defs
  by (rule nres_rel_trans2[OF inter_overappr_impl]) (autoref_monadic)
concrete_definition inter_overappr_impl for Xi Zi uses inter_overappr_autoref
lemmas [autoref_rules] = inter_overappr_impl.refine[autoref_higher_order_rule(1)]

definition "sctnbounds_of_ivl M X = do {
    (l, u) \<leftarrow> ivl_rep X;
    let ls = (\<lambda>b. Sctn (- b) (- l \<bullet> b)) ` (set (take M Basis_list)::'a::executable_euclidean_space set);
    let us = (\<lambda>b. Sctn (b) (u \<bullet> b)) ` (set (take M Basis_list)::'a set);
    RETURN (ls \<union> us)
  }"

lemma sctnbounds_of_ivl[THEN order_trans, refine_vcg]:
  "sctnbounds_of_ivl M X \<le> SPEC (\<lambda>sctns. finite sctns \<and> (\<forall>sctn \<in> sctns. normal sctn \<noteq> 0))"
  unfolding sctnbounds_of_ivl_def
  by refine_vcg (auto dest!: in_set_takeD)

schematic_goal sctnbounds_of_ivl_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE('a::executable_euclidean_space) D"
  assumes [autoref_rules]: "(Xi, X::'a set) \<in> lvivl_rel" "(Mi, M) \<in> nat_rel"
  shows "(?f, sctnbounds_of_ivl $ M $ X) \<in> \<langle>sctns_rel\<rangle>nres_rel"
  unfolding autoref_tag_defs
  unfolding sctnbounds_of_ivl_def
  by autoref_monadic
concrete_definition sctnbounds_of_ivl_impl for Mi Xi uses sctnbounds_of_ivl_impl
lemma sctnbounds_of_ivl_impl_refine[autoref_rules]:
  "DIM_precond TYPE('a::executable_euclidean_space) D \<Longrightarrow>
  (\<lambda>Mi Xi. RETURN (sctnbounds_of_ivl_impl D Mi Xi), sctnbounds_of_ivl::nat \<Rightarrow> 'a set \<Rightarrow> _)
    \<in> nat_rel \<rightarrow> \<langle>lv_rel\<rangle>ivl_rel \<rightarrow> \<langle>sctns_rel\<rangle>nres_rel"
  using sctnbounds_of_ivl_impl.refine by force

lemma SPEC_True_mono: "b \<le> c \<Longrightarrow> SPEC (\<lambda>_. True) \<bind> (\<lambda>_. b) \<le> c"
  by (auto simp: bind_le_nofailI)

definition "split_ivls_at_halfspace sctn XS = do {
    XS \<leftarrow> sets_of_coll XS;
    FORWEAK XS (RETURN op_empty_coll) (\<lambda>X. do {
      (A, B) \<leftarrow> split_ivl_at_halfspace sctn X;
      RETURN (filter_empty_ivls (mk_coll A \<union> mk_coll B))
    }) (\<lambda>X X'. RETURN (X' \<union> X))
  }"

lemma split_ivls_at_halfspace[THEN order_trans, refine_vcg]:
  "split_ivls_at_halfspace sctn X \<le> SPEC (\<lambda>R. R = X)"
  unfolding split_ivls_at_halfspace_def
  by (refine_vcg FORWEAK_mono_rule[where I="\<lambda>Xi XS. \<Union>Xi \<subseteq> XS \<and> XS \<subseteq> X"]) auto

schematic_goal split_ivls_at_halfspace_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE('a::executable_euclidean_space) D"
  assumes [autoref_rules]: "(Xi, X::'a set) \<in> clw_rel lvivl_rel" "(sctni, sctn) \<in> \<langle>lv_rel\<rangle>sctn_rel"
  shows "(?f, split_ivls_at_halfspace $ sctn $ X) \<in> \<langle>clw_rel lvivl_rel\<rangle>nres_rel"
  unfolding autoref_tag_defs
  unfolding split_ivls_at_halfspace_def
  by autoref_monadic
concrete_definition split_ivls_at_halfspace_impl for sctni Xi uses split_ivls_at_halfspace_impl
lemma split_ivls_at_halfspace_impl_refine[autoref_rules]:
  "DIM_precond TYPE('a::executable_euclidean_space) D \<Longrightarrow>
  (\<lambda>Xi sctni. nres_of (split_ivls_at_halfspace_impl D Xi sctni), split_ivls_at_halfspace::'a sctn \<Rightarrow> _)
  \<in>  \<langle>lv_rel\<rangle>sctn_rel \<rightarrow> clw_rel (\<langle>lv_rel\<rangle>ivl_rel) \<rightarrow> \<langle>clw_rel (\<langle>lv_rel\<rangle>ivl_rel)\<rangle>nres_rel"
  using split_ivls_at_halfspace_impl.refine
  by force

definition "split_along_ivls M X IS = do {
    IS \<leftarrow> sets_of_coll IS;
    sctns \<leftarrow> FORWEAK IS (RETURN {}) (sctnbounds_of_ivl M) (\<lambda>sctns sctns'. RETURN (sctns' \<union> sctns));
    FOREACH\<^bsup>\<lambda>_ R. R = X\<^esup> sctns split_ivls_at_halfspace X
  }"

lemma split_along_ivls[THEN order_trans, refine_vcg]:"split_along_ivls M X IS \<le> SPEC (\<lambda>R. R = X)"
  unfolding split_along_ivls_def
  by (refine_vcg FORWEAK_mono_rule[where I="\<lambda>_ r. finite r"])

schematic_goal split_along_ivls_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE('a::executable_euclidean_space) D"
  assumes [autoref_rules]: "(Xi, X::'a set) \<in> clw_rel lvivl_rel" "(ISi, IS) \<in> clw_rel lvivl_rel"
      "(Mi, M) \<in> nat_rel"
  shows "(?f, split_along_ivls $ M $ X $ IS) \<in> \<langle>clw_rel lvivl_rel\<rangle>nres_rel"
  unfolding autoref_tag_defs
  unfolding split_along_ivls_def
  by autoref_monadic
concrete_definition split_along_ivls_impl uses split_along_ivls_impl
lemmas [autoref_rules] = split_along_ivls_impl.refine

definition "op_ivl_rep_of_set X =
  do { let X = (X); i \<leftarrow> Inf_spec X; s \<leftarrow> Sup_spec X; RETURN (inf i s, s)}"

definition "op_ivl_rep_of_sets XS =
  FORWEAK XS (RETURN (0, 0)) op_ivl_rep_of_set (\<lambda>(i, s) (i', s').
    RETURN (inf i i':::lv_rel, sup s s':::lv_rel))"

definition "op_ivl_of_ivl_coll XS =
  do {XS \<leftarrow> sets_of_coll XS;
    (l, u) \<leftarrow> FORWEAK XS (RETURN (0, 0)) ivl_rep (\<lambda>(i, s) (i', s').
      RETURN (inf i i':::lv_rel, sup s s':::lv_rel));
    RETURN (op_atLeastAtMost_ivl l u)
  }"

schematic_goal op_ivl_of_ivl_coll_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE('a::executable_euclidean_space) D"
  assumes [autoref_rules]: "(ISi, IS::'a::executable_euclidean_space set) \<in> clw_rel lvivl_rel"
  shows "(?f, op_ivl_of_ivl_coll IS) \<in> \<langle>lvivl_rel\<rangle>nres_rel"
  unfolding op_ivl_of_ivl_coll_def
  by autoref_monadic
concrete_definition op_ivl_of_ivl_coll_impl uses op_ivl_of_ivl_coll_impl
lemmas op_ivl_of_ivl_coll_impl_refine[autoref_rules] =
  op_ivl_of_ivl_coll_impl.refine[autoref_higher_order_rule (1)]

lemma is_empty_lvivl_rel[autoref_rules]:
  shows "(\<lambda>(a, b). \<not> list_all2 (\<le>) a b, is_empty) \<in> lvivl_rel \<rightarrow> bool_rel"
  using le_left_mono
  by (fastforce simp: ivl_rel_def br_def set_of_ivl_def dest: lv_rel_le[param_fo])

definition [simp]: "op_times_ivl a b = a \<times> b"

lemma [autoref_op_pat]: "a \<times> b \<equiv> OP op_times_ivl $ a $ b"
  by (auto simp: )

lemma op_times_ivl[autoref_rules]:
  "(\<lambda>(l, u) (l', u'). (l @ l', u @ u'), op_times_ivl) \<in> lvivl_rel \<rightarrow> lvivl_rel \<rightarrow> lvivl_rel"
  apply (auto simp: ivl_rel_def br_def intro!: rel_funI)
  subgoal for a b c d e f g h
    apply (rule relcompI[where b="((c, g), (d, h))"])
    by (auto simp: lv_rel_def br_def set_of_ivl_def)
  done

end

end