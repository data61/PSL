theory Refine_ScaleR2
  imports
    Refine_Unions
    Refine_Interval
    Refine_String
begin

definition "scaleR2 l u X = (\<lambda>(r, (x, y)). (x, r *\<^sub>R y)) ` (ereal -` {l .. u} \<times> X)"

lemma scaleR2_1_1[simp]: "scaleR2 1 1 = (\<lambda>x::(_\<times>'x::real_vector)set. x)"
  by (force simp: scaleR2_def[abs_def] image_def vimage_def)

consts i_scaleR2::"interface\<Rightarrow>interface"

abbreviation "ereal_rel \<equiv> (Id::ereal rel)"

definition scaleR2_rel where scaleR2_rel_internal:
  "scaleR2_rel A = ((ereal_rel \<times>\<^sub>r ereal_rel) \<times>\<^sub>r A) O
    br (\<lambda>((l, u), X). scaleR2 l u X) (\<lambda>((l, u), _). ereal -` {l..u} \<noteq> {})"

definition [refine_vcg_def]: "scaleR2_rep X = SPEC (\<lambda>((l, u), Y). ereal -` {l..u} \<noteq> {} \<and> X = scaleR2 l u Y)"

definition [refine_vcg_def]: "scaleRe_ivl_spec l u X = SPEC (\<lambda>Y. Y = scaleR2 l u X)"

definition [simp]: "op_image_fst_colle = (`) fst"

definition [simp]: "op_image_fste = (`) fst"

definition "scaleR2_rep_coll X = do {
  XS \<leftarrow> sets_of_coll X;
  FORWEAK XS (RETURN ((0, 0), op_empty_coll)) (\<lambda>X. do {
    ((l, u), Y) \<leftarrow> scaleR2_rep X;
    RETURN ((l, u), mk_coll Y)
  }) (\<lambda>((l, u), Y) ((l', u'), Y'). RETURN ((inf l' l, sup u' u), Y' \<union> Y))
  }"

abbreviation "elvivl_rel \<equiv> \<langle>lvivl_rel\<rangle>scaleR2_rel"

definition [simp]: "op_times_UNIV_coll X = X \<times> UNIV"

definition [simp]: "op_inter_fst X Y = X \<inter> Y \<times> UNIV"

definition "scaleRe_ivl_coll_spec l u X = do {
    XS \<leftarrow> sets_of_coll X;
    FORWEAK XS (RETURN op_empty_coll)
      (\<lambda>X. do {I \<leftarrow> scaleRe_ivl_spec l u X; RETURN (mk_coll I)})
      (\<lambda>X X'. RETURN (X' \<union> X))
  }"

definition "op_inter_fst_ivl_scaleR2 X Y = do {
    ((l, u), X) \<leftarrow> scaleR2_rep X;
    (i, s) \<leftarrow> ivl_rep (op_inter_fst X Y);
    let R = op_inter_fst (op_atLeastAtMost_ivl i s) Y;
    scaleRe_ivl_coll_spec l u (filter_empty_ivls (mk_coll R))
  }"

definition "op_inter_fst_ivl_coll_scaleR2 X Y = do {
    Xs \<leftarrow> sets_of_coll X;
    FORWEAK Xs (RETURN op_empty_coll) (\<lambda>X. op_inter_fst_ivl_scaleR2 X Y) (\<lambda>X X'. RETURN (X' \<union> X))
  }"

definition [refine_vcg_def]: "op_image_fst_ivl X = SPEC (\<lambda>R. R = fst ` X)"

definition "op_image_fst_ivl_coll X = do {
  Xs \<leftarrow> sets_of_coll X;
  FORWEAK Xs (RETURN op_empty_coll) (\<lambda>X. do {i \<leftarrow> op_image_fst_ivl X; RETURN (mk_coll i)}) (\<lambda>X' X. RETURN (X' \<union> X))
  }"

lemma scaleR2_rel_def:
  "\<langle>A\<rangle>scaleR2_rel = ((ereal_rel \<times>\<^sub>r ereal_rel) \<times>\<^sub>r A) O
    br (\<lambda>((l, u), X). scaleR2 l u X) (\<lambda>((l, u), _). ereal -` {l..u} \<noteq> {})"
  by (auto simp: relAPP_def scaleR2_rel_internal)
lemmas [autoref_rel_intf] = REL_INTFI[of scaleR2_rel i_scaleR2]

lemma fst_scaleR2_image[simp]: "ad \<le> ereal r \<Longrightarrow> ereal r \<le> bd \<Longrightarrow> fst ` scaleR2 ad bd be = fst ` be"
  by (cases ad; cases bd; force simp: scaleR2_def image_image split_beta' vimage_def)

lemma scaleR2_rel_br: "\<langle>br a I\<rangle>scaleR2_rel =
  br (\<lambda>((x, xa), y). scaleR2 x xa (a y)) (\<lambda>((l, u), y). I y \<and> ereal -` {l..u} \<noteq> {})"
  unfolding scaleR2_rel_def
  unfolding Id_br br_rel_prod br_chain o_def
  by (auto simp: split_beta')

context includes autoref_syntax begin

lemma [autoref_rules]:
  "(sup, sup) \<in> ereal_rel \<rightarrow> ereal_rel \<rightarrow> ereal_rel"
  "(inf, inf) \<in> ereal_rel \<rightarrow> ereal_rel \<rightarrow> ereal_rel"
  by auto

lemma [autoref_rules]:
  "(ereal, ereal) \<in> rnv_rel \<rightarrow> ereal_rel"
  "((*), (*)) \<in> ereal_rel \<rightarrow> ereal_rel \<rightarrow> ereal_rel"
  by auto

lemma [autoref_rules]: "(\<infinity>, \<infinity>) \<in> ereal_rel"
  by auto

lemma lift_scaleR2:
  "(\<lambda>(lu, x). (lu, fi x), f) \<in> \<langle>A\<rangle>scaleR2_rel \<rightarrow> \<langle>B\<rangle>scaleR2_rel"
  if "(fi, f) \<in> A \<rightarrow> B"
  "\<And>l u x. x \<in> Range A \<Longrightarrow> ereal -` {l..u} \<noteq> {} \<Longrightarrow> scaleR2 l u (f x) = f (scaleR2 l u x)"
  using that
  apply (auto simp: scaleR2_rel_def )
  apply (rule relcompI)
   apply (rule prod_relI)
    apply (rule IdI)
   apply (drule fun_relD, assumption, assumption)
    apply (auto simp: br_def vimage_def)
  done

lemma appr1e_rep_impl[autoref_rules]:
  "(\<lambda>x. RETURN x, scaleR2_rep) \<in> \<langle>A\<rangle>scaleR2_rel \<rightarrow> \<langle>(ereal_rel \<times>\<^sub>r ereal_rel) \<times>\<^sub>r A\<rangle>nres_rel"
  by (force simp: nres_rel_def scaleR2_rep_def scaleR2_rel_def image_image split_beta'
      dest!: brD intro!: RETURN_SPEC_refine)

lemma [autoref_op_pat]: "fst ` X \<equiv> (OP op_image_fst_colle) $ X"
  by auto

lemma [autoref_op_pat]: "fst ` X \<equiv> (OP op_image_fste) $ X"
  by simp

lemma scaleRe_ivl_impl[autoref_rules]:
  "(\<lambda>l u X. if l < u \<or> l > - \<infinity> \<and> l \<le> u \<and> u < \<infinity> then RETURN ((l, u), X) else SUCCEED,
    scaleRe_ivl_spec) \<in> ereal_rel \<rightarrow> ereal_rel \<rightarrow> A \<rightarrow> \<langle>\<langle>A\<rangle>scaleR2_rel\<rangle>nres_rel"
  apply (auto simp: scaleRe_ivl_spec_def scaleR2_rep_def scaleR2_rel_def nres_rel_def
        RETURN_RES_refine_iff
      intro!: RETURN_SPEC_refine )
  apply (rule relcompI)
   apply (rule prod_relI)
    apply (rule IdI)
    apply assumption defer
  apply (rule relcompI)
   apply (rule prod_relI)
    apply (rule IdI)
    apply assumption defer
   apply (auto intro!: brI)
  subgoal for a b c d
    apply (cases a; cases b)
    by (auto simp: vimage_def)
  subgoal for a b c d
    apply (cases a; cases b)
    by (auto simp: vimage_def)
  done

lemma is_empty_scaleR2_rel[autoref_rules]:
  assumes "GEN_OP ie is_empty (A \<rightarrow> bool_rel)"
  shows "(\<lambda>(_, b). ie b, is_empty) \<in> (\<langle>A\<rangle>scaleR2_rel \<rightarrow> bool_rel)"
  using assms[THEN GEN_OP_D, param_fo]
  by (auto simp: scaleR2_rep_def scaleR2_rel_def  scaleR2_def vimage_def
      dest!: brD)

lemma sv_appr1e_rel[relator_props]: "single_valued A \<Longrightarrow> single_valued (\<langle>A\<rangle>scaleR2_rel)"
  by (auto simp: scaleR2_rep_def scaleR2_rel_def intro!: relator_props)

schematic_goal scaleR2_rep_coll_impl:
  assumes [THEN PREFER_sv_D, relator_props]: "PREFER single_valued A"
  assumes [autoref_rules]: "(ai, a) \<in> clw_rel (\<langle>A\<rangle>scaleR2_rel)"
  shows "(nres_of ?r, scaleR2_rep_coll a) \<in> \<langle>(ereal_rel \<times>\<^sub>r ereal_rel) \<times>\<^sub>r clw_rel A\<rangle>nres_rel"
  unfolding scaleR2_rep_coll_def
  including art
  by autoref_monadic
concrete_definition scaleR2_rep_coll_impl for ai uses scaleR2_rep_coll_impl
lemmas scaleR2_rep_coll_impl_refine[autoref_rules] =
  scaleR2_rep_coll_impl.refine[autoref_higher_order_rule (1)]


lemma fst_imageIcc:
  "fst ` {a::'a::ordered_euclidean_space\<times>'c::ordered_euclidean_space .. b} =
  (if a \<le> b then {fst a .. fst b} else {})"
  by (auto intro!: simp: less_eq_prod_def)

lemma
  interval_inter_times_UNIVI:
  assumes "{fst a .. fst b} \<inter> {c .. d} = {fst e .. fst f}"
  assumes "{snd a .. snd b} = {snd e .. snd f}"
  shows "{a::('a::ordered_euclidean_space \<times> 'c::ordered_euclidean_space) .. b} \<inter>
      ({c .. d} \<times> UNIV) = {e .. f}"
  using assms
  by (cases a; cases b; cases e; cases f) (auto simp: subset_iff set_eq_iff)

lemma op_inter_fst_impl:
  assumes "DIM_precond TYPE('a::executable_euclidean_space) D"
  assumes "GEN_OP intr (op_inter_ivl::('a) set\<Rightarrow>_) (lvivl_rel \<rightarrow> lvivl_rel \<rightarrow> lvivl_rel)"
  assumes "GEN_OP le   ((\<le>) ::'a\<times>('b::executable_euclidean_space) \<Rightarrow>_) (lv_rel \<rightarrow> lv_rel \<rightarrow> bool_rel)"
  shows "(\<lambda>x y.
    if le (fst x) (snd x) then
    case (intr (pairself (take D) x) y, pairself (drop D) x) of
      ((i, s), j, t) \<Rightarrow> (i @ j, s @ t)
    else x,
      op_inter_fst::('a \<times> 'b) set \<Rightarrow> 'a set \<Rightarrow> ('a \<times> 'b) set) \<in> lvivl_rel \<rightarrow> lvivl_rel \<rightarrow> lvivl_rel"
proof (auto simp: split: prod.splits, goal_cases)
  case (1 a b c d e f g h)
  from 1 have lens: "length a = DIM('a) + DIM('b)" "length b = DIM('a) + DIM('b)"
    by (auto simp: lvivl_rel_br br_def)
  have f_eq: "f = {eucl_of_list d .. eucl_of_list e}"
    and c_eq: "c = {eucl_of_list a .. eucl_of_list b}"
    using 1
    by (auto simp: lvivl_rel_br br_def set_of_ivl_def)
  from 1 assms(1,2) assms(3)[THEN GEN_OP_D, param_fo, OF lv_relI lv_relI, of a b]
  have "((take D a, take D b), fst ` c) \<in> \<langle>lv_rel\<rangle>ivl_rel"
    apply (auto simp: lv_rel_def ivl_rel_def dest!: brD)
    apply (rule relcompI)
     apply (rule prod_relI)
      apply (rule brI)
       apply (rule refl)
      apply (simp;fail)
     apply (rule brI)
      apply (rule refl)
     apply (simp;fail)
    apply (rule brI)
     apply (simp add: set_of_ivl_def fst_imageIcc)
    by (auto simp: eucl_of_list_prod)
  from assms(1) assms(2)[THEN GEN_OP_D, param_fo, OF this 1(2)]
  show ?case
    unfolding 1
    apply (auto simp: lv_rel_def ivl_rel_def dest!: brD)
    apply (rule relcompI)
     apply (rule prod_relI)
      apply (rule brI)
       apply (rule refl)
      apply (simp add: lens;fail)
     apply (rule brI)
      apply (rule refl)
     apply (simp add: lens;fail)
    apply (rule brI)
     apply (simp add: set_of_ivl_def fst_imageIcc)
     defer apply (simp; fail)
    apply (cases "(eucl_of_list (take DIM('a) a)::'a) \<le> eucl_of_list (take DIM('a) b) \<and>
        (eucl_of_list (drop DIM('a) a)::'b) \<le> eucl_of_list (drop DIM('a) b)")
    subgoal apply (simp split: if_splits add: c_eq f_eq)
      apply (rule interval_inter_times_UNIVI)
      by (auto simp: eucl_of_list_prod fst_imageIcc split: if_splits)
    subgoal
      by (auto simp: eucl_of_list_prod fst_imageIcc c_eq f_eq)
    done
next
  case (2 a b c d e f g h)
  from assms(3)[THEN GEN_OP_D, param_fo, OF lv_relI lv_relI, of a b] assms(1) 2
  show ?case
    apply (auto simp: lv_rel_def ivl_rel_def dest!: brD)
    apply (rule relcompI)
     apply (rule prod_relI)
      apply (rule brI)
       apply (rule refl)
      apply (simp;fail)
     apply (rule brI)
      apply (rule refl)
     apply (simp;fail)
     apply (rule brI)
      apply (simp add: set_of_ivl_def fst_imageIcc)
    apply (simp; fail)
    done
qed
concrete_definition op_inter_fst_impl uses op_inter_fst_impl
lemmas [autoref_rules] = op_inter_fst_impl.refine

definition "op_inter_fst_coll XS Y = do {
  XS \<leftarrow> sets_of_coll XS;
  FORWEAK XS (RETURN op_empty_coll) (\<lambda>X. RETURN (mk_coll (op_inter_fst X Y))) (\<lambda>X X'. RETURN (X' \<union> X))
  }"

schematic_goal op_inter_fst_coll_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE('a::executable_euclidean_space) D"
  assumes [THEN GEN_OP_D, autoref_rules]: "GEN_OP le ((\<le>) ::'a\<times>'b::executable_euclidean_space \<Rightarrow>_) (lv_rel \<rightarrow> lv_rel \<rightarrow> bool_rel)"
  assumes [autoref_rules]: "(XSi, XS::('a \<times> 'b) set) \<in> clw_rel lvivl_rel"
    "(Yi, Y::'a set) \<in> lvivl_rel"
  shows "(nres_of ?r, op_inter_fst_coll XS Y) \<in> \<langle>clw_rel lvivl_rel\<rangle>nres_rel"
  unfolding op_inter_fst_coll_def
  by autoref_monadic
concrete_definition op_inter_fst_coll_impl uses op_inter_fst_coll_impl
lemmas op_inter_fst_coll_impl_refine[autoref_rules] =
  op_inter_fst_coll_impl.refine[autoref_higher_order_rule(1 2)]

lemma [autoref_op_pat]: "X \<inter> Y \<times> UNIV \<equiv> OP op_inter_fst $ X $ Y"
  by auto

schematic_goal scaleRe_ivl_coll_impl:
  assumes [relator_props]: "single_valued A"
  assumes [autoref_rules]: "(li, l) \<in> ereal_rel" "(ui, u) \<in> ereal_rel" "(Xi, X) \<in> clw_rel A"
  shows "(nres_of ?r, scaleRe_ivl_coll_spec l u X) \<in> \<langle>clw_rel (\<langle>A\<rangle>scaleR2_rel)\<rangle>nres_rel"
  unfolding scaleRe_ivl_coll_spec_def
  including art
  by autoref_monadic
concrete_definition scaleRe_ivl_coll_impl uses scaleRe_ivl_coll_impl
lemma scaleRe_ivl_coll_impl_refine[autoref_rules]:
  "PREFER single_valued A \<Longrightarrow>
    (\<lambda>li ui Xi. nres_of (scaleRe_ivl_coll_impl li ui Xi), scaleRe_ivl_coll_spec)
    \<in> ereal_rel \<rightarrow> ereal_rel \<rightarrow> clw_rel A \<rightarrow> \<langle>clw_rel (\<langle>A\<rangle>scaleR2_rel)\<rangle>nres_rel"
  using scaleRe_ivl_coll_impl.refine by force

schematic_goal op_inter_fst_ivl_scaleR2_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE('a::executable_euclidean_space) E"
  assumes [THEN GEN_OP_D, autoref_rules]: "GEN_OP le ((\<le>) ::'a\<times>'b::executable_euclidean_space \<Rightarrow>_) (lv_rel \<rightarrow> lv_rel \<rightarrow> bool_rel)"
  assumes [autoref_rules]: "(XSi, XS::('a\<times>'b) set) \<in> elvivl_rel"
    "(Yi, Y::'a set) \<in> lvivl_rel"
  shows "(nres_of ?r, op_inter_fst_ivl_scaleR2 XS Y) \<in> \<langle>clw_rel elvivl_rel\<rangle>nres_rel"
  unfolding op_inter_fst_ivl_scaleR2_def
  including art
  by autoref_monadic
concrete_definition op_inter_fst_ivl_scaleR2_impl uses op_inter_fst_ivl_scaleR2_impl
lemmas op_inter_fst_ivl_scaleR2_impl_refine[autoref_rules] =
  op_inter_fst_ivl_scaleR2_impl.refine[autoref_higher_order_rule(1 2)]

schematic_goal op_inter_fst_ivl_coll_scaleR2_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE('a::executable_euclidean_space) E"
  assumes [THEN GEN_OP_D, autoref_rules]: "GEN_OP le ((\<le>) ::'a\<times>'b::executable_euclidean_space \<Rightarrow>_) (lv_rel \<rightarrow> lv_rel \<rightarrow> bool_rel)"
  assumes [autoref_rules]: "(XSi, XS::('a\<times>'b) set) \<in> clw_rel elvivl_rel"
    "(Yi, Y::'a set) \<in> lvivl_rel"
  shows "(nres_of ?r, op_inter_fst_ivl_coll_scaleR2 XS Y) \<in> \<langle>clw_rel elvivl_rel\<rangle>nres_rel"
  unfolding op_inter_fst_ivl_coll_scaleR2_def
  including art
  by autoref_monadic
concrete_definition op_inter_fst_ivl_coll_scaleR2_impl uses op_inter_fst_ivl_coll_scaleR2_impl
lemmas op_inter_fst_ivl_coll_scaleR2_impl_refine[autoref_rules]
  = op_inter_fst_ivl_coll_scaleR2_impl.refine[autoref_higher_order_rule(1 2)]

definition "op_inter_ivl_coll_scaleR2 X Y = do {
    eivls \<leftarrow> op_inter_fst_ivl_coll_scaleR2 X Y;
    ((l, u), ivls) \<leftarrow> scaleR2_rep_coll eivls;
    ivl \<leftarrow> op_ivl_of_ivl_coll ivls;
    let R = op_inter_fst ivl Y;
    scaleRe_ivl_coll_spec l u (filter_empty_ivls (mk_coll R))
  }"

definition "op_single_inter_ivl a fxs = do {
  let isa = (op_inter_ivl_coll (fxs:::clw_rel lvivl_rel) (a:::lvivl_rel));
  (if op_coll_is_empty isa then RETURN op_empty_coll else do {
    ivl \<leftarrow> op_ivl_of_ivl_coll isa;
    RETURN (mk_coll ((ivl:::lvivl_rel) \<inter> a))
  })
}"

schematic_goal op_inter_ivl_coll_scaleR2_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE('a::executable_euclidean_space) D"
  assumes [autoref_rules_raw]: "DIM_precond TYPE('b::executable_euclidean_space) E"
  assumes [THEN GEN_OP_D, autoref_rules]: "GEN_OP le ((\<le>) ::'a\<times>'b::executable_euclidean_space \<Rightarrow>_) (lv_rel \<rightarrow> lv_rel \<rightarrow> bool_rel)"
  assumes [autoref_rules]: "(XSi, XS::('a\<times>'b) set) \<in> clw_rel elvivl_rel"
    "(Yi, Y::'a set) \<in> lvivl_rel"
  shows "(nres_of ?r, op_inter_ivl_coll_scaleR2 XS Y) \<in> \<langle>clw_rel elvivl_rel\<rangle>nres_rel"
  unfolding op_inter_ivl_coll_scaleR2_def
  including art
  by autoref_monadic
concrete_definition op_inter_ivl_coll_scaleR2_impl uses op_inter_ivl_coll_scaleR2_impl
lemmas op_inter_ivl_coll_scaleR2_impl_refine[autoref_rules] =
  op_inter_ivl_coll_scaleR2_impl.refine[autoref_higher_order_rule(1 2 3)]

lemma op_image_fst_ivl[autoref_rules]:
  assumes [autoref_rules_raw]: "DIM_precond TYPE('a::executable_euclidean_space) D"
  assumes [THEN GEN_OP_D, autoref_rules]: "GEN_OP le ((\<le>) ::'a\<times>'b::executable_euclidean_space \<Rightarrow>_) (lv_rel \<rightarrow> lv_rel \<rightarrow> bool_rel)"
  shows "(\<lambda>(l,u). nres_of (if le l u then dRETURN (pairself (take D) (l, u)) else dSUCCEED)
    , op_image_fst_ivl::('a\<times>'b) set\<Rightarrow>_) \<in> lvivl_rel \<rightarrow> \<langle>lvivl_rel\<rangle>nres_rel"
  using assms
  apply (auto simp: ivl_rel_def nres_rel_def op_image_fst_ivl_def RETURN_RES_refine_iff
      dest!: brD intro!: )
  apply (rule relcompI)
   apply (rule prod_relI)
    apply (rule lv_relI)
    apply (simp add: lv_rel_def br_def)
    apply (rule lv_relI)
   apply (simp add: lv_rel_def br_def)
  apply (rule brI)
  subgoal for a b
    apply (drule fun_relD)
     apply (rule lv_relI[where x=a])
      apply (simp add: lv_rel_def br_def)
    apply (drule fun_relD)
     apply (rule lv_relI[where x=b])
      apply (simp add: lv_rel_def br_def)
    apply (auto simp: set_of_ivl_def lv_rel_def br_def fst_imageIcc eucl_of_list_prod)
    done
  subgoal by simp
  done

schematic_goal op_image_fst_ivl_coll_impl[autoref_rules]:
  assumes [autoref_rules_raw]: "DIM_precond TYPE('a::executable_euclidean_space) D"
  assumes "GEN_OP le ((\<le>) ::'a\<times>'b::executable_euclidean_space \<Rightarrow>_) (lv_rel \<rightarrow> lv_rel \<rightarrow> bool_rel)"
    assumes [autoref_rules]: "(Xi, X) \<in> clw_rel lvivl_rel"
    shows "(nres_of ?r, (op_image_fst_ivl_coll::('a\<times>'b) set\<Rightarrow>_) X) \<in> \<langle>clw_rel lvivl_rel\<rangle>nres_rel"
  unfolding op_image_fst_ivl_coll_def
  by autoref_monadic
concrete_definition op_image_fst_ivl_coll_impl uses op_image_fst_ivl_coll_impl
lemmas op_image_fst_ivl_coll_impl_refine[autoref_rules] =
  op_image_fst_ivl_coll_impl.refine[autoref_higher_order_rule(1 2)]

schematic_goal op_single_inter_ivl_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE('a::executable_euclidean_space) D"
  assumes [autoref_rules]: "(FXSi, FXS) \<in> clw_rel lvivl_rel" "(Ai, A::'a set) \<in> lvivl_rel"
  shows "(nres_of ?r, op_single_inter_ivl A FXS) \<in> \<langle>clw_rel lvivl_rel\<rangle>nres_rel"
  unfolding op_single_inter_ivl_def
  by autoref_monadic
concrete_definition op_single_inter_ivl_impl for Ai FXSi uses op_single_inter_ivl_impl
lemmas op_single_inter_ivl_impl_refine[autoref_rules]
  = op_single_inter_ivl_impl.refine[autoref_higher_order_rule (1)]

definition [refine_vcg_def]: "le_post_inter_granularity_op ro r = SPEC(\<lambda>x::bool. True)"

lemma le_post_inter_granularity_op_itype[autoref_itype]:
  "le_post_inter_granularity_op ::\<^sub>i A \<rightarrow>\<^sub>i \<langle>i_rnv\<rangle>\<^sub>ii_ivl \<rightarrow>\<^sub>i \<langle>i_bool\<rangle>\<^sub>ii_nres"
  by auto

definition partition_ivle::
  "_ \<Rightarrow> ('a::executable_euclidean_space \<times> 'c::executable_euclidean_space) set \<Rightarrow> _ set nres"
  where
 "partition_ivle ro xse =
  (if op_coll_is_empty xse then RETURN (op_empty_coll:::clw_rel (elvivl_rel)) else do {
    (_, xs) \<leftarrow> scaleR2_rep_coll xse;
    xsf \<leftarrow> op_image_fst_ivl_coll xs;
    r \<leftarrow> op_ivl_of_ivl_coll (xsf:::clw_rel (lvivl_rel));
    (i, s) \<leftarrow> ivl_rep r;
    CHECK (\<lambda>_. ()) (i \<le> s);
    (rs, ps) \<leftarrow>
      WHILE\<^bsup>(\<lambda>(rs, ps). xse \<subseteq> (rs \<times> UNIV) \<union> ps)\<^esup> (\<lambda>(rs, ps). \<not> op_coll_is_empty (rs:::clw_rel lvivl_rel))
      (\<lambda>(rs, ps).
      do {
        (r, rs') \<leftarrow> (split_spec_exact rs:::\<langle>lvivl_rel \<times>\<^sub>r clw_rel lvivl_rel\<rangle>nres_rel);
        okay \<leftarrow> le_post_inter_granularity_op ro r;
        if okay then do {
          I \<leftarrow> op_inter_ivl_coll_scaleR2 (xse) (r);
          RETURN (rs', I \<union> ps)
        } else do {
          (a, b) \<leftarrow> split_spec_ivl DIM('a) r;
          fxs \<leftarrow> op_image_fst_ivl_coll xs;
          ra' \<leftarrow> op_single_inter_ivl a fxs;
          rb' \<leftarrow> op_single_inter_ivl b fxs;
          RETURN (ra' \<union> rb' \<union> rs', ps)
        }
      }) (mk_coll r:::clw_rel lvivl_rel, op_empty_coll :::clw_rel elvivl_rel);
    RETURN ps
  })"

schematic_goal partition_ivle_nres:
  assumes [autoref_rules_raw]: "DIM_precond TYPE('a::executable_euclidean_space) F"
  assumes [autoref_rules_raw]: "DIM_precond TYPE('c::executable_euclidean_space) E"
  assumes okgs[THEN GEN_OP_D, autoref_rules]:
    "GEN_OP okay_granularityi (le_post_inter_granularity_op::_\<Rightarrow>'a set\<Rightarrow>_) (A \<rightarrow> lvivl_rel \<rightarrow> \<langle>bool_rel\<rangle>nres_rel)"
  assumes [unfolded autoref_tag_defs, refine_transfer]:
    "\<And>ro X. TRANSFER (nres_of (okay_granularityd ro X) \<le> okay_granularityi ro X)"
  assumes [autoref_rules]:
    "(xsi, xs::('a\<times>'c::executable_euclidean_space) set)\<in> clw_rel elvivl_rel"
  assumes [autoref_rules]: "(roi, ro) \<in> A"
  shows "(nres_of ?f, partition_ivle ro xs)\<in>\<langle>clw_rel elvivl_rel\<rangle>nres_rel"
  unfolding partition_ivle_def[abs_def]
  including art
  by autoref_monadic
concrete_definition partition_ivle_nres for okay_granularityd xsi uses partition_ivle_nres
lemmas [autoref_rules] = partition_ivle_nres.refine[autoref_higher_order_rule(1 2 3 4)]

definition "reduce_ivl (X::('a::executable_euclidean_space\<times>'b::executable_euclidean_space)set) b = do {
    (i, s) \<leftarrow> ivl_rep X;
    CHECK (\<lambda>_. ST ''reduce_ivl strange basis'') (b \<in> set Basis_list);
    CHECK (\<lambda>_. ST ''reduce_ivl strange ivl'') (i \<le> s);
    let (i0, i1) = split_lv_rel i;
    let (s0, s1) = split_lv_rel s;
    let ivl2 = op_atLeastAtMost_ivl i1 s1;
    P \<leftarrow> project_set_ivl ivl2 b 0;
    (iP, sP) \<leftarrow> ivl_rep P;
    if iP \<le> 0 \<and> 0 \<le> sP then
      if i1 \<bullet> b > 0 then do {
        let s = (i1 \<bullet> b) *\<^sub>R b;
        let P' = op_atLeastAtMost_ivl (Pair_lv_rel i0 (iP + s)) (Pair_lv_rel s0 (sP + s));
        scaleRe_ivl_spec 1 \<infinity> P'
      } else if s1 \<bullet> b < 0 then do {
        let s = (s1 \<bullet> b) *\<^sub>R b;
        let P' = op_atLeastAtMost_ivl (Pair_lv_rel i0 (iP + s)) (Pair_lv_rel s0 (sP + s));
        scaleRe_ivl_spec 1 \<infinity> P'
      } else scaleRe_ivl_spec 1 1 X
    else scaleRe_ivl_spec 1 1 X
  }"

definition "reduce_ivle Y b = do {
    ((l, u), X) \<leftarrow> scaleR2_rep Y;
    R \<leftarrow> reduce_ivl X b;
    ((l', u'), R) \<leftarrow> scaleR2_rep R;
    CHECK (\<lambda>_. ()) (0 < l' \<and> 0 < l \<and> 0 \<le> u \<and> l \<le> u \<and> l' \<le> u');
    scaleRe_ivl_spec (l'*l) (u' * u) R
  }"

definition "reduces_ivle (X::('a::executable_euclidean_space\<times>'b::executable_euclidean_space)set) =
  FOREACH\<^bsup>\<lambda>B R. X \<subseteq> R\<^esup> (set Basis_list:::\<langle>lv_rel\<rangle>list_set_rel) (\<lambda>b X. reduce_ivle X b) X"

definition "setse_of_ivlse (X:: ('a::executable_euclidean_space \<times> 'c::executable_euclidean_space) set) = do {
  Xs \<leftarrow> sets_of_coll X;
  FORWEAK Xs (RETURN op_empty_coll) (\<lambda>X. do {
    ((l, u), x) \<leftarrow> scaleR2_rep X;
    (i, s) \<leftarrow> ivl_rep x;
    if i \<le> s then do {
      x \<leftarrow> scaleRe_ivl_spec l u {i .. s};
      RETURN (mk_coll x)
    } else RETURN op_empty_coll
  }) (\<lambda>X' X. RETURN (X' \<union> X))
}"

schematic_goal reduce_ivl_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE('a::executable_euclidean_space) D"
  assumes [autoref_rules_raw]: "DIM_precond TYPE('b::executable_euclidean_space) E"
  assumes [autoref_rules]:
    "(Yi, Y::('a\<times>'b::executable_euclidean_space) set) \<in> lvivl_rel"
    "(bi, b::'b) \<in> lv_rel"
  shows "(nres_of ?r, reduce_ivl Y b) \<in> \<langle>elvivl_rel\<rangle>nres_rel"
  unfolding autoref_tag_defs
  unfolding reduce_ivl_def
  including art
  by autoref_monadic
concrete_definition reduce_ivl_impl for Yi bi uses reduce_ivl_impl
lemmas [autoref_rules] = reduce_ivl_impl.refine[autoref_higher_order_rule(1 2)]

schematic_goal reduce_ivle_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE('a::executable_euclidean_space) D"
  assumes [autoref_rules_raw]: "DIM_precond TYPE('b::executable_euclidean_space) E"
  assumes [autoref_rules]:
    "(Yi, Y::('a\<times>'b::executable_euclidean_space) set) \<in> elvivl_rel"
    "(bi, b::'b) \<in> lv_rel"
  shows "(nres_of ?r, reduce_ivle Y b) \<in> \<langle>elvivl_rel\<rangle>nres_rel"
  unfolding autoref_tag_defs
  unfolding reduce_ivle_def
  including art
  by autoref_monadic
concrete_definition reduce_ivle_impl for Yi bi uses reduce_ivle_impl
lemmas [autoref_rules] = reduce_ivle_impl.refine[autoref_higher_order_rule(1 2)]

schematic_goal reduces_ivle_impl:
  assumes [autoref_rules_raw]: "DIM_precond TYPE('a::executable_euclidean_space) D"
  assumes [autoref_rules_raw]: "DIM_precond TYPE('b::executable_euclidean_space) E"
  assumes [autoref_rules]: "(Yi, Y::('a\<times>'b::executable_euclidean_space) set) \<in> elvivl_rel"
  shows "(nres_of ?r, reduces_ivle Y) \<in> \<langle>elvivl_rel\<rangle>nres_rel"
  unfolding autoref_tag_defs
  unfolding reduces_ivle_def
  including art
  by autoref_monadic
concrete_definition reduces_ivle_impl for Yi uses reduces_ivle_impl
lemmas [autoref_rules] = reduces_ivle_impl.refine[autoref_higher_order_rule(1 2)]

lemma scaleR2_subset:
  assumes "x \<in> scaleR2 i' j' k'"
  assumes "i \<le> i'" "j' \<le> j" "k' \<subseteq> k"
  shows "x \<in> scaleR2 i j k"
  using assms
  by (force simp: scaleR2_def vimage_def image_def)

lemma subset_scaleR2_fstD: "X \<subseteq> scaleR2 l u Y \<Longrightarrow> fst ` X \<subseteq> fst ` Y"
  by (force simp: scaleR2_def subset_iff image_def vimage_def)

lemma mem_scaleR2_union[simp]: "x \<in> scaleR2 l u (A \<union> B) \<longleftrightarrow> x \<in> scaleR2 l u A \<or> x \<in> scaleR2 l u B"
  by (force simp: scaleR2_def vimage_def image_def)

lemma scaleR2_empty[simp]: "scaleR2 l u {} = {}"
  by (auto simp: scaleR2_def)

lemma scaleR2_eq_empty_iff:
  "scaleR2 l u X = {} \<longleftrightarrow> X = {} \<or> ereal -` {l..u} = {}"
  by (auto simp: scaleR2_def)

lemma scaleR2_id[simp]: "scaleR2 (1::ereal) 1 = (\<lambda>(x::('d \<times> 'c::real_vector) set). x)"
  by (rule scaleR2_1_1)

end

end