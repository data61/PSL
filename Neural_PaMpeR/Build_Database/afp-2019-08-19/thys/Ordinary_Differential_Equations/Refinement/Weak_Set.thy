theory Weak_Set
imports
  Autoref_Misc
begin

subsection \<open>generic things\<close>

lemma nres_rel_trans1: "a \<le> b \<Longrightarrow> (b, i) \<in> \<langle>R\<rangle>nres_rel \<Longrightarrow> (a, i) \<in> \<langle>R\<rangle>nres_rel"
  using nres_relD order_trans
  by (blast intro: nres_relI)

lemma nres_rel_trans2: "a \<le> b \<Longrightarrow> (i, a) \<in> \<langle>R\<rangle>nres_rel \<Longrightarrow> (i, b) \<in> \<langle>R\<rangle>nres_rel"
  using nres_relD
  by (blast intro: nres_relI ref_two_step)

lemma param_Union[param]: "(Union, Union) \<in> \<langle>\<langle>R\<rangle>set_rel\<rangle>set_rel \<rightarrow> \<langle>R\<rangle>set_rel"
  by (fastforce simp: set_rel_def)

subsection \<open>relation\<close>

definition list_wset_rel_internal_def: "list_wset_rel R = br set top O \<langle>R\<rangle>set_rel"

lemma list_wset_rel_def: "\<langle>R\<rangle>list_wset_rel = br set top O \<langle>R\<rangle>set_rel"
  unfolding list_wset_rel_internal_def[abs_def] by (simp add: relAPP_def)

lemma list_wset_rel_br_eq: "\<langle>br a I\<rangle>list_wset_rel = br (\<lambda>xs. a ` set xs) (\<lambda>xs. \<forall>x \<in> set xs. I x)"
  by (auto simp: list_wset_rel_def br_def set_rel_def)

lemma mem_br_list_wset_rel_iff:
  "(xs, X) \<in> \<langle>br a I\<rangle>list_wset_rel \<longleftrightarrow> (X = (a ` set xs) \<and> (\<forall>x \<in> set xs. I x))"
  by (auto simp: list_wset_rel_def set_rel_def br_def)

lemma list_set_rel_sv[relator_props]:
  "single_valued R \<Longrightarrow> single_valued (\<langle>R\<rangle>list_wset_rel)"
  unfolding list_wset_rel_def
  by tagged_solver

lemmas [autoref_rel_intf] = REL_INTFI[of list_wset_rel i_set]

lemma list_wset_relD:
  assumes "(a, b) \<in> \<langle>R\<rangle>list_wset_rel"
  shows "(set a, b) \<in> \<langle>R\<rangle>set_rel"
  using assms
  by (auto simp: list_wset_rel_def br_def)


subsection \<open>operations\<close>

definition "op_set_ndelete x X = RES {X - {x}, X}"

lemma op_set_ndelete_spec: "op_set_ndelete x X = SPEC(\<lambda>R. R = X - {x} \<or> R = X)"
  by (auto simp: op_set_ndelete_def)


subsection \<open>implementations\<close>

lemma list_wset_autoref_empty[autoref_rules]:
  "([],{})\<in>\<langle>R\<rangle>list_wset_rel"
  by (auto simp: list_wset_rel_def br_def relcompI)

context includes autoref_syntax begin

lemma mem_set_list_relE1:
  assumes "(xs, ys) \<in> \<langle>R\<rangle>list_rel"
  assumes "x \<in> set xs"
  obtains y where "y \<in> set ys" "(x, y) \<in> R"
  by (metis (no_types, lifting) assms in_set_conv_decomp list_relE3 list_rel_append1)

lemma mem_set_list_relE2:
  assumes "(xs, ys) \<in> \<langle>R\<rangle>list_rel"
  assumes "y \<in> set ys"
  obtains x where "x \<in> set xs" "(x, y) \<in> R"
  by (metis assms in_set_conv_decomp list_relE4 list_rel_append2)

lemma in_domain_list_relE:
  assumes "\<And>x. x \<in> set xs \<Longrightarrow> x \<in> Domain R"
  obtains ys where "(xs, ys) \<in> \<langle>R\<rangle>list_rel"
proof -
  obtain y where y: "\<And>x. x \<in> set xs \<Longrightarrow> (x, y x) \<in> R"
    using assms by (metis for_in_RI)
  have "(xs, map y xs) \<in> \<langle>R\<rangle>list_rel"
    by (auto simp: list_rel_def list_all2_iff in_set_zip intro!: y)
  then show ?thesis ..
qed

lemma list_rel_comp_list_wset_rel:
  assumes "single_valued R"
  shows "\<langle>R\<rangle>list_rel O \<langle>S\<rangle>list_wset_rel = \<langle>R O S\<rangle>list_wset_rel"
proof (safe, goal_cases)
  case hyps: (1 a b x y z)
  show ?case
    unfolding list_wset_rel_def
  proof (rule relcompI[where b = "set x"])
    show "(set x, z) \<in> \<langle>R O S\<rangle>set_rel"
      unfolding set_rel_def
      using hyps 
      by (clarsimp simp: list_wset_rel_def br_def set_rel_def)
        (meson mem_set_list_relE1 mem_set_list_relE2 relcomp.relcompI)
  qed (simp add: br_def)
next
  case hyps: (2 xs zs)
  then have "\<And>x. x \<in> set xs \<Longrightarrow> x \<in> Domain R"
    by (auto simp: list_wset_rel_def br_def set_rel_def)
  from in_domain_list_relE[OF this]
  obtain ys where ys: "(xs, ys) \<in> \<langle>R\<rangle>list_rel" .
  have set_rel: "(set ys, zs) \<in> \<langle>S\<rangle>set_rel"
    unfolding list_wset_rel_def set_rel_def
    using hyps
    by (clarsimp simp: list_wset_rel_def br_def set_rel_def)
      (metis (full_types) assms mem_set_list_relE1 mem_set_list_relE2 relcompEpair single_valued_def ys)
  from ys show ?case
    by (rule relcompI)
      (auto simp: list_wset_rel_def br_def intro!: relcompI[where b="set ys"] set_rel)
qed

lemma list_set_autoref_insert[autoref_rules]:
  assumes "PREFER single_valued R"
  shows "(Cons,Set.insert) \<in> R \<rightarrow> \<langle>R\<rangle>list_wset_rel \<rightarrow> \<langle>R\<rangle>list_wset_rel"
proof -
  have 1: "(Cons, Cons) \<in> R \<rightarrow> \<langle>R\<rangle>list_rel \<rightarrow> \<langle>R\<rangle>list_rel"
    by parametricity
  moreover have 2: "(Cons, Set.insert) \<in> Id \<rightarrow> \<langle>Id\<rangle>list_wset_rel \<rightarrow> \<langle>Id\<rangle>list_wset_rel"
    by (auto simp: list_wset_rel_def br_def)
  ultimately have "(Cons, Set.insert) \<in> (R \<rightarrow> \<langle>R\<rangle>list_rel \<rightarrow> \<langle>R\<rangle>list_rel) O (Id \<rightarrow> \<langle>Id\<rangle>list_wset_rel \<rightarrow> \<langle>Id\<rangle>list_wset_rel)"
    by auto
  also have "\<dots> \<subseteq> R \<rightarrow> \<langle>R\<rangle>list_wset_rel \<rightarrow> \<langle>R\<rangle>list_wset_rel"
  proof -
    have "\<langle>R\<rangle>list_rel O \<langle>Id\<rangle>list_wset_rel \<rightarrow> \<langle>R\<rangle>list_rel O \<langle>Id\<rangle>list_wset_rel \<subseteq>
        \<langle>R\<rangle>list_wset_rel \<rightarrow> \<langle>R\<rangle>list_wset_rel"
      by (rule fun_rel_mono)
        (simp_all add: list_rel_comp_list_wset_rel assms[unfolded autoref_tag_defs])
    then have "(\<langle>R\<rangle>list_rel \<rightarrow> \<langle>R\<rangle>list_rel) O (\<langle>Id\<rangle>list_wset_rel \<rightarrow> \<langle>Id\<rangle>list_wset_rel) \<subseteq>
        \<langle>R\<rangle>list_wset_rel \<rightarrow> \<langle>R\<rangle>list_wset_rel"
      by (rule order_trans[OF fun_rel_comp_dist])
    from _ this have
      "R O Id \<rightarrow> (\<langle>R\<rangle>list_rel \<rightarrow> \<langle>R\<rangle>list_rel) O (\<langle>Id\<rangle>list_wset_rel \<rightarrow> \<langle>Id\<rangle>list_wset_rel) \<subseteq>
        R \<rightarrow> \<langle>R\<rangle>list_wset_rel \<rightarrow> \<langle>R\<rangle>list_wset_rel"
      by (rule fun_rel_mono) simp
    then show ?thesis
      by (rule order_trans[OF fun_rel_comp_dist])
  qed
  finally show ?thesis .
qed

lemma op_set_ndelete_wset_refine[autoref_rules]:
  assumes "PREFER single_valued R"
  assumes "(x, y) \<in> R" "(xs, Y) \<in> \<langle>R\<rangle>list_wset_rel"
  shows "(nres_of (dRETURN (List.remove1 x xs)),op_set_ndelete $ y $ Y) \<in> \<langle>\<langle>R\<rangle>list_wset_rel\<rangle>nres_rel"
proof -
  from assms(3)[unfolded list_wset_rel_def]
  obtain u where u: "(xs, u) \<in> br set top" "(u, Y) \<in> \<langle>R\<rangle>set_rel"
    by (rule relcompE) auto
  have "\<exists>x'. (remove1 x xs, x') \<in> \<langle>R\<rangle>list_wset_rel \<and> (x' = Y - {y} \<or> x' = Y)"
  proof (cases "x \<in> set (remove1 x xs)")
    case True
    then have "set (remove1 x xs) = set xs"
      by (metis in_set_remove1 set_remove1_subset subsetI subset_antisym)
    then show ?thesis
      using True u
      by (auto intro!: simp: list_wset_rel_def br_def)
  next
    case False
    then have r: "set (remove1 x xs) = set xs - {x}"
      using in_set_remove1[of _ x xs] u
      by (auto simp del: in_set_remove1 simp add: br_def)
    from assms old_set_rel_sv_eq[of R] have [simp]: "\<langle>R\<rangle>set_rel = \<langle>R\<rangle>old_set_rel" by simp
    show ?thesis
      using False \<open>(x, y) \<in> R\<close> assms
      by (auto simp: relcomp_unfold r old_set_rel_def single_valued_def br_def list_wset_rel_def)
  qed
  then show ?thesis
    unfolding op_set_ndelete_spec autoref_tag_defs
    by (safe intro!: nres_relI SPEC_refine det_SPEC elim!: relcompE)
qed


subsection \<open>pick\<close>

lemma
  pick_wset_refine[autoref_rules]:
  assumes[unfolded autoref_tag_defs, simp]: "SIDE_PRECOND (X \<noteq> {})"
  assumes "(XS, X) \<in> \<langle>A\<rangle>list_wset_rel"
  shows "(nres_of (dRETURN (hd XS)), op_set_pick $ X) \<in> \<langle>A\<rangle>nres_rel"
proof -
  have "\<forall>x\<in>set XS. \<exists>y\<in>X. (x, y) \<in> A \<Longrightarrow> \<forall>y\<in>X. \<exists>x\<in>set XS. (x, y) \<in> A \<Longrightarrow>
    \<forall>x'. (hd XS, x') \<in> A \<longrightarrow> x' \<notin> X \<Longrightarrow> xa \<notin> X" for xa
    by (metis (full_types) empty_iff insertCI list.exhaust list.sel(1) list.set)
  show ?thesis
    using assms(2)
    unfolding op_set_pick_def[abs_def] autoref_tag_defs
    by (cases XS)
      (auto simp: Let_def list_wset_rel_def set_rel_def br_def intro!: nres_relI RETURN_RES_refine det_SPEC)
qed

subsection \<open>pick remove\<close>

definition "op_set_npick_remove X = SPEC (\<lambda>(x, X'). x \<in> X \<and> (X' = X - {x} \<or> X' = X))"
lemma op_set_pick_remove_pat[autoref_op_pat]:
  "SPEC (\<lambda>(x, X'). x \<in> X \<and> (X' = X - {x} \<or> X' = X)) \<equiv> op_set_npick_remove $ X"
  "SPEC (\<lambda>(x, X'). x \<in> X \<and> (X' = X \<or> X' = X - {x})) \<equiv> op_set_npick_remove $ X"
  "do { x \<leftarrow> SPEC (\<lambda>x. x \<in> X); X' \<leftarrow> op_set_ndelete x X; f x X' } \<equiv> do { (x, X') \<leftarrow> op_set_npick_remove X; f x X'}"
  by (auto simp: op_set_npick_remove_def op_set_ndelete_def pw_eq_iff refine_pw_simps intro!: eq_reflection)

lemma op_set_npick_remove_def':
  "X \<noteq> {} \<Longrightarrow> op_set_npick_remove X =
    do { ASSERT (X \<noteq> {}); x \<leftarrow> op_set_pick X; X' \<leftarrow> op_set_ndelete x X; RETURN (x, X')}"
  by (auto simp: op_set_npick_remove_def op_set_ndelete_def pw_eq_iff refine_pw_simps )

lemma aux: "(a, c) \<in> R \<Longrightarrow> a = b \<Longrightarrow> (b, c) \<in> R"
  by simp

lemma
  op_set_npick_remove_refine[autoref_rules]:
  assumes [THEN PREFER_sv_D, relator_props]: "PREFER single_valued A"
  assumes "SIDE_PRECOND (X \<noteq> {})"
  assumes [autoref_rules]: "(XS, X) \<in> \<langle>A\<rangle>list_wset_rel"
  shows "(RETURN (hd XS, tl XS), op_set_npick_remove $ X) \<in> \<langle>A \<times>\<^sub>r \<langle>A\<rangle>list_wset_rel\<rangle>nres_rel"
proof -
  have "(RETURN (hd XS, remove1 (hd XS) XS), ASSERT (X \<noteq> {}) \<bind> (\<lambda>_. op_set_pick X \<bind> (\<lambda>x. op_set_ndelete x X \<bind> (\<lambda>X'. RETURN (x, X')))))
    \<in> \<langle>A \<times>\<^sub>r \<langle>A\<rangle>list_wset_rel\<rangle>nres_rel"
    by (rule aux, autoref, simp)
  then show ?thesis
    unfolding autoref_tag_defs op_set_npick_remove_def'[OF assms(2)[unfolded autoref_tag_defs]]
    using assms
    by (subst remove1_tl[symmetric]) (force simp: list_wset_rel_def br_def set_rel_def)
qed


subsection \<open>emptiness check\<close>

lemma isEmpty_wset_refine[autoref_rules]:
  assumes "(xs, X) \<in> \<langle>A\<rangle>list_wset_rel"
  shows "(xs = [], op_set_isEmpty $ X) \<in> bool_rel"
  using assms
  by (auto simp: list_wset_rel_def br_def set_rel_def)


subsection \<open>union\<close>

lemma union_wset_refine[autoref_rules]:
  "(append, (\<union>)) \<in> \<langle>R\<rangle>list_wset_rel \<rightarrow> \<langle>R\<rangle>list_wset_rel \<rightarrow> \<langle>R\<rangle>list_wset_rel"
  by (auto 0 3 simp: list_wset_rel_def set_rel_def relcomp_unfold br_def)


subsection \<open>of list\<close>

lemma set_wset_refine[autoref_rules]:
  assumes "PREFER single_valued R"
  shows "((\<lambda>x. x), set) \<in> \<langle>R\<rangle>list_rel \<rightarrow> \<langle>R\<rangle>list_wset_rel"
proof (rule fun_relI)
  fix a a'
  assume aa': "(a, a') \<in> \<langle>R\<rangle>list_rel"
  moreover have "(a, a') \<in> \<langle>R\<rangle>list_rel \<Longrightarrow> (set a, set a') \<in> \<langle>R\<rangle>set_rel"
    using assms[THEN PREFER_sv_D]
    by parametricity
  ultimately show "(a, set a') \<in> \<langle>R\<rangle>list_wset_rel"
    unfolding list_wset_rel_def
    by (intro relcompI[where b="set a"]) (simp_all add: br_def)
qed


subsection \<open>filter set\<close>

lemma bCollect_param: "((\<lambda>y a. {x \<in> y. a x}), (\<lambda>z a'. {x \<in> z. a' x})) \<in> \<langle>R\<rangle>set_rel \<rightarrow> (R \<rightarrow> bool_rel) \<rightarrow> \<langle>R\<rangle>set_rel"
  unfolding set_rel_def
  apply safe
  subgoal using tagged_fun_relD_both by fastforce
  subgoal using tagged_fun_relD_both by fastforce
  done

lemma op_set_filter_list_wset_refine[autoref_rules]:
  "(filter, op_set_filter) \<in> (R \<rightarrow> bool_rel) \<rightarrow> \<langle>R\<rangle>list_wset_rel \<rightarrow> \<langle>R\<rangle>list_wset_rel"
  by (force simp: list_wset_rel_def br_def bCollect_param[param_fo])


subsection \<open>bound on cardinality\<close>

definition "op_set_wcard X = SPEC (\<lambda>c. card X \<le> c)"

lemma op_set_wcard_refine[autoref_rules]: "PREFER single_valued R \<Longrightarrow> ((\<lambda>xs. RETURN (length xs)), op_set_wcard) \<in> \<langle>R\<rangle>list_wset_rel \<rightarrow> \<langle>Id\<rangle>nres_rel"
proof (auto simp: list_wset_rel_def nres_rel_def br_def op_set_wcard_def, goal_cases)
  case (1 x z)
  thus ?case
    by (induction x arbitrary: z)
      (auto simp: old_set_rel_sv_eq[symmetric] old_set_rel_def Image_insert intro!: card_insert_le_m1)  
qed

lemmas op_set_wcard_spec[refine_vcg] = op_set_wcard_def[THEN eq_refl, THEN order_trans]

subsection \<open>big union\<close>

lemma Union_list_wset_rel[autoref_rules]:
  assumes "PREFER single_valued A"
  shows "(concat, Union) \<in> \<langle>\<langle>A\<rangle>list_wset_rel\<rangle>list_wset_rel \<rightarrow> \<langle>A\<rangle>list_wset_rel"
proof -
  have "(concat, concat) \<in> \<langle>\<langle>A\<rangle>list_rel\<rangle>list_rel \<rightarrow> \<langle>A\<rangle>list_rel" (is "_ \<in> ?A")
    by parametricity
  moreover have "(concat, Union) \<in> \<langle>\<langle>Id\<rangle>list_wset_rel\<rangle>list_wset_rel \<rightarrow> \<langle>Id\<rangle>list_wset_rel" (is "_ \<in> ?B")
    by (auto simp: list_wset_rel_def br_def relcomp_unfold set_rel_def; meson)
  ultimately have "(concat, Union) \<in> ?A O ?B"
    by auto
  also note fun_rel_comp_dist
  finally show ?thesis
    using assms
    by (simp add: list_rel_comp_list_wset_rel list_rel_sv_iff)
qed


subsection \<open>image\<close>

lemma image_list_wset_rel[autoref_rules]:
  assumes "PREFER single_valued B"
  shows "(map, (`)) \<in> (A \<rightarrow> B) \<rightarrow> \<langle>A\<rangle>list_wset_rel \<rightarrow> \<langle>B\<rangle>list_wset_rel"
  unfolding list_wset_rel_def relcomp_unfold
proof safe
  fix a a' aa a'a y
  assume H: "(a, a') \<in> A \<rightarrow> B" "(aa, y) \<in> br set top" "(y, a'a) \<in> \<langle>A\<rangle>set_rel"
  have "(map a aa, a ` y) \<in> br set top"
    using H
    by (auto simp: br_def)
  moreover have " (a ` y, a' ` a'a) \<in> \<langle>B\<rangle>set_rel"
    using H
    by (fastforce simp: fun_rel_def set_rel_def split: prod.split)
  ultimately show "\<exists>y. (map a aa, y) \<in> br set top \<and> (y, a' ` a'a) \<in> \<langle>B\<rangle>set_rel"
    by (safe intro!: exI[where x = "a ` y"])
qed

subsection \<open>Ball\<close>

lemma Ball_list_wset_rel[autoref_rules]:
  "((\<lambda>xs p. foldli xs (\<lambda>x. x) (\<lambda>a _. p a) True), Ball) \<in> \<langle>A\<rangle>list_wset_rel \<rightarrow> (A \<rightarrow> bool_rel) \<rightarrow> bool_rel"
proof -
  have "(set a, a') \<in> \<langle>A\<rangle>set_rel \<Longrightarrow> (Ball (set a), Ball a') \<in> (A \<rightarrow> bool_rel) \<rightarrow> bool_rel" for a a'
    by parametricity
  then have "(\<lambda>xs. Ball (set xs), Ball) \<in> {(x, z). (set x, z) \<in> \<langle>A\<rangle>set_rel} \<rightarrow> (A \<rightarrow> bool_rel) \<rightarrow> bool_rel"
    unfolding mem_Collect_eq split_beta' fst_conv snd_conv
    by (rule fun_relI) auto
  then show ?thesis
    by (simp add: relcomp_unfold br_def foldli_ball_aux list_wset_rel_def)
qed


subsection \<open>weak foreach loop\<close>

definition FORWEAK :: "'a set \<Rightarrow> 'b nres \<Rightarrow> ('a \<Rightarrow> 'b nres) \<Rightarrow> ('b \<Rightarrow> 'b \<Rightarrow> 'b nres) \<Rightarrow> 'b nres"
where "FORWEAK X d f c =
  (if X = {} then d
  else do {
    (a, X) \<leftarrow> op_set_npick_remove X;
    b \<leftarrow> f a;
    (b, _) \<leftarrow> WHILE (\<lambda>(_, X). \<not> op_set_isEmpty X) (\<lambda>(b, X).
      do {
        ASSERT (X \<noteq> {});
        (a, X) \<leftarrow> op_set_npick_remove X;
        b' \<leftarrow> f a;
        b \<leftarrow> c b b';
        RETURN (b, X)
      }) (b, X);
    RETURN b
  })"

schematic_goal
  FORWEAK_wset_WHILE_refine:
  assumes [relator_props]: "single_valued A"
  assumes [autoref_rules]:
    "(Xi, X) \<in> \<langle>A\<rangle>list_wset_rel"
    "(di, d) \<in> \<langle>B\<rangle>nres_rel"
    "(fi, f) \<in> A \<rightarrow> \<langle>B\<rangle>nres_rel"
    "(ci, c) \<in> B \<rightarrow> B \<rightarrow> \<langle>B\<rangle>nres_rel"
  shows "(?f, FORWEAK X d f c) \<in> \<langle>B\<rangle>nres_rel"
  unfolding FORWEAK_def
  by autoref

lemma FORWEAK_LIST_transfer_nfoldli:
  "nfoldli xs (\<lambda>_. True) (\<lambda>x a. c a x) a \<le> do {
    (a, _) \<leftarrow>
      WHILE (\<lambda>(a, xs). xs \<noteq> []) (\<lambda>(a, xs). do {
        (x, xs) \<leftarrow> RETURN (hd xs, tl xs);
        a \<leftarrow> c a x;
        RETURN (a, xs)
      }) (a, xs);
    RETURN a}"
proof (induct xs arbitrary: a)
  case Nil thus ?case by (auto simp: WHILE_unfold)
next
  case (Cons x xs)
  show ?case
    by (auto simp: WHILE_unfold intro!: bind_mono Cons[THEN order.trans])
qed

lemma
  FORWEAK_wset_refine:
  assumes [relator_props]: "PREFER single_valued A"
  assumes [autoref_rules]:
    "(Xi, X) \<in> \<langle>A\<rangle>list_wset_rel"
    "(di, d) \<in> \<langle>B\<rangle>nres_rel"
    "(fi, f) \<in> A \<rightarrow> \<langle>B\<rangle>nres_rel"
    "(ci, c) \<in> B \<rightarrow> B \<rightarrow> \<langle>B\<rangle>nres_rel"
  shows
    "((if Xi = [] then di else do { b \<leftarrow> fi (hd Xi); nfoldli (tl Xi) (\<lambda>_. True) (\<lambda>x b. do {b' \<leftarrow> fi x; ci b b'}) b }),
      (OP FORWEAK ::: \<langle>A\<rangle>list_wset_rel \<rightarrow> \<langle>B\<rangle>nres_rel \<rightarrow> (A \<rightarrow> \<langle>B\<rangle>nres_rel) \<rightarrow> (B \<rightarrow> B \<rightarrow> \<langle>B\<rangle>nres_rel) \<rightarrow> \<langle>B\<rangle>nres_rel) $ X $ d $ f $ c) \<in> \<langle>B\<rangle>nres_rel"
  unfolding autoref_tag_defs
  by (rule nres_rel_trans1[OF _ FORWEAK_wset_WHILE_refine[OF assms[simplified autoref_tag_defs]]])
    (auto intro!: bind_mono FORWEAK_LIST_transfer_nfoldli[THEN order.trans])
concrete_definition FORWEAK_LIST for Xi di fi ci uses FORWEAK_wset_refine
lemmas [autoref_rules] = FORWEAK_LIST.refine

schematic_goal FORWEAK_LIST_transfer_nres:
  assumes [refine_transfer]: "nres_of d \<le> d'"
  assumes [refine_transfer]: "\<And>x. nres_of (f x) \<le> f' x"
  assumes [refine_transfer]: "\<And>x y. nres_of (g x y) \<le> g' x y"
  shows
  "nres_of (?f) \<le> FORWEAK_LIST xs d' f' g'"
  unfolding FORWEAK_LIST_def
  by refine_transfer
concrete_definition dFORWEAK_LIST for xs d f g uses FORWEAK_LIST_transfer_nres
lemmas [refine_transfer] = dFORWEAK_LIST.refine

schematic_goal FORWEAK_LIST_transfer_plain:
  assumes [refine_transfer]: "RETURN d \<le> d'"
  assumes [refine_transfer]: "\<And>x. RETURN (f x) \<le> f' x"
  assumes [refine_transfer]: "\<And>x y. RETURN (g x y) \<le> g' x y"
  shows "RETURN ?f \<le> FORWEAK_LIST xs d' f' g'"
  unfolding FORWEAK_LIST_def
  by refine_transfer
concrete_definition FORWEAK_LIST_plain for xs f g uses FORWEAK_LIST_transfer_plain
lemmas [refine_transfer] = FORWEAK_LIST_plain.refine

schematic_goal FORWEAK_LIST_transfer_ne_plain:
  assumes "SIDE_PRECOND_OPT (xs \<noteq> [])"
  assumes [refine_transfer]: "\<And>x. RETURN (f x) \<le> f' x"
  assumes [refine_transfer]: "\<And>x y. RETURN (g x y) \<le> g' x y"
  shows "RETURN ?f \<le> FORWEAK_LIST xs d' f' g'"
  using assms
  by (simp add: FORWEAK_LIST_def) refine_transfer
concrete_definition FORWEAK_LIST_ne_plain for xs f g uses FORWEAK_LIST_transfer_ne_plain


lemma FORWEAK_empty[simp]: "FORWEAK {} = (\<lambda>d _ _. d)"
  by (auto simp: FORWEAK_def[abs_def])

lemma FORWEAK_WHILE_casesI:
  assumes "X = {} \<Longrightarrow> d \<le> SPEC P"
  assumes "\<And>a X'. a \<in> X \<Longrightarrow> X' = X - {a} \<Longrightarrow>
    f a \<le> SPEC (\<lambda>x. WHILE (\<lambda>(_, X). X \<noteq> {})
          (\<lambda>(b, X).
            do {
              ASSERT (X \<noteq> {});
              (a, X) \<leftarrow> op_set_npick_remove X;
              b' \<leftarrow> f a;
              b \<leftarrow> c b b';
              RETURN (b, X)
            })
          (x, X')
         \<le> SPEC (\<lambda>(b, _). RETURN b \<le> SPEC P))"
  assumes "\<And>a. a \<in> X \<Longrightarrow>
    f a \<le> SPEC (\<lambda>x. WHILE (\<lambda>(_, X). X \<noteq> {})
          (\<lambda>(b, X).
            do {
              ASSERT (X \<noteq> {});
              (a, X) \<leftarrow> op_set_npick_remove X;
              b' \<leftarrow> f a;
              b \<leftarrow> c b b';
              RETURN (b, X)
            })
          (x, X)
         \<le> SPEC (\<lambda>(b, _). RETURN b \<le> SPEC P))"
  shows "FORWEAK X d f c \<le> SPEC P"
  unfolding FORWEAK_def
  apply (cases "X = {}")
  subgoal by (simp add: assms(1))
  subgoal
    supply op_set_npick_remove_def[refine_vcg_def]
    apply (refine_vcg)
    apply clarsimp
    apply (erule disjE)
    subgoal
      by (refine_vcg assms(2))
    subgoal
      by (refine_vcg assms(3))
    done
  done

lemma FORWEAK_invarI:
  fixes I::"'b \<Rightarrow> 'a set \<Rightarrow> bool"
  assumes "X = {} \<Longrightarrow> d \<le> SPEC P"
  assumes fspec_init1[THEN order_trans]: "\<And>a. a \<in> X \<Longrightarrow> f a \<le> SPEC (\<lambda>x. I x (X - {a}))"
  assumes fspec_init2[THEN order_trans]: "\<And>a. a \<in> X \<Longrightarrow> f a \<le> SPEC (\<lambda>x. I x X)"
  assumes fspec_invar1[THEN order_trans]:
    "\<And>a aa b ba. I aa b \<Longrightarrow> a \<in> b \<Longrightarrow> f a \<le> SPEC (\<lambda>xb. c aa xb \<le> SPEC (\<lambda>r. I r (b - {a})))"
  assumes fspec_invar2[THEN order_trans]: "\<And>a aa b ba. I aa b \<Longrightarrow> a \<in> b \<Longrightarrow> f a \<le> SPEC (\<lambda>xb. c aa xb \<le> SPEC (\<lambda>r. I r b))"
  assumes fin: "\<And>aa. I aa {} \<Longrightarrow> P aa"
  shows "FORWEAK X d f c \<le> SPEC P"
  unfolding FORWEAK_def
  apply (cases "X = {}")
  subgoal by (simp add: assms(1))
  subgoal
    supply op_set_npick_remove_def[refine_vcg_def]
    apply (refine_vcg)
    apply clarsimp
    apply (erule disjE)
    subgoal
      apply (refine_vcg fspec_init1)
      apply (rule order_trans[OF WHILE_le_WHILEI[where I="\<lambda>(a, b). I a b"]])
      apply (refine_vcg)
      subgoal
        apply clarsimp
        apply (erule disjE)
        subgoal by (rule fspec_invar1, assumption, assumption)  (refine_vcg)
        subgoal by (rule fspec_invar2, assumption, assumption)  (refine_vcg)
        done
      subgoal by (simp add: fin)
      done
    subgoal
      apply (refine_vcg fspec_init2)
      apply (rule order_trans[OF WHILE_le_WHILEI[where I="\<lambda>(a, b). I a b"]])
      apply (refine_vcg)
      subgoal
        apply clarsimp
        apply (erule disjE)
        subgoal by (rule fspec_invar1, assumption, assumption)  (refine_vcg)
        subgoal by (rule fspec_invar2, assumption, assumption)  (refine_vcg)
        done
      subgoal by (simp add: fin)
      done
    done
  done

lemma FORWEAK_mono_rule:
  fixes f::"'d \<Rightarrow> 'e nres" and c::"'e \<Rightarrow> 'e \<Rightarrow> 'e nres" and I::"'d set \<Rightarrow> 'e \<Rightarrow> bool"
  assumes empty: "S = {} \<Longrightarrow> d \<le> SPEC P"
  assumes I0[THEN order_trans]: "\<And>s. s \<in> S \<Longrightarrow> f s \<le> SPEC (I {s})"
  assumes I_mono: "\<And>it it' \<sigma>. I it \<sigma> \<Longrightarrow> it' \<subseteq> it \<Longrightarrow> it \<subseteq> S \<Longrightarrow> I it' \<sigma>"
  assumes IP[THEN order_trans]:
    "\<And>x it \<sigma>. \<lbrakk> x\<in>S; it\<subseteq>S; I it \<sigma> \<rbrakk> \<Longrightarrow> f x \<le> SPEC (\<lambda>f'. c \<sigma> f' \<le> SPEC (I (insert x it)))"
  assumes II: "\<And>\<sigma>. I S \<sigma> \<Longrightarrow> P \<sigma>"
  shows "FORWEAK S d f c \<le> SPEC P"
  apply (rule FORWEAK_invarI[where I="\<lambda>b X. X \<subseteq> S \<and> I (S - X) b"])
  subgoal by (rule empty)
  subgoal by (auto simp: Diff_Diff_Int intro!: I0)
  subgoal
    by (metis (mono_tags, lifting) Diff_cancel I0 I_mono Refine_Basic.RES_sng_eq_RETURN iSPEC_rule
        less_eq_nres.simps(2) nres_order_simps(21) subset_insertI subset_refl)
  subgoal for a b it
    apply (rule IP[of _ "S - it" b])
    subgoal by force
    subgoal by force
    subgoal by force
    subgoal
      apply clarsimp
      apply (rule order_trans, assumption)
      by (auto simp: it_step_insert_iff intro: order_trans)
    done
  subgoal for a b it
    apply (rule IP[of _ "S - it" b])
    subgoal by force
    subgoal by force
    subgoal by force
    subgoal
      apply clarsimp
      apply (rule order_trans, assumption)
      by (auto simp: it_step_insert_iff intro: I_mono)
    done
  subgoal by (auto intro!: II)
  done

lemma FORWEAK_case_rule:
  fixes f::"'d \<Rightarrow> 'e nres" and c::"'e \<Rightarrow> 'e \<Rightarrow> 'e nres" and I::"'d set \<Rightarrow> 'e \<Rightarrow> bool"
  assumes empty: "S = {} \<Longrightarrow> d \<le> SPEC P"
  assumes I01[THEN order_trans]: "\<And>s. s \<in> S \<Longrightarrow> f s \<le> SPEC (I (S - {s}))"
  assumes I02[THEN order_trans]: "\<And>s. s \<in> S \<Longrightarrow> f s \<le> SPEC (I S)"
  assumes IP1[THEN order_trans]:
    "\<And>x it \<sigma>. \<lbrakk> x\<in>it; it\<subseteq>S; I it \<sigma> \<rbrakk> \<Longrightarrow> f x \<le> SPEC (\<lambda>f'. c \<sigma> f' \<le> SPEC (I (it-{x})))"
  assumes IP2[THEN order_trans]:
    "\<And>x it \<sigma>. \<lbrakk> x\<in>it; it\<subseteq>S; I it \<sigma> \<rbrakk> \<Longrightarrow> f x \<le> SPEC (\<lambda>f'. c \<sigma> f' \<le> SPEC (I it))"
  assumes II: "\<And>\<sigma>. I {} \<sigma> \<Longrightarrow> P \<sigma>"
  shows "FORWEAK S d f c \<le> SPEC P"
  apply (rule FORWEAK_invarI[where I = "\<lambda>a b. I b a \<and> b \<subseteq> S"])
  subgoal by (rule empty)
  subgoal by (rule I01) auto
  subgoal by (rule I02) auto
  subgoal for a b it
    apply (rule IP1[of a it b])
    subgoal by force
    subgoal by force
    subgoal by force
    subgoal
      apply clarsimp
      by (rule order_trans, assumption) auto
    done
  subgoal by (rule IP2) auto
  subgoal by (rule II) auto
  done

lemma FORWEAK_elementwise_rule:
  assumes "nofail d"
  assumes Inf_spec: "\<And>X. X \<in> XX \<Longrightarrow> Inf_spec X \<le> SPEC (Q X)"
  notes [refine_vcg] = order.trans[OF Inf_spec]
  assumes comb_spec1: "\<And>a b X Y. Q X a \<Longrightarrow> comb a b \<le> SPEC (Q X)"
  assumes comb_spec2: "\<And>a b X Y. Q X b \<Longrightarrow> comb a b \<le> SPEC (Q X)"
  shows "FORWEAK XX d Inf_spec comb \<le> SPEC (\<lambda>i. \<forall>x\<in>XX. Q x i)"
  apply (rule FORWEAK_mono_rule[where I="\<lambda>S i. \<forall>x\<in>S. Q x i"])
  subgoal using \<open>nofail d\<close> by (simp add: nofail_SPEC_iff)
  subgoal by (simp add: Diff_Diff_Int Inf_spec)
  subgoal by force
    subgoal for x it \<sigma>
      apply (refine_transfer refine_vcg)
      apply (rule SPEC_BallI)
      apply (rule SPEC_nofail)
      apply (rule comb_spec2)
      apply assumption
      subgoal for y z
        apply (cases "z = x")
        subgoal by simp (rule comb_spec2)
        subgoal by (rule comb_spec1) force
        done
      done
    subgoal by force
  done

end

lemma nofail_imp_RES_UNIV: "nofail s \<Longrightarrow> s \<le> RES UNIV"
  by (metis Refine_Basic.nofail_SPEC_triv_refine UNIV_I top_empty_eq top_set_def)

lemma FORWEAK_unit_rule[THEN order_trans, refine_vcg]:
  assumes "nofail d"
  assumes "\<And>s. nofail (f s)"
  assumes "nofail (c () ())"
  shows "FORWEAK XS d f c \<le> SPEC (\<lambda>(_::unit). True)"
  using assms
  by (intro order_trans[OF FORWEAK_elementwise_rule[where Q=top]])
    (auto simp: top_fun_def le_SPEC_UNIV_rule nofail_SPEC_triv_refine nofail_imp_RES_UNIV)

lemma FORWEAK_mono_rule':
  fixes f::"'d \<Rightarrow> 'e nres" and c::"'e \<Rightarrow> 'e \<Rightarrow> 'e nres" and I::"'d set \<Rightarrow> 'e \<Rightarrow> bool"
  assumes empty: "S = {} \<Longrightarrow> d \<le> SPEC P"
  assumes I0[THEN order_trans]: "\<And>s. s \<in> S \<Longrightarrow> f s \<le> SPEC (I {s})"
  assumes I_mono: "\<And>ab bb xb. ab \<in> bb \<Longrightarrow> bb \<subseteq> S \<Longrightarrow> I (insert ab (S - bb)) xb \<Longrightarrow> I (S - bb) xb"
  assumes IP[THEN order_trans]:
    "\<And>x it \<sigma>. \<lbrakk> x\<in>S; it\<subseteq>S; I it \<sigma> \<rbrakk> \<Longrightarrow> f x \<le> SPEC (\<lambda>f'. c \<sigma> f' \<le> SPEC (I (insert x it)))"
  assumes II: "\<And>\<sigma>. I S \<sigma> \<Longrightarrow> P \<sigma>"
  shows "FORWEAK S d f c \<le> SPEC P"
  apply (rule FORWEAK_invarI[where I="\<lambda>b X. X \<subseteq> S \<and> I (S - X) b"])
  subgoal by (rule empty)
  subgoal by (auto simp: Diff_Diff_Int intro!: I0)
  subgoal
    apply (rule I0, assumption)
    apply (rule SPEC_rule)
    apply (rule conjI)
    subgoal by simp
    subgoal by (rule I_mono, assumption) auto
    done
  subgoal for a b it
    apply (rule IP[of _ "S - it" b])
    subgoal by force
    subgoal by force
    subgoal by force
    subgoal
      apply clarsimp
      apply (rule order_trans, assumption)
      by (auto simp: it_step_insert_iff intro: order_trans)
    done
  subgoal for a b it
    apply (rule IP[of _ "S - it" b])
    subgoal by force
    subgoal by force
    subgoal by force
    subgoal
      apply clarsimp
      apply (rule order_trans, assumption)
      by (auto simp: it_step_insert_iff intro: I_mono)
    done
  subgoal by (auto intro!: II)
  done

lemma
  op_set_npick_remove_refine_SPEC[refine_vcg]:
  assumes "\<And>x X'. x \<in> X1 \<Longrightarrow> X' = X1 - {x} \<Longrightarrow> Q (x, X')"
  assumes "\<And>x. x \<in> X1 \<Longrightarrow> Q (x, X1)"
  shows "op_set_npick_remove X1 \<le> SPEC Q"
  using assms
  by (auto simp: op_set_npick_remove_def )

context includes autoref_syntax begin
definition "op_set_pick_remove X \<equiv> SPEC (\<lambda>(x, X'). x \<in> X \<and> X' = X - {x})"
lemma op_set_pick_removepat[autoref_op_pat]:
  "SPEC (\<lambda>(x, X'). x \<in> X \<and> X' = X - {x}) \<equiv> op_set_pick_remove $ X"
  "do { x \<leftarrow> SPEC (\<lambda>x. x \<in> X); let X' = X - {x}; f x X' } \<equiv> do { (x, X') \<leftarrow> op_set_pick_remove X; f x X'}"
  by (auto simp: op_set_pick_remove_def pw_eq_iff refine_pw_simps intro!: eq_reflection)

lemma list_all2_tlI: "list_all2 A XS y \<Longrightarrow> list_all2 A (tl XS) (tl y)"
  by (metis list.rel_sel list.sel(2))

lemma
  op_set_pick_remove_refine[autoref_rules]:
  assumes "(XS, X) \<in> \<langle>A\<rangle>list_set_rel"
  assumes "SIDE_PRECOND (X \<noteq> {})"
  shows "(nres_of (dRETURN (hd XS, tl XS)), op_set_pick_remove $ X) \<in> \<langle>A \<times>\<^sub>r \<langle>A\<rangle>list_set_rel\<rangle>nres_rel"
  using assms(1)
  unfolding op_set_pick_remove_def[abs_def] autoref_tag_defs list_set_rel_def list_rel_def br_def
  apply (intro nres_relI SPEC_refine det_SPEC)
  apply safe
  subgoal for x y z
    using assms(2)
    apply (safe intro!: exI[where x="(hd y, set (tl y))"])
    subgoal
      apply (rule prod_relI)
      subgoal by (induct XS y rule: list_all2_induct) auto
      subgoal
        apply (rule relcompI[where b = "tl y"])
        subgoal
          unfolding mem_Collect_eq split_beta' fst_conv snd_conv
          by (rule list_all2_tlI)
        subgoal
          unfolding mem_Collect_eq split_beta' fst_conv snd_conv
          apply (rule conjI)
          subgoal by (metis remove1_tl set_remove1_eq)
          subgoal by simp
          done
        done
      done
    subgoal by (subst (asm) list.rel_sel) simp
    subgoal by (simp add: in_set_tlD)
    subgoal by (simp add: distinct_hd_tl)
    subgoal by auto (meson in_hd_or_tl_conv)
    done
  done

definition [simp, refine_vcg_def]: "isEmpty_spec X = SPEC (\<lambda>b. b \<longrightarrow> X = {})"

lemma [autoref_itype]: "isEmpty_spec::\<^sub>i A \<rightarrow>\<^sub>i \<langle>i_bool\<rangle>\<^sub>ii_nres"
  by simp
lemma op_wset_isEmpty_list_wset_rel[autoref_rules]:
  "(\<lambda>x. RETURN (x = []), isEmpty_spec) \<in> \<langle>A\<rangle>list_wset_rel \<rightarrow> \<langle>bool_rel\<rangle>nres_rel"
  by (auto simp: nres_rel_def list_wset_rel_def set_rel_def br_def)


definition WEAK_ALL:: "('a \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> ('a \<Rightarrow> bool nres) \<Rightarrow> bool nres" ("WEAK'_ALL\<^bsup>_\<^esup>") where
  "WEAK_ALL I X P = do {
    (_, b) \<leftarrow> WHILE\<^bsup>\<lambda>(Y, b). b \<longrightarrow> (\<forall>x \<in> X - Y. I x)\<^esup> (\<lambda>(X, b). b \<and> X \<noteq> {}) (\<lambda>(X, b). do {
      ASSERT (X \<noteq> {});
      (x, X') \<leftarrow> op_set_npick_remove X;
      b' \<leftarrow> P x;
      RETURN (X', b' \<and> b)
    }) (X, True); RETURN b}"
schematic_goal WEAK_ALL_list[autoref_rules]:
  assumes [relator_props]: "single_valued A"
  assumes [autoref_rules]: "(Xi, X) \<in> \<langle>A\<rangle>list_wset_rel"
      "(P_impl, P) \<in> A \<rightarrow> \<langle>bool_rel\<rangle>nres_rel"
  shows "(?r, WEAK_ALL I X P) \<in> \<langle>bool_rel\<rangle>nres_rel"
  unfolding WEAK_ALL_def
  including art
  by (autoref)
concrete_definition WEAK_ALL_list for Xi P_impl uses WEAK_ALL_list
lemma WEAK_ALL_list_refine[autoref_rules]:
  "PREFER single_valued A \<Longrightarrow> (WEAK_ALL_list, WEAK_ALL I) \<in> \<langle>A\<rangle>list_wset_rel \<rightarrow> (A \<rightarrow> \<langle>bool_rel\<rangle>nres_rel) \<rightarrow> \<langle>bool_rel\<rangle>nres_rel"
  using WEAK_ALL_list.refine by force

schematic_goal WEAK_ALL_transfer_nres:
  assumes [refine_transfer]: "\<And>x. nres_of (f x) \<le> f' x"
  shows "nres_of (?f) \<le> WEAK_ALL_list xs f'"
  unfolding WEAK_ALL_list_def
  by refine_transfer
concrete_definition dWEAK_ALL for xs f uses WEAK_ALL_transfer_nres
lemmas [refine_transfer] = dWEAK_ALL.refine

definition WEAK_EX:: "('a \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> ('a \<Rightarrow> bool nres) \<Rightarrow> bool nres" ("WEAK'_EX\<^bsup>_\<^esup>") where
  "WEAK_EX I X P = do {
    (_, b) \<leftarrow> WHILE\<^bsup>\<lambda>(Y, b). Y \<subseteq> X \<and> (b \<longrightarrow> (\<exists>x \<in> X. I x))\<^esup> (\<lambda>(X, b). \<not>b \<and> X \<noteq> {}) (\<lambda>(X, b). do {
      ASSERT (X \<noteq> {});
      (x, X') \<leftarrow> op_set_npick_remove X;
      b' \<leftarrow> P x;
      RETURN (X', b' \<or> b)
    }) (X, False); RETURN b}"
schematic_goal WEAK_EX_list[autoref_rules]:
  assumes [relator_props]: "single_valued A"
  assumes [autoref_rules]: "(Xi, X) \<in> \<langle>A\<rangle>list_wset_rel"
      "(P_impl, P) \<in> A \<rightarrow> \<langle>bool_rel\<rangle>nres_rel"
  shows "(?r, WEAK_EX I X P) \<in> \<langle>bool_rel\<rangle>nres_rel"
  unfolding WEAK_EX_def
  including art
  by (autoref)
concrete_definition WEAK_EX_list for Xi P_impl uses WEAK_EX_list
lemma WEAK_EX_list_refine[autoref_rules]:
  "PREFER single_valued A \<Longrightarrow> (WEAK_EX_list, WEAK_EX I) \<in> \<langle>A\<rangle>list_wset_rel \<rightarrow> (A \<rightarrow> \<langle>bool_rel\<rangle>nres_rel) \<rightarrow> \<langle>bool_rel\<rangle>nres_rel"
  using WEAK_EX_list.refine by force

schematic_goal WEAK_EX_transfer_nres:
  assumes [refine_transfer]: "\<And>x. nres_of (f x) \<le> f' x"
  shows "nres_of (?f) \<le> WEAK_EX_list xs f'"
  unfolding WEAK_EX_list_def
  by refine_transfer
concrete_definition dWEAK_EX for xs f uses WEAK_EX_transfer_nres
lemmas [refine_transfer] = dWEAK_EX.refine

lemma WEAK_EX[THEN order_trans, refine_vcg]:
  assumes [THEN order_trans, refine_vcg]: "\<And>x. F x \<le> SPEC (\<lambda>r. r \<longrightarrow> I x)"
  shows "WEAK_EX I X F \<le> SPEC (\<lambda>r. r \<longrightarrow> (\<exists>x\<in>X. I x))"
  unfolding WEAK_EX_def
  by (refine_vcg ) (auto simp: )

lemma WEAK_ALL[THEN order_trans, refine_vcg]:
  assumes [THEN order_trans, refine_vcg]: "\<And>x. F x \<le> SPEC (\<lambda>r. r \<longrightarrow> I x)"
  shows "WEAK_ALL I X F \<le> SPEC (\<lambda>r. r \<longrightarrow> (\<forall>x\<in>X. I x))"
  unfolding WEAK_ALL_def
  by (refine_vcg) auto

lemma [autoref_op_pat_def]:
  "WEAK_ALL I \<equiv> OP (WEAK_ALL I)"
  "WEAK_EX I \<equiv> OP (WEAK_EX I)"
  by auto

lemma list_spec_impl[autoref_rules]:
  "(\<lambda>x. RETURN x, list_spec) \<in> \<langle>A\<rangle>list_wset_rel \<rightarrow> \<langle>\<langle>A\<rangle>list_rel\<rangle>nres_rel"
  if "PREFER single_valued A"
  using that
  apply (auto simp: list_spec_def nres_rel_def RETURN_RES_refine_iff list_wset_rel_br_eq
      br_list_rel intro!: brI dest!: brD
      elim!: single_valued_as_brE)
  subgoal for a I xs
    apply (rule exI[where x="map a xs"])
    by (auto simp: br_def list_all_iff)
  done

lemma list_wset_autoref_delete[autoref_rules]:
  assumes "PREFER single_valued R"
  assumes "GEN_OP eq (=) (R \<rightarrow> R \<rightarrow> bool_rel)"
  shows "(\<lambda>y xs. [x\<leftarrow>xs. \<not>eq y x], op_set_delete) \<in> R \<rightarrow> \<langle>R\<rangle>list_wset_rel \<rightarrow> \<langle>R\<rangle>list_wset_rel"
  using assms
  apply (auto simp: list_wset_rel_def dest!: brD elim!: single_valued_as_brE)
  apply (rule relcompI)
   apply (rule brI)
    apply (rule refl)
   apply auto
  apply (auto simp: set_rel_br)
  apply (rule brI)
   apply (auto dest!: brD dest: fun_relD)
   apply (auto simp: image_iff dest: fun_relD intro: brI)
  subgoal for a b c d e
    apply (drule spec[where x=e])
    apply auto
    apply (drule fun_relD)
     apply (rule brI[where c="c"])
      apply (rule refl)
     apply assumption
    apply (drule bspec, assumption)
    apply (drule fun_relD)
     apply (rule brI[where c="e"])
      apply (rule refl)
     apply assumption
    apply auto
    done
  done

lemma FORWEAK_mono_rule'':
  fixes f::"'d \<Rightarrow> 'e nres" and c::"'e \<Rightarrow> 'e \<Rightarrow> 'e nres" and I::"'d set \<Rightarrow> 'e \<Rightarrow> bool"
  assumes empty: "S = {} \<Longrightarrow> d \<le> SPEC P"
  assumes I0[THEN order_trans]: "\<And>s. s \<in> S \<Longrightarrow> f s \<le> SPEC (I {s})"
  assumes I_mono: "\<And>it it' \<sigma>. I it \<sigma> \<Longrightarrow> it' \<subseteq> it \<Longrightarrow> it \<subseteq> S \<Longrightarrow> I it' \<sigma>"
  assumes IP[THEN order_trans]:
    "\<And>x it \<sigma>. \<lbrakk> x\<in>S; x \<notin> it; it\<subseteq>S; I it \<sigma> \<rbrakk> \<Longrightarrow> f x \<le> SPEC (\<lambda>f'. c \<sigma> f' \<le> SPEC (I (insert x it)))"
  assumes II: "\<And>\<sigma>. I S \<sigma> \<Longrightarrow> P \<sigma>"
  shows "FORWEAK S d f c \<le> SPEC P"
  apply (rule FORWEAK_invarI[where I="\<lambda>b X. X \<subseteq> S \<and> I (S - X) b"])
  subgoal by (rule empty)
  subgoal by (auto simp: Diff_Diff_Int intro!: I0)
  subgoal
    by (metis (mono_tags, lifting) Diff_cancel I0 I_mono Refine_Basic.RES_sng_eq_RETURN iSPEC_rule
        less_eq_nres.simps(2) nres_order_simps(21) subset_insertI subset_refl)
  subgoal for a b it
    apply (rule IP[of _ "S - it" b])
    subgoal by force
    subgoal by force
    subgoal by force
    subgoal by force
    subgoal
      apply clarsimp
      apply (rule order_trans, assumption)
      by (auto simp: it_step_insert_iff intro: order_trans)
    done
  subgoal for a b it
    apply (rule IP[of _ "S - it" b])
    subgoal by force
    subgoal by force
    subgoal by force
    subgoal by force
    subgoal
      apply clarsimp
      apply (rule order_trans, assumption)
      by (auto simp: it_step_insert_iff intro: I_mono)
    done
  subgoal by (auto intro!: II)
  done

lemma FORWEAK_mono_rule_empty:
  fixes f::"'d \<Rightarrow> 'e nres" and c::"'e \<Rightarrow> 'e \<Rightarrow> 'e nres" and I::"'d set \<Rightarrow> 'e \<Rightarrow> bool"
  assumes empty: "S = {} \<Longrightarrow> RETURN d \<le> SPEC P"
  assumes I0: "I {} d"
  assumes I1: "\<And>s x. s \<in> S \<Longrightarrow> c d x \<le> SPEC (I {s}) \<Longrightarrow> I {s} x"
  assumes I_mono: "\<And>it it' \<sigma>. I it \<sigma> \<Longrightarrow> it' \<subseteq> it \<Longrightarrow> it \<subseteq> S \<Longrightarrow> I it' \<sigma>"
  assumes II: "\<And>\<sigma>. I S \<sigma> \<Longrightarrow> P \<sigma>"
  assumes IP: "\<And>x it \<sigma>. \<lbrakk> x\<in>S; x \<notin> it; it\<subseteq>S; I it \<sigma> \<rbrakk> \<Longrightarrow> f x \<le> SPEC (\<lambda>f'. c \<sigma> f' \<le> SPEC (I (insert x it)))"
  shows "FORWEAK S (RETURN d) f c \<le> SPEC P"
  apply (rule FORWEAK_mono_rule''[where S=S and I=I and P=P])
  subgoal by (rule empty)
  subgoal for s
    apply (rule IP[of _ "{}" d, THEN order_trans])
       apply assumption
       apply force
       apply force
     apply (rule I0)
    by (auto intro!: I1)
  subgoal by (rule I_mono)
  subgoal by (rule IP)
  subgoal by (rule II)
  done

end

end
