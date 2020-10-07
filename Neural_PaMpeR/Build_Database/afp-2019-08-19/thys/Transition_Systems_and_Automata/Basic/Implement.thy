section \<open>Implementation\<close>

theory Implement
imports
  "HOL-Library.Monad_Syntax"
  "Collections.Refine_Dflt"
  "Refine"
begin

  subsection \<open>Syntax\<close>

  (* TODO: this syntax has unnecessarily high inner binding strength, requiring extra parentheses
    the regular let syntax correctly uses inner binding strength 0: ("(2_ =/ _)" 10) *)
  no_syntax "_do_let" :: "[pttrn, 'a] \<Rightarrow> do_bind" ("(2let _ =/ _)" [1000, 13] 13)
  syntax "_do_let" :: "[pttrn, 'a] \<Rightarrow> do_bind" ("(2let _ =/ _)" 13)

  subsection \<open>Monadic Refinement\<close>

  lemmas [refine] = plain_nres_relI

  lemma vcg0:
    assumes "(f, g) \<in> \<langle>Id\<rangle> nres_rel"
    shows "g \<le> h \<Longrightarrow> f \<le> h"
    using order_trans nres_relD[OF assms[param_fo, OF], THEN refine_IdD] by this
  lemma vcg1:
    assumes "(f, g) \<in> Id \<rightarrow> \<langle>Id\<rangle> nres_rel"
    shows "g x \<le> h x \<Longrightarrow> f x \<le> h x"
    using order_trans nres_relD[OF assms[param_fo, OF IdI], THEN refine_IdD] by this
  lemma vcg2:
    assumes "(f, g) \<in> Id \<rightarrow> Id \<rightarrow> \<langle>Id\<rangle> nres_rel"
    shows "g x y \<le> h x y \<Longrightarrow> f x y \<le> h x y"
    using order_trans nres_relD[OF assms[param_fo, OF IdI IdI], THEN refine_IdD] by this

  lemma RETURN_nres_relD:
    assumes "(RETURN x, RETURN y) \<in> \<langle>A\<rangle> nres_rel"
    shows "(x, y) \<in> A"
    using assms unfolding nres_rel_def by simp

  lemma FOREACH_rule_insert:
    assumes "finite S"
    assumes "I {} s"
    assumes "\<And> s. I S s \<Longrightarrow> P s"
    assumes "\<And> T x s. T \<subseteq> S \<Longrightarrow> I T s \<Longrightarrow> x \<in> S \<Longrightarrow> x \<notin> T \<Longrightarrow> f x s \<le> SPEC (I (insert x T))"
    shows "FOREACH S f s \<le> SPEC P"
  proof (rule FOREACH_rule[where I = "\<lambda> T s. I (S - T) s"])
    show "finite S" using assms(1) by this
    show "I (S - S) s" using assms(2) by simp
    show "P s" if "I (S - {}) s" for s using assms(3) that by simp
  next
    fix x T s
    assume 1: "x \<in> T" "T \<subseteq> S" "I (S - T) s"
    have "f x s \<le> SPEC (I (insert x (S - T)))" using assms(4) 1 by blast
    also have "insert x (S - T) = S - (T - {x})" using 1(1, 2) by (simp add: it_step_insert_iff)
    finally show "f x s \<le> SPEC (I (S - (T - {x})))" by this
  qed
  lemma FOREACH_rule_map:
    assumes "finite (dom g)"
    assumes "I Map.empty s"
    assumes "\<And> s. I g s \<Longrightarrow> P s"
    assumes "\<And> h k v s. h \<subseteq>\<^sub>m g \<Longrightarrow> I h s \<Longrightarrow> g k = Some v \<Longrightarrow> k \<notin> dom h \<Longrightarrow>
      f (k, v) s \<le> SPEC (I (h (k \<mapsto> v)))"
    shows "FOREACH (map_to_set g) f s \<le> SPEC P"
  proof (rule FOREACH_rule_insert[where I = "\<lambda> H s. I (set_to_map H) s"])
    show "finite (map_to_set g)" unfolding finite_map_to_set using assms(1) by this
    show "I (set_to_map {}) s" using assms(2) by simp
    show "P s" if "I (set_to_map (map_to_set g)) s" for s
      using assms(3) that unfolding map_to_set_inverse by this
  next
    fix H x s
    assume 1: "H \<subseteq> map_to_set g" "I (set_to_map H) s" "x \<in> map_to_set g" "x \<notin> H"
    obtain k v where 2: "x = (k, v)" by force
    have 3: "inj_on fst H" using inj_on_fst_map_to_set inj_on_subset 1(1) by blast
    have "f x s = f (k, v) s" unfolding 2 by rule
    also have "\<dots> \<le> SPEC (I (set_to_map H (k \<mapsto> v)))"
    proof (rule assms(4))
      show "set_to_map H \<subseteq>\<^sub>m g"
        using 1(1) 3
        by (metis inj_on_fst_map_to_set map_leI map_to_set_inverse set_to_map_simp subset_eq)
      show "I (set_to_map H) s" using 1(2) by this
      show "g k = Some v" using 1(3) unfolding 2 map_to_set_def by simp
      show "k \<notin> dom (set_to_map H)"
        using 1(1, 3, 4) unfolding 2 set_to_map_dom
        by (metis fst_conv inj_on_fst_map_to_set inj_on_image_mem_iff)
    qed
    also have "set_to_map H (k \<mapsto> v) = set_to_map H (fst x \<mapsto> snd x)" unfolding 2 by simp
    also have "\<dots> = set_to_map (insert x H)"
      using 1(1, 3, 4) by (metis inj_on_fst_map_to_set inj_on_image_mem_iff set_to_map_insert)
    finally show "f x s \<le> SPEC (I (set_to_map (insert x H)))" by this
  qed
  lemma FOREACH_rule_insert_eq:
    assumes "finite S"
    assumes "X {} = s"
    assumes "X S = t"
    assumes "\<And> T x. T \<subseteq> S \<Longrightarrow> x \<in> S \<Longrightarrow> x \<notin> T \<Longrightarrow> f x (X T) \<le> SPEC (HOL.eq (X (insert x T)))"
    shows "FOREACH S f s \<le> SPEC (HOL.eq t)"
    by (rule FOREACH_rule_insert[where I = "HOL.eq \<circ> X"]) (use assms in auto)
  lemma FOREACH_rule_map_eq:
    assumes "finite (dom g)"
    assumes "X Map.empty = s"
    assumes "X g = t"
    assumes "\<And> h k v. h \<subseteq>\<^sub>m g \<Longrightarrow> g k = Some v \<Longrightarrow> k \<notin> dom h \<Longrightarrow>
      f (k, v) (X h) \<le> SPEC (HOL.eq (X (h (k \<mapsto> v))))"
    shows "FOREACH (map_to_set g) f s \<le> SPEC (HOL.eq t)"
    by (rule FOREACH_rule_map[where I = "HOL.eq \<circ> X"]) (use assms in auto)

  lemma FOREACH_rule_map_map: "(FOREACH (map_to_set m) (\<lambda> (k, v). F k (f k v)),
    FOREACH (map_to_set (\<lambda> k. map_option (f k) (m k))) (\<lambda> (k, v). F k v)) \<in> Id \<rightarrow> \<langle>Id\<rangle> nres_rel"
  proof refine_vcg
    show "inj_on (\<lambda> (k, v). (k, f k v)) (map_to_set m)"
      unfolding map_to_set_def by rule auto
    show "map_to_set (\<lambda> k. map_option (f k) (m k)) = (\<lambda> (k, v). (k, f k v)) ` map_to_set m"
      unfolding map_to_set_def by auto
  qed auto

  subsection \<open>Implementations for Sets Represented by Lists\<close>

  lemma list_set_rel_Id_on[simp]: "\<langle>Id_on A\<rangle> list_set_rel = \<langle>Id\<rangle> list_set_rel \<inter> UNIV \<times> Pow A"
    unfolding list_set_rel_def relcomp_unfold in_br_conv by auto

  lemma list_set_card[param]: "(length, card) \<in> \<langle>A\<rangle> list_set_rel \<rightarrow> nat_rel"
    unfolding list_set_rel_def relcomp_unfold in_br_conv
    by (auto simp: distinct_card list_rel_imp_same_length)
  lemma list_set_insert[param]:
    assumes "y \<notin> Y"
    assumes "(x, y) \<in> A" "(xs, Y) \<in> \<langle>A\<rangle> list_set_rel"
    shows "(x # xs, insert y Y) \<in> \<langle>A\<rangle> list_set_rel"
    using assms unfolding list_set_rel_def relcomp_unfold in_br_conv
    by (auto) (metis refine_list(2)[param_fo] distinct.simps(2) list.simps(15))
  lemma list_set_union[param]:
    assumes "X \<inter> Y = {}"
    assumes "(xs, X) \<in> \<langle>A\<rangle> list_set_rel" "(ys, Y) \<in> \<langle>A\<rangle> list_set_rel"
    shows "(xs @ ys, X \<union> Y) \<in> \<langle>A\<rangle> list_set_rel"
    using assms unfolding list_set_rel_def relcomp_unfold in_br_conv
    by (auto) (meson param_append[param_fo] distinct_append set_union_code)
  lemma list_set_Union[param]:
    assumes "\<And> X Y. X \<in> S \<Longrightarrow> Y \<in> S \<Longrightarrow> X \<noteq> Y \<Longrightarrow> X \<inter> Y = {}"
    assumes "(xs, S) \<in> \<langle>\<langle>A\<rangle> list_set_rel\<rangle> list_set_rel"
    shows "(concat xs, Union S) \<in> \<langle>A\<rangle> list_set_rel"
  proof -
    note distinct_map[iff]
    obtain zs where 1: "(xs, zs) \<in> \<langle>\<langle>A\<rangle> list_set_rel\<rangle> list_rel" "S = set zs" "distinct zs"
      using assms(2) unfolding list_set_rel_def relcomp_unfold in_br_conv by auto
    obtain ys where 2: "(xs, ys) \<in> \<langle>\<langle>A\<rangle> list_rel\<rangle> list_rel" "zs = map set ys" "list_all distinct ys"
      using 1(1)
      unfolding list_set_rel_def list_rel_compp
      unfolding relcomp_unfold mem_Collect_eq prod.case
      unfolding br_list_rel in_br_conv
      by auto
    have 20: "set a \<in> S" "set b \<in> S" "set a \<noteq> set b" if "a \<in> set ys" "b \<in> set ys" "a \<noteq> b" for a b
      using 1(3) that unfolding 1(2) 2(2) by (auto dest: inj_onD)
    have 3: "set a \<inter> set b = {}" if "a \<in> set ys" "b \<in> set ys" "a \<noteq> b" for a b
      using assms(1) 20 that by auto
    have 4: "Union S = set (concat ys)" unfolding 1(2) 2(2) by simp
    have 5: "distinct (concat ys)"
      using 1(3) 2(2, 3) 3 unfolding list.pred_set by (blast intro: distinct_concat)
    have 6: "(concat xs, concat ys) \<in> \<langle>A\<rangle> list_rel" using 2(1) by parametricity
    show ?thesis unfolding list_set_rel_def relcomp_unfold in_br_conv using 4 5 6 by blast
  qed
  lemma list_set_image[param]:
    assumes "inj_on g S"
    assumes "(f, g) \<in> A \<rightarrow> B" "(xs, S) \<in> \<langle>A\<rangle> list_set_rel"
    shows "(map f xs, g ` S) \<in> \<langle>B\<rangle> list_set_rel"
    using assms unfolding list_set_rel_def relcomp_unfold in_br_conv
    using param_map[param_fo] distinct_map by fastforce
  lemma list_set_bind[param]:
    assumes "\<And> x y. x \<in> S \<Longrightarrow> y \<in> S \<Longrightarrow> x \<noteq> y \<Longrightarrow> g x \<inter> g y = {}"
    assumes "(xs, S) \<in> \<langle>A\<rangle> list_set_rel" "(f, g) \<in> A \<rightarrow> \<langle>B\<rangle> list_set_rel"
    shows "(xs \<bind> f, S \<bind> g) \<in> \<langle>B\<rangle> list_set_rel"
  proof -
    note [param] = list_set_autoref_filter list_set_autoref_isEmpty
    let ?xs = "filter (Not \<circ> is_Nil \<circ> f) xs"
    let ?S = "op_set_filter (Not \<circ> op_set_isEmpty \<circ> g) S"
    have 1: "inj_on g ?S" using assms(1) by (fastforce intro: inj_onI)
    have "xs \<bind> f = concat (map f ?xs)" by (induct xs) (auto split: list.split)
    also have "(\<dots>, \<Union> (g ` ?S)) \<in> \<langle>B\<rangle> list_set_rel" using assms 1 by parametricity auto
    also have "\<Union> (g ` ?S) = S \<bind> g" by auto auto
    finally show ?thesis by this
  qed

  subsection \<open>Autoref Setup\<close>

  (* TODO: inline this? *)
  lemma dflt_ahm_rel_finite_nat: "finite_map_rel (\<langle>nat_rel, V\<rangle> dflt_ahm_rel)" by tagged_solver

  context
  begin

    interpretation autoref_syn by this
    lemma [autoref_op_pat]: "(Some \<circ> f) |` X \<equiv> OP (\<lambda> f X. (Some \<circ> f) |` X) f X" by simp
    lemma [autoref_op_pat]: "\<Union>(m ` S) \<equiv> OP (\<lambda>S m. \<Union>(m ` S)) S m" by simp

    definition gen_UNION where
      "gen_UNION tol emp un X f \<equiv> fold (un \<circ> f) (tol X) emp"

    lemma gen_UNION[autoref_rules_raw]:
      assumes PRIO_TAG_GEN_ALGO
      assumes to_list: "SIDE_GEN_ALGO (is_set_to_list A Rs1 tol)"
      assumes empty: "GEN_OP emp {} (\<langle>B\<rangle> Rs3)"
      assumes union: "GEN_OP un union (\<langle>B\<rangle> Rs2 \<rightarrow> \<langle>B\<rangle> Rs3 \<rightarrow> \<langle>B\<rangle> Rs3)"
      shows "(gen_UNION tol emp un, \<lambda>A f. \<Union> (f ` A)) \<in> \<langle>A\<rangle> Rs1 \<rightarrow> (A \<rightarrow> \<langle>B\<rangle> Rs2) \<rightarrow> \<langle>B\<rangle> Rs3"
    proof (intro fun_relI)
      note [unfolded autoref_tag_defs, param] = empty union
      fix f g T S
      assume 1[param]: "(T, S) \<in> \<langle>A\<rangle> Rs1" "(g, f) \<in> A \<rightarrow> \<langle>B\<rangle> Rs2"
      obtain tsl' where
        [param]: "(tol T, tsl') \<in> \<langle>A\<rangle> list_rel"
        and IT': "RETURN tsl' \<le> it_to_sorted_list (\<lambda>_ _. True) S"
        using to_list[unfolded autoref_tag_defs is_set_to_list_def] 1(1)
        by (rule is_set_to_sorted_listE)
      from IT' have 10: "S = set tsl'" "distinct tsl'" unfolding it_to_sorted_list_def by simp_all
      have "gen_UNION tol emp un T g = fold (un \<circ> g) (tol T) emp" unfolding gen_UNION_def by rule
      also have "(\<dots>, fold (union \<circ> f) tsl' {}) \<in> \<langle>B\<rangle> Rs3" by parametricity
      also have "fold (union \<circ> f) tsl' X = \<Union>(f ` S) \<union> X" for X
        unfolding 10(1) by (induct tsl' arbitrary: X) (auto)
      also have "\<Union>(f ` S) \<union> {} = \<Union>(f ` S)" by simp
      finally show "(gen_UNION tol emp un T g, \<Union>(f ` S)) \<in> \<langle>B\<rangle> Rs3" by this
    qed

    definition gen_Image where
      "gen_Image tol1 mem2 emp3 ins3 X Y \<equiv> fold
        (\<lambda> (a, b). if mem2 a Y then ins3 b else id) (tol1 X) emp3"

    lemma gen_Image[autoref_rules]:
      assumes PRIO_TAG_GEN_ALGO
      assumes to_list: "SIDE_GEN_ALGO (is_set_to_list (A \<times>\<^sub>r B) Rs1 tol1)"
      assumes member: "GEN_OP mem2 (\<in>) (A \<rightarrow> \<langle>A\<rangle> Rs2 \<rightarrow> bool_rel)"
      assumes empty: "GEN_OP emp3 {} (\<langle>B\<rangle> Rs3)"
      assumes insert: "GEN_OP ins3 Set.insert (B \<rightarrow> \<langle>B\<rangle> Rs3 \<rightarrow> \<langle>B\<rangle> Rs3)"
      shows "(gen_Image tol1 mem2 emp3 ins3, Image) \<in> \<langle>A \<times>\<^sub>r B\<rangle> Rs1 \<rightarrow> \<langle>A\<rangle> Rs2 \<rightarrow> \<langle>B\<rangle> Rs3"
    proof (intro fun_relI)
      note [unfolded autoref_tag_defs, param] = member empty insert
      fix T S X Y
      assume 1[param]: "(T, S) \<in> \<langle>A \<times>\<^sub>r B\<rangle> Rs1" "(Y, X) \<in> \<langle>A\<rangle> Rs2"
      obtain tsl' where
        [param]: "(tol1 T, tsl') \<in> \<langle>A \<times>\<^sub>r B\<rangle> list_rel"
        and IT': "RETURN tsl' \<le> it_to_sorted_list (\<lambda>_ _. True) S"
        using to_list[unfolded autoref_tag_defs is_set_to_list_def] 1(1)
        by (rule is_set_to_sorted_listE)
      from IT' have 10: "S = set tsl'" "distinct tsl'" unfolding it_to_sorted_list_def by simp_all
      have "gen_Image tol1 mem2 emp3 ins3 T Y =
        fold (\<lambda> (a, b). if mem2 a Y then ins3 b else id) (tol1 T) emp3"
        unfolding gen_Image_def by rule
      also have "(\<dots>, fold (\<lambda> (a, b). if a \<in> X then Set.insert b else id) tsl' {}) \<in> \<langle>B\<rangle> Rs3"
        by parametricity
      also have "fold (\<lambda> (a, b). if a \<in> X then Set.insert b else id) tsl' M = S `` X \<union> M" for M
        unfolding 10(1) by (induct tsl' arbitrary: M) (auto split: prod.splits)
      also have "S `` X \<union> {} = S `` X" by simp
      finally show "(gen_Image tol1 mem2 emp3 ins3 T Y, S `` X) \<in> \<langle>B\<rangle> Rs3" by this
    qed

    lemma list_set_union_autoref[autoref_rules]:
      assumes "PRIO_TAG_OPTIMIZATION"
      assumes "SIDE_PRECOND_OPT (a' \<inter> b' = {})"
      assumes "(a, a') \<in> \<langle>R\<rangle> list_set_rel"
      assumes "(b, b') \<in> \<langle>R\<rangle> list_set_rel"
      shows "(a @ b,
        (OP union ::: \<langle>R\<rangle> list_set_rel \<rightarrow> \<langle>R\<rangle> list_set_rel \<rightarrow> \<langle>R\<rangle> list_set_rel) $ a' $ b') \<in>
        \<langle>R\<rangle> list_set_rel"
      using assms list_set_union unfolding autoref_tag_defs by blast
    lemma list_set_image_autoref[autoref_rules]:
      assumes "PRIO_TAG_OPTIMIZATION"
      assumes INJ: "SIDE_PRECOND_OPT (inj_on f s)"
      assumes "\<And> xi x. (xi, x) \<in> Ra \<Longrightarrow> x \<in> s \<Longrightarrow> (fi xi, f $ x) \<in> Rb"
      assumes LP: "(l,s)\<in>\<langle>Ra\<rangle>list_set_rel"
      shows "(map fi l,
        (OP image ::: (Ra \<rightarrow> Rb) \<rightarrow> \<langle>Ra\<rangle> list_set_rel \<rightarrow> \<langle>Rb\<rangle> list_set_rel) $ f $ s) \<in>
        \<langle>Rb\<rangle> list_set_rel"
    proof -
      from LP obtain l' where 1: "(l,l')\<in>\<langle>Ra\<rangle>list_rel" and L'S: "(l',s)\<in>br set distinct"
        unfolding list_set_rel_def by auto
      have 2: "s = set l'" using L'S unfolding in_br_conv by auto
      have "(map fi l, map f l')\<in>\<langle>Rb\<rangle>list_rel"
        using 1 L'S assms(3) unfolding 2 in_br_conv by induct auto
      also from INJ L'S have "(map f l',f`s)\<in>br set distinct"
        by (induct l' arbitrary: s) (auto simp: br_def dest: injD)
      finally (relcompI) show ?thesis unfolding autoref_tag_defs list_set_rel_def by this
    qed
    lemma list_set_UNION_autoref[autoref_rules]:
      assumes "PRIO_TAG_OPTIMIZATION"
      assumes "SIDE_PRECOND_OPT (\<forall> x \<in> S. \<forall> y \<in> S. x \<noteq> y \<longrightarrow> g x \<inter> g y = {})"
      assumes "(xs, S) \<in> \<langle>A\<rangle> list_set_rel" "(f, g) \<in> A \<rightarrow> \<langle>B\<rangle> list_set_rel"
      shows "(xs \<bind> f,
        (OP (\<lambda>A f. \<Union> (f ` A)) ::: \<langle>A\<rangle> list_set_rel \<rightarrow> (A \<rightarrow> \<langle>B\<rangle> list_set_rel) \<rightarrow> \<langle>B\<rangle> list_set_rel) $ S $ g) \<in>
        \<langle>B\<rangle> list_set_rel"
      using assms list_set_bind unfolding bind_UNION autoref_tag_defs by metis

    definition gen_equals where
      "gen_equals ball lu eq f g \<equiv>
        ball f (\<lambda> (k, v). rel_option eq (lu k g) (Some v)) \<and>
        ball g (\<lambda> (k, v). rel_option eq (lu k f) (Some v))"

    lemma gen_equals[autoref_rules]:
      assumes PRIO_TAG_GEN_ALGO
      assumes BALL: "GEN_OP ball op_map_ball (\<langle>Rk, Rv\<rangle> Rm \<rightarrow> (Rk \<times>\<^sub>r Rv \<rightarrow> bool_rel) \<rightarrow> bool_rel)"
      assumes LU: "GEN_OP lu op_map_lookup (Rk \<rightarrow> \<langle>Rk, Rv\<rangle> Rm \<rightarrow> \<langle>Rv\<rangle> option_rel)"
      assumes EQ: "GEN_OP eq HOL.eq (Rv \<rightarrow> Rv \<rightarrow> bool_rel)"
      shows "(gen_equals ball lu eq, HOL.eq) \<in> \<langle>Rk, Rv\<rangle> Rm \<rightarrow> \<langle>Rk, Rv\<rangle> Rm \<rightarrow> bool_rel"
    proof (intro fun_relI)
      note [unfolded autoref_tag_defs, param] = BALL LU EQ
      fix fi f gi g
      assume [param]: "(fi, f) \<in> \<langle>Rk, Rv\<rangle> Rm" "(gi, g) \<in> \<langle>Rk, Rv\<rangle> Rm"
      have "gen_equals ball lu eq fi gi \<longleftrightarrow> ball fi (\<lambda> (k, v). rel_option eq (lu k gi) (Some v)) \<and>
        ball gi (\<lambda> (k, v). rel_option eq (lu k fi) (Some v))"
        unfolding gen_equals_def by rule
      also have "ball fi (\<lambda> (k, v). rel_option eq (lu k gi) (Some v)) \<longleftrightarrow>
        op_map_ball f (\<lambda> (k, v). rel_option HOL.eq (op_map_lookup k g) (Some v))"
        by (rule IdD) (parametricity)
      also have "ball gi (\<lambda> (k, v). rel_option eq (lu k fi) (Some v)) \<longleftrightarrow>
        op_map_ball g (\<lambda> (k, v). rel_option HOL.eq (op_map_lookup k f) (Some v))"
        by (rule IdD) (parametricity)
      also have "op_map_ball f (\<lambda> (k, v). rel_option HOL.eq (op_map_lookup k g) (Some v)) \<and>
        op_map_ball g (\<lambda> (k, v). rel_option HOL.eq (op_map_lookup k f) (Some v)) \<longleftrightarrow>
        (\<forall> a b. f a = Some b \<longleftrightarrow> g a = Some b)"
        unfolding op_map_ball_def map_to_set_def option.rel_eq op_map_lookup_def by auto
      also have "(\<forall> a b. f a = Some b \<longleftrightarrow> g a = Some b) \<longleftrightarrow> f = g" using option.exhaust ext by metis
      finally show "(gen_equals ball lu eq fi gi, f = g) \<in> bool_rel" by simp
    qed

    (* TODO: why don't we just SPEC a list and then use map_of \<circ> enumerate, all of this
      could be done right in the implementation so we don't need a generic algorithm *)
    (* TODO: generic algorithms should really be generic, this is sort of specialized,
      replace with do { xs \<leftarrow> op_set_to_list S; RETURN (map_of (xs || [0 ..< length xs])) } *)
    definition op_set_enumerate :: "'a set \<Rightarrow> ('a \<rightharpoonup> nat) nres" where
      "op_set_enumerate S \<equiv> SPEC (\<lambda> f. dom f = S \<and> inj_on f S)"

    lemma [autoref_itype]: "op_set_enumerate ::\<^sub>i \<langle>A\<rangle>\<^sub>i i_set \<rightarrow>\<^sub>i \<langle>\<langle>A, i_nat\<rangle>\<^sub>i i_map\<rangle>\<^sub>i i_nres" by simp
    lemma [autoref_hom]: "CONSTRAINT op_set_enumerate (\<langle>A\<rangle> Rs \<rightarrow> \<langle>\<langle>A, nat_rel\<rangle> Rm\<rangle> nres_rel)" by simp

    definition gen_enumerate where
      "gen_enumerate tol upd emp S \<equiv> snd (fold (\<lambda> x (k, m). (Suc k, upd x k m)) (tol S) (0, emp))"

    lemma gen_enumerate[autoref_rules_raw]:
      assumes PRIO_TAG_GEN_ALGO
      assumes to_list: "SIDE_GEN_ALGO (is_set_to_list A Rs tol)"
      assumes empty: "GEN_OP emp op_map_empty (\<langle>A, nat_rel\<rangle> Rm)"
      assumes update: "GEN_OP upd op_map_update (A \<rightarrow> nat_rel \<rightarrow> \<langle>A, nat_rel\<rangle> Rm \<rightarrow> \<langle>A, nat_rel\<rangle> Rm)"
      shows "(\<lambda> S. RETURN (gen_enumerate tol upd emp S), op_set_enumerate) \<in>
        \<langle>A\<rangle> Rs \<rightarrow> \<langle>\<langle>A, nat_rel\<rangle> Rm\<rangle> nres_rel"
    proof
      note [unfolded autoref_tag_defs, param] = empty update
      fix T S
      assume 1: "(T, S) \<in> \<langle>A\<rangle> Rs"
      obtain tsl' where
        [param]: "(tol T, tsl') \<in> \<langle>A\<rangle>list_rel"
        and IT': "RETURN tsl' \<le> it_to_sorted_list (\<lambda>_ _. True) S"
        using to_list[unfolded autoref_tag_defs is_set_to_list_def] 1
        by (rule is_set_to_sorted_listE)
      from IT' have 10: "S = set tsl'" "distinct tsl'" unfolding it_to_sorted_list_def by simp_all
      have 2: "dom (snd (fold (\<lambda> x (k, m). (Suc k, m (x \<mapsto> k))) tsl' (k, m))) = dom m \<union> set tsl'"
        for k m by (induct tsl' arbitrary: k m) (auto)
      have 3: "inj_on (snd (fold (\<lambda> x (k, m). (Suc k, m (x \<mapsto> k))) tsl' (0, Map.empty))) (set tsl')"
        using 10(2) by (auto intro!: inj_onI simp: fold_map_of)
          (metis diff_zero distinct_Ex1 distinct_upt length_upt map_of_zip_nth option.simps(1))
      let ?f = "RETURN (snd (fold (\<lambda> x (k, m). (Suc k, op_map_update x k m)) tsl' (0, op_map_empty)))"
      have "(RETURN (gen_enumerate tol upd emp T), ?f) \<in> \<langle>\<langle>A, nat_rel\<rangle> Rm\<rangle> nres_rel"
        unfolding gen_enumerate_def by parametricity
      also have "(?f, op_set_enumerate S) \<in> \<langle>Id\<rangle> nres_rel"
        unfolding op_set_enumerate_def using 2 3 10 by refine_vcg auto
      finally show "(RETURN (gen_enumerate tol upd emp T), op_set_enumerate S) \<in>
        \<langle>\<langle>A, nat_rel\<rangle> Rm\<rangle> nres_rel" unfolding nres_rel_comp by simp
    qed

    lemma gen_enumerate_it_to_list[refine_transfer_post_simp]:
      "gen_enumerate (it_to_list it) =
       (\<lambda> upd emp S. snd (foldli (it_to_list it S) (\<lambda> _. True)
      (\<lambda> x s. case s of (k, m) \<Rightarrow> (Suc k, upd x k m)) (0, emp)))"
      unfolding gen_enumerate_def
      unfolding foldl_conv_fold[symmetric]
      unfolding foldli_foldl[symmetric]
      by rule

    definition gen_build where
      "gen_build tol upd emp f X \<equiv> fold (\<lambda> x. upd x (f x)) (tol X) emp"

    lemma gen_build[autoref_rules]:
      assumes PRIO_TAG_GEN_ALGO
      assumes to_list: "SIDE_GEN_ALGO (is_set_to_list A Rs tol)"
      assumes empty: "GEN_OP emp op_map_empty (\<langle>A, B\<rangle> Rm)"
      assumes update: "GEN_OP upd op_map_update (A \<rightarrow> B \<rightarrow> \<langle>A, B\<rangle> Rm \<rightarrow> \<langle>A, B\<rangle> Rm)"
      shows "(\<lambda> f X. gen_build tol upd emp f X, \<lambda> f X. (Some \<circ> f) |` X) \<in>
        (A \<rightarrow> B) \<rightarrow> \<langle>A\<rangle> Rs \<rightarrow> \<langle>A, B\<rangle> Rm"
    proof (intro fun_relI)
      note [unfolded autoref_tag_defs, param] = empty update
      fix f g T S
      assume 1[param]: "(g, f) \<in> A \<rightarrow> B" "(T, S) \<in> \<langle>A\<rangle> Rs"
      obtain tsl' where
        [param]: "(tol T, tsl') \<in> \<langle>A\<rangle>list_rel"
        and IT': "RETURN tsl' \<le> it_to_sorted_list (\<lambda>_ _. True) S"
        using to_list[unfolded autoref_tag_defs is_set_to_list_def] 1(2)
        by (rule is_set_to_sorted_listE)
      from IT' have 10: "S = set tsl'" "distinct tsl'" unfolding it_to_sorted_list_def by simp_all
      have "gen_build tol upd emp g T = fold (\<lambda> x. upd x (g x)) (tol T) emp"
        unfolding gen_build_def by rule
      also have "(\<dots>, fold (\<lambda> x. op_map_update x (f x)) tsl' op_map_empty) \<in> \<langle>A, B\<rangle> Rm"
        by parametricity
      also have "fold (\<lambda> x. op_map_update x (f x)) tsl' m = m ++ (Some \<circ> f) |` S" for m
        unfolding 10 op_map_update_def
        by (induct tsl' arbitrary: m rule: rev_induct) (auto simp add: restrict_map_insert)
      also have "op_map_empty ++ (Some \<circ> f) |` S = (Some \<circ> f) |` S" by simp
      finally show "(gen_build tol upd emp g T, (Some \<circ> f) |` S) \<in> \<langle>A, B\<rangle> Rm" by this
    qed

    definition "to_list it s \<equiv> it s top Cons Nil"

    lemma map2set_to_list:
      assumes "GEN_ALGO_tag (is_map_to_list Rk unit_rel R it)"
      shows "is_set_to_list Rk (map2set_rel R) (to_list (map_iterator_dom \<circ> (foldli \<circ> it)))"
    unfolding is_set_to_list_def is_set_to_sorted_list_def
    proof safe
      fix f g
      assume 1: "(f, g) \<in> \<langle>Rk\<rangle> map2set_rel R"
      obtain xs where 2: "(it_to_list (map_iterator_dom \<circ> (foldli \<circ> it)) f, xs) \<in> \<langle>Rk\<rangle> list_rel"
        "RETURN xs \<le> it_to_sorted_list (\<lambda> _ _. True) g"
        using map2set_to_list[OF assms] 1
        unfolding is_set_to_list_def is_set_to_sorted_list_def
        by auto
      have 3: "map_iterator_dom (foldli xs) top (#) a =
        rev (map_iterator_dom (foldli xs) (\<lambda> _. True) (\<lambda> x l. l @ [x]) (rev a))"
          for xs :: "('k \<times> unit) list" and a
          unfolding map_iterator_dom_def set_iterator_image_def set_iterator_image_filter_def
          by (induct xs arbitrary: a) (auto)
      show "\<exists> xs. (to_list (map_iterator_dom \<circ> (foldli \<circ> it)) f, xs) \<in> \<langle>Rk\<rangle> list_rel \<and>
        RETURN xs \<le> it_to_sorted_list (\<lambda> _ _. True) g"
      proof (intro exI conjI)
        have "to_list (map_iterator_dom \<circ> (foldli \<circ> it)) f =
          rev (it_to_list (map_iterator_dom \<circ> (foldli \<circ> it)) f)"
          unfolding to_list_def it_to_list_def by (simp add: 3)
        also have "(rev (it_to_list (map_iterator_dom \<circ> (foldli \<circ> it)) f), rev xs) \<in> \<langle>Rk\<rangle> list_rel"
          using 2(1) by parametricity
        finally show "(to_list (map_iterator_dom \<circ> (foldli \<circ> it)) f, rev xs) \<in> \<langle>Rk\<rangle> list_rel" by this
        show "RETURN (rev xs) \<le> it_to_sorted_list (\<lambda> _ _. True) g"
          using 2(2) unfolding it_to_sorted_list_def by auto
      qed
    qed

    lemma CAST_to_list[autoref_rules_raw]:
      assumes PRIO_TAG_GEN_ALGO
      assumes "SIDE_GEN_ALGO (is_set_to_list A Rs tol)"
      shows "(tol, CAST) \<in> \<langle>A\<rangle> Rs \<rightarrow> \<langle>A\<rangle> list_set_rel"
      using assms(2) unfolding autoref_tag_defs is_set_to_list_def
      by (auto simp: it_to_sorted_list_def list_set_rel_def in_br_conv elim!: is_set_to_sorted_listE)

    (* TODO: do we really need stronger versions of all these small lemmata? *)
    lemma param_foldli:
      assumes "(xs, ys) \<in> \<langle>Ra\<rangle> list_rel"
      assumes "(c, d) \<in> Rs \<rightarrow> bool_rel"
      assumes "\<And> x y. (x, y) \<in> Ra \<Longrightarrow> x \<in> set xs \<Longrightarrow> y \<in> set ys \<Longrightarrow> (f x, g y) \<in> Rs \<rightarrow> Rs"
      assumes "(a, b) \<in> Rs"
      shows "(foldli xs c f a, foldli ys d g b) \<in> Rs"
    using assms
    proof (induct arbitrary: a b)
      case 1
      then show ?case by simp
    next
      case (2 x y xs ys)
      show ?case
      proof (cases "c a")
        case True
        have 10: "(c a, d b) \<in> bool_rel" using 2 by parametricity
        have 20: "d b" using 10 True by auto
        have 30: "(foldli xs c f (f x a), foldli ys d g (g y b)) \<in> Rs"
          by (auto intro!: 2 2(5)[THEN fun_relD])
        show ?thesis using True 20 30 by simp
      next
        case False
        have 10: "(c a, d b) \<in> bool_rel" using 2 by parametricity
        have 20: "\<not> d b" using 10 False by auto
        show ?thesis unfolding foldli.simps using False 20 2 by simp
      qed
    qed
    lemma det_fold_sorted_set:
      assumes 1: "det_fold_set ordR c' f' \<sigma>' result"
      assumes 2: "is_set_to_sorted_list ordR Rk Rs tsl"
      assumes SREF[param]: "(s,s')\<in>\<langle>Rk\<rangle>Rs"
      assumes [param]:  "(c,c')\<in>R\<sigma>\<rightarrow>Id"
      assumes [param]: "\<And> x y. (x, y) \<in> Rk \<Longrightarrow> y \<in> s' \<Longrightarrow> (f x,f' y)\<in>R\<sigma> \<rightarrow> R\<sigma>"
      assumes [param]: "(\<sigma>,\<sigma>')\<in>R\<sigma>"
      shows "(foldli (tsl s) c f \<sigma>, result s') \<in> R\<sigma>"
    proof -
      obtain tsl' where
        n[param]: "(tsl s,tsl') \<in> \<langle>Rk\<rangle>list_rel"
        and IT: "RETURN tsl' \<le> it_to_sorted_list ordR s'"
        using 2 SREF
        by (rule is_set_to_sorted_listE)
      from IT have suen: "s' = set tsl'"
        unfolding it_to_sorted_list_def by simp_all
      have "(foldli (tsl s) c f \<sigma>, foldli tsl' c' f' \<sigma>') \<in> R\<sigma>"
        using assms(4, 5, 6) n unfolding suen
        using param_foldli[OF n assms(4)] assms by simp
      also have "foldli tsl' c' f' \<sigma>' = result s'"
        using 1 IT
        unfolding det_fold_set_def it_to_sorted_list_def
        by simp
      finally show ?thesis .
    qed
    lemma det_fold_set:
      assumes "det_fold_set (\<lambda>_ _. True) c' f' \<sigma>' result"
      assumes "is_set_to_list Rk Rs tsl"
      assumes "(s,s')\<in>\<langle>Rk\<rangle>Rs"
      assumes "(c,c')\<in>R\<sigma>\<rightarrow>Id"
      assumes "\<And> x y. (x, y) \<in> Rk \<Longrightarrow> y \<in> s' \<Longrightarrow> (f x, f' y)\<in>R\<sigma> \<rightarrow> R\<sigma>"
      assumes "(\<sigma>,\<sigma>')\<in>R\<sigma>"
      shows "(foldli (tsl s) c f \<sigma>, result s') \<in> R\<sigma>"
      using assms unfolding is_set_to_list_def by (rule det_fold_sorted_set)
    lemma gen_image[autoref_rules_raw]:
      assumes PRIO_TAG_GEN_ALGO
      assumes IT: "SIDE_GEN_ALGO (is_set_to_list Rk Rs1 it1)"
      assumes INS: "GEN_OP ins2 Set.insert (Rk'\<rightarrow>\<langle>Rk'\<rangle>Rs2\<rightarrow>\<langle>Rk'\<rangle>Rs2)"
      assumes EMPTY: "GEN_OP empty2 {} (\<langle>Rk'\<rangle>Rs2)"
      assumes "\<And> xi x. (xi, x) \<in> Rk \<Longrightarrow> x \<in> s \<Longrightarrow> (fi xi, f $ x) \<in> Rk'"
      assumes "(l, s) \<in> \<langle>Rk\<rangle>Rs1"
      shows "(gen_image (\<lambda> x. foldli (it1 x)) empty2 ins2 fi l,
        (OP image ::: (Rk\<rightarrow>Rk') \<rightarrow> (\<langle>Rk\<rangle>Rs1) \<rightarrow> (\<langle>Rk'\<rangle>Rs2)) $ f $ s) \<in> (\<langle>Rk'\<rangle>Rs2)"
    proof -
      note [unfolded autoref_tag_defs, param] = INS EMPTY
      note 1 = det_fold_set[OF foldli_image IT[unfolded autoref_tag_defs]]
      show ?thesis using assms 1 unfolding gen_image_def autoref_tag_defs by parametricity
    qed

  end

end
