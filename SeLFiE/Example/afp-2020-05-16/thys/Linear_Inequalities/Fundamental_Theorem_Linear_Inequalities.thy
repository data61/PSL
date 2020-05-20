section \<open>The Fundamental Theorem of Linear Inequalities\<close>

text \<open>The theorem states that for a given set of vectors A and vector b, either
  b is in the cone of a linear independent subset of A, or
  there is a hyperplane that contains span(A,b)-1 linearly independent vectors of A
  that separates A from b. We prove this theorem and derive some consequences, e.g.,
  Caratheodory's theorem that b is the cone of A iff b is in the cone of a linear
  independent subset of A.\<close>

theory Fundamental_Theorem_Linear_Inequalities
  imports
    Cone
    Normal_Vector
    Dim_Span
begin

context gram_schmidt
begin

text \<open>The mentions equivances A-D are:
 \<^item> A: b is in the cone of vectors A,
 \<^item> B: b is in the cone of a subset of linear independent of vectors A,
 \<^item> C: there is no separating hyperplane of b and the vectors A,
      which contains dim many linear independent vectors of A
 \<^item> D: there is no separating hyperplane of b and the vectors A\<close>

lemma fundamental_theorem_of_linear_inequalities_A_imp_D:
  assumes A: "A \<subseteq> carrier_vec n"
    and fin: "finite A"
    and b: "b \<in> cone A"
  shows "\<nexists> c. c \<in> carrier_vec n \<and> (\<forall> a\<^sub>i \<in> A. c \<bullet> a\<^sub>i \<ge> 0) \<and> c \<bullet> b < 0"
proof
  assume "\<exists> c. c \<in> carrier_vec n \<and> (\<forall> a\<^sub>i \<in> A. c \<bullet> a\<^sub>i \<ge> 0) \<and> c \<bullet> b < 0"
  then obtain c where c: "c \<in> carrier_vec n"
    and ai: "\<And> ai. ai \<in> A \<Longrightarrow> c \<bullet> ai \<ge> 0"
    and cb: "c \<bullet> b < 0" by auto
  from b[unfolded cone_def nonneg_lincomb_def finite_cone_def]
  obtain l AA where bc: "b = lincomb l AA" and l: "l ` AA \<subseteq> {x. x \<ge> 0}" and AA: "AA \<subseteq> A" by auto
  from cone_carrier[OF A] b have b: "b \<in> carrier_vec n" by auto
  have "0 \<le> (\<Sum>ai\<in>AA. l ai * (c \<bullet> ai))"
    by (intro sum_nonneg mult_nonneg_nonneg, insert l ai AA, auto)
  also have "\<dots> = (\<Sum>ai\<in>AA. l ai * (ai \<bullet> c))"
    by (rule sum.cong, insert c A AA comm_scalar_prod, force+)
  also have "\<dots> = (\<Sum>ai\<in>AA. ((l ai \<cdot>\<^sub>v ai) \<bullet> c))"
    by (rule sum.cong, insert smult_scalar_prod_distrib c A AA, auto)
  also have "\<dots> = b \<bullet> c" unfolding bc lincomb_def
    by (subst finsum_scalar_prod_sum[symmetric], insert c A AA, auto)
  also have "\<dots> = c \<bullet> b" using comm_scalar_prod b c by auto
  also have "\<dots> < 0" by fact
  finally show False by simp
qed

text \<open>The difficult direction is that C implies B. To this end we follow the
  proof that at least one of B and the negation of C is satisfied.\<close>
context
  fixes a :: "nat \<Rightarrow> 'a vec"
    and b :: "'a vec"
    and m :: nat
  assumes a: "a ` {0 ..< m} \<subseteq> carrier_vec n"
    and inj_a: "inj_on a {0 ..< m}"
    and b: "b \<in> carrier_vec n"
    and full_span: "span (a ` {0 ..< m}) = carrier_vec n"
begin

private definition "goal = ((\<exists> I. I \<subseteq> {0 ..< m} \<and> card (a ` I) = n \<and> lin_indpt (a ` I) \<and> b \<in> finite_cone (a ` I))
  \<or> (\<exists> c I. I \<subseteq> {0 ..< m} \<and> c \<in> {normal_vector (a ` I), - normal_vector (a ` I)} \<and> Suc (card (a ` I)) = n
      \<and> lin_indpt (a ` I) \<and> (\<forall> i < m. c \<bullet> a i \<ge> 0) \<and> c \<bullet> b < 0))"

private lemma card_a_I[simp]: "I \<subseteq> {0 ..< m} \<Longrightarrow> card (a ` I) = card I"
  by (smt inj_a card_image inj_on_image_eq_iff subset_image_inj subset_refl subset_trans)

private lemma in_a_I[simp]: "I \<subseteq> {0 ..< m} \<Longrightarrow> i < m \<Longrightarrow> (a i \<in> a ` I) = (i \<in> I)"
  using inj_a
  by (meson atLeastLessThan_iff image_eqI inj_on_image_mem_iff_alt zero_le)

private definition "valid_I = { I. card I = n \<and> lin_indpt (a ` I) \<and> I \<subseteq> {0 ..< m}}"

private definition cond where "cond I I' l c h k \<equiv>
  b = lincomb l (a ` I) \<and>
  h \<in> I \<and> l (a h) < 0 \<and> (\<forall> h'. h' \<in> I \<longrightarrow> h' < h \<longrightarrow> l (a h') \<ge> 0) \<and>
  c \<in> carrier_vec n \<and> span (a ` (I - {h})) = { x. x \<in> carrier_vec n \<and> c \<bullet> x = 0} \<and> c \<bullet> b < 0 \<and>
  k < m \<and> c \<bullet> a k < 0 \<and> (\<forall> k'. k' < k \<longrightarrow> c \<bullet> a k' \<ge> 0) \<and>
  I' = insert k (I - {h})"

private definition "step_rel = Restr { (I'', I). \<exists> l c h k. cond I I'' l c h k } valid_I"

private lemma finite_step_rel: "finite step_rel"
proof (rule finite_subset)
  show "step_rel \<subseteq> (Pow {0 ..< m} \<times> Pow {0 ..< m})" unfolding step_rel_def valid_I_def by auto
qed auto

private lemma acyclic_imp_goal: "acyclic step_rel \<Longrightarrow> goal"
proof (rule ccontr)
  assume ngoal: "\<not> goal" (* then the algorithm will not terminate *)
  {
    fix I
    assume I: "I \<in> valid_I"
    hence Im: "I \<subseteq> {0..<m}" and
      lin: "lin_indpt (a ` I)" and
      cardI: "card I = n"
      by (auto simp: valid_I_def)
    let ?D = "(a ` I)"
    have finD: "finite ?D" using Im infinite_super by blast
    have carrD: "?D \<subseteq> carrier_vec n" using a Im by auto
    have cardD: "card ?D = n" using cardI Im by simp
    have spanD: "span ?D = carrier_vec n"
      by (intro span_carrier_lin_indpt_card_n lin cardD carrD)
    obtain lamb where b_is_lincomb: "b = lincomb lamb (a ` I)"
      using finite_in_span[OF fin carrD, of b] using spanD b carrD fin_dim lin by auto
    define h where "h = (LEAST h. h \<in> I \<and> lamb (a h) < 0)"
    have "\<exists> I'. (I', I) \<in> step_rel"
    proof (cases "\<forall>i\<in> I . lamb (a i) \<ge> 0")
      case cond1_T: True
      have goal unfolding goal_def
        by (intro disjI1 exI[of _ I] conjI lin cardI
            lincomb_in_finite_cone[OF b_is_lincomb finD _ carrD], insert cardI Im cond1_T, auto)
      with ngoal show ?thesis by auto
    next
      case cond1_F: False
      hence "\<exists> h. h \<in> I \<and> lamb (a h) < 0" by fastforce
      from LeastI_ex[OF this, folded h_def] have h: "h \<in> I" "lamb (a h) < 0" by auto
      from not_less_Least[of _ "\<lambda> h. h \<in> I \<and> lamb (a h) < 0", folded h_def]
      have h_least: "\<forall> k. k \<in> I \<longrightarrow> k < h \<longrightarrow> lamb (a k) \<ge> 0" by fastforce
      obtain I' where I'_def: "I' = I - {h}" by auto
      obtain c where c_def: "c = pos_norm_vec (a ` I') (a h)" by auto
      let ?D' = "a ` I'"
      have I'm: "I' \<subseteq> {0..<m}" using Im I'_def by auto
      have carrD': " ?D' \<subseteq> carrier_vec n" using a Im I'_def by auto
      have finD': "finite (?D')" using Im I'_def subset_eq_atLeast0_lessThan_finite by auto
      have D'subs: "?D' \<subseteq> ?D" using I'_def by auto
      have linD': "lin_indpt (?D')" using lin I'_def Im D'subs subset_li_is_li by auto
      have D'strictsubs: "?D = ?D' \<union> {a h}" using h I'_def by auto
      have h_nin_I: "h \<notin> I'" using h I'_def by auto
      have ah_nin_D': "a h \<notin> ?D'" using h inj_a Im h_nin_I by (subst in_a_I, auto simp: I'_def)
      have cardD': "Suc (card (?D')) = n " using cardD ah_nin_D' D'strictsubs finD' by simp
      have ah_carr: "a h \<in> carrier_vec n" using h a Im by auto
      note pnv = pos_norm_vec[OF carrD' finD' linD' cardD' c_def]
      have ah_nin_span: "a h \<notin> span ?D'"
        using D'strictsubs lin_dep_iff_in_span[OF carrD' linD' ah_carr ah_nin_D'] lin by auto
      have cah_ge_zero:"c \<bullet> a h > 0" and "c \<in> carrier_vec n"
        and cnorm: "span ?D' = {x \<in> carrier_vec n. x \<bullet> c = 0}"
        using ah_carr ah_nin_span pnv by auto
      have ccarr: "c \<in> carrier_vec n" by fact
      have "b \<bullet> c = lincomb lamb (a ` I) \<bullet> c" using b_is_lincomb by auto
      also have "\<dots> = (\<Sum>w\<in> ?D. lamb w * (w \<bullet> c))"
        using lincomb_scalar_prod_left[OF carrD, of c lamb] pos_norm_vec ccarr by blast
      also have "\<dots> = lamb (a h) * (a h \<bullet> c) + (\<Sum>w\<in> ?D'. lamb w * (w \<bullet> c))"
        using sum.insert[OF finD' ah_nin_D', of lamb] D'strictsubs ah_nin_D' finD' by auto
      also have "(\<Sum>w\<in> ?D'. lamb w * (w \<bullet> c)) = 0"
        apply (rule sum.neutral)
        using span_mem[OF carrD', unfolded cnorm] by simp
      also have "lamb (a h) * (a h \<bullet> c) + 0 < 0"
        using cah_ge_zero h(2) comm_scalar_prod[OF ah_carr ccarr]
        by (auto intro: mult_neg_pos)
      finally have cb_le_zero: "c \<bullet> b < 0" using comm_scalar_prod[OF b ccarr] by auto

      show ?thesis
      proof (cases "\<forall>i < m . c \<bullet> a i \<ge> 0")
        case cond2_T: True
        have goal
          unfolding goal_def
          by (intro disjI2 exI[of _ c] exI[of _ I'] conjI cb_le_zero linD' cond2_T cardD' I'm pnv(4))
        with ngoal show ?thesis by auto
      next
        case cond2_F: False
        define k where "k = (LEAST k. k < m \<and> c \<bullet> a k < 0)"
        let ?I'' = "insert k I'"
        show ?thesis unfolding step_rel_def
        proof (intro exI[of _ ?I''], standard, unfold mem_Collect_eq split, intro exI)
          from LeastI_ex[OF ]
          have "\<exists>k. k < m \<and> c \<bullet> a k < 0" using cond2_F by fastforce
          from LeastI_ex[OF this, folded k_def] have k: "k < m" "c \<bullet> a k < 0" by auto
          show "cond I ?I'' lamb c h k" unfolding cond_def I'_def[symmetric] cnorm
          proof(intro conjI cb_le_zero b_is_lincomb h ccarr h_least refl k)
            show "{x \<in> carrier_vec n. x \<bullet> c = 0} = {x \<in> carrier_vec n. c \<bullet> x = 0}"
              using comm_scalar_prod[OF ccarr] by auto
            from not_less_Least[of _ "\<lambda> k. k < m \<and> c \<bullet> a k < 0", folded k_def]
            have "\<forall>k' < k . k' > m \<or> c \<bullet> a k' \<ge> 0" using k(1) less_trans not_less by blast
            then show "\<forall>k' < k . c \<bullet> a k' \<ge> 0" using k(1) by auto
          qed

          have "?I'' \<in> valid_I" unfolding valid_I_def
          proof(standard, intro conjI)
            from k a have ak_carr: "a k \<in> carrier_vec n" by auto
            have ak_nin_span: "a k \<notin> span ?D'" using k(2) cnorm comm_scalar_prod[OF ak_carr ccarr] by auto
            hence ak_nin_D': "a k \<notin> ?D'" using span_mem[OF carrD'] by auto
            from lin_dep_iff_in_span[OF carrD' linD' ak_carr ak_nin_D']
            show "lin_indpt (a ` ?I'')" using ak_nin_span by auto
            show "?I'' \<subseteq> {0..<m}" using I'm k by auto
            show "card (insert k I') = n" using cardD' ak_nin_D' finD'
              by (metis \<open>insert k I' \<subseteq> {0..<m}\<close> card_a_I card_insert_disjoint image_insert)
          qed
          then show "(?I'', I) \<in> valid_I \<times> valid_I"  using I by auto

        qed
      qed
    qed
  } note step = this
  { (* create some valid initial set I *)
    from exists_lin_indpt_subset[OF a, unfolded full_span]
    obtain A where lin: "lin_indpt A" and span: "span A = carrier_vec n" and Am: "A \<subseteq> a ` {0 ..<m}" by auto
    from Am a have A: "A \<subseteq> carrier_vec n" by auto
    from lin span A have card: "card A = n"
      using basis_def dim_basis dim_is_n fin_dim_li_fin by auto
    from A Am obtain I where  A: "A = a ` I" and I: "I \<subseteq> {0 ..< m}" by (metis subset_imageE)
    have "I \<in> valid_I" using I card lin unfolding valid_I_def A by auto
    hence "\<exists> I. I \<in> valid_I" ..
  }
  note init = this
  have step_valid: "(I',I) \<in> step_rel \<Longrightarrow> I' \<in> valid_I" for I I' unfolding step_rel_def by auto
  have "\<not> (wf step_rel)"
  proof
    from init obtain I where I: "I \<in> valid_I" by auto
    assume "wf step_rel"
    from this[unfolded wf_eq_minimal, rule_format, OF I] step step_valid show False by blast
  qed
  with wf_iff_acyclic_if_finite[OF finite_step_rel]
  have "\<not> acyclic step_rel" by auto
  thus "acyclic step_rel \<Longrightarrow> False" by auto
qed

private lemma acyclic_step_rel: "acyclic step_rel"
proof (rule ccontr)
  assume "\<not> ?thesis"
  hence "\<not> acyclic (step_rel\<inverse>)" by auto

(* obtain cycle *)
  then obtain I where "(I, I) \<in> (step_rel^-1)^+" unfolding acyclic_def by blast
  from this[unfolded trancl_power]
  obtain len where "(I, I) \<in> (step_rel^-1) ^^ len" and len0: "len > 0" by blast
      (* obtain all intermediate I's *)
  from this[unfolded relpow_fun_conv] obtain Is where
    stepsIs: "\<And> i. i < len \<Longrightarrow> (Is (Suc i), Is i) \<in> step_rel"
    and IsI: "Is 0 = I" "Is len = I" by auto
  {
    fix i
    assume "i \<le> len" hence "i - 1 < len" using len0 by auto
    from stepsIs[unfolded step_rel_def, OF this]
    have "Is i \<in> valid_I" by (cases i, auto)
  } note Is_valid = this
  from stepsIs[unfolded step_rel_def]
  have "\<forall> i. \<exists> l c h k. i < len \<longrightarrow> cond (Is i) (Is (Suc i)) l c h k" by auto
      (* obtain all intermediate c's h's, l's, k's *)
  from choice[OF this] obtain ls where "\<forall> i. \<exists> c h k. i < len \<longrightarrow> cond (Is i) (Is (Suc i)) (ls i) c h k" by auto
  from choice[OF this] obtain cs where "\<forall> i. \<exists> h k. i < len \<longrightarrow> cond (Is i) (Is (Suc i)) (ls i) (cs i) h k" by auto
  from choice[OF this] obtain hs where "\<forall> i. \<exists> k. i < len \<longrightarrow> cond (Is i) (Is (Suc i)) (ls i) (cs i) (hs i) k" by auto
  from choice[OF this] obtain ks where
    cond: "\<And> i. i < len \<Longrightarrow> cond (Is i) (Is (Suc i)) (ls i) (cs i) (hs i) (ks i)" by auto
      (* finally derive contradiction *)
  let ?R = "{hs i | i. i < len}"
  define r where "r = Max ?R"
  from cond[OF len0] have "hs 0 \<in> I" using IsI unfolding cond_def by auto
  hence R0: "hs 0 \<in> ?R" using len0 by auto
  have finR: "finite ?R" by auto
  from Max_in[OF finR] R0
  have rR: "r \<in> ?R" unfolding r_def[symmetric] by auto
  then obtain p where rp: "r = hs p" and p: "p < len" by auto
  from Max_ge[OF finR, folded r_def]
  have rLarge: "i < len \<Longrightarrow> hs i \<le> r" for i by auto
  have exq: "\<exists>q. ks q = r \<and> q < len"
  proof (rule ccontr)
    assume neg: "\<not>?thesis"
    show False
    proof(cases "r \<in> I")
      case True
      have 1: "j\<in>{Suc p..len} \<Longrightarrow> r \<notin> Is j" for j
      proof(induction j rule: less_induct)
        case (less j)
        from less(2) have j_bounds: "j = Suc p \<or> j > Suc p" by auto
        from less(2) have j_len: "j \<le> len" by auto
        have pj_cond: "j = Suc p \<Longrightarrow> cond (Is p) (Is j) (ls p) (cs p) (hs p) (ks p)" using cond p by blast
        have r_neq_ksp: "r \<noteq> ks p" using p neg by auto
        have "j = Suc p \<Longrightarrow> Is j = insert (ks p) (Is p - {r})"
          using rp cond pj_cond cond_def[of "Is p" "Is j" _ _ r] by blast
        hence c1: "j = Suc p \<Longrightarrow> r \<notin> Is j" using r_neq_ksp by simp
        have IH: "\<And>t. t < j \<Longrightarrow> t \<in> {Suc p..len} \<Longrightarrow> r \<notin> Is t" by fact
        have r_neq_kspj: "j > Suc p \<and> j \<le> len \<Longrightarrow> r \<noteq> ks (j-1)" using j_len neg IH by auto
        have jsucj_cond: "j > Suc p \<and> j \<le> len \<Longrightarrow> Is j = insert (ks (j-1)) (Is (j-1) - {hs (j-1)})"
          using cond_def[of "Is (j-1)" "Is j"] cond
          by (metis (no_types, lifting) Suc_less_eq2 diff_Suc_1 le_simps(3))
        hence "j > Suc p \<and> j \<le> len \<Longrightarrow> r \<notin> insert (ks (j-1)) (Is (j-1))"
          using IH r_neq_kspj by auto
        hence "j > Suc p \<and> j \<le> len \<Longrightarrow> r \<notin> Is j" using jsucj_cond by simp
        then show ?case using j_bounds j_len c1 by blast
      qed
      then show ?thesis using neg IsI(2) True p by auto
    next
      case False
      have 2: "j\<in>{0..p} \<Longrightarrow> r \<notin> Is j" for j
      proof(induction j rule: less_induct)
        case(less j)
        from less(2) have j_bound: "j \<le> p" by auto
        have r_nin_Is0: "r \<notin> Is 0" using IsI(1) False by simp
        have IH: "\<And>t. t < j \<and> t \<in> {0..p} \<Longrightarrow> r \<notin> Is t" using less.IH by blast
        have j_neq_ksjpred: "j > 0 \<Longrightarrow> r \<noteq> ks (j -1)" using neg j_bound p by auto
        have Is_jpredj: "j > 0 \<Longrightarrow> Is j = insert (ks (j-1)) (Is (j-1) - {hs (j-1)})"
          using cond_def[of "Is (j-1)" "Is j" _ _ "hs (j-1)" "ks (j-1)"] cond
          by (metis (full_types) One_nat_def Suc_pred diff_le_self j_bound le_less_trans p)
        have "j > 0 \<Longrightarrow> r \<notin> insert (ks (j-1)) (Is (j-1))"
          using j_neq_ksjpred IH j_bound by fastforce
        hence "j > 0 \<Longrightarrow> r \<notin> Is j" using Is_jpredj by blast
        then show ?case using j_bound r_nin_Is0 by blast
      qed
      have 3: "r \<in> Is p" using rp cond cond_def p by blast
      then show ?thesis using 2 3 by auto
    qed
  qed
  then obtain q where q1: "ks q = r" and q_len: "q < len" by blast

  {
    fix t i1 i2
    assume "i1 < len" "i2 < len" "t < m"
    assume "t\<in> Is i1" "t\<notin> Is i2"
    have "\<exists>j < len. t = hs j"
    proof (rule ccontr)
      assume "\<not> ?thesis"
      hence hst: "\<And> j. j < len \<Longrightarrow> hs j \<noteq> t" by auto
      have main: "t \<notin> Is (i + k) \<Longrightarrow> i + k \<le> len \<Longrightarrow> t \<notin> Is k" for i k
      proof (induct i)
        case (Suc i)
        hence i: "i + k < len" by auto
        from cond[OF this, unfolded cond_def]
        have "Is (Suc i + k) = insert (ks (i + k)) (Is (i + k) - {hs (i + k)})" by auto
        from Suc(2)[unfolded this] hst[OF i] have "t \<notin> Is (i + k)" by auto
        from Suc(1)[OF this] i show ?case by auto
      qed auto
      from main[of i2 0] \<open>i2 < len\<close> \<open>t \<notin> Is i2\<close> have "t \<notin> Is 0" by auto
      with IsI have "t \<notin> Is len" by auto
      with main[of "len - i1" i1] \<open>i1 < len\<close> have "t \<notin> Is i1" by auto
      with \<open>t \<in> Is i1\<close> show False by blast
    qed
  } note innotin = this

  {
    fix i
    assume i: "i \<in> {Suc r..<m}"
    {
      assume i_in_Isp: "i \<in> Is p"
      have "i \<in> Is q"
      proof (rule ccontr)
        have i_range: "i < m" using i by simp
        assume "\<not> ?thesis"
        then have ex: "\<exists>j < len. i = hs j"
          using innotin[OF p q_len i_range i_in_Isp] by simp
        then obtain j where j_hs: "i = hs j" by blast
        have "i>r" using i by simp
        then show False using j_hs p rLarge ex by force
      qed
    }
    hence "(i \<in> Is p) \<Longrightarrow> (i \<in> Is q)" by blast
  } note bla = this
  have blin: "b = lincomb (ls p) (a ` (Is p))" using cond_def p cond by blast
  have carrDp: "(a ` (Is p)) \<subseteq> carrier_vec n " using Is_valid valid_I_def a p
    by (smt image_subset_iff less_imp_le_nat mem_Collect_eq subsetD)
  have carrcq: "cs q \<in> carrier_vec n" using cond cond_def q_len by simp
  have ineq1: "(cs q) \<bullet> b < 0" using cond_def q_len cond by blast
  let ?Isp_lt_r = "{x \<in> Is p . x < r}"
  let ?Isp_gt_r = "{x \<in> Is p . x > r}"
  have Is_disj: "?Isp_lt_r \<inter> ?Isp_gt_r = {}" using Is_valid by auto
  have "?Isp_lt_r \<subseteq> Is p" by simp
  hence Isp_lt_0m: "?Isp_lt_r \<subseteq> {0..<m}" using valid_I_def Is_valid p less_imp_le_nat by blast
  have "?Isp_gt_r \<subseteq> Is p" by simp
  hence Isp_gt_0m: "?Isp_gt_r \<subseteq> {0..<m}" using valid_I_def Is_valid p less_imp_le_nat by blast
  let ?Dp_lt = "a ` ?Isp_lt_r"
  let ?Dp_ge = "a ` ?Isp_gt_r"
  {
    fix A B
    assume Asub: "A \<subseteq> {0..<m} \<union> {0..<Suc r}"
    assume Bsub: "B \<subseteq> {0..<m} \<union> {0..<Suc r}"
    assume ABinters: "A \<inter> B = {}"
    have "r \<in> Is p" using rp p cond unfolding cond_def by simp
    hence r_lt_m: "r < m" using p Is_valid[of p] unfolding valid_I_def by auto
    hence 1: "A \<subseteq> {0..<m}" using Asub by auto
    have 2: "B \<subseteq> {0..<m}" using r_lt_m Bsub by auto
    have "a ` A \<inter> a ` B = {}"
      using inj_on_image_Int[OF inj_a 1 2] ABinters by auto
  } note inja = this

  have "(Is p \<inter> {0..<r}) \<inter> (Is p \<inter> {r}) = {}" by auto
  hence "a ` (Is p \<inter> {0..<r} \<union> Is p \<inter> {r}) = a ` (Is p \<inter> {0..<r}) \<union> a ` (Is p \<inter> {r})"
    using inj_a by auto
  moreover have "Is p \<inter> {0..<r} \<union> Is p \<inter> {r} \<subseteq> {0..<m} \<union> {0..<Suc r}" by auto
  moreover have "Is p \<inter> {Suc r..<m} \<subseteq> {0..<m} \<union> {0..<Suc r}" by auto
  moreover have "(Is p \<inter> {0..<r} \<union> Is p \<inter> {r}) \<inter> (Is p \<inter> {Suc r..<m}) = {}" by auto
  ultimately have one: "(a ` (Is p \<inter> {0..<r}) \<union> a ` (Is p \<inter> {r})) \<inter> a ` (Is p \<inter> {Suc r..<m}) = {}"
    using inja[of "Is p \<inter> {0..<r} \<union> Is p \<inter> {r}" "Is p \<inter> {Suc r..<m}"] by auto
  have split: "Is p = Is p \<inter> {0..<r} \<union> Is p \<inter> {r} \<union> Is p \<inter> {Suc r ..< m}"
    using rp p Is_valid[of p] unfolding valid_I_def by auto
  have gtr: "(\<Sum>w \<in> (a ` (Is p \<inter> {Suc r ..< m})). ((ls p) w) * (cs q \<bullet> w)) = 0"
  proof (rule sum.neutral, clarify)
    fix w
    assume w1: "w \<in> Is p" and w2: "w\<in>{Suc r..<m}"
    have w_in_q:  "w \<in> Is q" using bla[OF w2] w1 by blast
    moreover have "hs q \<le> r" using rR rLarge using q_len by blast
    ultimately have "w \<noteq> hs q" using w2 by simp
    hence "w \<in> Is q -{hs q}" using w1 w_in_q by auto
    moreover have "Is q - {hs q} \<subseteq> {0..<m}"
      using q_len Is_valid[of q] unfolding valid_I_def by auto
    ultimately have "a w \<in> span ( a ` (Is q - {hs q}))" using a by (intro span_mem, auto)
    moreover have "cs q \<in> carrier_vec n \<and> span (a ` (Is q - {hs q})) =
      { x. x \<in> carrier_vec n \<and> cs q \<bullet> x = 0}"
      using cond[of q] q_len unfolding cond_def by auto
    ultimately have "(cs q) \<bullet> (a w) = 0" using a w2 by simp
    then show "ls p (a w) * (cs q \<bullet> a w) = 0" by simp
  qed
  note pp = cond[OF p, unfolded cond_def rp[symmetric]]
  note qq = cond[OF q_len, unfolded cond_def q1]
  have "(cs q) \<bullet> b = (cs q) \<bullet> lincomb (ls p) (a ` (Is p))" using blin by auto
  also have "\<dots> = (\<Sum>w \<in> (a ` (Is p)). ((ls p) w) * (cs q \<bullet> w))"
    by (subst lincomb_scalar_prod_right[OF carrDp carrcq], simp)
  also have "\<dots> = (\<Sum>w \<in> (a ` (Is p \<inter> {0..<r}) \<union> a ` (Is p \<inter> {r}) \<union> a ` (Is p \<inter> {Suc r..<m})).
     ((ls p) w) * (cs q \<bullet> w))"
    by (subst (1) split, rule sum.cong, auto)
  also have "\<dots> = (\<Sum>w \<in> (a ` (Is p \<inter> {0..<r})). ((ls p) w) * (cs q \<bullet> w))
       + (\<Sum>w \<in> (a ` (Is p \<inter> {r})). ((ls p) w) * (cs q \<bullet> w))
      + (\<Sum>w \<in> (a ` (Is p \<inter> {Suc r ..< m})). ((ls p) w) * (cs q \<bullet> w))"
    apply (subst sum.union_disjoint[OF _ _ one])
      apply (force+)[2]
    apply (subst sum.union_disjoint)
       apply (force+)[2]
     apply (rule inja)
    by auto
  also have "\<dots> = (\<Sum>w \<in> (a ` (Is p \<inter> {0..<r})). ((ls p) w) * (cs q \<bullet> w))
       + (\<Sum>w \<in> (a ` (Is p \<inter> {r})). ((ls p) w) * (cs q \<bullet> w))"
    using sum.neutral gtr by simp
  also have "\<dots> > 0 + 0"
  proof (intro add_le_less_mono sum_nonneg mult_nonneg_nonneg)
    {
      fix x
      assume x: "x \<in> a ` (Is p \<inter> {0..<r})"
      show "0 \<le> ls p x" using pp x by auto
      show "0 \<le> cs q \<bullet> x" using qq x by auto
    }
    have "r \<in> Is p" using pp by blast
    hence "a ` (Is p \<inter> {r}) = {a r}" by auto
    hence id: "(\<Sum>w\<in>a ` (Is p \<inter> {r}). ls p w * (cs q \<bullet> w)) = ls p (a r) * (cs q \<bullet> a r)"
      by simp
    show "0 < (\<Sum>w\<in>a ` (Is p \<inter> {r}). ls p w * (cs q \<bullet> w))"
      unfolding id
    proof (rule mult_neg_neg)
      show "ls p (a r) < 0" using pp by auto
      show "cs q \<bullet> a r < 0" using qq by auto
    qed
  qed
  finally have "cs q \<bullet> b > 0" by simp
  moreover have "cs q \<bullet> b < 0" using qq by blast
  ultimately show False by auto
qed

lemma fundamental_theorem_neg_C_or_B_in_context:
  assumes W: "W = a ` {0 ..< m}"
  shows "(\<exists> U. U \<subseteq> W \<and> card U = n \<and> lin_indpt U \<and> b \<in> finite_cone U) \<or>
    (\<exists>c U. U \<subseteq> W \<and>
           c \<in> {normal_vector U, - normal_vector U} \<and>
           Suc (card U) = n \<and> lin_indpt U \<and> (\<forall>w \<in> W. 0 \<le> c \<bullet> w) \<and> c \<bullet> b < 0)"
  using acyclic_imp_goal[unfolded goal_def, OF acyclic_step_rel]
proof
  assume "\<exists>I. I\<subseteq>{0..<m} \<and> card (a ` I) = n \<and> lin_indpt (a ` I) \<and> b \<in> finite_cone (a ` I)"
  thus ?thesis unfolding W by (intro disjI1, blast)
next
  assume "\<exists>c I. I \<subseteq> {0..<m} \<and>
          c \<in> {normal_vector (a ` I), - normal_vector (a ` I)} \<and>
          Suc (card (a ` I)) = n \<and> lin_indpt (a ` I) \<and> (\<forall>i<m. 0 \<le> c \<bullet> a i) \<and> c \<bullet> b < 0"
  then obtain c I where "I \<subseteq> {0..<m} \<and>
          c \<in> {normal_vector (a ` I), - normal_vector (a ` I)} \<and>
          Suc (card (a ` I)) = n \<and> lin_indpt (a ` I) \<and> (\<forall>i<m. 0 \<le> c \<bullet> a i) \<and> c \<bullet> b < 0" by auto
  thus ?thesis unfolding W
    by (intro disjI2 exI[of _ c] exI[of _ "a ` I"], auto)
qed

end

lemma fundamental_theorem_of_linear_inequalities_C_imp_B_full_dim:
  assumes A: "A \<subseteq> carrier_vec n"
    and fin: "finite A"
    and span: "span A = carrier_vec n" (* this condition was a wlog in the proof *)
    and b: "b \<in> carrier_vec n"
    and C: "\<nexists> c B. B \<subseteq> A \<and> c \<in> {normal_vector B, - normal_vector B} \<and> Suc (card B) = n
      \<and> lin_indpt B \<and> (\<forall> a\<^sub>i \<in> A. c \<bullet> a\<^sub>i \<ge> 0) \<and> c \<bullet> b < 0"
  shows "\<exists> B \<subseteq> A. lin_indpt B \<and> card B = n \<and> b \<in> finite_cone B"
proof -
  from finite_distinct_list[OF fin] obtain as where Aas: "A = set as" and dist: "distinct as" by auto
  define m where "m = length as"
  define a where "a = (\<lambda> i. as ! i)"
  have inj: "inj_on a {0..< (m :: nat)}"
    and id: "A = a ` {0..<m}"
    unfolding m_def a_def Aas using inj_on_nth[OF dist] unfolding set_conv_nth
    by auto
  from fundamental_theorem_neg_C_or_B_in_context[OF _ inj b, folded id, OF A span refl] C
  show ?thesis by blast
qed


lemma fundamental_theorem_of_linear_inequalities_full_dim: fixes A :: "'a vec set"
  defines "HyperN \<equiv> {b. b \<in> carrier_vec n \<and> (\<nexists> B c. B \<subseteq> A \<and> c \<in> {normal_vector B, - normal_vector B}
      \<and> Suc (card B) = n \<and> lin_indpt B \<and> (\<forall> a\<^sub>i \<in> A. c \<bullet> a\<^sub>i \<ge> 0) \<and> c \<bullet> b < 0)}"
  defines "HyperA \<equiv> {b. b \<in> carrier_vec n \<and> (\<nexists> c. c \<in> carrier_vec n \<and> (\<forall> a\<^sub>i \<in> A. c \<bullet> a\<^sub>i \<ge> 0) \<and> c \<bullet> b < 0)}"
  defines "lin_indpt_cone \<equiv> \<Union> { finite_cone B | B. B \<subseteq> A \<and> card B = n \<and> lin_indpt B}"
  assumes A: "A \<subseteq> carrier_vec n"
    and fin: "finite A"
    and span: "span A = carrier_vec n"
  shows
    "cone A = lin_indpt_cone"
    "cone A = HyperN"
    "cone A = HyperA"
proof -
  have "lin_indpt_cone \<subseteq> cone A" unfolding lin_indpt_cone_def cone_def using fin finite_cone_mono A
    by auto
  moreover have "cone A \<subseteq> HyperA"
  proof
    fix c
    assume cA: "c \<in> cone A"
    from fundamental_theorem_of_linear_inequalities_A_imp_D[OF A fin this] cone_carrier[OF A] cA
    show "c \<in> HyperA" unfolding HyperA_def by auto
  qed
  moreover have "HyperA \<subseteq> HyperN"
  proof
    fix c
    assume "c \<in> HyperA"
    hence False: "\<And> v. v \<in> carrier_vec n \<Longrightarrow> (\<forall>a\<^sub>i\<in>A. 0 \<le> v \<bullet> a\<^sub>i) \<Longrightarrow> v \<bullet> c < 0 \<Longrightarrow> False"
      and c: "c \<in> carrier_vec n" unfolding HyperA_def by auto
    show "c \<in> HyperN"
      unfolding HyperN_def
    proof (standard, intro conjI c notI, clarify, goal_cases)
      case (1 W nv)
      with A fin have fin: "finite W" and W: "W \<subseteq> carrier_vec n" by (auto intro: finite_subset)
      show ?case using False[of nv] 1 normal_vector[OF fin _ _ W] by auto
    qed
  qed
  moreover have "HyperN \<subseteq> lin_indpt_cone"
  proof
    fix b
    assume "b \<in> HyperN"
    from this[unfolded HyperN_def]
      fundamental_theorem_of_linear_inequalities_C_imp_B_full_dim[OF A fin span, of b]
    show "b \<in> lin_indpt_cone" unfolding lin_indpt_cone_def by auto
  qed
  ultimately show
    "cone A = lin_indpt_cone"
    "cone A = HyperN"
    "cone A = HyperA"
    by auto
qed

lemma fundamental_theorem_of_linear_inequalities_C_imp_B:
  assumes A: "A \<subseteq> carrier_vec n"
    and fin: "finite A"
    and b: "b \<in> carrier_vec n"
    and C: "\<nexists> c A'. c \<in> carrier_vec n
      \<and> A' \<subseteq> A \<and> Suc (card A') = dim_span (insert b A)
      \<and> (\<forall> a \<in> A'. c \<bullet> a = 0)
      \<and> lin_indpt A' \<and> (\<forall> a\<^sub>i \<in> A. c \<bullet> a\<^sub>i \<ge> 0) \<and> c \<bullet> b < 0"
  shows "\<exists> B \<subseteq> A. lin_indpt B \<and> card B = dim_span A \<and> b \<in> finite_cone B"
proof -
  from exists_lin_indpt_sublist[OF A] obtain A' where
    lin: "lin_indpt_list A'" and span: "span (set A') = span A" and A'A: "set A' \<subseteq> A" by auto
  hence linA': "lin_indpt (set A')" unfolding lin_indpt_list_def by auto
  from A'A A have A': "set A' \<subseteq> carrier_vec n" by auto
  have dim_spanA: "dim_span A = card (set A')"
    by (rule sym, rule same_span_imp_card_eq_dim_span[OF A' A span linA'])
  show ?thesis
  proof (cases "b \<in> span A")
    case False
    with span have "b \<notin> span (set A')" by auto
    with lin have linAb: "lin_indpt_list (A' @ [b])" unfolding lin_indpt_list_def
      using lin_dep_iff_in_span[OF A' _ b] span_mem[OF A', of b] b by auto
    interpret gso: gram_schmidt_fs_lin_indpt n "A' @ [b]"
      by (standard, insert linAb[unfolded lin_indpt_list_def], auto)
    let ?m = "length A'"
    define c where "c = - gso.gso ?m"
    have c: "c \<in> carrier_vec n" using gso.gso_carrier[of ?m] unfolding c_def by auto
    from gso.gso_times_self_is_norm[of ?m]
    have "b \<bullet> gso.gso ?m = sq_norm (gso.gso ?m)" unfolding c_def using b c by auto
    also have "\<dots> > 0" using gso.sq_norm_pos[of ?m] by auto
    finally have cb: "c \<bullet> b < 0" using b c comm_scalar_prod[OF b c] unfolding c_def by auto
    {
      fix a
      assume "a \<in> A"
      hence "a \<in> span (set A')" unfolding span using span_mem[OF A] by auto
      from finite_in_span[OF _ A' this]
      obtain l where "a = lincomb l (set A')" by auto
      hence "c \<bullet> a = c \<bullet> lincomb l (set A')" by simp
      also have "\<dots> = 0"
        by (subst lincomb_scalar_prod_right[OF A' c], rule sum.neutral, insert A', unfold set_conv_nth,
            insert gso.gso_scalar_zero[of ?m] c, auto simp: c_def nth_append )
      finally have "c \<bullet> a = 0" .
    } note cA = this
    have "\<exists> c A'. c \<in> carrier_vec n \<and> A' \<subseteq> A \<and> Suc (card A') = dim_span (insert b A)
      \<and> (\<forall> a \<in> A'. c \<bullet> a = 0) \<and> lin_indpt A' \<and> (\<forall> a\<^sub>i \<in> A. c \<bullet> a\<^sub>i \<ge> 0) \<and> c \<bullet> b < 0"
    proof (intro exI[of _ c] exI[of _ "set A'"] conjI A'A linA' cb c)
      show "\<forall>a\<in>set A'. c \<bullet> a = 0" "\<forall>a\<^sub>i\<in>A. 0 \<le> c \<bullet> a\<^sub>i" using cA A'A by auto
      have "dim_span (insert b A) = Suc (dim_span A)"
        by (rule dim_span_insert[OF A b False])
      also have "\<dots> = Suc (card (set A'))" unfolding dim_spanA ..
      finally show "Suc (card (set A')) = dim_span (insert b A)" ..
    qed
    with C have False by blast
    thus ?thesis ..
  next
    case bspan: True
    define N where "N = normal_vectors A'"
    from normal_vectors[OF lin, folded N_def]
    have N: "set N \<subseteq> carrier_vec n" and
      orthA'N: "\<And> w nv. w \<in> set A' \<Longrightarrow> nv \<in> set N \<Longrightarrow> nv \<bullet> w = 0" and
      linAN: "lin_indpt_list (A' @ N)"  and
      lenAN: "length (A' @ N) = n" and
      disj: "set A' \<inter> set N = {}" by auto
    from linAN lenAN have full_span': "span (set (A' @ N)) = carrier_vec n"
      using lin_indpt_list_length_eq_n by blast
    hence full_span'': "span (set A' \<union> set N) = carrier_vec n" by auto
    from A N A' have AN: "A \<union> set N \<subseteq> carrier_vec n" and A'N: "set (A' @ N) \<subseteq> carrier_vec n" by auto
    hence "span (A \<union> set N) \<subseteq> carrier_vec n" by (simp add: span_is_subset2)
    with A'A span_is_monotone[of "set (A' @ N)" "A \<union> set N", unfolded full_span']
    have full_span: "span (A \<union> set N) = carrier_vec n" unfolding set_append by fast
    from fin have finAN: "finite (A \<union> set N)" by auto
    note fundamental = fundamental_theorem_of_linear_inequalities_full_dim[OF AN finAN full_span]
    show ?thesis
    proof (cases "b \<in> cone (A \<union> set N)")
      case True
      from this[unfolded fundamental(1)] obtain C where CAN: "C \<subseteq> A \<union> set N" and cardC: "card C = n"
        and linC: "lin_indpt C"
        and bC: "b \<in> finite_cone C" by auto
      have finC: "finite C" using finite_subset[OF CAN] fin by auto
      from CAN A N have C: "C \<subseteq> carrier_vec n" by auto
      from bC[unfolded finite_cone_def nonneg_lincomb_def] finC obtain c
        where bC: "b = lincomb c C" and nonneg: "\<And> b. b \<in> C \<Longrightarrow> c b \<ge> 0" by auto
      let ?C = "C - set N"
      show ?thesis
      proof (intro exI[of _ ?C] conjI)
        from subset_li_is_li[OF linC] show "lin_indpt ?C" by auto
        show CA: "?C \<subseteq> A" using CAN by auto
        have bc: "b = lincomb c (?C \<union> (C \<inter> set N))" unfolding bC
          by (rule arg_cong[of _ _ "lincomb _"], auto)
        have "b = lincomb c (?C - C \<inter> set N)"
        proof (rule orthogonal_cone(2)[OF A N fin full_span'' orthA'N refl span
              A'A linAN lenAN _ CA _ bc])
          show "\<forall>w\<in>set N. w \<bullet> b = 0"
            using ortho_span'[OF A' N _ bspan[folded span]] orthA'N by auto
        qed auto
        also have "?C - C \<inter> set N = ?C" by auto
        finally have "b = lincomb c ?C" .
        with nonneg have "nonneg_lincomb c ?C b" unfolding nonneg_lincomb_def by auto
        thus "b \<in> finite_cone ?C" unfolding finite_cone_def using finite_subset[OF CA fin] by auto
        have Cid: "C \<inter> set N \<union> ?C = C" by auto
        have "length A' + length N = n" by fact
        also have "\<dots> = card (C \<inter> set N \<union> ?C) " using Cid cardC by auto
        also have "\<dots> = card (C \<inter> set N) + card ?C"
          by (subst card_Un_disjoint, insert finC, auto)
        also have "\<dots> \<le> length N + card ?C"
          by (rule add_right_mono, rule order.trans, rule card_mono[OF finite_set[of N]],
              auto intro: card_length)
        also have "length A' = card (set A')" using lin[unfolded lin_indpt_list_def]
            distinct_card[of A'] by auto
        finally have le: "dim_span A \<le> card ?C" using dim_spanA by auto
        have CA: "?C \<subseteq> span A" using CA C in_own_span[OF A] by auto
        have linC: "lin_indpt ?C" using subset_li_is_li[OF linC] by auto
        show "card ?C = dim_span A"
          using card_le_dim_span[OF _ CA linC] le C by force
      qed
    next
      case False
      from False[unfolded fundamental(2)] b
      obtain C c where
        CAN: "C \<subseteq> A \<union> set N"  and
        cardC: "Suc (card C) = n"  and
        linC: "lin_indpt C" and
        contains: "(\<forall>a\<^sub>i\<in>A \<union> set N. 0 \<le> c \<bullet> a\<^sub>i)" and
        cb: "c \<bullet> b < 0" and
        nv: "c \<in> {normal_vector C, - normal_vector C}"
        by auto
      from CAN A N have C: "C \<subseteq> carrier_vec n" by auto
      from cardC have cardCn: "card C < n" by auto
      from finite_subset[OF CAN] fin have finC: "finite C" by auto
      let ?C = "C - set N"
      note nv' = normal_vector(1-4)[OF finC cardC linC C]
      from nv' nv have c: "c \<in> carrier_vec n" by auto
      have "\<exists> c A'. c \<in> carrier_vec n \<and> A' \<subseteq> A \<and> Suc (card A') = dim_span (insert b A)
          \<and> (\<forall> a \<in> A'. c \<bullet> a = 0) \<and> lin_indpt A' \<and> (\<forall> a\<^sub>i \<in> A. c \<bullet> a\<^sub>i \<ge> 0) \<and> c \<bullet> b < 0"
      proof (intro exI[of _ c] exI[of _ ?C] conjI cb c)
        show CA: "?C \<subseteq> A" using CAN by auto
        show "\<forall>a\<^sub>i\<in>A. 0 \<le> c \<bullet> a\<^sub>i" using contains by auto
        show lin': "lin_indpt ?C" using subset_li_is_li[OF linC] by auto
        show sC0: "\<forall>a\<in> ?C. c \<bullet> a = 0" using nv' nv C by auto
        have Cid: "C \<inter> set N \<union> ?C = C" by auto
        have "dim_span (set A') = card (set A')"
          by (rule sym, rule same_span_imp_card_eq_dim_span[OF A' A' refl linA'])
        also have "\<dots> = length A'"
          using lin[unfolded lin_indpt_list_def] distinct_card[of A'] by auto
        finally have dimA': "dim_span (set A') = length A'" .
        from bspan have "span (insert b A) = span A" using b A using already_in_span by auto
        from dim_span_cong[OF this[folded span]] dimA'
        have dimbA: "dim_span (insert b A) = length A'" by simp
        also have "\<dots> = Suc (card ?C)"
        proof (rule ccontr)
          assume neq: "length A' \<noteq> Suc (card ?C)"
          have "length A' + length N = n" by fact
          also have "\<dots> = Suc (card (C \<inter> set N \<union> ?C))" using Cid cardC by auto
          also have "\<dots> = Suc (card (C \<inter> set N) + card ?C)"
            by (subst card_Un_disjoint, insert finC, auto)
          finally have id: "length A' + length N = Suc (card (C \<inter> set N) + card ?C)" .
          have le1: "card (C \<inter> set N) \<le> length N"
            by (metis Int_lower2 List.finite_set card_length card_mono inf.absorb_iff2 le_inf_iff)
          from CA C A have CsA: "?C \<subseteq> span (set A')" unfolding span by (meson in_own_span order.trans)
          from card_le_dim_span[OF _ this lin'] C
          have le2: "card ?C \<le> length A'" unfolding dimA' by auto
          from id le1 le2 neq
          have id2: "card ?C = length A'" by linarith+
          from card_eq_dim_span_imp_same_span[OF A' CsA lin' id2[folded dimA']]
          have "span ?C = span A" unfolding span by auto
          with bspan have "b \<in> span ?C" by auto
          from orthocompl_span[OF _ _ c this] C sC0
          have "c \<bullet> b = 0" by auto
          with cb show False by simp
        qed
        finally show "Suc (card ?C) = dim_span (insert b A)" by simp
      qed
      with assms(4) have False by blast
      thus ?thesis ..
    qed
  qed
qed

lemma fundamental_theorem_of_linear_inequalities: fixes A :: "'a vec set"
  defines "HyperN \<equiv> {b. b \<in> carrier_vec n \<and> (\<nexists> c B. c \<in> carrier_vec n \<and> B \<subseteq> A
      \<and> Suc (card B) = dim_span (insert b A) \<and> lin_indpt B
      \<and> (\<forall> a \<in> B. c \<bullet> a = 0)
      \<and> (\<forall> a\<^sub>i \<in> A. c \<bullet> a\<^sub>i \<ge> 0) \<and> c \<bullet> b < 0)}"
  defines "HyperA \<equiv> {b. b \<in> carrier_vec n \<and> (\<nexists> c. c \<in> carrier_vec n \<and> (\<forall> a\<^sub>i \<in> A. c \<bullet> a\<^sub>i \<ge> 0) \<and> c \<bullet> b < 0)}"
  defines "lin_indpt_cone \<equiv> \<Union> { finite_cone B | B. B \<subseteq> A \<and> card B = dim_span A \<and> lin_indpt B}"
  assumes A: "A \<subseteq> carrier_vec n"
    and fin: "finite A"
  shows
    "cone A = lin_indpt_cone"
    "cone A = HyperN"
    "cone A = HyperA"
proof -
  have "lin_indpt_cone \<subseteq> cone A" 
    unfolding lin_indpt_cone_def cone_def using fin finite_cone_mono A by auto
  moreover have "cone A \<subseteq> HyperA"
    using fundamental_theorem_of_linear_inequalities_A_imp_D[OF A fin] cone_carrier[OF A]
    unfolding HyperA_def by blast
  moreover have "HyperA \<subseteq> HyperN" unfolding HyperA_def HyperN_def by blast
  moreover have "HyperN \<subseteq> lin_indpt_cone"
  proof
    fix b
    assume "b \<in> HyperN"
    from this[unfolded HyperN_def]
      fundamental_theorem_of_linear_inequalities_C_imp_B[OF A fin, of b]
    show "b \<in> lin_indpt_cone" unfolding lin_indpt_cone_def by blast
  qed
  ultimately show
    "cone A = lin_indpt_cone"
    "cone A = HyperN"
    "cone A = HyperA"
    by auto
qed

corollary Caratheodory_theorem: assumes A: "A \<subseteq> carrier_vec n"
  shows "cone A = \<Union> {finite_cone B |B. B \<subseteq> A \<and> lin_indpt B}" 
proof 
  show "\<Union> {finite_cone B |B. B \<subseteq> A \<and> lin_indpt B} \<subseteq> cone A" unfolding cone_def
    using fin[OF fin_dim _ subset_trans[OF _ A]] by auto
  {
    fix a
    assume "a \<in> cone A" 
    from this[unfolded cone_def] obtain B where 
      finB: "finite B" and BA: "B \<subseteq> A" and a: "a \<in> finite_cone B" by auto
    from BA A have B: "B \<subseteq> carrier_vec n" by auto
    hence "a \<in> cone B" using finB a by (simp add: cone_iff_finite_cone)
    with fundamental_theorem_of_linear_inequalities(1)[OF B finB]
    obtain C where CB: "C \<subseteq> B" and a: "a \<in> finite_cone C" and "lin_indpt C" by auto
    with BA have "a \<in> \<Union> {finite_cone B |B. B \<subseteq> A \<and> lin_indpt B}" by auto
  }
  thus "\<Union> {finite_cone B |B. B \<subseteq> A \<and> lin_indpt B} \<supseteq> cone A" by blast
qed
end
end