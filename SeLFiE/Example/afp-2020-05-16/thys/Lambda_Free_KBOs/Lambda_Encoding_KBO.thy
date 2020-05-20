(*  Title:       Properties of Lambda-Free KBO on the Lambda Encoding
    Author:      Jasmin Blanchette <j.c.blanchette at vu.nl>, 2019
    Maintainer:  Jasmin Blanchette <j.c.blanchette at vu.nl>
*)

section \<open>Properties of Lambda-Free KBO on the Lambda Encoding\<close>

theory Lambda_Encoding_KBO
imports Lambda_Free_RPOs.Lambda_Encoding Lambda_Free_KBO_Basic
begin

text \<open>
This theory explores the properties of the \<open>\<lambda>\<close>-free KBO on the proposed encoding of \<open>\<lambda>\<close>-expressions.
\<close>

locale kbo_lambda_encoding = kbo_basic _ _ _ _ "\<lambda>_ :: 'v. UNIV :: 's set" + lambda_encoding lam
  for lam :: 's +
  assumes
    gt_db_db: "j > i \<Longrightarrow> db j >\<^sub>s db i" and
    wt_db_db: "wt_sym (db j) = wt_sym (db i)"
begin

notation gt (infix ">\<^sub>t" 50)
notation gt_hd (infix ">\<^sub>h\<^sub>d" 50)

abbreviation ge :: "('s, 'v) tm \<Rightarrow> ('s, 'v) tm \<Rightarrow> bool" (infix "\<ge>\<^sub>t" 50) where
  "t \<ge>\<^sub>t s \<equiv> t >\<^sub>t s \<or> t = s"

lemma wary_raw_db_subst: "wary_subst (raw_db_subst i x)"
  unfolding wary_subst_def by (simp add: arity_def)

lemma wt_subst_db: "wt (subst_db i x s) = wt (subst (raw_db_subst j x) s)"
  by (induct s arbitrary: i j)
    (clarsimp simp: raw_db_subst_def wt_db_db split: hd.splits,
      metis lambda_encoding.subst_db.simps(2) subst.simps(2) wt.simps(2))

lemma subst_db_Suc_ge: "subst_db (Suc i) x s \<ge>\<^sub>t subst_db i x s"
proof (induct s arbitrary: i)
  case (Hd x)
  then show ?case
    by (auto intro: gt_diff simp: wt_db_db gt_db_db gt_sym_imp_hd)
next
  case (App s1 s2)
  show ?case
    by (simp, safe)
      (metis (full_types) App.hyps(1) App.hyps(2) gt_compat_arg gt_compat_fun gt_trans)+
qed

lemma gt_subst_db: "t >\<^sub>t s \<Longrightarrow> subst_db i x t >\<^sub>t subst_db i x s"
proof (simp only: atomize_imp,
    rule measure_induct_rule[of "\<lambda>(t, s, i). {#size t, size s#}"
        "\<lambda>(t, s, i). t >\<^sub>t s \<longrightarrow> subst_db i x t >\<^sub>t subst_db i x s" "(t, s, i)",
      simplified prod.case],
    simp only: split_paired_all prod.case atomize_imp[symmetric] atomize_all[symmetric])
  fix t s :: "('s, 'v) tm" and i :: nat
  assume
    ih: "\<And>ta sa i. {#size ta, size sa#} < {#size t, size s#} \<Longrightarrow> ta >\<^sub>t sa \<Longrightarrow>
      subst_db i x ta >\<^sub>t subst_db i x sa" and
    t_gt_s: "t >\<^sub>t s"

  let ?\<rho> = "subst_db i x"

  show "?\<rho> t >\<^sub>t ?\<rho> s"
  proof (cases "wt (?\<rho> t) = wt (?\<rho> s)")
    case wt_\<rho>t_ne_\<rho>s: False

    have vars_s: "vars_mset t \<supseteq># vars_mset s"
      using gt.cases t_gt_s by blast
    hence vars_\<rho>s: "vars_mset (?\<rho> t) \<supseteq># vars_mset (?\<rho> s)"
      by (simp add: var_mset_subst_db_subseteq)

    have wt_t_ge_s: "wt t \<ge> wt s"
      by (metis dual_order.strict_implies_order eq_imp_le gt.cases t_gt_s)

    have "wt (?\<rho> t) > wt (?\<rho> s)"
      using wt_\<rho>t_ne_\<rho>s unfolding wt_subst_db
      by (metis (full_types) gt.simps gt_subst t_gt_s wary_raw_db_subst wt_subst_db)
    thus ?thesis
      by (rule gt_wt[OF vars_\<rho>s])
  next
    case wt_\<rho>t_eq_\<rho>s: True
    show ?thesis
      using t_gt_s
    proof cases
      case gt_wt
      hence False
        using wt_\<rho>t_eq_\<rho>s
        by (metis add_less_le_mono kbo_std.extra_wt_subseteq nat_less_le wary_raw_db_subst wt_subst
            wt_subst_db)
      thus ?thesis
        by sat
    next
      case _: gt_diff
      note vars_s = this(1) and hd_t_gt_hd_s = this(3)
      have vars_\<rho>s: "vars_mset (?\<rho> t) \<supseteq># vars_mset (?\<rho> s)"
        by (simp add: var_mset_subst_db_subseteq vars_s)
      term gt_hd
      have "head (?\<rho> t) >\<^sub>h\<^sub>d head (?\<rho> s)"
        by (smt Set.set_insert gt_hd_def hd_t_gt_hd_s head_subst_db insert_subset wary_raw_db_subst
            wary_subst_ground_heads)
      thus ?thesis
        by (rule gt_diff[OF vars_\<rho>s wt_\<rho>t_eq_\<rho>s])
    next
      case _: gt_same
      note vars_s = this(1) and hd_s_eq_hd_t = this(3) and extf = this(4)

      have vars_\<rho>s: "vars_mset (?\<rho> t) \<supseteq># vars_mset (?\<rho> s)"
        by (simp add: var_mset_subst_db_subseteq vars_s)
      have hd_\<rho>t: "head (?\<rho> t) = head (?\<rho> s)"
        by (simp add: hd_s_eq_hd_t head_subst_db)

      {
        fix f
        assume f_in_grs: "f \<in> ground_heads (head (?\<rho> s))"

        let ?\<rho>a = "subst_db (if head s = Sym lam then i + 1 else i) x"
        let ?S = "set (args t) \<union> set (args s)"

        have extf_args_s_t: "extf f (>\<^sub>t) (args t) (args s)"
          using extf f_in_grs hd_s_eq_hd_t head_subst_db wary_raw_db_subst wary_subst_ground_heads
          by (metis (no_types, lifting) insert_subset mk_disjoint_insert)
        have "extf f (>\<^sub>t) (map ?\<rho>a (args t)) (map ?\<rho>a (args s))"
        proof (rule extf_map[of ?S, OF _ _ _ _ _ _ extf_args_s_t])
          show "\<forall>x \<in> ?S. \<not> ?\<rho>a x >\<^sub>t ?\<rho>a x"
            using gt_irrefl by blast
        next
          show "\<forall>z \<in> ?S. \<forall>y \<in> ?S. \<forall>x \<in> ?S. ?\<rho>a z >\<^sub>t ?\<rho>a y \<longrightarrow> ?\<rho>a y >\<^sub>t ?\<rho>a x \<longrightarrow> ?\<rho>a z >\<^sub>t ?\<rho>a x"
            using gt_trans by blast
        next
          have sz_a: "\<forall>ta \<in> ?S. \<forall>sa \<in> ?S. {#size ta, size sa#} < {#size t, size s#}"
            by (fastforce intro: Max_lt_imp_lt_mset dest: size_in_args)
          show "\<forall>y \<in> ?S. \<forall>x \<in> ?S. y >\<^sub>t x \<longrightarrow> ?\<rho>a y >\<^sub>t ?\<rho>a x"
            using ih sz_a by blast
        qed auto
        hence "extf f (>\<^sub>t) (args (?\<rho> t)) (args (?\<rho> s))"
          by (simp add: args_subst_db hd_s_eq_hd_t)
      }
      hence "\<forall>f \<in> ground_heads (head (?\<rho> s)). extf f (>\<^sub>t) (args (?\<rho> t)) (args (?\<rho> s))"
        by blast
      thus ?thesis
        by (rule gt_same[OF vars_\<rho>s wt_\<rho>t_eq_\<rho>s hd_\<rho>t])
    qed
  qed
qed

end

end
