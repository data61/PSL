(*  Title:       The Graceful Recursive Path Order for Lambda-Free Higher-Order Terms
    Author:      Jasmin Blanchette <jasmin.blanchette at inria.fr>, 2016
    Author:      Uwe Waldmann <waldmann at mpi-inf.mpg.de>, 2016
    Author:      Daniel Wand <dwand at mpi-inf.mpg.de>, 2016
    Maintainer:  Jasmin Blanchette <jasmin.blanchette at inria.fr>
*)

section \<open>The Graceful Recursive Path Order for Lambda-Free Higher-Order Terms\<close>

theory Lambda_Free_RPO_Std
imports Lambda_Free_Term Extension_Orders
abbrevs ">t" = ">\<^sub>t"
  and "\<ge>t" = "\<ge>\<^sub>t"
begin

text \<open>
This theory defines the graceful recursive path order (RPO) for \<open>\<lambda>\<close>-free
higher-order terms.
\<close>


subsection \<open>Setup\<close>

locale rpo_basis = ground_heads "(>\<^sub>s)" arity_sym arity_var
    for
      gt_sym :: "'s \<Rightarrow> 's \<Rightarrow> bool" (infix ">\<^sub>s" 50) and
      arity_sym :: "'s \<Rightarrow> enat" and
      arity_var :: "'v \<Rightarrow> enat" +
  fixes
    extf :: "'s \<Rightarrow> (('s, 'v) tm \<Rightarrow> ('s, 'v) tm \<Rightarrow> bool) \<Rightarrow> ('s, 'v) tm list \<Rightarrow> ('s, 'v) tm list \<Rightarrow> bool"
  assumes
    extf_ext_trans_before_irrefl: "ext_trans_before_irrefl (extf f)" and
    extf_ext_compat_cons: "ext_compat_cons (extf f)" and
    extf_ext_compat_list: "ext_compat_list (extf f)"
begin

lemma extf_ext_trans: "ext_trans (extf f)"
  by (rule ext_trans_before_irrefl.axioms(1)[OF extf_ext_trans_before_irrefl])

lemma extf_ext: "ext (extf f)"
  by (rule ext_trans.axioms(1)[OF extf_ext_trans])

lemmas extf_mono_strong = ext.mono_strong[OF extf_ext]
lemmas extf_mono = ext.mono[OF extf_ext, mono]
lemmas extf_map = ext.map[OF extf_ext]
lemmas extf_trans = ext_trans.trans[OF extf_ext_trans]
lemmas extf_irrefl_from_trans =
  ext_trans_before_irrefl.irrefl_from_trans[OF extf_ext_trans_before_irrefl]
lemmas extf_compat_append_left = ext_compat_cons.compat_append_left[OF extf_ext_compat_cons]
lemmas extf_compat_list = ext_compat_list.compat_list[OF extf_ext_compat_list]

definition chkvar :: "('s, 'v) tm \<Rightarrow> ('s, 'v) tm \<Rightarrow> bool" where
  [simp]: "chkvar t s \<longleftrightarrow> vars_hd (head s) \<subseteq> vars t"

end

locale rpo = rpo_basis _ _ arity_sym arity_var
  for
    arity_sym :: "'s \<Rightarrow> enat" and
    arity_var :: "'v \<Rightarrow> enat"
begin


subsection \<open>Inductive Definitions\<close>

definition
  chksubs :: "(('s, 'v) tm \<Rightarrow> ('s, 'v) tm \<Rightarrow> bool) \<Rightarrow> ('s, 'v) tm \<Rightarrow> ('s, 'v) tm \<Rightarrow> bool"
where
  [simp]: "chksubs gt t s \<longleftrightarrow> (case s of App s1 s2 \<Rightarrow> gt t s1 \<and> gt t s2 | _ \<Rightarrow> True)"

lemma chksubs_mono[mono]: "gt \<le> gt' \<Longrightarrow> chksubs gt \<le> chksubs gt'"
  by (auto simp: tm.case_eq_if) force+

inductive gt :: "('s, 'v) tm \<Rightarrow> ('s, 'v) tm \<Rightarrow> bool" (infix ">\<^sub>t" 50) where
  gt_sub: "is_App t \<Longrightarrow> (fun t >\<^sub>t s \<or> fun t = s) \<or> (arg t >\<^sub>t s \<or> arg t = s) \<Longrightarrow> t >\<^sub>t s"
| gt_diff: "head t >\<^sub>h\<^sub>d head s \<Longrightarrow> chkvar t s \<Longrightarrow> chksubs (>\<^sub>t) t s \<Longrightarrow> t >\<^sub>t s"
| gt_same: "head t = head s \<Longrightarrow> chksubs (>\<^sub>t) t s \<Longrightarrow>
    (\<forall>f \<in> ground_heads (head t). extf f (>\<^sub>t) (args t) (args s)) \<Longrightarrow> t >\<^sub>t s"

abbreviation ge :: "('s, 'v) tm \<Rightarrow> ('s, 'v) tm \<Rightarrow> bool" (infix "\<ge>\<^sub>t" 50) where
  "t \<ge>\<^sub>t s \<equiv> t >\<^sub>t s \<or> t = s"

inductive gt_sub :: "('s, 'v) tm \<Rightarrow> ('s, 'v) tm \<Rightarrow> bool" where
  gt_subI: "is_App t \<Longrightarrow> fun t \<ge>\<^sub>t s \<or> arg t \<ge>\<^sub>t s \<Longrightarrow> gt_sub t s"

inductive gt_diff :: "('s, 'v) tm \<Rightarrow> ('s, 'v) tm \<Rightarrow> bool" where
  gt_diffI: "head t >\<^sub>h\<^sub>d head s \<Longrightarrow> chkvar t s \<Longrightarrow> chksubs (>\<^sub>t) t s \<Longrightarrow> gt_diff t s"

inductive gt_same :: "('s, 'v) tm \<Rightarrow> ('s, 'v) tm \<Rightarrow> bool" where
  gt_sameI: "head t = head s \<Longrightarrow> chksubs (>\<^sub>t) t s \<Longrightarrow>
    (\<forall>f \<in> ground_heads (head t). extf f (>\<^sub>t) (args t) (args s)) \<Longrightarrow> gt_same t s"

lemma gt_iff_sub_diff_same: "t >\<^sub>t s \<longleftrightarrow> gt_sub t s \<or> gt_diff t s \<or> gt_same t s"
  by (subst gt.simps) (auto simp: gt_sub.simps gt_diff.simps gt_same.simps)


subsection \<open>Transitivity\<close>

lemma gt_fun_imp: "fun t >\<^sub>t s \<Longrightarrow> t >\<^sub>t s"
  by (cases t) (auto intro: gt_sub)

lemma gt_arg_imp: "arg t >\<^sub>t s \<Longrightarrow> t >\<^sub>t s"
  by (cases t) (auto intro: gt_sub)

lemma gt_imp_vars: "t >\<^sub>t s \<Longrightarrow> vars t \<supseteq> vars s"
proof (simp only: atomize_imp,
    rule measure_induct_rule[of "\<lambda>(t, s). size t + size s"
      "\<lambda>(t, s). t >\<^sub>t s \<longrightarrow> vars t \<supseteq> vars s" "(t, s)", simplified prod.case],
    simp only: split_paired_all prod.case atomize_imp[symmetric])
  fix t s
  assume
    ih: "\<And>ta sa. size ta + size sa < size t + size s \<Longrightarrow> ta >\<^sub>t sa \<Longrightarrow> vars ta \<supseteq> vars sa" and
    t_gt_s: "t >\<^sub>t s"
  show "vars t \<supseteq> vars s"
    using t_gt_s
  proof cases
    case gt_sub
    thus ?thesis
      using ih[of "fun t" s] ih[of "arg t" s]
      by (meson add_less_cancel_right subsetD size_arg_lt size_fun_lt subsetI tm.set_sel(5,6))
  next
    case gt_diff
    show ?thesis
    proof (cases s)
      case Hd
      thus ?thesis
        using gt_diff(2) by (auto elim: hd.set_cases(2))
    next
      case (App s1 s2)
      thus ?thesis
        using gt_diff(3) ih[of t s1] ih[of t s2] by simp
    qed
  next
    case gt_same
    show ?thesis
    proof (cases s)
      case Hd
      thus ?thesis
        using gt_same(1) vars_head_subseteq by fastforce
    next
      case (App s1 s2)
      thus ?thesis
        using gt_same(2) ih[of t s1] ih[of t s2] by simp
    qed
  qed
qed

theorem gt_trans: "u >\<^sub>t t \<Longrightarrow> t >\<^sub>t s \<Longrightarrow> u >\<^sub>t s"
proof (simp only: atomize_imp,
    rule measure_induct_rule[of "\<lambda>(u, t, s). {#size u, size t, size s#}"
        "\<lambda>(u, t, s). u >\<^sub>t t \<longrightarrow> t >\<^sub>t s \<longrightarrow> u >\<^sub>t s" "(u, t, s)",
      simplified prod.case],
    simp only: split_paired_all prod.case atomize_imp[symmetric])
  fix u t s
  assume
    ih: "\<And>ua ta sa. {#size ua, size ta, size sa#} < {#size u, size t, size s#} \<Longrightarrow>
      ua >\<^sub>t ta \<Longrightarrow> ta >\<^sub>t sa \<Longrightarrow> ua >\<^sub>t sa" and
    u_gt_t: "u >\<^sub>t t" and t_gt_s: "t >\<^sub>t s"

  have chkvar: "chkvar u s"
    by clarsimp (meson u_gt_t t_gt_s gt_imp_vars hd.set_sel(2) vars_head_subseteq subsetCE)

  have chk_u_s_if: "chksubs (>\<^sub>t) u s" if chk_t_s: "chksubs (>\<^sub>t) t s"
  proof (cases s)
    case (App s1 s2)
    thus ?thesis
      using chk_t_s by (auto intro: ih[of _ _ s1, OF _ u_gt_t] ih[of _ _ s2, OF _ u_gt_t])
  qed auto

  have
    fun_u_lt_etc: "is_App u \<Longrightarrow> {#size (fun u), size t, size s#} < {#size u, size t, size s#}" and
    arg_u_lt_etc: "is_App u \<Longrightarrow> {#size (arg u), size t, size s#} < {#size u, size t, size s#}"
    by (simp_all add: size_fun_lt size_arg_lt)

  have u_gt_s_if_ui: "is_App u \<Longrightarrow> fun u \<ge>\<^sub>t t \<or> arg u \<ge>\<^sub>t t \<Longrightarrow> u >\<^sub>t s"
    using ih[of "fun u" t s, OF fun_u_lt_etc] ih[of "arg u" t s, OF arg_u_lt_etc] gt_arg_imp
      gt_fun_imp t_gt_s by blast

  show "u >\<^sub>t s"
    using t_gt_s
  proof cases
    case gt_sub_t_s: gt_sub

    have u_gt_s_if_chk_u_t: ?thesis if chk_u_t: "chksubs (>\<^sub>t) u t"
      using gt_sub_t_s(1)
    proof (cases t)
      case t: (App t1 t2)
      show ?thesis
        using ih[of u t1 s] ih[of u t2 s] gt_sub_t_s(2) chk_u_t unfolding t by auto
    qed auto

    show ?thesis
      using u_gt_t by cases (auto intro: u_gt_s_if_ui u_gt_s_if_chk_u_t)
  next
    case gt_diff_t_s: gt_diff
    show ?thesis
      using u_gt_t
    proof cases
      case gt_diff_u_t: gt_diff
      have "head u >\<^sub>h\<^sub>d head s"
        using gt_diff_u_t(1) gt_diff_t_s(1) by (auto intro: gt_hd_trans)
      thus ?thesis
        by (rule gt_diff[OF _ chkvar chk_u_s_if[OF gt_diff_t_s(3)]])
    next
      case gt_same_u_t: gt_same
      have "head u >\<^sub>h\<^sub>d head s"
        using gt_diff_t_s(1) gt_same_u_t(1) by auto
      thus ?thesis
        by (rule gt_diff[OF _ chkvar chk_u_s_if[OF gt_diff_t_s(3)]])
    qed (auto intro: u_gt_s_if_ui)
  next
    case gt_same_t_s: gt_same
    show ?thesis
      using u_gt_t
    proof cases
      case gt_diff_u_t: gt_diff
      have "head u >\<^sub>h\<^sub>d head s"
        using gt_diff_u_t(1) gt_same_t_s(1) by simp
      thus ?thesis
        by (rule gt_diff[OF _ chkvar chk_u_s_if[OF gt_same_t_s(2)]])
    next
      case gt_same_u_t: gt_same
      have hd_u_s: "head u = head s"
        using gt_same_u_t(1) gt_same_t_s(1) by simp

      let ?S = "set (args u) \<union> set (args t) \<union> set (args s)"

      have gt_trans_args: "\<forall>ua \<in> ?S. \<forall>ta \<in> ?S. \<forall>sa \<in> ?S. ua >\<^sub>t ta \<longrightarrow> ta >\<^sub>t sa \<longrightarrow> ua >\<^sub>t sa"
      proof clarify
        fix sa ta ua
        assume
          ua_in: "ua \<in> ?S" and ta_in: "ta \<in> ?S" and sa_in: "sa \<in> ?S" and
          ua_gt_ta: "ua >\<^sub>t ta" and ta_gt_sa: "ta >\<^sub>t sa"
        show "ua >\<^sub>t sa"
          by (auto intro!: ih[OF Max_lt_imp_lt_mset ua_gt_ta ta_gt_sa])
            (meson ua_in ta_in sa_in Un_iff max.strict_coboundedI1 max.strict_coboundedI2
               size_in_args)+
      qed

      have "\<forall>f \<in> ground_heads (head u). extf f (>\<^sub>t) (args u) (args s)"
      proof (clarify, rule extf_trans[OF _ _ _ gt_trans_args])
        fix f
        assume f_in_grounds: "f \<in> ground_heads (head u)"
        show "extf f (>\<^sub>t) (args u) (args t)"
          using f_in_grounds gt_same_u_t(3) by blast
        show "extf f (>\<^sub>t) (args t) (args s)"
          using f_in_grounds gt_same_t_s(3) unfolding gt_same_u_t(1) by blast
      qed auto
      thus ?thesis
        by (rule gt_same[OF hd_u_s chk_u_s_if[OF gt_same_t_s(2)]])
    qed (auto intro: u_gt_s_if_ui)
  qed
qed


subsection \<open>Irreflexivity\<close>

theorem gt_irrefl: "\<not> s >\<^sub>t s"
proof (standard, induct s rule: measure_induct_rule[of size])
  case (less s)
  note ih = this(1) and s_gt_s = this(2)

  show False
    using s_gt_s
  proof cases
    case _: gt_sub
    note is_app = this(1) and si_ge_s = this(2)
    have s_gt_fun_s: "s >\<^sub>t fun s" and s_gt_arg_s: "s >\<^sub>t arg s"
      using is_app by (simp_all add: gt_sub)

    have "fun s >\<^sub>t s \<or> arg s >\<^sub>t s"
      using si_ge_s is_app s_gt_arg_s s_gt_fun_s by auto
    moreover
    {
      assume fun_s_gt_s: "fun s >\<^sub>t s"
      have "fun s >\<^sub>t fun s"
        by (rule gt_trans[OF fun_s_gt_s s_gt_fun_s])
      hence False
        using ih[of "fun s"] is_app size_fun_lt by blast
    }
    moreover
    {
      assume arg_s_gt_s: "arg s >\<^sub>t s"
      have "arg s >\<^sub>t arg s"
        by (rule gt_trans[OF arg_s_gt_s s_gt_arg_s])
      hence False
        using ih[of "arg s"] is_app size_arg_lt by blast
    }
    ultimately show False
      by sat
  next
    case gt_diff
    thus False
      by (cases "head s") (auto simp: gt_hd_irrefl)
  next
    case gt_same
    note in_grounds = this(3)

    obtain si where si_in_args: "si \<in> set (args s)" and si_gt_si: "si >\<^sub>t si"
      using in_grounds
      by (metis (full_types) all_not_in_conv extf_irrefl_from_trans ground_heads_nonempty gt_trans)
    have "size si < size s"
      by (rule size_in_args[OF si_in_args])
    thus False
      by (rule ih[OF _ si_gt_si])
  qed
qed

lemma gt_antisym: "t >\<^sub>t s \<Longrightarrow> \<not> s >\<^sub>t t"
  using gt_irrefl gt_trans by blast


subsection \<open>Subterm Property\<close>

lemma
  gt_sub_fun: "App s t >\<^sub>t s" and
  gt_sub_arg: "App s t >\<^sub>t t"
  by (auto intro: gt_sub)

theorem gt_proper_sub: "proper_sub s t \<Longrightarrow> t >\<^sub>t s"
  by (induct t) (auto intro: gt_sub_fun gt_sub_arg gt_trans)


subsection \<open>Compatibility with Functions\<close>

lemma gt_compat_fun:
  assumes t'_gt_t: "t' >\<^sub>t t"
  shows "App s t' >\<^sub>t App s t"
proof -
  have t'_ne_t: "t' \<noteq> t"
    using gt_antisym t'_gt_t by blast
  have extf_args_single: "\<forall>f \<in> ground_heads (head s). extf f (>\<^sub>t) (args s @ [t']) (args s @ [t])"
    by (simp add: extf_compat_list t'_gt_t t'_ne_t)
  show ?thesis
    by (rule gt_same) (auto simp: gt_sub gt_sub_fun t'_gt_t intro!: extf_args_single)
qed

theorem gt_compat_fun_strong:
  assumes t'_gt_t: "t' >\<^sub>t t"
  shows "apps s (t' # us) >\<^sub>t apps s (t # us)"
proof (induct us rule: rev_induct)
  case Nil
  show ?case
    using t'_gt_t by (auto intro!: gt_compat_fun)
next
  case (snoc u us)
  note ih = snoc

  let ?v' = "apps s (t' # us @ [u])"
  let ?v = "apps s (t # us @ [u])"

  show ?case
  proof (rule gt_same)
    show "chksubs (>\<^sub>t) ?v' ?v"
      using ih by (auto intro: gt_sub gt_sub_arg)
  next
    show "\<forall>f \<in> ground_heads (head ?v'). extf f (>\<^sub>t) (args ?v') (args ?v)"
      by (metis args_apps extf_compat_list gt_irrefl t'_gt_t)
  qed simp
qed


subsection \<open>Compatibility with Arguments\<close>

theorem gt_diff_same_compat_arg:
  assumes
    extf_compat_snoc: "\<And>f. ext_compat_snoc (extf f)" and
    diff_same: "gt_diff s' s \<or> gt_same s' s"
  shows "App s' t >\<^sub>t App s t"
proof -
  {
    assume "s' >\<^sub>t s"
    hence "App s' t >\<^sub>t s"
      using gt_sub_fun gt_trans by blast
    moreover have "App s' t >\<^sub>t t"
      by (simp add: gt_sub_arg)
    ultimately have "chksubs (>\<^sub>t) (App s' t) (App s t)"
      by auto
  }
  note chk_s't_st = this

  show ?thesis
    using diff_same
  proof
    assume "gt_diff s' s"
    hence
      s'_gt_s: "s' >\<^sub>t s" and
      hd_s'_gt_s: "head s' >\<^sub>h\<^sub>d head s" and
      chkvar_s'_s: "chkvar s' s" and
      chk_s'_s: "chksubs (>\<^sub>t) s' s"
      using gt_diff.cases by (auto simp: gt_iff_sub_diff_same)

    have chkvar_s't_st: "chkvar (App s' t) (App s t)"
      using chkvar_s'_s by auto
    show ?thesis
      by (rule gt_diff[OF _ chkvar_s't_st chk_s't_st[OF s'_gt_s]])
        (simp add: hd_s'_gt_s[simplified])
  next
    assume "gt_same s' s"
    hence
      s'_gt_s: "s' >\<^sub>t s" and
      hd_s'_eq_s: "head s' = head s" and
      chk_s'_s: "chksubs (>\<^sub>t) s' s" and
      gts_args: "\<forall>f \<in> ground_heads (head s'). extf f (>\<^sub>t) (args s') (args s)"
      using gt_same.cases by (auto simp: gt_iff_sub_diff_same, metis)

    have gts_args_t:
      "\<forall>f \<in> ground_heads (head (App s' t)). extf f (>\<^sub>t) (args (App s' t)) (args (App s t))"
      using gts_args ext_compat_snoc.compat_append_right[OF extf_compat_snoc] by simp

    show ?thesis
      by (rule gt_same[OF _ chk_s't_st[OF s'_gt_s] gts_args_t]) (simp add: hd_s'_eq_s)
  qed
qed


subsection \<open>Stability under Substitution\<close>

lemma gt_imp_chksubs_gt:
  assumes t_gt_s: "t >\<^sub>t s"
  shows "chksubs (>\<^sub>t) t s"
proof -
  have "is_App s \<Longrightarrow> t >\<^sub>t fun s \<and> t >\<^sub>t arg s"
    using t_gt_s by (meson gt_sub gt_trans)
  thus ?thesis
    by (simp add: tm.case_eq_if)
qed

theorem gt_subst:
  assumes wary_\<rho>: "wary_subst \<rho>"
  shows "t >\<^sub>t s \<Longrightarrow> subst \<rho> t >\<^sub>t subst \<rho> s"
proof (simp only: atomize_imp,
    rule measure_induct_rule[of "\<lambda>(t, s). {#size t, size s#}"
        "\<lambda>(t, s). t >\<^sub>t s \<longrightarrow> subst \<rho> t >\<^sub>t subst \<rho> s" "(t, s)",
      simplified prod.case],
    simp only: split_paired_all prod.case atomize_imp[symmetric])
  fix t s
  assume
    ih: "\<And>ta sa. {#size ta, size sa#} < {#size t, size s#} \<Longrightarrow> ta >\<^sub>t sa \<Longrightarrow>
      subst \<rho> ta >\<^sub>t subst \<rho> sa" and
    t_gt_s: "t >\<^sub>t s"

  {
    assume chk_t_s: "chksubs (>\<^sub>t) t s"
    have "chksubs (>\<^sub>t) (subst \<rho> t) (subst \<rho> s)"
    proof (cases s)
      case s: (Hd \<zeta>)
      show ?thesis
      proof (cases \<zeta>)
        case \<zeta>: (Var x)
        have psub_x_t: "proper_sub (Hd (Var x)) t"
          using \<zeta> s t_gt_s gt_imp_vars gt_irrefl in_vars_imp_sub by fastforce
        show ?thesis
          unfolding \<zeta> s
          by (rule gt_imp_chksubs_gt[OF gt_proper_sub[OF proper_sub_subst]]) (rule psub_x_t)
      qed (auto simp: s)
    next
      case s: (App s1 s2)
      have "t >\<^sub>t s1" and "t >\<^sub>t s2"
        using s chk_t_s by auto
      thus ?thesis
        using s by (auto intro!: ih[of t s1] ih[of t s2])
    qed
  }
  note chk_\<rho>t_\<rho>s_if = this

  show "subst \<rho> t >\<^sub>t subst \<rho> s"
    using t_gt_s
  proof cases
    case gt_sub_t_s: gt_sub
    obtain t1 t2 where t: "t = App t1 t2"
      using gt_sub_t_s(1) by (metis tm.collapse(2))
    show ?thesis
      using gt_sub ih[of t1 s] ih[of t2 s] gt_sub_t_s(2) t by auto
  next
    case gt_diff_t_s: gt_diff
    have "head (subst \<rho> t) >\<^sub>h\<^sub>d head (subst \<rho> s)"
      by (meson wary_subst_ground_heads gt_diff_t_s(1) gt_hd_def subsetCE wary_\<rho>)
    moreover have "chkvar (subst \<rho> t) (subst \<rho> s)"
      unfolding chkvar_def using vars_subst_subseteq[OF gt_imp_vars[OF t_gt_s]] vars_head_subseteq
      by force
    ultimately show ?thesis
      by (rule gt_diff[OF _ _ chk_\<rho>t_\<rho>s_if[OF gt_diff_t_s(3)]])
  next
    case gt_same_t_s: gt_same

    have hd_\<rho>t_eq_\<rho>s: "head (subst \<rho> t) = head (subst \<rho> s)"
      using gt_same_t_s(1) by simp

    {
      fix f
      assume f_in_grounds: "f \<in> ground_heads (head (subst \<rho> t))"

      let ?S = "set (args t) \<union> set (args s)"

      have extf_args_s_t: "extf f (>\<^sub>t) (args t) (args s)"
        using gt_same_t_s(3) f_in_grounds wary_\<rho> wary_subst_ground_heads by blast
      have "extf f (>\<^sub>t) (map (subst \<rho>) (args t)) (map (subst \<rho>) (args s))"
      proof (rule extf_map[of ?S, OF _ _ _ _ _ _ extf_args_s_t])
        have sz_a: "\<forall>ta \<in> ?S. \<forall>sa \<in> ?S. {#size ta, size sa#} < {#size t, size s#}"
          by (fastforce intro: Max_lt_imp_lt_mset dest: size_in_args)
        show "\<forall>ta \<in> ?S. \<forall>sa \<in> ?S. ta >\<^sub>t sa \<longrightarrow> subst \<rho> ta >\<^sub>t subst \<rho> sa"
          using ih sz_a size_in_args by fastforce
      qed (auto intro!: gt_irrefl elim!: gt_trans)
      hence "extf f (>\<^sub>t) (args (subst \<rho> t)) (args (subst \<rho> s))"
        by (auto simp: gt_same_t_s(1) intro: extf_compat_append_left)
    }
    hence "\<forall>f \<in> ground_heads (head (subst \<rho> t)).
      extf f (>\<^sub>t) (args (subst \<rho> t)) (args (subst \<rho> s))"
      by blast
    thus ?thesis
      by (rule gt_same[OF hd_\<rho>t_eq_\<rho>s chk_\<rho>t_\<rho>s_if[OF gt_same_t_s(2)]])
  qed
qed


subsection \<open>Totality on Ground Terms\<close>

theorem gt_total_ground:
  assumes extf_total: "\<And>f. ext_total (extf f)"
  shows "ground t \<Longrightarrow> ground s \<Longrightarrow> t >\<^sub>t s \<or> s >\<^sub>t t \<or> t = s"
proof (simp only: atomize_imp,
    rule measure_induct_rule[of "\<lambda>(t, s). size t + size s"
      "\<lambda>(t, s). ground t \<longrightarrow> ground s \<longrightarrow> t >\<^sub>t s \<or> s >\<^sub>t t \<or> t = s" "(t, s)", simplified prod.case],
    simp only: split_paired_all prod.case atomize_imp[symmetric])
  fix t s :: "('s, 'v) tm"
  assume
    ih: "\<And>ta sa. size ta + size sa < size t + size s \<Longrightarrow> ground ta \<Longrightarrow> ground sa \<Longrightarrow>
      ta >\<^sub>t sa \<or> sa >\<^sub>t ta \<or> ta = sa" and
    gr_t: "ground t" and gr_s: "ground s"

  let ?case = "t >\<^sub>t s \<or> s >\<^sub>t t \<or> t = s"

  have "chksubs (>\<^sub>t) t s \<or> s >\<^sub>t t"
    unfolding chksubs_def tm.case_eq_if using ih[of t "fun s"] ih[of t "arg s"]
    by (metis gt_sub add_less_cancel_left gr_s gr_t ground_arg ground_fun size_arg_lt size_fun_lt)
  moreover have "chksubs (>\<^sub>t) s t \<or> t >\<^sub>t s"
    unfolding chksubs_def tm.case_eq_if using ih[of "fun t" s] ih[of "arg t" s]
    by (metis gt_sub add_less_cancel_right gr_s gr_t ground_arg ground_fun size_arg_lt size_fun_lt)
  moreover
  {
    assume
      chksubs_t_s: "chksubs (>\<^sub>t) t s" and
      chksubs_s_t: "chksubs (>\<^sub>t) s t"

    obtain g where g: "head t = Sym g"
      using gr_t by (metis ground_head hd.collapse(2))
    obtain f where f: "head s = Sym f"
      using gr_s by (metis ground_head hd.collapse(2))

    have chkvar_t_s: "chkvar t s" and chkvar_s_t: "chkvar s t"
      using g f by simp_all

    {
      assume g_gt_f: "g >\<^sub>s f"
      have "t >\<^sub>t s"
        by (rule gt_diff[OF _ chkvar_t_s chksubs_t_s]) (simp add: g f gt_sym_imp_hd[OF g_gt_f])
    }
    moreover
    {
      assume f_gt_g: "f >\<^sub>s g"
      have "s >\<^sub>t t"
        by (rule gt_diff[OF _ chkvar_s_t chksubs_s_t]) (simp add: g f gt_sym_imp_hd[OF f_gt_g])
    }
    moreover
    {
      assume g_eq_f: "g = f"
      hence hd_t: "head t = head s"
        using g f by auto

      let ?ts = "args t"
      let ?ss = "args s"

      have gr_ts: "\<forall>ta \<in> set ?ts. ground ta"
        using ground_args[OF _ gr_t] by blast
      have gr_ss: "\<forall>sa \<in> set ?ss. ground sa"
        using ground_args[OF _ gr_s] by blast

      {
        assume ts_eq_ss: "?ts = ?ss"
        have "t = s"
          using hd_t ts_eq_ss by (rule tm_expand_apps)
      }
      moreover
      {
        assume ts_gt_ss: "extf g (>\<^sub>t) ?ts ?ss"
        have "t >\<^sub>t s"
          by (rule gt_same[OF hd_t chksubs_t_s]) (auto simp: g ts_gt_ss)
      }
      moreover
      {
        assume ss_gt_ts: "extf g (>\<^sub>t) ?ss ?ts"
        have "s >\<^sub>t t"
          by (rule gt_same[OF hd_t[symmetric] chksubs_s_t]) (auto simp: f[folded g_eq_f] ss_gt_ts)
      }
      ultimately have ?case
        using ih gr_ss gr_ts
          ext_total.total[OF extf_total, rule_format, of "set ?ts" "set ?ss" "(>\<^sub>t)" ?ts ?ss g]
        by (metis add_strict_mono in_listsI size_in_args)
    }
    ultimately have ?case
      using gt_sym_total by blast
  }
  ultimately show ?case
    by fast
qed


subsection \<open>Well-foundedness\<close>

abbreviation gtg :: "('s, 'v) tm \<Rightarrow> ('s, 'v) tm \<Rightarrow> bool" (infix ">\<^sub>t\<^sub>g" 50) where
  "(>\<^sub>t\<^sub>g) \<equiv> \<lambda>t s. ground t \<and> t >\<^sub>t s"

theorem gt_wf:
  assumes extf_wf: "\<And>f. ext_wf (extf f)"
  shows "wfP (\<lambda>s t. t >\<^sub>t s)"
proof -
  have ground_wfP: "wfP (\<lambda>s t. t >\<^sub>t\<^sub>g s)"
    unfolding wfP_iff_no_inf_chain
  proof
    assume "\<exists>f. inf_chain (>\<^sub>t\<^sub>g) f"
    then obtain t where t_bad: "bad (>\<^sub>t\<^sub>g) t"
      unfolding inf_chain_def bad_def by blast

    let ?ff = "worst_chain (>\<^sub>t\<^sub>g) (\<lambda>t s. size t > size s)"
    let ?U_of = "\<lambda>i. if is_App (?ff i) then {fun (?ff i)} \<union> set (args (?ff i)) else {}"

    note wf_sz = wf_app[OF wellorder_class.wf, of size, simplified]

    define U where "U = (\<Union>i. ?U_of i)"

    have gr: "\<And>i. ground (?ff i)"
      using worst_chain_bad[OF wf_sz t_bad, unfolded inf_chain_def] by fast
    have gr_fun: "\<And>i. ground (fun (?ff i))"
      by (rule ground_fun[OF gr])
    have gr_args: "\<And>i s. s \<in> set (args (?ff i)) \<Longrightarrow> ground s"
      by (rule ground_args[OF _ gr])
    have gr_u: "\<And>u. u \<in> U \<Longrightarrow> ground u"
      unfolding U_def by (auto dest: gr_args) (metis (lifting) empty_iff gr_fun)

    have "\<not> bad (>\<^sub>t\<^sub>g) u" if u_in: "u \<in> ?U_of i" for u i
    proof
      let ?ti = "?ff i"

      assume u_bad: "bad (>\<^sub>t\<^sub>g) u"
      have sz_u: "size u < size ?ti"
      proof (cases "?ff i")
        case Hd
        thus ?thesis
          using u_in size_in_args by fastforce
      next
        case App
        thus ?thesis
          using u_in size_in_args insert_iff size_fun_lt by fastforce
      qed

      show False
      proof (cases i)
        case 0
        thus False
          using sz_u min_worst_chain_0[OF wf_sz u_bad] by simp
      next
        case Suc
        hence "?ff (i - 1) >\<^sub>t ?ff i"
          using worst_chain_pred[OF wf_sz t_bad] by simp
        moreover have "?ff i >\<^sub>t u"
        proof -
          have u_in: "u \<in> ?U_of i"
            using u_in by blast
          have ffi_ne_u: "?ff i \<noteq> u"
            using sz_u by fastforce
          hence "is_App (?ff i) \<Longrightarrow> \<not> sub u (?ff i) \<Longrightarrow> ?ff i >\<^sub>t u"
            using u_in gt_sub sub_args by auto
          thus "?ff i >\<^sub>t u"
            using ffi_ne_u u_in gt_proper_sub sub_args by fastforce
        qed
        ultimately have "?ff (i - 1) >\<^sub>t u"
          by (rule gt_trans)
        thus False
          using Suc sz_u min_worst_chain_Suc[OF wf_sz u_bad] gr by fastforce
      qed
    qed
    hence u_good: "\<And>u. u \<in> U \<Longrightarrow> \<not> bad (>\<^sub>t\<^sub>g) u"
      unfolding U_def by blast

    have bad_diff_same: "inf_chain (\<lambda>t s. ground t \<and> (gt_diff t s \<or> gt_same t s)) ?ff"
      unfolding inf_chain_def
    proof (intro allI conjI)
      fix i

      show "ground (?ff i)"
        by (rule gr)

      have gt: "?ff i >\<^sub>t ?ff (Suc i)"
        using worst_chain_pred[OF wf_sz t_bad] by blast

      have "\<not> gt_sub (?ff i) (?ff (Suc i))"
      proof
        assume a: "gt_sub (?ff i) (?ff (Suc i))"
        hence fi_app: "is_App (?ff i)" and
          fun_or_arg_fi_ge: "fun (?ff i) \<ge>\<^sub>t ?ff (Suc i) \<or> arg (?ff i) \<ge>\<^sub>t ?ff (Suc i)"
          unfolding gt_sub.simps by blast+
        have "fun (?ff i) \<in> ?U_of i"
          unfolding U_def using fi_app by auto
        moreover have "arg (?ff i) \<in> ?U_of i"
          unfolding U_def using fi_app arg_in_args by force
        ultimately obtain uij where uij_in: "uij \<in> U" and uij_cases: "uij \<ge>\<^sub>t ?ff (Suc i)"
          unfolding U_def using fun_or_arg_fi_ge by blast

        have "\<And>n. ?ff n >\<^sub>t ?ff (Suc n)"
          by (rule worst_chain_pred[OF wf_sz t_bad, THEN conjunct2])
        hence uij_gt_i_plus_3: "uij >\<^sub>t ?ff (Suc (Suc i))"
          using gt_trans uij_cases by blast

        have "inf_chain (>\<^sub>t\<^sub>g) (\<lambda>j. if j = 0 then uij else ?ff (Suc (i + j)))"
          unfolding inf_chain_def
          by (auto intro!: gr gr_u[OF uij_in] uij_gt_i_plus_3 worst_chain_pred[OF wf_sz t_bad])
        hence "bad (>\<^sub>t\<^sub>g) uij"
          unfolding bad_def by fastforce
        thus False
          using u_good[OF uij_in] by sat
      qed
      thus "gt_diff (?ff i) (?ff (Suc i)) \<or> gt_same (?ff i) (?ff (Suc i))"
        using gt unfolding gt_iff_sub_diff_same by sat
    qed

    have "wf {(s, t). ground s \<and> ground t \<and> sym (head t) >\<^sub>s sym (head s)}"
      using gt_sym_wf unfolding wfP_def wf_iff_no_infinite_down_chain by fast
    moreover have "{(s, t). ground t \<and> gt_diff t s}
      \<subseteq> {(s, t). ground s \<and> ground t \<and> sym (head t) >\<^sub>s sym (head s)}"
    proof (clarsimp, intro conjI)
      fix s t
      assume gr_t: "ground t" and gt_diff_t_s: "gt_diff t s"
      thus gr_s: "ground s"
        using gt_iff_sub_diff_same gt_imp_vars by fastforce

      show "sym (head t) >\<^sub>s sym (head s)"
        using gt_diff_t_s ground_head[OF gr_s] ground_head[OF gr_t]
        by (cases; cases "head s"; cases "head t") (auto simp: gt_hd_def)
    qed
    ultimately have wf_diff: "wf {(s, t). ground t \<and> gt_diff t s}"
      by (rule wf_subset)

    have diff_O_same: "{(s, t). ground t \<and> gt_diff t s} O {(s, t). ground t \<and> gt_same t s}
      \<subseteq> {(s, t). ground t \<and> gt_diff t s}"
      unfolding gt_diff.simps gt_same.simps
      by clarsimp (metis chksubs_def empty_subsetI gt_diff[unfolded chkvar_def] gt_imp_chksubs_gt
        gt_same gt_trans)

    have diff_same_as_union: "{(s, t). ground t \<and> (gt_diff t s \<or> gt_same t s)} =
      {(s, t). ground t \<and> gt_diff t s} \<union> {(s, t). ground t \<and> gt_same t s}"
      by auto

    obtain k where bad_same: "inf_chain (\<lambda>t s. ground t \<and> gt_same t s) (\<lambda>i. ?ff (i + k))"
      using wf_infinite_down_chain_compatible[OF wf_diff _ diff_O_same, of ?ff] bad_diff_same
      unfolding inf_chain_def diff_same_as_union[symmetric] by auto
    hence hd_sym: "\<And>i. is_Sym (head (?ff (i + k)))"
      unfolding inf_chain_def by (simp add: ground_head)

    define f where "f = sym (head (?ff k))"

    have hd_eq_f: "head (?ff (i + k)) = Sym f" for i
    proof (induct i)
      case 0
      thus ?case
        by (auto simp: f_def hd.collapse(2)[OF hd_sym, of 0, simplified])
    next
      case (Suc ia)
      thus ?case
        using bad_same unfolding inf_chain_def gt_same.simps by simp
    qed

    let ?gtu = "\<lambda>t s. t \<in> U \<and> t >\<^sub>t s"

    have "t \<in> set (args (?ff i)) \<Longrightarrow> t \<in> ?U_of i" for t i
      unfolding U_def
      by (cases "is_App (?ff i)", simp_all,
        metis (lifting) neq_iff size_in_args sub.cases sub_args tm.discI(2))
    moreover have "\<And>i. extf f (>\<^sub>t) (args (?ff (i + k))) (args (?ff (Suc i + k)))"
      using bad_same hd_eq_f unfolding inf_chain_def gt_same.simps by auto
    ultimately have "\<And>i. extf f ?gtu (args (?ff (i + k))) (args (?ff (Suc i + k)))"
      using extf_mono_strong[of _ _ "(>\<^sub>t)" "\<lambda>t s. t \<in> U \<and> t >\<^sub>t s"] unfolding U_def by blast
    hence "inf_chain (extf f ?gtu) (\<lambda>i. args (?ff (i + k)))"
      unfolding inf_chain_def by blast
    hence nwf_ext: "\<not> wfP (\<lambda>xs ys. extf f ?gtu ys xs)"
      unfolding wfP_iff_no_inf_chain by fast

    have gtu_le_gtg: "?gtu \<le> (>\<^sub>t\<^sub>g)"
      by (auto intro!: gr_u)

    have "wfP (\<lambda>s t. ?gtu t s)"
      unfolding wfP_iff_no_inf_chain
    proof (intro notI, elim exE)
      fix f
      assume bad_f: "inf_chain ?gtu f"
      hence bad_f0: "bad ?gtu (f 0)"
        by (rule inf_chain_bad)

      have "f 0 \<in> U"
        using bad_f unfolding inf_chain_def by blast
      hence good_f0: "\<not> bad ?gtu (f 0)"
        using u_good bad_f inf_chain_bad inf_chain_subset[OF _ gtu_le_gtg] by blast

      show False
        using bad_f0 good_f0 by sat
    qed
    hence wf_ext: "wfP (\<lambda>xs ys. extf f ?gtu ys xs)"
      by (rule ext_wf.wf[OF extf_wf, rule_format])

    show False
      using nwf_ext wf_ext by blast
  qed

  let ?subst = "subst grounding_\<rho>"

  have "wfP (\<lambda>s t. ?subst t >\<^sub>t\<^sub>g ?subst s)"
    by (rule wfP_app[OF ground_wfP])
  hence "wfP (\<lambda>s t. ?subst t >\<^sub>t ?subst s)"
    by (simp add: ground_grounding_\<rho>)
  thus ?thesis
    by (auto intro: wfP_subset gt_subst[OF wary_grounding_\<rho>])
qed

end

end
