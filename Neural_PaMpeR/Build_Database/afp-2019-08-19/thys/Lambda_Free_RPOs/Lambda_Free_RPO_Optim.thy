(*  Title:       The Optimized Graceful Recursive Path Order for Lambda-Free Higher-Order Terms
    Author:      Jasmin Blanchette <jasmin.blanchette at inria.fr>, 2016
    Maintainer:  Jasmin Blanchette <jasmin.blanchette at inria.fr>
*)

section \<open>The Optimized Graceful Recursive Path Order for Lambda-Free Higher-Order Terms\<close>

theory Lambda_Free_RPO_Optim
imports Lambda_Free_RPO_Std
begin

text \<open>
This theory defines the optimized variant of the graceful recursive path order
(RPO) for \<open>\<lambda>\<close>-free higher-order terms.
\<close>


subsection \<open>Setup\<close>

locale rpo_optim = rpo_basis _ _ arity_sym arity_var
    for
      arity_sym :: "'s \<Rightarrow> enat" and
      arity_var :: "'v \<Rightarrow> enat" +
  assumes extf_ext_snoc: "ext_snoc (extf f)"
begin

lemmas extf_snoc = ext_snoc.snoc[OF extf_ext_snoc]


subsection \<open>Definition of the Order\<close>

definition
  chkargs :: "(('s, 'v) tm \<Rightarrow> ('s, 'v) tm \<Rightarrow> bool) \<Rightarrow> ('s, 'v) tm \<Rightarrow> ('s, 'v) tm \<Rightarrow> bool"
where
  [simp]: "chkargs gt t s \<longleftrightarrow> (\<forall>s' \<in> set (args s). gt t s')"

lemma chkargs_mono[mono]: "gt \<le> gt' \<Longrightarrow> chkargs gt \<le> chkargs gt'"
  by force

inductive gt :: "('s, 'v) tm \<Rightarrow> ('s, 'v) tm \<Rightarrow> bool" (infix ">\<^sub>t" 50) where
  gt_arg: "ti \<in> set (args t) \<Longrightarrow> ti >\<^sub>t s \<or> ti = s \<Longrightarrow> t >\<^sub>t s"
| gt_diff: "head t >\<^sub>h\<^sub>d head s \<Longrightarrow> chkvar t s \<Longrightarrow> chkargs (>\<^sub>t) t s \<Longrightarrow> t >\<^sub>t s"
| gt_same: "head t = head s \<Longrightarrow> chkargs (>\<^sub>t) t s \<Longrightarrow>
    (\<forall>f \<in> ground_heads (head t). extf f (>\<^sub>t) (args t) (args s)) \<Longrightarrow> t >\<^sub>t s"

abbreviation ge :: "('s, 'v) tm \<Rightarrow> ('s, 'v) tm \<Rightarrow> bool" (infix "\<ge>\<^sub>t" 50) where
  "t \<ge>\<^sub>t s \<equiv> t >\<^sub>t s \<or> t = s"


subsection \<open>Transitivity\<close>

lemma gt_in_args_imp: "ti \<in> set (args t) \<Longrightarrow> ti >\<^sub>t s \<Longrightarrow> t >\<^sub>t s"
  by (cases t) (auto intro: gt_arg)

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
    case (gt_arg ti)
    thus ?thesis
      using ih[of ti s]
      by (metis size_in_args vars_args_subseteq add_mono_thms_linordered_field(1) order_trans)
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
        using gt_diff ih
        by simp (metis (no_types) add.assoc gt.simps[unfolded chkargs_def chkvar_def] less_add_Suc1)
    qed
  next
    case gt_same
    thus ?thesis
    proof (cases s rule: tm_exhaust_apps)
      case s: (apps \<zeta> ss)
      thus ?thesis
        using gt_same unfolding chkargs_def s
        by (auto intro!: vars_head_subseteq)
          (metis ih[of t] insert_absorb insert_subset nat_add_left_cancel_less s size_in_args
            tm_collapse_apps tm_inject_apps)
    qed
  qed
qed

lemma gt_trans: "u >\<^sub>t t \<Longrightarrow> t >\<^sub>t s \<Longrightarrow> u >\<^sub>t s"
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

  have chk_u_s_if: "chkargs (>\<^sub>t) u s" if chk_t_s: "chkargs (>\<^sub>t) t s"
  proof (clarsimp simp only: chkargs_def)
    fix s'
    assume "s' \<in> set (args s)"
    thus "u >\<^sub>t s'"
      using chk_t_s by (auto intro!: ih[of _ _ s', OF _ u_gt_t] size_in_args)
  qed

  have u_gt_s_if_ui: "ui \<ge>\<^sub>t t \<Longrightarrow> u >\<^sub>t s" if ui_in: "ui \<in> set (args u)" for ui
    using ih[of ui t s, simplified, OF size_in_args[OF ui_in] _ t_gt_s]
      gt_in_args_imp[OF ui_in, of s] t_gt_s by blast

  show "u >\<^sub>t s"
    using t_gt_s
  proof cases
    case gt_arg_t_s: (gt_arg ti)
    have u_gt_s_if_chk_u_t: ?thesis if chk_u_t: "chkargs (>\<^sub>t) u t"
      using ih[of u ti s] gt_arg_t_s chk_u_t size_in_args by force
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

lemma gt_sub_fun: "App s t >\<^sub>t s"
  by (rule gt_same) (auto intro: extf_snoc gt_arg[of _ "App s t"])

end


subsection \<open>Conditional Equivalence with Unoptimized Version\<close>

context rpo
begin

context
  assumes extf_ext_snoc: "\<And>f. ext_snoc (extf f)"
begin

lemma rpo_optim: "rpo_optim ground_heads_var (>\<^sub>s) extf arity_sym arity_var"
  unfolding rpo_optim_def rpo_optim_axioms_def using rpo_basis_axioms extf_ext_snoc by auto

abbreviation
  chkargs :: "(('s, 'v) tm \<Rightarrow> ('s, 'v) tm \<Rightarrow> bool) \<Rightarrow> ('s, 'v) tm \<Rightarrow> ('s, 'v) tm \<Rightarrow> bool"
where
  "chkargs \<equiv> rpo_optim.chkargs"

abbreviation gt_optim :: "('s, 'v) tm \<Rightarrow> ('s, 'v) tm \<Rightarrow> bool" (infix ">\<^sub>t\<^sub>o" 50) where
  "(>\<^sub>t\<^sub>o) \<equiv> rpo_optim.gt ground_heads_var (>\<^sub>s) extf"

abbreviation ge_optim :: "('s, 'v) tm \<Rightarrow> ('s, 'v) tm \<Rightarrow> bool" (infix "\<ge>\<^sub>t\<^sub>o" 50) where
  "(\<ge>\<^sub>t\<^sub>o) \<equiv> rpo_optim.ge ground_heads_var (>\<^sub>s) extf"

theorem gt_iff_optim: "t >\<^sub>t s \<longleftrightarrow> t >\<^sub>t\<^sub>o s"
proof (rule measure_induct_rule[of "\<lambda>(t, s). size t + size s"
      "\<lambda>(t, s). t >\<^sub>t s \<longleftrightarrow> t >\<^sub>t\<^sub>o s" "(t, s)", simplified prod.case],
    simp only: split_paired_all prod.case)
  fix t s :: "('s, 'v) tm"
  assume ih: "\<And>ta sa. size ta + size sa < size t + size s \<Longrightarrow> ta >\<^sub>t sa \<longleftrightarrow> ta >\<^sub>t\<^sub>o sa"

  show "t >\<^sub>t s \<longleftrightarrow> t >\<^sub>t\<^sub>o s"
  proof
    assume t_gt_s: "t >\<^sub>t s"

    have chkargs_if_chksubs: "chkargs (>\<^sub>t\<^sub>o) t s" if chksubs: "chksubs (>\<^sub>t) t s"
      unfolding rpo_optim.chkargs_def[OF rpo_optim]
    proof (cases s, simp_all, intro conjI ballI)
      fix s1 s2
      assume s: "s = App s1 s2"

      have t_gt_s2: "t >\<^sub>t s2"
        using chksubs s by simp
      show "t >\<^sub>t\<^sub>o s2"
        by (rule ih[THEN iffD1, OF _ t_gt_s2]) (simp add: s)

      {
        fix s1i
        assume s1i_in: "s1i \<in> set (args s1)"

        have "t >\<^sub>t s1"
          using chksubs s by simp
        moreover have "s1 >\<^sub>t s1i"
          using s1i_in gt_proper_sub size_in_args sub_args by fastforce
        ultimately have t_gt_s1i: "t >\<^sub>t s1i"
          by (rule gt_trans)

        have sz_s1i: "size s1i < size s"
          using size_in_args[OF s1i_in] s by simp

        show "t >\<^sub>t\<^sub>o s1i"
          by (rule ih[THEN iffD1, OF _ t_gt_s1i]) (simp add: sz_s1i)
      }
    qed

    show "t >\<^sub>t\<^sub>o s"
      using t_gt_s
    proof cases
      case gt_sub
      note t_app = this(1) and ti_geo_s = this(2)

      obtain t1 t2 where t: "t = App t1 t2"
        using t_app by (metis tm.collapse(2))

      have t_gto_t1: "t >\<^sub>t\<^sub>o t1"
        unfolding t by (rule rpo_optim.gt_sub_fun[OF rpo_optim])
      have t_gto_t2: "t >\<^sub>t\<^sub>o t2"
        unfolding t by (rule rpo_optim.gt_arg[OF rpo_optim, of t2]) simp+

      {
        assume t1_gt_s: "t1 >\<^sub>t s"
        have "t1 >\<^sub>t\<^sub>o s"
          by (rule ih[THEN iffD1, OF _ t1_gt_s]) (simp add: t)
        hence ?thesis
          by (rule rpo_optim.gt_trans[OF rpo_optim t_gto_t1])
      }
      moreover
      {
        assume t2_gt_s: "t2 >\<^sub>t s"
        have "t2 >\<^sub>t\<^sub>o s"
          by (rule ih[THEN iffD1, OF _ t2_gt_s]) (simp add: t)
        hence ?thesis
          by (rule rpo_optim.gt_trans[OF rpo_optim t_gto_t2])
      }
      ultimately show ?thesis
        using t ti_geo_s t_gto_t1 t_gto_t2 by auto
    next
      case gt_diff
      note hd_t_gt_s = this(1) and chkvar = this(2) and chksubs = this(3)
      show ?thesis
        by (rule rpo_optim.gt_diff[OF rpo_optim hd_t_gt_s chkvar chkargs_if_chksubs[OF chksubs]])
    next
      case gt_same
      note hd_t_eq_s = this(1) and chksubs = this(2) and extf = this(3)

      have extf_gto: "\<forall>f \<in> ground_heads (head t). extf f (>\<^sub>t\<^sub>o) (args t) (args s)"
      proof (rule ballI, rule extf_mono_strong[of _ _ "(>\<^sub>t)", rule_format])
        fix f
        assume f_in_ground: "f \<in> ground_heads (head t)"

        {
          fix ta sa
          assume ta_in: "ta \<in> set (args t)" and sa_in: "sa \<in> set (args s)" and ta_gt_sa: "ta >\<^sub>t sa"

          show "ta >\<^sub>t\<^sub>o sa"
            by (rule ih[THEN iffD1, OF _ ta_gt_sa])
              (simp add: ta_in sa_in add_less_mono size_in_args)
        }

        show "extf f (>\<^sub>t) (args t) (args s)"
          using f_in_ground extf by simp
      qed

      show ?thesis
        by (rule rpo_optim.gt_same[OF rpo_optim hd_t_eq_s chkargs_if_chksubs[OF chksubs] extf_gto])
    qed
  next
    assume t_gto_s: "t >\<^sub>t\<^sub>o s"

    have chksubs_if_chkargs: "chksubs (>\<^sub>t) t s" if chkargs: "chkargs (>\<^sub>t\<^sub>o) t s"
      unfolding chksubs_def
    proof (cases s, simp_all, rule conjI)
      fix s1 s2
      assume s: "s = App s1 s2"

      have "s >\<^sub>t\<^sub>o s1"
        unfolding s by (rule rpo_optim.gt_sub_fun[OF rpo_optim])
      hence t_gto_s1: "t >\<^sub>t\<^sub>o s1"
        by (rule rpo_optim.gt_trans[OF rpo_optim t_gto_s])
      show "t >\<^sub>t s1"
        by (rule ih[THEN iffD2, OF _ t_gto_s1]) (simp add: s)

      have t_gto_s2: "t >\<^sub>t\<^sub>o s2"
        using chkargs unfolding rpo_optim.chkargs_def[OF rpo_optim] s by simp
      show "t >\<^sub>t s2"
        by (rule ih[THEN iffD2, OF _ t_gto_s2]) (simp add: s)
    qed

    show "t >\<^sub>t s"
    proof (cases rule: rpo_optim.gt.cases[OF rpo_optim t_gto_s,
        case_names gto_arg gto_diff gto_same])
      case (gto_arg ti)
      hence ti_in: "ti \<in> set (args t)" and ti_geo_s: "ti \<ge>\<^sub>t\<^sub>o s"
        by auto
      obtain \<zeta> ts where t: "t = apps (Hd \<zeta>) ts"
        by (fact tm_exhaust_apps)

      {
        assume ti_gto_s: "ti >\<^sub>t\<^sub>o s"
        hence ti_gt_s: "ti >\<^sub>t s"
          using ih[of ti s] size_in_args ti_in by auto
        moreover have "t >\<^sub>t ti"
          using sub_args[OF ti_in] gt_proper_sub size_in_args[OF ti_in] by blast
        ultimately have ?thesis
          using gt_trans by blast
      }
      moreover
      {
        assume "ti = s"
        hence ?thesis
          using sub_args[OF ti_in] gt_proper_sub size_in_args[OF ti_in] by blast
      }
      ultimately show ?thesis
        using ti_geo_s by blast
    next
      case gto_diff
      hence hd_t_gt_s: "head t >\<^sub>h\<^sub>d head s" and chkvar: "chkvar t s" and
        chkargs: "chkargs (>\<^sub>t\<^sub>o) t s"
        by blast+

      have "chksubs (>\<^sub>t) t s"
        by (rule chksubs_if_chkargs[OF chkargs])
      thus ?thesis
        by (rule gt_diff[OF hd_t_gt_s chkvar])
    next
      case gto_same
      hence hd_t_eq_s: "head t = head s" and chkargs: "chkargs (>\<^sub>t\<^sub>o) t s" and
        extf_gto: "\<forall>f \<in> ground_heads (head t). extf f (>\<^sub>t\<^sub>o) (args t) (args s)"
        by blast+

      have chksubs: "chksubs (>\<^sub>t) t s"
        by (rule chksubs_if_chkargs[OF chkargs])

      have extf: "\<forall>f \<in> ground_heads (head t). extf f (>\<^sub>t) (args t) (args s)"
      proof (rule ballI, rule extf_mono_strong[of _ _ "(>\<^sub>t\<^sub>o)", rule_format])
        fix f
        assume f_in_ground: "f \<in> ground_heads (head t)"

        {
          fix ta sa
          assume ta_in: "ta \<in> set (args t)" and sa_in: "sa \<in> set (args s)" and ta_gto_sa: "ta >\<^sub>t\<^sub>o sa"

          show "ta >\<^sub>t sa"
            by (rule ih[THEN iffD2, OF _ ta_gto_sa])
              (simp add: ta_in sa_in add_less_mono size_in_args)
        }

        show "extf f (>\<^sub>t\<^sub>o) (args t) (args s)"
          using f_in_ground extf_gto by simp
      qed

      show ?thesis
        by (rule gt_same[OF hd_t_eq_s chksubs extf])
    qed
  qed
qed

end

end

end
