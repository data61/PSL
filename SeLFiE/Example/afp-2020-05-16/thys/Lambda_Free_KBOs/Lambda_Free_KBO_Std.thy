(*  Title:       The Graceful Standard Knuth-Bendix Order for Lambda-Free Higher-Order Terms
    Author:      Heiko Becker <heikobecker92@gmail.com>, 2016
    Author:      Jasmin Blanchette <jasmin.blanchette at inria.fr>, 2016
    Author:      Uwe Waldmann <waldmann at mpi-inf.mpg.de>, 2016
    Author:      Daniel Wand <dwand at mpi-inf.mpg.de>, 2016
    Maintainer:  Jasmin Blanchette <jasmin.blanchette at inria.fr>
*)

section \<open>The Graceful Standard Knuth--Bendix Order for Lambda-Free Higher-Order Terms\<close>

theory Lambda_Free_KBO_Std
imports Lambda_Free_KBO_Util Nested_Multisets_Ordinals.Multiset_More
abbrevs ">t" = ">\<^sub>t"
  and "\<ge>t" = "\<ge>\<^sub>t"
begin

text \<open>
This theory defines the standard version of the graceful Knuth--Bendix order for \<open>\<lambda>\<close>-free
higher-order terms. Standard means that one symbol is allowed to have a weight of 0.
\<close>


subsection \<open>Setup\<close>

locale kbo_std = kbo_std_basis _ _ arity_sym arity_var wt_sym
  for
    arity_sym :: "'s \<Rightarrow> enat" and
    arity_var :: "'v \<Rightarrow> enat" and
    wt_sym :: "'s \<Rightarrow> nat"
begin


subsection \<open>Weights\<close>

primrec wt :: "('s, 'v) tm \<Rightarrow> nat" where
  "wt (Hd \<zeta>) = (LEAST w. \<exists>f \<in> ground_heads \<zeta>. w = wt_sym f + the_enat (\<delta> * arity_sym f))"
| "wt (App s t) = (wt s - \<delta>) + wt t"

lemma wt_Hd_Sym: "wt (Hd (Sym f)) = wt_sym f + the_enat (\<delta> * arity_sym f)"
  by simp

lemma exists_wt_sym: "\<exists>f \<in> ground_heads \<zeta>. wt (Hd \<zeta>) = wt_sym f + the_enat (\<delta> * arity_sym f)"
  by (auto intro: Least_in_nonempty_set_imp_ex)

lemma wt_le_wt_sym: "f \<in> ground_heads \<zeta> \<Longrightarrow> wt (Hd \<zeta>) \<le> wt_sym f + the_enat (\<delta> * arity_sym f)"
  using not_le_imp_less not_less_Least by fastforce

lemma enat_the_enat_\<delta>_times_arity_sym[simp]: "enat (the_enat (\<delta> * arity_sym f)) = \<delta> * arity_sym f"
  using arity_sym_ne_infinity_if_\<delta>_gt_0 imult_is_infinity zero_enat_def by fastforce

lemma wt_arg_le: "wt (arg s) \<le> wt s"
  by (cases s) auto

lemma wt_ge_\<epsilon>: "wt s \<ge> \<epsilon>"
  by (induct s, metis exists_wt_sym of_nat_eq_enat le_diff_conv of_nat_id wt_sym_ge,
    simp add: add_increasing)

lemma wt_ge_\<delta>: "wt s \<ge> \<delta>"
  by (meson \<delta>_le_\<epsilon> order.trans enat_ord_simps(1) wt_ge_\<epsilon>)

lemma wt_gt_\<delta>_if_superunary: "arity_hd (head s) > 1 \<Longrightarrow> wt s > \<delta>"
proof (induct s)
  case \<zeta>: (Hd \<zeta>)
  obtain g where
    g_in_grs: "g \<in> ground_heads \<zeta>" and
    wt_\<zeta>: "wt (Hd \<zeta>) = wt_sym g + the_enat (\<delta> * arity_sym g)"
    using exists_wt_sym by blast

  have "arity_hd \<zeta> > 1"
    using \<zeta> by auto
  hence ary_g: "arity_sym g > 1"
    using ground_heads_arity[OF g_in_grs] by simp

  show ?case
  proof (cases "\<delta> = 0")
    case True
    thus ?thesis
      by (metis \<epsilon>_gt_0 gr0I leD wt_ge_\<epsilon>)
  next
    case \<delta>_ne_0: False
    hence ary_g_ninf: "arity_sym g \<noteq> \<infinity>"
      using arity_sym_ne_infinity_if_\<delta>_gt_0 by blast
    hence "\<delta> < the_enat (enat \<delta> * arity_sym g)"
      using \<delta>_ne_0 ary_g by (cases "arity_sym g") (auto simp: one_enat_def)
    thus ?thesis
      unfolding wt_\<zeta> by simp
  qed
next
  case (App s t)
  thus ?case
    using wt_ge_\<delta>[of t] by force
qed

lemma wt_App_\<delta>: "wt (App s t) = wt t \<Longrightarrow> wt s = \<delta>"
  by (simp add: order.antisym wt_ge_\<delta>)

lemma wt_App_ge_fun: "wt (App s t) \<ge> wt s"
  by (metis diff_le_mono2 wt_ge_\<delta> le_diff_conv wt.simps(2))

lemma wt_hd_le: "wt (Hd (head s)) \<le> wt s"
  by (induct s, simp) (metis head_App leD le_less_trans not_le_imp_less wt_App_ge_fun)

lemma wt_\<delta>_imp_\<delta>_eq_\<epsilon>: "wt s = \<delta> \<Longrightarrow> \<delta> = \<epsilon>"
  by (metis \<delta>_le_\<epsilon> le_antisym wt_ge_\<epsilon>)

lemma wt_ge_arity_head_if_\<delta>_gt_0:
  assumes \<delta>_gt_0: "\<delta> > 0"
  shows "wt s \<ge> arity_hd (head s)"
proof (induct s)
  case (Hd \<zeta>)

  obtain f where
    f_in_\<zeta>: "f \<in> ground_heads \<zeta>" and
    wt_\<zeta>: "wt (Hd \<zeta>) = wt_sym f + the_enat (\<delta> * arity_sym f)"
    using exists_wt_sym by blast

  have "arity_sym f \<ge> arity_hd \<zeta>"
    by (rule ground_heads_arity[OF f_in_\<zeta>])
  hence "the_enat (\<delta> * arity_sym f) \<ge> arity_hd \<zeta>"
    using \<delta>_gt_0
    by (metis One_nat_def Suc_ile_eq dual_order.trans enat_ord_simps(2)
      enat_the_enat_\<delta>_times_arity_sym i0_lb mult.commute mult.right_neutral mult_left_mono
      one_enat_def)
  thus ?case
    unfolding wt_\<zeta> by (metis add.left_neutral add_mono le_iff_add plus_enat_simps(1) tm.sel(1))
next
  case App
  thus ?case
    by (metis dual_order.trans enat_ord_simps(1) head_App wt_App_ge_fun)
qed

lemma wt_ge_num_args_if_\<delta>_eq_0:
  assumes \<delta>_eq_0: "\<delta> = 0"
  shows "wt s \<ge> num_args s"
  by (induct s, simp_all,
    metis (no_types) \<delta>_eq_0 \<epsilon>_gt_0 wt_\<delta>_imp_\<delta>_eq_\<epsilon> add_le_same_cancel1 le_0_eq le_trans
      minus_nat.diff_0 not_gr_zero not_less_eq_eq)

lemma wt_ge_num_args: "wary s \<Longrightarrow> wt s \<ge> num_args s"
  using wt_ge_arity_head_if_\<delta>_gt_0 wt_ge_num_args_if_\<delta>_eq_0
  by (meson order.trans enat_ord_simps(1) neq0_conv wary_num_args_le_arity_head)


subsection \<open>Inductive Definitions\<close>

inductive gt :: "('s, 'v) tm \<Rightarrow> ('s, 'v) tm \<Rightarrow> bool" (infix ">\<^sub>t" 50) where
  gt_wt: "vars_mset t \<supseteq># vars_mset s \<Longrightarrow> wt t > wt s \<Longrightarrow> t >\<^sub>t s"
| gt_unary: "wt t = wt s \<Longrightarrow> \<not> head t \<le>\<ge>\<^sub>h\<^sub>d head s \<Longrightarrow> num_args t = 1 \<Longrightarrow>
    (\<exists>f \<in> ground_heads (head t). arity_sym f = 1 \<and> wt_sym f = 0) \<Longrightarrow> arg t >\<^sub>t s \<or> arg t = s \<Longrightarrow>
    t >\<^sub>t s"
| gt_diff: "vars_mset t \<supseteq># vars_mset s \<Longrightarrow> wt t = wt s \<Longrightarrow> head t >\<^sub>h\<^sub>d head s \<Longrightarrow> t >\<^sub>t s"
| gt_same: "vars_mset t \<supseteq># vars_mset s \<Longrightarrow> wt t = wt s \<Longrightarrow> head t = head s \<Longrightarrow>
    (\<forall>f \<in> ground_heads (head t). extf f (>\<^sub>t) (args t) (args s)) \<Longrightarrow> t >\<^sub>t s"

abbreviation ge :: "('s, 'v) tm \<Rightarrow> ('s, 'v) tm \<Rightarrow> bool" (infix "\<ge>\<^sub>t" 50) where
  "t \<ge>\<^sub>t s \<equiv> t >\<^sub>t s \<or> t = s"

inductive gt_wt :: "('s, 'v) tm \<Rightarrow> ('s, 'v) tm \<Rightarrow> bool" where
  gt_wtI: "vars_mset t \<supseteq># vars_mset s \<Longrightarrow> wt t > wt s \<Longrightarrow> gt_wt t s"

inductive gt_diff :: "('s, 'v) tm \<Rightarrow> ('s, 'v) tm \<Rightarrow> bool" where
  gt_diffI: "vars_mset t \<supseteq># vars_mset s \<Longrightarrow> wt t = wt s \<Longrightarrow> head t >\<^sub>h\<^sub>d head s \<Longrightarrow> gt_diff t s"

inductive gt_unary :: "('s, 'v) tm \<Rightarrow> ('s, 'v) tm \<Rightarrow> bool" where
  gt_unaryI: "wt t = wt s \<Longrightarrow> \<not> head t \<le>\<ge>\<^sub>h\<^sub>d head s \<Longrightarrow> num_args t = 1 \<Longrightarrow>
    (\<exists>f \<in> ground_heads (head t). arity_sym f = 1 \<and> wt_sym f = 0) \<Longrightarrow> arg t \<ge>\<^sub>t s \<Longrightarrow> gt_unary t s"

inductive gt_same :: "('s, 'v) tm \<Rightarrow> ('s, 'v) tm \<Rightarrow> bool" where
  gt_sameI: "vars_mset t \<supseteq># vars_mset s \<Longrightarrow> wt t = wt s \<Longrightarrow> head t = head s \<Longrightarrow>
    (\<forall>f \<in> ground_heads (head t). extf f (>\<^sub>t) (args t) (args s)) \<Longrightarrow> gt_same t s"

lemma gt_iff_wt_unary_diff_same: "t >\<^sub>t s \<longleftrightarrow> gt_wt t s \<or> gt_unary t s \<or> gt_diff t s \<or> gt_same t s"
  by (subst gt.simps) (auto simp: gt_wt.simps gt_unary.simps gt_diff.simps gt_same.simps)

lemma gt_imp_vars_mset: "t >\<^sub>t s \<Longrightarrow> vars_mset t \<supseteq># vars_mset s"
  by (induct rule: gt.induct) (auto intro: subset_mset.order.trans)

lemma gt_imp_vars: "t >\<^sub>t s \<Longrightarrow> vars t \<supseteq> vars s"
  using set_mset_mono[OF gt_imp_vars_mset] by simp


subsection \<open>Irreflexivity\<close>

theorem gt_irrefl: "wary s \<Longrightarrow> \<not> s >\<^sub>t s"
proof (induct "size s" arbitrary: s rule: less_induct)
  case less
  note ih = this(1) and wary_s = this(2)

  show ?case
  proof
    assume s_gt_s: "s >\<^sub>t s"
    show False
      using s_gt_s
    proof (cases rule: gt.cases)
      case gt_same
      then obtain f where f: "extf f (>\<^sub>t) (args s) (args s)"
        by fastforce
      thus False
        using wary_s ih by (metis wary_args extf_irrefl size_in_args)
    qed (auto simp: comp_hd_def gt_hd_irrefl)
  qed
qed


subsection \<open>Transitivity\<close>

lemma gt_imp_wt_ge: "t >\<^sub>t s \<Longrightarrow> wt t \<ge> wt s"
  by (induct rule: gt.induct) auto

lemma not_extf_gt_nil_singleton_if_\<delta>_eq_\<epsilon>:
  assumes wary_s: "wary s" and \<delta>_eq_\<epsilon>: "\<delta> = \<epsilon>"
  shows "\<not> extf f (>\<^sub>t) [] [s]"
proof
  assume nil_gt_s: "extf f (>\<^sub>t) [] [s]"
  note s_gt_nil = extf_singleton_nil_if_\<delta>_eq_\<epsilon>[OF \<delta>_eq_\<epsilon>, of f gt s]
  have "\<not> extf f (>\<^sub>t) [] []"
    by (rule extf_irrefl) simp
  moreover have "extf f (>\<^sub>t) [] []"
    using extf_trans_from_irrefl[of "{s}", OF _ _ _ _ _ _ nil_gt_s s_gt_nil] gt_irrefl[OF wary_s]
    by fastforce
  ultimately show False
    by sat
qed

lemma gt_sub_arg: "wary (App s t) \<Longrightarrow> App s t >\<^sub>t t"
proof (induct t arbitrary: s rule: measure_induct_rule[of size])
  case (less t)
  note ih = this(1) and wary_st = this(2)

  {
    assume wt_st: "wt (App s t) = wt t"
    hence \<delta>_eq_\<epsilon>: "\<delta> = \<epsilon>"
      using wt_App_\<delta> wt_\<delta>_imp_\<delta>_eq_\<epsilon> by metis
    hence \<delta>_gt_0: "\<delta> > 0"
      using \<epsilon>_gt_0 by simp

    have wt_s: "wt s = \<delta>"
      by (rule wt_App_\<delta>[OF wt_st])

    have
      wary_t: "wary t" and
      nargs_lt: "num_args s < arity_hd (head s)"
      using wary_st wary.simps by blast+

    have ary_hd_s: "arity_hd (head s) = 1"
      by (metis One_nat_def arity.wary_AppE dual_order.order_iff_strict eSuc_enat enat_defs(1)
        enat_defs(2) ileI1 linorder_not_le not_iless0 wary_st wt_gt_\<delta>_if_superunary wt_s)
    hence nargs_s: "num_args s = 0"
      by (metis enat_ord_simps(2) less_one nargs_lt one_enat_def)
    have "s = Hd (head s)"
      by (simp add: Hd_head_id nargs_s)
    then obtain f where
      f_in: "f \<in> ground_heads (head s)" and
      wt_f_etc: "wt_sym f + the_enat (\<delta> * arity_sym f) = \<delta>"
      using exists_wt_sym wt_s by fastforce

    have ary_f_1: "arity_sym f = 1"
    proof -
      have ary_f_ge_1: "arity_sym f \<ge> 1"
        using ary_hd_s f_in ground_heads_arity by fastforce
      hence "enat \<delta> * arity_sym f = \<delta>"
        using wt_f_etc by (metis enat_ord_simps(1) enat_the_enat_\<delta>_times_arity_sym le_add2
          le_antisym mult.right_neutral mult_left_mono zero_le)
      thus ?thesis
        using \<delta>_gt_0 by (cases "arity_sym f") (auto simp: one_enat_def)
    qed
    hence wt_f_0: "wt_sym f = 0"
      using wt_f_etc by simp

    {
      assume hd_s_ncmp_t: "\<not> head s \<le>\<ge>\<^sub>h\<^sub>d head t"
      have ?case
        by (rule gt_unary[OF wt_st]) (auto simp: hd_s_ncmp_t nargs_s intro: f_in ary_f_1 wt_f_0)
    }
    moreover
    {
      assume hd_s_gt_t: "head s >\<^sub>h\<^sub>d head t"
      have ?case
        by (rule gt_diff) (auto simp: hd_s_gt_t wt_s[folded \<delta>_eq_\<epsilon>])
    }
    moreover
    {
      assume "head t >\<^sub>h\<^sub>d head s"
      hence False
        using ary_f_1 exists_wt_sym f_in gt_hd_def gt_sym_antisym unary_wt_sym_0_gt wt_f_0 by blast
    }
    moreover
    {
      assume hd_t_eq_s: "head t = head s"
      hence nargs_t_le: "num_args t \<le> 1"
        using ary_hd_s wary_num_args_le_arity_head[OF wary_t] by (simp add: one_enat_def)

      have extf: "extf f (>\<^sub>t) [t] (args t)" for f
      proof (cases "args t")
        case Nil
        thus ?thesis
          by (simp add: extf_singleton_nil_if_\<delta>_eq_\<epsilon>[OF \<delta>_eq_\<epsilon>])
      next
        case args_t: (Cons ta ts)
        hence ts: "ts = []"
          using ary_hd_s[folded hd_t_eq_s] wary_num_args_le_arity_head[OF wary_t]
            nargs_t_le by simp
        have ta: "ta = arg t"
          by (metis apps.simps(1) apps.simps(2) args_t tm.sel(6) tm_collapse_apps ts)
        hence t: "t = App (fun t) ta"
          by (metis args.simps(1) args_t not_Cons_self2 tm.exhaust_sel ts)
        have "t >\<^sub>t ta"
          by (rule ih[of ta "fun t", folded t, OF _ wary_t]) (metis ta size_arg_lt t tm.disc(2))
        thus ?thesis
          unfolding args_t ts by (metis extf_singleton gt_irrefl wary_t)
      qed
      have ?case
        by (rule gt_same)
          (auto simp: hd_t_eq_s wt_s[folded \<delta>_eq_\<epsilon>] length_0_conv[THEN iffD1, OF nargs_s] extf)
    }
    ultimately have ?case
      unfolding comp_hd_def by metis
  }
  thus ?case
    using gt_wt by fastforce
qed

lemma gt_arg: "wary s \<Longrightarrow> is_App s \<Longrightarrow> s >\<^sub>t arg s"
  by (cases s) (auto intro: gt_sub_arg)

theorem gt_trans: "wary u \<Longrightarrow> wary t \<Longrightarrow> wary s \<Longrightarrow> u >\<^sub>t t \<Longrightarrow> t >\<^sub>t s \<Longrightarrow> u >\<^sub>t s"
proof (simp only: atomize_imp,
    rule measure_induct_rule[of "\<lambda>(u, t, s). {#size u, size t, size s#}"
        "\<lambda>(u, t, s). wary u \<longrightarrow> wary t \<longrightarrow> wary s \<longrightarrow> u >\<^sub>t t \<longrightarrow> t >\<^sub>t s \<longrightarrow> u >\<^sub>t s" "(u, t, s)",
      simplified prod.case],
    simp only: split_paired_all prod.case atomize_imp[symmetric])
  fix u t s
  assume
    ih: "\<And>ua ta sa. {#size ua, size ta, size sa#} < {#size u, size t, size s#} \<Longrightarrow>
      wary ua \<Longrightarrow> wary ta \<Longrightarrow> wary sa \<Longrightarrow> ua >\<^sub>t ta \<Longrightarrow> ta >\<^sub>t sa \<Longrightarrow> ua >\<^sub>t sa" and
    wary_u: "wary u" and wary_t: "wary t" and wary_s: "wary s" and
    u_gt_t: "u >\<^sub>t t" and t_gt_s: "t >\<^sub>t s"

  have "vars_mset u \<supseteq># vars_mset t" and "vars_mset t \<supseteq># vars_mset s"
    using u_gt_t t_gt_s by (auto simp: gt_imp_vars_mset)
  hence vars_u_s: "vars_mset u \<supseteq># vars_mset s"
    by auto

  have wt_u_ge_t: "wt u \<ge> wt t" and wt_t_ge_s: "wt t \<ge> wt s"
    using gt_imp_wt_ge u_gt_t t_gt_s by auto

  {
    assume wt_t_s: "wt t = wt s" and wt_u_t: "wt u = wt t"
    hence wt_u_s: "wt u = wt s"
      by simp

    have wary_arg_u: "wary (arg u)"
      by (rule wary_arg[OF wary_u])
    have wary_arg_t: "wary (arg t)"
      by (rule wary_arg[OF wary_t])
    have wary_arg_s: "wary (arg s)"
      by (rule wary_arg[OF wary_s])

    have "u >\<^sub>t s"
      using t_gt_s
    proof cases
      case gt_unary_t_s: gt_unary

      have t_app: "is_App t"
        by (metis args_Nil_iff_is_Hd gt_unary_t_s(3) length_greater_0_conv less_numeral_extra(1))

      have \<delta>_eq_\<epsilon>: "\<delta> = \<epsilon>"
        using gt_unary_t_s(4) unary_wt_sym_0_imp_\<delta>_eq_\<epsilon> by blast

      show ?thesis
        using u_gt_t
      proof cases
        case gt_unary_u_t: gt_unary
        have u_app: "is_App u"
          by (metis args_Nil_iff_is_Hd gt_unary_u_t(3) length_greater_0_conv less_numeral_extra(1))
        hence arg_u_gt_s: "arg u >\<^sub>t s"
          using ih[of "arg u" t s] gt_unary_u_t(5) t_gt_s size_arg_lt wary_arg_u wary_s wary_t
          by force
        hence arg_u_ge_s: "arg u \<ge>\<^sub>t s"
          by sat

        {
          assume "size (arg u) < size t"
          hence ?thesis
            using ih[of u "arg u" s] arg_u_gt_s gt_arg by (simp add: u_app wary_arg_u wary_s wary_u)
        }
        moreover
        {
          assume "size (arg t) < size s"
          hence "u >\<^sub>t arg t"
            using ih[of u t "arg t"] args_Nil_iff_is_Hd gt_arg gt_unary_t_s(3) u_gt_t wary_t wary_u
            by force
          hence ?thesis
            using ih[of u "arg t" s] args_Nil_iff_is_Hd gt_unary_t_s(3,5) size_arg_lt wary_arg_t
              wary_s wary_u by force
        }
        moreover
        {
          assume sz_u_gt_t: "size u > size t" and sz_t_gt_s: "size t > size s"

          have wt_fun_u: "wt (fun u) = \<delta>"
            by (metis antisym gt_imp_wt_ge gt_unary_u_t(5) tm.collapse(2) u_app wt_App_\<delta> wt_arg_le
              wt_t_s wt_u_s)

          have nargs_fun_u: "num_args (fun u) = 0"
            by (metis args.simps(1) gt_unary_u_t(3) list.size(3) one_arg_imp_Hd tm.collapse(2)
              u_app)

          {
            assume hd_u_eq_s: "head u = head s"
            hence ary_hd_s: "arity_hd (head s) = 1"
              using ground_heads_arity gt_unary_u_t(3,4) hd_u_eq_s one_enat_def
                wary_num_args_le_arity_head wary_u by fastforce

            have extf: "extf f (>\<^sub>t) (args u) (args s)" for f
            proof (cases "args s")
              case Nil
              thus ?thesis
                by (metis Hd_head_id \<delta>_eq_\<epsilon> append_Nil args.simps(2) extf_singleton_nil_if_\<delta>_eq_\<epsilon>
                  gt_unary_u_t(3) head_fun length_greater_0_conv less_irrefl_nat nargs_fun_u
                  tm.exhaust_sel zero_neq_one)
            next
              case args_s: (Cons sa ss)
              hence ss: "ss = []"
                by (cases s, simp, metis One_nat_def antisym_conv ary_hd_s diff_Suc_1
                  enat_ord_simps(1) le_add2 length_0_conv length_Cons list.size(4) one_enat_def
                  wary_num_args_le_arity_head wary_s)
              have sa: "sa = arg s"
                by (metis apps.simps(1) apps.simps(2) args_s tm.sel(6) tm_collapse_apps ss)

              have s_app: "is_App s"
                using args_Nil_iff_is_Hd args_s by force
              have args_u: "args u = [arg u]"
                by (metis append_Nil args.simps(2) args_Nil_iff_is_Hd gt_unary_u_t(3) length_0_conv
                  nargs_fun_u tm.collapse(2) zero_neq_one)

              have max_sz_u_t_s: "Max {size s, size t, size u} = size u"
                using sz_t_gt_s sz_u_gt_t by auto

              have max_sz_arg_u_t_arg_t: "Max {size (arg t), size t, size (arg u)} < size u"
                using size_arg_lt sz_u_gt_t t_app u_app by fastforce

              have "{#size (arg u), size t, size (arg t)#} < {#size u, size t, size s#}"
                using max_sz_arg_u_t_arg_t
                by (simp add: Max_lt_imp_lt_mset insert_commute max_sz_u_t_s)
              hence arg_u_gt_arg_t: "arg u >\<^sub>t arg t"
                using ih[OF _ wary_arg_u wary_t wary_arg_t] args_Nil_iff_is_Hd gt_arg
                  gt_unary_t_s(3) gt_unary_u_t(5) wary_t by force

              have max_sz_arg_s_s_arg_t: "Max {size (arg s), size s, size (arg t)} < size u"
                using s_app t_app size_arg_lt sz_t_gt_s sz_u_gt_t by force

              have "{#size (arg t), size s, size (arg s)#} < {#size u, size t, size s#}"
                by (meson add_mset_lt_lt_lt less_trans mset_lt_single_iff s_app size_arg_lt
                  sz_t_gt_s sz_u_gt_t t_app)
              hence arg_t_gt_arg_s: "arg t >\<^sub>t arg s"
                using ih[OF _ wary_arg_t wary_s wary_arg_s]
                  gt_unary_t_s(5) gt_arg args_Nil_iff_is_Hd args_s wary_s by force

              have "arg u >\<^sub>t arg s"
                using ih[of "arg u" "arg t" "arg s"] arg_u_gt_arg_t arg_t_gt_arg_s
                by (simp add: add_mset_lt_le_lt less_imp_le_nat s_app size_arg_lt t_app u_app
                  wary_arg_s wary_arg_t wary_arg_u)
              thus ?thesis
                unfolding args_u args_s ss sa by (metis extf_singleton gt_irrefl wary_arg_u)
            qed

            have ?thesis
              by (rule gt_same[OF vars_u_s wt_u_s hd_u_eq_s]) (simp add: extf)
          }
          moreover
          {
            assume "head u >\<^sub>h\<^sub>d head s"
            hence ?thesis
              by (rule gt_diff[OF vars_u_s wt_u_s])
          }
          moreover
          {
            assume "head s >\<^sub>h\<^sub>d head u"
            hence False
              using gt_hd_def gt_hd_irrefl gt_sym_antisym gt_unary_u_t(4) unary_wt_sym_0_gt by blast
          }
          moreover
          {
            assume "\<not> head u \<le>\<ge>\<^sub>h\<^sub>d head s"
            hence ?thesis
              by (rule gt_unary[OF wt_u_s _ gt_unary_u_t(3,4) arg_u_ge_s])
          }
          ultimately have ?thesis
            unfolding comp_hd_def by sat
        }
        ultimately show ?thesis
          by (metis args_Nil_iff_is_Hd dual_order.strict_trans2 gt_unary_t_s(3) gt_unary_u_t(3)
            length_0_conv not_le_imp_less size_arg_lt zero_neq_one)
      next
        case gt_diff_u_t: gt_diff
        have False
          using gt_diff_u_t(3) gt_hd_def gt_hd_irrefl gt_sym_antisym gt_unary_t_s(4)
            unary_wt_sym_0_gt by blast
        thus ?thesis
          by sat
      next
        case gt_same_u_t: gt_same

        have hd_u_ncomp_s: "\<not> head u \<le>\<ge>\<^sub>h\<^sub>d head s"
          by (rule gt_unary_t_s(2)[folded gt_same_u_t(3)])

        have "num_args u \<le> 1"
          by (metis enat_ord_simps(1) ground_heads_arity gt_same_u_t(3) gt_unary_t_s(4) one_enat_def
            order_trans wary_num_args_le_arity_head wary_u)
        hence nargs_u: "num_args u = 1"
          by (cases "args u",
            metis Hd_head_id \<delta>_eq_\<epsilon> append_Nil args.simps(2) gt_same_u_t(3,4) gt_unary_t_s(3,4)
              head_fun list.size(3) not_extf_gt_nil_singleton_if_\<delta>_eq_\<epsilon> one_arg_imp_Hd
              tm.collapse(2)[OF t_app] wary_arg_t,
            simp)

        have "arg u >\<^sub>t arg t"
          by (metis extf_singleton[THEN iffD1] append_Nil args.simps args_Nil_iff_is_Hd
            comp_hd_def gt_hd_def gt_irrefl gt_same_u_t(3,4) gt_unary_t_s(2,3) head_fun
            length_0_conv nargs_u one_arg_imp_Hd t_app tm.collapse(2) u_gt_t wary_u)
        hence "arg u >\<^sub>t s"
          using ih[OF _ wary_arg_u wary_arg_t wary_s] gt_unary_t_s(5)
          by (metis add_mset_lt_left_lt add_mset_lt_lt_lt args_Nil_iff_is_Hd list.size(3) nargs_u
            size_arg_lt t_app zero_neq_one)
        hence arg_u_ge_s: "arg u \<ge>\<^sub>t s"
          by sat
        show ?thesis
          by (rule gt_unary[OF wt_u_s hd_u_ncomp_s nargs_u _ arg_u_ge_s])
            (simp add: gt_same_u_t(3) gt_unary_t_s(4))
      qed (simp add: wt_u_t)
    next
      case gt_diff_t_s: gt_diff
      show ?thesis
        using u_gt_t
      proof cases
        case gt_unary_u_t: gt_unary
        have "is_App u"
          by (metis args_Nil_iff_is_Hd gt_unary_u_t(3) length_greater_0_conv less_numeral_extra(1))
        hence "arg u >\<^sub>t s"
          using ih[of "arg u" t s] gt_unary_u_t(5) t_gt_s size_arg_lt wary_arg_u wary_s wary_t
          by force
        hence arg_u_ge_s: "arg u \<ge>\<^sub>t s"
          by sat

        {
          assume "head u = head s"
          hence False
            using gt_diff_t_s(3) gt_unary_u_t(2) unfolding comp_hd_def by force
        }
        moreover
        {
          assume "head s >\<^sub>h\<^sub>d head u"
          hence False
            using gt_hd_def gt_hd_irrefl gt_sym_antisym gt_unary_u_t(4) unary_wt_sym_0_gt by blast
        }
        moreover
        {
          assume "head u >\<^sub>h\<^sub>d head s"
          hence ?thesis
            by (rule gt_diff[OF vars_u_s wt_u_s])
        }
        moreover
        {
          assume "\<not> head u \<le>\<ge>\<^sub>h\<^sub>d head s"
          hence ?thesis
            by (rule gt_unary[OF wt_u_s _ gt_unary_u_t(3,4) arg_u_ge_s])
        }
        ultimately show ?thesis
          unfolding comp_hd_def by sat
      next
        case gt_diff_u_t: gt_diff
        have "head u >\<^sub>h\<^sub>d head s"
          using gt_diff_u_t(3) gt_diff_t_s(3) gt_hd_trans by blast
        thus ?thesis
          by (rule gt_diff[OF vars_u_s wt_u_s])
      next
        case gt_same_u_t: gt_same
        have "head u >\<^sub>h\<^sub>d head s"
          using gt_diff_t_s(3) gt_same_u_t(3) by simp
        thus ?thesis
          by (rule gt_diff[OF vars_u_s wt_u_s])
      qed (simp add: wt_u_t)
    next
      case gt_same_t_s: gt_same
      show ?thesis
        using u_gt_t
      proof cases
        case gt_unary_u_t: gt_unary
        have "is_App u"
          by (metis args_Nil_iff_is_Hd gt_unary_u_t(3) length_greater_0_conv less_numeral_extra(1))
        hence "arg u >\<^sub>t s"
          using ih[of "arg u" t s] gt_unary_u_t(5) t_gt_s size_arg_lt wary_arg_u wary_s wary_t
          by force
        hence arg_u_ge_s: "arg u \<ge>\<^sub>t s"
          by sat

        have "\<not> head u \<le>\<ge>\<^sub>h\<^sub>d head s"
          using gt_same_t_s(3) gt_unary_u_t(2) by simp
        thus ?thesis
          by (rule gt_unary[OF wt_u_s _ gt_unary_u_t(3,4) arg_u_ge_s])
      next
        case gt_diff_u_t: gt_diff
        have "head u >\<^sub>h\<^sub>d head s"
          using gt_diff_u_t(3) gt_same_t_s(3) by simp
        thus ?thesis
          by (rule gt_diff[OF vars_u_s wt_u_s])
      next
        case gt_same_u_t: gt_same
        have hd_u_s: "head u = head s"
          by (simp only: gt_same_t_s(3) gt_same_u_t(3))

        let ?S = "set (args u) \<union> set (args t) \<union> set (args s)"

        have gt_trans_args: "\<forall>ua \<in> ?S. \<forall>ta \<in> ?S. \<forall>sa \<in> ?S. ua >\<^sub>t ta \<longrightarrow> ta >\<^sub>t sa \<longrightarrow> ua >\<^sub>t sa"
        proof clarify
          fix sa ta ua
          assume
            ua_in: "ua \<in> ?S" and ta_in: "ta \<in> ?S" and sa_in: "sa \<in> ?S" and
            ua_gt_ta: "ua >\<^sub>t ta" and ta_gt_sa: "ta >\<^sub>t sa"
          have wary_sa: "wary sa" and wary_ta: "wary ta" and wary_ua: "wary ua"
            using wary_args ua_in ta_in sa_in wary_u wary_t wary_s by blast+
          show "ua >\<^sub>t sa"
            by (auto intro!: ih[OF Max_lt_imp_lt_mset wary_ua wary_ta wary_sa ua_gt_ta ta_gt_sa])
              (meson ua_in ta_in sa_in Un_iff max.strict_coboundedI1 max.strict_coboundedI2
                 size_in_args)+
        qed
        have "\<forall>f \<in> ground_heads (head u). extf f (>\<^sub>t) (args u) (args s)"
          by (clarify, rule extf_trans_from_irrefl[of ?S _ "args t", OF _ _ _ _ _ gt_trans_args])
            (auto simp: gt_same_u_t(3,4) gt_same_t_s(4) wary_args wary_u wary_t wary_s gt_irrefl)
        thus ?thesis
          by (rule gt_same[OF vars_u_s wt_u_s hd_u_s])
      qed (simp add: wt_u_t)
    qed (simp add: wt_t_s)
  }
  thus "u >\<^sub>t s"
    using vars_u_s wt_t_ge_s wt_u_ge_t by (force intro: gt_wt)
qed

lemma gt_antisym: "wary s \<Longrightarrow> wary t \<Longrightarrow> t >\<^sub>t s \<Longrightarrow> \<not> s >\<^sub>t t"
  using gt_irrefl gt_trans by blast


subsection \<open>Subterm Property\<close>

lemma gt_sub_fun: "App s t >\<^sub>t s"
proof (cases "wt (App s t) > wt s")
  case True
  thus ?thesis
    using gt_wt by simp
next
  case False
  hence wt_st: "wt (App s t) = wt s"
    by (meson order.antisym not_le_imp_less wt_App_ge_fun)
  hence \<delta>_eq_\<epsilon>: "\<delta> = \<epsilon>"
    by (metis add_diff_cancel_left' diff_diff_cancel wt_\<delta>_imp_\<delta>_eq_\<epsilon> wt_ge_\<delta> wt.simps(2))

  have vars_st: "vars_mset (App s t) \<supseteq># vars_mset s"
    by auto
  have hd_st: "head (App s t) = head s"
    by auto
  have extf: "\<forall>f \<in> ground_heads (head (App s t)). extf f (>\<^sub>t) (args (App s t)) (args s)"
    by (simp add: \<delta>_eq_\<epsilon> extf_snoc_if_\<delta>_eq_\<epsilon>)
  show ?thesis
    by (rule gt_same[OF vars_st wt_st hd_st extf])
qed

theorem gt_proper_sub: "wary t \<Longrightarrow> proper_sub s t \<Longrightarrow> t >\<^sub>t s"
  by (induct t) (auto intro: gt_sub_fun gt_sub_arg gt_trans sub.intros wary_sub)


subsection \<open>Compatibility with Functions\<close>

theorem gt_compat_fun:
  assumes
    wary_t: "wary t" and
    t'_gt_t: "t' >\<^sub>t t"
  shows "App s t' >\<^sub>t App s t"
proof -
  have vars_st': "vars_mset (App s t') \<supseteq># vars_mset (App s t)"
    by (simp add: t'_gt_t gt_imp_vars_mset)

  show ?thesis
  proof (cases "wt t' > wt t")
    case True
    hence wt_st': "wt (App s t') > wt (App s t)"
      by (simp only: wt.simps)
    show ?thesis
      by (rule gt_wt[OF vars_st' wt_st'])
  next
    case False
    hence "wt t' = wt t"
      using t'_gt_t gt_imp_wt_ge order.not_eq_order_implies_strict by fastforce
    hence wt_st': "wt (App s t') = wt (App s t)"
      by (simp only: wt.simps)

    have head_st': "head (App s t') = head (App s t)"
      by simp

    have extf: "\<And>f. extf f (>\<^sub>t) (args s @ [t']) (args s @ [t])"
      using t'_gt_t by (metis extf_compat_list gt_irrefl[OF wary_t])

    show ?thesis
      by (rule gt_same[OF vars_st' wt_st' head_st']) (simp add: extf)
  qed
qed


subsection \<open>Compatibility with Arguments\<close>

theorem gt_compat_arg:
  assumes wary_s't: "wary (App s' t)" and s'_gt_s: "s' >\<^sub>t s"
  shows "App s' t >\<^sub>t App s t"
proof -
  have vars_s't: "vars_mset (App s' t) \<supseteq># vars_mset (App s t)"
    by (simp add: s'_gt_s gt_imp_vars_mset)
  show ?thesis
    using s'_gt_s
  proof cases
    case gt_wt_s'_s: gt_wt
    have "wt (App s' t) > wt (App s t)"
      by (simp add: wt_ge_\<delta>) (metis add_diff_assoc add_less_cancel_right gt_wt_s'_s(2) wt_ge_\<delta>)
    thus ?thesis
      by (rule gt_wt[OF vars_s't])
  next
    case gt_unary_s'_s: gt_unary
    have False
      by (metis ground_heads_arity gt_unary_s'_s(3) gt_unary_s'_s(4) leD one_enat_def wary_AppE
        wary_s't)
    thus ?thesis
      by sat
  next
    case _: gt_diff
    thus ?thesis
      by (simp add: gt_diff)
  next
    case gt_same_s'_s: gt_same
    have wt_s't: "wt (App s' t) = wt (App s t)"
      by (simp add: gt_same_s'_s(2))
    have hd_s't: "head (App s' t) = head (App s t)"
      by (simp add: gt_same_s'_s(3))
    have "\<forall>f \<in> ground_heads (head (App s' t)). extf f (>\<^sub>t) (args (App s' t)) (args (App s t))"
      using gt_same_s'_s(4) by (auto intro: extf_compat_append_right)
    thus ?thesis
      by (rule gt_same[OF vars_s't wt_s't hd_s't])
  qed
qed


subsection \<open>Stability under Substitution\<close>

definition extra_wt :: "('v \<Rightarrow> ('s, 'v) tm) \<Rightarrow> ('s, 'v) tm \<Rightarrow> nat" where
  "extra_wt \<rho> s = (\<Sum>x \<in># vars_mset s. wt (\<rho> x) - wt (Hd (Var x)))"

lemma
  extra_wt_Var[simp]: "extra_wt \<rho> (Hd (Var x)) = wt (\<rho> x) - wt (Hd (Var x))" and
  extra_wt_Sym[simp]: "extra_wt \<rho> (Hd (Sym f)) = 0" and
  extra_wt_App[simp]: "extra_wt \<rho> (App s t) = extra_wt \<rho> s + extra_wt \<rho> t"
  unfolding extra_wt_def by simp+

lemma extra_wt_subseteq:
  assumes vars_s: "vars_mset t \<supseteq># vars_mset s"
  shows "extra_wt \<rho> t \<ge> extra_wt \<rho> s"
proof (unfold extra_wt_def)
  let ?diff = "\<lambda>v. wt (\<rho> v) - wt (Hd (Var v))"

  have "vars_mset s + (vars_mset t - vars_mset s) = vars_mset t"
    using vars_s by (meson subset_mset.add_diff_inverse)
  hence "{#?diff v. v \<in># vars_mset t#} =
    {#?diff v. v \<in># vars_mset s#} + {#?diff v. v \<in># vars_mset t - vars_mset s#}"
    by (metis image_mset_union)
  thus "(\<Sum>v \<in># vars_mset t. ?diff v) \<ge> (\<Sum>v \<in># vars_mset s. ?diff v)"
    by simp
qed

lemma wt_subst:
  assumes wary_\<rho>: "wary_subst \<rho>" and wary_s: "wary s"
  shows "wt (subst \<rho> s) = wt s + extra_wt \<rho> s"
  using wary_s
proof (induct s rule: tm.induct)
  case \<zeta>: (Hd \<zeta>)
  show ?case
  proof (cases \<zeta>)
    case x: (Var x)

    let ?\<xi> = "head (\<rho> x)"

    obtain g where
      g_in_grs_\<xi>: "g \<in> ground_heads ?\<xi>" and
      wt_\<xi>: "wt (Hd ?\<xi>) = wt_sym g + the_enat (\<delta> * arity_sym g)"
      using exists_wt_sym by blast
    have "g \<in> ground_heads \<zeta>"
      using x g_in_grs_\<xi> wary_\<rho> wary_subst_def by auto
    hence wt_\<rho>x_ge: "wt (\<rho> x) \<ge> wt (Hd \<zeta>)"
      by (metis (full_types) dual_order.trans wt_le_wt_sym wt_\<xi> wt_hd_le)
    thus ?thesis
      using x by (simp add: extra_wt_def)
  qed auto
next
  case (App s t)
  note ih_s = this(1) and ih_t = this(2) and wary_st = this(3)
  have "wary s"
    using wary_st by (meson wary_AppE)
  hence "\<And>n. extra_wt \<rho> s + (wt s - \<delta> + n) = wt (subst \<rho> s) - \<delta> + n"
    using ih_s by (metis (full_types) add_diff_assoc2 ab_semigroup_add_class.add_ac(1)
      add.left_commute wt_ge_\<delta>)
  hence "extra_wt \<rho> s + (wt s + wt t - \<delta> + extra_wt \<rho> t) = wt (subst \<rho> s) + wt (subst \<rho> t) - \<delta>"
    using ih_t wary_st
    by (metis (no_types) add_diff_assoc2 ab_semigroup_add_class.add_ac(1) wary_AppE wt_ge_\<delta>)
  thus ?case
    by (simp add: wt_ge_\<delta>)
qed

theorem gt_subst:
  assumes wary_\<rho>: "wary_subst \<rho>"
  shows "wary t \<Longrightarrow> wary s \<Longrightarrow> t >\<^sub>t s \<Longrightarrow> subst \<rho> t >\<^sub>t subst \<rho> s"
proof (simp only: atomize_imp,
    rule measure_induct_rule[of "\<lambda>(t, s). {#size t, size s#}"
        "\<lambda>(t, s). wary t \<longrightarrow> wary s \<longrightarrow> t >\<^sub>t s \<longrightarrow> subst \<rho> t >\<^sub>t subst \<rho> s" "(t, s)",
      simplified prod.case],
    simp only: split_paired_all prod.case atomize_imp[symmetric])
  fix t s
  assume
    ih: "\<And>ta sa. {#size ta, size sa#} < {#size t, size s#} \<Longrightarrow> wary ta \<Longrightarrow> wary sa \<Longrightarrow> ta >\<^sub>t sa \<Longrightarrow>
      subst \<rho> ta >\<^sub>t subst \<rho> sa" and
    wary_t: "wary t" and wary_s: "wary s" and t_gt_s: "t >\<^sub>t s"

  show "subst \<rho> t >\<^sub>t subst \<rho> s"
  proof (cases "wt (subst \<rho> t) = wt (subst \<rho> s)")
    case wt_\<rho>t_ne_\<rho>s: False

    have vars_s: "vars_mset t \<supseteq># vars_mset s"
      by (simp add: t_gt_s gt_imp_vars_mset)
    hence vars_\<rho>s: "vars_mset (subst \<rho> t) \<supseteq># vars_mset (subst \<rho> s)"
      by (rule vars_mset_subst_subseteq)

    have wt_t_ge_s: "wt t \<ge> wt s"
      by (simp add: gt_imp_wt_ge t_gt_s)

    have "wt (subst \<rho> t) > wt (subst \<rho> s)"
      using wt_\<rho>t_ne_\<rho>s unfolding wt_subst[OF wary_\<rho> wary_s] wt_subst[OF wary_\<rho> wary_t]
      by (metis add_le_cancel_left add_less_le_mono extra_wt_subseteq
        order.not_eq_order_implies_strict vars_s wt_t_ge_s)
    thus ?thesis
      by (rule gt_wt[OF vars_\<rho>s])
  next
    case wt_\<rho>t_eq_\<rho>s: True
    show ?thesis
      using t_gt_s
    proof cases
      case gt_wt
      hence False
        using wt_\<rho>t_eq_\<rho>s wary_s wary_t
        by (metis add_diff_cancel_right' diff_le_mono2 extra_wt_subseteq wt_subst leD wary_\<rho>)
      thus ?thesis
        by sat
    next
      case gt_unary

      have wary_\<rho>t: "wary (subst \<rho> t)"
        by (simp add: wary_subst_wary wary_t wary_\<rho>)

      show ?thesis
      proof (cases t)
        case Hd
        hence False
          using gt_unary(3) by simp
        thus ?thesis
          by sat
      next
        case t: (App t1 t2)
        hence t2: "t2 = arg t"
          by simp
        hence wary_t2: "wary t2"
          using wary_t by blast

        show ?thesis
        proof (cases "t2 = s")
          case True
          moreover have "subst \<rho> t >\<^sub>t subst \<rho> t2"
            using gt_sub_arg wary_\<rho>t unfolding t by simp
          ultimately show ?thesis
            by simp
        next
          case t2_ne_s: False
          hence t2_gt_s: "t2 >\<^sub>t s"
            using gt_unary(5) t2 by blast

          have "subst \<rho> t2 >\<^sub>t subst \<rho> s"
            by (rule ih[OF _ wary_t2 wary_s t2_gt_s]) (simp add: t)
          thus ?thesis
            by (metis gt_sub_arg gt_trans subst.simps(2) t wary_\<rho> wary_\<rho>t wary_s wary_subst_wary
              wary_t2)
        qed
      qed
    next
      case _: gt_diff
      note vars_s = this(1) and hd_t_gt_hd_s = this(3)
      have vars_\<rho>s: "vars_mset (subst \<rho> t) \<supseteq># vars_mset (subst \<rho> s)"
        by (rule vars_mset_subst_subseteq[OF vars_s])

      have "head (subst \<rho> t) >\<^sub>h\<^sub>d head (subst \<rho> s)"
        by (meson hd_t_gt_hd_s wary_subst_ground_heads gt_hd_def rev_subsetD wary_\<rho>)
      thus ?thesis
        by (rule gt_diff[OF vars_\<rho>s wt_\<rho>t_eq_\<rho>s])
    next
      case _: gt_same
      note vars_s = this(1) and hd_s_eq_hd_t = this(3) and extf = this(4)

      have vars_\<rho>s: "vars_mset (subst \<rho> t) \<supseteq># vars_mset (subst \<rho> s)"
        by (rule vars_mset_subst_subseteq[OF vars_s])
      have hd_\<rho>t: "head (subst \<rho> t) = head (subst \<rho> s)"
        by (simp add: hd_s_eq_hd_t)

      {
        fix f
        assume f_in_grs: "f \<in> ground_heads (head (subst \<rho> t))"

        let ?S = "set (args t) \<union> set (args s)"

        have extf_args_s_t: "extf f (>\<^sub>t) (args t) (args s)"
          using extf f_in_grs wary_subst_ground_heads wary_\<rho> by blast
        have "extf f (>\<^sub>t) (map (subst \<rho>) (args t)) (map (subst \<rho>) (args s))"
        proof (rule extf_map[of ?S, OF _ _ _ _ _ _ extf_args_s_t])
          show "\<forall>x \<in> ?S. \<not> subst \<rho> x >\<^sub>t subst \<rho> x"
            using gt_irrefl wary_t wary_s wary_args wary_\<rho> wary_subst_wary by fastforce
        next
          show "\<forall>z \<in> ?S. \<forall>y \<in> ?S. \<forall>x \<in> ?S. subst \<rho> z >\<^sub>t subst \<rho> y \<longrightarrow> subst \<rho> y >\<^sub>t subst \<rho> x \<longrightarrow>
            subst \<rho> z >\<^sub>t subst \<rho> x"
            using gt_trans wary_t wary_s wary_args wary_\<rho> wary_subst_wary by (metis Un_iff)
        next
          have sz_a: "\<forall>ta \<in> ?S. \<forall>sa \<in> ?S. {#size ta, size sa#} < {#size t, size s#}"
            by (fastforce intro: Max_lt_imp_lt_mset dest: size_in_args)
          show "\<forall>y \<in> ?S. \<forall>x \<in> ?S. y >\<^sub>t x \<longrightarrow> subst \<rho> y >\<^sub>t subst \<rho> x"
            using ih sz_a size_in_args wary_t wary_s wary_args wary_\<rho> wary_subst_wary by fastforce
        qed auto
        hence "extf f (>\<^sub>t) (args (subst \<rho> t)) (args (subst \<rho> s))"
          by (auto simp: hd_s_eq_hd_t intro: extf_compat_append_left)
      }
      hence "\<forall>f \<in> ground_heads (head (subst \<rho> t)).
        extf f (>\<^sub>t) (args (subst \<rho> t)) (args (subst \<rho> s))"
        by blast
      thus ?thesis
        by (rule gt_same[OF vars_\<rho>s wt_\<rho>t_eq_\<rho>s hd_\<rho>t])
    qed
  qed
qed


subsection \<open>Totality on Ground Terms\<close>

theorem gt_total_ground:
  assumes extf_total: "\<And>f. ext_total (extf f)"
  shows "ground t \<Longrightarrow> ground s \<Longrightarrow> t >\<^sub>t s \<or> s >\<^sub>t t \<or> t = s"
proof (simp only: atomize_imp,
    rule measure_induct_rule[of "\<lambda>(t, s). {# size t, size s #}"
      "\<lambda>(t, s). ground t \<longrightarrow> ground s \<longrightarrow> t >\<^sub>t s \<or> s >\<^sub>t t \<or> t = s" "(t, s)", simplified prod.case],
    simp only: split_paired_all prod.case atomize_imp[symmetric])
  fix t s :: "('s, 'v) tm"
  assume
    ih: "\<And>ta sa. {# size ta, size sa #} < {# size t, size s #} \<Longrightarrow> ground ta \<Longrightarrow> ground sa \<Longrightarrow>
      ta >\<^sub>t sa \<or> sa >\<^sub>t ta \<or> ta = sa" and
    gr_t: "ground t" and gr_s: "ground s"

  let ?case = "t >\<^sub>t s \<or> s >\<^sub>t t \<or> t = s"

  have
    vars_t: "vars_mset t \<supseteq># vars_mset s" and
    vars_s: "vars_mset s \<supseteq># vars_mset t"
    by (simp only: vars_mset_empty_iff[THEN iffD2, OF gr_s]
      vars_mset_empty_iff[THEN iffD2, OF gr_t])+

  show ?case
  proof (cases "wt t = wt s")
    case False
    moreover
    {
      assume "wt t > wt s"
      hence "t >\<^sub>t s"
        by (rule gt_wt[OF vars_t])
    }
    moreover
    {
      assume "wt s > wt t"
      hence "s >\<^sub>t t"
        by (rule gt_wt[OF vars_s])
    }
    ultimately show ?thesis
      by linarith
  next
    case wt_t: True
    note wt_s = wt_t[symmetric]

    obtain g where \<xi>: "head t = Sym g"
      by (metis ground_head[OF gr_t] hd.collapse(2))
    obtain f where \<zeta>: "head s = Sym f"
      by (metis ground_head[OF gr_s] hd.collapse(2))

    {
      assume g_gt_f: "g >\<^sub>s f"
      have "t >\<^sub>t s"
        by (rule gt_diff[OF vars_t wt_t]) (simp add: \<xi> \<zeta> g_gt_f gt_hd_def)
    }
    moreover
    {
      assume f_gt_g: "f >\<^sub>s g"
      have "s >\<^sub>t t"
        by (rule gt_diff[OF vars_s wt_s]) (simp add: \<xi> \<zeta> f_gt_g gt_hd_def)
    }
    moreover
    {
      assume g_eq_f: "g = f"
      hence hd_t: "head t = head s"
        using \<xi> \<zeta> by force
      note hd_s = hd_t[symmetric]

      have gr_ts: "\<forall>t \<in> set (args t). ground t"
        using gr_t ground_args by auto
      have gr_ss: "\<forall>s \<in> set (args s). ground s"
        using gr_s ground_args by auto

      let ?ts = "args t"
      let ?ss = "args s"

      have ?thesis
      proof (cases "?ts = ?ss")
        case ts_eq_ss: True
        show ?thesis
          using \<xi> \<zeta> g_eq_f ts_eq_ss by (simp add: tm_expand_apps)
      next
        case False
        hence "extf g (>\<^sub>t) (args t) ?ss \<or> extf g (>\<^sub>t) ?ss ?ts"
          using ih gr_ss gr_ts
            ext_total.total[OF extf_total, rule_format, of "set ?ts \<union> set ?ss" "(>\<^sub>t)" ?ts ?ss g]
          by (metis Un_commute Un_iff in_lists_iff_set less_multiset_doubletons size_in_args sup_ge2)
        moreover
        {
          assume extf: "extf g (>\<^sub>t) ?ts ?ss"
          have "t >\<^sub>t s"
            by (rule gt_same[OF vars_t wt_t hd_t]) (simp add: extf \<xi>)
        }
        moreover
        {
          assume extf: "extf g (>\<^sub>t) ?ss ?ts"
          have "s >\<^sub>t t"
            by (rule gt_same[OF vars_s wt_s hd_s]) (simp add: extf[unfolded g_eq_f] \<zeta>)
        }
        ultimately show ?thesis
          by sat
      qed
    }
    ultimately show ?thesis
      using gt_sym_total by blast
  qed
qed


subsection \<open>Well-foundedness\<close>

abbreviation gtw :: "('s, 'v) tm \<Rightarrow> ('s, 'v) tm \<Rightarrow> bool" (infix ">\<^sub>t\<^sub>w" 50) where
  "(>\<^sub>t\<^sub>w) \<equiv> \<lambda>t s. wary t \<and> wary s \<and> t >\<^sub>t s"

abbreviation gtwg :: "('s, 'v) tm \<Rightarrow> ('s, 'v) tm \<Rightarrow> bool" (infix ">\<^sub>t\<^sub>w\<^sub>g" 50) where
  "(>\<^sub>t\<^sub>w\<^sub>g) \<equiv> \<lambda>t s. ground t \<and> t >\<^sub>t\<^sub>w s"

lemma ground_gt_unary:
  assumes gr_t: "ground t"
  shows "\<not> gt_unary t s"
proof
  assume gt_unary_t_s: "gt_unary t s"
  hence "t >\<^sub>t s"
    using gt_iff_wt_unary_diff_same by blast
  hence gr_s: "ground s"
    using gr_t gt_imp_vars by blast

  have ngr_t_or_s: "\<not> ground t \<or> \<not> ground s"
    using gt_unary_t_s by cases (blast dest: ground_head not_comp_hd_imp_Var)

  show False
    using gr_t gr_s ngr_t_or_s by sat
qed

theorem gt_wf: "wfP (\<lambda>s t. t >\<^sub>t\<^sub>w s)"
proof -
  have ground_wfP: "wfP (\<lambda>s t. t >\<^sub>t\<^sub>w\<^sub>g s)"
    unfolding wfP_iff_no_inf_chain
  proof
    assume "\<exists>f. inf_chain (>\<^sub>t\<^sub>w\<^sub>g) f"
    then obtain t where t_bad: "bad (>\<^sub>t\<^sub>w\<^sub>g) t"
      unfolding inf_chain_def bad_def by blast

    let ?ff = "worst_chain (>\<^sub>t\<^sub>w\<^sub>g) (\<lambda>t s. size t > size s)"

    note wf_sz = wf_app[OF wellorder_class.wf, of size, simplified]

    have ffi_ground: "\<And>i. ground (?ff i)" and ffi_wary: "\<And>i. wary (?ff i)"
      using worst_chain_bad[OF wf_sz t_bad, unfolded inf_chain_def] by fast+

    have "inf_chain (>\<^sub>t\<^sub>w\<^sub>g) ?ff"
      by (rule worst_chain_bad[OF wf_sz t_bad])
    hence bad_wt_diff_same:
      "inf_chain (\<lambda>t s. ground t \<and> (gt_wt t s \<or> gt_diff t s \<or> gt_same t s)) ?ff"
      unfolding inf_chain_def using gt_iff_wt_unary_diff_same ground_gt_unary by blast

    have wf_wt: "wf {(s, t). ground t \<and> gt_wt t s}"
      by (rule wf_subset[OF wf_app[of _ wt, OF wf_less]]) (auto simp: gt_wt.simps)

    have wt_O_diff_same: "{(s, t). ground t \<and> gt_wt t s}
      O {(s, t). ground t \<and> (gt_diff t s \<or> gt_same t s)} \<subseteq> {(s, t). ground t \<and> gt_wt t s}"
      unfolding gt_wt.simps gt_diff.simps gt_same.simps by auto

    have wt_diff_same_as_union: "{(s, t). ground t \<and> (gt_wt t s \<or> gt_diff t s \<or> gt_same t s)} =
      {(s, t). ground t \<and> gt_wt t s} \<union> {(s, t). ground t \<and> (gt_diff t s \<or> gt_same t s)}"
      by auto

    obtain k1 where bad_diff_same:
      "inf_chain (\<lambda>t s. ground t \<and> (gt_diff t s \<or> gt_same t s)) (\<lambda>i. ?ff (i + k1))"
      using wf_infinite_down_chain_compatible[OF wf_wt _ wt_O_diff_same, of ?ff] bad_wt_diff_same
      unfolding inf_chain_def wt_diff_same_as_union[symmetric] by auto

    have "wf {(s, t). ground s \<and> ground t \<and> sym (head t) >\<^sub>s sym (head s)}"
      using gt_sym_wf unfolding wfP_def wf_iff_no_infinite_down_chain by fast
    moreover have "{(s, t). ground t \<and> gt_diff t s}
      \<subseteq> {(s, t). ground s \<and> ground t \<and> sym (head t) >\<^sub>s sym (head s)}"
    proof (clarsimp, intro conjI)
      fix s t
      assume gr_t: "ground t" and gt_diff_t_s: "gt_diff t s"
      thus gr_s: "ground s"
        using gt_iff_wt_unary_diff_same gt_imp_vars by fastforce
      show "sym (head t) >\<^sub>s sym (head s)"
        using gt_diff_t_s by cases (simp add: gt_hd_def gr_s gr_t ground_hd_in_ground_heads)
    qed
    ultimately have wf_diff: "wf {(s, t). ground t \<and> gt_diff t s}"
      by (rule wf_subset)

    have diff_O_same: "{(s, t). ground t \<and> gt_diff t s} O {(s, t). ground t \<and> gt_same t s}
      \<subseteq> {(s, t). ground t \<and> gt_diff t s}"
      unfolding gt_diff.simps gt_same.simps by auto

    have diff_same_as_union: "{(s, t). ground t \<and> (gt_diff t s \<or> gt_same t s)} =
      {(s, t). ground t \<and> gt_diff t s} \<union> {(s, t). ground t \<and> gt_same t s}"
      by auto

    obtain k2 where bad_same: "inf_chain (\<lambda>t s. ground t \<and> gt_same t s) (\<lambda>i. ?ff (i + k2))"
      using wf_infinite_down_chain_compatible[OF wf_diff _ diff_O_same, of "\<lambda>i. ?ff (i + k1)"]
        bad_diff_same
      unfolding inf_chain_def diff_same_as_union[symmetric] by (auto simp: add.assoc)
    hence hd_sym: "\<And>i. is_Sym (head (?ff (i + k2)))"
      unfolding inf_chain_def by (simp add: ground_head)

    define f where "f = sym (head (?ff k2))"

    have hd_eq_f: "head (?ff (i + k2)) = Sym f" for i
      unfolding f_def
    proof (induct i)
      case 0
      thus ?case
        by (auto simp: hd.collapse(2)[OF hd_sym, of 0, simplified])
    next
      case (Suc ia)
      thus ?case
        using bad_same unfolding inf_chain_def gt_same.simps by simp
    qed

    define max_args where "max_args = wt (?ff k2)"

    have wt_eq_max_args: "wt (?ff (i + k2)) = max_args" for i
      unfolding max_args_def
    proof (induct i)
      case (Suc ia)
      thus ?case
        using bad_same unfolding inf_chain_def gt_same.simps by simp
    qed auto

    have nargs_le_max_args: "num_args (?ff (i + k2)) \<le> max_args" for i
      unfolding wt_eq_max_args[of i, symmetric] by (rule wt_ge_num_args[OF ffi_wary])

    let ?U_of = "\<lambda>i. set (args (?ff (i + k2)))"

    define U where "U = (\<Union>i. ?U_of i)"

    have gr_u: "\<And>u. u \<in> U \<Longrightarrow> ground u"
      unfolding U_def by (blast dest: ground_args[OF _ ffi_ground])
    have wary_u: "\<And>u. u \<in> U \<Longrightarrow> wary u"
      unfolding U_def by (blast dest: wary_args[OF _ ffi_wary])

    have "\<not> bad (>\<^sub>t\<^sub>w\<^sub>g) u" if u_in: "u \<in> ?U_of i" for u i
    proof
      assume u_bad: "bad (>\<^sub>t\<^sub>w\<^sub>g) u"
      have sz_u: "size u < size (?ff (i + k2))"
        by (rule size_in_args[OF u_in])

      show False
      proof (cases "i + k2")
        case 0
        thus False
          using sz_u min_worst_chain_0[OF wf_sz u_bad] by simp
      next
        case Suc
        hence gt: "?ff (i + k2 - 1) >\<^sub>t\<^sub>w ?ff (i + k2)"
          using worst_chain_pred[OF wf_sz t_bad] by auto
        moreover have "?ff (i + k2) >\<^sub>t\<^sub>w u"
          using gt gt_proper_sub sub_args sz_u u_in wary_args by auto
        ultimately have "?ff (i + k2 - 1) >\<^sub>t\<^sub>w u"
          using gt_trans by blast
        thus False
          using Suc sz_u min_worst_chain_Suc[OF wf_sz u_bad] ffi_ground by fastforce
      qed
    qed
    hence u_good: "\<And>u. u \<in> U \<Longrightarrow> \<not> bad (>\<^sub>t\<^sub>w\<^sub>g) u"
      unfolding U_def by blast

    let ?gtwu = "\<lambda>t s. t \<in> U \<and> t >\<^sub>t\<^sub>w s"

    have gtwu_irrefl: "\<And>x. \<not> ?gtwu x x"
      using gt_irrefl by auto

    have "\<And>i j. \<forall>t \<in> set (args (?ff (i + k2))). \<forall>s \<in> set (args (?ff (j + k2))). t >\<^sub>t s \<longrightarrow>
      t \<in> U \<and> t >\<^sub>t\<^sub>w s"
      using wary_u unfolding U_def by blast
    moreover have "\<And>i. extf f (>\<^sub>t) (args (?ff (i + k2))) (args (?ff (Suc i + k2)))"
      using bad_same hd_eq_f unfolding inf_chain_def gt_same.simps by auto
    ultimately have "\<And>i. extf f ?gtwu (args (?ff (i + k2))) (args (?ff (Suc i + k2)))"
      by (rule extf_mono_strong)
    hence "inf_chain (extf f ?gtwu) (\<lambda>i. args (?ff (i + k2)))"
      unfolding inf_chain_def by blast
    hence nwf_ext:
      "\<not> wfP (\<lambda>xs ys. length ys \<le> max_args \<and> length xs \<le> max_args \<and> extf f ?gtwu ys xs)"
      unfolding inf_chain_def wfP_def wf_iff_no_infinite_down_chain using nargs_le_max_args by fast

    have gtwu_le_gtwg: "?gtwu \<le> (>\<^sub>t\<^sub>w\<^sub>g)"
      by (auto intro!: gr_u)

    have "wfP (\<lambda>s t. ?gtwu t s)"
      unfolding wfP_iff_no_inf_chain
    proof (intro notI, elim exE)
      fix f
      assume bad_f: "inf_chain ?gtwu f"
      hence bad_f0: "bad ?gtwu (f 0)"
        by (rule inf_chain_bad)
      hence "f 0 \<in> U"
        using bad_f unfolding inf_chain_def by blast
      hence "\<not> bad (>\<^sub>t\<^sub>w\<^sub>g) (f 0)"
        using u_good by blast
      hence "\<not> bad ?gtwu (f 0)"
        using bad_f inf_chain_bad inf_chain_subset[OF _ gtwu_le_gtwg] by blast
      thus False
        using bad_f0 by sat
    qed
    hence wf_ext: "wfP (\<lambda>xs ys. length ys \<le> max_args \<and> length xs \<le> max_args \<and> extf f ?gtwu ys xs)"
      using extf_wf_bounded[of ?gtwu] gtwu_irrefl by blast

    show False
      using nwf_ext wf_ext by blast
  qed

  let ?subst = "subst grounding_\<rho>"

  have "wfP (\<lambda>s t. ?subst t >\<^sub>t\<^sub>w\<^sub>g ?subst s)"
    by (rule wfP_app[OF ground_wfP])
  hence "wfP (\<lambda>s t. ?subst t >\<^sub>t\<^sub>w ?subst s)"
    by (simp add: ground_grounding_\<rho>)
  thus ?thesis
    by (auto intro: wfP_subset wary_subst_wary[OF wary_grounding_\<rho>] gt_subst[OF wary_grounding_\<rho>])
qed

end

end
