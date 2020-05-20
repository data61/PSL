(*  Title:       The Graceful Basic Knuth-Bendix Order for Lambda-Free Higher-Order Terms
    Author:      Jasmin Blanchette <jasmin.blanchette at inria.fr>, 2016
    Maintainer:  Jasmin Blanchette <jasmin.blanchette at inria.fr>
*)

section \<open>The Graceful Basic Knuth--Bendix Order for Lambda-Free Higher-Order Terms\<close>

theory Lambda_Free_KBO_Basic
imports Lambda_Free_KBO_Std
begin

text \<open>
This theory defines the basic version of the graceful Knuth--Bendix order (KBO) for
\<open>\<lambda>\<close>-free higher-order terms. Basic means that all symbols must have a
positive weight. The results are lifted from the standard KBO.
\<close>

locale kbo_basic = kbo_basic_basis _ _ _ ground_heads_var
  for ground_heads_var :: "'v \<Rightarrow> 's set"
begin

sublocale kbo_std: kbo_std _ _ _ 0 _ "\<lambda>_. \<infinity>" "\<lambda>_. \<infinity>"
  by (simp add: \<epsilon>_gt_0 kbo_std_def kbo_std_basis_axioms)

fun wt :: "('s, 'v) tm \<Rightarrow> nat" where
  "wt (Hd \<zeta>) = (LEAST w. \<exists>f \<in> ground_heads \<zeta>. w = wt_sym f)"
| "wt (App s t) = wt s + wt t"

inductive gt :: "('s, 'v) tm \<Rightarrow> ('s, 'v) tm \<Rightarrow> bool" (infix ">\<^sub>t" 50) where
  gt_wt: "vars_mset t \<supseteq># vars_mset s \<Longrightarrow> wt t > wt s \<Longrightarrow> t >\<^sub>t s"
| gt_diff: "vars_mset t \<supseteq># vars_mset s \<Longrightarrow> wt t = wt s \<Longrightarrow> head t >\<^sub>h\<^sub>d head s \<Longrightarrow> t >\<^sub>t s"
| gt_same: "vars_mset t \<supseteq># vars_mset s \<Longrightarrow> wt t = wt s \<Longrightarrow> head t = head s \<Longrightarrow>
    (\<forall>f \<in> ground_heads (head s). extf f (>\<^sub>t) (args t) (args s)) \<Longrightarrow> t >\<^sub>t s"

lemma arity_hd_eq_inf[simp]: "arity_hd \<zeta> = \<infinity>"
  by (cases \<zeta>) auto

lemma waryI[intro, simp]: "wary s"
  by (simp add: wary_inf_ary)

lemma basic_wt_eq_wt: "wt s = kbo_std.wt s"
  by (induct s) auto

lemma
  basic_gt_and_gt_le_gt: "(\<lambda>t s. t >\<^sub>t s \<and> local.kbo_std.gt t s) \<le> kbo_std.gt" and
  gt_and_basic_gt_le_basic_gt: "(\<lambda>t s. local.kbo_std.gt t s \<and> t >\<^sub>t s) \<le> (>\<^sub>t)"
  by auto

lemma basic_gt_iff_gt: "t >\<^sub>t s \<longleftrightarrow> kbo_std.gt t s"
proof
  assume "t >\<^sub>t s"
  thus "kbo_std.gt t s"
  proof induct
    case gt_wt
    thus ?case
      by (auto intro: kbo_std.gt_wt simp: basic_wt_eq_wt[symmetric])
  next
    case gt_diff
    thus ?case
      by (auto intro: kbo_std.gt_diff simp: basic_wt_eq_wt[symmetric])
  next
    case gt_same
    thus ?case
      using extf_mono[OF basic_gt_and_gt_le_gt]
      by (force simp: basic_wt_eq_wt[symmetric] intro!: kbo_std.gt_same)
  qed
next
  assume "kbo_std.gt t s"
  thus "t >\<^sub>t s"
  proof induct
    case gt_wt_t_s: gt_wt
    thus ?case
      by (auto intro: gt_wt simp: basic_wt_eq_wt[symmetric])
  next
    case gt_unary_t_s: (gt_unary t s)
    have False
      using gt_unary_t_s(4) by (metis less_nat_zero_code wt_sym_gt_0)
    thus ?case
      by satx
  next
    case gt_diff_t_s: gt_diff
    thus ?case
      by (auto intro: gt_diff simp: basic_wt_eq_wt[symmetric])
  next
    case gt_same_t_s: gt_same
    thus ?case
      using extf_mono[OF gt_and_basic_gt_le_basic_gt]
      by (force intro!: gt_same simp: basic_wt_eq_wt[symmetric])
  qed
qed

theorem gt_irrefl: "\<not> s >\<^sub>t s"
  unfolding basic_gt_iff_gt by (rule kbo_std.gt_irrefl[simplified])

theorem gt_trans: "u >\<^sub>t t \<Longrightarrow> t >\<^sub>t s \<Longrightarrow> u >\<^sub>t s"
  unfolding basic_gt_iff_gt by (rule kbo_std.gt_trans[simplified])

theorem gt_proper_sub: "proper_sub s t \<Longrightarrow> t >\<^sub>t s"
  unfolding basic_gt_iff_gt by (rule kbo_std.gt_proper_sub[simplified])

theorem gt_compat_fun: "t' >\<^sub>t t \<Longrightarrow> App s t' >\<^sub>t App s t"
  unfolding basic_gt_iff_gt by (rule kbo_std.gt_compat_fun[simplified])

theorem gt_compat_arg: "s' >\<^sub>t s \<Longrightarrow> App s' t >\<^sub>t App s t"
  unfolding basic_gt_iff_gt by (rule kbo_std.gt_compat_arg[simplified])

lemma wt_subst: "wary_subst \<rho> \<Longrightarrow> wt (subst \<rho> s) = wt s + kbo_std.extra_wt \<rho> s"
  unfolding basic_gt_iff_gt basic_wt_eq_wt by (rule kbo_std.wt_subst[simplified])

theorem gt_subst: "wary_subst \<rho> \<Longrightarrow> t >\<^sub>t s \<Longrightarrow> subst \<rho> t >\<^sub>t subst \<rho> s"
  unfolding basic_gt_iff_gt by (rule kbo_std.gt_subst[simplified])

theorem gt_wf: "wfP (\<lambda>s t. t >\<^sub>t s)"
  unfolding basic_gt_iff_gt[abs_def] by (rule kbo_std.gt_wf[simplified])

end

end
