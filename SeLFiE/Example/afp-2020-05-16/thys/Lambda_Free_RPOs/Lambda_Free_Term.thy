(*  Title:       Lambda-Free Higher-Order Terms
    Author:      Jasmin Blanchette <jasmin.blanchette at inria.fr>, 2016
    Maintainer:  Jasmin Blanchette <jasmin.blanchette at inria.fr>
*)

section \<open>Lambda-Free Higher-Order Terms\<close>

theory Lambda_Free_Term
imports Lambda_Free_Util
abbrevs ">s" = ">\<^sub>s"
  and ">h" = ">\<^sub>h\<^sub>d"
  and "\<le>\<ge>h" = "\<le>\<ge>\<^sub>h\<^sub>d"
begin

text \<open>
This theory defines \<open>\<lambda>\<close>-free higher-order terms and related locales.
\<close>


subsection \<open>Precedence on Symbols\<close>

locale gt_sym =
  fixes
    gt_sym :: "'s \<Rightarrow> 's \<Rightarrow> bool" (infix ">\<^sub>s" 50)
  assumes
    gt_sym_irrefl: "\<not> f >\<^sub>s f" and
    gt_sym_trans: "h >\<^sub>s g \<Longrightarrow> g >\<^sub>s f \<Longrightarrow> h >\<^sub>s f" and
    gt_sym_total: "f >\<^sub>s g \<or> g >\<^sub>s f \<or> g = f" and
    gt_sym_wf: "wfP (\<lambda>f g. g >\<^sub>s f)"
begin

lemma gt_sym_antisym: "f >\<^sub>s g \<Longrightarrow> \<not> g >\<^sub>s f"
  by (metis gt_sym_irrefl gt_sym_trans)

end


subsection \<open>Heads\<close>

datatype (plugins del: size) (syms_hd: 's, vars_hd: 'v) hd =
  is_Var: Var (var: 'v)
| Sym (sym: 's)

abbreviation is_Sym :: "('s, 'v) hd \<Rightarrow> bool" where
  "is_Sym \<zeta> \<equiv> \<not> is_Var \<zeta>"

lemma finite_vars_hd[simp]: "finite (vars_hd \<zeta>)"
  by (cases \<zeta>) auto

lemma finite_syms_hd[simp]: "finite (syms_hd \<zeta>)"
  by (cases \<zeta>) auto


subsection \<open>Terms\<close>

consts head0 :: 'a

datatype (syms: 's, vars: 'v) tm =
  is_Hd: Hd (head: "('s, 'v) hd")
| App ("fun": "('s, 'v) tm") (arg: "('s, 'v) tm")
where
  "head (App s _) = head0 s"
| "fun (Hd \<zeta>) = Hd \<zeta>"
| "arg (Hd \<zeta>) = Hd \<zeta>"

overloading head0 \<equiv> "head0 :: ('s, 'v) tm \<Rightarrow> ('s, 'v) hd"
begin

primrec head0 :: "('s, 'v) tm \<Rightarrow> ('s, 'v) hd" where
  "head0 (Hd \<zeta>) = \<zeta>"
| "head0 (App s _) = head0 s"

end

lemma head_App[simp]: "head (App s t) = head s"
  by (cases s) auto

declare tm.sel(2)[simp del]

lemma head_fun[simp]: "head (fun s) = head s"
  by (cases s) auto

abbreviation ground :: "('s, 'v) tm \<Rightarrow> bool" where
  "ground t \<equiv> vars t = {}"

abbreviation is_App :: "('s, 'v) tm \<Rightarrow> bool" where
  "is_App s \<equiv> \<not> is_Hd s"

lemma
  size_fun_lt: "is_App s \<Longrightarrow> size (fun s) < size s" and
  size_arg_lt: "is_App s \<Longrightarrow> size (arg s) < size s"
  by (cases s; simp)+

lemma
  finite_vars[simp]: "finite (vars s)" and
  finite_syms[simp]: "finite (syms s)"
  by (induct s) auto

lemma
  vars_head_subseteq: "vars_hd (head s) \<subseteq> vars s" and
  syms_head_subseteq: "syms_hd (head s) \<subseteq> syms s"
  by (induct s) auto

fun args :: "('s, 'v) tm \<Rightarrow> ('s, 'v) tm list" where
  "args (Hd _) = []"
| "args (App s t) = args s @ [t]"

lemma set_args_fun: "set (args (fun s)) \<subseteq> set (args s)"
  by (cases s) auto

lemma arg_in_args: "is_App s \<Longrightarrow> arg s \<in> set (args s)"
  by (cases s rule: tm.exhaust) auto

lemma
  vars_args_subseteq: "si \<in> set (args s) \<Longrightarrow> vars si \<subseteq> vars s" and
  syms_args_subseteq: "si \<in> set (args s) \<Longrightarrow> syms si \<subseteq> syms s"
  by (induct s) auto

lemma args_Nil_iff_is_Hd: "args s = [] \<longleftrightarrow> is_Hd s"
  by (cases s) auto

abbreviation num_args :: "('s, 'v) tm \<Rightarrow> nat" where
  "num_args s \<equiv> length (args s)"

lemma size_ge_num_args: "size s \<ge> num_args s"
  by (induct s) auto

lemma Hd_head_id: "num_args s = 0 \<Longrightarrow> Hd (head s) = s"
  by (metis args.cases args.simps(2) length_0_conv snoc_eq_iff_butlast tm.collapse(1) tm.disc(1))

lemma one_arg_imp_Hd: "num_args s = 1 \<Longrightarrow> s = App t u \<Longrightarrow> t = Hd (head t)"
  by (simp add: Hd_head_id)

lemma size_in_args: "s \<in> set (args t) \<Longrightarrow> size s < size t"
  by (induct t) auto

primrec apps :: "('s, 'v) tm \<Rightarrow> ('s, 'v) tm list \<Rightarrow> ('s, 'v) tm" where
  "apps s [] = s"
| "apps s (t # ts) = apps (App s t) ts"

lemma
  vars_apps[simp]: "vars (apps s ss) = vars s \<union> (\<Union>s \<in> set ss. vars s)" and
  syms_apps[simp]: "syms (apps s ss) = syms s \<union> (\<Union>s \<in> set ss. syms s)" and
  head_apps[simp]: "head (apps s ss) = head s" and
  args_apps[simp]: "args (apps s ss) = args s @ ss" and
  is_App_apps[simp]: "is_App (apps s ss) \<longleftrightarrow> args (apps s ss) \<noteq> []" and
  fun_apps_Nil[simp]: "fun (apps s []) = fun s" and
  fun_apps_Cons[simp]: "fun (apps (App s sa) ss) = apps s (butlast (sa # ss))" and
  arg_apps_Nil[simp]: "arg (apps s []) = arg s" and
  arg_apps_Cons[simp]: "arg (apps (App s sa) ss) = last (sa # ss)"
  by (induct ss arbitrary: s sa) (auto simp: args_Nil_iff_is_Hd)

lemma apps_append[simp]: "apps s (ss @ ts) = apps (apps s ss) ts"
  by (induct ss arbitrary: s ts) auto

lemma App_apps: "App (apps s ts) t = apps s (ts @ [t])"
  by simp

lemma tm_inject_apps[iff, induct_simp]: "apps (Hd \<zeta>) ss = apps (Hd \<xi>) ts \<longleftrightarrow> \<zeta> = \<xi> \<and> ss = ts"
  by (metis args_apps head_apps same_append_eq tm.sel(1))

lemma tm_collapse_apps[simp]: "apps (Hd (head s)) (args s) = s"
  by (induct s) auto

lemma tm_expand_apps: "head s = head t \<Longrightarrow> args s = args t \<Longrightarrow> s = t"
  by (metis tm_collapse_apps)

lemma tm_exhaust_apps_sel[case_names apps]: "(s = apps (Hd (head s)) (args s) \<Longrightarrow> P) \<Longrightarrow> P"
  by (atomize_elim, induct s) auto

lemma tm_exhaust_apps[case_names apps]: "(\<And>\<zeta> ss. s = apps (Hd \<zeta>) ss \<Longrightarrow> P) \<Longrightarrow> P"
  by (metis tm_collapse_apps)

lemma tm_induct_apps[case_names apps]:
  assumes "\<And>\<zeta> ss. (\<And>s. s \<in> set ss \<Longrightarrow> P s) \<Longrightarrow> P (apps (Hd \<zeta>) ss)"
  shows "P s"
  using assms
  by (induct s taking: size rule: measure_induct_rule) (metis size_in_args tm_collapse_apps)

lemma
  ground_fun: "ground s \<Longrightarrow> ground (fun s)" and
  ground_arg: "ground s \<Longrightarrow> ground (arg s)"
  by (induct s) auto

lemma ground_head: "ground s \<Longrightarrow> is_Sym (head s)"
  by (cases s rule: tm_exhaust_apps) (auto simp: is_Var_def)

lemma ground_args: "t \<in> set (args s) \<Longrightarrow> ground s \<Longrightarrow> ground t"
  by (induct s rule: tm_induct_apps) auto

primrec vars_mset :: "('s, 'v) tm \<Rightarrow> 'v multiset" where
  "vars_mset (Hd \<zeta>) = mset_set (vars_hd \<zeta>)"
| "vars_mset (App s t) = vars_mset s + vars_mset t"

lemma set_vars_mset[simp]: "set_mset (vars_mset t) = vars t"
  by (induct t) auto

lemma vars_mset_empty_iff[iff]: "vars_mset s = {#} \<longleftrightarrow> ground s"
  by (induct s) (auto simp: mset_set_empty_iff)

lemma vars_mset_fun[intro]: "vars_mset (fun t) \<subseteq># vars_mset t"
  by (cases t) auto

lemma vars_mset_arg[intro]: "vars_mset (arg t) \<subseteq># vars_mset t"
  by (cases t) auto


subsection \<open>hsize\<close>

text \<open>The hsize of a term is the number of heads (Syms or Vars) in the term.\<close>

primrec hsize :: "('s, 'v) tm \<Rightarrow> nat" where
  "hsize (Hd \<zeta>) = 1"
| "hsize (App s t) = hsize s + hsize t"

lemma hsize_size: "hsize t * 2 = size t + 1"
  by (induct t) auto

lemma hsize_pos[simp]: "hsize t > 0"
  by (induction t; simp)

lemma hsize_fun_lt: "is_App s \<Longrightarrow> hsize (fun s) < hsize s"
  by (cases s; simp)

lemma hsize_arg_lt: "is_App s \<Longrightarrow> hsize (arg s) < hsize s"
  by (cases s; simp)
  
lemma hsize_ge_num_args: "hsize s \<ge> hsize s"
  by (induct s) auto

lemma hsize_in_args: "s \<in> set (args t) \<Longrightarrow> hsize s < hsize t"
  by (induct t) auto

lemma hsize_apps: "hsize (apps t ts) = hsize t + sum_list (map hsize ts)"
  by (induct ts arbitrary:t; simp)

lemma hsize_args: "1 + sum_list (map hsize (args t)) = hsize t"
  by (metis hsize.simps(1) hsize_apps tm_collapse_apps)


subsection \<open>Substitutions\<close>

primrec subst :: "('v \<Rightarrow> ('s, 'v) tm) \<Rightarrow> ('s, 'v) tm \<Rightarrow> ('s, 'v) tm" where
  "subst \<rho> (Hd \<zeta>) = (case \<zeta> of Var x \<Rightarrow> \<rho> x | Sym f \<Rightarrow> Hd (Sym f))"
| "subst \<rho> (App s t) = App (subst \<rho> s) (subst \<rho> t)"

lemma subst_apps[simp]: "subst \<rho> (apps s ts) = apps (subst \<rho> s) (map (subst \<rho>) ts)"
  by (induct ts arbitrary: s) auto

lemma head_subst[simp]: "head (subst \<rho> s) = head (subst \<rho> (Hd (head s)))"
  by (cases s rule: tm_exhaust_apps) (auto split: hd.split)

lemma args_subst[simp]:
  "args (subst \<rho> s) = (case head s of Var x \<Rightarrow> args (\<rho> x) | Sym f \<Rightarrow> []) @ map (subst \<rho>) (args s)"
  by (cases s rule: tm_exhaust_apps) (auto split: hd.split)

lemma ground_imp_subst_iden: "ground s \<Longrightarrow> subst \<rho> s = s"
  by (induct s) (auto split: hd.split)

lemma vars_mset_subst[simp]: "vars_mset (subst \<rho> s) = (\<Union># {#vars_mset (\<rho> x). x \<in># vars_mset s#})"
proof (induct s)
  case (Hd \<zeta>)
  show ?case
    by (cases \<zeta>) auto
qed auto

lemma vars_mset_subst_subseteq:
  "vars_mset t \<supseteq># vars_mset s \<Longrightarrow> vars_mset (subst \<rho> t) \<supseteq># vars_mset (subst \<rho> s)"
  unfolding vars_mset_subst
  by (metis (no_types) add_diff_cancel_right' diff_subset_eq_self image_mset_union sum_mset.union
    subset_mset.add_diff_inverse)

lemma vars_subst_subseteq: "vars t \<supseteq> vars s \<Longrightarrow> vars (subst \<rho> t) \<supseteq> vars (subst \<rho> s)"
  unfolding set_vars_mset[symmetric] vars_mset_subst by auto


subsection \<open>Subterms\<close>

inductive sub :: "('s, 'v) tm \<Rightarrow> ('s, 'v) tm \<Rightarrow> bool" where
  sub_refl: "sub s s"
| sub_fun: "sub s t \<Longrightarrow> sub s (App u t)"
| sub_arg: "sub s t \<Longrightarrow> sub s (App t u)"

inductive_cases sub_HdE[simplified, elim]: "sub s (Hd \<xi>)"
inductive_cases sub_AppE[simplified, elim]: "sub s (App t u)"
inductive_cases sub_Hd_HdE[simplified, elim]: "sub (Hd \<zeta>) (Hd \<xi>)"
inductive_cases sub_Hd_AppE[simplified, elim]: "sub (Hd \<zeta>) (App t u)"

lemma in_vars_imp_sub: "x \<in> vars s \<longleftrightarrow> sub (Hd (Var x)) s"
  by induct (auto intro: sub.intros elim: hd.set_cases(2))

lemma sub_args: "s \<in> set (args t) \<Longrightarrow> sub s t"
  by (induct t) (auto intro: sub.intros)

lemma sub_size: "sub s t \<Longrightarrow> size s \<le> size t"
  by induct auto

lemma sub_subst: "sub s t \<Longrightarrow> sub (subst \<rho> s) (subst \<rho> t)"
proof (induct t)
  case (Hd \<zeta>)
  thus ?case
    by (cases \<zeta>; blast intro: sub.intros)
qed (auto intro: sub.intros del: sub_AppE elim!: sub_AppE)

abbreviation proper_sub :: "('s, 'v) tm \<Rightarrow> ('s, 'v) tm \<Rightarrow> bool" where
  "proper_sub s t \<equiv> sub s t \<and> s \<noteq> t"

lemma proper_sub_Hd[simp]: "\<not> proper_sub s (Hd \<zeta>)"
  using sub.cases by blast

lemma proper_sub_subst:
  assumes psub: "proper_sub s t"
  shows "proper_sub (subst \<rho> s) (subst \<rho> t)"
proof (cases t)
  case Hd
  thus ?thesis
    using psub by simp
next
  case t: (App t1 t2)
  have "sub s t1 \<or> sub s t2"
    using t psub by blast
  hence "sub (subst \<rho> s) (subst \<rho> t1) \<or> sub (subst \<rho> s) (subst \<rho> t2)"
    using sub_subst by blast
  thus ?thesis
    unfolding t by (auto intro: sub.intros dest: sub_size)
qed


subsection \<open>Maximum Arities\<close>

locale arity =
  fixes
    arity_sym :: "'s \<Rightarrow> enat" and
    arity_var :: "'v \<Rightarrow> enat"
begin

primrec arity_hd :: "('s, 'v) hd \<Rightarrow> enat" where
  "arity_hd (Var x) = arity_var x"
| "arity_hd (Sym f) = arity_sym f"

definition arity :: "('s, 'v) tm \<Rightarrow> enat" where
  "arity s = arity_hd (head s) - num_args s"

lemma arity_simps[simp]:
  "arity (Hd \<zeta>) = arity_hd \<zeta>"
  "arity (App s t) = arity s - 1"
  by (auto simp: arity_def enat_diff_diff_eq add.commute eSuc_enat plus_1_eSuc(1))

lemma arity_apps[simp]: "arity (apps s ts) = arity s - length ts"
proof (induct ts arbitrary: s)
  case (Cons t ts)
  thus ?case
    by (case_tac "arity s"; simp add: one_enat_def)
qed simp

inductive wary :: "('s, 'v) tm \<Rightarrow> bool" where
  wary_Hd[intro]: "wary (Hd \<zeta>)"
| wary_App[intro]: "wary s \<Longrightarrow> wary t \<Longrightarrow> num_args s < arity_hd (head s) \<Longrightarrow> wary (App s t)"

inductive_cases wary_HdE: "wary (Hd \<zeta>)"
inductive_cases wary_AppE: "wary (App s t)"
inductive_cases wary_binaryE[simplified]: "wary (App (App s t) u)"

lemma wary_fun[intro]: "wary t \<Longrightarrow> wary (fun t)"
  by (cases t) (auto elim: wary.cases)

lemma wary_arg[intro]: "wary t \<Longrightarrow> wary (arg t)"
  by (cases t) (auto elim: wary.cases)

lemma wary_args: "s \<in> set (args t) \<Longrightarrow> wary t \<Longrightarrow> wary s"
  by (induct t arbitrary: s, simp)
   (metis Un_iff args.simps(2) wary.cases insert_iff length_pos_if_in_set
      less_numeral_extra(3) list.set(2) list.size(3) set_append tm.distinct(1) tm.inject(2))

lemma wary_sub: "sub s t \<Longrightarrow> wary t \<Longrightarrow> wary s"
  by (induct rule: sub.induct) (auto elim: wary.cases)

lemma wary_inf_ary: "(\<And>\<zeta>. arity_hd \<zeta> = \<infinity>) \<Longrightarrow> wary s"
  by induct auto

lemma wary_num_args_le_arity_head: "wary s \<Longrightarrow> num_args s \<le> arity_hd (head s)"
  by (induct rule: wary.induct) (auto simp: zero_enat_def[symmetric] Suc_ile_eq)

lemma wary_apps:
  "wary s \<Longrightarrow> (\<And>sa. sa \<in> set ss \<Longrightarrow> wary sa) \<Longrightarrow> length ss \<le> arity s \<Longrightarrow> wary (apps s ss)"
proof (induct ss arbitrary: s)
  case (Cons sa ss)
  note ih = this(1) and wary_s = this(2) and wary_ss = this(3) and nargs_s_sa_ss = this(4)
  show ?case
    unfolding apps.simps
  proof (rule ih)
    have "wary sa"
      using wary_ss by simp
    moreover have " enat (num_args s) < arity_hd (head s)"
      by (metis (mono_tags) One_nat_def add.comm_neutral arity_def diff_add_zero enat_ord_simps(1)
        idiff_enat_enat less_one list.size(4) nargs_s_sa_ss not_add_less2
        order.not_eq_order_implies_strict wary_num_args_le_arity_head wary_s)
    ultimately show "wary (App s sa)"
      by (rule wary_App[OF wary_s])
  next
    show "\<And>sa. sa \<in> set ss \<Longrightarrow> wary sa"
      using wary_ss by simp
  next
    show "length ss \<le> arity (App s sa)"
    proof (cases "arity s")
      case enat
      thus ?thesis
        using nargs_s_sa_ss by (simp add: one_enat_def)
    qed simp
  qed
qed simp

lemma wary_cases_apps[consumes 1, case_names apps]:
  assumes
    wary_t: "wary t" and
    apps: "\<And>\<zeta> ss. t = apps (Hd \<zeta>) ss \<Longrightarrow> (\<And>sa. sa \<in> set ss \<Longrightarrow> wary sa) \<Longrightarrow> length ss \<le> arity_hd \<zeta> \<Longrightarrow> P"
  shows P
  using apps
proof (atomize_elim, cases t rule: tm_exhaust_apps)
  case t: (apps \<zeta> ss)
  show "\<exists>\<zeta> ss. t = apps (Hd \<zeta>) ss \<and> (\<forall>sa. sa \<in> set ss \<longrightarrow> wary sa) \<and> enat (length ss) \<le> arity_hd \<zeta>"
    by (rule exI[of _ \<zeta>], rule exI[of _ ss])
      (auto simp: t wary_args[OF _ wary_t] wary_num_args_le_arity_head[OF wary_t, unfolded t, simplified])
qed

lemma arity_hd_head: "wary s \<Longrightarrow> arity_hd (head s) = arity s + num_args s"
  by (simp add: arity_def enat_sub_add_same wary_num_args_le_arity_head)

lemma arity_head_ge: "arity_hd (head s) \<ge> arity s"
  by (induct s) (auto intro: enat_le_imp_minus_le)

inductive wary_fo :: "('s, 'v) tm \<Rightarrow> bool" where
  wary_foI[intro]: "is_Hd s \<or> is_Sym (head s) \<Longrightarrow> length (args s) = arity_hd (head s) \<Longrightarrow>
    (\<forall>t \<in> set (args s). wary_fo t) \<Longrightarrow> wary_fo s"

lemma wary_fo_args: "s \<in> set (args t) \<Longrightarrow> wary_fo t \<Longrightarrow> wary_fo s"
  by (induct t arbitrary: s rule: tm_induct_apps, simp)
    (metis args.simps(1) args_apps self_append_conv2 wary_fo.cases)

lemma wary_fo_arg: "wary_fo (App s t) \<Longrightarrow> wary_fo t"
  by (erule wary_fo.cases) auto

end


subsection \<open>Potential Heads of Ground Instances of Variables\<close>

locale ground_heads = gt_sym "(>\<^sub>s)" + arity arity_sym arity_var
    for
      gt_sym :: "'s \<Rightarrow> 's \<Rightarrow> bool" (infix ">\<^sub>s" 50) and
      arity_sym :: "'s \<Rightarrow> enat" and
      arity_var :: "'v \<Rightarrow> enat" +
  fixes
    ground_heads_var :: "'v \<Rightarrow> 's set"
  assumes
    ground_heads_var_arity: "f \<in> ground_heads_var x \<Longrightarrow> arity_sym f \<ge> arity_var x" and
    ground_heads_var_nonempty: "ground_heads_var x \<noteq> {}"
begin

primrec ground_heads :: "('s, 'v) hd \<Rightarrow> 's set" where
  "ground_heads (Var x) = ground_heads_var x"
| "ground_heads (Sym f) = {f}"

lemma ground_heads_arity: "f \<in> ground_heads \<zeta> \<Longrightarrow> arity_sym f \<ge> arity_hd \<zeta>"
  by (cases \<zeta>) (auto simp: ground_heads_var_arity)

lemma ground_heads_nonempty[simp]: "ground_heads \<zeta> \<noteq> {}"
  by (cases \<zeta>) (auto simp: ground_heads_var_nonempty)

lemma sym_in_ground_heads: "is_Sym \<zeta> \<Longrightarrow> sym \<zeta> \<in> ground_heads \<zeta>"
  by (metis ground_heads.simps(2) hd.collapse(2) hd.set_sel(1) hd.simps(16))

lemma ground_hd_in_ground_heads: "ground s \<Longrightarrow> sym (head s) \<in> ground_heads (head s)"
  by (simp add: ground_head sym_in_ground_heads)

lemma some_ground_head_arity: "arity_sym (SOME f. f \<in> ground_heads (Var x)) \<ge> arity_var x"
  by (simp add: ground_heads_var_arity ground_heads_var_nonempty some_in_eq)

definition wary_subst :: "('v \<Rightarrow> ('s, 'v) tm) \<Rightarrow> bool" where
  "wary_subst \<rho> \<longleftrightarrow>
   (\<forall>x. wary (\<rho> x) \<and> arity (\<rho> x) \<ge> arity_var x \<and> ground_heads (head (\<rho> x)) \<subseteq> ground_heads_var x)"

definition strict_wary_subst :: "('v \<Rightarrow> ('s, 'v) tm) \<Rightarrow> bool" where
  "strict_wary_subst \<rho> \<longleftrightarrow>
   (\<forall>x. wary (\<rho> x) \<and> arity (\<rho> x) \<in> {arity_var x, \<infinity>}
    \<and> ground_heads (head (\<rho> x)) \<subseteq> ground_heads_var x)"

lemma strict_imp_wary_subst: "strict_wary_subst \<rho> \<Longrightarrow> wary_subst \<rho>"
  unfolding strict_wary_subst_def wary_subst_def using eq_iff by force

lemma wary_subst_wary:
  assumes wary_\<rho>: "wary_subst \<rho>" and wary_s: "wary s"
  shows "wary (subst \<rho> s)"
  using wary_s
proof (induct s rule: tm.induct)
  case (App s t)
  note wary_st = this(3)
  from wary_st have wary_s: "wary s"
    by (rule wary_AppE)
  from wary_st have wary_t: "wary t"
    by (rule wary_AppE)
  from wary_st have nargs_s_lt: "num_args s < arity_hd (head s)"
    by (rule wary_AppE)

  note wary_\<rho>s = App(1)[OF wary_s]
  note wary_\<rho>t = App(2)[OF wary_t]

  note wary_\<rho>x = wary_\<rho>[unfolded wary_subst_def, rule_format, THEN conjunct1]
  note ary_\<rho>x = wary_\<rho>[unfolded wary_subst_def, rule_format, THEN conjunct2]

  have "num_args (\<rho> x) + num_args s < arity_hd (head (\<rho> x))" if hd_s: "head s = Var x" for x
  proof -
    have ary_hd_s: "arity_hd (head s) = arity_var x"
      using hd_s arity_hd.simps(1) by presburger
    hence "num_args s \<le> arity (\<rho> x)"
      by (metis (no_types) wary_num_args_le_arity_head ary_\<rho>x dual_order.trans wary_s)
    hence "num_args s + num_args (\<rho> x) \<le> arity_hd (head (\<rho> x))"
      by (metis (no_types) arity_hd_head[OF wary_\<rho>x] add_right_mono plus_enat_simps(1))
    thus ?thesis
      using ary_hd_s by (metis (no_types) add.commute add_diff_cancel_left' ary_\<rho>x arity_def
        idiff_enat_enat leD nargs_s_lt order.not_eq_order_implies_strict)
  qed
  hence nargs_\<rho>s: "num_args (subst \<rho> s) < arity_hd (head (subst \<rho> s))"
    using nargs_s_lt by (auto split: hd.split)

  show ?case
    by simp (rule wary_App[OF wary_\<rho>s wary_\<rho>t nargs_\<rho>s])
qed (auto simp: wary_\<rho>[unfolded wary_subst_def] split: hd.split)

lemmas strict_wary_subst_wary = wary_subst_wary[OF strict_imp_wary_subst]

lemma wary_subst_ground_heads:
  assumes wary_\<rho>: "wary_subst \<rho>"
  shows "ground_heads (head (subst \<rho> s)) \<subseteq> ground_heads (head s)"
proof (induct s rule: tm_induct_apps)
  case (apps \<zeta> ss)
  show ?case
  proof (cases \<zeta>)
    case x: (Var x)
    thus ?thesis
      using wary_\<rho> wary_subst_def x by auto
  qed auto
qed

lemmas strict_wary_subst_ground_heads = wary_subst_ground_heads[OF strict_imp_wary_subst]

definition grounding_\<rho> :: "'v \<Rightarrow> ('s, 'v) tm" where
  "grounding_\<rho> x = (let s = Hd (Sym (SOME f. f \<in> ground_heads_var x)) in
     apps s (replicate (the_enat (arity s - arity_var x)) s))"

lemma ground_grounding_\<rho>: "ground (subst grounding_\<rho> s)"
  by (induct s) (auto simp: Let_def grounding_\<rho>_def elim: hd.set_cases(2) split: hd.split)

lemma strict_wary_grounding_\<rho>: "strict_wary_subst grounding_\<rho>"
  unfolding strict_wary_subst_def
proof (intro allI conjI)
  fix x

  define f where "f = (SOME f. f \<in> ground_heads_var x)"
  define s :: "('s, 'v) tm" where "s = Hd (Sym f)"

  have wary_s: "wary s"
    unfolding s_def by (rule wary_Hd)
  have ary_s_ge_x: "arity s \<ge> arity_var x"
    unfolding s_def f_def using some_ground_head_arity by simp
  have gr\<rho>_x: "grounding_\<rho> x = apps s (replicate (the_enat (arity s - arity_var x)) s)"
    unfolding grounding_\<rho>_def Let_def f_def[symmetric] s_def[symmetric] by (rule refl)

  show "wary (grounding_\<rho> x)"
    unfolding gr\<rho>_x by (auto intro!: wary_s wary_apps[OF wary_s] enat_the_enat_minus_le)
  show "arity (grounding_\<rho> x) \<in> {arity_var x, \<infinity>}"
    unfolding gr\<rho>_x using ary_s_ge_x by (cases "arity s"; cases "arity_var x"; simp)
  show "ground_heads (head (grounding_\<rho> x)) \<subseteq> ground_heads_var x"
    unfolding gr\<rho>_x s_def f_def by (simp add: some_in_eq ground_heads_var_nonempty)
qed

lemmas wary_grounding_\<rho> = strict_wary_grounding_\<rho>[THEN strict_imp_wary_subst]

definition gt_hd :: "('s, 'v) hd \<Rightarrow> ('s, 'v) hd \<Rightarrow> bool" (infix ">\<^sub>h\<^sub>d" 50) where
  "\<xi> >\<^sub>h\<^sub>d \<zeta> \<longleftrightarrow> (\<forall>g \<in> ground_heads \<xi>. \<forall>f \<in> ground_heads \<zeta>. g >\<^sub>s f)"

definition comp_hd :: "('s, 'v) hd \<Rightarrow> ('s, 'v) hd \<Rightarrow> bool" (infix "\<le>\<ge>\<^sub>h\<^sub>d" 50) where
  "\<xi> \<le>\<ge>\<^sub>h\<^sub>d \<zeta> \<longleftrightarrow> \<xi> = \<zeta> \<or> \<xi> >\<^sub>h\<^sub>d \<zeta> \<or> \<zeta> >\<^sub>h\<^sub>d \<xi>"

lemma gt_hd_irrefl: "\<not> \<zeta> >\<^sub>h\<^sub>d \<zeta>"
  unfolding gt_hd_def using gt_sym_irrefl by (meson ex_in_conv ground_heads_nonempty)

lemma gt_hd_trans: "\<chi> >\<^sub>h\<^sub>d \<xi> \<Longrightarrow> \<xi> >\<^sub>h\<^sub>d \<zeta> \<Longrightarrow> \<chi> >\<^sub>h\<^sub>d \<zeta>"
  unfolding gt_hd_def using gt_sym_trans by (meson ex_in_conv ground_heads_nonempty)

lemma gt_sym_imp_hd: "g >\<^sub>s f \<Longrightarrow> Sym g >\<^sub>h\<^sub>d Sym f"
  unfolding gt_hd_def by simp

lemma not_comp_hd_imp_Var: "\<not> \<xi> \<le>\<ge>\<^sub>h\<^sub>d \<zeta> \<Longrightarrow> is_Var \<zeta> \<or> is_Var \<xi>"
  using gt_sym_total by (cases \<zeta>; cases \<xi>; auto simp: comp_hd_def gt_hd_def)

end

end
