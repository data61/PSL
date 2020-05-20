(*
Author:  Christian Sternagel <c.sternagel@gmail.com>
Author:  René Thiemann <rene.thiemann@uibk.ac.at>
License: LGPL
*)
section \<open>Subsumption\<close>

text \<open>We define the subsumption relation on terms and prove its well-foundedness.\<close>

theory Subsumption
  imports
    Term
    "Abstract-Rewriting.Seq"
    "HOL-Library.Adhoc_Overloading"
    Fun_More
    Seq_More
begin

consts
  SUBSUMESEQ :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<le>\<cdot>" 50) 
  SUBSUMES :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "<\<cdot>" 50)
  LITSIM :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<doteq>" 50)

abbreviation (input) INSTANCEQ (infix "\<cdot>\<ge>" 50)
  where
    "x \<cdot>\<ge> y \<equiv> y \<le>\<cdot> x"

abbreviation (input) INSTANCE (infix "\<cdot>>" 50)
  where
    "x \<cdot>> y \<equiv> y <\<cdot> x"

abbreviation INSTANCEEQ_SET ("{\<cdot>\<ge>}")
  where
    "{\<cdot>\<ge>} \<equiv> {(x, y). y \<le>\<cdot> x}"

abbreviation INSTANCE_SET ("{\<cdot>>}")
  where
    "{\<cdot>>} \<equiv> {(x, y). y <\<cdot> x}"

abbreviation SUBSUMESEQ_SET ("{\<le>\<cdot>}")
  where
    "{\<le>\<cdot>} \<equiv> {(x, y). x \<le>\<cdot> y}"

abbreviation SUBSUMES_SET ("{<\<cdot>}")
  where
    "{<\<cdot>} \<equiv> {(x, y). x <\<cdot> y}"

abbreviation LITSIM_SET ("{\<doteq>}")
  where
    "{\<doteq>} \<equiv> {(x, y). x \<doteq> y}"

locale subsumable =
  fixes subsumeseq :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  assumes refl: "subsumeseq x x"
    and trans: "subsumeseq x y \<Longrightarrow> subsumeseq y z \<Longrightarrow> subsumeseq x z"
begin

adhoc_overloading
  SUBSUMESEQ subsumeseq

definition "subsumes t s \<longleftrightarrow> t \<le>\<cdot> s \<and> \<not> s \<le>\<cdot> t"

definition "litsim s t \<longleftrightarrow> s \<le>\<cdot> t \<and> t \<le>\<cdot> s"

adhoc_overloading
  SUBSUMES subsumes and
  LITSIM litsim

lemma litsim_refl [simp]:
  "s \<doteq> s"
  by (auto simp: litsim_def refl)

lemma litsim_sym:
  "s \<doteq> t \<Longrightarrow> t \<doteq> s"
  by (auto simp: litsim_def)

lemma litsim_trans:
  "s \<doteq> t \<Longrightarrow> t \<doteq> u \<Longrightarrow> s \<doteq> u"
  by (auto simp: litsim_def dest: trans)

end

sublocale subsumable \<subseteq> subsumption: preorder "(\<le>\<cdot>)" "(<\<cdot>)"
  by (unfold_locales) (auto simp: subsumes_def refl elim: trans)

inductive subsumeseq_term :: "('a, 'b) term \<Rightarrow> ('a, 'b) term \<Rightarrow> bool"
  where
    [intro]: "t = s \<cdot> \<sigma> \<Longrightarrow> subsumeseq_term s t"

adhoc_overloading
  SUBSUMESEQ subsumeseq_term

lemma subsumeseq_termE [elim]:
  assumes "s \<le>\<cdot> t"
  obtains \<sigma> where "t = s \<cdot> \<sigma>"
  using assms by (cases)

lemma subsumeseq_term_refl:
  fixes t :: "('a, 'b) term"
  shows "t \<le>\<cdot> t"
  by (rule subsumeseq_term.intros [of t t Var]) simp

lemma subsumeseq_term_trans:
  fixes s t u :: "('a, 'b) term"
  assumes "s \<le>\<cdot> t" and "t \<le>\<cdot> u"
  shows "s \<le>\<cdot> u"
proof -
  obtain \<sigma> \<tau>
    where [simp]: "t = s \<cdot> \<sigma>" "u = t \<cdot> \<tau>" using assms by fastforce
  show ?thesis
    by (rule subsumeseq_term.intros [of _ _ "\<sigma> \<circ>\<^sub>s \<tau>"]) simp
qed

interpretation term_subsumable: subsumable subsumeseq_term
  by standard (force simp: subsumeseq_term_refl dest: subsumeseq_term_trans)+

adhoc_overloading
  SUBSUMES term_subsumable.subsumes and
  LITSIM term_subsumable.litsim

lemma subsumeseq_term_iff:
  "s \<cdot>\<ge> t \<longleftrightarrow> (\<exists>\<sigma>. s = t \<cdot> \<sigma>)"
  by auto

fun num_syms :: "('f, 'v) term \<Rightarrow> nat"
  where
    "num_syms (Var x) = 1" |
    "num_syms (Fun f ts) = Suc (sum_list (map num_syms ts))"

fun num_vars :: "('f, 'v) term \<Rightarrow> nat"
  where
    "num_vars (Var x) = 1" |
    "num_vars (Fun f ts) = sum_list (map num_vars ts)"

definition num_unique_vars :: "('f, 'v) term \<Rightarrow> nat"
  where
    "num_unique_vars t = card (vars_term t)"

lemma num_syms_1: "num_syms t \<ge> 1"
  by (induct t) auto

lemma num_syms_subst:
  "num_syms (t \<cdot> \<sigma>) \<ge> num_syms t"
  using num_syms_1
  by (induct t) (auto, metis comp_apply sum_list_mono)


subsection \<open>Equality of terms modulo variables\<close>

inductive emv where
  Var [simp, intro!]: "emv (Var x) (Var y)" |
  Fun [intro]: "\<lbrakk>f = g; length ss = length ts; \<forall>i < length ts. emv (ss ! i) (ts ! i)\<rbrakk> \<Longrightarrow>
    emv (Fun f ss) (Fun g ts)"

lemma sum_list_map_num_syms_subst:
  assumes "sum_list (map (num_syms \<circ> (\<lambda>t. t \<cdot> \<sigma>)) ts) = sum_list (map num_syms ts)"
  shows "\<forall>i < length ts. num_syms (ts ! i \<cdot> \<sigma>) = num_syms (ts ! i)"
  using assms
proof (induct ts)
  case (Cons t ts)
  then have "num_syms (t \<cdot> \<sigma>) + sum_list (map (num_syms \<circ> (\<lambda>t. t \<cdot> \<sigma>)) ts)
    = num_syms t + sum_list (map num_syms ts)" by (simp add: o_def)
  moreover have "num_syms (t \<cdot> \<sigma>) \<ge> num_syms t" by (metis num_syms_subst)
  moreover have "sum_list (map (num_syms \<circ> (\<lambda>t. t \<cdot> \<sigma>)) ts) \<ge> sum_list (map num_syms ts)"
    using num_syms_subst [of _ \<sigma>] by (induct ts) (auto intro: add_mono)
  ultimately show ?case using Cons by (auto) (case_tac i, auto)
qed simp

lemma subst_size_emv:
  assumes "s = t \<cdot> \<tau>" and "num_syms s = num_syms t" and "num_funs s = num_funs t"
  shows "emv s t"
  using assms
proof (induct t arbitrary: s)
  case (Var x)
  then show ?case by (force elim: num_funs_0)
next
  case (Fun g ts)
  note IH = this
  show ?case
  proof (cases s)
    case (Var x)
    then show ?thesis using Fun by simp
  next
    case (Fun f ss)
    from IH(2-) [unfolded Fun]
      and sum_list_map_num_syms_subst [of \<tau> ts]
      and sum_list_map_num_funs_subst [of \<tau> ts]
    have "\<forall>i < length ts. num_syms (ts ! i  \<cdot> \<tau>) = num_syms (ts ! i)"
      and "\<forall>i < length ts. num_funs (ts ! i \<cdot> \<tau>) = num_funs (ts ! i)"
      by auto
    with Fun and IH show ?thesis by auto
  qed
qed

lemma subsumeseq_term_size_emv:
  assumes "s \<cdot>\<ge> t" and "num_syms s = num_syms t" and "num_funs s = num_funs t"
  shows "emv s t"
  using assms(1) and subst_size_emv [OF _ assms(2-)] by (cases) simp

lemma emv_subst_vars_term:
  assumes "emv s t"
    and "s = t \<cdot> \<sigma>"
  shows "vars_term s = (the_Var \<circ> \<sigma>) ` vars_term t"
  using assms [unfolded subsumeseq_term_iff]
  apply (induct)
   apply (auto simp: in_set_conv_nth iff: image_iff)
   apply (metis nth_mem)
  by (metis comp_apply imageI nth_mem)

lemma emv_subst_imp_num_unique_vars_le:
  assumes "emv s t"
    and "s = t \<cdot> \<sigma>"
  shows "num_unique_vars s \<le> num_unique_vars t"
  using emv_subst_vars_term [OF assms]
  apply (simp add: num_unique_vars_def)
  by (metis card_image_le finite_vars_term)

lemma emv_subsumeseq_term_imp_num_unique_vars_le:
  assumes "emv s t"
    and "s \<cdot>\<ge> t"
  shows "num_unique_vars s \<le> num_unique_vars t"
  using assms(2) and emv_subst_imp_num_unique_vars_le [OF assms(1)] by (cases) simp

lemma num_syms_geq_num_vars:
  "num_syms t \<ge> num_vars t"
proof (induct t)
  case (Fun f ts)
  with sum_list_mono [of ts num_vars num_syms]
  have "sum_list (map num_vars ts) \<le> sum_list (map num_syms ts)" by simp
  then show ?case by simp
qed simp

lemma num_unique_vars_Fun_Cons:
  "num_unique_vars (Fun f (t # ts)) \<le> num_unique_vars t + num_unique_vars (Fun f ts)"
  apply (simp_all add: num_unique_vars_def)
  unfolding card_Un_Int [OF finite_vars_term finite_Union_vars_term]
  apply simp
  done

lemma sum_list_map_unique_vars:
  "sum_list (map num_unique_vars ts) \<ge> num_unique_vars (Fun f ts)"
proof (induct ts)
  case (Cons t ts)
  with num_unique_vars_Fun_Cons [of f t ts]
  show ?case by simp
qed (simp add: num_unique_vars_def)

lemma num_unique_vars_Var_1 [simp]:
  "num_unique_vars (Var x) = 1"
  by (simp_all add: num_unique_vars_def)

lemma num_vars_geq_num_unique_vars:
  "num_vars t \<ge> num_unique_vars t"
proof -
  note * =
    sum_list_mono [of _ num_unique_vars num_vars, THEN sum_list_map_unique_vars [THEN le_trans]]
  show ?thesis by (induct t) (auto intro: *)
qed

lemma num_syms_ge_num_unique_vars:
  "num_syms t \<ge> num_unique_vars t"
  by (metis le_trans num_syms_geq_num_vars num_vars_geq_num_unique_vars)

lemma num_syms_num_unique_vars_clash:
  assumes "\<forall>i. num_syms (f i) = num_syms (f (Suc i))"
    and "\<forall>i. num_unique_vars (f i) < num_unique_vars (f (Suc i))"
  shows False
proof -
  have *: "\<forall>i j. i \<le> j \<longrightarrow> num_syms (f i) = num_syms (f j)"
  proof (intro allI impI)
    fix i j :: nat
    assume "i \<le> j"
    then show "num_syms (f i) = num_syms (f j)"
      using assms(1)
      apply (induct "j - i" arbitrary: i)
       apply auto
      by (metis Suc_diff_diff diff_zero less_eq_Suc_le order.not_eq_order_implies_strict)
  qed
  have "\<exists>i. num_unique_vars (f i) \<ge> num_syms (f 0)"
    using inc_seq_greater [OF assms(2), of "num_syms (f 0)"] by (metis nat_less_le)
  then obtain i where "num_unique_vars (f i) \<ge> num_syms (f 0)" by auto
  with * and assms(2) have "num_unique_vars (f (Suc i)) > num_syms (f (Suc i))"
    by (metis le0 le_antisym num_syms_ge_num_unique_vars)
  then show False
    by (metis less_Suc_eq_le not_less_eq num_syms_ge_num_unique_vars)
qed

lemma emv_subst_imp_is_Var:
  assumes "emv s t"
    and "s = t \<cdot> \<sigma>"
  shows "\<forall>x \<in> vars_term t. is_Var (\<sigma> x)"
  using assms
  apply (induct)
   apply auto
  by (metis in_set_conv_nth)

lemma bij_Var_subst_compose_Var:
  assumes "bij g"
  shows "(Var \<circ> g) \<circ>\<^sub>s (Var \<circ> inv g) = Var"
proof
  fix x
  show "((Var \<circ> g) \<circ>\<^sub>s (Var \<circ> inv g)) x = Var x"
    using assms
    apply (auto simp: subst_compose_def)
    by (metis UNIV_I bij_is_inj inv_into_f_f)
qed

subsection \<open>Well-foundedness\<close>

lemma wf_subsumes:
  "wf ({<\<cdot>} :: ('f, 'v) term rel)"
proof (rule ccontr)
  assume "\<not> ?thesis"
  then obtain f :: "('f, 'v) term seq"
    where strict: "\<forall>i. f i \<cdot>> f (Suc i)"
    by (metis mem_Collect_eq case_prodD wf_iff_no_infinite_down_chain)
  then have *: "\<forall>i. f i \<cdot>\<ge> f (Suc i)" by (metis term_subsumable.subsumption.less_imp_le)
  then have "\<forall>i. num_syms (f i) \<ge> num_syms (f (Suc i))"
    by (auto simp: subsumeseq_term_iff) (metis num_syms_subst)
  from down_chain_imp_eq [OF this] obtain N
    where N_syms: "\<forall>i > N. num_syms (f i) = num_syms (f (Suc i))" ..
  define g where "g i = f (i + N)" for i
  from * have "\<forall>i. num_funs (g i) \<ge> num_funs (g (Suc i))"
    by (auto simp: subsumeseq_term_iff g_def) (metis num_funs_subst)
  from down_chain_imp_eq [OF this] obtain K
    where K_funs: "\<forall>i > K. num_funs (g i) = num_funs (g (Suc i))" ..
  define M where "M = max K N"
  have strict_g: "\<forall>i > M. g i \<cdot>> g (Suc i)" using strict by (simp add: g_def M_def)
  have g: "\<forall>i > M. g i \<cdot>\<ge> g (Suc i)" using * by (simp add: g_def M_def)
  moreover have "\<forall>i > M. num_funs (g i) = num_funs (g (Suc i))"
    using K_funs unfolding M_def by (metis max_less_iff_conj)
  moreover have syms: "\<forall>i > M. num_syms (g i) = num_syms (g (Suc i))"
    using N_syms unfolding M_def g_def
    by (metis add_Suc_right add_lessD1 add_strict_left_mono add.commute)
  ultimately have emv: "\<forall>i > M. emv (g i) (g (Suc i))" by (metis subsumeseq_term_size_emv)
  then have "\<forall>i > M. num_unique_vars (g (Suc i)) \<ge> num_unique_vars (g i)"
    using emv_subsumeseq_term_imp_num_unique_vars_le and g by fast
  then obtain i where "i > M"
    and nuv: "num_unique_vars (g (Suc i)) = num_unique_vars (g i)"
    using num_syms_num_unique_vars_clash [of "\<lambda>i. g (i + Suc M)"] and syms
    by (metis add_Suc_right add_Suc_shift le_eq_less_or_eq less_add_Suc2)
  define s and t where "s = g i" and "t = g (Suc i)"
  from nuv have card: "card (vars_term s) = card (vars_term t)"
    by (simp add: num_unique_vars_def s_def t_def)
  from g [THEN spec, THEN mp, OF \<open>i > M\<close>] obtain \<sigma>
    where "s = t \<cdot> \<sigma>" by (cases) (auto simp: s_def t_def)
  then have "emv s t" and "vars_term s = (the_Var \<circ> \<sigma>) ` vars_term t"
    using emv_subst_vars_term [of s t \<sigma>] and emv and \<open>i > M\<close> by (auto simp: s_def t_def)
  with card have "card ((the_Var \<circ> \<sigma>) ` vars_term t) = card (vars_term t)" by simp
  from finite_card_eq_imp_bij_betw [OF finite_vars_term this]
  have "bij_betw (the_Var \<circ> \<sigma>) (vars_term t) ((the_Var \<circ> \<sigma>) ` vars_term t)" .

  from bij_betw_extend [OF this, of UNIV]
  obtain h where *: "\<forall>x\<in>vars_term t. h x = (the_Var \<circ> \<sigma>) x"
    and "finite {x. h x \<noteq> x}"
    and "bij h" by auto
  have "\<forall>x\<in>vars_term t. (Var \<circ> h) x = \<sigma> x"
  proof
    fix x
    assume "x \<in> vars_term t"
    with * have "h x = (the_Var \<circ> \<sigma>) x" by simp
    with emv_subst_imp_is_Var [OF \<open>emv s t\<close> \<open>s = t \<cdot> \<sigma>\<close>] \<open>x \<in> vars_term t\<close>
    show "(Var \<circ> h) x = \<sigma> x" by simp
  qed
  then have "t \<cdot> (Var \<circ> h) = s"
    using \<open>s = t \<cdot> \<sigma>\<close> by (auto simp: term_subst_eq_conv)
  then have "t \<cdot> (Var \<circ> h) \<circ>\<^sub>s (Var \<circ> inv h) = s \<cdot> (Var \<circ> inv h)" by auto
  then have "t = s \<cdot> (Var \<circ> inv h)"
    unfolding bij_Var_subst_compose_Var [OF \<open>bij h\<close>] by simp
  then have "t \<cdot>\<ge> s" by auto
  with strict_g and \<open>i > M\<close> show False by (auto simp: s_def t_def term_subsumable.subsumes_def)
qed

end
