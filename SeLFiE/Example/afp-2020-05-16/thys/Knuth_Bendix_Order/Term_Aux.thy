section \<open>Auxiliaries\<close>

theory Term_Aux
  imports
    Subterm_and_Context
    "HOL-Library.Multiset"
begin

text \<open>
  This theory contains material about terms that is required for KBO, 
  but does not belong to @{theory Knuth_Bendix_Order.Subterm_and_Context}.

  We plan to merge this material into the theory @{theory First_Order_Terms.Term}
  at some point.
\<close>

text \<open>The variables of a term as multiset.\<close>
fun vars_term_ms :: "('f, 'v) term \<Rightarrow> 'v multiset"
  where
    "vars_term_ms (Var x) = {#x#}" |
    "vars_term_ms (Fun f ts) = \<Union># (mset (map vars_term_ms ts))"

lemma vars_term_ms_subst [simp]:
  "vars_term_ms (t \<cdot> \<sigma>) =
    \<Union># (image_mset (\<lambda> x. vars_term_ms (\<sigma> x)) (vars_term_ms t))" (is "_ = ?V t")
proof (induct t)
  case (Fun f ts)
  have IH: "map (\<lambda> t. vars_term_ms (t \<cdot> \<sigma>)) ts = map (\<lambda> t. ?V t) ts"
    by (rule map_cong[OF refl Fun])
  show ?case by (simp add: o_def IH, induct ts, auto)
qed simp

lemma vars_term_ms_subst_mono:
  assumes "vars_term_ms s \<subseteq># vars_term_ms t"
  shows "vars_term_ms (s \<cdot> \<sigma>) \<subseteq># vars_term_ms (t \<cdot> \<sigma>)"
proof -
  from assms[unfolded mset_subset_eq_exists_conv] obtain u where t: "vars_term_ms t = vars_term_ms s + u" by auto
  show ?thesis unfolding vars_term_ms_subst unfolding t by auto
qed

lemma set_mset_vars_term_ms [simp]:
  "set_mset (vars_term_ms t) = vars_term t"
  by (induct t) auto

text \<open>A term is called \<^emph>\<open>ground\<close> if it does not contain any variables.\<close>
fun ground :: "('f, 'v) term \<Rightarrow> bool"
  where
    "ground (Var x) \<longleftrightarrow> False" |
    "ground (Fun f ts) \<longleftrightarrow> (\<forall>t \<in> set ts. ground t)"

lemma ground_vars_term_empty:
  "ground t \<longleftrightarrow> vars_term t = {}"
  by (induct t) simp_all

lemma ground_subst [simp]:
  "ground (t \<cdot> \<sigma>) \<longleftrightarrow> (\<forall>x \<in> vars_term t. ground (\<sigma> x))"
  by (induct t) simp_all

lemma ground_subst_apply:
  assumes "ground t"
  shows "t \<cdot> \<sigma> = t"
proof -
  have "t = t \<cdot> Var" by simp
  also have "\<dots> = t \<cdot> \<sigma>"
    by (rule term_subst_eq, insert assms[unfolded ground_vars_term_empty], auto)
  finally show ?thesis by simp
qed

text \<open>
  A \<^emph>\<open>signature\<close> is a set of function symbol/arity pairs, where the arity of a function symbol,
  denotes the number of arguments it expects.
\<close>
type_synonym 'f sig = "('f \<times> nat) set"

text \<open>The set of all function symbol/ arity pairs occurring in a term.\<close>
fun funas_term :: "('f, 'v) term \<Rightarrow> 'f sig"
  where
    "funas_term (Var _) = {}" |
    "funas_term (Fun f ts) = {(f, length ts)} \<union> \<Union>(set (map funas_term ts))"


lemma supt_imp_funas_term_subset:
  assumes "s \<rhd> t"
  shows "funas_term t \<subseteq> funas_term s"
  using assms by (induct) auto

lemma supteq_imp_funas_term_subset[simp]:
  assumes "s \<unrhd> t"
  shows "funas_term t \<subseteq> funas_term s"
  using assms by (induct) auto

text \<open>The set of all function symbol/arity pairs occurring in a context.\<close>
fun funas_ctxt :: "('f, 'v) ctxt \<Rightarrow> 'f sig"
  where
    "funas_ctxt Hole = {}" |
    "funas_ctxt (More f ss1 D ss2) = {(f, Suc (length (ss1 @ ss2)))}
     \<union> funas_ctxt D \<union> \<Union>(set (map funas_term (ss1 @ ss2)))"

lemma funas_term_ctxt_apply [simp]:
  "funas_term (C\<langle>t\<rangle>) = funas_ctxt C \<union> funas_term t"
proof (induct t)
  case (Var x) show ?case by (induct C) auto
next
  case (Fun f ts) show ?case by (induct C arbitrary: f ts) auto
qed

lemma funas_term_subst:
  "funas_term (t \<cdot> \<sigma>) = funas_term t \<union> \<Union>(funas_term ` \<sigma> ` vars_term t)"
  by (induct t) auto

lemma funas_ctxt_compose [simp]:
  "funas_ctxt (C \<circ>\<^sub>c D) = funas_ctxt C \<union> funas_ctxt D"
  by (induct C) auto

lemma funas_ctxt_subst [simp]:
  "funas_ctxt (C \<cdot>\<^sub>c \<sigma>) = funas_ctxt C \<union> \<Union>(funas_term ` \<sigma> ` vars_ctxt C)"
  by (induct C, auto simp: funas_term_subst)

end
