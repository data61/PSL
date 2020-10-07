section \<open>Deep embedding of Pure terms into term-rewriting logic\<close>

theory Embed
imports
  Constructor_Funs.Constructor_Funs
  "../Utils/Code_Utils"
  Eval_Class
keywords "embed" :: thy_decl
begin

fun non_overlapping' :: "term \<Rightarrow> term \<Rightarrow> bool" where
"non_overlapping' (Const x) (Const y) \<longleftrightarrow> x \<noteq> y" |
"non_overlapping' (Const _) (_ $ _) \<longleftrightarrow> True" |
"non_overlapping' (_ $ _) (Const _) \<longleftrightarrow> True" |
"non_overlapping' (t\<^sub>1 $ t\<^sub>2) (u\<^sub>1 $ u\<^sub>2) \<longleftrightarrow> non_overlapping' t\<^sub>1 u\<^sub>1 \<or> non_overlapping' t\<^sub>2 u\<^sub>2" |
"non_overlapping' _ _ \<longleftrightarrow> False"

lemma non_overlapping_approx:
  assumes "non_overlapping' t u"
  shows "non_overlapping t u"
using assms
by (induct t u rule: non_overlapping'.induct) fastforce+

fun pattern_compatible' :: "term \<Rightarrow> term \<Rightarrow> bool" where
"pattern_compatible' (t\<^sub>1 $ t\<^sub>2) (u\<^sub>1 $ u\<^sub>2) \<longleftrightarrow> pattern_compatible' t\<^sub>1 u\<^sub>1 \<and> (t\<^sub>1 = u\<^sub>1 \<longrightarrow> pattern_compatible' t\<^sub>2 u\<^sub>2)" |
"pattern_compatible' t u \<longleftrightarrow> t = u \<or> non_overlapping' t u"

lemma pattern_compatible_approx:
  assumes "pattern_compatible' t u"
  shows "pattern_compatible t u"
using assms
proof (induction t u rule: pattern_compatible.induct)
  case "2_1" (* FIXME intro rule setup for non_overlapping is broken *)
  thus ?case
    by (force simp: non_overlapping_approx)
next
  case "2_5"
  thus ?case
    by (force simp: non_overlapping_approx)
qed auto

abbreviation pattern_compatibles' :: "(term \<times> 'a) fset \<Rightarrow> bool" where
"pattern_compatibles' \<equiv> fpairwise (\<lambda>(lhs\<^sub>1, _) (lhs\<^sub>2, _). pattern_compatible' lhs\<^sub>1 lhs\<^sub>2)"

definition rules' :: "C_info \<Rightarrow> rule fset \<Rightarrow> bool" where
"rules' C_info rs \<longleftrightarrow>
  fBall rs rule \<and>
  arity_compatibles rs \<and>
  is_fmap rs \<and>
  pattern_compatibles' rs \<and>
  rs \<noteq> {||} \<and>
  fBall rs (\<lambda>(lhs, _). \<not> pre_constants.shadows_consts C_info (heads_of rs) lhs) \<and>
  fdisjnt (heads_of rs) (constructors.C C_info) \<and>
  fBall rs (\<lambda>(_, rhs). pre_constants.welldefined C_info (heads_of rs) rhs) \<and>
  distinct (constructors.all_constructors C_info)"

lemma rules_approx:
  assumes "rules' C_info rs"
  shows "rules C_info rs"
proof
  show "fBall rs rule" "arity_compatibles rs" "is_fmap rs" "rs \<noteq> {||}"
   and "fBall rs (\<lambda>(lhs, _). \<not> pre_constants.shadows_consts C_info (heads_of rs) lhs)"
   and "fBall rs (\<lambda>(_, rhs). pre_constants.welldefined C_info (heads_of rs) rhs)"
   and "fdisjnt (heads_of rs) (constructors.C C_info)"
   and "distinct (constructors.all_constructors C_info)"
    using assms unfolding rules'_def by simp+
next
  have "pattern_compatibles' rs"
    using assms unfolding rules'_def by simp
  thus "pattern_compatibles rs"
    by (rule fpairwise_weaken) (blast intro: pattern_compatible_approx)
qed

lemma embed_ext: "f \<equiv> g \<Longrightarrow> f x \<equiv> g x"
by auto

ML_file "embed.ML"

consts "lift_term" :: "'a \<Rightarrow> term" ("\<langle>_\<rangle>")

setup\<open>
  let
    fun embed ((Const (@{const_name lift_term}, _)) $ t) = HOL_Term.mk_term false t
      | embed (t $ u) = embed t $ embed u
      | embed t = t
  in Context.theory_map (Syntax_Phases.term_check 99 "lift" (K (map embed))) end
\<close>

end