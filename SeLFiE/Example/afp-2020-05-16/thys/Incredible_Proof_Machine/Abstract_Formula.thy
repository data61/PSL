theory Abstract_Formula
imports
  Main
  "HOL-Library.FSet"
  "HOL-Library.Stream"
  Indexed_FSet
begin

text \<open>
The following locale describes an abstract interface for a set of formulas, without fixing the
concret shape, or set of variables.

The variables mentioned in this locale are only the @{emph \<open>locally fixed constants\<close>} occurring in
formulas, e.g.\@ in the introduction rule for the universal quantifier. Normal variables are not
something we care about at this point; they are handled completely abstractly by the abstract notion
of a substitution.
\<close>

locale Abstract_Formulas =
  \<comment> \<open>Variables can be renamed injectively\<close>
  fixes freshenLC :: "nat \<Rightarrow> 'var \<Rightarrow> 'var"
  \<comment> \<open>A variable-changing function can be mapped over a formula\<close>
  fixes renameLCs :: "('var \<Rightarrow> 'var) \<Rightarrow> ('form \<Rightarrow> 'form)"
  \<comment> \<open>The set of variables occurring in a formula\<close>
  fixes lconsts :: "'form \<Rightarrow> 'var set"
  \<comment> \<open>A closed formula has no variables, and substitions do not affect it.\<close>
  fixes closed :: "'form \<Rightarrow> bool"
  \<comment> \<open>A substitution can be applied to a formula.\<close>
  fixes subst :: "'subst \<Rightarrow> 'form \<Rightarrow> 'form"
  \<comment> \<open>The set of variables occurring (in the image) of a substitution.\<close>
  fixes subst_lconsts :: "'subst \<Rightarrow> 'var set"
  \<comment> \<open>A variable-changing function can be mapped over a substitution\<close>
  fixes subst_renameLCs :: "('var \<Rightarrow> 'var) \<Rightarrow> ('subst \<Rightarrow> 'subst)"
  \<comment> \<open>A most generic formula, can be substitutied to anything.\<close>
  fixes anyP :: "'form"

  assumes freshenLC_eq_iff[simp]: "freshenLC a v = freshenLC a' v' \<longleftrightarrow> a = a' \<and> v = v'"
  assumes lconsts_renameLCs: "lconsts (renameLCs p f) = p ` lconsts f"
  assumes rename_closed: "lconsts f = {} \<Longrightarrow> renameLCs p f = f"
  assumes subst_closed: "closed f \<Longrightarrow> subst s f = f"
  assumes closed_no_lconsts: "closed f \<Longrightarrow> lconsts f = {}"
  assumes fv_subst: "lconsts (subst s f) \<subseteq> lconsts f \<union> subst_lconsts s"
  assumes rename_rename: "renameLCs p1 (renameLCs p2 f) = renameLCs (p1 \<circ> p2) f"
  assumes rename_subst: "renameLCs p (subst s f) = subst (subst_renameLCs p s) (renameLCs p f)"
  assumes renameLCs_cong: "(\<And> x. x \<in> lconsts f \<Longrightarrow> f1 x = f2 x) \<Longrightarrow> renameLCs f1 f = renameLCs f2 f"
  assumes subst_renameLCs_cong: "(\<And> x. x \<in> subst_lconsts s \<Longrightarrow> f1 x = f2 x) \<Longrightarrow> subst_renameLCs f1 s = subst_renameLCs f2 s"
  assumes subst_lconsts_subst_renameLCs: "subst_lconsts (subst_renameLCs p s) = p ` subst_lconsts s"
  assumes lconsts_anyP: "lconsts anyP = {}"
  assumes empty_subst: "\<exists> s. (\<forall> f. subst s f = f) \<and> subst_lconsts s = {}"
  assumes anyP_is_any: "\<exists> s. subst s anyP = f"
begin
  definition freshen :: "nat \<Rightarrow> 'form \<Rightarrow> 'form" where
    "freshen n = renameLCs (freshenLC n)"

  definition empty_subst :: "'subst" where
    "empty_subst = (SOME s. (\<forall> f. subst s f = f) \<and> subst_lconsts s = {})"

  lemma empty_subst_spec:
    "(\<forall> f. subst empty_subst f = f) \<and> subst_lconsts empty_subst = {}"
    unfolding empty_subst_def using empty_subst by (rule someI_ex)
  lemma subst_empty_subst[simp]: "subst empty_subst f = f"
    by (metis empty_subst_spec)
  lemma subst_lconsts_empty_subst[simp]: "subst_lconsts empty_subst = {}"
    by (metis empty_subst_spec)

  lemma lconsts_freshen: "lconsts (freshen a f) = freshenLC a ` lconsts f"
    unfolding freshen_def by (rule lconsts_renameLCs)

  lemma freshen_closed: "lconsts f = {} \<Longrightarrow> freshen a f = f"
    unfolding freshen_def by (rule rename_closed)
    
  lemma closed_eq:
    assumes "closed f1"
    assumes "closed f2"
    shows "subst s1 (freshen a1 f1) = subst s2 (freshen a2 f2) \<longleftrightarrow> f1 = f2"
  using assms
    by (auto simp add: closed_no_lconsts freshen_def lconsts_freshen subst_closed rename_closed)

  lemma freshenLC_range_eq_iff[simp]: "freshenLC a v \<in> range (freshenLC a') \<longleftrightarrow> a = a'"
    by auto

  definition rerename :: "'var set \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> ('var \<Rightarrow> 'var) \<Rightarrow> ('var \<Rightarrow> 'var)" where
    "rerename V from to f x = (if x \<in> freshenLC from ` V then freshenLC to (inv (freshenLC from) x) else f x)"
  
  lemma inj_freshenLC[simp]: "inj (freshenLC i)"
    by (rule injI) simp
  
  lemma rerename_freshen[simp]: "x \<in> V \<Longrightarrow> rerename  V i (isidx is) f (freshenLC i x) = freshenLC (isidx is) x"
    unfolding rerename_def by simp

  lemma range_rerename: "range (rerename V  from to f) \<subseteq> freshenLC to ` V \<union> range f"
    by (auto simp add: rerename_def split: if_splits)

  lemma rerename_noop:
      "x \<notin> freshenLC from ` V  \<Longrightarrow> rerename V from to f x = f x"
    by (auto simp add: rerename_def split: if_splits)

  lemma rerename_rename_noop:
      "freshenLC from ` V \<inter> lconsts form  = {}  \<Longrightarrow> renameLCs (rerename V from to f) form = renameLCs f form"
      by (intro renameLCs_cong rerename_noop) auto

  lemma rerename_subst_noop:
      "freshenLC from ` V \<inter> subst_lconsts s  = {}  \<Longrightarrow> subst_renameLCs (rerename V from to f) s = subst_renameLCs f s"
      by (intro subst_renameLCs_cong rerename_noop) auto
end
end
