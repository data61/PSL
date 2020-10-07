section \<open>Refinement Lattice \label{S:lattice}\<close>

theory Refinement_Lattice
imports
  Main
  "HOL-Library.Lattice_Syntax"
begin

text \<open>
  The underlying lattice of commands is complete and distributive.
  We follow the refinement calculus tradition so that $\nondet$ 
  is non-deterministic choice and $c \refsto d$ means $c$ is refined 
  (or implemented) by $d$.
\<close>

declare [[show_sorts]]

text \<open>Remove existing notation for quotient as it interferes with the rely quotient\<close>
no_notation Equiv_Relations.quotient  (infixl "'/'/" 90)

class refinement_lattice = complete_distrib_lattice
begin

text \<open>The refinement lattice infimum corresponds to non-deterministic choice for commands.\<close>

abbreviation
  refine :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<sqsubseteq>" 50)
where
  "c \<sqsubseteq> d \<equiv> less_eq c d"

abbreviation
  refine_strict :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<sqsubset>" 50)
where
  "c \<sqsubset> d \<equiv> less c d"

text \<open>Non-deterministic choice is monotonic in both arguments\<close>
lemma inf_mono_left: "a \<sqsubseteq> b \<Longrightarrow> a \<sqinter> c \<sqsubseteq> b \<sqinter> c"
  using inf_mono by auto

lemma inf_mono_right: "c \<sqsubseteq> d \<Longrightarrow> a \<sqinter> c \<sqsubseteq> a \<sqinter> d"
  using inf_mono by auto

text \<open>Binary choice is a special case of choice over a set.\<close>
lemma Inf2_inf: "\<Sqinter>{ f x | x. x \<in> {c, d}} = f c \<sqinter> f d"
proof -
  have "{ f x | x. x \<in> {c, d}} = {f c, f d}" by blast
  then have "\<Sqinter>{ f x | x. x \<in> {c, d}} = \<Sqinter>{f c, f d}" by simp
  also have "... = f c \<sqinter> f d" by simp
  finally show ?thesis .
qed

text \<open>Helper lemma for choice over indexed set.\<close>
lemma INF_Inf: "(\<Sqinter>x\<in>X. f x) = (\<Sqinter>{f x |x. x \<in> X})"
  by (simp add: Setcompr_eq_image)

lemma (in -) INF_absorb_args: "(\<Sqinter>i j. (f::nat \<Rightarrow> 'c::complete_lattice) (i + j)) = (\<Sqinter>k. f k)"
proof (rule order_class.order.antisym)
  show "(\<Sqinter>k. f k) \<le> (\<Sqinter>i j. f (i + j))"
    by (simp add: complete_lattice_class.INF_lower complete_lattice_class.le_INF_iff)
next
  have "\<And>k. \<exists>i j. f (i + j) \<le> f k"
    by (metis add.left_neutral order_class.eq_iff)
  then have "\<And>k. \<exists>i. (\<Sqinter>j. f (i + j)) \<le> f k"
    by (meson UNIV_I complete_lattice_class.INF_lower2)
  then show "(\<Sqinter>i j. f (i + j)) \<le> (\<Sqinter>k. f k)"
    by (simp add: complete_lattice_class.INF_mono)
qed

lemma (in -) nested_Collect: "{f y |y. y \<in> {g x |x. x \<in> X}} = {f (g x) |x. x \<in> X}"
  by blast

text \<open>A transition lemma for INF distributivity properties, going from Inf to INF,
  qualified version followed by a straightforward one.\<close>

lemma Inf_distrib_INF_qual:
  fixes f :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
  assumes qual: "P {d x |x. x \<in> X}"
  assumes f_Inf_distrib: "\<And>c D. P D \<Longrightarrow> f c (\<Sqinter> D) = \<Sqinter> {f c d | d . d \<in> D }"
  shows "f c (\<Sqinter>x\<in>X. d x) = (\<Sqinter>x\<in>X. f c (d x))"
proof -
  have "f c (\<Sqinter>x\<in>X. d x) = f c (\<Sqinter>{d x |x. x \<in> X})" by (simp add: INF_Inf)
  also have "... = (\<Sqinter>{f c dx |dx. dx \<in> {d x | x. x \<in> X}})" by (simp add: qual f_Inf_distrib)
  also have "... = (\<Sqinter>{f c (d x) |x. x \<in> X})" by (simp only: nested_Collect)
  also have "... = (\<Sqinter>x\<in>X. f c (d x))" by (simp add: INF_Inf)
  finally show ?thesis .
qed

lemma Inf_distrib_INF:
  fixes f :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
  assumes f_Inf_distrib: "\<And>c D. f c (\<Sqinter> D) = \<Sqinter> {f c d | d . d \<in> D }"
  shows "f c (\<Sqinter>x\<in>X. d x) = (\<Sqinter>x\<in>X. f c (d x))"
  by (simp add: Setcompr_eq_image f_Inf_distrib image_comp)

    
end

lemmas refine_trans = order.trans

text \<open>More transitivity rules to make calculational reasoning smoother\<close>
declare ord_eq_le_trans[trans]
declare ord_le_eq_trans[trans]
declare dual_order.trans[trans]


abbreviation
  dist_over_sup :: "('a::refinement_lattice \<Rightarrow> 'a) \<Rightarrow> bool"
where
  "dist_over_sup F \<equiv> (\<forall> X . F (\<Squnion> X) = (\<Squnion>x\<in>X. F (x)))"

abbreviation
  dist_over_inf :: "('a::refinement_lattice \<Rightarrow> 'a) \<Rightarrow> bool"
where
  "dist_over_inf F \<equiv> (\<forall> X . F (\<Sqinter> X) = (\<Sqinter>x\<in>X. F (x)))"

end
