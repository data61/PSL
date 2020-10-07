(* Title:      Relation Algebra
   Author:     Alasdair Armstrong, Simon Foster, Georg Struth, Tjark Weber
   Maintainer: Georg Struth <g.struth at sheffield.ac.uk>
               Tjark Weber <tjark.weber at it.uu.se>
*)

section \<open>Models of Relation Algebra\<close>

theory Relation_Algebra_Models
  imports Relation_Algebra Kleene_Algebra.Inf_Matrix
begin

text \<open>We formalise two models. First we show the obvious: binary relations
form a relation algebra. Then we show that infinite matrices (which we
formalised originally for Kleene algebras) form models of relation algebra if
we restrict their element type to @{typ bool}.\<close>

subsection \<open>Binary Relations\<close>

text \<open>Since Isabelle's libraries for binary relations are very well
developed, the proof for this model is entirely trivial.\<close>

interpretation rel_relation_algebra: relation_algebra "(-)" uminus "(\<inter>)" "(\<subseteq>)" "(\<subset>)" "(\<union>)" "{}" UNIV "(O)" Relation.converse Id
by unfold_locales auto

subsection \<open>Infinite Boolean Matrices\<close>

text \<open>Next we consider infinite Boolean matrices. We define the maximal
Boolean matrix (all of its entries are @{const True}), the converse or
transpose of a matrix, the intersection of two Boolean matrices and the
complement of a Boolean matrix.\<close>

definition mat_top :: "('a, 'b, bool) matrix" ("\<tau>")
  where "\<tau> i j \<equiv> True"

definition mat_transpose :: "('a, 'b, 'c) matrix \<Rightarrow> ('b, 'a, 'c) matrix" ("_\<^sup>\<dagger>" [101] 100)
  where "f\<^sup>\<dagger> \<equiv> (\<lambda>i j. f j i)"

definition mat_inter :: "('a, 'b, bool) matrix \<Rightarrow> ('a, 'b, bool) matrix \<Rightarrow> ('a, 'b, bool) matrix" (infixl "\<sqinter>" 70)
  where "f \<sqinter> g \<equiv> (\<lambda>i j. f i j \<cdot> g i j)"

definition mat_complement :: "('a, 'b, bool) matrix \<Rightarrow> ('a, 'b, bool) matrix" ("_\<^sup>c" [101] 100)
  where "f\<^sup>c = (\<lambda>i j. - f i j)"

text \<open>Next we show that the Booleans form a dioid. We state this as an
\emph{instantiation} result. The Kleene algebra files contain an
\emph{interpretation} proof, which is not sufficient for our purposes.\<close>

instantiation bool :: dioid_one_zero
begin

  definition zero_bool_def:
    "zero_bool \<equiv> False"

  definition one_bool_def:
    "one_bool \<equiv> True"

  definition times_bool_def:
    "times_bool \<equiv> (\<and>)"

  definition plus_bool_def:
    "plus_bool \<equiv> (\<or>)"

  instance
  by standard (auto simp: plus_bool_def times_bool_def one_bool_def zero_bool_def)

end

text \<open>We now show that infinite Boolean matrices form a Boolean algebra.\<close>

lemma le_funI2: "(\<And>i j. f i j \<le> g i j) \<Longrightarrow> f \<le> g"
by (metis le_funI)

interpretation matrix_ba: boolean_algebra "\<lambda>f g. f \<sqinter> g\<^sup>c" mat_complement "(\<sqinter>)" "(\<le>)" "(<)" mat_add mat_zero mat_top
by standard (force intro!: le_funI simp: mat_inter_def plus_bool_def mat_add_def mat_zero_def zero_bool_def mat_top_def mat_complement_def)+

text \<open>We continue working towards the main result of this section, that
infinite Boolean matrices form a relation algebra.\<close>

lemma mat_mult_var: "(f \<otimes> g) = (\<lambda>i j. \<Sum> {(f i k) * (g k j) | k. k \<in> UNIV})"
by (rule ext)+ (simp add: mat_mult_def)

text \<open>The following fact is related to proving the last relation algebra
axiom in the matrix model. It is more complicated than necessary since finite
infima are not well developed in Isabelle. Instead we translate properties of
finite infima into properties of finite suprema by using Boolean algebra. For
finite suprema we have developed special-purpose theorems in the Kleene algebra
files.\<close>

lemma mat_res_pointwise:
  fixes i j :: "'a::finite"
    and x :: "('a, 'a, bool) matrix"
  shows "(x\<^sup>\<dagger> \<otimes> (x \<otimes> y)\<^sup>c) i j \<le> (y\<^sup>c) i j"
proof -
  have "\<Sum>{(x\<^sup>\<dagger>) i k \<and> ((x \<otimes> y)\<^sup>c) k j |k. k \<in> UNIV} \<le> (y\<^sup>c) i j \<longleftrightarrow> (\<forall>k. ((x\<^sup>\<dagger>) i k \<and> ((x \<otimes> y)\<^sup>c) k j) \<le> (y\<^sup>c) i j)"
    by (subst sum_sup) auto
  also have "\<dots> \<longleftrightarrow> (\<forall>k. ((x\<^sup>\<dagger>) i k \<and> - (x \<otimes> y) k j) \<le> (y\<^sup>c) i j)"
    by (simp only: mat_complement_def)
  also have "\<dots> \<longleftrightarrow> (\<forall>k. (x\<^sup>\<dagger>) i k \<le> ((y\<^sup>c) i j \<or> (x \<otimes> y) k j))"
    by auto
  also have "\<dots> \<longleftrightarrow> (\<forall>k. (x\<^sup>\<dagger>) i k \<le> (- y i j \<or> (x \<otimes> y) k j))"
    by (simp only: mat_complement_def)
  also have "\<dots> \<longleftrightarrow> (\<forall>k. ((x\<^sup>\<dagger>) i k \<and> y i j) \<le> (x \<otimes> y) k j)"
    by auto
  also have "\<dots> \<longleftrightarrow> (\<forall>k. (x k i \<and> y i j) \<le> (x \<otimes> y) k j)"
    by (simp add: mat_transpose_def)
  also have "\<dots> \<longleftrightarrow> (\<forall>k. (x k i \<and> y i j) \<le> \<Sum>{x k l \<and> y l j |l. l \<in> UNIV})"
    by (simp add: mat_mult_def times_bool_def)
  also have "\<dots> \<longleftrightarrow> (\<forall>k. \<Sum>{x k i \<and> y i j} \<le> \<Sum>{x k l \<and> y l j |l. l \<in> UNIV})"
    by simp
  also have "\<dots> \<longleftrightarrow> True"
    by (intro iffI TrueI allI sum_intro[rule_format]) auto
  moreover have "(x\<^sup>\<dagger> \<otimes> (x \<otimes> y)\<^sup>c) i j = \<Sum>{(x\<^sup>\<dagger>) i k \<and> ((x \<otimes> y)\<^sup>c) k j |k. k \<in> UNIV}"
    by (subst mat_mult_def) (simp add: times_bool_def)
  ultimately show ?thesis
    by auto
qed

text \<open>Finally the main result of this section.\<close>

interpretation matrix_ra: relation_algebra "\<lambda>f g. f \<sqinter> g\<^sup>c" mat_complement "(\<sqinter>)" "(\<le>)" "(<)" "(\<oplus>)" "\<lambda>i j. False" \<tau> "(\<otimes>)" mat_transpose \<epsilon>
proof
  fix x y z :: "'a::finite \<Rightarrow> 'a \<Rightarrow> bool"
  show "(\<lambda>(i::'a) j::'a. False) \<le> x"
    by (metis predicate2I)
  show "x \<sqinter> x\<^sup>c = (\<lambda>i j. False)"
    by (metis matrix_ba.bot.extremum matrix_ba.inf_compl_bot rev_predicate2D)
  show "x \<oplus> x\<^sup>c = \<tau>"
    by (fact matrix_ba.sup_compl_top)
  show "x \<sqinter> y\<^sup>c = x \<sqinter> y\<^sup>c"
    by (fact refl)
  show "x \<otimes> y \<otimes> z = x \<otimes> (y \<otimes> z)"
    by (metis mat_mult_assoc)
  show "x \<otimes> \<epsilon> = x"
    by (fact mat_oner)
  show "x \<oplus> y \<otimes> z = (x \<otimes> z) \<oplus> (y \<otimes> z)"
    by (fact mat_distr)
  show "(x\<^sup>\<dagger>)\<^sup>\<dagger> = x"
    by (simp add: mat_transpose_def)
  show "(x \<oplus> y)\<^sup>\<dagger> = x\<^sup>\<dagger> \<oplus> y\<^sup>\<dagger>"
    by (simp add: mat_transpose_def mat_add_def)
  show "(x \<otimes> y)\<^sup>\<dagger> = y\<^sup>\<dagger> \<otimes> x\<^sup>\<dagger>"
    by (simp add: mat_transpose_def mat_mult_var times_bool_def conj_commute)
  show "x\<^sup>\<dagger> \<otimes> (x \<otimes> y)\<^sup>c \<le> y\<^sup>c"
    by (metis le_funI2 mat_res_pointwise)
qed

end

