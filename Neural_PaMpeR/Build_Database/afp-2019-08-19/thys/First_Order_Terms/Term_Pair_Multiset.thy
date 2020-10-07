(*
Author:  Christian Sternagel <c.sternagel@gmail.com>
Author:  René Thiemann <rene.thiemann@uibk.ac.at>
License: LGPL
*)
subsection \<open>Multisets of Pairs of Terms\<close>

theory Term_Pair_Multiset
  imports
    Term
    "HOL-Library.Multiset"
begin

text \<open>Multisets of pairs of terms are used in abstract inference systems for
matching and unification.\<close>


subsection \<open>Size\<close>

text \<open>Make sure that every pair has size at least @{term "1::nat"}.\<close>
definition "pair_size p = size (fst p) + size (snd p) + 1"

text \<open>Compute the number of symbols in a multiset of term pairs.\<close>
definition "size_mset M = fold_mset ((+) \<circ> pair_size) 0 M"

interpretation size_mset_fun:
  comp_fun_commute "(+) \<circ> pair_size"
  by standard auto

lemma fold_pair_size_plus:
  "fold_mset ((+) \<circ> pair_size) 0 M + n = fold_mset ((+) \<circ> pair_size) n M"
  by (induct M arbitrary: n) (simp add: size_mset_def)+

lemma size_mset_union [simp]:
  "size_mset (M + N) = size_mset N + size_mset M"
  by (auto simp: size_mset_def fold_pair_size_plus)

lemma size_mset_add_mset [simp]:
  "size_mset (add_mset x M) = pair_size x + (size_mset M)"
by (auto simp: size_mset_def)

lemma nonempty_size_mset [simp]:
  assumes "M \<noteq> {#}"
  shows "size_mset M > 0"
  using assms by (induct M) (simp add: size_mset_def pair_size_def)+

lemma size_mset_singleton [simp]:
  "size_mset {#(l, r)#} = size l + size r + 1"
  by (auto simp: size_mset_def pair_size_def)

lemma size_mset_empty [simp]:
  "size_mset {#} = 0"
  by (auto simp: size_mset_def)

lemma size_mset_set_zip_leq:
  "size_mset (mset (zip ss ts)) \<le> size_list size ss + size_list size ts"
proof (induct ss arbitrary: ts)
  case (Cons s ss)
  then show ?case
    by (cases ts) (auto intro: le_SucI simp: pair_size_def)
qed simp

lemma size_mset_Fun_less:
  "size_mset {#(Fun f ss, Fun g ts)#} > size_mset (mset (zip ss ts))"
  by (auto simp: pair_size_def intro: order_le_less_trans size_mset_set_zip_leq)

lemma decomp_size_mset_less:
  assumes "length ss = length ts"
  shows "size_mset (M + mset (zip ss ts)) < size_mset (M + {#(Fun f ss, Fun f ts)#})"
  using assms and size_mset_Fun_less [of ss ts f f] by simp


subsubsection \<open>Substitutions\<close>

text \<open>Applying a substitution to a multiset of term pairs.\<close>
definition "subst_mset \<sigma> M = image_mset (\<lambda>p. (fst p \<cdot> \<sigma>, snd p \<cdot> \<sigma>)) M"
lemma subst_mset_empty [simp]:
  "subst_mset \<sigma> {#} = {#}"
  by (auto simp: subst_mset_def)

lemma subst_mset_union:
  "subst_mset \<sigma> (M + N) = subst_mset \<sigma> M + subst_mset \<sigma> N"
  by (auto simp: subst_mset_def)

lemma subst_mset_Var [simp]:
  "subst_mset Var M = M"
  by (auto simp: subst_mset_def)

lemma subst_mset_subst_compose [simp]:
  "subst_mset (\<sigma> \<circ>\<^sub>s \<tau>) M = subst_mset \<tau> (subst_mset \<sigma> M)"
  by (simp add: subst_mset_def image_mset.compositionality o_def)


subsubsection \<open>Variables\<close>

text \<open>Compute the set of variables occurring in a multiset of term pairs.\<close>
definition "vars_mset M = \<Union>(set_mset (image_mset (\<lambda>r. vars_term (fst r) \<union> vars_term (snd r)) M))"

lemma vars_mset_singleton [simp]:
  "vars_mset {#p#} = vars_term (fst p) \<union> vars_term (snd p)"
  by (auto simp: vars_mset_def)

lemma vars_mset_union [simp]:
  "vars_mset (A + B) = vars_mset A \<union> vars_mset B"
  by (auto simp: vars_mset_def)

lemma vars_mset_add_mset [simp]:
  "vars_mset (add_mset x M) = vars_term (fst x) \<union> vars_term (snd x) \<union> vars_mset M"
  by (auto simp: vars_mset_def)

lemma vars_mset_set_zip [simp]:
  assumes "length xs = length ys"
  shows "vars_mset (mset (zip xs ys)) = (\<Union>x\<in>set xs \<union> set ys. vars_term x)"
  using assms by (induct xs ys rule: list_induct2) (auto simp: vars_mset_def)

lemma not_in_vars_mset_subst_mset [simp]:
  assumes "x \<notin> vars_term t"
  shows "x \<notin> vars_mset (subst_mset (subst x t) M)"
  using assms by (auto simp: vars_mset_def subst_mset_def vars_term_subst subst_def)
lemma vars_mset_subst_mset_subset:
  "vars_mset (subst_mset (subst x t) M) \<subseteq> vars_mset M \<union> vars_term t \<union> {x}" (is "?L \<subseteq> ?R")
proof
  fix y
  assume "y \<in> ?L"
  then obtain u v where "(u, v) \<in># M"
    and "y \<in> vars_term (u \<cdot> subst x t) \<union> vars_term (v \<cdot> subst x t)"
    by (auto simp: vars_mset_def subst_mset_def)
  moreover then have "y \<in> vars_term u \<union> vars_term v \<union> vars_term t"
    unfolding vars_term_subst subst_def fun_upd_def
    by (auto) (metis empty_iff)+
  ultimately show "y \<in> ?R" by (force simp: vars_mset_def)
qed

lemma Var_left_vars_mset_less:
  assumes "x \<notin> vars_term t"
  shows "vars_mset (subst_mset (subst x t) M) \<subset> vars_mset (add_mset (Var x, t) M)" (is "?L \<subset> ?R")
proof
  show "?L \<subseteq> ?R" using vars_mset_subst_mset_subset [of x t M] by (simp add: ac_simps)
next
  have "x \<in> ?R" using assms by (force simp: vars_mset_def)
  moreover have "x \<notin> ?L" using assms by simp
  ultimately show "?L \<noteq> ?R" by blast
qed

lemma Var_right_vars_mset_less:
  assumes "x \<notin> vars_term t"
  shows "vars_mset (subst_mset (subst x t) M) \<subset> vars_mset (add_mset (t, Var x) M)"
  using Var_left_vars_mset_less [OF assms] by simp

lemma mem_vars_mset_subst_mset:
  assumes "y \<in> vars_mset (subst_mset (subst x t) M)"
    and "y \<noteq> x"
    and "y \<notin> vars_term t"
  shows "y \<in> vars_mset M"
  using vars_mset_subst_mset_subset [of x t M] and assms by blast

lemma finite_vars_mset:
  "finite (vars_mset A)"
  by (auto simp: vars_mset_def)

end