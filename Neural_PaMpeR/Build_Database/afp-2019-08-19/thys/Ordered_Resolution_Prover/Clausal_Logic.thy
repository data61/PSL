(* Title:        Clausal Logic
    Author:      Jasmin Blanchette <j.c.blanchette at vu.nl>, 2014, 2017
    Author:      Dmitriy Traytel <traytel at inf.ethz.ch>, 2014
    Author:      Mathias Fleury <mathias.fleury at mpi-inf.mpg.de>, 2014
    Maintainer:  Jasmin Blanchette <jasmin.blanchette at inria.fr>
*)

section \<open>Clausal Logic\<close>

theory Clausal_Logic
  imports Nested_Multisets_Ordinals.Multiset_More
begin

text \<open>
Resolution operates of clauses, which are disjunctions of literals. The material formalized here
corresponds roughly to Sections 2.1 (``Formulas and Clauses'') of Bachmair and Ganzinger, excluding
the formula and term syntax.
\<close>


subsection \<open>Literals\<close>

text \<open>
Literals consist of a polarity (positive or negative) and an atom, of type @{typ 'a}.
\<close>

datatype 'a literal =
  is_pos: Pos (atm_of: 'a)
| Neg (atm_of: 'a)

abbreviation is_neg :: "'a literal \<Rightarrow> bool" where
  "is_neg L \<equiv> \<not> is_pos L"

lemma Pos_atm_of_iff[simp]: "Pos (atm_of L) = L \<longleftrightarrow> is_pos L"
  by (cases L) simp+

lemma Neg_atm_of_iff[simp]: "Neg (atm_of L) = L \<longleftrightarrow> is_neg L"
  by (cases L) simp+

lemma set_literal_atm_of: "set_literal L = {atm_of L}"
  by (cases L) simp+

lemma ex_lit_cases: "(\<exists>L. P L) \<longleftrightarrow> (\<exists>A. P (Pos A) \<or> P (Neg A))"
  by (metis literal.exhaust)

instantiation literal :: (type) uminus
begin

definition uminus_literal :: "'a literal \<Rightarrow> 'a literal" where
  "uminus L = (if is_pos L then Neg else Pos) (atm_of L)"

instance ..

end

lemma
  uminus_Pos[simp]: "- Pos A = Neg A" and
  uminus_Neg[simp]: "- Neg A = Pos A"
  unfolding uminus_literal_def by simp_all

lemma atm_of_uminus[simp]: "atm_of (-L) = atm_of L"
  by (case_tac L, auto)

lemma uminus_of_uminus_id[simp]: "- (- (x :: 'v literal)) = x"
  by (simp add: uminus_literal_def)

lemma uminus_not_id[simp]: "x \<noteq> - (x:: 'v literal)"
  by (case_tac x) auto

lemma uminus_not_id'[simp]: "- x \<noteq> (x:: 'v literal)"
  by (case_tac x, auto)

lemma uminus_eq_inj[iff]: "- (a::'v literal) = - b \<longleftrightarrow> a = b"
  by (case_tac a; case_tac b) auto+

lemma uminus_lit_swap: "(a::'a literal) = - b \<longleftrightarrow> - a = b"
  by auto

lemma is_pos_neg_not_is_pos: "is_pos (- L) \<longleftrightarrow> \<not> is_pos L"
  by (cases L) auto

instantiation literal :: (preorder) preorder
begin

definition less_literal :: "'a literal \<Rightarrow> 'a literal \<Rightarrow> bool" where
  "less_literal L M \<longleftrightarrow> atm_of L < atm_of M \<or> atm_of L \<le> atm_of M \<and> is_neg L < is_neg M"

definition less_eq_literal :: "'a literal \<Rightarrow> 'a literal \<Rightarrow> bool" where
  "less_eq_literal L M \<longleftrightarrow> atm_of L < atm_of M \<or> atm_of L \<le> atm_of M \<and> is_neg L \<le> is_neg M"

instance
  apply intro_classes
  unfolding less_literal_def less_eq_literal_def by (auto intro: order_trans simp: less_le_not_le)

end

instantiation literal :: (order) order
begin

instance
  by intro_classes (auto simp: less_eq_literal_def intro: literal.expand)

end

lemma pos_less_neg[simp]: "Pos A < Neg A"
  unfolding less_literal_def by simp

lemma pos_less_pos_iff[simp]: "Pos A < Pos B \<longleftrightarrow> A < B"
  unfolding less_literal_def by simp

lemma pos_less_neg_iff[simp]: "Pos A < Neg B \<longleftrightarrow> A \<le> B"
  unfolding less_literal_def by (auto simp: less_le_not_le)

lemma neg_less_pos_iff[simp]: "Neg A < Pos B \<longleftrightarrow> A < B"
  unfolding less_literal_def by simp

lemma neg_less_neg_iff[simp]: "Neg A < Neg B \<longleftrightarrow> A < B"
  unfolding less_literal_def by simp

lemma pos_le_neg[simp]: "Pos A \<le> Neg A"
  unfolding less_eq_literal_def by simp

lemma pos_le_pos_iff[simp]: "Pos A \<le> Pos B \<longleftrightarrow> A \<le> B"
  unfolding less_eq_literal_def by (auto simp: less_le_not_le)

lemma pos_le_neg_iff[simp]: "Pos A \<le> Neg B \<longleftrightarrow> A \<le> B"
  unfolding less_eq_literal_def by (auto simp: less_imp_le)

lemma neg_le_pos_iff[simp]: "Neg A \<le> Pos B \<longleftrightarrow> A < B"
  unfolding less_eq_literal_def by simp

lemma neg_le_neg_iff[simp]: "Neg A \<le> Neg B \<longleftrightarrow> A \<le> B"
  unfolding less_eq_literal_def by (auto simp: less_imp_le)

lemma leq_imp_less_eq_atm_of: "L \<le> M \<Longrightarrow> atm_of L \<le> atm_of M"
  unfolding less_eq_literal_def using less_imp_le by blast

instantiation literal :: (linorder) linorder
begin

instance
  apply intro_classes
  unfolding less_eq_literal_def less_literal_def by auto

end

instantiation literal :: (wellorder) wellorder
begin

instance
proof intro_classes
  fix P :: "'a literal \<Rightarrow> bool" and L :: "'a literal"
  assume ih: "\<And>L. (\<And>M. M < L \<Longrightarrow> P M) \<Longrightarrow> P L"
  have "\<And>x. (\<And>y. y < x \<Longrightarrow> P (Pos y) \<and> P (Neg y)) \<Longrightarrow> P (Pos x) \<and> P (Neg x)"
    by (rule conjI[OF ih ih])
      (auto simp: less_literal_def atm_of_def split: literal.splits intro: ih)
  then have "\<And>A. P (Pos A) \<and> P (Neg A)"
    by (rule less_induct) blast
  then show "P L"
    by (cases L) simp+
qed

end


subsection \<open>Clauses\<close>

text \<open>
Clauses are (finite) multisets of literals.
\<close>

type_synonym 'a clause = "'a literal multiset"

abbreviation map_clause :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a clause \<Rightarrow> 'b clause" where
  "map_clause f \<equiv> image_mset (map_literal f)"

abbreviation rel_clause :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a clause \<Rightarrow> 'b clause \<Rightarrow> bool" where
  "rel_clause R \<equiv> rel_mset (rel_literal R)"

abbreviation poss :: "'a multiset \<Rightarrow> 'a clause" where "poss AA \<equiv> {#Pos A. A \<in># AA#}"
abbreviation negs :: "'a multiset \<Rightarrow> 'a clause" where "negs AA \<equiv> {#Neg A. A \<in># AA#}"

lemma Max_in_lits: "C \<noteq> {#} \<Longrightarrow> Max_mset C \<in># C"
  by simp

lemma Max_atm_of_set_mset_commute: "C \<noteq> {#} \<Longrightarrow> Max (atm_of ` set_mset C) = atm_of (Max_mset C)"
  by (rule mono_Max_commute[symmetric]) (auto simp: mono_def less_eq_literal_def)

lemma Max_pos_neg_less_multiset:
  assumes max: "Max_mset C = Pos A" and neg: "Neg A \<in># D"
  shows "C < D"
proof -
  have "Max_mset C < Neg A"
    using max by simp
  then show ?thesis
    using neg by (metis (no_types) Max_less_iff empty_iff ex_gt_imp_less_multiset finite_set_mset)
qed

lemma pos_Max_imp_neg_notin: "Max_mset C = Pos A \<Longrightarrow> Neg A \<notin># C"
  using Max_pos_neg_less_multiset by blast

lemma less_eq_Max_lit: "C \<noteq> {#} \<Longrightarrow> C \<le> D \<Longrightarrow> Max_mset C \<le> Max_mset D"
proof (unfold less_eq_multiset\<^sub>H\<^sub>O)
  assume
    ne: "C \<noteq> {#}" and
    ex_gt: "\<forall>x. count D x < count C x \<longrightarrow> (\<exists>y > x. count C y < count D y)"
  from ne have "Max_mset C \<in># C"
    by (fast intro: Max_in_lits)
  then have "\<exists>l. l \<in># D \<and> \<not> l < Max_mset C"
    using ex_gt by (metis count_greater_zero_iff count_inI less_not_sym)
  then have "\<not> Max_mset D < Max_mset C"
    by (metis Max.coboundedI[OF finite_set_mset] le_less_trans)
  then show ?thesis
    by simp
qed

definition atms_of :: "'a clause \<Rightarrow> 'a set" where
  "atms_of C = atm_of ` set_mset C"

lemma atms_of_empty[simp]: "atms_of {#} = {}"
  unfolding atms_of_def by simp

lemma atms_of_singleton[simp]: "atms_of {#L#} = {atm_of L}"
  unfolding atms_of_def by auto

lemma atms_of_add_mset[simp]: "atms_of (add_mset a A) = insert (atm_of a) (atms_of A)"
  unfolding atms_of_def by auto

lemma atms_of_union_mset[simp]: "atms_of (A \<union># B) = atms_of A \<union> atms_of B"
  unfolding atms_of_def by auto

lemma finite_atms_of[iff]: "finite (atms_of C)"
  by (simp add: atms_of_def)

lemma atm_of_lit_in_atms_of: "L \<in># C \<Longrightarrow> atm_of L \<in> atms_of C"
  by (simp add: atms_of_def)

lemma atms_of_plus[simp]: "atms_of (C + D) = atms_of C \<union> atms_of D"
  unfolding atms_of_def by auto

lemma in_atms_of_minusD: "x \<in> atms_of (A - B) \<Longrightarrow> x \<in> atms_of A"
  by (auto simp: atms_of_def dest: in_diffD)

lemma pos_lit_in_atms_of: "Pos A \<in># C \<Longrightarrow> A \<in> atms_of C"
  unfolding atms_of_def by force

lemma neg_lit_in_atms_of: "Neg A \<in># C \<Longrightarrow> A \<in> atms_of C"
  unfolding atms_of_def by force

lemma atm_imp_pos_or_neg_lit: "A \<in> atms_of C \<Longrightarrow> Pos A \<in># C \<or> Neg A \<in># C"
  unfolding atms_of_def image_def mem_Collect_eq by (metis Neg_atm_of_iff Pos_atm_of_iff)

lemma atm_iff_pos_or_neg_lit: "A \<in> atms_of L \<longleftrightarrow> Pos A \<in># L \<or> Neg A \<in># L"
  by (auto intro: pos_lit_in_atms_of neg_lit_in_atms_of dest: atm_imp_pos_or_neg_lit)

lemma atm_of_eq_atm_of: "atm_of L = atm_of L' \<longleftrightarrow> (L = L' \<or> L = -L')"
  by (cases L; cases L') auto

lemma atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set: "atm_of L \<in> atm_of ` I \<longleftrightarrow> (L \<in> I \<or> -L \<in> I)"
  by (auto intro: rev_image_eqI simp: atm_of_eq_atm_of)

lemma lits_subseteq_imp_atms_subseteq: "set_mset C \<subseteq> set_mset D \<Longrightarrow> atms_of C \<subseteq> atms_of D"
  unfolding atms_of_def by blast

lemma atms_empty_iff_empty[iff]: "atms_of C = {} \<longleftrightarrow> C = {#}"
  unfolding atms_of_def image_def Collect_empty_eq by auto

lemma
  atms_of_poss[simp]: "atms_of (poss AA) = set_mset AA" and
  atms_of_negs[simp]: "atms_of (negs AA) = set_mset AA"
  unfolding atms_of_def image_def by auto

lemma less_eq_Max_atms_of: "C \<noteq> {#} \<Longrightarrow> C \<le> D \<Longrightarrow> Max (atms_of C) \<le> Max (atms_of D)"
  unfolding atms_of_def
  by (metis Max_atm_of_set_mset_commute leq_imp_less_eq_atm_of less_eq_Max_lit
      less_eq_multiset_empty_right)

lemma le_multiset_Max_in_imp_Max:
  "Max (atms_of D) = A \<Longrightarrow> C \<le> D \<Longrightarrow> A \<in> atms_of C \<Longrightarrow> Max (atms_of C) = A"
  by (metis Max.coboundedI[OF finite_atms_of] atms_of_def empty_iff eq_iff image_subsetI
      less_eq_Max_atms_of set_mset_empty subset_Compl_self_eq)

lemma atm_of_Max_lit[simp]: "C \<noteq> {#} \<Longrightarrow> atm_of (Max_mset C) = Max (atms_of C)"
  unfolding atms_of_def Max_atm_of_set_mset_commute ..

lemma Max_lit_eq_pos_or_neg_Max_atm:
  "C \<noteq> {#} \<Longrightarrow> Max_mset C = Pos (Max (atms_of C)) \<or> Max_mset C = Neg (Max (atms_of C))"
  by (metis Neg_atm_of_iff Pos_atm_of_iff atm_of_Max_lit)

lemma atms_less_imp_lit_less_pos: "(\<And>B. B \<in> atms_of C \<Longrightarrow> B < A) \<Longrightarrow> L \<in># C \<Longrightarrow> L < Pos A"
  unfolding atms_of_def less_literal_def by force

lemma atms_less_eq_imp_lit_less_eq_neg: "(\<And>B. B \<in> atms_of C \<Longrightarrow> B \<le> A) \<Longrightarrow> L \<in># C \<Longrightarrow> L \<le> Neg A"
  unfolding less_eq_literal_def by (simp add: atm_of_lit_in_atms_of)

end
