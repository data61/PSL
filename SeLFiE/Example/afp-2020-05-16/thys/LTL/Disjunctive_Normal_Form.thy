(*
    Author:   Benedikt Seidl
    Author:   Salomon Sickert
    License:  BSD
*)

section \<open>Disjunctive Normal Form of LTL formulas\<close>

theory Disjunctive_Normal_Form
imports
  LTL Equivalence_Relations "HOL-Library.FSet"
begin

text \<open>
  We use the propositional representation of LTL formulas to define
  the minimal disjunctive normal form of our formulas. For this purpose
  we define the minimal product \<open>\<otimes>\<^sub>m\<close> and union \<open>\<union>\<^sub>m\<close>.
  In the end we show that for a set \<open>\<A>\<close> of literals,
  @{term "\<A> \<Turnstile>\<^sub>P \<phi>"} if, and only if, there exists a subset
  of \<open>\<A>\<close> in the minimal DNF of \<open>\<phi>\<close>.
\<close>

subsection \<open>Definition of Minimum Sets\<close>

definition (in ord) min_set :: "'a set \<Rightarrow> 'a set" where
  "min_set X = {y \<in> X. \<forall>x \<in> X. x \<le> y \<longrightarrow> x = y}"

lemma min_set_iff:
  "x \<in> min_set X \<longleftrightarrow> x \<in> X \<and> (\<forall>y \<in> X. y \<le> x \<longrightarrow> y = x)"
  unfolding min_set_def by blast

lemma min_set_subset:
  "min_set X \<subseteq> X"
  by (auto simp: min_set_def)

lemma min_set_idem[simp]:
  "min_set (min_set X) = min_set X"
  by (auto simp: min_set_def)

lemma min_set_empty[simp]:
  "min_set {} = {}"
  using min_set_subset by blast

lemma min_set_singleton[simp]:
  "min_set {x} = {x}"
  by (auto simp: min_set_def)

lemma min_set_finite:
  "finite X \<Longrightarrow> finite (min_set X)"
  by (simp add: min_set_def)

lemma min_set_obtains_helper:
  "A \<in> B \<Longrightarrow> \<exists>C. C |\<subseteq>| A \<and> C \<in> min_set B"
proof (induction "fcard A" arbitrary: A rule: less_induct)
  case less

  then have "(\<forall>A'. A' \<notin> B \<or> \<not> A' |\<subseteq>| A \<or> A' = A) \<or> (\<exists>A'. A' |\<subseteq>| A \<and> A' \<in> min_set B)"
    by (metis (no_types) dual_order.trans order.not_eq_order_implies_strict pfsubset_fcard_mono)

  then show ?case
    using less.prems min_set_def by auto
qed

lemma min_set_obtains:
  assumes "A \<in> B"
  obtains C where "C |\<subseteq>| A" and "C \<in> min_set B"
  using min_set_obtains_helper assms by metis



subsection \<open>Minimal operators on sets\<close>

definition product :: "'a fset set \<Rightarrow> 'a fset set \<Rightarrow> 'a fset set" (infixr "\<otimes>" 65)
  where "A \<otimes> B = {a |\<union>| b | a b. a \<in> A \<and> b \<in> B}"

definition min_product :: "'a fset set \<Rightarrow> 'a fset set \<Rightarrow> 'a fset set" (infixr "\<otimes>\<^sub>m" 65)
  where "A \<otimes>\<^sub>m B = min_set (A \<otimes> B)"

definition min_union :: "'a fset set \<Rightarrow> 'a fset set \<Rightarrow> 'a fset set" (infixr "\<union>\<^sub>m" 65)
  where "A \<union>\<^sub>m B = min_set (A \<union> B)"

definition product_set :: "'a fset set set \<Rightarrow> 'a fset set" ("\<Otimes>")
  where "\<Otimes> X = Finite_Set.fold product {{||}} X"

definition min_product_set :: "'a fset set set \<Rightarrow> 'a fset set" ("\<Otimes>\<^sub>m")
  where "\<Otimes>\<^sub>m X = Finite_Set.fold min_product {{||}} X"


lemma min_product_idem[simp]:
  "A \<otimes>\<^sub>m A = min_set A"
  by (auto simp: min_product_def product_def min_set_def) fastforce

lemma min_union_idem[simp]:
  "A \<union>\<^sub>m A = min_set A"
  by (simp add: min_union_def)


lemma product_empty[simp]:
  "A \<otimes> {} = {}"
  "{} \<otimes> A = {}"
  by (simp_all add: product_def)

lemma min_product_empty[simp]:
  "A \<otimes>\<^sub>m {} = {}"
  "{} \<otimes>\<^sub>m A = {}"
  by (simp_all add: min_product_def)

lemma min_union_empty[simp]:
  "A \<union>\<^sub>m {} = min_set A"
  "{} \<union>\<^sub>m A = min_set A"
  by (simp_all add: min_union_def)

lemma product_empty_singleton[simp]:
  "A \<otimes> {{||}} = A"
  "{{||}} \<otimes> A = A"
  by (simp_all add: product_def)

lemma min_product_empty_singleton[simp]:
  "A \<otimes>\<^sub>m {{||}} = min_set A"
  "{{||}} \<otimes>\<^sub>m A = min_set A"
  by (simp_all add: min_product_def)

lemma product_singleton_singleton:
  "A \<otimes> {{|x|}} = finsert x ` A"
  "{{|x|}} \<otimes> A = finsert x ` A"
  unfolding product_def by blast+

lemma product_mono:
  "A \<subseteq> B \<Longrightarrow> A \<otimes> C \<subseteq> B \<otimes> C"
  "B \<subseteq> C \<Longrightarrow> A \<otimes> B \<subseteq> A \<otimes> C"
  unfolding product_def by auto



lemma product_finite:
  "finite A \<Longrightarrow> finite B \<Longrightarrow> finite (A \<otimes> B)"
  by (simp add: product_def finite_image_set2)

lemma min_product_finite:
  "finite A \<Longrightarrow> finite B \<Longrightarrow> finite (A \<otimes>\<^sub>m B)"
  by (metis min_product_def product_finite min_set_finite)

lemma min_union_finite:
  "finite A \<Longrightarrow> finite B \<Longrightarrow> finite (A \<union>\<^sub>m B)"
  by (simp add: min_union_def min_set_finite)


lemma product_set_infinite[simp]:
  "infinite X \<Longrightarrow> \<Otimes> X = {{||}}"
  by (simp add: product_set_def)

lemma min_product_set_infinite[simp]:
  "infinite X \<Longrightarrow> \<Otimes>\<^sub>m X = {{||}}"
  by (simp add: min_product_set_def)


lemma product_comm:
  "A \<otimes> B = B \<otimes> A"
  unfolding product_def by blast

lemma min_product_comm:
  "A \<otimes>\<^sub>m B = B \<otimes>\<^sub>m A"
  unfolding min_product_def
  by (simp add: product_comm)

lemma min_union_comm:
  "A \<union>\<^sub>m B = B \<union>\<^sub>m A"
  unfolding min_union_def
  by (simp add: sup.commute)


lemma product_iff:
  "x \<in> A \<otimes> B \<longleftrightarrow> (\<exists>a \<in> A. \<exists>b \<in> B. x = a |\<union>| b)"
  unfolding product_def by blast

lemma min_product_iff:
  "x \<in> A \<otimes>\<^sub>m B \<longleftrightarrow> (\<exists>a \<in> A. \<exists>b \<in> B. x = a |\<union>| b) \<and> (\<forall>a \<in> A. \<forall>b \<in> B. a |\<union>| b |\<subseteq>| x \<longrightarrow> a |\<union>| b = x)"
  unfolding min_product_def min_set_iff product_iff product_def by blast

lemma min_union_iff:
  "x \<in> A \<union>\<^sub>m B \<longleftrightarrow> x \<in> A \<union> B \<and> (\<forall>a \<in> A. a |\<subseteq>| x \<longrightarrow> a = x) \<and> (\<forall>b \<in> B. b |\<subseteq>| x \<longrightarrow> b = x)"
  unfolding min_union_def min_set_iff by blast


lemma min_set_min_product_helper:
  "x \<in> (min_set A) \<otimes>\<^sub>m B \<longleftrightarrow> x \<in> A \<otimes>\<^sub>m B"
proof
  fix x
  assume "x \<in> (min_set A) \<otimes>\<^sub>m B"

  then obtain a b where "a \<in> min_set A" and "b \<in> B" and "x = a |\<union>| b" and 1: "\<forall>a \<in> min_set A. \<forall>b \<in> B. a |\<union>| b |\<subseteq>| x \<longrightarrow> a |\<union>| b = x"
    unfolding min_product_iff by blast

  moreover

  {
    fix a' b'
    assume "a' \<in> A" and "b' \<in> B" and "a' |\<union>| b' |\<subseteq>| x"

    then obtain a'' where "a'' |\<subseteq>| a'" and "a'' \<in> min_set A"
      using min_set_obtains by metis

    then have "a'' |\<union>| b' = x"
      by (metis (full_types) 1 \<open>b' \<in> B\<close> \<open>a' |\<union>| b' |\<subseteq>| x\<close> dual_order.trans le_sup_iff)

    then have "a' |\<union>| b' = x"
      using \<open>a' |\<union>| b' |\<subseteq>| x\<close> \<open>a'' |\<subseteq>| a'\<close> by blast
  }

  ultimately show "x \<in> A \<otimes>\<^sub>m B"
    by (metis min_product_iff min_set_iff)
next
  fix x
  assume "x \<in> A \<otimes>\<^sub>m B"

  then have 1: "x \<in> A \<otimes> B" and "\<forall>y \<in> A \<otimes> B. y |\<subseteq>| x \<longrightarrow> y = x"
    unfolding min_product_def min_set_iff by simp+

  then have 2: "\<forall>y\<in>min_set A \<otimes> B. y |\<subseteq>| x \<longrightarrow> y = x"
    by (metis product_iff min_set_iff)

  then have "x \<in> min_set A \<otimes> B"
    by (metis 1 funion_mono min_set_obtains order_refl product_iff)

  then show "x \<in> min_set A \<otimes>\<^sub>m B"
    by (simp add: 2 min_product_def min_set_iff)
qed

lemma min_set_min_product[simp]:
  "(min_set A) \<otimes>\<^sub>m B = A \<otimes>\<^sub>m B"
  "A \<otimes>\<^sub>m (min_set B) = A \<otimes>\<^sub>m B"
  using min_product_comm min_set_min_product_helper by blast+

lemma min_set_min_union[simp]:
  "(min_set A) \<union>\<^sub>m B = A \<union>\<^sub>m B"
  "A \<union>\<^sub>m (min_set B) = A \<union>\<^sub>m B"
proof (unfold min_union_def min_set_def, safe)
  show "\<And>x xa xb. \<lbrakk>\<forall>xa\<in>{y \<in> A. \<forall>x\<in>A. x |\<subseteq>| y \<longrightarrow> x = y} \<union> B. xa |\<subseteq>| x \<longrightarrow> xa = x; x \<in> B; xa |\<subseteq>| x; xb |\<in>| x; xa \<in> A\<rbrakk> \<Longrightarrow> xb |\<in>| xa"
    by (metis (mono_tags) UnCI dual_order.trans fequalityI min_set_def min_set_obtains)
next
  show "\<And>x xa xb. \<lbrakk>\<forall>xa\<in>A \<union> {y \<in> B. \<forall>x\<in>B. x |\<subseteq>| y \<longrightarrow> x = y}. xa |\<subseteq>| x \<longrightarrow> xa = x; x \<in> A; xa |\<subseteq>| x; xb |\<in>| x; xa \<in> B\<rbrakk> \<Longrightarrow> xb |\<in>| xa"
    by (metis (mono_tags) UnCI dual_order.trans fequalityI min_set_def min_set_obtains)
qed blast+


lemma product_assoc[simp]:
  "(A \<otimes> B) \<otimes> C = A \<otimes> (B \<otimes> C)"
proof (unfold product_def, safe)
  fix a b c
  assume "a \<in> A" and "c \<in> C" and "b \<in> B"
  then have "b |\<union>| c \<in> {b |\<union>| c |b c. b \<in> B \<and> c \<in> C}"
    by blast
  then show "\<exists>a' bc. a |\<union>| b |\<union>| c = a' |\<union>| bc \<and> a' \<in> A \<and> bc \<in> {b |\<union>| c |b c. b \<in> B \<and> c \<in> C}"
    using `a \<in> A` by (metis (no_types) inf_sup_aci(5) sup_left_commute)
qed (metis (mono_tags, lifting) mem_Collect_eq sup_assoc)

lemma min_product_assoc[simp]:
  "(A \<otimes>\<^sub>m B) \<otimes>\<^sub>m C = A \<otimes>\<^sub>m (B \<otimes>\<^sub>m C)"
  unfolding min_product_def[of A B] min_product_def[of B C]
  by simp (simp add: min_product_def)

lemma min_union_assoc[simp]:
  "(A \<union>\<^sub>m B) \<union>\<^sub>m C = A \<union>\<^sub>m (B \<union>\<^sub>m C)"
  unfolding min_union_def[of A B] min_union_def[of B C]
  by simp (simp add: min_union_def sup_assoc)


lemma min_product_comp:
  "a \<in> A \<Longrightarrow> b \<in> B \<Longrightarrow> \<exists>c. c |\<subseteq>| (a |\<union>| b) \<and> c \<in> A \<otimes>\<^sub>m B"
  by (metis (mono_tags, lifting) mem_Collect_eq min_product_def product_def min_set_obtains)

lemma min_union_comp:
  "a \<in> A \<Longrightarrow> \<exists>c. c |\<subseteq>| a \<and> c \<in> A \<union>\<^sub>m B"
  by (metis Un_iff min_set_obtains min_union_def)


interpretation product_set_thms: Finite_Set.comp_fun_commute product
proof unfold_locales
  have "\<And>x y z. x \<otimes> (y \<otimes> z) = y \<otimes> (x \<otimes> z)"
    by (simp only: product_assoc[symmetric]) (simp only: product_comm)

  then show "\<And>x y. (\<otimes>) y \<circ> (\<otimes>) x = (\<otimes>) x \<circ> (\<otimes>) y"
    by fastforce
qed

interpretation min_product_set_thms: Finite_Set.comp_fun_idem min_product
proof unfold_locales
  have "\<And>x y z. x \<otimes>\<^sub>m (y \<otimes>\<^sub>m z) = y \<otimes>\<^sub>m (x \<otimes>\<^sub>m z)"
    by (simp only: min_product_assoc[symmetric]) (simp only: min_product_comm)

  then show "\<And>x y. (\<otimes>\<^sub>m) y \<circ> (\<otimes>\<^sub>m) x = (\<otimes>\<^sub>m) x \<circ> (\<otimes>\<^sub>m) y"
    by fastforce
next
  have "\<And>x y. x \<otimes>\<^sub>m (x \<otimes>\<^sub>m y) = x \<otimes>\<^sub>m y"
    by (simp add: min_product_assoc[symmetric])

  then show "\<And>x. (\<otimes>\<^sub>m) x \<circ> (\<otimes>\<^sub>m) x = (\<otimes>\<^sub>m) x"
    by fastforce
qed


interpretation min_union_set_thms: Finite_Set.comp_fun_idem min_union
proof unfold_locales
  have "\<And>x y z. x \<union>\<^sub>m (y \<union>\<^sub>m z) = y \<union>\<^sub>m (x \<union>\<^sub>m z)"
    by (simp only: min_union_assoc[symmetric]) (simp only: min_union_comm)

  then show "\<And>x y. (\<union>\<^sub>m) y \<circ> (\<union>\<^sub>m) x = (\<union>\<^sub>m) x \<circ> (\<union>\<^sub>m) y"
    by fastforce
next
  have "\<And>x y. x \<union>\<^sub>m (x \<union>\<^sub>m y) = x \<union>\<^sub>m y"
    by (simp add: min_union_assoc[symmetric])

  then show "\<And>x. (\<union>\<^sub>m) x \<circ> (\<union>\<^sub>m) x = (\<union>\<^sub>m) x"
    by fastforce
qed


lemma product_set_empty[simp]:
  "\<Otimes> {} = {{||}}"
  "\<Otimes> {{}} = {}"
  "\<Otimes> {{{||}}} = {{||}}"
  by (simp_all add: product_set_def)

lemma min_product_set_empty[simp]:
  "\<Otimes>\<^sub>m {} = {{||}}"
  "\<Otimes>\<^sub>m {{}} = {}"
  "\<Otimes>\<^sub>m {{{||}}} = {{||}}"
  by (simp_all add: min_product_set_def)

lemma product_set_code[code]:
  "\<Otimes> (set xs) = fold product (remdups xs) {{||}}"
  by (simp add: product_set_def product_set_thms.fold_set_fold_remdups)

lemma min_product_set_code[code]:
  "\<Otimes>\<^sub>m (set xs) = fold min_product (remdups xs) {{||}}"
  by (simp add: min_product_set_def min_product_set_thms.fold_set_fold_remdups)

lemma product_set_insert[simp]:
  "finite X \<Longrightarrow> \<Otimes> (insert x X) = x \<otimes> (\<Otimes> (X - {x}))"
  unfolding product_set_def product_set_thms.fold_insert_remove ..

lemma min_product_set_insert[simp]:
  "finite X \<Longrightarrow> \<Otimes>\<^sub>m (insert x X) = x \<otimes>\<^sub>m (\<Otimes>\<^sub>m X)"
  unfolding min_product_set_def min_product_set_thms.fold_insert_idem ..

lemma min_product_subseteq:
  "x \<in> A \<otimes>\<^sub>m B \<Longrightarrow> \<exists>a. a |\<subseteq>| x \<and> a \<in> A"
  by (metis funion_upper1 min_product_iff)

lemma min_product_set_subseteq:
  "finite X \<Longrightarrow> x \<in> \<Otimes>\<^sub>m X \<Longrightarrow> A \<in> X \<Longrightarrow> \<exists>a \<in> A. a |\<subseteq>| x"
  by (induction X rule: finite_induct) (blast, metis finite_insert insert_absorb min_product_set_insert min_product_subseteq)

lemma min_set_product_set:
  "\<Otimes>\<^sub>m A = min_set (\<Otimes> A)"
  by (cases "finite A", induction A rule: finite_induct) (simp_all add: min_product_set_def product_set_def, metis min_product_def)


lemma min_product_min_set[simp]:
  "min_set (A \<otimes>\<^sub>m B) = A \<otimes>\<^sub>m B"
  by (simp add: min_product_def)

lemma min_union_min_set[simp]:
  "min_set (A \<union>\<^sub>m B) = A \<union>\<^sub>m B"
  by (simp add: min_union_def)

lemma min_product_set_min_set[simp]:
  "finite X \<Longrightarrow> min_set (\<Otimes>\<^sub>m X) = \<Otimes>\<^sub>m X"
  by (induction X rule: finite_induct, auto simp add: min_product_set_def min_set_iff)

lemma min_set_min_product_set[simp]:
  "finite X \<Longrightarrow> \<Otimes>\<^sub>m (min_set ` X) = \<Otimes>\<^sub>m X"
  by (induction X rule: finite_induct) simp_all

lemma min_product_set_union[simp]:
  "finite X \<Longrightarrow> finite Y \<Longrightarrow> \<Otimes>\<^sub>m (X \<union> Y) = (\<Otimes>\<^sub>m X) \<otimes>\<^sub>m (\<Otimes>\<^sub>m Y)"
  by (induction X rule: finite_induct) simp_all


lemma product_set_finite:
  "(\<And>x. x \<in> X \<Longrightarrow> finite x) \<Longrightarrow> finite (\<Otimes> X)"
  by (cases "finite X", rotate_tac, induction X rule: finite_induct) (simp_all add: product_set_def, insert product_finite, blast)

lemma min_product_set_finite:
  "(\<And>x. x \<in> X \<Longrightarrow> finite x) \<Longrightarrow> finite (\<Otimes>\<^sub>m X)"
  by (cases "finite X", rotate_tac, induction X rule: finite_induct) (simp_all add: min_product_set_def, insert min_product_finite, blast)



subsection \<open>Disjunctive Normal Form\<close>

fun dnf :: "'a ltln \<Rightarrow> 'a ltln fset set"
where
  "dnf true\<^sub>n = {{||}}"
| "dnf false\<^sub>n = {}"
| "dnf (\<phi> and\<^sub>n \<psi>) = (dnf \<phi>) \<otimes> (dnf \<psi>)"
| "dnf (\<phi> or\<^sub>n \<psi>) = (dnf \<phi>) \<union> (dnf \<psi>)"
| "dnf \<phi> = {{|\<phi>|}}"

fun min_dnf :: "'a ltln \<Rightarrow> 'a ltln fset set"
where
  "min_dnf true\<^sub>n = {{||}}"
| "min_dnf false\<^sub>n = {}"
| "min_dnf (\<phi> and\<^sub>n \<psi>) = (min_dnf \<phi>) \<otimes>\<^sub>m (min_dnf \<psi>)"
| "min_dnf (\<phi> or\<^sub>n \<psi>) = (min_dnf \<phi>) \<union>\<^sub>m (min_dnf \<psi>)"
| "min_dnf \<phi> = {{|\<phi>|}}"

lemma dnf_min_set:
  "min_dnf \<phi> = min_set (dnf \<phi>)"
  by (induction \<phi>) (simp_all, simp_all only: min_product_def min_union_def)

lemma dnf_finite:
  "finite (dnf \<phi>)"
  by (induction \<phi>) (auto simp: product_finite)

lemma min_dnf_finite:
  "finite (min_dnf \<phi>)"
  by (induction \<phi>) (auto simp: min_product_finite min_union_finite)

lemma dnf_Abs_fset[simp]:
  "fset (Abs_fset (dnf \<phi>)) = dnf \<phi>"
  by (simp add: dnf_finite Abs_fset_inverse)

lemma min_dnf_Abs_fset[simp]:
  "fset (Abs_fset (min_dnf \<phi>)) = min_dnf \<phi>"
  by (simp add: min_dnf_finite Abs_fset_inverse)

lemma dnf_prop_atoms:
  "\<Phi> \<in> dnf \<phi> \<Longrightarrow> fset \<Phi> \<subseteq> prop_atoms \<phi>"
  by (induction \<phi> arbitrary: \<Phi>) (auto simp: product_def, blast+)

lemma min_dnf_prop_atoms:
  "\<Phi> \<in> min_dnf \<phi> \<Longrightarrow> fset \<Phi> \<subseteq> prop_atoms \<phi>"
  using dnf_min_set dnf_prop_atoms min_set_subset by blast

lemma min_dnf_atoms_dnf:
  "\<Phi> \<in> min_dnf \<psi> \<Longrightarrow> \<phi> \<in> fset \<Phi> \<Longrightarrow> dnf \<phi> = {{|\<phi>|}}"
proof (induction \<phi>)
  case True_ltln
  then show ?case
    using min_dnf_prop_atoms prop_atoms_notin(1) by blast
next
  case False_ltln
  then show ?case
    using min_dnf_prop_atoms prop_atoms_notin(2) by blast
next
  case (And_ltln \<phi>1 \<phi>2)
  then show ?case
    using min_dnf_prop_atoms prop_atoms_notin(3) by force
next
  case (Or_ltln \<phi>1 \<phi>2)
  then show ?case
    using min_dnf_prop_atoms prop_atoms_notin(4) by force
qed auto

lemma min_dnf_min_set[simp]:
  "min_set (min_dnf \<phi>) = min_dnf \<phi>"
  by (induction \<phi>) (simp_all add: min_set_def min_product_def min_union_def, blast+)


lemma min_dnf_iff_prop_assignment_subset:
  "\<A> \<Turnstile>\<^sub>P \<phi> \<longleftrightarrow> (\<exists>B. fset B \<subseteq> \<A> \<and> B \<in> min_dnf \<phi>)"
proof
  assume "\<A> \<Turnstile>\<^sub>P \<phi>"

  then show "\<exists>B. fset B \<subseteq> \<A> \<and> B \<in> min_dnf \<phi>"
  proof (induction \<phi> arbitrary: \<A>)
    case (And_ltln \<phi>\<^sub>1 \<phi>\<^sub>2)

    then obtain B\<^sub>1 B\<^sub>2 where 1: "fset B\<^sub>1 \<subseteq> \<A> \<and> B\<^sub>1 \<in> min_dnf \<phi>\<^sub>1" and 2: "fset B\<^sub>2 \<subseteq> \<A> \<and> B\<^sub>2 \<in> min_dnf \<phi>\<^sub>2"
      by fastforce

    then obtain C where "C |\<subseteq>| B\<^sub>1 |\<union>| B\<^sub>2" and "C \<in> min_dnf \<phi>\<^sub>1 \<otimes>\<^sub>m min_dnf \<phi>\<^sub>2"
      using min_product_comp by metis

    then show ?case
      by (metis 1 2 le_sup_iff min_dnf.simps(3) sup.absorb_iff1 sup_fset.rep_eq)
  next
    case (Or_ltln \<phi>\<^sub>1 \<phi>\<^sub>2)

    {
      assume "\<A> \<Turnstile>\<^sub>P \<phi>\<^sub>1"

      then obtain B where 1: "fset B \<subseteq> \<A> \<and> B \<in> min_dnf \<phi>\<^sub>1"
        using Or_ltln by fastforce

      then obtain C where "C |\<subseteq>| B" and "C \<in> min_dnf \<phi>\<^sub>1 \<union>\<^sub>m min_dnf \<phi>\<^sub>2"
        using min_union_comp by metis

      then have ?case
        by (metis 1 dual_order.trans less_eq_fset.rep_eq min_dnf.simps(4))
    }

    moreover

    {
      assume "\<A> \<Turnstile>\<^sub>P \<phi>\<^sub>2"

      then obtain B where 2: "fset B \<subseteq> \<A> \<and> B \<in> min_dnf \<phi>\<^sub>2"
        using Or_ltln by fastforce

      then obtain C where "C |\<subseteq>| B" and "C \<in> min_dnf \<phi>\<^sub>1 \<union>\<^sub>m min_dnf \<phi>\<^sub>2"
        using min_union_comp min_union_comm by metis

      then have ?case
        by (metis 2 dual_order.trans less_eq_fset.rep_eq min_dnf.simps(4))
    }

    ultimately show ?case
      using Or_ltln.prems by auto
  qed simp_all
next
  assume "\<exists>B. fset B \<subseteq> \<A> \<and> B \<in> min_dnf \<phi>"

  then obtain B where "fset B \<subseteq> \<A>" and "B \<in> min_dnf \<phi>"
    by auto

  then have "fset B \<Turnstile>\<^sub>P \<phi>"
    by (induction \<phi> arbitrary: B) (auto simp: min_set_def min_product_def product_def min_union_def, blast+)

  then show "\<A> \<Turnstile>\<^sub>P \<phi>"
    using \<open>fset B \<subseteq> \<A>\<close> by blast
qed


lemma ltl_prop_implies_min_dnf:
  "\<phi> \<longrightarrow>\<^sub>P \<psi> = (\<forall>A \<in> min_dnf \<phi>. \<exists>B \<in> min_dnf \<psi>. B |\<subseteq>| A)"
  by (meson less_eq_fset.rep_eq ltl_prop_implies_def min_dnf_iff_prop_assignment_subset order_refl dual_order.trans)

lemma ltl_prop_equiv_min_dnf:
  "\<phi> \<sim>\<^sub>P \<psi> = (min_dnf \<phi> = min_dnf \<psi>)"
proof
  assume "\<phi> \<sim>\<^sub>P \<psi>"

  then have "\<And>x. x \<in> min_set (min_dnf \<phi>) \<longleftrightarrow> x \<in> min_set (min_dnf \<psi>)"
    unfolding ltl_prop_implies_equiv ltl_prop_implies_min_dnf min_set_iff
    by fastforce

  then show "min_dnf \<phi> = min_dnf \<psi>"
    by auto
qed (simp add: ltl_prop_equiv_def min_dnf_iff_prop_assignment_subset)

lemma min_dnf_rep_abs[simp]:
  "min_dnf (rep_ltln\<^sub>P (abs_ltln\<^sub>P \<phi>)) = min_dnf \<phi>"
  by (simp add: ltl_prop_equiv_min_dnf[symmetric] Quotient3_ltln\<^sub>P rep_abs_rsp_left)


subsection \<open>Folding of \<open>and\<^sub>n\<close> and \<open>or\<^sub>n\<close> over Finite Sets\<close>

definition And\<^sub>n :: "'a ltln set \<Rightarrow> 'a ltln"
where
  "And\<^sub>n \<Phi> \<equiv> SOME \<phi>. fold_graph And_ltln True_ltln \<Phi> \<phi>"

definition Or\<^sub>n :: "'a ltln set \<Rightarrow> 'a ltln"
where
  "Or\<^sub>n \<Phi> \<equiv> SOME \<phi>. fold_graph Or_ltln False_ltln \<Phi> \<phi>"

lemma fold_graph_And\<^sub>n:
  "finite \<Phi> \<Longrightarrow> fold_graph And_ltln True_ltln \<Phi> (And\<^sub>n \<Phi>)"
  unfolding And\<^sub>n_def by (rule someI2_ex[OF finite_imp_fold_graph])

lemma fold_graph_Or\<^sub>n:
  "finite \<Phi> \<Longrightarrow> fold_graph Or_ltln False_ltln \<Phi> (Or\<^sub>n \<Phi>)"
  unfolding Or\<^sub>n_def by (rule someI2_ex[OF finite_imp_fold_graph])

lemma Or\<^sub>n_empty[simp]:
  "Or\<^sub>n {} = False_ltln"
  by (metis empty_fold_graphE finite.emptyI fold_graph_Or\<^sub>n)

lemma And\<^sub>n_empty[simp]:
  "And\<^sub>n {} = True_ltln"
  by (metis empty_fold_graphE finite.emptyI fold_graph_And\<^sub>n)

interpretation dnf_union_thms: Finite_Set.comp_fun_commute "\<lambda>\<phi>. (\<union>) (f \<phi>)"
  by unfold_locales fastforce

interpretation dnf_product_thms: Finite_Set.comp_fun_commute "\<lambda>\<phi>. (\<otimes>) (f \<phi>)"
  by unfold_locales (simp add: product_set_thms.comp_fun_commute)

\<comment> \<open>Copied from locale @{locale comp_fun_commute}\<close>
lemma fold_graph_finite:
  assumes "fold_graph f z A y"
  shows "finite A"
  using assms by induct simp_all


text \<open>Taking the DNF of @{const And\<^sub>n} and @{const Or\<^sub>n} is the same as folding over the individual DNFs.\<close>

lemma And\<^sub>n_dnf:
  "finite \<Phi> \<Longrightarrow> dnf (And\<^sub>n \<Phi>) = Finite_Set.fold (\<lambda>\<phi>. (\<otimes>) (dnf \<phi>)) {{||}} \<Phi>"
proof (drule fold_graph_And\<^sub>n, induction rule: fold_graph.induct)
  case (insertI x A y)

  then have "finite A"
    using fold_graph_finite by fast

  then show ?case
    using insertI by auto
qed simp

lemma Or\<^sub>n_dnf:
  "finite \<Phi> \<Longrightarrow> dnf (Or\<^sub>n \<Phi>) = Finite_Set.fold (\<lambda>\<phi>. (\<union>) (dnf \<phi>)) {} \<Phi>"
proof (drule fold_graph_Or\<^sub>n, induction rule: fold_graph.induct)
  case (insertI x A y)

  then have "finite A"
    using fold_graph_finite by fast

  then show ?case
    using insertI by auto
qed simp


text \<open>@{const And\<^sub>n} and @{const Or\<^sub>n} are injective on finite sets.\<close>

lemma And\<^sub>n_inj:
  "inj_on And\<^sub>n {s. finite s}"
proof (standard, simp)
  fix x y :: "'a ltln set"
  assume "finite x" and "finite y"

  then have 1: "fold_graph And_ltln True_ltln x (And\<^sub>n x)" and 2: "fold_graph And_ltln True_ltln y (And\<^sub>n y)"
    using fold_graph_And\<^sub>n by blast+

  assume "And\<^sub>n x = And\<^sub>n y"

  with 1 show "x = y"
  proof (induction rule: fold_graph.induct)
    case emptyI
    then show ?case
      using 2 fold_graph.cases by force
  next
    case (insertI x A y)
    with 2 show ?case
    proof (induction arbitrary: x A y rule: fold_graph.induct)
      case (insertI x A y)
      then show ?case
        by (metis fold_graph.cases insertI1 ltln.distinct(7) ltln.inject(3))
    qed blast
  qed
qed

lemma Or\<^sub>n_inj:
  "inj_on Or\<^sub>n {s. finite s}"
proof (standard, simp)
  fix x y :: "'a ltln set"
  assume "finite x" and "finite y"

  then have 1: "fold_graph Or_ltln False_ltln x (Or\<^sub>n x)" and 2: "fold_graph Or_ltln False_ltln y (Or\<^sub>n y)"
    using fold_graph_Or\<^sub>n by blast+

  assume "Or\<^sub>n x = Or\<^sub>n y"

  with 1 show "x = y"
  proof (induction rule: fold_graph.induct)
    case emptyI
    then show ?case
      using 2 fold_graph.cases by force
  next
    case (insertI x A y)
    with 2 show ?case
    proof (induction arbitrary: x A y rule: fold_graph.induct)
      case (insertI x A y)
      then show ?case
        by (metis fold_graph.cases insertI1 ltln.distinct(27) ltln.inject(4))
    qed blast
  qed
qed


text \<open>The semantics of @{const And\<^sub>n} and @{const Or\<^sub>n} can be expressed using quantifiers.\<close>

lemma And\<^sub>n_semantics:
  "finite \<Phi> \<Longrightarrow> w \<Turnstile>\<^sub>n And\<^sub>n \<Phi> \<longleftrightarrow> (\<forall>\<phi> \<in> \<Phi>. w \<Turnstile>\<^sub>n \<phi>)"
proof -
  assume "finite \<Phi>"
  have "\<And>\<psi>. fold_graph And_ltln True_ltln \<Phi> \<psi> \<Longrightarrow> w \<Turnstile>\<^sub>n \<psi> \<longleftrightarrow> (\<forall>\<phi> \<in> \<Phi>. w \<Turnstile>\<^sub>n \<phi>)"
    by (rule fold_graph.induct) auto
  then show ?thesis
    using fold_graph_And\<^sub>n[OF \<open>finite \<Phi>\<close>] by simp
qed

lemma Or\<^sub>n_semantics:
  "finite \<Phi> \<Longrightarrow> w \<Turnstile>\<^sub>n Or\<^sub>n \<Phi> \<longleftrightarrow> (\<exists>\<phi> \<in> \<Phi>. w \<Turnstile>\<^sub>n \<phi>)"
proof -
  assume "finite \<Phi>"
  have "\<And>\<psi>. fold_graph Or_ltln False_ltln \<Phi> \<psi> \<Longrightarrow> w \<Turnstile>\<^sub>n \<psi> \<longleftrightarrow> (\<exists>\<phi> \<in> \<Phi>. w \<Turnstile>\<^sub>n \<phi>)"
    by (rule fold_graph.induct) auto
  then show ?thesis
    using fold_graph_Or\<^sub>n[OF \<open>finite \<Phi>\<close>] by simp
qed

lemma And\<^sub>n_prop_semantics:
  "finite \<Phi> \<Longrightarrow> \<A> \<Turnstile>\<^sub>P And\<^sub>n \<Phi> \<longleftrightarrow> (\<forall>\<phi> \<in> \<Phi>. \<A> \<Turnstile>\<^sub>P \<phi>)"
proof -
  assume "finite \<Phi>"
  have "\<And>\<psi>. fold_graph And_ltln True_ltln \<Phi> \<psi> \<Longrightarrow> \<A> \<Turnstile>\<^sub>P \<psi> \<longleftrightarrow> (\<forall>\<phi> \<in> \<Phi>. \<A> \<Turnstile>\<^sub>P \<phi>)"
    by (rule fold_graph.induct) auto
  then show ?thesis
    using fold_graph_And\<^sub>n[OF \<open>finite \<Phi>\<close>] by simp
qed

lemma Or\<^sub>n_prop_semantics:
  "finite \<Phi> \<Longrightarrow> \<A> \<Turnstile>\<^sub>P Or\<^sub>n \<Phi> \<longleftrightarrow> (\<exists>\<phi> \<in> \<Phi>. \<A> \<Turnstile>\<^sub>P \<phi>)"
proof -
  assume "finite \<Phi>"
  have "\<And>\<psi>. fold_graph Or_ltln False_ltln \<Phi> \<psi> \<Longrightarrow> \<A> \<Turnstile>\<^sub>P \<psi> \<longleftrightarrow> (\<exists>\<phi> \<in> \<Phi>. \<A> \<Turnstile>\<^sub>P \<phi>)"
    by (rule fold_graph.induct) auto
  then show ?thesis
    using fold_graph_Or\<^sub>n[OF \<open>finite \<Phi>\<close>] by simp
qed

lemma Or\<^sub>n_And\<^sub>n_image_semantics:
  assumes "finite \<A>" and "\<And>\<Phi>. \<Phi> \<in> \<A> \<Longrightarrow> finite \<Phi>"
  shows "w \<Turnstile>\<^sub>n Or\<^sub>n (And\<^sub>n ` \<A>) \<longleftrightarrow> (\<exists>\<Phi> \<in> \<A>. \<forall>\<phi> \<in> \<Phi>. w \<Turnstile>\<^sub>n \<phi>)"
proof -
  have "w \<Turnstile>\<^sub>n Or\<^sub>n (And\<^sub>n ` \<A>) \<longleftrightarrow> (\<exists>\<Phi> \<in> \<A>. w \<Turnstile>\<^sub>n And\<^sub>n \<Phi>)"
    using Or\<^sub>n_semantics assms by auto
  then show ?thesis
    using And\<^sub>n_semantics assms by fast
qed

lemma Or\<^sub>n_And\<^sub>n_image_prop_semantics:
  assumes "finite \<A>" and "\<And>\<Phi>. \<Phi> \<in> \<A> \<Longrightarrow> finite \<Phi>"
  shows "\<I> \<Turnstile>\<^sub>P Or\<^sub>n (And\<^sub>n ` \<A>) \<longleftrightarrow> (\<exists>\<Phi> \<in> \<A>. \<forall>\<phi> \<in> \<Phi>. \<I> \<Turnstile>\<^sub>P \<phi>)"
proof -
  have "\<I> \<Turnstile>\<^sub>P Or\<^sub>n (And\<^sub>n ` \<A>) \<longleftrightarrow> (\<exists>\<Phi> \<in> \<A>. \<I> \<Turnstile>\<^sub>P And\<^sub>n \<Phi>)"
    using Or\<^sub>n_prop_semantics assms by blast
  then show ?thesis
    using And\<^sub>n_prop_semantics assms by metis
qed


subsection \<open>DNF to LTL conversion\<close>

definition ltln_of_dnf :: "'a ltln fset set \<Rightarrow> 'a ltln"
where
  "ltln_of_dnf \<A> = Or\<^sub>n (And\<^sub>n ` fset ` \<A>)"

lemma ltln_of_dnf_semantics:
  assumes "finite \<A>"
  shows "w \<Turnstile>\<^sub>n ltln_of_dnf \<A> \<longleftrightarrow> (\<exists>\<Phi> \<in> \<A>. \<forall>\<phi>. \<phi> |\<in>| \<Phi> \<longrightarrow> w \<Turnstile>\<^sub>n \<phi>)"
proof -
  have "finite (fset ` \<A>)"
    using assms by blast

  then have "w \<Turnstile>\<^sub>n ltln_of_dnf \<A> \<longleftrightarrow> (\<exists>\<Phi> \<in> fset ` \<A>. \<forall>\<phi> \<in> \<Phi>. w \<Turnstile>\<^sub>n \<phi>)"
    unfolding ltln_of_dnf_def using Or\<^sub>n_And\<^sub>n_image_semantics by fastforce

  then show ?thesis
    by (metis image_iff notin_fset)
qed

lemma ltln_of_dnf_prop_semantics:
  assumes "finite \<A>"
  shows "\<I> \<Turnstile>\<^sub>P ltln_of_dnf \<A> \<longleftrightarrow> (\<exists>\<Phi> \<in> \<A>. \<forall>\<phi>. \<phi> |\<in>| \<Phi> \<longrightarrow> \<I> \<Turnstile>\<^sub>P \<phi>)"
proof -
  have "finite (fset ` \<A>)"
    using assms by blast

  then have "\<I> \<Turnstile>\<^sub>P ltln_of_dnf \<A> \<longleftrightarrow> (\<exists>\<Phi> \<in> fset ` \<A>. \<forall>\<phi> \<in> \<Phi>. \<I> \<Turnstile>\<^sub>P \<phi>)"
    unfolding ltln_of_dnf_def using Or\<^sub>n_And\<^sub>n_image_prop_semantics by fastforce

  then show ?thesis
    by (metis image_iff notin_fset)
qed

lemma ltln_of_dnf_prop_equiv:
  "ltln_of_dnf (min_dnf \<phi>) \<sim>\<^sub>P \<phi>"
  unfolding ltl_prop_equiv_def
proof
  fix \<A>
  have "\<A> \<Turnstile>\<^sub>P ltln_of_dnf (min_dnf \<phi>) \<longleftrightarrow> (\<exists>\<Phi> \<in> min_dnf \<phi>. \<forall>\<phi>. \<phi> |\<in>| \<Phi> \<longrightarrow> \<A> \<Turnstile>\<^sub>P \<phi>)"
    using ltln_of_dnf_prop_semantics min_dnf_finite by metis
  also have "\<dots> \<longleftrightarrow> (\<exists>\<Phi> \<in> min_dnf \<phi>. fset \<Phi> \<subseteq> \<A>)"
    by (metis min_dnf_prop_atoms prop_atoms_entailment_iff notin_fset subset_eq)
  also have "\<dots> \<longleftrightarrow> \<A> \<Turnstile>\<^sub>P \<phi>"
    using min_dnf_iff_prop_assignment_subset by blast
  finally show "\<A> \<Turnstile>\<^sub>P ltln_of_dnf (min_dnf \<phi>) = \<A> \<Turnstile>\<^sub>P \<phi>" .
qed

lemma min_dnf_ltln_of_dnf[simp]:
  "min_dnf (ltln_of_dnf (min_dnf \<phi>)) = min_dnf \<phi>"
  using ltl_prop_equiv_min_dnf ltln_of_dnf_prop_equiv by blast


subsection \<open>Substitution in DNF formulas\<close>

definition subst_clause :: "'a ltln fset \<Rightarrow> ('a ltln \<rightharpoonup> 'a ltln) \<Rightarrow> 'a ltln fset set"
where
  "subst_clause \<Phi> m = \<Otimes>\<^sub>m {min_dnf (subst \<phi> m) | \<phi>. \<phi> \<in> fset \<Phi>}"

definition subst_dnf :: "'a ltln fset set \<Rightarrow> ('a ltln \<rightharpoonup> 'a ltln) \<Rightarrow> 'a ltln fset set"
where
  "subst_dnf \<A> m = (\<Union>\<Phi> \<in> \<A>. subst_clause \<Phi> m)"

lemma subst_clause_empty[simp]:
  "subst_clause {||} m = {{||}}"
  by (simp add: subst_clause_def)

lemma subst_dnf_empty[simp]:
  "subst_dnf {} m = {}"
  by (simp add: subst_dnf_def)

lemma subst_clause_inner_finite:
  "finite {min_dnf (subst \<phi> m) | \<phi>. \<phi> \<in> \<Phi>}" if "finite \<Phi>"
  using that by simp

lemma subst_clause_finite:
  "finite (subst_clause \<Phi> m)"
  unfolding subst_clause_def
  by (auto intro: min_dnf_finite min_product_set_finite)

lemma subst_dnf_finite:
  "finite \<A> \<Longrightarrow> finite (subst_dnf \<A> m)"
  unfolding subst_dnf_def using subst_clause_finite by blast

lemma subst_dnf_mono:
  "\<A> \<subseteq> \<B> \<Longrightarrow> subst_dnf \<A> m \<subseteq> subst_dnf \<B> m"
  unfolding subst_dnf_def by blast

lemma subst_clause_min_set[simp]:
  "min_set (subst_clause \<Phi> m) = subst_clause \<Phi> m"
  unfolding subst_clause_def by simp

lemma subst_clause_finsert[simp]:
  "subst_clause (finsert \<phi> \<Phi>) m = (min_dnf (subst \<phi> m)) \<otimes>\<^sub>m (subst_clause \<Phi> m)"
proof -
  have "{min_dnf (subst \<psi> m) | \<psi>. \<psi> \<in> fset (finsert \<phi> \<Phi>)}
    = insert (min_dnf (subst \<phi> m)) {min_dnf (subst \<psi> m) | \<psi>. \<psi> \<in> fset \<Phi>}"
    by auto

  then show ?thesis
    by (simp add: subst_clause_def)
qed

lemma subst_clause_funion[simp]:
  "subst_clause (\<Phi> |\<union>| \<Psi>) m = (subst_clause \<Phi> m) \<otimes>\<^sub>m (subst_clause \<Psi> m)"
proof (induction \<Psi>)
  case (insert x F)
  then show ?case
    using min_product_set_thms.fun_left_comm by fastforce
qed simp


text \<open>For the proof of correctness, we redefine the @{const product} operator on lists.\<close>

definition list_product :: "'a list set \<Rightarrow> 'a list set \<Rightarrow> 'a list set" (infixl "\<otimes>\<^sub>l" 65)
where
  "A \<otimes>\<^sub>l B = {a @ b | a b. a \<in> A \<and> b \<in> B}"

lemma list_product_fset_of_list[simp]:
  "fset_of_list ` (A \<otimes>\<^sub>l B) = (fset_of_list ` A) \<otimes> (fset_of_list ` B)"
  unfolding list_product_def product_def image_def by fastforce

lemma list_product_finite:
  "finite A \<Longrightarrow> finite B \<Longrightarrow> finite (A \<otimes>\<^sub>l B)"
  unfolding list_product_def by (simp add: finite_image_set2)

lemma list_product_iff:
  "x \<in> A \<otimes>\<^sub>l B \<longleftrightarrow> (\<exists>a b. a \<in> A \<and> b \<in> B \<and> x = a @ b)"
  unfolding list_product_def by blast

lemma list_product_assoc[simp]:
  "A \<otimes>\<^sub>l (B \<otimes>\<^sub>l C) = A \<otimes>\<^sub>l B \<otimes>\<^sub>l C"
  unfolding set_eq_iff list_product_iff by fastforce


text \<open>Furthermore, we introduct DNFs where the clauses are represented as lists.\<close>

fun list_dnf :: "'a ltln \<Rightarrow> 'a ltln list set"
where
  "list_dnf true\<^sub>n = {[]}"
| "list_dnf false\<^sub>n = {}"
| "list_dnf (\<phi> and\<^sub>n \<psi>) = (list_dnf \<phi>) \<otimes>\<^sub>l (list_dnf \<psi>)"
| "list_dnf (\<phi> or\<^sub>n \<psi>) = (list_dnf \<phi>) \<union> (list_dnf \<psi>)"
| "list_dnf \<phi> = {[\<phi>]}"

definition list_dnf_to_dnf :: "'a list set \<Rightarrow> 'a fset set"
where
  "list_dnf_to_dnf X = fset_of_list ` X"

lemma list_dnf_to_dnf_list_dnf[simp]:
  "list_dnf_to_dnf (list_dnf \<phi>) = dnf \<phi>"
  by (induction \<phi>) (simp_all add: list_dnf_to_dnf_def image_Un)

lemma list_dnf_finite:
  "finite (list_dnf \<phi>)"
  by (induction \<phi>) (simp_all add: list_product_finite)


text \<open>We use this to redefine @{const subst_clause} and @{const subst_dnf} on list DNFs.\<close>

definition subst_clause' :: "'a ltln list \<Rightarrow> ('a ltln \<rightharpoonup> 'a ltln) \<Rightarrow> 'a ltln list set"
where
  "subst_clause' \<Phi> m = fold (\<lambda>\<phi> acc. acc \<otimes>\<^sub>l list_dnf (subst \<phi> m)) \<Phi> {[]}"

definition subst_dnf' :: "'a ltln list set \<Rightarrow> ('a ltln \<rightharpoonup> 'a ltln) \<Rightarrow> 'a ltln list set"
where
  "subst_dnf' \<A> m = (\<Union>\<Phi> \<in> \<A>. subst_clause' \<Phi> m)"

lemma subst_clause'_finite:
  "finite (subst_clause' \<Phi> m)"
  by (induction \<Phi> rule: rev_induct) (simp_all add: subst_clause'_def list_dnf_finite list_product_finite)

lemma subst_clause'_nil[simp]:
  "subst_clause' [] m = {[]}"
  by (simp add: subst_clause'_def)

lemma subst_clause'_cons[simp]:
  "subst_clause' (xs @ [x]) m = subst_clause' xs m \<otimes>\<^sub>l list_dnf (subst x m)"
  by (simp add: subst_clause'_def)

lemma subst_clause'_append[simp]:
  "subst_clause' (A @ B) m = subst_clause' A m \<otimes>\<^sub>l subst_clause' B m"
proof (induction B rule: rev_induct)
  case (snoc x xs)
  then show ?case
    by simp (metis append_assoc subst_clause'_cons)
qed(simp add: list_product_def)


lemma subst_dnf'_iff:
  "x \<in> subst_dnf' A m \<longleftrightarrow> (\<exists>\<Phi> \<in> A. x \<in> subst_clause' \<Phi> m)"
  by (simp add: subst_dnf'_def)

lemma subst_dnf'_product:
  "subst_dnf' (A \<otimes>\<^sub>l B) m = (subst_dnf' A m) \<otimes>\<^sub>l (subst_dnf' B m)" (is "?lhs = ?rhs")
proof (unfold set_eq_iff, safe)
  fix x
  assume "x \<in> ?lhs"

  then obtain \<Phi> where "\<Phi> \<in> A \<otimes>\<^sub>l B" and "x \<in> subst_clause' \<Phi> m"
    unfolding subst_dnf'_iff by blast

  then obtain a b where "a \<in> A" and "b \<in> B" and "\<Phi> = a @ b"
    unfolding list_product_def by blast

  then have "x \<in> (subst_clause' a m) \<otimes>\<^sub>l (subst_clause' b m)"
    using \<open>x \<in> subst_clause' \<Phi> m\<close> by simp

  then obtain a' b' where "a' \<in> subst_clause' a m" and "b' \<in> subst_clause' b m" and "x = a' @ b'"
    unfolding list_product_iff by blast

  then have "a' \<in> subst_dnf' A m" and "b' \<in> subst_dnf' B m"
    unfolding subst_dnf'_iff using \<open>a \<in> A\<close> \<open>b \<in> B\<close> by auto

  then have "\<exists>a\<in>subst_dnf' A m. \<exists>b\<in>subst_dnf' B m. x = a @ b"
    using \<open>x = a' @ b'\<close> by blast

  then show "x \<in> ?rhs"
    unfolding list_product_iff by blast
next
  fix x
  assume "x \<in> ?rhs"

  then obtain a b where "a \<in> subst_dnf' A m" and "b \<in> subst_dnf' B m" and "x = a @ b"
    unfolding list_product_iff by blast

  then obtain a' b' where "a' \<in> A" and "b' \<in> B" and a: "a \<in> subst_clause' a' m" and b: "b \<in> subst_clause' b' m"
    unfolding subst_dnf'_iff by blast

  then have "x \<in> (subst_clause' a' m) \<otimes>\<^sub>l (subst_clause' b' m)"
    unfolding list_product_iff using \<open>x = a @ b\<close> by blast

  moreover

  have "a' @ b' \<in> A \<otimes>\<^sub>l B"
    unfolding list_product_iff using \<open>a' \<in> A\<close> \<open>b' \<in> B\<close> by blast

  ultimately show "x \<in> ?lhs"
    unfolding subst_dnf'_iff by force
qed

lemma subst_dnf'_list_dnf:
  "subst_dnf' (list_dnf \<phi>) m = list_dnf (subst \<phi> m)"
proof (induction \<phi>)
  case (And_ltln \<phi>1 \<phi>2)
  then show ?case
    by (simp add: subst_dnf'_product)
qed (simp_all add: subst_dnf'_def subst_clause'_def list_product_def)


lemma min_set_Union:
  "finite X \<Longrightarrow> min_set (\<Union> (min_set ` X)) = min_set (\<Union> X)" for X :: "'a fset set set"
  by (induction X rule: finite_induct) (force, metis Sup_insert image_insert min_set_min_union min_union_def)

lemma min_set_Union_image:
  "finite X \<Longrightarrow> min_set (\<Union>x \<in> X. min_set (f x)) = min_set (\<Union>x \<in> X. f x)" for f :: "'b \<Rightarrow> 'a fset set"
proof -
  assume "finite X"

  then have *: "finite (f ` X)" by auto

  with min_set_Union show ?thesis
    unfolding image_image by fastforce
qed

lemma subst_clause_fset_of_list:
  "subst_clause (fset_of_list \<Phi>) m = min_set (list_dnf_to_dnf (subst_clause' \<Phi> m))"
  unfolding list_dnf_to_dnf_def subst_clause'_def
proof (induction \<Phi> rule: rev_induct)
  case (snoc x xs)
  then show ?case
    by simp (metis (no_types, lifting) dnf_min_set list_dnf_to_dnf_def list_dnf_to_dnf_list_dnf min_product_comm min_product_def min_set_min_product(1))
qed simp

lemma min_set_list_dnf_to_dnf_subst_dnf':
  "finite X \<Longrightarrow> min_set (list_dnf_to_dnf (subst_dnf' X m)) = min_set (subst_dnf (list_dnf_to_dnf X) m)"
  by (simp add: subst_dnf'_def subst_dnf_def subst_clause_fset_of_list list_dnf_to_dnf_def min_set_Union_image image_Union)

lemma subst_dnf_dnf:
  "min_set (subst_dnf (dnf \<phi>) m) = min_dnf (subst \<phi> m)"
  unfolding dnf_min_set
  unfolding list_dnf_to_dnf_list_dnf[symmetric]
  unfolding subst_dnf'_list_dnf[symmetric]
  unfolding min_set_list_dnf_to_dnf_subst_dnf'[OF list_dnf_finite]
  by simp


text \<open>This is almost the lemma we need. However, we need to show that the same holds for @{term "min_dnf \<phi>"}, too.\<close>

lemma fold_product:
  "Finite_Set.fold (\<lambda>x. (\<otimes>) {{|x|}}) {{||}} (fset x) = {x}"
  by (induction x) (simp_all add: notin_fset, simp add: product_singleton_singleton)

lemma fold_union:
  "Finite_Set.fold (\<lambda>x. (\<union>) {x}) {} (fset x) = fset x"
  by (induction x) (simp_all add: notin_fset comp_fun_idem.fold_insert_idem comp_fun_idem_insert)

lemma fold_union_fold_product:
  assumes "finite X" and "\<And>\<Psi> \<psi>. \<Psi> \<in> X \<Longrightarrow> \<psi> \<in> fset \<Psi> \<Longrightarrow> dnf \<psi> = {{|\<psi>|}}"
  shows "Finite_Set.fold (\<lambda>x. (\<union>) (Finite_Set.fold (\<lambda>\<phi>. (\<otimes>) (dnf \<phi>)) {{||}} (fset x))) {} X = X" (is "?lhs = X")
proof -
  from assms have "?lhs = Finite_Set.fold (\<lambda>x. (\<union>) (Finite_Set.fold (\<lambda>\<phi>. (\<otimes>) {{|\<phi>|}}) {{||}} (fset x))) {} X"
  proof (induction X rule: finite_induct)
    case (insert \<Phi> X)

    from insert.prems have 1: "\<And>\<Psi> \<psi>. \<lbrakk>\<Psi> \<in> X; \<psi> \<in> fset \<Psi>\<rbrakk> \<Longrightarrow> dnf \<psi> = {{|\<psi>|}}"
      by force

    from insert.prems have "Finite_Set.fold (\<lambda>\<phi>. (\<otimes>) (dnf \<phi>)) {{||}} (fset \<Phi>) = Finite_Set.fold (\<lambda>\<phi>. (\<otimes>) {{|\<phi>|}}) {{||}} (fset \<Phi>)"
      by (induction \<Phi>) (force simp: notin_fset)+

    with insert 1 show ?case
      by simp
  qed simp

  with \<open>finite X\<close> show ?thesis
    unfolding fold_product by (metis fset_to_fset fold_union)
qed

lemma dnf_ltln_of_dnf_min_dnf:
  "dnf (ltln_of_dnf (min_dnf \<phi>)) = min_dnf \<phi>"
proof -
  have 1: "finite (And\<^sub>n ` fset ` min_dnf \<phi>)"
    using min_dnf_finite by blast

  have 2: "inj_on And\<^sub>n (fset ` min_dnf \<phi>)"
    by (metis (mono_tags, lifting) And\<^sub>n_inj f_inv_into_f fset inj_onI inj_on_contraD)

  have 3: "inj_on fset (min_dnf \<phi>)"
    by (meson fset_inject inj_onI)

  show ?thesis
    unfolding ltln_of_dnf_def
    unfolding Or\<^sub>n_dnf[OF 1]
    unfolding fold_image[OF 2]
    unfolding fold_image[OF 3]
    unfolding comp_def
    unfolding And\<^sub>n_dnf[OF finite_fset]
    by (metis fold_union_fold_product min_dnf_finite min_dnf_atoms_dnf)
qed

lemma min_dnf_subst:
  "min_set (subst_dnf (min_dnf \<phi>) m) = min_dnf (subst \<phi> m)" (is "?lhs = ?rhs")
proof -
  let ?\<phi>' = "ltln_of_dnf (min_dnf \<phi>)"

  have "?lhs = min_set (subst_dnf (dnf ?\<phi>') m)"
    unfolding dnf_ltln_of_dnf_min_dnf ..

  also have "\<dots> = min_dnf (subst ?\<phi>' m)"
    unfolding subst_dnf_dnf ..

  also have "\<dots> = min_dnf (subst \<phi> m)"
    using ltl_prop_equiv_min_dnf ltln_of_dnf_prop_equiv subst_respects_ltl_prop_entailment(2) by blast

  finally show ?thesis .
qed

end
