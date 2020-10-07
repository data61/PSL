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

text \<open>We use the propositional representation of LTL formulas to define
      the minimal disjunctive normal form of our formulas. For this purpose
      we define the minimal product $\otimes_m$ and union $\cup_m$.
      In the end we show that for a set $\mathcal{A}$ of literals,
      $\mathcal{A} \models \varphi$ if, and only if, there exists a subset
      of $\mathcal{A}$ in the minimal DNF of $\varphi$.\<close>


subsection \<open>Definition on minimum sets\<close>

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

definition min_product_set :: "'a fset set set \<Rightarrow> 'a fset set" ("\<Otimes>\<^sub>m")
  where "\<Otimes>\<^sub>m X = Finite_Set.fold min_product {{||}} X"

definition min_union :: "'a fset set \<Rightarrow> 'a fset set \<Rightarrow> 'a fset set" (infixr "\<union>\<^sub>m" 65)
  where "A \<union>\<^sub>m B = min_set (A \<union> B)"


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

lemma min_product_set_empty[simp]:
  "\<Otimes>\<^sub>m {} = {{||}}"
  by (simp add: min_product_set_def)

lemma product_empty_singleton[simp]:
  "A \<otimes> {{||}} = A"
  "{{||}} \<otimes> A = A"
  by (simp_all add: product_def)

lemma min_product_empty_singleton[simp]:
  "A \<otimes>\<^sub>m {{||}} = min_set A"
  "{{||}} \<otimes>\<^sub>m A = min_set A"
  by (simp_all add: min_product_def)


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


lemma min_product_set_insert[simp]:
  "finite X \<Longrightarrow> \<Otimes>\<^sub>m (insert x X) = x \<otimes>\<^sub>m (\<Otimes>\<^sub>m X)"
  unfolding min_product_set_def min_product_set_thms.fold_insert_idem ..

lemma min_product_subseteq:
  "x \<in> A \<otimes>\<^sub>m B \<Longrightarrow> \<exists>a. a |\<subseteq>| x \<and> a \<in> A"
  by (metis funion_upper1 min_product_iff)

lemma min_product_set_subseteq:
  "finite X \<Longrightarrow> x \<in> \<Otimes>\<^sub>m X \<Longrightarrow> A \<in> X \<Longrightarrow> \<exists>a \<in> A. a |\<subseteq>| x"
  by (induction X rule: finite_induct) (blast, metis finite_insert insert_absorb min_product_set_insert min_product_subseteq)


lemma min_product_min_set[simp]:
  "min_set (A \<otimes>\<^sub>m B) = A \<otimes>\<^sub>m B"
  by (simp add: min_product_def)

lemma min_product_set_min_set[simp]:
  "finite X \<Longrightarrow> min_set (\<Otimes>\<^sub>m X) = \<Otimes>\<^sub>m X"
  by (induction X rule: finite_induct) (auto simp add: min_product_set_def min_set_iff)

lemma min_union_min_set[simp]:
  "min_set (A \<union>\<^sub>m B) = A \<union>\<^sub>m B"
  by (simp add: min_union_def)


lemma min_product_set_union[simp]:
  "finite X \<Longrightarrow> finite Y \<Longrightarrow> \<Otimes>\<^sub>m (X \<union> Y) = (\<Otimes>\<^sub>m X) \<otimes>\<^sub>m (\<Otimes>\<^sub>m Y)"
  by (induction X rule: finite_induct) simp_all


lemma product_finite:
  "finite A \<Longrightarrow> finite B \<Longrightarrow> finite (A \<otimes> B)"
  by (simp add: product_def finite_image_set2)

lemma min_product_finite:
  "finite A \<Longrightarrow> finite B \<Longrightarrow> finite (A \<otimes>\<^sub>m B)"
  by (metis min_product_def product_finite min_set_finite)

lemma min_product_set_finite:
  "finite X \<Longrightarrow> (\<And>x. x \<in> X \<Longrightarrow> finite x) \<Longrightarrow> finite (\<Otimes>\<^sub>m X)"
  by (induction X rule: finite_induct) (simp_all add: min_product_set_def, insert min_product_finite, blast)

lemma min_union_finite:
  "finite A \<Longrightarrow> finite B \<Longrightarrow> finite (A \<union>\<^sub>m B)"
  by (simp add: min_union_def min_set_finite)



subsection \<open>Minimal Disjunctive Normal Form\<close>

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
  "A \<in> dnf \<phi> \<Longrightarrow> fset A \<subseteq> prop_atoms \<phi>"
  by (induction \<phi> arbitrary: A) (auto simp: product_def, blast+)

lemma min_dnf_prop_atoms:
  "A \<in> min_dnf \<phi> \<Longrightarrow> fset A \<subseteq> prop_atoms \<phi>"
  by (induction \<phi> arbitrary: A) (simp_all add: min_product_iff min_union_iff, fastforce+)

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

export_code dnf min_dnf checking



subsection \<open>DNF to LTL conversion\<close>

abbreviation And\<^sub>n :: "'a ltln list \<Rightarrow> 'a ltln"
where
  "And\<^sub>n xs \<equiv> foldr And_ltln xs true\<^sub>n"

abbreviation Or\<^sub>n :: "'a ltln list \<Rightarrow> 'a ltln"
where
  "Or\<^sub>n xs \<equiv> foldr Or_ltln xs false\<^sub>n"

lemma And\<^sub>n_semantics:
  "w \<Turnstile>\<^sub>n And\<^sub>n xs \<longleftrightarrow> (\<forall>x \<in> set xs. w \<Turnstile>\<^sub>n x)"
  by (induction xs) auto

lemma Or\<^sub>n_semantics:
  "w \<Turnstile>\<^sub>n Or\<^sub>n xs \<longleftrightarrow> (\<exists>x \<in> set xs. w \<Turnstile>\<^sub>n x)"
  by (induction xs) auto

lemma And\<^sub>n_prop_entailment:
  "\<A> \<Turnstile>\<^sub>P And\<^sub>n xs \<longleftrightarrow> (\<forall>x \<in> set xs. \<A> \<Turnstile>\<^sub>P x)"
  by (induction xs) auto

lemma Or\<^sub>n_prop_entailment:
  "\<A> \<Turnstile>\<^sub>P Or\<^sub>n xs \<longleftrightarrow> (\<exists>x \<in> set xs. \<A> \<Turnstile>\<^sub>P x)"
  by (induction xs) auto

end
