(*  Title:      Free_Boolean_Algebra.thy
    Author:     Brian Huffman, Portland State University
*)

section \<open>Free Boolean algebras\<close>

theory Free_Boolean_Algebra
imports Main
begin

(*<*)
notation
  bot ("\<bottom>") and
  top ("\<top>") and
  inf  (infixl "\<sqinter>" 70) and
  sup  (infixl "\<squnion>" 65)

lemma sup_conv_inf:
  fixes x y :: "'a::boolean_algebra"
  shows "x \<squnion> y = - (- x \<sqinter> - y)"
by simp
(*>*)

subsection \<open>Free boolean algebra as a set\<close>

text \<open>
  We start by defining the free boolean algebra over type @{typ 'a} as
  an inductive set.  Here \<open>i :: 'a\<close> represents a variable;
  \<open>A :: 'a set\<close> represents a valuation, assigning a truth
  value to each variable; and \<open>S :: 'a set set\<close> represents a
  formula, as the set of valuations that make the formula true.  The
  set \<open>fba\<close> contains representatives of formulas built from
  finite combinations of variables with negation and conjunction.
\<close>

inductive_set
  fba :: "'a set set set"
where
  var: "{A. i \<in> A} \<in> fba"
| Compl: "S \<in> fba \<Longrightarrow> - S \<in> fba"
| inter: "S \<in> fba \<Longrightarrow> T \<in> fba \<Longrightarrow> S \<inter> T \<in> fba"

lemma fba_Diff: "S \<in> fba \<Longrightarrow> T \<in> fba \<Longrightarrow> S - T \<in> fba"
unfolding Diff_eq by (intro fba.inter fba.Compl)

lemma fba_union: "S \<in> fba \<Longrightarrow> T \<in> fba \<Longrightarrow> S \<union> T \<in> fba"
proof -
  assume "S \<in> fba" and "T \<in> fba"
  hence "- (- S \<inter> - T) \<in> fba" by (intro fba.intros)
  thus "S \<union> T \<in> fba" by simp
qed

lemma fba_empty: "({} :: 'a set set) \<in> fba"
proof -
  obtain S :: "'a set set" where "S \<in> fba"
    by (fast intro: fba.var)
  hence "S \<inter> - S \<in> fba"
    by (intro fba.intros)
  thus ?thesis by simp
qed

lemma fba_UNIV: "(UNIV :: 'a set set) \<in> fba"
proof -
  have "- {} \<in> fba" using fba_empty by (rule fba.Compl)
  thus "UNIV \<in> fba" by simp
qed


subsection \<open>Free boolean algebra as a type\<close>

text \<open>
  The next step is to use \<open>typedef\<close> to define a type isomorphic
  to the set @{const fba}.  We also define a constructor \<open>var\<close>
  that corresponds with the similarly-named introduction rule for
  @{const fba}.
\<close>

typedef 'a formula = "fba :: 'a set set set"
  by (auto intro: fba_empty)

definition var :: "'a \<Rightarrow> 'a formula"
where "var i = Abs_formula {A. i \<in> A}"

lemma Rep_formula_var: "Rep_formula (var i) = {A. i \<in> A}"
unfolding var_def using fba.var by (rule Abs_formula_inverse)

text \<open>
  \medskip
  Now we make type @{typ "'a formula"} into a Boolean algebra.  This
  involves defining the various operations (ordering relations, binary
  infimum and supremum, complement, difference, top and bottom
  elements) and proving that they satisfy the appropriate laws.
\<close>

instantiation formula :: (type) boolean_algebra
begin

definition
  "x \<sqinter> y = Abs_formula (Rep_formula x \<inter> Rep_formula y)"

definition
  "x \<squnion> y = Abs_formula (Rep_formula x \<union> Rep_formula y)"

definition
  "\<top> = Abs_formula UNIV"

definition
  "\<bottom> = Abs_formula {}"

definition
  "x \<le> y \<longleftrightarrow> Rep_formula x \<subseteq> Rep_formula y"

definition
  "x < y \<longleftrightarrow> Rep_formula x \<subset> Rep_formula y"

definition
  "- x = Abs_formula (- Rep_formula x)"

definition
  "x - y = Abs_formula (Rep_formula x - Rep_formula y)"

lemma Rep_formula_inf:
  "Rep_formula (x \<sqinter> y) = Rep_formula x \<inter> Rep_formula y"
unfolding inf_formula_def
by (intro Abs_formula_inverse fba.inter Rep_formula)

lemma Rep_formula_sup:
  "Rep_formula (x \<squnion> y) = Rep_formula x \<union> Rep_formula y"
unfolding sup_formula_def
by (intro Abs_formula_inverse fba_union Rep_formula)

lemma Rep_formula_top: "Rep_formula \<top> = UNIV"
unfolding top_formula_def by (intro Abs_formula_inverse fba_UNIV)

lemma Rep_formula_bot: "Rep_formula \<bottom> = {}"
unfolding bot_formula_def by (intro Abs_formula_inverse fba_empty)

lemma Rep_formula_compl: "Rep_formula (- x) = - Rep_formula x"
unfolding uminus_formula_def
by (intro Abs_formula_inverse fba.Compl Rep_formula)

lemma Rep_formula_diff:
  "Rep_formula (x - y) = Rep_formula x - Rep_formula y"
unfolding minus_formula_def
by (intro Abs_formula_inverse fba_Diff Rep_formula)

lemmas eq_formula_iff = Rep_formula_inject [symmetric]

lemmas Rep_formula_simps =
  less_eq_formula_def less_formula_def eq_formula_iff
  Rep_formula_sup Rep_formula_inf Rep_formula_top Rep_formula_bot
  Rep_formula_compl Rep_formula_diff Rep_formula_var

instance proof
qed (unfold Rep_formula_simps, auto)

end

text \<open>
  \medskip
  The laws of a Boolean algebra do not require the top and bottom
  elements to be distinct, so the following rules must be proved
  separately:
\<close>

lemma bot_neq_top_formula [simp]: "(\<bottom> :: 'a formula) \<noteq> \<top>"
unfolding Rep_formula_simps by auto

lemma top_neq_bot_formula [simp]: "(\<top> :: 'a formula) \<noteq> \<bottom>"
unfolding Rep_formula_simps by auto

text \<open>
  \medskip
  Here we prove an essential property of a free Boolean algebra:
  all generators are independent.
\<close>

lemma var_le_var_simps [simp]:
  "var i \<le> var j \<longleftrightarrow> i = j"
  "\<not> var i \<le> - var j"
  "\<not> - var i \<le> var j"
unfolding Rep_formula_simps by fast+

lemma var_eq_var_simps [simp]:
  "var i = var j \<longleftrightarrow> i = j"
  "var i \<noteq> - var j"
  "- var i \<noteq> var j"
unfolding Rep_formula_simps set_eq_subset by fast+

text \<open>
  \medskip
  We conclude this section by proving an induction principle for
  formulas.  It mirrors the definition of the inductive set \<open>fba\<close>, with cases for variables, complements, and conjunction.
\<close>

lemma formula_induct [case_names var compl inf, induct type: formula]:
  fixes P :: "'a formula \<Rightarrow> bool"
  assumes 1: "\<And>i. P (var i)"
  assumes 2: "\<And>x. P x \<Longrightarrow> P (- x)"
  assumes 3: "\<And>x y. P x \<Longrightarrow> P y \<Longrightarrow> P (x \<sqinter> y)"
  shows "P x"
proof (induct x rule: Abs_formula_induct)
  fix y :: "'a set set"
  assume "y \<in> fba" thus "P (Abs_formula y)"
  proof (induct rule: fba.induct)
    case (var i)
    have "P (var i)" by (rule 1)
    thus ?case unfolding var_def .
  next
    case (Compl S)
    from \<open>P (Abs_formula S)\<close> have "P (- Abs_formula S)" by (rule 2)
    with \<open>S \<in> fba\<close> show ?case
      unfolding uminus_formula_def by (simp add: Abs_formula_inverse)
  next
    case (inter S T)
    from \<open>P (Abs_formula S)\<close> and \<open>P (Abs_formula T)\<close>
    have "P (Abs_formula S \<sqinter> Abs_formula T)" by (rule 3)
    with \<open>S \<in> fba\<close> and \<open>T \<in> fba\<close> show ?case
      unfolding inf_formula_def by (simp add: Abs_formula_inverse)
  qed
qed


subsection \<open>If-then-else for Boolean algebras\<close>

text \<open>
  This is a generic if-then-else operator for arbitrary Boolean
  algebras.
\<close>

definition
  ifte :: "'a::boolean_algebra \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a"
where
  "ifte a x y = (a \<sqinter> x) \<squnion> (- a \<sqinter> y)"

lemma ifte_top [simp]: "ifte \<top> x y = x"
unfolding ifte_def by simp

lemma ifte_bot [simp]: "ifte \<bottom> x y = y"
unfolding ifte_def by simp

lemma ifte_same: "ifte a x x = x"
unfolding ifte_def
by (simp add: inf_sup_distrib2 [symmetric] sup_compl_top)

lemma compl_ifte: "- ifte a x y = ifte a (- x) (- y)"
unfolding ifte_def
apply (rule order_antisym)
apply (simp add: inf_sup_distrib1 inf_sup_distrib2 compl_inf_bot)
apply (simp add: sup_inf_distrib1 sup_inf_distrib2 sup_compl_top)
apply (simp add: le_infI1 le_infI2 le_supI1 le_supI2)
apply (simp add: le_infI1 le_infI2 le_supI1 le_supI2)
done

lemma inf_ifte_distrib:
  "ifte x a b \<sqinter> ifte x c d = ifte x (a \<sqinter> c) (b \<sqinter> d)"
unfolding ifte_def
apply (simp add: inf_sup_distrib1 inf_sup_distrib2)
apply (simp add: inf_sup_aci inf_compl_bot)
done

lemma ifte_ifte_distrib:
  "ifte x (ifte y a b) (ifte y c d) = ifte y (ifte x a c) (ifte x b d)"
unfolding ifte_def [of x] sup_conv_inf
by (simp only: compl_ifte [symmetric] inf_ifte_distrib [symmetric] ifte_same)


subsection \<open>Formulas over a set of generators\<close>

text \<open>
  The set \<open>formulas S\<close> consists of those formulas that only
  depend on variables in the set \<open>S\<close>.  It is analogous to the
  @{const lists} operator for the list datatype.
\<close>

definition
  formulas :: "'a set \<Rightarrow> 'a formula set"
where
  "formulas S =
    {x. \<forall>A B. (\<forall>i\<in>S. i \<in> A \<longleftrightarrow> i \<in> B) \<longrightarrow>
      A \<in> Rep_formula x \<longleftrightarrow> B \<in> Rep_formula x}"

lemma formulasI:
  assumes "\<And>A B. \<forall>i\<in>S. i \<in> A \<longleftrightarrow> i \<in> B
    \<Longrightarrow> A \<in> Rep_formula x \<longleftrightarrow> B \<in> Rep_formula x"
  shows "x \<in> formulas S"
using assms unfolding formulas_def by simp

lemma formulasD:
  assumes "x \<in> formulas S"
  assumes "\<forall>i\<in>S. i \<in> A \<longleftrightarrow> i \<in> B"
  shows "A \<in> Rep_formula x \<longleftrightarrow> B \<in> Rep_formula x"
using assms unfolding formulas_def by simp

lemma formulas_mono: "S \<subseteq> T \<Longrightarrow> formulas S \<subseteq> formulas T"
by (fast intro!: formulasI elim!: formulasD)

lemma formulas_insert: "x \<in> formulas S \<Longrightarrow> x \<in> formulas (insert a S)"
unfolding formulas_def by simp

lemma formulas_var: "i \<in> S \<Longrightarrow> var i \<in> formulas S"
unfolding formulas_def by (simp add: Rep_formula_simps)

lemma formulas_var_iff: "var i \<in> formulas S \<longleftrightarrow> i \<in> S"
unfolding formulas_def by (simp add: Rep_formula_simps, fast)

lemma formulas_bot: "\<bottom> \<in> formulas S"
unfolding formulas_def by (simp add: Rep_formula_simps)

lemma formulas_top: "\<top> \<in> formulas S"
unfolding formulas_def by (simp add: Rep_formula_simps)

lemma formulas_compl: "x \<in> formulas S \<Longrightarrow> - x \<in> formulas S"
unfolding formulas_def by (simp add: Rep_formula_simps)

lemma formulas_inf:
  "x \<in> formulas S \<Longrightarrow> y \<in> formulas S \<Longrightarrow> x \<sqinter> y \<in> formulas S"
unfolding formulas_def by (auto simp add: Rep_formula_simps)

lemma formulas_sup:
  "x \<in> formulas S \<Longrightarrow> y \<in> formulas S \<Longrightarrow> x \<squnion> y \<in> formulas S"
unfolding formulas_def by (auto simp add: Rep_formula_simps)

lemma formulas_diff:
  "x \<in> formulas S \<Longrightarrow> y \<in> formulas S \<Longrightarrow> x - y \<in> formulas S"
unfolding formulas_def by (auto simp add: Rep_formula_simps)

lemma formulas_ifte:
  "a \<in> formulas S \<Longrightarrow> x \<in> formulas S \<Longrightarrow> y \<in> formulas S \<Longrightarrow>
    ifte a x y \<in> formulas S"
unfolding ifte_def
by (intro formulas_sup formulas_inf formulas_compl)

lemmas formulas_intros =
  formulas_var formulas_bot formulas_top formulas_compl
  formulas_inf formulas_sup formulas_diff formulas_ifte


subsection \<open>Injectivity of if-then-else\<close>

text \<open>
  The if-then-else operator is injective in some limited
  circumstances: when the scrutinee is a variable that is not
  mentioned in either branch.
\<close>

lemma ifte_inject:
  assumes "ifte (var i) x y = ifte (var i) x' y'" 
  assumes "i \<notin> S"
  assumes "x \<in> formulas S" and "x' \<in> formulas S"
  assumes "y \<in> formulas S" and "y' \<in> formulas S"
  shows "x = x' \<and> y = y'"
proof
  have 1: "\<And>A. i \<in> A \<Longrightarrow> A \<in> Rep_formula x \<longleftrightarrow> A \<in> Rep_formula x'"
    using assms(1)
    by (simp add: Rep_formula_simps ifte_def set_eq_iff, fast)
  have 2: "\<And>A. i \<notin> A \<Longrightarrow> A \<in> Rep_formula y \<longleftrightarrow> A \<in> Rep_formula y'"
    using assms(1)
    by (simp add: Rep_formula_simps ifte_def set_eq_iff, fast)

  show "x = x'"
  unfolding Rep_formula_simps
  proof (rule set_eqI)
    fix A
    have "A \<in> Rep_formula x \<longleftrightarrow> insert i A \<in> Rep_formula x"
      using \<open>x \<in> formulas S\<close> by (rule formulasD, force simp add: \<open>i \<notin> S\<close>)
    also have "\<dots> \<longleftrightarrow> insert i A \<in> Rep_formula x'"
      by (rule 1, simp)
    also have "\<dots> \<longleftrightarrow> A \<in> Rep_formula x'"
      using \<open>x' \<in> formulas S\<close> by (rule formulasD, force simp add: \<open>i \<notin> S\<close>)
    finally show "A \<in> Rep_formula x \<longleftrightarrow> A \<in> Rep_formula x'" .
  qed
  show  "y = y'"
  unfolding Rep_formula_simps
  proof (rule set_eqI)
    fix A
    have "A \<in> Rep_formula y \<longleftrightarrow> A - {i} \<in> Rep_formula y"
      using \<open>y \<in> formulas S\<close> by (rule formulasD, force simp add: \<open>i \<notin> S\<close>)
    also have "\<dots> \<longleftrightarrow> A - {i} \<in> Rep_formula y'"
      by (rule 2, simp)
    also have "\<dots> \<longleftrightarrow> A \<in> Rep_formula y'"
      using \<open>y' \<in> formulas S\<close> by (rule formulasD, force simp add: \<open>i \<notin> S\<close>)
    finally show "A \<in> Rep_formula y \<longleftrightarrow> A \<in> Rep_formula y'" .
  qed
qed


subsection \<open>Specification of homomorphism operator\<close>

text \<open>
  Our goal is to define a homomorphism operator \<open>hom\<close> such that
  for any function \<open>f\<close>, \<open>hom f\<close> is the unique Boolean
  algebra homomorphism satisfying \<open>hom f (var i) = f i\<close>
  for all \<open>i\<close>.

  Instead of defining \<open>hom\<close> directly, we will follow the
  approach used to define Isabelle's \<open>fold\<close> operator for finite
  sets.  First we define the graph of the \<open>hom\<close> function as a
  relation; later we will define the \<open>hom\<close> function itself using
  definite choice.

  The \<open>hom_graph\<close> relation is defined inductively, with
  introduction rules based on the if-then-else normal form of Boolean
  formulas.  The relation is also indexed by an extra set parameter
  \<open>S\<close>, to ensure that branches of each if-then-else do not use
  the same variable again.
\<close>

inductive
  hom_graph ::
    "('a \<Rightarrow> 'b::boolean_algebra) \<Rightarrow> 'a set \<Rightarrow> 'a formula \<Rightarrow> 'b \<Rightarrow> bool"
  for f :: "'a \<Rightarrow> 'b::boolean_algebra"
where
  bot: "hom_graph f {} bot bot"
| top: "hom_graph f {} top top"
| ifte: "i \<notin> S \<Longrightarrow> hom_graph f S x a \<Longrightarrow> hom_graph f S y b \<Longrightarrow>
  hom_graph f (insert i S) (ifte (var i) x y) (ifte (f i) a b)"

text \<open>
  \medskip
  The next two lemmas establish a stronger elimination rule for
  assumptions of the form @{term "hom_graph f (insert i S) x a"}.
  Essentially, they say that we can arrange the top-level if-then-else
  to use the variable of our choice.  The proof makes use of the
  distributive properties of if-then-else.
\<close>

lemma hom_graph_dest:
  "hom_graph f S x a \<Longrightarrow> k \<in> S \<Longrightarrow> \<exists>y z b c.
    x = ifte (var k) y z \<and> a = ifte (f k) b c \<and>
    hom_graph f (S - {k}) y b \<and> hom_graph f (S - {k}) z c"
proof (induct set: hom_graph)
  case (ifte i S x a y b) show ?case
  proof (cases "i = k")
    assume "i = k" with ifte(1,2,4) show ?case by auto
  next
    assume "i \<noteq> k"
    with \<open>k \<in> insert i S\<close> have k: "k \<in> S" by simp
    have *: "insert i S - {k} = insert i (S - {k})"
      using \<open>i \<noteq> k\<close> by (simp add: insert_Diff_if)
    have **: "i \<notin> S - {k}" using \<open>i \<notin> S\<close> by simp
    from ifte(1) ifte(3) [OF k] ifte(5) [OF k]
    show ?case
      unfolding *
      apply clarify
      apply (simp only: ifte_ifte_distrib [of "var i"])
      apply (simp only: ifte_ifte_distrib [of "f i"])
      apply (fast intro: hom_graph.ifte [OF **])
      done
  qed
qed simp_all

lemma hom_graph_insert_elim:
  assumes "hom_graph f (insert i S) x a" and "i \<notin> S"
  obtains y z b c
  where "x = ifte (var i) y z"
    and "a = ifte (f i) b c"
    and "hom_graph f S y b"
    and "hom_graph f S z c"
using hom_graph_dest [OF assms(1) insertI1]
by (clarify, simp add: assms(2))

text \<open>
  \medskip
  Now we prove the first uniqueness property of the @{const hom_graph}
  relation.  This version of uniqueness says that for any particular
  value of \<open>S\<close>, the relation @{term "hom_graph f S"} maps each
  \<open>x\<close> to at most one \<open>a\<close>.  The proof uses the
  injectiveness of if-then-else, which we proved earlier.
\<close>

lemma hom_graph_imp_formulas:
  "hom_graph f S x a \<Longrightarrow> x \<in> formulas S"
by (induct set: hom_graph, simp_all add: formulas_intros formulas_insert)

lemma hom_graph_unique:
  "hom_graph f S x a \<Longrightarrow> hom_graph f S x a' \<Longrightarrow> a = a'"
proof (induct arbitrary: a' set: hom_graph)
  case (ifte i S y b z c a')
  from ifte(6,1) obtain y' z' b' c'
    where 1: "ifte (var i) y z = ifte (var i) y' z'"
      and 2: "a' = ifte (f i) b' c'"
      and 3: "hom_graph f S y' b'"
      and 4: "hom_graph f S z' c'"
    by (rule hom_graph_insert_elim)
  from 1 3 4 ifte(1,2,4) have "y = y' \<and> z = z'"
    by (intro ifte_inject hom_graph_imp_formulas)
  with 2 3 4 ifte(3,5) show "ifte (f i) b c = a'"
    by simp
qed (erule hom_graph.cases, simp_all)+

text \<open>
  \medskip
  The next few lemmas will help to establish a stronger version of the
  uniqueness property of @{const hom_graph}.  They show that the @{const
  hom_graph} relation is preserved if we replace \<open>S\<close> with a
  larger finite set.
\<close>

lemma hom_graph_insert:
  assumes "hom_graph f S x a"
  shows "hom_graph f (insert i S) x a"
proof (cases "i \<in> S")
  assume "i \<in> S" with assms show ?thesis by (simp add: insert_absorb)
next
  assume "i \<notin> S"
  hence "hom_graph f (insert i S) (ifte (var i) x x) (ifte (f i) a a)"
    by (intro hom_graph.ifte assms)
  thus "hom_graph f (insert i S) x a"
    by (simp only: ifte_same)
qed

lemma hom_graph_finite_superset:
  assumes "hom_graph f S x a" and "finite T" and "S \<subseteq> T"
  shows "hom_graph f T x a"
proof -
  from \<open>finite T\<close> have "hom_graph f (S \<union> T) x a"
    by (induct set: finite, simp add: assms, simp add: hom_graph_insert)
  with \<open>S \<subseteq> T\<close> show "hom_graph f T x a"
    by (simp only: subset_Un_eq)
qed

lemma hom_graph_imp_finite:
  "hom_graph f S x a \<Longrightarrow> finite S"
by (induct set: hom_graph) simp_all

text \<open>
  \medskip
  This stronger uniqueness property says that @{term "hom_graph f"}
  maps each \<open>x\<close> to at most one \<open>a\<close>, even for
  \emph{different} values of the set parameter.
\<close>

lemma hom_graph_unique':
  assumes "hom_graph f S x a" and "hom_graph f T x a'"
  shows "a = a'"
proof (rule hom_graph_unique)
  have fin: "finite (S \<union> T)"
    using assms by (intro finite_UnI hom_graph_imp_finite)
  show "hom_graph f (S \<union> T) x a"
    using assms(1) fin Un_upper1 by (rule hom_graph_finite_superset)
  show "hom_graph f (S \<union> T) x a'"
    using assms(2) fin Un_upper2 by (rule hom_graph_finite_superset)
qed

text \<open>
  \medskip
  Finally, these last few lemmas establish that the @{term "hom_graph
  f"} relation is total: every \<open>x\<close> is mapped to some \<open>a\<close>.
\<close>

lemma hom_graph_var: "hom_graph f {i} (var i) (f i)"
proof -
  have "hom_graph f {i} (ifte (var i) top bot) (ifte (f i) top bot)"
    by (simp add: hom_graph.intros)
  thus "hom_graph f {i} (var i) (f i)"
    unfolding ifte_def by simp
qed

lemma hom_graph_compl:
  "hom_graph f S x a \<Longrightarrow> hom_graph f S (- x) (- a)"
by (induct set: hom_graph, simp_all add: hom_graph.intros compl_ifte)

lemma hom_graph_inf:
  "hom_graph f S x a \<Longrightarrow> hom_graph f S y b \<Longrightarrow>
   hom_graph f S (x \<sqinter> y) (a \<sqinter> b)"
 apply (induct arbitrary: y b set: hom_graph)
   apply (simp add: hom_graph.bot)
  apply simp
 apply (erule (1) hom_graph_insert_elim)
 apply (auto simp add: inf_ifte_distrib hom_graph.ifte)
done

lemma hom_graph_union_inf:
  assumes "hom_graph f S x a" and "hom_graph f T y b"
  shows "hom_graph f (S \<union> T) (x \<sqinter> y) (a \<sqinter> b)"
proof (rule hom_graph_inf)
  have fin: "finite (S \<union> T)"
    using assms by (intro finite_UnI hom_graph_imp_finite)
  show "hom_graph f (S \<union> T) x a"
    using assms(1) fin Un_upper1 by (rule hom_graph_finite_superset)
  show "hom_graph f (S \<union> T) y b"
    using assms(2) fin Un_upper2 by (rule hom_graph_finite_superset)
qed

lemma hom_graph_exists: "\<exists>a S. hom_graph f S x a"
by (induct x)
   (auto intro: hom_graph_var hom_graph_compl hom_graph_union_inf)


subsection \<open>Homomorphisms into other boolean algebras\<close>

text \<open>
  Now that we have proved the necessary existence and uniqueness
  properties of @{const hom_graph}, we can define the function \<open>hom\<close> using definite choice.
\<close>

definition
  hom :: "('a \<Rightarrow> 'b::boolean_algebra) \<Rightarrow> 'a formula \<Rightarrow> 'b"
where
  "hom f x = (THE a. \<exists>S. hom_graph f S x a)"

lemma hom_graph_hom: "\<exists>S. hom_graph f S x (hom f x)"
unfolding hom_def
apply (rule theI')
apply (rule ex_ex1I)
apply (rule hom_graph_exists)
apply (fast elim: hom_graph_unique')
done

lemma hom_equality:
  "hom_graph f S x a \<Longrightarrow> hom f x = a"
unfolding hom_def
apply (rule the_equality)
apply (erule exI)
apply (erule exE)
apply (erule (1) hom_graph_unique')
done

text \<open>
  \medskip
  The @{const hom} function correctly implements its specification:
\<close>

lemma hom_var [simp]: "hom f (var i) = f i"
by (rule hom_equality, rule hom_graph_var)

lemma hom_bot [simp]: "hom f \<bottom> = \<bottom>"
by (rule hom_equality, rule hom_graph.bot)

lemma hom_top [simp]: "hom f \<top> = \<top>"
by (rule hom_equality, rule hom_graph.top)

lemma hom_compl [simp]: "hom f (- x) = - hom f x"
proof -
  obtain S where "hom_graph f S x (hom f x)"
    using hom_graph_hom ..
  hence "hom_graph f S (- x) (- hom f x)"
    by (rule hom_graph_compl)
  thus "hom f (- x) = - hom f x"
    by (rule hom_equality)
qed

lemma hom_inf [simp]: "hom f (x \<sqinter> y) = hom f x \<sqinter> hom f y"
proof -
  obtain S where S: "hom_graph f S x (hom f x)"
    using hom_graph_hom ..
  obtain T where T: "hom_graph f T y (hom f y)"
    using hom_graph_hom ..
  have "hom_graph f (S \<union> T) (x \<sqinter> y) (hom f x \<sqinter> hom f y)"
    using S T by (rule hom_graph_union_inf)
  thus ?thesis by (rule hom_equality)
qed

lemma hom_sup [simp]: "hom f (x \<squnion> y) = hom f x \<squnion> hom f y"
unfolding sup_conv_inf by (simp only: hom_compl hom_inf)

lemma hom_diff [simp]: "hom f (x - y) = hom f x - hom f y"
unfolding diff_eq by (simp only: hom_compl hom_inf)

lemma hom_ifte [simp]:
  "hom f (ifte x y z) = ifte (hom f x) (hom f y) (hom f z)"
unfolding ifte_def by (simp only: hom_compl hom_inf hom_sup)

lemmas hom_simps =
  hom_var hom_bot hom_top hom_compl
  hom_inf hom_sup hom_diff hom_ifte

text \<open>
  \medskip
  The type @{typ "'a formula"} can be viewed as a monad, with @{const
  var} as the unit, and @{const hom} as the bind operator.  We can
  prove the standard monad laws with simple proofs by induction.
\<close>

lemma hom_var_eq_id: "hom var x = x"
by (induct x) simp_all

lemma hom_hom: "hom f (hom g x) = hom (\<lambda>i. hom f (g i)) x"
by (induct x) simp_all


subsection \<open>Map operation on Boolean formulas\<close>

text \<open>
  We can define a map functional in terms of @{const hom} and @{const
  var}.  The properties of \<open>fmap\<close> follow directly from the
  lemmas we have already proved about @{const hom}.
\<close>

definition
  fmap :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a formula \<Rightarrow> 'b formula"
where
  "fmap f = hom (\<lambda>i. var (f i))"

lemma fmap_var [simp]: "fmap f (var i) = var (f i)"
unfolding fmap_def by simp

lemma fmap_bot [simp]: "fmap f \<bottom> = \<bottom>"
unfolding fmap_def by simp

lemma fmap_top [simp]: "fmap f \<top> = \<top>"
unfolding fmap_def by simp

lemma fmap_compl [simp]: "fmap f (- x) = - fmap f x"
unfolding fmap_def by simp

lemma fmap_inf [simp]: "fmap f (x \<sqinter> y) = fmap f x \<sqinter> fmap f y"
unfolding fmap_def by simp

lemma fmap_sup [simp]: "fmap f (x \<squnion> y) = fmap f x \<squnion> fmap f y"
unfolding fmap_def by simp

lemma fmap_diff [simp]: "fmap f (x - y) = fmap f x - fmap f y"
unfolding fmap_def by simp

lemma fmap_ifte [simp]:
  "fmap f (ifte x y z) = ifte (fmap f x) (fmap f y) (fmap f z)"
unfolding fmap_def by simp

lemmas fmap_simps =
  fmap_var fmap_bot fmap_top fmap_compl
  fmap_inf fmap_sup fmap_diff fmap_ifte

text \<open>
  \medskip
  The map functional satisfies the functor laws: it preserves identity
  and function composition.
\<close>

lemma fmap_ident: "fmap (\<lambda>i. i) x = x"
by (induct x) simp_all

lemma fmap_fmap: "fmap f (fmap g x) = fmap (f \<circ> g) x"
by (induct x) simp_all


subsection \<open>Hiding lattice syntax\<close>

text \<open>
  The following command hides the lattice syntax, to avoid potential
  conflicts with other theories that import this one.  To re-enable
  the syntax, users should import theory \<open>Lattice_Syntax\<close> from
  the Isabelle library.
\<close>

no_notation
  top ("\<top>") and
  bot ("\<bottom>") and
  inf  (infixl "\<sqinter>" 70) and
  sup  (infixl "\<squnion>" 65)

end
