(*  Title:      Containers/Card_Datatype.thy
    Author:     Andreas Lochbihler, ETH Zurich *)

theory Card_Datatype
imports "HOL-Library.Cardinality"
begin

section \<open>Definitions to prove equations about the cardinality of data types\<close>

subsection \<open>Specialised @{term range} constants\<close>

definition rangeIt :: "'a \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a set"
where "rangeIt x f = range (\<lambda>n. (f ^^ n) x)"

definition rangeC :: "('a \<Rightarrow> 'b) set \<Rightarrow> 'b set"
where "rangeC F = (\<Union>f \<in> F. range f)"

lemma infinite_rangeIt: 
  assumes inj: "inj f"
  and x: "\<forall>y. x \<noteq> f y"
  shows "\<not> finite (rangeIt x f)"
proof -
  have "inj (\<lambda>n. (f ^^ n) x)"
  proof(rule injI)
    fix n m
    assume "(f ^^ n) x = (f ^^ m) x"
    thus "n = m"
    proof(induct n arbitrary: m)
      case 0
      thus ?case using x by(cases m)(auto intro: sym)
    next
      case (Suc n)
      thus ?case using x by(cases m)(auto intro: sym dest: injD[OF inj])
    qed
  qed
  thus ?thesis
    by(auto simp add: rangeIt_def dest: finite_imageD)
qed

lemma in_rangeC: "f \<in> A \<Longrightarrow> f x \<in> rangeC A"
by(auto simp add: rangeC_def)

lemma in_rangeCE: assumes "y \<in> rangeC A"
  obtains f x where "f \<in> A" "y = f x"
using assms by(auto simp add: rangeC_def)

lemma in_rangeC_singleton: "f x \<in> rangeC {f}"
by(auto simp add: rangeC_def)

lemma in_rangeC_singleton_const: "x \<in> rangeC {\<lambda>_. x}"
by(rule in_rangeC_singleton)

lemma rangeC_rangeC: "f \<in> rangeC A \<Longrightarrow> f x \<in> rangeC (rangeC A)"
by(auto simp add: rangeC_def)

lemma rangeC_eq_empty: "rangeC A = {} \<longleftrightarrow> A = {}"
by(auto simp add: rangeC_def)

lemma Ball_rangeC_iff:
  "(\<forall>x \<in> rangeC A. P x) \<longleftrightarrow> (\<forall>f \<in> A. \<forall>x. P (f x))"
by(auto intro: in_rangeC elim: in_rangeCE)

lemma Ball_rangeC_singleton:
  "(\<forall>x \<in> rangeC {f}. P x) \<longleftrightarrow> (\<forall>x. P (f x))"
by(simp add: Ball_rangeC_iff)

lemma Ball_rangeC_rangeC:
  "(\<forall>x \<in> rangeC (rangeC A). P x) \<longleftrightarrow> (\<forall>f \<in> rangeC A. \<forall>x. P (f x))"
by(simp add: Ball_rangeC_iff)

lemma finite_rangeC:
  assumes inj: "\<forall>f \<in> A. inj f"
  and disjoint: "\<forall>f \<in> A. \<forall>g \<in> A. f \<noteq> g \<longrightarrow> (\<forall>x y. f x \<noteq> g y)"
  shows "finite (rangeC (A :: ('a \<Rightarrow> 'b) set)) \<longleftrightarrow> finite A \<and> (A \<noteq> {} \<longrightarrow> finite (UNIV :: 'a set))"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?lhs
  thus ?rhs using inj disjoint
  proof(induct "rangeC A" arbitrary: A rule: finite_psubset_induct)
    case (psubset A)
    show ?case
    proof(cases "A = {}")
      case True thus ?thesis by simp
    next
      case False
      then obtain f A' where A: "A = insert f A'" and f: "f \<in> A" "f \<notin> A'"
        by(fastforce dest: mk_disjoint_insert)
      from A have rA: "rangeC A = rangeC A' \<union> range f"
        by(auto simp add: rangeC_def)

      have "\<not> range f \<subseteq> rangeC A'" 
      proof
        assume "range f \<subseteq> rangeC A'"
        moreover obtain x where x: "x \<in> range f" by auto
        ultimately have "x \<in> rangeC A'" by auto
        then obtain g where "g \<in> A'" "x \<in> range g" by(auto simp add: rangeC_def)
        with \<open>f \<notin> A'\<close> A have "g \<in> A" "f \<noteq> g" by auto
        with \<open>f \<in> A\<close> have "\<And>x y. f x \<noteq> g y" by(rule psubset.prems[rule_format])
        thus False using x \<open>x \<in> range g\<close> by auto
      qed
      hence "rangeC A' \<subset> rangeC A" unfolding rA by auto
      hence "finite A' \<and> (A' \<noteq> {} \<longrightarrow> finite (UNIV :: 'a set))"
        using psubset.prems
        by -(erule psubset.hyps, auto simp add: A)
      with A have "finite A" by simp
      moreover with \<open>finite (rangeC A)\<close> A \<open>\<forall>f \<in> A. inj f\<close>
      have "finite (UNIV :: 'a set)"
        by(auto simp add: rangeC_def dest: finite_imageD)
      ultimately show ?thesis by blast
    qed
  qed
qed(auto simp add: rangeC_def)

lemma finite_rangeC_singleton_const:
  "finite (rangeC {\<lambda>_. x})"
by(auto simp add: rangeC_def image_def)

lemma card_Un:
  "\<lbrakk> finite A; finite B \<rbrakk> \<Longrightarrow> card (A \<union> B) = card (A) + card (B) - card(A \<inter> B)"
by(subst card_Un_Int) simp_all

lemma card_rangeC_singleton_const:
  "card (rangeC {\<lambda>_. f}) = 1"
by(simp add: rangeC_def image_def)

lemma card_rangeC:
  assumes inj: "\<forall>f \<in> A. inj f"
  and disjoint: "\<forall>f \<in> A. \<forall>g \<in> A. f \<noteq> g \<longrightarrow> (\<forall>x y. f x \<noteq> g y)"
  shows "card (rangeC (A :: ('a \<Rightarrow> 'b) set)) = CARD('a) * card A"
  (is "?lhs = ?rhs")
proof(cases "finite (UNIV :: 'a set) \<and> finite A")
  case False
  thus ?thesis using False finite_rangeC[OF assms]
    by(auto simp add: card_eq_0_iff rangeC_eq_empty)
next
  case True
  { fix f
    assume "f \<in> A"
    hence "card (range f) = CARD('a)" using inj by(simp add: card_image) }
  thus ?thesis using disjoint True unfolding rangeC_def
    by(subst card_UN_disjoint) auto
qed

lemma rangeC_Int_rangeC:
  "\<lbrakk> \<forall>f \<in> A. \<forall>g \<in> B. \<forall>x y. f x \<noteq> g y \<rbrakk> \<Longrightarrow> rangeC A \<inter> rangeC B = {}"
by(auto simp add: rangeC_def)

lemmas rangeC_simps =
  in_rangeC_singleton
  in_rangeC_singleton_const
  rangeC_rangeC
  rangeC_eq_empty
  Ball_rangeC_singleton
  Ball_rangeC_rangeC
  finite_rangeC
  finite_rangeC_singleton_const
  card_rangeC_singleton_const
  card_rangeC
  rangeC_Int_rangeC

bundle card_datatype =
  rangeC_simps [simp]
  card_Un [simp]
  fun_eq_iff [simp]
  Int_Un_distrib [simp]
  Int_Un_distrib2 [simp]
  card_eq_0_iff [simp]
  imageI [simp] image_eqI [simp del]
  conj_cong [cong]
  infinite_rangeIt [simp]

subsection \<open>Cardinality primitives for polymorphic HOL types\<close>

ML \<open>
structure Card_Simp_Rules = Named_Thms
(
  val name = @{binding card_simps}
  val description = "Simplification rules for cardinality of types"
)
\<close>
setup \<open>Card_Simp_Rules.setup\<close>

definition card_fun :: "nat \<Rightarrow> nat \<Rightarrow> nat"
where "card_fun a b = (if a \<noteq> 0 \<and> b \<noteq> 0 \<or> b = 1 then b ^ a else 0)"

lemma CARD_fun [card_simps]:
  "CARD('a \<Rightarrow> 'b) = card_fun CARD('a) CARD('b)"
by(simp add: card_fun card_fun_def)

definition card_sum :: "nat \<Rightarrow> nat \<Rightarrow> nat"
where "card_sum a b = (if a = 0 \<or> b = 0 then 0 else a + b)"

lemma CARD_sum [card_simps]:
  "CARD('a + 'b) = card_sum CARD('a) CARD('b)"
by(simp add: card_UNIV_sum card_sum_def)

definition card_option :: "nat \<Rightarrow> nat"
where "card_option n = (if n = 0 then 0 else Suc n)"

lemma CARD_option [card_simps]:
  "CARD('a option) = card_option CARD('a)"
by(simp add: card_option_def card_UNIV_option)

definition card_prod :: "nat \<Rightarrow> nat \<Rightarrow> nat"
where "card_prod a b = a * b"

lemma CARD_prod [card_simps]:
  "CARD('a * 'b) = card_prod CARD('a) CARD('b)"
by(simp add: card_prod_def)

definition card_list :: "nat \<Rightarrow> nat"
where "card_list _ = 0"

lemma CARD_list [card_simps]: "CARD('a list) = card_list CARD('a)"
by(simp add: card_list_def infinite_UNIV_listI)

end
