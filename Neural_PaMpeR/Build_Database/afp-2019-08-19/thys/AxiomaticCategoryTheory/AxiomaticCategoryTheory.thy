(*<*)
theory AxiomaticCategoryTheory imports Main

abbrevs
 f_neg="\<^bold>\<not>" and f_or="\<^bold>\<or>" and f_and="\<^bold>\<and>" and f_impl="\<^bold>\<rightarrow>" and f_imp="\<^bold>\<leftarrow>" and mequ="\<^bold>\<leftrightarrow>" and f_all="\<^bold>\<forall>"
 and f_exi="\<^bold>\<exists>" and f_all2="(\<^bold>\<forall>x.)" and f_exi2="(\<^bold>\<exists>x.)" and f_kleeneeq="\<cong>" and f_primeq="\<simeq>" and
 f_comp2="(\<cdot>)" and f_comp="\<cdot>"

begin
 (*Begin: some useful parameter settings*)
  declare [[ smt_solver = cvc4, smt_oracle = true ]]
  nitpick_params[user_axioms, show_all, format = 2, expect = genuine]
  sledgehammer_params[overlord]
 (*End: some useful parameter settings*)
(*>*)

section\<open>Introduction\<close>

  text\<open>This document provides a concise overview on the core results of our previous
       work @{cite "C67,R58,C57"} on the exploration of axiom systems for category theory.
       Extending the previous studies we
       include one further axiomatic theory in our experiments. This additional
       theory has been suggested by Mac Lane~@{cite "MacLane48"} in
       1948. We show that the axioms proposed by Mac Lane are equivalent to the ones studied
       in~@{cite "R58"}, which includes an axioms set suggested by Scott~@{cite "Scott79"}
       in the 1970s and another axioms set proposed by Freyd and Scedrov~@{cite "FreydScedrov90"} in 1990,
       which we slightly modified in~@{cite "R58"} to remedy a minor technical issue.

      The explanations given below are minimal, for more details we refer to the referenced
      papers, in particular, to~@{cite "R58"}.\<close>


section\<open>Embedding of Free Logic in HOL\<close>

text\<open>We introduce a shallow semantical embedding of free logic @{cite "R58"} in Isabelle/HOL.
     Definite description is omitted, since it is not needed in the studies below and also
     since the definition provided in @{cite "C57"} introduces the here undesired commitment
     that at least one non-existing element of type $i$ is a priori given. We here want to
     consider this an optional condition.\<close>

 typedecl i \<comment> \<open>Type for individuals\<close>
 consts fExistence:: "i\<Rightarrow>bool" ("E") \<comment> \<open>Existence/definedness predicate in free logic\<close>

 abbreviation fNot   ("\<^bold>\<not>")               where "\<^bold>\<not>\<phi> \<equiv> \<not>\<phi>"
 abbreviation fImpl  (infixr "\<^bold>\<rightarrow>" 13)  where "\<phi> \<^bold>\<rightarrow> \<psi> \<equiv> \<phi> \<longrightarrow> \<psi>"
 abbreviation fId     (infixr "\<^bold>=" 25)   where "l \<^bold>= r \<equiv> l = r"
 abbreviation fAll    ("\<^bold>\<forall>")               where "\<^bold>\<forall>\<Phi> \<equiv> \<forall>x. E x \<longrightarrow> \<Phi> x"
 abbreviation fAllBi (binder "\<^bold>\<forall>" [8]9) where "\<^bold>\<forall>x. \<phi> x \<equiv> \<^bold>\<forall>\<phi>"
 abbreviation fOr    (infixr "\<^bold>\<or>" 21)     where "\<phi> \<^bold>\<or> \<psi> \<equiv> (\<^bold>\<not>\<phi>) \<^bold>\<rightarrow> \<psi>"
 abbreviation fAnd   (infixr "\<^bold>\<and>" 22)     where "\<phi> \<^bold>\<and> \<psi> \<equiv> \<^bold>\<not>(\<^bold>\<not>\<phi> \<^bold>\<or> \<^bold>\<not>\<psi>)"
 abbreviation fImpli (infixr "\<^bold>\<leftarrow>" 13)    where "\<phi> \<^bold>\<leftarrow> \<psi> \<equiv> \<psi> \<^bold>\<rightarrow> \<phi>"
 abbreviation fEquiv (infixr "\<^bold>\<leftrightarrow>" 15)    where "\<phi> \<^bold>\<leftrightarrow> \<psi> \<equiv> (\<phi> \<^bold>\<rightarrow> \<psi>) \<^bold>\<and> (\<psi> \<^bold>\<rightarrow> \<phi>)"
 abbreviation fEx     ("\<^bold>\<exists>")                 where "\<^bold>\<exists>\<Phi> \<equiv> \<^bold>\<not>(\<^bold>\<forall>(\<lambda>y. \<^bold>\<not>(\<Phi> y)))"
 abbreviation fExiBi (binder "\<^bold>\<exists>" [8]9)  where "\<^bold>\<exists>x. \<phi> x \<equiv> \<^bold>\<exists>\<phi>"



section\<open>Some Basic Notions in Category Theory\<close>

text \<open>Morphisms in the category are modeled as objects of type $i$.
We introduce three partial functions,
$dom$ (domain), $cod$ (codomain), and morphism composition ($\cdot$).

For composition we assume set-theoretical composition here (i.e., functional
composition from right to left). \label{IDMcL}\<close>

 consts
  domain:: "i\<Rightarrow>i" ("dom _" [108] 109)
  codomain:: "i\<Rightarrow>i" ("cod _" [110] 111)
  composition:: "i\<Rightarrow>i\<Rightarrow>i" (infix "\<cdot>" 110)

 \<comment> \<open>Kleene Equality\<close>
 abbreviation KlEq (infixr "\<cong>" 56) where "x \<cong> y \<equiv> (E x \<^bold>\<or> E y) \<^bold>\<rightarrow> x \<^bold>= y"
 \<comment> \<open>Existing Identity\<close>
 abbreviation ExId (infixr "\<simeq>" 56) where "x \<simeq> y \<equiv> (E x \<^bold>\<and> E y \<^bold>\<and> x \<^bold>= y)"

 \<comment> \<open>Identity-morphism: see also p.~4. of \cite{FreydScedrov90}.\<close>
 abbreviation "ID i \<equiv> (\<^bold>\<forall>x. E(i\<cdot>x) \<^bold>\<rightarrow> i\<cdot>x \<cong> x) \<^bold>\<and> (\<^bold>\<forall>x. E(x\<cdot>i) \<^bold>\<rightarrow> x\<cdot>i \<cong> x)"
 \<comment> \<open>Identity-morphism: Mac Lane's definition, the same as ID except for notion of equality.\<close>
 abbreviation "IDMcL \<rho> \<equiv> (\<^bold>\<forall>\<alpha>. E(\<rho>\<cdot>\<alpha>) \<^bold>\<rightarrow> \<rho>\<cdot>\<alpha> = \<alpha>) \<^bold>\<and> (\<^bold>\<forall>\<beta>. E(\<beta>\<cdot>\<rho>) \<^bold>\<rightarrow> \<beta>\<cdot>\<rho> = \<beta>)"

 \<comment> \<open>The two notions of identity-morphisms are obviously equivalent.\<close>
 lemma IDPredicates: "ID \<equiv> IDMcL" by auto


section\<open>The Axioms Sets studied by Benzm\"uller and Scott @{cite "R58"}\<close>

subsection\<open>AxiomsSet1\<close>

 text\<open>AxiomsSet1 generalizes the notion of a monoid by introducing a partial, strict binary
      composition operation ``$\cdot$''. The existence of left and right identity elements is
      addressed in axioms @{term "C\<^sub>i"} and @{term "D\<^sub>i"}. The notions of $dom$ (domain) and
      $cod$ (codomain)
      abstract from their common meaning in the context of sets. In category theory we
     work with just a single type of objects (the type $i$ in our setting) and therefore
     identity morphisms are employed to suitably characterize their
     meanings.\<close>

 locale AxiomsSet1 =
  assumes
   S\<^sub>i: "E(x\<cdot>y) \<^bold>\<rightarrow> (E x \<^bold>\<and> E y)" and
   E\<^sub>i: "E(x\<cdot>y) \<^bold>\<leftarrow> (E x \<^bold>\<and> E y \<^bold>\<and> (\<^bold>\<exists>z. z\<cdot>z \<cong> z \<^bold>\<and> x\<cdot>z \<cong> x \<^bold>\<and> z\<cdot>y \<cong> y))" and
   A\<^sub>i: "x\<cdot>(y\<cdot>z) \<cong> (x\<cdot>y)\<cdot>z" and
   C\<^sub>i: "\<^bold>\<forall>y.\<^bold>\<exists>i. ID i \<^bold>\<and> i\<cdot>y \<cong> y" and
   D\<^sub>i: "\<^bold>\<forall>x.\<^bold>\<exists>j. ID j \<^bold>\<and> x\<cdot>j \<cong> x"
  begin
   lemma True nitpick [satisfy] oops  \<comment> \<open>Consistency\<close>
   lemma assumes "\<exists>x. \<^bold>\<not>(E x)" shows True nitpick [satisfy] oops  \<comment> \<open>Consistency\<close>
   lemma assumes "(\<exists>x. \<^bold>\<not>(E x)) \<and> (\<exists>x. (E x))" shows True nitpick [satisfy] oops  \<comment> \<open>Consistency\<close>

   lemma E\<^sub>iImpl: "E(x\<cdot>y) \<^bold>\<rightarrow> (E x \<^bold>\<and> E y \<^bold>\<and> (\<^bold>\<exists>z. z\<cdot>z \<cong> z \<^bold>\<and> x\<cdot>z \<cong> x \<^bold>\<and> z\<cdot>y \<cong> y))" by (metis A\<^sub>i C\<^sub>i S\<^sub>i)
   \<comment> \<open>Uniqueness of i and j in the latter two axioms.\<close>
   lemma UC\<^sub>i: "\<^bold>\<forall>y.\<^bold>\<exists>i. ID i \<^bold>\<and> i\<cdot>y \<cong> y \<^bold>\<and> (\<^bold>\<forall>j.(ID j \<^bold>\<and> j\<cdot>y \<cong> y) \<^bold>\<rightarrow> i \<cong> j)" by (smt A\<^sub>i C\<^sub>i S\<^sub>i)
   lemma UD\<^sub>i: "\<^bold>\<forall>x.\<^bold>\<exists>j. ID j \<^bold>\<and> x\<cdot>j \<cong> x \<^bold>\<and> (\<^bold>\<forall>i.(ID i \<^bold>\<and> x\<cdot>i \<cong> x) \<^bold>\<rightarrow> j \<cong> i)" by (smt A\<^sub>i D\<^sub>i S\<^sub>i)
   \<comment> \<open>But i and j need not to equal.\<close>
   lemma "(\<exists>C D. (\<^bold>\<forall>y. ID (C y) \<^bold>\<and> (C y)\<cdot>y \<cong> y) \<^bold>\<and> (\<^bold>\<forall>x. ID (D x) \<^bold>\<and> x\<cdot>(D x) \<cong> x) \<^bold>\<and> \<^bold>\<not>(D \<^bold>= C))"
     nitpick [satisfy] oops \<comment> \<open>Model found\<close>
   lemma "(\<exists>x. E x) \<^bold>\<and> (\<exists>C D. (\<^bold>\<forall>y. ID(C y) \<^bold>\<and> (C y)\<cdot>y \<cong> y) \<^bold>\<and> (\<^bold>\<forall>x. ID(D x) \<^bold>\<and> x\<cdot>(D x) \<cong> x) \<^bold>\<and> \<^bold>\<not>(D \<^bold>= C))"
     nitpick [satisfy] oops \<comment> \<open>Model found\<close>
  end



subsection\<open>AxiomsSet2\<close>

text\<open>AxiomsSet2 is developed from AxiomsSet1 by Skolemization of the
     existentially quantified variables $i$ and $j$ in axioms $C_i$ and
     $D_i$. We can argue semantically that every model of AxiomsSet1 has
     such functions. Hence, we get a conservative extension of AxiomsSet1.
     The strictness axiom $S$ is extended, so
     that strictness is now also postulated for the new Skolem functions
     $dom$ and $cod$.\<close>

 locale AxiomsSet2 =
  assumes
   S\<^sub>i\<^sub>i: "(E(x\<cdot>y) \<^bold>\<rightarrow> (E x \<^bold>\<and> E y)) \<^bold>\<and> (E(dom x) \<^bold>\<rightarrow> E x) \<^bold>\<and> (E(cod y) \<^bold>\<rightarrow> E y)"  and
   E\<^sub>i\<^sub>i: "E(x\<cdot>y) \<^bold>\<leftarrow> (E x \<^bold>\<and> E y \<^bold>\<and> (\<^bold>\<exists>z. z\<cdot>z \<cong> z \<^bold>\<and> x\<cdot>z \<cong> x \<^bold>\<and> z\<cdot>y \<cong> y))" and
   A\<^sub>i\<^sub>i: "x\<cdot>(y\<cdot>z) \<cong> (x\<cdot>y)\<cdot>z" and
   C\<^sub>i\<^sub>i: "E y \<^bold>\<rightarrow> (ID(cod y) \<^bold>\<and> (cod y)\<cdot>y \<cong> y)" and
   D\<^sub>i\<^sub>i: "E x \<^bold>\<rightarrow> (ID(dom x) \<^bold>\<and> x\<cdot>(dom x) \<cong> x)"
  begin
   lemma True nitpick [satisfy] oops  \<comment> \<open>Consistency\<close>
   lemma assumes "\<exists>x. \<^bold>\<not>(E x)" shows True nitpick [satisfy] oops  \<comment> \<open>Consistency\<close>
   lemma assumes "(\<exists>x. \<^bold>\<not>(E x)) \<and> (\<exists>x. (E x))" shows True nitpick [satisfy] oops  \<comment> \<open>Consistency\<close>

   lemma E\<^sub>i\<^sub>iImpl: "E(x\<cdot>y) \<^bold>\<rightarrow> (E x \<^bold>\<and> E y \<^bold>\<and> (\<^bold>\<exists>z. z\<cdot>z \<cong> z \<^bold>\<and> x\<cdot>z \<cong> x \<^bold>\<and> z\<cdot>y \<cong> y))" by (metis A\<^sub>i\<^sub>i C\<^sub>i\<^sub>i S\<^sub>i\<^sub>i)
   lemma domTotal: "E x \<^bold>\<rightarrow> E(dom x)" by (metis D\<^sub>i\<^sub>i S\<^sub>i\<^sub>i)
   lemma codTotal: "E x \<^bold>\<rightarrow> E(cod x)" by (metis C\<^sub>i\<^sub>i S\<^sub>i\<^sub>i)
  end

 subsubsection\<open>AxiomsSet2 entails AxiomsSet1\<close>

 context AxiomsSet2
  begin
   lemma S\<^sub>i: "E(x\<cdot>y) \<^bold>\<rightarrow> (E x \<^bold>\<and> E y)" using S\<^sub>i\<^sub>i by blast
   lemma E\<^sub>i: "E(x\<cdot>y) \<^bold>\<leftarrow> (E x \<^bold>\<and> E y \<^bold>\<and> (\<^bold>\<exists>z. z\<cdot>z \<cong> z \<^bold>\<and> x\<cdot>z \<cong> x \<^bold>\<and> z\<cdot>y \<cong> y))" using E\<^sub>i\<^sub>i by blast
   lemma A\<^sub>i: "x\<cdot>(y\<cdot>z) \<cong> (x\<cdot>y)\<cdot>z" using A\<^sub>i\<^sub>i by blast
   lemma C\<^sub>i: "\<^bold>\<forall>y.\<^bold>\<exists>i. ID i \<^bold>\<and> i\<cdot>y \<cong> y" by (metis C\<^sub>i\<^sub>i S\<^sub>i\<^sub>i)
   lemma D\<^sub>i: "\<^bold>\<forall>x.\<^bold>\<exists>j. ID j \<^bold>\<and> x\<cdot>j \<cong> x" by (metis D\<^sub>i\<^sub>i S\<^sub>i\<^sub>i)
  end

 subsubsection\<open>AxiomsSet1 entails AxiomsSet2 (by semantic means)\<close>
 text\<open>By semantic means (Skolemization).\<close>



 subsection\<open>AxiomsSet3\<close>

 text\<open>In AxiomsSet3 the existence  axiom  $E_{ii}$ from AxiomsSet2  is simplified by taking
      advantage of the two new Skolem functions $dom$ and $cod$.

      The left-to-right direction of existence axiom $E_{iii}$ is implied.\<close>

 locale AxiomsSet3 =
  assumes
   S\<^sub>i\<^sub>i\<^sub>i: "(E(x\<cdot>y) \<^bold>\<rightarrow> (E x \<^bold>\<and> E y)) \<^bold>\<and> (E(dom x ) \<^bold>\<rightarrow> E x) \<^bold>\<and> (E(cod y) \<^bold>\<rightarrow> E y)"  and
   E\<^sub>i\<^sub>i\<^sub>i: "E(x\<cdot>y) \<^bold>\<leftarrow> (dom x \<cong> cod y \<^bold>\<and> E(cod y))" and
   A\<^sub>i\<^sub>i\<^sub>i: "x\<cdot>(y\<cdot>z) \<cong> (x\<cdot>y)\<cdot>z" and
   C\<^sub>i\<^sub>i\<^sub>i: "E y \<^bold>\<rightarrow> (ID(cod y) \<^bold>\<and> (cod y)\<cdot>y \<cong> y)" and
   D\<^sub>i\<^sub>i\<^sub>i: "E x \<^bold>\<rightarrow> (ID(dom x) \<^bold>\<and> x\<cdot>(dom x) \<cong> x)"
  begin
   lemma True nitpick [satisfy] oops  \<comment> \<open>Consistency\<close>
   lemma assumes "\<exists>x. \<^bold>\<not>(E x)" shows True nitpick [satisfy] oops  \<comment> \<open>Consistency\<close>
   lemma assumes "(\<exists>x. \<^bold>\<not>(E x)) \<and> (\<exists>x. (E x))" shows True nitpick [satisfy] oops  \<comment> \<open>Consistency\<close>

   lemma E\<^sub>i\<^sub>i\<^sub>iImpl: "E(x\<cdot>y) \<^bold>\<rightarrow> (dom x \<cong> cod y \<^bold>\<and> E(cod y))" by (metis (full_types) A\<^sub>i\<^sub>i\<^sub>i C\<^sub>i\<^sub>i\<^sub>i D\<^sub>i\<^sub>i\<^sub>i S\<^sub>i\<^sub>i\<^sub>i)
  end


 subsubsection\<open>AxiomsSet3 entails AxiomsSet2\<close>

 context AxiomsSet3
  begin
   lemma S\<^sub>i\<^sub>i: "(E(x\<cdot>y) \<^bold>\<rightarrow> (E x \<^bold>\<and> E y)) \<^bold>\<and> (E(dom x ) \<^bold>\<rightarrow> E x) \<^bold>\<and> (E(cod y) \<^bold>\<rightarrow> E y)" using S\<^sub>i\<^sub>i\<^sub>i by blast
   lemma E\<^sub>i\<^sub>i: "E(x\<cdot>y) \<^bold>\<leftarrow> (E x \<^bold>\<and> E y \<^bold>\<and> (\<^bold>\<exists>z. z\<cdot>z \<cong> z \<^bold>\<and> x\<cdot>z \<cong> x \<^bold>\<and> z\<cdot>y \<cong> y))" by (metis A\<^sub>i\<^sub>i\<^sub>i C\<^sub>i\<^sub>i\<^sub>i D\<^sub>i\<^sub>i\<^sub>i E\<^sub>i\<^sub>i\<^sub>i S\<^sub>i\<^sub>i\<^sub>i)
   lemma A\<^sub>i\<^sub>i: "x\<cdot>(y\<cdot>z) \<cong> (x\<cdot>y)\<cdot>z" using A\<^sub>i\<^sub>i\<^sub>i by blast
   lemma C\<^sub>i\<^sub>i: "E y \<^bold>\<rightarrow> (ID(cod y) \<^bold>\<and> (cod y)\<cdot>y \<cong> y)" using C\<^sub>i\<^sub>i\<^sub>i by auto
   lemma D\<^sub>i\<^sub>i: "E x \<^bold>\<rightarrow> (ID(dom x) \<^bold>\<and> x\<cdot>(dom x) \<cong> x)" using D\<^sub>i\<^sub>i\<^sub>i by auto
  end


 subsubsection\<open>AxiomsSet2 entails AxiomsSet3\<close>

 context AxiomsSet2
  begin
   lemma S\<^sub>i\<^sub>i\<^sub>i: "(E(x\<cdot>y) \<^bold>\<rightarrow> (E x \<^bold>\<and> E y)) \<^bold>\<and> (E(dom x) \<^bold>\<rightarrow> E x) \<^bold>\<and> (E(cod y) \<^bold>\<rightarrow> E y)" using S\<^sub>i\<^sub>i by blast
   lemma E\<^sub>i\<^sub>i\<^sub>i: "E(x\<cdot>y) \<^bold>\<leftarrow> (dom x \<cong> cod y \<^bold>\<and> E(cod y))" by (metis C\<^sub>i\<^sub>i D\<^sub>i\<^sub>i E\<^sub>i\<^sub>i S\<^sub>i\<^sub>i)
   lemma A\<^sub>i\<^sub>i\<^sub>i: "x\<cdot>(y\<cdot>z) \<cong> (x\<cdot>y)\<cdot>z" using A\<^sub>i\<^sub>i by blast
   lemma C\<^sub>i\<^sub>i\<^sub>i: "E y \<^bold>\<rightarrow> (ID(cod y) \<^bold>\<and> (cod y)\<cdot>y \<cong> y)" using C\<^sub>i\<^sub>i by auto
   lemma D\<^sub>i\<^sub>i\<^sub>i: "E x \<^bold>\<rightarrow> (ID(dom x) \<^bold>\<and> x\<cdot>(dom x) \<cong> x)" using D\<^sub>i\<^sub>i by auto
  end




  subsection\<open>The Axioms Set AxiomsSet4\<close>

  text\<open>AxiomsSet4 simplifies the axioms $C_{iii}$ and  $D_{iii}$. However, as it turned
       out, these simplifications also require the existence axiom $E_{iii}$ to be strengthened
       into an equivalence.\<close>

 locale AxiomsSet4 =
  assumes
   S\<^sub>i\<^sub>v: "(E(x\<cdot>y) \<^bold>\<rightarrow> (E x \<^bold>\<and> E y)) \<^bold>\<and> (E(dom x) \<^bold>\<rightarrow> E x) \<^bold>\<and> (E(cod y) \<^bold>\<rightarrow> E y)"  and
   E\<^sub>i\<^sub>v: "E(x\<cdot>y) \<^bold>\<leftrightarrow> (dom x \<cong> cod y \<^bold>\<and> E(cod y))" and
   A\<^sub>i\<^sub>v: "x\<cdot>(y\<cdot>z) \<cong> (x\<cdot>y)\<cdot>z" and
   C\<^sub>i\<^sub>v: "(cod y)\<cdot>y \<cong> y" and
   D\<^sub>i\<^sub>v: "x\<cdot>(dom x) \<cong> x"
  begin
   lemma True nitpick [satisfy] oops  \<comment> \<open>Consistency\<close>
   lemma assumes "\<exists>x. \<^bold>\<not>(E x)" shows True nitpick [satisfy] oops  \<comment> \<open>Consistency\<close>
   lemma assumes "(\<exists>x. \<^bold>\<not>(E x)) \<and> (\<exists>x. (E x))" shows True nitpick [satisfy] oops  \<comment> \<open>Consistency\<close>
  end

 subsubsection\<open>AxiomsSet4 entails AxiomsSet3\<close>

 context AxiomsSet4
  begin
   lemma S\<^sub>i\<^sub>i\<^sub>i: "(E(x\<cdot>y) \<^bold>\<rightarrow> (E x \<^bold>\<and> E y)) \<^bold>\<and> (E(dom x) \<^bold>\<rightarrow> E x) \<^bold>\<and> (E(cod y) \<^bold>\<rightarrow> E y)" using S\<^sub>i\<^sub>v by blast
   lemma E\<^sub>i\<^sub>i\<^sub>i: "E(x\<cdot>y) \<^bold>\<leftarrow> (dom x \<cong> cod y \<^bold>\<and> (E(cod y)))" using E\<^sub>i\<^sub>v by blast
   lemma A\<^sub>i\<^sub>i\<^sub>i: "x\<cdot>(y\<cdot>z) \<cong> (x\<cdot>y)\<cdot>z" using A\<^sub>i\<^sub>v by blast
   lemma C\<^sub>i\<^sub>i\<^sub>i: "E y \<^bold>\<rightarrow> (ID(cod y) \<^bold>\<and> (cod y)\<cdot>y \<cong> y)" by (metis C\<^sub>i\<^sub>v D\<^sub>i\<^sub>v E\<^sub>i\<^sub>v)
   lemma D\<^sub>i\<^sub>i\<^sub>i: "E x \<^bold>\<rightarrow> (ID(dom x) \<^bold>\<and> x\<cdot>(dom x) \<cong> x)" by (metis C\<^sub>i\<^sub>v D\<^sub>i\<^sub>v E\<^sub>i\<^sub>v)
  end


 subsubsection\<open>AxiomsSet3 entails AxiomsSet4\<close>

 context AxiomsSet3
  begin
   lemma S\<^sub>i\<^sub>v: "(E(x\<cdot>y) \<^bold>\<rightarrow> (E x \<^bold>\<and> E y)) \<^bold>\<and> (E(dom x ) \<^bold>\<rightarrow> E x) \<^bold>\<and> (E(cod y) \<^bold>\<rightarrow> E y)"  using S\<^sub>i\<^sub>i\<^sub>i by blast
   lemma E\<^sub>i\<^sub>v: "E(x\<cdot>y) \<^bold>\<leftrightarrow> (dom x \<cong> cod y \<^bold>\<and> E(cod y))" by (metis (full_types) A\<^sub>i\<^sub>i\<^sub>i C\<^sub>i\<^sub>i\<^sub>i D\<^sub>i\<^sub>i\<^sub>i E\<^sub>i\<^sub>i\<^sub>i S\<^sub>i\<^sub>i\<^sub>i)
   lemma A\<^sub>i\<^sub>v: "x\<cdot>(y\<cdot>z) \<cong> (x\<cdot>y)\<cdot>z" using A\<^sub>i\<^sub>i\<^sub>i by blast
   lemma C\<^sub>i\<^sub>v: "(cod y)\<cdot>y \<cong> y" using C\<^sub>i\<^sub>i\<^sub>i S\<^sub>i\<^sub>i\<^sub>i by blast
   lemma D\<^sub>i\<^sub>v: "x\<cdot>(dom x) \<cong> x" using D\<^sub>i\<^sub>i\<^sub>i S\<^sub>i\<^sub>i\<^sub>i by blast
  end




subsection\<open>AxiomsSet5\<close>

  text\<open>AxiomsSet5 has been proposed by Scott @{cite "Scott79"} in the 1970s. This set of
 axioms is equivalent to the axioms set presented by Freyd and Scedrov in their textbook
 ``Categories, Allegories'' @{cite "FreydScedrov90"} when encoded in free logic, corrected/adapted
 and further simplified, see Section 5.\<close>

 locale AxiomsSet5 =
  assumes
   S1: "E(dom x) \<^bold>\<rightarrow> E x" and
   S2: "E(cod y) \<^bold>\<rightarrow> E y" and
   S3: "E(x\<cdot>y) \<^bold>\<leftrightarrow> dom x \<simeq> cod y" and
   S4: "x\<cdot>(y\<cdot>z) \<cong> (x\<cdot>y)\<cdot>z" and
   S5: "(cod y)\<cdot>y \<cong> y" and
   S6: "x\<cdot>(dom x) \<cong> x"
  begin
   lemma True nitpick [satisfy] oops  \<comment> \<open>Consistency\<close>
   lemma assumes "\<exists>x. \<^bold>\<not>(E x)" shows True nitpick [satisfy] oops  \<comment> \<open>Consistency\<close>
   lemma assumes "(\<exists>x. \<^bold>\<not>(E x)) \<and> (\<exists>x. (E x))" shows True nitpick [satisfy] oops  \<comment> \<open>Consistency\<close>
  end



 subsubsection\<open>AxiomsSet5 entails AxiomsSet4\<close>

 context AxiomsSet5
  begin
   lemma S\<^sub>i\<^sub>v: "(E(x\<cdot>y) \<^bold>\<rightarrow> (E x \<^bold>\<and> E y)) \<^bold>\<and> (E(dom x ) \<^bold>\<rightarrow> E x) \<^bold>\<and> (E(cod y) \<^bold>\<rightarrow> E y)" using S1 S2 S3 by blast
   lemma E\<^sub>i\<^sub>v: "E(x\<cdot>y) \<^bold>\<leftrightarrow> (dom x \<cong> cod y \<^bold>\<and> E(cod y))" using S3 by metis
   lemma A\<^sub>i\<^sub>v: "x\<cdot>(y\<cdot>z) \<cong> (x\<cdot>y)\<cdot>z" using S4 by blast
   lemma C\<^sub>i\<^sub>v: "(cod y)\<cdot>y \<cong> y" using S5 by blast
   lemma D\<^sub>i\<^sub>v: "x\<cdot>(dom x) \<cong> x" using S6 by blast
  end


 subsubsection\<open>AxiomsSet4 entails AxiomsSet5\<close>

 context AxiomsSet4
  begin
   lemma S1: "E(dom x) \<^bold>\<rightarrow> E x" using S\<^sub>i\<^sub>v by blast
   lemma S2: "E(cod y) \<^bold>\<rightarrow> E y" using S\<^sub>i\<^sub>v by blast
   lemma S3: "E(x\<cdot>y) \<^bold>\<leftrightarrow> dom x \<simeq> cod y" using E\<^sub>i\<^sub>v by metis
   lemma S4: "x\<cdot>(y\<cdot>z) \<cong> (x\<cdot>y)\<cdot>z" using A\<^sub>i\<^sub>v by blast
   lemma S5: "(cod y)\<cdot>y \<cong> y" using C\<^sub>i\<^sub>v by blast
   lemma S6: "x\<cdot>(dom x) \<cong> x" using D\<^sub>i\<^sub>v by blast
  end




section\<open>The Axioms Sets by Freyd and Scedrov @{cite "FreydScedrov90"}\<close>

subsection\<open>AxiomsSet6\<close>
text\<open>The axioms by Freyd and Scedrov  @{cite "FreydScedrov90"} in our notation, when being
     corrected (cf. the modification in axiom A1).

     Freyd and Scedrov employ a different notation for $dom\ x$ and $cod\ 
     x$. They denote these operations by $\Box x$
     and $x\Box$. Moreover, they employ diagrammatic composition instead of the set-theoretic
     definition (functional composition from right to left) used so
     far.
     We leave it to the reader to verify that their axioms corresponds to the axioms presented
     here modulo an appropriate conversion of notation.\<close>

 locale AxiomsSet6 =
  assumes
    A1: "E(x\<cdot>y) \<^bold>\<leftrightarrow> dom x \<simeq> cod y" and
   A2a: "cod(dom x) \<cong> dom x" and
   A2b: "dom(cod y) \<cong> cod y" and
   A3a: "x\<cdot>(dom x) \<cong> x" and
   A3b: "(cod y)\<cdot>y \<cong> y" and
   A4a: "dom(x\<cdot>y) \<cong> dom((dom x)\<cdot>y)" and
   A4b: "cod(x\<cdot>y) \<cong> cod(x\<cdot>(cod y))" and
    A5: "x\<cdot>(y\<cdot>z) \<cong> (x\<cdot>y)\<cdot>z"
  begin
   lemma True nitpick [satisfy] oops  \<comment> \<open>Consistency\<close>
   lemma assumes "\<exists>x. \<^bold>\<not>(E x)" shows True nitpick [satisfy] oops  \<comment> \<open>Consistency\<close>
   lemma assumes "(\<exists>x. \<^bold>\<not>(E x)) \<and> (\<exists>x. (E x))" shows True nitpick [satisfy] oops  \<comment> \<open>Consistency\<close>
end


 subsubsection\<open>AxiomsSet6 entails AxiomsSet5\<close>

 context AxiomsSet6
  begin
   lemma S1: "E(dom x) \<^bold>\<rightarrow> E x" by (metis A1 A2a A3a)
   lemma S2: "E(cod y) \<^bold>\<rightarrow> E y" using A1 A2b A3b by metis
   lemma S3: "E(x\<cdot>y) \<^bold>\<leftrightarrow> dom x \<simeq> cod y" by (metis A1)
   lemma S4: "x\<cdot>(y\<cdot>z) \<cong> (x\<cdot>y)\<cdot>z" using A5 by blast
   lemma S5: "(cod y)\<cdot>y \<cong> y" using A3b by blast
   lemma S6: "x\<cdot>(dom x) \<cong> x" using A3a by blast

   lemma A4aRedundant: "dom(x\<cdot>y) \<cong> dom((dom x)\<cdot>y)" using A1 A2a A3a A5 by metis
   lemma A4bRedundant: "cod(x\<cdot>y) \<cong> cod(x\<cdot>(cod y))" using A1 A2b A3b A5 by smt
   lemma A2aRedundant: "cod(dom x) \<cong> dom x" using A1 A3a A3b A4a A4b by smt
   lemma A2bRedundant: "dom(cod y) \<cong> cod y" using  A1 A3a A3b A4a A4b by smt
  end


 subsubsection\<open>AxiomsSet5 entails AxiomsSet6\<close>

 context AxiomsSet5
  begin
   lemma A1: "E(x\<cdot>y) \<^bold>\<leftrightarrow> dom x \<simeq> cod y" using S3 by blast
   lemma A2: "cod(dom x) \<cong> dom x" by (metis S1 S2 S3 S6)
   lemma A2b: "dom(cod y) \<cong> cod y" using S1 S2 S3 S5 by metis
   lemma A3a: "x\<cdot>(dom x) \<cong> x" using S6 by auto
   lemma A3b: "(cod y)\<cdot>y \<cong> y" using S5 by blast
   lemma A4a: "dom(x\<cdot>y) \<cong> dom((dom x)\<cdot>y)" by (metis S1 S3 S4 S5 S6)
   lemma A4b: "cod(x\<cdot>y) \<cong> cod(x\<cdot>(cod y))" by (metis (full_types) S2 S3 S4 S5 S6)
   lemma  A5: "x\<cdot>(y\<cdot>z) \<cong> (x\<cdot>y)\<cdot>z" using S4 by blast
  end



subsection\<open>AxiomsSet7 (technically flawed)\<close>
  text\<open>The axioms by Freyd and Scedrov in our notation, without the suggested correction of
       axiom A1. This axioms set is technically flawed
       when encoded in our given context. It leads to a constricted inconsistency.\<close>


 locale AxiomsSet7 =
  assumes
    A1: "E(x\<cdot>y) \<^bold>\<leftrightarrow> dom x \<cong> cod y" and
   A2a: "cod(dom x) \<cong> dom x " and
   A2b: "dom(cod y) \<cong> cod y" and
   A3a: "x\<cdot>(dom x) \<cong> x" and
   A3b: "(cod y)\<cdot>y \<cong> y" and
   A4a: "dom(x\<cdot>y) \<cong> dom((dom x)\<cdot>y)" and
   A4b: "cod(x\<cdot>y) \<cong> cod(x\<cdot>(cod y))" and
    A5: "x\<cdot>(y\<cdot>z) \<cong> (x\<cdot>y)\<cdot>z"
  begin
   lemma True nitpick [satisfy] oops  \<comment> \<open>Consistency\<close>
   (*
   lemma assumes "\<exists>x. \<^bold>\<not>(E x)" shows True nitpick [satisfy] oops  --{*No model found*}
   lemma assumes "(\<exists>x. \<^bold>\<not>(E x)) \<and> (\<exists>x. (E x))" shows True nitpick [satisfy] oops  --{*No model found*}
   *)
   lemma InconsistencyAutomatic: "(\<exists>x. \<^bold>\<not>(E x)) \<^bold>\<rightarrow> False" by (metis A1 A2a A3a) \<comment> \<open>Inconsistency\<close>
   lemma "\<forall>x. E x" using InconsistencyAutomatic by auto

   lemma InconsistencyInteractive:
    assumes NEx: "\<exists>x. \<^bold>\<not>(E x)" shows False
    proof -
    obtain a where 1: "\<^bold>\<not>(E a)" using NEx by auto
    have 2: "a\<cdot>(dom a) \<cong> a" using A3a by blast
    have 3: "\<^bold>\<not>(E(a\<cdot>(dom a)))" using 1 2 by metis
    have 4: "E(a\<cdot>(dom a)) \<^bold>\<leftrightarrow> dom a \<cong> cod(dom a)" using A1 by blast
    have 5: "cod(dom a) \<cong> dom a" using A2a by blast
    have 6: "E(a\<cdot>(dom a)) \<^bold>\<leftrightarrow> dom a \<cong> dom a" using 4 5 by auto
    have 7: "E(a\<cdot>(dom a))" using 6 by blast
    then show ?thesis using 7 3 by blast
    qed
  end



subsection\<open>AxiomsSet7orig (technically flawed)\<close>

text\<open>The axioms by Freyd and Scedrov in their original notation, without the suggested
     correction of axiom A1.

      We present the constricted inconsistency argument from above once again,
      but this time in the original notation of Freyd and Scedrov.\<close>

 locale AxiomsSet7orig =
  fixes
   source:: "i\<Rightarrow>i" ("\<box>_" [108] 109) and
   target:: "i\<Rightarrow>i" ("_\<box>" [110] 111) and
   compositionF:: "i\<Rightarrow>i\<Rightarrow>i" (infix "\<^bold>\<cdot>" 110)
  assumes
    A1: "E(x\<^bold>\<cdot>y) \<^bold>\<leftrightarrow> (x\<box> \<cong> \<box>y)" and
   A2a: "((\<box>x)\<box>) \<cong> \<box>x" and
   A2b: "\<box>(x\<box>) \<cong> \<box>x" and
   A3a: "(\<box>x)\<^bold>\<cdot>x \<cong> x" and
   A3b: "x\<^bold>\<cdot>(x\<box>) \<cong> x" and
   A4a: "\<box>(x\<^bold>\<cdot>y) \<cong> \<box>(x\<^bold>\<cdot>(\<box>y))" and
   A4b: "(x\<^bold>\<cdot>y)\<box> \<cong> ((x\<box>)\<^bold>\<cdot>y)\<box>" and
    A5: "x\<^bold>\<cdot>(y\<^bold>\<cdot>z) \<cong> (x\<^bold>\<cdot>y)\<^bold>\<cdot>z"
  begin
   lemma True nitpick [satisfy] oops \<comment> \<open>Consistency\<close>
   (*
   lemma assumes "\<exists>x. \<^bold>\<not>(E x)" shows True nitpick [satisfy] oops  --{*No model found*}
   lemma assumes "(\<exists>x. \<^bold>\<not>(E x)) \<and> (\<exists>x. (E x))" shows True nitpick [satisfy] oops  --{*No model found*}
    *)
   lemma InconsistencyAutomatic: "(\<exists>x. \<^bold>\<not>(E x)) \<^bold>\<rightarrow> False" by (metis A1 A2a A3a) \<comment> \<open>Inconsistency\<close>
   lemma "\<forall>x. E x" using InconsistencyAutomatic by auto

   lemma InconsistencyInteractive:
    assumes NEx: "\<exists>x. \<^bold>\<not>(E x)" shows False
    proof -
    obtain a where 1: "\<^bold>\<not>(E a)" using assms by auto
    have 2: "(\<box>a)\<^bold>\<cdot>a \<cong> a" using A3a by blast
    have 3: "\<^bold>\<not>(E((\<box>a)\<^bold>\<cdot>a))" using 1 2 by metis
    have 4: "E((\<box>a)\<^bold>\<cdot>a) \<^bold>\<leftrightarrow> (\<box>a)\<box> \<cong> \<box>a" using A1 by blast
    have 5: "(\<box>a)\<box> \<cong> \<box>a" using A2a by blast
    have 6: "E((\<box>a)\<^bold>\<cdot>a)" using 4 5 by blast
    then show ?thesis using 6 3 by blast
    qed
  end


subsection\<open>AxiomsSet8 (algebraic reading, still technically flawed)\<close>

 text\<open>The axioms by Freyd and Scedrov in our notation again, but this time we adopt
      an algebraic reading of the free variables, meaning that they range over existing
      morphisms only.\<close>

 locale AxiomsSet8 =
  assumes
    B1: "\<^bold>\<forall>x.\<^bold>\<forall>y. E(x\<cdot>y) \<^bold>\<leftrightarrow> dom x \<cong> cod y" and
   B2a: "\<^bold>\<forall>x. cod(dom x) \<cong> dom x " and
   B2b: "\<^bold>\<forall>y. dom(cod y) \<cong> cod y" and
   B3a: "\<^bold>\<forall>x. x\<cdot>(dom x) \<cong> x" and
   B3b: "\<^bold>\<forall>y. (cod y)\<cdot>y \<cong> y" and
   B4a: "\<^bold>\<forall>x.\<^bold>\<forall>y. dom(x\<cdot>y) \<cong> dom((dom x)\<cdot>y)" and
   B4b: "\<^bold>\<forall>x.\<^bold>\<forall>y. cod(x\<cdot>y) \<cong> cod(x\<cdot>(cod y))" and
    B5: "\<^bold>\<forall>x.\<^bold>\<forall>y.\<^bold>\<forall>z. x\<cdot>(y\<cdot>z) \<cong> (x\<cdot>y)\<cdot>z"
  begin
   lemma True nitpick [satisfy] oops  \<comment> \<open>Consistency\<close>
   lemma assumes "\<exists>x. \<^bold>\<not>(E x)" shows True nitpick [satisfy] oops  \<comment> \<open>Consistency\<close>
   lemma assumes "(\<exists>x. \<^bold>\<not>(E x)) \<and> (\<exists>x. (E x))" shows True nitpick [satisfy] oops  \<comment> \<open>Consistency\<close>
  end


 text\<open>None of the axioms in AxiomsSet5 are implied.\<close>

 context AxiomsSet8
  begin
   lemma S1: "E(dom x) \<^bold>\<rightarrow> E x" nitpick oops \<comment> \<open>Nitpick finds a countermodel\<close>
   lemma S2: "E(cod y) \<^bold>\<rightarrow> E y" nitpick oops \<comment> \<open>Nitpick finds a countermodel\<close>
   lemma S3: "E(x\<cdot>y) \<^bold>\<leftrightarrow> dom x \<simeq> cod y" nitpick oops \<comment> \<open>Nitpick finds a countermodel\<close>
   lemma S4: "x\<cdot>(y\<cdot>z) \<cong> (x\<cdot>y)\<cdot>z" nitpick oops \<comment> \<open>Nitpick finds a countermodel\<close>
   lemma S5: "(cod y)\<cdot>y \<cong> y"  nitpick oops \<comment> \<open>Nitpick finds a countermodel\<close>
   lemma S6: "x\<cdot>(dom x) \<cong> x"  nitpick oops \<comment> \<open>Nitpick finds a countermodel\<close>
  end


subsection\<open>AxiomsSet8Strict (algebraic reading)\<close>

 text\<open>The situation changes when strictness conditions are postulated. Note that in the algebraic
      framework of Freyd and Scedrov such conditions have to be assumed as given in the
      logic, while here we can explicitly encode them as axioms.\<close>

 locale AxiomsSet8Strict = AxiomsSet8 +
  assumes
   B0a: "E(x\<cdot>y) \<^bold>\<rightarrow> (E x \<^bold>\<and> E y)" and
   B0b: "E(dom x) \<^bold>\<rightarrow> E x" and
   B0c: "E(cod x) \<^bold>\<rightarrow> E x"
  begin
   lemma True nitpick [satisfy] oops  \<comment> \<open>Consistency\<close>
   lemma assumes "\<exists>x. \<^bold>\<not>(E x)" shows True nitpick [satisfy] oops  \<comment> \<open>Consistency\<close>
   lemma assumes "(\<exists>x. \<^bold>\<not>(E x)) \<and> (\<exists>x. (E x))" shows True nitpick [satisfy] oops  \<comment> \<open>Consistency\<close>
  end


 subsubsection\<open>AxiomsSet8Strict entails AxiomsSet5\<close>

 context AxiomsSet8Strict
  begin
   lemma S1: "E(dom x) \<^bold>\<rightarrow> E x"  using B0b by blast
   lemma S2: "E(cod y) \<^bold>\<rightarrow> E y"  using B0c by blast
   lemma S3: "E(x\<cdot>y) \<^bold>\<leftrightarrow> dom x \<simeq> cod y" by (metis B0a B0b B0c B1 B3a)
   lemma S4: "x\<cdot>(y\<cdot>z) \<cong> (x\<cdot>y)\<cdot>z" by (meson B0a B5)
   lemma S5: "(cod y)\<cdot>y \<cong> y" using B0a B3b by blast
   lemma S6: "x\<cdot>(dom x) \<cong> x" using B0a B3a by blast
  end


 subsubsection\<open>AxiomsSet5 entails AxiomsSet8Strict\<close>

 context AxiomsSet5
  begin
   lemma B0a: "E(x\<cdot>y) \<^bold>\<rightarrow> (E x \<^bold>\<and> E y)" using S1 S2 S3 by blast
   lemma B0b: "E(dom x) \<^bold>\<rightarrow> E x" using S1 by blast
   lemma B0c: "E(cod x) \<^bold>\<rightarrow> E x" using S2 by blast
   lemma  B1: "\<^bold>\<forall>x.\<^bold>\<forall>y. E(x\<cdot>y) \<^bold>\<leftrightarrow> dom x \<cong> cod y" by (metis S3 S5)
   lemma B2a: "\<^bold>\<forall>x. cod(dom x) \<cong> dom x" using A2 by blast
   lemma B2b: "\<^bold>\<forall>y. dom(cod y) \<cong> cod y" using A2b by blast
   lemma B3a: "\<^bold>\<forall>x. x\<cdot>(dom x) \<cong> x" using S6 by blast
   lemma B3b: "\<^bold>\<forall>y. (cod y)\<cdot>y \<cong> y" using S5 by blast
   lemma B4a: "\<^bold>\<forall>x.\<^bold>\<forall>y. dom(x\<cdot>y) \<cong> dom((dom x)\<cdot>y)" by (metis S1 S3 S4 S6)
   lemma B4b: "\<^bold>\<forall>x.\<^bold>\<forall>y. cod(x\<cdot>y) \<cong> cod(x\<cdot>(cod y))" by (metis S1 S2 S3 S4 S5)
   lemma  B5: "\<^bold>\<forall>x.\<^bold>\<forall>y.\<^bold>\<forall>z. x\<cdot>(y\<cdot>z) \<cong> (x\<cdot>y)\<cdot>z" using S4 by blast
  end


  subsubsection\<open>AxiomsSet8Strict is Redundant\<close>

  text\<open>AxiomsSet8Strict is redundant: either the B2-axioms can be omitted or the B4-axioms.\<close>

 context AxiomsSet8Strict
  begin
   lemma B2aRedundant: "\<^bold>\<forall>x. cod(dom x) \<cong> dom x " by (metis B0a B1 B3a)
   lemma B2bRedundant: "\<^bold>\<forall>y. dom(cod y) \<cong> cod y" by (metis B0a B1 B3b)
   lemma B4aRedundant: "\<^bold>\<forall>x.\<^bold>\<forall>y. dom(x\<cdot>y) \<cong> dom((dom x)\<cdot>y)" by (metis B0a B0b B1 B3a B5)
   lemma B4bRedundant: "\<^bold>\<forall>x.\<^bold>\<forall>y. cod(x\<cdot>y) \<cong> cod(x\<cdot>(cod y))" by (metis B0a B0c B1 B3b B5)
  end





  section\<open>The Axioms Sets of Mac Lane @{cite "MacLane48"}\<close>

  text\<open>We analyse the axioms set suggested by Mac Lane~@{cite "MacLane48"} already in 1948.
      As for the theory by
       Freyd and Scedrov above, which was developed much later, we need to assume
       strictness of composition to show equivalence to our previous axiom sets.
       Note that his complicated conditions on existence of compositions proved to be
       unnecessary, as we show. It shows it is hard to think about partial operations.\<close>


 locale AxiomsSetMcL =
  assumes
   C\<^sub>0 : "E(x\<cdot>y) \<^bold>\<rightarrow> (E x \<^bold>\<and> E y)" and
   C\<^sub>1 : "\<^bold>\<forall>\<gamma> \<beta> \<alpha>. (E(\<gamma>\<cdot>\<beta>) \<^bold>\<and> E((\<gamma>\<cdot>\<beta>)\<cdot>\<alpha>)) \<^bold>\<rightarrow> E(\<beta>\<cdot>\<alpha>)" and
   C\<^sub>1': "\<^bold>\<forall>\<gamma> \<beta> \<alpha>. (E(\<beta>\<cdot>\<alpha>) \<^bold>\<and> E(\<gamma>\<cdot>(\<beta>\<cdot>\<alpha>))) \<^bold>\<rightarrow> E(\<gamma>\<cdot>\<beta>)" and
   C\<^sub>2 : "\<^bold>\<forall>\<gamma> \<beta> \<alpha>. (E(\<gamma>\<cdot>\<beta>) \<^bold>\<and> E(\<beta>\<cdot>\<alpha>)) \<^bold>\<rightarrow> (E((\<gamma>\<cdot>\<beta>)\<cdot>\<alpha>) \<^bold>\<and> E(\<gamma>\<cdot>(\<beta>\<cdot>\<alpha>)) \<^bold>\<and> ((\<gamma>\<cdot>\<beta>)\<cdot>\<alpha>) = (\<gamma>\<cdot>(\<beta>\<cdot>\<alpha>)))" and
   C\<^sub>3 : "\<^bold>\<forall>\<gamma>. \<^bold>\<exists>eD. IDMcL(eD) \<^bold>\<and> E(\<gamma>\<cdot>eD)" and
   C\<^sub>4 : "\<^bold>\<forall>\<gamma>. \<^bold>\<exists>eR. IDMcL(eR) \<^bold>\<and> E(eR\<cdot>\<gamma>)"
  begin
   lemma True nitpick [satisfy] oops  \<comment> \<open>Consistency\<close>
   lemma assumes "\<exists>x. \<^bold>\<not>(E x)" shows True nitpick [satisfy] oops  \<comment> \<open>Consistency\<close>
   lemma assumes "(\<exists>x. \<^bold>\<not>(E x)) \<and> (\<exists>x. (E x))" shows True nitpick [satisfy] oops  \<comment> \<open>Consistency\<close>
  end

  text\<open>Remember that IDMcL  was defined on p.~\pageref{IDMcL} and proved
       equivalent to ID.\<close>


 subsection\<open>AxiomsSetMcL entails AxiomsSet1\<close>

 context AxiomsSetMcL
  begin
   lemma S\<^sub>i: "E(x\<cdot>y) \<^bold>\<rightarrow> (E x \<^bold>\<and> E y)"  using C\<^sub>0 by blast
   lemma E\<^sub>i: "E(x\<cdot>y) \<^bold>\<leftarrow> (E x \<^bold>\<and> E y \<^bold>\<and> (\<^bold>\<exists>z. z\<cdot>z \<cong> z \<^bold>\<and> x\<cdot>z \<cong> x \<^bold>\<and> z\<cdot>y \<cong> y))" by (metis C\<^sub>2)
   lemma A\<^sub>i: "x\<cdot>(y\<cdot>z) \<cong> (x\<cdot>y)\<cdot>z"       by (metis C\<^sub>1 C\<^sub>1' C\<^sub>2 C\<^sub>0)
   lemma C\<^sub>i: "\<^bold>\<forall>y.\<^bold>\<exists>i. ID i \<^bold>\<and> i\<cdot>y \<cong> y" using C\<^sub>4 by fastforce
   lemma D\<^sub>i: "\<^bold>\<forall>x.\<^bold>\<exists>j. ID j \<^bold>\<and> x\<cdot>j \<cong> x" using C\<^sub>3 by fastforce
  end


 subsection\<open>AxiomsSet1 entails AxiomsSetMcL\<close>

 context AxiomsSet1
  begin
   lemma C\<^sub>0 : "E(x\<cdot>y) \<^bold>\<rightarrow> (E x \<^bold>\<and> E y)" using S\<^sub>i by blast
   lemma C\<^sub>1 : "\<^bold>\<forall>\<gamma> \<beta> \<alpha>. (E(\<gamma>\<cdot>\<beta>) \<^bold>\<and> E((\<gamma>\<cdot>\<beta>)\<cdot>\<alpha>)) \<^bold>\<rightarrow> E(\<beta>\<cdot>\<alpha>)" by (metis A\<^sub>i S\<^sub>i)
   lemma C\<^sub>1': "\<^bold>\<forall>\<gamma> \<beta> \<alpha>. (E(\<beta>\<cdot>\<alpha>) \<^bold>\<and> E(\<gamma>\<cdot>(\<beta>\<cdot>\<alpha>))) \<^bold>\<rightarrow> E(\<gamma>\<cdot>\<beta>)" by (metis A\<^sub>i S\<^sub>i)
   lemma C\<^sub>2 : "\<^bold>\<forall>\<gamma> \<beta> \<alpha>. (E(\<gamma>\<cdot>\<beta>) \<^bold>\<and> E(\<beta>\<cdot>\<alpha>)) \<^bold>\<rightarrow> (E((\<gamma>\<cdot>\<beta>)\<cdot>\<alpha>) \<^bold>\<and> E(\<gamma>\<cdot>(\<beta>\<cdot>\<alpha>)) \<^bold>\<and> ((\<gamma>\<cdot>\<beta>)\<cdot>\<alpha>) = (\<gamma>\<cdot>(\<beta>\<cdot>\<alpha>)))" by (smt A\<^sub>i C\<^sub>i E\<^sub>i S\<^sub>i)
   lemma C\<^sub>3 : "\<^bold>\<forall>\<gamma>. \<^bold>\<exists>eD. IDMcL(eD) \<^bold>\<and> E(\<gamma>\<cdot>eD)" using D\<^sub>i by force
   lemma C\<^sub>4 : "\<^bold>\<forall>\<gamma>. \<^bold>\<exists>eR. IDMcL(eR) \<^bold>\<and> E(eR\<cdot>\<gamma>)" using C\<^sub>i by force
  end



 subsection\<open>Skolemization of the Axioms of Mac Lane\<close>

 text\<open>Mac Lane employs diagrammatic composition instead of the set-theoretic
     definition as used in our axiom sets. As we have seen above,
      this is not a problem as long as composition is the only primitive.
      But when adding the Skolem terms $dom$ and $cod$ care must be taken and we should
      actually transform all axioms into a common form. Below we address this (in a minimal way) by
      using $dom$ in axiom @{term "C\<^sub>3s"} and $cod$ in axiom @{term "C\<^sub>4s"}, which is opposite of
      what Mac Lane proposed. For this axioms set we then show  equivalence to AxiomsSet1/2/5.\<close>

 locale SkolemizedAxiomsSetMcL =
  assumes
   C\<^sub>0s : "(E(x\<cdot>y) \<^bold>\<rightarrow> (E x \<^bold>\<and> E y)) \<and> (E(dom x) \<^bold>\<rightarrow> E x) \<and> (E(cod y) \<^bold>\<rightarrow> E y)" and
   C\<^sub>1s : "\<^bold>\<forall>\<gamma> \<beta> \<alpha>. (E(\<gamma>\<cdot>\<beta>) \<^bold>\<and> E((\<gamma>\<cdot>\<beta>)\<cdot>\<alpha>)) \<^bold>\<rightarrow> E(\<beta>\<cdot>\<alpha>)" and
   C\<^sub>1's: "\<^bold>\<forall>\<gamma> \<beta> \<alpha>. (E(\<beta>\<cdot>\<alpha>) \<^bold>\<and> E(\<gamma>\<cdot>(\<beta>\<cdot>\<alpha>))) \<^bold>\<rightarrow> E(\<gamma>\<cdot>\<beta>)" and
   C\<^sub>2s : "\<^bold>\<forall>\<gamma> \<beta> \<alpha>. (E(\<gamma>\<cdot>\<beta>) \<^bold>\<and> E(\<beta>\<cdot>\<alpha>)) \<^bold>\<rightarrow> (E((\<gamma>\<cdot>\<beta>)\<cdot>\<alpha>) \<^bold>\<and> E(\<gamma>\<cdot>(\<beta>\<cdot>\<alpha>)) \<^bold>\<and> ((\<gamma>\<cdot>\<beta>)\<cdot>\<alpha>) = (\<gamma>\<cdot>(\<beta>\<cdot>\<alpha>)))" and
   C\<^sub>3s : "\<^bold>\<forall>\<gamma>. IDMcL(dom \<gamma>) \<^bold>\<and> E(\<gamma>\<cdot>(dom \<gamma>))" and
   C\<^sub>4s : "\<^bold>\<forall>\<gamma>. IDMcL(cod \<gamma>) \<^bold>\<and> E((cod \<gamma>)\<cdot>\<gamma>)"
  begin
   lemma True nitpick [satisfy] oops  \<comment> \<open>Consistency\<close>
   lemma assumes "\<exists>x. \<^bold>\<not>(E x)" shows True nitpick [satisfy] oops  \<comment> \<open>Consistency\<close>
   lemma assumes "(\<exists>x. \<^bold>\<not>(E x)) \<and> (\<exists>x. (E x))" shows True nitpick [satisfy] oops  \<comment> \<open>Consistency\<close>
  end


 subsection\<open>SkolemizedAxiomsSetMcL entails AxiomsSetMcL and AxiomsSet1-5\<close>

 context SkolemizedAxiomsSetMcL
  begin
   lemma C\<^sub>0 : "E(x\<cdot>y) \<^bold>\<rightarrow> (E x \<^bold>\<and> E y)" using C\<^sub>0s by blast
   lemma C\<^sub>1 : "\<^bold>\<forall>\<gamma> \<beta> \<alpha>. (E(\<gamma>\<cdot>\<beta>) \<^bold>\<and> E((\<gamma>\<cdot>\<beta>)\<cdot>\<alpha>)) \<^bold>\<rightarrow> E(\<beta>\<cdot>\<alpha>)" using C\<^sub>1s by blast
   lemma C\<^sub>1': "\<^bold>\<forall>\<gamma> \<beta> \<alpha>. (E(\<beta>\<cdot>\<alpha>) \<^bold>\<and> E(\<gamma>\<cdot>(\<beta>\<cdot>\<alpha>))) \<^bold>\<rightarrow> E(\<gamma>\<cdot>\<beta>)" using C\<^sub>1's by blast
   lemma C\<^sub>2 : "\<^bold>\<forall>\<gamma> \<beta> \<alpha>. (E(\<gamma>\<cdot>\<beta>) \<^bold>\<and> E(\<beta>\<cdot>\<alpha>)) \<^bold>\<rightarrow> (E((\<gamma>\<cdot>\<beta>)\<cdot>\<alpha>) \<^bold>\<and> E(\<gamma>\<cdot>(\<beta>\<cdot>\<alpha>)) \<^bold>\<and> ((\<gamma>\<cdot>\<beta>)\<cdot>\<alpha>) = (\<gamma>\<cdot>(\<beta>\<cdot>\<alpha>)))" using C\<^sub>2s by blast
   lemma C\<^sub>3 : "\<^bold>\<forall>\<gamma>. \<^bold>\<exists>eD. IDMcL(eD) \<^bold>\<and> E(\<gamma>\<cdot>eD)" by (metis C\<^sub>0s C\<^sub>3s)
   lemma C\<^sub>4 : "\<^bold>\<forall>\<gamma>. \<^bold>\<exists>eR. IDMcL(eR) \<^bold>\<and> E(eR\<cdot>\<gamma>)" by (metis C\<^sub>0s C\<^sub>4s)

   lemma S\<^sub>i: "E(x\<cdot>y) \<^bold>\<rightarrow> (E x \<^bold>\<and> E y)"   using C\<^sub>0s by blast
   lemma E\<^sub>i: "E(x\<cdot>y) \<^bold>\<leftarrow> (E x \<^bold>\<and> E y \<^bold>\<and> (\<^bold>\<exists>z. z\<cdot>z \<cong> z \<^bold>\<and> x\<cdot>z \<cong> x \<^bold>\<and> z\<cdot>y \<cong> y))"  by (metis C\<^sub>2s)
   lemma A\<^sub>i: "x\<cdot>(y\<cdot>z) \<cong> (x\<cdot>y)\<cdot>z"        by (metis C\<^sub>1s C\<^sub>1's C\<^sub>2s C\<^sub>0s)
   lemma C\<^sub>i: "\<^bold>\<forall>y.\<^bold>\<exists>i. ID i \<^bold>\<and> i\<cdot>y \<cong> y"  by (metis C\<^sub>0s C\<^sub>4s)
   lemma D\<^sub>i: "\<^bold>\<forall>x.\<^bold>\<exists>j. ID j \<^bold>\<and> x\<cdot>j \<cong> x"  by (metis C\<^sub>0s C\<^sub>3s)

   lemma S\<^sub>i\<^sub>i: "(E(x\<cdot>y) \<^bold>\<rightarrow> (E x \<^bold>\<and> E y)) \<^bold>\<and> (E(dom x ) \<^bold>\<rightarrow> E x) \<^bold>\<and> (E(cod y) \<^bold>\<rightarrow> E y)" using C\<^sub>0s by blast
   lemma E\<^sub>i\<^sub>i: "E(x\<cdot>y) \<^bold>\<leftarrow> (E x \<^bold>\<and> E y \<^bold>\<and> (\<^bold>\<exists>z. z\<cdot>z \<cong> z \<^bold>\<and> x\<cdot>z \<cong> x \<^bold>\<and> z\<cdot>y \<cong> y))" by (metis C\<^sub>2s)
   lemma A\<^sub>i\<^sub>i: "x\<cdot>(y\<cdot>z) \<cong> (x\<cdot>y)\<cdot>z" by (metis C\<^sub>1s C\<^sub>1's C\<^sub>2s C\<^sub>0s)
   lemma C\<^sub>i\<^sub>i: "E y \<^bold>\<rightarrow> (ID(cod y) \<^bold>\<and> (cod y)\<cdot>y \<cong> y)" using C\<^sub>4s by auto
   lemma D\<^sub>i\<^sub>i: "E x \<^bold>\<rightarrow> (ID(dom x) \<^bold>\<and> x\<cdot>(dom x) \<cong> x)" using C\<^sub>3s by auto

   \<comment> \<open>AxiomsSets3/4 are omitted here; we already know they are equivalent.\<close>

   lemma S1: "E(dom x) \<^bold>\<rightarrow> E x"         using C\<^sub>0s by blast
   lemma S2: "E(cod y) \<^bold>\<rightarrow> E y"         using C\<^sub>0s by blast
   lemma S3: "E(x\<cdot>y) \<^bold>\<leftrightarrow> dom x \<simeq> cod y" by (metis (full_types) C\<^sub>0s C\<^sub>1s C\<^sub>1's C\<^sub>2s C\<^sub>3s C\<^sub>4s)
   lemma S4: "x\<cdot>(y\<cdot>z) \<cong> (x\<cdot>y)\<cdot>z"        by (metis C\<^sub>0s C\<^sub>1s C\<^sub>1's C\<^sub>2s)
   lemma S5: "(cod y)\<cdot>y \<cong> y"           using C\<^sub>0s C\<^sub>4s by blast
   lemma S6: "x\<cdot>(dom x) \<cong> x"           using C\<^sub>0s C\<^sub>3s by blast
  end



(*<*)
end
(*>*)


