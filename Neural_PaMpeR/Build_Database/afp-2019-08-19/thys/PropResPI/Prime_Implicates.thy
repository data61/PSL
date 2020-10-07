
(* N. Peltier. LIG/CNRS http://membres-lig.imag.fr/peltier/ *)


section \<open>Prime Implicates  Generation\<close>

text \<open>We show that the unrestricted resolution rule is deductive complete, i.e. that it is able
to generate all (prime) implicates of any given clause set.\<close>

theory Prime_Implicates

imports Propositional_Resolution

begin

context propositional_atoms

begin

subsection \<open>Implicates and Prime Implicates\<close>

text \<open>We first introduce the definitions of implicates and prime implicates.\<close>

definition implicates :: "'at Formula \<Rightarrow> 'at Formula"
  where "implicates S = { C. entails S C }"

definition prime_implicates :: "'at Formula \<Rightarrow> 'at Formula"
  where "prime_implicates S = simplify (implicates S)"

subsection \<open>Generation of Prime Implicates\<close>


text \<open>We introduce a function simplifying a given clause set by evaluating some literals
   to false. We show that this partial evaluation operation preserves saturatedness and 
that if the considered set of literals is an implicate of the initial clause set 
then the partial evaluation yields a clause set that is unsatisfiable.
Then the proof follows from refutational completeness: since the partially evaluated set 
is unsatisfiable and saturated it must contain the empty clause, and therefore the initial 
clause set necessarily contains a clause subsuming the implicate.\<close>

fun partial_evaluation :: "'a Formula \<Rightarrow> 'a Literal set \<Rightarrow> 'a Formula"
where
  "(partial_evaluation S C) = { E. \<exists>D. D \<in> S \<and> E = D-C \<and> \<not>(\<exists>L. (L \<in> C) \<and> (complement L) \<in> D)}"

lemma partial_evaluation_is_saturated : 
  assumes "saturated_binary_rule resolvent S"
  shows "saturated_binary_rule ordered_resolvent (partial_evaluation S C)"
proof (rule ccontr)
    let ?peval = "partial_evaluation S C"
    assume "\<not>saturated_binary_rule ordered_resolvent ?peval"
    from this obtain P1 and P2 and R where "P1 \<in> ?peval" and "P2 \<in> ?peval"
      and "ordered_resolvent P1 P2 R"  and "\<not>(tautology R)" 
      and not_subsumed: "\<not>(\<exists>D. ((D \<in> (partial_evaluation S C)) \<and> (subsumes D R)))" 
    unfolding saturated_binary_rule_def and redundant_def  by auto
    from \<open>P1 \<in> ?peval\<close> obtain PP1 where "PP1 \<in> S" and "P1 = PP1 - C" 
      and i: "\<not>(\<exists>L. (L \<in> C) \<and> (complement L) \<in> PP1)" by auto
    from \<open>P2 \<in> ?peval\<close> obtain PP2 where "PP2 \<in> S" and "P2 = PP2 - C" 
      and  ii: "\<not>(\<exists>L. (L \<in> C) \<and> (complement L) \<in> PP2)" by auto
    from \<open>(ordered_resolvent P1 P2 R)\<close> obtain A where 
      r_def: "R = (P1 - { Pos A }) \<union> (P2 - { Neg A })" and "(Pos A) \<in> P1" and "(Neg A) \<in> P2"
    unfolding ordered_resolvent_def strictly_maximal_literal_def by auto
    let ?RR = "(PP1 - { Pos A }) \<union> (PP2 - { Neg A })"
    from \<open>P1 = PP1 - C\<close> and \<open>(Pos A) \<in> P1\<close> have "(Pos A) \<in> PP1" by auto
    from \<open>P2 = PP2 - C\<close> and \<open>(Neg A) \<in> P2\<close> have "(Neg A) \<in> PP2" by auto
    from r_def and \<open>P1 = PP1 - C\<close> and \<open>P2 = PP2 - C\<close> have "R =  ?RR - C" by auto
    from \<open>(Pos A) \<in> PP1\<close> and \<open>(Neg A) \<in> PP2\<close> 
      have "resolvent PP1 PP2 ?RR" unfolding resolvent_def by auto
    with \<open>PP1 \<in> S\<close> and \<open>PP2 \<in> S\<close> and \<open>saturated_binary_rule resolvent S\<close> 
      have "tautology ?RR \<or> (\<exists>D. (D \<in> S \<and> (subsumes D ?RR)))"
    unfolding saturated_binary_rule_def redundant_def by auto
    thus "False"
    proof 
      assume "tautology ?RR"
      with \<open>R = ?RR - C\<close> and \<open>\<not>tautology R\<close>
        obtain X where "X \<in> C" and "complement X \<in> PP1 \<union> PP2"
        unfolding tautology_def by auto
      from \<open>X \<in> C\<close> and \<open>complement X \<in> PP1 \<union> PP2\<close> and i and ii 
        show "False" by auto
    next
      assume "\<exists>D. ((D \<in> S) \<and> (subsumes D ?RR))"
      from this obtain D where "D \<in> S" and "subsumes D ?RR"
      by auto
      from \<open>subsumes D ?RR\<close> and \<open>R = ?RR - C\<close> 
        have "subsumes (D - C) R" unfolding subsumes_def by auto
      from \<open>D \<in> S\<close> and ii and i and \<open>(subsumes D ?RR)\<close> have "D - C \<in> ?peval" 
        unfolding subsumes_def by auto
      with \<open>subsumes (D - C) R\<close> and not_subsumed show "False" by auto
    qed
qed

lemma evaluation_wrt_implicate_is_unsat : 
  assumes "entails S C"
  assumes "\<not>tautology C"
  shows "\<not>satisfiable (partial_evaluation S C)"
proof
    let ?peval = "partial_evaluation S C"
    assume "satisfiable ?peval"
    then obtain I where "validate_formula I ?peval" unfolding satisfiable_def by auto
    let ?J = "(I - { X. (Pos X) \<in> C }) \<union> { Y. (Neg Y) \<in> C }" 
    have "\<not>validate_clause ?J C"  
    proof 
      assume "validate_clause ?J C"
      then obtain L where "L \<in> C" and "validate_literal ?J L" by auto
      obtain X where "L = (Pos X) \<or> L = (Neg X)" using Literal.exhaust [of L] by auto
      from \<open>L = (Pos X) \<or> L = (Neg X)\<close> and \<open>L \<in> C\<close> and \<open>\<not>tautology C\<close> and \<open>validate_literal ?J L\<close> 
      show "False" unfolding tautology_def by auto
    qed
    have "validate_formula ?J S" 
    proof (rule ccontr)
      assume "\<not> (validate_formula ?J S)"
      then obtain D where "D \<in> S" and "\<not>(validate_clause ?J D)" by auto
      from \<open>D \<in> S\<close> have "D-C \<in> ?peval \<or>  (\<exists>L. (L \<in> C) \<and> (complement L) \<in> D)" 
      by auto
      thus "False" 
      proof
        assume "\<exists>L. (L \<in> C) \<and> (complement L) \<in> D"
        then obtain L where "L \<in> C" and "complement L \<in> D" by auto
        obtain X where "L = (Pos X) \<or> L = (Neg X)" using Literal.exhaust [of L] by auto
        from this  and \<open>L \<in> C\<close> and \<open>\<not>(tautology C)\<close> have "validate_literal ?J (complement L)" 
        unfolding tautology_def by auto
        from \<open>(validate_literal ?J (complement L))\<close> and \<open>(complement L) \<in> D\<close> 
          and \<open>\<not>(validate_clause ?J D)\<close>
        show "False" by auto
      next  
        assume "D-C \<in> ?peval"
        from \<open>D-C \<in> ?peval\<close> and \<open>(validate_formula I ?peval)\<close>
        have "validate_clause I (D-C)" using validate_formula.simps by blast
        from this obtain L where "L \<in> D" and "L \<notin> C" and "validate_literal I L" by auto
        obtain X where "L = (Pos X) \<or> L = (Neg X)" using Literal.exhaust [of L] by auto
        from \<open>L = (Pos X) \<or> L = (Neg X)\<close> and \<open>validate_literal I L\<close> and \<open>L \<notin> C\<close> 
        have "validate_literal ?J L" unfolding tautology_def by auto
        from \<open>validate_literal ?J L\<close> and \<open>L \<in> D\<close> and \<open>\<not>(validate_clause ?J D)\<close>
        show "False" by auto
      qed
    qed
    from \<open>\<not>validate_clause ?J C\<close> and \<open>validate_formula ?J S\<close> and \<open>entails S C\<close> show "False" 
    unfolding entails_def by auto
qed

lemma entailment_and_implicates:
  assumes "entails_formula S1 S2"
  shows "implicates S2 \<subseteq> implicates S1"
using assms entailed_formula_entails_implicates implicates_def by auto

lemma equivalence_and_implicates:
  assumes "equivalent S1 S2"
  shows "implicates S1 = implicates S2"
using assms entailment_and_implicates equivalent_def by blast

lemma equivalence_and_prime_implicates:
  assumes "equivalent S1 S2"
  shows "prime_implicates S1 = prime_implicates S2"
using assms equivalence_and_implicates prime_implicates_def by auto

lemma unrestricted_resolution_is_deductive_complete : 
  assumes "saturated_binary_rule resolvent S"
  assumes "all_fulfill finite S"
  assumes "C \<in> implicates S"
  shows "redundant C S"
proof ((cases "tautology C"),(simp add: redundant_def))
next 
  assume "\<not> tautology C"
  have "\<exists>D. (D \<in> S) \<and> (subsumes D C)"
  proof -
    let ?peval = "partial_evaluation S C"
    from \<open>saturated_binary_rule resolvent S\<close> 
      have "saturated_binary_rule ordered_resolvent ?peval" 
      using partial_evaluation_is_saturated by auto
    from \<open>C \<in> implicates S\<close> have "entails S C" unfolding implicates_def by auto
    from \<open>entails S C\<close> and \<open>\<not>tautology C\<close> have "\<not>satisfiable ?peval"
    using evaluation_wrt_implicate_is_unsat by auto
    from \<open>all_fulfill finite S\<close> have "all_fulfill finite ?peval" unfolding all_fulfill_def by auto
    from \<open>\<not>satisfiable ?peval\<close> and \<open>saturated_binary_rule ordered_resolvent ?peval\<close> 
      and \<open>all_fulfill finite ?peval\<close> 
    have "{} \<in> ?peval" using Complete_def ordered_resolution_is_complete by blast 
    then show ?thesis unfolding subsumes_def by auto
  qed
  then show ?thesis unfolding redundant_def by auto
qed

lemma prime_implicates_generation_correct :
  assumes "saturated_binary_rule resolvent S"
  assumes "non_redundant S"
  assumes "all_fulfill finite S"
  shows "S \<subseteq> prime_implicates S"
proof 
  fix x assume "x \<in> S"
  show "x \<in> prime_implicates S"
  proof (rule ccontr)
    assume "\<not> x \<in> prime_implicates S"
    from \<open>x \<in> S\<close> have "entails S x" unfolding entails_def implicates_def by auto
    then have "x \<in> implicates S" unfolding implicates_def by auto
    with \<open>\<not> x \<in> (prime_implicates S)\<close> have "strictly_redundant x (implicates S)"
      unfolding prime_implicates_def simplify_def by auto
    from this have "tautology x \<or> (\<exists>y. (y \<in> (implicates S)) \<and> (y \<subset> x))" 
      unfolding strictly_redundant_def by auto
    then have "strictly_redundant x S"
    proof ((cases "tautology x"),(simp add: strictly_redundant_def))
    next 
      assume "\<not>tautology x"
      with \<open>tautology x \<or> (\<exists>y. (y \<in> (implicates S)) \<and> (y \<subset> x))\<close> 
        obtain y where "y \<in> implicates S" and "y \<subset> x" by auto
      from \<open>y \<in> implicates S\<close> and \<open>saturated_binary_rule resolvent S\<close> and \<open>all_fulfill finite S\<close>
        have "redundant y S" using unrestricted_resolution_is_deductive_complete by auto
      from \<open>y \<subset> x\<close> and \<open>\<not>tautology x\<close> have "\<not>tautology y" unfolding tautology_def by auto 
      with \<open>redundant y S\<close> obtain z where "z \<in> S" and "z \<subseteq> y" 
        unfolding redundant_def subsumes_def by auto
      with \<open>y \<subset> x\<close> have "z \<subset> x" by auto
      with \<open>z \<in> S\<close> show "strictly_redundant x S" using strictly_redundant_def by auto
    qed
    with \<open>non_redundant S\<close> and \<open>x \<in> S\<close> show "False" unfolding non_redundant_def by auto
 qed
qed

theorem prime_implicates_of_saturated_sets: 
  assumes "saturated_binary_rule resolvent S"
  assumes "all_fulfill finite S"
  assumes "non_redundant S"
  shows "S = prime_implicates S"
proof
  from assms show "S \<subseteq> prime_implicates S" using prime_implicates_generation_correct by auto
  show "prime_implicates S \<subseteq> S"
  proof
    fix x assume "x \<in> prime_implicates S"
    from this have "x \<in> implicates S" unfolding prime_implicates_def simplify_def by auto
    with assms have "redundant x S" 
      using unrestricted_resolution_is_deductive_complete by auto
    show "x \<in> S"
    proof (rule ccontr)
      assume "x \<notin> S"
      with \<open>redundant x S\<close> have "strictly_redundant x S" 
        unfolding redundant_def strictly_redundant_def subsumes_def by auto
      with \<open>S \<subseteq> prime_implicates S\<close> have "strictly_redundant x (prime_implicates S)"
        unfolding strictly_redundant_def by auto
      then have "strictly_redundant x (implicates S)"
        unfolding strictly_redundant_def prime_implicates_def simplify_def by auto
      with \<open>x \<in> prime_implicates S\<close> show "False"  
        unfolding prime_implicates_def simplify_def  by auto
   qed
  qed
qed

subsection \<open>Incremental Prime Implicates Computation\<close>

text \<open>We show that it is possible to compute the set of prime implicates incrementally
i.e., to fix an ordering among atoms, and to compute the set of resolvents upon each atom
one by one, without backtracking (in the sense that if the resolvents upon a given atom are 
generated at some step @{ term i } then no resolvents upon the same atom are generated at 
step @{ term "j>i" }. 
This feature is critical in practice for the efficiency of prime implicates 
generation algorithms.\<close>

text \<open>We first introduce a function computing all resolvents upon a given atom.\<close>

definition all_resolvents_upon :: "'at Formula \<Rightarrow> 'at \<Rightarrow> 'at Formula"
 where  "(all_resolvents_upon S A) = { C. \<exists>P1 P2. P1 \<in> S \<and> P2 \<in> S \<and> C = (resolvent_upon P1 P2 A) }" 

lemma resolvent_upon_correct:
  assumes "P1 \<in> S"
  assumes "P2 \<in> S"
  assumes "C = resolvent_upon P1 P2 A"
  shows "entails S C"
proof cases
  assume "Pos A \<in> P1 \<and> Neg A \<in> P2" 
  with \<open>C = resolvent_upon P1 P2 A\<close> have "resolvent P1 P2 C" 
    unfolding resolvent_def by auto
  with \<open>P1 \<in> S\<close> and \<open>P2 \<in> S\<close> show ?thesis
    using soundness_and_entailment resolution_is_correct by auto
next 
  assume "\<not> (Pos A \<in> P1 \<and> Neg A \<in> P2)"
  with \<open>C = resolvent_upon P1 P2 A\<close> have "P1 \<subseteq> C \<or> P2 \<subseteq> C" by auto
  with \<open>P1 \<in> S\<close> and \<open>P2 \<in> S\<close> have "redundant C S" 
    unfolding redundant_def subsumes_def by auto 
  then show ?thesis using redundancy_implies_entailment by auto
qed

lemma all_resolvents_upon_is_finite:
  assumes "all_fulfill finite S"
  shows "all_fulfill finite (S \<union> (all_resolvents_upon S A))"
using assms unfolding all_fulfill_def all_resolvents_upon_def by auto

lemma atoms_formula_resolvents:
  shows "atoms_formula (all_resolvents_upon S A) \<subseteq>  atoms_formula S"
unfolding all_resolvents_upon_def by auto

text \<open>We define a partial saturation predicate that is restricted to a specific atom.\<close>

definition partial_saturation :: "'at Formula \<Rightarrow> 'at \<Rightarrow> 'at Formula \<Rightarrow> bool"
where
  "(partial_saturation S A R) = (\<forall>P1 P2. (P1 \<in> S \<longrightarrow> P2 \<in> S  
    \<longrightarrow>(redundant (resolvent_upon P1 P2 A) R)))"

text \<open>We show that the resolvent of two redundant clauses in a partially saturated set 
is itself redundant.\<close>

lemma resolvent_upon_and_partial_saturation :
  assumes "redundant P1 S"
  assumes "redundant P2 S"
  assumes "partial_saturation S A (S \<union> R)"
  assumes "C = resolvent_upon P1 P2 A"
  shows "redundant C (S \<union> R)"
proof (rule ccontr)
  assume "\<not>redundant C  (S \<union> R)"
  from \<open>C = resolvent_upon P1 P2 A\<close> have "C = (P1 - { Pos A }) \<union> (P2 - { Neg A })" by auto
  from \<open>\<not>redundant C  (S \<union> R)\<close> have "\<not>tautology C" unfolding redundant_def by auto 
  have "\<not> (tautology P1)"
  proof   
    assume "tautology P1"
    then obtain B where "Pos B \<in> P1" and "Neg B \<in> P1" unfolding tautology_def by auto
    show "False"
    proof cases
      assume "A = B"
      with \<open>Neg B \<in> P1\<close> and \<open>C = (P1 - { Pos A }) \<union> (P2 - { Neg A })\<close> have "subsumes P2 C"
        unfolding subsumes_def using Literal.distinct by blast
      with \<open>redundant P2 S\<close> have "redundant C S" 
        using subsumption_preserves_redundancy by auto
      with \<open>\<not>redundant C (S \<union> R)\<close> show "False" unfolding redundant_def by auto
    next 
      assume "A \<noteq> B"
      with \<open>C = (P1 - { Pos A }) \<union> (P2 - { Neg A })\<close> and \<open>Pos B \<in> P1\<close> and \<open>Neg B \<in> P1\<close> 
      have "Pos B \<in> C" and "Neg B \<in> C" by auto
      with \<open>\<not>redundant C  (S \<union> R)\<close> show "False" 
        unfolding tautology_def redundant_def by auto
    qed
  qed
  with \<open>redundant P1 S\<close> obtain Q1 where "Q1 \<in> S" and "subsumes Q1 P1" 
    unfolding redundant_def by auto
  have "\<not> (tautology P2)"
  proof   
    assume "tautology P2"
    then obtain B where "Pos B \<in> P2" and "Neg B \<in> P2" unfolding tautology_def by auto
    show "False"
    proof cases
      assume "A = B"
      with \<open>Pos B \<in> P2\<close> and \<open>C = (P1 - { Pos A }) \<union> (P2 - { Neg A })\<close> have "subsumes P1 C"
        unfolding subsumes_def using Literal.distinct by blast
      with \<open>redundant P1 S\<close> have "redundant C S" 
        using subsumption_preserves_redundancy by auto
      with \<open>\<not>redundant C  (S \<union> R)\<close> show "False" unfolding redundant_def by auto
    next 
      assume "A \<noteq> B"
      with \<open>C = (P1 - { Pos A }) \<union> (P2 - { Neg A })\<close> and \<open>Pos B \<in> P2\<close> and \<open>Neg B \<in> P2\<close> 
      have "Pos B \<in> C" and "Neg B \<in> C" by auto
      with \<open>\<not>redundant C  (S \<union> R)\<close> show "False" 
      unfolding tautology_def redundant_def  by auto
    qed
  qed
  with \<open>redundant P2 S\<close> obtain Q2 where "Q2 \<in> S" and "subsumes Q2 P2" 
    unfolding redundant_def by auto
  let ?res = "(Q1 - { Pos A }) \<union> (Q2 - { Neg A })"
  have "?res = resolvent_upon Q1 Q2 A" by auto
  from this  and \<open>partial_saturation S A  (S \<union> R)\<close> and \<open>Q1 \<in> S\<close> and  \<open>Q2 \<in> S\<close> 
    have "redundant ?res  (S \<union> R)" 
    unfolding partial_saturation_def by auto  
  from \<open>subsumes Q1 P1\<close> and \<open>subsumes Q2 P2\<close> and \<open>C = (P1 - { Pos A }) \<union> (P2 - { Neg A })\<close> 
  have "subsumes ?res C" unfolding subsumes_def by auto
  with \<open>redundant ?res  (S \<union> R)\<close> and \<open>\<not>redundant C  (S \<union> R)\<close> show False 
    using subsumption_preserves_redundancy by auto
qed

text \<open>We show that if @{term R} is a set of resolvents of a set of clauses @{term S} then the 
same holds for @{ term "S \<union> R"}. For the clauses in @{term S}, the premises are identical to 
the resolvent and the inference is thus redundant (this trick is useful to simplify proofs).\<close>

definition in_all_resolvents_upon:: "'at Formula \<Rightarrow> 'at \<Rightarrow> 'at Clause \<Rightarrow> bool"
where 
  "in_all_resolvents_upon S A C = (\<exists> P1 P2. (P1 \<in> S \<and> P2 \<in> S \<and> C = resolvent_upon P1 P2 A))"
 
lemma every_clause_is_a_resolvent:
  assumes "all_fulfill (in_all_resolvents_upon S A) R"
  assumes "all_fulfill (\<lambda>x. \<not>(tautology x)) S"
  assumes "P1 \<in> S \<union> R"
  shows "in_all_resolvents_upon S A P1"
proof ((cases "P1 \<in> R"),(metis all_fulfill_def assms(1)))
next 
    assume "P1 \<notin> R"
    with \<open>P1 \<in> S \<union> R\<close> have "P1 \<in> S" by auto
    with \<open>(all_fulfill (\<lambda>x. \<not>(tautology x)) S )\<close> have "\<not> tautology P1" 
      unfolding all_fulfill_def by auto
    from \<open>\<not> tautology P1\<close> have "Neg A \<notin> P1 \<or> Pos A \<notin> P1" unfolding tautology_def by auto
    from this have "P1 = (P1 - { Pos A }) \<union> (P1 - { Neg A })" by auto
    with \<open>P1 \<in> S\<close> show ?thesis unfolding resolvent_def 
      unfolding in_all_resolvents_upon_def by auto
qed

text \<open>We show that if a formula is partially saturated then it stays so when new resolvents 
are added in the set.\<close>

lemma partial_saturation_is_preserved :
  assumes "partial_saturation S E1 S"
  assumes "partial_saturation S E2 (S \<union> R)"
  assumes "all_fulfill (\<lambda>x. \<not>(tautology x)) S"
  assumes "all_fulfill (in_all_resolvents_upon S E2) R"
  shows "partial_saturation (S \<union> R) E1 (S \<union> R)"
proof (rule ccontr)
  assume "\<not> partial_saturation (S \<union> R) E1 (S \<union> R)"
  from this obtain P1 P2 C where "P1 \<in> S \<union> R" and "P2 \<in> S \<union> R" and "C = resolvent_upon P1 P2 E1" 
    and "\<not> redundant C (S \<union> R)"
    unfolding partial_saturation_def by auto
  from \<open>C = resolvent_upon P1 P2 E1\<close> have "C = (P1 - { Pos E1 }) \<union> (P2 - { Neg E1 })" by auto
  from \<open>P1 \<in> S \<union> R\<close> and assms(4) and \<open>(all_fulfill (\<lambda>x. \<not>(tautology x)) S )\<close> 
  have "in_all_resolvents_upon S E2 P1" using every_clause_is_a_resolvent by auto
  then obtain P1_1 P1_2 where "P1_1 \<in> S" and "P1_2 \<in> S" and "P1 = resolvent_upon P1_1 P1_2 E2"
    using every_clause_is_a_resolvent unfolding in_all_resolvents_upon_def by blast
  from \<open>P2 \<in> S \<union> R\<close> and assms(4) and \<open>(all_fulfill (\<lambda>x. \<not>(tautology x)) S )\<close> 
    have "in_all_resolvents_upon S E2 P2"  using every_clause_is_a_resolvent by auto
  then obtain P2_1 P2_2 where "P2_1 \<in> S" and "P2_2 \<in> S" and  "P2 = resolvent_upon P2_1 P2_2 E2"
    using every_clause_is_a_resolvent unfolding in_all_resolvents_upon_def by blast
  let ?R1 = "resolvent_upon P1_1 P2_1 E1"
  from \<open>partial_saturation S E1 S\<close> and \<open>P1_1 \<in> S\<close> and \<open>P2_1 \<in> S\<close> have "redundant ?R1 S" 
    unfolding partial_saturation_def by auto
  let ?R2 = "resolvent_upon P1_2 P2_2 E1"
  from \<open>partial_saturation S E1 S\<close> and \<open>P1_2 \<in> S\<close> and \<open>P2_2 \<in> S\<close> have "redundant ?R2 S" 
    unfolding partial_saturation_def by auto
  let ?C = "resolvent_upon ?R1 ?R2 E2"
  from \<open>C = resolvent_upon P1 P2 E1\<close> and \<open>P2 = resolvent_upon P2_1 P2_2 E2\<close> 
    and \<open>P1 = resolvent_upon P1_1 P1_2 E2\<close>
    have "?C = C" by auto
  with \<open>redundant ?R1 S\<close> and \<open>redundant ?R2 S\<close> and \<open>partial_saturation S E2 (S \<union> R)\<close> 
    and \<open>\<not> redundant C (S \<union> R)\<close>
    show "False" using resolvent_upon_and_partial_saturation by auto 
qed

text \<open>The next lemma shows that the clauses inferred by applying the resolution rule
 upon a given atom contain no occurrence of this atom, unless the inference is redundant.\<close>

lemma resolvents_do_not_contain_atom :
  assumes "\<not> tautology P1"
  assumes "\<not> tautology P2"
  assumes "C = resolvent_upon P1 P2 E2"
  assumes "\<not> subsumes P1 C"
  assumes "\<not> subsumes P2 C"
  shows "(Neg E2) \<notin> C \<and> (Pos E2) \<notin> C"
proof
  from \<open>C = resolvent_upon P1 P2 E2\<close> have "C = (P1 - { Pos E2 }) \<union> (P2 - { Neg E2 })" 
    by auto
  show "(Neg E2) \<notin> C"
  proof 
    assume "Neg E2 \<in> C"
    from \<open>C = resolvent_upon P1 P2 E2\<close> have "C = (P1 - { Pos E2 }) \<union> (P2 - { Neg E2 })" 
      by auto
    with \<open>Neg E2 \<in> C\<close> have "Neg E2 \<in> P1" by auto
    from \<open>\<not> subsumes P1 C\<close> and  \<open>C = (P1 - { Pos E2 }) \<union> (P2 - { Neg E2 })\<close> have "Pos E2 \<in> P1"  
      unfolding subsumes_def by auto
    from \<open>Neg E2 \<in> P1\<close> and \<open>Pos E2 \<in> P1\<close> and  \<open>\<not> tautology P1\<close> show "False" 
      unfolding tautology_def by auto
  qed
  next show "(Pos E2) \<notin> C"
  proof
    assume "Pos E2 \<in> C"
    from \<open>C = resolvent_upon P1 P2 E2\<close> have "C = (P1 - { Pos E2 }) \<union> (P2 - { Neg E2 })" 
      by auto
    with \<open>Pos E2 \<in> C\<close> have "Pos E2 \<in> P2" by auto
    from \<open>\<not> subsumes P2 C\<close> and  \<open>C = (P1 - { Pos E2 }) \<union> (P2 - { Neg E2 })\<close> have "Neg E2 \<in> P2"  
      unfolding subsumes_def by auto
    from \<open>Neg E2 \<in> P2\<close> and \<open>Pos E2 \<in> P2\<close> and  \<open>\<not> tautology P2\<close> show "False" 
      unfolding tautology_def by auto
  qed
qed

text \<open>The next lemma shows that partial saturation can be ensured by computing all 
(non-redundant) resolvents upon the considered atom.\<close>

lemma ensures_partial_saturation :
  assumes "partial_saturation S E2 (S \<union> R)"
  assumes "all_fulfill (\<lambda>x. \<not>(tautology x)) S"
  assumes "all_fulfill (in_all_resolvents_upon S E2) R"
  assumes "all_fulfill (\<lambda>x. (\<not>redundant x S)) R"
  shows "partial_saturation (S \<union> R) E2 (S \<union> R)"
proof (rule ccontr)
  assume "\<not> partial_saturation (S \<union> R) E2 (S \<union> R)"
  from this obtain P1 P2 C where "P1 \<in> S \<union> R" and "P2 \<in> S \<union> R" and "C = resolvent_upon P1 P2 E2" 
    and "\<not> redundant C (S \<union> R)"
    unfolding partial_saturation_def by auto
  have "P1 \<in> S"
  proof (rule ccontr)
    assume "P1 \<notin> S"
    with \<open>P1 \<in> S \<union> R\<close> have "P1 \<in> R" by auto
    with assms(3) obtain P1_1 and P1_2 where "P1_1 \<in> S" and "P1_2 \<in> S" 
     and "P1 = resolvent_upon P1_1 P1_2 E2"
     unfolding all_fulfill_def in_all_resolvents_upon_def by auto
    from \<open>all_fulfill (\<lambda>x. \<not>(tautology x)) S\<close> and \<open>P1_1 \<in> S\<close> and \<open>P1_2 \<in> S\<close> 
      have "\<not> tautology P1_1" and "\<not> tautology P1_2"
      unfolding all_fulfill_def by auto
    from \<open>all_fulfill (\<lambda>x. (\<not>redundant x S)) R\<close> and \<open>P1 \<in> R\<close> and \<open>P1_1 \<in> S\<close> and \<open>P1_2 \<in> S\<close> 
      have "\<not> subsumes P1_1 P1" and "\<not> subsumes P1_2 P1" 
      unfolding redundant_def all_fulfill_def by auto
    from \<open>\<not> tautology P1_1\<close> \<open>\<not> tautology P1_2\<close> \<open>\<not> subsumes P1_1 P1\<close> and \<open>\<not> subsumes P1_2 P1\<close> 
      and \<open>P1 = resolvent_upon P1_1 P1_2 E2\<close> 
      have "(Neg E2) \<notin> P1 \<and> (Pos E2) \<notin> P1" 
      using resolvents_do_not_contain_atom [of P1_1 P1_2 P1 E2] by auto
    with \<open>C = resolvent_upon P1 P2 E2\<close> have "subsumes P1 C" unfolding subsumes_def by auto
    with \<open>\<not> redundant C (S \<union> R)\<close> and \<open>P1 \<in> S \<union> R\<close> show "False" unfolding redundant_def 
      by auto
    qed    
  have "P2 \<in> S"
  proof (rule ccontr)
    assume "P2 \<notin> S"
    with \<open>P2 \<in> S \<union> R\<close> have "P2 \<in> R" by auto
    with assms(3) obtain P2_1 and P2_2 where "P2_1 \<in> S" and "P2_2 \<in> S" 
      and "P2 = resolvent_upon P2_1 P2_2 E2" 
      unfolding all_fulfill_def in_all_resolvents_upon_def by auto
    from \<open>(all_fulfill (\<lambda>x. \<not>(tautology x)) S )\<close> and \<open>P2_1 \<in> S\<close> and \<open>P2_2 \<in> S\<close> 
      have "\<not> tautology P2_1" and "\<not> tautology P2_2"
      unfolding all_fulfill_def by auto
    from \<open>all_fulfill (\<lambda>x. (\<not>redundant x S)) R\<close> and \<open>P2 \<in> R\<close> and \<open>P2_1 \<in> S\<close> and \<open>P2_2 \<in> S\<close> 
      have "\<not> subsumes P2_1 P2" and "\<not> subsumes P2_2 P2" 
      unfolding redundant_def all_fulfill_def by auto
    from \<open>\<not> tautology P2_1\<close> \<open>\<not> tautology P2_2\<close> \<open>\<not> subsumes P2_1 P2\<close> and \<open>\<not> subsumes P2_2 P2\<close> 
      and \<open>P2 = resolvent_upon P2_1 P2_2 E2\<close> 
      have "(Neg E2) \<notin> P2 \<and> (Pos E2) \<notin> P2" 
      using resolvents_do_not_contain_atom [of P2_1 P2_2 P2 E2] by auto
    with \<open>C = resolvent_upon P1 P2 E2\<close> have "subsumes P2 C" unfolding subsumes_def by auto
    with \<open>\<not> redundant C (S \<union> R)\<close> and \<open>P2 \<in> S \<union> R\<close> 
      show "False" unfolding redundant_def by auto
    qed    
   from \<open>P1 \<in> S\<close> and \<open>P2 \<in> S\<close> and \<open>partial_saturation S E2 (S \<union> R)\<close> 
    and \<open>C = resolvent_upon P1 P2 E2\<close> and \<open>\<not> redundant C (S \<union> R)\<close>
    show "False" unfolding redundant_def partial_saturation_def by auto
qed

lemma resolvents_preserve_equivalence:
  shows "equivalent S (S \<union> (all_resolvents_upon S A))"
proof -
  have "S \<subseteq> (S \<union> (all_resolvents_upon S A))" by auto
  then have "entails_formula (S \<union> (all_resolvents_upon S A)) S" using entailment_subset by auto
  have "entails_formula S (S \<union> (all_resolvents_upon S A))"
  proof (rule ccontr)
    assume "\<not>entails_formula S (S \<union> (all_resolvents_upon S A))"
    from this obtain C where "C \<in> (all_resolvents_upon S A)" and "\<not>entails S C" 
      unfolding entails_formula_def using entails_member by auto
    from \<open>C \<in> (all_resolvents_upon S A)\<close> obtain P1 P2 
      where "C = resolvent_upon P1 P2 A" and "P1 \<in> S" and "P2 \<in> S" 
      unfolding all_resolvents_upon_def by auto
    from \<open>C = resolvent_upon P1 P2 A\<close> and \<open>P1 \<in> S\<close> and \<open>P2 \<in> S\<close> have "entails S C" 
      using resolvent_upon_correct by auto
    with \<open>\<not>entails S C\<close> show "False" by auto
  qed
  from \<open>entails_formula (S \<union> (all_resolvents_upon S A)) S\<close> 
    and \<open>entails_formula S (S \<union> (all_resolvents_upon S A))\<close> 
    show ?thesis unfolding equivalent_def by auto
qed

text \<open>Given a sequence of atoms, we define a sequence of clauses obtained by resolving upon 
each atom successively. Simplification rules are applied at each iteration step.\<close>

fun resolvents_sequence :: "(nat \<Rightarrow> 'at) \<Rightarrow> 'at Formula \<Rightarrow> nat \<Rightarrow> 'at Formula"
 where 
  "(resolvents_sequence A S 0) = (simplify S)" |
  "(resolvents_sequence A S (Suc N)) = 
    (simplify ((resolvents_sequence A S N)
      \<union> (all_resolvents_upon (resolvents_sequence A S N) (A N))))"

text \<open>The following lemma states that partial saturation is preserved by simplification.\<close>
 
lemma redundancy_implies_partial_saturation:
  assumes "partial_saturation S1 A S1"
  assumes "S2 \<subseteq> S1"
  assumes "all_fulfill (\<lambda>x. redundant x S2) S1"
  shows "partial_saturation S2 A S2"
proof (rule ccontr)
  assume "\<not>partial_saturation S2 A S2"
  then obtain P1 P2 C where "P1 \<in> S2" "P2 \<in> S2" and "C = (resolvent_upon P1 P2 A)" 
    and "\<not> redundant C S2"
    unfolding partial_saturation_def by auto
  from \<open>P1 \<in> S2\<close> and \<open>S2 \<subseteq> S1\<close> have "P1 \<in> S1" by auto
  from \<open>P2 \<in> S2\<close> and \<open>S2 \<subseteq> S1\<close> have "P2 \<in> S1" by auto
  from \<open>P1 \<in> S1\<close> and \<open>P2 \<in> S1\<close> and \<open>partial_saturation S1 A S1\<close> and \<open>C = resolvent_upon P1 P2 A\<close> 
    have "redundant C S1" unfolding partial_saturation_def by auto
  from \<open>\<not> redundant C S2\<close> have "\<not>tautology C" unfolding redundant_def by auto
  with \<open>redundant C S1\<close> obtain D where "D \<in> S1" and "D \<subseteq> C"  
    unfolding redundant_def subsumes_def by auto
  from \<open>D \<in> S1\<close> and \<open>all_fulfill (\<lambda>x. redundant x S2) S1\<close> have "redundant D S2" 
    unfolding all_fulfill_def by auto
  from \<open>\<not> tautology C\<close> and \<open>D \<subseteq> C\<close> have "\<not> tautology D" unfolding tautology_def by auto
  with \<open>redundant D S2\<close> obtain E where "E \<in> S2" and "E \<subseteq> D" 
    unfolding redundant_def subsumes_def by auto
  from  \<open>E \<subseteq> D\<close> and \<open>D \<subseteq> C\<close> have "E \<subseteq> C" by auto
  from  \<open>E \<in> S2\<close> and \<open>E \<subseteq> C\<close> and \<open>\<not>redundant C S2\<close> show "False" 
    unfolding redundant_def subsumes_def by auto
qed

text \<open>The next theorem finally states that the implicate generation algorithm is sound and 
complete in the sense that the final clause set in the sequence is exactly the set of prime 
implicates of the considered clause set.\<close>

theorem incremental_prime_implication_generation:
  assumes "atoms_formula S = { X. \<exists>I::nat. I < N \<and> X = (A I) }"
  assumes "all_fulfill finite S"
  shows "(prime_implicates S) = (resolvents_sequence A S N)"
proof -

text \<open>We define a set of invariants and show that they are satisfied by all sets in the 
above sequence. For the last set in the sequence, the invariants ensure that the clause set is 
saturated, which entails the desired property.\<close>

  let ?Final = "resolvents_sequence A S N"

text \<open>We define some properties and show by induction that they are satisfied by all the 
clause sets in the constructed sequence\<close>

  let ?equiv_init = "\<lambda>I.(equivalent S (resolvents_sequence A S I))" 
  let ?partial_saturation = "\<lambda>I. (\<forall>J::nat. (J < I 
    \<longrightarrow> (partial_saturation (resolvents_sequence A S I) (A J) (resolvents_sequence A S I))))" 
  let ?no_tautologies = "\<lambda>I.(all_fulfill (\<lambda>x. \<not>(tautology x)) (resolvents_sequence A S I) )"
  let ?atoms_init = "\<lambda>I.(atoms_formula (resolvents_sequence A S I)  
                      \<subseteq>  { X. \<exists>I::nat. I < N \<and> X = (A I)})"
  let ?non_redundant = "\<lambda>I.(non_redundant (resolvents_sequence A S I))" 
  let ?finite ="\<lambda>I. (all_fulfill finite (resolvents_sequence A S I))"

  have "\<forall>I. (I \<le> N   \<longrightarrow> (?equiv_init I)  \<and> (?partial_saturation I) \<and>  (?no_tautologies I) 
          \<and> (?atoms_init I) \<and> (?non_redundant I) \<and> (?finite I) )"

  proof (rule allI)
    fix I
    show " (I \<le> N  
      \<longrightarrow> (?equiv_init I) \<and> (?partial_saturation I) \<and>  (?no_tautologies I) \<and> (?atoms_init I)    
            \<and> (?non_redundant I) \<and> (?finite I) )" (is "I \<le> N \<longrightarrow> ?P I")
    proof (induction I)

text \<open>We show that the properties are all satisfied by the initial clause set 
(after simplification).\<close>

      show "0 \<le> N \<longrightarrow> ?P 0" 
      proof (rule impI)+
          assume "0 \<le> N" 
          let ?R = "resolvents_sequence A S 0"
          from \<open>all_fulfill finite S\<close> 
          have "?equiv_init 0" using simplify_preserves_equivalence  by auto
          moreover have "?no_tautologies 0" 
            using simplify_def strictly_redundant_def all_fulfill_def by auto
          moreover have "?partial_saturation 0" by auto
          moreover from \<open>all_fulfill finite S\<close>  have "?finite 0" using simplify_finite by auto
          moreover have "atoms_formula ?R \<subseteq> atoms_formula S" using atoms_formula_simplify by auto
          moreover with \<open>atoms_formula S = { X. \<exists>I::nat. I < N \<and> X = (A I) }\<close> 
            have v: "?atoms_init 0"  unfolding simplify_def by auto
          moreover have "?non_redundant 0" using simplify_non_redundant by auto
          ultimately show "?P 0" by auto
      qed

text \<open>We then show that the properties are preserved by induction.\<close>

      next
      fix I assume "I \<le> N \<longrightarrow> ?P I" 
      show "(Suc I) \<le> N \<longrightarrow> (?P (Suc I))" 
      proof (rule impI)+
        assume  "(Suc I) \<le> N"
        let ?Prec = "resolvents_sequence A S I"
        let ?R = "resolvents_sequence A S (Suc I)"
        from \<open>Suc I \<le> N\<close> and \<open>I \<le> N \<longrightarrow> ?P I\<close> 
          have "?equiv_init I" and "?partial_saturation I" and "?no_tautologies I" and "?finite I"
            and "?atoms_init I" and "?non_redundant I" by auto
        have "equivalent ?Prec (?Prec \<union> (all_resolvents_upon ?Prec (A I)))" 
          using resolvents_preserve_equivalence by auto
        from \<open>?finite I\<close> have "all_fulfill finite (?Prec \<union> (all_resolvents_upon ?Prec (A I)))" 
          using all_resolvents_upon_is_finite by auto
        then have "all_fulfill finite (simplify (?Prec \<union> (all_resolvents_upon ?Prec (A I))))" 
          using simplify_finite by auto
        then have "?finite (Suc I)" by auto
        from \<open>all_fulfill finite (?Prec \<union> (all_resolvents_upon ?Prec (A I)))\<close> 
          have "equivalent (?Prec \<union> (all_resolvents_upon ?Prec (A I))) ?R" 
        using simplify_preserves_equivalence by auto
        from \<open>equivalent ?Prec (?Prec \<union> (all_resolvents_upon ?Prec (A I)))\<close> 
        and \<open>equivalent (?Prec \<union> (all_resolvents_upon ?Prec (A I))) ?R\<close>
          have "equivalent ?Prec ?R" by (rule equivalent_transitive)
        from \<open>?equiv_init I\<close> and this have "?equiv_init (Suc I)" by (rule equivalent_transitive)
        have "?no_tautologies (Suc I)" using simplify_def strictly_redundant_def all_fulfill_def 
          by auto
        let ?Delta = "?R - ?Prec"
        have "?R \<subseteq> ?Prec \<union> ?Delta" by auto
        have "all_fulfill (\<lambda>x. (redundant x ?R)) (?Prec \<union> ?Delta)"
        proof (rule ccontr)
          assume "\<not>all_fulfill (\<lambda>x. (redundant x ?R)) (?Prec \<union> ?Delta)"
          then obtain x where "\<not>redundant x ?R" and "x \<in> ?Prec \<union> ?Delta" unfolding all_fulfill_def 
            by auto
          from \<open>\<not>redundant x ?R\<close> have "\<not>x \<in> ?R" unfolding redundant_def subsumes_def by auto
          with \<open>x \<in> ?Prec \<union> ?Delta\<close> have "x \<in> (?Prec \<union> (all_resolvents_upon ?Prec (A I)))" 
            by auto
          with \<open>all_fulfill finite (?Prec \<union> (all_resolvents_upon ?Prec (A I)))\<close>
            have "redundant x (simplify (?Prec \<union> (all_resolvents_upon ?Prec (A I))))"
              using simplify_and_membership by blast 
          with \<open>\<not>redundant x ?R\<close> show "False" by auto
        qed
        have "all_fulfill (in_all_resolvents_upon ?Prec (A I)) ?Delta"
        proof (rule ccontr)
          assume "\<not> (all_fulfill (in_all_resolvents_upon ?Prec (A I)) ?Delta)"
          then obtain C where "C \<in> ?Delta" 
            and "\<not>in_all_resolvents_upon ?Prec (A I) C" 
            unfolding all_fulfill_def by auto
          then obtain C where "C \<in> ?Delta" 
            and not_res: "\<forall> P1 P2. \<not>(P1 \<in> ?Prec \<and> P2 \<in> ?Prec \<and> C = resolvent_upon P1 P2 (A I))" 
            unfolding all_fulfill_def in_all_resolvents_upon_def by blast
          from \<open>C \<in> ?Delta\<close> have "C \<in> ?R" and "C \<notin> ?Prec" by auto 
          then have "C \<in> simplify (?Prec \<union> (all_resolvents_upon ?Prec (A I)))" by auto 
          then have "C \<in> ?Prec \<union> (all_resolvents_upon ?Prec (A I))" unfolding simplify_def by auto
          with \<open>C \<notin> ?Prec\<close> have "C \<in> (all_resolvents_upon ?Prec (A I))" by auto
          with not_res show "False" unfolding all_resolvents_upon_def by auto
        qed
        have "all_fulfill (\<lambda>x. (\<not>redundant x ?Prec)) ?Delta"
        proof (rule ccontr)
          assume "\<not>all_fulfill (\<lambda>x. (\<not>redundant x ?Prec)) ?Delta"
          then obtain C where "C \<in> ?Delta" and redundant: "redundant C ?Prec" 
            unfolding all_fulfill_def by auto
          from \<open>C \<in> ?Delta\<close> have "C \<in> ?R" and "C \<notin> ?Prec" by auto 
            show "False"
          proof cases
            assume "strictly_redundant C ?Prec"
            then have "strictly_redundant C (?Prec \<union> (all_resolvents_upon ?Prec (A I)))" 
              unfolding strictly_redundant_def by auto
            then have "C \<notin> simplify (?Prec \<union> (all_resolvents_upon ?Prec (A I)))" 
              unfolding simplify_def by auto
            then have "C \<notin> ?R" by auto
            with \<open>C \<in> ?R\<close> show "False" by auto
            next assume "\<not>strictly_redundant C ?Prec"
            with redundant have "C \<in> ?Prec" 
              unfolding strictly_redundant_def redundant_def subsumes_def by auto
            with \<open>C \<notin> ?Prec\<close> show "False" by auto
          qed
        qed
        have "\<forall>J::nat. (J < (Suc I)) \<longrightarrow> (partial_saturation ?R (A J) ?R)"
        proof (rule ccontr)
          assume "\<not>(\<forall>J::nat. (J < (Suc I)) \<longrightarrow> (partial_saturation ?R (A J) ?R))"
          then obtain J where "J < (Suc I)" and "\<not>(partial_saturation ?R (A J) ?R)" by auto          
          from \<open>\<not>(partial_saturation ?R (A J) ?R)\<close> obtain P1 P2 C 
          where "P1 \<in> ?R" and "P2 \<in> ?R" and "C = resolvent_upon P1 P2 (A J)" and "\<not> redundant C ?R" 
          unfolding partial_saturation_def by auto
          have "partial_saturation ?Prec (A I) (?Prec \<union> ?Delta)"
          proof (rule ccontr)
            assume "\<not>partial_saturation ?Prec (A I) (?Prec \<union> ?Delta)"
            then obtain P1 P2 C where "P1 \<in> ?Prec" and "P2 \<in> ?Prec" 
              and "C = resolvent_upon P1 P2 (A I)" and 
              "\<not>redundant C (?Prec \<union> ?Delta)" unfolding partial_saturation_def by auto
            from \<open>C = resolvent_upon P1 P2 (A I)\<close> and \<open>P1 \<in> ?Prec\<close> and \<open>P2 \<in> ?Prec\<close> 
              have "C \<in> ?Prec \<union> (all_resolvents_upon ?Prec (A I))" 
              unfolding all_resolvents_upon_def by auto
            from \<open>all_fulfill finite (?Prec \<union> (all_resolvents_upon ?Prec (A I)))\<close> 
              and this have "redundant C ?R"  
              using simplify_and_membership [of "?Prec \<union> (all_resolvents_upon ?Prec (A I))" ?R C] 
              by auto
            with \<open>?R \<subseteq> ?Prec \<union> ?Delta\<close> have "redundant C (?Prec \<union> ?Delta)" 
            using superset_preserves_redundancy [of C ?R "(?Prec \<union> ?Delta)"] by auto
            with \<open>\<not>redundant C (?Prec \<union> ?Delta)\<close> show "False" by auto
          qed
          show "False"
          proof cases
            assume "J = I"
            from \<open>partial_saturation ?Prec (A I) (?Prec \<union> ?Delta)\<close> and \<open>?no_tautologies I\<close> 
              and \<open>(all_fulfill (in_all_resolvents_upon ?Prec (A I)) ?Delta)\<close> 
              and \<open>all_fulfill (\<lambda>x. (\<not>redundant x ?Prec)) ?Delta\<close>
              have "partial_saturation (?Prec \<union> ?Delta) (A I) (?Prec \<union> ?Delta)" 
              using ensures_partial_saturation [of ?Prec "(A I)" ?Delta] by auto
            with \<open>?R \<subseteq> ?Prec \<union> ?Delta\<close> 
              and \<open>all_fulfill (\<lambda>x. (redundant x ?R)) (?Prec \<union> ?Delta)\<close>
            have "partial_saturation ?R (A I) ?R" using redundancy_implies_partial_saturation 
              by auto
            with \<open>J = I\<close> and \<open>\<not>(partial_saturation ?R (A J) ?R)\<close> show "False" by auto
          next 
            assume "J \<noteq> I"
            with \<open>J < (Suc I)\<close> have "J < I" by auto
            with \<open>?partial_saturation I\<close> 
              have "partial_saturation ?Prec (A J) ?Prec" by auto
            with \<open>partial_saturation ?Prec (A I) (?Prec \<union> ?Delta)\<close> and \<open>?no_tautologies I\<close> 
              and \<open>(all_fulfill (in_all_resolvents_upon ?Prec (A I)) ?Delta)\<close>
              and \<open>all_fulfill (\<lambda>x. (\<not>redundant x ?Prec)) ?Delta\<close> 
              have "partial_saturation (?Prec \<union> ?Delta) (A J) (?Prec \<union> ?Delta)"
              using partial_saturation_is_preserved [of ?Prec "A J" "A I" ?Delta] by auto
            with \<open>?R \<subseteq> ?Prec \<union> ?Delta\<close> 
              and \<open>all_fulfill (\<lambda>x. (redundant x ?R)) (?Prec \<union> ?Delta)\<close>
              have "partial_saturation ?R (A J) ?R" 
              using redundancy_implies_partial_saturation by auto
            with \<open>\<not>(partial_saturation ?R (A J) ?R)\<close> show "False" by auto
         qed
       qed
       have  "non_redundant ?R" using simplify_non_redundant by auto
       from \<open>?atoms_init I\<close> have "atoms_formula (all_resolvents_upon ?Prec (A I)) 
                                    \<subseteq>  { X. \<exists>I::nat. I < N \<and> X = (A I)}"
       using atoms_formula_resolvents [of ?Prec "A I"] by auto
       with \<open>?atoms_init I\<close> 
        have "atoms_formula (?Prec \<union> (all_resolvents_upon ?Prec (A I))) 
                \<subseteq>  { X. \<exists>I::nat. I < N \<and> X = (A I)}"
        using atoms_formula_union [of ?Prec "all_resolvents_upon ?Prec (A I)"]  by auto
       from this have "atoms_formula ?R \<subseteq>  { X. \<exists>I::nat. I < N \<and> X = (A I)}"
       using atoms_formula_simplify [of "?Prec \<union> (all_resolvents_upon ?Prec (A I))"]  by auto
       from  \<open>equivalent S (resolvents_sequence A S (Suc I))\<close> 
          and \<open>(\<forall>J::nat. (J < (Suc I) 
            \<longrightarrow> (partial_saturation (resolvents_sequence A S (Suc I)) (A J) 
                  (resolvents_sequence A S (Suc I)))))\<close> 
          and \<open>(all_fulfill (\<lambda>x. \<not>(tautology x)) (resolvents_sequence A S (Suc I)) )\<close>
          and \<open>(all_fulfill finite (resolvents_sequence A S (Suc I)))\<close>
          and \<open>non_redundant ?R\<close>
          and \<open>atoms_formula (resolvents_sequence A S (Suc I))  \<subseteq>  { X. \<exists>I::nat. I < N \<and> X = (A I)}\<close>
       show "?P (Suc I)" by auto
     qed
   qed
  qed

text \<open>Using the above invariants, we show that the final clause set is saturated.\<close>

  from this have "\<forall>J. (J < N \<longrightarrow> partial_saturation ?Final (A J) ?Final)" 
    and "atoms_formula (resolvents_sequence A S N)  \<subseteq>  { X. \<exists>I::nat. I < N \<and> X = (A I)}" 
    and "equivalent S ?Final"
    and "non_redundant ?Final"
    and "all_fulfill finite ?Final"
  by auto
  have "saturated_binary_rule resolvent ?Final"
  proof (rule ccontr)
    assume "\<not> saturated_binary_rule resolvent ?Final"
    then obtain P1 P2 C where "P1 \<in> ?Final" and "P2 \<in> ?Final" and "resolvent P1 P2 C" 
      and "\<not>redundant C ?Final" 
      unfolding saturated_binary_rule_def by auto
    from \<open>resolvent P1 P2 C\<close> obtain B where "C = resolvent_upon P1 P2 B" 
      unfolding resolvent_def by auto
      show "False"
    proof cases
      assume "B \<in> (atoms_formula ?Final)"
      with \<open>atoms_formula ?Final \<subseteq> { X. \<exists>I::nat. I < N \<and> X = (A I) }\<close> 
        obtain I where "B = (A I)" and "I < N" 
        by auto
      from \<open>B = (A I)\<close> and \<open>C = resolvent_upon P1 P2 B\<close> have "C = resolvent_upon P1 P2 (A I)" 
        by auto
      from \<open>\<forall>J. (J < N \<longrightarrow> partial_saturation ?Final (A J) ?Final)\<close> and \<open>B = (A I)\<close>and \<open>I < N\<close> 
        have "partial_saturation ?Final (A I) ?Final" by auto 
      with \<open>C = resolvent_upon P1 P2 (A I)\<close>and \<open>P1 \<in> ?Final\<close> and \<open>P2 \<in> ?Final\<close>
        have "redundant C ?Final" unfolding partial_saturation_def by auto
      with \<open>\<not>redundant C ?Final\<close> show "False" by auto
    next 
      assume "B \<notin> atoms_formula ?Final"
      with \<open>P1 \<in> ?Final\<close> have "B \<notin> atoms_clause P1" by auto 
      then have "Pos B \<notin> P1" by auto 
      with \<open>C = resolvent_upon P1 P2 B\<close> have "P1 \<subseteq> C" by auto
      with \<open>P1 \<in> ?Final\<close> and  \<open>\<not>redundant C ?Final\<close> show "False" 
        unfolding redundant_def subsumes_def by auto
    qed
   qed
   with \<open>all_fulfill finite ?Final\<close> and \<open>non_redundant ?Final\<close> 
    have "prime_implicates ?Final = ?Final" 
    using prime_implicates_of_saturated_sets [of ?Final] by auto
   with \<open>equivalent S ?Final\<close> show ?thesis using  equivalence_and_prime_implicates by auto
qed

end
end
