section \<open>Introduction\<close>

theory AnselmGod
imports Main
begin

text \<open>This paper presents an automated verification of Anselm's ontological argument, as
reconstructed by Paul Oppenheimer and Edward Zalta @{cite "oppenheimer_logic_1991"}, in
Isabelle/HOL, an interactive theorem prover for higher-order logic. Previously, the argument has being
automated by Oppenheimer and Zalta in Prover9 @{cite "oppenheimer_computationally-discovered_2011"},
an automated theorem prover for first-order logic, and by John Rushby in PVS
@{cite "rushby_ontological_2013"}, an automated theorem prover for higher-order logic. Automations of
other versions of the argument include @{cite "benzmuller_godels_2013"}, @{cite "rushby_mechanized_2016"} 
and @{cite "fuenmayor_types_2017"}. My purpose here is to present a basis for comparison in the spirit 
of @{cite "wiedijk_seventeen_2006"}, which compares automated proofs of the irrationality 
of $\sqrt 2$.\<close>

text \<open>Oppenheimer and Zalta's reconstruction is based on the idea of treating `that than 
which nothing greater can be conceived' as a definite description, and treating definite
descriptions as singular terms. But in Isabelle/HOL all terms, including definite descriptions, 
are assumed to denote. So the main task is to embed a free logic for definite descriptions within 
Isabelle/HOL. (Previously, a free logic has been embedded into  Isabelle/HOL by  Christoph
Benzmuller and Dana Scott @{cite "benzmuller_automating_2016"}. But theirs differs from Zalta
and Oppenheimer's in several ways). Once Isabelle/HOL is equipped with free definite descriptions,
reconstructing the argument is straightforward.\<close>

section \<open>Free Logic\<close>

text \<open>Isabelle treats definite descriptions as singular terms of the form @{term "THE x. \<phi> x"}.
However, all terms in Isabelle are assumed to denote, and so from universal elimination we have 
the validity of the argument form:\<close>

lemma "\<forall> x. \<psi> x \<Longrightarrow> \<psi> (THE x. \<phi> x)" by (rule allE)

text \<open>In the presence of definite descriptions which do not denote, this argument form is invalid;
for example, from  `everyone has hair' we should not infer `the present King of France has hair',
since the present King of France does not exist.\<close>

text \<open>This problem can be avoided by introducing a null individual @{term "n"} to serve as the
reference of non-denoting definite descriptions, as follows:\<close>

typedecl i \<comment> \<open>the type of individuals\<close>
consts n:: "i" ("n") \<comment> \<open>the null individual\<close>

text \<open>Then the universal and particular quantifiers can be restricted to
individuals excluding the null-individual as follows, where the new free quantifiers
are distinguished from the classical quantifiers by bold type:\<close>
abbreviation universal_quantifier:: "(i \<Rightarrow> bool) \<Rightarrow> bool" ("\<^bold>\<forall>") 
  where "\<^bold>\<forall> \<phi> \<equiv> \<forall>x::i. (\<not> x = n \<longrightarrow> \<phi> x)"
abbreviation universal_syntax:: "(i \<Rightarrow> bool) \<Rightarrow> bool" (binder "\<^bold>\<forall>" [8] 9)
  where "\<^bold>\<forall> x. \<phi> x \<equiv> \<^bold>\<forall> \<phi>"

abbreviation particular_quantifier:: "(i \<Rightarrow> bool) \<Rightarrow> bool" ("\<^bold>\<exists>")
  where "\<^bold>\<exists> \<phi> \<equiv> \<exists>x::i. (x \<noteq> n \<and> \<phi> x)"
abbreviation particular_syntax:: "(i \<Rightarrow> bool) \<Rightarrow> bool" (binder "\<^bold>\<exists>" [8] 9)
  where "\<^bold>\<exists> x. \<phi> x \<equiv> \<^bold>\<exists> \<phi>"    
text \<open>Note that the quantifiers here range over both existent and non-existent individuals, whereas 
the quantifiers in @{cite "benzmuller_automating_2016"} range only over existent individuals.\<close>

text \<open>In the free logic employed by Oppenheimer and Zalta, statements of identity in which terms
do not denote are always false @{cite "oppenheimer_logic_1991"}, p. 511. So the domain of the identity
relation should be restricted to exclude the null-individual:\<close>

abbreviation identity:: "i \<Rightarrow> i \<Rightarrow> bool" ("is")
  where "is x y \<equiv> x \<noteq> n \<and> x = y"
abbreviation identity_syntax:: "i \<Rightarrow> i \<Rightarrow> bool" (infix "\<^bold>=" 50 )
  where "x \<^bold>= y \<equiv> is x y"

text \<open>Once identity is introduced, the uniqueness quantifier can then be defined in the usual way:\<close>
abbreviation uniqueness_quantifier:: "(i \<Rightarrow> bool) \<Rightarrow> bool" ("unique")
 where "unique \<phi> \<equiv> (\<^bold>\<exists> x::i. \<phi> x \<and> (\<^bold>\<forall> y::i. \<phi> y \<longrightarrow> x \<^bold>= y))"
abbreviation uniqueness_syntax:: "(i \<Rightarrow> bool) \<Rightarrow> bool" (binder "unique" [8] 9)
  where "unique x. \<phi> x \<equiv> unique \<phi>"

text \<open>Finally, the logic employed by Oppenheimer and Zalta is a negative free logic, in that
applications of atomic predicates to non-denoting terms are always false
@{cite "oppenheimer_logic_1991"}, p. 511. So it's necessary to introduce a higher-order predicate
distinguishing between atomic and non-atomic predicates, and to introduce an axiom stipulating that
no atomic predicate is true of the null individual:\<close>

consts atomic_predicates:: "(i \<Rightarrow> bool) \<Rightarrow> bool " ("atomic")
axiomatization where negativity_constraint: "atomic \<phi> \<Longrightarrow> \<not> \<phi> n"

text \<open>In addition, it has to be stated that identity is atomic:\<close>
axiomatization where identity_atomic: "\<And> x. atomic (is x)"

text \<open>One of the most controversial premises of  the ontological argument is that `exists'
is a genuine or atomic  predicate. But surprisingly, we shall see below that the argument
does not require this premise.\<close>

section \<open>Definite Descriptions\<close>

text \<open>The main idea of Oppenheimer and Zalta's reconstruction of the ontological argument is to
treat definite descriptions as genuine singular terms, which leads to the following syntax in
Isabelle/HOL:\<close>
consts definite_description:: "(i \<Rightarrow> bool) \<Rightarrow> i" ("\<^bold>\<tau>")
abbreviation description_syntax:: "(i \<Rightarrow> bool) \<Rightarrow> i" (binder "\<^bold>\<tau>" [8] 9)
where "\<^bold>\<tau> x. \<phi> x \<equiv> \<^bold>\<tau> \<phi>"

text \<open>In Oppenheimer and Zalta's reconstruction of the argument, definite descriptions
are governed by the Russellian axiom schema @{cite "oppenheimer_logic_1991"}, p. 513:\<close>
axiomatization where description_axiom:
"atomic \<psi> \<Longrightarrow> \<psi> (\<^bold>\<tau> x. \<phi> x) \<equiv> (\<^bold>\<exists> x. \<phi> x \<and> (\<^bold>\<forall> y. \<phi> y \<longrightarrow> x \<^bold>= y) \<and> \<psi> x)"

text \<open>From this axiom schema, Oppenheimer and Zalta derive two intermediary theorems
 to be used in the reconstruction of their argument  @{cite "oppenheimer_logic_1991"}, pp. 513-4. 
According to the first:\<close>
theorem  description_theorem_1: "unique x. \<phi> x \<Longrightarrow> \<^bold>\<exists> y. y \<^bold>= (\<^bold>\<tau> x. \<phi> x)"
using description_axiom identity_atomic by blast

text \<open>The second theorem follows directly from the following lemma:\<close>

lemma lemma_1: "a \<^bold>= (\<^bold>\<tau> x. \<phi> x) \<Longrightarrow> \<phi> (\<^bold>\<tau> x. \<phi> x)"
using description_axiom identity_atomic by blast

theorem description_theorem_2: "\<^bold>\<exists> x. x \<^bold>= (\<^bold>\<tau> x. \<phi> x) \<Longrightarrow> \<phi> (\<^bold>\<tau> x. \<phi> x)"
by (simp add: lemma_1)

text \<open>In the course of verifying the argument using Prover9, Oppenheimer and Zalta discovered 
a simplified proof which uses instead @{cite "oppenheimer_computationally-discovered_2011"}, p. 345:\<close>
theorem description_theorem_3:
"atomic \<psi> \<Longrightarrow> \<psi> (\<^bold>\<tau> x. \<phi> x) \<Longrightarrow> \<^bold>\<exists> y. y \<^bold>= (\<^bold>\<tau> x. \<phi> x)" 
using negativity_constraint by fastforce

text \<open>Notice that it is only this last theorem which presupposes the negativity constraint,
whereas the first two theorems depend only on the atomicity of identity.\<close>

section \<open>Anselm's Argument\<close>

text \<open>The argument proper employs the following non-logical vocabulary:\<close>
consts existence:: "i \<Rightarrow> bool" ("E") \<comment> \<open>exists in reality\<close>
consts greater_than:: "i\<Rightarrow>i\<Rightarrow>bool" ("G") \<comment> \<open>is greater than\<close>
consts conceivable:: "i\<Rightarrow>bool" ("C") \<comment> \<open>exists in the understanding\<close>
text \<open>Note that @{term "E a"} is not intended by Oppenheimer and Zalta to be equivalent to
@{term "\<^bold>\<exists> x. a = x"} since according to their reading of the argument, some things do not exist
in reality @{cite "oppenheimer_logic_1991"}, p. 514.\<close>

text \<open>Finally, the presentation of the argument is simplified by introducing
the following abbreviation for the predicate `is a being greater than which none can be conceived':\<close>
abbreviation none_greater_than :: "i\<Rightarrow>bool" ("\<Phi>")
where "\<Phi> x \<equiv> (C x \<and> \<not>(\<^bold>\<exists> y. G y x \<and> C y))"
  
text \<open>With this vocabulary in place, a name for God can be introduced as an abbreviation
for the description `the being greater than which none can be conceived':\<close>

definition g :: "i" where "g \<equiv> (\<^bold>\<tau> x. \<Phi> x)"

text \<open>In Oppenheimer and Zalta's presentation every name is assumed to denote, so a name for
God cannot be introduced until it is proved that the description @{term "(\<^bold>\<tau> x. \<Phi> x)"} denotes
 @{cite "oppenheimer_logic_1991"}, p, 520. But since it's not assumed in this presentation that every
name denotes or, in other words, since it's not assumed that no names denote the null individual,
 it's not necessary to postpone this step.\<close>

text \<open>The final quasi-logical premise in Oppenheimer and Zalta's reconstruction of the argument
is the connectivity of `is greater than', which is used in the proof of the following lemma
@{cite "oppenheimer_logic_1991"}, p. 518:\<close>
  
lemma lemma_2:
  assumes connectivity: "\<^bold>\<forall> x. \<^bold>\<forall> y. G x y \<or> G y x \<or> x \<^bold>= y"
  shows "\<^bold>\<exists> x. \<Phi> x \<Longrightarrow> unique x. \<Phi> x"
  using connectivity by blast 

text \<open>Note that \<open>connectivity\<close> disallows any ties with respect to greatness. This is
implausible, since you and I, for example, may be equally great, without being the same person. So
\<open>connectivity\<close> should not be thought of as merely stipulative, and a weaker premise would
be desirable.\<close>    
    
text \<open>With this vocabulary in place, Anselm's ontological argument, as reconstructed by
Oppenheimer and Zalta, can be stated as follows:\<close>
theorem 
  assumes premise_1:  "\<^bold>\<exists> x. \<Phi> x"
 \<comment> \<open>there exists in the understanding a being greater than which
none can be conceived\<close>
and premise_2:  "\<not> E (\<^bold>\<tau> x. \<Phi> x) \<longrightarrow> (\<^bold>\<exists> y. G y (\<^bold>\<tau> x. \<Phi> x) \<and> C y)"
 \<comment> \<open>if the being greater than which none can be conceived does not exist in reality,
then  a being exists in the understanding which is greater than the being greater than
which none can be conceived\<close>
and connectivity: "\<^bold>\<forall> x. \<^bold>\<forall> y. G x y \<or> G y x \<or> x \<^bold>= y"
shows "E g" \<comment> \<open>God exists.\<close>

  text \<open>Isabelle can verify the argument in one line with the command \<open>using premise_1 premise_2 connectivity lemma_1 g_def description_theorem_1 by smt\<close>.
But since proofs in Isabelle using \<open>smt\<close> are currently considered impermanent, I instead give Zalta
and Oppenheimer's handwritten proof @{cite "oppenheimer_computationally-discovered_2011"}, p. 337:\<close>  
proof (rule ccontr)
  assume atheism: "\<not> E g"
  from premise_1 and connectivity and lemma_2 have "unique x. \<Phi> x" by simp
  with description_theorem_1 have "\<^bold>\<exists> y. y \<^bold>= (\<^bold>\<tau> x. \<Phi> x)" by simp
  with description_theorem_2 have "\<Phi> (\<^bold>\<tau> x. \<Phi> x)" by simp
  hence god_is_greatest: "\<not>(\<^bold>\<exists> y. G y (\<^bold>\<tau> x.  \<Phi> x) \<and> C y)" by (rule conjE)
  from  atheism and premise_2 and g_def have "(\<^bold>\<exists> y. G y (\<^bold>\<tau> x. \<Phi> x) \<and> C y)" by simp
  with god_is_greatest show False..
qed  
text \<open>Note that neither Oppenheimer and Zalta's proof nor the one line \<open>smt\<close> proof
depend on the negativity constraint or whether any of the non-logical vocabulary is atomic
(though they do depend indirectly on the atomicity of identity).\<close>
  
section \<open>The Prover9 Argument\<close>

text \<open>In the course of verifying the argument using Prover9, Oppenheimer and Zalta 
discovered a simplified version which employs only \<open>premise_2\<close>, but not \<open>premise_1\<close>
or the connectivity of `greater than' @{cite "oppenheimer_computationally-discovered_2011"}.\<close>

theorem
assumes premise_2:  "\<not> E (\<^bold>\<tau> x. \<Phi> x) \<longrightarrow> (\<^bold>\<exists> y. G y (\<^bold>\<tau> x. \<Phi> x) \<and> C y)"
shows "E g" nitpick [user_axioms] oops

text \<open>However, Isabelle not only fails to verify this argument, but finds a counterexample 
using \<open>nitpick\<close>. The reason is that it needs to be specified that `greater than' is atomic, 
in order for \<open>description_theorem_3\<close> to be applicable:\<close>

theorem Prover9Argument:
assumes premise_2:  "\<not> E (\<^bold>\<tau> x. \<Phi> x) \<longrightarrow> (\<^bold>\<exists> y. G y (\<^bold>\<tau> x. \<Phi> x) \<and> C y)"
and G_atomic: "\<And> x. atomic (G x)"
shows "E g"
  text \<open>Once the atomicity of `greater than' is added as a premise, a call to \<open>sledgehammer\<close>
suggests the following two-step proof, which Isabelle verifies easily:\<close>
proof -
  have "C g \<and> (\<forall>i. i = n \<or> \<not> G i g \<or> \<not> C i) \<or> n = g"
    by (metis (lifting, full_types) g_def lemma_1)
  then show ?thesis
    by (metis (lifting) G_atomic g_def negativity_constraint premise_2)
qed
    
text \<open>If provided with all premises, \<open>sledgehammer\<close> still suggests a proof using only
\<open>premise_2\<close>:\<close>
theorem 
assumes connectivity:  "\<^bold>\<forall> x. \<^bold>\<forall> y. G x y \<or> G y x \<or> x \<^bold>= y"
and premise_1:  "\<^bold>\<exists> x. \<Phi> x"
and premise_2:  "\<not> E (\<^bold>\<tau> x. \<Phi> x) \<longrightarrow> (\<^bold>\<exists> y. G y (\<^bold>\<tau> x. \<Phi> x) \<and> C y)"
and G_atomic: "\<And> x. atomic (G x)"
shows "E g"
proof -
  have "\<Phi> g \<or> n = g"
    by (metis (lifting, full_types) g_def lemma_1)
  then show ?thesis
    by (metis (lifting) G_atomic g_def negativity_constraint premise_2)
qed

text \<open>Note that this version of the argument does employ the \<open>negativity_constraint\<close>,
as well as the premise that identity is atomic via \<open>lemma_1\<close>. So although it has less
non-logical premises than the original version of the argument, it has more, and more
controversial, logical premises.\<close>

section \<open>Soundness\<close>

text \<open>Since \<open>premise_1\<close> and the connectivity of `is greater than' are both dispensable, and 
the atomicity of `is greater than' is not especially controversial, the main non-logical premise 
of the argument turns out to be \<open>premise_2\<close>. Note that \<open>premise_2\<close> is entailed
by God's existence:\<close>

theorem
  assumes theism: "E g"
  shows "\<not> E (\<^bold>\<tau> x. \<Phi> x) \<longrightarrow> (\<^bold>\<exists> y. G y (\<^bold>\<tau> x. \<Phi> x) \<and> C y)"
  using g_def theism by auto

text \<open>So under the supposition that `is greater than' is atomic, \<open>premise_2\<close>
is equivalent to God's existence, suggesting an atheist might wish to reject it as question-begging
(see @{cite "oppenheimer_computationally-discovered_2011"}, pp. 348-9 and
@{cite "garbacz_prover9s_2012"} for more detailed discussion of this point).\<close> 

text \<open>However, Ted Parent has pointed out that \<open>premise_2\<close> need not stand on its own,
but may be further supported by the following argument @{cite "parent_prover9_2015"},
 p. 478:\<close>

lemma
assumes premise_3: "\<^bold>\<forall> y. \<^bold>\<forall> z. ((E y \<and> \<not> E z) \<longrightarrow> ((y \<^bold>= (\<^bold>\<tau> x. \<Phi> x) \<or> z = (\<^bold>\<tau> x. \<Phi> x)) \<longrightarrow> y =  (\<^bold>\<tau> x. \<Phi> x)))" and something_exists: "\<^bold>\<exists> x. E x" and god_is_conceivable: "C g" and C_atomic: "atomic C"
shows "\<not> E (\<^bold>\<tau> x. \<Phi> x) \<longrightarrow> (\<^bold>\<exists> y. C y \<and> G y (\<^bold>\<tau> x. \<Phi> x))"
by (metis (no_types, lifting) C_atomic description_theorem_3 g_def god_is_conceivable premise_3 something_exists)

text \<open>But as Parent says, the premise that `exists in the understanding' is atomic is
particularly questionable. If `exists in the understanding' is atomic, then it follows from
\<open>description_theorem_3\<close> that, for example, if the largest  positive integer exists in
the understanding, then something is the largest positive integer. But since `the largest positive
integer' is a grammatical description, there is a case to be made that the largest positive integer
does exist in the understanding, even though nothing is the largest positive integer
@{cite "parent_prover9_2015"}, p. 480-1.\<close>

section \<open>Conclusion\<close>

text \<open>The main difference between Oppenheimer and Zalta's reconstruction of the argument in 
Prover9 and the reconstruction presented here in Isabelle/HOL is that whereas  Prover9 employs 
first-order logic, Isabelle/HOL employs higher-order logic. That means that the Russellian 
\<open>description_axiom\<close> schema can be stated directly in Isabelle/HOL, whereas in Prover9 
it has to be represented indirectly using first-order quantifiers ranging over predicates and
relations @{cite "oppenheimer_computationally-discovered_2011"}, pp. 338-41.\<close>

text \<open>Because of the way Oppenheimer and Zalta carry out this embedding, it is presupposed
in their presentation that all the non-logical predicates which occur in their argument are 
atomic. In contrast, in the presentation in Isabelle/HOL, whenever the assumption that a certain 
predicate is atomic is needed, this has to be made explicit as a premise of the argument. This 
is not a merely practical matter since, as Parent points out, the question of whether `exists 
in the understanding' is an atomic predicate turns out to be crucial.\<close>

text \<open>Abstracting from the peculiarities of different software, a surprising result is that 
whereas every version of the argument requires the premise that identity is atomic, and some
versions require the additional premises that `is greater than' is atomic  and `exists in the
understanding' is atomic, no version of the argument requires the premises that `exists in
reality', or in other words `exists' simpliciter, is atomic. This is in spite of the fact that
 the question of whether `exists' is a genuine  predicate has historically being one of the most
controversial questions raised by Anselm's argument.\<close>

end
  
section \<open>Acknowledgements\<close>

text \<open>I thank Bob Beddor, Christoph Benzmuller, Dana Goswick, Frank Jackson, Paul Oppenheimer, 
Michael Pelczar, Abelard Podgorski, Hsueh Qu, Neil Sinhababu, Weng-Hong Tang, Jennifer Wang, 
Alastair Wilson and an audience at the University of Sydney for comments on this paper.
\<close>
