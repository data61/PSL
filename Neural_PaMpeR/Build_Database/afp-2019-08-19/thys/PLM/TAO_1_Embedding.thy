(*<*)
theory TAO_1_Embedding
imports Main
begin
(*>*)

section\<open>Representation Layer\<close>
text\<open>\label{TAO_Embedding}\<close>

subsection\<open>Primitives\<close>
text\<open>\label{TAO_Embedding_Primitives}\<close>

typedecl i \<comment> \<open>possible worlds\<close>
typedecl j \<comment> \<open>states\<close>

consts dw :: i \<comment> \<open>actual world\<close>
consts dj :: j \<comment> \<open>actual state\<close>

typedecl \<omega> \<comment> \<open>ordinary objects\<close>
typedecl \<sigma> \<comment> \<open>special urelements\<close>
datatype \<upsilon> = \<omega>\<upsilon> \<omega> | \<sigma>\<upsilon> \<sigma> \<comment> \<open>urelements\<close>

subsection\<open>Derived Types\<close>
text\<open>\label{TAO_Embedding_Derived_Types}\<close>

typedef \<o> = "UNIV::(j\<Rightarrow>i\<Rightarrow>bool) set"
  morphisms eval\<o> make\<o> .. \<comment> \<open>truth values\<close>

type_synonym \<Pi>\<^sub>0 = \<o> \<comment> \<open>zero place relations\<close>
typedef \<Pi>\<^sub>1 = "UNIV::(\<upsilon>\<Rightarrow>j\<Rightarrow>i\<Rightarrow>bool) set"
  morphisms eval\<Pi>\<^sub>1 make\<Pi>\<^sub>1 .. \<comment> \<open>one place relations\<close>
typedef \<Pi>\<^sub>2 = "UNIV::(\<upsilon>\<Rightarrow>\<upsilon>\<Rightarrow>j\<Rightarrow>i\<Rightarrow>bool) set"
  morphisms eval\<Pi>\<^sub>2 make\<Pi>\<^sub>2 .. \<comment> \<open>two place relations\<close>
typedef \<Pi>\<^sub>3 = "UNIV::(\<upsilon>\<Rightarrow>\<upsilon>\<Rightarrow>\<upsilon>\<Rightarrow>j\<Rightarrow>i\<Rightarrow>bool) set"
  morphisms eval\<Pi>\<^sub>3 make\<Pi>\<^sub>3 .. \<comment> \<open>three place relations\<close>

type_synonym \<alpha> = "\<Pi>\<^sub>1 set" \<comment> \<open>abstract objects\<close>

datatype \<nu> = \<omega>\<nu> \<omega> | \<alpha>\<nu> \<alpha> \<comment> \<open>individuals\<close>

typedef \<kappa> = "UNIV::(\<nu> option) set"
  morphisms eval\<kappa> make\<kappa> .. \<comment> \<open>individual terms\<close>

setup_lifting type_definition_\<o>
setup_lifting type_definition_\<kappa>
setup_lifting type_definition_\<Pi>\<^sub>1
setup_lifting type_definition_\<Pi>\<^sub>2
setup_lifting type_definition_\<Pi>\<^sub>3

subsection\<open>Individual Terms and Definite Descriptions\<close>
text\<open>\label{TAO_Embedding_IndividualTerms}\<close>

lift_definition \<nu>\<kappa> :: "\<nu>\<Rightarrow>\<kappa>" ("_\<^sup>P" [90] 90) is Some .
lift_definition proper :: "\<kappa>\<Rightarrow>bool" is "(\<noteq>) None" .
lift_definition rep :: "\<kappa>\<Rightarrow>\<nu>" is the .

lift_definition that::"(\<nu>\<Rightarrow>\<o>)\<Rightarrow>\<kappa>" (binder "\<^bold>\<iota>" [8] 9) is
  "\<lambda> \<phi> . if (\<exists>! x . (\<phi> x) dj dw)
         then Some (THE x . (\<phi> x) dj dw)
         else None" .

subsection\<open>Mapping from Individuals to Urelements\<close>
text\<open>\label{TAO_Embedding_AbstractObjectsToSpecialUrelements}\<close>

consts \<alpha>\<sigma> :: "\<alpha>\<Rightarrow>\<sigma>"
axiomatization where \<alpha>\<sigma>_surj: "surj \<alpha>\<sigma>"
definition \<nu>\<upsilon> :: "\<nu>\<Rightarrow>\<upsilon>" where "\<nu>\<upsilon> \<equiv> case_\<nu> \<omega>\<upsilon> (\<sigma>\<upsilon> \<circ> \<alpha>\<sigma>)"

subsection\<open>Exemplification of n-place-Relations.\<close>
text\<open>\label{TAO_Embedding_Exemplification}\<close>

lift_definition exe0::"\<Pi>\<^sub>0\<Rightarrow>\<o>" ("\<lparr>_\<rparr>") is id .
lift_definition exe1::"\<Pi>\<^sub>1\<Rightarrow>\<kappa>\<Rightarrow>\<o>" ("\<lparr>_,_\<rparr>") is
  "\<lambda> F x s w . (proper x) \<and> F (\<nu>\<upsilon> (rep x)) s w" .
lift_definition exe2::"\<Pi>\<^sub>2\<Rightarrow>\<kappa>\<Rightarrow>\<kappa>\<Rightarrow>\<o>" ("\<lparr>_,_,_\<rparr>") is
  "\<lambda> F x y s w . (proper x) \<and> (proper y) \<and>
     F (\<nu>\<upsilon> (rep x)) (\<nu>\<upsilon> (rep y)) s w" .
lift_definition exe3::"\<Pi>\<^sub>3\<Rightarrow>\<kappa>\<Rightarrow>\<kappa>\<Rightarrow>\<kappa>\<Rightarrow>\<o>" ("\<lparr>_,_,_,_\<rparr>") is
"\<lambda> F x y z s w . (proper x) \<and> (proper y) \<and> (proper z) \<and>
   F (\<nu>\<upsilon> (rep x)) (\<nu>\<upsilon> (rep y)) (\<nu>\<upsilon> (rep z)) s w" .

subsection\<open>Encoding\<close>
text\<open>\label{TAO_Embedding_Encoding}\<close>

lift_definition enc :: "\<kappa>\<Rightarrow>\<Pi>\<^sub>1\<Rightarrow>\<o>" ("\<lbrace>_,_\<rbrace>") is
  "\<lambda> x F s w . (proper x) \<and> case_\<nu> (\<lambda> \<omega> . False) (\<lambda> \<alpha> . F \<in> \<alpha>) (rep x)" .

subsection\<open>Connectives and Quantifiers\<close>
text\<open>\label{TAO_Embedding_Connectives}\<close>

consts I_NOT :: "j\<Rightarrow>(i\<Rightarrow>bool)\<Rightarrow>i\<Rightarrow>bool"
consts I_IMPL :: "j\<Rightarrow>(i\<Rightarrow>bool)\<Rightarrow>(i\<Rightarrow>bool)\<Rightarrow>(i\<Rightarrow>bool)"

lift_definition not :: "\<o>\<Rightarrow>\<o>" ("\<^bold>\<not>_" [54] 70) is
  "\<lambda> p s w . s = dj \<and> \<not>p dj w \<or> s \<noteq> dj \<and> (I_NOT s (p s) w)" .
lift_definition impl :: "\<o>\<Rightarrow>\<o>\<Rightarrow>\<o>" (infixl "\<^bold>\<rightarrow>" 51) is
  "\<lambda> p q s w . s = dj \<and> (p dj w \<longrightarrow> q dj w) \<or> s \<noteq> dj \<and> (I_IMPL s (p s) (q s) w)" .
lift_definition forall\<^sub>\<nu> :: "(\<nu>\<Rightarrow>\<o>)\<Rightarrow>\<o>" (binder "\<^bold>\<forall>\<^sub>\<nu>" [8] 9) is
  "\<lambda> \<phi> s w . \<forall> x :: \<nu> . (\<phi> x) s w" .
lift_definition forall\<^sub>0 :: "(\<Pi>\<^sub>0\<Rightarrow>\<o>)\<Rightarrow>\<o>" (binder "\<^bold>\<forall>\<^sub>0" [8] 9) is
  "\<lambda> \<phi> s w . \<forall> x :: \<Pi>\<^sub>0 . (\<phi> x) s w" .
lift_definition forall\<^sub>1 :: "(\<Pi>\<^sub>1\<Rightarrow>\<o>)\<Rightarrow>\<o>" (binder "\<^bold>\<forall>\<^sub>1" [8] 9) is
  "\<lambda> \<phi> s w . \<forall> x :: \<Pi>\<^sub>1  . (\<phi> x) s w" .
lift_definition forall\<^sub>2 :: "(\<Pi>\<^sub>2\<Rightarrow>\<o>)\<Rightarrow>\<o>" (binder "\<^bold>\<forall>\<^sub>2" [8] 9) is
  "\<lambda> \<phi> s w . \<forall> x :: \<Pi>\<^sub>2  . (\<phi> x) s w" .
lift_definition forall\<^sub>3 :: "(\<Pi>\<^sub>3\<Rightarrow>\<o>)\<Rightarrow>\<o>" (binder "\<^bold>\<forall>\<^sub>3" [8] 9) is
  "\<lambda> \<phi> s w . \<forall> x :: \<Pi>\<^sub>3  . (\<phi> x) s w" .
lift_definition forall\<^sub>\<o> :: "(\<o>\<Rightarrow>\<o>)\<Rightarrow>\<o>" (binder "\<^bold>\<forall>\<^sub>\<o>" [8] 9) is
  "\<lambda> \<phi> s w . \<forall> x :: \<o>  . (\<phi> x) s w" .
lift_definition box :: "\<o>\<Rightarrow>\<o>" ("\<^bold>\<box>_" [62] 63) is
  "\<lambda> p s w . \<forall> v . p s v" .
lift_definition actual :: "\<o>\<Rightarrow>\<o>" ("\<^bold>\<A>_" [64] 65) is
  "\<lambda> p s w . p s dw" .

text\<open>
\begin{remark}
  The connectives behave classically if evaluated for the actual state @{term "dj"},
  whereas their behavior is governed by uninterpreted constants for any
  other state.
\end{remark}
\<close>

subsection\<open>Lambda Expressions\<close>
text\<open>\label{TAO_Embedding_Lambda}\<close>

text\<open>
\begin{remark}
  Lambda expressions have to convert maps from individuals to propositions to
  relations that are represented by maps from urelements to truth values.
\end{remark}
\<close>

lift_definition lambdabinder0 :: "\<o>\<Rightarrow>\<Pi>\<^sub>0" ("\<^bold>\<lambda>\<^sup>0") is id .
lift_definition lambdabinder1 :: "(\<nu>\<Rightarrow>\<o>)\<Rightarrow>\<Pi>\<^sub>1" (binder "\<^bold>\<lambda>" [8] 9) is
  "\<lambda> \<phi> u s w . \<exists> x . \<nu>\<upsilon> x = u \<and> \<phi> x s w" .
lift_definition lambdabinder2 :: "(\<nu>\<Rightarrow>\<nu>\<Rightarrow>\<o>)\<Rightarrow>\<Pi>\<^sub>2" ("\<^bold>\<lambda>\<^sup>2") is
  "\<lambda> \<phi> u v s w . \<exists> x y . \<nu>\<upsilon> x = u \<and> \<nu>\<upsilon> y = v \<and> \<phi> x y s w" .
lift_definition lambdabinder3 :: "(\<nu>\<Rightarrow>\<nu>\<Rightarrow>\<nu>\<Rightarrow>\<o>)\<Rightarrow>\<Pi>\<^sub>3" ("\<^bold>\<lambda>\<^sup>3") is
  "\<lambda> \<phi> u v r s w . \<exists> x y z . \<nu>\<upsilon> x = u \<and> \<nu>\<upsilon> y = v \<and> \<nu>\<upsilon> z = r \<and> \<phi> x y z s w" .

subsection\<open>Proper Maps\<close>
text\<open>\label{TAO_Embedding_Proper}\<close>

text\<open>
\begin{remark}
  The embedding introduces the notion of \emph{proper} maps from
  individual terms to propositions.

  Such a map is proper if and only if for all proper individual terms its truth evaluation in the
  actual state only depends on the urelements corresponding to the individuals the terms denote.

  Proper maps are exactly those maps that - when used as matrix of a lambda-expression - unconditionally
  allow beta-reduction.
\end{remark}
\<close>

lift_definition IsProperInX :: "(\<kappa>\<Rightarrow>\<o>)\<Rightarrow>bool" is
  "\<lambda> \<phi> . \<forall> x v . (\<exists> a . \<nu>\<upsilon> a = \<nu>\<upsilon> x \<and> (\<phi> (a\<^sup>P) dj v)) = (\<phi> (x\<^sup>P) dj v)" .
lift_definition IsProperInXY :: "(\<kappa>\<Rightarrow>\<kappa>\<Rightarrow>\<o>)\<Rightarrow>bool" is
  "\<lambda> \<phi> . \<forall> x y v . (\<exists> a b . \<nu>\<upsilon> a = \<nu>\<upsilon> x \<and> \<nu>\<upsilon> b = \<nu>\<upsilon> y
                    \<and> (\<phi> (a\<^sup>P) (b\<^sup>P) dj v)) = (\<phi> (x\<^sup>P) (y\<^sup>P) dj v)" .
lift_definition IsProperInXYZ :: "(\<kappa>\<Rightarrow>\<kappa>\<Rightarrow>\<kappa>\<Rightarrow>\<o>)\<Rightarrow>bool" is
  "\<lambda> \<phi> . \<forall> x y z v . (\<exists> a b c . \<nu>\<upsilon> a = \<nu>\<upsilon> x \<and> \<nu>\<upsilon> b = \<nu>\<upsilon> y \<and> \<nu>\<upsilon> c = \<nu>\<upsilon> z
                      \<and> (\<phi> (a\<^sup>P) (b\<^sup>P) (c\<^sup>P) dj v)) = (\<phi> (x\<^sup>P) (y\<^sup>P) (z\<^sup>P) dj v)" .


subsection\<open>Validity\<close> 
text\<open>\label{TAO_Embedding_Validity}\<close>

lift_definition valid_in :: "i\<Rightarrow>\<o>\<Rightarrow>bool" (infixl "\<Turnstile>" 5) is
  "\<lambda> v \<phi> . \<phi> dj v" .

text\<open>
\begin{remark}
  A formula is considered semantically valid for a possible world,
  if it evaluates to @{term "True"} for the actual state @{term "dj"}
  and the given possible world.
\end{remark}
\<close>

subsection\<open>Concreteness\<close>
text\<open>\label{TAO_Embedding_Concreteness}\<close>

consts ConcreteInWorld :: "\<omega>\<Rightarrow>i\<Rightarrow>bool"

abbreviation (input) OrdinaryObjectsPossiblyConcrete where
  "OrdinaryObjectsPossiblyConcrete \<equiv> \<forall> x . \<exists> v . ConcreteInWorld x v"
abbreviation (input) PossiblyContingentObjectExists where
  "PossiblyContingentObjectExists \<equiv> \<exists> x v . ConcreteInWorld x v
                                        \<and> (\<exists> w . \<not> ConcreteInWorld x w)"
abbreviation (input) PossiblyNoContingentObjectExists where
  "PossiblyNoContingentObjectExists \<equiv> \<exists> w . \<forall> x . ConcreteInWorld x w
                                        \<longrightarrow> (\<forall> v . ConcreteInWorld x v)"
axiomatization where
  OrdinaryObjectsPossiblyConcreteAxiom:
    "OrdinaryObjectsPossiblyConcrete"
  and PossiblyContingentObjectExistsAxiom:
    "PossiblyContingentObjectExists"
  and PossiblyNoContingentObjectExistsAxiom:
    "PossiblyNoContingentObjectExists"

text\<open>
\begin{remark}
  Care has to be taken that the defined notion of concreteness
  coincides with the meta-logical distinction between
  abstract objects and ordinary objects. Furthermore the axioms about
  concreteness have to be satisfied. This is achieved by introducing an
  uninterpreted constant @{term "ConcreteInWorld"} that determines whether
  an ordinary object is concrete in a given possible world. This constant is
  axiomatized, such that all ordinary objects are possibly concrete, contingent
  objects possibly exist and possibly no contingent objects exist.
\end{remark}
\<close>


lift_definition Concrete::"\<Pi>\<^sub>1" ("E!") is
  "\<lambda> u s w . case u of \<omega>\<upsilon> x \<Rightarrow> ConcreteInWorld x w | _ \<Rightarrow> False" .

text\<open>
\begin{remark}
  Concreteness of ordinary objects is now defined using this
  axiomatized uninterpreted constant. Abstract objects on the other
  hand are never concrete.
\end{remark}
\<close>

subsection\<open>Collection of Meta-Definitions\<close>
text\<open>\label{TAO_Embedding_meta_defs}\<close>

named_theorems meta_defs

declare not_def[meta_defs] impl_def[meta_defs] forall\<^sub>\<nu>_def[meta_defs]
        forall\<^sub>0_def[meta_defs] forall\<^sub>1_def[meta_defs]
        forall\<^sub>2_def[meta_defs] forall\<^sub>3_def[meta_defs] forall\<^sub>\<o>_def[meta_defs]
        box_def[meta_defs] actual_def[meta_defs] that_def[meta_defs]
        lambdabinder0_def[meta_defs] lambdabinder1_def[meta_defs]
        lambdabinder2_def[meta_defs] lambdabinder3_def[meta_defs]
        exe0_def[meta_defs] exe1_def[meta_defs] exe2_def[meta_defs]
        exe3_def[meta_defs] enc_def[meta_defs] inv_def[meta_defs]
        that_def[meta_defs] valid_in_def[meta_defs] Concrete_def[meta_defs]

declare [[smt_solver = cvc4]]
declare [[simp_depth_limit = 10]] (* prevent the simplifier from running forever *)
declare [[unify_search_bound = 40]] (* prevent unification bound errors *)

subsection\<open>Auxiliary Lemmata\<close>
text\<open>\label{TAO_Embedding_Aux}\<close>
  
named_theorems meta_aux

declare make\<kappa>_inverse[meta_aux] eval\<kappa>_inverse[meta_aux]
        make\<o>_inverse[meta_aux] eval\<o>_inverse[meta_aux]
        make\<Pi>\<^sub>1_inverse[meta_aux] eval\<Pi>\<^sub>1_inverse[meta_aux]
        make\<Pi>\<^sub>2_inverse[meta_aux] eval\<Pi>\<^sub>2_inverse[meta_aux]
        make\<Pi>\<^sub>3_inverse[meta_aux] eval\<Pi>\<^sub>3_inverse[meta_aux]
lemma \<nu>\<upsilon>_\<omega>\<nu>_is_\<omega>\<upsilon>[meta_aux]: "\<nu>\<upsilon> (\<omega>\<nu> x) = \<omega>\<upsilon> x" by (simp add: \<nu>\<upsilon>_def)
lemma rep_proper_id[meta_aux]: "rep (x\<^sup>P) = x"
  by (simp add: meta_aux \<nu>\<kappa>_def rep_def)
lemma \<nu>\<kappa>_proper[meta_aux]: "proper (x\<^sup>P)"
  by (simp add: meta_aux \<nu>\<kappa>_def proper_def)
lemma no_\<alpha>\<omega>[meta_aux]: "\<not>(\<nu>\<upsilon> (\<alpha>\<nu> x) = \<omega>\<upsilon> y)" by (simp add: \<nu>\<upsilon>_def)
lemma no_\<sigma>\<omega>[meta_aux]: "\<not>(\<sigma>\<upsilon> x = \<omega>\<upsilon> y)" by blast
lemma \<nu>\<upsilon>_surj[meta_aux]: "surj \<nu>\<upsilon>"
  using \<alpha>\<sigma>_surj unfolding \<nu>\<upsilon>_def surj_def
  by (metis \<nu>.simps(5) \<nu>.simps(6) \<upsilon>.exhaust comp_apply)
lemma lambda\<Pi>\<^sub>1_aux[meta_aux]:
  "make\<Pi>\<^sub>1 (\<lambda>u s w. \<exists>x. \<nu>\<upsilon> x = u \<and> eval\<Pi>\<^sub>1 F (\<nu>\<upsilon> x) s w) = F"
  proof -
    have "\<And> u s w \<phi> . (\<exists> x . \<nu>\<upsilon> x = u \<and> \<phi> (\<nu>\<upsilon> x) (s::j) (w::i)) \<longleftrightarrow> \<phi> u s w"
      using \<nu>\<upsilon>_surj unfolding surj_def by metis
    thus ?thesis apply transfer by simp
  qed
lemma lambda\<Pi>\<^sub>2_aux[meta_aux]:
  "make\<Pi>\<^sub>2 (\<lambda>u v s w. \<exists>x . \<nu>\<upsilon> x = u \<and> (\<exists> y . \<nu>\<upsilon> y = v \<and> eval\<Pi>\<^sub>2 F (\<nu>\<upsilon> x) (\<nu>\<upsilon> y) s w)) = F"
  proof -
    have "\<And> u v (s ::j) (w::i) \<phi> .
      (\<exists> x . \<nu>\<upsilon> x = u \<and> (\<exists> y . \<nu>\<upsilon> y = v \<and> \<phi> (\<nu>\<upsilon> x) (\<nu>\<upsilon> y) s w))
      \<longleftrightarrow> \<phi> u v s w"
      using \<nu>\<upsilon>_surj unfolding surj_def by metis
    thus ?thesis apply transfer by simp
  qed
lemma lambda\<Pi>\<^sub>3_aux[meta_aux]:
  "make\<Pi>\<^sub>3 (\<lambda>u v r s w. \<exists>x. \<nu>\<upsilon> x = u \<and> (\<exists>y. \<nu>\<upsilon> y = v \<and>
   (\<exists>z. \<nu>\<upsilon> z = r \<and> eval\<Pi>\<^sub>3 F (\<nu>\<upsilon> x) (\<nu>\<upsilon> y) (\<nu>\<upsilon> z) s w))) = F"
  proof -
    have "\<And> u v r (s::j) (w::i) \<phi> . \<exists>x. \<nu>\<upsilon> x = u \<and> (\<exists>y. \<nu>\<upsilon> y = v
          \<and> (\<exists>z. \<nu>\<upsilon> z = r \<and> \<phi> (\<nu>\<upsilon> x) (\<nu>\<upsilon> y) (\<nu>\<upsilon> z) s w)) = \<phi> u v r s w"
      using \<nu>\<upsilon>_surj unfolding surj_def by metis
    thus ?thesis apply transfer apply (rule ext)+ by metis
  qed
(*<*)
end
(*>*)
