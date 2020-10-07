(*<*) 
theory LoweOntologicalArgument_7
imports QML
begin

nitpick_params[box=false, user_axioms=true, show_all, expect=genuine, format = 3,  atoms e = a b c d]
sledgehammer_params[verbose=true]
  
consts Concrete::"e\<Rightarrow>wo"
consts Abstract::"e\<Rightarrow>wo"
consts Necessary::"e\<Rightarrow>wo"
consts Contingent::"e\<Rightarrow>wo"
consts dependence::"e\<Rightarrow>e\<Rightarrow>wo" (infix "dependsOn"(*<*)100(*>*))
consts explanation::"e\<Rightarrow>e\<Rightarrow>wo" (infix "explains"(*<*)100(*>*))
consts Dependent::"e\<Rightarrow>wo"
abbreviation Independent::"e\<Rightarrow>wo" where "Independent x  \<equiv> \<^bold>\<not>(Dependent x)"

abbreviation Godlike::"e\<Rightarrow>wo" where "Godlike x \<equiv> \<^bold>\<box>Concrete x"

axiomatization where
P2: "\<lfloor>\<^bold>\<exists>x. \<^bold>\<box>Abstract x\<rfloor>" and
P3: "\<lfloor>\<^bold>\<forall>x. Abstract x \<^bold>\<rightarrow> Dependent x\<rfloor>" and
P4: "\<lfloor>\<^bold>\<forall>x. Dependent x \<^bold>\<rightarrow> (\<^bold>\<exists>y. Independent y \<^bold>\<and> x dependsOn y)\<rfloor>" and
P5: "\<lfloor>\<^bold>\<not>(\<^bold>\<exists>x. \<^bold>\<exists>y. Contingent y \<^bold>\<and> Necessary x \<^bold>\<and> y explains x)\<rfloor>"
(*>*)

subsection \<open>Modified Modal Argument II\<close>
  
text\<open>\noindent{We start again our interpretive process with no pre-understanding of the
concepts involved (by taking them as primitive).
We then see how their inferential role gradually becomes apparent in the process
of axiomatizing further constraints. We follow on with the adverbial reading of the expression "necessary"
as in the previous version.}\<close>

text\<open>\noindent{Another explication of the concepts of necessariness and contingency is provided below.
We think that this explication, in comparison to the previous one, better fits our intuitive
understanding of necessariness.
We now regard necessariness as being \emph{necessarily} abstract or concrete, and
explanation as the inverse relation of dependence, as before.}\<close>    
axiomatization where
Necessary_expl: "\<lfloor>\<^bold>\<forall>x. Necessary x \<^bold>\<leftrightarrow> \<^bold>\<box>(Abstract x \<^bold>\<or> Concrete x)\<rfloor>" and
Contingent_expl: "\<lfloor>\<^bold>\<forall>x. Contingent x \<^bold>\<leftrightarrow> \<^bold>\<not>Necessary x\<rfloor>" and
Explanation_expl: "\<lfloor>\<^bold>\<forall>x y. y explains x \<^bold>\<leftrightarrow> x dependsOn y\<rfloor>"

text\<open>\noindent{These constraints are, however, not enough to ensure the argument's validity as confirmed by Nitpick.}\<close>
theorem C10: "\<lfloor>\<^bold>\<exists>x. Godlike x\<rfloor>"
  nitpick oops \<comment> \<open>Countermodel found\<close>
    
text\<open>\noindent{After some iterations, we see that, by giving a more satisfactory explication of the concept
of necesariness, we are also required to assume the essentiality of abstractness
(as we did in a former iteration) and to restrict the accessibility relation by enforcing its symmetry
(i.e. assuming the modal axiom \emph{B}).}\<close>
axiomatization where
  abstractness_essential: "\<lfloor>\<^bold>\<forall>x. Abstract x \<^bold>\<rightarrow> \<^bold>\<box>Abstract x\<rfloor>" and
  B_Axiom:  "symmetric R"

theorem C10: "\<lfloor>\<^bold>\<exists>x. Godlike x\<rfloor>" using Contingent_expl Explanation_expl
    Necessary_expl P2 P3 P4 P5 abstractness_essential B_Axiom by metis
    
text\<open>\noindent{We have chosen to terminate, after this series of iterations, our interpretive endeavor.
In each of the previous versions we have illustrated how our understanding of the concepts of
necessity/contingency, explanation/dependence and abstractness/concreteness has gradually evolved
thanks to the kind of iterative hypothetico-deductive method which has been made possible
by the real-time feedback provided by Isabelle's automated proving tools.}\<close>

(*<*) 
(* We carry out our `sanity checks' as usual.*)
lemma True nitpick[satisfy, user_axioms] oops (* model found: axioms are consistent *)
lemma "\<lfloor>\<^bold>\<forall>x. Necessary x\<rfloor>" nitpick[user_axioms] oops \<comment> \<open>counter-model found: argument is not trivial\<close>
lemma "\<lfloor>\<phi> \<^bold>\<rightarrow> \<^bold>\<box>\<phi>\<rfloor>" nitpick[user_axioms] oops (* counter-model found: modal collapse is not valid *)
    
end
(*>*)
