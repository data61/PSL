(*<*) 
theory LoweOntologicalArgument_6
imports QML
begin

nitpick_params[box=false, user_axioms=true, show_all, expect=genuine, format = 3,  atoms e = a b c d]
sledgehammer_params[verbose=true]
(*>*)
  
subsection \<open>Modified Modal Argument I\<close>
text\<open>\noindent{In the following iterations we want to illustrate an approach in which we start our interpretive endeavor 
with no pre-understanding of the concepts involved.
We start by taking all concepts as primitive without providing any definition
or presupposing any interrelation between them. We see how we gradually improve our understanding of these
concepts in the iterative process of adding and removing axioms and, therefore,
by framing their inferential role in the argument.}\<close>
  
consts Concrete::"e\<Rightarrow>wo"
consts Abstract::"e\<Rightarrow>wo"
consts Necessary::"e\<Rightarrow>wo"
consts Contingent::"e\<Rightarrow>wo"
consts dependence::"e\<Rightarrow>e\<Rightarrow>wo" (infix "dependsOn"(*<*)100(*>*))
consts explanation::"e\<Rightarrow>e\<Rightarrow>wo" (infix "explains"(*<*)100(*>*))
consts Dependent::"e\<Rightarrow>wo"
abbreviation Independent::"e\<Rightarrow>wo" where "Independent x  \<equiv> \<^bold>\<not>(Dependent x)"

text\<open>\noindent{In order to honor the original intention of the author, i.e.  providing a \emph{modal} variant
of St. Anselm's ontological argument, we are required to make a change in Lowe's original formulation.
In this variant we have restated the expressions "necessary abstract" and "necessary concrete"
as "necessarily abstract" and "necessarily concrete" correspondingly.
With this new adverbial reading of the former "necessary" predicate we are no longer talking 
about the concept of \emph{necessariness}, but of \emph{necessity} instead,
so we use the modal box operator (\<open>\<box>\<close>) for its formalization.
Note that in this variant we are not concerned with the interpretation of the original ontological argument anymore.
We are interested, instead, in showing how our method can go beyond simple interpretation
and foster a creative approach to assessing and improving philosophical arguments.}\<close>

text\<open>\noindent{Premise P1 now reads: "God is, by definition, a necessari\emph{ly} concrete being."}\<close>
abbreviation Godlike::"e\<Rightarrow>wo" where "Godlike x \<equiv> \<^bold>\<box>Concrete x"

text\<open>\noindent{Premise P2 reads: "Some necessari\emph{ly} abstract beings exist".
The rest of the premises remains unchanged.}\<close>
axiomatization where
P2: "\<lfloor>\<^bold>\<exists>x. \<^bold>\<box>Abstract x\<rfloor>" and
P3: "\<lfloor>\<^bold>\<forall>x. Abstract x \<^bold>\<rightarrow> Dependent x\<rfloor>" and
P4: "\<lfloor>\<^bold>\<forall>x. Dependent x \<^bold>\<rightarrow> (\<^bold>\<exists>y. Independent y \<^bold>\<and> x dependsOn y)\<rfloor>" and
P5: "\<lfloor>\<^bold>\<not>(\<^bold>\<exists>x. \<^bold>\<exists>y. Contingent y \<^bold>\<and> Necessary x \<^bold>\<and> y explains x)\<rfloor>"

text\<open>\noindent{Without postulating any additional axioms, C10 ("A \emph{necessarily} concrete being exists")
can be falsified by Nitpick.}\<close>
theorem C10: "\<lfloor>\<^bold>\<exists>x. Godlike x\<rfloor>"
  nitpick oops \<comment> \<open>Countermodel found\<close>
    
text\<open>\noindent{An explication of the concepts of necessariness, contingency and explanation is provided below 
by axiomatizing their interrelation to other concepts.
We regard necessariness as being \emph{necessarily abstract} or \emph{necessarily concrete}.
We regard explanation as the inverse relation of dependence, as before.}\<close>    
axiomatization where
  Necessary_expl: "\<lfloor>\<^bold>\<forall>x. Necessary x \<^bold>\<leftrightarrow> (\<^bold>\<box>Abstract x \<^bold>\<or> \<^bold>\<box>Concrete x)\<rfloor>" and
  Contingent_expl: "\<lfloor>\<^bold>\<forall>x. Contingent x \<^bold>\<leftrightarrow> \<^bold>\<not>Necessary x\<rfloor>" and
  Explanation_expl: "\<lfloor>\<^bold>\<forall>x y. y explains x \<^bold>\<leftrightarrow> x dependsOn y\<rfloor>"

text\<open>\noindent{Without any further constraints, C10 becomes falsified by Nitpick.}\<close>
theorem C10: "\<lfloor>\<^bold>\<exists>x. Godlike x\<rfloor>"
  nitpick oops \<comment> \<open>Countermodel found\<close>
    
text\<open>\noindent{We postulate further modal axioms (using the \emph{Sahlqvist correspondence})
and ask Isabelle's \emph{Sledgehammer} for a proof. Sledgehammer is able to
find a proof for C10 which only relies on the modal axiom T (\<open>\<box>\<phi> \<^bold>\<rightarrow> \<phi>\<close>).}\<close>
  
axiomatization where 
 T_axiom: "reflexive R" and \<comment> \<open>@{text "\<box>\<phi> \<rightarrow> \<phi>"}\<close>
 B_axiom: "symmetric R" and \<comment> \<open>@{text "\<phi> \<rightarrow>  \<box>\<diamond>\<phi>"}\<close>
 IV_axiom: "transitive R"   \<comment> \<open>@{text "\<box>\<phi> \<rightarrow> \<box>\<box>\<phi>"}\<close>
 
theorem C10: "\<lfloor>\<^bold>\<exists>x. Godlike x\<rfloor>" using Contingent_expl Explanation_expl
    Necessary_expl P2 P3 P4 P5 T_axiom by metis

(*<*) 
(* We carry out our `sanity checks' as usual.*)
lemma True nitpick[satisfy, user_axioms] oops (* model found: axioms are consistent *)
lemma "\<lfloor>Necessary x\<rfloor>" nitpick[user_axioms] oops (* axioms do not trivialize argument *)
lemma "\<lfloor>\<phi> \<^bold>\<rightarrow> \<^bold>\<box>\<phi>\<rfloor>" nitpick[user_axioms] oops (* counter-model found: modal collapse is not valid *)
    
end
(*>*)
