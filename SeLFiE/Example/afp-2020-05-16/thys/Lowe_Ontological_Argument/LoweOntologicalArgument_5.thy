(*<*) 
theory LoweOntologicalArgument_5
imports QML
begin

nitpick_params[box=false, user_axioms=true, show_all, expect=genuine, format = 3,  atoms e = a b c d]
sledgehammer_params[verbose=true]
(*>*)
  
subsection \<open>Arriving at a Non-Modal Argument\<close>
  
text\<open>\noindent{A new simplified emendation of Lowe's argument is obtained after abandoning the concept of existence
and redefining necessariness and contingency accordingly. As we will see, this variant
is actually non-modal and can be easily formalized in first-order predicate logic.}\<close>
  
text\<open>\noindent{A more literal reading of Lowe's article has suggested a simplified formalization, in which necessariness
and contingency are taken as complementary predicates. According to this, our domain of discourse becomes
divided in four main categories, as exemplified in the table below:\footnote{
As Lowe explains in the article, "there is no logical restriction on combinations of the properties
involved in the concrete/abstract and the necessary/contingent distinctions.
In principle, then, we can have contingent concrete beings, contingent abstract beings,
necessary concrete beings, and necessary abstract beings."}
}\<close>
text\<open>\noindent{
\begin{center}
  \begin{tabular}{ l | c | r | }   
     & Abstract & Concrete \\ \hline
    Necessary & Numbers & God \\ \hline
    Contingent & Fiction & Stuff \\
    \hline
  \end{tabular}
\end{center}
}\<close>
consts Necessary::"e\<Rightarrow>wo"
abbreviation Contingent::"e\<Rightarrow>wo" where "Contingent x \<equiv> \<^bold>\<not>(Necessary x)"
    
consts Concrete::"e\<Rightarrow>wo"
abbreviation Abstract::"e\<Rightarrow>wo" where "Abstract x \<equiv>  \<^bold>\<not>(Concrete x)"
  
abbreviation Godlike::"e\<Rightarrow>w\<Rightarrow>bool" where "Godlike x\<equiv> Necessary x \<^bold>\<and> Concrete x" 
        
consts dependence::"e\<Rightarrow>e\<Rightarrow>wo" (infix "dependsOn"(*<*)100(*>*))
abbreviation explanation::"(e\<Rightarrow>e\<Rightarrow>wo)" (infix "explains"(*<*)100(*>*))
  where "y explains x \<equiv> x dependsOn y"

text\<open>\noindent{As shown below, we can even define the "dependent" predicate as \emph{primitive},
i.e. bearing no relation to ontological dependence, and still be able to validate the argument.
Being "independent" is defined as the negation of being "dependent", as before.}\<close>
consts Dependent::"e\<Rightarrow>wo"
abbreviation Independent::"e\<Rightarrow>wo" where "Independent x  \<equiv> \<^bold>\<not>(Dependent x)"
  
text\<open>\noindent{By taking, once again, metaphysical explanation as the inverse relation of ontological dependence
and by assuming premises P2 to P5 we can prove conclusion C10.}\<close>
  
axiomatization where
P2: "\<lfloor>\<^bold>\<exists>x. Necessary x \<^bold>\<and> Abstract x\<rfloor>" and
P3: "\<lfloor>\<^bold>\<forall>x. Abstract x \<^bold>\<rightarrow> Dependent x\<rfloor>" and
P4: "\<lfloor>\<^bold>\<forall>x. Dependent x \<^bold>\<rightarrow> (\<^bold>\<exists>y. Independent y \<^bold>\<and> x dependsOn y)\<rfloor>" and
P5: "\<lfloor>\<^bold>\<not>(\<^bold>\<exists>x. \<^bold>\<exists>y. Contingent y \<^bold>\<and> Necessary x \<^bold>\<and> y explains x)\<rfloor>"

theorem C10: "\<lfloor>\<^bold>\<exists>x. Godlike x\<rfloor>" using  P2 P3 P4 P5 by blast
    
text\<open>\noindent{Note that, in the axioms above, all actualist quantifiers have been changed into non-guarded quantifiers,
following the elimination of the concept of existence from our argument: Our quantifiers range over \emph{all}
beings, because all beings exist. Also note that all modal operators have disappeared;
thus, this new variant is directly formalizable in classical first-order logic.}\<close>

(*<*) 
(* We carry out our `sanity checks' as usual.*)
lemma True nitpick[satisfy, user_axioms] oops (* model found: axioms are consistent *)
lemma "\<lfloor>Necessary x\<rfloor>" nitpick[user_axioms] oops (* counter-model found: axioms do not trivialize argument *)
lemma "\<lfloor>\<phi> \<^bold>\<rightarrow> \<^bold>\<box>\<phi>\<rfloor>" nitpick[user_axioms] oops (* counter-model found: modal collapse is not valid *)
    
end
(*>*)
