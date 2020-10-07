(*<*) 
theory LoweOntologicalArgument_3
imports QML
begin

nitpick_params[box=false, user_axioms=true, show_all, expect=genuine, format = 3,  atoms e = a b c d]
sledgehammer_params[verbose=true]
  
consts isActualized::"e\<Rightarrow>wo" (infix "actualizedAt" 70)
  
abbreviation forallAct::"(e\<Rightarrow>wo)\<Rightarrow>wo" ("\<^bold>\<forall>\<^sup>A")
  where "\<^bold>\<forall>\<^sup>A\<Phi> \<equiv> \<lambda>w.\<forall>x. (x actualizedAt w)\<longrightarrow>(\<Phi> x w)"
abbreviation existsAct::"(e\<Rightarrow>wo)\<Rightarrow>wo" ("\<^bold>\<exists>\<^sup>A")
  where "\<^bold>\<exists>\<^sup>A\<Phi> \<equiv> \<lambda>w.\<exists>x. (x actualizedAt w) \<and> (\<Phi> x w)"
abbreviation mforallActB::"(e\<Rightarrow>wo)\<Rightarrow>wo" (binder"\<^bold>\<forall>\<^sup>A"[8]9)
  where "\<^bold>\<forall>\<^sup>Ax. (\<phi> x) \<equiv> \<^bold>\<forall>\<^sup>A\<phi>"
abbreviation mexistsActB::"(e\<Rightarrow>wo)\<Rightarrow>wo" (binder"\<^bold>\<exists>\<^sup>A"[8]9)
  where "\<^bold>\<exists>\<^sup>Ax. (\<phi> x) \<equiv> \<^bold>\<exists>\<^sup>A\<phi>"
  
definition Existence::"e\<Rightarrow>wo" ("E!") where "E! x  \<equiv> \<^bold>\<exists>\<^sup>Ay. y\<^bold>\<approx>x"    
definition Necessary::"e\<Rightarrow>wo" where "Necessary x \<equiv>  \<^bold>\<box>E! x"
definition Contingent::"e\<Rightarrow>wo" where "Contingent x \<equiv>  \<^bold>\<diamond>E! x \<^bold>\<and> \<^bold>\<not>(Necessary x)"  
  
consts Concrete::"e\<Rightarrow>wo"
abbreviation Abstract::"e\<Rightarrow>wo" where "Abstract x \<equiv>  \<^bold>\<not>(Concrete x)"  
  
abbreviation Godlike::"e\<Rightarrow>wo"  where "Godlike x \<equiv> Necessary x \<^bold>\<and> Concrete x"
  
consts dependence::"e\<Rightarrow>e\<Rightarrow>wo" (infix "dependsOn" 100)
definition Dependent::"e\<Rightarrow>wo" where "Dependent x \<equiv> \<^bold>\<exists>\<^sup>Ay. x dependsOn y"
abbreviation Independent::"e\<Rightarrow>wo" where "Independent x  \<equiv> \<^bold>\<not>(Dependent x)"  
  
consts explanation::"e\<Rightarrow>e\<Rightarrow>wo" (infix "explains" 100)
definition Explained::"e\<Rightarrow>wo" where "Explained x \<equiv> \<^bold>\<exists>\<^sup>Ay. y explains x"
  
axiomatization where
  P2: "\<lfloor>\<^bold>\<exists>\<^sup>Ax. Necessary x \<^bold>\<and> Abstract x\<rfloor>" and
  P3: "\<lfloor>\<^bold>\<forall>\<^sup>Ax. Abstract x \<^bold>\<rightarrow> Dependent x\<rfloor>" and
  P4: "\<lfloor>\<^bold>\<forall>\<^sup>Ax. Dependent x \<^bold>\<rightarrow> (\<^bold>\<exists>\<^sup>Ay. Independent y \<^bold>\<and> x dependsOn y)\<rfloor>" and
  P5: "\<lfloor>\<^bold>\<not>(\<^bold>\<exists>\<^sup>Ax. \<^bold>\<exists>\<^sup>Ay. Contingent y \<^bold>\<and> Necessary x \<^bold>\<and> y explains x)\<rfloor>"
(*>*)
  
subsection \<open>Validating the Argument II\<close>
  
text\<open>\noindent{We present a slightly simplified version of the original argument (without the implicit premises stated in
the previous version). In this variant premises P1 to P5 remain unchanged
and none of the last three premises proposed by Lowe (P6 to P8) show up anymore.
Those last premises have been introduced in order to interrelate the concepts of explanation and dependence
in such a way that they play somewhat opposite roles.
Now we want to go all the way and simply assume that they are inverse relations,
for we want to understand how the interrelation of these two concepts affects the validity of the argument.}\<close>

axiomatization where  
  dep_expl_inverse: "\<lfloor>\<^bold>\<forall>x y. y explains x \<^bold>\<leftrightarrow> x dependsOn y\<rfloor>"

text\<open>\noindent{We proceed to prove the relevant partial conclusions.}\<close>
theorem C1:  "\<lfloor>\<^bold>\<forall>\<^sup>Ax. Abstract x \<^bold>\<rightarrow> (\<^bold>\<exists>y. Concrete y \<^bold>\<and> x dependsOn y)\<rfloor>"
  using P3 P4 by blast
    
theorem C5: "\<lfloor>\<^bold>\<exists>\<^sup>Ax. Concrete x\<rfloor>"
  using P2 P3 P4 by blast
    
theorem C7: "\<lfloor>\<^bold>\<forall>\<^sup>Ax. (Necessary x \<^bold>\<and> Abstract x) \<^bold>\<rightarrow> Explained x\<rfloor>"
  using Explained_def P3 P4 dep_expl_inverse by meson
    
text\<open>\noindent{But the final conclusion C10 is still countersatisfiable, as shown by Nitpick:}\<close>
theorem C10:  "\<lfloor>\<^bold>\<exists>\<^sup>Ax. Godlike x\<rfloor>"
  nitpick[user_axioms] oops \<comment> \<open>Countermodel found\<close>

text\<open>\noindent{Next, we try assuming a stronger modal logic. We do this by postulating further axioms
using the \emph{Sahlqvist correspondence} and asking Sledgehammer to find a proof.
Sledgehammer is in fact able to find a proof for C10 which only relies on the modal axiom \emph{T}
(\<open>\<box>\<phi> \<^bold>\<rightarrow> \<phi>\<close>).}\<close>    
axiomatization where 
 T_axiom: "reflexive R" and \<comment> \<open>@{text "\<box>\<phi> \<rightarrow> \<phi>"}\<close>
 B_axiom: "symmetric R" and \<comment> \<open>@{text "\<phi> \<rightarrow>  \<box>\<diamond>\<phi>"}\<close>
 IV_axiom: "transitive R"   \<comment> \<open>@{text "\<box>\<phi> \<rightarrow> \<box>\<box>\<phi>"}\<close>

theorem C10: "\<lfloor>\<^bold>\<exists>\<^sup>Ax. Godlike x\<rfloor>" using Contingent_def Existence_def
     P2 P3 P4 P5 dep_expl_inverse T_axiom by meson
  
text\<open>\noindent{In this series of iterations we have verified a modified version of the original argument by Lowe. 
Our understanding of the concepts of \emph{ontological dependence} and \emph{metaphysical explanation}
have changed after the introduction of an additional axiom constraining both:
they are now inverse relations.
Still, we want to carry on with our iterative process in order to further illuminate the meaning
of the concepts involved in this argument.}\<close>
    
(*<*) 
(* We carry out our `sanity checks' as usual.*)
lemma True nitpick[satisfy, user_axioms] oops (* model found: axioms are consistent *)
lemma "\<lfloor>Necessary x\<rfloor>" nitpick[user_axioms] oops (* counter-model found: axioms do not trivialize argument *)
lemma "\<lfloor>\<phi> \<^bold>\<rightarrow> \<^bold>\<box>\<phi>\<rfloor>" nitpick[user_axioms] oops (* counter-model found: modal collapse is not valid *)
    
end
(*>*)
