(*<*) 
theory LoweOntologicalArgument_2
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
  P5: "\<lfloor>\<^bold>\<not>(\<^bold>\<exists>\<^sup>Ax. \<^bold>\<exists>\<^sup>Ay. Contingent y \<^bold>\<and> Necessary x \<^bold>\<and> y explains x)\<rfloor>" and
  P6: "\<lfloor>\<^bold>\<forall>x. Dependent x \<^bold>\<rightarrow> Explained x\<rfloor>" and
  P7: "\<lfloor>\<^bold>\<forall>x. Dependent x \<^bold>\<rightarrow> \<^bold>\<not>(x explains x)\<rfloor>" and
  P8:  "\<lfloor>\<^bold>\<forall>x y. y explains x \<^bold>\<rightarrow> x dependsOn y\<rfloor>"
  
theorem C1:  "\<lfloor>\<^bold>\<forall>\<^sup>Ax. Abstract x \<^bold>\<rightarrow> (\<^bold>\<exists>y. Concrete y \<^bold>\<and> x dependsOn y)\<rfloor>"  using P3 P4 by blast
theorem C5: "\<lfloor>\<^bold>\<exists>\<^sup>Ax. Concrete x\<rfloor>" using P2 P3 P4 by blast
theorem C7: "\<lfloor>\<^bold>\<forall>\<^sup>Ax. (Necessary x \<^bold>\<and> Abstract x) \<^bold>\<rightarrow> Explained x\<rfloor>"  using P3 P6 by blast
theorem C10:  "\<lfloor>\<^bold>\<exists>\<^sup>Ax. Godlike x\<rfloor>" nitpick[user_axioms]  oops
(*>*) 
    
subsection \<open>Validating the Argument I\<close>
text\<open>\noindent{By examining the countermodel found by Nitpick for C10 we can see that some necessary beings that
are abstract in the actual world may indeed be concrete in other accessible worlds. Lowe had previously
presented numbers as an example of such necessary abstract beings. It can be argued that numbers, while
existing necessarily, can never be concrete in any possible world, so we add the restriction
of abstractness being an essential property, i.e. a locally rigid predicate.
}\<close>
axiomatization where
  abstractness_essential: "\<lfloor>\<^bold>\<forall>x. Abstract x \<^bold>\<rightarrow> \<^bold>\<box>Abstract x\<rfloor>"

theorem C10:  "\<lfloor>\<^bold>\<exists>\<^sup>Ax. Godlike x\<rfloor>"
  nitpick[user_axioms] oops \<comment> \<open>Countermodel found\<close>
    
text\<open>\noindent{As Nitpick shows us, the former restriction is not enough to prove C10.
We try postulating further restrictions on the accessibility relation \emph{R} which, taken together,
would amount to it being an equivalence relation. Following the \emph{Sahlqvist correspondence}, this
would make for a modal logic \emph{S5}, and our abstractness property would consequently
become a (globally) rigid predicate.}\<close>
    
axiomatization where 
 T_axiom: "reflexive R" and \<comment> \<open>@{text "\<box>\<phi> \<rightarrow> \<phi>"}\<close>
 B_axiom: "symmetric R" and \<comment> \<open>@{text "\<phi> \<rightarrow>  \<box>\<diamond>\<phi>"}\<close>
 IV_axiom: "transitive R"   \<comment> \<open>@{text "\<box>\<phi> \<rightarrow> \<box>\<box>\<phi>"}\<close>
 
theorem C10:  "\<lfloor>\<^bold>\<exists>\<^sup>Ax. Godlike x\<rfloor>"
  nitpick[user_axioms] oops \<comment> \<open>Countermodel found\<close>

text\<open>\noindent{By examining the new countermodel found by Nitpick we notice that at some worlds there are  
non-existent concrete beings. We want to disallow this possibility, so we make concreteness
an existence-entailing property.}\<close>    
    
axiomatization where concrete_exist: "\<lfloor>\<^bold>\<forall>x. Concrete x \<^bold>\<rightarrow> E! x\<rfloor>"

text\<open>\noindent{We carry out the usual `sanity checks' to make sure the argument has not become trivialized.\footnote{
These checks are being carried out after postulating axioms for every iteration,
so we won't mention them anymore.}}\<close>  
lemma True
  nitpick[satisfy, user_axioms] oops \<comment> \<open>Model found: axioms are consistent\<close>
lemma "\<lfloor>\<^bold>\<forall>x. E! x\<rfloor>"
  nitpick[user_axioms] oops \<comment> \<open>Countermodel found: necessitism is not valid\<close>
lemma "\<lfloor>\<phi> \<^bold>\<rightarrow> \<^bold>\<box>\<phi>\<rfloor>"
  nitpick[user_axioms] oops \<comment> \<open>Countermodel found: modal collapse is not valid\<close>

text\<open>\noindent{Since this time Nitpick was not able to find a countermodel for C10, we have enough confidence in
the validity of the formula to ask Sledgehammer to search for a proof.}\<close>
theorem C10:  "\<lfloor>\<^bold>\<exists>\<^sup>Ax. Godlike x\<rfloor>" using Existence_def Necessary_def
    abstractness_essential concrete_exist P2 C1 B_axiom by meson
    
text\<open>\noindent{Sledgehammer is able to find a proof relying on all premises
but the two modal axioms \emph{T} and \emph{IV}. By the end of this iteration we see
that Lowe's modal ontological argument depends for its validity on three non-stated (i.e. implicit) premises:
the essentiality of abstractness, the existence-entailing nature of concreteness and the modal
axiom \emph{B} (\<open>\<phi> \<rightarrow>  \<box>\<diamond>\<phi>\<close>). Moreover, we have also shed some light on the meaning of the concepts
of abstractness and concreteness.}\<close>

(*<*)
end
(*>*)
