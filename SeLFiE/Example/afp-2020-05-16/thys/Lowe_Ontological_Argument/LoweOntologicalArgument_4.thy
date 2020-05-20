(*<*) 
theory LoweOntologicalArgument_4
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
  
axiomatization where
  P2: "\<lfloor>\<^bold>\<exists>\<^sup>Ax. Necessary x \<^bold>\<and> Abstract x\<rfloor>" and
  P3: "\<lfloor>\<^bold>\<forall>\<^sup>Ax. Abstract x \<^bold>\<rightarrow> Dependent x\<rfloor>" and
  P4: "\<lfloor>\<^bold>\<forall>\<^sup>Ax. Dependent x \<^bold>\<rightarrow> (\<^bold>\<exists>\<^sup>Ay. Independent y \<^bold>\<and> x dependsOn y)\<rfloor>"
(*>*) 

subsection \<open>Simplifying the Argument\<close>
  
text\<open>\noindent{After some further iterations we arrive at a new variant of the original argument:
Premises P1 to P4 remain unchanged and a new premise D5
("x depends for its existence on y := necessarily, x exists only if y exists") is added.
D5 corresponds to the `definition' of ontological dependence as put forth by
Lowe in his article (though just for illustrative purposes). As mentioned before, this purported definition was never meant by him to become part
of the argument. Nevertheless, we show here how, by assuming the left-to-right direction of this definition,
we get in a position to prove the main conclusions without any further assumptions.
}\<close>  
axiomatization where
  D5: "\<lfloor>\<^bold>\<forall>\<^sup>Ax y. x dependsOn y \<^bold>\<rightarrow> \<^bold>\<box>(E! x \<^bold>\<rightarrow> E! y)\<rfloor>"

theorem C1:  "\<lfloor>\<^bold>\<forall>\<^sup>Ax. Abstract x \<^bold>\<rightarrow> (\<^bold>\<exists>y. Concrete y \<^bold>\<and> x dependsOn y)\<rfloor>"
  using P3 P4 by meson
    
theorem C5: "\<lfloor>\<^bold>\<exists>\<^sup>Ax. Concrete x\<rfloor>"
  using P2 P3 P4 by meson
    
theorem C10:  "\<lfloor>\<^bold>\<exists>\<^sup>Ax. Godlike x\<rfloor>"
  using Necessary_def P2 P3 P4 D5 by meson
    
text\<open>\noindent{In this variant we have been able to verify the conclusion of the argument without appealing
to the concept of metaphysical explanation. We were able to get by with just the concept of
ontological dependence by explicating it in terms of existence and necessity (as suggested by Lowe).}\<close>
    
text\<open>\noindent{As a side note, we can also prove that the original premise P5
("No contingent being can explain the existence of a necessary being")
directly follows from D5 by redefining metaphysical explanation
as the inverse relation of ontological dependence.}\<close>
    
abbreviation explanation::"(e\<Rightarrow>e\<Rightarrow>wo)" (infix "explains"(*<*)100(*>*))
  where "y explains x \<equiv> x dependsOn y"
    
lemma P5: "\<lfloor>\<^bold>\<not>(\<^bold>\<exists>\<^sup>Ax. \<^bold>\<exists>\<^sup>Ay. Contingent y \<^bold>\<and> Necessary x \<^bold>\<and> y explains x)\<rfloor>"
  using Necessary_def Contingent_def D5 by meson
    
text\<open>\noindent{In this series of iterations we have reworked the argument so as to get rid of the somewhat obscure
concept of metaphysical explanation;
we also got some insight into Lowe's concept of ontological dependence vis-a-vis its
inferential role in this argument.}\<close>
text\<open>\noindent{There are still some interesting issues to consider.
Note that the definitions of existence (\<open>Existence_def\<close>) and being "dependent" (\<open>Dependent_def\<close>)
are not needed in any of the highly optimized proofs found by our automated tools.
This raises some suspicions concerning the role played by the existence predicate in the
definitions of necessariness and contingency, as well as putting into question the need for
a definition of being "dependent" linked to the ontological dependence relation.
We will see in the following section that our suspicions are justified and that
this argument can be dramatically simplified.}\<close>

(*<*) 
(* We carry out our `sanity checks' as usual.*)
lemma True nitpick[satisfy, user_axioms] oops (* model found: axioms are consistent *)
lemma "\<lfloor>Necessary x\<rfloor>" nitpick[user_axioms] oops (* counter-model found: axioms do not trivialize argument *)
lemma "\<lfloor>\<phi> \<^bold>\<rightarrow> \<^bold>\<box>\<phi>\<rfloor>" nitpick[user_axioms] oops (* counter-model found: modal collapse is not valid *)
    
end
(*>*)
