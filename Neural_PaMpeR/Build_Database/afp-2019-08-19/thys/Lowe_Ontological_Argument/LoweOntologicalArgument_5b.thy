(*<*) 
theory LoweOntologicalArgument_5b
imports Relations
begin

nitpick_params[box=false, user_axioms=true, show_all, expect=genuine, format = 3,  atoms e = a b c d]
sledgehammer_params[verbose=true]
  
typedecl e
(*>*)
  
section \<open>Fifth Iteration Series II: Non-Modal Ontological Argument in FOL\<close>
  
text\<open>\noindent{We show how we can formalize this argument entirely in first-order logic 
according to the literal reading shown in the previous iteration series.}\<close>
  
consts Necessary::"e\<Rightarrow>bool"
abbreviation Contingent::"e\<Rightarrow>bool" where "Contingent x \<equiv> \<not>(Necessary x)"
    
consts Concrete::"e\<Rightarrow>bool"
abbreviation Abstract::"e\<Rightarrow>bool" where "Abstract x \<equiv>  \<not>(Concrete x)"
  
consts Dependent::"e\<Rightarrow>bool" 
abbreviation Independent::"e\<Rightarrow>bool" where "Independent x  \<equiv> \<not>(Dependent x)"
        
consts dependence::"e\<Rightarrow>e\<Rightarrow>bool" (infix "dependsOn" 100)
abbreviation explanation::"(e\<Rightarrow>e\<Rightarrow>bool)" (infix "explains" 100)
  where "x explains y \<equiv> y dependsOn x"
  
axiomatization where
P2: "\<exists>x. Necessary x \<and> Abstract x" and
P3: "\<forall>x. Abstract x \<longrightarrow> Dependent x" and
P4: "\<forall>x. Dependent x \<longrightarrow> (\<exists>y. Independent y \<and> x dependsOn y)" and
P5: "\<not>(\<exists>x. \<exists>y. Contingent x \<and> Necessary y \<and> x explains y)"

abbreviation Godlike::"e\<Rightarrow>bool" where "Godlike x \<equiv> Necessary x \<and> Concrete x" 
  
theorem C10: "\<exists>x. Godlike x" using P2 P3 P4 P5 by blast

text\<open>\noindent{ We carry out our `sanity checks' as usual.}\<close>
lemma True nitpick[satisfy, user_axioms] oops (* Model found: axioms are consistent *)
lemma "\<forall>x. Concrete x" nitpick[user_axioms] oops (* Countermodel found: axioms do not trivialize argument *)
lemma "\<forall>x. Necessary x" nitpick[user_axioms] oops (* Countermodel found: axioms do not trivialize argument *)
    
end
