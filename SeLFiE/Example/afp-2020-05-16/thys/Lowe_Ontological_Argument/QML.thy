(*<*)
theory QML
imports Relations
begin  
nitpick_params[user_axioms=true, show_all, expect=genuine, format = 3, atoms e = a b c d]
(*>*)
  
section \<open>Embedding of Quantified Modal Logic\<close>
text\<open>\noindent{As is well known, the Isabelle proof assistant @{cite "Isabelle"} does not natively support modal logics, so
we have used a technique known as \emph{shallow semantic embedding}, which allows us
to take advantage of the expressive power of higher-order logic in order to embed the semantics
of an object language. We draw on previous work on the embedding of multimodal logics in HOL @{cite "J23"},
which has successfully been applied to the analysis and verification of ontological arguments
(e.g. @{cite C55 and J32 and J35}).}\<close>

subsection \<open>Type Declarations\<close>  

typedecl e                        \<comment> \<open>Type for entities\<close>             
typedecl w                        \<comment> \<open>Type for worlds\<close>
type_synonym wo = "w\<Rightarrow>bool" \<comment> \<open>Type for world-dependent formulas\<close>
  
subsection \<open>Logical Constants as Truth-Sets\<close>
text\<open>\noindent{Using the technique of \emph{shallow semantic embedding} each operator gets defined as a function
on world-dependent formulas or \emph{truth sets}.}\<close>
  
abbreviation mand::"wo\<Rightarrow>wo\<Rightarrow>wo" (infixr "\<^bold>\<and>"(*<*)51(*>*))
  where "\<phi>\<^bold>\<and>\<psi> \<equiv> \<lambda>w. (\<phi> w)\<and>(\<psi> w)"
abbreviation mor::"wo\<Rightarrow>wo\<Rightarrow>wo" (infixr "\<^bold>\<or>"(*<*)50(*>*))
  where "\<phi>\<^bold>\<or>\<psi> \<equiv> \<lambda>w. (\<phi> w)\<or>(\<psi> w)"
abbreviation mimp::"wo\<Rightarrow>wo\<Rightarrow>wo" (infixr "\<^bold>\<rightarrow>"(*<*)49(*>*))
  where "\<phi>\<^bold>\<rightarrow>\<psi> \<equiv> \<lambda>w. (\<phi> w)\<longrightarrow>(\<psi> w)"
abbreviation mequ::"wo\<Rightarrow>wo\<Rightarrow>wo" (infix "\<^bold>\<leftrightarrow>"(*<*)48(*>*))
  where "\<phi>\<^bold>\<leftrightarrow>\<psi> \<equiv> \<lambda>w. (\<phi> w)\<longleftrightarrow>(\<psi> w)"
abbreviation mnot::"wo\<Rightarrow>wo" ("\<^bold>\<not>_"(*<*)[52]53(*>*))
  where "\<^bold>\<not>\<phi> \<equiv> \<lambda>w. \<not>(\<phi> w)"
(*<*)
abbreviation xor:: "bool\<Rightarrow>bool\<Rightarrow>bool" (infix"\<oplus>"50) where "\<phi>\<oplus>\<psi> \<equiv>  (\<phi>\<or>\<psi>) \<and> \<not>(\<phi>\<and>\<psi>)" 
abbreviation mxor::"wo\<Rightarrow>wo\<Rightarrow>wo" (infix"\<^bold>\<oplus>"50) where "\<phi>\<^bold>\<oplus>\<psi> \<equiv> \<lambda>w. (\<phi> w)\<oplus>(\<psi> w)"
(*>*)

text\<open>\noindent{We embed a modal logic \emph{K} by defining the box and diamond operators using restricted quantification
over the set of `accessible' worlds (using an \emph{accessibility} relation \emph{R} as a guard).}\<close>
  
consts R::"w\<Rightarrow>w\<Rightarrow>bool" (infix "r"(*<*)70(*>*)) \<comment> \<open>Accessibility relation\<close>
abbreviation mbox :: "wo\<Rightarrow>wo" ("\<^bold>\<box>_"(*<*)[52]53(*>*))
  where "\<^bold>\<box>\<phi> \<equiv> \<lambda>w.\<forall>v. (w r v)\<longrightarrow>(\<phi> v)"
abbreviation mdia :: "wo\<Rightarrow>wo" ("\<^bold>\<diamond>_"(*<*)[52]53(*>*))
  where "\<^bold>\<diamond>\<phi> \<equiv> \<lambda>w.\<exists>v. (w r v)\<and>(\<phi> v)"

subsection \<open>Quantification\<close>
text\<open>\noindent{Quantifiers are defined analogously.}\<close>
  
abbreviation mforall::"('t\<Rightarrow>wo)\<Rightarrow>wo" ("\<^bold>\<forall>")
  where "\<^bold>\<forall>\<Phi> \<equiv> \<lambda>w.\<forall>x. (\<Phi> x w)"
abbreviation mexists::"('t\<Rightarrow>wo)\<Rightarrow>wo" ("\<^bold>\<exists>")
  where "\<^bold>\<exists>\<Phi> \<equiv> \<lambda>w.\<exists>x. (\<Phi> x w)"
abbreviation mforallB  :: "('t\<Rightarrow>wo)\<Rightarrow>wo" (binder "\<^bold>\<forall>"(*<*)[8]9(*>*))
  where "\<^bold>\<forall>x. (\<phi> x) \<equiv> \<^bold>\<forall>\<phi>"  
abbreviation mexistsB  :: "('t\<Rightarrow>wo)\<Rightarrow>wo" (binder "\<^bold>\<exists>"(*<*)[8]9(*>*))
  where "\<^bold>\<exists>x. (\<phi> x) \<equiv> \<^bold>\<exists>\<phi>" 
      
subsection \<open>Equality\<close> 
text\<open>\noindent{Two different definitions of equality are given. The first one is an extension of standard
equality for use in world-dependent formulas. The second is the well-known Leibniz equality.}\<close>
abbreviation meq:: "'t\<Rightarrow>'t\<Rightarrow>wo" (infix "\<^bold>\<approx>"(*<*)60(*>*))
  where "x \<^bold>\<approx> y \<equiv> \<lambda>w. x = y"    
abbreviation meqL:: "e\<Rightarrow>e\<Rightarrow>wo" (infix "\<^bold>\<approx>\<^sup>L"(*<*)52(*>*))
  where "x \<^bold>\<approx>\<^sup>L y \<equiv> \<lambda>w. \<forall>\<phi>. (\<phi> x w)\<longrightarrow>(\<phi> y w)"
      
subsection \<open>Validity\<close>
text\<open>\noindent{Validity is defined as truth in \emph{all} worlds and represented by wrapping the formula
in special brackets (\<open>\<lfloor>-\<rfloor>\<close>).}\<close>  
abbreviation valid::"wo\<Rightarrow>bool" ("\<lfloor>_\<rfloor>") where "\<lfloor>\<psi>\<rfloor> \<equiv>  \<forall>w.(\<psi> w)"
  
subsection \<open>Verifying the Embedding\<close>
text\<open>\noindent{The above definitions introduce modal logic \emph{K} with quantification,
as evidenced by the following tests.}\<close>
  
lemma K: "\<lfloor>(\<^bold>\<box>(\<phi> \<^bold>\<rightarrow> \<psi>)) \<^bold>\<rightarrow> (\<^bold>\<box>\<phi> \<^bold>\<rightarrow> \<^bold>\<box>\<psi>)\<rfloor>" by simp \<comment> \<open>Verifying \emph{K} principle\<close>
lemma NEC: "\<lfloor>\<phi>\<rfloor> \<Longrightarrow> \<lfloor>\<^bold>\<box>\<phi>\<rfloor>" by simp        \<comment> \<open>Verifying \emph{necessitation} rule\<close>
 
text\<open>\noindent{Local consequence implies global consequence (not the other way round).}\<close>
lemma localImpGlobalCons: "\<lfloor>\<phi> \<^bold>\<rightarrow> \<xi>\<rfloor> \<Longrightarrow> \<lfloor>\<phi>\<rfloor> \<longrightarrow> \<lfloor>\<xi>\<rfloor>" by simp
lemma "\<lfloor>\<phi>\<rfloor> \<longrightarrow> \<lfloor>\<xi>\<rfloor> \<Longrightarrow> \<lfloor>\<phi> \<^bold>\<rightarrow> \<xi>\<rfloor>" nitpick oops \<comment> \<open>Countersatisfiable\<close>

text\<open>\noindent{(Converse-)Barcan formulas are validated in this embedding.}\<close>
lemma "\<lfloor>(\<^bold>\<forall>x.\<^bold>\<box>(\<phi> x)) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<forall>x.(\<phi> x))\<rfloor>" by simp
lemma "\<lfloor>\<^bold>\<box>(\<^bold>\<forall>x.(\<phi> x)) \<^bold>\<rightarrow> (\<^bold>\<forall>x.\<^bold>\<box>(\<phi> x))\<rfloor>" by simp  
     
text\<open>\noindent{\<open>\<beta>\<close>-redex is valid.}\<close>
lemma "\<lfloor>(\<lambda>\<alpha>. \<phi> \<alpha>) (\<tau>::w\<Rightarrow>e) \<^bold>\<leftrightarrow> (\<phi>  \<tau>)\<rfloor>" by simp
lemma "\<lfloor>(\<lambda>\<alpha>. \<phi> \<alpha>) (\<tau>::e) \<^bold>\<leftrightarrow> (\<phi>  \<tau>)\<rfloor>" by simp
lemma "\<lfloor>(\<lambda>\<alpha>. \<^bold>\<box>\<phi> \<alpha>) (\<tau>::w\<Rightarrow>e) \<^bold>\<leftrightarrow> (\<^bold>\<box>\<phi> \<tau>)\<rfloor>" by simp
lemma "\<lfloor>(\<lambda>\<alpha>. \<^bold>\<box>\<phi> \<alpha>) (\<tau>::e) \<^bold>\<leftrightarrow> (\<^bold>\<box>\<phi> \<tau>)\<rfloor>" by simp    

text\<open>\noindent{Modal collapse is countersatisfiable, as shown by Nitpick @{cite "Nitpick"}.}\<close>
lemma "\<lfloor>\<phi> \<^bold>\<rightarrow> \<^bold>\<box>\<phi>\<rfloor>" nitpick oops

subsection \<open>Axiomatization of Further Logics\<close>

text\<open>\noindent{The best-known normal logics (\emph{K4, K5, KB, K45, KB5, D, D4, D5, ...}) can be obtained by
combinations of the following axioms.}\<close>
abbreviation T  where "T \<equiv> \<^bold>\<forall>\<phi>. \<^bold>\<box>\<phi> \<^bold>\<rightarrow> \<phi>"
abbreviation B  where "B \<equiv> \<^bold>\<forall>\<phi>. \<phi> \<^bold>\<rightarrow>  \<^bold>\<box>\<^bold>\<diamond>\<phi>"
abbreviation D  where "D \<equiv> \<^bold>\<forall>\<phi>. \<^bold>\<box>\<phi> \<^bold>\<rightarrow> \<^bold>\<diamond>\<phi>"
abbreviation IV where "IV \<equiv> \<^bold>\<forall>\<phi>. \<^bold>\<box>\<phi> \<^bold>\<rightarrow>  \<^bold>\<box>\<^bold>\<box>\<phi>"
abbreviation V  where "V \<equiv> \<^bold>\<forall>\<phi>. \<^bold>\<diamond>\<phi> \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<diamond>\<phi>"

text\<open>\noindent{Instead of postulating combinations of the above  axioms we make use of 
the well-known \emph{Sahlqvist correspondence}, which links axioms to constraints on a model's accessibility
relation (cf. @{cite "J23"} for further details).
We show  that  reflexivity, symmetry, seriality, transitivity and euclideanness imply
axioms \emph{T, B, D, IV, V} respectively.\footnote{Implication can also be proven in the reverse direction
(which is not needed for our purposes).
Using these definitions, we can derive axioms for the most common modal logics (see also @{cite "C47"}). 
Thereby we are free to use either the semantic constraints or the related \emph{Sahlqvist} axioms. Here we provide 
both versions. In what follows we use the semantic constraints for improved performance.}}\<close>
lemma "reflexive R  \<Longrightarrow>  \<lfloor>T\<rfloor>" by blast
lemma "symmetric R \<Longrightarrow> \<lfloor>B\<rfloor>" by blast
lemma "serial R  \<Longrightarrow> \<lfloor>D\<rfloor>" by blast         
lemma "transitive R  \<Longrightarrow> \<lfloor>IV\<rfloor>" by blast   
lemma "euclidean R \<Longrightarrow> \<lfloor>V\<rfloor>" by blast         
lemma "preorder R \<Longrightarrow> \<lfloor>T\<rfloor> \<and> \<lfloor>IV\<rfloor>" by blast \<comment> \<open>S4: reflexive + transitive\<close>
lemma "equivalence R \<Longrightarrow> \<lfloor>T\<rfloor> \<and> \<lfloor>V\<rfloor>" by blast \<comment> \<open>S5: preorder + symmetric\<close>     
(*<*) 
end
(*>*)   
