(*<*)
theory IHOML_Examples
imports IHOML
begin
nitpick_params[user_axioms=true, show_all, expect=genuine, format = 3, atoms e = a b c d]
sledgehammer_params[verbose=true]
(*>*)

section \<open>Textbook Examples\<close>
  
text\<open>  In this section we provide further evidence that our embedded logic works as intended by proving the examples discussed in the book.
 In many cases, we consider further theorems which we derived from the original ones. We were able to confirm that all results
 (proofs or counterexamples) agree with Fitting's claims. \<close>
  
subsection \<open>Modal Logic - Syntax and Semantics (Chapter 7)\<close>

text\<open> Reminder: We call a term \emph{relativized} if it is of the form \<open>\<down>\<alpha>\<close>
(i.e. an intensional term preceded by the \emph{extension-of} operator), otherwise it is \emph{non-relativized}.
Relativized terms are non-rigid and non-relativized terms are rigid. \<close>
  
subsubsection \<open>Considerations Regarding \<open>\<beta>\<eta>\<close>-redex  (p. 94)\<close>

text\<open>  \<open>\<beta>\<eta>\<close>-redex is valid for non-relativized (intensional or extensional) terms:  \<close>
lemma "\<lfloor>((\<lambda>\<alpha>. \<phi> \<alpha>)  (\<tau>::\<up>\<zero>)) \<^bold>\<leftrightarrow> (\<phi>  \<tau>)\<rfloor>" by simp
lemma "\<lfloor>((\<lambda>\<alpha>. \<phi> \<alpha>)  (\<tau>::\<zero>)) \<^bold>\<leftrightarrow> (\<phi>  \<tau>)\<rfloor>" by simp
lemma "\<lfloor>((\<lambda>\<alpha>. \<^bold>\<box>\<phi> \<alpha>) (\<tau>::\<up>\<zero>)) \<^bold>\<leftrightarrow> (\<^bold>\<box>\<phi> \<tau>)\<rfloor>" by simp
lemma "\<lfloor>((\<lambda>\<alpha>. \<^bold>\<box>\<phi> \<alpha>) (\<tau>::\<zero>)) \<^bold>\<leftrightarrow> (\<^bold>\<box>\<phi> \<tau>)\<rfloor>" by simp    
text\<open>  \<open>\<beta>\<eta>\<close>-redex is valid for relativized terms as long as no modal operators occur inside the predicate abstract:  \<close>
lemma "\<lfloor>((\<lambda>\<alpha>. \<phi> \<alpha>) \<downharpoonleft>(\<tau>::\<up>\<zero>)) \<^bold>\<leftrightarrow> (\<phi> \<downharpoonleft>\<tau>)\<rfloor>" by simp
text\<open>  \<open>\<beta>\<eta>\<close>-redex is non-valid for relativized terms when modal operators are present:  \<close>
lemma "\<lfloor>((\<lambda>\<alpha>. \<^bold>\<box>\<phi> \<alpha>) \<downharpoonleft>(\<tau>::\<up>\<zero>)) \<^bold>\<leftrightarrow> (\<^bold>\<box>\<phi> \<downharpoonleft>\<tau>)\<rfloor>" nitpick oops   \<comment> \<open>countersatisfiable\<close>
lemma "\<lfloor>((\<lambda>\<alpha>. \<^bold>\<diamond>\<phi> \<alpha>) \<downharpoonleft>(\<tau>::\<up>\<zero>)) \<^bold>\<leftrightarrow> (\<^bold>\<diamond>\<phi> \<downharpoonleft>\<tau>)\<rfloor>" nitpick oops   \<comment> \<open>countersatisfiable\<close>
    
text\<open>  Example 7.13, p. 96: \<close>
lemma "\<lfloor>(\<lambda>X. \<^bold>\<diamond>\<^bold>\<exists>X)  (P::\<up>\<langle>\<zero>\<rangle>) \<^bold>\<rightarrow> \<^bold>\<diamond>((\<lambda>X. \<^bold>\<exists>X)  P)\<rfloor>"  by simp    
lemma "\<lfloor>(\<lambda>X. \<^bold>\<diamond>\<^bold>\<exists>X) \<^bold>\<down>(P::\<up>\<langle>\<zero>\<rangle>) \<^bold>\<rightarrow> \<^bold>\<diamond>((\<lambda>X. \<^bold>\<exists>X) \<^bold>\<down>P)\<rfloor>"
  nitpick[card 't=1, card i=2] oops \<comment> \<open>nitpick finds same counterexample as book\<close>
text\<open>  with other types for @{term "P"}:  \<close>
lemma "\<lfloor>(\<lambda>X. \<^bold>\<diamond>\<^bold>\<exists>X)  (P::\<up>\<langle>\<up>\<zero>\<rangle>) \<^bold>\<rightarrow> \<^bold>\<diamond>((\<lambda>X. \<^bold>\<exists>X)  P)\<rfloor>"  by simp    
lemma "\<lfloor>(\<lambda>X. \<^bold>\<diamond>\<^bold>\<exists>X) \<^bold>\<down>(P::\<up>\<langle>\<up>\<zero>\<rangle>) \<^bold>\<rightarrow> \<^bold>\<diamond>((\<lambda>X. \<^bold>\<exists>X) \<^bold>\<down>P)\<rfloor>" 
  nitpick[card 't=1, card i=2] oops \<comment> \<open>countersatisfiable\<close>
lemma "\<lfloor>(\<lambda>X. \<^bold>\<diamond>\<^bold>\<exists>X)  (P::\<up>\<langle>\<langle>\<zero>\<rangle>\<rangle>) \<^bold>\<rightarrow> \<^bold>\<diamond>((\<lambda>X. \<^bold>\<exists>X)  P)\<rfloor>"  by simp    
lemma "\<lfloor>(\<lambda>X. \<^bold>\<diamond>\<^bold>\<exists>X) \<^bold>\<down>(P::\<up>\<langle>\<langle>\<zero>\<rangle>\<rangle>) \<^bold>\<rightarrow> \<^bold>\<diamond>((\<lambda>X. \<^bold>\<exists>X) \<^bold>\<down>P)\<rfloor>" 
  nitpick[card 't=1, card i=2] oops \<comment> \<open>countersatisfiable\<close>
lemma "\<lfloor>(\<lambda>X. \<^bold>\<diamond>\<^bold>\<exists>X)  (P::\<up>\<langle>\<up>\<langle>\<zero>\<rangle>\<rangle>)\<^bold>\<rightarrow> \<^bold>\<diamond>((\<lambda>X. \<^bold>\<exists>X)  P)\<rfloor>"  by simp    
lemma "\<lfloor>(\<lambda>X. \<^bold>\<diamond>\<^bold>\<exists>X) \<^bold>\<down>(P::\<up>\<langle>\<up>\<langle>\<zero>\<rangle>\<rangle>)\<^bold>\<rightarrow> \<^bold>\<diamond>((\<lambda>X. \<^bold>\<exists>X) \<^bold>\<down>P)\<rfloor>" 
  nitpick[card 't=1, card i=2] oops \<comment> \<open>countersatisfiable\<close>
    
text\<open>  Example 7.14, p. 98: \<close>
lemma "\<lfloor>(\<lambda>X. \<^bold>\<diamond>\<^bold>\<exists>X) \<^bold>\<down>(P::\<up>\<langle>\<zero>\<rangle>) \<^bold>\<rightarrow> (\<lambda>X. \<^bold>\<exists>X) \<^bold>\<down>P\<rfloor>" by simp
lemma "\<lfloor>(\<lambda>X. \<^bold>\<diamond>\<^bold>\<exists>X)  (P::\<up>\<langle>\<zero>\<rangle>) \<^bold>\<rightarrow> (\<lambda>X. \<^bold>\<exists>X)  P\<rfloor>" 
  nitpick[card 't=1, card i=2] oops \<comment> \<open>countersatisfiable\<close>
text\<open>  with other types for @{term "P"}:  \<close>
lemma "\<lfloor>(\<lambda>X. \<^bold>\<diamond>\<^bold>\<exists>X) \<^bold>\<down>(P::\<up>\<langle>\<up>\<zero>\<rangle>) \<^bold>\<rightarrow> (\<lambda>X. \<^bold>\<exists>X) \<^bold>\<down>P\<rfloor>" by simp
lemma "\<lfloor>(\<lambda>X. \<^bold>\<diamond>\<^bold>\<exists>X)  (P::\<up>\<langle>\<up>\<zero>\<rangle>) \<^bold>\<rightarrow> (\<lambda>X. \<^bold>\<exists>X)  P\<rfloor>" 
  nitpick[card 't=1, card i=2] oops \<comment> \<open>countersatisfiable\<close>
lemma "\<lfloor>(\<lambda>X. \<^bold>\<diamond>\<^bold>\<exists>X) \<^bold>\<down>(P::\<up>\<langle>\<langle>\<zero>\<rangle>\<rangle>) \<^bold>\<rightarrow> (\<lambda>X. \<^bold>\<exists>X) \<^bold>\<down>P\<rfloor>" by simp
lemma "\<lfloor>(\<lambda>X. \<^bold>\<diamond>\<^bold>\<exists>X)  (P::\<up>\<langle>\<langle>\<zero>\<rangle>\<rangle>) \<^bold>\<rightarrow> (\<lambda>X. \<^bold>\<exists>X)  P\<rfloor>" 
  nitpick[card 't=1, card i=2] oops \<comment> \<open>countersatisfiable\<close>
lemma "\<lfloor>(\<lambda>X. \<^bold>\<diamond>\<^bold>\<exists>X) \<^bold>\<down>(P::\<up>\<langle>\<up>\<langle>\<zero>\<rangle>\<rangle>)\<^bold>\<rightarrow> (\<lambda>X. \<^bold>\<exists>X) \<^bold>\<down>P\<rfloor>" by simp
lemma "\<lfloor>(\<lambda>X. \<^bold>\<diamond>\<^bold>\<exists>X)  (P::\<up>\<langle>\<up>\<langle>\<zero>\<rangle>\<rangle>)\<^bold>\<rightarrow> (\<lambda>X. \<^bold>\<exists>X)  P\<rfloor>" 
  nitpick[card 't=1, card i=2] oops \<comment> \<open>countersatisfiable\<close>
    
text\<open>  Example 7.15, p. 99: \<close>
lemma "\<lfloor>\<^bold>\<box>(P (c::\<up>\<zero>)) \<^bold>\<rightarrow> (\<^bold>\<exists>x::\<up>\<zero>. \<^bold>\<box>(P x))\<rfloor>" by auto
text\<open>  with other types for @{term "P"}:  \<close>
lemma "\<lfloor>\<^bold>\<box>(P (c::\<zero>)) \<^bold>\<rightarrow> (\<^bold>\<exists>x::\<zero>. \<^bold>\<box>(P x))\<rfloor>" by auto
lemma "\<lfloor>\<^bold>\<box>(P (c::\<langle>\<zero>\<rangle>)) \<^bold>\<rightarrow> (\<^bold>\<exists>x::\<langle>\<zero>\<rangle>. \<^bold>\<box>(P x))\<rfloor>" by auto
    
text\<open>  Example 7.16, p. 100: \<close>
lemma "\<lfloor>\<^bold>\<box>(P \<downharpoonleft>(c::\<up>\<zero>)) \<^bold>\<rightarrow> (\<^bold>\<exists>x::\<zero>. \<^bold>\<box>(P x))\<rfloor>" 
  nitpick[card 't=2, card i=2] oops \<comment> \<open>counterexample with two worlds found\<close>
    
text\<open>  Example 7.17, p. 101: \<close>
lemma "\<lfloor>\<^bold>\<forall>Z::\<up>\<zero>. (\<lambda>x::\<zero>.  \<^bold>\<box>((\<lambda>y::\<zero>.  x \<^bold>\<approx> y) \<downharpoonleft>Z)) \<downharpoonleft>Z\<rfloor>" 
  nitpick[card 't=2, card i=2] oops \<comment> \<open>countersatisfiable\<close>
lemma "\<lfloor>\<^bold>\<forall>z::\<zero>.  (\<lambda>x::\<zero>.  \<^bold>\<box>((\<lambda>y::\<zero>.  x \<^bold>\<approx> y)  z)) z\<rfloor>" by simp
lemma "\<lfloor>\<^bold>\<forall>Z::\<up>\<zero>. (\<lambda>X::\<up>\<zero>. \<^bold>\<box>((\<lambda>Y::\<up>\<zero>. X \<^bold>\<approx> Y)  Z)) Z\<rfloor>" by simp
    
subsubsection \<open>Exercises (p. 101)\<close>
    
text\<open>  For Exercises 7.1 and 7.2 see variations on Examples 7.13 and 7.14 above.  \<close>
text\<open>  Exercise 7.3:  \<close>    
lemma "\<lfloor>\<^bold>\<diamond>\<^bold>\<exists>(P::\<up>\<langle>\<zero>\<rangle>) \<^bold>\<rightarrow> (\<^bold>\<exists>X::\<up>\<zero>. \<^bold>\<diamond>(P \<downharpoonleft>X))\<rfloor>" by auto
text\<open>  Exercise 7.4:  \<close>  
lemma "\<lfloor>\<^bold>\<diamond>(\<^bold>\<exists>x::\<zero>. (\<lambda>Y. Y x) \<^bold>\<down>(P::\<up>\<langle>\<zero>\<rangle>)) \<^bold>\<rightarrow> (\<^bold>\<exists>x. (\<lambda>Y. \<^bold>\<diamond>(Y x)) \<^bold>\<down>P)\<rfloor>" 
  nitpick[card 't=1, card i=2] oops \<comment> \<open>countersatisfiable\<close>    
    
text\<open>  For Exercise 7.5 see Example 7.17 above.  \<close>
text\<open> \bigbreak \<close>    
subsection \<open>Miscellaneous Matters (Chapter 9)\<close>

subsubsection \<open>Equality Axioms (Subsection 1.1)\<close>
    
text\<open>  Example 9.1:  \<close>
lemma "\<lfloor>((\<lambda>X. \<^bold>\<box>(X \<downharpoonleft>(p::\<up>\<zero>))) \<^bold>\<down>(\<lambda>x. \<^bold>\<diamond>(\<lambda>z. z \<^bold>\<approx> x) \<downharpoonleft>p))\<rfloor>" 
  by auto \<comment> \<open>using normal equality\<close>
lemma "\<lfloor>((\<lambda>X. \<^bold>\<box>(X \<downharpoonleft>(p::\<up>\<zero>))) \<^bold>\<down>(\<lambda>x. \<^bold>\<diamond>(\<lambda>z. z \<^bold>\<approx>\<^sup>L x) \<downharpoonleft>p))\<rfloor>" 
  by auto \<comment> \<open>using Leibniz equality\<close>
lemma "\<lfloor>((\<lambda>X. \<^bold>\<box>(X  (p::\<up>\<zero>))) \<^bold>\<down>(\<lambda>x. \<^bold>\<diamond>(\<lambda>z. z \<^bold>\<approx>\<^sup>C x) p))\<rfloor>" 
  by simp  \<comment> \<open>using equality as defined for individual concepts\<close>

    
subsubsection \<open>Extensionality (Subsection 1.2)\<close>
  
text\<open>  In Fitting's book (p. 118), extensionality is assumed (globally) for extensional terms. While Fitting introduces 
the following extensionality principles as axioms, they are already implicitly valid in Isabelle/HOL:  \<close>    
lemma EXT: "\<forall>\<alpha>::\<langle>\<zero>\<rangle>. \<forall>\<beta>::\<langle>\<zero>\<rangle>. (\<forall>\<gamma>::\<zero>. (\<alpha> \<gamma> \<longleftrightarrow> \<beta> \<gamma>)) \<longrightarrow> (\<alpha> = \<beta>)" by auto
lemma EXT_set: "\<forall>\<alpha>::\<langle>\<langle>\<zero>\<rangle>\<rangle>. \<forall>\<beta>::\<langle>\<langle>\<zero>\<rangle>\<rangle>. (\<forall>\<gamma>::\<langle>\<zero>\<rangle>. (\<alpha> \<gamma> \<longleftrightarrow> \<beta> \<gamma>)) \<longrightarrow> (\<alpha> = \<beta>)" 
  by auto
    
subsubsection \<open>\emph{De Re} and \emph{De Dicto} (Subsection 2)\<close>

text\<open>  \emph{De re} is equivalent to \emph{de dicto} for non-relativized (extensional or intensional) terms:  \<close>
lemma "\<lfloor>\<^bold>\<forall>\<alpha>. ((\<lambda>\<beta>. \<^bold>\<box>(\<alpha> \<beta>)) (\<tau>::\<zero>))   \<^bold>\<leftrightarrow> \<^bold>\<box>((\<lambda>\<beta>. (\<alpha> \<beta>)) \<tau>)\<rfloor>" by simp
lemma "\<lfloor>\<^bold>\<forall>\<alpha>. ((\<lambda>\<beta>. \<^bold>\<box>(\<alpha> \<beta>)) (\<tau>::\<up>\<zero>))  \<^bold>\<leftrightarrow> \<^bold>\<box>((\<lambda>\<beta>. (\<alpha> \<beta>)) \<tau>)\<rfloor>" by simp
lemma "\<lfloor>\<^bold>\<forall>\<alpha>. ((\<lambda>\<beta>. \<^bold>\<box>(\<alpha> \<beta>)) (\<tau>::\<langle>\<zero>\<rangle>))  \<^bold>\<leftrightarrow> \<^bold>\<box>((\<lambda>\<beta>. (\<alpha> \<beta>)) \<tau>)\<rfloor>" by simp
lemma "\<lfloor>\<^bold>\<forall>\<alpha>. ((\<lambda>\<beta>. \<^bold>\<box>(\<alpha> \<beta>)) (\<tau>::\<up>\<langle>\<zero>\<rangle>)) \<^bold>\<leftrightarrow> \<^bold>\<box>((\<lambda>\<beta>. (\<alpha> \<beta>)) \<tau>)\<rfloor>" by simp

text\<open>  \emph{De re} is not equivalent to \emph{de dicto} for relativized terms:  \<close>    
lemma "\<lfloor>\<^bold>\<forall>\<alpha>. ((\<lambda>\<beta>. \<^bold>\<box>(\<alpha> \<beta>)) \<downharpoonleft>(\<tau>::\<up>\<zero>)) \<^bold>\<leftrightarrow> \<^bold>\<box>( (\<lambda>\<beta>. (\<alpha> \<beta>)) \<downharpoonleft>\<tau>)\<rfloor>" 
  nitpick[card 't=2, card i=2] oops \<comment> \<open>countersatisfiable\<close>
lemma "\<lfloor>\<^bold>\<forall>\<alpha>. ((\<lambda>\<beta>. \<^bold>\<box>(\<alpha> \<beta>)) \<^bold>\<down>(\<tau>::\<up>\<langle>\<zero>\<rangle>)) \<^bold>\<leftrightarrow> \<^bold>\<box>( (\<lambda>\<beta>. (\<alpha> \<beta>)) \<^bold>\<down>\<tau>)\<rfloor>" 
  nitpick[card 't=1, card i=2] oops \<comment> \<open>countersatisfiable\<close>
  
text\<open>  Proposition 9.6 - If we can prove one side of the equivalence, then we can prove the other (p. 120):  \<close>
abbreviation deDictoImplDeRe::"\<up>\<zero>\<Rightarrow>io" 
  where "deDictoImplDeRe \<tau> \<equiv> \<^bold>\<forall>\<alpha>. \<^bold>\<box>((\<lambda>\<beta>. (\<alpha> \<beta>)) \<downharpoonleft>\<tau>) \<^bold>\<rightarrow> ((\<lambda>\<beta>. \<^bold>\<box>(\<alpha> \<beta>)) \<downharpoonleft>\<tau>)"
abbreviation deReImplDeDicto::"\<up>\<zero>\<Rightarrow>io" 
  where "deReImplDeDicto \<tau> \<equiv> \<^bold>\<forall>\<alpha>. ((\<lambda>\<beta>. \<^bold>\<box>(\<alpha> \<beta>)) \<downharpoonleft>\<tau>) \<^bold>\<rightarrow> \<^bold>\<box>((\<lambda>\<beta>. (\<alpha> \<beta>)) \<downharpoonleft>\<tau>)"
abbreviation deReEquDeDicto::"\<up>\<zero>\<Rightarrow>io" 
  where "deReEquDeDicto \<tau> \<equiv> \<^bold>\<forall>\<alpha>. ((\<lambda>\<beta>. \<^bold>\<box>(\<alpha> \<beta>)) \<downharpoonleft>\<tau>) \<^bold>\<leftrightarrow> \<^bold>\<box>((\<lambda>\<beta>. (\<alpha> \<beta>)) \<downharpoonleft>\<tau>)"
text\<open> \bigbreak \<close>
abbreviation deDictoImplDeRe_pred::"('t\<Rightarrow>io)\<Rightarrow>io" 
  where "deDictoImplDeRe_pred \<tau> \<equiv> \<^bold>\<forall>\<alpha>. \<^bold>\<box>((\<lambda>\<beta>. (\<alpha> \<beta>)) \<^bold>\<down>\<tau>) \<^bold>\<rightarrow> ((\<lambda>\<beta>. \<^bold>\<box>(\<alpha> \<beta>)) \<^bold>\<down>\<tau>)"
abbreviation deReImplDeDicto_pred::"('t\<Rightarrow>io)\<Rightarrow>io" 
  where "deReImplDeDicto_pred \<tau> \<equiv> \<^bold>\<forall>\<alpha>. ((\<lambda>\<beta>. \<^bold>\<box>(\<alpha> \<beta>)) \<^bold>\<down>\<tau>) \<^bold>\<rightarrow> \<^bold>\<box>((\<lambda>\<beta>. (\<alpha> \<beta>)) \<^bold>\<down>\<tau>)"
abbreviation deReEquDeDicto_pred::"('t\<Rightarrow>io)\<Rightarrow>io" 
  where "deReEquDeDicto_pred \<tau> \<equiv> \<^bold>\<forall>\<alpha>. ((\<lambda>\<beta>. \<^bold>\<box>(\<alpha> \<beta>)) \<^bold>\<down>\<tau>) \<^bold>\<leftrightarrow> \<^bold>\<box>((\<lambda>\<beta>. (\<alpha> \<beta>)) \<^bold>\<down>\<tau>)"

text\<open>  We can prove local consequence: \<close>
lemma AimpB: "\<lfloor>deReImplDeDicto (\<tau>::\<up>\<zero>) \<^bold>\<rightarrow> deDictoImplDeRe \<tau>\<rfloor>"
  by force \<comment> \<open>for individuals\<close>
lemma AimpB_p: "\<lfloor>deReImplDeDicto_pred (\<tau>::\<up>\<langle>\<zero>\<rangle>) \<^bold>\<rightarrow> deDictoImplDeRe_pred \<tau>\<rfloor>"
  by force \<comment> \<open>for predicates\<close>

text\<open>  And global consequence follows directly (since local consequence implies global consequence, as shown before): \<close>
lemma "\<lfloor>deReImplDeDicto (\<tau>::\<up>\<zero>)\<rfloor> \<longrightarrow> \<lfloor>deDictoImplDeRe \<tau>\<rfloor>"
  using AimpB by (rule localImpGlobalCons) \<comment> \<open>for individuals\<close>
lemma "\<lfloor>deReImplDeDicto_pred (\<tau>::\<up>\<langle>\<zero>\<rangle>)\<rfloor> \<longrightarrow> \<lfloor>deDictoImplDeRe_pred \<tau>\<rfloor>"
  using AimpB_p by (rule localImpGlobalCons) \<comment> \<open>for predicates\<close>
       
    
subsubsection \<open>Rigidity (Subsection 3)\<close>
    
text\<open>  (Local) rigidity for intensional individuals:  \<close>    
abbreviation rigidIndiv::"\<up>\<langle>\<up>\<zero>\<rangle>" where
  "rigidIndiv \<tau> \<equiv> (\<lambda>\<beta>. \<^bold>\<box>((\<lambda>z. \<beta> \<^bold>\<approx> z) \<downharpoonleft>\<tau>)) \<downharpoonleft>\<tau>"
text\<open>  (Local) rigidity for intensional predicates:  \<close>    
abbreviation rigidPred::"('t\<Rightarrow>io)\<Rightarrow>io" where
  "rigidPred \<tau> \<equiv> (\<lambda>\<beta>. \<^bold>\<box>((\<lambda>z. \<beta> \<^bold>\<approx> z) \<^bold>\<down>\<tau>)) \<^bold>\<down>\<tau>"
  
text\<open>  Proposition 9.8 - An intensional term is rigid if and only if the \emph{de re/de dicto} distinction vanishes.
Note that we can prove this theorem for local consequence (global consequence follows directly).  \<close>  
lemma "\<lfloor>rigidIndiv (\<tau>::\<up>\<zero>) \<^bold>\<rightarrow> deReEquDeDicto \<tau>\<rfloor>" by simp
lemma "\<lfloor>deReImplDeDicto (\<tau>::\<up>\<zero>) \<^bold>\<rightarrow> rigidIndiv \<tau>\<rfloor>" by auto
lemma "\<lfloor>rigidPred (\<tau>::\<up>\<langle>\<zero>\<rangle>) \<^bold>\<rightarrow> deReEquDeDicto_pred \<tau>\<rfloor>" by simp
lemma "\<lfloor>deReImplDeDicto_pred (\<tau>::\<up>\<langle>\<zero>\<rangle>) \<^bold>\<rightarrow> rigidPred \<tau>\<rfloor>" by auto
   
subsubsection \<open>Stability Conditions (Subsection 4)\<close>
    
axiomatization where
 S5: "equivalence aRel" \<comment> \<open>using Sahlqvist correspondence for improved performance\<close>
    
text\<open>  Definition 9.10 - Stability conditions come in pairs:  \<close>
abbreviation stabilityA::"('t\<Rightarrow>io)\<Rightarrow>io" where "stabilityA \<tau> \<equiv> \<^bold>\<forall>\<alpha>. (\<tau> \<alpha>) \<^bold>\<rightarrow> \<^bold>\<box>(\<tau> \<alpha>)"
abbreviation stabilityB::"('t\<Rightarrow>io)\<Rightarrow>io" where "stabilityB \<tau> \<equiv> \<^bold>\<forall>\<alpha>. \<^bold>\<diamond>(\<tau> \<alpha>) \<^bold>\<rightarrow> (\<tau> \<alpha>)"

text\<open>  Proposition 9.10 - In an \emph{S5} modal logic both stability conditions are equivalent. \<close>
text\<open>  The last proposition holds for global consequence: \<close>  
lemma "\<lfloor>stabilityA (\<tau>::\<up>\<langle>\<zero>\<rangle>)\<rfloor> \<longrightarrow> \<lfloor>stabilityB \<tau>\<rfloor>" using S5 by blast    
lemma "\<lfloor>stabilityB (\<tau>::\<up>\<langle>\<zero>\<rangle>)\<rfloor> \<longrightarrow> \<lfloor>stabilityA \<tau>\<rfloor>" using S5 by blast    
text\<open>  But it does not hold for local consequence: \<close>      
lemma "\<lfloor>stabilityA (\<tau>::\<up>\<langle>\<zero>\<rangle>) \<^bold>\<rightarrow> stabilityB \<tau>\<rfloor>" 
  nitpick[card 't=1, card i=2] oops \<comment> \<open>countersatisfiable\<close>
lemma "\<lfloor>stabilityB (\<tau>::\<up>\<langle>\<zero>\<rangle>) \<^bold>\<rightarrow> stabilityA \<tau>\<rfloor>" 
  nitpick[card 't=1, card i=2] oops \<comment> \<open>countersatisfiable\<close>
    
text\<open>  Theorem 9.11 - A term is rigid if and only if it satisfies the stability conditions. Note that
 we can prove this theorem for local consequence (global consequence follows directly).  \<close>
theorem "\<lfloor>rigidPred (\<tau>::\<up>\<langle>\<zero>\<rangle>) \<^bold>\<leftrightarrow> (stabilityA \<tau> \<^bold>\<and> stabilityB \<tau>)\<rfloor>" by meson   
theorem "\<lfloor>rigidPred (\<tau>::\<up>\<langle>\<up>\<zero>\<rangle>) \<^bold>\<leftrightarrow> (stabilityA \<tau> \<^bold>\<and> stabilityB \<tau>)\<rfloor>" by meson   
theorem "\<lfloor>rigidPred (\<tau>::\<up>\<langle>\<up>\<langle>\<zero>\<rangle>\<rangle>) \<^bold>\<leftrightarrow> (stabilityA \<tau> \<^bold>\<and> stabilityB \<tau>)\<rfloor>" by meson   
text\<open>  \pagebreak \<close>
(*<*)
end
(*>*)
