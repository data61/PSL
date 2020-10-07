(*<*)
theory CJDDLplus
  imports Main
begin
nitpick_params[user_axioms=true, show_all, expect=genuine, format = 3]
(*>*)

section \<open>Introduction\<close>
text\<open>\noindent{We present an encoding of an ambitious ethical theory ---Alan Gewirth's "Principle of Generic Consistency (PGC)"--- 
in Isabelle/HOL. The PGC has stirred much attention in philosophy and ethics @{cite "Beyleveld"} and has been proposed as a
potential means to bound the impact of artificial general intelligence (AGI) @{cite "Kornai"}.
With our contribution we make a first, important step towards formally assessing the PGC and its potential applications in AI.
Our formalisation utilises the shallow semantical embedding approach @{cite "J23"}
and adapts a recent embedding of dyadic deontic logic in HOL @{cite "C71"} @{cite "BenzmuellerDDL"}.
}\<close>

section \<open>Semantic Embedding of Carmo and Jones' Dyadic Deontic Logic (DDL) augmented with Kaplanian contexts\<close>

text\<open>\noindent{We introduce a modification of the semantic embedding developed by Benzm\"uller et al. @{cite "C71"} @{cite "BenzmuellerDDL"}
for the Dyadic Deontic Logic originally presented by Carmo and Jones @{cite "CJDDL"}. We extend this embedding
to a two-dimensional semantics as originally presented by David Kaplan @{cite "Kaplan1979"} @{cite "Kaplan1989"}.}\<close>

subsection \<open>Definition of Types\<close>

typedecl w   \<comment> \<open>  Type for possible worlds (Kaplan's "circumstances of evaluation" or "counterfactual situations")  \<close>
typedecl e   \<comment> \<open>  Type for individuals (entities eligible to become agents) \<close>
typedecl c   \<comment> \<open>  Type for Kaplanian "contexts of use" \<close>
type_synonym wo = "w\<Rightarrow>bool" \<comment> \<open>  contents/propositions are identified with their truth-sets \<close>
type_synonym cwo = "c\<Rightarrow>wo"  \<comment> \<open>  sentence meaning (Kaplan's "character") is a function from contexts to contents \<close>
type_synonym m = "cwo"      \<comment> \<open>  we use the letter 'm' for characters (reminiscent of "meaning") \<close>

subsection \<open>Semantic Characterisation of DDL\<close> (*cf. original Carmo and Jones Paper @{cite "CJDDL"} p.290ff*)

subsubsection \<open>Basic Set Operations\<close>
abbreviation subset::"wo\<Rightarrow>wo\<Rightarrow>bool" (infix "\<sqsubseteq>" 46) where "\<alpha> \<sqsubseteq> \<beta> \<equiv> \<forall>w. \<alpha> w  \<longrightarrow> \<beta> w"
abbreviation intersection::"wo\<Rightarrow>wo\<Rightarrow>wo" (infixr "\<sqinter>" 48) where "\<alpha> \<sqinter> \<beta> \<equiv> \<lambda>x. \<alpha> x \<and> \<beta> x"
abbreviation union::"wo\<Rightarrow>wo\<Rightarrow>wo" (infixr "\<squnion>" 48) where "\<alpha> \<squnion> \<beta> \<equiv> \<lambda>x. \<alpha> x \<or> \<beta> x"
abbreviation complement::"wo\<Rightarrow>wo" ("\<sim>_"[45]46) where "\<sim>\<alpha> \<equiv> \<lambda>x. \<not>\<alpha> x"
abbreviation instantiated::"wo\<Rightarrow>bool" ("\<I>_"[45]46) where "\<I> \<phi> \<equiv> \<exists>x. \<phi> x"
abbreviation setEq::"wo\<Rightarrow>wo\<Rightarrow>bool" (infix "=\<^sub>s" 46) where "\<alpha> =\<^sub>s \<beta> \<equiv> \<forall>x. \<alpha> x \<longleftrightarrow> \<beta> x"
abbreviation univSet :: "wo" ("\<top>") where "\<top> \<equiv> \<lambda>w. True"
abbreviation emptySet :: "wo" ("\<bottom>") where "\<bottom> \<equiv> \<lambda>w. False"

subsubsection \<open>Set-Theoretic Conditions for DDL\<close>

consts
av::"w\<Rightarrow>wo"   \<comment> \<open> set of worlds that are open alternatives (aka. actual versions) of w \<close>
pv::"w\<Rightarrow>wo"   \<comment> \<open> set of worlds that are possible alternatives (aka. potential versions) of w \<close>
ob::"wo\<Rightarrow>wo\<Rightarrow>bool" \<comment> \<open> set of propositions which are obligatory in a given context (of type wo)  \<close>

axiomatization where
sem_3a: "\<forall>w. \<I>(av w)" and \<comment> \<open>  av is serial: in every situation there is always an open alternative \<close>
sem_4a: "\<forall>w. av w \<sqsubseteq> pv w" and \<comment> \<open>  open alternatives are possible alternatives \<close>
sem_4b: "\<forall>w. pv w w" and \<comment> \<open>  pv is reflexive: every situation is a possible alternative to itself \<close>
sem_5a: "\<forall>X. \<not>(ob X \<bottom>)" and \<comment> \<open>  contradictions cannot be obligatory \<close>
sem_5b: "\<forall>X Y Z. (X \<sqinter> Y) =\<^sub>s (X \<sqinter> Z) \<longrightarrow> (ob X Y \<longleftrightarrow> ob X Z)" and
sem_5c: "\<forall>X Y Z. \<I>(X \<sqinter> Y \<sqinter> Z) \<and> ob X Y \<and> ob X Z \<longrightarrow> ob X (Y \<sqinter> Z)" and
sem_5d: "\<forall>X Y Z. (Y \<sqsubseteq> X \<and> ob X Y \<and> X \<sqsubseteq> Z) \<longrightarrow> ob Z ((Z \<sqinter> (\<sim>X)) \<squnion> Y)" and
sem_5e: "\<forall>X Y Z. Y \<sqsubseteq> X \<and> ob X Z \<and> \<I>(Y \<sqinter> Z) \<longrightarrow> ob Y Z"

lemma True nitpick[satisfy] oops \<comment> \<open> model found: axioms are consistent \<close>

subsubsection \<open>Verifying Semantic Conditions\<close>

lemma sem_5b1: "ob X Y \<longrightarrow> ob X (Y \<sqinter> X)" by (metis (no_types, lifting) sem_5b)
lemma sem_5b2: "(ob X (Y \<sqinter> X) \<longrightarrow> ob X Y)" by (metis (no_types, lifting) sem_5b) 
lemma sem_5ab: "ob X Y \<longrightarrow> \<I>(X \<sqinter> Y)" by (metis (full_types) sem_5a sem_5b)
lemma sem_5bd1: "Y \<sqsubseteq> X \<and> ob X Y \<and> X \<sqsubseteq> Z \<longrightarrow> ob Z ((\<sim>X) \<squnion> Y)" using sem_5b sem_5d by smt
lemma sem_5bd2: "ob X Y \<and> X \<sqsubseteq> Z \<longrightarrow> ob Z ((Z \<sqinter> (\<sim>X)) \<squnion> Y)"  using sem_5b sem_5d  by (smt sem_5b1)  
lemma sem_5bd3: "ob X Y \<and> X \<sqsubseteq> Z \<longrightarrow> ob Z ((\<sim>X) \<squnion> Y)"  by (smt sem_5bd2 sem_5b) 
lemma sem_5bd4: "ob X Y \<and> X \<sqsubseteq> Z \<longrightarrow> ob Z ((\<sim>X) \<squnion> (X \<sqinter>  Y))" using sem_5bd3 by auto
lemma sem_5bcd: "(ob X Z \<and> ob Y Z) \<longrightarrow> ob (X \<squnion> Y) Z" using sem_5b sem_5c sem_5d oops

(* 5e and 5ab justify redefinition of @{cite "O\<langle>\<phi>|\<sigma>\<rangle>"} as (ob A B)*)
lemma "ob A B \<longleftrightarrow>  (\<I>(A \<sqinter> B) \<and> (\<forall>X. X \<sqsubseteq> A \<and> \<I>(X \<sqinter> B) \<longrightarrow> ob X B))" using sem_5e sem_5ab by blast

subsection \<open>(Shallow) Semantic Embedding of DDL\<close>

subsubsection \<open>Basic Propositional Logic\<close>
abbreviation pand::"m\<Rightarrow>m\<Rightarrow>m" (infixr"\<^bold>\<and>" 51) where "\<phi>\<^bold>\<and>\<psi> \<equiv> \<lambda>c w. (\<phi> c w)\<and>(\<psi> c w)"
abbreviation por::"m\<Rightarrow>m\<Rightarrow>m" (infixr"\<^bold>\<or>" 50) where "\<phi>\<^bold>\<or>\<psi> \<equiv> \<lambda>c w. (\<phi> c w)\<or>(\<psi> c w)"
abbreviation pimp::"m\<Rightarrow>m\<Rightarrow>m" (infix"\<^bold>\<rightarrow>" 49) where "\<phi>\<^bold>\<rightarrow>\<psi> \<equiv> \<lambda>c w. (\<phi> c w)\<longrightarrow>(\<psi> c w)"
abbreviation pequ::"m\<Rightarrow>m\<Rightarrow>m" (infix"\<^bold>\<leftrightarrow>" 48) where "\<phi>\<^bold>\<leftrightarrow>\<psi> \<equiv> \<lambda>c w. (\<phi> c w)\<longleftrightarrow>(\<psi> c w)"
abbreviation pnot::"m\<Rightarrow>m" ("\<^bold>\<not>_" [52]53) where "\<^bold>\<not>\<phi> \<equiv> \<lambda>c w. \<not>(\<phi> c w)"

subsubsection \<open>Modal Operators\<close>
abbreviation cjboxa :: "m\<Rightarrow>m" ("\<^bold>\<box>\<^sub>a_" [52]53) where "\<^bold>\<box>\<^sub>a\<phi> \<equiv> \<lambda>c w. \<forall>v. (av w) v \<longrightarrow> (\<phi> c v)"
abbreviation cjdiaa :: "m\<Rightarrow>m" ("\<^bold>\<diamond>\<^sub>a_" [52]53) where "\<^bold>\<diamond>\<^sub>a\<phi> \<equiv> \<lambda>c w. \<exists>v. (av w) v \<and> (\<phi> c v)"
abbreviation cjboxp :: "m\<Rightarrow>m" ("\<^bold>\<box>\<^sub>p_" [52]53) where "\<^bold>\<box>\<^sub>p\<phi> \<equiv> \<lambda>c w. \<forall>v. (pv w) v \<longrightarrow> (\<phi> c v)"
abbreviation cjdiap :: "m\<Rightarrow>m" ("\<^bold>\<diamond>\<^sub>p_" [52]53) where "\<^bold>\<diamond>\<^sub>p\<phi> \<equiv> \<lambda>c w. \<exists>v. (pv w) v \<and> (\<phi> c v)"
abbreviation cjtaut :: "m" ("\<^bold>\<top>") where "\<^bold>\<top> \<equiv> \<lambda>c w. True"
abbreviation cjcontr :: "m" ("\<^bold>\<bottom>") where "\<^bold>\<bottom> \<equiv> \<lambda>c w. False"

subsubsection \<open>Deontic Operators\<close>
abbreviation cjod :: "m\<Rightarrow>m\<Rightarrow>m" ("\<^bold>O\<langle>_|_\<rangle>"54) where "\<^bold>O\<langle>\<phi>|\<sigma>\<rangle> \<equiv> \<lambda>c w. ob (\<sigma> c) (\<phi> c)"
abbreviation cjoa :: "m\<Rightarrow>m" ("\<^bold>O\<^sub>a_" [53]54) where "\<^bold>O\<^sub>a\<phi> \<equiv> \<lambda>c w. (ob (av w)) (\<phi> c) \<and> (\<exists>x. (av w) x \<and> \<not>(\<phi> c x))"
abbreviation cjop :: "m\<Rightarrow>m" ("\<^bold>O\<^sub>i_" [53]54) where "\<^bold>O\<^sub>i\<phi> \<equiv> \<lambda>c w. (ob (pv w)) (\<phi> c) \<and> (\<exists>x. (pv w) x \<and> \<not>(\<phi> c x))"

subsubsection \<open>Logical Validity (Classical)\<close>
abbreviation modvalidctx :: "m\<Rightarrow>c\<Rightarrow>bool" ("\<lfloor>_\<rfloor>\<^sup>M") where "\<lfloor>\<phi>\<rfloor>\<^sup>M \<equiv> \<lambda>c. \<forall>w. \<phi> c w" \<comment> \<open> context-dependent modal validity \<close>
abbreviation modvalid :: "m\<Rightarrow>bool" ("\<lfloor>_\<rfloor>") where "\<lfloor>\<phi>\<rfloor> \<equiv> \<forall>c. \<lfloor>\<phi>\<rfloor>\<^sup>M c" \<comment> \<open> general modal validity (modally valid in each context) \<close>

(*
If we introduce the alternative definition of logical validity below (from Kaplan's LD) instead of the previous one,
we can prove valid most of the following theorems excepting only CJ_7 and CJ_8 and the necessitation rule.

consts World::"c\<Rightarrow>w"  \<comment> \<open> function retrieving the world corresponding to context c (Kaplanian contexts are world-centered) \<close>        
abbreviation ldtruectx::"m\<Rightarrow>c\<Rightarrow>bool" ("\<lfloor>_\<rfloor>\<^sub>_") where "\<lfloor>\<phi>\<rfloor>\<^sub>c \<equiv> \<phi> c (World c)" \<comment> \<open>  truth in the given context \<close>
abbreviation ldvalid::"m\<Rightarrow>bool" ("\<lfloor>_\<rfloor>") where "\<lfloor>\<phi>\<rfloor> \<equiv> \<forall>c. \<lfloor>\<phi>\<rfloor>\<^sub>c"    \<comment> \<open>  LD validity (true in every context) \<close>
*)

subsection \<open>Verifying the Embedding\<close>

subsubsection \<open>Avoiding Modal Collapse\<close>
lemma "\<lfloor>P \<^bold>\<rightarrow> \<^bold>O\<^sub>aP\<rfloor>" nitpick oops \<comment> \<open> (actual) deontic modal collapse is countersatisfiable \<close>
lemma "\<lfloor>P \<^bold>\<rightarrow> \<^bold>O\<^sub>iP\<rfloor>" nitpick oops \<comment> \<open> (ideal) deontic modal collapse is countersatisfiable \<close>
lemma "\<lfloor>P \<^bold>\<rightarrow> \<^bold>\<box>\<^sub>aP\<rfloor>" nitpick oops \<comment> \<open> alethic modal collapse is countersatisfiable (implies all other necessity operators) \<close>

subsubsection \<open>Necessitation Rule\<close>
lemma NecDDLa: "\<lfloor>A\<rfloor> \<Longrightarrow> \<lfloor>\<^bold>\<box>\<^sub>aA\<rfloor>"  by simp (* Valid only using classical (not LD) validity*)
lemma NecDDLp:  "\<lfloor>A\<rfloor> \<Longrightarrow> \<lfloor>\<^bold>\<box>\<^sub>pA\<rfloor>" by simp (* Valid only using classical (not LD) validity*)

subsubsection \<open>Lemmas for Semantic Conditions\<close> (* extracted from Benzmüller et al. paper @{cite "BenzmuellerDDL"}*)

abbreviation mboxS5 :: "m\<Rightarrow>m" ("\<^bold>\<box>\<^sup>S\<^sup>5_" [52]53) where "\<^bold>\<box>\<^sup>S\<^sup>5\<phi> \<equiv> \<lambda>c w. \<forall>v. \<phi> c v"
abbreviation mdiaS5 :: "m\<Rightarrow>m" ("\<^bold>\<diamond>\<^sup>S\<^sup>5_" [52]53) where "\<^bold>\<diamond>\<^sup>S\<^sup>5\<phi> \<equiv> \<lambda>c w. \<exists>v. \<phi> c v"

lemma C_2: "\<lfloor>\<^bold>O\<langle>A | B\<rangle> \<^bold>\<rightarrow> \<^bold>\<diamond>\<^sup>S\<^sup>5(B \<^bold>\<and> A)\<rfloor>" by (simp add: sem_5ab)
lemma C_3:  "\<lfloor>((\<^bold>\<diamond>\<^sup>S\<^sup>5(A \<^bold>\<and> B \<^bold>\<and> C)) \<^bold>\<and> \<^bold>O\<langle>B|A\<rangle> \<^bold>\<and> \<^bold>O\<langle>C|A\<rangle>) \<^bold>\<rightarrow> \<^bold>O\<langle>(B \<^bold>\<and> C)| A\<rangle>\<rfloor>" by (simp add: sem_5c)
lemma C_4: "\<lfloor>(\<^bold>\<box>\<^sup>S\<^sup>5(A \<^bold>\<rightarrow> B) \<^bold>\<and> \<^bold>\<diamond>\<^sup>S\<^sup>5(A \<^bold>\<and> C) \<^bold>\<and> \<^bold>O\<langle>C|B\<rangle>) \<^bold>\<rightarrow> \<^bold>O\<langle>C|A\<rangle>\<rfloor>" using sem_5e by blast
lemma C_5: "\<lfloor>\<^bold>\<box>\<^sup>S\<^sup>5(A \<^bold>\<leftrightarrow> B) \<^bold>\<rightarrow> (\<^bold>O\<langle>C|A\<rangle> \<^bold>\<rightarrow> \<^bold>O\<langle>C|B\<rangle>)\<rfloor>" using C_2 sem_5e by blast
lemma C_6: "\<lfloor>\<^bold>\<box>\<^sup>S\<^sup>5(C \<^bold>\<rightarrow> (A \<^bold>\<leftrightarrow> B)) \<^bold>\<rightarrow> (\<^bold>O\<langle>A|C\<rangle> \<^bold>\<leftrightarrow> \<^bold>O\<langle>B|C\<rangle>)\<rfloor>" by (metis sem_5b)
lemma C_7: "\<lfloor>\<^bold>O\<langle>B|A\<rangle> \<^bold>\<rightarrow> \<^bold>\<box>\<^sup>S\<^sup>5\<^bold>O\<langle>B|A\<rangle>\<rfloor>" by blast 
lemma C_8: "\<lfloor>\<^bold>O\<langle>B|A\<rangle> \<^bold>\<rightarrow> \<^bold>O\<langle>A \<^bold>\<rightarrow> B| \<^bold>\<top>\<rangle>\<rfloor>" using sem_5bd4 by presburger

subsubsection \<open>Verifying Axiomatic Characterisation\<close>

text\<open>\noindent{The following theorems have been taken from the original Carmo and Jones' paper (@{cite "CJDDL"} p.293ff).}\<close>

lemma CJ_3: "\<lfloor>\<^bold>\<box>\<^sub>pA \<^bold>\<rightarrow> \<^bold>\<box>\<^sub>aA\<rfloor>" by (simp add: sem_4a)
lemma CJ_4: "\<lfloor>\<^bold>\<not>\<^bold>O\<langle>\<^bold>\<bottom>|A\<rangle>\<rfloor>" by (simp add: sem_5a)

lemma CJ_5: "\<lfloor>(\<^bold>O\<langle>B|A\<rangle> \<^bold>\<and> \<^bold>O\<langle>C|A\<rangle>) \<^bold>\<rightarrow> \<^bold>O\<langle>B\<^bold>\<and>C|A\<rangle>\<rfloor>" nitpick oops \<comment> \<open> countermodel found \<close>
lemma CJ_5_minus: "\<lfloor>\<^bold>\<diamond>\<^sup>S\<^sup>5(A \<^bold>\<and> B \<^bold>\<and> C) \<^bold>\<and> (\<^bold>O\<langle>B|A\<rangle> \<^bold>\<and> \<^bold>O\<langle>C|A\<rangle>) \<^bold>\<rightarrow> \<^bold>O\<langle>B\<^bold>\<and>C|A\<rangle>\<rfloor>" by (simp add: sem_5c)

lemma CJ_6: "\<lfloor>\<^bold>O\<langle>B|A\<rangle> \<^bold>\<rightarrow> \<^bold>O\<langle>B|A\<^bold>\<and>B\<rangle>\<rfloor>" by (smt C_2 C_4)
lemma CJ_7: "\<lfloor>A \<^bold>\<leftrightarrow> B\<rfloor> \<longrightarrow> \<lfloor>\<^bold>O\<langle>C|A\<rangle> \<^bold>\<leftrightarrow> \<^bold>O\<langle>C|B\<rangle>\<rfloor>" using sem_5ab sem_5e by blast (* Valid only using classical (not Kaplan's indexical) validity*)
lemma CJ_8: "\<lfloor>C \<^bold>\<rightarrow> (A \<^bold>\<leftrightarrow> B)\<rfloor> \<longrightarrow> \<lfloor>\<^bold>O\<langle>A|C\<rangle> \<^bold>\<leftrightarrow> \<^bold>O\<langle>B|C\<rangle>\<rfloor>" using C_6 by simp (* Valid only using classical (not Kaplan's indexical) validity*)

lemma CJ_9a: "\<lfloor>\<^bold>\<diamond>\<^sub>p\<^bold>O\<langle>B|A\<rangle> \<^bold>\<rightarrow> \<^bold>\<box>\<^sub>p\<^bold>O\<langle>B|A\<rangle>\<rfloor>" by simp
lemma CJ_9p: "\<lfloor>\<^bold>\<diamond>\<^sub>a\<^bold>O\<langle>B|A\<rangle> \<^bold>\<rightarrow> \<^bold>\<box>\<^sub>a\<^bold>O\<langle>B|A\<rangle>\<rfloor>" by simp
lemma CJ_9_var_a: "\<lfloor>\<^bold>O\<langle>B|A\<rangle> \<^bold>\<rightarrow> \<^bold>\<box>\<^sub>a\<^bold>O\<langle>B|A\<rangle>\<rfloor>" by simp
lemma CJ_9_var_b: "\<lfloor>\<^bold>O\<langle>B|A\<rangle> \<^bold>\<rightarrow> \<^bold>\<box>\<^sub>p\<^bold>O\<langle>B|A\<rangle>\<rfloor>" by simp
lemma CJ_10: "\<lfloor>\<^bold>\<diamond>\<^sub>p(A \<^bold>\<and> B \<^bold>\<and> C) \<^bold>\<and> \<^bold>O\<langle>C|B\<rangle> \<^bold>\<rightarrow> \<^bold>O\<langle>C|A\<^bold>\<and>B\<rangle>\<rfloor>" by (smt C_4)

lemma CJ_11a: "\<lfloor>(\<^bold>O\<^sub>aA \<^bold>\<and> \<^bold>O\<^sub>aB) \<^bold>\<rightarrow> \<^bold>O\<^sub>a(A \<^bold>\<and> B)\<rfloor>" nitpick oops \<comment> \<open>  countermodel found \<close>
lemma CJ_11a_var: "\<lfloor>\<^bold>\<diamond>\<^sub>a(A \<^bold>\<and> B) \<^bold>\<and> (\<^bold>O\<^sub>aA \<^bold>\<and> \<^bold>O\<^sub>aB) \<^bold>\<rightarrow> \<^bold>O\<^sub>a(A \<^bold>\<and> B)\<rfloor>" using sem_5c by auto

lemma CJ_11p: "\<lfloor>(\<^bold>O\<^sub>iA \<^bold>\<and> \<^bold>O\<^sub>iB) \<^bold>\<rightarrow> \<^bold>O\<^sub>i(A \<^bold>\<and> B)\<rfloor>" nitpick oops \<comment> \<open>  countermodel found \<close>
lemma CJ_11p_var: "\<lfloor>\<^bold>\<diamond>\<^sub>p(A \<^bold>\<and> B) \<^bold>\<and> (\<^bold>O\<^sub>iA \<^bold>\<and> \<^bold>O\<^sub>iB) \<^bold>\<rightarrow> \<^bold>O\<^sub>i(A \<^bold>\<and> B)\<rfloor>" using sem_5c by auto

lemma CJ_12a: "\<lfloor>\<^bold>\<box>\<^sub>aA \<^bold>\<rightarrow> (\<^bold>\<not>\<^bold>O\<^sub>aA \<^bold>\<and> \<^bold>\<not>\<^bold>O\<^sub>a(\<^bold>\<not>A))\<rfloor>" using sem_5ab by blast (*using C_2 by blast *)
lemma CJ_12p: "\<lfloor>\<^bold>\<box>\<^sub>pA \<^bold>\<rightarrow> (\<^bold>\<not>\<^bold>O\<^sub>iA \<^bold>\<and> \<^bold>\<not>\<^bold>O\<^sub>i(\<^bold>\<not>A))\<rfloor>" using sem_5ab by blast (*using C_2 by blast*) 

lemma CJ_13a: "\<lfloor>\<^bold>\<box>\<^sub>a(A \<^bold>\<leftrightarrow> B) \<^bold>\<rightarrow> (\<^bold>O\<^sub>aA \<^bold>\<leftrightarrow> \<^bold>O\<^sub>aB)\<rfloor>" using sem_5b by metis (*using C_6 by blast *)
lemma CJ_13p: "\<lfloor>\<^bold>\<box>\<^sub>p(A \<^bold>\<leftrightarrow> B) \<^bold>\<rightarrow> (\<^bold>O\<^sub>iA \<^bold>\<leftrightarrow> \<^bold>O\<^sub>iB)\<rfloor>" using sem_5b by metis (*using C_6 by blast *)

lemma CJ_O_O: "\<lfloor>\<^bold>O\<langle>B|A\<rangle> \<^bold>\<rightarrow> \<^bold>O\<langle>A \<^bold>\<rightarrow> B|\<^bold>\<top>\<rangle>\<rfloor>" using sem_5bd4 by presburger

text\<open>\noindent{An ideal obligation which is actually possible both to fulfill and to violate entails an actual obligation (@{cite "CJDDL"} p.319).}\<close>
lemma CJ_Oi_Oa: "\<lfloor>(\<^bold>O\<^sub>iA \<^bold>\<and> \<^bold>\<diamond>\<^sub>aA \<^bold>\<and> \<^bold>\<diamond>\<^sub>a(\<^bold>\<not>A)) \<^bold>\<rightarrow> \<^bold>O\<^sub>aA\<rfloor>" using sem_5e sem_4a by blast

text\<open>\noindent{Bridge relations between conditional obligations and actual/ideal obligations:}\<close>
lemma CJ_14a: "\<lfloor>\<^bold>O\<langle>B|A\<rangle> \<^bold>\<and> \<^bold>\<box>\<^sub>aA \<^bold>\<and> \<^bold>\<diamond>\<^sub>aB \<^bold>\<and> \<^bold>\<diamond>\<^sub>a\<^bold>\<not>B \<^bold>\<rightarrow> \<^bold>O\<^sub>aB\<rfloor>" using sem_5e by blast
lemma CJ_14p: "\<lfloor>\<^bold>O\<langle>B|A\<rangle> \<^bold>\<and> \<^bold>\<box>\<^sub>pA \<^bold>\<and> \<^bold>\<diamond>\<^sub>pB \<^bold>\<and> \<^bold>\<diamond>\<^sub>p\<^bold>\<not>B \<^bold>\<rightarrow> \<^bold>O\<^sub>iB\<rfloor>" using sem_5e by blast

lemma CJ_15a: "\<lfloor>(\<^bold>O\<langle>B|A\<rangle> \<^bold>\<and> \<^bold>\<diamond>\<^sub>a(A \<^bold>\<and> B) \<^bold>\<and> \<^bold>\<diamond>\<^sub>a(A \<^bold>\<and> \<^bold>\<not>B)) \<^bold>\<rightarrow>  \<^bold>O\<^sub>a(A \<^bold>\<rightarrow> B)\<rfloor>" using CJ_O_O sem_5e by fastforce (*using CJ_O_O CJ_14a by blast*)
lemma CJ_15p: "\<lfloor>(\<^bold>O\<langle>B|A\<rangle> \<^bold>\<and> \<^bold>\<diamond>\<^sub>p(A \<^bold>\<and> B) \<^bold>\<and> \<^bold>\<diamond>\<^sub>p(A \<^bold>\<and> \<^bold>\<not>B)) \<^bold>\<rightarrow>  \<^bold>O\<^sub>i(A \<^bold>\<rightarrow> B)\<rfloor>" using CJ_O_O sem_5e by fastforce (*using CJ_O_O CJ_14p by blast*)

(*<*)
end
(*>*)
