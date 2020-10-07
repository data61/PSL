(*<*) 
theory GoedelGod
imports Main 

begin
(*>*)

section \<open>Introduction\<close>

 text \<open>Dana Scott's version \cite{ScottNotes} (cf.~Fig.~1)
 of G\"odel's proof of God's existence \cite{GoedelNotes} is 
 formalized in quantified modal logic KB (QML KB) within the proof assistant Isabelle/HOL. 
 QML KB is  modeled as a fragment of classical higher-order logic (HOL); 
 thus, the formalization is essentially a formalization in HOL. The employed embedding 
 of QML KB in HOL is adapting the work of Benzm\"uller and Paulson \cite{J23,B9}.
 Note that the QML KB formalization employs quantification over individuals and 
 quantification over sets of individuals (properties).

 The gaps in Scott's proof have been automated 
 with Sledgehammer \cite{Sledgehammer}, performing remote calls to the higher-order automated
 theorem prover LEO-II \cite{LEO-II}. Sledgehammer suggests the 
 Metis \cite{Metis} calls, which result in proofs that are verified by Isabelle/HOL.
 For consistency checking, the model finder Nitpick \cite{Nitpick} has been employed.
 The successfull calls to Sledgehammer
 are deliberately kept as comments in the file for demonstration purposes
 (normally, they are automatically eliminated by Isabelle/HOL).
 
 Isabelle is described in the textbook by Nipkow, 
 Paulson, and Wenzel \cite{Isabelle} and in tutorials available 
 at: @{url "http://isabelle.in.tum.de"}.
 
\subsection{Related Work}

 The formalization presented here is related to the THF \cite{J22} and 
 Coq \cite{Coq} formalizations at 
 @{url "https://github.com/FormalTheology/GoedelGod/tree/master/Formalizations/"}.
 
 An older ontological argument by Anselm was formalized in PVS by John Rushby \cite{rushby}.
\<close>

section \<open>An Embedding of QML KB in HOL\<close>

text \<open>The types \<open>i\<close> for possible worlds and $\mu$ for individuals are introduced.\<close>

  typedecl i    \<comment> \<open>the type for possible worlds\<close> 
  typedecl \<mu>    \<comment> \<open>the type for indiviuals\<close>      

text \<open>Possible worlds are connected by an accessibility relation \<open>r\<close>.\<close> 

  consts r :: "i \<Rightarrow> i \<Rightarrow> bool" (infixr "r" 70)    \<comment> \<open>accessibility relation r\<close>   

text \<open>QML formulas are translated as HOL terms of type @{typ "i \<Rightarrow> bool"}. 
This type is abbreviated as \<open>\<sigma>\<close>.\<close>

  type_synonym \<sigma> = "(i \<Rightarrow> bool)"
 
text \<open>The classical connectives $\neg, \wedge, \rightarrow$, and $\forall$
(over individuals and over sets of individuals) and $\exists$ (over individuals) are
lifted to type $\sigma$. The lifted connectives are \<open>m\<not>\<close>, \<open>m\<and>\<close>, \<open>m\<rightarrow>\<close>,
\<open>\<forall>\<close>, and \<open>\<exists>\<close> (the latter two are modeled as constant symbols). 
Other connectives can be introduced analogously. We exemplarily do this for \<open>m\<or>\<close> , 
\<open>m\<equiv>\<close>, and \<open>mL=\<close> (Leibniz equality on individuals). Moreover, the modal 
operators \<open>\<box>\<close> and \<open>\<diamond>\<close>  are introduced. Definitions could be used instead of 
abbreviations.\<close>

  abbreviation mnot :: "\<sigma> \<Rightarrow> \<sigma>" ("m\<not>") where "m\<not> \<phi> \<equiv> (\<lambda>w. \<not> \<phi> w)"    
  abbreviation mand :: "\<sigma> \<Rightarrow> \<sigma> \<Rightarrow> \<sigma>" (infixr "m\<and>" 65) where "\<phi> m\<and> \<psi> \<equiv> (\<lambda>w. \<phi> w \<and> \<psi> w)"   
  abbreviation mor :: "\<sigma> \<Rightarrow> \<sigma> \<Rightarrow> \<sigma>" (infixr "m\<or>" 70) where "\<phi> m\<or> \<psi> \<equiv> (\<lambda>w. \<phi> w \<or> \<psi> w)"   
  abbreviation mimplies :: "\<sigma> \<Rightarrow> \<sigma> \<Rightarrow> \<sigma>" (infixr "m\<rightarrow>" 74) where "\<phi> m\<rightarrow> \<psi> \<equiv> (\<lambda>w. \<phi> w \<longrightarrow> \<psi> w)"  
  abbreviation mequiv:: "\<sigma> \<Rightarrow> \<sigma> \<Rightarrow> \<sigma>" (infixr "m\<equiv>" 76) where "\<phi> m\<equiv> \<psi> \<equiv> (\<lambda>w. \<phi> w \<longleftrightarrow> \<psi> w)"  
  abbreviation mforall :: "('a \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>" ("\<forall>") where "\<forall> \<Phi> \<equiv> (\<lambda>w. \<forall>x. \<Phi> x w)"   
  abbreviation mexists :: "('a \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>" ("\<exists>") where "\<exists> \<Phi> \<equiv> (\<lambda>w. \<exists>x. \<Phi> x w)"
  abbreviation mLeibeq :: "\<mu> \<Rightarrow> \<mu> \<Rightarrow> \<sigma>" (infixr "mL=" 90) where "x mL= y \<equiv> \<forall>(\<lambda>\<phi>. (\<phi> x m\<rightarrow> \<phi> y))"
  abbreviation mbox :: "\<sigma> \<Rightarrow> \<sigma>" ("\<box>") where "\<box> \<phi> \<equiv> (\<lambda>w. \<forall>v.  w r v \<longrightarrow> \<phi> v)"
  abbreviation mdia :: "\<sigma> \<Rightarrow> \<sigma>" ("\<diamond>") where "\<diamond> \<phi> \<equiv> (\<lambda>w. \<exists>v. w r v \<and> \<phi> v)" 
  
text \<open>For grounding lifted formulas, the meta-predicate \<open>valid\<close> is introduced.\<close>

  (*<*) no_syntax "_list" :: "args \<Rightarrow> 'a list" ("[(_)]") (*>*) 
  abbreviation valid :: "\<sigma> \<Rightarrow> bool" ("[_]") where "[p] \<equiv> \<forall>w. p w"
  
section \<open>G\"odel's Ontological Argument\<close>  
  
text \<open>Constant symbol \<open>P\<close> (G\"odel's `Positive') is declared.\<close>

  consts P :: "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>"  

text \<open>The meaning of \<open>P\<close> is restricted by axioms \<open>A1(a/b)\<close>: $\all \phi 
[P(\neg \phi) \biimp \neg P(\phi)]$ (Either a property or its negation is positive, but not both.) 
and \<open>A2\<close>: $\all \phi \all \psi [(P(\phi) \wedge \nec \all x [\phi(x) \imp \psi(x)]) 
\imp P(\psi)]$ (A property necessarily implied by a positive property is positive).\<close>

  axiomatization where
    A1a: "[\<forall>(\<lambda>\<Phi>. P (\<lambda>x. m\<not> (\<Phi> x)) m\<rightarrow> m\<not> (P \<Phi>))]" and
    A1b: "[\<forall>(\<lambda>\<Phi>. m\<not> (P \<Phi>) m\<rightarrow> P (\<lambda>x. m\<not> (\<Phi> x)))]" and
    A2:  "[\<forall>(\<lambda>\<Phi>. \<forall>(\<lambda>\<Psi>. (P \<Phi> m\<and> \<box> (\<forall>(\<lambda>x. \<Phi> x m\<rightarrow> \<Psi> x))) m\<rightarrow> P \<Psi>))]"

text \<open>We prove theorem T1: $\all \phi [P(\phi) \imp \pos \ex x \phi(x)]$ (Positive 
properties are possibly exemplified). T1 is proved directly by Sledgehammer with command \<open>sledgehammer [provers = remote_leo2]\<close>. 
Sledgehammer suggests to call Metis with axioms A1a and A2. 
Metis sucesfully generates a proof object 
that is verified in Isabelle/HOL's kernel.\<close>
 
  theorem T1: "[\<forall>(\<lambda>\<Phi>. P \<Phi> m\<rightarrow> \<diamond> (\<exists> \<Phi>))]"  
  \<comment> \<open>sledgehammer [provers = remote\_leo2]\<close>
  by (metis A1a A2)

text \<open>Next, the symbol \<open>G\<close> for `God-like'  is introduced and defined 
as $G(x) \biimp \forall \phi [P(\phi) \to \phi(x)]$ \\ (A God-like being possesses 
all positive properties).\<close> 

  definition G :: "\<mu> \<Rightarrow> \<sigma>" where "G = (\<lambda>x. \<forall>(\<lambda>\<Phi>. P \<Phi> m\<rightarrow> \<Phi> x))"   

text \<open>Axiom \<open>A3\<close> is added: $P(G)$ (The property of being God-like is positive).
Sledgehammer and Metis then prove corollary \<open>C\<close>: $\pos \ex x G(x)$ 
(Possibly, God exists).\<close> 
 
  axiomatization where A3:  "[P G]" 

  corollary C: "[\<diamond> (\<exists> G)]" 
  \<comment> \<open>sledgehammer [provers = remote\_leo2]\<close>
  by (metis A3 T1)

text \<open>Axiom \<open>A4\<close> is added: $\all \phi [P(\phi) \to \Box \; P(\phi)]$ 
(Positive properties are necessarily positive).\<close>

  axiomatization where A4:  "[\<forall>(\<lambda>\<Phi>. P \<Phi> m\<rightarrow> \<box> (P \<Phi>))]" 

text \<open>Symbol \<open>ess\<close> for `Essence' is introduced and defined as 
$$\ess{\phi}{x} \biimp \phi(x) \wedge \all \psi (\psi(x) \imp \nec \all y (\phi(y) 
\imp \psi(y)))$$ (An \emph{essence} of an individual is a property possessed by it and necessarily implying any of its properties).\<close>

  definition ess :: "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<mu> \<Rightarrow> \<sigma>" (infixr "ess" 85) where
    "\<Phi> ess x = \<Phi> x m\<and> \<forall>(\<lambda>\<Psi>. \<Psi> x m\<rightarrow> \<box> (\<forall>(\<lambda>y. \<Phi> y m\<rightarrow> \<Psi> y)))"

text \<open>Next, Sledgehammer and Metis prove theorem \<open>T2\<close>: $\all x [G(x) \imp \ess{G}{x}]$ \\
(Being God-like is an essence of any God-like being).\<close>

  theorem T2: "[\<forall>(\<lambda>x. G x m\<rightarrow> G ess x)]"
  \<comment> \<open>sledgehammer [provers = remote\_leo2]\<close>
  by (metis A1b A4 G_def ess_def)

text \<open>Symbol \<open>NE\<close>, for `Necessary Existence', is introduced and
defined as $$\NE(x) \biimp \all \phi [\ess{\phi}{x} \imp \nec \ex y \phi(y)]$$ (Necessary 
existence of an individual is the necessary exemplification of all its essences).\<close>

  definition NE :: "\<mu> \<Rightarrow> \<sigma>" where "NE = (\<lambda>x. \<forall>(\<lambda>\<Phi>. \<Phi> ess x m\<rightarrow> \<box> (\<exists> \<Phi>)))"

text \<open>Moreover, axiom \<open>A5\<close> is added: $P(\NE)$ (Necessary existence is a positive 
property).\<close>

  axiomatization where A5:  "[P NE]"

text \<open>The \<open>B\<close> axiom (symmetry) for relation r is stated. \<open>B\<close> is needed only 
for proving theorem T3 and for corollary C2.\<close>

  axiomatization where sym: "x r y \<longrightarrow> y r x" 

text \<open>Finally, Sledgehammer and Metis prove the main theorem \<open>T3\<close>: $\nec \ex x G(x)$ \\
(Necessarily, God exists).\<close>

  theorem T3: "[\<box> (\<exists> G)]" 
  \<comment> \<open>sledgehammer [provers = remote\_leo2]\<close>
  by (metis A5 C T2 sym G_def NE_def)

text \<open>Surprisingly, the following corollary can be derived even without the \<open>T\<close> axiom 
(reflexivity).\<close>

  corollary C2: "[\<exists> G]" 
  \<comment> \<open>sledgehammer [provers = remote\_leo2]\<close>
  by (metis T1 T3 G_def sym)

text \<open>The consistency of the entire theory is confirmed by Nitpick.\<close>

  lemma True nitpick [satisfy, user_axioms, expect = genuine] oops


section \<open>Additional Results on G\"odel's God.\<close>  

text \<open>G\"odel's God is flawless: (s)he does not have non-positive properties.\<close>

  theorem Flawlessness: "[\<forall>(\<lambda>\<Phi>. \<forall>(\<lambda>x. (G x m\<rightarrow> (m\<not> (P \<Phi>) m\<rightarrow> m\<not> (\<Phi> x)))))]"
  \<comment> \<open>sledgehammer [provers = remote\_leo2]\<close>
  by (metis A1b G_def) 
  
text \<open>There is only one God: any two God-like beings are equal.\<close>   
  
  theorem Monotheism: "[\<forall>(\<lambda>x.\<forall>(\<lambda>y. (G x m\<rightarrow> (G y m\<rightarrow> (x mL= y)))))]"
  \<comment> \<open>sledgehammer [provers = remote\_leo2]\<close>
  by (metis Flawlessness G_def) 

section \<open>Modal Collapse\<close>  

text \<open>G\"odel's axioms have been criticized for entailing the so-called 
modal collapse. The prover Satallax \cite{Satallax} confirms this. 
However, sledgehammer is not able to determine which axioms, 
definitions and previous theorems are used by Satallax;
hence it suggests to call Metis using everything, but this (unsurprinsingly) fails.
Attempting to use `Sledegehammer min' to minimize Sledgehammer's suggestion does not work.
Calling Metis with \<open>T2\<close>, \<open>T3\<close> and \<open>ess_def\<close> also does not work.\<close> 

  lemma MC: "[\<forall>(\<lambda>\<Phi>.(\<Phi> m\<rightarrow> (\<box> \<Phi>)))]"  
  \<comment> \<open>sledgehammer [provers = remote\_satallax]\<close>
  \<comment> \<open>by (metis T2 T3 ess\_def)\<close>
  oops
(*<*) 
end
(*>*) 
