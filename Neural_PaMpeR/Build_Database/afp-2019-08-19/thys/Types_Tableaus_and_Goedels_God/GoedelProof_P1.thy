(*<*)
theory GoedelProof_P1
imports IHOML
begin
nitpick_params[user_axioms=true, show_all, expect=genuine, format = 3,  atoms e = a b c d]
sledgehammer_params[verbose=true]
(*>*)  

section \<open>G\"odel's Argument, Formally\<close>

text\<open> 
 "G\"odel's particular version of the argument is a direct descendent of that of Leibniz, which in turn derives
  from one of Descartes. These arguments all have a two-part structure: prove God's existence is necessary,
  if possible; and prove God's existence is possible." @{cite "Fitting"}, p. 138. \<close> 

subsection \<open>Part I - God's Existence is Possible\<close>

text\<open>  We separate G\"odel's Argument as presented in Fitting's textbook (ch. 11) in two parts. For the first one, while Leibniz provides
  some kind of proof for the compatibility of all perfections, G\"odel goes on to prove an analogous result:
 \emph{(T1) Every positive property is possibly instantiated}, which together with \emph{(T2) God is a positive property}
  directly implies the conclusion. In order to prove \emph{T1}, G\"odel assumes \emph{A2: Any property entailed by a positive property is positive}. \<close>
text\<open>  We are currently contemplating a follow-up analysis of the philosophical implications of these axioms,
 which encompasses some criticism of the notion of \emph{property entailment} used by G\"odel throughout the argument. \<close>
  
subsubsection \<open>General Definitions\<close>
               
abbreviation existencePredicate::"\<up>\<langle>\<zero>\<rangle>" ("E!") 
  where "E! x  \<equiv> \<lambda>w. (\<^bold>\<exists>\<^sup>Ey. y\<^bold>\<approx>x) w" \<comment> \<open>existence predicate in object language\<close>
    
lemma "E! x w \<longleftrightarrow> existsAt x w" 
  by simp \<comment> \<open>safety check: @{text "E!"} correctly matches its meta-logical counterpart\<close>

consts positiveProperty::"\<up>\<langle>\<up>\<langle>\<zero>\<rangle>\<rangle>" ("\<P>") \<comment> \<open>positiveness/perfection\<close>
  
text\<open>  Definitions of God (later shown to be equivalent under axiom \emph{A1b}):  \<close>    
abbreviation God::"\<up>\<langle>\<zero>\<rangle>" ("G") where "G \<equiv> (\<lambda>x. \<^bold>\<forall>Y. \<P> Y \<^bold>\<rightarrow> Y x)"
abbreviation God_star::"\<up>\<langle>\<zero>\<rangle>" ("G*") where "G* \<equiv> (\<lambda>x. \<^bold>\<forall>Y. \<P> Y \<^bold>\<leftrightarrow> Y x)"
  
text\<open>  Definitions needed to formalise \emph{A3}:  \<close>
abbreviation appliesToPositiveProps::"\<up>\<langle>\<up>\<langle>\<up>\<langle>\<zero>\<rangle>\<rangle>\<rangle>" ("pos") where
  "pos Z \<equiv>  \<^bold>\<forall>X. Z X \<^bold>\<rightarrow> \<P> X"  
abbreviation intersectionOf::"\<up>\<langle>\<up>\<langle>\<zero>\<rangle>,\<up>\<langle>\<up>\<langle>\<zero>\<rangle>\<rangle>\<rangle>" ("intersec") where
  "intersec X Z \<equiv>  \<^bold>\<box>(\<^bold>\<forall>x.(X x \<^bold>\<leftrightarrow> (\<^bold>\<forall>Y. (Z Y) \<^bold>\<rightarrow> (Y x))))" \<comment> \<open>quantifier is possibilist\<close>  
abbreviation Entailment::"\<up>\<langle>\<up>\<langle>\<zero>\<rangle>,\<up>\<langle>\<zero>\<rangle>\<rangle>" (infix "\<Rrightarrow>" 60) where
  "X \<Rrightarrow> Y \<equiv>  \<^bold>\<box>(\<^bold>\<forall>\<^sup>Ez. X z \<^bold>\<rightarrow> Y z)"
text\<open> \bigbreak \<close>
  
subsubsection \<open>Axioms\<close>
    
axiomatization where
  A1a:"\<lfloor>\<^bold>\<forall>X. \<P> (\<^bold>\<rightharpoondown>X) \<^bold>\<rightarrow> \<^bold>\<not>(\<P> X) \<rfloor>" and      \<comment> \<open>axiom 11.3A\<close>
  A1b:"\<lfloor>\<^bold>\<forall>X. \<^bold>\<not>(\<P> X) \<^bold>\<rightarrow> \<P> (\<^bold>\<rightharpoondown>X)\<rfloor>" and       \<comment> \<open>axiom 11.3B\<close>
  A2: "\<lfloor>\<^bold>\<forall>X Y. (\<P> X \<^bold>\<and> (X \<Rrightarrow> Y)) \<^bold>\<rightarrow> \<P> Y\<rfloor>" and   \<comment> \<open>axiom 11.5\<close>
  A3: "\<lfloor>\<^bold>\<forall>Z X. (pos Z \<^bold>\<and> intersec X Z) \<^bold>\<rightarrow> \<P> X\<rfloor>" \<comment> \<open>axiom 11.10\<close>

lemma True nitpick[satisfy] oops       \<comment> \<open>model found: axioms are consistent\<close>
    
lemma "\<lfloor>D\<rfloor>"  using A1a A1b A2 by blast \<comment> \<open>axioms already imply \emph{D} axiom\<close>
lemma "\<lfloor>D\<rfloor>" using A1a A3 by metis

subsubsection \<open>Theorems\<close>
    
lemma "\<lfloor>\<^bold>\<exists>X. \<P> X\<rfloor>" using A1b by auto
lemma "\<lfloor>\<^bold>\<exists>X. \<P> X \<^bold>\<and>  \<^bold>\<diamond>\<^bold>\<exists>\<^sup>E X\<rfloor>" using A1a A1b A2 by metis
    
text\<open>  Being self-identical is a positive property:  \<close>
lemma "\<lfloor>(\<^bold>\<exists>X. \<P> X \<^bold>\<and>  \<^bold>\<diamond>\<^bold>\<exists>\<^sup>E X) \<^bold>\<rightarrow> \<P> (\<lambda>x w. x = x)\<rfloor>" using A2 by fastforce
    
text\<open>  Proposition 11.6  \<close>
lemma "\<lfloor>(\<^bold>\<exists>X. \<P> X) \<^bold>\<rightarrow> \<P> (\<lambda>x w. x = x)\<rfloor>" using A2 by fastforce
    
lemma "\<lfloor>\<P> (\<lambda>x w. x = x)\<rfloor>" using A1b A2  by blast
lemma "\<lfloor>\<P> (\<lambda>x w. x = x)\<rfloor>" using A3 by metis
                                
text\<open>  Being non-self-identical is a negative property: \<close>
lemma "\<lfloor>(\<^bold>\<exists>X. \<P> X  \<^bold>\<and> \<^bold>\<diamond>\<^bold>\<exists>\<^sup>E X) \<^bold>\<rightarrow>  \<P> (\<^bold>\<rightharpoondown> (\<lambda>x w. \<not>x = x))\<rfloor>" 
  using A2 by fastforce
    
lemma "\<lfloor>(\<^bold>\<exists>X. \<P> X) \<^bold>\<rightarrow>  \<P> (\<^bold>\<rightharpoondown> (\<lambda>x w. \<not>x = x))\<rfloor>" using A2 by fastforce
lemma "\<lfloor>(\<^bold>\<exists>X. \<P> X) \<^bold>\<rightarrow>  \<P> (\<^bold>\<rightharpoondown> (\<lambda>x w. \<not>x = x))\<rfloor>" using A3 by metis 

text\<open>  Proposition 11.7  \<close>
lemma "\<lfloor>(\<^bold>\<exists>X. \<P> X) \<^bold>\<rightarrow> \<^bold>\<not>\<P> ((\<lambda>x w. \<not>x = x))\<rfloor>"  using A1a A2 by blast
lemma "\<lfloor>\<^bold>\<not>\<P> (\<lambda>x w. \<not>x = x)\<rfloor>"  using A1a A2 by blast
 
text\<open>  Proposition 11.8 (Informal Proposition 1) - Positive properties are possibly instantiated:  \<close>
theorem T1: "\<lfloor>\<^bold>\<forall>X. \<P> X \<^bold>\<rightarrow> \<^bold>\<diamond>\<^bold>\<exists>\<^sup>E X\<rfloor>" using A1a A2 by blast
    
text\<open>  Proposition 11.14 - Both defs (\emph{God/God*}) are equivalent. For improved performance we may prefer to use one or the other:  \<close>
lemma GodDefsAreEquivalent: "\<lfloor>\<^bold>\<forall>x. G x \<^bold>\<leftrightarrow> G* x\<rfloor>" using A1b by force 

text\<open>  Proposition 11.15 - Possibilist existence of \emph{God} directly implies \emph{A1b}:  \<close>    
lemma "\<lfloor>\<^bold>\<exists> G* \<^bold>\<rightarrow> (\<^bold>\<forall>X. \<^bold>\<not>(\<P> X) \<^bold>\<rightarrow> \<P> (\<^bold>\<rightharpoondown>X))\<rfloor>" by meson

text\<open>  Proposition 11.16 - \emph{A3} implies \emph{P(G)} (local consequence):   \<close>   
lemma A3implT2_local: "\<lfloor>(\<^bold>\<forall>Z X. (pos Z \<^bold>\<and> intersec X Z) \<^bold>\<rightarrow> \<P> X) \<^bold>\<rightarrow> \<P> G\<rfloor>"
proof -
  {
  fix w
  have 1: "pos \<P> w" by simp
  have 2: "intersec G \<P> w" by simp
  {    
    assume "(\<^bold>\<forall>Z X. (pos Z \<^bold>\<and> intersec X Z) \<^bold>\<rightarrow> \<P> X) w"
    hence "(\<^bold>\<forall>X. ((pos \<P>) \<^bold>\<and> (intersec X \<P>)) \<^bold>\<rightarrow> \<P> X) w"  by (rule allE)   
    hence "(((pos \<P>) \<^bold>\<and> (intersec G \<P>)) \<^bold>\<rightarrow> \<P> G) w" by (rule allE)
    hence 3: "((pos \<P> \<^bold>\<and> intersec G \<P>) w) \<longrightarrow> \<P> G w" by simp
    hence 4: "((pos \<P>) \<^bold>\<and> (intersec G \<P>)) w" using 1 2 by simp
    from 3 4 have "\<P> G w" by (rule mp)
  }
  hence "(\<^bold>\<forall>Z X. (pos Z \<^bold>\<and> intersec X Z) \<^bold>\<rightarrow> \<P> X) w  \<longrightarrow> \<P> G w" by (rule impI)
  } 
  thus ?thesis by (rule allI)
qed    
    
text\<open>  \emph{A3} implies \<open>P(G)\<close> (as global consequence): \<close>
lemma A3implT2_global: "\<lfloor>\<^bold>\<forall>Z X. (pos Z \<^bold>\<and> intersec X Z) \<^bold>\<rightarrow> \<P> X\<rfloor> \<longrightarrow> \<lfloor>\<P> G\<rfloor>" 
  using A3implT2_local by (rule localImpGlobalCons) 
  
text\<open>  Being Godlike is a positive property. Note that this theorem can be axiomatized directly,
as noted by Dana Scott (see @{cite "Fitting"}, p. 152). We will do so for the second part. \<close>
theorem T2: "\<lfloor>\<P> G\<rfloor>" using A3implT2_global A3 by simp
  
text\<open>  Theorem 11.17 (Informal Proposition 3) - Possibly God exists: \<close>
theorem T3: "\<lfloor>\<^bold>\<diamond>\<^bold>\<exists>\<^sup>E G\<rfloor>"  using T1 T2 by simp

(*<*)
end
(*>*)
