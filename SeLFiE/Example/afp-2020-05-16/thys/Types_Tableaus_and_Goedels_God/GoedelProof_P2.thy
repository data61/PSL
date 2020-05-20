(*<*)
theory GoedelProof_P2
imports IHOML
begin
nitpick_params[user_axioms=true, show_all, expect=genuine, format = 3,  atoms e = a b c d]
sledgehammer_params[verbose=true]
(*>*)
  
subsection \<open>Part II - God's Existence is Necessary if Possible\<close>
  
text\<open>  We show here that God's necessary existence follows from its possible existence by adding some
 additional (potentially controversial) assumptions including an \emph{essentialist} premise 
 and the \emph{S5} axioms.
 Further results like monotheism and the rejection of free will (\emph{modal collapse}) are also proved.
  \<close>

subsubsection \<open>General Definitions\<close>
  
abbreviation existencePredicate::"\<up>\<langle>\<zero>\<rangle>" ("E!") where
  "E! x  \<equiv> (\<lambda>w. (\<^bold>\<exists>\<^sup>Ey. y\<^bold>\<approx>x) w)" 
  
consts positiveProperty::"\<up>\<langle>\<up>\<langle>\<zero>\<rangle>\<rangle>" ("\<P>")
  
abbreviation God::"\<up>\<langle>\<zero>\<rangle>" ("G") where "G \<equiv> (\<lambda>x. \<^bold>\<forall>Y. \<P> Y \<^bold>\<rightarrow> Y x)"
abbreviation God_star::"\<up>\<langle>\<zero>\<rangle>" ("G*") where
  "G* \<equiv> (\<lambda>x. \<^bold>\<forall>Y. \<P> Y \<^bold>\<leftrightarrow> Y x)"
  
abbreviation Entailment::"\<up>\<langle>\<up>\<langle>\<zero>\<rangle>,\<up>\<langle>\<zero>\<rangle>\<rangle>" (infix "\<Rrightarrow>" 60) where 
  "X \<Rrightarrow> Y \<equiv>  \<^bold>\<box>(\<^bold>\<forall>\<^sup>Ez. X z \<^bold>\<rightarrow> Y z)"

subsubsection \<open>Results from Part I\<close> 
  
text\<open>  Note that the only use G\"odel makes of axiom A3 is to show that being Godlike is a positive property (\emph{T2}). 
 We follow therefore Scott's proposal and take (\emph{T2}) directly as an axiom:  \<close>  
axiomatization where
  A1a:"\<lfloor>\<^bold>\<forall>X. \<P> (\<^bold>\<rightharpoondown>X) \<^bold>\<rightarrow> \<^bold>\<not>(\<P> X) \<rfloor>" and          \<comment> \<open>axiom 11.3A\<close>
  A1b:"\<lfloor>\<^bold>\<forall>X. \<^bold>\<not>(\<P> X) \<^bold>\<rightarrow> \<P> (\<^bold>\<rightharpoondown>X)\<rfloor>" and           \<comment> \<open>axiom 11.3B\<close>
  A2: "\<lfloor>\<^bold>\<forall>X Y. (\<P> X \<^bold>\<and> (X \<Rrightarrow> Y)) \<^bold>\<rightarrow> \<P> Y\<rfloor>" and    \<comment> \<open>axiom 11.5\<close>
  T2: "\<lfloor>\<P> G\<rfloor>"                                  \<comment> \<open>proposition 11.16\<close>
        
lemma True nitpick[satisfy] oops \<comment> \<open>model found: axioms are consistent\<close>
    
lemma "\<lfloor>D\<rfloor>"  using A1a A1b A2 by blast \<comment> \<open>axioms already imply \emph{D} axiom\<close>
    
lemma GodDefsAreEquivalent: "\<lfloor>\<^bold>\<forall>x. G x \<^bold>\<leftrightarrow> G* x\<rfloor>" using A1b by fastforce 
    
theorem T1: "\<lfloor>\<^bold>\<forall>X. \<P> X \<^bold>\<rightarrow> \<^bold>\<diamond>\<^bold>\<exists>\<^sup>E X\<rfloor>" 
  using A1a A2 by blast  \<comment> \<open>positive properties are possibly instantiated\<close>  
theorem T3: "\<lfloor>\<^bold>\<diamond>\<^bold>\<exists>\<^sup>E G\<rfloor>" using T1 T2 by simp  \<comment> \<open>God exists possibly\<close>  
    
subsubsection \<open>Axioms\<close>
        
text\<open>  \<open>\<P>\<close> satisfies the so-called stability conditions (see @{cite "Fitting"}, p. 124), which means
 it designates rigidly (note that this makes for an \emph{essentialist} assumption). \<close>
axiomatization where
      A4a: "\<lfloor>\<^bold>\<forall>X. \<P> X \<^bold>\<rightarrow> \<^bold>\<box>(\<P> X)\<rfloor>"      \<comment> \<open>axiom 11.11\<close>
lemma A4b: "\<lfloor>\<^bold>\<forall>X. \<^bold>\<not>(\<P> X) \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<not>(\<P> X)\<rfloor>" using A1a A1b A4a by blast
    
abbreviation rigidPred::"('t\<Rightarrow>io)\<Rightarrow>io" where
 "rigidPred \<tau> \<equiv> (\<lambda>\<beta>. \<^bold>\<box>((\<lambda>z. \<beta> \<^bold>\<approx> z) \<^bold>\<down>\<tau>)) \<^bold>\<down>\<tau>"
 
lemma "\<lfloor>rigidPred \<P>\<rfloor>" 
  using A4a A4b by blast \<comment> \<open>@{term "\<P>"} is therefore rigid\<close>
    
lemma True nitpick[satisfy] oops \<comment> \<open>model found: so far all axioms A1-4 consistent\<close>    
text\<open> \bigbreak \<close>   
    
subsubsection \<open>Theorems\<close>
text\<open>  Remark: Essence is defined here (and in Fitting's variant) in the version of Scott; G\"odel's original version leads to the inconsistency
 reported in @{cite C55 and C60} \<close>

abbreviation essenceOf::"\<up>\<langle>\<up>\<langle>\<zero>\<rangle>,\<zero>\<rangle>" ("\<E>") where
  "\<E> Y x \<equiv> (Y x) \<^bold>\<and> (\<^bold>\<forall>Z. Z x \<^bold>\<rightarrow> Y \<Rrightarrow> Z)"   
abbreviation beingIdenticalTo::"\<zero>\<Rightarrow>\<up>\<langle>\<zero>\<rangle>" ("id") where
  "id x  \<equiv> (\<lambda>y. y\<^bold>\<approx>x)"  \<comment> \<open>note that \emph{id} is a rigid predicate\<close>  

text\<open>  Theorem 11.20 - Informal Proposition 5  \<close>
theorem GodIsEssential: "\<lfloor>\<^bold>\<forall>x. G x \<^bold>\<rightarrow> (\<E> G x)\<rfloor>" using A1b A4a by metis
    
text\<open>  Theorem 11.21  \<close>
theorem "\<lfloor>\<^bold>\<forall>x. G* x \<^bold>\<rightarrow> (\<E> G* x)\<rfloor>" using A4a by meson             
    
text\<open>  Theorem 11.22 - Something can have only one essence:  \<close>
theorem "\<lfloor>\<^bold>\<forall>X Y z. (\<E> X z \<^bold>\<and> \<E> Y z) \<^bold>\<rightarrow> (X \<Rrightarrow> Y)\<rfloor>" by meson  
  
text\<open>  Theorem 11.23 - An essence is a complete characterization of an individual:  \<close>
theorem EssencesCharacterizeCompletely: "\<lfloor>\<^bold>\<forall>X y. \<E> X y \<^bold>\<rightarrow> (X \<Rrightarrow> (id y))\<rfloor>"
proof (rule ccontr)
  assume "\<not> \<lfloor>\<^bold>\<forall>X y. \<E> X y \<^bold>\<rightarrow> (X \<Rrightarrow> (id y))\<rfloor>"
  hence "\<exists>w. \<not>(( \<^bold>\<forall>X y. \<E> X y \<^bold>\<rightarrow> X \<Rrightarrow> id y) w)" by simp
  then obtain w where "\<not>(( \<^bold>\<forall>X y. \<E> X y \<^bold>\<rightarrow> X \<Rrightarrow> id y) w)" ..
  hence "(\<^bold>\<exists>X y. \<E> X y \<^bold>\<and> \<^bold>\<not>(X \<Rrightarrow> id y)) w" by simp
  hence "\<exists>X y. \<E> X y w \<and> (\<^bold>\<not>(X \<Rrightarrow> id y)) w" by simp
  then obtain P where "\<exists>y. \<E> P y w \<and> (\<^bold>\<not>(P \<Rrightarrow> id y)) w" ..
  then obtain a where 1: "\<E> P a w \<and> (\<^bold>\<not>(P \<Rrightarrow> id a)) w" ..
  hence 2: "\<E> P a w" by (rule conjunct1)
  from 1 have "(\<^bold>\<not>(P \<Rrightarrow> id a)) w" by (rule conjunct2)
  hence "\<exists>x. \<exists>z. w r x \<and>  existsAt z x \<and> P z x \<and> \<not>(a = z)" by blast
  then obtain w1 where "\<exists>z. w r w1 \<and>  existsAt z w1 \<and> P z w1 \<and> \<not>(a = z)" ..
  then obtain b where 3: "w r w1 \<and>  existsAt b w1 \<and> P b w1 \<and> \<not>(a = b)" ..
  hence "w r w1" by simp
  from 3 have "existsAt b w1" by simp
  from 3 have "P b w1" by simp
  from 3 have 4: " \<not>(a = b)" by simp
  from 2 have "P a w" by simp
  from 2 have "\<forall>Y. Y a w \<longrightarrow> ((P \<Rrightarrow> Y) w)" by auto
  hence "(\<^bold>\<rightharpoondown>(id b)) a w \<longrightarrow> (P \<Rrightarrow> (\<^bold>\<rightharpoondown>(id b))) w" by (rule allE)
  hence "\<not>(\<^bold>\<rightharpoondown>(id b)) a w \<or> ((P \<Rrightarrow> (\<^bold>\<rightharpoondown>(id b))) w)" by blast 
  then show False proof
    assume "\<not>(\<^bold>\<rightharpoondown>(id b)) a w"
    hence "a = b" by simp
    thus False using 4 by auto
    next  
    assume "((P \<Rrightarrow> (\<^bold>\<rightharpoondown>(id b))) w)"
    hence "\<forall>x. \<forall>z. (w r x \<and> existsAt z x \<and> P z x) \<longrightarrow> (\<^bold>\<rightharpoondown>(id b)) z x" by blast
    hence "\<forall>z. (w r w1 \<and> existsAt z w1 \<and> P z w1) \<longrightarrow> (\<^bold>\<rightharpoondown>(id b)) z w1" 
        by (rule allE)
    hence "(w r w1 \<and> existsAt b w1 \<and> P b w1) \<longrightarrow> (\<^bold>\<rightharpoondown>(id b)) b w1" by (rule allE)
    hence  "\<not>(w r w1 \<and> existsAt b w1 \<and> P b w1) \<or> (\<^bold>\<rightharpoondown>(id b)) b w1" by simp
    hence "(\<^bold>\<rightharpoondown>(id b)) b w" using 3 by simp
    hence "\<not>(b=b)" by simp
    thus False by simp
  qed
qed

text\<open>  Definition 11.24 - Necessary Existence (Informal Definition 6):  \<close>  
abbreviation necessaryExistencePred::"\<up>\<langle>\<zero>\<rangle>" ("NE") 
  where "NE x  \<equiv> (\<lambda>w. (\<^bold>\<forall>Y.  \<E> Y x \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<exists>\<^sup>E Y) w)"

text\<open>  Axiom 11.25 (Informal Axiom 5) \<close>
axiomatization where 
 A5: "\<lfloor>\<P> NE\<rfloor>"
 
lemma True nitpick[satisfy] oops \<comment> \<open>model found: so far all axioms consistent\<close>
 
text\<open>  Theorem 11.26 (Informal Proposition 7) - Possibilist existence of God implies necessary actualist existence:  \<close> 
theorem GodExistenceImpliesNecExistence: "\<lfloor>\<^bold>\<exists> G \<^bold>\<rightarrow>  \<^bold>\<box>\<^bold>\<exists>\<^sup>E G\<rfloor>"
proof -
{
  fix w 
  {
    assume "\<exists>x. G x w"
    then obtain g where 1: "G g w" ..
    hence "NE g w" using A5 by auto                     \<comment> \<open>axiom 11.25\<close>
    hence "\<forall>Y. (\<E> Y g w) \<longrightarrow> (\<^bold>\<box>\<^bold>\<exists>\<^sup>E Y) w" by simp
    hence 2: "(\<E> G g w) \<longrightarrow> (\<^bold>\<box>\<^bold>\<exists>\<^sup>E G) w" by (rule allE)
    have  "(\<^bold>\<forall>x. G x \<^bold>\<rightarrow> (\<E> G x)) w" using GodIsEssential
      by (rule allE)     \<comment> \<open>GodIsEssential follows from Axioms 11.11 and 11.3B\<close>
    hence  "(G g \<^bold>\<rightarrow> (\<E> G g)) w" by (rule allE)
    hence  "G g w \<longrightarrow> \<E> G g w" by simp
    from this 1 have 3: "\<E> G g w" by (rule mp)
    from 2 3 have "(\<^bold>\<box>\<^bold>\<exists>\<^sup>E G) w" by (rule mp)
  }
  hence "(\<exists>x. G x w) \<longrightarrow> (\<^bold>\<box>\<^bold>\<exists>\<^sup>E G) w" by (rule impI)
  hence "((\<^bold>\<exists>x. G x) \<^bold>\<rightarrow>  \<^bold>\<box>\<^bold>\<exists>\<^sup>E G) w" by simp
}
 thus ?thesis by (rule allI) 
qed
  
text\<open>  \emph{Modal collapse} is countersatisfiable (unless we introduce S5 axioms): \<close>
lemma "\<lfloor>\<^bold>\<forall>\<Phi>.(\<Phi> \<^bold>\<rightarrow> (\<^bold>\<box> \<Phi>))\<rfloor>" nitpick oops
  
text\<open>  We postulate semantic frame conditions for some modal logics. Taken together, reflexivity, transitivity and symmetry
 make for an equivalence relation and therefore an \emph{S5} logic (via \emph{Sahlqvist correspondence}).
 We prefer to postulate them individually here in order to get more detailed information about their relevance 
 in the proofs presented below. \<close>
axiomatization where
 refl: "reflexive aRel" and
 tran: "transitive aRel" and
 symm: "symmetric aRel"
 
lemma True nitpick[satisfy] oops \<comment> \<open>model found: axioms still consistent\<close>
text\<open>  Using an \emph{S5} logic, \emph{modal collapse} (\<open>\<lfloor>\<^bold>\<forall>\<Phi>.(\<Phi> \<^bold>\<rightarrow> (\<^bold>\<box> \<Phi>))\<rfloor>\<close>) is actually valid (see `More Objections' some pages below) \<close>
    
text\<open>  We prove some useful inference rules: \<close>    
lemma modal_distr: "\<lfloor>\<^bold>\<box>(\<phi> \<^bold>\<rightarrow> \<psi>)\<rfloor> \<Longrightarrow> \<lfloor>(\<^bold>\<diamond>\<phi> \<^bold>\<rightarrow> \<^bold>\<diamond>\<psi>)\<rfloor>" by blast
lemma modal_trans: "(\<lfloor>\<phi> \<^bold>\<rightarrow> \<psi>\<rfloor> \<and> \<lfloor>\<psi> \<^bold>\<rightarrow> \<chi>\<rfloor>) \<Longrightarrow> \<lfloor>\<phi> \<^bold>\<rightarrow> \<chi>\<rfloor>" by simp

text\<open>  Theorem 11.27 - Informal Proposition 8. Note that only symmetry and transitivity for the accessibility relation are used. \<close> 
theorem possExistenceImpliesNecEx: "\<lfloor>\<^bold>\<diamond>\<^bold>\<exists> G \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<exists>\<^sup>E G\<rfloor>" \<comment> \<open>local consequence\<close>
proof -
  have "\<lfloor>\<^bold>\<exists> G \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<exists>\<^sup>E G\<rfloor>" using GodExistenceImpliesNecExistence 
    by simp \<comment> \<open>follows from Axioms 11.11, 11.25 and 11.3B\<close>
  hence "\<lfloor>\<^bold>\<box>(\<^bold>\<exists> G \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<exists>\<^sup>E G)\<rfloor>" using NEC by simp
  hence 1: "\<lfloor>\<^bold>\<diamond>\<^bold>\<exists> G \<^bold>\<rightarrow> \<^bold>\<diamond>\<^bold>\<box>\<^bold>\<exists>\<^sup>E G\<rfloor>" by (rule modal_distr)
  have 2: "\<lfloor>\<^bold>\<diamond>\<^bold>\<box>\<^bold>\<exists>\<^sup>E G \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<exists>\<^sup>E G\<rfloor>" using symm tran by metis \<comment> \<open>frame conditions\<close>
  from 1 2 have "\<lfloor>\<^bold>\<diamond>\<^bold>\<exists> G \<^bold>\<rightarrow> \<^bold>\<diamond>\<^bold>\<box>\<^bold>\<exists>\<^sup>E G\<rfloor> \<and> \<lfloor>\<^bold>\<diamond>\<^bold>\<box>\<^bold>\<exists>\<^sup>E G \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<exists>\<^sup>E G\<rfloor>" by simp
  thus ?thesis by (rule modal_trans)
qed

lemma T4: "\<lfloor>\<^bold>\<diamond>\<^bold>\<exists> G\<rfloor> \<longrightarrow> \<lfloor>\<^bold>\<box>\<^bold>\<exists>\<^sup>E G\<rfloor>" using possExistenceImpliesNecEx 
    by (rule localImpGlobalCons)  \<comment> \<open>global consequence\<close>
  
text\<open>  Corollary 11.28 - Necessary (actualist) existence of God (for both definitions); reflexivity is still not used:  \<close>    
lemma GodNecExists: "\<lfloor>\<^bold>\<box>\<^bold>\<exists>\<^sup>E G\<rfloor>" using T3 T4 by metis    
lemma God_starNecExists: "\<lfloor>\<^bold>\<box>\<^bold>\<exists>\<^sup>E G*\<rfloor>" 
  using GodNecExists GodDefsAreEquivalent by simp
    

subsubsection \<open>Monotheism\<close>
 
text\<open>  Monotheism for non-normal models (with Leibniz equality) follows directly from God having all and only positive properties:  \<close>
theorem Monotheism_LeibnizEq: "\<lfloor>\<^bold>\<forall>x. G x \<^bold>\<rightarrow> (\<^bold>\<forall>y. G y \<^bold>\<rightarrow> (x  \<^bold>\<approx>\<^sup>L y))\<rfloor>" 
  using GodDefsAreEquivalent by simp
    
text\<open>  Monotheism for normal models is trickier. We need to consider some previous results (p. 162): \<close>
    
lemma GodExistenceIsValid: "\<lfloor>\<^bold>\<exists>\<^sup>E G\<rfloor>" using GodNecExists refl
  by auto \<comment> \<open>reflexivity is now required by the solver\<close>
        
text\<open>  Proposition 11.29:  \<close>
theorem Monotheism_normalModel: "\<lfloor>\<^bold>\<exists>x.\<^bold>\<forall>y. G y \<^bold>\<leftrightarrow> x \<^bold>\<approx> y\<rfloor>"
proof -
{
  fix w 
  have "\<lfloor>\<^bold>\<exists>\<^sup>E G\<rfloor>" using GodExistenceIsValid by simp \<comment> \<open>follows from corollary 11.28\<close>
  hence "(\<^bold>\<exists>\<^sup>E G) w" by (rule allE)       
  then obtain g where 1: "existsAt g w \<and> G g w" ..
  hence 2: "\<E> G g w" using GodIsEssential by blast \<comment> \<open>follows from ax. 11.11/11.3B\<close>
  {
    fix y
    have "G y w \<longleftrightarrow> (g \<^bold>\<approx> y) w" proof 
      assume "G y w"
      hence 3: "\<E> G y w" using GodIsEssential by blast      
      have "(\<E> G y \<^bold>\<rightarrow> (G \<Rrightarrow> id y)) w" using EssencesCharacterizeCompletely
        by simp \<comment> \<open>follows from theorem 11.23\<close>
      hence "\<E> G y w \<longrightarrow> ((G \<Rrightarrow> id y) w)" by simp
      from this 3 have "(G \<Rrightarrow> id y) w" by (rule mp) 
      hence "(\<^bold>\<box>(\<^bold>\<forall>\<^sup>Ez. G z \<^bold>\<rightarrow> z \<^bold>\<approx> y)) w" by simp
      hence "\<forall>x. w r x \<longrightarrow> ((\<forall>z. (existsAt z x \<and> G z x) \<longrightarrow> z = y))" by auto
      hence "w r w \<longrightarrow> ((\<forall>z. (existsAt z w \<and> G z w) \<longrightarrow> z = y))" by (rule allE)
      hence "\<forall>z. (w r w \<and> existsAt z w \<and> G z w) \<longrightarrow> z = y" by auto
      hence 4: "(w r w \<and> existsAt g w \<and> G g w) \<longrightarrow> g = y" by (rule allE)
      have "w r w" using refl 
        by simp \<comment> \<open>using frame reflexivity (Axiom M)\<close>
      hence  "w r w \<and> (existsAt g w \<and> G g w)" using 1 by (rule conjI)
      from 4 this have "g = y" by (rule mp)
      thus "(g \<^bold>\<approx> y) w" by simp
    next
      assume "(g \<^bold>\<approx> y) w"
      from this 2 have "\<E> G y w" by simp
      thus "G y w " by (rule conjunct1)
    qed
  }
  hence "\<forall>y. G y w \<longleftrightarrow> (g \<^bold>\<approx> y) w" by (rule allI) 
  hence "\<exists>x. (\<forall>y. G y w \<longleftrightarrow> (x \<^bold>\<approx> y) w)" by (rule exI) 
  hence "(\<^bold>\<exists>x. (\<^bold>\<forall>y. G y \<^bold>\<leftrightarrow> (x \<^bold>\<approx> y))) w" by simp
}
thus ?thesis by (rule allI) 
qed
text\<open> \bigbreak \<close>  
text\<open> Corollary 11.30:  \<close>
lemma GodImpliesExistence: "\<lfloor>\<^bold>\<forall>x. G x \<^bold>\<rightarrow> E! x\<rfloor>" 
  using GodExistenceIsValid Monotheism_normalModel by metis

subsubsection \<open>Positive Properties are Necessarily Instantiated\<close>
  
lemma PosPropertiesNecExist: "\<lfloor>\<^bold>\<forall>Y. \<P> Y \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<exists>\<^sup>E Y\<rfloor>" using GodNecExists A4a
  by meson \<comment> \<open>proposition 11.31: follows from corollary 11.28 and axiom A4a\<close>
 
    
subsubsection \<open>More Objections\<close>
text\<open>  Fitting discusses the objection raised by Sobel @{cite "sobel2004logic"}, who argues that G\"odel's axiom system
 is too strong: it implies that whatever is the case is so necessarily, i.e. the modal system collapses (\<open>\<phi> \<longrightarrow> \<box>\<phi>\<close>).
 The \emph{modal collapse} has been philosophically interpreted as implying the absence of free will. \<close>

text\<open>  We start by proving an useful FOL lemma: \<close>  
lemma useful: "(\<forall>x. \<phi> x \<longrightarrow> \<psi>) \<Longrightarrow> ((\<exists>x. \<phi> x) \<longrightarrow> \<psi>)" by simp
    
text\<open>  In the context of our S5 axioms, the \emph{modal collapse} becomes valid (pp. 163-4):  \<close>     
lemma ModalCollapse: "\<lfloor>\<^bold>\<forall>\<Phi>.(\<Phi> \<^bold>\<rightarrow> (\<^bold>\<box> \<Phi>))\<rfloor>"
proof -
  {
  fix w
   {
    fix Q
    have "(\<^bold>\<forall>x. G x \<^bold>\<rightarrow> (\<E> G x)) w" using GodIsEssential 
      by (rule allE) \<comment> \<open>follows from Axioms 11.11 and 11.3B\<close>
    hence "\<forall>x. G x w \<longrightarrow> \<E> G x w" by simp
    hence "\<forall>x. G x w \<longrightarrow> (\<^bold>\<forall>Z. Z x \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<forall>\<^sup>Ez. G z \<^bold>\<rightarrow> Z z)) w" by force
    hence "\<forall>x. G x w \<longrightarrow> ((\<lambda>y. Q) x \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<forall>\<^sup>Ez. G z \<^bold>\<rightarrow> (\<lambda>y. Q) z)) w" by force
    hence "\<forall>x. G x w \<longrightarrow> (Q \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<forall>\<^sup>Ez. G z \<^bold>\<rightarrow> Q)) w" by simp
    hence 1: "(\<exists>x. G x w) \<longrightarrow> ((Q \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<forall>\<^sup>Ez. G z \<^bold>\<rightarrow> Q)) w)" by (rule useful)
    have "\<exists>x. G x w" using GodExistenceIsValid by auto
    from 1 this have "(Q \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<forall>\<^sup>Ez. G z \<^bold>\<rightarrow> Q)) w" by (rule mp)
    hence "(Q \<^bold>\<rightarrow> \<^bold>\<box>((\<^bold>\<exists>\<^sup>Ez. G z) \<^bold>\<rightarrow> Q)) w" using useful by blast
    hence "(Q \<^bold>\<rightarrow> (\<^bold>\<box>(\<^bold>\<exists>\<^sup>Ez. G z) \<^bold>\<rightarrow> \<^bold>\<box>Q)) w" by simp
    hence "(Q \<^bold>\<rightarrow> \<^bold>\<box>Q) w" using GodNecExists by simp
   }
  hence "(\<^bold>\<forall>\<Phi>. \<Phi> \<^bold>\<rightarrow> \<^bold>\<box> \<Phi>) w" by (rule allI)
  }
  thus ?thesis by (rule allI)
qed
  text\<open>  \pagebreak \<close>

(*<*)
end
(*>*)
