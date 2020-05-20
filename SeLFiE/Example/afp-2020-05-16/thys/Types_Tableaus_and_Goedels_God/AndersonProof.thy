(*<*)
theory AndersonProof  
imports IHOML
begin
nitpick_params[user_axioms=true, show_all, expect=genuine, format = 4,  atoms e = a b c d]
sledgehammer_params[verbose=true]
(*>*)
  
section \<open>Anderson's Alternative\<close>
  
text\<open> In this final section, we verify Anderson's emendation of G\"odel's argument, as it is presented in the last
part of the textbook by Fitting (pp. 169-171). \<close>
  
subsection \<open>General Definitions\<close>
 
abbreviation existencePredicate::"\<up>\<langle>\<zero>\<rangle>" ("E!") 
  where "E! x  \<equiv> \<lambda>w. (\<^bold>\<exists>\<^sup>Ey. y\<^bold>\<approx>x) w"
  
consts positiveProperty::"\<up>\<langle>\<up>\<langle>\<zero>\<rangle>\<rangle>" ("\<P>")
  
abbreviation God::"\<up>\<langle>\<zero>\<rangle>" ("G\<^sup>A") where "G\<^sup>A \<equiv> \<lambda>x. \<^bold>\<forall>Y. (\<P> Y) \<^bold>\<leftrightarrow> \<^bold>\<box>(Y x)"
  
abbreviation Entailment::"\<up>\<langle>\<up>\<langle>\<zero>\<rangle>,\<up>\<langle>\<zero>\<rangle>\<rangle>" (infix "\<Rrightarrow>" 60) where
  "X \<Rrightarrow> Y \<equiv>  \<^bold>\<box>(\<^bold>\<forall>\<^sup>Ez. X z \<^bold>\<rightarrow> Y z)"
  
subsection \<open>Part I - God's Existence is Possible\<close>  
  
axiomatization where
  A1a:"\<lfloor>\<^bold>\<forall>X. \<P> (\<^bold>\<rightharpoondown>X) \<^bold>\<rightarrow> \<^bold>\<not>(\<P> X) \<rfloor>" and          \<comment> \<open>Axiom 11.3A\<close>
  A2: "\<lfloor>\<^bold>\<forall>X Y. (\<P> X \<^bold>\<and> (X \<Rrightarrow> Y)) \<^bold>\<rightarrow> \<P> Y\<rfloor>" and   \<comment> \<open>Axiom 11.5\<close>
  T2: "\<lfloor>\<P> G\<^sup>A\<rfloor>"                                 \<comment> \<open>Proposition 11.16\<close>
        
lemma True nitpick[satisfy] oops \<comment> \<open>model found: axioms are consistent\<close>
    
theorem T1: "\<lfloor>\<^bold>\<forall>X. \<P> X \<^bold>\<rightarrow> \<^bold>\<diamond>\<^bold>\<exists>\<^sup>E X\<rfloor>" 
  using A1a A2 by blast  \<comment> \<open>positive properties are possibly instantiated\<close>  
theorem T3: "\<lfloor>\<^bold>\<diamond>\<^bold>\<exists>\<^sup>E G\<^sup>A\<rfloor>" using T1 T2 by simp  \<comment> \<open>God exists possibly\<close>  
    
    
subsection \<open>Part II - God's Existence is Necessary if Possible\<close>
        
text\<open>  \<open>\<P>\<close> now satisfies only one of the stability conditions. But since the argument uses an \emph{S5} logic, 
the other stability condition is implied. Therefore \<open>\<P>\<close> becomes rigid (see p. 124).  \<close>
axiomatization where
  A4a: "\<lfloor>\<^bold>\<forall>X. \<P> X \<^bold>\<rightarrow> \<^bold>\<box>(\<P> X)\<rfloor>"      \<comment> \<open>axiom 11.11\<close>
      
text\<open>  We again postulate our \emph{S5} axioms: \<close>
axiomatization where
 refl: "reflexive aRel" and
 tran: "transitive aRel" and
 symm: "symmetric aRel"
 
lemma True nitpick[satisfy] oops \<comment> \<open>model found: so far all axioms consistent\<close>
 
abbreviation rigidPred::"('t\<Rightarrow>io)\<Rightarrow>io" where
 "rigidPred \<tau> \<equiv> (\<lambda>\<beta>. \<^bold>\<box>((\<lambda>z. \<beta> \<^bold>\<approx> z) \<^bold>\<down>\<tau>)) \<^bold>\<down>\<tau>"

lemma A4b: "\<lfloor>\<^bold>\<forall>X. \<^bold>\<not>(\<P> X) \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<not>(\<P> X)\<rfloor>" 
  using A4a symm by auto \<comment> \<open>symmetry is needed (which corresponds to \emph{B} axiom)\<close>
lemma "\<lfloor>rigidPred \<P>\<rfloor>" 
  using A4a A4b by blast \<comment> \<open>@{text "\<P>"} is therefore rigid in a \emph{B} logic\<close>

text\<open>  Essence, Anderson Version (Definition 11.34) \<close>
abbreviation essenceOf::"\<up>\<langle>\<up>\<langle>\<zero>\<rangle>,\<zero>\<rangle>" ("\<E>\<^sup>A") where
  "\<E>\<^sup>A Y x \<equiv> (\<^bold>\<forall>Z. \<^bold>\<box>(Z x) \<^bold>\<leftrightarrow> Y \<Rrightarrow> Z)"

      
text\<open>  Necessary Existence, Anderson Version (Definition 11.35)  \<close>  
abbreviation necessaryExistencePred::"\<up>\<langle>\<zero>\<rangle>" ("NE\<^sup>A") 
  where "NE\<^sup>A x  \<equiv> (\<lambda>w. (\<^bold>\<forall>Y.  \<E>\<^sup>A Y x \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<exists>\<^sup>E Y) w)"
    
text\<open>  Theorem 11.36 - If g is God-like, then the property of being God-like is the essence of g. \<close>

text\<open> As shown before, this theorem's proof could be completely automatized for G\"odel's and Fitting's variants.
For Anderson's version however, we had to provide Isabelle with some help based on the corresponding natural-language proof 
given by Anderson (see @{cite "anderson90:_some_emend_of_goedel_ontol_proof"} Theorem 2*, p. 296) \<close>
(*Anderson's Proof: Suppose that g is God-like* and necessarily has a property Q. Then
by definition (of "God-like*"), that property is positive. But necessarily, if
Q is positive, then if anything is God-like*, then it has Q -again by the
definition of "God-like* ," together with the fact that if something has a
property necessarily, then it has the property. But if a property is positive,
then it is necessarily positive (Axiom 4). Hence, if Q is positive, then it is
entailed by being God-like* (by modal logic-as in the original Theorem 2).
But Q is positive and hence is entailed by being God-like*. Thus we have
proved that if an entity is God-like* and has a property essentially, then that
property is entailed by the property of being God-like*.
Suppose a property Q is entailed by the property of being God-like*. Then
Q is positive by Axioms 2 and 3* and therefore, since g is God-like*, g has
Q necessarily (by the definition of "God-like*"). Hence, if something is
God-like*, it has a property essentially if and only if that property is entailed
by being God-like-i.e., God-likeness* is an essence* of that thing.
Q.E.D.*)
theorem GodIsEssential: "\<lfloor>\<^bold>\<forall>x. G\<^sup>A x \<^bold>\<rightarrow> (\<E>\<^sup>A G\<^sup>A x)\<rfloor>"
proof -
{
  fix w
  {
    fix g
    {
      assume "G\<^sup>A g w"
      hence 1: "\<forall>Y. (\<P> Y w) \<longleftrightarrow> (\<^bold>\<box>(Y g)) w" by simp
      {
        fix Q
        from 1 have 2: "(\<P> Q w) \<longleftrightarrow> (\<^bold>\<box>(Q g)) w" by (rule allE)
        have  "(\<^bold>\<box>(Q g)) w \<longleftrightarrow> (G\<^sup>A \<Rrightarrow> Q) w" \<comment> \<open>we need to prove @{text "\<rightarrow>"} and @{text "\<leftarrow>"}\<close>
        proof
            assume "(\<^bold>\<box>(Q g)) w" \<comment> \<open>suppose g is God-like and necessarily has Q\<close>
            hence 3: "(\<P> Q w)" using 2 by simp \<comment> \<open>then Q is positive\<close>
            
            {
              fix u
              have "(\<P> Q u) \<longrightarrow> (\<forall>x. G\<^sup>A x u \<longrightarrow> (\<^bold>\<box>(Q x)) u)" 
                by auto \<comment> \<open>using the definition of God-like\<close>
              have "(\<P> Q u) \<longrightarrow> (\<forall>x. G\<^sup>A x u \<longrightarrow> ((Q x)) u)" 
                using refl by auto \<comment> \<open>and using @{text "\<box>(\<phi> x) \<longrightarrow> \<phi> x"}\<close>
            }    
            hence "\<forall>z. (\<P> Q z) \<longrightarrow> (\<forall>x. G\<^sup>A x z \<longrightarrow> Q x z)" by (rule allI)
            hence "\<lfloor>\<P> Q \<^bold>\<rightarrow> (\<^bold>\<forall>x. G\<^sup>A x \<^bold>\<rightarrow> Q x)\<rfloor>"
              by auto \<comment> \<open>if Q is positive, then whatever is God-like has Q\<close>
            hence "\<lfloor>\<^bold>\<box>(\<P> Q \<^bold>\<rightarrow> (\<^bold>\<forall>x. G\<^sup>A x \<^bold>\<rightarrow> Q x))\<rfloor>" by (rule NEC) 
            
            hence "\<lfloor>(\<^bold>\<box>(\<P> Q)) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<forall>x. G\<^sup>A x \<^bold>\<rightarrow> Q x)\<rfloor>" using K by auto
            hence "\<lfloor>(\<^bold>\<box>(\<P> Q)) \<^bold>\<rightarrow> G\<^sup>A \<Rrightarrow> Q\<rfloor>" by simp
            hence "((\<^bold>\<box>(\<P> Q)) \<^bold>\<rightarrow> G\<^sup>A \<Rrightarrow> Q) w" by (rule allE)
            hence 4: "(\<^bold>\<box>(\<P> Q)) w \<longrightarrow> (G\<^sup>A \<Rrightarrow> Q) w" by simp (*if a property is necessarily positive, then it is entailed by being God-like*)
            have "\<lfloor>\<^bold>\<forall>X. \<P> X \<^bold>\<rightarrow> \<^bold>\<box>(\<P> X)\<rfloor>" by (rule A4a) \<comment> \<open>using axiom 4\<close>
            hence "(\<^bold>\<forall>X. \<P> X \<^bold>\<rightarrow> (\<^bold>\<box>(\<P> X))) w" by (rule allE)
            hence "\<P> Q w \<longrightarrow> (\<^bold>\<box>(\<P> Q)) w" by (rule allE)
            hence "\<P> Q w \<longrightarrow> (G\<^sup>A \<Rrightarrow> Q) w" using 4 by simp (*if Q is positive, then it is entailed by being God-like*)
            thus "(G\<^sup>A \<Rrightarrow> Q) w" using 3 by (rule mp) \<comment> \<open>@{text "\<rightarrow>"} direction\<close>
         next
           assume 5: "(G\<^sup>A \<Rrightarrow> Q) w" \<comment> \<open>suppose Q is entailed by being God-like\<close>
           have "\<lfloor>\<^bold>\<forall>X Y. (\<P> X \<^bold>\<and> (X \<Rrightarrow> Y)) \<^bold>\<rightarrow> \<P> Y\<rfloor>" by (rule A2)
           hence "(\<^bold>\<forall>X Y. (\<P> X \<^bold>\<and> (X \<Rrightarrow> Y)) \<^bold>\<rightarrow> \<P> Y) w" by (rule allE)
           hence "\<forall>X Y. (\<P> X w \<and> (X \<Rrightarrow> Y) w) \<longrightarrow> \<P> Y w" by simp
           hence "\<forall>Y. (\<P> G\<^sup>A w \<and> (G\<^sup>A \<Rrightarrow> Y) w) \<longrightarrow> \<P> Y w" by (rule allE)
           hence 6: "(\<P> G\<^sup>A w \<and> (G\<^sup>A \<Rrightarrow> Q) w) \<longrightarrow> \<P> Q w" by (rule allE)
           have "\<lfloor>\<P> G\<^sup>A\<rfloor>" by (rule T2)
           hence "\<P> G\<^sup>A w" by (rule allE)
           hence "\<P> G\<^sup>A w \<and> (G\<^sup>A \<Rrightarrow> Q) w" using 5 by (rule conjI)
           from 6 this have "\<P> Q w" by (rule mp) \<comment> \<open>Q is positive by A2 and T2\<close>
           thus "(\<^bold>\<box>(Q g)) w" using 2 by simp (*@{text "\<leftarrow>"} direction *)
         qed    
     } 
     hence  "\<forall>Z. (\<^bold>\<box>(Z g)) w \<longleftrightarrow> (G\<^sup>A \<Rrightarrow> Z) w" by (rule allI)
     hence "(\<^bold>\<forall>Z. \<^bold>\<box>(Z g) \<^bold>\<leftrightarrow>  G\<^sup>A \<Rrightarrow> Z) w" by simp
     hence "\<E>\<^sup>A G\<^sup>A g w" by simp
    }
    hence "G\<^sup>A g w  \<longrightarrow> \<E>\<^sup>A G\<^sup>A g w " by (rule impI)
  }
  hence "\<forall>x. G\<^sup>A x w  \<longrightarrow> \<E>\<^sup>A G\<^sup>A x w "  by (rule allI)
}
 thus ?thesis by (rule allI) 
qed

text\<open>  Axiom 11.37 (Anderson's version of 11.25) \<close>
axiomatization where 
 A5: "\<lfloor>\<P> NE\<^sup>A\<rfloor>"
 
lemma True nitpick[satisfy] oops \<comment> \<open>model found: so far all axioms consistent\<close>
 
text\<open>  Theorem 11.38 - Possibilist existence of God implies necessary actualist existence:  \<close> 
theorem GodExistenceImpliesNecExistence: "\<lfloor>\<^bold>\<exists> G\<^sup>A \<^bold>\<rightarrow>  \<^bold>\<box>\<^bold>\<exists>\<^sup>E G\<^sup>A\<rfloor>"
proof -
{
  fix w 
  {
    assume "\<exists>x. G\<^sup>A x w"
    then obtain g where 1: "G\<^sup>A g w" ..
    hence "NE\<^sup>A g w" using A5 by blast                  \<comment> \<open>axiom 11.25\<close>
    hence "\<forall>Y. (\<E>\<^sup>A Y g w) \<longrightarrow> (\<^bold>\<box>\<^bold>\<exists>\<^sup>E Y) w" by simp
    hence 2: "(\<E>\<^sup>A G\<^sup>A g w) \<longrightarrow> (\<^bold>\<box>\<^bold>\<exists>\<^sup>E G\<^sup>A) w" by (rule allE)
    have  "(\<^bold>\<forall>x. G\<^sup>A x \<^bold>\<rightarrow> (\<E>\<^sup>A G\<^sup>A x)) w" using GodIsEssential
      by (rule allE) \<comment> \<open>GodIsEssential follows from Axioms 11.11 and 11.3B\<close>
    hence  "(G\<^sup>A g \<^bold>\<rightarrow> (\<E>\<^sup>A G\<^sup>A g)) w" by (rule allE)
    hence  "G\<^sup>A g w \<longrightarrow> \<E>\<^sup>A G\<^sup>A g w"  by blast
    from this 1 have 3: "\<E>\<^sup>A G\<^sup>A g w" by (rule mp)
    from 2 3 have "(\<^bold>\<box>\<^bold>\<exists>\<^sup>E G\<^sup>A) w" by (rule mp)
  }
  hence "(\<exists>x. G\<^sup>A x w) \<longrightarrow> (\<^bold>\<box>\<^bold>\<exists>\<^sup>E G\<^sup>A) w" by (rule impI)
  hence "((\<^bold>\<exists>x. G\<^sup>A x) \<^bold>\<rightarrow>  \<^bold>\<box>\<^bold>\<exists>\<^sup>E G\<^sup>A) w" by simp
}
 thus ?thesis by (rule allI) 
qed
    
text\<open>  Some useful rules: \<close>    
lemma modal_distr: "\<lfloor>\<^bold>\<box>(\<phi> \<^bold>\<rightarrow> \<psi>)\<rfloor> \<Longrightarrow> \<lfloor>(\<^bold>\<diamond>\<phi> \<^bold>\<rightarrow> \<^bold>\<diamond>\<psi>)\<rfloor>" by blast
lemma modal_trans: "(\<lfloor>\<phi> \<^bold>\<rightarrow> \<psi>\<rfloor> \<and> \<lfloor>\<psi> \<^bold>\<rightarrow> \<chi>\<rfloor>) \<Longrightarrow> \<lfloor>\<phi> \<^bold>\<rightarrow> \<chi>\<rfloor>" by simp

text\<open>  Anderson's version of Theorem 11.27  \<close> 
theorem possExistenceImpliesNecEx: "\<lfloor>\<^bold>\<diamond>\<^bold>\<exists> G\<^sup>A \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<exists>\<^sup>E G\<^sup>A\<rfloor>" \<comment> \<open>local consequence\<close>
proof -
  have "\<lfloor>\<^bold>\<exists> G\<^sup>A \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<exists>\<^sup>E G\<^sup>A\<rfloor>" using GodExistenceImpliesNecExistence 
    by simp \<comment> \<open>follows from Axioms 11.11, 11.25 and 11.3B\<close>
  hence "\<lfloor>\<^bold>\<box>(\<^bold>\<exists> G\<^sup>A \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<exists>\<^sup>E G\<^sup>A)\<rfloor>" using NEC by simp
  hence 1: "\<lfloor>\<^bold>\<diamond>\<^bold>\<exists> G\<^sup>A \<^bold>\<rightarrow> \<^bold>\<diamond>\<^bold>\<box>\<^bold>\<exists>\<^sup>E G\<^sup>A\<rfloor>" by (rule modal_distr)
  have 2: "\<lfloor>\<^bold>\<diamond>\<^bold>\<box>\<^bold>\<exists>\<^sup>E G\<^sup>A \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<exists>\<^sup>E G\<^sup>A\<rfloor>" using symm tran by metis
  from 1 2 have "\<lfloor>\<^bold>\<diamond>\<^bold>\<exists> G\<^sup>A \<^bold>\<rightarrow> \<^bold>\<diamond>\<^bold>\<box>\<^bold>\<exists>\<^sup>E G\<^sup>A\<rfloor> \<and> \<lfloor>\<^bold>\<diamond>\<^bold>\<box>\<^bold>\<exists>\<^sup>E G\<^sup>A \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<exists>\<^sup>E G\<^sup>A\<rfloor>" by simp
  thus ?thesis by (rule modal_trans)
qed

lemma T4: "\<lfloor>\<^bold>\<diamond>\<^bold>\<exists> G\<^sup>A\<rfloor> \<longrightarrow> \<lfloor>\<^bold>\<box>\<^bold>\<exists>\<^sup>E G\<^sup>A\<rfloor>" using possExistenceImpliesNecEx 
    by (rule localImpGlobalCons) \<comment> \<open>global consequence\<close>
  
text\<open>  Conclusion - Necessary (actualist) existence of God:  \<close>    
lemma GodNecExists: "\<lfloor>\<^bold>\<box>\<^bold>\<exists>\<^sup>E G\<^sup>A\<rfloor>" using T3 T4 by metis    
    
subsection \<open>Modal Collapse\<close>
  
text\<open>  Modal collapse is countersatisfiable  \<close>
lemma "\<lfloor>\<^bold>\<forall>\<Phi>.(\<Phi> \<^bold>\<rightarrow> (\<^bold>\<box> \<Phi>))\<rfloor>" nitpick oops
    
text\<open>  \pagebreak \<close>
    
section \<open>Conclusion\<close>
text\<open>  We presented a shallow semantical embedding in Isabelle/HOL for an intensional higher-order modal logic
(a successor of Montague/Gallin intensional logics) as introduced by M. Fitting in his textbook \emph{Types, Tableaus and 
G\"odel's God} @{cite "Fitting"}. 
We subsequently employed this logic to formalise and verify all results (theorems, examples and exercises) relevant 
to the discussion of G\"odel's ontological argument in the last part of Fitting's book. Three different versions of
the ontological argument have been considered: the first one by G\"odel himself (respectively, Scott), the second 
one by Fitting and the last one by Anderson. \<close>
  
text\<open> By employing an interactive theorem-prover like Isabelle, we were not only able to verify Fitting's results,
but also to guarantee consistency. We could prove even stronger versions
of many of the theorems and find better countermodels (i.e. with smaller cardinality) than the ones presented in the book.
Another interesting aspect was the possibility to explore the implications of alternative formalisations
for definitions and theorems which shed light on interesting philosophical issues concerning entailment,
essentialism and free will, which are currently the subject of some follow-up analysis. \<close>

text\<open> The latest developments in \emph{automated theorem proving} allow us to engage in much more experimentation
during the formalisation and assessment of arguments than ever before. The potential reduction (of several orders of magnitude)
in the time needed for proving or disproving theorems (compared to pen-and-paper proofs), results in almost real-time
feedback about the suitability of our speculations. The practical benefits of computer-supported argumentation go beyond
mere quantitative (easier, faster and more reliable proofs). The advantages are also qualitative, since it fosters a
different approach to argumentation: We can now work iteratively (by `trial-and-error') on an argument
by making gradual adjustments to its definitions, axioms and theorems. This allows us to continuously expose and revise 
the assumptions we indirectly commit ourselves everytime we opt for some particular formalisation.
\pagebreak
 \<close>
(*<*)
end
(*>*)
