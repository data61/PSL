(*File: Sound.thy
  Author: L Beringer & M Hofmann, LMU Munich
  Date: 05/12/2008
  Purpose: Interpretation of judgements, and soundness proof,
           of the program logic with  invariants, pre-
           and post-conditions, and local assertions, but no
           exploitation of sucessful bytecode verification.
*)
(*<*)
theory Sound imports Logic MultiStep Reachability begin
(*>*)

(*<*)
lemma MaxZero[rule_format]: "max n k = (0::nat) \<Longrightarrow> n=0 \<and> k=0"
by (simp add: max_def, case_tac "n\<le>k", clarsimp,clarsimp)
(*>*)

section\<open>Soundness\<close>
text\<open>This section contains the soundness proof of the program logic.
In the first subsection, we define our notion of validity, thus
formalising our intuitive explanation of the terms preconditions,
specifications, and invariants. The following two subsections contain
the details of the proof and can easily be skipped during a first pass
through the document.\<close>

subsection\<open>Validity\<close>

text\<open>A  judgement is valid at the program point \<open>C.m.l\<close>
(i.e.~at label \<open>l\<close> in method \<open>m\<close> of class \<open>C\<close>),
written $\mathit{valid}\; C\; m\; l\; A\; B\; I$ or, in symbols, $$\vDash\,
\lbrace A \rbrace\, C,m,l\, \lbrace B \rbrace\, I,$$ if $A$ is a
precondition for $B$ and for all local annotations following $l$ in an
execution of \<open>m\<close>, and all reachable states in the current frame
or yet-to-be created subframes satisfy $I$. More precisely,
whenever an execution of the method starting in an initial state $s_0$
reaches the label \<open>l\<close> with state \<open>s\<close>, the following 
properties are implied by $A(s_0,s)$.
\begin{enumerate}

  \item If the continued execution from \<open>s\<close> reaches a final
  state \<open>t\<close> (i.e.~the method terminates), then that final state
  \<open>t\<close> satisfies $B(s_0,s,t)$.

  \item Any state $s'$ visited in the current frame during the remaining
  program execution whose label carries an annotation \<open>Q\<close> will
  satisfy $Q(s_0,s')$, even if the execution of the frame does not
  terminate.

  \item Any state $s'$ visited in the current frame or a subframe of
  the current frame will satisfy $I(s_0,s,\mathit{heap}(s'))$, again even if the
  execution does not terminate.

\end{enumerate}

Formally, this interpretation is expressed as follows.
\<close>

definition valid::"Class \<Rightarrow> Method \<Rightarrow> Label \<Rightarrow> Assn \<Rightarrow> Post \<Rightarrow> Inv \<Rightarrow> bool" where
"valid C m l A B I =
   (\<forall> M. mbody_is C m M \<longrightarrow>
   (\<forall> Mspec Minv Anno . MST\<down>(C,m) = Some(Mspec,Minv,Anno) \<longrightarrow>
   (\<forall> par code l0 . M = (par,code,l0) \<longrightarrow>
   (\<forall> s0 s . MS M l0 (mkState s0) l s \<longrightarrow> A s0 s \<longrightarrow>
    ((\<forall> h v. Opsem M l s h v \<longrightarrow> B s0 s (h,v)) \<and>
     (\<forall> ll r . (MS M l s ll r  \<longrightarrow> (\<forall> Q . Anno\<down>(ll) = Some Q \<longrightarrow>  Q s0 r)) \<and>
               (Reach M l s r \<longrightarrow> I s0 s (heap r))))))))"

abbreviation valid_syntax :: "Assn \<Rightarrow> Class \<Rightarrow> Method \<Rightarrow> 
                    Label \<Rightarrow> Post \<Rightarrow> Inv \<Rightarrow> bool" 
       (" \<Turnstile> \<lbrace> _ \<rbrace> _ , _ , _ \<lbrace> _ \<rbrace> _" [200,200,200,200,200,200] 200)
where "valid_syntax A C m l B I == valid C m l A B I"

text\<open>This notion of validity extends that of Bannwart-M\"uller by
allowing the post-condition to differ from method specification and to
refer to the initial state, and by including invariants.  In
the logic of Bannwart and M\"uller, the validity of a method
specification is given by a partial correctness (Hoare-style)
interpretation, while the validity of  preconditions of
individual instructions is such that a precondition at $l$ implies the
preconditions of its immediate control flow successors.\<close>

text\<open>Validity us lifted to contexts and the method specification
table. In the case of the former, we simply require that all entries
be valid.\<close>

definition G_valid::"CTXT \<Rightarrow> bool" where
"G_valid G = (\<forall> C m l A B I. G\<down>(C,m,l) = Some (A,B,I)\<longrightarrow>
                                \<Turnstile> \<lbrace>A\<rbrace> C, m, l \<lbrace>B\<rbrace> I)"

text\<open>Regarding the specification table, we require that the initial
label of each method satisfies an assertion that ties the method
precondition to the current state.\<close>

definition MST_valid ::bool where
"MST_valid = (\<forall> C m par code l0 T MI Anno. 
  mbody_is C m (par,code,l0) \<longrightarrow> MST\<down>(C, m) = Some (T,MI,Anno) \<longrightarrow> 
  \<Turnstile> \<lbrace>(\<lambda> s0 s. s = mkState s0)\<rbrace> C, m, l0 \<lbrace>(mkPost T)\<rbrace> (mkInv MI))"

definition Prog_valid::bool where
"Prog_valid = (\<exists> G . G_valid G \<and> MST_valid)"

text\<open>The remainder of this section contains a proof of soundness,
i.e.~of the property $$\<open>VP\<close> \Longrightarrow \<open>Prog_valid\<close>,$$ and is structured into two parts. The first step
(Section \ref{SoundnessUnderValidContexts}) establishes a soundness
result where the \<open>VP\<close> property is replaced by validity
assumptions regarding the method specification table and the
context. In the second step (Section \ref{SectionContextElimination}),
we show that these validity assumptions are satisfied by verified
programs, which implies the overall soundness theorem.\<close>

subsection\<open>Soundness under valid contexts
\label{SoundnessUnderValidContexts}\<close>

text\<open>The soundness proof proceeds by induction on the axiomatic
semantics, based on an auxiliary lemma for method invocations that is
proven by induction on the derivation height of the operational
semantics. For the latter induction, relativised notions of validity
are employed that restrict the derivation height of the program
continuations affected by an assertion. The appropriate definitions of
relativised validity for judgements, for the precondition table, and
for the method specification table are as follows.\<close>

definition validn::
  "nat \<Rightarrow> Class \<Rightarrow> Method \<Rightarrow> Label \<Rightarrow> Assn \<Rightarrow> Post \<Rightarrow> Inv \<Rightarrow> bool" where
"validn K C m l A B I =
   (\<forall> M. mbody_is C m M \<longrightarrow>
   (\<forall> Mspec Minv Anno . MST\<down>(C,m) = Some(Mspec,Minv,Anno) \<longrightarrow>
   (\<forall> par code l0 . M = (par,code,l0) \<longrightarrow>
   (\<forall> s0 s . MS M l0 (mkState s0) l s \<longrightarrow> A s0 s \<longrightarrow>
   (\<forall> k . k \<le> K \<longrightarrow> 
    ((\<forall> h v. (M,l,s,k,h,v):Exec \<longrightarrow> B s0 s (h,v)) \<and>
     (\<forall> ll r . ((M,l,s,k,ll,r):MStep  \<longrightarrow>
                 (\<forall> Q . Anno\<down>(ll) = Some Q \<longrightarrow>  Q s0 r)) \<and>
               ((M,l,s,k,r):Reachable \<longrightarrow> I s0 s (heap r)))))))))"

abbreviation validn_syntax :: "nat \<Rightarrow> Assn \<Rightarrow> Class \<Rightarrow> Method \<Rightarrow>
                     Label \<Rightarrow> Post \<Rightarrow> Inv \<Rightarrow> bool" 
("\<Turnstile>\<^sub>_ \<lbrace> _ \<rbrace> _ , _ , _ \<lbrace> _ \<rbrace> _ " [200,200,200,200,200,200,200] 200)
where "validn_syntax K A C m l B I == validn K C m l A B I"

definition G_validn::"nat \<Rightarrow> CTXT \<Rightarrow> bool" where
"G_validn K G = (\<forall> C m l A B I. G\<down>(C,m,l) = Some (A,B,I) \<longrightarrow>
                                \<Turnstile>\<^sub>K \<lbrace>A\<rbrace> C, m, l \<lbrace>B\<rbrace> I)"

definition MST_validn::"nat \<Rightarrow> bool" where
"MST_validn K = (\<forall> C m par code l0 T MI Anno. 
   mbody_is C m (par,code,l0) \<longrightarrow> MST\<down>(C, m) = Some (T,MI,Anno) \<longrightarrow> 
   \<Turnstile>\<^sub>K \<lbrace>(\<lambda> s0 s. s = mkState s0)\<rbrace> C, m, l0 \<lbrace>(mkPost T)\<rbrace> (mkInv MI))"

definition Prog_validn::"nat \<Rightarrow> bool" where
"Prog_validn K = (\<exists> G . G_validn K G \<and> MST_validn K)"

text\<open>The relativised notions are related to each other, and to the
native notions of validity as follows.\<close>

lemma valid_validn: "\<Turnstile> \<lbrace>A\<rbrace> C, m, l \<lbrace>B\<rbrace> I \<Longrightarrow> \<Turnstile>\<^sub>K \<lbrace>A\<rbrace> C, m, l \<lbrace>B\<rbrace> I"
(*<*)
apply (simp add: valid_def validn_def Opsem_def MS_def Reach_def)
apply clarsimp
apply (erule_tac x=a in allE)
apply (erule_tac x=aa in allE)
apply (erule_tac x=b in allE, clarsimp)
apply (erule_tac x=ab in allE)
apply (erule_tac x=ba in allE)
apply (erule_tac x=ac in allE)
apply (erule_tac x=ad in allE)
apply (erule_tac x=bb in allE, erule impE) apply fast
apply fastforce
done
(*>*)

lemma validn_valid: "\<lbrakk>\<forall> K . \<Turnstile>\<^sub>K \<lbrace>A\<rbrace> C, m, l \<lbrace>B\<rbrace> I\<rbrakk> \<Longrightarrow> \<Turnstile> \<lbrace>A\<rbrace> C, m, l \<lbrace>B\<rbrace> I"
(*<*)
apply (unfold valid_def validn_def)(*apply ( Opsem_def MS_def Reach_def)*)
apply (rule, rule, rule)
apply (rule, rule, rule)
apply (rule, rule, rule)
apply (rule, rule, rule)
apply (rule, rule)
apply (rule,rule,rule, rule)    
    apply (unfold Opsem_def, erule exE)
    apply (erule_tac x=n in allE)
    apply (erule_tac x=M in allE, erule impE, assumption) 
    apply (erule_tac x=Mspec in allE, erule_tac x=Minv in allE, erule_tac x=Anno in allE, erule impE, assumption)
    apply (erule_tac x=par in allE, erule_tac x=code in allE)
    apply (erule_tac x=l0 in allE, erule impE, assumption) 
    apply (erule_tac x=s0 in allE, erule_tac x=s in allE)
    apply (erule impE, assumption) 
    apply (erule impE, assumption) 
    apply (erule_tac x=n in allE, erule impE, simp)
    apply fast
apply (rule, rule, rule)
apply (rule, rule, rule)
    apply (unfold MS_def, erule exE, erule exE)
    apply (erule_tac x=ka in allE)
    apply (erule_tac x=M in allE, erule impE, assumption) 
    apply (erule_tac x=Mspec in allE, erule_tac x=Minv in allE, erule_tac x=Anno in allE, erule impE, assumption)
    apply (erule_tac x=par in allE, erule_tac x=code in allE)
    apply (erule_tac x=l0 in allE, erule impE, assumption) 
    apply (erule_tac x=s0 in allE, erule_tac x=s in allE)
    apply (erule impE, fast) 
    apply (erule impE, assumption) 
    apply (erule_tac x=ka in allE, erule impE, simp)
    apply fast
apply rule
    apply (unfold Reach_def, erule exE, erule exE)
    apply (erule_tac x=ka in allE)
    apply (erule_tac x=M in allE, erule impE, assumption) 
    apply (erule_tac x=Mspec in allE, erule_tac x=Minv in allE, erule_tac x=Anno in allE, erule impE, assumption)
    apply (erule_tac x=par in allE, erule_tac x=code in allE)
    apply (erule_tac x=l0 in allE, erule impE, assumption) 
    apply (erule_tac x=s0 in allE, erule_tac x=s in allE)
    apply (erule impE, fast) 
    apply (erule impE, assumption) 
    apply (erule_tac x=ka in allE, erule impE, simp)
    apply fast
done
(*>*)

lemma validn_lower: 
 "\<lbrakk>\<Turnstile>\<^sub>K \<lbrace>A\<rbrace> C, m, l \<lbrace>B\<rbrace> I; L \<le> K\<rbrakk> \<Longrightarrow> \<Turnstile>\<^sub>L \<lbrace>A\<rbrace> C, m, l \<lbrace>B\<rbrace> I"
(*<*)
apply (unfold validn_def)
apply (rule, rule, rule)
apply (rule, rule, rule)
apply (rule, rule, rule)
apply (rule, rule, rule)
apply (rule, rule, rule)
apply rule
    apply (erule_tac x=M in allE, erule impE, assumption)
    apply (erule_tac x=Mspec in allE, erule_tac x=Minv in allE, erule_tac x=Anno in allE, erule impE, assumption)
    apply (erule_tac x=par in allE)
    apply (erule_tac x=code in allE)
    apply (erule_tac x=l0 in allE, erule impE, assumption)
    apply (erule_tac x=s0 in allE)
    apply (erule_tac x=s in allE, erule impE, assumption, erule impE, assumption)
    apply (erule_tac x=k in allE, erule impE, simp)
apply assumption
done
(*>*)

lemma G_valid_validn: "G_valid G \<Longrightarrow> G_validn K G"
(*<*)
apply (simp add: G_valid_def G_validn_def, clarsimp)
apply (rule valid_validn) apply fast
done
(*>*)

lemma G_validn_valid:"\<lbrakk>\<forall> K . G_validn K G\<rbrakk> \<Longrightarrow> G_valid G"
(*<*)
apply (simp add: G_valid_def G_validn_def, clarsimp)
apply (rule validn_valid) apply clarsimp
done
(*>*)

lemma G_validn_lower: "\<lbrakk>G_validn K G; L \<le> K\<rbrakk> \<Longrightarrow> G_validn L G"
(*<*)
apply (simp add: G_validn_def, clarsimp)
apply (rule validn_lower) apply fast apply assumption
done
(*>*)

lemma MST_validn_valid:"\<lbrakk>\<forall> K. MST_validn K\<rbrakk> \<Longrightarrow> MST_valid"
(*<*)
apply (simp add: MST_validn_def MST_valid_def, clarsimp)
apply (rule validn_valid, clarsimp)
done
(*>*)

lemma MST_valid_validn:"MST_valid \<Longrightarrow> MST_validn K"
(*<*)
apply (unfold MST_validn_def MST_valid_def)
apply (rule, rule, rule)
apply (rule, rule, rule)
apply (rule, rule, rule)
apply rule
apply (rule valid_validn)
apply fast
done
(*>*)

lemma MST_validn_lower: "\<lbrakk>MST_validn K; L \<le> K\<rbrakk> \<Longrightarrow> MST_validn L"
(*<*)
apply (simp add: MST_validn_def, clarsimp)
apply (erule_tac x=C in allE)
apply (erule_tac x=m in allE)
apply (erule_tac x=par in allE)
apply (erule_tac x=code in allE)
apply (erule_tac x=l0 in allE, erule impE, assumption)
apply (erule_tac x=T in allE)
apply (erule_tac x=MI in allE, clarsimp)
apply (erule validn_lower) apply assumption
done
(*>*)

text\<open>We define an abbreviation for the side conditions of the rule
for static method invocations\ldots\<close>

definition INVS_SC::
  "Class \<Rightarrow> Method \<Rightarrow> Label \<Rightarrow> Class \<Rightarrow> Method \<Rightarrow>  MethSpec \<Rightarrow> MethInv \<Rightarrow>
   ANNO \<Rightarrow> ANNO \<Rightarrow> Mbody \<Rightarrow> Assn \<Rightarrow> Inv \<Rightarrow> bool" where
"INVS_SC C m l D m' T MI Anno Anno2 M' A I = (\<exists> M par code l0 T1 MI1.
    mbody_is C m M \<and> get_ins M l = Some (invokeS D m') \<and> 
    MST\<down>(C,m) = Some (T1,MI1,Anno) \<and> 
    MST\<down>(D,m') = Some (T,MI,Anno2) \<and>  
    mbody_is D m' M' \<and> M'=(par,code,l0) \<and>  
    (\<forall> Q . Anno\<down>(l) = Some Q \<longrightarrow> (\<forall> s0 s . A s0 s \<longrightarrow> Q s0 s)) \<and> 
    (\<forall> s0 s . A s0 s \<longrightarrow> I s0 s (heap s)) \<and> 
    (\<forall> s0 ops1 ops2 S R h t . (ops1,par,R,ops2) : Frame \<longrightarrow>
          A s0 (ops1,S,h) \<longrightarrow> MI (R,h) t \<longrightarrow> I s0 (ops1,S,h) t))"

text\<open>\ldots and another abbreviation for the soundness property of
the same rule.\<close>

definition INVS_soundK::
  "nat \<Rightarrow> CTXT \<Rightarrow> Class \<Rightarrow> Method \<Rightarrow> Label \<Rightarrow> Class \<Rightarrow> Method \<Rightarrow> 
   MethSpec \<Rightarrow> MethInv \<Rightarrow> ANNO \<Rightarrow> ANNO \<Rightarrow> Mbody \<Rightarrow> Assn \<Rightarrow> 
   Post \<Rightarrow> Inv \<Rightarrow> bool" where
"INVS_soundK K G C m l D m' T MI Anno Anno2 M' A B I =
  (INVS_SC C m l D m' T MI Anno Anno2 M' A I \<longrightarrow> 
    G_validn K G \<longrightarrow> MST_validn K \<longrightarrow>
    \<Turnstile>\<^sub>K \<lbrace>(SINV_pre (fst M') T A)\<rbrace> C,m,(l+1)
        \<lbrace>(SINV_post (fst M') T B)\<rbrace> (SINV_inv (fst M') T I)
   \<longrightarrow> \<Turnstile>\<^sub>(K+1) \<lbrace> A \<rbrace> C,m,l \<lbrace> B \<rbrace> I)"

text\<open>The proof that this property holds for all $K$ proceeds by
induction on $K$.\<close>

lemma INVS_soundK_all:
  "INVS_soundK K G C m l D m' T MI Anno Anno2 M' A B I"
(*<*)
apply (induct K)
(*K=0*)
apply (simp add: INVS_soundK_def , clarsimp)
  apply (unfold validn_def)
  apply (rule, rule) apply (erule_tac x=M in allE, erule impE, assumption)
  apply (rule, rule, rule, rule)
  apply (erule_tac x=Mspec in allE, erule_tac x=Minv in allE, erule_tac x=Annoa in allE, erule impE, assumption)
  apply (rule, rule, rule, rule)
  apply (erule_tac x=par in allE, erule_tac x=code in allE, erule_tac x=l0 in allE, erule impE, assumption)
  apply (rule, rule, rule)
  apply (rule, rule, rule)
  apply rule  
    apply (rule, rule, rule) apply (case_tac k, clarsimp)  apply (drule no_zero_height_Exec_derivs, simp) apply clarsimp
       apply (erule eval_cases) apply (simp add: INVS_SC_def mbody_is_def,clarsimp) apply clarsimp apply (drule MaxZero, clarsimp)
       apply (drule no_zero_height_Exec_derivs, simp)
   apply (rule, rule, rule, rule)
     apply clarsimp 
           apply (case_tac k, clarsimp) apply (drule ZeroHeightMultiElim, clarsimp) 
             apply (simp add: INVS_SC_def mbody_is_def,clarsimp)
           apply clarsimp
               apply (drule MultiSplit, simp, clarsimp) apply (drule no_zero_height_Step_derivs, simp)
   apply rule apply (case_tac k, clarsimp) apply (drule ZeroHeightReachableElim, clarsimp)
          apply (simp add: INVS_SC_def mbody_is_def,clarsimp) 
         apply clarsimp apply (drule ReachableSplit, simp, clarsimp)
        apply (erule disjE)
         apply clarsimp  apply (drule no_zero_height_Step_derivs, simp)
         apply clarsimp  apply (drule ZeroHeightReachableElim, clarsimp)
         apply (rotate_tac 5, erule thin_rl)
          apply (simp add: INVS_SC_def mbody_is_def,clarsimp)  
             apply (simp add: MST_validn_def)
             apply (erule_tac x=D in allE, rotate_tac -1)
             apply (erule_tac x=m' in allE, rotate_tac -1)
             apply (erule_tac x=para in allE, rotate_tac -1)
             apply (erule_tac x=codea in allE, rotate_tac -1)
             apply (erule_tac x=l0a in allE, rotate_tac -1,erule impE) apply (simp add: mbody_is_def)
             apply (rotate_tac -1, erule_tac x=T in allE)
             apply (rotate_tac -1, erule_tac x=MI in allE, clarsimp)
             apply (simp add: validn_def)
             apply (simp add: mbody_is_def)
             apply (simp add: heap_def)
(*k>0*)
apply (simp add: INVS_soundK_def , clarsimp)
apply (rotate_tac -1, erule thin_rl)
apply (unfold validn_def)
apply (rule, rule) apply (erule_tac x=M in allE, erule impE, assumption)
apply (rule, rule) apply (rule, rule) apply (rule, rule) apply (rule, rule) apply (rule, rule) 
  apply (erule_tac x=Mspec in allE, erule_tac x=Minv in allE, erule_tac x=Annoa in allE, erule impE, assumption)
  apply (erule_tac x=par in allE, erule_tac x=code in allE)
  apply (erule_tac x=l0 in allE, erule impE, assumption)
apply (rule, rule) 
apply (rule, rule)
apply (erule_tac x=s0 in allE)
apply rule
(*Exec*)
  apply (rule, rule, rule)
   apply (erule eval_cases) apply clarsimp apply (simp add: INVS_SC_def mbody_is_def) apply clarsimp
   apply (erule_tac x=t in allE, erule impE)
     apply (frule InvokeElim)  apply (simp add: INVS_SC_def mbody_is_def) apply clarsimp apply fastforce
     apply (simp add: MS_def, erule exE, rule) apply clarsimp apply (erule MultiApp) apply assumption
   apply (erule impE, drule InvokeElim, simp add: INVS_SC_def mbody_is_def) apply clarsimp apply fastforce
     apply clarsimp apply (simp add: INVS_SC_def mbody_is_def SINV_pre_def) apply clarsimp apply (rule, rule)
        apply (rule, rule, rule, assumption) apply (rule, rule) prefer 2 apply (rule, assumption) apply simp
        apply (simp add: MST_validn_def) apply (erule_tac x=D in allE, erule_tac x=m' in allE)
          apply (erule_tac x=parb in allE, erule_tac x=codeb in allE) 
          apply (erule_tac x=l0b in allE, simp add: mbody_is_def) 
          apply (simp add: validn_def) 
          apply (erule_tac x=parb in allE, erule_tac x=codeb in allE) 
          apply (erule_tac x=l0b in allE, simp add: mbody_is_def) 
          apply (rotate_tac -1, erule_tac x=R in allE, erule_tac x=bb in allE)
          apply (rotate_tac -1, erule_tac x="[]" in allE, rotate_tac -1, erule_tac x=R in allE, erule_tac x=bb in allE)
          apply (simp add: mkState_def)
          apply (erule impE) apply (simp add: MS_def, rule) apply (rule MS_zero) apply simp apply simp apply simp
          apply (erule_tac x=ka in allE, erule impE, simp) 
          apply (simp add: mkPost_def, erule conjE)
          apply (erule_tac x=hh in allE, erule_tac x=va in allE, simp add: mkState_def)
        apply (erule_tac x=ma in allE, erule impE) apply (simp add: max_def) apply (case_tac "n \<le> ma") apply clarsimp apply clarsimp
         apply (erule conjE) apply (erule_tac x=h in allE, erule_tac x=v in allE, erule impE)
         apply (drule InvokeElim) apply (simp add: INVS_SC_def mbody_is_def) apply clarsimp apply fastforce
           apply clarsimp 
         apply (simp add: SINV_post_def) apply (simp add: INVS_SC_def mbody_is_def, clarsimp)
           apply (drule InvokeElim, clarsimp) apply fastforce apply clarsimp
           apply (simp add: mbody_is_def, clarsimp)
           apply (erule_tac x=ac in allE, erule_tac x=ops in allE, rotate_tac -1)
           apply (erule_tac x=ad in allE, erule_tac x=R in allE, rotate_tac -1, erule impE, assumption) 
           apply (erule_tac x=bb in allE, simp, erule mp)
           apply (simp add: MST_validn_def)
           apply (erule_tac x=D in allE, erule_tac x=m' in allE, rotate_tac -1)
           apply (erule_tac x=par in allE, erule_tac x=code in allE,  erule_tac x=l0 in allE, simp add: mbody_is_def)
           apply (simp add: validn_def)
           apply (rotate_tac -1) apply (erule thin_rl) apply (rotate_tac -1) 
           apply (simp add: mbody_is_def) 
           apply (erule_tac x=R in allE, rotate_tac -1, erule_tac x=bb in allE, rotate_tac -1)
           apply (erule_tac x="[]" in allE, rotate_tac -1, erule_tac x=R in allE, rotate_tac -1)
           apply (erule_tac x=bb in allE, erule impE)
             apply (simp add: MS_def, rule, rule MS_zero) apply (simp, simp add: mkState_def, simp)
           apply (simp add: mkState_def)
           apply (erule_tac x=k in allE, clarsimp)
           apply (erule_tac x=bc in allE, erule_tac x=va in allE, simp add: mkPost_def mkState_def)
(*MStep*)
apply (rule, rule)           
apply (rule, rule)
apply (rule, rule)
   apply (case_tac k, clarsimp) apply (drule ZeroHeightMultiElim, clarsimp) apply (simp add: INVS_SC_def) apply clarsimp
   apply clarsimp
   apply (frule MultiSplit) apply clarsimp apply clarsimp 
     apply (frule InvokeElim)  apply (simp add: INVS_SC_def mbody_is_def) apply clarsimp apply fastforce
     apply clarsimp
     apply (erule_tac x="v # ops" in allE, erule_tac x=ad in allE, erule_tac x=b in allE, erule impE)
     apply (simp add: MS_def, erule exE, rule)  apply (erule MultiApp) apply assumption
       apply (erule impE, simp add: SINV_pre_def INVS_SC_def mbody_is_def) apply clarsimp 
        apply (rule, rule, rule, rule, rule, assumption) apply (rule, rule) 
          prefer 2 apply (rule, assumption) apply simp
        apply (simp add: MST_validn_def) apply (erule_tac x=D in allE, erule_tac x=m' in allE)
          apply (erule_tac x=parb in allE, erule_tac x=codeb in allE) 
          apply (erule_tac x=l0b in allE, simp add: mbody_is_def) 
          apply (simp add: validn_def) 
          apply (erule_tac x=parb in allE, erule_tac x=codeb in allE) 
          apply (erule_tac x=l0b in allE, simp add: mbody_is_def) 
          apply (rotate_tac -1, erule_tac x=R in allE, erule_tac x=bb in allE)
          apply (rotate_tac -1, erule_tac x="[]" in allE, rotate_tac -1, erule_tac x=R in allE, erule_tac x=bb in allE)
          apply (simp add: mkState_def)
          apply (erule impE) apply (simp add: MS_def, rule) apply (rule MS_zero) apply simp apply simp apply simp
          apply (erule_tac x=k in allE, erule impE, simp) 
          apply (simp add: mkPost_def, erule conjE)
          apply (erule_tac x=hh in allE, erule_tac x=va in allE, simp add: mkState_def)
        apply (erule_tac x=ma in allE, erule impE) apply simp 
         apply (erule conjE) apply (erule_tac x=ll in allE, erule_tac x=ae in allE)
           apply (erule_tac x=af in allE, rotate_tac -1, erule_tac x=bc in allE, clarsimp)
(*Reach*)
apply rule
  apply (case_tac k, clarsimp) apply (drule ZeroHeightReachableElim, clarsimp)
       apply (simp add: INVS_SC_def mbody_is_def, clarsimp)
  apply clarsimp
  apply (drule ReachableSplit) apply simp apply clarsimp
  apply (erule disjE)
    apply clarsimp 
         apply (frule InvokeElim) apply (simp add: INVS_SC_def mbody_is_def) apply clarsimp apply fastforce
           apply clarsimp 
           apply (erule_tac x="v#ops" in allE, erule_tac x=ad in allE, erule_tac x=b in allE, erule impE)
           apply (simp add: MS_def, clarsimp, rule) apply (erule MultiApp) apply assumption
         apply (erule impE) apply (simp add: SINV_pre_def) apply (simp add: INVS_SC_def mbody_is_def, clarsimp)
            apply (rule, rule, rule, rule, rule) apply assumption 
            apply (rule, rule) prefer 2 apply (rule, assumption, simp)
           apply (simp add: MST_validn_def)
           apply (erule_tac x=D in allE, erule_tac x=m' in allE, rotate_tac -1)
           apply (erule_tac x=parb in allE, erule_tac x=codeb in allE,  erule_tac x=l0b in allE, simp add: mbody_is_def)
           apply (simp add: validn_def)
           apply (simp add: mbody_is_def) apply (rotate_tac -1)
           apply (erule_tac x=R in allE, rotate_tac -1, erule_tac x=bb in allE, rotate_tac -1)
           apply (erule_tac x="[]" in allE, rotate_tac -1, erule_tac x=R in allE, rotate_tac -1)
           apply (erule_tac x=bb in allE, erule impE)
             apply (simp add: MS_def, rule, rule MS_zero) apply (simp, simp add: mkState_def, simp)
           apply (simp add: mkState_def)
           apply (erule_tac x=k in allE, clarsimp)
           apply (erule_tac x=b in allE, erule_tac x=v in allE, simp add: mkPost_def mkState_def)
        apply (erule_tac x=ma in allE, clarsimp)
        apply (rotate_tac -1)
        apply (simp add: SINV_inv_def)
        apply (erule_tac x="l+1" in allE, erule_tac x=ae in allE)
        apply (erule_tac x=af in allE, rotate_tac -1, erule_tac x=bc in allE, clarsimp)
        apply (rotate_tac -2, erule thin_rl)
        apply (simp add: SINV_inv_def INVS_SC_def mbody_is_def) apply clarsimp 
        apply (rotate_tac -1, erule_tac x=ac in allE)
        apply (rotate_tac -1, erule_tac x=ops in allE)
        apply (rotate_tac -1, erule_tac x=ad in allE)
        apply (rotate_tac -1, erule_tac x=R in allE, clarsimp)
        apply (rotate_tac -1, erule_tac x=bb in allE, erule mp)
        apply (erule thin_rl)
           apply (simp add: MST_validn_def)
           apply (erule_tac x=D in allE, erule_tac x=m' in allE, rotate_tac -1)
           apply (erule_tac x=parb in allE, erule_tac x=codeb in allE,  erule_tac x=l0b in allE, simp add: mbody_is_def)
           apply (simp add: validn_def)
           apply (simp add: mbody_is_def) apply (rotate_tac -1)
           apply (erule_tac x=R in allE, rotate_tac -1, erule_tac x=bb in allE, rotate_tac -1)
           apply (erule_tac x="[]" in allE, rotate_tac -1, erule_tac x=R in allE, rotate_tac -1)
           apply (erule_tac x=bb in allE, erule impE)
             apply (simp add: MS_def, rule, rule MS_zero) apply (simp, simp add: mkState_def, simp)
           apply (simp add: mkState_def)
           apply (erule_tac x=k in allE, clarsimp)
           apply (erule_tac x=b in allE, erule_tac x=v in allE, simp add: mkPost_def mkState_def)
  apply clarsimp
  apply (simp add: INVS_SC_def mbody_is_def, clarsimp) 
  apply (rotate_tac -1, erule_tac x=ab in allE)
  apply (rotate_tac -1, erule_tac x=ba in allE)
  apply (rotate_tac -1, erule_tac x=ac in allE)
  apply (rotate_tac -1, erule_tac x=ops1 in allE)
  apply (rotate_tac -1, erule_tac x=ad in allE)
  apply (rotate_tac -1, erule_tac x=R in allE, clarsimp)
  apply (rotate_tac -1, erule_tac x=bb in allE, clarsimp)
  apply (rotate_tac -1, erule_tac x="heap (ae,af,bc)" in allE, erule mp)
  apply (rotate_tac 6) apply (erule thin_rl)
  apply (simp add: MST_validn_def)
  apply (erule_tac x=D in allE, erule_tac x=m' in allE)
  apply (simp add: mbody_is_def)
  apply (simp add: validn_def)
  apply (simp add: mbody_is_def mkInv_def)
  apply (rotate_tac -1)
  apply (erule_tac x=R in allE, erule_tac x=bb in allE)
  apply (rotate_tac -1) apply (erule_tac x="[]" in allE)
  apply (rotate_tac -1)
  apply (erule_tac x=R in allE, erule_tac x=bb in allE, simp add: mkState_def, erule impE)
  apply (simp add: MS_def, rule, rule MS_zero) apply (simp, simp, simp)
  apply (erule_tac x=nat in allE, simp)
done
(*>*)


text\<open>The heart of the soundness proof - the induction on the
axiomatic semantics.\<close>

lemma SOUND_Aux[rule_format]: 
"(b,G,C,m,l,A,B,I):SP_Judgement \<Longrightarrow> G_validn K G \<longrightarrow> MST_validn K \<longrightarrow> 
  ((b \<longrightarrow> \<Turnstile>\<^sub>K \<lbrace>A\<rbrace> C, m, l \<lbrace>B\<rbrace> I) \<and> 
   ((\<not> b) \<longrightarrow> \<Turnstile>\<^sub>(Suc K) \<lbrace>A\<rbrace> C, m, l \<lbrace>B\<rbrace> I))"
(*<*)
apply (erule SP_Judgement.induct)
(*INSTR*)
apply clarsimp
apply (rotate_tac -4) apply (erule thin_rl)
apply (simp add: mbody_is_def validn_def Opsem_def MS_def Reach_def, clarsimp)
apply rule
  apply clarsimp apply (erule eval_cases) apply simp
    apply clarsimp apply (frule InstrElimNext, simp, assumption, clarsimp)
    apply (erule_tac x=ad in allE)
    apply (erule_tac x=bb in allE)
    apply (erule_tac x=a in allE, rotate_tac -1)
    apply (erule_tac x=aa in allE)
    apply (erule_tac x=b in allE, erule impE)
      apply rule
        apply (erule MultiApp)
        apply assumption
      apply (erule impE, simp add: SP_pre_def) apply (rule, rule, rule, rule, assumption)
         apply (rule, rule,assumption) 
      apply (erule_tac x=ma in allE, clarsimp)
      apply (erule_tac x=h in allE, erule_tac x=v in allE, clarsimp)
      apply (simp add: SP_post_def) 
       apply (rotate_tac -1)
       apply (erule_tac x=ae in allE, rotate_tac -1)
       apply (erule_tac x=af in allE, rotate_tac -1)
       apply (erule_tac x=bc in allE, erule mp)
         apply (rule, rule, assumption)
apply clarsimp
apply rule
  apply clarsimp 
    apply (case_tac ka) apply clarsimp apply (drule ZeroHeightMultiElim) apply clarsimp
    apply clarsimp
    apply (rotate_tac -2, drule MultiSplit) apply simp apply clarsimp
      apply (frule InstrElimNext, simp, assumption, clarsimp)
      apply (erule_tac x=ad in allE)
      apply (erule_tac x=bb in allE)
      apply (erule_tac x=ag in allE, rotate_tac -1)
      apply (erule_tac x=ah in allE)
      apply (erule_tac x=bd in allE, erule impE)
        apply rule
          apply (erule MultiApp)
          apply assumption
       apply (erule impE, simp add: SP_pre_def) apply (rule, rule, rule, rule, assumption)
         apply (rule, rule, assumption) 
      apply (erule_tac x=ma in allE, clarsimp)
      apply (erule_tac x=ll in allE, rotate_tac -1)
      apply (erule_tac x=a in allE, rotate_tac -1)
      apply (erule_tac x=aa in allE, rotate_tac -1)
      apply (erule_tac x=b in allE, clarsimp)
  apply clarsimp 
    apply (case_tac ka) apply clarsimp apply (drule ZeroHeightReachableElim) apply clarsimp
    apply clarsimp
    apply (rotate_tac -2, drule ReachableSplit) apply simp apply clarsimp
    apply (rotate_tac -1, erule disjE)
      apply clarsimp
      apply (frule InstrElimNext, simp, assumption, clarsimp)
      apply (erule_tac x=ad in allE)
      apply (erule_tac x=bb in allE)
      apply (erule_tac x=ag in allE, rotate_tac -1)
      apply (erule_tac x=ah in allE)
      apply (erule_tac x=bd in allE, erule impE)
        apply rule
          apply (erule MultiApp)
          apply assumption
       apply (erule impE, simp add: SP_pre_def) apply (rule, rule, rule, rule, assumption)
         apply (rule, rule, assumption) 
       apply (erule_tac x=ma in allE, clarsimp)
         apply (rotate_tac -1, erule_tac x=ll in allE)
         apply (rotate_tac -1, erule_tac x=a in allE)
         apply (rotate_tac -1, erule_tac x=aa in allE)
         apply (rotate_tac -1, erule_tac x=b in allE, clarsimp)
         apply (simp add: SP_inv_def) 
(*         apply (rotate_tac -1, erule_tac x="l+1" in allE)*)
         apply (rotate_tac -1, erule_tac x=ae in allE)
         apply (rotate_tac -1, erule_tac x=af in allE)
         apply (rotate_tac -1, erule_tac x=bc in allE, erule mp) apply (rule, rule, assumption)
    apply clarsimp
(*GOTO*)
apply clarsimp
apply (rotate_tac 5) apply (erule thin_rl)
apply (simp add: mbody_is_def validn_def Opsem_def MS_def Reach_def, clarsimp)
apply rule
  apply clarsimp apply (erule eval_cases) apply simp
    apply clarsimp apply (drule GotoElim1) apply (simp, clarsimp)
    apply (erule_tac x=ad in allE)
    apply (erule_tac x=bb in allE)
    apply (erule_tac x=ae in allE, rotate_tac- 1)
    apply (erule_tac x=af in allE)
    apply (erule_tac x=bc in allE, erule impE)
      apply rule
        apply (erule MultiApp)
          apply (erule Goto) 
    apply (erule impE, simp add: SP_pre_def) apply (rule, rule, rule, rule, assumption)
         apply (rule, rule, erule Goto) 
         apply (erule_tac x=ma in allE, clarsimp) 
         apply (erule_tac x=h in allE, erule_tac x=v in allE, clarsimp)
         apply(simp add: SP_post_def, rotate_tac -1) 
         apply (erule_tac x=ae in allE, rotate_tac -1)
         apply (erule_tac x=af in allE, rotate_tac -1)
         apply (erule_tac x=bc in allE, erule mp)
           apply (rule, rule, erule Goto) 
apply clarsimp
apply rule
  apply clarsimp 
    apply (case_tac ka) apply clarsimp apply (drule ZeroHeightMultiElim) apply clarsimp 
    apply clarsimp
    apply (rotate_tac -2, drule MultiSplit) apply simp apply clarsimp
      apply (drule GotoElim1) apply simp apply clarsimp 
      apply (erule_tac x=ad in allE)
      apply (erule_tac x=bb in allE)
      apply (erule_tac x=ae in allE,rotate_tac -1)
      apply (erule_tac x=af in allE)
      apply (erule_tac x=bc in allE, erule impE)
        apply rule
          apply (erule MultiApp)
            apply (erule Goto) 
       apply (erule impE, simp add: SP_pre_def) apply (rule, rule, rule, rule, assumption)
         apply (rule, rule, erule Goto) 
      apply (erule_tac x=ma in allE, clarsimp)
      apply (erule_tac x=ll in allE, rotate_tac -1)
      apply (erule_tac x=a in allE, rotate_tac -1)
      apply (erule_tac x=aa in allE)
      apply (erule_tac x=b in allE, clarsimp)
  apply clarsimp 
    apply (case_tac ka) apply clarsimp apply (drule ZeroHeightReachableElim) apply clarsimp 
    apply clarsimp
    apply (rotate_tac -2, drule ReachableSplit) apply simp apply clarsimp
      apply (drule GotoElim1) apply simp apply clarsimp 
      apply (erule_tac x=ad in allE)
      apply (erule_tac x=bb in allE)
      apply (erule_tac x=ae in allE,rotate_tac -1)
      apply (erule_tac x=af in allE)
      apply (erule_tac x=bc in allE, erule impE)
        apply rule
          apply (erule MultiApp)
            apply (erule Goto) 
       apply (erule impE, simp add: SP_pre_def) apply (rule, rule, rule, rule, assumption)
         apply (rule, rule, erule Goto) 
      apply (erule_tac x=ma in allE, clarsimp)
         apply (rotate_tac -1, erule_tac x=ll in allE)
         apply (rotate_tac -1, erule_tac x=a in allE)
         apply (rotate_tac -1, erule_tac x=aa in allE)
         apply (rotate_tac -1, erule_tac x=b in allE, clarsimp)
         apply (simp add: SP_inv_def) 
(*         apply (rotate_tac -1, erule_tac x=pc in allE)*)
         apply (rotate_tac -1, erule_tac x=ae in allE)
         apply (rotate_tac -1, erule_tac x=af in allE)
         apply (rotate_tac -1, erule_tac x=bc in allE, erule mp)
         apply (rule, rule) 
            apply (erule Goto) 
(*If*) 
apply clarsimp
apply (rotate_tac 5) apply (erule thin_rl,erule thin_rl)
apply (simp add: mbody_is_def validn_def Opsem_def MS_def Reach_def, clarsimp)
apply rule
  apply clarsimp apply (erule eval_cases) apply simp
    apply clarsimp apply (drule IfElim1) apply (simp, clarsimp)
    apply (erule disjE)
    apply clarsimp
      apply (rotate_tac 3) apply (erule thin_rl)
      apply (rotate_tac -1)
      apply (erule_tac x=ad in allE)
      apply (erule_tac x=bb in allE)
      apply (erule_tac x=a in allE, rotate_tac -1)
      apply (erule_tac x=af in allE)
      apply (erule_tac x=bc in allE, erule impE)
        apply rule
          apply (erule MultiApp)
            apply (erule IfT, simp) 
      apply (erule impE, simp add: SP_pre_def) apply (rule, rule, rule, rule) prefer 2 
            apply (rule, rule, erule IfT, simp) apply fastforce
         apply (erule_tac x=ma in allE, clarsimp)
           apply (erule_tac x=h in allE, erule_tac x=v in allE, clarsimp)
           apply (simp add: SP_post_def)
           apply (rotate_tac -1)
           apply (erule_tac x="TRUE # a" in allE, erule_tac x=af in allE, erule_tac x=bc in allE, erule impE)
             apply (rule, rule, rule IfT, simp,simp)
           apply clarsimp
    apply clarsimp
      apply (rotate_tac 2) apply (erule thin_rl)
      apply (erule_tac x=ad in allE)
      apply (erule_tac x=bb in allE)
      apply (erule_tac x=a in allE, rotate_tac -1)
      apply (erule_tac x=af in allE)
      apply (erule_tac x=bc in allE, erule impE)
        apply rule
          apply (erule MultiApp)
            apply (rule IfF) apply (simp, assumption, simp) apply simp
      apply (erule impE, simp add: SP_pre_def) apply (rule, rule, rule, rule) prefer 2 
            apply (rule, rule, rule IfF) apply (simp, assumption) apply fastforce
            apply simp
            apply clarsimp
         apply (erule_tac x=ma in allE, clarsimp)
           apply (erule_tac x=h in allE, erule_tac x=v in allE, clarsimp)
           apply (simp add: SP_post_def)
           apply (rotate_tac -1)
           apply (erule_tac x="va # a" in allE, erule_tac x=af in allE, erule_tac x=bc in allE, erule impE)
             apply (rule, rule, rule IfF) apply (simp, assumption) apply fastforce apply simp
           apply clarsimp
apply clarsimp
apply rule
  apply clarsimp 
    apply (case_tac ka) apply clarsimp apply (drule ZeroHeightMultiElim) apply clarsimp 
    apply clarsimp
    apply (rotate_tac -2, drule MultiSplit) apply simp apply clarsimp
      apply (drule IfElim1) apply simp apply clarsimp 
      apply (erule disjE)
      apply clarsimp
        apply (rotate_tac 4) apply (erule thin_rl)
        apply (rotate_tac -1)
        apply (erule_tac x=ad in allE)
        apply (erule_tac x=bb in allE)
        apply (erule_tac x=ag in allE, rotate_tac -1)
        apply (erule_tac x=af in allE)
        apply (erule_tac x=bc in allE, erule impE)
          apply rule
            apply (erule MultiApp)
              apply (rule IfT) apply (simp, fastforce) 
        apply (erule impE, simp add: SP_pre_def) apply (rule, rule, rule,rule) prefer 2 
           apply (rule, rule, rule IfT) apply simp apply fastforce
           apply clarsimp
        apply (erule_tac x=ma in allE, clarsimp)
        apply (erule_tac x=ll in allE, rotate_tac -1)
        apply (erule_tac x=a in allE, rotate_tac -1)
        apply (erule_tac x=aa in allE, rotate_tac -1)
        apply (erule_tac x=b in allE, rotate_tac -1, clarsimp)
      apply clarsimp
        apply (rotate_tac 3) apply (erule thin_rl)
        apply (erule_tac x=ad in allE)
        apply (erule_tac x=bb in allE)
        apply (erule_tac x=ag in allE, rotate_tac -1)
        apply (erule_tac x=af in allE)
        apply (erule_tac x=bc in allE, erule impE)
          apply rule
            apply (erule MultiApp)
              apply (rule IfF) apply (simp, assumption, simp) apply simp
        apply (erule impE, simp add: SP_pre_def) apply (rule, rule, rule, rule) prefer 2 
           apply (rule, rule, rule IfF) apply (simp, assumption) apply fastforce apply simp 
           apply clarsimp
        apply (erule_tac x=ma in allE, clarsimp)
        apply (erule_tac x=ll in allE, rotate_tac -1)
        apply (erule_tac x=a in allE, rotate_tac -1)
        apply (erule_tac x=aa in allE, rotate_tac -1)
        apply (erule_tac x=b in allE, rotate_tac -1, clarsimp)
  apply clarsimp 
    apply (case_tac ka) apply clarsimp apply (drule ZeroHeightReachableElim) apply clarsimp 
    apply clarsimp
    apply (rotate_tac -2, drule ReachableSplit) apply simp apply clarsimp
      apply (drule IfElim1) apply simp apply clarsimp 
      apply (erule disjE)
      apply clarsimp
        apply (rotate_tac 4) apply (erule thin_rl)
        apply (rotate_tac -1)
        apply (erule_tac x=ad in allE)
        apply (erule_tac x=bb in allE)
        apply (erule_tac x=ag in allE, rotate_tac -1)
        apply (erule_tac x=af in allE)
        apply (erule_tac x=bc in allE, erule impE)
          apply rule
            apply (erule MultiApp)
              apply (rule IfT) apply (simp, fastforce) 
        apply (erule impE, simp add: SP_pre_def) apply (rule, rule, rule, rule) prefer 2 
           apply (rule, rule, rule IfT) apply simp apply fastforce
           apply clarsimp
        apply (erule_tac x=ma in allE, clarsimp)
         apply (rotate_tac -1, erule_tac x=ll in allE)
         apply (rotate_tac -1, erule_tac x=a in allE)
         apply (rotate_tac -1, erule_tac x=aa in allE)
         apply (rotate_tac -1, erule_tac x=b in allE, clarsimp)
         apply (simp add: SP_inv_def) 
(*         apply (rotate_tac -1, erule_tac x=pc in allE)*)
         apply (rotate_tac -1, erule_tac x="TRUE#ag" in allE)
         apply (rotate_tac -1, erule_tac x=af in allE)
         apply (rotate_tac -1, erule_tac x=bc in allE)
         apply (rotate_tac -1, erule impE)
            apply (rule, rule, erule IfT) apply simp
         apply clarsimp
      apply clarsimp
        apply (rotate_tac 3) apply (erule thin_rl)
        apply (erule_tac x=ad in allE)
        apply (erule_tac x=bb in allE)
        apply (erule_tac x=ag in allE, rotate_tac -1)
        apply (erule_tac x=af in allE)
        apply (erule_tac x=bc in allE, erule impE)
          apply rule
            apply (erule MultiApp)
              apply (erule IfF) apply (assumption, simp, simp) 
        apply (erule impE, simp add: SP_pre_def) apply (rule, rule, rule, rule) prefer 2 
           apply (rule, rule, erule IfF) apply (assumption, fastforce,simp) 
           apply clarsimp
        apply (erule_tac x=ma in allE, clarsimp)
         apply (rotate_tac -1, erule_tac x=ll in allE)
         apply (rotate_tac -1, erule_tac x=a in allE)
         apply (rotate_tac -1, erule_tac x=aa in allE)
         apply (rotate_tac -1, erule_tac x=b in allE, clarsimp)
         apply (simp add: SP_inv_def) 
(*         apply (rotate_tac -1, erule_tac x="Suc l" in allE)*)
         apply (rotate_tac -1, erule_tac x="v#ag" in allE)
         apply (rotate_tac -1, erule_tac x=af in allE)
         apply (rotate_tac -1, erule_tac x=bc in allE)
         apply (rotate_tac -1, erule impE)
         apply (rule, rule) 
            apply (erule IfF) apply (assumption, simp, simp) 
         apply clarsimp
(*RET*)
apply clarsimp
apply (simp add: mbody_is_def validn_def Opsem_def MS_def Reach_def, clarsimp)
apply rule
  apply clarsimp apply (erule eval_cases) apply clarsimp
    apply (drule RetElim1) apply simp apply simp
apply clarsimp
apply rule
  apply clarsimp 
    apply (case_tac ka) apply clarsimp apply (drule ZeroHeightMultiElim) apply clarsimp 
    apply clarsimp
    apply (rotate_tac -2, drule MultiSplit) apply simp apply clarsimp
      apply (drule RetElim1, clarsimp) apply simp  
apply clarsimp 
    apply (case_tac ka) apply clarsimp apply (drule ZeroHeightReachableElim) apply clarsimp 
    apply clarsimp
    apply (rotate_tac -2, drule ReachableSplit) apply simp apply clarsimp
      apply (drule RetElim1, clarsimp) apply simp  
(*INVS*)
apply clarsimp
  apply (subgoal_tac "INVS_soundK K G C m l D m' T MI Anno Anno2 (par,code,l0) A B I")
  apply (simp add: INVS_soundK_def) 
  apply (erule impE) apply (simp add: INVS_SC_def) apply (rule, rule, rule, rule) apply assumption apply (rule, assumption)
     apply assumption
  apply assumption
  apply (rule INVS_soundK_all)
(*CONSEQ*)
apply clarsimp 
apply rule
  apply clarsimp
  apply (simp add: validn_def,clarsimp)
  apply (erule thin_rl)
  apply (rotate_tac 5, erule thin_rl)
  apply (erule_tac x=a in allE, rotate_tac -1)
  apply (erule_tac x=aa in allE, rotate_tac -1)
  apply (erule_tac x=ba in allE, clarsimp, rotate_tac -1)
  apply (erule_tac x=ab in allE)
  apply (erule_tac x=bb in allE) 
  apply (rotate_tac -1)
  apply (erule_tac x=ac in allE, rotate_tac -1)
  apply (erule_tac x=ad in allE, rotate_tac -1)
  apply (erule_tac x=bc in allE, clarsimp)
  apply (erule_tac x=k in allE, clarsimp)
  apply (rotate_tac -1)
    apply (erule_tac x=ll in allE, rotate_tac -1)
    apply (erule_tac x=ae in allE, rotate_tac -1)
    apply (erule_tac x=af in allE)
    apply (erule_tac x=bd in allE, clarsimp)
  apply clarsimp
  apply (simp add: validn_def,clarsimp)
  apply (erule thin_rl)
  apply (rotate_tac 5, erule thin_rl)
  apply (erule_tac x=a in allE, rotate_tac -1)
  apply (erule_tac x=aa in allE, rotate_tac -1)
  apply (erule_tac x=ba in allE, clarsimp, rotate_tac -1)
  apply (erule_tac x=ab in allE)
  apply (erule_tac x=bb in allE) 
  apply (rotate_tac -1)
  apply (erule_tac x=ac in allE, rotate_tac -1)
  apply (erule_tac x=ad in allE, rotate_tac -1)
  apply (erule_tac x=bc in allE, clarsimp)
  apply (erule_tac x=k in allE, clarsimp)
  apply (rotate_tac -1)
    apply (erule_tac x=ll in allE, rotate_tac -1)
    apply (erule_tac x=ae in allE, rotate_tac -1)
    apply (erule_tac x=af in allE)
    apply (erule_tac x=bd in allE, clarsimp)
(*INJECT*)
apply clarsimp apply (rule validn_lower) apply fast apply simp
(*AX*)
apply clarsimp apply (simp add: G_validn_def) 
done
(*>*)

text\<open>The statement of this lemma gives a semantic interpretation of
the two judgement forms, as \<open>SP_Assum\<close>-judgements enjoy validity
up to execution height $K$, while \<open>SP_Deriv\<close>-judgements are
valid up to level $K+1$.\<close>

(*<*)
lemma SOUND_K: 
  "\<lbrakk> G \<rhd> \<lbrace>A\<rbrace> C,m,l \<lbrace>B\<rbrace> I; G_validn K G ; MST_validn K\<rbrakk>  
  \<Longrightarrow> \<Turnstile>\<^sub>(Suc K) \<lbrace>A\<rbrace> C, m, l \<lbrace>B\<rbrace> I"
apply (drule SOUND_Aux)  apply assumption+ apply simp
done
(*>*)

text\<open>From this, we obtain a soundness result that still involves
context validity.\<close>

theorem SOUND_in_CTXT: 
 "\<lbrakk>G \<rhd> \<lbrace>A\<rbrace> C,m,l \<lbrace>B\<rbrace> I; G_valid G; MST_valid\<rbrakk> \<Longrightarrow> \<Turnstile> \<lbrace>A\<rbrace> C, m, l \<lbrace>B\<rbrace> I"
(*<*)
apply (rule validn_valid)
apply clarsimp
apply (rule validn_lower)
apply (erule SOUND_K)
prefer 3 apply (subgoal_tac "K \<le> Suc K", assumption) apply simp
apply (erule G_valid_validn)
apply (erule MST_valid_validn)
done
(*>*)

text\<open>We will now show that the two semantic assumptions can be replaced by
the verified-program property.\<close>

subsection\<open>Soundness of verified programs \label{SectionContextElimination}\<close> 

text\<open>In order to obtain a soundness result that does not require
validity assumptions of the context or the specification table,
we show that the \<open>VP\<close> property implies context validity.
First, the elimination of contexts. By induction on
\<open>k\<close> we prove\<close>

lemma VPG_MSTn_Gn[rule_format]:
"VP_G G \<longrightarrow> MST_validn k \<longrightarrow> G_validn k G"
(*<*)
apply (induct k)
(*k=0*)
  apply clarsimp
    apply (simp add: VP_G_def, clarsimp) 
    apply (simp add: G_validn_def, clarsimp)
    apply (simp add: validn_def) apply clarsimp 
        apply rule 
          apply clarsimp apply (drule no_zero_height_Exec_derivs) apply simp
        apply clarsimp
        apply rule
          apply clarsimp apply (drule ZeroHeightMultiElim) apply clarsimp
            apply (rotate_tac 2)
            apply (erule_tac x=C in allE, erule_tac x=m in allE)
            apply (erule_tac x=a in allE, erule_tac x=aa in allE, erule_tac x=b in allE, clarsimp)
            apply (erule_tac x=C in allE, erule_tac x=m in allE)
            apply (erule_tac x=l in allE, erule_tac x=A in allE, erule_tac x=B in allE, clarsimp)
            apply (rule AssertionsImplyAnnoInvariants)
             prefer 3 apply assumption
             apply assumption+
          apply clarsimp apply (drule ZeroHeightReachableElim) apply clarsimp
            apply (rotate_tac 2)
            apply (erule_tac x=C in allE, erule_tac x=m in allE)
            apply (erule_tac x=a in allE, erule_tac x=aa in allE, erule_tac x=b in allE, clarsimp)
            apply (erule_tac x=C in allE, erule_tac x=m in allE, 
                   erule_tac x=l in allE, erule_tac x=A in allE, erule_tac x=B in allE, clarsimp)
            apply (erule AssertionsImplyMethInvariants, assumption+)
(*k>0*)
 apply clarsimp apply (simp add: VP_G_def)
   apply (simp (no_asm) add: G_validn_def, clarsimp)
   apply (subgoal_tac "MST_validn k", clarsimp)
   apply (rule SOUND_K) apply fast 
   apply assumption
   apply assumption
   apply (erule MST_validn_lower) apply simp 
done
(*>*)

text\<open>which implies\<close>

lemma VPG_MST_G: "\<lbrakk>VP_G G; MST_valid\<rbrakk> \<Longrightarrow> G_valid G"
(*<*)
apply (rule G_validn_valid, clarsimp)
apply (erule VPG_MSTn_Gn)
apply (erule MST_valid_validn)
done
(*>*)

text\<open>Next, the elimination of \<open>MST_valid\<close>. Again by induction on
\<open>k\<close>, we prove\<close>

lemma VPG_MSTn[rule_format]: "VP_G G \<longrightarrow> MST_validn k"
(*<*)
apply (induct k)
apply (simp add: MST_validn_def, clarsimp)
  apply (simp add: validn_def, clarsimp)
  apply rule
    apply clarsimp apply (drule no_zero_height_Exec_derivs) apply simp 
  apply clarsimp
  apply rule
    apply clarsimp apply (drule ZeroHeightMultiElim) apply clarsimp 
    apply (simp add: VP_G_def, clarsimp, rotate_tac -1)
    apply (erule_tac x=C in allE, erule_tac x=m in allE)
    apply (erule_tac x=par in allE, erule_tac x=code in allE, erule_tac x=l0 in allE, clarsimp)
    apply (rule AssertionsImplyAnnoInvariants) apply fast apply assumption+ apply simp
  apply clarsimp apply (drule ZeroHeightReachableElim) apply clarsimp
    apply (simp add: VP_G_def, clarsimp, rotate_tac -1)
    apply (erule_tac x=C in allE, erule_tac x=m in allE)
    apply (erule_tac x=par in allE, erule_tac x=code in allE, erule_tac x=l0 in allE, clarsimp)
    apply (frule AssertionsImplyMethInvariants) apply assumption apply (simp add: mkState_def) 
apply clarsimp
  apply (frule VPG_MSTn_Gn, assumption)
  apply (simp add: VP_G_def)
  apply (simp (no_asm) add: MST_validn_def, clarsimp)
  apply (rule SOUND_K)
   apply (rotate_tac 3) 
   apply (erule_tac x=C in allE, erule_tac x=m in allE)
   apply (erule_tac x=par in allE, erule_tac x=code in allE, erule_tac x=l0 in allE, clarsimp) apply assumption
  apply assumption
  apply assumption
done
(*>*)

text\<open>which yields\<close>

lemma VPG_MST:"VP_G G \<Longrightarrow> MST_valid"
(*<*)
apply (rule MST_validn_valid, clarsimp)
apply (erule VPG_MSTn)
done
(*>*)

text\<open>Combining these two results, and unfolding the definition of
program validity yields the final soundness result.\<close>

theorem VP_VALID: "VP \<Longrightarrow> Prog_valid"
(*<*)
apply (simp add: VP_def Prog_valid_def, clarsimp)
apply (frule VPG_MST, simp)
apply (drule VPG_MST_G, assumption) apply fast
done
(*>*)

(*<*)

text \<open>In particular, the $\mathit{VP}$ property implies that all
method specifications are honoured by their respective method
implementations.\<close>

theorem "VP \<Longrightarrow> MST_valid"
(*<*)
by (drule VP_VALID, simp add: Prog_valid_def)
(*>*)

end
(*>*)
