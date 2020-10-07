(*File: VS.thy*)
(*Authors: Lennart Beringer and Martin Hofmann, LMU Munich 2008*)
theory VS imports VDM begin
section\<open>Base-line noninterference\<close>

text\<open>\label{sec:BaseLineNI} We now show how to interprete the type
system of Volpano, Smith and Irvine~\cite{VolpanoSmithIrvine:JCS1996},
as described in Section 3 of our
paper~\cite{BeringerHofmann:CSF2007}.\<close>

subsection\<open>Basic definitions\<close>

text\<open>Muli-level security being treated in Section
\ref{sec:HuntSands}, we restrict our attention in the present section
to the two-point security lattice.\<close>

datatype TP = low | high

text\<open>A global context assigns a security type to each program
variable.\<close>

consts CONTEXT :: "Var \<Rightarrow> TP"

text\<open>Next, we define when two states are considered (low)
equivalent.\<close>

definition twiddle::"State \<Rightarrow> State \<Rightarrow> bool" (" _ \<approx> _ " [100,100] 100)
where "s \<approx> ss = (\<forall> x. CONTEXT x = low \<longrightarrow> s x = ss x)"

text\<open>A command $c$ is \emph{secure} if the low equivalence of any two
initial states entails the equivalence of the corresponding final
states.\<close>

definition secure::"IMP \<Rightarrow> bool"
where "secure c = (\<forall> s t ss tt . s \<approx> t \<longrightarrow> (s,c \<Down> ss) \<longrightarrow> 
                          (t,c \<Down> tt) \<longrightarrow> ss \<approx> tt)"

text \<open>Here is the definition of the assertion transformer
that is called $\mathit{Sec}$ in the paper \ldots\<close>

definition Sec :: "((State \<times> State) \<Rightarrow> bool) \<Rightarrow> VDMAssn"
where "Sec \<Phi> s t = ((\<forall> r . s \<approx> r \<longrightarrow> \<Phi>(t, r)) \<and> (\<forall> r . \<Phi>(r ,s) \<longrightarrow> r \<approx> t))"

text\<open>\ldots and the proofs of two directions of its characteristic
property, Proposition 1.\<close>

lemma Prop1A:"\<Turnstile> c : (Sec \<Phi>) \<Longrightarrow> secure c"
(*<*)
by (simp add: VDM_valid_def secure_def Sec_def)
(*>*)

lemma Prop1B:
  "secure c \<Longrightarrow> \<Turnstile> c : Sec (\<lambda> (r, t) . \<exists> s . (s , c \<Down> r) \<and> s \<approx> t)"
(*<*)
apply (simp add: VDM_valid_def Sec_def) 
apply clarsimp
apply (unfold secure_def)
apply rule
apply (rule, rule) apply (rule_tac x=s in exI) apply(rule, assumption+)
apply (rule, rule, erule exE, erule conjE) apply fast
done
(*>*)

lemma Prop1BB:"secure c \<Longrightarrow> \<exists> \<Phi> . \<Turnstile> c : Sec \<Phi>"
(*<*)
by (drule Prop1B, fast)
(*>*)

lemma Prop1:
"(secure c) = (\<Turnstile> c : Sec (\<lambda> (r, t) . \<exists> s . (s , c \<Down> r) \<and> s \<approx> t))"
(*<*)
apply rule
apply (erule Prop1B)
apply (erule Prop1A)
done
(*>*)

subsection\<open>Derivation of the LOW rules\<close>

text\<open>We now derive the interpretation of the LOW rules of Volpano et
al's paper according to the constructions given in the paper. (The
rules themselves are given later, since they are not yet needed).\<close>

lemma CAST[rule_format]:
  "G \<rhd> c : twiddle \<longrightarrow> G \<rhd> c : Sec (\<lambda> (s,t) . s \<approx> t)"
(*<*)
apply clarsimp
apply (erule VDMConseq)  apply (simp add: twiddle_def Sec_def)
done
(*>*)

lemma SKIP: "G \<rhd> Skip : Sec (\<lambda> (s,t) . s \<approx> t)"
(*<*)
apply (rule VDMConseq, rule VDMSkip)
apply (simp add: Sec_def twiddle_def)
done
(*>*)

lemma ASSIGN: 
  "(\<forall> s ss. s \<approx> ss \<longrightarrow> evalE e s = evalE e ss) \<Longrightarrow>
   G \<rhd> (Assign x e) 
     : (Sec (\<lambda> (s, t) . s \<approx> (update t x (evalE e t))))"
(*<*)
 apply (rule VDMConseq) apply(rule VDMAssign)
  apply clarsimp apply (simp add: Sec_def)
  apply clarsimp 
  apply (erule_tac x=s in allE, erule_tac x=r in allE, clarsimp)
  apply (simp add: twiddle_def update_def)
done
(*>*)

lemma COMP: 
  "\<lbrakk> G \<rhd> c1 : (Sec \<Phi>); G \<rhd> c2 : (Sec \<Psi>)\<rbrakk> \<Longrightarrow>
     G \<rhd> (Comp c1 c2) : (Sec (\<lambda> (s,t) . \<exists> r . \<Phi>(r, t) \<and> 
                           (\<forall> w . (r \<approx> w \<longrightarrow> \<Psi>(s, w)))))"
(*<*)
apply (rule VDMConseq) apply (erule VDMComp) apply assumption
    apply (simp add: Sec_def, clarsimp)
    apply rule
      apply clarsimp apply (erule_tac x=ra in allE, clarsimp)
        apply (rule_tac x=r in exI, clarsimp) 
     apply clarsimp
done
(*>*)

lemma IFF:
  "\<lbrakk> (\<forall> s ss. s \<approx> ss \<longrightarrow> evalB b s = evalB b ss);
     G \<rhd> c1 : (Sec \<Phi>); G \<rhd> c2 : (Sec \<Psi>)\<rbrakk> \<Longrightarrow>
     G \<rhd> (Iff b c1 c2) : Sec (\<lambda> (s, t) . (evalB b t \<longrightarrow> \<Phi>(s,t)) \<and> 
                                        ((\<not> evalB b t) \<longrightarrow> \<Psi>(s,t)))"
(*<*)
 apply (rule VDMConseq) apply(rule VDMIff) apply assumption+
  apply clarsimp apply (simp add: Sec_def)
  apply clarsimp 
  apply (case_tac "evalB b s")
  apply clarsimp 
  apply clarsimp 
done
(*>*)

text\<open>We introduce an explicit fixed point construction over the type
$TT$ of the invariants $\Phi$.\<close>

type_synonym TT = "(State \<times> State) \<Rightarrow> bool"

text\<open>We deliberately introduce a new type here since the agreement
with \<open>VDMAssn\<close> (modulo currying) is purely coincidental. In
particular, in the generalisation for objects in Section
\ref{sec:Objects} the type of invariants will differ from the
type of program logic assertions.\<close>

definition FIX::"(TT \<Rightarrow> TT) \<Rightarrow> TT"
where "FIX \<phi> = (\<lambda> (s,t). \<forall> \<Phi>. (\<forall> ss tt . \<phi> \<Phi> (ss,tt) \<longrightarrow> \<Phi> (ss,tt)) 
         \<longrightarrow> \<Phi> (s,t))" 

definition Monotone::"(TT \<Rightarrow> TT) \<Rightarrow> bool"
where "Monotone \<phi> = (\<forall> \<Phi> \<Psi> . (\<forall> s t . \<Phi>(s,t) \<longrightarrow> \<Psi>(s,t)) \<longrightarrow> 
                        (\<forall> s t . \<phi> \<Phi> (s,t) \<longrightarrow> \<phi> \<Psi> (s,t)))"

(*<*)
lemma Fix2: "\<lbrakk>Monotone \<phi>; \<phi> (FIX \<phi>) (s, t)\<rbrakk> \<Longrightarrow> FIX \<phi> (s,t)"
apply (simp add: FIX_def) apply clarsimp
apply (subgoal_tac "\<phi> \<Phi> (s,t)", simp)
apply (subgoal_tac "\<forall> r u . FIX \<phi> (r,u) \<longrightarrow> \<Phi>(r,u)")
prefer 2 apply (erule thin_rl) apply (simp add: FIX_def) apply clarsimp
  apply (erule_tac x=\<Phi> in allE, simp)
apply (unfold Monotone_def)
  apply (erule_tac x="FIX \<phi>" in allE, erule_tac x="\<Phi>" in allE)
  apply (erule impE) apply assumption
  apply (simp add: FIX_def)
done

lemma Fix1: "\<lbrakk>Monotone \<phi>; FIX \<phi> (s,t)\<rbrakk> \<Longrightarrow> \<phi> (FIX \<phi>) (s,t)"
apply (simp add: FIX_def) 
apply (erule_tac x="\<phi>(FIX \<phi>)" in allE) 
apply (erule impE)
prefer 2 apply (simp add: FIX_def)
apply (subgoal_tac "\<forall> r u .\<phi>(FIX \<phi>) (r,u) \<longrightarrow> (FIX \<phi>) (r,u)")
  prefer 2 apply clarsimp apply (erule Fix2) apply assumption
apply (unfold Monotone_def)
  apply (erule_tac x="\<phi>(FIX \<phi>)" in allE, erule_tac x="(FIX \<phi>)" in allE, erule impE) apply assumption
apply simp
done
(*>*)

text\<open>For monotone invariant transformers $\varphi$, the construction indeed
yields a fixed point.\<close>

lemma Fix_lemma:"Monotone \<phi> \<Longrightarrow> \<phi> (FIX \<phi>) = FIX \<phi>"
(*<*)
apply (rule ext, rule iffI)
apply clarsimp  apply (erule Fix2) apply assumption
apply clarsimp  apply (erule Fix1) apply assumption
done
(*>*)

text\<open>In order to derive the while rule we define the following
transfomer.\<close>

definition PhiWhileOp::"BExpr \<Rightarrow> TT \<Rightarrow> TT \<Rightarrow> TT"
where "PhiWhileOp b \<Phi> =
     (\<lambda> \<Psi> . (\<lambda>(s, t).
             (evalB b t \<longrightarrow> (\<exists>r. \<Phi> (r, t) \<and> 
                                 (\<forall>w. r \<approx> w \<longrightarrow> \<Psi> (s, w)))) \<and> 
             (\<not> evalB b t \<longrightarrow> s \<approx> t)))"

text\<open>Since this operator is monotone, \ldots\<close>

lemma PhiWhileOp_Monotone: "Monotone (PhiWhileOp b \<Phi>)"
(*<*)
apply (simp add: PhiWhileOp_def Monotone_def) apply clarsimp
  apply (rule_tac x=r in exI, simp)
done
(*>*)

text\<open>we may define its fixed point,\<close>

definition PhiWhile::"BExpr \<Rightarrow> TT \<Rightarrow> TT"
where "PhiWhile b \<Phi> = FIX (PhiWhileOp b \<Phi>)"

text\<open>which we can use to derive the following rule.\<close>

lemma WHILE:  
  "\<lbrakk> (\<forall> s t. s \<approx> t \<longrightarrow> evalB b s = evalB b t); G \<rhd> c : (Sec \<Phi>)\<rbrakk> \<Longrightarrow>
   G \<rhd> (While b c) : (Sec (PhiWhile b \<Phi>))"
(*<*)
apply (rule VDMConseq)
apply (rule VDMWhile) 
prefer 4 apply (subgoal_tac "\<forall>s t. (Sec (PhiWhileOp b \<Phi> (PhiWhile b \<Phi>))) s t \<and> \<not> evalB b t \<longrightarrow> Sec (PhiWhile b \<Phi>) s t") apply assumption
  apply clarsimp apply (subgoal_tac "PhiWhileOp b \<Phi> (PhiWhile b \<Phi>)= PhiWhile b \<Phi>", clarsimp)
                 apply (simp add: PhiWhile_def) apply (rule Fix_lemma) apply (rule PhiWhileOp_Monotone)
apply assumption
apply clarsimp apply (simp add: Sec_def) 
  apply (rule, clarsimp) apply (simp add: PhiWhileOp_def)
  apply clarsimp apply (simp add: PhiWhileOp_def)
apply clarsimp apply (simp add: Sec_def)
  apply rule
  prefer 2 apply clarsimp
    apply (subgoal_tac "\<exists>r. \<Phi> (r, s) \<and> (\<forall>w. r \<approx> w \<longrightarrow> (PhiWhile b \<Phi>) (ra, w))")
    prefer 2 apply (simp add: PhiWhileOp_def) 
    apply clarsimp apply (rotate_tac -3, erule thin_rl)
    apply (rotate_tac -1, erule_tac x=ra in allE, erule mp)
    apply (rotate_tac 1, erule_tac x=r in allE, erule impE) apply fast
    apply (subgoal_tac "PhiWhileOp b \<Phi> (PhiWhile b \<Phi>) = PhiWhile b \<Phi>", clarsimp)
    apply (simp add: PhiWhile_def)
    apply (rule Fix_lemma) apply (rule PhiWhileOp_Monotone)
  apply clarsimp
    apply (simp (no_asm_simp) add: PhiWhileOp_def)
    apply (rule_tac x=r in exI, rule) apply simp
    apply clarsimp
    apply (rotate_tac 5, erule_tac x=w in allE, clarsimp)
    apply (subgoal_tac "PhiWhileOp b \<Phi> (PhiWhile b \<Phi>) = PhiWhile b \<Phi>", clarsimp)
    apply (simp add: PhiWhile_def)
    apply (rule Fix_lemma) apply (rule PhiWhileOp_Monotone)
done
(*>*)

text\<open>The operator that given $\Phi$ returns the invariant
occurring in the conclusion of the rule is itself monotone - this is
the property required for the rule for procedure invocations.\<close>

lemma PhiWhileMonotone: "Monotone (\<lambda> \<Phi> . PhiWhile b \<Phi>)"
(*<*)
apply (simp add: Monotone_def) apply clarsimp
apply (simp add: PhiWhile_def)
apply (simp add: FIX_def) apply clarsimp
apply (erule_tac x=\<Phi>' in allE, erule mp)
apply (clarsimp) apply (erule_tac x=ss in allE, erule_tac x=tt in allE, erule mp)
apply (simp add: PhiWhileOp_def) apply clarsimp
apply (rule_tac x=r in exI, simp)
done
(*>*)

text\<open>We now derive an alternative while rule that employs an
inductive formulation of a variant that replaces the fixed point
construction. This version is given in the paper.\<close>

text\<open>First, the inductive definition of the $\mathit{var}$ relation.\<close>

inductive_set var::"(BExpr \<times> TT \<times> State \<times> State) set"
where
varFalse: "\<lbrakk>\<not> evalB b t; s \<approx> t\<rbrakk> \<Longrightarrow> (b,\<Phi>,s,t):var"
| varTrue:"\<lbrakk>evalB b t; \<Phi>(r,t); \<forall> w . r \<approx> w \<longrightarrow> (b,\<Phi>,s,w): var\<rbrakk>
           \<Longrightarrow> (b,\<Phi>,s,t):var"

text\<open>It is easy to prove the equivalence of $\mathit{var}$ and the
fixed point:\<close>

(*<*)
lemma varFIX: "(b,\<Phi>,s,t):var \<Longrightarrow> PhiWhile b \<Phi> (s,t)"
apply (erule var.induct)
apply (simp add: PhiWhile_def)
  apply (subgoal_tac "PhiWhileOp b \<Phi> (FIX (PhiWhileOp b \<Phi>)) (s,t)")
  apply (subgoal_tac "PhiWhileOp b \<Phi> (FIX (PhiWhileOp b \<Phi>)) = FIX (PhiWhileOp b \<Phi>)", clarsimp)
  apply (rule Fix_lemma) apply (rule PhiWhileOp_Monotone)
  apply (simp add: PhiWhileOp_def)
apply (simp (no_asm_simp) add: PhiWhile_def)
apply (subgoal_tac "PhiWhileOp b \<Phi> (FIX (PhiWhileOp b \<Phi>)) (s,t)")
  apply (subgoal_tac "PhiWhileOp b \<Phi> (FIX (PhiWhileOp b \<Phi>)) = FIX (PhiWhileOp b \<Phi>)", clarsimp)
  apply (rule Fix_lemma) apply (rule PhiWhileOp_Monotone)
  apply (simp add: PhiWhileOp_def)
  apply (rule_tac x=r in exI, simp)
  apply clarsimp
  apply (erule_tac x=w in allE, clarsimp)
  apply (simp add: PhiWhile_def)
  apply (simp add: PhiWhileOp_def)
done

lemma FIXvar: "PhiWhile b \<Phi> (s,t) \<Longrightarrow> (b,\<Phi>,s,t):var"
apply (simp add: PhiWhile_def)
apply (subgoal_tac "PhiWhileOp b \<Phi> (FIX (PhiWhileOp b \<Phi>)) (s, t)")
prefer 2 
  apply (subgoal_tac "PhiWhileOp b \<Phi> (FIX (PhiWhileOp b \<Phi>)) = FIX (PhiWhileOp b \<Phi>)", clarsimp)
  apply (rule Fix_lemma) apply (rule PhiWhileOp_Monotone)
apply (erule thin_rl, simp add: PhiWhileOp_def) apply clarsimp
  apply (case_tac "evalB b t")
  prefer 2 apply clarsimp apply (rule varFalse) apply assumption+
  apply clarsimp apply (rule varTrue) apply assumption apply assumption 
    apply clarsimp apply (erule_tac x=w in allE, clarsimp)
    apply (unfold FIX_def) apply clarify
    apply (erule_tac x="\<lambda> (x,y) . (b,\<Phi>,x,y):var" in allE, erule impE) prefer 2 apply simp
    apply clarsimp
    apply (case_tac "evalB b tt")
    prefer 2 apply clarsimp apply (rule varFalse) apply assumption+
    apply clarsimp apply (rule varTrue) apply assumption+
done

lemma varFIXvar: "(PhiWhile b \<Phi> (s,t)) = ((b,\<Phi>,s,t):var)"
apply rule
apply (erule FIXvar)
apply (erule varFIX)
done

lemma FIXvarFIX': "(PhiWhile b \<Phi>) = (\<lambda> (s,t) . (b,\<Phi>,s,t):var)"
apply (rule ext, rule iffI)
apply (case_tac x, clarsimp) apply (erule FIXvar)
apply (case_tac x, clarsimp) apply (simp add: varFIXvar)
done
(*>*)

lemma FIXvarFIX: "(PhiWhile b) = (\<lambda> \<Phi> . (\<lambda> (s,t) . (b,\<Phi>,s,t):var))"
(*<*)
by (rule, rule FIXvarFIX')
(*>*)

text\<open>From this rule and the rule WHILE above, one may derive the
while rule we gave in the paper.\<close> 

lemma WHILE_IND:
  "\<lbrakk> (\<forall> s t. s \<approx> t \<longrightarrow> evalB b s = evalB b t); G \<rhd> c : (Sec \<Phi>)\<rbrakk> \<Longrightarrow>
   G \<rhd> (While b c) : (Sec (\<lambda> (s,t) . (b,\<Phi>,s,t):var))"
(*<*)
apply (rule VDMConseq)
apply (rule WHILE [of b G c \<Phi>]) apply assumption+
apply (simp add: FIXvarFIX)
done
(*>*)

text\<open>Not suprisingly, the construction $\mathit{var}$ can be shown to
be monotone in $\Phi$.\<close>
(*<*)
lemma varMonotoneAux[rule_format]:
  "(b, \<Phi>, s, t) \<in> var \<Longrightarrow> 
   (\<forall>s t. \<Phi> (s, t) \<longrightarrow> \<Psi> (s, t)) \<longrightarrow> (b, \<Psi>, s, t) \<in> var"
apply (erule var.induct)
apply clarsimp apply (erule varFalse, simp)
apply clarsimp apply (erule varTrue) apply fast apply simp
done
(*>*)

lemma var_Monotone: "Monotone (\<lambda> \<Phi> . (\<lambda> (s,t) .(b,\<Phi>,s,t):var))"
(*<*)
apply (simp add: Monotone_def)
apply clarsimp
apply (rule varMonotoneAux) apply assumption apply simp
done
(*>*)

(*<*)
lemma varMonotone_byFIX: "Monotone (\<lambda> \<Phi> . (\<lambda> (s,t) .(b,\<Phi>,s,t):var))"
apply (subgoal_tac "Monotone (\<lambda> \<Phi> . PhiWhile b \<Phi>)")
apply (simp add: FIXvarFIX)
apply (rule PhiWhileMonotone)
done  
(*>*)

text\<open>The call rule is formulated for an arbitrary fixed point of
a monotone transformer.\<close>

lemma CALL: 
  "\<lbrakk> ({Sec(FIX \<Phi>)} \<union> G) \<rhd> body : Sec(\<Phi> (FIX \<Phi>)); Monotone \<Phi>\<rbrakk> \<Longrightarrow>
   G \<rhd> Call : Sec(FIX \<Phi>)"
(*<*)
apply (rule VDMCall)
apply (subgoal_tac "\<Phi> (FIX \<Phi>) = FIX \<Phi>", clarsimp)
apply (erule Fix_lemma)
done
(*>*)

subsection\<open>Derivation of the HIGH rules\<close>

text\<open>The HIGH rules are easy.\<close>

lemma HIGH_SKIP: "G \<rhd> Skip : twiddle"
(*<*)
apply (rule VDMConseq, rule VDMSkip) 
apply (simp add: twiddle_def)
done
(*>*)

lemma HIGH_ASSIGN:
  "CONTEXT x = high \<Longrightarrow> G \<rhd> (Assign x e) : twiddle"
(*<*)
apply (rule VDMConseq, rule VDMAssign) 
apply (simp add: update_def twiddle_def)
done
(*>*)

lemma HIGH_COMP: 
  "\<lbrakk> G \<rhd> c1 : twiddle; G \<rhd> c2 : twiddle\<rbrakk> 
  \<Longrightarrow> G \<rhd> (Comp c1 c2): twiddle"
(*<*)
apply (rule VDMConseq, rule VDMComp) apply assumption+
apply (simp add: twiddle_def)
apply clarsimp
done
(*>*)

lemma HIGH_IFF:
  "\<lbrakk> G \<rhd> c1 : twiddle; G \<rhd> c2 : twiddle \<rbrakk> 
  \<Longrightarrow> G \<rhd> (Iff b c1 c2) : twiddle"
(*<*)
apply (rule VDMConseq, rule VDMIff) apply assumption+
apply (simp add: twiddle_def)
done
(*>*)

lemma HIGH_WHILE:
  "\<lbrakk> G \<rhd> c  : twiddle\<rbrakk> \<Longrightarrow> G \<rhd> (While b c)  : twiddle"
(*<*)
apply (rule VDMConseq)
  apply (rule VDMWhile) 
  apply (subgoal_tac "G \<rhd> c : (\<lambda>s t. evalB b s \<longrightarrow> s \<approx> t)", erule thin_rl, assumption)
  apply (erule VDMConseq) apply simp
  prefer 3 apply (subgoal_tac "\<forall>s t. s \<approx> t \<and> \<not> evalB b t \<longrightarrow> s \<approx> t", assumption) apply simp
  apply (simp add: twiddle_def)
  apply (simp add: twiddle_def)
done
(*>*)

lemma HIGH_CALL:
  "({twiddle} \<union> G) \<rhd> body : twiddle \<Longrightarrow> G \<rhd> Call : twiddle"
(*<*)
by (erule VDMCall)
(*>*)

subsection\<open>The type system of Volpano, Smith and Irvine\<close>

text\<open>We now give the type system of Volpano et al.~and then prove its
embedding into the system of derived rules. First, type systems for
expressions and boolean expressions.\<close>

inductive_set VS_expr :: "(Expr \<times> TP) set"
where
VS_exprVar: "CONTEXT x = t \<Longrightarrow> (varE x, t) : VS_expr"
| VS_exprVal: "(valE v, low) : VS_expr"
| VS_exprOp: "\<lbrakk>(e1,t) : VS_expr; (e2,t):VS_expr\<rbrakk>
             \<Longrightarrow> (opE f e1 e2,t) : VS_expr"
| VS_exprHigh: "(e, high) : VS_expr"

inductive_set VS_Bexpr :: "(BExpr \<times> TP) set"
where
VS_BexprOp: "\<lbrakk>(e1,t) : VS_expr; (e2,t):VS_expr\<rbrakk>
             \<Longrightarrow> (compB f e1 e2,t) : VS_Bexpr"
| VS_BexprHigh: "(e,high) : VS_Bexpr"

text\<open>Next, the core of the type system, the rules for commands.\<close>

inductive_set VS_com :: "(TP \<times> IMP) set"
where

VS_comSkip: "(pc,Skip) : VS_com"

| VS_comAssHigh:
  "CONTEXT x = high \<Longrightarrow> (pc,Assign x e) : VS_com"

| VS_comAssLow:
  "\<lbrakk>CONTEXT x = low; pc = low; (e,low):VS_expr\<rbrakk> \<Longrightarrow>
   (pc,Assign x e) : VS_com"

| VS_comComp:
  "\<lbrakk> (pc,c1):VS_com; (pc,c2):VS_com\<rbrakk> \<Longrightarrow>
   (pc,Comp c1 c2) : VS_com"

| VS_comIf:
  "\<lbrakk> (b,pc):VS_Bexpr; (pc,c1):VS_com; (pc,c2):VS_com\<rbrakk> \<Longrightarrow>
   (pc,Iff b c1 c2):VS_com"

| VS_comWhile:
  "\<lbrakk>(b,pc):VS_Bexpr; (pc,c):VS_com\<rbrakk> \<Longrightarrow> (pc,While b c):VS_com"

| VS_comSub: "(high,c) : VS_com \<Longrightarrow> (low,c):VS_com"

text\<open>We define the interpretation of expression typings\ldots\<close>

primrec SemExpr::"Expr \<Rightarrow> TP \<Rightarrow> bool"
where
"SemExpr e low = (\<forall> s ss. s \<approx> ss \<longrightarrow> evalE e s = evalE e ss)" |
"SemExpr e high = True"

text\<open>\ldots and show the soundness of the typing rules.\<close>

lemma ExprSound: "(e,tp):VS_expr \<Longrightarrow> SemExpr e tp"
(*<*)
apply (erule VS_expr.induct)
apply (case_tac t,simp_all)
  apply (simp add: twiddle_def)
apply (case_tac t, simp_all)
done
(*>*)

text\<open>Likewise for the boolean expressions.\<close>

primrec SemBExpr::"BExpr \<Rightarrow> TP \<Rightarrow> bool"
where
"SemBExpr b low = (\<forall> s ss. s \<approx> ss \<longrightarrow> evalB b s = evalB b ss)" |
"SemBExpr b high = True"

lemma BExprSound: "(e,tp):VS_Bexpr \<Longrightarrow> SemBExpr e tp"
(*<*)
apply (erule VS_Bexpr.induct, simp_all)
apply (drule ExprSound) 
apply (drule ExprSound) 
apply (case_tac t, simp_all) 
done
(*>*)

text\<open>The proof of the main theorem (called Theorem 2 in our paper)
proceeds by induction on $(t,c):VS\_com$.\<close>

theorem VS_com_VDM[rule_format]:
"(t,c):VS_com \<Longrightarrow> (t=high \<longrightarrow> G \<rhd> c : twiddle) \<and>
                  (t=low \<longrightarrow> (\<exists> A . G \<rhd> c : Sec A))"
(*<*)
apply (erule VS_com.induct)
apply rule
  apply clarsimp
  apply (rule HIGH_SKIP)
  apply clarsimp
  apply (rule, rule SKIP)
apply rule
  apply clarsimp
  apply (erule HIGH_ASSIGN)
  apply clarsimp
  apply (subgoal_tac "\<exists> t. (e,t):VS_expr", clarsimp) prefer 2 apply (rule, rule VS_exprHigh)
  apply (drule ExprSound)
  apply (case_tac t)
    apply clarsimp apply (rule, erule ASSIGN) 
    apply clarsimp apply (rule_tac x="\<lambda> (s,t).  s \<approx> t" in exI, rule VDMConseq) 
         apply (erule HIGH_ASSIGN) apply (simp add: Sec_def twiddle_def)
apply rule
  apply clarsimp
  apply (drule ExprSound)
    apply clarsimp apply (rule, erule ASSIGN) 
apply rule
  apply clarsimp
  apply (rule HIGH_COMP) apply (assumption, assumption)
  apply clarsimp
  apply (rule, rule COMP) apply (assumption, assumption)
apply rule
  apply clarsimp
  apply (rule HIGH_IFF) apply (assumption, assumption)
  apply clarsimp
  apply (drule BExprSound)
  apply clarsimp
  apply (rule, erule IFF)  apply (assumption, assumption)
apply rule
  apply clarsimp
  apply (erule HIGH_WHILE) 
  apply clarsimp
  apply (drule BExprSound)
  apply clarsimp
  apply (rule, erule WHILE) apply assumption
apply clarsimp
  apply (rule, erule CAST)
done
(*>*)

text\<open>The semantic of typing judgements for commands is now the
expected one: HIGH commands require initial and final state be low
equivalent (i.e.~the low variables in the final state can't depend on
the high variables of the initial state), while LOW commands must
respect the above mentioned security property.\<close>

primrec SemCom::"TP \<Rightarrow> IMP \<Rightarrow> bool"
where
"SemCom low c = (\<forall> s ss t tt. s \<approx> ss \<longrightarrow> (s,c \<Down> t) \<longrightarrow>
                               (ss,c \<Down> tt) \<longrightarrow> t \<approx> tt)" |
"SemCom high c = (\<forall> s t . (s,c \<Down> t) \<longrightarrow> s \<approx> t)"

text\<open>Combining theorem \<open>VS_com_VDM\<close> with the soundness result
of the program logic and the definition of validity yields the
soundness of Volpano et al.'s type system.\<close>

theorem VS_SOUND: "(t,c):VS_com \<Longrightarrow> SemCom t c"
(*<*)
apply (subgoal_tac "(t=high \<longrightarrow> {} \<rhd> c : twiddle) \<and> (t=low \<longrightarrow> (\<exists> A . {} \<rhd> c : Sec A))")
prefer 2 apply (erule VS_com_VDM)
apply (case_tac t)
apply clarsimp apply (drule VDM_Sound) apply (simp add: valid_def VDM_valid_def Ctxt_valid_def Sec_def)
apply clarsimp apply (drule VDM_Sound) apply (simp add: valid_def VDM_valid_def Ctxt_valid_def) 
done
(*>*)

text\<open>As a further minor result, we prove that all judgements
interpreting the low rules indeed yield assertions $A$ of the form $A
= Sec(\Phi(FIX \Phi))$ for some monotone $\Phi$.\<close>

inductive_set Deriv ::"(VDMAssn set \<times> IMP \<times> VDMAssn) set"
where
D_CAST: 
  "(G,c,twiddle):Deriv \<Longrightarrow> (G, c, Sec (\<lambda> (s,t) . s \<approx> t)) : Deriv"

| D_SKIP: "(G, Skip, Sec (\<lambda> (s,t) . s \<approx> t)) : Deriv"

| D_ASSIGN:
  "(\<forall> s ss. s \<approx> ss \<longrightarrow> evalE e s = evalE e ss) \<Longrightarrow>
   (G, Assign x e, Sec (\<lambda> (s, t) . s \<approx> (update t x (evalE e t)))):Deriv"

| D_COMP: 
  "\<lbrakk> (G, c1, Sec \<Phi>):Deriv; (G, c2, Sec \<Psi>):Deriv\<rbrakk> \<Longrightarrow>
   (G, Comp c1 c2, Sec (\<lambda> (s,t) . \<exists> r . \<Phi>(r, t) \<and> 
                           (\<forall> w . (r \<approx> w \<longrightarrow> \<Psi>(s, w))))):Deriv"

| C_IFF:
  "\<lbrakk> (\<forall> s ss. s \<approx> ss \<longrightarrow> evalB b s = evalB b ss);
     (G, c1, Sec \<Phi>):Deriv; (G,c2, Sec \<Psi>):Deriv\<rbrakk> \<Longrightarrow>
   (G, Iff b c1 c2, Sec (\<lambda> (s, t) . (evalB b t \<longrightarrow> \<Phi>(s,t)) \<and> 
                                            ((\<not> evalB b t) \<longrightarrow> \<Psi>(s,t)))):Deriv"

| D_WHILE:  
  "\<lbrakk> (\<forall> s ss. s \<approx> ss \<longrightarrow> evalB b s = evalB b ss); 
     (G, c, Sec \<Phi>):Deriv\<rbrakk> \<Longrightarrow>
   (G, While b c, Sec (PhiWhile b \<Phi>)):Deriv"

| D_CALL:
  "\<lbrakk> ({Sec(FIX \<Phi>)} \<union> G, body, Sec(\<Phi>(FIX \<Phi>))):Deriv;
      Monotone \<Phi>\<rbrakk> \<Longrightarrow>
   (G, Call, Sec(FIX \<Phi>)):Deriv"

| D_HighSKIP:"(G, Skip, twiddle):Deriv"

| D_HighASSIGN:
  "CONTEXT x = high \<Longrightarrow> (G,Assign x e, twiddle):Deriv"

| D_HighCOMP:
  "\<lbrakk> (G,c1,twiddle):Deriv; (G,c2,twiddle):Deriv\<rbrakk> \<Longrightarrow>
   (G, Comp c1 c2, twiddle):Deriv"

| D_HighIFF:
  "\<lbrakk> (G,c1,twiddle):Deriv; (G,c2,twiddle):Deriv\<rbrakk> \<Longrightarrow>
   (G, Iff b c1 c2, twiddle):Deriv"

| D_HighWHILE:
  "(G, c, twiddle):Deriv \<Longrightarrow> (G, While b c, twiddle):Deriv"

| D_HighCALL:
  "({twiddle} \<union> G, body, twiddle):Deriv \<Longrightarrow> (G, Call, twiddle):Deriv"

(*<*)
definition DProp :: "VDMAssn \<Rightarrow> bool"
where "DProp A = (\<exists> \<phi> . A =  Sec (\<phi> (FIX \<phi>)) \<and> Monotone \<phi>)"

lemma DerivProp_Aux: "(X,c,A):Deriv \<Longrightarrow> DProp A"
apply (erule Deriv.induct)
apply (simp_all add: DProp_def)
  apply clarsimp
  apply (rule, rule) apply simp apply (simp add: Monotone_def)
  apply clarsimp?
  apply (rule, rule) apply simp apply (simp add: Monotone_def)
  apply clarsimp?
  apply (rule, rule) apply simp apply (simp add: Monotone_def)
  apply clarsimp?
  apply (rule, rule) apply simp apply (simp add: Monotone_def)
  apply clarsimp?
  apply (rule, rule) apply simp apply (simp add: Monotone_def)
  apply clarsimp?
  apply (rule, rule) apply simp apply (simp add: Monotone_def)
  apply clarsimp ?
  apply (rule, rule) apply simp apply (simp add: Monotone_def)
  apply clarsimp?
    apply (rule_tac x="\<lambda> \<Phi>. \<lambda> (s,t) . s \<approx> t" in exI)
    apply (subgoal_tac "Monotone (\<lambda> \<Phi>. \<lambda> (s,t) . s \<approx> t)", simp) 
      apply (drule Fix_lemma) apply (erule thin_rl)
      apply (rule ext, rule ext, rule iffI)
      apply (simp add: twiddle_def Sec_def)
      apply (simp add: Sec_def) apply (simp only: twiddle_def) apply fast
    apply (simp add: Monotone_def)
  apply clarsimp?
    apply (rule_tac x="\<lambda> \<Phi>. \<lambda> (s,t) . s \<approx> t" in exI)
    apply (subgoal_tac "Monotone (\<lambda> \<Phi>. \<lambda> (s,t) . s \<approx> t)", simp) 
      apply (drule Fix_lemma) apply (erule thin_rl)
      apply (rule ext, rule ext, rule iffI)
      apply (simp add: twiddle_def Sec_def)
      apply (simp add: Sec_def) apply (simp only: twiddle_def) apply fast
    apply (simp add: Monotone_def)
done
(*>*)

lemma DerivMono: 
 "(X,c,A):Deriv \<Longrightarrow> \<exists> \<Phi> . A =  Sec (\<Phi> (FIX \<Phi>)) \<and> Monotone \<Phi>"
(*<*)
by (drule DerivProp_Aux, simp add: DProp_def)
(*>*)

text\<open>Also, all rules in the \<open>Deriv\<close> relation are indeed
derivable in the program logic.\<close>

lemma Deriv_derivable: "(G,c,A):Deriv \<Longrightarrow> G \<rhd> c: A"
(*<*)
apply (erule Deriv.induct)
apply (erule CAST)
apply (rule SKIP)
apply (erule ASSIGN)
apply (erule COMP) apply assumption
apply (erule IFF) apply assumption apply assumption
apply (erule WHILE) apply assumption 
apply (erule CALL) apply assumption
apply (rule HIGH_SKIP)
apply (erule HIGH_ASSIGN)
apply (erule HIGH_COMP) apply assumption
apply (erule HIGH_IFF) apply assumption 
apply (erule HIGH_WHILE) 
apply (erule HIGH_CALL) 
done
(*>*)
text\<open>End of theory VS\<close>
end 
