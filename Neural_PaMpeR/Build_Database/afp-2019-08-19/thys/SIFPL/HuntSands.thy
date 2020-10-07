(*File: HuntSands.thy*)
(*Authors: Lennart Beringer and Martin Hofmann, LMU Munich 2008*)
theory HuntSands imports VDM Lattice begin
section\<open>Flow-sensitivity a la Hunt and Sands\<close>

text\<open>\label{sec:HuntSands}\footnote{As the Isabelle theory representing this section is
dependent only on VDM.thy and Lattice.thy, name conflicts with
notions defined in Section \ref{sec:BaseLineNI} are avoided.} The
paper \cite{HuntSands:POPL2006} by Hunt and Sands presents a
generalisation of the type system of Volpano et al.~to
flow-sensitivity. Thus, programs such as $l:=h; l:=5$ are not rejected
any longer by the type system. Following the description in Section 4
of our paper~\cite{BeringerHofmann:CSF2007}, we embed Hunt and Sands'
type system into the program logic given in Section \ref{sec:VDM}.\<close>

subsection\<open>General $A; R \Rightarrow S$-security\<close>
text\<open>\label{sec:ARSsecurity}Again, we define the type $TT$ of
intermediate formulae $\Phi$, and an assertion operator
$\mathit{Sec}$. The latter is now parametrised not only by the
intermediate formulae but also by the (possibly differing) pre- and
post-relations $R$ and $S$ (both instantiated to $\approx$ in Section
\ref{sec:BaseLineNI}), and by a specification $A$ that directly links
pre- and post-states.\<close>

type_synonym TT = "(State \<times> State) \<Rightarrow> bool"

definition RSsecure::"(State \<Rightarrow> State \<Rightarrow> bool) \<Rightarrow>
                      (State \<Rightarrow> State \<Rightarrow> bool) \<Rightarrow> IMP \<Rightarrow> bool"
where "RSsecure R S c = (\<forall> s t ss tt . R s t \<longrightarrow> (s,c \<Down> ss) \<longrightarrow>
                          (t,c \<Down> tt) \<longrightarrow> S ss tt)"

definition ARSsecure::"VDMAssn \<Rightarrow> (State \<Rightarrow> State \<Rightarrow> bool) \<Rightarrow>
                      (State \<Rightarrow> State \<Rightarrow> bool) \<Rightarrow> IMP \<Rightarrow> bool"
where "ARSsecure A R S c = ((\<Turnstile> c : A) \<and> RSsecure R S c)"

text\<open>Definition 3 of our paper follows.\<close>

definition Sec :: "VDMAssn \<Rightarrow> (State \<Rightarrow> State \<Rightarrow> bool) \<Rightarrow>
                  (State \<Rightarrow> State \<Rightarrow> bool) \<Rightarrow> TT \<Rightarrow> VDMAssn"
where "Sec A R S \<Phi> s t = (A s t \<and>
                   (\<forall> r . R s r \<longrightarrow> \<Phi>(t,r)) \<and> (\<forall> r . \<Phi>(r,s) \<longrightarrow> S r t))"

text\<open>With these definitions, we can prove Proposition 4 of our
paper.\<close>

lemma Prop4A: "\<Turnstile> c : Sec A R S \<Phi> \<Longrightarrow> ARSsecure A R S c"
(*<*)
by (simp add:  VDM_valid_def Sec_def ARSsecure_def RSsecure_def)
(*>*)

lemma Prop4B : "ARSsecure A R S c \<Longrightarrow>
   \<Turnstile> c : Sec A R S (\<lambda> (r,t) . \<exists> s . (s , c \<Down> r) \<and> R s t)"
(*<*)
apply (simp add: VDM_valid_def Sec_def) 
apply clarsimp
apply (unfold ARSsecure_def RSsecure_def VDM_valid_def)
apply rule apply fastforce
apply rule
apply (rule, rule) apply (rule_tac x=s in exI, rule, assumption+) 
apply (rule, rule, erule exE, erule conjE) apply fast
done
(*>*)

subsection\<open>Basic definitions\<close>

text\<open>Contexts map program variables to lattice elements.\<close>

type_synonym "CONTEXT" = "Var \<Rightarrow> L"

definition upd ::"CONTEXT \<Rightarrow> Var \<Rightarrow> L \<Rightarrow> CONTEXT"
where "upd G x p = (\<lambda> y . if x=y then p else G y)"

text\<open>We also define the predicate $\mathit{EQ}$ 
%(in our paper denoted by the symbol $\ltimes$) 
which expresses when two states agree on all
variables whose entry in a given context is below a certain security
level.\<close>

definition EQ:: "CONTEXT \<Rightarrow> L \<Rightarrow> State \<Rightarrow> State \<Rightarrow> bool"
where "EQ G p = (\<lambda> s t . \<forall> x . LEQ (G x) p \<longrightarrow>  s x = t x)"

lemma EQ_LEQ: "\<lbrakk>EQ G p s t; LEQ pp p\<rbrakk> \<Longrightarrow> EQ G pp s t"
(*<*)
apply (simp add: EQ_def, clarsimp)
apply (erule_tac x=x in allE, erule mp)
apply (erule LAT2, assumption)
done 
(*>*)

text\<open>The assertion called $\mathcal{Q}$ in our paper:\<close>

definition Q::"L \<Rightarrow> CONTEXT \<Rightarrow> VDMAssn"
where "Q p H = (\<lambda> s t . \<forall> x . (\<not> LEQ p (H x)) \<longrightarrow> t x = s x)"

text\<open>$Q$ expresses the preservation of values in a single execution,
and corresponds to the first clause of Definition 3.2 in
\cite{HuntSands:POPL2006}. In accordance with this, the following
definition of security instantiates the $A$ position of $A; R
\Rightarrow S$-security with $Q$, while the context-dependent binary
state relations are plugged in as the $R$ and $S$ components.\<close>

definition secure :: "L \<Rightarrow> CONTEXT \<Rightarrow> IMP \<Rightarrow> CONTEXT \<Rightarrow> bool"
where "secure p G c H = (\<forall> q . ARSsecure (Q p H) (EQ G q) (EQ H q) c)"

text\<open>Indeed, one may show that this notion of security amounds to the
conjunction of a unary (i.e.~one-execution-)property and a binary
(i.e.~two-execution-) property, as expressed in Hunt \& Sands'
Definition 3.2.\<close>

definition secure1 :: "L \<Rightarrow> CONTEXT \<Rightarrow> IMP \<Rightarrow> CONTEXT \<Rightarrow> bool"
where "secure1 p G c H = (\<forall> s t . (s,c \<Down> t) \<longrightarrow> Q p H s t)"

definition secure2 :: "L \<Rightarrow> CONTEXT \<Rightarrow> IMP \<Rightarrow> CONTEXT \<Rightarrow> bool"
where "secure2 p G c H = ((\<forall> s t ss tt . (s,c \<Down> t) \<longrightarrow> (ss,c \<Down> tt) \<longrightarrow>
                                    EQ G p s ss \<longrightarrow> EQ H p t tt))"

lemma secureEQUIV: 
  "secure p G c H = (\<forall> q . secure1 p G c H \<and> secure2 q G c H)"
(*<*)by (simp add: secure1_def secure2_def secure_def ARSsecure_def
              RSsecure_def Q_def VDM_valid_def, auto)
(*>*)

subsection\<open>Type system\<close>

text\<open>The type system of Hunt and Sands -- our language formalisation
uses a concrete datatype of expressions, so we add the obvious typing
rules for expressions and prove the expected evaluation lemmas.\<close>

inductive_set HS_E:: "(CONTEXT \<times> Expr \<times> L) set"
where 
HS_E_var: "(G, varE x, G x) : HS_E"
| HS_E_val: "(G, valE c, bottom) : HS_E"
| HS_E_op: "\<lbrakk>(G, e1,p1):HS_E; (G, e2,p2):HS_E; p= LUB p1 p2\<rbrakk>
           \<Longrightarrow> (G,opE f e1 e2,p) : HS_E"
| HS_E_sup: "\<lbrakk>(G,e,p):HS_E; LEQ p q\<rbrakk> \<Longrightarrow> (G,e,q):HS_E"

lemma HS_E_eval[rule_format]:
"(G, e, t) \<in> HS_E \<Longrightarrow> 
 \<forall> r s q. EQ G q r s \<longrightarrow> LEQ t q \<longrightarrow> evalE e r = evalE e s"
(*<*)
apply (erule HS_E.induct)
apply clarsimp  apply (simp add: EQ_def)
apply clarsimp
apply clarsimp
  apply (erule_tac x=r in allE, erule_tac x=r in allE)
  apply (erule_tac x=s in allE, erule_tac x=s in allE)
  apply (erule_tac x=q in allE, erule_tac x=q in allE, clarsimp)
  apply (erule impE) apply (rule LAT2) prefer 2 apply assumption
    apply (simp add: LAT3)
  apply (erule impE) apply (rule LAT2) prefer 2 apply assumption
    apply (subgoal_tac "LEQ p2 (LUB p2 p1)")
      apply (simp add: LAT4)
    apply (simp add: LAT3)
  apply clarsimp
apply clarsimp
  apply (erule_tac x=r in allE, erule_tac x=s in allE, erule_tac x=qa in allE, erule impE)
    apply clarsimp
  apply (erule mp) apply (erule LAT2, assumption)
done
(*>*)

text\<open>Likewise for boolean expressions:\<close>

inductive_set HS_B:: "(CONTEXT \<times> BExpr \<times> L) set"
where
HS_B_compB: "\<lbrakk>(G, e1,p1):HS_E; (G, e2,p2):HS_E; p= LUB p1 p2\<rbrakk>
             \<Longrightarrow> (G,compB f e1 e2,p) : HS_B"
| HS_B_sup: "\<lbrakk>(G,b,p):HS_B; LEQ p q\<rbrakk> \<Longrightarrow> (G,b,q):HS_B"

lemma HS_B_eval[rule_format]:
"(G, b, t) \<in> HS_B \<Longrightarrow>
 \<forall> r s pp . EQ G pp r s \<longrightarrow> LEQ t pp \<longrightarrow>  evalB b r = evalB b s"
(*<*)
apply (erule HS_B.induct)
apply clarsimp
  apply (subgoal_tac "evalE e1 r = evalE e1 s", clarsimp) 
  prefer 2 apply (erule HS_E_eval) apply assumption 
           apply (rule LAT2) prefer 2 apply assumption apply (simp add: LAT3)
  apply (subgoal_tac "evalE e2 r = evalE e2 s", clarsimp) 
    apply (erule HS_E_eval) apply assumption
           apply (rule LAT2) prefer 2 apply assumption 
           apply (subgoal_tac "LEQ p2 (LUB p2 p1)", simp add: LAT4)
           apply (simp add: LAT3)
apply clarsimp
  apply (erule_tac x=r in allE, erule_tac x=s in allE, erule_tac x=pp in allE, erule impE)
    apply clarsimp
  apply (erule mp) apply (erule LAT2, assumption)
done
(*>*)

text\<open>The typing rules for commands follow.\<close>

inductive_set HS::"(L \<times> CONTEXT \<times> IMP \<times> CONTEXT) set"
where
HS_Skip:   "(p,G,Skip,G):HS"

| HS_Assign:
  "(G,e,t):HS_E \<Longrightarrow> (p,G,Assign x e,upd G x (LUB p t)):HS"

| HS_Seq:
  "\<lbrakk>(p,G,c,K):HS; (p,K,d,H):HS\<rbrakk> \<Longrightarrow> (p,G, Comp c d,H):HS"

| HS_If:
  "\<lbrakk>(G,b,t):HS_B; (LUB p t,G,c,H):HS; (LUB p t,G,d,H):HS\<rbrakk> \<Longrightarrow>
   (p,G,Iff b c d,H):HS"

| HS_If_alg:
  "\<lbrakk>(G,b,p):HS_B; (p,G,c,H):HS; (p,G,d,H):HS\<rbrakk> \<Longrightarrow>
   (p,G,Iff b c d,H):HS"

| HS_While:
  "\<lbrakk>(G,b,t):HS_B; (LUB p t,G,c,H):HS;H=G\<rbrakk> \<Longrightarrow>
   (p,G,While b c,H):HS"

| HS_Sub:
  "\<lbrakk> (pp,GG,c,HH):HS; LEQ p pp; \<forall> x . LEQ (G x) (GG x); 
       \<forall> x . LEQ (HH x) (H x)\<rbrakk> \<Longrightarrow>
   (p,G,c,H):HS"

text \<open>Using \<open>HS_Sub\<close>, rules \<open>If\<close> and \<open>If_alg\<close> are
inter-derivable.\<close>

lemma IF_derivable_from_If_alg:
  "\<lbrakk>(G,b,t):HS_B; (LUB p t,G,c1,H):HS; (LUB p t,G,c2,H):HS\<rbrakk>
   \<Longrightarrow> (p,G,Iff b c1 c2,H):HS"
apply (subgoal_tac "(LUB p t,G,Iff b c1 c2,H):HS")
  apply (erule HS_Sub) apply (rule LAT3)
    apply (clarsimp, rule LAT6) apply (clarsimp, rule LAT6) 
apply (rule HS_If_alg) apply (erule HS_B_sup) 
  apply (subgoal_tac "LEQ t (LUB t p)", simp add: LAT4) 
  apply (rule LAT3) apply assumption+
done

lemma IF_alg_derivable_from_If:
  "\<lbrakk>(G,b,p):HS_B; (p,G,c1,H):HS; (p,G,c2,H):HS\<rbrakk> 
  \<Longrightarrow> (p,G,Iff b c1 c2,H):HS"
apply (erule HS_If) apply (subgoal_tac "LUB p p = p", clarsimp) 
  apply (subgoal_tac "p = LUB p p", fastforce) apply (rule LAT7)
apply (subgoal_tac "LUB p p = p", clarsimp) 
  apply (subgoal_tac "p = LUB p p", fastforce) apply (rule LAT7)
done

text\<open>An easy induction on typing derivations shows the following property.\<close>

lemma HS_Aux1: 
 "(p,G,c,H):HS \<Longrightarrow> \<forall> x. LEQ (G x) (H x) \<or> LEQ p (H x)"
(*<*)
apply (erule HS.induct)
(*Skip*)
apply (simp add: LAT6)
(*Assign*)
apply (simp add: upd_def) apply clarsimp apply rule
  apply clarsimp apply (simp add: LAT3)
  apply clarsimp apply (simp add: LAT6)
(*Seq*)
apply clarsimp
   apply (erule_tac x=x in allE, erule disjE)
   apply (erule_tac x=x in allE, erule disjE)
     apply (erule LAT2) apply assumption apply fast
   apply (erule_tac x=x in allE, erule disjE)
     apply(subgoal_tac "LEQ p (H x)", fast)
     apply (erule LAT2) apply assumption apply fast
(*If*)
apply clarsimp
   apply (erule_tac x=x in allE, erule disjE) apply assumption
     apply(subgoal_tac "LEQ p (H x)", fast)
     apply (subgoal_tac "LEQ p (LUB p t)", rotate_tac -1)
     apply (erule LAT2) apply assumption 
     apply (rule LAT3)
(*If2*)
apply clarsimp
(*While*)
apply clarsimp
   apply (simp add: LAT6)
(*Sub*)
apply clarsimp
   apply (erule_tac x=x in allE, erule disjE) 
   apply (erule_tac x=x in allE) 
   apply (erule_tac x=x in allE)
     apply (erule LAT2)
     apply (erule LAT2) apply assumption
   apply (erule_tac x=x in allE)
     apply (erule LAT2)
   apply (erule_tac x=x in allE)
     apply (subgoal_tac "LEQ p (H x)", fast)
     apply (erule LAT2)
     apply (erule LAT2) apply assumption
done
(*>*)

subsection\<open>Derived proof rules\<close>

text\<open>In order to show the derivability of the properties given in
Theorem 3.3 of Hunt and Sands' paper, we give the following derived
proof rules. By including the $Q$ property in the $A$ position of
$Sec$, we prove both parts of theorem in one proof, and can exploit
the first property ($Q$) in the proof of the second.\<close>

lemma SKIP:
 "X \<rhd> Skip : Sec (Q p H) (EQ G q) (EQ G q) 
                  (\<lambda> (s,t) . EQ G q s t)"
(*<*)
apply (rule VDMConseq, rule VDMSkip)
  apply (simp add: Sec_def EQ_def Q_def)
done
(*>*)

lemma ASSIGN: 
  "\<lbrakk>H = upd G x (LUB p t); 
    \<forall> s ss . EQ G t s ss \<longrightarrow> evalE e s = evalE e ss\<rbrakk>
  \<Longrightarrow> X \<rhd> Assign x e : Sec (Q p H) (EQ G q) (EQ H q) 
            (\<lambda> (s,t) . \<exists> r . s = update r x (evalE e r) \<and> EQ G q r t)"
(*<*)
  apply (rule VDMConseq, rule VDMAssign) apply clarsimp
  apply (simp add: Sec_def EQ_def Q_def)
  apply (rule, clarsimp) apply (simp add: update_def upd_def)
    apply (case_tac "x=xa", clarsimp) apply (simp add: LAT3)
    apply clarsimp
  apply (rule, clarsimp) apply (rule_tac x=s in exI, simp)
  apply clarsimp
    apply (case_tac "x=xa", clarsimp, hypsubst_thin)
      apply (simp add: update_def upd_def)
        apply (erule_tac x=ra in allE, erule_tac x=s in allE, erule mp, clarsimp)
        apply (erule_tac x=x in allE, erule mp)
        apply (erule LAT2, rule LAT2) prefer 2 apply assumption
        apply (subgoal_tac "LEQ t (LUB t p)", simp add: LAT4)  apply (rule LAT3)
      apply (simp add: update_def upd_def) 
done
(*>*)

lemma COMP: 
  "\<lbrakk> X \<rhd> c1 : Sec (Q p K) (EQ G q) (EQ K q) \<Phi>;
     X \<rhd> c2 : Sec (Q p H) (EQ K q) (EQ H q) \<Psi>;
    \<forall> x . LEQ (G x) (K x) \<or> LEQ p (K x);
    \<forall> x . LEQ (K x) (H x) \<or> LEQ p (H x)\<rbrakk> 
   \<Longrightarrow> X \<rhd> Comp c1 c2 : Sec (Q p H) (EQ G q) (EQ H q)
        (\<lambda> (x, y) . \<exists> z . \<Phi> (z, y) \<and> 
                          (\<forall> w . EQ K q z w \<longrightarrow> \<Psi> (x, w)))"
(*<*)
  apply (rule VDMConseq, rule VDMComp, assumption, assumption, clarsimp)
    apply (erule thin_rl, erule thin_rl)
  apply (simp add: Sec_def, rule, clarsimp)
    apply (simp add: Q_def, clarsimp)
    apply (rotate_tac 3, erule_tac x=x in allE, erule impE, assumption)
    apply (erule_tac x=x in allE, clarsimp)
    apply (erule_tac x=x in allE, clarsimp)
    apply (subgoal_tac "LEQ p (H x)", fast)
    apply (erule LAT2) apply assumption
  apply (rule, clarsimp)
    apply (rule_tac x=r in exI, simp) 
  apply clarsimp
done
(*>*)

text\<open>We distinguish, for any given $q$, \emph{parallel} conditionals
from \emph{diagonal} ones. Speaking operationally (i.e.~in terms of
two executions), conditionals of the former kind evaluate the branch
condition identically in both executions. The following rule
expresses this condition explicitly, in the first side condition. The
formula inside the $\mathit{Sec}$-operator of the conclusion resembles
the conclusion of the VDM rule for conditionals in that the formula
chosen depends on the outcome of the branch.\<close>

lemma IF_PARALLEL:
  "\<lbrakk> \<forall> s ss . EQ G p s ss \<longrightarrow> evalB b s = evalB b ss;
     \<forall> x. LEQ (G x) (H x) \<or> LEQ p (H x);
     \<exists> x . LEQ p (H x) \<and> LEQ (H x) q;
     X \<rhd> c1 : Sec (Q p H) (EQ G q) (EQ H q) \<Phi>;
     X \<rhd> c2 : Sec (Q p H) (EQ G q) (EQ H q) \<Psi>\<rbrakk>
  \<Longrightarrow> X \<rhd> Iff b c1 c2 : Sec (Q p H) (EQ G q) (EQ H q) 
                       (\<lambda> (r, u) . (evalB b u \<longrightarrow> \<Phi> (r, u)) \<and>
                                   ( (\<not> evalB b u) \<longrightarrow> \<Psi> (r, u)))"
(*<*)
    apply (rule VDMConseq, rule VDMIff) apply (assumption, assumption) apply clarsimp
    apply (simp add: Sec_def Q_def)
    apply (subgoal_tac "(\<forall>x. \<not> LEQ p (H x) \<longrightarrow> t x = s x)", simp)
    prefer 2 apply (case_tac "evalB b s", clarsimp,clarsimp) 
    apply (rule, clarsimp)
    (*left component of Sec*)
      apply (subgoal_tac "evalB b s = evalB b r")
      prefer 2 apply (erule_tac x=s in allE, rotate_tac -1, erule_tac x=r in allE, erule mp)
        apply (erule EQ_LEQ) apply (erule LAT2, assumption)
      apply (case_tac "evalB b s")
              apply clarsimp 
              apply clarsimp 
    (*right component of Sec*)
      apply clarsimp
      apply (case_tac "evalB b s")
        apply clarsimp  
        apply clarsimp 
done
(*>*)

text\<open>An alternative formulation replaces the first side condition
with a typing hypothesis on the branch condition, thus exploiting
lemma HS\_B\_eval.\<close>

lemma IF_PARALLEL_tp:
  "\<lbrakk> (G, b, p) \<in> HS_B; (p , G, c1, H) \<in> HS; (p, G, c2, H) \<in> HS;
     \<exists> x . LEQ p (H x) \<and> LEQ (H x) q;
     X \<rhd> c1 : Sec (Q p H) (EQ G q) (EQ H q) \<Phi>;
     X \<rhd> c2 : Sec (Q p H) (EQ G q) (EQ H q) \<Psi>\<rbrakk>
  \<Longrightarrow> X \<rhd> Iff b c1 c2 : Sec (Q p H) (EQ G q) (EQ H q) 
                       (\<lambda> (r, u) . (evalB b u \<longrightarrow> \<Phi> (r, u)) \<and>
                                   ( (\<not> evalB b u) \<longrightarrow> \<Psi> (r, u)))"
(*<*)
  apply (rule IF_PARALLEL)
    apply (clarsimp, erule HS_B_eval) apply assumption apply (rule LAT6)
    apply (erule HS_Aux1)
    apply assumption+
done
(*>*)

text\<open>Diagonal conditionals, in contrast, capture cases where (from
the perspective of an observer at level $q$) the two executions may
evaluate the branch condition differently. In this case, the formula
inside the $\mathit{Sec}$-operator in the conclusion cannot depend
upon the branch outcome, so the least common denominator of the two
branches must be taken, which is given by the equality condition
w.r.t.~the post-context $H$. A side condition (the first one given in
the rule) ensures that indeed no information leaks during the
execution of either branch, by relating $G$ and $H$.\<close>

lemma IF_DIAGONAL:
  "\<lbrakk> \<forall>x. LEQ (G x) (H x) \<or> LEQ p (H x);
      \<not> (\<exists>x. LEQ p (H x) \<and> LEQ (H x) q);
      X \<rhd> c1 : Sec (Q p H) (EQ G q) (EQ H q) \<Phi>;
      X \<rhd> c2 : Sec (Q p H) (EQ G q) (EQ H q) \<Psi>\<rbrakk>
   \<Longrightarrow> X \<rhd> Iff b c1 c2 : Sec (Q p H) (EQ G q) (EQ H q)
                             (\<lambda> (s,t). EQ H q s t)"
(*<*)
  apply clarsimp
  apply (rule VDMConseq, rule VDMIff) apply (assumption, assumption) apply clarsimp
  apply (simp add: Sec_def Q_def)
  apply (subgoal_tac "(\<forall>x. \<not> LEQ p (H x) \<longrightarrow> t x = s x)", simp)
  prefer 2 apply (case_tac "evalB b s")
           apply clarsimp
           apply clarsimp
  apply (rule, clarsimp)
  (*Left component*)
    apply (simp (no_asm) add: EQ_def, clarsimp)
    apply (case_tac "LEQ p (H x)") apply clarsimp
    apply (rotate_tac -4, erule_tac x=x in allE, clarsimp)
    apply (simp add: EQ_def)
    apply (erule_tac x=x in allE, erule mp)
    apply (rotate_tac -4, erule_tac x=x in allE, clarsimp)
    apply (erule LAT2, assumption)
  (*right component*)
    apply clarsimp
    apply (simp add: EQ_def, clarsimp)
    apply (case_tac "LEQ p (H x)")
    apply clarsimp
    apply clarsimp
done
(*>*)

text\<open>Again, the first side condition of the rule may be replaced by a
typing condition, but now this condition is on the commands (instead
of the branch condition) -- in fact, a derivation for either branch
suffices.\<close>

lemma IF_DIAGONAL_tp:
  "\<lbrakk> (p, G, c1, H) \<in> HS \<or> (p, G, c2, H) \<in> HS; 
      \<not> (\<exists>x. LEQ p (H x) \<and> LEQ (H x) q);
      X \<rhd> c1 : Sec (Q p H) (EQ G q) (EQ H q) \<Phi>;
      X \<rhd> c2 : Sec (Q p H) (EQ G q) (EQ H q) \<Psi>\<rbrakk>
   \<Longrightarrow> X \<rhd> Iff b c1 c2 : Sec (Q p H) (EQ G q) (EQ H q)
                             (\<lambda> (s,t). EQ H q s t)"
(*<*)
  apply (rule IF_DIAGONAL)
    apply (erule disjE) apply (erule HS_Aux1) apply (erule HS_Aux1)
    apply assumption+
done
(*>*)

text\<open>Obviously, given $q$, any conditional is either parallel or
diagonal as the second side conditions of the diagonal rules and the
parallel rules are exclusive.\<close>

lemma if_algorithmic:
  "\<lbrakk>\<exists> x . LEQ p (H x) \<and> LEQ (H x) q; 
    \<not> (\<exists>x. LEQ p (H x) \<and> LEQ (H x) q)\<rbrakk>
   \<Longrightarrow> False"
(*<*) by simp (*>*)


text\<open>As in Section \ref{sec:BaseLineNI} we define a fixed point
construction, useful for the (parallel) while rule.\<close>

definition FIX::"(TT \<Rightarrow> TT) \<Rightarrow> TT"
where "FIX \<phi> = (\<lambda> (s,t). \<forall> \<Phi> . (\<forall> ss tt . \<phi> \<Phi> (ss, tt) \<longrightarrow> \<Phi> (ss, tt))
                            \<longrightarrow> \<Phi> (s, t))"

text\<open>For monotone invariant transformers, the construction indeed
yields a fixed point.\<close>

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
  apply (erule_tac x="FIX \<phi>" in allE, erule_tac x=\<Phi> in allE)
  apply (erule impE) apply assumption
  apply (simp add: FIX_def)
done

lemma Fix1: "\<lbrakk>Monotone \<phi>; FIX \<phi> (s,t)\<rbrakk> \<Longrightarrow> \<phi> (FIX \<phi>) (s,t)"
apply (simp add: FIX_def) 
apply (erule_tac x="\<phi>(FIX \<phi>)" in allE) 
apply (erule impE)
prefer 2 apply (simp add: FIX_def)
apply (subgoal_tac "\<forall> r u . \<phi> (FIX \<phi>) (r,u) \<longrightarrow> FIX \<phi> (r,u)")
  prefer 2 apply clarsimp apply (erule Fix2) apply assumption
apply (unfold Monotone_def)
  apply (erule_tac x="\<phi>(FIX \<phi>)" in allE, erule_tac x="FIX \<phi>" in allE, erule impE) apply assumption
apply simp
done
(*>*)
lemma Fix_lemma:"Monotone \<phi> \<Longrightarrow> \<phi> (FIX \<phi>) = FIX \<phi>"
(*<*)
apply (rule ext, rule iffI)
apply clarsimp apply (erule Fix2) apply assumption
apply clarsimp apply (erule Fix1) apply assumption
done
(*>*)

text\<open>Next, the definition of a while-operator.\<close>

definition PhiWhilePOp::
          "VDMAssn \<Rightarrow> BExpr \<Rightarrow> TT \<Rightarrow> TT \<Rightarrow> TT"
where "PhiWhilePOp A b \<Phi> =
  (\<lambda> \<Psi> . (\<lambda>(r, u). (evalB b u \<longrightarrow> (\<exists>z. \<Phi> (z, u) \<and> 
                                        (\<forall>w. A z w \<longrightarrow> \<Psi> (r, w)))) \<and> 
                     ((\<not> evalB b u) \<longrightarrow> A r u)))"

text\<open>This operator is monotone in $\Phi$.\<close>

lemma PhiWhilePOp_Monotone:"Monotone (PhiWhilePOp A b \<Phi>)"
(*<*)
apply (simp add: PhiWhilePOp_def Monotone_def) apply clarsimp
  apply (rule_tac x=z in exI, simp)
done
(*>*)

text\<open>Therefore, we can define the following fixed point.\<close>

definition PhiWhileP::"VDMAssn \<Rightarrow> BExpr \<Rightarrow> TT \<Rightarrow> TT"
where "PhiWhileP A b \<Phi> = FIX (PhiWhilePOp A b \<Phi>)"

text\<open>As as a function on $\phi$, this PhiWhileP is itself monotone
in $\phi$:\<close>

lemma PhiWhilePMonotone: "Monotone (\<lambda> \<Phi> . PhiWhileP A b \<Phi>)"
(*<*)
apply (simp add: Monotone_def) apply clarsimp
apply (simp add: PhiWhileP_def)
apply (simp add: FIX_def) apply clarsimp
apply (erule_tac x=\<Phi>' in allE, erule mp)
apply (clarsimp) apply (erule_tac x=ss in allE, erule_tac x=tt in allE, erule mp)
apply (simp add: PhiWhilePOp_def) apply clarsimp
apply (rule_tac x=z in exI, simp)
done
(*>*)

text\<open>Now the rule for parallel while loops, i.e.~loops where the
branch condition evaluates identically in both executions.\<close>

lemma WHILE_PARALLEL:
 "\<lbrakk> X \<rhd> c : Sec (Q p G) (EQ G q) (EQ G q) \<Phi>; 
    \<forall> s ss . EQ G p s ss \<longrightarrow> evalB b s = evalB b ss; LEQ p q\<rbrakk>
 \<Longrightarrow> X \<rhd> While b c : Sec (Q p G) (EQ G q) (EQ G q)
                         (PhiWhileP (EQ G q) b \<Phi>)"
(*<*)
apply (rule VDMConseq)
apply (rule VDMWhile)
prefer 4 apply (subgoal_tac "\<forall>s t. Sec (Q p G) (EQ G q) (EQ G q) (PhiWhilePOp (EQ G q) b \<Phi> (PhiWhileP (EQ G q) b \<Phi>)) s t \<and> \<not> evalB b t \<longrightarrow> Sec (Q p G) (EQ G q) (EQ G q) (PhiWhileP (EQ G q) b \<Phi>) s t") apply assumption
  apply clarsimp apply (subgoal_tac "PhiWhilePOp (EQ G q) b \<Phi> (PhiWhileP (EQ G q) b \<Phi>) = PhiWhileP (EQ G q) b \<Phi>", clarsimp)
                 apply (simp add: PhiWhileP_def) apply (rule Fix_lemma) apply (rule PhiWhilePOp_Monotone)
apply assumption
apply clarsimp apply (simp add: Sec_def) 
  apply rule apply (simp add: Q_def)
  apply (rule, clarsimp) apply (simp add: PhiWhilePOp_def) apply clarsimp
      apply (erule_tac x=s in allE, erule_tac x=r in allE, erule impE) apply (erule EQ_LEQ) apply assumption apply clarsimp
  apply clarsimp apply (simp add: PhiWhilePOp_def)
apply clarsimp apply (simp add: Sec_def)
  apply rule apply clarsimp apply (simp add: Q_def)
  apply rule
  prefer 2 apply clarsimp
    apply (subgoal_tac "\<exists>r. \<Phi> (r, s) \<and> (\<forall>w. EQ G q r w \<longrightarrow> (PhiWhileP (EQ G q) b \<Phi>) (ra, w))")
    prefer 2 apply (simp add: PhiWhilePOp_def) 
    apply clarsimp apply (rotate_tac -3, erule thin_rl)
    apply (rotate_tac -1, erule_tac x=ra in allE, erule mp)
    apply (rotate_tac 1, erule_tac x=r in allE, erule impE) apply fast
    apply (subgoal_tac "PhiWhilePOp (EQ G q) b \<Phi> (PhiWhileP (EQ G q) b \<Phi>) = PhiWhileP (EQ G q) b \<Phi>", clarsimp)
    apply (simp add: PhiWhileP_def)
    apply (rule Fix_lemma) apply (rule PhiWhilePOp_Monotone)
  apply clarsimp
    apply (simp (no_asm_simp) add: PhiWhilePOp_def) 
    apply rule
    prefer 2  apply clarsimp
              apply (erule_tac x=s in allE, rotate_tac -1, erule_tac x=ra in allE, erule impE)
               apply (erule EQ_LEQ) apply assumption apply clarsimp 
    apply clarsimp
    apply (rotate_tac 2, erule_tac x=ra in allE, clarsimp)
    apply (rule_tac x=r in exI, rule) apply simp
    apply clarsimp
    apply (rotate_tac 5, erule_tac x=w in allE, clarsimp)
    apply (subgoal_tac "PhiWhilePOp (EQ G q) b \<Phi> (PhiWhileP (EQ G q) b \<Phi>) = PhiWhileP (EQ G q) b \<Phi>", clarsimp)
    apply (simp add: PhiWhileP_def)
    apply (rule Fix_lemma) apply (rule PhiWhilePOp_Monotone)
done
(*>*)

text\<open>The side condition regarding the evalution of the branch
condsition may be replaced by a typing hypothesis, thanks to lemma
\<open>HS_B_eval\<close>.\<close>

lemma WHILE_PARALLEL_tp:
 "\<lbrakk> X \<rhd> c : Sec (Q p G) (EQ G q) (EQ G q) \<Phi>; 
    (G, b, p) \<in> HS_B; LEQ p q\<rbrakk>
 \<Longrightarrow> X \<rhd> While b c : Sec (Q p G) (EQ G q) (EQ G q)
                         (PhiWhileP (EQ G q) b \<Phi>)"
(*<*)
apply (erule WHILE_PARALLEL)
apply clarsimp 
  apply (erule HS_B_eval) apply assumption apply (rule LAT6)
apply assumption
done
(*>*)

text\<open>One may also give an inductive formulation of FIX:\<close>

inductive_set var::"(BExpr \<times> VDMAssn \<times> TT \<times> State \<times> State) set"
where
varFalse:
   "\<lbrakk>\<not> evalB b t; A s t\<rbrakk> \<Longrightarrow> (b,A,\<Phi>,s,t):var"
| varTrue:
   "\<lbrakk>evalB b t; \<Phi>(r,t); (\<forall> w . A r w \<longrightarrow>
    (b,A,\<Phi>,s,w): var) \<rbrakk> \<Longrightarrow> (b,A,\<Phi>,s,t):var"

(*<*)
lemma varFIX: "(b,A,\<Phi>,s,t):var \<Longrightarrow> PhiWhileP A b \<Phi> (s,t)"
apply (erule var.induct)
apply (simp add: PhiWhileP_def)
  apply (subgoal_tac "PhiWhilePOp A b \<Phi> (FIX (PhiWhilePOp A b \<Phi>)) (s,t)")
  apply (subgoal_tac "PhiWhilePOp A b \<Phi> (FIX (PhiWhilePOp A b \<Phi>)) = FIX (PhiWhilePOp A b \<Phi>)", clarsimp)
  apply (rule Fix_lemma) apply (rule PhiWhilePOp_Monotone)
  apply (simp add: PhiWhilePOp_def)
apply (simp (no_asm_simp) add: PhiWhileP_def)
apply (subgoal_tac "PhiWhilePOp A b \<Phi> (FIX (PhiWhilePOp A b \<Phi>)) (s,t)")
  apply (subgoal_tac "PhiWhilePOp A b \<Phi> (FIX (PhiWhilePOp A b \<Phi>)) = FIX (PhiWhilePOp A b \<Phi>)", clarsimp)
  apply (rule Fix_lemma) apply (rule PhiWhilePOp_Monotone)
  apply (simp add: PhiWhilePOp_def)
  apply (rule_tac x=r in exI, simp)
  apply clarsimp
  apply (erule_tac x=w in allE, clarsimp)
  apply (simp add: PhiWhileP_def)
  apply (simp add: PhiWhilePOp_def)
done

lemma FIXvar: "PhiWhileP A b \<Phi> (s,t) \<Longrightarrow> (b,A,\<Phi>,s,t):var"
apply (simp add: PhiWhileP_def)
apply (subgoal_tac "PhiWhilePOp A b \<Phi> (FIX (PhiWhilePOp A b \<Phi>)) (s, t)")
prefer 2 
  apply (subgoal_tac "PhiWhilePOp A b \<Phi> (FIX (PhiWhilePOp A b \<Phi>)) = FIX (PhiWhilePOp A b \<Phi>)", clarsimp)
  apply (rule Fix_lemma) apply (rule PhiWhilePOp_Monotone)
apply (erule thin_rl, simp add: PhiWhilePOp_def) apply clarsimp
  apply (case_tac "evalB b t")
  prefer 2 apply clarsimp apply (rule varFalse) apply assumption+
  apply clarsimp apply (rule varTrue) apply assumption apply assumption 
    apply clarsimp apply (erule_tac x=w in allE, clarsimp)
    apply (unfold FIX_def) apply clarify
    apply (erule_tac x="\<lambda> (x,y) . (b,A,\<Phi>,x,y):var" in allE, erule impE) prefer 2 apply simp
    apply clarsimp
    apply (case_tac "evalB b tt")
    prefer 2 apply clarsimp apply (rule varFalse) apply assumption+
    apply clarsimp apply (rule varTrue) apply assumption+
done
(*>*)

text\<open>The inductive formulation and the fixed point formulation are
equivalent.\<close>
(*<*)
lemma varFIXvar: "(PhiWhileP A b \<Phi> (s,t)) = ((b,A,\<Phi>,s,t):var)"
apply rule
apply (erule FIXvar)
apply (erule varFIX)
done
(*>*)
(*<*)
lemma FIXvarFIX': "(PhiWhileP A b \<Phi>) = (\<lambda> (s,t) . (b,A,\<Phi>,s,t):var)"
apply (rule ext, rule iffI)
apply (case_tac x, clarsimp) apply (erule FIXvar)
apply (case_tac x, clarsimp) apply (simp add: varFIXvar)
done
(*>*)
lemma FIXvarFIX: 
"PhiWhileP A b = (\<lambda> \<Phi> . (\<lambda> (s,t) . (b,A,\<Phi>,s,t):var))"
(*<*)
by (rule, rule FIXvarFIX')
(*>*)

text\<open>Thus, the above while rule may also be written using the
inductive formulation.\<close>

lemma WHILE_PARALLEL_IND:
 "\<lbrakk> X \<rhd> c : Sec (Q p G) (EQ G q) (EQ G q) \<Phi>; 
    \<forall> s ss . EQ G p s ss \<longrightarrow> evalB b s = evalB b ss; LEQ p q\<rbrakk> \<Longrightarrow>
   X \<rhd> While b c : (Sec (Q p G) (EQ G q) (EQ G q)
                    (\<lambda> (s,t) . (b,EQ G q,\<Phi>,s,t):var))"
(*<*)
apply (rule VDMConseq)
apply (rule WHILE_PARALLEL) apply assumption+
apply clarsimp
apply (simp add: FIXvarFIX)
done
(*>*)

text\<open>Again, we may replace the side condition regarding the branch
condition by a typing hypothesis.\<close>

lemma WHILE_PARALLEL_IND_tp:
 "\<lbrakk> X \<rhd> c : Sec (Q p G) (EQ G q) (EQ G q) \<Phi>;
    (G, b, p) \<in> HS_B; LEQ p q \<rbrakk> \<Longrightarrow> 
 X \<rhd> (While b c) : 
  (Sec (Q p G) (EQ G q) (EQ G q) (\<lambda> (s,t) . (b,EQ G q,\<Phi>,s,t):var))"
(*<*)
apply (erule WHILE_PARALLEL_IND)
apply clarsimp 
  apply (erule HS_B_eval) apply assumption apply (rule LAT6)
apply assumption
done
(*>*)
(*<*)
lemma varMonotoneAux[rule_format]:
 "(b, A, \<Phi>, s, t) \<in> var \<Longrightarrow> 
  (\<forall>s t. \<Phi> (s, t) \<longrightarrow> \<Psi> (s, t)) \<longrightarrow>
  (b, A, \<Psi>, s, t) \<in> var"
apply (erule var.induct)
apply clarsimp apply (erule varFalse, simp)
apply clarsimp apply (erule varTrue) apply fast apply simp
done
(*>*)
text\<open>Of course, the inductive formulation is also monotone:\<close>

lemma var_MonotoneInPhi:
  "Monotone (\<lambda> \<Phi> . (\<lambda> (s,t) .(b,A, \<Phi>,s,t):var))"
(*<*)
apply (simp add: Monotone_def)
apply clarsimp
apply (rule varMonotoneAux) apply assumption apply simp
done
(*>*)
(*<*)
lemma varMonotone_byFIX: "Monotone (\<lambda> \<Phi> . (\<lambda> (s,t) .(b,A, \<Phi>,s,t):var))"
apply (subgoal_tac "Monotone (\<lambda> \<Phi> . PhiWhileP A b \<Phi>)")
apply (simp add: FIXvarFIX)
apply (rule PhiWhilePMonotone)
done  
(*>*)

text\<open>In order to derive a diagonal while rule, we directly define an
inductive relation that calculates the transitive closure of relation
$A$, such that all but the last state evaluate $b$ to
$\mathit{True}$.\<close>

inductive_set varD::"(BExpr \<times> VDMAssn \<times> State \<times> State) set"
where
varDFalse: "\<lbrakk>\<not> evalB b s; A s t\<rbrakk> \<Longrightarrow> (b,A,s,t):varD"
| varDTrue: "\<lbrakk>evalB b s; A s w; (b,A,w,t): varD \<rbrakk> \<Longrightarrow> (b,A,s,t):varD"

text\<open>Here is the obvious definition of transitivity for assertions.\<close>

definition transitive::"VDMAssn \<Rightarrow> bool"
where "transitive P = (\<forall> x y z . P x y \<longrightarrow> P y z \<longrightarrow> P x z)"

text\<open>The inductive relation satisfies the following property.\<close>

lemma varD_transitive[rule_format]: 
 "(b,A,s,t):varD \<Longrightarrow> transitive A \<longrightarrow> A s t"
(*<*)
apply (erule varD.induct)
apply clarsimp
apply clarsimp 
  apply (unfold transitive_def) apply (erule_tac x=s in allE, erule_tac x=w in allE, erule_tac x=t in allE, simp)
done
(*>*)

text\<open>On the other hand, the assertion $\mathit{Q}$ defined above is transitive,\<close>

lemma Q_transitive:"transitive (Q q G)"
(*<*)
by (simp add: Q_def transitive_def) 
(*>*)

text\<open>and is hence respected by the inductive closure:\<close> 

lemma varDQ:"(b,Q q G,s,t):varD \<Longrightarrow> Q q G s t"
(*<*)by (erule varD_transitive,rule Q_transitive)(*>*)

text\<open>The diagonal while rule has a conclusion that is independent of
$\phi$.\<close>

lemma WHILE_DIAGONAL:
 "\<lbrakk>X \<rhd> c : Sec (Q p G) (EQ G q) (EQ G q) \<Phi>; \<not> LEQ p q\<rbrakk>
       \<Longrightarrow> X \<rhd> While b c : Sec (Q p G) (EQ G q) (EQ G q)
                               (\<lambda> (s,t). EQ G q s t)"
(*<*)
apply (subgoal_tac "\<forall>x. LEQ p (G x) \<longrightarrow> \<not> LEQ (G x) q")
prefer 2 apply (case_tac "\<forall>x. LEQ p (G x) \<longrightarrow> \<not> LEQ (G x) q", assumption) apply clarsimp
  apply (subgoal_tac "LEQ p q", fast)
  apply (erule LAT2, assumption)
apply (rule VDMConseq)
apply (insert VDMWhile)
  apply (erule VDMWhile [of X c "Sec (Q p G) (EQ G q) (EQ G q) \<Phi>" b "(\<lambda> s t . (b,Q p G,s,t):varD)"])
    apply clarsimp apply (erule varDFalse) apply (simp add: Q_def) 
    apply clarsimp apply (simp add: Sec_def) apply clarsimp
      apply (rule varDTrue) apply assumption prefer 2 apply assumption 
        apply (erule_tac x=s in allE, erule impE, simp add: EQ_def) apply assumption 
apply clarsimp 
apply (simp add: Sec_def)
apply rule apply (erule varDQ) 
apply (rule, clarsimp) 
  apply (drule varDQ)  apply (simp add: Q_def EQ_def, clarsimp) 
  apply (case_tac "LEQ p (G x)") prefer 2 apply simp 
  apply (rotate_tac -1, drule LAT2) apply assumption apply fast 
apply (drule varDQ)  apply (simp add: Q_def EQ_def, clarsimp) 
  apply (case_tac "LEQ p (G x)") prefer 2 apply simp 
  apply (rotate_tac -1, drule LAT2) apply assumption apply fast 
done
(*>*)

text\<open>$\mathit{varD}$ is monotone in the assertion position.\<close>

lemma varDMonotoneInAssertion[rule_format]:
  "(b, A, s, t) \<in> varD \<Longrightarrow> 
   (\<forall>s t. A s t \<longrightarrow> B s t) \<longrightarrow> (b, B, s, t) \<in> varD"
(*<*)
apply (erule varD.induct) 
apply clarsimp apply (erule varDFalse) apply simp
apply clarsimp apply (erule varDTrue) prefer 2 apply assumption apply simp
done
(*>*)

(*<*)
text\<open>As $\mathit{varD}$ does not depend on $\Phi$, the monotonicity
property in this position is trivially fulfilled.\<close>

lemma varDMonotoneInPhi[rule_format]:
  "\<lbrakk>(b, A, s, t) \<in> varD; \<forall>s t. \<Phi>(s, t) \<longrightarrow> \<Psi>(s, t)\<rbrakk> 
  \<Longrightarrow> (b, A, s, t) \<in> varD"
by simp
(*>*)

text\<open>Finally, the subsumption rule.\<close>

lemma SUB:
  "\<lbrakk> LEQ p pp; \<forall>x. LEQ (G x) (GG x); \<forall>x. LEQ (HH x) (H x);
     X \<rhd> c : Sec (Q pp HH) (EQ GG q) (EQ HH q) \<Phi>\<rbrakk>
   \<Longrightarrow> X \<rhd> c : Sec (Q p H) (EQ G q) (EQ H q) \<Phi>"
(*<*)
apply (erule VDMConseq)
  apply (simp add: Sec_def EQ_def, clarsimp)
  apply (rule, simp add: Q_def, clarsimp)
    apply (erule_tac x=x in allE, erule mp, clarsimp)
    apply (subgoal_tac "LEQ p (H x)", fast)
    apply (rotate_tac 2, erule_tac x=x in allE)
    apply (erule LAT2)
    apply (erule LAT2, assumption)
  apply (rule, clarsimp)
    apply (erule_tac x=r in allE, erule mp, clarsimp)
    apply (erule_tac x=x in allE, erule mp)
    apply (erule_tac x=x in allE, erule LAT2,assumption) 
  apply clarsimp
    apply (erule_tac x=r in allE, erule impE, assumption)
    apply (erule_tac x=x in allE, erule mp)
    apply (erule_tac x=x in allE, erule LAT2, assumption) 
done
(*>*)

subsection\<open>Soundness results\<close>

(*<*)
definition Theorem3derivProp::"VDMAssn set \<Rightarrow> L \<Rightarrow> CONTEXT \<Rightarrow> IMP \<Rightarrow> CONTEXT \<Rightarrow> L \<Rightarrow> bool"
where "Theorem3derivProp X p G c H q = (\<exists> \<Phi> . X \<rhd> c : (Sec (Q p H) (EQ G q) (EQ H q) \<Phi>))"

lemma Theorem3_derivAux[rule_format]: 
"(p,G,c,H):HS \<Longrightarrow> Theorem3derivProp X p G c H q"
apply (erule HS.induct)
apply (simp_all add: Theorem3derivProp_def)
(*Skip*)
  apply (rule, rule SKIP) 
(*Assign*)
  apply (rule, rule ASSIGN[simplified]) apply simp 
  apply (clarsimp, erule HS_E_eval) apply assumption apply (rule LAT6)
(*COMP*)
apply clarsimp
  apply (rule, rule COMP) apply (assumption, assumption) apply (erule HS_Aux1) 
  apply (erule HS_Aux1)
(*IFF*) 
  apply clarsimp
  apply (subgoal_tac "(G, b, LUB p t) \<in> HS_B", erule thin_rl)
  prefer 2 apply (erule HS_B_sup) apply (subgoal_tac "LEQ t (LUB t p)", simp add: LAT4) apply (rule LAT3)
  apply (subgoal_tac "\<exists> psi. X \<rhd> Iff b c d : Sec (Q (LUB p t) H) (EQ G q) (EQ H q) psi", clarsimp)
  apply (rule_tac x=psi in exI, erule VDMConseq, clarsimp)
    apply (simp add: Sec_def, clarsimp)
    apply (simp add: Q_def, clarsimp)
    apply (erule_tac x=x in allE, erule mp, clarsimp)
    apply (subgoal_tac "LEQ p (LUB p t)")
    prefer 2 apply (rule LAT3)
    apply (rotate_tac -1, drule LAT2) apply assumption apply simp
  apply (case_tac "\<exists> x . LEQ (LUB p t) (H x) \<and> LEQ (H x) q")
    apply (rule, erule IF_PARALLEL_tp) apply assumption+
    apply (rule, rule IF_DIAGONAL) apply (erule HS_Aux1) apply assumption+
(*If2*)
  apply clarsimp
  apply (case_tac "\<exists> x . LEQ p (H x) \<and> LEQ (H x) q")
    apply (rule, erule IF_PARALLEL_tp) apply assumption+
    apply (rule, rule IF_DIAGONAL) apply (erule HS_Aux1) apply assumption+
(*While*)
  apply clarsimp
  apply (subgoal_tac "(G, b, LUB p t) \<in> HS_B", erule thin_rl)
  prefer 2 apply (erule HS_B_sup) apply (subgoal_tac "LEQ t (LUB t p)", simp add: LAT4) apply (rule LAT3)
  apply (subgoal_tac "\<exists> psi. X \<rhd> While b c : Sec (Q (LUB p t) G) (EQ G q) (EQ G q) psi", clarsimp)
  apply (rule_tac x=psi in exI, erule VDMConseq, clarsimp)
    apply (simp add: Sec_def, clarsimp)
    apply (simp add: Q_def, clarsimp)
    apply (erule_tac x=x in allE, erule mp, clarsimp)
    apply (subgoal_tac "LEQ p (LUB p t)")
    prefer 2 apply (rule LAT3)
    apply (rotate_tac -1, drule LAT2) apply assumption apply simp
  apply (case_tac "LEQ (LUB p t) q")
    apply (rule, rule WHILE_PARALLEL) apply assumption
      apply clarsimp apply (erule HS_B_eval)  apply assumption apply (rule LAT6) apply assumption
  (*OTHER CASE*)
  apply (rule, erule WHILE_DIAGONAL) apply assumption
(*Sub*)
  apply clarsimp
  apply (rule, erule SUB, assumption+)
done
(*>*)

text\<open>An induction on the typing rules now proves the main theorem
which was called Theorem 4 in~\cite{BeringerHofmann:CSF2007}.\<close>

theorem Theorem4[rule_format]: 
  "(p,G,c,H):HS \<Longrightarrow> 
  (\<exists> \<Phi> . X \<rhd> c : (Sec (Q p H) (EQ G q) (EQ H q) \<Phi>))"
(*<*)
by (drule Theorem3_derivAux, simp add: Theorem3derivProp_def)
(*>*)

text\<open>By the construction of the operator $\mathit{Sec}$ (lemmas
\<open>Prop4A\<close> and \<open>Prop4A\<close> in Section \ref{sec:ARSsecurity}) we
obtain the soundness property with respect to the oprational
semantics, i.e.~the result stated as Theorem 3.3 in
\cite{HuntSands:POPL2006}.\<close>

theorem HuntSands33: "(p,G,c,H):HS \<Longrightarrow> secure p G c H"
(*<*)
apply (simp add: secure_def, clarsimp)
apply (drule Theorem4, clarsimp) 
apply (rule Prop4A)
apply (rule VDM_Sound_emptyCtxt)  apply fast
done
(*>*)

text \<open>Both parts of this theorem may also be shown
individually. We factor both proofs by the program logic.\<close>

lemma Sec1_deriv: "(p,G,c,H):HS \<Longrightarrow> X \<rhd> c : (Q p H)"
(*<*)
apply (drule Theorem4, clarsimp)
apply (erule VDMConseq)
apply (simp add: Sec_def) apply clarsimp
done
(*>*)

(*<*)
lemma 
 "(p,G,c,H):HS \<Longrightarrow> 
  X \<rhd> c : (\<lambda> s t . \<forall> x . \<not> LEQ p (H x) \<longrightarrow> s x = t x)"
apply (drule Sec1_deriv) apply (erule VDMConseq) apply (simp add: Q_def)
done
(*>*)

theorem HuntSands33_1:"(p,G,c,H):HS \<Longrightarrow> secure1 p G c H"
(*<*)
apply (subgoal_tac "{} \<rhd> c : Q p H")
apply (drule VDM_Sound) 
  apply (simp add: Q_def secure1_def valid_def VDM_valid_def Ctxt_valid_def)
apply (erule Sec1_deriv)
done(*>*)

lemma Sec2_deriv: 
  "(p,G,c,H):HS \<Longrightarrow> 
  (\<exists> A . X \<rhd> c : (Sec (Q p H) (EQ G q) (EQ H q) A))"
(*<*)
by (drule Theorem4 [of p G c H "X" q], clarsimp)
(*>*)

(*<*)
lemma Sec2:
  "(p,G,c,H):HS \<Longrightarrow> 
   (\<exists> \<Phi> . \<Turnstile> c : (Sec (Q p H) (EQ G q) (EQ H q) \<Phi>))"
apply (drule Theorem4 [of p G c H "{}" q], clarsimp)
apply (rule_tac x=\<Phi> in exI, erule VDM_Sound_emptyCtxt)
done
(*>*)

theorem HuntSands33_2: "(p,G,c,H):HS \<Longrightarrow> secure2 q G c H"
(*<*)
apply (subgoal_tac "\<forall> q . ARSsecure (Q p H) (EQ G q) (EQ H q) c")
prefer 2 apply clarsimp
         apply (drule Sec2_deriv[of p G c H "{}"], erule exE)
         apply (rule Prop4A) apply (erule VDM_Sound_emptyCtxt)
apply (insert secureEQUIV [of p G c H]) apply (simp add: secure_def)
done
(*>*)

text\<open>Again, the call rule is formulated for an arbitrary fixed point
of a monotone transformer.\<close>

lemma CALL: 
  "\<lbrakk> ({B} \<union> X) \<rhd> body : Sec A R S (\<phi>(FIX \<phi>));
      Monotone \<phi>; B = Sec A R S (FIX \<phi>) \<rbrakk>
   \<Longrightarrow> X \<rhd> Call : B"
(*<*)
apply (rule VDMCall)
apply (subgoal_tac "\<phi> (FIX \<phi>) = FIX \<phi>", clarsimp)
apply (erule Fix_lemma)
done
(*>*)

(*<*)
text\<open>Monotonicity lemmas for the operators occurring in the derived proof rules.\<close>
lemma SkipMonotone:"Monotone (\<lambda> T (s,t). EQ G p s t)"
by (simp add: Monotone_def)

lemma AssignMonotone:"Monotone (\<lambda> T (s,t). \<exists>r. s = update r x (evalE e r) \<and> EQ G p r t)"
by (simp add: Monotone_def)

lemma CompMonotone: "Monotone (\<lambda> T (s,t). \<exists> r. A r t \<and> (\<forall>w. EQ K q r w \<longrightarrow> B s w))"
by (simp add: Monotone_def)

lemma IfPMonotone1: "Monotone (\<lambda> T (s,t). (evalB b t \<longrightarrow> T(s,t)) \<and> (\<not> evalB b t \<longrightarrow> B (s,t)))"
by (simp add: Monotone_def)

lemma IfPMonotone2: "Monotone (\<lambda> T (s,t). (evalB b t \<longrightarrow> A(s,t)) \<and> (\<not> evalB b t \<longrightarrow> T (s,t)))"
by (simp add: Monotone_def)

lemma IfDMonotone:"Monotone (\<lambda> T (s,t). EQ G p s t)"
by (simp add: Monotone_def)


lemma WhileDMonotone: "Monotone (\<lambda> T (s,t). EQ G q s t)"
by (simp add: Monotone_def)

lemma SubMonotone: "Monotone (\<lambda>T. T)"
by (simp add: Monotone_def)
(*>*)

text\<open>As in Section \ref{sec:BaseLineNI}, we define a formal derivation system
comprising all derived rules and show that all derivable judgements
are of the for $\mathit{Sec}(\Phi)$ for some monotone $\Phi$.\<close>

inductive_set Deriv:: "(VDMAssn set \<times> IMP \<times> VDMAssn) set"
where
D_SKIP: 
  "\<Omega> = (\<lambda> (s,t). EQ G q s t)
 \<Longrightarrow> (X, Skip, Sec (Q p H) (EQ G q) (EQ G q) \<Omega>) : Deriv"

| D_ASSIGN: 
  "\<lbrakk>H = upd G x (LUB p t); 
    \<forall> s ss . EQ G t s ss \<longrightarrow> evalE e s = evalE e ss;
    \<Omega> = (\<lambda> (s, t) . \<exists> r . s = update r x (evalE e r) \<and> EQ G q r t)\<rbrakk> 
\<Longrightarrow> (X, Assign x e, Sec (Q p H) (EQ G q) (EQ H q) \<Omega>) : Deriv"

| D_COMP: 
  "\<lbrakk> (X, c, Sec (Q p K) (EQ G q) (EQ K q) \<Phi>) : Deriv;
     (X, d, Sec (Q p H) (EQ K q) (EQ H q) \<Psi>) : Deriv;
    \<forall> x . LEQ (G x) (K x) \<or> LEQ p (K x);
    \<forall> x . LEQ (K x) (H x) \<or> LEQ p (H x);
    \<Omega> = (\<lambda> (x, y) . \<exists> z . \<Phi>(z,y) \<and> (\<forall> w . EQ K q z w \<longrightarrow> \<Psi>(x,w)))\<rbrakk> 
 \<Longrightarrow> (X, Comp c d, Sec (Q p H) (EQ G q) (EQ H q) \<Omega>) : Deriv"

| D_IF_PARALLEL:
  "\<lbrakk> \<forall> s ss . EQ G p s ss \<longrightarrow> evalB b s = evalB b ss;
     \<forall> x. LEQ (G x) (H x) \<or> LEQ p (H x);
     \<exists> x . LEQ p (H x) \<and> LEQ (H x) q;
     (X, c, Sec (Q p H) (EQ G q) (EQ H q) \<Phi>) : Deriv;
     (X, d, Sec (Q p H) (EQ G q) (EQ H q) \<Psi>) : Deriv;
     \<Omega> = (\<lambda> (r, u) . (evalB b u \<longrightarrow> \<Phi>(r,u)) \<and> 
                      ( (\<not> evalB b u) \<longrightarrow> \<Psi>(r,u)))\<rbrakk>
  \<Longrightarrow> (X, Iff b c d, Sec (Q p H) (EQ G q) (EQ H q) \<Omega>) : Deriv"

| D_IF_DIAGONAL:
  "\<lbrakk> \<forall>x. LEQ (G x) (H x) \<or> LEQ p (H x);
     \<not> (\<exists>x. LEQ p (H x) \<and> LEQ (H x) q);
     (X, c, Sec (Q p H) (EQ G q) (EQ H q) \<Phi>) : Deriv;
     (X, d, Sec (Q p H) (EQ G q) (EQ H q) \<Psi>) : Deriv;
     \<Omega> = (\<lambda> (s,t) . EQ H q s t)\<rbrakk>
   \<Longrightarrow> (X, Iff b c d, Sec (Q p H) (EQ G q) (EQ H q) \<Omega>) : Deriv"

| D_WHILE_PARALLEL:
 "\<lbrakk> (X, c, Sec (Q p G) (EQ G q) (EQ G q) \<Phi>):Deriv; 
    \<forall> s ss . EQ G p s ss \<longrightarrow> evalB b s = evalB b ss; LEQ p q;
    \<Omega> = (\<lambda> (s,t) . (b,EQ G q,\<Phi>,s,t):var)\<rbrakk>
   \<Longrightarrow> (X, While b c, Sec (Q p G) (EQ G q) (EQ G q) \<Omega>):Deriv"

| D_WHILE_DIAGONAL:
 "\<lbrakk>(X, c, Sec (Q p G) (EQ G q) (EQ G q) \<Phi>) : Deriv; \<not> LEQ p q;
   \<Omega> = (\<lambda> (s,t) . EQ G q s t)\<rbrakk>
 \<Longrightarrow> (X, While b c, Sec (Q p G) (EQ G q) (EQ G q) \<Omega>) : Deriv"

| D_SUB:
  "\<lbrakk> LEQ p pp; \<forall>x. LEQ (G x) (GG x); \<forall>x. LEQ (HH x) (H x);
     (X, c, Sec (Q pp HH) (EQ GG q) (EQ HH q) \<Phi>) : Deriv\<rbrakk>
   \<Longrightarrow> (X, c, Sec (Q p H) (EQ G q) (EQ H q) \<Phi>) :Deriv"

| D_CALL:
  "({A} \<union> X,body,A): Deriv \<Longrightarrow> (X,Call,A) : Deriv"

(*<*)
definition DProp :: "VDMAssn \<Rightarrow> bool"
where "DProp B = (\<exists> A R S \<phi> . B =  Sec A R S (\<phi> (FIX \<phi>)) \<and> Monotone \<phi>)"

lemma DerivProp_Aux: "(X,c,A):Deriv \<Longrightarrow> DProp A"
apply (erule Deriv.induct)
apply (simp_all add: DProp_def)
apply (rule_tac x="Q p H" in exI,
       rule_tac x="EQ G q" in exI,
       rule_tac x="EQ G q" in exI)
       apply rule apply rule 
       apply simp
       apply (simp add: Monotone_def)
apply (rule_tac x="(Q p (upd G x (LUB p t)))" in exI,
       rule_tac x="EQ G q" in exI,
       rule_tac x="(EQ (upd G x (LUB p t)) q)" in exI)
       apply rule apply rule
       apply simp
       apply (simp add: Monotone_def)
apply clarsimp
apply (rule_tac x="Q p H" in exI,
       rule_tac x="EQ G q" in exI,
       rule_tac x="EQ H q" in exI)
       apply rule apply rule
       apply simp
       apply (simp add: Monotone_def)
apply clarsimp 
apply (rule_tac x="Q p H" in exI,
       rule_tac x="EQ G q" in exI,
       rule_tac x="EQ H q" in exI)
       apply rule apply rule apply simp 
       apply (simp add: Monotone_def)
apply clarsimp
apply (rule_tac x="Q p H" in exI,
       rule_tac x="EQ G q" in exI,
       rule_tac x="EQ H q" in exI)
       apply rule apply rule
       apply simp
       apply (simp add: Monotone_def)
apply clarsimp
apply (rule_tac x="Q p G" in exI,
       rule_tac x="EQ G q" in exI,
       rule_tac x="EQ G q" in exI)
       apply rule apply rule 
       apply simp
       apply (simp add: Monotone_def)
apply clarsimp
apply (rule_tac x="Q p G" in exI,
       rule_tac x="EQ G q" in exI,
       rule_tac x="EQ G q" in exI)
       apply rule apply rule 
       apply simp
       apply (simp add: Monotone_def)
apply clarsimp
apply (rule_tac x="Q p H" in exI,
       rule_tac x="EQ G q" in exI,
       rule_tac x="EQ H q" in exI)
       apply rule apply rule apply simp
       apply (simp add: Monotone_def)
done
(*>*)

lemma DerivMono: 
 "(X,c,B):Deriv \<Longrightarrow>
  \<exists> A R S \<phi> . B =  Sec A R S (\<phi> (FIX \<phi>)) \<and> Monotone \<phi>"
(*<*)
by (drule DerivProp_Aux, simp add: DProp_def)
(*>*)

text\<open>Also, the \<open>Deriv\<close> is indeed a subsystem of the program
logic.\<close>

theorem Deriv_derivable: "(X,c,A):Deriv \<Longrightarrow> X \<rhd> c :A"
(*<*)
apply (erule Deriv.induct)
apply clarify apply (rule SKIP)
apply clarify apply (rule_tac t=t in ASSIGN) apply simp apply assumption
apply clarify apply (rule COMP) apply assumption apply assumption apply assumption apply assumption
apply clarify apply (rule IF_PARALLEL) apply assumption apply assumption apply (rule_tac x=x in exI, simp) apply assumption apply assumption 
apply clarify apply (rule IF_DIAGONAL) apply assumption apply assumption apply assumption apply assumption 
apply clarify apply (rule WHILE_PARALLEL_IND) apply assumption apply assumption apply assumption 
apply clarify apply (rule WHILE_DIAGONAL) apply assumption apply assumption 
apply (rule SUB) apply assumption apply assumption apply assumption apply assumption 
apply (frule DerivMono) apply (erule exE)+ apply clarsimp
  apply (subgoal_tac "X \<rhd> Call : Sec Aa R S (FIX \<phi>)")
  prefer 2 apply (rule CALL)
    prefer 2 apply assumption
    apply (simp add: Fix_lemma)
    apply simp
  apply (simp add: Fix_lemma)
done
(*>*)
text\<open>End of theory HuntSands\<close>
end
