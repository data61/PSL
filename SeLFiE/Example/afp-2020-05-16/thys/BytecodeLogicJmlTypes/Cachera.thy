(*File: Cachera.thy
  Author: L Beringer & M Hofmann, LMU Munich
  Date: 05/12/2008
  Purpose: Strong interpretation of, and derived proof system for,
           heap analysis a la Cachera/Jensen/Pichardie/Schneider,
           using invariants.
*)
(*<*)
theory Cachera imports Logic begin
(*>*)

section\<open>A derived logic for a strong type system\<close>

text\<open>In this section we consider a system of derived assertions, for
a type system for bounded heap consumption. The type system arises by
reformulating the analysis of Cachera, Jensen, Pichardie, and
Schneider \cite{CaJePiSc05MemoryUsage} for a high-level functional
language. The original approach of Cachera et al.~consists of
formalising the correctness proof of a certain analysis technique in
Coq. Consequently, the verification of a program requires the
execution of the analysis algorithm inside the theorem prover, which
involves the computation of the (method) call graph and fixed point
iterations.  In contrast, our approach follows the proof-carrying code
paradigm more closely: the analysis amounts to a type inference which
is left unformalised and can thus be carried out outside the trusted
code base. Only the result of the analysis is communicated to the code
recipient.  The recipient verifies the validity of the certificate by
a largely syntax-directed single-pass traversal of the (low-level)
code using a domain-specific program logic. This approach to
proof-carrying code was already explored in the MRG project, with
respect to program logics of partial correctness
\cite{BeringerHofmannMomiglianoShkaravska:LPAR2004} and a type system
for memory consumption by Hofmann and
Jost~\cite{HofmannJost:POPL2003}. In order to obtain
syntax-directedness of the proof rules, these had to be formulated at
the granularity of typing judgements. In contrast, the present proof
system admits proof rules for individual JVM instructions.

Having derived proof rules for individual JVM instructions, we
introduce a type system for a small functional language, and a
compilation into bytecode.  The type system associates a natural
number $n$ to an expression $e$, in a typing context
$\Sigma$. Informally, the interpretation of a typing judgement
$\Sigma \rhd e:n$ is that the evaluation of $e$ (which may include
the invocation of functions whose resource behaviour is specified in
$\Sigma$) does not perform more than $n$ allocations. The type system
is then formally proven sound, using the derived logic for bytecode.
By virtue of the invariants, the guarantee given by the present system
is stronger than the one given by our encoding of the Hofmann-Jost
system, as even non-terminating programs can be verified in a
meaningful way.\<close>

subsection\<open>Syntax and semantics of judgements\<close>

text\<open>The formal interpretation at JVM level of a type \<open>n\<close> is
given by a triple $$\mathit{Cachera}(n) = (A, B, I)$$ consisting of a
(trivial) precondition, a post-condition, and a strong invariant.\<close>

definition Cachera::"nat \<Rightarrow> (Assn \<times> Post \<times> Inv)" where
"Cachera n = (\<lambda> s0 s . True,
              \<lambda> s0 (ops,s,h) (k,v) . |k| \<le> |h| + n,
              \<lambda> s0 (ops,s,h) k.  |k| \<le> |h| + n)"

text\<open>This definition is motivated by the expectation that $\rhd
\lbrace A \rbrace\; \ulcorner\, e \urcorner\, \lbrace B \rbrace\, I$
should be derivable whenever the type judgement $\Sigma \rhd e:n$
holds, where $ \ulcorner e \urcorner$ is the translation of compiling
the expression $e$ into JVML, and the specification table \<open>MST\<close>
contains the interpretations of the entries in $\Sigma$.\<close>

text\<open>We abbreviate the above construction of judgements by a
predicate \<open>deriv\<close>.\<close>

definition deriv::"CTXT \<Rightarrow> Class \<Rightarrow> Method \<Rightarrow> Label \<Rightarrow> 
                    (Assn \<times> Post \<times> Inv) \<Rightarrow> bool" where
"deriv G C m l (ABI) = (let (A,B,I) = ABI in (G \<rhd> \<lbrace> A \<rbrace> C,m,l \<lbrace> B \<rbrace> I))"

text\<open>Thus, the intended interpretation of a typing judgement $\Sigma
\rhd e: n$ is $$\mathit{deriv}\; C\; m\; l\; (\mathit{Cachera}\; n)$$
if $e$ translates to a code block whose first instruction is at
$C.m.l$.\<close>

text\<open>We also define a judgement of the auxiliary form of
sequents.\<close>

definition derivAssum::"CTXT \<Rightarrow> Class \<Rightarrow> Method \<Rightarrow> Label \<Rightarrow> 
                         (Assn \<times> Post \<times> Inv) \<Rightarrow> bool" where
"derivAssum G C m l (ABI) = (let (A,B,I) = ABI in G \<rhd>  \<langle> A \<rangle> C,m,l \<langle> B \<rangle> I)"

text\<open>The following operation converts a derived judgement into the
syntactical form of method specifications.\<close>

definition mkSPEC::"(Assn \<times> Post \<times> Inv) \<Rightarrow> ANNO \<Rightarrow>
                   (MethSpec \<times> MethInv \<times> ANNO)" where
"mkSPEC (ABI) Anno = (let (A,B,I) = ABI in
       (\<lambda> s0 t . B s0 (mkState s0) t, \<lambda> s0 h . I s0 (mkState s0) h, Anno))"

text\<open>This enables the interpretation of typing contexts $\Sigma$ as a
set of constraints on the specification table \<open>MST\<close>.\<close>

subsection\<open>Derived proof rules\<close>
(*<*)
declare Let_def[simp]
(*>*)
text\<open>We are now ready to prove derived rules, i.e.~proof rules where
assumptions as well as conclusions are of the restricted assertion
form. While their justification unfolds the definition of the
predicate \<open>deriv\<close>, their application will not. We first give
syntax-directed proof rules for all JVM instructions:\<close>

lemma CACH_NEW:
 "\<lbrakk> ins_is C m l (new c); MST\<down>(C,m)=Some(Mspec,Minv,Anno);
    Anno\<down>(l) = None; n = k + 1; derivAssum G C m (l+1) (Cachera k) \<rbrakk>
 \<Longrightarrow> deriv G C m l (Cachera n)"
(*<*)
apply (simp add: ins_is_def Cachera_def deriv_def derivAssum_def, clarsimp)
apply (rule INSTR) apply assumption+ apply simp apply (simp add: heap_def)
apply fast
apply (erule CONSEQ)
apply (simp add: SP_pre_def) 
apply clarsimp apply (simp add: SP_post_def) apply clarsimp
  apply (drule NewElim1, fastforce) apply clarsimp
  apply (subgoal_tac "ba\<down>(nextLoc ba) = None")
    apply (simp add: AL_Size_UpdateSuc) 
  apply (rule nextLoc_fresh)
apply clarsimp
  apply (simp add: SP_inv_def)
  apply clarsimp
  apply (drule NewElim1, fastforce) apply clarsimp
  apply (subgoal_tac "ba\<down>(nextLoc ba) = None")
    apply (simp add: AL_Size_UpdateSuc) 
  apply (rule nextLoc_fresh)
done
(*>*)

lemma CACH_INSTR:
 "\<lbrakk> ins_is C m l I; 
    I \<in> { const c, dup, pop, swap, load x, store x, binop f, 
          unop g, getfield d F, putfield d F, checkcast d}; 
    MST\<down>(C,m)=Some(Mspec,Minv,Anno); Anno\<down>(l) = None; 
    derivAssum G C m (l+1) (Cachera n) \<rbrakk>
 \<Longrightarrow> deriv G C m l (Cachera n)"
(*<*)
apply (simp add: ins_is_def Cachera_def deriv_def derivAssum_def, clarsimp)
apply (rule INSTR) apply assumption+ apply simp apply (simp add: heap_def)
apply fast
apply (erule CONSEQ)
apply (simp add: SP_pre_def) 
apply (simp add: SP_post_def) apply clarsimp 
apply safe
apply (drule ConstElim1, fastforce) apply clarsimp
apply (drule DupElim1, fastforce) apply clarsimp
apply (drule PopElim1, fastforce) apply clarsimp
apply (drule SwapElim1, fastforce) apply clarsimp
apply (drule LoadElim1, fastforce) apply clarsimp
apply (drule StoreElim1, fastforce) apply clarsimp
apply (drule BinopElim1, fastforce) apply clarsimp
apply (drule UnopElim1, fastforce) apply clarsimp
apply (drule GetElim1, fastforce) apply clarsimp
apply (drule PutElim1, fastforce) apply clarsimp
  apply (simp add: updSize) 
apply (drule CastElim1, fastforce) apply clarsimp

apply (simp_all add: SP_inv_def)
apply safe
apply (drule ConstElim1, fastforce) apply clarsimp
apply (drule DupElim1, fastforce) apply clarsimp
apply (drule PopElim1, fastforce) apply clarsimp
apply (drule SwapElim1, fastforce) apply clarsimp
apply (drule LoadElim1, fastforce) apply clarsimp
apply (drule StoreElim1, fastforce) apply clarsimp
apply (drule BinopElim1, fastforce) apply clarsimp
apply (drule UnopElim1, fastforce) apply clarsimp
apply (drule GetElim1, fastforce) apply clarsimp
apply (drule PutElim1, fastforce) apply clarsimp
  apply (simp add: updSize) 
apply (drule CastElim1, fastforce) apply clarsimp
done
(*>*)

lemma CACH_RET: 
 "\<lbrakk> ins_is C m l vreturn; MST\<down>(C,m)=Some(Mspec,Minv,Anno); 
    Anno\<down>(l) = None \<rbrakk>
  \<Longrightarrow> deriv G C m l (Cachera 0)"
(*<*)
apply (simp add: ins_is_def Cachera_def deriv_def derivAssum_def, clarsimp)
apply (rule VRET) apply assumption+  apply simp apply (simp add: heap_def)
apply clarsimp
done
(*>*)

lemma CACH_GOTO:
 "\<lbrakk> ins_is C m l (goto pc); MST\<down>(C,m)=Some(Mspec,Minv,Anno);
    Anno\<down>(l) = None; derivAssum G C m pc (Cachera n) \<rbrakk>
 \<Longrightarrow> deriv G C m l (Cachera n)"
(*<*)
apply (simp add: ins_is_def Cachera_def deriv_def derivAssum_def, clarsimp)
apply (rule GOTO) apply assumption+ apply simp apply (simp add: heap_def)
apply (erule CONSEQ)
apply (simp add: SP_pre_def) 
apply (simp add: SP_post_def) apply clarsimp apply (drule GotoElim1, fastforce)
apply clarsimp
apply (simp add: SP_inv_def) apply clarsimp apply (drule GotoElim1, fastforce)
apply clarsimp
done
(*>*)

lemma CACH_IF:
  "\<lbrakk> ins_is C m l (iftrue pc); MST\<down>(C,m)=Some(Mspec,Minv,Anno); 
     Anno\<down>(l) = None; derivAssum G C m pc (Cachera n);
     derivAssum G C m (l+1) (Cachera n) \<rbrakk>
  \<Longrightarrow> deriv G C m l (Cachera n)"
(*<*)
apply (simp add: ins_is_def Cachera_def deriv_def derivAssum_def, clarsimp)
apply (rule IF) apply assumption+ apply (simp, simp add: heap_def)
apply (erule CONSEQ)
apply (simp add: SP_pre_def)
apply (simp add: SP_post_def) apply clarsimp apply (drule IfElim1, fastforce) apply clarsimp
apply (simp add: SP_inv_def) apply clarsimp  apply (drule IfElim1, fastforce) apply clarsimp
apply clarsimp
apply (erule CONSEQ)
apply (simp add: SP_pre_def)
apply (simp add: SP_post_def) apply clarsimp apply (drule IfElim1, fastforce) apply clarsimp
apply (simp add: SP_inv_def) apply clarsimp  apply (drule IfElim1, fastforce) apply clarsimp
done
(*>*)

lemma CACH_INVS: 
  "\<lbrakk> ins_is C m l (invokeS D m'); mbody_is D m' (par,code,l0);
     MST\<down>(C,m)=Some(Mspec,Minv,Anno); Anno\<down>(l) = None; 
     MST\<down>(D, m') = Some(mkSPEC (Cachera k) Anno2);
     nk = n+k; derivAssum G C m (l+1) (Cachera n)\<rbrakk>
   \<Longrightarrow> deriv G C m l (Cachera nk)"
(*<*)
apply (simp add: ins_is_def Cachera_def deriv_def derivAssum_def, clarsimp)

apply (rule INVS) apply assumption+ 
apply (simp add: mkSPEC_def) apply fastforce apply simp apply (simp add: heap_def)
apply (simp add: mkState_def)
apply (erule CONSEQ)
apply clarsimp
apply clarsimp apply (simp add: SINV_post_def mkState_def) 
apply clarsimp apply (simp add: SINV_inv_def mkState_def) 
done
(*>*)

text\<open>In addition, we have two rules for subtyping\<close>

lemma CACH_SUB:
 "\<lbrakk> deriv G C m l (Cachera n); n \<le> k\<rbrakk> \<Longrightarrow> deriv G C m l (Cachera k)"
(*<*)
apply (simp add: deriv_def derivAssum_def Cachera_def)
apply (rule CONSEQ, assumption+) 
apply simp
apply simp
apply simp
done
(*>*)

lemma CACHAssum_SUB:
 "\<lbrakk> derivAssum G C m l (Cachera n); n \<le> k\<rbrakk>
  \<Longrightarrow> derivAssum G C m l (Cachera k)"
(*<*)
apply (simp add: derivAssum_def Cachera_def)
apply (rule CONSEQ, assumption+) 
apply simp
apply simp
apply simp
done
(*>*)

text\<open>and specialised forms of the axiom rule and the injection rule.\<close>

lemma CACH_AX:
 "\<lbrakk> G\<down>(C,m,l) = Some (Cachera n); MST\<down>(C,m)=Some(Mspec,Minv,Anno); 
    Anno\<down>(l) = None\<rbrakk> 
 \<Longrightarrow> derivAssum G C m l (Cachera n)"
(*<*)
apply (simp add: derivAssum_def Cachera_def)
apply (drule AX) apply assumption apply simp apply (simp add: heap_def)
apply (rule CONSEQ) apply assumption+ apply simp apply simp apply simp
done
(*>*)

lemma CACH_INJECT:
  "deriv G C m l (Cachera n) \<Longrightarrow> derivAssum G C m l (Cachera n)"
(*<*)
apply (simp add: deriv_def derivAssum_def Cachera_def)
apply (erule INJECT)
done
(*>*)

text\<open>Finally, a verified-program rule relates specifications to
judgements for the method bodies. Thus, even the method specifications
may be given as derived assertions (modulo the \<open>mkSPEC\<close>-conversion).\<close>

lemma CACH_VP:
 "\<lbrakk> \<forall> c m par code l0. mbody_is c m (par, code, l0) \<longrightarrow>
          (\<exists> n Anno . MST\<down>(c,m) = Some(mkSPEC(Cachera n) Anno) \<and> 
                 deriv G c m l0 (Cachera n));
    \<forall> c m l A B I. G\<down>(c,m,l) = Some(A,B,I) \<longrightarrow>
                   (\<exists> n . (A,B,I) = Cachera n \<and> deriv G c m l (Cachera n))\<rbrakk> 
  \<Longrightarrow> VP"
(*<*)
apply (simp add: VP_def) apply (rule_tac x=G in exI, simp add: VP_G_def)
apply safe
(*G*)
  apply (erule thin_rl)
  apply (erule_tac x=C in allE, erule_tac x=m in allE, erule_tac x=l in allE, clarsimp)
  apply (simp add: deriv_def)
(*MST*)
apply (rotate_tac 1, erule thin_rl)
apply (erule_tac x=C in allE, erule_tac x=m in allE) 
apply(erule_tac x=par in allE, erule_tac x=code in allE, erule_tac x=l0 in allE, clarsimp)
apply (simp add: Cachera_def mkSPEC_def deriv_def, clarsimp)
apply (rule CONSEQ) apply assumption+ 
apply simp
apply (simp add: mkPost_def mkState_def)
apply (simp add: mkState_def mkInv_def)
done
(*>*)

subsection\<open>Soundness of high-level type system\<close>

text\<open>We define a first-order functional language where expressions
are stratified into primitive expressions and general expressions. The
language supports the construction of lists using constructors
$\mathit{NilPrim}$ and $\mathit{ConsPrim}\; h\; t$, and includes a
corresponding pattern match operation. In order to simplify the
compilation, function identifiers are taken to be pairs of class names
and method names.\<close>

type_synonym Fun = "Class \<times> Method"

datatype Prim =
  IntPrim int
| UnPrim "Val \<Rightarrow> Val" Var 
| BinPrim "Val \<Rightarrow> Val \<Rightarrow> Val" Var Var
| NilPrim
| ConsPrim Var Var
| CallPrim Fun "Var list"

datatype Expr = 
  PrimE Prim
| LetE Var Prim Expr
| CondE Var Expr Expr
| MatchE Var Expr Var Var Expr

type_synonym FunProg = "(Fun,Var list \<times> Expr) AssList"

text\<open>The type system uses contexts that associate a type (natural
number) to function identifiers.\<close>

type_synonym TP_Sig = "(Fun, nat) AssList"

text\<open>We first give the rules for primitive expressions.\<close>

inductive_set TP_prim::"(TP_Sig \<times> Prim \<times> nat)set"
where
TP_int: "(\<Sigma>,IntPrim i,0) : TP_prim"
|
TP_un: "(\<Sigma>,UnPrim f x,0) : TP_prim"
|
TP_bin: "(\<Sigma>,BinPrim f x y,0) : TP_prim"
|
TP_nil: "(\<Sigma>,NilPrim,0) : TP_prim"
|
TP_cons: "(\<Sigma>,ConsPrim x y,1) : TP_prim"
|
TP_Call: "\<lbrakk>\<Sigma>\<down>f = Some n\<rbrakk> \<Longrightarrow> (\<Sigma>,CallPrim f args,n) : TP_prim"

text\<open>Next, the rules for general expressions.\<close>

inductive_set TP_expr::"(TP_Sig \<times> Expr \<times> nat) set"
where
TP_sub: "\<lbrakk>(\<Sigma>,e,m):TP_expr; m \<le> n\<rbrakk> \<Longrightarrow> (\<Sigma>,e,n):TP_expr"
|
TP_prim:"\<lbrakk>(\<Sigma>,p,n):TP_prim\<rbrakk> \<Longrightarrow> (\<Sigma>,PrimE p,n) : TP_expr"
|
TP_let: "\<lbrakk>(\<Sigma>,p,k):TP_prim; (\<Sigma>,e,m):TP_expr; n = k+m\<rbrakk> 
        \<Longrightarrow> (\<Sigma>,LetE x p e,n) : TP_expr"
|
TP_Cond:"\<lbrakk>(\<Sigma>,e1,n):TP_expr; (\<Sigma>,e2,n):TP_expr\<rbrakk> 
        \<Longrightarrow>(\<Sigma>,CondE x e1 e2,n) : TP_expr"
|
TP_Match:"\<lbrakk>(\<Sigma>,e1,n):TP_expr; (\<Sigma>,e2,n):TP_expr \<rbrakk>
          \<Longrightarrow> (\<Sigma>,MatchE x e1 h t e2,n):TP_expr"

text\<open>A functional program is well-typed if its domain agrees with
that of some context such that each function body validates the
context entry.\<close>

definition TP::"TP_Sig \<Rightarrow> FunProg \<Rightarrow> bool" where
"TP \<Sigma> F = ((\<forall> f . (\<Sigma>\<down>f = None) = (F\<down>f = None)) \<and> 
          (\<forall> f n par e . \<Sigma>\<down>f = Some n \<longrightarrow> F\<down>f = Some (par,e) \<longrightarrow> (\<Sigma>,e,n):TP_expr))"

text\<open>For the translation into bytecode, we introduce identifiers for
a class of lists, the expected field names, and a temporary (reserved)
variable name.\<close> 

axiomatization
  LIST::Class and
  HD::Field and
  TL::Field and
  tmp::Var

text\<open>The compilation of primitive expressions extends a code block by
a sequence of JVM instructions that leave a value on the top of the
operand stack.\<close>

inductive_set compilePrim::
  "(Label \<times>  (Label,Instr) AssList \<times> Prim \<times> ((Label,Instr) AssList \<times> Label)) set" 
where
compileInt: "(l, code, IntPrim i, (code[l\<mapsto>(const (IVal i))],l+1)) : compilePrim"
|
compileUn:
  "(l, code, UnPrim f x, (code[l\<mapsto>(load x)][(l+1)\<mapsto>(unop f)],l+2)) : compilePrim"
|
compileBin: 
 "(l, code, BinPrim f x y,
     (code[l\<mapsto>(load x)][(l+1)\<mapsto>(load y)][(l+2)\<mapsto>(binop f)],l+3)) : compilePrim"
|
compileNil:
  "(l, code, NilPrim, (code[l\<mapsto>(const (RVal Nullref))],l+1)) : compilePrim"
|
compileCons:
  "(l, code, ConsPrim x y, 
      (code[l\<mapsto>(load y)][(l+1)\<mapsto>(load x)]
           [(l+2)\<mapsto>(new LIST)][(l+3)\<mapsto>store tmp]
           [(l+4)\<mapsto>load tmp][(l+5)\<mapsto>(putfield LIST HD)]
           [(l+6)\<mapsto>load tmp][(l+7)\<mapsto>(putfield LIST TL)]
           [(l+8)\<mapsto>(load tmp)], l+9)) : compilePrim"
|
compileCall_Nil:
  "(l, code, CallPrim f [],(code[l\<mapsto>invokeS (fst f) (snd f)],l+1)): compilePrim"  
|
compileCall_Cons:
  "\<lbrakk> (l+1,code[l\<mapsto>load x], CallPrim f args, OUT) : compilePrim\<rbrakk>
   \<Longrightarrow> (l, code, CallPrim f (x#args), OUT): compilePrim"            

text\<open>The following lemma shows that the resulting code is an
extension of the code submitted as an argument, and that the
new instructions define a contiguous block.\<close>

lemma compilePrim_Prop1[rule_format]:
"(l, code, p, OUT) : compilePrim \<Longrightarrow>
 (\<forall> code1l1 . OUT = (code1, l1) \<longrightarrow>
     (l < l1 \<and> (\<forall> ll . ll < l \<longrightarrow> code1\<down>ll = code\<down>ll) \<and> 
       (\<forall> ll . l \<le> ll \<longrightarrow> ll < l1 \<longrightarrow> (\<exists> ins . code1\<down>ll = Some ins))))"
(*<*)
apply (erule compilePrim.induct)
apply clarsimp 
  apply rule
  apply clarsimp apply (rule AL_update2) apply simp 
  apply (rule, rule AL_update1)
apply clarsimp
  apply rule
    apply clarsimp
    apply (rule AL_update5)
    apply (rule AL_update5)
    apply (simp, simp, simp)
  apply clarsimp
    apply (case_tac "ll=l", clarsimp, rule)
      apply (rule AL_update5)
      apply (simp add: AL_update1)
      apply simp
    apply (case_tac "ll=l+1", clarsimp, rule)
      apply (simp add: AL_update1)
    apply simp
(*BIN*)
 apply clarsimp
  apply rule
    apply clarsimp
    apply (rule AL_update5)
    apply (rule AL_update5)
    apply (rule AL_update5)
    apply (simp, simp, simp, simp)
  apply clarsimp
    apply (case_tac "ll=l", clarsimp, rule)
      apply (rule AL_update5)
      apply (rule AL_update5)
      apply (simp add: AL_update1)
      apply (simp, simp)
    apply (case_tac "ll=l+1", clarsimp, rule)
      apply (rule AL_update5)
      apply (simp add: AL_update1)
      apply simp
    apply (case_tac "ll=l+2", clarsimp, rule)
      apply (simp add: AL_update1)
    apply simp
apply clarsimp 
  apply rule
    apply clarsimp apply (rule AL_update2) apply simp
    apply (rule, rule AL_update1) apply simp
apply clarsimp
  apply rule apply clarsimp
    apply (rule AL_update5)
    apply (rule AL_update5)
    apply (rule AL_update5)
    apply (rule AL_update5)
    apply (rule AL_update5)
    apply (rule AL_update5)
    apply (rule AL_update5)
    apply (rule AL_update5)
    apply (rule AL_update5)
    apply (simp, simp, simp, simp)
    apply (simp, simp, simp, simp)
    apply (simp, simp)
  apply clarsimp
    apply (case_tac "ll=l", clarsimp, rule)
      apply (rule AL_update5)
      apply (rule AL_update5)
      apply (rule AL_update5)
      apply (rule AL_update5)
      apply (rule AL_update5)
      apply (rule AL_update5)
      apply (rule AL_update5)
      apply (rule AL_update5)
      apply (simp add: AL_update1)
      apply (simp, simp, simp,simp)
      apply (simp, simp, simp,simp)
    apply (case_tac "ll=l+1", clarsimp, rule)
      apply (rule AL_update5)
      apply (rule AL_update5)
      apply (rule AL_update5)
      apply (rule AL_update5)
      apply (rule AL_update5)
      apply (rule AL_update5)
      apply (rule AL_update5)
      apply (simp add: AL_update1)
      apply (simp, simp, simp,simp)
      apply (simp, simp, simp)
    apply (case_tac "ll=l+2", clarsimp, rule)
      apply (rule AL_update5)
      apply (rule AL_update5)
      apply (rule AL_update5)
      apply (rule AL_update5)
      apply (rule AL_update5)
      apply (rule AL_update5)
      apply (simp add: AL_update1)
      apply (simp, simp, simp,simp)
      apply (simp, simp)
    apply (case_tac "ll=l+3", clarsimp, rule)
      apply (rule AL_update5)
      apply (rule AL_update5)
      apply (rule AL_update5)
      apply (rule AL_update5)
      apply (rule AL_update5)
      apply (rule AL_update1) 
      apply (simp, simp, simp,simp)
      apply simp
    apply (case_tac "ll=l+4", clarsimp, rule)
      apply (rule AL_update5)
      apply (rule AL_update5)
      apply (rule AL_update5)
      apply (rule AL_update5)
      apply (rule AL_update1) 
      apply (simp, simp, simp,simp)
    apply (case_tac "ll=l+5", clarsimp, rule)
      apply (rule AL_update5)
      apply (rule AL_update5)
      apply (rule AL_update5)
      apply (rule AL_update1) 
      apply (simp, simp, simp)
    apply (case_tac "ll=l+6", clarsimp, rule)
      apply (rule AL_update5)
      apply (rule AL_update5)
      apply (rule AL_update1) 
      apply (simp, simp)
    apply (case_tac "ll=l+7", clarsimp, rule)
      apply (rule AL_update5)
      apply (rule AL_update1) 
      apply (simp)
    apply (case_tac "ll=l+8", clarsimp, rule)
      apply (rule AL_update1)
      apply simp
(*CALL-NIL*)
apply clarsimp 
  apply (rule, clarsimp)
    apply (rule AL_update5) apply (simp ,simp)
  apply (rule, rule AL_update1)
(*CALL-CONS*)
apply clarsimp
  apply (rule, clarsimp)
    apply (rule AL_update5) apply simp apply simp
  apply clarsimp
    apply (erule_tac x=ll in allE)+ apply clarsimp 
    apply (case_tac "l=ll", clarsimp) apply (rule, rule AL_update1) 
    apply clarsimp
done
(*>*)

text\<open>A signature corresponds to a method specification table if all
context entries are represented as \<open>MST\<close> entries and method
names that are defined in the global program \<open>P\<close>.\<close>

definition Sig_good::"TP_Sig \<Rightarrow> bool" where
"Sig_good \<Sigma> =
 (\<forall> C m n. \<Sigma>\<down>(C,m) = Some n \<longrightarrow> 
    (MST\<down>(C, m) = Some (mkSPEC (Cachera n) emp) \<and>
    (\<exists> par code l0 . mbody_is C m (par,code,l0))))"

text\<open>This definition requires \<open>MST\<close> to associate the
specification $$\mathit{mkSPEC}\; (\mathit{Cachera}\; n)\;
\mathit{emp}$$ to each method to which the type signature associates
the type $n$. In particular, this requires the annotation table of
such a method to be empty. Additionally, the global program $P$ is
required to contain a method definition for each method
(i.e.~function) name occurring in the domain of the signature.\<close>

text\<open>An auxiliary abbreviation that captures when a block of code has
trivial annotations and only comprises defined program labels.\<close>

definition Segment::
  "Class \<Rightarrow> Method \<Rightarrow> Label \<Rightarrow> Label \<Rightarrow> (Label,Instr)AssList \<Rightarrow> bool"
where
"Segment C m l l1 code =
    (\<exists> Mspec Minv Anno . MST\<down>(C,m) = Some(Mspec,Minv,Anno) \<and> 
      (\<forall>ll. l \<le> ll \<longrightarrow> ll < l1 \<longrightarrow>
          Anno\<down>(ll) = None \<and> (\<exists>ins. ins_is C m ll ins \<and> code\<down>ll = Some ins)))"

(*<*)
lemma Segment_triv:
  "\<lbrakk>Segment C m l l1 code; MST\<down>(C,m) = Some(Mspec,Minv,Anno); l \<le> ll; ll < l1\<rbrakk> 
  \<Longrightarrow> (Anno\<down>(ll) = None \<and> (\<exists>ins. ins_is C m ll ins \<and> code\<down>ll = Some ins))"
by (simp add: Segment_def)

lemma Segment_triv1:
  "\<lbrakk>Segment C m l l1 code; MST\<down>(C,m) = Some(Mspec,Minv,Anno); l \<le> ll; ll < l1\<rbrakk> \<Longrightarrow> Anno\<down>(ll) = None"
by (simp add: Segment_def)

lemma Segment_triv2:
  "\<lbrakk>Segment C m l l1 code; l \<le> ll; ll < l1\<rbrakk> \<Longrightarrow> (\<exists>ins. ins_is C m ll ins \<and> code\<down>ll = Some ins)"
apply (simp add: Segment_def) apply clarsimp done

lemma Segment_A:
  "\<lbrakk>Segment C m l l1 code; l \<le> ll; ll < l1\<rbrakk> \<Longrightarrow> Segment C m ll l1 code" by (simp add: Segment_def, clarsimp)
(*>*)

text\<open>The soundness of (the translation of) a function call is proven
by induction on the list of arguments.\<close>

lemma Call_SoundAux[rule_format]:
 "\<Sigma>\<down>f = Some n \<longrightarrow> 
    MST\<down>(fst f,snd f) = Some(mkSPEC (Cachera n) Anno2) \<longrightarrow>
    (\<exists> par body l0 . mbody_is (fst f) (snd f) (par,body,l0)) \<longrightarrow>
       (\<forall>l code code1 l1 G C m T MI k.
          (l, code, CallPrim f args, code1, l1) \<in> compilePrim \<longrightarrow>
          MST\<down>(C, m) = Some (T, MI,Anno) \<longrightarrow> Segment C m l l1 code1 \<longrightarrow>
          derivAssum G C m l1 (Cachera k) \<longrightarrow> 
          deriv G C m l (Cachera (n+k)))"
(*<*)
apply (induct args)
apply clarsimp
  apply (erule compilePrim.cases) apply (simp,simp,simp, simp, simp, clarsimp)  
    apply (drule Segment_triv) apply assumption apply (subgoal_tac "la \<le> la", assumption, simp) apply clarsimp 
  apply (erule conjE)+ apply (erule exE)+ apply (erule conjE)+
  apply (rule CACH_INVS) 
    apply (simp add: AL_update1) apply clarsimp apply fast
    apply assumption
    apply assumption
    apply assumption
    apply assumption
    apply simp
    apply simp
  apply simp
(*CONS*)
  apply clarsimp
  apply (erule compilePrim.cases) apply (simp, simp, simp, simp, simp, simp) apply clarsimp
  apply (erule impE) apply fast
  apply (erule_tac x="la+1" in allE, rotate_tac -1)
  apply (erule_tac x="codea[la\<mapsto>load x]" in allE, rotate_tac -1)
  apply (erule_tac x=ab in allE, rotate_tac -1)
  apply (erule_tac x=ba in allE, clarsimp)
  apply (erule_tac x=G in allE, rotate_tac -1)
  apply (erule_tac x=C in allE, rotate_tac -1)
  apply (erule_tac x=m in allE, clarsimp)
  apply (frule compilePrim_Prop1) apply fastforce apply clarsimp 
  apply (erule impE, erule Segment_A) apply simp apply simp 
    apply (drule Segment_triv) apply assumption apply (subgoal_tac "la \<le> la", assumption, simp) apply clarsimp 
  apply (erule conjE)+ apply (erule exE)+ apply (erule conjE)+
  apply (rule CACH_INSTR) apply assumption 
    apply (rotate_tac -5, erule_tac x=la in allE, clarsimp)   apply (simp add: AL_update1) 
      apply clarsimp apply fast
    apply assumption
    apply assumption
  apply (rule CACH_INJECT)
  apply simp
done
(*>*)

lemma Call_Sound:
 "\<lbrakk> Sig_good \<Sigma>; \<Sigma>\<down>f = Some n; 
   (l, code, CallPrim f args, code1, l1) \<in> compilePrim;
   MST\<down>(C,m) = Some (T, MI,Anno); Segment C m l l1 code1;
   derivAssum G C m l1 (Cachera nn); k = n+nn\<rbrakk> 
 \<Longrightarrow> deriv G C m l (Cachera k)"
(*<*)
apply (case_tac f, clarsimp)
apply (rule Call_SoundAux)
apply assumption apply (simp add: Sig_good_def) apply (simp add: Sig_good_def) 
apply assumption apply assumption apply assumption apply assumption 
done
(*>*)
 
text\<open>The definition of basic instructions.\<close>

definition basic::"Instr \<Rightarrow> bool" where
"basic ins = ((\<exists> c . ins = const c) \<or> ins = dup \<or> 
              ins= pop \<or> ins= swap \<or> (\<exists> x. ins= load x) \<or>
              (\<exists> y. ins= store y) \<or> (\<exists> f. ins= binop f) \<or>
              (\<exists> g. ins= unop g) \<or> (\<exists> c1 F1. ins= getfield c1 F1) \<or>
              (\<exists> c2 F2. ins=  putfield c2 F2) \<or>
              (\<exists> c3. ins=  checkcast c3))"

text\<open>Next, we prove the soundness of basic instructions. The
hypothesis refers to instructions located at the program
continuation.\<close>

lemma Basic_Sound: 
  "\<lbrakk> Segment C m l ll code; MST\<down>(C,m) = Some (T, MI,Anno); l\<le>l1; l1 < ll;
     l2=l1+1; code\<down>l1 = Some ins; basic ins; derivAssum G C m l2 (Cachera n)\<rbrakk>
   \<Longrightarrow> deriv G C m l1 (Cachera n)"
(*<*)
apply (drule Segment_triv) apply assumption+ apply clarsimp  apply (simp add: basic_def)
apply (erule disjE, clarsimp) apply (erule CACH_INSTR) apply fast apply assumption apply assumption apply simp
apply (erule disjE, clarsimp) apply (erule CACH_INSTR) apply fast apply assumption apply assumption apply simp
apply (erule disjE, clarsimp) apply (erule CACH_INSTR) apply fast apply assumption apply assumption apply simp
apply (erule disjE, clarsimp) apply (erule CACH_INSTR) apply fast apply assumption apply assumption apply simp
apply (erule disjE, clarsimp) apply (erule CACH_INSTR) apply fast apply assumption apply assumption apply simp
apply (erule disjE, clarsimp) apply (erule CACH_INSTR) apply fast apply assumption apply assumption apply simp
apply (erule disjE, clarsimp) apply (erule CACH_INSTR) apply fast apply assumption apply assumption apply simp
apply (erule disjE, clarsimp) apply (erule CACH_INSTR) apply fast apply assumption apply assumption apply simp
apply (erule disjE, clarsimp) apply (erule CACH_INSTR) apply fast apply assumption apply assumption apply simp 
apply (erule disjE, clarsimp) apply (erule CACH_INSTR) apply fast apply assumption apply assumption apply simp
apply clarsimp apply (erule CACH_INSTR) apply fast apply assumption apply assumption apply simp 
done
(*>*)

text\<open>Following this, the soundness of the type system for primitive
expressions. The proof proceeds by induction on the typing
judgement.\<close>

lemma TP_prim_Sound[rule_format]:
  "(\<Sigma>,p,n):TP_prim \<Longrightarrow> 
   Sig_good \<Sigma> \<longrightarrow>
   (\<forall> l code code1 l1 G C m T MI Anno nn k.
         (l, code, p, (code1,l1)) : compilePrim \<longrightarrow> 
         MST\<down>(C,m) = Some (T,MI,Anno) \<longrightarrow>
         Segment C m l l1 code1 \<longrightarrow> derivAssum G C m l1 (Cachera nn) \<longrightarrow> 
         k = n+nn \<longrightarrow> deriv G C m l (Cachera k))"
(*<*)
apply (erule TP_prim.induct)
(*INT*)
apply clarsimp apply (erule thin_rl)
  apply (erule compilePrim.cases, simp_all, clarsimp)
  apply (rule Basic_Sound) apply assumption apply assumption apply (simp,simp) apply simp
  apply (simp add: AL_update1)
  apply (simp add: basic_def)
  apply assumption
(*UN*) 
apply clarsimp apply (erule thin_rl)
  apply (erule compilePrim.cases, simp_all, clarsimp)
  apply (rule Basic_Sound) apply assumption apply assumption apply (simp, simp) 
  apply simp 
  apply (rule AL_update5) apply (simp add: AL_update1) apply simp
  apply (simp add: basic_def)
  apply (rule CACH_INJECT) 
  apply (rule Basic_Sound) apply assumption apply assumption apply (simp, simp) 
  apply simp 
  apply (simp add: AL_update1) 
  apply (simp add: basic_def)
   apply (subgoal_tac "la+2=2+la", clarsimp,simp)
(*BIN*)
apply clarsimp apply (erule thin_rl)
  apply (erule compilePrim.cases, simp_all, clarsimp)
  apply (rule Basic_Sound) apply assumption apply assumption apply (simp, simp) apply simp 
  apply (rule AL_update5) apply (rule AL_update5) apply (simp add: AL_update1) apply (simp, simp)
  apply (simp add: basic_def)
  apply (rule CACH_INJECT) 
  apply (rule Basic_Sound) apply assumption apply assumption apply (simp, simp) 
  apply simp 
  apply (rule AL_update5) apply (simp add: AL_update1) apply simp
  apply (simp add: basic_def)
  apply (rule CACH_INJECT) 
  apply (rule Basic_Sound) apply assumption apply assumption apply (simp, simp) 
  apply simp 
  apply (rule AL_update1a) apply simp
  apply (simp add: basic_def)
   apply (subgoal_tac "la+3=3+la", clarsimp, simp)
(*Nil*)
apply clarsimp apply (erule thin_rl)
  apply (erule compilePrim.cases, simp_all, clarsimp)
  apply (rule Basic_Sound) apply assumption apply assumption apply (simp,simp) apply simp 
  apply (simp add: AL_update1)
  apply (simp add: basic_def)
  apply assumption
(*CONS*)
apply clarsimp apply (erule thin_rl)
  apply (erule compilePrim.cases, simp_all, clarsimp)
  apply (rule Basic_Sound) apply assumption apply assumption apply (simp, simp) apply simp
  apply (rule AL_update5) apply (rule AL_update5) apply (rule AL_update5) apply (rule AL_update5)
    apply (rule AL_update5) apply (rule AL_update5) apply (rule AL_update5) apply (rule AL_update5) 
    apply (simp add: AL_update1) apply (simp,simp,simp,simp) apply (simp,simp,simp,simp)
  apply (simp add: basic_def)
  apply (rule CACH_INJECT) 
  apply (rule Basic_Sound) apply assumption apply assumption apply (simp, simp) apply simp
  apply (rule AL_update5) apply (rule AL_update5) apply (rule AL_update5) apply (rule AL_update5)
    apply (rule AL_update5) apply (rule AL_update5) apply (rule AL_update5) 
    apply (simp add: AL_update1) apply (simp,simp,simp,simp) apply (simp,simp,simp)
  apply (simp add: basic_def)
  apply (rule CACH_INJECT) 
  apply (frule Segment_triv) apply assumption apply (subgoal_tac "la \<le> la+2", assumption, simp) 
    apply simp 
  apply (subgoal_tac "la+2=2+la", clarsimp)
    apply (drule AL_update3, simp) 
    apply (drule AL_update3, simp) 
    apply (drule AL_update3, simp) 
    apply (drule AL_update3, simp) 
    apply (drule AL_update3, simp) 
    apply (drule AL_update3, simp) apply (simp add: AL_update1) apply clarsimp
    apply (rule CACH_NEW) apply assumption+
      apply (simp, simp)
    apply (rule CACH_INJECT) 
    apply (rule Basic_Sound) apply assumption apply assumption apply (simp, simp) apply simp
      apply (rule AL_update5) apply (rule AL_update5) apply (rule AL_update5) apply (rule AL_update5)
      apply (rule AL_update5)
      apply (rule AL_update1a) apply simp apply (simp,simp,simp,simp) apply simp
      apply (simp add: basic_def)
    apply (rule CACH_INJECT) 
    apply (rule Basic_Sound) apply assumption apply assumption apply (simp, simp) apply simp
      apply (rule AL_update5) apply (rule AL_update5) apply (rule AL_update5) apply (rule AL_update5)
        apply (rule AL_update1a) apply simp apply (simp,simp,simp,simp) 
    apply (simp add: basic_def)
    apply (rule CACH_INJECT) 
      apply (rule Basic_Sound) apply assumption apply assumption apply (simp, simp) apply simp
      apply (rule AL_update5) apply (rule AL_update5) apply (rule AL_update5) 
        apply (rule AL_update1a) apply simp apply (simp,simp,simp) 
        apply (simp add: basic_def)
    apply (rule CACH_INJECT) 
    apply (rule Basic_Sound) apply assumption apply assumption apply (simp, simp) apply simp
      apply (rule AL_update5) apply (rule AL_update5) 
        apply (rule AL_update1a) apply simp apply (simp,simp) 
        apply (simp add: basic_def)
    apply (rule CACH_INJECT) 
    apply (rule Basic_Sound) apply assumption apply assumption apply (simp, simp) apply simp
      apply (rule AL_update5) 
        apply (rule AL_update1a) apply simp apply simp
        apply (simp add: basic_def)
    apply (rule CACH_INJECT) 
    apply (rule Basic_Sound) apply assumption apply assumption apply (simp, simp) apply simp
      apply (rule AL_update1a) apply simp 
      apply (simp add: basic_def)
      apply (subgoal_tac "la+9=9+la", clarsimp, simp)
  apply simp
(*Call*)
apply clarsimp
  apply (rule Call_Sound) apply assumption+ apply simp
done
(*>*)

text\<open>The translation of general expressions is defined similarly, but
no code continuation is required.\<close>

inductive_set compileExpr::
  "(Label \<times> (Label,Instr) AssList \<times> Expr \<times> ((Label,Instr) AssList \<times> Label)) set"
where
compilePrimE: 
 "\<lbrakk>(l, code, p, (code1,l1)) : compilePrim; OUT = (code1[l1\<mapsto>vreturn],l1+1)\<rbrakk>
   \<Longrightarrow> (l, code, PrimE p, OUT):compileExpr"
|
compileLetE:
  "\<lbrakk>(l, code, p, (code1,l1)) : compilePrim; (code2,l2) = (code1[l1\<mapsto>(store x)],l1+1);
     (l2, code2, e, OUT) : compileExpr\<rbrakk>
   \<Longrightarrow> (l, code, LetE x p e, OUT) : compileExpr"
|
compileCondE:
  "\<lbrakk>(l+2, code, e2, (codeElse,XXX)) : compileExpr;
     (XXX, codeElse, e1, (codeThen,YYY) ) : compileExpr ;
     OUT = (codeThen[l\<mapsto>load x][(l+1)\<mapsto>(iftrue XXX)], YYY)\<rbrakk>
   \<Longrightarrow> (l, code, CondE x e1 e2, OUT): compileExpr" 
|                                                                        
compileMatchE:
  "\<lbrakk>(l+9, code, e2, (codeCons,lNil)) : compileExpr;
     (lNil, codeCons, e1, (codeNil,lRes) ) : compileExpr ;
     OUT = (codeNil[l\<mapsto>(load x)]
                   [(l+1)\<mapsto>(unop (\<lambda> v . if v = RVal Nullref
                                 then TRUE else FALSE))]
                   [(l+2)\<mapsto>(iftrue lNil)]
                   [(l+3)\<mapsto>(load x)]
                   [(l+4)\<mapsto>(getfield LIST HD)]
                   [(l+5)\<mapsto>(store h)]
                   [(l+6)\<mapsto>(load x)]
                   [(l+7)\<mapsto>(getfield LIST TL)]
                   [(l+8)\<mapsto>(store t)], lRes) \<rbrakk>
   \<Longrightarrow> (l, code, MatchE x e1 h t e2, OUT): compileExpr"

text\<open>Again, we prove an auxiliary result on the emitted code, by
induction on the compilation judgement.\<close>

lemma compileExpr_Prop1[rule_format]:
"(l,code,e,OUT) : compileExpr \<Longrightarrow> 
  (\<forall> code1 l1 . OUT = (code1, l1) \<longrightarrow> 
      (l < l1 \<and> 
       (\<forall> ll . ll < l \<longrightarrow> code1\<down>ll = code\<down>ll) \<and> 
       (\<forall> ll . l \<le> ll \<longrightarrow> ll < l1 \<longrightarrow> (\<exists> ins . code1\<down>ll = Some ins))))"
(*<*)
apply (erule compileExpr.induct)
(*PRIM*)
apply clarsimp apply (drule compilePrim_Prop1) apply fastforce  apply clarsimp
  apply rule apply clarsimp apply (erule_tac x=ll in allE, clarsimp)
    apply (erule AL_update5) apply simp 
  apply clarsimp apply (case_tac "ll < l1", clarsimp) 
      apply (rotate_tac 1, erule_tac x=ll in allE, clarsimp) 
        apply (rule, erule AL_update5) apply simp 
  apply (subgoal_tac "ll= l1", clarsimp) apply (rule, simp add: AL_update1) apply simp
(*LET*)
apply clarsimp
  apply (drule compilePrim_Prop1) apply fastforce apply clarsimp
  apply rule apply clarsimp
    apply (rule AL_update5) apply simp apply simp
  apply clarsimp apply (erule_tac x=ll in allE)+ apply clarsimp 
    apply (case_tac "ll <l1", clarsimp) apply (rule, erule AL_update5) apply simp
     apply (subgoal_tac "ll=l1", clarsimp)
     apply (simp add: AL_update1) apply simp
(*COND*)
apply clarsimp 
  apply (rule, clarsimp)
    apply (rule AL_update5)
    apply (rule AL_update5) apply (simp ,simp)
    apply simp
  apply clarsimp
    apply (case_tac "ll=l+1", clarsimp, rule) apply(rule AL_update1)
    apply (case_tac "ll=l", clarsimp, rule) 
      apply (rule AL_update5) apply(simp add: AL_update1) apply simp
    apply (case_tac "XXX \<le> ll", clarsimp)
      apply (rotate_tac -3, erule_tac x=ll in allE, clarsimp)
        apply rule apply (rule AL_update5) apply (erule AL_update5) apply (simp, simp)
    apply clarsimp 
      apply (rotate_tac -6, erule_tac x=ll in allE, clarsimp)
      apply (rotate_tac -2, erule_tac x=ll in allE, clarsimp)
        apply rule apply (rule AL_update5) apply (erule AL_update5) apply (simp, simp)
(*Match*)
apply clarsimp 
  apply (rule, clarsimp)
    apply (rule AL_update5)
    apply (rule AL_update5) 
    apply (rule AL_update5)
    apply (rule AL_update5)
    apply (rule AL_update5) 
    apply (rule AL_update5) 
    apply (rule AL_update5)
    apply (rule AL_update5) 
    apply (rule AL_update5) apply (simp ,simp, simp) apply (simp ,simp, simp) apply (simp ,simp, simp)
    apply simp
  apply clarsimp
    apply (case_tac "ll=l+8", clarsimp, rule) apply(simp add: AL_update1)
    apply (case_tac "ll=l+7", clarsimp, rule) apply (rule AL_update5) apply(simp add: AL_update1) apply simp
    apply (case_tac "ll=l+6", clarsimp, rule) apply (rule AL_update5) apply (rule AL_update5) 
      apply(simp add: AL_update1) apply simp apply simp
    apply (case_tac "ll=l+5", clarsimp, rule) apply (rule AL_update5)  apply (rule AL_update5) 
      apply (rule AL_update5)  apply(simp add: AL_update1) apply (simp,simp,simp)
    apply (case_tac "ll=l+4", clarsimp, rule) apply (rule AL_update5) apply (rule AL_update5) 
      apply (rule AL_update5) apply (rule AL_update5) apply(simp add: AL_update1) apply (simp,simp,simp,simp)
    apply (case_tac "ll=l+3", clarsimp, rule) apply (rule AL_update5) apply (rule AL_update5) 
      apply (rule AL_update5) apply (rule AL_update5) apply (rule AL_update5) apply(simp add: AL_update1)
      apply (simp,simp,simp,simp,simp)
    apply (case_tac "ll=l+2", clarsimp, rule) apply (rule AL_update5) apply (rule AL_update5) 
      apply (rule AL_update5) apply (rule AL_update5) apply (rule AL_update5) apply (rule AL_update5) 
      apply(simp add: AL_update1)
      apply (simp,simp,simp,simp,simp, simp)
    apply (case_tac "ll=l+1", clarsimp, rule) apply (rule AL_update5) apply (rule AL_update5) 
      apply (rule AL_update5) apply (rule AL_update5) apply (rule AL_update5) apply (rule AL_update5) 
      apply (rule AL_update5) apply(simp add: AL_update1) 
      apply (simp,simp,simp,simp,simp, simp, simp) 
    apply (case_tac "ll=l", clarsimp, rule) apply (rule AL_update5) apply (rule AL_update5) 
      apply (rule AL_update5) apply (rule AL_update5) apply (rule AL_update5) apply (rule AL_update5) 
      apply (rule AL_update5) apply (rule AL_update5) apply(simp add: AL_update1) apply (simp, simp)
      apply (simp,simp,simp,simp,simp, simp)
    apply (case_tac "lNil \<le> ll", clarsimp)
      apply (rotate_tac -3, erule_tac x=ll in allE, clarsimp)
        apply rule apply (rule AL_update5) apply (rule AL_update5) apply (rule AL_update5)
            apply (rule AL_update5) apply (rule AL_update5) apply (rule AL_update5)
            apply (rule AL_update5) apply (rule AL_update5) apply (erule AL_update5)
          apply (simp, simp, simp)
          apply (simp, simp, simp)
          apply (simp, simp, simp)
(*   apply simp*)
      apply (rotate_tac 5) apply( erule_tac x=ll in allE, erule impE) apply (erule thin_rl) 
         apply (erule thin_rl) apply (rotate_tac -1, erule thin_rl)
         apply (rotate_tac -1, erule thin_rl) 
         apply (rotate_tac -1, erule thin_rl) 
         apply (rotate_tac -1, erule thin_rl) 
         apply (rotate_tac -1, erule thin_rl) apply simp 
         apply (subgoal_tac "ll < lNil")
         prefer 2 apply(  erule thin_rl, erule thin_rl) 
           apply (erule thin_rl, erule thin_rl) 
           apply (erule thin_rl, erule thin_rl) 
           apply (erule thin_rl, erule thin_rl) 
           apply (erule thin_rl, erule thin_rl) 
           apply (erule thin_rl, erule thin_rl) 
           apply (erule thin_rl, rotate_tac 1, erule thin_rl) 
           apply (erule thin_rl, erule thin_rl) 
           apply (erule thin_rl, erule thin_rl) apply simp
         apply (erule impE, assumption) 
      apply (erule_tac x=ll in allE, erule impE, assumption)
      apply (erule exE)
        apply rule apply (rule AL_update5) apply (rule AL_update5) apply (rule AL_update5) 
         apply (rule AL_update5) apply (rule AL_update5) apply (rule AL_update5) 
         apply (rule AL_update5) apply (rule AL_update5) apply (rule AL_update5)
           apply (erule thin_rl, erule thin_rl) 
           apply (erule thin_rl, erule thin_rl) 
           apply (erule thin_rl, erule thin_rl)  
           apply (erule thin_rl, erule thin_rl) 
           apply (erule thin_rl, erule thin_rl) 
           apply (erule thin_rl, erule thin_rl) 
           apply (erule thin_rl, erule thin_rl) 
           apply (erule thin_rl, erule thin_rl) 
           apply (erule thin_rl, erule thin_rl) apply simp
          apply fast+ 
done
(*>*)

text\<open>Then, soundness of the epxression type system is proven by
induction on the typing judgement.\<close>

lemma TP_epxr_Sound[rule_format]:
"(\<Sigma>,e,n):TP_expr \<Longrightarrow> Sig_good \<Sigma> \<longrightarrow>
 (\<forall> l code code1 l1 G C m T MI Anno.
    (l, code, e, (code1,l1)):compileExpr \<longrightarrow>
    MST\<down>(C,m) = Some (T,MI,Anno) \<longrightarrow>
    Segment C m l l1 code1 \<longrightarrow> deriv G C m l (Cachera n))"
(*<*)
apply (erule TP_expr.induct)
(*SUB*)
apply clarsimp
   apply (rotate_tac 2, erule thin_rl, rotate_tac -2)
   apply (erule_tac x=l in allE, erule_tac x=code in allE)
   apply (erule_tac x=code1 in allE, rotate_tac -1, erule_tac x=l1 in allE, clarsimp)
   apply (erule_tac x=G in allE, erule_tac x=C in allE)
   apply (erule_tac x=ma in allE, clarsimp)
   apply (erule CACH_SUB) apply assumption
(*PRIM*)
apply clarsimp 
  apply (erule compileExpr.cases) 
  prefer 2 apply simp
  prefer 2 apply simp
  prefer 2 apply simp
  apply clarsimp 
  apply (erule TP_prim_Sound) apply fast  apply assumption+
     apply (simp add: Segment_def, clarsimp)
     apply (erule_tac x=ll in allE, clarsimp) 
       apply (drule AL_update3) apply simp 
       apply (rule, rule, assumption, assumption)
     prefer 2 apply simp
  apply (simp add: Segment_def)
     apply (erule_tac x=l1a in allE, simp) apply (erule impE)
       apply (drule compilePrim_Prop1) apply fastforce   apply simp
     apply clarsimp  
     apply (simp add: AL_update1, clarsimp)
     apply (rule CACH_INJECT)
     apply (erule CACH_RET)  apply assumption apply assumption
(*LET*)
apply clarsimp 
  apply (erule compileExpr.cases) 
  apply simp
  prefer 2 apply simp
  prefer 2 apply simp
  apply clarsimp
  apply (frule compilePrim_Prop1) apply fastforce
  apply (frule compileExpr_Prop1) apply fastforce apply clarsimp 
  apply (erule_tac x="l1a+1" in allE, erule_tac x="code1a[l1a\<mapsto>store xa]" in allE, 
         erule_tac x=a in allE, rotate_tac -1)
  apply (erule_tac x=b in allE, clarsimp)
  apply (erule_tac x=G in allE, erule_tac x=C in allE, erule_tac x=ma in allE, clarsimp)
  apply (erule impE) apply (erule Segment_A) apply (simp,simp)
  apply (rule TP_prim_Sound) apply assumption apply assumption
       apply assumption apply assumption 
         apply (simp add: Segment_def) apply clarsimp apply (erule_tac x=ll in allE, clarsimp) apply (rule, rule, assumption)
          apply(drule AL_update3) apply simp apply assumption
    prefer 2 apply simp
  apply (rule CACH_INJECT)
    apply (rule Basic_Sound) prefer 2 apply assumption prefer 4 apply simp prefer 2 apply (subgoal_tac "l1a \<le> l1a", assumption, simp)
    prefer 3 apply (subgoal_tac "a\<down>l1a = Some(store xa)", assumption)
         apply (rotate_tac -3, erule_tac x=l1a in allE, clarsimp) apply (simp add: AL_update1)
    apply (subgoal_tac "Segment C ma l1a b a", assumption) apply (erule Segment_A) apply (simp,simp) 
    apply simp
    apply (simp add: basic_def)
    apply (erule CACH_INJECT)
(*Cond*)
apply clarsimp
  apply (erule compileExpr.cases) 
  apply simp apply simp prefer 2 apply simp
  apply clarsimp
  apply (erule_tac x=XXX in allE, erule_tac x= codeElse in allE, 
         erule_tac x=codeThen in allE, rotate_tac -1) 
  apply (erule_tac x= YYY in allE, clarsimp)
  apply (erule_tac x=G in allE, rotate_tac -1, erule_tac x=C in allE,
         erule_tac x=m in allE, clarsimp)
  apply (erule_tac x="la+2" in allE, erule_tac x= codea in allE, 
         erule_tac x=codeElse in allE, rotate_tac -1) 
  apply (erule_tac x= XXX in allE, clarsimp)
  apply (erule_tac x=G in allE, rotate_tac -1, erule_tac x=C in allE,
         erule_tac x=m in allE, clarsimp)
  apply (drule compileExpr_Prop1) apply fastforce apply clarsimp 
  apply (drule compileExpr_Prop1) apply fastforce apply clarsimp 
  apply (erule impE) apply (rotate_tac 5, erule thin_rl, simp add: Segment_def,clarsimp)
    apply (rotate_tac -3, erule_tac x=ll in allE, clarsimp)
    apply (drule AL_update3, simp)
    apply (drule AL_update3, simp) apply (rule, rule, assumption, assumption)
  apply (erule impE) apply (simp add: Segment_def,clarsimp)
    apply (erule_tac x=ll in allE, clarsimp)
    apply (erule_tac x=ll in allE, clarsimp)
    apply (erule_tac x=ll in allE, clarsimp)
    apply (erule_tac x=ll in allE, clarsimp)
    apply (erule_tac x=ll in allE, clarsimp)
    apply (drule AL_update3, simp)
    apply (drule AL_update3, simp) apply clarsimp
  apply (frule Segment_triv) apply assumption apply (subgoal_tac "la \<le> la", assumption, simp) apply simp
  apply clarsimp
  apply (drule AL_update3) apply simp apply (simp add: AL_update1) apply clarsimp
  apply (rule CACH_INSTR) 
    apply assumption    
    apply fast
    apply assumption
    apply assumption
  apply (rule CACH_INJECT)
  apply (frule Segment_triv) apply assumption apply (subgoal_tac "la \<le> la+1", assumption, simp) apply simp
  apply clarsimp
  apply (simp add: AL_update1) apply clarsimp
  apply (frule Segment_triv) apply assumption apply (subgoal_tac "la \<le> XXX", assumption, simp) apply simp
  apply clarsimp
  apply (drule AL_update3, simp)
  apply (drule AL_update3, simp)
  apply (rule CACH_IF) 
    apply assumption 
    apply assumption
    apply assumption
    apply (erule CACH_INJECT) 
    apply (subgoal_tac "la+2=2+la", clarsimp) apply (erule CACH_INJECT) apply simp
(*Match*)
apply clarsimp
  apply (erule compileExpr.cases) 
  apply simp apply simp apply simp
  apply clarsimp
  apply (erule_tac x=lNil in allE, erule_tac x= codeCons in allE, 
         erule_tac x=codeNil in allE, rotate_tac -1) 
  apply (erule_tac x=lRes in allE, clarsimp)
  apply (erule_tac x=G in allE, rotate_tac -1, erule_tac x=C in allE,
         erule_tac x=m in allE, clarsimp)
  apply (erule_tac x="la+9" in allE, erule_tac x=codea in allE, 
         erule_tac x=codeCons in allE, rotate_tac -1) 
  apply (erule_tac x=lNil in allE, clarsimp)
  apply (erule_tac x=G in allE, rotate_tac -1, erule_tac x=C in allE,
         erule_tac x=m in allE, clarsimp)
  apply (drule compileExpr_Prop1) apply fastforce apply clarsimp 
  apply (drule compileExpr_Prop1) apply fastforce apply clarsimp 
  apply (erule impE) apply (rotate_tac 5, erule thin_rl)
    apply (simp add: Segment_def, clarsimp)
    apply (erule_tac x=ll in allE, clarsimp)
    apply (erule_tac x=ll in allE, clarsimp)
    apply (erule_tac x=ll in allE, clarsimp)
    apply (erule_tac x=ll in allE, clarsimp)
    apply (erule_tac x=ll in allE, clarsimp)
    apply (drule AL_update3, simp)
    apply (drule AL_update3, simp)
    apply (drule AL_update3, simp)
    apply (drule AL_update3, simp)
    apply (drule AL_update3, simp)
    apply (drule AL_update3, simp)
    apply (drule AL_update3, simp)
    apply (drule AL_update3, simp)
    apply (drule AL_update3, simp) apply clarsimp
  apply (erule impE) 
    apply (simp add: Segment_def, clarsimp)
    apply (erule_tac x=ll in allE, clarsimp)
    apply (erule_tac x=ll in allE, clarsimp)
    apply (erule_tac x=ll in allE, clarsimp)
    apply (erule_tac x=ll in allE, clarsimp)
    apply (erule_tac x=ll in allE, clarsimp)
    apply (drule AL_update3, simp)
    apply (drule AL_update3, simp)
    apply (drule AL_update3, simp)
    apply (drule AL_update3, simp)
    apply (drule AL_update3, simp)
    apply (drule AL_update3, simp)
    apply (drule AL_update3, simp)
    apply (drule AL_update3, simp)
    apply (drule AL_update3, simp) apply clarsimp
  apply (rule Basic_Sound) prefer 2 apply assumption prefer 4 apply simp prefer 2 apply (subgoal_tac "la \<le> la", assumption, simp)
    apply (erule Segment_A) apply simp apply simp apply simp
    apply (rule AL_update5) 
    apply (rule AL_update5) 
    apply (rule AL_update5) 
    apply (rule AL_update5) 
    apply (rule AL_update5) 
    apply (rule AL_update5) 
    apply (rule AL_update5) 
    apply (rule AL_update5) 
    apply (simp add: AL_update1)  apply (simp, simp, simp) apply (simp, simp, simp)  apply (simp, simp)
    apply (simp add: basic_def)
    apply (rule CACH_INJECT)
  apply (rule Basic_Sound) prefer 2 apply assumption prefer 4 apply simp prefer 2 apply (subgoal_tac "la +1 \<le> la+1", assumption, simp)
    apply (erule Segment_A) apply simp apply simp apply simp
    apply (rule AL_update5) 
    apply (rule AL_update5) 
    apply (rule AL_update5) 
    apply (rule AL_update5) 
    apply (rule AL_update5) 
    apply (rule AL_update5) 
    apply (rule AL_update5)
    apply (simp add: AL_update1)  apply (simp, simp, simp) apply (simp, simp, simp)  apply simp
    apply (simp add: basic_def)
    apply (rule CACH_INJECT)
  apply (frule Segment_triv) apply assumption apply (subgoal_tac "la \<le> lNil", assumption, simp, simp)
  apply (frule Segment_triv) apply assumption apply (subgoal_tac "la \<le> la+3", assumption, simp, simp)
  apply clarsimp
    apply (drule AL_update3, simp)
    apply (drule AL_update3, simp)
    apply (drule AL_update3, simp)
    apply (drule AL_update3, simp)
    apply (drule AL_update3, simp)
    apply (drule AL_update3, simp)
    apply (drule AL_update3, simp)
    apply (drule AL_update3, simp)
    apply (drule AL_update3, simp)
    apply (drule AL_update3, simp)
    apply (subgoal_tac "la+3=3+la", clarsimp) prefer 2 apply simp
    apply (simp add: AL_update1) apply clarsimp
    apply (drule AL_update3, simp)
    apply (drule AL_update3, simp)
    apply (drule AL_update3, simp)
    apply (drule AL_update3, simp)
    apply (frule Segment_triv) apply assumption apply (subgoal_tac "la \<le> 2+la", assumption, simp, simp,clarsimp)
    apply (drule AL_update3, simp)
    apply (drule AL_update3, simp)
    apply (drule AL_update3, simp)
    apply (drule AL_update3, simp)
    apply (drule AL_update3, simp)
    apply (drule AL_update3, simp)
    apply (simp add: AL_update1a, clarsimp)    
    apply (rule CACH_IF)
      apply assumption
      apply assumption
      apply assumption
      apply (erule CACH_INJECT)
    apply simp
    apply (rule CACH_INJECT)
    apply (rule Basic_Sound)
      prefer 2 apply assumption
      prefer 2 apply (subgoal_tac "3+la \<le> 3+la", assumption, simp)
      apply (erule Segment_A) apply (simp,simp)
      apply simp
      apply simp 
      apply (rule AL_update5) 
      apply (rule AL_update5) 
      apply (rule AL_update5) 
      apply (rule AL_update5) 
      apply (rule AL_update5) 
      apply (simp add: AL_update1) 
      apply (simp,simp,simp)
      apply (simp,simp)
      apply (simp add: basic_def)
    apply (rule CACH_INJECT)
    apply (rule Basic_Sound)
      prefer 2 apply assumption 
      prefer 2 apply (subgoal_tac "4+la \<le> 4+la", assumption, simp)
      apply (erule Segment_A) apply (simp,simp)
      apply simp
      apply simp 
      apply (rule AL_update5) 
      apply (rule AL_update5) 
      apply (rule AL_update5) 
      apply (rule AL_update5) 
      apply (rule AL_update1a) apply simp
      apply (simp,simp,simp)
      apply simp
      apply (simp add: basic_def)
      apply (rule CACH_INJECT)
    apply (rule Basic_Sound)
      prefer 2 apply assumption
      prefer 2 apply (subgoal_tac "5+la \<le> 5+la", assumption, simp)
      apply (erule Segment_A) apply (simp,simp)
      apply simp
      apply simp 
      apply (rule AL_update5) 
      apply (rule AL_update5) 
      apply (rule AL_update5) 
      apply (rule AL_update1a) apply simp
      apply (simp,simp,simp)
      apply (simp add: basic_def)
      apply (rule CACH_INJECT)
    apply (rule Basic_Sound)
      prefer 2 apply assumption
      prefer 2 apply (subgoal_tac "6+la \<le> 6+la", assumption, simp)
      apply (erule Segment_A) apply (simp,simp)
      apply simp
      apply simp 
      apply (rule AL_update5) 
      apply (rule AL_update5) 
      apply (rule AL_update1a) apply simp
      apply (simp,simp)
      apply (simp add: basic_def)
      apply (rule CACH_INJECT)
    apply (rule Basic_Sound)
      prefer 2 apply assumption
      prefer 2 apply (subgoal_tac "7+la \<le> 7+la", assumption, simp)
      apply (erule Segment_A) apply (simp,simp)
      apply simp
      apply simp 
      apply (rule AL_update5)
      apply (rule AL_update1a) apply simp
      apply simp
      apply (simp add: basic_def)
      apply (rule CACH_INJECT)
    apply (rule Basic_Sound)
      prefer 2 apply assumption
      prefer 2 apply (subgoal_tac "8+la \<le> 8+la", assumption, simp)
      apply (erule Segment_A) apply (simp,simp)
      apply simp
      apply simp 
      apply (rule AL_update1a) apply simp
      apply (simp add: basic_def)
    apply (rule CACH_INJECT) apply (subgoal_tac "la+9=9+la", clarsimp)
    apply simp
done
(*>*)

text\<open>The full translation of a functional program into a bytecode
program is defined as follows.\<close>

definition compileProg::"FunProg \<Rightarrow> bool" where
"compileProg F =
  ((\<forall> C m par e. F\<down>(C,m) = Some(par,e) \<longrightarrow> 
          (\<exists> code l0 l. mbody_is C m (rev par,code,l0) \<and>
                       (l0,[],e,(code,l)):compileExpr)) \<and>
   (\<forall> C m. (\<exists> M. mbody_is C m M) = (\<exists> fdecl . F\<down>(C,m) = Some fdecl)))"

text\<open>The final condition relating a typing context to a method
specification table.\<close>

definition TP_MST::"TP_Sig \<Rightarrow> bool" where
"TP_MST \<Sigma> =
   (\<forall> C m . case (MST\<down>(C,m)) of
            None \<Rightarrow> \<Sigma>\<down>(C,m) = None
          | Some(T,MI,Anno) \<Rightarrow> Anno = emp \<and> 
                                (\<exists> n . \<Sigma>\<down>(C,m)=Some n \<and> 
                                (T,MI,Anno) = mkSPEC (Cachera n) emp))"

text\<open>For well-typed programs, this property implies the earlier
condition on signatures.\<close>

lemma translation_good: "\<lbrakk>compileProg F; TP_MST \<Sigma>; TP \<Sigma> F\<rbrakk> \<Longrightarrow> Sig_good \<Sigma>"
(*<*)
apply (simp add: compileProg_def TP_MST_def Sig_good_def TP_def, clarsimp)
apply (erule_tac x=C in allE, erule_tac x=m in allE)
apply (erule_tac x=C in allE, erule_tac x=m in allE)
apply (erule_tac x=C in allE, erule_tac x=m in allE)
apply (erule_tac x=C in allE, erule_tac x=m in allE)
apply (erule_tac x=C in allE, erule_tac x=m in allE)
apply (case_tac "MST\<down>(C,m)", clarsimp,clarsimp)
done
(*>*)

text\<open>We can thus prove that well-typed function bodies satisfy the
specifications asserted by the typing context.\<close>

lemma CACH_BodiesDerivable[rule_format]:
  "\<lbrakk> mbody_is C m (par, code, l); compileProg F; TP_MST \<Sigma>; TP \<Sigma> F\<rbrakk> 
  \<Longrightarrow> \<exists> n . MST\<down>(C,m) = Some(mkSPEC(Cachera n) emp) \<and> 
            deriv [] C m l (Cachera n)"
(*<*)
apply (subgoal_tac "(\<forall> C m par e. F\<down>(C,m) = Some(par,e) \<longrightarrow> 
                     (\<exists> code l0 l. mbody_is C m (rev par,code,l0) \<and>
                                   (l0,[],e,(code,l)):compileExpr)) \<and>
                 (\<forall> C m . (\<exists> M. mbody_is C m M) = (\<exists> fdecl . F\<down>(C,m) = Some fdecl))")
prefer 2 apply (simp add: compileProg_def, clarsimp)
apply (erule_tac x=C in allE, erule_tac x=m in allE)
apply (erule_tac x=C in allE, erule_tac x=m in allE, auto)
apply (simp add: mbody_is_def, clarsimp)
apply (subgoal_tac "((\<Sigma>\<down>(C,m) = None) = (F\<down>(C,m) = None)) \<and> 
                       (\<forall> n par e . \<Sigma>\<down>(C,m) = Some n \<longrightarrow> F\<down>(C,m) = Some (par,e) \<longrightarrow> (\<Sigma>,e,n):TP_expr)")
prefer 2 apply (simp add: TP_def, clarsimp)
apply (subgoal_tac "MST\<down>(C, m) = Some (mkSPEC (Cachera y) emp)", clarsimp)
prefer 2 apply (simp add: TP_MST_def) 
  apply (erule_tac x=C in allE, erule_tac x=m in allE)
  apply (case_tac "MST\<down>(C, m)", clarsimp, clarsimp)
apply (rule_tac x=y in exI, simp)
apply (rule TP_epxr_Sound) apply assumption 
  apply (erule translation_good) apply assumption+
  apply (simp add: mkSPEC_def Cachera_def)

apply (drule compileExpr_Prop1) apply fastforce apply clarsimp
apply (simp add: Segment_def) 
apply (rule, rule, rule, rule, simp add: mkSPEC_def Cachera_def)
apply clarsimp apply (rule, rule AL_emp1) 
apply (erule_tac x=ll in allE)+ 
apply clarsimp 
apply (simp add: mbody_is_def get_ins_def ins_is_def) 
done
(*>*)

text\<open>From this, the overall soundness result follows easily.\<close>

theorem CACH_VERIFIED: "\<lbrakk>TP \<Sigma> F; TP_MST \<Sigma>; compileProg F\<rbrakk> \<Longrightarrow> VP"
(*<*)
apply (rule CACH_VP)
apply clarsimp apply (drule CACH_BodiesDerivable) apply assumption+ apply fast
apply clarsimp
done
(*>*)

(*<*)
end
(*>*)
