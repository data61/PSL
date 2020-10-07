(*File: Logic.thy
  Author: L Beringer & M Hofmann, LMU Munich
  Date: 05/12/2008
  Purpose: Definition of axiomatic semantics, with strong
           invariants, pre- and postconditions, and local assertions.
*)
(*<*)
theory Logic imports Language begin
(*>*)

section\<open>Axiomatic semantics\<close>

subsection\<open>Assertion forms\<close>

text\<open>We introduce two further kinds of states. Initial states do not
contain operand stacks, terminal states lack operand stacks and local
variables, but include return values.\<close>

type_synonym InitState = "Store \<times> Heap"
type_synonym TermState = "Heap \<times> Val"

text\<open>A judgements relating to a specific program point $C.m.l$
consists of pre- and post-conditions, an invariant, and
-- optionally -- a local annotation. Local pre-conditions and
annotations relate initial states to states,
i.e.~are of type\<close>

type_synonym Assn = "InitState \<Rightarrow> State \<Rightarrow> bool"

text\<open>Post-conditions additionally depend on a terminal state\<close>

type_synonym Post = "InitState \<Rightarrow> State \<Rightarrow> TermState \<Rightarrow> bool"

text\<open>Invariants hold for the heap components of all future
(reachable) states in the current frame as well as its subframes. They
relate these heaps to the current state and the initial state of the
current frame.\<close>

type_synonym Inv = "InitState \<Rightarrow> State \<Rightarrow> Heap \<Rightarrow> bool"

text\<open>Local annotations of a method implementation are collected in a
table of type\<close>

type_synonym ANNO = "(Label, Assn) AssList"

text\<open>Implicitly, the labels are always interpreted with respect to
the current method. In addition to such a table, the behaviour of
methods is specified by a partial-correctness assertion of type\<close>

type_synonym MethSpec = "InitState \<Rightarrow> TermState \<Rightarrow> bool"

text\<open>and a method invariant of type\<close>

type_synonym MethInv = "InitState \<Rightarrow> Heap \<Rightarrow> bool"

text\<open>A method invariant is expected to be satisfied by the heap
components of all states during the execution of the method, including
states in subframes, irrespectively of the termination behaviour.\<close>

text\<open>All method specifications are collected in a table of type\<close>

type_synonym MSPEC = "(Class \<times> Method, MethSpec \<times> MethInv \<times> ANNO) AssList"

text\<open>A table of this type assigns to each method a
partial-correctness specification, a method invariant, and a table of
local annotations for the instructions in this method.\<close>

subsection\<open>Proof system \label{SectionSPJudgementProofSystem}\<close> 

text\<open>The proof system derives judgements of the form $G \rhd \lbrace
A \rbrace C,m,l \lbrace B \rbrace\; I$ where $A$ is a pre-condition,
$B$ is a post-condition, $I$ is a strong invariant, $C.m.l$ represents
a program point, and $G$ is a proof context (see below). The proof
system consists of syntax-directed rules and structural rules. These
rules are formulated in such a way that assertions in the conclusions
are unconstrained, i.e.~a rule can be directly applied to derive a
judgement. In the case of the syntax-directed rules, the hypotheses
require the derivation of related statements for the control flow
successor instructions. Judgements occurring as hypotheses involve
assertions that are notationally constrained, and relate to the
conclusions' assertions via uniform constructions that resemble
strongest postconditions in Hoare-style logics.\<close>

text\<open>On pre-conditions, the operator\<close>

definition SP_pre::"Mbody \<Rightarrow> Label \<Rightarrow> Assn \<Rightarrow> Assn"
where "SP_pre M l A = (\<lambda> s0 r . (\<exists> s l1 n. A s0 s \<and> (M,l,s,n,l1,r):Step))"

text\<open>constructs an assertion that holds of a state $r$ precisely if
the argument assertion $A$ held at the predecessor state of
$r$. Similar readings explain the constructions on post-conditions\<close>

definition SP_post::"Mbody \<Rightarrow> Label \<Rightarrow> Post \<Rightarrow> Post"
where "SP_post M l B = (\<lambda> s0 r t . (\<forall> s l1 n. (M,l,s,n,l1,r):Step \<longrightarrow> B s0 s t))"

text\<open>and invariants\<close>

definition SP_inv::"Mbody \<Rightarrow> Label \<Rightarrow> Inv \<Rightarrow> Inv"
where "SP_inv M l I = (\<lambda> s0 r h . \<forall> s l1 n. (M,l,s,n,l1,r):Step \<longrightarrow> I s0 s h)"

text\<open>For the basic instructions, the appearance of the single-step
execution relation in these constructions makes the
strongest-postcondition interpretation apparent, but could easily be
eliminated by unfolding the definition of \<open>Step\<close>. In the proof
rule for static method invocations, such a direct reference to the
operational semantics is clearly undesirable. Instead, the proof rule
extracts the invoked method's specification from the specification
table. In order to simplify the formulation of the proof rule, we
introduce three operators which manipulate the extracted assertions in
a similar way as the above \<open>SP\<close>-operators.\<close>

definition SINV_pre::"Var list \<Rightarrow> MethSpec \<Rightarrow> Assn \<Rightarrow> Assn" where
"SINV_pre par T A =
  (\<lambda> s0 s . (\<exists> ops1 ops2 S R h k w. 
               (ops1,par,R,ops2) : Frame \<and> T (R, k) (h,w) \<and> 
               A s0 (ops1,S,k) \<and> s = (w#ops2,S, h)))"

definition SINV_post::"Var list \<Rightarrow> MethSpec \<Rightarrow> Post \<Rightarrow> Post" where
"SINV_post par T B =
  (\<lambda> s0 s t . \<forall> ops1 ops2 S R h k w r.
               (ops1,par,R,ops2) : Frame \<longrightarrow> T (R, k) (h,w) \<longrightarrow> 
               s=(w#ops2,S,h) \<longrightarrow> r=(ops1,S,k) \<longrightarrow> B s0 r t)"

definition SINV_inv::"Var list \<Rightarrow> MethSpec \<Rightarrow> Inv \<Rightarrow> Inv" where
"SINV_inv par T I =
  (\<lambda> s0 s h' . \<forall> ops1 ops2 S R h k w.
                (ops1,par,R,ops2) : Frame \<longrightarrow> T (R,k) (h,w) \<longrightarrow> 
                s=(w#ops2,S,h) \<longrightarrow> I s0 (ops1,S,k) h')"

text\<open>The derivation system is formulated using contexts $G$ of
proof-theoretic assumptions representing local judgements. The type of
contexts is\<close>

type_synonym CTXT = "(Class \<times> Method \<times> Label, Assn \<times> Post \<times> Inv) AssList"

text\<open>The existence of the proof context also motivates that the
hypotheses in the syntax-directed rules are formulated using an
auxiliary judgement form, $G \rhd \langle A \rangle C,m,l \langle B
\rangle\; I$. Statements for this auxiliary form can be derived by
essentially two rules. The first rule, \<open>AX\<close>, allows us to
extract assumptions from the context, while the second rule, \<open>INJECT\<close>, converts an ordinary judgement $G \rhd \lbrace A \rbrace C,m,l
\lbrace B \rbrace\; I$ into $G \rhd \langle A \rangle C,m,l \langle B
\rangle\; I$. No rule is provided for a direct embedding in the
opposite direction. As a consequence of this formulation, contextual
assumptions cannot be used directly to justify a statement $G \rhd
\lbrace A \rbrace C,m,l \lbrace B \rbrace\; I$. Instead, the
extraction of such an assumption has to be followed by at least one
''proper'' (syntax-driven) rule. In particular, attempts to verify
jumps by assuming a judgement and immediately using it to prove the
rule's hypothesis are ruled out.  More specifically, the purpose of
this technical device will become obvious when we discharge the
context in the proof of soundness (Section
\ref{SectionContextElimination}). Here, each entry
$((C',m',l'),(A',B',I'))$ of the context will need to be justified by
a derivation $G \rhd \lbrace A' \rbrace C',m',l' \lbrace B' \rbrace\;
I'$. This justification should in principle be allowed to rely on
other entries of the context. However, an axiom rule for judgements
$G \rhd \lbrace A \rbrace C,m,l \lbrace B \rbrace\; I$ would allow a
trivial discharge of any context entry. The introduction of the
auxiliary judgement form $G \rhd \langle A \rangle C,m,l \langle B
\rangle\; I$ thus ensures that the discharge of a contextual
assumption involves at least one application of a "proper"
(i.e.~syntax-directed) rule. Rule \<open>INJECT\<close> is used to chain
together syntax-directed rules. Indeed, it allows us to discharge a
hypothesis $G \rhd \langle A \rangle C,m,l \langle B \rangle\; I$ of a
syntax-directed rule using a derivation of $G \rhd \lbrace A \rbrace
C,m,l \lbrace B \rbrace\; I$.\<close>

text\<open>The proof rules are defined relative to a fixed method
specification table $\mathit{MST}$.\<close>

axiomatization MST::MSPEC

text\<open>In Isabelle, the distinction between the two judgement forms may
for example be achieved by introducing a single judgement form that
includes a boolean flag, and definiing two pretty-printing notions.\<close>

inductive_set SP_Judgement ::
  "(bool \<times> CTXT \<times> Class \<times> Method \<times> Label \<times> Assn \<times> Post \<times> Inv) set"
and
 SP_Deriv :: "CTXT => Assn => Class => Method => Label => 
              Post => Inv => bool"
  ("_ \<rhd> \<lbrace> _ \<rbrace> _,_,_ \<lbrace> _ \<rbrace> _" [100,100,100,100,100,100,100] 50)
and
 SP_Assum :: "CTXT => Assn => Class => Method => Label => 
              Post => Inv => bool"
   ("_ \<rhd> \<langle> _ \<rangle> _,_,_ \<langle> _ \<rangle> _" [100,100,100,100,100,100,100] 50)
where
 "G \<rhd> \<lbrace> A \<rbrace> C,m,l \<lbrace> B \<rbrace> I == (False, G, C, m, l, A, B, I):SP_Judgement"
|
 "G \<rhd> \<langle> A \<rangle> C,m,l \<langle> B \<rangle> I == (True, G, C, m, l, A, B, I):SP_Judgement"
|
INSTR: 
 "\<lbrakk> mbody_is C m M; get_ins M l = Some ins; 
    lookup MST (C,m) = Some (Mspec,Minv,Anno);
    \<forall> Q . lookup Anno l = Some Q \<longrightarrow> (\<forall> s0 s . A s0 s \<longrightarrow> Q s0 s);
    \<forall> s0 s . A s0 s \<longrightarrow> I s0 s (heap s);
    ins \<in> { const c, dup, pop, swap, load x, store x, binop f, unop g,
            new d, getfield d F, putfield d F, checkcast d}; 
    G \<rhd> \<langle> (SP_pre M l A) \<rangle> C,m,(l+1) \<langle> (SP_post M l B) \<rangle> (SP_inv M l I) \<rbrakk>
 \<Longrightarrow> G \<rhd> \<lbrace> A \<rbrace> C,m,l \<lbrace> B \<rbrace> I"
|
GOTO:
 "\<lbrakk> mbody_is C m M; get_ins M l = Some (goto pc); 
    MST\<down>(C,m) = Some (Mspec,Minv,Anno);
    \<forall> Q . Anno\<down>(l) = Some Q \<longrightarrow> (\<forall> s0 s . A s0 s \<longrightarrow> Q s0 s);
    \<forall> s0 s . A s0 s \<longrightarrow> I s0 s (heap s);
    G \<rhd> \<langle>SP_pre M l A\<rangle> C,m,pc \<langle>SP_post M l B\<rangle> (SP_inv M l I)\<rbrakk>
 \<Longrightarrow> G \<rhd> \<lbrace> A \<rbrace> C,m,l \<lbrace> B \<rbrace> I"
|
IF:
 "\<lbrakk> mbody_is C m M; get_ins M l = Some (iftrue pc);
    MST\<down>(C,m) = Some (Mspec,Minv,Anno);
    \<forall> Q . Anno\<down>(l) = Some Q \<longrightarrow> (\<forall> s0 s . A s0 s \<longrightarrow> Q s0 s);
    \<forall> s0 s . A s0 s \<longrightarrow> I s0 s (heap s);

    G \<rhd> \<langle> SP_pre M l (\<lambda> s0 s . (\<forall> ops S k . s=(TRUE#ops,S,k) \<longrightarrow> A s0 s))\<rangle>
        C,m,pc 
        \<langle> SP_post M l (\<lambda> s0 s t .
           (\<forall> ops S k . s=(TRUE#ops,S,k) \<longrightarrow> B s0 s t))\<rangle> 
        ( SP_inv M l (\<lambda> s0 s t .
           (\<forall> ops S k . s=(TRUE#ops,S,k) \<longrightarrow> I s0 s t)) );

    G \<rhd> \<langle> SP_pre M l (\<lambda> s0 s . 
           (\<forall> ops S k v . s = (v#ops,S,k) \<longrightarrow> v \<noteq> TRUE \<longrightarrow> A s0 s))\<rangle>
         C,m,(l+1)
         \<langle> SP_post M l (\<lambda> s0 s t.  
           (\<forall> ops S k v . s = (v#ops,S,k) \<longrightarrow> v \<noteq> TRUE \<longrightarrow> B s0 s t))\<rangle>
         ( SP_inv M l (\<lambda> s0 s t.  
           (\<forall> ops S k v . s = (v#ops,S,k) \<longrightarrow> v \<noteq> TRUE \<longrightarrow> I s0 s t)) )\<rbrakk> 
 \<Longrightarrow> G \<rhd> \<lbrace> A \<rbrace> C,m,l \<lbrace> B \<rbrace> I"
|
VRET:
 "\<lbrakk> mbody_is C m M; get_ins M l = Some vreturn;
    MST\<down>(C,m) = Some (Mspec,Minv,Anno);
    \<forall> Q . Anno\<down>(l) = Some Q \<longrightarrow> (\<forall> s0 s . A s0 s \<longrightarrow> Q s0 s);
    \<forall> s0 s . A s0 s \<longrightarrow> I s0 s (heap s);
    \<forall> s0 s . A s0 s \<longrightarrow> (\<forall> v ops S h . s = (v#ops,S,h) \<longrightarrow> B s0 s (h,v))\<rbrakk> 
 \<Longrightarrow> G \<rhd> \<lbrace> A \<rbrace> C,m,l \<lbrace> B \<rbrace> I"
|
INVS:
 "\<lbrakk> mbody_is C m M; get_ins M l = Some (invokeS D m');
    MST\<down>(C,m) = Some (Mspec,Minv,Anno);
    MST\<down>(D,m') = Some (T,MI,Anno2); mbody_is D m' (par,code,l0);
    \<forall> Q . Anno\<down>(l) = Some Q \<longrightarrow> (\<forall> s0 s . A s0 s \<longrightarrow> Q s0 s);
    \<forall> s0 s . A s0 s \<longrightarrow> I s0 s (heap s);
    \<forall> s0 ops1 ops2 S R k t . (ops1,par,R,ops2) : Frame \<longrightarrow> 
           A s0 (ops1,S,k) \<longrightarrow> MI (R,k) t \<longrightarrow> I s0 (ops1,S,k) t;
    G \<rhd> \<langle>SINV_pre par T A\<rangle> C,m,(l+1) \<langle>SINV_post par T B\<rangle> 
        (SINV_inv par T I)\<rbrakk>
 \<Longrightarrow> G \<rhd> \<lbrace> A \<rbrace> C,m,l \<lbrace> B \<rbrace> I"
|
CONSEQ:
 "\<lbrakk> (b,G,C,m,l,AA,BB,II) \<in> SP_Judgement;
    \<forall> s0 s . A s0 s \<longrightarrow> AA s0 s; \<forall> s0 s t . BB s0 s t \<longrightarrow> B s0 s t;
    \<forall> s0 s k. II s0 s k \<longrightarrow> I s0 s k\<rbrakk> 
 \<Longrightarrow> (b,G,C,m,l,A,B,I) \<in> SP_Judgement"
|
INJECT: "\<lbrakk> G \<rhd> \<lbrace> A \<rbrace> C,m,l \<lbrace> B \<rbrace> I\<rbrakk> \<Longrightarrow> G \<rhd> \<langle> A \<rangle> C,m,l \<langle> B \<rangle> I"
|
AX:
 "\<lbrakk> G\<down>(C,m,l) = Some (A,B,I); MST\<down>(C,m) = Some (Mspec,Minv,Anno);
    \<forall> Q . Anno\<down>(l) = Some Q \<longrightarrow> (\<forall> s0 s . A s0 s \<longrightarrow> Q s0 s);
    \<forall> s0 s . A s0 s \<longrightarrow> I s0 s (heap s)\<rbrakk> 
 \<Longrightarrow> G \<rhd> \<langle> A \<rangle> C,m,l \<langle> B \<rangle> I"

text\<open>As a first consequence, we can prove by induction on the proof
system that a derivable judgement entails its strong invariant and an
annotation that may be attached to the instruction.\<close>

(*<*)
lemma AssertionsImplyInvariantsAux[rule_format]:
"G \<rhd> \<lbrace> A \<rbrace> C,m,l \<lbrace> B \<rbrace> I \<Longrightarrow> 
  ((\<forall> s0 s t. A s0 s \<longrightarrow> I s0 s (heap s)) \<and>
   (\<forall> Mspec Minv Anno .
        MST\<down>(C,m) = Some (Mspec,Minv,Anno) \<longrightarrow>
        (\<forall> Q . Anno\<down>(l) = Some Q \<longrightarrow> 
               (\<forall> s0 s . A s0 s \<longrightarrow> Q s0 s))))"
apply (erule SP_Judgement.induct)
apply clarsimp
apply clarsimp
apply clarsimp
apply clarsimp
apply clarsimp
apply clarsimp
apply clarsimp (*fast*) 
apply clarsimp (*fast*)
done
(*>*)
lemma AssertionsImplyMethInvariants:
 "\<lbrakk> G \<rhd> \<lbrace> A \<rbrace> C,m,l \<lbrace> B \<rbrace> I; A s0 s\<rbrakk> \<Longrightarrow> I s0 s (heap s)"
(*<*)
by (drule AssertionsImplyInvariantsAux, fast)
(*>*)

lemma AssertionsImplyAnnoInvariants:
 "\<lbrakk> G \<rhd> \<lbrace> A \<rbrace> C,m,l \<lbrace> B \<rbrace> I; MST\<down>(C,m) = Some(Mspec,Minv,Anno);
    Anno\<down>(l) = Some Q; A s0 s\<rbrakk> \<Longrightarrow> Q s0 s"
(*<*)
by (drule AssertionsImplyInvariantsAux, fast) 
(*>*)

text\<open>For \emph{verified} \emph{programs}, all preconditions can be
justified by proof derivations, and initial labels of all methods
(again provably) satisfy the method preconditions.\<close>

definition mkState::"InitState \<Rightarrow> State"
where "mkState s0 = ([],fst s0,snd s0)"

definition mkPost::"MethSpec \<Rightarrow> Post"
where "mkPost T = (\<lambda> s0 s t . s=mkState s0 \<longrightarrow> T s0 t)"

definition mkInv::"MethInv \<Rightarrow> Inv"
where "mkInv MI = (\<lambda> s0 s t . s=mkState s0 \<longrightarrow> MI s0 t)"

definition VP_G::"CTXT \<Rightarrow> bool" where
"VP_G G =
  ((\<forall> C m l A B I. G\<down>(C,m,l) = Some (A,B,I) \<longrightarrow> G \<rhd> \<lbrace>A\<rbrace> C,m,l \<lbrace>B\<rbrace> I) \<and>
  (\<forall> C m par code l0 T MI Anno. 
      mbody_is C m (par,code,l0) \<longrightarrow> MST\<down>(C,m) = Some(T,MI,Anno) \<longrightarrow> 
      G \<rhd> \<lbrace>(\<lambda> s0 s. s = mkState s0)\<rbrace> C,m,l0 \<lbrace>mkPost T\<rbrace> (mkInv MI)))"

definition VP::bool where "VP = (\<exists> G . VP_G G)"

(*<*)
end
(*>*)
