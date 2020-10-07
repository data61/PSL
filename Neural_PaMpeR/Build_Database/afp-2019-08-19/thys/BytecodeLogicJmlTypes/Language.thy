(*File: Language.thy
  Author: L Beringer & M Hofmann, LMU Munich
  Date: 05/12/2008
  Purpose: Syntax and operational semantics of subset of JVML 
*)
(*<*)
theory Language imports AssocLists begin
(*>*)

section\<open>Language \label{sec:language}\<close>
subsection\<open>Syntax\<close>

text\<open>We have syntactic classes of (local) variables, class names,
field names, and method names. Naming restrictions, namespaces, long
Java names etc.~are not modelled.\<close>

typedecl Var
typedecl Class
typedecl Field
typedecl Method

text\<open>Since arithmetic operations are modelled as unimplemented
functions, we introduce the type of values in this section. The domain
of heap locations is arbitrary.\<close>

typedecl Addr 

text\<open>A reference is either null or an address.\<close>

datatype Ref = Nullref | Loc Addr

text\<open>Values are either integer numbers or references.\<close>

datatype Val = RVal Ref | IVal int

text\<open>The type of (instruction) labels is fixed, since the operational
semantics increments the program counter after each instruction.\<close>

type_synonym Label = int

text\<open>Regarding the instructions, we support basic operand-stack
manipulations, object creation, field modifications, casts, static
method invocations, conditional and unconditional jumps, and a return
instruction.

For every (Isabelle) function \<open>f : Val\<Rightarrow>Val\<Rightarrow>Val\<close> we have an
instruction \<open>binop f\<close> whose semantics is to invoke \<open>f\<close>
on the two topmost values on the operand stack and replace them with
the result.  Similarly for \<open>unop f\<close>.\<close>

datatype Instr =
  const Val
| dup
| pop
| swap
| load Var
| store Var
| binop "Val \<Rightarrow> Val \<Rightarrow> Val"
| unop "Val \<Rightarrow> Val" 
| new Class
| getfield Class Field
| putfield Class Field
| checkcast Class
| invokeS Class Method
| goto Label
| iftrue Label
| vreturn 

text\<open>Method body declarations contain a list of formal parameters, a
mapping from instruction labels to instructions, and a start
label. The operational semantics assumes that instructions are
labelled consecutively\footnote{In the paper, we slightly abstract
from this by including a successor functions on labels}.\<close>

type_synonym Mbody = "Var list \<times> (Label, Instr) AssList \<times> Label" 

text\<open>A class definition associates method bodies to method names.\<close>
type_synonym Classdef = "(Method, Mbody) AssList"

text\<open>Finally, a program consists of classes.\<close>
type_synonym Prog = "(Class, Classdef) AssList"

text\<open>Taken together, the three types \<open>Prog\<close>, \<open>Classdef\<close>,
and \<open>Mbody\<close> represent an abstract model of the virtual machine
environment. In our opinion, it would be desirable to avoid modelling
this environment at a finer level, at least for the purpose of the
program logic. For example, we prefer not to consider in detail the
representation of the constant pool.\<close>

subsection\<open>Dynamic semantics\<close>
subsubsection\<open>Semantic components\<close>

text\<open>An object consists of the identifier of its dynamic class and a
map from field names to values. Currently, we do not model
type-correctness, nor do we require that all (or indeed any) of the
fields stem from the static definition of the class, or a super-class.
Note, however, that type correctness can be expressed in the logic.\<close>

type_synonym Object = "Class \<times> (Field, Val) AssList"

text\<open>The heap is represented as a map from addresses to values.  The
JVM specification does not prescribe any particular object layout. The
proposed type reflects this indeterminacy, but allows one to calculate
the byte-correct size of a heap only after a layout scheme has been
supplied. Alternative heap models would be the store-less semantics in
the sense of Jonkers~\cite{Jonkers1981} and
Deutsch~\cite{Deutsch1992}, (where the heap is modelled as a partial
equivalence relation on access paths), or object-based semantics in
the sense of Reddy~\cite{Reddy1996}, where the heap is represented as
a history of update operations.  H\"ahnle et al.~use a variant of the
latter in their dynamic logic for a {\sc
JavaCard}~~\cite{HaehnleM:Cassis2005}.\<close>

type_synonym Heap = "(Addr, Object) AssList"

text\<open>Later, one might extend heaps by a component for static fields.\<close>

text\<open>The types of the (register) store and the operand stack are as
expected.\<close>

type_synonym Store = "(Var, Val) AssList"
type_synonym OpStack = "Val list"

text\<open>States contain an operand stack, a store, and a heap.\<close>
type_synonym State = "OpStack \<times> Store \<times> Heap"

definition heap::"State \<Rightarrow> Heap"
where "heap s = snd(snd s)"

text\<open>The operational semantics and the program logic are defined
relative to a fixed program \<open>P\<close>.  Alternatively, the type of the
operational semantics (and proof judgements) could be extended by a
program component.  We also define the constant value \<open>TRUE\<close>,
the representation of which does not matter for the current
formalisation.\<close>

axiomatization P::Prog and TRUE::Val

text\<open>In order to obtain more readable rules, we define operations
for extracting method bodies and instructions from the program.\<close>

definition mbody_is::"Class \<Rightarrow> Method \<Rightarrow> Mbody \<Rightarrow> bool"
where "mbody_is C m M = (\<exists> CD . P\<down>C = Some CD \<and> CD\<down>m = Some M)"

definition get_ins::"Mbody \<Rightarrow> Label \<Rightarrow> Instr option"
where "get_ins M l = (fst(snd M))\<down>l"

definition ins_is::"Class \<Rightarrow> Method \<Rightarrow> Label \<Rightarrow> Instr \<Rightarrow> bool"
where "ins_is C m l ins = (\<exists> M . mbody_is C m M \<and> get_ins M l = Some ins)"

text\<open>The transfer of method arguments from the caller's operand stack
to the formal parameters of an invoked method is modelled by the
predicate\<close>

inductive_set Frame::"(OpStack \<times> (Var list) \<times> Store \<times> OpStack) set"
where
FrameNil: "\<lbrakk>oo=ops\<rbrakk> \<Longrightarrow> (ops,[],emp,oo) : Frame"
|
Frame_cons: "\<lbrakk>(oo,par,S,ops) : Frame; R =S[x\<mapsto>v]\<rbrakk>
            \<Longrightarrow> (v # oo, x # par,R,ops):Frame"

(*<*)
lemma Frame_deterministic[rule_format]:
"(ops, par, S, os) \<in> Frame \<Longrightarrow> 
(\<forall> R opsa . (ops, par, R, opsa) \<in> Frame \<longrightarrow> R=S \<and> opsa = os)"
apply (erule Frame.induct, clarsimp)
apply (erule Frame.cases, clarsimp, clarsimp)
apply (erule thin_rl, clarsimp)
apply (erule Frame.cases, clarsimp, clarsimp)
done
(*>*)

text\<open>In order to obtain a deterministic semantics, we assume the
existence of a function, with the obvious freshness axiom for this
construction.\<close>

axiomatization nextLoc::"Heap \<Rightarrow> Addr"
where nextLoc_fresh: "h\<down>(nextLoc h) = None"

subsubsection\<open>Operational judgements\<close> 

text\<open>Similar to Bannwart-M\"uller~\cite{BannwartMueller05}, we define
two operational judgements: a one-step relation and a relation that
represents the transitive closure of the former until the end of the
current method invocation. These relations are mutually recursive,
since the method invocation rule contracts the execution of the
invoked method to a single step. The one-step relation associates a
state to its immediate successor state, where the program counter is
interpreted with respect to the current method body. The transitive
closure ignores the bottom part of the operand stack and the store of
the final configuration. It simply returns the heap and the result of
the method invocation, where the latter is given by the topmost value
on the operand stack. In contrast to~\cite{BannwartMueller05}, we do
not use an explicit \<open>return\<close> variable. Both relations take an
additional index of type \<open>nat\<close> that monitors the derivation
height. This is useful in the proof of soundness of the program
logic.\<close>

text\<open>Intuitively, \<open>(M,l,s,n,l',s'):Step\<close> means that method
(body) \<open>M\<close> evolves in one step from state \<open>s\<close> to state
\<open>s'\<close>, while statement \<open>(M,s,n,h,v):Exec\<close> indicates that
executing from \<open>s\<close> in method \<open>M\<close> leads eventually to a
state whose final value is \<open>h\<close>, where precisely the last step in
this sequence is a \<open>vreturn\<close> instruction and the return value is
\<open>v\<close>.\<close>

text\<open>Like Bannwart and M\"uller, we define a "frame-less"
semantics. i.e.~the execution of a method body is modelled by a
transitive closure of the basic step-relation, which results in a
one-step reduction at the invocation site. Arguably, an operational
semantics with an explicit frame stack is closer to the real JVM. It
should not be difficult to verify the operational soundness of the
present system w.r.t.~such a finer model, or to modify the
semantics.\<close>

inductive_set
  Step::"(Mbody \<times> Label \<times> State \<times> nat \<times> Label \<times> State) set"
and
  Exec::"(Mbody \<times> Label \<times> State \<times> nat \<times> Heap \<times> Val) set"
where
Const:"\<lbrakk>get_ins M l = Some (const v); NEXT = (v # os,s,h); ll=l+1\<rbrakk>
       \<Longrightarrow> (M,l,(os,s,h), 1, ll, NEXT) : Step"
|
Dup:  "\<lbrakk>get_ins M l = Some dup; NEXT = (v # v # os,s,h); ll =l+1\<rbrakk>
       \<Longrightarrow> (M,l,(v # os,s,h), 1, ll, NEXT) : Step"
|
Pop:  "\<lbrakk>get_ins M l = Some pop; NEXT = (os,s,h); ll=l+1\<rbrakk>
       \<Longrightarrow> (M,l,(v # os,s,h), 1, ll, NEXT) : Step"
|
Swap: "\<lbrakk>get_ins M l = Some swap; NEXT = (w # (v # os),s,h); ll= l+1\<rbrakk>
       \<Longrightarrow> (M,l,(v # (w # os),s,h), 1, ll, NEXT) : Step"
|
Load: "\<lbrakk>get_ins M l = Some (load x); s\<down>x = Some v;
         NEXT = (v # os,s,h); ll=l+1\<rbrakk>
       \<Longrightarrow> (M,l,(os,s,h), 1, ll,NEXT) : Step"
|
Store:"\<lbrakk>get_ins M l = Some (store x); NEXT = (os,s[x\<mapsto>v],h); ll= l+1\<rbrakk>
       \<Longrightarrow> (M,l,(v # os,s,h), 1, ll, NEXT) : Step"
|
Binop:"\<lbrakk>get_ins M l = Some (binop f); NEXT = ((f v w) # os,s,h); ll=l+1\<rbrakk>
       \<Longrightarrow> (M,l,(v # (w # os),s,h), 1, ll,NEXT) : Step"
|
Unop: "\<lbrakk>get_ins M l = Some (unop f); NEXT = ((f v) # os,s,h);ll=l+1\<rbrakk>
       \<Longrightarrow> (M,l,(v # os,s,h), 1, ll, NEXT) : Step"
|
New:  "\<lbrakk>get_ins M l = Some (new d); newobj = (d, emp); a=nextLoc h; 
         NEXT = ((RVal (Loc a)) # os,s,h[a\<mapsto>newobj]); ll = l+1\<rbrakk>
       \<Longrightarrow> (M,l,(os,s,h), 1, ll,NEXT) : Step"
|
Get:  "\<lbrakk>get_ins M l = Some (getfield d F); h\<down>a = Some (d, Flds);
         Flds\<down>F = Some v; NEXT = (v # os,s,h); ll=l+1\<rbrakk>
       \<Longrightarrow> (M,l,((RVal (Loc a)) # os,s,h), 1, ll,NEXT) : Step"
|
Put:  "\<lbrakk>get_ins M l = Some (putfield d F); h\<down>a = Some (d, Flds);
         newobj = (d, Flds[F\<mapsto>v]); NEXT = (os,s,h[a\<mapsto>newobj]); ll=l+1\<rbrakk>
       \<Longrightarrow> (M,l,(v # ((RVal (Loc a)) # os),s,h), 1, ll, NEXT) : Step"
|
Cast: "\<lbrakk>get_ins M l = Some (checkcast d); h\<down>a = Some (d, Flds);
         NEXT = ((RVal (Loc a)) # os,s,h); ll=l+1\<rbrakk>
       \<Longrightarrow> (M,l,((RVal (Loc a)) # os,s,h), 1, ll,NEXT) : Step"
|
Goto: "\<lbrakk>get_ins M l = Some (goto pc)\<rbrakk> \<Longrightarrow> (M,l,S, 1, pc,S) : Step"
|
IfT:  "\<lbrakk>get_ins M l = Some (iftrue pc); NEXT = (os,s,h)\<rbrakk>
       \<Longrightarrow> (M,l,(TRUE # os,s,h), 1, pc, NEXT) : Step"
|
IfF:  "\<lbrakk>get_ins M l = Some (iftrue pc); v \<noteq> TRUE; NEXT = (os,s,h); ll=l+1\<rbrakk>
       \<Longrightarrow> (M,l,(v # os,s,h), 1, ll, NEXT) : Step"
|
InvS: "\<lbrakk>get_ins M l = Some (invokeS C m); mbody_is C m (par,code,l0);
         ((par,code,l0),l0,([], S,h), n, hh, v): Exec; 
         (ops,par,S,os) : Frame; NEXT = (v # os,s,hh); ll = l+1\<rbrakk>
       \<Longrightarrow> (M,l,(ops,s,h), Suc n, ll, NEXT) : Step"
|
Vret: "\<lbrakk>get_ins M l = Some vreturn\<rbrakk> \<Longrightarrow> (M,l,(v # os,s,h), 1, h, v) : Exec"
|
Run:  "\<lbrakk>(M,l,s,n,ll,t):Step; (M,ll,t,m,h,v):Exec; k = (max n m) +1 \<rbrakk>
       \<Longrightarrow> (M,l,s,k,h,v) : Exec"

text\<open>A big-step operational judgement that abstracts from the
derivation height is easily defined.\<close>

definition Opsem::"Mbody \<Rightarrow> Label \<Rightarrow> State \<Rightarrow> Heap \<Rightarrow> Val \<Rightarrow> bool"
where "Opsem M l s h v = (\<exists> n . (M,l,s,n,h,v):Exec)"

subsection \<open>Basic properties\<close>

text \<open>We provide elimination lemmas for the inductively defined
relations\<close>

inductive_cases eval_cases: 
 "(M,l,s,n,ll,t) : Step"
 "(M,l,s,n,h,v) : Exec"
(*<*)
lemma no_zero_height_derivsAux[rule_format]: 
"\<forall>n . ((M,l,s,n,ll,t) : Step \<longrightarrow> (n=0 \<longrightarrow> False)) \<and> ((MM,lll,ss,m,h,v):Exec \<longrightarrow> (m=0 \<longrightarrow> False))"
by (rule allI, rule Step_Exec.induct, simp_all)

lemma no_zero_height_derivsAux2: "((M,l,s,0,ll,t):Step \<longrightarrow> False) \<and> ((MM,lll,ss,0,h,v):Exec \<longrightarrow> False)"
by (insert no_zero_height_derivsAux, fast)
(*>*)
text \<open>and observe that no derivations of height 0 exist.\<close>
lemma no_zero_height_Step_derivs: "(M,l,s,0,ll,t):Step \<Longrightarrow> False"
(*<*)by (insert no_zero_height_derivsAux2, fast)(*>*)
(*<*)
lemma no_zero_height_Step_derivs1: "(M,l,(os,S,H),0,ll,t):Step \<Longrightarrow> False"
by (insert no_zero_height_derivsAux2, fast)
(*>*)

lemma no_zero_height_Exec_derivs: "(M,l,s,0,h,v):Exec \<Longrightarrow> False"
(*<*)by (insert no_zero_height_derivsAux2, fast)(*>*)
(*<*)
lemma no_zero_height_Exec_derivs1: "(M,l,(os,S,H),0,h,v):Exec \<Longrightarrow> False"
by (insert no_zero_height_derivsAux2, fast)
(*>*)

(*<*)
(*Elimination rules*)
lemma ConstElim1:"\<lbrakk>(M, l, (os, S, h), n, ll,t) \<in> Step; get_ins M l = Some (const v)\<rbrakk> 
               \<Longrightarrow> n = Suc 0 \<and> t = (v # os, S, h) \<and> ll = l+1"
by (erule eval_cases, simp_all)

lemma DupElim1: "\<lbrakk>(M, l, (os, S, h), n, ll, t) \<in> Step; get_ins M l =  Some dup\<rbrakk> 
               \<Longrightarrow> \<exists> v ops . os = v # ops \<and> n = Suc 0 \<and> t = (v # os, S, h) \<and> ll = l+1"
by (erule eval_cases, simp_all)

lemma PopElim1: "\<lbrakk>(M, l, (os, S, h), n, ll, t) \<in> Step; get_ins M l =  Some pop\<rbrakk> 
               \<Longrightarrow> \<exists> v ops . os = v # ops \<and> n = Suc 0 \<and> t = (ops, S, h) \<and> ll = l+1"
by (erule eval_cases, simp_all)

lemma SwapElim1: "\<lbrakk>(M, l, (os, S, h), n, ll, t) \<in> Step; get_ins M l = Some swap\<rbrakk>
              \<Longrightarrow> \<exists> v w ops . os = v # w # ops \<and> n = Suc 0 \<and> t = (w # v # ops, S, h) \<and> ll = l+1"
by (erule eval_cases, simp_all)

lemma LoadElim1: "\<lbrakk>(M, l, (os, S, h), n, ll, t) \<in> Step; get_ins M l = Some (load x)\<rbrakk>
                 \<Longrightarrow> \<exists> v . S\<down>x = Some v \<and> n = Suc 0 \<and> t = (v # os, S, h) \<and> ll = l+1"
by (erule eval_cases, simp_all)

lemma StoreElim1: "\<lbrakk>(M, l, (os, S, h), n, ll, t) \<in> Step; get_ins M l = Some (store x)\<rbrakk>
                  \<Longrightarrow> \<exists> v ops . os = v # ops \<and> n = Suc 0 \<and> t = (ops, S[x\<mapsto>v], h) \<and> ll = l+1"
by (erule eval_cases, simp_all)

lemma BinopElim1: "\<lbrakk>(M, l, (os, S, h), n, ll, t) \<in> Step; get_ins M l = Some (binop f)\<rbrakk>
                  \<Longrightarrow> \<exists> v w ops . os = v # w # ops \<and> n = Suc 0 \<and> t = (f v w # ops, S, h) \<and> ll = l+1"
by (erule eval_cases, simp_all) 

lemma UnopElim1: "\<lbrakk>(M, l, (os, S, h), n, ll, t) \<in> Step; get_ins M l = Some (unop f)\<rbrakk>
                 \<Longrightarrow> \<exists> v ops . os = v # ops \<and> n = Suc 0 \<and> t = (f v # ops, S, h) \<and> ll = l+1"
by (erule eval_cases, simp_all)

lemma NewElim1: "\<lbrakk>(M, l, (os, S, h), n, ll, t) \<in> Step; get_ins M l = Some (new d)\<rbrakk>
               \<Longrightarrow> \<exists> a . a = nextLoc h \<and> n = Suc 0 \<and> t = (RVal (Loc a) # os, S, h[a\<mapsto>(d, emp)]) \<and> ll = l+1"
by (erule eval_cases, simp_all)

lemma GetElim1: "\<lbrakk>(M, l, (os, S, h), n, ll, t) \<in> Step; get_ins M l = Some (getfield d F)\<rbrakk>
               \<Longrightarrow> \<exists> a Flds v ops. h\<down>a = Some (d, Flds) \<and> Flds\<down>F = Some v \<and> 
                                   os = RVal (Loc a) # ops \<and> n = Suc 0 \<and> t = (v # ops, S, h) \<and> ll = l+1"
by (erule eval_cases, simp_all)

lemma PutElim1: "\<lbrakk>(M, l, (os, S, h), n, ll, t) \<in> Step; get_ins M l = Some (putfield d F)\<rbrakk>
                \<Longrightarrow> \<exists> a Flds v ops. h\<down>a = Some (d, Flds) \<and> os = v # RVal (Loc a) # ops \<and>
                                   n = Suc 0 \<and> t = (ops, S, h[a\<mapsto>(d, Flds[F\<mapsto>v])]) \<and> ll = l+1"
by (erule eval_cases, simp_all)

lemma CastElim1: "\<lbrakk>(M, l, (os, S, h), n, ll, t) \<in> Step; get_ins M l = Some (checkcast d)\<rbrakk>
                \<Longrightarrow> \<exists> a Flds ops . h\<down>a = Some (d, Flds) \<and> os = RVal (Loc a) # ops \<and> n = Suc 0 \<and> 
                                   t = (RVal (Loc a) # ops, S, h) \<and> ll = l+1"
by (erule eval_cases, simp_all)

lemma GotoElim1: "\<lbrakk>(M, l, (os, S, h), n, ll, t) \<in> Step; get_ins M l = Some (goto pc)\<rbrakk>
                \<Longrightarrow> n = Suc 0 \<and> t = (os, S, h) \<and> ll = pc"
by (erule eval_cases, simp_all)

lemma IfElim1: "\<lbrakk>(M, l, (os, S, h), n, ll, t) \<in> Step; get_ins M l = Some (iftrue pc)\<rbrakk>
              \<Longrightarrow> (\<exists> ops . os = TRUE # ops \<and> n = Suc 0 \<and> t = (ops, S, h) \<and> ll = pc) \<or> 
                  (\<exists> v ops . v \<noteq> TRUE \<and> os = v # ops \<and> n = Suc 0 \<and> t = (ops, S, h) \<and> ll = l+1)"
by (erule eval_cases, simp_all)

lemma InvokeElim1: "\<lbrakk>(M, l, (os, S, h), n, ll, t) \<in> Step; get_ins M l = Some (invokeS C m)\<rbrakk>
                   \<Longrightarrow> \<exists> code l0 v ops hh u k R par. 
                           mbody_is C m (par,code, l0) \<and> (os,par,R,ops):Frame \<and> 
                           ((par,code,l0), l0, ([], R, h), k, hh, v) \<in> Exec \<and> 
                           n = Suc k \<and> t = (v # ops, S, hh) \<and> ll = l+1"
by (erule eval_cases, simp_all, fastforce)
lemma InvokeElim: "\<lbrakk>(M, l, s, n, ll, t) \<in> Step; get_ins M l = Some (invokeS C m)\<rbrakk>
                   \<Longrightarrow> \<exists> code l0 v ops hh u k R par. 
                           mbody_is C m (par,code, l0) \<and> (fst s,par,R,ops):Frame \<and> 
                           ((par,code,l0), l0, ([], R, snd(snd s)), k, hh, v) \<in> Exec \<and> 
                           n = Suc k \<and> t = (v # ops, fst (snd s), hh) \<and> ll = l+1"
by (erule eval_cases, simp_all, fastforce)

lemma RetElim1: "\<lbrakk>(M, l, (os, S, h), n, ll, t) \<in> Step; get_ins M l = Some (vreturn)\<rbrakk> \<Longrightarrow> False"
by (erule eval_cases, simp_all)

lemma ExecElim1: "\<lbrakk>(M,l,(os,S,H),k,h,v):Exec\<rbrakk>
      \<Longrightarrow> (get_ins M l = Some vreturn \<and> (\<exists> ops . os = v # ops \<and> k = Suc 0 \<and> h=H)) \<or>
          (\<exists> n m t ll. (M, l,(os,S,H), n, ll,t) \<in> Step \<and> (M, ll, t, m, h, v) \<in> Exec \<and> k = Suc (max n m))"
apply (erule eval_cases, simp_all)
apply (rule disjI2)
  apply clarsimp
  apply (rule, rule, rule, rule) apply (rule, rule, rule) apply assumption
  apply (rule, assumption) apply simp
done

lemma InstrElimNext:
 "\<lbrakk>(M, l, s, n, ll, t) \<in> Step;
   get_ins M l = Some I;
   I = const c \<or> I = dup \<or> I = pop \<or> I = swap \<or> I = load x \<or>
   I = store x \<or> I = binop f \<or> I = unop g \<or> I = new d \<or>
   I = getfield d F \<or> I = putfield d F \<or> I = checkcast d\<rbrakk>
  \<Longrightarrow> ll = l+1"
apply (drule eval_cases, simp_all)
apply clarsimp 
apply clarsimp
done
(*>*)

text\<open>By induction on the derivation system one can show
determinism.\<close>

(*<*)
lemma StepExec_determ_Aux[rule_format]:
"(\<forall> n1 l M s l1 t . n1 \<le> n \<longrightarrow> (M, l, s, n1, l1, t) \<in> Step \<longrightarrow>
       (\<forall> n2 l2 r. (M,l,s,n2,l2,r):Step \<longrightarrow> (n1=n2 \<and> t=r \<and> l1=l2))) \<and>
 (\<forall> n1 l M s h v . n1 \<le> n \<longrightarrow> (M, l, s, n1, h, v) \<in> Exec \<longrightarrow>
      (\<forall> n2 k w . (M,l,s,n2,k,w):Exec \<longrightarrow> (n1=n2 \<and> h=k \<and> v=w)))"
apply (induct n)
apply clarsimp apply rule apply clarsimp apply (drule no_zero_height_Step_derivs1, simp)
   apply clarsimp apply (drule no_zero_height_Exec_derivs1, simp)
apply clarsimp
apply rule
  apply clarsimp 
apply (erule Step.cases)
  apply clarsimp apply (drule ConstElim1) apply simp apply clarsimp
  apply clarsimp apply (drule DupElim1) apply simp apply clarsimp
  apply clarsimp apply (drule PopElim1) apply simp apply clarsimp
  apply clarsimp apply (drule SwapElim1) apply simp apply clarsimp
  apply clarsimp apply (drule LoadElim1) apply simp apply clarsimp
  apply clarsimp apply (drule StoreElim1) apply simp apply clarsimp
  apply clarsimp apply (drule BinopElim1) apply simp apply clarsimp
  apply clarsimp apply (drule UnopElim1) apply simp apply clarsimp
  apply clarsimp apply (drule NewElim1) apply simp apply clarsimp
  apply clarsimp apply (drule GetElim1) apply fastforce apply clarsimp
  apply clarsimp apply (drule PutElim1) apply fastforce apply clarsimp
  apply clarsimp apply (drule CastElim1) apply simp apply clarsimp
  apply clarsimp apply (drule GotoElim1) apply simp apply clarsimp
  apply clarsimp apply (drule IfElim1) apply simp apply clarsimp
  apply clarsimp apply (drule IfElim1) apply simp apply clarsimp
  apply clarsimp apply (drule InvokeElim1) apply simp apply clarsimp
    apply (erule thin_rl)
    apply (simp add: mbody_is_def, clarsimp)
    apply (drule Frame_deterministic, assumption, clarsimp)
apply clarsimp
  apply (erule Exec.cases)
  apply clarsimp apply (erule Exec.cases)
    apply clarsimp
    apply clarsimp apply (drule RetElim1, simp, simp)
  apply clarsimp apply (drule ExecElim1)
    apply clarsimp
    apply (erule disjE, clarsimp) apply (drule RetElim1, simp, simp)
    apply clarsimp
      apply (erule_tac x=na in allE, rotate_tac -1, clarsimp)
      apply (erule_tac x=la in allE, rotate_tac -1)
      apply (erule_tac x=ad in allE, rotate_tac -1)
      apply (erule_tac x=ae in allE, rotate_tac -1)
      apply (erule_tac x=bb in allE, rotate_tac -1)
      apply (erule_tac x=af in allE, rotate_tac -1)
      apply (erule_tac x=ag in allE, rotate_tac -1)
      apply (erule_tac x=bc in allE, rotate_tac -1)
      apply (erule_tac x=ll in allE, rotate_tac -1)
      apply (erule_tac x=ah in allE, rotate_tac -1)
      apply (erule_tac x=ai in allE, rotate_tac -1)
      apply (erule_tac x=bd in allE, clarsimp)
      apply (rotate_tac -1)
      apply (erule_tac x=nb in allE, rotate_tac -1) 
      apply (erule_tac x=lla in allE, rotate_tac -1)
      apply (erule_tac x=a in allE, rotate_tac -1)
      apply (erule_tac x=aa in allE, rotate_tac -1)
      apply (erule_tac x=b in allE, clarsimp)
      apply (erule_tac x=m in allE, rotate_tac -1, clarsimp)
      apply (erule_tac x=lla in allE, rotate_tac -1)
      apply (erule_tac x=ad in allE, rotate_tac -1)
      apply (erule_tac x=ae in allE, rotate_tac -1)
      apply (erule_tac x=bb in allE, rotate_tac -1)
      apply (erule_tac x=a in allE, rotate_tac -1)
      apply (erule_tac x=aa in allE, rotate_tac -1)
      apply (erule_tac x=b in allE, rotate_tac -1)
      apply (erule_tac x=ha in allE, rotate_tac -1)
      apply (erule_tac x=va in allE, rotate_tac -1, clarsimp)
done
(*>*)

lemma Step_determ:
 "\<lbrakk>(M,l,s,n,l1,t) \<in> Step; (M,l,s,m,l2,r):Step\<rbrakk> \<Longrightarrow> n=m \<and> t=r \<and> l1=l2"
(*<*)
apply (insert StepExec_determ_Aux[of n])
apply (erule conjE)
apply (rotate_tac -1, erule thin_rl)
apply fast
done
(*>*)

lemma Exec_determ:
 "\<lbrakk>(M,l,s,n,h,v) \<in> Exec; (M,l,s,m,k,w):Exec\<rbrakk> \<Longrightarrow> n=m \<and> h=k \<and> v=w"
(*<*)
apply (insert StepExec_determ_Aux[of n])
apply (erule conjE)
apply (rotate_tac -2, erule thin_rl)
apply fast
done
(*>*)

(*<*)
end
(*>*)
