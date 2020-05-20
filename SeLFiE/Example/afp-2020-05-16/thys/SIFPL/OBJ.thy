(*File: OBJ.thy*)
(*Authors: Lennart Beringer and Martin Hofmann, LMU Munich 2008*)
theory OBJ imports Main begin

section\<open>Base-line non-interference with objects\<close>

text\<open>\label{sec:Objects} We now extend the encoding for base-line
non-interference to a language with objects.  The development follows
the structure of Sections \ref{sec:IMP} to
\ref{sec:BaseLineNI}. Syntax and operational semantics are defined in
Section \ref{sec:ObjLanguage}, the axiomatic semantics in Section
\ref{sec:ObjLogic}. The generalised definition of non-interference is
given in \ref{sec:ObjNI}, the derived proof rules in Section
\ref{sec:ObjDerivedRules}, and a type system in the style of Volpano
et al.~in Section \ref{sec:ObjTypeSystem}. Finally, Section
\ref{sec:contextObj} concludes with results on contextual closure.\<close>

subsection \<open>Syntax and operational semantics\<close>
text\<open>\label{sec:ObjLanguage}\<close>

text\<open>First, some operations for association lists\<close>

primrec lookup :: "('a \<times> 'b) list \<Rightarrow> 'a \<Rightarrow> 'b option"
where
"lookup [] l = None" |
"lookup (h # t) l = (if (fst h)=l then Some (snd h) else lookup t l)" 

definition Dom::"('a \<times> 'b) list \<Rightarrow> 'a set"
where "Dom L = {l . \<exists> a . lookup L l = Some a}"

(*<*)
lemma lookupNoneAppend[rule_format]: 
"\<forall> l L2. (lookup L1 l = None \<longrightarrow> lookup L2 l = None \<longrightarrow> lookup (L1 @ L2) l = None)"
by (induct L1, simp+)

lemma DomAppendUnion[rule_format]: "\<forall> ab. Dom (a @ ab) = Dom a \<union> Dom ab"
apply (induct a)
apply (simp add: Dom_def)
apply (simp add: Dom_def)
apply clarsimp apply fast
done

lemma DomAppend: "Dom L \<subseteq> Dom((a, b) # L)"
by (simp add: Dom_def, auto)

lemma lookupSomeAppend1[rule_format]:
"\<forall> L2 l c . lookup L1 l = Some c \<longrightarrow> lookup (L1 @ L2) l = Some c"
by (induct L1, simp, simp)

lemma DomUnion[rule_format]:"Dom ((a,b) # L) = {a} \<union> Dom L"
by (simp add: Dom_def DomAppendUnion, fast)

lemma lookupSomeAppend2[rule_format]:
"\<forall> l c L2 . lookup L2 l = Some c \<longrightarrow> Dom L1 \<inter> Dom L2 = {} \<longrightarrow> lookup (L1 @ L2) l = Some c"
apply (induct L1)
apply (simp add: Dom_def)
apply clarsimp
  apply rule
    apply clarsimp apply (subgoal_tac "l:Dom L2") apply (simp add: DomUnion) 
   apply (simp add: Dom_def) 
apply clarsimp
  apply (erule_tac x=l in allE)
  apply (erule_tac x=c in allE)
  apply (erule_tac x=L2 in allE)
  apply simp apply (erule impE) apply (simp add: DomUnion) 
  apply simp
done
(*>*)

text\<open>Abstract types of variables, class names, field names, and
locations.\<close>

typedecl Var
typedecl Class
typedecl Field
typedecl Location

text\<open>References are either null or a location. Values are either
integers or references.\<close>

datatype Ref = Nullref | Loc Location

datatype Val = RVal Ref | IVal int 

text\<open>The heap is a finite map from locations to objects. Objects have
a dynamic class and a field map.\<close>

type_synonym Object = "Class \<times> ((Field \<times> Val) list)"
type_synonym Heap = "(Location \<times> Object) list"

text\<open>Stores contain values for all variables, and states are pairs of
stores and heaps.\<close>

type_synonym Store = "Var \<Rightarrow> Val"

definition update :: "Store \<Rightarrow> Var \<Rightarrow> Val \<Rightarrow> Store"
where "update s x v = (\<lambda> y . if x=y then v else s y)"

type_synonym State = "Store \<times> Heap"

text\<open>Arithmetic and boolean expressions are as before.\<close>

datatype Expr = 
    varE Var 
  | valE Val
  | opE "Val \<Rightarrow> Val \<Rightarrow> Val" Expr Expr

datatype BExpr = compB "Val \<Rightarrow> Val \<Rightarrow> bool" Expr Expr

text\<open>The same applies to their semantics.\<close>

primrec evalE::"Expr \<Rightarrow> Store \<Rightarrow> Val"
where
"evalE (varE x) s = s x" |
"evalE (valE v) s = v" |
"evalE (opE f e1 e2) s = f (evalE e1 s) (evalE e2 s)"

primrec evalB::"BExpr \<Rightarrow> Store \<Rightarrow> bool"
where
"evalB (compB f e1 e2) s = f (evalE e1 s) (evalE e2 s)"

text\<open>The category of commands is extended by instructions for
allocating a fresh object, obtaining a value from a field and assigning
a value to a field.\<close>

datatype OBJ =
    Skip 
  | Assign Var Expr
  | New Var Class
  | Get Var Var Field
  | Put Var Field Expr
  | Comp OBJ OBJ
  | While BExpr OBJ
  | Iff BExpr OBJ OBJ
  | Call

text\<open>The body of the procedure is identified by the same constant as
before.\<close>

consts body :: OBJ

text\<open>The operational semantics is again a standard big-step
relation.\<close>

inductive_set Semn :: "(State \<times> OBJ \<times> nat \<times> State) set"
where
SemSkip: "s=t \<Longrightarrow> (s,Skip,1, t):Semn"

| SemAssign:
  "\<lbrakk> t = (update (fst s) x (evalE e (fst s)), snd s)\<rbrakk> 
  \<Longrightarrow> (s, Assign x e, 1, t):Semn"

| SemNew:
  "\<lbrakk>l \<notin> Dom (snd s); 
       t = (update (fst s) x (RVal (Loc l)), (l,(C,[])) # (snd s))\<rbrakk> 
  \<Longrightarrow> (s, New x C, 1, t):Semn"

| SemGet:
  "\<lbrakk>(fst s) y = RVal(Loc l); lookup (snd s) l = Some(C,Flds); 
       lookup Flds F = Some v; t = (update (fst s) x v, snd s)\<rbrakk> 
  \<Longrightarrow> (s, Get x y F, 1, t):Semn"

| SemPut:
  "\<lbrakk>(fst s) x = RVal(Loc l); lookup (snd s) l = Some(C,Flds); 
       t = (fst s, (l,(C,(F,evalE e (fst s)) # Flds)) # (snd s))\<rbrakk> 
  \<Longrightarrow> (s, Put x F e, 1, t):Semn"

| SemComp:
  "\<lbrakk> (s, c, n, r):Semn; (r,d, m, t):Semn; k=(max n m)+1\<rbrakk>
  \<Longrightarrow> (s, Comp c d, k, t):Semn"

| SemWhileT:
  "\<lbrakk>evalB b (fst s); (s,c, n, r):Semn; (r, While b c, m, t):Semn; k=((max n m)+1)\<rbrakk>
  \<Longrightarrow> (s, While b c, k, t):Semn"

| SemWhileF:
  "\<lbrakk>\<not> (evalB b (fst s)); t=s\<rbrakk> \<Longrightarrow> (s, While b c, 1, t):Semn"

| SemTrue:
  "\<lbrakk>evalB b (fst s); (s,c1, n, t):Semn\<rbrakk> 
  \<Longrightarrow> (s, Iff b c1 c2, n+1, t):Semn"

| SemFalse:
  "\<lbrakk>\<not> (evalB b (fst s)); (s,c2, n, t):Semn\<rbrakk>
  \<Longrightarrow> (s, Iff b c1 c2, n+1, t):Semn"

| SemCall: "\<lbrakk> (s,body,n, t):Semn\<rbrakk> \<Longrightarrow> (s,Call,n+1, t):Semn"

abbreviation
  SemN  :: "[State, OBJ, nat, State] \<Rightarrow> bool"   (" _ , _ \<rightarrow>\<^sub>_  _ ")
where
"s,c \<rightarrow>\<^sub>n t == (s,c,n,t) : Semn"

text\<open>Often, the height index does not matter, so we define a notion
hiding it.\<close>

definition
Sem :: "[State, OBJ, State] \<Rightarrow> bool" ("_ , _ \<Down> _ " 1000)
where "s,c \<Down> t = (\<exists> n. s,c \<rightarrow>\<^sub>n t)"

inductive_cases Sem_eval_cases: 
 "s,Skip \<rightarrow>\<^sub>n t"
 "s,(Assign x e) \<rightarrow>\<^sub>n t"
 "s,(New x C) \<rightarrow>\<^sub>n t"
 "s,(Get x y F) \<rightarrow>\<^sub>n t"
 "s,(Put x F e) \<rightarrow>\<^sub>n t"
 "s,(Comp c1 c2) \<rightarrow>\<^sub>n t"
 "s,(While b c) \<rightarrow>\<^sub>n t"
 "s,(Iff b c1 c2) \<rightarrow>\<^sub>n t"
 "s, Call \<rightarrow>\<^sub>n t"

(*<*)
lemma Sem_no_zero_height_derivsAux: "\<forall> s t. ((s, c \<rightarrow>\<^sub>0 t) \<longrightarrow> False)"
by (induct_tac c, auto elim: Sem_eval_cases)
(*>*)
lemma Sem_no_zero_height_derivs: "(s, c \<rightarrow>\<^sub>0 t) \<Longrightarrow> False"
(*<*)by (insert Sem_no_zero_height_derivsAux, fastforce)(*>*)

text\<open>Determinism does not hold as allocation is nondeterministic.\<close>

text\<open>End of theory OBJ\<close>
end
