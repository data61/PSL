(*File: IMP.thy*)
(*Authors: Lennart Beringer and Martin Hofmann, LMU Munich 2008*)
theory IMP imports Main begin
section \<open>The language IMP\<close>

text\<open>\label{sec:IMP}In this section we define a simple imperative programming
language. Syntax and operational semantics are as in \cite{Winskel93},
except that we enrich the language with a single unnamed,
parameterless procedure. Both, this section and the following one
merely set the basis for the development described in the later
sections and largely follow the approach to formalize program logics
advocated by Kleymann, Nipkow, and others - see for example
\cite{KleymannPhD,Nipkow-CSL02,Nipkow-AFP-AHL}.\<close>

subsection\<open>Syntax\<close> 

text\<open>We start from unspecified categories of program variables and
values.\<close>

typedecl Var
typedecl Val

text\<open>Arithmetic expressions are inductively built up from variables,
values, and binary operators which are modeled as meta-logical
functions over values. Similarly, boolean expressions are built up
from arithmetic expressions using binary boolean operators which are 
modeled as functions of the ambient logic HOL.\<close>

datatype Expr =
   varE Var
 | valE Val
 | opE "Val \<Rightarrow> Val \<Rightarrow> Val" Expr Expr

datatype BExpr = compB "Val \<Rightarrow> Val \<Rightarrow> bool" Expr Expr

text\<open>Commands are the usual ones for an imperative language, plus the
command $\mathit{Call}$ which stands for the invocation of a single
(unnamed, parameterless) procedure.\<close>

datatype IMP =
    Skip 
  | Assign Var Expr
  | Comp IMP IMP
  | While BExpr IMP
  | Iff BExpr IMP IMP
  | Call

text\<open>The body of this procedure is identified by the following
constant.\<close>

consts body :: IMP

subsection\<open>Dynamic semantics\<close>

text\<open>States are given by stores - in our case, HOL functions
mapping program variables to values.\<close>

type_synonym State = "Var \<Rightarrow> Val"

definition update :: "State \<Rightarrow> Var \<Rightarrow> Val \<Rightarrow> State"
where "update s x v = (\<lambda> y . if x=y then v else s y)"

text\<open>The evaluation of expressions is defined inductively, as
standard.\<close>

primrec evalE::"Expr \<Rightarrow> State \<Rightarrow> Val"
where
"evalE (varE x) s = s x" |
"evalE (valE v) s = v" |
"evalE (opE f e1 e2) s = f (evalE e1 s) (evalE e2 s)"

primrec evalB::"BExpr \<Rightarrow> State \<Rightarrow> bool"
where
"evalB (compB f e1 e2) s = f (evalE e1 s) (evalE e2 s)"

text\<open>The operational semantics is a standard big-step relation, with
a height index that facilitates the Kleymann-Nipkow-style~\cite{KleymannPhD,Nipkow-CSL02}
soundness proof of the program logic.\<close>

inductive_set Semn :: "(State \<times> IMP \<times> nat \<times> State) set" where
 SemSkip: "(s,Skip,1,s) : Semn" 

| SemAssign:
  "\<lbrakk> t = update s x (evalE e s)\<rbrakk> \<Longrightarrow> (s,Assign x e,1,t):Semn"

| SemComp:
  "\<lbrakk> (s,c1,n,r):Semn; (r,c2,m,t):Semn; k=(max n m)+1\<rbrakk>
   \<Longrightarrow> (s,Comp c1 c2,k,t):Semn"

| SemWhileT:
  "\<lbrakk>evalB b s; (s,c,n,r):Semn; (r,While b c,m,t):Semn; 
       k=((max n m)+1)\<rbrakk>
   \<Longrightarrow> (s,While b c,k,t):Semn"

| SemWhileF: "\<lbrakk>\<not> (evalB b s); t=s\<rbrakk> \<Longrightarrow> (s,While b c,1,t):Semn"

| SemTrue:
  "\<lbrakk>evalB b s; (s,c1,n,t):Semn \<rbrakk> \<Longrightarrow> (s,Iff b c1 c2,n+1,t):Semn"

| SemFalse:
  "\<lbrakk>\<not> (evalB b s); (s,c2,n,t):Semn\<rbrakk> \<Longrightarrow> (s,Iff b c1 c2,n+1,t):Semn"

| SemCall: "(s,body,n,t):Semn \<Longrightarrow> (s,Call,n+1,t):Semn"
(*
 SemSkip:  "(s,Skip \<longrightarrow>\<^sub>1 s" 
 SemAssign:"\<lbrakk> t = update s x (evalE e s)\<rbrakk> \<Longrightarrow> s,(Assign x e) \<longrightarrow>\<^sub>1 t"
SemComp:  "\<lbrakk> s,c1 \<longrightarrow>\<^sub>n r; r,c2 \<longrightarrow>\<^sub>m t; k=(max n m)+1\<rbrakk>
          \<Longrightarrow> s,(Comp c1 c2) \<longrightarrow>\<^sub>k t"
 SemWhileT:"\<lbrakk>evalB b s; s,c \<longrightarrow>\<^sub>n r; r,(While b c) \<longrightarrow>\<^sub>m t; 
             k=((max n m)+1)\<rbrakk>
          \<Longrightarrow> s,(While b c) \<longrightarrow>\<^sub>k t"
 SemWhileF:"\<lbrakk>\<not> (evalB b s); t=s\<rbrakk> \<Longrightarrow> s,(While b c) \<longrightarrow>\<^sub>1 t"
 SemTrue:  "\<lbrakk>evalB b s; s,c1 \<longrightarrow>\<^sub>n t\<rbrakk> \<Longrightarrow> s,(Iff b c1 c2) \<longrightarrow>\<^sub>(n+1) t"
 SemFalse: "\<lbrakk>\<not> (evalB b s); s,c2 \<longrightarrow>\<^sub>n t\<rbrakk> 
          \<Longrightarrow> s,(Iff b c1 c2) \<longrightarrow>\<^sub>(n+1) t"
 SemCall:  "\<lbrakk> s,body \<longrightarrow>\<^sub>n t\<rbrakk> \<Longrightarrow> s,Call \<longrightarrow>\<^sub>(n+1) t"
*)

abbreviation
SemN  :: "[State, IMP, nat, State] \<Rightarrow> bool"   (" _ , _ \<rightarrow>\<^sub>_  _ ")
where
"s,c \<rightarrow>\<^sub>n t == (s,c,n,t) : Semn"

text\<open>Often, the height index does not matter, so we define a notion
hiding it.\<close>

definition Sem :: "[State, IMP, State] \<Rightarrow> bool" ("_ , _ \<Down> _ " 1000)
where "s,c \<Down> t = (\<exists> n. s,c \<rightarrow>\<^sub>n t)"

text\<open>Inductive elimination rules for the (indexed) dynamic semantics:\<close>

inductive_cases Sem_eval_cases: 
 "s,Skip \<rightarrow>\<^sub>n t"
 "s,(Assign x e) \<rightarrow>\<^sub>n t"
 "s,(Comp c1 c2) \<rightarrow>\<^sub>n t"
 "s,(While b c) \<rightarrow>\<^sub>n t"
 "s,(Iff b c1 c2) \<rightarrow>\<^sub>n t"
 "s, Call \<rightarrow>\<^sub>n t"

(*<*)
lemma Sem_no_zero_height_derivsAux: "\<forall> s t. ((s, c \<rightarrow>\<^sub>0 t) --> False)"
by (induct_tac c, auto elim: Sem_eval_cases)
(*>*)

text\<open>An induction on $c$ shows that no derivations of height
$0$ exist.\<close>

lemma Sem_no_zero_height_derivs: "(s, c \<rightarrow>\<^sub>0 t) ==> False"
(*<*)by (insert Sem_no_zero_height_derivsAux, fastforce)(*>*)

(*<*)
lemma SemnDeterm[rule_format]:
"(s, c \<rightarrow>\<^sub>n t) ==> (\<forall> r m . (s, c \<rightarrow>\<^sub>m r) --> m=n \<and> r=t)"
apply (erule Semn.induct)
apply(clarsimp, elim Sem_eval_cases, simp)
(*Assign*)
apply (rule allI)+ apply rule
apply(elim Sem_eval_cases)
apply simp
(*Comp*)
apply (rule allI)+ apply rule
apply(elim Sem_eval_cases)
apply simp
(*WhileT*)
apply (rule allI)+ apply rule
apply (rotate_tac 3) apply (erule thin_rl)
apply (erule Sem_eval_cases) apply clarify
  apply (rotate_tac -4)
  apply (erule_tac x=rb in allE) apply (erule_tac x=na in allE) apply clarsimp 
  apply clarify
(*WhileF*)
apply (rule allI)+ apply rule
apply (erule Sem_eval_cases) apply clarify
  apply simp
(*True*)
apply (rule allI)+ apply rule
apply(elim Sem_eval_cases) 
apply simp
apply fast
(*False*)
apply (rule allI)+ apply rule
apply(elim Sem_eval_cases) 
apply fast
apply simp
(*Call*)
apply clarify
apply(elim Sem_eval_cases) 
apply simp
done
(*>*)

text\<open>The proof of determinism is by induction on the 
      (indexed) operational semantics.\<close>

lemma SemDeterm: "\<lbrakk>s, c \<Down> t; s, c \<Down> r\<rbrakk> \<Longrightarrow> r=t"
(*<*)
apply (simp add: Sem_def, clarsimp)
apply (drule SemnDeterm, assumption)
apply simp
done
(*>*)

text\<open>End of theory IMP\<close>
end
