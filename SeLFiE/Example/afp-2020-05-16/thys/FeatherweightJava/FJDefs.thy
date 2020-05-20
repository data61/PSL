(*  Title:       A theory of Featherweight Java in Isabelle/HOL
    Author:      Nate Foster <jnfoster at cis.upenn.edu>, 
                 Dimitrios Vytiniotis <dimitriv at cis.upenn.edu>, 2006
    Maintainer:  Nate Foster <jnfoster at cis.upenn.edu>,
                 Dimitrios Vytiniotis <dimitriv at cis.upenn.edu>
    License:     LGPL
*)

section \<open>{\tt FJDefs}: Basic Definitions\<close>

theory FJDefs
imports Main
begin

subsection \<open>Syntax\<close>

text \<open>We use a named representation for terms: variables, method
names, and class names, are all represented as {\tt nat}s. We use the
finite maps defined in {\tt Map.thy} to represent typing contexts and
the static class table. This section defines the representations of
each syntactic category (expressions, methods, constructors, classes,
class tables) and defines several constants ({\tt Object} and {\tt this}).
\<close>

subsubsection\<open>Type definitions\<close>

type_synonym varName = nat
type_synonym methodName = nat
type_synonym className = nat
record varDef     = 
  vdName :: "varName"
  vdType :: "className"
type_synonym varCtx = "varName \<rightharpoonup> className"

subsubsection\<open>Constants\<close>

definition
  Object :: "className" where
  "Object = 0"

definition
  this :: "varName" where
  "this == 0"

subsubsection \<open>Expressions\<close>

datatype exp = 
    Var "varName"
  | FieldProj "exp" "varName"              
  | MethodInvk "exp" "methodName" "exp list"
  | New "className" "exp list"
  | Cast "className" "exp"

subsubsection \<open>Methods\<close>

record methodDef = 
  mReturn :: "className"
  mName :: "methodName"
  mParams :: "varDef list"
  mBody :: "exp"


subsubsection \<open>Constructors\<close>

record constructorDef = 
  kName :: "className"
  kParams :: "varDef list"
  kSuper :: "varName list"
  kInits :: "varName list"

subsubsection \<open>Classes\<close>

record classDef = 
  cName :: "className"
  cSuper :: "className"
  cFields :: "varDef list"
  cConstructor :: "constructorDef"
  cMethods :: "methodDef list"

subsubsection \<open>Class Tables\<close>

type_synonym classTable = "className \<rightharpoonup> classDef"

subsection \<open>Sub-expression Relation\<close>

text \<open>The sub-expression relation, written $t \in
\mathit{subexprs}(s)$, is defined as the reflexive and transitive
closure of the immediate subexpression relation.
\<close>

inductive_set
  isubexprs :: "(exp * exp) set" 
  and isubexprs' :: "[exp,exp] \<Rightarrow> bool"  ("_ \<in> isubexprs'(_')" [80,80] 80)
where
  "e' \<in> isubexprs(e) \<equiv> (e',e) \<in> isubexprs"
| se_field    : "e \<in> isubexprs(FieldProj e fi)"
| se_invkrecv : "e \<in> isubexprs(MethodInvk e m es)"
| se_invkarg  : "\<lbrakk> ei \<in> set es \<rbrakk> \<Longrightarrow> ei \<in> isubexprs(MethodInvk e m es)"
| se_newarg   : "\<lbrakk> ei \<in> set es \<rbrakk> \<Longrightarrow> ei \<in> isubexprs(New C es)"
| se_cast     : "e \<in> isubexprs(Cast C e)"

abbreviation
  subexprs :: "[exp,exp] \<Rightarrow> bool"  ("_ \<in> subexprs'(_')" [80,80] 80)  where
  "e' \<in> subexprs(e) \<equiv> (e',e) \<in> isubexprs^*"

subsection \<open>Values\<close>

text\<open>A {\em value} is an expression of the form $\mathtt{new}\
\mathtt{C}(\mathit{overline{vs}})$, where $\mathit{\overline{vs}}$ is a list
of values.\<close>

inductive
  vals :: "[exp list] \<Rightarrow> bool" ("vals'(_')" [80] 80)
  and val :: "[exp] \<Rightarrow> bool" ("val'(_')" [80] 80)
where
   vals_nil : "vals([])"
 | vals_cons : "\<lbrakk> val(vh); vals(vt) \<rbrakk> \<Longrightarrow> vals((vh # vt))"
 | val : "\<lbrakk> vals(vs) \<rbrakk> \<Longrightarrow> val(New C vs)"

subsection \<open>Substitution\<close>

text \<open>The substitutions of a list of expressions $\mathit{ds}$ for a
list of variables $\mathit{xs}$ in another expression $e$ or a list of
expressions $\mathit{es}$ are defined in the obvious way, and written
$(\mathit{ds}/\mathit{xs})e$ and $[\mathit{ds}/\mathit{xs}]es$
respecitvely. 
\<close>

primrec substs :: "(varName \<rightharpoonup> exp) \<Rightarrow> exp \<Rightarrow> exp"
  and subst_list1 :: "(varName \<rightharpoonup> exp) \<Rightarrow> exp list \<Rightarrow> exp list"
  and subst_list2 :: "(varName \<rightharpoonup> exp) \<Rightarrow> exp list \<Rightarrow> exp list" where
  "substs \<sigma> (Var x) =             (case (\<sigma>(x)) of None \<Rightarrow> (Var x) | Some p \<Rightarrow> p)"
| "substs \<sigma> (FieldProj e f) =     FieldProj (substs \<sigma> e) f"
| "substs \<sigma> (MethodInvk e m es) = MethodInvk (substs \<sigma> e) m (subst_list1 \<sigma> es)"
| "substs \<sigma> (New C es) =          New C (subst_list2 \<sigma> es)"
| "substs \<sigma> (Cast C e) =          Cast C (substs \<sigma> e)"
| "subst_list1 \<sigma> [] = []"
| "subst_list1 \<sigma> (h # t) = (substs \<sigma> h) # (subst_list1 \<sigma> t)"
| "subst_list2 \<sigma> [] = []"
| "subst_list2 \<sigma> (h # t) = (substs \<sigma> h) # (subst_list2 \<sigma> t)"

abbreviation
  substs_syn :: "[exp list] \<Rightarrow> [varName list] \<Rightarrow> [exp] \<Rightarrow> exp"
    ("'(_'/_')_" [80,80,80] 80) where
  "(ds/xs)e \<equiv> substs (map_upds Map.empty xs ds) e"

abbreviation
  subst_list_syn :: "[exp list] \<Rightarrow> [varName list] \<Rightarrow> [exp list] \<Rightarrow> exp list"
    ("'[_'/_']_" [80,80,80] 80) where
  "[ds/xs]es \<equiv> map (substs (map_upds Map.empty xs ds)) es"


subsection \<open>Lookup\<close>

text \<open>The fuction $\mathit{lookup}\ f\ l$ function returns an option
containing the first element of $l$ satisfying $f$, or $\mathtt{None}$
if no such element exists 
\<close>

primrec lookup :: "'a list \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'a option"
where
  "lookup [] P = None"
| "lookup (h#t) P = (if P h then Some h else lookup t P)"

primrec lookup2 :: "'a list \<Rightarrow> 'b list \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'b option"
where
  "lookup2 [] l2 P = None"
| "lookup2 (h1#t1) l2 P = (if P h1 then Some(hd l2) else lookup2 t1 (tl l2) P)"

subsection \<open>Variable Definition Accessors\<close>

text\<open>This section contains several helper functions for reading off
the names and types of variable definitions (e.g., in field
 and method parameter declarations).\<close>

definition
  varDefs_names :: "varDef list \<Rightarrow> varName list" where
  "varDefs_names = map vdName"

definition
  varDefs_types :: "varDef list \<Rightarrow> className list" where
  "varDefs_types = map vdType"

subsection \<open>Subtyping Relation\<close>

text \<open>The subtyping relation, written $\mathit{CT} \vdash C
\mathtt{\lt:} D$ is just the reflexive and transitive closure of the
immediate subclass relation. (For the sake of simplicity, we define
subtyping directly instead of using the reflexive and transitive
closure operator.) The subtyping relation is extended to lists of
classes, written $\mathit{CT} \vdash\mathtt{+} \mathit{Cs} \mathtt{\lt:}
\mathit{Ds}$.\<close>

inductive
  subtyping :: "[classTable, className, className] \<Rightarrow> bool"  ("_ \<turnstile> _ <: _" [80,80,80] 80)
where
  s_refl  :  "CT \<turnstile> C <: C"
| s_trans : "\<lbrakk> CT \<turnstile> C <: D; CT \<turnstile> D <: E \<rbrakk> \<Longrightarrow> CT \<turnstile> C <: E"
| s_super : "\<lbrakk> CT(C) = Some(CDef); cSuper CDef = D \<rbrakk> \<Longrightarrow> CT \<turnstile> C <: D"

abbreviation
  neg_subtyping :: "[classTable, className, className] \<Rightarrow> bool"  ("_ \<turnstile> _ \<not><: _" [80,80,80] 80)
  where "CT \<turnstile> S \<not><: T \<equiv> \<not> CT \<turnstile> S <: T"

inductive
  subtypings :: "[classTable, className list, className list] \<Rightarrow> bool"  ("_ \<turnstile>+ _ <: _" [80,80,80] 80)
where
  ss_nil  : "CT \<turnstile>+ [] <: []"
| ss_cons : "\<lbrakk> CT \<turnstile> C0 <: D0; CT \<turnstile>+ Cs <: Ds \<rbrakk> \<Longrightarrow> CT \<turnstile>+ (C0 # Cs) <: (D0 # Ds)"

subsection \<open>{\tt fields} Relation\<close>

text\<open>The {\tt fields} relation, written
$\mathtt{fields}(\mathit{CT},C) = \mathit{Cf}$, relates $\mathit{Cf}$
to $C$ when $\mathit{Cf}$ is the list of fields declared directly or
indirectly (i.e., by a superclass) in $C$.\<close>

inductive
  fields :: "[classTable, className, varDef list] \<Rightarrow> bool" ("fields'(_,_') = _" [80,80,80] 80)
where
  f_obj: 
  "fields(CT,Object) = []"
| f_class: 
  "\<lbrakk> CT(C) = Some(CDef); cSuper CDef = D; cFields CDef = Cf; fields(CT,D) = Dg; DgCf = Dg @ Cf \<rbrakk> 
  \<Longrightarrow> fields(CT,C) = DgCf"

subsection \<open>{\tt mtype } Relation\<close>

text\<open>The {\tt mtype} relation, written
$\mathtt{mtype}(\mathit{CT},m,C) = \mathit{Cs} \rightarrow C_0$ relates
a class $C$, method name $m$, and the arrow type $\mathit{Cs}
\rightarrow C_0$. It either returns the type of the declaration of $m$
in $C$, if any such declaration exists, and otherwise returning the
type of $m$ from $C$'s superclass.
\<close>

inductive
  mtype :: "[classTable, methodName, className, className list, className] \<Rightarrow> bool" ("mtype'(_,_,_') = _ \<rightarrow> _" [80,80,80,80] 80)
where
  mt_class: 
  "\<lbrakk> CT(C) = Some(CDef);
    lookup (cMethods CDef) (\<lambda>md.(mName md = m)) = Some(mDef);
    varDefs_types (mParams mDef) = Bs;
    mReturn mDef = B \<rbrakk>
  \<Longrightarrow> mtype(CT,m,C) = Bs \<rightarrow> B"

| mt_super: 
  "\<lbrakk> CT(C) = Some (CDef);
    lookup (cMethods CDef) (\<lambda>md.(mName md = m)) = None;
    cSuper CDef = D;
    mtype(CT,m,D) = Bs \<rightarrow> B \<rbrakk>
  \<Longrightarrow> mtype(CT,m,C) = Bs \<rightarrow> B"

subsection \<open>{\tt mbody} Relation\<close>

text\<open>The {\tt mtype} relation, written
$\mathtt{mbody}(\mathit{CT},m,C) = \mathit{xs} . e_0$ relates a class
$C$, method name $m$, and the names of the parameters $\mathit{xs}$
and the body of the method $e_0$. It either returns the parameter
names and body of the declaration of $m$ in $C$, if any such
declaration exists, and otherwise the parameter names and body of $m$
from $C$'s superclass.  
\<close>

inductive
  mbody :: "[classTable, methodName, className, varName list, exp] \<Rightarrow> bool" ("mbody'(_,_,_') = _ . _" [80,80,80,80] 80)
where
  mb_class: 
  "\<lbrakk> CT(C) = Some(CDef);
     lookup (cMethods CDef) (\<lambda>md.(mName md = m)) = Some(mDef);
     varDefs_names (mParams mDef) = xs;
     mBody mDef = e \<rbrakk>
  \<Longrightarrow> mbody(CT,m,C) = xs . e"

| mb_super:
  "\<lbrakk> CT(C) = Some(CDef);
     lookup (cMethods CDef) (\<lambda>md.(mName md = m)) = None;
     cSuper CDef = D;
     mbody(CT,m,D) = xs . e \<rbrakk>
  \<Longrightarrow> mbody(CT,m,C) = xs . e"


subsection \<open>Typing Relation\<close>

text \<open>
The typing relation, written $\mathit{CT};\Gamma \vdash e : C$
relates an expression $e$ to its type $C$, under the typing context
$\Gamma$. The multi-typing relation, written $\mathit{CT};\Gamma
\vdash\mathtt{+} \mathit{es}:\mathit{Cs}$ relates lists of expressions
to lists of types. 
\<close>

inductive
  typings :: "[classTable, varCtx, exp list, className list] \<Rightarrow> bool" ("_;_ \<turnstile>+ _ : _" [80,80,80,80] 80)
  and typing :: "[classTable, varCtx, exp, className] \<Rightarrow> bool" ("_;_ \<turnstile> _ : _" [80,80,80,80] 80)
where
  ts_nil : "CT;\<Gamma> \<turnstile>+ [] : []"

| ts_cons  : 
  "\<lbrakk> CT;\<Gamma> \<turnstile> e0 : C0; CT;\<Gamma> \<turnstile>+ es : Cs \<rbrakk> 
  \<Longrightarrow> CT;\<Gamma> \<turnstile>+ (e0 # es) : (C0 # Cs)"

| t_var : 
  "\<lbrakk> \<Gamma>(x) = Some C \<rbrakk> \<Longrightarrow> CT;\<Gamma> \<turnstile> (Var x) : C"

| t_field : 
  "\<lbrakk> CT;\<Gamma> \<turnstile> e0 : C0;
     fields(CT,C0) = Cf;
     lookup Cf (\<lambda>fd.(vdName fd = fi)) = Some(fDef);
     vdType fDef = Ci \<rbrakk>
  \<Longrightarrow> CT;\<Gamma> \<turnstile> FieldProj e0 fi : Ci"

| t_invk : 
  "\<lbrakk> CT;\<Gamma> \<turnstile> e0 : C0;
     mtype(CT,m,C0) = Ds \<rightarrow> C;
     CT;\<Gamma> \<turnstile>+ es : Cs;
     CT \<turnstile>+ Cs <: Ds;
     length es = length Ds \<rbrakk>
  \<Longrightarrow> CT;\<Gamma> \<turnstile> MethodInvk e0 m es : C"

| t_new : 
  "\<lbrakk> fields(CT,C) = Df;
     length es = length Df;
     varDefs_types Df = Ds;
     CT;\<Gamma> \<turnstile>+ es : Cs;
     CT \<turnstile>+ Cs <: Ds \<rbrakk>
  \<Longrightarrow> CT;\<Gamma> \<turnstile> New C es : C"

| t_ucast : 
  "\<lbrakk> CT;\<Gamma> \<turnstile> e0 : D; 
     CT \<turnstile> D <: C \<rbrakk>
  \<Longrightarrow> CT;\<Gamma> \<turnstile> Cast C e0 : C"

| t_dcast : 
  "\<lbrakk> CT;\<Gamma> \<turnstile> e0 : D; 
     CT \<turnstile> C <: D; C \<noteq> D \<rbrakk>
  \<Longrightarrow> CT;\<Gamma> \<turnstile> Cast C e0 : C"

| t_scast : 
  "\<lbrakk> CT;\<Gamma> \<turnstile> e0 : D;
     CT \<turnstile> C \<not><: D;
     CT \<turnstile> D \<not><: C \<rbrakk>
  \<Longrightarrow> CT;\<Gamma> \<turnstile> Cast C e0 : C"

text \<open>We occasionally find the following induction principle, which
only mentions the typing of a single expression, more useful than the
mutual induction principle generated by Isabelle, which mentions the
typings of single expressions and of lists of expressions. 
\<close>

lemma typing_induct:
  assumes "CT;\<Gamma> \<turnstile> e : C" (is ?T)
  and "\<And>C CT \<Gamma> x. \<Gamma> x = Some C \<Longrightarrow> P CT \<Gamma> (Var x) C" 
  and "\<And>C0 CT Cf Ci \<Gamma> e0 fDef fi. \<lbrakk>CT;\<Gamma> \<turnstile> e0 : C0; P CT \<Gamma> e0 C0; fields(CT,C0) = Cf; lookup Cf (\<lambda>fd. vdName fd = fi) = Some fDef; vdType fDef = Ci\<rbrakk> \<Longrightarrow> P CT \<Gamma> (FieldProj e0 fi) Ci" 
  and "\<And>C C0 CT Cs Ds \<Gamma> e0 es m. \<lbrakk>CT;\<Gamma> \<turnstile> e0 : C0; P CT \<Gamma> e0 C0; mtype(CT,m,C0) = Ds \<rightarrow> C; CT;\<Gamma> \<turnstile>+ es : Cs; \<And>i . \<lbrakk> i < length es \<rbrakk> \<Longrightarrow>  P CT \<Gamma> (es!i) (Cs!i); CT \<turnstile>+ Cs <: Ds; length es = length Ds\<rbrakk> \<Longrightarrow> P CT \<Gamma> (MethodInvk e0 m es) C"
  and "\<And>C CT Cs Df Ds \<Gamma> es. \<lbrakk>fields(CT,C) = Df; length es = length Df; varDefs_types Df = Ds; CT;\<Gamma> \<turnstile>+ es : Cs; \<And>i. \<lbrakk> i < length es \<rbrakk> \<Longrightarrow> P CT \<Gamma> (es!i) (Cs!i); CT \<turnstile>+ Cs <: Ds\<rbrakk> \<Longrightarrow> P CT \<Gamma> (New C es) C"
  and "\<And>C CT D \<Gamma> e0. \<lbrakk>CT;\<Gamma> \<turnstile> e0 : D; P CT \<Gamma> e0 D; CT \<turnstile> D <: C\<rbrakk> \<Longrightarrow> P CT \<Gamma> (Cast C e0) C" 
  and "\<And>C CT D \<Gamma> e0. \<lbrakk>CT;\<Gamma> \<turnstile> e0 : D; P CT \<Gamma> e0 D; CT \<turnstile> C <: D; C \<noteq> D\<rbrakk> \<Longrightarrow> P CT \<Gamma> (Cast C e0) C"
  and "\<And>C CT D \<Gamma> e0. \<lbrakk>CT;\<Gamma> \<turnstile> e0 : D; P CT \<Gamma> e0 D; CT \<turnstile> C \<not><: D; CT \<turnstile> D \<not><: C\<rbrakk> \<Longrightarrow> P CT \<Gamma> (Cast C e0) C" 
 shows "P CT \<Gamma> e C" (is ?P)
proof -
  fix es Cs
  let ?IH="CT;\<Gamma> \<turnstile>+ es : Cs \<longrightarrow> (\<forall>i < length es.  P CT \<Gamma> (es!i) (Cs!i))"
  have "?IH \<and> (?T \<longrightarrow> ?P)"
  proof(induct rule:typings_typing.induct)
    case (ts_nil CT \<Gamma>) show ?case by auto
  next
    case (ts_cons CT \<Gamma> e0 C0 es Cs) 
    show ?case proof
      fix i
      show "i < length (e0#es) \<longrightarrow> P CT \<Gamma> ((e0#es)!i) ((C0#Cs)!i)" using ts_cons by(cases i, auto)
    qed
  next
    case t_var then show ?case using assms by auto
  next
    case t_field then show ?case using assms by auto
  next
    case t_invk then show ?case using assms by auto
  next
    case t_new then show ?case using assms by auto
  next
    case t_ucast then show ?case using assms by auto
  next
    case t_dcast then show ?case using assms by auto
  next
    case t_scast then show ?case using assms by auto
  qed
  thus ?thesis using assms by auto
qed

subsection \<open>Method Typing Relation\<close>

text \<open>A method definition $\mathit{md}$, declared in a class $C$, is
well-typed, written $\mathit{CT} \vdash \mathit{md} \texttt{OK IN}\ C$
if its body is well-typed and it has the same type (i.e., overrides)
any method with the same name declared in the superclass of $C$.\<close>

inductive
  method_typing :: "[classTable, methodDef, className] \<Rightarrow> bool" ("_ \<turnstile> _ OK IN _" [80,80,80] 80)
where
m_typing:
  "\<lbrakk> CT(C) = Some(CDef);
     cName CDef = C;
     cSuper CDef = D;
     mName mDef = m;
     lookup (cMethods CDef) (\<lambda>md.(mName md = m)) = Some(mDef);
     mReturn mDef = C0; mParams mDef = Cxs; mBody mDef = e0;
     varDefs_types Cxs = Cs;
     varDefs_names Cxs = xs;
     \<Gamma> = (map_upds Map.empty xs Cs)(this \<mapsto> C); 
     CT;\<Gamma> \<turnstile> e0 : E0;
     CT \<turnstile> E0 <: C0;
     \<forall>Ds D0. (mtype(CT,m,D) = Ds \<rightarrow> D0) \<longrightarrow> (Cs=Ds \<and> C0=D0) \<rbrakk>
  \<Longrightarrow> CT \<turnstile> mDef OK IN C"

inductive
  method_typings :: "[classTable, methodDef list, className] \<Rightarrow> bool" ("_ \<turnstile>+ _ OK IN _" [80,80,80] 80)
where
  ms_nil : 
  "CT \<turnstile>+ [] OK IN C"

| ms_cons : 
  "\<lbrakk> CT \<turnstile> m OK IN C; 
     CT \<turnstile>+ ms OK IN C \<rbrakk>
  \<Longrightarrow> CT \<turnstile>+ (m # ms) OK IN C"


subsection \<open>Class Typing Relation\<close>

text \<open>A class definition $\mathit{cd}$ is well-typed, written
$\mathit{CT}\vdash \mathit{cd} \texttt{OK}$ if its constructor
initializes each field, and all of its methods are well-typed.\<close>

inductive
  class_typing :: "[classTable, classDef] \<Rightarrow> bool" ("_ \<turnstile> _ OK" [80,80] 80)
where
t_class: "\<lbrakk> cName CDef = C;            
            cSuper CDef = D;
            cConstructor CDef = KDef;
            cMethods CDef = M;
            kName KDef = C;
            kParams KDef = (Dg@Cf);
            kSuper KDef = varDefs_names Dg;
            kInits KDef = varDefs_names Cf;
            fields(CT,D) = Dg;
            CT \<turnstile>+ M OK IN C \<rbrakk>
  \<Longrightarrow> CT \<turnstile> CDef OK"

subsection \<open>Class Table Typing Relation\<close>

text \<open>A class table is well-typed, written $\mathit{CT}\
\texttt{OK}$ if for every class name $C$, the class definition mapped
to by $\mathit{CT}$ is is well-typed and has name $C$.\<close>

inductive
  ct_typing :: "classTable \<Rightarrow> bool" ("_ OK" 80)
where
ct_all_ok: 
  "\<lbrakk> Object \<notin> dom(CT); 
     \<forall>C CDef. CT(C) = Some(CDef) \<longrightarrow> (CT \<turnstile> CDef OK) \<and> (cName CDef = C) \<rbrakk>
  \<Longrightarrow> CT OK"

subsection \<open>Evaluation Relation\<close>

text \<open>The single-step and multi-step evaluation relations are
written $\mathit{CT} \vdash e \rightarrow e'$ and $\mathit{CT} \vdash
e \rightarrow^* e'$ respectively.\<close>

inductive
  reduction :: "[classTable, exp, exp] \<Rightarrow> bool" ("_ \<turnstile> _ \<rightarrow> _" [80,80,80] 80)
where

  r_field: 
  "\<lbrakk> fields(CT,C) = Cf;                   
     lookup2 Cf es (\<lambda>fd.(vdName fd = fi)) = Some(ei) \<rbrakk>
  \<Longrightarrow> CT \<turnstile> FieldProj (New C es) fi \<rightarrow> ei"

| r_invk: 
  "\<lbrakk> mbody(CT,m,C) = xs . e0;
     substs ((map_upds Map.empty xs ds)(this \<mapsto> (New C es))) e0 = e0' \<rbrakk>
  \<Longrightarrow> CT \<turnstile> MethodInvk (New C es) m ds \<rightarrow> e0'"

| r_cast: 
  "\<lbrakk> CT \<turnstile> C <: D \<rbrakk> 
  \<Longrightarrow> CT \<turnstile> Cast D (New C es) \<rightarrow> New C es"

| rc_field: 
  "\<lbrakk> CT \<turnstile> e0 \<rightarrow> e0' \<rbrakk> 
  \<Longrightarrow> CT \<turnstile> FieldProj e0 f \<rightarrow> FieldProj e0' f"

| rc_invk_recv: 
  "\<lbrakk> CT \<turnstile> e0 \<rightarrow> e0' \<rbrakk> 
  \<Longrightarrow> CT \<turnstile> MethodInvk e0 m es \<rightarrow> MethodInvk e0' m es"

| rc_invk_arg: 
  "\<lbrakk> CT \<turnstile> ei \<rightarrow> ei' \<rbrakk>
  \<Longrightarrow> CT \<turnstile> MethodInvk e0 m (el@ei#er) \<rightarrow> MethodInvk e0 m (el@ei'#er)"

| rc_new_arg: 
  "\<lbrakk> CT \<turnstile> ei \<rightarrow> ei' \<rbrakk> 
  \<Longrightarrow> CT \<turnstile> New C (el@ei#er) \<rightarrow> New C (el@ei'#er)"

| rc_cast: 
  "\<lbrakk> CT \<turnstile> e0 \<rightarrow> e0' \<rbrakk> 
  \<Longrightarrow> CT \<turnstile> Cast C e0 \<rightarrow> Cast C e0'"

inductive
  reductions :: "[classTable, exp, exp] \<Rightarrow> bool" ("_ \<turnstile> _ \<rightarrow>* _" [80,80,80] 80)
where
  rs_refl: "CT \<turnstile> e \<rightarrow>* e" 
| rs_trans: "\<lbrakk> CT \<turnstile> e \<rightarrow> e'; CT \<turnstile> e' \<rightarrow>* e'' \<rbrakk> \<Longrightarrow>  CT \<turnstile> e \<rightarrow>* e''"

end
