theory Syntax
imports
  Complex_Main
  "Ids"
begin 
section \<open>Syntax\<close>
text \<open>
  We define the syntax of dL terms, formulas and hybrid programs. As in
  CADE'15, the syntax allows arbitrarily nested differentials. However, 
  the semantics of such terms is very surprising (e.g. (x')' is zero in
  every state), so we define predicates dfree and dsafe to describe terms
  with no differentials and no nested differentials, respectively.

  In keeping with the CADE'15 presentation we currently make the simplifying
  assumption that all terms are smooth, and thus division and arbitrary
  exponentiation are absent from the syntax. Several other standard logical
  constructs are implemented as derived forms to reduce the soundness burden.
  
  The types of formulas and programs are parameterized by three finite types 
  ('a, 'b, 'c) used as identifiers for function constants, context constants, and
  everything else, respectively. These type variables are distinct because some
  substitution operations affect one type variable while leaving the others unchanged.
  Because these types will be finite in practice, it is more useful to think of them
  as natural numbers that happen to be represented as types (due to HOL's lack of dependent types).
  The types of terms and ODE systems follow the same approach, but have only two type 
  variables because they cannot contain contexts.
\<close>
datatype ('a, 'c) trm =
\<comment> \<open>Real-valued variables given meaning by the state and modified by programs.\<close>
  Var 'c
\<comment> \<open>N.B. This is technically more expressive than true dL since most reals\<close>
\<comment> \<open>can't be written down.\<close>
| Const real
\<comment> \<open>A function (applied to its arguments) consists of an identifier for the function\<close>
\<comment> \<open>and a function \<open>'c \<Rightarrow> ('a, 'c) trm\<close> (where \<open>'c\<close> is a finite type) which specifies one\<close>
\<comment> \<open>argument of the function for each element of type \<open>'c\<close>. To simulate a function with\<close>
\<comment> \<open>less than \<open>'c\<close> arguments, set the remaining arguments to a constant, such as \<open>Const 0\<close>\<close>
| Function 'a "'c \<Rightarrow> ('a, 'c) trm" ("$f")
| Plus "('a, 'c) trm" "('a, 'c) trm"
| Times "('a, 'c) trm" "('a, 'c) trm"
\<comment> \<open>A (real-valued) variable standing for a differential, such as \<open>x'\<close>, given meaning by the state\<close>
\<comment> \<open>and modified by programs.\<close>
| DiffVar 'c ("$'")
\<comment> \<open>The differential of an arbitrary term \<open>(\<theta>)'\<close>\<close>
| Differential "('a, 'c) trm"

datatype('a, 'c) ODE =
\<comment> \<open>Variable standing for an ODE system, given meaning by the interpretation\<close>
OVar 'c
\<comment> \<open>Singleton ODE defining \<open>x' = \<theta>\<close>, where \<open>\<theta>\<close> may or may not contain \<open>x\<close>\<close>
\<comment> \<open>(but must not contain differentials)\<close>
| OSing 'c "('a, 'c) trm"
\<comment> \<open>The product \<open>OProd ODE1 ODE2\<close> composes two ODE systems in parallel, e.g.\<close>
\<comment> \<open>\<open>OProd (x' = y) (y' = -x)\<close> is the system \<open>{x' = y, y' = -x}\<close>\<close>
| OProd "('a, 'c) ODE" "('a, 'c) ODE"

datatype ('a, 'b, 'c) hp =
\<comment> \<open>Variables standing for programs, given meaning by the interpretation.\<close>
  Pvar 'c                           ("$\<alpha>")
\<comment> \<open>Assignment to a real-valued variable \<open>x := \<theta>\<close>\<close>
| Assign 'c "('a, 'c) trm"                (infixr ":=" 10)
\<comment> \<open>Assignment to a differential variable\<close>
| DiffAssign 'c "('a, 'c) trm"
\<comment> \<open>Program \<open>?\<phi>\<close> succeeds iff \<open>\<phi>\<close> holds in current state.\<close>
| Test "('a, 'b, 'c) formula"                 ("?")
\<comment> \<open>An ODE program is an ODE system with some evolution domain.\<close>
| EvolveODE "('a, 'c) ODE" "('a, 'b, 'c) formula"
\<comment> \<open>Non-deterministic choice between two programs \<open>a\<close> and \<open>b\<close>\<close>
| Choice "('a, 'b, 'c) hp" "('a, 'b, 'c) hp"            (infixl "\<union>\<union>" 10)
\<comment> \<open>Sequential composition of two programs \<open>a\<close> and \<open>b\<close>\<close>
| Sequence "('a, 'b, 'c) hp"  "('a, 'b, 'c) hp"         (infixr ";;" 8)
\<comment> \<open>Nondeterministic repetition of a program \<open>a\<close>, zero or more times.\<close>
| Loop "('a, 'b, 'c) hp"                      ("_**")

and ('a, 'b, 'c) formula =
  Geq "('a, 'c) trm" "('a, 'c) trm"
| Prop 'c "'c \<Rightarrow> ('a, 'c) trm"      ("$\<phi>")
| Not "('a, 'b, 'c) formula"            ("!")
| And "('a, 'b, 'c) formula" "('a, 'b, 'c) formula"    (infixl "&&" 8)
| Exists 'c "('a, 'b, 'c) formula"
\<comment> \<open>\<open>\<langle>\<alpha>\<rangle>\<phi>\<close> iff exists run of \<open>\<alpha>\<close> where \<open>\<phi>\<close> is true in end state\<close>
| Diamond "('a, 'b, 'c) hp" "('a, 'b, 'c) formula"         ("(\<langle> _ \<rangle> _)" 10)
\<comment> \<open>Contexts \<open>C\<close> are symbols standing for functions from (the semantics of) formulas to\<close>
\<comment> \<open>(the semantics of) formulas, thus \<open>C(\<phi>)\<close> is another formula. While not necessary\<close>
\<comment> \<open>in terms of expressiveness, contexts allow for more efficient reasoning principles.\<close>
| InContext 'b "('a, 'b, 'c) formula"
    
\<comment> \<open>Derived forms\<close>
definition Or :: "('a, 'b, 'c) formula \<Rightarrow> ('a, 'b, 'c) formula \<Rightarrow> ('a, 'b, 'c) formula" (infixl "||" 7)
where "Or P Q = Not (And (Not P) (Not Q))"

definition Implies :: "('a, 'b, 'c) formula \<Rightarrow> ('a, 'b, 'c) formula \<Rightarrow> ('a, 'b, 'c) formula" (infixr "\<rightarrow>" 10)
where "Implies P Q = Or Q (Not P)"

definition Equiv :: "('a, 'b, 'c) formula \<Rightarrow> ('a, 'b, 'c) formula \<Rightarrow> ('a, 'b, 'c) formula" (infixl "\<leftrightarrow>" 10)
where "Equiv P Q = Or (And P Q) (And (Not P) (Not Q))"

definition Forall :: "'c \<Rightarrow> ('a, 'b, 'c) formula \<Rightarrow> ('a, 'b, 'c) formula"
where "Forall x P = Not (Exists x (Not P))"

definition Equals :: "('a, 'c) trm \<Rightarrow> ('a, 'c) trm \<Rightarrow> ('a, 'b, 'c) formula"
where "Equals \<theta> \<theta>' = ((Geq \<theta> \<theta>') && (Geq \<theta>' \<theta>))"

definition Greater :: "('a, 'c) trm \<Rightarrow> ('a, 'c) trm \<Rightarrow> ('a, 'b, 'c) formula"
where "Greater \<theta> \<theta>' = ((Geq \<theta> \<theta>') && (Not (Geq \<theta>' \<theta>)))"
  
definition Box :: "('a, 'b, 'c) hp \<Rightarrow> ('a, 'b, 'c) formula \<Rightarrow> ('a, 'b, 'c) formula" ("([[_]]_)" 10)
where "Box \<alpha> P = Not (Diamond \<alpha> (Not P))"
  
definition TT ::"('a,'b,'c) formula" 
where "TT = Geq (Const 0) (Const 0)"

definition FF ::"('a,'b,'c) formula" 
where "FF = Geq (Const 0) (Const 1)"

type_synonym ('a,'b,'c) sequent = "('a,'b,'c) formula list * ('a,'b,'c) formula list"
\<comment> \<open>Rule: assumptions, then conclusion\<close>
type_synonym ('a,'b,'c) rule = "('a,'b,'c) sequent list * ('a,'b,'c) sequent"

  
\<comment> \<open>silliness to enable proving disequality lemmas\<close>
primrec sizeF::"('sf,'sc, 'sz) formula \<Rightarrow> nat"
  and   sizeP::"('sf,'sc, 'sz) hp \<Rightarrow> nat"
where 
  "sizeP (Pvar a) = 1"
| "sizeP (Assign x \<theta>) = 1"
| "sizeP (DiffAssign x \<theta>) = 1"
| "sizeP (Test \<phi>) = Suc (sizeF \<phi>)"
| "sizeP (EvolveODE ODE \<phi>) = Suc (sizeF \<phi>)"
| "sizeP (Choice \<alpha> \<beta>) = Suc (sizeP \<alpha> + sizeP \<beta>)"
| "sizeP (Sequence \<alpha> \<beta>) = Suc (sizeP \<alpha> + sizeP \<beta>)"
| "sizeP (Loop \<alpha>) = Suc (sizeP \<alpha>)"
| "sizeF (Geq p q) = 1"
| "sizeF (Prop p args) = 1"
| "sizeF (Not p) = Suc (sizeF p)"
| "sizeF (And p q) = sizeF p + sizeF q"
| "sizeF (Exists x p) = Suc (sizeF p)"
| "sizeF (Diamond p q) = Suc (sizeP p + sizeF q)"
| "sizeF (InContext C \<phi>) = Suc (sizeF \<phi>)"

lemma sizeF_diseq:"sizeF p \<noteq> sizeF q \<Longrightarrow> p \<noteq> q" by auto
  
named_theorems "expr_diseq" "Structural disequality rules for expressions"  
lemma [expr_diseq]:"p \<noteq> And p q" by(induction p, auto)
lemma [expr_diseq]:"q \<noteq> And p q" by(induction q, auto)
lemma [expr_diseq]:"p \<noteq> Not p" by(induction p, auto)
lemma [expr_diseq]:"p \<noteq> Or p q" by(rule sizeF_diseq, auto simp add: Or_def)
lemma [expr_diseq]:"q \<noteq> Or p q" by(rule sizeF_diseq, auto simp add: Or_def)
lemma [expr_diseq]:"p \<noteq> Implies p q" by(rule sizeF_diseq, auto simp add: Implies_def Or_def)
lemma [expr_diseq]:"q \<noteq> Implies p q" by(rule sizeF_diseq, auto simp add: Implies_def Or_def)
lemma [expr_diseq]:"p \<noteq> Equiv p q" by(rule sizeF_diseq, auto simp add: Equiv_def Or_def)
lemma [expr_diseq]:"q \<noteq> Equiv p q" by(rule sizeF_diseq, auto simp add: Equiv_def Or_def)
lemma [expr_diseq]:"p \<noteq> Exists x p" by(induction p, auto)
lemma [expr_diseq]:"p \<noteq> Diamond a p" by(induction p, auto)
lemma [expr_diseq]:"p \<noteq> InContext C p" by(induction p, auto)

\<comment> \<open>A predicational is like a context with no argument, i.e. a variable standing for a\<close>
\<comment> \<open>state-dependent formula, given meaning by the interpretation. This differs from a predicate\<close>
\<comment> \<open>because predicates depend only on their arguments (which might then indirectly depend on the state).\<close>
\<comment> \<open>We encode a predicational as a context applied to a formula whose truth value is constant with\<close>
\<comment> \<open>respect to the state (specifically, always true)\<close>
fun Predicational :: "'b \<Rightarrow> ('a, 'b, 'c) formula" ("Pc")
where "Predicational P = InContext P (Geq (Const 0) (Const 0))"

\<comment> \<open>Abbreviations for common syntactic constructs in order to make axiom definitions, etc. more\<close>
\<comment> \<open>readable.\<close>
context ids begin
\<comment> \<open>"Empty" function argument tuple, encoded as tuple where all arguments assume a constant value.\<close>
definition empty::" 'b \<Rightarrow> ('a, 'b) trm"
where "empty \<equiv> \<lambda>i.(Const 0)"

\<comment> \<open>Function argument tuple with (effectively) one argument, where all others have a constant value.\<close>
fun singleton :: "('a, 'sz) trm \<Rightarrow> ('sz \<Rightarrow> ('a, 'sz) trm)"
where "singleton t i = (if i = vid1 then t else (Const 0))"

lemma expand_singleton:"singleton t = (\<lambda>i. (if i = vid1 then t else (Const 0)))"
  by auto

\<comment> \<open>Function applied to one argument\<close>
definition f1::"'sf \<Rightarrow> 'sz \<Rightarrow> ('sf,'sz) trm"
where "f1 f x = Function f (singleton (Var x))"

\<comment> \<open>Function applied to zero arguments (simulates a constant symbol given meaning by the interpretation)\<close>
definition f0::"'sf \<Rightarrow> ('sf,'sz) trm"
where "f0 f = Function f empty"

\<comment> \<open>Predicate applied to one argument\<close>
definition p1::"'sz \<Rightarrow> 'sz \<Rightarrow> ('sf, 'sc, 'sz) formula"
where "p1 p x = Prop p (singleton (Var x))"

\<comment> \<open>Predicational\<close>
definition P::"'sc \<Rightarrow> ('sf, 'sc, 'sz) formula"
where "P p = Predicational p"
end

subsection \<open>Well-Formedness predicates\<close>
inductive dfree :: "('a, 'c) trm \<Rightarrow> bool"
where
  dfree_Var: "dfree (Var i)"
| dfree_Const: "dfree (Const r)"
| dfree_Fun: "(\<And>i. dfree (args i)) \<Longrightarrow> dfree (Function i args)"
| dfree_Plus: "dfree \<theta>\<^sub>1 \<Longrightarrow> dfree \<theta>\<^sub>2 \<Longrightarrow> dfree (Plus \<theta>\<^sub>1 \<theta>\<^sub>2)"
| dfree_Times: "dfree \<theta>\<^sub>1 \<Longrightarrow> dfree \<theta>\<^sub>2 \<Longrightarrow> dfree (Times \<theta>\<^sub>1 \<theta>\<^sub>2)"
  
inductive dsafe :: "('a, 'c) trm \<Rightarrow> bool"
where
  dsafe_Var: "dsafe (Var i)"
| dsafe_Const: "dsafe (Const r)"
| dsafe_Fun: "(\<And>i. dsafe (args i)) \<Longrightarrow> dsafe (Function i args)"
| dsafe_Plus: "dsafe \<theta>\<^sub>1 \<Longrightarrow> dsafe \<theta>\<^sub>2 \<Longrightarrow> dsafe (Plus \<theta>\<^sub>1 \<theta>\<^sub>2)"
| dsafe_Times: "dsafe \<theta>\<^sub>1 \<Longrightarrow> dsafe \<theta>\<^sub>2 \<Longrightarrow> dsafe (Times \<theta>\<^sub>1 \<theta>\<^sub>2)"
| dsafe_Diff: "dfree \<theta> \<Longrightarrow> dsafe (Differential \<theta>)"
| dsafe_DiffVar: "dsafe ($' i)"

\<comment> \<open>Explictly-written variables that are bound by the ODE. Needed to compute whether\<close>
\<comment> \<open>ODE's are valid (e.g. whether they bind the same variable twice)\<close>
fun ODE_dom::"('a, 'c) ODE \<Rightarrow> 'c set"
where 
  "ODE_dom (OVar c) =  {}"
| "ODE_dom (OSing x \<theta>) = {x}"
| "ODE_dom (OProd ODE1 ODE2) = ODE_dom ODE1 \<union> ODE_dom ODE2"

inductive osafe:: "('a, 'c) ODE \<Rightarrow> bool"
where
  osafe_Var:"osafe (OVar c)"
| osafe_Sing:"dfree \<theta> \<Longrightarrow> osafe (OSing x \<theta>)"
| osafe_Prod:"osafe ODE1 \<Longrightarrow> osafe ODE2 \<Longrightarrow> ODE_dom ODE1 \<inter> ODE_dom ODE2 = {} \<Longrightarrow> osafe (OProd ODE1 ODE2)"

\<comment> \<open>Programs/formulas without any differential terms. This definition not currently used but may\<close>
\<comment> \<open>be useful in the future.\<close>
inductive hpfree:: "('a, 'b, 'c) hp \<Rightarrow> bool"
  and     ffree::  "('a, 'b, 'c) formula \<Rightarrow> bool"
where
  "hpfree (Pvar x)"
| "dfree e \<Longrightarrow> hpfree (Assign x e)"
\<comment> \<open>Differential programs allowed but not differential terms\<close>
| "dfree e \<Longrightarrow> hpfree (DiffAssign x e)"
| "ffree P \<Longrightarrow> hpfree (Test P)" 
\<comment> \<open>Differential programs allowed but not differential terms\<close>
| "osafe ODE \<Longrightarrow> ffree P \<Longrightarrow> hpfree (EvolveODE ODE P)"
| "hpfree a \<Longrightarrow> hpfree b \<Longrightarrow> hpfree (Choice a b )"
| "hpfree a \<Longrightarrow> hpfree b \<Longrightarrow> hpfree (Sequence a b)"
| "hpfree a \<Longrightarrow> hpfree (Loop a)"
| "ffree f \<Longrightarrow> ffree (InContext C f)"
| "(\<And>arg. arg \<in> range args \<Longrightarrow> dfree arg) \<Longrightarrow> ffree (Prop p args)"
| "ffree p \<Longrightarrow> ffree (Not p)"
| "ffree p \<Longrightarrow> ffree q \<Longrightarrow> ffree (And p q)"
| "ffree p \<Longrightarrow> ffree (Exists x p)"
| "hpfree a \<Longrightarrow> ffree p \<Longrightarrow> ffree (Diamond a p)"
| "ffree (Predicational P)"
| "dfree t1 \<Longrightarrow> dfree t2 \<Longrightarrow> ffree (Geq t1 t2)"

inductive hpsafe:: "('a, 'b, 'c) hp \<Rightarrow> bool"
  and     fsafe::  "('a, 'b, 'c) formula \<Rightarrow> bool"
where
   hpsafe_Pvar:"hpsafe (Pvar x)"
 | hpsafe_Assign:"dsafe e \<Longrightarrow> hpsafe (Assign x e)"
 | hpsafe_DiffAssign:"dsafe e \<Longrightarrow> hpsafe (DiffAssign x e)"
 | hpsafe_Test:"fsafe P \<Longrightarrow> hpsafe (Test P)" 
 | hpsafe_Evolve:"osafe ODE \<Longrightarrow> fsafe P \<Longrightarrow> hpsafe (EvolveODE ODE P)"
 | hpsafe_Choice:"hpsafe a \<Longrightarrow> hpsafe b \<Longrightarrow> hpsafe (Choice a b )"
 | hpsafe_Sequence:"hpsafe a \<Longrightarrow> hpsafe b \<Longrightarrow> hpsafe (Sequence a b)"
 | hpsafe_Loop:"hpsafe a \<Longrightarrow> hpsafe (Loop a)"

 | fsafe_Geq:"dsafe t1 \<Longrightarrow> dsafe t2 \<Longrightarrow> fsafe (Geq t1 t2)"
 | fsafe_Prop:"(\<And>i. dsafe (args i)) \<Longrightarrow> fsafe (Prop p args)"
 | fsafe_Not:"fsafe p \<Longrightarrow> fsafe (Not p)"
 | fsafe_And:"fsafe p \<Longrightarrow> fsafe q \<Longrightarrow> fsafe (And p q)"
 | fsafe_Exists:"fsafe p \<Longrightarrow> fsafe (Exists x p)"
 | fsafe_Diamond:"hpsafe a \<Longrightarrow> fsafe p \<Longrightarrow> fsafe (Diamond a p)"
 | fsafe_InContext:"fsafe f \<Longrightarrow> fsafe (InContext C f)"

\<comment> \<open>Auto-generated simplifier rules for safety predicates\<close>
inductive_simps
      dfree_Plus_simps[simp]: "dfree (Plus a b)"
  and dfree_Times_simps[simp]: "dfree (Times a b)"
  and dfree_Var_simps[simp]: "dfree (Var x)"
  and dfree_DiffVar_simps[simp]: "dfree (DiffVar x)"
  and dfree_Differential_simps[simp]: "dfree (Differential x)"
  and dfree_Fun_simps[simp]: "dfree (Function i args)"
  and dfree_Const_simps[simp]: "dfree (Const r)"

inductive_simps
      dsafe_Plus_simps[simp]: "dsafe (Plus a b)"
  and dsafe_Times_simps[simp]: "dsafe (Times a b)"
  and dsafe_Var_simps[simp]: "dsafe (Var x)"
  and dsafe_DiffVar_simps[simp]: "dsafe (DiffVar x)"
  and dsafe_Fun_simps[simp]: "dsafe (Function i args)"
  and dsafe_Diff_simps[simp]: "dsafe (Differential a)"
  and dsafe_Const_simps[simp]: "dsafe (Const r)"

inductive_simps
      osafe_OVar_simps[simp]:"osafe (OVar c)"
  and osafe_OSing_simps[simp]:"osafe (OSing x \<theta>)"
  and osafe_OProd_simps[simp]:"osafe (OProd ODE1 ODE2)"

inductive_simps
      hpsafe_Pvar_simps[simp]: "hpsafe (Pvar a)"
  and hpsafe_Sequence_simps[simp]: "hpsafe (a ;; b)"
  and hpsafe_Loop_simps[simp]: "hpsafe (a**)"
  and hpsafe_ODE_simps[simp]: "hpsafe (EvolveODE ODE p)"
  and hpsafe_Choice_simps[simp]: "hpsafe (a \<union>\<union> b)"
  and hpsafe_Assign_simps[simp]: "hpsafe (Assign x e)"
  and hpsafe_DiffAssign_simps[simp]: "hpsafe (DiffAssign x e)"
  and hpsafe_Test_simps[simp]: "hpsafe (? p)"
  
  and fsafe_Geq_simps[simp]: "fsafe (Geq t1 t2)"
  and fsafe_Prop_simps[simp]: "fsafe (Prop p args)"
  and fsafe_Not_simps[simp]: "fsafe (Not p)"
  and fsafe_And_simps[simp]: "fsafe (And p q)"
  and fsafe_Exists_simps[simp]: "fsafe (Exists x p)"
  and fsafe_Diamond_simps[simp]: "fsafe (Diamond a p)"
  and fsafe_Context_simps[simp]: "fsafe (InContext C p)"

definition Ssafe::"('sf,'sc,'sz) sequent \<Rightarrow> bool"
where "Ssafe S \<longleftrightarrow>((\<forall>i. i \<ge> 0 \<longrightarrow> i < length (fst S) \<longrightarrow> fsafe (nth (fst S) i))
                 \<and>(\<forall>i. i \<ge> 0 \<longrightarrow> i < length (snd S) \<longrightarrow> fsafe (nth (snd S) i)))"

definition Rsafe::"('sf,'sc,'sz) rule \<Rightarrow> bool"
where "Rsafe R \<longleftrightarrow> ((\<forall>i. i \<ge> 0 \<longrightarrow> i < length (fst R) \<longrightarrow> Ssafe (nth (fst R) i)) 
                    \<and> Ssafe (snd R))"
  
\<comment> \<open>Basic reasoning principles about syntactic constructs, including inductive principles\<close>
lemma dfree_is_dsafe: "dfree \<theta> \<Longrightarrow> dsafe \<theta>"
  by (induction rule: dfree.induct) (auto intro: dsafe.intros)
  
lemma hp_induct [case_names Var Assign DiffAssign Test Evolve Choice Compose Star]:
   "(\<And>x. P ($\<alpha> x)) \<Longrightarrow>
    (\<And>x1 x2. P (x1 := x2)) \<Longrightarrow>
    (\<And>x1 x2. P (DiffAssign x1 x2)) \<Longrightarrow>
    (\<And>x. P (? x)) \<Longrightarrow>
    (\<And>x1 x2. P (EvolveODE x1 x2)) \<Longrightarrow>
    (\<And>x1 x2. P x1 \<Longrightarrow> P x2 \<Longrightarrow> P (x1 \<union>\<union> x2)) \<Longrightarrow>
    (\<And>x1 x2. P x1 \<Longrightarrow> P x2 \<Longrightarrow> P (x1 ;; x2)) \<Longrightarrow>
    (\<And>x. P x \<Longrightarrow> P x**) \<Longrightarrow>
     P hp"
  by(induction rule: hp.induct) (auto)

lemma fml_induct:
  "(\<And>t1 t2. P (Geq t1 t2))
  \<Longrightarrow> (\<And>p args. P (Prop p args))
  \<Longrightarrow> (\<And>p. P p \<Longrightarrow> P (Not p))
  \<Longrightarrow> (\<And>p q. P p \<Longrightarrow> P q \<Longrightarrow> P (And p q))
  \<Longrightarrow> (\<And>x p. P p \<Longrightarrow> P (Exists x p))
  \<Longrightarrow> (\<And>a p. P p \<Longrightarrow> P (Diamond a p))
  \<Longrightarrow> (\<And>C p. P p \<Longrightarrow> P (InContext C p))
  \<Longrightarrow> P \<phi>"
  by (induction rule: formula.induct) (auto)

context ids begin
lemma proj_sing1:"(singleton \<theta> vid1) = \<theta>"
  by (auto)

lemma proj_sing2:"vid1 \<noteq> y  \<Longrightarrow> (singleton \<theta> y) = (Const 0)"
  by (auto)
end

end
