(*  Author:     Stefan Berghofer, TU Muenchen, 2003
*)

theory FOL_Fitting
imports Main "HOL-Library.Infinite_Set" "../Assertion_Checker"
begin


section {* Miscellaneous Utilities *}

text {*
Rules for manipulating goals where both the premises and the conclusion
contain conjunctions of similar structure.
*}

theorem conjE': "P \<and> Q \<Longrightarrow> (P \<Longrightarrow> P') \<Longrightarrow> (Q \<Longrightarrow> Q') \<Longrightarrow> P' \<and> Q'"
  by iprover

theorem conjE'': "(\<forall>x. P x \<longrightarrow> Q x \<and> R x) \<Longrightarrow>
  ((\<forall>x. P x \<longrightarrow> Q x) \<Longrightarrow> Q') \<Longrightarrow> ((\<forall>x. P x \<longrightarrow> R x) \<Longrightarrow> R') \<Longrightarrow> Q' \<and> R'"
  by iprover

text {* Some facts about (in)finite sets *}

theorem [simp]: "- A \<inter> B = B - A" by blast

theorem Compl_UNIV_eq: "- A = UNIV - A" by fast

theorem infinite_nonempty: "\<not> finite A \<Longrightarrow> \<exists>x. x \<in> A"
  by (subgoal_tac "A \<noteq> {}") fast+

declare Diff_infinite_finite [simp]


section {* Terms and formulae *}

text {*
\label{sec:terms}
The datatypes of terms and formulae in {\em de Bruijn notation}
are defined as follows:
*}
  
datatype (plugins del: size) 'a "term" =
    Var nat
  | App 'a "'a term list"

datatype (plugins del: size) ('a, 'b) form =
    FF
  | TT
  | Pred 'b "'a term list"
  | And "('a, 'b) form" "('a, 'b) form"
  | Or "('a, 'b) form" "('a, 'b) form"
  | Impl "('a, 'b) form" "('a, 'b) form"
  | Neg "('a, 'b) form"
  | Forall "('a, 'b) form"
  | Exists "('a, 'b) form"

text {*
We use @{text "'a"} and @{text "'b"} to denote the type of
{\em function symbols} and {\em predicate symbols}, respectively.
In applications @{text "App a ts"} and predicates
@{text "Pred a ts"}, the length of @{text "ts"} is considered
to be a part of the function or predicate name, so @{text "App a [t]"}
and @{text "App a [t,u]"} refer to different functions.

The size of a formula is used later for wellfounded induction. The
default implementation provided by the datatype package is not quite
what we need, so here is an alternative version:
*}

primrec size_form :: "('a, 'b) form \<Rightarrow> nat" where
  "size_form FF = 0"
| "size_form TT = 0"
| "size_form (Pred _ _) = 0"
| "size_form (And phi psi) = size_form phi + size_form psi + 1"
| "size_form (Or phi psi) = size_form phi + size_form psi + 1"
| "size_form (Impl phi psi) = size_form phi + size_form psi + 1"
| "size_form (Neg phi) = size_form phi + 1"
| "size_form (Forall phi) = size_form phi + 1"
| "size_form (Exists phi) = size_form phi + 1"


subsection {* Closed terms and formulae *}

text {*
Many of the results proved in the following sections are restricted
to closed terms and formulae. We call a term or formula {\em closed at
level @{text i}}, if it only contains ``loose'' bound variables with
indices smaller than @{text i}.
*}

primrec
  closedt :: "nat \<Rightarrow> 'a term \<Rightarrow> bool"
  and closedts :: "nat \<Rightarrow> 'a term list \<Rightarrow> bool"
where
  "closedt m (Var n) = (n < m)"
| "closedt m (App a ts) = closedts m ts"
| "closedts m [] = True"
| "closedts m (t # ts) = (closedt m t \<and> closedts m ts)"

primrec
  closed :: "nat \<Rightarrow> ('a, 'b) form \<Rightarrow> bool"
where
  "closed m FF = True"
| "closed m TT = True"
| "closed m (Pred b ts) = closedts m ts"
| "closed m (And p q) = (closed m p \<and> closed m q)"
| "closed m (Or p q) = (closed m p \<and> closed m q)"
| "closed m (Impl p q) = (closed m p \<and> closed m q)"
| "closed m (Neg p) = closed m p"
| "closed m (Forall p) = closed (Suc m) p"
| "closed m (Exists p) = closed (Suc m) p"

theorem closedt_mono: assumes le: "i \<le> j"
  shows "closedt i (t::'a term) \<Longrightarrow> closedt j t"
  and "closedts i (ts::'a term list) \<Longrightarrow> closedts j ts" using le
  by (induct t and ts rule: closedt.induct closedts.induct) simp_all


subsection {* Substitution *}

text {*
We now define substitution functions for terms and formulae. When performing
substitutions under quantifiers, we need to {\em lift} the terms to be substituted
for variables, in order for the ``loose'' bound variables to point to the right
position.
*}

primrec
  substt :: "'a term \<Rightarrow> 'a term \<Rightarrow> nat \<Rightarrow> 'a term" ("_[_'/_]" [300, 0, 0] 300)
  and substts :: "'a term list \<Rightarrow> 'a term \<Rightarrow> nat \<Rightarrow> 'a term list" ("_[_'/_]" [300, 0, 0] 300)
where
  "(Var i)[s/k] = (if k < i then Var (i - 1) else if i = k then s else Var i)"
| "(App a ts)[s/k] = App a (ts[s/k])"
| "[][s/k] = []"
| "(t # ts)[s/k] = t[s/k] # ts[s/k]"

primrec
  liftt :: "'a term \<Rightarrow> 'a term"
  and liftts :: "'a term list \<Rightarrow> 'a term list"
where
  "liftt (Var i) = Var (Suc i)"
| "liftt (App a ts) = App a (liftts ts)"
| "liftts [] = []"
| "liftts (t # ts) = liftt t # liftts ts"

primrec
  subst :: "('a, 'b) form \<Rightarrow> 'a term \<Rightarrow> nat \<Rightarrow> ('a, 'b) form" ("_[_'/_]" [300, 0, 0] 300)
where
  "FF[s/k] = FF"
| "TT[s/k] = TT"
| "(Pred b ts)[s/k] = Pred b (ts[s/k])"
| "(And p q)[s/k] = And (p[s/k]) (q[s/k])"
| "(Or p q)[s/k] = Or (p[s/k]) (q[s/k])"
| "(Impl p q)[s/k] = Impl (p[s/k]) (q[s/k])"
| "(Neg p)[s/k] = Neg (p[s/k])"
| "(Forall p)[s/k] = Forall (p[liftt s/Suc k])"
| "(Exists p)[s/k] = Exists (p[liftt s/Suc k])"

theorem lift_closed [simp]:
  "closedt 0 (t::'a term) \<Longrightarrow> closedt 0 (liftt t)"
  "closedts 0 (ts::'a term list) \<Longrightarrow> closedts 0 (liftts ts)"
  by (induct t and ts rule: closedt.induct closedts.induct) simp_all

theorem subst_closedt [simp]: assumes u: "closedt 0 u"
  shows "closedt (Suc i) t \<Longrightarrow> closedt i (t[u/i])"
  and "closedts (Suc i) ts \<Longrightarrow> closedts i (ts[u/i])" using u
  apply (induct t and ts rule: closedt.induct closedts.induct)
  apply simp_all
  apply (rule impI)
  apply (rule closedt_mono(1) [of 0])
  apply simp+
  done

theorem subst_closed [simp]:
  "closedt 0 t \<Longrightarrow> closed (Suc i) p \<Longrightarrow> closed i (p[t/i])"
  by (induct p arbitrary: i t) simp_all

theorem subst_size_form [simp]: "size_form (subst p t i) = size_form p"
  by (induct p arbitrary: i t) auto
  

subsection {* Parameters *}

text {*
The introduction rule @{text ForallI} for the universal quantifier,
as well as the elimination rule @{text ExistsE} for the existential
quantifier introduced in \secref{sec:proof-calculus} require the
quantified variable to be replaced by a ``fresh'' parameter. Fitting's
solution is to use a new nullary function symbol for this purpose.
To express that a function symbol is ``fresh'', we introduce functions
for collecting all function symbols occurring in a term or formula.
*}

primrec
  paramst  :: "'a term \<Rightarrow> 'a set"
  and paramsts :: "'a term list \<Rightarrow> 'a set"
where
  "paramst (Var n) = {}"
| "paramst (App a ts) = {a} \<union> paramsts ts"
| "paramsts [] = {}"
| "paramsts (t # ts) = (paramst t \<union> paramsts ts)"

primrec
  params :: "('a, 'b) form \<Rightarrow> 'a set"
where
  "params FF = {}"
| "params TT = {}"
| "params (Pred b ts) = paramsts ts"
| "params (And p q) = params p \<union> params q"
| "params (Or p q) = params p \<union> params q"
| "params (Impl p q) = params p \<union> params q"
| "params (Neg p) = params p"
| "params (Forall p) = params p"
| "params (Exists p) = params p"

text{*
We also define parameter substitution functions on terms and formulae
that apply a function @{text f} to all function symbols.
*}

primrec
  psubstt :: "('a \<Rightarrow> 'c) \<Rightarrow> 'a term \<Rightarrow> 'c term"
  and psubstts :: "('a \<Rightarrow> 'c) \<Rightarrow> 'a term list \<Rightarrow> 'c term list"
where
  "psubstt f (Var i) = Var i"
| "psubstt f (App x ts) = App (f x) (psubstts f ts)"
| "psubstts f [] = []"
| "psubstts f (t # ts) = psubstt f t # psubstts f ts"

primrec
  psubst :: "('a \<Rightarrow> 'c) \<Rightarrow> ('a, 'b) form \<Rightarrow> ('c, 'b) form"
where
  "psubst f FF = FF"
| "psubst f TT = TT"
| "psubst f (Pred b ts) = Pred b (psubstts f ts)"
| "psubst f (And p q) = And (psubst f p) (psubst f q)"
| "psubst f (Or p q) = Or (psubst f p) (psubst f q)"
| "psubst f (Impl p q) = Impl (psubst f p) (psubst f q)"
| "psubst f (Neg p) = Neg (psubst f p)"
| "psubst f (Forall p) = Forall (psubst f p)"
| "psubst f (Exists p) = Exists (psubst f p)"

theorem psubstt_closed [simp]:
  "closedt i (psubstt f t) = closedt i t"
  "closedts i (psubstts f ts) = closedts i ts"
  by (induct t and ts rule: closedt.induct closedts.induct) simp_all

theorem psubst_closed [simp]:
  "closed i (psubst f p) = closed i p"
  by (induct p arbitrary: i) simp_all

theorem psubstt_subst [simp]:
  "psubstt f (substt t u i) = substt (psubstt f t) (psubstt f u) i"
  "psubstts f (substts ts u i) = substts (psubstts f ts) (psubstt f u) i"
  by (induct t and ts rule: psubstt.induct psubstts.induct) simp_all

theorem psubstt_lift [simp]:
  "psubstt f (liftt t) = liftt (psubstt f t)"
  "psubstts f (liftts ts) = liftts (psubstts f ts)"
  by (induct t and ts rule: psubstt.induct psubstts.induct) simp_all

theorem psubst_subst [simp]:
  "psubst f (subst P t i) = subst (psubst f P) (psubstt f t) i"
  by (induct P arbitrary: i t) simp_all

theorem psubstt_upd [simp]:
  "x \<notin> paramst (t::'a term) \<Longrightarrow> psubstt (f(x:=y)) t = psubstt f t"
  "x \<notin> paramsts (ts::'a term list) \<Longrightarrow> psubstts (f(x:=y)) ts = psubstts f ts"
  by (induct t and ts rule: psubstt.induct psubstts.induct) (auto split: sum.split)

theorem psubst_upd [simp]: "x \<notin> params P \<Longrightarrow> psubst (f(x:=y)) P = psubst f P"
  by (induct P) (simp_all del: fun_upd_apply)

theorem psubstt_id [simp]: "psubstt (%x. x) (t::'a term) = t"
  "psubstts (%x. x) (ts::'a term list) = ts"
  by (induct t and ts rule: psubstt.induct psubstts.induct) simp_all

theorem psubst_id [simp]: "psubst (%x. x) = (%p. p)"
  apply (rule ext)
  apply (induct_tac p)
  apply simp_all
  done

theorem psubstt_image [simp]:
  "paramst (psubstt f t) = f ` paramst t"
  "paramsts (psubstts f ts) = f ` paramsts ts"
  by (induct t and ts rule: paramst.induct paramsts.induct) (simp_all add: image_Un)

theorem psubst_image [simp]: "params (psubst f p) = f ` params p"
  by (induct p) (simp_all add: image_Un)


section {* Semantics *}

text {*
\label{sec:semantics}
In this section, we define evaluation functions for terms and formulae.
Evaluation is performed relative to an environment mapping indices of variables
to values. We also introduce a function, denoted by @{text "e\<langle>i:a\<rangle>"}, for inserting
a value @{text a} at position @{text i} into the environment. All values of variables
with indices less than @{text i} are left untouched by this operation, whereas the
values of variables with indices greater or equal than @{text i} are shifted one
position up.
*}

definition
  shift :: "(nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a"  ("_\<langle>_:_\<rangle>" [90, 0, 0] 91)  where
  "e\<langle>i:a\<rangle> = (\<lambda>j. if j < i then e j else if j = i then a else e (j - 1))"

lemma shift_eq [simp]: "i = j \<Longrightarrow> (e\<langle>i:T\<rangle>) j = T"
  by (simp add: shift_def)

lemma shift_gt [simp]: "j < i \<Longrightarrow> (e\<langle>i:T\<rangle>) j = e j"
  by (simp add: shift_def)

lemma shift_lt [simp]: "i < j \<Longrightarrow> (e\<langle>i:T\<rangle>) j = e (j - 1)"
  by (simp add: shift_def)

lemma shift_commute [simp]: "e\<langle>i:U\<rangle>\<langle>0:T\<rangle> = e\<langle>0:T\<rangle>\<langle>Suc i:U\<rangle>"
  apply (rule ext)
  apply (case_tac x)
   apply simp
  apply (case_tac nat)
   apply (simp_all add: shift_def)
  done

primrec
  evalt :: "(nat \<Rightarrow> 'c) \<Rightarrow> ('a \<Rightarrow> 'c list \<Rightarrow> 'c) \<Rightarrow> 'a term \<Rightarrow> 'c"
  and evalts :: "(nat \<Rightarrow> 'c) \<Rightarrow> ('a \<Rightarrow> 'c list \<Rightarrow> 'c) \<Rightarrow> 'a term list \<Rightarrow> 'c list"
where
  "evalt e f (Var n) = e n"
| "evalt e f (App a ts) = f a (evalts e f ts)"
| "evalts e f [] = []"
| "evalts e f (t # ts) = evalt e f t # evalts e f ts"

primrec
  eval :: "(nat \<Rightarrow> 'c) \<Rightarrow> ('a \<Rightarrow> 'c list \<Rightarrow> 'c) \<Rightarrow>
    ('b \<Rightarrow> 'c list \<Rightarrow> bool) \<Rightarrow> ('a, 'b) form \<Rightarrow> bool"
where
  "eval e f g FF = False"
| "eval e f g TT = True"
| "eval e f g (Pred a ts) = g a (evalts e f ts)"
| "eval e f g (And p q) = ((eval e f g p) \<and> (eval e f g q))"
| "eval e f g (Or p q) = ((eval e f g p) \<or> (eval e f g q))"
| "eval e f g (Impl p q) = ((eval e f g p) \<longrightarrow> (eval e f g q))"
| "eval e f g (Neg p) = (\<not> (eval e f g p))"
| "eval e f g (Forall p) = (\<forall>z. eval (e\<langle>0:z\<rangle>) f g p)"
| "eval e f g (Exists p) = (\<exists>z. eval (e\<langle>0:z\<rangle>) f g p)"

text {*
We write @{text "e,f,g,ps \<Turnstile> p"} to mean that the formula @{text p} is a
semantic consequence of the list of formulae @{text p} with respect to an
environment @{text e} and interpretations @{text f} and @{text g} for
function and predicate symbols, respectively.
*}

definition
  model :: "(nat \<Rightarrow> 'c) \<Rightarrow> ('a \<Rightarrow> 'c list \<Rightarrow> 'c) \<Rightarrow> ('b \<Rightarrow> 'c list \<Rightarrow> bool) \<Rightarrow>
    ('a, 'b) form list \<Rightarrow> ('a, 'b) form \<Rightarrow> bool"  ("_,_,_,_ \<Turnstile> _" [50,50] 50)  where
  "(e,f,g,ps \<Turnstile> p) = (list_all (eval e f g) ps \<longrightarrow> eval e f g p)"

text {*
The following substitution lemmas relate substitution and evaluation functions:
*}

theorem subst_lemma' [simp]:
  "evalt e f (substt t u i) = evalt (e\<langle>i:evalt e f u\<rangle>) f t"
  "evalts e f (substts ts u i) = evalts (e\<langle>i:evalt e f u\<rangle>) f ts"
  by (induct t and ts rule: evalt.induct evalts.induct) simp_all

theorem lift_lemma [simp]:
  "evalt (e\<langle>0:z\<rangle>) f (liftt t) = evalt e f t"
  "evalts (e\<langle>0:z\<rangle>) f (liftts ts) = evalts e f ts"
  by (induct t and ts rule: evalt.induct evalts.induct) simp_all

theorem subst_lemma [simp]:
  "\<And>e i t. eval e f g (subst a t i) = eval (e\<langle>i:evalt e f t\<rangle>) f g a"
  by (induct a) simp_all

theorem upd_lemma' [simp]:
  "n \<notin> paramst t \<Longrightarrow> evalt e (f(n:=x)) t = evalt e f t"
  "n \<notin> paramsts ts \<Longrightarrow> evalts e (f(n:=x)) ts = evalts e f ts"
  by (induct t and ts rule: evalt.induct evalts.induct) auto

theorem upd_lemma [simp]:
  "n \<notin> params p \<Longrightarrow> eval e (f(n:=x)) g p = eval e f g p"
  by (induct p arbitrary: e) simp_all

theorem list_upd_lemma [simp]: "list_all (\<lambda>p. n \<notin> params p) G \<Longrightarrow>
  list_all (eval e (f(n:=x)) g) G = list_all (eval e f g) G"
  by (induct G) simp_all

text {*
In order to test the evaluation function defined above, we apply it
to an example:
*}

theorem ex_all_commute_eval:
  "eval e f g (Impl (Exists (Forall (Pred p [Var 1, Var 0])))
    (Forall (Exists (Pred p [Var 0, Var 1]))))"
  apply simp
txt {*
Simplification yields the following proof state:
@{subgoals [display]}
This is easily proved using intuitionistic logic:
*}
  apply iprover
  done


section {* Proof calculus *}

text {*
\label{sec:proof-calculus}
We now introduce a natural deduction proof calculus for first order logic.
The derivability judgement @{text "G \<turnstile> a"} is defined as an inductive predicate.
*}

inductive
  deriv :: "('a, 'b) form list \<Rightarrow> ('a, 'b) form \<Rightarrow> bool" ("_ \<turnstile> _" [50,50] 50)
where
  Assum: "a \<in> set G \<Longrightarrow> G \<turnstile> a"
| TTI: "G \<turnstile> TT"
| FFE: "G \<turnstile> FF \<Longrightarrow> G \<turnstile> a"
| NegI: "a # G \<turnstile> FF \<Longrightarrow> G \<turnstile> Neg a"
| NegE: "G \<turnstile> Neg a \<Longrightarrow> G \<turnstile> a \<Longrightarrow> G \<turnstile> FF"
| Class: "Neg a # G \<turnstile> FF \<Longrightarrow> G \<turnstile> a"
| AndI: "G \<turnstile> a \<Longrightarrow> G \<turnstile> b \<Longrightarrow> G \<turnstile> And a b"
| AndE1: "G \<turnstile> And a b \<Longrightarrow> G \<turnstile> a"
| AndE2: "G \<turnstile> And a b \<Longrightarrow> G \<turnstile> b"
| OrI1: "G \<turnstile> a \<Longrightarrow> G \<turnstile> Or a b"
| OrI2: "G \<turnstile> b \<Longrightarrow> G \<turnstile> Or a b"
| OrE: "G \<turnstile> Or a b \<Longrightarrow> a # G \<turnstile> c \<Longrightarrow> b # G \<turnstile> c \<Longrightarrow> G \<turnstile> c"
| ImplI: "a # G \<turnstile> b \<Longrightarrow> G \<turnstile> Impl a b"
| ImplE: "G \<turnstile> Impl a b \<Longrightarrow> G \<turnstile> a \<Longrightarrow> G \<turnstile> b"
| ForallI: "G \<turnstile> a[App n []/0] \<Longrightarrow> list_all (\<lambda>p. n \<notin> params p) G \<Longrightarrow>
    n \<notin> params a \<Longrightarrow> G \<turnstile> Forall a"
| ForallE: "G \<turnstile> Forall a \<Longrightarrow> G \<turnstile> a[t/0]"
| ExistsI: "G \<turnstile> a[t/0] \<Longrightarrow> G \<turnstile> Exists a"
| ExistsE: "G \<turnstile> Exists a \<Longrightarrow> a[App n []/0] # G \<turnstile> b \<Longrightarrow>
    list_all (\<lambda>p. n \<notin> params p) G \<Longrightarrow> n \<notin> params a \<Longrightarrow> n \<notin> params b \<Longrightarrow> G \<turnstile> b"

text {*
The following derived inference rules are sometimes useful in applications.
*}

theorem cut: "G \<turnstile> A \<Longrightarrow> A # G \<turnstile> B \<Longrightarrow> G \<turnstile> B"
  by (rule ImplE) (rule ImplI)

theorem cut': "A # G \<turnstile> B \<Longrightarrow> G \<turnstile> A \<Longrightarrow> G \<turnstile> B"
  by (rule ImplE) (rule ImplI)

theorem Class': "Neg A # G \<turnstile> A \<Longrightarrow> G \<turnstile> A"
  apply (rule Class)
  apply (rule_tac A="A" in cut')
  apply (rule_tac a=A in NegE)
  apply (rule Assum)
  apply simp
  apply (rule Assum)
  apply simp
  apply assumption
  done

theorem ForallE': "G \<turnstile> Forall a \<Longrightarrow> subst a t 0 # G \<turnstile> B \<Longrightarrow> G \<turnstile> B"
  by (rule cut) (rule ForallE)

text {*
As an example, we show that the excluded middle, a commutation property
for existential and universal quantifiers, the drinker principle, as well
as Peirce's law are derivable in the calculus given above.
*}

theorem tnd: "[] \<turnstile> Or (Pred p []) (Neg (Pred p []))"
  apply (rule Class)
  apply (rule NegE)
  apply (rule Assum, simp)
  apply (rule OrI2)
  apply (rule NegI)
  apply (rule NegE)
  apply (rule Assum, simp)
  apply (rule OrI1)
  apply (rule Assum, simp)
  done

theorem ex_all_commute:
  "([]::(nat, 'b) form list) \<turnstile> Impl (Exists (Forall (Pred p [Var 1, Var 0])))
     (Forall (Exists (Pred p [Var 0, Var 1])))"
  apply (rule ImplI)
  apply (rule_tac n=0 in ForallI)
  prefer 2
  apply simp
  prefer 2
  apply simp
  apply simp
  apply (rule_tac n=1 and a="Forall (Pred p [Var 1, Var 0])" in ExistsE)
  apply (rule Assum, simp)
  prefer 2
  apply simp
  prefer 2
  apply simp
  prefer 2
  apply simp
  apply simp
  apply (rule_tac t="App 1 []" in ExistsI)
  apply simp
  apply (rule_tac t="App 0 []" and a="Pred p [App (Suc 0) [], Var 0]" in ForallE')
  apply (rule Assum, simp)
  apply (rule Assum, simp)
  done

theorem drinker: "([]::(nat, 'b) form list) \<turnstile>
  Exists (Impl (Pred P [Var 0]) (Forall (Pred P [Var 0])))"
  apply (rule Class')
  apply (rule_tac t="Var 0" in ExistsI)
  apply simp
  apply (rule ImplI)
  apply (rule_tac n=0 in ForallI)
  prefer 2
  apply simp
  prefer 2
  apply simp
  apply simp
  apply (rule Class)
  apply (rule_tac a="Exists (Impl (Pred P [Var 0]) (Forall (Pred P [Var 0])))" in NegE)
  apply (rule Assum, simp)
  apply (rule_tac t="App 0 []" in ExistsI)
  apply simp
  apply (rule ImplI)
  apply (rule FFE)
  apply (rule_tac a="Pred P [App 0 []]" in NegE)
  apply (rule Assum, simp)
  apply (rule Assum, simp)
  done

theorem peirce:
  "[] \<turnstile> Impl (Impl (Impl (Pred P []) (Pred Q [])) (Pred P [])) (Pred P [])"
  apply (rule Class')
  apply (rule ImplI)
  apply (rule_tac a="Impl (Pred P []) (Pred Q [])" in ImplE)
  apply (rule Assum, simp)
  apply (rule ImplI)
  apply (rule FFE)
  apply (rule_tac
    a="Impl (Impl (Impl (Pred P []) (Pred Q [])) (Pred P [])) (Pred P [])"
    in NegE)
  apply (rule Assum, simp)
  apply (rule ImplI)
  apply (rule Assum, simp)
  done


section {* Correctness *}

text {*
The correctness of the proof calculus introduced in \secref{sec:proof-calculus}
can now be proved by induction on the derivation of @{term "G \<turnstile> p"}, using the
substitution rules proved in \secref{sec:semantics}.
*}

theorem correctness: "G \<turnstile> p \<Longrightarrow> \<forall>e f g. e,f,g,G \<Turnstile> p"
  apply (unfold model_def)
  apply (erule deriv.induct)
  apply (rule allI impI)+
  apply (simp add: list_all_iff)
  apply simp_all
  apply blast+
  apply (rule allI impI)+
  apply (erule_tac x=e in allE)
  apply (erule_tac x="f(n:=\<lambda>x. z)" in allE)
  apply (simp del: fun_upd_apply add: fun_upd_same)
  apply iprover
  apply (rule allI impI)+
  apply (erule allE, erule allE, erule allE, erule impE, assumption)
  apply (erule exE)
  apply (erule_tac x=e in allE)
  apply (erule_tac x="f(n:=\<lambda>x. z)" in allE)
  apply (simp del: fun_upd_apply add: fun_upd_same)
  done


section {* Completeness *}

text {*
The goal of this section is to prove completeness of the natural deduction
calculus introduced in \secref{sec:proof-calculus}. Before we start with the
actual proof, it is useful to note that the following two formulations of
completeness are equivalent:
\begin{enumerate}
\item All valid formulae are derivable, i.e.
  @{text "ps \<Turnstile> p \<Longrightarrow> ps \<turnstile> p"}
\item All consistent sets are satisfiable
\end{enumerate}
The latter property is called the {\em model existence theorem}. To see why 2
implies 1, observe that @{text "Neg p, ps \<notturnstile> FF"} implies
that @{text "Neg p, ps"} is consistent, which, by the model existence theorem,
implies that @{text "Neg p, ps"} has a model, which in turn implies that
@{text "ps \<notTurnstile> p"}. By contraposition, it therefore follows
from @{text "ps \<Turnstile> p"} that @{text "Neg p, ps \<turnstile> FF"}, which allows us to
deduce @{text "ps \<turnstile> p"} using rule @{text Class}.

In most textbooks on logic, a set @{text S} of formulae is called {\em consistent},
if no contradiction can be derived from @{text S} using a {\em specific proof calculus},
i.e.\ @{text "S \<notturnstile> FF"}. Rather than defining consistency relative to
a {\em specific} calculus, Fitting uses the more general approach of describing
properties that all consistent sets must have (see \secref{sec:consistent-sets}).

The key idea behind the proof of the model existence theorem is to
extend a consistent set to one that is {\em maximal} (see \secref{sec:extend}).
In order to do this, we use the fact that the set of formulae is enumerable
(see \secref{sec:enumeration}), which allows us to form a sequence
$\phi_0$, $\phi_1$, $\phi_2$, $\ldots$ containing all formulae.
We can then construct a sequence $S_i$ of consistent sets as follows:
\[
\begin{array}{l}
  S_0 = S \\
  S_{i+1} = \left\{\begin{array}{ll}
    S_i \cup \{\phi_i\} & \hbox{if } S_i \cup \{\phi_i\} \hbox{ consistent} \\
    S_i & \hbox{otherwise}
  \end{array}\right.
\end{array}
\]
To obtain a maximal consistent set, we form the union $\bigcup_i S_i$ of these
sets. To ensure that this union is still consistent, additional closure
(see \secref{sec:closure}) and finiteness (see \secref{sec:finiteness})
properties are needed.
It can be shown that a maximal consistent set is a {\em Hintikka set}
(see \secref{sec:hintikka}). Hintikka sets are satisfiable in {\em Herbrand}
models, where closed terms coincide with their interpretation.
*}


subsection {* Consistent sets *}

text {*
\label{sec:consistent-sets}
In this section, we describe an abstract criterion for consistent sets.
A set of sets of formulae is called a {\em consistency property}, if the
following holds:
*}

definition
  consistency :: "('a, 'b) form set set \<Rightarrow> bool" where
  "consistency C = (\<forall>S. S \<in> C \<longrightarrow>
     (\<forall>p ts. \<not> (Pred p ts \<in> S \<and> Neg (Pred p ts) \<in> S)) \<and>
     FF \<notin> S \<and> Neg TT \<notin> S \<and>
     (\<forall>Z. Neg (Neg Z) \<in> S \<longrightarrow> S \<union> {Z} \<in> C) \<and>
     (\<forall>A B. And A B \<in> S \<longrightarrow> S \<union> {A, B} \<in> C) \<and>
     (\<forall>A B. Neg (Or A B) \<in> S \<longrightarrow> S \<union> {Neg A, Neg B} \<in> C) \<and>
     (\<forall>A B. Or A B \<in> S \<longrightarrow> S \<union> {A} \<in> C \<or> S \<union> {B} \<in> C) \<and>
     (\<forall>A B. Neg (And A B) \<in> S \<longrightarrow> S \<union> {Neg A} \<in> C \<or> S \<union> {Neg B} \<in> C) \<and>
     (\<forall>A B. Impl A B \<in> S \<longrightarrow> S \<union> {Neg A} \<in> C \<or> S \<union> {B} \<in> C) \<and>
     (\<forall>A B. Neg (Impl A B) \<in> S \<longrightarrow> S \<union> {A, Neg B} \<in> C) \<and>
     (\<forall>P t. closedt 0 t \<longrightarrow> Forall P \<in> S \<longrightarrow> S \<union> {P[t/0]} \<in> C) \<and>
     (\<forall>P t. closedt 0 t \<longrightarrow> Neg (Exists P) \<in> S \<longrightarrow> S \<union> {Neg (P[t/0])} \<in> C) \<and>
     (\<forall>P. Exists P \<in> S \<longrightarrow> (\<exists>x. S \<union> {P[App x []/0]} \<in> C)) \<and>
     (\<forall>P. Neg (Forall P) \<in> S \<longrightarrow> (\<exists>x. S \<union> {Neg (P[App x []/0])} \<in> C)))"

text {*
In \secref{sec:finiteness}, we will show how to extend a consistency property
to one that is of {\em finite character}. However, the above
definition of a consistency property cannot be used for this, since there is
a problem with the treatment of formulae of the form @{text "Exists P"} and
@{text "Neg (Forall P)"}. Fitting therefore suggests to define an {\em alternative
consistency property} as follows:
*}

definition
  alt_consistency :: "('a, 'b) form set set \<Rightarrow> bool" where
  "alt_consistency C = (\<forall>S. S \<in> C \<longrightarrow>
     (\<forall>p ts. \<not> (Pred p ts \<in> S \<and> Neg (Pred p ts) \<in> S)) \<and>
     FF \<notin> S \<and> Neg TT \<notin> S \<and>
     (\<forall>Z. Neg (Neg Z) \<in> S \<longrightarrow> S \<union> {Z} \<in> C) \<and>
     (\<forall>A B. And A B \<in> S \<longrightarrow> S \<union> {A, B} \<in> C) \<and>
     (\<forall>A B. Neg (Or A B) \<in> S \<longrightarrow> S \<union> {Neg A, Neg B} \<in> C) \<and>
     (\<forall>A B. Or A B \<in> S \<longrightarrow> S \<union> {A} \<in> C \<or> S \<union> {B} \<in> C) \<and>
     (\<forall>A B. Neg (And A B) \<in> S \<longrightarrow> S \<union> {Neg A} \<in> C \<or> S \<union> {Neg B} \<in> C) \<and>
     (\<forall>A B. Impl A B \<in> S \<longrightarrow> S \<union> {Neg A} \<in> C \<or> S \<union> {B} \<in> C) \<and>
     (\<forall>A B. Neg (Impl A B) \<in> S \<longrightarrow> S \<union> {A, Neg B} \<in> C) \<and>
     (\<forall>P t. closedt 0 t \<longrightarrow> Forall P \<in> S \<longrightarrow> S \<union> {P[t/0]} \<in> C) \<and>
     (\<forall>P t. closedt 0 t \<longrightarrow> Neg (Exists P) \<in> S \<longrightarrow> S \<union> {Neg (P[t/0])} \<in> C) \<and>
     (\<forall>P x. (\<forall>a\<in>S. x \<notin> params a) \<longrightarrow> Exists P \<in> S \<longrightarrow>
       S \<union> {P[App x []/0]} \<in> C) \<and>
     (\<forall>P x. (\<forall>a\<in>S. x \<notin> params a) \<longrightarrow> Neg (Forall P) \<in> S \<longrightarrow>
       S \<union> {Neg (P[App x []/0])} \<in> C))"

text {*
Note that in the clauses for @{text "Exists P"} and @{text "Neg (Forall P)"},
the first definition requires the existence of a parameter @{text x} with a certain
property, whereas the second definition requires that all parameters @{text x} that
are new for @{text S} have a certain property. A consistency property can easily be
turned into an alternative consistency property by applying a suitable parameter
substitution:
*}

definition
  mk_alt_consistency :: "('a, 'b) form set set \<Rightarrow> ('a, 'b) form set set" where
  "mk_alt_consistency C = {S. \<exists>f. psubst f ` S \<in> C}"

theorem alt_consistency:
  "consistency C \<Longrightarrow> alt_consistency (mk_alt_consistency C)"
  apply (simp add: consistency_def alt_consistency_def mk_alt_consistency_def)
  apply (rule allI)
  apply (rule impI)
  apply (erule exE)
  apply (erule allE impE)+
  apply assumption
  apply (erule conjE')
  apply (rule allI impI notI)+
  apply (erule allE impE)+
  apply (rule image_eqI)
  prefer 2
  apply assumption
  apply (rule psubst.simps [symmetric])
  apply (erule notE)
  apply (rule image_eqI)
  prefer 2
  apply (rotate_tac -1)
  apply assumption
  apply simp
  apply (erule conjE')
  apply (rule notI)
  apply (erule notE)
  apply (rule image_eqI)
  prefer 2
  apply assumption
  apply simp
  apply (erule conjE')
  apply (rule notI)
  apply (erule notE)
  apply (rule image_eqI)
  prefer 2
  apply assumption
  apply simp
  apply (erule conjE')
  apply (rule allI impI)+
  apply (erule allE impE)+
  apply (rule image_eqI)
  prefer 2
  apply assumption
  apply simp
  apply (erule exI)
  apply (erule conjE')
  apply (rule allI impI)+
  apply (erule allE impE)+
  apply (rule image_eqI)
  prefer 2
  apply assumption
  apply (rule psubst.simps [symmetric])
  apply iprover
  apply (erule conjE')
  apply (rule allI impI)+
  apply (erule allE impE)+
  apply (rule image_eqI)
  prefer 2
  apply assumption
  apply simp
  apply iprover
  apply (erule conjE')
  apply (rule allI impI)+
  apply (erule allE impE)+
  apply (rule image_eqI)
  prefer 2
  apply assumption
  apply (rule psubst.simps [symmetric])
  apply iprover
  apply (erule conjE')
  apply (rule allI impI)+
  apply (erule allE impE)+
  apply (rule image_eqI)
  prefer 2
  apply assumption
  apply simp
  apply iprover
  apply (erule conjE')
  apply (rule allI impI)+
  apply (erule allE impE)+
  apply (rule image_eqI)
  prefer 2
  apply assumption
  apply simp
  apply iprover
  apply (erule conjE')
  apply (rule allI impI)+
  apply (erule allE impE)+
  apply (rule image_eqI)
  prefer 2
  apply assumption
  apply simp
  apply iprover
  apply (erule conjE')
  apply (rule allI impI)+
  apply (erule allE)
  apply (erule_tac x="psubstt f t" in allE)
  apply (erule impE)
  apply simp
  apply (erule impE)
  apply (rule image_eqI)
  prefer 2
  apply assumption
  apply simp
  apply (erule exI)
  apply (erule conjE')
  apply (rule allI impI)+
  apply (erule allE)
  apply (erule_tac x="psubstt f t" in allE)
  apply (erule impE)
  apply simp
  apply (erule impE)
  apply (rule image_eqI)
  prefer 2
  apply assumption
  apply simp
  apply (erule exI)
  apply (erule conjE')
  apply (rule allI impI)+
  apply (erule allE impE)+
  apply (rule image_eqI)
  prefer 2
  apply assumption
  apply simp
  apply (erule exE)
  apply (rule_tac x="f(x:=xa)" in exI)
  apply (frule bspec)
  apply assumption
  apply (simp cong add: image_cong)
  apply (rule allI impI)+
  apply (erule allE impE)+
  apply (rule image_eqI)
  prefer 2
  apply assumption
  apply simp
  apply (erule exE)
  apply (rule_tac x="f(x:=xa)" in exI)
  apply (frule bspec)
  apply assumption
  apply (simp cong add: image_cong)
  done

theorem mk_alt_consistency_subset: "C \<subseteq> mk_alt_consistency C"
  apply (unfold mk_alt_consistency_def)
  apply (rule subsetI)
  apply (rule CollectI)
  apply (rule_tac x="%x. x" in exI)
  apply simp
  done


subsection {* Closure under subsets *}

text {*
\label{sec:closure}
We now show that a consistency property can be extended to one
that is closed under subsets.
*}

definition
  close :: "('a, 'b) form set set \<Rightarrow> ('a, 'b) form set set" where
  "close C = {S. \<exists>S' \<in> C. S \<subseteq> S'}"

definition
  subset_closed :: "'a set set \<Rightarrow> bool" where
  "subset_closed C = (\<forall>S' \<in> C. \<forall>S. S \<subseteq> S' \<longrightarrow> S \<in> C)"

theorem close_consistency: "consistency C \<Longrightarrow> consistency (close C)"
  apply (simp add: close_def consistency_def)
  apply (rule allI)
  apply (rule impI)
  apply (erule bexE)
  apply (erule allE impE)+
  apply assumption
  apply (erule conjE', blast)
  apply (erule conjE', blast)
  apply (erule conjE', blast)
  apply (erule conjE', blast)
  apply (erule conjE', blast)
  apply (erule conjE', blast)
  apply (erule conjE')
  apply (rule allI impI)+
  apply (erule allE impE)+
  apply (erule subsetD)
  apply assumption
  apply (erule disjE)
  apply (rule disjI1)
  apply (rule_tac x="insert A x" in bexI)
  apply blast
  apply assumption
  apply (rule disjI2)
  apply (rule_tac x="insert B x" in bexI)
  apply blast
  apply assumption
  apply (erule conjE')
  apply (rule allI impI)+
  apply (erule allE impE)+
  apply (erule subsetD)
  apply assumption
  apply (erule disjE)
  apply (rule disjI1)
  apply (rule_tac x="insert (Neg A) x" in bexI)
  apply blast
  apply assumption
  apply (rule disjI2)
  apply (rule_tac x="insert (Neg B) x" in bexI)
  apply blast
  apply assumption
  apply (erule conjE')
  apply (rule allI impI)+
  apply (erule allE impE)+
  apply (erule subsetD)
  apply assumption
  apply (erule disjE)
  apply (rule disjI1)
  apply (rule_tac x="insert (Neg A) x" in bexI)
  apply blast
  apply assumption
  apply (rule disjI2)
  apply (rule_tac x="insert B x" in bexI)
  apply blast
  apply assumption
  apply (erule conjE', blast)
  apply (erule conjE', blast)
  apply (erule conjE', blast)
  apply (erule conjE')
  apply (rule allI impI)+
  apply (erule allE impE)+
  apply (erule subsetD)
  apply assumption
  apply blast
  apply (rule allI impI)+
  apply (erule allE impE)+
  apply (erule subsetD)
  apply assumption
  apply blast
  done

theorem close_closed: "subset_closed (close C)"
  by (unfold close_def subset_closed_def) blast

theorem close_subset: "C \<subseteq> close C"
  by (unfold close_def) blast

text {*
If a consistency property @{text C} is closed under subsets, so is the
corresponding alternative consistency property:
*}

theorem mk_alt_consistency_closed:
  "subset_closed C \<Longrightarrow> subset_closed (mk_alt_consistency C)"
  apply (unfold mk_alt_consistency_def subset_closed_def)
  apply (rule ballI allI impI)+
  apply (rule CollectI)
  apply (erule CollectE)
  apply (erule exE)
  apply (subgoal_tac "psubst f ` S \<subseteq> psubst f ` S'")
  apply blast+
  done


subsection {* Finite character *}

text {*
\label{sec:finiteness}
In this section, we show that an alternative consistency property can
be extended to one of finite character. A set of sets @{text C} is said
to be of finite character, provided that @{text S} is a member of @{text C}
if and only if every subset of @{text S} is.
*}

definition
  finite_char :: "'a set set \<Rightarrow> bool" where
  "finite_char C = (\<forall>S. S \<in> C = (\<forall>S'. finite S' \<longrightarrow> S' \<subseteq> S \<longrightarrow> S' \<in> C))"

definition
  mk_finite_char :: "'a set set \<Rightarrow> 'a set set" where
  "mk_finite_char C = {S. \<forall>S'. S' \<subseteq> S \<longrightarrow> finite S' \<longrightarrow> S' \<in> C}"

theorem finite_alt_consistency:
  "alt_consistency C \<Longrightarrow> subset_closed C \<Longrightarrow> alt_consistency (mk_finite_char C)"
  apply (unfold alt_consistency_def subset_closed_def mk_finite_char_def)
  apply (rule allI impI)+
  apply (erule CollectE)
  apply (erule conjE'')
  apply (rule allI notI)+
  apply (rotate_tac 1)
  apply (erule_tac x="{Pred p ts, Neg (Pred p ts)}" in allE)
  apply blast
  apply (erule conjE'')
  apply (rotate_tac 1)
  apply (erule_tac x="{FF}" in allE)
  apply blast
  apply (erule conjE'')
  apply (rotate_tac 1)
  apply (erule_tac x="{Neg TT}" in allE)
  apply blast
  apply (erule conjE'')
  apply (rule allI impI CollectI)+
  apply (rotate_tac 1)
  apply (erule_tac x="S' - {Z} \<union> {Neg (Neg Z)}" in allE)
  apply (erule impE)
  apply blast
  apply (erule impE)
  apply (simp (no_asm))
  apply (erule allE)
  apply (erule impE)
  apply assumption
  apply (erule_tac x=Z in allE)
  apply (erule impE)
  apply (simp (no_asm))
  apply (drule_tac x="S' - {Z} \<union> {Neg (Neg Z)} \<union> {Z}" in bspec)
  apply assumption
  apply blast
  apply (erule conjE'')
  apply (rule allI impI CollectI)+
  apply (rotate_tac 1)
  apply (erule_tac x="S' - {A, B} \<union> {And A B}" in allE)
  apply (erule impE)
  apply blast
  apply (erule impE)
  apply (simp (no_asm))
  apply (erule allE)
  apply (erule impE)
  apply assumption
  apply (erule_tac x=A in allE)
  apply (erule_tac x=B in allE)
  apply (erule impE)
  apply (simp (no_asm))
  apply (drule_tac x="S' - {A, B} \<union> {And A B} \<union> {A, B}" in bspec)
  apply assumption
  apply blast
  apply (erule conjE'')
  apply (rule allI impI CollectI)+
  apply (rotate_tac 1)
  apply (erule_tac x="S' - {Neg A, Neg B} \<union> {Neg (Or A B)}" in allE)
  apply (erule impE)
  apply blast
  apply (erule impE)
  apply (simp (no_asm))
  apply (erule allE)
  apply (erule impE)
  apply assumption
  apply (erule_tac x=A in allE)
  apply (erule_tac x=B in allE)
  apply (erule impE)
  apply (simp (no_asm))
  apply (drule_tac x="S' - {Neg A, Neg B} \<union> {Neg (Or A B)} \<union> {Neg A, Neg B}" in bspec)
  apply assumption
  apply blast
  apply (erule conjE'')
  apply (rule allI impI)+
  apply (rule ccontr)
  apply (simp (no_asm_use))
  apply (erule conjE exE)+
  apply (rotate_tac 1)
  apply (erule_tac x="(S' - {A}) \<union> (S'a - {B}) \<union> {Or A B}" in allE)
  apply (erule impE)
  apply blast
  apply (erule impE)
  apply (simp (no_asm_simp))
  apply (erule allE)
  apply (erule impE)
  apply assumption
  apply (erule_tac x=A in allE)
  apply (erule_tac x=B in allE)
  apply (erule impE)
  apply (simp (no_asm))
  apply (erule disjE)
  apply (drule_tac x="insert A (S' - {A} \<union> (S'a - {B}) \<union> {Or A B})" in bspec)
  apply assumption
  apply blast
  apply (drule_tac x="insert B (S' - {A} \<union> (S'a - {B}) \<union> {Or A B})" in bspec)
  apply assumption
  apply blast
  apply (erule conjE'')
  apply (rule allI impI)+
  apply (rule ccontr)
  apply (simp (no_asm_use))
  apply (erule conjE exE)+
  apply (rotate_tac 1)
  apply (erule_tac x="(S' - {Neg A}) \<union> (S'a - {Neg B}) \<union> {Neg (And A B)}" in allE)
  apply (erule impE)
  apply blast
  apply (erule impE)
  apply (simp (no_asm_simp))
  apply (erule allE)
  apply (erule impE)
  apply assumption
  apply (erule_tac x=A in allE)
  apply (erule_tac x=B in allE)
  apply (erule impE)
  apply (simp (no_asm))
  apply (erule disjE)
  apply (drule_tac x="insert (Neg A) (S' - {Neg A} \<union> (S'a - {Neg B}) \<union> {Neg (And A B)})" in bspec)
  apply assumption
  apply blast
  apply (drule_tac x="insert (Neg B) (S' - {Neg A} \<union> (S'a - {Neg B}) \<union> {Neg (And A B)})" in bspec)
  apply assumption
  apply blast
  apply (erule conjE'')
  apply (rule allI impI)+
  apply (rule ccontr)
  apply (simp (no_asm_use))
  apply (erule conjE exE)+
  apply (rotate_tac 1)
  apply (erule_tac x="(S' - {Neg A}) \<union> (S'a - {B}) \<union> {Impl A B}" in allE)
  apply (erule impE)
  apply blast
  apply (erule impE)
  apply (simp (no_asm_simp))
  apply (erule allE)
  apply (erule impE)
  apply assumption
  apply (erule_tac x=A in allE)
  apply (erule_tac x=B in allE)
  apply (erule impE)
  apply (simp (no_asm))
  apply (erule disjE)
  apply (drule_tac x="insert (Neg A) (S' - {Neg A} \<union> (S'a - {B}) \<union> {Impl A B})" in bspec)
  apply assumption
  apply blast
  apply (drule_tac x="insert B (S' - {Neg A} \<union> (S'a - {B}) \<union> {Impl A B})" in bspec)
  apply assumption
  apply blast
  apply (erule conjE'')
  apply (rule allI impI CollectI)+
  apply (rotate_tac 1)
  apply (erule_tac x="S' - {A, Neg B} \<union> {Neg (Impl A B)}" in allE)
  apply (erule impE)
  apply blast
  apply (erule impE)
  apply (simp (no_asm))
  apply (erule allE)
  apply (erule impE)
  apply assumption
  apply (erule_tac x=A in allE)
  apply (erule_tac x=B in allE)
  apply (erule impE)
  apply (simp (no_asm))
  apply (drule_tac x="S' - {A, Neg B} \<union> {Neg (Impl A B)} \<union> {A, Neg B}" in bspec)
  apply assumption
  apply blast
  apply (erule conjE'')
  apply (rule allI impI CollectI)+
  apply (rotate_tac 1)
  apply (erule_tac x="S' - {subst P t 0} \<union> {Forall P}" in allE)
  apply (erule impE)
  apply blast
  apply (erule impE)
  apply (simp (no_asm))
  apply (erule allE)
  apply (erule impE)
  apply assumption
  apply (erule_tac x=P in allE)
  apply (erule_tac x=t in allE)
  apply (erule impE)
  apply assumption
  apply (drule_tac x="S' - {subst P t 0} \<union> {Forall P} \<union> {subst P t 0}" in bspec)
  apply blast
  apply blast
  apply (erule conjE'')
  apply (rule allI impI CollectI)+
  apply (rotate_tac 1)
  apply (erule_tac x="S' - {Neg (subst P t 0)} \<union> {Neg (Exists P)}" in allE)
  apply (erule impE)
  apply blast
  apply (erule impE)
  apply (simp (no_asm))
  apply (erule allE)
  apply (erule impE)
  apply assumption
  apply (erule_tac x=P in allE)
  apply (erule_tac x=t in allE)
  apply (erule impE)
  apply assumption
  apply (drule_tac x="S' - {Neg (subst P t 0)} \<union> {Neg (Exists P)} \<union> {Neg (subst P t 0)}" in bspec)
  apply blast
  apply blast
  apply (erule conjE'')
  apply (rule allI impI CollectI)+
  apply (rotate_tac 1)
  apply (erule_tac x="S' - {subst P (App x []) 0} \<union> {Exists P}" in allE)
  apply (erule impE)
  apply blast
  apply (erule impE)
  apply (simp (no_asm))
  apply (erule allE)
  apply (erule impE)
  apply assumption
  apply (erule_tac x=P in allE)
  apply (erule_tac x=x in allE)
  apply (erule impE)
  apply blast
  apply (drule_tac x="S' - {subst P (App x []) 0} \<union> {Exists P} \<union> {subst P (App x []) 0}" in bspec)
  apply blast
  apply blast
  apply (rule allI impI CollectI)+
  apply (rotate_tac 1)
  apply (erule_tac x="S' - {Neg (subst P (App x []) 0)} \<union> {Neg (Forall P)}" in allE)
  apply (erule impE)
  apply blast
  apply (erule impE)
  apply (simp (no_asm))
  apply (erule allE)
  apply (erule impE)
  apply assumption
  apply (erule_tac x=P in allE)
  apply (erule_tac x=x in allE)
  apply (erule impE)
  apply blast
  apply (drule_tac x="S' - {Neg (subst P (App x []) 0)} \<union> {Neg (Forall P)} \<union> {Neg (subst P (App x []) 0)}" in bspec)
  apply blast
  apply blast
  done

theorem finite_char: "finite_char (mk_finite_char C)"
  by (unfold finite_char_def mk_finite_char_def) blast

theorem finite_char_closed: "finite_char C \<Longrightarrow> subset_closed C"
  apply (unfold finite_char_def subset_closed_def)
  apply (rule ballI allI impI)+
  apply (frule spec)
  apply (erule iffD2)
  apply blast
  done

theorem finite_char_subset: "subset_closed C \<Longrightarrow> C \<subseteq> mk_finite_char C"
  by (unfold mk_finite_char_def subset_closed_def) blast


subsection {* Enumerating datatypes *}

text {*
\label{sec:enumeration}
In the following section, we will show that elements of datatypes
can be enumerated. This will be done by specifying functions that
map natural numbers to elements of datatypes and vice versa.
*}

subsubsection {* Enumerating pairs of natural numbers *}

text {*
\begin{figure}
\begin{center}
\includegraphics[scale=0.6]{diag}
\end{center}
\caption{Cantor's method for enumerating sets of pairs}\label{fig:diag}
\end{figure}
As a starting point, we show that pairs of natural numbers are enumerable.
For this purpose, we use a method due to Cantor, which is illustrated in
\figref{fig:diag}. The function for mapping natural numbers to pairs of
natural numbers can be characterized recursively as follows:
*}

primrec
  diag :: "nat \<Rightarrow> (nat \<times> nat)"
where
  "diag 0 = (0, 0)"
| "diag (Suc n) =
     (let (x, y) = diag n
      in case y of
          0 \<Rightarrow> (0, Suc x)
        | Suc y \<Rightarrow> (Suc x, y))"

theorem diag_le1: "fst (diag (Suc n)) < Suc n"
  by (induct n) (simp_all add: Let_def split_def split: nat.split)

theorem diag_le2: "snd (diag (Suc (Suc n))) < Suc (Suc n)"
  apply (induct n)
  apply (simp_all add: Let_def split_def split: nat.split nat.split_asm)
  apply (rule impI)
  apply (case_tac n)
  apply simp assert_nth_true 74
  apply hypsubst
  apply (rule diag_le1)
  done

theorem diag_le3: "fst (diag n) = Suc x \<Longrightarrow> snd (diag n) < n"
  apply (case_tac n)
  apply simp
  apply (case_tac nat)
  apply (simp add: Let_def)
  apply hypsubst
  apply (rule diag_le2)
  done

theorem diag_le4: "fst (diag n) = Suc x \<Longrightarrow> x < n"
  apply (case_tac n)
  apply simp
  apply (case_tac nat)
  apply (simp add: Let_def)
  apply hypsubst_thin
  apply (drule sym)
  apply (drule ord_eq_less_trans)
  apply (rule diag_le1)
  apply simp
  done

function
  undiag :: "nat \<times> nat \<Rightarrow> nat"
where
  "undiag (0, 0) = 0"
| "undiag (0, Suc y) = Suc (undiag (y, 0))"
| "undiag (Suc x, y) = Suc (undiag (x, Suc y))"
  by pat_completeness auto

termination
  by (relation "measure (\<lambda>(x, y). ((x + y) * (x + y + 1)) div 2 + x)") auto

theorem diag_undiag [simp]: "diag (undiag (x, y)) = (x, y)"
  by (rule undiag.induct) (simp add: Let_def)+


subsubsection {* Enumerating trees *}

text {*
When writing enumeration functions for datatypes, it is useful to
note that all datatypes are some kind of trees. In order to
avoid re-inventing the wheel, we therefore write enumeration functions
for trees once and for all. In applications, we then only have to write
functions for converting between trees and concrete datatypes.
*}

datatype btree = Leaf nat | Branch btree btree

function
  diag_btree :: "nat \<Rightarrow> btree"
where
  "diag_btree n = (case fst (diag n) of
       0 \<Rightarrow> Leaf (snd (diag n))
     | Suc x \<Rightarrow> Branch (diag_btree x) (diag_btree (snd (diag n))))"
  by auto

termination
  by (relation "measure (\<lambda>x. x)") (auto intro: diag_le3 diag_le4)

primrec
  undiag_btree :: "btree \<Rightarrow> nat"
where
  "undiag_btree (Leaf n) = undiag (0, n)"
| "undiag_btree (Branch t1 t2) =
     undiag (Suc (undiag_btree t1), undiag_btree t2)"

theorem diag_undiag_btree [simp]: "diag_btree (undiag_btree t) = t"
  by (induct t) (simp_all add: Let_def)

declare diag_btree.simps [simp del] undiag_btree.simps [simp del]


subsubsection {* Enumerating lists *}

fun
  list_of_btree :: "(nat \<Rightarrow> 'a) \<Rightarrow> btree \<Rightarrow> 'a list"
where
  "list_of_btree f (Leaf x) = []"
| "list_of_btree f (Branch (Leaf n) t) = f n # list_of_btree f t"

primrec
  btree_of_list :: "('a \<Rightarrow> nat) \<Rightarrow> 'a list \<Rightarrow> btree"
where
  "btree_of_list f [] = Leaf 0"
| "btree_of_list f (x # xs) = Branch (Leaf (f x)) (btree_of_list f xs)"

definition
  diag_list :: "(nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a list" where
  "diag_list f n = list_of_btree f (diag_btree n)"

definition
  undiag_list :: "('a \<Rightarrow> nat) \<Rightarrow> 'a list \<Rightarrow> nat" where
  "undiag_list f xs = undiag_btree (btree_of_list f xs)"

theorem diag_undiag_list [simp]:
  "(\<And>x. d (u x) = x) \<Longrightarrow> diag_list d (undiag_list u xs) = xs"
  by (induct xs) (simp_all add: diag_list_def undiag_list_def)


subsubsection {* Enumerating terms *}

fun
  term_of_btree :: "(nat \<Rightarrow> 'a) \<Rightarrow> btree \<Rightarrow> 'a term"
  and term_list_of_btree :: "(nat \<Rightarrow> 'a) \<Rightarrow> btree \<Rightarrow> 'a term list"
where
  "term_of_btree f (Leaf m) = Var m"
| "term_of_btree f (Branch (Leaf m) t) =
     App (f m) (term_list_of_btree f t)"
| "term_list_of_btree f (Leaf m) = []"
| "term_list_of_btree f (Branch t1 t2) =
     term_of_btree f t1 # term_list_of_btree f t2"

primrec
  btree_of_term :: "('a \<Rightarrow> nat) \<Rightarrow> 'a term \<Rightarrow> btree"
  and btree_of_term_list :: "('a \<Rightarrow> nat) \<Rightarrow> 'a term list \<Rightarrow> btree"
where
  "btree_of_term f (Var m) = Leaf m"
| "btree_of_term f (App m ts) = Branch (Leaf (f m)) (btree_of_term_list f ts)"
| "btree_of_term_list f [] = Leaf 0"
| "btree_of_term_list f (t # ts) = Branch (btree_of_term f t) (btree_of_term_list f ts)"

theorem term_btree: assumes du: "\<And>x. d (u x) = x"
  shows "term_of_btree d (btree_of_term u t) = t"
  and "term_list_of_btree d (btree_of_term_list u ts) = ts"
  by (induct t and ts rule: btree_of_term.induct btree_of_term_list.induct) (simp_all add: du)

definition
  diag_term :: "(nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a term" where
  "diag_term f n = term_of_btree f (diag_btree n)"

definition
  undiag_term :: "('a \<Rightarrow> nat) \<Rightarrow> 'a term \<Rightarrow> nat" where
  "undiag_term f t = undiag_btree (btree_of_term f t)"

theorem diag_undiag_term [simp]:
  "(\<And>x. d (u x) = x) \<Longrightarrow> diag_term d (undiag_term u t) = t"
  by (simp add: diag_term_def undiag_term_def term_btree)

fun
  form_of_btree :: "(nat \<Rightarrow> 'a) \<Rightarrow> (nat \<Rightarrow> 'b) \<Rightarrow> btree \<Rightarrow> ('a, 'b) form"
where
  "form_of_btree f g (Leaf 0) = FF"
| "form_of_btree f g (Leaf (Suc 0)) = TT"
| "form_of_btree f g (Branch (Leaf 0) (Branch (Leaf m) (Leaf n))) =
     Pred (g m) (diag_list (diag_term f) n)"
| "form_of_btree f g (Branch (Leaf (Suc 0)) (Branch t1 t2)) =
     And (form_of_btree f g t1) (form_of_btree f g t2)"
| "form_of_btree f g (Branch (Leaf (Suc (Suc 0))) (Branch t1 t2)) =
     Or (form_of_btree f g t1) (form_of_btree f g t2)"
| "form_of_btree f g (Branch (Leaf (Suc (Suc (Suc 0)))) (Branch t1 t2)) =
     Impl (form_of_btree f g t1) (form_of_btree f g t2)"
| "form_of_btree f g (Branch (Leaf (Suc (Suc (Suc (Suc 0))))) t) =
     Neg (form_of_btree f g t)"
| "form_of_btree f g (Branch (Leaf (Suc (Suc (Suc (Suc (Suc 0)))))) t) =
     Forall (form_of_btree f g t)"
| "form_of_btree f g (Branch (Leaf (Suc (Suc (Suc (Suc (Suc (Suc 0))))))) t) =
     Exists (form_of_btree f g t)"

primrec
  btree_of_form :: "('a \<Rightarrow> nat) \<Rightarrow> ('b \<Rightarrow> nat) \<Rightarrow> ('a, 'b) form \<Rightarrow> btree"
where
  "btree_of_form f g FF = Leaf 0"
| "btree_of_form f g TT = Leaf (Suc 0)"
| "btree_of_form f g (Pred b ts) = Branch (Leaf 0)
     (Branch (Leaf (g b)) (Leaf (undiag_list (undiag_term f) ts)))"
| "btree_of_form f g (And a b) = Branch (Leaf (Suc 0))
     (Branch (btree_of_form f g a) (btree_of_form f g b))"
| "btree_of_form f g (Or a b) = Branch (Leaf (Suc (Suc 0)))
     (Branch (btree_of_form f g a) (btree_of_form f g b))"
| "btree_of_form f g (Impl a b) = Branch (Leaf (Suc (Suc (Suc 0))))
     (Branch (btree_of_form f g a) (btree_of_form f g b))"
| "btree_of_form f g (Neg a) = Branch (Leaf (Suc (Suc (Suc (Suc 0)))))
     (btree_of_form f g a)"
| "btree_of_form f g (Forall a) = Branch (Leaf (Suc (Suc (Suc (Suc (Suc 0))))))
     (btree_of_form f g a)"
| "btree_of_form f g (Exists a) = Branch
     (Leaf (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))
     (btree_of_form f g a)"

definition
  diag_form :: "(nat \<Rightarrow> 'a) \<Rightarrow> (nat \<Rightarrow> 'b) \<Rightarrow> nat \<Rightarrow> ('a, 'b) form" where
  "diag_form f g n = form_of_btree f g (diag_btree n)"

definition
  undiag_form :: "('a \<Rightarrow> nat) \<Rightarrow> ('b \<Rightarrow> nat) \<Rightarrow> ('a, 'b) form \<Rightarrow> nat" where
  "undiag_form f g x = undiag_btree (btree_of_form f g x)"

theorem diag_undiag_form [simp]:
  "(\<And>x. d (u x) = x) \<Longrightarrow> (\<And>x. d' (u' x) = x) \<Longrightarrow>
  diag_form d d' (undiag_form u u' f) = f"
  by (induct f) (simp_all add: diag_form_def undiag_form_def)

definition
  diag_form' :: "nat \<Rightarrow> (nat, nat) form" where
  "diag_form' = diag_form (\<lambda>n. n) (\<lambda>n. n)"

definition
  undiag_form' :: "(nat, nat) form \<Rightarrow> nat" where
  "undiag_form' = undiag_form (\<lambda>n. n) (\<lambda>n. n)"

theorem diag_undiag_form' [simp]: "diag_form' (undiag_form' f) = f"
  by (simp add: diag_form'_def undiag_form'_def)


subsection {* Extension to maximal consistent sets *}

text {*
\label{sec:extend}
Given a set @{text C} of finite character, we show that
the least upper bound of a chain of sets that are elements
of @{text C} is again an element of @{text C}.
*}

definition
  is_chain :: "(nat \<Rightarrow> 'a set) \<Rightarrow> bool" where
  "is_chain f = (\<forall>n. f n \<subseteq> f (Suc n))"

theorem is_chainD: "is_chain f \<Longrightarrow> x \<in> f m \<Longrightarrow> x \<in> f (m + n)"
  by (induct n) (fastforce simp add: is_chain_def)+

theorem is_chainD': "is_chain f \<Longrightarrow> x \<in> f m \<Longrightarrow> m \<le> k \<Longrightarrow> x \<in> f k"
  apply (subgoal_tac "\<exists>n. k = m + n")
  apply (erule exE)
  apply simp
  apply (erule_tac n=n in is_chainD)
  apply assumption
  apply arith
  done

theorem chain_index:
  assumes ch: "is_chain f" and fin: "finite F"
  shows "F \<subseteq> (\<Union>n. f n) \<Longrightarrow> \<exists>n. F \<subseteq> f n" using fin
  apply (induct rule: finite_induct)
  apply blast
  apply (insert ch)
  apply simp
  apply (erule conjE exE)+
  apply (rule_tac x="max n xa" in exI)
  apply (rule conjI)
  apply (erule is_chainD')
  apply assumption
  apply (simp add: max_def)
  apply (rule subsetI)
  apply (drule_tac B="f n" in subsetD)
  apply assumption
  apply (erule is_chainD')
  apply assumption
  apply (simp add: max_def)
  done
  
theorem chain_union_closed:
  "finite_char C \<Longrightarrow> is_chain f \<Longrightarrow> \<forall>n. f n \<in> C \<Longrightarrow> (\<Union>n. f n) \<in> C"
  apply (frule finite_char_closed)
  apply (unfold finite_char_def subset_closed_def)
  apply (drule spec)
  apply (erule iffD2)
  apply (rule allI impI)+
  apply (drule chain_index)
  apply blast+
  done

text {*
We can now define a function @{text Extend} that extends a consistent
set to a maximal consistent set. To this end, we first define an auxiliary
function @{text extend} that produces the elements of an ascending chain of
consistent sets.
*}

primrec
  dest_Neg :: "('a, 'b) form \<Rightarrow> ('a, 'b) form"
where
  "dest_Neg (Neg p) = p"

primrec
  dest_Forall :: "('a, 'b) form \<Rightarrow> ('a, 'b) form"
where
  "dest_Forall (Forall p) = p"

primrec
  dest_Exists :: "('a, 'b) form \<Rightarrow> ('a, 'b) form"
where
  "dest_Exists (Exists p) = p"

primrec
  extend :: "(nat, 'b) form set \<Rightarrow> (nat, 'b) form set set \<Rightarrow>
    (nat \<Rightarrow> (nat, 'b) form) \<Rightarrow> nat \<Rightarrow> (nat, 'b) form set"
where
  "extend S C f 0 = S"
  | "extend S C f (Suc n) = (if extend S C f n \<union> {f n} \<in> C
     then
       (if (\<exists>p. f n = Exists p)
        then extend S C f n \<union> {f n} \<union> {subst (dest_Exists (f n))
          (App (SOME k. k \<notin> (\<Union>p \<in> extend S C f n \<union> {f n}. params p)) []) 0}
        else if (\<exists>p. f n = Neg (Forall p))
        then extend S C f n \<union> {f n} \<union> {Neg (subst (dest_Forall (dest_Neg (f n)))
          (App (SOME k. k \<notin> (\<Union>p \<in> extend S C f n \<union> {f n}. params p)) []) 0)}
        else extend S C f n \<union> {f n})
     else extend S C f n)"

definition
  Extend :: "(nat, 'b) form set \<Rightarrow> (nat, 'b) form set set \<Rightarrow>
    (nat \<Rightarrow> (nat, 'b) form) \<Rightarrow> (nat, 'b) form set" where
  "Extend S C f = (\<Union>n. extend S C f n)"

theorem is_chain_extend: "is_chain (extend S C f)"
  by (simp add: is_chain_def) blast

theorem finite_paramst [simp]: "finite (paramst (t :: 'a term))"
  "finite (paramsts (ts :: 'a term list))"
  by (induct t and ts rule: paramst.induct paramsts.induct) (simp_all split: sum.split)

theorem finite_params [simp]: "finite (params p)"
  by (induct p) simp_all

theorem finite_params_extend [simp]:
  "\<not> finite (\<Inter>p \<in> S. - params p) \<Longrightarrow> \<not> finite (\<Inter>p \<in> extend S C f n. - params p)"
  by (induct n) simp_all

theorem extend_in_C: "alt_consistency C \<Longrightarrow>
  S \<in> C \<Longrightarrow> \<not> finite (- (\<Union>p \<in> S. params p)) \<Longrightarrow> extend S C f n \<in> C"
  apply (induct n)
  apply simp_all
  apply (rule conjI impI)+
  apply (erule exE)+
  apply simp
  apply (simp add: alt_consistency_def)
  apply (rule impI)+
  apply (erule exE)
  apply (erule_tac x="insert (f n) (extend S C f n)" in allE)
  apply (erule impE)
  apply assumption
  apply ((drule conjunct2)+,
    erule_tac x=p in allE,
    erule_tac x="SOME k.
      k \<notin> (\<Union>x\<in>extend S C f n \<union> {f n}. params x)" in allE)
  apply (erule impE)
  apply (subgoal_tac "\<not> finite (- (\<Union>x\<in>extend S C f n \<union> {f n}. params x))")
  prefer 2
  apply simp
  apply (rule ballI)
  apply (drule_tac A="- S" for S in infinite_nonempty)
  apply (erule exE)
  apply (rule someI2)
  apply (simp only: Compl_iff [symmetric])
  apply fast
  apply simp
  apply (rule impI)+
  apply (erule exE)
  apply (simp add: alt_consistency_def)
  apply (erule_tac x="insert (Exists p) (extend S C f n)" in allE)
  apply (erule impE)
  apply assumption
  apply (drule conjunct2)
  apply (drule conjunct2)
  apply (drule conjunct2)
  apply (drule conjunct2)
  apply (drule conjunct2)
  apply (drule conjunct2)
  apply (drule conjunct2)
  apply (drule conjunct2)
  apply (drule conjunct2)
  apply (drule conjunct2)
  apply (drule conjunct2)
  apply (drule conjunct2)
  apply (drule conjunct1)
  apply (erule_tac x=p in allE)
  apply (erule_tac x="SOME k.
      k \<notin> (\<Union>x\<in>extend S C f n \<union> {Exists p}. params x)" in allE)
  apply (erule impE)
  apply (subgoal_tac "\<not> finite (- (\<Union>x\<in>extend S C f n \<union> {Exists p}. params x))")
  prefer 2
  apply simp
  apply (rule ballI)
  apply (drule_tac A="- S" for S in infinite_nonempty)
  apply (erule exE)
  apply (rule someI2)
  apply (simp only: Compl_iff [symmetric])
  apply auto
  done

text {*
The main theorem about @{text Extend} says that if @{text C} is an
alternative consistency property that is of finite character,
@{text S} is consistent and @{text S} uses only finitely many
parameters, then @{text "Extend S C f"} is again consistent.
*}

theorem Extend_in_C: "alt_consistency C \<Longrightarrow> finite_char C \<Longrightarrow>
  S \<in> C \<Longrightarrow> \<not> finite (- (\<Union>p \<in> S. params p)) \<Longrightarrow> Extend S C f \<in> C"
  apply (unfold Extend_def)
  apply (erule chain_union_closed)
  apply (rule is_chain_extend)
  apply (rule allI)
  by (rule extend_in_C)

theorem Extend_subset: "S \<subseteq> Extend S C f"
  apply (rule subsetI)
  apply (simp add: Extend_def)
  apply (rule_tac x=0 in exI)
  apply simp
  done

text {*
The @{text Extend} function yields a maximal set:
*}

definition
  maximal :: "'a set \<Rightarrow> 'a set set \<Rightarrow> bool" where
  "maximal S C = (\<forall>S'\<in>C. S \<subseteq> S' \<longrightarrow> S = S')"

theorem extend_maximal: "\<forall>y. \<exists>n. y = f n \<Longrightarrow>
  finite_char C \<Longrightarrow> maximal (Extend S C f) C"
  apply (simp add: maximal_def Extend_def)
  apply (rule ballI impI)+
  apply (rule subset_antisym)
  apply assumption
  apply (rule ccontr)
  apply (subgoal_tac "\<exists>z. z \<in> S' \<and> z \<notin> (\<Union>x. extend S C f x)")
  prefer 2
  apply blast
  apply (erule exE conjE)+
  apply (erule_tac x=z in allE)
  apply (erule exE)
  apply (subgoal_tac "extend S C f n \<union> {f n} \<subseteq> S'")
  prefer 2
  apply simp
  apply (rule subset_trans)
  prefer 2
  apply assumption
  apply (rule UN_upper [OF UNIV_I])
  apply (drule finite_char_closed)
  apply (unfold subset_closed_def)
  apply (drule bspec)
  apply assumption
  apply (erule_tac x="a \<union> b" for a b in allE)
  apply (erule impE)
  apply assumption
  apply (erule_tac P="a \<in> b" for a b in notE)
  apply (rule_tac a="Suc n" in UN_I [OF UNIV_I])
  apply simp
  done


subsection {* Hintikka sets and Herbrand models *}

text {*
\label{sec:hintikka}
A Hintikka set is defined as follows:
*}

definition
  hintikka :: "('a, 'b) form set \<Rightarrow> bool" where
  "hintikka H =
     ((\<forall>p ts. \<not> (Pred p ts \<in> H \<and> Neg (Pred p ts) \<in> H)) \<and>
     FF \<notin> H \<and> Neg TT \<notin> H \<and>
     (\<forall>Z. Neg (Neg Z) \<in> H \<longrightarrow> Z \<in> H) \<and>
     (\<forall>A B. And A B \<in> H \<longrightarrow> A \<in> H \<and> B \<in> H) \<and>
     (\<forall>A B. Neg (Or A B) \<in> H \<longrightarrow> Neg A \<in> H \<and> Neg B \<in> H) \<and>
     (\<forall>A B. Or A B \<in> H \<longrightarrow> A \<in> H \<or> B \<in> H) \<and>
     (\<forall>A B. Neg (And A B) \<in> H \<longrightarrow> Neg A \<in> H \<or> Neg B \<in> H) \<and>
     (\<forall>A B. Impl A B \<in> H \<longrightarrow> Neg A \<in> H \<or> B \<in> H) \<and>
     (\<forall>A B. Neg (Impl A B) \<in> H \<longrightarrow> A \<in> H \<and> Neg B \<in> H) \<and>
     (\<forall>P t. closedt 0 t \<longrightarrow> Forall P \<in> H \<longrightarrow> subst P t 0 \<in> H) \<and>
     (\<forall>P t. closedt 0 t \<longrightarrow> Neg (Exists P) \<in> H \<longrightarrow> Neg (subst P t 0) \<in> H) \<and>
     (\<forall>P. Exists P \<in> H \<longrightarrow> (\<exists>t. closedt 0 t \<and> subst P t 0 \<in> H)) \<and>
     (\<forall>P. Neg (Forall P) \<in> H \<longrightarrow> (\<exists>t. closedt 0 t \<and> Neg (subst P t 0) \<in> H)))"

text {*
In Herbrand models, each {\em closed} term is interpreted by itself.
We introduce a new datatype @{text hterm} (``Herbrand terms''), which
is similar to the datatype @{text term} introduced in \secref{sec:terms},
but without variables. We also define functions for converting between
closed terms and Herbrand terms.
*}

datatype 'a hterm = HApp 'a "'a hterm list"

primrec
  term_of_hterm :: "'a hterm \<Rightarrow> 'a term"
  and terms_of_hterms :: "'a hterm list \<Rightarrow> 'a term list"
where
  "term_of_hterm (HApp a hts) = App a (terms_of_hterms hts)"
| "terms_of_hterms [] = []"
| "terms_of_hterms (ht # hts) = term_of_hterm ht # terms_of_hterms hts"

theorem herbrand_evalt [simp]:
  "closedt 0 t \<Longrightarrow> term_of_hterm (evalt e HApp t) = t"
  "closedts 0 ts \<Longrightarrow> terms_of_hterms (evalts e HApp ts) = ts"
  by (induct t and ts rule: closedt.induct closedts.induct) simp_all

theorem herbrand_evalt' [simp]:
  "evalt e HApp (term_of_hterm ht) = ht"
  "evalts e HApp (terms_of_hterms hts) = hts"
  by (induct ht and hts rule: term_of_hterm.induct terms_of_hterms.induct) simp_all

theorem closed_hterm [simp]:
  "closedt 0 (term_of_hterm (ht::'a hterm))"
  "closedts 0 (terms_of_hterms (hts::'a hterm list))"
  by (induct ht and hts rule: term_of_hterm.induct terms_of_hterms.induct) simp_all

theorem measure_size_eq [simp]: "((x, y) \<in> measure f) = (f x < f y)"
  by (simp add: measure_def inv_image_def)

text {*
We can prove that Hintikka sets are satisfiable in Herbrand models.
Note that this theorem cannot be proved by a simple structural induction
(as claimed in Fitting's book), since a parameter substitution has
to be applied in the cases for quantifiers. However, since parameter
substitution does not change the size of formulae, the theorem can
be proved by well-founded induction on the size of the formula @{text p}.
*}

theorem hintikka_model: "hintikka H \<Longrightarrow>
  (p \<in> H \<longrightarrow> closed 0 p \<longrightarrow>
    eval e HApp (\<lambda>a ts. Pred a (terms_of_hterms ts) \<in> H) p) \<and>
  (Neg p \<in> H \<longrightarrow> closed 0 p \<longrightarrow>
    eval e HApp (\<lambda>a ts. Pred a (terms_of_hterms ts) \<in> H) (Neg p))"
  apply (unfold hintikka_def)
  apply (rule_tac r="measure size_form" and a=p in wf_induct)
  apply (simp (no_asm))
  apply (case_tac x)
  apply hypsubst
  apply (rule conjI)
  apply (drule conjunct2)
  apply (drule conjunct1)
  apply iprover
  apply (simp (no_asm))
  apply hypsubst
  apply (simp (no_asm))
  apply iprover
  apply hypsubst
  apply (simp (no_asm))
  apply (drule conjunct1)
  apply iprover
  apply hypsubst
  apply (rule conjI impI)+
  apply (drule conjunct2, drule conjunct2,
    drule conjunct2, drule conjunct2,
    drule conjunct1, erule allE, erule allE,
    erule impE, assumption)
  apply simp
  apply (rule impI)+
  apply (drule conjunct2, drule conjunct2,
    drule conjunct2, drule conjunct2,
    drule conjunct2, drule conjunct2,
    drule conjunct2, drule conjunct1,
    erule allE, erule allE,
    erule impE, assumption)
  apply fastforce
  apply hypsubst
  apply (rule conjI impI)+
  apply (drule conjunct2, drule conjunct2,
    drule conjunct2, drule conjunct2,
    drule conjunct2, drule conjunct2,
    drule conjunct1, erule allE, erule allE,
    erule impE, assumption)
  apply fastforce
  apply (rule impI)+
  apply (drule conjunct2,
    drule conjunct2, drule conjunct2,
    drule conjunct2, drule conjunct2,
    drule conjunct1, erule allE, erule allE,
    erule impE, assumption)
  apply simp
  apply hypsubst
  apply (rule conjI impI)+
  apply (drule conjunct2, drule conjunct2,
    drule conjunct2, drule conjunct2,
    drule conjunct2, drule conjunct2,
    drule conjunct2, drule conjunct2,
    drule conjunct1, erule allE, erule allE,
    erule impE, assumption)
  apply fastforce
  apply (rule impI)+
  apply (drule conjunct2, drule conjunct2,
    drule conjunct2, drule conjunct2,
    drule conjunct2, drule conjunct2,
    drule conjunct2, drule conjunct2,
    drule conjunct2, drule conjunct1,
    erule allE, erule allE,
    erule impE, assumption)
  apply simp
  apply (rule conjI)
  apply (erule thin_rl)
  apply simp
  apply hypsubst
  apply (rule impI)+
  apply (drule conjunct2, drule conjunct2,
    drule conjunct2, drule conjunct1,
    erule allE, erule impE, assumption)
  apply simp
  apply hypsubst
  apply (simp (no_asm))
  apply (rule conjI impI allI)+
  apply (drule conjunct2, drule conjunct2,
    drule conjunct2, drule conjunct2,
    drule conjunct2, drule conjunct2,
    drule conjunct2, drule conjunct2,
    drule conjunct2, drule conjunct2,
    drule conjunct1)
  apply (rename_tac form z)
  apply (erule_tac x="subst form (term_of_hterm z) 0" in allE)
  apply simp
  apply (rule impI)+
  apply (drule conjunct2, drule conjunct2,
    drule conjunct2, drule conjunct2,
    drule conjunct2, drule conjunct2,
    drule conjunct2, drule conjunct2,
    drule conjunct2, drule conjunct2,
    drule conjunct2, drule conjunct2,
    drule conjunct2)
  apply (erule allE, erule impE, assumption, erule exE)
  apply (rename_tac form t)
  apply (erule_tac x="subst form t 0" in allE)
  apply fastforce
  apply hypsubst
  apply (simp (no_asm))
  apply (rule conjI impI allI)+
  apply (drule conjunct2, drule conjunct2,
    drule conjunct2, drule conjunct2,
    drule conjunct2, drule conjunct2,
    drule conjunct2, drule conjunct2,
    drule conjunct2, drule conjunct2,
    drule conjunct2, drule conjunct2,
    drule conjunct1)
  apply (erule allE, erule impE, assumption, erule exE)
  apply (rename_tac form t)
  apply (erule_tac x="subst form t 0" in allE)
  apply fastforce
  apply (rule impI allI)+
  apply (drule conjunct2, drule conjunct2,
    drule conjunct2, drule conjunct2,
    drule conjunct2, drule conjunct2,
    drule conjunct2, drule conjunct2,
    drule conjunct2, drule conjunct2,
    drule conjunct2, drule conjunct1)
  apply (rename_tac form z)
  apply (erule_tac x="subst form (term_of_hterm z) 0" in allE)
  apply simp
  done

text {*
Using the maximality of @{term "Extend S C f"}, we can show
that @{term "Extend S C f"} yields Hintikka sets:
*}

theorem extend_hintikka:
  assumes fin_ch: "finite_char C"
  and infin_p: "\<not> finite (- (\<Union>p\<in>S. params p))"
  and surj: "\<forall>y. \<exists>n. y = f n"
  shows "alt_consistency C \<Longrightarrow> S \<in> C \<Longrightarrow> hintikka (Extend S C f)"
  apply (insert extend_maximal [OF surj fin_ch, of S])
  apply (frule Extend_in_C)
  apply (rule fin_ch)
  apply assumption
  apply (rule infin_p)
  apply (unfold alt_consistency_def maximal_def hintikka_def)
  apply (erule_tac x="Extend S C f" in allE,
    erule impE, assumption)
  apply (erule conjE', fast)
  apply (erule conjE', fast)
  apply (erule conjE', fast)
  apply (erule conjE', fast)
  apply (erule conjE', fast)
  apply (erule conjE', fast)
  apply (erule conjE', fast)
  apply (erule conjE', fast)
  apply (erule conjE', fast)
  apply (erule conjE', fast)
  apply (erule conjE', fast)
  apply (erule conjE', fast)
  apply (erule conjE')
  apply (rule allI impI)+
  apply (erule_tac x=P in allE)
  apply (simp only: Extend_def)
  apply (insert surj)
  apply (erule_tac x="Exists P" in allE)
  apply (erule exE)
  apply (subgoal_tac "extend S C f n \<union> {f n} \<in> C")
  prefer 2
  apply (cut_tac finite_char_closed [OF fin_ch])
  apply (unfold subset_closed_def)
  apply (drule_tac x="\<Union>n. extend S C f n" in bspec,
    assumption, erule allE, erule mp)
  apply simp
  apply blast
  apply (rule_tac
    x="(App (SOME k. k \<notin> (\<Union>p \<in> extend S C f n \<union> {f n}. params p)) [])" in exI)
  apply (rule conjI)
  apply simp
  apply (rule_tac a="Suc n" in UN_I [OF UNIV_I])
  apply simp
  apply (rule conjI impI)+
  apply (erule exE)+
  apply simp
  apply (rule impI)
  apply (erule_tac x=P in allE)
  apply simp
  apply (drule sym)
  apply simp
  apply (rule allI impI)+
  apply (erule_tac x=P in allE)
  apply (simp only: Extend_def)
  apply (insert surj)
  apply (erule_tac x="Neg (Forall P)" in allE)
  apply (erule exE)
  apply (subgoal_tac "extend S C f n \<union> {f n} \<in> C")
  prefer 2
  apply (cut_tac finite_char_closed [OF fin_ch])
  apply (unfold subset_closed_def)
  apply (drule_tac x="\<Union>n. extend S C f n" in bspec,
    assumption, erule allE, erule mp)
  apply simp
  apply blast
  apply (rule_tac
    x="(App (SOME k. k \<notin> (\<Union>p \<in> extend S C f n \<union> {f n}. params p)) [])" in exI)
  apply (rule conjI)
  apply simp
  apply (rule_tac a="Suc n" in UN_I [OF UNIV_I])
  apply simp
  apply (rule conjI impI)+
  apply (erule exE)+
  apply simp
  apply (drule sym)
  apply simp
  apply (rule impI)
  apply (erule_tac P="%x. l \<noteq> f x" and x=P for l f in allE)
  apply simp
  done


subsection {* Model existence theorem *}

text {*
\label{sec:model-existence}
Since the result of extending @{text S} is a superset of @{text S},
it follows that each consistent set @{text S} has a Herbrand model:
*}

theorem model_existence:
  "consistency C \<Longrightarrow> S \<in> C \<Longrightarrow> \<not> finite (- (\<Union>p \<in> S. params p)) \<Longrightarrow>
    p \<in> S \<Longrightarrow> closed 0 p \<Longrightarrow> eval e HApp (\<lambda>a ts.
      Pred a (terms_of_hterms ts) \<in> Extend S
        (mk_finite_char (mk_alt_consistency (close C))) diag_form') p"
  apply (rule hintikka_model [THEN conjunct1, THEN mp, THEN mp])
  apply (rule extend_hintikka)
  apply (rule finite_char)
  apply assumption
  apply (rule allI)
  apply (rule_tac x="undiag_form' y" in exI)
  apply simp
  apply (rule finite_alt_consistency)
  apply (rule alt_consistency)
  apply (erule close_consistency)
  apply (rule mk_alt_consistency_closed)
  apply (rule close_closed)
  apply (drule close_subset [THEN subsetD])
  apply (drule mk_alt_consistency_subset [THEN subsetD])
  apply (erule finite_char_subset
    [OF mk_alt_consistency_closed, OF close_closed, THEN subsetD])
  apply (erule Extend_subset [THEN subsetD])
  apply assumption
  done


subsection {* Completeness for Natural Deduction *}

text {*
Thanks to the model existence theorem, we can now show the completeness
of the natural deduction calculus introduced in \secref{sec:proof-calculus}.
In order for the model existence theorem to be applicable, we have to prove
that the set of sets that are consistent with respect to @{text "\<turnstile>"} is a
consistency property:
*}

theorem deriv_consistency:
  assumes inf_param: "\<not> finite (UNIV::'a set)"
  shows "consistency {S::('a, 'b) form set. \<exists>G. S = set G \<and> \<not> G \<turnstile> FF}"
  apply (unfold consistency_def)
  apply (rule allI impI)+
  apply simp
  apply (erule exE)
  apply (erule conjE)
  apply simp
  apply (rule conjI allI impI notI)+
  apply (erule notE)
  apply (rule FFE)
  apply (rule_tac a="Pred p ts" in NegE)
  apply (rule Assum)
  apply simp
  apply (rule Assum)
  apply simp
  apply (rule conjI notI)+
  apply (erule notE)
  apply (rule FFE)
  apply (rule Assum)
  apply simp
  apply (rule conjI notI)+
  apply (erule notE)
  apply (rule FFE)
  apply (rule_tac a="TT" in NegE)
  apply (rule Assum)
  apply simp
  apply (rule TTI)
  apply (rule conjI allI impI)+
  apply (rule_tac x="Z # G" in exI)
  apply simp
  apply (rule notI)
  apply (erule notE)
  apply (erule cut')
  apply (rule Class)
  apply (rule_tac a="Neg Z" in NegE)
  apply (rule Assum)
  apply simp
  apply (rule Assum)
  apply simp
  apply (rule allI impI conjI)+
  apply (rule_tac x="A # B # G" in exI)
  apply simp
  apply (rule notI)
  apply (erule notE)
  apply (erule cut' [OF cut'])
  apply (rule_tac b=B in AndE1)
  apply (rule Assum)
  apply simp
  apply (rule_tac a=A in AndE2)
  apply (rule Assum)
  apply simp
  apply (rule allI impI conjI)+
  apply (rule_tac x="Neg A # Neg B # G" in exI)
  apply simp
  apply (rule notI)
  apply (erule notE)
  apply (erule cut' [OF cut'])
  apply (rule NegI)
  apply (rule_tac a="Or A B" in NegE)
  apply (rule Assum)
  apply simp
  apply (rule OrI1)
  apply (rule Assum)
  apply simp
  apply (rule NegI)
  apply (rule_tac a="Or A B" in NegE)
  apply (rule Assum)
  apply simp
  apply (rule OrI2)
  apply (rule Assum)
  apply simp
  apply (rule allI impI conjI)+
  apply (rule ccontr)
  apply simp
  apply (erule conjE notE)+
  apply (rule_tac a=A and b=B in OrE)
  apply (rule Assum)
  apply simp
  apply simp
  apply simp
  apply (rule allI impI conjI)+
  apply (rule ccontr)
  apply simp
  apply (erule conjE notE)+
  apply (subgoal_tac "G \<turnstile> Or (Neg A) (Neg B)")
  apply (erule_tac a="Neg A" and b="Neg B" in OrE)
  apply simp
  apply simp
  apply (rule Class')
  apply (rule OrI1)
  apply (rule NegI)
  apply (rule_tac a="Or (Neg A) (Neg B)" in NegE)
  apply (rule Assum, simp)
  apply (rule OrI2)
  apply (rule NegI)
  apply (rule_tac a="And A B" in NegE)
  apply (rule Assum, simp)
  apply (rule AndI)
  apply (rule Assum, simp)
  apply (rule Assum, simp)
  apply (rule allI impI conjI)+
  apply (rule ccontr)
  apply simp
  apply (erule conjE notE)+
  apply (subgoal_tac "G \<turnstile> Or (Neg A) B")
  apply (erule_tac a="Neg A" and b="B" in OrE)
  apply simp
  apply simp
  apply (rule Class')
  apply (rule OrI1)
  apply (rule NegI)
  apply (rule_tac a="Or (Neg A) B" in NegE)
  apply (rule Assum, simp)
  apply (rule OrI2)
  apply (rule_tac a=A in ImplE)
  apply (rule Assum, simp)
  apply (rule Assum, simp)
  apply (rule allI impI conjI)+
  apply (rule_tac x="A # Neg B # G" in exI)
  apply simp
  apply (rule notI)
  apply (erule notE)
  apply (erule cut' [OF cut'])
  apply (rule Class)
  apply (rule_tac a="Impl A B" in NegE)
  apply (rule Assum, simp)
  apply (rule ImplI)
  apply (rule FFE)
  apply (rule_tac a=A in NegE)
  apply (rule Assum, simp)
  apply (rule Assum, simp)
  apply (rule NegI)
  apply (rule_tac a="Impl A B" in NegE)
  apply (rule Assum, simp)
  apply (rule ImplI)
  apply (rule Assum, simp)
  apply (rule allI impI conjI)+
  apply (rule_tac x="subst P t 0 # G" in exI)
  apply simp
  apply (rule notI)
  apply (erule notE)
  apply (erule cut')
  apply (rule ForallE)
  apply (rule Assum, simp)
  apply (rule allI impI conjI)+
  apply (rule_tac x="Neg (subst P t 0) # G" in exI)
  apply simp
  apply (rule notI)
  apply (erule notE)
  apply (erule cut')
  apply (rule NegI)
  apply (rule_tac a="Exists P" in NegE)
  apply (rule Assum, simp)
  apply (rule_tac t=t in ExistsI)
  apply (rule Assum, simp)
  apply (rule allI impI conjI)+
  apply (subgoal_tac "\<exists>x. x \<in> - ((\<Union>p \<in> set G. params p) \<union> params P)")
  apply simp
  apply (erule exE)
  apply (rule_tac x=x in exI)
  apply (rule_tac x="subst P (App x []) 0 # G" in exI)
  apply simp
  apply (rule notI)
  apply (erule notE)
  apply (rule_tac a=P in ExistsE)
  apply (rule Assum, simp)
  apply assumption
  apply (simp add: list_all_iff)
  apply simp
  apply simp
  apply (rule infinite_nonempty)
  apply (simp only: Compl_UNIV_eq)
  apply (rule Diff_infinite_finite)
  apply simp
  apply (rule inf_param)
  apply (rule allI impI)+
  apply (subgoal_tac "\<exists>x. x \<in> - ((\<Union>p \<in> set G. params p) \<union> params P)")
  apply simp
  apply (erule exE)
  apply (rule_tac x=x in exI)
  apply (rule_tac x="Neg (subst P (App x []) 0) # G" in exI)
  apply simp
  apply (rule notI)
  apply (erule notE)
  apply (rule_tac a="Neg P" and n=x in ExistsE)
  apply (rule Class)
  apply (rule_tac a="Forall P" in NegE)
  apply (rule Assum, simp)
  apply (rule_tac n=x in ForallI)
  apply (rule Class)
  apply (rule_tac a="Exists (Neg P)" in NegE)
  apply (rule Assum, simp)
  apply (rule_tac t="App x []" in ExistsI)
  apply (rule Assum, simp)
  apply (simp add: list_all_iff)
  apply simp
  apply simp
  apply (simp add: list_all_iff)
  apply simp
  apply simp
  apply (rule infinite_nonempty)
  apply (simp only: Compl_UNIV_eq)
  apply (rule Diff_infinite_finite)
  apply simp
  apply (rule inf_param)
  done

text {*
Hence, by contradiction, we have completeness of natural deduction:
*}

theorem natded_complete: "closed 0 p \<Longrightarrow> list_all (closed 0) ps \<Longrightarrow>
  \<forall>e (f::nat \<Rightarrow> nat hterm list \<Rightarrow> nat hterm) (g::nat \<Rightarrow> nat hterm list \<Rightarrow> bool).
    e,f,g,ps \<Turnstile> p \<Longrightarrow> ps \<turnstile> p"
  apply (rule Class)
  apply (rule ccontr)
  apply (subgoal_tac "\<exists>e f g. list_all (eval e f g) (Neg p # ps)")
  apply (simp add: model_def)
  apply iprover
  apply (subgoal_tac "list_all (closed 0) (Neg p # ps)")
  apply (simp only: list_all_iff)
  apply (rule_tac x=arbitrary in exI)
  apply (rule exI ballI)+
  apply (rule_tac S="set (Neg p # ps)" in model_existence) 
  apply (rule deriv_consistency)
  apply (rule infinite_UNIV_nat)
  apply (simp del: set_simps)
  apply (rule exI)
  apply (rule conjI)
  apply (rule refl)
  apply assumption
  apply (simp only: Compl_UNIV_eq)
  apply (rule Diff_infinite_finite)
  apply (rule finite_UN_I)
  apply simp
  apply simp
  apply (rule infinite_UNIV_nat)
  apply simp
  apply fast
  apply simp
  done


section {* L\"owenheim-Skolem theorem *}

text {*
Another application of the model existence theorem presented in \secref{sec:model-existence}
is the L\"owenheim-Skolem theorem. It says that a set of formulae that is satisfiable in an
{\em arbitrary model} is also satisfiable in a {\em Herbrand model}. The main idea behind the
proof is to show that satisfiable sets are consistent, hence they must be satisfiable in a
Herbrand model.
*}

theorem sat_consistency: "consistency {S. \<not> finite (- (\<Union>p\<in>S. params p)) \<and>
  (\<exists>f. \<forall>(p::('a, 'b)form)\<in>S. eval e f g p)}"
  apply (unfold consistency_def)
  apply (rule allI impI)+
  apply (erule CollectE conjE)+
  apply (rule conjI)
  apply (rule allI notI)+
  apply (erule conjE exE)+
  apply (frule_tac x="Pred p ts" in bspec)
  apply assumption
  apply (frule_tac x="Neg (Pred p ts)" in bspec)
  apply assumption
  apply simp
  apply (rule conjI)
  apply fastforce
  apply (rule conjI)
  apply fastforce
  apply (rule conjI)
  apply force
  apply (rule conjI)
  apply (auto intro!: exI)[1]
  apply (rule conjI)
  apply (auto intro!: exI)[1]
  apply (rule conjI)
  apply (rule allI impI)+
  apply (erule exE)+
  apply (frule bspec)
  apply assumption
  apply simp
  apply (erule disjE)
  apply (rule disjI1)
  apply (rule exI)+
  apply (rule conjI)
  apply assumption
  apply assumption
  apply (rule disjI2)
  apply (rule exI)+
  apply (rule conjI)
  apply assumption
  apply assumption
  apply (rule conjI)
  apply (rule allI impI)+
  apply (erule exE)+
  apply (frule bspec)
  apply assumption
  apply (simp del: disj_not1)
  apply (erule disjE)
  apply (rule disjI1)
  apply (rule exI)+
  apply (rule conjI)
  apply assumption
  apply assumption
  apply (rule disjI2)
  apply (rule exI)+
  apply (rule conjI)
  apply assumption
  apply assumption
  apply (rule conjI)
  apply (rule allI impI)+
  apply (erule exE)+
  apply (frule bspec)
  apply assumption
  apply simp
  apply (drule iffD1 [OF imp_conv_disj])
  apply (erule disjE)
  apply (rule disjI1)
  apply (rule exI)+
  apply (rule conjI)
  apply assumption
  apply assumption
  apply (rule disjI2)
  apply (rule exI)+
  apply (rule conjI)
  apply assumption
  apply assumption
  apply (rule conjI)
  apply (auto intro!: exI)[1]
  apply (rule conjI)
  apply (auto intro!: exI)[1]
  apply (rule conjI)
  apply (auto intro!: exI)[1]
  apply (rule conjI)
  apply (rule allI impI)+
  apply (erule exE)+
  apply (frule bspec)
  apply assumption
  apply (frule_tac A="- S" for S in infinite_nonempty)
  apply simp
  apply (erule exE)+
  apply (rule_tac x=x in exI)
  apply (rule_tac x="f(x:=\<lambda>y. z)" in exI)
  apply (frule_tac P="\<lambda>y. x \<notin> params y" in bspec)
  apply assumption
  apply simp
  apply (rule allI impI)+
  apply (erule exE)+
  apply (frule bspec)
  apply assumption
  apply (frule_tac A="- S" for S in infinite_nonempty)
  apply simp
  apply (erule exE)+
  apply (rule_tac x=x in exI)
  apply (rule_tac x="f(x:=\<lambda>y. z)" in exI)
  apply (frule_tac P="\<lambda>y. x \<notin> params y" in bspec)
  apply assumption
  apply simp
  done

theorem doublep_evalt [simp]:
  "evalt e f (psubstt (\<lambda>n::nat. 2 * n) t) = evalt e (\<lambda>n. f (2*n)) t"
  "evalts e f (psubstts (\<lambda>n::nat. 2 * n) ts) = evalts e (\<lambda>n. f (2*n)) ts"
  by (induct t and ts rule: evalt.induct evalts.induct) simp_all

theorem doublep_eval: "\<And>e. eval e f g (psubst (\<lambda>n::nat. 2 * n) p) =
  eval e (\<lambda>n. f (2*n)) g p"
  by (induct p) simp_all

theorem doublep_infinite_params:
  "\<not> finite (- (\<Union>p \<in> psubst (\<lambda>n::nat. 2 * n) ` S. params p))"
proof (rule infinite_super)
  show "infinite (range (\<lambda>n::nat. 2 * n + 1))"
    by (auto intro!: range_inj_infinite inj_onI)
next
  have "\<And>m n. Suc (2 * m) \<noteq> 2 * n" by arith
  then show "range (\<lambda>n::nat. (2::nat) * n + (1::nat))
    \<subseteq> - (\<Union>p::(nat, 'a) form\<in>psubst (op * (2::nat)) ` S. params p)"
    by auto
qed

text {*
When applying the model existence theorem, there is a technical
complication. We must make sure that there are infinitely many
unused parameters. In order to achieve this, we encode parameters
as natural numbers and multiply each parameter occurring in the
set @{text S} by @{text 2}.
*}

theorem loewenheim_skolem: "\<forall>p\<in>S. eval e f g p \<Longrightarrow>
  \<forall>p\<in>S. closed 0 p \<longrightarrow> eval e' (\<lambda>n. HApp (2*n)) (\<lambda>a ts.
      Pred a (terms_of_hterms ts) \<in> Extend (psubst (\<lambda>n. 2 * n) ` S)
        (mk_finite_char (mk_alt_consistency (close
          {S. \<not> finite (- (\<Union>p\<in>S. params p)) \<and>
            (\<exists>f. \<forall>p\<in>S. eval e f g p)}))) diag_form') p"
  apply (simp only: doublep_eval [symmetric])
  apply (rule ballI impI)+
  apply (rule model_existence)
  apply (rule sat_consistency)
  apply (rule CollectI)
  apply (rule conjI)
  apply (rule doublep_infinite_params)
  apply (rule_tac x="\<lambda>n. f (n div 2)" in exI)
  apply (rule ballI)
  apply (erule imageE)
  apply (drule_tac x=xa in bspec)
  apply assumption
  apply (simp add: doublep_eval)
  apply (rule doublep_infinite_params)
  apply simp
  apply simp
  done

end
