(*  Author:     Stefan Berghofer, TU Muenchen, 2003
    Author: Asta Halkjær From, DTU Compute, 2019
    Thanks to John Bruntse Larsen, Anders Schlichtkrull & Jørgen Villadsen
    See also the Natural Deduction Assistant: https://nadea.compute.dtu.dk/
*)

section \<open>First-Order Logic According to Fitting\<close>

theory FOL_Fitting
  imports "HOL-Library.Countable"
begin

section \<open>Miscellaneous Utilities\<close>

text \<open>Some facts about (in)finite sets\<close>

theorem set_inter_compl_diff [simp]: \<open>- A \<inter> B = B - A\<close> by blast

section \<open>Terms and formulae\<close>

text \<open>
\label{sec:terms}
The datatypes of terms and formulae in {\em de Bruijn notation}
are defined as follows:
\<close>

datatype 'a "term"
  = Var nat
  | App 'a \<open>'a term list\<close>

datatype ('a, 'b) form
  = FF
  | TT
  | Pred 'b \<open>'a term list\<close>
  | And \<open>('a, 'b) form\<close> \<open>('a, 'b) form\<close>
  | Or \<open>('a, 'b) form\<close> \<open>('a, 'b) form\<close>
  | Impl \<open>('a, 'b) form\<close> \<open>('a, 'b) form\<close>
  | Neg \<open>('a, 'b) form\<close>
  | Forall \<open>('a, 'b) form\<close>
  | Exists \<open>('a, 'b) form\<close>

text \<open>
We use \<open>'a\<close> and \<open>'b\<close> to denote the type of
{\em function symbols} and {\em predicate symbols}, respectively.
In applications \<open>App a ts\<close> and predicates
\<open>Pred a ts\<close>, the length of \<open>ts\<close> is considered
to be a part of the function or predicate name, so \<open>App a [t]\<close>
and \<open>App a [t,u]\<close> refer to different functions.

The size of a formula is used later for wellfounded induction. The
default implementation provided by the datatype package is not quite
what we need, so here is an alternative version:
\<close>

primrec size_form :: \<open>('a, 'b) form \<Rightarrow> nat\<close> where
  \<open>size_form FF = 0\<close>
| \<open>size_form TT = 0\<close>
| \<open>size_form (Pred _ _) = 0\<close>
| \<open>size_form (And p q) = size_form p + size_form q + 1\<close>
| \<open>size_form (Or p q) = size_form p + size_form q + 1\<close>
| \<open>size_form (Impl p q) = size_form p + size_form q + 1\<close>
| \<open>size_form (Neg p) = size_form p + 1\<close>
| \<open>size_form (Forall p) = size_form p + 1\<close>
| \<open>size_form (Exists p) = size_form p + 1\<close>

subsection \<open>Closed terms and formulae\<close>

text \<open>
Many of the results proved in the following sections are restricted
to closed terms and formulae. We call a term or formula {\em closed at
level \<open>i\<close>}, if it only contains ``loose'' bound variables with
indices smaller than \<open>i\<close>.
\<close>

primrec
  closedt :: \<open>nat \<Rightarrow> 'a term \<Rightarrow> bool\<close> and
  closedts :: \<open>nat \<Rightarrow> 'a term list \<Rightarrow> bool\<close> where
  \<open>closedt m (Var n) = (n < m)\<close>
| \<open>closedt m (App a ts) = closedts m ts\<close>
| \<open>closedts m [] = True\<close>
| \<open>closedts m (t # ts) = (closedt m t \<and> closedts m ts)\<close>

primrec closed :: \<open>nat \<Rightarrow> ('a, 'b) form \<Rightarrow> bool\<close> where
  \<open>closed m FF = True\<close>
| \<open>closed m TT = True\<close>
| \<open>closed m (Pred b ts) = closedts m ts\<close>
| \<open>closed m (And p q) = (closed m p \<and> closed m q)\<close>
| \<open>closed m (Or p q) = (closed m p \<and> closed m q)\<close>
| \<open>closed m (Impl p q) = (closed m p \<and> closed m q)\<close>
| \<open>closed m (Neg p) = closed m p\<close>
| \<open>closed m (Forall p) = closed (Suc m) p\<close>
| \<open>closed m (Exists p) = closed (Suc m) p\<close>

theorem closedt_mono: assumes le: \<open>i \<le> j\<close>
  shows \<open>closedt i (t::'a term) \<Longrightarrow> closedt j t\<close>
    and \<open>closedts i (ts::'a term list) \<Longrightarrow> closedts j ts\<close>
  using le by (induct t and ts rule: closedt.induct closedts.induct) simp_all

theorem closed_mono: assumes le: \<open>i \<le> j\<close>
  shows \<open>closed i p \<Longrightarrow> closed j p\<close>
  using le
proof (induct p arbitrary: i j)
  case (Pred i l)
  then show ?case
    using closedt_mono by simp
qed auto

subsection \<open>Substitution\<close>

text \<open>
We now define substitution functions for terms and formulae. When performing
substitutions under quantifiers, we need to {\em lift} the terms to be substituted
for variables, in order for the ``loose'' bound variables to point to the right
position.
\<close>

primrec
  substt :: \<open>'a term \<Rightarrow> 'a term \<Rightarrow> nat \<Rightarrow> 'a term\<close> ("_[_'/_]" [300, 0, 0] 300) and
  substts :: \<open>'a term list \<Rightarrow> 'a term \<Rightarrow> nat \<Rightarrow> 'a term list\<close> ("_[_'/_]" [300, 0, 0] 300) where
  \<open>(Var i)[s/k] = (if k < i then Var (i - 1) else if i = k then s else Var i)\<close>
| \<open>(App a ts)[s/k] = App a (ts[s/k])\<close>
| \<open>[][s/k] = []\<close>
| \<open>(t # ts)[s/k] = t[s/k] # ts[s/k]\<close>

primrec
  liftt :: \<open>'a term \<Rightarrow> 'a term\<close> and
  liftts :: \<open>'a term list \<Rightarrow> 'a term list\<close> where
  \<open>liftt (Var i) = Var (Suc i)\<close>
| \<open>liftt (App a ts) = App a (liftts ts)\<close>
| \<open>liftts [] = []\<close>
| \<open>liftts (t # ts) = liftt t # liftts ts\<close>

primrec subst :: \<open>('a, 'b) form \<Rightarrow> 'a term \<Rightarrow> nat \<Rightarrow> ('a, 'b) form\<close>
  ("_[_'/_]" [300, 0, 0] 300) where
  \<open>FF[s/k] = FF\<close>
| \<open>TT[s/k] = TT\<close>
| \<open>(Pred b ts)[s/k] = Pred b (ts[s/k])\<close>
| \<open>(And p q)[s/k] = And (p[s/k]) (q[s/k])\<close>
| \<open>(Or p q)[s/k] = Or (p[s/k]) (q[s/k])\<close>
| \<open>(Impl p q)[s/k] = Impl (p[s/k]) (q[s/k])\<close>
| \<open>(Neg p)[s/k] = Neg (p[s/k])\<close>
| \<open>(Forall p)[s/k] = Forall (p[liftt s/Suc k])\<close>
| \<open>(Exists p)[s/k] = Exists (p[liftt s/Suc k])\<close>

theorem lift_closed [simp]:
  \<open>closedt 0 (t::'a term) \<Longrightarrow> closedt 0 (liftt t)\<close>
  \<open>closedts 0 (ts::'a term list) \<Longrightarrow> closedts 0 (liftts ts)\<close>
  by (induct t and ts rule: closedt.induct closedts.induct) simp_all

theorem subst_closedt [simp]:
  assumes u: \<open>closedt 0 u\<close>
  shows \<open>closedt (Suc i) t \<Longrightarrow> closedt i (t[u/i])\<close>
    and \<open>closedts (Suc i) ts \<Longrightarrow> closedts i (ts[u/i])\<close>
  using u closedt_mono(1)
  by (induct t and ts rule: closedt.induct closedts.induct) auto

theorem subst_closed [simp]:
  \<open>closedt 0 t \<Longrightarrow> closed (Suc i) p \<Longrightarrow> closed i (p[t/i])\<close>
  by (induct p arbitrary: i t) simp_all

theorem subst_size_form [simp]: \<open>size_form (subst p t i) = size_form p\<close>
  by (induct p arbitrary: i t) simp_all

subsection \<open>Parameters\<close>

text \<open>
The introduction rule \<open>ForallI\<close> for the universal quantifier,
as well as the elimination rule \<open>ExistsE\<close> for the existential
quantifier introduced in \secref{sec:proof-calculus} require the
quantified variable to be replaced by a ``fresh'' parameter. Fitting's
solution is to use a new nullary function symbol for this purpose.
To express that a function symbol is ``fresh'', we introduce functions
for collecting all function symbols occurring in a term or formula.
\<close>

primrec
  paramst :: \<open>'a term \<Rightarrow> 'a set\<close> and
  paramsts :: \<open>'a term list \<Rightarrow> 'a set\<close> where
  \<open>paramst (Var n) = {}\<close>
| \<open>paramst (App a ts) = {a} \<union> paramsts ts\<close>
| \<open>paramsts [] = {}\<close>
| \<open>paramsts (t # ts) = (paramst t \<union> paramsts ts)\<close>

primrec params :: \<open>('a, 'b) form \<Rightarrow> 'a set\<close> where
  \<open>params FF = {}\<close>
| \<open>params TT = {}\<close>
| \<open>params (Pred b ts) = paramsts ts\<close>
| \<open>params (And p q) = params p \<union> params q\<close>
| \<open>params (Or p q) = params p \<union> params q\<close>
| \<open>params (Impl p q) = params p \<union> params q\<close>
| \<open>params (Neg p) = params p\<close>
| \<open>params (Forall p) = params p\<close>
| \<open>params (Exists p) = params p\<close>

text\<open>
We also define parameter substitution functions on terms and formulae
that apply a function \<open>f\<close> to all function symbols.
\<close>

primrec
  psubstt :: \<open>('a \<Rightarrow> 'c) \<Rightarrow> 'a term \<Rightarrow> 'c term\<close> and
  psubstts :: \<open>('a \<Rightarrow> 'c) \<Rightarrow> 'a term list \<Rightarrow> 'c term list\<close> where
  \<open>psubstt f (Var i) = Var i\<close>
| \<open>psubstt f (App x ts) = App (f x) (psubstts f ts)\<close>
| \<open>psubstts f [] = []\<close>
| \<open>psubstts f (t # ts) = psubstt f t # psubstts f ts\<close>

primrec psubst :: \<open>('a \<Rightarrow> 'c) \<Rightarrow> ('a, 'b) form \<Rightarrow> ('c, 'b) form\<close> where
  \<open>psubst f FF = FF\<close>
| \<open>psubst f TT = TT\<close>
| \<open>psubst f (Pred b ts) = Pred b (psubstts f ts)\<close>
| \<open>psubst f (And p q) = And (psubst f p) (psubst f q)\<close>
| \<open>psubst f (Or p q) = Or (psubst f p) (psubst f q)\<close>
| \<open>psubst f (Impl p q) = Impl (psubst f p) (psubst f q)\<close>
| \<open>psubst f (Neg p) = Neg (psubst f p)\<close>
| \<open>psubst f (Forall p) = Forall (psubst f p)\<close>
| \<open>psubst f (Exists p) = Exists (psubst f p)\<close>

theorem psubstt_closed [simp]:
  \<open>closedt i (psubstt f t) = closedt i t\<close>
  \<open>closedts i (psubstts f ts) = closedts i ts\<close>
  by (induct t and ts rule: closedt.induct closedts.induct) simp_all

theorem psubst_closed [simp]:
  \<open>closed i (psubst f p) = closed i p\<close>
  by (induct p arbitrary: i) simp_all

theorem psubstt_subst [simp]:
  \<open>psubstt f (substt t u i) = substt (psubstt f t) (psubstt f u) i\<close>
  \<open>psubstts f (substts ts u i) = substts (psubstts f ts) (psubstt f u) i\<close>
  by (induct t and ts rule: psubstt.induct psubstts.induct) simp_all

theorem psubstt_lift [simp]:
  \<open>psubstt f (liftt t) = liftt (psubstt f t)\<close>
  \<open>psubstts f (liftts ts) = liftts (psubstts f ts)\<close>
  by (induct t and ts rule: psubstt.induct psubstts.induct) simp_all

theorem psubst_subst [simp]:
  \<open>psubst f (subst P t i) = subst (psubst f P) (psubstt f t) i\<close>
  by (induct P arbitrary: i t) simp_all

theorem psubstt_upd [simp]:
  \<open>x \<notin> paramst (t::'a term) \<Longrightarrow> psubstt (f(x := y)) t = psubstt f t\<close>
  \<open>x \<notin> paramsts (ts::'a term list) \<Longrightarrow> psubstts (f(x := y)) ts = psubstts f ts\<close>
  by (induct t and ts rule: psubstt.induct psubstts.induct) (auto split: sum.split)

theorem psubst_upd [simp]: \<open>x \<notin> params P \<Longrightarrow> psubst (f(x := y)) P = psubst f P\<close>
  by (induct P) (simp_all del: fun_upd_apply)

theorem psubstt_id:
  fixes t :: \<open>'a term\<close> and ts :: \<open>'a term list\<close>
  shows \<open>psubstt id t = t\<close> and \<open>psubstts (\<lambda>x. x) ts = ts\<close>
  by (induct t and ts rule: psubstt.induct psubstts.induct) simp_all

theorem psubst_id [simp]: \<open>psubst id = id\<close>
proof
  fix p :: \<open>('a, 'b) form\<close>
  show \<open>psubst id p = id p\<close>
    by (induct p) (simp_all add: psubstt_id)
qed

theorem psubstt_image [simp]:
  \<open>paramst (psubstt f t) = f ` paramst t\<close>
  \<open>paramsts (psubstts f ts) = f ` paramsts ts\<close>
  by (induct t and ts rule: paramst.induct paramsts.induct) (simp_all add: image_Un)

theorem psubst_image [simp]: \<open>params (psubst f p) = f ` params p\<close>
  by (induct p) (simp_all add: image_Un)

section \<open>Semantics\<close>

text \<open>
\label{sec:semantics}
In this section, we define evaluation functions for terms and formulae.
Evaluation is performed relative to an environment mapping indices of variables
to values. We also introduce a function, denoted by \<open>e\<langle>i:a\<rangle>\<close>, for inserting
a value \<open>a\<close> at position \<open>i\<close> into the environment. All values of variables
with indices less than \<open>i\<close> are left untouched by this operation, whereas the
values of variables with indices greater or equal than \<open>i\<close> are shifted one
position up.
\<close>

definition shift :: \<open>(nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a\<close> ("_\<langle>_:_\<rangle>" [90, 0, 0] 91) where
  \<open>e\<langle>i:a\<rangle> = (\<lambda>j. if j < i then e j else if j = i then a else e (j - 1))\<close>

lemma shift_eq [simp]: \<open>i = j \<Longrightarrow> (e\<langle>i:T\<rangle>) j = T\<close>
  by (simp add: shift_def)

lemma shift_gt [simp]: \<open>j < i \<Longrightarrow> (e\<langle>i:T\<rangle>) j = e j\<close>
  by (simp add: shift_def)

lemma shift_lt [simp]: \<open>i < j \<Longrightarrow> (e\<langle>i:T\<rangle>) j = e (j - 1)\<close>
  by (simp add: shift_def)

lemma shift_commute [simp]: \<open>e\<langle>i:U\<rangle>\<langle>0:T\<rangle> = e\<langle>0:T\<rangle>\<langle>Suc i:U\<rangle>\<close>
proof
  fix x
  show \<open>(e\<langle>i:U\<rangle>\<langle>0:T\<rangle>) x = (e\<langle>0:T\<rangle>\<langle>Suc i:U\<rangle>) x\<close>
    by (cases x) (simp_all add: shift_def)
qed

primrec
  evalt :: \<open>(nat \<Rightarrow> 'c) \<Rightarrow> ('a \<Rightarrow> 'c list \<Rightarrow> 'c) \<Rightarrow> 'a term \<Rightarrow> 'c\<close> and
  evalts :: \<open>(nat \<Rightarrow> 'c) \<Rightarrow> ('a \<Rightarrow> 'c list \<Rightarrow> 'c) \<Rightarrow> 'a term list \<Rightarrow> 'c list\<close> where
  \<open>evalt e f (Var n) = e n\<close>
| \<open>evalt e f (App a ts) = f a (evalts e f ts)\<close>
| \<open>evalts e f [] = []\<close>
| \<open>evalts e f (t # ts) = evalt e f t # evalts e f ts\<close>

primrec eval :: \<open>(nat \<Rightarrow> 'c) \<Rightarrow> ('a \<Rightarrow> 'c list \<Rightarrow> 'c) \<Rightarrow>
  ('b \<Rightarrow> 'c list \<Rightarrow> bool) \<Rightarrow> ('a, 'b) form \<Rightarrow> bool\<close> where
  \<open>eval e f g FF = False\<close>
| \<open>eval e f g TT = True\<close>
| \<open>eval e f g (Pred a ts) = g a (evalts e f ts)\<close>
| \<open>eval e f g (And p q) = ((eval e f g p) \<and> (eval e f g q))\<close>
| \<open>eval e f g (Or p q) = ((eval e f g p) \<or> (eval e f g q))\<close>
| \<open>eval e f g (Impl p q) = ((eval e f g p) \<longrightarrow> (eval e f g q))\<close>
| \<open>eval e f g (Neg p) = (\<not> (eval e f g p))\<close>
| \<open>eval e f g (Forall p) = (\<forall>z. eval (e\<langle>0:z\<rangle>) f g p)\<close>
| \<open>eval e f g (Exists p) = (\<exists>z. eval (e\<langle>0:z\<rangle>) f g p)\<close>

text \<open>
We write \<open>e,f,g,ps \<Turnstile> p\<close> to mean that the formula \<open>p\<close> is a
semantic consequence of the list of formulae \<open>ps\<close> with respect to an
environment \<open>e\<close> and interpretations \<open>f\<close> and \<open>g\<close> for
function and predicate symbols, respectively.
\<close>

definition model :: \<open>(nat \<Rightarrow> 'c) \<Rightarrow> ('a \<Rightarrow> 'c list \<Rightarrow> 'c) \<Rightarrow> ('b \<Rightarrow> 'c list \<Rightarrow> bool) \<Rightarrow>
    ('a, 'b) form list \<Rightarrow> ('a, 'b) form \<Rightarrow> bool\<close> ("_,_,_,_ \<Turnstile> _" [50,50] 50) where
  \<open>(e,f,g,ps \<Turnstile> p) = (list_all (eval e f g) ps \<longrightarrow> eval e f g p)\<close>

text \<open>
The following substitution lemmas relate substitution and evaluation functions:
\<close>

theorem subst_lemma' [simp]:
  \<open>evalt e f (substt t u i) = evalt (e\<langle>i:evalt e f u\<rangle>) f t\<close>
  \<open>evalts e f (substts ts u i) = evalts (e\<langle>i:evalt e f u\<rangle>) f ts\<close>
  by (induct t and ts rule: substt.induct substts.induct) simp_all

theorem lift_lemma [simp]:
  \<open>evalt (e\<langle>0:z\<rangle>) f (liftt t) = evalt e f t\<close>
  \<open>evalts (e\<langle>0:z\<rangle>) f (liftts ts) = evalts e f ts\<close>
  by (induct t and ts rule: liftt.induct liftts.induct) simp_all

theorem subst_lemma [simp]:
  \<open>eval e f g (subst a t i) = eval (e\<langle>i:evalt e f t\<rangle>) f g a\<close>
  by (induct a arbitrary: e i t) simp_all

theorem upd_lemma' [simp]:
  \<open>n \<notin> paramst t \<Longrightarrow> evalt e (f(n := x)) t = evalt e f t\<close>
  \<open>n \<notin> paramsts ts \<Longrightarrow> evalts e (f(n := x)) ts = evalts e f ts\<close>
  by (induct t and ts rule: paramst.induct paramsts.induct) auto

theorem upd_lemma [simp]:
  \<open>n \<notin> params p \<Longrightarrow> eval e (f(n := x)) g p = eval e f g p\<close>
  by (induct p arbitrary: e) simp_all

theorem list_upd_lemma [simp]: \<open>list_all (\<lambda>p. n \<notin> params p) G \<Longrightarrow>
  list_all (eval e (f(n := x)) g) G = list_all (eval e f g) G\<close>
  by (induct G) simp_all

theorem psubst_eval' [simp]:
  \<open>evalt e f (psubstt h t) = evalt e (\<lambda>p. f (h p)) t\<close>
  \<open>evalts e f (psubstts h ts) = evalts e (\<lambda>p. f (h p)) ts\<close>
  by (induct t and ts rule: psubstt.induct psubstts.induct) simp_all

theorem psubst_eval:
  \<open>eval e f g (psubst h p) = eval e (\<lambda>p. f (h p)) g p\<close>
  by (induct p arbitrary: e) simp_all

text \<open>
In order to test the evaluation function defined above, we apply it
to an example:
\<close>

theorem ex_all_commute_eval:
  \<open>eval e f g (Impl (Exists (Forall (Pred p [Var 1, Var 0])))
    (Forall (Exists (Pred p [Var 0, Var 1]))))\<close>
  apply simp
  txt \<open>
Simplification yields the following proof state:
@{subgoals [display]}
This is easily proved using intuitionistic logic:
\<close>
  by iprover

section \<open>Proof calculus\<close>

text \<open>
\label{sec:proof-calculus}
We now introduce a natural deduction proof calculus for first order logic.
The derivability judgement \<open>G \<turnstile> a\<close> is defined as an inductive predicate.
\<close>

inductive deriv :: \<open>('a, 'b) form list \<Rightarrow> ('a, 'b) form \<Rightarrow> bool\<close> ("_ \<turnstile> _" [50,50] 50) where
  Assum: \<open>a \<in> set G \<Longrightarrow> G \<turnstile> a\<close>
| TTI: \<open>G \<turnstile> TT\<close>
| FFE: \<open>G \<turnstile> FF \<Longrightarrow> G \<turnstile> a\<close>
| NegI: \<open>a # G \<turnstile> FF \<Longrightarrow> G \<turnstile> Neg a\<close>
| NegE: \<open>G \<turnstile> Neg a \<Longrightarrow> G \<turnstile> a \<Longrightarrow> G \<turnstile> FF\<close>
| Class: \<open>Neg a # G \<turnstile> FF \<Longrightarrow> G \<turnstile> a\<close>
| AndI: \<open>G \<turnstile> a \<Longrightarrow> G \<turnstile> b \<Longrightarrow> G \<turnstile> And a b\<close>
| AndE1: \<open>G \<turnstile> And a b \<Longrightarrow> G \<turnstile> a\<close>
| AndE2: \<open>G \<turnstile> And a b \<Longrightarrow> G \<turnstile> b\<close>
| OrI1: \<open>G \<turnstile> a \<Longrightarrow> G \<turnstile> Or a b\<close>
| OrI2: \<open>G \<turnstile> b \<Longrightarrow> G \<turnstile> Or a b\<close>
| OrE: \<open>G \<turnstile> Or a b \<Longrightarrow> a # G \<turnstile> c \<Longrightarrow> b # G \<turnstile> c \<Longrightarrow> G \<turnstile> c\<close>
| ImplI: \<open>a # G \<turnstile> b \<Longrightarrow> G \<turnstile> Impl a b\<close>
| ImplE: \<open>G \<turnstile> Impl a b \<Longrightarrow> G \<turnstile> a \<Longrightarrow> G \<turnstile> b\<close>
| ForallI: \<open>G \<turnstile> a[App n []/0] \<Longrightarrow> list_all (\<lambda>p. n \<notin> params p) G \<Longrightarrow>
    n \<notin> params a \<Longrightarrow> G \<turnstile> Forall a\<close>
| ForallE: \<open>G \<turnstile> Forall a \<Longrightarrow> G \<turnstile> a[t/0]\<close>
| ExistsI: \<open>G \<turnstile> a[t/0] \<Longrightarrow> G \<turnstile> Exists a\<close>
| ExistsE: \<open>G \<turnstile> Exists a \<Longrightarrow> a[App n []/0] # G \<turnstile> b \<Longrightarrow>
    list_all (\<lambda>p. n \<notin> params p) G \<Longrightarrow> n \<notin> params a \<Longrightarrow> n \<notin> params b \<Longrightarrow> G \<turnstile> b\<close>

text \<open>
The following derived inference rules are sometimes useful in applications.
\<close>

theorem Class': \<open>Neg A # G \<turnstile> A \<Longrightarrow> G \<turnstile> A\<close>
  by (rule Class, rule NegE, rule Assum) (simp, iprover)

theorem cut: \<open>G \<turnstile> A \<Longrightarrow> A # G \<turnstile> B \<Longrightarrow> G \<turnstile> B\<close>
  by (rule ImplE, rule ImplI)

theorem ForallE': \<open>G \<turnstile> Forall a \<Longrightarrow> subst a t 0 # G \<turnstile> B \<Longrightarrow> G \<turnstile> B\<close>
  by (rule cut, rule ForallE)

text \<open>
As an example, we show that the excluded middle, a commutation property
for existential and universal quantifiers, the drinker principle, as well
as Peirce's law are derivable in the calculus given above.
\<close>

theorem tnd: \<open>[] \<turnstile> Or (Pred p []) (Neg (Pred p []))\<close> (is \<open>_ \<turnstile> ?or\<close>)
proof -
  have \<open>[Neg ?or] \<turnstile> Neg ?or\<close>
    by (simp add: Assum)
  moreover { have \<open>[Pred p [], Neg ?or] \<turnstile> Neg ?or\<close>
      by (simp add: Assum)
    moreover have \<open>[Pred p [], Neg ?or] \<turnstile> Pred p []\<close>
      by (simp add: Assum)
    then have \<open>[Pred p [], Neg ?or] \<turnstile> ?or\<close>
      by (rule OrI1)
    ultimately have \<open>[Pred p [], Neg ?or] \<turnstile> FF\<close>
      by (rule NegE)
    then have \<open>[Neg ?or] \<turnstile> Neg (Pred p [])\<close>
      by (rule NegI)
    then have \<open>[Neg ?or] \<turnstile> ?or\<close>
      by (rule OrI2) }
  ultimately have \<open>[Neg ?or] \<turnstile> FF\<close>
    by (rule NegE)
  then show ?thesis
    by (rule Class)
qed

theorem ex_all_commute:
  \<open>([]::(nat, 'b) form list) \<turnstile> Impl (Exists (Forall (Pred p [Var 1, Var 0])))
     (Forall (Exists (Pred p [Var 0, Var 1])))\<close>
proof -
  let ?forall = \<open>Forall (Pred p [Var 1, Var 0]) :: (nat, 'b) form\<close>

  have \<open>[Exists ?forall] \<turnstile> Exists ?forall\<close>
    by (simp add: Assum)
  moreover { have \<open>[?forall[App 1 []/0], Exists ?forall] \<turnstile> Forall (Pred p [App 1 [], Var 0])\<close>
      by (simp add: Assum)
    moreover have \<open>[Pred p [App 1 [], Var 0][App 0 []/0], ?forall[App 1 []/0],
      Exists ?forall] \<turnstile> Pred p [Var 0, App 0 []][App 1 []/0]\<close>
      by (simp add: Assum)
    ultimately have \<open>[?forall[App 1 []/0], Exists ?forall] \<turnstile> (Pred p [Var 0, App 0 []])[App 1 []/0]\<close>
      by (rule ForallE') }
  then have \<open>[?forall[App 1 []/0], Exists ?forall] \<turnstile> Exists (Pred p [Var 0, App 0 []])\<close>
    by (rule ExistsI)
  moreover have \<open>list_all (\<lambda>p. 1 \<notin> params p) [Exists ?forall]\<close>
    by simp
  moreover have \<open>1 \<notin> params ?forall\<close>
    by simp
  moreover have \<open>1 \<notin> params (Exists (Pred p [Var 0, App (0 :: nat) []]))\<close>
    by simp
  ultimately have \<open>[Exists ?forall] \<turnstile> Exists (Pred p [Var 0, App 0 []])\<close>
    by (rule ExistsE)
  then have \<open>[Exists ?forall] \<turnstile> (Exists (Pred p [Var 0, Var 1]))[App 0 []/0]\<close>
    by simp
  moreover have \<open>list_all (\<lambda>p. 0 \<notin> params p) [Exists ?forall]\<close>
    by simp
  moreover have \<open>0 \<notin> params (Exists (Pred p [Var 0, Var 1]))\<close>
    by simp
  ultimately have \<open>[Exists ?forall] \<turnstile> Forall (Exists (Pred p [Var 0, Var 1]))\<close>
    by (rule ForallI)
  then show ?thesis
    by (rule ImplI)
qed

theorem drinker: \<open>([]::(nat, 'b) form list) \<turnstile>
  Exists (Impl (Pred P [Var 0]) (Forall (Pred P [Var 0])))\<close>
proof -
  let ?impl = \<open>(Impl (Pred P [Var 0]) (Forall (Pred P [Var 0]))) :: (nat, 'b) form\<close>
  let ?G' = \<open>[Pred P [Var 0], Neg (Exists ?impl)]\<close>
  let ?G = \<open>Neg (Pred P [App 0 []]) # ?G'\<close>

  have \<open>?G \<turnstile> Neg (Exists ?impl)\<close>
    by (simp add: Assum)
  moreover have \<open>Pred P [App 0 []] # ?G \<turnstile> Neg (Pred P [App 0 []])\<close>
    and \<open>Pred P [App 0 []] # ?G \<turnstile> Pred P [App 0 []]\<close>
    by (simp_all add: Assum)
  then have \<open>Pred P [App 0 []] # ?G \<turnstile> FF\<close>
    by (rule NegE)
  then have \<open>Pred P [App 0 []] # ?G \<turnstile> Forall (Pred P [Var 0])\<close>
    by (rule FFE)
  then have \<open>?G \<turnstile> ?impl[App 0 []/0]\<close>
    using ImplI by simp
  then have \<open>?G \<turnstile> Exists ?impl\<close>
    by (rule ExistsI)
  ultimately have \<open>?G \<turnstile> FF\<close>
    by (rule NegE)
  then have \<open>?G' \<turnstile> Pred P [Var 0][App 0 []/0]\<close>
    using Class by simp
  moreover have \<open>list_all (\<lambda>p. (0 :: nat) \<notin> params p) ?G'\<close>
    by simp
  moreover have \<open>(0 :: nat) \<notin> params (Pred P [Var 0])\<close>
    by simp
  ultimately have \<open>?G' \<turnstile> Forall (Pred P [Var 0])\<close>
    by (rule ForallI)
  then have \<open>[Neg (Exists ?impl)] \<turnstile> ?impl[Var 0/0]\<close>
    using ImplI by simp
  then have \<open>[Neg (Exists ?impl)] \<turnstile> Exists ?impl\<close>
    by (rule ExistsI)
  then show ?thesis
    by (rule Class')
qed

theorem peirce:
  \<open>[] \<turnstile> Impl (Impl (Impl (Pred P []) (Pred Q [])) (Pred P [])) (Pred P [])\<close>
  (is \<open>[] \<turnstile> Impl ?PQP (Pred P [])\<close>)
proof -
  let ?PQPP = \<open>Impl ?PQP (Pred P [])\<close>

  have \<open>[?PQP, Neg ?PQPP] \<turnstile> ?PQP\<close>
    by (simp add: Assum)
  moreover { have \<open>[Pred P [], ?PQP, Neg ?PQPP] \<turnstile> Neg ?PQPP\<close>
      by (simp add: Assum)
    moreover have \<open>[?PQP, Pred P [], ?PQP, Neg ?PQPP] \<turnstile> Pred P []\<close>
      by (simp add: Assum)
    then have \<open>[Pred P [], ?PQP, Neg ?PQPP] \<turnstile> ?PQPP\<close>
      by (rule ImplI)
    ultimately have \<open>[Pred P [], ?PQP, Neg ?PQPP] \<turnstile> FF\<close>
      by (rule NegE) }
  then have \<open>[Pred P [], ?PQP, Neg ?PQPP] \<turnstile> Pred Q []\<close>
    by (rule FFE)
  then have \<open>[?PQP, Neg ?PQPP] \<turnstile> Impl (Pred P []) (Pred Q [])\<close>
    by (rule ImplI)
  ultimately have \<open>[?PQP, Neg ?PQPP] \<turnstile> Pred P []\<close>
    by (rule ImplE)
  then have \<open>[Neg ?PQPP] \<turnstile> ?PQPP\<close>
    by (rule ImplI)
  then show \<open>[] \<turnstile> ?PQPP\<close>
    by (rule Class')
qed

section \<open>Correctness\<close>

text \<open>
The correctness of the proof calculus introduced in \secref{sec:proof-calculus}
can now be proved by induction on the derivation of @{term \<open>G \<turnstile> p\<close>}, using the
substitution rules proved in \secref{sec:semantics}.
\<close>

theorem correctness: \<open>G \<turnstile> p \<Longrightarrow> \<forall>e f g. e,f,g,G \<Turnstile> p\<close>
proof (induct p rule: deriv.induct)
  case (Assum a G)
  then show ?case by (simp add: model_def list_all_iff)
next
  case (ForallI G a n)
  show ?case
  proof (intro allI)
    fix f g and e :: \<open>nat \<Rightarrow> 'c\<close>
    have \<open>\<forall>z. e, (f(n := \<lambda>x. z)), g, G \<Turnstile> (a[App n []/0])\<close>
      using ForallI by blast
    then have \<open>\<forall>z. list_all (eval e f g) G \<longrightarrow> eval (e\<langle>0:z\<rangle>) f g a\<close>
      using ForallI unfolding model_def by simp
    then show \<open>e,f,g,G \<Turnstile> Forall a\<close> unfolding model_def by simp
  qed
next
  case (ExistsE G a n b)
  show ?case
  proof (intro allI)
    fix f g and e :: \<open>nat \<Rightarrow> 'c\<close>
    obtain z where \<open>list_all (eval e f g) G \<longrightarrow> eval (e\<langle>0:z\<rangle>) f g a\<close>
      using ExistsE unfolding model_def by simp blast
    then have \<open>e, (f(n := \<lambda>x. z)), g, G \<Turnstile> b\<close>
      using ExistsE unfolding model_def by simp
    then show \<open>e,f,g,G \<Turnstile> b\<close>
      using ExistsE unfolding model_def by simp
  qed
qed (simp_all add: model_def, blast+)

section \<open>Completeness\<close>

text \<open>
The goal of this section is to prove completeness of the natural deduction
calculus introduced in \secref{sec:proof-calculus}. Before we start with the
actual proof, it is useful to note that the following two formulations of
completeness are equivalent:
\begin{enumerate}
\item All valid formulae are derivable, i.e.
  \<open>ps \<Turnstile> p \<Longrightarrow> ps \<turnstile> p\<close>
\item All consistent sets are satisfiable
\end{enumerate}
The latter property is called the {\em model existence theorem}. To see why 2
implies 1, observe that \<open>Neg p, ps \<notturnstile> FF\<close> implies
that \<open>Neg p, ps\<close> is consistent, which, by the model existence theorem,
implies that \<open>Neg p, ps\<close> has a model, which in turn implies that
\<open>ps \<notTurnstile> p\<close>. By contraposition, it therefore follows
from \<open>ps \<Turnstile> p\<close> that \<open>Neg p, ps \<turnstile> FF\<close>, which allows us to
deduce \<open>ps \<turnstile> p\<close> using rule \<open>Class\<close>.

In most textbooks on logic, a set \<open>S\<close> of formulae is called {\em consistent},
if no contradiction can be derived from \<open>S\<close> using a {\em specific proof calculus},
i.e.\ \<open>S \<notturnstile> FF\<close>. Rather than defining consistency relative to
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
\<close>

subsection \<open>Consistent sets\<close>

text \<open>
\label{sec:consistent-sets}
In this section, we describe an abstract criterion for consistent sets.
A set of sets of formulae is called a {\em consistency property}, if the
following holds:
\<close>

definition consistency :: \<open>('a, 'b) form set set \<Rightarrow> bool\<close> where
  \<open>consistency C = (\<forall>S. S \<in> C \<longrightarrow>
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
     (\<forall>P. Neg (Forall P) \<in> S \<longrightarrow> (\<exists>x. S \<union> {Neg (P[App x []/0])} \<in> C)))\<close>

text \<open>
In \secref{sec:finiteness}, we will show how to extend a consistency property
to one that is of {\em finite character}. However, the above
definition of a consistency property cannot be used for this, since there is
a problem with the treatment of formulae of the form \<open>Exists P\<close> and
\<open>Neg (Forall P)\<close>. Fitting therefore suggests to define an {\em alternative
consistency property} as follows:
\<close>

definition alt_consistency :: \<open>('a, 'b) form set set \<Rightarrow> bool\<close> where
  \<open>alt_consistency C = (\<forall>S. S \<in> C \<longrightarrow>
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
     (\<forall>P x. (\<forall>a \<in> S. x \<notin> params a) \<longrightarrow> Exists P \<in> S \<longrightarrow>
       S \<union> {P[App x []/0]} \<in> C) \<and>
     (\<forall>P x. (\<forall>a \<in> S. x \<notin> params a) \<longrightarrow> Neg (Forall P) \<in> S \<longrightarrow>
       S \<union> {Neg (P[App x []/0])} \<in> C))\<close>

text \<open>
Note that in the clauses for \<open>Exists P\<close> and \<open>Neg (Forall P)\<close>,
the first definition requires the existence of a parameter \<open>x\<close> with a certain
property, whereas the second definition requires that all parameters \<open>x\<close> that
are new for \<open>S\<close> have a certain property. A consistency property can easily be
turned into an alternative consistency property by applying a suitable parameter
substitution:
\<close>

definition mk_alt_consistency :: \<open>('a, 'b) form set set \<Rightarrow> ('a, 'b) form set set\<close> where
  \<open>mk_alt_consistency C = {S. \<exists>f. psubst f ` S \<in> C}\<close>

theorem alt_consistency:
  assumes conc: \<open>consistency C\<close>
  shows \<open>alt_consistency (mk_alt_consistency C)\<close> (is \<open>alt_consistency ?C'\<close>)
  unfolding alt_consistency_def
proof (intro allI impI conjI)
  fix f :: \<open>'a \<Rightarrow> 'a\<close> and S :: \<open>('a, 'b) form set\<close>

  assume \<open>S \<in> mk_alt_consistency C\<close>
  then obtain f where sc: \<open>psubst f ` S \<in> C\<close> (is \<open>?S' \<in> C\<close>)
    unfolding mk_alt_consistency_def by blast

  fix p ts
  show \<open>\<not> (Pred p ts \<in> S \<and> Neg (Pred p ts) \<in> S)\<close>
  proof
    assume *: \<open>Pred p ts \<in> S \<and> Neg (Pred p ts) \<in> S\<close>
    then have \<open>psubst f (Pred p ts) \<in> ?S'\<close>
      by blast
    then have \<open>Pred p (psubstts f ts) \<in> ?S'\<close>
      by simp
    then have \<open>Neg (Pred p (psubstts f ts)) \<notin> ?S'\<close>
      using conc sc by (simp add: consistency_def)
    then have \<open>Neg (Pred p ts) \<notin> S\<close>
      by force
    then show False
      using * by blast
  qed

  have \<open>FF \<notin> ?S'\<close> and \<open>Neg TT \<notin> ?S'\<close>
    using conc sc unfolding consistency_def by simp_all
  then show \<open>FF \<notin> S\<close> and \<open>Neg TT \<notin> S\<close>
    by (force, force)

  { fix Z
    assume \<open>Neg (Neg Z) \<in> S\<close>
    then have \<open>psubst f (Neg (Neg Z)) \<in> ?S'\<close>
      by blast
    then have \<open>?S' \<union> {psubst f Z} \<in> C\<close>
      using conc sc by (simp add: consistency_def)
    then show \<open>S \<union> {Z} \<in> ?C'\<close>
      unfolding mk_alt_consistency_def by auto }

  { fix A B
    assume \<open>And A B \<in> S\<close>
    then have \<open>psubst f (And A B) \<in> ?S'\<close>
      by blast
    then have \<open>?S' \<union> {psubst f A, psubst f B} \<in> C\<close>
      using conc sc by (simp add: consistency_def)
    then show \<open>S \<union> {A, B} \<in> ?C'\<close>
      unfolding mk_alt_consistency_def by auto }

  { fix A B
    assume \<open>Neg (Or A B) \<in> S\<close>
    then have \<open>psubst f (Neg (Or A B)) \<in> ?S'\<close>
      by blast
    then have \<open>?S' \<union> {Neg (psubst f A), Neg (psubst f B)} \<in> C\<close>
      using conc sc by (simp add: consistency_def)
    then show \<open>S \<union> {Neg A, Neg B} \<in> ?C'\<close>
      unfolding mk_alt_consistency_def by auto }

  { fix A B
    assume \<open>Neg (Impl A B) \<in> S\<close>
    then have \<open>psubst f (Neg (Impl A B)) \<in> ?S'\<close>
      by blast
    then have \<open>?S' \<union> {psubst f A, Neg (psubst f B)} \<in> C\<close>
      using conc sc by (simp add: consistency_def)
    then show \<open>S \<union> {A, Neg B} \<in> ?C'\<close>
      unfolding mk_alt_consistency_def by auto }

  { fix A B
    assume \<open>Or A B \<in> S\<close>
    then have \<open>psubst f (Or A B) \<in> ?S'\<close>
      by blast
    then have \<open>?S' \<union> {psubst f A} \<in> C \<or> ?S' \<union> {psubst f B} \<in> C\<close>
      using conc sc by (simp add: consistency_def)
    then show \<open>S \<union> {A} \<in> ?C' \<or> S \<union> {B} \<in> ?C'\<close>
      unfolding mk_alt_consistency_def by auto }

  { fix A B
    assume \<open>Neg (And A B) \<in> S\<close>
    then have \<open>psubst f (Neg (And A B)) \<in> ?S'\<close>
      by blast
    then have \<open>?S' \<union> {Neg (psubst f A)} \<in> C \<or> ?S' \<union> {Neg (psubst f B)} \<in> C\<close>
      using conc sc by (simp add: consistency_def)
    then show \<open>S \<union> {Neg A} \<in> ?C' \<or> S \<union> {Neg B} \<in> ?C'\<close>
      unfolding mk_alt_consistency_def by auto }

  { fix A B
    assume \<open>Impl A B \<in> S\<close>
    then have \<open>psubst f (Impl A B) \<in> ?S'\<close>
      by blast
    then have \<open>?S' \<union> {Neg (psubst f A)} \<in> C \<or> ?S' \<union> {psubst f B} \<in> C\<close>
      using conc sc by (simp add: consistency_def)
    then show \<open>S \<union> {Neg A} \<in> ?C' \<or> S \<union> {B} \<in> ?C'\<close>
      unfolding mk_alt_consistency_def by auto }

  { fix P and t :: \<open>'a term\<close>
    assume \<open>closedt 0 t\<close> and \<open>Forall P \<in> S\<close>
    then have \<open>psubst f (Forall P) \<in> ?S'\<close>
      by blast
    then have \<open>?S' \<union> {psubst f P[psubstt f t/0]} \<in> C\<close>
      using \<open>closedt 0 t\<close> conc sc by (simp add: consistency_def)
    then show \<open>S \<union> {P[t/0]} \<in> ?C'\<close>
      unfolding mk_alt_consistency_def by auto }

  { fix P and t :: \<open>'a term\<close>
    assume \<open>closedt 0 t\<close> and \<open>Neg (Exists P) \<in> S\<close>
    then have \<open>psubst f (Neg (Exists P)) \<in> ?S'\<close>
      by blast
    then have \<open>?S' \<union> {Neg (psubst f P[psubstt f t/0])} \<in> C\<close>
      using \<open>closedt 0 t\<close> conc sc by (simp add: consistency_def)
    then show \<open>S \<union> {Neg (P[t/0])} \<in> ?C'\<close>
      unfolding mk_alt_consistency_def by auto }

  { fix P :: \<open>('a, 'b) form\<close> and x f'
    assume \<open>\<forall>a \<in> S. x \<notin> params a\<close> and \<open>Exists P \<in> S\<close>
    moreover have \<open>psubst f (Exists P) \<in> ?S'\<close>
      using calculation by blast
    then have \<open>\<exists>y. ?S' \<union> {psubst f P[App y []/0]} \<in> C\<close>
      using conc sc by (simp add: consistency_def)
    then obtain y where \<open>?S' \<union> {psubst f P[App y []/0]} \<in> C\<close>
      by blast

    moreover have \<open>psubst (f(x := y)) ` S = ?S'\<close>
      using calculation by (simp cong add: image_cong)
    moreover have \<open>psubst (f(x := y)) `
        S \<union> {psubst (f(x := y)) P[App ((f(x := y)) x) []/0]} \<in> C\<close>
      using calculation by auto
    ultimately have \<open>\<exists>f. psubst f ` S \<union> {psubst f P[App (f x) []/0]} \<in> C\<close>
      by blast
    then show \<open>S \<union> {P[App x []/0]} \<in> ?C'\<close>
      unfolding mk_alt_consistency_def by simp }

  { fix P :: \<open>('a, 'b) form\<close> and x
    assume \<open>\<forall>a \<in> S. x \<notin> params a\<close> and \<open>Neg (Forall P) \<in> S\<close>
    moreover have \<open>psubst f (Neg (Forall P)) \<in> ?S'\<close>
      using calculation by blast
    then have \<open>\<exists>y. ?S' \<union> {Neg (psubst f P[App y []/0])} \<in> C\<close>
      using conc sc by (simp add: consistency_def)
    then obtain y where \<open>?S' \<union> {Neg (psubst f P[App y []/0])} \<in> C\<close>
      by blast

    moreover have \<open>psubst (f(x := y)) ` S = ?S'\<close>
      using calculation by (simp cong add: image_cong)
    moreover have \<open>psubst (f(x := y)) `
    S \<union> {Neg (psubst (f(x := y)) P[App ((f(x := y)) x) []/0])} \<in> C\<close>
      using calculation by auto
    ultimately have \<open>\<exists>f. psubst f ` S \<union> {Neg (psubst f P[App (f x) []/0])} \<in> C\<close>
      by blast
    then show \<open>S \<union> {Neg (P[App x []/0])} \<in> ?C'\<close>
      unfolding mk_alt_consistency_def by simp }
qed

theorem mk_alt_consistency_subset: \<open>C \<subseteq> mk_alt_consistency C\<close>
  unfolding mk_alt_consistency_def
proof
  fix x assume \<open>x \<in> C\<close>
  then have \<open>psubst id ` x \<in> C\<close>
    by simp
  then have \<open>(\<exists>f. psubst f ` x \<in> C)\<close>
    by blast
  then show \<open>x \<in> {S. \<exists>f. psubst f ` S \<in> C}\<close>
    by simp
qed

subsection \<open>Closure under subsets\<close>

text \<open>
\label{sec:closure}
We now show that a consistency property can be extended to one
that is closed under subsets.
\<close>

definition close :: \<open>('a, 'b) form set set \<Rightarrow> ('a, 'b) form set set\<close> where
  \<open>close C = {S. \<exists>S' \<in> C. S \<subseteq> S'}\<close>

definition subset_closed :: \<open>'a set set \<Rightarrow> bool\<close> where
  \<open>subset_closed C = (\<forall>S' \<in> C. \<forall>S. S \<subseteq> S' \<longrightarrow> S \<in> C)\<close>

lemma subset_in_close:
  assumes \<open>S \<subseteq> S'\<close>
  shows \<open>S' \<union> x \<in> C \<longrightarrow> S \<union> x \<in> close C\<close>
proof -
  have \<open>S' \<union> x \<in> close C \<longrightarrow> S \<union> x \<in> close C\<close>
    unfolding close_def using \<open>S \<subseteq> S'\<close> by blast
  then show ?thesis unfolding close_def by blast
qed

theorem close_consistency:
  assumes conc: \<open>consistency C\<close>
  shows \<open>consistency (close C)\<close>
  unfolding consistency_def
proof (intro allI impI conjI)
  fix S
  assume \<open>S \<in> close C\<close>
  then obtain x where \<open>x \<in> C\<close> and \<open>S \<subseteq> x\<close>
    unfolding close_def by blast

  { fix p ts
    have \<open>\<not> (Pred p ts \<in> x \<and> Neg (Pred p ts) \<in> x)\<close>
      using \<open>x \<in> C\<close> conc unfolding consistency_def by simp
    then show \<open>\<not> (Pred p ts \<in> S \<and> Neg (Pred p ts) \<in> S)\<close>
      using \<open>S \<subseteq> x\<close> by blast }

  { have \<open>FF \<notin> x\<close>
      using \<open>x \<in> C\<close> conc unfolding consistency_def by blast
    then show \<open>FF \<notin> S\<close>
      using \<open>S \<subseteq> x\<close> by blast }

  { have \<open>Neg TT \<notin> x\<close>
      using \<open>x \<in> C\<close> conc unfolding consistency_def by blast
    then show \<open>Neg TT \<notin> S\<close>
      using \<open>S \<subseteq> x\<close> by blast }

  { fix Z
    assume \<open>Neg (Neg Z) \<in> S\<close>
    then have \<open>Neg (Neg Z) \<in> x\<close>
      using \<open>S \<subseteq> x\<close> by blast
    then have \<open>x \<union> {Z} \<in> C\<close>
      using \<open>x \<in> C\<close> conc unfolding consistency_def by simp
    then show \<open>S \<union> {Z} \<in> close C\<close>
      using \<open>S \<subseteq> x\<close> subset_in_close by blast }

  { fix A B
    assume \<open>And A B \<in> S\<close>
    then have \<open>And A B \<in> x\<close>
      using \<open>S \<subseteq> x\<close> by blast
    then have \<open>x \<union> {A, B} \<in> C\<close>
      using \<open>x \<in> C\<close> conc unfolding consistency_def by simp
    then show \<open>S \<union> {A, B} \<in> close C\<close>
      using \<open>S \<subseteq> x\<close> subset_in_close by blast }

  { fix A B
    assume \<open>Neg (Or A B) \<in> S\<close>
    then have \<open>Neg (Or A B) \<in> x\<close>
      using \<open>S \<subseteq> x\<close> by blast
    then have \<open>x \<union> {Neg A, Neg B} \<in> C\<close>
      using \<open>x \<in> C\<close> conc unfolding consistency_def by simp
    then show \<open>S \<union> {Neg A, Neg B} \<in> close C\<close>
      using \<open>S \<subseteq> x\<close> subset_in_close by blast }

  { fix A B
    assume \<open>Or A B \<in> S\<close>
    then have \<open>Or A B \<in> x\<close>
      using \<open>S \<subseteq> x\<close> by blast
    then have \<open>x \<union> {A} \<in> C \<or> x \<union> {B} \<in> C\<close>
      using \<open>x \<in> C\<close> conc unfolding consistency_def by simp
    then show \<open>S \<union> {A} \<in> close C \<or> S \<union> {B} \<in> close C\<close>
      using \<open>S \<subseteq> x\<close> subset_in_close by blast }

  { fix A B
    assume \<open>Neg (And A B) \<in> S\<close>
    then have \<open>Neg (And A B) \<in> x\<close>
      using \<open>S \<subseteq> x\<close> by blast
    then have \<open>x \<union> {Neg A} \<in> C \<or> x \<union> {Neg B} \<in> C\<close>
      using \<open>x \<in> C\<close> conc unfolding consistency_def by simp
    then show \<open>S \<union> {Neg A} \<in> close C \<or> S \<union> {Neg B} \<in> close C\<close>
      using \<open>S \<subseteq> x\<close> subset_in_close by blast }

  { fix A B
    assume \<open>Impl A B \<in> S\<close>
    then have \<open>Impl A B \<in> x\<close>
      using \<open>S \<subseteq> x\<close> by blast
    then have \<open>x \<union> {Neg A} \<in> C \<or> x \<union> {B} \<in> C\<close>
      using \<open>x \<in> C\<close> conc unfolding consistency_def by simp
    then show \<open>S \<union> {Neg A} \<in> close C \<or> S \<union> {B} \<in> close C\<close>
      using \<open>S \<subseteq> x\<close> subset_in_close by blast }

  { fix A B
    assume \<open>Neg (Impl A B) \<in> S\<close>
    then have \<open>Neg (Impl A B) \<in> x\<close>
      using \<open>S \<subseteq> x\<close> by blast
    then have \<open>x \<union> {A, Neg B} \<in> C\<close>
      using \<open>x \<in> C\<close> conc unfolding consistency_def by blast
    then show \<open>S \<union> {A, Neg B} \<in> close C\<close>
      using \<open>S \<subseteq> x\<close> subset_in_close by blast }

  { fix P and t :: \<open>'a term\<close>
    assume \<open>closedt 0 t\<close> and \<open>Forall P \<in> S\<close>
    then have \<open>Forall P \<in> x\<close>
      using \<open>S \<subseteq> x\<close> by blast
    then have \<open>x \<union> {P[t/0]} \<in> C\<close>
      using \<open>closedt 0 t\<close> \<open>x \<in> C\<close> conc unfolding consistency_def by blast
    then show \<open>S \<union> {P[t/0]} \<in> close C\<close>
      using \<open>S \<subseteq> x\<close> subset_in_close by blast }

  { fix P and t :: \<open>'a term\<close>
    assume \<open>closedt 0 t\<close> and \<open>Neg (Exists P) \<in> S\<close>
    then have \<open>Neg (Exists P) \<in> x\<close>
      using \<open>S \<subseteq> x\<close> by blast
    then have \<open>x \<union> {Neg (P[t/0])} \<in> C\<close>
      using \<open>closedt 0 t\<close> \<open>x \<in> C\<close> conc unfolding consistency_def by blast
    then show \<open>S \<union> {Neg (P[t/0])} \<in> close C\<close>
      using \<open>S \<subseteq> x\<close> subset_in_close by blast }

  { fix P
    assume \<open>Exists P \<in> S\<close>
    then have \<open>Exists P \<in> x\<close>
      using \<open>S \<subseteq> x\<close> by blast
    then have \<open>\<exists>c. x \<union> {P[App c []/0]} \<in> C\<close>
      using \<open>x \<in> C\<close> conc unfolding consistency_def by blast
    then show \<open>\<exists>c. S \<union> {P[App c []/0]} \<in> close C\<close>
      using \<open>S \<subseteq> x\<close> subset_in_close by blast }

  { fix P
    assume \<open>Neg (Forall P) \<in> S\<close>
    then have \<open>Neg (Forall P) \<in> x\<close>
      using \<open>S \<subseteq> x\<close> by blast
    then have \<open>\<exists>c. x \<union> {Neg (P[App c []/0])} \<in> C\<close>
      using \<open>x \<in> C\<close> conc unfolding consistency_def by simp
    then show \<open>\<exists>c. S \<union> {Neg (P[App c []/0])} \<in> close C\<close>
      using \<open>S \<subseteq> x\<close> subset_in_close by blast }
qed

theorem close_closed: \<open>subset_closed (close C)\<close>
  unfolding close_def subset_closed_def by blast

theorem close_subset: \<open>C \<subseteq> close C\<close>
  unfolding close_def by blast

text \<open>
If a consistency property \<open>C\<close> is closed under subsets, so is the
corresponding alternative consistency property:
\<close>

theorem mk_alt_consistency_closed:
  assumes \<open>subset_closed C\<close>
  shows \<open>subset_closed (mk_alt_consistency C)\<close>
  unfolding subset_closed_def mk_alt_consistency_def
proof (intro ballI allI impI)
  fix S S' :: \<open>('a, 'b) form set\<close>
  assume \<open>S \<subseteq> S'\<close> and \<open>S' \<in> {S. \<exists>f. psubst f ` S \<in> C}\<close>
  then obtain f where *: \<open>psubst f ` S' \<in> C\<close>
    by blast
  moreover have \<open>psubst f ` S \<subseteq> psubst f ` S'\<close>
    using \<open>S \<subseteq> S'\<close> by blast
  moreover have \<open>\<forall>S' \<in> C. \<forall>S \<subseteq> S'. S \<in> C\<close>
    using \<open>subset_closed C\<close> unfolding subset_closed_def by blast
  ultimately have \<open>psubst f ` S \<in> C\<close>
    by blast
  then show \<open>S \<in> {S. \<exists>f. psubst f ` S \<in> C}\<close>
    by blast
qed

subsection \<open>Finite character\<close>

text \<open>
\label{sec:finiteness}
In this section, we show that an alternative consistency property can
be extended to one of finite character. A set of sets \<open>C\<close> is said
to be of finite character, provided that \<open>S\<close> is a member of \<open>C\<close>
if and only if every subset of \<open>S\<close> is.
\<close>

definition finite_char :: \<open>'a set set \<Rightarrow> bool\<close> where
  \<open>finite_char C = (\<forall>S. S \<in> C = (\<forall>S'. finite S' \<longrightarrow> S' \<subseteq> S \<longrightarrow> S' \<in> C))\<close>

definition mk_finite_char :: \<open>'a set set \<Rightarrow> 'a set set\<close> where
  \<open>mk_finite_char C = {S. \<forall>S'. S' \<subseteq> S \<longrightarrow> finite S' \<longrightarrow> S' \<in> C}\<close>

theorem finite_alt_consistency:
  assumes altconc: \<open>alt_consistency C\<close>
    and \<open>subset_closed C\<close>
  shows \<open>alt_consistency (mk_finite_char C)\<close>
  unfolding alt_consistency_def
proof (intro allI impI conjI)
  fix S
  assume \<open>S \<in> mk_finite_char C\<close>
  then have finc: \<open>\<forall>S' \<subseteq> S. finite S' \<longrightarrow> S' \<in> C\<close>
    unfolding mk_finite_char_def by blast

  have \<open>\<forall>S' \<in> C. \<forall>S \<subseteq> S'. S \<in> C\<close>
    using \<open>subset_closed C\<close> unfolding subset_closed_def by blast
  then have sc: \<open>\<forall>S' x. S' \<union> x \<in> C \<longrightarrow> (\<forall>S \<subseteq> S' \<union> x. S \<in> C)\<close>
    by blast

  { fix p ts
    show \<open>\<not> (Pred p ts \<in> S \<and> Neg (Pred p ts) \<in> S)\<close>
    proof
      assume \<open>Pred p ts \<in> S \<and> Neg (Pred p ts) \<in> S\<close>
      then have \<open>{Pred p ts, Neg (Pred p ts)} \<in> C\<close>
        using finc by simp
      then show False
        using altconc unfolding alt_consistency_def by fast
    qed }

  show \<open>FF \<notin> S\<close>
  proof
    assume \<open>FF \<in> S\<close>
    then have \<open>{FF} \<in> C\<close>
      using finc by simp
    then show False
      using altconc unfolding alt_consistency_def by fast
  qed

  show \<open>Neg TT \<notin> S\<close>
  proof
    assume \<open>Neg TT \<in> S\<close>
    then have \<open>{Neg TT} \<in> C\<close>
      using finc by simp
    then show False
      using altconc unfolding alt_consistency_def by fast
  qed

  { fix Z
    assume *: \<open>Neg (Neg Z) \<in> S\<close>
    show \<open>S \<union> {Z} \<in> mk_finite_char C\<close>
      unfolding mk_finite_char_def
    proof (intro allI impI CollectI)
      fix S'
      let ?S' = \<open>S' - {Z} \<union> {Neg (Neg Z)}\<close>

      assume \<open>S' \<subseteq> S \<union> {Z}\<close> and \<open>finite S'\<close>
      then have \<open>?S' \<subseteq> S\<close>
        using * by blast
      moreover have \<open>finite ?S'\<close>
        using \<open>finite S'\<close> by blast
      ultimately have \<open>?S' \<in> C\<close>
        using finc by blast
      then have \<open>?S' \<union> {Z} \<in> C\<close>
        using altconc unfolding alt_consistency_def by simp
      then show \<open>S' \<in> C\<close>
        using sc by blast
    qed }

  { fix A B
    assume *: \<open>And A B \<in> S\<close>
    show \<open>S \<union> {A, B} \<in> mk_finite_char C\<close>
      unfolding mk_finite_char_def
    proof (intro allI impI CollectI)
      fix S'
      let ?S' = \<open>S' - {A, B} \<union> {And A B}\<close>

      assume \<open>S' \<subseteq> S \<union> {A, B}\<close> and \<open>finite S'\<close>
      then have \<open>?S' \<subseteq> S\<close>
        using * by blast
      moreover have \<open>finite ?S'\<close>
        using \<open>finite S'\<close> by blast
      ultimately have \<open>?S' \<in> C\<close>
        using finc by blast
      then have \<open>?S' \<union> {A, B} \<in> C\<close>
        using altconc unfolding alt_consistency_def by simp
      then show \<open>S' \<in> C\<close>
        using sc by blast
    qed }

  { fix A B
    assume *: \<open>Neg (Or A B) \<in> S\<close>
    show \<open>S \<union> {Neg A, Neg B} \<in> mk_finite_char C\<close>
      unfolding mk_finite_char_def
    proof (intro allI impI CollectI)
      fix S'
      let ?S' = \<open>S' - {Neg A, Neg B} \<union> {Neg (Or A B)}\<close>

      assume \<open>S' \<subseteq> S \<union> {Neg A, Neg B}\<close> and \<open>finite S'\<close>
      then have \<open>?S' \<subseteq> S\<close>
        using * by blast
      moreover have \<open>finite ?S'\<close>
        using \<open>finite S'\<close> by blast
      ultimately have \<open>?S' \<in> C\<close>
        using finc by blast
      then have \<open>?S' \<union> {Neg A, Neg B} \<in> C\<close>
        using altconc unfolding alt_consistency_def by simp
      then show \<open>S' \<in> C\<close>
        using sc by blast
    qed }

  { fix A B
    assume *: \<open>Neg (Impl A B) \<in> S\<close>
    show \<open>S \<union> {A, Neg B} \<in> mk_finite_char C\<close>
      unfolding mk_finite_char_def
    proof (intro allI impI CollectI)
      fix S'
      let ?S' = \<open>S' - {A, Neg B} \<union> {Neg (Impl A B)}\<close>

      assume \<open>S' \<subseteq> S \<union> {A, Neg B}\<close> and \<open>finite S'\<close>
      then have \<open>?S' \<subseteq> S\<close>
        using * by blast
      moreover have \<open>finite ?S'\<close>
        using \<open>finite S'\<close> by blast
      ultimately have \<open>?S' \<in> C\<close>
        using finc by blast
      then have \<open>?S' \<union> {A, Neg B} \<in> C\<close>
        using altconc unfolding alt_consistency_def by simp
      then show \<open>S' \<in> C\<close>
        using sc by blast
    qed }

  { fix A B
    assume *: \<open>Or A B \<in> S\<close>
    show \<open>S \<union> {A} \<in> mk_finite_char C \<or> S \<union> {B} \<in> mk_finite_char C\<close>
    proof (rule ccontr)
      assume \<open>\<not> ?thesis\<close>
      then obtain Sa and Sb
        where \<open>Sa \<subseteq> S \<union> {A}\<close> and \<open>finite Sa\<close> and \<open>Sa \<notin> C\<close>
          and \<open>Sb \<subseteq> S \<union> {B}\<close> and \<open>finite Sb\<close> and \<open>Sb \<notin> C\<close>
        unfolding mk_finite_char_def by blast

      let ?S' = \<open>(Sa - {A}) \<union> (Sb - {B}) \<union> {Or A B}\<close>

      have \<open>?S' \<subseteq> S\<close>
        using \<open>Sa \<subseteq> S \<union> {A}\<close> \<open>Sb \<subseteq> S \<union> {B}\<close> * by blast
      moreover have \<open>finite ?S'\<close>
        using \<open>finite Sa\<close> \<open>finite Sb\<close> by blast
      ultimately have \<open>?S' \<in> C\<close>
        using finc by blast
      then have \<open>?S' \<union> {A} \<in> C \<or> ?S' \<union> {B} \<in> C\<close>
        using altconc unfolding alt_consistency_def by simp
      then have \<open>Sa \<in> C \<or> Sb \<in> C\<close>
        using sc by blast
      then show False
        using \<open>Sa \<notin> C\<close> \<open>Sb \<notin> C\<close> by blast
    qed }

  { fix A B
    assume *: \<open>Neg (And A B) \<in> S\<close>
    show \<open>S \<union> {Neg A} \<in> mk_finite_char C \<or> S \<union> {Neg B} \<in> mk_finite_char C\<close>
    proof (rule ccontr)
      assume \<open>\<not> ?thesis\<close>
      then obtain Sa and Sb
        where \<open>Sa \<subseteq> S \<union> {Neg A}\<close> and \<open>finite Sa\<close> and \<open>Sa \<notin> C\<close>
          and \<open>Sb \<subseteq> S \<union> {Neg B}\<close> and \<open>finite Sb\<close> and \<open>Sb \<notin> C\<close>
        unfolding mk_finite_char_def by blast

      let ?S' = \<open>(Sa - {Neg A}) \<union> (Sb - {Neg B}) \<union> {Neg (And A B)}\<close>

      have \<open>?S' \<subseteq> S\<close>
        using \<open>Sa \<subseteq> S \<union> {Neg A}\<close> \<open>Sb \<subseteq> S \<union> {Neg B}\<close> * by blast
      moreover have \<open>finite ?S'\<close>
        using \<open>finite Sa\<close> \<open>finite Sb\<close> by blast
      ultimately have \<open>?S' \<in> C\<close>
        using finc by blast
      then have \<open>?S' \<union> {Neg A} \<in> C \<or> ?S' \<union> {Neg B} \<in> C\<close>
        using altconc unfolding alt_consistency_def by simp
      then have \<open>Sa \<in> C \<or> Sb \<in> C\<close>
        using sc by blast
      then show False
        using \<open>Sa \<notin> C\<close> \<open>Sb \<notin> C\<close> by blast
    qed }

  { fix A B
    assume *: \<open>Impl A B \<in> S\<close>
    show \<open>S \<union> {Neg A} \<in> mk_finite_char C \<or> S \<union> {B} \<in> mk_finite_char C\<close>
    proof (rule ccontr)
      assume \<open>\<not> ?thesis\<close>
      then obtain Sa and Sb
        where \<open>Sa \<subseteq> S \<union> {Neg A}\<close> and \<open>finite Sa\<close> and \<open>Sa \<notin> C\<close>
          and \<open>Sb \<subseteq> S \<union> {B}\<close> and \<open>finite Sb\<close> and \<open>Sb \<notin> C\<close>
        unfolding mk_finite_char_def by blast

      let ?S' = \<open>(Sa - {Neg A}) \<union> (Sb - {B}) \<union> {Impl A B}\<close>

      have \<open>?S' \<subseteq> S\<close>
        using \<open>Sa \<subseteq> S \<union> {Neg A}\<close> \<open>Sb \<subseteq> S \<union> {B}\<close> * by blast
      moreover have \<open>finite ?S'\<close>
        using \<open>finite Sa\<close> \<open>finite Sb\<close> by blast
      ultimately have \<open>?S' \<in> C\<close>
        using finc by blast
      then have \<open>?S' \<union> {Neg A} \<in> C \<or> ?S' \<union> {B} \<in> C\<close>
        using altconc unfolding alt_consistency_def by simp
      then have \<open>Sa \<in> C \<or> Sb \<in> C\<close>
        using sc by blast
      then show False
        using \<open>Sa \<notin> C\<close> \<open>Sb \<notin> C\<close> by blast
    qed }

  { fix P and t :: \<open>'a term\<close>
    assume *: \<open>Forall P \<in> S\<close> and \<open>closedt 0 t\<close>
    show \<open>S \<union> {P[t/0]} \<in> mk_finite_char C\<close>
      unfolding mk_finite_char_def
    proof (intro allI impI CollectI)
      fix S'
      let ?S' = \<open>S' - {P[t/0]} \<union> {Forall P}\<close>

      assume \<open>S' \<subseteq> S \<union> {P[t/0]}\<close> and \<open>finite S'\<close>
      then have \<open>?S' \<subseteq> S\<close>
        using * by blast
      moreover have \<open>finite ?S'\<close>
        using \<open>finite S'\<close> by blast
      ultimately have \<open>?S' \<in> C\<close>
        using finc by blast
      then have \<open>?S' \<union> {P[t/0]} \<in> C\<close>
        using altconc \<open>closedt 0 t\<close> unfolding alt_consistency_def by simp
      then show \<open>S' \<in> C\<close>
        using sc by blast
    qed }

  { fix P and t :: \<open>'a term\<close>
    assume *: \<open>Neg (Exists P) \<in> S\<close> and \<open>closedt 0 t\<close>
    show \<open>S \<union> {Neg (P[t/0])} \<in> mk_finite_char C\<close>
      unfolding mk_finite_char_def
    proof (intro allI impI CollectI)
      fix S'
      let ?S' = \<open>S' - {Neg (P[t/0])} \<union> {Neg (Exists P)}\<close>

      assume \<open>S' \<subseteq> S \<union> {Neg (P[t/0])}\<close> and \<open>finite S'\<close>
      then have \<open>?S' \<subseteq> S\<close>
        using * by blast
      moreover have \<open>finite ?S'\<close>
        using \<open>finite S'\<close> by blast
      ultimately have \<open>?S' \<in> C\<close>
        using finc by blast
      then have \<open>?S' \<union> {Neg (P[t/0])} \<in> C\<close>
        using altconc \<open>closedt 0 t\<close> unfolding alt_consistency_def by simp
      then show \<open>S' \<in> C\<close>
        using sc by blast
    qed }

  { fix P x
    assume *: \<open>Exists P \<in> S\<close> and \<open>\<forall>a \<in> S. x \<notin> params a\<close>
    show \<open>S \<union> {P[App x []/0]} \<in> mk_finite_char C\<close>
      unfolding mk_finite_char_def
    proof (intro allI impI CollectI)
      fix S'
      let ?S' = \<open>S' - {P[App x []/0]} \<union> {Exists P}\<close>

      assume \<open>S' \<subseteq> S \<union> {P[App x []/0]}\<close> and \<open>finite S'\<close>
      then have \<open>?S' \<subseteq> S\<close>
        using * by blast
      moreover have \<open>finite ?S'\<close>
        using \<open>finite S'\<close> by blast
      ultimately have \<open>?S' \<in> C\<close>
        using finc by blast
      moreover have \<open>\<forall>a \<in> ?S'. x \<notin> params a\<close>
        using \<open>\<forall>a \<in> S. x \<notin> params a\<close> \<open>?S' \<subseteq> S\<close> by blast
      ultimately have \<open>?S' \<union> {P[App x []/0]} \<in> C\<close>
        using altconc \<open>\<forall>a \<in> S. x \<notin> params a\<close> unfolding alt_consistency_def by blast
      then show \<open>S' \<in> C\<close>
        using sc by blast
    qed }

  { fix P x
    assume *: \<open>Neg (Forall P) \<in> S\<close> and \<open>\<forall>a \<in> S. x \<notin> params a\<close>
    show \<open>S \<union> {Neg (P[App x []/0])} \<in> mk_finite_char C\<close>
      unfolding mk_finite_char_def
    proof (intro allI impI CollectI)
      fix S'
      let ?S' = \<open>S' - {Neg (P[App x []/0])} \<union> {Neg (Forall P)}\<close>

      assume \<open>S' \<subseteq> S \<union> {Neg (P[App x []/0])}\<close> and \<open>finite S'\<close>
      then have \<open>?S' \<subseteq> S\<close>
        using * by blast
      moreover have \<open>finite ?S'\<close>
        using \<open>finite S'\<close> by blast
      ultimately have \<open>?S' \<in> C\<close>
        using finc by blast
      moreover have \<open>\<forall>a \<in> ?S'. x \<notin> params a\<close>
        using \<open>\<forall>a \<in> S. x \<notin> params a\<close> \<open>?S' \<subseteq> S\<close> by blast
      ultimately have \<open>?S' \<union> {Neg (P[App x []/0])} \<in> C\<close>
        using altconc \<open>\<forall>a \<in> S. x \<notin> params a\<close> unfolding alt_consistency_def by simp
      then show \<open>S' \<in> C\<close>
        using sc by blast
    qed }
qed

theorem finite_char: \<open>finite_char (mk_finite_char C)\<close>
  unfolding finite_char_def mk_finite_char_def by blast

theorem finite_char_closed: \<open>finite_char C \<Longrightarrow> subset_closed C\<close>
  unfolding finite_char_def subset_closed_def
proof (intro ballI allI impI)
  fix S S'
  assume *: \<open>\<forall>S. (S \<in> C) = (\<forall>S'. finite S' \<longrightarrow> S' \<subseteq> S \<longrightarrow> S' \<in> C)\<close>
    and \<open>S' \<in> C\<close> and \<open>S \<subseteq> S'\<close>
  then have \<open>\<forall>S'. finite S' \<longrightarrow> S' \<subseteq> S \<longrightarrow> S' \<in> C\<close> by blast
  then show \<open>S \<in> C\<close> using * by blast
qed

theorem finite_char_subset: \<open>subset_closed C \<Longrightarrow> C \<subseteq> mk_finite_char C\<close>
  unfolding mk_finite_char_def subset_closed_def by blast

subsection \<open>Enumerating datatypes\<close>

text \<open>
\label{sec:enumeration}
As has already been mentioned earlier, the proof of the model existence theorem
relies on the fact that the set of formulae is enumerable. Using the infrastructure
for datatypes, the types @{type term} and @{type form} can automatically be shown to
be a member of the @{class countable} type class:
\<close>

instance \<open>term\<close> :: (countable) countable
  by countable_datatype

instance form :: (countable, countable) countable
  by countable_datatype

subsection \<open>Extension to maximal consistent sets\<close>

text \<open>
\label{sec:extend}
Given a set \<open>C\<close> of finite character, we show that
the least upper bound of a chain of sets that are elements
of \<open>C\<close> is again an element of \<open>C\<close>.
\<close>

definition is_chain :: \<open>(nat \<Rightarrow> 'a set) \<Rightarrow> bool\<close> where
  \<open>is_chain f = (\<forall>n. f n \<subseteq> f (Suc n))\<close>

theorem is_chainD: \<open>is_chain f \<Longrightarrow> x \<in> f m \<Longrightarrow> x \<in> f (m + n)\<close>
  by (induct n) (auto simp: is_chain_def)

theorem is_chainD':
  assumes \<open>is_chain f\<close> and \<open>x \<in> f m\<close> and \<open>m \<le> k\<close>
  shows \<open>x \<in> f k\<close>
proof -
  have \<open>\<exists>n. k = m + n\<close>
    using \<open>m \<le> k\<close> by (simp add: le_iff_add)
  then obtain n where \<open>k = m + n\<close>
    by blast
  then show \<open>x \<in> f k\<close>
    using \<open>is_chain f\<close> \<open>x \<in> f m\<close>
    by (simp add: is_chainD)
qed

theorem chain_index:
  assumes ch: \<open>is_chain f\<close> and fin: \<open>finite F\<close>
  shows \<open>F \<subseteq> (\<Union>n. f n) \<Longrightarrow> \<exists>n. F \<subseteq> f n\<close>
  using fin
proof (induct rule: finite_induct)
  case empty
  then show ?case by blast
next
  case (insert x F)
  then have \<open>\<exists>n. F \<subseteq> f n\<close> and \<open>\<exists>m. x \<in> f m\<close> and \<open>F \<subseteq> (\<Union>x. f x)\<close>
    using ch by simp_all
  then obtain n and m where \<open>F \<subseteq> f n\<close> and \<open>x \<in> f m\<close>
    by blast
  have \<open>m \<le> max n m\<close> and \<open>n \<le> max n m\<close>
    by simp_all
  have \<open>x \<in> f (max n m)\<close>
    using is_chainD' ch \<open>x \<in> f m\<close> \<open>m \<le> max n m\<close> by fast
  moreover have \<open>F \<subseteq> f (max n m)\<close>
    using is_chainD' ch \<open>F \<subseteq> f n\<close> \<open>n \<le> max n m\<close> by fast
  moreover have \<open>x \<in> f (max n m) \<and> F \<subseteq> f (max n m)\<close>
    using calculation by blast
  ultimately show ?case by blast
qed

lemma chain_union_closed':
  assumes \<open>is_chain f\<close> and \<open>(\<forall>n. f n \<in> C)\<close> and \<open>\<forall>S' \<in> C. \<forall>S \<subseteq> S'. S \<in> C\<close>
    and \<open>finite S'\<close> and \<open>S' \<subseteq> (\<Union>n. f n)\<close>
  shows \<open>S' \<in> C\<close>
proof -
  note \<open>finite S'\<close> and \<open>S' \<subseteq> (\<Union>n. f n)\<close>
  then obtain n where \<open>S' \<subseteq> f n\<close>
    using chain_index \<open>is_chain f\<close> by blast
  moreover have \<open>f n \<in> C\<close>
    using \<open>\<forall>n. f n \<in> C\<close> by blast
  ultimately show \<open>S' \<in> C\<close>
    using \<open>\<forall>S' \<in> C. \<forall>S \<subseteq> S'. S \<in> C\<close> by blast
qed

theorem chain_union_closed:
  assumes \<open>finite_char C\<close> and \<open>is_chain f\<close> and \<open>\<forall>n. f n \<in> C\<close>
  shows \<open>(\<Union>n. f n) \<in> C\<close>
proof -
  have \<open>subset_closed C\<close>
    using finite_char_closed \<open>finite_char C\<close> by blast
  then have \<open>\<forall>S' \<in> C. \<forall>S \<subseteq> S'. S \<in> C\<close>
    using subset_closed_def by blast
  then have \<open>\<forall>S'. finite S' \<longrightarrow> S' \<subseteq> (\<Union>n. f n) \<longrightarrow> S' \<in> C\<close>
    using chain_union_closed' assms by blast
  moreover have \<open>((\<Union>n. f n) \<in> C) = (\<forall>S'. finite S' \<longrightarrow> S' \<subseteq> (\<Union>n. f n) \<longrightarrow> S' \<in> C)\<close>
    using \<open>finite_char C\<close> unfolding finite_char_def by blast
  ultimately show ?thesis by blast
qed

text \<open>
We can now define a function \<open>Extend\<close> that extends a consistent
set to a maximal consistent set. To this end, we first define an auxiliary
function \<open>extend\<close> that produces the elements of an ascending chain of
consistent sets.
\<close>

primrec (nonexhaustive) dest_Neg :: \<open>('a, 'b) form \<Rightarrow> ('a, 'b) form\<close> where
  \<open>dest_Neg (Neg p) = p\<close>

primrec (nonexhaustive) dest_Forall :: \<open>('a, 'b) form \<Rightarrow> ('a, 'b) form\<close> where
  \<open>dest_Forall (Forall p) = p\<close>

primrec (nonexhaustive) dest_Exists :: \<open>('a, 'b) form \<Rightarrow> ('a, 'b) form\<close> where
  \<open>dest_Exists (Exists p) = p\<close>

primrec extend :: \<open>(nat, 'b) form set \<Rightarrow> (nat, 'b) form set set \<Rightarrow>
    (nat \<Rightarrow> (nat, 'b) form) \<Rightarrow> nat \<Rightarrow> (nat, 'b) form set\<close> where
  \<open>extend S C f 0 = S\<close>
| \<open>extend S C f (Suc n) = (if extend S C f n \<union> {f n} \<in> C
     then
       (if (\<exists>p. f n = Exists p)
        then extend S C f n \<union> {f n} \<union> {subst (dest_Exists (f n))
          (App (SOME k. k \<notin> (\<Union>p \<in> extend S C f n \<union> {f n}. params p)) []) 0}
        else if (\<exists>p. f n = Neg (Forall p))
        then extend S C f n \<union> {f n} \<union> {Neg (subst (dest_Forall (dest_Neg (f n)))
          (App (SOME k. k \<notin> (\<Union>p \<in> extend S C f n \<union> {f n}. params p)) []) 0)}
        else extend S C f n \<union> {f n})
     else extend S C f n)\<close>

definition Extend :: \<open>(nat, 'b) form set \<Rightarrow> (nat, 'b) form set set \<Rightarrow>
    (nat \<Rightarrow> (nat, 'b) form) \<Rightarrow> (nat, 'b) form set\<close> where
  \<open>Extend S C f = (\<Union>n. extend S C f n)\<close>

theorem is_chain_extend: \<open>is_chain (extend S C f)\<close>
  by (simp add: is_chain_def) blast

theorem finite_paramst [simp]: \<open>finite (paramst (t :: 'a term))\<close>
  \<open>finite (paramsts (ts :: 'a term list))\<close>
  by (induct t and ts rule: paramst.induct paramsts.induct) (simp_all split: sum.split)

theorem finite_params [simp]: \<open>finite (params p)\<close>
  by (induct p) simp_all

theorem finite_params_extend [simp]:
  \<open>infinite (\<Inter>p \<in> S. - params p) \<Longrightarrow> infinite (\<Inter>p \<in> extend S C f n. - params p)\<close>
  by (induct n) simp_all

lemma infinite_params_available:
  assumes \<open>infinite (- (\<Union>p \<in> S. params p))\<close>
  shows \<open>\<exists>x. x \<notin> (\<Union>p \<in> extend S C f n \<union> {f n}. params p)\<close>
proof -
  let ?S' = \<open>extend S C f n \<union> {f n}\<close>

  have \<open>infinite (- (\<Union>x \<in> ?S'. params x))\<close>
    using assms by simp
  then obtain x where \<open>x \<in> - (\<Union>x \<in> ?S'. params x)\<close>
    using infinite_imp_nonempty by blast
  then have \<open>\<forall>a \<in> ?S'. x \<notin> params a\<close>
    by blast
  then show ?thesis
    by blast
qed

lemma extend_in_C_Exists:
  assumes \<open>alt_consistency C\<close>
    and \<open>infinite (- (\<Union>p \<in> S. params p))\<close>
    and \<open>extend S C f n \<union> {f n} \<in> C\<close> (is \<open>?S' \<in> C\<close>)
    and \<open>\<exists>p. f n = Exists p\<close>
  shows \<open>extend S C f (Suc n) \<in> C\<close>
proof -
  obtain p where *: \<open>f n = Exists p\<close>
    using \<open>\<exists>p. f n = Exists p\<close> by blast
  have \<open>\<exists>x. x \<notin> (\<Union>p \<in> ?S'. params p)\<close>
    using \<open>infinite (- (\<Union>p \<in> S. params p))\<close> infinite_params_available
    by blast
  moreover have \<open>Exists p \<in> ?S'\<close>
    using * by simp
  then have \<open>\<forall>x. x \<notin> (\<Union>p \<in> ?S'. params p) \<longrightarrow> ?S' \<union> {p[App x []/0]} \<in> C\<close>
    using \<open>?S' \<in> C\<close> \<open>alt_consistency C\<close>
    unfolding alt_consistency_def by simp
  ultimately have \<open>(?S' \<union> {p[App (SOME k. k \<notin> (\<Union>p \<in> ?S'. params p)) []/0]}) \<in> C\<close>
    by (metis (mono_tags, lifting) someI2)
  then show ?thesis
    using assms * by simp
qed

lemma extend_in_C_Neg_Forall:
  assumes \<open>alt_consistency C\<close>
    and \<open>infinite (- (\<Union>p \<in> S. params p))\<close>
    and \<open>extend S C f n \<union> {f n} \<in> C\<close> (is \<open>?S' \<in> C\<close>)
    and \<open>\<forall>p. f n \<noteq> Exists p\<close>
    and \<open>\<exists>p. f n = Neg (Forall p)\<close>
  shows \<open>extend S C f (Suc n) \<in> C\<close>
proof -
  obtain p where *: \<open>f n = Neg (Forall p)\<close>
    using \<open>\<exists>p. f n = Neg (Forall p)\<close> by blast
  have \<open>\<exists>x. x \<notin> (\<Union>p \<in> ?S'. params p)\<close>
    using \<open>infinite (- (\<Union>p \<in> S. params p))\<close> infinite_params_available
    by blast
  moreover have \<open>Neg (Forall p) \<in> ?S'\<close>
    using * by simp
  then have \<open>\<forall>x. x \<notin> (\<Union>p \<in> ?S'. params p) \<longrightarrow> ?S' \<union> {Neg (p[App x []/0])} \<in> C\<close>
    using \<open>?S' \<in> C\<close> \<open>alt_consistency C\<close>
    unfolding alt_consistency_def by simp
  ultimately have \<open>(?S' \<union> {Neg (p[App (SOME k. k \<notin> (\<Union>p \<in> ?S'. params p)) []/0])}) \<in> C\<close>
    by (metis (mono_tags, lifting) someI2)
  then show ?thesis
    using assms * by simp
qed

lemma extend_in_C_no_delta:
  assumes \<open>extend S C f n \<union> {f n} \<in> C\<close>
    and \<open>\<forall>p. f n \<noteq> Exists p\<close>
    and \<open>\<forall>p. f n \<noteq> Neg (Forall p)\<close>
  shows \<open>extend S C f (Suc n) \<in> C\<close>
  using assms by simp

lemma extend_in_C_stop:
  assumes \<open>extend S C f n \<in> C\<close>
    and \<open>extend S C f n \<union> {f n} \<notin> C\<close>
  shows \<open>extend S C f (Suc n) \<in> C\<close>
  using assms by simp

theorem extend_in_C: \<open>alt_consistency C \<Longrightarrow>
  S \<in> C \<Longrightarrow> infinite (- (\<Union>p \<in> S. params p)) \<Longrightarrow> extend S C f n \<in> C\<close>
proof (induct n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then show ?case
    using extend_in_C_Exists extend_in_C_Neg_Forall
      extend_in_C_no_delta extend_in_C_stop
    by metis
qed

text \<open>
The main theorem about \<open>Extend\<close> says that if \<open>C\<close> is an
alternative consistency property that is of finite character,
\<open>S\<close> is consistent and \<open>S\<close> uses only finitely many
parameters, then \<open>Extend S C f\<close> is again consistent.
\<close>

theorem Extend_in_C: \<open>alt_consistency C \<Longrightarrow> finite_char C \<Longrightarrow>
  S \<in> C \<Longrightarrow> infinite (- (\<Union>p \<in> S. params p)) \<Longrightarrow> Extend S C f \<in> C\<close>
  unfolding Extend_def
  using chain_union_closed is_chain_extend extend_in_C
  by blast

theorem Extend_subset: \<open>S \<subseteq> Extend S C f\<close>
proof
  fix x
  assume \<open>x \<in> S\<close>
  then have \<open>x \<in> extend S C f 0\<close> by simp
  then have \<open>\<exists>n. x \<in> extend S C f n\<close> by blast
  then show \<open>x \<in> Extend S C f\<close> by (simp add: Extend_def)
qed

text \<open>
The \<open>Extend\<close> function yields a maximal set:
\<close>

definition maximal :: \<open>'a set \<Rightarrow> 'a set set \<Rightarrow> bool\<close> where
  \<open>maximal S C = (\<forall>S' \<in> C. S \<subseteq> S' \<longrightarrow> S = S')\<close>

theorem extend_maximal:
  assumes \<open>\<forall>y. \<exists>n. y = f n\<close>
    and \<open>finite_char C\<close>
  shows \<open>maximal (Extend S C f) C\<close>
  unfolding maximal_def Extend_def
proof (intro ballI impI)
  fix S'
  assume \<open>S' \<in> C\<close>
    and \<open>(\<Union>x. extend S C f x) \<subseteq> S'\<close>
  moreover have \<open>S' \<subseteq> (\<Union>x. extend S C f x)\<close>
  proof (rule ccontr)
    assume \<open>\<not> S' \<subseteq> (\<Union>x. extend S C f x)\<close>
    then have \<open>\<exists>z. z \<in> S' \<and> z \<notin> (\<Union>x. extend S C f x)\<close>
      by blast
    then obtain z where \<open>z \<in> S'\<close> and *: \<open>z \<notin> (\<Union>x. extend S C f x)\<close>
      by blast
    then obtain n where \<open>z = f n\<close>
      using \<open>\<forall>y. \<exists>n. y = f n\<close> by blast

    from \<open>(\<Union>x. extend S C f x) \<subseteq> S'\<close> \<open>z = f n\<close> \<open>z \<in> S'\<close>
    have \<open>extend S C f n \<union> {f n} \<subseteq> S'\<close> by blast

    from \<open>finite_char C\<close>
    have \<open>subset_closed C\<close> using finite_char_closed by blast
    then have \<open>\<forall>S' \<in> C. \<forall>S \<subseteq> S'. S \<in> C\<close>
      unfolding subset_closed_def by simp
    then have \<open>\<forall>S \<subseteq> S'. S \<in> C\<close>
      using \<open>S' \<in> C\<close> by blast
    then have \<open>extend S C f n \<union> {f n} \<in> C\<close>
      using \<open>extend S C f n \<union> {f n} \<subseteq> S'\<close>
      by blast
    then have \<open>z \<in> extend S C f (Suc n)\<close>
      using \<open>z \<notin> (\<Union>x. extend S C f x)\<close> \<open>z = f n\<close>
      by simp
    then show False using * by blast
  qed
  ultimately show \<open>(\<Union>x. extend S C f x) = S'\<close>
    by simp
qed

subsection \<open>Hintikka sets and Herbrand models\<close>

text \<open>
\label{sec:hintikka}
A Hintikka set is defined as follows:
\<close>

definition hintikka :: \<open>('a, 'b) form set \<Rightarrow> bool\<close> where
  \<open>hintikka H =
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
     (\<forall>P. Neg (Forall P) \<in> H \<longrightarrow> (\<exists>t. closedt 0 t \<and> Neg (subst P t 0) \<in> H)))\<close>

text \<open>
In Herbrand models, each {\em closed} term is interpreted by itself.
We introduce a new datatype \<open>hterm\<close> (``Herbrand terms''), which
is similar to the datatype \<open>term\<close> introduced in \secref{sec:terms},
but without variables. We also define functions for converting between
closed terms and Herbrand terms.
\<close>

datatype 'a hterm = HApp 'a \<open>'a hterm list\<close>

primrec
  term_of_hterm :: \<open>'a hterm \<Rightarrow> 'a term\<close> and
  terms_of_hterms :: \<open>'a hterm list \<Rightarrow> 'a term list\<close> where
  \<open>term_of_hterm (HApp a hts) = App a (terms_of_hterms hts)\<close>
| \<open>terms_of_hterms [] = []\<close>
| \<open>terms_of_hterms (ht # hts) = term_of_hterm ht # terms_of_hterms hts\<close>

theorem herbrand_evalt [simp]:
  \<open>closedt 0 t \<Longrightarrow> term_of_hterm (evalt e HApp t) = t\<close>
  \<open>closedts 0 ts \<Longrightarrow> terms_of_hterms (evalts e HApp ts) = ts\<close>
  by (induct t and ts rule: closedt.induct closedts.induct) simp_all

theorem herbrand_evalt' [simp]:
  \<open>evalt e HApp (term_of_hterm ht) = ht\<close>
  \<open>evalts e HApp (terms_of_hterms hts) = hts\<close>
  by (induct ht and hts rule: term_of_hterm.induct terms_of_hterms.induct) simp_all

theorem closed_hterm [simp]:
  \<open>closedt 0 (term_of_hterm (ht::'a hterm))\<close>
  \<open>closedts 0 (terms_of_hterms (hts::'a hterm list))\<close>
  by (induct ht and hts rule: term_of_hterm.induct terms_of_hterms.induct) simp_all

text \<open>
We can prove that Hintikka sets are satisfiable in Herbrand models.
Note that this theorem cannot be proved by a simple structural induction
(as claimed in Fitting's book), since a parameter substitution has
to be applied in the cases for quantifiers. However, since parameter
substitution does not change the size of formulae, the theorem can
be proved by well-founded induction on the size of the formula \<open>p\<close>.
\<close>

theorem hintikka_model:
  assumes hin: \<open>hintikka H\<close>
  shows \<open>(p \<in> H \<longrightarrow> closed 0 p \<longrightarrow>
    eval e HApp (\<lambda>a ts. Pred a (terms_of_hterms ts) \<in> H) p) \<and>
  (Neg p \<in> H \<longrightarrow> closed 0 p \<longrightarrow>
    eval e HApp (\<lambda>a ts. Pred a (terms_of_hterms ts) \<in> H) (Neg p))\<close>
proof (induct p rule: wf_induct [where r=\<open>measure size_form\<close>])
  show \<open>wf (measure size_form)\<close>
    by blast
next
  let ?eval = \<open>eval e HApp (\<lambda>a ts. Pred a (terms_of_hterms ts) \<in> H)\<close>

  fix x
  assume wf: \<open>\<forall>y. (y, x) \<in> measure size_form \<longrightarrow>
                  (y \<in> H \<longrightarrow> closed 0 y \<longrightarrow> ?eval y) \<and>
              (Neg y \<in> H \<longrightarrow> closed 0 y \<longrightarrow> ?eval (Neg y))\<close>

  show \<open>(x \<in> H \<longrightarrow> closed 0 x \<longrightarrow> ?eval x) \<and> (Neg x \<in> H \<longrightarrow> closed 0 x \<longrightarrow> ?eval (Neg x))\<close>
  proof (cases x)
    case FF
    show ?thesis
    proof (intro conjI impI)
      assume \<open>x \<in> H\<close>
      then show \<open>?eval x\<close>
        using FF hin by (simp add: hintikka_def)
    next
      assume \<open>Neg x \<in> H\<close>
      then show \<open>?eval (Neg x)\<close> using FF by simp
    qed
  next
    case TT
    show ?thesis
    proof (intro conjI impI)
      assume \<open>x \<in> H\<close>
      then show \<open>?eval x\<close>
        using TT by simp
    next
      assume \<open>Neg x \<in> H\<close>
      then show \<open>?eval (Neg x)\<close>
        using TT hin by (simp add: hintikka_def)
    qed
  next
    case (Pred p ts)
    show ?thesis
    proof (intro conjI impI)
      assume \<open>x \<in> H\<close> and \<open>closed 0 x\<close>
      then show \<open>?eval x\<close> using Pred by simp
    next
      assume \<open>Neg x \<in> H\<close> and \<open>closed 0 x\<close>
      then have \<open>Neg (Pred p ts) \<in> H\<close>
        using Pred by simp
      then have \<open>Pred p ts \<notin> H\<close>
        using hin unfolding hintikka_def by fast
      then show \<open>?eval (Neg x)\<close>
        using Pred \<open>closed 0 x\<close> by simp
    qed
  next
    case (Neg Z)
    then show ?thesis
    proof (intro conjI impI)
      assume \<open>x \<in> H\<close> and \<open>closed 0 x\<close>
      then show \<open>?eval x\<close>
        using Neg wf by simp
    next
      assume \<open>Neg x \<in> H\<close>
      then have \<open>Z \<in> H\<close>
        using Neg hin unfolding hintikka_def by blast
      moreover assume \<open>closed 0 x\<close>
      then have \<open>closed 0 Z\<close>
        using Neg by simp
      ultimately have \<open>?eval Z\<close>
        using Neg wf by simp
      then show \<open>?eval (Neg x)\<close>
        using Neg by simp
    qed
  next
    case (And A B)
    then show ?thesis
    proof (intro conjI impI)
      assume \<open>x \<in> H\<close> and \<open>closed 0 x\<close>
      then have \<open>And A B \<in> H\<close> and \<open>closed 0 (And A B)\<close>
        using And by simp_all
      then have \<open>A \<in> H \<and> B \<in> H\<close>
        using And hin unfolding hintikka_def by blast
      then show \<open>?eval x\<close>
        using And wf \<open>closed 0 (And A B)\<close> by simp
    next
      assume \<open>Neg x \<in> H\<close> and \<open>closed 0 x\<close>
      then have \<open>Neg (And A B) \<in> H\<close> and \<open>closed 0 (And A B)\<close>
        using And by simp_all
      then have \<open>Neg A \<in> H \<or> Neg B \<in> H\<close>
        using hin unfolding hintikka_def by blast
      then show \<open>?eval (Neg x)\<close>
        using And wf \<open>closed 0 (And A B)\<close> by fastforce
    qed
  next
    case (Or A B)
    then show ?thesis
    proof (intro conjI impI)
      assume \<open>x \<in> H\<close> and \<open>closed 0 x\<close>
      then have \<open>Or A B \<in> H\<close> and \<open>closed 0 (Or A B)\<close>
        using Or by simp_all
      then have \<open>A \<in> H \<or> B \<in> H\<close>
        using hin unfolding hintikka_def by blast
      then show \<open>?eval x\<close>
        using Or wf \<open>closed 0 (Or A B)\<close> by fastforce
    next
      assume \<open>Neg x \<in> H\<close> and \<open>closed 0 x\<close>
      then have \<open>Neg (Or A B) \<in> H\<close> and \<open>closed 0 (Or A B)\<close>
        using Or by simp_all
      then have \<open>Neg A \<in> H \<and> Neg B \<in> H\<close>
        using hin unfolding hintikka_def by blast
      then show \<open>?eval (Neg x)\<close>
        using Or wf \<open>closed 0 (Or A B)\<close> by simp
    qed
  next
    case (Impl A B)
    then show ?thesis
    proof (intro conjI impI)
      assume \<open>x \<in> H\<close> and \<open>closed 0 x\<close>
      then have \<open>Impl A B \<in> H\<close> and \<open>closed 0 (Impl A B)\<close>
        using Impl by simp_all
      then have \<open>Neg A \<in> H \<or> B \<in> H\<close>
        using hin unfolding hintikka_def by blast
      then show \<open>?eval x\<close>
        using Impl wf \<open>closed 0 (Impl A B)\<close> by fastforce
    next
      assume \<open>Neg x \<in> H\<close> and \<open>closed 0 x\<close>
      then have \<open>Neg (Impl A B) \<in> H\<close> and \<open>closed 0 (Impl A B)\<close>
        using Impl by simp_all
      then have \<open>A \<in> H \<and> Neg B \<in> H\<close>
        using hin unfolding hintikka_def by blast
      then show \<open>?eval (Neg x)\<close>
        using Impl wf \<open>closed 0 (Impl A B)\<close> by simp
    qed
  next
    case (Forall P)
    then show ?thesis
    proof (intro conjI impI)
      assume \<open>x \<in> H\<close> and \<open>closed 0 x\<close>
      have \<open>\<forall>z. eval (e\<langle>0:z\<rangle>) HApp (\<lambda>a ts. Pred a (terms_of_hterms ts) \<in> H) P\<close>
      proof (rule allI)
        fix z
        from \<open>x \<in> H\<close> and \<open>closed 0 x\<close>
        have \<open>Forall P \<in> H\<close> and \<open>closed 0 (Forall P)\<close>
          using Forall by simp_all
        then have *: \<open>\<forall>P t. closedt 0 t \<longrightarrow> Forall P \<in> H \<longrightarrow> P[t/0] \<in> H\<close>
          using hin unfolding hintikka_def by blast
        from \<open>closed 0 (Forall P)\<close>
        have \<open>closed (Suc 0) P\<close> by simp

        have \<open>(P[term_of_hterm z/0], Forall P) \<in> measure size_form \<longrightarrow>
              (P[term_of_hterm z/0] \<in> H \<longrightarrow> closed 0 (P[term_of_hterm z/0]) \<longrightarrow>
              ?eval (P[term_of_hterm z/0]))\<close>
          using Forall wf by blast
        then show \<open>eval (e\<langle>0:z\<rangle>) HApp (\<lambda>a ts. Pred a (terms_of_hterms ts) \<in> H) P\<close>
          using * \<open>Forall P \<in> H\<close> \<open>closed (Suc 0) P\<close> by simp
      qed
      then show \<open>?eval x\<close>
        using Forall by simp
    next
      assume \<open>Neg x \<in> H\<close> and \<open>closed 0 x\<close>
      then have \<open>Neg (Forall P) \<in> H\<close>
        using Forall by simp
      then have \<open>\<exists>t. closedt 0 t \<and> Neg (P[t/0]) \<in> H\<close>
        using Forall hin unfolding hintikka_def by blast
      then obtain t where *: \<open>closedt 0 t \<and> Neg (P[t/0]) \<in> H\<close>
        by blast
      then have \<open>closed 0 (P[t/0])\<close>
        using Forall \<open>closed 0 x\<close> by simp

      have \<open>(subst P t 0, Forall P) \<in> measure size_form \<longrightarrow>
              (Neg (subst P t 0) \<in> H \<longrightarrow> closed 0 (subst P t 0) \<longrightarrow>
              ?eval (Neg (subst P t 0)))\<close>
        using Forall wf by blast
      then have \<open>?eval (Neg (P[t/0]))\<close>
        using Forall * \<open>closed 0 (P[t/0])\<close> by simp
      then have \<open>\<exists>z. \<not> eval (e\<langle>0:z\<rangle>) HApp (\<lambda>a ts. Pred a (terms_of_hterms ts) \<in> H) P\<close>
        by auto
      then show \<open>?eval (Neg x)\<close>
        using Forall by simp
    qed
  next
    case (Exists P)
    then show ?thesis
    proof (intro conjI impI allI)
      assume \<open>x \<in> H\<close> and \<open>closed 0 x\<close>
      then have \<open>\<exists>t. closedt 0 t \<and> (P[t/0]) \<in> H\<close>
        using Exists hin unfolding hintikka_def by blast
      then obtain t where *: \<open>closedt 0 t \<and> (P[t/0]) \<in> H\<close>
        by blast
      then have \<open>closed 0 (P[t/0])\<close>
        using Exists \<open>closed 0 x\<close> by simp

      have \<open>(subst P t 0, Exists P) \<in> measure size_form \<longrightarrow>
              ((subst P t 0) \<in> H \<longrightarrow> closed 0 (subst P t 0) \<longrightarrow>
              ?eval (subst P t 0))\<close>
        using Exists wf by blast
      then have \<open>?eval (P[t/0])\<close>
        using Exists * \<open>closed 0 (P[t/0])\<close> by simp
      then have \<open>\<exists>z. eval (e\<langle>0:z\<rangle>) HApp (\<lambda>a ts. Pred a (terms_of_hterms ts) \<in> H) P\<close>
        by auto
      then show \<open>?eval x\<close>
        using Exists by simp
    next
      assume \<open>Neg x \<in> H\<close> and \<open>closed 0 x\<close>
      have \<open>\<forall>z. \<not> eval (e\<langle>0:z\<rangle>) HApp (\<lambda>a ts. Pred a (terms_of_hterms ts) \<in> H) P\<close>
      proof (rule allI)
        fix z
        from \<open>Neg x \<in> H\<close> and \<open>closed 0 x\<close>
        have \<open>Neg (Exists P) \<in> H\<close> and \<open>closed 0 (Neg (Exists P))\<close>
          using Exists by simp_all
        then have *: \<open>\<forall>P t. closedt 0 t \<longrightarrow> Neg (Exists P) \<in> H \<longrightarrow> Neg (P[t/0]) \<in> H\<close>
          using hin unfolding hintikka_def by blast
        from \<open>closed 0 (Neg (Exists P))\<close>
        have \<open>closed (Suc 0) P\<close> by simp

        have \<open>(P[term_of_hterm z/0], Exists P) \<in> measure size_form \<longrightarrow>
              (Neg (P[term_of_hterm z/0]) \<in> H \<longrightarrow> closed 0 (P[term_of_hterm z/0]) \<longrightarrow>
              ?eval (Neg (P[term_of_hterm z/0])))\<close>
          using Exists wf by blast
        then show \<open>\<not> eval (e\<langle>0:z\<rangle>) HApp (\<lambda>a ts. Pred a (terms_of_hterms ts) \<in> H) P\<close>
          using * \<open>Neg (Exists P) \<in> H\<close> \<open>closed (Suc 0) P\<close> by simp
      qed
      then show \<open>?eval (Neg x)\<close>
        using Exists by simp
    qed
  qed
qed

text \<open>
Using the maximality of @{term \<open>Extend S C f\<close>}, we can show
that @{term \<open>Extend S C f\<close>} yields Hintikka sets:
\<close>

lemma Exists_in_extend:
  assumes \<open>extend S C f n \<union> {f n} \<in> C\<close> (is \<open>?S' \<in> C\<close>)
    and \<open>Exists P = f n\<close>
  shows \<open>P[(App (SOME k. k \<notin> (\<Union>p \<in> extend S C f n \<union> {f n}. params p)) [])/0] \<in>
          extend S C f (Suc n)\<close>
    (is \<open>subst P ?t 0 \<in> extend S C f (Suc n)\<close>)
proof -
  have \<open>\<exists>p. f n = Exists p\<close>
    using \<open>Exists P = f n\<close> by metis
  then have \<open>extend S C f (Suc n) = (?S' \<union> {(dest_Exists (f n))[?t/0]})\<close>
    using \<open>?S' \<in> C\<close> by simp
  also have \<open>\<dots> = (?S' \<union> {(dest_Exists (Exists P))[?t/0]})\<close>
    using \<open>Exists P = f n\<close> by simp
  also have \<open>\<dots> = (?S' \<union> {P[?t/0]})\<close>
    by simp
  finally show ?thesis
    by blast
qed

lemma Neg_Forall_in_extend:
  assumes \<open>extend S C f n \<union> {f n} \<in> C\<close> (is \<open>?S' \<in> C\<close>)
    and \<open>Neg (Forall P) = f n\<close>
  shows \<open>Neg (P[(App (SOME k. k \<notin> (\<Union>p \<in> extend S C f n \<union> {f n}. params p)) [])/0])  \<in>
          extend S C f (Suc n)\<close>
    (is \<open>Neg (subst P ?t 0) \<in> extend S C f (Suc n)\<close>)
proof -
  have \<open>f n \<noteq> Exists P\<close>
    using \<open>Neg (Forall P) = f n\<close> by auto

  have \<open>\<exists>p. f n = Neg (Forall p)\<close>
    using \<open>Neg (Forall P) = f n\<close> by metis
  then have \<open>extend S C f (Suc n) = (?S' \<union> {Neg (dest_Forall (dest_Neg (f n))[?t/0])})\<close>
    using \<open>?S' \<in> C\<close> \<open>f n \<noteq> Exists P\<close> by auto
  also have \<open>\<dots> = (?S' \<union> {Neg (dest_Forall (dest_Neg (Neg (Forall P)))[?t/0])})\<close>
    using \<open>Neg (Forall P) = f n\<close> by simp
  also have \<open>\<dots> = (?S' \<union> {Neg (P[?t/0])})\<close>
    by simp
  finally show ?thesis
    by blast
qed

theorem extend_hintikka:
  assumes fin_ch: \<open>finite_char C\<close>
    and infin_p: \<open>infinite (- (\<Union>p \<in> S. params p))\<close>
    and surj: \<open>\<forall>y. \<exists>n. y = f n\<close>
    and altc: \<open>alt_consistency C\<close>
    and \<open>S \<in> C\<close>
  shows \<open>hintikka (Extend S C f)\<close> (is \<open>hintikka ?H\<close>)
  unfolding hintikka_def
proof (intro allI impI conjI)
  have \<open>maximal ?H C\<close>
    by (simp add: extend_maximal fin_ch surj)

  have \<open>?H \<in> C\<close>
    using Extend_in_C assms by blast

  have \<open>\<forall>S' \<in> C. ?H \<subseteq> S' \<longrightarrow> ?H = S'\<close>
    using \<open>maximal ?H C\<close>
    unfolding maximal_def by blast

  { fix p ts
    show \<open>\<not> (Pred p ts \<in> ?H \<and> Neg (Pred p ts) \<in> ?H)\<close>
      using \<open>?H \<in> C\<close> altc unfolding alt_consistency_def by fast }

  show \<open>FF \<notin> ?H\<close>
    using \<open>?H \<in> C\<close> altc unfolding alt_consistency_def by blast

  show \<open>Neg TT \<notin> ?H\<close>
    using \<open>?H \<in> C\<close> altc unfolding alt_consistency_def by blast

  { fix Z
    assume \<open>Neg (Neg Z) \<in> ?H\<close>
    then have \<open>?H \<union> {Z} \<in> C\<close>
      using \<open>?H \<in> C\<close> altc unfolding alt_consistency_def by fast
    then show \<open>Z \<in> ?H\<close>
      using \<open>maximal ?H C\<close> unfolding maximal_def by fast }

  { fix A B
    assume \<open>And A B \<in> ?H\<close>
    then have \<open>?H \<union> {A, B} \<in> C\<close>
      using \<open>?H \<in> C\<close> altc unfolding alt_consistency_def by fast
    then show \<open>A \<in> ?H\<close> and \<open>B \<in> ?H\<close>
      using \<open>maximal ?H C\<close> unfolding maximal_def by fast+ }

  { fix A B
    assume \<open>Neg (Or A B) \<in> ?H\<close>
    then have \<open>?H \<union> {Neg A, Neg B} \<in> C\<close>
      using \<open>?H \<in> C\<close> altc unfolding alt_consistency_def by fast
    then show \<open>Neg A \<in> ?H\<close> and \<open>Neg B \<in> ?H\<close>
      using \<open>maximal ?H C\<close> unfolding maximal_def by fast+ }

  { fix A B
    assume \<open>Neg (Impl A B) \<in> ?H\<close>
    then have \<open>?H \<union> {A, Neg B} \<in> C\<close>
      using \<open>?H \<in> C\<close> altc unfolding alt_consistency_def by blast
    then show \<open>A \<in> ?H\<close> and \<open>Neg B \<in> ?H\<close>
      using \<open>maximal ?H C\<close> unfolding maximal_def by fast+ }

  { fix A B
    assume \<open>Or A B \<in> ?H\<close>
    then have \<open>?H \<union> {A} \<in> C \<or> ?H \<union> {B} \<in> C\<close>
      using \<open>?H \<in> C\<close> altc unfolding alt_consistency_def by fast
    then show \<open>A \<in> ?H \<or> B \<in> ?H\<close>
      using \<open>maximal ?H C\<close> unfolding maximal_def by fast }

  { fix A B
    assume \<open>Neg (And A B) \<in> ?H\<close>
    then have \<open>?H \<union> {Neg A} \<in> C \<or> ?H \<union> {Neg B} \<in> C\<close>
      using \<open>?H \<in> C\<close> altc unfolding alt_consistency_def by simp
    then show \<open>Neg A \<in> ?H \<or> Neg B \<in> ?H\<close>
      using \<open>maximal ?H C\<close> unfolding maximal_def by fast }

  { fix A B
    assume \<open>Impl A B \<in> ?H\<close>
    then have \<open>?H \<union> {Neg A} \<in> C \<or> ?H \<union> {B} \<in> C\<close>
      using \<open>?H \<in> C\<close> altc unfolding alt_consistency_def by simp
    then show \<open>Neg A \<in> ?H \<or> B \<in> ?H\<close>
      using \<open>maximal ?H C\<close> unfolding maximal_def by fast }

  { fix P and t :: \<open>nat term\<close>
    assume \<open>Forall P \<in> ?H\<close> and \<open>closedt 0 t\<close>
    then have \<open>?H \<union> {P[t/0]} \<in> C\<close>
      using \<open>?H \<in> C\<close> altc unfolding alt_consistency_def by blast
    then show \<open>P[t/0] \<in> ?H\<close>
      using \<open>maximal ?H C\<close> unfolding maximal_def by fast }

  { fix P and t :: \<open>nat term\<close>
    assume \<open>Neg (Exists P) \<in> ?H\<close> and \<open>closedt 0 t\<close>
    then have \<open>?H \<union> {Neg (P[t/0])} \<in> C\<close>
      using \<open>?H \<in> C\<close> altc unfolding alt_consistency_def by blast
    then show \<open>Neg (P[t/0]) \<in> ?H\<close>
      using \<open>maximal ?H C\<close> unfolding maximal_def by fast }

  { fix P
    assume \<open>Exists P \<in> ?H\<close>
    obtain n where *: \<open>Exists P = f n\<close>
      using surj by blast

    let ?t = \<open>App (SOME k. k \<notin> (\<Union>p \<in> extend S C f n \<union> {f n}. params p)) []\<close>
    have \<open>closedt 0 ?t\<close> by simp

    have \<open>Exists P \<in> (\<Union>n. extend S C f n)\<close>
      using \<open>Exists P \<in> ?H\<close> Extend_def by blast
    then have \<open>extend S C f n \<union> {f n} \<subseteq> (\<Union>n. extend S C f n)\<close>
      using * by (simp add: UN_upper)
    then have \<open>extend S C f n \<union> {f n} \<in> C\<close>
      using Extend_def \<open>Extend S C f \<in> C\<close> fin_ch finite_char_closed
      unfolding subset_closed_def by metis
    then have \<open>P[?t/0] \<in> extend S C f (Suc n)\<close>
      using * Exists_in_extend by blast
    then have \<open>P[?t/0] \<in> ?H\<close>
      using Extend_def by blast
    then show \<open>\<exists>t. closedt 0 t \<and> P[t/0] \<in> ?H\<close>
      using \<open>closedt 0 ?t\<close> by blast }

  { fix P
    assume \<open>Neg (Forall P) \<in> ?H\<close>
    obtain n where *: \<open>Neg (Forall P) = f n\<close>
      using surj by blast

    let ?t = \<open>App (SOME k. k \<notin> (\<Union>p \<in> extend S C f n \<union> {f n}. params p)) []\<close>
    have \<open>closedt 0 ?t\<close> by simp

    have \<open>Neg (Forall P) \<in> (\<Union>n. extend S C f n)\<close>
      using \<open>Neg (Forall P) \<in> ?H\<close> Extend_def by blast
    then have \<open>extend S C f n \<union> {f n} \<subseteq> (\<Union>n. extend S C f n)\<close>
      using * by (simp add: UN_upper)
    then have \<open>extend S C f n \<union> {f n} \<in> C\<close>
      using Extend_def \<open>Extend S C f \<in> C\<close> fin_ch finite_char_closed
      unfolding subset_closed_def by metis
    then have \<open>Neg (P[?t/0]) \<in> extend S C f (Suc n)\<close>
      using * Neg_Forall_in_extend by blast
    then have \<open>Neg (P[?t/0]) \<in> ?H\<close>
      using Extend_def by blast
    then show \<open>\<exists>t. closedt 0 t \<and> Neg (P[t/0]) \<in> ?H\<close>
      using \<open>closedt 0 ?t\<close> by blast }
qed

subsection \<open>Model existence theorem\<close>

text \<open>
\label{sec:model-existence}
Since the result of extending \<open>S\<close> is a superset of \<open>S\<close>,
it follows that each consistent set \<open>S\<close> has a Herbrand model:
\<close>

lemma hintikka_Extend_S:
  assumes \<open>consistency C\<close> and \<open>S \<in> C\<close>
    and \<open>infinite (- (\<Union>p \<in> S. params p))\<close>
  shows \<open>hintikka (Extend S (mk_finite_char (mk_alt_consistency (close C))) from_nat)\<close>
    (is \<open>hintikka (Extend S ?C' from_nat)\<close>)
proof -
  have \<open>finite_char ?C'\<close>
    using finite_char by blast
  moreover have \<open>\<forall>y. y = from_nat (to_nat y)\<close>
    by simp
  then have \<open>\<forall>y. \<exists>n. y = from_nat n\<close>
    by blast
  moreover have \<open>alt_consistency ?C'\<close>
    using alt_consistency close_closed close_consistency \<open>consistency C\<close>
      finite_alt_consistency mk_alt_consistency_closed
    by blast
  moreover have \<open>S \<in> close C\<close>
    using close_subset \<open>S \<in> C\<close> by blast
  then have \<open>S \<in> mk_alt_consistency (close C)\<close>
    using mk_alt_consistency_subset by blast
  then have \<open>S \<in> ?C'\<close>
    using close_closed finite_char_subset mk_alt_consistency_closed by blast
  ultimately show ?thesis
    using extend_hintikka \<open>infinite (- (\<Union>p \<in> S. params p))\<close>
    by metis
qed

theorem model_existence:
  assumes \<open>consistency C\<close>
    and \<open>S \<in> C\<close>
    and \<open>infinite (- (\<Union>p \<in> S. params p))\<close>
    and \<open>p \<in> S\<close>
    and \<open>closed 0 p\<close>
  shows \<open>eval e HApp (\<lambda>a ts. Pred a (terms_of_hterms ts) \<in> Extend S
        (mk_finite_char (mk_alt_consistency (close C))) from_nat) p\<close>
  using assms hintikka_model hintikka_Extend_S Extend_subset
  by blast

subsection \<open>Completeness for Natural Deduction\<close>

text \<open>
Thanks to the model existence theorem, we can now show the completeness
of the natural deduction calculus introduced in \secref{sec:proof-calculus}.
In order for the model existence theorem to be applicable, we have to prove
that the set of sets that are consistent with respect to \<open>\<turnstile>\<close> is a
consistency property:
\<close>

theorem deriv_consistency:
  assumes inf_param: \<open>infinite (UNIV :: 'a set)\<close>
  shows \<open>consistency {S::('a, 'b) form set. \<exists>G. S = set G \<and> \<not> G \<turnstile> FF}\<close>
  unfolding consistency_def
proof (intro conjI allI impI notI)
  fix S :: \<open>('a, 'b) form set\<close>
  assume \<open>S \<in> {set G | G. \<not> G \<turnstile> FF}\<close> (is \<open>S \<in> ?C\<close>)
  then obtain G :: \<open>('a, 'b) form list\<close>
    where *: \<open>S = set G\<close> and \<open>\<not> G \<turnstile> FF\<close>
    by blast

  { fix p ts
    assume \<open>Pred p ts \<in> S \<and> Neg (Pred p ts) \<in> S\<close>
    then have \<open>G \<turnstile> Pred p ts\<close> and \<open>G \<turnstile> Neg (Pred p ts)\<close>
      using Assum * by blast+
    then have \<open>G \<turnstile> FF\<close>
      using NegE by blast
    then show False
      using \<open>\<not> G \<turnstile> FF\<close> by blast }

  { assume \<open>FF \<in> S\<close>
    then have \<open>G \<turnstile> FF\<close>
      using Assum * by blast
    then show False
      using \<open>\<not> G \<turnstile> FF\<close> by blast }

  { assume \<open>Neg TT \<in> S\<close>
    then have \<open>G \<turnstile> Neg TT\<close>
      using Assum * by blast
    moreover have \<open>G \<turnstile> TT\<close>
      using TTI by blast
    ultimately have \<open>G \<turnstile> FF\<close>
      using NegE by blast
    then show False
      using \<open>\<not> G \<turnstile> FF\<close> by blast }

  { fix Z
    assume \<open>Neg (Neg Z) \<in> S\<close>
    then have \<open>G \<turnstile> Neg (Neg Z)\<close>
      using Assum * by blast

    { assume \<open>Z # G \<turnstile> FF\<close>
      then have \<open>G \<turnstile> Neg Z\<close>
        using NegI by blast
      then have \<open>G \<turnstile> FF\<close>
        using NegE \<open>G \<turnstile> Neg (Neg Z)\<close> by blast
      then have False
        using \<open>\<not> G \<turnstile> FF\<close> by blast }
    then have \<open>\<not> Z # G \<turnstile> FF\<close>
      by blast
    moreover have \<open>S \<union> {Z} = set (Z # G)\<close>
      using * by simp
    ultimately show \<open>S \<union> {Z} \<in> ?C\<close>
      by blast }

  { fix A B
    assume \<open>And A B \<in> S\<close>
    then have \<open>G \<turnstile> And A B\<close>
      using Assum * by blast
    then have \<open>G \<turnstile> A\<close> and \<open>G \<turnstile> B\<close>
      using AndE1 AndE2 by blast+

    { assume \<open>A # B # G \<turnstile> FF\<close>
      then have \<open>B # G \<turnstile> Neg A\<close>
        using NegI by blast
      then have \<open>G \<turnstile> Neg A\<close>
        using cut \<open>G \<turnstile> B\<close> by blast
      then have \<open>G \<turnstile> FF\<close>
        using NegE \<open>G \<turnstile> A\<close> by blast
      then have False
        using \<open>\<not> G \<turnstile> FF\<close> by blast }
    then have \<open>\<not> A # B # G \<turnstile> FF\<close>
      by blast
    moreover have \<open>S \<union> {A, B} = set (A # B # G)\<close>
      using * by simp
    ultimately show \<open>S \<union> {A, B} \<in> ?C\<close>
      by blast }

  { fix A B
    assume \<open>Neg (Or A B) \<in> S\<close>
    then have \<open>G \<turnstile> Neg (Or A B)\<close>
      using Assum * by blast

    have \<open>A # Neg B # G \<turnstile> A\<close>
      by (simp add: Assum)
    then have \<open>A # Neg B # G \<turnstile> Or A B\<close>
      using OrI1 by blast
    moreover have \<open>A # Neg B # G \<turnstile> Neg (Or A B)\<close>
      using * \<open>Neg (Or A B) \<in> S\<close> by (simp add: Assum)
    ultimately have \<open>A # Neg B # G \<turnstile> FF\<close>
      using NegE \<open>A # Neg B # G \<turnstile> Neg (Or A B)\<close> by blast
    then have \<open>Neg B # G \<turnstile> Neg A\<close>
      using NegI by blast

    have \<open>B # G \<turnstile> B\<close>
      by (simp add: Assum)
    then have \<open>B # G \<turnstile> Or A B\<close>
      using OrI2 by blast
    moreover have \<open>B # G \<turnstile> Neg (Or A B)\<close>
      using * \<open>Neg (Or A B) \<in> S\<close> by (simp add: Assum)
    ultimately have \<open>B # G \<turnstile> FF\<close>
      using NegE \<open>B # G \<turnstile> Neg (Or A B)\<close> by blast
    then have \<open>G \<turnstile> Neg B\<close>
      using NegI by blast

    { assume \<open>Neg A # Neg B # G \<turnstile> FF\<close>
      then have \<open>Neg B # G \<turnstile> Neg (Neg A)\<close>
        using NegI by blast
      then have \<open>Neg B # G \<turnstile> FF\<close>
        using NegE \<open>Neg B # G \<turnstile> Neg A\<close> by blast
      then have \<open>G \<turnstile> FF\<close>
        using cut \<open>G \<turnstile> Neg B\<close> by blast
      then have False
        using \<open>\<not> G \<turnstile> FF\<close> by blast }
    then have \<open>\<not> Neg A # Neg B # G \<turnstile> FF\<close>
      by blast
    moreover have \<open>S \<union> {Neg A, Neg B} = set (Neg A # Neg B # G)\<close>
      using * by simp
    ultimately show \<open>S \<union> {Neg A, Neg B} \<in> ?C\<close>
      by blast }

  { fix A B
    assume \<open>Neg (Impl A B) \<in> S\<close>

    have \<open>A # Neg A # Neg B # G \<turnstile> A\<close>
      by (simp add: Assum)
    moreover have \<open>A # Neg A # Neg B # G \<turnstile> Neg A\<close>
      by (simp add: Assum)
    ultimately have \<open>A # Neg A # Neg B # G \<turnstile> FF\<close>
      using NegE by blast
    then have \<open>A # Neg A # Neg B # G \<turnstile> B\<close>
      using FFE by blast
    then have \<open>Neg A # Neg B # G \<turnstile> Impl A B\<close>
      using ImplI by blast
    moreover have \<open>Neg A # Neg B # G \<turnstile> Neg (Impl A B)\<close>
      using * \<open>Neg (Impl A B) \<in> S\<close> by (simp add: Assum)
    ultimately have \<open>Neg A # Neg B # G \<turnstile> FF\<close>
      using NegE by blast
    then have \<open>Neg B # G \<turnstile> A\<close>
      using Class by blast

    have \<open>A # B # G \<turnstile> B\<close>
      by (simp add: Assum)
    then have \<open>B # G \<turnstile> Impl A B\<close>
      using ImplI by blast
    moreover have \<open>B # G \<turnstile> Neg (Impl A B)\<close>
      using * \<open>Neg (Impl A B) \<in> S\<close> by (simp add: Assum)
    ultimately have \<open>B # G \<turnstile> FF\<close>
      using NegE by blast
    then have \<open>G \<turnstile> Neg B\<close>
      using NegI by blast

    { assume \<open>A # Neg B # G \<turnstile> FF\<close>
      then have \<open>Neg B # G \<turnstile> Neg A\<close>
        using NegI by blast
      then have \<open>Neg B # G \<turnstile> FF\<close>
        using NegE \<open>Neg B # G \<turnstile> A\<close> by blast
      then have \<open>G \<turnstile> FF\<close>
        using cut \<open>G \<turnstile> Neg B\<close> by blast
      then have False
        using \<open>\<not> G \<turnstile> FF\<close>
        by blast }
    then have \<open>\<not> A # Neg B # G \<turnstile> FF\<close>
      by blast
    moreover have \<open>{A, Neg B} \<union> S = set (A # Neg B # G)\<close>
      using * by simp
    ultimately show \<open>S \<union> {A, Neg B} \<in> ?C\<close>
      by blast }

  { fix A B
    assume \<open>Or A B \<in> S\<close>
    then have \<open>G \<turnstile> Or A B\<close>
      using * Assum by blast

    { assume \<open>(\<forall>G'. set G' = S \<union> {A} \<longrightarrow> G' \<turnstile> FF)\<close>
        and \<open>(\<forall>G'. set G' = S \<union> {B} \<longrightarrow> G' \<turnstile> FF)\<close>
      then have \<open>A # G \<turnstile> FF\<close> and \<open>B # G \<turnstile> FF\<close>
        using * by simp_all
      then have \<open>G \<turnstile> FF\<close>
        using OrE \<open>G \<turnstile> Or A B\<close> by blast
      then have False
        using \<open>\<not> G \<turnstile> FF\<close> by blast }
    then show \<open>S \<union> {A} \<in> ?C \<or> S \<union> {B} \<in> ?C\<close>
      by blast }

  { fix A B
    assume \<open>Neg (And A B) \<in> S\<close>

    let ?x = \<open>Or (Neg A) (Neg B)\<close>

    have \<open>B # A # Neg ?x # G \<turnstile> A\<close> and \<open>B # A # Neg ?x # G \<turnstile> B\<close>
      by (simp_all add: Assum)
    then have \<open>B # A # Neg ?x # G \<turnstile> And A B\<close>
      using AndI by blast
    moreover have \<open>B # A # Neg ?x # G \<turnstile> Neg (And A B)\<close>
      using * \<open>Neg (And A B) \<in> S\<close> by (simp add: Assum)
    ultimately have \<open>B # A # Neg ?x # G \<turnstile> FF\<close>
      using NegE by blast
    then have \<open>A # Neg ?x # G \<turnstile> Neg B\<close>
      using NegI by blast
    then have \<open>A # Neg ?x # G \<turnstile> ?x\<close>
      using OrI2 by blast
    moreover have \<open>A # Neg ?x # G \<turnstile> Neg ?x\<close>
      by (simp add: Assum)
    ultimately have \<open>A # Neg ?x # G \<turnstile> FF\<close>
      using NegE by blast
    then have \<open>Neg ?x # G \<turnstile> Neg A\<close>
      using NegI by blast
    then have \<open>Neg ?x # G \<turnstile> ?x\<close>
      using OrI1 by blast
    then have \<open>G \<turnstile> Or (Neg A) (Neg B)\<close>
      using Class' by blast

    { assume \<open>(\<forall>G'. set G' = S \<union> {Neg A} \<longrightarrow> G' \<turnstile> FF)\<close>
        and \<open>(\<forall>G'. set G' = S \<union> {Neg B} \<longrightarrow> G' \<turnstile> FF)\<close>
      then have \<open>Neg A # G \<turnstile> FF\<close> and \<open>Neg B # G \<turnstile> FF\<close>
        using * by simp_all
      then have \<open>G \<turnstile> FF\<close>
        using OrE \<open>G \<turnstile> Or (Neg A) (Neg B)\<close> by blast
      then have False
        using \<open>\<not> G \<turnstile> FF\<close> by blast }
    then show \<open>S \<union> {Neg A} \<in> ?C \<or> S \<union> {Neg B} \<in> ?C\<close>
      by blast }

  { fix A B
    assume \<open>Impl A B \<in> S\<close>

    let ?x = \<open>Or (Neg A) B\<close>

    have \<open>A # Neg ?x # G \<turnstile> A\<close>
      by (simp add: Assum)
    moreover have \<open>A # Neg ?x # G \<turnstile> Impl A B\<close>
      using * \<open>Impl A B \<in> S\<close> by (simp add: Assum)
    ultimately have \<open>A # Neg ?x # G \<turnstile> B\<close>
      using ImplE by blast
    then have \<open>A # Neg ?x # G \<turnstile> ?x\<close>
      using OrI2 by blast
    moreover have \<open>A # Neg ?x # G \<turnstile> Neg ?x\<close>
      by (simp add: Assum)
    ultimately have \<open>A # Neg ?x # G \<turnstile> FF\<close>
      using NegE by blast
    then have \<open>Neg ?x # G \<turnstile> Neg A\<close>
      using NegI by blast
    then have \<open>Neg ?x # G \<turnstile> ?x\<close>
      using OrI1 by blast
    then have \<open>G \<turnstile> Or (Neg A) B\<close>
      using Class' by blast

    { assume \<open>(\<forall>G'. set G' = S \<union> {Neg A} \<longrightarrow> G' \<turnstile> FF)\<close>
        and \<open>(\<forall>G'. set G' = S \<union> {B} \<longrightarrow> G' \<turnstile> FF)\<close>
      then have \<open>Neg A # G \<turnstile> FF\<close> and \<open>B # G \<turnstile> FF\<close>
        using * by simp_all
      then have \<open>G \<turnstile> FF\<close>
        using OrE \<open>G \<turnstile> Or (Neg A) B\<close> by blast
      then have False
        using \<open>\<not> G \<turnstile> FF\<close> by blast }
    then show \<open>S \<union> {Neg A} \<in> ?C \<or> S \<union> {B} \<in> ?C\<close>
      by blast }

  { fix P and t :: \<open>'a term\<close>
    assume \<open>closedt 0 t\<close> and \<open>Forall P \<in> S\<close>
    then have \<open>G \<turnstile> Forall P\<close>
      using Assum * by blast
    then have \<open>G \<turnstile> P[t/0]\<close>
      using ForallE by blast

    { assume \<open>P[t/0] # G \<turnstile> FF\<close>
      then have \<open>G \<turnstile> FF\<close>
        using cut \<open>G \<turnstile> P[t/0]\<close> by blast
      then have False
        using \<open>\<not> G \<turnstile> FF\<close> by blast }
    then have \<open>\<not> P[t/0] # G \<turnstile> FF\<close>
      by blast
    moreover have \<open>S \<union> {P[t/0]} = set (P[t/0] # G)\<close>
      using * by simp
    ultimately show \<open>S \<union> {P[t/0]} \<in> ?C\<close>
      by blast }

  { fix P and t :: \<open>'a term\<close>
    assume \<open>closedt 0 t\<close> and \<open>Neg (Exists P) \<in> S\<close>
    then have \<open>G \<turnstile> Neg (Exists P)\<close>
      using Assum * by blast
    then have \<open>P[t/0] \<in> set (P[t/0] # G)\<close>
      by (simp add: Assum)
    then have \<open>P[t/0] # G \<turnstile> P[t/0]\<close>
      using Assum by blast
    then have \<open>P[t/0] # G \<turnstile> Exists P\<close>
      using ExistsI by blast
    moreover have \<open>P[t/0] # G \<turnstile> Neg (Exists P)\<close>
      using * \<open>Neg (Exists P) \<in> S\<close> by (simp add: Assum)
    ultimately have \<open>P[t/0] # G \<turnstile> FF\<close>
      using NegE by blast
    then have \<open>G \<turnstile> Neg (P[t/0])\<close>
      using NegI by blast

    { assume \<open>Neg (P[t/0]) # G \<turnstile> FF\<close>
      then have \<open>G \<turnstile> FF\<close>
        using cut \<open>G \<turnstile> Neg (P[t/0])\<close> by blast
      then have False
        using \<open>\<not> G \<turnstile> FF\<close> by blast }
    then have \<open>\<not> Neg (P[t/0]) # G \<turnstile> FF\<close>
      by blast
    moreover have \<open>S \<union> {Neg (P[t/0])} = set (Neg (P[t/0]) # G)\<close>
      using * by simp
    ultimately show \<open>S \<union> {Neg (P[t/0])} \<in> ?C\<close>
      by blast }

  { fix P
    assume \<open>Exists P \<in> S\<close>
    then have \<open>G \<turnstile> Exists P\<close>
      using * Assum by blast

    have \<open>finite ((\<Union>p \<in> set G. params p) \<union> params P)\<close>
      by simp
    then have \<open>infinite (- ((\<Union>p \<in> set G. params p) \<union> params P))\<close>
      using inf_param Diff_infinite_finite finite_compl by blast
    then have \<open>infinite (- ((\<Union>p \<in> set G. params p) \<union> params P))\<close>
      by (simp add: Compl_eq_Diff_UNIV)
    then obtain x where **: \<open>x \<in> - ((\<Union>p \<in> set G. params p) \<union> params P)\<close>
      using infinite_imp_nonempty by blast

    { assume \<open>P[App x []/0] # G \<turnstile> FF\<close>
      moreover have \<open>list_all (\<lambda>p. x \<notin> params p) G\<close>
        using ** by (simp add: list_all_iff)
      moreover have \<open>x \<notin> params P\<close>
        using ** by simp
      moreover have \<open>x \<notin> params FF\<close>
        by simp
      ultimately have \<open>G \<turnstile> FF\<close>
        using ExistsE \<open>G \<turnstile> Exists P\<close> by fast
      then have False
        using \<open>\<not> G \<turnstile> FF\<close>
        by blast}
    then have \<open>\<not> P[App x []/0] # G \<turnstile> FF\<close>
      by blast
    moreover have \<open>S \<union> {P[App x []/0]} = set (P[App x []/0] # G)\<close>
      using * by simp
    ultimately show \<open>\<exists>x. S \<union> {P[App x []/0]} \<in> ?C\<close>
      by blast }

  { fix P
    assume \<open>Neg (Forall P) \<in> S\<close>
    then have \<open>G \<turnstile> Neg (Forall P)\<close>
      using * Assum by blast

    have \<open>finite ((\<Union>p \<in> set G. params p) \<union> params P)\<close>
      by simp
    then have \<open>infinite (- ((\<Union>p \<in> set G. params p) \<union> params P))\<close>
      using inf_param Diff_infinite_finite finite_compl by blast
    then have \<open>infinite (- ((\<Union>p \<in> set G. params p) \<union> params P))\<close>
      by (simp add: Compl_eq_Diff_UNIV)
    then obtain x where **: \<open>x \<in> - ((\<Union>p \<in> set G. params p) \<union> params P)\<close>
      using infinite_imp_nonempty by blast

    let ?x = \<open>Neg (Exists (Neg P))\<close>

    have \<open>Neg (P[App x []/0]) # ?x # G \<turnstile> Neg P[App x []/0]\<close>
      by (simp add: Assum)
    then have \<open>Neg (P[App x []/0]) # ?x # G \<turnstile> Exists (Neg P)\<close>
      using ExistsI by blast
    moreover have \<open>Neg (P[App x []/0]) # ?x # G \<turnstile> ?x\<close>
      by (simp add: Assum)
    ultimately have \<open>Neg (P[App x []/0]) # ?x # G \<turnstile> FF\<close>
      using NegE by blast
    then have \<open>?x # G \<turnstile> P[App x []/0]\<close>
      using Class by blast
    moreover have \<open>list_all (\<lambda>p. x \<notin> params p) (?x # G)\<close>
      using ** by (simp add: list_all_iff)
    moreover have \<open>x \<notin> params P\<close>
      using ** by simp
    ultimately have \<open>?x # G \<turnstile> Forall P\<close>
      using ForallI by fast
    moreover have \<open>?x # G \<turnstile> Neg (Forall P)\<close>
      using * \<open>Neg (Forall P) \<in> S\<close> by (simp add: Assum)
    ultimately have \<open>?x # G \<turnstile> FF\<close>
      using NegE by blast
    then have \<open>G \<turnstile> Exists (Neg P)\<close>
      using Class by blast

    { assume \<open>Neg (P[App x []/0]) # G \<turnstile> FF\<close>
      moreover have \<open>list_all (\<lambda>p. x \<notin> params p) G\<close>
        using ** by (simp add: list_all_iff)
      moreover have \<open>x \<notin> params P\<close>
        using ** by simp
      moreover have \<open>x \<notin> params FF\<close>
        by simp
      ultimately have \<open>G \<turnstile> FF\<close>
        using ExistsE \<open>G \<turnstile> Exists (Neg P)\<close> by fastforce
      then have False
        using \<open>\<not> G \<turnstile> FF\<close>
        by blast}
    then have \<open>\<not> Neg (P[App x []/0]) # G \<turnstile> FF\<close>
      by blast
    moreover have \<open>S \<union> {Neg (P[App x []/0])} = set (Neg (P[App x []/0]) # G)\<close>
      using * by simp
    ultimately show \<open>\<exists>x. S \<union> {Neg (P[App x []/0])} \<in> ?C\<close>
      by blast }
qed

text \<open>
Hence, by contradiction, we have completeness of natural deduction:
\<close>

theorem natded_complete:
  assumes \<open>closed 0 p\<close>
    and \<open>list_all (closed 0) ps\<close>
    and mod: \<open>\<forall>e f g. e,(f :: nat \<Rightarrow> nat hterm list \<Rightarrow> nat hterm),
              (g :: nat \<Rightarrow> nat hterm list \<Rightarrow> bool),ps \<Turnstile> p\<close>
  shows \<open>ps \<turnstile> p\<close>
proof (rule Class, rule ccontr)
  fix e
  assume \<open>\<not> Neg p # ps \<turnstile> FF\<close>

  let ?S = \<open>set (Neg p # ps)\<close>
  let ?C = \<open>{set (G :: (nat, nat) form list) | G. \<not> G \<turnstile> FF}\<close>
  let ?f = HApp
  let ?g = \<open>(\<lambda>a ts. Pred a (terms_of_hterms ts) \<in> Extend ?S
              (mk_finite_char (mk_alt_consistency (close ?C))) from_nat)\<close>

  from \<open>list_all (closed 0) ps\<close>
  have \<open>\<forall>p \<in> set ps. closed 0 p\<close>
    by (simp add: list_all_iff)

  { fix x
    assume \<open>x \<in> ?S\<close>
    moreover have \<open>consistency ?C\<close>
      using deriv_consistency by blast
    moreover have \<open>?S \<in> ?C\<close>
      using \<open>\<not> Neg p # ps \<turnstile> FF\<close> by blast
    moreover have \<open>infinite (- (\<Union>p \<in> ?S. params p))\<close>
      by (simp add: Compl_eq_Diff_UNIV)
    moreover note \<open>closed 0 p\<close> \<open>\<forall>p \<in> set ps. closed 0 p\<close> \<open>x \<in> ?S\<close>
    then have \<open>closed 0 x\<close> by auto
    ultimately have \<open>eval e ?f ?g x\<close>
      using model_existence by blast }
  then have \<open>list_all (eval e ?f ?g) (Neg p # ps)\<close>
    by (simp add: list_all_iff)
  moreover have \<open>eval e ?f ?g (Neg p)\<close>
    using calculation by simp
  moreover have \<open>list_all (eval e ?f ?g) ps\<close>
    using calculation by simp
  then have \<open>eval e ?f ?g p\<close>
    using mod unfolding model_def by blast
  ultimately show False by simp
qed

section \<open>L\"owenheim-Skolem theorem\<close>

text \<open>
Another application of the model existence theorem presented in \secref{sec:model-existence}
is the L\"owenheim-Skolem theorem. It says that a set of formulae that is satisfiable in an
{\em arbitrary model} is also satisfiable in a {\em Herbrand model}. The main idea behind the
proof is to show that satisfiable sets are consistent, hence they must be satisfiable in a
Herbrand model.
\<close>

theorem sat_consistency:
  \<open>consistency {S. infinite (- (\<Union>p \<in> S. params p)) \<and> (\<exists>f. \<forall>(p::('a, 'b)form) \<in> S. eval e f g p)}\<close>
  unfolding consistency_def
proof (intro allI impI conjI)
  let ?C = \<open>{S. infinite (- (\<Union>p \<in> S. params p)) \<and> (\<exists>f. \<forall>p \<in> S. eval e f g p)}\<close>

  fix S :: \<open>('a, 'b) form set\<close>
  assume \<open>S \<in> ?C\<close>
  then have inf_params: \<open>infinite (- (\<Union>p \<in> S. params p))\<close>
    and \<open>\<exists>f. \<forall>p \<in> S. eval e f g p\<close>
    by blast+
  then obtain f where *: \<open>\<forall>x \<in> S. eval e f g x\<close> by blast

  { fix p ts
    show \<open>\<not> (Pred p ts \<in> S \<and> Neg (Pred p ts) \<in> S)\<close>
    proof
      assume \<open>Pred p ts \<in> S \<and> Neg (Pred p ts) \<in> S\<close>
      then have \<open>eval e f g (Pred p ts) \<and> eval e f g (Neg (Pred p ts))\<close>
        using * by blast
      then show False by simp
    qed }

  show \<open>FF \<notin> S\<close>
    using * by fastforce

  show \<open>Neg TT \<notin> S\<close>
    using * by fastforce

  { fix Z
    assume \<open>Neg (Neg Z) \<in> S\<close>
    then have \<open>\<forall>x \<in> S \<union> {Neg (Neg Z)}. eval e f g x\<close>
      using * by blast
    then have \<open>\<forall>x \<in> S \<union> {Z}. eval e f g x\<close>
      by simp
    moreover have \<open>infinite (- (\<Union>p \<in> S \<union> {Z}. params p))\<close>
      using inf_params by simp
    ultimately show \<open>S \<union> {Z} \<in> ?C\<close>
      by blast }

  { fix A B
    assume \<open>And A B \<in> S\<close>
    then have \<open>\<forall>x \<in> S \<union> {And A B}. eval e f g x\<close>
      using * by blast
    then have \<open>\<forall>x \<in> S \<union> {A, B}. eval e f g x\<close>
      by simp
    moreover have \<open>infinite (- (\<Union>p \<in> S \<union> {A, B}. params p))\<close>
      using inf_params by simp
    ultimately show \<open>S \<union> {A, B} \<in> ?C\<close>
      by blast }

  { fix A B
    assume \<open>Neg (Or A B) \<in> S\<close>
    then have \<open>\<forall>x \<in> S \<union> {Neg (Or A B)}. eval e f g x\<close>
      using * by blast
    then have \<open>\<forall>x \<in> S \<union> {Neg A, Neg B}. eval e f g x\<close>
      by simp
    moreover have \<open>infinite (- (\<Union>p \<in> S \<union> {Neg A, Neg B}. params p))\<close>
      using inf_params by simp
    ultimately show \<open>S \<union> {Neg A, Neg B} \<in> ?C\<close>
      by blast }

  { fix A B
    assume \<open>Neg (Impl A B) \<in> S\<close>
    then have \<open>\<forall>x \<in> S \<union> {Neg (Impl A B)}. eval e f g x\<close>
      using * by blast
    then have \<open>\<forall>x \<in> S \<union> {A, Neg B}. eval e f g x\<close>
      by simp
    moreover have \<open>infinite (- (\<Union>p \<in> S \<union> {A, Neg B}. params p))\<close>
      using inf_params by simp
    ultimately show \<open>S \<union> {A, Neg B} \<in> ?C\<close>
      by blast }

  { fix A B
    assume \<open>Or A B \<in> S\<close>
    then have \<open>\<forall>x \<in> S \<union> {Or A B}. eval e f g x\<close>
      using * by blast
    then have \<open>(\<forall>x \<in> S \<union> {A}. eval e f g x) \<or>
               (\<forall>x \<in> S \<union> {B}. eval e f g x)\<close>
      by simp
    moreover have \<open>infinite (- (\<Union>p \<in> S \<union> {A}. params p))\<close>
      and \<open>infinite (- (\<Union>p \<in> S \<union> {B}. params p))\<close>
      using inf_params by simp_all
    ultimately show \<open>S \<union> {A} \<in> ?C \<or> S \<union> {B} \<in> ?C\<close>
      by blast }

  { fix A B
    assume \<open>Neg (And A B) \<in> S\<close>
    then have \<open>\<forall>x \<in> S \<union> {Neg (And A B)}. eval e f g x\<close>
      using * by blast
    then have \<open>(\<forall>x \<in> S \<union> {Neg A}. eval e f g x) \<or>
               (\<forall>x \<in> S \<union> {Neg B}. eval e f g x)\<close>
      by simp
    moreover have \<open>infinite (- (\<Union>p \<in> S \<union> {Neg A}. params p))\<close>
      and \<open>infinite (- (\<Union>p \<in> S \<union> {Neg B}. params p))\<close>
      using inf_params by simp_all
    ultimately show \<open>S \<union> {Neg A} \<in> ?C \<or> S \<union> {Neg B} \<in> ?C\<close>
      by blast }

  { fix A B
    assume \<open>Impl A B \<in> S\<close>
    then have \<open>\<forall>x \<in> S \<union> {Impl A B}. eval e f g x\<close>
      using * by blast
    then have \<open>(\<forall>x \<in> S \<union> {Neg A}. eval e f g x) \<or>
               (\<forall>x \<in> S \<union> {B}. eval e f g x)\<close>
      by simp
    moreover have \<open>infinite (- (\<Union>p \<in> S \<union> {Neg A}. params p))\<close>
      and \<open>infinite (- (\<Union>p \<in> S \<union> {B}. params p))\<close>
      using inf_params by simp_all
    ultimately show \<open>S \<union> {Neg A} \<in> ?C \<or> S \<union> {B} \<in> ?C\<close>
      by blast }

  { fix P and t :: \<open>'a term\<close>
    assume \<open>Forall P \<in> S\<close>
    then have \<open>\<forall>x \<in> S \<union> {Forall P}. eval e f g x\<close>
      using * by blast
    then have \<open>\<forall>x \<in> S \<union> {P[t/0]}. eval e f g x\<close>
      by simp
    moreover have \<open>infinite (- (\<Union>p \<in> S \<union> {P[t/0]}. params p))\<close>
      using inf_params by simp
    ultimately show \<open>S \<union> {P[t/0]} \<in> ?C\<close>
      by blast }

  { fix P and t :: \<open>'a term\<close>
    assume \<open>Neg (Exists P) \<in> S\<close>
    then have \<open>\<forall>x \<in> S \<union> {Neg (Exists P)}. eval e f g x\<close>
      using * by blast
    then have \<open>\<forall>x \<in> S \<union> {Neg (P[t/0])}. eval e f g x\<close>
      by simp
    moreover have \<open>infinite (- (\<Union>p \<in> S \<union> {Neg (P[t/0])}. params p))\<close>
      using inf_params by simp
    ultimately show \<open>S \<union> {Neg (P[t/0])} \<in> ?C\<close>
      by blast }

  { fix P
    assume \<open>Exists P \<in> S\<close>
    then have \<open>\<forall>x \<in> S \<union> {Exists P}. eval e f g x\<close>
      using * by blast
    then have \<open>eval e f g (Exists P)\<close>
      by blast
    then obtain z where \<open>eval (e\<langle>0:z\<rangle>) f g P\<close>
      by auto
    moreover obtain x where **: \<open>x \<in> - (\<Union>p \<in> S. params p)\<close>
      using inf_params infinite_imp_nonempty by blast
    then have \<open>x \<notin> params P\<close>
      using \<open>Exists P \<in> S\<close> by auto
    ultimately have \<open>eval (e\<langle>0:(f(x := \<lambda>y. z)) x []\<rangle>) (f(x := \<lambda>y. z)) g P\<close>
      by simp
    moreover have \<open>\<forall>p \<in> S. eval e (f(x := \<lambda>y. z)) g p\<close>
      using * ** by simp
    moreover have \<open>infinite (- (\<Union>p \<in> S \<union> {P[App x []/0]}. params p))\<close>
      using inf_params by simp
    ultimately have \<open>S \<union> {P[App x []/0]}  \<in>
                      {S. infinite (- (\<Union>p \<in> S. params p)) \<and> (\<forall>p \<in> S. eval e (f(x := \<lambda>y. z)) g p)}\<close>
      by simp
    then show \<open>\<exists>x. S \<union> {P[App x []/0]} \<in> ?C\<close>
      by blast }

  { fix P
    assume \<open>Neg (Forall P) \<in> S\<close>
    then have \<open>\<forall>x \<in> S \<union> {Neg (Forall P)}. eval e f g x\<close>
      using * by blast
    then have \<open>eval e f g (Neg (Forall P))\<close>
      by blast
    then obtain z where \<open>\<not> eval (e\<langle>0:z\<rangle>) f g P\<close>
      by auto
    moreover obtain x where **: \<open>x \<in> - (\<Union>p \<in> S. params p)\<close>
      using inf_params infinite_imp_nonempty by blast
    then have \<open>x \<notin> params P\<close>
      using \<open>Neg (Forall P) \<in> S\<close> by auto
    ultimately have \<open>\<not> eval (e\<langle>0:(f(x := \<lambda>y. z)) x []\<rangle>) (f(x := \<lambda>y. z)) g P\<close>
      by simp
    moreover have \<open>\<forall>p \<in> S. eval e (f(x := \<lambda>y. z)) g p\<close>
      using * ** by simp
    moreover have \<open>infinite (- (\<Union>p \<in> S \<union> {P[App x []/0]}. params p))\<close>
      using inf_params by simp
    ultimately have \<open>S \<union> {Neg (P[App x []/0])}  \<in>
                      {S. infinite (- (\<Union>p \<in> S. params p)) \<and> (\<forall>p \<in> S. eval e (f(x := \<lambda>y. z)) g p)}\<close>
      by simp
    then show \<open>\<exists>x. S \<union> {Neg (P[App x []/0])} \<in> ?C\<close>
      by blast }
qed

theorem doublep_infinite_params:
  \<open>infinite (- (\<Union>p \<in> psubst (\<lambda>n::nat. 2 * n) ` S. params p))\<close>
proof (rule infinite_super)
  show \<open>infinite (range (\<lambda>n::nat. 2 * n + 1))\<close>
    using inj_onI Suc_1 Suc_mult_cancel1 add_right_imp_eq finite_imageD infinite_UNIV_char_0
    by (metis (no_types, lifting))
next
  have \<open>\<And>m n. Suc (2 * m) \<noteq> 2 * n\<close> by arith
  then show \<open>range (\<lambda>n. 2 * n + 1)
    \<subseteq> - (\<Union>p::(nat, 'a) form \<in> psubst (\<lambda>n . 2 * n) ` S. params p)\<close>
    by auto
qed

text \<open>
When applying the model existence theorem, there is a technical
complication. We must make sure that there are infinitely many
unused parameters. In order to achieve this, we encode parameters
as natural numbers and multiply each parameter occurring in the
set \<open>S\<close> by \<open>2\<close>.
\<close>

theorem loewenheim_skolem:
  assumes evalS: \<open>\<forall>p \<in> S. eval e f g p\<close>
  shows \<open>\<forall>p \<in> S. closed 0 p \<longrightarrow> eval e' (\<lambda>n. HApp (2*n)) (\<lambda>a ts.
      Pred a (terms_of_hterms ts) \<in> Extend (psubst (\<lambda>n. 2 * n) ` S)
        (mk_finite_char (mk_alt_consistency (close
          {S. infinite (- (\<Union>p \<in> S. params p)) \<and> (\<exists>f. \<forall>p \<in> S. eval e f g p)}))) from_nat) p\<close>
    (is \<open>\<forall>_ \<in> _. _ _ _ \<longrightarrow> eval _ _ ?g _\<close>)
  using evalS
proof (intro ballI impI)
  fix p

  let ?C = \<open>{S. infinite (- (\<Union>p \<in> S. params p)) \<and> (\<exists>f. \<forall>x \<in> S. eval e f g x)}\<close>

  assume \<open>p \<in> S\<close>
    and \<open>closed 0 p\<close>
  then have \<open>eval e f g p\<close>
    using evalS by blast
  then have \<open>\<forall>x \<in> S. eval e f g x\<close>
    using evalS by blast
  then have \<open>\<forall>p \<in> psubst (\<lambda>n. 2 * n) ` S. eval e (\<lambda>n. f (n div 2)) g p\<close>
    by (simp add: psubst_eval)
  then have \<open>psubst (\<lambda>n. 2 * n) ` S \<in> ?C\<close>
    using doublep_infinite_params by blast
  moreover have \<open>psubst (\<lambda>n. 2 * n) p \<in> psubst (\<lambda>n. 2 * n) ` S\<close>
    using \<open>p \<in> S\<close> by blast
  moreover have \<open>closed 0 (psubst (\<lambda>n. 2 * n) p)\<close>
    using \<open>closed 0 p\<close> by simp
  moreover have \<open>consistency ?C\<close>
    using sat_consistency by blast
  ultimately have \<open>eval e' HApp ?g (psubst (\<lambda>n. 2 * n) p)\<close>
    using model_existence by blast
  then show \<open>eval e' (\<lambda>n. HApp (2 * n)) ?g p\<close>
    using psubst_eval by blast
qed

section \<open>Completeness for open formulas\<close>

abbreviation \<open>new_term c t \<equiv> c \<notin> paramst t\<close>
abbreviation \<open>new_list c ts \<equiv> c \<notin> paramsts ts\<close>

abbreviation \<open>new c p \<equiv> c \<notin> params p\<close>

abbreviation \<open>news c z \<equiv> list_all (new c) z\<close>

subsection \<open>Renaming\<close>

lemma new_psubst_image':
  \<open>new_term c t \<Longrightarrow> d \<notin> image f (paramst t) \<Longrightarrow> new_term d (psubstt (f(c := d)) t)\<close>
  \<open>new_list c l \<Longrightarrow> d \<notin> image f (paramsts l) \<Longrightarrow> new_list d (psubstts (f(c := d)) l)\<close>
  by (induct t and l rule: paramst.induct paramsts.induct) auto

lemma new_psubst_image: \<open>new c p \<Longrightarrow> d \<notin> image f (params p) \<Longrightarrow> new d (psubst (f(c := d)) p)\<close>
  using new_psubst_image' by (induct p) auto

lemma news_psubst: \<open>news c z \<Longrightarrow> d \<notin> image f (\<Union>p \<in> set z. params p) \<Longrightarrow>
    news d (map (psubst (f(c := d))) z)\<close>
  using new_psubst_image by (induct z) auto

lemma member_psubst: \<open>p \<in> set z \<Longrightarrow> psubst f p \<in> set (map (psubst f) z)\<close>
  by (induct z) auto

lemma deriv_psubst:
  fixes f :: \<open>'a \<Rightarrow> 'a\<close>
  assumes inf_params: \<open>infinite (UNIV :: 'a set)\<close>
  shows \<open>z \<turnstile> p \<Longrightarrow> map (psubst f) z \<turnstile> psubst f p\<close>
proof (induct z p arbitrary: f rule: deriv.induct)
  case (Assum a G)
  then show ?case
    using deriv.Assum member_psubst by blast
next
  case (TTI G)
  then show ?case
    using deriv.TTI by auto
next
  case (FFE G a)
  then show ?case
    using deriv.FFE by auto
next
  case (NegI a G)
  then show ?case
    using deriv.NegI by auto
next
  case (NegE G a)
  then show ?case
    using deriv.NegE by auto
next
  case (Class a G)
  then show ?case
    using deriv.Class by auto
next
  case (ImplE G a b)
  then have \<open>map (psubst f) G \<turnstile> Impl (psubst f a) (psubst f b)\<close>
    and \<open>map (psubst f) G \<turnstile> psubst f a\<close>
    by simp_all
  then show ?case
    using deriv.ImplE by blast
next
  case (ImplI G a b)
  then show ?case
    using deriv.ImplI by auto
next
  case (OrE G a b c)
  then have \<open>map (psubst f) G \<turnstile> Or (psubst f a) (psubst f b)\<close>
    and \<open>psubst f a # map (psubst f) G \<turnstile> psubst f c\<close>
    and \<open>psubst f b # map (psubst f) G \<turnstile> psubst f c\<close>
    by simp_all
  then show ?case
    using deriv.OrE by blast
next
  case (OrI1 G a b)
  then show ?case
    using deriv.OrI1 by auto
next
  case (OrI2 G a b)
  then show ?case
    using deriv.OrI2 by auto
next
  case (AndE1 G a b)
  then show ?case
    using deriv.AndE1 by auto
next
  case (AndE2 p q z)
  then show ?case
    using deriv.AndE2 by auto
next
  case (AndI G a b)
  then show ?case
    using deriv.AndI by fastforce
next
  case (ExistsE z p c q)
  let ?params = \<open>params p \<union> params q \<union> (\<Union>p \<in> set z. params p)\<close>

  have \<open>finite ?params\<close>
    by simp
  then obtain fresh where *: \<open>fresh \<notin> ?params \<union> {c} \<union> image f ?params\<close>
    using ex_new_if_finite inf_params
    by (metis finite.emptyI finite.insertI finite_UnI finite_imageI)

  let ?f = \<open>f(c := fresh)\<close>

  have \<open>news c (p # q # z)\<close>
    using ExistsE by simp
  then have \<open>new fresh (psubst ?f p)\<close> \<open>new fresh (psubst ?f q)\<close> \<open>news fresh (map (psubst ?f) z)\<close>
    using * new_psubst_image news_psubst by (fastforce simp add: image_Un)+
  then have \<open>map (psubst ?f) z = map (psubst f) z\<close>
    using ExistsE by (metis (mono_tags, lifting) Ball_set map_eq_conv psubst_upd)

  have \<open>map (psubst ?f) z \<turnstile> psubst ?f (Exists p)\<close>
    using ExistsE by blast
  then have \<open>map (psubst ?f) z \<turnstile> Exists (psubst ?f p)\<close>
    by simp
  moreover have \<open>map (psubst ?f) (subst p (App c []) 0 # z) \<turnstile> psubst ?f q\<close>
    using ExistsE by blast
  then have \<open>subst (psubst ?f p) (App fresh []) 0 # map (psubst ?f) z \<turnstile> psubst ?f q\<close>
    by simp
  moreover have \<open>news fresh (map (psubst ?f) (p # q # z))\<close>
    using \<open>new fresh (psubst ?f p)\<close> \<open>new fresh (psubst ?f q)\<close> \<open>news fresh (map (psubst ?f) z)\<close>
    by simp
  then have \<open>new fresh (psubst ?f p)\<close> \<open>new fresh (psubst ?f q)\<close> \<open>news fresh (map (psubst ?f) z)\<close>
    by simp_all
  ultimately have \<open>map (psubst ?f) z \<turnstile> psubst ?f q\<close>
    using deriv.ExistsE by metis
  then show ?case
    using ExistsE \<open>map (psubst ?f) z = map (psubst f) z\<close> by simp
next
  case (ExistsI z p t)
  then show ?case
    using deriv.ExistsI by auto
next
  case (ForallE z p t)
  then show ?case
    using deriv.ForallE by auto
next
  case (ForallI z p c)
  let ?params = \<open>params p \<union>(\<Union>p \<in> set z. params p)\<close>

  have \<open>finite ?params\<close>
    by simp
  then obtain fresh where *: \<open>fresh \<notin> ?params \<union> {c} \<union> image f ?params\<close>
    using ex_new_if_finite inf_params
    by (metis finite.emptyI finite.insertI finite_UnI finite_imageI)

  let ?f = \<open>f(c := fresh)\<close>

  have \<open>news c (p # z)\<close>
    using ForallI by simp
  then have \<open>new fresh (psubst ?f p)\<close> \<open>news fresh (map (psubst ?f) z)\<close>
    using * new_psubst_image news_psubst by (fastforce simp add: image_Un)+
  then have \<open>map (psubst ?f) z = map (psubst f) z\<close>
    using ForallI by (metis (mono_tags, lifting) Ball_set map_eq_conv psubst_upd)

  have \<open>map (psubst ?f) z \<turnstile> psubst ?f (subst p (App c []) 0)\<close>
    using ForallI by blast
  then have \<open>map (psubst ?f) z \<turnstile> subst (psubst ?f p) (App fresh []) 0\<close>
    by simp
  moreover have \<open>news fresh (map (psubst ?f) (p # z))\<close>
    using \<open>new fresh (psubst ?f p)\<close> \<open>news fresh (map (psubst ?f) z)\<close>
    by simp
  then have \<open>new fresh (psubst ?f p)\<close> \<open>news fresh (map (psubst ?f) z)\<close>
    by simp_all
  ultimately have \<open>map (psubst ?f) z \<turnstile> Forall (psubst ?f p)\<close>
    using deriv.ForallI by metis
  then show ?case
    using ForallI \<open>map (psubst ?f) z = map (psubst f) z\<close> by simp
qed

subsection \<open>Substitution for constants\<close>

primrec
  subc_term :: \<open>'a \<Rightarrow> 'a term \<Rightarrow> 'a term \<Rightarrow> 'a term\<close> and
  subc_list :: \<open>'a \<Rightarrow> 'a term \<Rightarrow> 'a term list \<Rightarrow> 'a term list\<close> where
  \<open>subc_term c s (Var n) = Var n\<close> |
  \<open>subc_term c s (App i l) = (if i = c then s else App i (subc_list c s l))\<close> |
  \<open>subc_list c s [] = []\<close> |
  \<open>subc_list c s (t # l) = subc_term c s t # subc_list c s l\<close>

primrec subc :: \<open>'a \<Rightarrow> 'a term \<Rightarrow> ('a, 'b) form \<Rightarrow> ('a, 'b) form\<close> where
  \<open>subc c s FF = FF\<close> |
  \<open>subc c s TT = TT\<close> |
  \<open>subc c s (Pred i l) = Pred i (subc_list c s l)\<close> |
  \<open>subc c s (Neg p) = Neg (subc c s p)\<close> |
  \<open>subc c s (Impl p q) = Impl (subc c s p) (subc c s q)\<close> |
  \<open>subc c s (Or p q) = Or (subc c s p) (subc c s q)\<close> |
  \<open>subc c s (And p q) = And (subc c s p) (subc c s q)\<close> |
  \<open>subc c s (Exists p) = Exists (subc c (liftt s) p)\<close> |
  \<open>subc c s (Forall p) = Forall (subc c (liftt s) p)\<close>

primrec subcs :: \<open>'a \<Rightarrow> 'a term \<Rightarrow> ('a, 'b) form list \<Rightarrow> ('a, 'b) form list\<close> where
  \<open>subcs c s [] = []\<close> |
  \<open>subcs c s (p # z) = subc c s p # subcs c s z\<close>

lemma subst_0_lift:
  \<open>substt (liftt t) s 0 = t\<close>
  \<open>substts (liftts l) s 0 = l\<close>
  by (induct t and l rule: substt.induct substts.induct) simp_all

lemma params_lift [simp]:
  fixes t :: \<open>'a term\<close> and ts :: \<open>'a term list\<close>
  shows
    \<open>paramst (liftt t) = paramst t\<close>
    \<open>paramsts (liftts ts) = paramsts ts\<close>
  by (induct t and ts rule: paramst.induct paramsts.induct) simp_all

lemma subst_new' [simp]:
  \<open>new_term c s \<Longrightarrow> new_term c t \<Longrightarrow> new_term c (substt t s m)\<close>
  \<open>new_term c s \<Longrightarrow> new_list c l \<Longrightarrow> new_list c (substts l s m)\<close>
  by (induct t and l rule: substt.induct substts.induct) simp_all

lemma subst_new [simp]: \<open>new_term c s \<Longrightarrow> new c p \<Longrightarrow> new c (subst p s m)\<close>
  by (induct p arbitrary: m s) simp_all

lemma subst_new_all:
  assumes \<open>a \<notin> set cs\<close> \<open>list_all (\<lambda>c. new c p) cs\<close>
  shows \<open>list_all (\<lambda>c. new c (subst p (App a []) m)) cs\<close>
  using assms by (induct cs) auto

lemma subc_new' [simp]:
  \<open>new_term c t \<Longrightarrow> subc_term c s t = t\<close>
  \<open>new_list c l \<Longrightarrow> subc_list c s l = l\<close>
  by (induct t and l rule: subc_term.induct subc_list.induct) auto

lemma subc_new [simp]: \<open>new c p \<Longrightarrow> subc c s p = p\<close>
  by (induct p arbitrary: s) simp_all

lemma subcs_news: \<open>news c z \<Longrightarrow> subcs c s z = z\<close>
  by (induct z) simp_all

lemma subc_psubst' [simp]:
  \<open>(\<forall>x \<in> paramst t. x \<noteq> c \<longrightarrow> f x \<noteq> f c) \<Longrightarrow>
    psubstt f (subc_term c s t) = subc_term (f c) (psubstt f s) (psubstt f t)\<close>
  \<open>(\<forall>x \<in> paramsts l. x \<noteq> c \<longrightarrow> f x \<noteq> f c) \<Longrightarrow>
    psubstts f (subc_list c s l) = subc_list (f c) (psubstt f s) (psubstts f l)\<close>
  by (induct t and l rule: psubstt.induct psubstts.induct) simp_all

lemma subc_psubst: \<open>(\<forall>x \<in> params p. x \<noteq> c \<longrightarrow> f x \<noteq> f c) \<Longrightarrow>
    psubst f (subc c s p) = subc (f c) (psubstt f s) (psubst f p)\<close>
  by (induct p arbitrary: s) simp_all

lemma subcs_psubst: \<open>(\<forall>x \<in> (\<Union>p \<in> set z. params p). x \<noteq> c \<longrightarrow> f x \<noteq> f c) \<Longrightarrow>
    map (psubst f) (subcs c s z) = subcs (f c) (psubstt f s) (map (psubst f) z)\<close>
  by (induct z) (simp_all add: subc_psubst)

lemma new_lift:
  \<open>new_term c t \<Longrightarrow> new_term c (liftt t)\<close>
  \<open>new_list c l \<Longrightarrow> new_list c (liftts l)\<close>
  by (induct t and l rule: liftt.induct liftts.induct) simp_all

lemma new_subc' [simp]:
  \<open>new_term d s \<Longrightarrow> new_term d t \<Longrightarrow> new_term d (subc_term c s t)\<close>
  \<open>new_term d s \<Longrightarrow> new_list d l \<Longrightarrow> new_list d (subc_list c s l)\<close>
  by (induct t and l rule: substt.induct substts.induct) simp_all

lemma new_subc [simp]: \<open>new_term d s \<Longrightarrow> new d p \<Longrightarrow> new d (subc c s p)\<close>
  by (induct p arbitrary: s) simp_all

lemma news_subcs: \<open>new_term d s \<Longrightarrow> news d z \<Longrightarrow> news d (subcs c s z)\<close>
  by (induct z) simp_all

lemma psubst_new_free':
  \<open>c \<noteq> n \<Longrightarrow> new_term n (psubstt (id(n := c)) t)\<close>
  \<open>c \<noteq> n \<Longrightarrow> new_list n (psubstts (id(n := c)) l)\<close>
  by (induct t and l rule: paramst.induct paramsts.induct) simp_all

lemma psubst_new_free: \<open>c \<noteq> n \<Longrightarrow> new n (psubst (id(n := c)) p)\<close>
  using psubst_new_free' by (induct p) fastforce+

lemma map_psubst_new_free: \<open>c \<noteq> n \<Longrightarrow> news n (map (psubst (id(n := c))) z)\<close>
  using psubst_new_free by (induct z) fastforce+

lemma psubst_new_away' [simp]:
  \<open>new_term fresh t \<Longrightarrow> psubstt (id(fresh := c)) (psubstt (id(c := fresh)) t) = t\<close>
  \<open>new_list fresh l \<Longrightarrow> psubstts (id(fresh := c)) (psubstts (id(c := fresh)) l) = l\<close>
  by (induct t and l rule: psubstt.induct psubstts.induct) auto

lemma psubst_new_away [simp]: \<open>new fresh p \<Longrightarrow> psubst (id(fresh := c)) (psubst (id(c := fresh)) p) = p\<close>
  by (induct p) simp_all

lemma map_psubst_new_away:
  \<open>news fresh z \<Longrightarrow> map (psubst (id(fresh := c))) (map (psubst (id(c := fresh))) z) = z\<close>
  by (induct z) simp_all

lemma psubst_new':
  \<open>new_term c t \<Longrightarrow> psubstt (id(c := x)) t = t\<close>
  \<open>new_list c l \<Longrightarrow> psubstts (id(c := x)) l = l\<close>
  by (induct t and l rule: psubstt.induct psubstts.induct) auto

lemma psubst_new: \<open>new c p \<Longrightarrow> psubst (id(c := x)) p = p\<close>
  using psubst_new' by (induct p) fastforce+

lemma map_psubst_new: \<open>news c z \<Longrightarrow> map (psubst (id(c := x))) z = z\<close>
  using psubst_new by (induct z) auto

lemma lift_subst [simp]:
  \<open>liftt (substt t u m) = substt (liftt t) (liftt u) (m + 1)\<close>
  \<open>liftts (substts l u m) = substts (liftts l) (liftt u) (m + 1)\<close>
  by (induct t and l rule: substt.induct substts.induct) simp_all

lemma new_subc_same' [simp]:
  \<open>new_term c s \<Longrightarrow> new_term c (subc_term c s t)\<close>
  \<open>new_term c s \<Longrightarrow> new_list c (subc_list c s l)\<close>
  by (induct t and l rule: subc_term.induct subc_list.induct) simp_all

lemma new_subc_same: \<open>new_term c s \<Longrightarrow> new c (subc c s p)\<close>
  by (induct p arbitrary: s) simp_all

lemma lift_subc:
  \<open>liftt (subc_term c s t) = subc_term c (liftt s) (liftt t)\<close>
  \<open>liftts (subc_list c s l) = subc_list c (liftt s) (liftts l)\<close>
  by (induct t and l rule: liftt.induct liftts.induct) simp_all

lemma new_subc_put':
  \<open>new_term c s \<Longrightarrow> subc_term c s (substt t u m) = subc_term c s (substt t (subc_term c s u) m)\<close>
  \<open>new_term c s \<Longrightarrow> subc_list c s (substts l u m) = subc_list c s (substts l (subc_term c s u) m)\<close>
  by (induct t and l rule: subc_term.induct subc_list.induct) simp_all

lemma new_subc_put:
  \<open>new_term c s \<Longrightarrow> subc c s (subst p t m) = subc c s (subst p (subc_term c s t) m)\<close>
proof (induct p arbitrary: s m t)
  case FF
  then show ?case
    by simp
next
  case TT
  then show ?case
    by simp
next
  case (Pred i l)
  then show ?case
    using new_subc_put' by fastforce
next
  case (Neg p)
  then show ?case
    by (metis subc.simps(4) subst.simps(7))
next
  case (Impl p q)
  then show ?case
    by (metis subc.simps(5) subst.simps(6))
next
  case (Or p q)
  then show ?case
    by (metis subc.simps(6) subst.simps(5))
next
  case (And p q)
  then show ?case
    by (metis subc.simps(7) subst.simps(4))
next
  case (Exists p)
  have \<open>subc c s (subst (Exists p) (subc_term c s t) m) =
      Exists (subc c (liftt s) (subst p (subc_term c (liftt s) (liftt t)) (Suc m)))\<close>
    by (simp add: lift_subc)
  also have \<open>\<dots> = Exists (subc c (liftt s) (subst p (liftt t) (Suc m)))\<close>
    using Exists new_lift(1) by metis
  finally show ?case
    by simp
next
  case (Forall p)
  have \<open>subc c s (subst (Forall p) (subc_term c s t) m) =
      Forall (subc c (liftt s) (subst p (subc_term c (liftt s) (liftt t)) (Suc m)))\<close>
    by (simp add: lift_subc)
  also have \<open>\<dots> = Forall (subc c (liftt s) (subst p (liftt t) (Suc m)))\<close>
    using Forall new_lift(1) by metis
  finally show ?case
    by simp
qed

lemma subc_subst_new':
  \<open>new_term c u \<Longrightarrow> subc_term c (substt s u m) (substt t u m) = substt (subc_term c s t) u m\<close>
  \<open>new_term c u \<Longrightarrow> subc_list c (substt s u m) (substts l u m) = substts (subc_list c s l) u m\<close>
  by (induct t and l rule: subc_term.induct subc_list.induct) simp_all

lemma subc_subst_new:
  \<open>new_term c t \<Longrightarrow> subc c (substt s t m) (subst p t m) = subst (subc c s p) t m\<close>
  using subc_subst_new' by (induct p arbitrary: m t s) fastforce+

lemma subc_sub_0_new [simp]:
  \<open>new_term c t \<Longrightarrow> subc c s (subst p t 0) = subst (subc c (liftt s) p) t 0\<close>
  using subc_subst_new subst_0_lift(1) by metis

lemma member_subc: \<open>p \<in> set z \<Longrightarrow> subc c s p \<in> set (subcs c s z)\<close>
  by (induct z) auto

lemma deriv_subc:
  fixes p :: \<open>('a, 'b) form\<close>
  assumes inf_params: \<open>infinite (UNIV :: 'a set)\<close>
  shows \<open>z \<turnstile> p \<Longrightarrow> subcs c s z \<turnstile> subc c s p\<close>
proof (induct z p arbitrary: c s rule: deriv.induct)
  case (Assum p z)
  then show ?case
    using member_subc deriv.Assum by fast
next
  case TTI
  then show ?case
    using deriv.TTI by simp
  case FFE
  then show ?case
    using deriv.FFE by auto
next
  case (NegI z p)
  then show ?case
    using deriv.NegI by auto
next
  case (NegE z p)
  then show ?case
    using deriv.NegE by fastforce
next
  case (Class p z)
  then show ?case
    using deriv.Class by auto
next
  case (ImplE z p q)
  then show ?case
    using deriv.ImplE by fastforce
next
  case (ImplI z q p)
  then show ?case
    using deriv.ImplI by fastforce
next
  case (OrE z p q r)
  then show ?case
    using deriv.OrE by fastforce
next
  case (OrI1 z p q)
  then show ?case
    using deriv.OrI1 by fastforce
next
  case (OrI2 z q p)
  then show ?case
    using deriv.OrI2 by fastforce
next
  case (AndE1 z p q)
  then show ?case
    using deriv.AndE1 by fastforce
next
  case (AndE2 z p q)
  then show ?case
    using deriv.AndE2 by fastforce
next
  case (AndI p z q)
  then show ?case
    using deriv.AndI by fastforce
next
  case (ExistsE z p d q)
  then show ?case
  proof (cases \<open>c = d\<close>)
    case True
    then have \<open>z \<turnstile> q\<close>
      using ExistsE deriv.ExistsE by fast
    moreover have \<open>new c q\<close> and \<open>news c z\<close>
      using ExistsE True by simp_all
    ultimately show ?thesis
      using subc_new subcs_news by metis
  next
    case False
    let ?params = \<open>params p \<union> params q \<union> (\<Union>p \<in> set z. params p) \<union> paramst s \<union> {c} \<union> {d}\<close>

    have \<open>finite ?params\<close>
      by simp
    then obtain fresh where fresh: \<open>fresh \<notin> ?params\<close>
      using inf_params by (meson ex_new_if_finite infinite_UNIV_listI)

    let ?s = \<open>psubstt (id(d := fresh)) s\<close>
    let ?f = \<open>id(d := fresh, fresh := d)\<close>

    have f: \<open>\<forall>x \<in> ?params. x \<noteq> c \<longrightarrow> ?f x \<noteq> ?f c\<close>
      using fresh by simp

    have \<open>new_term d ?s\<close>
      using fresh psubst_new_free'(1) by fast
    then have \<open>psubstt ?f ?s = psubstt (id(fresh := d)) ?s\<close>
      by (metis fun_upd_twist psubstt_upd(1))
    then have psubst_s: \<open>psubstt ?f ?s = s\<close>
      using fresh by simp

    have \<open>?f c = c\<close> and \<open>new_term (?f c) (App fresh [])\<close>
      using False fresh by auto

    have \<open>subcs c (psubstt ?f ?s) z \<turnstile> subc c (psubstt ?f ?s) (Exists p)\<close>
      using ExistsE by blast
    then have exi_p:
      \<open>subcs c s z \<turnstile> Exists (subc c (liftt (psubstt ?f ?s)) p)\<close>
      using psubst_s by simp

    have \<open>news d z\<close>
      using ExistsE by simp
    moreover have \<open>news fresh z\<close>
      using fresh by (induct z) simp_all
    ultimately have \<open>map (psubst ?f) z = z\<close>
      by (induct z) simp_all
    moreover have \<open>\<forall>x \<in> \<Union>p \<in> set z. params p. x \<noteq> c \<longrightarrow> ?f x \<noteq> ?f c\<close>
      by auto
    ultimately have psubst_z: \<open>map (psubst ?f) (subcs c ?s z) = subcs c s z\<close>
      using \<open>?f c = c\<close> psubst_s by (simp add: subcs_psubst)

    have \<open>psubst ?f (subc c ?s (subst p (App d []) 0)) =
        subc (?f c) (psubstt ?f ?s) (psubst ?f (subst p (App d []) 0))\<close>
      using fresh by (simp add: subc_psubst)
    also have \<open>\<dots> = subc c s (subst (psubst ?f p) (App fresh []) 0)\<close>
      using psubst_subst psubst_s \<open>?f c = c\<close> by simp
    also have \<open>\<dots> = subc c s (subst p (App fresh []) 0)\<close>
      using ExistsE fresh by simp
    finally have psubst_p: \<open>psubst ?f (subc c ?s (subst p (App d []) 0)) =
        subst (subc c (liftt s) p) (App fresh []) 0\<close>
      using subc_sub_0_new \<open>new_term (?f c) (App fresh [])\<close> \<open>?f c = c\<close> by metis

    have \<open>\<forall>x \<in> params q. x \<noteq> c \<longrightarrow> ?f x \<noteq> ?f c\<close>
      using f by blast
    then have psubst_q: \<open>psubst ?f (subc c ?s q) = subc c s q\<close>
      using ExistsE fresh \<open>?f c = c\<close> psubst_s f by (simp add: subc_psubst)

    have \<open>subcs c ?s (subst p (App d []) 0 # z) \<turnstile> subc c ?s q\<close>
      using ExistsE by blast
    then have \<open>subc c ?s (subst p (App d []) 0) # subcs c ?s z \<turnstile> subc c ?s q\<close>
      by simp
    then have \<open>psubst ?f (subc c ?s (subst p (App d []) 0)) # map (psubst ?f) (subcs c ?s z)
        \<turnstile> psubst ?f (subc c ?s q)\<close>
      using deriv_psubst inf_params by fastforce
    then have q: \<open>subst (subc c (liftt s) p) (App fresh []) 0 # subcs c s z \<turnstile> subc c s q\<close>
      using psubst_q psubst_z psubst_p by simp

    have \<open>new fresh (subc c (liftt s) p)\<close>
      using fresh new_subc new_lift by simp
    moreover have \<open>new fresh (subc c s q)\<close>
      using fresh new_subc by simp
    moreover have \<open>news fresh (subcs c s z)\<close>
      using fresh \<open>news fresh z\<close> by (simp add: news_subcs)
    ultimately show \<open>subcs c s z \<turnstile> subc c s q\<close>
      using deriv.ExistsE exi_p q psubst_s by metis
  qed
next
  case (ExistsI z p t)
  let ?params = \<open>params p \<union> (\<Union>p \<in> set z. params p) \<union> paramst s \<union> paramst t \<union> {c}\<close>

  have \<open>finite ?params\<close>
    by simp
  then obtain fresh where fresh: \<open>fresh \<notin> ?params\<close>
    using inf_params by (meson ex_new_if_finite infinite_UNIV_listI)

  let ?f = \<open>id(c := fresh)\<close>
  let ?g = \<open>id(fresh := c)\<close>
  let ?s = \<open>psubstt ?f s\<close>

  have c: \<open>?g c = c\<close>
    using fresh by simp
  have s: \<open>psubstt ?g ?s = s\<close>
    using fresh by simp
  have p: \<open>psubst ?g (Exists p) = Exists p\<close>
    using fresh by simp

  have \<open>\<forall>x \<in> (\<Union>p \<in> set z. params p). x \<noteq> c \<longrightarrow> ?g x \<noteq> ?g c\<close>
    using fresh by auto
  moreover have \<open>map (psubst ?g) z = z\<close>
    using fresh by (induct z) simp_all
  ultimately have z: \<open>map (psubst ?g) (subcs c ?s z) = subcs c s z\<close>
    using s by (simp add: subcs_psubst)

  have \<open>new_term c ?s\<close>
    using fresh psubst_new_free' by fast
  then have \<open>subcs c ?s z \<turnstile> subc c ?s (subst p (subc_term c ?s t) 0)\<close>
    using ExistsI new_subc_put by metis
  moreover have \<open>new_term c (subc_term c ?s t)\<close>
    using \<open>new_term c ?s\<close> new_subc_same' by fast
  ultimately have \<open>subcs c ?s z \<turnstile> subst (subc c (liftt ?s) p) (subc_term c ?s t) 0\<close>
    using subc_sub_0_new by metis

  then have \<open>subcs c ?s z \<turnstile> subc c ?s (Exists p)\<close>
    using deriv.ExistsI by simp
  then have \<open>map (psubst ?g) (subcs c ?s z) \<turnstile> psubst ?g (subc c ?s (Exists p))\<close>
    using deriv_psubst inf_params by blast
  moreover have \<open>\<forall>x \<in> params (Exists p). x \<noteq> c \<longrightarrow> ?g x \<noteq> ?g c\<close>
    using fresh by auto
  ultimately show \<open>subcs c s z \<turnstile> subc c s (Exists p)\<close>
    using c s p z by (simp add: subc_psubst)
next
  case (ForallE z p t)
  let ?params = \<open>params p \<union> (\<Union>p \<in> set z. params p) \<union> paramst s \<union> paramst t \<union> {c}\<close>

  have \<open>finite ?params\<close>
    by simp
  then obtain fresh where fresh: \<open>fresh \<notin> ?params\<close>
    using inf_params by (meson ex_new_if_finite infinite_UNIV_listI)

  let ?f = \<open>id(c := fresh)\<close>
  let ?g = \<open>id(fresh := c)\<close>
  let ?s = \<open>psubstt ?f s\<close>

  have c: \<open>?g c = c\<close>
    using fresh by simp
  have s: \<open>psubstt ?g ?s = s\<close>
    using fresh by simp
  have p: \<open>psubst ?g (subst p t 0) = subst p t 0\<close>
    using fresh psubst_new psubst_subst subst_new psubst_new'(1) by fastforce

  have \<open>\<forall>x \<in> (\<Union>p \<in> set z. params p). x \<noteq> c \<longrightarrow> ?g x \<noteq> ?g c\<close>
    using fresh by auto
  moreover have \<open>map (psubst ?g) z = z\<close>
    using fresh by (induct z) simp_all
  ultimately have z: \<open>map (psubst ?g) (subcs c ?s z) = subcs c s z\<close>
    using s by (simp add: subcs_psubst)

  have \<open>new_term c ?s\<close>
    using fresh psubst_new_free' by fastforce

  have \<open>subcs c ?s z \<turnstile> Forall (subc c (liftt ?s) p)\<close>
    using ForallE by simp
  then have \<open>subcs c ?s z \<turnstile> subst (subc c (liftt ?s) p) (subc_term c ?s t) 0\<close>
    using deriv.ForallE by blast
  moreover have \<open>new_term c (subc_term c ?s t)\<close>
    using \<open>new_term c ?s\<close> new_subc_same' by fast
  ultimately have \<open>subcs c ?s z \<turnstile> subc c ?s (subst p (subc_term c ?s t) 0)\<close>
    by simp
  then have \<open>subcs c ?s z \<turnstile> subc c ?s (subst p t 0)\<close>
    using new_subc_put \<open>new_term c ?s\<close> by metis
  then have \<open>map (psubst ?g) (subcs c ?s z) \<turnstile> psubst ?g (subc c ?s (subst p t 0))\<close>
    using deriv_psubst inf_params by blast
  moreover have \<open>\<forall>x \<in> params (subst p t 0). x \<noteq> c \<longrightarrow> ?g x \<noteq> ?g c\<close>
    using fresh p psubst_new_free by (metis fun_upd_apply id_apply)
  ultimately show \<open>subcs c s z \<turnstile> subc c s (subst p t 0)\<close>
    using c s p z by (simp add: subc_psubst)
next
  case (ForallI z p d)
  then show ?case
  proof (cases \<open>c = d\<close>)
    case True
    then have \<open>z \<turnstile> Forall p\<close>
      using ForallI deriv.ForallI by fast
    moreover have \<open>new c p\<close> and \<open>news c z\<close>
      using ForallI True by simp_all
    ultimately show ?thesis
      by (simp add: subcs_news)
  next
    case False
    let ?params = \<open>params p \<union> (\<Union>p \<in> set z. params p) \<union> paramst s \<union> {c} \<union> {d}\<close>

    have \<open>finite ?params\<close>
      by simp
    then obtain fresh where fresh: \<open>fresh \<notin> ?params\<close>
      using inf_params by (meson ex_new_if_finite infinite_UNIV_listI)

    let ?s = \<open>psubstt (id(d := fresh)) s\<close>
    let ?f = \<open>id(d := fresh, fresh := d)\<close>

    have f: \<open>\<forall>x \<in> ?params. x \<noteq> c \<longrightarrow> ?f x \<noteq> ?f c\<close>
      using fresh by simp

    have \<open>new_term d ?s\<close>
      using fresh psubst_new_free' by fastforce
    then have \<open>psubstt ?f ?s = psubstt (id(fresh := d)) ?s\<close>
      by (metis fun_upd_twist psubstt_upd(1))
    then have psubst_s: \<open>psubstt ?f ?s = s\<close>
      using fresh by simp

    have \<open>?f c = c\<close> and \<open>new_term c (App fresh [])\<close>
      using False fresh by auto

    have \<open>psubst ?f (subc c ?s (subst p (App d []) 0)) =
      subc (?f c) (psubstt ?f ?s) (psubst ?f (subst p (App d []) 0))\<close>
      by (simp add: subc_psubst)
    also have \<open>\<dots> = subc c s (subst (psubst ?f p) (App fresh []) 0)\<close>
      using \<open>?f c = c\<close> psubst_subst psubst_s by simp
    also have \<open>\<dots> = subc c s (subst p (App fresh []) 0)\<close>
      using ForallI fresh by simp
    finally have psubst_p: \<open>psubst ?f (subc c ?s (subst p (App d []) 0)) =
        subst (subc c (liftt s) p) (App fresh []) 0\<close>
      using subc_sub_0_new \<open>new_term c (App fresh [])\<close> by simp

    have \<open>news d z\<close>
      using ForallI by simp
    moreover have \<open>news fresh z\<close>
      using fresh by (induct z) simp_all
    ultimately have \<open>map (psubst ?f) z = z\<close>
      by (induct z) simp_all
    moreover have \<open>\<forall>x \<in> \<Union>p \<in> set z. params p. x \<noteq> c \<longrightarrow> ?f x \<noteq> ?f c\<close>
      by auto
    ultimately have psubst_z: \<open>map (psubst ?f) (subcs c ?s z) = subcs c s z\<close>
      using \<open>?f c = c\<close> psubst_s by (simp add: subcs_psubst)

    have \<open>subcs c ?s z \<turnstile> subc c ?s (subst p (App d []) 0)\<close>
      using ForallI by blast
    then have \<open>map (psubst ?f) (subcs c ?s z) \<turnstile> psubst ?f (subc c ?s (subst p (App d []) 0))\<close>
      using deriv_psubst inf_params by blast
    then have \<open>subcs c s z \<turnstile> psubst ?f (subc c ?s (subst p (App d []) 0))\<close>
      using psubst_z by simp
    then have sub_p: \<open>subcs c s z \<turnstile> subst (subc c (liftt s) p) (App fresh []) 0\<close>
      using psubst_p by simp

    have \<open>new_term fresh s\<close>
      using fresh by simp
    then have \<open>new_term fresh (liftt s)\<close>
      using new_lift by simp
    then have \<open>new fresh (subc c (liftt s) p)\<close>
      using fresh new_subc by simp
    moreover have \<open>news fresh (subcs c s z)\<close>
      using \<open>news fresh z\<close> \<open>new_term fresh s\<close> news_subcs by fast
    ultimately show \<open>subcs c s z \<turnstile> subc c s (Forall p)\<close>
      using deriv.ForallI sub_p by simp
  qed
qed

subsection \<open>Weakening assumptions\<close>

lemma psubst_new_subset:
  assumes \<open>set z \<subseteq> set z'\<close> \<open>c \<notin> (\<Union>p \<in> set z. params p)\<close>
  shows \<open>set z \<subseteq> set (map (psubst (id(c := n))) z')\<close>
  using assms by force

lemma subset_cons: \<open>set z \<subseteq> set z' \<Longrightarrow> set (p # z) \<subseteq> set (p # z')\<close>
  by auto

lemma weaken_assumptions:
  fixes p :: \<open>('a, 'b) form\<close>
  assumes inf_params: \<open>infinite (UNIV :: 'a set)\<close>
  shows \<open>z \<turnstile> p \<Longrightarrow> set z \<subseteq> set z' \<Longrightarrow> z' \<turnstile> p\<close>
proof (induct z p arbitrary: z' rule: deriv.induct)
  case (Assum p z)
  then show ?case
    using deriv.Assum by auto
next
  case TTI
  then show ?case
    using deriv.TTI by auto
next
  case FFE
  then show ?case
    using deriv.FFE by auto
next
  case (NegI p z)
  then show ?case
    using deriv.NegI subset_cons by metis
next
  case (NegE p z)
  then show ?case
    using deriv.NegE by metis
next
  case (Class z p)
  then show ?case
    using deriv.Class subset_cons by metis
next
  case (ImplE z p q)
  then show ?case
    using deriv.ImplE by blast
next
  case (ImplI z q p)
  then show ?case
    using deriv.ImplI subset_cons by metis
next
  case (OrE z p q z )
  then show ?case
    using deriv.OrE subset_cons by metis
next
  case (OrI1 z p q)
  then show ?case
    using deriv.OrI1 by blast
next
  case (OrI2 z q p)
  then show ?case
    using deriv.OrI2 by blast
next
  case (AndE1 z p q)
  then show ?case
    using deriv.AndE1 by blast
next
  case (AndE2 z p q)
  then show ?case
    using deriv.AndE2 by blast
next
  case (AndI z p q)
  then show ?case
    using deriv.AndI by blast
next
  case (ExistsE z p c q)
  let ?params = \<open>params p \<union> params q \<union> (\<Union>p \<in> set z'. params p) \<union> {c}\<close>

  have \<open>finite ?params\<close>
    by simp
  then obtain fresh where fresh: \<open>fresh \<notin> ?params\<close>
    using inf_params by (meson ex_new_if_finite List.finite_set infinite_UNIV_listI)

  let ?z' = \<open>map (psubst (id(c := fresh))) z'\<close>

  have \<open>news c z\<close>
    using ExistsE by simp
  then have \<open>set z \<subseteq> set ?z'\<close>
    using ExistsE psubst_new_subset by (simp add: Ball_set)
  then have \<open>?z' \<turnstile> Exists p\<close>
    using ExistsE by blast

  moreover have \<open>set (subst p (App c []) 0 # z) \<subseteq> set (subst p (App c []) 0 # ?z')\<close>
    using \<open>set z \<subseteq> set ?z'\<close> by auto
  then have \<open>subst p (App c []) 0 # ?z' \<turnstile> q\<close>
    using ExistsE by blast

  moreover have \<open>news c ?z'\<close>
    using fresh by (simp add: map_psubst_new_free)
  then have \<open>new c p\<close> \<open>new c q\<close> \<open>news c ?z'\<close>
    using ExistsE by simp_all

  ultimately have \<open>?z' \<turnstile> q\<close>
    using ExistsE deriv.ExistsE by metis

  then have \<open>map (psubst (id(fresh := c))) ?z' \<turnstile> psubst (id(fresh := c)) q\<close>
    using deriv_psubst inf_params by blast
  moreover have \<open>map (psubst (id(fresh := c))) ?z' = z'\<close>
    using fresh map_psubst_new_away Ball_set by fastforce
  moreover have \<open>psubst (id(fresh := c)) q = q\<close>
    using fresh by simp
  ultimately show \<open>z' \<turnstile> q\<close>
    by simp
next
  case (ExistsI z p t)
  then show ?case
    using deriv.ExistsI by blast
next
  case (ForallE p z t)
  then show ?case
    using deriv.ForallE by blast
next
  case (ForallI z p c)
  let ?params = \<open>params p \<union> (\<Union>p \<in> set z'. params p) \<union> {c}\<close>

  have \<open>finite ?params\<close>
    by simp
  then obtain fresh where fresh: \<open>fresh \<notin> ?params\<close>
    using inf_params by (meson ex_new_if_finite List.finite_set infinite_UNIV_listI)

  let ?z' = \<open>map (psubst (id(c := fresh))) z'\<close>

  have \<open>news c z\<close>
    using ForallI by simp
  then have \<open>set z \<subseteq> set ?z'\<close>
    using ForallI psubst_new_subset by (metis (no_types, lifting) Ball_set UN_iff)
  then have \<open>?z' \<turnstile> subst p (App c []) 0\<close>
    using ForallI by blast

  moreover have \<open>\<forall>p \<in> set ?z'. c \<notin> params p\<close>
    using fresh psubst_new_free by fastforce
  then have \<open>list_all (\<lambda>p. c \<notin> params p) (p # ?z')\<close>
    using ForallI by (simp add: list_all_iff)
  then have \<open>new c p\<close> \<open>news c ?z'\<close>
    by simp_all

  ultimately have \<open>?z' \<turnstile> Forall p\<close>
    using ForallI deriv.ForallI by fast

  then have \<open>map (psubst (id(fresh := c))) ?z' \<turnstile> psubst (id(fresh := c)) (Forall p)\<close>
    using deriv_psubst inf_params by blast
  moreover have \<open>map (psubst (id(fresh := c))) ?z' = z'\<close>
    using fresh map_psubst_new_away Ball_set by fastforce
  moreover have \<open>psubst (id(fresh := c)) (Forall p) = Forall p\<close>
    using fresh ForallI by simp
  ultimately show \<open>z' \<turnstile> Forall p\<close>
    by simp
qed

subsection \<open>Implications and assumptions\<close>

primrec put_imps :: \<open>('a, 'b) form \<Rightarrow> ('a, 'b) form list \<Rightarrow> ('a, 'b) form\<close> where
  \<open>put_imps p [] = p\<close> |
  \<open>put_imps p (q # z) = Impl q (put_imps p z)\<close>

lemma semantics_put_imps:
  \<open>(e,f,g,z \<Turnstile> p) = eval e f g (put_imps p z)\<close>
  unfolding model_def by (induct z) auto

lemma shift_imp_assum:
  fixes p :: \<open>('a, 'b) form\<close>
  assumes inf_params: \<open>infinite (UNIV :: 'a set)\<close>
    and \<open>z \<turnstile> Impl p q\<close>
  shows \<open>p # z \<turnstile> q\<close>
proof -
  have \<open>set z \<subseteq> set (p # z)\<close>
    by auto
  then have \<open>p # z \<turnstile> Impl p q\<close>
    using assms weaken_assumptions inf_params by blast
  moreover have \<open>p # z \<turnstile> p\<close>
    by (simp add: Assum)
  ultimately show \<open>p # z \<turnstile> q\<close>
    using ImplE by blast
qed

lemma remove_imps:
  assumes \<open>infinite (- params p)\<close>
  shows \<open>z' \<turnstile> put_imps p z \<Longrightarrow> rev z @ z' \<turnstile> p\<close>
  using assms shift_imp_assum by (induct z arbitrary: z') auto

subsection \<open>Closure elimination\<close>

lemma subc_sub_closed_var' [simp]:
  \<open>new_term c t \<Longrightarrow> closedt (Suc m) t \<Longrightarrow> subc_term c (Var m) (substt t (App c []) m) = t\<close>
  \<open>new_list c l \<Longrightarrow> closedts (Suc m) l \<Longrightarrow> subc_list c (Var m) (substts l (App c []) m) = l\<close>
  by (induct t and l rule: substt.induct substts.induct) auto

lemma subc_sub_closed_var [simp]: \<open>new c p \<Longrightarrow> closed (Suc m) p \<Longrightarrow>
    subc c (Var m) (subst p (App c []) m) = p\<close>
  by (induct p arbitrary: m) simp_all

primrec put_unis :: \<open>nat \<Rightarrow> ('a, 'b) form \<Rightarrow> ('a, 'b) form\<close> where
  \<open>put_unis 0 p = p\<close> |
  \<open>put_unis (Suc m) p = Forall (put_unis m p)\<close>

lemma sub_put_unis [simp]:
  \<open>subst (put_unis k p) (App c []) i = put_unis k (subst p (App c []) (i + k))\<close>
  by (induct k arbitrary: i) simp_all

lemma closed_put_unis [simp]: \<open>closed m (put_unis k p) = closed (m + k) p\<close>
  by (induct k arbitrary: m) simp_all

lemma valid_put_unis: \<open>\<forall>(e :: nat \<Rightarrow> 'a) f g. eval e f g p \<Longrightarrow>
    eval (e :: nat \<Rightarrow> 'a) f g (put_unis m p)\<close>
  by (induct m arbitrary: e) simp_all

lemma put_unis_collapse: \<open>put_unis m (put_unis n p) = put_unis (m + n) p\<close>
  by (induct m) simp_all

fun consts_for_unis :: \<open>('a, 'b) form \<Rightarrow> 'a list \<Rightarrow> ('a, 'b) form\<close> where
  \<open>consts_for_unis (Forall p) (c#cs) = consts_for_unis (subst p (App c []) 0) cs\<close> |
  \<open>consts_for_unis p _ = p\<close>

lemma consts_for_unis: \<open>[] \<turnstile> put_unis (length cs) p \<Longrightarrow>
  [] \<turnstile> consts_for_unis (put_unis (length cs) p) cs\<close>
proof (induct cs arbitrary: p)
  case (Cons c cs)
  then have \<open>[] \<turnstile> Forall (put_unis (length cs) p)\<close>
    by simp
  then have \<open>[] \<turnstile> subst (put_unis (length cs) p) (App c []) 0\<close>
    using ForallE by blast
  then show ?case
    using Cons by simp
qed simp

primrec vars_for_consts :: \<open>('a, 'b) form \<Rightarrow> 'a list \<Rightarrow> ('a, 'b) form\<close> where
  \<open>vars_for_consts p [] = p\<close> |
  \<open>vars_for_consts p (c # cs) = subc c (Var (length cs)) (vars_for_consts p cs)\<close>

lemma vars_for_consts:
  assumes \<open>infinite (- params p)\<close>
  shows \<open>[] \<turnstile> p \<Longrightarrow> [] \<turnstile> vars_for_consts p xs\<close>
  using assms deriv_subc by (induct xs arbitrary: p) fastforce+

lemma vars_for_consts_for_unis:
  \<open>closed (length cs) p \<Longrightarrow> list_all (\<lambda>c. new c p) cs \<Longrightarrow> distinct cs \<Longrightarrow>
   vars_for_consts (consts_for_unis (put_unis (length cs) p) cs) cs = p\<close>
  by (induct cs arbitrary: p) (simp_all add: subst_new_all)

lemma fresh_constant:
  fixes p :: \<open>('a, 'b) form\<close>
  assumes \<open>infinite (UNIV :: 'a set)\<close>
  shows \<open>\<exists>c. c \<notin> set cs \<and> new c p\<close>
proof -
  have \<open>finite (set cs \<union> params p)\<close>
    by simp
  then show ?thesis
    using assms ex_new_if_finite UnI1 UnI2 by metis
qed

lemma fresh_constants:
  fixes p :: \<open>('a, 'b) form\<close>
  assumes \<open>infinite (UNIV :: 'a set)\<close>
  shows \<open>\<exists>cs. length cs = m \<and> list_all (\<lambda>c. new c p) cs \<and> distinct cs\<close>
proof (induct m)
  case (Suc m)
  then obtain cs where \<open>length cs = m \<and> list_all (\<lambda>c. new c p) cs \<and> distinct cs\<close>
    by blast
  moreover obtain c where \<open>c \<notin> set cs \<and> new c p\<close>
    using Suc assms fresh_constant by blast
  ultimately have \<open>length (c # cs) = Suc m \<and> list_all (\<lambda>c. new c p) (c # cs) \<and> distinct (c # cs)\<close>
    by simp
  then show ?case
    by blast
qed simp

lemma closed_max:
  assumes \<open>closed m p\<close> \<open>closed n q\<close>
  shows \<open>closed (max m n) p \<and> closed (max m n) q\<close>
proof -
  have \<open>m \<le> max m n\<close> and \<open>n \<le> max m n\<close>
    by simp_all
  then show ?thesis
    using assms closed_mono by metis
qed

lemma ex_closed' [simp]:
  fixes t :: \<open>'a term\<close> and l :: \<open>'a term list\<close>
  shows \<open>\<exists>m. closedt m t\<close> \<open>\<exists>n. closedts n l\<close>
proof (induct t and l rule: closedt.induct closedts.induct)
  case (Cons_term t l)
  then obtain m and n where \<open>closedt m t\<close> and \<open>closedts n l\<close>
    by blast
  moreover have \<open>m \<le> max m n\<close> and \<open>n \<le> max m n\<close>
    by simp_all
  ultimately have \<open>closedt (max m n) t\<close> and \<open>closedts (max m n) l\<close>
    using closedt_mono by blast+
  then show ?case
    by auto
qed auto

lemma ex_closed [simp]: \<open>\<exists>m. closed m p\<close>
proof (induct p)
  case FF
  then show ?case
    by simp
next
  case TT
  then show ?case
    by simp
next
  case (Neg p)
  then show ?case
    by simp
next
  case (Impl p q)
  then show ?case
    using closed_max by fastforce
next
  case (Or p q)
  then show ?case
    using closed_max by fastforce
next
  case (And p q)
  then show ?case
    using closed_max by fastforce
next
  case (Exists p)
  then obtain m where \<open>closed m p\<close>
    by blast
  then have \<open>closed (Suc m) p\<close>
    using closed_mono Suc_n_not_le_n nat_le_linear by blast
  then show ?case
    by auto
next
  case (Forall p)
  then obtain m where \<open>closed m p\<close>
    by blast
  then have \<open>closed (Suc m) p\<close>
    using closed_mono Suc_n_not_le_n nat_le_linear by blast
  then show ?case
    by auto
qed simp_all

lemma ex_closure: \<open>\<exists>m. closed 0 (put_unis m p)\<close>
  by simp

lemma remove_unis_sentence:
  assumes inf_params: \<open>infinite (- params p)\<close>
    and \<open>closed 0 (put_unis m p)\<close> \<open>[] \<turnstile> put_unis m p\<close>
  shows \<open>[] \<turnstile> p\<close>
proof -
  obtain cs :: \<open>'a list\<close> where \<open>length cs = m\<close>
    and *: \<open>distinct cs\<close> and **: \<open>list_all (\<lambda>c. new c p) cs\<close>
    using assms finite_compl finite_params fresh_constants inf_params by metis
  then have \<open>[] \<turnstile> consts_for_unis (put_unis (length cs) p) cs\<close>
    using assms consts_for_unis by blast
  then have \<open>[] \<turnstile> vars_for_consts (consts_for_unis (put_unis (length cs) p) cs) cs\<close>
    using vars_for_consts inf_params by fastforce
  moreover have \<open>closed (length cs) p\<close>
    using assms \<open>length cs = m\<close> by simp
  ultimately show \<open>[] \<turnstile> p\<close>
    using vars_for_consts_for_unis * ** by metis
qed

subsection \<open>Completeness\<close>

theorem completeness:
  fixes p :: \<open>(nat, nat) form\<close>
  assumes \<open>\<forall>(e :: nat \<Rightarrow> nat hterm) f g. e, f, g, z \<Turnstile> p\<close>
  shows \<open>z \<turnstile> p\<close>
proof -
  let ?p = \<open>put_imps p (rev z)\<close>

  have *: \<open>\<forall>(e :: nat \<Rightarrow> nat hterm) f g. eval e f g ?p\<close>
    using assms semantics_put_imps unfolding model_def by fastforce
  obtain m where **: \<open>closed 0 (put_unis m ?p)\<close>
    using ex_closure by blast
  moreover have \<open>list_all (closed 0) []\<close>
    by simp
  moreover have \<open>\<forall>(e :: nat \<Rightarrow> nat hterm) f g. e, f, g, [] \<Turnstile> put_unis m ?p\<close>
    using * valid_put_unis unfolding model_def by blast
  ultimately have \<open>[] \<turnstile> put_unis m ?p\<close>
    using natded_complete by blast
  then have \<open>[] \<turnstile> ?p\<close>
    using ** remove_unis_sentence by fastforce
  then show \<open>z \<turnstile> p\<close>
    using remove_imps by fastforce
qed

abbreviation \<open>valid p \<equiv> \<forall>(e :: nat \<Rightarrow> nat hterm) f g. eval e f g p\<close>

proposition
  fixes p :: \<open>(nat, nat) form\<close>
  shows \<open>valid p \<Longrightarrow> eval e f g p\<close>
  using completeness correctness
  unfolding model_def by (metis list.pred_inject(1))

proposition
  fixes p :: \<open>(nat, nat) form\<close>
  shows \<open>([] \<turnstile> p) = valid p\<close>
  using completeness correctness
  unfolding model_def by fastforce

corollary \<open>\<forall>e (f::nat \<Rightarrow> nat hterm list \<Rightarrow> nat hterm) (g::nat \<Rightarrow> nat hterm list \<Rightarrow> bool).
    e,f,g,ps \<Turnstile> p \<Longrightarrow> ps \<turnstile> p\<close>
  by (rule completeness)

end
