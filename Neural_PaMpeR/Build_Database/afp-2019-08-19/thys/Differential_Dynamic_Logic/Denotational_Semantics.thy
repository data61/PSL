theory "Denotational_Semantics" 
imports
  Ordinary_Differential_Equations.ODE_Analysis
  "Lib"
  "Ids"
  "Syntax"
begin
subsection \<open>Denotational Semantics\<close>
text \<open>
  The canonical dynamic semantics of dL are given as a denotational semantics.
  The important definitions for the denotational semantics are states $\nu$,
  interpretations I and the semantic functions $[[\psi]]I$, $[[\theta]]I\nu$,
  $[[\alpha]]I$, which are represented by the Isabelle functions \verb|fml_sem|,
  \verb|dterm_sem| and \verb|prog_sem|, respectively.
  \<close>
subsection \<open>States\<close>
text \<open>We formalize a state S as a pair $(S_V, S_V') : R^n \times R^n $, where $S_V$ assigns
  values to the program variables and $S_V$' assigns values to their
  differentials. Function constants are also formalized as having a fixed arity
  m \verb|(Rvec_dim)| which may differ from n. If a function does not need to
  have m arguments, any remaining arguments can be uniformly set to 0,
  which simulates the affect of having functions of less arguments.
  
  Most semantic proofs need to reason about states agreeing on variables.
  We say Vagree A B V if states A and B have the same values on all variables in V,
  similarly with VSagree A B V for simple states A and B and Iagree I J V for interpretations
  I and J.
  \<close>

\<comment> \<open>Vector of reals of length \<open>'a\<close>\<close>
type_synonym 'a Rvec = "real^('a::finite)"
\<comment> \<open>A state specifies one vector of values for unprimed variables \<open>x\<close> and a second vector for \<open>x'\<close>\<close>
type_synonym 'a state = "'a Rvec \<times> 'a Rvec"
\<comment> \<open>\<open>'a simple_state\<close> is half a state - either the \<open>x\<close>s or the \<open>x'\<close>s\<close>
type_synonym 'a simple_state = "'a Rvec"

definition Vagree :: "'c::finite state \<Rightarrow> 'c state \<Rightarrow> ('c + 'c) set \<Rightarrow> bool"
where "Vagree \<nu> \<nu>' V \<equiv>
   (\<forall>i. Inl i \<in> V \<longrightarrow> fst \<nu> $ i = fst \<nu>' $ i)
 \<and> (\<forall>i. Inr i \<in> V \<longrightarrow> snd \<nu> $ i = snd \<nu>' $ i)"

definition VSagree :: "'c::finite simple_state \<Rightarrow> 'c simple_state \<Rightarrow> 'c set \<Rightarrow> bool"
where "VSagree \<nu> \<nu>' V \<longleftrightarrow> (\<forall>i \<in> V. (\<nu> $ i) = (\<nu>' $ i))"

\<comment> \<open>Agreement lemmas\<close>
lemma agree_nil:"Vagree \<nu> \<omega> {}"
  by (auto simp add: Vagree_def)

lemma agree_supset:"A \<supseteq> B \<Longrightarrow> Vagree \<nu> \<nu>' A \<Longrightarrow> Vagree \<nu> \<nu>' B"
  by (auto simp add: Vagree_def)

lemma VSagree_nil:"VSagree \<nu> \<omega> {}"
  by (auto simp add: VSagree_def)

lemma VSagree_supset:"A \<supseteq> B \<Longrightarrow> VSagree \<nu> \<nu>' A \<Longrightarrow> VSagree \<nu> \<nu>' B"
  by (auto simp add: VSagree_def)

lemma VSagree_UNIV_eq:"VSagree A B UNIV \<Longrightarrow> A = B"
  unfolding VSagree_def by (auto simp add: vec_eq_iff)

lemma agree_comm:"\<And>A B V. Vagree A B V \<Longrightarrow> Vagree B A V" unfolding Vagree_def by auto

lemma agree_sub:"\<And>\<nu> \<omega> A B . A \<subseteq> B \<Longrightarrow> Vagree \<nu> \<omega> B \<Longrightarrow> Vagree \<nu> \<omega> A"
  unfolding Vagree_def by auto

lemma agree_UNIV_eq:"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> UNIV \<Longrightarrow> \<nu> = \<omega>"
  unfolding Vagree_def by (auto simp add: vec_eq_iff)

lemma agree_UNIV_fst:"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (Inl ` UNIV) \<Longrightarrow> (fst \<nu>) = (fst \<omega>)"
  unfolding Vagree_def by (auto simp add: vec_eq_iff)

lemma agree_UNIV_snd:"\<And>\<nu> \<omega>. Vagree \<nu> \<omega> (Inr ` UNIV) \<Longrightarrow> (snd \<nu>) = (snd \<omega>)"
  unfolding Vagree_def by (auto simp add: vec_eq_iff)

lemma Vagree_univ:"\<And>a b c d. Vagree (a,b) (c,d) UNIV \<Longrightarrow> a = c \<and> b = d"
  by (auto simp add: Vagree_def vec_eq_iff)

lemma agree_union:"\<And>\<nu> \<omega> A B. Vagree \<nu> \<omega> A \<Longrightarrow> Vagree \<nu> \<omega> B \<Longrightarrow> Vagree \<nu> \<omega> (A \<union> B)"
  unfolding Vagree_def by (auto simp add: vec_eq_iff)

lemma agree_trans:"Vagree \<nu> \<mu> A \<Longrightarrow> Vagree \<mu> \<omega> B \<Longrightarrow> Vagree \<nu> \<omega> (A \<inter> B)"
  by (auto simp add: Vagree_def)

lemma agree_refl:"Vagree \<nu> \<nu> A"
  by (auto simp add: Vagree_def)

lemma VSagree_sub:"\<And>\<nu> \<omega> A B . A \<subseteq> B \<Longrightarrow> VSagree \<nu> \<omega> B \<Longrightarrow> VSagree \<nu> \<omega> A"
  unfolding VSagree_def by auto

lemma VSagree_refl:"VSagree \<nu> \<nu> A"
  by (auto simp add: VSagree_def)

subsection Interpretations
text\<open>
    For convenience we pretend interpretations contain an extra field called
  FunctionFrechet specifying the Frechet derivative \verb|(FunctionFrechet f \<nu>)| : $R^m \rightarrow R$ 
  for every function in every state. The proposition \verb|(is_interp I)| says that such a
  derivative actually exists and is continuous (i.e. all functions are C1-continuous)
  without saying what the exact derivative is.
  
  The type parameters 'a, 'b, 'c are finite types whose cardinalities indicate the maximum number 
  of functions, contexts, and <everything else defined by the interpretation>, respectively.
\<close>
record ('a, 'b, 'c) interp =
  Functions       :: "'a \<Rightarrow> 'c Rvec \<Rightarrow> real"
  Predicates      :: "'c \<Rightarrow> 'c Rvec \<Rightarrow> bool"
  Contexts        :: "'b \<Rightarrow> 'c state set \<Rightarrow> 'c state set"
  Programs        :: "'c \<Rightarrow> ('c state * 'c state) set"
  ODEs            :: "'c \<Rightarrow> 'c simple_state \<Rightarrow> 'c simple_state"
  ODEBV           :: "'c \<Rightarrow> 'c set"

fun FunctionFrechet :: "('a::finite, 'b::finite, 'c::finite) interp \<Rightarrow> 'a \<Rightarrow> 'c Rvec \<Rightarrow> 'c Rvec \<Rightarrow> real"
  where "FunctionFrechet I i = (THE f'. \<forall> x. (Functions I i has_derivative f' x) (at x))"

\<comment> \<open>For an interpretation to be valid, all functions must be differentiable everywhere.\<close>
definition is_interp :: "('a::finite, 'b::finite, 'c::finite) interp \<Rightarrow> bool"
  where "is_interp I \<equiv>
   \<forall>x. \<forall>i. ((FDERIV (Functions I i) x :> (FunctionFrechet I i x)) \<and> continuous_on UNIV (\<lambda>x. Blinfun (FunctionFrechet I i x)))"

lemma is_interpD:"is_interp I \<Longrightarrow> \<forall>x. \<forall>i. (FDERIV (Functions I i) x :> (FunctionFrechet I i x))"
  unfolding is_interp_def by auto
  
\<comment> \<open>Agreement between interpretations.\<close>
definition Iagree :: "('a::finite, 'b::finite, 'c::finite) interp \<Rightarrow> ('a::finite, 'b::finite, 'c::finite) interp \<Rightarrow> ('a + 'b + 'c) set \<Rightarrow> bool"
where "Iagree I J V \<equiv>
  (\<forall>i\<in>V.
    (\<forall>x. i = Inl x \<longrightarrow> Functions I x = Functions J x) \<and>
    (\<forall>x. i = Inr (Inl x) \<longrightarrow> Contexts I x = Contexts J x) \<and>
    (\<forall>x. i = Inr (Inr x) \<longrightarrow> Predicates I x = Predicates J x) \<and>
    (\<forall>x. i = Inr (Inr x) \<longrightarrow> Programs I x = Programs J x) \<and>
    (\<forall>x. i = Inr (Inr x) \<longrightarrow> ODEs I x = ODEs J x) \<and>
    (\<forall>x. i = Inr (Inr x) \<longrightarrow> ODEBV I x = ODEBV J x))"

lemma Iagree_Func:"Iagree I J V \<Longrightarrow> Inl f \<in> V \<Longrightarrow> Functions I f = Functions J f"
  unfolding Iagree_def by auto

lemma Iagree_Contexts:"Iagree I J V \<Longrightarrow> Inr (Inl C) \<in> V \<Longrightarrow> Contexts I C = Contexts J C"
  unfolding Iagree_def by auto

lemma Iagree_Pred:"Iagree I J V \<Longrightarrow> Inr (Inr p) \<in> V \<Longrightarrow> Predicates I p = Predicates J p"
  unfolding Iagree_def by auto

lemma Iagree_Prog:"Iagree I J V \<Longrightarrow> Inr (Inr a) \<in> V \<Longrightarrow> Programs I a = Programs J a"
  unfolding Iagree_def by auto

lemma Iagree_ODE:"Iagree I J V \<Longrightarrow> Inr (Inr a) \<in> V \<Longrightarrow> ODEs I a = ODEs J a"
  unfolding Iagree_def by auto  

lemma Iagree_comm:"\<And>A B V. Iagree A B V \<Longrightarrow> Iagree B A V" 
  unfolding Iagree_def by auto

lemma Iagree_sub:"\<And>I J A B . A \<subseteq> B \<Longrightarrow> Iagree I J B \<Longrightarrow> Iagree I J A"
  unfolding Iagree_def by auto

lemma Iagree_refl:"Iagree I I A"
  by (auto simp add: Iagree_def)

\<comment> \<open>Semantics for differential-free terms. Because there are no differentials, depends only on the \<open>x\<close> variables\<close>
\<comment> \<open>and not the \<open>x'\<close> variables.\<close>
primrec sterm_sem :: "('a::finite, 'b::finite, 'c::finite) interp \<Rightarrow> ('a, 'c) trm \<Rightarrow> 'c simple_state \<Rightarrow> real"
where
  "sterm_sem I (Var x) v = v $ x"
| "sterm_sem I (Function f args) v = Functions I f (\<chi> i. sterm_sem I (args i) v)"
| "sterm_sem I (Plus t1 t2) v = sterm_sem I t1 v + sterm_sem I t2 v"
| "sterm_sem I (Times t1 t2) v = sterm_sem I t1 v * sterm_sem I t2 v"
| "sterm_sem I (Const r) v = r"
| "sterm_sem I ($' c) v = undefined"
| "sterm_sem I (Differential d) v = undefined"
  
\<comment> \<open>\<open>frechet I \<theta> \<nu>\<close> syntactically computes the frechet derivative of the term \<open>\<theta>\<close> in the interpretation\<close>
\<comment> \<open>\<open>I\<close> at state \<open>\<nu>\<close> (containing only the unprimed variables). The frechet derivative is a\<close>
\<comment> \<open>linear map from the differential state \<open>\<nu>\<close> to reals.\<close>
primrec frechet :: "('a::finite, 'b::finite, 'c::finite) interp \<Rightarrow> ('a, 'c) trm \<Rightarrow> 'c simple_state \<Rightarrow> 'c simple_state \<Rightarrow> real"
where
  "frechet I (Var x) v = (\<lambda>v'. v' \<bullet> axis x 1)"
| "frechet I (Function f args) v =
    (\<lambda>v'. FunctionFrechet I f (\<chi> i. sterm_sem I (args i) v) (\<chi> i. frechet I (args i) v v'))"
| "frechet I (Plus t1 t2) v = (\<lambda>v'. frechet I t1 v v' + frechet I t2 v v')"
| "frechet I (Times t1 t2) v =
    (\<lambda>v'. sterm_sem I t1 v * frechet I t2 v v' + frechet I t1 v v' * sterm_sem I t2 v)"
| "frechet I (Const r) v = (\<lambda>v'. 0)"
| "frechet I ($' c) v = undefined"
| "frechet I (Differential d) v = undefined"

definition directional_derivative :: "('a::finite, 'b::finite, 'c::finite) interp \<Rightarrow> ('a, 'c) trm \<Rightarrow> 'c state \<Rightarrow> real"
where "directional_derivative I t = (\<lambda>v. frechet I t (fst v) (snd v))"

\<comment> \<open>Sem for terms that are allowed to contain differentials.\<close>
\<comment> \<open>Note there is some duplication with \<open>sterm_sem\<close>.\<close>
primrec dterm_sem :: "('a::finite, 'b::finite, 'c::finite) interp \<Rightarrow> ('a, 'c) trm \<Rightarrow> 'c state \<Rightarrow> real"
where
  "dterm_sem I (Var x) = (\<lambda>v. fst v $ x)"
| "dterm_sem I (DiffVar x) = (\<lambda>v. snd v $ x)"
| "dterm_sem I (Function f args) = (\<lambda>v. Functions I f (\<chi> i. dterm_sem I (args i) v))"
| "dterm_sem I (Plus t1 t2) = (\<lambda>v. (dterm_sem I t1 v) + (dterm_sem I t2 v))"
| "dterm_sem I (Times t1 t2) = (\<lambda>v. (dterm_sem I t1 v) * (dterm_sem I t2 v))"
| "dterm_sem I (Differential t) = (\<lambda>v. directional_derivative I t v)"
| "dterm_sem I (Const c) = (\<lambda>v. c)"

text\<open> The semantics of an ODE is the vector field at a given point. ODE's are all time-independent
  so no time variable is necessary. Terms on the RHS of an ODE must be differential-free, so
  depends only on the xs.

  The safety predicate \texttt{osafe} ensures the domains of ODE1 and ODE2 are disjoint, so vector addition
  is equivalent to saying "take things defined from ODE1 from ODE1, take things defined
  by ODE2 from ODE2"\<close>
fun ODE_sem:: "('a::finite, 'b::finite, 'c::finite) interp \<Rightarrow> ('a, 'c) ODE \<Rightarrow> 'c Rvec \<Rightarrow> 'c Rvec"
  where
  ODE_sem_OVar:"ODE_sem I (OVar x) = ODEs I x"
| ODE_sem_OSing:"ODE_sem I (OSing x \<theta>) =  (\<lambda>\<nu>. (\<chi> i. if i = x then sterm_sem I \<theta> \<nu> else 0))"
\<comment> \<open>Note: Could define using \<open>SOME\<close> operator in a way that more closely matches above description,\<close>
\<comment> \<open>but that gets complicated in the \<open>OVar\<close> case because not all variables are bound by the \<open>OVar\<close>\<close>
| ODE_sem_OProd:"ODE_sem I (OProd ODE1 ODE2) = (\<lambda>\<nu>. ODE_sem I ODE1 \<nu> + ODE_sem I ODE2 \<nu>)"

\<comment> \<open>The bound variables of an ODE\<close>
fun ODE_vars :: "('a,'b,'c) interp \<Rightarrow> ('a, 'c) ODE \<Rightarrow> 'c set"
  where 
  "ODE_vars I (OVar c) = ODEBV I c"
| "ODE_vars I (OSing x \<theta>) = {x}"
| "ODE_vars I (OProd ODE1 ODE2) = ODE_vars I ODE1 \<union> ODE_vars I ODE2"
  
fun semBV ::"('a, 'b,'c) interp \<Rightarrow> ('a, 'c) ODE \<Rightarrow> ('c + 'c) set"
  where "semBV I ODE = Inl ` (ODE_vars I ODE) \<union> Inr ` (ODE_vars I ODE)"

lemma ODE_vars_lr:
  fixes x::"'sz" and ODE::"('sf,'sz) ODE" and I::"('sf,'sc,'sz) interp"
  shows "Inl x \<in> semBV I ODE \<longleftrightarrow> Inr x \<in> semBV I ODE"
  by (induction "ODE", auto)

fun mk_xode::"('a::finite, 'b::finite, 'c::finite) interp \<Rightarrow> ('a::finite, 'c::finite) ODE \<Rightarrow> 'c::finite simple_state \<Rightarrow> 'c::finite state"
where "mk_xode I ODE sol = (sol, ODE_sem I ODE sol)"
 
text\<open> Given an initial state $\nu$ and solution to an ODE at some point, construct the resulting state $\omega$.
  This is defined using the SOME operator because the concrete definition is unwieldy. \<close>
definition mk_v::"('a::finite, 'b::finite, 'c::finite) interp \<Rightarrow> ('a::finite, 'c::finite) ODE \<Rightarrow> 'c::finite state \<Rightarrow> 'c::finite simple_state \<Rightarrow> 'c::finite state"
where "mk_v I ODE \<nu> sol = (THE \<omega>. 
  Vagree \<omega> \<nu> (- semBV I ODE) 
\<and> Vagree \<omega> (mk_xode I ODE sol) (semBV I ODE))"

\<comment> \<open>\<open>repv \<nu> x r\<close> replaces the value of (unprimed) variable \<open>x\<close> in the state \<open>\<nu>\<close> with r\<close>
fun repv :: "'c::finite state \<Rightarrow> 'c \<Rightarrow> real \<Rightarrow> 'c state"
where "repv v x r = ((\<chi> y. if x = y then r else vec_nth (fst v) y), snd v)"

\<comment> \<open>\<open>repd \<nu> x' r\<close> replaces the value of (primed) variable \<open>x'\<close> in the state \<open>\<nu>\<close> with \<open>r\<close>\<close>
fun repd :: "'c::finite state \<Rightarrow> 'c \<Rightarrow> real \<Rightarrow> 'c state"
where "repd v x r = (fst v, (\<chi> y. if x = y then r else vec_nth (snd v) y))"  
  
\<comment> \<open>Semantics for formulas, differential formulas, programs.\<close>
fun fml_sem  :: "('a::finite, 'b::finite, 'c::finite) interp \<Rightarrow> ('a::finite, 'b::finite, 'c::finite) formula \<Rightarrow> 'c::finite state set" and
  prog_sem :: "('a::finite, 'b::finite, 'c::finite) interp \<Rightarrow> ('a::finite, 'b::finite, 'c::finite) hp \<Rightarrow> ('c::finite state * 'c::finite state) set"
where
  "fml_sem I (Geq t1 t2) = {v. dterm_sem I t1 v \<ge> dterm_sem I t2 v}"
| "fml_sem I (Prop P terms) = {\<nu>. Predicates I P (\<chi> i. dterm_sem I (terms i) \<nu>)}"
| "fml_sem I (Not \<phi>) = {v. v \<notin> fml_sem I \<phi>}"
| "fml_sem I (And \<phi> \<psi>) = fml_sem I \<phi> \<inter> fml_sem I \<psi>"
| "fml_sem I (Exists x \<phi>) = {v | v r. (repv v x r) \<in> fml_sem I \<phi>}"
| "fml_sem I (Diamond \<alpha> \<phi>) = {\<nu> | \<nu> \<omega>. (\<nu>, \<omega>) \<in> prog_sem I \<alpha> \<and> \<omega> \<in> fml_sem I \<phi>}"
| "fml_sem I (InContext c \<phi>) = Contexts I c (fml_sem I \<phi>)"

| "prog_sem I (Pvar p) = Programs I p"
| "prog_sem I (Assign x t) = {(\<nu>, \<omega>). \<omega> = repv \<nu> x (dterm_sem I t \<nu>)}"
| "prog_sem I (DiffAssign x t) = {(\<nu>, \<omega>). \<omega> = repd \<nu> x (dterm_sem I t \<nu>)}"
| "prog_sem I (Test \<phi>) = {(\<nu>, \<nu>) | \<nu>. \<nu> \<in> fml_sem I \<phi>}"
| "prog_sem I (Choice \<alpha> \<beta>) = prog_sem I \<alpha> \<union> prog_sem I \<beta>"
| "prog_sem I (Sequence \<alpha> \<beta>) = prog_sem I \<alpha> O prog_sem I \<beta>"
| "prog_sem I (Loop \<alpha>) = (prog_sem I \<alpha>)\<^sup>*"
| "prog_sem I (EvolveODE ODE \<phi>) =
  ({(\<nu>, mk_v I ODE \<nu> (sol t)) | \<nu> sol t.
      t \<ge> 0 \<and>
      (sol solves_ode (\<lambda>_. ODE_sem I ODE)) {0..t} {x. mk_v I ODE \<nu> x \<in> fml_sem I \<phi>} \<and>
      sol 0 = fst \<nu>})"

context ids begin
definition valid :: "('sf, 'sc, 'sz) formula \<Rightarrow> bool"
where "valid \<phi> \<equiv> (\<forall> I. \<forall> \<nu>. is_interp I \<longrightarrow> \<nu> \<in> fml_sem I \<phi>)"
end

text\<open> Because mk\_v is defined with the SOME operator, need to construct a state that satisfies
    ${\tt Vagree} \omega \nu (- {\tt ODE\_vars\ ODE}) 
     \wedge {\tt Vagree} \omega {\tt (mk\_xode\ I\ ODE\ sol)\ (ODE\_vars\ ODE)})$
    to do anything useful \<close>
fun concrete_v::"('a::finite, 'b::finite, 'c::finite) interp \<Rightarrow> ('a::finite, 'c::finite) ODE \<Rightarrow> 'c::finite state \<Rightarrow> 'c::finite simple_state \<Rightarrow> 'c::finite state"
where "concrete_v I ODE \<nu> sol =
((\<chi> i. (if Inl i \<in> semBV I ODE then sol else (fst \<nu>)) $ i),
 (\<chi> i. (if Inr i \<in> semBV I ODE then ODE_sem I ODE sol else (snd \<nu>)) $ i))"

lemma mk_v_exists:"\<exists>\<omega>. Vagree \<omega> \<nu> (- semBV I ODE) 
\<and> Vagree \<omega> (mk_xode I ODE sol) (semBV I ODE)"
  by(rule exI[where x="(concrete_v I ODE \<nu> sol)"], auto simp add: Vagree_def)
    
lemma mk_v_agree:"Vagree (mk_v I ODE \<nu> sol) \<nu> (- semBV I ODE) 
\<and> Vagree (mk_v I ODE \<nu> sol) (mk_xode I ODE sol) (semBV I ODE)"
  unfolding mk_v_def 
  apply(rule theI[where a= "((\<chi> i. (if Inl i \<in> semBV I ODE then sol else (fst \<nu>)) $ i),
  (\<chi> i. (if Inr i \<in> semBV I ODE then ODE_sem I ODE sol else (snd \<nu>)) $ i))"])
   using exE[OF mk_v_exists, of \<nu> I ODE sol]
   by (auto simp add: Vagree_def vec_eq_iff)

lemma mk_v_concrete:"mk_v I ODE \<nu> sol = ((\<chi> i. (if Inl i \<in> semBV I ODE then sol else (fst \<nu>)) $ i),
  (\<chi> i. (if Inr i \<in> semBV I ODE then ODE_sem I ODE sol else (snd \<nu>)) $ i))"
  apply(rule agree_UNIV_eq)
  using mk_v_agree[of I ODE \<nu> sol]
  unfolding Vagree_def by auto

subsection \<open>Trivial Simplification Lemmas\<close>
text \<open>
 We often want to pretend the definitions in the semantics are written slightly
 differently than they are. Since the simplifier has some trouble guessing that
 these are the right simplifications to do, we write them all out explicitly as
 lemmas, even though they prove trivially.
\<close>

lemma svar_case:
  "sterm_sem I (Var x) = (\<lambda>v. v $ x)"
  by auto

lemma sconst_case:
  "sterm_sem I (Const r) = (\<lambda>v. r)"
  by auto

lemma sfunction_case:
  "sterm_sem I (Function f args) = (\<lambda>v. Functions I f (\<chi> i. sterm_sem I (args i) v))"
  by auto

lemma splus_case:
  "sterm_sem I (Plus t1 t2) = (\<lambda>v. (sterm_sem I t1 v) + (sterm_sem I t2 v))"
  by auto

lemma stimes_case:
  "sterm_sem I (Times t1 t2) = (\<lambda>v. (sterm_sem I t1 v) * (sterm_sem I t2 v))"
  by auto  

lemma or_sem [simp]:
  "fml_sem I (Or \<phi> \<psi>) = fml_sem I \<phi> \<union> fml_sem I \<psi>"
  by (auto simp add: Or_def)

lemma iff_sem [simp]: "(\<nu> \<in> fml_sem I (A \<leftrightarrow> B))
  \<longleftrightarrow> ((\<nu> \<in> fml_sem I A) \<longleftrightarrow> (\<nu> \<in> fml_sem I B))"
  by (auto simp add: Equiv_def)

lemma box_sem [simp]:"fml_sem I (Box \<alpha> \<phi>) = {\<nu>. \<forall> \<omega>. (\<nu>, \<omega>) \<in> prog_sem I \<alpha> \<longrightarrow> \<omega> \<in> fml_sem I \<phi>}"
  unfolding Box_def fml_sem.simps
  using Collect_cong by (auto)
  
lemma forall_sem [simp]:"fml_sem I (Forall x \<phi>) = {v. \<forall>r. (repv v x r) \<in> fml_sem I \<phi>}"
  unfolding Forall_def fml_sem.simps
  using Collect_cong by (auto)
  
lemma greater_sem[simp]:"fml_sem I (Greater \<theta> \<theta>') = {v. dterm_sem I \<theta> v > dterm_sem I \<theta>' v}"
  unfolding Greater_def by auto

lemma loop_sem:"prog_sem I (Loop \<alpha>) = (prog_sem I \<alpha>)\<^sup>*"
  by (auto)

lemma impl_sem [simp]: "(\<nu> \<in> fml_sem I (A \<rightarrow> B))
  = ((\<nu> \<in> fml_sem I A) \<longrightarrow> (\<nu> \<in> fml_sem I B))"
  by (auto simp add: Implies_def)

lemma equals_sem [simp]: "(\<nu> \<in> fml_sem I (Equals \<theta> \<theta>'))
  = (dterm_sem I \<theta> \<nu> = dterm_sem I \<theta>' \<nu>)"
  by (auto simp add: Equals_def)

lemma diamond_sem [simp]: "fml_sem I (Diamond \<alpha> \<phi>)
  = {\<nu>. \<exists> \<omega>. (\<nu>, \<omega>) \<in> prog_sem I \<alpha> \<and> \<omega> \<in> fml_sem I \<phi>}"
  by auto

lemma tt_sem [simp]:"fml_sem I TT = UNIV" unfolding TT_def by auto
lemma ff_sem [simp]:"fml_sem I FF = {}" unfolding FF_def by auto

lemma iff_to_impl: "((\<nu> \<in> fml_sem I A) \<longleftrightarrow> (\<nu> \<in> fml_sem I B))
  \<longleftrightarrow> (((\<nu> \<in> fml_sem I A) \<longrightarrow> (\<nu> \<in> fml_sem I B))
     \<and> ((\<nu> \<in> fml_sem I B) \<longrightarrow> (\<nu> \<in> fml_sem I A)))"
  by (auto) 
    
    fun seq2fml :: "('a,'b,'c) sequent \<Rightarrow> ('a,'b,'c) formula"
where
  "seq2fml (ante,succ) = Implies (foldr And ante TT) (foldr Or succ FF)"
  
context ids begin
fun seq_sem ::"('sf, 'sc, 'sz) interp \<Rightarrow> ('sf, 'sc, 'sz) sequent \<Rightarrow> 'sz state set"
where "seq_sem I S = fml_sem I (seq2fml S)"

lemma and_foldl_sem:"\<nu> \<in> fml_sem I (foldr And \<Gamma> TT) \<Longrightarrow> (\<And>\<phi>. List.member \<Gamma> \<phi> \<Longrightarrow> \<nu> \<in> fml_sem I \<phi>)"
  by(induction \<Gamma>, auto simp add: member_rec)

lemma and_foldl_sem_conv:"(\<And>\<phi>. List.member \<Gamma> \<phi> \<Longrightarrow> \<nu> \<in> fml_sem I \<phi>) \<Longrightarrow> \<nu> \<in> fml_sem I (foldr And \<Gamma> TT)"
  by(induction \<Gamma>, auto simp add: member_rec)

lemma or_foldl_sem:"List.member \<Gamma> \<phi> \<Longrightarrow> \<nu> \<in> fml_sem I \<phi> \<Longrightarrow> \<nu> \<in> fml_sem I (foldr Or \<Gamma> FF)"
  by(induction \<Gamma>, auto simp add: member_rec)

lemma or_foldl_sem_conv:"\<nu> \<in> fml_sem I (foldr Or \<Gamma> FF) \<Longrightarrow> \<exists> \<phi>. \<nu> \<in> fml_sem I \<phi> \<and> List.member \<Gamma> \<phi>"
  by(induction \<Gamma>, auto simp add: member_rec)

lemma seq_semI':"(\<nu> \<in> fml_sem I (foldr And \<Gamma> TT) \<Longrightarrow> \<nu> \<in> fml_sem I (foldr Or \<Delta> FF)) \<Longrightarrow> \<nu> \<in> seq_sem I (\<Gamma>,\<Delta>)"
  by auto 

lemma seq_semD':"\<And>P. \<nu> \<in> seq_sem I (\<Gamma>,\<Delta>) \<Longrightarrow> ((\<nu> \<in> fml_sem I (foldr And \<Gamma> TT) \<Longrightarrow> \<nu> \<in> fml_sem I (foldr Or \<Delta> FF)) \<Longrightarrow> P) \<Longrightarrow> P"
  by simp

definition sublist::"'a list \<Rightarrow> 'a list \<Rightarrow> bool"
where "sublist A B \<equiv> (\<forall>x. List.member A x \<longrightarrow> List.member B x)"

lemma sublistI:"(\<And>x. List.member A x \<Longrightarrow> List.member B x) \<Longrightarrow> sublist A B"
  unfolding sublist_def by auto

lemma \<Gamma>_sub_sem:"sublist \<Gamma>1 \<Gamma>2 \<Longrightarrow> \<nu> \<in> fml_sem I (foldr And \<Gamma>2 TT) \<Longrightarrow> \<nu> \<in> fml_sem I (foldr And \<Gamma>1 TT)"
  unfolding sublist_def 
  by (metis and_foldl_sem and_foldl_sem_conv)

lemma seq_semI:"List.member \<Delta> \<psi> \<Longrightarrow>((\<And>\<phi>. List.member \<Gamma> \<phi> \<Longrightarrow> \<nu> \<in> fml_sem I \<phi>) \<Longrightarrow> \<nu> \<in> fml_sem I \<psi>) \<Longrightarrow> \<nu> \<in> seq_sem I (\<Gamma>,\<Delta>)"
  apply(rule seq_semI')
  using and_foldl_sem[of \<nu> I \<Gamma>] or_foldl_sem by blast

lemma seq_semD:"\<nu> \<in> seq_sem I (\<Gamma>,\<Delta>) \<Longrightarrow> (\<And>\<phi>. List.member \<Gamma> \<phi> \<Longrightarrow> \<nu> \<in> fml_sem I \<phi>) \<Longrightarrow> \<exists>\<phi>. (List.member \<Delta> \<phi>) \<and>\<nu> \<in> fml_sem I \<phi> "
  apply(rule seq_semD')
  using and_foldl_sem_conv or_foldl_sem_conv
  by blast+

lemma seq_MP:"\<nu> \<in> seq_sem I (\<Gamma>,\<Delta>) \<Longrightarrow> \<nu> \<in> fml_sem I (foldr And \<Gamma> TT) \<Longrightarrow> \<nu> \<in> fml_sem I (foldr Or \<Delta> FF)"
  by(induction \<Delta>, auto)

definition seq_valid
where "seq_valid S \<equiv> \<forall>I. is_interp I \<longrightarrow> seq_sem I S = UNIV"  


text\<open> Soundness for derived rules is local soundness, i.e. if the premisses are all true in the same interpretation,
  then the conclusion is also true in that same interpretation. \<close>
definition sound :: "('sf, 'sc, 'sz) rule \<Rightarrow> bool"
where "sound R \<longleftrightarrow> (\<forall>I. is_interp I \<longrightarrow> (\<forall>i. i \<ge> 0 \<longrightarrow> i < length (fst R) \<longrightarrow> seq_sem I (nth (fst R) i) = UNIV) \<longrightarrow> seq_sem I (snd R) = UNIV)"

lemma soundI:"(\<And>I. is_interp I \<Longrightarrow> (\<And>i. i \<ge> 0 \<Longrightarrow> i < length SG \<Longrightarrow> seq_sem I (nth SG i) = UNIV) \<Longrightarrow> seq_sem I G = UNIV) \<Longrightarrow> sound (SG,G)"
  unfolding sound_def by auto

lemma soundI':"(\<And>I \<nu>. is_interp I \<Longrightarrow> (\<And>i . i \<ge> 0 \<Longrightarrow> i < length SG \<Longrightarrow> \<nu> \<in> seq_sem I (nth SG i)) \<Longrightarrow> \<nu> \<in> seq_sem I G) \<Longrightarrow> sound (SG,G)"
  unfolding sound_def by auto
    
lemma soundI_mem:"(\<And>I. is_interp I \<Longrightarrow> (\<And>\<phi>. List.member SG \<phi> \<Longrightarrow> seq_sem I \<phi> = UNIV) \<Longrightarrow> seq_sem I C = UNIV) \<Longrightarrow> sound (SG,C)"
  apply (auto simp add: sound_def)
  by (metis in_set_conv_nth in_set_member iso_tuple_UNIV_I seq2fml.simps)

lemma soundI_memv:"(\<And>I. is_interp I \<Longrightarrow> (\<And>\<phi> \<nu>. List.member SG \<phi> \<Longrightarrow> \<nu> \<in> seq_sem I \<phi>) \<Longrightarrow> (\<And>\<nu>. \<nu> \<in> seq_sem I C)) \<Longrightarrow> sound (SG,C)"
  apply(rule soundI_mem)
  using impl_sem by blast

lemma soundI_memv':"(\<And>I. is_interp I \<Longrightarrow> (\<And>\<phi> \<nu>. List.member SG \<phi> \<Longrightarrow> \<nu> \<in> seq_sem I \<phi>) \<Longrightarrow> (\<And>\<nu>. \<nu> \<in> seq_sem I C)) \<Longrightarrow> R = (SG,C) \<Longrightarrow> sound R"
  using  soundI_mem
  using impl_sem by blast

lemma soundD_mem:"sound (SG,C) \<Longrightarrow> (\<And>I. is_interp I \<Longrightarrow> (\<And>\<phi>. List.member SG \<phi> \<Longrightarrow> seq_sem I \<phi> = UNIV) \<Longrightarrow> seq_sem I C = UNIV)"
  apply (auto simp add: sound_def)
  using in_set_conv_nth in_set_member iso_tuple_UNIV_I seq2fml.simps
  by (metis seq2fml.elims)

lemma soundD_memv:"sound (SG,C) \<Longrightarrow> (\<And>I. is_interp I \<Longrightarrow> (\<And>\<phi> \<nu>. List.member SG \<phi> \<Longrightarrow> \<nu> \<in> seq_sem I \<phi>) \<Longrightarrow> (\<And>\<nu>. \<nu> \<in> seq_sem I C))"
  using soundD_mem
  by (metis UNIV_I UNIV_eq_I)

end
end
