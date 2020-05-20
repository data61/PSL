(*  Title:       A Definitional Encoding of TLA in Isabelle/HOL
    Authors:     Gudmund Grov <ggrov at inf.ed.ac.uk>
                 Stephan Merz <Stephan.Merz at loria.fr>
    Year:        2011
    Maintainer:  Gudmund Grov <ggrov at inf.ed.ac.uk>
*)

section \<open>Semantics\<close> 

theory Semantics
imports Sequence Intensional
begin

text \<open>
  This theory mechanises a \emph{shallow} embedding of \tlastar{} using the
  \<open>Sequence\<close> and \<open>Intensional\<close> theories. A shallow embedding
  represents \tlastar{} using Isabelle/HOL predicates, while a \emph{deep}
  embedding would represent \tlastar{} formulas and pre-formulas as mutually
  inductive datatypes\footnote{See e.g. \cite{Wildmoser04} for a discussion
  about deep vs. shallow embeddings in Isabelle/HOL.}.  
  The choice of a shallow over a deep embedding is motivated by the following 
  factors: a shallow embedding is usually less involved, and existing Isabelle
  theories and tools can be applied more directly to enhance automation; due to
  the lifting in the \<open>Intensional\<close> theory, a shallow embedding can reuse
  standard logical operators, whilst a deep embedding requires a different
  set of operators for both formulas and pre-formulas. Finally, since our 
  target is system verification rather than proving meta-properties of \tlastar{},
  which requires a deep embedding, a shallow embedding is more fit for purpose.
\<close>

subsection "Types of Formulas"

text \<open>
  To mechanise the \tlastar{} semantics, the following
  type abbreviations are used:
\<close>

type_synonym ('a,'b) formfun = "'a seq \<Rightarrow> 'b"
type_synonym 'a formula = "('a,bool) formfun"
type_synonym ('a,'b) stfun = "'a \<Rightarrow> 'b"
type_synonym 'a stpred = "('a,bool) stfun"

instance 
 "fun" :: (type,type) world ..

instance
 "prod" :: (type,type) world ..

text \<open>
  Pair and function are instantiated to be of type class world.
  This allows use of the lifted intensional logic for formulas, and 
  standard logical connectives can therefore be used.
\<close>

subsection "Semantics of TLA*"

text \<open>The semantics of \tlastar{} is defined.\<close>

definition always :: "('a::world) formula \<Rightarrow> 'a formula" 
where "always F \<equiv> \<lambda> s. \<forall> n. (s |\<^sub>s n) \<Turnstile> F"

definition nexts :: "('a::world) formula \<Rightarrow> 'a formula" 
where "nexts F \<equiv> \<lambda> s. (tail s) \<Turnstile> F"

definition before :: "('a::world,'b) stfun \<Rightarrow> ('a,'b) formfun"
where "before f \<equiv> \<lambda> s. (first s) \<Turnstile> f"

definition after :: "('a::world,'b) stfun \<Rightarrow> ('a,'b) formfun"
where "after f \<equiv> \<lambda> s. (second s) \<Turnstile> f" 

definition unch  :: "('a::world,'b) stfun \<Rightarrow> 'a formula" 
where "unch v \<equiv> \<lambda> s. s \<Turnstile> (after v) = (before v)"

definition action :: "('a::world) formula \<Rightarrow> ('a,'b) stfun \<Rightarrow> 'a formula"
where "action P v \<equiv> \<lambda> s. \<forall> i. ((s |\<^sub>s i) \<Turnstile> P) \<or> ((s |\<^sub>s i) \<Turnstile> unch v)"

subsubsection "Concrete Syntax"

text\<open>This is the concrete syntax for the (abstract) operators above.\<close>

syntax
 "_always" :: "lift \<Rightarrow> lift" ("(\<box>_)" [90] 90) 
 "_nexts" :: "lift \<Rightarrow> lift" ("(\<circle>_)" [90] 90) 
 "_action" :: "[lift,lift] \<Rightarrow> lift" ("(\<box>[_]'_(_))" [20,1000] 90)
 "_before"    :: "lift \<Rightarrow> lift"  ("($_)" [100] 99)
 "_after"     :: "lift \<Rightarrow> lift"  ("(_$)" [100] 99)
 "_prime"     :: "lift \<Rightarrow> lift"  ("(_`)" [100] 99)  
 "_unch"     :: "lift \<Rightarrow> lift"  ("(Unchanged _)" [100] 99) 
 "TEMP"  :: "lift \<Rightarrow> 'b" ("(TEMP _)")

syntax (ASCII)
 "_always" :: "lift \<Rightarrow> lift" ("([]_)" [90] 90)
 "_nexts" :: "lift \<Rightarrow> lift" ("(Next _)" [90] 90)
 "_action" :: "[lift,lift] \<Rightarrow> lift" ("([][_]'_(_))" [20,1000] 90)

translations
 "_always" \<rightleftharpoons> "CONST always"
 "_nexts" \<rightleftharpoons> "CONST nexts"
 "_action" \<rightleftharpoons> "CONST action"
 "_before"    \<rightleftharpoons> "CONST before" 
 "_after"     \<rightleftharpoons> "CONST after" 
 "_prime"     \<rightharpoonup> "CONST after"
 "_unch"     \<rightleftharpoons> "CONST unch" 
 "TEMP F" \<rightharpoonup> "(F:: (nat \<Rightarrow> _) \<Rightarrow> _)"


subsection "Abbreviations"

text \<open>Some standard temporal abbreviations, with their concrete syntax.\<close>

definition actrans :: "('a::world) formula \<Rightarrow> ('a,'b) stfun \<Rightarrow> 'a formula"
where "actrans P v \<equiv> TEMP(P \<or> unch v)"

definition eventually :: "('a::world) formula \<Rightarrow> 'a formula"
where "eventually F \<equiv> LIFT(\<not>\<box>(\<not>F))"

definition angle_action :: "('a::world) formula \<Rightarrow> ('a,'b) stfun \<Rightarrow> 'a formula"
where "angle_action P v \<equiv> LIFT(\<not>\<box>[\<not>P]_v)"

definition angle_actrans :: "('a::world) formula \<Rightarrow> ('a,'b) stfun \<Rightarrow> 'a formula"
where "angle_actrans P v \<equiv> TEMP (\<not> actrans (LIFT(\<not>P)) v)"

definition leadsto :: "('a::world) formula \<Rightarrow> 'a formula \<Rightarrow> 'a formula"
where "leadsto P Q \<equiv> LIFT \<box>(P \<longrightarrow> eventually Q)"

subsubsection "Concrete Syntax"

syntax (ASCII)
  "_actrans" :: "[lift,lift] \<Rightarrow> lift" ("([_]'_(_))"  [20,1000] 90)
  "_eventually" :: "lift \<Rightarrow> lift" ("(<>_)" [90] 90)
  "_angle_action" :: "[lift,lift] \<Rightarrow> lift" ("(<><_>'_(_))" [20,1000] 90)
  "_angle_actrans" :: "[lift,lift] \<Rightarrow> lift" ("(<_>'_(_))" [20,1000] 90)
  "_leadsto" :: "[lift,lift] \<Rightarrow> lift" ("(_ ~> _)" [26,25] 25)

syntax
  "_eventually" :: "lift \<Rightarrow> lift" ("(\<diamond>_)" [90] 90)
  "_angle_action" :: "[lift,lift] \<Rightarrow> lift" ("(\<diamond>\<langle>_\<rangle>'_(_))" [20,1000] 90)
  "_angle_actrans" :: "[lift,lift] \<Rightarrow> lift" ("(\<langle>_\<rangle>'_(_))" [20,1000] 90)
  "_leadsto" :: "[lift,lift] \<Rightarrow> lift" ("(_ \<leadsto> _)" [26,25] 25)

translations 
  "_actrans" \<rightleftharpoons> "CONST actrans"
  "_eventually" \<rightleftharpoons> "CONST eventually"
  "_angle_action" \<rightleftharpoons> "CONST angle_action"
  "_angle_actrans" \<rightleftharpoons> "CONST angle_actrans"
  "_leadsto" \<rightleftharpoons> "CONST leadsto"


subsection "Properties of Operators"

text \<open>The following lemmas show that these operators have the expected semantics.\<close>

lemma eventually_defs: "(w \<Turnstile> \<diamond> F) = (\<exists> n. (w |\<^sub>s n) \<Turnstile> F)"
  by (simp add: eventually_def always_def)

lemma angle_action_defs: "(w \<Turnstile> \<diamond>\<langle>P\<rangle>_v) = (\<exists> i. ((w |\<^sub>s i) \<Turnstile> P) \<and> ((w |\<^sub>s i) \<Turnstile> v$ \<noteq> $v))"
  by (simp add: angle_action_def action_def unch_def)

lemma unch_defs: "(w \<Turnstile> Unchanged v) = (((second w) \<Turnstile> v) = ((first w) \<Turnstile> v))"
  by (simp add: unch_def before_def nexts_def after_def tail_def suffix_def first_def second_def)

lemma linalw:
  assumes h1: "a \<le> b" and h2: "(w |\<^sub>s a) \<Turnstile> \<box>A"
  shows "(w |\<^sub>s b) \<Turnstile> \<box>A"
proof (clarsimp simp: always_def)
  fix n
  from h1 obtain k where g1: "b = a + k" by (auto simp: le_iff_add)
  with h2 show "(w |\<^sub>s b |\<^sub>s n) \<Turnstile> A" by (auto simp: always_def suffix_plus ac_simps)
qed

subsection "Invariance Under Stuttering"

text \<open>
  A key feature of \tlastar{} is that specification at different abstraction
  levels can be compared. The soundness of this relies on the stuttering invariance 
  of formulas. Since the embedding is shallow, it cannot be shown that a generic 
  \tlastar{} formula is stuttering invariant. However, this section will show that 
  each operator is stuttering invariant or preserves stuttering invariance in an
  appropriate sense, which can be used to show stuttering invariance
  for given specifications. 

  Formula \<open>F\<close> is stuttering invariant if for any two similar behaviours
  (i.e., sequences of states), \<open>F\<close> holds in one iff it holds in the other.
  The definition is generalised to arbitrary expressions, and not just predicates.
\<close>

definition stutinv :: "('a,'b) formfun \<Rightarrow> bool"
where "stutinv F \<equiv> \<forall> \<sigma> \<tau>. \<sigma> \<approx> \<tau> \<longrightarrow> (\<sigma> \<Turnstile> F) = (\<tau> \<Turnstile> F)"

text\<open>
  The requirement for stuttering invariance is too strong for pre-formulas. 
  For example, an action formula specifies a relation between the first two states
  of a behaviour, and will rarely be satisfied by a stuttering step. This is why
  pre-formulas are ``protected'' by (square or angle) brackets in \tlastar{}:
  the only place a pre-formula \<open>P\<close> can be used is inside an action:
  \<open>\<box>[P]_v\<close>.
  To show that \<open>\<box>[P]_v\<close> is stuttering invariant, is must be shown that a 
  slightly weaker predicate holds for @{term P}. For example, if @{term P} contains 
  a term of the form \<open>\<circle>\<circle>Q\<close>, then it is not a well-formed pre-formula, thus 
  \<open>\<box>[P]_v\<close> is not stuttering invariant. This weaker version of
  stuttering invariance has been named \emph{near stuttering invariance}.
\<close>

definition nstutinv :: "('a,'b) formfun \<Rightarrow> bool"
where "nstutinv P \<equiv> \<forall> \<sigma> \<tau>. (first \<sigma> = first \<tau>) \<and> (tail \<sigma>) \<approx> (tail \<tau>) \<longrightarrow> (\<sigma> \<Turnstile> P) = (\<tau> \<Turnstile> P)"

syntax
  "_stutinv" :: "lift \<Rightarrow> bool" ("(STUTINV _)" [40] 40)
  "_nstutinv" :: "lift \<Rightarrow> bool" ("(NSTUTINV _)" [40] 40)

translations
  "_stutinv" \<rightleftharpoons> "CONST stutinv"
  "_nstutinv" \<rightleftharpoons> "CONST nstutinv"


text \<open>
  Predicate @{term "stutinv F"} formalises stuttering invariance for
  formula @{term F}. That is if two sequences are similar @{term "s \<approx> t"} (equal up
  to stuttering) then the validity of @{term F} under both @{term s} and @{term t}
  are equivalent. Predicate @{term "nstutinv P"} should be read as \emph{nearly
  stuttering invariant} -- and is required for some stuttering invariance proofs.
\<close>

lemma stutinv_strictly_stronger: 
  assumes h: "STUTINV F" shows "NSTUTINV F"
  unfolding nstutinv_def
proof (clarify)
  fix s t :: "nat \<Rightarrow> 'a"
  assume a1: "first s = first t" and a2: "(tail s) \<approx> (tail t)"
  have "s \<approx> t"
  proof -
    have tg1: "(first s) ## (tail s) = s" by (rule seq_app_first_tail)
    have tg2: "(first t) ## (tail t) = t" by (rule seq_app_first_tail)
    with a1 have tg2': "(first s) ## (tail t) = t" by simp
    from a2 have "(first s) ## (tail s) \<approx> (first s) ## (tail t)" by (rule app_seqsimilar)
    with tg1 tg2' show ?thesis by simp
  qed
  with h show "(s \<Turnstile> F) = (t \<Turnstile> F)" by (simp add: stutinv_def)
qed

subsubsection "Properties of @{term stutinv}"

text \<open>
  This subsection proves stuttering invariance, preservation of stuttering invariance
  and introduction of stuttering invariance for different formulas. 
  First, state predicates are stuttering invariant.
\<close>

theorem stut_before: "STUTINV $F"
proof (clarsimp simp: stutinv_def)
  fix s t :: "'a seq"
  assume a1: "s \<approx> t"
  hence "(first s) = (first t)" by (rule sim_first)
  thus "(s \<Turnstile> $F) = (t \<Turnstile> $F)" by (simp add: before_def)
qed

lemma nstut_after: "NSTUTINV F$"
proof (clarsimp simp: nstutinv_def)
  fix s t :: "'a seq"
  assume a1: "tail s \<approx> tail t"
  thus "(s \<Turnstile> F$) = (t \<Turnstile> F$)" by (simp add: after_def tail_sim_second)
qed

text\<open>The always operator preserves stuttering invariance.\<close>

theorem stut_always: assumes H:"STUTINV F" shows "STUTINV \<box>F"
proof (clarsimp simp: stutinv_def)
  fix s t :: "'a seq"
  assume a2: "s \<approx> t"
  show "(s \<Turnstile> (\<box> F)) = (t \<Turnstile> (\<box> F))"
  proof 
    assume a1: "t \<Turnstile> \<box> F"
    show "s \<Turnstile> \<box> F"
    proof (clarsimp simp: always_def)
      fix n
      from a2[THEN sim_step] obtain m where m: "s |\<^sub>s n \<approx> t |\<^sub>s m" by blast
      from a1 have "(t |\<^sub>s m) \<Turnstile> F" by (simp add: always_def)
      with H m show "(s |\<^sub>s n) \<Turnstile> F" by (simp add: stutinv_def)
    qed
  next
    assume a1: "s \<Turnstile> (\<box> F)"
    show "t \<Turnstile> (\<box> F)"
    proof (clarsimp simp: always_def)
      fix n
      from a2[THEN seqsim_sym, THEN sim_step] obtain m where m: "t |\<^sub>s n \<approx> s |\<^sub>s m" by blast
      from a1 have "(s |\<^sub>s m) \<Turnstile> F" by (simp add: always_def)
      with H m show "(t |\<^sub>s n) \<Turnstile> F" by (simp add: stutinv_def)
    qed
  qed
qed

text \<open>
  Assuming that formula @{term P} is nearly suttering invariant
  then \<open>\<box>[P]_v\<close> will be stuttering invariant.
\<close>

lemma stut_action_lemma:
  assumes H: "NSTUTINV P" and st: "s \<approx> t" and P: "t \<Turnstile> \<box>[P]_v"
  shows "s \<Turnstile> \<box>[P]_v"
proof (clarsimp simp: action_def)
  fix n
  assume "\<not> ((s |\<^sub>s n) \<Turnstile> Unchanged v)"
  hence v: "v (s (Suc n)) \<noteq> v (s n)" 
    by (simp add: unch_defs first_def second_def suffix_def)
  from st[THEN sim_step] obtain m where
    a2': "s |\<^sub>s n \<approx> t |\<^sub>s m 
          \<and> (s |\<^sub>s Suc n \<approx> t |\<^sub>s Suc m \<or> s |\<^sub>s Suc n \<approx> t |\<^sub>s m)" ..
  hence g1: "(s |\<^sub>s n \<approx> t |\<^sub>s m)" by simp
  hence g1'': "first (s |\<^sub>s n) = first (t |\<^sub>s m)" by (simp add: sim_first)
  hence g1': "s n = t m" by (simp add: suffix_def first_def)
  from a2' have g2: "s |\<^sub>s Suc n \<approx> t |\<^sub>s Suc m \<or> s |\<^sub>s Suc n \<approx> t |\<^sub>s m" by simp
  from P have a1': "((t |\<^sub>s m) \<Turnstile> P) \<or> ((t |\<^sub>s m) \<Turnstile> Unchanged v)" by (simp add: action_def)
  from g2 show "(s |\<^sub>s n) \<Turnstile> P"
  proof
    assume "s |\<^sub>s Suc n \<approx> t |\<^sub>s m"
    hence "first (s |\<^sub>s Suc n) = first (t |\<^sub>s m)" by (simp add: sim_first)
    hence "s (Suc n) = t m" by (simp add: suffix_def first_def)
    with g1' v show ?thesis by simp  \<comment> \<open>by contradiction\<close>
  next
    assume a3: "s |\<^sub>s Suc n \<approx> t |\<^sub>s Suc m"
    hence "first (s |\<^sub>s Suc n) = first (t |\<^sub>s Suc m)" by (simp add: sim_first)
    hence a3': "s (Suc n) = t (Suc m)" by (simp add: suffix_def first_def)
    from a1' show ?thesis
    proof
      assume "(t |\<^sub>s m) \<Turnstile> Unchanged v"
      hence "v (t (Suc m)) = v (t m)"
        by (simp add: unch_defs first_def second_def suffix_def)
      with g1' a3' v show ?thesis by simp  \<comment> \<open>again, by contradiction\<close>
    next
      assume a4: "(t |\<^sub>s m) \<Turnstile> P"
      from a3 have "tail (s |\<^sub>s n) \<approx> tail (t |\<^sub>s m)" by (simp add: tail_def suffix_plus)
      with H g1'' a4 show ?thesis by (auto simp: nstutinv_def)
    qed
  qed
qed

theorem stut_action: assumes H: "NSTUTINV P" shows "STUTINV \<box>[P]_v"
proof (clarsimp simp: stutinv_def)
  fix s t :: "'a seq"
  assume st: "s \<approx> t"
  show "(s \<Turnstile> \<box>[P]_v) = (t \<Turnstile> \<box>[P]_v)"
  proof
    assume "t \<Turnstile> \<box>[P]_v"
    with H st show "s \<Turnstile> \<box>[P]_v" by (rule stut_action_lemma)
  next
    assume "s \<Turnstile> \<box>[P]_v"
    with H st[THEN seqsim_sym] show "t \<Turnstile> \<box>[P]_v" by (rule stut_action_lemma)
  qed
qed

text \<open>
  The lemmas below shows that propositional and predicate operators 
  preserve stuttering invariance.
\<close>

lemma stut_and: "\<lbrakk>STUTINV F;STUTINV G\<rbrakk> \<Longrightarrow> STUTINV (F \<and> G)"
  by (simp add: stutinv_def)

lemma stut_or: "\<lbrakk>STUTINV F;STUTINV G\<rbrakk> \<Longrightarrow> STUTINV (F \<or> G)"
  by (simp add: stutinv_def)

lemma stut_imp: "\<lbrakk>STUTINV F;STUTINV G\<rbrakk> \<Longrightarrow> STUTINV (F \<longrightarrow> G)"
  by (simp add: stutinv_def)

lemma stut_eq: "\<lbrakk>STUTINV F;STUTINV G\<rbrakk> \<Longrightarrow> STUTINV (F = G)"
  by (simp add: stutinv_def)

lemma stut_noteq: "\<lbrakk>STUTINV F;STUTINV G\<rbrakk> \<Longrightarrow> STUTINV (F \<noteq> G)"
  by (simp add: stutinv_def)

lemma stut_not: "STUTINV F \<Longrightarrow> STUTINV (\<not> F)"
  by (simp add: stutinv_def)

lemma stut_all: "(\<And>x. STUTINV (F x)) \<Longrightarrow> STUTINV (\<forall> x. F x)"
  by (simp add: stutinv_def)

lemma stut_ex: "(\<And>x. STUTINV (F x)) \<Longrightarrow> STUTINV (\<exists> x. F x)"
  by (simp add: stutinv_def)

lemma stut_const: "STUTINV #c"
  by (simp add: stutinv_def)

lemma stut_fun1: "STUTINV X \<Longrightarrow> STUTINV (f <X>)"
  by (simp add: stutinv_def)

lemma stut_fun2: "\<lbrakk>STUTINV X;STUTINV Y\<rbrakk> \<Longrightarrow> STUTINV (f <X,Y>)"
  by (simp add: stutinv_def)

lemma stut_fun3: "\<lbrakk>STUTINV X;STUTINV Y;STUTINV Z\<rbrakk> \<Longrightarrow> STUTINV (f <X,Y,Z>)"
  by (simp add: stutinv_def)

lemma stut_fun4: "\<lbrakk>STUTINV X;STUTINV Y;STUTINV Z; STUTINV W\<rbrakk> \<Longrightarrow> STUTINV (f <X,Y,Z,W>)"
  by (simp add: stutinv_def)

lemma stut_plus: "\<lbrakk>STUTINV x;STUTINV y\<rbrakk> \<Longrightarrow> STUTINV (x+y)"
  by (simp add: stutinv_def)

subsubsection "Properties of @{term nstutinv}"

text \<open>
  This subsection shows analogous properties about near stuttering
  invariance.

  If a formula @{term F} is stuttering invariant then \<open>\<circle>F\<close> is
  nearly stuttering invariant.
\<close>

lemma nstut_nexts: assumes H: "STUTINV F" shows "NSTUTINV \<circle>F"
using H by (simp add: stutinv_def nstutinv_def nexts_def)

text \<open>
  The lemmas below shows that propositional and predicate operators 
  preserves near stuttering invariance.
\<close>

lemma nstut_and: "\<lbrakk>NSTUTINV F;NSTUTINV G\<rbrakk> \<Longrightarrow> NSTUTINV (F \<and> G)"
  by (auto simp: nstutinv_def)

lemma nstut_or: "\<lbrakk>NSTUTINV F;NSTUTINV G\<rbrakk> \<Longrightarrow> NSTUTINV (F \<or> G)"
  by (auto simp: nstutinv_def)

lemma nstut_imp: "\<lbrakk>NSTUTINV F;NSTUTINV G\<rbrakk> \<Longrightarrow> NSTUTINV (F \<longrightarrow> G)"
  by (auto simp: nstutinv_def)

lemma nstut_eq: "\<lbrakk>NSTUTINV F; NSTUTINV G\<rbrakk> \<Longrightarrow> NSTUTINV (F = G)"
  by (force simp: nstutinv_def)

lemma nstut_not: "NSTUTINV F \<Longrightarrow> NSTUTINV (\<not> F)"
  by (auto simp: nstutinv_def)

lemma nstut_noteq: "\<lbrakk>NSTUTINV F; NSTUTINV G\<rbrakk> \<Longrightarrow> NSTUTINV (F \<noteq> G)"
  by (simp add: nstut_eq nstut_not)

lemma nstut_all: "(\<And>x. NSTUTINV (F x)) \<Longrightarrow> NSTUTINV (\<forall> x. F x)"
  by (auto simp: nstutinv_def)

lemma nstut_ex: "(\<And>x. NSTUTINV (F x)) \<Longrightarrow> NSTUTINV (\<exists> x. F x)"
  by (auto simp: nstutinv_def)

lemma nstut_const: "NSTUTINV #c"
  by (auto simp: nstutinv_def)

lemma nstut_fun1: "NSTUTINV X \<Longrightarrow> NSTUTINV (f <X>)"
  by (force simp: nstutinv_def)

lemma nstut_fun2: "\<lbrakk>NSTUTINV X; NSTUTINV Y\<rbrakk> \<Longrightarrow> NSTUTINV (f <X,Y>)"
  by (force simp: nstutinv_def)

lemma nstut_fun3: "\<lbrakk>NSTUTINV X; NSTUTINV Y; NSTUTINV Z\<rbrakk> \<Longrightarrow> NSTUTINV (f <X,Y,Z>)"
  by (force simp: nstutinv_def)

lemma nstut_fun4: "\<lbrakk>NSTUTINV X; NSTUTINV Y; NSTUTINV Z; NSTUTINV W\<rbrakk> \<Longrightarrow> NSTUTINV (f <X,Y,Z,W>)"
  by (force simp: nstutinv_def)

lemma nstut_plus: "\<lbrakk>NSTUTINV x;NSTUTINV y\<rbrakk> \<Longrightarrow> NSTUTINV (x+y)"
  by (simp add: nstut_fun2)

subsubsection "Abbreviations"

text \<open>
  We show the obvious fact that the same properties holds for abbreviated
  operators.
\<close>

lemmas nstut_before = stut_before[THEN stutinv_strictly_stronger]

lemma nstut_unch: "NSTUTINV (Unchanged v)"
proof (unfold unch_def)
  have g1: "NSTUTINV v$" by (rule nstut_after)
  have "NSTUTINV $v" by (rule stut_before[THEN stutinv_strictly_stronger])
  with g1 show "NSTUTINV (v$ = $v)" by (rule nstut_eq)
qed

text\<open>
  Formulas \<open>[P]_v\<close> are not \tlastar{} formulas by themselves,
  but we need to reason about them when they appear wrapped
  inside \<open>\<box>[-]_v\<close>. We only require that it preserves nearly
  stuttering invariance. Observe that \<open>[P]_v\<close> trivially holds for
  a stuttering step, so it cannot be stuttering invariant.
\<close>

lemma nstut_actrans: "NSTUTINV P \<Longrightarrow> NSTUTINV [P]_v"
  by (simp add: actrans_def nstut_unch nstut_or)

lemma stut_eventually: "STUTINV F \<Longrightarrow> STUTINV \<diamond>F"
  by (simp add: eventually_def stut_not stut_always)

lemma stut_leadsto: "\<lbrakk>STUTINV F; STUTINV G\<rbrakk> \<Longrightarrow> STUTINV (F \<leadsto> G)"
  by (simp add: leadsto_def stut_always stut_eventually stut_imp)

lemma stut_angle_action: "NSTUTINV P \<Longrightarrow> STUTINV \<diamond>\<langle>P\<rangle>_v"
  by (simp add: angle_action_def nstut_not stut_action stut_not)

lemma nstut_angle_acttrans: "NSTUTINV P \<Longrightarrow> NSTUTINV \<langle>P\<rangle>_v"
  by (simp add: angle_actrans_def nstut_not nstut_actrans)

lemmas stutinvs = stut_before stut_always stut_action
  stut_and stut_or stut_imp stut_eq stut_noteq stut_not
  stut_all stut_ex stut_eventually stut_leadsto stut_angle_action stut_const 
  stut_fun1 stut_fun2 stut_fun3 stut_fun4

lemmas nstutinvs =  nstut_after nstut_nexts nstut_actrans
  nstut_unch nstut_and nstut_or nstut_imp nstut_eq nstut_noteq nstut_not
  nstut_all nstut_ex nstut_angle_acttrans stutinv_strictly_stronger 
  nstut_fun1 nstut_fun2 nstut_fun3 nstut_fun4 stutinvs[THEN stutinv_strictly_stronger]

lemmas bothstutinvs = stutinvs nstutinvs

end
