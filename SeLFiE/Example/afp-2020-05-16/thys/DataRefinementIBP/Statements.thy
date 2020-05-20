section \<open>Program Statements as Predicate Transformers\<close>

theory Statements
imports Preliminaries
begin

text \<open>
  Program statements are modeled as predicate transformers, functions from predicates to predicates.
  If $\mathit{State}$ is the type of program states, then a program $S$ is a a function from 
  $\mathit{State}\ \mathit{set}$ to
  $\mathit{State}\ \mathit{set}$. If $q \in \mathit{State}\ \mathit{set}$, then the elements of 
  $S\ q$ are the initial states from which
  $S$ is guarantied to terminate in a state from $q$.

  However, most of the time we will work with an arbitrary compleate lattice, or an arbitrary boolean algebra
  instead of the complete boolean algebra of predicate transformers. 

  We will introduce in this section assert, assume, demonic choice, angelic choice, demonic update, and 
  angelic update statements. We will prove also that these statements are monotonic.
\<close>

lemma mono_top[simp]: "mono top"
  by (simp add: mono_def top_fun_def)

lemma mono_choice[simp]: "mono S \<Longrightarrow> mono T \<Longrightarrow> mono (S \<sqinter> T)"
  apply (simp add: mono_def inf_fun_def)
  apply safe
  apply (rule_tac y = "S x" in order_trans)
  apply simp_all
  apply (rule_tac y = "T x" in order_trans)
  by simp_all

subsection "Assert statement"

text \<open>
The assert statement of a predicate $p$ when executed from a state $s$ fails
if $s\not\in p$ and behaves as skip otherwise.
\<close>

definition
  assert::"'a::semilattice_inf \<Rightarrow> 'a \<Rightarrow> 'a" ("{. _ .}" [0] 1000) where
  "{.p.} q \<equiv>  p \<sqinter> q"

lemma mono_assert [simp]: "mono {.p.}"
  apply (simp add: assert_def mono_def, safe)
  apply (rule_tac y = "x" in order_trans)
  by simp_all

subsection "Assume statement"

text \<open>
The assume statement of a predicate $p$ when executed from a state $s$ is not enabled
if $s\not\in p$ and behaves as skip otherwise.
\<close>

definition
  "assume" :: "'a::boolean_algebra \<Rightarrow> 'a \<Rightarrow> 'a" ("[. _ .]" [0] 1000) where
  "[. p .] q \<equiv>  -p \<squnion> q"


lemma mono_assume [simp]: "mono (assume P)"
  apply (simp add: assume_def mono_def)
  apply safe
  apply (rule_tac y = "y" in order_trans)
  by simp_all

subsection "Demonic update statement"

text \<open>
The demonic update statement of a relation $Q: \mathit{State} \to \mathit{Sate} \to bool$,
when executed in a state $s$ computes nondeterministically a new state $s'$ such 
$Q\ s \ s'$ is true. In order for this statement to be correct all
possible choices of $s'$ should be correct. If there is no state $s'$
such that $Q\ s \ s'$, then the demonic update of $Q$ is not enabled
in $s$.
\<close>

definition
  demonic :: "('a \<Rightarrow> 'b::ord) \<Rightarrow> 'b::ord \<Rightarrow> 'a set" ("[: _ :]" [0] 1000) where
  "[:Q:] p = {s . Q s \<le> p}"

lemma mono_demonic [simp]: "mono [:Q:]"
  apply (simp add: mono_def demonic_def)
  by auto

theorem demonic_bottom:
  "[:R:] (\<bottom>::('a::order_bot)) = {s . (R s) = \<bottom>}"
  apply (unfold demonic_def, safe, simp_all)
  apply (rule antisym)
  by auto

theorem demonic_bottom_top [simp]:
  "[:(\<bottom>::_::order_bot):]  = \<top>"
  by (simp add: fun_eq_iff inf_fun_def sup_fun_def demonic_def top_fun_def bot_fun_def)

theorem demonic_sup_inf:
  "[:Q \<squnion> Q':] = [:Q:] \<sqinter> [:Q':]"
  by (simp add: fun_eq_iff sup_fun_def inf_fun_def demonic_def, blast)

subsection "Angelic update statement"

text \<open>
The angelic update statement of a relation $Q: \mathit{State} \to \mathit{State} \to \mathit{bool}$ is similar
to the demonic version, except that it is enough that at least for one choice $s'$, $Q \ s \ s'$
is correct. If there is no state $s'$
such that $Q\ s \ s'$, then the angelic update of $Q$ fails in $s$.
\<close>

definition
  angelic :: "('a \<Rightarrow> 'b::{semilattice_inf,order_bot}) \<Rightarrow> 'b \<Rightarrow> 'a set" 
               ("{: _ :}" [0] 1000) where
  "{:Q:} p = {s . (Q s) \<sqinter> p \<noteq> \<bottom>}"

syntax "_update" :: "patterns => patterns => logic => logic" ("_ \<leadsto> _ . _" 0)
translations
  "_update (_patterns x xs) (_patterns y ys) t" == "CONST id (_abs
           (_pattern x xs) (_Coll (_pattern y ys) t))"
  "_update x y t" == "CONST id (_abs x (_Coll y t))"

term "{: y, z \<leadsto> x, z' . P x y z z' :}"

theorem angelic_bottom [simp]:
  "angelic R \<bottom>  = {}"
  by (simp add: angelic_def inf_bot_bot)

theorem angelic_disjunctive [simp]:
  "{:(R::('a \<Rightarrow> 'b::complete_distrib_lattice)):} \<in> Apply.Disjunctive"
  by (simp add: Apply.Disjunctive_def angelic_def inf_Sup, blast)


subsection "The guard of a statement"

text \<open>
The guard of a statement $S$ is the set of iniatial states from which $S$
is enabled or fails.
\<close>

definition
  "((grd S)::'a::boolean_algebra) = - (S bot)"

lemma grd_choice[simp]: "grd (S \<sqinter> T) = (grd S) \<squnion> (grd T)"
  by (simp add: grd_def inf_fun_def)

lemma grd_demonic: "grd [:Q:] = {s . \<exists> s' . s' \<in> (Q s) }" 
  apply (simp add: grd_def demonic_def)
  by blast

lemma grd_demonic_2[simp]: "(s \<notin> grd [:Q:]) = (\<forall> s' . s' \<notin>  (Q s))" 
  by (simp add: grd_demonic)

theorem grd_angelic:
  "grd {:R:} = UNIV"
  by (simp add: grd_def)

end
