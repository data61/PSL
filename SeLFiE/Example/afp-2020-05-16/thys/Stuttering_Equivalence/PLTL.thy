theory PLTL
  imports Main LTL.LTL Samplers StutterEquivalence
begin

section \<open>Stuttering Invariant LTL Formulas\<close>

text \<open>
  We show that the next-free fragment of propositional linear-time
  temporal logic PLTL is invariant to finite stuttering.
\<close>

subsection \<open>Finite Conjunctions and Disjunctions in PLTL\<close>

(* It would be tempting to define these operators as follows:

definition OR where "OR \<Phi> = Finite_Set.fold or false \<Phi>"
definition AND where "AND \<Phi> = Finite_Set.fold and true \<Phi>"

However, this would only work if "or" and "and" were left-commutative,
which they are not (syntactically). We must therefore resort to
the more general fold_graph predicate, effectively picking a
conjunction (or disjunction) in arbitrary order. 

An alternative would be to define these generalized operators
over lists of formulas, but working with sets is more natural
in the following.
*)

definition OR where "OR \<Phi> \<equiv> SOME \<phi>. fold_graph Or_ltlp False_ltlp \<Phi> \<phi>"

definition AND where "AND \<Phi> \<equiv> SOME \<phi>. fold_graph And_ltlp True_ltlp \<Phi> \<phi>"

lemma fold_graph_OR: "finite \<Phi> \<Longrightarrow> fold_graph Or_ltlp False_ltlp \<Phi> (OR \<Phi>)"
  unfolding OR_def by (rule someI2_ex[OF finite_imp_fold_graph])

lemma fold_graph_AND: "finite \<Phi> \<Longrightarrow> fold_graph And_ltlp True_ltlp \<Phi> (AND \<Phi>)"
  unfolding AND_def by (rule someI2_ex[OF finite_imp_fold_graph])

lemma holds_of_OR [simp]: 
  assumes fin: "finite (\<Phi>::'a pltl set)"
  shows "(\<sigma> \<Turnstile>\<^sub>p OR \<Phi>) = (\<exists>\<phi>\<in>\<Phi>. \<sigma> \<Turnstile>\<^sub>p \<phi>)"
proof -
  {
    fix \<psi>::"'a pltl"
    assume "fold_graph Or_ltlp False_ltlp \<Phi> \<psi>"
    hence "(\<sigma> \<Turnstile>\<^sub>p \<psi>) = (\<exists>\<phi>\<in>\<Phi>. \<sigma> \<Turnstile>\<^sub>p \<phi>)"
      by (rule fold_graph.induct) auto
  }
  with fold_graph_OR[OF fin] show ?thesis by simp
qed

lemma holds_of_AND [simp]: 
  assumes fin: "finite (\<Phi>::'a pltl set)"
  shows "(\<sigma> \<Turnstile>\<^sub>p AND \<Phi>) = (\<forall>\<phi>\<in>\<Phi>. \<sigma> \<Turnstile>\<^sub>p \<phi>)"
proof -
  {
    fix \<psi>::"'a pltl"
    assume "fold_graph And_ltlp True_ltlp \<Phi> \<psi>"
    hence "(\<sigma> \<Turnstile>\<^sub>p \<psi>) = (\<forall>\<phi>\<in>\<Phi>. \<sigma> \<Turnstile>\<^sub>p \<phi>)"
      by (rule fold_graph.induct) auto
  }
  with fold_graph_AND[OF fin] show ?thesis by simp
qed

subsection \<open>Next-Free PLTL Formulas\<close>

text \<open>
  A PLTL formula is called \emph{next-free} if it does not contain any
  subformula.
\<close>

fun next_free :: "'a pltl \<Rightarrow> bool"
where
  "next_free false\<^sub>p = True"
| "next_free (atom\<^sub>p(p)) = True"
| "next_free (\<phi> implies\<^sub>p \<psi>) = (next_free \<phi> \<and> next_free \<psi>)"
| "next_free (X\<^sub>p \<phi>) = False"
| "next_free (\<phi> U\<^sub>p \<psi>) = (next_free \<phi> \<and> next_free \<psi>)"

lemma next_free_not [simp]: 
  "next_free (not\<^sub>p \<phi>) = next_free \<phi>"
  by (simp add: Not_ltlp_def)

lemma next_free_true [simp]: 
  "next_free true\<^sub>p"
  by (simp add: True_ltlp_def)

lemma next_free_or [simp]: 
  "next_free (\<phi> or\<^sub>p \<psi>) = (next_free \<phi> \<and> next_free \<psi>)"
  by (simp add: Or_ltlp_def)

lemma next_free_and [simp]: "next_free (\<phi> and\<^sub>p \<psi>) = (next_free \<phi> \<and> next_free \<psi>)"
  by (simp add: And_ltlp_def)

lemma next_free_eventually [simp]: 
  "next_free (F\<^sub>p \<phi>) = next_free \<phi>"
  by (simp add: Eventually_ltlp_def)

lemma next_free_always [simp]: 
  "next_free (G\<^sub>p \<phi>) = next_free \<phi>"
  by (simp add: Always_ltlp_def)

lemma next_free_release [simp]:
  "next_free (\<phi> R\<^sub>p \<psi>) = (next_free \<phi> \<and> next_free \<psi>)"
  by (simp add: Release_ltlp_def)

lemma next_free_weak_until [simp]:
  "next_free (\<phi> W\<^sub>p \<psi>) = (next_free \<phi> \<and> next_free \<psi>)"
  by (auto simp: WeakUntil_ltlp_def)

lemma next_free_strong_release [simp]:
  "next_free (\<phi> M\<^sub>p \<psi>) = (next_free \<phi> \<and> next_free \<psi>)"
  by (auto simp: StrongRelease_ltlp_def)

lemma next_free_OR [simp]: 
  assumes fin: "finite (\<Phi>::'a pltl set)"
  shows "next_free (OR \<Phi>) = (\<forall>\<phi>\<in>\<Phi>. next_free \<phi>)"
proof -
  {
    fix \<psi>::"'a pltl"
    assume "fold_graph Or_ltlp False_ltlp \<Phi> \<psi>"
    hence "next_free \<psi> = (\<forall>\<phi>\<in>\<Phi>. next_free \<phi>)"
      by (rule fold_graph.induct) auto
  }
  with fold_graph_OR[OF fin] show ?thesis by simp
qed

lemma next_free_AND [simp]: 
  assumes fin: "finite (\<Phi>::'a pltl set)"
  shows "next_free (AND \<Phi>) = (\<forall>\<phi>\<in>\<Phi>. next_free \<phi>)"
proof -
  {
    fix \<psi>::"'a pltl"
    assume "fold_graph And_ltlp True_ltlp \<Phi> \<psi>"
    hence "next_free \<psi> = (\<forall>\<phi>\<in>\<Phi>. next_free \<phi>)"
      by (rule fold_graph.induct) auto
  }
  with fold_graph_AND[OF fin] show ?thesis by simp
qed


subsection \<open>Stuttering Invariance of PLTL Without ``Next''\<close>

text \<open>
  A PLTL formula is \emph{stuttering invariant} if for any stuttering equivalent
  state sequences \<open>\<sigma> \<approx> \<tau>\<close>, the formula holds of \<open>\<sigma>\<close> iff it
  holds of \<open>\<tau>\<close>.
\<close>

definition stutter_invariant where
  "stutter_invariant \<phi> = (\<forall>\<sigma> \<tau>. (\<sigma> \<approx> \<tau>) \<longrightarrow> (\<sigma> \<Turnstile>\<^sub>p \<phi>) = (\<tau> \<Turnstile>\<^sub>p \<phi>))"

text \<open>
  Since stuttering equivalence is symmetric, it is enough to show an
  implication in the above definition instead of an equivalence.
\<close>

lemma stutter_invariantI [intro!]:
  assumes "\<And>\<sigma> \<tau>. \<lbrakk>\<sigma> \<approx> \<tau>; \<sigma> \<Turnstile>\<^sub>p \<phi>\<rbrakk> \<Longrightarrow> \<tau> \<Turnstile>\<^sub>p \<phi>"
  shows "stutter_invariant \<phi>"
proof -
  {
    fix \<sigma> \<tau>
    assume st: "\<sigma> \<approx> \<tau>" and f: "\<sigma> \<Turnstile>\<^sub>p \<phi>"
    hence "\<tau> \<Turnstile>\<^sub>p \<phi>" by (rule assms)
  }
moreover
  {
    fix \<sigma> \<tau>
    assume st: "\<sigma> \<approx> \<tau>" and f: "\<tau> \<Turnstile>\<^sub>p \<phi>"
    from st have "\<tau> \<approx> \<sigma>" by (rule stutter_equiv_sym)
    from this f have "\<sigma> \<Turnstile>\<^sub>p \<phi>" by (rule assms)
  }
ultimately show ?thesis by (auto simp: stutter_invariant_def)
qed

lemma stutter_invariantD [dest]:
  assumes "stutter_invariant \<phi>" and "\<sigma> \<approx> \<tau>"
  shows "(\<sigma> \<Turnstile>\<^sub>p \<phi>) = (\<tau> \<Turnstile>\<^sub>p \<phi>)"
  using assms by (auto simp: stutter_invariant_def)

text \<open>
  We first show that next-free PLTL formulas are indeed stuttering invariant.
  The proof proceeds by straightforward induction on the syntax of PLTL formulas.
\<close>
theorem next_free_stutter_invariant:
  "next_free \<phi> \<Longrightarrow> stutter_invariant (\<phi>::'a pltl)"
proof (induct "\<phi>")
    show "stutter_invariant false\<^sub>p" by auto
next
  fix p :: "'a \<Rightarrow> bool"
  show "stutter_invariant (atom\<^sub>p(p))"
  proof
    fix \<sigma> \<tau>
    assume "\<sigma> \<approx> \<tau>" "\<sigma> \<Turnstile>\<^sub>p atom\<^sub>p(p)"
    thus "\<tau> \<Turnstile>\<^sub>p atom\<^sub>p(p)" by (simp add: stutter_equiv_0)
  qed
next
  fix \<phi> \<psi> :: "'a pltl"
  assume ih: "next_free \<phi> \<Longrightarrow> stutter_invariant \<phi>"
             "next_free \<psi> \<Longrightarrow> stutter_invariant \<psi>"
  assume "next_free (\<phi> implies\<^sub>p \<psi>)"
  with ih show "stutter_invariant (\<phi> implies\<^sub>p \<psi>)" by auto
next
  fix \<phi> :: "'a pltl"
  assume "next_free (X\<^sub>p \<phi>)"  \<comment> \<open>hence contradiction\<close>
  thus "stutter_invariant (X\<^sub>p \<phi>)" by simp
next
  fix \<phi> \<psi> :: "'a pltl"
  assume ih: "next_free \<phi> \<Longrightarrow> stutter_invariant \<phi>"
             "next_free \<psi> \<Longrightarrow> stutter_invariant \<psi>"
  assume "next_free (\<phi> U\<^sub>p \<psi>)"
  with ih have stinv: "stutter_invariant \<phi>" "stutter_invariant \<psi>" by auto
  show "stutter_invariant (\<phi> U\<^sub>p \<psi>)"
  proof
    fix \<sigma> \<tau>
    assume st: "\<sigma> \<approx> \<tau>" and unt: "\<sigma> \<Turnstile>\<^sub>p \<phi> U\<^sub>p \<psi>"
    from unt obtain m
      where 1: "\<sigma>[m..] \<Turnstile>\<^sub>p \<psi>" and 2: "\<forall>j<m. (\<sigma>[j..] \<Turnstile>\<^sub>p \<phi>)" by auto
    from st obtain n
      where 3: "(\<sigma>[m..]) \<approx> (\<tau>[n..])" and 4: "\<forall>i<n. \<exists>j<m. (\<sigma>[j..]) \<approx> (\<tau>[i..])"
      by (rule stutter_equiv_suffixes_right)
    from 1 3 stinv have "\<tau>[n..] \<Turnstile>\<^sub>p \<psi>" by auto
    moreover
    from 2 4 stinv have "\<forall>i<n. (\<tau>[i..] \<Turnstile>\<^sub>p \<phi>)" by force
    ultimately show "\<tau> \<Turnstile>\<^sub>p \<phi> U\<^sub>p \<psi>" by auto
  qed
qed


subsection \<open>Atoms, Canonical State Sequences, and Characteristic Formulas\<close>

text \<open>
  We now address the converse implication: any stutter invariant PLTL
  formula \<open>\<phi>\<close> can be equivalently expressed by a next-free formula.
  The construction of that formula requires attention to the atomic
  formulas that appear in \<open>\<phi>\<close>. We will also prove that the
  next-free formula does not need any new atoms beyond those present
  in \<open>\<phi>\<close>.

  The following function collects the atoms (of type \<open>'a \<Rightarrow> bool\<close>)
  of a PLTL formula.
\<close>


lemma atoms_pltl_OR [simp]:
  assumes fin: "finite (\<Phi>::'a pltl set)"
  shows "atoms_pltl (OR \<Phi>) = (\<Union>\<phi>\<in>\<Phi>. atoms_pltl \<phi>)"
proof -
  {
    fix \<psi>::"'a pltl"
    assume "fold_graph Or_ltlp False_ltlp \<Phi> \<psi>"
    hence "atoms_pltl \<psi> = (\<Union>\<phi>\<in>\<Phi>. atoms_pltl \<phi>)"
      by (rule fold_graph.induct) auto
  }
  with fold_graph_OR[OF fin] show ?thesis by simp
qed

lemma atoms_pltl_AND [simp]:
  assumes fin: "finite (\<Phi>::'a pltl set)"
  shows "atoms_pltl (AND \<Phi>) = (\<Union>\<phi>\<in>\<Phi>. atoms_pltl \<phi>)"
proof -
  {
    fix \<psi>::"'a pltl"
    assume "fold_graph And_ltlp True_ltlp \<Phi> \<psi>"
    hence "atoms_pltl \<psi> = (\<Union>\<phi>\<in>\<Phi>. atoms_pltl \<phi>)"
      by (rule fold_graph.induct) auto
  }
  with fold_graph_AND[OF fin] show ?thesis by simp
qed

text \<open>
  Given a set of atoms \<open>A\<close> as above, we say that two states
  are \<open>A\<close>-similar if they agree on all atoms in \<open>A\<close>.
  Two state sequences \<open>\<sigma>\<close> and \<open>\<tau>\<close> are \<open>A\<close>-similar
  if corresponding states are \<open>A\<close>-equal.
\<close>

definition state_sim :: "['a, ('a \<Rightarrow> bool) set, 'a] \<Rightarrow> bool" 
  ("_ ~_~ _" [70,100,70] 50) where
  "s ~A~ t = (\<forall>p\<in>A. p s \<longleftrightarrow> p t)"

definition seq_sim :: "[nat \<Rightarrow> 'a, ('a \<Rightarrow> bool) set, nat \<Rightarrow> 'a] \<Rightarrow> bool"
  ("_ \<simeq>_\<simeq> _" [70,100,70] 50)  where
  "\<sigma> \<simeq>A\<simeq> \<tau> = (\<forall>n. (\<sigma> n) ~A~ (\<tau> n))"

text \<open>
  These relations are (indexed) equivalence relations. Moreover
  \<open>s ~A~ t\<close> implies \<open>s ~B~ t\<close> for \<open>B \<subseteq> A\<close>,
  and similar for \<open>\<sigma> \<simeq>A\<simeq> \<tau>\<close> and \<open>\<sigma> \<simeq>B\<simeq> \<tau>\<close>.
\<close>

lemma state_sim_refl [simp]: "s ~A~ s"
  by (simp add: state_sim_def)

lemma state_sim_sym: "s ~A~ t \<Longrightarrow> t ~A~ s"
  by (auto simp: state_sim_def)

lemma state_sim_trans[trans]: "s ~A~ t \<Longrightarrow> t ~A~ u \<Longrightarrow> s ~A~ u"
  unfolding state_sim_def by blast

lemma state_sim_mono:
  assumes "s ~A~ t" and "B \<subseteq> A"
  shows "s ~B~ t"
  using assms unfolding state_sim_def by auto

lemma seq_sim_refl [simp]: "\<sigma> \<simeq>A\<simeq> \<sigma>"
  by (simp add: seq_sim_def)

lemma seq_sim_sym: "\<sigma> \<simeq>A\<simeq> \<tau> \<Longrightarrow> \<tau> \<simeq>A\<simeq> \<sigma>"
  by (auto simp: seq_sim_def state_sim_sym)

lemma seq_sim_trans[trans]: "\<rho> \<simeq>A\<simeq> \<sigma> \<Longrightarrow> \<sigma> \<simeq>A\<simeq> \<tau> \<Longrightarrow> \<rho> \<simeq>A\<simeq> \<tau>"
  unfolding seq_sim_def by (blast intro: state_sim_trans)

lemma seq_sim_mono:
  assumes "\<sigma> \<simeq>A\<simeq> \<tau>" and "B \<subseteq> A"
  shows "\<sigma> \<simeq>B\<simeq> \<tau>"
  using assms unfolding seq_sim_def by (blast intro: state_sim_mono)

text \<open>
  State sequences that are similar w.r.t. the atoms of a PLTL formula
  evaluate that formula to the same value.  
\<close>

lemma pltl_seq_sim: "\<sigma> \<simeq> atoms_pltl \<phi> \<simeq> \<tau> \<Longrightarrow> (\<sigma> \<Turnstile>\<^sub>p \<phi>) = (\<tau> \<Turnstile>\<^sub>p \<phi>)"
  (is "?sim \<sigma> \<phi> \<tau> \<Longrightarrow> ?P \<sigma> \<phi> \<tau>")
proof (induct \<phi> arbitrary: \<sigma> \<tau>)
  fix \<sigma> \<tau>
  show "?P \<sigma> false\<^sub>p \<tau>" by simp
next
  fix p \<sigma> \<tau>
  assume "?sim \<sigma> (atom\<^sub>p(p)) \<tau>" thus "?P \<sigma> (atom\<^sub>p(p)) \<tau>"
    by (auto simp: seq_sim_def state_sim_def)
next
  fix \<phi> \<psi> \<sigma> \<tau>
  assume ih: "\<And>\<sigma> \<tau>. ?sim \<sigma> \<phi> \<tau> \<Longrightarrow> ?P \<sigma> \<phi> \<tau>" 
             "\<And>\<sigma> \<tau>. ?sim \<sigma> \<psi> \<tau> \<Longrightarrow> ?P \<sigma> \<psi> \<tau>"
     and sim: "?sim \<sigma> (\<phi> implies\<^sub>p \<psi>) \<tau>"
  from sim have "?sim \<sigma> \<phi> \<tau>" "?sim \<sigma> \<psi> \<tau>"
    by (auto elim: seq_sim_mono)
  with ih show "?P \<sigma> (\<phi> implies\<^sub>p \<psi>) \<tau>" by simp
next
  fix \<phi> \<sigma> \<tau>
  assume ih: "\<And>\<sigma> \<tau>. ?sim \<sigma> \<phi> \<tau> \<Longrightarrow> ?P \<sigma> \<phi> \<tau>"
     and sim: "\<sigma> \<simeq> atoms_pltl (X\<^sub>p \<phi>) \<simeq> \<tau>"
  from sim have "(\<sigma>[1..]) \<simeq> atoms_pltl \<phi> \<simeq> (\<tau>[1..])"
    by (auto simp: seq_sim_def)
  with ih show "?P \<sigma> (X\<^sub>p \<phi>) \<tau>" by auto
next
  fix \<phi> \<psi> \<sigma> \<tau>
  assume ih: "\<And>\<sigma> \<tau>. ?sim \<sigma> \<phi> \<tau> \<Longrightarrow> ?P \<sigma> \<phi> \<tau>" 
             "\<And>\<sigma> \<tau>. ?sim \<sigma> \<psi> \<tau> \<Longrightarrow> ?P \<sigma> \<psi> \<tau>"
     and sim: "?sim \<sigma> (\<phi> U\<^sub>p \<psi>) \<tau>"
  from sim have "\<forall>i. (\<sigma>[i..]) \<simeq> atoms_pltl \<phi> \<simeq> (\<tau>[i..])" "\<forall>j. (\<sigma>[j..]) \<simeq> atoms_pltl \<psi> \<simeq> (\<tau>[j..])"
    by (auto simp: seq_sim_def state_sim_def)
  with ih have "\<forall>i. ?P (\<sigma>[i..]) \<phi> (\<tau>[i..])" "\<forall>j. ?P (\<sigma>[j..]) \<psi> (\<tau>[j..])"
    by blast+
  thus "?P \<sigma> (\<phi> U\<^sub>p \<psi>) \<tau>"
    by (meson semantics_pltl.simps(5))
qed

text \<open>
  The following function picks an arbitrary representative among
  \<open>A\<close>-similar states. Because the choice is functional,
  any two \<open>A\<close>-similar states are mapped to the same state.
\<close>

definition canonize where
  "canonize A s \<equiv> SOME t. t ~A~ s"

lemma canonize_state_sim: "canonize A s ~A~ s"
  unfolding canonize_def by (rule someI, rule state_sim_refl)

lemma canonize_canonical:
  assumes st: "s ~A~ t"
  shows "canonize A s = canonize A t"
proof -
  from st have "\<forall>u. (u ~A~s) = (u ~A~ t)"
    by (auto elim: state_sim_sym state_sim_trans)
  thus ?thesis unfolding canonize_def by simp
qed

lemma canonize_idempotent:
  "canonize A (canonize A s) = canonize A s"
  by (rule canonize_canonical[OF canonize_state_sim])

text \<open>
  In a canonical state sequence, any two \<open>A\<close>-similar states
  are in fact equal.
\<close>

definition canonical_sequence where
  "canonical_sequence A \<sigma> \<equiv> \<forall>m (n::nat). \<sigma> m ~A~ \<sigma> n \<longrightarrow> \<sigma> m = \<sigma> n"

text \<open>
  Every suffix of a canonical sequence is canonical, as is any
  (sampled) subsequence, in particular any stutter-sampling.
\<close>

lemma canonical_suffix:
  "canonical_sequence A \<sigma> \<Longrightarrow> canonical_sequence A (\<sigma>[k..])"
  by (auto simp: canonical_sequence_def)

lemma canonical_sampled:
  "canonical_sequence A \<sigma> \<Longrightarrow> canonical_sequence A (\<sigma> \<circ> f)"
  by (auto simp: canonical_sequence_def)

lemma canonical_reduced:
  "canonical_sequence A \<sigma> \<Longrightarrow> canonical_sequence A (\<natural>\<sigma>)"
  unfolding stutter_reduced_def by (rule canonical_sampled)

text \<open>
  For any sequence \<open>\<sigma>\<close> there exists a canonical
  \<open>A\<close>-similar sequence \<open>\<tau>\<close>. Such a \<open>\<tau>\<close>
  can be obtained by canonizing all states of \<open>\<sigma>\<close>.
\<close>

lemma canonical_exists:
  obtains \<tau> where "\<tau> \<simeq>A\<simeq> \<sigma>" "canonical_sequence A \<tau>"
proof -
  have "(canonize A \<circ> \<sigma>) \<simeq>A\<simeq> \<sigma>"
    by (simp add: seq_sim_def canonize_state_sim)
  moreover
  have "canonical_sequence A (canonize A \<circ> \<sigma>)"
    by (auto simp: canonical_sequence_def canonize_idempotent
             dest: canonize_canonical)
  ultimately
  show ?thesis using that by blast
qed

text \<open>
  Given a state \<open>s\<close> and a set \<open>A\<close> of atoms, we define
  the characteristic formula of \<open>s\<close> as the conjunction of
  all atoms in \<open>A\<close> that hold of \<open>s\<close> and the negation of
  the atoms in \<open>A\<close> that do not hold of \<open>s\<close>.
\<close>

definition characteristic_formula where
  "characteristic_formula A s \<equiv>
   ((AND { atom\<^sub>p(p) | p . p \<in> A \<and> p s }) and\<^sub>p (AND { not\<^sub>p (atom\<^sub>p(p)) | p . p \<in> A \<and> \<not>(p s) }))"

lemma characteristic_holds: 
  "finite A \<Longrightarrow> \<sigma> \<Turnstile>\<^sub>p characteristic_formula A (\<sigma> 0)"
  by (auto simp: characteristic_formula_def)

lemma characteristic_state_sim:
  assumes fin: "finite A"
  shows "(\<sigma> 0 ~A~ \<tau> 0) = (\<tau> \<Turnstile>\<^sub>p characteristic_formula A (\<sigma> (0::nat)))"
proof
  assume sim: "\<sigma> 0 ~A~ \<tau> 0"
  {
    fix p
    assume "p \<in> A"
    with sim have "p (\<tau> 0) = p (\<sigma> 0)" by (auto simp: state_sim_def)
  }
  with fin show "\<tau> \<Turnstile>\<^sub>p characteristic_formula A (\<sigma> 0)"
    by (auto simp: characteristic_formula_def) (blast+)
next
  assume "\<tau> \<Turnstile>\<^sub>p characteristic_formula A (\<sigma> 0)"
  with fin show "\<sigma> 0 ~A~ \<tau> 0"
    by (auto simp: characteristic_formula_def state_sim_def)
qed


subsection \<open>Stuttering Invariant PLTL Formulas Don't Need Next\<close>

text \<open>
  The following is the main lemma used in the proof of the
  completeness theorem: for any PLTL formula \<open>\<phi>\<close> there
  exists a next-free formula \<open>\<psi>\<close> such that the two
  formulas evaluate to the same value over stutter-free and
  canonical sequences (w.r.t. some \<open>A \<supseteq> atoms_pltl \<phi>\<close>).
\<close>

lemma ex_next_free_stutter_free_canonical:
  assumes A: "atoms_pltl \<phi> \<subseteq> A" and fin: "finite A"
  shows "\<exists>\<psi>. next_free \<psi> \<and> atoms_pltl \<psi> \<subseteq> A \<and>
             (\<forall>\<sigma>. stutter_free \<sigma> \<and> canonical_sequence A \<sigma> \<longrightarrow> (\<sigma> \<Turnstile>\<^sub>p \<psi>) = (\<sigma> \<Turnstile>\<^sub>p \<phi>))"
    (is "\<exists>\<psi>. ?P \<phi> \<psi>")
using A proof (induct \<phi>)
  txt \<open>The cases of \<open>false\<close> and atomic formulas are trivial.\<close>
  have "?P false\<^sub>p false\<^sub>p" by auto
  thus "\<exists>\<psi>. ?P false\<^sub>p \<psi>" ..
next
  fix p
  assume "atoms_pltl (atom\<^sub>p(p)) \<subseteq> A"
  hence "?P (atom\<^sub>p(p)) (atom\<^sub>p(p))" by auto
  thus "\<exists>\<psi>. ?P (atom\<^sub>p(p)) \<psi>" ..
next
  txt \<open>Implication is easy, using the induction hypothesis.\<close>
  fix \<phi> \<psi>
  assume "atoms_pltl \<phi> \<subseteq> A \<Longrightarrow> \<exists>\<phi>'. ?P \<phi> \<phi>'"
     and "atoms_pltl \<psi> \<subseteq> A \<Longrightarrow> \<exists>\<psi>'. ?P \<psi> \<psi>'"
     and "atoms_pltl (\<phi> implies\<^sub>p \<psi>) \<subseteq> A"
  then obtain \<phi>' \<psi>' where "?P \<phi> \<phi>'" "?P \<psi> \<psi>'" by auto
  hence "?P (\<phi> implies\<^sub>p \<psi>) (\<phi>' implies\<^sub>p \<psi>')" by auto
  thus "\<exists>\<chi>. ?P (\<phi> implies\<^sub>p \<psi>) \<chi>" ..
next
  txt \<open>The case of \<open>until\<close> follows similarly.\<close>
  fix \<phi> \<psi>
  assume "atoms_pltl \<phi> \<subseteq> A \<Longrightarrow> \<exists>\<phi>'. ?P \<phi> \<phi>'"
     and "atoms_pltl \<psi> \<subseteq> A \<Longrightarrow> \<exists>\<psi>'. ?P \<psi> \<psi>'"
     and "atoms_pltl (\<phi> U\<^sub>p \<psi>) \<subseteq> A"
  then obtain \<phi>' \<psi>' where 1: "?P \<phi> \<phi>'" and 2: "?P \<psi> \<psi>'" by auto
  {
    fix \<sigma>
    assume sigma: "stutter_free \<sigma>" "canonical_sequence A \<sigma>"
    hence "\<And>k. stutter_free (\<sigma>[k..])" "\<And>k. canonical_sequence A (\<sigma>[k..])"
      by (auto simp: stutter_free_suffix canonical_suffix)
    with 1 2 
    have "\<And>k. (\<sigma>[k..] \<Turnstile>\<^sub>p \<phi>') = (\<sigma>[k..] \<Turnstile>\<^sub>p \<phi>)"
     and "\<And>k. (\<sigma>[k..] \<Turnstile>\<^sub>p \<psi>') = (\<sigma>[k..] \<Turnstile>\<^sub>p \<psi>)"
      by (blast+)
    hence "(\<sigma> \<Turnstile>\<^sub>p \<phi>' U\<^sub>p \<psi>') = (\<sigma> \<Turnstile>\<^sub>p \<phi> U\<^sub>p \<psi>)"
      by auto
  }
  with 1 2 have "?P (\<phi> U\<^sub>p \<psi>) (\<phi>' U\<^sub>p \<psi>')" by auto
  thus "\<exists>\<chi>. ?P (\<phi> U\<^sub>p \<psi>) \<chi>" ..
next
  txt \<open>The interesting case is the one of the \<open>next\<close>-operator.\<close>
  fix \<phi>
  assume ih: "atoms_pltl \<phi> \<subseteq> A \<Longrightarrow> \<exists>\<psi>. ?P \<phi> \<psi>" and at: "atoms_pltl (X\<^sub>p \<phi>) \<subseteq> A"
  then obtain \<psi> where psi: "?P \<phi> \<psi>" by auto
  txt \<open>A valuation (over \<open>A\<close>) is a set \<open>val \<subseteq> A\<close> of atoms. We
    define some auxiliary notions: the valuation corresponding to a state and
    the characteristic formula for a valuation. Finally, we define the formula
    \<open>psi'\<close> that we will prove to be equivalent to \<open>X\<^sub>p \<phi>\<close> over
    the stutter-free and canonical sequence \<open>\<sigma>\<close>.\<close>
  define stval where "stval = (\<lambda>s. { p \<in> A . p s })"
  define chi where "chi = (\<lambda>val. ((AND {atom\<^sub>p(p) | p . p \<in> val}) and\<^sub>p
                        (AND {not\<^sub>p (atom\<^sub>p(p)) | p . p \<in> A - val})))"
  define psi' where "psi' = ((\<psi> and\<^sub>p (OR {G\<^sub>p (chi val) | val . val \<subseteq> A })) or\<^sub>p
                  (OR {(chi val) and\<^sub>p ((chi val) U\<^sub>p ( \<psi> and\<^sub>p (chi val'))) | val val'.
                        val \<subseteq> A \<and> val' \<subseteq> A \<and> val' \<noteq> val }))"
        (is "_ = (( _ and\<^sub>p (OR ?ALW)) or\<^sub>p (OR ?UNT))")

  have "\<And>s. {not\<^sub>p (atom\<^sub>p(p)) | p . p \<in> A - stval s}
           = {not\<^sub>p (atom\<^sub>p(p)) | p . p \<in> A \<and> \<not>(p s)}"
    by (auto simp: stval_def)
  hence chi1: "\<And>s. chi (stval s) = characteristic_formula A s"
    by (auto simp: chi_def stval_def characteristic_formula_def)
  {
    fix val \<tau>
    assume val: "val \<subseteq> A" and tau: "\<tau> \<Turnstile>\<^sub>p chi val"
    with fin have "val = stval (\<tau> 0)"
      by (auto simp: stval_def chi_def finite_subset)
  }
  note chi2 = this

  have "?UNT \<subseteq> (\<lambda>(val,val'). (chi val) and\<^sub>p ((chi val) U\<^sub>p (\<psi> and\<^sub>p (chi val'))))
               ` (Pow A \<times> Pow A)"
    (is "_ \<subseteq> ?S")
    by auto
  with fin have fin_UNT: "finite ?UNT"
    by (auto simp: finite_subset)

  have nf: "next_free psi'"
  proof -
    from fin have "\<And>val. val \<subseteq> A \<Longrightarrow> next_free (chi val)"
      by (auto simp: chi_def finite_subset)
    with fin fin_UNT psi show ?thesis
      by (force simp: psi'_def finite_subset)
  qed

  have atoms_pltl: "atoms_pltl psi' \<subseteq> A"
  proof -
    from fin have at_chi: "\<And>val. val \<subseteq> A \<Longrightarrow> atoms_pltl (chi val) \<subseteq> A"
      by (auto simp: chi_def finite_subset)
    with fin psi have at_alw: "atoms_pltl (\<psi> and\<^sub>p (OR ?ALW)) \<subseteq> A"
      by auto blast?    (** FRAGILE: auto leaves trivial goal about subset **)
    from fin fin_UNT psi at_chi have "atoms_pltl (OR ?UNT) \<subseteq> A"
      by auto (blast+)? (** FRAGILE: even more left-over goals here **)
    with at_alw show ?thesis by (auto simp: psi'_def)
  qed

  {
    fix \<sigma>
    assume st: "stutter_free \<sigma>" and can: "canonical_sequence A \<sigma>"
    have "(\<sigma> \<Turnstile>\<^sub>p X\<^sub>p \<phi>) = (\<sigma> \<Turnstile>\<^sub>p psi')"
    proof (cases "\<sigma> (Suc 0) = \<sigma> 0")
      case True
      txt \<open>In the case of a stuttering transition at the beginning, we must have
        infinite stuttering, and the first disjunct of \<open>psi'\<close> holds,
        whereas the second does not.\<close>
      {
        fix n
        have "\<sigma> n = \<sigma> 0"
        proof (cases n)
          case 0 thus ?thesis by simp
        next
          case Suc
          hence "n > 0" by simp
          with True st show ?thesis unfolding stutter_free_def by blast
        qed
      }
      note alleq = this
      have suffix: "\<And>n. \<sigma>[n..] = \<sigma>"
      proof (rule ext)
        fix n i
        have "(\<sigma>[n..]) i = \<sigma> 0" by (auto intro: alleq)
        moreover have "\<sigma> i = \<sigma> 0" by (rule alleq)
        ultimately show "(\<sigma>[n..]) i = \<sigma> i" by simp
      qed
      with st can psi have 1: "(\<sigma> \<Turnstile>\<^sub>p X\<^sub>p \<phi>) = (\<sigma> \<Turnstile>\<^sub>p \<psi>)" by simp

      from fin have "\<sigma> \<Turnstile>\<^sub>p chi (stval (\<sigma> 0))" by (simp add: chi1 characteristic_holds)
      with suffix have "\<sigma> \<Turnstile>\<^sub>p G\<^sub>p (chi (stval (\<sigma> 0)))" (is "_ \<Turnstile>\<^sub>p ?alw") by simp
      moreover have "?alw \<in> ?ALW" by (auto simp: stval_def)
      ultimately have 2: "\<sigma> \<Turnstile>\<^sub>p OR ?ALW"
        using fin by (auto simp: finite_subset simp del: semantics_pltl_sugar)

      have 3: "\<not>(\<sigma> \<Turnstile>\<^sub>p OR ?UNT)"
      proof
        assume unt: "\<sigma> \<Turnstile>\<^sub>p OR ?UNT"
        with fin_UNT obtain val val' k where
          val: "val \<subseteq> A" "val' \<subseteq> A" "val' \<noteq> val" and
          now: "\<sigma> \<Turnstile>\<^sub>p chi val" and k: "\<sigma>[k..] \<Turnstile>\<^sub>p chi val'"
          by auto (blast+)?  (* FRAGILE: similar as above *)
        from \<open>val \<subseteq> A\<close> now have "val = stval (\<sigma> 0)" by (rule chi2)
        moreover
        from \<open>val' \<subseteq> A\<close> k suffix have "val' = stval (\<sigma> 0)" by (simp add: chi2)
        moreover note \<open>val' \<noteq> val\<close>
        ultimately show "False" by simp
      qed

      from 1 2 3 show ?thesis by (simp add: psi'_def)

    next
      case False
      txt \<open>Otherwise, \<open>\<sigma> \<Turnstile>\<^sub>p X\<^sub>p \<phi>\<close> is equivalent to \<open>\<sigma>\<close> satisfying
        the second disjunct of \<open>psi'\<close>. We show both implications separately.\<close>
      let ?val = "stval (\<sigma> 0)"
      let ?val' = "stval (\<sigma> 1)"
      from False can have vals: "?val' \<noteq> ?val"
        by (auto simp: canonical_sequence_def state_sim_def stval_def)
        
      show ?thesis
      proof
        assume phi: "\<sigma> \<Turnstile>\<^sub>p X\<^sub>p \<phi>"
        from fin have 1: "\<sigma> \<Turnstile>\<^sub>p chi ?val" by (simp add: chi1 characteristic_holds)

        from st can have "stutter_free (\<sigma>[1..])" "canonical_sequence A (\<sigma>[1..])"
          by (auto simp: stutter_free_suffix canonical_suffix)
        with phi psi have 2: "\<sigma>[1..] \<Turnstile>\<^sub>p \<psi>" by auto

        from fin have "\<sigma>[1..] \<Turnstile>\<^sub>p characteristic_formula A ((\<sigma>[1..]) 0)"
          by (rule characteristic_holds)
        hence 3: "\<sigma>[1..] \<Turnstile>\<^sub>p chi ?val'" by (simp add: chi1)

        from 1 2 3 have "\<sigma> \<Turnstile>\<^sub>p And_ltlp (chi ?val) ((chi ?val) U\<^sub>p (And_ltlp \<psi> (chi ?val')))"
          (is "_ \<Turnstile>\<^sub>p ?unt")
          by auto
        moreover from vals have "?unt \<in> ?UNT"
          by (auto simp: stval_def)
        ultimately have "\<sigma> \<Turnstile>\<^sub>p OR ?UNT"
          using fin_UNT[THEN holds_of_OR] by blast
        thus "\<sigma> \<Turnstile>\<^sub>p psi'" by (simp add: psi'_def)

      next
        assume psi': "\<sigma> \<Turnstile>\<^sub>p psi'"
        have "\<not>(\<sigma> \<Turnstile>\<^sub>p OR ?ALW)"
        proof
          assume "\<sigma> \<Turnstile>\<^sub>p OR ?ALW"
          with fin obtain val where 1: "val \<subseteq> A" and 2: "\<forall>n. (\<sigma>[n..] \<Turnstile>\<^sub>p chi val)"
            by (force simp: finite_subset)
          from 2 have "\<sigma>[0..] \<Turnstile>\<^sub>p chi val" ..
          with 1 have "val = ?val" by (simp add: chi2)
          moreover
          from 2 have "\<sigma>[1..] \<Turnstile>\<^sub>p chi val" ..
          with 1 have "val = ?val'" by (force dest: chi2)
          ultimately
          show "False" using vals by simp
        qed
        with psi' have "\<sigma> \<Turnstile>\<^sub>p OR ?UNT" by (simp add: psi'_def)
        with fin_UNT obtain val val' k where
          val: "val \<subseteq> A" "val' \<subseteq> A" "val' \<noteq> val" and
          now: "\<sigma> \<Turnstile>\<^sub>p chi val" and
          k: "\<sigma>[k..] \<Turnstile>\<^sub>p \<psi>" "\<sigma>[k..] \<Turnstile>\<^sub>p chi val'" and
          i: "\<forall>i<k. (\<sigma>[i..] \<Turnstile>\<^sub>p chi val)"
          by auto (blast+)?  (* FRAGILE: similar as above *)

        from val now have 1: "val = ?val" by (simp add: chi2)

        have 2: "k \<noteq> 0"
        proof
          assume "k=0"
          with val k have "val' = ?val" by (simp add: chi2)
          with 1 \<open>val' \<noteq> val\<close> show "False" by simp
        qed

        have 3: "k \<le> 1"
        proof (rule ccontr)
          assume "\<not>(k \<le> 1)"
          with i have "\<sigma>[1..] \<Turnstile>\<^sub>p chi val" by simp
          with 1 have "\<sigma>[1..] \<Turnstile>\<^sub>p characteristic_formula A (\<sigma> 0)" 
            by (simp add: chi1)
          hence "(\<sigma> 0) ~A~ ((\<sigma>[1..]) 0)"
            using characteristic_state_sim[OF fin] by blast
          with can have "\<sigma> 0 = \<sigma> 1"
            by (simp add: canonical_sequence_def)
          with \<open>\<sigma> (Suc 0) \<noteq> \<sigma> 0\<close> show "False" by simp
        qed

        from 2 3 have "k=1" by simp
        moreover
        from st can have "stutter_free (\<sigma>[1..])" "canonical_sequence A (\<sigma>[1..])"
          by (auto simp: stutter_free_suffix canonical_suffix)
        ultimately show "\<sigma> \<Turnstile>\<^sub>p X\<^sub>p \<phi>" using \<open>\<sigma>[k..] \<Turnstile>\<^sub>p \<psi>\<close> psi by auto
      qed
    qed
  }
  with nf atoms_pltl show "\<exists>\<psi>'. ?P (X\<^sub>p \<phi>) \<psi>'" by blast
qed

text \<open>
  Comparing the definition of the next-free formula in the case of
  formulas \<open>X\<^sub>p \<phi>\<close> with the one that appears in~\cite{peled:ltl-x},
  there is a subtle difference. Peled and Wilke define the second disjunct as
  a disjunction of formulas
%
  \begin{center}\(
    \<open>(chi val) U\<^sub>p (\<psi> and\<^sub>p (chi val'))\<close>
  \)\end{center}
%
  for subsets \<open>val, val' \<subseteq> A\<close> whereas we conjoin the formula
  \<open>chi val\<close> to the ``until'' formula. This conjunct is indeed
  necessary in order to rule out the case of the ``until'' formula
  being true because of \<open>chi val'\<close> being true immediately.
  The subtle error in the definition of the formula was acknowledged 
  by Peled and Wilke and apparently had not been noticed since the 
  publication of~\cite{peled:ltl-x} in 1996 (which has been cited more
  than a hundred times according to Google Scholar). Although the error
  was corrected easily, the fact that authors, reviewers, and readers
  appear to have missed it for so long underscores the usefulness of
  formal proofs.

  We now show that any stuttering invariant PLTL formula
  can be expressed without the \<open>X\<^sub>p\<close> operator.
\<close>

theorem stutter_invariant_next_free:
  assumes phi: "stutter_invariant \<phi>"
  obtains \<psi> where "next_free \<psi>" "atoms_pltl \<psi> \<subseteq> atoms_pltl \<phi>"
                  "\<forall>\<sigma>. (\<sigma> \<Turnstile>\<^sub>p \<psi>) = (\<sigma> \<Turnstile>\<^sub>p \<phi>)"
proof -
  have "atoms_pltl \<phi> \<subseteq> atoms_pltl \<phi>" "finite (atoms_pltl \<phi>)" by simp_all
  then obtain \<psi> where
    psi: "next_free \<psi>" "atoms_pltl \<psi> \<subseteq> atoms_pltl \<phi>" and
    equiv: "\<forall>\<sigma>. stutter_free \<sigma> \<and> canonical_sequence (atoms_pltl \<phi>) \<sigma> \<longrightarrow> (\<sigma> \<Turnstile>\<^sub>p \<psi>) = (\<sigma> \<Turnstile>\<^sub>p \<phi>)"
    by (blast dest: ex_next_free_stutter_free_canonical)
  from \<open>next_free \<psi>\<close> have sinv: "stutter_invariant \<psi>"
    by (rule next_free_stutter_invariant)
  {
    fix \<sigma>
    obtain \<tau> where 1: "\<tau> \<simeq> atoms_pltl \<phi> \<simeq> \<sigma>" and 2: "canonical_sequence (atoms_pltl \<phi>) \<tau>"
      by (rule canonical_exists)
    from 1 \<open>atoms_pltl \<psi> \<subseteq> atoms_pltl \<phi>\<close> have 3: "\<tau> \<simeq> atoms_pltl \<psi> \<simeq> \<sigma>"
      by (rule seq_sim_mono)

    from 1 have "(\<sigma> \<Turnstile>\<^sub>p \<phi>) = (\<tau> \<Turnstile>\<^sub>p \<phi>)" by (simp add: pltl_seq_sim)
    also from phi stutter_reduced_equivalent have "... = (\<natural>\<tau> \<Turnstile>\<^sub>p \<phi>)" by auto
    also from 2[THEN canonical_reduced] equiv stutter_reduced_stutter_free 
    have "... = (\<natural>\<tau> \<Turnstile>\<^sub>p \<psi>)" by auto
    also from sinv stutter_reduced_equivalent have "... = (\<tau> \<Turnstile>\<^sub>p \<psi>)" by auto
    also from 3 have "... = (\<sigma> \<Turnstile>\<^sub>p \<psi>)" by (simp add: pltl_seq_sim)
    finally have "(\<sigma> \<Turnstile>\<^sub>p \<psi>) = (\<sigma> \<Turnstile>\<^sub>p \<phi>)" by (rule sym)
  }
  with psi that show ?thesis by blast
qed

text \<open>
  Combining theorems \<open>next_free_stutter_invariant\<close> and
  \<open>stutter_invariant_next_free\<close>, it follows that a PLTL
  formula is stuttering invariant iff it is equivalent to a next-free
  formula.
\<close>

theorem pltl_stutter_invariant:
  "stutter_invariant \<phi> \<longleftrightarrow> 
   (\<exists>\<psi>. next_free \<psi> \<and> atoms_pltl \<psi> \<subseteq> atoms_pltl \<phi> \<and> (\<forall>\<sigma>. \<sigma> \<Turnstile>\<^sub>p \<psi> \<longleftrightarrow> \<sigma> \<Turnstile>\<^sub>p \<phi>))"
proof -
  {
    assume "stutter_invariant \<phi>"
    hence "\<exists>\<psi>. next_free \<psi> \<and> atoms_pltl \<psi> \<subseteq> atoms_pltl \<phi> \<and> (\<forall>\<sigma>. \<sigma> \<Turnstile>\<^sub>p \<psi> \<longleftrightarrow> \<sigma> \<Turnstile>\<^sub>p \<phi>)"
      by (rule stutter_invariant_next_free) blast
  }
  moreover
  {
    fix \<psi>
    assume 1: "next_free \<psi>" and 2: "\<forall>\<sigma>. \<sigma> \<Turnstile>\<^sub>p \<psi> \<longleftrightarrow> \<sigma> \<Turnstile>\<^sub>p \<phi>"
    from 1 have "stutter_invariant \<psi>" by (rule next_free_stutter_invariant)
    with 2 have "stutter_invariant \<phi>" by blast
  }
  ultimately show ?thesis by blast
qed


subsection \<open>Stutter Invariance for LTL with Syntactic Sugar\<close>

text \<open>We lift the results for PLTL to an extensive version of LTL.\<close>

primrec ltlc_next_free :: "'a ltlc \<Rightarrow> bool"
  where
    "ltlc_next_free true\<^sub>c = True"
  | "ltlc_next_free false\<^sub>c = True"
  | "ltlc_next_free (prop\<^sub>c(q)) = True"
  | "ltlc_next_free (not\<^sub>c \<phi>) = ltlc_next_free \<phi>"
  | "ltlc_next_free (\<phi> and\<^sub>c \<psi>) = (ltlc_next_free \<phi> \<and> ltlc_next_free \<psi>)"
  | "ltlc_next_free (\<phi> or\<^sub>c \<psi>) = (ltlc_next_free \<phi> \<and> ltlc_next_free \<psi>)"
  | "ltlc_next_free (\<phi> implies\<^sub>c \<psi>) = (ltlc_next_free \<phi> \<and> ltlc_next_free \<psi>)"
  | "ltlc_next_free (X\<^sub>c \<phi>) = False"
  | "ltlc_next_free (F\<^sub>c \<phi>) = ltlc_next_free \<phi>"
  | "ltlc_next_free (G\<^sub>c \<phi>) = ltlc_next_free \<phi>"
  | "ltlc_next_free (\<phi> U\<^sub>c \<psi>) = (ltlc_next_free \<phi> \<and> ltlc_next_free \<psi>)"
  | "ltlc_next_free (\<phi> R\<^sub>c \<psi>) = (ltlc_next_free \<phi> \<and> ltlc_next_free \<psi>)"
  | "ltlc_next_free (\<phi> W\<^sub>c \<psi>) = (ltlc_next_free \<phi> \<and> ltlc_next_free \<psi>)"
  | "ltlc_next_free (\<phi> M\<^sub>c \<psi>) = (ltlc_next_free \<phi> \<and> ltlc_next_free \<psi>)"

lemma ltlc_next_free_iff[simp]: "next_free (ltlc_to_pltl \<phi>) \<longleftrightarrow> ltlc_next_free \<phi>"
  by (induction \<phi>) auto

text \<open>A next free formula cannot distinguish between stutter-equivalent runs.\<close>

theorem ltlc_next_free_stutter_invariant:
  assumes next_free: "ltlc_next_free \<phi>"
  assumes eq: "r \<approx> r'"
  shows "r \<Turnstile>\<^sub>c \<phi> \<longleftrightarrow> r' \<Turnstile>\<^sub>c \<phi>"
proof -
  {
    fix r r'
    assume eq: "r \<approx> r'" and holds: "r \<Turnstile>\<^sub>c \<phi>"
    then have "r \<Turnstile>\<^sub>p (ltlc_to_pltl \<phi>)"by simp

    from next_free_stutter_invariant[of "ltlc_to_pltl \<phi>"] next_free
    have "PLTL.stutter_invariant (ltlc_to_pltl \<phi>)" by simp
    from stutter_invariantD[OF this eq] holds have "r' \<Turnstile>\<^sub>c \<phi>" by simp
  } note aux=this

  from aux[of r r'] aux[of r' r] eq stutter_equiv_sym[OF eq] show ?thesis
    by blast
qed


end

