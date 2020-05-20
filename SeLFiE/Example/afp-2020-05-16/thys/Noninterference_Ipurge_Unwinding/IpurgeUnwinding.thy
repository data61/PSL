(*  Title:       The Ipurge Unwinding Theorem for CSP Noninterference Security
    Author:      Pasquale Noce
                 Security Certification Specialist at Arjo Systems - Gep S.p.A.
                 pasquale dot noce dot lavoro at gmail dot com
                 pasquale dot noce at arjowiggins-it dot com
*)

section "The Ipurge Unwinding Theorem in its general form"

theory IpurgeUnwinding
imports Noninterference_CSP.CSPNoninterference List_Interleaving.ListInterleaving
begin

text \<open>
\null

The definition of noninterference security for Communicating Sequential Processes given in \cite{R1}
requires to consider any possible future, i.e. any indefinitely long sequence of subsequent events
and any indefinitely large set of refused events associated to that sequence, for each process
trace. In order to render the verification of the security of a process more straightforward, there
is a need of some sufficient condition for security such that just individual accepted and refused
events, rather than unbounded sequences and sets of events, have to be considered.

Of course, if such a sufficient condition were necessary as well, it would be even more valuable,
since it would permit to prove not only that a process is secure by verifying that the condition
holds, but also that a process is not secure by verifying that the condition fails to hold.

This section provides a necessary and sufficient condition for CSP noninterference security, which
indeed requires to just consider individual accepted and refused events and applies to the general
case of a possibly intransitive policy. This condition follows Rushby's output consistency for
deterministic state machines with outputs \cite{R4}, and has to be satisfied by a specific function
mapping security domains into equivalence relations over process traces. The definition of this
function makes use of an intransitive purge function following Rushby's one; hence the name given to
the condition, \emph{Ipurge Unwinding Theorem}.

The contents of this paper are based on those of \cite{R1}. The salient points of definitions and
proofs are commented; for additional information, cf. Isabelle documentation, particularly
\cite{R5}, \cite{R6}, \cite{R7}, and \cite{R8}.

For the sake of brevity, given a function \<open>F\<close> of type
\<open>'a\<^sub>1 \<Rightarrow> \<dots> \<Rightarrow> 'a\<^sub>m \<Rightarrow> 'a\<^sub>m\<^sub>+\<^sub>1 \<Rightarrow> \<dots> \<Rightarrow> 'a\<^sub>n \<Rightarrow> 'b\<close>, the explanatory text may discuss of \<open>F\<close>
using attributes that would more exactly apply to a term of type \<open>'a\<^sub>m\<^sub>+\<^sub>1 \<Rightarrow> \<dots> \<Rightarrow> 'a\<^sub>n \<Rightarrow> 'b\<close>.
In this case, it shall be understood that strictly speaking, such attributes apply to a term
matching pattern \<open>F a\<^sub>1 \<dots> a\<^sub>m\<close>.
\<close>


subsection "Propaedeutic definitions and lemmas"

text \<open>
The definition of CSP noninterference security formulated in \cite{R1} requires that some sets of
events be refusals, i.e. sets of refused events, for some traces. Therefore, a sufficient condition
for security just involving individual refused events will require that some single events be
refused, viz. form singleton refusals, after the occurrence of some traces. However, such a
statement may actually be a sufficient condition for security just in the case of a process such
that the union of any set of singleton refusals for a given trace is itself a refusal for that
trace.

This turns out to be true if and only if the union of any set \emph{A} of refusals, not necessarily
singletons, is still a refusal. The direct implication is trivial. As regards the converse one, let
\emph{A'} be the set of the singletons included in some element of \emph{A}. Then, each element of
\emph{A'} is a singleton refusal by virtue of rule @{thm process_rule_3}, so that the union of the
elements of \emph{A'}, which is equal to the union of the elements of \emph{A}, is a refusal by
hypothesis.

This property, henceforth referred to as \emph{refusals union closure} and formalized in what
follows, clearly holds for any process admitting a meaningful interpretation, as it would be a
nonsense, in the case of a process modeling a real system, to say that some sets of events are
refused after the occurrence of a trace, but their union is not. Thus, taking the refusals union
closure of the process as an assumption for the equivalence between process security and a given
condition, as will be done in the Ipurge Unwinding Theorem, does not give rise to any actual
limitation on the applicability of such a result.

As for predicates \emph{view partition} and \emph{future consistent}, defined here below as well,
they translate Rushby's predicates \emph{view-partitioned} and \emph{output consistent} \cite{R4},
applying to deterministic state machines with outputs, into Hoare's Communicating Sequential
Processes model of computation \cite{R3}. The reason for the verbal difference between the active
form of predicate \emph{view partition} and the passive form of predicate \emph{view-partitioned} is
that the implied subject of the former is a domain-relation map rather than a process, whose
homologous in \cite{R4}, viz. a machine, is the implied subject of the latter predicate instead.

More remarkably, the formal differences with respect to Rushby's original predicates are the
following ones:

\begin{itemize}

\item
The relations in the range of the domain-relation map hold between event lists rather than machine
states.

\item
The domains appearing as inputs of the domain-relation map do not unnecessarily encompass all the
possible values of the data type of domains, but just the domains in the range of the event-domain
map.

\item
The equality of the outputs in domain \emph{u} produced by machine states equivalent for \emph{u},
as required by output consistency, is replaced by the equality of the events in domain \emph{u}
accepted or refused after the occurrence of event lists equivalent for \emph{u}; hence the name of
the property, \emph{future consistency}.

\end{itemize}

An additional predicate, \emph{weakly future consistent}, renders future consistency less strict by
requiring the equality of subsequent accepted and refused events to hold only for event domains not
allowed to be affected by some event domain.

\null
\<close>

type_synonym ('a, 'd) dom_rel_map = "'d \<Rightarrow> ('a list \<times> 'a list) set"

type_synonym ('a, 'd) domset_rel_map = "'d set \<Rightarrow> ('a list \<times> 'a list) set"

definition ref_union_closed :: "'a process \<Rightarrow> bool" where
"ref_union_closed P \<equiv>
  \<forall>xs A. (\<exists>X. X \<in> A) \<longrightarrow> (\<forall>X \<in> A. (xs, X) \<in> failures P) \<longrightarrow>
    (xs, \<Union>X \<in> A. X) \<in> failures P"

definition view_partition ::
 "'a process \<Rightarrow> ('a \<Rightarrow> 'd) \<Rightarrow> ('a, 'd) dom_rel_map \<Rightarrow> bool" where
"view_partition P D R \<equiv> \<forall>u \<in> range D. equiv (traces P) (R u)"

definition next_dom_events ::
 "'a process \<Rightarrow> ('a \<Rightarrow> 'd) \<Rightarrow> 'd \<Rightarrow> 'a list \<Rightarrow> 'a set" where
"next_dom_events P D u xs \<equiv> {x. u = D x \<and> x \<in> next_events P xs}"

definition ref_dom_events ::
 "'a process \<Rightarrow> ('a \<Rightarrow> 'd) \<Rightarrow> 'd \<Rightarrow> 'a list \<Rightarrow> 'a set" where
"ref_dom_events P D u xs \<equiv> {x. u = D x \<and> {x} \<in> refusals P xs}"

definition future_consistent ::
 "'a process \<Rightarrow> ('a \<Rightarrow> 'd) \<Rightarrow> ('a, 'd) dom_rel_map \<Rightarrow> bool" where
"future_consistent P D R \<equiv>
  \<forall>u \<in> range D. \<forall>xs ys. (xs, ys) \<in> R u \<longrightarrow>
    next_dom_events P D u xs = next_dom_events P D u ys \<and>
    ref_dom_events P D u xs = ref_dom_events P D u ys"

definition weakly_future_consistent ::
 "'a process \<Rightarrow> ('d \<times> 'd) set \<Rightarrow> ('a \<Rightarrow> 'd) \<Rightarrow> ('a, 'd) dom_rel_map \<Rightarrow> bool" where
"weakly_future_consistent P I D R \<equiv>
  \<forall>u \<in> range D \<inter> (-I) `` range D. \<forall>xs ys. (xs, ys) \<in> R u \<longrightarrow>
    next_dom_events P D u xs = next_dom_events P D u ys \<and>
    ref_dom_events P D u xs = ref_dom_events P D u ys"

text \<open>
\null

Here below are some lemmas propaedeutic for the proof of the Ipurge Unwinding Theorem, just
involving constants defined in \cite{R1}.

\null
\<close>

lemma process_rule_2_traces:
 "xs @ xs' \<in> traces P \<Longrightarrow> xs \<in> traces P"
proof (simp add: traces_def Domain_iff, erule exE, rule_tac x = "{}" in exI)
qed (rule process_rule_2_failures)

lemma process_rule_4 [rule_format]:
 "(xs, X) \<in> failures P \<longrightarrow> (xs @ [x], {}) \<in> failures P \<or> (xs, insert x X) \<in> failures P"
proof (simp add: failures_def)
  have "Rep_process P \<in> process_set" (is "?P' \<in> _") by (rule Rep_process)
  hence "\<forall>xs x X. (xs, X) \<in> fst ?P' \<longrightarrow>
    (xs @ [x], {}) \<in> fst ?P' \<or> (xs, insert x X) \<in> fst ?P'"
   by (simp add: process_set_def process_prop_4_def)
  thus "(xs, X) \<in> fst ?P' \<longrightarrow>
    (xs @ [x], {}) \<in> fst ?P' \<or> (xs, insert x X) \<in> fst ?P'"
   by blast
qed

lemma failures_traces:
 "(xs, X) \<in> failures P \<Longrightarrow> xs \<in> traces P"
by (simp add: traces_def Domain_iff, rule exI)

lemma traces_failures:
 "xs \<in> traces P \<Longrightarrow> (xs, {}) \<in> failures P"
proof (simp add: traces_def Domain_iff, erule exE)
qed (erule process_rule_3, simp)

lemma sinks_interference [rule_format]:
 "D x \<in> sinks I D u xs \<longrightarrow>
  (u, D x) \<in> I \<or> (\<exists>v \<in> sinks I D u xs. (v, D x) \<in> I)"
proof (induction xs rule: rev_induct, simp, rule impI)
  fix x' xs
  assume
    A: "D x \<in> sinks I D u xs \<longrightarrow>
      (u, D x) \<in> I \<or> (\<exists>v \<in> sinks I D u xs. (v, D x) \<in> I)" and
    B: "D x \<in> sinks I D u (xs @ [x'])"
  show "(u, D x) \<in> I \<or> (\<exists>v \<in> sinks I D u (xs @ [x']). (v, D x) \<in> I)"
  proof (cases "(u, D x') \<in> I \<or> (\<exists>v \<in> sinks I D u xs. (v, D x') \<in> I)")
    case True
    hence "D x = D x' \<or> D x \<in> sinks I D u xs" using B by simp
    moreover {
      assume C: "D x = D x'"
      have ?thesis using True
      proof (rule disjE, erule_tac [2] bexE)
        assume "(u, D x') \<in> I"
        hence "(u, D x) \<in> I" using C by simp
        thus ?thesis ..
      next
        fix v
        assume "(v, D x') \<in> I"
        hence "(v, D x) \<in> I" using C by simp
        moreover assume "v \<in> sinks I D u xs"
        hence "v \<in> sinks I D u (xs @ [x'])" by simp
        ultimately have "\<exists>v \<in> sinks I D u (xs @ [x']). (v, D x) \<in> I" ..
        thus ?thesis ..
      qed
    }
    moreover {
      assume "D x \<in> sinks I D u xs"
      with A have "(u, D x) \<in> I \<or> (\<exists>v \<in> sinks I D u xs. (v, D x) \<in> I)" ..
      hence ?thesis
      proof (rule disjE, erule_tac [2] bexE)
        assume "(u, D x) \<in> I"
        thus ?thesis ..
      next
        fix v
        assume "(v, D x) \<in> I"
        moreover assume "v \<in> sinks I D u xs"
        hence "v \<in> sinks I D u (xs @ [x'])" by simp
        ultimately have "\<exists>v \<in> sinks I D u (xs @ [x']). (v, D x) \<in> I" ..
        thus ?thesis ..
      qed
    }
    ultimately show ?thesis ..
  next
    case False
    hence C: "sinks I D u (xs @ [x']) = sinks I D u xs" by simp
    hence "D x \<in> sinks I D u xs" using B by simp
    with A have "(u, D x) \<in> I \<or> (\<exists>v \<in> sinks I D u xs. (v, D x) \<in> I)" ..
    thus ?thesis using C by simp
  qed
qed

lemma sinks_interference_eq:
 "((u, D x) \<in> I \<or> (\<exists>v \<in> sinks I D u xs. (v, D x) \<in> I)) =
  (D x \<in> sinks I D u (xs @ [x]))"
proof (rule iffI, erule_tac [2] contrapos_pp, simp_all (no_asm_simp))
qed (erule contrapos_nn, rule sinks_interference)

text \<open>
\null

In what follows, some lemmas concerning the constants defined above are proven.

In the definition of predicate @{term ref_union_closed}, the conclusion that the union of a set of
refusals is itself a refusal for the same trace is subordinated to the condition that the set of
refusals be nonempty. The first lemma shows that in the absence of this condition, the predicate
could only be satisfied by a process admitting any event list as a trace, which proves that the
condition must be present for the definition to be correct.

The subsequent lemmas prove that, for each domain \emph{u} in the ranges respectively taken into
consideration, the image of \emph{u} under a future consistent or weakly future consistent
domain-relation map may only correlate a pair of event lists such that either both are traces, or
both are not traces. Finally, it is demonstrated that future consistency implies weak future
consistency.

\null
\<close>

lemma
  assumes A: "\<forall>xs A. (\<forall>X \<in> A. (xs, X) \<in> failures P) \<longrightarrow>
    (xs, \<Union>X \<in> A. X) \<in> failures P"
  shows "\<forall>xs. xs \<in> traces P"
proof
  fix xs
  have "(\<forall>X \<in> {}. (xs, X) \<in> failures P) \<longrightarrow> (xs, \<Union>X \<in> {}. X) \<in> failures P"
   using A by blast
  moreover have "\<forall>X \<in> {}. (xs, X) \<in> failures P" by simp
  ultimately have "(xs, \<Union>X \<in> {}. X) \<in> failures P" ..
  thus "xs \<in> traces P" by (rule failures_traces)
qed

lemma traces_dom_events:
  assumes A: "u \<in> range D"
  shows "xs \<in> traces P =
    (next_dom_events P D u xs \<union> ref_dom_events P D u xs \<noteq> {})"
    (is "_ = (?S \<noteq> {})")
proof
  have "\<exists>x. u = D x" using A by (simp add: image_def)
  then obtain x where B: "u = D x" ..
  assume "xs \<in> traces P"
  hence "(xs, {}) \<in> failures P" by (rule traces_failures)
  hence "(xs @ [x], {}) \<in> failures P \<or> (xs, {x}) \<in> failures P" by (rule process_rule_4)
  moreover {
    assume "(xs @ [x], {}) \<in> failures P"
    hence "xs @ [x] \<in> traces P" by (rule failures_traces)
    hence "x \<in> next_dom_events P D u xs"
     using B by (simp add: next_dom_events_def next_events_def)
    hence "x \<in> ?S" ..
  }                                                    
  moreover {
    assume "(xs, {x}) \<in> failures P"
    hence "x \<in> ref_dom_events P D u xs"
     using B by (simp add: ref_dom_events_def refusals_def)
    hence "x \<in> ?S" ..
  }
  ultimately have "x \<in> ?S" ..
  hence "\<exists>x. x \<in> ?S" ..
  thus "?S \<noteq> {}" by (subst ex_in_conv [symmetric])
next
  assume "?S \<noteq> {}"
  hence "\<exists>x. x \<in> ?S" by (subst ex_in_conv)
  then obtain x where "x \<in> ?S" ..
  moreover {
    assume "x \<in> next_dom_events P D u xs"
    hence "xs @ [x] \<in> traces P" by (simp add: next_dom_events_def next_events_def)
    hence "xs \<in> traces P" by (rule process_rule_2_traces)
  }
  moreover {
    assume "x \<in> ref_dom_events P D u xs"
    hence "(xs, {x}) \<in> failures P" by (simp add: ref_dom_events_def refusals_def)
    hence "xs \<in> traces P" by (rule failures_traces)
  }
  ultimately show "xs \<in> traces P" ..
qed

lemma fc_traces:
  assumes
    A: "future_consistent P D R" and
    B: "u \<in> range D" and
    C: "(xs, ys) \<in> R u"
  shows "(xs \<in> traces P) = (ys \<in> traces P)"
proof -
  have "\<forall>u \<in> range D. \<forall>xs ys. (xs, ys) \<in> R u \<longrightarrow>
    next_dom_events P D u xs = next_dom_events P D u ys \<and>
    ref_dom_events P D u xs = ref_dom_events P D u ys"
   using A by (simp add: future_consistent_def)
  hence "\<forall>xs ys. (xs, ys) \<in> R u \<longrightarrow>
    next_dom_events P D u xs = next_dom_events P D u ys \<and>
    ref_dom_events P D u xs = ref_dom_events P D u ys"
   using B ..
  hence "(xs, ys) \<in> R u \<longrightarrow>
    next_dom_events P D u xs = next_dom_events P D u ys \<and>
    ref_dom_events P D u xs = ref_dom_events P D u ys"
   by blast
  hence "next_dom_events P D u xs = next_dom_events P D u ys \<and>
    ref_dom_events P D u xs = ref_dom_events P D u ys"
   using C ..
  hence "next_dom_events P D u xs \<union> ref_dom_events P D u xs \<noteq> {} =
    (next_dom_events P D u ys \<union> ref_dom_events P D u ys \<noteq> {})"
   by simp
  moreover have "xs \<in> traces P =
    (next_dom_events P D u xs \<union> ref_dom_events P D u xs \<noteq> {})"
   using B by (rule traces_dom_events)
  moreover have "ys \<in> traces P =
    (next_dom_events P D u ys \<union> ref_dom_events P D u ys \<noteq> {})"
   using B by (rule traces_dom_events)
  ultimately show ?thesis by simp
qed

lemma wfc_traces:
  assumes
    A: "weakly_future_consistent P I D R" and
    B: "u \<in> range D \<inter> (-I) `` range D" and
    C: "(xs, ys) \<in> R u"
  shows "(xs \<in> traces P) = (ys \<in> traces P)"
proof -
  have "\<forall>u \<in> range D \<inter> (-I) `` range D. \<forall>xs ys. (xs, ys) \<in> R u \<longrightarrow>
    next_dom_events P D u xs = next_dom_events P D u ys \<and>
    ref_dom_events P D u xs = ref_dom_events P D u ys"
   using A by (simp add: weakly_future_consistent_def)
  hence "\<forall>xs ys. (xs, ys) \<in> R u \<longrightarrow>
    next_dom_events P D u xs = next_dom_events P D u ys \<and>
    ref_dom_events P D u xs = ref_dom_events P D u ys"
   using B ..
  hence "(xs, ys) \<in> R u \<longrightarrow>
    next_dom_events P D u xs = next_dom_events P D u ys \<and>
    ref_dom_events P D u xs = ref_dom_events P D u ys"
   by blast
  hence "next_dom_events P D u xs = next_dom_events P D u ys \<and>
    ref_dom_events P D u xs = ref_dom_events P D u ys"
   using C ..
  hence "next_dom_events P D u xs \<union> ref_dom_events P D u xs \<noteq> {} =
    (next_dom_events P D u ys \<union> ref_dom_events P D u ys \<noteq> {})"
   by simp
  moreover have B': "u \<in> range D" using B ..
  hence "xs \<in> traces P =
    (next_dom_events P D u xs \<union> ref_dom_events P D u xs \<noteq> {})"
   by (rule traces_dom_events)
  moreover have "ys \<in> traces P =
    (next_dom_events P D u ys \<union> ref_dom_events P D u ys \<noteq> {})"
   using B' by (rule traces_dom_events)
  ultimately show ?thesis by simp
qed

lemma fc_implies_wfc:
 "future_consistent P D R \<Longrightarrow> weakly_future_consistent P I D R"
by (simp only: future_consistent_def weakly_future_consistent_def, blast)

text \<open>
\null

Finally, the definition is given of an auxiliary function \<open>singleton_set\<close>, whose output is the
set of the singleton subsets of a set taken as input, and then some basic properties of this
function are proven.

\null
\<close>

definition singleton_set :: "'a set \<Rightarrow> 'a set set" where
"singleton_set X \<equiv> {Y. \<exists>x \<in> X. Y = {x}}"

lemma singleton_set_some:
 "(\<exists>Y. Y \<in> singleton_set X) = (\<exists>x. x \<in> X)"
proof (rule iffI, simp_all add: singleton_set_def, erule_tac [!] exE, erule bexE)
  fix x
  assume "x \<in> X"
  thus "\<exists>x. x \<in> X" ..
next
  fix x
  assume A: "x \<in> X"
  have "{x} = {x}" ..
  hence "\<exists>x' \<in> X. {x} = {x'}" using A ..
  thus "\<exists>Y. \<exists>x' \<in> X. Y = {x'}" by (rule exI)
qed

lemma singleton_set_union:
 "(\<Union>Y \<in> singleton_set X. Y) = X"
proof (subst singleton_set_def, rule equalityI, rule_tac [!] subsetI)
  fix x
  assume A: "x \<in> (\<Union>Y \<in> {Y'. \<exists>x' \<in> X. Y' = {x'}}. Y)"
  show "x \<in> X"
  proof (rule UN_E [OF A], simp)
  qed (erule bexE, simp)
next
  fix x
  assume A: "x \<in> X"
  show "x \<in> (\<Union>Y \<in> {Y'. \<exists>x' \<in> X. Y' = {x'}}. Y)"
  proof (rule UN_I [of "{x}"])
  qed (simp_all add: A)
qed


subsection "Additional intransitive purge functions and their properties"

text \<open>
Functions \<open>sinks_aux\<close>, \<open>ipurge_tr_aux\<close>, and \<open>ipurge_ref_aux\<close>, defined here below,
are auxiliary versions of functions @{term sinks}, @{term ipurge_tr}, and @{term ipurge_ref} taking
as input a set of domains rather than a single domain. As shown below, these functions are useful
for the study of single domain ones, involved in the definition of CSP noninterference security
\cite{R1}, since they distribute over list concatenation, while being susceptible to be expressed in
terms of the corresponding single domain functions in case the input set of domains is a singleton.

A further function, \<open>unaffected_domains\<close>, takes as inputs a set of domains \<open>U\<close> and an
event list \<open>xs\<close>, and outputs the set of the event domains not allowed to be affected by
\<open>U\<close> after the occurrence of \<open>xs\<close>.

\null
\<close>

function sinks_aux ::
 "('d \<times> 'd) set \<Rightarrow> ('a \<Rightarrow> 'd) \<Rightarrow> 'd set \<Rightarrow> 'a list \<Rightarrow> 'd set" where
"sinks_aux _ _ U [] = U" |
"sinks_aux I D U (xs @ [x]) = (if \<exists>v \<in> sinks_aux I D U xs. (v, D x) \<in> I
  then insert (D x) (sinks_aux I D U xs)
  else sinks_aux I D U xs)"
proof (atomize_elim, simp_all add: split_paired_all)
qed (rule rev_cases, rule disjI1, assumption, simp)
termination by lexicographic_order

function ipurge_tr_aux ::
 "('d \<times> 'd) set \<Rightarrow> ('a \<Rightarrow> 'd) \<Rightarrow> 'd set \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"ipurge_tr_aux _ _ _ [] = []" |
"ipurge_tr_aux I D U (xs @ [x]) = (if \<exists>v \<in> sinks_aux I D U xs. (v, D x) \<in> I
  then ipurge_tr_aux I D U xs
  else ipurge_tr_aux I D U xs @ [x])"
proof (atomize_elim, simp_all add: split_paired_all)
qed (rule rev_cases, rule disjI1, assumption, simp)
termination by lexicographic_order

definition ipurge_ref_aux ::
 "('d \<times> 'd) set \<Rightarrow> ('a \<Rightarrow> 'd) \<Rightarrow> 'd set \<Rightarrow> 'a list \<Rightarrow> 'a set \<Rightarrow> 'a set" where
"ipurge_ref_aux I D U xs X \<equiv>
  {x \<in> X. \<forall>v \<in> sinks_aux I D U xs. (v, D x) \<notin> I}"

definition unaffected_domains ::
 "('d \<times> 'd) set \<Rightarrow> ('a \<Rightarrow> 'd) \<Rightarrow> 'd set \<Rightarrow> 'a list \<Rightarrow> 'd set" where
"unaffected_domains I D U xs \<equiv>
  {u \<in> range D. \<forall>v \<in> sinks_aux I D U xs. (v, u) \<notin> I}"

text \<open>
\null

Function \<open>ipurge_tr_rev\<close>, defined here below in terms of function \<open>sources\<close>, is the
reverse of function @{term ipurge_tr} with regard to both the order in which events are considered,
and the criterion by which they are purged.

In some detail, both functions \<open>sources\<close> and \<open>ipurge_tr_rev\<close> take as inputs a domain
\<open>u\<close> and an event list \<open>xs\<close>, whose recursive decomposition is performed by item
prepending rather than appending. Then:

\begin{itemize}

\item
\<open>sources\<close> outputs the set of the domains of the events in \<open>xs\<close> allowed to affect
\<open>u\<close>;

\item
\<open>ipurge_tr_rev\<close> outputs the sublist of \<open>xs\<close> obtained by recursively deleting the events
not allowed to affect \<open>u\<close>, as detected via function \<open>sources\<close>.

\end{itemize}

In other words, these functions follow Rushby's ones \emph{sources} and \emph{ipurge} \cite{R4},
formalized in \cite{R1} as \<open>c_sources\<close> and \<open>c_ipurge\<close>. The only difference consists of
dropping the implicit supposition that the noninterference policy be reflexive, as done in the
definition of CPS noninterference security \cite{R1}. This goal is achieved by defining the output
of function \<open>sources\<close>, when it is applied to the empty list, as being the empty set rather
than the singleton comprised of the input domain.

As for functions \<open>sources_aux\<close> and \<open>ipurge_tr_rev_aux\<close>, they are auxiliary versions of
functions \<open>sources\<close> and \<open>ipurge_tr_rev\<close> taking as input a set of domains rather than a
single domain. As shown below, these functions distribute over list concatenation, while being
susceptible to be expressed in terms of the corresponding single domain functions in case the input
set of domains is a singleton.

\null
\<close>

primrec sources :: "('d \<times> 'd) set \<Rightarrow> ('a \<Rightarrow> 'd) \<Rightarrow> 'd \<Rightarrow> 'a list \<Rightarrow> 'd set" where
"sources _ _ _ [] = {}" |
"sources I D u (x # xs) =
  (if (D x, u) \<in> I \<or> (\<exists>v \<in> sources I D u xs. (D x, v) \<in> I)
  then insert (D x) (sources I D u xs)
  else sources I D u xs)"

primrec ipurge_tr_rev :: "('d \<times> 'd) set \<Rightarrow> ('a \<Rightarrow> 'd) \<Rightarrow> 'd \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"ipurge_tr_rev _ _ _ [] = []" |
"ipurge_tr_rev I D u (x # xs) = (if D x \<in> sources I D u (x # xs)
  then x # ipurge_tr_rev I D u xs
  else ipurge_tr_rev I D u xs)"

primrec sources_aux ::
 "('d \<times> 'd) set \<Rightarrow> ('a \<Rightarrow> 'd) \<Rightarrow> 'd set \<Rightarrow> 'a list \<Rightarrow> 'd set" where
"sources_aux _ _ U [] = U" |
"sources_aux I D U (x # xs) = (if \<exists>v \<in> sources_aux I D U xs. (D x, v) \<in> I
  then insert (D x) (sources_aux I D U xs)
  else sources_aux I D U xs)"

primrec ipurge_tr_rev_aux ::
 "('d \<times> 'd) set \<Rightarrow> ('a \<Rightarrow> 'd) \<Rightarrow> 'd set \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"ipurge_tr_rev_aux _ _ _ [] = []" |
"ipurge_tr_rev_aux I D U (x # xs) = (if \<exists>v \<in> sources_aux I D U xs. (D x, v) \<in> I
  then x # ipurge_tr_rev_aux I D U xs
  else ipurge_tr_rev_aux I D U xs)"

text \<open>
\null

Here below are some lemmas on functions @{term sinks_aux}, @{term ipurge_tr_aux},
@{term ipurge_ref_aux}, and @{term unaffected_domains}. As anticipated above, these lemmas
essentially concern distributivity over list concatenation and expressions in terms of single domain
functions in the degenerate case of a singleton set of domains.

\null
\<close>

lemma sinks_aux_subset:
 "U \<subseteq> sinks_aux I D U xs"
proof (induction xs rule: rev_induct, simp_all, rule impI)
qed (rule subset_insertI2)

lemma sinks_aux_single_dom:
 "sinks_aux I D {u} xs = insert u (sinks I D u xs)"
by (induction xs rule: rev_induct, simp_all add: insert_commute)

lemma sinks_aux_single_event:
 "sinks_aux I D U [x] = (if \<exists>v \<in> U. (v, D x) \<in> I
   then insert (D x) U
   else U)"
proof -
  have "sinks_aux I D U [x] = sinks_aux I D U ([] @ [x])" by simp
  thus ?thesis by (simp only: sinks_aux.simps)
qed

lemma sinks_aux_cons:
 "sinks_aux I D U (x # xs) = (if \<exists>v \<in> U. (v, D x) \<in> I
   then sinks_aux I D (insert (D x) U) xs
   else sinks_aux I D U xs)"
proof (induction xs rule: rev_induct, case_tac [!] "\<exists>v \<in> U. (v, D x) \<in> I",
 simp_all add: sinks_aux_single_event del: sinks_aux.simps(2))
  fix x' xs
  assume A: "sinks_aux I D U (x # xs) = sinks_aux I D (insert (D x) U) xs"
    (is "?S = ?S'")
  show "sinks_aux I D U (x # xs @ [x']) =
    sinks_aux I D (insert (D x) U) (xs @ [x'])"
  proof (cases "\<exists>v \<in> ?S. (v, D x') \<in> I")
    case True
    hence "sinks_aux I D U ((x # xs) @ [x']) = insert (D x') ?S"
     by (simp only: sinks_aux.simps, simp)
    moreover have "\<exists>v \<in> ?S'. (v, D x') \<in> I" using A and True by simp
    hence "sinks_aux I D (insert (D x) U) (xs @ [x']) = insert (D x') ?S'"
     by simp
    ultimately show ?thesis using A by simp
  next
    case False
    hence "sinks_aux I D U ((x # xs) @ [x']) = ?S"
     by (simp only: sinks_aux.simps, simp)
    moreover have "\<not> (\<exists>v \<in> ?S'. (v, D x') \<in> I)" using A and False by simp
    hence "sinks_aux I D (insert (D x) U) (xs @ [x']) = ?S'" by simp
    ultimately show ?thesis using A by simp
  qed
next
  fix x' xs
  assume A: "sinks_aux I D U (x # xs) = sinks_aux I D U xs"
    (is "?S = ?S'")
  show "sinks_aux I D U (x # xs @ [x']) = sinks_aux I D U (xs @ [x'])"
  proof (cases "\<exists>v \<in> ?S. (v, D x') \<in> I")
    case True
    hence "sinks_aux I D U ((x # xs) @ [x']) = insert (D x') ?S"
     by (simp only: sinks_aux.simps, simp)
    moreover have "\<exists>v \<in> ?S'. (v, D x') \<in> I" using A and True by simp
    hence "sinks_aux I D U (xs @ [x']) = insert (D x') ?S'" by simp
    ultimately show ?thesis using A by simp
  next
    case False
    hence "sinks_aux I D U ((x # xs) @ [x']) = ?S"
     by (simp only: sinks_aux.simps, simp)
    moreover have "\<not> (\<exists>v \<in> ?S'. (v, D x') \<in> I)" using A and False by simp
    hence "sinks_aux I D U (xs @ [x']) = ?S'" by simp
    ultimately show ?thesis using A by simp
  qed
qed

lemma ipurge_tr_aux_single_dom:
 "ipurge_tr_aux I D {u} xs = ipurge_tr I D u xs"
proof (induction xs rule: rev_induct, simp)
  fix x xs
  assume A: "ipurge_tr_aux I D {u} xs = ipurge_tr I D u xs"
  show "ipurge_tr_aux I D {u} (xs @ [x]) = ipurge_tr I D u (xs @ [x])"
  proof (cases "\<exists>v \<in> sinks_aux I D {u} xs. (v, D x) \<in> I",
   simp_all only: ipurge_tr_aux.simps if_True if_False)
    case True
    hence "(u, D x) \<in> I \<or> (\<exists>v \<in> sinks I D u xs. (v, D x) \<in> I)"
     by (simp add: sinks_aux_single_dom)
    hence "ipurge_tr I D u (xs @ [x]) = ipurge_tr I D u xs" by simp
    thus "ipurge_tr_aux I D {u} xs = ipurge_tr I D u (xs @ [x])"
     using A by simp
  next
    case False
    hence "\<not> ((u, D x) \<in> I \<or> (\<exists>v \<in> sinks I D u xs. (v, D x) \<in> I))"
     by (simp add: sinks_aux_single_dom)
    hence "D x \<notin> sinks I D u (xs @ [x])"
     by (simp only: sinks_interference_eq, simp)
    hence "ipurge_tr I D u (xs @ [x]) = ipurge_tr I D u xs @ [x]" by simp
    thus "ipurge_tr_aux I D {u} xs @ [x] = ipurge_tr I D u (xs @ [x])"
     using A by simp
  qed
qed

lemma ipurge_ref_aux_single_dom:
 "ipurge_ref_aux I D {u} xs X = ipurge_ref I D u xs X"
by (simp add: ipurge_ref_aux_def ipurge_ref_def sinks_aux_single_dom)

lemma ipurge_ref_aux_all [rule_format]:
 "(\<forall>u \<in> U. \<not> (\<exists>v \<in> D ` (X \<union> set xs). (u, v) \<in> I)) \<longrightarrow>
  ipurge_ref_aux I D U xs X = X"
proof (induction xs, simp_all add: ipurge_ref_aux_def sinks_aux_cons)
qed (rule impI, rule equalityI, rule_tac [!] subsetI, simp_all)

lemma ipurge_ref_all:
 "\<not> (\<exists>v \<in> D ` (X \<union> set xs). (u, v) \<in> I) \<Longrightarrow> ipurge_ref I D u xs X = X"
by (subst ipurge_ref_aux_single_dom [symmetric], rule ipurge_ref_aux_all, simp)

lemma unaffected_domains_single_dom:
 "{x \<in> X. D x \<in> unaffected_domains I D {u} xs} = ipurge_ref I D u xs X"
by (simp add: ipurge_ref_def unaffected_domains_def sinks_aux_single_dom)

text \<open>
\null

Here below are some lemmas on functions @{term sources}, @{term ipurge_tr_rev}, @{term sources_aux},
and @{term ipurge_tr_rev_aux}. As anticipated above, the lemmas on the last two functions basically
concern distributivity over list concatenation and expressions in terms of single domain functions
in the degenerate case of a singleton set of domains.

\null
\<close>

lemma sources_sinks:
 "sources I D u xs = sinks (I\<inverse>) D u (rev xs)"
by (induction xs, simp_all)

lemma sources_sinks_aux:
 "sources_aux I D U xs = sinks_aux (I\<inverse>) D U (rev xs)"
by (induction xs, simp_all)

lemma sources_aux_subset:
 "U \<subseteq> sources_aux I D U xs"
by (subst sources_sinks_aux, rule sinks_aux_subset)

lemma sources_aux_append:
 "sources_aux I D U (xs @ ys) = sources_aux I D (sources_aux I D U ys) xs"
by (induction xs, simp_all)

lemma sources_aux_append_nil [rule_format]:
 "sources_aux I D U ys = U \<longrightarrow>
  sources_aux I D U (xs @ ys) = sources_aux I D U xs"
by (induction xs, simp_all)

lemma ipurge_tr_rev_aux_append:
 "ipurge_tr_rev_aux I D U (xs @ ys) =
  ipurge_tr_rev_aux I D (sources_aux I D U ys) xs @ ipurge_tr_rev_aux I D U ys"
by (induction xs, simp_all add: sources_aux_append)

lemma ipurge_tr_rev_aux_nil_1 [rule_format]:
 "ipurge_tr_rev_aux I D U xs = [] \<longrightarrow> (\<forall>u \<in> U. \<not> (\<exists>v \<in> D ` set xs. (v, u) \<in> I))"
by (induction xs rule: rev_induct, simp_all add: ipurge_tr_rev_aux_append)

lemma ipurge_tr_rev_aux_nil_2 [rule_format]:
 "(\<forall>u \<in> U. \<not> (\<exists>v \<in> D ` set xs. (v, u) \<in> I)) \<longrightarrow> ipurge_tr_rev_aux I D U xs = []"
by (induction xs rule: rev_induct, simp_all add: ipurge_tr_rev_aux_append)

lemma ipurge_tr_rev_aux_nil:
 "(ipurge_tr_rev_aux I D U xs = []) = (\<forall>u \<in> U. \<not> (\<exists>v \<in> D ` set xs. (v, u) \<in> I))"
proof (rule iffI, rule ballI, erule ipurge_tr_rev_aux_nil_1, assumption)
qed (rule ipurge_tr_rev_aux_nil_2, erule bspec)

lemma ipurge_tr_rev_aux_nil_sources [rule_format]:
 "ipurge_tr_rev_aux I D U xs = [] \<longrightarrow> sources_aux I D U xs = U"
by (induction xs, simp_all)

lemma ipurge_tr_rev_aux_append_nil_1 [rule_format]:
 "ipurge_tr_rev_aux I D U ys = [] \<longrightarrow>
  ipurge_tr_rev_aux I D U (xs @ ys) = ipurge_tr_rev_aux I D U xs"
by (induction xs, simp_all add: ipurge_tr_rev_aux_nil_sources sources_aux_append_nil)

lemma ipurge_tr_rev_aux_first [rule_format]:
 "ipurge_tr_rev_aux I D U xs = x # ws \<longrightarrow>
  (\<exists>ys zs. xs = ys @ x # zs \<and>
    ipurge_tr_rev_aux I D (sources_aux I D U (x # zs)) ys = [] \<and>
    (\<exists>v \<in> sources_aux I D U zs. (D x, v) \<in> I))"
proof (induction xs, simp, rule impI)
  fix x' xs
  assume
    A: "ipurge_tr_rev_aux I D U xs = x # ws \<longrightarrow>
      (\<exists>ys zs. xs = ys @ x # zs \<and>
        ipurge_tr_rev_aux I D (sources_aux I D U (x # zs)) ys = [] \<and>
        (\<exists>v \<in> sources_aux I D U zs. (D x, v) \<in> I))" and
    B: "ipurge_tr_rev_aux I D U (x' # xs) = x # ws"
  show "\<exists>ys zs. x' # xs = ys @ x # zs \<and>
    ipurge_tr_rev_aux I D (sources_aux I D U (x # zs)) ys = [] \<and>
    (\<exists>v \<in> sources_aux I D U zs. (D x, v) \<in> I)"
  proof (cases "\<exists>v \<in> sources_aux I D U xs. (D x', v) \<in> I")
    case True
    then have "x' = x" using B by simp
    with True have "x' # xs = x # xs \<and>
      ipurge_tr_rev_aux I D (sources_aux I D U (x # xs)) [] = [] \<and>
      (\<exists>v \<in> sources_aux I D U xs. (D x, v) \<in> I)"
     by simp
    thus ?thesis by blast
  next
    case False
    hence "ipurge_tr_rev_aux I D U xs = x # ws" using B by simp
    with A have "\<exists>ys zs. xs = ys @ x # zs \<and>
      ipurge_tr_rev_aux I D (sources_aux I D U (x # zs)) ys = [] \<and>
      (\<exists>v \<in> sources_aux I D U zs. (D x, v) \<in> I)" ..
    then obtain ys and zs where xs: "xs = ys @ x # zs \<and>
      ipurge_tr_rev_aux I D (sources_aux I D U (x # zs)) ys = [] \<and>
      (\<exists>v \<in> sources_aux I D U zs. (D x, v) \<in> I)"
     by blast
    then have
      "\<not> (\<exists>v \<in> sources_aux I D (sources_aux I D U (x # zs)) ys. (D x', v) \<in> I)"
     using False by (simp add: sources_aux_append)
    hence "ipurge_tr_rev_aux I D (sources_aux I D U (x # zs)) (x' # ys) =
      ipurge_tr_rev_aux I D (sources_aux I D U (x # zs)) ys"
     by simp
    with xs have "x' # xs = (x' # ys) @ x # zs \<and>
      ipurge_tr_rev_aux I D (sources_aux I D U (x # zs)) (x' # ys) = [] \<and>
      (\<exists>v \<in> sources_aux I D U zs. (D x, v) \<in> I)"
     by (simp del: sources_aux.simps)
    thus ?thesis by blast
  qed
qed

lemma ipurge_tr_rev_aux_last_1 [rule_format]:
 "ipurge_tr_rev_aux I D U xs = ws @ [x] \<longrightarrow> (\<exists>v \<in> U. (D x, v) \<in> I)"
proof (induction xs rule: rev_induct, simp, rule impI)
  fix xs x'
  assume
    A: "ipurge_tr_rev_aux I D U xs = ws @ [x] \<longrightarrow> (\<exists>v \<in> U. (D x, v) \<in> I)" and
    B: "ipurge_tr_rev_aux I D U (xs @ [x']) = ws @ [x]"
  show "\<exists>v \<in> U. (D x, v) \<in> I"
  proof (cases "\<exists>v \<in> U. (D x', v) \<in> I")
    case True
    hence "ipurge_tr_rev_aux I D U (xs @ [x']) =
      ipurge_tr_rev_aux I D (insert (D x') U) xs @ [x']"
     by (simp add: ipurge_tr_rev_aux_append)
    hence "x' = x" using B by simp
    thus ?thesis using True by simp
  next
    case False
    hence "ipurge_tr_rev_aux I D U (xs @ [x']) = ipurge_tr_rev_aux I D U xs"
     by (simp add: ipurge_tr_rev_aux_append)
    hence "ipurge_tr_rev_aux I D U xs = ws @ [x]" using B by simp
    with A show ?thesis ..
  qed
qed

lemma ipurge_tr_rev_aux_last_2 [rule_format]:
 "ipurge_tr_rev_aux I D U xs = ws @ [x] \<longrightarrow>
  (\<exists>ys zs. xs = ys @ x # zs \<and> ipurge_tr_rev_aux I D U zs = [])"
proof (induction xs rule: rev_induct, simp, rule impI)
  fix xs x'
  assume
    A: "ipurge_tr_rev_aux I D U xs = ws @ [x] \<longrightarrow>
      (\<exists>ys zs. xs = ys @ x # zs \<and> ipurge_tr_rev_aux I D U zs = [])" and
    B: "ipurge_tr_rev_aux I D U (xs @ [x']) = ws @ [x]"
  show "\<exists>ys zs. xs @ [x'] = ys @ x # zs \<and> ipurge_tr_rev_aux I D U zs = []"
  proof (cases "\<exists>v \<in> U. (D x', v) \<in> I")
    case True
    hence "ipurge_tr_rev_aux I D U (xs @ [x']) =
      ipurge_tr_rev_aux I D (insert (D x') U) xs @ [x']"
     by (simp add: ipurge_tr_rev_aux_append)
    hence "xs @ [x'] = xs @ x # [] \<and> ipurge_tr_rev_aux I D U [] = []"
     using B by simp
    thus ?thesis by blast
  next
    case False
    hence "ipurge_tr_rev_aux I D U (xs @ [x']) = ipurge_tr_rev_aux I D U xs"
     by (simp add: ipurge_tr_rev_aux_append)
    hence "ipurge_tr_rev_aux I D U xs = ws @ [x]" using B by simp
    with A have "\<exists>ys zs. xs = ys @ x # zs \<and> ipurge_tr_rev_aux I D U zs = []" ..
    then obtain ys and zs where
      C: "xs = ys @ x # zs \<and> ipurge_tr_rev_aux I D U zs = []"
     by blast
    hence "xs @ [x'] = ys @ x # zs @ [x']" by simp
    moreover have
     "ipurge_tr_rev_aux I D U (zs @ [x']) = ipurge_tr_rev_aux I D U zs"
     using False by (simp add: ipurge_tr_rev_aux_append)
    hence "ipurge_tr_rev_aux I D U (zs @ [x']) = []" using C by simp
    ultimately have "xs @ [x'] = ys @ x # zs @ [x'] \<and>
      ipurge_tr_rev_aux I D U (zs @ [x']) = []" ..
    thus ?thesis by blast
  qed
qed

lemma ipurge_tr_rev_aux_all [rule_format]:
 "(\<forall>v \<in> D ` set xs. \<exists>u \<in> U. (v, u) \<in> I) \<longrightarrow> ipurge_tr_rev_aux I D U xs = xs"
proof (induction xs, simp, rule impI, simp, erule conjE)
  fix x xs
  assume "\<exists>u \<in> U. (D x, u) \<in> I"
  then obtain u where A: "u \<in> U" and B: "(D x, u) \<in> I" ..
  have "U \<subseteq> sources_aux I D U xs" by (rule sources_aux_subset)
  hence "u \<in> sources_aux I D U xs" using A ..
  with B show "\<exists>u \<in> sources_aux I D U xs. (D x, u) \<in> I" ..
qed

text \<open>
\null

Here below, further properties of the functions defined above are investigated thanks to the
introduction of function \<open>offset\<close>, which searches a list for a given item and returns the
offset of its first occurrence, if any, from the first item of the list.

\null
\<close>

primrec offset :: "nat \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> nat option" where
"offset _ _ [] = None" |
"offset n x (y # ys) = (if y = x then Some n else offset (Suc n) x ys)"

lemma offset_not_none_1 [rule_format]:
 "offset k x xs \<noteq> None \<longrightarrow> (\<exists>ys zs. xs = ys @ x # zs)"
proof (induction xs arbitrary: k, simp, rule impI)
  fix w xs k
  assume
    A: "\<And>k. offset k x xs \<noteq> None \<longrightarrow> (\<exists>ys zs. xs = ys @ x # zs)" and
    B: "offset k x (w # xs) \<noteq> None"
  show "\<exists>ys zs. w # xs = ys @ x # zs"
  proof (cases "w = x", simp)
    case True
    hence "x # xs = [] @ x # xs" by simp
    thus "\<exists>ys zs. x # xs = ys @ x # zs" by blast
  next
    case False
    hence "offset k x (w # xs) = offset (Suc k) x xs" by simp
    hence "offset (Suc k) x xs \<noteq> None" using B by simp
    moreover have "offset (Suc k) x xs \<noteq> None \<longrightarrow> (\<exists>ys zs. xs = ys @ x # zs)"
     using A .
    ultimately have "\<exists>ys zs. xs = ys @ x # zs" by simp
    then obtain ys and zs where "xs = ys @ x # zs" by blast
    hence "w # xs = (w # ys) @ x # zs" by simp
    thus "\<exists>ys zs. w # xs = ys @ x # zs" by blast
  qed
qed

lemma offset_not_none_2 [rule_format]:
 "xs = ys @ x # zs \<longrightarrow> offset k x xs \<noteq> None"
proof (induction xs arbitrary: ys k, simp_all del: not_None_eq, rule impI)
  fix w xs ys k
  assume
    A: "\<And>ys' k'. xs = ys' @ x # zs \<longrightarrow> offset k' x (ys' @ x # zs) \<noteq> None" and
    B: "w # xs = ys @ x # zs"
  show "offset k x (ys @ x # zs) \<noteq> None"
  proof (cases ys, simp_all del: not_None_eq, rule impI)
    fix y' ys'
    have "xs = ys' @ x # zs \<longrightarrow> offset (Suc k) x (ys' @ x # zs) \<noteq> None"
     using A .
    moreover assume "ys = y' # ys'"
    hence "xs = ys' @ x # zs" using B by simp
    ultimately show "offset (Suc k) x (ys' @ x # zs) \<noteq> None" ..
  qed
qed

lemma offset_not_none:
 "(offset k x xs \<noteq> None) = (\<exists>ys zs. xs = ys @ x # zs)"
by (rule iffI, erule offset_not_none_1, (erule exE)+, rule offset_not_none_2)

lemma offset_addition [rule_format]:
 "offset k x xs \<noteq> None \<longrightarrow> offset (n + m) x xs = Some (the (offset n x xs) + m)"
proof (induction xs arbitrary: k n, simp, rule impI)
  fix w xs k n
  assume
    A: "\<And>k n. offset k x xs \<noteq> None \<longrightarrow>
      offset (n + m) x xs = Some (the (offset n x xs) + m)" and
    B: "offset k x (w # xs) \<noteq> None"
  show "offset (n + m) x (w # xs) = Some (the (offset n x (w # xs)) + m)"
  proof (cases "w = x", simp_all)
    case False
    hence "offset k x (w # xs) = offset (Suc k) x xs" by simp
    hence "offset (Suc k) x xs \<noteq> None" using B by simp
    moreover have "offset (Suc k) x xs \<noteq> None \<longrightarrow>
      offset (Suc n + m) x xs = Some (the (offset (Suc n) x xs) + m)"
     using A .
    ultimately show "offset (Suc (n + m)) x xs =
      Some (the (offset (Suc n) x xs) + m)"
     by simp
  qed
qed

lemma offset_suc:
  assumes A: "offset k x xs \<noteq> None"
  shows "offset (Suc n) x xs = Some (Suc (the (offset n x xs)))"
proof -
  have "offset (Suc n) x xs = offset (n + Suc 0) x xs" by simp
  also have "\<dots> = Some (the (offset n x xs) + Suc 0)" using A by (rule offset_addition)
  also have "\<dots> = Some (Suc (the (offset n x xs)))" by simp
  finally show ?thesis .
qed

lemma ipurge_tr_rev_aux_first_offset [rule_format]:
 "xs = ys @ x # zs \<and> ipurge_tr_rev_aux I D (sources_aux I D U (x # zs)) ys = [] \<and>
    (\<exists>v \<in> sources_aux I D U zs. (D x, v) \<in> I) \<longrightarrow>
  ys = take (the (offset 0 x xs)) xs"
proof (induction xs arbitrary: ys, simp, rule impI, (erule conjE)+)
  fix x' xs ys
  assume
    A: "\<And>ys. xs = ys @ x # zs \<and>
        ipurge_tr_rev_aux I D (sources_aux I D U (x # zs)) ys = [] \<and>
        (\<exists>v \<in> sources_aux I D U zs. (D x, v) \<in> I) \<longrightarrow>
      ys = take (the (offset 0 x xs)) xs" and
    B: "x' # xs = ys @ x # zs" and
    C: "ipurge_tr_rev_aux I D (sources_aux I D U (x # zs)) ys = []" and
    D: "\<exists>v \<in> sources_aux I D U zs. (D x, v) \<in> I"
  show "ys = take (the (offset 0 x (x' # xs))) (x' # xs)"
  proof (cases ys)
    case Nil
    then have "x' = x" using B by simp
    with Nil show ?thesis by simp
  next
    case (Cons y ys')
    hence E: "xs = ys' @ x # zs" using B by simp
    moreover have
      F: "ipurge_tr_rev_aux I D (sources_aux I D U (x # zs)) (y # ys') = []"
     using Cons and C by simp
    hence
      G: "\<not> (\<exists>v \<in> sources_aux I D (sources_aux I D U (x # zs)) ys'. (D y, v) \<in> I)"
     by (rule_tac notI, simp)
    hence "ipurge_tr_rev_aux I D (sources_aux I D U (x # zs)) ys' = []"
     using F by simp
    ultimately have "xs = ys' @ x # zs \<and>
      ipurge_tr_rev_aux I D (sources_aux I D U (x # zs)) ys' = [] \<and>
      (\<exists>v \<in> sources_aux I D U zs. (D x, v) \<in> I)"
     using D by blast
    with A have H: "ys' = take (the (offset 0 x xs)) xs" ..
    have I: "x' = y" using Cons and B by simp
    hence
      J: "\<not> (\<exists>v \<in> sources_aux I D (sources_aux I D U zs) (ys' @ [x]). (D x', v) \<in> I)"
     using G by (simp add: sources_aux_append)
    have "x' \<noteq> x"
    proof
      assume "x' = x"
      hence "\<exists>v \<in> sources_aux I D U zs. (D x', v) \<in> I" using D by simp
      then obtain v where K: "v \<in> sources_aux I D U zs" and L: "(D x', v) \<in> I" ..
      have "sources_aux I D U zs \<subseteq>
        sources_aux I D (sources_aux I D U zs) (ys' @ [x])"
       by (rule sources_aux_subset)
      hence "v \<in> sources_aux I D (sources_aux I D U zs) (ys' @ [x])" using K ..
      with L have
       "\<exists>v \<in> sources_aux I D (sources_aux I D U zs) (ys' @ [x]). (D x', v) \<in> I" ..
      thus False using J by contradiction
    qed
    hence "offset 0 x (x' # xs) = offset (Suc 0) x xs" by simp
    also have "\<dots> = Some (Suc (the (offset 0 x xs)))"
    proof -
      have "\<exists>ys zs. xs = ys @ x # zs" using E by blast
      hence "offset 0 x xs \<noteq> None" by (simp only: offset_not_none)
      thus ?thesis by (rule offset_suc)
    qed
    finally have "take (the (offset 0 x (x' # xs))) (x' # xs) =
      x' # take (the (offset 0 x xs)) xs"
     by simp
    thus ?thesis using Cons and H and I by simp
  qed
qed

lemma ipurge_tr_rev_aux_append_nil_2 [rule_format]:
 "ipurge_tr_rev_aux I D U (xs @ ys) = ipurge_tr_rev_aux I D V xs \<longrightarrow>
  ipurge_tr_rev_aux I D U ys = []"
proof (induction xs, simp, simp only: append_Cons, rule impI)
  fix x xs
  assume
    A: "ipurge_tr_rev_aux I D U (xs @ ys) = ipurge_tr_rev_aux I D V xs \<longrightarrow>
      ipurge_tr_rev_aux I D U ys = []" and
    B: "ipurge_tr_rev_aux I D U (x # xs @ ys) = ipurge_tr_rev_aux I D V (x # xs)"
  show "ipurge_tr_rev_aux I D U ys = []"
  proof (cases "\<exists>v \<in> sources_aux I D V xs. (D x, v) \<in> I")
    case True
    hence C: "ipurge_tr_rev_aux I D U (x # xs @ ys) =
      x # ipurge_tr_rev_aux I D V xs"
     using B by simp
    hence "\<exists>vs ws. x # xs @ ys = vs @ x # ws \<and>
      ipurge_tr_rev_aux I D (sources_aux I D U (x # ws)) vs = [] \<and>
      (\<exists>v \<in> sources_aux I D U ws. (D x, v) \<in> I)"
     by (rule ipurge_tr_rev_aux_first)
    then obtain vs and ws where *: "x # xs @ ys = vs @ x # ws \<and>
      ipurge_tr_rev_aux I D (sources_aux I D U (x # ws)) vs = [] \<and>
      (\<exists>v \<in> sources_aux I D U ws. (D x, v) \<in> I)"
     by blast
    then have "vs = take (the (offset 0 x (x # xs @ ys))) (x # xs @ ys)"
      by (rule ipurge_tr_rev_aux_first_offset)
    hence "vs = []" by simp
    with * have "\<exists>v \<in> sources_aux I D U (xs @ ys). (D x, v) \<in> I" by simp
    hence "ipurge_tr_rev_aux I D U (xs @ ys) = ipurge_tr_rev_aux I D V xs"
     using C by simp
    with A show ?thesis ..
  next
    case False
    moreover have "\<not> (\<exists>v \<in> sources_aux I D U (xs @ ys). (D x, v) \<in> I)"
    proof
      assume "\<exists>v \<in> sources_aux I D U (xs @ ys). (D x, v) \<in> I"
      hence "ipurge_tr_rev_aux I D V (x # xs) =
        x # ipurge_tr_rev_aux I D U (xs @ ys)"
       using B by simp
      hence "\<exists>vs ws. x # xs = vs @ x # ws \<and>
        ipurge_tr_rev_aux I D (sources_aux I D V (x # ws)) vs = [] \<and>
        (\<exists>v \<in> sources_aux I D V ws. (D x, v) \<in> I)"
       by (rule ipurge_tr_rev_aux_first)
      then obtain vs and ws where *: "x # xs = vs @ x # ws \<and>
        ipurge_tr_rev_aux I D (sources_aux I D V (x # ws)) vs = [] \<and>
        (\<exists>v \<in> sources_aux I D V ws. (D x, v) \<in> I)"
       by blast
      then have "vs = take (the (offset 0 x (x # xs))) (x # xs)"
        by (rule ipurge_tr_rev_aux_first_offset)
      hence "vs = []" by simp
      with * have "\<exists>v \<in> sources_aux I D V xs. (D x, v) \<in> I" by simp
      thus False using False by contradiction
    qed
    ultimately have "ipurge_tr_rev_aux I D U (xs @ ys) =
      ipurge_tr_rev_aux I D V xs"
     using B by simp
    with A show ?thesis ..
  qed
qed

lemma ipurge_tr_rev_aux_append_nil:
 "(ipurge_tr_rev_aux I D U (xs @ ys) = ipurge_tr_rev_aux I D U xs) =
  (ipurge_tr_rev_aux I D U ys = [])"
by (rule iffI, erule ipurge_tr_rev_aux_append_nil_2, rule ipurge_tr_rev_aux_append_nil_1)

text \<open>
\null

In what follows, it is proven by induction that the lists output by functions @{term ipurge_tr} and
@{term ipurge_tr_rev}, as well as those output by @{term ipurge_tr_aux} and
@{term ipurge_tr_rev_aux}, satisfy predicate @{term Interleaves} (cf. \cite{R2}), in correspondence
with suitable input predicates expressed in terms of functions @{term sinks} and @{term sinks_aux},
respectively. Then, some lemmas on the aforesaid functions are demonstrated without induction, using
previous lemmas along with the properties of predicate @{term Interleaves}.

\null
\<close>

lemma Interleaves_ipurge_tr:
 "xs \<cong> {ipurge_tr_rev I D u xs, rev (ipurge_tr (I\<inverse>) D u (rev xs)),
    \<lambda>y ys. D y \<in> sinks (I\<inverse>) D u (rev (y # ys))}"
proof (induction xs, simp, simp only: rev.simps)
  fix x xs
  assume A: "xs \<cong> {ipurge_tr_rev I D u xs, rev (ipurge_tr (I\<inverse>) D u (rev xs)),
    \<lambda>y ys. D y \<in> sinks (I\<inverse>) D u (rev ys @ [y])}"
    (is "_ \<cong> {?ys, ?zs, ?P}")
  show "x # xs \<cong>
    {ipurge_tr_rev I D u (x # xs), rev (ipurge_tr (I\<inverse>) D u (rev xs @ [x])), ?P}"
  proof (cases "?P x xs", simp_all add: sources_sinks del: sinks.simps)
    case True
    thus "x # xs \<cong> {x # ?ys, ?zs, ?P}" using A by (cases ?zs, simp_all)
  next
    case False
    thus "x # xs \<cong> {?ys, x # ?zs, ?P}" using A by (cases ?ys, simp_all)
  qed
qed

lemma Interleaves_ipurge_tr_aux:
 "xs \<cong> {ipurge_tr_rev_aux I D U xs, rev (ipurge_tr_aux (I\<inverse>) D U (rev xs)),
    \<lambda>y ys. \<exists>v \<in> sinks_aux (I\<inverse>) D U (rev ys). (D y, v) \<in> I}"
proof (induction xs, simp, simp only: rev.simps)
  fix x xs
  assume A: "xs \<cong> {ipurge_tr_rev_aux I D U xs,
    rev (ipurge_tr_aux (I\<inverse>) D U (rev xs)),
    \<lambda>y ys. \<exists>v \<in> sinks_aux (I\<inverse>) D U (rev ys). (D y, v) \<in> I}"
    (is "_ \<cong> {?ys, ?zs, ?P}")
  show "x # xs \<cong>
    {ipurge_tr_rev_aux I D U (x # xs),
    rev (ipurge_tr_aux (I\<inverse>) D U (rev xs @ [x])), ?P}"
  proof (cases "?P x xs", simp_all (no_asm_simp) add: sources_sinks_aux)
    case True
    thus "x # xs \<cong> {x # ?ys, ?zs, ?P}" using A by (cases ?zs, simp_all)
  next
    case False
    thus "x # xs \<cong> {?ys, x # ?zs, ?P}" using A by (cases ?ys, simp_all)
  qed
qed

lemma ipurge_tr_aux_all:
 "(ipurge_tr_aux I D U xs = xs) = (\<forall>u \<in> U. \<not> (\<exists>v \<in> D ` set xs. (u, v) \<in> I))"
proof -
  have A: "rev xs \<cong> {ipurge_tr_rev_aux (I\<inverse>) D U (rev xs),
    rev (ipurge_tr_aux ((I\<inverse>)\<inverse>) D U (rev (rev xs))),
    \<lambda>y ys. \<exists>v \<in> sinks_aux ((I\<inverse>)\<inverse>) D U (rev ys). (D y, v) \<in> (I\<inverse>)}"
    (is "_ \<cong> {_, _, ?P}")
   by (rule Interleaves_ipurge_tr_aux)
  show ?thesis
  proof
    assume "ipurge_tr_aux I D U xs = xs"
    hence "rev xs \<cong> {ipurge_tr_rev_aux (I\<inverse>) D U (rev xs), rev xs, ?P}"
     using A by simp
    hence "rev xs \<simeq> {ipurge_tr_rev_aux (I\<inverse>) D U (rev xs), rev xs, ?P}"
     by (rule Interleaves_interleaves)
    moreover have "rev xs \<simeq> {[], rev xs, ?P}" by (rule interleaves_nil_all)
    ultimately have "ipurge_tr_rev_aux (I\<inverse>) D U (rev xs) = []"
     by (rule interleaves_equal_fst)
    thus "\<forall>u \<in> U. \<not> (\<exists>v \<in> D ` set xs. (u, v) \<in> I)"
     by (simp add: ipurge_tr_rev_aux_nil)
  next
    assume "\<forall>u \<in> U. \<not> (\<exists>v \<in> D ` set xs. (u, v) \<in> I)"
    hence "ipurge_tr_rev_aux (I\<inverse>) D U (rev xs) = []"
     by (simp add: ipurge_tr_rev_aux_nil)
    hence "rev xs \<cong> {[], rev (ipurge_tr_aux I D U xs), ?P}" using A by simp
    hence "rev xs \<simeq> {[], rev (ipurge_tr_aux I D U xs), ?P}"
     by (rule Interleaves_interleaves)
    hence "rev xs \<simeq> {rev (ipurge_tr_aux I D U xs), [], \<lambda>w ws. \<not> ?P w ws}"
     by (subst (asm) interleaves_swap)
    moreover have "rev xs \<simeq> {rev xs, [], \<lambda>w ws. \<not> ?P w ws}"
     by (rule interleaves_all_nil)
    ultimately have "rev (ipurge_tr_aux I D U xs) = rev xs"
     by (rule interleaves_equal_fst)
    thus "ipurge_tr_aux I D U xs = xs" by simp
  qed
qed

lemma ipurge_tr_rev_aux_single_dom:
 "ipurge_tr_rev_aux I D {u} xs = ipurge_tr_rev I D u xs" (is "?ys = ?ys'")
proof -
  have "xs \<cong> {?ys, rev (ipurge_tr_aux (I\<inverse>) D {u} (rev xs)),
    \<lambda>y ys. \<exists>v \<in> sinks_aux (I\<inverse>) D {u} (rev ys). (D y, v) \<in> I}"
   by (rule Interleaves_ipurge_tr_aux)
  hence "xs \<cong> {?ys, rev (ipurge_tr (I\<inverse>) D u (rev xs)),
    \<lambda>y ys. (u, D y) \<in> I\<inverse> \<or> (\<exists>v \<in> sinks (I\<inverse>) D u (rev ys). (v, D y) \<in> I\<inverse>)}"
   by (simp add: ipurge_tr_aux_single_dom sinks_aux_single_dom)
  hence "xs \<cong> {?ys, rev (ipurge_tr (I\<inverse>) D u (rev xs)),
    \<lambda>y ys. D y \<in> sinks (I\<inverse>) D u (rev (y # ys))}"
    (is "_ \<cong> {_, ?zs, ?P}")
   by (simp only: sinks_interference_eq, simp)
  moreover have "xs \<cong> {?ys', ?zs, ?P}" by (rule Interleaves_ipurge_tr)
  ultimately show ?thesis by (rule Interleaves_equal_fst)
qed

lemma ipurge_tr_all:
 "(ipurge_tr I D u xs = xs) = (\<not> (\<exists>v \<in> D ` set xs. (u, v) \<in> I))"
by (subst ipurge_tr_aux_single_dom [symmetric], simp add: ipurge_tr_aux_all)

lemma ipurge_tr_rev_all:
 "\<forall>v \<in> D ` set xs. (v, u) \<in> I \<Longrightarrow> ipurge_tr_rev I D u xs = xs"
proof (subst ipurge_tr_rev_aux_single_dom [symmetric], rule ipurge_tr_rev_aux_all)
qed (simp (no_asm_simp))


subsection "A domain-relation map based on intransitive purge"

text \<open>
In what follows, constant \<open>rel_ipurge\<close> is defined as the domain-relation map that associates
each domain \<open>u\<close> to the relation comprised of the pairs of traces whose images under function
@{term "ipurge_tr_rev I D u"} are equal, viz. whose events affecting \<open>u\<close> are the same.

An auxiliary domain set-relation map, \<open>rel_ipurge_aux\<close>, is also defined by replacing
@{term ipurge_tr_rev} with @{term ipurge_tr_rev_aux}, so as to exploit the distributivity of the
latter function over list concatenation. Unsurprisingly, since @{term ipurge_tr_rev_aux} degenerates
into @{term ipurge_tr_rev} for a singleton set of domains, the same happens for
\<open>rel_ipurge_aux\<close> and \<open>rel_ipurge\<close>.

Subsequently, some basic properties of domain-relation map \<open>rel_ipurge\<close> are proven, namely
that it is a view partition, and is future consistent if and only if it is weakly future consistent.
The nontrivial implication, viz. the direct one, derives from the fact that for each domain
\<open>u\<close> allowed to be affected by any event domain, function @{term "ipurge_tr_rev I D u"} matches
the identity function, so that two traces are correlated by the image of \<open>rel_ipurge\<close> under
\<open>u\<close> just in case they are equal.

\null
\<close>

definition rel_ipurge ::
 "'a process \<Rightarrow> ('d \<times> 'd) set \<Rightarrow> ('a \<Rightarrow> 'd) \<Rightarrow> ('a, 'd) dom_rel_map" where
"rel_ipurge P I D u \<equiv> {(xs, ys). xs \<in> traces P \<and> ys \<in> traces P \<and>
  ipurge_tr_rev I D u xs = ipurge_tr_rev I D u ys}"

definition rel_ipurge_aux ::
 "'a process \<Rightarrow> ('d \<times> 'd) set \<Rightarrow> ('a \<Rightarrow> 'd) \<Rightarrow> ('a, 'd) domset_rel_map" where
"rel_ipurge_aux P I D U \<equiv> {(xs, ys). xs \<in> traces P \<and> ys \<in> traces P \<and>
  ipurge_tr_rev_aux I D U xs = ipurge_tr_rev_aux I D U ys}"

lemma rel_ipurge_aux_single_dom:
 "rel_ipurge_aux P I D {u} = rel_ipurge P I D u"
by (simp add: rel_ipurge_def rel_ipurge_aux_def ipurge_tr_rev_aux_single_dom)

lemma view_partition_rel_ipurge:
 "view_partition P D (rel_ipurge P I D)"
proof (subst view_partition_def, rule ballI, rule equivI)
  fix u
  show "refl_on (traces P) (rel_ipurge P I D u)"
  proof (rule refl_onI, simp_all add: rel_ipurge_def)
  qed (rule subsetI, simp add: split_paired_all)
next
  fix u
  show "sym (rel_ipurge P I D u)"
  by (rule symI, simp add: rel_ipurge_def)
next
  fix u
  show "trans (rel_ipurge P I D u)"
  by (rule transI, simp add: rel_ipurge_def)
qed

lemma fc_equals_wfc_rel_ipurge:
 "future_consistent P D (rel_ipurge P I D) =
  weakly_future_consistent P I D (rel_ipurge P I D)"
proof (rule iffI, erule fc_implies_wfc,
 simp only: future_consistent_def weakly_future_consistent_def,
 rule ballI, (rule allI)+, rule impI)
  fix u xs ys
  assume
    A: "\<forall>u \<in> range D \<inter> (-I) `` range D. \<forall>xs ys. (xs, ys) \<in> rel_ipurge P I D u \<longrightarrow>
      next_dom_events P D u xs = next_dom_events P D u ys \<and>
      ref_dom_events P D u xs = ref_dom_events P D u ys" and
    B: "u \<in> range D" and
    C: "(xs, ys) \<in> rel_ipurge P I D u"
  show "next_dom_events P D u xs = next_dom_events P D u ys \<and>
    ref_dom_events P D u xs = ref_dom_events P D u ys"
  proof (cases "u \<in> range D \<inter> (-I) `` range D")
    case True
    with A have "\<forall>xs ys. (xs, ys) \<in> rel_ipurge P I D u \<longrightarrow>
      next_dom_events P D u xs = next_dom_events P D u ys \<and>
      ref_dom_events P D u xs = ref_dom_events P D u ys" ..
    hence "(xs, ys) \<in> rel_ipurge P I D u \<longrightarrow>
      next_dom_events P D u xs = next_dom_events P D u ys \<and>
      ref_dom_events P D u xs = ref_dom_events P D u ys"
     by blast
    thus ?thesis using C ..
  next
    case False
    hence D: "u \<notin> (-I) `` range D" using B by simp
    have "ipurge_tr_rev I D u xs = ipurge_tr_rev I D u ys"
     using C by (simp add: rel_ipurge_def)
    moreover have "\<forall>zs. ipurge_tr_rev I D u zs = zs"
    proof (rule allI, rule ipurge_tr_rev_all, rule ballI, erule imageE, rule ccontr)
      fix v x
      assume "(v, u) \<notin> I"
      hence "(v, u) \<in> -I" by simp
      moreover assume "v = D x"
      hence "v \<in> range D" by simp
      ultimately have "u \<in> (-I) `` range D" ..
      thus False using D by contradiction
    qed
    ultimately show ?thesis by simp
  qed
qed


subsection "The Ipurge Unwinding Theorem: proof of condition sufficiency"

text \<open>
The Ipurge Unwinding Theorem, formalized in what follows as theorem \<open>ipurge_unwinding\<close>, states
that a necessary and sufficient condition for the CSP noninterference security \cite{R1} of a
process being refusals union closed is that domain-relation map @{term rel_ipurge} be weakly future
consistent. Notwithstanding the equivalence of future consistency and weak future consistency for
@{term rel_ipurge} (cf. above), expressing the theorem in terms of the latter reduces the range of
the domains to be considered in order to prove or disprove the security of a process, and then is
more convenient.

According to the definition of CSP noninterference security formulated in \cite{R1}, a process is
regarded as being secure just in case the occurrence of an event \emph{e} may only affect future
events allowed to be affected by \emph{e}. Identifying security with the weak future consistency of
@{term rel_ipurge} means reversing the view of the problem with respect to the direction of time. In
fact, from this view, a process is secure just in case the occurrence of an event \emph{e} may only
be affected by past events allowed to affect \emph{e}. Therefore, what the Ipurge Unwinding Theorem
proves is that ultimately, opposite perspectives with regard to the direction of time give rise to
equivalent definitions of the noninterference security of a process.

Here below, it is proven that the condition expressed by the Ipurge Unwinding Theorem is sufficient
for security.

\null
\<close>

lemma ipurge_tr_rev_ipurge_tr_aux_1 [rule_format]:
 "U \<subseteq> unaffected_domains I D (D ` set ys) zs \<longrightarrow>
  ipurge_tr_rev_aux I D U (xs @ ys @ zs) =
  ipurge_tr_rev_aux I D U (xs @ ipurge_tr_aux I D (D ` set ys) zs)"
proof (induction zs arbitrary: U rule: rev_induct, rule_tac [!] impI, simp)
  fix U
  assume A: "U \<subseteq> unaffected_domains I D (D ` set ys) []"
  have "\<forall>u \<in> U. \<forall>v \<in> D ` set ys. (v, u) \<notin> I"
  proof
    fix u
    assume "u \<in> U"
    with A have "u \<in> unaffected_domains I D (D ` set ys) []" ..
    thus "\<forall>v \<in> D ` set ys. (v, u) \<notin> I" by (simp add: unaffected_domains_def)
  qed
  hence "ipurge_tr_rev_aux I D U ys = []" by (simp add: ipurge_tr_rev_aux_nil)
  thus "ipurge_tr_rev_aux I D U (xs @ ys) = ipurge_tr_rev_aux I D U xs"
   by (simp add: ipurge_tr_rev_aux_append_nil)
next
  fix z zs U
  let ?U' = "insert (D z) U"
  assume
    A: "\<And>U. U \<subseteq> unaffected_domains I D (D ` set ys) zs \<longrightarrow>
      ipurge_tr_rev_aux I D U (xs @ ys @ zs) =
      ipurge_tr_rev_aux I D U (xs @ ipurge_tr_aux I D (D ` set ys) zs)" and
    B: "U \<subseteq> unaffected_domains I D (D ` set ys) (zs @ [z])"
  have C: "U \<subseteq> unaffected_domains I D (D ` set ys) zs"
  proof
    fix u
    assume "u \<in> U"
    with B have "u \<in> unaffected_domains I D (D ` set ys) (zs @ [z])" ..
    thus "u \<in> unaffected_domains I D (D ` set ys) zs"
     by (simp add: unaffected_domains_def)
  qed
  have D: "ipurge_tr_rev_aux I D U (xs @ ys @ zs) =
    ipurge_tr_rev_aux I D U (xs @ ipurge_tr_aux I D (D ` set ys) zs)"
  proof -
    have "U \<subseteq> unaffected_domains I D (D ` set ys) zs \<longrightarrow>
      ipurge_tr_rev_aux I D U (xs @ ys @ zs) =
      ipurge_tr_rev_aux I D U (xs @ ipurge_tr_aux I D (D ` set ys) zs)"
     using A .
    thus ?thesis using C ..
  qed
  have E: "\<not> (\<exists>v \<in> sinks_aux I D (D ` set ys) zs. (v, D z) \<in> I) \<longrightarrow>
    ipurge_tr_rev_aux I D ?U' (xs @ ys @ zs) =
    ipurge_tr_rev_aux I D ?U' (xs @ ipurge_tr_aux I D (D ` set ys) zs)"
    (is "?P \<longrightarrow> ?Q")
  proof
    assume ?P
    have "?U' \<subseteq> unaffected_domains I D (D ` set ys) zs \<longrightarrow>
      ipurge_tr_rev_aux I D ?U' (xs @ ys @ zs) =
      ipurge_tr_rev_aux I D ?U' (xs @ ipurge_tr_aux I D (D ` set ys) zs)"
     using A .
    moreover have "?U' \<subseteq> unaffected_domains I D (D ` set ys) zs"
     by (simp add: C, simp add: unaffected_domains_def \<open>?P\<close> [simplified])
    ultimately show ?Q ..
  qed
  show "ipurge_tr_rev_aux I D U (xs @ ys @ zs @ [z]) =
    ipurge_tr_rev_aux I D U (xs @ ipurge_tr_aux I D (D ` set ys) (zs @ [z]))"
  proof (cases "\<exists>v \<in> sinks_aux I D (D ` set ys) zs. (v, D z) \<in> I",
   simp_all (no_asm_simp))
    case True
    have "\<not> (\<exists>u \<in> U. (D z, u) \<in> I)"
    proof
      assume "\<exists>u \<in> U. (D z, u) \<in> I"
      then obtain u where F: "u \<in> U" and G: "(D z, u) \<in> I" ..
      have "D z \<in> sinks_aux I D (D ` set ys) (zs @ [z])" using True by simp
      with G have "\<exists>v \<in> sinks_aux I D (D ` set ys) (zs @ [z]). (v, u) \<in> I" ..
      moreover have "u \<in> unaffected_domains I D (D ` set ys) (zs @ [z])"
       using B and F ..
      hence "\<not> (\<exists>v \<in> sinks_aux I D (D ` set ys) (zs @ [z]). (v, u) \<in> I)"
       by (simp add: unaffected_domains_def)
      ultimately show False by contradiction
    qed
    hence "ipurge_tr_rev_aux I D U ((xs @ ys @ zs) @ [z]) =
      ipurge_tr_rev_aux I D U (xs @ ys @ zs)"
     by (subst ipurge_tr_rev_aux_append, simp)
    also have "\<dots> = ipurge_tr_rev_aux I D U
      (xs @ ipurge_tr_aux I D (D ` set ys) zs)"
     using D .
    finally show "ipurge_tr_rev_aux I D U (xs @ ys @ zs @ [z]) =
      ipurge_tr_rev_aux I D U (xs @ ipurge_tr_aux I D (D ` set ys) zs)"
     by simp
  next
    case False
    note F = this
    show "ipurge_tr_rev_aux I D U (xs @ ys @ zs @ [z]) =
      ipurge_tr_rev_aux I D U (xs @ ipurge_tr_aux I D (D ` set ys) zs @ [z])"
    proof (cases "\<exists>u \<in> U. (D z, u) \<in> I")
      case True
      hence "ipurge_tr_rev_aux I D U ((xs @ ys @ zs) @ [z]) =
        ipurge_tr_rev_aux I D ?U' (xs @ ys @ zs) @ [z]"
       by (subst ipurge_tr_rev_aux_append, simp)
      also have "\<dots> =
        ipurge_tr_rev_aux I D ?U' (xs @ ipurge_tr_aux I D (D ` set ys) zs) @ [z]"
       using E and F by simp
      also have "\<dots> =
        ipurge_tr_rev_aux I D U ((xs @ ipurge_tr_aux I D (D ` set ys) zs) @ [z])"
       using True by (subst ipurge_tr_rev_aux_append, simp)
      finally show ?thesis by simp
    next
      case False
      hence "ipurge_tr_rev_aux I D U ((xs @ ys @ zs) @ [z]) =
        ipurge_tr_rev_aux I D U (xs @ ys @ zs)"
       by (subst ipurge_tr_rev_aux_append, simp)
      also have "\<dots> =
        ipurge_tr_rev_aux I D U (xs @ ipurge_tr_aux I D (D ` set ys) zs)"
       using D .
      also have "\<dots> =
        ipurge_tr_rev_aux I D U ((xs @ ipurge_tr_aux I D (D ` set ys) zs) @ [z])"
       using False by (subst ipurge_tr_rev_aux_append, simp)
      finally show ?thesis by simp
    qed
  qed
qed

lemma ipurge_tr_rev_ipurge_tr_aux_2 [rule_format]:
 "U \<subseteq> unaffected_domains I D (D ` set ys) zs \<longrightarrow>
  ipurge_tr_rev_aux I D U (xs @ zs) =
  ipurge_tr_rev_aux I D U (xs @ ys @ ipurge_tr_aux I D (D ` set ys) zs)"
proof (induction zs arbitrary: U rule: rev_induct, rule_tac [!] impI, simp)
  fix U
  assume A: "U \<subseteq> unaffected_domains I D (D ` set ys) []"
  have "\<forall>u \<in> U. \<forall>v \<in> D ` set ys. (v, u) \<notin> I"
  proof
    fix u
    assume "u \<in> U"
    with A have "u \<in> unaffected_domains I D (D ` set ys) []" ..
    thus "\<forall>v \<in> D ` set ys. (v, u) \<notin> I" by (simp add: unaffected_domains_def)
  qed
  hence "ipurge_tr_rev_aux I D U ys = []" by (simp add: ipurge_tr_rev_aux_nil)
  hence "ipurge_tr_rev_aux I D U (xs @ ys) = ipurge_tr_rev_aux I D U xs"
   by (simp add: ipurge_tr_rev_aux_append_nil)
  thus "ipurge_tr_rev_aux I D U xs = ipurge_tr_rev_aux I D U (xs @ ys)" ..
next
  fix z zs U
  let ?U' = "insert (D z) U"
  assume
    A: "\<And>U. U \<subseteq> unaffected_domains I D (D ` set ys) zs \<longrightarrow>
      ipurge_tr_rev_aux I D U (xs @ zs) =
      ipurge_tr_rev_aux I D U (xs @ ys @ ipurge_tr_aux I D (D ` set ys) zs)" and
    B: "U \<subseteq> unaffected_domains I D (D ` set ys) (zs @ [z])"
  have C: "U \<subseteq> unaffected_domains I D (D ` set ys) zs"
  proof
    fix u
    assume "u \<in> U"
    with B have "u \<in> unaffected_domains I D (D ` set ys) (zs @ [z])" ..
    thus "u \<in> unaffected_domains I D (D ` set ys) zs"
     by (simp add: unaffected_domains_def)
  qed
  have D: "ipurge_tr_rev_aux I D U (xs @ zs) =
    ipurge_tr_rev_aux I D U (xs @ ys @ ipurge_tr_aux I D (D ` set ys) zs)"
  proof -
    have "U \<subseteq> unaffected_domains I D (D ` set ys) zs \<longrightarrow>
      ipurge_tr_rev_aux I D U (xs @ zs) =
      ipurge_tr_rev_aux I D U (xs @ ys @ ipurge_tr_aux I D (D ` set ys) zs)"
     using A .
    thus ?thesis using C ..
  qed
  have E: "\<not> (\<exists>v \<in> sinks_aux I D (D ` set ys) zs. (v, D z) \<in> I) \<longrightarrow>
    ipurge_tr_rev_aux I D ?U' (xs @ zs) =
    ipurge_tr_rev_aux I D ?U' (xs @ ys @ ipurge_tr_aux I D (D ` set ys) zs)"
    (is "?P \<longrightarrow> ?Q")
  proof
    assume ?P
    have "?U' \<subseteq> unaffected_domains I D (D ` set ys) zs \<longrightarrow>
      ipurge_tr_rev_aux I D ?U' (xs @ zs) =
      ipurge_tr_rev_aux I D ?U' (xs @ ys @ ipurge_tr_aux I D (D ` set ys) zs)"
     using A .
    moreover have "?U' \<subseteq> unaffected_domains I D (D ` set ys) zs"
     by (simp add: C, simp add: unaffected_domains_def \<open>?P\<close> [simplified])
    ultimately show ?Q ..
  qed
  show "ipurge_tr_rev_aux I D U (xs @ zs @ [z]) =
    ipurge_tr_rev_aux I D U (xs @ ys @ ipurge_tr_aux I D (D ` set ys) (zs @ [z]))"
  proof (cases "\<exists>v \<in> sinks_aux I D (D ` set ys) zs. (v, D z) \<in> I",
   simp_all (no_asm_simp))
    case True
    have "\<not> (\<exists>u \<in> U. (D z, u) \<in> I)"
    proof
      assume "\<exists>u \<in> U. (D z, u) \<in> I"
      then obtain u where F: "u \<in> U" and G: "(D z, u) \<in> I" ..
      have "D z \<in> sinks_aux I D (D ` set ys) (zs @ [z])" using True by simp
      with G have "\<exists>v \<in> sinks_aux I D (D ` set ys) (zs @ [z]). (v, u) \<in> I" ..
      moreover have "u \<in> unaffected_domains I D (D ` set ys) (zs @ [z])"
       using B and F ..
      hence "\<not> (\<exists>v \<in> sinks_aux I D (D ` set ys) (zs @ [z]). (v, u) \<in> I)"
       by (simp add: unaffected_domains_def)
      ultimately show False by contradiction
    qed
    hence "ipurge_tr_rev_aux I D U ((xs @ zs) @ [z]) =
      ipurge_tr_rev_aux I D U (xs @ zs)"
     by (subst ipurge_tr_rev_aux_append, simp)
    also have
     "\<dots> = ipurge_tr_rev_aux I D U (xs @ ys @ ipurge_tr_aux I D (D ` set ys) zs)"
     using D .
    finally show "ipurge_tr_rev_aux I D U (xs @ zs @ [z]) =
      ipurge_tr_rev_aux I D U (xs @ ys @ ipurge_tr_aux I D (D ` set ys) zs)"
     by simp
  next
    case False
    note F = this
    show "ipurge_tr_rev_aux I D U (xs @ zs @ [z]) =
      ipurge_tr_rev_aux I D U (xs @ ys @ ipurge_tr_aux I D (D ` set ys) zs @ [z])"
    proof (cases "\<exists>u \<in> U. (D z, u) \<in> I")
      case True
      hence "ipurge_tr_rev_aux I D U ((xs @ zs) @ [z]) =
        ipurge_tr_rev_aux I D ?U' (xs @ zs) @ [z]"
       by (subst ipurge_tr_rev_aux_append, simp)
      also have "\<dots> =
        ipurge_tr_rev_aux I D ?U'
        (xs @ ys @ ipurge_tr_aux I D (D ` set ys) zs) @ [z]"
       using E and F by simp
      also have "\<dots> =
        ipurge_tr_rev_aux I D U
        ((xs @ ys @ ipurge_tr_aux I D (D ` set ys) zs) @ [z])"
       using True by (subst ipurge_tr_rev_aux_append, simp)
      finally show ?thesis by simp
    next
      case False
      hence "ipurge_tr_rev_aux I D U ((xs @ zs) @ [z]) =
        ipurge_tr_rev_aux I D U (xs @ zs)"
       by (subst ipurge_tr_rev_aux_append, simp)
      also have "\<dots> =
        ipurge_tr_rev_aux I D U (xs @ ys @ ipurge_tr_aux I D (D ` set ys) zs)"
       using D .
      also have "\<dots> =
        ipurge_tr_rev_aux I D U
        ((xs @ ys @ ipurge_tr_aux I D (D ` set ys) zs) @ [z])"
       using False by (subst ipurge_tr_rev_aux_append, simp)
      finally show ?thesis by simp
    qed
  qed
qed

lemma ipurge_tr_rev_ipurge_tr_1:
  assumes A: "u \<in> unaffected_domains I D {D y} zs"
  shows "ipurge_tr_rev I D u (xs @ y # zs) =
    ipurge_tr_rev I D u (xs @ ipurge_tr I D (D y) zs)"
proof -
  have "ipurge_tr_rev I D u (xs @ y # zs) =
    ipurge_tr_rev_aux I D {u} (xs @ [y] @ zs)"
   by (simp add: ipurge_tr_rev_aux_single_dom)
  also have "\<dots> = ipurge_tr_rev_aux I D {u}
    (xs @ ipurge_tr_aux I D (D ` set [y]) zs)"
   by (rule ipurge_tr_rev_ipurge_tr_aux_1, simp add: A)
  also have "\<dots> = ipurge_tr_rev I D u (xs @ ipurge_tr I D (D y) zs)"
   by (simp add: ipurge_tr_aux_single_dom ipurge_tr_rev_aux_single_dom)
  finally show ?thesis .
qed

lemma ipurge_tr_rev_ipurge_tr_2:
  assumes A: "u \<in> unaffected_domains I D {D y} zs"
  shows "ipurge_tr_rev I D u (xs @ zs) =
    ipurge_tr_rev I D u (xs @ y # ipurge_tr I D (D y) zs)"
proof -
  have "ipurge_tr_rev I D u (xs @ zs) = ipurge_tr_rev_aux I D {u} (xs @ zs)"
   by (simp add: ipurge_tr_rev_aux_single_dom)
  also have
   "\<dots> = ipurge_tr_rev_aux I D {u} (xs @ [y] @ ipurge_tr_aux I D (D ` set [y]) zs)"
   by (rule ipurge_tr_rev_ipurge_tr_aux_2, simp add: A)
  also have "\<dots> = ipurge_tr_rev I D u (xs @ y # ipurge_tr I D (D y) zs)"
   by (simp add: ipurge_tr_aux_single_dom ipurge_tr_rev_aux_single_dom)
  finally show ?thesis .
qed

lemma iu_condition_imply_secure_aux_1:
  assumes
    RUC: "ref_union_closed P" and
    IU: "weakly_future_consistent P I D (rel_ipurge P I D)" and
    A: "(xs @ y # ys, Y) \<in> failures P" and
    B: "xs @ ipurge_tr I D (D y) ys \<in> traces P" and
    C: "\<exists>y'. y' \<in> ipurge_ref I D (D y) ys Y"
  shows "(xs @ ipurge_tr I D (D y) ys, ipurge_ref I D (D y) ys Y) \<in> failures P"
proof -
  let ?A = "singleton_set (ipurge_ref I D (D y) ys Y)"
  have "(\<exists>X. X \<in> ?A) \<longrightarrow>
    (\<forall>X \<in> ?A. (xs @ ipurge_tr I D (D y) ys, X) \<in> failures P) \<longrightarrow>
    (xs @ ipurge_tr I D (D y) ys, \<Union>X \<in> ?A. X) \<in> failures P"
   using RUC by (simp add: ref_union_closed_def)
  moreover obtain y' where D: "y' \<in> ipurge_ref I D (D y) ys Y" using C ..
  hence "\<exists>X. X \<in> ?A" by (simp add: singleton_set_some, rule exI)
  ultimately have "(\<forall>X \<in> ?A. (xs @ ipurge_tr I D (D y) ys, X) \<in> failures P) \<longrightarrow>
    (xs @ ipurge_tr I D (D y) ys, \<Union>X \<in> ?A. X) \<in> failures P" ..
  moreover have "\<forall>X \<in> ?A. (xs @ ipurge_tr I D (D y) ys, X) \<in> failures P"
  proof (rule ballI, simp add: singleton_set_def, erule bexE, simp)
    fix y'
    have "\<forall>u \<in> range D \<inter> (-I) `` range D.
      \<forall>xs ys. (xs, ys) \<in> rel_ipurge P I D u \<longrightarrow>
      ref_dom_events P D u xs = ref_dom_events P D u ys"
     using IU by (simp add: weakly_future_consistent_def)
    moreover assume E: "y' \<in> ipurge_ref I D (D y) ys Y"
    hence "(D y, D y') \<notin> I" by (simp add: ipurge_ref_def)
    hence "D y' \<in> range D \<inter> (-I) `` range D" by (simp add: Image_iff, rule exI)
    ultimately have "\<forall>xs ys. (xs, ys) \<in> rel_ipurge P I D (D y') \<longrightarrow>
      ref_dom_events P D (D y') xs = ref_dom_events P D (D y') ys" ..
    hence
      F: "(xs @ y # ys, xs @ ipurge_tr I D (D y) ys) \<in> rel_ipurge P I D (D y') \<longrightarrow>
        ref_dom_events P D (D y') (xs @ y # ys) =
        ref_dom_events P D (D y') (xs @ ipurge_tr I D (D y) ys)"
     by blast
    have "y' \<in> {x \<in> Y. D x \<in> unaffected_domains I D {D y} ys}"
     using E by (simp add: unaffected_domains_single_dom)
    hence "D y' \<in> unaffected_domains I D {D y} ys" by simp
    hence "ipurge_tr_rev I D (D y') (xs @ y # ys) =
      ipurge_tr_rev I D (D y') (xs @ ipurge_tr I D (D y) ys)"
     by (rule ipurge_tr_rev_ipurge_tr_1)
    moreover have "xs @ y # ys \<in> traces P" using A by (rule failures_traces)
    ultimately have
     "(xs @ y # ys, xs @ ipurge_tr I D (D y) ys) \<in> rel_ipurge P I D (D y')"
     using B by (simp add: rel_ipurge_def)
    with F have "ref_dom_events P D (D y') (xs @ y # ys) =
      ref_dom_events P D (D y') (xs @ ipurge_tr I D (D y) ys)" ..
    moreover have "y' \<in> ref_dom_events P D (D y') (xs @ y # ys)"
    proof (simp add: ref_dom_events_def refusals_def)
      have "{y'} \<subseteq> Y" using E by (simp add: ipurge_ref_def)
      with A show "(xs @ y # ys, {y'}) \<in> failures P" by (rule process_rule_3)
    qed
    ultimately have "y' \<in> ref_dom_events P D (D y')
      (xs @ ipurge_tr I D (D y) ys)"
     by simp
    thus "(xs @ ipurge_tr I D (D y) ys, {y'}) \<in> failures P"
     by (simp add: ref_dom_events_def refusals_def)
  qed
  ultimately have "(xs @ ipurge_tr I D (D y) ys, \<Union>X \<in> ?A. X) \<in> failures P" ..
  thus ?thesis by (simp only: singleton_set_union)
qed

lemma iu_condition_imply_secure_aux_2:
  assumes
    RUC: "ref_union_closed P" and
    IU: "weakly_future_consistent P I D (rel_ipurge P I D)" and
    A: "(xs @ zs, Z) \<in> failures P" and
    B: "xs @ y # ipurge_tr I D (D y) zs \<in> traces P" and
    C: "\<exists>z'. z' \<in> ipurge_ref I D (D y) zs Z"
  shows "(xs @ y # ipurge_tr I D (D y) zs, ipurge_ref I D (D y) zs Z) \<in> failures P"
proof -
  let ?A = "singleton_set (ipurge_ref I D (D y) zs Z)"
  have "(\<exists>X. X \<in> ?A) \<longrightarrow>
    (\<forall>X \<in> ?A. (xs @ y # ipurge_tr I D (D y) zs, X) \<in> failures P) \<longrightarrow>
    (xs @ y # ipurge_tr I D (D y) zs, \<Union>X \<in> ?A. X) \<in> failures P"
   using RUC by (simp add: ref_union_closed_def)
  moreover obtain z' where D: "z' \<in> ipurge_ref I D (D y) zs Z" using C ..
  hence "\<exists>X. X \<in> ?A" by (simp add: singleton_set_some, rule exI)
  ultimately have
   "(\<forall>X \<in> ?A. (xs @ y # ipurge_tr I D (D y) zs, X) \<in> failures P) \<longrightarrow>
    (xs @ y # ipurge_tr I D (D y) zs, \<Union>X \<in> ?A. X) \<in> failures P" ..
  moreover have "\<forall>X \<in> ?A. (xs @ y # ipurge_tr I D (D y) zs, X) \<in> failures P"
  proof (rule ballI, simp add: singleton_set_def, erule bexE, simp)
    fix z'
    have "\<forall>u \<in> range D \<inter> (-I) `` range D.
      \<forall>xs ys. (xs, ys) \<in> rel_ipurge P I D u \<longrightarrow>
      ref_dom_events P D u xs = ref_dom_events P D u ys"
     using IU by (simp add: weakly_future_consistent_def)
    moreover assume E: "z' \<in> ipurge_ref I D (D y) zs Z"
    hence "(D y, D z') \<notin> I" by (simp add: ipurge_ref_def)
    hence "D z' \<in> range D \<inter> (-I) `` range D" by (simp add: Image_iff, rule exI)
    ultimately have "\<forall>xs ys. (xs, ys) \<in> rel_ipurge P I D (D z') \<longrightarrow>
      ref_dom_events P D (D z') xs = ref_dom_events P D (D z') ys" ..
    hence
      F: "(xs @ zs, xs @ y # ipurge_tr I D (D y) zs) \<in> rel_ipurge P I D (D z') \<longrightarrow>
        ref_dom_events P D (D z') (xs @ zs) =
        ref_dom_events P D (D z') (xs @ y # ipurge_tr I D (D y) zs)"
     by blast
    have "z' \<in> {x \<in> Z. D x \<in> unaffected_domains I D {D y} zs}"
     using E by (simp add: unaffected_domains_single_dom)
    hence "D z' \<in> unaffected_domains I D {D y} zs" by simp
    hence "ipurge_tr_rev I D (D z') (xs @ zs) =
      ipurge_tr_rev I D (D z') (xs @ y # ipurge_tr I D (D y) zs)"
     by (rule ipurge_tr_rev_ipurge_tr_2)
    moreover have "xs @ zs \<in> traces P" using A by (rule failures_traces)
    ultimately have
     "(xs @ zs, xs @ y # ipurge_tr I D (D y) zs) \<in> rel_ipurge P I D (D z')"
     using B by (simp add: rel_ipurge_def)
    with F have "ref_dom_events P D (D z') (xs @ zs) =
      ref_dom_events P D (D z') (xs @ y # ipurge_tr I D (D y) zs)" ..
    moreover have "z' \<in> ref_dom_events P D (D z') (xs @ zs)"
    proof (simp add: ref_dom_events_def refusals_def)
      have "{z'} \<subseteq> Z" using E by (simp add: ipurge_ref_def)
      with A show "(xs @ zs, {z'}) \<in> failures P" by (rule process_rule_3)
    qed
    ultimately have "z' \<in> ref_dom_events P D (D z')
      (xs @ y # ipurge_tr I D (D y) zs)"
     by simp
    thus "(xs @ y # ipurge_tr I D (D y) zs, {z'}) \<in> failures P"
     by (simp add: ref_dom_events_def refusals_def)
  qed
  ultimately have
   "(xs @ y # ipurge_tr I D (D y) zs, \<Union>X \<in> ?A. X) \<in> failures P" ..
  thus ?thesis by (simp only: singleton_set_union)
qed

lemma iu_condition_imply_secure_1 [rule_format]:
  assumes
    RUC: "ref_union_closed P" and
    IU: "weakly_future_consistent P I D (rel_ipurge P I D)"
  shows "(xs @ y # ys, Y) \<in> failures P \<longrightarrow>
    (xs @ ipurge_tr I D (D y) ys, ipurge_ref I D (D y) ys Y) \<in> failures P"
proof (induction ys arbitrary: Y rule: rev_induct, rule_tac [!] impI)
  fix Y
  assume A: "(xs @ [y], Y) \<in> failures P"
  show "(xs @ ipurge_tr I D (D y) [], ipurge_ref I D (D y) [] Y) \<in> failures P"
  proof (cases "\<exists>y'. y' \<in> ipurge_ref I D (D y) [] Y")
    case True
    have "xs @ [y] \<in> traces P" using A by (rule failures_traces)
    hence "xs \<in> traces P" by (rule process_rule_2_traces)
    hence "xs @ ipurge_tr I D (D y) [] \<in> traces P" by simp
    with RUC and IU and A show ?thesis
     using True by (rule iu_condition_imply_secure_aux_1)
  next
    case False
    moreover have "(xs, {}) \<in> failures P" using A by (rule process_rule_2)
    ultimately show ?thesis by simp
  qed
next
  fix y' ys Y
  assume
    A: "\<And>Y'. (xs @ y # ys, Y') \<in> failures P \<longrightarrow>
      (xs @ ipurge_tr I D (D y) ys, ipurge_ref I D (D y) ys Y') \<in> failures P" and
    B: "(xs @ y # ys @ [y'], Y) \<in> failures P"
  have "(xs @ y # ys, {}) \<in> failures P \<longrightarrow>
    (xs @ ipurge_tr I D (D y) ys, ipurge_ref I D (D y) ys {}) \<in> failures P"
    (is "_ \<longrightarrow> (_, ?Y') \<in> _")
   using A .
  moreover have "((xs @ y # ys) @ [y'], Y) \<in> failures P" using B by simp
  hence C: "(xs @ y # ys, {}) \<in> failures P" by (rule process_rule_2)
  ultimately have "(xs @ ipurge_tr I D (D y) ys, ?Y') \<in> failures P" ..
  moreover have "{} \<subseteq> ?Y'" ..
  ultimately have D: "(xs @ ipurge_tr I D (D y) ys, {}) \<in> failures P"
   by (rule process_rule_3)
  have E: "xs @ ipurge_tr I D (D y) (ys @ [y']) \<in> traces P"
  proof (cases "D y' \<in> sinks I D (D y) (ys @ [y'])")
    case True
    hence "(xs @ ipurge_tr I D (D y) (ys @ [y']), {}) \<in> failures P" using D by simp
    thus ?thesis by (rule failures_traces)
  next
    case False
    have "\<forall>u \<in> range D \<inter> (-I) `` range D.
      \<forall>xs ys. (xs, ys) \<in> rel_ipurge P I D u \<longrightarrow>
      next_dom_events P D u xs = next_dom_events P D u ys"
     using IU by (simp add: weakly_future_consistent_def)
    moreover have "(D y, D y') \<notin> I"
     using False by (simp add: sinks_interference_eq [symmetric] del: sinks.simps)
    hence "D y' \<in> range D \<inter> (-I) `` range D" by (simp add: Image_iff, rule exI)
    ultimately have "\<forall>xs ys. (xs, ys) \<in> rel_ipurge P I D (D y') \<longrightarrow>
      next_dom_events P D (D y') xs = next_dom_events P D (D y') ys" ..
    hence
      F: "(xs @ y # ys, xs @ ipurge_tr I D (D y) ys) \<in> rel_ipurge P I D (D y') \<longrightarrow>
        next_dom_events P D (D y') (xs @ y # ys) =
        next_dom_events P D (D y') (xs @ ipurge_tr I D (D y) ys)"
     by blast
    have "\<forall>v \<in> insert (D y) (sinks I D (D y) ys). (v, D y') \<notin> I"
     using False by (simp add: sinks_interference_eq [symmetric] del: sinks.simps)
    hence "\<forall>v \<in> sinks_aux I D {D y} ys. (v, D y') \<notin> I"
     by (simp add: sinks_aux_single_dom)
    hence "D y' \<in> unaffected_domains I D {D y} ys"
     by (simp add: unaffected_domains_def)
    hence "ipurge_tr_rev I D (D y') (xs @ y # ys) =
      ipurge_tr_rev I D (D y') (xs @ ipurge_tr I D (D y) ys)"
     by (rule ipurge_tr_rev_ipurge_tr_1)
    moreover have "xs @ y # ys \<in> traces P" using C by (rule failures_traces)
    moreover have "xs @ ipurge_tr I D (D y) ys \<in> traces P"
     using D by (rule failures_traces)
    ultimately have
     "(xs @ y # ys, xs @ ipurge_tr I D (D y) ys) \<in> rel_ipurge P I D (D y')"
     by (simp add: rel_ipurge_def)
    with F have "next_dom_events P D (D y') (xs @ y # ys) =
      next_dom_events P D (D y') (xs @ ipurge_tr I D (D y) ys)" ..
    moreover have "y' \<in> next_dom_events P D (D y') (xs @ y # ys)"
    proof (simp add: next_dom_events_def next_events_def)
    qed (rule failures_traces [OF B])
    ultimately have "y' \<in> next_dom_events P D (D y')
      (xs @ ipurge_tr I D (D y) ys)"
     by simp
    hence "xs @ ipurge_tr I D (D y) ys @ [y'] \<in> traces P"
     by (simp add: next_dom_events_def next_events_def)
    thus ?thesis using False by simp
  qed
  show "(xs @ ipurge_tr I D (D y) (ys @ [y']), ipurge_ref I D (D y) (ys @ [y']) Y)
    \<in> failures P"
  proof (cases "\<exists>x. x \<in> ipurge_ref I D (D y) (ys @ [y']) Y")
    case True
    with RUC and IU and B and E show ?thesis by (rule iu_condition_imply_secure_aux_1)
  next
    case False
    moreover have "(xs @ ipurge_tr I D (D y) (ys @ [y']), {}) \<in> failures P"
     using E by (rule traces_failures)
    ultimately show ?thesis by simp
  qed
qed

lemma iu_condition_imply_secure_2 [rule_format]:
  assumes
    RUC: "ref_union_closed P" and
    IU: "weakly_future_consistent P I D (rel_ipurge P I D)" and
    Y: "xs @ [y] \<in> traces P"
  shows "(xs @ zs, Z) \<in> failures P \<longrightarrow>
    (xs @ y # ipurge_tr I D (D y) zs, ipurge_ref I D (D y) zs Z) \<in> failures P"
proof (induction zs arbitrary: Z rule: rev_induct, rule_tac [!] impI)
  fix Z
  assume A: "(xs @ [], Z) \<in> failures P"
  show "(xs @ y # ipurge_tr I D (D y) [], ipurge_ref I D (D y) [] Z) \<in> failures P"
  proof (cases "\<exists>z'. z' \<in> ipurge_ref I D (D y) [] Z")
    case True
    have "xs @ y # ipurge_tr I D (D y) [] \<in> traces P" using Y by simp
    with RUC and IU and A show ?thesis
     using True by (rule iu_condition_imply_secure_aux_2)
  next
    case False
    moreover have "(xs @ [y], {}) \<in> failures P" using Y by (rule traces_failures)
    ultimately show ?thesis by simp
  qed
next
  fix z zs Z
  assume
    A: "\<And>Z. (xs @ zs, Z) \<in> failures P \<longrightarrow>
      (xs @ y # ipurge_tr I D (D y) zs, ipurge_ref I D (D y) zs Z) \<in> failures P" and
    B: "(xs @ zs @ [z], Z) \<in> failures P"
  have "(xs @ zs, {}) \<in> failures P \<longrightarrow>
    (xs @ y # ipurge_tr I D (D y) zs, ipurge_ref I D (D y) zs {}) \<in> failures P"
    (is "_ \<longrightarrow> (_, ?Z') \<in> _")
   using A .
  moreover have "((xs @ zs) @ [z], Z) \<in> failures P" using B by simp
  hence C: "(xs @ zs, {}) \<in> failures P" by (rule process_rule_2)
  ultimately have "(xs @ y # ipurge_tr I D (D y) zs, ?Z') \<in> failures P" ..
  moreover have "{} \<subseteq> ?Z'" ..
  ultimately have D: "(xs @ y # ipurge_tr I D (D y) zs, {}) \<in> failures P"
   by (rule process_rule_3)
  have E: "xs @ y # ipurge_tr I D (D y) (zs @ [z]) \<in> traces P"
  proof (cases "D z \<in> sinks I D (D y) (zs @ [z])")
    case True
    hence "(xs @ y # ipurge_tr I D (D y) (zs @ [z]), {}) \<in> failures P"
     using D by simp
    thus ?thesis by (rule failures_traces)
  next
    case False
    have "\<forall>u \<in> range D \<inter> (-I) `` range D.
      \<forall>xs ys. (xs, ys) \<in> rel_ipurge P I D u \<longrightarrow>
      next_dom_events P D u xs = next_dom_events P D u ys"
     using IU by (simp add: weakly_future_consistent_def)
    moreover have "(D y, D z) \<notin> I"
     using False by (simp add: sinks_interference_eq [symmetric] del: sinks.simps)
    hence "D z \<in> range D \<inter> (-I) `` range D" by (simp add: Image_iff, rule exI)
    ultimately have "\<forall>xs ys. (xs, ys) \<in> rel_ipurge P I D (D z) \<longrightarrow>
      next_dom_events P D (D z) xs = next_dom_events P D (D z) ys" ..
    hence
      F: "(xs @ zs, xs @ y # ipurge_tr I D (D y) zs) \<in> rel_ipurge P I D (D z) \<longrightarrow>
        next_dom_events P D (D z) (xs @ zs) =
        next_dom_events P D (D z) (xs @ y # ipurge_tr I D (D y) zs)"
     by blast
    have "\<forall>v \<in> insert (D y) (sinks I D (D y) zs). (v, D z) \<notin> I"
     using False by (simp add: sinks_interference_eq [symmetric] del: sinks.simps)
    hence "\<forall>v \<in> sinks_aux I D {D y} zs. (v, D z) \<notin> I"
     by (simp add: sinks_aux_single_dom)
    hence "D z \<in> unaffected_domains I D {D y} zs"
     by (simp add: unaffected_domains_def)
    hence "ipurge_tr_rev I D (D z) (xs @ zs) =
      ipurge_tr_rev I D (D z) (xs @ y # ipurge_tr I D (D y) zs)"
     by (rule ipurge_tr_rev_ipurge_tr_2)
    moreover have "xs @ zs \<in> traces P" using C by (rule failures_traces)
    moreover have "xs @ y # ipurge_tr I D (D y) zs \<in> traces P"
     using D by (rule failures_traces)
    ultimately have
     "(xs @ zs, xs @ y # ipurge_tr I D (D y) zs) \<in> rel_ipurge P I D (D z)"
     by (simp add: rel_ipurge_def)
    with F have "next_dom_events P D (D z) (xs @ zs) =
      next_dom_events P D (D z) (xs @ y # ipurge_tr I D (D y) zs)" ..
    moreover have "z \<in> next_dom_events P D (D z) (xs @ zs)"
    proof (simp add: next_dom_events_def next_events_def)
    qed (rule failures_traces [OF B])
    ultimately have "z \<in> next_dom_events P D (D z)
      (xs @ y # ipurge_tr I D (D y) zs)"
     by simp
    hence "xs @ y # ipurge_tr I D (D y) zs @ [z] \<in> traces P"
     by (simp add: next_dom_events_def next_events_def)
    thus ?thesis using False by simp
  qed
  show "(xs @ y # ipurge_tr I D (D y) (zs @ [z]),
    ipurge_ref I D (D y) (zs @ [z]) Z)
    \<in> failures P"
  proof (cases "\<exists>x. x \<in> ipurge_ref I D (D y) (zs @ [z]) Z")
    case True
    with RUC and IU and B and E show ?thesis by (rule iu_condition_imply_secure_aux_2)
  next
    case False
    moreover have "(xs @ y # ipurge_tr I D (D y) (zs @ [z]), {}) \<in> failures P"
     using E by (rule traces_failures)
    ultimately show ?thesis by simp
  qed
qed

theorem iu_condition_imply_secure:
  assumes
    RUC: "ref_union_closed P" and
    IU: "weakly_future_consistent P I D (rel_ipurge P I D)"
  shows "secure P I D"
proof (simp add: secure_def futures_def, (rule allI)+, rule impI, erule conjE)
  fix xs y ys Y zs Z
  assume
    A: "(xs @ y # ys, Y) \<in> failures P" and
    B: "(xs @ zs, Z) \<in> failures P"
  show "(xs @ ipurge_tr I D (D y) ys, ipurge_ref I D (D y) ys Y) \<in> failures P \<and>
    (xs @ y # ipurge_tr I D (D y) zs, ipurge_ref I D (D y) zs Z) \<in> failures P"
    (is "?P \<and> ?Q")
  proof
    show ?P using RUC and IU and A by (rule iu_condition_imply_secure_1)
  next
    have "((xs @ [y]) @ ys, Y) \<in> failures P" using A by simp
    hence "(xs @ [y], {}) \<in> failures P" by (rule process_rule_2_failures)
    hence "xs @ [y] \<in> traces P" by (rule failures_traces)
    with RUC and IU show ?Q using B by (rule iu_condition_imply_secure_2)
  qed
qed


subsection "The Ipurge Unwinding Theorem: proof of condition necessity"

text \<open>
Here below, it is proven that the condition expressed by the Ipurge Unwinding Theorem is necessary
for security. Finally, the lemmas concerning condition sufficiency and necessity are gathered in the
main theorem.

\null
\<close>

lemma secure_implies_failure_consistency_aux [rule_format]:
  assumes S: "secure P I D"
  shows "(xs @ ys @ zs, X) \<in> failures P \<longrightarrow>
    ipurge_tr_rev_aux I D (D ` (X \<union> set zs)) ys = [] \<longrightarrow> (xs @ zs, X) \<in> failures P"
proof (induction ys rule: rev_induct, simp_all, (rule impI)+)
  fix y ys
  assume *: "ipurge_tr_rev_aux I D (D ` (X \<union> set zs)) (ys @ [y]) = []"
  then have A: "\<not> (\<exists>v \<in> D ` (X \<union> set zs). (D y, v) \<in> I)"
    by (cases "\<exists>v \<in> D ` (X \<union> set zs). (D y, v) \<in> I",
        simp_all add: ipurge_tr_rev_aux_append)
  with * have B: "ipurge_tr_rev_aux I D (D ` (X \<union> set zs)) ys = []"
    by (simp add: ipurge_tr_rev_aux_append)
  assume "(xs @ ys @ y # zs, X) \<in> failures P"
  hence "(y # zs, X) \<in> futures P (xs @ ys)" by (simp add: futures_def)
  hence "(ipurge_tr I D (D y) zs, ipurge_ref I D (D y) zs X)
    \<in> futures P (xs @ ys)"
    using S by (simp add: secure_def)
  moreover have "ipurge_tr I D (D y) zs = zs" using A by (simp add: ipurge_tr_all)
  moreover have "ipurge_ref I D (D y) zs X = X" using A by (rule ipurge_ref_all)
  ultimately have "(zs, X) \<in> futures P (xs @ ys)" by simp
  hence C: "(xs @ ys @ zs, X) \<in> failures P" by (simp add: futures_def)
  assume "(xs @ ys @ zs, X) \<in> failures P \<longrightarrow>
    ipurge_tr_rev_aux I D (D ` (X \<union> set zs)) ys = [] \<longrightarrow>
    (xs @ zs, X) \<in> failures P"
  hence "ipurge_tr_rev_aux I D (D ` (X \<union> set zs)) ys = [] \<longrightarrow>
    (xs @ zs, X) \<in> failures P"
    using C ..
  thus "(xs @ zs, X) \<in> failures P" using B ..
qed

lemma secure_implies_failure_consistency [rule_format]:
  assumes S: "secure P I D"
  shows "(xs, ys) \<in> rel_ipurge_aux P I D (D ` (X \<union> set zs)) \<longrightarrow>
    (xs @ zs, X) \<in> failures P \<longrightarrow> (ys @ zs, X) \<in> failures P"
proof (induction ys arbitrary: xs zs rule: rev_induct,
 simp_all add: rel_ipurge_aux_def, (rule_tac [!] impI)+, (erule_tac [!] conjE)+)
  fix xs zs
  assume "(xs @ zs, X) \<in> failures P"
  hence "([] @ xs @ zs, X) \<in> failures P" by simp
  moreover assume "ipurge_tr_rev_aux I D (D ` (X \<union> set zs)) xs = []"
  ultimately have "([] @ zs, X) \<in> failures P"
   using S by (rule_tac secure_implies_failure_consistency_aux)
  thus "(zs, X) \<in> failures P" by simp
next
  fix y ys xs zs
  assume
    A: "\<And>xs' zs'. xs' \<in> traces P \<and> ys \<in> traces P \<and>
      ipurge_tr_rev_aux I D (D ` (X \<union> set zs')) xs' =
      ipurge_tr_rev_aux I D (D ` (X \<union> set zs')) ys \<longrightarrow>
      (xs' @ zs', X) \<in> failures P \<longrightarrow> (ys @ zs', X) \<in> failures P" and
    B: "(xs @ zs, X) \<in> failures P" and
    C: "xs \<in> traces P" and
    D: "ys @ [y] \<in> traces P" and
    E: "ipurge_tr_rev_aux I D (D ` (X \<union> set zs)) xs =
      ipurge_tr_rev_aux I D (D ` (X \<union> set zs)) (ys @ [y])"
  show "(ys @ y # zs, X) \<in> failures P"
  proof (cases "\<exists>v \<in> D ` (X \<union> set zs). (D y, v) \<in> I")
    case True
    hence F: "ipurge_tr_rev_aux I D (D ` (X \<union> set zs)) xs =
      ipurge_tr_rev_aux I D (D ` (X \<union> set (y # zs))) ys @ [y]"
     using E by (simp add: ipurge_tr_rev_aux_append)
    hence
     "\<exists>vs ws. xs = vs @ y # ws \<and> ipurge_tr_rev_aux I D (D ` (X \<union> set zs)) ws = []"
     by (rule ipurge_tr_rev_aux_last_2)
    then obtain vs and ws where
      G: "xs = vs @ y # ws \<and> ipurge_tr_rev_aux I D (D ` (X \<union> set zs)) ws = []"
     by blast
    hence "ipurge_tr_rev_aux I D (D ` (X \<union> set zs)) xs =
      ipurge_tr_rev_aux I D (D ` (X \<union> set zs)) ((vs @ [y]) @ ws)"
     by simp
    hence "ipurge_tr_rev_aux I D (D ` (X \<union> set zs)) xs =
      ipurge_tr_rev_aux I D (D ` (X \<union> set zs)) (vs @ [y])"
     using G by (simp only: ipurge_tr_rev_aux_append_nil)
    moreover have "\<exists>v \<in> D ` (X \<union> set zs). (D y, v) \<in> I"
     using F by (rule ipurge_tr_rev_aux_last_1)
    ultimately have "ipurge_tr_rev_aux I D (D ` (X \<union> set zs)) xs =
      ipurge_tr_rev_aux I D (D ` (X \<union> set (y # zs))) vs @ [y]"
     by (simp add: ipurge_tr_rev_aux_append)
    hence "ipurge_tr_rev_aux I D (D ` (X \<union> set (y # zs))) vs =
      ipurge_tr_rev_aux I D (D ` (X \<union> set (y # zs))) ys"
     using F by simp
    moreover have "vs @ y # ws \<in> traces P" using C and G by simp
    hence "vs \<in> traces P" by (rule process_rule_2_traces)
    moreover have "ys \<in> traces P" using D by (rule process_rule_2_traces)
    moreover have "vs \<in> traces P \<and> ys \<in> traces P \<and>
      ipurge_tr_rev_aux I D (D ` (X \<union> set (y # zs))) vs =
      ipurge_tr_rev_aux I D (D ` (X \<union> set (y # zs))) ys \<longrightarrow>
      (vs @ y # zs, X) \<in> failures P \<longrightarrow> (ys @ y # zs, X) \<in> failures P"
     using A .
    ultimately have H: "(vs @ y # zs, X) \<in> failures P \<longrightarrow>
      (ys @ y # zs, X) \<in> failures P"
     by simp
    have "((vs @ [y]) @ ws @ zs, X) \<in> failures P" using B and G by simp
    moreover have "ipurge_tr_rev_aux I D (D ` (X \<union> set zs)) ws = []" using G ..
    ultimately have "((vs @ [y]) @ zs, X) \<in> failures P"
     using S by (rule_tac secure_implies_failure_consistency_aux)
    thus ?thesis using H by simp
  next
    case False
    hence "ipurge_tr_rev_aux I D (D ` (X \<union> set zs)) xs =
      ipurge_tr_rev_aux I D (D ` (X \<union> set zs)) ys"
     using E by (simp add: ipurge_tr_rev_aux_append)
    moreover have "ys \<in> traces P" using D by (rule process_rule_2_traces)
    moreover have "xs \<in> traces P \<and> ys \<in> traces P \<and>
      ipurge_tr_rev_aux I D (D ` (X \<union> set zs)) xs =
      ipurge_tr_rev_aux I D (D ` (X \<union> set zs)) ys \<longrightarrow>
      (xs @ zs, X) \<in> failures P \<longrightarrow> (ys @ zs, X) \<in> failures P"
     using A .
    ultimately have "(ys @ zs, X) \<in> failures P" using B and C by simp
    hence "(zs, X) \<in> futures P ys" by (simp add: futures_def)
    moreover have "\<exists>Y. ([y], Y) \<in> futures P ys"
     using D by (simp add: traces_def Domain_iff futures_def)
    then obtain Y where "([y], Y) \<in> futures P ys" ..
    ultimately have
      "(y # ipurge_tr I D (D y) zs, ipurge_ref I D (D y) zs X) \<in> futures P ys"
     using S by (simp add: secure_def)
    moreover have "ipurge_tr I D (D y) zs = zs"
     using False by (simp add: ipurge_tr_all)
    moreover have "ipurge_ref I D (D y) zs X = X"
     using False by (rule ipurge_ref_all)
    ultimately show ?thesis by (simp add: futures_def)
  qed
qed

lemma secure_implies_trace_consistency:
 "secure P I D \<Longrightarrow> (xs, ys) \<in> rel_ipurge_aux P I D (D ` set zs) \<Longrightarrow>
  xs @ zs \<in> traces P \<Longrightarrow> ys @ zs \<in> traces P"
proof (simp add: traces_def Domain_iff, rule_tac x = "{}" in exI,
 rule secure_implies_failure_consistency, simp_all)
qed (erule exE, erule process_rule_3, simp)

lemma secure_implies_next_event_consistency:
 "secure P I D \<Longrightarrow> (xs, ys) \<in> rel_ipurge P I D (D x) \<Longrightarrow>
  x \<in> next_events P xs \<Longrightarrow> x \<in> next_events P ys"
  by (auto simp add: next_events_def rel_ipurge_aux_single_dom intro: secure_implies_trace_consistency)

lemma secure_implies_refusal_consistency:
 "secure P I D \<Longrightarrow> (xs, ys) \<in> rel_ipurge_aux P I D (D ` X) \<Longrightarrow>
  X \<in> refusals P xs \<Longrightarrow> X \<in> refusals P ys"
by (simp add: refusals_def, subst append_Nil2 [symmetric],
 rule secure_implies_failure_consistency, simp_all)

lemma secure_implies_ref_event_consistency:
 "secure P I D \<Longrightarrow> (xs, ys) \<in> rel_ipurge P I D (D x) \<Longrightarrow>
  {x} \<in> refusals P xs \<Longrightarrow> {x} \<in> refusals P ys"
by (rule secure_implies_refusal_consistency, simp_all add: rel_ipurge_aux_single_dom)

theorem secure_implies_iu_condition:
  assumes S: "secure P I D"
  shows "future_consistent P D (rel_ipurge P I D)"
proof (simp add: future_consistent_def next_dom_events_def ref_dom_events_def,
 (rule allI)+, rule impI, rule conjI, rule_tac [!] equalityI, rule_tac [!] subsetI,
 simp_all, erule_tac [!] conjE)
  fix xs ys x
  assume "(xs, ys) \<in> rel_ipurge P I D (D x)" and "x \<in> next_events P xs"
  with S show "x \<in> next_events P ys" by (rule secure_implies_next_event_consistency)
next
  fix xs ys x
  have "\<forall>u \<in> range D. equiv (traces P) (rel_ipurge P I D u)"
   using view_partition_rel_ipurge by (simp add: view_partition_def)
  hence "sym (rel_ipurge P I D (D x))" by (simp add: equiv_def)
  moreover assume "(xs, ys) \<in> rel_ipurge P I D (D x)"
  ultimately have "(ys, xs) \<in> rel_ipurge P I D (D x)" by (rule symE)
  moreover assume "x \<in> next_events P ys"
  ultimately show "x \<in> next_events P xs"
   using S by (rule_tac secure_implies_next_event_consistency)
next
  fix xs ys x
  assume "(xs, ys) \<in> rel_ipurge P I D (D x)" and "{x} \<in> refusals P xs"
  with S show "{x} \<in> refusals P ys" by (rule secure_implies_ref_event_consistency)
next
  fix xs ys x
  have "\<forall>u \<in> range D. equiv (traces P) (rel_ipurge P I D u)"
   using view_partition_rel_ipurge by (simp add: view_partition_def)
  hence "sym (rel_ipurge P I D (D x))" by (simp add: equiv_def)
  moreover assume "(xs, ys) \<in> rel_ipurge P I D (D x)"
  ultimately have "(ys, xs) \<in> rel_ipurge P I D (D x)" by (rule symE)
  moreover assume "{x} \<in> refusals P ys"
  ultimately show "{x} \<in> refusals P xs"
   using S by (rule_tac secure_implies_ref_event_consistency)
qed

theorem ipurge_unwinding:
 "ref_union_closed P \<Longrightarrow>
  secure P I D = weakly_future_consistent P I D (rel_ipurge P I D)"
proof (rule iffI, subst fc_equals_wfc_rel_ipurge [symmetric])
qed (erule secure_implies_iu_condition, rule iu_condition_imply_secure)

end
