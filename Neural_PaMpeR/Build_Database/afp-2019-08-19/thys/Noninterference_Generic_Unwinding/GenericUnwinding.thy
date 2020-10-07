(*  Title:       The Generic Unwinding Theorem for CSP Noninterference Security
    Author:      Pasquale Noce
                 Security Certification Specialist at Arjo Systems - Gep S.p.A.
                 pasquale dot noce dot lavoro at gmail dot com
                 pasquale dot noce at arjowiggins-it dot com
*)

section "The Generic Unwinding Theorem"

theory GenericUnwinding
imports Noninterference_Ipurge_Unwinding.DeterministicProcesses
begin

text \<open>
\null

The classical definition of noninterference security for a deterministic state machine with outputs
requires to consider the outputs produced by machine actions after any trace, i.e. any indefinitely
long sequence of actions, of the machine. In order to render the verification of the security of
such a machine more straightforward, there is a need of some sufficient condition for security such
that just individual actions, rather than unbounded sequences of actions, have to be taken into
consideration.

By extending previous results applying to transitive noninterference policies, Rushby \cite{R4} has
proven an unwinding theorem that provides a sufficient condition of this kind in the general case of
a possibly intransitive policy. This condition consists of a combination of predicates, which have
to be satisfied by a generic function mapping security domains into equivalence relations over
machine states.

An analogous problem arises for CSP noninterference security, whose definition given in \cite{R1}
requires to consider any possible future, i.e. any indefinitely long sequence of subsequent events
and any indefinitely large set of refused events associated to that sequence, for each process
trace.

This paper provides a sufficient condition for CSP noninterference security, which indeed requires
to just consider individual accepted and refused events and applies to the general case of a
possibly intransitive policy. This condition follows Rushby's one for classical noninterference
security; in some detail, it consists of a combination of predicates, which are the translations of
Rushby's ones into Hoare's Communicating Sequential Processes model of computation \cite{R3}. These
predicates have to be satisfied by a generic function mapping security domains into equivalence
relations over process traces; hence the name given to the condition,
\emph{Generic Unwinding Theorem}. Variants of this theorem applying to deterministic processes and
trace set processes (cf. \cite{R2}) are also proven.

The sufficient condition for security expressed by the Generic Unwinding Theorem would be even more
valuable if it also provided a necessary condition, viz. if for any secure process, there existed
some domain-relation map satisfying the condition. Particularly, a constructive proof of such
proposition, showing that some specified domain-relation map satisfies the condition whatever secure
process is given, would permit to determine whether a process is secure or not by verifying whether
the condition is satisfied by that map or not. However, this paper proves by counterexample that the
Generic Unwinding Theorem does not express a necessary condition for security as well, viz. a
process and a noninterference policy for that process are constructed such that the process is
secure with respect to the policy, but no domain-relation map satisfying the condition exists.

The contents of this paper are based on those of \cite{R1} and \cite{R2}. The salient points of
definitions and proofs are commented; for additional information, cf. Isabelle documentation,
particularly \cite{R5}, \cite{R6}, \cite{R7}, and \cite{R8}.

For the sake of brevity, given a function \<open>F\<close> of type
\<open>'a\<^sub>1 \<Rightarrow> \<dots> \<Rightarrow> 'a\<^sub>m \<Rightarrow> 'a\<^sub>m\<^sub>+\<^sub>1 \<Rightarrow> \<dots> \<Rightarrow> 'a\<^sub>n \<Rightarrow> 'b\<close>, the explanatory text may discuss of \<open>F\<close>
using attributes that would more exactly apply to a term of type \<open>'a\<^sub>m\<^sub>+\<^sub>1 \<Rightarrow> \<dots> \<Rightarrow> 'a\<^sub>n \<Rightarrow> 'b\<close>.
In this case, it shall be understood that strictly speaking, such attributes apply to a term
matching pattern \<open>F a\<^sub>1 \<dots> a\<^sub>m\<close>.
\<close>


subsection "Propaedeutic definitions and lemmas"

text \<open>
Here below are the translations of Rushby's predicates \emph{weakly step consistent} and
\emph{locally respects} \cite{R4}, applying to deterministic state machines, into Hoare's
Communicating Sequential Processes model of computation \cite{R3}.

The differences with respect to Rushby's original predicates are the following ones:

\begin{itemize}

\item
The relations in the range of the domain-relation map hold between event lists rather than machine
states.

\item
The domains appearing as inputs of the domain-relation map do not unnecessarily encompass all the
possible values of the data type of domains, but just the domains in the range of the event-domain
map.

\item
While every machine action is accepted in a machine state, not every process event is generally
accepted after a process trace. Thus, whenever an event is appended to an event list in the
consequent of an implication, the antecedent of the implication constrains the event list to be a
trace, and the event to be accepted after that trace. In this way, the predicates do not
unnecessarily impose that the relations in the range of the domain-relation map hold between event
lists not being process traces.

\end{itemize}

\null
\<close>

definition weakly_step_consistent ::
 "'a process \<Rightarrow> ('a \<Rightarrow> 'd) \<Rightarrow> ('a, 'd) dom_rel_map \<Rightarrow> bool" where
"weakly_step_consistent P D R \<equiv> \<forall>u \<in> range D. \<forall>xs ys x.
  (xs, ys) \<in> R u \<inter> R (D x) \<and> x \<in> next_events P xs \<inter> next_events P ys \<longrightarrow>
  (xs @ [x], ys @ [x]) \<in> R u"

definition locally_respects ::
 "'a process \<Rightarrow> ('d \<times> 'd) set \<Rightarrow> ('a \<Rightarrow> 'd) \<Rightarrow> ('a, 'd) dom_rel_map \<Rightarrow> bool" where
"locally_respects P I D R \<equiv> \<forall>u \<in> range D. \<forall>xs x.
  (D x, u) \<notin> I \<and> x \<in> next_events P xs \<longrightarrow> (xs, xs @ [x]) \<in> R u"

text \<open>
\null

In what follows, some lemmas propaedeutic for the proof of the Generic Unwinding Theorem are
demonstrated.

\null
\<close>

lemma ipurge_tr_aux_single_event:
 "ipurge_tr_aux I D U [x] = (if \<exists>v \<in> U. (v, D x) \<in> I
   then []
   else [x])"
proof (cases "\<exists>v \<in> U. (v, D x) \<in> I")
  case True
  have "ipurge_tr_aux I D U [x] = ipurge_tr_aux I D U ([] @ [x])" by simp
  also have "\<dots> = []" using True by (simp only: ipurge_tr_aux.simps, simp)
  finally show ?thesis using True by simp
next
  case False
  have "ipurge_tr_aux I D U [x] = ipurge_tr_aux I D U ([] @ [x])" by simp
  also have "\<dots> = [x]" using False by (simp only: ipurge_tr_aux.simps, simp)
  finally show ?thesis using False by simp
qed

lemma ipurge_tr_aux_cons:
 "ipurge_tr_aux I D U (x # xs) = (if \<exists>v \<in> U. (v, D x) \<in> I
   then ipurge_tr_aux I D (insert (D x) U) xs
   else x # ipurge_tr_aux I D U xs)"
proof (induction xs rule: rev_induct, case_tac [!] "\<exists>v \<in> U. (v, D x) \<in> I",
 simp_all add: ipurge_tr_aux_single_event del: ipurge_tr_aux.simps(2))
  fix x' xs
  assume A: "ipurge_tr_aux I D U (x # xs) =
    ipurge_tr_aux I D (insert (D x) U) xs"
    (is "?T = ?T'")
  assume "\<exists>v \<in> U. (v, D x) \<in> I"
  hence B: "sinks_aux I D U (x # xs) = sinks_aux I D (insert (D x) U) xs"
    (is "?S = ?S'")
   by (simp add: sinks_aux_cons)
  show "ipurge_tr_aux I D U (x # xs @ [x']) =
    ipurge_tr_aux I D (insert (D x) U) (xs @ [x'])"
  proof (cases "\<exists>v \<in> ?S. (v, D x') \<in> I")
    case True
    hence "ipurge_tr_aux I D U ((x # xs) @ [x']) = ?T"
     by (simp only: ipurge_tr_aux.simps, simp)
    moreover have "\<exists>v \<in> ?S'. (v, D x') \<in> I" using B and True by simp
    hence "ipurge_tr_aux I D (insert (D x) U) (xs @ [x']) = ?T'" by simp
    ultimately show ?thesis using A by simp
  next
    case False
    hence "ipurge_tr_aux I D U ((x # xs) @ [x']) = ?T @ [x']"
     by (simp only: ipurge_tr_aux.simps, simp)
    moreover have "\<not> (\<exists>v \<in> ?S'. (v, D x') \<in> I)" using B and False by simp
    hence "ipurge_tr_aux I D (insert (D x) U) (xs @ [x']) = ?T' @ [x']" by simp
    ultimately show ?thesis using A by simp
  qed
next
  fix x' xs
  assume A: "ipurge_tr_aux I D U (x # xs) = x # ipurge_tr_aux I D U xs"
    (is "?T = ?T'")
  assume "\<forall>v \<in> U. (v, D x) \<notin> I"
  hence B: "sinks_aux I D U (x # xs) = sinks_aux I D U xs"
    (is "?S = ?S'")
   by (simp add: sinks_aux_cons)
  show "ipurge_tr_aux I D U (x # xs @ [x']) =
    x # ipurge_tr_aux I D U (xs @ [x'])"
  proof (cases "\<exists>v \<in> ?S. (v, D x') \<in> I")
    case True
    hence "ipurge_tr_aux I D U ((x # xs) @ [x']) = ?T"
     by (simp only: ipurge_tr_aux.simps, simp)
    moreover have "\<exists>v \<in> ?S'. (v, D x') \<in> I" using B and True by simp
    hence "x # ipurge_tr_aux I D U (xs @ [x']) = ?T'" by simp
    ultimately show ?thesis using A by simp
  next
    case False
    hence "ipurge_tr_aux I D U ((x # xs) @ [x']) = ?T @ [x']"
     by (simp only: ipurge_tr_aux.simps, simp)
    moreover have "\<not> (\<exists>v \<in> ?S'. (v, D x') \<in> I)" using B and False by simp
    hence "x # ipurge_tr_aux I D U (xs @ [x']) = ?T' @ [x']" by simp
    ultimately show ?thesis using A by simp
  qed
qed

lemma unaffected_domains_subset:
  assumes
    A: "U \<subseteq> range D" and
    B: "U \<noteq> {}"
  shows "unaffected_domains I D U xs \<subseteq> range D \<inter> (-I) `` range D"
proof (subst unaffected_domains_def, rule subsetI, simp, erule conjE)
  fix v
  have "U \<subseteq> sinks_aux I D U xs" by (rule sinks_aux_subset)
  moreover have "\<exists>u. u \<in> U" using B by (simp add: ex_in_conv)
  then obtain u where C: "u \<in> U" ..
  ultimately have D: "u \<in> sinks_aux I D U xs" ..
  assume "\<forall>u \<in> sinks_aux I D U xs. (u, v) \<notin> I"
  hence "(u, v) \<notin> I" using D ..
  hence "(u, v) \<in> -I" by simp
  moreover have "u \<in> range D" using A and C ..
  ultimately show "v \<in> (-I) `` range D" ..
qed


subsection "The Generic Unwinding Theorem: proof of condition sufficiency"

text \<open>
Rushby's \emph{Unwinding Theorem for Intransitive Policies} \cite{R4} states that a sufficient
condition for a deterministic state machine with outputs to be secure is the existence of some
domain-relation map \emph{R} such that:

\begin{enumerate}

\item
\emph{R} is a \emph{view partition}, i.e. the relations over machine states in its range are
equivalence relations;

\item
\emph{R} is \emph{output consistent}, i.e. states equivalent with respect to the domain of an action
produce the same output as a result of that action;

\item
\emph{R} is weakly step consistent;

\item
\emph{R} locally respects the policy.

\end{enumerate}

The idea behind the theorem is that a machine is secure if its states can be partitioned, for each
domain \emph{u}, into equivalence classes (1), such that the states in any such class \emph{C} are
indistinguishable with respect to the actions in \emph{u} (2), transition into the same equivalence
class \emph{C'} as a result of an action (3), and transition remaining inside \emph{C} as a result
of an action not allowed to affect \emph{u} (4).

This idea can simply be translated into the realm of Communicating Sequential Processes \cite{R3} by
replacing the words "machine", "state", "action" with "process", "trace", "event", respectively, as
long as a clarification is provided of what it precisely means for a pair of traces to be
"indistinguishable" with respect to the events in a given domain. Intuitively, this happens just in
case the events in that domain being accepted or refused after either trace are the same, thus the
simplest choice would be to replace output consistency with \emph{future consistency} as defined in
\cite{R2}. However, indistinguishability between traces in the same equivalence class is not
required in the case of a domain allowed to be affected by any domain, since the policy puts no
restriction on the differences in process histories that may be detected by such a domain. Hence, it
is sufficient to replace output consistency with \emph{weak future consistency} \cite{R2}.

Furthermore, indistinguishability with respect to individual refused events does not imply
indistinguishability with respect to sets of refused events, i.e. refusals, unless for each trace,
the corresponding refusals set is closed under set union. Therefore, for the condition to be
sufficient for process security, the \emph{refusals union closure} of the process \cite{R2} is also
required. As remarked in \cite{R2}, this property holds for any process admitting a meaningful
interpretation, so that taking it as an additional assumption does not give rise to any actual
limitation on the applicability of the theorem.

As a result of these considerations, the Generic Unwinding Theorem, formalized in what follows as
theorem \<open>generic_unwinding\<close>, states that a sufficient condition for the CSP noninterference
security \cite{R1} of a process being refusals union closed \cite{R2} is the existence of some
domain-relation map \emph{R} such that:

\begin{enumerate}

\item
\emph{R} is a view partition \cite{R2};

\item
\emph{R} is weakly future consistent \cite{R2};

\item
\emph{R} is weakly step consistent;

\item
\emph{R} locally respects the policy.

\end{enumerate}

\null
\<close>

lemma ruc_wfc_failures:
  assumes
    RUC:  "ref_union_closed P" and
    WFC:  "weakly_future_consistent P I D R" and
    A:    "U \<subseteq> range D \<inter> (-I) `` range D" and
    B:    "U \<noteq> {}" and
    C:    "\<forall>u \<in> U. (xs, xs') \<in> R u" and
    D:    "(xs, X) \<in> failures P"
  shows "(xs', X \<inter> D -` U) \<in> failures P"
proof (cases "\<exists>x. x \<in> X \<inter> D -` U")
  let ?A = "singleton_set (X \<inter> D -` U)"
  have "\<forall>xs A. (\<exists>X. X \<in> A) \<longrightarrow> (\<forall>X \<in> A. (xs, X) \<in> failures P) \<longrightarrow>
    (xs, \<Union>X \<in> A. X) \<in> failures P"
   using RUC by (simp add: ref_union_closed_def)
  hence "(\<exists>X. X \<in> ?A) \<longrightarrow> (\<forall>X \<in> ?A. (xs', X) \<in> failures P) \<longrightarrow>
    (xs', \<Union>X \<in> ?A. X) \<in> failures P"
   by blast
  moreover case True
  hence "\<exists>X. X \<in> ?A" by (simp add: singleton_set_some)
  ultimately have "(\<forall>X \<in> ?A. (xs', X) \<in> failures P) \<longrightarrow>
    (xs', \<Union>X \<in> ?A. X) \<in> failures P" ..
  moreover have "\<forall>X \<in> ?A. (xs', X) \<in> failures P"
  proof (simp add: singleton_set_def, rule allI, rule impI, erule bexE, erule IntE,
   simp)
    fix x
    have "\<forall>u \<in> range D \<inter> (-I) `` range D. \<forall>xs ys. (xs, ys) \<in> R u \<longrightarrow>
      next_dom_events P D u xs = next_dom_events P D u ys \<and>
      ref_dom_events P D u xs = ref_dom_events P D u ys"
     using WFC by (simp add: weakly_future_consistent_def)
    moreover assume E: "D x \<in> U"
    with A have "D x \<in> range D \<inter> (- I) `` range D" ..
    ultimately have "\<forall>xs ys. (xs, ys) \<in> R (D x) \<longrightarrow>
      next_dom_events P D (D x) xs = next_dom_events P D (D x) ys \<and>
      ref_dom_events P D (D x) xs = ref_dom_events P D (D x) ys" ..
    hence "(xs, xs') \<in> R (D x) \<longrightarrow>
      next_dom_events P D (D x) xs = next_dom_events P D (D x) xs' \<and>
      ref_dom_events P D (D x) xs = ref_dom_events P D (D x) xs'"
     by blast
    moreover have "(xs, xs') \<in> R (D x)" using C and E ..
    ultimately have "ref_dom_events P D (D x) xs =
      ref_dom_events P D (D x) xs'"
     by simp
    moreover assume "x \<in> X"
    hence "{x} \<subseteq> X" by simp
    with D have "(xs, {x}) \<in> failures P" by (rule process_rule_3)
    hence "x \<in> ref_dom_events P D (D x) xs"
     by (simp add: ref_dom_events_def refusals_def)
    ultimately have "x \<in> ref_dom_events P D (D x) xs'" by simp
    thus "(xs', {x}) \<in> failures P" by (simp add: ref_dom_events_def refusals_def)
  qed
  ultimately have "(xs', \<Union>X \<in> ?A. X) \<in> failures P" ..
  thus "(xs', X \<inter> D -` U) \<in> failures P" by (simp only: singleton_set_union)
next
  have "\<exists>u. u \<in> U" using B by (simp add: ex_in_conv)
  then obtain u where E: "u \<in> U" ..
  with A have "u \<in> range D \<inter> (- I) `` range D" ..
  moreover have "(xs, xs') \<in> R u" using C and E ..
  ultimately have "(xs \<in> traces P) = (xs' \<in> traces P)"
   by (rule wfc_traces [OF WFC])
  moreover have "xs \<in> traces P" using D by (rule failures_traces)
  ultimately have "xs' \<in> traces P" by simp
  hence "(xs', {}) \<in> failures P" by (rule traces_failures)
  moreover case False
  hence "X \<inter> D -` U = {}" by (simp only: ex_in_conv, simp)
  ultimately show "(xs', X \<inter> D -` U) \<in> failures P" by simp
qed

lemma ruc_wfc_lr_failures_1:
  assumes
    RUC:  "ref_union_closed P" and
    WFC:  "weakly_future_consistent P I D R" and
    LR:   "locally_respects P I D R" and
    A:    "(xs @ [y], Y) \<in> failures P"
  shows "(xs, {x \<in> Y. (D y, D x) \<notin> I}) \<in> failures P"
proof (cases "\<exists>x. x \<in> {x \<in> Y. (D y, D x) \<notin> I}")
  let ?A = "singleton_set {x \<in> Y. (D y, D x) \<notin> I}"
  have "\<forall>xs A. (\<exists>X. X \<in> A) \<longrightarrow> (\<forall>X \<in> A. (xs, X) \<in> failures P) \<longrightarrow>
    (xs, \<Union>X \<in> A. X) \<in> failures P"
   using RUC by (simp add: ref_union_closed_def)
  hence "(\<exists>X. X \<in> ?A) \<longrightarrow> (\<forall>X \<in> ?A. (xs, X) \<in> failures P) \<longrightarrow>
    (xs, \<Union>X \<in> ?A. X) \<in> failures P"
   by blast
  moreover case True
  hence "\<exists>X. X \<in> ?A" by (simp add: singleton_set_some)
  ultimately have "(\<forall>X \<in> ?A. (xs, X) \<in> failures P) \<longrightarrow>
    (xs, \<Union>X \<in> ?A. X) \<in> failures P" ..
  moreover have "\<forall>X \<in> ?A. (xs, X) \<in> failures P"
  proof (rule ballI, simp add: singleton_set_def, erule exE, (erule conjE)+, simp)
    fix x
    have "\<forall>u \<in> range D \<inter> (-I) `` range D. \<forall>xs ys. (xs, ys) \<in> R u \<longrightarrow>
      next_dom_events P D u xs = next_dom_events P D u ys \<and>
      ref_dom_events P D u xs = ref_dom_events P D u ys"
     using WFC by (simp add: weakly_future_consistent_def)
    moreover assume B: "(D y, D x) \<notin> I"
    hence "D x \<in> range D \<inter> (-I) `` range D" by (simp add: Image_iff, rule exI)
    ultimately have "\<forall>xs ys. (xs, ys) \<in> R (D x) \<longrightarrow>
      next_dom_events P D (D x) xs = next_dom_events P D (D x) ys \<and>
      ref_dom_events P D (D x) xs = ref_dom_events P D (D x) ys" ..
    hence C: "(xs, xs @ [y]) \<in> R (D x) \<longrightarrow>
      ref_dom_events P D (D x) xs = ref_dom_events P D (D x) (xs @ [y])"
     by simp
    have "\<forall>xs y. (D y, D x) \<notin> I \<and> y \<in> next_events P xs \<longrightarrow>
      (xs, xs @ [y]) \<in> R (D x)"
     using LR by (simp add: locally_respects_def)
    hence "(D y, D x) \<notin> I \<and> y \<in> next_events P xs \<longrightarrow> (xs, xs @ [y]) \<in> R (D x)"
     by blast
    moreover have "xs @ [y] \<in> traces P" using A by (rule failures_traces)
    hence "y \<in> next_events P xs" by (simp add: next_events_def)
    ultimately have "(xs, xs @ [y]) \<in> R (D x)" using B by simp
    with C have "ref_dom_events P D (D x) xs =
      ref_dom_events P D (D x) (xs @ [y])" ..
    moreover assume D: "x \<in> Y"
    have "x \<in> ref_dom_events P D (D x) (xs @ [y])"
    proof (simp add: ref_dom_events_def refusals_def)
      have "{x} \<subseteq> Y" using D by (simp add: ipurge_ref_def)
      with A show "(xs @ [y], {x}) \<in> failures P" by (rule process_rule_3)
    qed
    ultimately have "x \<in> ref_dom_events P D (D x) xs" by simp
    thus "(xs, {x}) \<in> failures P" by (simp add: ref_dom_events_def refusals_def)
  qed
  ultimately have "(xs, \<Union>X \<in> ?A. X) \<in> failures P" ..
  thus ?thesis by (simp only: singleton_set_union)
next
  case False
  hence "{x \<in> Y. (D y, D x) \<notin> I} = {}" by simp
  moreover have "(xs, {}) \<in> failures P" using A by (rule process_rule_2)
  ultimately show ?thesis by (simp (no_asm_simp))
qed

lemma ruc_wfc_lr_failures_2:
  assumes
    RUC:  "ref_union_closed P" and
    WFC:  "weakly_future_consistent P I D R" and
    LR:   "locally_respects P I D R" and
    A:    "(xs, Z) \<in> failures P" and
    Y:    "xs @ [y] \<in> traces P"
  shows "(xs @ [y], {x \<in> Z. (D y, D x) \<notin> I}) \<in> failures P"
proof (cases "\<exists>x. x \<in> {x \<in> Z. (D y, D x) \<notin> I}")
  let ?A = "singleton_set {x \<in> Z. (D y, D x) \<notin> I}"
  have "\<forall>xs A. (\<exists>X. X \<in> A) \<longrightarrow> (\<forall>X \<in> A. (xs, X) \<in> failures P) \<longrightarrow>
    (xs, \<Union>X \<in> A. X) \<in> failures P"
   using RUC by (simp add: ref_union_closed_def)
  hence "(\<exists>X. X \<in> ?A) \<longrightarrow> (\<forall>X \<in> ?A. (xs @ [y], X) \<in> failures P) \<longrightarrow>
    (xs @ [y], \<Union>X \<in> ?A. X) \<in> failures P"
   by blast
  moreover case True
  hence "\<exists>X. X \<in> ?A" by (simp add: singleton_set_some)
  ultimately have "(\<forall>X \<in> ?A. (xs @ [y], X) \<in> failures P) \<longrightarrow>
    (xs @ [y], \<Union>X \<in> ?A. X) \<in> failures P" ..
  moreover have "\<forall>X \<in> ?A. (xs @ [y], X) \<in> failures P"
  proof (rule ballI, simp add: singleton_set_def, erule exE, (erule conjE)+, simp)
    fix x
    have "\<forall>u \<in> range D \<inter> (-I) `` range D. \<forall>xs ys. (xs, ys) \<in> R u \<longrightarrow>
      next_dom_events P D u xs = next_dom_events P D u ys \<and>
      ref_dom_events P D u xs = ref_dom_events P D u ys"
     using WFC by (simp add: weakly_future_consistent_def)
    moreover assume B: "(D y, D x) \<notin> I"
    hence "D x \<in> range D \<inter> (-I) `` range D" by (simp add: Image_iff, rule exI)
    ultimately have "\<forall>xs ys. (xs, ys) \<in> R (D x) \<longrightarrow>
      next_dom_events P D (D x) xs = next_dom_events P D (D x) ys \<and>
      ref_dom_events P D (D x) xs = ref_dom_events P D (D x) ys" ..
    hence C: "(xs, xs @ [y]) \<in> R (D x) \<longrightarrow>
      ref_dom_events P D (D x) xs = ref_dom_events P D (D x) (xs @ [y])"
     by simp
    have "\<forall>xs y. (D y, D x) \<notin> I \<and> y \<in> next_events P xs \<longrightarrow>
      (xs, xs @ [y]) \<in> R (D x)"
     using LR by (simp add: locally_respects_def)
    hence "(D y, D x) \<notin> I \<and> y \<in> next_events P xs \<longrightarrow> (xs, xs @ [y]) \<in> R (D x)"
     by blast
    moreover have "y \<in> next_events P xs" using Y by (simp add: next_events_def)
    ultimately have "(xs, xs @ [y]) \<in> R (D x)" using B by simp
    with C have "ref_dom_events P D (D x) xs =
      ref_dom_events P D (D x) (xs @ [y])" ..
    moreover assume D: "x \<in> Z"
    have "x \<in> ref_dom_events P D (D x) xs"
    proof (simp add: ref_dom_events_def refusals_def)
      have "{x} \<subseteq> Z" using D by (simp add: ipurge_ref_def)
      with A show "(xs, {x}) \<in> failures P" by (rule process_rule_3)
    qed
    ultimately have "x \<in> ref_dom_events P D (D x) (xs @ [y])" by simp
    thus "(xs @ [y], {x}) \<in> failures P"
     by (simp add: ref_dom_events_def refusals_def)
  qed
  ultimately have "(xs @ [y], \<Union>X \<in> ?A. X) \<in> failures P" ..
  thus ?thesis by (simp only: singleton_set_union)
next
  case False
  hence "{x \<in> Z. (D y, D x) \<notin> I} = {}" by simp
  moreover have "(xs @ [y], {}) \<in> failures P" using Y by (rule traces_failures)
  ultimately show ?thesis by (simp (no_asm_simp))
qed

lemma gu_condition_imply_secure_aux [rule_format]:
  assumes
    VP:   "view_partition P D R" and
    WFC:  "weakly_future_consistent P I D R" and
    WSC:  "weakly_step_consistent P D R" and
    LR:   "locally_respects P I D R"
  shows "U \<subseteq> range D \<longrightarrow> U \<noteq> {} \<longrightarrow> xs @ ys \<in> traces P \<longrightarrow>
    (\<forall>u \<in> unaffected_domains I D U []. (xs, xs') \<in> R u) \<longrightarrow>
    (\<forall>u \<in> unaffected_domains I D U ys.
      (xs @ ys, xs' @ ipurge_tr_aux I D U ys) \<in> R u)"
proof (induction ys arbitrary: xs xs' U, simp_all add: unaffected_domains_def,
 ((rule impI)+, (rule allI)?)+, erule conjE)
  fix y ys xs xs' U u
  assume
    A: "\<And>xs xs' U. U \<subseteq> range D \<longrightarrow> U \<noteq> {} \<longrightarrow> xs @ ys \<in> traces P \<longrightarrow>
      (\<forall>u. u \<in> range D \<and> (\<forall>v \<in> U. (v, u) \<notin> I) \<longrightarrow>
        (xs, xs') \<in> R u) \<longrightarrow>
      (\<forall>u. u \<in> range D \<and> (\<forall>v \<in> sinks_aux I D U ys. (v, u) \<notin> I) \<longrightarrow>
        (xs @ ys, xs' @ ipurge_tr_aux I D U ys) \<in> R u)" and
    B: "U \<subseteq> range D" and
    C: "U \<noteq> {}" and
    D: "xs @ y # ys \<in> traces P" and
    E: "\<forall>u. u \<in> range D \<and> (\<forall>v \<in> U. (v, u) \<notin> I) \<longrightarrow> (xs, xs') \<in> R u" and
    F: "u \<in> range D" and
    G: "\<forall>v \<in> sinks_aux I D U (y # ys). (v, u) \<notin> I"
  show "(xs @ y # ys, xs' @ ipurge_tr_aux I D U (y # ys)) \<in> R u"
  proof (cases "\<exists>v \<in> U. (v, D y) \<in> I",
   simp_all (no_asm_simp) add: ipurge_tr_aux_cons)
    case True
    let ?U' = "insert (D y) U"
    have "?U' \<subseteq> range D \<longrightarrow> ?U' \<noteq> {} \<longrightarrow> (xs @ [y]) @ ys \<in> traces P \<longrightarrow>
      (\<forall>u. u \<in> range D \<and> (\<forall>v \<in> ?U'. (v, u) \<notin> I) \<longrightarrow>
        (xs @ [y], xs') \<in> R u) \<longrightarrow>
      (\<forall>u. u \<in> range D \<and> (\<forall>v \<in> sinks_aux I D ?U' ys. (v, u) \<notin> I) \<longrightarrow>
        ((xs @ [y]) @ ys, xs' @ ipurge_tr_aux I D ?U' ys) \<in> R u)"
     using A .
    hence
     "(\<forall>u. u \<in> range D \<and> (\<forall>v \<in> ?U'. (v, u) \<notin> I) \<longrightarrow>
        (xs @ [y], xs') \<in> R u) \<longrightarrow>
      (\<forall>u. u \<in> range D \<and> (\<forall>v \<in> sinks_aux I D ?U' ys. (v, u) \<notin> I) \<longrightarrow>
        (xs @ y # ys, xs' @ ipurge_tr_aux I D ?U' ys) \<in> R u)"
     using B and D by simp
    moreover have
     "\<forall>u. u \<in> range D \<and> (\<forall>v \<in> ?U'. (v, u) \<notin> I) \<longrightarrow>
        (xs @ [y], xs') \<in> R u"
    proof (rule allI, rule impI, erule conjE)
      fix u
      assume F: "u \<in> range D" and G: "\<forall>v \<in> ?U'. (v, u) \<notin> I"
      moreover have "u \<in> range D \<and> (\<forall>v \<in> U. (v, u) \<notin> I) \<longrightarrow> (xs, xs') \<in> R u"
       using E ..
      ultimately have H: "(xs, xs') \<in> R u" by simp
      have "\<forall>u \<in> range D. (D y, u) \<notin> I \<and> y \<in> next_events P xs \<longrightarrow>
        (xs, xs @ [y]) \<in> R u"
       using LR by (simp add: locally_respects_def)
      hence "(D y, u) \<notin> I \<and> y \<in> next_events P xs \<longrightarrow> (xs, xs @ [y]) \<in> R u"
       using F ..
      moreover have "D y \<in> ?U'" by simp
      with G have "(D y, u) \<notin> I" ..
      moreover have "(xs @ [y]) @ ys \<in> traces P" using D by simp
      hence "y \<in> next_events P xs"
       by (simp (no_asm_simp) add: next_events_def, rule process_rule_2_traces)
      ultimately have I: "(xs, xs @ [y]) \<in> R u" by simp
      have "\<forall>u \<in> range D. equiv (traces P) (R u)"
       using VP by (simp add: view_partition_def)
      hence J: "equiv (traces P) (R u)" using F ..
      hence "trans (R u)" by (simp add: equiv_def)
      moreover have "sym (R u)" using J by (simp add: equiv_def)
      hence "(xs @ [y], xs) \<in> R u" using I by (rule symE)
      ultimately show "(xs @ [y], xs') \<in> R u" using H by (rule transE)
    qed
    ultimately have
     "\<forall>u. u \<in> range D \<and> (\<forall>v \<in> sinks_aux I D ?U' ys. (v, u) \<notin> I) \<longrightarrow>
        (xs @ y # ys, xs' @ ipurge_tr_aux I D ?U' ys) \<in> R u" ..
    hence
     "u \<in> range D \<and> (\<forall>v \<in> sinks_aux I D ?U' ys. (v, u) \<notin> I) \<longrightarrow>
        (xs @ y # ys, xs' @ ipurge_tr_aux I D ?U' ys) \<in> R u" ..
    moreover have "sinks_aux I D U (y # ys) = sinks_aux I D ?U' ys"
     using Cons and True by (simp add: sinks_aux_cons)
    hence "\<forall>v \<in> sinks_aux I D ?U' ys. (v, u) \<notin> I" using G by simp
    with F have "u \<in> range D \<and> (\<forall>v \<in> sinks_aux I D ?U' ys. (v, u) \<notin> I)" ..
    ultimately show "(xs @ y # ys, xs' @ ipurge_tr_aux I D ?U' ys) \<in> R u" ..
  next
    case False
    have
     "U \<subseteq> range D \<longrightarrow> U \<noteq> {} \<longrightarrow> (xs @ [y]) @ ys \<in> traces P \<longrightarrow>
      (\<forall>u. u \<in> range D \<and> (\<forall>v \<in> U. (v, u) \<notin> I) \<longrightarrow>
        (xs @ [y], xs' @ [y]) \<in> R u) \<longrightarrow>
      (\<forall>u. u \<in> range D \<and> (\<forall>v \<in> sinks_aux I D U ys. (v, u) \<notin> I) \<longrightarrow>
        ((xs @ [y]) @ ys, (xs' @ [y]) @ ipurge_tr_aux I D U ys) \<in> R u)"
     using A .
    hence
     "(\<forall>u. u \<in> range D \<and> (\<forall>v \<in> U. (v, u) \<notin> I) \<longrightarrow>
        (xs @ [y], xs' @ [y]) \<in> R u) \<longrightarrow>
      (\<forall>u. u \<in> range D \<and> (\<forall>v \<in> sinks_aux I D U ys. (v, u) \<notin> I) \<longrightarrow>
        (xs @ y # ys, xs' @ y # ipurge_tr_aux I D U ys) \<in> R u)"
     using B and C and D by simp
    moreover have
     "\<forall>u. u \<in> range D \<and> (\<forall>v \<in> U. (v, u) \<notin> I) \<longrightarrow>
        (xs @ [y], xs' @ [y]) \<in> R u"
    proof (rule allI, rule impI, erule conjE)
      fix u
      assume F: "u \<in> range D" and G: "\<forall>v \<in> U. (v, u) \<notin> I"
      moreover have "u \<in> range D \<and> (\<forall>v \<in> U. (v, u) \<notin> I) \<longrightarrow> (xs, xs') \<in> R u"
       using E ..
      ultimately have "(xs, xs') \<in> R u" by simp
      moreover have "D y \<in> range D \<and>
        (\<forall>v \<in> U. (v, D y) \<notin> I) \<longrightarrow> (xs, xs') \<in> R (D y)"
       using E ..
      hence "(xs, xs') \<in> R (D y)" using False by simp
      ultimately have H: "(xs, xs') \<in> R u \<inter> R (D y)" ..
      have "\<exists>v. v \<in> U" using C by (simp add: ex_in_conv)
      then obtain v where I: "v \<in> U" ..
      hence "(v, D y) \<in> -I" using False by simp
      moreover have "v \<in> range D" using B and I ..
      ultimately have "D y \<in> (-I) `` range D" ..
      hence J: "D y \<in> range D \<inter> (-I) `` range D" by simp
      have "\<forall>u \<in> range D \<inter> (-I) `` range D. \<forall>xs ys. (xs, ys) \<in> R u \<longrightarrow>
        next_dom_events P D u xs = next_dom_events P D u ys \<and>
        ref_dom_events P D u xs = ref_dom_events P D u ys"
       using WFC by (simp add: weakly_future_consistent_def)
      hence "\<forall>xs ys. (xs, ys) \<in> R (D y) \<longrightarrow>
        next_dom_events P D (D y) xs = next_dom_events P D (D y) ys \<and>
        ref_dom_events P D (D y) xs = ref_dom_events P D (D y) ys"
       using J ..
      hence "(xs, xs') \<in> R (D y) \<longrightarrow>
        next_dom_events P D (D y) xs = next_dom_events P D (D y) xs' \<and>
        ref_dom_events P D (D y) xs = ref_dom_events P D (D y) xs'"
       by blast
      hence "next_dom_events P D (D y) xs = next_dom_events P D (D y) xs'"
       using H by simp
      moreover have "(xs @ [y]) @ ys \<in> traces P" using D by simp
      hence K: "y \<in> next_events P xs"
       by (simp (no_asm_simp) add: next_events_def, rule process_rule_2_traces)
      hence "y \<in> next_dom_events P D (D y) xs"
       by (simp add: next_dom_events_def)
      ultimately have "y \<in> next_events P xs'" by (simp add: next_dom_events_def)
      with K have L: "y \<in> next_events P xs \<inter> next_events P xs'" ..
      have "\<forall>u \<in> range D. \<forall>xs ys x.
        (xs, ys) \<in> R u \<inter> R (D x) \<and> x \<in> next_events P xs \<inter> next_events P ys \<longrightarrow>
        (xs @ [x], ys @ [x]) \<in> R u"
       using WSC by (simp add: weakly_step_consistent_def)
      hence "\<forall>xs ys x.
        (xs, ys) \<in> R u \<inter> R (D x) \<and> x \<in> next_events P xs \<inter> next_events P ys \<longrightarrow>
        (xs @ [x], ys @ [x]) \<in> R u"
       using F ..
      hence
       "(xs, xs') \<in> R u \<inter> R (D y) \<and> y \<in> next_events P xs \<inter> next_events P xs' \<longrightarrow>
        (xs @ [y], xs' @ [y]) \<in> R u"
       by blast
      thus "(xs @ [y], xs' @ [y]) \<in> R u" using H and L by simp
    qed
    ultimately have
     "\<forall>u. u \<in> range D \<and> (\<forall>v \<in> sinks_aux I D U ys. (v, u) \<notin> I) \<longrightarrow>
      (xs @ y # ys, xs' @ y # ipurge_tr_aux I D U ys) \<in> R u" ..
    hence "u \<in> range D \<and> (\<forall>v \<in> sinks_aux I D U ys. (v, u) \<notin> I) \<longrightarrow>
      (xs @ y # ys, xs' @ y # ipurge_tr_aux I D U ys) \<in> R u" ..
    moreover have "sinks_aux I D U (y # ys) = sinks_aux I D U ys"
     using Cons and False by (simp add: sinks_aux_cons)
    hence "\<forall>v \<in> sinks_aux I D U ys. (v, u) \<notin> I" using G by simp
    with F have "u \<in> range D \<and> (\<forall>v \<in> sinks_aux I D U ys. (v, u) \<notin> I)" ..
    ultimately show "(xs @ y # ys, xs' @ y # ipurge_tr_aux I D U ys) \<in> R u" ..
  qed
qed

lemma gu_condition_imply_secure_1 [rule_format]:
  assumes
    RUC:  "ref_union_closed P" and
    VP:   "view_partition P D R" and
    WFC:  "weakly_future_consistent P I D R" and
    WSC:  "weakly_step_consistent P D R" and
    LR:   "locally_respects P I D R"
  shows "(xs @ y # ys, Y) \<in> failures P \<longrightarrow>
    (xs @ ipurge_tr I D (D y) ys, ipurge_ref I D (D y) ys Y) \<in> failures P"
proof (induction ys arbitrary: Y rule: rev_induct, rule_tac [!] impI,
 simp add: ipurge_ref_def)
  fix Y
  assume "(xs @ [y], Y) \<in> failures P"
  with RUC and WFC and LR show
   "(xs, {x \<in> Y. (D y, D x) \<notin> I}) \<in> failures P"
   by (rule ruc_wfc_lr_failures_1)
next
  fix y' ys Y
  assume
    A: "\<And>Y'. (xs @ y # ys, Y') \<in> failures P \<longrightarrow>
      (xs @ ipurge_tr I D (D y) ys, ipurge_ref I D (D y) ys Y') \<in> failures P" and
    B: "(xs @ y # ys @ [y'], Y) \<in> failures P"
  show "(xs @ ipurge_tr I D (D y) (ys @ [y']), ipurge_ref I D (D y) (ys @ [y']) Y)
    \<in> failures P"
  proof (cases "D y' \<in> sinks I D (D y) (ys @ [y'])", simp del: sinks.simps)
    let ?Y' = "{x \<in> Y. (D y', D x) \<notin> I}"
    have "(xs @ y # ys, ?Y') \<in> failures P \<longrightarrow>
      (xs @ ipurge_tr I D (D y) ys, ipurge_ref I D (D y) ys ?Y') \<in> failures P"
     using A .
    moreover have "((xs @ y # ys) @ [y'], Y) \<in> failures P" using B by simp
    with RUC and WFC and LR have "(xs @ y # ys, ?Y') \<in> failures P"
     by (rule ruc_wfc_lr_failures_1)
    ultimately have
     "(xs @ ipurge_tr I D (D y) ys, ipurge_ref I D (D y) ys ?Y') \<in> failures P" ..
    moreover case True
    hence "ipurge_ref I D (D y) (ys @ [y']) Y = ipurge_ref I D (D y) ys ?Y'"
     by (rule ipurge_ref_eq)
    ultimately show
     "(xs @ ipurge_tr I D (D y) ys, ipurge_ref I D (D y) (ys @ [y']) Y) \<in> failures P"
     by simp
 next
   case False
   have "unaffected_domains I D {D y} (ys @ [y']) \<subseteq> range D \<inter> (-I) `` range D"
     (is "?U \<subseteq> _")
     by (rule unaffected_domains_subset, simp_all)
   moreover have "?U \<noteq> {}"
   proof -
     have "(D y, D y') \<notin> I" using False by (rule_tac notI, simp)
     moreover
     have "\<not> ((D y, D y') \<in> I \<or> (\<exists>v \<in> sinks I D (D y) ys. (v, D y') \<in> I))"
       using False by (simp only: sinks_interference_eq, simp)
     then have "\<forall>v \<in> sinks I D (D y) (ys @ [y']). (v, D y') \<notin> I" by simp
     ultimately show "?U \<noteq> {}"
       apply (simp (no_asm_simp) add: unaffected_domains_def sinks_aux_single_dom set_eq_iff)
       using \<open>(D y, D y') \<notin> I\<close> by auto
   qed
   moreover have C: "xs @ y # ys @ [y'] \<in> traces P"
     using B by (rule failures_traces)
   have "\<forall>u \<in> ?U. ((xs @ [y]) @ ys @ [y'],
      xs @ ipurge_tr_aux I D {D y} (ys @ [y'])) \<in> R u"
   proof (rule ballI, rule gu_condition_imply_secure_aux [OF VP WFC WSC LR],
       simp_all add: unaffected_domains_def C, (erule conjE)+)
     fix u
     have "\<forall>u \<in> range D. \<forall>xs x.
        (D x, u) \<notin> I \<and> x \<in> next_events P xs \<longrightarrow> (xs, xs @ [x]) \<in> R u"
       using LR by (simp add: locally_respects_def)
     moreover assume D: "u \<in> range D"
     ultimately have "\<forall>xs x.
        (D x, u) \<notin> I \<and> x \<in> next_events P xs \<longrightarrow> (xs, xs @ [x]) \<in> R u" ..
     hence "(D y, u) \<notin> I \<and> y \<in> next_events P xs \<longrightarrow>
        (xs, xs @ [y]) \<in> R u"
       by blast
     moreover assume "(D y, u) \<notin> I"
     moreover have "(xs @ [y]) @ ys @ [y'] \<in> traces P" using C by simp
     hence "xs @ [y] \<in> traces P" by (rule process_rule_2_traces)
     hence "y \<in> next_events P xs" by (simp add: next_events_def)
     ultimately have E: "(xs, xs @ [y]) \<in> R u" by simp
     have "\<forall>u \<in> range D. equiv (traces P) (R u)"
       using VP by (simp add: view_partition_def)
     hence "equiv (traces P) (R u)" using D ..
     hence "sym (R u)" by (simp add: equiv_def)
     thus "(xs @ [y], xs) \<in> R u" using E by (rule symE)
   qed
    hence "\<forall>u \<in> ?U. (xs @ y # ys @ [y'],
      xs @ ipurge_tr I D (D y) (ys @ [y'])) \<in> R u"
     by (simp only: ipurge_tr_aux_single_dom, simp)
    ultimately have "(xs @ ipurge_tr I D (D y) (ys @ [y']), Y \<inter> D -` ?U)
      \<in> failures P"
     using B by (rule ruc_wfc_failures [OF RUC WFC])
    moreover have
     "Y \<inter> D -` ?U = {x \<in> Y. D x \<in> unaffected_domains I D {D y} (ys @ [y'])}"
     by (simp add: set_eq_iff)
    ultimately show ?thesis by (simp only: unaffected_domains_single_dom)
  qed
qed

lemma gu_condition_imply_secure_2 [rule_format]:
  assumes
    RUC:  "ref_union_closed P" and
    VP:   "view_partition P D R" and
    WFC:  "weakly_future_consistent P I D R" and
    WSC:  "weakly_step_consistent P D R" and
    LR:   "locally_respects P I D R" and
    Y:    "xs @ [y] \<in> traces P"
  shows "(xs @ zs, Z) \<in> failures P \<longrightarrow>
    (xs @ y # ipurge_tr I D (D y) zs, ipurge_ref I D (D y) zs Z) \<in> failures P"
proof (induction zs arbitrary: Z rule: rev_induct, rule_tac [!] impI,
 simp add: ipurge_ref_def)
  fix Z
  assume "(xs, Z) \<in> failures P"
  with RUC and WFC and LR show
   "(xs @ [y], {x \<in> Z. (D y, D x) \<notin> I}) \<in> failures P"
   using Y by (rule ruc_wfc_lr_failures_2)
next
  fix z zs Z
  assume
    A: "\<And>Z'. (xs @ zs, Z') \<in> failures P \<longrightarrow>
      (xs @ y # ipurge_tr I D (D y) zs,
      ipurge_ref I D (D y) zs Z') \<in> failures P" and
    B: "(xs @ zs @ [z], Z) \<in> failures P"
  show "(xs @ y # ipurge_tr I D (D y) (zs @ [z]),
    ipurge_ref I D (D y) (zs @ [z]) Z) \<in> failures P"
  proof (cases "D z \<in> sinks I D (D y) (zs @ [z])", simp del: sinks.simps)
    let ?Z' = "{x \<in> Z. (D z, D x) \<notin> I}"
    have "(xs @ zs, ?Z') \<in> failures P \<longrightarrow>
      (xs @ y # ipurge_tr I D (D y) zs, ipurge_ref I D (D y) zs ?Z') \<in> failures P"
     using A .
    moreover have "((xs @ zs) @ [z], Z) \<in> failures P" using B by simp
    with RUC and WFC and LR have "(xs @ zs, ?Z') \<in> failures P"
     by (rule ruc_wfc_lr_failures_1)
    ultimately have
     "(xs @ y # ipurge_tr I D (D y) zs, ipurge_ref I D (D y) zs ?Z') \<in> failures P" ..
    moreover case True
    hence "ipurge_ref I D (D y) (zs @ [z]) Z = ipurge_ref I D (D y) zs ?Z'"
     by (rule ipurge_ref_eq)
    ultimately show
     "(xs @ y # ipurge_tr I D (D y) zs, ipurge_ref I D (D y) (zs @ [z]) Z)
        \<in> failures P"
     by simp
 next
   case False
   have "unaffected_domains I D {D y} (zs @ [z]) \<subseteq> range D \<inter> (-I) `` range D"
     (is "?U \<subseteq> _")
     by (rule unaffected_domains_subset, simp_all)
   moreover have "?U \<noteq> {}"
   proof -
     have "(D y, D z) \<notin> I" using False by (rule_tac notI, simp)
     moreover
     have "\<not> ((D y, D z) \<in> I \<or> (\<exists>v \<in> sinks I D (D y) zs. (v, D z) \<in> I))"
       using False by (simp only: sinks_interference_eq, simp)
     then have "\<forall>v \<in> sinks I D (D y) (zs @ [z]). (v, D z) \<notin> I" by simp
     ultimately show "?U \<noteq> {}"
       apply (simp (no_asm_simp) add: unaffected_domains_def sinks_aux_single_dom set_eq_iff)
       using \<open>(D y, D z) \<notin> I\<close> by auto
   qed
   moreover have C: "xs @ zs @ [z] \<in> traces P" using B by (rule failures_traces)
   have "\<forall>u \<in> ?U. (xs @ zs @ [z],
      (xs @ [y]) @ ipurge_tr_aux I D {D y} (zs @ [z])) \<in> R u"
   proof (rule ballI, rule gu_condition_imply_secure_aux [OF VP WFC WSC LR],
       simp_all add: unaffected_domains_def C, (erule conjE)+)
     fix u
     have "\<forall>u \<in> range D. \<forall>xs x.
        (D x, u) \<notin> I \<and> x \<in> next_events P xs \<longrightarrow> (xs, xs @ [x]) \<in> R u"
       using LR by (simp add: locally_respects_def)
     moreover assume D: "u \<in> range D"
     ultimately have "\<forall>xs x.
        (D x, u) \<notin> I \<and> x \<in> next_events P xs \<longrightarrow> (xs, xs @ [x]) \<in> R u" ..
     hence "(D y, u) \<notin> I \<and> y \<in> next_events P xs \<longrightarrow> (xs, xs @ [y]) \<in> R u" by blast
     moreover assume "(D y, u) \<notin> I"
     moreover have "y \<in> next_events P xs" using Y by (simp add: next_events_def)
     ultimately show "(xs, xs @ [y]) \<in> R u" by simp
   qed
   hence "\<forall>u \<in> ?U. (xs @ zs @ [z],
      xs @ y # ipurge_tr I D (D y) (zs @ [z])) \<in> R u"
     by (simp only: ipurge_tr_aux_single_dom, simp)
   ultimately have "(xs @ y # ipurge_tr I D (D y) (zs @ [z]), Z \<inter> D -` ?U)
      \<in> failures P"
     using B by (rule ruc_wfc_failures [OF RUC WFC])
   moreover have
     "Z \<inter> D -` ?U = {x \<in> Z. D x \<in> unaffected_domains I D {D y} (zs @ [z])}"
     by (simp add: set_eq_iff)
   ultimately show ?thesis by (simp only: unaffected_domains_single_dom)
 qed
qed

theorem generic_unwinding:
  assumes
    RUC:  "ref_union_closed P" and
    VP:   "view_partition P D R" and
    WFC:  "weakly_future_consistent P I D R" and
    WSC:  "weakly_step_consistent P D R" and
    LR:   "locally_respects P I D R"
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
    show ?P using RUC and VP and WFC and WSC and LR and A
     by (rule gu_condition_imply_secure_1)
  next
    have "((xs @ [y]) @ ys, Y) \<in> failures P" using A by simp
    hence "(xs @ [y], {}) \<in> failures P" by (rule process_rule_2_failures)
    hence "xs @ [y] \<in> traces P" by (rule failures_traces)
    with RUC and VP and WFC and WSC and LR show ?Q using B
     by (rule gu_condition_imply_secure_2)
  qed
qed

text \<open>
\null

It is interesting to observe that unlike symmetry and transitivity, the assumed reflexivity of the
relations in the range of the domain-relation map is never used in the proof of the Generic
Unwinding Theorem. Nonetheless, by assuming that such relations be equivalence relations over
process traces rather than just symmetric and transitive ones, reflexivity has been kept among
assumptions for both historical reasons -- Rushby's Unwinding Theorem for deterministic state
machines deals with equivalence relations -- and practical reasons -- predicate
@{term "refl_on (traces P)"} may only be verified by a relation included in
@{term "traces P \<times> traces P"}, thus ensuring that traces be not correlated with non-trace event
lists, which is a necessary condition for weak future consistency (cf. \cite{R2}).

Here below are convenient variants of the Generic Unwinding Theorem applying to deterministic
processes and trace set processes (cf. \cite{R2}).

\null
\<close>

theorem d_generic_unwinding:
 "deterministic P \<Longrightarrow>
  view_partition P D R \<Longrightarrow>
  d_weakly_future_consistent P I D R \<Longrightarrow>
  weakly_step_consistent P D R \<Longrightarrow>
  locally_respects P I D R \<Longrightarrow>
  secure P I D"
proof (rule generic_unwinding, rule d_implies_ruc, simp_all)
qed (drule d_wfc_equals_dwfc [of P I D R], simp)

theorem ts_generic_unwinding:
 "trace_set T \<Longrightarrow>
  view_partition (ts_process T) D R \<Longrightarrow>
  d_weakly_future_consistent (ts_process T) I D R \<Longrightarrow>
  weakly_step_consistent (ts_process T) D R \<Longrightarrow>
  locally_respects (ts_process T) I D R \<Longrightarrow>
  secure (ts_process T) I D"
proof (rule d_generic_unwinding, simp_all)
qed (rule ts_process_d)


subsection "The Generic Unwinding Theorem: counterexample to condition necessity"

text \<open>
At a first glance, it seems reasonable to hypothesize that the Generic Unwinding Theorem expresses
a necessary, as well as sufficient, condition for security, viz. that whenever a process is secure
with respect to a policy, there should exist a set of "views" of process traces, one per domain,
satisfying the apparently simple assumptions of the theorem.

It can thus be surprising to discover that this hypothesis is false, as proven in what follows by
constructing a counterexample. The key observation for attaining this result is that symmetry,
transitivity, weak step consistency, and local policy respect permit to infer the correlation of
pairs of traces, and can then be given the form of introduction rules in the inductive definition of
a set. In this way, a "minimum" domain-relation map \<open>rel_induct\<close> is obtained, viz. a map such
that, for each domain \<open>u\<close>, the image of \<open>u\<close> under this map is included in the image of
\<open>u\<close> under any map which has the aforesaid properties -- particularly, which satisfies the
assumptions of the Generic Unwinding Theorem.

Although reflexivity can be given the form of an introduction rule, too, it has been omitted from
the inductive definition. This has been done in order to ensure that the "minimum" domain-relation
map, and consequently the counterexample as well, still remain such even if reflexivity, being
unnecessary (cf. above), were removed from the assumptions of the Generic Unwinding Theorem.

\null
\<close>

inductive_set rel_induct_aux ::
 "'a process \<Rightarrow> ('d \<times> 'd) set \<Rightarrow> ('a \<Rightarrow> 'd) \<Rightarrow> ('d \<times> 'a list \<times> 'a list) set"
for P :: "'a process" and I :: "('d \<times> 'd) set" and D :: "'a \<Rightarrow> 'd" where
rule_sym:   "(u, xs, ys) \<in> rel_induct_aux P I D \<Longrightarrow>
               (u, ys, xs) \<in> rel_induct_aux P I D" |
rule_trans: "\<lbrakk>(u, xs, ys) \<in> rel_induct_aux P I D;
             (u, ys, zs) \<in> rel_induct_aux P I D\<rbrakk> \<Longrightarrow>
               (u, xs, zs) \<in> rel_induct_aux P I D" |
rule_WSC:   "\<lbrakk>(u, xs, ys) \<in> rel_induct_aux P I D;
             (D x, xs, ys) \<in> rel_induct_aux P I D;
             x \<in> next_events P xs \<inter> next_events P ys\<rbrakk> \<Longrightarrow>
               (u, xs @ [x], ys @ [x]) \<in> rel_induct_aux P I D" |
rule_LR:    "\<lbrakk>u \<in> range D; (D x, u) \<notin> I; x \<in> next_events P xs\<rbrakk> \<Longrightarrow>
               (u, xs, xs @ [x]) \<in> rel_induct_aux P I D"

definition rel_induct ::
 "'a process \<Rightarrow> ('d \<times> 'd) set \<Rightarrow> ('a \<Rightarrow> 'd) \<Rightarrow> ('a, 'd) dom_rel_map" where
"rel_induct P I D u \<equiv> rel_induct_aux P I D `` {u}"

lemma rel_induct_subset:
  assumes
    VP:   "view_partition P D R" and
    WSC:  "weakly_step_consistent P D R" and
    LR:   "locally_respects P I D R"
  shows "rel_induct P I D u \<subseteq> R u"
proof (rule subsetI, simp add: rel_induct_def split_paired_all,
 erule rel_induct_aux.induct)
  fix u xs ys
  have "\<forall>u \<in> range D. equiv (traces P) (R u)"
   using VP by (simp add: view_partition_def)
  moreover assume "(u, xs, ys) \<in> rel_induct_aux P I D"
  hence "u \<in> range D" by (rule rel_induct_aux.induct)
  ultimately have "equiv (traces P) (R u)" ..
  hence "sym (R u)" by (simp add: equiv_def)
  moreover assume "(xs, ys) \<in> R u"
  ultimately show "(ys, xs) \<in> R u" by (rule symE)
next
  fix u xs ys zs
  have "\<forall>u \<in> range D. equiv (traces P) (R u)"
   using VP by (simp add: view_partition_def)
  moreover assume "(u, xs, ys) \<in> rel_induct_aux P I D"
  hence "u \<in> range D" by (rule rel_induct_aux.induct)
  ultimately have "equiv (traces P) (R u)" ..
  hence "trans (R u)" by (simp add: equiv_def)
  moreover assume "(xs, ys) \<in> R u" and "(ys, zs) \<in> R u"
  ultimately show "(xs, zs) \<in> R u" by (rule transE)
next
  fix u xs ys x
  have "\<forall>u \<in> range D. \<forall>xs ys x.
    (xs, ys) \<in> R u \<inter> R (D x) \<and> x \<in> next_events P xs \<inter> next_events P ys \<longrightarrow>
    (xs @ [x], ys @ [x]) \<in> R u"
   using WSC by (simp add: weakly_step_consistent_def)
  moreover assume "(u, xs, ys) \<in> rel_induct_aux P I D"
  hence "u \<in> range D" by (rule rel_induct_aux.induct)
  ultimately have "\<forall>xs ys x.
    (xs, ys) \<in> R u \<inter> R (D x) \<and> x \<in> next_events P xs \<inter> next_events P ys \<longrightarrow>
    (xs @ [x], ys @ [x]) \<in> R u" ..
  hence "(xs, ys) \<in> R u \<inter> R (D x) \<and> x \<in> next_events P xs \<inter> next_events P ys \<longrightarrow>
    (xs @ [x], ys @ [x]) \<in> R u"
   by blast
  moreover assume
    "(xs, ys) \<in> R u" and
    "(xs, ys) \<in> R (D x)" and
    "x \<in> next_events P xs \<inter> next_events P ys"
  ultimately show "(xs @ [x], ys @ [x]) \<in> R u" by simp
next
  fix u xs x
  have "\<forall>u \<in> range D. \<forall>xs x.
    (D x, u) \<notin> I \<and> x \<in> next_events P xs \<longrightarrow> (xs, xs @ [x]) \<in> R u"
   using LR by (simp add: locally_respects_def)
  moreover assume "u \<in> range D"
  ultimately have "\<forall>xs x.
    (D x, u) \<notin> I \<and> x \<in> next_events P xs \<longrightarrow> (xs, xs @ [x]) \<in> R u" ..
  hence "(D x, u) \<notin> I \<and> x \<in> next_events P xs \<longrightarrow> (xs, xs @ [x]) \<in> R u" by blast
  moreover assume "(D x, u) \<notin> I" and "x \<in> next_events P xs"
  ultimately show "(xs, xs @ [x]) \<in> R u" by simp
qed

text \<open>
\null

The next step consists of the definition of a trace set \<open>T\<^sub>c\<close>, the corresponding trace set
process \<open>P\<^sub>c\<close> (cf. \cite{R2}), and a reflexive, intransitive noninterference policy \<open>I\<^sub>c\<close>
for this process, where subscript "c" stands for "counterexample". As event-domain map, the identity
function is used, which explains why the policy is defined over events themselves.

\null
\<close>

datatype event\<^sub>c = a\<^sub>c | b\<^sub>c | c\<^sub>c

definition T\<^sub>c :: "event\<^sub>c list set" where
"T\<^sub>c \<equiv> {[],
  [a\<^sub>c], [a\<^sub>c, b\<^sub>c], [a\<^sub>c, b\<^sub>c, c\<^sub>c], [a\<^sub>c, b\<^sub>c, c\<^sub>c, a\<^sub>c],
  [b\<^sub>c], [b\<^sub>c, a\<^sub>c], [b\<^sub>c, c\<^sub>c], [b\<^sub>c, a\<^sub>c, c\<^sub>c]}"

definition P\<^sub>c :: "event\<^sub>c process" where
"P\<^sub>c \<equiv> ts_process T\<^sub>c"

definition I\<^sub>c :: "(event\<^sub>c \<times> event\<^sub>c) set" where
"I\<^sub>c \<equiv> {(a\<^sub>c, a\<^sub>c), (b\<^sub>c, b\<^sub>c), (b\<^sub>c, c\<^sub>c), (c\<^sub>c, c\<^sub>c), (c\<^sub>c, a\<^sub>c)}"

text \<open>
\null

Process @{term P\<^sub>c} can be shown to be secure with respect to policy @{term I\<^sub>c}. This result can be
obtained by applying the Ipurge Unwinding Theorem, in the version for trace set processes \cite{R2},
and then performing an exhaustive case distinction over all traces and domains, which obviously is
possible by virtue of their finiteness.

Nevertheless, @{term P\<^sub>c} and @{term I\<^sub>c} are such that there exists no domain-relation map satisfying
the assumptions of the Generic Unwinding Theorem. A proof \emph{ad absurdum} is given, based on the
fact that the pair of traces @{term "([a\<^sub>c, b\<^sub>c, c\<^sub>c], [b\<^sub>c, a\<^sub>c, c\<^sub>c])"} can be shown to be contained in
the image of @{term a\<^sub>c} under the "minimum" domain-relation map \<open>rel_induct\<close>. Therefore, it
would also be contained in the image of @{term a\<^sub>c} under a map satisfying the assumptions of the
Generic Unwinding Theorem, so that according to weak future consistency, @{term a\<^sub>c} should be a
possible subsequent event for trace @{term "[a\<^sub>c, b\<^sub>c, c\<^sub>c]"} just in case it were such for trace
@{term "[b\<^sub>c, a\<^sub>c, c\<^sub>c]"}. However, this conclusion contradicts the fact that @{term a\<^sub>c} is a possible
subsequent event for the former trace only.

\null
\<close>

lemma counterexample_trace_set:
 "trace_set T\<^sub>c"
by (simp add: trace_set_def T\<^sub>c_def)

lemma counterexample_next_events_1:
 "(x \<in> next_events (ts_process T\<^sub>c) xs) = (xs @ [x] \<in> T\<^sub>c)"
by (rule ts_process_next_events, rule counterexample_trace_set)

lemma counterexample_next_events_2:
 "(x \<in> next_events P\<^sub>c xs) = (xs @ [x] \<in> T\<^sub>c)"
by (subst P\<^sub>c_def, rule counterexample_next_events_1)

lemma counterexample_secure:
 "secure P\<^sub>c I\<^sub>c id"
proof (simp add: P\<^sub>c_def ts_ipurge_unwinding [OF counterexample_trace_set]
 dfc_equals_dwfc_rel_ipurge [symmetric] d_future_consistent_def, (rule allI)+)
  fix u xs ys
  show "(xs, ys) \<in> rel_ipurge (ts_process T\<^sub>c) I\<^sub>c id u \<longrightarrow>
    (xs \<in> traces (ts_process T\<^sub>c)) = (ys \<in> traces (ts_process T\<^sub>c)) \<and>
    next_dom_events (ts_process T\<^sub>c) id u xs =
    next_dom_events (ts_process T\<^sub>c) id u ys"
  proof (simp add: rel_ipurge_def ts_process_traces [OF counterexample_trace_set]
   next_dom_events_def counterexample_next_events_1)
    show "xs \<in> T\<^sub>c \<and> ys \<in> T\<^sub>c \<and>
      ipurge_tr_rev I\<^sub>c id u xs = ipurge_tr_rev I\<^sub>c id u ys \<longrightarrow>
      {x. u = x \<and> xs @ [x] \<in> T\<^sub>c} = {x. u = x \<and> ys @ [x] \<in> T\<^sub>c}"
    (* The following proof step performs an exhaustive case distinction over all traces and domains,
       and then could take ca. 20 seconds to be completed. *)
       apply (simp add: T\<^sub>c_def I\<^sub>c_def)
       apply clarify
       apply (cases u; elim disjE; simp; blast)
       done
  qed
qed

lemma counterexample_not_gu_condition_aux:
 "([a\<^sub>c, b\<^sub>c, c\<^sub>c], [b\<^sub>c, a\<^sub>c, c\<^sub>c]) \<in> rel_induct P\<^sub>c I\<^sub>c id a\<^sub>c"
proof (simp add: rel_induct_def)
  have "(a\<^sub>c, [a\<^sub>c, b\<^sub>c], [b\<^sub>c, a\<^sub>c]) \<in> rel_induct_aux P\<^sub>c I\<^sub>c id"
  proof -
    have A: "a\<^sub>c \<in> range id" by simp
    moreover have B: "(id b\<^sub>c, a\<^sub>c) \<notin> I\<^sub>c" by (simp add: I\<^sub>c_def)
    moreover have "b\<^sub>c \<in> next_events P\<^sub>c []"
      by (simp add: counterexample_next_events_2 T\<^sub>c_def)
    ultimately have "(a\<^sub>c, [], [] @ [b\<^sub>c]) \<in> rel_induct_aux P\<^sub>c I\<^sub>c id" by (rule rule_LR)
    hence C: "(a\<^sub>c, [], [b\<^sub>c]) \<in> rel_induct_aux P\<^sub>c I\<^sub>c id" by simp
    moreover from C have "(id a\<^sub>c, [], [b\<^sub>c]) \<in> rel_induct_aux P\<^sub>c I\<^sub>c id" by simp
    moreover have "a\<^sub>c \<in> next_events P\<^sub>c [] \<inter> next_events P\<^sub>c [b\<^sub>c]"
      by (simp add: counterexample_next_events_2 T\<^sub>c_def)
    ultimately have "(a\<^sub>c, [] @ [a\<^sub>c], [b\<^sub>c] @ [a\<^sub>c]) \<in> rel_induct_aux P\<^sub>c I\<^sub>c id"
      by (rule rule_WSC)
    hence D: "(a\<^sub>c, [a\<^sub>c], [b\<^sub>c, a\<^sub>c]) \<in> rel_induct_aux P\<^sub>c I\<^sub>c id" by simp
    have "b\<^sub>c \<in> next_events P\<^sub>c [a\<^sub>c]"
      by (simp add: counterexample_next_events_2 T\<^sub>c_def)
    with A and B have "(a\<^sub>c, [a\<^sub>c], [a\<^sub>c] @ [b\<^sub>c]) \<in> rel_induct_aux P\<^sub>c I\<^sub>c id"
      by (rule rule_LR)
    hence "(a\<^sub>c, [a\<^sub>c], [a\<^sub>c, b\<^sub>c]) \<in> rel_induct_aux P\<^sub>c I\<^sub>c id" by simp
    hence "(a\<^sub>c, [a\<^sub>c, b\<^sub>c], [a\<^sub>c]) \<in> rel_induct_aux P\<^sub>c I\<^sub>c id" by (rule rule_sym)
    thus ?thesis using D by (rule rule_trans)
  qed
  moreover have "(id c\<^sub>c, [a\<^sub>c, b\<^sub>c], [b\<^sub>c, a\<^sub>c]) \<in> rel_induct_aux P\<^sub>c I\<^sub>c id"
  proof simp
    have A: "c\<^sub>c \<in> range id" by simp
    moreover have B: "(id a\<^sub>c, c\<^sub>c) \<notin> I\<^sub>c" by (simp add: I\<^sub>c_def)
    moreover have C: "a\<^sub>c \<in> next_events P\<^sub>c []"
      by (simp add: counterexample_next_events_2 T\<^sub>c_def)
    ultimately have "(c\<^sub>c, [], [] @ [a\<^sub>c]) \<in> rel_induct_aux P\<^sub>c I\<^sub>c id" by (rule rule_LR)
    hence D: "(c\<^sub>c, [], [a\<^sub>c]) \<in> rel_induct_aux P\<^sub>c I\<^sub>c id" by simp
    have "b\<^sub>c \<in> range id" by simp
    moreover have "(id a\<^sub>c, b\<^sub>c) \<notin> I\<^sub>c" by (simp add: I\<^sub>c_def)
    ultimately have "(b\<^sub>c, [], [] @ [a\<^sub>c]) \<in> rel_induct_aux P\<^sub>c I\<^sub>c id"
      using C by (rule rule_LR)
    hence "(id b\<^sub>c, [], [a\<^sub>c]) \<in> rel_induct_aux P\<^sub>c I\<^sub>c id" by simp
    moreover have "b\<^sub>c \<in> next_events P\<^sub>c [] \<inter> next_events P\<^sub>c [a\<^sub>c]"
      by (simp add: counterexample_next_events_2 T\<^sub>c_def)
    ultimately have "(c\<^sub>c, [] @ [b\<^sub>c], [a\<^sub>c] @ [b\<^sub>c]) \<in> rel_induct_aux P\<^sub>c I\<^sub>c id"
      by (rule rule_WSC [OF D])
    hence "(c\<^sub>c, [b\<^sub>c], [a\<^sub>c, b\<^sub>c]) \<in> rel_induct_aux P\<^sub>c I\<^sub>c id" by simp
    hence "(c\<^sub>c, [a\<^sub>c, b\<^sub>c], [b\<^sub>c]) \<in> rel_induct_aux P\<^sub>c I\<^sub>c id" by (rule rule_sym)
    moreover have "a\<^sub>c \<in> next_events P\<^sub>c [b\<^sub>c]"
      by (simp add: counterexample_next_events_2 T\<^sub>c_def)
    with A and B have "(c\<^sub>c, [b\<^sub>c], [b\<^sub>c] @ [a\<^sub>c]) \<in> rel_induct_aux P\<^sub>c I\<^sub>c id"
      by (rule rule_LR)
    hence "(c\<^sub>c, [b\<^sub>c], [b\<^sub>c, a\<^sub>c]) \<in> rel_induct_aux P\<^sub>c I\<^sub>c id" by simp
    ultimately show "(c\<^sub>c, [a\<^sub>c, b\<^sub>c], [b\<^sub>c, a\<^sub>c]) \<in> rel_induct_aux P\<^sub>c I\<^sub>c id"
      by (rule rule_trans)
  qed
  moreover have "c\<^sub>c \<in> next_events P\<^sub>c [a\<^sub>c, b\<^sub>c] \<inter> next_events P\<^sub>c [b\<^sub>c, a\<^sub>c]"
    by (simp add: counterexample_next_events_2 T\<^sub>c_def)
  ultimately have "(a\<^sub>c, [a\<^sub>c, b\<^sub>c] @ [c\<^sub>c], [b\<^sub>c, a\<^sub>c] @ [c\<^sub>c]) \<in> rel_induct_aux P\<^sub>c I\<^sub>c id"
    by (rule rule_WSC)
  thus "(a\<^sub>c, [a\<^sub>c, b\<^sub>c, c\<^sub>c], [b\<^sub>c, a\<^sub>c, c\<^sub>c]) \<in> rel_induct_aux P\<^sub>c I\<^sub>c id" by simp
qed

lemma counterexample_not_gu_condition:
 "\<not> (\<exists>R.  view_partition P\<^sub>c id R \<and>
          weakly_future_consistent P\<^sub>c I\<^sub>c id R \<and>
          weakly_step_consistent P\<^sub>c id R \<and>
          locally_respects P\<^sub>c I\<^sub>c id R)"
proof (rule notI, erule exE, (erule conjE)+)
  fix R
  assume "weakly_future_consistent P\<^sub>c I\<^sub>c id R"
  hence "\<forall>u \<in> range id \<inter> (-I\<^sub>c) `` range id. \<forall>xs ys. (xs, ys) \<in> R u \<longrightarrow>
    next_dom_events P\<^sub>c id u xs = next_dom_events P\<^sub>c id u ys"
   by (simp add: weakly_future_consistent_def)
  moreover have "a\<^sub>c \<in> range id \<inter> (-I\<^sub>c) `` range id"
   by (simp add: I\<^sub>c_def, rule ImageI [of b\<^sub>c], simp_all)
  ultimately have "\<forall>xs ys. (xs, ys) \<in> R a\<^sub>c \<longrightarrow>
    next_dom_events P\<^sub>c id a\<^sub>c xs = next_dom_events P\<^sub>c id a\<^sub>c ys" ..
  hence "([a\<^sub>c, b\<^sub>c, c\<^sub>c], [b\<^sub>c, a\<^sub>c, c\<^sub>c]) \<in> R a\<^sub>c \<longrightarrow>
    next_dom_events P\<^sub>c id a\<^sub>c [a\<^sub>c, b\<^sub>c, c\<^sub>c] = next_dom_events P\<^sub>c id a\<^sub>c [b\<^sub>c, a\<^sub>c, c\<^sub>c]"
   by blast
  moreover assume
    "view_partition P\<^sub>c id R" and
    "weakly_step_consistent P\<^sub>c id R" and
    "locally_respects P\<^sub>c I\<^sub>c id R"
  hence "rel_induct P\<^sub>c I\<^sub>c id a\<^sub>c \<subseteq> R a\<^sub>c" by (rule rel_induct_subset)
  hence "([a\<^sub>c, b\<^sub>c, c\<^sub>c], [b\<^sub>c, a\<^sub>c, c\<^sub>c]) \<in> R a\<^sub>c"
   using counterexample_not_gu_condition_aux ..
  ultimately have
   "next_dom_events P\<^sub>c id a\<^sub>c [a\<^sub>c, b\<^sub>c, c\<^sub>c] = next_dom_events P\<^sub>c id a\<^sub>c [b\<^sub>c, a\<^sub>c, c\<^sub>c]" ..
  thus False
   by (simp add: next_dom_events_def counterexample_next_events_2 T\<^sub>c_def)
qed

theorem not_secure_implies_gu_condition:
 "\<not> (secure P\<^sub>c I\<^sub>c id \<longrightarrow>
    (\<exists>R.  view_partition P\<^sub>c id R \<and>
          weakly_future_consistent P\<^sub>c I\<^sub>c id R \<and>
          weakly_step_consistent P\<^sub>c id R \<and>
          locally_respects P\<^sub>c I\<^sub>c id R))"
proof (simp del: not_ex, rule conjI, rule counterexample_secure)
qed (rule counterexample_not_gu_condition)

end
