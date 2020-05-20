(*  Title:       Noninterference Security in Communicating Sequential Processes
    Author:      Pasquale Noce
                 Security Certification Specialist at Arjo Systems - Gep S.p.A.
                 pasquale dot noce dot lavoro at gmail dot com
                 pasquale dot noce at arjowiggins-it dot com
*)

section "Noninterference in CSP"

theory CSPNoninterference
imports Main
begin

text \<open>
\null

An extension of classical noninterference security for deterministic state machines, as introduced
by Goguen and Meseguer \cite{R2} and elegantly formalized by Rushby \cite{R3}, to nondeterministic
systems should satisfy two fundamental requirements: it should be based on a mathematically precise
theory of nondeterminism, and should be equivalent to (or at least not weaker than) the classical
notion in the degenerate deterministic case.

The purpose of this section is to formulate a definition of noninterference security that meet these
requirements, applying to the concept of process as formalized by Hoare in his remarkable theory of
Communicating Sequential Processes (CSP) \cite{R1}. The general case of a possibly intransitive
noninterference policy will be considered.

Throughout this paper, the salient points of definitions and proofs are commented; for additional
information see Isabelle documentation, particularly \cite{R5}, \cite{R6}, \cite{R7}, and \cite{R8}.
\<close>


subsection "Processes"

text \<open>
It is convenient to represent CSP processes by means of a type definition including a type variable,
which stands for the process alphabet. Type \<open>process\<close> shall then be isomorphic to the subset
of the product type of failures sets and divergences sets comprised of the pairs that satisfy the
properties enunciated in \cite{R1}, section 3.9. Such subset shall be shown to contain process
\emph{STOP}, which proves that it is nonempty.

Property \emph{C5} is not considered as it is entailed by \emph{C7}. Moreover, the formalization of
properties \emph{C2} and \emph{C6} only takes into account event lists \emph{t} containing a single
item. Such formulation is equivalent to the original one, since the truth of \emph{C2} and \emph{C6}
for a singleton list \emph{t} immediately derives from that for a generic list, and conversely:

\begin{itemize}

\item
the truth of \emph{C2} and \emph{C6} for a generic nonempty list \emph{t} results from the repeated
application of \emph{C2} and \emph{C6} for a singleton list;

\item
the truth of \emph{C2} for \emph{t} matching the empty list is implied by property \emph{C3};

\item
the truth of \emph{C6} for \emph{t} matching the empty list is a tautology.

\end{itemize}

The advantage of the proposed formulation is that it facilitates the task to prove that pairs of
failures and divergences sets defined inductively indeed be processes, viz. be included in the set
of pairs isomorphic to type \<open>process\<close>, since the introduction rules in such inductive
definitions will typically construct process traces by appending one item at a time.

In what follows, the concept of process is formalized according to the previous considerations.

\null
\<close>

type_synonym 'a failure = "'a list \<times> 'a set"

type_synonym 'a process_prod = "'a failure set \<times> 'a list set"

definition process_prop_1 :: "'a process_prod \<Rightarrow> bool" where
"process_prop_1 P \<equiv> ([], {}) \<in> fst P"

definition process_prop_2 :: "'a process_prod \<Rightarrow> bool" where
"process_prop_2 P \<equiv> \<forall>xs x X. (xs @ [x], X) \<in> fst P \<longrightarrow> (xs, {}) \<in> fst P"

definition process_prop_3 :: "'a process_prod \<Rightarrow> bool" where
"process_prop_3 P \<equiv> \<forall>xs X Y. (xs, Y) \<in> fst P \<and> X \<subseteq> Y \<longrightarrow> (xs, X) \<in> fst P"

definition process_prop_4 :: "'a process_prod \<Rightarrow> bool" where
"process_prop_4 P \<equiv> \<forall>xs x X. (xs, X) \<in> fst P \<longrightarrow>
  (xs @ [x], {}) \<in> fst P \<or> (xs, insert x X) \<in> fst P"

definition process_prop_5 :: "'a process_prod \<Rightarrow> bool" where
"process_prop_5 P \<equiv> \<forall>xs x. xs \<in> snd P \<longrightarrow> xs @ [x] \<in> snd P"

definition process_prop_6 :: "'a process_prod \<Rightarrow> bool" where
"process_prop_6 P \<equiv> \<forall>xs X. xs \<in> snd P \<longrightarrow> (xs, X) \<in> fst P"

definition process_set :: "'a process_prod set" where
"process_set \<equiv> {P.
  process_prop_1 P \<and>
  process_prop_2 P \<and>
  process_prop_3 P \<and>
  process_prop_4 P \<and>
  process_prop_5 P \<and>
  process_prop_6 P}"

typedef 'a process = "process_set :: 'a process_prod set"
by (rule_tac x = "({(xs, X). xs = []}, {})" in exI, simp add:
  process_set_def
  process_prop_1_def
  process_prop_2_def
  process_prop_3_def
  process_prop_4_def
  process_prop_5_def
  process_prop_6_def)

text \<open>
\null

Here below are the definitions of some functions acting on processes. Functions \<open>failures\<close>,
\<open>traces\<close>, and \<open>deterministic\<close> match the homonymous notions defined in \cite{R1}. As for
the other ones:

\begin{itemize}

\item
\<open>futures P xs\<close> matches the failures set of process \emph{P / xs};

\item
\<open>refusals P xs\<close> matches the refusals set of process \emph{P / xs};

\item
\<open>next_events P xs\<close> matches the event set (\emph{P / xs})\textsuperscript{0}.

\end{itemize}

\null
\<close>

definition failures :: "'a process \<Rightarrow> 'a failure set" where
"failures P \<equiv> fst (Rep_process P)"

definition futures :: "'a process \<Rightarrow> 'a list \<Rightarrow> 'a failure set" where
"futures P xs \<equiv> {(ys, Y). (xs @ ys, Y) \<in> failures P}"

definition traces :: "'a process \<Rightarrow> 'a list set" where
"traces P \<equiv> Domain (failures P)"

definition refusals :: "'a process \<Rightarrow> 'a list \<Rightarrow> 'a set set" where
"refusals P xs \<equiv> failures P `` {xs}"

definition next_events :: "'a process \<Rightarrow> 'a list \<Rightarrow> 'a set" where
"next_events P xs \<equiv> {x. xs @ [x] \<in> traces P}"

definition deterministic :: "'a process \<Rightarrow> bool" where
"deterministic P \<equiv>
  \<forall>xs \<in> traces P. \<forall>X. X \<in> refusals P xs = (X \<inter> next_events P xs = {})"

text \<open>
\null

In what follows, properties \<open>process_prop_2\<close> and \<open>process_prop_3\<close> of processes are put
into the form of introduction rules, which will turn out to be useful in subsequent proofs.
Particularly, the more general formulation of \<open>process_prop_2\<close> as given in \cite{R1} (section
3.9, property \emph{C2}) is restored, and it is expressed in terms of both functions
\<open>failures\<close> and \<open>futures\<close>.

\null
\<close>

lemma process_rule_2: "(xs @ [x], X) \<in> failures P \<Longrightarrow> (xs, {}) \<in> failures P"
proof (simp add: failures_def)
  have "Rep_process P \<in> process_set" (is "?P' \<in> _") by (rule Rep_process)
  hence "\<forall>xs x X. (xs @ [x], X) \<in> fst ?P' \<longrightarrow> (xs, {}) \<in> fst ?P'"
   by (simp add: process_set_def process_prop_2_def)
  thus "(xs @ [x], X) \<in> fst ?P' \<Longrightarrow> (xs, {}) \<in> fst ?P'" by blast
qed

lemma process_rule_3: "(xs, Y) \<in> failures P \<Longrightarrow> X \<subseteq> Y \<Longrightarrow> (xs, X) \<in> failures P"
proof (simp add: failures_def)
  have "Rep_process P \<in> process_set" (is "?P' \<in> _") by (rule Rep_process)
  hence "\<forall>xs X Y. (xs, Y) \<in> fst ?P' \<and> X \<subseteq> Y \<longrightarrow> (xs, X) \<in> fst ?P'"
   by (simp add: process_set_def process_prop_3_def)
  thus "(xs, Y) \<in> fst ?P' \<Longrightarrow> X \<subseteq> Y \<Longrightarrow> (xs, X) \<in> fst ?P'" by blast
qed

lemma process_rule_2_failures [rule_format]:
 "(xs @ xs', X) \<in> failures P \<longrightarrow> (xs, {}) \<in> failures P"
proof (induction xs' arbitrary: X rule: rev_induct, rule_tac [!] impI, simp)
  fix X
  assume "(xs, X) \<in> failures P"
  moreover have "{} \<subseteq> X" ..
  ultimately show "(xs, {}) \<in> failures P" by (rule process_rule_3)
next
  fix x xs' X
  assume "\<And>X. (xs @ xs', X) \<in> failures P \<longrightarrow> (xs, {}) \<in> failures P"
  hence "(xs @ xs', {}) \<in> failures P \<longrightarrow> (xs, {}) \<in> failures P" .
  moreover assume "(xs @ xs' @ [x], X) \<in> failures P"
  hence "((xs @ xs') @ [x], X) \<in> failures P" by simp
  hence "(xs @ xs', {}) \<in> failures P" by (rule process_rule_2)
  ultimately show "(xs, {}) \<in> failures P" ..
qed

lemma process_rule_2_futures:
 "(ys @ ys', Y) \<in> futures P xs \<Longrightarrow> (ys, {}) \<in> futures P xs"
by (simp add: futures_def, simp only: append_assoc [symmetric], rule process_rule_2_failures)


subsection "Noninterference"

text \<open>
In the classical theory of noninterference, a deterministic state machine is considered to be secure
just in case, for any trace of the machine and any action occurring next, the observable effect of
the action, i.e. the produced output, is compatible with the assigned noninterference policy.

Thus, by analogy, it seems reasonable to regard a process as being noninterference-secure just in
case, for any of its traces and any event occurring next, the observable effect of the event, i.e.
the set of the possible futures of the process, is compatible with a given noninterference policy.

More precisely, let \<open>sinks I D u xs\<close> be the set of the security domains of the events within
event list \<open>xs\<close> that may be affected by domain \<open>u\<close> according to interference relation
\<open>I\<close>, where \<open>D\<close> is the mapping of events into their domains. Since the general case of a
possibly intransitive relation \<open>I\<close> is considered, function \<open>sinks\<close> has to be defined
recursively, similarly to what happens for function \emph{sources} in \cite{R3}. However,
contrariwise to function \emph{sources}, function \<open>sinks\<close> takes into account the influence of
the input domain on the input event list, so that the recursive decomposition of the latter has to
be performed by item appending rather than prepending.

Furthermore, let \<open>ipurge_tr I D u xs\<close> be the sublist of event list \<open>xs\<close> obtained by
recursively deleting the events that may be affected by domain \<open>u\<close> as detected via function
\<open>sinks\<close>, and \<open>ipurge_ref I D u xs X\<close> be the subset of refusal \<open>X\<close> whose elements
may not be affected by either \<open>u\<close> or any domain in \<open>sinks I D u xs\<close>.

Then, a process \<open>P\<close> is secure just in case, for each event list \<open>xs\<close> and each
\<open>(y # ys, Y), (zs, Z) \<in> futures P xs\<close>, both of the following conditions are satisfied:

\begin{itemize}

\item
\<open>(ipurge_tr I D (D y) ys, ipurge_ref I D (D y) ys Y) \<in> futures P xs\<close>.
\\Otherwise, the absence of event \<open>y\<close> after \<open>xs\<close> would affect the possibility for pair
\<open>(ipurge_tr I D (D y) ys, ipurge_ref I D (D y) ys Y)\<close> to occur as a future of \<open>xs\<close>,
although its components, except for the deletion of \<open>y\<close>, are those of possible future
\<open>(y # ys, Y)\<close> deprived of any event allowed to be affected by \<open>y\<close>.

\item
\<open>(y # ipurge_tr I D (D y) zs, ipurge_ref I D (D y) zs Z)\<close>
\\\<open>\<in> futures P xs\<close>.
\\Otherwise, the presence of event \<open>y\<close> after \<open>xs\<close> would affect the possibility for pair
\<open>(y # ipurge_tr I D (D y) zs, ipurge_ref I D (D y) zs Z)\<close> to occur as a future of
\<open>xs\<close>, although its components, except for the addition of \<open>y\<close>, are those of possible
future \<open>(zs, Z)\<close> deprived of any event allowed to be affected by \<open>y\<close>.

\end{itemize}

Observe that this definition of security, henceforth referred to as
\emph{CSP noninterference security}, does not rest on the supposition that noninterference policy
\<open>I\<close> be reflexive, even though any policy of practical significance will be such.

Moreover, this simpler formulation is equivalent to the one obtained by restricting the range of
event list \<open>xs\<close> to the traces of process \<open>P\<close>. In fact, for each \<open>zs\<close>, \<open>Z\<close>,
\<open>(zs, Z) \<in> futures P xs\<close> just in case \<open>(xs @ zs, Z) \<in> failures P\<close>, which by virtue
of rule \<open>process_rule_2_failures\<close> implies that \<open>xs\<close> is a trace of \<open>P\<close>. Therefore,
formula \<open>(zs, Z) \<in> futures P xs\<close> is invariably false in case \<open>xs\<close> is not a trace of
\<open>P\<close>.

Here below are the formal counterparts of the definitions discussed so far.

\null
\<close>

function sinks :: "('d \<times> 'd) set \<Rightarrow> ('a \<Rightarrow> 'd) \<Rightarrow> 'd \<Rightarrow> 'a list \<Rightarrow> 'd set" where
"sinks _ _ _ [] = {}" |
"sinks I D u (xs @ [x]) = (if (u, D x) \<in> I \<or> (\<exists>v \<in> sinks I D u xs. (v, D x) \<in> I)
  then insert (D x) (sinks I D u xs)
  else sinks I D u xs)"
proof (atomize_elim, simp_all add: split_paired_all)
qed (rule rev_cases, rule disjI1, assumption, simp)
termination by lexicographic_order

function ipurge_tr :: "('d \<times> 'd) set \<Rightarrow> ('a \<Rightarrow> 'd) \<Rightarrow> 'd \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"ipurge_tr _ _ _ [] = []" |
"ipurge_tr I D u (xs @ [x]) = (if D x \<in> sinks I D u (xs @ [x])
  then ipurge_tr I D u xs
  else ipurge_tr I D u xs @ [x])"
proof (atomize_elim, simp_all add: split_paired_all)
qed (rule rev_cases, rule disjI1, assumption, simp)
termination by lexicographic_order

definition ipurge_ref ::
 "('d \<times> 'd) set \<Rightarrow> ('a \<Rightarrow> 'd) \<Rightarrow> 'd \<Rightarrow> 'a list \<Rightarrow> 'a set \<Rightarrow> 'a set" where
"ipurge_ref I D u xs X \<equiv>
  {x \<in> X. (u, D x) \<notin> I \<and> (\<forall>v \<in> sinks I D u xs. (v, D x) \<notin> I)}"

definition secure :: "'a process \<Rightarrow> ('d \<times> 'd) set \<Rightarrow> ('a \<Rightarrow> 'd) \<Rightarrow> bool" where
"secure P I D \<equiv>
  \<forall>xs y ys Y zs Z. (y # ys, Y) \<in> futures P xs \<and> (zs, Z) \<in> futures P xs \<longrightarrow>
  (ipurge_tr I D (D y) ys, ipurge_ref I D (D y) ys Y) \<in> futures P xs \<and>
  (y # ipurge_tr I D (D y) zs, ipurge_ref I D (D y) zs Z) \<in> futures P xs"

text \<open>
\null

The continuation of this section is dedicated to the demonstration of some lemmas concerning
functions \<open>sinks\<close>, \<open>ipurge_tr\<close>, and \<open>ipurge_ref\<close> which will turn out to be useful
in subsequent proofs.

\null
\<close>

lemma sinks_cons_same:
  assumes R: "refl I"
  shows "sinks I D (D x) (x # xs) = insert (D x) (sinks I D (D x) xs)"
proof (rule rev_induct, simp)
  have A: "[x] = [] @ [x]" by simp
  have "sinks I D (D x) [x] = (if (D x, D x) \<in> I \<or> (\<exists>v \<in> {}. (v, D x) \<in> I)
    then insert (D x) {}
    else {})"
   by (subst A, simp only: sinks.simps)
  moreover have "(D x, D x) \<in> I" using R by (simp add: refl_on_def)
  ultimately show "sinks I D (D x) [x] = {D x}" by simp
next
  fix x' xs
  assume A: "sinks I D (D x) (x # xs) = insert (D x) (sinks I D (D x) xs)"
  show "sinks I D (D x) (x # xs @ [x']) =
    insert (D x) (sinks I D (D x) (xs @ [x']))"
  proof (cases "(D x, D x') \<in> I \<or> (\<exists>v \<in> sinks I D (D x) xs. (v, D x') \<in> I)",
   simp_all (no_asm_simp))
    case True
    hence "(D x, D x') \<in> I \<or> (\<exists>v \<in> sinks I D (D x) (x # xs). (v, D x') \<in> I)"
     using A by simp
    hence "sinks I D (D x) ((x # xs) @ [x']) =
      insert (D x') (sinks I D (D x) (x # xs))"
     by (simp only: sinks.simps if_True)
    thus "sinks I D (D x) (x # xs @ [x']) =
      insert (D x) (insert (D x') (sinks I D (D x) xs))"
     using A by (simp add: insert_commute)
  next
    case False
    hence "\<not> ((D x, D x') \<in> I \<or> (\<exists>v \<in> sinks I D (D x) (x # xs). (v, D x') \<in> I))"
     using A by simp
    hence "sinks I D (D x) ((x # xs) @ [x']) = sinks I D (D x) (x # xs)"
     by (simp only: sinks.simps if_False)
    thus "sinks I D (D x) (x # xs @ [x']) = insert (D x) (sinks I D (D x) xs)"
     using A by simp
  qed
qed

lemma ipurge_tr_cons_same:
  assumes R: "refl I"
  shows "ipurge_tr I D (D x) (x # xs) = ipurge_tr I D (D x) xs"
proof (induction xs rule: rev_induct, simp)
  have A: "[x] = [] @ [x]" by simp
  have "ipurge_tr I D (D x) [x] = (if D x \<in> sinks I D (D x) ([] @ [x])
    then []
    else [] @ [x])"
   by (subst A, simp only: ipurge_tr.simps)
  moreover have "sinks I D (D x) [x] = {D x}"
   using R by (simp add: sinks_cons_same)
  ultimately show "ipurge_tr I D (D x) [x] = []" by simp
next
  fix x' xs
  assume A: "ipurge_tr I D (D x) (x # xs) = ipurge_tr I D (D x) xs"
  show "ipurge_tr I D (D x) (x # xs @ [x']) = ipurge_tr I D (D x) (xs @ [x'])"
  proof (cases "D x' \<in> sinks I D (D x) (x # xs @ [x'])")
    assume B: "D x' \<in> sinks I D (D x) (x # xs @ [x'])"
    hence "D x' \<in> sinks I D (D x) ((x # xs) @ [x'])" by simp
    hence "ipurge_tr I D (D x) ((x # xs) @ [x']) = ipurge_tr I D (D x) (x # xs)"
     by (simp only: ipurge_tr.simps if_True)
    hence C: "ipurge_tr I D (D x) (x # xs @ [x']) = ipurge_tr I D (D x) xs"
     using A by simp
    have "D x' = D x \<or> D x' \<in> sinks I D (D x) (xs @ [x'])"
     using R and B by (simp add: sinks_cons_same)
    moreover {
      assume "D x' = D x"
      hence "(D x, D x') \<in> I" using R by (simp add: refl_on_def)
      hence "ipurge_tr I D (D x) (xs @ [x']) = ipurge_tr I D (D x) xs" by simp
    }
    moreover {
      assume "D x' \<in> sinks I D (D x) (xs @ [x'])"
      hence "ipurge_tr I D (D x) (xs @ [x']) = ipurge_tr I D (D x) xs" by simp
    }
    ultimately have D: "ipurge_tr I D (D x) (xs @ [x']) = ipurge_tr I D (D x) xs"
     by blast
    show ?thesis using C and D by simp
  next
    assume B: "D x' \<notin> sinks I D (D x) (x # xs @ [x'])"
    hence "D x' \<notin> sinks I D (D x) ((x # xs) @ [x'])" by simp
    hence "ipurge_tr I D (D x) ((x # xs) @ [x']) =
      ipurge_tr I D (D x) (x # xs) @ [x']"
     by (simp only: ipurge_tr.simps if_False)
    hence "ipurge_tr I D (D x) (x # xs @ [x']) = ipurge_tr I D (D x) xs @ [x']"
     using A by simp
    moreover have "\<not> (D x' = D x \<or> D x' \<in> sinks I D (D x) (xs @ [x']))"
     using R and B by (simp add: sinks_cons_same)
    hence "ipurge_tr I D (D x) (xs @ [x']) = ipurge_tr I D (D x) xs @ [x']"
     by simp
    ultimately show ?thesis by simp
  qed
qed

lemma sinks_cons_nonint:
  assumes A: "(u, D x) \<notin> I"
  shows "sinks I D u (x # xs) = sinks I D u xs"
proof (rule rev_induct, simp)
  have "sinks I D u [x] = sinks I D u ([] @ [x])" by simp
  hence "sinks I D u [x] = (if (u, D x) \<in> I \<or> (\<exists>v \<in> {}. (v, D x) \<in> I)
    then insert (D x) {}
    else {})"
   by (simp only: sinks.simps)
  thus "sinks I D u [x] = {}" using A by simp
next
  fix xs x'
  assume B: "sinks I D u (x # xs) = sinks I D u xs" (is "?d' = ?d")
  have "x # xs @ [x'] = (x # xs) @ [x']" by simp
  hence C: "sinks I D u (x # xs @ [x']) =
    (if (u, D x') \<in> I \<or> (\<exists>v \<in> ?d'. (v, D x') \<in> I)
    then insert (D x') ?d'
    else ?d')"
    by (simp only: sinks.simps)
  show "sinks I D u (x # xs @ [x']) = sinks I D u (xs @ [x'])"
  proof (cases "(u, D x') \<in> I \<or> (\<exists>v \<in> ?d. (v, D x') \<in> I)")
    case True
    with B and C have "sinks I D u (x # xs @ [x']) = insert (D x') ?d"
      by simp
    with True show ?thesis by simp
  next
    case False
    with B and C have "sinks I D u (x # xs @ [x']) = ?d" by simp
    with False show ?thesis by simp
  qed
qed

lemma sinks_empty [rule_format]:
 "sinks I D u xs = {} \<longrightarrow> ipurge_tr I D u xs = xs"
proof (rule rev_induct, simp, rule impI)
  fix x xs
  assume A: "sinks I D u (xs @ [x]) = {}"
  moreover have "sinks I D u xs \<subseteq> sinks I D u (xs @ [x])"
   by (simp add: subset_insertI)
  ultimately have "sinks I D u xs = {}" by simp
  moreover assume "sinks I D u xs = {} \<longrightarrow> ipurge_tr I D u xs = xs"
  ultimately have "ipurge_tr I D u xs = xs" by (rule rev_mp)
  thus "ipurge_tr I D u (xs @ [x]) = xs @ [x]" using A by simp
qed

lemma ipurge_ref_eq:
  assumes A: "D x \<in> sinks I D u (xs @ [x])"
  shows "ipurge_ref I D u (xs @ [x]) X =
    ipurge_ref I D u xs {x' \<in> X. (D x, D x') \<notin> I}"
proof (rule equalityI, rule_tac [!] subsetI, simp_all add: ipurge_ref_def del: sinks.simps,
 (erule conjE)+, (erule_tac [2] conjE)+)
  fix y
  assume B: "\<forall>v \<in> sinks I D u (xs @ [x]). (v, D y) \<notin> I"
  show "(D x, D y) \<notin> I \<and> (\<forall>v \<in> sinks I D u xs. (v, D y) \<notin> I)"
  proof (rule conjI, rule_tac [2] ballI)
    show "(D x, D y) \<notin> I" using B and A ..
  next
    fix v
    assume "v \<in> sinks I D u xs"
    hence "v \<in> sinks I D u (xs @ [x])" by simp
    with B show "(v, D y) \<notin> I" ..
  qed
next
  fix y
  assume
    B: "(D x, D y) \<notin> I" and
    C: "\<forall>v \<in> sinks I D u xs. (v, D y) \<notin> I"
  show "\<forall>v \<in> sinks I D u (xs @ [x]). (v, D y) \<notin> I"
  proof (rule ballI, cases "(u, D x) \<in> I \<or> (\<exists>v \<in> sinks I D u xs. (v, D x) \<in> I)")
    fix v
    case True
    moreover assume "v \<in> sinks I D u (xs @ [x])"
    ultimately have "v = D x \<or> v \<in> sinks I D u xs" by simp
    moreover {
      assume "v = D x"
      with B have "(v, D y) \<notin> I" by simp
    }
    moreover {
      assume "v \<in> sinks I D u xs"
      with C have "(v, D y) \<notin> I" ..
    }
    ultimately show "(v, D y) \<notin> I" by blast
  next
    fix v
    case False
    moreover assume "v \<in> sinks I D u (xs @ [x])"
    ultimately have "v \<in> sinks I D u xs" by simp
    with C show "(v, D y) \<notin> I" ..
  qed
qed

end
