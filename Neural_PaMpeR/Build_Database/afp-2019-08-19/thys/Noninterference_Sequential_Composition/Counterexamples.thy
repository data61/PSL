(*  Title:       Conservation of CSP Noninterference Security under Sequential Composition
    Author:      Pasquale Noce
                 Security Certification Specialist at Arjo Systems, Italy
                 pasquale dot noce dot lavoro at gmail dot com
                 pasquale dot noce at arjosystems dot com
*)

section "Necessity of nontrivial assumptions"

theory Counterexamples
imports SequentialComposition
begin

text \<open>
\null

The security conservation theorem proven in this paper contains two nontrivial assumptions; namely,
the security policy must satisfy predicate @{term secure_termination}, and the first input process
must satisfy predicate @{term sequential} instead of @{term weakly_sequential} alone. This section
shows, by means of counterexamples, that both of these assumptions are necessary for the theorem to
hold.

In more detail, two counterexamples will be constructed: the former drops the termination security
assumption, whereas the latter drops the process sequentiality assumption, replacing it with weak
sequentiality alone. In both cases, all the other assumptions of the theorem keep being satisfied.

Both counterexamples make use of reflexive security policies, which is the case for any policy of
practical significance, and are based on trace set processes as defined in \cite{R3}. The security
of the processes input to sequential composition, as well as the insecurity of the resulting
process, are demonstrated by means of the Ipurge Unwinding Theorem proven in \cite{R3}.
\<close>


subsection "Preliminary definitions and lemmas"

text \<open>
Both counterexamples will use the same type @{term event} as native type of ordinary events, as well
as the same process @{term Q} as second input to sequential composition. Here below are the
definitions of these constants, followed by few useful lemmas on process @{term Q}.

\null
\<close>

datatype event = a | b

definition Q :: "event option process" where
"Q \<equiv> ts_process {[], [Some b]}"

lemma trace_set_snd:
 "trace_set {[], [Some b]}"
by (simp add: trace_set_def)

lemmas failures_snd = ts_process_failures [OF trace_set_snd]

lemmas traces_snd = ts_process_traces [OF trace_set_snd]

lemmas next_events_snd = ts_process_next_events [OF trace_set_snd]

lemmas unwinding_snd = ts_ipurge_unwinding [OF trace_set_snd]


subsection "Necessity of termination security"

text \<open>
The reason why the conservation of noninterference security under sequential composition requires
the security policy to satisfy predicate @{term secure_termination} is that the second input process
cannot engage in its events unless the first process has terminated successfully. Thus, the ordinary
events of the first process can indirectly affect the events of the second process by affecting the
successful termination of the first process. Therefore, if an ordinary event is allowed to affect
successful termination, then the policy must allow it to affect any other event as well, which is
exactly what predicate @{term secure_termination} states.

A counterexample showing the necessity of this assumption can then be constructed by defining a
reflexive policy @{term I\<^sub>1} that allows event @{term "Some a"} to affect @{term None}, but not
@{term "Some b"}, and a deterministic process @{term P\<^sub>1} that can engage in @{term None} only after
engaging in @{term "Some a"}. The resulting process @{term "P\<^sub>1 ; Q"} will number
@{term "[Some a, Some b]"}, but not @{term "[Some b]"}, among its traces, so that event
@{term "Some a"} affects the occurrence of event @{term "Some b"} in contrast with policy
@{term I\<^sub>1}, viz. @{term "P\<^sub>1 ; Q"} is not secure with respect to @{term I\<^sub>1}.

Here below are the definitions of constants @{term I\<^sub>1} and @{term P\<^sub>1}, followed by few useful lemmas
on process @{term P\<^sub>1}.

\null
\<close>

definition I\<^sub>1 :: "(event option \<times> event option) set" where
"I\<^sub>1 \<equiv> {(Some a, None)}\<^sup>="

definition P\<^sub>1 :: "event option process" where
"P\<^sub>1 \<equiv> ts_process {[], [Some a], [Some a, None]}"

lemma trace_set_fst_1:
 "trace_set {[], [Some a], [Some a, None]}"
by (simp add: trace_set_def)

lemmas failures_fst_1 = ts_process_failures [OF trace_set_fst_1]

lemmas traces_fst_1 = ts_process_traces [OF trace_set_fst_1]

lemmas next_events_fst_1 = ts_process_next_events [OF trace_set_fst_1]

lemmas unwinding_fst_1 = ts_ipurge_unwinding [OF trace_set_fst_1]

text \<open>
\null

Here below is the proof that policy @{term I\<^sub>1} does not satisfy predicate
@{term secure_termination}, whereas the remaining assumptions of the security conservation theorem
keep being satisfied. For the sake of simplicity, the identity function is used as event-domain map.

\null
\<close>

lemma not_secure_termination_1:
 "\<not> secure_termination I\<^sub>1 id"
proof (simp add: secure_termination_def I\<^sub>1_def, rule exI [where x = "Some a"],
 simp)
qed (rule exI [where x = "Some b"], simp)

lemma ref_union_closed_fst_1:
 "ref_union_closed P\<^sub>1"
by (rule d_implies_ruc, subst P\<^sub>1_def, rule ts_process_d, rule trace_set_fst_1)

lemma sequential_fst_1:
 "sequential P\<^sub>1"
proof (simp add: sequential_def sentences_def P\<^sub>1_def traces_fst_1)
qed (simp add: set_eq_iff next_events_fst_1)

lemma secure_fst_1:
 "secure P\<^sub>1 I\<^sub>1 id"
proof (simp add: P\<^sub>1_def unwinding_fst_1 dfc_equals_dwfc_rel_ipurge [symmetric]
 d_future_consistent_def rel_ipurge_def traces_fst_1, (rule allI)+)
  fix u xs ys
  show
   "(xs = [] \<or> xs = [Some a] \<or> xs = [Some a, None]) \<and>
    (ys = [] \<or> ys = [Some a] \<or> ys = [Some a, None]) \<and>
    ipurge_tr_rev I\<^sub>1 id u xs = ipurge_tr_rev I\<^sub>1 id u ys \<longrightarrow>
      next_dom_events (ts_process {[], [Some a], [Some a, None]}) id u xs =
      next_dom_events (ts_process {[], [Some a], [Some a, None]}) id u ys"
  proof (simp add: next_dom_events_def next_events_fst_1, cases u)
    case None
    show
     "(xs = [] \<or> xs = [Some a] \<or> xs = [Some a, None]) \<and>
      (ys = [] \<or> ys = [Some a] \<or> ys = [Some a, None]) \<and>
      ipurge_tr_rev I\<^sub>1 id u xs = ipurge_tr_rev I\<^sub>1 id u ys \<longrightarrow>
        {x. u = x \<and> (xs = [] \<and> x = Some a \<or> xs = [Some a] \<and> x = None)} =
        {x. u = x \<and> (ys = [] \<and> x = Some a \<or> ys = [Some a] \<and> x = None)}"
     by (simp add: I\<^sub>1_def None, rule impI, (erule conjE)+,
      (((erule disjE)+)?, simp)+)
  next
    case (Some v)
    show
     "(xs = [] \<or> xs = [Some a] \<or> xs = [Some a, None]) \<and>
      (ys = [] \<or> ys = [Some a] \<or> ys = [Some a, None]) \<and>
      ipurge_tr_rev I\<^sub>1 id u xs = ipurge_tr_rev I\<^sub>1 id u ys \<longrightarrow>
        {x. u = x \<and> (xs = [] \<and> x = Some a \<or> xs = [Some a] \<and> x = None)} =
        {x. u = x \<and> (ys = [] \<and> x = Some a \<or> ys = [Some a] \<and> x = None)}"
     by (simp add: I\<^sub>1_def Some, rule impI, (erule conjE)+, cases v,
      (((erule disjE)+)?, simp, blast?)+)
  qed
qed

lemma secure_snd_1:
 "secure Q I\<^sub>1 id"
proof (simp add: Q_def unwinding_snd dfc_equals_dwfc_rel_ipurge [symmetric]
 d_future_consistent_def rel_ipurge_def traces_snd, (rule allI)+)
  fix u xs ys
  show
   "(xs = [] \<or> xs = [Some b]) \<and>
    (ys = [] \<or> ys = [Some b]) \<and>
    ipurge_tr_rev I\<^sub>1 id u xs = ipurge_tr_rev I\<^sub>1 id u ys \<longrightarrow>
      next_dom_events (ts_process {[], [Some b]}) id u xs =
      next_dom_events (ts_process {[], [Some b]}) id u ys"
  proof (simp add: next_dom_events_def next_events_snd, cases u)
    case None
    show
     "(xs = [] \<or> xs = [Some b]) \<and>
      (ys = [] \<or> ys = [Some b]) \<and>
      ipurge_tr_rev I\<^sub>1 id u xs = ipurge_tr_rev I\<^sub>1 id u ys \<longrightarrow>
        {x. u = x \<and> xs = [] \<and> x = Some b} = {x. u = x \<and> ys = [] \<and> x = Some b}"
     by (simp add: None, rule impI, (erule conjE)+,
      (((erule disjE)+)?, simp)+)
  next
    case (Some v)
    show
     "(xs = [] \<or> xs = [Some b]) \<and>
      (ys = [] \<or> ys = [Some b]) \<and>
      ipurge_tr_rev I\<^sub>1 id u xs = ipurge_tr_rev I\<^sub>1 id u ys \<longrightarrow>
        {x. u = x \<and> xs = [] \<and> x = Some b} = {x. u = x \<and> ys = [] \<and> x = Some b}"
     by (simp add: I\<^sub>1_def Some, rule impI, (erule conjE)+, cases v,
      (((erule disjE)+)?, simp)+)
  qed
qed

text \<open>
\null

In what follows, the insecurity of process @{term "P\<^sub>1 ; Q"} is demonstrated by proving that event
list @{term "[Some a, Some b]"} is a trace of the process, whereas @{term "[Some b]"} is not.

\null
\<close>

lemma traces_comp_1:
 "traces (P\<^sub>1 ; Q) = Domain (seq_comp_failures P\<^sub>1 Q)"
by (subst seq_comp_traces, rule seq_implies_weakly_seq, rule sequential_fst_1, simp)

lemma ref_union_closed_comp_1:
 "ref_union_closed (P\<^sub>1 ; Q)"
proof (rule seq_comp_ref_union_closed, rule seq_implies_weakly_seq,
 rule sequential_fst_1, rule ref_union_closed_fst_1)
qed (rule d_implies_ruc, subst Q_def, rule ts_process_d, rule trace_set_snd)

lemma not_secure_comp_1_aux_aux_1:
 "(xs, X) \<in> seq_comp_failures P\<^sub>1 Q \<Longrightarrow> xs \<noteq> [Some b]"
proof (rule notI, erule rev_mp, erule seq_comp_failures.induct, (rule_tac [!] impI)+,
 simp_all add: P\<^sub>1_def Q_def sentences_def)
qed (simp_all add: failures_fst_1 traces_fst_1)

lemma not_secure_comp_1_aux_1:
 "[Some b] \<notin> traces (P\<^sub>1 ; Q)"
proof (simp add: traces_comp_1 Domain_iff, rule allI, rule notI)
qed (drule not_secure_comp_1_aux_aux_1, simp)

lemma not_secure_comp_1_aux_2:
 "[Some a, Some b] \<in> traces (P\<^sub>1 ; Q)"
proof (simp add: traces_comp_1 Domain_iff, rule exI [where x = "{}"])
  have "[Some a] \<in> sentences P\<^sub>1"
   by (simp add: P\<^sub>1_def sentences_def traces_fst_1)
  moreover have "([Some b], {}) \<in> failures Q"
   by (simp add: Q_def failures_snd)
  moreover have "[Some b] \<noteq> []"
   by simp
  ultimately have "([Some a] @ [Some b], {}) \<in> seq_comp_failures P\<^sub>1 Q"
   by (rule SCF_R3)
  thus "([Some a, Some b], {}) \<in> seq_comp_failures P\<^sub>1 Q"
   by simp
qed

lemma not_secure_comp_1:
 "\<not> secure (P\<^sub>1 ; Q) I\<^sub>1 id"
proof (subst ipurge_unwinding, rule ref_union_closed_comp_1, simp
 add: fc_equals_wfc_rel_ipurge [symmetric] future_consistent_def rel_ipurge_def
 del: disj_not1, rule exI [where x = "Some b"], rule exI [where x = "[]"], rule conjI)
  show "[] \<in> traces (P\<^sub>1 ; Q)"
   by (rule failures_traces [where X = "{}"], rule process_rule_1)
next
  show "\<exists>ys. ys \<in> traces (P\<^sub>1 ; Q) \<and>
    ipurge_tr_rev I\<^sub>1 id (Some b) [] = ipurge_tr_rev I\<^sub>1 id (Some b) ys \<and>
    (next_dom_events (P\<^sub>1 ; Q) id (Some b) [] \<noteq>
       next_dom_events (P\<^sub>1 ; Q) id (Some b) ys \<or>
     ref_dom_events (P\<^sub>1 ; Q) id (Some b) [] \<noteq>
       ref_dom_events (P\<^sub>1 ; Q) id (Some b) ys)"
  proof (rule exI [where x = "[Some a]"], rule conjI, rule_tac [2] conjI,
   rule_tac [3] disjI1)
    have "[Some a] @ [Some b] \<in> traces (P\<^sub>1 ; Q)"
     by (simp add: not_secure_comp_1_aux_2)
    thus "[Some a] \<in> traces (P\<^sub>1 ; Q)"
     by (rule process_rule_2_traces)
  next
    show "ipurge_tr_rev I\<^sub>1 id (Some b) [] = ipurge_tr_rev I\<^sub>1 id (Some b) [Some a]"
     by (simp add: I\<^sub>1_def)
  next
    show
     "next_dom_events (P\<^sub>1 ; Q) id (Some b) [] \<noteq>
      next_dom_events (P\<^sub>1 ; Q) id (Some b) [Some a]"
    proof (simp add: next_dom_events_def next_events_def set_eq_iff,
     rule exI [where x = "Some b"], simp)
    qed (simp add: not_secure_comp_1_aux_1 not_secure_comp_1_aux_2)
  qed
qed

text \<open>
\null

Here below, the previous results are used to show that constants @{term I\<^sub>1}, @{term P\<^sub>1}, @{term Q},
and @{term id} indeed constitute a counterexample to the statement obtained by removing termination
security from the assumptions of the security conservation theorem.

\null
\<close>

lemma counterexample_1:
 "\<not> (ref_union_closed P\<^sub>1 \<and>
     sequential P\<^sub>1 \<and>
     secure P\<^sub>1 I\<^sub>1 id \<and>
     secure Q I\<^sub>1 id \<longrightarrow>
   secure (P\<^sub>1 ; Q) I\<^sub>1 id)"
proof (simp, simp only: conj_assoc [symmetric], (rule conjI)+)
  show "ref_union_closed P\<^sub>1"
   by (rule ref_union_closed_fst_1)
next
  show "sequential P\<^sub>1"
   by (rule sequential_fst_1)
next
  show "secure P\<^sub>1 I\<^sub>1 id"
   by (rule secure_fst_1)
next
  show "secure Q I\<^sub>1 id"
   by (rule secure_snd_1)
next
  show "\<not> secure (P\<^sub>1 ; Q) I\<^sub>1 id"
   by (rule not_secure_comp_1)
qed


subsection "Necessity of process sequentiality"

text \<open>
The reason why the conservation of noninterference security under sequential composition requires
the first input process to satisfy predicate @{term sequential}, instead of the more permissive
predicate @{term weakly_sequential}, is that the possibility for the first process to engage in
events alternative to successful termination entails the possibility for the resulting process to
engage in events alternative to the initial ones of the second process. Namely, the resulting
process would admit some state in which events of the first process can occur in alternative to
events of the second process. But neither process, though being secure on its own, will in general
be prepared to handle securely the alternative events added by the other process. Therefore, the
first process must not admit alternatives to successful termination, which is exactly what predicate
@{term sequential} states in addition to @{term weakly_sequential}.

A counterexample showing the necessity of this assumption can then be constructed by defining a
reflexive policy @{term I\<^sub>2} that does not allow event @{term "Some b"} to affect @{term "Some a"},
and a deterministic process @{term P\<^sub>2} that can engage in @{term "Some a"} in alternative to
@{term None}. The resulting process @{term "P\<^sub>2 ; Q"} will number both @{term "[Some b]"} and
@{term "[Some a]"}, but not @{term "[Some b, Some a]"}, among its traces, so that event
@{term "Some b"} affects the occurrence of event @{term "Some a"} in contrast with policy
@{term I\<^sub>2}, viz. @{term "P\<^sub>2 ; Q"} is not secure with respect to @{term I\<^sub>2}.

Here below are the definitions of constants @{term I\<^sub>2} and @{term P\<^sub>2}, followed by few useful lemmas
on process @{term P\<^sub>2}.

\null
\<close>

definition I\<^sub>2 :: "(event option \<times> event option) set" where
"I\<^sub>2 \<equiv> {(None, Some a)}\<^sup>="

definition P\<^sub>2 :: "event option process" where
"P\<^sub>2 \<equiv> ts_process {[], [None], [Some a], [Some a, None]}"

lemma trace_set_fst_2:
 "trace_set {[], [None], [Some a], [Some a, None]}"
by (simp add: trace_set_def)

lemmas failures_fst_2 = ts_process_failures [OF trace_set_fst_2]

lemmas traces_fst_2 = ts_process_traces [OF trace_set_fst_2]

lemmas next_events_fst_2 = ts_process_next_events [OF trace_set_fst_2]

lemmas unwinding_fst_2 = ts_ipurge_unwinding [OF trace_set_fst_2]

text \<open>
\null

Here below is the proof that process @{term P\<^sub>2} does not satisfy predicate @{term sequential}, but
rather predicate @{term weakly_sequential} only, whereas the remaining assumptions of the security
conservation theorem keep being satisfied. For the sake of simplicity, the identity function is used
as event-domain map.

\null
\<close>

lemma secure_termination_2:
 "secure_termination I\<^sub>2 id"
by (simp add: secure_termination_def I\<^sub>2_def)

lemma ref_union_closed_fst_2:
 "ref_union_closed P\<^sub>2"
by (rule d_implies_ruc, subst P\<^sub>2_def, rule ts_process_d, rule trace_set_fst_2)

lemma weakly_sequential_fst_2:
 "weakly_sequential P\<^sub>2"
by (simp add: weakly_sequential_def P\<^sub>2_def traces_fst_2)

lemma not_sequential_fst_2:
 "\<not> sequential P\<^sub>2"
proof (simp add: sequential_def, rule disjI2, rule bexI [where x = "[]"])
  show "next_events P\<^sub>2 [] \<noteq> {None}"
  proof (rule notI, drule eqset_imp_iff [where x = "Some a"], simp)
  qed (simp add: P\<^sub>2_def next_events_fst_2)
next
  show "[] \<in> sentences P\<^sub>2"
   by (simp add: sentences_def P\<^sub>2_def traces_fst_2)
qed

lemma secure_fst_2:
 "secure P\<^sub>2 I\<^sub>2 id"
proof (simp add: P\<^sub>2_def unwinding_fst_2 dfc_equals_dwfc_rel_ipurge [symmetric]
 d_future_consistent_def rel_ipurge_def traces_fst_2, (rule allI)+)
  fix u xs ys
  show
   "(xs = [] \<or> xs = [None] \<or> xs = [Some a] \<or> xs = [Some a, None]) \<and>
    (ys = [] \<or> ys = [None] \<or> ys = [Some a] \<or> ys = [Some a, None]) \<and>
    ipurge_tr_rev I\<^sub>2 id u xs = ipurge_tr_rev I\<^sub>2 id u ys \<longrightarrow>
      next_dom_events (ts_process {[], [None], [Some a], [Some a, None]}) id u xs =
      next_dom_events (ts_process {[], [None], [Some a], [Some a, None]}) id u ys"
  proof (simp add: next_dom_events_def next_events_fst_2, cases u)
    case None
    show
     "(xs = [] \<or> xs = [None] \<or> xs = [Some a] \<or> xs = [Some a, None]) \<and>
      (ys = [] \<or> ys = [None] \<or> ys = [Some a] \<or> ys = [Some a, None]) \<and>
      ipurge_tr_rev I\<^sub>2 id u xs = ipurge_tr_rev I\<^sub>2 id u ys \<longrightarrow>
        {x. u = x \<and> (xs = [] \<and> x = None \<or> xs = [] \<and> x = Some a \<or>
          xs = [Some a] \<and> x = None)} =
        {x. u = x \<and> (ys = [] \<and> x = None \<or> ys = [] \<and> x = Some a \<or>
          ys = [Some a] \<and> x = None)}"
     by (simp add: I\<^sub>2_def None, rule impI, (erule conjE)+,
      (((erule disjE)+)?, simp, blast?)+)
  next
    case (Some v)
    show
     "(xs = [] \<or> xs = [None] \<or> xs = [Some a] \<or> xs = [Some a, None]) \<and>
      (ys = [] \<or> ys = [None] \<or> ys = [Some a] \<or> ys = [Some a, None]) \<and>
      ipurge_tr_rev I\<^sub>2 id u xs = ipurge_tr_rev I\<^sub>2 id u ys \<longrightarrow>
        {x. u = x \<and> (xs = [] \<and> x = None \<or> xs = [] \<and> x = Some a \<or>
          xs = [Some a] \<and> x = None)} =
        {x. u = x \<and> (ys = [] \<and> x = None \<or> ys = [] \<and> x = Some a \<or>
          ys = [Some a] \<and> x = None)}"
     by (simp add: I\<^sub>2_def Some, rule impI, (erule conjE)+, cases v,
      (((erule disjE)+)?, simp, blast?)+)
  qed
qed

lemma secure_snd_2:
 "secure Q I\<^sub>2 id"
proof (simp add: Q_def unwinding_snd dfc_equals_dwfc_rel_ipurge [symmetric]
 d_future_consistent_def rel_ipurge_def traces_snd, (rule allI)+)
  fix u xs ys
  show
   "(xs = [] \<or> xs = [Some b]) \<and>
    (ys = [] \<or> ys = [Some b]) \<and>
    ipurge_tr_rev I\<^sub>2 id u xs = ipurge_tr_rev I\<^sub>2 id u ys \<longrightarrow>
      next_dom_events (ts_process {[], [Some b]}) id u xs =
      next_dom_events (ts_process {[], [Some b]}) id u ys"
  proof (simp add: next_dom_events_def next_events_snd, cases u)
    case None
    show
     "(xs = [] \<or> xs = [Some b]) \<and>
      (ys = [] \<or> ys = [Some b]) \<and>
      ipurge_tr_rev I\<^sub>2 id u xs = ipurge_tr_rev I\<^sub>2 id u ys \<longrightarrow>
        {x. u = x \<and> xs = [] \<and> x = Some b} = {x. u = x \<and> ys = [] \<and> x = Some b}"
     by (simp add: None, rule impI, (erule conjE)+,
      (((erule disjE)+)?, simp)+)
  next
    case (Some v)
    show
     "(xs = [] \<or> xs = [Some b]) \<and>
      (ys = [] \<or> ys = [Some b]) \<and>
      ipurge_tr_rev I\<^sub>2 id u xs = ipurge_tr_rev I\<^sub>2 id u ys \<longrightarrow>
        {x. u = x \<and> xs = [] \<and> x = Some b} = {x. u = x \<and> ys = [] \<and> x = Some b}"
     by (simp add: I\<^sub>2_def Some, rule impI, (erule conjE)+, cases v,
      (((erule disjE)+)?, simp)+)
  qed
qed

text \<open>
\null

In what follows, the insecurity of process @{term "P\<^sub>2 ; Q"} is demonstrated by proving that event
lists @{term "[Some b]"} and @{term "[Some a]"} are traces of the process, whereas
@{term "[Some b, Some a]"} is not.

\null
\<close>

lemma traces_comp_2:
 "traces (P\<^sub>2 ; Q) = Domain (seq_comp_failures P\<^sub>2 Q)"
by (subst seq_comp_traces, rule weakly_sequential_fst_2, simp)

lemma ref_union_closed_comp_2:
 "ref_union_closed (P\<^sub>2 ; Q)"
proof (rule seq_comp_ref_union_closed, rule weakly_sequential_fst_2,
 rule ref_union_closed_fst_2)
qed (rule d_implies_ruc, subst Q_def, rule ts_process_d, rule trace_set_snd)

lemma not_secure_comp_2_aux_aux_1:
 "(xs, X) \<in> seq_comp_failures P\<^sub>2 Q \<Longrightarrow> xs \<noteq> [Some b, Some a]"
proof (rule notI, erule rev_mp, erule seq_comp_failures.induct, (rule_tac [!] impI)+,
 simp_all add: P\<^sub>2_def Q_def sentences_def)
qed (simp_all add: failures_fst_2 traces_fst_2 failures_snd)

lemma not_secure_comp_2_aux_1:
 "[Some b, Some a] \<notin> traces (P\<^sub>2 ; Q)"
proof (simp add: traces_comp_2 Domain_iff, rule allI, rule notI)
qed (drule not_secure_comp_2_aux_aux_1, simp)

lemma not_secure_comp_2_aux_2:
 "[Some a] \<in> traces (P\<^sub>2 ; Q)"
proof (simp add: traces_comp_2 Domain_iff, rule exI [where x = "{}"])
  have "[Some a] \<in> sentences P\<^sub>2"
   by (simp add: P\<^sub>2_def sentences_def traces_fst_2)
  moreover have "([Some a], {}) \<in> failures P\<^sub>2"
   by (simp add: P\<^sub>2_def failures_fst_2)
  moreover have "([], {}) \<in> failures Q"
   by (simp add: Q_def failures_snd)
  ultimately have "([Some a], insert None {} \<inter> {}) \<in> seq_comp_failures P\<^sub>2 Q"
   by (rule SCF_R2)
  thus "([Some a], {}) \<in> seq_comp_failures P\<^sub>2 Q"
   by simp
qed

lemma not_secure_comp_2_aux_3:
 "[Some b] \<in> traces (P\<^sub>2 ; Q)"
proof (simp add: traces_comp_2 Domain_iff, rule exI [where x = "{}"])
  have "[] \<in> sentences P\<^sub>2"
   by (simp add: P\<^sub>2_def sentences_def traces_fst_2)
  moreover have "([Some b], {}) \<in> failures Q"
   by (simp add: Q_def failures_snd)
  moreover have "[Some b] \<noteq> []"
   by simp
  ultimately have "([] @ [Some b], {}) \<in> seq_comp_failures P\<^sub>2 Q"
   by (rule SCF_R3)
  thus "([Some b], {}) \<in> seq_comp_failures P\<^sub>2 Q"
   by simp
qed

lemma not_secure_comp_2:
 "\<not> secure (P\<^sub>2 ; Q) I\<^sub>2 id"
proof (subst ipurge_unwinding, rule ref_union_closed_comp_2, simp
 add: fc_equals_wfc_rel_ipurge [symmetric] future_consistent_def rel_ipurge_def
 del: disj_not1, rule exI [where x = "Some a"], rule exI [where x = "[]"], rule conjI)
  show "[] \<in> traces (P\<^sub>2 ; Q)"
   by (rule failures_traces [where X = "{}"], rule process_rule_1)
next
  show "\<exists>ys. ys \<in> traces (P\<^sub>2 ; Q) \<and>
    ipurge_tr_rev I\<^sub>2 id (Some a) [] = ipurge_tr_rev I\<^sub>2 id (Some a) ys \<and>
    (next_dom_events (P\<^sub>2 ; Q) id (Some a) [] \<noteq>
       next_dom_events (P\<^sub>2 ; Q) id (Some a) ys \<or>
     ref_dom_events (P\<^sub>2 ; Q) id (Some a) [] \<noteq>
       ref_dom_events (P\<^sub>2 ; Q) id (Some a) ys)"
  proof (rule exI [where x = "[Some b]"], rule conjI, rule_tac [2] conjI,
   rule_tac [3] disjI1)
    show "[Some b] \<in> traces (P\<^sub>2 ; Q)"
     by (rule not_secure_comp_2_aux_3)
  next
    show "ipurge_tr_rev I\<^sub>2 id (Some a) [] = ipurge_tr_rev I\<^sub>2 id (Some a) [Some b]"
     by (simp add: I\<^sub>2_def)
  next
    show
     "next_dom_events (P\<^sub>2 ; Q) id (Some a) [] \<noteq>
      next_dom_events (P\<^sub>2 ; Q) id (Some a) [Some b]"
    proof (simp add: next_dom_events_def next_events_def set_eq_iff,
     rule exI [where x = "Some a"], simp)
    qed (simp add: not_secure_comp_2_aux_1 not_secure_comp_2_aux_2)
  qed
qed

text \<open>
\null

Here below, the previous results are used to show that constants @{term I\<^sub>2}, @{term P\<^sub>2}, @{term Q},
and @{term id} indeed constitute a counterexample to the statement obtained by replacing process
sequentiality with weak sequentiality in the assumptions of the security conservation theorem.

\null
\<close>

lemma counterexample_2:
 "\<not> (secure_termination I\<^sub>2 id \<and>
     ref_union_closed P\<^sub>2 \<and>
     weakly_sequential P\<^sub>2 \<and>
     secure P\<^sub>2 I\<^sub>2 id \<and>
     secure Q I\<^sub>2 id \<longrightarrow>
   secure (P\<^sub>2 ; Q) I\<^sub>2 id)"
proof (simp, simp only: conj_assoc [symmetric], (rule conjI)+)
  show "secure_termination I\<^sub>2 id"
   by (rule secure_termination_2)
next
  show "ref_union_closed P\<^sub>2"
   by (rule ref_union_closed_fst_2)
next
  show "weakly_sequential P\<^sub>2"
   by (rule weakly_sequential_fst_2)
next
  show "secure P\<^sub>2 I\<^sub>2 id"
   by (rule secure_fst_2)
next
  show "secure Q I\<^sub>2 id"
   by (rule secure_snd_2)
next
  show "\<not> secure (P\<^sub>2 ; Q) I\<^sub>2 id"
   by (rule not_secure_comp_2)
qed

end
