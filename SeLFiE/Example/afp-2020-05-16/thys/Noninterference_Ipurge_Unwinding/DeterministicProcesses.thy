(*  Title:       The Ipurge Unwinding Theorem for CSP Noninterference Security
    Author:      Pasquale Noce
                 Security Certification Specialist at Arjo Systems - Gep S.p.A.
                 pasquale dot noce dot lavoro at gmail dot com
                 pasquale dot noce at arjowiggins-it dot com
*)

section "The Ipurge Unwinding Theorem for deterministic and trace set processes"

theory DeterministicProcesses
imports IpurgeUnwinding
begin

text \<open>
\null

In accordance with Hoare's formal definition of deterministic processes \cite{R3}, this section
shows that a process is deterministic just in case it is a \emph{trace set process}, i.e. it may be
identified by means of a trace set alone, matching the set of its traces, in place of a
failures-divergences pair. Then, variants of the Ipurge Unwinding Theorem are proven for
deterministic processes and trace set processes.
\<close>


subsection "Deterministic processes"

text \<open>
Here below are the definitions of predicates \<open>d_future_consistent\<close> and
\<open>d_weakly_future_consistent\<close>, which are variants of predicates @{term future_consistent} and
@{term weakly_future_consistent} meant for applying to deterministic processes. In some detail,
being deterministic processes such that refused events are completely specified by accepted events
(cf. \cite{R3}, \cite{R1}), the new predicates are such that their truth values can be determined
by just considering the accepted events of the process taken as input.

Then, it is proven that these predicates are characterized by the same connection as that of their
general-purpose counterparts, viz. \<open>d_future_consistent\<close> implies
\<open>d_weakly_future_consistent\<close>, and they are equivalent for domain-relation map
@{term rel_ipurge}. Finally, the predicates are shown to be equivalent to their general-purpose
counterparts in the case of a deterministic process.

\null
\<close>

definition d_future_consistent ::
 "'a process \<Rightarrow> ('a \<Rightarrow> 'd) \<Rightarrow> ('a, 'd) dom_rel_map \<Rightarrow> bool" where
"d_future_consistent P D R \<equiv>
  \<forall>u \<in> range D. \<forall>xs ys. (xs, ys) \<in> R u \<longrightarrow>
    (xs \<in> traces P) = (ys \<in> traces P) \<and>
    next_dom_events P D u xs = next_dom_events P D u ys"

definition d_weakly_future_consistent ::
 "'a process \<Rightarrow> ('d \<times> 'd) set \<Rightarrow> ('a \<Rightarrow> 'd) \<Rightarrow> ('a, 'd) dom_rel_map \<Rightarrow> bool" where
"d_weakly_future_consistent P I D R \<equiv>
  \<forall>u \<in> range D \<inter> (-I) `` range D. \<forall>xs ys. (xs, ys) \<in> R u \<longrightarrow>
    (xs \<in> traces P) = (ys \<in> traces P) \<and>
    next_dom_events P D u xs = next_dom_events P D u ys"

lemma dfc_implies_dwfc:
 "d_future_consistent P D R \<Longrightarrow> d_weakly_future_consistent P I D R"
by (simp only: d_future_consistent_def d_weakly_future_consistent_def, blast)

lemma dfc_equals_dwfc_rel_ipurge:
 "d_future_consistent P D (rel_ipurge P I D) =
  d_weakly_future_consistent P I D (rel_ipurge P I D)"
proof (rule iffI, erule dfc_implies_dwfc,
 simp only: d_future_consistent_def d_weakly_future_consistent_def,
 rule ballI, (rule allI)+, rule impI)
  fix u xs ys
  assume
    A: "\<forall>u \<in> range D \<inter> (-I) `` range D. \<forall>xs ys. (xs, ys) \<in> rel_ipurge P I D u \<longrightarrow>
      (xs \<in> traces P) = (ys \<in> traces P) \<and>
      next_dom_events P D u xs = next_dom_events P D u ys" and
    B: "u \<in> range D" and
    C: "(xs, ys) \<in> rel_ipurge P I D u"
  show "(xs \<in> traces P) = (ys \<in> traces P) \<and>
    next_dom_events P D u xs = next_dom_events P D u ys"
  proof (cases "u \<in> range D \<inter> (-I) `` range D")
    case True
    with A have "\<forall>xs ys. (xs, ys) \<in> rel_ipurge P I D u \<longrightarrow>
      (xs \<in> traces P) = (ys \<in> traces P) \<and>
      next_dom_events P D u xs = next_dom_events P D u ys" ..
    hence "(xs, ys) \<in> rel_ipurge P I D u \<longrightarrow>
      (xs \<in> traces P) = (ys \<in> traces P) \<and>
      next_dom_events P D u xs = next_dom_events P D u ys"
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

lemma d_fc_equals_dfc:
  assumes A: "deterministic P"
  shows "future_consistent P D R = d_future_consistent P D R"
proof (rule iffI, simp_all only: d_future_consistent_def,
 rule ballI, (rule allI)+, rule impI, rule conjI, rule fc_traces, assumption+,
 simp_all add: future_consistent_def del: ball_simps)
  assume B: "\<forall>u \<in> range D. \<forall>xs ys. (xs, ys) \<in> R u \<longrightarrow>
    (xs \<in> traces P) = (ys \<in> traces P) \<and>
    next_dom_events P D u xs = next_dom_events P D u ys"
  show "\<forall>u \<in> range D. \<forall>xs ys. (xs, ys) \<in> R u \<longrightarrow>
    ref_dom_events P D u xs = ref_dom_events P D u ys"
  proof (rule ballI, (rule allI)+, rule impI,
   simp add: ref_dom_events_def set_eq_iff, rule allI)
    fix u xs ys x
    assume "u \<in> range D"
    with B have "\<forall>xs ys. (xs, ys) \<in> R u \<longrightarrow>
      (xs \<in> traces P) = (ys \<in> traces P) \<and>
      next_dom_events P D u xs = next_dom_events P D u ys" ..
    hence "(xs, ys) \<in> R u \<longrightarrow>
      (xs \<in> traces P) = (ys \<in> traces P) \<and>
      next_dom_events P D u xs = next_dom_events P D u ys"
     by blast
    moreover assume "(xs, ys) \<in> R u"
    ultimately have C: "(xs \<in> traces P) = (ys \<in> traces P) \<and>
      next_dom_events P D u xs = next_dom_events P D u ys" ..
    show "(u = D x \<and> {x} \<in> refusals P xs) = (u = D x \<and> {x} \<in> refusals P ys)"
    proof (cases "u = D x", simp_all, cases "xs \<in> traces P")
      assume D: "u = D x" and E: "xs \<in> traces P"
      have
        A': "\<forall>xs \<in> traces P. \<forall>X. X \<in> refusals P xs = (X \<inter> next_events P xs = {})"
       using A by (simp add: deterministic_def)
      hence "\<forall>X. X \<in> refusals P xs = (X \<inter> next_events P xs = {})" using E ..
      hence "{x} \<in> refusals P xs = ({x} \<inter> next_events P xs = {})" ..
      moreover have "ys \<in> traces P" using C and E by simp
      with A' have "\<forall>X. X \<in> refusals P ys = (X \<inter> next_events P ys = {})" ..
      hence "{x} \<in> refusals P ys = ({x} \<inter> next_events P ys = {})" ..
      moreover have "{x} \<inter> next_events P xs = {x} \<inter> next_events P ys"
      proof (simp add: set_eq_iff, rule allI, rule iffI, erule_tac [!] conjE, simp_all)
        assume "x \<in> next_events P xs"
        hence "x \<in> next_dom_events P D u xs" using D by (simp add: next_dom_events_def)
        hence "x \<in> next_dom_events P D u ys" using C by simp
        thus "x \<in> next_events P ys" by (simp add: next_dom_events_def)
      next
        assume "x \<in> next_events P ys"
        hence "x \<in> next_dom_events P D u ys" using D by (simp add: next_dom_events_def)
        hence "x \<in> next_dom_events P D u xs" using C by simp
        thus "x \<in> next_events P xs" by (simp add: next_dom_events_def)
      qed
      ultimately show "({x} \<in> refusals P xs) = ({x} \<in> refusals P ys)" by simp
    next
      assume D: "xs \<notin> traces P"
      hence "\<forall>X. (xs, X) \<notin> failures P" by (simp add: traces_def Domain_iff)
      hence "refusals P xs = {}" by (rule_tac equals0I, simp add: refusals_def)
      moreover have "ys \<notin> traces P" using C and D by simp
      hence "\<forall>X. (ys, X) \<notin> failures P" by (simp add: traces_def Domain_iff)
      hence "refusals P ys = {}" by (rule_tac equals0I, simp add: refusals_def)
      ultimately show "({x} \<in> refusals P xs) = ({x} \<in> refusals P ys)" by simp
    qed
  qed
qed

lemma d_wfc_equals_dwfc:
  assumes A: "deterministic P"
  shows "weakly_future_consistent P I D R = d_weakly_future_consistent P I D R"
proof (rule iffI, simp_all only: d_weakly_future_consistent_def,
 rule ballI, (rule allI)+, rule impI, rule conjI, rule wfc_traces, assumption+,
 simp_all add: weakly_future_consistent_def del: ball_simps)
  assume B: "\<forall>u \<in> range D \<inter> (- I) `` range D. \<forall>xs ys. (xs, ys) \<in> R u \<longrightarrow>
    (xs \<in> traces P) = (ys \<in> traces P) \<and>
    next_dom_events P D u xs = next_dom_events P D u ys"
  show "\<forall>u \<in> range D \<inter> (- I) `` range D. \<forall>xs ys. (xs, ys) \<in> R u \<longrightarrow>
    ref_dom_events P D u xs = ref_dom_events P D u ys"
  proof (rule ballI, (rule allI)+, rule impI,
   simp (no_asm_simp) add: ref_dom_events_def set_eq_iff, rule allI)
    fix u xs ys x
    assume "u \<in> range D \<inter> (- I) `` range D"
    with B have "\<forall>xs ys. (xs, ys) \<in> R u \<longrightarrow>
      (xs \<in> traces P) = (ys \<in> traces P) \<and>
      next_dom_events P D u xs = next_dom_events P D u ys" ..
    hence "(xs, ys) \<in> R u \<longrightarrow>
      (xs \<in> traces P) = (ys \<in> traces P) \<and>
      next_dom_events P D u xs = next_dom_events P D u ys"
     by blast
    moreover assume "(xs, ys) \<in> R u"
    ultimately have C: "(xs \<in> traces P) = (ys \<in> traces P) \<and>
      next_dom_events P D u xs = next_dom_events P D u ys" ..
    show "(u = D x \<and> {x} \<in> refusals P xs) = (u = D x \<and> {x} \<in> refusals P ys)"
    proof (cases "u = D x", simp_all, cases "xs \<in> traces P")
      assume D: "u = D x" and E: "xs \<in> traces P"
      have A': "\<forall>xs \<in> traces P. \<forall>X.
        X \<in> refusals P xs = (X \<inter> next_events P xs = {})"
       using A by (simp add: deterministic_def)
      hence "\<forall>X. X \<in> refusals P xs = (X \<inter> next_events P xs = {})" using E ..
      hence "{x} \<in> refusals P xs = ({x} \<inter> next_events P xs = {})" ..
      moreover have "ys \<in> traces P" using C and E by simp
      with A' have "\<forall>X. X \<in> refusals P ys = (X \<inter> next_events P ys = {})" ..
      hence "{x} \<in> refusals P ys = ({x} \<inter> next_events P ys = {})" ..
      moreover have "{x} \<inter> next_events P xs = {x} \<inter> next_events P ys"
      proof (simp add: set_eq_iff, rule allI, rule iffI, erule_tac [!] conjE, simp_all)
        assume "x \<in> next_events P xs"
        hence "x \<in> next_dom_events P D u xs" using D by (simp add: next_dom_events_def)
        hence "x \<in> next_dom_events P D u ys" using C by simp
        thus "x \<in> next_events P ys" by (simp add: next_dom_events_def)
      next
        assume "x \<in> next_events P ys"
        hence "x \<in> next_dom_events P D u ys" using D by (simp add: next_dom_events_def)
        hence "x \<in> next_dom_events P D u xs" using C by simp
        thus "x \<in> next_events P xs" by (simp add: next_dom_events_def)
      qed
      ultimately show "({x} \<in> refusals P xs) = ({x} \<in> refusals P ys)" by simp
    next
      assume D: "xs \<notin> traces P"
      hence "\<forall>X. (xs, X) \<notin> failures P" by (simp add: traces_def Domain_iff)
      hence "refusals P xs = {}" by (rule_tac equals0I, simp add: refusals_def)
      moreover have "ys \<notin> traces P" using C and D by simp
      hence "\<forall>X. (ys, X) \<notin> failures P" by (simp add: traces_def Domain_iff)
      hence "refusals P ys = {}" by (rule_tac equals0I, simp add: refusals_def)
      ultimately show "({x} \<in> refusals P xs) = ({x} \<in> refusals P ys)" by simp
    qed
  qed
qed

text \<open>
\null

Here below is the proof of a variant of the Ipurge Unwinding Theorem applying to deterministic
processes. Unsurprisingly, its enunciation contains predicate @{term d_weakly_future_consistent} in
place of @{term weakly_future_consistent}. Furthermore, the assumption that the process be refusals
union closed is replaced by the assumption that it be deterministic, since the former property is
shown to be entailed by the latter.

\null
\<close>

lemma d_implies_ruc:
  assumes A: "deterministic P"
  shows "ref_union_closed P"
proof (subst ref_union_closed_def, (rule allI)+, (rule impI)+, erule exE)
  fix xs A X
  have "\<forall>xs \<in> traces P. \<forall>X. X \<in> refusals P xs = (X \<inter> next_events P xs = {})"
   using A by (simp add: deterministic_def)
  moreover assume B: "\<forall>X \<in> A. (xs, X) \<in> failures P" and "X \<in> A"
  hence "(xs, X) \<in> failures P" ..
  hence "xs \<in> traces P" by (rule failures_traces)
  ultimately have C: "\<forall>X. X \<in> refusals P xs = (X \<inter> next_events P xs = {})" ..
  have D: "\<forall>X \<in> A. X \<inter> next_events P xs = {}"
  proof
    fix X
    assume "X \<in> A"
    with B have "(xs, X) \<in> failures P" ..
    hence "X \<in> refusals P xs" by (simp add: refusals_def)
    thus "X \<inter> next_events P xs = {}" using C by simp
  qed
  have "(\<Union>X \<in> A. X) \<in> refusals P xs = ((\<Union>X \<in> A. X) \<inter> next_events P xs = {})"
   using C ..
  hence E: "(xs, \<Union>X \<in> A. X) \<in> failures P =
    ((\<Union>X \<in> A. X) \<inter> next_events P xs = {})"
   by (simp add: refusals_def)
  show "(xs, \<Union>X \<in> A. X) \<in> failures P"
  proof (rule ssubst [OF E], rule equals0I, erule IntE, erule UN_E)
    fix x X
    assume "X \<in> A"
    with D have "X \<inter> next_events P xs = {}" ..
    moreover assume "x \<in> X" and "x \<in> next_events P xs"
    hence "x \<in> X \<inter> next_events P xs" ..
    hence "\<exists>x. x \<in> X \<inter> next_events P xs" ..
    hence "X \<inter> next_events P xs \<noteq> {}" by (subst ex_in_conv [symmetric])
    ultimately show False by contradiction
  qed
qed

theorem d_ipurge_unwinding:
  assumes A: "deterministic P"
  shows "secure P I D = d_weakly_future_consistent P I D (rel_ipurge P I D)"
proof (insert d_wfc_equals_dwfc [of P I D "rel_ipurge P I D", OF A], erule subst)
qed (insert d_implies_ruc [OF A], rule ipurge_unwinding)


subsection "Trace set processes"

text \<open>
In \cite{R3}, section 2.8, Hoare formulates a simplified definition of a deterministic process,
identified with a \emph{trace set}, i.e. a set of event lists containing the empty list and any
prefix of each of its elements. Of course, this is consistent with the definition of determinism
applying to processes identified with failures-divergences pairs, which implies that their refusals
are completely specified by their traces (cf. \cite{R3}, \cite{R1}).

Here below are the definitions of a function \<open>ts_process\<close>, converting the input set of lists
into a process, and a predicate \<open>trace_set\<close>, returning @{term True} just in case the input set
of lists has the aforesaid properties. An analysis is then conducted about the output of the
functions defined in \cite{R1}, section 1.1, when acting on a \emph{trace set process}, i.e. a
process that may be expressed as \<open>ts_process T\<close> where \<open>trace_set T\<close> matches
@{term True}.

\null
\<close>

definition ts_process :: "'a list set \<Rightarrow> 'a process" where
"ts_process T \<equiv> Abs_process ({(xs, X). xs \<in> T \<and> (\<forall>x \<in> X. xs @ [x] \<notin> T)}, {})"

definition trace_set :: "'a list set \<Rightarrow> bool" where
"trace_set T \<equiv> [] \<in> T \<and> (\<forall>xs x. xs @ [x] \<in> T \<longrightarrow> xs \<in> T)"

lemma ts_process_rep:
  assumes A: "trace_set T"
  shows "Rep_process (ts_process T) =
    ({(xs, X). xs \<in> T \<and> (\<forall>x \<in> X. xs @ [x] \<notin> T)}, {})"
proof (subst ts_process_def, rule Abs_process_inverse, simp add: process_set_def,
 (subst conj_assoc [symmetric])+, (rule conjI)+, simp_all add:
 process_prop_1_def
 process_prop_2_def
 process_prop_3_def
 process_prop_4_def
 process_prop_5_def
 process_prop_6_def)
  show "[] \<in> T" using A by (simp add: trace_set_def)
next
  show "\<forall>xs. (\<exists>x. xs @ [x] \<in> T \<and> (\<exists>X. \<forall>x' \<in> X. xs @ [x, x'] \<notin> T)) \<longrightarrow> xs \<in> T"
  proof (rule allI, rule impI, erule exE, erule conjE)
    fix xs x
    have "\<forall>xs x. xs @ [x] \<in> T \<longrightarrow> xs \<in> T" using A by (simp add: trace_set_def)
    hence "xs @ [x] \<in> T \<longrightarrow> xs \<in> T" by blast
    moreover assume "xs @ [x] \<in> T"
    ultimately show "xs \<in> T" ..
  qed
next
  show "\<forall>xs X. xs \<in> T \<and> (\<exists>Y. (\<forall>x \<in> Y. xs @ [x] \<notin> T) \<and> X \<subseteq> Y) \<longrightarrow>
    (\<forall>x \<in> X. xs @ [x] \<notin> T)"
  proof ((rule allI)+, rule impI, (erule conjE, (erule exE)?)+, rule ballI)
    fix xs x X Y
    assume "\<forall>x \<in> Y. xs @ [x] \<notin> T"
    moreover assume "X \<subseteq> Y" and "x \<in> X"
    hence "x \<in> Y" ..
    ultimately show "xs @ [x] \<notin> T" ..
  qed
qed

lemma ts_process_failures:
 "trace_set T \<Longrightarrow>
  failures (ts_process T) = {(xs, X). xs \<in> T \<and> (\<forall>x \<in> X. xs @ [x] \<notin> T)}"
by (drule ts_process_rep, simp add: failures_def)

lemma ts_process_futures:
 "trace_set T \<Longrightarrow>
  futures (ts_process T) xs =
  {(ys, Y). xs @ ys \<in> T \<and> (\<forall>y \<in> Y. xs @ ys @ [y] \<notin> T)}"
by (simp add: futures_def ts_process_failures)

lemma ts_process_traces:
 "trace_set T \<Longrightarrow> traces (ts_process T) = T"
proof (drule ts_process_failures, simp add: traces_def, rule set_eqI, rule iffI, simp_all)
qed (rule_tac x = "{}" in exI, simp)

lemma ts_process_refusals:
 "trace_set T \<Longrightarrow> xs \<in> T \<Longrightarrow>
  refusals (ts_process T) xs = {X. \<forall>x \<in> X. xs @ [x] \<notin> T}"
by (drule ts_process_failures, simp add: refusals_def)

lemma ts_process_next_events:
 "trace_set T \<Longrightarrow> (x \<in> next_events (ts_process T) xs) = (xs @ [x] \<in> T)"
by (drule ts_process_traces, simp add: next_events_def)

text \<open>
\null

In what follows, the proof is given of two results which provide a connection between the notions of
deterministic and trace set processes: any trace set process is deterministic, and any process is
deterministic just in case it is equal to the trace set process corresponding to the set of its
traces.

\null
\<close>

lemma ts_process_d:
 "trace_set T \<Longrightarrow> deterministic (ts_process T)"
proof (frule ts_process_traces, simp add: deterministic_def, rule ballI,
 drule ts_process_refusals, assumption, simp add: next_events_def,
 rule allI, rule iffI)
  fix xs X
  assume "\<forall>x \<in> X. xs @ [x] \<notin> T"
  thus "X \<inter> {x. xs @ [x] \<in> T} = {}"
  by (rule_tac equals0I, erule_tac IntE, simp)
next
  fix xs X
  assume A: "X \<inter> {x. xs @ [x] \<in> T} = {}"
  show "\<forall>x \<in> X. xs @ [x] \<notin> T"
  proof (rule ballI, rule notI)
    fix x
    assume "x \<in> X" and "xs @ [x] \<in> T"
    hence "x \<in> X \<inter> {x. xs @ [x] \<in> T}" by simp
    moreover have "x \<notin> X \<inter> {x. xs @ [x] \<in> T}" using A by (rule equals0D)
    ultimately show False by contradiction
  qed
qed

definition divergences :: "'a process \<Rightarrow> 'a list set" where
"divergences P \<equiv> snd (Rep_process P)"

lemma d_divergences:
  assumes A: "deterministic P"
  shows "divergences P = {}"
proof (subst divergences_def, rule equals0I)
  fix xs
  have B: "Rep_process P \<in> process_set" (is "?P' \<in> _") by (rule Rep_process)
  hence "\<forall>xs. \<exists>x. xs \<in> snd ?P' \<longrightarrow> xs @ [x] \<in> snd ?P'"
   by (simp add: process_set_def process_prop_5_def)
  hence "\<exists>x. xs \<in> snd ?P' \<longrightarrow> xs @ [x] \<in> snd ?P'" ..
  then obtain x where "xs \<in> snd ?P' \<longrightarrow> xs @ [x] \<in> snd ?P'" ..
  moreover assume C: "xs \<in> snd ?P'"
  ultimately have D: "xs @ [x] \<in> snd ?P'" ..
  have E: "\<forall>xs X. xs \<in> snd ?P' \<longrightarrow> (xs, X) \<in> fst ?P'"
   using B by (simp add: process_set_def process_prop_6_def)
  hence "xs \<in> snd ?P' \<longrightarrow> (xs, {x}) \<in> fst ?P'" by blast
  hence "{x} \<in> refusals P xs"
   using C by (drule_tac mp, simp_all add: failures_def refusals_def)
  moreover have "xs @ [x] \<in> snd ?P' \<longrightarrow> (xs @ [x], {}) \<in> fst ?P'"
   using E by blast
  hence "(xs @ [x], {}) \<in> failures P"
   using D by (drule_tac mp, simp_all add: failures_def)
  hence F: "xs @ [x] \<in> traces P" by (rule failures_traces)
  hence "{x} \<inter> next_events P xs \<noteq> {}" by (simp add: next_events_def)
  ultimately have G: "({x} \<in> refusals P xs) \<noteq> ({x} \<inter> next_events P xs = {})"
   by simp
  have "\<forall>xs \<in> traces P. \<forall>X. X \<in> refusals P xs = (X \<inter> next_events P xs = {})"
   using A by (simp add: deterministic_def)
  moreover have "xs \<in> traces P" using F by (rule process_rule_2_traces)
  ultimately have "\<forall>X. X \<in> refusals P xs = (X \<inter> next_events P xs = {})" ..
  hence "{x} \<in> refusals P xs = ({x} \<inter> next_events P xs = {})" ..
  thus False using G by contradiction
qed

lemma trace_set_traces:
 "trace_set (traces P)"
proof (simp only: trace_set_def traces_def failures_def Domain_iff,
 rule conjI, (rule_tac [2] allI)+, rule_tac [2] impI, erule_tac [2] exE)
  have "Rep_process P \<in> process_set" (is "?P' \<in> _") by (rule Rep_process)
  hence "([], {}) \<in> fst ?P'" by (simp add: process_set_def process_prop_1_def)
  thus "\<exists>X. ([], X) \<in> fst ?P'" ..
next
  fix xs x X
  have "Rep_process P \<in> process_set" (is "?P' \<in> _") by (rule Rep_process)
  hence "\<forall>xs x X. (xs @ [x], X) \<in> fst ?P' \<longrightarrow> (xs, {}) \<in> fst ?P'"
   by (simp add: process_set_def process_prop_2_def)
  hence "(xs @ [x], X) \<in> fst ?P' \<longrightarrow> (xs, {}) \<in> fst ?P'" by blast
  moreover assume "(xs @ [x], X) \<in> fst ?P'"
  ultimately have "(xs, {}) \<in> fst ?P'" ..
  thus "\<exists>X. (xs, X) \<in> fst ?P'" ..
qed

lemma d_implies_ts_process_traces:
 "deterministic P \<Longrightarrow> ts_process (traces P) = P"
proof (simp add: Rep_process_inject [symmetric] prod_eq_iff failures_def [symmetric],
 insert trace_set_traces [of P], frule ts_process_rep, frule d_divergences,
 simp add: divergences_def deterministic_def)
  assume A: "\<forall>xs \<in> traces P. \<forall>X.
    (X \<in> refusals P xs) = (X \<inter> next_events P xs = {})"
  assume B: "trace_set (traces P)"
  hence C: "traces (ts_process (traces P)) = traces P" by (rule ts_process_traces)
  show "failures (ts_process (traces P)) = failures P"
  proof (rule equalityI, rule_tac [!] subsetI, simp_all only: split_paired_all)
    fix xs X
    assume D: "(xs, X) \<in> failures (ts_process (traces P))"
    hence "xs \<in> traces (ts_process (traces P))" by (rule failures_traces)
    hence E: "xs \<in> traces P" using C by simp
    with B have
     "refusals (ts_process (traces P)) xs = {X. \<forall>x \<in> X. xs @ [x] \<notin> traces P}"
     by (rule ts_process_refusals)
    moreover have "X \<in> refusals (ts_process (traces P)) xs"
     using D by (simp add: refusals_def)
    ultimately have "\<forall>x \<in> X. xs @ [x] \<notin> traces P" by simp
    hence "X \<inter> next_events P xs = {}"
     by (rule_tac equals0I, erule_tac IntE, simp add: next_events_def)
    moreover have "\<forall>X. (X \<in> refusals P xs) = (X \<inter> next_events P xs = {})"
     using A and E ..
    hence "(X \<in> refusals P xs) = (X \<inter> next_events P xs = {})" ..
    ultimately have "X \<in> refusals P xs" by simp
    thus "(xs, X) \<in> failures P" by (simp add: refusals_def)
  next
    fix xs X
    assume D: "(xs, X) \<in> failures P"
    hence E: "xs \<in> traces P" by (rule failures_traces)
    with A have "\<forall>X. (X \<in> refusals P xs) = (X \<inter> next_events P xs = {})" ..
    hence "(X \<in> refusals P xs) = (X \<inter> next_events P xs = {})" ..
    moreover have "X \<in> refusals P xs" using D by (simp add: refusals_def)
    ultimately have F: "X \<inter> {x. xs @ [x] \<in> traces P} = {}"
     by (simp add: next_events_def)
    have "\<forall>x \<in> X. xs @ [x] \<notin> traces P"
    proof (rule ballI, rule notI)
      fix x
      assume "x \<in> X" and "xs @ [x] \<in> traces P"
      hence "x \<in> X \<inter> {x. xs @ [x] \<in> traces P}" by simp
      moreover have "x \<notin> X \<inter> {x. xs @ [x] \<in> traces P}" using F by (rule equals0D)
      ultimately show False by contradiction
    qed
    moreover have
     "refusals (ts_process (traces P)) xs = {X. \<forall>x \<in> X. xs @ [x] \<notin> traces P}"
     using B and E by (rule ts_process_refusals)
    ultimately have "X \<in> refusals (ts_process (traces P)) xs" by simp
    thus "(xs, X) \<in> failures (ts_process (traces P))" by (simp add: refusals_def)
  qed
qed

lemma ts_process_traces_implies_d:
 "ts_process (traces P) = P \<Longrightarrow> deterministic P"
by (insert trace_set_traces [of P], drule ts_process_d, simp)

lemma d_equals_ts_process_traces:
 "deterministic P = (ts_process (traces P) = P)"
by (rule iffI, erule d_implies_ts_process_traces, rule ts_process_traces_implies_d)

text \<open>
\null

Finally, a variant of the Ipurge Unwinding Theorem applying to trace set processes is derived from
the variant for deterministic processes. Particularly, the assumption that the process be
deterministic is replaced by the assumption that it be a trace set process,
since the former property is entailed by the latter (cf. above).

\null
\<close>

theorem ts_ipurge_unwinding:
 "trace_set T \<Longrightarrow>
  secure (ts_process T) I D =
  d_weakly_future_consistent (ts_process T) I D (rel_ipurge (ts_process T) I D)"
by (rule d_ipurge_unwinding, rule ts_process_d)

end
