(*  Title:       Conservation of CSP Noninterference Security under Sequential Composition
    Author:      Pasquale Noce
                 Security Certification Specialist at Arjo Systems, Italy
                 pasquale dot noce dot lavoro at gmail dot com
                 pasquale dot noce at arjosystems dot com
*)

section "Sequential composition and noninterference security"

theory SequentialComposition
imports Propaedeutics
begin

text \<open>
\null

This section formalizes the definitions of sequential processes and sequential composition given in
\cite{R4}, and then proves that under the assumptions discussed above, noninterference security is
conserved under sequential composition for any pair of processes sharing an alphabet that contains
successful termination. Finally, this result is generalized to an arbitrary list of processes.
\<close>


subsection "Sequential processes"

text \<open>
In \cite{R4}, a \emph{sequential process} is defined as a process whose alphabet contains successful
termination. Since sequential composition applies to sequential processes, the first problem put by
the formalization of this operation is that of finding a suitable way to represent such a process.

A simple but effective strategy is to identify it with a process having alphabet @{typ "'a option"},
where @{typ 'a} is the native type of its ordinary (i.e. distinct from termination) events. Then,
ordinary events will be those matching pattern \<open>Some _\<close>, whereas successful termination will
be denoted by the special event @{term None}. This means that the \emph{sentences} of a sequential
process, defined in \cite{R4} as the traces after which the process can terminate successfully, will
be nothing but the event lists @{term xs} such that @{term "xs @ [None]"} is a trace (which implies
that @{term xs} is a trace as well).

Once a suitable representation of successful termination has been found, the next step is to
formalize the properties of sequential processes related to this event, expressing them in terms of
the selected representation. The first of the resulting predicates, \<open>weakly_sequential\<close>, is
the minimum required for allowing the identification of event @{term None} with successful
termination, namely that @{term None} may occur in a trace as its last event only. The second
predicate, \<open>sequential\<close>, following what Hoare does in \cite{R4}, extends the first predicate
with an additional requirement, namely that whenever the process can engage in event @{term None},
it cannot engage in any other event. A simple counterexample shows that this requirement does not
imply the first one: a process whose traces are @{term "{[], [None], [None, None]}"} satisfies the
second requirement, but not the first one.

Moreover, here below is the definition of a further predicate, \<open>secure_termination\<close>, which
applies to a security policy rather than to a process, and is satisfied just in case the policy does
not allow event @{term None} to be affected by confidential events, viz. by ordinary events not
allowed to affect some event in the alphabet. Interestingly, this property, which will prove to be
necessary for the target theorem to hold, is nothing but the CSP counterpart of a condition required
for a security type system to enforce termination-sensitive noninterference security of programs,
namely that program termination must not depend on confidential data (cf. \cite{R5}, section 9.2.6).

\null
\<close>

definition sentences :: "'a option process \<Rightarrow> 'a option list set" where
"sentences P \<equiv> {xs. xs @ [None] \<in> traces P}"

definition weakly_sequential :: "'a option process \<Rightarrow> bool" where
"weakly_sequential P \<equiv>
  \<forall>xs \<in> traces P. None \<notin> set (butlast xs)"

definition sequential :: "'a option process \<Rightarrow> bool" where
"sequential P \<equiv>
  (\<forall>xs \<in> traces P. None \<notin> set (butlast xs)) \<and>
  (\<forall>xs \<in> sentences P. next_events P xs = {None})"

definition secure_termination :: "('d \<times> 'd) set \<Rightarrow> ('a option \<Rightarrow> 'd) \<Rightarrow> bool" where
"secure_termination I D \<equiv>
  \<forall>x. (D x, D None) \<in> I \<and> x \<noteq> None \<longrightarrow> (\<forall>u \<in> range D. (D x, u) \<in> I)"

text \<open>
\null

Here below is the proof of some useful lemmas involving the constants just defined. Particularly, it
is proven that process sequentiality is indeed stronger than weak sequentiality, and a sentence of a
refusals union closed (cf. \cite{R3}), sequential process admits the set of all the ordinary events
of the process as a refusal. The use of the latter lemma in the proof of the target security
conservation theorem is the reason why the theorem requires to assume that the first of the
processes to be composed be refusals union closed (cf. below).

\null
\<close>

lemma seq_implies_weakly_seq:
 "sequential P \<Longrightarrow> weakly_sequential P"
by (simp add: weakly_sequential_def sequential_def)

lemma weakly_seq_sentences_none:
  assumes
    WS: "weakly_sequential P" and
    A: "xs \<in> sentences P"
  shows "None \<notin> set xs"
proof -
  have "\<forall>xs \<in> traces P. None \<notin> set (butlast xs)"
   using WS by (simp add: weakly_sequential_def)
  moreover have "xs @ [None] \<in> traces P"
   using A by (simp add: sentences_def)
  ultimately have "None \<notin> set (butlast (xs @ [None]))" ..
  thus ?thesis
   by simp
qed

lemma seq_sentences_none:
  assumes
    S: "sequential P" and
    A: "xs \<in> sentences P" and
    B: "xs @ y # ys \<in> traces P"
  shows "y = None"
proof -
  have "\<forall>xs \<in> sentences P. next_events P xs = {None}"
   using S by (simp add: sequential_def)
  hence "next_events P xs = {None}"
   using A ..
  moreover have "(xs @ [y]) @ ys \<in> traces P"
   using B by simp
  hence "xs @ [y] \<in> traces P"
   by (rule process_rule_2_traces)
  hence "y \<in> next_events P xs"
   by (simp add: next_events_def)
  ultimately show ?thesis
   by simp
qed

lemma seq_sentences_ref:
  assumes
    A: "ref_union_closed P" and
    B: "sequential P" and
    C: "xs \<in> sentences P"
  shows "(xs, {x. x \<noteq> None}) \<in> failures P"
    (is "(_, ?X) \<in> _")
proof -
  have "(\<exists>X. X \<in> singleton_set ?X) \<longrightarrow>
    (\<forall>X \<in> singleton_set ?X. (xs, X) \<in> failures P) \<longrightarrow>
    (xs, \<Union>X \<in> singleton_set ?X. X) \<in> failures P"
   using A by (simp add: ref_union_closed_def)
  moreover have "\<exists>x. x \<in> ?X"
   by blast
  hence "\<exists>X. X \<in> singleton_set ?X"
   by (simp add: singleton_set_some)
  ultimately have "(\<forall>X \<in> singleton_set ?X. (xs, X) \<in> failures P) \<longrightarrow>
    (xs, \<Union>X \<in> singleton_set ?X. X) \<in> failures P" ..
  moreover have "\<forall>X \<in> singleton_set ?X. (xs, X) \<in> failures P"
  proof (rule ballI, simp add: singleton_set_def del: not_None_eq,
   erule exE, erule conjE, simp (no_asm_simp))
    fix x :: "'a option"
    assume D: "x \<noteq> None"
    have "xs @ [None] \<in> traces P"
     using C by (simp add: sentences_def)
    hence "xs \<in> traces P"
     by (rule process_rule_2_traces)
    hence "(xs, {}) \<in> failures P"
     by (rule traces_failures)
    hence "(xs @ [x], {}) \<in> failures P \<or> (xs, {x}) \<in> failures P"
     by (rule process_rule_4)
    thus "(xs, {x}) \<in> failures P"
    proof (rule disjE, rule_tac ccontr, simp_all)
      assume "(xs @ [x], {}) \<in> failures P"
      hence "xs @ [x] \<in> traces P"
       by (rule failures_traces)
      with B and C have "x = None"
       by (rule seq_sentences_none)
      thus False
       using D by contradiction
    qed
  qed
  ultimately have "(xs, \<Union>X \<in> singleton_set ?X. X) \<in> failures P" ..
  thus ?thesis
   by (simp only: singleton_set_union)
qed


subsection "Sequential composition"

text \<open>
In what follows, the definition of the failures resulting from the sequential composition of two
processes @{term P}, @{term Q} given in \cite{R4} is formalized as the inductive definition of set
\<open>seq_comp_failures P Q\<close>. Then, the sequential composition of @{term P} and @{term Q},
denoted by means of notation \<open>P ; Q\<close> following \cite{R4}, is defined as the process having
\<open>seq_comp_failures P Q\<close> as failures set and the empty set as divergences set.

For the sake of generality, this definition is based on the mere implicit assumption that the input
processes be weakly sequential, rather than sequential. This slightly complicates things, since the
sentences of process @{term P} may number further events in addition to @{term None} in their
future.

Therefore, the resulting refusals of a sentence @{term xs} of @{term P} will have the form
@{term "insert None X \<inter> Y"}, where @{term X} is a refusal of @{term xs} in @{term P} and @{term Y}
is an initial refusal of @{term Q} (cf. rule \<open>SCF_R2\<close>). In fact, after @{term xs}, process
\<open>P ; Q\<close> must be able to refuse @{term None} if @{term Q} is, whereas it cannot refuse an
ordinary event unless both @{term P} and @{term Q}, in their respective states, can.

Moreover, a trace @{term xs} of \<open>P ; Q\<close> may result from different combinations of a sentence
of @{term P} with a trace of @{term Q}. Thus, in order that the refusals of \<open>P ; Q\<close> be
closed under set union, the union of any two refusals of @{term xs} must still be a refusal (cf.
rule \<open>SCF_R4\<close>). Indeed, this property will prove to be sufficient to ensure that for any two
processes whose refusals are closed under set union, their sequential composition still be such,
which is what is expected for any process of practical significance (cf. \cite{R3}).

According to the definition given in \cite{R4}, a divergence of \<open>P ; Q\<close> is either a
divergence of @{term P}, or the concatenation of a sentence of @{term P} with a divergence of
@{term Q}. Apparently, this definition does not match the formal one stated here below, which
identifies the divergences set of \<open>P ; Q\<close> with the empty set. Nonetheless, as remarked
above, sequential composition does not make sense unless the input processes are weakly sequential,
since this is the minimum required to confer the meaning of successful termination on the
corresponding alphabet symbol. But a weakly sequential process cannot have any divergence, so that
the two definitions are actually equivalent. In fact, a divergence is a trace such that, however it
is extended with arbitrary additional events, the resulting event list is still a trace (cf. process
properties @{term process_prop_5} and @{term process_prop_6} in \cite{R2}). Therefore, if @{term xs}
were a divergence, then @{term "xs @ [None, None]"} would be a trace, which is impossible in case
the process satisfies predicate @{term weakly_sequential}.

\null
\<close>

inductive_set seq_comp_failures ::
 "'a option process \<Rightarrow> 'a option process \<Rightarrow> 'a option failure set"
for P :: "'a option process" and Q :: "'a option process" where

SCF_R1: "\<lbrakk>xs \<notin> sentences P; (xs, X) \<in> failures P; None \<notin> set xs\<rbrakk> \<Longrightarrow>
  (xs, X) \<in> seq_comp_failures P Q" |

SCF_R2: "\<lbrakk>xs \<in> sentences P; (xs, X) \<in> failures P; ([], Y) \<in> failures Q\<rbrakk> \<Longrightarrow>
  (xs, insert None X \<inter> Y) \<in> seq_comp_failures P Q" |

SCF_R3: "\<lbrakk>xs \<in> sentences P; (ys, Y) \<in> failures Q; ys \<noteq> []\<rbrakk> \<Longrightarrow>
  (xs @ ys, Y) \<in> seq_comp_failures P Q" |

SCF_R4: "\<lbrakk>(xs, X) \<in> seq_comp_failures P Q; (xs, Y) \<in> seq_comp_failures P Q\<rbrakk> \<Longrightarrow>
  (xs, X \<union> Y) \<in> seq_comp_failures P Q"

definition seq_comp ::
 "'a option process \<Rightarrow> 'a option process \<Rightarrow> 'a option process" (infixl ";" 60)
where
"P ; Q \<equiv> Abs_process (seq_comp_failures P Q, {})"

text \<open>
\null

Here below is the proof that, for any two processes @{term P}, @{term Q} defined over the same
alphabet containing successful termination, set @{term "seq_comp_failures P Q"} indeed enjoys the
characteristic properties of the failures set of a process as defined in \cite{R2} provided that
@{term P} is weakly sequential, which is what happens in any meaningful case.

\null
\<close>

lemma seq_comp_prop_1:
 "([], {}) \<in> seq_comp_failures P Q"
proof (cases "[] \<in> sentences P")
  case False
  moreover have "([], {}) \<in> failures P"
   by (rule process_rule_1)
  moreover have "None \<notin> set []"
   by simp
  ultimately show ?thesis
   by (rule SCF_R1)
next
  case True
  moreover have "([], {}) \<in> failures P"
   by (rule process_rule_1)
  moreover have "([], {}) \<in> failures Q"
   by (rule process_rule_1)
  ultimately have "([], {None} \<inter> {}) \<in> seq_comp_failures P Q"
   by (rule SCF_R2)
  thus ?thesis by simp
qed

lemma seq_comp_prop_2_aux [rule_format]:
  assumes WS: "weakly_sequential P"
  shows "(ws, X) \<in> seq_comp_failures P Q \<Longrightarrow>
    ws = xs @ [x] \<longrightarrow> (xs, {}) \<in> seq_comp_failures P Q"
proof (erule seq_comp_failures.induct, rule_tac [!] impI, simp_all, erule conjE)
  fix X'
  assume
    A: "(xs @ [x], X') \<in> failures P" and
    B: "None \<notin> set xs"
  have A': "(xs, {}) \<in> failures P"
   using A by (rule process_rule_2)
  show "(xs, {}) \<in> seq_comp_failures P Q"
  proof (cases "xs \<in> sentences P")
    case False
    thus ?thesis
     using A' and B by (rule SCF_R1)
  next
    case True
    have "([], {}) \<in> failures Q"
     by (rule process_rule_1)
    with True and A' have "(xs, {None} \<inter> {}) \<in> seq_comp_failures P Q"
     by (rule SCF_R2)
    thus ?thesis by simp
  qed
next
  fix X'
  assume A: "(xs @ [x], X') \<in> failures P"
  hence A': "(xs, {}) \<in> failures P"
   by (rule process_rule_2)
  show "(xs, {}) \<in> seq_comp_failures P Q"
  proof (cases "xs \<in> sentences P")
    case False
    have "\<forall>xs \<in> traces P. None \<notin> set (butlast xs)"
     using WS by (simp add: weakly_sequential_def)
    moreover have "xs @ [x] \<in> traces P"
     using A by (rule failures_traces)
    ultimately have "None \<notin> set (butlast (xs @ [x]))" ..
    hence "None \<notin> set xs" by simp
    with False and A' show ?thesis
     by (rule SCF_R1)
  next
    case True
    have "([], {}) \<in> failures Q"
     by (rule process_rule_1)
    with True and A' have "(xs, {None} \<inter> {}) \<in> seq_comp_failures P Q"
     by (rule SCF_R2)
    thus ?thesis by simp
  qed
next
  fix xs' ys Y
  assume
    A: "xs' @ ys = xs @ [x]" and
    B: "xs' \<in> sentences P" and
    C: "(ys, Y) \<in> failures Q" and
    D: "ys \<noteq> []"
  have "\<exists>y ys'. ys = ys' @ [y]"
   using D by (rule_tac xs = ys in rev_cases, simp_all)
  then obtain y and ys' where D': "ys = ys' @ [y]"
   by blast
  hence "xs = xs' @ ys'"
   using A by simp
  thus "(xs, {}) \<in> seq_comp_failures P Q"
  proof (cases "ys' = []", simp_all)
    case True
    have "xs' @ [None] \<in> traces P"
     using B by (simp add: sentences_def)
    hence "xs' \<in> traces P"
     by (rule process_rule_2_traces)
    hence "(xs', {}) \<in> failures P"
     by (rule traces_failures)
    moreover have "([], {}) \<in> failures Q"
     by (rule process_rule_1)
    ultimately have "(xs', {None} \<inter> {}) \<in> seq_comp_failures P Q"
     by (rule SCF_R2 [OF B])
    thus "(xs', {}) \<in> seq_comp_failures P Q"
     by simp
  next
    case False
    have "(ys' @ [y], Y) \<in> failures Q"
     using C and D' by simp
    hence C': "(ys', {}) \<in> failures Q"
     by (rule process_rule_2)
    with B show "(xs' @ ys', {}) \<in> seq_comp_failures P Q"
     using False by (rule SCF_R3)
  qed
qed

lemma seq_comp_prop_2:
  assumes WS: "weakly_sequential P"
  shows "(xs @ [x], X) \<in> seq_comp_failures P Q \<Longrightarrow>
    (xs, {}) \<in> seq_comp_failures P Q"
by (erule seq_comp_prop_2_aux [OF WS], simp)

lemma seq_comp_prop_3 [rule_format]:
 "(xs, Y) \<in> seq_comp_failures P Q \<Longrightarrow> X \<subseteq> Y \<longrightarrow>
    (xs, X) \<in> seq_comp_failures P Q"
proof (induction arbitrary: X rule: seq_comp_failures.induct, rule_tac [!] impI)
  fix xs X Y
  assume
    A: "xs \<notin> sentences P" and
    B: "(xs, X) \<in> failures P" and
    C: "None \<notin> set xs" and
    D: "Y \<subseteq> X"
  have "(xs, Y) \<in> failures P"
   using B and D by (rule process_rule_3)
  with A show "(xs, Y) \<in> seq_comp_failures P Q"
   using C by (rule SCF_R1)
next
  fix xs X Y Z
  assume
    A: "xs \<in> sentences P" and
    B: "(xs, X) \<in> failures P" and
    C: "([], Y) \<in> failures Q" and
    D: "Z \<subseteq> insert None X \<inter> Y"
  have "Z - {None} \<subseteq> X"
   using D by blast
  with B have "(xs, Z - {None}) \<in> failures P"
   by (rule process_rule_3)
  moreover have "Z \<subseteq> Y"
   using D by simp
  with C have "([], Z) \<in> failures Q"
   by (rule process_rule_3)
  ultimately have "(xs, insert None (Z - {None}) \<inter> Z) \<in> seq_comp_failures P Q"
   by (rule SCF_R2 [OF A])
  moreover have "insert None (Z - {None}) \<inter> Z = Z"
   by blast
  ultimately show "(xs, Z) \<in> seq_comp_failures P Q"
   by simp
next
  fix xs ys X Y
  assume
    A: "xs \<in> sentences P" and
    B: "(ys, Y) \<in> failures Q" and
    C: "ys \<noteq> []" and
    D: "X \<subseteq> Y"
  have "(ys, X) \<in> failures Q"
   using B and D by (rule process_rule_3)
  with A show "(xs @ ys, X) \<in> seq_comp_failures P Q"
   using C by (rule SCF_R3)
next
  fix xs X Y Z
  assume
    A: "\<And>W. W \<subseteq> X \<longrightarrow> (xs, W) \<in> seq_comp_failures P Q" and
    B: "\<And>W. W \<subseteq> Y \<longrightarrow> (xs, W) \<in> seq_comp_failures P Q" and
    C: "Z \<subseteq> X \<union> Y"
  have "Z \<inter> X \<subseteq> X \<longrightarrow> (xs, Z \<inter> X) \<in> seq_comp_failures P Q"
   using A .
  hence "(xs, Z \<inter> X) \<in> seq_comp_failures P Q"
   by simp
  moreover have "Z \<inter> Y \<subseteq> Y \<longrightarrow> (xs, Z \<inter> Y) \<in> seq_comp_failures P Q"
   using B .
  hence "(xs, Z \<inter> Y) \<in> seq_comp_failures P Q"
   by simp
  ultimately have "(xs, Z \<inter> X \<union> Z \<inter> Y) \<in> seq_comp_failures P Q"
   by (rule SCF_R4)
  hence "(xs, Z \<inter> (X \<union> Y)) \<in> seq_comp_failures P Q"
   by (simp add: Int_Un_distrib)
  moreover have "Z \<inter> (X \<union> Y) = Z"
   using C by (rule Int_absorb2)
  ultimately show "(xs, Z) \<in> seq_comp_failures P Q"
   by simp
qed

lemma seq_comp_prop_4:
  assumes WS: "weakly_sequential P"
  shows "(xs, X) \<in> seq_comp_failures P Q \<Longrightarrow>
    (xs @ [x], {}) \<in> seq_comp_failures P Q \<or>
    (xs, insert x X) \<in> seq_comp_failures P Q"
proof (erule seq_comp_failures.induct, simp_all)
  fix xs X
  assume
    A: "xs \<notin> sentences P" and
    B: "(xs, X) \<in> failures P" and
    C: "None \<notin> set xs"
  have "(xs @ [x], {}) \<in> failures P \<or>
    (xs, insert x X) \<in> failures P"
   using B by (rule process_rule_4)
  thus "(xs @ [x], {}) \<in> seq_comp_failures P Q \<or>
    (xs, insert x X) \<in> seq_comp_failures P Q"
  proof
    assume D: "(xs @ [x], {}) \<in> failures P"
    show ?thesis
    proof (cases "xs @ [x] \<in> sentences P")
      case False
      have "None \<notin> set (xs @ [x])"
      proof (simp add: C, rule notI)
        assume "None = x"
        hence "(xs @ [None], {}) \<in> failures P"
         using D by simp
        hence "xs @ [None] \<in> traces P"
         by (rule failures_traces)
        hence "xs \<in> sentences P"
         by (simp add: sentences_def)
        thus False
         using A by contradiction
      qed
      with False and D have "(xs @ [x], {}) \<in> seq_comp_failures P Q"
       by (rule SCF_R1)
      thus ?thesis ..
    next
      case True
      have "([], {}) \<in> failures Q"
       by (rule process_rule_1)
      with True and D have "(xs @ [x], {None} \<inter> {}) \<in> seq_comp_failures P Q"
       by (rule SCF_R2)
      thus ?thesis by simp
    qed
  next
    assume "(xs, insert x X) \<in> failures P"
    with A have "(xs, insert x X) \<in> seq_comp_failures P Q"
     using C by (rule SCF_R1)
    thus ?thesis ..
  qed
next
  fix xs X Y
  assume
    A: "xs \<in> sentences P" and
    B: "(xs, X) \<in> failures P" and
    C: "([], Y) \<in> failures Q"
  show "(xs @ [x], {}) \<in> seq_comp_failures P Q \<or>
    (xs, insert x (insert None X \<inter> Y)) \<in> seq_comp_failures P Q"
  proof (cases "x = None", simp)
    case True
    have "([] @ [None], {}) \<in> failures Q \<or> ([], insert None Y) \<in> failures Q"
     using C by (rule process_rule_4)
    thus "(xs @ [None], {}) \<in> seq_comp_failures P Q \<or>
      (xs, insert None (insert None X \<inter> Y)) \<in> seq_comp_failures P Q"
    proof (rule disjE, simp)
      assume "([None], {}) \<in> failures Q"
      moreover have "[None] \<noteq> []"
       by simp
      ultimately have "(xs @ [None], {}) \<in> seq_comp_failures P Q"
       by (rule SCF_R3 [OF A])
      thus ?thesis ..
    next
      assume "([], insert None Y) \<in> failures Q"
      with A and B have "(xs, insert None X \<inter> insert None Y)
        \<in> seq_comp_failures P Q"
       by (rule SCF_R2)
      moreover have "insert None X \<inter> insert None Y =
        insert None (insert None X \<inter> Y)"
       by blast
      ultimately have "(xs, insert None (insert None X \<inter> Y))
        \<in> seq_comp_failures P Q"
       by simp
      thus ?thesis ..
    qed
  next
    case False
    have "(xs @ [x], {}) \<in> failures P \<or> (xs, insert x X) \<in> failures P"
     using B by (rule process_rule_4)
    thus ?thesis
    proof (rule disjE, cases "xs @ [x] \<in> sentences P")
      assume
        D: "xs @ [x] \<notin> sentences P" and
        E: "(xs @ [x], {}) \<in> failures P"
      have "None \<notin> set xs"
       using WS and A by (rule weakly_seq_sentences_none)
      hence "None \<notin> set (xs @ [x])"
       using False by (simp del: not_None_eq)
      with D and E have "(xs @ [x], {}) \<in> seq_comp_failures P Q"
       by (rule SCF_R1)
      thus ?thesis ..
    next
      assume
        "xs @ [x] \<in> sentences P" and
        "(xs @ [x], {}) \<in> failures P"
      moreover have "([], {}) \<in> failures Q"
       by (rule process_rule_1)
      ultimately have "(xs @ [x], {None} \<inter> {}) \<in> seq_comp_failures P Q"
       by (rule SCF_R2)
      thus ?thesis by simp
    next
      assume D: "(xs, insert x X) \<in> failures P"
      have "([] @ [x], {}) \<in> failures Q \<or> ([], insert x Y) \<in> failures Q"
       using C by (rule process_rule_4)
      thus ?thesis
      proof (rule disjE, simp)
        assume "([x], {}) \<in> failures Q"
        moreover have "[x] \<noteq> []"
         by simp
        ultimately have "(xs @ [x], {}) \<in> seq_comp_failures P Q"
         by (rule SCF_R3 [OF A])
        thus ?thesis ..
      next
        assume "([], insert x Y) \<in> failures Q"
        with A and D have "(xs, insert None (insert x X) \<inter> insert x Y)
          \<in> seq_comp_failures P Q"
         by (rule SCF_R2)
        moreover have "insert None (insert x X) \<inter> insert x Y =
          insert x (insert None X \<inter> Y)"
         by blast
        ultimately have "(xs, insert x (insert None X \<inter> Y))
          \<in> seq_comp_failures P Q"
         by simp
        thus ?thesis ..
      qed
    qed
  qed
next
  fix xs ys Y
  assume
    A: "xs \<in> sentences P" and
    B: "(ys, Y) \<in> failures Q" and
    C: "ys \<noteq> []"
  have "(ys @ [x], {}) \<in> failures Q \<or> (ys, insert x Y) \<in> failures Q"
   using B by (rule process_rule_4)
  thus "(xs @ ys @ [x], {}) \<in> seq_comp_failures P Q \<or>
    (xs @ ys, insert x Y) \<in> seq_comp_failures P Q"
  proof
    assume "(ys @ [x], {}) \<in> failures Q"
    moreover have "ys @ [x] \<noteq> []"
     by simp
    ultimately have "(xs @ ys @ [x], {}) \<in> seq_comp_failures P Q"
     by (rule SCF_R3 [OF A])
    thus ?thesis ..
  next
    assume "(ys, insert x Y) \<in> failures Q"
    with A have "(xs @ ys, insert x Y) \<in> seq_comp_failures P Q"
     using C by (rule SCF_R3)
    thus ?thesis ..
  qed
next
  fix xs X Y
  assume
    "(xs @ [x], {}) \<in> seq_comp_failures P Q \<or>
      (xs, insert x X) \<in> seq_comp_failures P Q" and
    "(xs @ [x], {}) \<in> seq_comp_failures P Q \<or>
      (xs, insert x Y) \<in> seq_comp_failures P Q"
  thus "(xs @ [x], {}) \<in> seq_comp_failures P Q \<or>
    (xs, insert x (X \<union> Y)) \<in> seq_comp_failures P Q"
  proof (cases "(xs @ [x], {}) \<in> seq_comp_failures P Q", simp_all)
    assume
      "(xs, insert x X) \<in> seq_comp_failures P Q" and
      "(xs, insert x Y) \<in> seq_comp_failures P Q"
    hence "(xs, insert x X \<union> insert x Y) \<in> seq_comp_failures P Q"
     by (rule SCF_R4)
    thus "(xs, insert x (X \<union> Y)) \<in> seq_comp_failures P Q"
     by simp
  qed
qed

lemma seq_comp_rep:
  assumes WS: "weakly_sequential P"
  shows "Rep_process (P ; Q) = (seq_comp_failures P Q, {})"
proof (subst seq_comp_def, rule Abs_process_inverse, simp add: process_set_def,
 (subst conj_assoc [symmetric])+, (rule conjI)+)
  show "process_prop_1 (seq_comp_failures P Q, {})"
  proof (simp add: process_prop_1_def)
  qed (rule seq_comp_prop_1)
next
  show "process_prop_2 (seq_comp_failures P Q, {})"
  proof (simp add: process_prop_2_def del: all_simps, (rule allI)+, rule impI)
  qed (rule seq_comp_prop_2 [OF WS])
next
  show "process_prop_3 (seq_comp_failures P Q, {})"
  proof (simp add: process_prop_3_def del: all_simps, (rule allI)+, rule impI,
   erule conjE)
  qed (rule seq_comp_prop_3)
next
  show "process_prop_4 (seq_comp_failures P Q, {})"
  proof (simp add: process_prop_4_def, (rule allI)+, rule impI)
  qed (rule seq_comp_prop_4 [OF WS])
next
  show "process_prop_5 (seq_comp_failures P Q, {})"
   by (simp add: process_prop_5_def)
next
  show "process_prop_6 (seq_comp_failures P Q, {})"
   by (simp add: process_prop_6_def)
qed

text \<open>
\null

Here below, the previous result is applied to derive useful expressions for the outputs of the
functions returning the elements of a process, as defined in \cite{R2} and \cite{R3}, when acting on
the sequential composition of a pair of processes.

\null
\<close>

lemma seq_comp_failures:
 "weakly_sequential P \<Longrightarrow>
    failures (P ; Q) = seq_comp_failures P Q"
by (drule seq_comp_rep [where Q = Q], simp add: failures_def)

lemma seq_comp_divergences:
 "weakly_sequential P \<Longrightarrow>
    divergences (P ; Q) = {}"
by (drule seq_comp_rep [where Q = Q], simp add: divergences_def)

lemma seq_comp_futures:
 "weakly_sequential P \<Longrightarrow>
    futures (P ; Q) xs = {(ys, Y). (xs @ ys, Y) \<in> seq_comp_failures P Q}"
by (simp add: futures_def seq_comp_failures)

lemma seq_comp_traces:
 "weakly_sequential P \<Longrightarrow>
    traces (P ; Q) = Domain (seq_comp_failures P Q)"
by (simp add: traces_def seq_comp_failures)

lemma seq_comp_refusals:
 "weakly_sequential P \<Longrightarrow>
    refusals (P ; Q) xs \<equiv> seq_comp_failures P Q `` {xs}"
by (simp add: refusals_def seq_comp_failures)

lemma seq_comp_next_events:
 "weakly_sequential P \<Longrightarrow>
    next_events (P ; Q) xs = {x. xs @ [x] \<in> Domain (seq_comp_failures P Q)}"
by (simp add: next_events_def seq_comp_traces)


subsection "Conservation of refusals union closure and sequentiality under sequential composition"

text \<open>
Here below is the proof that, for any two processes @{term P}, @{term Q} and any failure
@{term "(xs, X)"} of @{term "P ; Q"}, the refusal @{term X} is the union of a set of refusals where,
for any such refusal @{term W}, @{term "(xs, W)"} is a failure of @{term "P ; Q"} by virtue of one
of rules \<open>SCF_R1\<close>, \<open>SCF_R2\<close>, or \<open>SCF_R3\<close>.

The converse is also proven, under the assumption that the refusals of both @{term P} and @{term Q}
be closed under union: namely, for any trace @{term xs} of @{term "P ; Q"} and any set of refusals
where, for any such refusal @{term W}, @{term "(xs, W)"} is a failure of the aforesaid kind, the
union of these refusals is still a refusal of @{term xs}.

The proof of the latter lemma makes use of the axiom of choice.

\null
\<close>

lemma seq_comp_refusals_1:
 "(xs, X) \<in> seq_comp_failures P Q \<Longrightarrow> \<exists>R.
    X = (\<Union>n \<in> {..length xs}. \<Union>W \<in> R n. W) \<and>
    (\<forall>W \<in> R 0.
      xs \<notin> sentences P \<and> None \<notin> set xs \<and> (xs, W) \<in> failures P \<or>
      xs \<in> sentences P \<and> (\<exists>U V. (xs, U) \<in> failures P \<and> ([], V) \<in> failures Q \<and>
        W = insert None U \<inter> V)) \<and>
    (\<forall>n \<in> {0<..length xs}. \<forall>W \<in> R n.
      take (length xs - n) xs \<in> sentences P \<and>
      (drop (length xs - n) xs, W) \<in> failures Q) \<and>
    (\<exists>n \<in> {..length xs}. \<exists>W. W \<in> R n)"
  (is "_ \<Longrightarrow> \<exists>R. ?T R xs X")
proof (erule seq_comp_failures.induct, (erule_tac [4] exE)+)
  fix xs X
  assume
    A: "xs \<notin> sentences P" and
    B: "(xs, X) \<in> failures P" and
    C: "None \<notin> set xs"
  show "\<exists>R. ?T R xs X"
  proof (rule_tac x = "\<lambda>n. if n = 0 then {X} else {}" in exI,
   simp add: A B C, rule equalityI, rule_tac [!] subsetI, simp_all)
    fix x
    assume "\<exists>n \<in> {..length xs}.
      \<exists>W \<in> if n = 0 then {X} else {}. x \<in> W"
    thus "x \<in> X"
     by (simp split: if_split_asm)
  qed
next
  fix xs X Y
  assume
    A: "xs \<in> sentences P" and
    B: "(xs, X) \<in> failures P" and
    C: "([], Y) \<in> failures Q"
  show "\<exists>R. ?T R xs (insert None X \<inter> Y)"
  proof (rule_tac x = "\<lambda>n. if n = 0 then {insert None X \<inter> Y} else {}" in exI,
   simp add: A, rule conjI, rule equalityI, rule_tac [1-2] subsetI, simp_all)
    fix x
    assume "\<exists>n \<in> {..length xs}.
      \<exists>W \<in> if n = 0 then {insert None X \<inter> Y} else {}. x \<in> W"
    thus "(x = None \<or> x \<in> X) \<and> x \<in> Y"
     by (simp split: if_split_asm)
  next
    show "\<exists>U. (xs, U) \<in> failures P \<and> (\<exists>V. ([], V) \<in> failures Q \<and>
      insert None X \<inter> Y = insert None U \<inter> V)"
    proof (rule_tac x = X in exI, rule conjI, simp add: B)
    qed (rule_tac x = Y in exI, rule conjI, simp_all add: C)
  qed
next
  fix xs ys Y
  assume
    A: "xs \<in> sentences P" and
    B: "(ys, Y) \<in> failures Q" and
    C: "ys \<noteq> []"
  show "\<exists>R. ?T R (xs @ ys) Y"
  proof (rule_tac x = "\<lambda>n. if n = length ys then {Y} else {}" in exI,
   simp add: A B C, rule equalityI, rule_tac [!] subsetI, simp_all)
    fix x
    assume "\<exists>n \<in> {..length xs + length ys}.
      \<exists>W \<in> if n = length ys then {Y} else {}. x \<in> W"
    thus "x \<in> Y"
     by (simp split: if_split_asm)
  qed
next
  fix xs X Y Rx Ry
  assume
    A: "?T Rx xs X" and
    B: "?T Ry xs Y"
  show "\<exists>R. ?T R xs (X \<union> Y)"
  proof (rule_tac x = "\<lambda>n. Rx n \<union> Ry n" in exI, rule conjI, rule_tac [2] conjI,
   rule_tac [3] conjI, rule_tac [2] ballI, (rule_tac [3] ballI)+)
    have "X \<union> Y = (\<Union>n \<le> length xs. \<Union>W \<in> Rx n. W) \<union>
      (\<Union>n \<le> length xs. \<Union>W \<in> Ry n. W)"
     using A and B by simp
    also have "\<dots> = (\<Union>n \<le> length xs. (\<Union>W \<in> Rx n. W) \<union> (\<Union>W \<in> Ry n. W))"
     by blast
    also have "\<dots> = (\<Union>n \<le> length xs. \<Union>W \<in> Rx n \<union> Ry n. W)"
     by simp
    finally show "X \<union> Y = (\<Union>n \<le> length xs. \<Union>W \<in> Rx n \<union> Ry n. W)" .
  next
    fix W
    assume "W \<in> Rx 0 \<union> Ry 0"
    thus
     "xs \<notin> sentences P \<and> None \<notin> set xs \<and> (xs, W) \<in> failures P \<or>
      xs \<in> sentences P \<and> (\<exists>U V. (xs, U) \<in> failures P \<and> ([], V) \<in> failures Q \<and>
        W = insert None U \<inter> V)"
      (is "?T' W")
    proof
      have "\<forall>W \<in> Rx 0. ?T' W"
       using A by simp
      moreover assume "W \<in> Rx 0"
      ultimately show ?thesis ..
    next
      have "\<forall>W \<in> Ry 0. ?T' W"
       using B by simp
      moreover assume "W \<in> Ry 0"
      ultimately show ?thesis ..
    qed
  next
    fix n W
    assume C: "n \<in> {0<..length xs}"
    assume "W \<in> Rx n \<union> Ry n"
    thus
     "take (length xs - n) xs \<in> sentences P \<and>
      (drop (length xs - n) xs, W) \<in> failures Q"
      (is "?T' n W")
    proof
      have "\<forall>n \<in> {0<..length xs}. \<forall>W \<in> Rx n. ?T' n W"
       using A by simp
      hence "\<forall>W \<in> Rx n. ?T' n W"
       using C ..
      moreover assume "W \<in> Rx n"
      ultimately show ?thesis ..
    next
      have "\<forall>n \<in> {0<..length xs}. \<forall>W \<in> Ry n. ?T' n W"
       using B by simp
      hence "\<forall>W \<in> Ry n. ?T' n W"
       using C ..
      moreover assume "W \<in> Ry n"
      ultimately show ?thesis ..
    qed
  next
    have "\<exists>n \<in> {..length xs}. \<exists>W. W \<in> Rx n"
     using A by simp
    then obtain n where C: "n \<in> {..length xs}" and D: "\<exists>W. W \<in> Rx n" ..
    obtain W where "W \<in> Rx n"
     using D ..
    hence "W \<in> Rx n \<union> Ry n" ..
    hence "\<exists>W. W \<in> Rx n \<union> Ry n" ..
    thus "\<exists>n \<in> {..length xs}. \<exists>W. W \<in> Rx n \<union> Ry n"
     using C ..
  qed
qed

lemma seq_comp_refusals_finite [rule_format]:
  assumes A: "xs \<in> Domain (seq_comp_failures P Q)"
  shows "finite A \<Longrightarrow> (\<forall>x \<in> A. (xs, F x) \<in> seq_comp_failures P Q) \<longrightarrow>
    (xs, \<Union>x \<in> A. F x) \<in> seq_comp_failures P Q"
proof (erule finite_induct, simp, rule_tac [2] impI)
  have "\<exists>X. (xs, X) \<in> seq_comp_failures P Q"
   using A by (simp add: Domain_iff)
  then obtain X where "(xs, X) \<in> seq_comp_failures P Q" ..
  moreover have "{} \<subseteq> X" ..
  ultimately show "(xs, {}) \<in> seq_comp_failures P Q"
   by (rule seq_comp_prop_3)
next
  fix x' A
  assume B: "\<forall>x \<in> insert x' A. (xs, F x) \<in> seq_comp_failures P Q"
  hence "(xs, F x') \<in> seq_comp_failures P Q"
   by simp
  moreover assume "(\<forall>x \<in> A. (xs, F x) \<in> seq_comp_failures P Q) \<longrightarrow>
    (xs, \<Union>x \<in> A. F x) \<in> seq_comp_failures P Q"
  hence "(xs, \<Union>x \<in> A. F x) \<in> seq_comp_failures P Q"
   using B by simp
  ultimately have "(xs, F x' \<union> (\<Union>x \<in> A. F x)) \<in> seq_comp_failures P Q"
   by (rule SCF_R4)
  thus "(xs, \<Union>x \<in> insert x' A. F x) \<in> seq_comp_failures P Q"
   by simp
qed

lemma seq_comp_refusals_2:
  assumes
    A: "ref_union_closed P" and
    B: "ref_union_closed Q" and
    C: "xs \<in> Domain (seq_comp_failures P Q)" and
    D: "X = (\<Union>n \<in> {..length xs}. \<Union>W \<in> R n. W) \<and>
      (\<forall>W \<in> R 0.
        xs \<notin> sentences P \<and> None \<notin> set xs \<and> (xs, W) \<in> failures P \<or>
        xs \<in> sentences P \<and> (\<exists>U V. (xs, U) \<in> failures P \<and> ([], V) \<in> failures Q \<and>
          W = insert None U \<inter> V)) \<and>
      (\<forall>n \<in> {0<..length xs}. \<forall>W \<in> R n.
        take (length xs - n) xs \<in> sentences P \<and>
        (drop (length xs - n) xs, W) \<in> failures Q)"
  shows "(xs, X) \<in> seq_comp_failures P Q"
proof -
  have "\<exists>Y. (xs, Y) \<in> seq_comp_failures P Q"
   using C by (simp add: Domain_iff)
  then obtain Y where "(xs, Y) \<in> seq_comp_failures P Q" ..
  moreover have "{} \<subseteq> Y" ..
  ultimately have E: "(xs, {}) \<in> seq_comp_failures P Q"
   by (rule seq_comp_prop_3)
  have "(xs, \<Union>W \<in> R 0. W) \<in> seq_comp_failures P Q"
  proof (cases "\<exists>W. W \<in> R 0", cases "xs \<in> sentences P")
    assume "\<not> (\<exists>W. W \<in> R 0)"
    thus ?thesis
     using E by simp
  next
    assume
      F: "\<exists>W. W \<in> R 0" and
      G: "xs \<notin> sentences P"
    have H: "\<forall>W \<in> R 0. None \<notin> set xs \<and> (xs, W) \<in> failures P"
     using D and G by simp
    show ?thesis
    proof (rule SCF_R1 [OF G])
      have "\<forall>xs A. (\<exists>W. W \<in> A) \<longrightarrow> (\<forall>W \<in> A. (xs, W) \<in> failures P) \<longrightarrow>
        (xs, \<Union>W \<in> A. W) \<in> failures P"
       using A by (simp add: ref_union_closed_def)
      hence "(\<exists>W. W \<in> R 0) \<longrightarrow> (\<forall>W \<in> R 0. (xs, W) \<in> failures P) \<longrightarrow>
        (xs, \<Union>W \<in> R 0. W) \<in> failures P"
       by blast
      thus "(xs, \<Union>W \<in> R 0. W) \<in> failures P"
       using F and H by simp
    next
      obtain W where "W \<in> R 0" using F ..
      thus "None \<notin> set xs"
       using H by simp
    qed
  next
    assume
      F: "\<exists>W. W \<in> R 0" and
      G: "xs \<in> sentences P"
    have "\<forall>W \<in> R 0. \<exists>U V. (xs, U) \<in> failures P \<and> ([], V) \<in> failures Q \<and>
      W = insert None U \<inter> V"
     using D and G by simp
    hence "\<exists>F. \<forall>W \<in> R 0. \<exists>V. (xs, F W) \<in> failures P \<and> ([], V) \<in> failures Q \<and>
      W = insert None (F W) \<inter> V"
     by (rule bchoice)
    then obtain F where "\<forall>W \<in> R 0.
      \<exists>V. (xs, F W) \<in> failures P \<and> ([], V) \<in> failures Q \<and>
        W = insert None (F W) \<inter> V" ..
    hence "\<exists>G. \<forall>W \<in> R 0. (xs, F W) \<in> failures P \<and> ([], G W) \<in> failures Q \<and>
      W = insert None (F W) \<inter> G W"
     by (rule bchoice)
    then obtain G where H: "\<forall>W \<in> R 0.
      (xs, F W) \<in> failures P \<and> ([], G W) \<in> failures Q \<and>
        W = insert None (F W) \<inter> G W" ..
    have "(xs, insert None (\<Union>W \<in> R 0. F W) \<inter> (\<Union>W \<in> R 0. G W))
      \<in> seq_comp_failures P Q"
      (is "(_, ?S) \<in> _")
    proof (rule SCF_R2 [OF G])
      have "\<forall>xs A. (\<exists>X. X \<in> A) \<longrightarrow> (\<forall>X \<in> A. (xs, X) \<in> failures P) \<longrightarrow>
        (xs, \<Union>X \<in> A. X) \<in> failures P"
       using A by (simp add: ref_union_closed_def)
      hence "(\<exists>X. X \<in> F ` R 0) \<longrightarrow> (\<forall>X \<in> F ` R 0. (xs, X) \<in> failures P) \<longrightarrow>
        (xs, \<Union>X \<in> F ` R 0. X) \<in> failures P"
        (is "?A \<longrightarrow> ?B \<longrightarrow> ?C")
       by (erule_tac x = xs in allE, erule_tac x = "F ` R 0" in allE)
      moreover obtain W where "W \<in> R 0" using F ..
      hence ?A
      proof (simp add: image_def, rule_tac x = "F W" in exI)
      qed (rule bexI, simp)
      ultimately have "?B \<longrightarrow> ?C" ..
      moreover have ?B
      proof (rule ballI, simp add: image_def, erule bexE)
        fix W X
        assume "W \<in> R 0"
        hence "(xs, F W) \<in> failures P"
         using H by simp
        moreover assume "X = F W"
        ultimately show "(xs, X) \<in> failures P"
         by simp
      qed
      ultimately have ?C ..
      thus "(xs, \<Union>W \<in> R 0. F W) \<in> failures P"
       by simp
    next
      have "\<forall>xs A. (\<exists>Y. Y \<in> A) \<longrightarrow> (\<forall>Y \<in> A. (xs, Y) \<in> failures Q) \<longrightarrow>
        (xs, \<Union>Y \<in> A. Y) \<in> failures Q"
       using B by (simp add: ref_union_closed_def)
      hence "(\<exists>Y. Y \<in> G ` R 0) \<longrightarrow> (\<forall>Y \<in> G ` R 0. ([], Y) \<in> failures Q) \<longrightarrow>
        ([], \<Union>Y \<in> G ` R 0. Y) \<in> failures Q"
        (is "?A \<longrightarrow> ?B \<longrightarrow> ?C")
       by (erule_tac x = "[]" in allE, erule_tac x = "G ` R 0" in allE)
      moreover obtain W where "W \<in> R 0" using F ..
      hence ?A
      proof (simp add: image_def, rule_tac x = "G W" in exI)
      qed (rule bexI, simp)
      ultimately have "?B \<longrightarrow> ?C" ..
      moreover have ?B
      proof (rule ballI, simp add: image_def, erule bexE)
        fix W Y
        assume "W \<in> R 0"
        hence "([], G W) \<in> failures Q"
         using H by simp
        moreover assume "Y = G W"
        ultimately show "([], Y) \<in> failures Q"
         by simp
      qed
      ultimately have ?C ..
      thus "([], \<Union>W \<in> R 0. G W) \<in> failures Q"
       by simp
    qed
    moreover have "(\<Union>W \<in> R 0. W) \<subseteq> ?S"
    proof (rule subsetI, simp, erule bexE)
      fix x W
      assume I: "W \<in> R 0"
      hence "W = insert None (F W) \<inter> G W"
       using H by simp
      moreover assume "x \<in> W"
      ultimately have "x \<in> insert None (F W) \<inter> G W"
       by simp
      thus "(x = None \<or> (\<exists>W \<in> R 0. x \<in> F W)) \<and> (\<exists>W \<in> R 0. x \<in> G W)"
        (is "?A \<and> ?B")
      proof (rule IntE, simp)
        assume "x = None \<or> x \<in> F W"
        moreover {
          assume "x = None"
          hence ?A ..
        }
        moreover {
          assume "x \<in> F W"
          hence "\<exists>W \<in> R 0. x \<in> F W" using I ..
          hence ?A ..
        }
        ultimately have ?A ..
        moreover assume "x \<in> G W"
        hence ?B using I ..
        ultimately show ?thesis ..
      qed
    qed
    ultimately show ?thesis
     by (rule seq_comp_prop_3)
  qed
  moreover have "\<forall>n \<in> {0<..length xs}.
    (xs, \<Union>W \<in> R n. W) \<in> seq_comp_failures P Q"
  proof
    fix n
    assume F: "n \<in> {0<..length xs}"
    hence G: "\<forall>W \<in> R n.
      take (length xs - n) xs \<in> sentences P \<and>
      (drop (length xs - n) xs, W) \<in> failures Q"
     using D by simp
    show "(xs, \<Union>W \<in> R n. W) \<in> seq_comp_failures P Q"
    proof (cases "\<exists>W. W \<in> R n")
      case False
      thus ?thesis
       using E by simp
    next
      case True
      have "(take (length xs - n) xs @ drop (length xs - n) xs, \<Union>W \<in> R n. W)
        \<in> seq_comp_failures P Q"
      proof (rule SCF_R3)
        obtain W where "W \<in> R n" using True ..
        thus "take (length xs - n) xs \<in> sentences P"
         using G by simp
      next
        have "\<forall>xs A. (\<exists>W. W \<in> A) \<longrightarrow> (\<forall>W \<in> A. (xs, W) \<in> failures Q) \<longrightarrow>
          (xs, \<Union>W \<in> A. W) \<in> failures Q"
         using B by (simp add: ref_union_closed_def)
        hence "(\<exists>W. W \<in> R n) \<longrightarrow>
          (\<forall>W \<in> R n. (drop (length xs - n) xs, W) \<in> failures Q) \<longrightarrow>
          (drop (length xs - n) xs, \<Union>W \<in> R n. W) \<in> failures Q"
         by blast
        thus "(drop (length xs - n) xs, \<Union>W \<in> R n. W) \<in> failures Q"
         using G and True by simp
      next
        show "drop (length xs - n) xs \<noteq> []"
         using F by (simp, arith)
      qed
      thus ?thesis
       by simp
    qed
  qed
  ultimately have F: "\<forall>n \<in> {..length xs}.
    (xs, \<Union>W \<in> R n. W) \<in> seq_comp_failures P Q"
   by auto
  have "(xs, \<Union>n \<in> {..length xs}. \<Union>W \<in> R n. W) \<in> seq_comp_failures P Q"
  proof (rule seq_comp_refusals_finite [OF C], simp)
    fix n
    assume "n \<in> {..length xs}"
    with F show "(xs, \<Union>W \<in> R n. W) \<in> seq_comp_failures P Q" ..
  qed
  moreover have "X = (\<Union>n \<in> {..length xs}. \<Union>W \<in> R n. W)"
   using D by simp
  ultimately show ?thesis
   by simp
qed

text \<open>
\null

In what follows, the previous results are used to prove that refusals union closure, weak
sequentiality, and sequentiality are conserved under sequential composition. The proof of the first
of these lemmas makes use of the axiom of choice.

Since the target security conservation theorem, in addition to the security of both of the processes
to be composed, also requires to assume that the first process be refusals union closed and
sequential (cf. below), these further conservation lemmas will permit to generalize the theorem to
the sequential composition of an arbitrary list of processes.

\null
\<close>

lemma seq_comp_ref_union_closed:
  assumes
    WS: "weakly_sequential P" and
    A: "ref_union_closed P" and
    B: "ref_union_closed Q"
  shows "ref_union_closed (P ; Q)"
proof (simp only: ref_union_closed_def seq_comp_failures [OF WS],
 (rule allI)+, (rule impI)+, erule exE)
  fix xs A X'
  assume
    C: "\<forall>X \<in> A. (xs, X) \<in> seq_comp_failures P Q" and
    D: "X' \<in> A"
  have "\<forall>X \<in> A. \<exists>R.
    X = (\<Union>n \<in> {..length xs}. \<Union>W \<in> R n. W) \<and>
    (\<forall>W \<in> R 0.
      xs \<notin> sentences P \<and> None \<notin> set xs \<and> (xs, W) \<in> failures P \<or>
      xs \<in> sentences P \<and> (\<exists>U V. (xs, U) \<in> failures P \<and> ([], V) \<in> failures Q \<and>
        W = insert None U \<inter> V)) \<and>
    (\<forall>n \<in> {0<..length xs}. \<forall>W \<in> R n.
      take (length xs - n) xs \<in> sentences P \<and>
      (drop (length xs - n) xs, W) \<in> failures Q)"
    (is "\<forall>X \<in> A. \<exists>R. ?T R X")
  proof
    fix X
    assume "X \<in> A"
    with C have "(xs, X) \<in> seq_comp_failures P Q" ..
    hence "\<exists>R. X = (\<Union>n \<in> {..length xs}. \<Union>W \<in> R n. W) \<and>
      (\<forall>W \<in> R 0.
        xs \<notin> sentences P \<and> None \<notin> set xs \<and> (xs, W) \<in> failures P \<or>
        xs \<in> sentences P \<and> (\<exists>U V. (xs, U) \<in> failures P \<and> ([], V) \<in> failures Q \<and>
          W = insert None U \<inter> V)) \<and>
      (\<forall>n \<in> {0<..length xs}. \<forall>W \<in> R n.
        take (length xs - n) xs \<in> sentences P \<and>
        (drop (length xs - n) xs, W) \<in> failures Q) \<and>
      (\<exists>n \<in> {..length xs}. \<exists>W. W \<in> R n)"
     by (rule seq_comp_refusals_1)
    thus "\<exists>R. ?T R X"
     by blast
  qed
  hence "\<exists>R. \<forall>X \<in> A. ?T (R X) X"
   by (rule bchoice)
  then obtain R where E: "\<forall>X \<in> A. ?T (R X) X" ..
  have "xs \<in> Domain (seq_comp_failures P Q)"
  proof (simp add: Domain_iff)
    have "(xs, X') \<in> seq_comp_failures P Q"
     using C and D ..
    thus "\<exists>X. (xs, X) \<in> seq_comp_failures P Q" ..
  qed
  moreover have "?T (\<lambda>n. \<Union>X \<in> A. R X n) (\<Union>X \<in> A. X)"
  proof (rule conjI, rule_tac [2] conjI)
    show "(\<Union>X \<in> A. X) = (\<Union>n \<in> {..length xs}. \<Union>W \<in> \<Union>X \<in> A. R X n. W)"
    proof (rule equalityI, rule_tac [!] subsetI, simp_all,
     erule bexE, (erule_tac [2] bexE)+)
      fix x X
      assume F: "X \<in> A"
      hence "X = (\<Union>n \<in> {..length xs}. \<Union>W \<in> R X n. W)"
       using E by simp
      moreover assume "x \<in> X"
      ultimately have "x \<in> (\<Union>n \<in> {..length xs}. \<Union>W \<in> R X n. W)"
       by simp
      hence "\<exists>n \<in> {..length xs}. \<exists>W \<in> R X n. x \<in> W"
       by simp
      hence "\<exists>X \<in> A. \<exists>n \<in> {..length xs}. \<exists>W \<in> R X n. x \<in> W"
       using F ..
      thus "\<exists>n \<in> {..length xs}. \<exists>X \<in> A. \<exists>W \<in> R X n. x \<in> W"
       by blast
    next
      fix x n X W
      assume F: "X \<in> A"
      hence G: "X = (\<Union>n \<in> {..length xs}. \<Union>W \<in> R X n. W)"
       using E by simp
      assume "x \<in> W" and "W \<in> R X n"
      hence "\<exists>W \<in> R X n. x \<in> W" ..
      moreover assume "n \<in> {..length xs}"
      ultimately have "\<exists>n \<in> {..length xs}. \<exists>W \<in> R X n. x \<in> W" ..
      hence "x \<in> (\<Union>n \<in> {..length xs}. \<Union>W \<in> R X n. W)"
       by simp
      hence "x \<in> X"
       by (subst G)
      thus "\<exists>X \<in> A. x \<in> X"
       using F ..
    qed
  next
    show "\<forall>W \<in> \<Union>X \<in> A. R X 0.
      xs \<notin> sentences P \<and> None \<notin> set xs \<and> (xs, W) \<in> failures P \<or>
      xs \<in> sentences P \<and> (\<exists>U V. (xs, U) \<in> failures P \<and> ([], V) \<in> failures Q \<and>
        W = insert None U \<inter> V)"
      (is "\<forall>W \<in> _. ?T W")
    proof (rule ballI, simp only: UN_iff, erule bexE)
      fix W X
      assume "X \<in> A"
      hence "\<forall>W \<in> R X 0. ?T W"
       using E by simp
      moreover assume "W \<in> R X 0"
      ultimately show "?T W" ..
    qed
  next
    show "\<forall>n \<in> {0<..length xs}. \<forall>W \<in> \<Union>X \<in> A. R X n.
      take (length xs - n) xs \<in> sentences P \<and>
      (drop (length xs - n) xs, W) \<in> failures Q"
      (is "\<forall>n \<in> _. \<forall>W \<in> _. ?T n W")
    proof ((rule ballI)+, simp only: UN_iff, erule bexE)
      fix n W X
      assume "X \<in> A"
      hence "\<forall>n \<in> {0<..length xs}. \<forall>W \<in> R X n. ?T n W"
       using E by simp
      moreover assume "n \<in> {0<..length xs}"
      ultimately have "\<forall>W \<in> R X n. ?T n W" ..
      moreover assume "W \<in> R X n"
      ultimately show "?T n W" ..
    qed
  qed
  ultimately show "(xs, \<Union>X \<in> A. X) \<in> seq_comp_failures P Q"
   by (rule seq_comp_refusals_2 [OF A B])
qed

lemma seq_comp_weakly_sequential:
  assumes
    A: "weakly_sequential P" and
    B: "weakly_sequential Q"
  shows "weakly_sequential (P ; Q)"
proof (subst weakly_sequential_def, rule ballI, drule traces_failures,
 subst (asm) seq_comp_failures [OF A], erule seq_comp_failures.induct, simp_all)
  fix xs :: "'a option list"
  assume C: "None \<notin> set xs"
  show "None \<notin> set (butlast xs)"
  proof
    assume "None \<in> set (butlast xs)"
    hence "None \<in> set xs"
     by (rule in_set_butlastD)
    thus False
     using C by contradiction
  qed
next
  fix xs
  assume "xs \<in> sentences P"
  with A have C: "None \<notin> set xs"
   by (rule weakly_seq_sentences_none)
  show "None \<notin> set (butlast xs)"
  proof
    assume "None \<in> set (butlast xs)"
    hence "None \<in> set xs"
     by (rule in_set_butlastD)
    thus False
     using C by contradiction
  qed
next
  fix xs ys Y
  assume "xs \<in> sentences P"
  with A have C: "None \<notin> set xs"
   by (rule weakly_seq_sentences_none)
  have "\<forall>xs \<in> traces Q. None \<notin> set (butlast xs)"
   using B by (simp add: weakly_sequential_def)
  moreover assume "(ys, Y) \<in> failures Q"
  hence "ys \<in> traces Q"
   by (rule failures_traces)
  ultimately have "None \<notin> set (butlast ys)" ..
  hence "None \<notin> set (xs @ butlast ys)"
   using C by simp
  moreover assume "ys \<noteq> []"
  hence "butlast (xs @ ys) = xs @ butlast ys"
   by (simp add: butlast_append)
  ultimately show "None \<notin> set (butlast (xs @ ys))"
   by simp
qed

lemma seq_comp_sequential:
  assumes
    A: "sequential P" and
    B: "sequential Q"
  shows "sequential (P ; Q)"
proof (subst sequential_def, rule conjI)
  have "weakly_sequential P"
   using A by (rule seq_implies_weakly_seq)
  moreover have "weakly_sequential Q"
   using B by (rule seq_implies_weakly_seq)
  ultimately have "weakly_sequential (P ; Q)"
   by (rule seq_comp_weakly_sequential)
  thus "\<forall>xs \<in> traces (P ; Q). None \<notin> set (butlast xs)"
   by (simp add: weakly_sequential_def)
next
  have C: "weakly_sequential P"
   using A by (rule seq_implies_weakly_seq)
  show "\<forall>xs \<in> sentences (P ; Q). next_events (P ; Q) xs = {None}"
  proof (rule ballI, simp add: sentences_def next_events_def, rule equalityI,
   rule_tac [!] subsetI, simp_all, (drule traces_failures)+,
   simp add: seq_comp_failures [OF C])
    fix xs x
    assume
      D: "(xs @ [None], {}) \<in> seq_comp_failures P Q" and
      E: "(xs @ [x], {}) \<in> seq_comp_failures P Q"
    have "\<exists>R. {} = (\<Union>n \<in> {..length (xs @ [None])}. \<Union>W \<in> R n. W) \<and>
      (\<forall>W \<in> R 0.
        xs @ [None] \<notin> sentences P \<and>
          None \<notin> set (xs @ [None]) \<and> (xs @ [None], W) \<in> failures P \<or>
        xs @ [None] \<in> sentences P \<and>
          (\<exists>U V. (xs @ [None], U) \<in> failures P \<and> ([], V) \<in> failures Q \<and>
            W = insert None U \<inter> V)) \<and>
      (\<forall>n \<in> {0<..length (xs @ [None])}. \<forall>W \<in> R n.
        take (length (xs @ [None]) - n) (xs @ [None]) \<in> sentences P \<and>
        (drop (length (xs @ [None]) - n) (xs @ [None]), W) \<in> failures Q) \<and>
      (\<exists>n \<in> {..length (xs @ [None])}. \<exists>W. W \<in> R n)"
      (is "\<exists>R. ?T R")
     using D by (rule seq_comp_refusals_1)
    then obtain R where F: "?T R" ..
    hence "\<exists>n \<in> {..Suc (length xs)}. \<exists>W. W \<in> R n"
     by simp
    moreover have "R 0 = {}"
    proof (rule equals0I)
      fix W
      assume "W \<in> R 0"
      hence "xs @ [None] \<in> sentences P"
       using F by simp
      with C have "None \<notin> set (xs @ [None])"
       by (rule weakly_seq_sentences_none)
      thus False
       by simp
    qed
    ultimately have "\<exists>n \<in> {0<..Suc (length xs)}. \<exists>W. W \<in> R n"
    proof -
      assume "\<exists>n \<in> {..Suc (length xs)}. \<exists>W. W \<in> R n"
      then obtain n where G: "n \<in> {..Suc (length xs)}" and H: "\<exists>W. W \<in> R n" ..
      assume I: "R 0 = {}"
      show "\<exists>n \<in> {0<..Suc (length xs)}. \<exists>W. W \<in> R n"
      proof (cases n)
        case 0
        hence "\<exists>W. W \<in> R 0"
         using H by simp
        then obtain W where "W \<in> R 0" ..
        moreover have "W \<notin> R 0"
         using I by (rule equals0D)
        ultimately show ?thesis
         by contradiction
      next
        case (Suc m)
        hence "n \<in> {0<..Suc (length xs)}"
         using G by simp
        with H show ?thesis ..
      qed
    qed
    then obtain n and W where G: "n \<in> {0<..Suc (length xs)}" and "W \<in> R n"
     by blast
    hence
     "take (Suc (length xs) - n) (xs @ [None]) \<in> sentences P \<and>
      (drop (Suc (length xs) - n) (xs @ [None]), W) \<in> failures Q"
     using F by simp
    moreover have H: "Suc (length xs) - n \<le> length xs"
     using G by (simp, arith)
    ultimately have I:
     "take (Suc (length xs) - n) xs \<in> sentences P \<and>
      (drop (Suc (length xs) - n) xs @ [None], W) \<in> failures Q"
     by simp
    have "\<exists>R. {} = (\<Union>n \<in> {..length (xs @ [x])}. \<Union>W \<in> R n. W) \<and>
      (\<forall>W \<in> R 0.
        xs @ [x] \<notin> sentences P \<and>
          None \<notin> set (xs @ [x]) \<and> (xs @ [x], W) \<in> failures P \<or>
        xs @ [x] \<in> sentences P \<and>
          (\<exists>U V. (xs @ [x], U) \<in> failures P \<and> ([], V) \<in> failures Q \<and>
            W = insert None U \<inter> V)) \<and>
      (\<forall>n \<in> {0<..length (xs @ [x])}. \<forall>W \<in> R n.
        take (length (xs @ [x]) - n) (xs @ [x]) \<in> sentences P \<and>
        (drop (length (xs @ [x]) - n) (xs @ [x]), W) \<in> failures Q) \<and>
      (\<exists>n \<in> {..length (xs @ [x])}. \<exists>W. W \<in> R n)"
      (is "\<exists>R. ?T R")
     using E by (rule seq_comp_refusals_1)
    then obtain R' where J: "?T R'" ..
    hence "\<exists>n \<in> {..Suc (length xs)}. \<exists>W. W \<in> R' n"
     by simp
    then obtain n' where K: "n' \<in> {..Suc (length xs)}" and L: "\<exists>W. W \<in> R' n'" ..
    have "n' = 0 \<or> n' \<in> {0<..Suc (length xs)}"
     using K by auto
    thus "x = None"
    proof
      assume "n' = 0"
      hence "\<exists>W. W \<in> R' 0"
       using L by simp
      then obtain W' where "W' \<in> R' 0" ..
      hence
       "xs @ [x] \<notin> sentences P \<and>
          None \<notin> set (xs @ [x]) \<and> (xs @ [x], W') \<in> failures P \<or>
        xs @ [x] \<in> sentences P \<and>
          (\<exists>U V. (xs @ [x], U) \<in> failures P \<and> ([], V) \<in> failures Q \<and>
            W' = insert None U \<inter> V)"
       using J by simp
      hence M: "xs @ [x] \<in> traces P \<and> None \<notin> set (xs @ [x])"
      proof (cases "xs @ [x] \<in> sentences P", simp_all, (erule_tac [2] conjE)+,
       simp_all)
        case False
        assume "(xs @ [x], W') \<in> failures P"
        thus "xs @ [x] \<in> traces P"
         by (rule failures_traces)
      next
        case True
        hence "(xs @ [x]) @ [None] \<in> traces P"
         by (simp add: sentences_def)
        hence "xs @ [x] \<in> traces P"
         by (rule process_rule_2_traces)
        moreover have "None \<notin> set (xs @ [x])"
         using C and True by (rule weakly_seq_sentences_none)
        ultimately show "xs @ [x] \<in> traces P \<and> None \<noteq> x \<and> None \<notin> set xs"
         by simp
      qed
      have "xs @ [x] = take (Suc (length xs) - n) (xs @ [x]) @
        drop (Suc (length xs) - n) (xs @ [x])"
       by (simp only: append_take_drop_id)
      hence "xs @ [x] = take (Suc (length xs) - n) xs @
        drop (Suc (length xs) - n) xs @ [x]"
       using H by simp
      moreover have "\<exists>y ys. drop (Suc (length xs) - n) xs @ [x] = y # ys"
       by (cases "drop (Suc (length xs) - n) xs @ [x]", simp_all)
      then obtain y and ys where "drop (Suc (length xs) - n) xs @ [x] = y # ys"
       by blast
      ultimately have N: "xs @ [x] = take (Suc (length xs) - n) xs @ y # ys"
       by simp
      have "take (Suc (length xs) - n) xs \<in> sentences P"
       using I ..
      moreover have "take (Suc (length xs) - n) xs @ y # ys \<in> traces P"
       using M and N by simp
      ultimately have "y = None"
       by (rule seq_sentences_none [OF A])
      moreover have "y \<noteq> None"
       using M and N by (rule_tac not_sym, simp)
      ultimately show ?thesis
       by contradiction
    next
      assume M: "n' \<in> {0<..Suc (length xs)}"
      moreover obtain W' where "W' \<in> R' n'"
       using L ..
      ultimately have
       "take (Suc (length xs) - n') (xs @ [x]) \<in> sentences P \<and>
        (drop (Suc (length xs) - n') (xs @ [x]), W') \<in> failures Q"
       using J by simp
      moreover have N: "Suc (length xs) - n' \<le> length xs"
       using M by (simp, arith)
      ultimately have O:
       "take (Suc (length xs) - n') xs \<in> sentences P \<and>
        (drop (Suc (length xs) - n') xs @ [x], W') \<in> failures Q"
       by simp
      moreover have "n = n'"
      proof (rule ccontr, simp add: neq_iff, erule disjE)
        assume P: "n < n'"
        have "take (Suc (length xs) - n) xs =
          take (Suc (length xs) - n') (take (Suc (length xs) - n) xs) @
          drop (Suc (length xs) - n') (take (Suc (length xs) - n) xs)"
         by (simp only: append_take_drop_id)
        also have "\<dots> =
          take (Suc (length xs) - n') xs @
          drop (Suc (length xs) - n') (take (Suc (length xs) - n) xs)"
         using P by (simp add: min_def)
        also have "\<dots> =
          take (Suc (length xs) - n') xs @
          take (n' - n) (drop (Suc (length xs) - n') xs)"
         using M by (subst drop_take, simp)
        finally have "take (Suc (length xs) - n) xs =
          take (Suc (length xs) - n') xs @
          take (n' - n) (drop (Suc (length xs) - n') xs)" .
        moreover have "take (n' - n) (drop (Suc (length xs) - n') xs) \<noteq> []"
        proof (rule_tac notI, simp, erule disjE)
          assume "n' \<le> n"
          thus False
           using P by simp
        next
          assume "length xs \<le> Suc (length xs) - n'"
          moreover have "Suc (length xs) - n' < Suc (length xs) - n"
           using M and P by simp
          hence "Suc (length xs) - n' < length xs"
           using H by simp
          ultimately show False
           by simp
        qed
        hence "\<exists>y ys. take (n' - n) (drop (Suc (length xs) - n') xs) = y # ys"
         by (cases "take (n' - n) (drop (Suc (length xs) - n') xs)", simp_all)
        then obtain y and ys where
         "take (n' - n) (drop (Suc (length xs) - n') xs) = y # ys"
         by blast
        ultimately have Q: "take (Suc (length xs) - n) xs =
          take (Suc (length xs) - n') xs @ y # ys"
         by simp
        have "take (Suc (length xs) - n') xs \<in> sentences P"
         using O ..
        moreover have R: "take (Suc (length xs) - n) xs \<in> sentences P"
         using I ..
        hence "take (Suc (length xs) - n) xs @ [None] \<in> traces P"
         by (simp add: sentences_def)
        hence "take (Suc (length xs) - n) xs \<in> traces P"
         by (rule process_rule_2_traces)
        hence "take (Suc (length xs) - n') xs @ y # ys \<in> traces P"
         using Q by simp
        ultimately have "y = None"
         by (rule seq_sentences_none [OF A])
        moreover have "None \<notin> set (take (Suc (length xs) - n) xs)"
         using C and R by (rule weakly_seq_sentences_none)
        hence "y \<noteq> None"
         using Q by (rule_tac not_sym, simp)
        ultimately show False
         by contradiction
      next
        assume P: "n' < n"
        have "take (Suc (length xs) - n') xs =
          take (Suc (length xs) - n) (take (Suc (length xs) - n') xs) @
          drop (Suc (length xs) - n) (take (Suc (length xs) - n') xs)"
         by (simp only: append_take_drop_id)
        also have "\<dots> =
          take (Suc (length xs) - n) xs @
          drop (Suc (length xs) - n) (take (Suc (length xs) - n') xs)"
         using P by (simp add: min_def)
        also have "\<dots> =
          take (Suc (length xs) - n) xs @
          take (n - n') (drop (Suc (length xs) - n) xs)"
         using G by (subst drop_take, simp)
        finally have "take (Suc (length xs) - n') xs =
          take (Suc (length xs) - n) xs @
          take (n - n') (drop (Suc (length xs) - n) xs)" .
        moreover have "take (n - n') (drop (Suc (length xs) - n) xs) \<noteq> []"
        proof (rule_tac notI, simp, erule disjE)
          assume "n \<le> n'"
          thus False
           using P by simp
        next
          assume "length xs \<le> Suc (length xs) - n"
          moreover have "Suc (length xs) - n < Suc (length xs) - n'"
           using G and P by simp
          hence "Suc (length xs) - n < length xs"
           using N by simp
          ultimately show False
           by simp
        qed
        hence "\<exists>y ys. take (n - n') (drop (Suc (length xs) - n) xs) = y # ys"
         by (cases "take (n - n') (drop (Suc (length xs) - n) xs)", simp_all)
        then obtain y and ys where
         "take (n - n') (drop (Suc (length xs) - n) xs) = y # ys"
         by blast
        ultimately have Q: "take (Suc (length xs) - n') xs =
          take (Suc (length xs) - n) xs @ y # ys"
         by simp
        have "take (Suc (length xs) - n) xs \<in> sentences P"
         using I ..
        moreover have R: "take (Suc (length xs) - n') xs \<in> sentences P"
         using O ..
        hence "take (Suc (length xs) - n') xs @ [None] \<in> traces P"
         by (simp add: sentences_def)
        hence "take (Suc (length xs) - n') xs \<in> traces P"
         by (rule process_rule_2_traces)
        hence "take (Suc (length xs) - n) xs @ y # ys \<in> traces P"
         using Q by simp
        ultimately have "y = None"
         by (rule seq_sentences_none [OF A])
        moreover have "None \<notin> set (take (Suc (length xs) - n') xs)"
         using C and R by (rule weakly_seq_sentences_none)
        hence "y \<noteq> None"
         using Q by (rule_tac not_sym, simp)
        ultimately show False
         by contradiction
      qed
      ultimately have "(drop (Suc (length xs) - n) xs @ [x], W') \<in> failures Q"
       by simp
      hence P: "drop (Suc (length xs) - n) xs @ [x] \<in> traces Q"
       by (rule failures_traces)
      have "(drop (Suc (length xs) - n) xs @ [None], W) \<in> failures Q"
       using I ..
      hence "drop (Suc (length xs) - n) xs @ [None] \<in> traces Q"
       by (rule failures_traces)
      hence "drop (Suc (length xs) - n) xs \<in> sentences Q"
       by (simp add: sentences_def)
      with B show ?thesis
       using P by (rule seq_sentences_none)
    qed
  qed
qed


subsection "Conservation of noninterference security under sequential composition"

text \<open>
Everything is now ready for proving the target security conservation theorem. The two closure
properties that the definition of noninterference security requires process futures to satisfy, one
for the addition of events into traces and the other for the deletion of events from traces (cf.
\cite{R2}), will be faced separately; here below is the proof of the former property.
Unsurprisingly, rule induction on set @{term seq_comp_failures} is applied, and the closure of the
failures of a secure process under intransitive purge (proven in the previous section) is used to
meet the proof obligations arising from rule \<open>SCF_R3\<close>.

\null
\<close>

lemma seq_comp_secure_aux_1_case_1:
  assumes
    A: "secure_termination I D" and
    B: "sequential P" and
    C: "secure P I D" and
    D: "xs @ y # ys \<notin> sentences P" and
    E: "(xs @ y # ys, X) \<in> failures P" and
    F: "None \<noteq> y" and
    G: "None \<notin> set xs" and
    H: "None \<notin> set ys"
  shows "(xs @ ipurge_tr I D (D y) ys, ipurge_ref I D (D y) ys X)
    \<in> seq_comp_failures P Q"
proof -
  have "(y # ys, X) \<in> futures P xs"
   using E by (simp add: futures_def)
  hence "(ipurge_tr I D (D y) ys, ipurge_ref I D (D y) ys X) \<in>
    futures P xs"
   using C by (simp add: secure_def)
  hence I: "(xs @ ipurge_tr I D (D y) ys, ipurge_ref I D (D y) ys X) \<in>
    failures P"
   by (simp add: futures_def)
  show ?thesis
  proof (cases "xs @ ipurge_tr I D (D y) ys \<in> sentences P",
   cases "(D y, D None) \<in> I \<or> (\<exists>u \<in> sinks I D (D y) ys. (u, D None) \<in> I)",
   simp_all)
    assume "xs @ ipurge_tr I D (D y) ys \<notin> sentences P"
    thus ?thesis using I
    proof (rule SCF_R1, simp add: F G)
      have "set (ipurge_tr I D (D y) ys) \<subseteq> set ys"
       by (rule ipurge_tr_set)
      thus "None \<notin> set (ipurge_tr I D (D y) ys)"
       using H by (rule contra_subsetD)
    qed
  next
    assume
      J: "xs @ ipurge_tr I D (D y) ys \<in> sentences P" and
      K: "(D y, D None) \<in> I \<or> (\<exists>u \<in> sinks I D (D y) ys. (u, D None) \<in> I)"
    have "ipurge_ref I D (D y) ys X = {}"
    proof (rule disjE [OF K], erule_tac [2] bexE)
      assume L: "(D y, D None) \<in> I"
      show ?thesis
      proof (rule ipurge_ref_empty [of "D y"], simp)
        fix x
        have "(D y, D None) \<in> I \<and> y \<noteq> None \<longrightarrow> (\<forall>u \<in> range D. (D y, u) \<in> I)"
         using A by (simp add: secure_termination_def)
        hence "\<forall>u \<in> range D. (D y, u) \<in> I"
         using F and L by simp
        thus "(D y, D x) \<in> I"
         by simp
      qed
    next
      fix u
      assume
        L: "u \<in> sinks I D (D y) ys" and
        M: "(u, D None) \<in> I"
      have "\<exists>y' \<in> set ys. u = D y'"
       using L by (rule sinks_elem)
      then obtain y' where N: "y' \<in> set ys" and O: "u = D y'" ..
      have P: "y' \<noteq> None"
      proof
        assume "y' = None"
        hence "None \<in> set ys"
         using N by simp
        thus False
         using H by contradiction
      qed
      show ?thesis
      proof (rule ipurge_ref_empty [of u], simp add: L)
        fix x
        have "(D y', D None) \<in> I \<and> y' \<noteq> None \<longrightarrow> (\<forall>v \<in> range D. (D y', v) \<in> I)"
         using A by (simp add: secure_termination_def)
        moreover have "(D y', D None) \<in> I"
         using M and O by simp
        ultimately have "\<forall>v \<in> range D. (D y', v) \<in> I"
         using P by simp
        thus "(u, D x) \<in> I"
         using O by simp
      qed
    qed
    thus ?thesis
    proof simp
      have "([], {}) \<in> failures Q"
       by (rule process_rule_1)
      with J and I have "(xs @ ipurge_tr I D (D y) ys,
        insert None (ipurge_ref I D (D y) ys X) \<inter> {}) \<in> seq_comp_failures P Q"
       by (rule SCF_R2)
      thus "(xs @ ipurge_tr I D (D y) ys, {}) \<in> seq_comp_failures P Q"
       by simp
    qed
  next
    assume
      J: "xs @ ipurge_tr I D (D y) ys \<in> sentences P" and
      K: "(D y, D None) \<notin> I \<and> (\<forall>u \<in> sinks I D (D y) ys. (u, D None) \<notin> I)"
    have "(xs @ [y]) @ ys \<in> sentences P"
    proof (simp add: sentences_def del: append_assoc, subst (2) append_assoc,
     rule ipurge_tr_del_traces [OF C, where u = "D y"], simp_all add: K)
      have "(y # ys, X) \<in> futures P xs"
       using E by (simp add: futures_def)
      moreover have "xs @ ipurge_tr I D (D y) ys @ [None] \<in> traces P"
       using J by (simp add: sentences_def)
      hence "(xs @ ipurge_tr I D (D y) ys @ [None], {}) \<in> failures P"
       by (rule traces_failures)
      hence "(ipurge_tr I D (D y) ys @ [None], {}) \<in> futures P xs"
       by (simp add: futures_def)
      ultimately have "(y # ipurge_tr I D (D y) (ipurge_tr I D (D y) ys @ [None]),
        ipurge_ref I D (D y) (ipurge_tr I D (D y) ys @ [None]) {}) \<in> futures P xs"
       using C by (simp add: secure_def del: ipurge_tr.simps)
      hence "(xs @ y # ipurge_tr I D (D y) (ipurge_tr I D (D y) ys @ [None]), {})
        \<in> failures P"
       by (simp add: futures_def ipurge_ref_def)
      moreover have "sinks I D (D y) (ipurge_tr I D (D y) ys) = {}"
       by (rule sinks_idem)
      hence "\<not> ((D y, D None) \<in> I \<or>
        (\<exists>u \<in> sinks I D (D y) (ipurge_tr I D (D y) ys). (u, D None) \<in> I))"
       using K by simp
      hence "D None \<notin> sinks I D (D y) (ipurge_tr I D (D y) ys @ [None])"
       by (simp only: sinks_interference_eq, simp)
      ultimately have "(xs @ y # ipurge_tr I D (D y) (ipurge_tr I D (D y) ys)
        @ [None], {}) \<in> failures P"
       by simp
      hence "(xs @ y # ipurge_tr I D (D y) ys @ [None], {}) \<in> failures P"
       by (simp add: ipurge_tr_idem)
      thus "xs @ y # ipurge_tr I D (D y) ys @ [None] \<in> traces P"
       by (rule failures_traces)
    next
      show "xs @ y # ys \<in> traces P"
       using E by (rule failures_traces)
    qed
    hence "xs @ y # ys \<in> sentences P"
     by simp
    thus ?thesis
     using D by contradiction
  qed
qed

lemma seq_comp_secure_aux_1_case_2:
  assumes
    A: "secure_termination I D" and
    B: "sequential P" and
    C: "secure P I D" and
    D: "secure Q I D" and
    E: "xs @ y # ys \<in> sentences P" and
    F: "(xs @ y # ys, X) \<in> failures P" and
    G: "([], Y) \<in> failures Q"
  shows "(xs @ ipurge_tr I D (D y) ys,
    ipurge_ref I D (D y) ys (insert None X \<inter> Y)) \<in> seq_comp_failures P Q"
proof -
  have "(y # ys, X) \<in> futures P xs"
   using F by (simp add: futures_def)
  hence "(ipurge_tr I D (D y) ys, ipurge_ref I D (D y) ys X)
    \<in> futures P xs"
   using C by (simp add: secure_def)
  hence H: "(xs @ ipurge_tr I D (D y) ys, ipurge_ref I D (D y) ys X)
    \<in> failures P"
   by (simp add: futures_def)
  have "weakly_sequential P"
   using B by (rule seq_implies_weakly_seq)
  hence I: "None \<notin> set (xs @ y # ys)"
   using E by (rule weakly_seq_sentences_none)
  show ?thesis
  proof (cases "xs @ ipurge_tr I D (D y) ys \<in> sentences P",
   case_tac [2] "(D y, D None) \<in> I \<or> (\<exists>u \<in> sinks I D (D y) ys. (u, D None) \<in> I)",
   simp_all)
    assume J: "xs @ ipurge_tr I D (D y) ys \<in> sentences P"
    have "ipurge_ref I D (D y) ys Y \<subseteq> Y"
     by (rule ipurge_ref_subset)
    with G have "([], ipurge_ref I D (D y) ys Y) \<in> failures Q"
     by (rule process_rule_3)
    with J and H have "(xs @ ipurge_tr I D (D y) ys,
      insert None (ipurge_ref I D (D y) ys X) \<inter> ipurge_ref I D (D y) ys Y)
      \<in> seq_comp_failures P Q"
     by (rule SCF_R2)
    moreover have
     "ipurge_ref I D (D y) ys (insert None X) \<inter> ipurge_ref I D (D y) ys Y \<subseteq>
      insert None (ipurge_ref I D (D y) ys X) \<inter> ipurge_ref I D (D y) ys Y"
    proof (rule subsetI, simp del: insert_iff, erule conjE)
      fix x
      have "ipurge_ref I D (D y) ys (insert None X) \<subseteq>
        insert None (ipurge_ref I D (D y) ys X)"
       by (rule ipurge_ref_subset_insert)
      moreover assume "x \<in> ipurge_ref I D (D y) ys (insert None X)"
      ultimately show "x \<in> insert None (ipurge_ref I D (D y) ys X)" ..
    qed
    ultimately have "(xs @ ipurge_tr I D (D y) ys,
      ipurge_ref I D (D y) ys (insert None X) \<inter> ipurge_ref I D (D y) ys Y)
      \<in> seq_comp_failures P Q"
     by (rule seq_comp_prop_3)
    thus ?thesis
     by (simp add: ipurge_ref_distrib_inter)
  next
    assume
      J: "xs @ ipurge_tr I D (D y) ys \<notin> sentences P" and
      K: "(D y, D None) \<in> I \<or> (\<exists>u \<in> sinks I D (D y) ys. (u, D None) \<in> I)"
    have "ipurge_ref I D (D y) ys (insert None X \<inter> Y) = {}"
    proof (rule disjE [OF K], erule_tac [2] bexE)
      assume L: "(D y, D None) \<in> I"
      show ?thesis
      proof (rule ipurge_ref_empty [of "D y"], simp)
        fix x
        have "(D y, D None) \<in> I \<and> y \<noteq> None \<longrightarrow> (\<forall>u \<in> range D. (D y, u) \<in> I)"
         using A by (simp add: secure_termination_def)
        moreover have "y \<noteq> None"
         using I by (rule_tac not_sym, simp)
        ultimately have "\<forall>u \<in> range D. (D y, u) \<in> I"
         using L by simp
        thus "(D y, D x) \<in> I"
         by simp
      qed
    next
      fix u
      assume
        L: "u \<in> sinks I D (D y) ys" and
        M: "(u, D None) \<in> I"
      have "\<exists>y' \<in> set ys. u = D y'"
       using L by (rule sinks_elem)
      then obtain y' where N: "y' \<in> set ys" and O: "u = D y'" ..
      have P: "y' \<noteq> None"
      proof
        assume "y' = None"
        hence "None \<in> set ys"
         using N by simp
        moreover have "None \<notin> set ys"
         using I by simp
        ultimately show False
         by contradiction
      qed
      show ?thesis
      proof (rule ipurge_ref_empty [of u], simp add: L)
        fix x
        have "(D y', D None) \<in> I \<and> y' \<noteq> None \<longrightarrow> (\<forall>v \<in> range D. (D y', v) \<in> I)"
         using A by (simp add: secure_termination_def)
        moreover have "(D y', D None) \<in> I"
         using M and O by simp
        ultimately have "\<forall>v \<in> range D. (D y', v) \<in> I"
         using P by simp
        thus "(u, D x) \<in> I"
         using O by simp
      qed
    qed
    thus ?thesis
    proof simp
      have "{} \<subseteq> ipurge_ref I D (D y) ys X" ..
      with H have "(xs @ ipurge_tr I D (D y) ys, {}) \<in> failures P"
       by (rule process_rule_3)
      with J show "(xs @ ipurge_tr I D (D y) ys, {}) \<in> seq_comp_failures P Q"
      proof (rule SCF_R1)
        show "None \<notin> set (xs @ ipurge_tr I D (D y) ys)"
         using I
        proof (simp, (erule_tac conjE)+)
          have "set (ipurge_tr I D (D y) ys) \<subseteq> set ys"
           by (rule ipurge_tr_set)
          moreover assume "None \<notin> set ys"
          ultimately show "None \<notin> set (ipurge_tr I D (D y) ys)"
           by (rule contra_subsetD)
        qed
      qed
    qed
  next
    assume
      J: "xs @ ipurge_tr I D (D y) ys \<notin> sentences P" and
      K: "(D y, D None) \<notin> I \<and> (\<forall>u \<in> sinks I D (D y) ys. (u, D None) \<notin> I)"
    have "xs @ y # ys @ [None] \<in> traces P"
     using E by (simp add: sentences_def)
    hence "(xs @ y # ys @ [None], {}) \<in> failures P"
     by (rule traces_failures)
    hence "(y # ys @ [None], {}) \<in> futures P xs"
     by (simp add: futures_def)
    hence "(ipurge_tr I D (D y) (ys @ [None]),
      ipurge_ref I D (D y) (ys @ [None]) {}) \<in> futures P xs"
      (is "(_, ?Y) \<in> _")
     using C by (simp add: secure_def del: ipurge_tr.simps)
    hence "(xs @ ipurge_tr I D (D y) (ys @ [None]), ?Y) \<in> failures P"
     by (simp add: futures_def)
    hence "xs @ ipurge_tr I D (D y) (ys @ [None]) \<in> traces P"
     by (rule failures_traces)
    moreover have "\<not> ((D y, D None) \<in> I \<or>
      (\<exists>u \<in> sinks I D (D y) ys. (u, D None) \<in> I))"
     using K by simp
    hence "D None \<notin> sinks I D (D y) (ys @ [None])"
     by (simp only: sinks_interference_eq, simp)
    ultimately have "xs @ ipurge_tr I D (D y) ys @ [None] \<in> traces P"
     by simp
    hence "xs @ ipurge_tr I D (D y) ys \<in> sentences P"
     by (simp add: sentences_def)
    thus ?thesis
     using J by contradiction
  qed
qed

lemma seq_comp_secure_aux_1_case_3:
  assumes
    A: "secure_termination I D" and
    B: "ref_union_closed Q" and
    C: "sequential Q" and
    D: "secure Q I D" and
    E: "secure R I D" and
    F: "ws \<in> sentences Q" and
    G: "(ys', Y) \<in> failures R" and
    H: "ws @ ys' = xs @ y # ys"
  shows "(xs @ ipurge_tr I D (D y) ys, ipurge_ref I D (D y) ys Y)
    \<in> seq_comp_failures Q R"
proof (cases "length xs < length ws")
  case True
  have "drop (Suc (length xs)) (xs @ y # ys) = drop (Suc (length xs)) (ws @ ys')"
   using H by simp
  hence I: "ys = drop (Suc (length xs)) ws @ ys'"
    (is "_ = ?ws' @ _")
   using True by simp
  let ?U = "insert (D y) (sinks I D (D y) ?ws')"
  have "ipurge_tr I D (D y) ys =
    ipurge_tr I D (D y) ?ws' @ ipurge_tr_aux I D ?U ys'"
   using I by (simp add: ipurge_tr_append)
  moreover have "ipurge_ref I D (D y) ys Y = ipurge_ref_aux I D ?U ys' Y"
   using I by (simp add: ipurge_ref_append)
  ultimately show ?thesis
  proof (cases "xs @ ipurge_tr I D (D y) ?ws' \<in> sentences Q", simp_all)
    assume J: "xs @ ipurge_tr I D (D y) ?ws' \<in> sentences Q"
    have K: "(ipurge_tr_aux I D ?U ys', ipurge_ref_aux I D ?U ys' Y) \<in> failures R"
     using E and G by (rule ipurge_tr_ref_aux_failures)
    show "(xs @ ipurge_tr I D (D y) ?ws' @ ipurge_tr_aux I D ?U ys',
      ipurge_ref_aux I D ?U ys' Y) \<in> seq_comp_failures Q R"
    proof (cases "ipurge_tr_aux I D ?U ys'")
      case Nil
      have "(xs @ ipurge_tr I D (D y) ?ws', {x. x \<noteq> None}) \<in> failures Q"
       using B and C and J by (rule seq_sentences_ref)
      moreover have "([], ipurge_ref_aux I D ?U ys' Y) \<in> failures R"
       using K and Nil by simp
      ultimately have "(xs @ ipurge_tr I D (D y) ?ws',
        insert None {x. x \<noteq> None} \<inter> ipurge_ref_aux I D ?U ys' Y)
        \<in> seq_comp_failures Q R"
       by (rule SCF_R2 [OF J])
      moreover have "insert None {x. x \<noteq> None} \<inter>
        ipurge_ref_aux I D ?U ys' Y = ipurge_ref_aux I D ?U ys' Y"
       by blast
      ultimately show ?thesis
       using Nil by simp
    next
      case Cons
      hence "ipurge_tr_aux I D ?U ys' \<noteq> []"
       by simp
      with J and K have
       "((xs @ ipurge_tr I D (D y) ?ws') @ ipurge_tr_aux I D ?U ys',
          ipurge_ref_aux I D ?U ys' Y) \<in> seq_comp_failures Q R"
       by (rule SCF_R3)
      thus ?thesis
       by simp
    qed
  next
    assume J: "xs @ ipurge_tr I D (D y) ?ws' \<notin> sentences Q"
    have "ws = take (Suc (length xs)) ws @ ?ws'"
     by simp
    moreover have "take (Suc (length xs)) (ws @ ys') =
      take (Suc (length xs)) (xs @ y # ys)"
     using H by simp
    hence "take (Suc (length xs)) ws = xs @ [y]"
     using True by simp
    ultimately have K: "xs @ y # ?ws' \<in> sentences Q"
     using F by simp
    hence "xs @ y # ?ws' @ [None] \<in> traces Q"
     by (simp add: sentences_def)
    hence "(xs @ y # ?ws' @ [None], {}) \<in> failures Q"
     by (rule traces_failures)
    hence "(y # ?ws' @ [None], {}) \<in> futures Q xs"
     by (simp add: futures_def)
    hence "(ipurge_tr I D (D y) (?ws' @ [None]),
      ipurge_ref I D (D y) (?ws' @ [None]) {}) \<in> futures Q xs"
     using D by (simp add: secure_def del: ipurge_tr.simps)
    hence L: "(xs @ ipurge_tr I D (D y) (?ws' @ [None]), {}) \<in> failures Q"
     by (simp add: futures_def ipurge_ref_def)
    have "weakly_sequential Q"
     using C by (rule seq_implies_weakly_seq)
    hence N: "None \<notin> set (xs @ y # ?ws')"
     using K by (rule weakly_seq_sentences_none)
    show "(xs @ ipurge_tr I D (D y) ?ws' @ ipurge_tr_aux I D ?U ys',
      ipurge_ref_aux I D ?U ys' Y) \<in> seq_comp_failures Q R"
    proof (cases "(D y, D None) \<in> I \<or>
     (\<exists>u \<in> sinks I D (D y) ?ws'. (u, D None) \<in> I)")
      assume M: "(D y, D None) \<in> I \<or>
        (\<exists>u \<in> sinks I D (D y) ?ws'. (u, D None) \<in> I)"
      have "ipurge_tr_aux I D ?U ys' = []"
      proof (rule disjE [OF M], erule_tac [2] bexE)
        assume O: "(D y, D None) \<in> I"
        show ?thesis
        proof (rule ipurge_tr_aux_nil [of "D y"], simp)
          fix x
          have "(D y, D None) \<in> I \<and> y \<noteq> None \<longrightarrow> (\<forall>u \<in> range D. (D y, u) \<in> I)"
           using A by (simp add: secure_termination_def)
          moreover have "y \<noteq> None"
           using N by (rule_tac not_sym, simp)
          ultimately have "\<forall>u \<in> range D. (D y, u) \<in> I"
           using O by simp
          thus "(D y, D x) \<in> I"
           by simp
        qed
      next
        fix u
        assume
          O: "u \<in> sinks I D (D y) ?ws'" and
          P: "(u, D None) \<in> I"
        have "\<exists>w \<in> set ?ws'. u = D w"
         using O by (rule sinks_elem)
        then obtain w where Q: "w \<in> set ?ws'" and R: "u = D w" ..
        have S: "w \<noteq> None"
        proof
          assume "w = None"
          hence "None \<in> set ?ws'"
           using Q by simp
          moreover have "None \<notin> set ?ws'"
           using N by simp
          ultimately show False
           by contradiction
        qed
        show ?thesis
        proof (rule ipurge_tr_aux_nil [of u], simp add: O)
          fix x
          have "(D w, D None) \<in> I \<and> w \<noteq> None \<longrightarrow> (\<forall>v \<in> range D. (D w, v) \<in> I)"
           using A by (simp add: secure_termination_def)
          moreover have "(D w, D None) \<in> I"
           using P and R by simp
          ultimately have "\<forall>v \<in> range D. (D w, v) \<in> I"
           using S by simp
          thus "(u, D x) \<in> I"
           using R by simp
        qed
      qed
      moreover have "ipurge_ref_aux I D ?U ys' Y = {}"
      proof (rule disjE [OF M], erule_tac [2] bexE)
        assume O: "(D y, D None) \<in> I"
        show ?thesis
        proof (rule ipurge_ref_aux_empty [of "D y"])
          have "?U \<subseteq> sinks_aux I D ?U ys'"
           by (rule sinks_aux_subset)
          moreover have "D y \<in> ?U"
           by simp
          ultimately show "D y \<in> sinks_aux I D ?U ys'" ..
        next
          fix x
          have "(D y, D None) \<in> I \<and> y \<noteq> None \<longrightarrow> (\<forall>u \<in> range D. (D y, u) \<in> I)"
           using A by (simp add: secure_termination_def)
          moreover have "y \<noteq> None"
           using N by (rule_tac not_sym, simp)
          ultimately have "\<forall>u \<in> range D. (D y, u) \<in> I"
           using O by simp
          thus "(D y, D x) \<in> I"
           by simp
        qed
      next
        fix u
        assume
          O: "u \<in> sinks I D (D y) ?ws'" and
          P: "(u, D None) \<in> I"
        have "\<exists>w \<in> set ?ws'. u = D w"
         using O by (rule sinks_elem)
        then obtain w where Q: "w \<in> set ?ws'" and R: "u = D w" ..
        have S: "w \<noteq> None"
        proof
          assume "w = None"
          hence "None \<in> set ?ws'"
           using Q by simp
          moreover have "None \<notin> set ?ws'"
           using N by simp
          ultimately show False
           by contradiction
        qed
        show ?thesis
        proof (rule ipurge_ref_aux_empty [of u])
          have "?U \<subseteq> sinks_aux I D ?U ys'"
           by (rule sinks_aux_subset)
          moreover have "u \<in> ?U"
           using O by simp
          ultimately show "u \<in> sinks_aux I D ?U ys'" ..
        next
          fix x
          have "(D w, D None) \<in> I \<and> w \<noteq> None \<longrightarrow> (\<forall>v \<in> range D. (D w, v) \<in> I)"
           using A by (simp add: secure_termination_def)
          moreover have "(D w, D None) \<in> I"
           using P and R by simp
          ultimately have "\<forall>v \<in> range D. (D w, v) \<in> I"
           using S by simp
          thus "(u, D x) \<in> I"
           using R by simp
        qed
      qed
      ultimately show ?thesis
      proof simp
        have "D None \<in> sinks I D (D y) (?ws' @ [None])"
         using M by (simp only: sinks_interference_eq)
        hence "(xs @ ipurge_tr I D (D y) ?ws', {}) \<in> failures Q"
         using L by simp
        moreover have "None \<notin> set (xs @ ipurge_tr I D (D y) ?ws')"
        proof -
          show ?thesis
           using N
          proof (simp, (erule_tac conjE)+)
            have "set (ipurge_tr I D (D y) ?ws') \<subseteq> set ?ws'"
             by (rule ipurge_tr_set)
            moreover assume "None \<notin> set ?ws'"
            ultimately show "None \<notin> set (ipurge_tr I D (D y) ?ws')"
             by (rule contra_subsetD)
          qed
        qed
        ultimately show "(xs @ ipurge_tr I D (D y) ?ws', {})
          \<in> seq_comp_failures Q R"
         by (rule SCF_R1 [OF J])
      qed
    next
      assume "\<not> ((D y, D None) \<in> I \<or>
        (\<exists>u \<in> sinks I D (D y) ?ws'. (u, D None) \<in> I))"
      hence "D None \<notin> sinks I D (D y) (?ws' @ [None])"
       by (simp only: sinks_interference_eq, simp)
      hence "(xs @ ipurge_tr I D (D y) ?ws' @ [None], {}) \<in> failures Q"
       using L by simp
      hence "xs @ ipurge_tr I D (D y) ?ws' @ [None] \<in> traces Q"
       by (rule failures_traces)
      hence "xs @ ipurge_tr I D (D y) ?ws' \<in> sentences Q"
       by (simp add: sentences_def)
      thus ?thesis
       using J by contradiction
    qed
  qed
next
  case False
  have "drop (length ws) (ws @ ys') = drop (length ws) (xs @ y # ys)"
   using H by simp
  hence "ys' = drop (length ws) xs @ y # ys"
    (is "_ = ?xs' @ _")
   using False by simp
  hence "(?xs' @ y # ys, Y) \<in> failures R"
   using G by simp
  hence "(y # ys, Y) \<in> futures R ?xs'"
   by (simp add: futures_def)
  hence "(ipurge_tr I D (D y) ys, ipurge_ref I D (D y) ys Y)
    \<in> futures R ?xs'"
   using E by (simp add: secure_def)
  hence I: "(?xs' @ ipurge_tr I D (D y) ys, ipurge_ref I D (D y) ys Y)
    \<in> failures R"
   by (simp add: futures_def)
  have "xs = take (length ws) xs @ ?xs'"
   by simp
  hence "xs = take (length ws) (xs @ y # ys) @ ?xs'"
   using False by simp
  hence "xs = take (length ws) (ws @ ys') @ ?xs'"
   using H by simp
  hence J: "xs = ws @ ?xs'"
   by simp
  show ?thesis
  proof (cases "?xs' @ ipurge_tr I D (D y) ys = []", insert I, subst J, simp)
    have "(ws, {x. x \<noteq> None}) \<in> failures Q"
     using B and C and F by (rule seq_sentences_ref)
    moreover assume "([], ipurge_ref I D (D y) ys Y) \<in> failures R"
    ultimately have "(ws, insert None {x. x \<noteq> None} \<inter>
      ipurge_ref I D (D y) ys Y) \<in> seq_comp_failures Q R"
     by (rule SCF_R2 [OF F])
    moreover have "insert None {x. x \<noteq> None} \<inter> ipurge_ref I D (D y) ys Y =
      ipurge_ref I D (D y) ys Y"
     by blast
    ultimately show "(ws, ipurge_ref I D (D y) ys Y) \<in> seq_comp_failures Q R"
     by simp
  next
    assume "?xs' @ ipurge_tr I D (D y) ys \<noteq> []"
    with F and I have
     "(ws @ ?xs' @ ipurge_tr I D (D y) ys, ipurge_ref I D (D y) ys Y)
      \<in> seq_comp_failures Q R"
     by (rule SCF_R3)
    hence "((ws @ ?xs') @ ipurge_tr I D (D y) ys, ipurge_ref I D (D y) ys Y)
      \<in> seq_comp_failures Q R"
     by simp
    thus ?thesis
     using J by simp
  qed
qed

lemma seq_comp_secure_aux_1 [rule_format]:
  assumes
    A: "secure_termination I D" and
    B: "ref_union_closed P" and
    C: "sequential P" and
    D: "secure P I D" and
    E: "secure Q I D"
  shows "(ws, Y) \<in> seq_comp_failures P Q \<Longrightarrow>
    ws = xs @ y # ys \<longrightarrow>
    (xs @ ipurge_tr I D (D y) ys, ipurge_ref I D (D y) ys Y)
      \<in> seq_comp_failures P Q"
proof (erule seq_comp_failures.induct, rule_tac [!] impI, simp_all, (erule conjE)+)
  fix X
  assume
   "xs @ y # ys \<notin> sentences P" and
   "(xs @ y # ys, X) \<in> failures P" and
   "None \<noteq> y" and
   "None \<notin> set xs" and
   "None \<notin> set ys"
  thus "(xs @ ipurge_tr I D (D y) ys, ipurge_ref I D (D y) ys X)
    \<in> seq_comp_failures P Q"
   by (rule seq_comp_secure_aux_1_case_1 [OF A C D])
next
  fix X Y
  assume
   "xs @ y # ys \<in> sentences P" and
   "(xs @ y # ys, X) \<in> failures P" and
   "([], Y) \<in> failures Q"
  thus "(xs @ ipurge_tr I D (D y) ys,
    ipurge_ref I D (D y) ys (insert None X \<inter> Y)) \<in> seq_comp_failures P Q"
   by (rule seq_comp_secure_aux_1_case_2 [OF A C D E])
next
  fix ws ys' Y
  assume
   "ws \<in> sentences P" and
   "(ys', Y) \<in> failures Q" and
   "ws @ ys' = xs @ y # ys"
  thus "(xs @ ipurge_tr I D (D y) ys, ipurge_ref I D (D y) ys Y)
    \<in> seq_comp_failures P Q"
   by (rule seq_comp_secure_aux_1_case_3 [OF A B C D E])
next
  fix X Y
  assume
   "(xs @ ipurge_tr I D (D y) ys, ipurge_ref I D (D y) ys X)
      \<in> seq_comp_failures P Q" and
   "(xs @ ipurge_tr I D (D y) ys, ipurge_ref I D (D y) ys Y)
      \<in> seq_comp_failures P Q"
  hence "(xs @ ipurge_tr I D (D y) ys,
    ipurge_ref I D (D y) ys X \<union> ipurge_ref I D (D y) ys Y)
    \<in> seq_comp_failures P Q"
   by (rule SCF_R4)
  thus "(xs @ ipurge_tr I D (D y) ys, ipurge_ref I D (D y) ys (X \<union> Y))
    \<in> seq_comp_failures P Q"
   by (simp add: ipurge_ref_distrib_union)
qed

lemma seq_comp_secure_1:
  assumes
    A: "secure_termination I D" and
    B: "ref_union_closed P" and
    C: "sequential P" and
    D: "secure P I D" and
    E: "secure Q I D"
  shows "(xs @ y # ys, Y) \<in> seq_comp_failures P Q \<Longrightarrow>
    (xs @ ipurge_tr I D (D y) ys, ipurge_ref I D (D y) ys Y)
      \<in> seq_comp_failures P Q"
by (rule seq_comp_secure_aux_1 [OF A B C D E, where ws = "xs @ y # ys"],
 simp_all)

text \<open>
\null

This completes the proof that the former requirement for noninterference security is satisfied, so
it is the turn of the latter one. Again, rule induction on set @{term seq_comp_failures} is applied,
and the closure of the failures of a secure process under intransitive purge is used to meet the
proof obligations arising from rule \<open>SCF_R3\<close>. In more detail, rule induction is applied to the
trace into which the event is inserted, and then a case distinction is performed on the trace from
which the event is extracted, using the expression of its refusal as union of a set of refusals
derived previously.

\null
\<close>

lemma seq_comp_secure_aux_2_case_1:
  assumes
    A: "secure_termination I D" and
    B: "sequential P" and
    C: "secure P I D" and
    D: "xs @ zs \<notin> sentences P" and
    E: "(xs @ zs, X) \<in> failures P" and
    F: "None \<notin> set xs" and
    G: "None \<notin> set zs" and
    H: "(xs @ [y], {}) \<in> seq_comp_failures P Q"
  shows "(xs @ y # ipurge_tr I D (D y) zs, ipurge_ref I D (D y) zs X)
    \<in> seq_comp_failures P Q"
proof -
  have "\<exists>R. {} = (\<Union>n \<in> {..length (xs @ [y])}. \<Union>W \<in> R n. W) \<and>
    (\<forall>W \<in> R 0.
      xs @ [y] \<notin> sentences P \<and> None \<notin> set (xs @ [y]) \<and>
        (xs @ [y], W) \<in> failures P \<or>
      xs @ [y] \<in> sentences P \<and> (\<exists>U V. (xs @ [y], U) \<in> failures P \<and>
        ([], V) \<in> failures Q \<and> W = insert None U \<inter> V)) \<and>
    (\<forall>n \<in> {0<..length (xs @ [y])}. \<forall>W \<in> R n.
      take (length (xs @ [y]) - n) (xs @ [y]) \<in> sentences P \<and>
      (drop (length (xs @ [y]) - n) (xs @ [y]), W) \<in> failures Q) \<and>
    (\<exists>n \<in> {..length (xs @ [y])}. \<exists>W. W \<in> R n)"
    (is "\<exists>R. ?T R")
   using H by (rule seq_comp_refusals_1)
  then obtain R where I: "?T R" ..
  hence "\<exists>n \<in> {..length (xs @ [y])}. \<exists>W. W \<in> R n"
   by simp
  moreover have "\<forall>n \<in> {0<..length (xs @ [y])}. R n = {}"
  proof (rule ballI, rule equals0I)
    fix n W
    assume J: "n \<in> {0<..length (xs @ [y])}"
    hence "\<forall>W \<in> R n. take (length (xs @ [y]) - n) (xs @ [y]) \<in> sentences P"
     using I by simp
    moreover assume "W \<in> R n"
    ultimately have "take (length (xs @ [y]) - n) (xs @ [y]) \<in> sentences P" ..
    moreover have "take (length (xs @ [y]) - n) (xs @ [y]) =
      take (length (xs @ [y]) - n) (xs @ zs)"
     using J by simp
    ultimately have K: "take (length (xs @ [y]) - n) (xs @ zs) \<in> sentences P"
     by simp
    show False
    proof (cases "drop (length (xs @ [y]) - n) (xs @ zs)")
      case Nil
      hence "xs @ zs \<in> sentences P"
       using K by simp
      thus False
       using D by contradiction
    next
      case (Cons v vs)
      moreover have "xs @ zs = take (length (xs @ [y]) - n) (xs @ zs) @
        drop (length (xs @ [y]) - n) (xs @ zs)"
       by (simp only: append_take_drop_id)
      ultimately have L: "xs @ zs =
        take (length (xs @ [y]) - n) (xs @ zs) @ v # vs"
       by (simp del: take_append)
      hence "(take (length (xs @ [y]) - n) (xs @ zs) @ v # vs, X)
        \<in> failures P"
       using E by (simp del: take_append)
      hence "take (length (xs @ [y]) - n) (xs @ zs) @ v # vs \<in> traces P"
       by (rule failures_traces)
      with B and K have "v = None"
       by (rule seq_sentences_none)
      moreover have "None \<notin> set (xs @ zs)"
       using F and G by simp
      hence "None \<notin> set (take (length (xs @ [y]) - n) (xs @ zs) @ v # vs)"
       by (subst (asm) L)
      hence "v \<noteq> None"
       by (rule_tac not_sym, simp)
      ultimately show False
       by contradiction
    qed
  qed
  ultimately have "\<exists>W. W \<in> R 0"
  proof simp
    assume "\<exists>n \<in> {..Suc (length xs)}. \<exists>W. W \<in> R n"
    then obtain n where J: "n \<in> {..Suc (length xs)}" and K: "\<exists>W. W \<in> R n" ..
    assume L: "\<forall>n \<in> {0<..Suc (length xs)}. R n = {}"
    show ?thesis
    proof (cases n)
      case 0
      thus ?thesis
       using K by simp
    next
      case (Suc m)
      obtain W where "W \<in> R n"
       using K ..
      moreover have "0 < n"
       using Suc by simp
      hence "n \<in> {0<..Suc (length xs)}"
       using J by simp
      with L have "R n = {}" ..
      hence "W \<notin> R n"
       by (rule equals0D)
      ultimately show ?thesis
       by contradiction
    qed
  qed
  then obtain W where J: "W \<in> R 0" ..
  have "\<forall>W \<in> R 0.
    xs @ [y] \<notin> sentences P \<and>
      None \<notin> set (xs @ [y]) \<and> (xs @ [y], W) \<in> failures P \<or>
    xs @ [y] \<in> sentences P \<and>
      (\<exists>U V. (xs @ [y], U) \<in> failures P \<and> ([], V) \<in> failures Q \<and>
        W = insert None U \<inter> V)"
    (is "\<forall>W \<in> R 0. ?T W")
   using I by simp
  hence "?T W" using J ..
  hence K: "(xs @ [y], {}) \<in> failures P \<and> None \<noteq> y"
  proof (cases "xs @ [y] \<in> sentences P", simp_all del: ex_simps,
   (erule_tac exE)+, (erule_tac [!] conjE)+, simp_all)
    case False
    assume "(xs @ [y], W) \<in> failures P"
    moreover have "{} \<subseteq> W" ..
    ultimately show "(xs @ [y], {}) \<in> failures P"
     by (rule process_rule_3)
  next
    fix U
    case True
    assume "(xs @ [y], U) \<in> failures P"
    moreover have "{} \<subseteq> U" ..
    ultimately have "(xs @ [y], {}) \<in> failures P"
     by (rule process_rule_3)
    moreover have "weakly_sequential P"
     using B by (rule seq_implies_weakly_seq)
    hence "None \<notin> set (xs @ [y])"
     using True by (rule weakly_seq_sentences_none)
    hence "None \<noteq> y"
     by simp
    ultimately show ?thesis ..
  qed
  have "(zs, X) \<in> futures P xs"
   using E by (simp add: futures_def)
  moreover have "([y], {}) \<in> futures P xs"
   using K by (simp add: futures_def)
  ultimately have "(y # ipurge_tr I D (D y) zs, ipurge_ref I D (D y) zs X) \<in>
    futures P xs"
   using C by (simp add: secure_def)
  hence L: "(xs @ y # ipurge_tr I D (D y) zs, ipurge_ref I D (D y) zs X) \<in>
    failures P"
   by (simp add: futures_def)
  show ?thesis
  proof (cases "xs @ y # ipurge_tr I D (D y) zs \<in> sentences P",
   cases "(D y, D None) \<in> I \<or> (\<exists>u \<in> sinks I D (D y) zs. (u, D None) \<in> I)",
   simp_all)
    assume "xs @ y # ipurge_tr I D (D y) zs \<notin> sentences P"
    thus ?thesis using L
    proof (rule SCF_R1, simp add: F K)
      have "set (ipurge_tr I D (D y) zs) \<subseteq> set zs"
       by (rule ipurge_tr_set)
      thus "None \<notin> set (ipurge_tr I D (D y) zs)"
       using G by (rule contra_subsetD)
    qed
  next
    assume
      M: "xs @ y # ipurge_tr I D (D y) zs \<in> sentences P" and
      N: "(D y, D None) \<in> I \<or> (\<exists>u \<in> sinks I D (D y) zs. (u, D None) \<in> I)"
    have "ipurge_ref I D (D y) zs X = {}"
    proof (rule disjE [OF N], erule_tac [2] bexE)
      assume O: "(D y, D None) \<in> I"
      show ?thesis
      proof (rule ipurge_ref_empty [of "D y"], simp)
        fix x
        have "(D y, D None) \<in> I \<and> y \<noteq> None \<longrightarrow> (\<forall>u \<in> range D. (D y, u) \<in> I)"
         using A by (simp add: secure_termination_def)
        moreover have "y \<noteq> None"
         using K by (rule_tac not_sym, simp)
        ultimately have "\<forall>u \<in> range D. (D y, u) \<in> I"
         using O by simp
        thus "(D y, D x) \<in> I"
         by simp
      qed
    next
      fix u
      assume
        O: "u \<in> sinks I D (D y) zs" and
        P: "(u, D None) \<in> I"
      have "\<exists>z \<in> set zs. u = D z"
       using O by (rule sinks_elem)
      then obtain z where Q: "z \<in> set zs" and R: "u = D z" ..
      have S: "z \<noteq> None"
      proof
        assume "z = None"
        hence "None \<in> set zs"
         using Q by simp
        thus False
         using G by contradiction
      qed
      show ?thesis
      proof (rule ipurge_ref_empty [of u], simp add: O)
        fix x
        have "(D z, D None) \<in> I \<and> z \<noteq> None \<longrightarrow> (\<forall>v \<in> range D. (D z, v) \<in> I)"
         using A by (simp add: secure_termination_def)
        moreover have "(D z, D None) \<in> I"
         using P and R by simp
        ultimately have "\<forall>v \<in> range D. (D z, v) \<in> I"
         using S by simp
        thus "(u, D x) \<in> I"
         using R by simp
      qed
    qed
    thus ?thesis
    proof simp
      have "([], {}) \<in> failures Q"
       by (rule process_rule_1)
      with M and L have "(xs @ y # ipurge_tr I D (D y) zs,
        insert None (ipurge_ref I D (D y) zs X) \<inter> {}) \<in> seq_comp_failures P Q"
       by (rule SCF_R2)
      thus "(xs @ y # ipurge_tr I D (D y) zs, {}) \<in> seq_comp_failures P Q"
       by simp
    qed
  next
    assume
      M: "xs @ y # ipurge_tr I D (D y) zs \<in> sentences P" and
      N: "(D y, D None) \<notin> I \<and> (\<forall>u \<in> sinks I D (D y) zs. (u, D None) \<notin> I)"
    have "xs @ zs \<in> sentences P"
    proof (simp add: sentences_def,
     rule ipurge_tr_del_traces [OF C, where u = "D y"], simp add: N)
      have "xs @ y # ipurge_tr I D (D y) zs @ [None] \<in> traces P"
       using M by (simp add: sentences_def)
      hence "(xs @ y # ipurge_tr I D (D y) zs @ [None], {}) \<in> failures P"
       by (rule traces_failures)
      hence "(y # ipurge_tr I D (D y) zs @ [None], {}) \<in> futures P xs"
       by (simp add: futures_def)
      hence "(ipurge_tr I D (D y) (ipurge_tr I D (D y) zs @ [None]),
        ipurge_ref I D (D y) (ipurge_tr I D (D y) zs @ [None]) {}) \<in> futures P xs"
       using C by (simp add: secure_def del: ipurge_tr.simps)
      hence "(xs @ ipurge_tr I D (D y) (ipurge_tr I D (D y) zs @ [None]), {})
        \<in> failures P"
       by (simp add: futures_def ipurge_ref_def)
      moreover have "sinks I D (D y) (ipurge_tr I D (D y) zs) = {}"
       by (rule sinks_idem)
      hence "\<not> ((D y, D None) \<in> I \<or>
        (\<exists>u \<in> sinks I D (D y) (ipurge_tr I D (D y) zs). (u, D None) \<in> I))"
       using N by simp
      hence "D None \<notin> sinks I D (D y) (ipurge_tr I D (D y) zs @ [None])"
       by (simp only: sinks_interference_eq, simp)
      ultimately have "(xs @ ipurge_tr I D (D y) (ipurge_tr I D (D y) zs)
        @ [None], {}) \<in> failures P"
       by simp
      hence "(xs @ ipurge_tr I D (D y) zs @ [None], {}) \<in> failures P"
       by (simp add: ipurge_tr_idem)
      thus "xs @ ipurge_tr I D (D y) zs @ [None] \<in> traces P"
       by (rule failures_traces)
    next
      show "xs @ zs \<in> traces P"
       using E by (rule failures_traces)
    qed
    thus ?thesis
     using D by contradiction
  qed
qed

lemma seq_comp_secure_aux_2_case_2:
  assumes
    A: "secure_termination I D" and
    B: "sequential P" and
    C: "secure P I D" and
    D: "secure Q I D" and
    E: "xs @ zs \<in> sentences P" and
    F: "(xs @ zs, X) \<in> failures P" and
    G: "([], Y) \<in> failures Q" and
    H: "(xs @ [y], {}) \<in> seq_comp_failures P Q"
  shows "(xs @ y # ipurge_tr I D (D y) zs,
    ipurge_ref I D (D y) zs (insert None X \<inter> Y)) \<in> seq_comp_failures P Q"
proof -
  have "\<exists>R. {} = (\<Union>n \<in> {..length (xs @ [y])}. \<Union>W \<in> R n. W) \<and>
    (\<forall>W \<in> R 0.
      xs @ [y] \<notin> sentences P \<and> None \<notin> set (xs @ [y]) \<and>
        (xs @ [y], W) \<in> failures P \<or>
      xs @ [y] \<in> sentences P \<and> (\<exists>U V. (xs @ [y], U) \<in> failures P \<and>
        ([], V) \<in> failures Q \<and> W = insert None U \<inter> V)) \<and>
    (\<forall>n \<in> {0<..length (xs @ [y])}. \<forall>W \<in> R n.
      take (length (xs @ [y]) - n) (xs @ [y]) \<in> sentences P \<and>
      (drop (length (xs @ [y]) - n) (xs @ [y]), W) \<in> failures Q) \<and>
    (\<exists>n \<in> {..length (xs @ [y])}. \<exists>W. W \<in> R n)"
    (is "\<exists>R. ?T R")
   using H by (rule seq_comp_refusals_1)
  then obtain R where I: "?T R" ..
  hence "\<exists>n \<in> {..length (xs @ [y])}. \<exists>W. W \<in> R n"
   by simp
  then obtain n where J: "n \<in> {..length (xs @ [y])}" and K: "\<exists>W. W \<in> R n" ..
  have "weakly_sequential P"
   using B by (rule seq_implies_weakly_seq)
  hence L: "None \<notin> set (xs @ zs)"
   using E by (rule weakly_seq_sentences_none)
  have "n = 0 \<or> n \<in> {0<..length (xs @ [y])}"
   using J by auto
  thus ?thesis
  proof
    assume "n = 0"
    hence "\<exists>W. W \<in> R 0"
     using K by simp
    then obtain W where M: "W \<in> R 0" ..
    have "\<forall>W \<in> R 0.
      xs @ [y] \<notin> sentences P \<and>
        None \<notin> set (xs @ [y]) \<and> (xs @ [y], W) \<in> failures P \<or>
      xs @ [y] \<in> sentences P \<and>
        (\<exists>U V. (xs @ [y], U) \<in> failures P \<and> ([], V) \<in> failures Q \<and>
          W = insert None U \<inter> V)"
      (is "\<forall>W \<in> R 0. ?T W")
     using I by simp
    hence "?T W" using M ..
    hence N: "(xs @ [y], {}) \<in> failures P \<and> None \<notin> set xs \<and> None \<noteq> y"
    proof (cases "xs @ [y] \<in> sentences P", simp_all del: ex_simps,
     (erule_tac exE)+, (erule_tac [!] conjE)+, simp_all)
      case False
      assume "(xs @ [y], W) \<in> failures P"
      moreover have "{} \<subseteq> W" ..
      ultimately show "(xs @ [y], {}) \<in> failures P"
       by (rule process_rule_3)
    next
      fix U
      case True
      assume "(xs @ [y], U) \<in> failures P"
      moreover have "{} \<subseteq> U" ..
      ultimately have "(xs @ [y], {}) \<in> failures P"
       by (rule process_rule_3)
      moreover have "weakly_sequential P"
       using B by (rule seq_implies_weakly_seq)
      hence "None \<notin> set (xs @ [y])"
       using True by (rule weakly_seq_sentences_none)
      hence "None \<notin> set xs \<and> None \<noteq> y"
       by simp
      ultimately show ?thesis ..
    qed
    have "(zs, X) \<in> futures P xs"
     using F by (simp add: futures_def)
    moreover have "([y], {}) \<in> futures P xs"
     using N by (simp add: futures_def)
    ultimately have "(y # ipurge_tr I D (D y) zs, ipurge_ref I D (D y) zs X)
      \<in> futures P xs"
     using C by (simp add: secure_def)
    hence O: "(xs @ y # ipurge_tr I D (D y) zs, ipurge_ref I D (D y) zs X)
      \<in> failures P"
     by (simp add: futures_def)
    show ?thesis
    proof (cases "xs @ y # ipurge_tr I D (D y) zs \<in> sentences P",
     case_tac [2] "(D y, D None) \<in> I \<or>
      (\<exists>u \<in> sinks I D (D y) zs. (u, D None) \<in> I)",
     simp_all)
      assume P: "xs @ y # ipurge_tr I D (D y) zs \<in> sentences P"
      have "ipurge_ref I D (D y) zs Y \<subseteq> Y"
       by (rule ipurge_ref_subset)
      with G have "([], ipurge_ref I D (D y) zs Y) \<in> failures Q"
       by (rule process_rule_3)
      with P and O have "(xs @ y # ipurge_tr I D (D y) zs,
        insert None (ipurge_ref I D (D y) zs X) \<inter> ipurge_ref I D (D y) zs Y)
        \<in> seq_comp_failures P Q"
       by (rule SCF_R2)
      moreover have
       "ipurge_ref I D (D y) zs (insert None X) \<inter> ipurge_ref I D (D y) zs Y \<subseteq>
        insert None (ipurge_ref I D (D y) zs X) \<inter> ipurge_ref I D (D y) zs Y"
      proof (rule subsetI, simp del: insert_iff, erule conjE)
        fix x
        have "ipurge_ref I D (D y) zs (insert None X) \<subseteq>
          insert None (ipurge_ref I D (D y) zs X)"
         by (rule ipurge_ref_subset_insert)
        moreover assume "x \<in> ipurge_ref I D (D y) zs (insert None X)"
        ultimately show "x \<in> insert None (ipurge_ref I D (D y) zs X)" ..
      qed
      ultimately have "(xs @ y # ipurge_tr I D (D y) zs,
        ipurge_ref I D (D y) zs (insert None X) \<inter> ipurge_ref I D (D y) zs Y)
        \<in> seq_comp_failures P Q"
       by (rule seq_comp_prop_3)
      thus ?thesis
       by (simp add: ipurge_ref_distrib_inter)
    next
      assume
        P: "xs @ y # ipurge_tr I D (D y) zs \<notin> sentences P" and
        Q: "(D y, D None) \<in> I \<or> (\<exists>u \<in> sinks I D (D y) zs. (u, D None) \<in> I)"
      have "ipurge_ref I D (D y) zs (insert None X \<inter> Y) = {}"
      proof (rule disjE [OF Q], erule_tac [2] bexE)
        assume R: "(D y, D None) \<in> I"
        show ?thesis
        proof (rule ipurge_ref_empty [of "D y"], simp)
          fix x
          have "(D y, D None) \<in> I \<and> y \<noteq> None \<longrightarrow> (\<forall>u \<in> range D. (D y, u) \<in> I)"
           using A by (simp add: secure_termination_def)
          moreover have "y \<noteq> None"
           using N by (rule_tac not_sym, simp)
          ultimately have "\<forall>u \<in> range D. (D y, u) \<in> I"
           using R by simp
          thus "(D y, D x) \<in> I"
           by simp
        qed
      next
        fix u
        assume
          R: "u \<in> sinks I D (D y) zs" and
          S: "(u, D None) \<in> I"
        have "\<exists>z \<in> set zs. u = D z"
         using R by (rule sinks_elem)
        then obtain z where T: "z \<in> set zs" and U: "u = D z" ..
        have V: "z \<noteq> None"
        proof
          assume "z = None"
          hence "None \<in> set zs"
           using T by simp
          moreover have "None \<notin> set zs"
           using L by simp
          ultimately show False
           by contradiction
        qed
        show ?thesis
        proof (rule ipurge_ref_empty [of u], simp add: R)
          fix x
          have "(D z, D None) \<in> I \<and> z \<noteq> None \<longrightarrow> (\<forall>v \<in> range D. (D z, v) \<in> I)"
           using A by (simp add: secure_termination_def)
          moreover have "(D z, D None) \<in> I"
           using S and U by simp
          ultimately have "\<forall>v \<in> range D. (D z, v) \<in> I"
           using V by simp
          thus "(u, D x) \<in> I"
           using U by simp
        qed
      qed
      thus ?thesis
      proof simp
        have "{} \<subseteq> ipurge_ref I D (D y) zs X" ..
        with O have "(xs @ y # ipurge_tr I D (D y) zs, {}) \<in> failures P"
         by (rule process_rule_3)
        with P show "(xs @ y # ipurge_tr I D (D y) zs, {})
          \<in> seq_comp_failures P Q"
        proof (rule SCF_R1, simp add: N)
          have "set (ipurge_tr I D (D y) zs) \<subseteq> set zs"
           by (rule ipurge_tr_set)
          moreover have "None \<notin> set zs"
           using L by simp
          ultimately show "None \<notin> set (ipurge_tr I D (D y) zs)"
           by (rule contra_subsetD)
        qed
      qed
    next
      assume
        P: "xs @ y # ipurge_tr I D (D y) zs \<notin> sentences P" and
        Q: "(D y, D None) \<notin> I \<and> (\<forall>u \<in> sinks I D (D y) zs. (u, D None) \<notin> I)"
      have "xs @ zs @ [None] \<in> traces P"
       using E by (simp add: sentences_def)
      hence "(xs @ zs @ [None], {}) \<in> failures P"
       by (rule traces_failures)
      hence "(zs @ [None], {}) \<in> futures P xs"
       by (simp add: futures_def)
      moreover have "([y], {}) \<in> futures P xs"
       using N by (simp add: futures_def)
      ultimately have "(y # ipurge_tr I D (D y) (zs @ [None]),
        ipurge_ref I D (D y) (zs @ [None]) {}) \<in> futures P xs"
        (is "(_, ?Z) \<in> _")
       using C by (simp add: secure_def del: ipurge_tr.simps)
      hence "(xs @ y # ipurge_tr I D (D y) (zs @ [None]), ?Z) \<in> failures P"
       by (simp add: futures_def)
      hence "xs @ y # ipurge_tr I D (D y) (zs @ [None]) \<in> traces P"
       by (rule failures_traces)
      moreover have "\<not> ((D y, D None) \<in> I \<or>
        (\<exists>u \<in> sinks I D (D y) zs. (u, D None) \<in> I))"
       using Q by simp
      hence "D None \<notin> sinks I D (D y) (zs @ [None])"
       by (simp only: sinks_interference_eq, simp)
      ultimately have "xs @ y # ipurge_tr I D (D y) zs @ [None] \<in> traces P"
       by simp
      hence "xs @ y # ipurge_tr I D (D y) zs \<in> sentences P"
       by (simp add: sentences_def)
      thus ?thesis
       using P by contradiction
    qed
  next
    assume M: "n \<in> {0<..length (xs @ [y])}"
    have "\<forall>n \<in> {0<..length (xs @ [y])}. \<forall>W \<in> R n.
      take (length (xs @ [y]) - n) (xs @ [y]) \<in> sentences P \<and>
      (drop (length (xs @ [y]) - n) (xs @ [y]), W) \<in> failures Q"
      (is "\<forall>n \<in> _. \<forall>W \<in> _. ?T n W")
     using I by simp
    hence "\<forall>W \<in> R n. ?T n W"
     using M ..
    moreover obtain W where "W \<in> R n"
     using K ..
    ultimately have N: "?T n W" ..
    moreover have O: "take (length (xs @ [y]) - n) (xs @ [y]) =
      take (length (xs @ [y]) - n) (xs @ zs)"
     using M by simp
    ultimately have P: "take (length (xs @ [y]) - n) (xs @ zs) \<in> sentences P"
     by simp
    have Q: "drop (length (xs @ [y]) - n) (xs @ zs) = []"
    proof (cases "drop (length (xs @ [y]) - n) (xs @ zs)", simp)
      case (Cons v vs)
      moreover have "xs @ zs = take (length (xs @ [y]) - n) (xs @ zs) @
        drop (length (xs @ [y]) - n) (xs @ zs)"
       by (simp only: append_take_drop_id)
      ultimately have R: "xs @ zs =
        take (length (xs @ [y]) - n) (xs @ zs) @ v # vs"
       by (simp del: take_append)
      hence "(take (length (xs @ [y]) - n) (xs @ zs) @ v # vs, X)
        \<in> failures P"
       using F by (simp del: take_append)
      hence "take (length (xs @ [y]) - n) (xs @ zs) @ v # vs \<in> traces P"
       by (rule failures_traces)
      with B and P have "v = None"
       by (rule seq_sentences_none)
      moreover have
       "None \<notin> set (take (length (xs @ [y]) - n) (xs @ zs) @ v # vs)"
       using L by (subst (asm) R)
      hence "v \<noteq> None"
       by (rule_tac not_sym, simp)
      ultimately show ?thesis
       by contradiction
    qed
    hence R: "zs = []"
     using M by simp
    moreover have "xs @ zs = take (length (xs @ [y]) - n) (xs @ zs) @
      drop (length (xs @ [y]) - n) (xs @ zs)"
     by (simp only: append_take_drop_id)
    ultimately have "take (length (xs @ [y]) - n) (xs @ zs) = xs"
     using Q by simp
    hence "take (length (xs @ [y]) - n) (xs @ [y]) = xs"
     using O by simp
    moreover have "xs @ [y] = take (length (xs @ [y]) - n) (xs @ [y]) @
      drop (length (xs @ [y]) - n) (xs @ [y])"
     by (simp only: append_take_drop_id)
    ultimately have "drop (length (xs @ [y]) - n) (xs @ [y]) = [y]"
     by simp
    hence S: "([y], W) \<in> failures Q"
     using N by simp
    show ?thesis using E and R
    proof (rule_tac SCF_R3, simp_all)
      have "\<forall>xs y ys Y zs Z.
        (y # ys, Y) \<in> futures Q xs \<and> (zs, Z) \<in> futures Q xs \<longrightarrow>
        (ipurge_tr I D (D y) ys, ipurge_ref I D (D y) ys Y) \<in> futures Q xs \<and>
        (y # ipurge_tr I D (D y) zs, ipurge_ref I D (D y) zs Z) \<in> futures Q xs"
       using D by (simp add: secure_def)
      hence "([y], W) \<in> futures Q [] \<and> ([], Y) \<in> futures Q [] \<longrightarrow>
        (ipurge_tr I D (D y) [], ipurge_ref I D (D y) [] W) \<in> futures Q [] \<and>
        (y # ipurge_tr I D (D y) [], ipurge_ref I D (D y) [] Y) \<in> futures Q []"
       by blast
      moreover have "([y], W) \<in> futures Q []"
       using S by (simp add: futures_def)
      moreover have "([], Y) \<in> futures Q []"
       using G by (simp add: futures_def)
      ultimately have "([y], ipurge_ref I D (D y) [] Y) \<in> failures Q"
        (is "(_, ?Y') \<in> _")
       by (simp add: futures_def)
      moreover have "ipurge_ref I D (D y) [] (insert None X) \<inter> ?Y' \<subseteq> ?Y'"
       by simp
      ultimately have "([y], ipurge_ref I D (D y) [] (insert None X) \<inter> ?Y')
        \<in> failures Q"
       by (rule process_rule_3)
      thus "([y], ipurge_ref I D (D y) [] (insert None X \<inter> Y)) \<in> failures Q"
       by (simp add: ipurge_ref_distrib_inter)
    qed
  qed
qed

lemma seq_comp_secure_aux_2_case_3:
  assumes
    A: "secure_termination I D" and
    B: "ref_union_closed P" and
    C: "sequential P" and
    D: "secure P I D" and
    E: "secure Q I D" and
    F: "ws \<in> sentences P" and
    G: "(ys, Y) \<in> failures Q" and
    H: "ys \<noteq> []" and
    I: "ws @ ys = xs @ zs" and
    J: "(xs @ [y], {}) \<in> seq_comp_failures P Q"
  shows "(xs @ y # ipurge_tr I D (D y) zs, ipurge_ref I D (D y) zs Y)
    \<in> seq_comp_failures P Q"
proof -
  have "\<exists>R. {} = (\<Union>n \<in> {..length (xs @ [y])}. \<Union>W \<in> R n. W) \<and>
    (\<forall>W \<in> R 0.
      xs @ [y] \<notin> sentences P \<and> None \<notin> set (xs @ [y]) \<and>
        (xs @ [y], W) \<in> failures P \<or>
      xs @ [y] \<in> sentences P \<and> (\<exists>U V. (xs @ [y], U) \<in> failures P \<and>
        ([], V) \<in> failures Q \<and> W = insert None U \<inter> V)) \<and>
    (\<forall>n \<in> {0<..length (xs @ [y])}. \<forall>W \<in> R n.
      take (length (xs @ [y]) - n) (xs @ [y]) \<in> sentences P \<and>
      (drop (length (xs @ [y]) - n) (xs @ [y]), W) \<in> failures Q) \<and>
    (\<exists>n \<in> {..length (xs @ [y])}. \<exists>W. W \<in> R n)"
    (is "\<exists>R. ?T R")
   using J by (rule seq_comp_refusals_1)
  then obtain R where J: "?T R" ..
  hence "\<exists>n \<in> {..length (xs @ [y])}. \<exists>W. W \<in> R n"
   by simp
  then obtain n where K: "n \<in> {..length (xs @ [y])}" and L: "\<exists>W. W \<in> R n" ..
  have M: "n = 0 \<or> n \<in> {0<..length (xs @ [y])}"
   using K by auto
  show ?thesis
  proof (cases "length xs < length ws")
    case True
    have "\<forall>W \<in> R 0.
      xs @ [y] \<notin> sentences P \<and>
        None \<notin> set (xs @ [y]) \<and> (xs @ [y], W) \<in> failures P \<or>
      xs @ [y] \<in> sentences P \<and>
        (\<exists>U V. (xs @ [y], U) \<in> failures P \<and> ([], V) \<in> failures Q \<and>
          W = insert None U \<inter> V)"
      (is "\<forall>W \<in> _. ?T W")
     using J by simp
    moreover have "n \<notin> {0<..length (xs @ [y])}"
    proof
      assume N: "n \<in> {0<..length (xs @ [y])}"
      hence "\<forall>W \<in> R n. take (length (xs @ [y]) - n) (xs @ [y]) \<in> sentences P"
       using J by simp
      moreover obtain W where "W \<in> R n"
       using L ..
      ultimately have "take (length (xs @ [y]) - n) (xs @ [y]) \<in> sentences P" ..
      moreover have "take (length (xs @ [y]) - n) (xs @ [y]) =
        take (length (xs @ [y]) - n) (xs @ zs)"
       using N by simp
      ultimately have "take (length (xs @ [y]) - n) (xs @ zs) \<in> sentences P"
       by simp
      hence "take (length (xs @ [y]) - n) (ws @ ys) \<in> sentences P"
       using I by simp
      moreover have "length (xs @ [y]) - n \<le> length xs"
       using N by (simp, arith)
      hence O: "length (xs @ [y]) - n < length ws"
       using True by simp
      ultimately have P: "take (length (xs @ [y]) - n) ws \<in> sentences P"
       by simp
      show False
      proof (cases "drop (length (xs @ [y]) - n) ws")
        case Nil
        thus False
         using O by simp
      next
        case (Cons v vs)
        moreover have "ws = take (length (xs @ [y]) - n) ws @
          drop (length (xs @ [y]) - n) ws"
         by simp
        ultimately have Q: "ws = take (length (xs @ [y]) - n) ws @ v # vs"
         by simp
        hence "take (length (xs @ [y]) - n) ws @ v # vs \<in> sentences P"
         using F by simp
        hence "(take (length (xs @ [y]) - n) ws @ v # vs) @ [None] \<in> traces P"
         by (simp add: sentences_def)
        hence "take (length (xs @ [y]) - n) ws @ v # vs \<in> traces P"
         by (rule process_rule_2_traces)
        with C and P have "v = None"
         by (rule seq_sentences_none)
        moreover have "weakly_sequential P"
         using C by (rule seq_implies_weakly_seq)
        hence "None \<notin> set ws"
         using F by (rule weakly_seq_sentences_none)
        hence "None \<notin> set (take (length (xs @ [y]) - n) ws @ v # vs)"
         by (subst (asm) Q)
        hence "v \<noteq> None"
         by (rule_tac not_sym, simp)
        ultimately show False
         by contradiction
      qed
    qed
    hence "n = 0"
     using M by blast
    hence "\<exists>W. W \<in> R 0"
     using L by simp
    then obtain W where "W \<in> R 0" ..
    ultimately have "?T W" ..
    hence N: "(xs @ [y], {}) \<in> failures P \<and> None \<notin> set xs \<and> None \<noteq> y"
    proof (cases "xs @ [y] \<in> sentences P", simp_all del: ex_simps,
     (erule_tac exE)+, (erule_tac [!] conjE)+, simp_all)
      case False
      assume "(xs @ [y], W) \<in> failures P"
      moreover have "{} \<subseteq> W" ..
      ultimately show "(xs @ [y], {}) \<in> failures P"
       by (rule process_rule_3)
    next
      fix U
      case True
      assume "(xs @ [y], U) \<in> failures P"
      moreover have "{} \<subseteq> U" ..
      ultimately have "(xs @ [y], {}) \<in> failures P"
       by (rule process_rule_3)
      moreover have "weakly_sequential P"
       using C by (rule seq_implies_weakly_seq)
      hence "None \<notin> set (xs @ [y])"
       using True by (rule weakly_seq_sentences_none)
      hence "None \<notin> set xs \<and> None \<noteq> y"
       by simp
      ultimately show ?thesis ..
    qed
    have "drop (length xs) (xs @ zs) = drop (length xs) (ws @ ys)"
     using I by simp
    hence O: "zs = drop (length xs) ws @ ys"
      (is "_ = ?ws' @ _")
     using True by simp
    let ?U = "insert (D y) (sinks I D (D y) ?ws')"
    have "ipurge_tr I D (D y) zs =
      ipurge_tr I D (D y) ?ws' @ ipurge_tr_aux I D ?U ys"
     using O by (simp add: ipurge_tr_append)
    moreover have "ipurge_ref I D (D y) zs Y = ipurge_ref_aux I D ?U ys Y"
     using O by (simp add: ipurge_ref_append)
    ultimately show ?thesis
    proof (cases "xs @ y # ipurge_tr I D (D y) ?ws' \<in> sentences P", simp_all)
      assume P: "xs @ y # ipurge_tr I D (D y) ?ws' \<in> sentences P"
      have Q: "(ipurge_tr_aux I D ?U ys, ipurge_ref_aux I D ?U ys Y) \<in> failures Q"
       using E and G by (rule ipurge_tr_ref_aux_failures)
      show "(xs @ y # ipurge_tr I D (D y) ?ws' @ ipurge_tr_aux I D ?U ys,
        ipurge_ref_aux I D ?U ys Y) \<in> seq_comp_failures P Q"
      proof (cases "ipurge_tr_aux I D ?U ys")
        case Nil
        have "(xs @ y # ipurge_tr I D (D y) ?ws', {x. x \<noteq> None}) \<in> failures P"
         using B and C and P by (rule seq_sentences_ref)
        moreover have "([], ipurge_ref_aux I D ?U ys Y) \<in> failures Q"
         using Q and Nil by simp
        ultimately have "(xs @ y # ipurge_tr I D (D y) ?ws',
          insert None {x. x \<noteq> None} \<inter> ipurge_ref_aux I D ?U ys Y)
          \<in> seq_comp_failures P Q"
         by (rule SCF_R2 [OF P])
        moreover have "insert None {x. x \<noteq> None} \<inter>
          ipurge_ref_aux I D ?U ys Y = ipurge_ref_aux I D ?U ys Y"
         by blast
        ultimately show ?thesis
         using Nil by simp
      next
        case Cons
        hence "ipurge_tr_aux I D ?U ys \<noteq> []"
         by simp
        with P and Q have
         "((xs @ y # ipurge_tr I D (D y) ?ws') @ ipurge_tr_aux I D ?U ys,
            ipurge_ref_aux I D ?U ys Y) \<in> seq_comp_failures P Q"
         by (rule SCF_R3)
        thus ?thesis
         by simp
      qed
    next
      assume P: "xs @ y # ipurge_tr I D (D y) ?ws' \<notin> sentences P"
      have "ws = take (length xs) ws @ ?ws'"
       by simp
      moreover have "take (length xs) (ws @ ys) = take (length xs) (xs @ zs)"
       using I by simp
      hence "take (length xs) ws = xs"
       using True by simp
      ultimately have "xs @ ?ws' \<in> sentences P"
       using F by simp
      hence "xs @ ?ws' @ [None] \<in> traces P"
       by (simp add: sentences_def)
      hence "(xs @ ?ws' @ [None], {}) \<in> failures P"
       by (rule traces_failures)
      hence "(?ws' @ [None], {}) \<in> futures P xs"
       by (simp add: futures_def)
      moreover have "([y], {}) \<in> futures P xs"
       using N by (simp add: futures_def)
      ultimately have "(y # ipurge_tr I D (D y) (?ws' @ [None]),
        ipurge_ref I D (D y) (?ws' @ [None]) {}) \<in> futures P xs"
       using D by (simp add: secure_def del: ipurge_tr.simps)
      hence Q: "(xs @ y # ipurge_tr I D (D y) (?ws' @ [None]), {}) \<in> failures P"
       by (simp add: futures_def ipurge_ref_def)
      have "set ?ws' \<subseteq> set ws"
       by (rule set_drop_subset)
      moreover have "weakly_sequential P"
       using C by (rule seq_implies_weakly_seq)
      hence "None \<notin> set ws"
       using F by (rule weakly_seq_sentences_none)
      ultimately have R: "None \<notin> set ?ws'"
       by (rule contra_subsetD)
      show "(xs @ y # ipurge_tr I D (D y) ?ws' @ ipurge_tr_aux I D ?U ys,
        ipurge_ref_aux I D ?U ys Y) \<in> seq_comp_failures P Q"
      proof (cases "(D y, D None) \<in> I \<or>
       (\<exists>u \<in> sinks I D (D y) ?ws'. (u, D None) \<in> I)")
        assume S: "(D y, D None) \<in> I \<or>
          (\<exists>u \<in> sinks I D (D y) ?ws'. (u, D None) \<in> I)"
        have "ipurge_tr_aux I D ?U ys = []"
        proof (rule disjE [OF S], erule_tac [2] bexE)
          assume T: "(D y, D None) \<in> I"
          show ?thesis
          proof (rule ipurge_tr_aux_nil [of "D y"], simp)
            fix x
            have "(D y, D None) \<in> I \<and> y \<noteq> None \<longrightarrow> (\<forall>u \<in> range D. (D y, u) \<in> I)"
             using A by (simp add: secure_termination_def)
            moreover have "y \<noteq> None"
             using N by (rule_tac not_sym, simp)
            ultimately have "\<forall>u \<in> range D. (D y, u) \<in> I"
             using T by simp
            thus "(D y, D x) \<in> I"
             by simp
          qed
        next
          fix u
          assume
            T: "u \<in> sinks I D (D y) ?ws'" and
            U: "(u, D None) \<in> I"
          have "\<exists>w \<in> set ?ws'. u = D w"
           using T by (rule sinks_elem)
          then obtain w where V: "w \<in> set ?ws'" and W: "u = D w" ..
          have X: "w \<noteq> None"
          proof
            assume "w = None"
            hence "None \<in> set ?ws'"
             using V by simp
            moreover have "None \<notin> set ?ws'"
             using R by simp
            ultimately show False
             by contradiction
          qed
          show ?thesis
          proof (rule ipurge_tr_aux_nil [of u], simp add: T)
            fix x
            have "(D w, D None) \<in> I \<and> w \<noteq> None \<longrightarrow>
              (\<forall>v \<in> range D. (D w, v) \<in> I)"
             using A by (simp add: secure_termination_def)
            moreover have "(D w, D None) \<in> I"
             using U and W by simp
            ultimately have "\<forall>v \<in> range D. (D w, v) \<in> I"
             using X by simp
            thus "(u, D x) \<in> I"
             using W by simp
          qed
        qed
        moreover have "ipurge_ref_aux I D ?U ys Y = {}"
        proof (rule disjE [OF S], erule_tac [2] bexE)
          assume T: "(D y, D None) \<in> I"
          show ?thesis
          proof (rule ipurge_ref_aux_empty [of "D y"])
            have "?U \<subseteq> sinks_aux I D ?U ys"
             by (rule sinks_aux_subset)
            moreover have "D y \<in> ?U"
             by simp
            ultimately show "D y \<in> sinks_aux I D ?U ys" ..
          next
            fix x
            have "(D y, D None) \<in> I \<and> y \<noteq> None \<longrightarrow> (\<forall>u \<in> range D. (D y, u) \<in> I)"
             using A by (simp add: secure_termination_def)
            moreover have "y \<noteq> None"
             using N by (rule_tac not_sym, simp)
            ultimately have "\<forall>u \<in> range D. (D y, u) \<in> I"
             using T by simp
            thus "(D y, D x) \<in> I"
             by simp
          qed
        next
          fix u
          assume
            T: "u \<in> sinks I D (D y) ?ws'" and
            U: "(u, D None) \<in> I"
          have "\<exists>w \<in> set ?ws'. u = D w"
           using T by (rule sinks_elem)
          then obtain w where V: "w \<in> set ?ws'" and W: "u = D w" ..
          have X: "w \<noteq> None"
          proof
            assume "w = None"
            hence "None \<in> set ?ws'"
             using V by simp
            moreover have "None \<notin> set ?ws'"
             using R by simp
            ultimately show False
             by contradiction
          qed
          show ?thesis
          proof (rule ipurge_ref_aux_empty [of u])
            have "?U \<subseteq> sinks_aux I D ?U ys"
             by (rule sinks_aux_subset)
            moreover have "u \<in> ?U"
             using T by simp
            ultimately show "u \<in> sinks_aux I D ?U ys" ..
          next
            fix x
            have "(D w, D None) \<in> I \<and> w \<noteq> None \<longrightarrow>
              (\<forall>v \<in> range D. (D w, v) \<in> I)"
             using A by (simp add: secure_termination_def)
            moreover have "(D w, D None) \<in> I"
             using U and W by simp
            ultimately have "\<forall>v \<in> range D. (D w, v) \<in> I"
             using X by simp
            thus "(u, D x) \<in> I"
             using W by simp
          qed
        qed
        ultimately show ?thesis
        proof simp
          have "D None \<in> sinks I D (D y) (?ws' @ [None])"
           using S by (simp only: sinks_interference_eq)
          hence "(xs @ y # ipurge_tr I D (D y) ?ws', {}) \<in> failures P"
           using Q by simp
          moreover have "None \<notin> set (xs @ y # ipurge_tr I D (D y) ?ws')"
          proof (simp add: N)
            have "set (ipurge_tr I D (D y) ?ws') \<subseteq> set ?ws'"
             by (rule ipurge_tr_set)
            thus "None \<notin> set (ipurge_tr I D (D y) ?ws')"
             using R by (rule contra_subsetD)
          qed
          ultimately show "(xs @ y # ipurge_tr I D (D y) ?ws', {})
            \<in> seq_comp_failures P Q"
           by (rule SCF_R1 [OF P])
        qed
      next
        assume "\<not> ((D y, D None) \<in> I \<or>
          (\<exists>u \<in> sinks I D (D y) ?ws'. (u, D None) \<in> I))"
        hence "D None \<notin> sinks I D (D y) (?ws' @ [None])"
         by (simp only: sinks_interference_eq, simp)
        hence "(xs @ y # ipurge_tr I D (D y) ?ws' @ [None], {}) \<in> failures P"
         using Q by simp
        hence "xs @ y # ipurge_tr I D (D y) ?ws' @ [None] \<in> traces P"
         by (rule failures_traces)
        hence "xs @ y # ipurge_tr I D (D y) ?ws' \<in> sentences P"
         by (simp add: sentences_def)
        thus ?thesis
         using P by contradiction
      qed
    qed
  next
    case False
    have "\<forall>n \<in> {0<..length (xs @ [y])}. \<forall>W \<in> R n.
      take (length (xs @ [y]) - n) (xs @ [y]) \<in> sentences P \<and>
      (drop (length (xs @ [y]) - n) (xs @ [y]), W) \<in> failures Q"
      (is "\<forall>n \<in> _. \<forall>W \<in> _. ?T n W")
     using J by simp
    moreover have "n \<noteq> 0"
    proof
      have "\<forall>W \<in> R 0.
        xs @ [y] \<notin> sentences P \<and>
          None \<notin> set (xs @ [y]) \<and> (xs @ [y], W) \<in> failures P \<or>
        xs @ [y] \<in> sentences P \<and>
          (\<exists>U V. (xs @ [y], U) \<in> failures P \<and> ([], V) \<in> failures Q \<and>
            W = insert None U \<inter> V)"
        (is "\<forall>W \<in> _. ?T' W")
       using J by blast
      moreover assume "n = 0"
      hence "\<exists>W. W \<in> R 0"
       using L by simp
      then obtain W where "W \<in> R 0" ..
      ultimately have "?T' W" ..
      hence N: "xs @ [y] \<in> traces P \<and> None \<notin> set (xs @ [y])"
      proof (cases "xs @ [y] \<in> sentences P", simp_all del: ex_simps,
       (erule_tac exE)+, (erule_tac [!] conjE)+, simp_all)
        case False
        assume "(xs @ [y], W) \<in> failures P"
        moreover have "{} \<subseteq> W" ..
        ultimately have "(xs @ [y], {}) \<in> failures P"
         by (rule process_rule_3)
        thus "xs @ [y] \<in> traces P"
         by (rule failures_traces)
      next
        fix U
        case True
        assume "(xs @ [y], U) \<in> failures P"
        moreover have "{} \<subseteq> U" ..
        ultimately have "(xs @ [y], {}) \<in> failures P"
         by (rule process_rule_3)
        hence "xs @ [y] \<in> traces P"
         by (rule failures_traces)
        moreover have "weakly_sequential P"
         using C by (rule seq_implies_weakly_seq)
        hence "None \<notin> set (xs @ [y])"
         using True by (rule weakly_seq_sentences_none)
        hence "None \<noteq> y \<and> None \<notin> set xs"
         by simp
        ultimately show "xs @ [y] \<in> traces P \<and> None \<noteq> y \<and> None \<notin> set xs" ..
      qed
      have "take (length xs) (xs @ zs) @ [y] = take (length xs) (ws @ ys) @ [y]"
       using I by simp
      hence "xs @ [y] = ws @ take (length xs - length ws) ys @ [y]"
       using False by simp
      moreover have "\<exists>v vs. take (length xs - length ws) ys @ [y] = v # vs"
       by (cases "take (length xs - length ws) ys @ [y]", simp_all)
      then obtain v and vs where
       "take (length xs - length ws) ys @ [y] = v # vs"
       by blast
      ultimately have O: "xs @ [y] = ws @ v # vs"
       by simp
      hence "ws @ v # vs \<in> traces P"
       using N by simp
      with C and F have "v = None"
       by (rule seq_sentences_none)
      moreover have "v \<noteq> None"
       using N and O by (rule_tac not_sym, simp)
      ultimately show False
       by contradiction
    qed
    hence N: "n \<in> {0<..length (xs @ [y])}"
     using M by blast
    ultimately have "\<forall>W \<in> R n. ?T n W" ..
    moreover obtain W where "W \<in> R n"
     using L ..
    ultimately have O: "?T n W" ..
    have P: "length (xs @ [y]) - n \<le> length xs"
     using N by (simp, arith)
    have "length (xs @ [y]) - n = length ws"
    proof (rule ccontr, simp only: neq_iff, erule disjE)
      assume Q: "length (xs @ [y]) - n < length ws"
      moreover have "ws = take (length (xs @ [y]) - n) ws @
        drop (length (xs @ [y]) - n) ws"
        (is "_ = _ @ ?ws'")
       by simp
      ultimately have "ws = take (length (xs @ [y]) - n) (ws @ ys) @ ?ws'"
       by simp
      hence "ws = take (length (xs @ [y]) - n) (xs @ zs) @ ?ws'"
       using I by simp
      hence "ws = take (length (xs @ [y]) - n) (xs @ [y]) @ ?ws'"
       using P by simp
      moreover have "?ws' \<noteq> []"
       using Q by simp
      hence "\<exists>v vs. ?ws' = v # vs"
       by (cases ?ws', simp_all)
      then obtain v and vs where "?ws' = v # vs"
       by blast
      ultimately have S: "ws = take (length (xs @ [y]) - n) (xs @ [y]) @ v # vs"
       by simp
      hence "(take (length (xs @ [y]) - n) (xs @ [y]) @ v # vs) @ [None]
        \<in> traces P"
       using F by (simp add: sentences_def)
      hence T: "take (length (xs @ [y]) - n) (xs @ [y]) @ v # vs \<in> traces P"
       by (rule process_rule_2_traces)
      have "take (length (xs @ [y]) - n) (xs @ [y]) \<in> sentences P"
       using O ..
      with C have "v = None"
       using T by (rule seq_sentences_none)
      moreover have "weakly_sequential P"
       using C by (rule seq_implies_weakly_seq)
      hence "None \<notin> set ws"
       using F by (rule weakly_seq_sentences_none)
      hence "v \<noteq> None"
       using S by (rule_tac not_sym, simp)
      ultimately show False
       by contradiction
    next
      assume Q: "length ws < length (xs @ [y]) - n"
      have "take (length (xs @ [y]) - n) (xs @ [y]) =
        take (length (xs @ [y]) - n) (xs @ zs)"
       using P by simp
      also have "\<dots> = take (length (xs @ [y]) - n) (ws @ ys)"
       using I by simp
      also have "\<dots> = take (length (xs @ [y]) - n) ws @
        take (length (xs @ [y]) - n - length ws) ys"
        (is "_ = _ @ ?ys'")
       by simp
      also have "\<dots> = ws @ ?ys'"
       using Q by simp
      finally have "take (length (xs @ [y]) - n) (xs @ [y]) = ws @ ?ys'" .
      moreover have "?ys' \<noteq> []"
       using Q and H by simp
      hence "\<exists>v vs. ?ys' = v # vs"
       by (cases ?ys', simp_all)
      then obtain v and vs where "?ys' = v # vs"
       by blast
      ultimately have S: "take (length (xs @ [y]) - n) (xs @ [y]) = ws @ v # vs"
       by simp
      hence "(ws @ v # vs) @ [None] \<in> traces P"
       using O by (simp add: sentences_def)
      hence "ws @ v # vs \<in> traces P"
       by (rule process_rule_2_traces)
      with C and F have T: "v = None"
       by (rule seq_sentences_none)
      have "weakly_sequential P"
       using C by (rule seq_implies_weakly_seq)
      moreover have "take (length (xs @ [y]) - n) (xs @ [y]) \<in> sentences P"
       using O ..
      ultimately have "None \<notin> set (take (length (xs @ [y]) - n) (xs @ [y]))"
       by (rule weakly_seq_sentences_none)
      hence "v \<noteq> None"
       using S by (rule_tac not_sym, simp)
      thus False
       using T by contradiction
    qed
    hence "(drop (length ws) (xs @ [y]), W) \<in> failures Q"
     using O by simp
    hence "(drop (length ws) xs @ [y], W) \<in> failures Q"
      (is "(?xs' @ _, _) \<in> _")
     using False by simp
    hence "([y], W) \<in> futures Q ?xs'"
     by (simp add: futures_def)
    moreover have "drop (length ws) (ws @ ys) = drop (length ws) (xs @ zs)"
     using I by simp
    hence "ys = ?xs' @ zs"
     using False by simp
    hence "(?xs' @ zs, Y) \<in> failures Q"
     using G by simp
    hence "(zs, Y) \<in> futures Q ?xs'"
     by (simp add: futures_def)
    ultimately have "(y # ipurge_tr I D (D y) zs, ipurge_ref I D (D y) zs Y)
      \<in> futures Q ?xs'"
     using E by (simp add: secure_def)
    hence "(?xs' @ y # ipurge_tr I D (D y) zs, ipurge_ref I D (D y) zs Y)
      \<in> failures Q"
     by (simp add: futures_def)
    moreover have "?xs' @ y # ipurge_tr I D (D y) zs \<noteq> []"
     by simp
    ultimately have "(ws @ ?xs' @ y # ipurge_tr I D (D y) zs,
      ipurge_ref I D (D y) zs Y) \<in> seq_comp_failures P Q"
     by (rule SCF_R3 [OF F])
    hence "((ws @ ?xs') @ y # ipurge_tr I D (D y) zs,
      ipurge_ref I D (D y) zs Y) \<in> seq_comp_failures P Q"
     by simp
    moreover have "xs = take (length ws) xs @ ?xs'"
     by simp
    hence "xs = take (length ws) (xs @ zs) @ ?xs'"
     using False by simp
    hence "xs = take (length ws) (ws @ ys) @ ?xs'"
     using I by simp
    hence "xs = ws @ ?xs'"
     by simp
    ultimately show ?thesis
     by simp
  qed
qed

lemma seq_comp_secure_aux_2 [rule_format]:
  assumes
    A: "secure_termination I D" and
    B: "ref_union_closed P" and
    C: "sequential P" and
    D: "secure P I D" and
    E: "secure Q I D"
  shows "(ws, Z) \<in> seq_comp_failures P Q \<Longrightarrow>
    ws = xs @ zs \<longrightarrow>
    (xs @ [y], {}) \<in> seq_comp_failures P Q \<longrightarrow>
    (xs @ y # ipurge_tr I D (D y) zs, ipurge_ref I D (D y) zs Z)
      \<in> seq_comp_failures P Q"
proof (erule seq_comp_failures.induct, (rule_tac [!] impI)+, simp_all, (erule conjE)+)
  fix X
  assume
   "xs @ zs \<notin> sentences P" and
   "(xs @ zs, X) \<in> failures P" and
   "None \<notin> set xs" and
   "None \<notin> set zs" and
   "(xs @ [y], {}) \<in> seq_comp_failures P Q"
  thus "(xs @ y # ipurge_tr I D (D y) zs, ipurge_ref I D (D y) zs X)
    \<in> seq_comp_failures P Q"
   by (rule seq_comp_secure_aux_2_case_1 [OF A C D])
next
  fix X Y
  assume
   "xs @ zs \<in> sentences P" and
   "(xs @ zs, X) \<in> failures P" and
   "([], Y) \<in> failures Q" and
   "(xs @ [y], {}) \<in> seq_comp_failures P Q"
  thus "(xs @ y # ipurge_tr I D (D y) zs,
    ipurge_ref I D (D y) zs (insert None X \<inter> Y)) \<in> seq_comp_failures P Q"
   by (rule seq_comp_secure_aux_2_case_2 [OF A C D E])
next
  fix ws ys Y
  assume
   "ws \<in> sentences P" and
   "(ys, Y) \<in> failures Q" and
   "ys \<noteq> []" and
   "ws @ ys = xs @ zs" and
   "(xs @ [y], {}) \<in> seq_comp_failures P Q"
  thus "(xs @ y # ipurge_tr I D (D y) zs, ipurge_ref I D (D y) zs Y)
    \<in> seq_comp_failures P Q"
   by (rule seq_comp_secure_aux_2_case_3 [OF A B C D E])
next
  fix X Y
  assume
   "(xs @ y # ipurge_tr I D (D y) zs, ipurge_ref I D (D y) zs X)
      \<in> seq_comp_failures P Q" and
   "(xs @ y # ipurge_tr I D (D y) zs, ipurge_ref I D (D y) zs Y)
      \<in> seq_comp_failures P Q"
  hence "(xs @ y # ipurge_tr I D (D y) zs,
    ipurge_ref I D (D y) zs X \<union> ipurge_ref I D (D y) zs Y)
    \<in> seq_comp_failures P Q"
   by (rule SCF_R4)
  thus "(xs @ y # ipurge_tr I D (D y) zs, ipurge_ref I D (D y) zs (X \<union> Y))
    \<in> seq_comp_failures P Q"
   by (simp add: ipurge_ref_distrib_union)
qed

lemma seq_comp_secure_2:
  assumes
    A: "secure_termination I D" and
    B: "ref_union_closed P" and
    C: "sequential P" and
    D: "secure P I D" and
    E: "secure Q I D"
  shows "(xs @ zs, Z) \<in> seq_comp_failures P Q \<Longrightarrow>
    (xs @ [y], {}) \<in> seq_comp_failures P Q \<Longrightarrow>
    (xs @ y # ipurge_tr I D (D y) zs, ipurge_ref I D (D y) zs Z)
      \<in> seq_comp_failures P Q"
by (rule seq_comp_secure_aux_2 [OF A B C D E, where ws = "xs @ zs"], simp_all)

text \<open>
\null

Finally, the target security conservation theorem can be enunciated and proven, which is done here
below. The theorem states that for any two processes @{term P}, @{term Q} defined over the same
alphabet containing successful termination, to which the noninterference policy @{term I} and the
event-domain map @{term D} apply, if:

\begin{itemize}

\item
@{term I} and @{term D} enforce termination security,

\item
@{term P} is refusals union closed and sequential, and

\item
both @{term P} and @{term Q} are secure with respect to @{term I} and @{term D},

\end{itemize}

then @{term "P ; Q"} is secure as well.

\null
\<close>

theorem seq_comp_secure:
  assumes
    A: "secure_termination I D" and
    B: "ref_union_closed P" and
    C: "sequential P" and
    D: "secure P I D" and
    E: "secure Q I D"
  shows "secure (P ; Q) I D"
proof (simp add: secure_def seq_comp_futures seq_implies_weakly_seq [OF C],
 (rule allI)+, rule impI, erule conjE)
  fix xs y ys Y zs Z
  assume
    F: "(xs @ y # ys, Y) \<in> seq_comp_failures P Q" and
    G: "(xs @ zs, Z) \<in> seq_comp_failures P Q"
  show
   "(xs @ ipurge_tr I D (D y) ys, ipurge_ref I D (D y) ys Y)
      \<in> seq_comp_failures P Q \<and>
    (xs @ y # ipurge_tr I D (D y) zs, ipurge_ref I D (D y) zs Z)
      \<in> seq_comp_failures P Q"
    (is "?A \<and> ?B")
  proof
    show ?A
     by (rule seq_comp_secure_1 [OF A B C D E F])
  next
    have H: "weakly_sequential P"
     using C by (rule seq_implies_weakly_seq)
    hence "((xs @ [y]) @ ys, Y) \<in> failures (P ; Q)"
     using F by (simp add: seq_comp_failures)
    hence "(xs @ [y], {}) \<in> failures (P ; Q)"
     by (rule process_rule_2_failures)
    hence "(xs @ [y], {}) \<in> seq_comp_failures P Q"
     using H by (simp add: seq_comp_failures)
    thus ?B
     by (rule seq_comp_secure_2 [OF A B C D E G])
  qed
qed


subsection "Generalization of the security conservation theorem to lists of processes"

text \<open>
The target security conservation theorem, in the basic version just proven, applies to the
sequential composition of a pair of processes. However, given an arbitrary list of processes where
each process satisfies its assumptions, the theorem could be orderly applied to the composition of
the first two processes in the list, then to the composition of the resulting process with the third
process in the list, and so on, until the last process is reached. The final outcome would be that
the sequential composition of all the processes in the list is secure.

Of course, this argument works provided that the assumptions of the theorem keep being satisfied by
the composed processes produced in each step of the recursion. But this is what indeed happens, by
virtue of the conservation of refusals union closure and sequentiality under sequential composition,
proven previously, and of the conservation of security under sequential composition, ensured by the
target theorem itself.

Therefore, the target security conservation theorem can be generalized to an arbitrary list of
processes, which is done here below. The resulting theorem states that for any nonempty list of
processes defined over the same alphabet containing successful termination, to which the
noninterference policy @{term I} and the event-domain map @{term D} apply, if:

\begin{itemize}

\item
@{term I} and @{term D} enforce termination security,

\item
each process in the list, with the possible exception of the last one, is refusals union closed and
sequential, and

\item
each process in the list is secure with respect to @{term I} and @{term D},

\end{itemize}

then the sequential composition of all the processes in the list is secure as well.

As a precondition, the above conservation lemmas for weak sequentiality, refusals union closure, and
sequentiality are generalized, too.

\null
\<close>

lemma seq_comp_list_weakly_sequential [rule_format]:
 "(\<forall>X \<in> set (P # PS). weakly_sequential X) \<longrightarrow>
    weakly_sequential (foldl (;) P PS)"
proof (induction PS rule: rev_induct, simp, rule impI, simp, (erule conjE)+)
qed (rule seq_comp_weakly_sequential)

lemma seq_comp_list_ref_union_closed [rule_format]:
 "(\<forall>X \<in> set (butlast (P # PS)). weakly_sequential X) \<longrightarrow>
  (\<forall>X \<in> set (P # PS). ref_union_closed X) \<longrightarrow>
    ref_union_closed (foldl (;) P PS)"
proof (induction PS rule: rev_induct, simp, (rule impI)+, simp, split if_split_asm,
 simp, rule seq_comp_ref_union_closed, assumption+)
  fix PS and Q :: "'a option process"
  assume
    A: "weakly_sequential P" and
    B: "\<forall>X \<in> set PS. weakly_sequential X" and
    C: "ref_union_closed Q" and
    D: "(\<forall>X \<in> set (P # butlast PS). weakly_sequential X) \<longrightarrow>
      ref_union_closed (foldl (;) P PS)"
  have "weakly_sequential (foldl (;) P PS)"
  proof (rule seq_comp_list_weakly_sequential, simp, erule disjE, simp add: A)
    fix X
    assume "X \<in> set PS"
    with B show "weakly_sequential X" ..
  qed
  moreover have "\<forall>X \<in> set (P # butlast PS). weakly_sequential X"
  proof (rule ballI, simp, erule disjE, simp add: A)
    fix X
    assume "X \<in> set (butlast PS)"
    hence "X \<in> set PS"
     by (rule in_set_butlastD)
    with B show "weakly_sequential X" ..
  qed
  with D have "ref_union_closed (foldl (;) P PS)" ..
  ultimately show "ref_union_closed (foldl (;) P PS ; Q)"
   using C by (rule seq_comp_ref_union_closed)
qed

lemma seq_comp_list_sequential [rule_format]:
 "(\<forall>X \<in> set (P # PS). sequential X) \<longrightarrow>
    sequential (foldl (;) P PS)"
proof (induction PS rule: rev_induct, simp, rule impI, simp, (erule conjE)+)
qed (rule seq_comp_sequential)

theorem seq_comp_list_secure [rule_format]:
  assumes A: "secure_termination I D"
  shows
   "(\<forall>X \<in> set (butlast (P # PS)). ref_union_closed X \<and> sequential X) \<longrightarrow>
    (\<forall>X \<in> set (P # PS). secure X I D) \<longrightarrow>
      secure (foldl (;) P PS) I D"
proof (induction PS rule: rev_induct, simp, (rule impI)+, simp, split if_split_asm,
 simp, rule seq_comp_secure [OF A], assumption+)
  fix PS Q
  assume
    B: "PS \<noteq> []" and
    C: "ref_union_closed P" and
    D: "sequential P" and
    E: "\<forall>X \<in> set PS. ref_union_closed X \<and> sequential X" and
    F: "secure Q I D" and
    G: "(\<forall>X \<in> set (P # butlast PS). ref_union_closed X \<and> sequential X) \<longrightarrow>
      secure (foldl (;) P PS) I D"
  have "ref_union_closed (foldl (;) P PS)"
  proof (rule seq_comp_list_ref_union_closed, simp_all add: B, erule_tac [!] disjE,
   simp_all add: C)
    show "weakly_sequential P"
     using D by (rule seq_implies_weakly_seq)
  next
    fix X
    assume "X \<in> set (butlast PS)"
    hence "X \<in> set PS"
     by (rule in_set_butlastD)
    with E have "ref_union_closed X \<and> sequential X" ..
    hence "sequential X" ..
    thus "weakly_sequential X"
     by (rule seq_implies_weakly_seq)
  next
    fix X
    assume "X \<in> set PS"
    with E have "ref_union_closed X \<and> sequential X" ..
    thus "ref_union_closed X" ..
  qed
  moreover have "sequential (foldl (;) P PS)"
  proof (rule seq_comp_list_sequential, simp, erule disjE, simp add: D)
    fix X
    assume "X \<in> set PS"
    with E have "ref_union_closed X \<and> sequential X" ..
    thus "sequential X" ..
  qed
  moreover have "\<forall>X \<in> set (P # butlast PS). ref_union_closed X \<and> sequential X"
  proof (rule ballI, simp, erule disjE, simp add: C D)
    fix X
    assume "X \<in> set (butlast PS)"
    hence "X \<in> set PS"
     by (rule in_set_butlastD)
    with E show "ref_union_closed X \<and> sequential X" ..
  qed
  with G have "secure (foldl (;) P PS) I D" ..
  ultimately show "secure (foldl (;) P PS ; Q) I D"
   using F by (rule seq_comp_secure [OF A])
qed

end
