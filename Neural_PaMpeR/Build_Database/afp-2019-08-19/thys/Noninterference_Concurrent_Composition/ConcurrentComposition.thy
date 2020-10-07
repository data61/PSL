(*  Title:       Conservation of CSP Noninterference Security under Concurrent Composition
    Author:      Pasquale Noce
                 Security Certification Specialist at Arjo Systems, Italy
                 pasquale dot noce dot lavoro at gmail dot com
                 pasquale dot noce at arjosystems dot com
*)

section "Concurrent composition and noninterference security"

theory ConcurrentComposition
imports Noninterference_Sequential_Composition.Propaedeutics
begin

text \<open>
\null

In his outstanding work on Communicating Sequential Processes \cite{R6}, Hoare has defined two
fundamental binary operations allowing to compose the input processes into another, typically more
complex, process: sequential composition and concurrent composition. Particularly, the output of the
latter operation is a process in which any event not shared by both operands can occur whenever the
operand that admits the event can engage in it, whereas any event shared by both operands can occur
just in case both can engage in it. In other words, shared events are those that synchronize the
concurrent processes, which on the contrary can engage asynchronously in the respective non-shared
events.

This paper formalizes Hoare's definition of concurrent composition and proves, in the general case
of a possibly intransitive policy, that CSP noninterference security \cite{R1} is conserved under
this operation, viz. the security of both of the input processes implies that of the output process.
This result, along with the analogous one concerning sequential composition attained in \cite{R5},
enables the construction of more and more complex processes enforcing noninterference security by
composing, sequentially or concurrently, simpler secure processes, whose security can in turn be
proven using either the definition of security formulated in \cite{R1}, or the unwinding theorems
demonstrated in \cite{R2}, \cite{R3}, and \cite{R4}.

Throughout this paper, the salient points of definitions and proofs are commented; for additional
information, cf. Isabelle documentation, particularly \cite{R7}, \cite{R8}, \cite{R9}, and
\cite{R10}.
\<close>


subsection "Propaedeutic definitions and lemmas"

text \<open>
The starting point is comprised of some definitions and lemmas propaedeutic to the proof of the
target security conservation theorem.

Particularly, the definition of operator \emph{after} given in \cite{R6} is formalized, and it is
proven that for any secure process @{term P} and any trace @{term xs} of @{term P}, @{term P} after
@{term xs} is still a secure process. Then, this result is used to generalize the lemma stating the
closure of the failures of a secure process @{term P} under intransitive purge, proven in \cite{R5},
to the futures of @{term P} associated to any one of its traces. This is a generalization of the
former result since @{term "futures P xs = failures P"} for @{term "xs = []"}.

\null
\<close>

lemma sinks_aux_elem [rule_format]:
 "u \<in> sinks_aux I D U xs \<longrightarrow> u \<in> U \<or> (\<exists>x \<in> set xs. u = D x)"
by (induction xs rule: rev_induct, simp_all, blast)

lemma ipurge_ref_aux_cons:
 "ipurge_ref_aux I D U (x # xs) X = ipurge_ref_aux I D (sinks_aux I D U [x]) xs X"
by (subgoal_tac "x # xs = [x] @ xs", simp only: ipurge_ref_aux_append, simp)

lemma process_rule_1_futures:
 "xs \<in> traces P \<Longrightarrow> ([], {}) \<in> futures P xs"
by (simp add: futures_def, rule traces_failures)

lemma process_rule_3_futures:
 "(ys, Y) \<in> futures P xs \<Longrightarrow> Y' \<subseteq> Y \<Longrightarrow> (ys, Y') \<in> futures P xs"
by (simp add: futures_def, rule process_rule_3)

lemma process_rule_4_futures:
 "(ys, Y) \<in> futures P xs \<Longrightarrow>
    (ys @ [x], {}) \<in> futures P xs \<or> (ys, insert x Y) \<in> futures P xs"
by (simp add: futures_def, subst append_assoc [symmetric], rule process_rule_4)

lemma process_rule_5_general [rule_format]:
 "xs \<in> divergences P \<longrightarrow> xs @ ys \<in> divergences P"
proof (induction ys rule: rev_induct, simp, rule impI, simp)
qed (subst append_assoc [symmetric], rule process_rule_5)

text \<open>
\null

Here below is the definition of operator \emph{after}, for which a symbolic notation similar to the
one used in \cite{R6} is introduced. Then, it is proven that for any process @{term P} and any trace
@{term xs} of @{term P}, the failures set and the divergences set of @{term P} after @{term xs}
indeed enjoy their respective characteristic properties as defined in \cite{R1}.

\null
\<close>

definition future_divergences :: "'a process \<Rightarrow> 'a list \<Rightarrow> 'a list set" where
"future_divergences P xs \<equiv> {ys. xs @ ys \<in> divergences P}"

definition after :: "'a process \<Rightarrow> 'a list \<Rightarrow> 'a process" (infixl "\<setminus>" 64) where
"P \<setminus> xs \<equiv> Abs_process (futures P xs, future_divergences P xs)"

lemma process_rule_5_futures:
 "ys \<in> future_divergences P xs \<Longrightarrow> ys @ [x] \<in> future_divergences P xs"
by (simp add: future_divergences_def, subst append_assoc [symmetric],
 rule process_rule_5)

lemma process_rule_6_futures:
 "ys \<in> future_divergences P xs \<Longrightarrow> (ys, Y) \<in> futures P xs"
by (simp add: futures_def future_divergences_def, rule process_rule_6)

lemma after_rep:
  assumes A: "xs \<in> traces P"
  shows "Rep_process (P \<setminus> xs) = (futures P xs, future_divergences P xs)"
    (is "_ = ?X")
proof (subst after_def, rule Abs_process_inverse, simp add: process_set_def,
 (subst conj_assoc [symmetric])+, (rule conjI)+)
  show "process_prop_1 ?X"
  proof (simp add: process_prop_1_def)
  qed (rule process_rule_1_futures [OF A])
next
  show "process_prop_2 ?X"
  proof (simp add: process_prop_2_def del: all_simps, (rule allI)+, rule impI)
  qed (rule process_rule_2_futures)
next
  show "process_prop_3 ?X"
  proof (simp add: process_prop_3_def del: all_simps, (rule allI)+, rule impI,
   erule conjE)
  qed (rule process_rule_3_futures)
next
  show "process_prop_4 ?X"
  proof (simp add: process_prop_4_def, (rule allI)+, rule impI)
  qed (rule process_rule_4_futures)
next
  show "process_prop_5 ?X"
  proof (simp add: process_prop_5_def, rule allI, rule impI, rule allI)
  qed (rule process_rule_5_futures)
next
  show "process_prop_6 ?X"
  proof (simp add: process_prop_6_def, rule allI, rule impI, rule allI)
  qed (rule process_rule_6_futures)
qed

lemma after_failures:
  assumes A: "xs \<in> traces P"
  shows "failures (P \<setminus> xs) = futures P xs"
by (simp add: failures_def after_rep [OF A])

lemma after_futures:
  assumes A: "xs \<in> traces P"
  shows "futures (P \<setminus> xs) ys = futures P (xs @ ys)"
by (simp add: futures_def after_failures [OF A])

text \<open>
\null

Finally, the closure of the futures of a secure process under intransitive purge is proven.

\null
\<close>

lemma after_secure:
  assumes A: "xs \<in> traces P"
  shows "secure P I D \<Longrightarrow> secure (P \<setminus> xs) I D"
by (simp add: secure_def after_futures [OF A], blast)

lemma ipurge_tr_ref_aux_futures:
 "\<lbrakk>secure P I D; (ys, Y) \<in> futures P xs\<rbrakk> \<Longrightarrow>
    (ipurge_tr_aux I D U ys, ipurge_ref_aux I D U ys Y) \<in> futures P xs"
proof (subgoal_tac "xs \<in> traces P", simp add: after_failures [symmetric],
 rule ipurge_tr_ref_aux_failures, rule after_secure, assumption+)
qed (simp add: futures_def, drule failures_traces, rule process_rule_2_traces)

lemma ipurge_tr_ref_aux_failures_general:
 "\<lbrakk>secure P I D; (xs @ ys, Y) \<in> failures P\<rbrakk> \<Longrightarrow>
    (xs @ ipurge_tr_aux I D U ys, ipurge_ref_aux I D U ys Y) \<in> failures P"
by (drule ipurge_tr_ref_aux_futures, simp_all add: futures_def)


subsection "Concurrent composition"

text \<open>
In \cite{R6}, the concurrent composition of two processes @{term P}, @{term Q}, expressed using
notation \<open>P \<parallel> Q\<close>, is defined as a process whose alphabet is the union of the alphabets of
@{term P} and @{term Q}, so that the shared events requiring the synchronous participation of both
processes are those in the intersection of their alphabets.

In the formalization of Communicating Sequential Processes developed in \cite{R1}, the alphabets of
@{term P} and @{term Q} are the data types @{typ 'a} and @{typ 'b} nested in their respective types
@{typ "'a process"} and @{typ "'b process"}. Therefore, for any two maps @{term "p :: 'a \<Rightarrow> 'c"},
@{term "q :: 'b \<Rightarrow> 'c"}, the concurrent composition of @{term P} and @{term Q} with respect to
@{term p} and @{term q}, expressed using notation \<open>P \<parallel> Q <p, q>\<close>, is defined in what follows
as a process of type @{typ "'c process"}, where meaningful events are those in
@{term "range p \<union> range q"} and shared events are those in @{term "range p \<inter> range q"}.

The case where @{term "- (range p \<union> range q) \<noteq> {}"} constitutes a generalization of the definition
given in \cite{R6}, and the events in @{term "- (range p \<union> range q)"}, not being mapped to any event
in the alphabets of the input processes, shall be understood as fake events lacking any meaning.
Consistently with this interpretation, such events are allowed to occur in divergent traces only --
necessarily, since divergences are capable by definition of giving rise to any sort of event. As a
result, while in \cite{R6} the refusals associated to non-divergent traces are the union of two
sets, a refusal of @{term P} and a refusal of @{term Q}, in the following definition they are the
union of three sets instead, where the third set is any subset of @{term "- (range p \<union> range q)"}.

Since the definition given in \cite{R6} preserves the identity of the events of the input processes,
a further generalization resulting from the following definition corresponds to the case where
either map @{term p}, @{term q} is not injective. However, as shown below, these generalizations
turn out to compromise neither the compliance of the output of concurrent composition with the
characteristic properties of processes as defined in \cite{R1}, nor even the validity of the target
security conservation theorem.

Since divergences can contain fake events, whereas non-divergent traces cannot, it is necessary to
add divergent failures to the failures set explicitly. The following definition of the divergences
set restricts the definition given in \cite{R6}, as it identifies a divergence with an arbitrary
extension of an event sequence @{term xs} being a divergence of both @{term P} and @{term Q}, rather
than a divergence of either process and a trace of the other one. This is a reasonable restriction,
in that it requires the concurrent composition of @{term P} and @{term Q} to admit a shared event
@{term x} in a divergent trace just in case both @{term P} and @{term Q} diverge and can then accept
@{term x}, analogously to what is required for a non-divergent trace. Anyway, the definitions match
if the input processes do not diverge, which is the case for any process of practical significance
(cf. \cite{R6}).

\null
\<close>

definition con_comp_divergences ::
 "'a process \<Rightarrow> 'b process \<Rightarrow> ('a \<Rightarrow> 'c) \<Rightarrow> ('b \<Rightarrow> 'c) \<Rightarrow> 'c list set" where
"con_comp_divergences P Q p q \<equiv>
  {xs @ ys | xs ys.
    set xs \<subseteq> range p \<union> range q \<and>
    map (inv p) [x\<leftarrow>xs. x \<in> range p] \<in> divergences P \<and>
    map (inv q) [x\<leftarrow>xs. x \<in> range q] \<in> divergences Q}"

definition con_comp_failures ::
 "'a process \<Rightarrow> 'b process \<Rightarrow> ('a \<Rightarrow> 'c) \<Rightarrow> ('b \<Rightarrow> 'c) \<Rightarrow> 'c failure set" where
"con_comp_failures P Q p q \<equiv>
  {(xs, X \<union> Y \<union> Z) | xs X Y Z.
    set xs \<subseteq> range p \<union> range q \<and>
    X \<subseteq> range p \<and> Y \<subseteq> range q \<and> Z \<subseteq> - (range p \<union> range q) \<and>
    (map (inv p) [x\<leftarrow>xs. x \<in> range p], inv p ` X) \<in> failures P \<and>
    (map (inv q) [x\<leftarrow>xs. x \<in> range q], inv q ` Y) \<in> failures Q} \<union>
  {(xs, X). xs \<in> con_comp_divergences P Q p q}"

definition con_comp ::
 "'a process \<Rightarrow> 'b process \<Rightarrow> ('a \<Rightarrow> 'c) \<Rightarrow> ('b \<Rightarrow> 'c) \<Rightarrow> 'c process" where
"con_comp P Q p q \<equiv>
  Abs_process (con_comp_failures P Q p q, con_comp_divergences P Q p q)"

abbreviation con_comp_syntax ::
 "'a process \<Rightarrow> 'b process \<Rightarrow> ('a \<Rightarrow> 'c) \<Rightarrow> ('b \<Rightarrow> 'c) \<Rightarrow> 'c process"
 ("(_ \<parallel> _ <_, _>)" 55)
where
"P \<parallel> Q <p, q> \<equiv> con_comp P Q p q"

text \<open>
\null

Here below is the proof that, for any two processes @{term P}, @{term Q} and any two maps @{term p},
@{term q}, sets @{term "con_comp_failures P Q p q"} and @{term "con_comp_divergences P Q p q"} enjoy
the characteristic properties of the failures and the divergences sets of a process as defined in
\cite{R1}.

\null
\<close>

lemma con_comp_prop_1:
 "([], {}) \<in> con_comp_failures P Q p q"
proof (simp add: con_comp_failures_def)
qed (rule disjI1, rule conjI, (rule process_rule_1)+)

lemma con_comp_prop_2:
 "(xs @ [x], X) \<in> con_comp_failures P Q p q \<Longrightarrow>
    (xs, {}) \<in> con_comp_failures P Q p q"
proof (simp add: con_comp_failures_def del: filter_append,
 erule disjE, (erule exE)+, (erule conjE)+, rule disjI1)
  fix X Y
  assume
    A: "set xs \<subseteq> range p \<union> range q" and
    B: "(map (inv p) [x\<leftarrow>xs @ [x]. x \<in> range p], inv p ` X) \<in> failures P" and
    C: "(map (inv q) [x\<leftarrow>xs @ [x]. x \<in> range q], inv q ` Y) \<in> failures Q"
  show "set xs \<subseteq> range p \<union> range q \<and>
    (map (inv p) [x\<leftarrow>xs. x \<in> range p], {}) \<in> failures P \<and>
    (map (inv q) [x\<leftarrow>xs. x \<in> range q], {}) \<in> failures Q"
  proof (simp add: A, rule conjI, cases "x \<in> range p",
   case_tac [3] "x \<in> range q")
    assume "x \<in> range p"
    hence "(map (inv p) [x\<leftarrow>xs. x \<in> range p] @ [inv p x], inv p ` X) \<in> failures P"
     using B by simp
    thus "(map (inv p) [x\<leftarrow>xs. x \<in> range p], {}) \<in> failures P"
     by (rule process_rule_2)
  next
    assume "x \<notin> range p"
    hence "(map (inv p) [x\<leftarrow>xs. x \<in> range p], inv p ` X) \<in> failures P"
     using B by simp
    moreover have "{} \<subseteq> inv p ` X" ..
    ultimately show "(map (inv p) [x\<leftarrow>xs. x \<in> range p], {}) \<in> failures P"
     by (rule process_rule_3)
  next
    assume "x \<in> range q"
    hence "(map (inv q) [x\<leftarrow>xs. x \<in> range q] @ [inv q x], inv q ` Y) \<in> failures Q"
     using C by simp
    thus "(map (inv q) [x\<leftarrow>xs. x \<in> range q], {}) \<in> failures Q"
     by (rule process_rule_2)
  next
    assume "x \<notin> range q"
    hence "(map (inv q) [x\<leftarrow>xs. x \<in> range q], inv q ` Y) \<in> failures Q"
     using C by simp
    moreover have "{} \<subseteq> inv q ` Y" ..
    ultimately show "(map (inv q) [x\<leftarrow>xs. x \<in> range q], {}) \<in> failures Q"
     by (rule process_rule_3)
  qed
next
  assume A: "xs @ [x] \<in> con_comp_divergences P Q p q"
  show
   "set xs \<subseteq> range p \<union> range q \<and>
      (map (inv p) [x\<leftarrow>xs. x \<in> range p], {}) \<in> failures P \<and>
      (map (inv q) [x\<leftarrow>xs. x \<in> range q], {}) \<in> failures Q \<or>
    xs \<in> con_comp_divergences P Q p q"
    (is "?A \<or> _")
  proof (insert A, simp add: con_comp_divergences_def,
   ((erule exE)?, erule conjE)+)
    fix ws ys
    assume
      B: "xs @ [x] = ws @ ys" and
      C: "set ws \<subseteq> range p \<union> range q" and
      D: "map (inv p) [x\<leftarrow>ws. x \<in> range p] \<in> divergences P" and
      E: "map (inv q) [x\<leftarrow>ws. x \<in> range q] \<in> divergences Q"
    show "?A \<or> (\<exists>ws'.
      (\<exists>ys'. xs = ws' @ ys') \<and>
      set ws' \<subseteq> range p \<union> range q \<and>
      map (inv p) [x\<leftarrow>ws'. x \<in> range p] \<in> divergences P \<and>
      map (inv q) [x\<leftarrow>ws'. x \<in> range q] \<in> divergences Q)"
      (is "_ \<or> (\<exists>ws'. ?B ws')")
    proof (cases ys, rule disjI1, rule_tac [2] disjI2)
      case Nil
      hence "set (xs @ [x]) \<subseteq> range p \<union> range q"
       using B and C by simp
      hence "insert x (set xs) \<subseteq> range p \<union> range q"
       by simp
      moreover have "set xs \<subseteq> insert x (set xs)"
       by (rule subset_insertI)
      ultimately have "set xs \<subseteq> range p \<union> range q"
       by simp
      moreover have "map (inv p) [x\<leftarrow>xs @ [x]. x \<in> range p] \<in> divergences P"
       using Nil and B and D by simp
      hence "(map (inv p) [x\<leftarrow>xs. x \<in> range p], {}) \<in> failures P"
      proof (cases "x \<in> range p", simp_all)
        assume "map (inv p) [x\<leftarrow>xs. x \<in> range p] @ [inv p x] \<in> divergences P"
        hence "(map (inv p) [x\<leftarrow>xs. x \<in> range p] @ [inv p x], {}) \<in> failures P"
         by (rule process_rule_6)
        thus ?thesis
         by (rule process_rule_2)
      next
        assume "map (inv p) [x\<leftarrow>xs. x \<in> range p] \<in> divergences P"
        thus ?thesis
         by (rule process_rule_6)
      qed
      moreover have "map (inv q) [x\<leftarrow>xs @ [x]. x \<in> range q] \<in> divergences Q"
       using Nil and B and E by simp
      hence "(map (inv q) [x\<leftarrow>xs. x \<in> range q], {}) \<in> failures Q"
      proof (cases "x \<in> range q", simp_all)
        assume "map (inv q) [x\<leftarrow>xs. x \<in> range q] @ [inv q x] \<in> divergences Q"
        hence "(map (inv q) [x\<leftarrow>xs. x \<in> range q] @ [inv q x], {}) \<in> failures Q"
         by (rule process_rule_6)
        thus ?thesis
         by (rule process_rule_2)
      next
        assume "map (inv q) [x\<leftarrow>xs. x \<in> range q] \<in> divergences Q"
        thus ?thesis
         by (rule process_rule_6)
      qed
      ultimately show ?A
       by blast
    next
      case Cons
      moreover have "butlast (xs @ [x]) = butlast (ws @ ys)"
       using B by simp
      ultimately have "xs = ws @ butlast ys"
       by (simp add: butlast_append)
      hence "\<exists>ys'. xs = ws @ ys'" ..
      hence "?B ws"
       using C and D and E by simp
      thus "\<exists>ws'. ?B ws'" ..
    qed
  qed
qed

lemma con_comp_prop_3:
 "\<lbrakk>(xs, Y) \<in> con_comp_failures P Q p q; X \<subseteq> Y\<rbrakk> \<Longrightarrow>
    (xs, X) \<in> con_comp_failures P Q p q"
proof (simp add: con_comp_failures_def, erule disjE, simp_all,
 (erule exE)+, (erule conjE)+, rule disjI1, simp)
  fix X' Y' Z'
  assume
    A: "X \<subseteq> X' \<union> Y' \<union> Z'" and
    B: "X' \<subseteq> range p" and
    C: "Y' \<subseteq> range q" and
    D: "Z' \<subseteq> - range p" and
    E: "Z' \<subseteq> - range q" and
    F: "(map (inv p) [x\<leftarrow>xs. x \<in> range p], inv p ` X') \<in> failures P" and
    G: "(map (inv q) [x\<leftarrow>xs. x \<in> range q], inv q ` Y') \<in> failures Q"
  show "\<exists>X' Y' Z'.
    X = X' \<union> Y' \<union> Z' \<and>
    X' \<subseteq> range p \<and>
    Y' \<subseteq> range q \<and>
    Z' \<subseteq> - range p \<and>
    Z' \<subseteq> - range q \<and>
    (map (inv p) [x\<leftarrow>xs. x \<in> range p], inv p ` X') \<in> failures P \<and>
    (map (inv q) [x\<leftarrow>xs. x \<in> range q], inv q ` Y') \<in> failures Q"
  proof (rule_tac x = "X' \<inter> X" in exI, rule_tac x = "Y' \<inter> X" in exI,
   rule_tac x = "Z' \<inter> X" in exI, (subst conj_assoc [symmetric])+, (rule conjI)+)
    show "X = X' \<inter> X \<union> Y' \<inter> X \<union> Z' \<inter> X"
     using A by blast
  next
    show "X' \<inter> X \<subseteq> range p"
     using B by blast
  next
    show "Y' \<inter> X \<subseteq> range q"
     using C by blast
  next
    show "Z' \<inter> X \<subseteq> - range p"
     using D by blast
  next
    show "Z' \<inter> X \<subseteq> - range q"
     using E by blast
  next
    have "inv p ` (X' \<inter> X) \<subseteq> inv p ` X'"
     by blast
    with F show "(map (inv p) [x\<leftarrow>xs. x \<in> range p], inv p ` (X' \<inter> X))
      \<in> failures P"
     by (rule process_rule_3)
  next
    have "inv q ` (Y' \<inter> X) \<subseteq> inv q ` Y'"
     by blast
    with G show "(map (inv q) [x\<leftarrow>xs. x \<in> range q], inv q ` (Y' \<inter> X))
      \<in> failures Q"
     by (rule process_rule_3)
  qed
qed

lemma con_comp_prop_4:
 "(xs, X) \<in> con_comp_failures P Q p q \<Longrightarrow>
    (xs @ [x], {}) \<in> con_comp_failures P Q p q \<or>
    (xs, insert x X) \<in> con_comp_failures P Q p q"
proof (simp add: con_comp_failures_def del: filter_append,
 erule disjE, (erule exE)+, (erule conjE)+, simp_all del: filter_append)
  fix X Y Z
  assume
    A: "X \<subseteq> range p" and
    B: "Y \<subseteq> range q" and
    C: "Z \<subseteq> - range p" and
    D: "Z \<subseteq> - range q" and
    E: "(map (inv p) [x\<leftarrow>xs. x \<in> range p], inv p ` X) \<in> failures P" and
    F: "(map (inv q) [x\<leftarrow>xs. x \<in> range q], inv q ` Y) \<in> failures Q"
  show
   "(x \<in> range p \<or> x \<in> range q) \<and>
      (map (inv p) [x\<leftarrow>xs @ [x]. x \<in> range p], {}) \<in> failures P \<and>
      (map (inv q) [x\<leftarrow>xs @ [x]. x \<in> range q], {}) \<in> failures Q \<or>
    xs @ [x] \<in> con_comp_divergences P Q p q \<or>
    (\<exists>X' Y' Z'.
      insert x (X \<union> Y \<union> Z) = X' \<union> Y' \<union> Z' \<and>
      X' \<subseteq> range p \<and>
      Y' \<subseteq> range q \<and>
      Z' \<subseteq> - range p \<and>
      Z' \<subseteq> - range q \<and>
      (map (inv p) [x\<leftarrow>xs. x \<in> range p], inv p ` X') \<in> failures P \<and>
      (map (inv q) [x\<leftarrow>xs. x \<in> range q], inv q ` Y') \<in> failures Q) \<or>
    xs \<in> con_comp_divergences P Q p q"
    (is "_ \<or> _ \<or> ?A \<or> _")
  proof (cases "x \<in> range p", case_tac [!] "x \<in> range q", simp_all)
    assume
      G: "x \<in> range p" and
      H: "x \<in> range q"
    show
     "(map (inv p) [x\<leftarrow>xs. x \<in> range p] @ [inv p x], {}) \<in> failures P \<and>
        (map (inv q) [x\<leftarrow>xs. x \<in> range q] @ [inv q x], {}) \<in> failures Q \<or>
      xs @ [x] \<in> con_comp_divergences P Q p q \<or>
      ?A \<or>
      xs \<in> con_comp_divergences P Q p q"
      (is "?B \<or> _")
    proof (cases ?B, simp_all del: disj_not1, erule disjE)
      assume
        I: "(map (inv p) [x\<leftarrow>xs. x \<in> range p] @ [inv p x], {}) \<notin> failures P"
      have ?A
      proof (rule_tac x = "insert x X" in exI, rule_tac x = "Y" in exI,
       rule_tac x = "Z" in exI, (subst conj_assoc [symmetric])+, (rule conjI)+)
        show "insert x (X \<union> Y \<union> Z) = insert x X \<union> Y \<union> Z"
         by simp
      next
        show "insert x X \<subseteq> range p"
         using A and G by simp
      next
        show "Y \<subseteq> range q"
         using B .
      next
        show "Z \<subseteq> - range p"
         using C .
      next
        show "Z \<subseteq> - range q"
         using D .
      next
        have
         "(map (inv p) [x\<leftarrow>xs. x \<in> range p] @ [inv p x], {})
            \<in> failures P \<or>
          (map (inv p) [x\<leftarrow>xs. x \<in> range p], insert (inv p x) (inv p ` X))
            \<in> failures P"
         using E by (rule process_rule_4)
        thus "(map (inv p) [x\<leftarrow>xs. x \<in> range p], inv p ` insert x X) \<in> failures P"
         using I by simp
      next
        show "(map (inv q) [x\<leftarrow>xs. x \<in> range q], inv q ` Y) \<in> failures Q"
         using F .
      qed
      thus ?thesis
       by simp
    next
      assume
        I: "(map (inv q) [x\<leftarrow>xs. x \<in> range q] @ [inv q x], {}) \<notin> failures Q"
      have ?A
      proof (rule_tac x = "X" in exI, rule_tac x = "insert x Y" in exI,
       rule_tac x = "Z" in exI, (subst conj_assoc [symmetric])+, (rule conjI)+)
        show "insert x (X \<union> Y \<union> Z) = X \<union> insert x Y \<union> Z"
         by simp
      next
        show "X \<subseteq> range p"
         using A .
      next
        show "insert x Y \<subseteq> range q"
         using B and H by simp
      next
        show "Z \<subseteq> - range p"
         using C .
      next
        show "Z \<subseteq> - range q"
         using D .
      next
        show "(map (inv p) [x\<leftarrow>xs. x \<in> range p], inv p ` X) \<in> failures P"
         using E .
      next
        have
         "(map (inv q) [x\<leftarrow>xs. x \<in> range q] @ [inv q x], {})
            \<in> failures Q \<or>
          (map (inv q) [x\<leftarrow>xs. x \<in> range q], insert (inv q x) (inv q ` Y))
            \<in> failures Q"
         using F by (rule process_rule_4)
        thus "(map (inv q) [x\<leftarrow>xs. x \<in> range q], inv q ` insert x Y) \<in> failures Q"
         using I by simp
      qed
      thus ?thesis
       by simp
    qed
  next
    assume G: "x \<in> range p"
    show
     "(map (inv p) [x\<leftarrow>xs. x \<in> range p] @ [inv p x], {}) \<in> failures P \<and>
        (map (inv q) [x\<leftarrow>xs. x \<in> range q], {}) \<in> failures Q \<or>
      xs @ [x] \<in> con_comp_divergences P Q p q \<or>
      ?A \<or>
      xs \<in> con_comp_divergences P Q p q"
    proof (cases "(map (inv p) [x\<leftarrow>xs. x \<in> range p] @ [inv p x], {})
     \<in> failures P")
      case True
      moreover have "{} \<subseteq> inv q ` Y" ..
      with F have "(map (inv q) [x\<leftarrow>xs. x \<in> range q], {}) \<in> failures Q"
       by (rule process_rule_3)
      ultimately show ?thesis
       by simp
    next
      case False
      have ?A
      proof (rule_tac x = "insert x X" in exI, rule_tac x = "Y" in exI,
       rule_tac x = "Z" in exI, (subst conj_assoc [symmetric])+, (rule conjI)+)
        show "insert x (X \<union> Y \<union> Z) = insert x X \<union> Y \<union> Z"
         by simp
      next
        show "insert x X \<subseteq> range p"
         using A and G by simp
      next
        show "Y \<subseteq> range q"
         using B .
      next
        show "Z \<subseteq> - range p"
         using C .
      next
        show "Z \<subseteq> - range q"
         using D .
      next
        have
         "(map (inv p) [x\<leftarrow>xs. x \<in> range p] @ [inv p x], {})
            \<in> failures P \<or>
          (map (inv p) [x\<leftarrow>xs. x \<in> range p], insert (inv p x) (inv p ` X))
            \<in> failures P"
         using E by (rule process_rule_4)
        thus "(map (inv p) [x\<leftarrow>xs. x \<in> range p], inv p ` insert x X) \<in> failures P"
         using False by simp
      next
        show "(map (inv q) [x\<leftarrow>xs. x \<in> range q], inv q ` Y) \<in> failures Q"
         using F .
      qed
      thus ?thesis
       by simp
    qed
  next
    assume G: "x \<in> range q"
    show
     "(map (inv p) [x\<leftarrow>xs. x \<in> range p], {}) \<in> failures P \<and>
        (map (inv q) [x\<leftarrow>xs. x \<in> range q] @ [inv q x], {}) \<in> failures Q \<or>
      xs @ [x] \<in> con_comp_divergences P Q p q \<or>
      ?A \<or>
      xs \<in> con_comp_divergences P Q p q"
    proof (cases "(map (inv q) [x\<leftarrow>xs. x \<in> range q] @ [inv q x], {})
     \<in> failures Q")
      case True
      moreover have "{} \<subseteq> inv p ` X" ..
      with E have "(map (inv p) [x\<leftarrow>xs. x \<in> range p], {}) \<in> failures P"
       by (rule process_rule_3)
      ultimately show ?thesis
       by simp
    next
      case False
      have ?A
      proof (rule_tac x = "X" in exI, rule_tac x = "insert x Y" in exI,
       rule_tac x = "Z" in exI, (subst conj_assoc [symmetric])+, (rule conjI)+)
        show "insert x (X \<union> Y \<union> Z) = X \<union> insert x Y \<union> Z"
         by simp
      next
        show "X \<subseteq> range p"
         using A .
      next
        show "insert x Y \<subseteq> range q"
         using B and G by simp
      next
        show "Z \<subseteq> - range p"
         using C .
      next
        show "Z \<subseteq> - range q"
         using D .
      next
        show "(map (inv p) [x\<leftarrow>xs. x \<in> range p], inv p ` X) \<in> failures P"
         using E .
      next
        have
         "(map (inv q) [x\<leftarrow>xs. x \<in> range q] @ [inv q x], {})
            \<in> failures Q \<or>
          (map (inv q) [x\<leftarrow>xs. x \<in> range q], insert (inv q x) (inv q ` Y))
            \<in> failures Q"
         using F by (rule process_rule_4)
        thus "(map (inv q) [x\<leftarrow>xs. x \<in> range q], inv q ` insert x Y) \<in> failures Q"
         using False by simp
      qed
      thus ?thesis
       by simp
    qed
  next
    assume
      G: "x \<notin> range p" and
      H: "x \<notin> range q"
    have ?A
    proof (rule_tac x = "X" in exI, rule_tac x = "Y" in exI,
     rule_tac x = "insert x Z" in exI, (subst conj_assoc [symmetric])+,
     (rule conjI)+)
      show "insert x (X \<union> Y \<union> Z) = X \<union> Y \<union> insert x Z"
       by simp
    next
      show "X \<subseteq> range p"
       using A .
    next
      show "Y \<subseteq> range q"
       using B .
    next
      show "insert x Z \<subseteq> - range p"
       using C and G by simp
    next
      show "insert x Z \<subseteq> - range q"
       using D and H by simp
    next
      show "(map (inv p) [x\<leftarrow>xs. x \<in> range p], inv p ` X) \<in> failures P"
       using E .
    next
      show "(map (inv q) [x\<leftarrow>xs. x \<in> range q], inv q ` Y) \<in> failures Q"
       using F .
    qed
    thus
     "xs @ [x] \<in> con_comp_divergences P Q p q \<or>
      ?A \<or>
      xs \<in> con_comp_divergences P Q p q"
     by simp
  qed
qed

lemma con_comp_prop_5:
 "xs \<in> con_comp_divergences P Q p q \<Longrightarrow>
    xs @ [x] \<in> con_comp_divergences P Q p q"
proof (simp add: con_comp_divergences_def, erule exE, (erule conjE)+, erule exE)
  fix xs' ys'
  assume
    A: "set xs' \<subseteq> range p \<union> range q" and
    B: "map (inv p) [x\<leftarrow>xs'. x \<in> range p] \<in> divergences P" and
    C: "map (inv q) [x\<leftarrow>xs'. x \<in> range q] \<in> divergences Q" and
    D: "xs = xs' @ ys'"
  show "\<exists>xs'.
    (\<exists>ys'. xs @ [x] = xs' @ ys') \<and>
    set xs' \<subseteq> range p \<union> range q \<and>
    map (inv p) [x\<leftarrow>xs'. x \<in> range p] \<in> divergences P \<and>
    map (inv q) [x\<leftarrow>xs'. x \<in> range q] \<in> divergences Q"
  proof (rule_tac x = xs' in exI, simp_all add: A B C)
  qed (rule_tac x = "ys' @ [x]" in exI, simp add: D)
qed

lemma con_comp_prop_6:
 "xs \<in> con_comp_divergences P Q p q \<Longrightarrow>
    (xs, X) \<in> con_comp_failures P Q p q"
by (simp add: con_comp_failures_def)

lemma con_comp_rep:
 "Rep_process (P \<parallel> Q <p, q>) =
    (con_comp_failures P Q p q, con_comp_divergences P Q p q)"
  (is "_ = ?X")
proof (subst con_comp_def, rule Abs_process_inverse, simp add: process_set_def,
 (subst conj_assoc [symmetric])+, (rule conjI)+)
  show "process_prop_1 ?X"
  proof (simp add: process_prop_1_def)
  qed (rule con_comp_prop_1)
next
  show "process_prop_2 ?X"
  proof (simp add: process_prop_2_def del: all_simps, (rule allI)+, rule impI)
  qed (rule con_comp_prop_2)
next
  show "process_prop_3 ?X"
  proof (simp add: process_prop_3_def del: all_simps, (rule allI)+, rule impI,
   erule conjE)
  qed (rule con_comp_prop_3)
next
  show "process_prop_4 ?X"
  proof (simp add: process_prop_4_def, (rule allI)+, rule impI)
  qed (rule con_comp_prop_4)
next
  show "process_prop_5 ?X"
  proof (simp add: process_prop_5_def, rule allI, rule impI, rule allI)
  qed (rule con_comp_prop_5)
next
  show "process_prop_6 ?X"
  proof (simp add: process_prop_6_def, rule allI, rule impI, rule allI)
  qed (rule con_comp_prop_6)
qed

text \<open>
\null

Here below, the previous result is applied to derive useful expressions for the outputs of the
functions returning the elements of a process, as defined in \cite{R1} and \cite{R2}, when acting on
the concurrent composition of a pair of processes.

\null
\<close>

lemma con_comp_failures:
 "failures (P \<parallel> Q <p, q>) = con_comp_failures P Q p q"
by (simp add: failures_def con_comp_rep)

lemma con_comp_divergences:
 "divergences (P \<parallel> Q <p, q>) = con_comp_divergences P Q p q"
by (simp add: divergences_def con_comp_rep)

lemma con_comp_futures:
 "futures (P \<parallel> Q <p, q>) xs =
    {(ys, Y). (xs @ ys, Y) \<in> con_comp_failures P Q p q}"
by (simp add: futures_def con_comp_failures)

lemma con_comp_traces:
 "traces (P \<parallel> Q <p, q>) = Domain (con_comp_failures P Q p q)"
by (simp add: traces_def con_comp_failures)

lemma con_comp_refusals:
 "refusals (P \<parallel> Q <p, q>) xs \<equiv> con_comp_failures P Q p q `` {xs}"
by (simp add: refusals_def con_comp_failures)

lemma con_comp_next_events:
 "next_events (P \<parallel> Q <p, q>) xs =
    {x. xs @ [x] \<in> Domain (con_comp_failures P Q p q)}"
by (simp add: next_events_def con_comp_traces)

text \<open>
\null

In what follows, three lemmas are proven. The first one, whose proof makes use of the axiom of
choice, establishes an additional property required for the above definition of concurrent
composition to be correct, namely that for any two processes whose refusals are closed under set
union, their concurrent composition still be such, which is what is expected for any process of
practical significance (cf. \cite{R2}). The other two lemmas are auxiliary properties of concurrent
composition used in the proof of the target security conservation theorem.

\null
\<close>

lemma con_comp_ref_union_closed:
  assumes
    A: "ref_union_closed P" and
    B: "ref_union_closed Q"
  shows "ref_union_closed (P \<parallel> Q <p, q>)"
proof (simp add: ref_union_closed_def con_comp_failures con_comp_failures_def
 con_comp_divergences_def del: SUP_identity_eq cong: SUP_cong_simp, (rule allI)+, (rule impI)+,
 erule exE, rule disjI1)
  fix xs A X
  assume "\<forall>X \<in> A. \<exists>R S T.
    X = R \<union> S \<union> T \<and>
    set xs \<subseteq> range p \<union> range q \<and>
    R \<subseteq> range p \<and>
    S \<subseteq> range q \<and>
    T \<subseteq> - range p \<and>
    T \<subseteq> - range q \<and>
    (map (inv p) [x\<leftarrow>xs. x \<in> range p], inv p ` R) \<in> failures P \<and>
    (map (inv q) [x\<leftarrow>xs. x \<in> range q], inv q ` S) \<in> failures Q"
    (is "\<forall>X \<in> A. \<exists>R S T. ?F X R S T")
  hence "\<exists>r. \<forall>X \<in> A. \<exists>S T. ?F X (r X) S T"
   by (rule bchoice)
  then obtain r where "\<forall>X \<in> A. \<exists>S T. ?F X (r X) S T" ..
  hence "\<exists>s. \<forall>X \<in> A. \<exists>T. ?F X (r X) (s X) T"
   by (rule bchoice)
  then obtain s where "\<forall>X \<in> A. \<exists>T. ?F X (r X) (s X) T" ..
  hence "\<exists>t. \<forall>X \<in> A. ?F X (r X) (s X) (t X)"
   by (rule bchoice)
  then obtain t where C: "\<forall>X \<in> A. ?F X (r X) (s X) (t X)" ..
  assume D: "X \<in> A"
  show "\<exists>R S T. ?F (\<Union>X \<in> A. X) R S T"
  proof (rule_tac x = "\<Union>X \<in> A. r X" in exI, rule_tac x = "\<Union>X \<in> A. s X" in exI,
   rule_tac x = "\<Union>X \<in> A. t X" in exI, (subst conj_assoc [symmetric])+,
   (rule conjI)+)
    show "(\<Union>X \<in> A. X) = (\<Union>X \<in> A. r X) \<union> (\<Union>X \<in> A. s X) \<union> (\<Union>X \<in> A. t X)"
    proof (simp add: set_eq_iff, rule allI, rule iffI, erule_tac [2] disjE,
     erule_tac [3] disjE, erule_tac [!] bexE)
      fix x X
      have "\<forall>X \<in> A. X = r X \<union> s X \<union> t X"
       using C by simp
      moreover assume E: "X \<in> A"
      ultimately have "X = r X \<union> s X \<union> t X" ..
      moreover assume "x \<in> X"
      ultimately have "x \<in> r X \<or> x \<in> s X \<or> x \<in> t X"
       by blast
      hence "\<exists>X \<in> A. x \<in> r X \<or> x \<in> s X \<or> x \<in> t X"
       using E ..
      thus "(\<exists>X \<in> A. x \<in> r X) \<or> (\<exists>X \<in> A. x \<in> s X) \<or> (\<exists>X \<in> A. x \<in> t X)"
       by blast
    next
      fix x X
      have "\<forall>X \<in> A. X = r X \<union> s X \<union> t X"
       using C by simp
      moreover assume E: "X \<in> A"
      ultimately have "X = r X \<union> s X \<union> t X" ..
      moreover assume "x \<in> r X"
      ultimately have "x \<in> X"
       by blast
      thus "\<exists>X \<in> A. x \<in> X"
       using E ..
    next
      fix x X
      have "\<forall>X \<in> A. X = r X \<union> s X \<union> t X"
       using C by simp
      moreover assume E: "X \<in> A"
      ultimately have "X = r X \<union> s X \<union> t X" ..
      moreover assume "x \<in> s X"
      ultimately have "x \<in> X"
       by blast
      thus "\<exists>X \<in> A. x \<in> X"
       using E ..
    next
      fix x X
      have "\<forall>X \<in> A. X = r X \<union> s X \<union> t X"
       using C by simp
      moreover assume E: "X \<in> A"
      ultimately have "X = r X \<union> s X \<union> t X" ..
      moreover assume "x \<in> t X"
      ultimately have "x \<in> X"
       by blast
      thus "\<exists>X \<in> A. x \<in> X"
       using E ..
    qed
  next
    have "\<forall>X \<in> A. set xs \<subseteq> range p \<union> range q"
     using C by simp
    thus "set xs \<subseteq> range p \<union> range q"
     using D ..
  next
    show "(\<Union>X \<in> A. r X) \<subseteq> range p"
    proof (rule subsetI, erule UN_E)
      fix x X
      have "\<forall>X \<in> A. r X \<subseteq> range p"
       using C by simp
      moreover assume "X \<in> A"
      ultimately have "r X \<subseteq> range p" ..
      moreover assume "x \<in> r X"
      ultimately show "x \<in> range p" ..
    qed
  next
    show "(\<Union>X \<in> A. s X) \<subseteq> range q"
    proof (rule subsetI, erule UN_E)
      fix x X
      have "\<forall>X \<in> A. s X \<subseteq> range q"
       using C by simp
      moreover assume "X \<in> A"
      ultimately have "s X \<subseteq> range q" ..
      moreover assume "x \<in> s X"
      ultimately show "x \<in> range q" ..
    qed
  next
    show "(\<Union>X \<in> A. t X) \<subseteq> - range p"
    proof (rule subsetI, erule UN_E)
      fix x X
      have "\<forall>X \<in> A. t X \<subseteq> - range p"
       using C by simp
      moreover assume "X \<in> A"
      ultimately have "t X \<subseteq> - range p" ..
      moreover assume "x \<in> t X"
      ultimately show "x \<in> - range p" ..
    qed
  next
    show "(\<Union>X \<in> A. t X) \<subseteq> - range q"
    proof (rule subsetI, erule UN_E)
      fix x X
      have "\<forall>X \<in> A. t X \<subseteq> - range q"
       using C by simp
      moreover assume "X \<in> A"
      ultimately have "t X \<subseteq> - range q" ..
      moreover assume "x \<in> t X"
      ultimately show "x \<in> - range q" ..
    qed
  next
    let ?A' = "{inv p ` X | X. X \<in> r ` A}"
    have
     "(\<exists>X. X \<in> ?A') \<longrightarrow>
      (\<forall>X \<in> ?A'. (map (inv p) [x\<leftarrow>xs. x \<in> range p], X) \<in> failures P) \<longrightarrow>
        (map (inv p) [x\<leftarrow>xs. x \<in> range p], \<Union>X \<in> ?A'. X) \<in> failures P"
     using A by (simp add: ref_union_closed_def)
    moreover have "\<exists>X. X \<in> ?A'"
     using D by blast
    ultimately have
     "(\<forall>X \<in> ?A'. (map (inv p) [x\<leftarrow>xs. x \<in> range p], X) \<in> failures P) \<longrightarrow>
        (map (inv p) [x\<leftarrow>xs. x \<in> range p], \<Union>X \<in> ?A'. X) \<in> failures P" ..
    moreover have
     "\<forall>X \<in> ?A'. (map (inv p) [x\<leftarrow>xs. x \<in> range p], X) \<in> failures P"
    proof (rule ballI, simp, erule exE, erule conjE)
      fix R R'
      assume "R \<in> r ` A"
      hence "\<exists>X \<in> A. R = r X"
       by (simp add: image_iff)
      then obtain X where E: "X \<in> A" and F: "R = r X" ..
      have "\<forall>X \<in> A. (map (inv p) [x\<leftarrow>xs. x \<in> range p], inv p ` r X) \<in> failures P"
       using C by simp
      hence "(map (inv p) [x\<leftarrow>xs. x \<in> range p], inv p ` r X) \<in> failures P"
       using E ..
      moreover assume "R' = inv p ` R"
      ultimately show "(map (inv p) [x\<leftarrow>xs. x \<in> range p], R') \<in> failures P"
       using F by simp
    qed
    ultimately have "(map (inv p) [x\<leftarrow>xs. x \<in> range p], \<Union>X \<in> ?A'. X)
      \<in> failures P" ..
    moreover have "(\<Union>X \<in> ?A'. X) = inv p ` (\<Union>X \<in> A. r X)"
    proof (subst set_eq_iff, simp, rule allI, rule iffI, (erule exE, erule conjE)+)
      fix a R R'
      assume "R \<in> r ` A"
      hence "\<exists>X \<in> A. R = r X"
       by (simp add: image_iff)
      then obtain X where E: "X \<in> A" and F: "R = r X" ..
      assume "a \<in> R'" and "R' = inv p ` R"
      hence "a \<in> inv p ` r X"
       using F by simp
      hence "\<exists>x \<in> r X. a = inv p x"
       by (simp add: image_iff)
      then obtain x where G: "x \<in> r X" and H: "a = inv p x" ..
      have "x \<in> (\<Union>X \<in> A. r X)"
       using E and G by (rule UN_I)
      with H have "\<exists>x \<in> (\<Union>X \<in> A. r X). a = inv p x" ..
      thus "a \<in> inv p ` (\<Union>X \<in> A. r X)"
       by (simp add: image_iff)
    next
      fix a
      assume "a \<in> inv p ` (\<Union>X \<in> A. r X)"
      hence "\<exists>x \<in> (\<Union>X \<in> A. r X). a = inv p x"
       by (simp add: image_iff)
      then obtain x where E: "x \<in> (\<Union>X \<in> A. r X)" and F: "a = inv p x" ..
      obtain X where G: "X \<in> A" and H: "x \<in> r X" using E ..
      show "\<exists>R'. (\<exists>R. R' = inv p ` R \<and> R \<in> r ` A) \<and> a \<in> R'"
      proof (rule_tac x = "inv p ` r X" in exI, rule conjI,
       rule_tac x = "r X" in exI)
      qed (rule_tac [2] image_eqI, simp add: G, simp add: F, simp add: H)
    qed
    ultimately show "(map (inv p) [x\<leftarrow>xs. x \<in> range p], inv p ` (\<Union>X \<in> A. r X))
      \<in> failures P"
     by simp
  next
    let ?A' = "{inv q ` X | X. X \<in> s ` A}"
    have
     "(\<exists>X. X \<in> ?A') \<longrightarrow>
      (\<forall>X \<in> ?A'. (map (inv q) [x\<leftarrow>xs. x \<in> range q], X) \<in> failures Q) \<longrightarrow>
        (map (inv q) [x\<leftarrow>xs. x \<in> range q], \<Union>X \<in> ?A'. X) \<in> failures Q"
     using B by (simp add: ref_union_closed_def)
    moreover have "\<exists>X. X \<in> ?A'"
     using D by blast
    ultimately have
     "(\<forall>X \<in> ?A'. (map (inv q) [x\<leftarrow>xs. x \<in> range q], X) \<in> failures Q) \<longrightarrow>
        (map (inv q) [x\<leftarrow>xs. x \<in> range q], \<Union>X \<in> ?A'. X) \<in> failures Q" ..
    moreover have
     "\<forall>X \<in> ?A'. (map (inv q) [x\<leftarrow>xs. x \<in> range q], X) \<in> failures Q"
    proof (rule ballI, simp, erule exE, erule conjE)
      fix S S'
      assume "S \<in> s ` A"
      hence "\<exists>X \<in> A. S = s X"
       by (simp add: image_iff)
      then obtain X where E: "X \<in> A" and F: "S = s X" ..
      have "\<forall>X \<in> A. (map (inv q) [x\<leftarrow>xs. x \<in> range q], inv q ` s X) \<in> failures Q"
       using C by simp
      hence "(map (inv q) [x\<leftarrow>xs. x \<in> range q], inv q ` s X) \<in> failures Q"
       using E ..
      moreover assume "S' = inv q ` S"
      ultimately show "(map (inv q) [x\<leftarrow>xs. x \<in> range q], S') \<in> failures Q"
       using F by simp
    qed
    ultimately have "(map (inv q) [x\<leftarrow>xs. x \<in> range q], \<Union>X \<in> ?A'. X)
      \<in> failures Q" ..
    moreover have "(\<Union>X \<in> ?A'. X) = inv q ` (\<Union>X \<in> A. s X)"
    proof (subst set_eq_iff, simp, rule allI, rule iffI, (erule exE, erule conjE)+)
      fix b S S'
      assume "S \<in> s ` A"
      hence "\<exists>X \<in> A. S = s X"
       by (simp add: image_iff)
      then obtain X where E: "X \<in> A" and F: "S = s X" ..
      assume "b \<in> S'" and "S' = inv q ` S"
      hence "b \<in> inv q ` s X"
       using F by simp
      hence "\<exists>x \<in> s X. b = inv q x"
       by (simp add: image_iff)
      then obtain x where G: "x \<in> s X" and H: "b = inv q x" ..
      have "x \<in> (\<Union>X \<in> A. s X)"
       using E and G by (rule UN_I)
      with H have "\<exists>x \<in> (\<Union>X \<in> A. s X). b = inv q x" ..
      thus "b \<in> inv q ` (\<Union>X \<in> A. s X)"
       by (simp add: image_iff)
    next
      fix b
      assume "b \<in> inv q ` (\<Union>X \<in> A. s X)"
      hence "\<exists>x \<in> (\<Union>X \<in> A. s X). b = inv q x"
       by (simp add: image_iff)
      then obtain x where E: "x \<in> (\<Union>X \<in> A. s X)" and F: "b = inv q x" ..
      obtain X where G: "X \<in> A" and H: "x \<in> s X" using E ..
      show "\<exists>S'. (\<exists>S. S' = inv q ` S \<and> S \<in> s ` A) \<and> b \<in> S'"
      proof (rule_tac x = "inv q ` s X" in exI, rule conjI,
       rule_tac x = "s X" in exI)
      qed (rule_tac [2] image_eqI, simp add: G, simp add: F, simp add: H)
    qed
    ultimately show "(map (inv q) [x\<leftarrow>xs. x \<in> range q], inv q ` (\<Union>X \<in> A. s X))
      \<in> failures Q"
     by simp
  qed
qed

lemma con_comp_failures_traces:
 "(xs, X) \<in> con_comp_failures P Q p q \<Longrightarrow>
    map (inv p) [x\<leftarrow>xs. x \<in> range p] \<in> traces P \<and>
    map (inv q) [x\<leftarrow>xs. x \<in> range q] \<in> traces Q"
proof (simp add: con_comp_failures_def con_comp_divergences_def, erule disjE,
 (erule exE)+, (erule conjE)+, erule_tac [2] exE, (erule_tac [2] conjE)+,
 erule_tac [2] exE)
  fix X Y
  assume "(map (inv p) [x\<leftarrow>xs. x \<in> range p], inv p ` X) \<in> failures P"
  hence "map (inv p) [x\<leftarrow>xs. x \<in> range p] \<in> traces P"
   by (rule failures_traces)
  moreover assume "(map (inv q) [x\<leftarrow>xs. x \<in> range q], inv q ` Y) \<in> failures Q"
  hence "map (inv q) [x\<leftarrow>xs. x \<in> range q] \<in> traces Q"
   by (rule failures_traces)
  ultimately show ?thesis ..
next
  fix vs ws
  assume A: "xs = vs @ ws"
  assume "map (inv p) [x\<leftarrow>vs. x \<in> range p] \<in> divergences P"
  hence "map (inv p) [x\<leftarrow>vs. x \<in> range p] @ map (inv p) [x\<leftarrow>ws. x \<in> range p]
    \<in> divergences P"
   by (rule process_rule_5_general)
  hence "map (inv p) [x\<leftarrow>xs. x \<in> range p] \<in> divergences P"
   using A by simp
  hence "(map (inv p) [x\<leftarrow>xs. x \<in> range p], {}) \<in> failures P"
   by (rule process_rule_6)
  hence "map (inv p) [x\<leftarrow>xs. x \<in> range p] \<in> traces P"
   by (rule failures_traces)
  moreover assume "map (inv q) [x\<leftarrow>vs. x \<in> range q] \<in> divergences Q"
  hence "map (inv q) [x\<leftarrow>vs. x \<in> range q] @ map (inv q) [x\<leftarrow>ws. x \<in> range q]
    \<in> divergences Q"
   by (rule process_rule_5_general)
  hence "map (inv q) [x\<leftarrow>xs. x \<in> range q] \<in> divergences Q"
   using A by simp
  hence "(map (inv q) [x\<leftarrow>xs. x \<in> range q], {}) \<in> failures Q"
   by (rule process_rule_6)
  hence "map (inv q) [x\<leftarrow>xs. x \<in> range q] \<in> traces Q"
   by (rule failures_traces)
  ultimately show ?thesis ..
qed

lemma con_comp_failures_divergences:
 "(xs @ y # ys, Y) \<in> con_comp_failures P Q p q \<Longrightarrow>
  y \<notin> range p \<Longrightarrow>
  y \<notin> range q \<Longrightarrow>
    \<exists>xs'.
      (\<exists>ys'. xs @ zs = xs' @ ys') \<and>
      set xs' \<subseteq> range p \<union> range q \<and>
      map (inv p) [x\<leftarrow>xs'. x \<in> range p] \<in> divergences P \<and>
      map (inv q) [x\<leftarrow>xs'. x \<in> range q] \<in> divergences Q"
proof (simp add: con_comp_failures_def con_comp_divergences_def,
 erule exE, (erule conjE)+, erule exE)
  fix xs' ys'
  assume
    A: "y \<notin> range p" and
    B: "y \<notin> range q" and
    C: "set xs' \<subseteq> range p \<union> range q" and
    D: "map (inv p) [x\<leftarrow>xs'. x \<in> range p] \<in> divergences P" and
    E: "map (inv q) [x\<leftarrow>xs'. x \<in> range q] \<in> divergences Q" and
    F: "xs @ y # ys = xs' @ ys'"
  have "length xs' \<le> length xs"
  proof (rule ccontr)
    assume "\<not> length xs' \<le> length xs"
    moreover have "take (length xs') (xs @ [y] @ ys) =
      take (length xs') (xs @ [y]) @ take (length xs' - Suc (length xs)) ys"
      (is "_ = _ @ ?vs")
     by (simp only: take_append, simp)
    ultimately have "take (length xs') (xs @ y # ys) = xs @ y # ?vs"
     by simp
    moreover have "take (length xs') (xs @ y # ys) =
      take (length xs') (xs' @ ys')"
     using F by simp
    ultimately have "xs' = xs @ y # ?vs"
     by simp
    hence "set (xs @ y # ?vs) \<subseteq> range p \<union> range q"
     using C by simp
    hence "y \<in> range p \<union> range q"
     by simp
    thus False
     using A and B by simp
  qed
  moreover have "xs @ zs =
    take (length xs') (xs @ zs) @ drop (length xs') (xs @ zs)"
    (is "_ = _ @ ?vs")
   by (simp only: append_take_drop_id)
  ultimately have "xs @ zs = take (length xs') (xs @ y # ys) @ ?vs"
   by simp
  moreover have "take (length xs') (xs @ y # ys) =
    take (length xs') (xs' @ ys')"
   using F by simp
  ultimately have G: "xs @ zs = xs' @ ?vs"
   by (simp del: take_append, simp)
  show ?thesis
  proof (rule_tac x = xs' in exI, rule conjI, rule_tac x = ?vs in exI)
  qed (subst G, simp_all add: C D E)
qed

text \<open>
\null

In order to prove that CSP noninterference security is conserved under concurrent composition, the
first issue to be solved is to identify the noninterference policy @{term I'} and the event-domain
map @{term D'} with respect to which the output process is secure.

If the events of the input processes corresponding to those of the output process contained in
@{term "range p \<inter> range q"} were mapped by the respective event-domain maps @{term D}, @{term E}
into distinct security domains, there would be no criterion for determining the domains of the
aforesaid events of the output process, due to the equivalence of the input processes ensuing from
the commutative property of concurrent composition. Therefore, @{term D} and @{term E} must map the
events of the input processes into security domains of the same type @{typ 'd}, and for each
@{term x} in @{term "range p \<inter> range q"}, @{term D} and @{term E} must map the events of the input
processes corresponding to @{term x} into the same domain. This requirement is formalized here below
by means of predicate \<open>consistent_maps\<close>.

Similarly, if distinct noninterference policies applied to the input processes, there would exist
some ordered pair of security domains included in one of the policies, but not in the other one.
Thus, again, there would be no criterion for determining the inclusion of such a pair of domains in
the policy @{term I'} applying to the output process. As a result, the input processes are required
to enforce the same noninterference policy @{term I}, so that for any two domains @{term d},
@{term e} of type @{typ 'd}, the ordered pair comprised of the corresponding security domains for
the output process will be included in @{term I'} just in case @{term "(d, e) \<in> I"}.

However, in case @{term "- (range p \<union> range q) \<noteq> {}"}, the event-domain map @{term D'} for the
output process must assign a security domain to the fake events in @{term "- (range p \<union> range q)"}
as well. Since such events lack any meaning, they may all be mapped to the same security domain,
distinct from the domains of the meaningful events in @{term "range p \<union> range q"}. A simple way to
do this is to identify the type of the security domains for the output process with
@{typ "'d option"}. Then, for any meaningful event @{term x}, @{term D'} will assign @{term x} to
domain @{term "Some d"}, where @{term d} is the domain of the events of the input processes mapped
to @{term x}, whereas @{term "D' y = None"} for any fake event @{term y}. Such an event-domain map,
denoted using notation @{term "con_comp_map D E p q"}, is defined here below.

Therefore, for any two security domains @{term "Some d"}, @{term "Some e"} for the output process,
the above considerations about policy @{term I'} entail that @{term "(Some d, Some e) \<in> I'"} just in
case @{term "(d, e) \<in> I"}. Furthermore, since fake events may only occur in divergent traces, which
are extensions of divergences of the input processes comprised of meaningful events, @{term I'} must
allow the security domain @{term None} of fake events to be affected by any meaningful domain
matching pattern \<open>Some _\<close>. Such a noninterference policy, denoted using notation
@{term "con_comp_pol I"}, is defined here below. Observe that @{term "con_comp_pol I"} keeps being
reflexive or transitive if @{term I} is.

\null
\<close>

definition con_comp_pol ::
 "('d \<times> 'd) set \<Rightarrow> ('d option \<times> 'd option) set" where
"con_comp_pol I \<equiv>
  {(Some d, Some e) | d e. (d, e) \<in> I} \<union> {(u, v). v = None}"

function con_comp_map ::
 "('a \<Rightarrow> 'd) \<Rightarrow> ('b \<Rightarrow> 'd) \<Rightarrow> ('a \<Rightarrow> 'c) \<Rightarrow> ('b \<Rightarrow> 'c) \<Rightarrow> 'c \<Rightarrow> 'd option" where
"x \<in> range p \<Longrightarrow>
  con_comp_map D E p q x = Some (D (inv p x))" |
"x \<notin> range p \<Longrightarrow> x \<in> range q \<Longrightarrow>
  con_comp_map D E p q x = Some (E (inv q x))" |
"x \<notin> range p \<Longrightarrow> x \<notin> range q \<Longrightarrow>
  con_comp_map D E p q x = None"
by (atomize_elim, simp_all add: split_paired_all, blast)
termination by lexicographic_order

definition consistent_maps ::
 "('a \<Rightarrow> 'd) \<Rightarrow> ('b \<Rightarrow> 'd) \<Rightarrow> ('a \<Rightarrow> 'c) \<Rightarrow> ('b \<Rightarrow> 'c) \<Rightarrow> bool" where
"consistent_maps D E p q \<equiv>
  \<forall>x \<in> range p \<inter> range q. D (inv p x) = E (inv q x)"


subsection "Auxiliary intransitive purge functions"

text \<open>
Let @{term I} be a noninterference policy, @{term D} an event-domain map, @{term U} a domain set,
and @{term "xs = x # xs'"} an event list. Suppose to take event @{term x} just in case it satisfies
predicate @{term P}, to append @{term xs'} to the resulting list (matching either @{term "[x]"} or
@{term "[]"}), and then to compute the intransitive purge of the resulting list with domain set
@{term U}. If recursion with respect to the input list is added, replacing @{term xs'} with the list
produced by the same algorithm using @{term xs'} as input list and @{term "sinks_aux I D U [x]"} as
domain set, the final result matches that obtained by applying filter @{term P} to the intransitive
purge of @{term xs} with domain set @{term U}. In fact, in each recursive step, the processed item
of the input list is retained in the output list just in case it passes filter @{term P} and may be
affected neither by the domains in @{term U}, nor by the domains of the previous items affected by
some domain in @{term U}.

Here below is the formal definition of such purge function, named \<open>ipurge_tr_aux_foldr\<close> as its
action resembles that of function @{term foldr}.

\null
\<close>

primrec ipurge_tr_aux_foldr ::
 "('d \<times> 'd) set \<Rightarrow> ('a \<Rightarrow> 'd) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'd set \<Rightarrow> 'a list \<Rightarrow> 'a list"
where
"ipurge_tr_aux_foldr I D P U [] = []" |
"ipurge_tr_aux_foldr I D P U (x # xs) = ipurge_tr_aux I D U
   ((if P x then [x] else []) @
     ipurge_tr_aux_foldr I D P (sinks_aux I D U [x]) xs)"

text \<open>
\null

Likewise, given @{term I}, @{term D}, @{term U}, @{term "xs = x # xs'"}, and an event set @{term X},
suppose to take @{term x} just in case it satisfies predicate @{term P}, to append
@{term "ipurge_tr_aux_foldr I D P (sinks_aux I D U [x]) xs'"} to the resulting list (matching either
@{term "[x]"} or @{term "[]"}), and then to compute the intransitive purge of @{term X} using the
resulting list as input list and @{term U} as domain set. If recursion with respect to the input
list is added, replacing @{term X} with the set produced by the same algorithm using @{term xs'} as
input list, @{term X} as input set, and @{term "sinks_aux I D U [x]"} as domain set, the final
result matches the intransitive purge of @{term X} with input list @{term xs} and domain set
@{term U}. In fact, each recursive step is such as to remove from @{term X} any event that may be
affected either by the domains in @{term U}, or by the domains of the items of @{term xs} preceding
the processed one which are affected by some domain in @{term U}.

From the above considerations on function @{term ipurge_tr_aux_foldr}, it follows that the presence
of list @{term "ipurge_tr_aux_foldr I D P (sinks_aux I D U [x]) xs'"} has no impact on the final
result, because none of its items may be affected by the domains in @{term U}.

Here below is the formal definition of such purge function, named \<open>ipurge_ref_aux_foldr\<close>,
which at first glance just seems a uselessly complicate and inefficient way to compute the
intransitive purge of an event set.

\null
\<close>

primrec ipurge_ref_aux_foldr ::
 "('d \<times> 'd) set \<Rightarrow> ('a \<Rightarrow> 'd) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'd set \<Rightarrow> 'a list \<Rightarrow> 'a set \<Rightarrow> 'a set"
where
"ipurge_ref_aux_foldr I D P U [] X = ipurge_ref_aux I D U [] X" |
"ipurge_ref_aux_foldr I D P U (x # xs) X = ipurge_ref_aux I D U
   ((if P x then [x] else []) @
     ipurge_tr_aux_foldr I D P (sinks_aux I D U [x]) xs)
   (ipurge_ref_aux_foldr I D P (sinks_aux I D U [x]) xs X)"

text \<open>
\null

The reason for the introduction of such intransitive purge functions is that the recursive equations
contained in their definitions, along with lemma @{thm [source] ipurge_tr_ref_aux_failures_general},
enable to prove by induction on list @{term ys}, assuming that process @{term P} be secure in
addition to further, minor premises, the following implication:

\null

@{term "(map (inv p) [x\<leftarrow>xs @ ys. x \<in> range p], inv p ` Y) \<in> failures P \<longrightarrow>
  (map (inv p) [x\<leftarrow>xs. x \<in> range p] @
   map (inv p) (ipurge_tr_aux_foldr (con_comp_pol I) (con_comp_map D E p q)
     (\<lambda>x. x \<in> range p) U ys),
   inv p ` ipurge_ref_aux_foldr (con_comp_pol I) (con_comp_map D E p q)
     (\<lambda>x. x \<in> range p) U ys Y) \<in> failures P"}

\null

In fact, for @{term "ys = y # ys'"}, the induction hypothesis entails that the consequent holds if
@{term xs}, @{term ys}, and @{term U} are replaced with @{term "xs @ [y]"}, @{term ys'}, and
@{term "sinks_aux (con_comp_pol I) (con_comp_map D E p q) U [y]"}, respectively. The proof can then
be accomplished by applying lemma @{thm [source] ipurge_tr_ref_aux_failures_general} to the
resulting future of trace @{term "map (inv p) [x\<leftarrow>xs. x \<in> range p]"}, moving functions
@{term ipurge_tr_aux} and @{term "ipurge_ref_aux"} into the arguments of @{term "map (inv p)"} and
@{term "(`) (inv p)"}, and using the recursive equations contained in the definitions of functions
@{term ipurge_tr_aux_foldr} and @{term ipurge_ref_aux_foldr}.

This property, along with the match of the outputs of functions @{term ipurge_tr_aux_foldr} and
@{term ipurge_ref_aux_foldr} with the filtered intransitive purge of the input event list and the
intransitive purge of the input event set, respectively, permits to solve the main proof obligations
arising from the demonstration of the target security conservation theorem.

Here below is the proof of the equivalence between function @{term ipurge_tr_aux_foldr} and the
filtered intransitive purge of an event list.

\null
\<close>

lemma ipurge_tr_aux_foldr_subset:
 "U \<subseteq> V \<Longrightarrow>
  ipurge_tr_aux I D U (ipurge_tr_aux_foldr I D P V xs) =
    ipurge_tr_aux_foldr I D P V xs"
proof (induction xs, simp_all add: ipurge_tr_aux_union [symmetric])
qed (drule Un_absorb2, simp)

lemma ipurge_tr_aux_foldr_eq:
 "[x\<leftarrow>ipurge_tr_aux I D U xs. P x] = ipurge_tr_aux_foldr I D P U xs"
proof (induction xs arbitrary: U, simp)
  fix x xs U
  assume
    A: "\<And>U. [x\<leftarrow>ipurge_tr_aux I D U xs. P x] = ipurge_tr_aux_foldr I D P U xs"
  show "[x\<leftarrow>ipurge_tr_aux I D U (x # xs). P x] =
    ipurge_tr_aux_foldr I D P U (x # xs)"
  proof (cases "\<exists>u \<in> U. (u, D x) \<in> I",
   simp_all only: ipurge_tr_aux_foldr.simps ipurge_tr_aux_cons
   sinks_aux_single_event if_True if_False)
    case True
    have B: "[x\<leftarrow>ipurge_tr_aux I D (insert (D x) U) xs. P x] =
      ipurge_tr_aux_foldr I D P (insert (D x) U) xs"
     using A .
    show "[x\<leftarrow>ipurge_tr_aux I D (insert (D x) U) xs. P x] = ipurge_tr_aux I D U
      ((if P x then [x] else []) @ ipurge_tr_aux_foldr I D P (insert (D x) U) xs)"
    proof (cases "P x", simp_all add: ipurge_tr_aux_cons True
     del: con_comp_map.simps)
      have "insert (D x) U \<subseteq> insert (D x) U" ..
      hence "ipurge_tr_aux I D (insert (D x) U)
        (ipurge_tr_aux_foldr I D P (insert (D x) U) xs) =
          ipurge_tr_aux_foldr I D P (insert (D x) U) xs"
       by (rule ipurge_tr_aux_foldr_subset)
      thus "[x\<leftarrow>ipurge_tr_aux I D (insert (D x) U) xs. P x] =
        ipurge_tr_aux I D (insert (D x) U)
          (ipurge_tr_aux_foldr I D P (insert (D x) U) xs)"
       using B by simp
    next
      have "U \<subseteq> insert (D x) U"
       by (rule subset_insertI)
      hence "ipurge_tr_aux I D U
        (ipurge_tr_aux_foldr I D P (insert (D x) U) xs) =
          ipurge_tr_aux_foldr I D P (insert (D x) U) xs"
       by (rule ipurge_tr_aux_foldr_subset)
      thus "[x\<leftarrow>ipurge_tr_aux I D (insert (D x) U) xs. P x] =
        ipurge_tr_aux I D U
          (ipurge_tr_aux_foldr I D P (insert (D x) U) xs)"
       using B by simp
    qed
  next
    case False
    have B: "[x\<leftarrow>ipurge_tr_aux I D U xs. P x] = ipurge_tr_aux_foldr I D P U xs"
     using A .
    show "[x\<leftarrow>x # ipurge_tr_aux I D U xs. P x] = ipurge_tr_aux I D U
      ((if P x then [x] else []) @ ipurge_tr_aux_foldr I D P U xs)"
    proof (cases "P x", simp_all add: ipurge_tr_aux_cons False
     del: con_comp_map.simps)
      have "U \<subseteq> U" ..
      hence "ipurge_tr_aux I D U (ipurge_tr_aux_foldr I D P U xs) =
        ipurge_tr_aux_foldr I D P U xs"
       by (rule ipurge_tr_aux_foldr_subset)
      thus "[x\<leftarrow>ipurge_tr_aux I D U xs. P x] =
        ipurge_tr_aux I D U (ipurge_tr_aux_foldr I D P U xs)"
       using B by simp
    next
      have "U \<subseteq> U" ..
      hence "ipurge_tr_aux I D U (ipurge_tr_aux_foldr I D P U xs) =
        ipurge_tr_aux_foldr I D P U xs"
       by (rule ipurge_tr_aux_foldr_subset)
      thus "[x\<leftarrow>ipurge_tr_aux I D U xs. P x] =
        ipurge_tr_aux I D U (ipurge_tr_aux_foldr I D P U xs)"
       using B by simp
    qed
  qed
qed

text \<open>
\null

Here below is the proof of the equivalence between function @{term ipurge_ref_aux_foldr} and the
intransitive purge of an event set.

\null
\<close>

lemma ipurge_tr_aux_foldr_sinks_aux [rule_format]:
 "U \<subseteq> V \<longrightarrow> sinks_aux I D U (ipurge_tr_aux_foldr I D P V xs) = U"
proof (induction xs arbitrary: V, simp, rule impI)
  fix x xs V
  assume
    A: "\<And>V. U \<subseteq> V \<longrightarrow> sinks_aux I D U (ipurge_tr_aux_foldr I D P V xs) = U" and
    B: "U \<subseteq> V"
  show "sinks_aux I D U (ipurge_tr_aux_foldr I D P V (x # xs)) = U"
  proof (cases "P x", case_tac [!] "\<exists>v \<in> V. (v, D x) \<in> I",
   simp_all (no_asm_simp) add: sinks_aux_cons ipurge_tr_aux_cons)
    have "U \<subseteq> insert (D x) V \<longrightarrow>
      sinks_aux I D U (ipurge_tr_aux_foldr I D P (insert (D x) V) xs) = U"
      (is "_ \<longrightarrow> sinks_aux I D U ?ys = U")
     using A .
    moreover have "U \<subseteq> insert (D x) V"
     using B by (rule subset_insertI2)
    ultimately have "sinks_aux I D U ?ys = U" ..
    moreover have "insert (D x) V \<subseteq> insert (D x) V" ..
    hence "ipurge_tr_aux I D (insert (D x) V)
      (ipurge_tr_aux_foldr I D P (insert (D x) V) xs) = ?ys"
      (is "?zs = _")
     by (rule ipurge_tr_aux_foldr_subset)
    ultimately show "sinks_aux I D U ?zs = U"
     by simp
  next
    assume C: "\<not> (\<exists>v \<in> V. (v, D x) \<in> I)"
    have "\<not> (\<exists>u \<in> U. (u, D x) \<in> I)"
    proof
      assume "\<exists>u \<in> U. (u, D x) \<in> I"
      then obtain u where D: "u \<in> U" and E: "(u, D x) \<in> I" ..
      have "u \<in> V"
       using B and D ..
      with E have "\<exists>v \<in> V. (v, D x) \<in> I" ..
      thus False
       using C by contradiction
    qed
    thus
     "((\<exists>v \<in> U. (v, D x) \<in> I) \<longrightarrow> sinks_aux I D (insert (D x) U)
        (ipurge_tr_aux I D V (ipurge_tr_aux_foldr I D P V xs)) = U) \<and>
      ((\<forall>v \<in> U. (v, D x) \<notin> I) \<longrightarrow> sinks_aux I D U
        (ipurge_tr_aux I D V (ipurge_tr_aux_foldr I D P V xs)) = U)"
    proof simp
      have "U \<subseteq> V \<longrightarrow> sinks_aux I D U (ipurge_tr_aux_foldr I D P V xs) = U"
        (is "_ \<longrightarrow> sinks_aux I D U ?ys = U")
       using A .
      hence "sinks_aux I D U ?ys = U" using B ..
      moreover have "V \<subseteq> V" ..
      hence "ipurge_tr_aux I D V (ipurge_tr_aux_foldr I D P V xs) = ?ys"
        (is "?zs = _")
       by (rule ipurge_tr_aux_foldr_subset)
      ultimately show "sinks_aux I D U ?zs = U"
       by simp
    qed
  next
    have "U \<subseteq> insert (D x) V \<longrightarrow>
      sinks_aux I D U (ipurge_tr_aux_foldr I D P (insert (D x) V) xs) = U"
      (is "_ \<longrightarrow> sinks_aux I D U ?ys = U")
     using A .
    moreover have "U \<subseteq> insert (D x) V"
     using B by (rule subset_insertI2)
    ultimately have "sinks_aux I D U ?ys = U" ..
    moreover have "V \<subseteq> insert (D x) V"
     by (rule subset_insertI)
    hence "ipurge_tr_aux I D V
      (ipurge_tr_aux_foldr I D P (insert (D x) V) xs) = ?ys"
      (is "?zs = _")
     by (rule ipurge_tr_aux_foldr_subset)
    ultimately show "sinks_aux I D U ?zs = U"
     by simp
  next
    have "U \<subseteq> V \<longrightarrow> sinks_aux I D U (ipurge_tr_aux_foldr I D P V xs) = U"
      (is "_ \<longrightarrow> sinks_aux I D U ?ys = U")
     using A .
    hence "sinks_aux I D U ?ys = U" using B ..
    moreover have "V \<subseteq> V" ..
    hence "ipurge_tr_aux I D V (ipurge_tr_aux_foldr I D P V xs) = ?ys"
      (is "?zs = _")
     by (rule ipurge_tr_aux_foldr_subset)
    ultimately show "sinks_aux I D U ?zs = U"
     by simp
  qed
qed

lemma ipurge_tr_aux_foldr_ref_aux:
  assumes A: "U \<subseteq> V"
  shows "ipurge_ref_aux I D U (ipurge_tr_aux_foldr I D P V xs) X =
    ipurge_ref_aux I D U [] X"
by (simp add: ipurge_ref_aux_def ipurge_tr_aux_foldr_sinks_aux [OF A])

lemma ipurge_ref_aux_foldr_subset [rule_format]:
 "sinks_aux I D U ys \<subseteq> V \<longrightarrow>
  ipurge_ref_aux I D U ys (ipurge_ref_aux_foldr I D P V xs X) =
    ipurge_ref_aux_foldr I D P V xs X"
proof (induction xs arbitrary: ys U V, rule_tac [!] impI,
 simp add: ipurge_ref_aux_def, blast)
  fix x xs ys U V
  assume
    A: "\<And>ys U V.
      sinks_aux I D U ys \<subseteq> V \<longrightarrow>
      ipurge_ref_aux I D U ys (ipurge_ref_aux_foldr I D P V xs X) =
        ipurge_ref_aux_foldr I D P V xs X" and
    B: "sinks_aux I D U ys \<subseteq> V"
  show "ipurge_ref_aux I D U ys (ipurge_ref_aux_foldr I D P V (x # xs) X) =
    ipurge_ref_aux_foldr I D P V (x # xs) X"
  proof (cases "P x", simp_all add: ipurge_ref_aux_cons)
    have C: "sinks_aux I D V [x] \<subseteq> sinks_aux I D V [x]" ..
    show
     "ipurge_ref_aux I D U ys (ipurge_ref_aux I D (sinks_aux I D V [x])
        (ipurge_tr_aux_foldr I D P (sinks_aux I D V [x]) xs)
        (ipurge_ref_aux_foldr I D P (sinks_aux I D V [x]) xs X)) =
      ipurge_ref_aux I D (sinks_aux I D V [x])
        (ipurge_tr_aux_foldr I D P (sinks_aux I D V [x]) xs)
        (ipurge_ref_aux_foldr I D P (sinks_aux I D V [x]) xs X)"
    proof (simp add: ipurge_tr_aux_foldr_ref_aux [OF C])
      have "sinks_aux I D (sinks_aux I D V [x]) [] \<subseteq> sinks_aux I D V [x] \<longrightarrow>
        ipurge_ref_aux I D (sinks_aux I D V [x]) []
          (ipurge_ref_aux_foldr I D P (sinks_aux I D V [x]) xs X) =
        ipurge_ref_aux_foldr I D P (sinks_aux I D V [x]) xs X"
        (is "?A \<longrightarrow> ?us = ?vs")
       using A .
      moreover have ?A
       by simp
      ultimately have "?us = ?vs" ..
      thus "ipurge_ref_aux I D U ys ?us = ?us"
      proof simp
        have "sinks_aux I D U ys \<subseteq> sinks_aux I D V [x] \<longrightarrow>
          ipurge_ref_aux I D U ys
            (ipurge_ref_aux_foldr I D P (sinks_aux I D V [x]) xs X) =
          ipurge_ref_aux_foldr I D P (sinks_aux I D V [x]) xs X"
          (is "_ \<longrightarrow> ?T")
         using A .
        moreover have "V \<subseteq> sinks_aux I D V [x]"
         by (rule sinks_aux_subset)
        hence "sinks_aux I D U ys \<subseteq> sinks_aux I D V [x]"
         using B by simp
        ultimately show ?T ..
      qed
    qed
  next
    have C: "V \<subseteq> sinks_aux I D V [x]"
     by (rule sinks_aux_subset)
    show
     "ipurge_ref_aux I D U ys (ipurge_ref_aux I D V
        (ipurge_tr_aux_foldr I D P (sinks_aux I D V [x]) xs)
        (ipurge_ref_aux_foldr I D P (sinks_aux I D V [x]) xs X)) =
      ipurge_ref_aux I D V
        (ipurge_tr_aux_foldr I D P (sinks_aux I D V [x]) xs)
        (ipurge_ref_aux_foldr I D P (sinks_aux I D V [x]) xs X)"
    proof (simp add: ipurge_tr_aux_foldr_ref_aux [OF C])
      have "sinks_aux I D V [] \<subseteq> sinks_aux I D V [x] \<longrightarrow>
        ipurge_ref_aux I D V []
          (ipurge_ref_aux_foldr I D P (sinks_aux I D V [x]) xs X) =
        ipurge_ref_aux_foldr I D P (sinks_aux I D V [x]) xs X"
        (is "?A \<longrightarrow> ?us = ?vs")
       using A .
      moreover have ?A
       using C by simp
      ultimately have "?us = ?vs" ..
      thus "ipurge_ref_aux I D U ys ?us = ?us"
      proof simp
        have "sinks_aux I D U ys \<subseteq> sinks_aux I D V [x] \<longrightarrow>
          ipurge_ref_aux I D U ys
            (ipurge_ref_aux_foldr I D P (sinks_aux I D V [x]) xs X) =
          ipurge_ref_aux_foldr I D P (sinks_aux I D V [x]) xs X"
          (is "_ \<longrightarrow> ?T")
         using A .
        moreover have "sinks_aux I D U ys \<subseteq> sinks_aux I D V [x]"
         using B and C by simp
        ultimately show ?T ..
      qed
    qed
  qed
qed

lemma ipurge_ref_aux_foldr_eq:
 "ipurge_ref_aux I D U xs X = ipurge_ref_aux_foldr I D P U xs X"
proof (induction xs arbitrary: U, simp)
  fix x xs U
  assume A: "\<And>U. ipurge_ref_aux I D U xs X = ipurge_ref_aux_foldr I D P U xs X"
  show "ipurge_ref_aux I D U (x # xs) X =
    ipurge_ref_aux_foldr I D P U (x # xs) X"
  proof (cases "P x", simp_all add: ipurge_ref_aux_cons)
    have "sinks_aux I D U [x] \<subseteq> sinks_aux I D U [x]" ..
    hence
     "ipurge_ref_aux I D (sinks_aux I D U [x])
        (ipurge_tr_aux_foldr I D P (sinks_aux I D U [x]) xs)
        (ipurge_ref_aux_foldr I D P (sinks_aux I D U [x]) xs X) =
      ipurge_ref_aux I D (sinks_aux I D U [x]) []
        (ipurge_ref_aux_foldr I D P (sinks_aux I D U [x]) xs X)"
      (is "ipurge_ref_aux _ _ _ ?xs' ?X' = _")
     by (rule ipurge_tr_aux_foldr_ref_aux)
    also have "sinks_aux I D (sinks_aux I D U [x]) [] \<subseteq> sinks_aux I D U [x]"
     by simp
    hence "ipurge_ref_aux I D (sinks_aux I D U [x]) [] ?X' = ?X'"
     by (rule ipurge_ref_aux_foldr_subset)
    finally have "ipurge_ref_aux I D (sinks_aux I D U [x]) ?xs' ?X' = ?X'" .
    thus "ipurge_ref_aux I D (sinks_aux I D U [x]) xs X =
      ipurge_ref_aux I D (sinks_aux I D U [x]) ?xs' ?X'"
    proof simp
      show "ipurge_ref_aux I D (sinks_aux I D U [x]) xs X =
        ipurge_ref_aux_foldr I D P (sinks_aux I D U [x]) xs X"
       using A .
    qed
  next
    have "U \<subseteq> sinks_aux I D U [x]"
     by (rule sinks_aux_subset)
    hence
     "ipurge_ref_aux I D U
        (ipurge_tr_aux_foldr I D P (sinks_aux I D U [x]) xs)
        (ipurge_ref_aux_foldr I D P (sinks_aux I D U [x]) xs X) =
      ipurge_ref_aux I D U []
        (ipurge_ref_aux_foldr I D P (sinks_aux I D U [x]) xs X)"
      (is "ipurge_ref_aux _ _ _ ?xs' ?X' = _")
     by (rule ipurge_tr_aux_foldr_ref_aux)
    also have "sinks_aux I D U [] \<subseteq> sinks_aux I D U [x]"
     by (simp, rule sinks_aux_subset)
    hence "ipurge_ref_aux I D U [] ?X' = ?X'"
     by (rule ipurge_ref_aux_foldr_subset)
    finally have "ipurge_ref_aux I D U ?xs' ?X' = ?X'" .
    thus "ipurge_ref_aux I D (sinks_aux I D U [x]) xs X =
      ipurge_ref_aux I D U ?xs' ?X'"
    proof simp
      show "ipurge_ref_aux I D (sinks_aux I D U [x]) xs X =
        ipurge_ref_aux_foldr I D P (sinks_aux I D U [x]) xs X"
       using A .
    qed
  qed
qed

text \<open>
\null

Finally, here below is the proof of the implication involving functions @{term ipurge_tr_aux_foldr}
and @{term ipurge_ref_aux_foldr} discussed above.

\null
\<close>

lemma con_comp_sinks_aux_range:
  assumes
    A: "U \<subseteq> range Some" and
    B: "set xs \<subseteq> range p \<union> range q"
  shows "sinks_aux (con_comp_pol I) (con_comp_map D E p q) U xs \<subseteq> range Some"
    (is "sinks_aux _ ?D' _ _ \<subseteq> _")
proof (rule subsetI, drule sinks_aux_elem, erule disjE, erule_tac [2] bexE)
  fix u
  assume "u \<in> U"
  with A show "u \<in> range Some" ..
next
  fix u x
  assume "x \<in> set xs"
  with B have "x \<in> range p \<union> range q" ..
  hence "?D' x \<in> range Some"
   by (cases "x \<in> range p", simp_all)
  moreover assume "u = ?D' x"
  ultimately show "u \<in> range Some"
   by simp
qed

lemma con_comp_sinks_aux [rule_format]:
  assumes A: "U \<subseteq> range Some"
  shows "set xs \<subseteq> range p \<longrightarrow>
    sinks_aux I D (the ` U) (map (inv p) xs) =
    the ` sinks_aux (con_comp_pol I) (con_comp_map D E p q) U xs"
    (is "_ \<longrightarrow> _ = the ` sinks_aux ?I' ?D' _ _")
proof (induction xs rule: rev_induct, simp, rule impI)
  fix x xs
  assume "set xs \<subseteq> range p \<longrightarrow>
    sinks_aux I D (the ` U) (map (inv p) xs) =
    the ` sinks_aux ?I' ?D' U xs"
  moreover assume B: "set (xs @ [x]) \<subseteq> range p"
  ultimately have C: "sinks_aux I D (the ` U) (map (inv p) xs) =
    the ` sinks_aux ?I' ?D' U xs"
   by simp
  show "sinks_aux I D (the ` U) (map (inv p) (xs @ [x])) =
    the ` sinks_aux ?I' ?D' U (xs @ [x])"
  proof (cases "\<exists>u \<in> sinks_aux ?I' ?D' U xs. (u, ?D' x) \<in> ?I'",
   simp_all (no_asm_simp) del: map_append)
    case True
    then obtain u where
      D: "u \<in> sinks_aux ?I' ?D' U xs" and E: "(u, ?D' x) \<in> ?I'" ..
    have "(the u, D (inv p x)) \<in> I"
     using B and E by (simp add: con_comp_pol_def, erule_tac exE, simp)
    moreover have "the u \<in> the ` sinks_aux ?I' ?D' U xs"
     using D by simp
    hence "the u \<in> sinks_aux I D (the ` U) (map (inv p) xs)"
     using C by simp
    ultimately have "\<exists>d \<in> sinks_aux I D (the ` U) (map (inv p) xs).
      (d, D (inv p x)) \<in> I" ..
    hence "sinks_aux I D (the ` U) (map (inv p) (xs @ [x])) =
      insert (D (inv p x)) (sinks_aux I D (the ` U) (map (inv p) xs))"
     by simp
    thus "sinks_aux I D (the ` U) (map (inv p) (xs @ [x])) =
      insert (the (?D' x)) (the ` sinks_aux ?I' ?D' U xs)"
     using B and C by simp
  next
    case False
    have "\<not> (\<exists>d \<in> sinks_aux I D (the ` U) (map (inv p) xs).
      (d, D (inv p x)) \<in> I)"
    proof (rule notI, erule bexE)
      fix d
      assume "d \<in> sinks_aux I D (the ` U) (map (inv p) xs)"
      hence "d \<in> the ` sinks_aux ?I' ?D' U xs"
       using C by simp
      hence "\<exists>u \<in> sinks_aux ?I' ?D' U xs. d = the u"
       by (simp add: image_iff)
      then obtain u where
        D: "u \<in> sinks_aux ?I' ?D' U xs" and E: "d = the u" ..
      have "set xs \<subseteq> range p \<union> range q"
       using B by (simp, blast)
      with A have "sinks_aux ?I' ?D' U xs \<subseteq> range Some"
       by (rule con_comp_sinks_aux_range)
      hence "u \<in> range Some"
       using D ..
      hence "u = Some d"
       using E by (simp add: image_iff)
      moreover assume "(d, D (inv p x)) \<in> I"
      hence "(Some d, Some (D (inv p x))) \<in> ?I'"
       by (simp add: con_comp_pol_def)
      ultimately have "(u, ?D' x) \<in> ?I'"
       using B by simp
      hence "\<exists>u \<in> sinks_aux ?I' ?D' U xs. (u, ?D' x) \<in> ?I'"
       using D ..
      thus False
       using False by contradiction
    qed
    thus "sinks_aux I D (the ` U) (map (inv p) (xs @ [x])) =
      the ` sinks_aux ?I' ?D' U xs"
     using C by simp
  qed
qed

lemma con_comp_ipurge_tr_aux [rule_format]:
  assumes A: "U \<subseteq> range Some"
  shows "set xs \<subseteq> range p \<longrightarrow>
    ipurge_tr_aux I D (the ` U) (map (inv p) xs) =
    map (inv p) (ipurge_tr_aux (con_comp_pol I) (con_comp_map D E p q) U xs)"
    (is "_ \<longrightarrow> _ = map (inv p) (ipurge_tr_aux ?I' ?D' _ _)")
proof (induction xs rule: rev_induct, simp, rule impI)
  fix x xs
  assume "set xs \<subseteq> range p \<longrightarrow>
    ipurge_tr_aux I D (the ` U) (map (inv p) xs) =
    map (inv p) (ipurge_tr_aux ?I' ?D' U xs)"
  moreover assume B: "set (xs @ [x]) \<subseteq> range p"
  ultimately have C: "ipurge_tr_aux I D (the ` U) (map (inv p) xs) =
    map (inv p) (ipurge_tr_aux ?I' ?D' U xs)"
   by simp
  show "ipurge_tr_aux I D (the ` U) (map (inv p) (xs @ [x])) =
    map (inv p) (ipurge_tr_aux ?I' ?D' U (xs @ [x]))"
  proof (cases "\<exists>u \<in> sinks_aux ?I' ?D' U xs. (u, ?D' x) \<in> ?I'")
    case True
    then obtain u where
      D: "u \<in> sinks_aux ?I' ?D' U xs" and E: "(u, ?D' x) \<in> ?I'" ..
    have "(the u, D (inv p x)) \<in> I"
     using B and E by (simp add: con_comp_pol_def, erule_tac exE, simp)
    moreover have F: "the u \<in> the ` sinks_aux ?I' ?D' U xs"
     using D by simp
    have "set xs \<subseteq> range p"
     using B by simp
    with A have "sinks_aux I D (the ` U) (map (inv p) xs) =
      the ` sinks_aux ?I' ?D' U xs"
     by (rule con_comp_sinks_aux)
    hence "the u \<in> sinks_aux I D (the ` U) (map (inv p) xs)"
     using F by simp
    ultimately have "\<exists>d \<in> sinks_aux I D (the ` U) (map (inv p) xs).
      (d, D (inv p x)) \<in> I" ..
    hence "ipurge_tr_aux I D (the ` U) (map (inv p) (xs @ [x])) =
      ipurge_tr_aux I D (the ` U) (map (inv p) xs)"
     by simp
    moreover have "map (inv p) (ipurge_tr_aux ?I' ?D' U (xs @ [x])) =
      map (inv p) (ipurge_tr_aux ?I' ?D' U xs)"
     using True by simp
    ultimately show ?thesis
     using C by simp
  next
    case False
    have "\<not> (\<exists>d \<in> sinks_aux I D (the ` U) (map (inv p) xs).
      (d, D (inv p x)) \<in> I)"
    proof (rule notI, erule bexE)
      fix d
      assume "d \<in> sinks_aux I D (the ` U) (map (inv p) xs)"
      moreover have "set xs \<subseteq> range p"
       using B by simp
      with A have "sinks_aux I D (the ` U) (map (inv p) xs) =
        the ` sinks_aux ?I' ?D' U xs"
       by (rule con_comp_sinks_aux)
      ultimately have "d \<in> the ` sinks_aux ?I' ?D' U xs"
       by simp
      hence "\<exists>u \<in> sinks_aux ?I' ?D' U xs. d = the u"
       by (simp add: image_iff)
      then obtain u where
        D: "u \<in> sinks_aux ?I' ?D' U xs" and E: "d = the u" ..
      have "set xs \<subseteq> range p \<union> range q"
       using B by (simp, blast)
      with A have "sinks_aux ?I' ?D' U xs \<subseteq> range Some"
       by (rule con_comp_sinks_aux_range)
      hence "u \<in> range Some"
       using D ..
      hence "u = Some d"
       using E by (simp add: image_iff)
      moreover assume "(d, D (inv p x)) \<in> I"
      hence "(Some d, Some (D (inv p x))) \<in> ?I'"
       by (simp add: con_comp_pol_def)
      ultimately have "(u, ?D' x) \<in> ?I'"
       using B by simp
      hence "\<exists>u \<in> sinks_aux ?I' ?D' U xs. (u, ?D' x) \<in> ?I'"
       using D ..
      thus False
       using False by contradiction
    qed
    hence "ipurge_tr_aux I D (the ` U) (map (inv p) (xs @ [x])) =
      ipurge_tr_aux I D (the ` U) (map (inv p) xs) @ [inv p x]"
     by simp
    moreover have "map (inv p) (ipurge_tr_aux ?I' ?D' U (xs @ [x])) =
      map (inv p) (ipurge_tr_aux ?I' ?D' U xs) @ [inv p x]"
     using False by simp
    ultimately show ?thesis
     using C by simp
  qed
qed

lemma con_comp_ipurge_ref_aux:
  assumes
    A: "U \<subseteq> range Some" and
    B: "set xs \<subseteq> range p" and
    C: "X \<subseteq> range p"
  shows "ipurge_ref_aux I D (the ` U) (map (inv p) xs) (inv p ` X) =
    inv p ` ipurge_ref_aux (con_comp_pol I) (con_comp_map D E p q) U xs X"
  (is "_ = inv p ` ipurge_ref_aux ?I' ?D' _ _ _")
proof (simp add: ipurge_ref_aux_def set_eq_iff image_iff, rule allI, rule iffI,
 erule conjE, erule bexE, erule_tac [2] exE, (erule_tac [2] conjE)+)
  fix a x
  assume
    D: "x \<in> X" and
    E: "a = inv p x" and
    F: "\<forall>d \<in> sinks_aux I D (the ` U) (map (inv p) xs). (d, D a) \<notin> I"
  show "\<exists>x. x \<in> X \<and> (\<forall>u \<in> sinks_aux ?I' ?D' U xs. (u, ?D' x) \<notin> ?I') \<and>
    a = inv p x"
  proof (rule_tac x = x in exI, simp add: D E, rule ballI)
    fix u
    assume G: "u \<in> sinks_aux ?I' ?D' U xs"
    moreover have "sinks_aux I D (the ` U) (map (inv p) xs) =
      the ` sinks_aux ?I' ?D' U xs"
     using A and B by (rule con_comp_sinks_aux)
    ultimately have "the u \<in> sinks_aux I D (the ` U) (map (inv p) xs)"
     by simp
    with F have "(the u, D a) \<notin> I" ..
    moreover have "set xs \<subseteq> range p \<union> range q"
     using B by blast
    with A have "sinks_aux ?I' ?D' U xs \<subseteq> range Some"
     by (rule con_comp_sinks_aux_range)
    hence "u \<in> range Some"
     using G ..
    hence "\<exists>d. u = Some d"
     by (simp add: image_iff)
    then obtain d where H: "u = Some d" ..
    ultimately have "(d, D (inv p x)) \<notin> I"
     using E by simp
    hence "(u, Some (D (inv p x))) \<notin> ?I'"
     using H by (simp add: con_comp_pol_def)
    moreover have "x \<in> range p"
     using C and D ..
    ultimately show "(u, ?D' x) \<notin> ?I'"
     by simp
  qed
next
  fix a x
  assume
    D: "x \<in> X" and
    E: "a = inv p x" and
    F: "\<forall>u \<in> sinks_aux ?I' ?D' U xs. (u, ?D' x) \<notin> ?I'"
  show "(\<exists>x \<in> X. a = inv p x) \<and>
    (\<forall>u \<in> sinks_aux I D (the ` U) (map (inv p) xs). (u, D a) \<notin> I)"
  proof (rule conjI, rule_tac [2] ballI)
    show "\<exists>x \<in> X. a = inv p x"
     using E and D ..
  next
    fix d
    assume "d \<in> sinks_aux I D (the ` U) (map (inv p) xs)"
    moreover have "sinks_aux I D (the ` U) (map (inv p) xs) =
      the ` sinks_aux ?I' ?D' U xs"
     using A and B by (rule con_comp_sinks_aux)
    ultimately have "d \<in> the ` sinks_aux ?I' ?D' U xs"
     by simp
    hence "\<exists>u \<in> sinks_aux ?I' ?D' U xs. d = the u"
     by (simp add: image_iff)
    then obtain u where G: "u \<in> sinks_aux ?I' ?D' U xs" and H: "d = the u" ..
    have "(u, ?D' x) \<notin> ?I'"
     using F and G ..
    moreover have "set xs \<subseteq> range p \<union> range q"
     using B by blast
    with A have "sinks_aux ?I' ?D' U xs \<subseteq> range Some"
     by (rule con_comp_sinks_aux_range)
    hence "u \<in> range Some"
     using G ..
    hence "u = Some d"
     using H by (simp add: image_iff)
    moreover have "x \<in> range p"
     using C and D ..
    ultimately have "(d, D (inv p x)) \<notin> I"
     by (simp add: con_comp_pol_def)
    thus "(d, D a) \<notin> I"
     using E by simp
  qed
qed

lemma con_comp_sinks_filter:
 "sinks (con_comp_pol I) (con_comp_map D E p q) u
    [x\<leftarrow>xs. x \<in> range p \<union> range q] =
  sinks (con_comp_pol I) (con_comp_map D E p q) u xs \<inter> range Some"
  (is "sinks ?I' ?D' _ _ = _")
proof (induction xs rule: rev_induct, simp)
  fix x xs
  assume A: "sinks ?I' ?D' u [x\<leftarrow>xs. x \<in> range p \<union> range q] =
    sinks ?I' ?D' u xs \<inter> range Some"
    (is "sinks _ _ _ ?xs' = _")
  show "sinks ?I' ?D' u [x\<leftarrow>xs @ [x]. x \<in> range p \<union> range q] =
    sinks ?I' ?D' u (xs @ [x]) \<inter> range Some"
  proof (cases "x \<in> range p \<union> range q", simp_all del: Un_iff sinks.simps,
   cases "(u, ?D' x) \<in> ?I' \<or> (\<exists>v \<in> sinks ?I' ?D' u ?xs'. (v, ?D' x) \<in> ?I')")
    assume
      B: "x \<in> range p \<union> range q" and
      C: "(u, ?D' x) \<in> ?I' \<or> (\<exists>v \<in> sinks ?I' ?D' u ?xs'. (v, ?D' x) \<in> ?I')"
    have "sinks ?I' ?D' u (?xs' @ [x]) =
      insert (?D' x) (sinks ?I' ?D' u ?xs')"
     using C by simp
    also have "\<dots> =
      insert (?D' x) (sinks ?I' ?D' u xs \<inter> range Some)"
     using A by simp
    also have "\<dots> =
      insert (?D' x) (sinks ?I' ?D' u xs) \<inter> insert (?D' x) (range Some)"
     by simp
    finally have "sinks ?I' ?D' u (?xs' @ [x]) =
      insert (?D' x) (sinks ?I' ?D' u xs) \<inter> insert (?D' x) (range Some)" .
    moreover have "insert (?D' x) (range Some) = range Some"
     using B by (rule_tac insert_absorb, cases "x \<in> range p", simp_all)
    ultimately have "sinks ?I' ?D' u (?xs' @ [x]) =
      insert (?D' x) (sinks ?I' ?D' u xs) \<inter> range Some"
     by simp
    moreover have "(u, ?D' x) \<in> ?I' \<or>
      (\<exists>v \<in> sinks ?I' ?D' u xs. (v, ?D' x) \<in> ?I')"
     using A and C by (simp, blast)
    ultimately show "sinks ?I' ?D' u (?xs' @ [x]) =
      sinks ?I' ?D' u (xs @ [x]) \<inter> range Some"
     by simp
  next
    assume
      B: "x \<in> range p \<union> range q" and
      C: "\<not> ((u, ?D' x) \<in> ?I' \<or> (\<exists>v \<in> sinks ?I' ?D' u ?xs'. (v, ?D' x) \<in> ?I'))"
    have "sinks ?I' ?D' u (?xs' @ [x]) = sinks ?I' ?D' u ?xs'"
     using C by simp
    hence "sinks ?I' ?D' u (?xs' @ [x]) = sinks ?I' ?D' u xs \<inter> range Some"
     using A by simp
    moreover from C have
     "\<not> ((u, ?D' x) \<in> ?I' \<or> (\<exists>v \<in> sinks ?I' ?D' u xs. (v, ?D' x) \<in> ?I'))"
    proof (rule_tac notI, simp del: bex_simps)
      assume "\<exists>v \<in> sinks ?I' ?D' u xs. (v, ?D' x) \<in> ?I'"
      then obtain v where E: "v \<in> sinks ?I' ?D' u xs" and F: "(v, ?D' x) \<in> ?I'" ..
      have "\<exists>d. ?D' x = Some d"
       using B by (cases "x \<in> range p", simp_all)
      then obtain d where "?D' x = Some d" ..
      hence "(v, Some d) \<in> ?I'"
       using F by simp
      hence "v \<in> range Some"
       by (cases v, simp_all add: con_comp_pol_def)
      with E have "v \<in> sinks ?I' ?D' u xs \<inter> range Some" ..
      hence "v \<in> sinks ?I' ?D' u ?xs'"
       using A by simp
      with F have "\<exists>v \<in> sinks ?I' ?D' u ?xs'. (v, ?D' x) \<in> ?I'" ..
      thus False
       using C by simp
    qed
    ultimately show "sinks ?I' ?D' u (?xs' @ [x]) =
      sinks ?I' ?D' u (xs @ [x]) \<inter> range Some"
     by simp
  next
    assume B: "x \<notin> range p \<union> range q"
    hence "(u, ?D' x) \<in> ?I'"
     by (simp add: con_comp_pol_def)
    hence "sinks ?I' ?D' u (xs @ [x]) = insert (?D' x) (sinks ?I' ?D' u xs)"
     by simp
    moreover have "insert (?D' x) (sinks ?I' ?D' u xs) \<inter> range Some =
      sinks ?I' ?D' u xs \<inter> range Some"
     using B by simp
    ultimately have "sinks ?I' ?D' u (xs @ [x]) \<inter> range Some =
      sinks ?I' ?D' u xs \<inter> range Some"
     by simp
    thus "sinks ?I' ?D' u ?xs' = sinks ?I' ?D' u (xs @ [x]) \<inter> range Some"
     using A by simp
  qed
qed

lemma con_comp_ipurge_tr_filter:
 "ipurge_tr (con_comp_pol I) (con_comp_map D E p q) u
    [x\<leftarrow>xs. x \<in> range p \<union> range q] =
  ipurge_tr (con_comp_pol I) (con_comp_map D E p q) u xs"
  (is "ipurge_tr ?I' ?D' _ _ = _")
proof (induction xs rule: rev_induct, simp)
  fix x xs
  assume A: "ipurge_tr ?I' ?D' u [x\<leftarrow>xs. x \<in> range p \<union> range q] =
    ipurge_tr ?I' ?D' u xs"
    (is "ipurge_tr _ _ _ ?xs' = _")
  show "ipurge_tr ?I' ?D' u [x\<leftarrow>xs @ [x]. x \<in> range p \<union> range q] =
    ipurge_tr ?I' ?D' u (xs @ [x])"
  proof (cases "x \<in> range p \<union> range q", simp_all del: Un_iff ipurge_tr.simps,
   cases "?D' x \<in> sinks ?I' ?D' u (?xs' @ [x])")
    assume
      B: "x \<in> range p \<union> range q" and
      C: "?D' x \<in> sinks ?I' ?D' u (?xs' @ [x])"
    have "ipurge_tr ?I' ?D' u (?xs' @ [x]) = ipurge_tr ?I' ?D' u ?xs'"
     using C by simp
    hence "ipurge_tr ?I' ?D' u (?xs' @ [x]) = ipurge_tr ?I' ?D' u xs"
     using A by simp
    moreover have "?D' x \<in> sinks ?I' ?D' u [x\<leftarrow>xs @ [x]. x \<in> range p \<union> range q]"
     using B and C by simp
    hence "?D' x \<in> sinks ?I' ?D' u (xs @ [x])"
     by (simp only: con_comp_sinks_filter, blast)
    ultimately show "ipurge_tr ?I' ?D' u (?xs' @ [x]) =
      ipurge_tr ?I' ?D' u (xs @ [x])"
     by simp
  next
    assume
      B: "x \<in> range p \<union> range q" and
      C: "\<not> (?D' x \<in> sinks ?I' ?D' u (?xs' @ [x]))"
    have "ipurge_tr ?I' ?D' u (?xs' @ [x]) = ipurge_tr ?I' ?D' u ?xs' @ [x]"
     using C by simp
    hence "ipurge_tr ?I' ?D' u (?xs' @ [x]) = ipurge_tr ?I' ?D' u xs @ [x]"
     using A by simp
    moreover have "?D' x \<notin> sinks ?I' ?D' u [x\<leftarrow>xs @ [x]. x \<in> range p \<union> range q]"
     using B and C by simp
    hence "?D' x \<notin> sinks ?I' ?D' u (xs @ [x]) \<inter> range Some"
     by (simp only: con_comp_sinks_filter, simp)
    hence "?D' x \<notin> sinks ?I' ?D' u (xs @ [x])"
     using B by (cases "x \<in> range p", simp_all)
    ultimately show "ipurge_tr ?I' ?D' u (?xs' @ [x]) =
      ipurge_tr ?I' ?D' u (xs @ [x])"
     by simp
  next
    assume "x \<notin> range p \<union> range q"
    hence "(u, ?D' x) \<in> ?I'"
     by (simp add: con_comp_pol_def)
    hence "?D' x \<in> sinks ?I' ?D' u (xs @ [x])"
     by simp
    thus "ipurge_tr ?I' ?D' u ?xs' = ipurge_tr ?I' ?D' u (xs @ [x])"
     using A by simp
  qed
qed

lemma con_comp_ipurge_ref_filter:
 "ipurge_ref (con_comp_pol I) (con_comp_map D E p q) u
    [x\<leftarrow>xs. x \<in> range p \<union> range q] X =
  ipurge_ref (con_comp_pol I) (con_comp_map D E p q) u xs X"
  (is "ipurge_ref ?I' ?D' _ _ _ = _")
proof (simp add: ipurge_ref_def con_comp_sinks_filter set_eq_iff del: Un_iff,
 rule allI, rule iffI, simp_all, (erule conjE)+, rule ballI)
  fix x v
  assume
    A: "(u, ?D' x) \<notin> ?I'" and
    B: "\<forall>v \<in> sinks ?I' ?D' u xs \<inter> range Some. (v, ?D' x) \<notin> ?I'" and
    C: "v \<in> sinks ?I' ?D' u xs"
  show "(v, ?D' x) \<notin> ?I'"
  proof (cases v, simp)
    have "?D' x \<in> range Some"
     using A by (cases "?D' x", simp_all add: con_comp_pol_def)
    thus "(None, ?D' x) \<notin> ?I'"
     by (simp add: image_iff con_comp_pol_def)
  next
    fix d
    assume "v = Some d"
    hence "v \<in> range Some"
     by simp
    with C have "v \<in> sinks ?I' ?D' u xs \<inter> range Some" ..
    with B show "(v, ?D' x) \<notin> ?I'" ..
  qed
qed

lemma con_comp_secure_aux [rule_format]:
  assumes
    A: "secure P I D" and
    B: "Y \<subseteq> range p"
  shows "set ys \<subseteq> range p \<union> range q \<longrightarrow> U \<subseteq> range Some \<longrightarrow>
    (map (inv p) [x\<leftarrow>xs @ ys. x \<in> range p], inv p ` Y) \<in> failures P \<longrightarrow>
    (map (inv p) [x\<leftarrow>xs. x \<in> range p] @
     map (inv p) (ipurge_tr_aux_foldr (con_comp_pol I) (con_comp_map D E p q)
       (\<lambda>x. x \<in> range p) U ys),
     inv p ` ipurge_ref_aux_foldr (con_comp_pol I) (con_comp_map D E p q)
       (\<lambda>x. x \<in> range p) U ys Y) \<in> failures P"
proof (induction ys arbitrary: xs U, (rule_tac [!] impI)+, simp)
  fix xs U
  assume "(map (inv p) [x\<leftarrow>xs. x \<in> range p], inv p ` Y) \<in> failures P"
  moreover have
   "ipurge_ref_aux (con_comp_pol I) (con_comp_map D E p q) U [] Y \<subseteq> Y"
    (is "?Y' \<subseteq> _")
   by (rule ipurge_ref_aux_subset)
  hence "inv p ` ?Y' \<subseteq> inv p ` Y"
   by (rule image_mono)
  ultimately show "(map (inv p) [x\<leftarrow>xs. x \<in> range p], inv p ` ?Y') \<in> failures P"
   by (rule process_rule_3)
next
  fix y ys xs U
  assume "\<And>xs U. set ys \<subseteq> range p \<union> range q \<longrightarrow> U \<subseteq> range Some \<longrightarrow>
    (map (inv p) [x\<leftarrow>xs @ ys. x \<in> range p], inv p ` Y) \<in> failures P \<longrightarrow>
    (map (inv p) [x\<leftarrow>xs. x \<in> range p] @
     map (inv p) (ipurge_tr_aux_foldr (con_comp_pol I) (con_comp_map D E p q)
       (\<lambda>x. x \<in> range p) U ys),
     inv p ` ipurge_ref_aux_foldr (con_comp_pol I) (con_comp_map D E p q)
       (\<lambda>x. x \<in> range p) U ys Y) \<in> failures P"
  hence "set ys \<subseteq> range p \<union> range q \<longrightarrow>
    sinks_aux (con_comp_pol I) (con_comp_map D E p q) U [y] \<subseteq> range Some \<longrightarrow>
    (map (inv p) [x\<leftarrow>(xs @ [y]) @ ys. x \<in> range p], inv p ` Y) \<in> failures P \<longrightarrow>
    (map (inv p) [x\<leftarrow>xs @ [y]. x \<in> range p] @
     map (inv p) (ipurge_tr_aux_foldr (con_comp_pol I) (con_comp_map D E p q)
       (\<lambda>x. x \<in> range p) (sinks_aux (con_comp_pol I) (con_comp_map D E p q)
         U [y]) ys),
     inv p ` ipurge_ref_aux_foldr (con_comp_pol I) (con_comp_map D E p q)
       (\<lambda>x. x \<in> range p) (sinks_aux (con_comp_pol I) (con_comp_map D E p q)
         U [y]) ys Y) \<in> failures P"
    (is "_ \<longrightarrow> _ \<longrightarrow> _ \<longrightarrow>
      (_ @ map (inv p) (ipurge_tr_aux_foldr ?I' ?D' ?F ?U' _), _) \<in> _") .
  moreover assume C: "set (y # ys) \<subseteq> range p \<union> range q"
  hence "set ys \<subseteq> range p \<union> range q"
   by simp
  ultimately have "?U' \<subseteq> range Some \<longrightarrow>
    (map (inv p) [x\<leftarrow>(xs @ [y]) @ ys. x \<in> range p], inv p ` Y) \<in> failures P \<longrightarrow>
    (map (inv p) [x\<leftarrow>xs @ [y]. x \<in> range p] @
     map (inv p) (ipurge_tr_aux_foldr ?I' ?D' ?F ?U' ys),
     inv p ` ipurge_ref_aux_foldr ?I' ?D' ?F ?U' ys Y) \<in> failures P" ..
  moreover assume D: "U \<subseteq> range Some"
  hence "?U' \<subseteq> range Some"
  proof (cases "\<exists>u \<in> U. (u, ?D' y) \<in> ?I'", simp_all add: sinks_aux_single_event)
    have "y \<in> range p \<union> range q"
     using C by simp
    thus "?D' y \<in> range Some"
     by (cases "y \<in> range p", simp_all)
  qed
  ultimately have
   "(map (inv p) [x\<leftarrow>(xs @ [y]) @ ys. x \<in> range p], inv p ` Y) \<in> failures P \<longrightarrow>
    (map (inv p) [x\<leftarrow>xs @ [y]. x \<in> range p] @
     map (inv p) (ipurge_tr_aux_foldr ?I' ?D' ?F ?U' ys),
     inv p ` ipurge_ref_aux_foldr ?I' ?D' ?F ?U' ys Y) \<in> failures P" ..
  moreover assume
   "(map (inv p) [x\<leftarrow>xs @ y # ys. x \<in> range p], inv p ` Y) \<in> failures P"
  ultimately have
   "(map (inv p) [x\<leftarrow>xs @ [y]. x \<in> range p] @
     map (inv p) (ipurge_tr_aux_foldr ?I' ?D' ?F ?U' ys),
     inv p ` ipurge_ref_aux_foldr ?I' ?D' ?F ?U' ys Y) \<in> failures P"
   by simp
  hence
   "(map (inv p) [x\<leftarrow>xs. x \<in> range p] @
     map (inv p) ((if y \<in> range p then [y] else []) @
       ipurge_tr_aux_foldr ?I' ?D' ?F ?U' ys),
     inv p ` ipurge_ref_aux_foldr ?I' ?D' ?F ?U' ys Y) \<in> failures P"
   by (cases "y \<in> range p", simp_all)
  with A have
   "(map (inv p) [x\<leftarrow>xs. x \<in> range p] @
     ipurge_tr_aux I D (the ` U) (map (inv p) ((if y \<in> range p then [y] else []) @
       ipurge_tr_aux_foldr ?I' ?D' ?F ?U' ys)),
     ipurge_ref_aux I D (the ` U) (map (inv p) ((if y \<in> range p then [y] else []) @
       ipurge_tr_aux_foldr ?I' ?D' ?F ?U' ys))
     (inv p ` ipurge_ref_aux_foldr ?I' ?D' ?F ?U' ys Y)) \<in> failures P"
   by (rule ipurge_tr_ref_aux_failures_general)
  moreover have
   "ipurge_tr_aux I D (the ` U) (map (inv p) ((if y \<in> range p then [y] else []) @
      ipurge_tr_aux_foldr ?I' ?D' ?F ?U' ys)) =
    map (inv p) (ipurge_tr_aux ?I' ?D' U ((if y \<in> range p then [y] else []) @
      ipurge_tr_aux_foldr ?I' ?D' ?F ?U' ys))"
   by (rule con_comp_ipurge_tr_aux, simp_all add:
    D ipurge_tr_aux_foldr_eq [symmetric], blast)
  moreover have
   "ipurge_ref_aux I D (the ` U) (map (inv p) ((if y \<in> range p then [y] else []) @
      ipurge_tr_aux_foldr ?I' ?D' ?F ?U' ys))
      (inv p ` ipurge_ref_aux_foldr ?I' ?D' ?F ?U' ys Y) =
    inv p ` ipurge_ref_aux ?I' ?D' U ((if y \<in> range p then [y] else []) @
      ipurge_tr_aux_foldr ?I' ?D' ?F ?U' ys)
      (ipurge_ref_aux_foldr ?I' ?D' ?F ?U' ys Y)"
  proof (rule con_comp_ipurge_ref_aux, simp_all add:
   D ipurge_tr_aux_foldr_eq [symmetric] ipurge_ref_aux_foldr_eq [symmetric], blast)
    have "ipurge_ref_aux ?I' ?D' ?U' ys Y \<subseteq> Y"
     by (rule ipurge_ref_aux_subset)
    thus "ipurge_ref_aux ?I' ?D' ?U' ys Y \<subseteq> range p"
     using B by simp
  qed
  ultimately show
   "(map (inv p) [x\<leftarrow>xs. x \<in> range p] @
     map (inv p) (ipurge_tr_aux_foldr ?I' ?D' ?F U (y # ys)),
     inv p ` ipurge_ref_aux_foldr ?I' ?D' ?F U (y # ys) Y) \<in> failures P"
   by simp
qed


subsection "Conservation of noninterference security under concurrent composition"

text \<open>
Everything is now ready for proving the target security conservation theorem. It states that for any
two processes @{term P}, @{term Q} being secure with respect to the noninterference policy @{term I}
and the event-domain maps @{term D}, @{term E}, their concurrent composition @{term "P \<parallel> Q <p, q>"}
is secure with respect to the noninterference policy @{term "con_comp_pol I"} and the event-domain
map @{term "con_comp_map D E p q"}, provided that condition @{term "consistent_maps D E p q"} is
satisfied.

The only assumption, in addition to the security of the input processes, is the consistency of the
respective event-domain maps. Particularly, this assumption permits to solve the proof obligations
concerning the latter input process by just swapping @{term D} for @{term E} and @{term p} for
@{term q} in the term @{term "con_comp_map D E p q"} and then applying the corresponding lemmas
proven for the former input process.

\null
\<close>

lemma con_comp_secure_del_aux_1:
  assumes
    A: "secure P I D" and
    B: "y \<in> range p \<or> y \<in> range q" and
    C: "set ys \<subseteq> range p \<union> range q" and
    D: "Y \<subseteq> range p" and
    E: "(map (inv p) [x\<leftarrow>xs @ y # ys. x \<in> range p], inv p ` Y) \<in> failures P"
  shows
   "(map (inv p) [x\<leftarrow>xs @ ipurge_tr (con_comp_pol I) (con_comp_map D E p q)
       (con_comp_map D E p q y) ys. x \<in> range p],
     inv p ` ipurge_ref (con_comp_pol I) (con_comp_map D E p q)
       (con_comp_map D E p q y) ys Y) \<in> failures P"
    (is "(map (inv p) [x\<leftarrow>xs @ ipurge_tr ?I' ?D' _ _. _], _) \<in> _")
proof (simp add:
 ipurge_tr_aux_single_dom [symmetric] ipurge_ref_aux_single_dom [symmetric]
 ipurge_tr_aux_foldr_eq ipurge_ref_aux_foldr_eq [where P = "\<lambda>x. x \<in> range p"])
  have "(map (inv p) [x\<leftarrow>xs @ [y]. x \<in> range p] @
    map (inv p) (ipurge_tr_aux_foldr ?I' ?D' (\<lambda>x. x \<in> range p) {?D' y} ys),
    inv p ` ipurge_ref_aux_foldr ?I' ?D' (\<lambda>x. x \<in> range p) {?D' y} ys Y)
      \<in> failures P"
    (is "(_ @ map (inv p) (ipurge_tr_aux_foldr _ _ ?F _ _), _) \<in> _")
  proof (rule con_comp_secure_aux [OF A D C])
    show "{?D' y} \<subseteq> range Some"
     using B by (cases "y \<in> range p", simp_all)
  next
    show "(map (inv p) [x\<leftarrow>(xs @ [y]) @ ys. x \<in> range p], inv p ` Y) \<in> failures P"
     using E by simp
  qed
  thus "(map (inv p) [x\<leftarrow>xs. x \<in> range p] @
    map (inv p) (ipurge_tr_aux_foldr ?I' ?D' ?F {?D' y} ys),
    inv p ` ipurge_ref_aux_foldr ?I' ?D' ?F {?D' y} ys Y)
      \<in> failures P"
  proof (cases "y \<in> range p", simp_all)
    assume "(map (inv p) [x\<leftarrow>xs. x \<in> range p] @ inv p y #
      map (inv p) (ipurge_tr_aux_foldr ?I' ?D' ?F {Some (D (inv p y))} ys),
      inv p ` ipurge_ref_aux_foldr ?I' ?D' ?F {Some (D (inv p y))} ys Y)
      \<in> failures P"
    hence "(inv p y #
      map (inv p) (ipurge_tr_aux_foldr ?I' ?D' ?F {Some (D (inv p y))} ys),
      inv p ` ipurge_ref_aux_foldr ?I' ?D' ?F {Some (D (inv p y))} ys Y)
      \<in> futures P (map (inv p) [x\<leftarrow>xs. x \<in> range p])"
     by (simp add: futures_def)
    hence
     "(ipurge_tr I D (D (inv p y))
         (map (inv p) (ipurge_tr_aux_foldr ?I' ?D' ?F {Some (D (inv p y))} ys)),
       ipurge_ref I D (D (inv p y))
         (map (inv p) (ipurge_tr_aux_foldr ?I' ?D' ?F {Some (D (inv p y))} ys))
         (inv p ` ipurge_ref_aux_foldr ?I' ?D' ?F {Some (D (inv p y))} ys Y))
      \<in> futures P (map (inv p) [x\<leftarrow>xs. x \<in> range p])"
     using A by (simp add: secure_def)
    hence
     "(ipurge_tr_aux I D (the ` {Some (D (inv p y))})
         (map (inv p) (ipurge_tr_aux_foldr ?I' ?D' ?F {Some (D (inv p y))} ys)),
       ipurge_ref_aux I D (the ` {Some (D (inv p y))})
         (map (inv p) (ipurge_tr_aux_foldr ?I' ?D' ?F {Some (D (inv p y))} ys))
         (inv p ` ipurge_ref_aux_foldr ?I' ?D' ?F {Some (D (inv p y))} ys Y))
      \<in> futures P (map (inv p) [x\<leftarrow>xs. x \<in> range p])"
     by (simp add: ipurge_tr_aux_single_dom ipurge_ref_aux_single_dom)
    moreover have
     "ipurge_tr_aux I D (the ` {Some (D (inv p y))})
        (map (inv p) (ipurge_tr_aux_foldr ?I' ?D' ?F {Some (D (inv p y))} ys)) =
      map (inv p) (ipurge_tr_aux ?I' ?D' {Some (D (inv p y))}
        (ipurge_tr_aux_foldr ?I' ?D' ?F {Some (D (inv p y))} ys))"
     by (rule con_comp_ipurge_tr_aux, simp_all add:
      ipurge_tr_aux_foldr_eq [symmetric], blast)
    moreover have
     "ipurge_ref_aux I D (the ` {Some (D (inv p y))})
        (map (inv p) (ipurge_tr_aux_foldr ?I' ?D' ?F {Some (D (inv p y))} ys))
        (inv p ` ipurge_ref_aux_foldr ?I' ?D' ?F {Some (D (inv p y))} ys Y) =
      inv p ` ipurge_ref_aux ?I' ?D' {Some (D (inv p y))}
        (ipurge_tr_aux_foldr ?I' ?D' ?F {Some (D (inv p y))} ys)
        (ipurge_ref_aux_foldr ?I' ?D' ?F {Some (D (inv p y))} ys Y)"
    proof (rule con_comp_ipurge_ref_aux, simp_all add:
     ipurge_tr_aux_foldr_eq [symmetric] ipurge_ref_aux_foldr_eq [symmetric], blast)
      have "ipurge_ref_aux ?I' ?D' {Some (D (inv p y))} ys Y \<subseteq> Y"
       by (rule ipurge_ref_aux_subset)
      thus "ipurge_ref_aux ?I' ?D' {Some (D (inv p y))} ys Y \<subseteq> range p"
       using D by simp
    qed
    ultimately have
     "(map (inv p) (ipurge_tr_aux ?I' ?D' {Some (D (inv p y))}
         (ipurge_tr_aux_foldr ?I' ?D' ?F {Some (D (inv p y))} ys)),
       inv p ` ipurge_ref_aux ?I' ?D' {Some (D (inv p y))}
         (ipurge_tr_aux_foldr ?I' ?D' ?F {Some (D (inv p y))} ys)
         (ipurge_ref_aux_foldr ?I' ?D' ?F {Some (D (inv p y))} ys Y))
      \<in> futures P (map (inv p) [x\<leftarrow>xs. x \<in> range p])"
     by simp
    moreover have
     "ipurge_tr_aux ?I' ?D' {Some (D (inv p y))}
        (ipurge_tr_aux_foldr ?I' ?D' ?F {Some (D (inv p y))} ys) =
      ipurge_tr_aux_foldr ?I' ?D' ?F {Some (D (inv p y))} ys"
     by (rule ipurge_tr_aux_foldr_subset, simp)
    moreover have
     "ipurge_ref_aux ?I' ?D' {Some (D (inv p y))}
        (ipurge_tr_aux_foldr ?I' ?D' ?F {Some (D (inv p y))} ys)
        (ipurge_ref_aux_foldr ?I' ?D' ?F {Some (D (inv p y))} ys Y) =
      ipurge_ref_aux_foldr ?I' ?D' ?F {Some (D (inv p y))} ys Y"
     by (rule ipurge_ref_aux_foldr_subset, subst ipurge_tr_aux_foldr_sinks_aux, simp)
    ultimately have
     "(map (inv p) (ipurge_tr_aux_foldr ?I' ?D' ?F {Some (D (inv p y))} ys),
       inv p ` ipurge_ref_aux_foldr ?I' ?D' ?F {Some (D (inv p y))} ys Y)
      \<in> futures P (map (inv p) [x\<leftarrow>xs. x \<in> range p])"
     by simp
    thus "(map (inv p) [x\<leftarrow>xs. x \<in> range p] @
      map (inv p) (ipurge_tr_aux_foldr ?I' ?D' ?F {Some (D (inv p y))} ys),
      inv p ` ipurge_ref_aux_foldr ?I' ?D' ?F {Some (D (inv p y))} ys Y)
      \<in> failures P"
     by (simp add: futures_def)
  qed
qed

lemma con_comp_secure_add_aux_1:
  assumes
    A: "secure P I D" and
    B: "y \<in> range p \<or> y \<in> range q" and
    C: "set zs \<subseteq> range p \<union> range q" and
    D: "Z \<subseteq> range p" and
    E: "(map (inv p) [x\<leftarrow>xs @ zs. x \<in> range p], inv p ` Z) \<in> failures P" and
    F: "map (inv p) [x\<leftarrow>xs @ [y]. x \<in> range p] \<in> traces P"
  shows
   "(map (inv p) [x\<leftarrow>xs @ y # ipurge_tr (con_comp_pol I) (con_comp_map D E p q)
       (con_comp_map D E p q y) zs. x \<in> range p],
     inv p ` ipurge_ref (con_comp_pol I) (con_comp_map D E p q)
       (con_comp_map D E p q y) zs Z) \<in> failures P"
    (is "(map (inv p) [x\<leftarrow>xs @ y # ipurge_tr ?I' ?D' _ _. _], _) \<in> _")
proof -
  have
   "(map (inv p) [x\<leftarrow>(xs @ [y]) @ ipurge_tr ?I' ?D' (?D' y) zs. x \<in> range p],
     inv p ` ipurge_ref ?I' ?D' (?D' y) zs Z) \<in> failures P"
  proof (subst filter_append, simp del: filter_append add:
   ipurge_tr_aux_single_dom [symmetric] ipurge_ref_aux_single_dom [symmetric]
   ipurge_tr_aux_foldr_eq ipurge_ref_aux_foldr_eq [where P = "\<lambda>x. x \<in> range p"])
    have "(map (inv p) [x\<leftarrow>xs. x \<in> range p] @
      map (inv p) (ipurge_tr_aux_foldr ?I' ?D' (\<lambda>x. x \<in> range p) {?D' y} zs),
      inv p ` ipurge_ref_aux_foldr ?I' ?D' (\<lambda>x. x \<in> range p) {?D' y} zs Z)
        \<in> failures P"
      (is "(_ @ map (inv p) (ipurge_tr_aux_foldr _ _ ?F _ _), _) \<in> _")
    proof (rule con_comp_secure_aux [OF A D C])
      show "{?D' y} \<subseteq> range Some"
       using B by (cases "y \<in> range p", simp_all)
    next
      show "(map (inv p) [x\<leftarrow>xs @ zs. x \<in> range p], inv p ` Z) \<in> failures P"
       using E .
    qed
    thus "(map (inv p) [x\<leftarrow>xs @ [y]. x \<in> range p] @
      map (inv p) (ipurge_tr_aux_foldr ?I' ?D' ?F {?D' y} zs),
      inv p ` ipurge_ref_aux_foldr ?I' ?D' ?F {?D' y} zs Z)
        \<in> failures P"
    proof (cases "y \<in> range p", simp_all)
      case True
      assume "(map (inv p) [x\<leftarrow>xs. x \<in> range p] @
        map (inv p) (ipurge_tr_aux_foldr ?I' ?D' ?F {Some (D (inv p y))} zs),
        inv p ` ipurge_ref_aux_foldr ?I' ?D' ?F {Some (D (inv p y))} zs Z)
        \<in> failures P"
      hence
       "(map (inv p) (ipurge_tr_aux_foldr ?I' ?D' ?F {Some (D (inv p y))} zs),
         inv p ` ipurge_ref_aux_foldr ?I' ?D' ?F {Some (D (inv p y))} zs Z)
        \<in> futures P (map (inv p) [x\<leftarrow>xs. x \<in> range p])"
       by (simp add: futures_def)
      moreover have "(map (inv p) [x\<leftarrow>xs @ [y]. x \<in> range p], {}) \<in> failures P"
       using F by (rule traces_failures)
      hence "([inv p y], {}) \<in> futures P (map (inv p) [x\<leftarrow>xs. x \<in> range p])"
       using True by (simp add: futures_def)
      ultimately have
       "(inv p y # ipurge_tr I D (D (inv p y))
           (map (inv p) (ipurge_tr_aux_foldr ?I' ?D' ?F {Some (D (inv p y))} zs)),
         ipurge_ref I D (D (inv p y))
           (map (inv p) (ipurge_tr_aux_foldr ?I' ?D' ?F {Some (D (inv p y))} zs))
           (inv p ` ipurge_ref_aux_foldr ?I' ?D' ?F {Some (D (inv p y))} zs Z))
        \<in> futures P (map (inv p) [x\<leftarrow>xs. x \<in> range p])"
       using A by (simp add: secure_def)
      hence
       "(inv p y # ipurge_tr_aux I D (the ` {Some (D (inv p y))})
           (map (inv p) (ipurge_tr_aux_foldr ?I' ?D' ?F {Some (D (inv p y))} zs)),
         ipurge_ref_aux I D (the ` {Some (D (inv p y))})
           (map (inv p) (ipurge_tr_aux_foldr ?I' ?D' ?F {Some (D (inv p y))} zs))
           (inv p ` ipurge_ref_aux_foldr ?I' ?D' ?F {Some (D (inv p y))} zs Z))
        \<in> futures P (map (inv p) [x\<leftarrow>xs. x \<in> range p])"
       by (simp add: ipurge_tr_aux_single_dom ipurge_ref_aux_single_dom)
      moreover have
       "ipurge_tr_aux I D (the ` {Some (D (inv p y))})
          (map (inv p) (ipurge_tr_aux_foldr ?I' ?D' ?F {Some (D (inv p y))} zs)) =
        map (inv p) (ipurge_tr_aux ?I' ?D' {Some (D (inv p y))}
          (ipurge_tr_aux_foldr ?I' ?D' ?F {Some (D (inv p y))} zs))"
       by (rule con_comp_ipurge_tr_aux, simp_all add:
        ipurge_tr_aux_foldr_eq [symmetric], blast)
      moreover have
       "ipurge_ref_aux I D (the ` {Some (D (inv p y))})
          (map (inv p) (ipurge_tr_aux_foldr ?I' ?D' ?F {Some (D (inv p y))} zs))
          (inv p ` ipurge_ref_aux_foldr ?I' ?D' ?F {Some (D (inv p y))} zs Z) =
        inv p ` ipurge_ref_aux ?I' ?D' {Some (D (inv p y))}
          (ipurge_tr_aux_foldr ?I' ?D' ?F {Some (D (inv p y))} zs)
          (ipurge_ref_aux_foldr ?I' ?D' ?F {Some (D (inv p y))} zs Z)"
      proof (rule con_comp_ipurge_ref_aux, simp_all add:
       ipurge_tr_aux_foldr_eq [symmetric] ipurge_ref_aux_foldr_eq [symmetric], blast)
        have "ipurge_ref_aux ?I' ?D' {Some (D (inv p y))} zs Z \<subseteq> Z"
         by (rule ipurge_ref_aux_subset)
        thus "ipurge_ref_aux ?I' ?D' {Some (D (inv p y))} zs Z \<subseteq> range p"
         using D by simp
      qed
      ultimately have
       "(inv p y # map (inv p) (ipurge_tr_aux ?I' ?D' {Some (D (inv p y))}
           (ipurge_tr_aux_foldr ?I' ?D' ?F {Some (D (inv p y))} zs)),
         inv p ` ipurge_ref_aux ?I' ?D' {Some (D (inv p y))}
           (ipurge_tr_aux_foldr ?I' ?D' ?F {Some (D (inv p y))} zs)
           (ipurge_ref_aux_foldr ?I' ?D' ?F {Some (D (inv p y))} zs Z))
        \<in> futures P (map (inv p) [x\<leftarrow>xs. x \<in> range p])"
       by simp
      moreover have
       "ipurge_tr_aux ?I' ?D' {Some (D (inv p y))}
          (ipurge_tr_aux_foldr ?I' ?D' ?F {Some (D (inv p y))} zs) =
        ipurge_tr_aux_foldr ?I' ?D' ?F {Some (D (inv p y))} zs"
       by (rule ipurge_tr_aux_foldr_subset, simp)
      moreover have
       "ipurge_ref_aux ?I' ?D' {Some (D (inv p y))}
          (ipurge_tr_aux_foldr ?I' ?D' ?F {Some (D (inv p y))} zs)
          (ipurge_ref_aux_foldr ?I' ?D' ?F {Some (D (inv p y))} zs Z) =
        ipurge_ref_aux_foldr ?I' ?D' ?F {Some (D (inv p y))} zs Z"
       by (rule ipurge_ref_aux_foldr_subset, subst ipurge_tr_aux_foldr_sinks_aux, simp)
      ultimately have
       "(inv p y # map (inv p) (ipurge_tr_aux_foldr ?I' ?D' ?F
           {Some (D (inv p y))} zs),
         inv p ` ipurge_ref_aux_foldr ?I' ?D' ?F
           {Some (D (inv p y))} zs Z)
        \<in> futures P (map (inv p) [x\<leftarrow>xs. x \<in> range p])"
       by simp
      thus "(map (inv p) [x\<leftarrow>xs. x \<in> range p] @ inv p y #
        map (inv p) (ipurge_tr_aux_foldr ?I' ?D' ?F {Some (D (inv p y))} zs),
        inv p ` ipurge_ref_aux_foldr ?I' ?D' ?F {Some (D (inv p y))} zs Z)
        \<in> failures P"
       by (simp add: futures_def)
    qed
  qed
  thus ?thesis
   by simp
qed

lemma con_comp_consistent_maps:
 "consistent_maps D E p q \<Longrightarrow> con_comp_map D E p q = con_comp_map E D q p"
proof (simp add: consistent_maps_def, rule ext)
  fix x
  assume A: "\<forall>x \<in> range p \<inter> range q. D (inv p x) = E (inv q x)"
  show "con_comp_map D E p q x = con_comp_map E D q p x"
  proof (rule con_comp_map.cases [of "(D, E, p, q, x)"], simp_all, (erule conjE)+)
    fix p' q' D' E' x'
    assume
      B: "p = p'" and
      C: "q = q'" and
      D: "D = D'" and
      E: "E = E'" and
      F: "x' \<in> range p'"
    show "Some (D' (inv p' x')) = con_comp_map E' D' q' p' x'"
    proof (cases "x' \<in> range q'", simp_all add: F)
      case True
      with F have "x' \<in> range p' \<inter> range q'" ..
      hence "x' \<in> range p \<inter> range q"
       using B and C by simp
      with A have "D (inv p x') = E (inv q x')" ..
      thus "D' (inv p' x') = E' (inv q' x')"
       using B and C and D and E by simp
    qed
  qed
qed

lemma con_comp_secure_del_aux_2:
  assumes A: "consistent_maps D E p q"
  shows
   "secure Q I E \<Longrightarrow>
    y \<in> range p \<or> y \<in> range q \<Longrightarrow>
    set ys \<subseteq> range p \<union> range q \<Longrightarrow>
    Y \<subseteq> range q \<Longrightarrow>
    (map (inv q) [x\<leftarrow>xs @ y # ys. x \<in> range q], inv q ` Y) \<in> failures Q \<Longrightarrow>
      (map (inv q) [x\<leftarrow>xs @ ipurge_tr (con_comp_pol I) (con_comp_map D E p q)
         (con_comp_map D E p q y) ys. x \<in> range q],
       inv q ` ipurge_ref (con_comp_pol I) (con_comp_map D E p q)
         (con_comp_map D E p q y) ys Y) \<in> failures Q"
proof (simp only: con_comp_consistent_maps [OF A], rule con_comp_secure_del_aux_1)
qed (simp_all, blast+)

lemma con_comp_secure_add_aux_2:
  assumes A: "consistent_maps D E p q"
  shows
   "secure Q I E \<Longrightarrow>
    y \<in> range p \<or> y \<in> range q \<Longrightarrow>
    set zs \<subseteq> range p \<union> range q \<Longrightarrow>
    Z \<subseteq> range q \<Longrightarrow>
    (map (inv q) [x\<leftarrow>xs @ zs. x \<in> range q], inv q ` Z) \<in> failures Q \<Longrightarrow>
    map (inv q) [x\<leftarrow>xs @ [y]. x \<in> range q] \<in> traces Q \<Longrightarrow>
      (map (inv q) [x\<leftarrow>xs @ y # ipurge_tr (con_comp_pol I)
         (con_comp_map D E p q) (con_comp_map D E p q y) zs. x \<in> range q],
       inv q ` ipurge_ref (con_comp_pol I)
         (con_comp_map D E p q) (con_comp_map D E p q y) zs Z) \<in> failures Q"
proof (simp only: con_comp_consistent_maps [OF A], rule con_comp_secure_add_aux_1)
qed (simp_all, blast+)

lemma con_comp_secure_del_case_1:
  assumes
    A: "consistent_maps D E p q" and
    B: "secure P I D" and
    C: "secure Q I E"
  shows
   "\<exists>R S T.
      Y = R \<union> S \<union> T \<and>
      (y \<in> range p \<or> y \<in> range q) \<and>
      set xs \<subseteq> range p \<union> range q \<and>
      set ys \<subseteq> range p \<union> range q \<and>
      R \<subseteq> range p \<and>
      S \<subseteq> range q \<and>
      T \<subseteq> - range p \<and>
      T \<subseteq> - range q \<and>
      (map (inv p) [x\<leftarrow>xs @ y # ys. x \<in> range p], inv p ` R) \<in> failures P \<and>
      (map (inv q) [x\<leftarrow>xs @ y # ys. x \<in> range q], inv q ` S) \<in> failures Q \<Longrightarrow>
    \<exists>R S T.
      ipurge_ref (con_comp_pol I) (con_comp_map D E p q)
        (con_comp_map D E p q y) ys Y = R \<union> S \<union> T \<and>
      set xs \<subseteq> range p \<union> range q \<and>                     
      set (ipurge_tr (con_comp_pol I) (con_comp_map D E p q)
        (con_comp_map D E p q y) ys) \<subseteq> range p \<union> range q \<and>
      R \<subseteq> range p \<and>
      S \<subseteq> range q \<and>
      T \<subseteq> - range p \<and>
      T \<subseteq> - range q \<and>
      (map (inv p) [x\<leftarrow>xs @ ipurge_tr (con_comp_pol I) (con_comp_map D E p q)
        (con_comp_map D E p q y) ys. x \<in> range p], inv p ` R) \<in> failures P \<and>
      (map (inv q) [x\<leftarrow>xs @ ipurge_tr (con_comp_pol I) (con_comp_map D E p q)
        (con_comp_map D E p q y) ys. x \<in> range q], inv q ` S) \<in> failures Q"
  (is "_ \<Longrightarrow> \<exists>_ _ _. ipurge_ref ?I' ?D' _ _ _ = _ \<and> _")
proof ((erule exE)+, (erule conjE)+)
  fix R S T
  assume
    D: "Y = R \<union> S \<union> T" and
    E: "y \<in> range p \<or> y \<in> range q" and
    F: "set xs \<subseteq> range p \<union> range q" and
    G: "set ys \<subseteq> range p \<union> range q" and
    H: "R \<subseteq> range p" and
    I: "S \<subseteq> range q" and
    J: "T \<subseteq> - range p" and
    K: "T \<subseteq> - range q" and
    L: "(map (inv p) [x\<leftarrow>xs @ y # ys. x \<in> range p], inv p ` R) \<in> failures P" and
    M: "(map (inv q) [x\<leftarrow>xs @ y # ys. x \<in> range q], inv q ` S) \<in> failures Q"
  show ?thesis
  proof (rule_tac x = "ipurge_ref ?I' ?D' (?D' y) ys R" in exI,
   rule_tac x = "ipurge_ref ?I' ?D' (?D' y) ys S" in exI, rule_tac x = "{}" in exI,
   (subst conj_assoc [symmetric])+, (rule conjI)+, simp_all del: filter_append)
    have "ipurge_ref ?I' ?D' (?D' y) ys Y =
      ipurge_ref ?I' ?D' (?D' y) ys (R \<union> S \<union> T)"
     using D by simp
    hence "ipurge_ref ?I' ?D' (?D' y) ys Y =
      ipurge_ref ?I' ?D' (?D' y) ys R \<union>
      ipurge_ref ?I' ?D' (?D' y) ys S \<union>
      ipurge_ref ?I' ?D' (?D' y) ys T"
     by (simp add: ipurge_ref_distrib_union)
    moreover have "ipurge_ref ?I' ?D' (?D' y) ys T = {}"
    proof (rule ipurge_ref_empty [of "?D' y"], simp, insert E,
     cases "y \<in> range p", simp_all)
      fix x
      assume N: "x \<in> T"
      with J have "x \<in> - range p" ..
      moreover have "x \<in> - range q"
       using K and N ..
      ultimately have "?D' x = None"
       by simp
      thus "(Some (D (inv p y)), ?D' x) \<in> ?I'"
       by (simp add: con_comp_pol_def)
    next
      fix x
      assume N: "x \<in> T"
      with J have "x \<in> - range p" ..
      moreover have "x \<in> - range q"
       using K and N ..
      ultimately have "?D' x = None"
       by simp
      thus "(Some (E (inv q y)), ?D' x) \<in> ?I'"
       by (simp add: con_comp_pol_def)
    qed
    ultimately show "ipurge_ref ?I' ?D' (?D' y) ys Y =
      ipurge_ref ?I' ?D' (?D' y) ys R \<union>
      ipurge_ref ?I' ?D' (?D' y) ys S"
     by simp
  next
    show "set xs \<subseteq> range p \<union> range q"
     using F .
  next
    have "set (ipurge_tr ?I' ?D' (?D' y) ys) \<subseteq> set ys"
     by (rule ipurge_tr_set)
    thus "set (ipurge_tr ?I' ?D' (?D' y) ys) \<subseteq> range p \<union> range q"
     using G by simp
  next
    have "ipurge_ref ?I' ?D' (?D' y) ys R \<subseteq> R"
     by (rule ipurge_ref_subset)
    thus "ipurge_ref ?I' ?D' (?D' y) ys R \<subseteq> range p"
     using H by simp
  next
    have "ipurge_ref ?I' ?D' (?D' y) ys S \<subseteq> S"
     by (rule ipurge_ref_subset)
    thus "ipurge_ref ?I' ?D' (?D' y) ys S \<subseteq> range q"
     using I by simp
  next
    show "(map (inv p) [x\<leftarrow>xs @ ipurge_tr ?I' ?D' (?D' y) ys. x \<in> range p],
      inv p ` ipurge_ref ?I' ?D' (?D' y) ys R) \<in> failures P"
     by (rule con_comp_secure_del_aux_1 [OF B E G H L])
  next
    show "(map (inv q) [x\<leftarrow>xs @ ipurge_tr ?I' ?D' (?D' y) ys. x \<in> range q],
      inv q ` ipurge_ref ?I' ?D' (?D' y) ys S) \<in> failures Q"
     by (rule con_comp_secure_del_aux_2 [OF A C E G I M])
  qed
qed

lemma con_comp_secure_del_case_2:
  assumes
    A: "consistent_maps D E p q" and
    B: "secure P I D" and
    C: "secure Q I E"
  shows
   "\<exists>xs'.
      (\<exists>ys'. xs @ y # ys = xs' @ ys') \<and>
      set xs' \<subseteq> range p \<union> range q \<and>
      map (inv p) [x\<leftarrow>xs'. x \<in> range p] \<in> divergences P \<and>
      map (inv q) [x\<leftarrow>xs'. x \<in> range q] \<in> divergences Q \<Longrightarrow>
    (\<exists>R S T.
      ipurge_ref (con_comp_pol I) (con_comp_map D E p q)
        (con_comp_map D E p q y) ys Y = R \<union> S \<union> T \<and>
      set xs \<subseteq> range p \<union> range q \<and>
      set (ipurge_tr (con_comp_pol I) (con_comp_map D E p q)
        (con_comp_map D E p q y) ys) \<subseteq> range p \<union> range q \<and>
      R \<subseteq> range p \<and>
      S \<subseteq> range q \<and>
      T \<subseteq> - range p \<and>
      T \<subseteq> - range q \<and>
      (map (inv p) [x\<leftarrow>xs @ ipurge_tr (con_comp_pol I) (con_comp_map D E p q)
        (con_comp_map D E p q y) ys. x \<in> range p], inv p ` R) \<in> failures P \<and>
      (map (inv q) [x\<leftarrow>xs @ ipurge_tr (con_comp_pol I) (con_comp_map D E p q)
        (con_comp_map D E p q y) ys. x \<in> range q], inv q ` S) \<in> failures Q) \<or>
    (\<exists>xs'.
      (\<exists>ys'. xs @ ipurge_tr (con_comp_pol I) (con_comp_map D E p q)
        (con_comp_map D E p q y) ys = xs' @ ys') \<and>
      set xs' \<subseteq> range p \<union> range q \<and>
      map (inv p) [x\<leftarrow>xs'. x \<in> range p] \<in> divergences P \<and>
      map (inv q) [x\<leftarrow>xs'. x \<in> range q] \<in> divergences Q)"
  (is "_ \<Longrightarrow> (\<exists>R S T. ?F R S T ys) \<or> ?G")
proof (erule exE, (erule conjE)+, erule exE)
  fix xs' ys'
  assume
    D: "set xs' \<subseteq> range p \<union> range q" and
    E: "map (inv p) [x\<leftarrow>xs'. x \<in> range p] \<in> divergences P" and
    F: "map (inv q) [x\<leftarrow>xs'. x \<in> range q] \<in> divergences Q" and
    G: "xs @ y # ys = xs' @ ys'"
  show ?thesis
  proof (cases "length xs < length xs'", rule disjI1, rule_tac [2] disjI2)
    case True
    moreover have "take (length xs') (xs @ [y] @ ys) =
      take (length xs') (xs @ [y]) @ take (length xs' - Suc (length xs)) ys"
     by (simp only: take_append, simp)
    ultimately have "take (length xs') (xs @ [y] @ ys) =
      xs @ y # take (length xs' - Suc (length xs)) ys"
      (is "_ = _ @ _ # ?vs")
     by simp
    moreover have "take (length xs') (xs @ [y] @ ys) =
      take (length xs') (xs' @ ys')"
     using G by simp
    ultimately have H: "xs @ y # ?vs = xs'"
     by simp
    moreover have "y \<in> set (xs @ y # ?vs)"
     by simp
    ultimately have "y \<in> set xs'"
     by simp
    with D have I: "y \<in> range p \<union> range q" ..
    have "set xs \<subseteq> set (xs @ y # ?vs)"
     by auto
    hence "set xs \<subseteq> set xs'"
     using H by simp
    hence J: "set xs \<subseteq> range p \<union> range q"
     using D by simp
    have "\<exists>R S T. ?F R S T [x\<leftarrow>ys. x \<in> range p \<union> range q]"
      (is "\<exists>_ _ _. ipurge_ref ?I' ?D' _ _ _ = _ \<and> _")
    proof (rule con_comp_secure_del_case_1 [OF A B C],
     rule_tac x = "range p \<inter> Y" in exI, rule_tac x = "range q \<inter> Y" in exI,
     rule_tac x = "- range p \<inter> - range q \<inter> Y" in exI,
     (subst conj_assoc [symmetric])+, (rule conjI)+, simp_all del: filter_append)
      show "Y = range p \<inter> Y \<union> range q \<inter> Y \<union> - range p \<inter> - range q \<inter> Y"
       by blast
    next
      show "y \<in> range p \<or> y \<in> range q"
       using I by simp
    next
      show "set xs \<subseteq> range p \<union> range q"
       using J .
    next
      show "{x \<in> set ys. x \<in> range p \<or> x \<in> range q} \<subseteq> range p \<union> range q"
       by blast
    next
      show "- range p \<inter> - range q \<inter> Y \<subseteq> - range p"
       by blast
    next
      show "- range p \<inter> - range q \<inter> Y \<subseteq> - range q"
       by blast
    next
      have "map (inv p) [x\<leftarrow>xs @ y # ?vs. x \<in> range p] \<in> divergences P"
       using E and H by simp
      hence "map (inv p) [x\<leftarrow>xs @ y # ?vs. x \<in> range p] @
        map (inv p) [x\<leftarrow>drop (length xs' - Suc (length xs)) ys. x \<in> range p]
        \<in> divergences P"
        (is "_ @ map (inv p) [x\<leftarrow>?ws. _] \<in> _")
       by (rule process_rule_5_general)
      hence "map (inv p) [x\<leftarrow>(xs @ y # ?vs) @ ?ws. x \<in> range p] \<in> divergences P"
       by (subst filter_append, simp)
      hence "map (inv p) [x\<leftarrow>(xs @ [y]) @ ys. x \<in> range p] \<in> divergences P"
       by simp
      hence "map (inv p) [x\<leftarrow>(xs @ [y]) @ [x\<leftarrow>ys. x \<in> range p \<or> x \<in> range q].
        x \<in> range p] \<in> divergences P"
      proof (subst (asm) filter_append, subst filter_append, subst filter_filter)
      qed (subgoal_tac "(\<lambda>x. (x \<in> range p \<or> x \<in> range q) \<and> x \<in> range p) =
       (\<lambda>x. x \<in> range p)", simp, blast)
      hence "map (inv p) [x\<leftarrow>xs @ y # [x\<leftarrow>ys. x \<in> range p \<or> x \<in> range q].
        x \<in> range p] \<in> divergences P"
       by simp
      thus "(map (inv p) [x\<leftarrow>xs @ y # [x\<leftarrow>ys. x \<in> range p \<or> x \<in> range q].
        x \<in> range p], inv p ` (range p \<inter> Y)) \<in> failures P"
       by (rule process_rule_6)
    next
      have "map (inv q) [x\<leftarrow>xs @ y # ?vs. x \<in> range q] \<in> divergences Q"
       using F and H by simp
      hence "map (inv q) [x\<leftarrow>xs @ y # ?vs. x \<in> range q] @
        map (inv q) [x\<leftarrow>drop (length xs' - Suc (length xs)) ys. x \<in> range q]
        \<in> divergences Q"
        (is "_ @ map (inv q) [x\<leftarrow>?ws. _] \<in> _")
       by (rule process_rule_5_general)
      hence "map (inv q) [x\<leftarrow>(xs @ y # ?vs) @ ?ws. x \<in> range q] \<in> divergences Q"
       by (subst filter_append, simp)
      hence "map (inv q) [x\<leftarrow>(xs @ [y]) @ ys. x \<in> range q] \<in> divergences Q"
       by simp
      hence "map (inv q) [x\<leftarrow>(xs @ [y]) @ [x\<leftarrow>ys. x \<in> range p \<or> x \<in> range q].
        x \<in> range q] \<in> divergences Q"
      proof (subst (asm) filter_append, subst filter_append, subst filter_filter)
      qed (subgoal_tac "(\<lambda>x. (x \<in> range p \<or> x \<in> range q) \<and> x \<in> range q) =
       (\<lambda>x. x \<in> range q)", simp, blast)
      hence "map (inv q) [x\<leftarrow>xs @ y # [x\<leftarrow>ys. x \<in> range p \<or> x \<in> range q].
        x \<in> range q] \<in> divergences Q"
       by simp
      thus "(map (inv q) [x\<leftarrow>xs @ y # [x\<leftarrow>ys. x \<in> range p \<or> x \<in> range q].
        x \<in> range q], inv q ` (range q \<inter> Y)) \<in> failures Q"
       by (rule process_rule_6)
    qed
    then obtain R and S and T where
     "?F R S T [x\<leftarrow>ys. x \<in> range p \<union> range q]"
     by blast
    thus "\<exists>R S T. ?F R S T ys"
    proof (rule_tac x = R in exI, rule_tac x = S in exI, rule_tac x = T in exI)
    qed (simp only: con_comp_ipurge_tr_filter con_comp_ipurge_ref_filter)
  next
    let
      ?I' = "con_comp_pol I" and
      ?D' = "con_comp_map D E p q"
    case False
    moreover have "xs @ ipurge_tr ?I' ?D' (?D' y) ys =
      take (length xs') (xs @ ipurge_tr ?I' ?D' (?D' y) ys) @
      drop (length xs') (xs @ ipurge_tr ?I' ?D' (?D' y) ys)"
      (is "_ = _ @ ?vs")
     by (simp only: append_take_drop_id)
    ultimately have "xs @ ipurge_tr ?I' ?D' (?D' y) ys =
      take (length xs') (xs @ y # ys) @ ?vs"
     by simp
    hence H: "xs @ ipurge_tr ?I' ?D' (?D' y) ys = xs' @ ?vs"
     using G by simp
    show ?G
    proof (rule_tac x = xs' in exI, rule conjI, rule_tac x = ?vs in exI)
    qed (subst H, simp_all add: D E F)
  qed
qed

lemma con_comp_secure_add_case_1:
  assumes
    A: "consistent_maps D E p q" and
    B: "secure P I D" and
    C: "secure Q I E" and
    D: "(xs @ y # ys, Y) \<in> con_comp_failures P Q p q" and
    E: "y \<in> range p \<or> y \<in> range q"
  shows
   "\<exists>R S T.
      Z = R \<union> S \<union> T \<and>
      set xs \<subseteq> range p \<union> range q \<and>
      set zs \<subseteq> range p \<union> range q \<and>
      R \<subseteq> range p \<and>
      S \<subseteq> range q \<and>
      T \<subseteq> - range p \<and>
      T \<subseteq> - range q \<and>
      (map (inv p) [x\<leftarrow>xs @ zs. x \<in> range p], inv p ` R) \<in> failures P \<and>
      (map (inv q) [x\<leftarrow>xs @ zs. x \<in> range q], inv q ` S) \<in> failures Q \<Longrightarrow>
    \<exists>R S T.
      ipurge_ref (con_comp_pol I) (con_comp_map D E p q)
        (con_comp_map D E p q y) zs Z = R \<union> S \<union> T \<and>
      set xs \<subseteq> range p \<union> range q \<and>
      set (ipurge_tr (con_comp_pol I) (con_comp_map D E p q)
        (con_comp_map D E p q y) zs) \<subseteq> range p \<union> range q \<and>
      R \<subseteq> range p \<and>
      S \<subseteq> range q \<and>
      T \<subseteq> - range p \<and>
      T \<subseteq> - range q \<and>
      (map (inv p) [x\<leftarrow>xs @ y # ipurge_tr (con_comp_pol I)
         (con_comp_map D E p q) (con_comp_map D E p q y) zs. x \<in> range p],
       inv p ` R) \<in> failures P \<and>
      (map (inv q) [x\<leftarrow>xs @ y # ipurge_tr (con_comp_pol I)
         (con_comp_map D E p q) (con_comp_map D E p q y) zs. x \<in> range q],
       inv q ` S) \<in> failures Q"
  (is "_ \<Longrightarrow> \<exists>_ _ _. ipurge_ref ?I' ?D' _ _ _ = _ \<and> _")
proof ((erule exE)+, (erule conjE)+)
  fix R S T
  assume
    F: "Z = R \<union> S \<union> T" and
    G: "set xs \<subseteq> range p \<union> range q" and
    H: "set zs \<subseteq> range p \<union> range q" and
    I: "R \<subseteq> range p" and
    J: "S \<subseteq> range q" and
    K: "T \<subseteq> - range p" and
    L: "T \<subseteq> - range q" and
    M: "(map (inv p) [x\<leftarrow>xs @ zs. x \<in> range p], inv p ` R) \<in> failures P" and
    N: "(map (inv q) [x\<leftarrow>xs @ zs. x \<in> range q], inv q ` S) \<in> failures Q"
  show ?thesis
  proof (rule_tac x = "ipurge_ref ?I' ?D' (?D' y) zs R" in exI,
   rule_tac x = "ipurge_ref ?I' ?D' (?D' y) zs S" in exI, rule_tac x = "{}" in exI,
   (subst conj_assoc [symmetric])+, (rule conjI)+, simp_all del: filter_append)
    have "ipurge_ref ?I' ?D' (?D' y) zs Z =
      ipurge_ref ?I' ?D' (?D' y) zs (R \<union> S \<union> T)"
     using F by simp
    hence "ipurge_ref ?I' ?D' (?D' y) zs Z =
      ipurge_ref ?I' ?D' (?D' y) zs R \<union>
      ipurge_ref ?I' ?D' (?D' y) zs S \<union>
      ipurge_ref ?I' ?D' (?D' y) zs T"
     by (simp add: ipurge_ref_distrib_union)
    moreover have "ipurge_ref ?I' ?D' (?D' y) zs T = {}"
    proof (rule ipurge_ref_empty [of "?D' y"], simp, insert E,
     cases "y \<in> range p", simp_all)
      fix x
      assume O: "x \<in> T"
      with K have "x \<in> - range p" ..
      moreover have "x \<in> - range q"
       using L and O ..
      ultimately have "?D' x = None"
       by simp
      thus "(Some (D (inv p y)), ?D' x) \<in> ?I'"
       by (simp add: con_comp_pol_def)
    next
      fix x
      assume O: "x \<in> T"
      with K have "x \<in> - range p" ..
      moreover have "x \<in> - range q"
       using L and O ..
      ultimately have "?D' x = None"
       by simp
      thus "(Some (E (inv q y)), ?D' x) \<in> ?I'"
       by (simp add: con_comp_pol_def)
    qed
    ultimately show "ipurge_ref ?I' ?D' (?D' y) zs Z =
      ipurge_ref ?I' ?D' (?D' y) zs R \<union>
      ipurge_ref ?I' ?D' (?D' y) zs S"
     by simp
  next
    show "set xs \<subseteq> range p \<union> range q"
     using G .
  next
    have "set (ipurge_tr ?I' ?D' (?D' y) zs) \<subseteq> set zs"
     by (rule ipurge_tr_set)
    thus "set (ipurge_tr ?I' ?D' (?D' y) zs) \<subseteq> range p \<union> range q"
     using H by simp
  next
    have "ipurge_ref ?I' ?D' (?D' y) zs R \<subseteq> R"
     by (rule ipurge_ref_subset)
    thus "ipurge_ref ?I' ?D' (?D' y) zs R \<subseteq> range p"
     using I by simp
  next
    have "ipurge_ref ?I' ?D' (?D' y) zs S \<subseteq> S"
     by (rule ipurge_ref_subset)
    thus "ipurge_ref ?I' ?D' (?D' y) zs S \<subseteq> range q"
     using J by simp
  next
    have "map (inv p) [x\<leftarrow>xs @ y # ys. x \<in> range p] \<in> traces P \<and>
      map (inv q) [x\<leftarrow>xs @ y # ys. x \<in> range q] \<in> traces Q"
     using D by (rule con_comp_failures_traces)
    hence "map (inv p) [x\<leftarrow>(xs @ [y]) @ ys. x \<in> range p] \<in> traces P"
     by simp
    hence "map (inv p) [x\<leftarrow>xs @ [y]. x \<in> range p] @
      map (inv p) [x\<leftarrow>ys. x \<in> range p] \<in> traces P"
     by (subst (asm) filter_append, simp)
    hence "map (inv p) [x\<leftarrow>xs @ [y]. x \<in> range p] \<in> traces P"
     by (rule process_rule_2_traces)
    thus "(map (inv p) [x\<leftarrow>xs @ y # ipurge_tr ?I' ?D' (?D' y) zs. x \<in> range p],
      inv p ` ipurge_ref ?I' ?D' (?D' y) zs R) \<in> failures P"
     by (rule con_comp_secure_add_aux_1 [OF B E H I M])
  next
    have "map (inv p) [x\<leftarrow>xs @ y # ys. x \<in> range p] \<in> traces P \<and>
      map (inv q) [x\<leftarrow>xs @ y # ys. x \<in> range q] \<in> traces Q"
     using D by (rule con_comp_failures_traces)
    hence "map (inv q) [x\<leftarrow>(xs @ [y]) @ ys. x \<in> range q] \<in> traces Q"
     by simp
    hence "map (inv q) [x\<leftarrow>xs @ [y]. x \<in> range q] @
      map (inv q) [x\<leftarrow>ys. x \<in> range q] \<in> traces Q"
     by (subst (asm) filter_append, simp)
    hence "map (inv q) [x\<leftarrow>xs @ [y]. x \<in> range q] \<in> traces Q"
     by (rule process_rule_2_traces)
    thus "(map (inv q) [x\<leftarrow>xs @ y # ipurge_tr ?I' ?D' (?D' y) zs. x \<in> range q],
      inv q ` ipurge_ref ?I' ?D' (?D' y) zs S) \<in> failures Q"
     by (rule con_comp_secure_add_aux_2 [OF A C E H J N])
  qed
qed

lemma con_comp_secure_add_case_2:
  assumes
    A: "consistent_maps D E p q" and
    B: "secure P I D" and
    C: "secure Q I E" and
    D: "(xs @ y # ys, Y) \<in> con_comp_failures P Q p q" and
    E: "y \<in> range p \<or> y \<in> range q"
  shows
   "\<exists>xs'.
      (\<exists>ys'. xs @ zs = xs' @ ys') \<and>
      set xs' \<subseteq> range p \<union> range q \<and>
      map (inv p) [x\<leftarrow>xs'. x \<in> range p] \<in> divergences P \<and>
      map (inv q) [x\<leftarrow>xs'. x \<in> range q] \<in> divergences Q \<Longrightarrow>
    (\<exists>R S T.
      ipurge_ref (con_comp_pol I) (con_comp_map D E p q)
        (con_comp_map D E p q y) zs Z = R \<union> S \<union> T \<and>
      set xs \<subseteq> range p \<union> range q \<and>
      set (ipurge_tr (con_comp_pol I) (con_comp_map D E p q)
        (con_comp_map D E p q y) zs) \<subseteq> range p \<union> range q \<and>
      R \<subseteq> range p \<and>
      S \<subseteq> range q \<and>
      T \<subseteq> - range p \<and>
      T \<subseteq> - range q \<and>
      (map (inv p) [x\<leftarrow>xs @ y # ipurge_tr (con_comp_pol I)
         (con_comp_map D E p q) (con_comp_map D E p q y) zs. x \<in> range p],
       inv p ` R) \<in> failures P \<and>
      (map (inv q) [x\<leftarrow>xs @ y # ipurge_tr (con_comp_pol I)
         (con_comp_map D E p q) (con_comp_map D E p q y) zs. x \<in> range q],
       inv q ` S) \<in> failures Q) \<or>
    (\<exists>xs'.
      (\<exists>ys'. xs @ y # ipurge_tr (con_comp_pol I) (con_comp_map D E p q)
        (con_comp_map D E p q y) zs = xs' @ ys') \<and>
      set xs' \<subseteq> range p \<union> range q \<and>
      map (inv p) [x\<leftarrow>xs'. x \<in> range p] \<in> divergences P \<and>
      map (inv q) [x\<leftarrow>xs'. x \<in> range q] \<in> divergences Q)"
  (is "_ \<Longrightarrow> (\<exists>R S T. ?F R S T zs) \<or> ?G")
proof (erule exE, (erule conjE)+, erule exE)
  fix xs' ys'
  assume
    F: "set xs' \<subseteq> range p \<union> range q" and
    G: "map (inv p) [x\<leftarrow>xs'. x \<in> range p] \<in> divergences P" and
    H: "map (inv q) [x\<leftarrow>xs'. x \<in> range q] \<in> divergences Q" and
    I: "xs @ zs = xs' @ ys'"
  show ?thesis
  proof (cases "length xs < length xs'", rule disjI1, rule_tac [2] disjI2)
    case True
    moreover have "take (length xs') (xs @ zs) =
      take (length xs') xs @ take (length xs' - length xs) zs"
     by simp
    ultimately have "take (length xs') (xs @ zs) =
      xs @ take (length xs' - length xs) zs"
      (is "_ = _ @ ?vs")
     by simp
    moreover have "take (length xs') (xs @ zs) =
      take (length xs') (xs' @ ys')"
     using I by simp
    ultimately have J: "xs @ ?vs = xs'"
     by simp
    moreover have "set xs \<subseteq> set (xs @ ?vs)"
     by simp
    ultimately have "set xs \<subseteq> set xs'"
     by simp
    hence K: "set xs \<subseteq> range p \<union> range q"
     using F by simp
    have "\<exists>R S T. ?F R S T [x\<leftarrow>zs. x \<in> range p \<union> range q]"
      (is "\<exists>_ _ _. ipurge_ref ?I' ?D' _ _ _ = _ \<and> _")
    proof (rule con_comp_secure_add_case_1 [OF A B C D E],
     rule_tac x = "range p \<inter> Z" in exI, rule_tac x = "range q \<inter> Z" in exI,
     rule_tac x = "- range p \<inter> - range q \<inter> Z" in exI,
     (subst conj_assoc [symmetric])+, (rule conjI)+, simp_all del: filter_append)
      show "Z = range p \<inter> Z \<union> range q \<inter> Z \<union> - range p \<inter> - range q \<inter> Z"
       by blast
    next
      show "set xs \<subseteq> range p \<union> range q"
       using K .
    next
      show "{x \<in> set zs. x \<in> range p \<or> x \<in> range q} \<subseteq> range p \<union> range q"
       by blast
    next
      show "- range p \<inter> - range q \<inter> Z \<subseteq> - range p"
       by blast
    next
      show "- range p \<inter> - range q \<inter> Z \<subseteq> - range q"
       by blast
    next
      have "map (inv p) [x\<leftarrow>xs @ ?vs. x \<in> range p] \<in> divergences P"
       using G and J by simp
      hence "map (inv p) [x\<leftarrow>xs @ ?vs. x \<in> range p] @
        map (inv p) [x\<leftarrow>drop (length xs' - length xs) zs. x \<in> range p]
        \<in> divergences P"
        (is "_ @ map (inv p) [x\<leftarrow>?ws. _] \<in> _")
       by (rule process_rule_5_general)
      hence "map (inv p) [x\<leftarrow>(xs @ ?vs) @ ?ws. x \<in> range p] \<in> divergences P"
       by (subst filter_append, simp)
      hence "map (inv p) [x\<leftarrow>xs @ zs. x \<in> range p] \<in> divergences P"
       by simp
      hence "map (inv p) [x\<leftarrow>xs @ [x\<leftarrow>zs. x \<in> range p \<or> x \<in> range q].
        x \<in> range p] \<in> divergences P"
      proof (subst (asm) filter_append, subst filter_append, subst filter_filter)
      qed (subgoal_tac "(\<lambda>x. (x \<in> range p \<or> x \<in> range q) \<and> x \<in> range p) =
       (\<lambda>x. x \<in> range p)", simp, blast)
      thus "(map (inv p) [x\<leftarrow>xs @ [x\<leftarrow>zs. x \<in> range p \<or> x \<in> range q].
        x \<in> range p], inv p ` (range p \<inter> Z)) \<in> failures P"
       by (rule process_rule_6)
    next
      have "map (inv q) [x\<leftarrow>xs @ ?vs. x \<in> range q] \<in> divergences Q"
       using H and J by simp
      hence "map (inv q) [x\<leftarrow>xs @ ?vs. x \<in> range q] @
        map (inv q) [x\<leftarrow>drop (length xs' - length xs) zs. x \<in> range q]
        \<in> divergences Q"
        (is "_ @ map (inv q) [x\<leftarrow>?ws. _] \<in> _")
       by (rule process_rule_5_general)
      hence "map (inv q) [x\<leftarrow>(xs @ ?vs) @ ?ws. x \<in> range q] \<in> divergences Q"
       by (subst filter_append, simp)
      hence "map (inv q) [x\<leftarrow>xs @ zs. x \<in> range q] \<in> divergences Q"
       by simp
      hence "map (inv q) [x\<leftarrow>xs @ [x\<leftarrow>zs. x \<in> range p \<or> x \<in> range q].
        x \<in> range q] \<in> divergences Q"
      proof (subst (asm) filter_append, subst filter_append, subst filter_filter)
      qed (subgoal_tac "(\<lambda>x. (x \<in> range p \<or> x \<in> range q) \<and> x \<in> range q) =
       (\<lambda>x. x \<in> range q)", simp, blast)
      thus "(map (inv q) [x\<leftarrow>xs @ [x\<leftarrow>zs. x \<in> range p \<or> x \<in> range q].
        x \<in> range q], inv q ` (range q \<inter> Z)) \<in> failures Q"
       by (rule process_rule_6)
    qed
    then obtain R and S and T where
     "?F R S T [x\<leftarrow>zs. x \<in> range p \<union> range q]"
     by blast
    thus "\<exists>R S T. ?F R S T zs"
    proof (rule_tac x = R in exI, rule_tac x = S in exI, rule_tac x = T in exI)
    qed (simp only: con_comp_ipurge_tr_filter con_comp_ipurge_ref_filter)
  next
    let
      ?I' = "con_comp_pol I" and
      ?D' = "con_comp_map D E p q"
    case False
    moreover have "xs @ y # ipurge_tr ?I' ?D' (?D' y) zs =
      take (length xs') (xs @ y # ipurge_tr ?I' ?D' (?D' y) zs) @
      drop (length xs') (xs @ y # ipurge_tr ?I' ?D' (?D' y) zs)"
      (is "_ = _ @ ?vs")
     by (simp only: append_take_drop_id)
    ultimately have "xs @ y # ipurge_tr ?I' ?D' (?D' y) zs =
      take (length xs') (xs @ zs) @ ?vs"
     by simp
    hence J: "xs @ y # ipurge_tr ?I' ?D' (?D' y) zs = xs' @ ?vs"
     using I by simp
    show ?G
    proof (rule_tac x = xs' in exI, rule conjI, rule_tac x = ?vs in exI)
    qed (subst J, simp_all add: F G H)
  qed
qed

theorem con_comp_secure:
  assumes
    A: "consistent_maps D E p q" and
    B: "secure P I D" and
    C: "secure Q I E"
  shows "secure (P \<parallel> Q <p, q>) (con_comp_pol I) (con_comp_map D E p q)"
proof (simp add: secure_def con_comp_futures, (rule allI)+, rule impI,
 erule conjE, rule conjI, (erule rev_mp)+, rotate_tac [2], erule_tac [2] rev_mp)
  fix xs y ys Y zs Z
  show
   "(xs @ zs, Z) \<in> con_comp_failures P Q p q \<longrightarrow>
    (xs @ y # ys, Y) \<in> con_comp_failures P Q p q \<longrightarrow>
      (xs @ ipurge_tr (con_comp_pol I) (con_comp_map D E p q)
         (con_comp_map D E p q y) ys,
       ipurge_ref (con_comp_pol I) (con_comp_map D E p q)
         (con_comp_map D E p q y) ys Y)
      \<in> con_comp_failures P Q p q"
    (is "_ \<longrightarrow> _ \<longrightarrow> (_ @ ipurge_tr ?I' ?D' _ _, _) \<in> _")
  proof ((rule impI)+, thin_tac "(xs @ zs, Z) \<in> con_comp_failures P Q p q",
   simp_all add: con_comp_failures_def con_comp_divergences_def
   del: filter_append, erule disjE, rule disjI1)
  qed (erule con_comp_secure_del_case_1 [OF A B C],
   rule con_comp_secure_del_case_2 [OF A B C])
next
  fix xs y ys Y zs Z
  assume D: "(xs @ y # ys, Y) \<in> con_comp_failures P Q p q"
  show
   "(xs @ zs, Z) \<in> con_comp_failures P Q p q \<longrightarrow>
      (xs @ y # ipurge_tr (con_comp_pol I) (con_comp_map D E p q)
         (con_comp_map D E p q y) zs,
       ipurge_ref (con_comp_pol I) (con_comp_map D E p q)
         (con_comp_map D E p q y) zs Z)
      \<in> con_comp_failures P Q p q"
    (is "_ \<longrightarrow> (_ @ _ # ipurge_tr ?I' ?D' _ _, _) \<in> _")
  proof (rule impI, simp_all add: con_comp_failures_def con_comp_divergences_def
   del: filter_append, cases "y \<in> range p \<or> y \<in> range q", simp del: filter_append,
   erule disjE, rule disjI1, rule_tac [3] disjI2)
  qed (erule con_comp_secure_add_case_1 [OF A B C D], assumption,
   erule con_comp_secure_add_case_2 [OF A B C D], assumption,
   rule con_comp_failures_divergences [OF D], simp_all)
qed


subsection "Conservation of noninterference security in the absence of fake events"

text \<open>
In what follows, it is proven that in the absence of fake events, namely if
@{term "range p \<union> range q = UNIV"}, the output of the concurrent composition of two secure processes
is secure with respect to the same noninterference policy enforced by the input processes, and to
the event-domain map that simply associates each event to the same security domain as the
corresponding events of the input processes.

More formally, for any two processes @{term P}, @{term Q} being secure with respect to the
noninterference policy @{term I} and the event-domain maps @{term D}, @{term E}, their concurrent
composition @{term "P \<parallel> Q <p, q>"} is secure with respect to the same noninterference policy
@{term I} and the event-domain map @{term "the \<circ> con_comp_map D E p q"}, provided that conditions
@{term "range p \<union> range q = UNIV"} and @{term "consistent_maps D E p q"} are satisfied.

\null
\<close>

lemma con_comp_sinks_range:
 "u \<in> range Some \<Longrightarrow>
  set xs \<subseteq> range p \<union> range q \<Longrightarrow>
    sinks (con_comp_pol I) (con_comp_map D E p q) u xs \<subseteq> range Some"
by (insert con_comp_sinks_aux_range [of "{u}" xs p q I D E],
 simp add: sinks_aux_single_dom)

lemma con_comp_sinks_no_fake:
  assumes
    A: "range p \<union> range q = UNIV" and
    B: "u \<in> range Some"
  shows "sinks I (the \<circ> con_comp_map D E p q) (the u) xs =
    the ` sinks (con_comp_pol I) (con_comp_map D E p q) u xs"
    (is "_ = the ` sinks ?I' ?D' _ _")
proof (induction xs rule: rev_induct, simp)
  fix x xs
  assume C: "sinks I (the \<circ> ?D') (the u) xs = the ` sinks ?I' ?D' u xs"
  have "x \<in> range p \<union> range q"
   using A by simp
  hence D: "?D' x = Some (the (?D' x))"
   by (cases "x \<in> range p", simp_all)
  have E: "u = Some (the u)"
   using B by (simp add: image_iff)
  show "sinks I (the \<circ> ?D') (the u) (xs @ [x]) = the ` sinks ?I' ?D' u (xs @ [x])"
  proof (cases "(u, ?D' x) \<in> ?I' \<or> (\<exists>v \<in> sinks ?I' ?D' u xs. (v, ?D' x) \<in> ?I')")
    case True
    hence "sinks ?I' ?D' u (xs @ [x]) = insert (?D' x) (sinks ?I' ?D' u xs)"
     by simp
    moreover have "(the u, the (?D' x)) \<in> I \<or>
      (\<exists>d \<in> sinks I (the \<circ> ?D') (the u) xs. (d, the (?D' x)) \<in> I)"
    proof (rule disjE [OF True], rule disjI1, rule_tac [2] disjI2)
      assume "(u, ?D' x) \<in> ?I'"
      hence "(Some (the u), Some (the (?D' x))) \<in> ?I'"
       using D and E by simp
      thus "(the u, the (?D' x)) \<in> I"
       by (simp add: con_comp_pol_def)
    next
      assume "\<exists>v \<in> sinks ?I' ?D' u xs. (v, ?D' x) \<in> ?I'"
      then obtain v where F: "v \<in> sinks ?I' ?D' u xs" and G: "(v, ?D' x) \<in> ?I'" ..
      have "sinks ?I' ?D' u xs \<subseteq> range Some"
       by (rule con_comp_sinks_range, simp_all add: A B)
      hence "v \<in> range Some"
       using F ..
      hence "v = Some (the v)"
       by (simp add: image_iff)
      hence "(Some (the v), Some (the (?D' x))) \<in> ?I'"
       using D and G by simp
      hence "(the v, the (?D' x)) \<in> I"
       by (simp add: con_comp_pol_def)
      moreover have "the v \<in> sinks I (the \<circ> ?D') (the u) xs"
       using C and F by simp
      ultimately show "\<exists>d \<in> sinks I (the \<circ> ?D') (the u) xs.
        (d, the (?D' x)) \<in> I" ..
    qed
    hence "sinks I (the \<circ> ?D') (the u) (xs @ [x]) =
      insert (the (?D' x)) (sinks I (the \<circ> ?D') (the u) xs)"
     by simp
    ultimately show ?thesis
     using C by simp
  next
    case False
    hence "sinks ?I' ?D' u (xs @ [x]) = sinks ?I' ?D' u xs"
     by simp
    moreover have "\<not> ((the u, the (?D' x)) \<in> I \<or>
      (\<exists>v \<in> sinks I (the \<circ> ?D') (the u) xs. (v, the (?D' x)) \<in> I))"
    proof (insert False, simp, erule conjE, rule conjI, rule_tac [2] ballI)
      assume "(u, ?D' x) \<notin> ?I'"
      hence "(Some (the u), Some (the (?D' x))) \<notin> ?I'"
       using D and E by simp
      thus "(the u, the (?D' x)) \<notin> I"
       by (simp add: con_comp_pol_def)
    next
      fix d
      assume "d \<in> sinks I (the \<circ> ?D') (the u) xs"
      hence "d \<in> the ` sinks ?I' ?D' u xs"
       using C by simp
      hence "\<exists>v \<in> sinks ?I' ?D' u xs. d = the v"
       by (simp add: image_iff)
      then obtain v where F: "v \<in> sinks ?I' ?D' u xs" and G: "d = the v" ..
      have "sinks ?I' ?D' u xs \<subseteq> range Some"
       by (rule con_comp_sinks_range, simp_all add: A B)
      hence "v \<in> range Some"
       using F ..
      hence H: "v = Some d"
       using G by (simp add: image_iff)
      assume "\<forall>v \<in> sinks ?I' ?D' u xs. (v, ?D' x) \<notin> ?I'"
      hence "(v, ?D' x) \<notin> ?I'"
       using F ..
      hence "(Some d, Some (the (?D' x))) \<notin> ?I'"
       using D and H by simp
      thus "(d, the (?D' x)) \<notin> I"
       by (simp add: con_comp_pol_def)
    qed
    hence "sinks I (the \<circ> ?D') (the u) (xs @ [x]) = sinks I (the \<circ> ?D') (the u) xs"
     by simp
    ultimately show ?thesis
     using C by simp
  qed
qed

lemma con_comp_ipurge_tr_no_fake:
  assumes
    A: "range p \<union> range q = UNIV" and
    B: "u \<in> range Some"
  shows "ipurge_tr (con_comp_pol I) (con_comp_map D E p q) u xs =
    ipurge_tr I (the \<circ> con_comp_map D E p q) (the u) xs"
    (is "ipurge_tr ?I' ?D' _ _ = _")
proof (induction xs rule: rev_induct, simp)
  fix x xs
  assume C: "ipurge_tr ?I' ?D' u xs = ipurge_tr I (the \<circ> ?D') (the u) xs"
  show "ipurge_tr ?I' ?D' u (xs @ [x]) = ipurge_tr I (the \<circ> ?D') (the u) (xs @ [x])"
  proof (cases "?D' x \<in> sinks ?I' ?D' u (xs @ [x])")
    case True
    hence "ipurge_tr ?I' ?D' u (xs @ [x]) = ipurge_tr ?I' ?D' u xs"
     by simp
    moreover have "the (?D' x) \<in> the ` sinks ?I' ?D' u (xs @ [x])"
     using True by simp
    hence "the (?D' x) \<in> sinks I (the \<circ> ?D') (the u) (xs @ [x])"
     by (subst con_comp_sinks_no_fake [OF A B])
    hence "ipurge_tr I (the \<circ> ?D') (the u) (xs @ [x]) =
      ipurge_tr I (the \<circ> ?D') (the u) xs"
     by simp
    ultimately show ?thesis
     using C by simp
  next
    case False
    hence "ipurge_tr ?I' ?D' u (xs @ [x]) = ipurge_tr ?I' ?D' u xs @ [x]"
     by simp
    moreover have "the (?D' x) \<notin> the ` sinks ?I' ?D' u (xs @ [x])"
    proof
      assume "the (?D' x) \<in> the ` sinks ?I' ?D' u (xs @ [x])"
      hence "\<exists>v \<in> sinks ?I' ?D' u (xs @ [x]). the (?D' x) = the v"
       by (simp add: image_iff)
      then obtain v where
        D: "v \<in> sinks ?I' ?D' u (xs @ [x])" and E: "the (?D' x) = the v" ..
      have "x \<in> range p \<union> range q"
       using A by simp
      hence "\<exists>d. ?D' x = Some d"
       by (cases "x \<in> range p", simp_all)
      then obtain d where "?D' x = Some d" ..
      moreover have "sinks ?I' ?D' u (xs @ [x]) \<subseteq> range Some"
       by (rule con_comp_sinks_range, simp_all add: A B)
      hence "v \<in> range Some"
       using D ..
      hence "\<exists>d'. v = Some d'"
       by (simp add: image_iff)
      then obtain d' where "v = Some d'" ..
      ultimately have "?D' x = v"
       using E by simp
      hence "?D' x \<in> sinks ?I' ?D' u (xs @ [x])"
       using D by simp
      thus False
       using False by contradiction
    qed
    hence "the (?D' x) \<notin> sinks I (the \<circ> ?D') (the u) (xs @ [x])"
     by (subst con_comp_sinks_no_fake [OF A B])
    hence "ipurge_tr I (the \<circ> ?D') (the u) (xs @ [x]) =
      ipurge_tr I (the \<circ> ?D') (the u) xs @ [x]"
     by simp
    ultimately show ?thesis
     using C by simp
  qed
qed

lemma con_comp_ipurge_ref_no_fake:
  assumes
    A: "range p \<union> range q = UNIV" and
    B: "u \<in> range Some"
  shows "ipurge_ref (con_comp_pol I) (con_comp_map D E p q) u xs X =
    ipurge_ref I (the \<circ> con_comp_map D E p q) (the u) xs X"
    (is "ipurge_ref ?I' ?D' _ _ _ = _")
proof (simp add: ipurge_ref_def set_eq_iff, rule allI,
 simp_all add: con_comp_sinks_no_fake [OF A B])
  fix x
  have "x \<in> range p \<union> range q"
   using A by simp
  hence C: "?D' x = Some (the (?D' x))"
   by (cases "x \<in> range p", simp_all)
  have D: "u = Some (the u)"
   using B by (simp add: image_iff)
  show
   "(x \<in> X \<and> (u, ?D' x) \<notin> con_comp_pol I \<and>
      (\<forall>v \<in> sinks ?I' ?D' u xs. (v, ?D' x) \<notin> con_comp_pol I)) =
    (x \<in> X \<and> (the u, the (?D' x)) \<notin> I \<and>
      (\<forall>v \<in> sinks ?I' ?D' u xs. (the v, the (?D' x)) \<notin> I))"
  proof (rule iffI, (erule_tac [!] conjE)+, simp_all, rule_tac [!] conjI,
   rule_tac [2] ballI, rule_tac [4] ballI)
    assume "(u, ?D' x) \<notin> ?I'"
    hence "(Some (the u), Some (the (?D' x))) \<notin> ?I'"
     using C and D by simp
    thus "(the u, the (?D' x)) \<notin> I"
     by (simp add: con_comp_pol_def)
  next
    fix v
    assume "\<forall>v \<in> sinks ?I' ?D' u xs. (v, ?D' x) \<notin> ?I'" and
      E: "v \<in> sinks ?I' ?D' u xs"
    hence "(v, ?D' x) \<notin> ?I'" ..
    moreover have "sinks ?I' ?D' u xs \<subseteq> range Some"
     by (rule con_comp_sinks_range, simp_all add: A B)
    hence "v \<in> range Some"
     using E ..
    hence "v = Some (the v)"
     by (simp add: image_iff)
    ultimately have "(Some (the v), Some (the (?D' x))) \<notin> ?I'"
     using C by simp
    thus "(the v, the (?D' x)) \<notin> I"
     by (simp add: con_comp_pol_def)
  next
    assume "(the u, the (?D' x)) \<notin> I"
    hence "(Some (the u), Some (the (?D' x))) \<notin> ?I'"
     by (simp add: con_comp_pol_def)
    thus "(u, ?D' x) \<notin> ?I'"
     using C and D by simp
  next
    fix v
    assume "\<forall>v \<in> sinks ?I' ?D' u xs. (the v, the (?D' x)) \<notin> I" and
      E: "v \<in> sinks ?I' ?D' u xs"
    hence "(the v, the (?D' x)) \<notin> I" ..
    hence "(Some (the v), Some (the (?D' x))) \<notin> ?I'"
     by (simp add: con_comp_pol_def)
    moreover have "sinks ?I' ?D' u xs \<subseteq> range Some"
     by (rule con_comp_sinks_range, simp_all add: A B)
    hence "v \<in> range Some"
     using E ..
    hence "v = Some (the v)"
     by (simp add: image_iff)
    ultimately show "(v, ?D' x) \<notin> ?I'"
     using C by simp
  qed
qed

theorem con_comp_secure_no_fake:
  assumes
    A: "range p \<union> range q = UNIV" and
    B: "consistent_maps D E p q" and
    C: "secure P I D" and
    D: "secure Q I E"
  shows "secure (P \<parallel> Q <p, q>) I (the \<circ> con_comp_map D E p q)"
proof (insert con_comp_secure [OF B C D], simp add: secure_def,
 (rule allI)+, rule impI)
  fix xs y ys Y zs Z
  let
    ?I' = "con_comp_pol I" and
    ?D' = "con_comp_map D E p q"
  have "y \<in> range p \<union> range q"
   using A by simp
  hence E: "?D' y \<in> range Some"
   by (cases "y \<in> range p", simp_all)
  assume "\<forall>xs y ys Y zs Z.
    (y # ys, Y) \<in> futures (P \<parallel> Q <p, q>) xs \<and>
    (zs, Z) \<in> futures (P \<parallel> Q <p, q>) xs \<longrightarrow>
      (ipurge_tr ?I' ?D' (?D' y) ys, ipurge_ref ?I' ?D' (?D' y) ys Y)
        \<in> futures (P \<parallel> Q <p, q>) xs \<and>
      (y # ipurge_tr ?I' ?D' (?D' y) zs, ipurge_ref ?I' ?D' (?D' y) zs Z)
        \<in> futures (P \<parallel> Q <p, q>) xs" and
   "(y # ys, Y) \<in> futures (P \<parallel> Q <p, q>) xs \<and>
    (zs, Z) \<in> futures (P \<parallel> Q <p, q>) xs"
  hence
   "(ipurge_tr ?I' ?D' (?D' y) ys, ipurge_ref ?I' ?D' (?D' y) ys Y)
      \<in> futures (P \<parallel> Q <p, q>) xs \<and>
    (y # ipurge_tr ?I' ?D' (?D' y) zs, ipurge_ref ?I' ?D' (?D' y) zs Z)
      \<in> futures (P \<parallel> Q <p, q>) xs"
   by blast
  thus
   "(ipurge_tr I (the \<circ> ?D') (the (?D' y)) ys,
      ipurge_ref I (the \<circ> ?D') (the (?D' y)) ys Y) \<in> futures (P \<parallel> Q <p, q>) xs \<and>
    (y # ipurge_tr I (the \<circ> ?D') (the (?D' y)) zs,
      ipurge_ref I (the \<circ> ?D') (the (?D' y)) zs Z) \<in> futures (P \<parallel> Q <p, q>) xs"
   by (simp add: con_comp_ipurge_tr_no_fake [OF A E]
    con_comp_ipurge_ref_no_fake [OF A E])
qed

end
