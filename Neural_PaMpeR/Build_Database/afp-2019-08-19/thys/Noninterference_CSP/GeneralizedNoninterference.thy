(*  Title:       Noninterference Security in Communicating Sequential Processes
    Author:      Pasquale Noce
                 Security Certification Specialist at Arjo Systems - Gep S.p.A.
                 pasquale dot noce dot lavoro at gmail dot com
                 pasquale dot noce at arjowiggins-it dot com
*)

section "CSP noninterference vs. generalized noninterference"

theory GeneralizedNoninterference
imports ClassicalNoninterference
begin

text \<open>
\null

The purpose of this section is to compare CSP noninterference security as defined previously with
McCullough's notion of generalized noninterference security as formulated in \cite{R4}. It will be
shown that this security property is weaker than both CSP noninterference security for a generic
process, and classical noninterference security for classical processes, viz. it is a necessary but
not sufficient condition for them. This renders CSP noninterference security preferable as an
extension of classical noninterference security to nondeterministic systems.

For clarity, all the constants and fact names defined in this section, with the possible exception
of datatype constructors and main theorems, contain prefix \<open>g_\<close>.
\<close>


subsection "Generalized noninterference"

text \<open>
The original formulation of generalized noninterference security as contained in \cite{R4} focuses
on systems whose events, split in inputs and outputs, are mapped into either of two security levels,
\emph{high} and \emph{low}. Such a system is said to be secure just in case, for any trace
\<open>xs\<close> and any high-level input \<open>x\<close>, the set of the \emph{possible low-level futures} of
\<open>xs\<close>, i.e. of the sequences of low-level events that may succeed \<open>xs\<close> in the traces of
the system, is equal to the set of the possible low-level futures of \<open>xs @ [x]\<close>.

This definition requires the following corrections:

\begin{itemize}

\item
Variable \<open>x\<close> must range over all high-level events rather than over high-level inputs alone,
since high-level outputs must not be allowed to affect low-level futures as well.

\item
For any \<open>x\<close>, the range of trace \<open>xs\<close> must be restricted to the traces of the system that
may be succeeded by \<open>x\<close>, viz. trace \<open>xs\<close> must be such that event list \<open>xs @ [x]\<close>
be itself a trace.
\\Otherwise, a system that admits both high-level and low-level events in its alphabet but never
accepts any high-level event, always accepting any low-level one instead, would turn out not to be
secure, which is paradoxical since \emph{high} can by no means affect \emph{low} in a system never
engaging in high-level events. The cause of the paradox is that, for each trace \<open>xs\<close> and each
high-level event \<open>x\<close> of such a system, the set of the possible low-level futures of \<open>xs\<close>
matches the Kleene closure of the set of low-level events, whereas the set of the possible low-level
futures of \<open>xs @ [x]\<close> matches the empty set as \<open>xs @ [x]\<close> is not a trace.

\end{itemize}

Observe that the latter correction renders it unnecessary to explicitly assume that event list
\<open>xs\<close> be a trace of the system, as this follows from the assumption that \<open>xs @ [x]\<close> be
such.

Here below is a formal definition of the notion of generalized noninterference security for
processes, amended in accordance with the previous considerations.

\null
\<close>

datatype g_level = High | Low

definition g_secure :: "'a process \<Rightarrow> ('a \<Rightarrow> g_level) \<Rightarrow> bool" where
"g_secure P L \<equiv> \<forall>xs x. xs @ [x] \<in> traces P \<and> L x = High \<longrightarrow>
  {ys'. \<exists>ys. xs @ ys \<in> traces P \<and> ys' = [y\<leftarrow>ys. L y = Low]} =
  {ys'. \<exists>ys. xs @ x # ys \<in> traces P \<and> ys' = [y\<leftarrow>ys. L y = Low]}"

text \<open>
\null

It is possible to prove that a weaker sufficient (as well as necessary, as obvious) condition for
generalized noninterference security is that the set of the possible low-level futures of trace
\<open>xs\<close> be included in the set of the possible low-level futures of trace \<open>xs @ [x]\<close>,
because the latter is always included in the former.

In what follows, such security property is defined formally and its sufficiency for generalized
noninterference security to hold is demonstrated in the form of an introduction rule, which will
turn out to be useful in subsequent proofs.

\null
\<close>

definition g_secure_suff :: "'a process \<Rightarrow> ('a \<Rightarrow> g_level) \<Rightarrow> bool" where
"g_secure_suff P L \<equiv> \<forall>xs x. xs @ [x] \<in> traces P \<and> L x = High \<longrightarrow>
  {ys'. \<exists>ys. xs @ ys \<in> traces P \<and> ys' = [y\<leftarrow>ys. L y = Low]} \<subseteq>
  {ys'. \<exists>ys. xs @ x # ys \<in> traces P \<and> ys' = [y\<leftarrow>ys. L y = Low]}"

lemma g_secure_suff_implies_g_secure:
  assumes S: "g_secure_suff P L"
  shows "g_secure P L"
proof (simp add: g_secure_def, (rule allI)+, rule impI, erule conjE)
  fix xs x
  assume
    A: "xs @ [x] \<in> traces P" and
    B: "L x = High"
  show "{ys'. \<exists>ys. xs @ ys \<in> traces P \<and> ys' = [y\<leftarrow>ys . L y = Low]} =
    {ys'. \<exists>ys. xs @ x # ys \<in> traces P \<and> ys' = [y\<leftarrow>ys . L y = Low]}"
   (is "{ys'. \<exists>ys. ?Q ys ys'} = {ys'. \<exists>ys. ?Q' ys ys'}")
  proof (rule equalityI, rule_tac [2] subsetI, simp_all, erule_tac [2] exE,
   erule_tac [2] conjE)
    show "{ys'. \<exists>ys. ?Q ys ys'} \<subseteq> {ys'. \<exists>ys. ?Q' ys ys'}"
     using S and A and B by (simp add: g_secure_suff_def)
  next
    fix ys ys'
    assume "xs @ x # ys \<in> traces P"
    moreover assume "ys' = [y\<leftarrow>ys. L y = Low]"
    hence "ys' = [y\<leftarrow>x # ys. L y = Low]" using B by simp
    ultimately have "?Q (x # ys) ys'" ..
    thus "\<exists>ys. ?Q ys ys'" ..
  qed
qed


subsection "Comparison between security properties"

text \<open>
In the continuation, it will be proven that CSP noninterference security is a sufficient condition
for generalized noninterference security for any process whose events are mapped into either
security domain \<open>High\<close> or \<open>Low\<close>, under the policy that \<open>High\<close> may not affect
\<open>Low\<close>.

Particularly, this is the case for any such classical process. This fact, along with the equivalence
between CSP noninterference security and classical noninterference security for classical processes,
is used to additionally prove that the classical noninterference security of a deterministic state
machine is a sufficient condition for the generalized noninterference security of the corresponding
classical process under the aforesaid policy.

\null
\<close>

definition g_I :: "(g_level \<times> g_level) set" where
"g_I \<equiv> {(High, High), (Low, Low), (Low, High)}"

lemma g_I_refl: "refl g_I"
proof (simp add: refl_on_def, rule allI)
  fix x
  show "(x, x) \<in> g_I" by (cases x, simp_all add: g_I_def)
qed

lemma g_sinks: "sinks g_I L High xs \<subseteq> {High}"
proof (induction xs rule: rev_induct, simp)
  fix x xs
  assume A: "sinks g_I L High xs \<subseteq> {High}"
  show "sinks g_I L High (xs @ [x]) \<subseteq> {High}"
  proof (cases "L x")
    assume "L x = High"
    thus ?thesis using A by simp
  next
    assume B: "L x = Low"
    have "\<not> ((High, L x) \<in> g_I \<or> (\<exists>v \<in> sinks g_I L High xs. (v, L x) \<in> g_I))"
    proof (rule notI, simp add: B, erule disjE)
      assume "(High, Low) \<in> g_I"
      moreover have "(High, Low) \<notin> g_I" by (simp add: g_I_def)
      ultimately show False by contradiction
    next
      assume "\<exists>v \<in> sinks g_I L High xs. (v, Low) \<in> g_I"
      then obtain v where C: "v \<in> sinks g_I L High xs" and D: "(v, Low) \<in> g_I" ..
      have "v \<in> {High}" using A and C ..
      hence "(High, Low) \<in> g_I" using D by simp
      moreover have "(High, Low) \<notin> g_I" by (simp add: g_I_def)
      ultimately show False by contradiction
    qed
    thus ?thesis using A by simp
  qed
qed

lemma g_ipurge_tr: "ipurge_tr g_I L High xs = [x\<leftarrow>xs. L x = Low]"
proof (induction xs rule: rev_induct, simp)
  fix x xs
  assume A: "ipurge_tr g_I L High xs = [x'\<leftarrow>xs. L x' = Low]"
  show "ipurge_tr g_I L High (xs @ [x]) = [x'\<leftarrow>xs @ [x]. L x' = Low]"
  proof (cases "L x")
    assume B: "L x = High"
    hence "ipurge_tr g_I L High (xs @ [x]) = ipurge_tr g_I L High xs"
     by (simp add: g_I_def)
    moreover have "[x'\<leftarrow>xs @ [x]. L x' = Low] = [x'\<leftarrow>xs. L x' = Low]"
     using B by simp
    ultimately show ?thesis using A by simp
  next
    assume B: "L x = Low"
    have "L x \<notin> sinks g_I L High (xs @ [x])"
    proof (rule notI, simp only: B)
      have "sinks g_I L High (xs @ [x]) \<subseteq> {High}" by (rule g_sinks)
      moreover assume "Low \<in> sinks g_I L High (xs @ [x])"
      ultimately have "Low \<in> {High}" ..
      thus False by simp
    qed
    hence "ipurge_tr g_I L High (xs @ [x]) = ipurge_tr g_I L High xs @ [x]"
     by simp
    moreover have "[x'\<leftarrow>xs @ [x]. L x' = Low] = [x'\<leftarrow>xs. L x' = Low] @ [x]"
     using B by simp
    ultimately show ?thesis using A by simp
  qed
qed

theorem secure_implies_g_secure:
  assumes S: "secure P g_I L"
  shows "g_secure P L"
proof (rule g_secure_suff_implies_g_secure, simp add: g_secure_suff_def, (rule allI)+,
 rule impI, rule subsetI, simp, erule exE, (erule conjE)+)
  fix xs x ys ys'
  assume "xs @ [x] \<in> traces P"
  hence "\<exists>X. ([x], X) \<in> futures P xs"
   by (simp add: traces_def Domain_iff futures_def)
  then obtain X where "([x], X) \<in> futures P xs" ..
  moreover assume "xs @ ys \<in> traces P"
  hence "\<exists>Y. (ys, Y) \<in> futures P xs"
   by (simp add: traces_def Domain_iff futures_def)
  then obtain Y where "(ys, Y) \<in> futures P xs" ..
  ultimately have "(x # ipurge_tr g_I L (L x) ys,
    ipurge_ref g_I L (L x) ys Y) \<in> futures P xs"
   (is "(_, ?Y') \<in> futures P xs") using S by (simp add: secure_def)
  moreover assume "L x = High" and A: "ys' = [y\<leftarrow>ys. L y = Low]"
  ultimately have "(x # ys', ?Y') \<in> futures P xs" by (simp add: g_ipurge_tr)
  hence "\<exists>Y'. (x # ys', Y') \<in> futures P xs" ..
  hence "xs @ x # ys' \<in> traces P"
   by (simp add: traces_def Domain_iff futures_def)
  moreover have "ys' = [y\<leftarrow>ys'. L y = Low]" using A by simp
  ultimately have "xs @ x # ys' \<in> traces P \<and> ys' = [y\<leftarrow>ys'. L y = Low]" ..
  thus "\<exists>ys. xs @ x # ys \<in> traces P \<and> ys' = [y\<leftarrow>ys. L y = Low]" ..
qed

theorem c_secure_implies_g_secure:
 "c_secure step out s\<^sub>0 g_I L \<Longrightarrow> g_secure (c_process step out s\<^sub>0) (c_dom L)"
by (rule secure_implies_g_secure, rule c_secure_implies_secure, rule g_I_refl)

text \<open>
\null

Since the definition of generalized noninterference security does not impose any explicit
requirement on process refusals, intuition suggests that this security property is likely to be
generally weaker than CSP noninterference security for nondeterministic processes, which are such
that even a complete specification of their traces leaves underdetermined their refusals. This is
not the case for deterministic processes, so the aforesaid security properties might in principle
be equivalent as regards such processes.

However, a counterexample proving the contrary is provided by a deterministic state machine
resembling systems \emph{A} and \emph{B} described in \cite{R4}, section 3.1. This machine is proven
not to be classical noninterference-secure, whereas the corresponding classical process turns out to
be generalized noninterference-secure, which proves that the generalized noninterference security of
a classical process is not a sufficient condition for the classical noninterference security of the
associated deterministic state machine.

This result, along with the equivalence between CSP noninterference security and classical
noninterference security for classical processes, is then used to demonstrate that the generalized
noninterference security of the aforesaid classical process does not entail its CSP noninterference
security, which proves that generalized noninterference security is actually not a sufficient
condition for CSP noninterference security even in the case of deterministic processes.

The remainder of this section is dedicated to the construction of such counterexample.

\null
\<close>

datatype g_state = Even | Odd

datatype g_action = Any | Count

primrec g_step :: "g_state \<Rightarrow> g_action \<Rightarrow> g_state" where
"g_step s Any = (case s of Even \<Rightarrow> Odd | Odd \<Rightarrow> Even)" |
"g_step s Count = s"

primrec g_out :: "g_state \<Rightarrow> g_action \<Rightarrow> g_state option" where
"g_out _ Any = None" |
"g_out s Count = Some s"

primrec g_D :: "g_action \<Rightarrow> g_level" where
"g_D Any = High" |
"g_D Count = Low"

definition g_s\<^sub>0 :: g_state where
"g_s\<^sub>0 \<equiv> Even"

lemma g_secure_counterexample:
 "g_secure (c_process g_step g_out g_s\<^sub>0) (c_dom g_D)"
proof (rule g_secure_suff_implies_g_secure, simp add: g_secure_suff_def, (rule allI)+,
 rule impI, rule subsetI, simp, erule exE, (erule conjE)+)
  fix xps x p yps yps'
  assume "xps @ [(x, p)] \<in> traces (c_process g_step g_out g_s\<^sub>0)"
  hence "\<exists>X. (xps @ [(x, p)], X) \<in> c_failures g_step g_out g_s\<^sub>0"
   by (simp add: c_traces)
  then obtain X where "(xps @ [(x, p)], X) \<in> c_failures g_step g_out g_s\<^sub>0" ..
  hence "xps @ [(x, p)] = c_tr g_step g_out g_s\<^sub>0 (map fst (xps @ [(x, p)]))"
   by (rule c_failures_tr)
  moreover assume "c_dom g_D (x, p) = High"
  hence "x = Any" by (cases x, simp_all add: c_dom_def)
  ultimately have "xps @ [(x, p)] = c_tr g_step g_out g_s\<^sub>0 (map fst xps @ [Any])"
   (is "_ = _ (?xs @ _)") by simp
  moreover assume "xps @ yps \<in> traces (c_process g_step g_out g_s\<^sub>0)"
  hence "\<exists>Y. (xps @ yps, Y) \<in> c_failures g_step g_out g_s\<^sub>0"
   by (simp add: c_traces)
  then obtain Y where "(xps @ yps, Y) \<in> c_failures g_step g_out g_s\<^sub>0" ..
  hence "(yps, Y) \<in> futures (c_process g_step g_out g_s\<^sub>0) xps"
   by (simp add: c_futures_failures)
  hence "yps = c_tr g_step g_out (foldl g_step g_s\<^sub>0 ?xs) (map fst yps)"
   (is "_ = c_tr _ _ _ ?ys") by (rule c_futures_tr)
  hence "yps =
    c_tr g_step g_out (foldl g_step (foldl g_step g_s\<^sub>0 (?xs @ [Any])) [Any]) ?ys"
   (is "_ = c_tr _ _ (foldl _ ?s _) _") by (cases "foldl g_step g_s\<^sub>0 ?xs", simp_all)
  hence "c_tr g_step g_out ?s [Any] @ yps = c_tr g_step g_out ?s ([Any] @ ?ys)"
   (is "?yp @ _ = _") by (simp only: c_tr_append)
  moreover have "(c_tr g_step g_out ?s ([Any] @ ?ys),
    {(x, p). p \<noteq> g_out (foldl g_step ?s ([Any] @ ?ys)) x})
    \<in> futures (c_process g_step g_out g_s\<^sub>0) (c_tr g_step g_out g_s\<^sub>0 (?xs @ [Any]))"
   (is "(_, ?Y') \<in> _") by (rule c_tr_futures)
  ultimately have "(?yp @ yps, ?Y')
    \<in> futures (c_process g_step g_out g_s\<^sub>0) (xps @ [(x, p)])"
   by simp
  hence "(xps @ (x, p) # ?yp @ yps, ?Y') \<in> c_failures g_step g_out g_s\<^sub>0"
   by (simp add: c_futures_failures)
  hence "\<exists>Y'. (xps @ (x, p) # ?yp @ yps, Y') \<in> c_failures g_step g_out g_s\<^sub>0" ..
  hence "xps @ (x, p) # ?yp @ yps \<in> traces (c_process g_step g_out g_s\<^sub>0)"
   (is "?P (?yp @ yps)") by (simp add: c_traces)
  moreover assume "yps' = [yp\<leftarrow>yps. c_dom g_D yp = Low]"
  hence "yps' = [yp\<leftarrow>?yp @ yps. c_dom g_D yp = Low]"
   (is "?Q (?yp @ yps)") by (simp add: c_tr_singleton c_dom_def)
  ultimately have "?P (?yp @ yps) \<and> ?Q (?yp @ yps)" ..
  thus "\<exists>yps. ?P yps \<and> ?Q yps" ..
qed

lemma not_c_secure_counterexample:
 "\<not> c_secure g_step g_out g_s\<^sub>0 g_I g_D"
proof (simp add: c_secure_def)
  have "g_out (foldl g_step g_s\<^sub>0 [Any]) Count = Some Odd"
   (is "?f Count [Any] = _") by (simp add: g_s\<^sub>0_def)
  moreover have
    "g_out (foldl g_step g_s\<^sub>0 (c_ipurge g_I g_D (g_D Count) [Any])) Count =
    Some Even"
   (is "?g Count [Any] = _") by (simp add: g_I_def g_s\<^sub>0_def)
  ultimately have "?f Count [Any] \<noteq> ?g Count [Any]" by simp
  thus "\<exists>x xs. ?f x xs \<noteq> ?g x xs" by blast
qed

theorem not_g_secure_implies_c_secure:
 "\<not> (g_secure (c_process g_step g_out g_s\<^sub>0) (c_dom g_D) \<longrightarrow>
  c_secure g_step g_out g_s\<^sub>0 g_I g_D)"
proof (simp, rule conjI, rule g_secure_counterexample)
qed (rule not_c_secure_counterexample)

theorem not_g_secure_implies_secure:
 "\<not> (g_secure (c_process g_step g_out g_s\<^sub>0) (c_dom g_D) \<longrightarrow>
  secure (c_process g_step g_out g_s\<^sub>0) g_I (c_dom g_D))"
proof (simp, rule conjI, rule g_secure_counterexample)
qed (rule notI, drule secure_implies_c_secure, erule contrapos_pp,
 rule not_c_secure_counterexample)

end
