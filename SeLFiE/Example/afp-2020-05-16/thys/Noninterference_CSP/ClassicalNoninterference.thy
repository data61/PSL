(*  Title:       Noninterference Security in Communicating Sequential Processes
    Author:      Pasquale Noce
                 Security Certification Specialist at Arjo Systems - Gep S.p.A.
                 pasquale dot noce dot lavoro at gmail dot com
                 pasquale dot noce at arjowiggins-it dot com
*)

section "CSP noninterference vs. classical noninterference"

theory ClassicalNoninterference
imports CSPNoninterference
begin

text \<open>
\null

The purpose of this section is to prove the equivalence of CSP noninterference security as defined
previously to the classical notion of noninterference security as formulated in \cite{R3} in the
case of processes representing deterministic state machines, henceforth briefly referred to as
\emph{classical processes}.

For clarity, all the constants and fact names defined in this section, with the possible exception
of main theorems, contain prefix \<open>c_\<close>.
\<close>


subsection "Classical noninterference"

text \<open>
Here below are the formalizations of the functions \emph{sources} and \emph{ipurge} defined in
\cite{R3}, as well as of the classical notion of noninterference security as stated ibid. for a
deterministic state machine in the general case of a possibly intransitive noninterference policy.

Observe that the function \emph{run} used in \emph{R3} is formalized as function
\<open>foldl step\<close>, where \<open>step\<close> is the state transition function of the machine.

\null
\<close>

primrec c_sources :: "('d \<times> 'd) set \<Rightarrow> ('a \<Rightarrow> 'd) \<Rightarrow> 'd \<Rightarrow> 'a list \<Rightarrow> 'd set" where
"c_sources _ _ u [] = {u}" |
"c_sources I D u (x # xs) = (if \<exists>v \<in> c_sources I D u xs. (D x, v) \<in> I
  then insert (D x) (c_sources I D u xs)
  else c_sources I D u xs)"

primrec c_ipurge :: "('d \<times> 'd) set \<Rightarrow> ('a \<Rightarrow> 'd) \<Rightarrow> 'd \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"c_ipurge _ _ _ [] = []" |
"c_ipurge I D u (x # xs) = (if D x \<in> c_sources I D u (x # xs)
  then x # c_ipurge I D u xs
  else c_ipurge I D u xs)"

definition c_secure ::
 "('s \<Rightarrow> 'a \<Rightarrow> 's) \<Rightarrow> ('s \<Rightarrow> 'a \<Rightarrow> 'o) \<Rightarrow> 's \<Rightarrow> ('d \<times> 'd) set \<Rightarrow> ('a \<Rightarrow> 'd) \<Rightarrow> bool" where
"c_secure step out s\<^sub>0 I D \<equiv>
  \<forall>x xs. out (foldl step s\<^sub>0 xs) x = out (foldl step s\<^sub>0 (c_ipurge I D (D x) xs)) x"

text \<open>
\null

In addition, the definitions are given of variants of functions \<open>c_sources\<close> and
\<open>c_ipurge\<close> accepting in input a set of security domains rather than a single domain, and then
some lemmas concerning them are demonstrated. These definitions and lemmas will turn out to be
useful in subsequent proofs.

\null
\<close>

primrec c_sources_aux :: "('d \<times> 'd) set \<Rightarrow> ('a \<Rightarrow> 'd) \<Rightarrow> 'd set \<Rightarrow> 'a list \<Rightarrow> 'd set" where
"c_sources_aux _ _ U [] = U" |
"c_sources_aux I D U (x # xs) = (if \<exists>v \<in> c_sources_aux I D U xs. (D x, v) \<in> I
  then insert (D x) (c_sources_aux I D U xs)
  else c_sources_aux I D U xs)"

primrec c_ipurge_aux :: "('d \<times> 'd) set \<Rightarrow> ('a \<Rightarrow> 'd) \<Rightarrow> 'd set \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"c_ipurge_aux _ _ _ [] = []" |
"c_ipurge_aux I D U (x # xs) = (if D x \<in> c_sources_aux I D U (x # xs)
  then x # c_ipurge_aux I D U xs
  else c_ipurge_aux I D U xs)"

lemma c_sources_aux_singleton_1: "c_sources_aux I D {u} xs = c_sources I D u xs"
by (induction xs, simp_all)

lemma c_ipurge_aux_singleton: "c_ipurge_aux I D {u} xs = c_ipurge I D u xs"
by (induction xs, simp_all add: c_sources_aux_singleton_1)

lemma c_sources_aux_singleton_2:
 "D x \<in> c_sources_aux I D U [x] = (D x \<in> U \<or> (\<exists>v \<in> U. (D x, v) \<in> I))"
by simp

lemma c_sources_aux_append:
 "c_sources_aux I D U (xs @ [x]) = (if D x \<in> c_sources_aux I D U [x]
    then c_sources_aux I D (insert (D x) U) xs
    else c_sources_aux I D U xs)"
by (induction xs, simp_all add: insert_absorb)

lemma c_ipurge_aux_append:
 "c_ipurge_aux I D U (xs @ [x]) = (if D x \<in> c_sources_aux I D U [x]
    then c_ipurge_aux I D (insert (D x) U) xs @ [x]
    else c_ipurge_aux I D U xs)"
by (induction xs, simp_all add: c_sources_aux_append)

text \<open>
\null

In what follows, a few useful lemmas are proven about functions \<open>c_sources\<close>, \<open>c_ipurge\<close>
and their relationships with functions \<open>sinks\<close>, \<open>ipurge_tr\<close>.

\null
\<close>

lemma c_sources_ipurge: "c_sources I D u (c_ipurge I D u xs) = c_sources I D u xs"
by (induction xs, simp_all)

lemma c_sources_append_1:
 "c_sources I D (D x) (xs @ [x]) = c_sources I D (D x) xs"
by (induction xs, simp_all)

lemma c_ipurge_append_1:
 "c_ipurge I D (D x) (xs @ [x]) = c_ipurge I D (D x) xs @ [x]"
by (induction xs, simp_all add: c_sources_append_1)

lemma c_sources_append_2:
 "(D x, u) \<notin> I \<Longrightarrow> c_sources I D u (xs @ [x]) = c_sources I D u xs"
by (induction xs, simp_all)

lemma c_ipurge_append_2:
 "refl I \<Longrightarrow> (D x, u) \<notin> I \<Longrightarrow> c_ipurge I D u (xs @ [x]) = c_ipurge I D u xs"
proof (induction xs, simp_all add: refl_on_def c_sources_append_2)
qed (rule notI, simp)

lemma c_sources_mono:
  assumes A: "c_sources I D u ys \<subseteq> c_sources I D u zs"
  shows "c_sources I D u (x # ys) \<subseteq> c_sources I D u (x # zs)"
proof (cases "\<exists>v \<in> c_sources I D u ys. (D x, v) \<in> I")
  assume B: "\<exists>v \<in> c_sources I D u ys. (D x, v) \<in> I"
  then obtain v where C: "v \<in> c_sources I D u ys" and D: "(D x, v) \<in> I" ..
  from A and C have "v \<in> c_sources I D u zs" ..
  with D have E: "\<exists>v \<in> c_sources I D u zs. (D x, v) \<in> I" ..
  have "insert (D x) (c_sources I D u ys) \<subseteq> insert (D x) (c_sources I D u zs)"
   using A by (rule insert_mono)
  moreover have "c_sources I D u (x # ys) = insert (D x) (c_sources I D u ys)"
   using B by simp
  moreover have "c_sources I D u (x # zs) = insert (D x) (c_sources I D u zs)"
   using E by simp
  ultimately show "c_sources I D u (x # ys) \<subseteq> c_sources I D u (x # zs)" by simp
next
  assume "\<not> (\<exists>v \<in> c_sources I D u ys. (D x, v) \<in> I)"
  hence "c_sources I D u (x # ys) = c_sources I D u ys" by simp
  hence "c_sources I D u (x # ys) \<subseteq> c_sources I D u zs" using A by simp
  moreover have "c_sources I D u zs \<subseteq> c_sources I D u (x # zs)"
   by (simp add: subset_insertI)
  ultimately show "c_sources I D u (x # ys) \<subseteq> c_sources I D u (x # zs)" by simp
qed

lemma c_sources_sinks [rule_format]:
  "D x \<notin> c_sources I D u (x # xs) \<longrightarrow> sinks I D (D x) (c_ipurge I D u xs) = {}"
proof (induction xs, simp, rule impI)
  fix x' xs
  assume A: "D x \<notin> c_sources I D u (x # xs) \<longrightarrow>
    sinks I D (D x) (c_ipurge I D u xs) = {}"
  assume B: "D x \<notin> c_sources I D u (x # x' # xs)"
  have "c_sources I D u xs \<subseteq> c_sources I D u (x' # xs)"
   by (simp add: subset_insertI)
  hence "c_sources I D u (x # xs) \<subseteq> c_sources I D u (x # x' # xs)"
   by (rule c_sources_mono)
  hence "D x \<notin> c_sources I D u (x # xs)" using B by (rule contra_subsetD)
  with A have C: "sinks I D (D x) (c_ipurge I D u xs) = {}" ..
  show "sinks I D (D x) (c_ipurge I D u (x' # xs)) = {}"
  proof (cases "D x' \<in> c_sources I D u (x' # xs)",
   simp_all only: c_ipurge.simps if_True if_False)
    assume D: "D x' \<in> c_sources I D u (x' # xs)"
    have "(D x, D x') \<notin> I"
    proof
      assume "(D x, D x') \<in> I"
      hence "\<exists>v \<in> c_sources I D u (x' # xs). (D x, v) \<in> I" using D ..
      hence "D x \<in> c_sources I D u (x # x' # xs)" by simp
      thus False using B by contradiction
    qed
    thus "sinks I D (D x) (x' # c_ipurge I D u xs) = {}"
     using C by (simp add: sinks_cons_nonint)
  next
    show "sinks I D (D x) (c_ipurge I D u xs) = {}" using C .
  qed
qed

lemmas c_ipurge_tr_ipurge = c_sources_sinks [THEN sinks_empty]

lemma c_ipurge_aux_ipurge_tr [rule_format]:
  assumes R: "refl I"
  shows "\<not> (\<exists>v \<in> sinks I D u ys. \<exists>w \<in> U. (v, w) \<in> I) \<longrightarrow>
    c_ipurge_aux I D U (xs @ ipurge_tr I D u ys) = c_ipurge_aux I D U (xs @ ys)"
proof (induction ys arbitrary: U rule: rev_induct, simp, rule impI)
  fix y ys U
  assume
    A: "\<And>U. \<not> (\<exists>v \<in> sinks I D u ys. \<exists>w \<in> U. (v, w) \<in> I) \<longrightarrow>
      c_ipurge_aux I D U (xs @ ipurge_tr I D u ys) =
      c_ipurge_aux I D U (xs @ ys)" and
    B: "\<not> (\<exists>v \<in> sinks I D u (ys @ [y]). \<exists>w \<in> U. (v, w) \<in> I)"
  have C: "\<not> (\<exists>v \<in> sinks I D u ys. \<exists>w \<in> U. (v, w) \<in> I)"
  proof (rule notI, (erule bexE)+)
    fix v w
    assume "(v, w) \<in> I" and "w \<in> U"
    hence "\<exists>w \<in> U. (v, w) \<in> I" ..
    moreover assume "v \<in> sinks I D u ys"
    hence "v \<in> sinks I D u (ys @ [y])" by simp
    ultimately have "\<exists>v \<in> sinks I D u (ys @ [y]). \<exists>w \<in> U. (v, w) \<in> I" ..
    thus False using B by contradiction
  qed
  show "c_ipurge_aux I D U (xs @ ipurge_tr I D u (ys @ [y])) =
    c_ipurge_aux I D U (xs @ ys @ [y])"
  proof (cases "D y \<in> c_sources_aux I D U [y]",
   case_tac [!] "D y \<in> sinks I D u (ys @ [y])",
   simp_all (no_asm_simp) only: ipurge_tr.simps append_assoc [symmetric]
   c_ipurge_aux_append append_same_eq if_True if_False)
    assume D: "D y \<in> sinks I D u (ys @ [y])"
    assume "D y \<in> c_sources_aux I D U [y]"
    hence "D y \<in> U \<or> (\<exists>w \<in> U. (D y, w) \<in> I)"
     by (simp only: c_sources_aux_singleton_2)
    moreover {
      have "(D y, D y) \<in> I" using R by (simp add: refl_on_def)
      moreover assume "D y \<in> U"
      ultimately have "\<exists>w \<in> U. (D y, w) \<in> I" ..
      hence "\<exists>v \<in> sinks I D u (ys @ [y]). \<exists>w \<in> U. (v, w) \<in> I" using D ..
    }
    moreover {
      assume "\<exists>w \<in> U. (D y, w) \<in> I"
      hence "\<exists>v \<in> sinks I D u (ys @ [y]). \<exists>w \<in> U. (v, w) \<in> I" using D ..
    }
    ultimately have "\<exists>v \<in> sinks I D u (ys @ [y]). \<exists>w \<in> U. (v, w) \<in> I" by blast
    thus "c_ipurge_aux I D U (xs @ ipurge_tr I D u ys) =
      c_ipurge_aux I D (insert (D y) U) (xs @ ys) @ [y]"
     using B by contradiction
  next
    assume D: "D y \<notin> sinks I D u (ys @ [y])"
    have "\<not> (\<exists>v \<in> sinks I D u ys. \<exists>w \<in> insert (D y) U. (v, w) \<in> I) \<longrightarrow>
      c_ipurge_aux I D (insert (D y) U) (xs @ ipurge_tr I D u ys) =
      c_ipurge_aux I D (insert (D y) U) (xs @ ys)"
     using A .
    moreover have "\<not> (\<exists>v \<in> sinks I D u ys. \<exists>w \<in> insert (D y) U. (v, w) \<in> I)"
    proof (rule notI, (erule bexE)+, simp, erule disjE, simp)
      fix v
      assume "(v, D y) \<in> I" and "v \<in> sinks I D u ys"
      hence "\<exists>v \<in> sinks I D u ys. (v, D y) \<in> I" ..
      hence "D y \<in> sinks I D u (ys @ [y])" by simp
      thus False using D by contradiction
    next
      fix v w
      assume "(v, w) \<in> I" and "w \<in> U"
      hence "\<exists>w \<in> U. (v, w) \<in> I" ..
      moreover assume "v \<in> sinks I D u ys"
      ultimately have "\<exists>v \<in> sinks I D u ys. \<exists>w \<in> U. (v, w) \<in> I" ..
      thus False using C by contradiction
    qed
    ultimately show "c_ipurge_aux I D (insert (D y) U) (xs @ ipurge_tr I D u ys)
      = c_ipurge_aux I D (insert (D y) U) (xs @ ys)" ..
  next
    have "\<not> (\<exists>v \<in> sinks I D u ys. \<exists>w \<in> U. (v, w) \<in> I) \<longrightarrow>
      c_ipurge_aux I D U (xs @ ipurge_tr I D u ys) = c_ipurge_aux I D U (xs @ ys)"
     using A .
    thus "c_ipurge_aux I D U (xs @ ipurge_tr I D u ys) =
      c_ipurge_aux I D U (xs @ ys)"
     using C ..
  next
    have "\<not> (\<exists>v \<in> sinks I D u ys. \<exists>w \<in> U. (v, w) \<in> I) \<longrightarrow>
      c_ipurge_aux I D U (xs @ ipurge_tr I D u ys) = c_ipurge_aux I D U (xs @ ys)"
     using A .
    thus "c_ipurge_aux I D U (xs @ ipurge_tr I D u ys) =
      c_ipurge_aux I D U (xs @ ys)"
     using C ..
  qed
qed

lemma c_ipurge_ipurge_tr:
  assumes R: "refl I" and D: "\<not> (\<exists>v \<in> sinks I D u ys. (v, u') \<in> I)"
  shows "c_ipurge I D u' (xs @ ipurge_tr I D u ys) = c_ipurge I D u' (xs @ ys)"
proof -
  have "\<not> (\<exists>v \<in> sinks I D u ys. \<exists>w \<in> {u'}. (v, w) \<in> I)" using D by simp
  with R have "c_ipurge_aux I D {u'} (xs @ ipurge_tr I D u ys) =
    c_ipurge_aux I D {u'} (xs @ ys)"
   by (rule c_ipurge_aux_ipurge_tr)
  thus ?thesis by (simp add: c_ipurge_aux_singleton)
qed


subsection "Classical processes"

text \<open>
The deterministic state machines used as model of computation in the classical theory of
noninterference security, as expounded in \cite{R3}, have the property that each action produces an
output. Hence, it is natural to take as alphabet of a classical process the universe of the pairs
\<open>(x, p)\<close>, where \<open>x\<close> is an action and \<open>p\<close> an output. For any state \<open>s\<close>,
such an event \<open>(x, p)\<close> may occur just in case \<open>p\<close> matches the output produced by
\<open>x\<close> in \<open>s\<close>.

Therefore, a trace of a classical process can be defined as an event list \<open>xps\<close> such that for
each item \<open>(x, p)\<close>, \<open>p\<close> is equal to the output produced by \<open>x\<close> in the state
resulting from the previous actions in \<open>xps\<close>. Furthermore, for each trace \<open>xps\<close>, the
refusals set associated to \<open>xps\<close> is comprised of any set of pairs \<open>(x, p)\<close> such that
\<open>p\<close> is different from the output produced by \<open>x\<close> in the state resulting from the actions
in \<open>xps\<close>.

In accordance with the previous considerations, an inductive definition is formulated here below for
the failures set \<open>c_failures step out s\<^sub>0\<close> corresponding to the deterministic state machine
with state transition function \<open>step\<close>, output function \<open>out\<close>, and initial state
\<open>s\<^sub>0\<close>. Then, the classical process \<open>c_process step out s\<^sub>0\<close> representing this machine is
defined as the process having \<open>c_failures step out s\<^sub>0\<close> as failures set and the empty set as
divergences set.

\null
\<close>

inductive_set c_failures ::
 "('s \<Rightarrow> 'a \<Rightarrow> 's) \<Rightarrow> ('s \<Rightarrow> 'a \<Rightarrow> 'o) \<Rightarrow> 's \<Rightarrow> ('a \<times> 'o) failure set"
for step :: "'s \<Rightarrow> 'a \<Rightarrow> 's" and out :: "'s \<Rightarrow> 'a \<Rightarrow> 'o" and s\<^sub>0 :: 's where
R0: "([], {(x, p). p \<noteq> out s\<^sub>0 x}) \<in> c_failures step out s\<^sub>0" |
R1: "\<lbrakk>(xps, _) \<in> c_failures step out s\<^sub>0; s = foldl step s\<^sub>0 (map fst xps)\<rbrakk> \<Longrightarrow>
     (xps @ [(x, out s x)], {(y, p). p \<noteq> out (step s x) y}) \<in> c_failures step out s\<^sub>0" |
R2: "\<lbrakk>(xps, Y) \<in> c_failures step out s\<^sub>0; X \<subseteq> Y\<rbrakk> \<Longrightarrow>
     (xps, X) \<in> c_failures step out s\<^sub>0"

definition c_process ::
 "('s \<Rightarrow> 'a \<Rightarrow> 's) \<Rightarrow> ('s \<Rightarrow> 'a \<Rightarrow> 'o) \<Rightarrow> 's \<Rightarrow> ('a \<times> 'o) process" where
"c_process step out s\<^sub>0 \<equiv> Abs_process (c_failures step out s\<^sub>0, {})"

text \<open>
\null

In what follows, the fact that classical processes are indeed processes is proven as a theorem.

\null
\<close>

lemma c_process_prop_1 [simp]: "process_prop_1 (c_failures step out s\<^sub>0, {})"
proof (simp add: process_prop_1_def)
  have "([], {(x, p). p \<noteq> out s\<^sub>0 x}) \<in> c_failures step out s\<^sub>0" by (rule R0)
  moreover have "{} \<subseteq> {(x, p). p \<noteq> out s\<^sub>0 x}" ..
  ultimately show "([], {}) \<in> c_failures step out s\<^sub>0" by (rule R2)
qed

lemma c_process_prop_2 [simp]: "process_prop_2 (c_failures step out s\<^sub>0, {})"
proof (simp only: process_prop_2_def fst_conv, (rule allI)+, rule impI)
  fix xps xp X
  assume "(xps @ [xp], X) \<in> c_failures step out s\<^sub>0"
  hence "(butlast (xps @ [xp]), {}) \<in> c_failures step out s\<^sub>0"
  proof (rule c_failures.induct
   [where P = "\<lambda>xps X. (butlast xps, {}) \<in> c_failures step out s\<^sub>0"], simp_all)
    have "([], {(x, p). p \<noteq> out s\<^sub>0 x}) \<in> c_failures step out s\<^sub>0" by (rule R0)
    moreover have "{} \<subseteq> {(x, p). p \<noteq> out s\<^sub>0 x}" ..
    ultimately show "([], {}) \<in> c_failures step out s\<^sub>0" by (rule R2)
  next
    fix xps' X'
    assume "(xps', X') \<in> c_failures step out s\<^sub>0"
    moreover have "{} \<subseteq> X'" ..
    ultimately show "(xps', {}) \<in> c_failures step out s\<^sub>0" by (rule R2)
  qed
  thus "(xps, {}) \<in> c_failures step out s\<^sub>0" by simp
qed

lemma c_process_prop_3 [simp]: "process_prop_3 (c_failures step out s\<^sub>0, {})"
by (simp only: process_prop_3_def fst_conv, (rule allI)+, rule impI, erule conjE, rule R2)

lemma c_process_prop_4 [simp]: "process_prop_4 (c_failures step out s\<^sub>0, {})"
proof (simp only: process_prop_4_def fst_conv, (rule allI)+, rule impI)
  fix xps xp X
  assume "(xps, X) \<in> c_failures step out s\<^sub>0"
  thus "(xps @ [xp], {}) \<in> c_failures step out s\<^sub>0 \<or>
    (xps, insert xp X) \<in> c_failures step out s\<^sub>0"
  proof (case_tac xp, rule c_failures.induct)
    fix x p
    assume A: "xp = (x, p)"
    have B: "([], {(x, p). p \<noteq> out s\<^sub>0 x}) \<in> c_failures step out s\<^sub>0"
     (is "(_, ?X) \<in> _") by (rule R0)
    show "([] @ [xp], {}) \<in> c_failures step out s\<^sub>0 \<or> ([], insert xp ?X)
      \<in> c_failures step out s\<^sub>0"
    proof (cases "p = out s\<^sub>0 x")
      assume C: "p = out s\<^sub>0 x"
      have "s\<^sub>0 = foldl step s\<^sub>0 (map fst [])" by simp
      with B have "([] @ [(x, out s\<^sub>0 x)], {(y, p). p \<noteq> out (step s\<^sub>0 x) y})
        \<in> c_failures step out s\<^sub>0"
       (is "(_, ?Y) \<in> _") by (rule R1)
      hence "([] @ [xp], ?Y) \<in> c_failures step out s\<^sub>0" using A and C by simp
      moreover have "{} \<subseteq> ?Y" ..
      ultimately have "([] @ [xp], {}) \<in> c_failures step out s\<^sub>0" by (rule R2)
      thus ?thesis ..
    next
      assume "p \<noteq> out s\<^sub>0 x"
      hence "xp \<in> ?X" using A by simp
      hence "insert xp ?X = ?X" by (rule insert_absorb)
      hence "([], insert xp ?X) \<in> c_failures step out s\<^sub>0" using B by simp
      thus ?thesis ..
    qed
  next
    fix x p xps' X' s x'
    let ?s = "step s x'"
    assume A: "xp = (x, p)"
    assume "(xps', X') \<in> c_failures step out s\<^sub>0" and
      S: "s = foldl step s\<^sub>0 (map fst xps')"
    hence B: "(xps' @ [(x', out s x')], {(y, p). p \<noteq> out ?s y})
      \<in> c_failures step out s\<^sub>0"
     (is "(?xps, ?X) \<in> _") by (rule R1)
    show "(?xps @ [xp], {}) \<in> c_failures step out s\<^sub>0 \<or> (?xps, insert xp ?X)
      \<in> c_failures step out s\<^sub>0"
    proof (cases "p = out ?s x")
      assume C: "p = out ?s x"
      have "?s = foldl step s\<^sub>0 (map fst ?xps)" using S by simp
      with B have "(?xps @ [(x, out ?s x)], {(y, p). p \<noteq> out (step ?s x) y})
        \<in> c_failures step out s\<^sub>0"
       (is "(_, ?Y) \<in> _") by (rule R1)
      hence "(?xps @ [xp], ?Y) \<in> c_failures step out s\<^sub>0" using A and C by simp
      moreover have "{} \<subseteq> ?Y" ..
      ultimately have "(?xps @ [xp], {}) \<in> c_failures step out s\<^sub>0" by (rule R2)
      thus ?thesis ..
    next
      assume "p \<noteq> out ?s x"
      hence "xp \<in> ?X" using A by simp
      hence "insert xp ?X = ?X" by (rule insert_absorb)
      hence "(?xps, insert xp ?X) \<in> c_failures step out s\<^sub>0" using B by simp
      thus ?thesis ..
    qed
  next
    fix xps' X' Y
    assume
      "(xps' @ [xp], {}) \<in> c_failures step out s\<^sub>0 \<or>
       (xps', insert xp Y) \<in> c_failures step out s\<^sub>0" (is "?A \<or> ?B") and
      "X' \<subseteq> Y"
    show "(xps' @ [xp], {}) \<in> c_failures step out s\<^sub>0 \<or> (xps', insert xp X')
      \<in> c_failures step out s\<^sub>0"
    using \<open>?A \<or> ?B\<close>
    proof (rule disjE)
      assume ?A
      thus ?thesis ..
    next
      assume ?B
      moreover have "insert xp X' \<subseteq> insert xp Y" using \<open>X' \<subseteq> Y\<close>
       by (rule insert_mono)
      ultimately have "(xps', insert xp X') \<in> c_failures step out s\<^sub>0" by (rule R2)
      thus ?thesis ..
    qed
  qed
qed

lemma c_process_prop_5 [simp]: "process_prop_5 (F, {})"
by (simp add: process_prop_5_def)

lemma c_process_prop_6 [simp]: "process_prop_6 (F, {})"
by (simp add: process_prop_6_def)

theorem c_process_process: "(c_failures step out s\<^sub>0, {}) \<in> process_set"
by (simp add: process_set_def)

text \<open>
\null

The continuation of this section is dedicated to the proof of a few lemmas on the properties of
classical processes, particularly on the application to them of the generic functions acting on
processes defined previously, and culminates in the theorem stating that classical processes are
deterministic. Since they are intended to be a representation of deterministic state machines as
processes, this result provides an essential confirmation of the correctness of such correspondence.

\null
\<close>

lemma c_failures_last [rule_format]:
 "(xps, X) \<in> c_failures step out s\<^sub>0 \<Longrightarrow> xps \<noteq> [] \<longrightarrow>
  snd (last xps) = out (foldl step s\<^sub>0 (butlast (map fst xps))) (last (map fst xps))"
by (erule c_failures.induct, simp_all)

lemma c_failures_ref:
 "(xps, X) \<in> c_failures step out s\<^sub>0 \<Longrightarrow>
  X \<subseteq> {(x, p). p \<noteq> out (foldl step s\<^sub>0 (map fst xps)) x}"
by (erule c_failures.induct, simp_all)

lemma c_failures_failures: "failures (c_process step out s\<^sub>0) = c_failures step out s\<^sub>0"
by (simp add: failures_def c_process_def c_process_process Abs_process_inverse)

lemma c_futures_failures:
 "(yps, Y) \<in> futures (c_process step out s\<^sub>0) xps =
  ((xps @ yps, Y) \<in> c_failures step out s\<^sub>0)"
by (simp add: futures_def failures_def c_process_def c_process_process Abs_process_inverse)

lemma c_traces:
 "xps \<in> traces (c_process step out s\<^sub>0) = (\<exists>X. (xps, X) \<in> c_failures step out s\<^sub>0)"
by (simp add: traces_def failures_def Domain_iff c_process_def c_process_process
 Abs_process_inverse)

lemma c_refusals:
 "X \<in> refusals (c_process step out s\<^sub>0) xps = ((xps, X) \<in> c_failures step out s\<^sub>0)"
by (simp add: refusals_def c_failures_failures)

lemma c_next_events:
 "xp \<in> next_events (c_process step out s\<^sub>0) xps =
  (\<exists>X. (xps @ [xp], X) \<in> c_failures step out s\<^sub>0)"
by (simp add: next_events_def c_traces)

lemma c_traces_failures:
 "xps \<in> traces (c_process step out s\<^sub>0) \<Longrightarrow>
  (xps, {(x, p). p \<noteq> out (foldl step s\<^sub>0 (map fst xps)) x}) \<in> c_failures step out s\<^sub>0"
proof (simp add: c_traces, erule exE, rule rev_cases [of xps],
 simp_all add: R0 split_paired_all)
  fix yps y p Y
  assume A: "(yps @ [(y, p)], Y) \<in> c_failures step out s\<^sub>0"
  let ?s = "foldl step s\<^sub>0 (map fst yps)"
  let ?ys' = "map fst (yps @ [(y, p)])"
  have "(yps @ [(y, p)], Y) \<in> failures (c_process step out s\<^sub>0)"
   using A by (simp add: c_failures_failures)
  hence "(yps, {}) \<in> failures (c_process step out s\<^sub>0)" by (rule process_rule_2)
  hence "(yps, {}) \<in> c_failures step out s\<^sub>0" by (simp add: c_failures_failures)
  moreover have "?s = foldl step s\<^sub>0 (map fst yps)" by simp
  ultimately have "(yps @ [(y, out ?s y)], {(x, p). p \<noteq> out (step ?s y) x})
    \<in> c_failures step out s\<^sub>0"
   by (rule R1)
  moreover have "yps @ [(y, p)] \<noteq> []" by simp
  with A have "snd (last (yps @ [(y, p)])) =
    out (foldl step s\<^sub>0 (butlast ?ys')) (last ?ys')"
   by (rule c_failures_last)
  hence "p = out ?s y" by simp
  ultimately show "(yps @ [(y, p)], {(x, p). p \<noteq> out (step ?s y) x})
    \<in> c_failures step out s\<^sub>0"
   by simp
qed

theorem c_process_deterministic: "deterministic (c_process step out s\<^sub>0)"
proof (simp add: deterministic_def c_refusals c_next_events set_eq_iff, rule ballI,
 rule allI)
  fix xps X
  assume T: "xps \<in> traces (c_process step out s\<^sub>0)"
  let ?s = "foldl step s\<^sub>0 (map fst xps)"
  show "(xps, X) \<in> c_failures step out s\<^sub>0 =
    (\<forall>x p. (x, p) \<in> X \<longrightarrow> (\<forall>X. (xps @ [(x, p)], X) \<notin> c_failures step out s\<^sub>0))"
   (is "?P = ?Q")
  proof (rule iffI, (rule allI)+, rule impI, rule allI, rule notI)
    fix x p Y
    let ?xs' = "map fst (xps @ [(x, p)])"
    assume ?P
    hence "X \<subseteq> {(x, p). p \<noteq> out ?s x}" (is "_ \<subseteq> ?X'") by (rule c_failures_ref)
    moreover assume "(x, p) \<in> X"
    ultimately have "(x, p) \<in> ?X'" ..
    hence A: "p \<noteq> out ?s x" by simp
    assume "(xps @ [(x, p)], Y) \<in> c_failures step out s\<^sub>0"
    moreover have "xps @ [(x, p)] \<noteq> []" by simp
    ultimately have "snd (last (xps @ [(x, p)])) =
      out (foldl step s\<^sub>0 (butlast ?xs')) (last ?xs')"
     by (rule c_failures_last)
    hence "p = out ?s x" by simp
    thus False using A by contradiction
  next
    assume ?Q
    have A: "(xps, {(x, p). p \<noteq> out ?s x}) \<in> c_failures step out s\<^sub>0"
     using T by (rule c_traces_failures)
    moreover have "X \<subseteq> {(x, p). p \<noteq> out ?s x}"
    proof (rule subsetI, simp add: split_paired_all, rule notI)
      fix x p
      assume "(x, p) \<in> X" and "p = out ?s x"
      hence "(xps @ [(x, out ?s x)], {(y, p). p \<noteq> out (step ?s x) y})
        \<notin> c_failures step out s\<^sub>0"
       using \<open>?Q\<close> by simp
      moreover have "?s = foldl step s\<^sub>0 (map fst xps)" by simp
      with A have "(xps @ [(x, out ?s x)], {(y, p). p \<noteq> out (step ?s x) y})
        \<in> c_failures step out s\<^sub>0"
       by (rule R1)
      ultimately show False by contradiction
    qed
    ultimately show ?P by (rule R2)
  qed
qed


subsection "Traces in classical processes"

text \<open>
Here below is the definition of function \<open>c_tr\<close>, where \<open>c_tr step out s xs\<close> is the
trace of classical process \<open>c_process step out s\<close> corresponding to the trace \<open>xs\<close> of
the associated deterministic state machine. Moreover, some useful lemmas are proven about this
function.

\null
\<close>

function c_tr :: "('s \<Rightarrow> 'a \<Rightarrow> 's) \<Rightarrow> ('s \<Rightarrow> 'a \<Rightarrow> 'o) \<Rightarrow> 's \<Rightarrow> 'a list \<Rightarrow> ('a \<times> 'o) list" where
"c_tr _ _ _ [] = []" |
"c_tr step out s (xs @ [x]) = c_tr step out s xs @ [(x, out (foldl step s xs) x)]"
proof (atomize_elim, simp_all add: split_paired_all)
qed (rule rev_cases, rule disjI1, assumption, simp)
termination by lexicographic_order

lemma c_tr_length: "length (c_tr step out s xs) = length xs"
by (rule rev_induct, simp_all)

lemma c_tr_map: "map fst (c_tr step out s xs) = xs"
by (rule rev_induct, simp_all)

lemma c_tr_singleton: "c_tr step out s [x] = [(x, out s x)]"
proof -
  have "c_tr step out s [x] = c_tr step out s ([] @ [x])" by simp
  also have "\<dots> = c_tr step out s [] @ [(x, out (foldl step s []) x)]"
   by (rule c_tr.simps(2))
  also have "\<dots> = [(x, out s x)]" by simp
  finally show ?thesis .
qed

lemma c_tr_append:
 "c_tr step out s (xs @ ys) = c_tr step out s xs @ c_tr step out (foldl step s xs) ys"
proof (rule_tac xs = ys in rev_induct, simp, subst append_assoc [symmetric])
qed (simp del: append_assoc)

lemma c_tr_hd_tl:
  assumes A: "xs \<noteq> []"
  shows "c_tr step out s xs =
    (hd xs, out s (hd xs)) # c_tr step out (step s (hd xs)) (tl xs)"
proof -
  let ?s = "foldl step s [hd xs]"
  have "c_tr step out s ([hd xs] @ tl xs) =
    c_tr step out s [hd xs] @ c_tr step out ?s (tl xs)"
   by (rule c_tr_append)
  moreover have "[hd xs] @ tl xs = xs" using A by simp
  ultimately have "c_tr step out s xs =
    c_tr step out s [hd xs] @ c_tr step out ?s (tl xs)"
   by simp
  moreover have "c_tr step out s [hd xs] = [(hd xs, out s (hd xs))]"
   by (simp add: c_tr_singleton)
  ultimately show ?thesis by simp
qed

lemma c_failures_tr:
 "(xps, X) \<in> c_failures step out s\<^sub>0 \<Longrightarrow> xps = c_tr step out s\<^sub>0 (map fst xps)"
by (erule c_failures.induct, simp_all)

lemma c_futures_tr:
  assumes A: "(yps, Y) \<in> futures (c_process step out s\<^sub>0) xps"
  shows "yps = c_tr step out (foldl step s\<^sub>0 (map fst xps)) (map fst yps)"
proof -
  have B: "(xps @ yps, Y) \<in> c_failures step out s\<^sub>0"
   using A by (simp add: c_futures_failures)
  hence "xps @ yps = c_tr step out s\<^sub>0 (map fst (xps @ yps))"
   by (rule c_failures_tr)
  hence "xps @ yps = c_tr step out s\<^sub>0 (map fst xps) @
    c_tr step out (foldl step s\<^sub>0 (map fst xps)) (map fst yps)"
   by (simp add: c_tr_append)
  moreover have "(xps @ yps, Y) \<in> failures (c_process step out s\<^sub>0)"
   using B by (simp add: c_failures_failures)
  hence "(xps, {}) \<in> failures (c_process step out s\<^sub>0)"
   by (rule process_rule_2_failures)
  hence "(xps, {}) \<in> c_failures step out s\<^sub>0" by (simp add: c_failures_failures)
  hence "xps = c_tr step out s\<^sub>0 (map fst xps)" by (rule c_failures_tr)
  ultimately show ?thesis by simp
qed

lemma c_tr_failures:
 "(c_tr step out s\<^sub>0 xs, {(x, p). p \<noteq> out (foldl step s\<^sub>0 xs) x})
  \<in> c_failures step out s\<^sub>0"
proof (rule rev_induct, simp_all, rule R0)
  fix x xs
  let ?s = "foldl step s\<^sub>0 (map fst (c_tr step out s\<^sub>0 xs))"
  assume "(c_tr step out s\<^sub>0 xs, {(x, p). p \<noteq> out (foldl step s\<^sub>0 xs) x})
    \<in> c_failures step out s\<^sub>0"
  moreover have "?s = foldl step s\<^sub>0 (map fst (c_tr step out s\<^sub>0 xs))" by simp
  ultimately have "(c_tr step out s\<^sub>0 xs @ [(x, out ?s x)],
    {(y, p). p \<noteq> out (step ?s x) y}) \<in> c_failures step out s\<^sub>0"
   by (rule R1)
  moreover have "?s = foldl step s\<^sub>0 xs" by (simp add: c_tr_map)
  ultimately show "(c_tr step out s\<^sub>0 xs @ [(x, out (foldl step s\<^sub>0 xs) x)],
   {(y, p). p \<noteq> out (step (foldl step s\<^sub>0 xs) x) y}) \<in> c_failures step out s\<^sub>0" by simp
qed

lemma c_tr_futures:
 "(c_tr step out (foldl step s\<^sub>0 xs) ys,
  {(x, p). p \<noteq> out (foldl step (foldl step s\<^sub>0 xs) ys) x})
  \<in> futures (c_process step out s\<^sub>0) (c_tr step out s\<^sub>0 xs)"
proof (simp add: c_futures_failures)
  have "(c_tr step out s\<^sub>0 (xs @ ys), {(x, p). p \<noteq> out (foldl step s\<^sub>0 (xs @ ys)) x})
    \<in> c_failures step out s\<^sub>0"
   by (rule c_tr_failures)
  moreover have "c_tr step out s\<^sub>0 (xs @ ys) =
    c_tr step out s\<^sub>0 xs @ c_tr step out (foldl step s\<^sub>0 xs) ys"
   by (rule c_tr_append)
  ultimately show "(c_tr step out s\<^sub>0 xs @ c_tr step out (foldl step s\<^sub>0 xs) ys,
    {(x, p). p \<noteq> out (foldl step (foldl step s\<^sub>0 xs) ys) x})
    \<in> c_failures step out s\<^sub>0"
   by simp
qed


subsection "Noninterference in classical processes"

text \<open>
Given a mapping \<open>D\<close> of the actions of a deterministic state machine into their security
domains, it is natural to map each event \<open>(x, p)\<close> of the corresponding classical process
into the domain \<open>D x\<close> of action \<open>x\<close>.

Such mapping of events into domains, formalized as function \<open>c_dom D\<close> in the continuation,
ensures that the same noninterference policy applying to a deterministic state machine be applicable
to the associated classical process as well. This is the simplest, and thus preferable way to
construct a policy for the process such as to be isomorphic to the one assigned for the machine, as
required in order to prove the equivalence of CSP noninterference security to the classical notion
in the case of classical processes.

In what follows, function \<open>c_dom\<close> will be used in the proof of some useful lemmas concerning
the application of functions \<open>sinks\<close>, \<open>ipurge_tr\<close>, \<open>c_sources\<close>, \<open>c_ipurge\<close>
from noninterference theory to the traces of classical processes, constructed by means of function
\<open>c_tr\<close>.

\null
\<close>

definition c_dom :: "('a \<Rightarrow> 'd) \<Rightarrow> ('a \<times> 'o) \<Rightarrow> 'd" where
"c_dom D xp \<equiv> D (fst xp)"

lemma c_dom_sources:
 "c_sources I (c_dom D) u xps = c_sources I D u (map fst xps)"
by (induction xps, simp_all add: c_dom_def)

lemma c_dom_sinks: "sinks I (c_dom D) u xps = sinks I D u (map fst xps)"
by (induction xps rule: rev_induct, simp_all add: c_dom_def)

lemma c_tr_sources:
 "c_sources I (c_dom D) u (c_tr step out s xs) = c_sources I D u xs"
by (simp add: c_dom_sources c_tr_map)

lemma c_tr_sinks: "sinks I (c_dom D) u (c_tr step out s xs) = sinks I D u xs"
by (simp add: c_dom_sinks c_tr_map)

lemma c_tr_ipurge:
 "c_ipurge I (c_dom D) u (c_tr step out s (c_ipurge I D u xs)) =
  c_tr step out s (c_ipurge I D u xs)"
proof (induction xs arbitrary: s, simp)
  fix x xs s
  assume A: "\<And>s. c_ipurge I (c_dom D) u (c_tr step out s (c_ipurge I D u xs)) =
    c_tr step out s (c_ipurge I D u xs)"
  show "c_ipurge I (c_dom D) u (c_tr step out s (c_ipurge I D u (x # xs))) =
    c_tr step out s (c_ipurge I D u (x # xs))"
  proof (cases "D x \<in> c_sources I D u (x # xs)", simp_all del: c_sources.simps)
    have B: "c_tr step out s (x # c_ipurge I D u xs) =
      (x, out s x) # c_tr step out (step s x) (c_ipurge I D u xs)"
     by (simp add: c_tr_hd_tl)
    assume C: "D x \<in> c_sources I D u (x # xs)"
    hence "D x \<in> c_sources I D u (c_ipurge I D u (x # xs))"
     by (subst c_sources_ipurge)
    hence "D x \<in> c_sources I (c_dom D) u (c_tr step out s (x # c_ipurge I D u xs))"
     using C by (simp add: c_tr_sources)
    hence "c_dom D (x, out s x) \<in> c_sources I (c_dom D) u
      ((x, out s x) # c_tr step out (step s x) (c_ipurge I D u xs))"
     using B by (simp add: c_dom_def)
    hence "c_ipurge I (c_dom D) u (c_tr step out s (x # c_ipurge I D u xs)) = 
      (x, out s x) # c_ipurge I (c_dom D) u
      (c_tr step out (step s x) (c_ipurge I D u xs))"
     using B by simp
    moreover have "c_ipurge I (c_dom D) u
      (c_tr step out (step s x) (c_ipurge I D u xs)) =
      c_tr step out (step s x) (c_ipurge I D u xs)"
     using A .
    ultimately show "c_ipurge I (c_dom D) u
      (c_tr step out s (x # c_ipurge I D u xs)) =
      c_tr step out s (x # c_ipurge I D u xs)"
     using B by simp
  next
    show "c_ipurge I (c_dom D) u (c_tr step out s (c_ipurge I D u xs)) =
      c_tr step out s (c_ipurge I D u xs)"
     using A .
  qed
qed

lemma c_tr_ipurge_tr_1 [rule_format]:
 "(\<forall>n \<in> {..<length xs}. D (xs ! n) \<notin> sinks I D u (take (Suc n) xs) \<longrightarrow>
  out (foldl step s (ipurge_tr I D u (take n xs))) (xs ! n) =
  out (foldl step s (take n xs)) (xs ! n)) \<longrightarrow>
  ipurge_tr I (c_dom D) u (c_tr step out s xs) = c_tr step out s (ipurge_tr I D u xs)"
proof (induction xs rule: rev_induct, simp, rule impI)
  fix x xs
  assume "(\<forall>n \<in> {..<length xs}.
    D (xs ! n) \<notin> sinks I D u (take (Suc n) xs) \<longrightarrow>
    out (foldl step s (ipurge_tr I D u (take n xs))) (xs ! n) =
    out (foldl step s (take n xs)) (xs ! n)) \<longrightarrow>
    ipurge_tr I (c_dom D) u (c_tr step out s xs) =
    c_tr step out s (ipurge_tr I D u xs)"
  moreover assume A: "\<forall>n \<in> {..<length (xs @ [x])}.
    D ((xs @ [x]) ! n) \<notin> sinks I D u (take (Suc n) (xs @ [x])) \<longrightarrow>
    out (foldl step s (ipurge_tr I D u (take n (xs @ [x])))) ((xs @ [x]) ! n) =
    out (foldl step s (take n (xs @ [x]))) ((xs @ [x]) ! n)"
  have "\<forall>n \<in> {..<length xs}.
    D (xs ! n) \<notin> sinks I D u (take (Suc n) xs) \<longrightarrow>
    out (foldl step s (ipurge_tr I D u (take n xs))) (xs ! n) =
    out (foldl step s (take n xs)) (xs ! n)"
  proof (rule ballI, rule impI)
    fix n
    assume B: "n \<in> {..<length xs}"
    hence "n \<in> {..<length (xs @ [x])}" by simp
    with A have "D ((xs @ [x]) ! n) \<notin> sinks I D u (take (Suc n) (xs @ [x])) \<longrightarrow>
      out (foldl step s (ipurge_tr I D u (take n (xs @ [x])))) ((xs @ [x]) ! n) =
      out (foldl step s (take n (xs @ [x]))) ((xs @ [x]) ! n)" ..
    hence "D (xs ! n) \<notin> sinks I D u (take (Suc n) xs) \<longrightarrow>
      out (foldl step s (ipurge_tr I D u (take n xs))) (xs ! n) =
      out (foldl step s (take n xs)) (xs ! n)"
     using B by (simp add: nth_append)
    moreover assume "D (xs ! n) \<notin> sinks I D u (take (Suc n) xs)"
    ultimately show "out (foldl step s (ipurge_tr I D u (take n xs))) (xs ! n) =
      out (foldl step s (take n xs)) (xs ! n)" ..
  qed
  ultimately have C: "ipurge_tr I (c_dom D) u (c_tr step out s xs) =
    c_tr step out s (ipurge_tr I D u xs)" ..
  show "ipurge_tr I (c_dom D) u (c_tr step out s (xs @ [x])) =
    c_tr step out s (ipurge_tr I D u (xs @ [x]))"
  proof (cases "D x \<in> sinks I D u (xs @ [x])")
    case True
    then have "D x \<in> sinks I (c_dom D) u
      (c_tr step out s (xs @ [x]))"
     by (subst c_tr_sinks)
    hence "c_dom D (x, out (foldl step s xs) x)
      \<in> sinks I (c_dom D) u (c_tr step out s xs @ [(x, out (foldl step s xs) x)])"
     by (simp add: c_dom_def)
    with True show ?thesis using C by simp
  next
    case False
    then have "D x \<notin> sinks I (c_dom D) u
      (c_tr step out s (xs @ [x]))"
     by (subst c_tr_sinks)
    hence "c_dom D (x, out (foldl step s xs) x)
      \<notin> sinks I (c_dom D) u (c_tr step out s xs @ [(x, out (foldl step s xs) x)])"
     by (simp add: c_dom_def)
    with False show ?thesis
    proof (simp add: C)
      have "length xs \<in> {..<length (xs @ [x])}" by simp
      with A have "D ((xs @ [x]) ! length xs)
        \<notin> sinks I D u (take (Suc (length xs)) (xs @ [x])) \<longrightarrow>
        out (foldl step s (ipurge_tr I D u (take (length xs) (xs @ [x]))))
        ((xs @ [x]) ! (length xs)) =
        out (foldl step s (take (length xs) (xs @ [x]))) ((xs @ [x]) ! (length xs))" ..
      hence "D x \<notin> sinks I D u (xs @ [x]) \<longrightarrow>
        out (foldl step s (ipurge_tr I D u xs)) x = out (foldl step s xs) x"
       by simp
      thus "out (foldl step s xs) x = out (foldl step s (ipurge_tr I D u xs)) x"
       using False by simp
    qed
  qed
qed

lemma c_tr_ipurge_tr_2 [rule_format]:
  assumes A: "\<forall>n \<in> {..length ys}. \<exists>Y.
    (ipurge_tr I (c_dom D) u (c_tr step out (foldl step s\<^sub>0 xs) (take n ys)), Y)
    \<in> futures (c_process step out s\<^sub>0) (c_tr step out s\<^sub>0 xs)"
  shows "n \<in> {..<length ys} \<longrightarrow> D (ys ! n) \<notin> sinks I D u (take (Suc n) ys) \<longrightarrow>
    out (foldl step (foldl step s\<^sub>0 xs) (ipurge_tr I D u (take n ys))) (ys ! n) =
    out (foldl step (foldl step s\<^sub>0 xs) (take n ys)) (ys ! n)"
proof (rule nat_less_induct, (rule impI)+)
  fix n
  let ?s = "foldl step s\<^sub>0 xs"
  let ?yp = "(ys ! n, out (foldl step ?s (take n ys)) (ys ! n))"
  assume
    B: "\<forall>m < n. m \<in> {..<length ys} \<longrightarrow>
      D (ys ! m) \<notin> sinks I D u (take (Suc m) ys) \<longrightarrow>
      out (foldl step ?s (ipurge_tr I D u (take m ys))) (ys ! m) =
      out (foldl step ?s (take m ys)) (ys ! m)" and
    C: "n \<in> {..<length ys}" and
    D: "D (ys ! n) \<notin> sinks I D u (take (Suc n) ys)"
  have "n < length ys" using C by simp
  hence E: "take (Suc n) ys = take n ys @ [ys ! n]"
   by (rule take_Suc_conv_app_nth)
  moreover have "Suc n \<in> {..length ys}" using C by simp
  with A have "\<exists>Y.
    (ipurge_tr I (c_dom D) u (c_tr step out ?s (take (Suc n) ys)), Y)
    \<in> futures (c_process step out s\<^sub>0) (c_tr step out s\<^sub>0 xs)" ..
  then obtain Y where
    "(ipurge_tr I (c_dom D) u (c_tr step out ?s (take (Suc n) ys)), Y)
    \<in> futures (c_process step out s\<^sub>0) (c_tr step out s\<^sub>0 xs)" ..
  ultimately have
    "(ipurge_tr I (c_dom D) u (c_tr step out ?s (take n ys) @ [?yp]), Y)
    \<in> futures (c_process step out s\<^sub>0) (c_tr step out s\<^sub>0 xs)"
   by simp
  moreover have "c_dom D ?yp
    \<notin> sinks I (c_dom D) u (c_tr step out ?s (take (Suc n) ys))"
   using D by (simp add: c_dom_def c_tr_sinks)
  hence "c_dom D ?yp \<notin> sinks I (c_dom D) u
    (c_tr step out ?s (take n ys) @ [?yp])"
   using E by simp
  ultimately have
    "(ipurge_tr I (c_dom D) u (c_tr step out ?s (take n ys)) @ [?yp], Y)
    \<in> futures (c_process step out s\<^sub>0) (c_tr step out s\<^sub>0 xs)"
   by simp
  moreover have "ipurge_tr I (c_dom D) u (c_tr step out ?s (take n ys)) =
    c_tr step out ?s (ipurge_tr I D u (take n ys))"
  proof (rule c_tr_ipurge_tr_1, simp, erule conjE, simp add: min_def)
    fix m
    have "m < n \<longrightarrow> m \<in> {..<length ys} \<longrightarrow>
      D (ys ! m) \<notin> sinks I D u (take (Suc m) ys) \<longrightarrow>
      out (foldl step ?s (ipurge_tr I D u (take m ys))) (ys ! m) =
      out (foldl step ?s (take m ys)) (ys ! m)" using B ..
    moreover assume "m < n"
    ultimately have "m \<in> {..<length ys} \<longrightarrow>
      D (ys ! m) \<notin> sinks I D u (take (Suc m) ys) \<longrightarrow>
      out (foldl step ?s (ipurge_tr I D u (take m ys))) (ys ! m) =
      out (foldl step ?s (take m ys)) (ys ! m)" ..
    moreover assume "m < length ys"
    hence "m \<in> {..<length ys}" by simp
    ultimately have "D (ys ! m) \<notin> sinks I D u (take (Suc m) ys) \<longrightarrow>
      out (foldl step ?s (ipurge_tr I D u (take m ys))) (ys ! m) =
      out (foldl step ?s (take m ys)) (ys ! m)" ..
    moreover assume "D (ys ! m) \<notin> sinks I D u (take (Suc m) ys)"
    ultimately show "out (foldl step ?s (ipurge_tr I D u (take m ys))) (ys ! m) =
      out (foldl step ?s (take m ys)) (ys ! m)" ..
  qed
  ultimately have "(c_tr step out ?s (ipurge_tr I D u (take n ys)) @ [?yp], Y)
    \<in> futures (c_process step out s\<^sub>0) (c_tr step out s\<^sub>0 xs)"
   by simp
  hence "(c_tr step out s\<^sub>0 (xs @ ipurge_tr I D u (take n ys)) @ [?yp], Y)
    \<in> c_failures step out s\<^sub>0"
   (is "(?xps, _) \<in> _") by (simp add: c_futures_failures c_tr_append)
  moreover have "?xps \<noteq> []" by simp
  ultimately have "snd (last ?xps) =
    out (foldl step s\<^sub>0 (butlast (map fst ?xps))) (last (map fst ?xps))"
   by (rule c_failures_last)
  thus "out (foldl step ?s (ipurge_tr I D u (take n ys))) (ys ! n) =
    out (foldl step ?s (take n ys)) (ys ! n)"
   by (simp add: c_tr_map butlast_append)
qed

lemma c_tr_ipurge_tr [rule_format]:
  assumes A: "\<forall>n \<in> {..length ys}. \<exists>Y.
    (ipurge_tr I (c_dom D) u (c_tr step out (foldl step s\<^sub>0 xs) (take n ys)), Y)
    \<in> futures (c_process step out s\<^sub>0) (c_tr step out s\<^sub>0 xs)"
  shows "ipurge_tr I (c_dom D) u (c_tr step out (foldl step s\<^sub>0 xs) ys) =
    c_tr step out (foldl step s\<^sub>0 xs) (ipurge_tr I D u ys)"
proof (rule c_tr_ipurge_tr_1)
  fix n
  have "\<And>n. n \<in> {..length ys} \<Longrightarrow> \<exists>Y.
    (ipurge_tr I (c_dom D) u (c_tr step out (foldl step s\<^sub>0 xs) (take n ys)), Y)
    \<in> futures (c_process step out s\<^sub>0) (c_tr step out s\<^sub>0 xs)"
   using A ..
  moreover assume
    "n \<in> {..<length ys}" and
    "D (ys ! n) \<notin> sinks I D u (take (Suc n) ys)"
  ultimately show
    "out (foldl step (foldl step s\<^sub>0 xs) (ipurge_tr I D u (take n ys))) (ys ! n) =
    out (foldl step (foldl step s\<^sub>0 xs) (take n ys)) (ys ! n)"
   by (rule c_tr_ipurge_tr_2)
qed


subsection "Equivalence between security properties"

text \<open>
The remainder of this section is dedicated to the proof of the equivalence between the CSP
noninterference security of a classical process and the classical noninterference security of the
corresponding deterministic state machine.

In some detail, it will be proven that CSP noninterference security alone is a sufficient condition
for classical noninterference security, whereas the latter security property entails the former for
any reflexive noninterference policy. Therefore, the security properties under consideration turn
out to be equivalent if the enforced noninterference policy is reflexive, which is the case for any
policy of practical significance.

\null
\<close>

lemma secure_implies_c_secure_aux:
  assumes S: "secure (c_process step out s\<^sub>0) I (c_dom D)"
  shows "out (foldl step (foldl step s\<^sub>0 xs) ys) x =
    out (foldl step (foldl step s\<^sub>0 xs) (c_ipurge I D (D x) ys)) x"
proof (induction ys arbitrary: xs, simp)
  fix y ys xs
  assume "\<And>xs. out (foldl step (foldl step s\<^sub>0 xs) ys) x =
    out (foldl step (foldl step s\<^sub>0 xs) (c_ipurge I D (D x) ys)) x"
  hence A: "out (foldl step (foldl step s\<^sub>0 (xs @ [y])) ys) x =
    out (foldl step (foldl step s\<^sub>0 (xs @ [y])) (c_ipurge I D (D x) ys)) x" .
  show "out (foldl step (foldl step s\<^sub>0 xs) (y # ys)) x =
    out (foldl step (foldl step s\<^sub>0 xs) (c_ipurge I D (D x) (y # ys))) x"
  proof (cases "D y \<in> c_sources I D (D x) (y # ys)")
    assume "D y \<in> c_sources I D (D x) (y # ys)"
    thus ?thesis using A by simp
  next
    let ?s = "foldl step s\<^sub>0 xs"
    let ?yp = "(y, out ?s y)"
    have "(c_tr step out ?s [y], {(x', p). p \<noteq> out (foldl step ?s [y]) x'})
      \<in> futures (c_process step out s\<^sub>0) (c_tr step out s\<^sub>0 xs)" (is "(_, ?Y) \<in> _")
     by (rule c_tr_futures)
    hence "([?yp], ?Y) \<in> futures (c_process step out s\<^sub>0) (c_tr step out s\<^sub>0 xs)"
     by (simp add: c_tr_hd_tl)
    moreover have "(c_tr step out ?s (c_ipurge I D (D x) (ys @ [x])),
      {(x', p). p \<noteq> out (foldl step ?s (c_ipurge I D (D x) (ys @ [x]))) x'})
      \<in> futures (c_process step out s\<^sub>0) (c_tr step out s\<^sub>0 xs)" (is "(_, ?Z) \<in> _")
     by (rule c_tr_futures)
    ultimately have "(?yp # ipurge_tr I (c_dom D) (c_dom D ?yp)
      (c_tr step out ?s (c_ipurge I D (D x) (ys @ [x]))),
      ipurge_ref I (c_dom D) (c_dom D ?yp)
      (c_tr step out ?s (c_ipurge I D (D x) (ys @ [x]))) ?Z)
      \<in> futures (c_process step out s\<^sub>0) (c_tr step out s\<^sub>0 xs)"
     (is "(_, ?X) \<in> _") using S by (simp add: secure_def)
    hence C: "(?yp # ipurge_tr I (c_dom D) (c_dom D ?yp)
      (c_ipurge I (c_dom D) (D x)
      (c_tr step out ?s (c_ipurge I D (D x) (ys @ [x])))), ?X)
      \<in> futures (c_process step out s\<^sub>0) (c_tr step out s\<^sub>0 xs)"
     by (simp add: c_tr_ipurge)
    assume D: "D y \<notin> c_sources I D (D x) (y # ys)"
    hence "D y \<notin> c_sources I D (D x) ((y # ys) @ [x])"
     by (subst c_sources_append_1)
    hence "D y \<notin> c_sources I D (D x) (y # ys @ [x])" by simp
    moreover have "c_sources I D (D x) (y # ys @ [x]) =
      c_sources I D (D x) (y # c_ipurge I D (D x) (ys @ [x]))"
     by (simp add: c_sources_ipurge)
    ultimately have "D y \<notin> c_sources I D (D x)
      (y # c_ipurge I D (D x) (ys @ [x]))"
     by simp
    moreover have "map fst (?yp # c_tr step out ?s
      (c_ipurge I D (D x) (ys @ [x]))) =
      y # c_ipurge I D (D x) (ys @ [x])"
     by (simp add: c_tr_map)
    hence "c_sources I D (D x) (y # c_ipurge I D (D x) (ys @ [x])) =
      c_sources I (c_dom D) (D x)
      (?yp # c_tr step out ?s (c_ipurge I D (D x) (ys @ [x])))"
     by (subst c_dom_sources, simp)
    ultimately have "c_dom D ?yp \<notin> c_sources I (c_dom D) (D x)
      (?yp # c_tr step out ?s (c_ipurge I D (D x) (ys @ [x])))"
     by (simp add: c_dom_def)
    hence "ipurge_tr I (c_dom D) (c_dom D ?yp) (c_ipurge I (c_dom D) (D x)
      (c_tr step out ?s (c_ipurge I D (D x) (ys @ [x])))) =
      c_ipurge I (c_dom D) (D x) (c_tr step out ?s (c_ipurge I D (D x) (ys @ [x])))"
     by (rule c_ipurge_tr_ipurge)
    hence "(?yp # c_tr step out ?s (c_ipurge I D (D x) (ys @ [x])), ?X)
      \<in> futures (c_process step out s\<^sub>0) (c_tr step out s\<^sub>0 xs)"
     using C by (simp add: c_tr_ipurge)
    hence "(c_tr step out s\<^sub>0 xs @ ?yp #
      c_tr step out ?s (c_ipurge I D (D x) ys @ [x]), ?X)
      \<in> c_failures step out s\<^sub>0"
     (is "(?xps, _) \<in> _") by (simp add: c_futures_failures c_ipurge_append_1)
    moreover have "?xps \<noteq> []" by simp
    ultimately have "snd (last ?xps) =
      out (foldl step s\<^sub>0 (butlast (map fst ?xps))) (last (map fst ?xps))"
     by (rule c_failures_last)
    hence "snd (last ?xps) =
      out (foldl step (foldl step s\<^sub>0 (xs @ [y])) (c_ipurge I D (D x) ys)) x"
     by (simp add: c_tr_map butlast_append)
    moreover have "snd (last ?xps) =
      out (foldl step (foldl step s\<^sub>0 xs) (c_ipurge I D (D x) (y # ys))) x"
     using D by simp
    ultimately show ?thesis using A by simp
  qed
qed

theorem secure_implies_c_secure:
  assumes S: "secure (c_process step out s\<^sub>0) I (c_dom D)"
  shows "c_secure step out s\<^sub>0 I D"
proof (simp add: c_secure_def, (rule allI)+)
  fix x xs
  have "out (foldl step (foldl step s\<^sub>0 []) xs) x =
    out (foldl step (foldl step s\<^sub>0 []) (c_ipurge I D (D x) xs)) x"
   using S by (rule secure_implies_c_secure_aux)
  thus "out (foldl step s\<^sub>0 xs) x = out (foldl step s\<^sub>0 (c_ipurge I D (D x) xs)) x"
   by simp
qed

lemma c_secure_futures_1:
  assumes R: "refl I" and S: "c_secure step out s\<^sub>0 I D"
  shows "(yps @ [yp], Y) \<in> futures (c_process step out s\<^sub>0) xps \<Longrightarrow>
    (yps, {x \<in> Y. (c_dom D yp, c_dom D x) \<notin> I})
    \<in> futures (c_process step out s\<^sub>0) xps"
proof (simp add: c_futures_failures)
  let ?zs = "map fst (xps @ yps)"
  let ?y = "fst yp"
  assume A: "(xps @ yps @ [yp], Y) \<in> c_failures step out s\<^sub>0"
  hence "((xps @ yps) @ [yp], Y) \<in> failures (c_process step out s\<^sub>0)"
   by (simp add: c_failures_failures)
  hence "(xps @ yps, {}) \<in> failures (c_process step out s\<^sub>0)"
   by (rule process_rule_2_failures)
  hence "(xps @ yps, {}) \<in> c_failures step out s\<^sub>0" by (simp add: c_failures_failures)
  hence B: "xps @ yps = c_tr step out s\<^sub>0 ?zs" by (rule c_failures_tr)
  have "Y \<subseteq> {(x, p). p \<noteq> out (foldl step s\<^sub>0 (map fst (xps @ yps @ [yp]))) x}"
   using A by (rule c_failures_ref)
  hence C: "Y \<subseteq> {(x, p). p \<noteq> out (foldl step s\<^sub>0 (?zs @ [?y])) x}"
   (is "_ \<subseteq> ?Y'") by simp
  have "(xps @ yps, {(x, p). p \<noteq> out (foldl step s\<^sub>0 ?zs) x}) \<in> c_failures step out s\<^sub>0"
   (is "(_, ?X') \<in> _") by (subst B, rule c_tr_failures)
  moreover have "{x \<in> Y. (c_dom D yp, c_dom D x) \<notin> I} \<subseteq> ?X'" (is "?X \<subseteq> _")
  proof (rule subsetI, simp add: split_paired_all c_dom_def del: map_append,
   erule conjE)
    fix x p
    assume "(x, p) \<in> Y"
    with C have "(x, p) \<in> ?Y'" ..
    hence "p \<noteq> out (foldl step s\<^sub>0 (?zs @ [?y])) x" by simp
    moreover have "out (foldl step s\<^sub>0 (?zs @ [?y])) x =
      out (foldl step s\<^sub>0 (c_ipurge I D (D x) (?zs @ [?y]))) x"
     using S by (simp add: c_secure_def)
    ultimately have "p \<noteq> out (foldl step s\<^sub>0 (c_ipurge I D (D x) (?zs @ [?y]))) x"
     by simp
    moreover assume "(D ?y, D x) \<notin> I"
    with R have "c_ipurge I D (D x) (?zs @ [?y]) = c_ipurge I D (D x) ?zs"
     by (rule c_ipurge_append_2)
    ultimately have "p \<noteq> out (foldl step s\<^sub>0 (c_ipurge I D (D x) ?zs)) x" by simp
    moreover have "out (foldl step s\<^sub>0 (c_ipurge I D (D x) ?zs)) x =
      out (foldl step s\<^sub>0 ?zs) x"
     using S by (simp add: c_secure_def)
    ultimately show "p \<noteq> out (foldl step s\<^sub>0 ?zs) x" by simp
  qed
  ultimately show "(xps @ yps, ?X) \<in> c_failures step out s\<^sub>0" by (rule R2)
qed

lemma c_secure_implies_secure_aux_1 [rule_format]:
  assumes
    R: "refl I" and
    S: "c_secure step out s\<^sub>0 I D"
  shows "(yp # yps, Y) \<in> futures (c_process step out s\<^sub>0) xps \<longrightarrow>
    (ipurge_tr I (c_dom D) (c_dom D yp) yps,
    ipurge_ref I (c_dom D) (c_dom D yp) yps Y)
    \<in> futures (c_process step out s\<^sub>0) xps"
proof (induction yps arbitrary: Y rule: length_induct, rule impI)
  fix yps Y
  assume
    A: "\<forall>yps'. length yps' < length yps \<longrightarrow>
      (\<forall>Y'. (yp # yps', Y') \<in> futures (c_process step out s\<^sub>0) xps \<longrightarrow>
      (ipurge_tr I (c_dom D) (c_dom D yp) yps',
      ipurge_ref I (c_dom D) (c_dom D yp) yps' Y')
      \<in> futures (c_process step out s\<^sub>0) xps)" and
    B: "(yp # yps, Y) \<in> futures (c_process step out s\<^sub>0) xps"
  show "(ipurge_tr I (c_dom D) (c_dom D yp) yps,
    ipurge_ref I (c_dom D) (c_dom D yp) yps Y)
    \<in> futures (c_process step out s\<^sub>0) xps"
  proof (cases yps, simp add: ipurge_ref_def)
    case Nil
    hence "([] @ [yp], Y) \<in> futures (c_process step out s\<^sub>0) xps" using B by simp
    with R and S show "([], {x \<in> Y. (c_dom D yp, c_dom D x) \<notin> I})
      \<in> futures (c_process step out s\<^sub>0) xps"
     by (rule c_secure_futures_1)
  next
    case Cons
    have "\<exists>wps wp. yps = wps @ [wp]"
     by (rule rev_cases [of yps], simp_all add: Cons)
    then obtain wps and wp where C: "yps = wps @ [wp]" by blast
    have B': "((yp # wps) @ [wp], Y) \<in> futures (c_process step out s\<^sub>0) xps"
     using B and C by simp
    show ?thesis
    proof (simp only: C,
     cases "c_dom D wp \<in> sinks I (c_dom D) (c_dom D yp) (wps @ [wp])")
      let ?Y' = "{x \<in> Y. (c_dom D wp, c_dom D x) \<notin> I}"
      have "length wps < length yps \<longrightarrow>
        (\<forall>Y'. (yp # wps, Y') \<in> futures (c_process step out s\<^sub>0) xps \<longrightarrow>
        (ipurge_tr I (c_dom D) (c_dom D yp) wps,
        ipurge_ref I (c_dom D) (c_dom D yp) wps Y')
        \<in> futures (c_process step out s\<^sub>0) xps)"
       using A ..
      moreover have "length wps < length yps" using C by simp
      ultimately have "\<forall>Y'.
        (yp # wps, Y') \<in> futures (c_process step out s\<^sub>0) xps \<longrightarrow>
        (ipurge_tr I (c_dom D) (c_dom D yp) wps,
        ipurge_ref I (c_dom D) (c_dom D yp) wps Y')
        \<in> futures (c_process step out s\<^sub>0) xps" ..
      hence "(yp # wps, ?Y') \<in> futures (c_process step out s\<^sub>0) xps \<longrightarrow>
        (ipurge_tr I (c_dom D) (c_dom D yp) wps,
        ipurge_ref I (c_dom D) (c_dom D yp) wps ?Y')
        \<in> futures (c_process step out s\<^sub>0) xps" ..
      moreover have "(yp # wps, ?Y') \<in> futures (c_process step out s\<^sub>0) xps"
       using R and S and B' by (rule c_secure_futures_1)
      ultimately have "(ipurge_tr I (c_dom D) (c_dom D yp) wps,
        ipurge_ref I (c_dom D) (c_dom D yp) wps ?Y')
        \<in> futures (c_process step out s\<^sub>0) xps" ..
      moreover assume
        D: "c_dom D wp \<in> sinks I (c_dom D) (c_dom D yp) (wps @ [wp])"
      hence "ipurge_tr I (c_dom D) (c_dom D yp) (wps @ [wp]) =
        ipurge_tr I (c_dom D) (c_dom D yp) wps"
       by simp
      moreover have "ipurge_ref I (c_dom D) (c_dom D yp) (wps @ [wp]) Y =
        ipurge_ref I (c_dom D) (c_dom D yp) wps ?Y'"
       using D by (rule ipurge_ref_eq)
      ultimately show "(ipurge_tr I (c_dom D) (c_dom D yp) (wps @ [wp]),
        ipurge_ref I (c_dom D) (c_dom D yp) (wps @ [wp]) Y)
        \<in> futures (c_process step out s\<^sub>0) xps"
       by simp
    next
      let ?xs = "map fst xps"
      let ?y = "fst yp"
      let ?ws = "map fst wps"
      let ?w = "fst wp"
      let ?s = "foldl step s\<^sub>0 ?xs"
      have "(xps @ yp # wps @ [wp], Y) \<in> failures (c_process step out s\<^sub>0)"
       using B' by (simp add: c_futures_failures c_failures_failures)
      hence "(xps, {}) \<in> failures (c_process step out s\<^sub>0)"
       by (rule process_rule_2_failures)
      hence "(xps, {}) \<in> c_failures step out s\<^sub>0"
       by (simp add: c_failures_failures)
      hence X: "xps = c_tr step out s\<^sub>0 ?xs" by (rule c_failures_tr)
      have W: "(yp # wps, {}) \<in> futures (c_process step out s\<^sub>0) xps"
       using B' by (rule process_rule_2_futures)
      hence "yp # wps = c_tr step out ?s (map fst (yp # wps))"
       by (rule c_futures_tr)
      hence W': "yp # wps = c_tr step out ?s (?y # ?ws)" by simp
      assume D: "c_dom D wp \<notin> sinks I (c_dom D) (c_dom D yp) (wps @ [wp])"
      hence "ipurge_tr I (c_dom D) (c_dom D yp) (wps @ [wp]) =
        ipurge_tr I (c_dom D) (c_dom D yp) (yp # wps) @ [wp]"
       using R by (simp add: ipurge_tr_cons_same)
      hence "ipurge_tr I (c_dom D) (c_dom D yp) (wps @ [wp]) =
        ipurge_tr I (c_dom D) (c_dom D yp) (c_tr step out ?s (?y # ?ws)) @ [wp]"
       using W' by simp
      also have "\<dots> =
        c_tr step out ?s (ipurge_tr I D (c_dom D yp) (?y # ?ws)) @ [wp]"
      proof (simp, rule c_tr_ipurge_tr)
        fix n
        show "\<exists>W. (ipurge_tr I (c_dom D) (c_dom D yp)
          (c_tr step out ?s (take n (?y # ?ws))), W)
          \<in> futures (c_process step out s\<^sub>0) (c_tr step out s\<^sub>0 ?xs)"
        proof (cases n, simp_all add: c_tr_hd_tl)
          have "(c_tr step out ?s [], {(x, p). p \<noteq> out (foldl step ?s []) x})
            \<in> futures (c_process step out s\<^sub>0) (c_tr step out s\<^sub>0 ?xs)"
           by (rule c_tr_futures)
          hence "([], {(x, p). p \<noteq> out ?s x})
            \<in> futures (c_process step out s\<^sub>0) (c_tr step out s\<^sub>0 ?xs)"
           by simp
          thus "\<exists>W. ([], W)
            \<in> futures (c_process step out s\<^sub>0) (c_tr step out s\<^sub>0 ?xs)" ..
        next
          case (Suc m)
          let ?wps' = "c_tr step out (step ?s ?y) (take m ?ws)"
          have "length ?wps' < length yps \<longrightarrow>
            (\<forall>Y'. (yp # ?wps', Y') \<in> futures (c_process step out s\<^sub>0) xps \<longrightarrow>
            (ipurge_tr I (c_dom D) (c_dom D yp) ?wps',
            ipurge_ref I (c_dom D) (c_dom D yp) ?wps' Y')
            \<in> futures (c_process step out s\<^sub>0) xps)"
           using A ..
          moreover have "length ?wps' < length yps"
           using C by (simp add: c_tr_length)
          ultimately have "\<forall>Y'.
            (yp # ?wps', Y') \<in> futures (c_process step out s\<^sub>0) xps \<longrightarrow>
            (ipurge_tr I (c_dom D) (c_dom D yp) ?wps',
            ipurge_ref I (c_dom D) (c_dom D yp) ?wps' Y')
            \<in> futures (c_process step out s\<^sub>0) xps" ..
          hence "(yp # ?wps', {}) \<in> futures (c_process step out s\<^sub>0) xps \<longrightarrow>
            (ipurge_tr I (c_dom D) (c_dom D yp) ?wps',
            ipurge_ref I (c_dom D) (c_dom D yp) ?wps' {})
            \<in> futures (c_process step out s\<^sub>0) xps"
           (is "_ \<longrightarrow> (_, ?W') \<in> _") ..
          moreover have E: "yp # wps = (?y, out ?s ?y) #
            c_tr step out (step ?s ?y) (take m ?ws @ drop m ?ws)"
           using W' by (simp add: c_tr_hd_tl)
          hence F: "yp = (?y, out ?s ?y)" by simp
          hence "yp # wps = yp # ?wps' @
            c_tr step out (foldl step (step ?s ?y) (take m ?ws)) (drop m ?ws)"
           using E by (simp only: c_tr_append)
          hence "((yp # ?wps') @
            c_tr step out (foldl step (step ?s ?y) (take m ?ws)) (drop m ?ws), {})
            \<in> futures (c_process step out s\<^sub>0) xps"
           using W by simp
          hence "(yp # ?wps', {}) \<in> futures (c_process step out s\<^sub>0) xps"
           by (rule process_rule_2_futures)
          ultimately have "(ipurge_tr I (c_dom D) (c_dom D yp) ?wps', ?W')
            \<in> futures (c_process step out s\<^sub>0) xps" ..
          moreover have "ipurge_tr I (c_dom D) (c_dom D yp) ?wps' =
            ipurge_tr I (c_dom D) (c_dom D yp) ((?y, out ?s ?y) # ?wps')"
           using R and F by (simp add: ipurge_tr_cons_same)
          ultimately have
            "(ipurge_tr I (c_dom D) (c_dom D yp) ((?y, out ?s ?y) # ?wps'), ?W')
            \<in> futures (c_process step out s\<^sub>0) (c_tr step out s\<^sub>0 ?xs)"
           using X by simp
          thus "\<exists>W.
            (ipurge_tr I (c_dom D) (c_dom D yp) ((?y, out ?s ?y) # ?wps'), W)
            \<in> futures (c_process step out s\<^sub>0) (c_tr step out s\<^sub>0 ?xs)"
           by (rule_tac x = ?W' in exI)
        qed
      qed
      finally have E: "ipurge_tr I (c_dom D) (c_dom D yp) (wps @ [wp]) =
        c_tr step out ?s (ipurge_tr I D (c_dom D yp) (?y # ?ws)) @ [wp]" .
      have "(xps @ yp # wps @ [wp], Y) \<in> c_failures step out s\<^sub>0"
       (is "(?xps', _) \<in> _") using B' by (simp add: c_futures_failures)
      moreover have "?xps' \<noteq> []" by simp
      ultimately have "snd (last ?xps') =
        out (foldl step s\<^sub>0 (butlast (map fst ?xps'))) (last (map fst ?xps'))"
       by (rule c_failures_last)
      hence "snd wp = out (foldl step s\<^sub>0 (?xs @ ?y # ?ws)) ?w"
       by (simp add: butlast_append)
      hence "snd wp =
        out (foldl step s\<^sub>0 (c_ipurge I D (D ?w) (?xs @ ?y # ?ws))) ?w"
       using S by (simp add: c_secure_def)
      moreover have F: "D ?w \<notin> sinks I D (c_dom D yp) (?ws @ [?w])"
       using D by (simp only: c_dom_sinks, simp add: c_dom_def)
      have "\<not> (\<exists>v \<in> sinks I D (c_dom D yp) (?y # ?ws). (v, D ?w) \<in> I)"
      proof (rule notI, simp add: c_dom_def sinks_cons_same R, erule disjE)
        assume "(D ?y, D ?w) \<in> I"
        hence "D ?w \<in> sinks I D (c_dom D yp) (?ws @ [?w])"
         by (simp add: c_dom_def)
        thus False using F by contradiction
      next
        assume "\<exists>v \<in> sinks I D (D ?y) ?ws. (v, D ?w) \<in> I"
        hence "D ?w \<in> sinks I D (c_dom D yp) (?ws @ [?w])"
         by (simp add: c_dom_def)
        thus False using F by contradiction
      qed
      ultimately have "snd wp = out (foldl step s\<^sub>0
        (c_ipurge I D (D ?w) (?xs @ ipurge_tr I D (c_dom D yp) (?y # ?ws)))) ?w"
       using R by (simp add: c_ipurge_ipurge_tr)
      hence "snd wp =
        out (foldl step s\<^sub>0 (?xs @ ipurge_tr I D (c_dom D yp) (?y # ?ws))) ?w"
       using S by (simp add: c_secure_def)
      hence "ipurge_tr I (c_dom D) (c_dom D yp) (wps @ [wp]) =
        c_tr step out ?s (ipurge_tr I D (c_dom D yp) (?y # ?ws)) @
        [(?w, out (foldl step ?s (ipurge_tr I D (c_dom D yp) (?y # ?ws))) ?w)]"
       using E by (cases wp, simp)
      hence "ipurge_tr I (c_dom D) (c_dom D yp) (wps @ [wp]) =
        c_tr step out ?s (ipurge_tr I D (c_dom D yp) (?y # ?ws)) @
        c_tr step out (foldl step ?s (ipurge_tr I D (c_dom D yp) (?y # ?ws))) [?w]"
       by (simp add: c_tr_singleton)
      hence "ipurge_tr I (c_dom D) (c_dom D yp) (wps @ [wp]) =
        c_tr step out ?s (ipurge_tr I D (c_dom D yp) (?y # ?ws) @ [?w])"
       by (simp add: c_tr_append)
      moreover have
        "(c_tr step out ?s (ipurge_tr I D (c_dom D yp) (?y # ?ws) @ [?w]),
        {(x, p). p \<noteq> out (foldl step ?s
        (ipurge_tr I D (c_dom D yp) (?y # ?ws) @ [?w])) x})
        \<in> futures (c_process step out s\<^sub>0) (c_tr step out s\<^sub>0 ?xs)"
       (is "(_, ?Y') \<in> _") by (rule c_tr_futures)
      ultimately have
        "(xps @ ipurge_tr I (c_dom D) (c_dom D yp) (wps @ [wp]), ?Y')
        \<in> c_failures step out s\<^sub>0"
       using X by (simp add: c_futures_failures)
      moreover have
        "ipurge_ref I (c_dom D) (c_dom D yp) (wps @ [wp]) Y \<subseteq> ?Y'"
      proof (rule subsetI, simp add: split_paired_all ipurge_ref_def c_dom_def
       del: sinks.simps, (erule conjE)+)
        fix x p
        assume
          G: "\<forall>v \<in> sinks I (c_dom D) (D ?y) (wps @ [wp]). (v, D x) \<notin> I" and
          H: "(D ?y, D x) \<notin> I"
        have "(xps @ yp # wps @ [wp], Y) \<in> c_failures step out s\<^sub>0"
         using B' by (simp add: c_futures_failures)
        hence "Y \<subseteq> {(x', p'). p' \<noteq>
          out (foldl step s\<^sub>0 (map fst (xps @ yp # wps @ [wp]))) x'}"
         by (rule c_failures_ref)
        hence "Y \<subseteq> {(x', p'). p' \<noteq>
          out (foldl step s\<^sub>0 (?xs @ ?y # ?ws @ [?w])) x'}"
         by simp
        moreover assume "(x, p) \<in> Y"
        ultimately have "(x, p) \<in> {(x', p'). p' \<noteq>
          out (foldl step s\<^sub>0 (?xs @ ?y # ?ws @ [?w])) x'}" ..
        hence "p \<noteq> out (foldl step s\<^sub>0
          (c_ipurge I D (D x) (?xs @ ?y # ?ws @ [?w]))) x"
         using S by (simp add: c_secure_def)
        moreover have
          "\<not> (\<exists>v \<in> sinks I D (D ?y) (?y # ?ws @ [?w]). (v, D x) \<in> I)"
        proof
          assume "\<exists>v \<in> sinks I D (D ?y) (?y # ?ws @ [?w]). (v, D x) \<in> I"
          then obtain v where
            A: "v \<in> sinks I D (D ?y) (?y # ?ws @ [?w])" and
            B: "(v, D x) \<in> I" ..
          have "v = D ?y \<or> v \<in> sinks I D (D ?y) (?ws @ [?w])"
           using R and A by (simp add: sinks_cons_same)
          moreover {
            assume "v = D ?y"
            hence "(D ?y, D x) \<in> I" using B by simp
            hence False using H by contradiction
          }
          moreover {
            assume "v \<in> sinks I D (D ?y) (?ws @ [?w])"
            hence "v \<in> sinks I (c_dom D) (D ?y) (wps @ [wp])"
             by (simp only: c_dom_sinks, simp)
            with G have "(v, D x) \<notin> I" ..
            hence False using B by contradiction
          }
          ultimately show False by blast
        qed
        ultimately have "p \<noteq> out (foldl step s\<^sub>0 (c_ipurge I D (D x)
          (?xs @ ipurge_tr I D (D ?y) (?y # ?ws @ [?w])))) x"
         using R by (simp add: c_ipurge_ipurge_tr)
        hence "p \<noteq> out (foldl step s\<^sub>0 (?xs @ ipurge_tr I D (D ?y) (?ws @ [?w]))) x"
         using R and S by (simp add: c_secure_def ipurge_tr_cons_same)
        hence "p \<noteq> out (foldl step s\<^sub>0 (?xs @ ipurge_tr I D (D ?y) ?ws @ [?w])) x"
         using F by (simp add: c_dom_def)
        thus "p \<noteq> out (step (foldl step ?s
          (ipurge_tr I D (D ?y) (?y # ?ws))) ?w) x"
         using R by (simp add: ipurge_tr_cons_same)
      qed
      ultimately have "(xps @ ipurge_tr I (c_dom D) (c_dom D yp) (wps @ [wp]),
        ipurge_ref I (c_dom D) (c_dom D yp) (wps @ [wp]) Y)
        \<in> c_failures step out s\<^sub>0"
       by (rule R2)
      thus "(ipurge_tr I (c_dom D) (c_dom D yp) (wps @ [wp]),
        ipurge_ref I (c_dom D) (c_dom D yp) (wps @ [wp]) Y)
        \<in> futures (c_process step out s\<^sub>0) xps"
       by (simp add: c_futures_failures)
    qed
  qed
qed

lemma c_secure_futures_2:
  assumes R: "refl I" and S: "c_secure step out s\<^sub>0 I D"
  shows "(yps @ [yp], A) \<in> futures (c_process step out s\<^sub>0) xps \<Longrightarrow>
    (yps, Y) \<in> futures (c_process step out s\<^sub>0) xps \<Longrightarrow>
    (yps @ [yp], {x \<in> Y. (c_dom D yp, c_dom D x) \<notin> I})
    \<in> futures (c_process step out s\<^sub>0) xps"
proof (simp add: c_futures_failures)
  let ?zs = "map fst (xps @ yps)"
  let ?y = "fst yp"
  assume "(xps @ yps @ [yp], A) \<in> c_failures step out s\<^sub>0"
  hence "xps @ yps @ [yp] = c_tr step out s\<^sub>0 (map fst (xps @ yps @ [yp]))"
   by (rule c_failures_tr)
  hence A: "xps @ yps @ [yp] = c_tr step out s\<^sub>0 (?zs @ [?y])" by simp
  assume "(xps @ yps, Y) \<in> c_failures step out s\<^sub>0"
  hence B: "Y \<subseteq> {(x, p). p \<noteq> out (foldl step s\<^sub>0 ?zs) x}"
   (is "_ \<subseteq> ?Y'") by (rule c_failures_ref)
  have "(xps @ yps @ [yp], {(x, p). p \<noteq> out (foldl step s\<^sub>0 (?zs @ [?y])) x})
    \<in> c_failures step out s\<^sub>0"
   (is "(_, ?X') \<in> _") by (subst A, rule c_tr_failures)
  moreover have "{x \<in> Y. (c_dom D yp, c_dom D x) \<notin> I} \<subseteq> ?X'" (is "?X \<subseteq> _")
  proof (rule subsetI, simp add: split_paired_all c_dom_def
   del: map_append foldl_append, erule conjE)
    fix x p
    assume "(x, p) \<in> Y"
    with B have "(x, p) \<in> ?Y'" ..
    hence "p \<noteq> out (foldl step s\<^sub>0 ?zs) x" by simp
    moreover have "out (foldl step s\<^sub>0 ?zs) x =
      out (foldl step s\<^sub>0 (c_ipurge I D (D x) ?zs)) x"
     using S by (simp add: c_secure_def)
    ultimately have "p \<noteq> out (foldl step s\<^sub>0 (c_ipurge I D (D x) ?zs)) x" by simp
    moreover assume "(D ?y, D x) \<notin> I"
    with R have "c_ipurge I D (D x) (?zs @ [?y]) = c_ipurge I D (D x) ?zs"
     by (rule c_ipurge_append_2)
    ultimately have "p \<noteq> out (foldl step s\<^sub>0 (c_ipurge I D (D x) (?zs @ [?y]))) x"
     by simp
    moreover have "out (foldl step s\<^sub>0 (c_ipurge I D (D x) (?zs @ [?y]))) x =
      out (foldl step s\<^sub>0 (?zs @ [?y])) x"
     using S by (simp add: c_secure_def)
    ultimately show "p \<noteq> out (foldl step s\<^sub>0 (?zs @ [?y])) x" by simp
  qed
  ultimately show "(xps @ yps @ [yp], ?X) \<in> c_failures step out s\<^sub>0" by (rule R2)
qed

lemma c_secure_ipurge_tr:
  assumes R: "refl I" and S: "c_secure step out s\<^sub>0 I D"
  shows "ipurge_tr I (c_dom D) (D x) (c_tr step out (step (foldl step s\<^sub>0 xs) x) ys)
    = ipurge_tr I (c_dom D) (D x) (c_tr step out (foldl step s\<^sub>0 xs) ys)"
proof (induction ys rule: rev_induct, simp, simp only: c_tr.simps)
  let ?s = "foldl step s\<^sub>0 xs"
  fix ys y
  assume A: "ipurge_tr I (c_dom D) (D x) (c_tr step out (step ?s x) ys) =
    ipurge_tr I (c_dom D) (D x) (c_tr step out ?s ys)"
  show "ipurge_tr I (c_dom D) (D x) (c_tr step out (step ?s x) ys @
    [(y, out (foldl step (step ?s x) ys) y)]) =
    ipurge_tr I (c_dom D) (D x)
    (c_tr step out ?s ys @ [(y, out (foldl step ?s ys) y)])"
   (is "_ (_ @ [?yp']) = _ (_ @ [?yp])")
  proof (cases "D y \<in> sinks I D (D x) (ys @ [y])")
    assume D: "D y \<in> sinks I D (D x) (ys @ [y])"
    hence "c_dom D ?yp' \<in> sinks I (c_dom D) (D x)
      (c_tr step out (step ?s x) ys @ [?yp'])"
     using D by (simp only: c_dom_sinks, simp add: c_dom_def c_tr_map)
    hence "ipurge_tr I (c_dom D) (D x) (c_tr step out (step ?s x) ys @ [?yp']) =
      ipurge_tr I (c_dom D) (D x) (c_tr step out (step ?s x) ys)"
     by simp
    moreover have "c_dom D ?yp \<in> sinks I (c_dom D) (D x)
      (c_tr step out ?s ys @ [?yp])"
     using D by (simp only: c_dom_sinks, simp add: c_dom_def c_tr_map)
    hence "ipurge_tr I (c_dom D) (D x) (c_tr step out ?s ys @ [?yp]) =
      ipurge_tr I (c_dom D) (D x) (c_tr step out ?s ys)"
     by simp
    ultimately show ?thesis using A by simp
  next
    assume D: "D y \<notin> sinks I D (D x) (ys @ [y])"
    hence "c_dom D ?yp' \<notin> sinks I (c_dom D) (D x)
      (c_tr step out (step ?s x) ys @ [?yp'])"
     using D by (simp only: c_dom_sinks, simp add: c_dom_def c_tr_map)
    hence "ipurge_tr I (c_dom D) (D x) (c_tr step out (step ?s x) ys @ [?yp']) =
      ipurge_tr I (c_dom D) (D x) (c_tr step out (step ?s x) ys) @ [?yp']"
     by simp
    moreover have "c_dom D ?yp \<notin> sinks I (c_dom D) (D x)
      (c_tr step out ?s ys @ [?yp])"
     using D by (simp only: c_dom_sinks, simp add: c_dom_def c_tr_map)
    hence "ipurge_tr I (c_dom D) (D x) (c_tr step out ?s ys @ [?yp]) =
      ipurge_tr I (c_dom D) (D x) (c_tr step out ?s ys) @ [?yp]"
     by simp
    ultimately show ?thesis
    proof (simp add: A)
      have B: "\<not> (\<exists>v \<in> sinks I D (D x) ys. (v, D y) \<in> I)"
      proof
        assume "\<exists>v \<in> sinks I D (D x) ys. (v, D y) \<in> I"
        hence "D y \<in> sinks I D (D x) (ys @ [y])" by simp
        thus False using D by contradiction
      qed
      have C: "\<not> (\<exists>v \<in> sinks I D (D x) (x # ys). (v, D y) \<in> I)"
      proof (rule notI, simp add: sinks_cons_same R B)
        assume "(D x, D y) \<in> I"
        hence "D y \<in> sinks I D (D x) (ys @ [y])" by simp
        thus False using D by contradiction
      qed
      have "out (foldl step (step ?s x) ys) y = out (foldl step s\<^sub>0 (xs @ x # ys)) y"
       by simp
      also have "\<dots> = out (foldl step s\<^sub>0 (c_ipurge I D (D y) (xs @ x # ys))) y"
       using S by (simp add: c_secure_def)
      also have "\<dots> = out (foldl step s\<^sub>0 (c_ipurge I D (D y)
        (xs @ ipurge_tr I D (D x) (x # ys)))) y"
       using R and C by (simp add: c_ipurge_ipurge_tr)
      also have "\<dots> = out (foldl step s\<^sub>0 (c_ipurge I D (D y)
        (xs @ ipurge_tr I D (D x) ys))) y"
       using R by (simp add: ipurge_tr_cons_same)
      also have "\<dots> = out (foldl step s\<^sub>0 (c_ipurge I D (D y) (xs @ ys))) y"
       using R and B by (simp add: c_ipurge_ipurge_tr)
      also have "\<dots> = out (foldl step s\<^sub>0 (xs @ ys)) y"
       using S by (simp add: c_secure_def)
      also have "\<dots> = out (foldl step ?s ys) y" by simp
      finally show "out (foldl step (step ?s x) ys) y = out (foldl step ?s ys) y" .
    qed
  qed
qed

lemma c_secure_implies_secure_aux_2 [rule_format]:
  assumes
    R: "refl I" and
    S: "c_secure step out s\<^sub>0 I D" and
    Y: "(yp # yps, Y) \<in> futures (c_process step out s\<^sub>0) xps"
  shows "(zps, Z) \<in> futures (c_process step out s\<^sub>0) xps \<longrightarrow>
    (yp # ipurge_tr I (c_dom D) (c_dom D yp) zps,
    ipurge_ref I (c_dom D) (c_dom D yp) zps Z)
    \<in> futures (c_process step out s\<^sub>0) xps"
proof (induction zps arbitrary: Z rule: length_induct, rule impI)
  fix zps Z
  assume
    A: "\<forall>zps'. length zps' < length zps \<longrightarrow>
      (\<forall>Z'. (zps', Z') \<in> futures (c_process step out s\<^sub>0) xps \<longrightarrow>
      (yp # ipurge_tr I (c_dom D) (c_dom D yp) zps',
      ipurge_ref I (c_dom D) (c_dom D yp) zps' Z')
      \<in> futures (c_process step out s\<^sub>0) xps)" and
    B: "(zps, Z) \<in> futures (c_process step out s\<^sub>0) xps"
  show "(yp # ipurge_tr I (c_dom D) (c_dom D yp) zps,
    ipurge_ref I (c_dom D) (c_dom D yp) zps Z)
    \<in> futures (c_process step out s\<^sub>0) xps"
  proof (cases zps, simp add: ipurge_ref_def)
    case Nil
    hence C: "([], Z) \<in> futures (c_process step out s\<^sub>0) xps" using B by simp
    have "(([] @ [yp]) @ yps, Y) \<in> futures (c_process step out s\<^sub>0) xps"
     using Y by simp
    hence "([] @ [yp], {}) \<in> futures (c_process step out s\<^sub>0) xps"
     by (rule process_rule_2_futures)
    with R and S have "([] @ [yp], {x \<in> Z. (c_dom D yp, c_dom D x) \<notin> I})
      \<in> futures (c_process step out s\<^sub>0) xps"
     using C by (rule c_secure_futures_2)
    thus "([yp], {x \<in> Z. (c_dom D yp, c_dom D x) \<notin> I})
      \<in> futures (c_process step out s\<^sub>0) xps"
     by simp
  next
    case Cons
    have "\<exists>wps wp. zps = wps @ [wp]"
     by (rule rev_cases [of zps], simp_all add: Cons)
    then obtain wps and wp where C: "zps = wps @ [wp]" by blast
    have B': "(wps @ [wp], Z) \<in> futures (c_process step out s\<^sub>0) xps"
     using B and C by simp
    show ?thesis
    proof (simp only: C,
     cases "c_dom D wp \<in> sinks I (c_dom D) (c_dom D yp) (wps @ [wp])")
      let ?Z' = "{x \<in> Z. (c_dom D wp, c_dom D x) \<notin> I}"
      have "length wps < length zps \<longrightarrow>
        (\<forall>Z'. (wps, Z') \<in> futures (c_process step out s\<^sub>0) xps \<longrightarrow>
        (yp # ipurge_tr I (c_dom D) (c_dom D yp) wps,
        ipurge_ref I (c_dom D) (c_dom D yp) wps Z')
        \<in> futures (c_process step out s\<^sub>0) xps)"
       using A ..
      moreover have "length wps < length zps" using C by simp
      ultimately have "\<forall>Z'. (wps, Z') \<in> futures (c_process step out s\<^sub>0) xps \<longrightarrow>
        (yp # ipurge_tr I (c_dom D) (c_dom D yp) wps,
        ipurge_ref I (c_dom D) (c_dom D yp) wps Z')
        \<in> futures (c_process step out s\<^sub>0) xps" ..
      hence "(wps, ?Z') \<in> futures (c_process step out s\<^sub>0) xps \<longrightarrow>
        (yp # ipurge_tr I (c_dom D) (c_dom D yp) wps,
        ipurge_ref I (c_dom D) (c_dom D yp) wps ?Z')
        \<in> futures (c_process step out s\<^sub>0) xps" ..
      moreover have "(wps, ?Z') \<in> futures (c_process step out s\<^sub>0) xps"
       using R and S and B' by (rule c_secure_futures_1)
      ultimately have "(yp # ipurge_tr I (c_dom D) (c_dom D yp) wps,
        ipurge_ref I (c_dom D) (c_dom D yp) wps ?Z')
        \<in> futures (c_process step out s\<^sub>0) xps" ..
      moreover assume
        D: "c_dom D wp \<in> sinks I (c_dom D) (c_dom D yp) (wps @ [wp])"
      hence "ipurge_tr I (c_dom D) (c_dom D yp) (wps @ [wp]) =
        ipurge_tr I (c_dom D) (c_dom D yp) wps"
       by simp
      moreover have "ipurge_ref I (c_dom D) (c_dom D yp) (wps @ [wp]) Z =
        ipurge_ref I (c_dom D) (c_dom D yp) wps ?Z'"
       using D by (rule ipurge_ref_eq)
      ultimately show "(yp # ipurge_tr I (c_dom D) (c_dom D yp) (wps @ [wp]),
        ipurge_ref I (c_dom D) (c_dom D yp) (wps @ [wp]) Z)
        \<in> futures (c_process step out s\<^sub>0) xps"
       by simp
    next
      let ?xs = "map fst xps"
      let ?y = "fst yp"
      let ?ws = "map fst wps"
      let ?w = "fst wp"
      let ?s = "foldl step s\<^sub>0 ?xs"
      let ?s' = "foldl step s\<^sub>0 (?xs @ [?y])"
      have "((xps @ [yp]) @ yps, Y) \<in> failures (c_process step out s\<^sub>0)"
       using Y by (simp add: c_futures_failures c_failures_failures)
      hence "(xps @ [yp], {}) \<in> failures (c_process step out s\<^sub>0)"
       by (rule process_rule_2_failures)
      hence "(xps @ [yp], {}) \<in> c_failures step out s\<^sub>0"
       by (simp add: c_failures_failures)
      hence "xps @ [yp] = c_tr step out s\<^sub>0 (map fst (xps @ [yp]))"
       by (rule c_failures_tr)
      hence XY: "xps @ [yp] = c_tr step out s\<^sub>0 (?xs @ [?y])" by simp
      hence X: "xps = c_tr step out s\<^sub>0 ?xs" by simp
      have "([yp] @ yps, Y) \<in> futures (c_process step out s\<^sub>0) xps"
       using Y by simp
      hence "([yp], {}) \<in> futures (c_process step out s\<^sub>0) xps"
       by (rule process_rule_2_futures)
      hence "[yp] = c_tr step out ?s (map fst [yp])" by (rule c_futures_tr)
      hence Y': "[yp] = c_tr step out ?s ([?y])" by simp
      have W: "(wps, {}) \<in> futures (c_process step out s\<^sub>0) xps"
       using B' by (rule process_rule_2_futures)
      hence W': "wps = c_tr step out (foldl step s\<^sub>0 ?xs) ?ws" by (rule c_futures_tr)
      assume D: "c_dom D wp \<notin> sinks I (c_dom D) (c_dom D yp) (wps @ [wp])"
      hence "ipurge_tr I (c_dom D) (c_dom D yp) (wps @ [wp]) =
        ipurge_tr I (c_dom D) (c_dom D yp) wps @ [wp]"
       by simp
      hence "ipurge_tr I (c_dom D) (c_dom D yp) (wps @ [wp]) =
        ipurge_tr I (c_dom D) (c_dom D yp)
        (c_tr step out (foldl step s\<^sub>0 ?xs) ?ws) @ [wp]"
       using W' by simp
      also have "\<dots> =
        ipurge_tr I (c_dom D) (c_dom D yp) (c_tr step out ?s' ?ws) @ [wp]"
       using R and S by (simp add: c_secure_ipurge_tr c_dom_def)
      also have "\<dots> = c_tr step out ?s' (ipurge_tr I D (c_dom D yp) ?ws) @ [wp]"
      proof (simp del: foldl_append, rule c_tr_ipurge_tr)
        fix n
        let ?wps' = "c_tr step out ?s (take n ?ws)"
        have "length ?wps' < length zps \<longrightarrow>
          (\<forall>Z'. (?wps', Z') \<in> futures (c_process step out s\<^sub>0) xps \<longrightarrow>
          (yp # ipurge_tr I (c_dom D) (c_dom D yp) ?wps',
          ipurge_ref I (c_dom D) (c_dom D yp) ?wps' Z')
          \<in> futures (c_process step out s\<^sub>0) xps)"
         using A ..
        moreover have "length ?wps' < length zps"
         using C by (simp add: c_tr_length)
        ultimately have "\<forall>Z'.
          (?wps', Z') \<in> futures (c_process step out s\<^sub>0) xps \<longrightarrow>
          (yp # ipurge_tr I (c_dom D) (c_dom D yp) ?wps',
          ipurge_ref I (c_dom D) (c_dom D yp) ?wps' Z')
          \<in> futures (c_process step out s\<^sub>0) xps" ..
        hence "(?wps', {}) \<in> futures (c_process step out s\<^sub>0) xps \<longrightarrow>
          (yp # ipurge_tr I (c_dom D) (c_dom D yp) ?wps',
          ipurge_ref I (c_dom D) (c_dom D yp) ?wps' {})
          \<in> futures (c_process step out s\<^sub>0) xps"
         (is "_ \<longrightarrow> (_, ?W') \<in> _") ..
        moreover have "wps = c_tr step out ?s (take n ?ws @ drop n ?ws)"
         using W' by simp
        hence "wps = ?wps' @
          c_tr step out (foldl step ?s (take n ?ws)) (drop n ?ws)"
         by (simp only: c_tr_append)
        hence "(?wps' @ c_tr step out (foldl step ?s (take n ?ws)) (drop n ?ws), {})
          \<in> futures (c_process step out s\<^sub>0) xps"
         using W by simp
        hence "(?wps', {}) \<in> futures (c_process step out s\<^sub>0) xps"
         by (rule process_rule_2_futures)
        ultimately have "(yp # ipurge_tr I (c_dom D) (c_dom D yp) ?wps', ?W')
          \<in> futures (c_process step out s\<^sub>0) xps" ..
        hence "(c_tr step out s\<^sub>0 (?xs @ [?y]) @
          ipurge_tr I (c_dom D) (c_dom D yp) ?wps', ?W')
          \<in> c_failures step out s\<^sub>0"
         using XY by (simp add: c_futures_failures)
        hence "(ipurge_tr I (c_dom D) (c_dom D yp) ?wps', ?W')
          \<in> futures (c_process step out s\<^sub>0) (c_tr step out s\<^sub>0 (?xs @ [?y]))"
         by (simp add: c_futures_failures)
        hence "(ipurge_tr I (c_dom D) (c_dom D yp)
          (c_tr step out ?s' (take n ?ws)), ?W')
          \<in> futures (c_process step out s\<^sub>0) (c_tr step out s\<^sub>0 (?xs @ [?y]))"
         using R and S by (simp add: c_dom_def c_secure_ipurge_tr)
        thus "\<exists>W. (ipurge_tr I (c_dom D) (c_dom D yp)
          (c_tr step out ?s' (take n ?ws)), W)
          \<in> futures (c_process step out s\<^sub>0) (c_tr step out s\<^sub>0 (?xs @ [?y]))"
         by (rule_tac x = ?W' in exI)
      qed
      finally have E: "ipurge_tr I (c_dom D) (c_dom D yp) (wps @ [wp]) =
        c_tr step out ?s' (ipurge_tr I D (c_dom D yp) ?ws) @ [wp]" .
      have "(xps @ wps @ [wp], Z) \<in> c_failures step out s\<^sub>0"
       (is "(?xps', _) \<in> _") using B' by (simp add: c_futures_failures)
      moreover have "?xps' \<noteq> []" by simp
      ultimately have "snd (last ?xps') =
        out (foldl step s\<^sub>0 (butlast (map fst ?xps'))) (last (map fst ?xps'))"
       by (rule c_failures_last)
      hence "snd wp = out (foldl step s\<^sub>0 (?xs @ ?ws)) ?w"
       by (simp add: butlast_append)
      hence "snd wp = out (foldl step s\<^sub>0 (c_ipurge I D (D ?w) (?xs @ ?ws))) ?w"
       using S by (simp add: c_secure_def)
      moreover have F: "D ?w \<notin> sinks I D (c_dom D yp) (?ws @ [?w])"
       using D by (simp only: c_dom_sinks, simp add: c_dom_def)
      have G: "\<not> (\<exists>v \<in> sinks I D (c_dom D yp) ?ws. (v, D ?w) \<in> I)"
      proof
        assume "\<exists>v \<in> sinks I D (c_dom D yp) ?ws. (v, D ?w) \<in> I"
        hence "D ?w \<in> sinks I D (c_dom D yp) (?ws @ [?w])" by simp
        thus False using F by contradiction
      qed
      ultimately have "snd wp = out (foldl step s\<^sub>0
        (c_ipurge I D (D ?w) (?xs @ ipurge_tr I D (c_dom D yp) ?ws))) ?w"
       using R by (simp add: c_ipurge_ipurge_tr)
      hence "snd wp = out (foldl step s\<^sub>0
        (c_ipurge I D (D ?w) (?xs @ ipurge_tr I D (c_dom D yp) (?y # ?ws)))) ?w"
       using R by (simp add: c_dom_def ipurge_tr_cons_same)
      moreover have
        "\<not> (\<exists>v \<in> sinks I D (c_dom D yp) (?y # ?ws). (v, D ?w) \<in> I)"
      proof (rule notI, simp add: sinks_cons_same c_dom_def R G [simplified])
        assume "(D ?y, D ?w) \<in> I"
        hence "D ?w \<in> sinks I D (c_dom D yp) (?ws @ [?w])"
         by (simp add: c_dom_def)
        thus False using F by contradiction
      qed
      ultimately have "snd wp =
        out (foldl step s\<^sub>0 (c_ipurge I D (D ?w) (?xs @ [?y] @ ?ws))) ?w"
       using R by (simp add: c_ipurge_ipurge_tr)
      moreover have "c_ipurge I D (D ?w) ((?xs @ [?y]) @
        ipurge_tr I D (c_dom D yp) ?ws) =
        c_ipurge I D (D ?w) ((?xs @ [?y]) @ ?ws)"
       using R and G by (rule c_ipurge_ipurge_tr)
      ultimately have "snd wp = out (foldl step s\<^sub>0
        (c_ipurge I D (D ?w) (?xs @ [?y] @ ipurge_tr I D (c_dom D yp) ?ws))) ?w"
       by simp
      hence "snd wp =
        out (foldl step s\<^sub>0 (?xs @ [?y] @ ipurge_tr I D (c_dom D yp) ?ws)) ?w"
       using S by (simp add: c_secure_def)
      hence "yp # ipurge_tr I (c_dom D) (c_dom D yp) (wps @ [wp]) =
        c_tr step out ?s ([?y]) @
        c_tr step out ?s' (ipurge_tr I D (c_dom D yp) ?ws) @
        [(?w, out (foldl step ?s' (ipurge_tr I D (c_dom D yp) ?ws)) ?w)]"
       using Y' and E by (cases wp, simp)
      hence "yp # ipurge_tr I (c_dom D) (c_dom D yp) (wps @ [wp]) =
        c_tr step out ?s ([?y]) @
        c_tr step out ?s' (ipurge_tr I D (c_dom D yp) ?ws) @
        c_tr step out (foldl step ?s' (ipurge_tr I D (c_dom D yp) ?ws)) [?w]"
       by (simp add: c_tr_singleton)
      hence "yp # ipurge_tr I (c_dom D) (c_dom D yp) (wps @ [wp]) =
        c_tr step out ?s ([?y]) @
        c_tr step out (foldl step ?s [?y]) (ipurge_tr I D (c_dom D yp) ?ws @ [?w])"
       by (simp add: c_tr_append)
      hence "yp # ipurge_tr I (c_dom D) (c_dom D yp) (wps @ [wp]) =
        c_tr step out ?s ([?y] @ ipurge_tr I D (c_dom D yp) ?ws @ [?w])"
       by (simp only: c_tr_append)
      moreover have
        "(c_tr step out ?s (?y # ipurge_tr I D (c_dom D yp) ?ws @ [?w]),
        {(x, p). p \<noteq> out (foldl step ?s
        (?y # ipurge_tr I D (c_dom D yp) ?ws @ [?w])) x})
        \<in> futures (c_process step out s\<^sub>0) (c_tr step out s\<^sub>0 ?xs)"
       (is "(_, ?Z') \<in> _") by (rule c_tr_futures)
      ultimately have
        "(xps @ yp # ipurge_tr I (c_dom D) (c_dom D yp) (wps @ [wp]), ?Z')
        \<in> c_failures step out s\<^sub>0"
       using X by (simp add: c_futures_failures)
      moreover have
        "ipurge_ref I (c_dom D) (c_dom D yp) (wps @ [wp]) Z \<subseteq> ?Z'"
      proof (rule subsetI, simp add: split_paired_all ipurge_ref_def c_dom_def
       del: sinks.simps foldl.simps, (erule conjE)+)
        fix x p
        assume
          H: "\<forall>v \<in> sinks I (c_dom D) (D ?y) (wps @ [wp]). (v, D x) \<notin> I" and
          I: "(D ?y, D x) \<notin> I"
        have "(xps @ wps @ [wp], Z) \<in> c_failures step out s\<^sub>0"
         using B' by (simp add: c_futures_failures)
        hence "Z \<subseteq> {(x', p'). p' \<noteq>
          out (foldl step s\<^sub>0 (map fst (xps @ wps @ [wp]))) x'}"
         by (rule c_failures_ref)
        hence "Z \<subseteq> {(x', p'). p' \<noteq>
          out (foldl step s\<^sub>0 (?xs @ ?ws @ [?w])) x'}"
         by simp
        moreover assume "(x, p) \<in> Z"
        ultimately have "(x, p) \<in> {(x', p'). p' \<noteq>
          out (foldl step s\<^sub>0 (?xs @ ?ws @ [?w])) x'}" ..
        hence "p \<noteq> out (foldl step s\<^sub>0
          (c_ipurge I D (D x) (?xs @ ?ws @ [?w]))) x"
         using S by (simp add: c_secure_def)
        moreover have
          J: "\<not> (\<exists>v \<in> sinks I D (D ?y) (?ws @ [?w]). (v, D x) \<in> I)"
        proof (rule notI,
         cases "(D ?y, D ?w) \<in> I \<or> (\<exists>v \<in> sinks I D (D ?y) ?ws. (v, D ?w) \<in> I)",
         simp_all only: sinks.simps if_True if_False)
          case True
          hence "c_dom D wp \<in> sinks I (c_dom D) (c_dom D yp) (wps @ [wp])"
           by (simp only: c_dom_sinks, simp add: c_dom_def)
          thus False using D by contradiction
        next
          assume "\<exists>v \<in> sinks I D (D ?y) ?ws. (v, D x) \<in> I"
          then obtain v where
            A: "v \<in> sinks I D (D ?y) ?ws" and
            B: "(v, D x) \<in> I" ..
          have "v \<in> sinks I (c_dom D) (D ?y) (wps @ [wp])"
           using A by (simp add: c_dom_sinks)
          with H have "(v, D x) \<notin> I" ..
          thus False using B by contradiction
        qed
        ultimately have "p \<noteq> out (foldl step s\<^sub>0 (c_ipurge I D (D x)
          (?xs @ ipurge_tr I D (D ?y) (?ws @ [?w])))) x"
         using R by (simp add: c_ipurge_ipurge_tr del: ipurge_tr.simps)
        hence "p \<noteq> out (foldl step s\<^sub>0 (c_ipurge I D (D x)
          (?xs @ ipurge_tr I D (D ?y) (?y # ?ws @ [?w])))) x"
         using R by (simp add: ipurge_tr_cons_same)
        moreover have
          "\<not> (\<exists>v \<in> sinks I D (D ?y) (?y # ?ws @ [?w]). (v, D x) \<in> I)"
        proof
          assume "\<exists>v \<in> sinks I D (D ?y) (?y # ?ws @ [?w]). (v, D x) \<in> I"
          then obtain v where
            A: "v \<in> sinks I D (D ?y) (?y # ?ws @ [?w])" and
            B: "(v, D x) \<in> I" ..
          have "v = D ?y \<or> v \<in> sinks I D (D ?y) (?ws @ [?w])"
           using R and A by (simp add: sinks_cons_same)
          moreover {
            assume "v = D ?y"
            hence "(D ?y, D x) \<in> I" using B by simp
            hence False using I by contradiction
          }
          moreover {
            assume "v \<in> sinks I D (D ?y) (?ws @ [?w])"
            with B have "\<exists>v \<in> sinks I D (D ?y) (?ws @ [?w]). (v, D x) \<in> I" ..
            hence False using J by contradiction
          }
          ultimately show False by blast
        qed
        ultimately have "p \<noteq> out (foldl step s\<^sub>0 (c_ipurge I D (D x)
          (?xs @ [?y] @ ?ws @ [?w]))) x"
         using R by (simp add: c_ipurge_ipurge_tr del: ipurge_tr.simps)
        moreover have "c_ipurge I D (D x) ((?xs @ [?y]) @
          ipurge_tr I D (D ?y) (?ws @ [?w])) =
          c_ipurge I D (D x) ((?xs @ [?y]) @ ?ws @ [?w])"
         using R and J by (rule c_ipurge_ipurge_tr)
        ultimately have "p \<noteq> out (foldl step s\<^sub>0 (c_ipurge I D (D x)
          (?xs @ ?y # ipurge_tr I D (D ?y) (?ws @ [?w])))) x"
         by simp
        hence "p \<noteq> out (foldl step s\<^sub>0
          (?xs @ ?y # ipurge_tr I D (D ?y) (?ws @ [?w]))) x"
         using S by (simp add: c_secure_def)
        thus "p \<noteq> out (foldl step ?s
          (?y # ipurge_tr I D (D ?y) ?ws @ [?w])) x"
         using F by (simp add: c_dom_def)
      qed
      ultimately have
        "(xps @ yp # ipurge_tr I (c_dom D) (c_dom D yp) (wps @ [wp]),
        ipurge_ref I (c_dom D) (c_dom D yp) (wps @ [wp]) Z)
        \<in> c_failures step out s\<^sub>0"
       by (rule R2)
      thus "(yp # ipurge_tr I (c_dom D) (c_dom D yp) (wps @ [wp]),
        ipurge_ref I (c_dom D) (c_dom D yp) (wps @ [wp]) Z)
        \<in> futures (c_process step out s\<^sub>0) xps"
       by (simp add: c_futures_failures)
    qed
  qed
qed

theorem c_secure_implies_secure:
  assumes R: "refl I" and S: "c_secure step out s\<^sub>0 I D"
  shows "secure (c_process step out s\<^sub>0) I (c_dom D)"
proof (simp only: secure_def, (rule allI)+, rule impI, erule conjE)
  fix xps yp yps Y zps Z
  assume
    Y: "(yp # yps, Y) \<in> futures (c_process step out s\<^sub>0) xps" and
    Z: "(zps, Z) \<in> futures (c_process step out s\<^sub>0) xps"
  show "(ipurge_tr I (c_dom D) (c_dom D yp) yps,
    ipurge_ref I (c_dom D) (c_dom D yp) yps Y)
    \<in> futures (c_process step out s\<^sub>0) xps \<and>
    (yp # ipurge_tr I (c_dom D) (c_dom D yp) zps,
    ipurge_ref I (c_dom D) (c_dom D yp) zps Z)
    \<in> futures (c_process step out s\<^sub>0) xps"
   (is "?P \<and> ?Q")
  proof
    show ?P using R and S and Y
     by (rule c_secure_implies_secure_aux_1)
  next
    show ?Q using R and S and Y and Z
     by (rule c_secure_implies_secure_aux_2)
  qed
qed

theorem secure_equals_c_secure:
 "refl I \<Longrightarrow> secure (c_process step out s\<^sub>0) I (c_dom D) = c_secure step out s\<^sub>0 I D"
by (rule iffI, rule secure_implies_c_secure, assumption, rule c_secure_implies_secure)

end
