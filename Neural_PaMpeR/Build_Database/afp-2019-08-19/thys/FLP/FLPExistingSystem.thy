section \<open>An Existing FLPSystem\<close>

theory FLPExistingSystem
imports FLPTheorem
begin

text \<open>
  We define an example FLPSystem with some example execution to show that the
  locales employed are not void. (If they were, the consensus impossibility
  result would be trivial.)
\<close>

subsection \<open>System definition\<close>

datatype proc = p0 | p1
datatype state = s0 | s1
datatype val = v0 | v1

primrec trans :: "proc \<Rightarrow> state \<Rightarrow> val messageValue \<Rightarrow> state"
where
  "trans p s0 v = s1"
| "trans p s1 v = s0"

primrec sends ::
  "proc \<Rightarrow> state \<Rightarrow> val messageValue \<Rightarrow> (proc, val) message multiset"
where
  "sends p s0 v = {# <p0, v1> }"
| "sends p s1 v = {# <p1, v0> }"

definition start :: "proc \<Rightarrow> state"
where "start p  \<equiv> s0"

\<comment> \<open>An example execution\<close>
definition exec ::
  "(proc, val, state ) configuration list"
where
  exec_def: "exec \<equiv> [ \<lparr> 
    states = (\<lambda>p. s0),
    msgs = ({# <p0, inM True> } \<union># {# <p1, inM True> }) \<rparr> ]"

lemma ProcUniv: "(UNIV :: proc set) = {p0, p1}"
  by (metis UNIV_eq_I insert_iff proc.exhaust)

subsection \<open>Interpretation as FLP Locale\<close>

interpretation FLPSys: flpSystem trans sends start
proof
  \<comment> \<open>finiteProcs\<close>
  show "finite (UNIV :: proc set)"
    unfolding ProcUniv by simp
next
  \<comment> \<open>minimalProcs\<close>
  have "card (UNIV :: proc set) = 2"
    unfolding ProcUniv by simp
  thus "2 \<le> card (UNIV :: proc set)" by simp
next
  \<comment> \<open>finiteSends\<close>
  fix p s m
  have FinExplSends: "finite {<p0, v1>, <p1, v0>}" by auto
  have "{v. 0 < sends p s m v} \<subseteq> {<p0, v1>, <p1, v0>}"
  proof auto
    fix x
    assume "x \<noteq> <p0, v1>" "0 < sends p s m x"
    thus "x = <p1, v0>"
      by (metis (full_types) neq0_conv sends.simps(1,2) state.exhaust)
  qed
  thus "finite {v. 0 < sends p s m v}"
    using FinExplSends finite_subset by blast
next
  \<comment> \<open>noInSends\<close>
  fix p s m p2 v
  show "sends p s m <p2, inM v> = 0" by (induct s, auto)
qed

interpretation FLPExec: execution trans sends start exec "[]"
proof
  \<comment> \<open>notEmpty\<close>
  show "1 \<le> length exec"
    by (simp add:exec_def)
next
  \<comment> \<open>length\<close>
  show "length exec - 1 = length []"
    by (simp add:exec_def)
next
  \<comment> \<open>base\<close>
  show "asynchronousSystem.initial start (hd exec)"
    unfolding asynchronousSystem.initial_def isReceiverOf_def
    by (auto simp add: start_def exec_def, metis proc.exhaust)
next
  \<comment> \<open>step\<close>
  fix i cfg1 cfg2
  assume "i < length exec - 1"
  hence "False" by (simp add:exec_def)
  thus "asynchronousSystem.steps FLPExistingSystem.trans sends cfg1 ([] ! i) cfg2"
    by rule
qed

end
