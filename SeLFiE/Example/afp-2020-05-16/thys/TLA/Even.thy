(*  Title:       A Definitional Encoding of TLA in Isabelle/HOL
    Authors:     Gudmund Grov <ggrov at inf.ed.ac.uk>
                 Stephan Merz <Stephan.Merz at loria.fr>
    Year:        2011
    Maintainer:  Gudmund Grov <ggrov at inf.ed.ac.uk>
*)

section \<open>A simple illustrative example\<close>

theory Even
imports State 
begin

text\<open>
  A trivial example illustrating invariant proofs in the logic, and how
  Isabelle/HOL can help with specification. It proves that \<open>x\<close> is
  always even in a program where \<open>x\<close> is initialized as 0 and
  always incremented by 2.
\<close>

inductive_set
  Even :: "nat set"
where
  even_zero: "0 \<in> Even"
| even_step: "n \<in> Even \<Longrightarrow> Suc (Suc n) \<in> Even"

locale Program =
  fixes x :: "state \<Rightarrow> nat"
  and init :: "temporal"
  and act :: "temporal"
  and phi :: "temporal"
  defines "init \<equiv> TEMP $x = # 0"
  and "act \<equiv> TEMP x` = Suc<Suc<$x>>"
  and "phi \<equiv> TEMP init \<and> \<box>[act]_x"

lemma (in Program) stutinvprog: "STUTINV phi"
  by (auto simp: phi_def init_def act_def stutinvs nstutinvs)

lemma  (in Program) inveven: "\<turnstile> phi \<longrightarrow> \<box>($x \<in> # Even)"
  unfolding phi_def
proof (rule invmono)
  show "\<turnstile> init \<longrightarrow> $x \<in> #Even"
    by (auto simp: init_def even_zero)
next
  show "|~ $x \<in> #Even \<and> [act]_x \<longrightarrow> \<circle>($x \<in> #Even)"
    by (auto simp: act_def even_step tla_defs)
qed


end
