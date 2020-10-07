section \<open>Preliminaries\<close>

theory Preliminaries
imports Main LatticeProperties.Complete_Lattice_Prop 
  LatticeProperties.Conj_Disj
begin

notation
  less_eq (infix "\<sqsubseteq>" 50) and
  less (infix "\<sqsubset>" 50) and
  inf (infixl "\<sqinter>" 70) and
  sup (infixl "\<squnion>" 65) and
  top ("\<top>") and
  bot ("\<bottom>") and
  Inf ("\<Sqinter>_" [900] 900) and
  Sup ("\<Squnion>_" [900] 900)

subsection \<open>Simplification Lemmas\<close>

declare fun_upd_idem[simp]

lemma simp_eq_emptyset:
  "(X = {}) = (\<forall> x. x \<notin> X)"
  by blast

lemma mono_comp: "mono f \<Longrightarrow> mono g \<Longrightarrow> mono (f o g)" 
  by (unfold mono_def) auto

text \<open>Some lattice simplification rules\<close>

lemma inf_bot_bot: (* FIXME *)
  "(x::'a::{semilattice_inf,order_bot}) \<sqinter> \<bottom> = \<bottom>"
  apply (rule antisym)
  by auto

end
