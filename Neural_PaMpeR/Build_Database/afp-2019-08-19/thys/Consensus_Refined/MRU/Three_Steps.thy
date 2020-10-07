(*<*)
theory Three_Steps
imports "../Consensus_Misc"
begin
(*>*)
subsection \<open>Step definitions for 3-step algorithms\<close>

abbreviation (input) "nr_steps \<equiv> 3"

definition three_phase where "three_phase (r::nat) \<equiv> r div nr_steps"

definition three_step where "three_step (r::nat) \<equiv> r mod nr_steps"

lemma three_phase_zero [simp]: "three_phase 0 = 0"
by (simp add: three_phase_def)

lemma three_step_zero [simp]: "three_step 0 = 0"
by (simp add: three_step_def)

lemma three_phase_step: "(three_phase r * nr_steps) + three_step r = r"
  by (auto simp add: three_phase_def three_step_def)

lemma three_step_Suc:
  "three_step r = 0 \<Longrightarrow> three_step (Suc (Suc r)) = 2"
  "three_step r = 0 \<Longrightarrow> three_step (Suc r) = 1"
  "three_step r = (Suc 0) \<Longrightarrow> three_step (Suc r) = 2"
  "three_step r = (Suc 0) \<Longrightarrow> three_step (Suc (Suc r)) = 0"
  "three_step r = (Suc (Suc 0)) \<Longrightarrow> three_step ((Suc r)) = 0"
  by(unfold three_step_def, simp_all add: mod_Suc)

lemma three_step_phase_Suc:
  "three_step r = 0 \<Longrightarrow> three_phase (Suc r) = three_phase r"
  "three_step r = 0 \<Longrightarrow> three_phase (Suc (Suc r)) = three_phase r"
  "three_step r = 0 \<Longrightarrow> three_phase (Suc (Suc (Suc r))) = Suc (three_phase r)"
  "three_step r = (Suc 0) \<Longrightarrow> three_phase (Suc r) = three_phase r"
  "three_step r = (Suc 0) \<Longrightarrow> three_phase (Suc (Suc r)) = Suc (three_phase r)"
  "three_step r = (Suc (Suc 0)) \<Longrightarrow> three_phase (Suc r) = Suc (three_phase r)"
  by(simp_all add: three_step_def three_phase_def mod_Suc div_Suc)

lemma three_step2_phase_Suc:
  "three_step r = 2 \<Longrightarrow> (3 * (Suc (three_phase r)) - 1) = r"
  apply(simp add: three_step_def three_phase_def)
  by (metis add_2_eq_Suc' mult_div_mod_eq)

lemma three_stepE:
  "\<lbrakk> three_step r = 0 \<Longrightarrow> P; three_step r = 1 \<Longrightarrow> P; three_step r = 2 \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by(unfold three_step_def, arith)

end
