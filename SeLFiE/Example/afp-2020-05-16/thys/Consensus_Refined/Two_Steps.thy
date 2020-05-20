(*<*)
theory Two_Steps
imports Consensus_Misc
begin
(*>*)
subsection \<open>Step definitions for 2-step algorithms\<close>

definition two_phase where "two_phase (r::nat) \<equiv> r div 2"

definition two_step where "two_step (r::nat) \<equiv> r mod 2"

lemma two_phase_zero [simp]: "two_phase 0 = 0"
by (simp add: two_phase_def)

lemma two_step_zero [simp]: "two_step 0 = 0"
by (simp add: two_step_def)

lemma two_phase_step: "(two_phase r * 2) + two_step r = r"
  by (auto simp add: two_phase_def two_step_def)

lemma two_step_phase_Suc:
  "two_step r = 0 \<Longrightarrow> two_phase (Suc r) = two_phase r"
  "two_step r = 0 \<Longrightarrow> two_step (Suc r) = 1"
  "two_step r = 0 \<Longrightarrow> two_phase (Suc (Suc r)) = Suc (two_phase r)"
  "two_step r = (Suc 0) \<Longrightarrow> two_phase (Suc r) = Suc (two_phase r)"
  "two_step r = (Suc 0) \<Longrightarrow> two_step (Suc r) = 0"
  by(simp_all add: two_step_def two_phase_def mod_Suc div_Suc)

end
