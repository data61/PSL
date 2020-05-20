theory Lens_Record_Example
  imports Optics
begin

text \<open>The alphabet command supports syntax illustrated in the following comments.\<close>

alphabet mylens =
  x :: nat
  y :: string

thm base_more_bij_lens
thm indeps
thm equivs
thm sublenses
thm quotients
thm compositions

lemma mylens_composition: 
  "x +\<^sub>L y +\<^sub>L more\<^sub>L \<approx>\<^sub>L 1\<^sub>L" (is "?P \<approx>\<^sub>L ?Q")
proof -
  have "?Q \<approx>\<^sub>L base\<^sub>L +\<^sub>L more\<^sub>L"
    by (simp add: lens_equiv_sym)
  also have "... \<approx>\<^sub>L (x +\<^sub>L y) +\<^sub>L more\<^sub>L"
    by (simp add: lens_plus_eq_left)
  also have "... \<approx>\<^sub>L x +\<^sub>L y +\<^sub>L more\<^sub>L"
    by (simp add: lens_plus_assoc)
  finally show ?thesis
    using lens_equiv_sym by auto
qed

lemma mylens_bij_lens:
  "bij_lens (x +\<^sub>L y +\<^sub>L more\<^sub>L)"
  using bij_lens_equiv_id mylens_composition by auto

alphabet mylens_2 = mylens +
  z :: int
  k :: "string list"

thm lens_defs

thm base_more_bij_lens
thm indeps
thm equivs
thm sublenses

alphabet mylens_3 = mylens_2 +
  n :: real
  h :: nat

thm base_more_bij_lens
thm indeps
thm equivs
thm sublenses

end
