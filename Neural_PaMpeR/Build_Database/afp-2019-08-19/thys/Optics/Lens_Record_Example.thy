theory Lens_Record_Example
imports Lens_Instances
begin

text \<open>The alphabet command supports syntax illustrated in the following comments.\<close>

alphabet mylens =
  x :: nat
  y :: string

lemma mylens_bij_lens:
  "bij_lens (x +\<^sub>L y +\<^sub>L mylens_child_lens)"
  by (unfold_locales, simp_all add: lens_plus_def x_def y_def mylens_child_lens_def id_lens_def sublens_def lens_comp_def prod.case_eq_if)

alphabet mylens_2 = mylens +
  z :: int
  k :: "string list"

alphabet mylens_3 = mylens_2 +
  n :: real
  h :: nat

end
