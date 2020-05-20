theory Simpl_Anno imports Simpl.Vcg begin

definition "named_loop name = UNIV"

lemma annotate_named_loop_inv:
  "whileAnno b (named_loop name) V c = whileAnno b I V c"
  by (simp add: whileAnno_def)

lemma annotate_named_loop_inv_fix:
  "whileAnno b (named_loop name) V c = whileAnnoFix b I (\<lambda>_. V) (\<lambda>_. c)"
  by (simp add: whileAnno_def whileAnnoFix_def)

lemma annotate_named_loop_var:
  "whileAnno b (named_loop name) V' c = whileAnno b I V c"
  by (simp add: whileAnno_def)

lemma annotate_named_loop_var_fix:
  "whileAnno b (named_loop name) V' c = whileAnnoFix b I (\<lambda>_. V) (\<lambda>_. c)"
  by (simp add: whileAnno_def whileAnnoFix_def)


end
