theory "Env-Set-Cpo"
imports Launchbury.Env "Set-Cpo"
begin

lemma cont_edom[THEN cont_compose, simp, cont2cont]:
  "cont (\<lambda> f. edom f)"
  apply (rule set_contI)
  apply (auto simp add: edom_def)
  apply (metis ch2ch_fun lub_eq_bottom_iff lub_fun)
  apply (metis ch2ch_fun lub_eq_bottom_iff lub_fun)
  done

end
