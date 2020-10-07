theory Example_PaMpeR
imports "PaMpeR.PaMpeR"
begin

lemma "rev xs = rev (rev xs)"
  which_method
  why_method induct
  rank_method induct
  oops

end