(* 
   Title: The pi-calculus   
   Author/Maintainer: Jesper Bengtson (jebe.dk), 2012
*)
theory Late_Semantics1
  imports Late_Semantics
begin

free_constructors case_subject for
  InputS
| BoundOutputS
by(auto simp add: subject.inject)
  (metis Rep_subject_inverse subject.constr_rep(1,2) subject_Rep.exhaust)

free_constructors case_freeRes for
  OutputR
| TauR
by(auto simp add: freeRes.inject)
  (metis Abs_freeRes_cases Abs_freeRes_inverse freeRes.constr_rep(1,2) freeRes_Rep.exhaust)

end
