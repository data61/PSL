(* Title: Verification Component Based on KAT: Examples
   Author: Victor Gomes, Georg Struth
   Maintainer: Victor Gomes <victor.gomes@cl.cam.ac.uk>
               Georg Struth <g.struth@sheffield.ac.uk> 
*)

subsubsection \<open>Verification Examples\<close>

theory VC_KAT_Examples
  imports VC_KAT
begin

lemma euclid:
  "PRE (\<lambda>s::nat store. s ''x'' = x \<and> s ''y'' = y)
   (WHILE (\<lambda>s. s ''y'' \<noteq> 0) INV (\<lambda>s. gcd (s ''x'') (s ''y'') = gcd x y) 
    DO
     (''z'' ::= (\<lambda>s. s ''y''));
     (''y'' ::= (\<lambda>s. s ''x'' mod s ''y''));
     (''x'' ::= (\<lambda>s. s ''z''))
    OD)
   POST (\<lambda>s. s ''x'' = gcd x y)"
  apply (rule sH_while_inv)
  apply simp_all
  apply force
  apply (intro rel_kat.H_seq)
  apply (subst H_assign, simp)+
  apply (intro H_assign_var)
  using gcd_red_nat by auto

lemma maximum: 
  "PRE (\<lambda>s:: nat store. True)
   (IF (\<lambda>s. s ''x'' \<ge> s ''y'') 
    THEN (''z'' ::= (\<lambda>s. s ''x''))
    ELSE (''z'' ::= (\<lambda>s. s ''y''))
    FI)
   POST (\<lambda>s. s ''z'' = max (s ''x'') (s ''y''))"
  by auto

lemma integer_division: 
  "PRE (\<lambda>s::nat store. s ''x'' \<ge> 0)
    (''q'' ::= (\<lambda>s. 0)); 
    (''r'' ::= (\<lambda>s. s ''x''));
    (WHILE (\<lambda>s. s ''y'' \<le> s ''r'') INV (\<lambda>s. s ''x'' = s ''q'' * s ''y'' + s ''r'' \<and> s ''r'' \<ge> 0)
     DO
      (''q'' ::= (\<lambda>s. s ''q'' + 1));
      (''r'' ::= (\<lambda>s. s ''r'' - s ''y''))
      OD)
   POST (\<lambda>s. s ''x'' = s ''q'' * s ''y'' + s ''r'' \<and> s ''r'' \<ge> 0 \<and> s ''r'' < s ''y'')"
  apply (intro rel_kat.H_seq, subst sH_while_inv, simp_all)
  apply auto[1]
  apply (intro rel_kat.H_seq)
  by (subst H_assign, simp_all)+

lemma imp_reverse:
  "PRE (\<lambda>s:: 'a list store. s ''x'' = X)
   (''y'' ::= (\<lambda>s. []));
   (WHILE (\<lambda>s. s ''x'' \<noteq> []) INV (\<lambda>s. rev (s ''x'') @ s ''y'' = rev X)
    DO 
     (''y'' ::= (\<lambda>s. hd (s ''x'') # s ''y'')); 
     (''x'' ::= (\<lambda>s. tl (s ''x'')))
    OD) 
   POST (\<lambda>s. s ''y''= rev X )"
  apply (intro rel_kat.H_seq, rule sH_while_inv)
  apply auto[2]
  apply (rule rel_kat.H_seq, rule H_assign_var)
  apply auto[1]
  apply (rule H_assign_var)
  apply (clarsimp, metis append.simps(1) append.simps(2) append_assoc hd_Cons_tl rev.simps(2))
  by simp

end
