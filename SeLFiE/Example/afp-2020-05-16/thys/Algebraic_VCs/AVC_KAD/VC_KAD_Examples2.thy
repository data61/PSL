(* Title: Verification Component Based on KAD: Examples with Automated VCG
   Author: Victor Gomes, Georg Struth
   Maintainer: Victor Gomes <victor.gomes@cl.cam.ac.uk>
               Georg Struth <g.struth@sheffield.ac.uk> 
*)

subsubsection\<open>Verification Examples with Automated VCG\<close>

theory VC_KAD_Examples2
imports VC_KAD "HOL-Eisbach.Eisbach"
begin

text \<open>We have provide a simple tactic in the Eisbach proof method language. Additional simplification
steps are sometimes needed to bring the resulting verification conditions into shape for first-order automated
theorem proving.\<close>


named_theorems ht

declare rel_antidomain_kleene_algebra.fbox_whilei [ht]
  rel_antidomain_kleene_algebra.fbox_seq_var [ht]
  subset_refl[ht]

method hoare = (rule ht; hoare?)

lemma euclid2:
  "PRE (\<lambda>s::nat store. s ''x'' = x \<and> s ''y'' = y)
   (WHILE (\<lambda>s. s ''y'' \<noteq> 0) INV (\<lambda>s. gcd (s ''x'') (s ''y'') = gcd x y) 
    DO
     (''z'' ::= (\<lambda>s. s ''y''));
     (''y'' ::= (\<lambda>s. s ''x'' mod s ''y''));
     (''x'' ::= (\<lambda>s. s ''z''))
    OD)
   POST (\<lambda>s. s ''x'' = gcd x y)"
  apply hoare
  using gcd_red_nat by auto

lemma euclid_diff2: 
   "PRE (\<lambda>s::nat store. s ''x'' = x \<and> s ''y'' = y \<and> x > 0 \<and> y > 0)
    (WHILE (\<lambda>s. s ''x''\<noteq> s ''y'') INV (\<lambda>s. gcd (s ''x'') (s ''y'') = gcd x y) 
     DO
        (IF (\<lambda>s. s ''x'' >  s ''y'')
         THEN (''x'' ::= (\<lambda>s. s ''x'' - s ''y''))
         ELSE (''y'' ::= (\<lambda>s. s ''y'' - s ''x''))
         FI)
    OD)
    POST (\<lambda>s. s ''x'' = gcd x y)"
  apply (hoare, simp_all) 
  apply auto[1]
  by (metis gcd.commute gcd_diff1_nat le_cases nat_less_le)

lemma integer_division2: 
  "PRE (\<lambda>s::nat store. x \<ge> 0)
    (''q'' ::= (\<lambda>s. 0)); 
    (''r'' ::= (\<lambda>s. x));
    (WHILE (\<lambda>s. y \<le> s ''r'') INV (\<lambda>s. x = s ''q'' * y + s ''r'' \<and> s ''r'' \<ge> 0)
     DO
      (''q'' ::= (\<lambda>s. s ''q'' + 1));
      (''r'' ::= (\<lambda>s. s ''r'' - y))
      OD)
   POST (\<lambda>s. x = s ''q'' * y + s ''r'' \<and> s ''r'' \<ge> 0 \<and> s ''r'' < y)"
   by hoare simp_all

lemma factorial2:
  "PRE (\<lambda>s::nat store. True)
   (''x'' ::= (\<lambda>s. 0));
   (''y'' ::= (\<lambda>s. 1));
   (WHILE (\<lambda>s. s ''x'' \<noteq> x0) INV (\<lambda>s. s ''y'' = fact (s ''x''))
   DO
     (''x'' ::= (\<lambda>s. s ''x'' + 1));
     (''y'' ::= (\<lambda>s. s ''y'' \<cdot> s ''x''))
   OD)
   POST (\<lambda>s. s ''y'' = fact x0)"
  by hoare simp_all

lemma my_power2:
  "PRE (\<lambda>s::nat store. True)
   (''i'' ::= (\<lambda>s. 0));
   (''y'' ::= (\<lambda>s. 1));
   (WHILE (\<lambda>s. s ''i'' < n) INV (\<lambda>s. s ''y'' = x ^ (s ''i'') \<and> s ''i'' \<le> n)
     DO
       (''y'' ::= (\<lambda>s. (s ''y'') * x));
       (''i'' ::= (\<lambda>s. s ''i'' + 1))
     OD)
   POST (\<lambda>s. s ''y'' = x ^ n)"
  by hoare auto

lemma imp_reverse2:
  "PRE (\<lambda>s:: 'a list store. s ''x'' = X)
   (''y'' ::= (\<lambda>s. []));
   (WHILE (\<lambda>s. s ''x'' \<noteq> []) INV (\<lambda>s. rev (s ''x'') @ s ''y'' = rev X)
    DO 
     (''y'' ::= (\<lambda>s. hd (s ''x'') # s ''y'')); 
     (''x'' ::= (\<lambda>s. tl (s ''x'')))
    OD) 
   POST (\<lambda>s. s ''y''= rev X )"
  apply (hoare, simp_all)
  apply auto[1]
  by (clarsimp, metis append.simps append_assoc hd_Cons_tl rev.simps(2))

end
