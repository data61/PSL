(* Title: Verification Component Based on KAT: Examples with Automated VCG
   Author: Victor Gomes, Georg Struth
   Maintainer: Victor Gomes <victor.gomes@cl.cam.ac.uk>
               Georg Struth <g.struth@sheffield.ac.uk> 
*)

subsubsection \<open>Verification Examples with Automated VCG\<close>

theory VC_KAT_Examples2
  imports VC_KAT "HOL-Eisbach.Eisbach"
begin

text \<open>The following simple tactic for verification condition generation has been 
implemented with the Eisbach proof methods language.\<close>

named_theorems hl_intro

declare sH_while_inv [hl_intro]
  rel_kat.H_seq [hl_intro]
  H_assign_var [hl_intro]
  rel_kat.H_cond [hl_intro]

method hoare = (rule hl_intro; hoare?)

lemma euclid:
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
   by hoare auto

lemma imp_reverse:
  "PRE (\<lambda>s:: 'a list store. s ''x'' = X)
   (''y'' ::= (\<lambda>s. []));
   (WHILE (\<lambda>s. s ''x'' \<noteq> []) INV (\<lambda>s. rev (s ''x'') @ s ''y'' = rev X)
    DO 
     (''y'' ::= (\<lambda>s. hd (s ''x'') # s ''y'')); 
     (''x'' ::= (\<lambda>s. tl (s ''x'')))
    OD) 
   POST (\<lambda>s. s ''y''= rev X )"
   apply hoare 
   apply auto[3]
   apply (clarsimp, metis (no_types, lifting) Cons_eq_appendI append_eq_append_conv2 hd_Cons_tl rev.simps(2) self_append_conv)
   by simp

end
