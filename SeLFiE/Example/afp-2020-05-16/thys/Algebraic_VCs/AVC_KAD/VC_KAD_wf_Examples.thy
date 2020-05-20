(* Title: Verification Component Based on Divergence Kleene Algebra for Total Correctness: Examples
   Author: Victor Gomes, Georg Struth
   Maintainer: Victor Gomes <victor.gomes@cl.cam.ac.uk>
               Georg Struth <g.struth@sheffield.ac.uk> 
*)

subsubsection\<open>Verification Examples\<close>

theory VC_KAD_wf_Examples
  imports VC_KAD_wf
begin

text \<open>The example should be taken with a grain of salt. More work is needed to make 
the while rule cooperate with simplification.\<close>

lemma euclid:
  "rel_nabla (
    \<lceil>\<lambda>s::nat store. 0 < s ''y''\<rceil> ; 
      ((''z'' ::= (\<lambda>s. s ''y'')) ; 
      (''y'' ::= (\<lambda>s. s ''x'' mod s ''y'')) ;
      (''x'' ::= (\<lambda>s. s ''z'')))) 
    = {}
    \<Longrightarrow>
  PRE (\<lambda>s::nat store. s ''x'' = x \<and> s ''y'' = y)
   (WHILE (\<lambda>s. s ''y'' \<noteq> 0) INV (\<lambda>s. gcd (s ''x'') (s ''y'') = gcd x y) 
    DO
     (''z'' ::= (\<lambda>s. s ''y''));
     (''y'' ::= (\<lambda>s. s ''x'' mod s ''y''));
     (''x'' ::= (\<lambda>s. s ''z''))
    OD)
   POST (\<lambda>s. s ''x'' = gcd x y)"
  apply (subst rel_fdivka.fbox_arden_whilei[symmetric], simp_all)
  using gcd_red_nat gr0I by force

text \<open>The termination assumption is now explicit in the verification proof. Here it is left 
untouched. Means beyond these components are required for discharging it.\<close>

end
