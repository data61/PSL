(*
    Authors:      Jose Divasón
                  Sebastiaan Joosten
                  René Thiemann
                  Akihisa Yamada
*)
theory Code_Abort_Gcd
imports   
  "HOL-Computational_Algebra.Polynomial_Factorial"
begin

text \<open>Dummy code-setup for @{const Gcd} and @{const Lcm} in the presence of 
  Container.\<close>

definition dummy_Gcd where "dummy_Gcd x = Gcd x" 
definition dummy_Lcm where "dummy_Lcm x = Lcm x" 
declare  [[code abort: dummy_Gcd]]

lemma dummy_Gcd_Lcm: "Gcd x = dummy_Gcd x" "Lcm x = dummy_Lcm x" 
  unfolding dummy_Gcd_def dummy_Lcm_def by auto

lemmas dummy_Gcd_Lcm_poly [code] = dummy_Gcd_Lcm [where ?'a = "'a :: factorial_ring_gcd poly"] 
lemmas dummy_Gcd_Lcm_int [code] = dummy_Gcd_Lcm [where ?'a = int] 
lemmas dummy_Gcd_Lcm_nat [code] = dummy_Gcd_Lcm [where ?'a = nat] 

declare [[code abort: Euclidean_Algorithm.Gcd Euclidean_Algorithm.Lcm]]

end
