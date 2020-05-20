(*  Title:      RSAPSS/Mod.thy

    Author:     Christina Lindenberg, Kai Wirt, Technische Universität Darmstadt
    Copyright:  2005 - Technische Universität Darmstadt 
*)

section "Leammata for modular arithmetic"

theory Mod
imports Main
begin

lemma divmultassoc: "a div (b*c) * (b*c) = ((a div (b * c)) * b)*(c::nat)"
  by (rule mult.assoc [symmetric])

lemma delmod: "(a::nat) mod (b*c) mod c = a mod c"
  by (rule mod_mod_cancel [OF dvd_triv_right])

lemma timesmod1: "((x::nat)*((y::nat) mod n)) mod (n::nat) = ((x*y) mod n)"
  by (rule mod_mult_right_eq)

lemma timesmod3: "((a mod (n::nat)) * b) mod n = (a*b) mod n"
  by (rule mod_mult_left_eq)

lemma remainderexplemma: "(y mod (a::nat) = z mod a) \<Longrightarrow> (x*y) mod a = (x*z) mod a"
  by (rule mod_mult_cong [OF refl])

lemma remainderexp: "((a mod (n::nat))^i) mod n = (a^i) mod n"
  by (rule power_mod)

end
