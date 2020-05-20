(*
    Author:   Benedikt Seidl
    License:  BSD
*)

section \<open>Quotient Type Emulation for Locales\<close>

theory Quotient_Type
imports
  Main
begin

locale quotient =
  fixes
    eq :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  and
    Rep :: "'b \<Rightarrow> 'a"
  and
    Abs :: "'a \<Rightarrow> 'b"
  assumes
    Rep_inverse: "Abs (Rep a) = a"
  and
    Abs_eq: "Abs x = Abs y \<longleftrightarrow> eq x y"
begin

lemma Rep_inject:
  "Rep x = Rep y \<longleftrightarrow> x = y"
  by (metis Rep_inverse)

lemma Rep_Abs_eq:
  "eq x (Rep (Abs x))"
  by (metis Abs_eq Rep_inverse)

end

end
