(* This Isabelle theory is produced using the TIP tool offered at the following website: 
     https://github.com/tip-org/tools 
   This file was originally provided as part of TIP benchmark at the following website:
     https://github.com/tip-org/benchmarks 
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.*)
  theory TIP_int_add_ident_right
imports "../../Test_Base"
begin

datatype Nat = Z | S "Nat"

datatype Integer = P "Nat" | N "Nat"

definition(*fun*) zero :: "Integer" where
"zero = P Z"

fun pred :: "Nat => Nat" where
"pred (S y) = y"

fun plus2 :: "Nat => Nat => Nat" where
"plus2 (Z) y = y"
| "plus2 (S z) y = S (plus2 z y)"

fun t2 :: "Nat => Nat => Integer" where
"t2 x y =
   (let fail :: Integer =
     (case y of
        Z => P x
        | S z =>
            (case x of
               Z => N y
               | S x2 => t2 x2 z))
   in (case x of
         Z =>
           (case y of
              Z => P Z
              | S x4 => fail)
         | S x3 => fail))"

fun plus :: "Integer => Integer => Integer" where
"plus (P m) (P n) = P (plus2 m n)"
| "plus (P m) (N o2) = t2 m (plus2 (S Z) o2)"
| "plus (N m2) (P n2) = t2 n2 (plus2 (S Z) m2)"
| "plus (N m2) (N n3) = N (plus2 (plus2 (S Z) m2) n3)"

theorem property0 :
  "(x = (plus x zero))"
  oops

end
