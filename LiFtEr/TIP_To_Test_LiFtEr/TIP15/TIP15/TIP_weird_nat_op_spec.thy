(* This Isabelle theory is produced using the TIP tool offered at the following website: 
     https://github.com/tip-org/tools 
   This file was originally provided as part of TIP benchmark at the following website:
     https://github.com/tip-org/benchmarks 
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.*)
  theory TIP_weird_nat_op_spec
  imports "../../Test_Base"
begin

datatype Nat = Z | S "Nat"

fun plus :: "Nat => Nat => Nat" where
  "plus (Z) y = y"
| "plus (S z) y = S (plus z y)"

fun times :: "Nat => Nat => Nat" where
  "times (Z) y = Z"
| "times (S z) y = plus y (times z y)"

fun op1 :: "Nat => Nat => Nat => Nat => Nat" where
  "op1 x y z x2 =
   (let fail :: Nat =
     (case z of
        Z => (case x of S x4 => op1 x4 y y x2)
        | S x3 => op1 x y x3 (S x2))
   in (case x of
         Z =>
           (case z of
              Z => x2
              | S x6 => fail)
         | S x5 => fail))"

theorem property0 :
  "((op1 a b c d) = (plus (plus (times a b) c) d))"
  oops

end
