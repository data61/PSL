(* This Isabelle theory is produced using the TIP tool offered at the following website: 
     https://github.com/tip-org/tools 
   This file was originally provided as part of TIP benchmark at the following website:
     https://github.com/tip-org/benchmarks 
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.
\:w
   Some proofs were added by Yutaka Nagashima.*)
  theory TIP_weird_nat_op_assoc2
  imports "../../Test_Base"
begin

datatype Nat = Z | S "Nat"

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
  "((op1 (op1 x a a a) b c d) = (op1 a (op1 b x b b) c d))"
  oops

end
