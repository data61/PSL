(* This Isabelle theory is produced using the TIP tool offered at the following website: 
     https://github.com/tip-org/tools 
   This file was originally provided as part of TIP benchmark at the following website:
     https://github.com/tip-org/benchmarks 
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.
\:w
   Some proofs were added by Yutaka Nagashima.*)
  theory TIP_int_right_distrib
  imports "../../Test_Base"
begin

datatype Sign = Pos | Neg

datatype Nat = Z | S "Nat"

datatype Integer = P "Nat" | N "Nat"

fun toInteger :: "Sign => Nat => Integer" where
  "toInteger (Pos) y = P y"
| "toInteger (Neg) (Z) = P Z"
| "toInteger (Neg) (S z) = N z"

fun sign :: "Integer => Sign" where
  "sign (P y) = Pos"
| "sign (N z) = Neg"

fun pred :: "Nat => Nat" where
  "pred (S y) = y"

fun plus :: "Nat => Nat => Nat" where
  "plus (Z) y = y"
| "plus (S z) y = S (plus z y)"

fun times2 :: "Nat => Nat => Nat" where
  "times2 (Z) y = Z"
| "times2 (S z) y = plus y (times2 z y)"

fun opposite :: "Sign => Sign" where
  "opposite (Pos) = Neg"
| "opposite (Neg) = Pos"

fun timesSign :: "Sign => Sign => Sign" where
  "timesSign (Pos) y = y"
| "timesSign (Neg) y = opposite y"

fun absVal :: "Integer => Nat" where
  "absVal (P n) = n"
| "absVal (N m) = plus (S Z) m"

fun times :: "Integer => Integer => Integer" where
  "times x y =
   toInteger
     (timesSign (sign x) (sign y)) (times2 (absVal x) (absVal y))"

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

fun plus2 :: "Integer => Integer => Integer" where
  "plus2 (P m) (P n) = P (plus m n)"
| "plus2 (P m) (N o2) = t2 m (plus (S Z) o2)"
| "plus2 (N m2) (P n2) = t2 n2 (plus (S Z) m2)"
| "plus2 (N m2) (N n3) = N (plus (plus (S Z) m2) n3)"

theorem property0 :
  "((times (plus2 x y) z) = (plus2 (times x z) (times y z)))"
  oops

end
