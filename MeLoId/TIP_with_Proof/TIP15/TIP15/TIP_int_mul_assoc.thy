(* This Isabelle theory is produced using the TIP tool offered at the following website: 
     https://github.com/tip-org/tools 
   This file was originally provided as part of TIP benchmark at the following website:
     https://github.com/tip-org/benchmarks 
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.
\:w
   Some proofs were added by Yutaka Nagashima.*)
  theory TIP_int_mul_assoc
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

theorem property0 :
  "((times x (times y z)) = (times (times x y) z))"
  oops

end
