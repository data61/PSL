(* This Isabelle theory is produced using the TIP tool offered at the following website: 
     https://github.com/tip-org/tools 
   This file was originally provided as part of TIP benchmark at the following website:
     https://github.com/tip-org/benchmarks 
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.
\:w
   Some proofs were added by Yutaka Nagashima.*)
  theory TIP_list_nat_PairUnpair
  imports "../../Test_Base"
begin

datatype ('a, 'b) pair = pair2 "'a" "'b"

datatype 'a list = nil2 | cons2 "'a" "'a list"

datatype Nat = Z | S "Nat"

fun unpair :: "(('t, 't) pair) list => 't list" where
  "unpair (nil2) = nil2"
| "unpair (cons2 (pair2 z y2) xys) =
     cons2 z (cons2 y2 (unpair xys))"

fun plus :: "Nat => Nat => Nat" where
  "plus (Z) y = y"
| "plus (S z) y = S (plus z y)"

fun pairs :: "'t list => (('t, 't) pair) list" where
  "pairs (nil2) = nil2"
| "pairs (cons2 y (nil2)) = nil2"
| "pairs (cons2 y (cons2 y2 xs)) = cons2 (pair2 y y2) (pairs xs)"

fun minus :: "Nat => Nat => Nat" where
  "minus (Z) y = Z"
| "minus (S z) (S y2) = minus z y2"

fun lt :: "Nat => Nat => bool" where
  "lt x (Z) = False"
| "lt (Z) (S z) = True"
| "lt (S n) (S z) = lt n z"

fun length :: "'a list => Nat" where
  "length (nil2) = Z"
| "length (cons2 y l) = plus (S Z) (length l)"

fun le :: "Nat => Nat => bool" where
  "le (Z) y = True"
| "le (S z) (Z) = False"
| "le (S z) (S x2) = le z x2"

(*fun did not finish the proof*)
function imod :: "Nat => Nat => Nat" where
  "imod x y = (if lt x y then x else imod (minus x y) y)"
  by pat_completeness auto

theorem property0 :
  "((let eta :: Nat = length xs
     in ((let md :: Nat = imod eta (S (S Z))
          in (if
                ((case eta of
                    Z => Z
                    | S x => (if le eta Z then (case Z of S y => p Z) else S Z) =
                    (if le (S (S Z)) Z then (case Z of S z => minus Z (p Z)) else
                       (case Z of S x2 => p Z))) &
                   (md ~= Z))
                then
                minus md (S (S Z))
                else
                md)) =
           Z)) ==>
      ((unpair (pairs xs)) = xs))"
  oops

end
