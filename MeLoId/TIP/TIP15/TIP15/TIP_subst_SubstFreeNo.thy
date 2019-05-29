(* This Isabelle theory is produced using the TIP tool offered at the following website: 
     https://github.com/tip-org/tools 
   This file was originally provided as part of TIP benchmark at the following website:
     https://github.com/tip-org/benchmarks 
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.*)
  theory TIP_subst_SubstFreeNo
  imports "../../Test_Base"
begin

datatype 'a list = nil2 | cons2 "'a" "'a list"

datatype Expr = Var "int" | Lam "int" "Expr" | App "Expr" "Expr"

fun x :: "'a list => 'a list => 'a list" where
  "x (nil2) z = z"
| "x (cons2 z2 xs) z = cons2 z2 (x xs z)"

fun newmaximum :: "int => int list => int" where
  "newmaximum y (nil2) = y"
| "newmaximum y (cons2 z2 ys) =
     (if y <= z2 then newmaximum z2 ys else newmaximum y ys)"

fun new :: "int list => int" where
  "new y = (newmaximum 0 y) + 1"

fun filter :: "('a => bool) => 'a list => 'a list" where
  "filter p (nil2) = nil2"
| "filter p (cons2 z xs) =
     (if p z then cons2 z (filter p xs) else filter p xs)"

fun free :: "Expr => int list" where
  "free (Var z) = cons2 z (nil2)"
| "free (Lam z2 b) = filter (% (x2 :: int) => (z2 ~= x2)) (free b)"
| "free (App a2 b2) = x (free a2) (free b2)"

fun elem :: "'a => 'a list => bool" where
  "elem y (nil2) = False"
| "elem y (cons2 z2 xs) = ((z2 = y) | (elem y xs))"

(*fun did not finish the proof*)
function subst :: "int => Expr => Expr => Expr" where
  "subst y z (Var y2) = (if (y = y2) then z else Var y2)"
| "subst y z (Lam y3 a) =
     (let z22 :: int = new (x (free z) (free a))
     in (if (y = y3) then Lam y3 a else
           (if elem y3 (free z) then
              subst y z (Lam z22 (subst y3 (Var z22) a))
              else
              Lam y3 (subst y z a))))"
| "subst y z (App a2 b2) = App (subst y z a2) (subst y z b2)"
  by pat_completeness auto

theorem property0 :
  "((~ (elem y (free a))) ==>
      ((elem z (free a)) = (elem z (free (subst y e a)))))"
  oops

end
