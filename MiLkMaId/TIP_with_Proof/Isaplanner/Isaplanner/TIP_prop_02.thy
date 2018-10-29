(* Property from Case-Analysis for Rippling and Inductive Proof, 
   Moa Johansson, Lucas Dixon and Alan Bundy, ITP 2010. 
   This Isabelle theory is produced using the TIP tool offered at the following website: 
     https://github.com/tip-org/tools 
   This file was originally provided as part of TIP benchmark at the following website:
     https://github.com/tip-org/benchmarks 
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.
   Some proofs were added by Yutaka Nagashima.*)
theory TIP_prop_02
  imports "../../Test_Base" "../../../src/Build_Database/Build_Database"
begin

datatype 'a list = nil2 | cons2 "'a" "'a list"

datatype Nat = Z | S "Nat"

fun y :: "'a list => 'a list => 'a list" where
  "y (nil2) y2 = y2"
| "y (cons2 z2 xs) y2 = cons2 z2 (y xs y2)"

fun x :: "Nat => Nat => bool" where
  "x (Z) (Z) = True"
| "x (Z) (S z2) = False"
| "x (S x2) (Z) = False"
| "x (S x2) (S y22) = x x2 y22"

fun count :: "Nat => Nat list => Nat" where
  "count z (nil2) = Z"
| "count z (cons2 z2 ys) =
     (if x z z2 then S (count z ys) else count z ys)"

fun t2 :: "Nat => Nat => Nat" where
  "t2 (Z) y2 = y2"
| "t2 (S z2) y2 = S (t2 z2 y2)"

theorem property0 :
  "t2 (count n xs) (count n ys) = count n (y xs ys)"
  find_proof DInd
  apply (induct n xs arbitrary: ys rule: TIP_prop_02.count.induct)
  apply auto
  done

theorem property0_5:
  "t2 (count n xs) (count n ys) = count n (y xs ys)"
  apply2(induct xs arbitrary:n ys)
   apply(subst y.simps(1))
   apply(subst count.simps(1))
   apply(subst t2.simps(1))
   apply(rule HOL.refl)
  apply auto
  done

theorem property0' :
  "((t2 (count n xs) (count n ys)) = (count n (y xs ys)))"
  (*why not "induct ys"?*)
  apply2(induct ys)
   apply(subst count.simps(1))
    (* Neither of the innermost recursively defined constant "count" in "(count n xs)" and 
   "y" in "(y xs nil2)" has a simp rule applicable to these.*)
   apply(induct xs)
    apply auto[1]
   apply auto[1]
  oops

(*alternative proof*)
theorem property0'' :
  "((t2 (count n xs) (count n ys)) = (count n (y xs ys)))"
  apply2 (induct (*n*) xs arbitrary: n ys rule: count.induct)
    (*Why "count.induct" not "y.induct"?
     *Because "(induct rule: y.induct)" leads to a non-theorem.
     *Because "y" is under another "recursive" function ("count")?
     *No. "y.induct" can be useful as well. See property0'''' for more detail.*)
    (*"xs" in "induct xs" here is removable.*)
    (*Why "induct xs" (why induction on xs)?
     *Because two innermost recursive constants ("count" in "count n xs" and "y" in "y xs ys")
     *is recursively defined on "xs". *)
    (*Why "arbitrary: ys", "arbitrary: n", "arbitrary: ys n", or "arbitrary: n ys"?
     *Because of "n" and "ys" in "count n ys".
     *This "count" is also the innermost recursive constant, but we induct on "xs".*)
   apply auto
  done

theorem property0''' :
  "((t2 (count n xs) (count n ys)) = (count n (y xs ys)))"
  apply(induct rule:y.induct)
  nitpick
  oops

theorem property0'''' :
  "((t2 (count n xs) (count n ys)) = (count n (y xs ys)))"
  apply(induct xs ys arbitrary: n rule:y.induct)
  by auto

end