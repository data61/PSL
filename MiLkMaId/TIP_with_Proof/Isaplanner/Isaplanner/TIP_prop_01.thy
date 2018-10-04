(* Property from Case-Analysis for Rippling and Inductive Proof, 
   Moa Johansson, Lucas Dixon and Alan Bundy, ITP 2010. 
   This Isabelle theory is produced using the TIP tool offered at the following website: 
     https://github.com/tip-org/tools 
   This file was originally provided as part of TIP benchmark at the following website:
     https://github.com/tip-org/benchmarks 
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.
   Some proofs were added by Yutaka Nagashima.*)
theory TIP_prop_01
  imports "../../Test_Base" "../../../src/Build_Database/Build_Database"
begin

datatype 'a list = nil2 | cons2 "'a" "'a list"

datatype Nat = Z | S "Nat"

fun x :: "'a list => 'a list => 'a list" where
  "x (nil2) z = z"
| "x (cons2 z2 xs) z = cons2 z2 (x xs z)"

fun take :: "Nat => 'a list => 'a list" where
  "take (Z) z = nil2"
| "take (S z2) (nil2) = nil2"
| "take (S z2) (cons2 x2 x3) = cons2 x2 (take z2 x3)"

fun drop :: "Nat => 'a list => 'a list" where
  "drop (Z) z = z"
| "drop (S z2) (nil2) = nil2"
| "drop (S z2) (cons2 x2 x3) = drop z2 x3"

theorem property0 :(*Probably the best proof.*)
  "x (take n xs) (drop n xs) = xs"
  find_proof DInd
  (*"induct rule:take.induct also works well.*)
  (*Because take.induct and drop.induct are identical.*)
  (*why "induct rule:take.induct" or "induct rule:drop.induct"?
    Because all the definitions of the innermost recursively defined constants ("take" and "drop") 
    produce the same rule. *)
  (*Why induction on xs?*)
  (* Induction on "n xs rule: TIP_prop_01.drop.induct" works as well.
   * Induction on "n" rule: TIP_prop_01.drop.induct is bad
   * because the resulting proof goal is identical to the original goal. *)
  apply2 (induct xs rule: TIP_prop_01.drop.induct)
    apply auto
  done

theorem property0'(*sub-optimal proof*):
  "x (take n xs) (drop n xs) = xs"
  (*Induction on n might look promising in the first try
    since both "take" and "drop" are defined recursively on the first argument, but...*)
  apply2(induct n arbitrary: xs)
   apply2 auto[1]
    (*This is problematic:
    We cannot use the simplification rule of "x"
    because we cannot simplify "TIP_prop_01.take (S n) xs".
   *)
  apply(case_tac n)
   apply(case_tac xs)
    apply auto[1]
   apply auto[1]
  apply(case_tac xs)
   apply auto[1]
  apply auto[1](*To discharge the last sub-goal using this auto[1], we need to generalize xs*)
  done

theorem property0''(*sub-optimal proof*):
  "x (take n xs) (drop n xs) = xs"
  (*Induction on "xs" without "rule:take.induct" might look promising in the first try
    since both "take" and "drop" are defined recursively on the first argument, but...*)
  apply2(induct xs arbitrary: n)
   apply2(induct n)
    apply(case_tac n)(*cases is not good enough because "n" is quantified by \<And>*)
     apply fastforce+
    (*It is not so easy from this point
    "(inductino hypothesis) \<Longrightarrow>
     x (TIP_prop_01.take n (cons2 x1 xs)) (TIP_prop_01.drop n (cons2 x1 xs)) = cons2 x1 xs"
    because we cannot apply any of the following simplification rules.
     x.simps   : because "(TIP_prop_01.take n (cons2 x1 xs))" is not fully evaluated.
     take.simps: because "n" is a variable and Isabelle cannot do patter matching.
     drop.simps: because "n" is a variable and Isabelle cannot do patter matching. 
   *)
  apply(case_tac n)
   apply auto[1]
  apply(simp del: take.simps drop.simps)
  apply(thin_tac "n = S x2")
  apply(subst "take.simps")
  apply(subst "drop.simps")
  apply(subst "x.simps")
  by auto

end