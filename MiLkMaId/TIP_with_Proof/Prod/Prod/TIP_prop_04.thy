(* Property from Productive Use of Failure in Inductive Proof, 
   Andrew Ireland and Alan Bundy, JAR 1996. 
   This Isabelle theory is produced using the TIP tool offered at the following website: 
     https://github.com/tip-org/tools 
   This file was originally provided as part of TIP benchmark at the following website:
     https://github.com/tip-org/benchmarks 
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.
   Some proofs were added by Yutaka Nagashima.*)
  theory TIP_prop_04
  imports "../../Test_Base"
begin

datatype 'a list = nil2 | cons2 "'a" "'a list"

datatype Nat = Z | S "Nat"

fun x :: "'a list => 'a list => 'a list" where
  "x (nil2) z = z"
| "x (cons2 z2 xs) z = cons2 z2 (x xs z)"

fun length :: "'a list => Nat" where
  "length (nil2) = Z"
| "length (cons2 z xs) = S (length xs)"

fun double :: "Nat => Nat" where
  "double (Z) = Z"
| "double (S z) = S (S (double z))"

theorem property0 :
  "((length (x y y)) = (double (length y)))"
  (*why not "induct y"?*)
  apply(induct rule:x.induct)
  apply(induct rule:length.induct)
   apply auto[1]
  apply clarsimp
  apply(subgoal_tac "\<And>z xs. TIP_prop_04.length (x xs xs) = double (TIP_prop_04.length xs) \<longrightarrow>
            TIP_prop_04.length (x xs (cons2 z xs)) = S (double (TIP_prop_04.length xs))")
   apply fastforce
  apply(thin_tac "TIP_prop_04.length (x xs xs) = double (TIP_prop_04.length xs)")
  apply(subgoal_tac "\<And>z xs za xsa dlenxsa.
       TIP_prop_04.length (x xsa xsa) = dlenxsa \<longrightarrow>
       TIP_prop_04.length (x xsa (cons2 za xsa)) = S dlenxsa")
   apply fastforce
  apply(induct_tac xsaa rule:x.induct)
   apply clarsimp
   apply(induct_tac rule:x.induct)
  oops

end
