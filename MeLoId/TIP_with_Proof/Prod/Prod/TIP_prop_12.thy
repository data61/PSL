(* Property from Productive Use of Failure in Inductive Proof, 
   Andrew Ireland and Alan Bundy, JAR 1996. 
   This Isabelle theory is produced using the TIP tool offered at the following website: 
     https://github.com/tip-org/tools 
   This file was originally provided as part of TIP benchmark at the following website:
     https://github.com/tip-org/benchmarks 
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.
   Some proofs were added by Yutaka Nagashima.*)
  theory TIP_prop_12
  imports "../../Test_Base"
begin

datatype 'a list = nil2 | cons2 "'a" "'a list"

fun x :: "'a list => 'a list => 'a list" where
  "x (nil2) z = z"
| "x (cons2 z2 xs) z = cons2 z2 (x xs z)"

fun rev :: "'a list => 'a list" where
  "rev (nil2) = nil2"
| "rev (cons2 z xs) = x (rev xs) (cons2 z (nil2))"

fun qrev :: "'a list => 'a list => 'a list" where
  "qrev (nil2) z = z"
| "qrev (cons2 z2 xs) z = qrev xs (cons2 z2 z)"

lemma app_assoc: "x (x y z) w = x y (x z w)" by (induction y, auto)
lemma qrev_rev: "qrev y z = x (rev y) z"
  apply(induction y arbitrary: z, auto)
  apply(simp add: app_assoc)
  done
lemma app_nil: "x y nil2 = y" by(induction y, auto)
lemma rev_app: "rev (x y z) = x (rev z) (rev y)"
  apply(induction y, auto)
   apply(simp add: app_nil) 
  using app_assoc apply(auto)
  done

theorem property0 :
  "((qrev y z) = (x (rev y) z))"
  apply(induction y arbitrary: z, auto)
  apply(simp add: qrev_rev)
  apply(simp add: app_assoc)
  done

end
