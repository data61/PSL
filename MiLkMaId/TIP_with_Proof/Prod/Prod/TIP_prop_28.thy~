(* Property from Productive Use of Failure in Inductive Proof, 
   Andrew Ireland and Alan Bundy, JAR 1996. 
   This Isabelle theory is produced using the TIP tool offered at the following website: 
     https://github.com/tip-org/tools 
   This file was originally provided as part of TIP benchmark at the following website:
     https://github.com/tip-org/benchmarks 
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.
   Some proofs were added by Yutaka Nagashima.*)
  theory TIP_prop_28
  imports "../../Test_Base"
begin

datatype 'a list = nil2 | cons2 "'a" "'a list"

fun x :: "'a list => 'a list => 'a list" where
  "x (nil2) z = z"
| "x (cons2 z2 xs) z = cons2 z2 (x xs z)"

fun rev :: "'a list => 'a list" where
  "rev (nil2) = nil2"
| "rev (cons2 z xs) = x (rev xs) (cons2 z (nil2))"

fun revflat :: "('a list) list => 'a list" where
  "revflat (nil2) = nil2"
| "revflat (cons2 xs xss) = x (revflat xss) (rev xs)"

fun qrevflat :: "('a list) list => 'a list => 'a list" where
  "qrevflat (nil2) z = z"
| "qrevflat (cons2 xs xss) z = qrevflat xss (x (rev xs) z)"
lemma app_nil: "x y nil2 = y" by (induction y, auto)
lemma app_comm: "x (x y z) w = x y (x z w)" by (induction y, auto)
lemma revflat_qrevflat:  "(qrevflat y z) = x (revflat y) z"
  apply(induction y arbitrary: z, auto)
  apply(simp add: app_comm)
  done
theorem property0 :
  "((revflat y) = (qrevflat y (nil2)))"
  apply(induction y, auto)
  apply(simp add: app_nil revflat_qrevflat)
  done

end
