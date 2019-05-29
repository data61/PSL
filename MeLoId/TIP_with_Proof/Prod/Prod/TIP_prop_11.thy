(* Property from Productive Use of Failure in Inductive Proof, 
   Andrew Ireland and Alan Bundy, JAR 1996. 
   This Isabelle theory is produced using the TIP tool offered at the following website: 
     https://github.com/tip-org/tools 
   This file was originally provided as part of TIP benchmark at the following website:
     https://github.com/tip-org/benchmarks 
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.
   Some proofs were added by Yutaka Nagashima.*)
  theory TIP_prop_11
  imports "../../Test_Base"
begin

datatype 'a list = nil2 | cons2 "'a" "'a list"

fun x :: "'a list => 'a list => 'a list" where
  "x (nil2) z = z"
| "x (cons2 z2 xs) z = cons2 z2 (x xs z)"

fun rev :: "'a list => 'a list" where
  "rev (nil2) = nil2"
| "rev (cons2 z xs) = x (rev xs) (cons2 z (nil2))"

lemma app_nil: "x y nil2 = y"
  by (induct y, auto)

lemma app_assoc: "x (x w y) z = x w (x y z)"
  by(induction w, auto)

lemma rev_app: "rev (x y z) = x (rev z) (rev y)"
  apply(induction y, simp add: app_nil)
  apply(simp add: app_assoc)
  done

lemma revrev: "rev (rev y) = y"
  apply(induct y rule: rev.induct, auto)
   apply(simp add: rev_app)
  done

theorem property0 :
  "((rev (x (rev y) (rev z))) = (x z y))"
  apply(induct y, auto)
   apply(simp add: app_nil revrev)
  apply(simp add: revrev rev_app)
  done

end
