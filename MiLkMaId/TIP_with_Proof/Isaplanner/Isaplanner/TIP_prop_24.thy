(* Property from Case-Analysis for Rippling and Inductive Proof, 
   Moa Johansson, Lucas Dixon and Alan Bundy, ITP 2010. 
   This Isabelle theory is produced using the TIP tool offered at the following website: 
     https://github.com/tip-org/tools 
   This file was originally provided as part of TIP benchmark at the following website:
     https://github.com/tip-org/benchmarks 
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.
   Some proofs were added by Yutaka Nagashima.*)
theory TIP_prop_24
  imports "../../Test_Base"
begin

datatype Nat = Z | S "Nat"

fun x :: "Nat => Nat => bool" where
  "x (Z) (Z) = True"
| "x (Z) (S z2) = False"
| "x (S x2) (Z) = False"
| "x (S x2) (S y2) = x x2 y2"

fun max :: "Nat => Nat => Nat" where
  "max (Z) z = z"
| "max (S z2) (Z) = S z2"
| "max (S z2) (S x2) = S (max z2 x2)"

fun t2 :: "Nat => Nat => bool" where
  "t2 (Z) z = True"
| "t2 (S z2) (Z) = False"
| "t2 (S z2) (S x2) = t2 z2 x2"


theorem property0 :(*Probably the best proof.*)
  "((x (max a b) a) = (t2 b a))"
  apply(induct rule:x.induct)
     apply fastforce
    apply clarsimp
    apply(induct_tac z2)
     apply fastforce+
  done
    (*Why does "x.induct" lead to the shortest proof?
  Because "x"'s pattern-matching is complete, meaning that it does not involve any wild-card.*)

theorem property0' :
  "((x (max a b) a) = (t2 b a))"
  apply(induct b arbitrary:a)(*This arbitrary is important.*)
   apply(induct_tac a)
    apply fastforce+
   apply(induct_tac xa)
    apply fastforce+
  apply(induct_tac a)
   apply fastforce+
  done

(*We can finish proving this theorem starting induction on "a".*)
theorem property0'' :
  "((x (max a b) a) = (t2 b a))"
  apply(induct a arbitrary:b)(*This arbitrary is important.*)
   apply clarsimp
   apply(induct_tac b)
    apply fastforce+
  apply(induct_tac b)
   apply clarsimp
   apply(induct_tac a)
    apply fastforce+
  done

theorem property0''' :
  "((x (max a b) a) = (t2 b a))"
  apply(induct rule:t2.induct)
    apply clarsimp
    apply(induct_tac z)
     apply fastforce
    apply clarsimp
    apply(induct_tac xa)
     apply fastforce+
  done

theorem property0'''' :
  "((x (max a b) a) = (t2 b a))"
  apply(induct rule:max.induct)(*This is equivalent to "(induct rule:t2.induct)"*)
    apply clarsimp
    apply(induct_tac z)
     apply fastforce
    apply clarsimp
    apply(induct_tac xa)
     apply fastforce+
  done

end