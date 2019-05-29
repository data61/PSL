(* Property from Case-Analysis for Rippling and Inductive Proof, 
   Moa Johansson, Lucas Dixon and Alan Bundy, ITP 2010. 
   This Isabelle theory is produced using the TIP tool offered at the following website: 
     https://github.com/tip-org/tools 
   This file was originally provided as part of TIP benchmark at the following website:
     https://github.com/tip-org/benchmarks 
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.
   Some proofs were added by Yutaka Nagashima.*)
theory TIP_prop_08
  imports "../../Test_Base"
begin

datatype Nat = Z | S "Nat"

fun t22 :: "Nat => Nat => Nat" where
  "t22 (Z) y = y"
| "t22 (S z) y = S (t22 z y)"

fun t2 :: "Nat => Nat => Nat" where
  "t2 (Z) y = Z"
| "t2 (S z) (Z) = S z"
| "t2 (S z) (S x2) = t2 z x2"

theorem property0 :
  "((t2 (t22 k m) (t22 k n)) = (t2 m n))"
  find_proof DInd
  apply (induct arbitrary: n rule: TIP_prop_08.t22.induct)
   apply auto
  done

theorem property0' :
  "((t2 (t22 k m) (t22 k n)) = (t2 m n))"
  apply(induct k arbitrary:n m)(*equivalent to apply (induct arbitrary: n rule: TIP_prop_08.t22.induct)*)
   apply auto
  done

theorem property0'' :
  "((t2 (t22 k m) (t22 k n)) = (t2 m n))"
  (*applying induction on "k" is the natural choice:
    "t22" is the unique innermost recursive constant, which pattern-matches on the first parameter.
    Furthermore, the other recursive function, "t2" takes "t22" in its arguments, and
    the two "t22"s have different arguments ("m" and "n"). Therefore, without applying induction on
    "t22"'s argument we cannot finish this proof.*)
  apply(induct k)
   apply auto
  done

theorem property0''' :(*sub-optimal proof*)
  "((t2 (t22 k m) (t22 k n)) = (t2 m n))"
  apply(induct m)
   apply clarsimp
   apply(induct k)(*extra induction*)
    apply fastforce+
  apply(induct k)(*extra induction*)
   apply auto
  done

end