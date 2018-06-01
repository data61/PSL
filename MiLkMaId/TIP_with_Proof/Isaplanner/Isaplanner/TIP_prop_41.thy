(* Property from Case-Analysis for Rippling and Inductive Proof, 
   Moa Johansson, Lucas Dixon and Alan Bundy, ITP 2010. 
   This Isabelle theory is produced using the TIP tool offered at the following website: 
     https://github.com/tip-org/tools 
   This file was originally provided as part of TIP benchmark at the following website:
     https://github.com/tip-org/benchmarks 
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.
   Some proofs were added by Yutaka Nagashima.*)
theory TIP_prop_41
  imports "../../Test_Base"
begin

datatype 'a list = nil2 | cons2 "'a" "'a list"

datatype Nat = Z | S "Nat"

fun take :: "Nat => 'a list => 'a list" where
  "take (Z) y = nil2"
| "take (S z) (nil2) = nil2"
| "take (S z) (cons2 x2 x3) = cons2 x2 (take z x3)"

fun map :: "('a => 'b) => 'a list => 'b list" where
  "map x (nil2) = nil2"
| "map x (cons2 z xs) = cons2 (x z) (map x xs)"

theorem property0 :(*Probably the best proof*)
  "((take n (map f xs)) = (map f (take n xs)))"
  find_proof DInd
    (*specifying "xs" is necessary.*)
  apply (induct xs rule: TIP_prop_41.take.induct)
    (*Why "rule:take.induct" instead of "rule:map.induct"?*)
    (*Because "take"'s pattern-matching is complete on the first parameter and 
    both first arguments ("n" and "n") are variables here, while
    "map"'s pattern-matching is complete on the second parameter and 
    "map"'s second arguments are "xs" and "take n xs" in this case (?)*)
    apply auto
  done 

theorem property0' :
  "((take n (map f xs)) = (map f (take n xs)))"
  apply (induct n xs rule: TIP_prop_41.take.induct)(*equivalent to "(induct xs rule: TIP_prop_41.take.induct)"*)
    apply auto
  done

theorem property0'' :(*sub-optimal proof*)
  "((take n (map f xs)) = (map f (take n xs)))"
  apply (induct n arbitrary: xs) (*This "arbitrary: xs" is necessary.*)
   apply fastforce
  apply(induct_tac xs)
   apply auto
  done

theorem property0''' :(*sub-optimal proof*)
  "((take n (map f xs)) = (map f (take n xs)))"
  (*Why does "induct n arbitrary:xs" lead to a shorter proof.
    Because "induct xs arbitrary:n" cannot process the right-hand side ("map f (take n xs)") 
    very well. *)
  apply (induct xs arbitrary: n) (*This "arbitrary: xs" is necessary.*)
   apply(induct_tac n)
    apply fastforce+
  apply(induct_tac n)
   apply auto
  done

theorem property0''' :
  "((take n (map f xs)) = (map f (take n xs)))"
  apply (induct rule: TIP_prop_41.take.induct)
  nitpick
  oops

end