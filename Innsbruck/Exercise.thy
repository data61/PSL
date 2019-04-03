(* Title:       Innsbruck/Exercise.thy
    Author:     Yutaka Nagashima, Data61, CSIRO
   Property from Case-Analysis for Rippling and Inductive Proof, 
   Moa Johansson, Lucas Dixon and Alan Bundy, ITP 2010. 
   This Isabelle theory is produced using the TIP tool offered at the following website: 
     https://github.com/tip-org/tools 
   This file was originally provided as part of TIP benchmark at the following website:
     https://github.com/tip-org/benchmarks 
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.
   Some proofs were added by Yutaka Nagashima.*)

theory Exercise
imports Main
begin

(*** Exercise I ***)
(* TODO: Prove the following three lemmas using PSL. *)

datatype 'a list = nil2 | cons2 "'a" "'a list"

datatype Nat = Z | S "Nat"

fun len :: "'a list => Nat" where
  "len (nil2) = Z"
| "len (cons2 y xs) = S (len xs)"

fun t2 :: "Nat => Nat => bool" where
  "t2 x (Z) = False"
| "t2 (Z) (S z) = True"
| "t2 (S x2) (S z) = t2 x2 z"

fun ins :: "Nat => Nat list => Nat list" where
  "ins x (nil2) = cons2 x (nil2)"
| "ins x (cons2 z xs) =
     (if t2 x z then cons2 x (cons2 z xs) else cons2 z (ins x xs))"

theorem property15 :
  "((len (ins x xs)) = (S (len xs)))"
  oops

fun map :: "('a => 'b) => 'a list => 'b list" where
  "map x (nil2) = nil2"
| "map x (cons2 z xs) = cons2 (x z) (map x xs)"

fun drop :: "Nat => 'a list => 'a list" where
  "drop (Z) y = y"
| "drop (S z) (nil2) = nil2"
| "drop (S z) (cons2 x2 x3) = drop z x3"

theorem property12 :
  "((drop n (map f xs)) = (map f (drop n xs)))"
  oops

fun x :: "'a list => 'a list => 'a list" where
  "x (nil2) z = z"
| "x (cons2 z2 xs) z = cons2 z2 (x xs z)"

fun filter :: "('a => bool) => 'a list => 'a list" where
  "filter y (nil2) = nil2"
| "filter y (cons2 z2 xs) =
     (if y z2 then cons2 z2 (filter y xs) else filter y xs)"

theorem property14 :
  "((filter p (x xs ys)) = (x (filter p xs) (filter p ys)))"
  oops

(*** Exercise II-a ***)
(* TODO: Define Seq_Min. *)

ML_file "Constructor_Class.ML"

ML{* structure List_Min : MONAD_MIN =
struct
  type 'a monad     = 'a list;
  fun return x      = [x];
  fun bind seq func = flat (map func seq);
end;
*}

ML{* structure ListCC = mk_Monad (List_Min); *}

(* Some monad functions become available *)
ML{* ListCC.>>=; *}
ML{* ListCC.>=>; *}
ML{* ListCC.join;*}

(* Since every monad is an applicative, ListCC has applicative functions. *)
ML{* ListCC.<*> *}
ML{* ListCC.liftA *}

(* Since every applicative is a functor, ListCC has functor functions. *)
ML{* ListCC.fmap *}
ML{* ListCC.<$> *}

ML{* structure Seq_Min (*: MONAD_MIN*) =
struct
  type 'a monad     = 'a Seq.seq;
  (* TODO *)
end;
*}

(* If you define Seq_Min properly, mk_Monad can produce many auxiliary functions for Seq.seq. *)
(*ML{* structure SeqCC = mk_Monad (Seq_Min); *}*)

(*** Exercise II-b ***)
(* TODO: Prove the following lemma using the tactic-method.
 *       The tactic-method takes a ML tactic of type "thm ⇒ thm Seq.seq" *)
lemma "True ∨ False"
  apply (tactic {* fn thm:thm => (*TODO: Change here*) Seq.single thm *})
  oops

end
