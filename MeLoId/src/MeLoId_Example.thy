(*  Title:      MeLoId/src/MiLkMaId_Example.thy
    Author:     Yutaka Nagashima, CIIRC, CTU

This file defines auxiliary constants defined in available literature.
We use these constants to test ML functions defined in MiLkMaId/Assertion.thy.
*)
theory MeLoId_Example
imports "../TIP_with_Proof/Isaplanner/Isaplanner/TIP_prop_01" "HOL.Real"
begin

(** Isabelle definitions for testing **)

definition "MyTrue1 \<equiv> True" print_theorems

definition MyTrueDef: "MyTrue2 \<equiv> True" print_theorems

definition nand :: "bool \<Rightarrow> bool \<Rightarrow> bool" where "nand A B \<equiv> \<not> (A \<and> B)"
print_theorems

(* Example from the Isabelle tutorial by Tobias Nipkow et al. *)
inductive evn :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
step: "evn n m \<Longrightarrow> evn (Suc(Suc n)) m" |
zero: "evn 0 n" |
step_test: "evn n m \<Longrightarrow> evn (Suc(Suc n)) m"
print_theorems (*cases, induct, inducts, intros, simps(, step, step_test, zero)*)

(* Example from Defining Recursive Functions in Isabelle/HOL by Alexander Krauss *)
fun fib :: "nat \<Rightarrow> nat" where
  "fib 0 = 1"
| "fib (Suc 0) = 1"
| "fib (Suc (Suc n)) = fib n + fib (Suc n)"
print_theorems (*cases, elims, induct, pelims, simps*)

(* Example from Defining Recursive Functions in Isabelle/HOL by Alexander Krauss *)
function even::"nat \<Rightarrow> bool"
 and     odd ::"nat \<Rightarrow> bool" where
  "even 0 = True"
| "odd  0 = False"
| "even (Suc n) = odd n"
| "odd  (Suc n) = even n"
  by pat_completeness auto

datatype 'a list = nil2 | cons2 "'a" "'a list"

(* Example from TIP benchmark https://github.com/tip-org/benchmarks *)
fun filter :: "('a => bool) => 'a list => 'a list" where
"filter p (nil2) = nil2"
| "filter p (cons2 y xs) =
     (if p y then cons2 y (filter p xs) else filter p xs)"
print_theorems (*cases, elims, induct, pelims, simps*)

(* Example from TIP benchmark https://github.com/tip-org/benchmarks *)
function nubBy :: "('a => ('a => bool)) => 'a list => 'a list" where
"nubBy xx (nil2) = nil2"
| "nubBy xx (cons2 z xs) =
     cons2 z (nubBy xx (filter (% (y2 :: 'a) => (~ ((xx z) y2))) xs))"
  by pat_completeness auto
print_theorems  (*cases, pelims, pinduct, psimps*)

(* Example from the old Isabelle tutorial *)
inductive_set even_set :: "nat set" where
zero_set: "0 \<in> even_set" |
step_set: "n \<in> even_set \<Longrightarrow> (Suc (Suc n)) \<in> even_set"
print_theorems 
(* cases, induct, inducts, intros, simps, step_set, zero_set, _def, cases induct, \<dots>*)

(*Probably we should use the type to detect if a constant is defined with the "inductive_set" keywords.*)
ML{* @{term "0 \<in> even_set"}; @{term "even_set"}; @{typ "nat set"} *}

(* test *)
fun identity::"'a \<Rightarrow> 'a" where "identity z = z"

term "append"
find_theorems name:"append." name:"simp"
find_theorems name:"append." name:"psimp"
find_theorems name:"append." name:"induct"
find_theorems name:"append."
term append

(* Example similar to the append function defined in Isabelle's standard library (src/HOL/List.thy) *)
primrec append2 :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
append_Nil2: "append2  nil2         ys = ys" |
append_Cons2:"append2 (cons2 x1 xs) ys = cons2 x1 (append2 xs ys)"
print_theorems

end