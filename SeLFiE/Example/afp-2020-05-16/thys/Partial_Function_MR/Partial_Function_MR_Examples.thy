(* Author: Rene Thiemann, License: LGPL *)

section \<open>Examples\<close>
theory Partial_Function_MR_Examples
imports 
  Partial_Function_MR
  "HOL-Library.Monad_Syntax"
  HOL.Rat
begin

subsection \<open>Collatz function\<close>
text \<open>In the following, we define the Collatz function, 
which is artificially encoded via mutually recursive functions.
As second argument we store the intermediate values.
It is currently unknown whether this function is terminating for all inputs or not.\<close>

partial_function_mr (tailrec) collatz and even_case and odd_case where
  "collatz (x :: int) xs = 
    (if (x \<le> 1) then rev (x # xs) else 
    (if (x mod 2 = 0) then even_case x (x # xs)
     else odd_case x xs))"
| "even_case x xs = collatz (x div 2) xs"
| [simp]: "odd_case x xs = collatz (3 * x + 1) (x # xs)"

text \<open>The equations are registered as code-equations.\<close>
lemma "length (collatz 327 []) = 144" by eval

text \<open>The equations are accessible via .simps, but are not put in the standard simpset.\<close>
lemma "collatz 5 [] = [5,16,8,4,2,1]" by (simp add: collatz.simps even_case.simps)

subsection \<open>Evaluating expressions\<close>
text \<open>Note that we also provide a least fixpoint operator.
  Hence, the evaluation function will clearly be partial.
  The example also illustrates the usage
  of polymorphism and of different return types.\<close>

text \<open>In the following datatype, \isa{Mu b f a} encodes the least $n$ such that $b(f^n(a))$.\<close>
datatype 'a bexp = 
  BConst bool
| Less "'a aexp" "'a aexp"
| Eq "'a aexp" "'a aexp"
| And "'a bexp" "'a bexp"
and 'a aexp =
  Plus "'a aexp" "'a aexp"
| Div "'a aexp" "'a aexp"
| IfThenElse "'a bexp" "'a aexp" "'a aexp"
| AConst 'a
| Mu "'a \<Rightarrow> 'a bexp" "'a \<Rightarrow> 'a aexp" "'a aexp" 

partial_function_mr (option) 
  b_eval and a_eval and mu_eval where
  "b_eval bexp = (case bexp of
     BConst b \<Rightarrow> Some b
   | Less a1 a2 \<Rightarrow> do {
        x1 \<leftarrow> a_eval a1;
        x2 \<leftarrow> a_eval a2;
        Some (x1 < x2)
     }
   | Eq a1 a2 \<Rightarrow> do {
        x1 \<leftarrow> a_eval a1;
        x2 \<leftarrow> a_eval a2;
        Some (x1 = x2)
     }
   | And be1 be2 \<Rightarrow> do {
        b1 \<leftarrow> b_eval be1;
        b2 \<leftarrow> b_eval be2;
        Some (b1 \<and> b2)
     }
  )"
| "a_eval aexp = (case aexp of
     AConst x \<Rightarrow> Some x
   | Plus a1 a2 \<Rightarrow> do {
        x1 \<leftarrow> a_eval a1;
        x2 \<leftarrow> a_eval a2;
        Some (x1 + x2)
     }
   | Div a1 a2 \<Rightarrow> do {
        x1 \<leftarrow> a_eval a1;
        x2 \<leftarrow> a_eval a2;
        if (x2 = 0) then None else Some (x1 / x2)
     }
   | IfThenElse bexp a1 a2 \<Rightarrow> do {
        b \<leftarrow> b_eval bexp;
        (if b then a_eval a1 else a_eval a2)
     }
   | Mu b f a \<Rightarrow> do {
        mu_eval b f a 0
     }
  )"
| "mu_eval b f a n = do {
      x \<leftarrow> a_eval a;
      check \<leftarrow> b_eval (b x); 
      (if check then Some (of_nat n) else 
       mu_eval b f (f x) (Suc n))
   }"

definition 
  "five_minus_two = a_eval (Mu (\<lambda> x. Eq (AConst 5) (AConst x)) (\<lambda> x. Plus (AConst x) (AConst 1)) (AConst (2 :: rat)))"

value five_minus_two


subsection \<open>An example with contexts\<close>

text \<open>Mutual recursive partial functions also work within contexts.\<close>

context
  fixes y :: int
begin
partial_function_mr (tailrec) foo and bar where
  "foo x = (if x = y then foo (x - 1) else (bar x (y - 1)))" 
| "bar x z = foo (x + (1 :: int) + y)" 
end


end
