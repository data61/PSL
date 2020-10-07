(*
  File:    Linear_Recurrences_Pretty.thy
  Author:  Manuel Eberl, TU München
*)
section \<open>Pretty-printing for linear recurrence solutions\<close>
theory Linear_Recurrences_Pretty
imports
  Complex_Main Rational_FPS_Solver 
  "Show.Show_Complex"
  "Show.Show_Poly"
begin

context
begin

qualified fun parenthesized_aux :: "nat \<Rightarrow> string \<Rightarrow> bool" where
  "parenthesized_aux n [] = True"
| "parenthesized_aux n [c] = True"
| "parenthesized_aux n (c#cs) = 
     (if c = CHR '')'' then n > 0 \<and> parenthesized_aux (n - 1) cs
      else if c = CHR ''('' then parenthesized_aux (n + 1) cs
      else parenthesized_aux n cs)"

qualified definition parenthesized :: "string \<Rightarrow> bool" where
  "parenthesized s = (case s of c#cs \<Rightarrow> c = CHR ''('' \<and> parenthesized_aux 0 cs | _ \<Rightarrow> False)"

qualified definition is_num :: "string \<Rightarrow> bool" where
  "is_num s = (list_all (\<lambda>c. c \<in> set ''0123456789'') s  \<or> parenthesized s)"
  
qualified definition is_simple_poly :: "string \<Rightarrow> bool" where
  "is_simple_poly s \<longleftrightarrow> list_all (\<lambda>c. c \<in> set ''0123456789-*^x '') s \<or> parenthesized s"

qualified definition show_base where
  "show_base x = (let s = show x in if is_num s then s else ''('' @ s @ '')'')"
  
qualified definition show_poly' where
  "show_poly' p = (let s = show_poly p in if is_simple_poly s then s else ''('' @ s @ '')'')"

qualified definition show_ratfps_solution_summand 
  :: "('a :: {comm_semiring_1,show}) poly \<times> 'a \<Rightarrow> string" where
  "show_ratfps_solution_summand x = (case x of (p, c) \<Rightarrow> 
     (if p = 1 then 
        if c = 1 then ''1'' else show_base c @ '' ^ x'' 
      else 
        if c = 1 then show_poly' p else show_poly' p @ '' * '' @ show_base c @ '' ^ x''))" 

qualified fun intercalate :: "'a list \<Rightarrow> 'a list list \<Rightarrow> 'a list" where
  "intercalate _ []     = []"
| "intercalate _ [y]    = y"
| "intercalate x (y#ys) = y @ x @ intercalate x ys"

qualified definition show_ratfps_kronecker :: "'a :: {one,show} \<Rightarrow> nat \<Rightarrow> string" where
  "show_ratfps_kronecker c n = 
     (if c = 1 then [] else show c @ '' * '') @ ''[x = '' @ show n @ '']''"  

definition show_ratfps_solution :: 
    "'a::{comm_semiring_1,show} poly \<times> ('a poly \<times> 'a) list \<Rightarrow> string" where
  "show_ratfps_solution x = 
     (case x of (a, bs) \<Rightarrow> intercalate '' + '' 
       ([show_ratfps_kronecker c n. (c,n) \<leftarrow> zip (coeffs a) [0..<Suc (degree a)], c \<noteq> 0] @ 
         map show_ratfps_solution_summand bs))"

end

value [code] "show_ratfps_solution ([:0,0,-3:], [([:0,0,2::int:],-2), ([:-1,2:],-1)])"

end
