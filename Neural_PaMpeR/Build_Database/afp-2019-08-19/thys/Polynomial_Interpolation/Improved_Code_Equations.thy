(*  
    Author:      René Thiemann 
                 Akihisa Yamada
    License:     BSD
*)
section \<open>Improved Code Equations\<close>

text \<open>This theory contains improved code equations for certain algorithms.\<close>

theory Improved_Code_Equations
imports 
  "HOL-Computational_Algebra.Polynomial"
  "HOL-Library.Code_Target_Nat"
begin

subsection \<open>@{const divmod_integer}.\<close>

text \<open>We improve @{thm divmod_integer_code} by deleting @{const sgn}-expressions.\<close>

text \<open>We guard the application of divmod-abs' with the condition @{term "x \<ge> 0 \<and> y \<ge> 0"}, 
  so that application can be ensured on non-negative values. Hence, one can drop "abs" in 
   target language setup.\<close>

definition divmod_abs' where 
  "x \<ge> 0 \<Longrightarrow> y \<ge> 0 \<Longrightarrow> divmod_abs' x y = Code_Numeral.divmod_abs x y" 

(* led to an another 10 % improvement on factorization example *)

lemma divmod_integer_code''[code]: "divmod_integer k l =
  (if k = 0 then (0, 0)
    else if l > 0 then
            (if k > 0 then divmod_abs' k l
             else case divmod_abs' (- k) l of (r, s) \<Rightarrow>
                  if s = 0 then (- r, 0) else (- r - 1, l - s))
    else if l = 0 then (0, k)
    else apsnd uminus
            (if k < 0 then divmod_abs' (-k) (-l)
             else case divmod_abs' k (-l) of (r, s) \<Rightarrow>
                  if s = 0 then (- r, 0) else (- r - 1, - l - s)))"
   unfolding divmod_integer_code
   by (cases "l = 0"; cases "l < 0"; cases "l > 0"; auto split: prod.splits simp: divmod_abs'_def divmod_abs_def)

code_printing \<comment> \<open>FIXME illusion of partiality\<close>
  constant divmod_abs' \<rightharpoonup>
    (SML) "IntInf.divMod/ ( _,/ _ )"
    and (Eval) "Integer.div'_mod/ ( _ )/ ( _ )"
    and (OCaml) "Z.div'_rem"
    and (Haskell) "divMod/ ( _ )/ ( _ )"
    and (Scala) "!((k: BigInt) => (l: BigInt) =>/ if (l == 0)/ (BigInt(0), k) else/ (k '/% l))"

subsection \<open>@{const Divides.divmod_nat}.\<close>
text \<open>We implement @{const Divides.divmod_nat} via @{const divmod_integer}
  instead of invoking both division and modulo separately, 
  and we further simplify the case-analysis which is
  performed in @{thm divmod_integer_code''}.\<close>

lemma divmod_nat_code'[code]: "Divides.divmod_nat m n = (
  let k = integer_of_nat m; l = integer_of_nat n
  in map_prod nat_of_integer nat_of_integer
  (if k = 0 then (0, 0)
    else if l = 0 then (0,k) else
            divmod_abs' k l))"
  using divmod_nat_code [of m n]
  by (simp add: divmod_abs'_def integer_of_nat_eq_of_nat Let_def)


subsection \<open>@{const binomial}\<close>

lemma binomial_code[code]:
  "n choose k = (if k \<le> n then fact n div (fact k * fact (n - k)) else 0)"
  using binomial_eq_0[of n k] binomial_altdef_nat[of k n] by simp

end
