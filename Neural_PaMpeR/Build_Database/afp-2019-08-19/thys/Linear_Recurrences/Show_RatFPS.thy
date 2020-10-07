(*
  File:    Show_RatFPS.thy
  Author:  Manuel Eberl, TU München
*)
section \<open>Pretty-printing for rational formal power series\<close>
theory Show_RatFPS
imports
  RatFPS
  Show.Show_Poly
begin

definition ratfps_parens where
  "ratfps_parens s = (if list_ex (\<lambda>c. c \<in> set ''+-'') (tl s) then ''('' @ s @ '')'' else s)"

definition "show_ratfps x = (case quot_of_ratfps x of (p, q) \<Rightarrow>
  if q = 1 then show p else ratfps_parens (show p) @ '' / '' @ ratfps_parens (show q))"

definition showsp_ratfps :: "'a :: {field, euclidean_ring_gcd,show} ratfps showsp"
where
  "showsp_ratfps p x y = (show_ratfps x @ y)"

instantiation ratfps:: ("{show,field,euclidean_ring_gcd}") "show"
begin

definition "shows_prec p (x :: 'a ratfps) = showsp_ratfps p x"
definition "shows_list (ps :: 'a ratfps list) = showsp_list shows_prec 0 ps"

lemma show_law_ratfps [show_law_simps]:
  "shows_prec p (a :: 'a ratfps) (r @ s) = shows_prec p a r @ s"
  by (simp add: shows_prec_ratfps_def showsp_ratfps_def show_law_simps)

instance by standard (auto simp: shows_list_ratfps_def show_law_simps)

end

end
