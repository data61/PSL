(*  
    Author:      René Thiemann 
    License:     LPGL
*)
subsection \<open>Displaying Polynomials\<close>

text \<open>We define a method which converts polynomials to strings and registers it in the Show class.\<close>

theory Show_Poly
imports 
  Show_Instances
  "HOL-Computational_Algebra.Polynomial"
begin

fun show_factor :: "nat \<Rightarrow> string" where
  "show_factor 0 = []"
| "show_factor (Suc 0) = ''x''"
| "show_factor n = ''x^'' @ show n"

fun show_coeff_factor where
  "show_coeff_factor c n = (if n = 0 then show c else if c = 1 then show_factor n else show c @ show_factor n)"

fun show_poly_main :: "nat \<Rightarrow> 'a :: {zero,one,show} list \<Rightarrow> string" where
  "show_poly_main _ [] = ''0''"
| "show_poly_main n [c] = show_coeff_factor c n"
| "show_poly_main n (c # cs) = (if c = 0 then show_poly_main (Suc n) cs else
    show_coeff_factor c n @ '' + '' @ show_poly_main (Suc n) cs)"

definition show_poly :: "'a :: {zero,one,show}poly \<Rightarrow> string" where
  "show_poly p = show_poly_main 0 (coeffs p)"

definition showsp_poly :: "'a :: {zero,one,show}poly showsp"
where
  "showsp_poly p x = shows_string (show_poly x)"


instantiation poly :: ("{show,one,zero}") "show"
begin

definition "shows_prec p (x :: 'a poly) = showsp_poly p x"
definition "shows_list (ps :: 'a poly list) = showsp_list shows_prec 0 ps"

lemma show_law_poly [show_law_simps]:
  "shows_prec p (a :: 'a poly) (r @ s) = shows_prec p a r @ s"
  by (simp add: shows_prec_poly_def showsp_poly_def show_law_simps)

instance by standard (auto simp: shows_list_poly_def show_law_simps)

end

end
