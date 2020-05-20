(*  
    Author:      René Thiemann 
    License:     LGPL
*)
section \<open>Show for Complex Numbers\<close>

text \<open>We print complex numbers as real and imaginary parts. Note that by transitivity, this theory
  demands that an implementations for \textit{show-real} is available, e.g., by using 
  one of the theories \textit{Show-Real-Impl} or \textit{../Algebraic-Numbers/Show-Real-...}.\<close>
theory Show_Complex
imports 
  HOL.Complex
  Show_Real
begin

definition "show_complex x = (
  let r = Re x; i = Im x in
  if (i = 0) then show_real r else if 
  r = 0 then show_real i @ ''i'' else
  ''('' @ show_real r @ ''+'' @ show_real i @ ''i)'')"

definition showsp_complex :: "complex showsp"
where
  "showsp_complex p x y =
    (show_complex x @ y)"

lemma show_law_complex [show_law_intros]:
  "show_law showsp_complex r"
  by (rule show_lawI) (simp add: showsp_complex_def show_law_simps)

lemma showsp_complex_append [show_law_simps]:
  "showsp_complex p r (x @ y) = showsp_complex p r x @ y"
  by (intro show_lawD show_law_intros)

local_setup \<open>
  Show_Generator.register_foreign_showsp @{typ complex} @{term "showsp_complex"} @{thm show_law_complex}
\<close>

derive "show" complex
end
