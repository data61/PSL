(*  
    Author:      René Thiemann 
    License:     LGPL
*)
section \<open>Show for Real Numbers -- Interface\<close>

text \<open>We just demand that there is some function from reals to string and register this
  as show-function. Implementations are available in one of the theories \textit{Show-Real-Impl}
  and \textit{../Algebraic-Numbers/Show-Real-...}.\<close>

theory Show_Real
imports 
  HOL.Real
  Show
begin

consts show_real :: "real \<Rightarrow> string"

definition showsp_real :: "real showsp"
where
  "showsp_real p x y =
    (show_real x @ y)"

lemma show_law_real [show_law_intros]:
  "show_law showsp_real r"
  by (rule show_lawI) (simp add: showsp_real_def show_law_simps)

lemma showsp_real_append [show_law_simps]:
  "showsp_real p r (x @ y) = showsp_real p r x @ y"
  by (intro show_lawD show_law_intros)

local_setup \<open>
  Show_Generator.register_foreign_showsp @{typ real} @{term "showsp_real"} @{thm show_law_real}
\<close>

derive "show" real
end
