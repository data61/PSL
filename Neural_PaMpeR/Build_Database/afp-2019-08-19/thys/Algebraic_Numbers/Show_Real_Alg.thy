(*  
    Author:      René Thiemann 
                 Akihisa Yamada
    License:     BSD
*)
section \<open>Show for Real Algebraic Numbers -- Interface\<close>

text \<open>We just demand that there is some function from real algebraic numbers to string and register this
  as show-function and use it to implement \textit{show-real}.
  
  Implementations for real algebraic numbers are available in one of the theories \textit{Show-Real-Precise}
  and \textit{Show-Real-Approx}.\<close>
theory Show_Real_Alg
imports 
  Real_Algebraic_Numbers
  Show.Show_Real
begin

consts show_real_alg :: "real_alg \<Rightarrow> string"

definition showsp_real_alg :: "real_alg showsp" where
  "showsp_real_alg p x y = (show_real_alg x @ y)"

lemma show_law_real_alg [show_law_intros]:
  "show_law showsp_real_alg r"
  by (rule show_lawI) (simp add: showsp_real_alg_def show_law_simps)

lemma showsp_real_alg_append [show_law_simps]:
  "showsp_real_alg p r (x @ y) = showsp_real_alg p r x @ y"
  by (intro show_lawD show_law_intros)

local_setup \<open>
  Show_Generator.register_foreign_showsp @{typ real_alg} @{term "showsp_real_alg"} @{thm show_law_real_alg}
\<close>

derive "show" real_alg

text \<open>We now define @{const show_real}.\<close>
overloading show_real \<equiv> show_real
begin
  definition "show_real \<equiv> show_real_alg o real_alg_of_real"
end

end
