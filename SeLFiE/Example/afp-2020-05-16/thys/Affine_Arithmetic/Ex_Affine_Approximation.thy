section \<open>Examples\<close>
theory Ex_Affine_Approximation
imports
  Affine_Code
  Print
  Float_Real
begin

context includes floatarith_notation begin

definition "rotate_fas =
  [Cos (Rad_of (Var 2)) * Var 0 - Sin (Rad_of (Var 2)) * Var 1,
   Sin (Rad_of (Var 2)) * Var 0 + Cos (Rad_of (Var 2)) * Var 1]"

definition "rotate_slp = slp_of_fas rotate_fas"
definition "approx_rotate p t X = approx_slp_outer p 3 rotate_slp X"

fun rotate_aform where
  "rotate_aform x i = (let r = (((the o (\<lambda>x. approx_rotate 30 (FloatR 1 (-3)) x))^^i) x) in
    (r ! 0) \<times>\<^sub>a (r ! 1) \<times>\<^sub>a (r ! 2))"

value [code] "rotate_aform (aforms_of_ivls [2, 1, 45] [3, 5, 45]) 70"

definition "translate_slp = slp_of_fas [Var 0 + Var 2, Var 1 + Var 2]"
fun translatei where "translatei x i = (((the o (\<lambda>x. approx_slp_outer 7 3 translate_slp x))^^i) x)"

value "translatei (aforms_of_ivls [2, 1, 512] [3, 5, 512]) 50"

end

hide_const rotate_fas rotate_slp approx_rotate rotate_aform translate_slp translatei

end
