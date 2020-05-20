(*  Title:       Knuth-Bendix Orders for Lambda-Free Higher-Order Terms
    Author:      Heiko Becker <heikobecker92@gmail.com>, 2016
    Author:      Jasmin Blanchette <jasmin.blanchette at inria.fr>, 2016
    Author:      Uwe Waldmann <waldmann at mpi-inf.mpg.de>, 2016
    Author:      Daniel Wand <dwand at mpi-inf.mpg.de>, 2016
    Maintainer:  Jasmin Blanchette <jasmin.blanchette at inria.fr>
*)

section \<open>Knuth--Bendix Orders for Lambda-Free Higher-Order Terms\<close>

theory Lambda_Free_KBOs
imports Lambda_Free_KBO_App Lambda_Free_KBO_Basic Lambda_Free_TKBO_Coefs Lambda_Encoding_KBO
begin

locale simple_kbo_instances
begin

definition arity_sym :: "nat \<Rightarrow> enat" where
  "arity_sym n = \<infinity>"

definition arity_var :: "nat \<Rightarrow> enat" where
  "arity_var n = \<infinity>"

definition ground_head_var :: "nat \<Rightarrow> nat set" where
  "ground_head_var x = UNIV"

definition gt_sym :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
  "gt_sym g f \<longleftrightarrow> g > f"

definition \<epsilon> :: nat where
  "\<epsilon> = 1"

definition \<delta> :: nat where
  "\<delta> = 0"

definition wt_sym :: "nat \<Rightarrow> nat" where
  "wt_sym n = 1"

definition wt_sym\<^sub>h :: "nat \<Rightarrow> hmultiset" where
  "wt_sym\<^sub>h n = 1"

definition coef_sym\<^sub>h :: "nat \<Rightarrow> nat \<Rightarrow> hmultiset" where
  "coef_sym\<^sub>h n i = 1"

sublocale kbo_app: kbo_app gt_sym wt_sym \<epsilon> len_lexext
  by unfold_locales (auto simp: gt_sym_def \<epsilon>_def wt_sym_def intro: wf_less[folded wfP_def])

sublocale kbo_basic: kbo_basic gt_sym wt_sym \<epsilon> "\<lambda>f. len_lexext" ground_head_var
  by unfold_locales (auto simp: ground_head_var_def gt_sym_def \<epsilon>_def wt_sym_def)

sublocale kbo_std: kbo_std ground_head_var gt_sym \<epsilon> \<delta> "\<lambda>f. len_lexext" arity_sym arity_var wt_sym
  by unfold_locales
    (auto simp: arity_sym_def arity_var_def ground_head_var_def \<epsilon>_def \<delta>_def wt_sym_def)

sublocale tkbo_coefs: tkbo_coefs ground_head_var gt_sym \<epsilon> \<delta> "\<lambda>f. len_lexext" arity_sym arity_var
    wt_sym\<^sub>h coef_sym\<^sub>h
  by unfold_locales (auto simp: \<epsilon>_def \<delta>_def wt_sym\<^sub>h_def coef_sym\<^sub>h_def)

end

end
