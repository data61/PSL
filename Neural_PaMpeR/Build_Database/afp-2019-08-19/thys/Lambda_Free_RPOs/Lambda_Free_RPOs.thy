(*  Title:       Recursive Path Orders for Lambda-Free Higher-Order Terms
    Author:      Jasmin Blanchette <jasmin.blanchette at inria.fr>, 2016
    Author:      Uwe Waldmann <waldmann at mpi-inf.mpg.de>, 2016
    Author:      Daniel Wand <dwand at mpi-inf.mpg.de>, 2016
    Maintainer:  Jasmin Blanchette <jasmin.blanchette at inria.fr>
*)

section \<open>Recursive Path Orders for Lambda-Free Higher-Order Terms\<close>

theory Lambda_Free_RPOs
imports Lambda_Free_RPO_App Lambda_Free_RPO_Optim Lambda_Encoding
begin

locale simple_rpo_instances
begin

definition arity_sym :: "nat \<Rightarrow> enat" where
  "arity_sym n = \<infinity>"

definition arity_var :: "nat \<Rightarrow> enat" where
  "arity_var n = \<infinity>"

definition ground_head_var :: "nat \<Rightarrow> nat set" where
  "ground_head_var x = UNIV"

definition gt_sym :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
  "gt_sym g f \<longleftrightarrow> g > f"

sublocale app: rpo_app gt_sym len_lexext
  by unfold_locales (auto simp: gt_sym_def intro: wf_less[folded wfP_def])

sublocale std: rpo ground_head_var gt_sym "\<lambda>f. len_lexext" arity_sym arity_var
  by unfold_locales (auto simp: arity_var_def arity_sym_def ground_head_var_def)

sublocale optim: rpo_optim ground_head_var gt_sym "\<lambda>f. len_lexext" arity_sym arity_var
  by unfold_locales

end

end
