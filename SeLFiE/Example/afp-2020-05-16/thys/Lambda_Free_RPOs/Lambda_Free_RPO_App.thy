(*  Title:       The Applicative Recursive Path Order for Lambda-Free Higher-Order Terms
    Author:      Jasmin Blanchette <jasmin.blanchette at inria.fr>, 2016
    Maintainer:  Jasmin Blanchette <jasmin.blanchette at inria.fr>
*)

section \<open>The Applicative Recursive Path Order for Lambda-Free Higher-Order Terms\<close>

theory Lambda_Free_RPO_App
imports Lambda_Free_Term Extension_Orders
abbrevs ">t" = ">\<^sub>t"
  and "\<ge>t" = "\<ge>\<^sub>t"
begin

text \<open>
This theory defines the applicative recursive path order (RPO), a variant of RPO
for \<open>\<lambda>\<close>-free higher-order terms. It corresponds to the order obtained by
applying the standard first-order RPO on the applicative encoding of higher-order
terms and assigning the lowest precedence to the application symbol.
\<close>

locale rpo_app = gt_sym "(>\<^sub>s)"
    for gt_sym :: "'s \<Rightarrow> 's \<Rightarrow> bool" (infix ">\<^sub>s" 50) +
  fixes ext :: "(('s, 'v) tm \<Rightarrow> ('s, 'v) tm \<Rightarrow> bool) \<Rightarrow> ('s, 'v) tm list \<Rightarrow> ('s, 'v) tm list \<Rightarrow> bool"
  assumes
    ext_ext_trans_before_irrefl: "ext_trans_before_irrefl ext" and
    ext_ext_compat_list: "ext_compat_list ext"
begin

lemma ext_mono[mono]: "gt \<le> gt' \<Longrightarrow> ext gt \<le> ext gt'"
  by (simp add: ext.mono ext_ext_compat_list[unfolded ext_compat_list_def, THEN conjunct1])

inductive gt :: "('s, 'v) tm \<Rightarrow> ('s, 'v) tm \<Rightarrow> bool" (infix ">\<^sub>t" 50) where
  gt_sub: "is_App t \<Longrightarrow> (fun t >\<^sub>t s \<or> fun t = s) \<or> (arg t >\<^sub>t s \<or> arg t = s) \<Longrightarrow> t >\<^sub>t s"
| gt_sym_sym: "g >\<^sub>s f \<Longrightarrow> Hd (Sym g) >\<^sub>t Hd (Sym f)"
| gt_sym_app: "Hd (Sym g) >\<^sub>t s1 \<Longrightarrow> Hd (Sym g) >\<^sub>t s2 \<Longrightarrow> Hd (Sym g) >\<^sub>t App s1 s2"
| gt_app_app: "ext (>\<^sub>t) [t1, t2] [s1, s2] \<Longrightarrow> App t1 t2 >\<^sub>t s1 \<Longrightarrow> App t1 t2 >\<^sub>t s2 \<Longrightarrow>
    App t1 t2 >\<^sub>t App s1 s2"

abbreviation ge :: "('s, 'v) tm \<Rightarrow> ('s, 'v) tm \<Rightarrow> bool" (infix "\<ge>\<^sub>t" 50) where
  "t \<ge>\<^sub>t s \<equiv> t >\<^sub>t s \<or> t = s"

end

end
