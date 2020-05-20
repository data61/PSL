(*  Title:       The Applicative Knuth-Bendix Order for Lambda-Free Higher-Order Terms
    Author:      Jasmin Blanchette <jasmin.blanchette at inria.fr>, 2016
    Maintainer:  Jasmin Blanchette <jasmin.blanchette at inria.fr>
*)

section \<open>The Applicative Knuth--Bendix Order for Lambda-Free Higher-Order Terms\<close>

theory Lambda_Free_KBO_App
imports Lambda_Free_KBO_Util
abbrevs ">t" = ">\<^sub>t"
  and "\<ge>t" = "\<ge>\<^sub>t"
begin

text \<open>
This theory defines the applicative Knuth--Bendix order, a variant of KBO for \<open>\<lambda>\<close>-free
higher-order terms. It corresponds to the order obtained by applying the standard first-order KBO on
the applicative encoding of higher-order terms and assigning the lowest precedence to the
application symbol.
\<close>

locale kbo_app = gt_sym "(>\<^sub>s)"
    for gt_sym :: "'s \<Rightarrow> 's \<Rightarrow> bool" (infix ">\<^sub>s" 50) +
  fixes
    wt_sym :: "'s \<Rightarrow> nat" and
    \<epsilon> :: nat and
    ext :: "(('s, 'v) tm \<Rightarrow> ('s, 'v) tm \<Rightarrow> bool) \<Rightarrow> ('s, 'v) tm list \<Rightarrow> ('s, 'v) tm list \<Rightarrow> bool"
  assumes
    \<epsilon>_gt_0: "\<epsilon> > 0" and
    wt_sym_ge_\<epsilon>: "wt_sym f \<ge> \<epsilon>" and
    ext_ext_irrefl_before_trans: "ext_irrefl_before_trans ext" and
    ext_ext_compat_list: "ext_compat_list ext" and
    ext_ext_hd_or_tl: "ext_hd_or_tl ext"
begin

lemma ext_mono[mono]: "gt \<le> gt' \<Longrightarrow> ext gt \<le> ext gt'"
  by (simp add: ext.mono ext_ext_compat_list[unfolded ext_compat_list_def, THEN conjunct1])

fun wt :: "('s, 'v) tm \<Rightarrow> nat" where
  "wt (Hd (Var x)) = \<epsilon>"
| "wt (Hd (Sym f)) = wt_sym f"
| "wt (App s t) = wt s + wt t"

inductive gt :: "('s, 'v) tm \<Rightarrow> ('s, 'v) tm \<Rightarrow> bool" (infix ">\<^sub>t" 50) where
  gt_wt: "vars_mset t \<supseteq># vars_mset s \<Longrightarrow> wt t > wt s \<Longrightarrow> t >\<^sub>t s"
| gt_sym_sym: "wt_sym g = wt_sym f \<Longrightarrow> g >\<^sub>s f \<Longrightarrow> Hd (Sym g) >\<^sub>t Hd (Sym f)"
| gt_sym_app: "vars s = {} \<Longrightarrow> wt t = wt s \<Longrightarrow> t = Hd (Sym g) \<Longrightarrow> is_App s \<Longrightarrow> t >\<^sub>t s"
| gt_app_app: "vars_mset t \<supseteq># vars_mset s \<Longrightarrow> wt t = wt s \<Longrightarrow> t = App t1 t2 \<Longrightarrow> s = App s1 s2 \<Longrightarrow>
    ext (>\<^sub>t) [t1, t2] [s1, s2] \<Longrightarrow> t >\<^sub>t s"

abbreviation ge :: "('s, 'v) tm \<Rightarrow> ('s, 'v) tm \<Rightarrow> bool" (infix "\<ge>\<^sub>t" 50) where
  "t \<ge>\<^sub>t s \<equiv> t >\<^sub>t s \<or> t = s"

end

end
