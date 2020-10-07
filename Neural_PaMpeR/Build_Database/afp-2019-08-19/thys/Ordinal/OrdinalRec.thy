(*  Title:       Countable Ordinals

    Author:      Brian Huffman, 2005
    Maintainer:  Brian Huffman <brianh at cse.ogi.edu>
*)

section \<open>Recursive Definitions\<close>

theory OrdinalRec
imports OrdinalCont
begin

definition
  oPrec :: "ordinal \<Rightarrow> ordinal" where
  "oPrec x = (THE p. x = oSuc p)"

lemma oPrec_oSuc [simp]: "oPrec (oSuc x) = x"
by (unfold oPrec_def, rule the_equality, simp_all)

lemma oPrec_less: "\<exists>p. x = oSuc p \<Longrightarrow> oPrec x < x"
by clarsimp

definition
  ordinal_rec0 ::
    "['a, ordinal \<Rightarrow> 'a \<Rightarrow> 'a, (nat \<Rightarrow> 'a) \<Rightarrow> 'a, ordinal] \<Rightarrow> 'a" where
  "ordinal_rec0 z s l \<equiv> wfrec {(x,y). x < y} (\<lambda>F x.
    if x = 0 then z else
    if (\<exists>p. x = oSuc p) then s (oPrec x) (F (oPrec x)) else
    (THE y. \<forall>f. (\<forall>n. f n < oLimit f) \<and> oLimit f = x
            \<longrightarrow> l (\<lambda>n. F (f n)) = y))"

lemma ordinal_rec0_0:
"ordinal_rec0 z s l 0 = z"
 apply (rule trans[OF def_wfrec[OF ordinal_rec0_def wf]])
 apply simp
done

lemma ordinal_rec0_oSuc:
"ordinal_rec0 z s l (oSuc x) = s x (ordinal_rec0 z s l x)"
 apply (rule trans[OF def_wfrec[OF ordinal_rec0_def wf]])
 apply (simp add: cut_apply)
done

lemma limit_ordinal_not_0: "limit_ordinal x \<Longrightarrow> x \<noteq> 0"
by (clarsimp)

lemma limit_ordinal_not_oSuc: "limit_ordinal x \<Longrightarrow> x \<noteq> oSuc p"
by (clarsimp)

lemma ordinal_rec0_limit_ordinal:
"limit_ordinal x \<Longrightarrow> ordinal_rec0 z s l x =
 (THE y. \<forall>f. (\<forall>n. f n < oLimit f) \<and> oLimit f = x \<longrightarrow> 
   l (\<lambda>n. ordinal_rec0 z s l (f n)) = y)"
 apply (rule trans[OF def_wfrec[OF ordinal_rec0_def wf]])
 apply (simp add: limit_ordinal_not_oSuc limit_ordinal_not_0)
 apply (rule_tac f=The in arg_cong, rule ext)
 apply (rule_tac f=All in arg_cong, rule ext)
 apply safe
  apply (simp add: cut_apply)
 apply (simp add: cut_apply)
done


subsection \<open>Partial orders\<close>

locale porder =
  fixes le  :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infixl "<<" 55)
assumes po_refl:    "\<And>x. x << x"
    and po_trans:   "\<And>x y z. \<lbrakk>x << y; y << z\<rbrakk> \<Longrightarrow> x << z"
    and po_antisym: "\<And>x y. \<lbrakk>x << y; y << x\<rbrakk> \<Longrightarrow> x = y"

lemma porder_order: "porder ((\<le>) :: 'a::order \<Rightarrow> 'a \<Rightarrow> bool)"
 apply (rule porder.intro)
   apply (rule order_refl)
  apply (rule order_trans, assumption+)
 apply (rule order_antisym, assumption+)
done

lemma (in porder) flip: "porder (\<lambda>x y. y << x)"
 apply (rule porder.intro)
   apply (rule po_refl)
  apply (rule po_trans, assumption+)
 apply (rule po_antisym, assumption+)
done

locale omega_complete = porder +
fixes lub :: "(nat \<Rightarrow> 'a) \<Rightarrow> 'a"
assumes is_ub_lub: "\<And>f n. f n << lub f"
assumes is_lub_lub: "\<And>f x. \<forall>n. f n << x \<Longrightarrow> lub f << x"

lemma (in omega_complete) lub_cong_lemma:
"\<lbrakk>\<forall>n. f n < oLimit f; \<forall>m. g m < oLimit g; oLimit f \<le> oLimit g;
 \<forall>y<oLimit g. \<forall>x\<le>y. F x << F y\<rbrakk>
 \<Longrightarrow> lub (\<lambda>n. F (f n)) << lub (\<lambda>n. F (g n))"
 apply (rule is_lub_lub[rule_format])
 apply (subgoal_tac "f n < oLimit g")
  apply (drule less_oLimitD, clarify, rename_tac m)
  apply (drule_tac x="g m" in spec, drule mp)
   apply (erule spec)
  apply (drule_tac x="f n" in spec, drule mp)
   apply (erule order_less_imp_le)
  apply (erule po_trans)
  apply (rule is_ub_lub)
 apply (rule order_less_le_trans)
  apply (erule spec)
 apply assumption
done

lemma (in omega_complete) lub_cong:
"\<lbrakk>\<forall>n. f n < oLimit f; \<forall>m. g m < oLimit g; oLimit f = oLimit g;
 \<forall>y<oLimit g. \<forall>x\<le>y. F x << F y\<rbrakk>
 \<Longrightarrow> lub (\<lambda>n. F (f n)) = lub (\<lambda>n. F (g n))"
 apply (rule po_antisym)
  apply (rule lub_cong_lemma, assumption+)
   apply (simp add: po_refl)
  apply assumption
 apply (rule lub_cong_lemma, assumption+)
  apply (simp add: po_refl)
 apply (drule sym, simp)
done

lemma (in omega_complete) ordinal_rec0_mono_lemma:
assumes s: "\<forall>p x. x << s p x"
shows "\<forall>y\<le>w. \<forall>x\<le>y. ordinal_rec0 z s lub x << ordinal_rec0 z s lub y"
 apply (rule_tac a=w in oLimit_induct)
   apply (simp add: po_refl)
  apply clarify
  apply (erule le_oSucE, simp, clarsimp)
  apply (erule le_oSucE)
   apply (drule spec, drule mp, rule order_refl)
   apply (drule spec, drule mp, assumption)
   apply (erule po_trans)
   apply (simp add: ordinal_rec0_oSuc s)
  apply (simp add: po_refl)
 apply clarify
 apply (erule le_oLimitE)
  apply simp
 apply clarsimp
 apply (subgoal_tac "ordinal_rec0 z s lub (oLimit f) =
                     lub (\<lambda>n. ordinal_rec0 z s lub (f n))")
  apply (erule le_oLimitE)
   apply (drule_tac x=n in spec)
   apply (drule spec, drule mp, rule order_refl)
   apply (drule spec, drule mp, assumption)
   apply (erule po_trans)
   apply (simp, rule is_ub_lub)
  apply (simp add: po_refl)
 apply (simp only: ordinal_rec0_limit_ordinal strict_mono_limit_ordinal)
 apply (rule the_equality, clarify)
  apply (rule lub_cong, assumption)
    apply (simp add: strict_mono_less_oLimit)
   apply assumption
  apply clarify
  apply (drule less_oLimitD, clarify)
  apply (drule order_less_imp_le)
  apply simp
 apply (drule_tac x=f in spec, simp add: strict_mono_less_oLimit)
done

lemma (in omega_complete) ordinal_rec0_mono:
assumes s: "\<forall>p x. x << s p x"
shows "x \<le> y \<Longrightarrow> ordinal_rec0 z s lub x << ordinal_rec0 z s lub y"
 apply (rule ordinal_rec0_mono_lemma[OF s, rule_format])
  apply (rule order_refl)
 apply assumption
done

lemma (in omega_complete) ordinal_rec0_oLimit:
assumes s: "\<forall>p x. x << s p x"
shows "ordinal_rec0 z s lub (oLimit f) =
         lub (\<lambda>n. ordinal_rec0 z s lub (f n))"
 apply (case_tac "\<forall>n. f n < oLimit f")
  apply (simp add: ordinal_rec0_limit_ordinal limit_ordinal_oLimitI)
  apply (rule the_equality, clarify)
   apply (rule lub_cong, assumption+)
   apply clarify
   apply (erule ordinal_rec0_mono[OF s])
  apply (drule_tac x=f in spec, simp)
 apply (simp add: linorder_not_less, clarify)
 apply (rule po_antisym)
  apply (erule po_trans[OF ordinal_rec0_mono[OF s]])
  apply (rule is_ub_lub)
 apply (rule is_lub_lub[rule_format])
 apply (rule ordinal_rec0_mono[OF s le_oLimit])
done


subsection \<open>Recursive definitions for @{typ "ordinal => ordinal"}\<close>

definition
  ordinal_rec ::
    "[ordinal, ordinal \<Rightarrow> ordinal \<Rightarrow> ordinal, ordinal] \<Rightarrow> ordinal" where
  "ordinal_rec z s = ordinal_rec0 z s oLimit"

lemma omega_complete_oLimit: "omega_complete (\<le>) oLimit"
 apply (rule omega_complete.intro)
  apply (rule porder_order)
 apply (rule omega_complete_axioms.intro)
  apply (rule le_oLimit)
 apply (erule oLimit_leI)
done

lemma ordinal_rec_0 [simp]: "ordinal_rec z s 0 = z"
by (unfold ordinal_rec_def, rule ordinal_rec0_0)

lemma ordinal_rec_oSuc [simp]:
"ordinal_rec z s (oSuc x) = s x (ordinal_rec z s x)"
by (unfold ordinal_rec_def, rule ordinal_rec0_oSuc)

lemma ordinal_rec_oLimit:
assumes s: "\<forall>p x. x \<le> s p x"
shows "ordinal_rec z s (oLimit f) = oLimit (\<lambda>n. ordinal_rec z s (f n))"
 apply (unfold ordinal_rec_def)
 apply (rule omega_complete.ordinal_rec0_oLimit)
  apply (rule omega_complete_oLimit)
 apply (rule s)
done

lemma continuous_ordinal_rec:
assumes s: "\<forall>p x. x \<le> s p x"
shows "continuous (ordinal_rec z s)"
 apply (rule continuousI)
  apply (rule ordinal_rec_oLimit[OF s])
 apply (simp add: s)
done

lemma mono_ordinal_rec:
assumes s: "\<forall>p x. x \<le> s p x"
shows "mono (ordinal_rec z s)"
 apply (rule continuous.mono)
 apply (rule continuous_ordinal_rec[OF s])
done

lemma normal_ordinal_rec:
assumes s: "\<forall>p x. x < s p x"
shows "normal (ordinal_rec z s)"
 apply (rule normalI)
  apply (rule ordinal_rec_oLimit)
  apply (simp add: s order_less_imp_le)
 apply (simp add: s)
done

end
