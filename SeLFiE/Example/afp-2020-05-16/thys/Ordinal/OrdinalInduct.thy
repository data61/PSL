(*  Title:       Countable Ordinals

    Author:      Brian Huffman, 2005
    Maintainer:  Brian Huffman <brianh at cse.ogi.edu>
*)

section \<open>Ordinal Induction\<close>

theory OrdinalInduct
imports OrdinalDef
begin

subsection \<open>Zero and successor ordinals\<close>

definition
  oSuc :: "ordinal \<Rightarrow> ordinal" where
    "oSuc x = oStrictLimit (\<lambda>n. x)"

lemma less_oSuc[iff]: "x < oSuc x"
by (unfold oSuc_def, rule oStrictLimit_ub)

lemma oSuc_leI: "x < y \<Longrightarrow> oSuc x \<le> y"
by (unfold oSuc_def, rule oStrictLimit_lub, simp)

instantiation ordinal :: "{zero, one}"
begin

definition
  ordinal_zero_def:       "(0::ordinal) = oZero"

definition
  ordinal_one_def [simp]: "(1::ordinal) = oSuc 0"

instance ..

end


subsubsection \<open>Derived properties of 0 and oSuc\<close>

lemma less_oSuc_eq_le: "(x < oSuc y) = (x \<le> y)"
 apply (rule iffI)
  apply (erule contrapos_pp, simp add: linorder_not_less linorder_not_le)
  apply (erule oSuc_leI)
 apply (erule order_le_less_trans[OF _ less_oSuc])
done

lemma ordinal_0_le [iff]: "0 \<le> (x::ordinal)"
by (unfold ordinal_zero_def, rule oZero_least)

lemma ordinal_not_less_0 [iff]: "\<not> (x::ordinal) < 0"
by (simp add: linorder_not_less)

lemma ordinal_le_0 [iff]: "(x \<le> 0) = (x = (0::ordinal))"
by (simp add: order_le_less)

lemma ordinal_neq_0 [iff]: "(x \<noteq> 0) = (0 < (x::ordinal))"
by (simp add: order_less_le)

lemma ordinal_not_0_less [iff]: "(\<not> 0 < x) = (x = (0::ordinal))"
by (simp add: linorder_not_less)

lemma oSuc_le_eq_less: "(oSuc x \<le> y) = (x < y)"
 apply (rule iffI)
  apply (erule order_less_le_trans[OF less_oSuc])
 apply (erule oSuc_leI)
done

lemma zero_less_oSuc [iff]: "0 < oSuc x"
by (rule order_le_less_trans, rule ordinal_0_le, rule less_oSuc)

lemma oSuc_not_0 [iff]: "oSuc x \<noteq> 0"
by simp

lemma less_oSuc0 [iff]: "(x < oSuc 0) = (x = 0)"
by (simp add: less_oSuc_eq_le)

lemma oSuc_less_oSuc [iff]: "(oSuc x < oSuc y) = (x < y)"
 apply (rule iffI)
  apply (simp add: less_oSuc_eq_le order_less_le_trans[OF less_oSuc])
 apply (erule order_le_less_trans[OF oSuc_leI less_oSuc])
done

lemma oSuc_eq_oSuc [iff]: "(oSuc x = oSuc y) = (x = y)"
by (safe, erule contrapos_pp, simp add: linorder_neq_iff)

lemma oSuc_le_oSuc [iff]: "(oSuc x \<le> oSuc y) = (x \<le> y)"
by (simp add: order_le_less)

lemma le_oSucE: 
"\<lbrakk>x \<le> oSuc y; x \<le> y \<Longrightarrow> R; x = oSuc y \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R"
by (auto simp add: order_le_less less_oSuc_eq_le)

lemma less_oSucE:
"\<lbrakk>x < oSuc y; x < y \<Longrightarrow> P; x = y \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
by (auto simp add: less_oSuc_eq_le order_le_less)


subsection \<open>Strict monotonicity\<close>

locale strict_mono =
  fixes f
  assumes strict_mono: "A < B \<Longrightarrow> f A < f B"

lemmas strict_monoI = strict_mono.intro
   and strict_monoD = strict_mono.strict_mono

lemma strict_mono_natI:
fixes f :: "nat \<Rightarrow> 'a::order"
shows "(\<And>n. f n < f (Suc n)) \<Longrightarrow> strict_mono f"
 apply (rule strict_monoI)
 apply (drule Suc_leI)
 apply (drule le_add_diff_inverse)
 apply (subgoal_tac "\<forall>k. f A < f (Suc A + k)")
  apply (erule subst, erule spec)
 apply (rule allI, induct_tac k, simp)
 apply (erule order_less_trans, simp)
done

lemma mono_natI:
fixes f :: "nat \<Rightarrow> 'a::order"
shows "(\<And>n. f n \<le> f (Suc n)) \<Longrightarrow> mono f"
 apply (rule monoI)
 apply (drule le_add_diff_inverse)
 apply (subgoal_tac "\<forall>k. f x \<le> f (x + k)")
  apply (erule subst, erule spec)
 apply (rule allI, induct_tac k, simp)
 apply (erule order_trans, simp)
done

lemma strict_mono_mono:
fixes f :: "'a::order \<Rightarrow> 'b::order"
shows "strict_mono f \<Longrightarrow> mono f"
by (auto intro!: monoI simp add: order_le_less strict_monoD)

lemma strict_mono_monoD:
fixes f :: "'a::order \<Rightarrow> 'b::order"
shows "\<lbrakk>strict_mono f; A \<le> B\<rbrakk> \<Longrightarrow> f A \<le> f B"
by (rule monoD[OF strict_mono_mono])

lemma strict_mono_cancel_eq:
fixes f :: "'a::linorder \<Rightarrow> 'b::linorder"
shows "strict_mono f \<Longrightarrow> (f x = f y) = (x = y)"
 apply safe
 apply (rule_tac x=x and y=y in linorder_cases)
   apply (drule strict_monoD, assumption, simp)
  apply assumption
 apply (drule strict_monoD, assumption, simp)
done

lemma strict_mono_cancel_less: 
fixes f :: "'a::linorder \<Rightarrow> 'b::linorder"
shows "strict_mono f \<Longrightarrow> (f x < f y) = (x < y)"
 apply safe
  apply (rule_tac x=x and y=y in linorder_cases)
    apply assumption
   apply simp
  apply (drule strict_monoD, assumption, simp)
 apply (simp add: strict_monoD)
done

lemma strict_mono_cancel_le:
fixes f :: "'a::linorder \<Rightarrow> 'b::linorder"
shows "strict_mono f \<Longrightarrow> (f x \<le> f y) = (x \<le> y)"
 apply (auto simp add: order_le_less)
   apply (simp add: strict_mono_cancel_less)
  apply (simp add: strict_mono_cancel_eq)
 apply (simp add: strict_monoD)
done


subsection \<open>Limit ordinals\<close>

definition
  oLimit :: "(nat \<Rightarrow> ordinal) \<Rightarrow> ordinal" where
  "oLimit f = (LEAST k. \<forall>n. f n \<le> k)"

lemma oLimit_leI: "\<forall>n. f n \<le> x \<Longrightarrow> oLimit f \<le> x"
 apply (unfold oLimit_def)
 apply (erule Least_le)
done

lemma le_oLimit [iff]: "f n \<le> oLimit f"
 apply (unfold oLimit_def)
 apply (rule_tac x=n in spec)
 apply (rule_tac k="oStrictLimit f" in LeastI)
 apply (clarify, rule order_less_imp_le)
 apply (rule oStrictLimit_ub)
done

lemma le_oLimitI: "x \<le> f n \<Longrightarrow> x \<le> oLimit f"
by (erule order_trans, rule le_oLimit)

lemma less_oLimitI: "x < f n \<Longrightarrow> x < oLimit f"
by (erule order_less_le_trans, rule le_oLimit)

lemma less_oLimitD: "x < oLimit f \<Longrightarrow> \<exists>n. x < f n"
 apply (unfold oLimit_def)
 apply (drule not_less_Least)
 apply (simp add: linorder_not_le)
done

lemma less_oLimitE:
"\<lbrakk>x < oLimit f; \<And>n. x < f n \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
by (auto dest: less_oLimitD)

lemma le_oLimitE:
"\<lbrakk>x \<le> oLimit f; \<And>n. x \<le> f n \<Longrightarrow> R; x = oLimit f \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R"
by (auto simp add: order_le_less dest: less_oLimitD)

lemma oLimit_const [simp]: "oLimit (\<lambda>n. x) = x"
 apply (rule order_antisym[OF _ le_oLimit])
 apply (rule oLimit_leI, simp)
done

lemma strict_mono_less_oLimit:
"strict_mono f \<Longrightarrow> f n < oLimit f"
 apply (rule order_less_le_trans)
  apply (erule strict_monoD, rule lessI)
 apply (rule le_oLimit)
done

lemma oLimit_eqI:
"\<lbrakk>\<And>n. \<exists>m. f n \<le> g m; \<And>n. \<exists>m. g n \<le> f m\<rbrakk> \<Longrightarrow> oLimit f = oLimit g"
 apply atomize
 apply (rule order_antisym)
  apply (rule oLimit_leI, clarify)
  apply (drule spec, erule exE, erule le_oLimitI)
 apply (rule oLimit_leI, clarify)
 apply (drule spec, erule exE, erule le_oLimitI)
done

lemma oLimit_Suc:
"f 0 < oLimit f \<Longrightarrow> oLimit (\<lambda>n. f (Suc n)) = oLimit f"
 apply (rule oLimit_eqI)
  apply (rule exI, rule order_refl)
 apply (case_tac n)
  apply (drule less_oLimitD, clarify, rename_tac m)
  apply (case_tac m, simp)
  apply (rule_tac x=nat in exI)
  apply (simp add: order_less_imp_le)
 apply (rule_tac x=nat in exI, simp)
done

lemma oLimit_shift:
"\<forall>n. f n < oLimit f \<Longrightarrow> oLimit (\<lambda>n. f (n + k)) = oLimit f"
 apply (induct_tac k, simp, rename_tac k)
 apply (simp only: add_Suc_right add_Suc[symmetric])
 apply (rule trans[OF oLimit_Suc], simp_all)
done

lemma oLimit_shift_mono:
"mono f \<Longrightarrow> oLimit (\<lambda>n. f (n + k)) = oLimit f"
 apply (rule oLimit_eqI)
  apply (rule exI, rule order_refl)
 apply (rule_tac x=n in exI)
 apply (erule monoD, simp)
done


text "limit ordinal predicate"

definition
  limit_ordinal :: "ordinal \<Rightarrow> bool" where
  "limit_ordinal x \<longleftrightarrow> (x \<noteq> 0) \<and> (\<forall>y. x \<noteq> oSuc y)"

lemma limit_ordinal_not_0 [simp]: "\<not> limit_ordinal 0"
by (simp add: limit_ordinal_def)

lemma zero_less_limit_ordinal [simp]: "limit_ordinal x \<Longrightarrow> 0 < x"
by (simp add: limit_ordinal_def)

lemma limit_ordinal_not_oSuc [simp]: "\<not> limit_ordinal (oSuc p)"
by (simp add: limit_ordinal_def)

lemma oSuc_less_limit_ordinal:
"limit_ordinal x \<Longrightarrow> (oSuc w < x) = (w < x)"
 apply (rule iffI)
  apply (erule order_less_trans[OF less_oSuc])
 apply (simp add: linorder_not_le[symmetric])
 apply (erule contrapos_nn)
 apply (auto simp add: order_le_less less_oSuc_eq_le)
done

lemma limit_ordinal_oLimitI:
"\<forall>n. f n < oLimit f \<Longrightarrow> limit_ordinal (oLimit f)"
 apply (unfold limit_ordinal_def, simp)
 apply (rule conjI)
  apply (rule order_le_less_trans[OF ordinal_0_le])
  apply (erule spec)
 apply (clarsimp simp add: less_oSuc_eq_le)
 apply (drule oLimit_leI)
 apply (simp add: linorder_not_less[symmetric])
done

lemma strict_mono_limit_ordinal:
"strict_mono f \<Longrightarrow> limit_ordinal (oLimit f)"
 apply (rule limit_ordinal_oLimitI)
 apply (simp add: strict_mono_less_oLimit)
done

lemma limit_ordinalI:
"\<lbrakk>0 < z; \<forall>x<z. oSuc x < z\<rbrakk> \<Longrightarrow> limit_ordinal z"
 apply (erule contrapos_pp)
 apply (unfold limit_ordinal_def, clarsimp)
 apply (drule_tac x=y in spec, clarsimp)
done


subsubsection \<open>Making strict monotonic sequences\<close>

primrec make_mono :: "(nat \<Rightarrow> ordinal) \<Rightarrow> nat \<Rightarrow> nat"
where
  "make_mono f 0       = 0"
| "make_mono f (Suc n) = (LEAST x. f (make_mono f n) < f x)"

lemma f_make_mono_less:
"\<forall>n. f n < oLimit f \<Longrightarrow> f (make_mono f n) < f (make_mono f (Suc n))"
 apply (drule_tac x="make_mono f n" in spec)
 apply (drule less_oLimitD, clarsimp)
 apply (erule LeastI)
done

lemma strict_mono_f_make_mono:
"\<forall>n. f n < oLimit f \<Longrightarrow> strict_mono (\<lambda>n. f (make_mono f n))"
by (rule strict_mono_natI, erule f_make_mono_less)

lemma le_f_make_mono:
"\<lbrakk>\<forall>n. f n < oLimit f; m \<le> make_mono f n\<rbrakk> \<Longrightarrow> f m \<le> f (make_mono f n)"
 apply (auto simp add: order_le_less)
 apply (case_tac n, simp_all)
 apply (drule not_less_Least)
 apply (simp add: linorder_not_less)
 apply (erule order_le_less_trans)
 apply (rule LeastI)
 apply (erule f_make_mono_less)
done

lemma make_mono_less:
"\<forall>n. f n < oLimit f \<Longrightarrow> make_mono f n < make_mono f (Suc n)"
 apply (frule_tac n=n in f_make_mono_less)
 apply (rule ccontr, simp only: linorder_not_less)
 apply (drule le_f_make_mono, assumption)
 apply (simp add: linorder_not_less[symmetric])
done

declare make_mono.simps [simp del]

lemma oLimit_make_mono_eq:
"\<forall>n. f n < oLimit f \<Longrightarrow> oLimit (\<lambda>n. f (make_mono f n)) = oLimit f"
 apply (rule oLimit_eqI, force)
 apply (rule_tac x=n in exI)
 apply (rule le_f_make_mono, assumption)
 apply (induct_tac n, simp)
 apply (rule Suc_leI)
 apply (erule order_le_less_trans)
 apply (erule make_mono_less)
done


subsection \<open>Induction principle for ordinals\<close>

lemma oLimit_le_oStrictLimit: "oLimit f \<le> oStrictLimit f"
 apply (rule oLimit_leI, clarify)
 apply (rule order_less_imp_le)
 apply (rule oStrictLimit_ub)
done

lemma oLimit_induct:
assumes zero: "P 0"
    and suc:  "\<And>x. P x \<Longrightarrow> P (oSuc x)"
    and lim:  "\<And>f. \<lbrakk>strict_mono f; \<forall>n. P (f n)\<rbrakk> \<Longrightarrow> P (oLimit f)"
shows "P a"
 apply (rule oStrictLimit_induct)
  apply (rule zero[unfolded ordinal_zero_def])
 apply (cut_tac f=f in oLimit_le_oStrictLimit)
 apply (simp add: order_le_less, erule disjE)
  apply (drule less_oStrictLimitD, clarify)
  apply (subgoal_tac "oStrictLimit f = oSuc (f n)", simp add: suc)
  apply (rule order_antisym)
   apply (rule oStrictLimit_lub, clarify)
   apply (simp add: less_oSuc_eq_le)
   apply (erule order_trans[OF le_oLimit])
  apply (rule oSuc_leI, rule oStrictLimit_ub)
 apply (subgoal_tac "\<forall>n. f n < oLimit f")
  apply (subgoal_tac "P (oLimit (\<lambda>n. f (make_mono f n)))")
   apply (simp add: oLimit_make_mono_eq)
  apply (rule lim)
   apply (erule strict_mono_f_make_mono)
  apply simp
 apply (simp add: oStrictLimit_ub)
done

lemma ordinal_cases:
assumes zero: "a = 0 \<Longrightarrow> P"
    and suc:  "\<And>x. a = oSuc x \<Longrightarrow> P"
    and lim:  "\<And>f. \<lbrakk>strict_mono f; a = oLimit f\<rbrakk> \<Longrightarrow> P"
shows "P"
 apply (subgoal_tac "\<forall>x. a = x \<longrightarrow> P", force)
 apply (rule allI)
 apply (rule_tac a=x in oLimit_induct)
   apply (rule impI, erule zero)
  apply (rule impI, erule suc)
 apply (rule impI, erule lim, assumption)
done

end
