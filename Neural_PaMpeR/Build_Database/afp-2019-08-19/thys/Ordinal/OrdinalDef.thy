(*  Title:       Countable Ordinals

    Author:      Brian Huffman, 2005
    Maintainer:  Brian Huffman <brianh at cse.ogi.edu>
*)

section \<open>Definition of Ordinals\<close>

theory OrdinalDef
imports Main
begin

subsection \<open>Preliminary datatype for ordinals\<close>

datatype ord0 = ord0_Zero | ord0_Lim "nat \<Rightarrow> ord0"

text \<open>subterm ordering on ord0\<close>

definition
  ord0_prec :: "(ord0 \<times> ord0) set" where
  "ord0_prec = (\<Union>f i. {(f i, ord0_Lim f)})"

lemma wf_ord0_prec: "wf ord0_prec"
 apply (unfold ord0_prec_def)
 apply (rule wfUNIVI, induct_tac x)
  apply (drule spec, erule mp, simp)
 apply (drule spec, erule mp, auto)
done

lemmas ord0_prec_induct = wf_induct[OF wf_trancl[OF wf_ord0_prec]]


text \<open>less-than-or-equal ordering on ord0\<close>

inductive_set ord0_leq :: "(ord0 \<times> ord0) set" where
"\<lbrakk>\<forall>a. (a,x) \<in> ord0_prec\<^sup>+ \<longrightarrow> (\<exists>b. (b,y) \<in> ord0_prec\<^sup>+ \<and> (a,b) \<in> ord0_leq)\<rbrakk>
  \<Longrightarrow> (x,y) \<in> ord0_leq"

lemma ord0_leqI:
"\<lbrakk>\<forall>a. (a,x) \<in> ord0_prec\<^sup>+ \<longrightarrow> (a,y) \<in> ord0_leq O ord0_prec\<^sup>+\<rbrakk>
 \<Longrightarrow> (x,y) \<in> ord0_leq"
by (rule ord0_leq.intros, auto)

lemma ord0_leqD:
"\<lbrakk>(x,y) \<in> ord0_leq; (a,x) \<in> ord0_prec\<^sup>+\<rbrakk> \<Longrightarrow> (a,y) \<in> ord0_leq O ord0_prec\<^sup>+"
by (ind_cases "(x,y) \<in> ord0_leq", auto)

lemma ord0_leq_refl: "(x, x) \<in> ord0_leq"
by (rule ord0_prec_induct, rule ord0_leqI, auto)

lemma ord0_leq_trans[rule_format]:
"\<forall>y. (x,y) \<in> ord0_leq \<longrightarrow>
   (\<forall>z. (y,z) \<in> ord0_leq \<longrightarrow> (x,z) \<in> ord0_leq)"
 apply (rule ord0_prec_induct, clarify)
 apply (rule ord0_leqI, clarify)
 apply (drule spec, drule mp, assumption)
 apply (drule ord0_leqD, assumption, clarify)
 apply (drule spec, drule mp, assumption)
 apply (drule ord0_leqD, assumption, clarify)
 apply (drule spec, drule mp, assumption)
 apply auto
done

lemma wf_ord0_leq: "wf (ord0_leq O ord0_prec\<^sup>+)"
 apply (unfold wf_def, clarify)
 apply (subgoal_tac "\<forall>z. (z,x) \<in> ord0_leq \<longrightarrow> P z")
  apply (drule spec, erule mp, rule ord0_leq_refl)
 apply (rule ord0_prec_induct, clarify)
 apply (drule spec, erule mp, clarify)
 apply (drule ord0_leqD, assumption, clarify)
 apply (drule spec, drule mp, assumption)
 apply (drule spec, erule mp)
 apply (erule ord0_leq_trans, assumption)
done


text \<open>ordering on ord0\<close>

instantiation ord0 :: ord
begin

definition
  ord0_less_def: "x < y \<longleftrightarrow> (x,y) \<in> ord0_leq O ord0_prec\<^sup>+"

definition
  ord0_le_def:   "x \<le> y \<longleftrightarrow> (x,y) \<in> ord0_leq"

instance ..

end

lemma ord0_order_refl[simp]: "(x::ord0) \<le> x"
by (unfold ord0_le_def, rule ord0_leq_refl)

lemma ord0_order_trans: "\<lbrakk>(x::ord0) \<le> y; y \<le> z\<rbrakk> \<Longrightarrow> x \<le> z"
by (unfold ord0_le_def, rule ord0_leq_trans)

lemma ord0_wf: "wf {(x,y::ord0). x < y}"
 apply (subgoal_tac "{(x,y). x < y} = ord0_leq O ord0_prec\<^sup>+")
  apply (simp add: wf_ord0_leq)
 apply (auto simp add: ord0_less_def)
done

lemmas ord0_less_induct = wf_induct[OF ord0_wf]

lemma ord0_leI:
"\<lbrakk>\<forall>a::ord0. a < x \<longrightarrow> a < y\<rbrakk> \<Longrightarrow> x \<le> y"
 apply (unfold ord0_less_def ord0_le_def)
 apply (rule ord0_leqI[rule_format])
 apply (drule spec, erule mp)
 apply (erule relcompI[OF ord0_leq_refl])
done

lemma ord0_less_le_trans:
"\<lbrakk>(x::ord0) < y; y \<le> z\<rbrakk> \<Longrightarrow> x < z"
 apply (unfold ord0_le_def ord0_less_def, clarify)
 apply (drule ord0_leqD, assumption, clarify)
by (rule relcompI[OF ord0_leq_trans])

lemma ord0_le_less_trans:
"\<lbrakk>(x::ord0) \<le> y; y < z\<rbrakk> \<Longrightarrow> x < z"
 apply (unfold ord0_le_def ord0_less_def, clarify)
by (rule relcompI[OF ord0_leq_trans])

lemma rev_ord0_le_less_trans:
"\<lbrakk>(y::ord0) < z; x \<le> y\<rbrakk> \<Longrightarrow> x < z"
by (rule ord0_le_less_trans)

lemma ord0_less_trans:
"\<lbrakk>(x::ord0) < y; y < z\<rbrakk> \<Longrightarrow> x < z"
 apply (unfold ord0_less_def, clarify)
 apply (drule ord0_leqD, assumption, clarify)
by (rule relcompI[OF ord0_leq_trans trancl_trans])

lemma ord0_less_imp_le: "(x::ord0) < y \<Longrightarrow> x \<le> y"
by (rule ord0_leI[rule_format], rule ord0_less_trans)

lemma ord0_linear_lemma:
fixes m :: ord0 and n :: ord0
shows "m < n \<or> n < m \<or> (m \<le> n \<and> n \<le> m)"
 apply (rule_tac x=m in spec)
 apply (rule_tac a=n in ord0_less_induct, rename_tac n)
 apply (rule allI, rename_tac m)
 apply (rule_tac a=m in ord0_less_induct, rename_tac m)
 apply (case_tac "\<forall>a. a < n \<longrightarrow> a < m")
  apply (rule disjI2)
  apply (case_tac "\<forall>a. a < m \<longrightarrow> a < n")
   apply (rule disjI2)
   apply (rule conjI, erule ord0_leI, erule ord0_leI)
  apply (rule disjI1, clarsimp)
  apply (drule spec, drule mp, assumption)
  apply (erule rev_ord0_le_less_trans)
  apply (force simp add: ord0_less_imp_le)
 apply (rule disjI1, clarsimp)
 apply (drule spec, drule mp, assumption)
 apply (drule_tac x=m in spec, simp)
 apply (erule rev_ord0_le_less_trans)
 apply (force simp add: ord0_less_imp_le)
done

lemma ord0_linear: "(x::ord0) \<le> y \<or> y \<le> x"
 apply (cut_tac ord0_linear_lemma[of x y])
 apply (auto dest: ord0_less_imp_le)
done

lemma ord0_order_less_le: "(x::ord0) < y = (x \<le> y \<and> \<not> y \<le> x)"
 apply (rule iffI)
  apply (clarsimp simp add: ord0_less_imp_le)
  apply (drule ord0_less_le_trans, assumption)
  apply (cut_tac a=x in wf_not_refl[OF ord0_wf], simp)
 apply (cut_tac ord0_linear_lemma[of x y], simp)
 apply (auto dest: ord0_less_imp_le)
done


subsection \<open>Ordinal type\<close>

definition
  ord0rel :: "(ord0 \<times> ord0) set" where
  "ord0rel = {(x,y). x \<le> y \<and> y \<le> x}"

typedef ordinal = "(UNIV::ord0 set) // ord0rel"
by (unfold quotient_def, auto)

theorem Abs_ordinal_cases2 [case_names Abs_ordinal, cases type: ordinal]:
"(\<And>z. x = Abs_ordinal (ord0rel `` {z}) \<Longrightarrow> P) \<Longrightarrow> P"
by (cases x, auto simp add: quotient_def)


instantiation ordinal :: ord
begin

definition
  ordinal_less_def: "x < y \<longleftrightarrow> (\<forall>a\<in>Rep_ordinal x. \<forall>b\<in>Rep_ordinal y. a < b)"

definition
  ordinal_le_def: "x \<le> y \<longleftrightarrow> (\<forall>a\<in>Rep_ordinal x. \<forall>b\<in>Rep_ordinal y. a \<le> b)"

instance ..

end

lemma Rep_Abs_ord0rel [simp]:
"Rep_ordinal (Abs_ordinal (ord0rel `` {x})) = (ord0rel `` {x})"
by (simp add: Abs_ordinal_inverse quotientI)

lemma mem_ord0rel_Image [simp, intro!]: "x \<in> ord0rel `` {x}"
by (simp add: ord0rel_def)

lemma equiv_ord0rel: "equiv UNIV ord0rel"
 apply (unfold equiv_def refl_on_def sym_def trans_def ord0rel_def)
 apply (auto elim: ord0_order_trans)
done

lemma Abs_ordinal_eq[simp]:
"(Abs_ordinal (ord0rel `` {x}) = Abs_ordinal (ord0rel `` {y}))
  = (x \<le> y \<and> y \<le> x)"
 apply (simp add: Abs_ordinal_inject quotientI)
 apply (simp add: eq_equiv_class_iff[OF equiv_ord0rel])
 apply (simp add: ord0rel_def)
done

lemma Abs_ordinal_le[simp]:
"Abs_ordinal (ord0rel `` {x}) \<le> Abs_ordinal (ord0rel `` {y}) = (x \<le> y)"
 apply (auto simp add: ordinal_le_def)
 apply (unfold ord0rel_def)
 apply (auto elim: ord0_order_trans)
done

lemma Abs_ordinal_less[simp]:
"Abs_ordinal (ord0rel `` {x}) < Abs_ordinal (ord0rel `` {y}) = (x < y)"
 apply (auto simp add: ordinal_less_def)
 apply (unfold ord0rel_def)
 apply (auto elim: ord0_less_le_trans[OF rev_ord0_le_less_trans])
done

lemma ordinal_order_refl: "(x::ordinal) \<le> x"
by (cases x, simp)

lemma ordinal_order_trans: "(x::ordinal) \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
by (cases x, cases y, cases z, auto elim: ord0_order_trans)

lemma ordinal_order_antisym: "(x::ordinal) \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
by (cases x, cases y, simp)

lemma ordinal_order_less_le_not_le: "((x::ordinal) < y) = (x \<le> y \<and> \<not> y \<le> x)"
by (cases x, cases y, auto simp add: ord0_order_less_le)

lemma ordinal_linear: "(x::ordinal) \<le> y \<or> y \<le> x"
by (cases x, cases y, simp add: ord0_linear)

lemma ordinal_wf: "wf {(x,y::ordinal). x < y}"
 apply (rule wfUNIVI)
 apply (rule_tac x=x in Abs_ordinal_cases2, clarify)
 apply (rule ord0_less_induct, rename_tac a)
 apply (drule spec, erule mp, clarify)
 apply (rule_tac x=y in Abs_ordinal_cases2, simp)
done

instance ordinal :: wellorder
 apply (rule wf_wellorderI)
 apply (rule ordinal_wf)
 apply (intro_classes)
       apply (rule ordinal_order_less_le_not_le)
      apply (rule ordinal_order_refl)
     apply (rule ordinal_order_trans, assumption+)
    apply (rule ordinal_order_antisym, assumption+)
  apply (rule ordinal_linear)
done


subsection \<open>Induction over ordinals\<close>

text "zero and strict limits"

definition
  oZero :: "ordinal" where
    "oZero = Abs_ordinal (ord0rel `` {ord0_Zero})"

definition
  oStrictLimit :: "(nat \<Rightarrow> ordinal) \<Rightarrow> ordinal" where
    "oStrictLimit f = Abs_ordinal
      (ord0rel `` {ord0_Lim (\<lambda>n. SOME x. x \<in> Rep_ordinal (f n))})"

text "induction over ordinals"

lemma ord0relD: "(x,y) \<in> ord0rel \<Longrightarrow> x \<le> y \<and> y \<le> x"
by (simp add: ord0rel_def)

lemma ord0_precD: "(x,y) \<in> ord0_prec \<Longrightarrow> \<exists>f n. x = f n \<and> y = ord0_Lim f"
by (simp add: ord0_prec_def)

lemma less_ord0_LimI: "f n < ord0_Lim f"
 apply (simp add: ord0_less_def)
 apply (rule relcompI[OF ord0_leq_refl])
 apply (rule r_into_trancl)
 apply (auto simp add: ord0_prec_def)
done

lemma less_ord0_LimD: "x < ord0_Lim f \<Longrightarrow> \<exists>n. x \<le> f n"
 apply (simp add: ord0_less_def, clarify)
 apply (erule tranclE)
  apply (drule ord0_precD, clarify)
  apply (force simp add: ord0_le_def)
 apply (drule ord0_precD, clarify)
 apply (rule_tac x=n in exI)
 apply (rule ord0_less_imp_le)
 apply (auto simp add: ord0_less_def)
done

lemma some_ord0rel: "(x, SOME y. (x,y) \<in> ord0rel) \<in> ord0rel"
by (rule_tac x=x in someI, simp add: ord0rel_def)

lemma ord0_Lim_le:
"\<forall>n. f n \<le> g n \<Longrightarrow> ord0_Lim f \<le> ord0_Lim g"
 apply (rule ord0_leI[rule_format])
 apply (drule less_ord0_LimD, clarify)
 apply (erule ord0_le_less_trans)
 apply (drule_tac x=n in spec)
 apply (erule ord0_le_less_trans)
 apply (rule less_ord0_LimI)
done

lemma ord0_Lim_ord0rel:
"\<forall>n. (f n, g n) \<in> ord0rel \<Longrightarrow> (ord0_Lim f, ord0_Lim g) \<in> ord0rel"
by (simp add: ord0rel_def ord0_Lim_le)

lemma Abs_ordinal_oStrictLimit:
"Abs_ordinal (ord0rel `` {ord0_Lim f})
  = oStrictLimit (\<lambda>n. Abs_ordinal (ord0rel `` {f n}))"
 apply (simp add: oStrictLimit_def)
 apply (rule ord0relD)
 apply (rule ord0_Lim_ord0rel)
 apply (simp add: some_ord0rel)
done

lemma oStrictLimit_induct:
assumes base: "P oZero"
assumes step: "\<And>f. \<forall>n. P (f n) \<Longrightarrow> P (oStrictLimit f)"
shows "P a"
 apply (cases a, clarsimp)
 apply (induct_tac z)
  apply (rule base[unfolded oZero_def])
 apply (simp add: Abs_ordinal_oStrictLimit step)
done

text "order properties of 0 and strict limits"

lemma oZero_least: "oZero \<le> x"
 apply (unfold oZero_def, cases x, clarsimp)
 apply (induct_tac z, simp, atomize)
 apply (rule ord0_less_imp_le)
 apply (rule ord0_le_less_trans)
 apply (auto simp: less_ord0_LimI)
done

lemma oStrictLimit_ub: "f n < oStrictLimit f"
 apply (cases "f n", simp add: oStrictLimit_def)
 apply (rule_tac y="SOME x. x \<in> Rep_ordinal (f n)" in ord0_le_less_trans)
  apply (simp, rule ord0relD[THEN conjunct1])
  apply (rule some_ord0rel)
 apply (rule less_ord0_LimI)
done

lemma oStrictLimit_lub: "\<forall>n. f n < x \<Longrightarrow> oStrictLimit f \<le> x"
 apply (erule contrapos_pp, simp add: linorder_not_less linorder_not_le)
 apply (cases x, simp add: oStrictLimit_def)
 apply (drule less_ord0_LimD, clarify)
 apply (rule_tac x=n in exI)
 apply (rule_tac x="f n" in Abs_ordinal_cases2, simp, rename_tac y)
 apply (erule ord0_order_trans)
 apply (rule ord0relD[THEN conjunct2])
 apply (rule some_ord0rel)
done

lemma less_oStrictLimitD: "x < oStrictLimit f \<Longrightarrow> \<exists>n. x \<le> f n"
 apply (erule contrapos_pp)
 apply (simp add: linorder_not_less linorder_not_le)
 apply (erule oStrictLimit_lub)
done

end
