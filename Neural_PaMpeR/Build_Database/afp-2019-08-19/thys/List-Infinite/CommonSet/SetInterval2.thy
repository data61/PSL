(*  Title:      SetInterval2.thy
    Date:       Oct 2006
    Author:     David Trachtenherz
*)

section \<open>Sets of natural numbers\<close>

theory SetInterval2
imports
  "HOL-Library.Infinite_Set"
  Util_Set
  "../CommonArith/Util_MinMax"
  "../CommonArith/Util_NatInf"
  "../CommonArith/Util_Div"
begin

subsection \<open>Auxiliary results for monotonic, injective and surjective functions over sets\<close>

subsubsection \<open>Monotonicity\<close>

definition mono_on :: "('a::order \<Rightarrow> 'b::order) \<Rightarrow> 'a set \<Rightarrow> bool"
  where "mono_on f A \<equiv> \<forall>a\<in>A. \<forall>b\<in>A. a \<le> b \<longrightarrow> f a \<le> f b"

definition strict_mono_on :: "('a::order \<Rightarrow> 'b::order) \<Rightarrow> 'a set \<Rightarrow> bool"
  where "strict_mono_on f A \<equiv> \<forall>a\<in>A. \<forall>b\<in>A. a < b \<longrightarrow> f a < f b"


lemma mono_on_subset: "\<lbrakk> mono_on f A ; B \<subseteq> A \<rbrakk> \<Longrightarrow> mono_on f B"
unfolding mono_on_def by blast

lemma strict_mono_on_subset: "\<lbrakk> strict_mono_on f A ; B \<subseteq> A \<rbrakk> \<Longrightarrow> strict_mono_on f B"
unfolding strict_mono_on_def by blast


lemma mono_on_UNIV_mono_conv: "mono_on f UNIV = mono f"
unfolding mono_on_def mono_def by blast
lemma strict_mono_on_UNIV_strict_mono_conv: "
  strict_mono_on f UNIV = strict_mono f"
unfolding strict_mono_on_def strict_mono_def by blast

lemma mono_imp_mono_on: "mono f \<Longrightarrow> mono_on f A"
unfolding mono_on_def mono_def by blast
lemma strict_mono_imp_strict_mono_on: "strict_mono f \<Longrightarrow> strict_mono_on f A"
unfolding strict_mono_on_def strict_mono_def by blast

lemma strict_mono_on_imp_mono_on: "strict_mono_on f A \<Longrightarrow> mono_on f A"
apply (unfold strict_mono_on_def mono_on_def)
apply (fastforce simp: order_le_less)
done


subsubsection \<open>Injectivity\<close>

lemma inj_imp_inj_on: "inj f \<Longrightarrow> inj_on f A"
unfolding inj_on_def by blast

lemma strict_mono_on_imp_inj_on: "
  strict_mono_on f (A::'a::linorder set) \<Longrightarrow> inj_on f A"
apply (unfold strict_mono_on_def inj_on_def, clarify)
apply (rule ccontr)
apply (fastforce simp add: linorder_neq_iff)
done



lemma strict_mono_imp_inj: "strict_mono (f::('a::linorder \<Rightarrow> 'b::order)) \<Longrightarrow> inj f"
by (rule strict_mono_imp_inj_on)

lemma strict_mono_on_mono_on_conv: "
  strict_mono_on f (A::'a::linorder set) = (mono_on f A \<and> inj_on f A)"
apply (rule iffI)
 apply (frule strict_mono_on_imp_mono_on)
 apply (frule strict_mono_on_imp_inj_on)
 apply blast
apply (erule conjE)
apply (unfold inj_on_def mono_on_def strict_mono_on_def, clarify)
apply fastforce
done

corollary strict_mono_mono_conv: "
  strict_mono (f::('a::linorder \<Rightarrow> 'b::order)) = (mono f \<and> inj f)"
by (simp only: strict_mono_on_UNIV_strict_mono_conv[symmetric]
  mono_on_UNIV_mono_conv[symmetric] strict_mono_on_mono_on_conv)


lemma inj_on_image_mem_iff: "
  \<lbrakk> inj_on f A; B \<subseteq> A; a \<in> A \<rbrakk> \<Longrightarrow> (f a \<in> f ` B) = (a \<in> B)"
unfolding inj_on_def by blast

corollary inj_on_union_image_Int: "
  inj_on f (A \<union> B) \<Longrightarrow> f ` (A \<inter> B) = f ` A \<inter> f ` B"
by (rule inj_on_image_Int[OF _ Un_upper1 Un_upper2])


subsubsection \<open>Surjectivity\<close>

definition surj_on :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> 'b set \<Rightarrow> bool"
  where "surj_on f A B \<equiv> \<forall>b\<in>B. \<exists>a\<in>A. b = f a"

lemma surj_on_conv: "(surj_on f A B) = (\<forall>b\<in>B. \<exists>a\<in>A. b = f a)"
unfolding surj_on_def ..

lemma surj_on_image_conv: "(surj_on f A B) = (B \<subseteq> f ` A)"
unfolding surj_on_conv by blast

lemma surj_on_id: "surj_on id A A"
unfolding id_def surj_on_conv by blast

lemma
  surj_onI: "\<lbrakk> \<forall>b \<in> B. \<exists>a\<in>A. b = f a \<rbrakk> \<Longrightarrow> surj_on f A B" and
  surj_onD2: "surj_on f A B \<Longrightarrow> \<forall>b \<in> B. \<exists>a\<in>A. b = f a" and
  surj_onD: "\<lbrakk> surj_on f A B; b \<in> B \<rbrakk> \<Longrightarrow> \<exists>a\<in>A. b = f a"
unfolding surj_on_conv
by blast+

lemma comp_surj_on: "
  \<lbrakk> surj_on f A B; surj_on g B C \<rbrakk> \<Longrightarrow> surj_on (g \<circ> f) A C"
unfolding comp_def surj_on_image_conv by blast

lemma surj_on_Un_right: "surj_on f A (B1 \<union> B2) = (surj_on f A B1 \<and> surj_on f A B2)"
unfolding surj_on_image_conv
by blast

lemma surj_on_Un_left: "
  surj_on f (A1 \<union> A2) B =
  (\<exists>B1. \<exists>B2. B \<subseteq> B1 \<union> B2 \<and> surj_on f A1 B1 \<and> surj_on f A2 B2)"
unfolding surj_on_image_conv
apply (rule iffI)
 apply (rule_tac x="f ` A1" in exI)
 apply (rule_tac x="f ` A2" in exI)
 apply blast
apply blast
done

lemma surj_on_diff_right: "surj_on f A B \<Longrightarrow> surj_on f A (B - B')"
unfolding surj_on_conv by blast

lemma surj_on_empty_right: "surj_on f A {}"
unfolding surj_on_conv by blast

lemma surj_on_empty_left: "surj_on f {} B = (B = {})"
unfolding surj_on_conv by blast

lemma surj_on_imageI: "surj_on (g \<circ> f) A B \<Longrightarrow> surj_on g (f ` A) B"
unfolding surj_on_conv by fastforce

lemma surj_on_insert_right: "surj_on f A (insert b B) = (surj_on f A B \<and> surj_on f A {b})"
unfolding surj_on_conv by blast

lemma surj_on_insert_left: "surj_on f (insert a A) B = (surj_on f A (B - {f a}))"
unfolding surj_on_conv by blast

lemma surj_on_subset_right: "\<lbrakk> surj_on f A B; B' \<subseteq> B \<rbrakk> \<Longrightarrow> surj_on f A B'"
unfolding surj_on_conv by blast

lemma surj_on_subset_left: "\<lbrakk> surj_on f A B; A \<subseteq> A' \<rbrakk> \<Longrightarrow> surj_on f A' B"
unfolding surj_on_conv by blast

lemma bij_betw_imp_surj_on: "bij_betw f A B \<Longrightarrow> surj_on f A B"
unfolding bij_betw_def surj_on_image_conv by simp

lemma bij_betw_inj_on_surj_on_conv: "
  bij_betw f A B = (inj_on f A \<and> surj_on f A B \<and> f ` A \<subseteq> B)"
unfolding bij_betw_def surj_on_image_conv by blast


subsubsection \<open>Induction over natural sets\<close>

lemma image_nat_induct: "
  \<lbrakk> P (f 0); \<And>n. P (f n) \<Longrightarrow> P (f (Suc n)); surj_on f UNIV I; a \<in> I \<rbrakk> \<Longrightarrow> P a"
proof -
  assume as_P0: "P (f 0)"
    and  as_IA: "\<And>n. P (f n) \<Longrightarrow> P (f (Suc n))"
    and  as_surj_f: "surj_on f UNIV I"
    and  as_a: "a \<in> I"
  have P_n:"\<And>n. P (f n)"
    apply (induct_tac n)
    apply (simp only: as_P0)
    apply (simp only: as_IA)
    done
  have "\<forall>x\<in>I. \<exists>n. x = f n"
    using as_surj_f
    by (unfold surj_on_conv, blast)
  hence "\<exists>n. a = f n"
    using as_a by blast
  thus "P a"
    using P_n by blast
qed

lemma nat_induct'[rule_format]: "
  \<lbrakk> P n0; \<And>n. \<lbrakk> n0 \<le> n;  P n \<rbrakk> \<Longrightarrow> P (Suc n); n0 \<le> n \<rbrakk> \<Longrightarrow> P n"
by (insert nat_induct[where n="n-n0" and P="\<lambda>n. P (n0+n)"], simp)

lemma enat_induct: "
  \<lbrakk> P 0; P \<infinity>; \<And>n. P n \<Longrightarrow> P (eSuc n)\<rbrakk> \<Longrightarrow> P n"
apply (case_tac n)
 prefer 2
 apply simp
apply (simp only: enat_defs)
apply (rename_tac n1)
apply (induct_tac n1)
apply (simp add: enat.splits)+
done


lemma eSuc_imp_Suc_aux_0:
  "\<lbrakk> \<And>n. P n \<Longrightarrow> P (eSuc n); n0' \<le> n'; P (enat n')\<rbrakk> \<Longrightarrow> P (enat (Suc n'))"
by (simp only: enat_defs enat.splits)

lemma eSuc_imp_Suc_aux_n0:
  "\<lbrakk> \<And>n. \<lbrakk>enat n0' \<le> n; P n\<rbrakk> \<Longrightarrow> P (eSuc n); n0' \<le> n'; P (enat n')\<rbrakk> \<Longrightarrow> P (enat (Suc n'))"
proof -
  assume IA: "\<And>n. \<lbrakk>enat n0' \<le> n; P n\<rbrakk> \<Longrightarrow> P (eSuc n)"
    and n0_n: "n0' \<le> n'"
    and Pn: "P (enat n')"
  from n0_n
  have "(enat n0' \<le> enat n')" by simp
  with Pn IA
  have "P (eSuc (enat n'))" by blast
  thus "P (enat (Suc n'))" by (simp only: eSuc_enat)
qed

lemma enat_induct': "
  \<lbrakk> P (n0::enat); P \<infinity>; \<And>n. \<lbrakk> n0 \<le> n;  P n \<rbrakk> \<Longrightarrow> P (eSuc n); n0 \<le> n \<rbrakk> \<Longrightarrow> P n"
apply (case_tac n)
 prefer 2 apply simp
apply (case_tac n0)
 prefer 2 apply simp
apply (rename_tac n' n0', simp)
apply (rule_tac ?n0.0="n0'" and n=n' and P="\<lambda>n. P (enat n)" in nat_induct')
  apply simp
 apply (simp add: eSuc_enat[symmetric])
apply simp
done

lemma wf_less_interval:"
  wf { (x,y). x \<in> (I::nat set) \<and> y \<in> I \<and> x < y }"
apply (rule wf_subset[where
  p="{ (x,y). x \<in> I \<and> y \<in> I \<and> x < y }" and
  r="{(x,y). x < y}"])
apply (rule wf_less)
apply blast
done

lemma interval_induct: "
  \<lbrakk> \<And>x. \<forall>y. (x\<in>(I::nat set) \<and> y \<in> I \<and> y < x \<longrightarrow> P y) \<Longrightarrow> P x \<rbrakk>
  \<Longrightarrow> P a"
  (is "\<lbrakk> \<And>x. \<forall>y. ?IA x y \<Longrightarrow> P x \<rbrakk> \<Longrightarrow> P a")
apply (rule_tac r="{ (x,y). x \<in> I \<and> y \<in> I \<and> x < y }" in wf_induct)
apply (rule wf_less_interval)
apply simp
done

corollary interval_induct_rule:"
  \<lbrakk> \<And>x. (\<And>y. (x\<in>(I::nat set) \<and> y \<in> I \<and> y < x \<Longrightarrow> P y)) \<Longrightarrow> P x \<rbrakk>
  \<Longrightarrow> P a"
by (blast intro: interval_induct)


subsubsection \<open>Monotonicity and injectivity of artithmetic operators\<close>

lemma add_left_inj: "inj (\<lambda>x. n + (x::'a::cancel_ab_semigroup_add))"
by (simp add: inj_on_def)

lemma add_right_inj: "inj (\<lambda>x. x + (n::'a::cancel_ab_semigroup_add))"
by (simp add: inj_on_def)

lemma mult_left_inj: "0 < n \<Longrightarrow> inj (\<lambda>x. (n::nat) * x)"
by (simp add: inj_on_def)

lemma mult_right_inj: "0 < n \<Longrightarrow> inj (\<lambda>x. x * (n::nat))"
by (simp add: inj_on_def)

lemma sub_left_inj_on: "inj_on (\<lambda>x. (x::nat) - k) {k..}"
by (rule inj_onI, simp)

lemma sub_right_inj_on: "inj_on (\<lambda>x. k - (x::nat)) {..k}"
by (rule inj_onI, simp)

lemma add_left_strict_mono: "strict_mono (\<lambda>x. n + (x::'a::ordered_cancel_ab_semigroup_add))"
by (unfold strict_mono_def, clarify, rule add_strict_left_mono)

lemma add_right_strict_mono: "strict_mono (\<lambda>x. x + (n::'a::ordered_cancel_ab_semigroup_add))"
by (unfold strict_mono_def, clarify, rule add_strict_right_mono)

lemma mult_left_strict_mono: "0 < n \<Longrightarrow> strict_mono (\<lambda>x. n * (x::nat))"
by (unfold strict_mono_def, clarify, simp)

lemma mult_right_strict_mono: "0 < n \<Longrightarrow> strict_mono (\<lambda>x. x * (n::nat))"
by (unfold strict_mono_def, clarify, simp)

lemma sub_left_strict_mono_on: "strict_mono_on (\<lambda>x. (x::nat) - k) {k..}"
apply (rule strict_mono_on_mono_on_conv[THEN iffD2], rule conjI)
apply (unfold mono_on_def, clarify, simp)
apply (rule sub_left_inj_on)
done

lemma div_right_strict_mono_on: "
  \<lbrakk> 0 < (k::nat); \<forall>x\<in>I. \<forall>y\<in>I. x < y \<longrightarrow> x + k \<le> y \<rbrakk> \<Longrightarrow>
  strict_mono_on (\<lambda>x. x div k) I"
apply (unfold strict_mono_on_def, clarify)
apply (fastforce dest: div_le_mono[of _ _ k])
done

lemma mod_eq_div_right_strict_mono_on: "
  \<lbrakk> 0 < (k::nat); \<forall>x\<in>I. \<forall>y\<in>I. x mod k = y mod k \<rbrakk> \<Longrightarrow>
  strict_mono_on (\<lambda>x. x div k) I"
apply (rule div_right_strict_mono_on, simp)
apply (blast intro: less_mod_eq_imp_add_divisor_le)
done

corollary div_right_inj_on: "
  \<lbrakk> 0 < (k::nat); \<forall>x\<in>I. \<forall>y\<in>I. x < y \<longrightarrow> x + k \<le> y \<rbrakk> \<Longrightarrow>
  inj_on (\<lambda>x. x div k) I"
by (rule strict_mono_on_imp_inj_on[OF div_right_strict_mono_on])

corollary mod_eq_imp_div_right_inj_on: "
  \<lbrakk> 0 < (k::nat); \<forall>x\<in>I. \<forall>y\<in>I. x mod k = y mod k \<rbrakk> \<Longrightarrow>
  inj_on (\<lambda>x. x div k) I"
by (rule strict_mono_on_imp_inj_on[OF mod_eq_div_right_strict_mono_on])


subsection \<open>\<open>Min\<close> and \<open>Max\<close> elements of a set\<close>

text \<open>A special minimum operator is required for dealing with infinite wellordered sets
  because the standard operator @{term "Min"} is usable only with finite sets.\<close>

definition iMin :: "'a::wellorder set \<Rightarrow> 'a"
  where "iMin I \<equiv> LEAST x. x \<in> I"


subsubsection \<open>Basic results, as for \<open>Least\<close>\<close>

lemma iMinI: "k \<in> I \<Longrightarrow> iMin I \<in> I"
unfolding iMin_def
by (rule_tac k=k in LeastI)

lemma iMinI_ex: "\<exists>x. x \<in> I \<Longrightarrow> iMin I \<in> I"
by (blast intro: iMinI)

corollary  iMinI_ex2: "I \<noteq> {} \<Longrightarrow> iMin I \<in> I"
by (blast intro: iMinI_ex)

lemma iMinI2: "\<lbrakk> k \<in> I; \<And>x. x \<in> I \<Longrightarrow> P x \<rbrakk> \<Longrightarrow> P (iMin I)"
by (blast intro: iMinI)

lemma iMinI2_ex: "\<lbrakk> \<exists>x. x \<in> I; \<And>x. x \<in> I \<Longrightarrow> P x \<rbrakk> \<Longrightarrow> P (iMin I)"
by (blast intro: iMinI_ex)

lemma iMinI2_ex2: "\<lbrakk> I \<noteq> {} ; \<And>x. x \<in> I \<Longrightarrow> P x \<rbrakk> \<Longrightarrow> P (iMin I)"
by (blast intro: iMinI_ex2)

lemma iMin_le[dest]: "k \<in> I \<Longrightarrow> iMin I \<le> k"
by (simp only: iMin_def Least_le)

lemma iMin_neq_imp_greater[dest]: "\<lbrakk> k \<in> I; k \<noteq> iMin I \<rbrakk> \<Longrightarrow> iMin I < k"
by (rule order_neq_le_trans[OF not_sym iMin_le])

lemma iMin_mono: "
  \<lbrakk> mono f; \<exists>x. x \<in> I \<rbrakk> \<Longrightarrow> iMin (f ` I) = f (iMin I)"
apply (unfold iMin_def)
apply (rule Least_mono[of f I], simp)
apply (rule_tac x="iMin I" in bexI)
 apply (simp add: iMin_le)
apply (simp add: iMinI_ex)
done

corollary iMin_mono2: "
  \<lbrakk> mono f; I \<noteq> {} \<rbrakk> \<Longrightarrow> iMin (f ` I) = f (iMin I)"
by (blast intro: iMin_mono)

lemma not_less_iMin: "k < iMin I \<Longrightarrow> k \<notin> I"
unfolding iMin_def
by (rule not_less_Least)

lemma Collect_not_less_iMin: "k < iMin {x. P x} \<Longrightarrow> \<not> P k"
by (drule not_less_iMin, blast)

lemma Collect_iMin_le: "P k \<Longrightarrow> iMin {x. P x} \<le> k"
by (rule iMin_le, blast)

lemma Collect_minI: "\<lbrakk> k \<in> I; P (k::('a::wellorder)) \<rbrakk> \<Longrightarrow> \<exists>x\<in>I. P x \<and> (\<forall>y\<in>I. y < x \<longrightarrow> \<not> P y)"
apply (rule_tac x="iMin {y \<in> I. P y}" in bexI)
 prefer 2
 apply (rule subsetD[OF _ iMinI, OF Collect_is_subset], blast)
apply (rule conjI)
 apply (blast intro: iMinI2)
apply (blast dest: not_less_iMin)
done

corollary Collect_minI_ex: "\<exists>k\<in>I. P (k::('a::wellorder)) \<Longrightarrow> \<exists>x\<in>I. P x \<and> (\<forall>y\<in>I. y < x \<longrightarrow> \<not> P y)"
by (erule bexE, rule Collect_minI)

corollary Collect_minI_ex2: "{k\<in>I. P (k::('a::wellorder))} \<noteq> {} \<Longrightarrow> \<exists>x\<in>I. P x \<and> (\<forall>y\<in>I. y < x \<longrightarrow> \<not> P y)"
by (drule ex_in_conv[THEN iffD2], blast intro: Collect_minI)

lemma iMin_the:  "iMin I = (THE x. x \<in> I \<and> (\<forall>y. y \<in> I \<longrightarrow> x \<le> y))"
by (simp add: iMin_def Least_def)

lemma iMin_the2: "iMin I = (THE x. x \<in> I \<and> (\<forall>y\<in>I. x \<le> y))"
apply (simp add: iMin_the)
apply (subgoal_tac "\<And>x. (\<forall>y \<in> I. x \<le> y) = (\<forall>y. y \<in> I \<longrightarrow> x \<le> y) ")
 prefer 2 apply blast
apply simp
done

lemma iMin_equality: "
  \<lbrakk> k \<in> I; \<And>x. x \<in> I \<Longrightarrow> k \<le> x \<rbrakk> \<Longrightarrow> iMin I = k"
unfolding iMin_def
by (blast intro: Least_equality)

lemma iMin_mono_on: "
  \<lbrakk> mono_on f I; \<exists>x. x \<in> I \<rbrakk> \<Longrightarrow> iMin (f ` I) = f (iMin I)"
apply (unfold mono_on_def)
apply (rule iMin_equality)
apply (blast intro: iMinI_ex)+
done

lemma iMin_mono_on2: "
  \<lbrakk> mono_on f I; I \<noteq> {} \<rbrakk> \<Longrightarrow> iMin (f ` I) = f (iMin I)"
by (rule iMin_mono_on, blast+)

lemma iMinI2_order:"
  \<lbrakk> k \<in> I; \<And>y. y \<in> I \<Longrightarrow> k \<le> y;
    \<And>x. \<lbrakk> x \<in> I; \<forall>y\<in>I. x \<le> y \<rbrakk> \<Longrightarrow> P x \<rbrakk> \<Longrightarrow>
  P (iMin I)"
by (simp add: iMin_def LeastI2_order)

lemma wellorder_iMin_lemma: "
  k \<in> I \<Longrightarrow> iMin I \<in> I \<and> iMin I \<le> k"
by (blast intro: iMinI iMin_le)

lemma iMin_Min_conv: "
  \<lbrakk> finite I; I \<noteq> {} \<rbrakk> \<Longrightarrow> iMin I = Min I"
apply (rule order_antisym)
apply (rule Min_ge_iff[THEN iffD2], assumption+)
apply blast
apply (rule Min_le_iff[THEN iffD2], assumption+)
apply (blast intro: iMinI_ex2)
done

lemma Min_neq_imp_greater[dest]: "\<lbrakk> finite I; k \<in> I; k \<noteq> Min I \<rbrakk> \<Longrightarrow> Min I < k"
by (rule order_neq_le_trans[OF not_sym Min_le])

lemma Max_neq_imp_less[dest]: "\<lbrakk> finite I; k \<in> I; k \<noteq> Max I \<rbrakk> \<Longrightarrow> k < Max I"
by (rule order_neq_le_trans[OF _ Max_ge])

lemma nat_Least_mono: "
  \<lbrakk> A \<noteq> {}; mono (f::(nat\<Rightarrow>nat)) \<rbrakk> \<Longrightarrow>
  (LEAST x. x \<in> f ` A) = f (LEAST x. x \<in> A)"
unfolding iMin_def[symmetric]
by (blast intro: iMin_mono2)


lemma Least_disj: "
  \<lbrakk> \<exists>x. P x; \<exists>x. Q x \<rbrakk> \<Longrightarrow>
  (LEAST (x::'a::wellorder). (P x \<or> Q x)) = min (LEAST x. P x) (LEAST x. Q x)"
apply (elim exE, rename_tac x1 x2)
apply (subgoal_tac "\<And>x1 x2 P Q. \<lbrakk>P x1; Q x2; Least P \<le> Least Q\<rbrakk> \<Longrightarrow> (LEAST x. P x \<or> Q x) = Least P")
 prefer 2
 apply (rule Least_equality)
  apply (blast intro: LeastI Least_le)
  apply (erule disjE)
   apply (rule Least_le, assumption)
  apply (rule order_trans, assumption)
  apply (rule Least_le, assumption)
apply (unfold min_def, split if_split, safe)
 apply blast
apply (subst disj_commute)
apply (fastforce simp: linorder_not_le)
done

lemma Least_imp_le: "
  \<lbrakk> \<exists>x. P x; \<And>x. P x \<Longrightarrow> Q x \<rbrakk> \<Longrightarrow>
  (LEAST (x::'a::wellorder). Q x) \<le> (LEAST x. P x)"
by (blast intro: Least_le LeastI2_ex)

lemma Least_imp_disj_eq: "
  \<lbrakk> \<exists>x. P x; \<And>x. P x \<Longrightarrow> Q x \<rbrakk> \<Longrightarrow>
  (LEAST (x::'a::wellorder). P x \<or> Q x) = (LEAST x. Q x)"
apply (subst Least_disj, assumption, blast)
apply (subst min.commute)
apply (rule min.absorb_iff1[THEN iffD1])
apply (rule Least_imp_le, assumption, blast)
done

lemma Least_le_imp_le: "
  \<lbrakk> \<exists>x. P x; \<exists>x. Q x; \<And>x y. \<lbrakk> P x; Q y \<rbrakk> \<Longrightarrow> x \<le> y \<rbrakk> \<Longrightarrow>
  (LEAST (x::'a::wellorder). P x) \<le> (LEAST (x::'a::wellorder). Q x)"
by (blast intro: LeastI)
lemma Least_le_imp_le_disj: "
  \<lbrakk> \<exists>x. P x; \<And>x y. \<lbrakk> P x; Q y \<rbrakk> \<Longrightarrow> x \<le> y \<rbrakk> \<Longrightarrow>
  (LEAST (x::'a::wellorder). P x \<or> Q x) = (LEAST (x::'a::wellorder). P x)"
apply (case_tac "\<exists>x. Q x")
 apply (simp only: Least_disj min.absorb_iff1[THEN iffD1, OF Least_le_imp_le])
apply simp
done


lemma Max_equality: "\<lbrakk> (k::'a::linorder) \<in> A; finite A; \<And>x. x \<in> A \<Longrightarrow> x \<le> k \<rbrakk> \<Longrightarrow>
  Max A = k"
by (rule Max_eqI)

lemma not_greater_Max: "\<lbrakk> finite A; Max A < k \<rbrakk>  \<Longrightarrow> k \<notin> A"
apply (rule ccontr, simp)
apply (frule Max_ge[of A k], blast)
apply (frule order_le_less_trans[of _ _ k], blast)
apply blast
done

lemma Collect_not_greater_Max: "\<lbrakk> finite {x. P x}; Max {x. P x} < k \<rbrakk> \<Longrightarrow> \<not> P k"
by (drule not_greater_Max, assumption, drule Collect_not_in_imp_not)

lemma Collect_Max_ge: "\<lbrakk> finite {x. P x}; P k \<rbrakk> \<Longrightarrow> k \<le> Max {x. P x}"
by (rule Max_ge, assumption, rule CollectI)

lemma MaxI: "\<lbrakk> k \<in> A; finite A \<rbrakk> \<Longrightarrow> Max A \<in> A"
by (case_tac "A = {}", simp_all)

lemma MaxI_ex: "\<lbrakk> \<exists>x. x \<in> A; finite A \<rbrakk> \<Longrightarrow> Max A \<in> A"
by (blast intro: MaxI)

lemma MaxI_ex2: "\<lbrakk> A \<noteq> {}; finite A \<rbrakk> \<Longrightarrow> Max A \<in> A"
by (blast intro: MaxI)

lemma MaxI2: "\<lbrakk> k \<in> A; \<And>x. x \<in> A \<Longrightarrow> P x; finite A \<rbrakk> \<Longrightarrow> P (Max A)"
by (drule Max_in, blast+)

lemma MaxI2_ex:"\<lbrakk> \<exists>x. x \<in> A; \<And>x. x \<in> A \<Longrightarrow> P x; finite A \<rbrakk> \<Longrightarrow> P (Max A)"
by (blast intro: MaxI2)

lemma MaxI2_ex2:"\<lbrakk> A \<noteq> {}; \<And>x. x \<in> A \<Longrightarrow> P x; finite A \<rbrakk> \<Longrightarrow> P (Max A)"
by (blast intro: MaxI2)

lemma Max_mono: "\<lbrakk> mono f; \<exists>x. x \<in> A; finite A \<rbrakk> \<Longrightarrow> Max (f ` A) = f (Max A)"
apply (unfold mono_def)
apply clarify
apply (frule Max_in, blast)
apply (rule Max_equality, clarsimp+)
done

lemma Max_mono2:"\<lbrakk> mono f; A \<noteq> {}; finite A \<rbrakk> \<Longrightarrow> Max (f ` A) = f (Max A)"
by (blast intro: Max_mono)

lemma Max_mono_on: "\<lbrakk> mono_on f A; \<exists>x. x \<in> A; finite A \<rbrakk> \<Longrightarrow> Max (f ` A) = f (Max A)"
apply (unfold mono_on_def)
apply (rule Max_equality)
  apply (blast intro: Max_in)
 apply (rule finite_imageI, assumption)
apply (blast intro: Max_in Max_ge)
done

lemma Max_mono_on2: "
  \<lbrakk> mono_on f A; A \<noteq> {}; finite A \<rbrakk> \<Longrightarrow> Max (f ` A) = f (Max A)"
by (rule Max_mono_on, blast+)

lemma Max_the: "
  \<lbrakk> A \<noteq> {}; finite A \<rbrakk> \<Longrightarrow>
  Max A = (THE x. x \<in> A \<and> (\<forall>y. y \<in> A \<longrightarrow> y \<le> x))"
apply (rule iffD1[OF eq_commute])
apply (rule the_equality, simp)
apply (rule sym)
apply (rule Max_equality)
apply blast+
done

lemma Max_the2: "\<lbrakk> A \<noteq> {}; finite A \<rbrakk> \<Longrightarrow>
  Max A = (THE x. x \<in> A \<and> (\<forall>y\<in>A. y \<le> x))"
apply (simp add: Max_the)
apply (subgoal_tac "\<And>x. (\<forall>y\<in>A. y \<le> x) = (\<forall>y. y \<in> A \<longrightarrow> y \<le> x) ")
 prefer 2
 apply blast
apply simp
done

lemma wellorder_Max_lemma: "\<lbrakk> k \<in> A; finite A \<rbrakk> \<Longrightarrow> Max A \<in> A \<and> k \<le> Max A"
by (case_tac "A = {}", simp_all)

lemma MaxI2_order: "\<lbrakk> k \<in> A; finite A; \<And>y. y \<in> A \<Longrightarrow> y \<le> k;
  \<And>x. \<lbrakk> x \<in> A; \<forall>y\<in>A. y \<le> x \<rbrakk> \<Longrightarrow> P x \<rbrakk>
  \<Longrightarrow> P (Max A)"
by (simp add: Max_equality)

lemma Min_le_Max: "\<lbrakk> finite A; A \<noteq> {} \<rbrakk> \<Longrightarrow> Min A \<le> Max A"
by (rule Max_ge[OF _ Min_in])

lemma iMin_le_Max: "\<lbrakk> finite A; A \<noteq> {} \<rbrakk> \<Longrightarrow> iMin A \<le> Max A"
by (rule ssubst[OF iMin_Min_conv], assumption+, rule Min_le_Max)


subsubsection \<open>\<open>Max\<close> for sets over \<open>enat\<close>\<close>

definition iMax :: "nat set \<Rightarrow> enat"
  where "iMax i \<equiv> if (finite i) then (enat (Max i)) else \<infinity>"

lemma iMax_finite_conv: "finite I = (iMax I \<noteq> \<infinity>)"
by (simp add: iMax_def)

lemma iMax_infinite_conv: "infinite I = (iMax I = \<infinity>)"
by (simp add: iMax_def)

lemma "class.distrib_lattice (min::('a::linorder \<Rightarrow> 'a \<Rightarrow> 'a)) (\<le>) (<) max"
apply (subgoal_tac "class.order (\<le>) (<)")
 prefer 2
 apply (rule class.order.intro)
  apply (rule class.preorder.intro)
  apply (rule less_le_not_le)
  apply (rule order_refl)
  apply (rule order_trans, assumption+)
 apply (rule class.order_axioms.intro)
 apply (rule order_antisym, assumption+)
apply (subgoal_tac "class.linorder (\<le>) (<)")
 prefer 2
 apply (rule class.linorder.intro, assumption)
 apply (rule class.linorder_axioms.intro)
 apply (rule linorder_class.linear)
apply (rule class.distrib_lattice.intro)
 apply (rule class.lattice.intro)
  apply (rule class.semilattice_inf.intro, assumption)
  apply (rule class.semilattice_inf_axioms.intro)
    apply (rule le_minI1)
   apply (rule le_minI2)
  apply (rule conj_le_imp_min, assumption+)
 apply (rule class.semilattice_sup.intro, assumption)
 apply (rule class.semilattice_sup_axioms.intro)
   apply (rule max.cobounded1)
  apply (rule max.cobounded2)
 apply (rule conj_le_imp_max, assumption+)
apply (rule class.distrib_lattice_axioms.intro)
apply (rule max_min_distrib2)
done

print_locale Lattices.distrib_lattice

lemma max_Min_eq_Min_max[rule_format]: "
  finite A \<Longrightarrow>
  A \<noteq> {} \<longrightarrow>
  max x (Min A) = Min {max x a |a. a \<in> A}"
apply (rule finite.induct[of A], simp_all del: insert_iff)
apply (rename_tac A1 a)
apply (case_tac "A1 = {}", simp)
apply (rule_tac
  t="{max x b |b. b \<in> insert a A1}" and
  s="insert (max x a) {max x b |b. b \<in> A1}"
  in subst)
 apply blast
apply (subst Min_insert, simp_all)
apply (case_tac "a \<le> Min A1")
 apply (frule max_le_monoR[where x=x])
 apply (simp only: min_eqL)
apply (simp only: linorder_not_le)
apply (frule max_le_monoR[where x=x, OF less_imp_le])
apply (simp only: min_eqR)
done

lemma max_iMin_eq_iMin_max: "
  \<lbrakk> finite A; A \<noteq> {} \<rbrakk> \<Longrightarrow>
  max x (iMin A) = iMin {max x a |a. a \<in> A}"
apply (simp add: iMin_Min_conv)
apply (insert iMin_Min_conv[of "{max x a |a. a \<in> A}"], simp)
apply (subgoal_tac "finite {max x a |a. a \<in> A}")
 prefer 2
 apply simp
apply (simp add: max_Min_eq_Min_max)
done

lemma "\<lbrakk> finite A; A \<noteq>{} \<rbrakk> \<Longrightarrow> \<forall>x\<in>A. x \<le> Max A"
by simp


subsubsection \<open>\<open>Min\<close> and \<open>Max\<close> for set operations\<close>

lemma iMin_subset: "\<lbrakk> A \<noteq> {}; A \<subseteq> B \<rbrakk> \<Longrightarrow> iMin B \<le> iMin A"
by (blast intro: iMin_le iMinI_ex2)

lemma Max_subset: "\<lbrakk> A \<noteq> {}; A \<subseteq> B; finite B \<rbrakk> \<Longrightarrow> Max A \<le> Max B"
by (rule linorder_class.Max_mono)

lemma Min_subset: "\<lbrakk> A \<noteq> {}; A \<subseteq> B; finite B \<rbrakk> \<Longrightarrow> Min B \<le> Min A"
by (rule linorder_class.Min_antimono)

lemma iMin_Int_ge1: "(A \<inter> B) \<noteq> {} \<Longrightarrow> iMin A \<le> iMin (A \<inter> B)"
by (rule iMin_subset[OF _ Int_lower1])

lemma iMin_Int_ge2: "(A \<inter> B) \<noteq> {} \<Longrightarrow> iMin B \<le> iMin (A \<inter> B)"
by (rule iMin_subset[OF _ Int_lower2])

lemma iMin_Int_ge: "(A \<inter> B) \<noteq> {} \<Longrightarrow> max (iMin A) (iMin B) \<le> iMin (A \<inter> B)"
apply (rule conj_le_imp_max)
apply (rule iMin_Int_ge1, assumption)
apply (rule iMin_Int_ge2, assumption)
done

lemma Max_Int_le1: "\<lbrakk> (A \<inter> B) \<noteq> {}; finite A \<rbrakk> \<Longrightarrow> Max (A \<inter> B) \<le> Max A"
by (rule Max_subset[OF _ Int_lower1])

lemma Max_Int_le2: "\<lbrakk> (A \<inter> B) \<noteq> {}; finite B \<rbrakk> \<Longrightarrow> Max (A \<inter> B) \<le> Max B"
by (rule Max_subset[OF _ Int_lower2])

lemma Max_Int_le: "\<lbrakk> (A \<inter> B) \<noteq> {}; finite A; finite B \<rbrakk> \<Longrightarrow>
  Max (A \<inter> B) \<le> min (Max A) (Max B)"
apply (rule conj_le_imp_min)
apply (rule Max_Int_le1, assumption+)
apply (rule Max_Int_le2, assumption+)
done





lemma iMin_Un[rule_format]: "
  \<lbrakk> A \<noteq> {}; B \<noteq> {} \<rbrakk> \<Longrightarrow>
  iMin (A \<union> B) = min (iMin A) (iMin B)"
apply (rule order_antisym)
 apply simp
 apply (blast intro: iMin_subset)
apply (simp add: min_le_iff_disj)
apply (insert iMinI_ex2[of "A\<union>B"])
apply (blast intro: iMin_le)
done

lemma iMin_singleton[simp]: "iMin {a} = a"
by (rule singletonI[THEN iMinI, THEN singletonD])

lemma iMax_singleton[simp]: "iMax {a} = enat a"
by (simp add: iMax_def)

lemma Max_le_Min_imp_singleton: "
  \<lbrakk> finite A; A \<noteq> {}; Max A \<le> Min A \<rbrakk> \<Longrightarrow> A = {Min A}"
apply (frule Max_le_iff[THEN iffD1, of _ "Min A"], assumption+)
apply (frule Min_ge_iff[THEN iffD1, of _ "Min A"], assumption, simp)
apply (rule set_eqI)
apply (unfold Ball_def)
apply (erule_tac x=x in allE, erule_tac x=x in allE)
apply (blast intro: order_antisym Min_in)
done
lemma Max_le_Min_conv_singleton: "
  \<lbrakk> finite A; A \<noteq> {} \<rbrakk> \<Longrightarrow> (Max A \<le> Min A) = (\<exists>x. A = {x})"
apply (rule iffI)
 apply (rule_tac x="Min A" in exI)
 apply (rule Max_le_Min_imp_singleton, assumption+)
apply fastforce
done



lemma Max_le_iMin_imp_le: "
  \<lbrakk> finite A; Max A \<le> iMin B; a \<in> A; b \<in> B \<rbrakk> \<Longrightarrow> a \<le> b"
by (blast dest: Max_ge intro: order_trans)

lemma le_imp_Max_le_iMin: "
  \<lbrakk> finite A; A \<noteq> {}; B \<noteq> {}; \<forall>a\<in>A. \<forall>b\<in>B. a \<le> b \<rbrakk> \<Longrightarrow> Max A \<le> iMin B"
by (blast intro: Max_in iMinI_ex2)

lemma Max_le_iMin_conv_le: "
  \<lbrakk> finite A; A \<noteq> {}; B \<noteq> {} \<rbrakk> \<Longrightarrow> (Max A \<le> iMin B) = (\<forall>a\<in>A. \<forall>b\<in>B. a \<le> b)"
by (blast intro: Max_le_iMin_imp_le le_imp_Max_le_iMin)

lemma Max_less_iMin_imp_less: "
  \<lbrakk> finite A; Max A < iMin B; a \<in> A; b \<in> B \<rbrakk> \<Longrightarrow> a < b"
by (blast dest: Max_less_iff intro: order_less_le_trans iMin_le)

lemma less_imp_Max_less_iMin: "
  \<lbrakk> finite A; A \<noteq> {}; B \<noteq> {}; \<forall>a\<in>A. \<forall>b\<in>B. a < b \<rbrakk> \<Longrightarrow> Max A < iMin B"
by (blast intro: Max_in iMinI_ex2)

lemma Max_less_iMin_conv_less: "
  \<lbrakk> finite A; A \<noteq> {}; B \<noteq> {} \<rbrakk> \<Longrightarrow> (Max A < iMin B) = (\<forall>a\<in>A. \<forall>b\<in>B. a < b)"
by (blast intro: Max_less_iMin_imp_less less_imp_Max_less_iMin)

lemma Max_less_iMin_imp_disjoint: "
  \<lbrakk> finite A; Max A < iMin B \<rbrakk> \<Longrightarrow> A \<inter> B = {}"
apply (case_tac "A = {}", simp)
apply (case_tac "B = {}", simp)
apply (rule disjoint_iff_not_equal[THEN iffD2])
apply (intro ballI)
apply (rule less_imp_neq)
by (rule Max_less_iMin_imp_less)


lemma iMin_in_idem: "n \<in> I \<Longrightarrow> min n (iMin I) = iMin I"
by (simp add: iMin_le min_eqR)

lemma iMin_insert: "I \<noteq> {} \<Longrightarrow> iMin (insert n I) = min n (iMin I)"
apply (subst insert_is_Un)
apply (subst iMin_Un)
apply simp_all
done

lemma iMin_insert_remove: "
  iMin (insert n I) =
  (if I - {n} = {} then n else min n (iMin (I - {n})))"
by (metis iMin_insert iMin_singleton insert_Diff_single)

lemma iMin_remove: "n \<in> I \<Longrightarrow> iMin I = (if I - {n} = {} then n else min n (iMin (I - {n})))"
by (metis iMin_insert_remove insert_absorb)

lemma iMin_subset_idem: "\<lbrakk> B \<noteq> {}; B \<subseteq> A \<rbrakk> \<Longrightarrow> min (iMin B) (iMin A) = iMin A"
by (metis iMin_subset min.absorb2)

lemma iMin_union_inter: "A \<inter> B \<noteq> {} \<Longrightarrow> min (iMin (A \<union> B)) (iMin (A \<inter> B)) = min (iMin A) (iMin B)"
by (metis Int_empty_left Int_lower2 Un_absorb2 Un_assoc Un_empty iMin_Un)

lemma iMin_ge_iff: "I \<noteq> {} \<Longrightarrow> (n \<le> iMin I) = (\<forall>a\<in>I. n \<le> a)"
by (metis Collect_iMin_le Collect_mem_eq iMinI_ex2 order_trans)

lemma iMin_gr_iff: "I \<noteq> {} \<Longrightarrow> (n < iMin I) = (\<forall>a\<in>I. n < a)"
by (metis iMinI_ex2 iMin_neq_imp_greater order_less_trans)

lemma iMin_le_iff: "I \<noteq> {} \<Longrightarrow> (iMin I \<le> n) = (\<exists>a\<in>I. a \<le> n)"
by (metis Collect_iMin_le Collect_mem_eq iMinI_ex2 order_trans)

lemma iMin_less_iff: "I \<noteq> {} \<Longrightarrow> (iMin I < n) = (\<exists>a\<in>I. a < n)"
by (metis iMinI_ex2 iMin_neq_imp_greater order_less_trans)

lemma hom_iMin_commute: "\<lbrakk> \<And>x y. h (min x y) = min (h x) (h y); I \<noteq> {} \<rbrakk> \<Longrightarrow> iMin (h ` I) = h (iMin I)"
apply (rule iMin_equality)
 apply (blast intro: iMinI_ex2)
apply (rename_tac y)
apply (drule_tac x="iMin I" in meta_spec)
apply (clarsimp simp: image_iff, rename_tac x)
apply (drule_tac x=x in meta_spec)
apply (rule_tac t="h (iMin I)" and s="min (h (iMin I)) (h x)" in subst)
 apply (simp add: min_eqL[OF iMin_le])
apply simp
done

text \<open>Synonyms for similarity with theorem names for @{term Min}"\<close>

lemmas iMin_eqI = iMin_equality

lemmas iMin_in = iMinI_ex2


subsection \<open>Some auxiliary results for set operations\<close>

subsubsection \<open>Some additional abbreviations for relations\<close>

text \<open>Abbreviations for \<open>refl\<close>, \<open>sym\<close>, \<open>equiv\<close>, \<open>refl\<close>, \<open>trans\<close>\<close>

abbreviation (input) reflP :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool" where
  "reflP r \<equiv> refl {(x, y). r x y}"

abbreviation (input) symP :: "('a => 'a => bool) => bool" where
  "symP r == sym {(x, y). r x y}"

abbreviation (input) transP :: "('a => 'a => bool) => bool" where
  "transP r == trans {(x, y). r x y}"

abbreviation (input) equivP :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool" where
  "equivP r \<equiv> reflP r \<and> symP r \<and> transp r"

abbreviation (input) irreflP :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool" where
  "irreflP r \<equiv> irrefl {(x, y). r x y}"


text \<open>Example for \<open>reflP\<close>\<close>
lemma "reflP ((\<le>)::('a::preorder \<Rightarrow> 'a \<Rightarrow> bool))"
by (simp add: refl_on_def)

text \<open>Example for \<open>symP\<close>\<close>
lemma "symP (=)"
by (simp add: sym_def)

text \<open>Example for \<open>equivP\<close>\<close>
lemma "equivP (=)"
by (simp add: trans_def refl_on_def sym_def)

text \<open>Example for \<open>irreflP\<close>\<close>
lemma "irreflP ((<)::('a::preorder \<Rightarrow> 'a \<Rightarrow> bool))"
by (simp add: irrefl_def)


subsubsection \<open>Auxiliary results for \<open>singletons\<close>\<close>

lemma singleton_not_empty: "{a} \<noteq> {}" by blast
lemma singleton_finite: "finite {a}" by blast

lemma singleton_ball: "(\<forall>x\<in>{a}. P x) = P a" by blast
lemma singleton_bex: "(\<exists>x\<in>{a}. P x) = P a" by blast

lemma subset_singleton_conv: "(A \<subseteq> {a}) = (A = {} \<or> A = {a})" by blast
lemma singleton_subset_conv: "({a} \<subseteq> A) = (a \<in> A)" by blast

lemma singleton_eq_conv: "({a} = {b}) = (a = b)" by blast
lemma singleton_subset_singleton_conv: "({a} \<subseteq> {b}) = (a = b)" by blast

lemma singleton_Int1_if: "{a} \<inter> A = (if a \<in> A then {a} else {})"
by (split if_split, blast)

lemma singleton_Int2_if: "A \<inter> {a} = (if a \<in> A then {a} else {})"
by (split if_split, blast)

lemma singleton_image: "f ` {a} = {f a}" by blast
lemma inj_on_singleton: "inj_on f {a}" by blast
lemma strict_mono_on_singleton: "strict_mono_on f {a}"
unfolding strict_mono_on_def by blast


subsubsection \<open>Auxiliary results for \<open>finite\<close> and \<open>infinite\<close> sets\<close>

lemma infinite_imp_not_singleton: "infinite A \<Longrightarrow> \<not> (\<exists>a. A = {a})" by blast

lemma infinite_insert: "infinite (insert a A) = infinite A"
by simp

lemma infinite_Diff_insert: "infinite (A - insert a B) = infinite (A - B)"
by simp

lemma subset_finite_imp_finite: "\<lbrakk> finite A; B \<subseteq> A \<rbrakk> \<Longrightarrow> finite B"
by (rule finite_subset)

lemma infinite_not_subset_finite: "\<lbrakk> infinite A; finite B \<rbrakk> \<Longrightarrow> \<not> A \<subseteq> B"
by (blast intro: subset_finite_imp_finite)

lemma Un_infinite_right: "infinite T \<Longrightarrow> infinite (S \<union> T)" by blast
lemma Un_infinite_iff: "infinite (S \<union> T) = (infinite S \<or> infinite T)" by blast

text \<open>Give own name to the lemma about finiteness of the integer image of a nat set\<close>
corollary finite_A_int_A_conv: "finite A = finite (int ` A)"
proof -
  have "inj_on int A"
    by (auto intro: inj_onI)
  then show ?thesis
    by (simp add: finite_image_iff)
qed

text \<open>Corresponding fact fo infinite sets\<close>
corollary infinite_A_int_A_conv: "infinite A = infinite (int ` A)"
by (simp only: finite_A_int_A_conv)


lemma cartesian_product_infiniteL_imp_infinite: "\<lbrakk> infinite A; B \<noteq> {} \<rbrakk> \<Longrightarrow> infinite (A \<times> B)"
by (blast dest: finite_cartesian_productD1)

lemma cartesian_product_infiniteR_imp_infinite: "\<lbrakk> infinite B; A \<noteq> {} \<rbrakk> \<Longrightarrow> infinite (A \<times> B)"
by (blast dest: finite_cartesian_productD2)

lemma finite_nat_iff_bounded2: "
  finite S = (\<exists>(k::nat).\<forall>n\<in>S. n < k)"
by (simp only: finite_nat_iff_bounded, blast)

lemma finite_nat_iff_bounded_le2: "
  finite S = (\<exists>(k::nat).\<forall>n\<in>S. n \<le> k)"
by (simp only: finite_nat_iff_bounded_le, blast)

lemma nat_asc_chain_imp_unbounded: "
  \<lbrakk> S \<noteq> {}; (\<forall>m\<in>S. \<exists>n\<in>S. m < (n::nat)) \<rbrakk> \<Longrightarrow> \<forall>m. \<exists>n\<in>S. m \<le> n"
apply (rule allI)
apply (induct_tac m)
 apply blast
apply (erule bexE)
apply (rename_tac n1)
apply (erule_tac x=n1 in ballE)
  prefer 2
  apply simp
apply (clarify, rename_tac x, rule_tac x=x in bexI)
apply simp_all
done

lemma infinite_nat_iff_asc_chain: "
  S \<noteq> {} \<Longrightarrow> infinite S = (\<forall>m\<in>S. \<exists>n\<in>S. m < (n::nat))"
by (metis Max_in infinite_nat_iff_unbounded not_greater_Max)

lemma infinite_imp_asc_chain: "infinite S \<Longrightarrow> \<forall>m\<in>S. \<exists>n\<in>S. m < (n::nat)"
by (rule infinite_nat_iff_asc_chain[THEN iffD1, OF infinite_imp_nonempty])


lemma infinite_image_imp_infinite: "infinite (f ` A) \<Longrightarrow> infinite A"
by fastforce

lemma inj_on_imp_infinite_image: "\<lbrakk> infinite A; inj_on f A \<rbrakk> \<Longrightarrow> infinite (f ` A)"
apply (frule card_image)
apply (fastforce simp: card_eq_0_iff)
done

lemma inj_on_infinite_image_iff: "inj_on f A \<Longrightarrow> infinite (f ` A) = infinite A"
apply (rule iffI)
 apply (rule ccontr, simp)
apply (rule inj_on_imp_infinite_image, assumption+)
done

lemma inj_on_finite_image_iff: "inj_on f A \<Longrightarrow> finite (f ` A) = finite A"
by (drule inj_on_infinite_image_iff, simp)

lemma nat_ex_greater_finite_Max_conv: "
  A \<noteq> {} \<Longrightarrow> (\<exists>x\<in>A. (n::nat) < x) = (finite A \<longrightarrow> n < Max A)"
apply (rule iffI)
 apply (blast intro: order_less_le_trans Max_ge)
apply (case_tac "finite A")
 apply (blast intro: Max_in)
apply (drule infinite_nat_iff_unbounded[THEN iffD1, rule_format, of _ n])
apply blast
done

corollary nat_ex_greater_infinite_finite_Max_conv': "
  (\<exists>x\<in>A. (n::nat) < x) = (finite A \<and> A \<noteq> {} \<and> n < Max A \<or> infinite A)"
apply (case_tac "A = {}", blast)
apply (drule nat_ex_greater_finite_Max_conv[of _ n])
apply blast
done


subsubsection \<open>Some auxiliary results for disjoint sets\<close>

lemma disjoint_iff_in_not_in1: "(A \<inter> B = {}) = (\<forall>x\<in>A. x \<notin> B)" by blast
lemma disjoint_iff_in_not_in2: "(A \<inter> B = {}) = (\<forall>x\<in>B. x \<notin> A)" by blast

lemma disjoint_in_Un: "
  \<lbrakk> A \<inter> B = {}; x \<in> A \<union> B \<rbrakk> \<Longrightarrow> x \<notin> A \<or> x \<notin> B"
by (blast intro: disjoint_iff_in_not_in1[THEN iffD1])+


lemma partition_Union: "A \<subseteq> \<Union>C \<Longrightarrow> (\<Union>c\<in>C. A \<inter> c) = A" by blast

lemma disjoint_partition_Int: "
  \<forall>c1\<in>C. \<forall>c2\<in>C. c1 \<noteq> c2 \<longrightarrow> c1 \<inter> c2 = {} \<Longrightarrow>
  \<forall>a1\<in>{A \<inter> c| c. c \<in> C}. \<forall>a2\<in>{A \<inter> c| c. c \<in> C}.
    a1 \<noteq> a2 \<longrightarrow> a1 \<inter> a2 = {}"
by blast

lemma "{f x |x. x \<in> A} = (\<Union>x\<in>A. {f x})"
by fastforce

text \<open>This lemma version drops the superfluous precondition @{term "finite (\<Union>C)"}
  (and turns the resulting equation to the sensible order \<open>card .. = k * card ..\<close>).\<close>
lemma card_partition: "
  \<lbrakk> finite C; \<And>c. c \<in> C \<Longrightarrow> card c = k; \<And>c1 c2. \<lbrakk>c1 \<in> C; c2 \<in> C; c1 \<noteq> c2\<rbrakk> \<Longrightarrow> c1 \<inter> c2 = {} \<rbrakk> \<Longrightarrow>
  card (\<Union>C) = k * card C"
by (metis card_infinite card_partition finite_Union mult_eq_if)



subsubsection \<open>Some auxiliary results for subset relation\<close>

lemma subset_image_Int: "A \<subseteq> B \<Longrightarrow> f ` (A \<inter> B) = f ` A \<inter> f ` B"
by (simp only: Int_absorb2 image_mono)

lemma image_diff_disjoint_image_Int: "
  \<lbrakk> f ` (A - B) \<inter> f ` B = {} \<rbrakk> \<Longrightarrow>
  f ` (A \<inter> B) = f ` A \<inter> f ` B"
apply (rule set_eqI)
apply (simp add: image_iff)
apply blast
done

lemma subset_imp_Int_subset1: "A \<subseteq> C \<Longrightarrow> A \<inter> B \<subseteq> C"
by (rule subset_trans[of _ "C \<inter> B", OF Int_mono, OF _ subset_refl Int_lower1])

lemma subset_imp_Int_subset2: "B \<subseteq> C \<Longrightarrow> A \<inter> B \<subseteq> C"
by (simp only: Int_commute[of A], rule subset_imp_Int_subset1)


subsubsection \<open>Auxiliary results for intervals from \<open>SetInterval\<close>\<close>

lemmas set_interval_defs =
  lessThan_def atMost_def
  greaterThan_def atLeast_def
  greaterThanLessThan_def atLeastLessThan_def
  greaterThanAtMost_def atLeastAtMost_def

lemma image_add_atLeast:
  "(\<lambda>n::nat. n+k) ` {i..} = {i+k..}" (is "?A = ?B")
proof
  show "?A \<subseteq> ?B" by fastforce
next
  show "?B \<subseteq> ?A"
  proof
    fix n assume a: "n : ?B"
    hence "n - k \<in> {i..}" by simp
    moreover have "n = (n - k) + k" using a by fastforce
    ultimately show "n \<in> ?A" by blast
  qed
qed

lemma image_add_atMost:
  "(\<lambda>n::nat. n+k) ` {..i} = {k..i+k}" (is "?A = ?B")
  
proof -
  have s1: "{..i} = {0..i}"
    by (simp add: set_interval_defs)
  then show "?A = ?B"
    by simp
qed

corollary image_Suc_atLeast: "Suc ` {i..} = {Suc i..}"
by (insert image_add_atLeast[of "Suc 0"], simp)

corollary image_Suc_atMost: "Suc ` {..i} = {Suc 0..Suc i}"
by (insert image_add_atMost[of "Suc 0"], simp)

lemmas image_add_lemmas =
  image_add_atLeastAtMost
  image_add_atLeast
  image_add_atMost
lemmas image_Suc_lemmas =
  image_Suc_atLeastAtMost
  image_Suc_atLeast
  image_Suc_atMost

lemma atMost_atLeastAtMost_0_conv: "{..i::nat} = {0..i}"
by (simp add: set_interval_defs)

lemma atLeastAtMost_subset_atMost: "(k::'a::order) \<le> k' \<Longrightarrow> {l..k} \<subseteq> {..k'}"
by (simp)

lemma lessThan_insert: "insert (n::'a::order) {..<n} = {..n}"
apply (rule set_eqI)
apply (clarsimp simp add: order_le_less)
apply blast
done

lemma greaterThan_insert: "insert (n::'a::order) {n<..} = {n..}"
apply (rule set_eqI)
apply (clarsimp simp add: order_le_less)
apply blast
done

lemma atMost_remove: "{..n} - {(n::'a::order)} = {..<n}"
apply (simp only: lessThan_insert[symmetric])
apply (rule Diff_insert_absorb)
apply simp
done

lemma atLeast_remove: "{n..} - {(n::'a::order)} = {n<..}"
apply (simp only: greaterThan_insert[symmetric])
apply (rule Diff_insert_absorb)
apply simp
done


lemma atMost_lessThan_conv: "{..n} = {..<Suc n}"
by (simp only: atMost_def lessThan_def less_Suc_eq_le)

lemma atLeastAtMost_atLeastLessThan_conv: "{l..u} = {l..<Suc u}"
by (simp only: atLeastAtMost_def atLeastLessThan_def atMost_lessThan_conv)

lemma atLeast_greaterThan_conv: "{Suc n..} = {n<..}"
by (simp only: atLeast_def greaterThan_def Suc_le_eq)

lemma atLeastAtMost_greaterThanAtMost_conv: "{Suc l..u} = {l<..u}"
by (simp only: greaterThanAtMost_def atLeastAtMost_def atLeast_greaterThan_conv)



lemma finite_subset_atLeastAtMost: "finite A \<Longrightarrow> A \<subseteq> {Min A..Max A}"
by (simp add: subset_eq)

lemma Max_le_imp_subset_atMost: "
  \<lbrakk> finite A;  Max A \<le> n \<rbrakk> \<Longrightarrow> A \<subseteq> {..n}"
by (rule subset_trans[OF finite_subset_atLeastAtMost atLeastAtMost_subset_atMost])

lemma subset_atMost_imp_Max_le:"
  \<lbrakk> finite A; A \<noteq> {}; A \<subseteq> {..n} \<rbrakk> \<Longrightarrow> Max A \<le> n"
by (simp add: subset_iff)

lemma subset_atMost_Max_le_conv: "
  \<lbrakk> finite A; A \<noteq> {} \<rbrakk> \<Longrightarrow> (A \<subseteq> {..n}) = (Max A \<le> n)"
apply (rule iffI)
 apply (blast intro: subset_atMost_imp_Max_le)
apply (rule Max_le_imp_subset_atMost, assumption+)
done


lemma iMin_atLeast: "iMin {n..} = n"
by (rule iMin_equality, simp_all)

lemma iMin_greaterThan: "iMin {n<..} = Suc n"
by (simp only: atLeast_Suc_greaterThan[symmetric] iMin_atLeast)

lemma iMin_atMost: "iMin {..(n::nat)} = 0"
by (rule iMin_equality, simp_all)

lemma iMin_lessThan: "0 < n \<Longrightarrow> iMin {..<(n::nat)} = 0"
by (rule iMin_equality, simp_all)

lemma Max_atMost: "Max {..(n::nat)} = n"
by (rule Max_equality[OF _ finite_atMost], simp_all)

lemma Max_lessThan: "0 < n \<Longrightarrow> Max {..<n} = n - Suc 0"
by (rule Max_equality[OF _ finite_lessThan], simp_all)

lemma iMin_atLeastLessThan: "m < n \<Longrightarrow> iMin {m..<n} = m"
by (rule iMin_equality, simp_all)

lemma Max_atLeastLessThan: "m < n \<Longrightarrow> Max {m..<n} = n - Suc 0"
by (rule Max_equality[OF _ finite_atLeastLessThan], simp_all add: less_imp_le_pred)

lemma iMin_greaterThanLessThan: "Suc m < n \<Longrightarrow> iMin {m<..<n} = Suc m"
by (simp only: atLeastSucLessThan_greaterThanLessThan[symmetric] iMin_atLeastLessThan)

lemma Max_greaterThanLessThan: "Suc m < n \<Longrightarrow> Max {m<..<n} = n - Suc 0"
by (simp only: atLeastSucLessThan_greaterThanLessThan[symmetric] Max_atLeastLessThan)

lemma iMin_greaterThanAtMost: "m < n \<Longrightarrow> iMin {m<..n} = Suc m"
by (simp only: atLeastSucAtMost_greaterThanAtMost[symmetric] atLeastLessThanSuc_atLeastAtMost[symmetric] iMin_atLeastLessThan)

lemma Max_greaterThanAtMost: "m < n \<Longrightarrow> Max {m<..(n::nat)} = n"
by (simp add: atLeastSucAtMost_greaterThanAtMost[symmetric] atLeastLessThanSuc_atLeastAtMost[symmetric] Max_atLeastLessThan)

lemma iMin_atLeastAtMost: "m \<le> n \<Longrightarrow> iMin {m..n} = m"
by (rule iMin_equality, simp_all)

lemma Max_atLeastAtMost: "m \<le> n \<Longrightarrow> Max {m..(n::nat)} = n"
by (rule Max_equality[OF _ finite_atLeastAtMost], simp_all)

lemma infinite_atLeast: "infinite {(n::nat)..}"
by (rule unbounded_k_infinite[of n], fastforce)

lemma infinite_greaterThan: "infinite {(n::nat)<..}"
by (simp add: atLeast_Suc_greaterThan[symmetric] infinite_atLeast)

lemma infinite_atLeast_int: "infinite {(n::int)..}"
apply (rule_tac f="\<lambda>x. nat (x - n)" in inj_on_infinite_image_iff[THEN iffD1, rule_format])
 apply (fastforce simp: inj_on_def)
apply (rule_tac t="((\<lambda>x. nat (x - n)) ` {n..})" and s="{0..}" in subst)
 apply (simp add: set_eq_iff image_iff Bex_def)
 apply (clarify, rename_tac n1)
 apply (rule_tac x="n + int n1" in exI)
apply simp_all
done

lemma infinite_greaterThan_int: "infinite {(n::int)<..}"
apply (simp only: atLeast_remove[symmetric])
apply (rule Diff_infinite_finite[OF singleton_finite])
apply (rule infinite_atLeast_int)
done

lemma infinite_atMost_int: "infinite {..(n::int)}"
apply (rule_tac f="\<lambda>x. n - x" in inj_on_infinite_image_iff[THEN iffD1, rule_format])
 apply (simp add: inj_on_def)
apply (rule_tac t="((-) n ` {..n})" and s="{0..}" in subst)
 apply (simp add: set_eq_iff image_iff Bex_def)
apply (rule infinite_atLeast_int)
done

lemma infinite_lessThan_int: "infinite {..<(n::int)}"
apply (simp only: atMost_remove[symmetric])
apply (rule Diff_infinite_finite[OF singleton_finite])
apply (rule infinite_atMost_int)
done


subsubsection \<open>Auxiliary results for @{term card}\<close>

lemma sum_singleton: "(\<Sum>x\<in>{a}. f x) = f a"
by simp

lemma card_singleton: "card {a} = Suc 0"
by simp

lemma card_cartesian_product_singleton_right: "card (A \<times> {x}) = card A"
by (simp add: card_cartesian_product)

lemma card_1_imp_singleton: "card A = Suc 0 \<Longrightarrow> (\<exists>a. A = {a})"
by (metis card_eq_SucD)

lemma card_1_singleton_conv: "(card A = Suc 0) = (\<exists>a. A = {a})"
apply (rule iffI)
apply (simp add: card_1_imp_singleton)
apply fastforce
done

lemma card_gr0_imp_finite: "0 < card A \<Longrightarrow> finite A"
by (rule ccontr, simp)
lemma card_gr0_imp_not_empty: "(0 < card A) \<Longrightarrow> A \<noteq> {}"
by (rule ccontr, simp)
lemma not_empty_card_gr0_conv: "finite A \<Longrightarrow> (A \<noteq> {}) = (0 < card A)"
by fastforce

lemma nat_card_le_Max: "card (A::nat set) \<le> Suc (Max A)"
apply (case_tac "finite A")
 prefer 2
 apply simp
apply (cut_tac card_mono[OF finite_atMost, of A "Max A"])
 apply simp
apply fastforce
done

lemma Int_card1: "finite A \<Longrightarrow> card (A \<inter> B) \<le> card A"
by (rule card_mono, simp_all)
lemma Int_card2: "finite B \<Longrightarrow> card (A \<inter> B) \<le> card B"
by (simp only: Int_commute[of A], rule Int_card1)
lemma Un_card1: "\<lbrakk> finite A; finite B \<rbrakk> \<Longrightarrow> card A \<le> card (A \<union> B)"
by (rule card_mono, simp_all)
lemma Un_card2: "\<lbrakk> finite A; finite B \<rbrakk> \<Longrightarrow> card B \<le> card (A \<union> B)"
by (simp only: Un_commute[of A], rule Un_card1)

lemma card_Un_conv: "
  \<lbrakk> finite A; finite B \<rbrakk> \<Longrightarrow>
  card (A \<union> B) = card A + card B - card (A \<inter> B)"
by (simp only: card_Un_Int diff_add_inverse2)
lemma card_Int_conv: "
  \<lbrakk> finite A; finite B \<rbrakk> \<Longrightarrow>
  card (A \<inter> B) = card A + card B - card (A \<union> B)"
by (simp only: card_Un_Int diff_add_inverse)



text \<open>Pigeonhole principle, dirichlet's box principle\<close>
lemma pigeonhole_principle[rule_format]: "
  card (f ` A) < card A \<longrightarrow> (\<exists>x\<in>A. \<exists>y\<in>A. x \<noteq> y \<and> f x = f y)"
apply (case_tac "finite A")
 prefer 2
 apply simp
apply (rule finite.induct[of A])
apply simp_all
apply (clarsimp, rename_tac A1 a)
apply (case_tac "a \<in> A1", force simp: insert_absorb)
apply (case_tac "f a \<in> f ` A1", fastforce+)
done

corollary pigeonhole_principle_linorder[rule_format]: "
  card (f ` A) < card (A::'a::linorder set) \<Longrightarrow> (\<exists>x\<in>A. \<exists>y\<in>A. x < y \<and> f x = f y)"
apply (drule pigeonhole_principle, clarify)
apply (drule neq_iff[THEN iffD1])
apply fastforce
done

corollary pigeonhole_mod: "
  \<lbrakk> 0 < m; m < card A \<rbrakk> \<Longrightarrow> \<exists>x\<in>A. \<exists>y\<in>A. x < y \<and> x mod m = y mod m"
apply (rule pigeonhole_principle_linorder)
apply (rule le_less_trans[of _ "card {..<m}"])
apply (rule card_mono)
apply fastforce+
done

corollary pigeonhole_mod2: "
  \<lbrakk> (0::nat) < m; m \<le> c; inj_on f {..c} \<rbrakk> \<Longrightarrow> \<exists>x\<le>c. \<exists>y\<le>c. x < y \<and> f x mod m = f y mod m"
apply (insert pigeonhole_mod[of m "f ` {..c}"])
apply (clarsimp simp add: card_image, rename_tac x y)
apply (subgoal_tac "x \<noteq> y")
 prefer 2
 apply blast
apply (drule neq_iff[THEN iffD1], safe)
 apply blast
apply (blast intro: eq_commute[THEN iffD1])
done

end
