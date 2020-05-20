(*  Title:       Signed Hereditar(il)y (Finite) Multisets
    Author:      Jasmin Blanchette <jasmin.blanchette at inria.fr>, 2016
    Author:      Dmitriy Traytel <traytel at inf.ethz.ch>, 2016
    Maintainer:  Jasmin Blanchette <jasmin.blanchette at inria.fr>
*)

section \<open>Signed Hereditar(il)y (Finite) Multisets\<close>

theory Signed_Hereditary_Multiset
imports Signed_Multiset Hereditary_Multiset
begin


subsection \<open>Type Definition\<close>

typedef zhmultiset = "UNIV :: hmultiset zmultiset set"
  morphisms zhmsetmset ZHMSet
  by simp

lemmas ZHMSet_inverse[simp] = ZHMSet_inverse[OF UNIV_I]
lemmas ZHMSet_inject[simp] = ZHMSet_inject[OF UNIV_I UNIV_I]

declare
  zhmsetmset_inverse [simp]
  zhmsetmset_inject [simp]

setup_lifting type_definition_zhmultiset


subsection \<open>Multiset Order\<close>

instantiation zhmultiset :: linorder
begin

lift_definition less_zhmultiset :: "zhmultiset \<Rightarrow> zhmultiset \<Rightarrow> bool" is "(<)" .
lift_definition less_eq_zhmultiset :: "zhmultiset \<Rightarrow> zhmultiset \<Rightarrow> bool" is "(\<le>)" .

instance
  by (intro_classes; transfer) auto

end

lemmas ZHMSet_less[simp] = less_zhmultiset.abs_eq
lemmas ZHMSet_le[simp] = less_eq_zhmultiset.abs_eq
lemmas zhmsetmset_less[simp] = less_zhmultiset.rep_eq[symmetric]
lemmas zhmsetmset_le[simp] = less_eq_zhmultiset.rep_eq[symmetric]


subsection \<open>Embedding and Projections of Syntactic Ordinals\<close>

abbreviation zhmset_of :: "hmultiset \<Rightarrow> zhmultiset" where
  "zhmset_of M \<equiv> ZHMSet (zmset_of (hmsetmset M))"

lemma zhmset_of_inject[simp]: "zhmset_of M = zhmset_of N \<longleftrightarrow> M = N"
  by simp

lemma zhmset_of_less: "zhmset_of M < zhmset_of N \<longleftrightarrow> M < N"
  by (simp add: zmset_of_less)

lemma zhmset_of_le: "zhmset_of M \<le> zhmset_of N \<longleftrightarrow> M \<le> N"
  by (simp add: zmset_of_le)

abbreviation hmset_pos :: "zhmultiset \<Rightarrow> hmultiset" where
  "hmset_pos M \<equiv> HMSet (mset_pos (zhmsetmset M))"

abbreviation hmset_neg :: "zhmultiset \<Rightarrow> hmultiset" where
  "hmset_neg M \<equiv> HMSet (mset_neg (zhmsetmset M))"


subsection \<open>Disjoint Union and Difference\<close>

instantiation zhmultiset :: cancel_comm_monoid_add
begin

lift_definition zero_zhmultiset :: zhmultiset is "{#}\<^sub>z" .

lift_definition plus_zhmultiset :: "zhmultiset \<Rightarrow> zhmultiset \<Rightarrow> zhmultiset" is
  "\<lambda>A B. A + B" .

lift_definition minus_zhmultiset :: "zhmultiset \<Rightarrow> zhmultiset \<Rightarrow> zhmultiset" is
  "\<lambda>A B. A - B" .

lemmas ZHMSet_plus = plus_zhmultiset.abs_eq[symmetric]
lemmas ZHMSet_diff = minus_zhmultiset.abs_eq[symmetric]
lemmas zhmsetmset_plus = plus_zhmultiset.rep_eq
lemmas zhmsetmset_diff = minus_zhmultiset.rep_eq

lemma zhmset_of_plus: "zhmset_of (A + B) = zhmset_of A + zhmset_of B"
  by (simp add: hmsetmset_plus ZHMSet_plus zmset_of_plus)

lemma hmsetmset_0[simp]: "hmsetmset 0 = {#}"
  by (rule hmultiset.inject[THEN iffD1]) (simp add: zero_hmultiset_def)

instance
  by (intro_classes; transfer) (auto intro: mult.assoc add.commute)

end

lemma zhmset_of_0: "zhmset_of 0 = 0"
  by (simp add: zero_zhmultiset_def)

lemma hmset_pos_plus:
  "hmset_pos (A + B) = (hmset_pos A - hmset_neg B) + (hmset_pos B - hmset_neg A)"
  by (simp add: HMSet_diff HMSet_plus zhmsetmset_plus)

lemma hmset_neg_plus:
  "hmset_neg (A + B) = (hmset_neg A - hmset_pos B) + (hmset_neg B - hmset_pos A)"
  by (simp add: HMSet_diff HMSet_plus zhmsetmset_plus)

lemma zhmset_pos_neg_partition: "M = zhmset_of (hmset_pos M) - zhmset_of (hmset_neg M)"
  by (cases M, simp add: ZHMSet_diff[symmetric], rule mset_pos_neg_partition)

lemma zhmset_pos_as_neg: "zhmset_of (hmset_pos M) = zhmset_of (hmset_neg M) + M"
  using mset_pos_as_neg zhmsetmset_plus zhmsetmset_inject by fastforce

lemma zhmset_neg_as_pos: "zhmset_of (hmset_neg M) = zhmset_of (hmset_pos M) - M"
  using zhmsetmset_diff mset_neg_as_pos zhmsetmset_inject by fastforce

lemma hmset_pos_neg_dual:
  "hmset_pos a + hmset_pos b + (hmset_neg a - hmset_pos b) + (hmset_neg b - hmset_pos a) =
   hmset_neg a + hmset_neg b + (hmset_pos a - hmset_neg b) + (hmset_pos b - hmset_neg a)"
  by (simp add: HMSet_plus[symmetric] HMSet_diff[symmetric]) (rule mset_pos_neg_dual)

lemma zhmset_of_sum_list: "zhmset_of (sum_list Ms) = sum_list (map zhmset_of Ms)"
  by (induct Ms) (auto simp: zero_zhmultiset_def zhmset_of_plus)

lemma less_hmset_zhmsetE:
  assumes m_lt_n: "M < N"
  obtains A B C where "M = zhmset_of A + C" and "N = zhmset_of B + C" and "A < B"
  by (rule less_mset_zmsetE[OF m_lt_n[folded zhmsetmset_less]])
    (metis hmsetmset_less hmultiset.sel ZHMSet_plus zhmsetmset_inverse)

lemma less_eq_hmset_zhmsetE:
  assumes m_le_n: "M \<le> N"
  obtains A B C where "M = zhmset_of A + C" and "N = zhmset_of B + C" and "A \<le> B"
  by (rule less_eq_mset_zmsetE[OF m_le_n[folded zhmsetmset_le]])
    (metis hmsetmset_le hmultiset.sel ZHMSet_plus zhmsetmset_inverse)

instantiation zhmultiset :: ab_group_add
begin

lift_definition uminus_zhmultiset :: "zhmultiset \<Rightarrow> zhmultiset" is "\<lambda>A. - A" .

lemmas ZHMSet_uminus = uminus_zhmultiset.abs_eq[symmetric]
lemmas zhmsetmset_uminus = uminus_zhmultiset.rep_eq

instance
  by (intro_classes; transfer; simp)

end


subsection \<open>Infimum and Supremum\<close>

instance zhmultiset :: ordered_cancel_comm_monoid_add
  by (intro_classes; transfer) (auto simp: add_left_mono)

instance zhmultiset :: ordered_ab_group_add
  by (intro_classes; transfer; simp)

instantiation zhmultiset :: distrib_lattice
begin

definition inf_zhmultiset :: "zhmultiset \<Rightarrow> zhmultiset \<Rightarrow> zhmultiset" where
  "inf_zhmultiset A B = (if A < B then A else B)"

definition sup_zhmultiset :: "zhmultiset \<Rightarrow> zhmultiset \<Rightarrow> zhmultiset" where
  "sup_zhmultiset A B = (if B > A then B else A)"

instance
  by intro_classes (auto simp: inf_zhmultiset_def sup_zhmultiset_def)

end

end
