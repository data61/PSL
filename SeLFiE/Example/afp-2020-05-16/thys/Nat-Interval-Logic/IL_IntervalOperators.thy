(*  Title:      IL_IntOperator.thy
    Date:       Jan 2007
    Author:     David Trachtenherz
*)

section \<open>Arithmetic operators on natural intervals\<close>

theory IL_IntervalOperators
imports IL_Interval
begin


subsection \<open>Arithmetic operations with intervals\<close>

subsubsection \<open>Addition of and multiplication by constants\<close>

definition iT_Plus :: "iT \<Rightarrow> Time \<Rightarrow> iT" (infixl "\<oplus>" 55)
  where "I \<oplus> k \<equiv> (\<lambda>n.(n + k)) ` I"

definition iT_Mult :: "iT \<Rightarrow> Time \<Rightarrow> iT" (infixl "\<otimes>" 55)
  where iT_Mult_def : "I \<otimes> k \<equiv> (\<lambda>n.(n * k)) ` I"

(*<*)
(* Some examples *)
(*
lemma "[\<dots>10]\<oplus>5 = {5..15}"
apply (simp only: iIN_0_iTILL_conv[symmetric])
apply (simp add: iT_defs)
apply (simp add: iT_Plus_def)
apply (simp add: image_add_atLeastAtMost)
done

lemma "[1\<dots>,2] = {1,2,3}"
apply (simp add: iIN_def)
apply fastforce
done

lemma "[1\<dots>,2]\<otimes>2 = {2,4,6}"
apply (simp add: iT_Mult_def iIN_def)
apply auto
done
lemma "[10\<dots>]\<otimes>k = {x*k | x. 10 \<le> x}"
apply (simp add: iFROM_def iT_Mult_def)
by blast

lemma "[\<dots>4] \<otimes> 10 = {0, 10, 20, 30, 40}"
apply (simp add: iT_Mult_def iTILL_def)
by auto
lemma "[\<dots>4] \<otimes> 10 \<oplus> 2 = {2, 12, 22, 32, 42}"
apply (simp add: iT_Plus_def iT_Mult_def iTILL_def)
by auto
*)
(*>*)

lemma iT_Plus_image_conv: "I \<oplus> k = (\<lambda>n.(n + k)) ` I"
by (simp add:  iT_Plus_def)

lemma iT_Mult_image_conv: "I \<otimes> k = (\<lambda>n.(n * k)) ` I"
by (simp add:  iT_Mult_def)

lemma iT_Plus_empty: "{} \<oplus> k = {}"
by (simp add: iT_Plus_def)

lemma iT_Mult_empty: "{} \<otimes> k = {}"
by (simp add: iT_Mult_def)

lemma iT_Plus_not_empty: "I \<noteq> {} \<Longrightarrow> I \<oplus> k \<noteq> {}"
by (simp add: iT_Plus_def)

lemma iT_Mult_not_empty: "I \<noteq> {} \<Longrightarrow> I \<otimes> k \<noteq> {}"
by (simp add: iT_Mult_def)


lemma iT_Plus_empty_iff: "(I \<oplus> k = {}) = (I = {})"
by (simp add: iT_Plus_def)

lemma iT_Mult_empty_iff: "(I \<otimes> k = {}) = (I = {})"
by (simp add: iT_Mult_def)

lemma iT_Plus_mono: "A \<subseteq> B \<Longrightarrow> A \<oplus> k \<subseteq> B \<oplus> k"
by (simp add: iT_Plus_def image_mono)

lemma iT_Mult_mono: "A \<subseteq> B \<Longrightarrow> A \<otimes> k \<subseteq> B \<otimes> k"
by (simp add: iT_Mult_def image_mono)


lemma iT_Mult_0: "I \<noteq> {} \<Longrightarrow> I \<otimes> 0 = [\<dots>0]"
by (fastforce simp add: iTILL_def iT_Mult_def)

corollary iT_Mult_0_if: "I \<otimes> 0 = (if I = {} then {} else [\<dots>0])"
by (simp add: iT_Mult_empty iT_Mult_0)


lemma iT_Plus_mem_iff: "x \<in> (I \<oplus> k) = (k \<le> x \<and> (x - k) \<in> I)"
apply (simp add: iT_Plus_def image_iff)
apply (rule iffI)
 apply fastforce
apply (rule_tac x="x - k" in bexI, simp+)
done

lemma iT_Plus_mem_iff2: "x + k \<in> (I \<oplus> k) = (x \<in> I)"
by (simp add: iT_Plus_def image_iff)

lemma iT_Mult_mem_iff_0: "x \<in> (I \<otimes> 0) = (I \<noteq> {} \<and> x = 0)"
apply (case_tac "I = {}")
 apply (simp add: iT_Mult_empty)
apply (simp add: iT_Mult_0 iT_iff)
done

lemma iT_Mult_mem_iff: " 
  0 < k \<Longrightarrow> x \<in> (I \<otimes> k) = (x mod k = 0 \<and> x div k \<in> I)"
by (fastforce simp: iT_Mult_def image_iff)

lemma iT_Mult_mem_iff2: "0 < k \<Longrightarrow> x * k \<in> (I \<otimes> k) = (x \<in> I)"
by (simp add: iT_Mult_def image_iff)

lemma iT_Plus_singleton: "{a} \<oplus> k = {a + k}"
by (simp add: iT_Plus_def)

lemma iT_Mult_singleton: "{a} \<otimes> k = {a * k}"
by (simp add: iT_Mult_def)


lemma iT_Plus_Un: "(A \<union> B) \<oplus> k = (A \<oplus> k) \<union> (B \<oplus> k)"
by (simp add: iT_Plus_def image_Un)

lemma iT_Mult_Un: "(A \<union> B) \<otimes> k = (A \<otimes> k) \<union> (B \<otimes> k)"
by (simp add: iT_Mult_def image_Un)

lemma iT_Plus_Int: "(A \<inter> B) \<oplus> k = (A \<oplus> k) \<inter> (B \<oplus> k)"
by (simp add: iT_Plus_def image_Int)

lemma iT_Mult_Int: "0 < k \<Longrightarrow> (A \<inter> B) \<otimes> k = (A \<otimes> k) \<inter> (B \<otimes> k)"
by (simp add: iT_Mult_def image_Int mult_right_inj)

lemma iT_Plus_image: "f ` I \<oplus> n = (\<lambda>x. f x + n) ` I"
by (fastforce simp: iT_Plus_def)

lemma iT_Mult_image: "f ` I \<otimes> n = (\<lambda>x. f x * n) ` I"
by (fastforce simp: iT_Mult_def)

lemma iT_Plus_commute: "I \<oplus> a \<oplus> b = I \<oplus> b \<oplus> a"
by (fastforce simp: iT_Plus_def)

lemma iT_Mult_commute: "I \<otimes> a \<otimes> b = I \<otimes> b \<otimes> a"
by (fastforce simp: iT_Mult_def)

lemma iT_Plus_assoc:"I \<oplus> a \<oplus> b = I \<oplus> (a + b)"
by (fastforce simp: iT_Plus_def)

lemma iT_Mult_assoc:"I \<otimes> a \<otimes> b = I \<otimes> (a * b)"
by (fastforce simp: iT_Mult_def)

lemma iT_Plus_Mult_distrib: "I \<oplus> n \<otimes> m = I \<otimes> m \<oplus> n * m"
by (simp add: iT_Plus_def iT_Mult_def image_image add_mult_distrib)


(*<*)
lemma "i \<otimes> n1 \<otimes> n2 \<otimes> n3 \<otimes> n4 \<otimes> n5 \<otimes> n6 \<otimes> n7 =  
  i \<otimes> n1 * n2 * n3 * n4 * n5 * n6 * n7"
by (simp add: iT_Mult_assoc)
lemma "i \<oplus> n1 \<oplus> n2 \<oplus> n3 \<oplus> n4 \<oplus> n5 = i \<oplus> n1 + n2 + n3 + n4 + n5"
by (simp add: iT_Plus_assoc)
lemma "i \<oplus> n1 \<otimes> m \<oplus> n2 = i \<otimes> m \<oplus> n1 * m + n2"
by (simp add: iT_Plus_assoc iT_Plus_Mult_distrib)
lemma "i \<oplus> n1 \<otimes> m1 \<otimes> m2 \<oplus> n2 = i \<otimes> m1 * m2 \<oplus> n1 * m1 * m2 + n2"
by (simp add: iT_Plus_assoc iT_Mult_assoc iT_Plus_Mult_distrib)

lemma "n \<in> I \<oplus> k \<Longrightarrow> k \<le> n"
by (clarsimp simp add: iT_Plus_def)
(*>*)

lemma iT_Plus_finite_iff: "finite (I \<oplus> k) = finite I"
by (simp add: iT_Plus_def inj_on_finite_image_iff)

lemma iT_Mult_0_finite: "finite (I \<otimes> 0)"
by (simp add: iT_Mult_0_if iTILL_0)

lemma iT_Mult_finite_iff: "0 < k \<Longrightarrow> finite (I \<otimes> k) = finite I"
by (simp add: iT_Mult_def inj_on_finite_image_iff[OF inj_imp_inj_on] mult_right_inj)

lemma iT_Plus_Min: "I \<noteq> {} \<Longrightarrow> iMin (I \<oplus> k) = iMin I + k"
by (simp add: iT_Plus_def iMin_mono2 mono_def)

lemma iT_Mult_Min: "I \<noteq> {} \<Longrightarrow> iMin (I \<otimes> k) = iMin I * k"
by (simp add: iT_Mult_def iMin_mono2 mono_def)

lemma iT_Plus_Max: "\<lbrakk> finite I; I \<noteq> {} \<rbrakk> \<Longrightarrow> Max (I \<oplus> k) = Max I + k"
by (simp add: iT_Plus_def Max_mono2 mono_def)

lemma iT_Mult_Max: "\<lbrakk> finite I; I \<noteq> {} \<rbrakk> \<Longrightarrow> Max (I \<otimes> k) = Max I * k"
by (simp add: iT_Mult_def Max_mono2 mono_def)

corollary 
  iMOD_mult_0: "[r, mod m] \<otimes> 0 = [\<dots>0]" and
  iMODb_mult_0: "[r, mod m, c] \<otimes> 0 = [\<dots>0]" and
  iFROM_mult_0: "[n\<dots>] \<otimes> 0 = [\<dots>0]" and
  iIN_mult_0: "[n\<dots>,d] \<otimes> 0 = [\<dots>0]" and
  iTILL_mult_0: "[\<dots>n] \<otimes> 0 = [\<dots>0]"
by (simp add: iT_not_empty iT_Mult_0)+

lemmas iT_mult_0 =
  iTILL_mult_0
  iFROM_mult_0
  iIN_mult_0
  iMOD_mult_0
  iMODb_mult_0

lemma iT_Plus_0: "I \<oplus> 0 = I"
by (simp add: iT_Plus_def)

lemma iT_Mult_1: "I \<otimes> Suc 0 = I"
by (simp add: iT_Mult_def)

corollary 
  iFROM_add_Min: "iMin ([n\<dots>] \<oplus> k) = n + k" and
  iIN_add_Min:   "iMin ([n\<dots>,d] \<oplus> k) = n + k" and
  iTILL_add_Min: "iMin ([\<dots>n] \<oplus> k) = k" and
  iMOD_add_Min:  "iMin ([r, mod m] \<oplus> k) = r + k" and
  iMODb_add_Min: "iMin ([r, mod m, c] \<oplus> k) = r + k"
by (simp add: iT_not_empty iT_Plus_Min iT_Min)+

corollary 
  iFROM_mult_Min: "iMin ([n\<dots>] \<otimes> k) = n * k" and
  iIN_mult_Min:   "iMin ([n\<dots>,d] \<otimes> k) = n * k" and
  iTILL_mult_Min: "iMin ([\<dots>n] \<otimes> k) = 0" and
  iMOD_mult_Min:  "iMin ([r, mod m] \<otimes> k) = r * k" and
  iMODb_mult_Min: "iMin ([r, mod m, c] \<otimes> k) = r * k"
by (simp add: iT_not_empty iT_Mult_Min iT_Min)+


lemmas iT_add_Min = 
  iIN_add_Min
  iTILL_add_Min
  iFROM_add_Min
  iMOD_add_Min
  iMODb_add_Min

lemmas iT_mult_Min = 
  iIN_mult_Min
  iTILL_mult_Min
  iFROM_mult_Min
  iMOD_mult_Min
  iMODb_mult_Min


lemma iFROM_add: "[n\<dots>] \<oplus> k = [n+k\<dots>]"
by (simp add: iFROM_def iT_Plus_def image_add_atLeast)

lemma iIN_add: "[n\<dots>,d] \<oplus> k = [n+k\<dots>,d]"
by (fastforce simp add: iIN_def iT_Plus_def)

lemma iTILL_add: "[\<dots>i] \<oplus> k = [k\<dots>,i]"
by (simp add: iIN_0_iTILL_conv[symmetric] iIN_add)

lemma iMOD_add: "[r, mod m] \<oplus> k = [r + k, mod m]"
apply (clarsimp simp: set_eq_iff iMOD_def iT_Plus_def image_iff)
apply (rule iffI)
 apply (clarsimp simp: mod_add)
apply (rule_tac x="x - k" in exI)
apply clarsimp
apply (simp add: mod_sub_add)
done

lemma iMODb_add: "[r, mod m, c] \<oplus> k = [r + k, mod m, c]"
by (simp add: iMODb_iMOD_iIN_conv iT_Plus_Int iMOD_add iIN_add)

lemmas iT_add =
  iMOD_add 
  iMODb_add
  iFROM_add
  iIN_add
  iTILL_add
  iT_Plus_singleton

lemma iFROM_mult: "[n\<dots>] \<otimes> k = [ n * k, mod k ]"
apply (case_tac "k = 0")
 apply (simp add: iMOD_0 iT_mult_0 iIN_0 iTILL_0)
apply (clarsimp simp: set_eq_iff iT_Mult_mem_iff iT_iff)
apply (rule conj_cong, simp)
apply (rule iffI)
 apply (drule mult_le_mono1[of _ _ k])
 apply (rule order_trans, assumption)
 apply (simp add: div_mult_cancel)
apply (drule div_le_mono[of _ _ k])
apply simp
done

lemma iIN_mult: "[n\<dots>,d] \<otimes> k = [ n * k, mod k, d ]"
apply (case_tac "k = 0")
 apply (simp add: iMODb_mod_0 iT_mult_0 iIN_0 iTILL_0)
apply (clarsimp simp: set_eq_iff iT_Mult_mem_iff iT_iff)
apply (rule conj_cong, simp)
apply (rule iffI)
 apply (elim conjE)
 apply (drule mult_le_mono1[of _ _ k], drule mult_le_mono1[of _ _ k])
 apply (rule conjI)
  apply (rule order_trans, assumption)
  apply (simp add: div_mult_cancel)
 apply (simp add: div_mult_cancel add_mult_distrib mult.commute[of k])
apply (erule conjE)
apply (drule div_le_mono[of _ _ k], drule div_le_mono[of _ _ k])
apply simp
done

lemma iTILL_mult: "[\<dots>n] \<otimes> k = [ 0, mod k, n ]"
by (simp add: iIN_0_iTILL_conv[symmetric] iIN_mult)


lemma iMOD_mult: "[r, mod m ] \<otimes> k = [ r * k, mod m * k ]"
apply (case_tac "k = 0")
 apply (simp add: iMOD_0 iT_mult_0 iIN_0 iTILL_0)
apply (clarsimp simp: set_eq_iff iT_Mult_mem_iff iT_iff)
apply (subst mult.commute[of m k])
apply (simp add: mod_mult2_eq)
apply (rule iffI)
 apply (elim conjE)
 apply (drule mult_le_mono1[of _ _ k])
 apply (simp add: div_mult_cancel)
apply (elim conjE)
apply (subgoal_tac "x mod k = 0")
 prefer 2
 apply (drule_tac arg_cong[where f="\<lambda>x. x mod k"])
 apply (simp add: mult.commute[of k])
apply (drule div_le_mono[of _ _ k])
apply simp
done

lemma iMODb_mult: "
  [r, mod m, c ] \<otimes> k = [ r * k, mod m * k, c ]"
apply (case_tac "k = 0")
 apply (simp add: iMODb_mod_0 iT_mult_0 iIN_0 iTILL_0)
apply (subst iMODb_iMOD_iTILL_conv)
apply (simp add: iT_Mult_Int iMOD_mult iTILL_mult iMODb_iMOD_iTILL_conv)
apply (subst Int_assoc[symmetric])
apply (subst Int_absorb2)
 apply (simp add: iMOD_subset)
apply (simp add: iMOD_iTILL_iMODb_conv add_mult_distrib2)
done

lemmas iT_mult =
  iTILL_mult
  iFROM_mult
  iIN_mult
  iMOD_mult
  iMODb_mult
  iT_Mult_singleton


subsubsection \<open>Some conversions between intervals using constant addition and multiplication\<close>

lemma iFROM_conv: "[n\<dots>] = UNIV \<oplus> n"
by (simp add: iFROM_0[symmetric] iFROM_add)

lemma iIN_conv: "[n\<dots>,d] = [\<dots>d] \<oplus> n"
by (simp add: iTILL_add)

lemma iMOD_conv: "[r, mod m] = [0\<dots>] \<otimes> m \<oplus> r"
apply (case_tac "m = 0")
 apply (simp add: iMOD_0 iT_mult_0 iTILL_add)
apply (simp add: iFROM_mult iMOD_add)
done

lemma iMODb_conv: "[r, mod m, c] = [\<dots>c] \<otimes> m \<oplus> r" 
apply (case_tac "m = 0")
 apply (simp add: iMODb_mod_0 iT_mult_0 iTILL_add)
apply (simp add: iTILL_mult iMODb_add)
done


text \<open>Some examples showing the utility of iMODb\_conv\<close>
lemma "[12, mod 10, 4] = {12, 22, 32, 42, 52}"
apply (simp add: iT_defs)
apply safe
defer 1
apply simp+
txt \<open>The direct proof without iMODb\_conv fails\<close>
oops

lemma "[12, mod 10, 4] = {12, 22, 32, 42, 52}"
apply (simp only: iMODb_conv)
apply (simp add: iT_defs iT_Mult_def iT_Plus_def)
apply safe
apply simp+
done

lemma "[12, mod 10, 4] = {12, 22, 32, 42, 52}"
apply (simp only: iMODb_conv)
apply (simp add: iT_defs iT_Mult_def iT_Plus_def)
apply (simp add: atMost_def)
apply safe
apply simp+
done

lemma "[r, mod m, 4] = {r, r+m, r+2*m, r+3*m, r+4*m}"
apply (simp only: iMODb_conv)
apply (simp add: iT_defs iT_Mult_def iT_Plus_def atMost_def)
apply (simp add: image_Collect)
apply safe
apply fastforce+
done

lemma "[2, mod 10, 4] = {2, 12, 22, 32, 42}"
apply (simp only: iMODb_conv)
apply (simp add: iT_defs iT_Plus_def iT_Mult_def)
apply fastforce
done


subsubsection \<open>Subtraction of constants\<close>

definition iT_Plus_neg :: "iT \<Rightarrow> Time \<Rightarrow> iT" (infixl "\<oplus>-" 55) where
  "I \<oplus>- k \<equiv> {x. x + k \<in> I}"

lemma iT_Plus_neg_mem_iff: "(x \<in> I \<oplus>- k) = (x + k \<in> I)"
by (simp add: iT_Plus_neg_def)

lemma iT_Plus_neg_mem_iff2: "k \<le> x \<Longrightarrow> (x - k \<in> I \<oplus>- k) = (x \<in> I)"
by (simp add: iT_Plus_neg_def)

lemma iT_Plus_neg_image_conv: "I \<oplus>- k = (\<lambda>n.(n - k)) ` (I \<down>\<ge> k)"
apply (simp add: iT_Plus_neg_def cut_ge_def, safe)
apply (rule_tac x="x+k" in image_eqI)
apply simp+
done

lemma iT_Plus_neg_cut_eq: "t \<le> k \<Longrightarrow> (I \<down>\<ge> t) \<oplus>- k = I \<oplus>- k"
by (simp add: set_eq_iff iT_Plus_neg_mem_iff cut_ge_mem_iff)

lemma iT_Plus_neg_mono: "A \<subseteq> B \<Longrightarrow> A \<oplus>- k \<subseteq> B \<oplus>- k"
by (simp add: iT_Plus_neg_def subset_iff)

lemma iT_Plus_neg_empty: "{} \<oplus>- k = {}"
by (simp add: iT_Plus_neg_def)
lemma iT_Plus_neg_Max_less_empty: "
  \<lbrakk> finite I; Max I < k \<rbrakk> \<Longrightarrow> I \<oplus>- k = {}"
by (simp add: iT_Plus_neg_image_conv cut_ge_Max_empty)

lemma iT_Plus_neg_not_empty_iff: "(I \<oplus>- k \<noteq> {}) = (\<exists>x\<in>I. k \<le> x)"
by (simp add: iT_Plus_neg_image_conv cut_ge_not_empty_iff)

lemma iT_Plus_neg_empty_iff: "
  (I \<oplus>- k = {}) = (I = {} \<or> (finite I \<and> Max I < k))"
apply (case_tac "I = {}")
 apply (simp add: iT_Plus_neg_empty)
apply (simp add: iT_Plus_neg_image_conv)
apply (case_tac "infinite I")
 apply (simp add: nat_cut_ge_infinite_not_empty)
apply (simp add: cut_ge_empty_iff)
done

lemma iT_Plus_neg_assoc: "(I \<oplus>- a) \<oplus>- b = I \<oplus>- (a + b)"
apply (simp add: iT_Plus_neg_def)
apply (simp add: add.assoc add.commute[of b])
done

lemma iT_Plus_neg_commute: "I \<oplus>- a \<oplus>- b = I \<oplus>- b \<oplus>- a"
by (simp add: iT_Plus_neg_assoc add.commute[of b])

lemma iT_Plus_neg_0: "I \<oplus>- 0 = I"
by (simp add: iT_Plus_neg_image_conv cut_ge_0_all)

lemma iT_Plus_Plus_neg_assoc: "b \<le> a \<Longrightarrow> I \<oplus> a \<oplus>- b = I \<oplus> (a - b)"
apply (simp add: iT_Plus_neg_image_conv)
apply (clarsimp simp add: set_eq_iff image_iff Bex_def cut_ge_mem_iff iT_Plus_mem_iff)
apply (rule iffI)
 apply fastforce
apply (rule_tac x="x + b" in exI)
apply (simp add: le_diff_conv)
done

lemma iT_Plus_Plus_neg_assoc2: "a \<le> b \<Longrightarrow> I \<oplus> a \<oplus>- b = I \<oplus>- (b - a)"
apply (simp add: iT_Plus_neg_image_conv)
apply (clarsimp simp add: set_eq_iff image_iff Bex_def cut_ge_mem_iff iT_Plus_mem_iff)
apply (rule iffI)
 apply fastforce
apply (clarify, rename_tac x')
apply (rule_tac x="x' + a" in exI)
apply simp
done

lemma iT_Plus_neg_Plus_le_cut_eq: "
  a \<le> b \<Longrightarrow> (I \<oplus>- a) \<oplus> b = (I \<down>\<ge> a) \<oplus> (b - a)"
apply (simp add: iT_Plus_neg_image_conv)
apply (clarsimp simp add: set_eq_iff image_iff Bex_def cut_ge_mem_iff iT_Plus_mem_iff)
apply (rule iffI)
 apply (clarify, rename_tac x')
 apply (subgoal_tac "x' = x + a - b")
  prefer 2
  apply simp
 apply (simp add: le_imp_diff_le le_add_diff)
apply fastforce 
done

corollary iT_Plus_neg_Plus_le_Min_eq: "
  \<lbrakk> a \<le> b; a \<le> iMin I \<rbrakk> \<Longrightarrow> (I \<oplus>- a) \<oplus> b = I \<oplus> (b - a)"
by (simp add: iT_Plus_neg_Plus_le_cut_eq cut_ge_Min_all)

lemma iT_Plus_neg_Plus_ge_cut_eq: "
  b \<le> a \<Longrightarrow> (I \<oplus>- a) \<oplus> b = (I \<down>\<ge> a) \<oplus>- (a - b)"
apply (simp add: iT_Plus_neg_image_conv iT_Plus_def cut_cut_ge max_eqL)
apply (subst image_comp)
apply (rule image_cong, simp)
apply (simp add: cut_ge_mem_iff)
done

corollary iT_Plus_neg_Plus_ge_Min_eq: "
  \<lbrakk> b \<le> a; a \<le> iMin I \<rbrakk> \<Longrightarrow> (I \<oplus>- a) \<oplus> b = I \<oplus>- (a - b)"
by (simp add: iT_Plus_neg_Plus_ge_cut_eq cut_ge_Min_all)

lemma iT_Plus_neg_Mult_distrib: "
  0 < m \<Longrightarrow> I \<oplus>- n \<otimes> m = I \<otimes> m \<oplus>- n * m"
apply (clarsimp simp: set_eq_iff iT_Plus_neg_image_conv image_iff iT_Plus_def iT_Mult_def Bex_def cut_ge_mem_iff)
apply (rule iffI)
 apply (clarsimp, rename_tac x')
 apply (rule_tac x="x' * m" in exI)
 apply (simp add: diff_mult_distrib)
apply (clarsimp, rename_tac x')
apply (rule_tac x="x' - n" in exI)
apply (simp add: diff_mult_distrib)
apply fastforce
done

lemma iT_Plus_neg_Plus_le_inverse: "k \<le> iMin I \<Longrightarrow> I \<oplus>- k \<oplus> k = I"
by (simp add: iT_Plus_neg_Plus_le_Min_eq iT_Plus_0)

lemma iT_Plus_neg_Plus_inverse: "I \<oplus>- k \<oplus> k = I \<down>\<ge> k"
by (simp add: iT_Plus_neg_Plus_ge_cut_eq iT_Plus_neg_0)

lemma iT_Plus_Plus_neg_inverse: "I \<oplus> k \<oplus>- k = I"
by (simp add: iT_Plus_Plus_neg_assoc iT_Plus_0)


lemma iT_Plus_neg_Un: "(A \<union> B) \<oplus>- k = (A \<oplus>- k) \<union> (B \<oplus>- k)"
by (fastforce simp: iT_Plus_neg_def)

lemma iT_Plus_neg_Int: "(A \<inter> B) \<oplus>- k = (A \<oplus>- k) \<inter> (B \<oplus>- k)"
by (fastforce simp: iT_Plus_neg_def)

lemma iT_Plus_neg_Max_singleton: "\<lbrakk> finite I; I \<noteq> {} \<rbrakk> \<Longrightarrow> I \<oplus>- Max I= {0}"
apply (rule set_eqI)
apply (simp add: iT_Plus_neg_def)
apply (case_tac "x = 0")
 apply simp
apply fastforce
done

lemma iT_Plus_neg_singleton: "{a} \<oplus>- k = (if k \<le> a then {a - k} else {})"
by (force simp add: set_eq_iff iT_Plus_neg_mem_iff singleton_iff)

corollary iT_Plus_neg_singleton1: "k \<le> a \<Longrightarrow> {a} \<oplus>- k = {a-k}"
by (simp add: iT_Plus_neg_singleton)

corollary iT_Plus_neg_singleton2: "a < k \<Longrightarrow> {a} \<oplus>- k= {}"
by (simp add: iT_Plus_neg_singleton)

lemma iT_Plus_neg_finite_iff: "finite (I \<oplus>- k) = finite I"
  apply (simp add: iT_Plus_neg_image_conv)
  apply (subst inj_on_finite_image_iff)
  apply (metis cut_geE inj_on_diff_nat)
  apply (simp add: nat_cut_ge_finite_iff)
  done

lemma iT_Plus_neg_Min: "
  I \<oplus>- k \<noteq> {} \<Longrightarrow> iMin (I \<oplus>- k) = iMin (I \<down>\<ge> k) - k"
apply (simp add: iT_Plus_neg_image_conv)
apply (simp add: iMin_mono2 monoI)
done

lemma iT_Plus_neg_Max: "
  \<lbrakk> finite I; I \<oplus>- k \<noteq> {} \<rbrakk> \<Longrightarrow> Max (I \<oplus>- k) = Max I - k"
apply (simp add: iT_Plus_neg_image_conv)
apply (simp add: Max_mono2 monoI cut_ge_finite cut_ge_Max_eq)
done


text \<open>Subtractions of constants from intervals\<close>

lemma iFROM_add_neg: "[n\<dots>] \<oplus>- k = [n - k\<dots>]"
by (fastforce simp: set_eq_iff iT_Plus_neg_mem_iff)

lemma iTILL_add_neg: "[\<dots>n] \<oplus>- k = (if k \<le> n then [\<dots>n - k] else {})"
by (force simp add: set_eq_iff iT_Plus_neg_mem_iff iT_iff)
lemma iTILL_add_neg1: "k \<le> n \<Longrightarrow> [\<dots>n] \<oplus>- k = [\<dots>n-k]"
by (simp add: iTILL_add_neg)
lemma iTILL_add_neg2: "n < k \<Longrightarrow> [\<dots>n] \<oplus>- k = {}"
by (simp add: iTILL_add_neg)

lemma iIN_add_neg: "
  [n\<dots>,d] \<oplus>- k = (
    if k \<le> n then [n - k\<dots>,d] 
    else if k \<le> n + d then [\<dots>n + d - k] else {})"
by (simp add: iIN_iFROM_iTILL_conv iT_Plus_neg_Int iFROM_add_neg iTILL_add_neg iFROM_0)

lemma iIN_add_neg1: "k \<le> n \<Longrightarrow> [n\<dots>,d] \<oplus>- k = [n - k\<dots>,d]"
by (simp add: iIN_add_neg)

lemma iIN_add_neg2: "\<lbrakk> n \<le> k; k \<le> n + d \<rbrakk> \<Longrightarrow> [n\<dots>,d] \<oplus>- k = [\<dots>n + d - k]"
by (simp add: iIN_add_neg iIN_0_iTILL_conv)

lemma iIN_add_neg3: "n + d < k \<Longrightarrow> [n\<dots>,d] \<oplus>- k = {}"
by (simp add: iT_Plus_neg_Max_less_empty iT_finite iT_Max)

lemma iMOD_0_add_neg: "[r, mod 0] \<oplus>- k = {r} \<oplus>- k"
by (simp add: iMOD_0 iIN_0)

(*
lemma "[25, mod 10] \<oplus>- 32 = [3, mod 10]"
apply (rule set_eqI)
apply (simp add: iT_Plus_neg_mem_iff iMOD_iff)
apply (simp add: mod_add_eq[of _ 32] mod_Suc)
apply clarify
apply (rule iffI)
apply simp+
done
*)

lemma iMOD_gr0_add_neg: "
  0 < m \<Longrightarrow> 
  [r, mod m] \<oplus>- k = (
    if k \<le> r then [r - k, mod m] 
    else [(m + r mod m - k mod m) mod m, mod m])"
apply (rule set_eqI)
apply (simp add: iMOD_def iT_Plus_neg_def)
apply (simp add: eq_sym_conv[of _ "r mod m"])
apply (intro conjI impI)
 apply (simp add: eq_sym_conv[of _ "(r - k) mod m"] mod_sub_add le_diff_conv)
apply (simp add: eq_commute[of "r mod m"] mod_add_eq_mod_conv)
apply safe
apply (drule sym)
apply simp
done

lemma iMOD_add_neg: "
  [r, mod m] \<oplus>- k = (
    if k \<le> r then [r - k, mod m] 
    else if 0 < m then [(m + r mod m - k mod m) mod m, mod m] else {})"
apply (case_tac "0 < m")
 apply (simp add: iMOD_gr0_add_neg)
apply (simp add: iMOD_0 iIN_0 iT_Plus_neg_singleton)
done

corollary iMOD_add_neg1: "
  k \<le> r \<Longrightarrow> [r, mod m] \<oplus>- k = [r - k, mod m]"
by (simp add: iMOD_add_neg)

lemma iMOD_add_neg2: "
  \<lbrakk> 0 < m; r < k \<rbrakk> \<Longrightarrow> [r, mod m] \<oplus>- k = [(m + r mod m - k mod m) mod m, mod m]"
by (simp add: iMOD_add_neg)


lemma iMODb_mod_0_add_neg: "[r, mod 0, c] \<oplus>- k = {r} \<oplus>- k"
by (simp add: iMODb_mod_0 iIN_0)

(*
lemma "[25, mod 10, 5] \<oplus>- 32 = [3, mod 10, 4]"
apply (rule set_eqI)
apply (simp add: iMODb_conv iT_Plus_neg_mem_iff iT_Plus_mem_iff iT_Mult_mem_iff)
apply (case_tac "x < 3", simp)
apply (simp add: linorder_not_less)
apply (rule_tac t="(x - 3) mod 10 = 0" and s="x mod 10 = 3" in subst)
 apply (simp add: mod_eq_diff_mod_0_conv[symmetric])
apply (rule_tac t="(7 + x) mod 10 = 0" and s="x mod 10 = 3" in subst)
 apply (simp add: mod_add1_eq_if[of 7])
apply (rule conj_cong[OF refl])
apply (simp add: div_add1_eq_if)
apply (simp add: div_diff1_eq1)
apply (simp add: iTILL_iff)
done

lemma "[25, mod 10, 5] \<oplus>- 32 = [3, mod 10, 4]"
apply (simp add: iT_Plus_neg_image_conv iMODb_cut_ge)
apply (simp add: iMODb_conv iT_Mult_def iT_Plus_def)
apply (rule_tac t=4 and s="Suc(Suc(Suc(Suc 0)))" in subst, simp)
apply (simp add: iTILL_def atMost_Suc)
done
*)

lemma iMODb_add_neg: "
  [r, mod m, c] \<oplus>- k = (
    if k \<le> r then [r - k, mod m, c] 
    else 
      if k \<le> r + m * c then 
      [(m + r mod m - k mod m) mod m, mod m, (r + m * c - k) div m]
      else {})"
apply (clarsimp simp add: iMODb_iMOD_iIN_conv iT_Plus_neg_Int iMOD_add_neg iIN_add_neg)
apply (simp add: iMOD_iIN_iMODb_conv)
apply (rule_tac t="(m + r mod m - k mod m) mod m" and s="(r + m * c - k) mod m" in subst)
 apply (simp add: mod_diff1_eq[of k])
apply (subst iMOD_iTILL_iMODb_conv, simp)
apply (subst sub_mod_div_eq_div, simp)
done

lemma iMODb_add_neg': "
  [r, mod m, c] \<oplus>- k = (
    if k \<le> r then [r - k, mod m, c] 
    else if k \<le> r + m * c then 
      if k mod m \<le> r mod m
        then [ r mod m - k mod m, mod m, c + r div m - k div m]
        else [ m + r mod m - k mod m, mod m, c + r div m - Suc (k div m) ]
      else {})"
apply (clarsimp simp add: iMODb_add_neg)
apply (case_tac "m = 0", simp+)
apply (case_tac "k mod m \<le> r mod m")
 apply (clarsimp simp: linorder_not_le)
 apply (simp add: divisor_add_diff_mod_if)
 apply (simp add: div_diff1_eq_if)
apply (clarsimp simp: linorder_not_le)
apply (simp add:  div_diff1_eq_if)
done

corollary iMODb_add_neg1: "
  k \<le> r \<Longrightarrow> [r, mod m, c] \<oplus>- k = [r - k, mod m, c]"
by (simp add: iMODb_add_neg)

corollary iMODb_add_neg2: "
  \<lbrakk> r < k; k \<le> r + m * c \<rbrakk> \<Longrightarrow> 
  [r, mod m, c] \<oplus>- k = 
  [(m + r mod m - k mod m) mod m, mod m, (r + m * c - k) div m]"
by (simp add: iMODb_add_neg)

corollary iMODb_add_neg2_mod_le: "
  \<lbrakk> r < k; k \<le> r + m * c; k mod m \<le> r mod m \<rbrakk> \<Longrightarrow> 
  [r, mod m, c] \<oplus>- k = 
  [ r mod m - k mod m, mod m, c + r div m - k div m]"
by (simp add: iMODb_add_neg')

corollary iMODb_add_neg2_mod_less: "
  \<lbrakk> r < k; k \<le> r + m * c; r mod m < k mod m\<rbrakk> \<Longrightarrow> 
  [r, mod m, c] \<oplus>- k = 
  [ m + r mod m - k mod m, mod m, c + r div m - Suc (k div m) ]"
by (simp add: iMODb_add_neg')

lemma iMODb_add_neg3: "r + m * c < k  \<Longrightarrow> [r, mod m, c] \<oplus>- k = {}"
by (simp add: iMODb_add_neg)

lemmas iT_add_neg =
  iFROM_add_neg 
  iIN_add_neg
  iTILL_add_neg
  iMOD_add_neg
  iMODb_add_neg
  iT_Plus_neg_singleton


subsubsection \<open>Subtraction of intervals from constants\<close>

definition iT_Minus :: "Time \<Rightarrow> iT \<Rightarrow> iT" (infixl "\<ominus>" 55)
  where "k \<ominus> I \<equiv> {x. x \<le> k \<and> (k - x) \<in> I}"

lemma iT_Minus_mem_iff: "(x \<in> k \<ominus> I) = (x \<le> k \<and> k - x \<in> I)"
by (simp add: iT_Minus_def)

lemma iT_Minus_mono: "A \<subseteq> B \<Longrightarrow> k \<ominus> A \<subseteq> k \<ominus> B"
by (simp add: subset_iff iT_Minus_mem_iff)

lemma iT_Minus_image_conv: "k \<ominus> I = (\<lambda>x. k - x) ` (I \<down>\<le> k)"
by (fastforce simp: iT_Minus_def cut_le_def image_iff)

lemma iT_Minus_cut_eq: "k \<le> t \<Longrightarrow> k \<ominus> (I \<down>\<le> t) = k \<ominus> I"
by (fastforce simp: set_eq_iff iT_Minus_mem_iff)

lemma iT_Minus_Minus_cut_eq: "k \<ominus> (k \<ominus> (I \<down>\<le> k)) = I \<down>\<le> k"
by (fastforce simp: iT_Minus_def)

lemma "10 \<ominus> [\<dots>3] = [7\<dots>,3]"
by (fastforce simp: iT_Minus_def)

lemma iT_Minus_empty: "k \<ominus> {} = {}"
by (simp add: iT_Minus_def)

lemma iT_Minus_0: "k \<ominus> {0} = {k}"
by (simp add: iT_Minus_image_conv cut_le_def image_Collect)

lemma iT_Minus_bound: "x \<in> k \<ominus> I \<Longrightarrow> x \<le> k"
by (simp add: iT_Minus_def)

lemma iT_Minus_finite: "finite (k \<ominus> I)"
apply (rule finite_nat_iff_bounded_le2[THEN iffD2])
apply (rule_tac x=k in exI)
apply (simp add: iT_Minus_bound)
done

lemma iT_Minus_less_Min_empty: "k < iMin I \<Longrightarrow> k \<ominus> I = {}"
by (simp add: iT_Minus_image_conv cut_le_Min_empty)

lemma iT_Minus_Min_singleton: "I \<noteq> {} \<Longrightarrow> (iMin I) \<ominus> I = {0}"
apply (rule set_eqI)
apply (simp add: iT_Minus_mem_iff)
apply (fastforce intro: iMinI_ex2)
done

lemma iT_Minus_empty_iff: "(k \<ominus> I = {}) = (I = {} \<or> k < iMin I)"
apply (case_tac "I = {}", simp add: iT_Minus_empty)
apply (simp add: iT_Minus_image_conv cut_le_empty_iff iMin_gr_iff)
done


(* 
An example: 
  100 \<ominus> {60, 70, 80, 90, 95} = {5, 10, 20, 30, 40} 
  imirror {60, 70, 80, 90, 95} = {60, 65, 75, 95, 95}
  {60, 65, 75, 85, 95} \<oplus> 100 \<oplus>- (60 + 95)
  = {160, 165, 175, 185, 195} \<oplus>- 155 
  = {5, 10, 20, 30, 40}

I \<oplus> k \<oplus>- (iMin I + Max I))
*)
lemma iT_Minus_imirror_conv: "
  k \<ominus> I = imirror (I \<down>\<le> k) \<oplus> k \<oplus>- (iMin I + Max (I \<down>\<le> k))"
apply (case_tac "I = {}")
 apply (simp add: iT_Minus_empty cut_le_empty imirror_empty iT_Plus_empty iT_Plus_neg_empty)
apply (case_tac "k < iMin I")
 apply (simp add: iT_Minus_less_Min_empty cut_le_Min_empty imirror_empty iT_Plus_empty iT_Plus_neg_empty)
apply (simp add: linorder_not_less)
apply (frule cut_le_Min_not_empty[of _ k], assumption)
apply (rule set_eqI)
apply (simp add: iT_Minus_image_conv iT_Plus_neg_image_conv iT_Plus_neg_mem_iff iT_Plus_mem_iff imirror_iff image_iff Bex_def i_cut_mem_iff cut_le_Min_eq)
apply (rule iffI)
 apply (clarsimp, rename_tac x')
 apply (rule_tac x="k - x' + iMin I + Max (I \<down>\<le> k)" in exI, simp)
 apply (simp add: add.assoc le_add_diff)
 apply (simp add: add.commute[of k] le_add_diff nat_cut_le_finite cut_leI trans_le_add2)
 apply (rule_tac x=x' in exI, simp)
apply (clarsimp, rename_tac x1 x2)
apply (rule_tac x=x2 in exI)
apply simp
apply (drule nat_add_right_cancel[THEN iffD2, of _ _ k], simp)
apply (simp add: trans_le_add2 nat_cut_le_finite cut_le_mem_iff)
done

lemma iT_Minus_imirror_conv': "
  k \<ominus> I = imirror (I \<down>\<le> k) \<oplus> k \<oplus>- (iMin (I \<down>\<le> k) + Max (I \<down>\<le> k))"
apply (case_tac "I = {}")
 apply (simp add: iT_Minus_empty cut_le_empty imirror_empty iT_Plus_empty iT_Plus_neg_empty)
apply (case_tac "k < iMin I")
 apply (simp add: iT_Minus_less_Min_empty cut_le_Min_empty imirror_empty iT_Plus_empty iT_Plus_neg_empty)
apply (simp add: cut_le_Min_not_empty cut_le_Min_eq iT_Minus_imirror_conv)
done

lemma iT_Minus_Max: "
  \<lbrakk> I \<noteq> {}; iMin I \<le> k \<rbrakk> \<Longrightarrow> Max (k \<ominus> I) = k - (iMin I)"
apply (rule Max_equality)
  apply (simp add: iT_Minus_mem_iff iMinI_ex2)
 apply (simp add: iT_Minus_finite)
apply (fastforce simp: iT_Minus_def)
done

lemma iT_Minus_Min: "
  \<lbrakk> I \<noteq> {}; iMin I \<le> k \<rbrakk> \<Longrightarrow> iMin (k \<ominus> I) = k - (Max (I \<down>\<le> k))"
apply (insert nat_cut_le_finite[of I k])
apply (frule cut_le_Min_not_empty[of _ k], assumption)
apply (rule iMin_equality)
 apply (simp add: iT_Minus_mem_iff nat_cut_le_Max_le del: Max_le_iff)
 apply (simp add: subsetD[OF cut_le_subset, OF Max_in])
apply (clarsimp simp add: iT_Minus_image_conv image_iff, rename_tac x')
apply (rule diff_le_mono2)
apply (simp add: Max_ge_iff cut_le_mem_iff)
done

lemma iT_Minus_Minus_eq: "\<lbrakk> finite I; Max I \<le> k \<rbrakk> \<Longrightarrow> k \<ominus> (k \<ominus> I) = I"
apply (simp add: iT_Minus_cut_eq[of k k I, symmetric] iT_Minus_Minus_cut_eq)
apply (simp add: cut_le_Max_all)
done

lemma iT_Minus_Minus_eq2: "I \<subseteq> [\<dots>k] \<Longrightarrow> k \<ominus> (k \<ominus> I) = I"
apply (case_tac "I = {}")
 apply (simp add: iT_Minus_empty)
apply (rule iT_Minus_Minus_eq)
 apply (simp add: finite_subset iTILL_finite)
apply (frule Max_subset)
apply (simp add: iTILL_finite iTILL_Max)+
done

(* An example:
  10 \<ominus> (100 \<ominus> {97,98,99,101,102}) = {7,8,9} 
  1000 \<ominus> (100 \<ominus> {97,98,99,101,102, 998,1002}) = {997,998,999} 
*)
lemma iT_Minus_Minus: "a \<ominus> (b \<ominus> I) = (I \<down>\<le> b) \<oplus> a \<oplus>- b"
apply (rule set_eqI)
apply (simp add: iT_Minus_image_conv iT_Plus_image_conv iT_Plus_neg_image_conv image_iff Bex_def i_cut_mem_iff)
apply fastforce
done

lemma iT_Minus_Plus_empty: "k < n \<Longrightarrow> k \<ominus> (I \<oplus> n) = {}"
apply (case_tac "I = {}")
 apply (simp add: iT_Plus_empty iT_Minus_empty)
apply (simp add: iT_Minus_empty_iff iT_Plus_empty_iff iT_Plus_Min)
done
lemma iT_Minus_Plus_commute: "n \<le> k \<Longrightarrow> k \<ominus> (I \<oplus> n) = (k - n) \<ominus> I"
apply (rule set_eqI)
apply (simp add: iT_Minus_image_conv iT_Plus_image_conv image_iff Bex_def i_cut_mem_iff)
apply fastforce
done

lemma iT_Minus_Plus_cut_assoc: "(k \<ominus> I) \<oplus> n = (k + n) \<ominus> (I \<down>\<le> k)"
apply (rule set_eqI)
apply (simp add: iT_Plus_mem_iff iT_Minus_mem_iff cut_le_mem_iff)
apply fastforce
done

lemma iT_Minus_Plus_assoc: "
  \<lbrakk> finite I; Max I \<le> k \<rbrakk> \<Longrightarrow> (k \<ominus> I) \<oplus> n = (k + n) \<ominus> I"
by (insert iT_Minus_Plus_cut_assoc[of k I n], simp add: cut_le_Max_all)
lemma iT_Minus_Plus_assoc2: "
  I \<subseteq> [\<dots>k] \<Longrightarrow> (k \<ominus> I) \<oplus> n = (k + n) \<ominus> I"
apply (case_tac "I = {}")
 apply (simp add: iT_Minus_empty iT_Plus_empty)
apply (rule iT_Minus_Plus_assoc)
 apply (simp add: finite_subset iTILL_finite)
apply (frule Max_subset)
apply (simp add: iTILL_finite iTILL_Max)+
done


lemma iT_Minus_Un: "k \<ominus> (A \<union> B) = (k \<ominus> A) \<union> (k \<ominus> B)"
by (fastforce simp: iT_Minus_def)

lemma iT_Minus_Int: "k \<ominus> (A \<inter> B) = (k \<ominus> A) \<inter> (k \<ominus> B)"
by (fastforce simp: set_eq_iff iT_Minus_mem_iff)

lemma iT_Minus_singleton: "k \<ominus> {a} = (if a \<le> k then {k - a} else {})"
by (simp add: iT_Minus_image_conv cut_le_singleton)
corollary iT_Minus_singleton1: "a \<le> k \<Longrightarrow> k \<ominus> {a} = {k-a}"
by (simp add: iT_Minus_singleton)
corollary iT_Minus_singleton2: "k < a \<Longrightarrow> k \<ominus> {a} = {}"
by (simp add: iT_Minus_singleton)


lemma iMOD_sub: "
  k \<ominus> [r, mod m] = 
  (if r \<le> k then [(k - r) mod m, mod m, (k - r) div m] else {})"
apply (rule set_eqI)
apply (simp add: iT_Minus_mem_iff iT_iff)
apply (fastforce simp add: mod_sub_eq_mod_swap[of r, symmetric])
done

corollary iMOD_sub1: "
  r \<le> k \<Longrightarrow> k \<ominus> [r, mod m] = [(k - r) mod m, mod m, (k - r) div m]"
by (simp add: iMOD_sub)

corollary iMOD_sub2: "k < r \<Longrightarrow> k \<ominus> [r, mod m] = {}"
apply (rule iT_Minus_less_Min_empty)
apply (simp add: iMOD_Min)
done


lemma iTILL_sub: "k \<ominus> [\<dots>n] = (if n \<le> k then [k - n\<dots>,n] else [\<dots>k])"
by (force simp add: set_eq_iff iT_Minus_mem_iff iT_iff)

corollary iTILL_sub1: "n \<le> k \<Longrightarrow> k \<ominus> [\<dots>n] = [k - n\<dots>,n]"
by (simp add: iTILL_sub)

corollary iTILL_sub2: "k \<le> n \<Longrightarrow> k \<ominus> [\<dots>n] = [\<dots>k]"
by (simp add: iTILL_sub iIN_0_iTILL_conv)

(* An example: 30 \<ominus> [2, mod 10] = {8,18,28} *)
lemma iMODb_sub: "
  k \<ominus> [r, mod m, c] = (
    if r + m * c \<le> k then [ k - r - m * c, mod m, c] else 
      if r \<le> k then [ (k - r) mod m, mod m, (k - r) div m] else {})"
apply (case_tac "m = 0")
 apply (simp add: iMODb_mod_0 iIN_0 iT_Minus_singleton)
apply (subst iMODb_iMOD_iTILL_conv)
apply (subst iT_Minus_Int) 
apply (simp add: iMOD_sub iTILL_sub)
apply (intro conjI impI)
 apply simp
 apply (subgoal_tac "(k - r) mod m \<le> k - (r + m * c)")
  prefer 2
  apply (subgoal_tac "m * c \<le> k - r - (k - r) mod m")
   prefer 2
   apply (drule add_le_imp_le_diff2)
   apply (drule div_le_mono[of _ _ m], simp)
   apply (drule mult_le_mono2[of _ _ m])
   apply (simp add: minus_mod_eq_mult_div [symmetric])
  apply (simp add: le_diff_conv2[OF mod_le_dividend] del: diff_diff_left)
 apply (subst iMODb_iMOD_iIN_conv)
 apply (simp add: Int_assoc minus_mod_eq_mult_div [symmetric])
 apply (subst iIN_inter, simp+)
 apply (rule set_eqI)
 apply (fastforce simp add: iT_iff mod_diff_mult_self2 diff_diff_left[symmetric] simp del: diff_diff_left)
apply (simp add: Int_absorb2 iMODb_iTILL_subset)
done

corollary iMODb_sub1: "
  \<lbrakk> r \<le> k; k \<le> r + m * c \<rbrakk> \<Longrightarrow> 
  k \<ominus> [r, mod m, c] = [(k - r) mod m, mod m, (k - r) div m]"
by (clarsimp simp: iMODb_sub iMODb_mod_0)

corollary iMODb_sub2: "k < r \<Longrightarrow> k \<ominus> [r, mod m, c] = {}"
apply (rule iT_Minus_less_Min_empty)
apply (simp add: iMODb_Min)
done

corollary iMODb_sub3: "
  r + m * c \<le> k \<Longrightarrow> k \<ominus> [r, mod m, c] = [ k - r - m * c, mod m, c]"
by (simp add: iMODb_sub)

lemma iFROM_sub: "k \<ominus> [n\<dots>] = (if n \<le> k then [\<dots>k - n] else {})"
by (simp add: iMOD_1[symmetric] iMOD_sub iMODb_mod_1 iIN_0_iTILL_conv)

corollary iFROM_sub1: "n \<le> k \<Longrightarrow> k \<ominus> [n\<dots>] = [\<dots>k-n]"
by (simp add: iFROM_sub)

corollary iFROM_sub_empty: "k < n \<Longrightarrow> k \<ominus> [n\<dots>] = {}"
by (simp add: iFROM_sub)


(* Examples:
  10 \<ominus> [2\<dots>,3] = {3,4,5,6,7,8}
  10 \<ominus> [7\<dots>,5] = {0,1,2,3} 
*)
lemma iIN_sub: "
  k \<ominus> [n\<dots>,d] = (
  if n + d \<le> k then [k - (n + d)\<dots>,d]
  else if n \<le> k then [\<dots>k - n] else {})"
apply (simp add: iMODb_mod_1[symmetric] iMODb_sub)
apply (simp add: iMODb_mod_1 iIN_0_iTILL_conv)
done

lemma iIN_sub1: "n + d \<le> k \<Longrightarrow> k \<ominus> [n\<dots>,d] = [k - (n + d)\<dots>,d]"
by (simp add: iIN_sub)

lemma iIN_sub2: "\<lbrakk> n \<le> k; k \<le> n + d \<rbrakk> \<Longrightarrow> k \<ominus> [n\<dots>,d] = [\<dots>k - n]"
by (clarsimp simp: iIN_sub iIN_0_iTILL_conv)

lemma iIN_sub3: "k < n \<Longrightarrow> k \<ominus> [n\<dots>,d] = {}"
by (simp add: iIN_sub)

lemmas iT_sub =
  iFROM_sub
  iIN_sub
  iTILL_sub
  iMOD_sub
  iMODb_sub
  iT_Minus_singleton


subsubsection \<open>Division of intervals by constants\<close>

text \<open>Monotonicity and injectivity of artithmetic operators\<close>

lemma iMOD_div_right_strict_mono_on: "
  \<lbrakk> 0 < k; k \<le> m \<rbrakk> \<Longrightarrow> strict_mono_on (\<lambda>x. x div k) [r, mod m]"
apply (rule div_right_strict_mono_on, assumption)
apply (clarsimp simp: iT_iff)
apply (drule_tac s="y mod m" in sym, simp)
apply (rule_tac y="x + m" in order_trans, simp)
apply (simp add: less_mod_eq_imp_add_divisor_le)
done

corollary iMOD_div_right_inj_on: "
  \<lbrakk> 0 < k; k \<le> m \<rbrakk> \<Longrightarrow> inj_on (\<lambda>x. x div k) [r, mod m]"
by (rule strict_mono_on_imp_inj_on[OF iMOD_div_right_strict_mono_on])

lemma iMOD_mult_div_right_inj_on: "
  inj_on (\<lambda>x. x div (k::nat)) [r, mod (k * m)]"
apply (case_tac "k * m = 0")
 apply (simp del: mult_is_0 mult_eq_0_iff add: iMOD_0 iIN_0)
apply (simp add: iMOD_div_right_inj_on)
done

lemma iMOD_mult_div_right_inj_on2: "
  m mod k = 0 \<Longrightarrow> inj_on (\<lambda>x. x div k) [r, mod m]"
  by (auto simp add: iMOD_mult_div_right_inj_on)

lemma iMODb_div_right_strict_mono_on: "
  \<lbrakk> 0 < k; k \<le> m \<rbrakk> \<Longrightarrow> strict_mono_on (\<lambda>x. x div k) [r, mod m, c]"
by (rule strict_mono_on_subset[OF iMOD_div_right_strict_mono_on iMODb_iMOD_subset_same])

corollary iMODb_div_right_inj_on: "
  \<lbrakk> 0 < k; k \<le> m \<rbrakk> \<Longrightarrow> inj_on (\<lambda>x. x div k) [r, mod m, c]"
by (rule strict_mono_on_imp_inj_on[OF iMODb_div_right_strict_mono_on])

lemma iMODb_mult_div_right_inj_on: "
  inj_on (\<lambda>x. x div (k::nat)) [r, mod (k * m), c]"
by (rule subset_inj_on[OF iMOD_mult_div_right_inj_on iMODb_iMOD_subset_same])

corollary iMODb_mult_div_right_inj_on2: "
  m mod k = 0 \<Longrightarrow> inj_on (\<lambda>x. x div k) [r, mod m, c]"
  by (auto simp add: iMODb_mult_div_right_inj_on)


definition iT_Div :: "iT \<Rightarrow> Time \<Rightarrow> iT" (infixl "\<oslash>" 55)
  where "I \<oslash> k \<equiv> (\<lambda>n.(n div k)) ` I"

lemma iT_Div_image_conv: "I \<oslash> k = (\<lambda>n.(n div k)) ` I"
by (simp add: iT_Div_def)

lemma iT_Div_mono: "A \<subseteq> B \<Longrightarrow> A \<oslash> k \<subseteq> B \<oslash> k"
by (simp add: iT_Div_def image_mono)

lemma iT_Div_empty: "{} \<oslash> k = {}"
by (simp add: iT_Div_def)
lemma iT_Div_not_empty: "I \<noteq> {} \<Longrightarrow> I \<oslash> k \<noteq> {}"
by (simp add: iT_Div_def)

lemma iT_Div_empty_iff: "(I \<oslash> k = {}) = (I = {})"
by (simp add: iT_Div_def)


lemma iT_Div_0: "I \<noteq> {} \<Longrightarrow> I \<oslash> 0 = [\<dots>0]"
by (force simp: iT_Div_def)
corollary iT_Div_0_if: "I \<oslash> 0 = (if I = {} then {} else [\<dots>0])"
by (force simp: iT_Div_def)
corollary 
  iFROM_div_0: "[n\<dots>] \<oslash> 0 = [\<dots>0]" and
  iTILL_div_0: "[\<dots>n] \<oslash> 0 = [\<dots>0]" and
  iIN_div_0: "[n\<dots>,d] \<oslash> 0 = [\<dots>0]" and
  iMOD_div_0: "[r, mod m] \<oslash> 0 = [\<dots>0]" and
  iMODb_div_0: "[r, mod m, c] \<oslash> 0 = [\<dots>0]"
by (simp add: iT_Div_0 iT_not_empty)+

lemmas iT_div_0 =
  iTILL_div_0 
  iFROM_div_0
  iIN_div_0
  iMOD_div_0
  iMODb_div_0

lemma iT_Div_1: "I \<oslash> Suc 0 = I"
by (simp add: iT_Div_def)

lemma iT_Div_mem_iff_0: "x \<in> (I \<oslash> 0) = (I \<noteq> {} \<and> x = 0)"
by (force simp: iT_Div_0_if)

lemma iT_Div_mem_iff: "
  0 < k \<Longrightarrow> x \<in> (I \<oslash> k) = (\<exists>y \<in> I. y div k = x)"
by (force simp: iT_Div_def)

lemma iT_Div_mem_iff2: "
  0 < k \<Longrightarrow> x div k \<in> (I \<oslash> k) = (\<exists>y \<in> I. y div k = x div k)"
by (rule iT_Div_mem_iff)

lemma iT_Div_mem_iff_Int: "
  0 < k \<Longrightarrow> x \<in> (I \<oslash> k) = (I \<inter> [x * k\<dots>,k - Suc 0] \<noteq> {})"
apply (simp add: ex_in_conv[symmetric] iT_Div_mem_iff iT_iff)
apply (simp add: le_less_div_conv[symmetric] add.commute[of k])
apply (subst less_eq_le_pred, simp)
apply blast
done

lemma iT_Div_imp_mem: "
  0 < k \<Longrightarrow> x \<in> I \<Longrightarrow> x div k \<in> (I \<oslash> k)"
by (force simp: iT_Div_mem_iff2)

lemma iT_Div_singleton: "{a} \<oslash> k = {a div k}"
by (simp add: iT_Div_def)


lemma iT_Div_Un: "(A \<union> B) \<oslash> k = (A \<oslash> k) \<union> (B \<oslash> k)"
by (fastforce simp: iT_Div_def)

lemma iT_Div_insert: "(insert n I) \<oslash> k = insert (n div k) (I \<oslash> k)"
by (fastforce simp: iT_Div_def)

(* Examples:
  {1,2,3,4} \<oslash> 3 \<inter> {5,6,7} \<oslash> 3 = {0,1} \<inter> {1,2} = {1}
  ({1,2,3,4} \<inter> {5,6,7}) \<oslash> 3 = {} \<oslash> 3 = {} 
*)
lemma not_iT_Div_Int: "\<not> (\<forall> k A B. (A \<inter> B) \<oslash> k = (A \<oslash> k) \<inter> (B \<oslash> k))"
apply simp
apply (
  rule_tac x=3 in exI,
  rule_tac x="{0}" in exI,
  rule_tac x="{1}" in exI)
by (simp add: iT_Div_def)

lemma subset_iT_Div_Int: "A \<subseteq> B \<Longrightarrow> (A \<inter> B) \<oslash> k = (A \<oslash> k) \<inter> (B \<oslash> k)"
by (simp add: iT_Div_def subset_image_Int)

lemma iFROM_iT_Div_Int: "
  \<lbrakk> 0 < k; n \<le> iMin A \<rbrakk> \<Longrightarrow> (A \<inter> [n\<dots>]) \<oslash> k = (A \<oslash> k) \<inter> ([n\<dots>] \<oslash> k)"
apply (rule subset_iT_Div_Int)
apply (blast intro: order_trans iMin_le)
done

lemma iIN_iT_Div_Int: "
  \<lbrakk> 0 < k; n \<le> iMin A; \<forall>x\<in>A. x div k \<le> (n + d) div k \<longrightarrow> x \<le> n + d \<rbrakk> \<Longrightarrow> 
  (A \<inter> [n\<dots>,d]) \<oslash> k = (A \<oslash> k) \<inter> ([n\<dots>,d] \<oslash> k)"
apply (rule set_eqI)
apply (simp add: iT_Div_mem_iff Bex_def iIN_iff)
apply (rule iffI)
 apply blast
apply (clarsimp, rename_tac x1 x2)
apply (frule iMin_le)
apply (rule_tac x=x1 in exI, simp)
apply (drule_tac x=x1 in bspec, simp)
apply (drule div_le_mono[of _ "n + d" k])
apply simp
done
corollary iTILL_iT_Div_Int: "
  \<lbrakk> 0 < k; \<forall>x\<in>A. x div k \<le> n div k \<longrightarrow> x \<le> n \<rbrakk> \<Longrightarrow> 
  (A \<inter> [\<dots>n]) \<oslash> k = (A \<oslash> k) \<inter> ([\<dots>n] \<oslash> k)"
by (simp add: iIN_0_iTILL_conv[symmetric] iIN_iT_Div_Int)
lemma iIN_iT_Div_Int_mod_0: "
  \<lbrakk> 0 < k; n mod k = 0; \<forall>x\<in>A. x div k \<le> (n + d) div k \<longrightarrow> x \<le> n + d \<rbrakk> \<Longrightarrow> 
  (A \<inter> [n\<dots>,d]) \<oslash> k = (A \<oslash> k) \<inter> ([n\<dots>,d] \<oslash> k)"
apply (rule set_eqI)
apply (simp add: iT_Div_mem_iff Bex_def iIN_iff)
apply (rule iffI)
 apply blast
apply (elim conjE exE, rename_tac x1 x2)
apply (rule_tac x=x1 in exI, simp)
apply (rule conjI)
 apply (rule ccontr, simp add: linorder_not_le)
 apply (drule_tac m=n and n=x2 and k=k in div_le_mono)
 apply (drule_tac a=x1 and m=k in less_mod_0_imp_div_less)
 apply simp+
apply (drule_tac x=x1 in bspec, simp)
apply (drule div_le_mono[of _ "n + d" k])
apply simp
done

lemma mod_partition_iT_Div_Int: "
  \<lbrakk> 0 < k; 0 < d \<rbrakk> \<Longrightarrow> 
  (A \<inter> [n * k\<dots>,d * k - Suc 0]) \<oslash> k = 
  (A \<oslash> k) \<inter> ([n * k\<dots>,d * k - Suc 0] \<oslash> k)"
apply (rule iIN_iT_Div_Int_mod_0, simp+)
apply (clarify, rename_tac x)
apply (simp add: mod_0_imp_sub_1_div_conv)
apply (rule ccontr, simp add: linorder_not_le pred_less_eq_le)
apply (drule_tac n=x and k=k in div_le_mono)
apply simp
done

(*<*)
lemma "{0,1,2} \<otimes> x = {0*x, 1*x, 2*x}"
by (simp add: iT_Mult_def)
(*>*)

corollary mod_partition_iT_Div_Int2: "
  \<lbrakk> 0 < k; 0 < d; n mod k = 0; d mod k = 0 \<rbrakk> \<Longrightarrow> 
  (A \<inter> [n\<dots>,d - Suc 0]) \<oslash> k =  
  (A \<oslash> k) \<inter> ([n\<dots>,d - Suc 0] \<oslash> k)"
  by (auto simp add: ac_simps mod_partition_iT_Div_Int elim!: dvdE)

corollary mod_partition_iT_Div_Int_one_segment: "
  0 < k \<Longrightarrow> 
  (A \<inter> [n * k\<dots>,k - Suc 0]) \<oslash> k = (A \<oslash> k) \<inter> ([n * k\<dots>,k - Suc 0] \<oslash> k)"
by (insert mod_partition_iT_Div_Int[where d=1], simp)

corollary mod_partition_iT_Div_Int_one_segment2: "
  \<lbrakk> 0 < k; n mod k = 0 \<rbrakk> \<Longrightarrow>
  (A \<inter> [n\<dots>,k - Suc 0]) \<oslash> k = (A \<oslash> k) \<inter> ([n\<dots>,k - Suc 0] \<oslash> k)"
  using mod_partition_iT_Div_Int2[where k=k and d=k and n=n]
by (insert mod_partition_iT_Div_Int2[where k=k and d=k and n=n], simp)


lemma iT_Div_assoc:"I \<oslash> a \<oslash> b = I \<oslash> (a * b)"
by (simp add: iT_Div_def image_image div_mult2_eq)

lemma iT_Div_commute: "I \<oslash> a \<oslash> b = I \<oslash> b \<oslash> a"
by (simp add: iT_Div_assoc mult.commute[of a])

lemma iT_Mult_Div_self: "0 < k \<Longrightarrow> I \<otimes> k \<oslash> k = I"
by (simp add: iT_Mult_def iT_Div_def image_image)
lemma iT_Mult_Div: "
  \<lbrakk> 0 < d;  k mod d = 0 \<rbrakk> \<Longrightarrow> I \<otimes> k \<oslash> d = I \<otimes> (k div d)"
  by (auto simp add: ac_simps iT_Mult_assoc[symmetric] iT_Mult_Div_self)

lemma iT_Div_Mult_self: "
  0 < k \<Longrightarrow> I \<oslash> k \<otimes> k = {y. \<exists>x \<in> I. y = x - x mod k}"
by (simp add: set_eq_iff iT_Mult_def iT_Div_def image_image image_iff div_mult_cancel)

lemma iT_Plus_Div_distrib_mod_less: "
  \<forall>x\<in>I. x mod m + n mod m < m \<Longrightarrow> I \<oplus> n \<oslash> m = I \<oslash> m \<oplus> n div m"
by (simp add: set_eq_iff iT_Div_def iT_Plus_def image_image image_iff div_add1_eq1)
corollary iT_Plus_Div_distrib_mod_0: "
  n mod m = 0 \<Longrightarrow> I \<oplus> n \<oslash> m = I \<oslash> m \<oplus> n div m"
apply (case_tac "m = 0", simp add: iT_Plus_0 iT_Div_0)
apply (simp add: iT_Plus_Div_distrib_mod_less)
done

lemma iT_Div_Min: "I \<noteq> {} \<Longrightarrow> iMin (I \<oslash> k) = iMin I div k"
by (simp add: iT_Div_def iMin_mono2 mono_def div_le_mono)

corollary 
  iFROM_div_Min: "iMin ([n\<dots>] \<oslash> k) = n div k" and
  iIN_div_Min:   "iMin ([n\<dots>,d] \<oslash> k) = n div k" and
  iTILL_div_Min: "iMin ([\<dots>n] \<oslash> k) = 0" and
  iMOD_div_Min:  "iMin ([r, mod m] \<oslash> k) = r div k" and
  iMODb_div_Min: "iMin ([r, mod m, c] \<oslash> k) = r div k"
by (simp add: iT_not_empty iT_Div_Min iT_Min)+

lemmas iT_div_Min = 
  iFROM_div_Min
  iIN_div_Min
  iTILL_div_Min
  iMOD_div_Min
  iMODb_div_Min

lemma iT_Div_Max: "\<lbrakk> finite I; I \<noteq> {} \<rbrakk> \<Longrightarrow> Max (I \<oslash> k) = Max I div k"
by (simp add: iT_Div_def Max_mono2 mono_def div_le_mono)

corollary 
  iIN_div_Max:   "Max ([n\<dots>,d] \<oslash> k) = (n + d) div k" and
  iTILL_div_Max: "Max ([\<dots>n] \<oslash> k) = n div k" and
  iMODb_div_Max: "Max ([r, mod m, c] \<oslash> k) = (r + m * c) div k"
by (simp add: iT_not_empty iT_finite iT_Div_Max iT_Max)+

lemma iT_Div_0_finite: "finite (I \<oslash> 0)"
by (simp add: iT_Div_0_if iTILL_0)

lemma iT_Div_infinite_iff: "0 < k \<Longrightarrow> infinite (I \<oslash> k) = infinite I"
apply (unfold iT_Div_def)
apply (rule iffI)
 apply (rule infinite_image_imp_infinite, assumption)
apply (clarsimp simp: infinite_nat_iff_unbounded_le image_iff, rename_tac x1)
apply (drule_tac x="x1 * k" in spec, clarsimp, rename_tac x2)
apply (drule div_le_mono[of _ _ k], simp)
apply (rule_tac x="x2 div k" in exI)
apply fastforce
done
lemma iT_Div_finite_iff: "0 < k \<Longrightarrow> finite (I \<oslash> k) = finite I"
by (insert iT_Div_infinite_iff, simp)


lemma iFROM_div: "0 < k \<Longrightarrow> [n\<dots>] \<oslash> k = [n div k\<dots>]"
apply (clarsimp simp: set_eq_iff iT_Div_def image_iff Bex_def iFROM_iff, rename_tac x)
apply (rule iffI)
 apply (clarsimp simp: div_le_mono)
apply (rule_tac x="n mod k + k * x" in exI)
apply simp
apply (subst add.commute, subst le_diff_conv[symmetric])
apply (subst minus_mod_eq_mult_div)
apply simp
done

lemma iIN_div: "
  0 < k \<Longrightarrow> 
  [n\<dots>,d] \<oslash> k = [n div k\<dots>, d div k + (n mod k + d mod k) div k ]"
apply (clarsimp simp: set_eq_iff iT_Div_def image_iff Bex_def iIN_iff, rename_tac x)
apply (rule iffI)
 apply clarify
 apply (drule div_le_mono[of n _ k])
 apply (drule div_le_mono[of _ "n + d" k])
 apply (simp add: div_add1_eq[of n d])
apply (clarify, rename_tac x)
apply (simp add: add.assoc[symmetric] div_add1_eq[symmetric])
apply (frule mult_le_mono1[of "n div k" _ k])
apply (frule mult_le_mono1[of _ "(n + d) div k" k])
apply (simp add: mult.commute[of _ k] minus_mod_eq_mult_div [symmetric])
apply (simp add: le_diff_conv le_diff_conv2[OF mod_le_dividend])
apply (drule order_le_less[of _ "(n + d) div k", THEN iffD1], erule disjE)
 apply (rule_tac x="k * x + n mod k" in exI)
 apply (simp add: add.commute[of _ "n mod k"])
 apply (case_tac "n mod k \<le> (n + d) mod k", simp)
 apply (simp add: linorder_not_le)
 apply (drule_tac m=x in less_imp_le_pred)
 apply (drule_tac i=x and k=k in mult_le_mono2)
 apply (simp add: diff_mult_distrib2 minus_mod_eq_mult_div [symmetric])
 apply (subst add.commute[of "n mod k"])
 apply (subst le_diff_conv2[symmetric])
  apply (simp add: trans_le_add1)
 apply (rule order_trans, assumption)
 apply (rule diff_le_mono2)
 apply (simp add: trans_le_add2)
apply (rule_tac x="n + d" in exI, simp)
done

corollary iIN_div_if: "
  0 < k \<Longrightarrow> [n\<dots>,d] \<oslash> k = 
  [n div k\<dots>, d div k + (if n mod k + d mod k < k then 0 else Suc 0)]"
apply (simp add: iIN_div)
apply (simp add: iIN_def add.assoc[symmetric] div_add1_eq[symmetric] div_add1_eq2[where a=n])
done

corollary iIN_div_eq1: "
  \<lbrakk> 0 < k; n mod k + d mod k < k \<rbrakk> \<Longrightarrow> 
  [n\<dots>,d] \<oslash> k = [n div k\<dots>,d div k]"
by (simp add: iIN_div_if)

corollary iIN_div_eq2: "
  \<lbrakk> 0 < k; k \<le> n mod k + d mod k \<rbrakk> \<Longrightarrow> 
  [n\<dots>,d] \<oslash> k = [n div k\<dots>, Suc (d div k)]"
by (simp add: iIN_div_if)

corollary iIN_div_mod_eq_0: "
  \<lbrakk> 0 < k; n mod k = 0 \<rbrakk> \<Longrightarrow> [n\<dots>,d] \<oslash> k = [n div k\<dots>,d div k]"
by (simp add: iIN_div_eq1)


lemma iTILL_div: "
   0 < k \<Longrightarrow> [\<dots>n] \<oslash> k = [\<dots>n div k]"
by (simp add: iIN_0_iTILL_conv[symmetric] iIN_div_if)

lemma iMOD_div_ge: "
  \<lbrakk> 0 < m; m \<le> k \<rbrakk> \<Longrightarrow> [r, mod m] \<oslash> k = [r div k\<dots>]"
apply (frule less_le_trans[of _ _ k], assumption)
apply (clarsimp simp: set_eq_iff iT_Div_mem_iff Bex_def iT_iff, rename_tac x)
apply (rule iffI)
 apply (fastforce simp: div_le_mono)
apply (rule_tac x="
  if x * k < r then r else 
    ((if x * k mod m \<le> r mod m then 0 else m) + r mod m + (x * k - x * k mod m))" 
  in exI)
apply (case_tac "x * k < r")
 apply simp
 apply (drule less_imp_le[of _ r], drule div_le_mono[of _ r k], simp)
apply (simp add: linorder_not_less linorder_not_le)
apply (simp add: div_le_conv add.commute[of k])
apply (subst diff_add_assoc, simp)+
apply (simp add: div_mult_cancel[symmetric] del: add_diff_assoc)
apply (case_tac "x * k mod m = 0")
 apply (clarsimp elim!: dvdE)
 apply (drule sym)
 apply (simp add: mult.commute[of m])
 apply (blast intro: div_less order_less_le_trans mod_less_divisor)
apply simp
apply (intro conjI impI)
   apply (simp add: div_mult_cancel)
  apply (simp add: div_mult_cancel)
  apply (subst add.commute, subst diff_add_assoc, simp)
  apply (subst add.commute, subst div_mult_self1, simp)
  apply (subst div_less)
   apply (rule order_less_le_trans[of _ m], simp add: less_imp_diff_less)
   apply simp
  apply simp
 apply (rule_tac y="x * k" in order_trans, assumption)
 apply (simp add: div_mult_cancel)
 apply (rule le_add_diff)
 apply (simp add: trans_le_add1)
apply (simp add: div_mult_cancel)
apply (subst diff_add_assoc2, simp add: trans_le_add1)
apply simp
done
corollary iMOD_div_self: "
  0 < m \<Longrightarrow> [r, mod m] \<oslash> m = [r div m\<dots>]"
by (simp add: iMOD_div_ge)

lemma iMOD_div: "
  \<lbrakk> 0 < k; m mod k = 0 \<rbrakk> \<Longrightarrow> 
  [r, mod m] \<oslash> k = [r div k, mod (m div k) ]"
apply (case_tac "m = 0")
   apply (simp add: iMOD_0 iIN_0 iT_Div_singleton)
  apply (clarsimp elim!: dvdE)
apply (rename_tac q)
apply hypsubst_thin
apply (cut_tac r="r div k" and k=k and m=q in iMOD_mult)
apply (drule arg_cong[where f="\<lambda>x. x \<oplus> (r mod k)"])
apply (drule sym)
apply (simp add: iMOD_add mult.commute[of k])
apply (cut_tac I="[r div k, mod q] \<otimes> k" and m=k and n="r mod k" in iT_Plus_Div_distrib_mod_less)
 apply (rule ballI)
 apply (simp only: iMOD_mult iMOD_iff, elim conjE)
 apply (drule mod_factor_imp_mod_0)
 apply simp
apply (simp add: iT_Plus_0)
apply (simp add: iT_Mult_Div[OF _ mod_self] iT_Mult_1)
done

lemma iMODb_div_self: "
  0 < m \<Longrightarrow> [r, mod m, c] \<oslash> m = [r div m\<dots>,c]"
apply (subst iMODb_iMOD_iTILL_conv)
apply (subst iTILL_iT_Div_Int)
  apply simp
 apply (clarsimp simp: iT_iff simp del: div_mult_self1 div_mult_self2, rename_tac x)
 apply (drule div_le_mod_le_imp_le)
 apply simp+
apply (simp add: iMOD_div_self iTILL_div iFROM_iTILL_iIN_conv)
done

lemma iMODb_div_ge: "
  \<lbrakk> 0 < m; m \<le> k \<rbrakk> \<Longrightarrow> 
  [r, mod m, c] \<oslash> k = [r div k\<dots>,(r + m * c) div k - r div k]"
apply (case_tac "m = k")
 apply (simp add: iMODb_div_self)
apply (drule le_neq_trans, simp+)
apply (induct c)
 apply (simp add: iMODb_0 iIN_0 iT_Div_singleton)
apply (rule_tac t="[ r, mod m, Suc c ]" and s="[ r, mod m, c ] \<union> {r + m * c + m}" in subst)
 apply (cut_tac c=c and c'=0 and r=r and m=m in iMODb_append_union_Suc[symmetric])
 apply (simp add: iMODb_0 iIN_0 add.commute[of m] add.assoc)
apply (subst iT_Div_Un)
apply (simp add: iT_Div_singleton)
apply (simp add: add.commute[of m] add.assoc[symmetric])
apply (case_tac "(r + m * c) mod k + m mod k < k")
 apply (simp add: div_add1_eq1)
 apply (rule insert_absorb)
 apply (simp add: iIN_iff div_le_mono)
apply (simp add: linorder_not_less)
apply (simp add: div_add1_eq2)
apply (rule_tac t="Suc ((r + m * c) div k)" and s="Suc (r div k + ((r + m * c) div k - r div k))" in subst)
 apply (simp add: div_le_mono)
apply (simp add: iIN_Suc_insert_conv)
done

corollary iMODb_div_ge_if: "
  \<lbrakk> 0 < m; m \<le> k \<rbrakk> \<Longrightarrow> 
  [r, mod m, c] \<oslash> k = 
  [r div k\<dots>, m * c div k + (if r mod k + m * c mod k < k then 0 else Suc 0)]"
by (simp add: iMODb_div_ge div_add1_eq_if[of _ r])

lemma iMODb_div: "
  \<lbrakk> 0 < k; m mod k = 0 \<rbrakk> \<Longrightarrow> 
  [r, mod m, c] \<oslash> k = [r div k, mod (m div k), c ]"
apply (subst iMODb_iMOD_iTILL_conv)
apply (subst iTILL_iT_Div_Int)
  apply simp
 apply (simp add: Ball_def iMOD_iff, intro allI impI, elim conjE, rename_tac x)
 apply (drule div_le_mod_le_imp_le)
  apply (subst mod_add1_eq_if)
  apply (simp add: mod_0_imp_mod_mult_right_0)
  apply (drule mod_eq_mod_0_imp_mod_eq, simp+)
apply (simp add: iMOD_div iTILL_div)
apply (simp add: iMOD_iTILL_iMODb_conv div_le_mono)
apply (clarsimp simp: mult.assoc iMODb_mod_0 iMOD_0 elim!: dvdE)
done

lemmas iT_div =
  iTILL_div
  iFROM_div
  iIN_div
  iMOD_div
  iMODb_div
  iT_Div_singleton

text \<open>This lemma is valid for all @{term "k \<le> m"},i. e., also for k with @{term "m mod k \<noteq> 0"}.\<close> 
lemma iMODb_div_unique: "
  \<lbrakk> 0 < k; k \<le> m; k \<le> c; [r', mod m', c'] = [r, mod m, c] \<oslash> k \<rbrakk> \<Longrightarrow> 
  r' = r div k \<and> m' = m div k \<and> c' = c"
apply (case_tac "r' \<noteq> r div k")
 apply (drule arg_cong[where f="iMin"])
 apply (simp add: iT_Min iT_not_empty iT_Div_Min)
apply simp
apply (case_tac "m' = 0 \<or> c' = 0")
 apply (subgoal_tac "[ r div k, mod m', c' ] = {r div k}")
  prefer 2
  apply (rule iMODb_singleton_eq_conv[THEN iffD2], simp)
 apply simp
 apply (drule arg_cong[where f="Max"])
 apply (simp add: iMODb_mod_0 iIN_0 iT_Max iT_Div_Max iT_Div_finite_iff iT_Div_not_empty iT_finite iT_not_empty)
 apply (subgoal_tac "r div k < (r + m * c) div k", simp)
 apply (subst div_add1_eq_if, simp)
 apply clarsimp
 apply (rule order_less_le_trans[of _ "k * k div k"], simp)
 apply (rule div_le_mono)
 apply (simp add: mult_mono)
apply (subgoal_tac "c' = c")
 prefer 2
 apply (drule arg_cong[where f="\<lambda>A. card A"])
 apply (simp add: iT_Div_def card_image[OF iMODb_div_right_inj_on] iMODb_card)
apply clarsimp
apply (frule iMODb_div_right_strict_mono_on[of k m r c], assumption)
apply (frule_tac a=k and b=0 and m=m' and r="r div k" and c=c in iMODb_inext_nth_diff, simp)
apply (simp add: iT_Div_Min iT_not_empty iT_Min)
apply (simp add: iT_Div_def inext_nth_image[OF iMODb_not_empty])
apply (simp add: iMODb_inext_nth)
done


lemma iMODb_div_mod_gr0_is_0_not_ex0: "
  \<lbrakk> 0 < k; k < m; 0 < m mod k; k \<le> c; r mod k = 0 \<rbrakk> \<Longrightarrow>
  \<not>(\<exists>r' m' c'. [r', mod m', c'] = [r, mod m, c] \<oslash> k)"
apply (rule ccontr, simp, elim exE conjE)
apply (frule_tac r'=r' and m'=m' and c'=c' and r=r and k=k and m=m and c=c
  in iMODb_div_unique[OF _ less_imp_le], simp+)
apply (drule arg_cong[where f="Max"])
apply (simp add: iT_Max iT_Div_Max iT_Div_finite_iff iT_Div_not_empty iT_finite iT_not_empty)
apply (simp add: div_add1_eq1)
apply (simp add: mult.commute[of m])
apply (simp add: div_mult1_eq[of c m] div_eq_0_conv)
apply (subgoal_tac "c \<le> c * (m mod k)")
apply simp+
done

lemma iMODb_div_mod_gr0_not_ex__arith_aux1: "
  \<lbrakk> (0::nat) < k; k < m; 0 < x1 \<rbrakk> \<Longrightarrow>
  x1 * m + x2 - x mod k + x3 + x mod k = x1 * m + x2 + x3"
apply (drule Suc_leI[of _ x1])
apply (drule mult_le_mono1[of "Suc 0" _ m])
apply (subgoal_tac "x mod k \<le> x1 * m")
 prefer 2
 apply (rule order_trans[OF mod_le_divisor], assumption)
 apply (rule order_less_imp_le)
 apply (rule order_less_le_trans)
 apply simp+
done

lemma iMODb_div_mod_gr0_not_ex: "
  \<lbrakk> 0 < k; k < m; 0 < m mod k; k \<le> c \<rbrakk> \<Longrightarrow>
  \<not>(\<exists>r' m' c'. [r', mod m', c'] = [r, mod m, c] \<oslash> k)"
apply (case_tac "r mod k = 0")
 apply (simp add: iMODb_div_mod_gr0_is_0_not_ex0)
apply (rule ccontr, simp, elim exE conjE)
apply (frule_tac r'=r' and m'=m' and c'=c' and r=r and k=k and m=m and c=c
  in iMODb_div_unique[OF _ less_imp_le], simp+)
apply clarsimp
apply (drule arg_cong[where f="Max"])
apply (simp add: iT_Max iT_Div_Max iT_Div_finite_iff iT_Div_not_empty iT_finite iT_not_empty)
apply (simp add: div_add1_eq[of r "m * c"])
apply (simp add: mult.commute[of _ c])
apply (clarsimp simp add: div_mult1_eq[of c m k])
apply (subgoal_tac "Suc 0 \<le> c * (m mod k) div k", simp)
apply (thin_tac "_ = 0")+
apply (drule div_le_mono[of k c k], simp)
apply (rule order_trans[of _ "c div k"], simp)
apply (rule div_le_mono, simp)
done


lemma iMOD_div_eq_imp_iMODb_div_eq: "
  \<lbrakk> 0 < k; k \<le> m; [r', mod m'] = [r, mod m] \<oslash> k \<rbrakk> \<Longrightarrow>
  [r', mod m', c] = [r, mod m, c] \<oslash> k"
apply (subgoal_tac "r' = r div k")
 prefer 2
 apply (drule arg_cong[where f=iMin])
 apply (simp add: iT_Div_Min iMOD_not_empty iMOD_Min)
apply clarsimp
apply (frule iMOD_div_right_strict_mono_on[of _ m r], assumption)
apply (frule card_image[OF strict_mono_on_imp_inj_on[OF iMODb_div_right_strict_mono_on[of k m r c]]], assumption)
apply (simp add: iMODb_card)
apply (subgoal_tac "r + m * c \<in> [r, mod m]")
 prefer 2
 apply (simp add: iMOD_iff)
apply (subgoal_tac "[r, mod m, c] = [ r, mod m ] \<down>\<le> (r + m * c)")
 prefer 2
 apply (simp add: iMOD_cut_le1)
apply (simp add: iT_Div_def)
apply (simp add: cut_le_image[symmetric])
apply (drule sym)
apply (simp add: iMOD_cut_le)
apply (simp add: linorder_not_le[of "r div k", symmetric])
apply (simp add: div_le_mono)
apply (case_tac "m' = 0")
 apply (simp add: iMODb_mod_0_card)
apply (rule arg_cong[where f="\<lambda>c. [r div k, mod m', c]"])
apply (simp add: iMODb_card)
done


lemma iMOD_div_unique: "
  \<lbrakk> 0 < k; k \<le> m; [r', mod m'] = [r, mod m] \<oslash> k \<rbrakk> \<Longrightarrow>
  r' = r div k \<and> m' = m div k"
apply (frule iMOD_div_eq_imp_iMODb_div_eq[of k m r' m' r k], assumption+)
apply (simp add: iMODb_div_unique[of k _ k])
done

lemma iMOD_div_mod_gr0_not_ex: "
  \<lbrakk> 0 < k; k < m; 0 < m mod k \<rbrakk> \<Longrightarrow>
  \<not> (\<exists>r' m'. [r', mod m'] = [r, mod m] \<oslash> k)"
apply (rule ccontr, clarsimp)
apply (frule_tac k=k and m=m and r'=r' and m'=m' and c=k 
  in iMOD_div_eq_imp_iMODb_div_eq[OF _ less_imp_le], assumption+)
apply (frule iMODb_div_mod_gr0_not_ex[of k m k r], simp+)
done


subsection \<open>Interval cut operators with arithmetic interval operators\<close>

lemma 
  iT_Plus_cut_le2:      "(I \<oplus> k) \<down>\<le> (t + k) = (I \<down>\<le> t) \<oplus> k" and
  iT_Plus_cut_less2:    "(I \<oplus> k) \<down>< (t + k) = (I \<down>< t) \<oplus> k" and
  iT_Plus_cut_ge2:      "(I \<oplus> k) \<down>\<ge> (t + k) = (I \<down>\<ge> t) \<oplus> k" and
  iT_Plus_cut_greater2: "(I \<oplus> k) \<down>> (t + k) = (I \<down>> t) \<oplus> k"
unfolding iT_Plus_def by fastforce+

lemma iT_Plus_cut_le: "
  (I \<oplus> k) \<down>\<le> t = (if t < k then {} else I \<down>\<le> (t - k) \<oplus> k)"
apply (case_tac "t < k")
 apply (simp add: cut_le_empty_iff iT_Plus_mem_iff)
apply (insert iT_Plus_cut_le2[of I k "t - k"], simp)
done

lemma iT_Plus_cut_less: "(I \<oplus> k) \<down>< t = I \<down>< (t - k) \<oplus> k"
apply (case_tac "t < k")
 apply (simp add: cut_less_0_empty iT_Plus_empty cut_less_empty_iff iT_Plus_mem_iff)
apply (insert iT_Plus_cut_less2[of I k "t - k"], simp)
done

lemma iT_Plus_cut_ge: "(I \<oplus> k) \<down>\<ge> t = I \<down>\<ge> (t - k) \<oplus> k"
apply (case_tac "t < k")
 apply (simp add: cut_ge_0_all cut_ge_all_iff iT_Plus_mem_iff)
apply (insert iT_Plus_cut_ge2[of I k "t - k"], simp)
done

lemma iT_Plus_cut_greater: "
  (I \<oplus> k) \<down>> t = (if t < k then I \<oplus> k else I \<down>> (t - k) \<oplus> k)"
apply (case_tac "t < k")
 apply (simp add: cut_greater_all_iff iT_Plus_mem_iff)
apply (insert iT_Plus_cut_greater2[of I k "t - k"], simp)
done


lemma 
  iT_Mult_cut_le2:      "0 < k \<Longrightarrow> (I \<otimes> k) \<down>\<le> (t * k) = (I \<down>\<le> t) \<otimes> k" and
  iT_Mult_cut_less2:    "0 < k \<Longrightarrow> (I \<otimes> k) \<down>< (t * k) = (I \<down>< t) \<otimes> k" and
  iT_Mult_cut_ge2:      "0 < k \<Longrightarrow> (I \<otimes> k) \<down>\<ge> (t * k) = (I \<down>\<ge> t) \<otimes> k" and
  iT_Mult_cut_greater2: "0 < k \<Longrightarrow> (I \<otimes> k) \<down>> (t * k) = (I \<down>> t) \<otimes> k"
unfolding iT_Mult_def by fastforce+

lemma iT_Mult_cut_le: "
  0 < k \<Longrightarrow> (I \<otimes> k) \<down>\<le> t = (I \<down>\<le> (t div k)) \<otimes> k"
apply (clarsimp simp: set_eq_iff iT_Mult_mem_iff cut_le_mem_iff)
apply (rule conj_cong, simp)+
apply (rule iffI)
 apply (simp add: div_le_mono)
apply (rule div_le_mod_le_imp_le, simp+)
done

lemma iT_Mult_cut_less: "
  0 < k \<Longrightarrow> (I \<otimes> k) \<down>< t = 
    (if t mod k = 0 then (I \<down>< (t div k)) else I \<down>< Suc (t div k)) \<otimes> k"
apply (case_tac "t mod k = 0")
 apply (clarsimp simp add: mult.commute[of k] iT_Mult_cut_less2 elim!: dvdE)
apply (clarsimp simp: set_eq_iff iT_Mult_mem_iff cut_less_mem_iff)
apply (rule conj_cong, simp)+
apply (subst less_Suc_eq_le)
apply (rule iffI)
 apply (rule div_le_mono, simp)
apply (rule ccontr, simp add: linorder_not_less)
apply (drule le_imp_less_or_eq[of t], erule disjE)
 apply (fastforce dest: less_mod_0_imp_div_less[of t _ k])
apply simp
done

lemma iT_Mult_cut_greater: "
  0 < k \<Longrightarrow> (I \<otimes> k) \<down>> t = (I \<down>> (t div k)) \<otimes> k"
apply (clarsimp simp: set_eq_iff iT_Mult_mem_iff cut_greater_mem_iff)
apply (rule conj_cong, simp)+
apply (rule iffI)
 apply (simp add: less_mod_ge_imp_div_less)
apply (rule ccontr, simp add: linorder_not_less)
apply (fastforce dest: div_le_mono[of _ _ k])
done

lemma iT_Mult_cut_ge: "
  0 < k \<Longrightarrow> (I \<otimes> k) \<down>\<ge> t = 
    (if t mod k = 0 then (I \<down>\<ge> (t div k)) else I \<down>\<ge> Suc (t div k)) \<otimes> k"
apply (case_tac "t mod k = 0")
 apply (clarsimp simp add: mult.commute[of k] iT_Mult_cut_ge2 elim!: dvdE)
apply (clarsimp simp: set_eq_iff iT_Mult_mem_iff cut_ge_mem_iff)
apply (rule conj_cong, simp)+
apply (rule iffI)
 apply (rule Suc_leI)
 apply (simp add: le_mod_greater_imp_div_less)
apply (rule ccontr)
apply (drule Suc_le_lessD)
apply (simp add: linorder_not_le)
apply (fastforce dest: div_le_mono[OF order_less_imp_le, of _ t k])
done

lemma iT_Plus_neg_cut_le2: "k \<le> t \<Longrightarrow> (I \<oplus>- k) \<down>\<le> (t - k) = (I \<down>\<le> t) \<oplus>- k"
apply (simp add: iT_Plus_neg_image_conv)
apply (simp add: i_cut_commute_disj[of "(\<down>\<le>)" "(\<down>\<ge>)"])
apply (rule i_cut_image[OF sub_left_strict_mono_on])
apply (simp add: cut_ge_Int_conv)+
done

lemma iT_Plus_neg_cut_less2: "(I \<oplus>- k) \<down>< (t - k) = (I \<down>< t) \<oplus>- k"
apply (case_tac "t \<le> k")
 apply (simp add: cut_less_0_empty)
 apply (case_tac "I \<down>< t = {}")
  apply (simp add: iT_Plus_neg_empty)
 apply (rule sym, rule iT_Plus_neg_Max_less_empty[OF nat_cut_less_finite])
 apply (rule order_less_le_trans[OF cut_less_Max_less[OF nat_cut_less_finite]], assumption+)
apply (simp add: linorder_not_le iT_Plus_neg_image_conv)
apply (simp add: i_cut_commute_disj[of "(\<down><)" "(\<down>\<ge>)"])
apply (rule i_cut_image[OF sub_left_strict_mono_on])
apply (simp add: cut_ge_Int_conv)+
done

lemma iT_Plus_neg_cut_ge2: "(I \<oplus>- k) \<down>\<ge> (t - k) = (I \<down>\<ge> t) \<oplus>- k"
apply (case_tac "t \<le> k")
 apply (simp add: cut_ge_0_all iT_Plus_neg_cut_eq)
apply (simp add: linorder_not_le iT_Plus_neg_image_conv)
apply (simp add: i_cut_commute_disj[of "(\<down>\<ge>)" "(\<down>\<ge>)"])
apply (rule i_cut_image[OF sub_left_strict_mono_on])
apply (simp add: cut_ge_Int_conv)+
done

lemma iT_Plus_neg_cut_greater2: "k \<le> t \<Longrightarrow> (I \<oplus>- k) \<down>> (t - k) = (I \<down>> t) \<oplus>- k"
apply (simp add: iT_Plus_neg_image_conv)
apply (simp add: i_cut_commute_disj[of "(\<down>>)" "(\<down>\<ge>)"])
apply (rule i_cut_image[OF sub_left_strict_mono_on])
apply (simp add: cut_ge_Int_conv)+
done

lemma iT_Plus_neg_cut_le: "(I \<oplus>- k) \<down>\<le> t = I \<down>\<le> (t + k) \<oplus>- k"
by (insert iT_Plus_neg_cut_le2[of k "t + k" I, OF le_add2], simp)

lemma iT_Plus_neg_cut_less: "(I \<oplus>- k) \<down>< t = I \<down>< (t + k) \<oplus>- k"
by (insert iT_Plus_neg_cut_less2[of I k "t + k"], simp)

lemma iT_Plus_neg_cut_ge: "(I \<oplus>- k) \<down>\<ge> t = I \<down>\<ge> (t + k) \<oplus>- k"
by (insert iT_Plus_neg_cut_ge2[of I k "t + k"], simp)

lemma iT_Plus_neg_cut_greater: "(I \<oplus>- k) \<down>> t = I \<down>> (t + k) \<oplus>- k"
by (insert iT_Plus_neg_cut_greater2[of k "t + k" I], simp)


lemma iT_Minus_cut_le2: "t \<le> k \<Longrightarrow> (k \<ominus> I) \<down>\<le> (k - t) = k \<ominus> (I \<down>\<ge> t)"
by (fastforce simp: i_cut_mem_iff iT_Minus_mem_iff)

lemma iT_Minus_cut_less2: "(k \<ominus> I) \<down>< (k - t) = k \<ominus> (I \<down>> t)"
by (fastforce simp: i_cut_mem_iff iT_Minus_mem_iff)

lemma iT_Minus_cut_ge2: "(k \<ominus> I) \<down>\<ge> (k - t) = k \<ominus> (I \<down>\<le> t)"
by (fastforce simp: i_cut_mem_iff iT_Minus_mem_iff)

lemma iT_Minus_cut_greater2: "t \<le> k \<Longrightarrow> (k \<ominus> I) \<down>> (k - t) = k \<ominus> (I \<down>< t)"
by (fastforce simp: i_cut_mem_iff iT_Minus_mem_iff)

lemma iT_Minus_cut_le: "(k \<ominus> I) \<down>\<le> t = k \<ominus> (I \<down>\<ge> (k - t))"
by (fastforce simp: i_cut_mem_iff iT_Minus_mem_iff)

lemma iT_Minus_cut_less: "
  (k \<ominus> I) \<down>< t = (if t \<le> k then k \<ominus> (I \<down>> (k - t)) else k \<ominus> I)"
apply (case_tac "t \<le> k")
 apply (cut_tac iT_Minus_cut_less2[of k I "k - t"], simp)
apply (fastforce simp: i_cut_mem_iff iT_Minus_mem_iff)
done

lemma iT_Minus_cut_ge: "
  (k \<ominus> I) \<down>\<ge> t = (if t \<le> k then k \<ominus> (I \<down>\<le> (k - t)) else {})"
apply (case_tac "t \<le> k")
 apply (cut_tac iT_Minus_cut_ge2[of k I "k - t"], simp)
apply (fastforce simp: i_cut_mem_iff iT_Minus_mem_iff)
done

lemma iT_Minus_cut_greater: "(k \<ominus> I) \<down>> t = k \<ominus> (I \<down>< (k - t))"
apply (case_tac "t \<le> k")
 apply (cut_tac iT_Minus_cut_greater2[of "k - t" k I], simp+)
apply (fastforce simp: i_cut_mem_iff iT_Minus_mem_iff)
done


lemma iT_Div_cut_le: "
  0 < k \<Longrightarrow> (I \<oslash> k) \<down>\<le> t = I \<down>\<le> (t * k + (k - Suc 0)) \<oslash> k"
apply (simp add: set_eq_iff i_cut_mem_iff iT_Div_mem_iff Bex_def)
apply (fastforce simp: div_le_conv)
done

lemma iT_Div_cut_less: "
  0 < k \<Longrightarrow> (I \<oslash> k) \<down>< t = I \<down>< (t * k) \<oslash> k"
apply (case_tac "t = 0")
 apply (simp add: cut_less_0_empty iT_Div_empty)
apply (simp add: nat_cut_less_le_conv iT_Div_cut_le diff_mult_distrib)
done

lemma iT_Div_cut_ge: "
  0 < k \<Longrightarrow> (I \<oslash> k) \<down>\<ge> t = I \<down>\<ge> (t * k) \<oslash> k"
apply (simp add: set_eq_iff i_cut_mem_iff iT_Div_mem_iff Bex_def)
apply (fastforce simp: le_div_conv)
done

lemma iT_Div_cut_greater: "
  0 < k \<Longrightarrow> (I \<oslash> k) \<down>> t = I \<down>> (t * k + (k - Suc 0)) \<oslash> k"
by (simp add: nat_cut_ge_greater_conv[symmetric] iT_Div_cut_ge add.commute[of k])


lemma iT_Div_cut_le2: "
  0 < k \<Longrightarrow> (I \<oslash> k) \<down>\<le> (t div k) = I \<down>\<le> (t - t mod k + (k - Suc 0)) \<oslash> k"
by (frule iT_Div_cut_le[of k I "t div k"], simp add: div_mult_cancel)

lemma iT_Div_cut_less2: "
  0 < k \<Longrightarrow> (I \<oslash> k) \<down>< (t div k) = I \<down>< (t - t mod k) \<oslash> k"
by (frule iT_Div_cut_less[of k I "t div k"], simp add: div_mult_cancel)

lemma iT_Div_cut_ge2: "
  0 < k \<Longrightarrow> (I \<oslash> k) \<down>\<ge> (t div k) = I \<down>\<ge> (t - t mod k) \<oslash> k"
by (frule iT_Div_cut_ge[of k I "t div k"], simp add: div_mult_cancel)

lemma iT_Div_cut_greater2: "
  0 < k \<Longrightarrow> (I \<oslash> k) \<down>> (t div k) = I \<down>> (t - t mod k + (k - Suc 0)) \<oslash> k"
by (frule iT_Div_cut_greater[of k I "t div k"], simp add: div_mult_cancel)


subsection \<open>\<open>inext\<close> and \<open>iprev\<close> with interval operators\<close>

lemma iT_Plus_inext: "inext (n + k) (I \<oplus> k) = (inext n I) + k"
by (unfold iT_Plus_def, rule inext_image2[OF add_right_strict_mono])

lemma iT_Plus_iprev: "iprev (n + k) (I \<oplus> k) = (iprev n I) + k"
by (unfold iT_Plus_def, rule iprev_image2[OF add_right_strict_mono])

lemma iT_Plus_inext2: "k \<le> n \<Longrightarrow> inext n (I \<oplus> k) = (inext (n - k) I) + k"
by (insert iT_Plus_inext[of "n - k" k I], simp)
lemma iT_Plus_prev2: "k \<le> n \<Longrightarrow> iprev n (I \<oplus> k) = (iprev (n - k) I) + k"
by (insert iT_Plus_iprev[of "n - k" k I], simp)


lemma iT_Mult_inext: "inext (n * k) (I \<otimes> k) = (inext n I) * k"
apply (case_tac "I = {}")
 apply (simp add: iT_Mult_empty inext_empty)
apply (case_tac "k = 0")
 apply (simp add: iT_Mult_0 iTILL_0 inext_singleton)
apply (simp add: iT_Mult_def inext_image2[OF mult_right_strict_mono])
done

lemma iT_Mult_iprev: "iprev (n * k) (I \<otimes> k) = (iprev n I) * k"
apply (case_tac "I = {}")
 apply (simp add: iT_Mult_empty iprev_empty)
apply (case_tac "k = 0")
 apply (simp add: iT_Mult_0 iTILL_0 iprev_singleton)
apply (simp add: iT_Mult_def iprev_image2[OF mult_right_strict_mono])
done

lemma iT_Mult_inext2_if: "
  inext n (I \<otimes> k) = (if n mod k = 0 then (inext (n div k) I) * k else n)"
apply (case_tac "I = {}")
 apply (simp add: iT_Mult_empty inext_empty div_mult_cancel)
apply (case_tac "k = 0")
 apply (simp add: iT_Mult_0 iTILL_0 inext_singleton)
apply (case_tac "n mod k = 0")
 apply (clarsimp simp: mult.commute[of k] iT_Mult_inext elim!: dvdE)
apply (simp add: not_in_inext_fix iT_Mult_mem_iff)
done

lemma iT_Mult_iprev2_if: "
  iprev n (I \<otimes> k) = (if n mod k = 0 then (iprev (n div k) I) * k else n)"
apply (case_tac "I = {}")
 apply (simp add: iT_Mult_empty iprev_empty div_mult_cancel)
apply (case_tac "k = 0")
 apply (simp add: iT_Mult_0 iTILL_0 iprev_singleton)
apply (case_tac "n mod k = 0")
 apply (clarsimp simp: mult.commute[of k] iT_Mult_iprev elim!: dvdE)
apply (simp add: not_in_iprev_fix iT_Mult_mem_iff)
done

corollary iT_Mult_inext2: "
  n mod k = 0 \<Longrightarrow> inext n (I \<otimes> k) = (inext (n div k) I) * k"
by (simp add: iT_Mult_inext2_if)

corollary iT_Mult_iprev2: "
  n mod k = 0 \<Longrightarrow> iprev n (I \<otimes> k) = (iprev (n div k) I) * k"
by (simp add: iT_Mult_iprev2_if)

lemma iT_Plus_neg_inext: "
  k \<le> n \<Longrightarrow> inext (n - k) (I \<oplus>- k) = inext n I - k"
apply (case_tac "I = {}")
 apply (simp add: iT_Plus_neg_empty inext_empty)
apply (case_tac "n \<in> I")
 apply (simp add: iT_Plus_neg_image_conv)
 apply (rule subst[OF inext_cut_ge_conv, of k], simp)
 apply (rule inext_image)
  apply (simp add: cut_ge_mem_iff)
 apply (subst cut_ge_Int_conv)
 apply (rule strict_mono_on_subset[OF _ Int_lower2])
 apply (rule sub_left_strict_mono_on)
apply (subgoal_tac "n - k \<notin> I \<oplus>- k")
 prefer 2
 apply (simp add: iT_Plus_neg_mem_iff)
apply (simp add: not_in_inext_fix)
done

lemma iT_Plus_neg_iprev: "
  iprev (n - k) (I \<oplus>- k) = iprev n (I \<down>\<ge> k) - k"
apply (case_tac "I = {}")
 apply (simp add: iT_Plus_neg_empty i_cut_empty iprev_empty)
apply (case_tac "n < k")
 apply (simp add: iprev_le_iMin)
 apply (simp add: order_trans[OF iprev_mono])
apply (simp add: linorder_not_less)
apply (case_tac "n \<in> I")
 apply (frule iT_Plus_neg_mem_iff2[THEN iffD2, of _ _ I], assumption)
 apply (simp add: iT_Plus_neg_image_conv)
 apply (rule iprev_image)
  apply (simp add: cut_ge_mem_iff)
 apply (subst cut_ge_Int_conv)
 apply (rule strict_mono_on_subset[OF _ Int_lower2])
 apply (rule sub_left_strict_mono_on)
apply (frule cut_ge_not_in_imp[of _ _ k])
apply (subgoal_tac "n - k \<notin> I \<oplus>- k")
 prefer 2
 apply (simp add: iT_Plus_neg_mem_iff)
apply (simp add: not_in_iprev_fix)
done

corollary iT_Plus_neg_inext2: "inext n (I \<oplus>- k) = inext (n + k) I - k"
by (insert iT_Plus_neg_inext[of k "n + k" I, OF le_add2], simp)

corollary iT_Plus_neg_iprev2: "iprev n (I \<oplus>- k) = iprev (n + k) (I \<down>\<ge> k) - k"
by (insert iT_Plus_neg_iprev[of "n + k" k I], simp)


lemma iT_Minus_inext: "
  \<lbrakk> k \<ominus> I \<noteq> {}; n \<le> k \<rbrakk> \<Longrightarrow> inext (k - n) (k \<ominus> I) = k - iprev n I"
apply (subgoal_tac "iMin I \<le> k")
 prefer 2
 apply (simp add: iT_Minus_empty_iff)
apply (subgoal_tac "I \<down>\<le> k \<noteq> {}")
 prefer 2
 apply (simp add: iT_Minus_empty_iff cut_le_Min_not_empty)
apply (case_tac "n \<in> I")
 apply (simp add: iT_Minus_imirror_conv)
 apply (simp add: iT_Plus_neg_inext2)
 apply (subgoal_tac "n \<le> iMin I + Max (I \<down>\<le> k)")
  prefer 2
  apply (rule trans_le_add2)
  apply (rule Max_ge[OF nat_cut_le_finite])
  apply (simp add: cut_le_mem_iff)
 apply (simp add: diff_add_assoc del: add_diff_assoc)
 apply (subst add.commute[of k], subst iT_Plus_inext)
 apply (simp add: cut_le_Min_eq[of I, symmetric])
 apply (fold nat_mirror_def mirror_elem_def)
 apply (simp add: inext_imirror_iprev_conv[OF nat_cut_le_finite])
 apply (simp add: iprev_cut_le_conv)
 apply (simp add: mirror_elem_def nat_mirror_def)
 apply (frule iprev_mono[THEN order_trans, of n "iMin (I \<down>\<le> k) + Max (I \<down>\<le> k)" I])
 apply simp
apply (subgoal_tac "k - n \<notin> k \<ominus> I")
 prefer 2
 apply (simp add: iT_Minus_mem_iff)
apply (simp add: not_in_inext_fix not_in_iprev_fix)
done

corollary iT_Minus_inext2: "
  \<lbrakk> k \<ominus> I \<noteq> {}; n \<le> k \<rbrakk> \<Longrightarrow> inext n (k \<ominus> I) = k - iprev (k - n) I"
by (insert iT_Minus_inext[of k I "k - n"], simp)

lemma iT_Minus_iprev: "
  \<lbrakk> k \<ominus> I \<noteq> {}; n \<le> k \<rbrakk> \<Longrightarrow> iprev (k - n) (k \<ominus> I) = k - inext n (I \<down>\<le> k)"
apply (subgoal_tac "I \<down>\<le> k \<noteq> {}")
 prefer 2
 apply (simp add: iT_Minus_empty_iff cut_le_Min_not_empty)
apply (subst iT_Minus_cut_eq[OF le_refl, of _ I, symmetric])
apply (insert iT_Minus_inext2[of k "k \<ominus> (I \<down>\<le> k)" n])
apply (simp add: iT_Minus_Minus_cut_eq)
apply (rule diff_diff_cancel[symmetric])
apply (rule order_trans[OF iprev_mono])
apply simp
done

lemma iT_Minus_iprev2: "
  \<lbrakk> k \<ominus> I \<noteq> {}; n \<le> k \<rbrakk> \<Longrightarrow> iprev n (k \<ominus> I) = k - inext (k - n) (I \<down>\<le> k)"
by (insert iT_Minus_iprev[of k I "k - n"], simp)


lemma iT_Plus_inext_nth: "I \<noteq> {} \<Longrightarrow> (I \<oplus> k) \<rightarrow> n = (I \<rightarrow> n) + k"
apply (induct n)
 apply (simp add: iT_Plus_Min)
apply (simp add: iT_Plus_inext)
done

lemma iT_Plus_iprev_nth: "\<lbrakk> finite I; I \<noteq> {} \<rbrakk> \<Longrightarrow> (I \<oplus> k) \<leftarrow> n = (I \<leftarrow> n) + k"
apply (induct n)
 apply (simp add: iT_Plus_Max)
apply (simp add: iT_Plus_iprev)
done

lemma iT_Mult_inext_nth: "I \<noteq> {} \<Longrightarrow> (I \<otimes> k) \<rightarrow> n = (I \<rightarrow> n) * k"
apply (induct n)
 apply (simp add: iT_Mult_Min)
apply (simp add: iT_Mult_inext)
done

lemma iT_Mult_iprev_nth: "\<lbrakk> finite I; I \<noteq> {} \<rbrakk> \<Longrightarrow> (I \<otimes> k) \<leftarrow> n = (I \<leftarrow> n) * k"
apply (induct n)
 apply (simp add: iT_Mult_Max)
apply (simp add: iT_Mult_iprev)
done

lemma iT_Plus_neg_inext_nth: "
  I \<oplus>- k \<noteq> {} \<Longrightarrow> (I \<oplus>- k) \<rightarrow> n = (I \<down>\<ge> k \<rightarrow> n) - k"
apply (subgoal_tac "I \<down>\<ge> k \<noteq> {}")
 prefer 2
 apply (simp add: cut_ge_not_empty_iff iT_Plus_neg_not_empty_iff)
apply (induct n)
 apply (simp add: iT_Plus_neg_Min)
apply (simp add: iT_Plus_neg_cut_eq[of k k I, symmetric])
apply (rule iT_Plus_neg_inext)
apply (rule cut_ge_bound[of _ I])
apply (simp add: inext_nth_closed)
done

lemma iT_Plus_neg_iprev_nth: "
  \<lbrakk> finite I; I \<oplus>- k \<noteq> {} \<rbrakk> \<Longrightarrow> (I \<oplus>- k) \<leftarrow> n = (I \<down>\<ge> k \<leftarrow> n) - k"
apply (subgoal_tac "I \<down>\<ge> k \<noteq> {}")
 prefer 2
 apply (simp add: cut_ge_not_empty_iff iT_Plus_neg_not_empty_iff)
apply (induct n)
 apply (simp add: iT_Plus_neg_Max cut_ge_Max_eq)
apply (simp add: iT_Plus_neg_iprev)
done

lemma iT_Minus_inext_nth: "
  k \<ominus> I \<noteq> {} \<Longrightarrow> (k \<ominus> I) \<rightarrow> n = k - ((I \<down>\<le> k) \<leftarrow> n)"
apply (subgoal_tac "I \<down>\<le> k \<noteq> {} \<and> I \<noteq> {} \<and> iMin I \<le> k")
 prefer 2
 apply (simp add: iT_Minus_empty_iff cut_le_Min_not_empty)
apply (elim conjE)
apply (induct n)
 apply(simp add: iT_Minus_Min)
apply (simp add: iT_Minus_cut_eq[OF order_refl, of _ I, symmetric])
apply (rule iT_Minus_inext)
 apply simp
apply (rule cut_le_bound, rule iprev_nth_closed[OF nat_cut_le_finite])
apply assumption
done

lemma iT_Minus_iprev_nth: "
  k \<ominus> I \<noteq> {} \<Longrightarrow> (k \<ominus> I) \<leftarrow> n = k - ((I \<down>\<le> k) \<rightarrow> n)"
apply (subgoal_tac "I \<down>\<le> k \<noteq> {} \<and> I \<noteq> {} \<and> iMin I \<le> k")
 prefer 2
 apply (simp add: iT_Minus_empty_iff cut_le_Min_not_empty)
apply (elim conjE)
apply (induct n)
 apply(simp add: iT_Minus_Max cut_le_Min_eq)
apply simp
apply (rule iT_Minus_iprev)
 apply simp
apply (rule cut_le_bound, rule inext_nth_closed)
apply assumption
done

lemma iT_Div_ge_inext_nth: "
  \<lbrakk> I \<noteq> {}; \<forall>x\<in>I. \<forall>y\<in>I. x < y \<longrightarrow> x + k \<le> y \<rbrakk> \<Longrightarrow>
  (I \<oslash> k) \<rightarrow> n = (I \<rightarrow> n) div k"
apply (case_tac "k = 0")
 apply (simp add: iT_Div_0 iTILL_0 inext_nth_singleton)
apply (simp add: iT_Div_def)
by (rule inext_nth_image[OF _ div_right_strict_mono_on])

lemma iT_Div_mod_inext_nth: "
  \<lbrakk> I \<noteq> {}; \<forall>x\<in>I. \<forall>y\<in>I. x mod k = y mod k \<rbrakk> \<Longrightarrow>
  (I \<oslash> k) \<rightarrow> n = (I \<rightarrow> n) div k"
apply (case_tac "k = 0")
 apply (simp add: iT_Div_0 iTILL_0 inext_nth_singleton)
apply (simp add: iT_Div_def)
by (rule inext_nth_image[OF _ mod_eq_div_right_strict_mono_on])

lemma iT_Div_ge_iprev_nth: "
  \<lbrakk> finite I; I \<noteq> {}; \<forall>x\<in>I. \<forall>y\<in>I. x < y \<longrightarrow> x + k \<le> y \<rbrakk> \<Longrightarrow>
  (I \<oslash> k) \<leftarrow> n = (I \<leftarrow> n) div k"
apply (case_tac "k = 0")
 apply (simp add: iT_Div_0 iTILL_0 iprev_nth_singleton)
apply (simp add: iT_Div_def)
by (rule iprev_nth_image[OF _ _ div_right_strict_mono_on])

lemma iT_Div_mod_iprev_nth: "
  \<lbrakk> finite I; I \<noteq> {}; \<forall>x\<in>I. \<forall>y\<in>I. x mod k = y mod k \<rbrakk> \<Longrightarrow>
  (I \<oslash> k) \<leftarrow> n = (I \<leftarrow> n) div k"
apply (case_tac "k = 0")
 apply (simp add: iT_Div_0 iTILL_0 iprev_nth_singleton)
apply (simp add: iT_Div_def)
by (rule iprev_nth_image[OF _ _ mod_eq_div_right_strict_mono_on])





subsection \<open>Cardinality of intervals with interval operators\<close>

lemma iT_Plus_card: "card (I \<oplus> k) = card I"
apply (unfold iT_Plus_def)
apply (rule card_image)
apply (rule inj_imp_inj_on)
apply (rule add_right_inj)
done
lemma iT_Mult_card: "0 < k \<Longrightarrow> card (I \<otimes> k) = card I"
apply (unfold iT_Mult_def)
apply (rule card_image)
apply (rule inj_imp_inj_on)
apply (rule mult_right_inj)
apply assumption
done

lemma iT_Plus_neg_card: "card (I \<oplus>- k) = card (I \<down>\<ge> k)"
apply (simp add: iT_Plus_neg_image_conv)
apply (rule card_image)
apply (subst cut_ge_Int_conv)
apply (rule subset_inj_on[OF _ Int_lower2])
apply (rule sub_left_inj_on)
done

lemma iT_Plus_neg_card_le: "card (I \<oplus>- k) \<le> card I"
apply (simp add: iT_Plus_neg_card)
apply (case_tac "finite I")
 apply (rule cut_ge_card, assumption)
apply (simp add: nat_cut_ge_finite_iff)
done

lemma iT_Minus_card: "card (k \<ominus> I) = card (I \<down>\<le> k)"
apply (simp add: iT_Minus_image_conv)
apply (rule card_image)
apply (subst cut_le_Int_conv)
apply (rule subset_inj_on[OF _ Int_lower2])
apply (rule sub_right_inj_on)
done

lemma iT_Minus_card_le: "finite I \<Longrightarrow> card (k \<ominus> I) \<le> card I"
by (subst iT_Minus_card, rule cut_le_card)

lemma iT_Div_0_card_if: "
  card (I \<oslash> 0) = (if I ={} then 0 else Suc 0)"
by (fastforce simp: iT_Div_empty iT_Div_0 iTILL_0)

lemma Int_empty_sum:"
  (\<Sum>k\<le>(n::nat). if {} \<inter> (I k) = {} then 0 else Suc 0) = 0"
apply (rule sum_eq_0_iff[THEN iffD2])
 apply (rule finite_atMost)
apply simp
done

lemma iT_Div_mod_partition_card:"
  card (I \<inter> [n * d\<dots>,d - Suc 0] \<oslash> d) =
  (if I \<inter> [n * d\<dots>,d - Suc 0] = {} then 0 else Suc 0)"
apply (case_tac "d = 0")
 apply (simp add: iIN_0 iTILL_0 iT_Div_0_if)
apply (split if_split, rule conjI)
 apply (simp add: iT_Div_empty)
apply clarsimp
apply (subgoal_tac "I \<inter> [n * d\<dots>,d - Suc 0] \<oslash> d = {n}", simp)
apply (rule set_eqI)
apply (simp add: iT_Div_mem_iff Bex_def iIN_iff)
apply (rule iffI)
 apply (clarsimp simp: le_less_imp_div)
apply (drule ex_in_conv[THEN iffD2], clarsimp simp: iIN_iff, rename_tac x')
apply (rule_tac x=x' in exI)
apply (simp add: le_less_imp_div)
done

lemma iT_Div_conv_count: "
  0 < d \<Longrightarrow> I \<oslash> d = {k. I \<inter> [k * d\<dots>,d - Suc 0] \<noteq> {}}"
apply (case_tac "I = {}")
 apply (simp add: iT_Div_empty)
apply (rule set_eqI)
apply (simp add: iT_Div_mem_iff_Int)
done

lemma iT_Div_conv_count2: "
  \<lbrakk> 0 < d; finite I; Max I div d \<le> n \<rbrakk> \<Longrightarrow> 
  I \<oslash> d = {k. k \<le> n \<and> I \<inter> [k * d\<dots>,d - Suc 0] \<noteq> {}}"
apply (simp add: iT_Div_conv_count)
apply (rule set_eqI, simp)
apply (rule iffI)
 apply simp
 apply (rule ccontr)
 apply (drule ex_in_conv[THEN iffD2], clarify, rename_tac x')
 apply (clarsimp simp: linorder_not_le iIN_iff)
 apply (drule order_le_less_trans, simp)
 apply (drule div_less_conv[THEN iffD1, of _ "Max I"], simp)
 apply (drule_tac x=x' in Max_ge, simp)
 apply simp+
done

lemma mod_partition_count_Suc: "
  {k. k \<le> Suc n \<and> I \<inter> [k * d\<dots>,d - Suc 0] \<noteq> {}} = 
  {k. k \<le> n \<and> I \<inter> [k * d\<dots>,d - Suc 0] \<noteq> {}} \<union> 
    (if I \<inter> [Suc n * d\<dots>,d - Suc 0] \<noteq> {} then {Suc n} else {})"
apply (rule set_eqI, rename_tac x)
apply (simp add: le_less[of _ "Suc n"] less_Suc_eq_le)
apply (simp add: conj_disj_distribR)
apply (intro conjI impI)
 apply fastforce
apply (rule iffI, clarsimp+)
done

lemma iT_Div_card: "
  \<And>I.\<lbrakk> 0 < d; finite I; Max I div d \<le> n\<rbrakk> \<Longrightarrow>
  card (I \<oslash> d) = (\<Sum>k\<le>n. 
    if I \<inter> [k * d\<dots>,d - Suc 0] = {} then 0 else Suc 0)"
apply (case_tac "I = {}")
 apply (simp add: iT_Div_empty)
apply (simp add: iT_Div_conv_count2)
apply (induct n)
 apply (simp add: div_eq_0_conv iIN_0_iTILL_conv)
 apply (subgoal_tac "I \<inter> [\<dots>d - Suc 0] \<noteq> {}")
  prefer 2
  apply (simp add: ex_in_conv[symmetric], fastforce)
 apply (simp add: card_1_singleton_conv)
 apply (rule_tac x=0 in exI)
 apply (rule set_eqI)
 apply (simp add: ex_in_conv[symmetric], fastforce)
apply simp
apply (simp add: mod_partition_count_Suc)
apply (drule_tac x="I \<inter> [\<dots>n * d + d - Suc 0]" in meta_spec)
apply simp
apply (case_tac "I \<inter> [\<dots>n * d + d - Suc 0] = {}")
 apply simp
 apply (subgoal_tac "{k. k \<le> n \<and> I \<inter> [k * d\<dots>,d - Suc 0] \<noteq> {}} = {}", simp)
 apply (clarsimp, rename_tac x)
 apply (subgoal_tac "I \<inter> [x * d\<dots>,d - Suc 0] \<subseteq> I \<inter> [\<dots>n * d + d - Suc 0]", simp)
 apply (rule Int_mono[OF order_refl])
 apply (simp add: iIN_iTILL_subset_conv)
 apply (simp add: diff_le_mono)
apply (subgoal_tac "Max (I \<inter> [\<dots>n * d + d - Suc 0]) div d \<le> n")
 prefer 2
 apply (simp add: div_le_conv add.commute[of d] iTILL_iff)
apply (subgoal_tac "\<And>k. k \<le> n \<Longrightarrow> [\<dots>n * d + d - Suc 0] \<inter> [k * d\<dots>,d - Suc 0] = [k * d\<dots>,d - Suc 0]")
 prefer 2
 apply (subst Int_commute)
 apply (simp add: iTILL_def cut_le_Int_conv[symmetric])
 apply (rule cut_le_Max_all[OF iIN_finite])
 apply (simp add: iIN_Max diff_le_mono)
apply (simp add: Int_assoc)
apply (subgoal_tac "
  {k. k \<le> n \<and> I \<inter> ([\<dots>n * d + d - Suc 0] \<inter> [k * d\<dots>,d - Suc 0]) \<noteq> {}} =
  {k. k \<le> n \<and> I \<inter> [k * d\<dots>,d - Suc 0] \<noteq> {}}")
 prefer 2
 apply (rule set_eqI, rename_tac x)
 apply simp
 apply (rule conj_cong, simp)
 apply simp
apply simp
done

corollary iT_Div_card_Suc: "
  \<And>I.\<lbrakk> 0 < d; finite I; Max I div d \<le> n\<rbrakk> \<Longrightarrow>
  card (I \<oslash> d) = (\<Sum>k<Suc n. 
    if I \<inter> [k * d\<dots>,d - Suc 0] = {} then 0 else Suc 0)"
by (simp add: lessThan_Suc_atMost iT_Div_card)
corollary iT_Div_Max_card: "\<lbrakk> 0 < d; finite I \<rbrakk> \<Longrightarrow> 
  card (I \<oslash> d) = (\<Sum>k\<le>Max I div d.
    if I \<inter> [k * d\<dots>,d - Suc 0] = {} then 0 else Suc 0)"
by (simp add: iT_Div_card)

lemma iT_Div_card_le: "0 < k \<Longrightarrow> card (I \<oslash> k) \<le> card I"
apply (case_tac "finite I")
 apply (simp add: iT_Div_def card_image_le)
apply (simp add: iT_Div_finite_iff)
done

lemma iT_Div_card_inj_on: "
  inj_on (\<lambda>n. n div k) I \<Longrightarrow> card (I \<oslash> k) = card I"
by (unfold iT_Div_def, rule card_image)

(*
lemma "let I=[\<dots>19] in 
  d \<in> {1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21} \<longrightarrow>
  card I div d \<le> card (I \<oslash> d)"
apply (simp add: Let_def iTILL_card iTILL_div)
done
lemma "let I=[\<dots>19] in 
  d \<in> {1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21} \<longrightarrow>
  card I div d + (if card I mod d \<noteq> 0 then 1 else 0) \<le> card (I \<oslash> d)"
apply (simp add: Let_def iTILL_card iTILL_div)
done
lemma "let I=[5\<dots>,19] in 
  d \<in> {1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21} \<longrightarrow>
  card I div d + (if card I mod d \<noteq> 0 then 1 else 0) \<le> card (I \<oslash> d)"
apply (simp add: Let_def iIN_card iIN_div)
done
*)


(* ToDo: to be moved to Util_Div *)

lemma mod_Suc': "
  0 < n \<Longrightarrow> Suc m mod n = (if m mod n < n - Suc 0 then Suc (m mod n) else 0)"
apply (simp add: mod_Suc)
apply (intro conjI impI)
 apply simp
apply (insert le_neq_trans[OF mod_less_divisor[THEN Suc_leI, of n m]], simp)
done

lemma div_Suc: "
  0 < n \<Longrightarrow> Suc m div n = (if Suc (m mod n) = n then Suc (m div n) else m div n)"
apply (drule Suc_leI, drule le_imp_less_or_eq)
apply (case_tac "n = Suc 0", simp)
apply (split if_split, intro conjI impI)
 apply (rule_tac t="Suc m" and s="m + 1" in subst, simp)
 apply (subst div_add1_eq2, simp+)
apply (insert le_neq_trans[OF mod_less_divisor[THEN Suc_leI, of n m]], simp)
apply (rule_tac t="Suc m" and s="m + 1" in subst, simp)
apply (subst div_add1_eq1, simp+)
done

lemma div_Suc': "
  0 < n \<Longrightarrow> Suc m div n = (if m mod n < n - Suc 0 then m div n else Suc (m div n))"
apply (simp add: div_Suc)
apply (intro conjI impI)
 apply simp
apply (insert le_neq_trans[OF mod_less_divisor[THEN Suc_leI, of n m]], simp)
done

lemma iT_Div_card_ge_aux: "
  \<And>I. \<lbrakk> 0 < d; finite I; Max I div d \<le> n \<rbrakk> \<Longrightarrow> 
  card I div d + (if card I mod d = 0 then 0 else Suc 0) \<le> card (I \<oslash> d)"
apply (induct n)
 apply (case_tac "I = {}", simp)
 apply (frule_tac m=d and n="Max I" and k=0 in div_le_conv[THEN iffD1, rule_format], assumption)
 apply (simp del: Max_le_iff)
 apply (subgoal_tac "I \<oslash> d = {0}")
  prefer 2
  apply (rule set_eqI)
  apply (simp add: iT_Div_mem_iff)
  apply (rule iffI)
   apply (fastforce simp: div_eq_0_conv')
  apply fastforce
 apply (simp add: iT_Div_singleton card_singleton del: Max_le_iff)
 apply (drule Suc_le_mono[THEN iffD2, of _ "d - Suc 0"])
 apply (drule order_trans[OF nat_card_le_Max])
 apply (simp, intro conjI impI)
  apply (drule div_le_mono[of _ d d])
  apply simp
 apply (subgoal_tac "card I \<noteq> d", simp)
 apply clarsimp
apply (drule order_le_less[THEN iffD1], erule disjE)
 apply simp
apply (rule_tac t=I and s="I \<inter> [\<dots>n * d + d - Suc 0] \<union> I \<inter> [Suc n * d\<dots>,d - Suc 0]" in subst)
 apply (simp add: Int_Un_distrib[symmetric] add.commute[of d])
 apply (subst iIN_0_iTILL_conv[symmetric])
 apply (simp add: iIN_union)
 apply (rule Int_absorb2)
 apply (simp add: iIN_0_iTILL_conv iTILL_def)
 apply (case_tac "I = {}", simp)
 apply (simp add: subset_atMost_Max_le_conv le_less_div_conv[symmetric] less_eq_le_pred[symmetric] add.commute[of d])
apply (cut_tac A="I \<inter> [\<dots>n * d + d - Suc 0]" and B="I \<inter> [Suc n * d\<dots>,d - Suc 0]" in card_Un_disjoint)
   apply simp
  apply simp
 apply (clarsimp simp: disjoint_iff_in_not_in1 iT_iff)
apply (case_tac "I \<inter> [\<dots>n * d + d - Suc 0] = {}")
 apply (simp add: iT_Div_mod_partition_card del: mult_Suc)
 apply (intro conjI impI)
  apply (rule div_le_conv[THEN iffD2], assumption)
  apply simp
  apply (rule order_trans[OF Int_card2[OF iIN_finite]])
  apply (simp add: iIN_card)
 apply (cut_tac A=I and n="Suc n * d" and d="d - Suc 0" in Int_card2[OF iIN_finite, rule_format])
 apply (simp add: iIN_card)
 apply (drule order_le_less[THEN iffD1], erule disjE)
  apply simp
 apply simp
apply (subgoal_tac "Max (I \<inter> [\<dots>n * d + d - Suc 0]) div d \<le> n")
 prefer 2
 apply (rule div_le_conv[THEN iffD2], assumption)
 apply (rule order_trans[OF Max_Int_le2[OF _ iTILL_finite]], assumption)
 apply (simp add: iTILL_Max)
apply (simp only: iT_Div_Un)
apply (cut_tac A="I \<inter> [\<dots>n * d + d - Suc 0] \<oslash> d" and B="I \<inter> [Suc n * d\<dots>,d - Suc 0] \<oslash> d" in card_Un_disjoint)
   apply (simp add: iT_Div_finite_iff)
  apply (simp add: iT_Div_finite_iff)
 apply (subst iIN_0_iTILL_conv[symmetric])
 apply (subst mod_partition_iT_Div_Int_one_segment, simp)
 apply (cut_tac n=0 and d="n * d+d" and k=d and A=I in mod_partition_iT_Div_Int2, simp+)
 apply (rule disjoint_iff_in_not_in1[THEN iffD2])
 apply clarsimp
 apply (simp add: iIN_div_mod_eq_0)
 apply (simp add: mod_0_imp_sub_1_div_conv iIN_0_iTILL_conv iIN_0 iTILL_iff)
apply (simp only: iT_Div_mod_partition_card)
apply (subgoal_tac "finite (I \<inter> [\<dots>n * d + d - Suc 0])")
 prefer 2 
 apply simp
apply simp
apply (intro conjI impI)
 apply (rule add_le_divisor_imp_le_Suc_div)
  apply (rule add_leD1, blast)
 apply (rule Int_card2[OF iIN_finite, THEN le_trans])
 apply (simp add: iIN_card)
apply (cut_tac A=I and n="Suc n * d" and d="d - Suc 0" in Int_card2[OF iIN_finite, rule_format])
apply (simp add: iIN_card)
apply (rule_tac y="let I=I \<inter> [\<dots>n * d + d - Suc 0] in
  card I div d + (if card I mod d = 0 then 0 else Suc 0)" in order_trans)
 prefer 2
 apply (simp add: Let_def)
apply (unfold Let_def)
apply (split if_split, intro conjI impI)
 apply (subgoal_tac "card (I \<inter> [Suc n * d\<dots>,d - Suc 0]) \<noteq> d")
  prefer 2
  apply (rule ccontr, simp)
 apply (simp add: div_add1_eq1_mod_0_left)
apply (simp add: add_le_divisor_imp_le_Suc_div)
done

lemma iT_Div_card_ge: "
  card I div d + (if card I mod d = 0 then 0 else Suc 0) \<le> card (I \<oslash> d)"
apply (case_tac "I = {}", simp)
apply (case_tac "finite I")
 prefer 2
 apply simp
apply (case_tac "d = 0")
 apply (simp add: iT_Div_0 iTILL_0)
apply (simp add: iT_Div_card_ge_aux[OF _ _ order_refl])
done

corollary iT_Div_card_ge_div: "card I div d \<le> card (I \<oslash> d)"
by (rule iT_Div_card_ge[THEN add_leD1])


text \<open>
  There is no better lower bound function @{term f} for @{term "(i \<oslash> d)"} 
  with @{term "card i"} and @{term d} as arguments.\<close>
lemma iT_Div_card_ge__is_maximal_lower_bound: "
  \<forall>I d. card I div d + (if card I mod d = 0 then 0 else Suc 0) \<le> f (card I) d \<and> 
        f (card I) d \<le> card (I \<oslash> d) \<Longrightarrow> 
  f (card (I::nat set)) d = card I div d + (if card I mod d = 0 then 0 else Suc 0)"
apply (case_tac "I = {}")
 apply (erule_tac x=I in allE, erule_tac x=d in allE)
 apply (simp add: iT_Div_empty)
apply (case_tac "d = 0")
 apply (frule_tac x="{}" in spec, erule_tac x=I in allE)
 apply (erule_tac x=d in allE, erule_tac x=d in allE)
 apply (clarsimp simp: iT_Div_0 iTILL_card iT_Div_empty)
apply (rule order_antisym)
 prefer 2
 apply simp
apply (case_tac "finite I")
 prefer 2
 apply (erule_tac x=I in allE, erule_tac x=d in allE)
 apply (simp add: iT_Div_finite_iff)
apply (erule_tac x="[\<dots>card I - Suc 0]" in allE, erule_tac x=d in allE, elim conjE)
apply (frule not_empty_card_gr0_conv[THEN iffD1], assumption)
apply (simp add: iTILL_card iTILL_div)
apply (intro conjI impI)
 apply (simp add: mod_0_imp_sub_1_div_conv)
 apply (subgoal_tac "d \<le> card I")
 prefer 2
  apply (clarsimp elim!: dvdE)
 apply (drule div_le_mono[of d _ d])
 apply simp
apply (case_tac "d = Suc 0", simp)
apply (simp add: div_diff1_eq1)
done


lemma iT_Plus_icard: "icard (I \<oplus> k) = icard I"
by (simp add: iT_Plus_def icard_image)

lemma iT_Mult_icard: "0 < k \<Longrightarrow> icard (I \<otimes> k) = icard I"
apply (unfold iT_Mult_def)
apply (rule icard_image)
apply (rule inj_imp_inj_on)
apply (simp add: mult_right_inj)
done
 
lemma iT_Plus_neg_icard: "icard (I \<oplus>- k) = icard (I \<down>\<ge> k)"
apply (case_tac "finite I")
 apply (simp add: iT_Plus_neg_finite_iff cut_ge_finite icard_finite iT_Plus_neg_card)
apply (simp add: iT_Plus_neg_finite_iff nat_cut_ge_finite_iff)
done

lemma iT_Plus_neg_icard_le: "icard (I \<oplus>- k) \<le> icard I"
apply (case_tac "finite I")
 apply (simp add: iT_Plus_neg_finite_iff icard_finite iT_Plus_neg_card_le)
apply simp
done

lemma iT_Minus_icard: "icard (k \<ominus> I) = icard (I \<down>\<le> k)"
by (simp add: icard_finite iT_Minus_finite nat_cut_le_finite iT_Minus_card)
 
lemma iT_Minus_icard_le: "icard (k \<ominus> I) \<le> icard I"
apply (case_tac "finite I")
 apply (simp add: icard_finite iT_Minus_finite iT_Minus_card_le)
apply simp
done

lemma iT_Div_0_icard_if: "icard (I \<oslash> 0) = enat (if I = {} then 0 else Suc 0)"
by (simp add: icard_finite iT_Div_0_finite iT_Div_0_card_if)

lemma iT_Div_mod_partition_icard: "
  icard (I \<inter> [n * d\<dots>,d - Suc 0] \<oslash> d) =
  enat (if I \<inter> [n * d\<dots>,d - Suc 0] = {} then 0 else Suc 0)"
apply (subgoal_tac "finite (I \<inter> [n * d\<dots>,d - Suc 0] \<oslash> d)")
 prefer 2
 apply (case_tac "d = 0", simp add: iT_Div_0_finite)
 apply (simp add: iT_Div_finite_iff iIN_finite)
apply (simp add: icard_finite iT_Div_mod_partition_card)
done

lemma iT_Div_icard: "
  \<lbrakk> 0 < d; finite I \<Longrightarrow> Max I div d \<le> n\<rbrakk> \<Longrightarrow>
  icard (I \<oslash> d) = 
  (if finite I then enat (\<Sum>k\<le>n. if I \<inter> [k * d\<dots>,d - Suc 0] = {} then 0 else Suc 0) else \<infinity>)"
by (simp add: icard_finite iT_Div_finite_iff iT_Div_card)

corollary iT_Div_Max_icard: "0 < d \<Longrightarrow> 
  icard (I \<oslash> d) = (if finite I 
    then enat (\<Sum>k\<le>Max I div d. if I \<inter> [k * d\<dots>,d - Suc 0] = {} then 0 else Suc 0) else \<infinity>)"
by (simp add: iT_Div_icard)

lemma iT_Div_icard_le: "0 < k \<Longrightarrow> icard (I \<oslash> k) \<le> icard I"
apply (case_tac "finite I")
 apply (simp add: iT_Div_finite_iff icard_finite iT_Div_card_le)
apply simp
done

lemma iT_Div_icard_inj_on: "inj_on (\<lambda>n. n div k) I \<Longrightarrow> icard (I \<oslash> k) = icard I"
by (simp add: iT_Div_def icard_image)

lemma iT_Div_icard_ge: "icard I div (enat d) + enat (if icard I mod (enat d) = 0 then 0 else Suc 0) \<le> icard (I \<oslash> d)"
apply (case_tac "d = 0")
 apply (simp add: icard_finite iT_Div_0_finite)
 apply (case_tac "icard I")
  apply (fastforce simp: iT_Div_0_card_if)
 apply (simp add: iT_Div_0_card_if icard_infinite_conv infinite_imp_nonempty)
apply (case_tac "finite I")
 apply (simp add: iT_Div_finite_iff icard_finite iT_Div_card_ge)
apply (simp add: iT_Div_finite_iff)
done

corollary iT_Div_icard_ge_div: "icard I div (enat d) \<le> icard (I \<oslash> d)"
by (rule iT_Div_icard_ge[THEN iadd_ileD1])


lemma iT_Div_icard_ge__is_maximal_lower_bound: "
  \<forall>I d. icard I div (enat d) + enat (if icard I mod (enat d) = 0 then 0 else Suc 0) 
        \<le> f (icard I) d \<and> 
        f (icard I) d \<le> icard (I \<oslash> d) \<Longrightarrow> 
  f (icard (I::nat set)) d = 
  icard I div (enat d) + enat (if icard I mod (enat d) = 0 then 0 else Suc 0)"
apply (case_tac "d = 0")
 apply (drule_tac x=I in spec, drule_tac x=d in spec, erule conjE)
 apply (simp add: iT_Div_0_icard_if icard_0_eq[unfolded zero_enat_def])
apply (case_tac "finite I")
 prefer 2
 apply (drule_tac x=I in spec, drule_tac x=d in spec)
 apply simp
apply simp
apply (frule_tac iT_Div_finite_iff[THEN iffD2], assumption)
apply (cut_tac f="\<lambda>c d. the_enat (f (enat c) d)" and I=I and d=d in iT_Div_card_ge__is_maximal_lower_bound)
 apply (intro allI, rename_tac I' d')
 apply (subgoal_tac "\<And>k. f 0 k = 0")
  prefer 2
  apply (drule_tac x="{}" in spec, drule_tac x=k in spec, erule conjE)
  apply (simp add: iT_Div_empty)
 apply (drule_tac x=I' in spec, drule_tac x=d' in spec, erule conjE)
 apply (case_tac "d' = 0")
  apply (simp add: idiv_by_0 imod_by_0 iT_Div_0_card_if iT_Div_0_icard_if)
  apply (case_tac "I' = {}", simp)
  apply (case_tac "finite I'")
   apply (simp add: icard_finite)
  apply simp
 apply simp
 apply (case_tac "finite I'")
  apply (frule_tac I=I' and k=d' in iT_Div_finite_iff[THEN iffD2, rule_format], assumption)
  apply (simp add: icard_finite)
  apply (subgoal_tac "\<exists>n. f (enat (card I')) d' = enat n")
   prefer 2
   apply (rule enat_ile, assumption)
  apply clarsimp
 apply (subgoal_tac "infinite (I' \<oslash> d')")
  prefer 2
  apply (simp add: iT_Div_finite_iff)
 apply simp
apply (drule_tac x=I in spec, drule_tac x=d in spec, erule conjE)
apply (simp add: icard_finite)
apply (subgoal_tac "\<exists>n. f (enat (card I)) d = enat n")
 prefer 2
 apply (rule enat_ile, assumption)
apply clarsimp
done


subsection \<open>Results about sets of intervals\<close>

subsubsection \<open>Set of intervals without and with empty interval\<close>

definition iFROM_UN_set :: "(nat set) set"
  where "iFROM_UN_set \<equiv> \<Union>n. {[n\<dots>]}"

definition iTILL_UN_set :: "(nat set) set"
  where "iTILL_UN_set \<equiv> \<Union>n. {[\<dots>n]}"

definition iIN_UN_set   :: "(nat set) set"
  where "iIN_UN_set   \<equiv> \<Union>n d. {[n\<dots>,d]}"

definition iMOD_UN_set  :: "(nat set) set"
  where "iMOD_UN_set  \<equiv> \<Union>r m. {[r, mod m]}"

definition iMODb_UN_set :: "(nat set) set"
  where "iMODb_UN_set \<equiv> \<Union>r m c. {[r, mod m, c]}"


definition iFROM_set :: "(nat set) set"
  where "iFROM_set \<equiv> {[n\<dots>] |n. True}"

definition iTILL_set :: "(nat set) set"
  where "iTILL_set \<equiv> {[\<dots>n] |n. True}"

definition iIN_set   :: "(nat set) set"
  where "iIN_set   \<equiv> {[n\<dots>,d] |n d. True}"

definition iMOD_set  :: "(nat set) set"
  where "iMOD_set  \<equiv> {[r, mod m] |r m. True}"

definition iMODb_set :: "(nat set) set"
  where "iMODb_set \<equiv> {[r, mod m, c] |r m c. True}"


definition iMOD2_set  :: "(nat set) set"
  where "iMOD2_set  \<equiv> {[r, mod m] |r m. 2 \<le> m}"

definition iMODb2_set :: "(nat set) set"
  where "iMODb2_set \<equiv> {[r, mod m, c] |r m c. 2 \<le> m \<and> 1 \<le> c}"


definition iMOD2_UN_set  :: "(nat set) set"
  where "iMOD2_UN_set  \<equiv> \<Union>r. \<Union>m\<in>{2..}. {[r, mod m]}"

definition iMODb2_UN_set :: "(nat set) set"
  where "iMODb2_UN_set \<equiv> \<Union>r. \<Union>m\<in>{2..}. \<Union>c\<in>{1..}. {[r, mod m, c]}"

lemmas i_set_defs = 
  iFROM_set_def iTILL_set_def iIN_set_def
  iMOD_set_def iMODb_set_def
  iMOD2_set_def iMODb2_set_def
lemmas i_UN_set_defs = 
  iFROM_UN_set_def iTILL_UN_set_def iIN_UN_set_def 
  iMOD_UN_set_def iMODb_UN_set_def
  iMOD2_UN_set_def iMODb2_UN_set_def

lemma iFROM_set_UN_set_eq: "iFROM_set = iFROM_UN_set"
by (fastforce simp: iFROM_set_def iFROM_UN_set_def)

lemma 
  iTILL_set_UN_set_eq: "iTILL_set = iTILL_UN_set" and
  iIN_set_UN_set_eq:   "iIN_set = iIN_UN_set" and
  iMOD_set_UN_set_eq:  "iMOD_set = iMOD_UN_set" and
  iMODb_set_UN_set_eq: "iMODb_set = iMODb_UN_set"
by (fastforce simp: i_set_defs i_UN_set_defs)+

lemma iMOD2_set_UN_set_eq: "iMOD2_set = iMOD2_UN_set"
by (fastforce simp: i_set_defs i_UN_set_defs)

lemma iMODb2_set_UN_set_eq: "iMODb2_set = iMODb2_UN_set"
by (fastforce simp: i_set_defs i_UN_set_defs)

lemmas i_set_i_UN_set_sets_eq =
  iFROM_set_UN_set_eq
  iTILL_set_UN_set_eq
  iIN_set_UN_set_eq
  iMOD_set_UN_set_eq
  iMODb_set_UN_set_eq
  iMOD2_set_UN_set_eq
  iMODb2_set_UN_set_eq

lemma iMOD2_set_iMOD_set_subset: "iMOD2_set \<subseteq> iMOD_set"
by (fastforce simp: i_set_defs)

lemma iMODb2_set_iMODb_set_subset: "iMODb2_set \<subseteq> iMODb_set"
by (fastforce simp: i_set_defs)

definition i_set :: "(nat set) set"
  where "i_set \<equiv> iFROM_set \<union> iTILL_set \<union> iIN_set \<union> iMOD_set \<union> iMODb_set"

definition i_UN_set :: "(nat set) set"
  where "i_UN_set \<equiv> iFROM_UN_set \<union> iTILL_UN_set \<union> iIN_UN_set \<union> iMOD_UN_set \<union> iMODb_UN_set"


text \<open>Minimal definitions for @{term i_set} and @{term i_set}\<close>

definition i_set_min :: "(nat set) set"
  where "i_set_min \<equiv> iFROM_set \<union> iIN_set \<union> iMOD2_set \<union> iMODb2_set"

definition i_UN_set_min :: "(nat set) set"
  where "i_UN_set_min \<equiv> iFROM_UN_set \<union> iIN_UN_set \<union> iMOD2_UN_set \<union> iMODb2_UN_set"


definition i_set0 :: "(nat set) set"
  where "i_set0 \<equiv> insert {} i_set"


lemma i_set_i_UN_set_eq: "i_set = i_UN_set"
by (simp add: i_set_def i_UN_set_def i_set_i_UN_set_sets_eq)

lemma i_set_min_i_UN_set_min_eq: "i_set_min = i_UN_set_min"
by (simp add: i_set_min_def i_UN_set_min_def i_set_i_UN_set_sets_eq)

lemma i_set_min_eq: "i_set = i_set_min"
apply (unfold i_set_def i_set_min_def)
apply (rule equalityI)
apply (rule subsetI)
apply (simp add: i_set_defs)
apply (elim disjE)
     apply blast
    apply (fastforce simp: iIN_0_iTILL_conv[symmetric])
   apply blast
  apply (elim exE)
  apply (case_tac "2 \<le> m", blast)
  apply (simp add: nat_ge2_conv)
  apply (fastforce simp: iMOD_0 iMOD_1)
 apply (elim exE)
 apply (case_tac "1 \<le> c")
  apply (case_tac "2 \<le> m", fastforce)
  apply (simp add: nat_ge2_conv) 
  apply (fastforce simp: iMODb_mod_0 iMODb_mod_1)
 apply (fastforce simp: linorder_not_le less_Suc_eq_le iMODb_0)
apply (rule Un_mono)+
apply (simp_all add: iMOD2_set_iMOD_set_subset iMODb2_set_iMODb_set_subset)
done

corollary i_UN_set_i_UN_min_set_eq: "i_UN_set = i_UN_set_min"
by (simp add: i_set_min_eq i_set_i_UN_set_eq[symmetric] i_set_min_i_UN_set_min_eq[symmetric])

lemma i_set_min_is_minimal_let: "
  let s1 = iFROM_set; s2= iIN_set; s3= iMOD2_set; s4= iMODb2_set in
  s1 \<inter> s2 = {} \<and> s1 \<inter> s3 = {} \<and> s1 \<inter> s4 = {} \<and> 
  s2 \<inter> s3 = {} \<and> s2 \<inter> s4 = {} \<and> s3 \<inter> s4 = {}"
apply (unfold Let_def i_set_defs, intro conjI)
apply (rule disjoint_iff_in_not_in1[THEN iffD2], clarsimp simp: iT_neq)+
done

lemmas i_set_min_is_minimal = i_set_min_is_minimal_let[simplified]


inductive_set i_set_ind:: "(nat set) set"
where
  i_set_ind_FROM[intro!]:  "[n\<dots>] \<in> i_set_ind"
| i_set_ind_TILL[intro!]:  "[\<dots>n] \<in> i_set_ind"
| i_set_ind_IN[intro!]:    "[n\<dots>,d] \<in> i_set_ind"
| i_set_ind_MOD[intro!]:   "[r, mod m] \<in> i_set_ind"
| i_set_ind_MODb[intro!]:  "[r, mod m, c] \<in> i_set_ind"

inductive_set i_set0_ind :: "(nat set) set"
where
  i_set0_ind_empty[intro!] : "{} \<in> i_set0_ind"
| i_set0_ind_i_set[intro]:  "I \<in> i_set_ind \<Longrightarrow> I \<in> i_set0_ind"

text \<open>
  The introduction rule \<open>i_set0_ind_i_set\<close> is not declared a safe introduction rule,
  because it would disturb the correct usage of the \<open>safe\<close> method.\<close>

lemma i_set_ind_subset_i_set0_ind: "i_set_ind \<subseteq> i_set0_ind"
by (rule subsetI, rule i_set0_ind_i_set)

lemma 
  i_set0_ind_FROM[intro!] : "[n\<dots>] \<in> i_set0_ind" and
  i_set0_ind_TILL[intro!] : "[\<dots>n] \<in> i_set0_ind" and
  i_set0_ind_IN[intro!]   : "[n\<dots>,d] \<in> i_set0_ind" and
  i_set0_ind_MOD[intro!]  : "[r, mod m] \<in> i_set0_ind" and
  i_set0_ind_MODb[intro!] : "[r, mod m, c] \<in> i_set0_ind"
by (rule subsetD[OF i_set_ind_subset_i_set0_ind], rule i_set_ind.intros)+

lemmas i_set0_ind_intros2 = 
  i_set0_ind_empty
  i_set0_ind_FROM
  i_set0_ind_TILL
  i_set0_ind_IN
  i_set0_ind_MOD
  i_set0_ind_MODb

lemma i_set_i_set_ind_eq: "i_set = i_set_ind"
apply (rule set_eqI, unfold i_set_def i_set_defs)
apply (rule iffI, blast)
apply (induct_tac x rule: i_set_ind.induct)
apply blast+
done

lemma i_set0_i_set0_ind_eq: "i_set0 = i_set0_ind"
apply (rule set_eqI, unfold i_set0_def)
apply (simp add: i_set_i_set_ind_eq)
apply (rule iffI)
 apply blast
apply (rule_tac a=x in i_set0_ind.cases)
apply blast+
done

lemma i_set_imp_not_empty: "I \<in> i_set \<Longrightarrow> I \<noteq> {}"
apply (simp add: i_set_i_set_ind_eq)
apply (induct I rule: i_set_ind.induct)
apply (rule iT_not_empty)+
done

lemma i_set0_i_set_mem_conv: "(I \<in> i_set0) = (I \<in> i_set \<or> I = {})"
apply (simp add: i_set_i_set_ind_eq i_set0_i_set0_ind_eq)
apply (rule iffI)
apply (rule i_set0_ind.cases[of I])
apply blast+
done

lemma i_set_i_set0_mem_conv: "(I \<in> i_set) = (I \<in> i_set0 \<and> I \<noteq> {})"
apply (insert i_set_imp_not_empty[of I])
apply (fastforce simp: i_set0_i_set_mem_conv)
done

lemma i_set0_i_set_conv: "i_set0 - {{}} = i_set"
by (fastforce simp: i_set_i_set0_mem_conv)

corollary i_set_subset_i_set0: "i_set \<subseteq> i_set0"
by (simp add: i_set0_i_set_conv[symmetric])

lemma i_set_singleton: "{a} \<in> i_set"
by (fastforce simp: i_set_def iIN_set_def iIN_0[symmetric])

lemma i_set0_singleton: "{a} \<in> i_set0"
apply (rule subsetD[OF i_set_subset_i_set0])
apply (simp add: iIN_0[symmetric] i_set_i_set_ind_eq i_set_ind.intros)
done

corollary
  i_set_FROM[intro!] : "[n\<dots>] \<in> i_set" and
  i_set_TILL[intro!] : "[\<dots>n] \<in> i_set" and
  i_set_IN[intro!]   : "[n\<dots>,d] \<in> i_set" and
  i_set_MOD[intro!]  : "[r, mod m] \<in> i_set" and
  i_set_MODb[intro!] : "[r, mod m, c] \<in> i_set"
by (rule ssubst[OF i_set_i_set_ind_eq], rule i_set_ind.intros)+

lemmas i_set_intros =
  i_set_FROM
  i_set_TILL
  i_set_IN
  i_set_MOD
  i_set_MODb

lemma
  i_set0_empty[intro!]: "{} \<in> i_set0" and
  i_set0_FROM[intro!] : "[n\<dots>] \<in> i_set0" and
  i_set0_TILL[intro!] : "[\<dots>n] \<in> i_set0" and
  i_set0_IN[intro!]   : "[n\<dots>,d] \<in> i_set0" and
  i_set0_MOD[intro!]  : "[r, mod m] \<in> i_set0" and
  i_set0_MODb[intro!] : "[r, mod m, c] \<in> i_set0"
by (rule ssubst[OF i_set0_i_set0_ind_eq], rule i_set0_ind_intros2)+

lemmas i_set0_intros =
  i_set0_empty
  i_set0_FROM
  i_set0_TILL
  i_set0_IN
  i_set0_MOD
  i_set0_MODb


lemma i_set_infinite_as_iMOD:"
  \<lbrakk> I \<in> i_set; infinite I \<rbrakk> \<Longrightarrow> \<exists>r m. I = [r, mod m]"
apply (simp add: i_set_i_set_ind_eq)
apply (induct I rule: i_set_ind.induct)
apply (simp_all add: iT_finite)
apply (rule_tac x=n in exI, rule_tac x="Suc 0" in exI, simp add: iMOD_1)
apply blast
done

lemma i_set_finite_as_iMODb:"
  \<lbrakk> I \<in> i_set; finite I \<rbrakk> \<Longrightarrow> \<exists>r m c. I = [r, mod m, c]"
apply (simp add: i_set_i_set_ind_eq)
apply (induct I rule: i_set_ind.induct)
apply (simp add: iT_infinite)
apply (rule_tac x=0 in exI, rule_tac x="Suc 0" in exI, rule_tac x=n in exI)
 apply (simp add: iMODb_mod_1 iIN_0_iTILL_conv)
apply (rule_tac x=n in exI, rule_tac x="Suc 0" in exI, rule_tac x=d in exI)
 apply (simp add: iMODb_mod_1)
apply (case_tac "m = 0")
 apply (rule_tac x=r in exI, rule_tac x="Suc 0" in exI, rule_tac x=0 in exI)
 apply (simp add: iMOD_0 iIN_0 iMODb_0)
apply (simp add: iT_infinite)
apply blast
done

lemma i_set_as_iMOD_iMODb: "
  I \<in> i_set \<Longrightarrow> (\<exists>r m. I = [r, mod m]) \<or> (\<exists>r m c. I = [r, mod m, c])"
by (blast intro: i_set_finite_as_iMODb i_set_infinite_as_iMOD)


subsubsection \<open>Interval sets are closed under cutting\<close>

lemma i_set_cut_le_ge_closed_disj: "
  \<lbrakk> I \<in> i_set; t \<in> I; cut_op = (\<down>\<le>) \<or> cut_op = (\<down>\<ge>) \<rbrakk> \<Longrightarrow> 
  cut_op I t \<in> i_set"
apply (simp add: i_set_i_set_ind_eq)
apply (induct rule: i_set_ind.induct)
apply safe
apply (simp_all add: iT_cut_le1 iT_cut_ge1 i_set_ind.intros iMODb_iff)
done

corollary 
  i_set_cut_le_closed: "\<lbrakk> I \<in> i_set; t \<in> I \<rbrakk> \<Longrightarrow> I \<down>\<le> t \<in> i_set" and
  i_set_cut_ge_closed: "\<lbrakk> I \<in> i_set; t \<in> I \<rbrakk> \<Longrightarrow> I \<down>\<ge> t \<in> i_set"
by (simp_all add: i_set_cut_le_ge_closed_disj)

lemmas i_set_cut_le_ge_closed = i_set_cut_le_closed i_set_cut_ge_closed

lemma i_set0_cut_closed_disj: "
  \<lbrakk> I \<in> i_set0;
    cut_op = (\<down>\<le>) \<or> cut_op = (\<down>\<ge>) \<or>
    cut_op = (\<down><) \<or> cut_op = (\<down>>) \<rbrakk> \<Longrightarrow> 
  cut_op I t \<in> i_set0"
apply (simp add: i_set0_i_set0_ind_eq)
apply (induct rule: i_set0_ind.induct)
 apply (rule ssubst[OF set_restriction_empty, where P="\<lambda>x. x \<in> i_set0_ind"])
  apply (rule i_cut_set_restriction_disj[of cut_op], blast)
  apply blast
 apply blast
apply (induct_tac I rule: i_set_ind.induct)
apply safe
apply (simp_all add: iT_cut_le iT_cut_ge iT_cut_less iT_cut_greater i_set0_ind_intros2)
done

corollary 
  i_set0_cut_le_closed: "I \<in> i_set0 \<Longrightarrow> I \<down>\<le> t \<in> i_set0" and
  i_set0_cut_less_closed: "I \<in> i_set0 \<Longrightarrow> I \<down>< t \<in> i_set0" and
  i_set0_cut_ge_closed: "I \<in> i_set0 \<Longrightarrow> I \<down>\<ge> t \<in> i_set0" and
  i_set0_cut_greater_closed: "I \<in> i_set0 \<Longrightarrow> I \<down>> t \<in> i_set0"
by (simp_all add: i_set0_cut_closed_disj)

lemmas i_set0_cut_closed =
  i_set0_cut_le_closed 
  i_set0_cut_less_closed
  i_set0_cut_ge_closed
  i_set0_cut_greater_closed


subsubsection \<open>Interval sets are closed under addition and multiplication\<close>

lemma i_set_Plus_closed: "I \<in> i_set \<Longrightarrow> I \<oplus> k \<in> i_set"
apply (simp add: i_set_i_set_ind_eq)
apply (induct rule: i_set_ind.induct)
apply (simp_all add: iT_add i_set_ind.intros)
done

lemma i_set_Mult_closed: "I \<in> i_set \<Longrightarrow> I \<otimes> k \<in> i_set"
apply (case_tac "k = 0")
 apply (simp add: i_set_imp_not_empty iT_Mult_0_if i_set_intros)
apply (simp add: i_set_i_set_ind_eq)
apply (induct rule: i_set_ind.induct)
apply (simp_all add: iT_mult i_set_ind.intros)
done


lemma i_set0_Plus_closed: "I \<in> i_set0 \<Longrightarrow> I \<oplus> k \<in> i_set0"
apply (simp add: i_set0_i_set0_ind_eq)
apply (induct I rule: i_set0_ind.induct)
 apply (simp add: iT_Plus_empty i_set0_ind_empty)
apply (rule subsetD[OF i_set_ind_subset_i_set0_ind])
apply (simp add: i_set_i_set_ind_eq[symmetric] i_set_Plus_closed)
done

lemma i_set0_Mult_closed: "I \<in> i_set0 \<Longrightarrow> I \<otimes> k \<in> i_set0"
apply (simp add: i_set0_i_set0_ind_eq)
apply (induct I rule: i_set0_ind.induct)
 apply (simp add: iT_Mult_empty i_set0_ind_empty)
apply (rule subsetD[OF i_set_ind_subset_i_set0_ind])
apply (simp add: i_set_i_set_ind_eq[symmetric] i_set_Mult_closed)
done


subsubsection \<open>Interval sets are closed with certain conditions under subtraction\<close>

lemma i_set_Plus_neg_closed: "
  \<lbrakk> I \<in> i_set; \<exists>x\<in>I. k \<le> x \<rbrakk> \<Longrightarrow> I \<oplus>- k \<in> i_set"
apply (simp add: i_set_i_set_ind_eq)
apply (induct rule: i_set_ind.induct)
apply (fastforce simp: iT_iff iT_add_neg)+
done

lemma i_set_Minus_closed: "
  \<lbrakk> I \<in> i_set; iMin I \<le> k \<rbrakk> \<Longrightarrow> k \<ominus> I \<in> i_set"
apply (simp add: i_set_i_set_ind_eq)
apply (induct rule: i_set_ind.induct)
apply (fastforce simp: iT_Min iT_sub)+
done


lemma i_set0_Plus_neg_closed: "I \<in> i_set0 \<Longrightarrow> I \<oplus>- k \<in> i_set0"
apply (simp add: i_set0_i_set0_ind_eq)
apply (induct rule: i_set0_ind.induct)
 apply (fastforce simp: iT_Plus_neg_empty)
apply (induct_tac I rule: i_set_ind.induct)
apply (fastforce simp: iT_add_neg)+
done

lemma i_set0_Minus_closed: "I \<in> i_set0 \<Longrightarrow> k \<ominus> I \<in> i_set0"
apply (simp add: i_set0_i_set0_ind_eq)
apply (induct rule: i_set0_ind.induct)
 apply (simp add: iT_Minus_empty i_set0_ind_empty)
apply (induct_tac I rule: i_set_ind.induct)
apply (fastforce simp: iT_sub)+
done

lemmas i_set_IntOp_closed =
  i_set_Plus_closed
  i_set_Mult_closed
  i_set_Plus_neg_closed
  i_set_Minus_closed
lemmas i_set0_IntOp_closed =
  i_set0_Plus_closed
  i_set0_Mult_closed
  i_set0_Plus_neg_closed
  i_set0_Minus_closed


subsubsection \<open>Interval sets are not closed under division\<close>

lemma iMOD_div_mod_gr0_not_in_i_set: "
  \<lbrakk> 0 < k; k < m; 0 < m mod k \<rbrakk> \<Longrightarrow> [r, mod m] \<oslash> k \<notin> i_set"
apply (rule ccontr, simp)
apply (drule i_set_infinite_as_iMOD)
 apply (simp add: iT_Div_finite_iff iMOD_infinite)
apply (elim exE, rename_tac r' m')
apply (frule iMOD_div_mod_gr0_not_ex[of k m r], assumption+)
apply fastforce
done

lemma iMODb_div_mod_gr0_not_in_i_set: "
  \<lbrakk> 0 < k; k < m; 0 < m mod k; k \<le> c \<rbrakk> \<Longrightarrow> [r, mod m, c] \<oslash> k \<notin> i_set"
apply (rule ccontr, simp)
apply (drule i_set_finite_as_iMODb)
 apply (simp add: iT_Div_finite_iff iMODb_finite)
apply (elim exE, rename_tac r' m' c')
apply (frule iMODb_div_mod_gr0_not_ex[of k m c r], assumption+)
apply fastforce
done

lemma "[0, mod 3] \<oslash> 2 \<notin> i_set"
by (rule iMOD_div_mod_gr0_not_in_i_set, simp+)

lemma i_set_Div_not_closed: "Suc 0 < k \<Longrightarrow> \<exists>I\<in>i_set. I \<oslash> k \<notin> i_set"
apply (rule_tac x="[0, mod (Suc k)]" in bexI)
apply (rule iMOD_div_mod_gr0_not_in_i_set)
apply (simp_all add: mod_Suc i_set_MOD)
done
lemma i_set0_Div_not_closed: "Suc 0 < k \<Longrightarrow> \<exists>I\<in>i_set0. I \<oslash> k \<notin> i_set0"
apply (frule i_set_Div_not_closed, erule bexE)
apply (rule_tac x=I in bexI)
 apply (simp add: i_set0_def iT_Div_not_empty i_set_imp_not_empty)
apply (rule subsetD[OF i_set_subset_i_set0], assumption)
done


subsubsection \<open>Sets of intervals closed under division\<close>

inductive_set NatMultiples :: "nat set \<Rightarrow> nat set"
  for F :: "nat set"
where 
  NatMultiples_Factor: "k \<in> F \<Longrightarrow> k \<in> NatMultiples F"
| NatMultiples_Product: "\<lbrakk> k \<in> F; m \<in> NatMultiples F \<rbrakk> \<Longrightarrow> k * m \<in> NatMultiples F"

lemma NatMultiples_ex_divisor: "m \<in> NatMultiples F \<Longrightarrow> \<exists>k\<in>F. m mod k = 0"
apply (induct m rule: NatMultiples.induct)
apply (rule_tac x=k in bexI, simp+)+
done

lemma NatMultiples_product_factor: "\<lbrakk> a \<in> F; b \<in> F \<rbrakk> \<Longrightarrow> a * b \<in> NatMultiples F"
by (drule NatMultiples_Factor[of b], rule NatMultiples_Product)

lemma NatMultiples_product_factor_multiple: "
  \<lbrakk> a \<in> F; b \<in> NatMultiples F \<rbrakk> \<Longrightarrow> a * b \<in> NatMultiples F"
by (rule NatMultiples_Product)

lemma NatMultiples_product_multiple_factor: "
  \<lbrakk> a \<in> NatMultiples F; b \<in> F \<rbrakk> \<Longrightarrow> a * b \<in> NatMultiples F"
by (simp add: mult.commute[of a] NatMultiples_Product)

lemma NatMultiples_product_multiple: "
  \<lbrakk> a \<in> NatMultiples F; b \<in> NatMultiples F \<rbrakk> \<Longrightarrow> a * b \<in> NatMultiples F"
apply (induct a rule: NatMultiples.induct)
 apply (simp add: NatMultiples_Product)
apply (simp add: mult.assoc[of _ _ b] NatMultiples_Product)
done


text \<open>Subset of @{term i_set} containing only continuous intervals, i. e., without @{term iMOD} and @{term iMODb}.\<close>
  
inductive_set i_set_cont :: "(nat set) set"
where
    i_set_cont_FROM[intro]: "[n\<dots>] \<in> i_set_cont"
  | i_set_cont_TILL[intro]: "[\<dots>n] \<in> i_set_cont"
  | i_set_cont_IN[intro]:   "[n\<dots>,d] \<in> i_set_cont"

definition i_set0_cont :: "(nat set) set"
  where "i_set0_cont \<equiv> insert {} i_set_cont"

lemma i_set_cont_subset_i_set: "i_set_cont \<subseteq> i_set"
apply (unfold subset_eq, rule ballI, rename_tac x)
apply (rule_tac a=x in i_set_cont.cases)
apply blast+
done

lemma i_set0_cont_subset_i_set0: "i_set0_cont \<subseteq> i_set0"
apply (unfold i_set0_cont_def i_set0_def)
apply (rule insert_mono)
apply (rule i_set_cont_subset_i_set)
done

text \<open>Minimal definition of @{term i_set_cont}\<close>
  
inductive_set i_set_cont_min :: "(nat set) set"
where
  i_set_cont_FROM[intro]: "[n\<dots>] \<in> i_set_cont_min"
| i_set_cont_IN[intro]:   "[n\<dots>,d] \<in> i_set_cont_min"

definition i_set0_cont_min :: "(nat set) set"
  where "i_set0_cont_min \<equiv> insert {} i_set_cont_min"

lemma i_set_cont_min_eq: "i_set_cont = i_set_cont_min"
apply (rule set_eqI, rule iffI)
 apply (rename_tac x, rule_tac a=x in i_set_cont.cases)
 apply (fastforce simp: iIN_0_iTILL_conv[symmetric])+
apply (rename_tac x, rule_tac a=x in i_set_cont_min.cases)
apply blast+
done


text \<open>\<open>inext\<close> and \<open>iprev\<close> with continuous intervals\<close>

lemma i_set_cont_inext: "
  \<lbrakk> I \<in> i_set_cont; n \<in> I; finite I \<Longrightarrow> n < Max I \<rbrakk> \<Longrightarrow> inext n I = Suc n"
apply (simp add: i_set_cont_min_eq)
apply (rule i_set_cont_min.cases, assumption)
apply (simp_all add: iT_finite iT_Max iT_inext_if iT_iff)
done

lemma i_set_cont_iprev: "
  \<lbrakk> I \<in> i_set_cont; n \<in> I; iMin I < n \<rbrakk> \<Longrightarrow> iprev n I = n - Suc 0"
apply (simp add: i_set_cont_min_eq)
apply (rule i_set_cont_min.cases, assumption)
apply (simp_all add: iT_iprev_if iT_Min iT_iff)
done

lemma i_set_cont_inext__less: "
  \<lbrakk> I \<in> i_set_cont; n \<in> I; n < n0; n0 \<in> I \<rbrakk> \<Longrightarrow> inext n I = Suc n"
apply (case_tac "finite I")
 apply (rule i_set_cont_inext, assumption+)
 apply (rule order_less_le_trans[OF _ Max_ge], assumption+)
apply (rule i_set_cont.cases, assumption)
apply (simp_all add: iT_finite iT_inext)
done

lemma i_set_cont_iprev__greater: "
  \<lbrakk> I \<in> i_set_cont; n \<in> I; n0 < n; n0 \<in> I \<rbrakk> \<Longrightarrow> iprev n I = n - Suc 0"
apply (rule i_set_cont_iprev, assumption+)
apply (rule order_le_less_trans[OF iMin_le, of n0], assumption+)
done


text \<open>Sets of modulo intervals\<close>

inductive_set i_set_mult :: "nat \<Rightarrow> (nat set) set"
  for k :: nat
where
  i_set_mult_FROM[intro!]: "[n\<dots>] \<in> i_set_mult k"
| i_set_mult_TILL[intro!]: "[\<dots>n] \<in> i_set_mult k"
| i_set_mult_IN[intro!]:   "[n\<dots>,d] \<in> i_set_mult k"
| i_set_mult_MOD[intro!]:  "[r, mod m * k] \<in> i_set_mult k"
| i_set_mult_MODb[intro!]: "[r, mod m * k, c] \<in> i_set_mult k"

definition i_set0_mult :: "nat \<Rightarrow> (nat set) set"
  where "i_set0_mult k \<equiv> insert {} (i_set_mult k)"

lemma
  i_set0_mult_empty[intro!]: "{} \<in> i_set0_mult k" and
  i_set0_mult_FROM[intro!] : "[n\<dots>] \<in> i_set0_mult k" and
  i_set0_mult_TILL[intro!] : "[\<dots>n] \<in> i_set0_mult k" and
  i_set0_mult_IN[intro!]   : "[n\<dots>,d] \<in> i_set0_mult k" and
  i_set0_mult_MOD[intro!]  : "[r, mod m * k] \<in> i_set0_mult k" and
  i_set0_mult_MODb[intro!] : "[r, mod m * k, c] \<in> i_set0_mult k"
by (simp_all add: i_set0_mult_def i_set_mult.intros)

lemmas i_set0_mult_intros =
  i_set0_mult_empty
  i_set0_mult_FROM
  i_set0_mult_TILL
  i_set0_mult_IN
  i_set0_mult_MOD
  i_set0_mult_MODb

lemma i_set_mult_subset_i_set0_mult: "i_set_mult k \<subseteq> i_set0_mult k"
by (unfold i_set0_mult_def, rule subset_insertI)

lemma i_set_mult_subset_i_set: "i_set_mult k \<subseteq> i_set"
apply (clarsimp simp: subset_iff)
apply (rule_tac a=t in i_set_mult.cases[of _ k])
apply (simp_all add: i_set_intros)
done

lemma i_set0_mult_subset_i_set0: "i_set0_mult k \<subseteq> i_set0"
apply (simp add: i_set0_mult_def i_set0_empty)
apply (rule order_trans[OF _ i_set_subset_i_set0, OF i_set_mult_subset_i_set])
done

lemma i_set_mult_0_eq_i_set_cont: "i_set_mult 0 = i_set_cont"
apply (rule set_eqI, rule iffI)
 apply (rename_tac x, rule_tac a=x in i_set_mult.cases[of _ 0])
 apply (simp_all add: i_set_cont.intros iMOD_0 iMODb_mod_0)
apply (rename_tac x, rule_tac a=x in i_set_cont.cases)
apply (simp_all add: i_set_mult.intros)
done

lemma i_set0_mult_0_eq_i_set0_cont: "i_set0_mult 0 = i_set0_cont"
by (simp add: i_set0_mult_def i_set0_cont_def i_set_mult_0_eq_i_set_cont)

lemma i_set_mult_1_eq_i_set: "i_set_mult (Suc 0) = i_set"
apply (rule set_eqI, rule iffI)
 apply (rename_tac x, induct_tac x rule: i_set_mult.induct[of _ 1])
 apply (simp_all add: i_set_intros)
apply (simp add: i_set_i_set_ind_eq)
apply (rename_tac x, induct_tac x rule: i_set_ind.induct)
apply (simp_all add: i_set_mult.intros)
apply (rule_tac t=m and s="m * Suc 0" in subst, simp, rule i_set_mult.intros)+
done

lemma i_set0_mult_1_eq_i_set0: "i_set0_mult (Suc 0) = i_set0"
by (simp add: i_set0_mult_def i_set0_def i_set_mult_1_eq_i_set)

lemma i_set_mult_imp_not_empty: "I \<in> i_set_mult k \<Longrightarrow> I \<noteq> {}"
by (induct I rule: i_set_mult.induct, simp_all add: iT_not_empty)

lemma iMOD_in_i_set_mult_imp_divisor_mod_0: "
  \<lbrakk> m \<noteq> Suc 0; [r, mod m] \<in> i_set_mult k \<rbrakk> \<Longrightarrow> m mod k = 0"
apply (case_tac "m = 0", simp)
apply (rule i_set_mult.cases[of "[r, mod m]" k], assumption)
apply (blast dest: iFROM_iMOD_neq)
apply (blast dest: iTILL_iMOD_neq)
apply (blast dest: iIN_iMOD_neq)
apply (simp add: iMOD_eq_conv)
apply (blast dest: iMOD_iMODb_neq)
done

lemma 
  divisor_mod_0_imp_iMOD_in_i_set_mult: "m mod k = 0 \<Longrightarrow> [r, mod m] \<in> i_set_mult k" and
  divisor_mod_0_imp_iMODb_in_i_set_mult: "m mod k = 0 \<Longrightarrow> [r, mod m, c] \<in> i_set_mult k"
  by (auto simp add: ac_simps)

lemma iMOD_in_i_set_mult__divisor_mod_0_conv: "
  m \<noteq> Suc 0 \<Longrightarrow> ([r, mod m] \<in> i_set_mult k) = (m mod k = 0)"
apply (rule iffI)
 apply (simp add: iMOD_in_i_set_mult_imp_divisor_mod_0)
apply (simp add: divisor_mod_0_imp_iMOD_in_i_set_mult)
done

lemma i_set_mult_neq1_subset_i_set: "k \<noteq> Suc 0 \<Longrightarrow> i_set_mult k \<subset> i_set"
apply (rule psubsetI, rule i_set_mult_subset_i_set)
apply (simp add: set_eq_iff)
apply (drule neq_iff[THEN iffD1], erule disjE)
 apply (simp add: i_set_mult_0_eq_i_set_cont)
 apply (thin_tac "k = 0")
 apply (rule_tac x="[0, mod 2]" in exI)
 apply (rule ccontr)
 apply (simp add: i_set_intros)
 apply (drule i_set_cont.cases[where P=False])
  apply (drule sym, simp add: iT_neq)+
 apply simp
apply (rule_tac x="[0, mod Suc k]" in exI)
apply (rule ccontr)
apply (simp add: i_set_intros)
apply (insert iMOD_in_i_set_mult_imp_divisor_mod_0[of "Suc k" 0 k])
apply (simp add: mod_Suc)
done

lemma mod_0_imp_i_set_mult_subset: "
  a mod b = 0 \<Longrightarrow> i_set_mult a \<subseteq> i_set_mult b"
  apply (auto simp add: ac_simps elim!: dvdE)
apply (rule_tac a=x and k="k * b" in i_set_mult.cases)
apply (simp_all add: i_set_mult.intros mult.assoc[symmetric])
done

lemma i_set_mult_subset_imp_mod_0: "
  \<lbrakk> a \<noteq> Suc 0; (i_set_mult a \<subseteq> i_set_mult b) \<rbrakk> \<Longrightarrow> a mod b = 0"
apply (simp add: subset_iff)
apply (erule_tac x="[0, mod a]" in allE)
apply (simp add: divisor_mod_0_imp_iMOD_in_i_set_mult)
apply (simp add: iMOD_in_i_set_mult_imp_divisor_mod_0[of _ 0 b])
done

lemma i_set_mult_subset_conv: "
  a \<noteq> Suc 0 \<Longrightarrow> (i_set_mult a \<subseteq> i_set_mult b) = (a mod b = 0)"
apply (rule iffI)
 apply (simp add: i_set_mult_subset_imp_mod_0)
apply (simp add: mod_0_imp_i_set_mult_subset)
done


lemma i_set_mult_mod_0_div: "
  \<lbrakk> I \<in> i_set_mult k; k mod d = 0 \<rbrakk> \<Longrightarrow> I \<oslash> d \<in> i_set_mult (k div d)"
apply (case_tac "d = 0")
 apply (simp add: iT_Div_0[OF i_set_mult_imp_not_empty] i_set_mult.intros)
apply (induct I rule: i_set_mult.induct)
apply (simp_all add: iT_div i_set_mult.intros)
apply (simp_all add: iMOD_div iMODb_div mod_0_imp_mod_mult_left_0 mod_0_imp_div_mult_left_eq i_set_mult.intros)
done

text \<open>Intervals from @{term "i_set_mult k"} remain in @{term i_set} after division by @{term d} a divisor of @{term k}.\<close>
corollary i_set_mult_mod_0_div_i_set: "
  \<lbrakk> I \<in> i_set_mult k; k mod d = 0 \<rbrakk> \<Longrightarrow> I \<oslash> d \<in> i_set"
by (rule subsetD[OF i_set_mult_subset_i_set[of "k div d"]], rule i_set_mult_mod_0_div)
corollary i_set_mult_div_self_i_set: "
  I \<in> i_set_mult k \<Longrightarrow> I \<oslash> k \<in> i_set"
by (simp add: i_set_mult_mod_0_div_i_set)


lemma i_set_mod_0_mult_in_i_set_mult: "
  \<lbrakk> I \<in> i_set; m mod k = 0 \<rbrakk> \<Longrightarrow> I \<otimes> m \<in> i_set_mult k"
apply (case_tac "m = 0")
 apply (simp add: iT_Mult_0 i_set_imp_not_empty i_set_mult.intros)
apply (clarsimp simp: mult.commute[of k] elim!: dvdE)
apply (simp add: i_set_i_set_ind_eq)
apply (rule_tac a=I in i_set_ind.cases)
apply (simp_all add: iT_mult mult.assoc[symmetric] i_set_mult.intros)
done

lemma i_set_self_mult_in_i_set_mult: "
  I \<in> i_set \<Longrightarrow> I \<otimes> k \<in> i_set_mult k"
by (rule i_set_mod_0_mult_in_i_set_mult[OF _ mod_self])

lemma i_set_mult_mod_gr0_div_not_in_i_set:"
  \<lbrakk> 0 < k; 0 < d; 0 < k mod d \<rbrakk> \<Longrightarrow> \<exists>I\<in>i_set_mult k. I \<oslash> d \<notin> i_set"
apply (case_tac "d = Suc 0", simp)
apply (frule iMOD_div_mod_gr0_not_ex[of d "Suc d * k" 0])
  apply (rule Suc_le_lessD, rule gr0_imp_self_le_mult1, assumption)
 apply simp
apply (rule_tac x="[0, mod Suc d * k]" in bexI)
 apply (rule ccontr, simp)
 apply (frule i_set_infinite_as_iMOD)
  apply (simp add: iT_Div_finite_iff iMOD_infinite)
 apply fastforce
apply (simp add: i_set_mult.intros del: mult_Suc)
done

lemma i_set0_mult_mod_0_div: "
  \<lbrakk> I \<in> i_set0_mult k; k mod d = 0 \<rbrakk> \<Longrightarrow> I \<oslash> d \<in> i_set0_mult (k div d)"
apply (simp add: i_set0_mult_def)
apply (elim disjE)
 apply (simp add: iT_Div_empty)
apply (simp add: i_set_mult_mod_0_div)
done

corollary i_set0_mult_mod_0_div_i_set0: "
  \<lbrakk> I \<in> i_set0_mult k; k mod d = 0 \<rbrakk> \<Longrightarrow> I \<oslash> d \<in> i_set0"
by (rule subsetD[OF i_set0_mult_subset_i_set0[of "k div d"]], rule i_set0_mult_mod_0_div)

corollary i_set0_mult_div_self_i_set0: "
  I \<in> i_set0_mult k \<Longrightarrow> I \<oslash> k \<in> i_set0"
by (simp add: i_set0_mult_mod_0_div_i_set0)

lemma i_set0_mod_0_mult_in_i_set0_mult: "
  \<lbrakk> I \<in> i_set0; m mod k = 0 \<rbrakk> \<Longrightarrow> I \<otimes> m \<in> i_set0_mult k"
apply (simp add: i_set0_def)
apply (erule disjE)
 apply (simp add: iT_Mult_empty i_set0_mult_empty)
apply (rule subsetD[OF i_set_mult_subset_i_set0_mult])
apply (simp add: i_set_mod_0_mult_in_i_set_mult)
done

lemma i_set0_self_mult_in_i_set0_mult: "
  I \<in> i_set0 \<Longrightarrow> I \<otimes> k \<in> i_set0_mult k"
by (simp add: i_set0_mod_0_mult_in_i_set0_mult)

lemma i_set0_mult_mod_gr0_div_not_in_i_set0:"
  \<lbrakk> 0 < k; 0 < d; 0 < k mod d \<rbrakk> \<Longrightarrow> \<exists>I\<in>i_set0_mult k. I \<oslash> d \<notin> i_set0"
apply (frule i_set_mult_mod_gr0_div_not_in_i_set[of k d], assumption+)
apply (erule bexE, rename_tac I, rule_tac x=I in bexI)
 apply (simp add: i_set0_def iT_Div_not_empty i_set_mult_imp_not_empty)
apply (simp add: subsetD[OF i_set_mult_subset_i_set0_mult])
done

end
