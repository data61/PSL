(*  Title:      IL_Interval.thy
    Date:       Oct 2006
    Author:     David Trachtenherz
*)

section \<open>Intervals and operations for temporal logic declarations\<close>

theory IL_Interval
imports 
  "List-Infinite.InfiniteSet2"
  "List-Infinite.SetIntervalStep"
begin

subsection \<open>Time intervals -- definitions and basic lemmata\<close>

subsubsection \<open>Definitions\<close>

type_synonym Time = nat

(* Time interval *)
type_synonym iT = "Time set"

text \<open>Infinite interval starting at some natural @{term "n"}.\<close>
definition 
  iFROM :: "Time \<Rightarrow> iT" ("[_\<dots>]") (* [n, \<infinity>) *) 
where
  "[n\<dots>] \<equiv> {n..}"

text \<open>Finite interval starting at @{term "0"} and ending at some natural @{term "n"}.\<close>
definition
  iTILL :: "Time \<Rightarrow> iT" ("[\<dots>_]") (* [0, n] *) (* Equivalent to [0\<dots>,n] *)
where
  "[\<dots>n] \<equiv> {..n}"

text \<open>
  Finite bounded interval containing the naturals between 
  @{term "n"} and @{term "n + d"}.
  @{term "d"} denotes the difference between left and right interval bound.
  The number of elements is @{term "d + 1"} so that an empty interval cannot be defined.\<close>
definition
  iIN   :: "Time \<Rightarrow> nat \<Rightarrow> iT" ( "[_\<dots>,_]") (* [n, n+d] *)
where
  "[n\<dots>,d] \<equiv> {n..n+d}"



text \<open>
  Infinite modulo interval containing all naturals
  having the same division remainder modulo @{term "m"}
  as @{term "r"}, and beginning at @{term "n"}.\<close>
definition
  iMOD  :: "Time \<Rightarrow> nat \<Rightarrow> iT" ( "[ _, mod _ ]" ) 
where
  "[r, mod m] \<equiv> { x. x mod m = r mod m \<and> r \<le> x}" 


text \<open>
  Finite bounded modulo interval containing all naturals
  having the same division remainder modulo @{term "m"}
  as @{term "r"}, beginning at @{term "n"},
  and ending after @{term "c"} cycles at @{term "r + m * c"}.
  The number of elements is @{term "c + 1"} so that an empty interval cannot be defined.\<close>
definition
  iMODb :: "Time \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> iT" ( "[ _, mod _, _ ]" ) 
where
  "[r, mod m, c] \<equiv> { x. x mod m = r mod m \<and> r \<le> x \<and> x \<le> r + m * c}"

subsubsection \<open>Membership in an interval\<close>

lemmas iT_defs = iFROM_def iTILL_def iIN_def iMOD_def iMODb_def

lemma iFROM_iff: "x \<in> [n\<dots>] = (n \<le> x)"
by (simp add: iFROM_def)
lemma iTILL_iff: "x \<in> [\<dots>n] = (x \<le> n)"
by (simp add: iTILL_def)
lemma iIN_iff:"x \<in> [n\<dots>,d] = (n \<le> x \<and> x \<le> n + d)"
by (simp add: iIN_def)
lemma iMOD_iff: "x \<in> [r, mod m] = (x mod m = r mod m \<and> r \<le> x)"
by (simp add: iMOD_def)
lemma iMODb_iff: "x \<in> [r, mod m, c] = 
  (x mod m = r mod m \<and> r \<le> x \<and> x \<le> r + m * c)"
by (simp add: iMODb_def)

lemma iFROM_D: "x \<in> [n\<dots>] \<Longrightarrow> (n \<le> x)"
by (rule iFROM_iff[THEN iffD1])
lemma iTILL_D: "x \<in> [\<dots>n] \<Longrightarrow> (x \<le> n)"
by (rule iTILL_iff[THEN iffD1])
corollary iIN_geD: "x \<in> [n\<dots>,d] \<Longrightarrow> n \<le> x"
by (simp add: iIN_iff)
corollary iIN_leD: "x \<in> [n\<dots>,d] \<Longrightarrow> x \<le> n + d"
by (simp add: iIN_iff)
corollary iMOD_modD: "x \<in> [r, mod m] \<Longrightarrow> x mod m = r mod m"
by (simp add: iMOD_iff)
corollary iMOD_geD: "x \<in> [r, mod m] \<Longrightarrow> r \<le> x"
by (simp add: iMOD_iff)
corollary iMODb_modD: "x \<in> [r, mod m, c] \<Longrightarrow> x mod m = r mod m"
by (simp add: iMODb_iff)
corollary iMODb_geD: "x \<in> [r, mod m, c] \<Longrightarrow> r \<le> x"
by (simp add: iMODb_iff)
corollary iMODb_leD: "x \<in> [r, mod m, c] \<Longrightarrow> x \<le> r + m * c"
by (simp add: iMODb_iff)

lemmas iT_iff = iFROM_iff iTILL_iff iIN_iff iMOD_iff iMODb_iff

lemmas iT_drule =
  iFROM_D
  iTILL_D
  iIN_geD iIN_leD
  iMOD_modD iMOD_geD
  iMODb_modD iMODb_geD iMODb_leD

lemma 
  iFROM_I [intro]: "n \<le> x \<Longrightarrow> x \<in> [n\<dots>]" and
  iTILL_I [intro]: "x \<le> n \<Longrightarrow> x \<in> [\<dots>n]" and
  iIN_I [intro]:   "n \<le> x \<Longrightarrow> x \<le> n + d \<Longrightarrow> x \<in> [n\<dots>,d]" and
  iMOD_I [intro]:  "x mod m = r mod m \<Longrightarrow> r \<le> x \<Longrightarrow> x \<in> [r, mod m]" and
  iMODb_I [intro]: "x mod m = r mod m \<Longrightarrow> r \<le> x \<Longrightarrow> x \<le> r + m * c \<Longrightarrow> x \<in> [r, mod m, c]"
by (simp add: iT_iff)+

lemma 
  iFROM_E [elim]:  "x \<in> [n\<dots>] \<Longrightarrow> (n \<le> x \<Longrightarrow> P) \<Longrightarrow> P" and 
  iTILL_E [elim]:  "x \<in> [\<dots>n] \<Longrightarrow> (x \<le> n \<Longrightarrow> P) \<Longrightarrow> P" and 
  iIN_E [elim]:    "x \<in> [n\<dots>,d] \<Longrightarrow> (n \<le> x \<Longrightarrow> x \<le> n + d \<Longrightarrow> P) \<Longrightarrow> P" and 
  iMOD_E [elim]:   "x \<in> [r, mod m] \<Longrightarrow> (x mod m = r mod m \<Longrightarrow> r \<le> x \<Longrightarrow> P) \<Longrightarrow> P" and 
  iMODb_E [elim]:   "x \<in> [r, mod m, c] \<Longrightarrow> (x mod m = r mod m \<Longrightarrow> r \<le> x \<Longrightarrow> x \<le> r + m * c \<Longrightarrow> P) \<Longrightarrow> P"
by (simp add: iT_iff)+

(*
lemma "0 < n \<Longrightarrow> \<exists>x \<in> [n\<dots>,2*n]. x mod 2 = 0"
apply (simp add: iT_defs)
apply (rule_tac x="2*n" in bexI)
apply simp
apply simp
done
lemma "0 < n \<Longrightarrow> \<exists>x \<in> [n\<dots>,2*n]. x mod 2 = 0"
apply (simp add: iT_defs atLeastAtMost_def atLeast_def atMost_def Collect_conj_eq[symmetric])
apply (rule_tac x="2*n" in exI)
apply simp
done
*)



lemma iIN_Suc_insert_conv: "
  insert (Suc (n + d)) [n\<dots>,d] = [n\<dots>,Suc d]"
by (fastforce simp: iIN_iff)

lemma iTILL_Suc_insert_conv: "insert (Suc n) [\<dots>n] = [\<dots>Suc n]"
by (fastforce simp: iIN_Suc_insert_conv[of 0 n])

lemma iMODb_Suc_insert_conv: "
  insert (r + m * Suc c) [r, mod m, c] = [r, mod m, Suc c]"
apply (rule set_eqI)
apply (simp add: iMODb_iff add.commute[of _ r])
apply (simp add: add.commute[of m])
apply (simp add: add.assoc[symmetric])
apply (rule iffI)
 apply fastforce
apply (elim conjE)
apply (drule_tac x=x in order_le_less[THEN iffD1, rule_format])
apply (erule disjE)
 apply (frule less_mod_eq_imp_add_divisor_le[where m=m], simp)
 apply (drule add_le_imp_le_right)
 apply simp
apply simp
done

lemma iFROM_pred_insert_conv: "insert (n - Suc 0) [n\<dots>] = [n - Suc 0\<dots>]"
by (fastforce simp: iFROM_iff)

lemma iIN_pred_insert_conv: "
  0 < n \<Longrightarrow> insert (n - Suc 0) [n\<dots>,d] = [n - Suc 0\<dots>,Suc d]"
by (fastforce simp: iIN_iff)

lemma iMOD_pred_insert_conv: "
  m \<le> r \<Longrightarrow> insert (r - m) [r, mod m] = [r - m, mod m]"
apply (case_tac "m = 0")
 apply (simp add: iMOD_iff insert_absorb)
apply simp
apply (rule set_eqI)
apply (simp add: iMOD_iff mod_diff_self2)
apply (rule iffI)
 apply (erule disjE)
  apply (simp add: mod_diff_self2)
 apply (simp add: le_imp_diff_le)
apply (erule conjE)
apply (drule order_le_less[THEN iffD1, of "r-m"], erule disjE)
 prefer 2
 apply simp
apply (frule order_less_le_trans[of _ m r], assumption)
apply (drule less_mod_eq_imp_add_divisor_le[of "r-m" _ m])
 apply (simp add: mod_diff_self2)
apply simp
done

lemma iMODb_pred_insert_conv: "
  m \<le> r \<Longrightarrow> insert (r - m) [r, mod m, c] = [r - m, mod m, Suc c]"
apply (rule set_eqI)
apply (frule iMOD_pred_insert_conv)
apply (drule_tac f="\<lambda>s. x \<in> s" in arg_cong)
apply (force simp: iMOD_iff iMODb_iff)
done

lemma iFROM_Suc_pred_insert_conv: "insert n [Suc n\<dots>] = [n\<dots>]"
by (insert iFROM_pred_insert_conv[of "Suc n"], simp)
lemma iIN_Suc_pred_insert_conv: "insert n [Suc n\<dots>,d] = [n\<dots>,Suc d]"
by (insert iIN_pred_insert_conv[of "Suc n"], simp)
lemma iMOD_Suc_pred_insert_conv: "insert r [r + m, mod m] = [r, mod m]"
by (insert iMOD_pred_insert_conv[of m "r + m"], simp)
lemma iMODb_Suc_pred_insert_conv: "insert r [r + m, mod m, c] = [r, mod m, Suc c]"
by (insert iMODb_pred_insert_conv[of m "r + m"], simp)

lemmas iT_Suc_insert =
  iIN_Suc_insert_conv
  iTILL_Suc_insert_conv
  iMODb_Suc_insert_conv
lemmas iT_pred_insert =
  iFROM_pred_insert_conv
  iIN_pred_insert_conv
  iMOD_pred_insert_conv
  iMODb_pred_insert_conv
lemmas iT_Suc_pred_insert =
  iFROM_Suc_pred_insert_conv
  iIN_Suc_pred_insert_conv
  iMOD_Suc_pred_insert_conv
  iMODb_Suc_pred_insert_conv

lemma iMOD_mem_diff: "\<lbrakk> a \<in> [r, mod m]; b \<in> [r, mod m] \<rbrakk> \<Longrightarrow> (a - b) mod m = 0"
by (simp add: iMOD_iff mod_eq_imp_diff_mod_0)
lemma iMODb_mem_diff: "\<lbrakk> a \<in> [r, mod m, c]; b \<in> [r, mod m, c] \<rbrakk> \<Longrightarrow> (a - b) mod m = 0"
by (simp add: iMODb_iff mod_eq_imp_diff_mod_0)



subsubsection \<open>Interval conversions\<close>

lemma iIN_0_iTILL_conv:"[0\<dots>,n] = [\<dots>n]"
by (simp add: iTILL_def iIN_def atMost_atLeastAtMost_0_conv)
lemma iIN_iTILL_iTILL_conv: "0 < n \<Longrightarrow> [n\<dots>,d] = [\<dots>n+d] - [\<dots>n - Suc 0]"
by (fastforce simp: iTILL_iff iIN_iff)
lemma iIN_iFROM_iTILL_conv: "[n\<dots>,d] = [n\<dots>] \<inter> [\<dots>n+d]"
by (simp add: iT_defs atLeastAtMost_def)
lemma iMODb_iMOD_iTILL_conv: "[r, mod m, c] = [r, mod m] \<inter> [\<dots>r+m*c]"
by (force simp: iT_defs set_interval_defs)
lemma iMODb_iMOD_iIN_conv: "[r, mod m, c] = [r, mod m] \<inter> [r\<dots>,m*c]"
by (force simp: iT_defs set_interval_defs)

lemma iFROM_iTILL_iIN_conv: "n \<le> n' \<Longrightarrow> [n\<dots>] \<inter> [\<dots>n'] = [n\<dots>,n'-n]"
by (simp add: iT_defs atLeastAtMost_def)
lemma iMOD_iTILL_iMODb_conv: "
  r \<le> n \<Longrightarrow> [r, mod m] \<inter> [\<dots>n] = [r, mod m, (n - r) div m]"
apply (rule set_eqI)
apply (simp add: iT_iff minus_mod_eq_mult_div [symmetric])
apply (rule iffI)
 apply clarify
 apply (frule_tac x=x and y=n and m=m in le_imp_sub_mod_le)
 apply (simp add: mod_diff_right_eq)
apply fastforce
done

lemma iMOD_iIN_iMODb_conv: "
  [r, mod m] \<inter> [r\<dots>,d] = [r, mod m, d div m]"
apply (case_tac "r = 0")
 apply (simp add: iIN_0_iTILL_conv iMOD_iTILL_iMODb_conv)
apply (simp add: iIN_iTILL_iTILL_conv Diff_Int_distrib iMOD_iTILL_iMODb_conv diff_add_inverse)
apply (rule subst[of "{}" _ "\<lambda>t. \<forall>x.(x - t) = x", THEN spec])
 prefer 2
 apply simp
apply (rule sym)
apply (fastforce simp: disjoint_iff_not_equal iMOD_iff iTILL_iff)
done

lemma iFROM_0: "[0\<dots>] = UNIV"
by (simp add: iFROM_def)

lemma iTILL_0: "[\<dots>0] = {0}"
by (simp add: iTILL_def)

lemma iIN_0: "[n\<dots>,0] = {n}"
by (simp add: iIN_def)

lemma iMOD_0: "[r, mod 0] = [r\<dots>,0]"
by (fastforce simp: iIN_0 iMOD_def)

lemma iMODb_mod_0: "[r, mod 0, c] = [r\<dots>,0]"
by (fastforce simp: iMODb_def iIN_0)

lemma iMODb_0: "[r, mod m, 0] = [r\<dots>,0]"
by (fastforce simp: iMODb_def iIN_0 set_eq_iff)

lemmas iT_0 =
  iFROM_0
  iTILL_0
  iIN_0
  iMOD_0
  iMODb_mod_0
  iMODb_0

lemma iMOD_1: "[r, mod Suc 0] = [r\<dots>]"
by (fastforce simp: iFROM_iff)

lemma iMODb_mod_1: "[r, mod Suc 0, c] = [r\<dots>,c]"
by (fastforce simp: iT_iff)


subsubsection \<open>Finiteness and emptiness of intervals\<close>

lemma 
  iFROM_not_empty: "[n\<dots>] \<noteq> {}" and
  iTILL_not_empty: "[\<dots>n] \<noteq> {}" and
  iIN_not_empty: "[n\<dots>,d] \<noteq> {}" and
  iMOD_not_empty: "[r, mod m] \<noteq> {}" and
  iMODb_not_empty: "[r, mod m, c] \<noteq> {}"
by (fastforce simp: iT_iff)+

lemmas iT_not_empty = 
  iFROM_not_empty
  iTILL_not_empty
  iIN_not_empty
  iMOD_not_empty
  iMODb_not_empty

lemma 
  iTILL_finite: "finite [\<dots>n]" and
  iIN_finite: "finite [n\<dots>,d]" and
  iMODb_finite: "finite [r, mod m, c]" and
  iMOD_0_finite: "finite [r, mod 0]"
by (simp add: iT_defs)+

lemma iFROM_infinite: "infinite [n\<dots>]"
by (simp add: iT_defs infinite_atLeast)

lemma iMOD_infinite: "0 < m \<Longrightarrow> infinite [r, mod m]"
apply (rule infinite_nat_iff_asc_chain[THEN iffD2])
 apply (rule iT_not_empty)
apply (rule ballI, rename_tac n)
apply (rule_tac x="n+m" in bexI, simp)
apply (simp add: iMOD_iff)
done

lemmas iT_finite =
  iTILL_finite
  iIN_finite
  iMODb_finite iMOD_0_finite

lemmas iT_infinite =
  iFROM_infinite
  iMOD_infinite


subsubsection \<open>\<open>Min\<close> and \<open>Max\<close> element of an interval\<close>

lemma 
  iTILL_Min: "iMin [\<dots>n] = 0" and
  iFROM_Min: "iMin [n\<dots>] = n" and
  iIN_Min:   "iMin [n\<dots>,d] = n" and
  iMOD_Min:  "iMin [r, mod m] = r" and
  iMODb_Min: "iMin [r, mod m, c] = r"
by (rule iMin_equality, (simp add: iT_iff)+)+

lemmas iT_Min = 
  iIN_Min
  iTILL_Min
  iFROM_Min
  iMOD_Min
  iMODb_Min

lemma 
  iTILL_Max: "Max [\<dots>n] = n" and
  iIN_Max: "Max [n\<dots>,d] = n+d" and
  iMODb_Max: "Max [r, mod m, c] = r + m * c" and
  iMOD_0_Max: "Max [r, mod 0] = r"
by (rule Max_equality, (simp add: iT_iff iT_finite)+)+

lemmas iT_Max =
  iTILL_Max
  iIN_Max
  iMODb_Max
  iMOD_0_Max

lemma
  iTILL_iMax: "iMax [\<dots>n] = enat n" and
  iIN_iMax: "iMax [n\<dots>,d] = enat (n+d)" and
  iMODb_iMax: "iMax [r, mod m, c] = enat (r + m * c)" and
  iMOD_0_iMax: "iMax [r, mod 0] = enat r" and
  iFROM_iMax: "iMax [n\<dots>] = \<infinity>" and
  iMOD_iMax: "0 < m \<Longrightarrow> iMax [r, mod m] = \<infinity>"
by (simp add: iMax_def iT_finite iT_infinite iT_Max)+

lemmas iT_iMax =
  iTILL_iMax
  iIN_iMax
  iMODb_iMax
  iMOD_0_iMax
  iFROM_iMax
  iMOD_iMax


subsection \<open>Adding and subtracting constants to interval elements\<close>

lemma 
  iFROM_plus: "x \<in> [n\<dots>] \<Longrightarrow> x + k \<in> [n\<dots>]" and
  iFROM_Suc: "x \<in> [n\<dots>] \<Longrightarrow> Suc x \<in> [n\<dots>]" and
  iFROM_minus: "\<lbrakk> x \<in> [n\<dots>]; k \<le> x - n \<rbrakk> \<Longrightarrow> x - k \<in> [n\<dots>]" and
  iFROM_pred: "n < x  \<Longrightarrow> x - Suc 0 \<in> [n\<dots>]"
by (simp add: iFROM_iff)+

lemma 
  iTILL_plus: "\<lbrakk> x \<in> [\<dots>n]; k \<le> n - x \<rbrakk> \<Longrightarrow> x + k \<in> [\<dots>n]" and
  iTILL_Suc: "x < n \<Longrightarrow> Suc x \<in> [\<dots>n]" and
  iTILL_minus: "x \<in> [\<dots>n] \<Longrightarrow> x - k \<in> [\<dots>n]" and
  iTILL_pred: "x \<in> [\<dots>n] \<Longrightarrow> x - Suc 0 \<in> [\<dots>n]"
by (simp add: iTILL_iff)+

lemma iIN_plus: "\<lbrakk> x \<in> [n\<dots>,d]; k \<le> n + d - x \<rbrakk> \<Longrightarrow> x + k \<in> [n\<dots>,d]"
by (fastforce simp: iIN_iff)

lemma iIN_Suc: "\<lbrakk> x \<in> [n\<dots>,d]; x < n + d \<rbrakk> \<Longrightarrow> Suc x \<in> [n\<dots>,d]"
by (simp add: iIN_iff)

lemma iIN_minus: "\<lbrakk> x \<in> [n\<dots>,d]; k \<le> x - n \<rbrakk> \<Longrightarrow> x - k \<in> [n\<dots>,d]"
by (fastforce simp: iIN_iff)

lemma iIN_pred: "\<lbrakk> x \<in> [n\<dots>,d]; n < x \<rbrakk> \<Longrightarrow> x - Suc 0 \<in> [n\<dots>,d]"
by (fastforce simp: iIN_iff)

lemma iMOD_plus_divisor_mult: "x \<in> [r, mod m] \<Longrightarrow> x + k * m \<in> [r, mod m]"
by (simp add: iMOD_def)

corollary iMOD_plus_divisor: "x \<in> [r, mod m] \<Longrightarrow> x + m \<in> [r, mod m]"
by (simp add: iMOD_def)

lemma iMOD_minus_divisor_mult: "
  \<lbrakk> x \<in> [r, mod m]; k * m \<le> x - r \<rbrakk> \<Longrightarrow> x - k * m \<in> [r, mod m]"
by (fastforce simp: iMOD_def mod_diff_mult_self1)

corollary iMOD_minus_divisor_mult2: "
  \<lbrakk> x \<in> [r, mod m]; k \<le> (x - r) div m \<rbrakk> \<Longrightarrow> x - k * m \<in> [r, mod m]"
apply (rule iMOD_minus_divisor_mult, assumption)
apply (clarsimp simp: iMOD_iff)
apply (drule mult_le_mono1[of _ _ m])
apply (simp add: mod_0_div_mult_cancel[THEN iffD1, OF mod_eq_imp_diff_mod_0])
done

corollary iMOD_minus_divisor: "
  \<lbrakk> x \<in> [r, mod m]; m + r \<le> x \<rbrakk> \<Longrightarrow> x - m \<in> [r, mod m]"
apply (frule iMOD_geD)
apply (insert iMOD_minus_divisor_mult[of x r m 1])
apply simp
done

lemma iMOD_plus: "
  x \<in> [r, mod m] \<Longrightarrow> (x + k \<in> [r, mod m]) = (k mod m = 0)"
apply safe
 apply (drule iMOD_modD)+
 apply (rule mod_add_eq_imp_mod_0[of x, THEN iffD1])
   apply simp
  apply (erule dvdE)
apply (simp add: mult.commute iMOD_plus_divisor_mult)
done
corollary iMOD_Suc: "
  x \<in> [r, mod m] \<Longrightarrow> (Suc x \<in> [r, mod m]) = (m = Suc 0)"
apply (simp add: iMOD_iff, safe)
apply (simp add: mod_Suc, split if_split_asm)
apply simp+
done

lemma iMOD_minus: "
  \<lbrakk> x \<in> [r, mod m]; k \<le> x - r \<rbrakk> \<Longrightarrow> (x - k \<in> [r, mod m]) = (k mod m = 0)"
apply safe
 apply (clarsimp simp: iMOD_iff)
 apply (rule mod_add_eq_imp_mod_0[of "x - k" k, THEN iffD1])
   apply simp
  apply (erule dvdE)
apply (simp add: mult.commute iMOD_minus_divisor_mult)
done

corollary iMOD_pred: "
  \<lbrakk> x \<in> [r, mod m]; r < x \<rbrakk> \<Longrightarrow> (x - Suc 0 \<in> [r, mod m]) = (m = Suc 0)"
apply safe
 apply (simp add: iMOD_Suc[of "x - Suc 0" r, THEN iffD1])
apply (simp add: iMOD_iff)
done

lemma iMODb_plus_divisor_mult: "
  \<lbrakk> x \<in> [r, mod m, c]; k * m \<le> r + m * c - x \<rbrakk> \<Longrightarrow> x + k * m \<in> [r, mod m, c]"
by (fastforce simp: iMODb_def)

lemma iMODb_plus_divisor_mult2: "
  \<lbrakk> x \<in> [r, mod m, c]; k \<le> c - (x - r) div m \<rbrakk> \<Longrightarrow> 
  x + k * m \<in> [r, mod m, c]"
apply (rule iMODb_plus_divisor_mult, assumption)
apply (clarsimp simp: iMODb_iff)
apply (drule mult_le_mono1[of _ _ m])
apply (simp add: diff_mult_distrib
  mod_0_div_mult_cancel[THEN iffD1, OF mod_eq_imp_diff_mod_0]
  add.commute[of r] mult.commute[of c])
done
lemma iMODb_plus_divisor: "
  \<lbrakk> x \<in> [r, mod m, c]; x < r + m * c \<rbrakk> \<Longrightarrow> x + m \<in> [r, mod m, c]"
by (simp add: iMODb_iff less_mod_eq_imp_add_divisor_le)

lemma iMODb_minus_divisor_mult: "
  \<lbrakk> x \<in> [r, mod m, c]; r + k * m \<le> x \<rbrakk>  \<Longrightarrow> x - k * m \<in> [r, mod m, c]"
by (fastforce simp: iMODb_def mod_diff_mult_self1)

lemma iMODb_plus: "
  \<lbrakk> x \<in> [r, mod m, c]; k \<le> r + m * c - x \<rbrakk> \<Longrightarrow> 
  (x + k \<in> [r, mod m, c]) = (k mod m = 0)"
apply safe
 apply (rule mod_add_eq_imp_mod_0[of x, THEN iffD1])
 apply (simp add: iT_iff)
apply fastforce
done

corollary iMODb_Suc: "
  \<lbrakk> x \<in> [r, mod m, c]; x < r + m * c \<rbrakk> \<Longrightarrow> 
  (Suc x \<in> [r, mod m, c]) = (m = Suc 0)"
apply (rule iffI)
 apply (simp add: iMODb_iMOD_iTILL_conv iMOD_Suc)
apply (simp add: iMODb_iMOD_iTILL_conv iMOD_1 iFROM_Suc iTILL_Suc)
done

lemma iMODb_minus: "
  \<lbrakk> x \<in> [r, mod m, c]; k \<le> x - r \<rbrakk> \<Longrightarrow> 
  (x - k \<in> [r, mod m, c]) = (k mod m = 0)"
apply (rule iffI)
 apply (simp add: iMODb_iMOD_iTILL_conv iMOD_minus)
apply (simp add: iMODb_iMOD_iTILL_conv iMOD_minus iTILL_minus)
done

corollary iMODb_pred: "
  \<lbrakk> x \<in> [r, mod m, c]; r < x \<rbrakk> \<Longrightarrow> 
  (x - Suc 0 \<in> [r, mod m, c]) = (m = Suc 0)"
apply (rule iffI)
 apply (subgoal_tac "x \<in> [r, mod m] \<and> x - Suc 0 \<in> [r, mod m]")
  prefer 2
  apply (simp add: iT_iff)
 apply (clarsimp simp: iMOD_pred)
apply (fastforce simp add: iMODb_iff)
done

lemmas iFROM_plus_minus =
  iFROM_plus
  iFROM_Suc
  iFROM_minus
  iFROM_pred

lemmas iTILL_plus_minus =
  iTILL_plus
  iTILL_Suc
  iTILL_minus
  iTILL_pred

lemmas iIN_plus_minus =
  iIN_plus
  iIN_Suc
  iTILL_minus
  iIN_pred

lemmas iMOD_plus_minus_divisor =
  iMOD_plus_divisor_mult
  iMOD_plus_divisor
  iMOD_minus_divisor_mult
  iMOD_minus_divisor_mult2
  iMOD_minus_divisor

lemmas iMOD_plus_minus =
  iMOD_plus
  iMOD_Suc
  iMOD_minus
  iMOD_pred

lemmas iMODb_plus_minus_divisor =
  iMODb_plus_divisor_mult
  iMODb_plus_divisor_mult2
  iMODb_plus_divisor
  iMODb_minus_divisor_mult

lemmas iMODb_plus_minus =
  iMODb_plus
  iMODb_Suc
  iMODb_minus
  iMODb_pred

lemmas iT_plus_minus =
  iFROM_plus_minus
  iTILL_plus_minus
  iIN_plus_minus
  iMOD_plus_minus_divisor
  iMOD_plus_minus
  iMODb_plus_minus_divisor
  iMODb_plus_minus


(*
lemma "a \<in> [3\<dots>,2] \<Longrightarrow> 3 \<le> a \<and> a \<le> 5"
by (simp add: iT_iff)
lemma "15 \<in> [5, mod 10]"
by (simp add: iT_iff)


lemma "n \<in> [15, mod 10] \<Longrightarrow> n \<in> [5, mod 10]"
by (simp add: iT_iff)

lemma "[15, mod 10] \<subseteq> [5, mod 10]"
by (fastforce simp: iMOD_def)

lemma "n \<le> i \<Longrightarrow> n \<in> [\<dots>i]"
by (simp add: iT_iff)
lemma "\<forall>n \<in> [\<dots>i]. n \<le> i"
by (simp add: iT_iff)

lemma "\<exists>n \<in> [2, mod 10].n \<notin> [12, mod 10]"
apply (simp add: iT_defs)
apply (rule_tac x=2 in exI)
apply simp
done
*)


subsection \<open>Relations between intervals\<close>

subsubsection \<open>Auxiliary lemmata\<close>


lemma Suc_in_imp_not_subset_iMOD: "
  \<lbrakk> n \<in> S; Suc n \<in> S; m \<noteq> Suc 0 \<rbrakk> \<Longrightarrow> \<not> S \<subseteq> [r, mod m]"
by (blast intro: iMOD_Suc[THEN iffD1])

corollary Suc_in_imp_neq_iMOD: "
  \<lbrakk> n \<in> S; Suc n \<in> S; m \<noteq> Suc 0 \<rbrakk> \<Longrightarrow> S \<noteq> [r, mod m]"
by (blast dest: Suc_in_imp_not_subset_iMOD)

lemma Suc_in_imp_not_subset_iMODb: "
  \<lbrakk> n \<in> S; Suc n \<in> S; m \<noteq> Suc 0 \<rbrakk> \<Longrightarrow> \<not> S \<subseteq> [r, mod m, c]"
apply (rule ccontr, simp)
apply (frule subsetD[of _ _ n], assumption)
apply (drule subsetD[of _ _ "Suc n"], assumption)
apply (frule iMODb_Suc[THEN iffD1])
 apply (drule iMODb_leD[of "Suc n"])
 apply simp
apply blast+
done
corollary Suc_in_imp_neq_iMODb: "
  \<lbrakk> n \<in> S; Suc n \<in> S; m \<noteq> Suc 0 \<rbrakk> \<Longrightarrow> S \<noteq> [r, mod m, c]"
by (blast dest: Suc_in_imp_not_subset_iMODb)


subsubsection \<open>Subset relation between intervals\<close>

lemma 
  iIN_iFROM_subset_same: "[n\<dots>,d] \<subseteq> [n\<dots>]" and
  iIN_iTILL_subset_same: "[n\<dots>,d] \<subseteq> [\<dots>n+d]" and
  iMOD_iFROM_subset_same: "[r, mod m] \<subseteq> [r\<dots>]" and
  iMODb_iTILL_subset_same: "[r, mod m, c] \<subseteq> [\<dots>r+m*c]" and
  iMODb_iIN_subset_same: "[r, mod m, c] \<subseteq> [r\<dots>,m*c]" and
  iMODb_iMOD_subset_same: "[r, mod m, c] \<subseteq> [r, mod m]"
by (simp add: subset_iff iT_iff)+

lemmas iT_subset_same = 
  iIN_iFROM_subset_same
  iIN_iTILL_subset_same
  iMOD_iFROM_subset_same
  iMODb_iTILL_subset_same
  iMODb_iIN_subset_same
  iMODb_iTILL_subset_same
  iMODb_iMOD_subset_same

lemma iMODb_imp_iMOD: "x \<in> [r, mod m, c] \<Longrightarrow> x \<in> [r, mod m]"
by (blast intro: iMODb_iMOD_subset_same)

lemma iMOD_imp_iMODb: "
  \<lbrakk> x \<in> [r, mod m]; x \<le> r + m * c \<rbrakk> \<Longrightarrow> x \<in> [r, mod m, c]"
by (simp add: iT_iff)

lemma iMOD_singleton_subset_conv: "([r, mod m] \<subseteq> {a}) = (r = a \<and> m = 0)"
apply (rule iffI)
 apply (simp add: subset_singleton_conv iT_not_empty)
 apply (simp add: set_eq_iff iT_iff)
 apply (frule_tac x=r in spec, drule_tac x="r+m" in spec)
 apply simp
apply (simp add: iMOD_0 iIN_0)
done
lemma iMOD_singleton_eq_conv: "([r, mod m] = {a}) = (r = a \<and> m = 0)"
apply (rule_tac t="[r, mod m] = {a}" and s="[r, mod m] \<subseteq> {a}" in subst)
 apply (simp add: subset_singleton_conv iMOD_not_empty)
apply (simp add: iMOD_singleton_subset_conv)
done

lemma iMODb_singleton_subset_conv: "
  ([r, mod m, c] \<subseteq> {a}) = (r = a \<and> (m = 0 \<or> c = 0))"
apply (rule iffI)
 apply (simp add: subset_singleton_conv iT_not_empty)
 apply (simp add: set_eq_iff iT_iff)
 apply (frule_tac x=r in spec, drule_tac x="r+m" in spec)
 apply clarsimp
apply (fastforce simp: iMODb_0 iMODb_mod_0 iIN_0)
done
lemma iMODb_singleton_eq_conv: "
  ([r, mod m, c] = {a}) = (r = a \<and> (m = 0 \<or> c = 0))"
apply (rule_tac t="[r, mod m, c] = {a}" and s="[r, mod m, c] \<subseteq> {a}" in subst)
 apply (simp add:  subset_singleton_conv iMODb_not_empty)
apply (simp add: iMODb_singleton_subset_conv)
done

lemma iMODb_subset_imp_divisor_mod_0: "
  \<lbrakk> 0 < c'; [r', mod m', c'] \<subseteq> [r, mod m, c] \<rbrakk> \<Longrightarrow> m' mod m = 0"
apply (simp add: subset_iff iMODb_iff)
apply (drule gr0_imp_self_le_mult1[of _ m'])
apply (rule mod_add_eq_imp_mod_0[of r' m' m, THEN iffD1])
apply (frule_tac x=r' in spec, drule_tac x="r'+m'" in spec)
apply simp
done

lemma iMOD_subset_imp_divisor_mod_0: "
  [r', mod m'] \<subseteq> [r, mod m] \<Longrightarrow> m' mod m = 0"
apply (simp add: subset_iff iMOD_iff)
apply (rule mod_add_eq_imp_mod_0[of r' m' m, THEN iffD1])
apply simp
done

lemma iMOD_subset_imp_iMODb_subset: "
  \<lbrakk> [r', mod m'] \<subseteq> [r, mod m]; r' + m' * c' \<le> r + m * c \<rbrakk> \<Longrightarrow> 
  [r', mod m', c'] \<subseteq> [r, mod m, c]"
by (simp add: subset_iff iT_iff)

lemma iMODb_subset_imp_iMOD_subset: "
  \<lbrakk> [r', mod m', c'] \<subseteq> [r, mod m, c]; 0 < c' \<rbrakk> \<Longrightarrow> 
  [r', mod m'] \<subseteq> [r, mod m]"
apply (frule subsetD[of _ _ r'])
 apply (simp add: iMODb_iff)
apply (rule subsetI)
apply (simp add: iMOD_iff iMODb_iff, clarify)
apply (drule mod_eq_mod_0_imp_mod_eq[where m=m and m'=m'])
 apply (simp add: iMODb_subset_imp_divisor_mod_0)
apply simp
done

lemma iMODb_0_iMOD_subset_conv: "
  ([r', mod m', 0] \<subseteq> [r, mod m]) = 
  (r' mod m = r mod m \<and> r \<le> r')"
by (simp add: iMODb_0 iIN_0 singleton_subset_conv iMOD_iff)

lemma iFROM_subset_conv: "([n'\<dots>] \<subseteq> [n\<dots>]) = (n \<le> n')"
by (simp add: iFROM_def)

lemma iFROM_iMOD_subset_conv: "([n'\<dots>] \<subseteq> [r, mod m]) = (r \<le> n' \<and> m = Suc 0)"
apply (rule iffI)
 apply (rule conjI)
  apply (drule iMin_subset[OF iFROM_not_empty])
  apply (simp add: iT_Min)
 apply (rule ccontr)
 apply (cut_tac Suc_in_imp_not_subset_iMOD[of n' "[n'\<dots>]" m r])
 apply (simp add: iT_iff)+
apply (simp add: subset_iff iT_iff)
done

lemma iIN_subset_conv: "([n'\<dots>,d'] \<subseteq> [n\<dots>,d]) = (n \<le> n' \<and> n'+d' \<le> n+d)"
apply (rule iffI)
 apply (frule iMin_subset[OF iIN_not_empty])
 apply (drule Max_subset[OF iIN_not_empty _ iIN_finite])
 apply (simp add: iIN_Min iIN_Max)
apply (simp add: subset_iff iIN_iff)
done

lemma iIN_iFROM_subset_conv: "([n'\<dots>,d'] \<subseteq> [n\<dots>]) = (n \<le> n')"
by (fastforce simp: subset_iff iFROM_iff iIN_iff)

lemma iIN_iTILL_subset_conv: "([n'\<dots>,d'] \<subseteq> [\<dots>n]) = (n' + d' \<le> n)"
by (fastforce simp: subset_iff iT_iff)

lemma iIN_iMOD_subset_conv: "
  0 < d' \<Longrightarrow> ([n'\<dots>,d'] \<subseteq> [r, mod m]) = (r \<le> n' \<and> m = Suc 0)"
apply (rule iffI)
 apply (frule iMin_subset[OF iIN_not_empty])
 apply (simp add: iT_Min)
 apply (subgoal_tac "n' \<in> [n'\<dots>,d']")
  prefer 2
  apply (simp add: iIN_iff)
 apply (rule ccontr)
 apply (frule Suc_in_imp_not_subset_iMOD[where r=r and m=m])
 apply (simp add: iIN_Suc)+
apply (simp add: iMOD_1 iIN_iFROM_subset_conv)
done

lemma iIN_iMODb_subset_conv: "
  0 < d' \<Longrightarrow> 
  ([n'\<dots>,d'] \<subseteq> [r, mod m, c]) = 
  (r \<le> n' \<and> m = Suc 0 \<and> n' + d' \<le> r + m * c)"
apply (rule iffI)
 apply (frule subset_trans[OF _ iMODb_iMOD_subset_same])
 apply (simp add: iIN_iMOD_subset_conv iMODb_mod_1 iIN_subset_conv)
apply (clarsimp simp: iMODb_mod_1 iIN_subset_conv)
done


lemma iTILL_subset_conv: "([\<dots>n'] \<subseteq> [\<dots>n]) = (n' \<le> n)"
by (simp add: iTILL_def)

lemma iTILL_iFROM_subset_conv: "([\<dots>n'] \<subseteq> [n\<dots>]) = (n = 0)"
apply (rule iffI)
 apply (drule subsetD[of _ _ 0])
 apply (simp add: iT_iff)+
apply (simp add: iFROM_0)
done

lemma iTILL_iIN_subset_conv: "([\<dots>n'] \<subseteq> [n\<dots>,d]) = (n = 0 \<and> n' \<le> d)"
apply (rule iffI)
 apply (frule iMin_subset[OF iTILL_not_empty])
 apply (drule Max_subset[OF iTILL_not_empty _ iIN_finite])
 apply (simp add: iT_Min iT_Max)
apply (simp add: iIN_0_iTILL_conv iTILL_subset_conv)
done

lemma iTILL_iMOD_subset_conv: "
  0 < n' \<Longrightarrow> ([\<dots>n'] \<subseteq> [r, mod m]) = (r = 0 \<and> m = Suc 0)"
apply (drule iIN_iMOD_subset_conv[of n' 0 r m])
apply (simp add: iIN_0_iTILL_conv)
done

lemma iTILL_iMODb_subset_conv: "
  0 < n' \<Longrightarrow> ([\<dots>n'] \<subseteq> [r, mod m, c]) = (r = 0 \<and> m = Suc 0 \<and> n' \<le> r + m * c)"
apply (drule iIN_iMODb_subset_conv[of n' 0 r m c])
apply (simp add: iIN_0_iTILL_conv)
done

lemma iMOD_iFROM_subset_conv: "([r', mod m']) \<subseteq> [n\<dots>] = (n \<le> r')"
by (fastforce simp: subset_iff iT_iff)

lemma iMODb_iFROM_subset_conv: "([r', mod m', c'] \<subseteq> [n\<dots>]) = (n \<le> r')"
by (fastforce simp: subset_iff iT_iff)

lemma iMODb_iIN_subset_conv: "
  ([r', mod m', c'] \<subseteq> [n\<dots>,d]) = (n \<le> r' \<and> r' + m' * c' \<le> n + d)"
by (fastforce simp: subset_iff iT_iff)

lemma iMODb_iTILL_subset_conv: "
  ([r', mod m', c'] \<subseteq> [\<dots>n]) = (r' + m' * c' \<le> n)"
by (fastforce simp: subset_iff iT_iff)

lemma iMOD_0_subset_conv: "([r', mod 0] \<subseteq> [r, mod m]) = (r' mod m = r mod m  \<and>  r \<le> r')"
by (fastforce simp: iMOD_0 iIN_0 singleton_subset_conv iMOD_iff)

lemma iMOD_subset_conv: "0 < m \<Longrightarrow> 
  ([r', mod m'] \<subseteq> [r, mod m]) = 
  (r' mod m = r mod m  \<and>  r \<le> r'  \<and>  m' mod m = 0)"
apply (rule iffI)
 apply (frule subsetD[of _ _ r'])
  apply (simp add: iMOD_iff)
 apply (drule iMOD_subset_imp_divisor_mod_0)
 apply (simp add: iMOD_iff)
apply (rule subsetI)
apply (simp add: iMOD_iff, elim conjE)
apply (drule mod_eq_mod_0_imp_mod_eq[where m'=m' and m=m])
apply simp+
done
 
lemma iMODb_subset_mod_0_conv: "
  ([r', mod m', c'] \<subseteq> [r, mod 0, c ]) = (r'=r \<and> (m'=0 \<or> c'=0))"
by (simp add: iMODb_mod_0 iIN_0 iMODb_singleton_subset_conv)

lemma iMODb_subset_0_conv: "
  ([r', mod m', c'] \<subseteq> [r, mod m, 0 ]) = (r'=r \<and> (m'=0 \<or> c'=0))"
by (simp add: iMODb_0 iIN_0 iMODb_singleton_subset_conv)

lemma iMODb_0_subset_conv: "
  ([r', mod m', 0] \<subseteq> [r, mod m, c ]) = (r' \<in> [r, mod m, c])" 
by (simp add: iMODb_0 iIN_0)

lemma iMODb_mod_0_subset_conv: "
  ([r', mod 0, c'] \<subseteq> [r, mod m, c ]) = (r' \<in> [r, mod m, c])" 
by (simp add: iMODb_mod_0 iIN_0)

lemma iMODb_subset_conv': "\<lbrakk> 0 < c; 0 < c' \<rbrakk> \<Longrightarrow> 
  ([r', mod m', c'] \<subseteq> [r, mod m, c]) = 
  (r' mod m = r mod m  \<and>  r \<le> r'  \<and>  m' mod m = 0  \<and>
   r' + m' * c' \<le> r + m * c)"
apply (rule iffI)
 apply (frule iMODb_subset_imp_iMOD_subset, assumption)
 apply (drule iMOD_subset_imp_divisor_mod_0)
 apply (frule subsetD[OF _ iMinI_ex2[OF iMODb_not_empty]])
 apply (drule Max_subset[OF iMODb_not_empty _ iMODb_finite])
 apply (simp add: iMODb_iff iMODb_Min iMODb_Max)
apply (elim conjE)
apply (case_tac "m = 0", simp add: iMODb_mod_0)
apply (simp add: iMOD_subset_imp_iMODb_subset iMOD_subset_conv)
done

lemma iMODb_subset_conv: "\<lbrakk> 0 < m'; 0 < c' \<rbrakk> \<Longrightarrow> 
  ([r', mod m', c'] \<subseteq> [r, mod m, c]) = 
  (r' mod m = r mod m  \<and>  r \<le> r'  \<and>  m' mod m = 0  \<and>
   r' + m' * c' \<le> r + m * c)"
apply (case_tac "c = 0")
 apply (simp add: iMODb_0 iIN_0 iMODb_singleton_subset_conv linorder_not_le, intro impI)
 apply (case_tac "r' < r", simp)
 apply (simp add: linorder_not_less)
 apply (insert add_less_le_mono[of 0 "m' * c'" r r'])
 apply simp
apply (simp add: iMODb_subset_conv')
done

lemma iMODb_iMOD_subset_conv: "0 < c' \<Longrightarrow>
  ([r', mod m', c'] \<subseteq> [r, mod m]) = 
  (r' mod m = r mod m  \<and>  r \<le> r'  \<and>  m' mod m = 0)"
apply (rule iffI)
 apply (frule subsetD[OF _ iMinI_ex2[OF iMODb_not_empty]])
 apply (simp add: iMODb_Min iMOD_iff, elim conjE)
 apply (simp add: iMODb_iMOD_iTILL_conv)
 apply (subgoal_tac "[ r', mod m', c' ] \<subseteq> [ r, mod m ] \<inter> [\<dots>r' + m' * c']")
  prefer 2
  apply (simp add: iMODb_iMOD_iTILL_conv)
 apply (simp add: iMOD_iTILL_iMODb_conv iMODb_subset_imp_divisor_mod_0)
apply (rule subset_trans[OF iMODb_iMOD_subset_same])
apply (case_tac "m = 0", simp)
apply (simp add: iMOD_subset_conv)
done

lemmas iT_subset_conv =
  iFROM_subset_conv
  iFROM_iMOD_subset_conv
  iTILL_subset_conv
  iTILL_iFROM_subset_conv
  iTILL_iIN_subset_conv
  iTILL_iMOD_subset_conv
  iTILL_iMODb_subset_conv
  iIN_subset_conv
  iIN_iFROM_subset_conv
  iIN_iTILL_subset_conv
  iIN_iMOD_subset_conv
  iIN_iMODb_subset_conv
  iMOD_subset_conv
  iMOD_iFROM_subset_conv
  iMODb_subset_conv'
  iMODb_subset_conv
  iMODb_iFROM_subset_conv
  iMODb_iIN_subset_conv
  iMODb_iTILL_subset_conv
  iMODb_iMOD_subset_conv

lemma iFROM_subset: "n \<le> n' \<Longrightarrow> [n'\<dots>] \<subseteq> [n\<dots>]"
by (simp add: iFROM_subset_conv)

lemma not_iFROM_iIN_subset: "\<not> [n'\<dots>] \<subseteq> [n\<dots>,d]"
apply (rule ccontr, simp)
apply (drule subsetD[of _ _ "max n' (Suc (n + d))"])
 apply (simp add: iFROM_iff)
apply (simp add: iIN_iff)
done

lemma not_iFROM_iTILL_subset: "\<not> [n'\<dots>] \<subseteq> [\<dots>n]"
by (simp add: iIN_0_iTILL_conv [symmetric] not_iFROM_iIN_subset)

lemma not_iFROM_iMOD_subset: "m \<noteq> Suc 0 \<Longrightarrow> \<not> [n'\<dots>] \<subseteq> [r, mod m]"
apply (rule Suc_in_imp_not_subset_iMOD[of n'])
apply (simp add: iT_iff)+
done

lemma not_iFROM_iMODb_subset: "\<not> [n'\<dots>] \<subseteq> [r, mod m, c]"
by (rule infinite_not_subset_finite[OF iFROM_infinite iMODb_finite])

lemma iIN_subset: "\<lbrakk> n \<le> n'; n' + d' \<le> n + d \<rbrakk> \<Longrightarrow> [n'\<dots>,d'] \<subseteq> [n\<dots>,d]"
by (simp add: iIN_subset_conv)

lemma iIN_iFROM_subset: "n \<le> n' \<Longrightarrow> [n'\<dots>,d'] \<subseteq> [n\<dots>]"
by (simp add: subset_iff iT_iff)

lemma iIN_iTILL_subset: "n' + d' \<le> n \<Longrightarrow> [n'\<dots>,d'] \<subseteq> [\<dots>n]"
by (simp add: iIN_0_iTILL_conv[symmetric] iIN_subset)

lemma not_iIN_iMODb_subset: "\<lbrakk> 0 < d'; m \<noteq> Suc 0 \<rbrakk> \<Longrightarrow> \<not> [n'\<dots>,d'] \<subseteq> [r, mod m, c]"
apply (rule Suc_in_imp_not_subset_iMODb[of n'])
apply (simp add: iIN_iff)+
done

lemma not_iIN_iMOD_subset: "\<lbrakk> 0 < d'; m \<noteq> Suc 0 \<rbrakk> \<Longrightarrow> \<not> [n'\<dots>,d'] \<subseteq> [r, mod m]"
apply (rule ccontr, simp)
apply (case_tac "r \<le> n' + d'")
 apply (drule Int_greatest[OF _ iIN_iTILL_subset[OF order_refl]])
 apply (simp add: iMOD_iTILL_iMODb_conv not_iIN_iMODb_subset)
apply (drule subsetD[of _ _ "n'+d'"])
apply (simp add: iT_iff)+
done

lemma iTILL_subset: "n' \<le> n \<Longrightarrow> [\<dots>n'] \<subseteq> [\<dots>n]"
by (rule iTILL_subset_conv[THEN iffD2])

lemma iTILL_iFROM_subset: "([\<dots>n'] \<subseteq> [0\<dots>])"
by (simp add: iFROM_0)

lemma iTILL_iIN_subset: "n' \<le> d \<Longrightarrow> ([\<dots>n'] \<subseteq> [0\<dots>,d])"
by (simp add: iIN_0_iTILL_conv iTILL_subset)

lemma not_iTILL_iMOD_subset: "
  \<lbrakk> 0 < n'; m \<noteq> Suc 0 \<rbrakk> \<Longrightarrow> \<not> [\<dots>n'] \<subseteq> [r, mod m]"
by (simp add: iIN_0_iTILL_conv[symmetric] not_iIN_iMOD_subset)

lemma not_iTILL_iMODb_subset: "
  \<lbrakk> 0 < n'; m \<noteq> Suc 0 \<rbrakk> \<Longrightarrow> \<not> [\<dots>n'] \<subseteq> [r, mod m, c]"
by (simp add: iIN_0_iTILL_conv[symmetric] not_iIN_iMODb_subset)

lemma iMOD_iFROM_subset: "n \<le> r' \<Longrightarrow> [r', mod m'] \<subseteq> [n\<dots>]"
by (rule iMOD_iFROM_subset_conv[THEN iffD2])

lemma not_iMOD_iIN_subset: "0 < m' \<Longrightarrow> \<not> [r', mod m'] \<subseteq> [n\<dots>,d]"
by (rule infinite_not_subset_finite[OF iMOD_infinite iIN_finite])

lemma not_iMOD_iTILL_subset: "0 < m' \<Longrightarrow> \<not> [r', mod m'] \<subseteq> [\<dots>n]"
by (rule infinite_not_subset_finite[OF iMOD_infinite iTILL_finite])

lemma iMOD_subset: "
  \<lbrakk> r \<le> r'; r' mod m = r mod m; m' mod m = 0 \<rbrakk> \<Longrightarrow> [r', mod m'] \<subseteq> [r, mod m]"
apply (case_tac "m = 0", simp)
apply (simp add: iMOD_subset_conv)
done

lemma not_iMOD_iMODb_subset: "0 < m' \<Longrightarrow> \<not> [r', mod m'] \<subseteq> [r, mod m, c]"
by (rule infinite_not_subset_finite[OF iMOD_infinite iMODb_finite])

lemma iMODb_iFROM_subset: "n \<le> r' \<Longrightarrow> [r', mod m', c'] \<subseteq> [n\<dots>]"
by (rule iMODb_iFROM_subset_conv[THEN iffD2])

lemma iMODb_iTILL_subset: "
  r' + m' * c' \<le> n \<Longrightarrow> [r', mod m', c'] \<subseteq> [\<dots>n]"
by (rule iMODb_iTILL_subset_conv[THEN iffD2])

lemma iMODb_iIN_subset: "
  \<lbrakk> n \<le> r'; r' + m' * c' \<le> n + d \<rbrakk> \<Longrightarrow> [r', mod m', c'] \<subseteq> [n\<dots>,d]"
by (simp add: iMODb_iIN_subset_conv)

lemma iMODb_iMOD_subset: "
  \<lbrakk> r \<le> r'; r' mod m = r mod m; m' mod m = 0 \<rbrakk> \<Longrightarrow> [r', mod m', c'] \<subseteq> [r, mod m]"
apply (case_tac "c' = 0")
 apply (simp add: iMODb_0 iIN_0 iMOD_iff)
apply (simp add: iMODb_iMOD_subset_conv)
done

lemma iMODb_subset: "
  \<lbrakk> r \<le> r'; r' mod m = r mod m; m' mod m = 0; r' + m' * c' \<le> r + m * c \<rbrakk> \<Longrightarrow> 
  [r', mod m', c'] \<subseteq> [r, mod m, c]"
apply (case_tac "m' = 0")
 apply (simp add: iMODb_mod_0 iIN_0 iMODb_iff)
apply (case_tac "c' = 0")
 apply (simp add: iMODb_0 iIN_0 iMODb_iff)
apply (simp add: iMODb_subset_conv)
done

lemma iFROM_trans: "\<lbrakk> y \<in> [x\<dots>]; z \<in> [y\<dots>] \<rbrakk> \<Longrightarrow> z \<in> [x\<dots>]"
by (rule subsetD[OF iFROM_subset[OF iFROM_D]])

lemma iTILL_trans: "\<lbrakk> y \<in> [\<dots>x]; z \<in> [\<dots>y] \<rbrakk> \<Longrightarrow> z \<in> [\<dots>x]"
by (rule subsetD[OF iTILL_subset[OF iTILL_D]])

lemma iIN_trans: "
  \<lbrakk> y \<in> [x\<dots>,d]; z \<in> [y\<dots>,d']; d' \<le> x + d - y \<rbrakk> \<Longrightarrow> z \<in> [x\<dots>,d]"
by fastforce

lemma iMOD_trans: "
  \<lbrakk> y \<in> [x, mod m]; z \<in> [y, mod m] \<rbrakk> \<Longrightarrow> z \<in> [x, mod m]"
by (rule subsetD[OF iMOD_subset[OF iMOD_geD iMOD_modD mod_self]])

lemma iMODb_trans: "
  \<lbrakk> y \<in> [x, mod m, c]; z \<in> [y, mod m, c']; m * c' \<le> x + m * c - y \<rbrakk> \<Longrightarrow> 
  z \<in> [x, mod m, c]"
by fastforce

lemma iMODb_trans': "
  \<lbrakk> y \<in> [x, mod m, c]; z \<in> [y, mod m, c']; c' \<le> x div m + c - y div m \<rbrakk> \<Longrightarrow> 
  z \<in> [x, mod m, c]"
apply (rule iMODb_trans[where c'=c'], assumption+)
apply (frule iMODb_geD, frule div_le_mono[of x y m])
apply (simp add: add.commute[of _ c] add.commute[of _ "m*c"])
apply (drule mult_le_mono[OF le_refl, of _ _ m])
apply (simp add: add_mult_distrib2 diff_mult_distrib2 minus_mod_eq_mult_div [symmetric])
apply (simp add: iMODb_iff)
done


subsubsection \<open>Equality of intervals\<close>

lemma iFROM_eq_conv: "([n\<dots>] = [n'\<dots>]) = (n = n')"
apply (rule iffI)
 apply (drule set_eq_subset[THEN iffD1])
 apply (simp add: iFROM_subset_conv)
apply simp
done

lemma iIN_eq_conv: "([n\<dots>,d] = [n'\<dots>,d']) = (n = n' \<and> d = d')"
apply (rule iffI)
 apply (drule set_eq_subset[THEN iffD1])
 apply (simp add: iIN_subset_conv)
apply simp
done

lemma iTILL_eq_conv: "([\<dots>n] = [\<dots>n']) = (n = n')"
by (simp add: iIN_0_iTILL_conv[symmetric] iIN_eq_conv)

lemma iMOD_0_eq_conv: "([r, mod 0] = [r', mod m']) = (r = r' \<and> m' = 0)"
apply (simp add: iMOD_0 iIN_0)
apply (simp add: iMOD_singleton_eq_conv eq_sym_conv[of "{r}"] eq_sym_conv[of "r"])
done

lemma iMOD_eq_conv: "0 < m \<Longrightarrow> ([r, mod m] = [r', mod m']) = (r = r' \<and> m = m')"
apply (case_tac "m' = 0")
 apply (simp add: eq_sym_conv[of "[r, mod m]"] iMOD_0_eq_conv)
apply (rule iffI)
 apply (fastforce simp add: set_eq_subset iMOD_subset_conv)
apply simp
done

lemma iMODb_mod_0_eq_conv: "
  ([r, mod 0, c] = [r', mod m', c']) = (r = r' \<and> (m' = 0 \<or> c' = 0))"
apply (simp add: iMODb_mod_0 iIN_0)
apply (fastforce simp: iMODb_singleton_eq_conv eq_sym_conv[of "{r}"])
done

lemma iMODb_0_eq_conv: "
  ([r, mod m, 0] = [r', mod m', c']) = (r = r' \<and> (m' = 0 \<or> c' = 0))"
apply (simp add: iMODb_0 iIN_0)
apply (fastforce simp: iMODb_singleton_eq_conv eq_sym_conv[of "{r}"])
done

lemma iMODb_eq_conv: "\<lbrakk> 0 < m; 0 < c \<rbrakk> \<Longrightarrow> 
  ([r, mod m, c] = [r', mod m', c']) = (r = r' \<and> m = m' \<and> c = c')"
apply (case_tac "c' = 0")
 apply (simp add: iMODb_0 iIN_0 iMODb_singleton_eq_conv)
apply (rule iffI)
 apply (fastforce simp: set_eq_subset iMODb_subset_conv')
apply simp
done

lemma iMOD_iFROM_eq_conv: "([n\<dots>] = [r, mod m]) = (n = r \<and> m = Suc 0)"
by (fastforce simp: iMOD_1[symmetric] iMOD_eq_conv)

lemma iMODb_iIN_0_eq_conv: "
  ([n\<dots>,0] = [r, mod m, c]) = (n = r \<and> (m = 0 \<or> c = 0))"
by (simp add: iIN_0 eq_commute[of "{n}"] eq_commute[of n] iMODb_singleton_eq_conv)

lemma iMODb_iIN_eq_conv: "
  0 < d \<Longrightarrow> ([n\<dots>,d] = [r, mod m, c]) = (n = r \<and> m = Suc 0 \<and> c = d)"
by (fastforce simp: iMODb_mod_1[symmetric] iMODb_eq_conv)


subsubsection \<open>Inequality of intervals\<close>

lemma iFROM_iIN_neq: "[n'\<dots>] \<noteq> [n\<dots>,d]"
apply (rule ccontr)
apply (insert iFROM_infinite[of n'], insert iIN_finite[of n d])
apply simp
done

corollary iFROM_iTILL_neq: "[n'\<dots>] \<noteq> [\<dots>n]"
by (simp add: iIN_0_iTILL_conv[symmetric] iFROM_iIN_neq)

corollary iFROM_iMOD_neq: "m \<noteq> Suc 0 \<Longrightarrow> [n\<dots>] \<noteq> [r, mod m]"
apply (subgoal_tac "n \<in> [n\<dots>]")
 prefer 2
 apply (simp add: iFROM_iff)
apply (simp add: Suc_in_imp_neq_iMOD iFROM_Suc)
done
corollary iFROM_iMODb_neq: "[n\<dots>] \<noteq> [r, mod m, c]"
apply (rule ccontr)
apply (insert iMODb_finite[of r m c], insert iFROM_infinite[of n])
apply simp
done

corollary iIN_iMOD_neq: "0 < m \<Longrightarrow> [n\<dots>,d] \<noteq> [r, mod m]"
apply (rule ccontr)
apply (insert iMOD_infinite[of m r], insert iIN_finite[of n d])
apply simp
done

corollary iIN_iMODb_neq2: "\<lbrakk> m \<noteq> Suc 0; 0 < d \<rbrakk> \<Longrightarrow> [n\<dots>,d] \<noteq> [r, mod m, c]"
apply (subgoal_tac "n \<in> [n\<dots>,d]")
 prefer 2
 apply (simp add: iIN_iff)
apply (simp add: Suc_in_imp_neq_iMODb iIN_Suc)
done

lemma iIN_iMODb_neq: "\<lbrakk> 2 \<le> m; 0 < c \<rbrakk> \<Longrightarrow> [n\<dots>,d] \<noteq> [r, mod m, c]"
apply (simp add: nat_ge2_conv, elim conjE)
apply (case_tac "d=0")
 apply (rule not_sym)
 apply (simp add: iIN_0 iMODb_singleton_eq_conv)
apply (simp add: iIN_iMODb_neq2)
done

lemma iTILL_iIN_neq: "0 < n \<Longrightarrow> [\<dots>n'] \<noteq> [n\<dots>,d]"
by (fastforce simp: set_eq_iff iT_iff)

corollary iTILL_iMOD_neq: "0 < m \<Longrightarrow> [\<dots>n] \<noteq> [r, mod m]"
by (simp add: iIN_0_iTILL_conv[symmetric] iIN_iMOD_neq)

corollary iTILL_iMODb_neq: "
  \<lbrakk> m \<noteq> Suc 0; 0 < n \<rbrakk> \<Longrightarrow> [\<dots>n] \<noteq> [r, mod m, c]"
by (simp add: iIN_0_iTILL_conv[symmetric] iIN_iMODb_neq2)

lemma iMOD_iMODb_neq: "0 < m \<Longrightarrow> [r, mod m] \<noteq> [r', mod m', c']"
apply (rule ccontr)
apply (insert iMODb_finite[of r' m' c'], insert iMOD_infinite[of m r])
apply simp
done

lemmas iT_neq = 
  iFROM_iTILL_neq iFROM_iIN_neq iFROM_iMOD_neq iFROM_iMODb_neq
  iTILL_iIN_neq iTILL_iMOD_neq iTILL_iMODb_neq
  iIN_iMOD_neq  iIN_iMODb_neq iIN_iMODb_neq2
  iMOD_iMODb_neq


subsection \<open>Union and intersection of intervals\<close>

lemma iFROM_union': "[n\<dots>] \<union> [n'\<dots>] = [min n n'\<dots>]"
by (fastforce simp: iFROM_iff)

corollary iFROM_union: "n \<le> n' \<Longrightarrow> [n\<dots>] \<union> [n'\<dots>] = [n\<dots>]"
by (simp add: iFROM_union' min_eqL)

lemma iFROM_inter': "[n\<dots>] \<inter> [n'\<dots>] = [max n n'\<dots>]"
by (fastforce simp: iFROM_iff)

corollary iFROM_inter: "n' \<le> n \<Longrightarrow> [n\<dots>] \<inter> [n'\<dots>] = [n\<dots>]"
by (simp add: iFROM_inter' max_eqL)

lemma iTILL_union': "[\<dots>n] \<union> [\<dots>n'] = [\<dots>max n n']"
by (fastforce simp: iTILL_iff)

corollary iTILL_union: "n' \<le> n \<Longrightarrow> [\<dots>n] \<union> [\<dots>n'] = [\<dots>n]"
by (simp add: iTILL_union' max_eqL)

lemma iTILL_iFROM_union: "n \<le> n' \<Longrightarrow> [\<dots>n'] \<union> [n\<dots>] = UNIV"
by (fastforce simp: iT_iff)

lemma iTILL_inter': "[\<dots>n] \<inter> [\<dots>n'] = [\<dots>min n n']"
by (fastforce simp: iT_iff)

corollary iTILL_inter: "n \<le> n' \<Longrightarrow> [\<dots>n] \<inter> [\<dots>n'] = [\<dots>n]"
by (simp add: iTILL_inter' min_eqL)

text \<open>
  Union and intersection for iIN 
  only when there intersection is not empty and 
  none of them is other's subset,
  for instance: 
  ..  n    ..   n+d
  ..      n'    ..   n'+d'
\<close>
lemma iIN_union: "
  \<lbrakk> n \<le> n'; n' \<le> Suc (n + d); n + d \<le> n' + d' \<rbrakk> \<Longrightarrow> 
  [n\<dots>,d] \<union> [n'\<dots>,d'] = [n\<dots>,n' - n + d'] "
by (fastforce simp add: iIN_iff)

(* The case of the second interval starting directly after the first one *)
lemma iIN_append_union: "
  [n\<dots>,d] \<union> [n + d\<dots>,d'] = [n\<dots>,d + d']"
by (simp add: iIN_union)

lemma iIN_append_union_Suc: "
  [n\<dots>,d] \<union> [Suc (n + d)\<dots>,d'] = [n\<dots>,Suc (d + d')]"
by (simp add: iIN_union)

lemma iIN_append_union_pred: "
  0 < d \<Longrightarrow> [n\<dots>,d - Suc 0] \<union> [n + d\<dots>,d'] = [n\<dots>,d + d']"
by (simp add: iIN_union)

lemma iIN_iFROM_union: "
  n' \<le> Suc (n + d) \<Longrightarrow> [n\<dots>,d] \<union> [n'\<dots>] = [min n n'\<dots>]"
by (fastforce simp: iIN_iff)

lemma iIN_iFROM_append_union: "
  [n\<dots>,d] \<union> [n + d\<dots>] = [n\<dots>]"
by (simp add: iIN_iFROM_union min_eqL)

lemma iIN_iFROM_append_union_Suc: "
  [n\<dots>,d] \<union> [Suc (n + d)\<dots>] = [n\<dots>]"
by (simp add: iIN_iFROM_union min_eqL)

lemma iIN_iFROM_append_union_pred: "
  0 < d \<Longrightarrow> [n\<dots>,d - Suc 0] \<union> [n + d\<dots>] = [n\<dots>]"
by (simp add: iIN_iFROM_union min_eqL)


lemma iIN_inter: "
  \<lbrakk> n \<le> n'; n' \<le> n + d; n + d \<le> n' + d' \<rbrakk> \<Longrightarrow>
  [n\<dots>,d] \<inter> [n'\<dots>,d'] = [n'\<dots>,n + d - n']"
by (fastforce simp: iIN_iff)

lemma iMOD_union: "
  \<lbrakk> r \<le> r'; r mod m = r' mod m \<rbrakk> \<Longrightarrow>
  [r, mod m] \<union> [r', mod m] = [r, mod m]"
by (fastforce simp: iT_iff)
lemma iMOD_union': "
  r mod m = r' mod m \<Longrightarrow>
  [r, mod m] \<union> [r', mod m] = [min r r', mod m]"
apply (case_tac "r \<le> r'")
apply (fastforce simp: iMOD_union min_eq)+
done

lemma iMOD_inter: "
  \<lbrakk> r \<le> r'; r mod m = r' mod m \<rbrakk> \<Longrightarrow>
  [r, mod m] \<inter> [r', mod m] = [r', mod m]"
by (fastforce simp: iT_iff)

lemma iMOD_inter': "
  r mod m = r' mod m \<Longrightarrow> 
  [r, mod m] \<inter> [r', mod m] = [max r r', mod m]"
apply (case_tac "r \<le> r'")
apply (fastforce simp: iMOD_inter max_eq)+
done

lemma iMODb_union: "
  \<lbrakk> r \<le> r'; r mod m = r' mod m; r' \<le> r + m * c; r + m * c \<le> r' + m * c' \<rbrakk> \<Longrightarrow>
  [r, mod m, c] \<union> [r', mod m, c'] = [r, mod m, r' div m - r div m + c']"
apply (rule set_eqI)
apply (simp add: iMODb_iff)
apply (drule sym[of "r mod m"], simp)
apply (fastforce simp: add_mult_distrib2 diff_mult_distrib2 minus_mod_eq_mult_div [symmetric])
done

lemma iMODb_append_union: "
  [r, mod m, c] \<union> [ r + m * c, mod m, c'] = [r, mod m, c + c']"
apply (insert iMODb_union[of r "r + m * c" m c c'])
apply (case_tac "m = 0")
 apply (simp add: iMODb_mod_0)
apply simp
done

lemma iMODb_iMOD_append_union': "
  \<lbrakk> r mod m = r' mod m; r' \<le> r + m * Suc c \<rbrakk>  \<Longrightarrow> 
  [r, mod m, c] \<union> [ r', mod m ] = [min r r', mod m]"
apply (subgoal_tac "(min r r') mod m = r' mod m")
 prefer 2
 apply (simp add: min_def)
apply (rule set_eqI)
apply (simp add: iT_iff)
apply (drule sym[of "r mod m"], simp)
apply (rule iffI)
 apply fastforce
apply (clarsimp simp: linorder_not_le)
apply (case_tac "r \<le> r'")
apply (simp add: min_eqL)
apply (rule add_le_imp_le_right[of _ m])
apply (rule less_mod_eq_imp_add_divisor_le)
apply simp+
done

lemma iMODb_iMOD_append_union: "
  \<lbrakk> r \<le> r'; r mod m = r' mod m; r' \<le> r + m * Suc c \<rbrakk>  \<Longrightarrow> 
  [r, mod m, c] \<union> [ r', mod m ] = [r, mod m]"
by (simp add: iMODb_iMOD_append_union' min_eqL)

lemma iMODb_append_union_Suc: "
  [r, mod m, c] \<union> [ r + m * Suc c, mod m, c'] = [r, mod m, Suc (c + c')]"
apply (subst insert_absorb[of "r + m * c" "[r, mod m, c] \<union> [ r + m * Suc c, mod m, c']", symmetric])
 apply (simp add: iT_iff)
apply (simp del: Un_insert_right add: Un_insert_right[symmetric] add.commute[of m] add.assoc[symmetric] iMODb_Suc_pred_insert_conv)
apply (simp add: iMODb_append_union)
done

lemma iMODb_append_union_pred: "
  0 < c \<Longrightarrow> [r, mod m, c - Suc 0] \<union> [ r + m * c, mod m, c'] = [r, mod m, c + c']"
by (insert iMODb_append_union_Suc[of r m "c - Suc 0" c'], simp)


lemma iMODb_inter: "
  \<lbrakk> r \<le> r'; r mod m = r' mod m; r' \<le> r + m * c; r + m * c \<le> r' + m * c' \<rbrakk> \<Longrightarrow>
  [r, mod m, c] \<inter> [r', mod m, c'] = [r', mod m, c - (r'-r) div m]"
apply (rule set_eqI)
apply (simp add: iMODb_iff)
apply (simp add: diff_mult_distrib2)
apply (simp add: mult.commute[of _ "(r' - r) div m"])
apply (simp add: mod_0_div_mult_cancel[THEN iffD1, OF mod_eq_imp_diff_mod_0])
apply (simp add: add.commute[of _ r])
apply fastforce
done


lemmas iT_union' = 
  iFROM_union'
  iTILL_union'
  iMOD_union'
  iMODb_iMOD_append_union'
lemmas iT_union =
  iFROM_union
  iTILL_union
  iTILL_iFROM_union
  iIN_union
  iIN_iFROM_union
  iMOD_union
  iMODb_union
lemmas iT_union_append =
  iIN_append_union
  iIN_append_union_Suc
  iIN_append_union_pred
  iIN_iFROM_append_union
  iIN_iFROM_append_union_Suc
  iIN_iFROM_append_union_pred
  iMODb_append_union
  iMODb_iMOD_append_union
  iMODb_append_union_Suc
  iMODb_append_union_pred

lemmas iT_inter' =
  iFROM_inter'
  iTILL_inter'
  iMOD_inter'
lemmas iT_inter =
  iFROM_inter
  iTILL_inter
  iIN_inter
  iMOD_inter
  iMODb_inter


lemma mod_partition_Union: "
  0 < m \<Longrightarrow> (\<Union>k. A \<inter> [k * m\<dots>,m - Suc 0]) = A"
apply simp
apply (rule subst[where s=UNIV and P="\<lambda>x. A \<inter> x = A"])
apply (rule set_eqI)
 apply (simp add: iT_iff)
 apply (rule_tac x="x div m" in exI)
 apply (simp add: div_mult_cancel)
 apply (subst add.commute)
 apply (rule le_add_diff)
 apply (simp add: Suc_mod_le_divisor)
apply simp
done

lemma finite_mod_partition_Union: "
  \<lbrakk> 0 < m; finite A \<rbrakk> \<Longrightarrow>
  (\<Union>k\<le>Max A div m. A \<inter> [k*m\<dots>,m - Suc 0]) = A"
apply (rule subst[OF mod_partition_Union[of m], where
  P="\<lambda>x. (\<Union>k\<le>Max A div m. A \<inter> [k*m\<dots>,m - Suc 0]) = x"])
 apply assumption
apply (rule set_eqI)
apply (simp add: iIN_iff)
apply (rule iffI, blast)
apply clarsimp
apply (rename_tac x x1)
apply (rule_tac x="x div m" in bexI)
apply (frule in_imp_not_empty[where A=A])
apply (frule_tac Max_ge, assumption)
apply (cut_tac n=x and k="x div m" and m=m in div_imp_le_less)
apply clarsimp+
apply (drule_tac m=x in less_imp_le_pred)
apply (simp add: add.commute[of m])
apply (simp add: div_le_mono)
done

lemma mod_partition_is_disjoint: "
  \<lbrakk> 0 < (m::nat); k \<noteq> k' \<rbrakk> \<Longrightarrow> 
  (A \<inter> [k * m\<dots>,m - Suc 0]) \<inter>  (A \<inter> [k' * m\<dots>,m - Suc 0]) = {}"
apply (clarsimp simp add: all_not_in_conv[symmetric] iT_iff)
apply (subgoal_tac "\<And>k. \<lbrakk> k * m \<le> x; x \<le> k * m + m - Suc 0 \<rbrakk> \<Longrightarrow> x div m = k")
 apply blast
apply (rule le_less_imp_div, assumption)
apply simp
done


subsection \<open>Cutting intervals\<close>

(*
lemma "[10\<dots>,5] \<down>< 12 = [10\<dots>,1]"
apply (simp add: iT_iff cut_less_def)
apply (simp add: iT_defs set_interval_defs Collect_conj_eq[symmetric])
apply fastforce
done
*)

lemma iTILL_cut_le: "[\<dots>n] \<down>\<le> t = (if t \<le> n then [\<dots>t] else [\<dots>n])"
unfolding i_cut_defs iT_defs atMost_def
by force

corollary iTILL_cut_le1: "t \<in> [\<dots>n] \<Longrightarrow> [\<dots>n] \<down>\<le> t = [\<dots>t]"
by (simp add: iTILL_cut_le iT_iff)

corollary iTILL_cut_le2: "t \<notin> [\<dots>n] \<Longrightarrow> [\<dots>n] \<down>\<le> t = [\<dots>n]"
by (simp add: iTILL_cut_le iT_iff)


lemma iFROM_cut_le: "
  [n\<dots>] \<down>\<le> t = 
  (if t < n then {} else [n\<dots>,t-n])"
by (simp add: set_eq_iff i_cut_mem_iff iT_iff)

corollary iFROM_cut_le1: "t \<in> [n\<dots>] \<Longrightarrow> [n\<dots>] \<down>\<le> t = [n\<dots>,t - n]"
by (simp add: iFROM_cut_le iT_iff) 

lemma iIN_cut_le: "
  [n\<dots>,d] \<down>\<le> t = (
  if t < n then {} else 
  if t \<le> n+d then [n\<dots>,t-n]
  else [n\<dots>,d])"
by (force simp: set_eq_iff i_cut_mem_iff iT_iff)

corollary iIN_cut_le1: "
  t \<in> [n\<dots>,d] \<Longrightarrow> [n\<dots>,d] \<down>\<le> t = [n\<dots>,t - n]"
by (simp add: iIN_cut_le iT_iff)


lemma iMOD_cut_le: "
  [r, mod m] \<down>\<le> t = (
  if t < r then {} 
  else [r, mod m, (t - r) div m])"
apply (case_tac "m = 0")
 apply (simp add: iMOD_0 iMODb_0 iIN_0 i_cut_empty i_cut_singleton)
apply (case_tac "t < r")
 apply (simp add: cut_le_Min_empty iMOD_Min)
apply (clarsimp simp: linorder_not_less set_eq_iff i_cut_mem_iff iT_iff)
apply (rule conj_cong, simp)+
apply (clarsimp simp: minus_mod_eq_mult_div [symmetric])
apply (drule_tac x=r and y=x in le_imp_less_or_eq, erule disjE)
 prefer 2
 apply simp
apply (drule_tac x=r and y=x and m=m in less_mod_eq_imp_add_divisor_le, simp)
apply (rule iffI)
 apply (rule_tac x=x in subst[OF mod_eq_imp_diff_mod_eq[of _ m r t], rule_format], simp+)
 apply (subgoal_tac "r + (t - x) mod m \<le> t")
  prefer 2
  apply (simp add: order_trans[OF add_le_mono2[OF mod_le_divisor]])
 apply simp
 apply (simp add: le_imp_sub_mod_le)
apply (subgoal_tac "r + (t - r) mod m \<le> t")
 prefer 2
 apply (rule ccontr)
 apply simp
apply simp
done

lemma iMOD_cut_le1: "
  t \<in> [r, mod m] \<Longrightarrow> 
  [r, mod m] \<down>\<le> t = [r, mod m, (t - r) div m]"
by (simp add: iMOD_cut_le iT_iff)

lemma iMODb_cut_le: "
  [r, mod m, c] \<down>\<le> t = (
    if t < r then {} 
    else if t < r + m * c then [r, mod m, (t - r) div m]
    else [r, mod m, c])"
apply (case_tac "m = 0")
 apply (simp add: iMODb_mod_0 iIN_0 cut_le_singleton)
apply (case_tac "t < r")
 apply (simp add: cut_le_Min_empty iT_Min)
apply (case_tac "r + m * c \<le> t")
 apply (simp add: cut_le_Max_all iT_Max iT_finite)
apply (simp add: linorder_not_le linorder_not_less)
apply (rule_tac t=c and s="(r + m * c - r) div m" in subst, simp)
apply (subst iMOD_iTILL_iMODb_conv[symmetric], simp)
apply (simp add: cut_le_Int_right iTILL_cut_le)
apply (simp add: iMOD_iTILL_iMODb_conv)
done

lemma iMODb_cut_le1: "
  t \<in> [r, mod m, c] \<Longrightarrow> 
  [r, mod m, c] \<down>\<le> t = [r, mod m, (t - r) div m]"
by (clarsimp simp: iMODb_cut_le iT_iff iMODb_mod_0)


lemma iTILL_cut_less: "
  [\<dots>n] \<down>< t = (
    if n < t then [\<dots>n] else
    if t = 0 then {} 
    else [\<dots>t - Suc 0])"
apply (case_tac "n < t")
 apply (simp add: cut_less_Max_all iT_Max iT_finite)
apply (case_tac "t = 0")
 apply (simp add: cut_less_0_empty)
apply (fastforce simp: nat_cut_less_le_conv iTILL_cut_le)
done

lemma iTILL_cut_less1: "
  \<lbrakk> t \<in> [\<dots>n]; 0 < t \<rbrakk> \<Longrightarrow> [\<dots>n] \<down>< t = [\<dots>t - Suc 0]"
by (simp add: iTILL_cut_less iT_iff)


lemma iFROM_cut_less: "
  [n\<dots>] \<down>< t = (
    if t \<le> n then {}
    else [n\<dots>,t - Suc n])"
apply (case_tac "t \<le> n")
 apply (simp add: cut_less_Min_empty iT_Min)
apply (fastforce simp: nat_cut_less_le_conv iFROM_cut_le)
done

lemma iFROM_cut_less1: "
  n < t \<Longrightarrow> [n\<dots>] \<down>< t = [n\<dots>,t - Suc n]"
by (simp add: iFROM_cut_less)


lemma iIN_cut_less: "
  [n\<dots>,d] \<down>< t = ( 
    if t \<le> n then {} else
    if t \<le> n + d then [n\<dots>, t - Suc n]
    else [n\<dots>,d])"
apply (case_tac "t \<le> n")
 apply (simp add: cut_less_Min_empty iT_Min )
apply (case_tac "n + d < t")
 apply (simp add: cut_less_Max_all iT_Max iT_finite)
apply (fastforce simp: nat_cut_less_le_conv iIN_cut_le)
done


lemma iIN_cut_less1: "
  \<lbrakk> t \<in> [n\<dots>,d]; n < t \<rbrakk> \<Longrightarrow> [n\<dots>,d] \<down>< t = [n\<dots>, t - Suc n]"
by (simp add: iIN_cut_less iT_iff)

lemma iMOD_cut_less: "
  [r, mod m] \<down>< t = (
    if t \<le> r then {} 
    else [r, mod m, (t - Suc r) div m])"
apply (case_tac "t = 0")
 apply (simp add: cut_less_0_empty)
apply (simp add: nat_cut_less_le_conv iMOD_cut_le)
apply fastforce
done

lemma iMOD_cut_less1: "
  \<lbrakk> t \<in> [r, mod m]; r < t \<rbrakk> \<Longrightarrow> 
  [r, mod m] \<down>< t = [r, mod m, (t - r) div m - Suc 0]"
apply (case_tac "m = 0")
 apply (simp add: iMOD_0 iMODb_mod_0 iIN_0)
apply (simp add: iMOD_cut_less)
apply (simp add: mod_0_imp_diff_Suc_div_conv mod_eq_imp_diff_mod_0 iT_iff)
done

lemma iMODb_cut_less: "
  [r, mod m, c] \<down>< t = (
    if t \<le> r then {} else
    if r + m * c < t then [r, mod m, c]
    else [r, mod m, (t - Suc r) div m])"
apply (case_tac "t = 0")
 apply (simp add: cut_less_0_empty)
apply (simp add: nat_cut_less_le_conv iMODb_cut_le)
apply fastforce
done

lemma iMODb_cut_less1: "\<lbrakk> t \<in> [r, mod m, c]; r < t \<rbrakk> \<Longrightarrow> 
  [r, mod m, c] \<down>< t = [r, mod m, (t - r) div m - Suc 0]"
apply (case_tac "m = 0")
 apply (simp add: iMODb_mod_0 iIN_0)
apply (simp add: iMODb_cut_less)
apply (simp add: mod_0_imp_diff_Suc_div_conv mod_eq_imp_diff_mod_0 iT_iff)
done


lemmas iT_cut_le =
  iTILL_cut_le
  iFROM_cut_le
  iIN_cut_le
  iMOD_cut_le
  iMODb_cut_le

lemmas iT_cut_le1 =
  iTILL_cut_le1
  iFROM_cut_le1
  iIN_cut_le1
  iMOD_cut_le1
  iMODb_cut_le1

lemmas iT_cut_less =
  iTILL_cut_less
  iFROM_cut_less
  iIN_cut_less
  iMOD_cut_less
  iMODb_cut_less

lemmas iT_cut_less1 =
  iTILL_cut_less1
  iFROM_cut_less1
  iIN_cut_less1
  iMOD_cut_less1
  iMODb_cut_less1

lemmas iT_cut_le_less =
  iTILL_cut_le
  iTILL_cut_less
  iFROM_cut_le
  iFROM_cut_less
  iIN_cut_le
  iIN_cut_less
  iMOD_cut_le
  iMOD_cut_less
  iMODb_cut_le
  iMODb_cut_less

lemmas iT_cut_le_less1 =
  iTILL_cut_le1
  iTILL_cut_less1
  iFROM_cut_le1
  iFROM_cut_less1
  iIN_cut_le1
  iIN_cut_less1
  iMOD_cut_le1
  iMOD_cut_less1
  iMODb_cut_le1
  iMODb_cut_less1

lemma iTILL_cut_ge: "
  [\<dots>n] \<down>\<ge> t = (if n < t then {} else [t\<dots>,n-t])"
by (force simp: i_cut_mem_iff iT_iff)

corollary iTILL_cut_ge1: "t \<in> [\<dots>n] \<Longrightarrow> [\<dots>n] \<down>\<ge> t = [t\<dots>,n-t]"
by (simp add: iTILL_cut_ge iT_iff)

corollary iTILL_cut_ge2: "t \<notin> [\<dots>n] \<Longrightarrow> [\<dots>n] \<down>\<ge> t = {}"
by (simp add: iTILL_cut_ge iT_iff)

lemma iTILL_cut_greater: "
  [\<dots>n] \<down>> t = (if n \<le> t then {} else [Suc t\<dots>,n - Suc t])"
by (force simp: i_cut_mem_iff iT_iff)

corollary iTILL_cut_greater1: "
  t \<in> [\<dots>n] \<Longrightarrow> t < n \<Longrightarrow> [\<dots>n] \<down>> t = [Suc t\<dots>,n - Suc t]"
by (simp add: iTILL_cut_greater iT_iff)

corollary iTILL_cut_greater2: "t \<notin> [\<dots>n] \<Longrightarrow> [\<dots>n] \<down>> t = {}"
by (simp add: iTILL_cut_greater iT_iff)


lemma iFROM_cut_ge: "
  [n\<dots>] \<down>\<ge> t = (if n \<le> t then [t\<dots>] else [n\<dots>])"
by (force simp: i_cut_mem_iff iT_iff)
corollary iFROM_cut_ge1: "t \<in> [n\<dots>] \<Longrightarrow> [n\<dots>] \<down>\<ge> t = [t\<dots>]"
by (simp add: iFROM_cut_ge iT_iff) 

lemma iFROM_cut_greater: "
  [n\<dots>] \<down>> t = (if n \<le> t then [Suc t\<dots>] else [n\<dots>])"
by (force simp: i_cut_mem_iff iT_iff)
corollary iFROM_cut_greater1: "
  t \<in> [n\<dots>] \<Longrightarrow> [n\<dots>] \<down>> t = [Suc t\<dots>]"
by (simp add: iFROM_cut_greater iT_iff) 

lemma iIN_cut_ge: "
  [n\<dots>,d] \<down>\<ge> t = (
    if t < n then [n\<dots>,d] else 
    if t \<le> n+d then [t\<dots>,n+d-t]
    else {})"
by (force simp: i_cut_mem_iff iT_iff)

corollary iIN_cut_ge1: "t \<in> [n\<dots>,d] \<Longrightarrow> 
  [n\<dots>,d] \<down>\<ge> t = [t\<dots>,n+d-t]"
by (simp add: iIN_cut_ge iT_iff) 

corollary iIN_cut_ge2: "t \<notin> [n\<dots>,d] \<Longrightarrow> 
  [n\<dots>,d] \<down>\<ge> t = (if t < n then [n\<dots>,d] else {})"
by (simp add: iIN_cut_ge iT_iff)


lemma iIN_cut_greater: "
  [n\<dots>,d] \<down>> t = (
    if t < n then [n\<dots>,d] else 
    if t < n+d then [Suc t\<dots>,n + d - Suc t]
    else {})"
by (force simp: i_cut_mem_iff iT_iff)

corollary iIN_cut_greater1: "
  \<lbrakk> t \<in> [n\<dots>,d]; t < n + d \<rbrakk>\<Longrightarrow>
  [n\<dots>,d] \<down>> t = [Suc t\<dots>,n + d - Suc t]"
by (simp add: iIN_cut_greater iT_iff) 


(*
lemma "let m=5 in let r = 12 in let t = 16 in
  [r, mod m] \<down>> t = (
  if t < r then [r, mod m] else
  if (m = 0 \<and> r \<le> t) then {}
  else [r + (t - r) div m * m + m, mod m])"
apply (simp add: Let_def)
oops
lemma "let m=5 in let r = 12 in let t = 16 in
  [r, mod m] \<down>> t = (
  if t < r then [r, mod m] else
  if (m = 0 \<and> r \<le> t) then {}
  else [t + m - (t - r) mod m, mod m])"
apply (simp add: Let_def)
oops
*)

lemma mod_cut_greater_aux_t_less: "
  \<lbrakk> 0 < (m::nat); r \<le> t \<rbrakk> \<Longrightarrow> 
  t < t + m - (t - r) mod m"
by (simp add: less_add_diff add.commute)

lemma mod_cut_greater_aux_le_x: "
  \<lbrakk> (r::nat) \<le> t; t < x; x mod m = r mod m\<rbrakk> \<Longrightarrow> 
  t + m - (t - r) mod m \<le> x"
apply (insert diff_mod_le[of t r m])
apply (subst diff_add_assoc2, simp)
apply (rule less_mod_eq_imp_add_divisor_le, simp)
apply (simp add: sub_diff_mod_eq)
done

lemma iMOD_cut_greater: "
  [r, mod m] \<down>> t = (
    if t < r then [r, mod m] else
    if m = 0 then {}
    else [t + m - (t - r) mod m, mod m])"
apply (case_tac "m = 0")
 apply (simp add: iMOD_0 iIN_0 i_cut_singleton)
apply (case_tac "t < r")
 apply (simp add: iT_Min cut_greater_Min_all)
apply (simp add: linorder_not_less)
apply (simp add: set_eq_iff i_cut_mem_iff iT_iff, clarify)
apply (subgoal_tac "(t - r) mod m \<le> t")
 prefer 2
 apply (rule order_trans[OF mod_le_dividend], simp)
apply (simp add: diff_add_assoc2 del: add_diff_assoc2)
apply (simp add: sub_diff_mod_eq del: add_diff_assoc2)
apply (rule conj_cong, simp)
apply (rule iffI)
 apply clarify
 apply (rule less_mod_eq_imp_add_divisor_le)
  apply simp
 apply (simp add: sub_diff_mod_eq)
apply (subgoal_tac "t < x")
 prefer 2
 apply (rule_tac y="t - (t - r) mod m + m" in order_less_le_trans)
  apply (simp add: mod_cut_greater_aux_t_less)
 apply simp+
done

lemma iMOD_cut_greater1: "
  t \<in> [r, mod m] \<Longrightarrow> 
  [r, mod m] \<down>> t = (
    if m = 0 then {}
    else [t + m, mod m])"
by (simp add: iMOD_cut_greater iT_iff mod_eq_imp_diff_mod_0)

lemma iMODb_cut_greater_aux: "
  \<lbrakk> 0 < m; t < r + m * c; r \<le> t\<rbrakk> \<Longrightarrow> 
  (r + m * c - (t + m - (t - r) mod m)) div m =
  c - Suc ((t - r) div m)"
apply (subgoal_tac "r \<le> t + m - (t - r) mod m")
 prefer 2
 apply (rule order_trans[of _ t], simp)
 apply (simp add: mod_cut_greater_aux_t_less less_imp_le)
apply (rule_tac t="(r + m * c - (t + m - (t - r) mod m))" and s="m * (c - Suc ((t - r) div m))" in subst)
 apply (simp add: diff_mult_distrib2 minus_mod_eq_mult_div [symmetric] del: diff_diff_left)
apply simp
done

lemma iMODb_cut_greater: "
  [r, mod m, c] \<down>> t = (
    if t < r then [r, mod m, c] else
    if r + m * c \<le> t then {}
    else [t + m - (t - r) mod m, mod m, c - Suc ((t-r) div m)])"
apply (case_tac "m = 0") 
 apply (simp add: iMODb_mod_0 iIN_0 i_cut_singleton)
apply (case_tac "r + m * c \<le> t")
 apply (simp add: cut_greater_Max_empty iT_Max iT_finite)
apply (case_tac "t < r")
 apply (simp add: cut_greater_Min_all iT_Min)
apply (simp add: linorder_not_less linorder_not_le)
apply (rule_tac t="[ r, mod m, c ]" and s="[ r, mod m ] \<inter> [\<dots>r + m * c]" in subst)
 apply (simp add: iMOD_iTILL_iMODb_conv)
apply (simp add: i_cut_Int_left iMOD_cut_greater)
apply (subst iMOD_iTILL_iMODb_conv)
 apply (rule mod_cut_greater_aux_le_x, simp+)
apply (simp add: iMODb_cut_greater_aux)
done

lemma iMODb_cut_greater1: "
  t \<in> [r, mod m, c] \<Longrightarrow> 
    [r, mod m, c] \<down>> t = (
    if r + m * c \<le> t then {}
    else [t + m, mod m, c - Suc ((t-r) div m)])"
by (simp add: iMODb_cut_greater iT_iff mod_eq_imp_diff_mod_0)

(*
lemma "let m=5 in let r = 12 in let t = 17 in
  [r, mod m] \<down>\<ge> t = (
  if t \<le> r then [r, mod m] else
  if m=0 then {}
  else [t + m - Suc ((t - Suc r) mod m), mod m])"
apply (simp add: Let_def)
oops
*)

lemma iMOD_cut_ge: "
  [r, mod m] \<down>\<ge> t = (
    if t \<le> r then [r, mod m] else
    if m = 0 then {} 
    else [t + m - Suc ((t - Suc r) mod m), mod m])"
apply (case_tac "t = 0")
 apply (simp add: cut_ge_0_all)
apply (force simp: nat_cut_greater_ge_conv[symmetric] iMOD_cut_greater)
done

lemma iMOD_cut_ge1: "
  t \<in> [r, mod m] \<Longrightarrow> 
  [r, mod m] \<down>\<ge> t = [t, mod m]"
by (fastforce simp: iMOD_cut_ge)

(*
lemma "let m=5 in let r = 12 in let t = 21 in let c=5 in
  [r, mod m, c] \<down>\<ge> t = (
    if t \<le> r then [r, mod m, c] else
    if r + m * c < t then {} 
    else [t + m - Suc ((t - Suc r) mod m), mod m, c - (t + m - Suc r) div m])"
apply (simp add: Let_def)
oops
*)

lemma iMODb_cut_ge: "
  [r, mod m, c] \<down>\<ge> t = (
    if t \<le> r then [r, mod m, c] else
    if r + m * c < t then {} 
    else [t + m - Suc ((t - Suc r) mod m), mod m, c - (t + m - Suc r) div m])"
apply (case_tac "m = 0") 
 apply (simp add: iMODb_mod_0 iIN_0 i_cut_singleton)
apply (case_tac "r + m * c < t")
 apply (simp add: cut_ge_Max_empty iT_Max iT_finite)
apply (case_tac "t \<le> r")
 apply (simp add: cut_ge_Min_all iT_Min)
apply (simp add: linorder_not_less linorder_not_le)
apply (case_tac "r mod m = t mod m")
 apply (simp add: diff_mod_pred)
 apply (simp add: mod_0_imp_diff_Suc_div_conv mod_eq_diff_mod_0_conv diff_add_assoc2 del: add_diff_assoc2)
 apply (subgoal_tac "0 < (t - r) div m")
  prefer 2
  apply (frule_tac x=r in less_mod_eq_imp_add_divisor_le)
   apply (simp add: mod_eq_diff_mod_0_conv)
  apply (drule add_le_imp_le_diff2)
  apply (drule_tac m=m and k=m in div_le_mono)
  apply simp
 apply (simp add: set_eq_iff i_cut_mem_iff iT_iff, intro allI)
 apply (simp add: mod_eq_diff_mod_0_conv[symmetric])
 apply (rule conj_cong, simp)
 apply (case_tac "t \<le> x")
  prefer 2
  apply simp
 apply (simp add: diff_mult_distrib2 minus_mod_eq_mult_div [symmetric] mod_eq_diff_mod_0_conv add.commute[of r])
apply (subgoal_tac "Suc ((t - Suc r) mod m) = (t - r) mod m")
 prefer 2
 apply (clarsimp simp add: diff_mod_pred mod_eq_diff_mod_0_conv)
apply (rule_tac t="[ r, mod m, c ]" and s="[ r, mod m ] \<inter> [\<dots>r + m * c]" in subst)
 apply (simp add: iMOD_iTILL_iMODb_conv)
apply (simp add: i_cut_Int_left iMOD_cut_ge)
apply (subst iMOD_iTILL_iMODb_conv)
 apply (drule_tac x=t in le_imp_less_or_eq, erule disjE)
 apply (rule mod_cut_greater_aux_le_x, simp+)
apply (rule arg_cong [where y="c - (t + m - Suc r) div m"])
apply (drule_tac x=t in le_imp_less_or_eq, erule disjE)
 prefer 2
 apply simp
apply (simp add: iMODb_cut_greater_aux)
apply (rule arg_cong[where f="(-) c"])
apply (simp add: diff_add_assoc2 del: add_diff_assoc2)
apply (rule_tac t="t - Suc r" and s="t - r - Suc 0" in subst, simp)
apply (subst div_diff1_eq[of _ "Suc 0"])
apply (case_tac "m = Suc 0", simp)
apply simp
done

lemma iMODb_cut_ge1: "
  t \<in> [r, mod m, c] \<Longrightarrow>
  [r, mod m, c] \<down>\<ge> t = (
    if r + m * c < t then {} 
    else [t, mod m, c - (t - r) div m])"
apply (case_tac "m = 0")
 apply (simp add: iMODb_mod_0 iT_iff iIN_0 i_cut_singleton)
apply (clarsimp simp: iMODb_cut_ge iT_iff)
apply (simp add: mod_eq_imp_diff_mod_eq_divisor)
apply (rule_tac t="t + m - Suc r" and s="t - r + (m - Suc 0)" in subst, simp)
apply (subst div_add1_eq)
apply (simp add: mod_eq_imp_diff_mod_0)
done

lemma iMOD_0_cut_greater: "
  t \<in> [r, mod 0] \<Longrightarrow> [r, mod 0] \<down>> t = {}"
by (simp add: iT_iff iMOD_0 iIN_0 i_cut_singleton)
lemma iMODb_0_cut_greater: "t \<in> [r, mod 0, c] \<Longrightarrow>
  [r, mod 0, c] \<down>> t = {}"
by (simp add: iT_iff iMODb_mod_0 iIN_0 i_cut_singleton)

lemmas iT_cut_ge =
  iTILL_cut_ge
  iFROM_cut_ge
  iIN_cut_ge
  iMOD_cut_ge
  iMODb_cut_ge

lemmas iT_cut_ge1 =
  iTILL_cut_ge1
  iFROM_cut_ge1
  iIN_cut_ge1
  iMOD_cut_ge1
  iMODb_cut_ge1

lemmas iT_cut_greater =
  iTILL_cut_greater
  iFROM_cut_greater
  iIN_cut_greater
  iMOD_cut_greater
  iMODb_cut_greater

lemmas iT_cut_greater1 =
  iTILL_cut_greater1
  iFROM_cut_greater1
  iIN_cut_greater1
  iMOD_cut_greater1
  iMODb_cut_greater1

lemmas iT_cut_ge_greater =
  iTILL_cut_ge
  iTILL_cut_greater
  iFROM_cut_ge
  iFROM_cut_greater
  iIN_cut_ge
  iIN_cut_greater
  iMOD_cut_ge
  iMOD_cut_greater
  iMODb_cut_ge
  iMODb_cut_greater
lemmas iT_cut_ge_greater1 =
  iTILL_cut_ge1
  iTILL_cut_greater1
  iFROM_cut_ge1
  iFROM_cut_greater1
  iIN_cut_ge1
  iIN_cut_greater1
  iMOD_cut_ge1
  iMOD_cut_greater1
  iMODb_cut_ge1
  iMODb_cut_greater1


subsection \<open>Cardinality of intervals\<close>

lemma iFROM_card: "card [n\<dots>] = 0"
by (simp add: iFROM_infinite)

lemma iTILL_card: "card [\<dots>n] = Suc n"
by (simp add: iTILL_def)

lemma iIN_card: "card [n\<dots>,d] = Suc d"
by (simp add: iIN_def)

lemma iMOD_0_card: "card [r, mod 0] = Suc 0"
by (simp add: iMOD_0 iIN_card)

lemma iMOD_card: "0 < m \<Longrightarrow> card [r, mod m] = 0"
by (simp add: iMOD_infinite)

lemma iMOD_card_if: "card [r, mod m] = (if m = 0 then Suc 0 else 0)"
by (simp add: iMOD_0_card iMOD_card)

lemma iMODb_mod_0_card: "card [r, mod 0, c] = Suc 0"
by (simp add: iMODb_mod_0 iIN_card)

lemma iMODb_card: "0 < m \<Longrightarrow> card [r, mod m, c] = Suc c"
apply (induct c)
 apply (simp add: iMODb_0 iIN_card)
apply (subst iMODb_Suc_insert_conv[symmetric])
apply (subst card_insert_disjoint)
apply (simp add: iT_finite iT_iff)+
done

lemma iMODb_card_if: "
  card [r, mod m, c] = (if m = 0 then Suc 0 else Suc c)"
by (simp add: iMODb_mod_0_card iMODb_card)

lemmas iT_card =
  iFROM_card
  iTILL_card
  iIN_card
  iMOD_card_if
  iMODb_card_if

text \<open>Cardinality with \<open>icard\<close>\<close>

lemma iFROM_icard: "icard [n\<dots>] = \<infinity>"
by (simp add: iFROM_infinite)

lemma iTILL_icard: "icard [\<dots>n] = enat (Suc n)"
by (simp add: icard_finite iT_finite iT_card)

lemma iIN_icard: "icard [n\<dots>,d] = enat (Suc d)"
by (simp add: icard_finite iT_finite iT_card)

lemma iMOD_0_icard: "icard [r, mod 0] = eSuc 0"
by (simp add: icard_finite iT_finite iT_card eSuc_enat)

lemma iMOD_icard: "0 < m \<Longrightarrow> icard [r, mod m] = \<infinity>"
by (simp add: iMOD_infinite)

lemma iMOD_icard_if: "icard [r, mod m] = (if m = 0 then eSuc 0 else \<infinity>)"
by (simp add: icard_finite iT_finite iT_infinite eSuc_enat iT_card)

lemma iMODb_mod_0_icard: "icard [r, mod 0, c] = eSuc 0"
by (simp add: icard_finite iT_finite eSuc_enat iT_card)

lemma iMODb_icard: "0 < m \<Longrightarrow> icard [r, mod m, c] = enat (Suc c)"
by (simp add: icard_finite iT_finite iMODb_card)

lemma iMODb_icard_if: "icard [r, mod m, c] = enat (if m = 0 then Suc 0 else Suc c)"
by (simp add: icard_finite iT_finite iMODb_card_if)

lemmas iT_icard =
  iFROM_icard
  iTILL_icard
  iIN_icard
  iMOD_icard_if
  iMODb_icard_if


subsection \<open>Functions \<open>inext\<close> and \<open>iprev\<close> with intervals\<close>

(*
lemma "inext 5 [\<dots>10] = 6"
apply (simp add: inext_def)
apply (simp add: iT_iff)
apply (simp add: iT_cut_greater)
apply (simp add: iT_not_empty)
apply (simp add: iT_Min)
done
lemma "inext 12 [\<dots>10] = 12"
apply (simp add: inext_def)
apply (simp add: iT_iff)
done

lemma "inext 5 [4\<dots>,5] = 6"
apply (simp add: inext_def)
apply (simp add: iT_iff)
apply (simp add: iT_cut_greater)
apply (simp add: iT_not_empty)
apply (simp add: iT_Min)
done
lemma "inext 14 [2, mod 4] = 18"
apply (simp add: inext_def)
apply safe
apply (simp add: iMOD_cut_greater iT_iff 
  iT_Min)
apply (simp add: iT_iff)
apply (simp add: iMOD_cut_greater iT_iff 
  iT_not_empty)
done

lemma "iprev 5 [\<dots>10] = 4"
apply (simp add: iprev_def)
apply (simp add: iT_iff)
apply (simp add: i_cut_defs)
apply safe
apply (simp add: iT_iff)
apply (rule le_antisym)
apply (rule iffD2[OF Max_le_iff])
apply fastforce+
done
*)

lemma 
  iFROM_inext: "t \<in> [n\<dots>] \<Longrightarrow> inext t [n\<dots>] = Suc t" and
  iTILL_inext: "t < n \<Longrightarrow> inext t [\<dots>n] = Suc t" and
  iIN_inext: "\<lbrakk> n \<le> t; t < n + d \<rbrakk> \<Longrightarrow> inext t [n\<dots>,d] = Suc t"
by (simp add: iT_defs inext_atLeast inext_atMost inext_atLeastAtMost)+

lemma 
  iFROM_iprev': "t \<in> [n\<dots>] \<Longrightarrow> iprev (Suc t) [n\<dots>] = t" and
  iFROM_iprev: "n < t  \<Longrightarrow> iprev t [n\<dots>] = t - Suc 0" and
  iTILL_iprev: "t \<in> [\<dots>n] \<Longrightarrow> iprev t [\<dots>n] = t - Suc 0" and
  iIN_iprev: "\<lbrakk> n < t; t \<le> n + d \<rbrakk> \<Longrightarrow> iprev t [n\<dots>,d] = t - Suc 0" and
  iIN_iprev': "\<lbrakk> n \<le> t; t < n + d \<rbrakk> \<Longrightarrow> iprev (Suc t) [n\<dots>,d] = t"
by (simp add: iT_defs iprev_atLeast iprev_atMost iprev_atLeastAtMost)+

lemma iMOD_inext: "t \<in> [r, mod m] \<Longrightarrow> inext t [r, mod m] = t + m"
by (clarsimp simp add: inext_def iMOD_cut_greater iT_iff iT_Min iT_not_empty mod_eq_imp_diff_mod_0)
lemma iMOD_iprev: "\<lbrakk> t \<in> [r, mod m]; r < t \<rbrakk> \<Longrightarrow> iprev t [r, mod m] = t - m"
apply (case_tac "m = 0", simp add: iMOD_iff)
apply (clarsimp simp add: iprev_def iMOD_cut_less iT_iff iT_Max iT_not_empty minus_mod_eq_mult_div [symmetric])
apply (simp del: add_Suc_right add: add_Suc_right[symmetric] mod_eq_imp_diff_mod_eq_divisor)
apply (simp add: less_mod_eq_imp_add_divisor_le)
done

lemma iMOD_iprev': "t \<in> [r, mod m] \<Longrightarrow> iprev (t + m) [r, mod m] = t"
apply (case_tac "m = 0")
 apply (simp add: iMOD_0 iIN_0 iprev_singleton)
apply (simp add: iMOD_iprev iT_iff)
done

lemma iMODb_inext: "
  \<lbrakk> t \<in> [r, mod m, c]; t < r + m * c \<rbrakk> \<Longrightarrow> 
  inext t [r, mod m, c] = t + m"
by (clarsimp simp add: inext_def iMODb_cut_greater iT_iff iT_Min iT_not_empty mod_eq_imp_diff_mod_0)

lemma iMODb_iprev: "
  \<lbrakk> t \<in> [r, mod m, c]; r < t \<rbrakk> \<Longrightarrow> 
  iprev t [r, mod m, c] = t - m"
apply (case_tac "m = 0", simp add: iMODb_iff)
apply (clarsimp simp add: iprev_def iMODb_cut_less iT_iff iT_Max iT_not_empty minus_mod_eq_mult_div [symmetric])
apply (simp del: add_Suc_right add: add_Suc_right[symmetric] mod_eq_imp_diff_mod_eq_divisor)
apply (simp add: less_mod_eq_imp_add_divisor_le)
done

lemma iMODb_iprev': "
  \<lbrakk> t \<in> [r, mod m, c]; t < r + m * c \<rbrakk> \<Longrightarrow> 
  iprev (t + m) [r, mod m, c] = t"
apply (case_tac "m = 0")
 apply (simp add: iMODb_mod_0 iIN_0 iprev_singleton)
apply (simp add: iMODb_iprev iT_iff less_mod_eq_imp_add_divisor_le)
done

lemmas iT_inext =
  iFROM_inext
  iTILL_inext
  iIN_inext
  iMOD_inext
  iMODb_inext
lemmas iT_iprev =
  iFROM_iprev'
  iFROM_iprev
  iTILL_iprev
  iIN_iprev
  iIN_iprev'
  iMOD_iprev
  iMOD_iprev'
  iMODb_iprev
  iMODb_iprev'

lemma iFROM_inext_if: "
  inext t [n\<dots>] = (if t \<in> [n\<dots>] then Suc t else t)"
by (simp add: iFROM_inext not_in_inext_fix)

lemma iTILL_inext_if: "
  inext t [\<dots>n] = (if t < n then Suc t else t)"
by (simp add: iTILL_inext iT_finite iT_Max inext_ge_Max)

lemma iIN_inext_if: "
  inext t [n\<dots>,d] = (if n \<le> t \<and> t < n + d then Suc t else t)"
by (fastforce simp: iIN_inext iT_iff not_in_inext_fix iT_finite iT_Max inext_ge_Max)

lemma iMOD_inext_if: "
  inext t [r, mod m] = (if t \<in> [r, mod m] then t + m else t)"
by (simp add: iMOD_inext not_in_inext_fix)

lemma iMODb_inext_if: "
  inext t [r, mod m, c] = 
  (if t \<in> [r, mod m, c] \<and> t < r + m * c then t + m else t)"
by (fastforce simp: iMODb_inext iT_iff not_in_inext_fix iT_finite iT_Max inext_ge_Max)

lemmas iT_inext_if =
  iFROM_inext_if
  iTILL_inext_if
  iIN_inext_if
  iMOD_inext_if
  iMODb_inext_if

lemma iFROM_iprev_if: "
  iprev t [n\<dots>] = (if n < t then t - Suc 0 else t)"
by (simp add: iFROM_iprev iT_Min iprev_le_iMin)
lemma iTILL_iprev_if: "
  iprev t [\<dots>n] = (if t \<in> [\<dots>n] then t - Suc 0 else t)"
by (simp add: iTILL_iprev not_in_iprev_fix)
lemma iIN_iprev_if: "
  iprev t [n\<dots>,d] = (if n < t \<and> t \<le> n + d  then t - Suc 0 else t)"
by (fastforce simp: iIN_iprev iT_iff not_in_iprev_fix iT_Min iprev_le_iMin)
lemma iMOD_iprev_if: "
  iprev t [r, mod m] = 
  (if t \<in> [r, mod m] \<and> r < t then t - m else t)"
by (fastforce simp add: iMOD_iprev iT_iff not_in_iprev_fix iT_Min iprev_le_iMin)
lemma iMODb_iprev_if: "
  iprev t [r, mod m, c] = 
  (if t \<in> [r, mod m, c] \<and> r < t then t - m else t)"
by (fastforce simp add: iMODb_iprev iT_iff not_in_iprev_fix iT_Min iprev_le_iMin)

lemmas iT_iprev_if =
  iFROM_iprev_if
  iTILL_iprev_if
  iIN_iprev_if
  iMOD_iprev_if
  iMODb_iprev_if

text \<open>
  The difference between an element and the next/previous element is constant
  if the element is different from Min/Max of the interval\<close>

lemma iFROM_inext_diff_const: "
  t \<in> [n\<dots>] \<Longrightarrow> inext t [n\<dots>] - t = Suc 0"
by (simp add: iFROM_inext)

lemma iFROM_iprev_diff_const: "
  n < t \<Longrightarrow> t - iprev t [n\<dots>] = Suc 0"
by (simp add: iFROM_iprev )

lemma iFROM_iprev_diff_const': "
  t \<in> [n\<dots>] \<Longrightarrow> Suc t - iprev (Suc t) [n\<dots>] = Suc 0"
by (simp add: iFROM_iprev')

lemma iTILL_inext_diff_const: "
  t < n \<Longrightarrow> inext t [\<dots>n] - t = Suc 0"
by (simp add: iTILL_inext)
lemma iTILL_iprev_diff_const: "
  \<lbrakk> t \<in> [\<dots>n]; 0 < t \<rbrakk> \<Longrightarrow> t - iprev t [\<dots>n] = Suc 0"
by (simp add: iTILL_iprev)

lemma iIN_inext_diff_const: "
  \<lbrakk> n \<le> t; t < n + d \<rbrakk> \<Longrightarrow> inext t [n\<dots>,d] - t = Suc 0"
by (simp add: iIN_inext)

lemma iIN_iprev_diff_const: "
  \<lbrakk> n < t; t \<le> n + d \<rbrakk> \<Longrightarrow> t - iprev t [n\<dots>,d] = Suc 0"
by (simp add: iIN_iprev)
lemma iIN_iprev_diff_const': "
  \<lbrakk> n \<le> t; t < n + d \<rbrakk> \<Longrightarrow> Suc t - iprev (Suc t) [n\<dots>,d] = Suc 0"
by (simp add: iIN_iprev)

lemma iMOD_inext_diff_const: "
  t \<in> [r, mod m] \<Longrightarrow> inext t [r, mod m] - t = m"
by (simp add: iMOD_inext)

lemma iMOD_iprev_diff_const': "
  t \<in> [r, mod m] \<Longrightarrow> (t + m) - iprev (t + m) [r, mod m] = m"
by (simp add: iMOD_iprev')

lemma iMOD_iprev_diff_const: "
  \<lbrakk> t \<in> [r, mod m]; r < t \<rbrakk> \<Longrightarrow> t - iprev t [r, mod m] = m"
apply (simp add: iMOD_iprev iT_iff)
apply (drule less_mod_eq_imp_add_divisor_le[where m=m], simp+)
done

lemma iMODb_inext_diff_const: "
  \<lbrakk> t \<in> [r, mod m, c]; t < r + m * c \<rbrakk> \<Longrightarrow> inext t [r, mod m, c] - t = m"
by (simp add: iMODb_inext)

lemma iMODb_iprev_diff_const': "
  \<lbrakk> t \<in> [r, mod m, c]; t < r + m * c \<rbrakk> \<Longrightarrow> (t + m) - iprev (t + m) [r, mod m, c] = m"
by (simp add: iMODb_iprev')

lemma iMODb_iprev_diff_const: "
  \<lbrakk> t \<in> [r, mod m, c]; r < t \<rbrakk> \<Longrightarrow> t - iprev t [r, mod m, c] = m"
apply (simp add: iMODb_iprev iT_iff)
apply (drule less_mod_eq_imp_add_divisor_le[where m=m], simp+)
done

lemmas iT_inext_diff_const =
  iFROM_inext_diff_const
  iTILL_inext_diff_const
  iIN_inext_diff_const
  iMOD_inext_diff_const
  iMODb_inext_diff_const
lemmas iT_iprev_diff_const =
  iFROM_iprev_diff_const
  iFROM_iprev_diff_const'
  iTILL_iprev_diff_const
  iIN_iprev_diff_const
  iIN_iprev_diff_const'
  iMOD_iprev_diff_const'
  iMOD_iprev_diff_const
  iMODb_iprev_diff_const'
  iMODb_iprev_diff_const


subsubsection \<open>Mirroring of intervals\<close>

lemma 
  iIN_mirror_elem: "mirror_elem x [n\<dots>,d] = n + n + d - x" and
  iTILL_mirror_elem: "mirror_elem x [\<dots>n] = n - x" and
  iMODb_mirror_elem: "mirror_elem x [r, mod m, c] = r + r + m * c - x"
by (simp add: mirror_elem_def nat_mirror_def iT_Min iT_Max)+

lemma iMODb_imirror_bounds: "
  r' + m' * c' \<le> l + r \<Longrightarrow> 
  imirror_bounds [r', mod m', c'] l r = [l + r - r' - m' * c', mod m', c']"
apply (clarsimp simp: set_eq_iff Bex_def imirror_bounds_iff iT_iff)
apply (frule diff_le_mono[of _ _ r'], simp)
apply (simp add: mod_diff_right_eq)
apply (rule iffI)
 apply (clarsimp, rename_tac x')
 apply (rule_tac a=x' in ssubst[OF mod_diff_right_eq, rule_format], simp+)
 apply (simp add: diff_le_mono2)
apply clarsimp
apply (rule_tac x="l+r-x" in exI)
apply (simp add: le_diff_swap)
apply (simp add: le_diff_conv2)
apply (subst mod_sub_eq_mod_swap, simp+)
apply (simp add: mod_diff_right_eq)
done

lemma iIN_imirror_bounds: "
  n + d \<le> l + r \<Longrightarrow> imirror_bounds [n\<dots>,d] l r = [l + r - n - d\<dots>,d]"
apply (insert iMODb_imirror_bounds[of n "Suc 0" d l r])
apply (simp add: iMODb_mod_1)
done

lemma iTILL_imirror_bounds: "
  n \<le> l + r \<Longrightarrow> imirror_bounds [\<dots>n] l r = [l + r - n\<dots>,n]"
apply (insert iIN_imirror_bounds[of 0 n l r])
apply (simp add: iIN_0_iTILL_conv)
done

lemmas iT_imirror_bounds =
  iTILL_imirror_bounds
  iIN_imirror_bounds
  iMODb_imirror_bounds


lemma iMODb_imirror_ident: "imirror [r, mod m, c] = [r, mod m, c]"
by (simp add: imirror_eq_imirror_bounds iMODb_Min iMODb_Max iMODb_imirror_bounds)
lemma iIN_imirror_ident: "imirror [n\<dots>,d] = [n\<dots>,d]"
by (simp add: iMODb_mod_1[symmetric] iMODb_imirror_ident)
lemma iTILL_imirror_ident: "imirror [\<dots>n] = [\<dots>n]"
by (simp add: iIN_0_iTILL_conv[symmetric] iIN_imirror_ident)

lemmas iT_imirror_ident =
  iTILL_imirror_ident
  iIN_imirror_ident
  iMODb_imirror_ident


subsubsection \<open>Functions @{term inext_nth} and @{term iprev_nth} on intervals\<close>

lemma iFROM_inext_nth : "[n\<dots>] \<rightarrow> a = n + a"
by (simp add: iT_defs inext_nth_atLeast)

lemma iIN_inext_nth : "a \<le> d \<Longrightarrow> [n\<dots>,d] \<rightarrow> a = n + a"
by (simp add: iT_defs inext_nth_atLeastAtMost)

lemma iIN_iprev_nth: "a \<le> d \<Longrightarrow> [n\<dots>,d] \<leftarrow> a = n + d - a"
by (simp add: iT_defs iprev_nth_atLeastAtMost)

lemma iIN_inext_nth_if : "
  [n\<dots>,d] \<rightarrow> a = (if a \<le> d then n + a else n + d)"
by (simp add: iIN_inext_nth inext_nth_card_Max iT_finite iT_not_empty iT_Max iT_card)

lemma iIN_iprev_nth_if: "
  [n\<dots>,d] \<leftarrow> a = (if a \<le> d then n + d - a else n)"
by (simp add: iIN_iprev_nth iprev_nth_card_iMin iT_finite iT_not_empty iT_Min iT_card)

lemma iTILL_inext_nth : "a \<le> n \<Longrightarrow> [\<dots>n] \<rightarrow> a = a"
by (simp add: iTILL_def inext_nth_atMost)

lemma iTILL_inext_nth_if : "
  [\<dots>n] \<rightarrow> a = (if a \<le> n then a else n)"
by (insert iIN_inext_nth_if[of 0 n a], simp add: iIN_0_iTILL_conv)

lemma iTILL_iprev_nth: "a \<le> n \<Longrightarrow> [\<dots>n] \<leftarrow> a = n - a"
by (simp add: iTILL_def iprev_nth_atMost)

lemma iTILL_iprev_nth_if: "
  [\<dots>n] \<leftarrow> a= (if a \<le> n then n - a else 0)"
by (insert iIN_iprev_nth_if[of 0 n a], simp add: iIN_0_iTILL_conv)


lemma iMOD_inext_nth: "[r, mod m] \<rightarrow> a = r + m * a"
apply (induct a)
 apply (simp add: iT_Min)
apply (simp add: iMOD_inext_if iT_iff)
done

lemma iMODb_inext_nth: "a \<le> c \<Longrightarrow> [r, mod m, c] \<rightarrow> a = r + m * a"
apply (case_tac "m = 0")
 apply (simp add: iMODb_mod_0 iIN_0 inext_nth_singleton)
apply (induct a)
 apply (simp add: iMODb_Min)
apply (simp add: iMODb_inext_if iT_iff)
done

lemma iMODb_inext_nth_if: "
  [r, mod m, c] \<rightarrow> a = (if a \<le> c then r + m * a else r + m * c)"
by (simp add: iMODb_inext_nth inext_nth_card_Max iT_finite iT_not_empty iT_Max iT_card)

lemma iMODb_iprev_nth: "
  a \<le> c \<Longrightarrow> [r, mod m, c] \<leftarrow> a = r + m * (c - a)"
apply (case_tac "m = 0")
 apply (simp add: iMODb_mod_0 iIN_0 iprev_nth_singleton)
apply (induct a)
 apply (simp add: iMODb_Max)
apply (simp add: iMODb_iprev_if iT_iff)
apply (frule mult_left_mono[of _ _ m], simp)
apply (simp add: diff_mult_distrib2)
done

lemma iMODb_iprev_nth_if: "
  [r, mod m, c] \<leftarrow> a = (if a \<le> c then r + m * (c - a) else r)"
by (simp add: iMODb_iprev_nth iprev_nth_card_iMin iT_finite iT_not_empty iT_Min iT_card)


lemma iIN_iFROM_inext_nth: "
  a \<le> d \<Longrightarrow> [n\<dots>,d] \<rightarrow> a = [n\<dots>] \<rightarrow> a"
by (simp add: iIN_inext_nth iFROM_inext_nth)

lemma iIN_iFROM_inext: "
  a < n + d \<Longrightarrow> inext a [n\<dots>,d] = inext a [n\<dots>]"
by (simp add: iT_inext_if iT_iff)

lemma iMOD_iMODb_inext_nth: "
  a \<le> c \<Longrightarrow> [r, mod m, c] \<rightarrow> a = [r, mod m] \<rightarrow> a"
by (simp add: iMOD_inext_nth iMODb_inext_nth)

lemma iMOD_iMODb_inext: "
  a < r + m * c \<Longrightarrow> inext a [r, mod m, c] = inext a [r, mod m]"
by (simp add: iT_inext_if iT_iff)


lemma iMOD_inext_nth_Suc_diff: "
  ([r, mod m] \<rightarrow> (Suc n)) - ([r, mod m] \<rightarrow> n) = m"
by (simp add: iMOD_inext_nth del: inext_nth.simps)

lemma iMOD_inext_nth_diff: "
  ([r, mod m] \<rightarrow> a) - ([r, mod m] \<rightarrow> b) = (a - b) * m"
by (simp add: iMOD_inext_nth diff_mult_distrib mult.commute[of m])

lemma iMODb_inext_nth_diff: "\<lbrakk> a \<le> c; b \<le> c \<rbrakk> \<Longrightarrow>
  ([r, mod m, c] \<rightarrow> a) - ([r, mod m, c] \<rightarrow> b) = (a - b) * m"
by (simp add: iMODb_inext_nth diff_mult_distrib  mult.commute[of m])



subsection \<open>Induction with intervals\<close>

lemma iFROM_induct: "
  \<lbrakk> P n; \<And>k. \<lbrakk> k \<in> [n\<dots>]; P k \<rbrakk> \<Longrightarrow> P (Suc k); a \<in> [n\<dots>] \<rbrakk> \<Longrightarrow> P a"
apply (rule inext_induct[of _ "[n\<dots>]"])
apply (simp add: iT_Min iT_inext_if)+
done

lemma iIN_induct: "
  \<lbrakk> P n; \<And>k. \<lbrakk> k \<in> [n\<dots>,d]; k \<noteq> n + d; P k \<rbrakk> \<Longrightarrow> P (Suc k); a \<in> [n\<dots>,d] \<rbrakk> \<Longrightarrow> P a"
apply (rule inext_induct[of _ "[n\<dots>,d]"])
apply (simp add: iT_Min iT_inext_if)+
done

lemma iTILL_induct: "
  \<lbrakk> P 0; \<And>k. \<lbrakk> k \<in> [\<dots>n]; k \<noteq> n; P k \<rbrakk> \<Longrightarrow> P (Suc k); a \<in> [\<dots>n] \<rbrakk> \<Longrightarrow> P a"
apply (rule inext_induct[of _ "[\<dots>n]"])
apply (simp add: iT_Min iT_inext_if)+
done

lemma iMOD_induct: "
  \<lbrakk> P r; \<And>k. \<lbrakk> k \<in> [r, mod m]; P k \<rbrakk> \<Longrightarrow> P (k + m); a \<in> [r, mod m] \<rbrakk> \<Longrightarrow> P a"
apply (rule inext_induct[of _ "[r, mod m]"])
apply (simp add: iT_Min iT_inext_if)+
done

lemma iMODb_induct: "
  \<lbrakk> P r; \<And>k. \<lbrakk> k \<in> [r, mod m, c]; k \<noteq> r + m * c; P k \<rbrakk> \<Longrightarrow> P (k + m); a \<in> [r, mod m, c] \<rbrakk> \<Longrightarrow> P a"
apply (rule inext_induct[of _ "[r, mod m, c]"])
apply (simp add: iT_Min iT_inext_if)+
done

lemma iIN_rev_induct: "
  \<lbrakk> P (n + d); \<And>k. \<lbrakk> k \<in> [n\<dots>,d]; k \<noteq> n; P k \<rbrakk> \<Longrightarrow> P (k - Suc 0); a \<in> [n\<dots>,d] \<rbrakk> \<Longrightarrow> P a"
apply (rule iprev_induct[of _ "[n\<dots>,d]"])
apply (simp add: iT_Max iT_finite iT_iprev_if)+
done

lemma iTILL_rev_induct: "
  \<lbrakk> P n; \<And>k. \<lbrakk> k \<in> [\<dots>n]; 0 < k; P k \<rbrakk> \<Longrightarrow> P (k - Suc 0); a \<in> [\<dots>n] \<rbrakk> \<Longrightarrow> P a"
apply (rule iprev_induct[of _ "[\<dots>n]"])
apply (fastforce simp: iT_Max iT_finite iT_iprev_if)+
done

lemma iMODb_rev_induct: "
  \<lbrakk> P (r + m * c); \<And>k. \<lbrakk> k \<in> [r, mod m, c]; k \<noteq> r; P k \<rbrakk> \<Longrightarrow> P (k - m); a \<in> [r, mod m, c] \<rbrakk> \<Longrightarrow> P a"
apply (rule iprev_induct[of _ "[r, mod m, c]"])
apply (simp add: iT_Max iT_finite iT_iprev_if)+
done

end
