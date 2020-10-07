(*  Title:      ListSlice.thy
    Date:       Oct 2006
    Author:     David Trachtenherz
*)

section \<open>Additional definitions and results for lists\<close>

theory ListSlice
imports "List-Infinite.ListInf"
begin

subsection \<open>Slicing lists into lists of lists\<close>

definition ilist_slice  :: "'a ilist \<Rightarrow> nat \<Rightarrow> 'a list ilist"
  where "ilist_slice f k \<equiv> \<lambda>x. map f [x * k..<Suc x * k]"

primrec list_slice_aux :: "'a list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a list list"
where
  "list_slice_aux xs k 0 = []"
| "list_slice_aux xs k (Suc n) = take k xs # list_slice_aux (xs \<up> k) k n"

definition list_slice :: "'a list \<Rightarrow> nat \<Rightarrow> 'a list list"
  where "list_slice xs k \<equiv> list_slice_aux xs k (length xs div k)"

definition list_slice2 :: "'a list \<Rightarrow> nat \<Rightarrow> 'a list list"
  where "list_slice2 xs k \<equiv>
    list_slice xs k @ (if length xs mod k = 0 then [] else [xs \<up> (length xs div k * k)])"

text \<open>
  No function \<open>list_unslice\<close> for finite lists is needed 
  because the corresponding functionality is already provided by \<open>concat\<close>. 
  Therefore, only a \<open>ilist_unslice\<close> function for infinite lists is defined.\<close>

definition ilist_unslice  :: "'a list ilist \<Rightarrow> 'a ilist"
  where "ilist_unslice f \<equiv> \<lambda>n. f (n div length (f 0)) ! (n mod length (f 0))"


lemma list_slice_aux_length: "\<And>xs. length (list_slice_aux xs k n) = n"
by (induct n, simp+)

lemma list_slice_aux_nth: "
 \<And>m xs. m < n \<Longrightarrow> (list_slice_aux xs k n) ! m = (xs \<up> (m * k) \<down> k)"
apply (induct n)
 apply simp
apply (simp add: nth_Cons' diff_mult_distrib)
done

lemma list_slice_length: "length (list_slice xs k) = length xs div k"
by (simp add: list_slice_def list_slice_aux_length)

lemma list_slice_0: "list_slice xs 0 = []"
by (simp add: list_slice_def)

lemma list_slice_1: "list_slice xs (Suc 0) = map (\<lambda>x. [x]) xs"
by (fastforce simp: list_eq_iff list_slice_def list_slice_aux_nth list_slice_aux_length)

lemma list_slice_less: "length xs < k \<Longrightarrow> list_slice xs k = []"
by (simp add: list_slice_def)

lemma list_slice_Nil: "list_slice [] k = []"
by (simp add: list_slice_def)

lemma list_slice_nth: "
  m < length xs div k \<Longrightarrow> list_slice xs k ! m = xs \<up> (m * k) \<down> k"
by (simp add: list_slice_def list_slice_aux_nth)

lemma list_slice_nth_length: "
  m < length xs div k \<Longrightarrow> length ((list_slice xs k) ! m) = k"
apply (case_tac "length xs < k")
 apply simp
apply (simp add: list_slice_nth)
thm less_div_imp_mult_add_divisor_le
apply (drule less_div_imp_mult_add_divisor_le)
apply simp
done

lemma list_slice_nth_eq_sublist_list: "
  m < length xs div k \<Longrightarrow> list_slice xs k ! m = sublist_list xs [m * k..<m * k + k]"
apply (simp add: list_slice_nth)
apply (rule take_drop_eq_sublist_list)
apply (rule less_div_imp_mult_add_divisor_le, assumption+)
done

lemma list_slice_nth_nth: "
  \<lbrakk> m < length xs div k; n < k \<rbrakk> \<Longrightarrow> 
  (list_slice xs k) ! m ! n = xs ! (m * k + n)"
apply (frule list_slice_nth_length[of m xs k])
apply (simp add: list_slice_nth)
done

lemma list_slice_nth_nth_rev: "
  n < length xs div k * k \<Longrightarrow>
  (list_slice xs k) ! (n div k) ! (n mod k) = xs ! n"
apply (case_tac "k = 0", simp)
apply (simp add: list_slice_nth_nth div_less_conv)
done

lemma list_slice_eq_list_slice_take: "
  list_slice (xs \<down> (length xs div k * k)) k = list_slice xs k"
apply (case_tac "k = 0")
 apply (simp add: list_slice_0)
apply (simp add: list_eq_iff list_slice_length)
apply (simp add: div_mult_le min_eqR list_slice_nth)
apply (clarify, rename_tac i)
apply (subgoal_tac "k \<le> length xs div k * k - i * k")
 prefer 2
 apply (drule_tac m=i in Suc_leI)
 apply (drule mult_le_mono1[of _ _ k])
 apply simp
apply (subgoal_tac "length xs div k * k - i * k \<le> length xs - i * k")
 prefer 2
 apply (simp add: div_mult_cancel)
apply (simp add: min_eqR)
by (simp add: less_diff_conv)

lemma list_slice_append_mult: "
  \<And>xs. length xs = m * k \<Longrightarrow>
  list_slice (xs @ ys) k = list_slice xs k @ list_slice ys k"
apply (case_tac "k = 0")
 apply (simp add: list_slice_0)
apply (induct m)
 apply (simp add: list_slice_Nil)
apply (simp add: list_slice_def)
apply (simp add: list_slice_def add.commute[of _ "length ys"] add.assoc[symmetric])
done

lemma list_slice_append_mod: "
  length xs mod k = 0 \<Longrightarrow>
  list_slice (xs @ ys) k = list_slice xs k @ list_slice ys k"
  by (auto intro: list_slice_append_mult elim!: dvdE)

lemma list_slice_div_eq_1[rule_format]: "
  length xs div k = Suc 0 \<Longrightarrow> list_slice xs k = [take k xs]"
by (simp add: list_slice_def)

lemma list_slice_div_eq_Suc[rule_format]: "
  length xs div k = Suc n \<Longrightarrow>
  list_slice xs k = list_slice (xs \<down> (n * k)) k @ [xs \<up> (n * k) \<down> k]"
apply (case_tac "k = 0", simp)
apply (subgoal_tac "n * k < length xs")
 prefer 2
 apply (case_tac "length xs = 0", simp)
 apply (drule_tac arg_cong[where f="\<lambda>x. x - Suc 0"], drule sym)
 apply (simp add: diff_mult_distrib div_mult_cancel)
apply (insert list_slice_append_mult[of "take (n * k) xs" n k "drop (n * k) xs"])
apply (simp add: min_eqR)
apply (rule list_slice_div_eq_1)
apply (simp add: div_diff_mult_self1)
done

lemma list_slice2_mod_0: "
  length xs mod k = 0 \<Longrightarrow> list_slice2 xs k = list_slice xs k"
by (simp add: list_slice2_def)

lemma list_slice2_mod_gr0: "
  0 < length xs mod k \<Longrightarrow> list_slice2 xs k = list_slice xs k @ [xs \<up> (length xs div k * k)]"
by (simp add: list_slice2_def)

lemma list_slice2_length: "
  length (list_slice2 xs k) = (
  if length xs mod k = 0 then length xs div k else Suc (length xs div k))"
by (simp add: list_slice2_def list_slice_length)

lemma list_slice2_0: "
  list_slice2 xs 0 = (if (length xs = 0) then [] else [xs])"
by (simp add: list_slice2_def list_slice_0)

lemma list_slice2_1: "list_slice2 xs (Suc 0) = map (\<lambda>x. [x]) xs"
by (simp add: list_slice2_def list_slice_1)

lemma list_slice2_le: "
  length xs \<le> k \<Longrightarrow> list_slice2 xs k = (if length xs = 0 then [] else [xs])"
apply (case_tac "k = 0")
 apply (simp add: list_slice2_0)
apply (drule order_le_less[THEN iffD1], erule disjE)
 apply (simp add: list_slice2_def list_slice_def)
apply (simp add: list_slice2_def list_slice_div_eq_1)
done

lemma list_slice2_Nil: "list_slice2 [] k = []"
by (simp add: list_slice2_def list_slice_Nil)

lemma list_slice2_list_slice_nth: "
  m < length xs div k \<Longrightarrow> list_slice2 xs k ! m = list_slice xs k ! m"
by (simp add: list_slice2_def list_slice_length nth_append)

lemma list_slice2_last: "
  \<lbrakk> length xs mod k > 0; m = length xs div k \<rbrakk> \<Longrightarrow>
  list_slice2 xs k ! m = xs \<up> (length xs div k * k)"
by (simp add: list_slice2_def nth_append list_slice_length)

lemma list_slice2_nth: "
  \<lbrakk> m < length xs div k \<rbrakk> \<Longrightarrow> 
  list_slice2 xs k ! m = xs \<up> (m * k) \<down> k"
by (simp add: list_slice2_def list_slice_length nth_append list_slice_nth)

lemma list_slice2_nth_length_eq1: "
  m < length xs div k \<Longrightarrow> length (list_slice2 xs k ! m) = k"
by (simp add: list_slice2_def nth_append list_slice_length list_slice_nth_length)

lemma list_slice2_nth_length_eq2: "
  \<lbrakk> length xs mod k > 0; m = length xs div k \<rbrakk> \<Longrightarrow> 
  length (list_slice2 xs k ! m) = length xs mod k"
by (simp add: list_slice2_def list_slice_length nth_append minus_div_mult_eq_mod [symmetric])

lemma list_slice2_nth_nth_eq1: "
  \<lbrakk> m < length xs div k; n < k \<rbrakk> \<Longrightarrow> 
  (list_slice2 xs k) ! m ! n = xs ! (m * k + n)"
by (simp add: list_slice2_list_slice_nth list_slice_nth_nth)

lemma list_slice2_nth_nth_eq2: "
  \<lbrakk> m = length xs div k; n < length xs mod k \<rbrakk> \<Longrightarrow> 
  (list_slice2 xs k) ! m ! n = xs ! (m * k + n)"
by (simp add: mult.commute[of _ k] minus_mod_eq_mult_div [symmetric] list_slice2_last)

lemma list_slice2_nth_nth_rev: "
  n < length xs \<Longrightarrow> (list_slice2 xs k) ! (n div k) ! (n mod k) = xs ! n"
apply (case_tac "k = 0")
 apply (clarsimp simp: list_slice2_0)
apply (case_tac "n div k < length xs div k")
 apply (simp add: list_slice2_nth_nth_eq1)
apply (frule div_le_mono[OF less_imp_le, of _ _ k])
apply simp
apply (drule sym)
apply (subgoal_tac "n mod k < length xs mod k")
 prefer 2
 apply (rule ccontr)
 apply (simp add: linorder_not_less)
 apply (drule less_mod_ge_imp_div_less[of n "length xs" k], simp+)
apply (simp add: list_slice2_nth_nth_eq2)
done

lemma list_slice2_append_mult: "
  length xs = m * k \<Longrightarrow>
  list_slice2 (xs @ ys) k = list_slice2 xs k @ list_slice2 ys k"
apply (case_tac "k = 0")
 apply (simp add: list_slice2_0)
apply (clarsimp simp: list_slice2_def list_slice_append_mult)
apply (simp add: add.commute[of "m * k"] add_mult_distrib)
done

lemma list_slice2_append_mod: "
  length xs mod k = 0 \<Longrightarrow>
  list_slice2 (xs @ ys) k = list_slice2 xs k @ list_slice2 ys k"
  by (auto intro: list_slice2_append_mult elim!: dvdE)

lemma ilist_slice_nth: "
  (ilist_slice f k) m = map f [m * k..<Suc m * k]"
by (simp add: ilist_slice_def)

lemma ilist_slice_nth_length: "length ((ilist_slice f k) m) = k"
by (simp add: ilist_slice_def)

lemma ilist_slice_nth_nth: "
  n < k \<Longrightarrow> (ilist_slice f k) m ! n = f (m * k + n)"
by (simp add: ilist_slice_def)

lemma ilist_slice_nth_nth_rev: "
  0 < k \<Longrightarrow> (ilist_slice f k) (n div k) ! (n mod k) = f n"
by (simp add: ilist_slice_nth_nth)

lemma list_slice_concat: "
  concat (list_slice xs k) = xs \<down> (length xs div k * k)"
  (is "?P xs k")
apply (case_tac "k = 0")
 apply (simp add: list_slice_0)
apply simp
apply (subgoal_tac "\<And>m. \<forall>xs. length xs div k = m \<longrightarrow> ?P xs k", simp)
apply (induct_tac m)
 apply (intro allI impI)
 apply (simp add: in_set_conv_nth div_eq_0_conv' list_slice_less)
apply clarify
apply (simp add: add.commute[of k])
apply (subgoal_tac "n * k + k \<le> length xs")
 prefer 2
 apply (simp add: le_less_div_conv[symmetric])
apply (simp add: list_slice_div_eq_Suc)
apply (drule_tac x="xs \<down> (n * k)" in spec)
apply (simp add: min_eqR)
apply (simp add: take_add)
done

lemma list_slice_unslice_mult: "
  length xs = m * k \<Longrightarrow> concat (list_slice xs k) = xs"
apply (case_tac "k = 0")
 apply (simp add: list_slice_Nil)
apply (simp add: list_slice_concat)
done

lemma ilist_slice_unslice: "0 < k \<Longrightarrow> ilist_unslice (ilist_slice f k) = f"
by (simp add: ilist_unslice_def ilist_slice_nth_length ilist_slice_nth_nth)

lemma i_take_ilist_slice_eq_list_slice: "
  0 < k \<Longrightarrow> ilist_slice f k \<Down> n = list_slice (f \<Down> (n * k)) k"
apply (simp add: list_eq_iff list_slice_length ilist_slice_nth list_slice_nth)
apply (clarify, rename_tac i)
apply (subgoal_tac "k \<le> n * k - i * k")
 prefer 2
 apply (drule_tac m=i in Suc_leI)
 apply (drule mult_le_mono1[of _ _ k])
 apply simp
apply simp
done

lemma list_slice_i_take_eq_i_take_ilist_slice: "
  list_slice (f \<Down> n) k = ilist_slice f k \<Down> (n div k)"
apply (case_tac "k = 0")
 apply (simp add: list_slice_0)
apply (simp add: i_take_ilist_slice_eq_list_slice)
apply (subst list_slice_eq_list_slice_take[of "f \<Down> n", symmetric])
apply (simp add: div_mult_le min_eqR)
done


lemma ilist_slice_i_append_mod: "
  length xs mod k = 0 \<Longrightarrow> 
  ilist_slice (xs \<frown> f) k = list_slice xs k \<frown> ilist_slice f k"
apply (simp add: ilist_eq_iff ilist_slice_nth i_append_nth list_slice_length)
apply (clarsimp simp: mult.commute[of k] elim!: dvdE, rename_tac n i)
apply (intro conjI impI)
 apply (simp add: list_slice_nth)
 apply (subgoal_tac "k \<le> n * k - i * k")
  prefer 2
  apply (drule_tac m=i in Suc_leI)
  apply (drule mult_le_mono1[of _ _ k])
  apply simp
 apply (fastforce simp: list_eq_iff i_append_nth min_eqR)
apply (simp add: ilist_eq_iff list_eq_iff i_append_nth linorder_not_less)
apply (clarify, rename_tac j)
apply (subgoal_tac "n * k \<le> i * k + j")
 prefer 2
 apply (simp add: trans_le_add1) 
apply (simp add: diff_mult_distrib)
done

corollary ilist_slice_append_mult: "
  length xs = m * k \<Longrightarrow> 
  ilist_slice (xs \<frown> f) k = list_slice xs k \<frown> ilist_slice f k"
by (simp add: ilist_slice_i_append_mod)

end
