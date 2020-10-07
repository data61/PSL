(*  Title:      IL_AF_Stream.thy
    Date:       Jan 2007
    Author:     David Trachtenherz
*)

section \<open>\textsc{AutoFocus} message streams and temporal logic on intervals\<close>

theory IL_AF_Stream
imports Main "Nat-Interval-Logic.IL_TemporalOperators" AF_Stream
begin


subsection \<open>Stream views -- joining streams and intervals\<close>

subsubsection \<open>Basic definitions\<close>

primrec f_join_aux :: "'a list \<Rightarrow> nat \<Rightarrow> iT \<Rightarrow> 'a list"
where
  "f_join_aux [] n I = []"
| "f_join_aux (x # xs) n I =
    (if n \<in> I then [x] else []) @ f_join_aux xs (Suc n) I"

text \<open>
  The functions \<open>f_join\<close> and \<open>i_join\<close>
  deliver views of finite and infinite streams through intervals
  (more exactly: arbitrary natural sets).
  A stream view contains only the elements of the original stream
  at positions, which are contained in the interval.
  For instance, \<open>f_join [0,10,20,30,40] {1,4} = [10,40]\<close>\<close>

definition f_join :: "'a list \<Rightarrow> iT \<Rightarrow> 'a list"      (infixl "\<Join>\<^sub>f" 100)
  where "xs \<Join>\<^sub>f I \<equiv> f_join_aux xs 0 I"

definition i_join :: "'a ilist \<Rightarrow> iT \<Rightarrow> 'a ilist"    (infixl "\<Join>\<^sub>i" 100)
  where "f \<Join>\<^sub>i I \<equiv> \<lambda>n. (f (I \<rightarrow> n))"

notation
  f_join  (infixl "\<Join>\<^sub>" 100) and
  i_join  (infixl "\<Join>\<^sub>" 100)

text \<open>
  The function \<open>i_f_join\<close> can be used for the case,
  when an infinite stream is joined with a finite interval.
  The function \<open>i_join\<close> would then deliver
  an infinite stream, whose elements after position \<open>card I\<close>
  are equal to initial stream's element at position \<open>Max I\<close>.
  The function \<open>i_f_join\<close> in contrast
  cuts the resulting stream at this position
  and returns a finite stream.\<close>

definition i_f_join :: "'a ilist \<Rightarrow> iT \<Rightarrow> 'a list"    (infixl "\<Join>\<^bsub>i-f\<^esub>" 100)
  where "f \<Join>\<^bsub>i-f\<^esub> I \<equiv> f \<Down> Suc (Max I) \<Join>\<^sub>f I"
notation
  i_f_join  (infixl "\<Join>\<^sub>" 100)

text \<open>
  The function \<open>i_f_join\<close> should be used
  only for finite sets in order to deliver well-defined results.
  The function \<open>i_join\<close> should be used for infinite sets,
  because joining an infinite stream \<open>s\<close> and a finite set \<open>I\<close>
  using \<open>i_join\<close> would deliver an infinite stream,
  ending with an infinite sequence of elements equal to
  \<open>s (Max I)\<close>.\<close>


subsubsection \<open>Basic results\<close>

lemma f_join_aux_length: "
  \<And>n. length (f_join_aux xs n I) = card (I \<inter> {n..<n + length xs})"
apply (induct xs, simp)
apply (simp add: atLeastLessThan_def)
apply (rule_tac t="{n..}" and s="insert n {Suc n..}" in subst, fastforce)
apply simp
done

lemma f_join_aux_nth[rule_format]: "
  \<forall>n i. i < card (I \<inter> {n..<n + length xs}) \<longrightarrow>
  (f_join_aux xs n I) ! i = xs ! (((I \<inter> {n..<n + length xs}) \<rightarrow> i) - n)"
apply (induct xs, simp)
apply (clarsimp split del: if_split)
apply (subgoal_tac "{n..<Suc (n + length xs)} = insert n {Suc n..<Suc (n + length xs)}")
 prefer 2
 apply fastforce
apply (frule card_gr0_imp_not_empty[OF gr_implies_gr0])
apply (case_tac "n \<in> I")
 prefer 2
 apply (simp add: nth_Cons')
 apply (subgoal_tac "Suc n \<le> (I \<inter> {Suc n..<Suc (n + length xs)}) \<rightarrow> i", simp)
 apply (rule order_trans[OF _ iMin_le[OF inext_nth_closed]])
  apply (rule order_trans[OF _ iMin_Int_ge2])
   apply (subgoal_tac "n < n + length xs")
    prefer 2
    apply (rule ccontr, simp)
   apply (simp add: iMin_atLeastLessThan)
  apply assumption+
apply simp
apply (case_tac "I \<inter> {Suc n..<Suc (n + length xs)} = {}", simp)
apply (case_tac i)
 apply (simp add: iMin_insert)
apply (subgoal_tac "Suc n \<le> iMin {Suc n..<Suc (n + length xs)}")
 prefer 2
 apply (subgoal_tac "n < n + length xs")
  prefer 2
  apply (rule ccontr, simp)
 apply (simp add: iMin_atLeastLessThan)
apply (rename_tac i1)
apply (simp del: inext_nth.simps)
apply (subst inext_nth_insert_Suc)
   apply simp
  apply (rule Suc_le_lessD)
  apply (rule order_trans[OF _ iMin_Int_ge2])
  apply assumption+
apply (simp add: nth_Cons')
apply (subgoal_tac "Suc n \<le> (I \<inter> {Suc n..<Suc (n + length xs)}) \<rightarrow> i1", simp)
apply (rule order_trans[OF _ iMin_le[OF inext_nth_closed]])
 apply (rule order_trans[OF _ iMin_Int_ge2])
 apply assumption+
done



text \<open>Joining finite streams and intervals\<close>

(*<*)
(*
lemma "[(0::nat),10,20,30,40] \<Join>\<^sub>f {1,4} = [10,40]"
by (simp add: f_join_def)
*)
(*>*)

lemma f_join_length: "length (xs \<Join>\<^sub>f I) = card (I \<down>< length xs)"
by (simp add: f_join_def f_join_aux_length atLeast0LessThan cut_less_Int_conv)

lemma f_join_nth: "n < length (xs \<Join>\<^sub>f I) \<Longrightarrow> (xs \<Join>\<^sub>f I) ! n = xs ! (I \<rightarrow> n)"
apply (simp add: f_join_length)
apply (unfold f_join_def)
apply (drule back_subst[OF _ cut_less_Int_conv])
apply (simp add: f_join_aux_nth atLeast0LessThan cut_less_Int_conv[symmetric] inext_nth_cut_less_eq)
done

lemma f_join_nth2: "n < card (I \<down>< length xs) \<Longrightarrow> (xs \<Join>\<^sub>f I) ! n = xs ! (I \<rightarrow> n)"
by (simp add: f_join_nth f_join_length)

lemma f_join_empty: "xs \<Join>\<^sub>f {} = []"
by (simp add: length_0_conv[symmetric] f_join_length cut_less_empty del: length_0_conv)

lemma f_join_Nil: "[] \<Join>\<^sub>f I = []"
by (simp add: length_0_conv[symmetric] f_join_length cut_less_0_empty del: length_0_conv)

lemma f_join_Nil_conv: "(xs \<Join>\<^sub>f I = []) = (I \<down>< length xs = {})"
by (simp add: length_0_conv[symmetric] f_join_length card_0_eq[OF nat_cut_less_finite] del: length_0_conv)

lemma f_join_Nil_conv': "(xs \<Join>\<^sub>f I = []) = (\<forall>i<length xs. i \<notin> I)"
by (fastforce simp: f_join_Nil_conv)

lemma f_join_all_conv: "(xs \<Join>\<^sub>f I = xs) = ({..<length xs} \<subseteq> I)"
apply (case_tac "length xs = 0", simp add: f_join_Nil)
apply (rule iffI)
 apply (rule subsetI, rename_tac t)
 apply (clarsimp simp: list_eq_iff[of _ xs] f_join_length)
 apply (rule ccontr)
 apply (subgoal_tac "I \<down>< length xs \<subset> {..<length xs}")
  prefer 2
  apply blast
 apply (drule psubset_card_mono[OF finite_lessThan])
 apply simp
apply (subgoal_tac "length (xs \<Join>\<^sub>f I) = length xs")
 prefer 2
 apply (simp add: f_join_length cut_less_Int_conv Int_absorb1)
apply (clarsimp simp: list_eq_iff[of _ xs] f_join_nth)
apply (rule arg_cong[where f="(!) xs"])
apply (subgoal_tac "I \<down>< length xs = {..<length xs}")
 prefer 2
 apply fastforce
apply (subst inext_nth_cut_less_eq[where t="length xs", symmetric], simp)
apply (simp add: inext_nth_lessThan)
done

lemma f_join_all: "{..<length xs} \<subseteq> I \<Longrightarrow> xs \<Join>\<^sub>f I = xs"
by (rule f_join_all_conv[THEN iffD2])

corollary f_join_UNIV: "xs \<Join>\<^sub>f UNIV = xs"
by (simp add: f_join_all)

lemma f_join_union: "
  \<lbrakk> finite A; Max A < iMin B \<rbrakk> \<Longrightarrow> xs \<Join>\<^sub>f (A \<union> B) = xs \<Join>\<^sub>f A @ (xs \<Join>\<^sub>f B)"
apply (case_tac "A = {}", simp add: f_join_empty)
apply (case_tac "B = {}", simp add: f_join_empty)
apply (frule Max_less_iMin_imp_disjoint, assumption)
apply (simp add: list_eq_iff f_join_length cut_less_Un del: Max_less_iff)
apply (subgoal_tac "A \<down>< length xs \<inter> B \<down>< length xs = {}")
 prefer 2
 apply (simp add: cut_less_Int[symmetric] cut_less_empty)
apply (frule card_Un_disjoint[OF nat_cut_less_finite nat_cut_less_finite])
apply (clarsimp simp del: Max_less_iff)
apply (subst f_join_nth)
 apply (simp add: f_join_length cut_less_Un)
apply (simp add: nth_append f_join_length del: Max_less_iff, intro conjI impI)
 apply (simp add: f_join_nth f_join_length del: Max_less_iff)
   apply (rule ssubst[OF inext_nth_card_append_eq1], assumption)
  apply (rule order_less_le_trans[OF _ cut_less_card], assumption+)
 apply simp
apply (subst f_join_nth)
 apply (simp add: f_join_length)
apply (subgoal_tac "iMin B < length xs")
 prefer 2
 apply (rule ccontr)
 apply (simp add: linorder_not_less cut_less_Min_empty)
apply (frule order_less_trans, assumption)
apply (rule arg_cong[where f="\<lambda>x. xs ! x"])
apply (simp add: cut_less_Max_all inext_nth_card_append_eq2)
done

lemma f_join_singleton_if: "
  xs \<Join>\<^sub>f {n} = (if n < length xs then [xs ! n] else [])"
apply (clarsimp simp: list_eq_iff f_join_length cut_less_singleton)
apply (insert f_join_nth[of 0 xs "{n}"])
apply (simp add: f_join_length cut_less_singleton)
done

lemma f_join_insert: "
  n < length xs \<Longrightarrow>
  xs \<Join>\<^sub>f insert n I = xs \<Join>\<^sub>f (I \<down>< n) @ (xs ! n) # (xs \<Join>\<^sub>f (I \<down>> n))"
apply (rule_tac t="insert n I" and s="(I \<down>< n) \<union> {n} \<union> (I \<down>> n)" in subst, fastforce)
apply (insert nat_cut_less_finite[of I n])
apply (case_tac "I \<down>> n = {}")
 apply (simp add: f_join_empty del: Un_insert_right)
 apply (case_tac "I \<down>< n = {}")
  apply (simp add: f_join_empty f_join_singleton_if)
 apply (subgoal_tac "Max (I \<down>< n) < iMin {n}")
  prefer 2
  apply (simp add: cut_less_mem_iff)
 apply (simp add: f_join_union f_join_singleton_if del: Un_insert_right)
apply (subgoal_tac "Max {n} < iMin (I \<down>> n)")
 prefer 2
 apply (simp add: iMin_gr_iff cut_greater_mem_iff)
apply (case_tac "I \<down>< n = {}")
 apply (simp add: f_join_empty f_join_union f_join_singleton_if del: Un_insert_left)
apply (subgoal_tac "Max (I \<down>< n) < iMin {n}")
 prefer 2
 apply (simp add: cut_less_mem_iff)
apply (subgoal_tac "Max (I \<down>< n \<union> {n}) < iMin (I \<down>> n)")
 prefer 2
 apply (simp add: iMin_gr_iff i_cut_mem_iff)
apply (simp add: f_join_union f_join_singleton_if del: Un_insert_right)
done

lemma f_join_snoc: "
  (xs @ [x]) \<Join>\<^sub>f I =
  xs \<Join>\<^sub>f I @ (if length xs \<in> I then [x] else [])"
apply (simp add: list_eq_iff f_join_length)
apply (subgoal_tac "
  card (I \<down>< Suc (length xs)) =
  card (I \<down>< length xs) + (if length xs \<in> I then Suc 0 else 0)")
 prefer 2
 apply (simp add: nat_cut_le_less_conv[symmetric] cut_le_less_conv_if)
 apply (simp add: card_insert_if[OF nat_cut_less_finite] cut_less_mem_iff)
apply simp
apply (case_tac "length xs \<in> I")
 apply (clarsimp simp: f_join_length)
 apply (simp add: nth_append f_join_length, intro conjI impI)
  apply (subst f_join_nth[of _ "xs @ [x]"])
   apply (simp add: f_join_length)
  apply (simp add: nth_append less_card_cut_less_imp_inext_nth_less)
  apply (simp add: f_join_nth f_join_length)
 apply (simp add: linorder_not_less less_Suc_eq_le)
 apply (subst f_join_nth)
  apply (simp add: f_join_length)
 apply (subgoal_tac "I \<rightarrow> i = length xs")
  prefer 2
  apply (rule_tac t="length xs" and s="Max (I \<down>< Suc (length xs))" in subst)
   apply (rule Max_equality[OF _ nat_cut_less_finite])
   apply (simp add: cut_less_mem_iff)+
  apply (subst inext_nth_cut_less_eq[of _ _ "Suc (length xs)", symmetric], simp)
  apply (rule inext_nth_card_Max[OF nat_cut_less_finite])
   apply (simp add: card_gr0_imp_not_empty)
  apply simp+
apply (simp add: f_join_nth f_join_length)
apply (simp add: nth_append less_card_cut_less_imp_inext_nth_less)
done

(*<*)
(*
lemma "
  let xs = [0::nat,10,20,30]; ys =[100,110,120,130]; I = {0,2,4,6} in
  (xs @ ys) \<Join>\<^sub>f I = xs \<Join>\<^sub>f I @ (ys \<Join>\<^sub>f (I \<oplus>- (length xs)))"
by (simp add: Let_def f_join_def iT_Plus_neg_def)
*)
(*>*)


lemma f_join_append: "
  (xs @ ys) \<Join>\<^sub>f I = xs \<Join>\<^sub>f I @ ys \<Join>\<^sub>f (I \<oplus>- (length xs))"
apply (induct ys rule: rev_induct)
 apply (simp add: f_join_Nil)
apply (simp add: append_assoc[symmetric] f_join_snoc del: append_assoc)
apply (simp add: iT_Plus_neg_mem_iff add.commute[of "length xs"])
done

lemma take_f_join_eq1: "
  n < card (I \<down>< length xs) \<Longrightarrow>
  (xs \<Join>\<^sub>f I) \<down> n = xs \<Join>\<^sub>f (I \<down>< (I \<rightarrow> n))"
apply (frule less_card_cut_less_imp_inext_nth_less)
apply (simp add: list_eq_iff f_join_length cut_cut_less min_eqR)
apply (subgoal_tac "n < card I \<or> infinite I")
 prefer 2
 apply (case_tac "finite I")
 apply (drule order_less_le_trans[OF _ cut_less_card], simp+)
apply (simp add: min_eqL cut_less_inext_nth_card_eq1)
apply clarify
apply (subst f_join_nth)
 apply (simp add: f_join_length)
apply (subst f_join_nth)
 apply (simp add: f_join_length cut_cut_less min_eqL)
 apply (simp add: cut_less_inext_nth_card_eq1)
apply (simp add: cut_less_inext_nth_card_eq1 inext_nth_cut_less_eq)
done

lemma take_f_join_eq2: "
  card (I \<down>< length xs) \<le> n \<Longrightarrow> (xs \<Join>\<^sub>f I) \<down> n = xs \<Join>\<^sub>f I"
by (simp add: f_join_length)
lemma take_f_join_if: "
  (xs \<Join>\<^sub>f I) \<down> n =
  (if n < card (I \<down>< length xs) then xs \<Join>\<^sub>f (I \<down>< (I \<rightarrow> n)) else xs \<Join>\<^sub>f I)"
by (simp add: take_f_join_eq1 take_f_join_eq2)

lemma drop_f_join_eq1: "
  n < card (I \<down>< length xs) \<Longrightarrow>
  (xs \<Join>\<^sub>f I) \<up> n = xs \<Join>\<^sub>f (I \<down>\<ge> (I \<rightarrow> n))"
apply (case_tac "I = {}")
 apply (simp add: cut_less_empty)
apply (case_tac "I \<down>< length xs = {}")
 apply (simp add: cut_less_empty)
apply (rule same_append_eq[THEN iffD1, of "xs \<Join>\<^sub>f I \<down> n"])
txt \<open>First, a simplification step without \<open>take_f_join_eq1\<close> required for correct transformation, in order to eliminate \<open>(xs \<Join>\<^sub>f I) \<down> n\<close> in the equation.\<close>
apply simp
txt \<open>Now, \<open>take_f_join_eq1\<close> can be applied\<close>
apply (simp add: take_f_join_eq1)
apply (case_tac "I \<down>< (I \<rightarrow> n) = {}")
 apply (simp add: f_join_empty)
 apply (rule_tac t= "I \<rightarrow> n" and s="iMin I" in subst)
  apply (rule ccontr)
  apply (drule neq_le_trans[of "iMin I"])
   apply (simp add: iMin_le[OF inext_nth_closed])
  apply (simp add: cut_less_Min_not_empty)
 apply (simp add: cut_ge_Min_all)
apply (subst f_join_union[OF nat_cut_less_finite, symmetric])
 apply (subgoal_tac "I \<down>\<ge> (I \<rightarrow> n) \<noteq> {}")
  prefer 2
  apply (simp add: cut_ge_not_empty_iff)
  apply (blast intro: inext_nth_closed)
 apply (simp add: nat_cut_less_finite i_cut_mem_iff iMin_gr_iff)
apply (simp add: cut_less_cut_ge_ident)
done

lemma drop_f_join_eq2: "
  card (I \<down>< length xs) \<le> n \<Longrightarrow> (xs \<Join>\<^sub>f I) \<up> n = []"
by (simp add: f_join_length)

lemma drop_f_join_if: "
  (xs \<Join>\<^sub>f I) \<up> n =
  (if n < card (I \<down>< length xs) then xs \<Join>\<^sub>f (I \<down>\<ge> (I \<rightarrow> n)) else [])"
by (simp add: drop_f_join_eq1 drop_f_join_eq2)

lemma f_join_take: "xs \<down> n \<Join>\<^sub>f I = xs \<Join>\<^sub>f (I \<down>< n)"
apply (clarsimp simp: list_eq_iff f_join_length cut_cut_less min.commute)
apply (simp add: f_join_nth f_join_length cut_cut_less min.commute)
apply (case_tac "n < length xs")
 apply (simp add: min_eqL inext_nth_cut_less_eq)
 apply (simp add: less_card_cut_less_imp_inext_nth_less)
apply (simp add: min_eqR linorder_not_less)
apply (subst inext_nth_cut_less_eq)
apply (rule order_less_le_trans, assumption)
apply (rule card_mono[OF nat_cut_less_finite cut_less_mono], assumption)
apply simp
done

lemma f_join_drop: "xs \<up> n \<Join>\<^sub>f I = xs \<Join>\<^sub>f (I \<oplus> n)"
apply (case_tac "length xs \<le> n")
 apply (simp add: f_join_Nil)
 apply (rule sym)
 apply (simp add: f_join_Nil_conv' iT_Plus_mem_iff)
apply (rule subst[OF append_take_drop_id, of "\<lambda>x. xs \<up> n \<Join>\<^sub>f I = x \<Join>\<^sub>f (I \<oplus> n)" n])
apply (simp only: f_join_append)
apply (simp add: f_join_take min_eqR)
apply (simp add: iT_Plus_Plus_neg_inverse)
apply (rule_tac t="(I \<oplus> n) \<down>< n" and s="{}" in subst)
 apply (rule sym)
 apply (simp add: cut_less_empty_iff iT_Plus_mem_iff)
apply (simp add: f_join_empty)
done

lemma cut_less_eq_imp_f_join_eq: "
  A \<down>< length xs = B \<down>< length xs \<Longrightarrow> xs \<Join>\<^sub>f A = xs \<Join>\<^sub>f B"
apply (clarsimp simp: list_eq_iff f_join_length f_join_nth)
apply (rule subst[OF inext_nth_cut_less_eq, of _ A "length xs"], simp)
apply (rule subst[OF inext_nth_cut_less_eq, of _ B "length xs"], simp)
apply simp
done

corollary f_join_cut_less_eq: "
  length xs \<le> t \<Longrightarrow> xs \<Join>\<^sub>f (I \<down>< t) = xs \<Join>\<^sub>f I"
apply (rule cut_less_eq_imp_f_join_eq)
apply (simp add: cut_cut_less min_eqR)
done

lemma take_Suc_Max_eq_imp_f_join_eq: "
  \<lbrakk> finite I; xs \<down> Suc (Max I) = ys \<down> Suc (Max I) \<rbrakk> \<Longrightarrow>
  xs \<Join>\<^sub>f I = ys \<Join>\<^sub>f I"
apply (case_tac "I = {}")
 apply (simp add: f_join_empty)
apply (simp add: list_eq_iff f_join_length)
apply (case_tac "length xs < Suc (Max I)")
 apply (case_tac "length ys < Suc (Max I)")
  apply (clarsimp simp: min_eqL, rename_tac i)
  apply (simp add: f_join_nth2)
  apply (drule_tac x="I \<rightarrow> i" in spec)
  apply (subgoal_tac "I \<rightarrow> i < length ys")
   prefer 2
   apply (rule less_card_cut_less_imp_inext_nth_less, simp)
  apply simp
 apply (simp add: min_eq)
apply (case_tac "length ys < Suc (Max I)")
 apply (simp add: min_eq)
apply (simp add: linorder_not_less min_eqR Suc_le_eq del: Max_less_iff)
apply (subgoal_tac "I \<down>< length xs = I \<down>< length ys")
 prefer 2
 apply (simp add: cut_less_Max_all)
apply (clarsimp simp: f_join_nth2 simp del: Max_less_iff, rename_tac i)
apply (drule_tac x="I \<rightarrow> i" in spec)
apply (subgoal_tac "I \<rightarrow> i < Suc (Max I)")
 prefer 2
 apply (simp add: less_Suc_eq_le inext_nth_closed)
apply (simp del: Max_less_iff)
done

corollary f_join_take_Suc_Max_eq: "
  finite I \<Longrightarrow> xs \<down> Suc (Max I) \<Join>\<^sub>f I = xs \<Join>\<^sub>f I"
by (rule take_Suc_Max_eq_imp_f_join_eq, simp+)


text \<open>Joining infinite streams and infinite intervals\<close>

lemma i_join_nth: "(f \<Join>\<^sub>i I) n = f (I \<rightarrow> n)"
by (simp add: i_join_def)

lemma i_join_UNIV: "f \<Join>\<^sub>i UNIV = f"
by (simp add: ilist_eq_iff i_join_nth inext_nth_UNIV)

lemma i_join_union: "
  \<lbrakk> finite A; Max A < iMin B; B \<noteq> {} \<rbrakk> \<Longrightarrow>
  f \<Join>\<^sub>i (A \<union> B) = (f \<Down> Suc (Max A) \<Join>\<^sub>f A) \<frown> (f \<Join>\<^sub>i B)"
apply (case_tac "A = {}")
 apply (simp add: f_join_empty)
apply (simp (no_asm) add: ilist_eq_iff, clarify)
apply (simp add: i_join_nth i_append_nth f_join_length del: Max_less_iff)
apply (subgoal_tac "A \<down>< Suc (Max A) = A")
 prefer 2
 apply (simp add: nat_cut_le_less_conv[symmetric] cut_le_Max_all)
apply (simp del: Max_less_iff, intro conjI impI)
 apply (simp add: inext_nth_card_append_eq1)
 apply (simp add: f_join_nth f_join_length)
 apply (simp add: less_card_cut_less_imp_inext_nth_less)
apply (simp add: inext_nth_card_append_eq2)
done

lemma i_join_singleton: "f \<Join>\<^sub>i {a} = (\<lambda>n. f a)"
by (simp add: ilist_eq_iff i_join_nth inext_nth_singleton)

lemma i_join_insert: "
  f \<Join>\<^sub>i (insert n I) =
  (f \<Down> n) \<Join>\<^sub>f (I \<down>< n) \<frown> [f n] \<frown> (
    if I \<down>> n = {} then (\<lambda>x. f n) else f \<Join>\<^sub>i (I \<down>> n))"
apply (rule ssubst[OF insert_eq_cut_less_cut_greater])
apply (case_tac "I \<down>< n = {}")
 apply (simp add: f_join_empty, intro conjI impI)
  apply (simp add: i_join_singleton ilist_eq_iff i_append_nth)
 apply (subgoal_tac "Max {n} < iMin (I \<down>> n)")
  prefer 2
  apply (simp add: cut_greater_Min_greater)
 apply simp
 apply (subst insert_is_Un)
 apply (subst i_join_union[OF singleton_finite])
 apply (simp add: f_join_singleton_if)+
apply (intro conjI impI)
 apply (subgoal_tac "Max (I \<down>< n) < iMin {n}")
  prefer 2
  apply (simp add: nat_cut_less_Max_less)
 apply (rule_tac t="insert n (I \<down>< n)" and s="(I \<down>< n) \<union> {n}" in subst, simp)
 apply (subst i_join_union[OF nat_cut_less_finite _ singleton_not_empty], simp)
 apply (simp add: i_join_singleton)
 apply (rule_tac s="\<lambda>x. f n" and t="[f n] \<frown> (\<lambda>x. f n)" in subst)
  apply (simp add: ilist_eq_iff i_append_nth)
 apply (subst i_append_assoc[symmetric])
 apply (rule_tac t="[f n] \<frown> (\<lambda>x. f n)" and s="(\<lambda>x. f n)" in subst)
  apply (simp add: ilist_eq_iff i_append_nth)
 apply (rule arg_cong)
 apply (simp add: take_Suc_Max_eq_imp_f_join_eq[OF nat_cut_less_finite] min_eqR)
apply (subgoal_tac "Max (I \<down>< n) < iMin {n} \<and> Max {n} < iMin (I \<down>> n)", elim conjE)
 prefer 2
 apply (simp add: cut_greater_Min_greater nat_cut_less_Max_less)
apply (rule_tac t="insert n (I \<down>< n \<union> I \<down>> n)" and s="(I \<down>< n \<union> ({n} \<union> I \<down>> n))" in subst, simp)
apply (subgoal_tac "({n} \<union> I \<down>> n) \<noteq> {} \<and> Max (I \<down>< n) < iMin ({n} \<union> I \<down>> n)", elim conjE)
 prefer 2
 apply (simp add: iMin_insert)
apply (simp add: i_join_union nat_cut_less_finite singleton_finite del: Un_insert_left Un_insert_right Max_less_iff)
apply (simp add: f_join_singleton_if)
apply (rule arg_cong)
apply (simp add: take_Suc_Max_eq_imp_f_join_eq[OF nat_cut_less_finite] min_eqR)
done

lemma i_join_i_append: "
  infinite I \<Longrightarrow> (xs \<frown> f) \<Join>\<^sub>i I = (xs \<Join>\<^sub>f I) \<frown> (f \<Join>\<^sub>i (I \<oplus>- length xs))"
apply (clarsimp simp: ilist_eq_iff)
apply (simp add: i_join_nth i_append_nth f_join_length)
apply (subgoal_tac "I \<down>\<ge> length xs \<noteq> {}")
 prefer 2
 apply (fastforce simp: cut_ge_not_empty_iff infinite_nat_iff_unbounded_le)
apply (simp add: inext_nth_less_less_card_conv)
apply (intro conjI impI)
 apply (simp add: f_join_nth f_join_length)
apply (subgoal_tac "I \<oplus>- length xs \<noteq> {}")
 prefer 2
 apply (simp add: iT_Plus_neg_empty_iff infinite_imp_nonempty)
apply (simp add: iT_Plus_neg_inext_nth)
apply (case_tac "I \<down>< length xs = {}")
 apply (frule cut_less_empty_iff[THEN iffD1, THEN cut_ge_all_iff[THEN iffD2]])
 apply simp
apply (rule subst[OF inext_nth_card_append_eq2, OF nat_cut_less_finite], simp+)
  apply (simp add: less_imp_Max_less_iMin[OF nat_cut_less_finite] i_cut_mem_iff)
 apply simp
apply (simp add: cut_less_cut_ge_ident)
done

lemma i_take_i_join: "infinite I \<Longrightarrow> f \<Join>\<^sub>i I \<Down> n = f \<Down> (I \<rightarrow> n) \<Join>\<^sub>f I"
apply (clarsimp simp: list_eq_iff f_join_length cut_less_inext_nth_card_eq1, rename_tac i)
apply (simp add: i_join_nth)
apply (frule inext_nth_mono2_infin[THEN iffD2], assumption)
apply (rule_tac t="f (I \<rightarrow> i)" and s="f \<Down> (I \<rightarrow> n) ! (I \<rightarrow> i)" in subst, simp)
apply (rule sym, rule f_join_nth)
apply (simp add: f_join_length)
apply (simp add: inext_nth_less_less_card_conv[OF nat_cut_ge_infinite_not_empty])
done

lemma i_drop_i_join: "I \<noteq> {} \<Longrightarrow> f \<Join>\<^sub>i I \<Up> n = f \<Join>\<^sub>i (I \<down>\<ge> (I \<rightarrow> n))"
apply (simp (no_asm) add: ilist_eq_iff)
apply (simp add: i_join_nth inext_nth_cut_ge_inext_nth)
done

lemma i_join_i_take: "f \<Down> n \<Join>\<^sub>f I = f \<Join>\<^sub>i I \<Down> card (I \<down>< n)"
apply (clarsimp simp: list_eq_iff f_join_length)
apply (frule less_card_cut_less_imp_inext_nth_less)
apply (simp add: i_join_nth f_join_length f_join_nth)
done

lemma i_join_i_drop: "I \<noteq> {} \<Longrightarrow> f \<Up> n \<Join>\<^sub>i I = f \<Join>\<^sub>i (I \<oplus> n)"
apply (simp (no_asm) add: ilist_eq_iff)
apply (simp add: i_join_nth iT_Plus_inext_nth add.commute[of _ n])
done


lemma i_join_finite_nth_ge_card_eq_nth_Max: "
  \<lbrakk> finite I; I \<noteq> {}; card I \<le> Suc n \<rbrakk> \<Longrightarrow> (f \<Join>\<^sub>i I) n = f (Max I)"
by (simp add: i_join_nth inext_nth_card_Max)

lemma i_join_finite_i_drop_card_eq_const_nth_Max: "
  \<lbrakk> finite I; I \<noteq> {} \<rbrakk> \<Longrightarrow> (f \<Join>\<^sub>i I) \<Up> (card I) = (\<lambda>n. f (Max I))"
by (simp add: ilist_eq_iff i_join_finite_nth_ge_card_eq_nth_Max)

lemma i_join_finite_i_append_nth_Max_conv: "
  \<lbrakk> finite I; I \<noteq> {} \<rbrakk> \<Longrightarrow> (f \<Join>\<^sub>i I) = f \<Down> Suc (Max I) \<Join>\<^sub>f I \<frown> (\<lambda>n. f (Max I))"
apply (simp (no_asm) add: ilist_eq_iff, clarify)
apply (subgoal_tac "I \<down>< (Suc (Max I)) = I")
 prefer 2
 apply (simp add: nat_cut_le_less_conv[symmetric] cut_le_Max_all)
apply (simp add: i_append_nth i_join_nth f_join_length)
apply (intro conjI impI)
 apply (simp add: f_join_nth f_join_length)
 apply (rule sym, rule i_take_nth)
 apply (simp add: less_card_cut_less_imp_inext_nth_less)
apply (simp add: inext_nth_card_Max)
done


text \<open>Joining infinite streams and finite intervals\<close>

lemma i_f_join_length: "finite I \<Longrightarrow> length (f \<Join>\<^bsub>i-f\<^esub> I) = card I"
apply (simp add: i_f_join_def f_join_length)
apply (simp add: nat_cut_le_less_conv[symmetric] cut_le_Max_all)
done

lemma i_f_join_nth: "n < card I \<Longrightarrow> f \<Join>\<^bsub>i-f\<^esub> I ! n = f (I \<rightarrow> n)"
apply (frule card_gr0_imp_finite[OF gr_implies_gr0])
apply (frule card_gr0_imp_not_empty[OF gr_implies_gr0])
apply (simp add: i_f_join_def)
apply (subst i_take_nth[ of "I \<rightarrow> n" "Suc (Max I)" f, symmetric])
 apply (rule le_imp_less_Suc)
 apply (simp add: Max_ge[OF _ inext_nth_closed])
apply (simp add: f_join_nth2 nat_cut_le_less_conv[symmetric] cut_le_Max_all)
done

lemma i_f_join_empty: "f \<Join>\<^bsub>i-f\<^esub> {} = []"
by (simp add: i_f_join_def f_join_empty)

lemma i_f_join_eq_i_join_i_take: "
  finite I \<Longrightarrow> f \<Join>\<^bsub>i-f\<^esub> I = f \<Join>\<^sub>i I \<Down> (card I)"
apply (simp add: i_f_join_def)
apply (simp add: i_join_i_take nat_cut_le_less_conv[symmetric] cut_le_Max_all)
done

lemma i_f_join_union: "
  \<lbrakk> finite A; finite B; Max A < iMin B \<rbrakk> \<Longrightarrow>
  f \<Join>\<^bsub>i-f\<^esub> (A \<union> B) = f \<Join>\<^bsub>i-f\<^esub> A @ f \<Join>\<^bsub>i-f\<^esub> B"
apply (case_tac "A = {}", simp add: i_f_join_empty)
apply (case_tac "B = {}", simp add: i_f_join_empty)
apply (simp add: i_f_join_def f_join_union del: Max_less_iff)
apply (subgoal_tac "Max A < Max B")
 prefer 2
 apply (rule order_less_le_trans[OF _ iMin_le_Max], assumption+)
apply (simp add: Max_Un max_eqR[OF less_imp_le])
apply (rule take_Suc_Max_eq_imp_f_join_eq, assumption)
apply (simp add: min_eqR[OF less_imp_le])
done

lemma i_f_join_singleton: "f \<Join>\<^bsub>i-f\<^esub> {n} = [f n]"
by (simp add: i_f_join_def f_join_singleton_if)

lemma i_f_join_insert: "
  finite I \<Longrightarrow>
  f \<Join>\<^bsub>i-f\<^esub> insert n I = f \<Join>\<^bsub>i-f\<^esub> (I \<down>< n) @ f n # f \<Join>\<^bsub>i-f\<^esub> (I \<down>> n)"
apply (case_tac "I = {}")
 apply (simp add: i_f_join_singleton i_cut_empty i_f_join_empty)
(*
apply (subgoal_tac "n < Suc (Max (insert n I))")
 prefer 2
 apply simp
apply (frule less_Suc_eq_le[THEN iffD1])*)
apply (simp add: i_f_join_def)
apply (simp add: f_join_insert)
apply (frule cut_greater_finite[of _ n])
apply (case_tac "I \<down>> n = {}")
 apply (simp add: f_join_empty)
 apply (case_tac "I \<down>< n = {}")
  apply (simp add: f_join_empty)
 apply (rule take_Suc_Max_eq_imp_f_join_eq[OF nat_cut_less_finite])
 apply simp
 apply (rule arg_cong[where f="\<lambda>x. f \<Down> x"])
 apply simp
 apply (rule min_eqR, rule max.coboundedI1, rule less_imp_le)
 apply (simp add: nat_cut_less_Max_less)
apply (simp add: cut_greater_Max_eq)
apply (subgoal_tac "n < Max I")
 prefer 2
 apply (rule ccontr)
 apply (simp add: linorder_not_less cut_greater_Max_empty)
apply (simp add: max_eqR[OF less_imp_le])
apply (case_tac "I \<down>< n = {}")
 apply (simp add: f_join_empty)
apply (rule take_Suc_Max_eq_imp_f_join_eq[OF nat_cut_less_finite])
apply simp
apply (rule arg_cong[where f="\<lambda>x. f \<Down> x"])
apply simp
apply (rule min_eqR)
apply (blast intro: Max_subset)
done

lemma take_i_f_join_eq1: "
  n < card I \<Longrightarrow> f \<Join>\<^bsub>i-f\<^esub> I \<down> n = f \<Join>\<^bsub>i-f\<^esub> (I \<down>< (I \<rightarrow> n))"
apply (frule card_ge_0_finite[OF gr_implies_gr0])
apply (case_tac "I = {}")
 apply (simp add: cut_less_empty i_f_join_empty)
apply (subgoal_tac "n < card (I \<down>< Suc (Max I))")
 prefer 2
 apply (simp add: cut_less_Max_all)
apply (simp add: i_f_join_def take_f_join_eq1)
apply (case_tac "I \<down>< (I \<rightarrow> n) = {}")
 apply (simp add: f_join_empty)
apply (rule take_Suc_Max_eq_imp_f_join_eq[OF nat_cut_less_finite])
apply simp
apply (rule arg_cong[where f="\<lambda>x. f \<Down> x"])
apply simp
apply (rule min_eqR)
apply (rule order_trans[OF less_imp_le[OF cut_less_Max_less]])
apply (simp add: nat_cut_less_finite inext_nth_closed)+
done

lemma take_i_f_join_eq2: "
  \<lbrakk> finite I; card I \<le> n \<rbrakk> \<Longrightarrow> f \<Join>\<^bsub>i-f\<^esub> I \<down> n = f \<Join>\<^bsub>i-f\<^esub> I"
apply (case_tac "I = {}")
 apply (simp add: cut_less_empty i_f_join_empty)
apply (simp add: i_f_join_def take_f_join_eq2 cut_less_Max_all)
done

lemma take_i_f_join_if: "
  finite I \<Longrightarrow>
  f \<Join>\<^bsub>i-f\<^esub> I \<down> n = (if n < card I then f \<Join>\<^bsub>i-f\<^esub> (I \<down>< (I \<rightarrow> n)) else f \<Join>\<^bsub>i-f\<^esub> I)"
by (simp add: take_i_f_join_eq1 take_i_f_join_eq2)

lemma drop_i_f_join_eq1: "
  n < card I \<Longrightarrow> f \<Join>\<^bsub>i-f\<^esub> I \<up> n = f \<Join>\<^bsub>i-f\<^esub> (I \<down>\<ge> (I \<rightarrow> n))"
apply (frule card_ge_0_finite[OF gr_implies_gr0])
apply (case_tac "I = {}")
 apply (simp add: cut_ge_empty i_f_join_empty)
apply (subgoal_tac "n < card (I \<down>< Suc (Max I))")
 prefer 2
 apply (simp add: cut_less_Max_all)
apply (simp add: i_f_join_def drop_f_join_eq1)
apply (subgoal_tac "I \<down>\<ge> (I \<rightarrow> n) \<noteq> {}")
 prefer 2
 apply (rule in_imp_not_empty[of "I \<rightarrow> n"])
 apply (simp add: cut_ge_mem_iff inext_nth_closed)
apply (rule take_Suc_Max_eq_imp_f_join_eq)
 apply (rule cut_ge_finite, assumption)
apply simp
apply (rule arg_cong[where f="\<lambda>x. f \<Down> x"])
apply (simp add: min_eqR cut_ge_Max_eq)
done

lemma drop_i_f_join_eq2: "
  \<lbrakk> finite I; card I \<le> n \<rbrakk> \<Longrightarrow> f \<Join>\<^bsub>i-f\<^esub> I \<up> n = []"
by (simp add: i_f_join_length)

lemma drop_i_f_join_if: "
  finite I \<Longrightarrow>
  f \<Join>\<^bsub>i-f\<^esub> I \<up> n = (if n < card I then f \<Join>\<^bsub>i-f\<^esub> (I \<down>\<ge> (I \<rightarrow> n)) else [])"
by (simp add: drop_i_f_join_eq1 drop_i_f_join_eq2)

lemma i_f_join_i_drop: "
  finite I \<Longrightarrow> f \<Up> n \<Join>\<^bsub>i-f\<^esub> I = f \<Join>\<^bsub>i-f\<^esub> (I \<oplus> n)"
apply (case_tac "I = {}")
 apply (simp add: iT_Plus_empty i_f_join_empty)
apply (simp add: i_f_join_def iT_Plus_Max)
apply (simp add: i_take_i_drop f_join_drop)
done

lemma i_take_Suc_Max_eq_imp_i_f_join_eq: "
  f \<Down> Suc (Max I) = g \<Down> Suc (Max I) \<Longrightarrow> f \<Join>\<^bsub>i-f\<^esub> I = g \<Join>\<^bsub>i-f\<^esub> I"
by (simp add: i_f_join_def)

lemma i_take_i_join_eq_i_f_join: "
  infinite I \<Longrightarrow> f \<Join>\<^sub>i I \<Down> n = f \<Join>\<^bsub>i-f\<^esub> (I \<down>< (I \<rightarrow> n))"
apply (frule infinite_imp_nonempty)
apply (case_tac "n = 0")
 apply (simp add: cut_less_Min_empty i_f_join_empty)
apply (frule inext_nth_gr_Min_conv_infinite[THEN iffD2], simp)
apply (simp add: i_take_i_join i_f_join_def)
apply (subgoal_tac "Suc (Max (I \<down>< (I \<rightarrow> n))) \<le> I \<rightarrow> n")
 prefer 2
 apply (rule Suc_leI)
 apply (rule nat_cut_less_Max_less)
 apply (simp add: cut_less_Min_not_empty)
apply (simp add: f_join_cut_less_eq)
apply (simp add: i_join_i_take)
apply (rule arg_cong[where f="\<lambda>x. f \<Join>\<^sub>i I \<Down> card x"])
apply (clarsimp simp: gr0_conv_Suc)
apply (simp add: cut_le_less_inext_conv[OF inext_nth_closed, symmetric])
apply (simp add: nat_cut_le_less_conv[symmetric])
apply (rule arg_cong[where f="\<lambda>x. I \<down>\<le> x"])
apply (rule sym, rule Max_equality[OF _ nat_cut_le_finite])
apply (simp add: cut_le_mem_iff inext_nth_closed)+
done


subsubsection \<open>Results for intervals from \<open>IL_Interval\<close>\<close>

lemma f_join_iFROM: "xs \<Join>\<^sub>f [n\<dots>] = xs \<up> n"
apply (clarsimp simp: list_eq_iff f_join_length iFROM_cut_less iIN_card Suc_diff_Suc)
apply (subst f_join_nth2)
 apply (simp add: iFROM_cut_less iIN_card)
apply (simp add: iFROM_inext_nth)
done

lemma i_join_iFROM: "f \<Join>\<^sub>i [n\<dots>] = f \<Up> n"
by (simp add: ilist_eq_iff i_join_nth iFROM_inext_nth)

lemma f_join_iIN: "xs \<Join>\<^sub>f [n\<dots>,d] = xs \<up> n \<down> Suc d"
apply (simp add: list_eq_iff f_join_length iIN_cut_less iIN_card Suc_diff_Suc min_eq)
apply (simp add: f_join_nth2 iIN_cut_less iIN_card iIN_inext_nth)
done

lemma i_f_join_iIN: "f \<Join>\<^bsub>i-f\<^esub> [n\<dots>,d] = f \<Up> n \<Down> Suc d"
by (simp add: i_f_join_def f_join_iIN iIN_Max i_take_drop)

lemma f_join_iTILL: "xs \<Join>\<^sub>f [\<dots>n] = xs \<down> (Suc n)"
by (simp add: iIN_0_iTILL_conv[symmetric] f_join_iIN)

lemma i_f_join_iTILL: "f \<Join>\<^bsub>i-f\<^esub> [\<dots>n] = f \<Down> Suc n"
by (simp add: iIN_0_iTILL_conv[symmetric] i_f_join_iIN)


lemma f_join_f_expand_iT_Mult: "
  0 < k \<Longrightarrow> xs \<odot>\<^sub>f k \<Join>\<^sub>f (I \<otimes> k) = xs \<Join>\<^sub>f I"
apply (case_tac "I = {}")
 apply (simp add: iT_Mult_empty f_join_empty)
apply (simp add: list_eq_iff f_join_length)
apply (clarsimp simp: iT_Mult_cut_less2 iT_Mult_card)
apply (simp add: f_join_nth2 iT_Mult_cut_less2 iT_Mult_card)
apply (drule less_card_cut_less_imp_inext_nth_less)
apply (simp add: iT_Mult_inext_nth f_expand_nth_mult)
done

lemma i_join_i_expand_iT_Mult: "
  \<lbrakk> 0 < k; I \<noteq> {} \<rbrakk> \<Longrightarrow> f \<odot>\<^sub>i k \<Join>\<^sub>i (I \<otimes> k) = f \<Join>\<^sub>i I"
apply (simp (no_asm) add: ilist_eq_iff, clarify)
apply (simp add: i_join_nth iT_Mult_inext_nth i_expand_nth_mult)
done

lemma i_f_join_i_expand_iT_Mult: "
  \<lbrakk> 0 < k; finite I \<rbrakk> \<Longrightarrow> f \<odot>\<^sub>i k \<Join>\<^bsub>i-f\<^esub> (I \<otimes> k) = f \<Join>\<^bsub>i-f\<^esub> I"
apply (case_tac "I = {}")
 apply (simp add: iT_Mult_empty i_f_join_empty)
apply (clarsimp simp: list_eq_iff i_f_join_length iT_Mult_finite_iff iT_Mult_not_empty iT_Mult_card)
apply (simp add: i_f_join_nth iT_Mult_card iT_Mult_inext_nth i_expand_nth_mult)
done

lemma f_join_f_shrink_iT_Plus_iT_Div_mod: "
  \<lbrakk> 0 < k; \<forall>x\<in>I. x mod k = 0 \<rbrakk> \<Longrightarrow>
  (xs \<longmapsto>\<^sub>f k) \<Join>\<^sub>f (I \<oplus> (k - 1)) = xs \<div>\<^sub>f k \<Join>\<^sub>f (I \<oslash> k)"
apply (case_tac "I = {}")
 apply (simp add: iT_Plus_empty iT_Div_empty f_join_empty)
apply (simp add: list_eq_iff f_join_length f_shrink_length)
apply (subgoal_tac "Suc (length xs) - k \<le> length xs - length xs mod k")
 prefer 2
 apply (case_tac "length xs < k", simp)
 apply (simp add: Suc_diff_le linorder_not_less)
 apply (rule Suc_leI)
 apply (rule diff_less_mono2, simp)
 apply (rule order_less_le_trans[OF mod_less_divisor], assumption+)
apply (rule context_conjI)
 apply (simp add: iT_Plus_cut_less iT_Div_cut_less2 iT_Plus_card)
 apply (subst iT_Div_card_inj_on)
  apply (rule mod_eq_imp_div_right_inj_on)
  apply clarsimp+
 apply (rule arg_cong[where f=card])
 apply (simp (no_asm_simp) add: set_eq_iff cut_less_mem_iff, clarify)
 apply (rule conj_cong, simp)
 apply (rule iffI)
  apply simp
   apply (frule_tac x=x and m=k in less_mod_eq_imp_add_divisor_le)
  apply (simp add: mod_diff_right_eq [symmetric])
 apply simp
apply (clarsimp simp: f_join_nth f_join_length f_shrink_length)
apply (simp add: iT_Plus_inext_nth iT_Plus_not_empty)
apply (simp add: iT_Div_mod_inext_nth)
apply (subst f_shrink_nth_eq_f_last_message_hold_nth)
 apply (drule sym, simp, thin_tac "card x = card y" for x y)
 apply (simp add: iT_Plus_cut_less iT_Plus_card)
 apply (rule less_mult_imp_div_less)
 apply (rule less_le_trans[OF less_card_cut_less_imp_inext_nth_less], assumption)
 apply (simp add: div_mult_cancel)
apply (simp add: div_mult_cancel inext_nth_closed)
done

lemma i_join_i_shrink_iT_Plus_iT_Div_mod: "
  \<lbrakk> 0 < k; I \<noteq> {}; \<forall>x\<in>I. x mod k = 0 \<rbrakk> \<Longrightarrow>
  (f \<longmapsto>\<^sub>i k) \<Join>\<^sub>i (I \<oplus> (k - 1))= f \<div>\<^sub>i k \<Join>\<^sub>i (I \<oslash> k)"
apply (simp (no_asm) add: ilist_eq_iff, clarify)
apply (simp add: i_join_nth)
apply (simp add: i_shrink_nth_eq_i_last_message_hold_nth)
apply (simp add: iT_Plus_inext_nth iT_Div_mod_inext_nth)
apply (drule_tac x="I \<rightarrow> x" in bspec)
 apply (simp add: inext_nth_closed)
apply (simp add: mod_0_div_mult_cancel)
done

lemma i_f_join_i_shrink_iT_Plus_iT_Div_mod: "
  \<lbrakk> 0 < k; finite I; \<forall>x\<in>I. x mod k = 0 \<rbrakk> \<Longrightarrow>
  (f \<longmapsto>\<^sub>i k) \<Join>\<^bsub>i-f\<^esub> (I \<oplus> (k - 1))= f \<div>\<^sub>i k \<Join>\<^bsub>i-f\<^esub> (I \<oslash> k)"
apply (case_tac "I = {}")
 apply (simp add: iT_Plus_empty iT_Div_empty i_f_join_empty)
apply (simp add: i_f_join_def iT_Plus_Max iT_Div_Max)
apply (simp add: i_last_message_hold_i_take[symmetric] i_shrink_i_take_mult[symmetric])
apply (simp add: add.commute[of k])
apply (simp add: mod_0_div_mult_cancel[THEN iffD1])
apply (simp add: f_join_f_shrink_iT_Plus_iT_Div_mod[unfolded One_nat_def])
done

corollary f_join_f_shrink_iT_Plus_iT_Div_mod_subst: "
  \<lbrakk> 0 < k; \<forall>x\<in>I. x mod k = 0;
    A = I \<oplus> (k - 1); B = I \<oslash> k \<rbrakk> \<Longrightarrow>
  (xs \<longmapsto>\<^sub>f k) \<Join>\<^sub>f A = xs \<div>\<^sub>f k \<Join>\<^sub>f B"
by (simp add: f_join_f_shrink_iT_Plus_iT_Div_mod[unfolded One_nat_def])
corollary i_join_i_shrink_iT_Plus_iT_Div_mod_subst: "
  \<lbrakk> 0 < k; I \<noteq> {}; \<forall>x\<in>I. x mod k = 0;
    A = I \<oplus> (k - 1); B = I \<oslash> k \<rbrakk> \<Longrightarrow>
  (f \<longmapsto>\<^sub>i k) \<Join>\<^sub>i A = f \<div>\<^sub>i k \<Join>\<^sub>i B"
by (simp add: i_join_i_shrink_iT_Plus_iT_Div_mod[unfolded One_nat_def])
corollary i_f_join_i_shrink_iT_Plus_iT_Div_mod_subst: "
  \<lbrakk> 0 < k; finite I; \<forall>x\<in>I. x mod k = 0;
    A = I \<oplus> (k - 1); B = I \<oslash> k \<rbrakk> \<Longrightarrow>
  (f \<longmapsto>\<^sub>i k) \<Join>\<^bsub>i-f\<^esub> A= f \<div>\<^sub>i k \<Join>\<^bsub>i-f\<^esub> B"
by (simp add: i_f_join_i_shrink_iT_Plus_iT_Div_mod[unfolded One_nat_def])



lemma f_join_f_shrink_iT_Div_mod: "
  \<lbrakk> 0 < k; \<forall>x\<in>I. x mod k = k - 1 \<rbrakk> \<Longrightarrow>
  (xs \<longmapsto>\<^sub>f k) \<Join>\<^sub>f I = xs \<div>\<^sub>f k \<Join>\<^sub>f (I \<oslash> k)"
apply (case_tac "I = {}")
 apply (simp add: iT_Div_empty f_join_empty)
apply (frule Suc_leI, drule order_le_imp_less_or_eq, erule disjE)
 prefer 2
 apply (drule sym, simp add: iT_Div_1)
apply (rule_tac t=I and s="I \<oplus>- (k - 1) \<oplus> (k - 1)" in subst)
 apply (rule iT_Plus_neg_Plus_le_inverse)
 apply (rule ccontr)
 apply (drule_tac x="iMin I" in bspec, simp add: iMinI_ex2)
 apply (simp add: iMinI_ex2)+
apply (subgoal_tac "\<And>x. x + k - Suc 0 \<in> I \<Longrightarrow> x mod k = 0")
 prefer 2
 apply (rule mod_add_eq_imp_mod_0[THEN iffD1, of "k - Suc 0"])
 apply (simp add: add.commute[of k])
apply (subst iT_Plus_Div_distrib_mod_less)
 apply (clarsimp simp: iT_Plus_neg_mem_iff)
apply (simp add: iT_Plus_0)
apply (rule f_join_f_shrink_iT_Plus_iT_Div_mod[unfolded One_nat_def], simp)
apply (simp add: iT_Plus_neg_mem_iff)
done

lemma i_join_i_shrink_iT_Div_mod: "
  \<lbrakk> 0 < k; I \<noteq> {}; \<forall>x\<in>I. x mod k = k - 1 \<rbrakk> \<Longrightarrow>
  (f \<longmapsto>\<^sub>i k) \<Join>\<^sub>i I= f \<div>\<^sub>i k \<Join>\<^sub>i (I \<oslash> k)"
apply (simp (no_asm) add: ilist_eq_iff, clarify)
apply (simp add: i_join_nth)
apply (simp add: i_shrink_nth_eq_i_last_message_hold_nth)
apply (simp add: iT_Div_mod_inext_nth)
apply (drule_tac x="I \<rightarrow> x" in bspec)
 apply (rule inext_nth_closed, assumption)
apply (simp add: div_mult_cancel)
apply (subgoal_tac "k - Suc 0 \<le> I \<rightarrow> x ")
 prefer 2
 apply (rule order_trans[OF _ mod_le_dividend[where n=k]])
 apply simp
apply simp
done

lemma i_f_join_i_shrink_iT_Div_mod: "
  \<lbrakk> 0 < k; finite I; \<forall>x\<in>I. x mod k = k - 1 \<rbrakk> \<Longrightarrow>
  (f \<longmapsto>\<^sub>i k) \<Join>\<^bsub>i-f\<^esub> I = f \<div>\<^sub>i k \<Join>\<^bsub>i-f\<^esub> (I \<oslash> k)"
apply (case_tac "I = {}")
 apply (simp add: iT_Plus_empty iT_Div_empty i_f_join_empty)
apply (simp add: i_f_join_def)
apply (simp add: iT_Div_Max)
apply (simp add: i_last_message_hold_i_take[symmetric] i_shrink_i_take_mult[symmetric] add.commute[of k])
apply (simp add: div_mult_cancel)
apply (subgoal_tac "k - Suc 0 \<le> Max I")
 prefer 2
 apply (rule order_trans[OF _ mod_le_dividend[where n=k]])
 apply simp
apply (simp add: f_join_f_shrink_iT_Div_mod)
done

lemma f_join_f_expand_iMOD: "
  0 < k \<Longrightarrow> xs \<odot>\<^sub>f k \<Join>\<^sub>f [n * k, mod k] = xs \<Join>\<^sub>f [n\<dots>]"
by (subst iFROM_mult[symmetric], rule f_join_f_expand_iT_Mult)
corollary f_join_f_expand_iMOD_0: "
  0 < k \<Longrightarrow> xs \<odot>\<^sub>f k \<Join>\<^sub>f [0, mod k] = xs"
apply (drule f_join_f_expand_iMOD[of k xs 0])
apply (simp add: iFROM_0 f_join_UNIV)
done

lemma f_join_f_expand_iMODb: "
  0 < k \<Longrightarrow> xs \<odot>\<^sub>f k \<Join>\<^sub>f [n * k, mod k, d] = xs \<Join>\<^sub>f [n\<dots>,d]"
by (subst iIN_mult[symmetric], rule f_join_f_expand_iT_Mult)

corollary f_join_f_expand_iMODb_0: "
  0 < k \<Longrightarrow> xs \<odot>\<^sub>f k \<Join>\<^sub>f [0, mod k, n] = xs \<Join>\<^sub>f [\<dots>n]"
apply (drule f_join_f_expand_iMODb[of k xs 0 n])
apply (simp add: iIN_0_iTILL_conv)
done

lemma i_join_i_expand_iMOD: "
  0 < k \<Longrightarrow> f \<odot>\<^sub>i k \<Join>\<^sub>i [n * k, mod k] = f \<Join>\<^sub>i [n\<dots>]"
by (subst iFROM_mult[symmetric], rule i_join_i_expand_iT_Mult[OF _ iFROM_not_empty])

corollary i_join_i_expand_iMOD_0: "
  0 < k \<Longrightarrow> f \<odot>\<^sub>i k \<Join>\<^sub>i [0, mod k] = f"
apply (drule i_join_i_expand_iMOD[of k f 0])
apply (simp add: iFROM_0 i_join_UNIV)
done

lemma i_join_i_expand_iMODb: "
  0 < k \<Longrightarrow> f \<odot>\<^sub>i k \<Join>\<^sub>i [n * k, mod k, d] = f \<Join>\<^sub>i [n\<dots>,d]"
by (subst iIN_mult[symmetric], rule i_join_i_expand_iT_Mult[OF _ iIN_not_empty])

corollary i_join_i_expand_iMODb_0: "
  0 < k \<Longrightarrow> f \<odot>\<^sub>i k \<Join>\<^sub>i [0, mod k, n] = f \<Join>\<^sub>i [\<dots>n]"
apply (drule i_join_i_expand_iMODb[of k f 0 n])
apply (simp add: iIN_0_iTILL_conv)
done


lemma i_f_join_i_expand_iMODb: "
  0 < k \<Longrightarrow> f \<odot>\<^sub>i k \<Join>\<^bsub>i-f\<^esub> [n * k, mod k, d] = f \<Join>\<^bsub>i-f\<^esub> [n\<dots>,d]"
by (subst iIN_mult[symmetric], rule i_f_join_i_expand_iT_Mult[OF _ iIN_finite])
corollary i_f_join_i_expand_iMODb_0: "
  0 < k \<Longrightarrow> f \<odot>\<^sub>i k \<Join>\<^bsub>i-f\<^esub> [0, mod k, n] = f \<Join>\<^bsub>i-f\<^esub> [\<dots>n]"
apply (drule i_f_join_i_expand_iMODb[of k f 0 n])
apply (simp add: iIN_0_iTILL_conv)
done


lemma f_join_f_shrink_iMOD: "
  0 < k \<Longrightarrow> (xs \<longmapsto>\<^sub>f k) \<Join>\<^sub>f [n * k + (k - 1), mod k] = xs \<div>\<^sub>f k \<Join>\<^sub>f [n\<dots>]"
apply (rule f_join_f_shrink_iT_Plus_iT_Div_mod_subst[where I="[n * k, mod k]"])
apply (simp add: iMOD_iff iMOD_add iMOD_div_ge)+
done

corollary f_join_f_shrink_iMOD_0: "
  0 < k \<Longrightarrow> (xs \<longmapsto>\<^sub>f k) \<Join>\<^sub>f [k - 1, mod k] = xs \<div>\<^sub>f k"
apply (frule f_join_f_shrink_iMOD[of k xs 0])
apply (simp add: iFROM_0 f_join_UNIV)
done

lemma f_join_f_shrink_iMODb: "
  0 < k \<Longrightarrow> (xs \<longmapsto>\<^sub>f k) \<Join>\<^sub>f [n * k + (k - 1), mod k, d] = xs \<div>\<^sub>f k \<Join>\<^sub>f [n\<dots>,d]"
apply (rule f_join_f_shrink_iT_Plus_iT_Div_mod_subst[where I="[n * k, mod k, d]"])
apply (simp add: iMODb_iff iMODb_add iMODb_div_ge)+
done

corollary f_join_f_shrink_iMODb_0: "
  0 < k \<Longrightarrow> (xs \<longmapsto>\<^sub>f k) \<Join>\<^sub>f [k - 1, mod k, n] = xs \<div>\<^sub>f k \<Join>\<^sub>f [\<dots>n]"
apply (frule f_join_f_shrink_iMODb[of k xs 0 n])
apply (simp add: iIN_0_iTILL_conv)
done

lemma i_join_i_shrink_iMOD: "
  0 < k \<Longrightarrow> (f \<longmapsto>\<^sub>i k) \<Join>\<^sub>i [n * k + (k - 1), mod k] = f \<div>\<^sub>i k \<Join>\<^sub>i [n\<dots>]"
apply (rule i_join_i_shrink_iT_Plus_iT_Div_mod_subst[where I="[n * k, mod k]"])
apply (simp add: iMOD_not_empty iMOD_iff iMOD_add iMOD_div_ge)+
done

corollary i_join_i_shrink_iMOD_0: "
  0 < k \<Longrightarrow> (f \<longmapsto>\<^sub>i k) \<Join>\<^sub>i [k - 1, mod k] = f \<div>\<^sub>i k"
apply (frule i_join_i_shrink_iMOD[of k f 0])
apply (simp add: iFROM_0 i_join_UNIV)
done

lemma i_f_join_i_shrink_iMODb: "
  0 < k \<Longrightarrow> (f \<longmapsto>\<^sub>i k) \<Join>\<^bsub>i-f\<^esub> [n * k + (k - 1), mod k, d] = f \<div>\<^sub>i k \<Join>\<^bsub>i-f\<^esub> [n\<dots>,d]"
apply (rule i_f_join_i_shrink_iT_Plus_iT_Div_mod_subst[where I="[n * k, mod k, d]"])
apply (simp add: iMODb_finite iMODb_iff iMODb_add iMODb_div_ge)+
done

corollary i_f_join_i_shrink_iMODb_0: "
  0 < k \<Longrightarrow> (f \<longmapsto>\<^sub>i k) \<Join>\<^bsub>i-f\<^esub> [k - 1, mod k, n] = f \<div>\<^sub>i k \<Join>\<^bsub>i-f\<^esub> [\<dots>n]"
apply (frule i_f_join_i_shrink_iMODb[of k f 0 n])
apply (simp add: iIN_0_iTILL_conv i_join_UNIV)
done


subsection \<open>Streams and temporal operators\<close>

lemma i_shrink_eq_NoMsg_iAll_conv: "
  0 < k \<Longrightarrow> ((s \<div>\<^sub>i k) t = \<NoMsg>) = (\<box> t1 [t * k\<dots>,k - Suc 0]. s t1 = \<NoMsg>)"
apply (simp add: i_shrink_nth last_message_NoMsg_conv iAll_def Ball_def iIN_iff)
apply (rule iffI)
 apply (clarify, rename_tac i)
 apply (drule_tac x="i - t * k" in spec)
 apply simp
apply (clarify, rename_tac i)
apply (drule_tac x="t * k + i" in spec)
apply simp
done

lemma i_shrink_eq_NoMsg_iAll_conv2: "
  0 < k \<Longrightarrow> ((s \<div>\<^sub>i k) t = \<NoMsg>) = (\<box> t1 [\<dots>k - 1] \<oplus> (t * k). s t1 = \<NoMsg>)"
by (simp add: iT_add i_shrink_eq_NoMsg_iAll_conv)

lemma i_shrink_eq_Msg_iEx_iAll_conv: "
  \<lbrakk> 0 < k; m \<noteq> \<NoMsg> \<rbrakk> \<Longrightarrow>
  ((s \<div>\<^sub>i k) t = m) =
  (\<diamond> t1 [t * k\<dots>,k - Suc 0]. s t1 = m \<and>
    (\<box> t2 [Suc t1\<dots>]. t2 \<le> t * k + k - Suc 0 \<longrightarrow> s t2 = \<NoMsg>))"
apply (simp add: i_shrink_nth last_message_conv)
apply (simp add: iAll_def iEx_def Ball_def Bex_def iIN_iff iFROM_iff)
apply (rule iffI)
 apply (clarsimp, rename_tac i)
 apply (rule_tac x="t * k + i" in exI)
 apply (simp add: diff_add_assoc less_imp_le_pred del: add_diff_assoc)
 apply (clarsimp, rename_tac j)
 apply (drule_tac x="j - t * k" in spec)
 apply simp
apply (clarsimp, rename_tac i)
apply (rule_tac x="i - t * k" in exI)
apply simp
done

lemma i_shrink_eq_Msg_iEx_iAll_conv2: "
  \<lbrakk> 0 < k; m \<noteq> \<NoMsg> \<rbrakk> \<Longrightarrow>
  ((s \<div>\<^sub>i k) t = m) =
  (\<diamond> t1 [\<dots>k - 1] \<oplus> (t * k). s t1 = m \<and>
    (\<box> t2 [1\<dots>] \<oplus> t1 . t2 \<le> t * k + k - 1 \<longrightarrow> s t2 = \<NoMsg>))"
by (simp add: iT_add i_shrink_eq_Msg_iEx_iAll_conv)

lemma i_shrink_eq_Msg_iEx_iAll_cut_greater_conv: "
  \<lbrakk> 0 < k; m \<noteq> \<NoMsg> \<rbrakk> \<Longrightarrow>
  ((s \<div>\<^sub>i k) t = m) =
  (\<diamond> t1 [t * k\<dots>,k - Suc 0]. s t1 = m \<and>
    (\<box> t2 [t * k\<dots>,k - Suc 0] \<down>> t1. s t2 = \<NoMsg>))"
apply (simp add: i_shrink_eq_Msg_iEx_iAll_conv)
apply (simp add: iIN_cut_greater iEx_def)
apply (rule bex_cong2[OF subset_refl])
apply (force simp: iAll_def Ball_def iT_iff)
done

lemma i_shrink_eq_Msg_iEx_iAll_cut_greater_conv2: "
  \<lbrakk> 0 < k; m \<noteq> \<NoMsg> \<rbrakk> \<Longrightarrow>
  ((s \<div>\<^sub>i k) t = m) =
  (\<diamond> t1 [\<dots>k - 1] \<oplus> (t * k). s t1 = m \<and>
    (\<box> t2 ([\<dots>k - 1] \<oplus> (t * k)) \<down>> t1. s t2 = \<NoMsg>))"
by (simp add: iT_add i_shrink_eq_Msg_iEx_iAll_cut_greater_conv)

lemma i_shrink_eq_Msg_iSince_conv: "
  \<lbrakk> 0 < k; m \<noteq> \<NoMsg> \<rbrakk> \<Longrightarrow>
  ((s \<div>\<^sub>i k) t = m) =
  (s t2 = \<NoMsg>. t2 \<S> t1 [t * k\<dots>,k - Suc 0]. s t1 = m)"
by (simp add: iSince_def iIN_cut_greater i_shrink_eq_Msg_iEx_iAll_cut_greater_conv)
lemma i_shrink_eq_Msg_iSince_conv2: "
  \<lbrakk> 0 < k; m \<noteq> \<NoMsg> \<rbrakk> \<Longrightarrow>
  ((s \<div>\<^sub>i k) t = m) =
  (s t2 = \<NoMsg>. t2 \<S> t1 [\<dots>k - 1] \<oplus> (t * k). s t1 = m)"
by (simp add: iT_add i_shrink_eq_Msg_iSince_conv)


lemma iT_Mult_iAll_i_expand_nth_iff:
  "0 < k \<Longrightarrow> (\<box> t (I \<otimes> k). P ((f \<odot>\<^sub>i k) t)) = (\<box> t I. P (f t))"
apply (rule iffI)
 apply clarify
 apply (drule_tac t="t * k" in ispec)
  apply (simp add: iT_Mult_mem_iff2)
 apply (simp add: i_expand_nth_mult)
apply (fastforce simp: iT_Mult_mem_iff mult.commute[of k] i_expand_nth_mod_eq_0)
done


text \<open>Streams and temporal operators cycle start/finish events\<close>

lemma i_shrink_eq_NoMsg_iAll_start_event_conv: "
  \<lbrakk> 0 < k; \<And>t. event t = (t mod k = 0); t0 = t * k \<rbrakk> \<Longrightarrow>
  ((s \<div>\<^sub>i k) t = \<NoMsg>) =
  (s t0 = \<NoMsg> \<and> (\<circle> t' t0 [0\<dots>]. (s t1 = \<NoMsg>. t1 \<U> t2 ([0\<dots>] \<oplus> t'). event t2)))"
apply (case_tac "k = Suc 0")
 apply (simp add: iT_add iT_not_empty iNext_True)
apply (drule neq_le_trans[OF not_sym], simp)
apply (simp add: i_shrink_eq_NoMsg_iAll_conv iTL_defs Ball_def Bex_def iT_add iT_iff iFROM_cut_less iFROM_inext)
apply (rule iffI)
 apply simp
 apply (rule_tac x="t * k + k" in exI)
 apply fastforce
apply (clarify elim!: dvdE, rename_tac x1 x2)
apply (case_tac "x2 = Suc (t * k)")
 apply (simp add: mod_Suc)
apply (clarsimp elim!: dvdE, rename_tac q)
apply (drule_tac y=x1 in order_le_imp_less_or_eq, erule disjE)
 prefer 2
 apply simp
apply (drule_tac x=x1 in spec)
apply (simp add: mult.commute[of k])
apply (drule Suc_le_lessD)
apply (drule_tac y="q * k" and m=k in less_mod_eq_imp_add_divisor_le, simp)
apply simp
done

lemma i_shrink_eq_Msg_iUntil_start_event_conv: "
  \<lbrakk> 0 < k; m \<noteq> \<NoMsg>; \<And>t. event t = (t mod k = 0); t0 = t * k \<rbrakk> \<Longrightarrow>
  ((s \<div>\<^sub>i k) t = m) = (
  (s t0 = m \<and> (\<circle> t' t0 [0\<dots>]. (s t1 = \<NoMsg>. t1 \<U> t2 ([0\<dots>] \<oplus> t'). event t2))) \<or>
  (\<circle> t' t0 [0\<dots>]. (\<not> event t1. t1 \<U> t2 ([0\<dots>] \<oplus> t'). (
    s t2 = m \<and> \<not> event t2 \<and> (\<circle> t'' t2 [0\<dots>].
      (s t3 = \<NoMsg>. t3 \<U> t4 ([0\<dots>] \<oplus> t''). event t4))))))"
apply (case_tac "k = Suc 0")
 apply (simp add: iT_add iT_not_empty iNext_iff)
apply (drule neq_le_trans[OF not_sym], simp)
apply (simp add: i_shrink_eq_Msg_iSince_conv iTL_defs iT_add iT_cut_greater iT_cut_less Ball_def Bex_def iT_iff iFROM_inext)
apply (rule_tac t="Suc (t * k + k - 2)" and s="t * k + k - Suc 0" in subst, simp)
apply (rule iffI)
 apply (elim exE conjE, rename_tac i)
 apply (case_tac "i = t * k")
  apply (rule disjI1)
  apply simp
  apply (rule_tac x="t * k + k" in exI)
  apply force
 apply (rule disjI2)
 apply (rule_tac x=i in exI)
 apply (case_tac "i = Suc (t * k)")
  apply simp
  apply (case_tac "Suc (t * k) < t * k + k - Suc 0")
   apply (clarsimp simp: mod_Suc)
   apply (case_tac "k = Suc (Suc 0)", simp)
   apply simp
   apply (rule_tac x="t * k + k" in exI)
   apply force
  apply clarsimp
  apply (subgoal_tac "k = Suc (Suc 0)")
   prefer 2
   apply simp
  apply (simp add: mod_Suc)
  apply (simp add: mult_2_right[symmetric] numeral_2_eq_2 del: mult_Suc_right)
  apply (rule_tac x="t * k + k" in exI)
  apply simp
 apply simp
 apply (subgoal_tac "Suc (t * k) \<le> i")
  prefer 2
  apply (rule ccontr, simp)
 apply simp
 apply (case_tac "i < t * k + k - Suc 0")
  apply clarsimp
  apply (subgoal_tac "0 < i mod k")
   prefer 2
   apply (simp add: mult.commute[of t])
   apply (rule between_imp_mod_gr0[OF Suc_le_lessD], simp+)
  apply (rule conjI)
   apply (rule_tac x="t * k + k" in exI)
   apply force
  apply clarify
  apply (simp add: mult.commute[of t])
  apply (rule between_imp_mod_gr0[OF Suc_le_lessD], assumption)
  apply simp
 apply clarsimp
 apply (subgoal_tac "Suc (Suc 0) < k")
  prefer 2
  apply simp
 apply (simp add: mod_0_imp_mod_pred)
 apply (rule conjI, blast)
 apply clarify
 apply (simp add: mult.commute[of t])
 apply (rule between_imp_mod_gr0[OF Suc_le_lessD], assumption)
 apply simp
apply (simp add: mod_Suc)
apply (erule disjE)
 apply (clarsimp simp: mult.commute[of k] elim!: dvdE, rename_tac i)
 apply (subgoal_tac "t < i")
  prefer 2
  apply (rule ccontr)
  apply (simp add: linorder_not_less)
  apply (drule_tac i=i and k=k in mult_le_mono1)
  apply simp
 apply (rule_tac x="t * k" in exI)
 apply simp
 apply (subgoal_tac "t * k < t * k + k - Suc 0")
  prefer 2
  apply simp
 apply (clarsimp, rename_tac j)
 apply (drule_tac x=j in spec)
 apply (simp add: numeral_2_eq_2 Suc_diff_Suc)
 apply (drule mp)
  apply (rule order_trans, assumption)
  apply (drule_tac m=t and n=i in Suc_leI)
  apply (drule mult_le_mono1[of "Suc t"_ k])
  apply simp
 apply simp
apply (clarsimp, rename_tac i)
apply (case_tac "i = Suc (t * k)")
 apply (clarsimp, rename_tac i1)
 apply (rule_tac x="Suc (t * k)" in exI)
 apply simp
 apply (case_tac "k = Suc (Suc 0)", simp)
 apply (clarsimp simp: mult.commute[of k] elim!: dvdE, rename_tac q)
 apply (subgoal_tac "Suc (t * k) < t * k + k - Suc 0")
  prefer 2
  apply simp
 apply (clarsimp elim!: dvdE, rename_tac j)
 apply (drule_tac x=j in spec)
 apply (simp add: numeral_3_eq_3 Suc_diff_Suc)
 apply (subgoal_tac "t * k + k \<le> q * k")
  prefer 2
  apply (rule less_mod_eq_imp_add_divisor_le)
   apply (rule Suc_le_lessD, simp)
  apply simp
 apply simp
apply (clarsimp, rename_tac i1)
apply (rule_tac x=i in exI)
apply (simp add: numeral_2_eq_2 Suc_diff_Suc)
apply (case_tac "i1 = Suc i")
 apply simp
 apply (case_tac "Suc (i mod k) = k")
  apply simp
  apply (subgoal_tac "i \<le> t * k + k - Suc 0")
   prefer 2
   apply (rule ccontr)
   apply (drule_tac x="t * k + k" in spec)
   apply (simp add: linorder_not_le)
   apply (drule pred_less_imp_le)+
   apply clarsimp
  apply simp
  apply (drule_tac x=i in le_imp_less_or_eq, erule disjE)
   apply simp
   apply (cut_tac b="k - Suc (Suc 0)" and m=k and k=t and a="Suc 0" and n=i in between_imp_mod_between)
   apply (simp add: mult.commute[of k])+
   apply (clarsimp elim!: dvdE)+
apply (rename_tac q)
apply (simp add: mult.commute[of k])
apply (subgoal_tac "Suc t \<le> q")
 prefer 2
 apply (rule Suc_leI)
 apply (rule mult_less_cancel2[where k=k, THEN iffD1, THEN conjunct2])
 apply (rule Suc_le_lessD)
 apply simp
apply (frule mult_le_mono1[of "Suc t" _ k])
apply (simp add: add.commute[of k])
apply (intro conjI impI allI)
 apply force
apply (simp add: linorder_not_less)
apply (case_tac "i > t * k + k")
 apply (drule_tac x="t * k + k" in spec)
 apply simp
apply (case_tac "i = t * k + k", simp)
apply simp
done

lemma i_shrink_eq_NoMsg_iAll_finish_event_conv: "
  \<lbrakk> 1 < k; \<And>t. event t = (t mod k = k - 1); t0 = t * k \<rbrakk> \<Longrightarrow>
  ((s \<div>\<^sub>i k) t = \<NoMsg>) =
  (s t0 = \<NoMsg> \<and> (\<circle> t' t0 [0\<dots>]. (s t1 = \<NoMsg>. t1 \<U> t2 ([0\<dots>] \<oplus> t'). (event t2 \<and> s t2 = \<NoMsg>))))"
apply (simp add: i_shrink_eq_NoMsg_iAll_conv iT_add)
apply (unfold iTL_defs Ball_def Bex_def)
apply (simp add: iT_iff div_mult_cancel iFROM_cut_less iFROM_inext)
apply (subgoal_tac "t * k < t * k + k - Suc 0")
 prefer 2
 apply simp
apply (rule iffI)
 apply simp
 apply (rule_tac x="t * k + k - Suc 0" in exI)
 apply (simp add: mod_pred)
 apply (clarify, rename_tac t1)
 apply (drule Suc_leI[of "t * k"])
 apply (drule order_le_less[THEN iffD1], erule disjE)
  prefer 2
  apply simp
 apply (clarsimp simp: iIN_iff)
apply (clarify, rename_tac t1 t2)
apply (case_tac "t2 \<le> Suc (t * k)")
 apply (clarsimp simp: mod_Suc)
 apply (drule_tac s="Suc 0" in sym, drule_tac x="k - Suc 0" and f=Suc in arg_cong)
 apply (drule_tac y=t1 in order_le_imp_less_or_eq, erule disjE)
  apply (drule_tac n=t1 in Suc_leI)
  apply simp
 apply simp
apply clarsimp
apply (drule_tac x=t1 in spec)
apply (simp add: iIN_iff linorder_not_le)
apply (drule_tac y=t1 in order_le_imp_less_or_eq, erule disjE)
 prefer 2
 apply simp
apply (subgoal_tac "t * k + k - Suc 0 \<le> t2")
 prefer 2
 apply (rule le_diff_conv[THEN iffD2])
 apply (rule less_mod_eq_imp_add_divisor_le, simp)
 apply (simp add: mod_Suc)
apply simp
apply (drule_tac x="t * k + k - Suc 0" and y=t2 in order_le_imp_less_or_eq, erule disjE)
 prefer 2
 apply (drule_tac t=t2 in sym, simp)
 apply (drule_tac x=t1 in order_le_imp_less_or_eq, erule disjE)
 apply simp+
done

lemma i_shrink_eq_Msg_iUntil_finish_event_conv: "
  \<lbrakk> 1 < k; m \<noteq> \<NoMsg>; \<And>t. event t = (t mod k = k - 1); t0 = t * k \<rbrakk> \<Longrightarrow>
  ((s \<div>\<^sub>i k) t = m) = (
  (\<not> event t1. t1 \<U> t2 ([0\<dots>] \<oplus> t0). event t2 \<and> s t2 = m) \<or>
  (\<not> event t1. t1 \<U> t2 ([0\<dots>] \<oplus> t0). (\<not> event t2 \<and> s t2 = m \<and> (
    \<circle> t' t2 [0\<dots>]. (s t3 = \<NoMsg>. t3 \<U> t4 ([0\<dots>] \<oplus> t'). event t4 \<and> s t4 = \<NoMsg>)))))"
apply (simp add: i_shrink_eq_Msg_iSince_conv split del: if_split)
apply (simp only: iTL_defs iT_add iT_cut_greater iT_cut_less Ball_def Bex_def iT_iff iFROM_inext)
apply (subgoal_tac "t * k < t * k + k - Suc 0")
 prefer 2
 apply simp
apply (rule iffI)
 apply (subgoal_tac "\<And>x. t * k \<le> x \<Longrightarrow> x < t * k + k - Suc 0 \<Longrightarrow> x mod k \<noteq> k - Suc 0")
  prefer 2
  apply (rule less_imp_neq)
  apply (rule le_pred_imp_less, simp)
  apply (simp only: mult.commute[of t k])
  apply (rule between_imp_mod_le[of "k - Suc 0 - Suc 0" k t])
  apply (simp split del: if_split)+
 apply (elim exE conjE, rename_tac t1)
 apply (drule_tac x=t1 in order_le_imp_less_or_eq, erule disjE)
  prefer 2
  apply (rule disjI1)
  apply (rule_tac x=t1 in exI)
  apply (clarsimp simp add: mod_pred iIN_iff)
 apply (rule disjI2)
 apply (rule_tac x=t1 in exI)
 apply (simp split del: if_split)
 apply (rule conjI)
  apply (rule_tac x="t * k + k - Suc 0" in exI)
  apply (clarsimp simp: mod_pred iIN_iff)
 apply (clarsimp simp: iIN_iff)
apply (erule disjE)
 apply (clarsimp, rename_tac t1)
 apply (drule_tac y=t1 in order_le_imp_less_or_eq, erule disjE)
  prefer 2
  apply (drule_tac t=t1 in sym, simp)
 apply (simp add: iIN_iff)
 apply (subgoal_tac "t1 \<le> t * k + k - Suc 0")
  prefer 2
  apply (rule ccontr)
  apply (drule_tac x="t * k + k - Suc 0" in spec)
  apply (simp add: mod_pred)
 apply (frule_tac a="t * k" and b=t1 and k="k - Suc 0" and m=k
   in le_mod_add_eq_imp_add_mod_le[OF less_imp_le, rule_format])
  apply (simp add: add.commute[of "t * k"] mod_pred)
 apply (rule_tac x=t1 in exI)
 apply simp
apply (clarsimp, rename_tac t1 t2)
apply (rule_tac x=t1 in exI)
apply (drule_tac y=t1 in order_le_imp_less_or_eq, erule disjE)
 prefer 2
 apply (drule_tac t=t1 in sym)
 apply (clarsimp simp: iIN_iff, rename_tac t3)
 apply (split if_split_asm)
  apply (subgoal_tac "t2 = Suc (t * k)")
   prefer 2
   apply simp
  apply (subgoal_tac "k = Suc (Suc 0)")
   prefer 2
   apply (simp add: mod_Suc)
  apply (simp add: mod_Suc)
 apply (simp add: iIN_iff)
 apply (subgoal_tac "t * k + k - Suc 0 \<le> t2")
  prefer 2
  apply (rule ccontr)
  apply (simp add: linorder_not_le)
  apply (drule_tac m=t2 in less_imp_le_pred)
  apply (simp only: mult.commute[of t])
  apply (frule_tac n=t2 in between_imp_mod_le[of "k - Suc (Suc 0)" k t _, OF diff_Suc_less, OF gr_implies_gr0])
   apply simp+
 apply (drule_tac x=t3 in spec)
 apply simp
 apply (drule_tac x=t3 in order_le_imp_less_or_eq)
 apply (drule_tac x="t * k + k - Suc 0" and y=t2 in order_le_imp_less_or_eq)
 apply (fastforce simp: numeral_2_eq_2 Suc_diff_Suc)
apply simp
apply (case_tac "Suc t1 = t2")
 apply (drule_tac t=t2 in sym)
 apply (simp add: iIN_iff numeral_2_eq_2 Suc_diff_Suc)
 apply (subgoal_tac "t1 \<le> t * k + k - Suc 0")
  prefer 2
  apply (rule ccontr)
  apply (drule_tac x="t * k + k - Suc 0" in spec)
  apply (simp add: mod_pred)
 apply (intro conjI impI)
 apply (subgoal_tac "Suc t1 = t * k + k - Suc 0", clarsimp)
 apply (subgoal_tac "t * k + (k - Suc 0) \<le> Suc t1")
  prefer 2
  apply (rule ccontr)
  apply (subgoal_tac "k - Suc 0 - Suc 0 < k")
   prefer 2
   apply simp
  apply (simp only: mult.commute[of t])
  apply (drule_tac n="Suc t1" in between_imp_mod_le[of "k - Suc 0 - Suc 0" k t])
  apply simp_all
apply (simp add: iIN_iff)
apply (subgoal_tac "t1 \<le> t * k + k - Suc 0")
 prefer 2
 apply (rule ccontr)
 apply (drule_tac x="t * k + k - Suc 0" in spec)
 apply (simp add: mod_pred)
apply (clarsimp, rename_tac t3)
apply (thin_tac "All (\<lambda>x. A x \<longrightarrow> B (x mod k))" for A B)
apply (drule_tac x=t3 in spec)
apply (subgoal_tac "t3 \<le> t2 \<Longrightarrow> s t3 = \<NoMsg>")
 prefer 2
 apply (drule_tac x=t3 and y=t2 in order_le_imp_less_or_eq, erule disjE)
  apply simp
 apply simp
apply (drule_tac P="t3 \<le> t2" in meta_mp)
 apply (subgoal_tac "t * k < t2")
  prefer 2
  apply (rule_tac y=t1 in less_trans, assumption+)
 apply (case_tac "t * k + (k - Suc 0) < t2")
  apply simp
 apply simp
apply (subgoal_tac "t * k + (k - Suc 0) \<le> t2")
 prefer 2
 apply (simp only: mult.commute[of t])
 apply (rule mult_divisor_le_mod_ge_imp_ge)
 apply simp_all
done

end
