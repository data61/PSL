(*  Title:      AF_Stream.thy
    Date:       Jan 2007
    Author:     David Trachtenherz
*)

section \<open>\textsc{AutoFocus} message streams\<close>

theory AF_Stream
imports ListSlice
begin

subsection \<open>Basic definitions\<close>

subsubsection \<open>Time-synchronous streams\<close>

datatype 'a message_af = NoMsg | Msg 'a

notation (latex)
  NoMsg  ("\<NoMsg>") and
  Msg  ("\<Msg>")

text \<open>Abbreviation for finite streams\<close>
type_synonym 'a fstream_af = "'a message_af list"

text \<open>Abbreviation for infinite streams\<close>
type_synonym 'a istream_af = "'a message_af ilist"

lemma not_NoMsg_eq: "(m \<noteq> \<NoMsg>) = (\<exists>x. m = \<Msg> x)"
by (case_tac m, simp_all)

lemma not_Msg_eq: "(\<forall>x. m \<noteq> \<Msg> x) = (m = \<NoMsg>) "
by (case_tac m, simp_all)

primrec the_af :: "'a message_af \<Rightarrow> 'a"
  where "the_af (\<Msg> x) = x"

text \<open>
  By this definition one can determine,
  whether data elements of different data structures with messages,
  especially product types of arbitrary sizes and records,
  are pointwise equal to NoMsg, i.e., contain only NoMsg entries.\<close>

consts is_NoMsg :: "'a \<Rightarrow> bool"

overloading is_NoMsg \<equiv> "is_NoMsg :: 'a message_af \<Rightarrow> bool"
begin

primrec is_NoMsg :: "'a message_af \<Rightarrow> bool"
where
  "is_NoMsg \<NoMsg> = True"
| "is_NoMsg (\<Msg> x) = False"

end

overloading is_NoMsg \<equiv> "is_NoMsg :: ('a \<times> 'b) \<Rightarrow> bool"
begin

definition is_NoMsg_tuple_def  :
  "is_NoMsg (p::'a \<times> 'b) \<equiv> (is_NoMsg (fst p) \<and> is_NoMsg (snd p))"

end

overloading is_NoMsg \<equiv> "is_NoMsg :: 'a set \<Rightarrow> bool"
begin

definition is_NoMsg_set_def :
  "is_NoMsg (A::'a set) \<equiv> (\<forall>x\<in>A. is_NoMsg x)"

end


record SomeRecordExample =
  Field1 :: "nat message_af"
  Field2 :: "int message_af"
  Field3 :: "int message_af"
overloading is_NoMsg \<equiv> "is_NoMsg :: 'a SomeRecordExample_scheme \<Rightarrow> bool"
begin

definition is_NoMsg_SomeRecordExample_def :
  "is_NoMsg (r:: 'a SomeRecordExample_scheme) \<equiv>
    Field1 r = \<NoMsg> \<and> Field2 r = \<NoMsg> \<and> Field3 r = \<NoMsg>"

end

definition is_Msg :: "'a \<Rightarrow> bool"
  where "is_Msg x \<equiv> (\<not> is_NoMsg x)"

lemma is_NoMsg_message_af_conv: "is_NoMsg m = (case m of \<NoMsg> \<Rightarrow> True | \<Msg> x \<Rightarrow> False)"
by (case_tac m, simp+)

lemma is_NoMsg_message_af_conv2: "is_NoMsg m = (m = \<NoMsg>)"
by (case_tac m, simp+)

lemma is_Msg_message_af_conv: "is_Msg m = (case m of \<NoMsg> \<Rightarrow> False | \<Msg> x \<Rightarrow> True)"
by (unfold is_Msg_def, case_tac m, simp+)

lemma is_Msg_message_af_conv2: "is_Msg m = (m \<noteq> \<NoMsg>)"
by (unfold is_Msg_def, case_tac m, simp+)


text \<open>Collection for definitions for \<open>is_NoMsg\<close>.\<close>

named_theorems is_NoMsg_defs

declare
  is_NoMsg_tuple_def[is_NoMsg_defs]
  is_NoMsg_set_def [is_NoMsg_defs]
  is_NoMsg_SomeRecordExample_def[is_NoMsg_defs]
  is_Msg_def[is_NoMsg_defs]

lemma not_is_NoMsg: "(\<not> is_NoMsg m) = is_Msg m"
by (simp add: is_NoMsg_defs)

lemma not_is_Msg: "(\<not> is_Msg m) = is_NoMsg m"
by (simp add: is_NoMsg_defs)

lemma "is_NoMsg (\<NoMsg>::(nat message_af))"
by simp

lemma "is_NoMsg (\<NoMsg>::(nat message_af), \<NoMsg>::(nat message_af))"
by (simp add: is_NoMsg_defs)

lemma "is_NoMsg (\<NoMsg>::(nat message_af), \<NoMsg>::(nat message_af), \<NoMsg>::(nat message_af))"
by (simp add: is_NoMsg_defs)

lemma "is_Msg (\<NoMsg>::(nat message_af), \<Msg> (1::nat), \<NoMsg>::(nat message_af))"
by (simp add: is_NoMsg_defs)

lemma "is_NoMsg {\<NoMsg>::(nat message_af), \<NoMsg>}"
by (simp add: is_NoMsg_defs)

lemma "is_Msg {\<NoMsg>::(nat message_af), \<Msg> 1}"
by (simp add: is_NoMsg_defs)

lemma "is_NoMsg \<lparr> Field1 = \<NoMsg>, Field2 = \<NoMsg>, Field3 = \<NoMsg> \<rparr>"
by (simp add: is_NoMsg_defs)

lemma "is_Msg  \<lparr> Field1 = \<NoMsg>, Field2 = Msg 1, Field3 = \<NoMsg> \<rparr>"
by (simp add: is_NoMsg_defs)


subsubsection \<open>Time abstraction\<close>

(* Time abstraction:
   Extracts non-empty messages from a stream =
   time abstraction for time-synchronous streams*)
primrec untime :: "'a fstream_af \<Rightarrow> 'a list" (*("\<registered>_" 100)*)
where
  "untime [] = []"
| "untime (x#xs) =
    (if x = \<NoMsg>
     then (untime xs)
     else (the_af x) # (untime xs))"

lemma untime_eq_filter[rule_format]: "
  map (\<lambda>x. \<Msg> x) (untime s) = filter (\<lambda>x. x \<noteq> \<NoMsg>) s"
apply (induct s, simp)
apply (case_tac a, simp_all)
done

text \<open>The following lemma involves @{term the_af} function
  and thus is some more limited than the previous lemma\<close>
corollary untime_eq_filter2[rule_format]: "
  untime s = map (\<lambda>x. the_af x) (filter (\<lambda>x. x \<noteq> \<NoMsg>) s)"
by (induct s, simp_all)


definition untime_length :: "'a fstream_af \<Rightarrow> nat"
  where "untime_length s \<equiv> length (untime s)"

primrec untime_length_cnt :: "'a fstream_af \<Rightarrow> nat"
where
  "untime_length_cnt [] = 0"
| "untime_length_cnt (x # xs) =
    (if x = \<NoMsg> then 0 else Suc 0) + untime_length_cnt xs"

lemma untime_length_eq_untime_length_cnt: "
  untime_length s = untime_length_cnt s"
by (induct s, simp_all add: untime_length_def)

definition untime_length_filter :: "'a fstream_af \<Rightarrow> nat"
  where "untime_length_filter s \<equiv> length (filter (\<lambda>x. x \<noteq> \<NoMsg>) s)"

lemma untime_length_filter_eq_untime_length: "
  untime_length_filter s = untime_length s"
apply (unfold untime_length_def untime_length_filter_def)
apply (simp add: untime_eq_filter2)
done

lemma untime_empty_conv: "(untime s = []) = (\<forall>n<length s. s ! n = \<NoMsg>)"
apply (induct s)
 apply simp
apply (force simp add: nth.simps split: nat.split)
done

lemma untime_not_empty_conv: "(untime s \<noteq> []) = (\<exists>n<length s. s ! n \<noteq> \<NoMsg>)"
by (simp add: untime_empty_conv)

corollary untime_empty_imp_NoMsg[rule_format]: "
  \<lbrakk> untime s = []; n < length s \<rbrakk> \<Longrightarrow> s ! n = \<NoMsg>"
by (rule untime_empty_conv[THEN iffD1, rule_format])


lemma untime_nth_eq_filter: "
  n < untime_length s \<Longrightarrow>
  \<Msg> (untime s ! n) = (filter (\<lambda>x. x \<noteq> \<NoMsg>) s) ! n"
by (simp add: untime_eq_filter[symmetric] untime_length_def)

corollary untime_nth_eq_filter2: "
  n < untime_length s \<Longrightarrow>
  untime s ! n = the_af ((filter (\<lambda>x. x \<noteq> \<NoMsg>) s) ! n)"
by (simp add: untime_length_def untime_nth_eq_filter[symmetric])


lemma untime_hd_eq_filter_hd: "
  untime s \<noteq> [] \<Longrightarrow>
  \<Msg> (hd (untime s)) = hd (filter (\<lambda>x. x \<noteq> \<NoMsg>) s)"
by (simp add: untime_eq_filter[symmetric] hd_eq_first[symmetric])

corollary untime_hd_eq_filter_hd2: "
  untime s \<noteq> [] \<Longrightarrow>
  hd (untime s) = the_af (hd (filter (\<lambda>x. x \<noteq> \<NoMsg>) s))"
by (simp add: untime_hd_eq_filter_hd[symmetric])


lemma untime_last_eq_filter_last: "
  untime s \<noteq> [] \<Longrightarrow>
  \<Msg> (last (untime s)) = last (filter (\<lambda>x. x \<noteq> \<NoMsg>) s)"
by (simp add: untime_eq_filter[symmetric] last_nth)

corollary untime_last_eq_filter_last2: "
  untime s \<noteq> [] \<Longrightarrow>
  last (untime s) = the_af (last (filter (\<lambda>x. x \<noteq> \<NoMsg>) s))"
by (simp add: untime_last_eq_filter_last[symmetric])


subsection \<open>Expanding and compressing lists and streams\<close>

subsubsection \<open>Expanding message streams\<close>

primrec f_expand :: "'a fstream_af \<Rightarrow> nat \<Rightarrow> 'a fstream_af" (infixl "\<odot>\<^sub>f" 100)
where
  f_expand_Nil: "[] \<odot>\<^sub>f k = []"
| f_expand_Cons: "(x # xs) \<odot>\<^sub>f k =
    (if 0 < k then x # \<NoMsg>\<^bsup>k - Suc 0\<^esup> @ (xs \<odot>\<^sub>f k) else [])"

definition i_expand :: "'a istream_af \<Rightarrow> nat \<Rightarrow> 'a istream_af" (infixl "\<odot>\<^sub>i" 100)
where
  "i_expand \<equiv> \<lambda>f k n.
   (if k = 0 then \<NoMsg> else
    if n mod k = 0 then f (n div k) else \<NoMsg>)"

primrec f_expand_Suc :: "'a fstream_af \<Rightarrow> nat \<Rightarrow> 'a fstream_af" (infixl "\<odot>\<^bsub>fSuc\<^esub>" 100)
where
  "f_expand_Suc [] k = []"
| "f_expand_Suc (x # xs) k = x # \<NoMsg>\<^bsup>k\<^esup> @ (f_expand_Suc xs k)"

definition i_expand_Suc :: "'a istream_af \<Rightarrow> nat \<Rightarrow> 'a istream_af" (infixl "\<odot>\<^bsub>iSuc\<^esub>" 100)
  where "i_expand_Suc \<equiv> \<lambda>f k n. if n mod (Suc k) = 0 then f (n div (Suc k)) else \<NoMsg>"

notation
  f_expand  (infixl "\<odot>" 100) and
  i_expand  (infixl "\<odot>" 100)


lemma length_f_expand_Suc[simp]: "length (f_expand_Suc xs k) = length xs * Suc k"
by (induct xs, simp+)

lemma i_expand_if: "
  f \<odot>\<^sub>i k = (if k = 0 then (\<lambda>n. \<NoMsg>) else
    (\<lambda>n. if n mod k = 0 then f (n div k) else \<NoMsg>))"
by (simp add: i_expand_def ilist_eq_iff)

lemma f_expand_one: "0 < k \<Longrightarrow> [a] \<odot>\<^sub>f k = a # \<NoMsg>\<^bsup>k - Suc 0\<^esup>"
by simp

lemma f_expand_0[simp]: "xs \<odot>\<^sub>f 0 = []"
by (induct xs, simp+)
corollary f_expand_0_is_zero_element: "xs \<odot>\<^sub>f 0 = ys \<odot>\<^sub>f 0"
by simp
lemma i_expand_0[simp]: "f \<odot>\<^sub>i 0 = (\<lambda>n. \<NoMsg>)"
by (simp add: i_expand_def)
corollary i_expand_0_is_zero_element: "f \<odot>\<^sub>i 0 = g \<odot>\<^sub>i 0"
by simp

lemma f_expand_gr0_f_expand_Suc: "0 < k \<Longrightarrow> xs \<odot>\<^sub>f k = f_expand_Suc xs (k - Suc 0)"
by (induct xs, simp+)
lemma i_expand_gr0_i_expand_Suc: "0 < k \<Longrightarrow> f \<odot>\<^sub>i k = i_expand_Suc f (k - Suc 0)"
by (simp add: i_expand_def i_expand_Suc_def ilist_eq_iff)
lemma i_expand_gr0: "
  0 < k \<Longrightarrow> f \<odot>\<^sub>i k = (\<lambda>n. if n mod k = 0 then f (n div k) else \<NoMsg>)"
by (simp add: i_expand_if)
lemma f_expand_1[simp]: "xs \<odot>\<^sub>f Suc 0 = xs"
by (induct xs, simp+)
lemma i_expand_1[simp]: "f \<odot>\<^sub>i Suc 0 = f"
by (simp add: i_expand_gr0)

lemma f_expand_length[simp]: "length (xs \<odot>\<^sub>f k) = length xs * k"
apply (case_tac k, simp)
apply (simp add: f_expand_gr0_f_expand_Suc)
done

lemma f_expand_empty_conv: "(xs \<odot>\<^sub>f k = []) = (xs = [] \<or> k = 0)"
by (simp add: length_0_conv[symmetric] del: length_0_conv)
lemma f_expand_not_empty_conv: "(xs \<odot>\<^sub>f k \<noteq> []) = (xs \<noteq> [] \<and> 0 < k)"
by (simp add: f_expand_empty_conv)

lemma f_expand_Cons: "
  0 < k \<Longrightarrow> (x # xs) \<odot>\<^sub>f k = x # \<NoMsg>\<^bsup>k - Suc 0\<^esup> @ (xs \<odot>\<^sub>f k)"
by simp
lemma f_expand_append[simp]: "\<And>ys. (xs @ ys) \<odot>\<^sub>f k = (xs \<odot>\<^sub>f k) @ (ys \<odot>\<^sub>f k)"
apply (case_tac "k = 0", simp)
apply (induct xs, simp+)
done

lemma f_expand_snoc: "
  0 < k \<Longrightarrow> (xs @ [x]) \<odot>\<^sub>f k = xs \<odot>\<^sub>f k @ x # replicate (k - Suc 0) \<NoMsg>"
by simp

lemma f_expand_nth_mult: "\<And>n.
  \<lbrakk> n < length xs; 0 < k \<rbrakk> \<Longrightarrow> (xs \<odot>\<^sub>f k) ! (n * k) = xs ! n"
apply (induct xs)
 apply simp
apply (case_tac n, simp)
apply (simp add: nth_append append_Cons[symmetric] del: append_Cons)
done

lemma i_expand_nth_mult: "0 < k \<Longrightarrow> (f \<odot>\<^sub>i k) (n * k) = f n"
by (simp add: i_expand_gr0)

lemma f_expand_nth_if: "\<And>n.
  n < length xs * k \<Longrightarrow>
  (xs \<odot>\<^sub>f k) ! n = (if n mod k = 0 then xs ! (n div k) else \<NoMsg>)"
apply (case_tac "k = 0", simp)
apply (simp, intro conjI impI)
 apply (clarsimp simp: f_expand_nth_mult mult.commute[of k] elim!: dvdE)
apply (induct xs, simp)
apply (simp add: nth_append append_Cons[symmetric] del: append_Cons)
apply (intro conjI impI)
 apply (simp add: nth_Cons')
apply (case_tac "length xs = 0", simp)
apply (simp add: add.commute[of k] diff_less_conv[symmetric] mod_diff_self2)
done

corollary f_expand_nth_mod_eq_0: "
  \<lbrakk> n < length xs * k; n mod k = 0 \<rbrakk> \<Longrightarrow> (xs \<odot>\<^sub>f k) ! n = xs ! (n div k)"
by (simp add: f_expand_nth_if)

corollary f_expand_nth_mod_neq_0: "
  \<lbrakk> n < length xs * k; 0 < n mod k \<rbrakk> \<Longrightarrow> (xs \<odot>\<^sub>f k) ! n = \<NoMsg>"
by (simp add: f_expand_nth_if)

lemma f_expand_nth_0_upto_k_minus_1_if: "
  \<lbrakk> t < length xs; n = t * k + i; i < k \<rbrakk> \<Longrightarrow>
  (xs \<odot>\<^sub>f k) ! n = (if i = 0 then xs ! t else \<NoMsg>)"
apply (subst f_expand_nth_if)
 apply (drule Suc_leI[of t])
 apply (drule mult_le_mono1[of _ _ k])
 apply simp+
done


lemma f_expand_take_mult: "xs \<odot>\<^sub>f k \<down> (n * k) = (xs \<down> n) \<odot>\<^sub>f k"
apply (clarsimp simp add: list_eq_iff min_def)
apply (rename_tac i)
apply (case_tac "\<not> i < n * k", simp)
apply (subgoal_tac "i < length xs * k")
 prefer 2
 apply (rule_tac y="n * k" in order_le_less_trans, simp+)
apply (clarsimp simp: f_expand_nth_if elim!: dvdE)
done

lemma f_expand_take_mod: "
  n mod k = 0 \<Longrightarrow> xs \<odot>\<^sub>f k \<down> n = xs \<down> (n div k) \<odot>\<^sub>f k"
  by (clarsimp simp: mult.commute[of k] f_expand_take_mult elim!: dvdE)

lemma f_expand_drop_mult: "xs \<odot>\<^sub>f k \<up> (n * k) = (xs \<up> n) \<odot>\<^sub>f k"
apply (insert arg_cong[OF append_take_drop_id, of "\<lambda>x. x \<odot>\<^sub>f k" n xs])
apply (drule ssubst[OF append_take_drop_id, of _ "xs \<odot>\<^sub>f k" "n * k"])
apply (simp only: f_expand_append)
apply (simp only: f_expand_take_mult)
apply simp
done

lemma f_expand_drop_mod: "
  n mod k = 0 \<Longrightarrow> xs \<odot>\<^sub>f k \<up> n = xs \<up> (n div k) \<odot>\<^sub>f k"
  by (clarsimp simp: mult.commute[of k] f_expand_drop_mult elim!: dvdE)

lemma f_expand_take_mult_Suc: "
  \<lbrakk> n < length xs; i < k \<rbrakk> \<Longrightarrow>
  xs \<odot>\<^sub>f k \<down> (n * k + Suc i) = (xs \<down> n) \<odot>\<^sub>f k @ (xs ! n # \<NoMsg>\<^bsup>i\<^esup>)"
apply (subgoal_tac "n * k + Suc i \<le> length xs * k")
 prefer 2
 apply (drule Suc_leI[of n])
 apply (drule mult_le_mono1[of "Suc n" _ k])
 apply simp
apply (clarsimp simp: list_eq_iff min_eqR nth_append f_expand_nth_if min_def nth_Cons' elim!: dvdE)
apply (simp add: mult.commute[of k] linorder_not_less)
apply (drule_tac n=ka in le_neq_implies_less, simp+)
apply (drule_tac n=ka in Suc_leI)
apply (drule_tac j=ka in mult_le_mono1[of _ _ k])
apply simp
done

lemma f_expand_take_Suc: "
  n < length xs * k \<Longrightarrow>
  xs \<odot>\<^sub>f k \<down> Suc n = (xs \<down> (n div k)) \<odot>\<^sub>f k @ (xs ! (n div k) # \<NoMsg>\<^bsup>n mod k\<^esup>)"
apply (case_tac "k = 0", simp)
apply (insert f_expand_take_mult_Suc[of "n div k" xs "n mod k" k])
apply (simp add: div_less_conv)
done

lemma i_expand_nth_if: "
  0 < k \<Longrightarrow> (f \<odot>\<^sub>i k) n = (if n mod k = 0 then f (n div k) else \<NoMsg>)"
by (simp add: i_expand_gr0)
corollary i_expand_nth_mod_eq_0: "
  \<lbrakk> 0 < k; n mod k = 0 \<rbrakk> \<Longrightarrow> (f \<odot>\<^sub>i k) n = f (n div k)"
by (simp add: i_expand_gr0)
corollary i_expand_nth_mod_neq_0: "
  0 < n mod k \<Longrightarrow> (f \<odot>\<^sub>i k) n = \<NoMsg>"
apply (case_tac "k = 0", simp)
apply (simp add: i_expand_gr0)
done

lemma i_expand_nth_0_upto_k_minus_1_if: "
  \<lbrakk> n = t * k + i; i < k \<rbrakk> \<Longrightarrow>
  (f \<odot>\<^sub>i k) n = (if i = 0 then f t else \<NoMsg>)"
by (simp add: i_expand_nth_if)

lemma i_expand_i_take_mult: "f \<odot>\<^sub>i k \<Down> (n * k) = (f \<Down> n) \<odot>\<^sub>f k"
apply (case_tac "k = 0", simp)
apply (clarsimp simp: list_eq_iff i_expand_nth_if f_expand_nth_if elim!: dvdE)
done

lemma i_expand_i_take_mod: "
  n mod k = 0 \<Longrightarrow> f \<odot>\<^sub>i k \<Down> n = f \<Down> (n div k) \<odot>\<^sub>f k"
  by (clarsimp simp: mult.commute[of k] i_expand_i_take_mult elim!: dvdE)

lemma i_expand_i_drop_mult: "(f \<odot>\<^sub>i k) \<Up> (n * k) = (f \<Up> n) \<odot>\<^sub>i k"
apply (case_tac "k = 0", simp)
apply (clarsimp simp: ilist_eq_iff i_expand_nth_if)
done

lemma i_expand_i_drop_mod: "
  n mod k = 0 \<Longrightarrow> f \<odot>\<^sub>i k \<Up> n = f \<Up> (n div k) \<odot>\<^sub>i k"
  by (clarsimp simp: mult.commute[of k] i_expand_i_drop_mult elim!: dvdE)

lemma i_expand_i_take_mult_Suc: "
  i < k \<Longrightarrow> f \<odot>\<^sub>i k \<Down> (n * k + Suc i) = (f \<Down> n) \<odot>\<^sub>f k @ (f n # \<NoMsg>\<^bsup>i\<^esup>)"
apply (clarsimp simp: list_eq_iff, rename_tac i')
apply (clarsimp simp: i_expand_nth_if f_expand_nth_if nth_append nth_Cons' elim!: dvdE)
apply (simp add: linorder_not_less mult.commute[of k])
apply (drule_tac n=ka in le_neq_implies_less, simp+)
apply (drule_tac n=ka in Suc_leI)
apply (drule_tac j=ka in mult_le_mono1[of _ _ k])
apply simp
done

lemma i_expand_i_take_Suc: "
  0 < k \<Longrightarrow> f \<odot>\<^sub>i k \<Down> Suc n = (f \<Down> (n div k)) \<odot>\<^sub>f k @ (f (n div k) # \<NoMsg>\<^bsup>n mod k\<^esup>)"
apply (insert i_expand_i_take_mult_Suc[of "n mod k" k "n div k" f])
apply simp
done

lemma f_expand_nth_interval_eq_nth_append_replicate_NoMsg[rule_format]: "
  \<lbrakk> 0 < k; t < length xs; t * k \<le> t1; t1 \<le> t * k + k - Suc 0 \<rbrakk> \<Longrightarrow>
  xs \<odot>\<^sub>f k \<down> Suc t1 \<up> (t * k) = xs ! t # \<NoMsg>\<^bsup>t1 - t * k\<^esup>"
apply (rule_tac t="Suc t1" and s="t * k + Suc (t1 - t * k)" in subst, simp)
apply (subst f_expand_take_mult_Suc)
apply simp+
done

lemma f_expand_nth_interval_eq_replicate_NoMsg: "
  \<lbrakk> 0 < k; t * k < t1; t1 \<le> t2; t2 \<le> t * k + k; t2 \<le> length xs * k\<rbrakk> \<Longrightarrow>
  xs \<odot>\<^sub>f k \<down> t2 \<up> t1 = \<NoMsg>\<^bsup>t2 - t1\<^esup>"
apply (clarsimp simp: list_eq_iff min_eqR f_expand_nth_if elim!: dvdE, rename_tac i q)
apply (drule_tac i=i and k=t1 in add_less_mono2, simp)
apply (drule_tac i="t * k" and j=t1 and m=i in trans_less_add1)
apply (drule_tac x="t * k" and y="t1 + i" and m=k in less_mod_eq_imp_add_divisor_le, simp)
apply simp
done


lemma i_expand_nth_interval_eq_nth_append_replicate_NoMsg[rule_format]: "
  \<lbrakk> 0 < k; t * k \<le> t1; t1 \<le> t * k + k - Suc 0 \<rbrakk> \<Longrightarrow>
  f \<odot>\<^sub>i k \<Down> Suc t1 \<up> (t * k) = f t # \<NoMsg>\<^bsup>t1 - t * k\<^esup>"
by (simp add: list_eq_iff Suc_diff_le i_expand_nth_if nth_Cons')

lemma i_expand_nth_interval_eq_replicate_NoMsg: "
  \<lbrakk> 0 < k; t * k < t1; t1 \<le> t2; t2 \<le> t * k + k \<rbrakk> \<Longrightarrow>
  f \<odot>\<^sub>i k \<Down> t2 \<up> t1 = \<NoMsg>\<^bsup>t2 - t1\<^esup>"
apply (clarsimp simp: list_eq_iff i_expand_nth_if add.commute[of k])
apply (drule_tac i=i and k=t1 in add_less_mono2, simp)
apply (drule_tac i="t * k" and j=t1 and m=i in trans_less_add1)
apply (drule_tac x="t * k" and y="t1 + i" and m=k in less_mod_eq_imp_add_divisor_le, simp)
apply simp
done


lemma f_expand_replicate_NoMsg[simp]: "(\<NoMsg>\<^bsup>n\<^esup>) \<odot>\<^sub>f k =  \<NoMsg>\<^bsup>n * k\<^esup>"
  by (clarsimp simp: list_eq_iff f_expand_nth_if elim!: dvdE)

lemma i_expand_const_NoMsg[simp]: "(\<lambda>n. \<NoMsg>) \<odot>\<^sub>i k = (\<lambda>n. \<NoMsg>)"
by (simp add: i_expand_def ilist_eq_iff)

lemma f_expand_assoc: "xs \<odot>\<^sub>f a \<odot>\<^sub>f b = xs \<odot>\<^sub>f (a * b)"
apply (induct xs)
 apply simp
apply (simp add: replicate_add[symmetric] diff_mult_distrib)
done

lemma i_expand_assoc: "f \<odot>\<^sub>i a \<odot>\<^sub>i b = f \<odot>\<^sub>i (a * b)"
by (fastforce simp: i_expand_def ilist_eq_iff)

lemma f_expand_commute: "xs \<odot>\<^sub>f a \<odot>\<^sub>f b = xs \<odot>\<^sub>f b \<odot>\<^sub>f a"
by (simp add: f_expand_assoc mult.commute[of b])

lemma i_expand_commute: "f \<odot>\<^sub>i a \<odot>\<^sub>i b = f \<odot>\<^sub>i b \<odot>\<^sub>i a"
by (simp add: i_expand_assoc mult.commute[of b])


lemma i_expand_i_append: "(xs \<frown> f) \<odot>\<^sub>i k = xs \<odot>\<^sub>f k \<frown> (f \<odot>\<^sub>i k)"
apply (case_tac "k = 0", simp)
apply (clarsimp simp add: ilist_eq_iff i_expand_gr0 i_append_nth)
apply (case_tac "x < length xs * k")
 apply (frule_tac n=x and k="length xs" in div_less_conv[THEN iffD2, of k, rule_format], simp)
 apply (simp add: f_expand_nth_if)
apply (simp add: linorder_not_less)
apply (frule div_le_mono[of _ _ k])
apply (simp add: mod_diff_mult_self1 div_diff_mult_self1)
done

lemma f_expand_eq_conv: "
  0 < k \<Longrightarrow> (xs \<odot>\<^sub>f k = ys \<odot>\<^sub>f k) = (xs = ys)"
apply (rule iffI)
 apply (clarsimp simp: list_eq_iff, rename_tac i)
 apply (drule_tac x="i * k" in spec)
 apply (simp add: f_expand_nth_mult)
apply simp
done

lemma i_expand_eq_conv: "
  0 < k \<Longrightarrow> (f \<odot>\<^sub>i k = g \<odot>\<^sub>i k) = (f = g)"
apply (rule iffI)
 apply (clarsimp simp: ilist_eq_iff, rename_tac i)
 apply (drule_tac x="i * k" in spec)
 apply (simp add: i_expand_nth_mult)
apply simp
done

lemma f_expand_eq_conv': "
  (xs' \<odot>\<^sub>f k = xs) =
  (length xs' * k = length xs \<and>
  (\<forall>i<length xs. xs ! i = (if i mod k = 0 then xs' ! (i div k) else \<NoMsg>)))"
by (fastforce simp: list_eq_iff f_expand_nth_if)

lemma i_expand_eq_conv': "
  0 < k \<Longrightarrow> (f' \<odot>\<^sub>i k = f) =
  (\<forall>i. f i = (if i mod k = 0 then f' (i div k) else \<NoMsg>))"
by (fastforce simp: ilist_eq_iff i_expand_nth_if)


subsubsection \<open>Aggregating lists\<close>

definition f_aggregate :: "'a list \<Rightarrow> nat \<Rightarrow> ('a list \<Rightarrow> 'a) \<Rightarrow> 'a list"
  where "f_aggregate s k ag \<equiv> map ag (list_slice s k)"

definition i_aggregate :: "'a ilist \<Rightarrow> nat \<Rightarrow> ('a list \<Rightarrow> 'a) \<Rightarrow> 'a ilist"
  where "i_aggregate s k ag \<equiv> \<lambda>n. ag (s \<Up> (n * k) \<Down> k)"

lemma f_aggregate_0[simp]: "f_aggregate xs 0 ag = []"
by (simp add: f_aggregate_def list_slice_0)

lemma f_aggregate_1: "
  (\<And>x. ag [x] = x) \<Longrightarrow>
  f_aggregate xs (Suc 0) ag = xs"
by (simp add: list_eq_iff f_aggregate_def list_slice_1)

lemma f_aggregate_Nil[simp]: "f_aggregate [] k ag = []"
by (simp add: f_aggregate_def list_slice_Nil)

lemma f_aggregate_length[simp]: "length (f_aggregate xs k ag) = length xs div k"
by (simp add: f_aggregate_def list_slice_length)

lemma f_aggregate_empty_conv: "
  0 < k \<Longrightarrow> (f_aggregate xs k ag = []) = (length xs < k)"
by (simp add: length_0_conv[symmetric] div_eq_0_conv' del: length_0_conv )

lemma f_aggregate_one: "
  \<lbrakk> 0 < k; length xs = k \<rbrakk> \<Longrightarrow> f_aggregate xs k ag = [ag xs]"
by (simp add: f_aggregate_def list_slice_def)

lemma f_aggregate_Cons: "
  \<lbrakk> 0 < k; length xs = k \<rbrakk> \<Longrightarrow>
  f_aggregate (xs @ ys) k ag = ag xs # (f_aggregate ys k ag)"
by (simp add: f_aggregate_def list_slice_def)

lemma f_aggregate_eq_f_aggregate_take: "
  f_aggregate (xs \<down> (length xs div k * k)) k ag = f_aggregate xs k ag"
by (simp add: f_aggregate_def list_slice_eq_list_slice_take)

lemma f_aggregate_nth: "
  n < length xs div k \<Longrightarrow>
  (f_aggregate xs k ag) ! n = ag (xs \<up> (n * k) \<down> k)"
by (simp add: f_aggregate_def list_slice_length list_slice_nth)

lemma f_aggregate_nth_eq_sublist_list: "
  n < length xs div k \<Longrightarrow>
  (f_aggregate xs k ag) ! n = ag (sublist_list xs [n * k..<n * k + k])"
apply (frule less_div_imp_mult_add_divisor_le)
apply (simp add: f_aggregate_nth take_drop_eq_sublist_list)
done

lemma f_aggregate_take_nth: "
  \<And>xs m. \<lbrakk> n < length xs div k; n < m div k \<rbrakk> \<Longrightarrow>
  f_aggregate (xs \<down> m) k ag ! n = f_aggregate xs k ag ! n"
apply (simp add: f_aggregate_nth drop_take)
apply (drule_tac n=m in less_div_imp_mult_add_divisor_le)
apply (simp add: min_eqL)
done

lemma f_aggregate_hd: "
  \<lbrakk> 0 < k; k \<le> length xs \<rbrakk> \<Longrightarrow>
  hd (f_aggregate xs k ag) = ag (xs \<down> k)"
apply (drule div_le_mono[of _ _ k])
apply (simp add: Suc_le_eq)
apply (subst hd_eq_first[symmetric])
 apply (simp add: length_greater_0_conv[symmetric])
apply (simp add: f_aggregate_nth)
done

lemma f_aggregate_append_mod: "
  length xs mod k = 0 \<Longrightarrow>
  f_aggregate (xs @ ys) k ag =
  f_aggregate xs k ag @ f_aggregate ys k ag"
by (simp add: f_aggregate_def list_slice_append_mod)
lemma f_aggregate_append_mult: "
  length xs = m * k \<Longrightarrow>
  f_aggregate (xs @ ys) k ag =
  f_aggregate xs k ag @ f_aggregate ys k ag"
by (simp add: f_aggregate_append_mod)

lemma f_aggregate_snoc: "
  \<lbrakk> 0 < k; length ys = k; length xs mod k = 0 \<rbrakk> \<Longrightarrow>
  f_aggregate (xs @ ys) k ag = f_aggregate xs k ag @ [ag ys]"
by (simp add: f_aggregate_append_mod f_aggregate_one)

lemma f_aggregate_take: "
  f_aggregate (xs \<down> n) k ag = f_aggregate xs k ag \<down> (n div k)"
apply (case_tac "k = 0", simp)
apply (simp add: list_eq_iff)
apply (case_tac "length xs \<le> n")
 apply (simp add: min_eqL div_le_mono f_aggregate_nth)
apply (clarsimp simp: linorder_not_le min_eqR div_le_mono f_aggregate_nth drop_take)
apply (frule less_div_imp_mult_add_divisor_le)
apply (simp add: min_eqL)
apply (subgoal_tac "i < length xs div k")
 prefer 2
 apply (drule_tac y=n in order_le_less_trans, assumption)
 apply (drule_tac m="i * k + k" and k=k in div_le_mono[OF less_imp_le])
 apply simp
apply (simp add: f_aggregate_nth)
done

lemma f_aggregate_take_mult: "
  f_aggregate (xs \<down> (n * k)) k ag = f_aggregate xs k ag \<down> n"
by (simp add: f_aggregate_take)

lemma f_aggregate_drop_mult: "
  f_aggregate (xs \<up> (n * k)) k ag = f_aggregate xs k ag \<up> n"
by (simp add: list_eq_iff div_diff_mult_self1 f_aggregate_nth add_mult_distrib add.commute[of "n * k"])
lemma f_aggregate_drop_mod: "
  n mod k = 0 \<Longrightarrow> f_aggregate (xs \<up> n) k ag = f_aggregate xs k ag \<up> (n div k)"
  by (clarsimp simp: mult.commute[of k] f_aggregate_drop_mult elim!: dvdE)

lemma f_aggregate_assoc: "
  (\<And>xs. length xs mod a = 0 \<Longrightarrow> ag (f_aggregate xs a ag) = ag xs) \<Longrightarrow>
  f_aggregate (f_aggregate xs a ag) b ag = f_aggregate xs (a * b) ag"
apply (clarsimp simp add: list_eq_iff div_mult2_eq f_aggregate_nth, rename_tac i)
apply (simp add: take_drop f_aggregate_take_mult[symmetric])
apply (simp add: add_mult_distrib2 mult.commute[of _ a] f_aggregate_drop_mult[symmetric] mult.assoc[symmetric])
apply (drule_tac x="(xs \<down> (a * b + a * i * b) \<up> (a * i * b))" in meta_spec)
apply (subgoal_tac "a * b + a * i * b \<le> length xs")
 prefer 2
 apply (simp add: div_mult2_eq[symmetric])
 apply (drule_tac x=i in less_div_imp_mult_add_divisor_le)
 apply (simp add: mult.assoc[symmetric] mult.commute[of _ a] add.commute[of _ "a * b"])
apply (simp add: min_eqR)
done

lemma f_aggregate_commute: "
  \<lbrakk> \<And>xs. length xs mod a = 0 \<Longrightarrow> ag (f_aggregate xs a ag) = ag xs;
    \<And>xs. length xs mod b = 0 \<Longrightarrow> ag (f_aggregate xs b ag) = ag xs \<rbrakk> \<Longrightarrow>
  f_aggregate (f_aggregate xs a ag) b ag = f_aggregate (f_aggregate xs b ag) a ag"
by (simp add: f_aggregate_assoc mult.commute[of _ b])

lemma i_aggregate_0[simp]: "i_aggregate f 0 ag = (\<lambda>x. ag [])"
by (simp add: i_aggregate_def)
lemma i_aggregate_1: "(\<And>x. ag [x] = x) \<Longrightarrow> i_aggregate f (Suc 0) ag = f"
by (simp add: i_aggregate_def i_take_first)
lemma i_aggregate_nth: "i_aggregate f k ag n = ag (f \<Up> (n * k) \<Down> k)"
by (simp add: i_aggregate_def)
lemma i_aggregate_hd: "i_aggregate f k ag 0 = ag (f \<Down> k)"
by (simp add: i_aggregate_nth)

lemma i_aggregate_nth_eq_map: "i_aggregate f k ag n = ag (map f [n * k..<n * k + k])"
by (simp add: i_aggregate_nth i_take_drop_eq_map)

lemma i_aggregate_i_append_mod: "
  length xs mod k = 0 \<Longrightarrow>
  i_aggregate (xs \<frown> f) k ag = f_aggregate xs k ag \<frown> i_aggregate f k ag"
apply (clarsimp simp: ilist_eq_iff i_aggregate_nth i_append_nth f_aggregate_nth mult.commute[of k] diff_mult_distrib elim!: dvdE, rename_tac i n)
apply (drule_tac n=i in Suc_leI)
apply (drule mult_le_mono1[of _ _ k])
apply simp
done

lemma i_aggregate_i_append_mult: "
  length xs = m * k \<Longrightarrow>
  i_aggregate (xs \<frown> f) k ag = f_aggregate xs k ag \<frown> i_aggregate f k ag"
by (rule i_aggregate_i_append_mod, simp)

lemma i_aggregate_Cons: "
  \<lbrakk> 0 < k; length xs = k \<rbrakk> \<Longrightarrow>
  i_aggregate (xs \<frown> f) k ag = [ag xs] \<frown> (i_aggregate f k ag)"
apply (insert i_aggregate_i_append_mod[of xs k f ag], simp)
apply (simp add: f_aggregate_def list_slice_div_eq_1)
done

lemma i_aggregate_take_nth: "
  n < m div k \<Longrightarrow> f_aggregate (f \<Down> m) k ag ! n = i_aggregate f k ag n"
apply (simp add: f_aggregate_nth i_aggregate_nth)
apply (drule less_div_imp_mult_add_divisor_le)
apply (simp add: i_take_drop_map i_take_drop_eq_map take_map)
done

lemma i_aggregate_i_take: "
  f_aggregate (f \<Down> n) k ag = i_aggregate f k ag \<Down> (n div k)"
by (simp add: list_eq_iff i_aggregate_take_nth)

lemma i_aggregate_i_take_mult: "
  0 < k \<Longrightarrow> f_aggregate (f \<Down> (n * k)) k ag = i_aggregate f k ag \<Down> n"
by (simp add: i_aggregate_i_take)

lemma i_aggregate_i_drop_mult: "
  i_aggregate (f \<Up> (n * k)) k ag = i_aggregate f k ag \<Up> n"
by (simp add: ilist_eq_iff i_aggregate_nth add_mult_distrib)

lemma i_aggregate_i_drop_mod: "
  n mod k = 0 \<Longrightarrow>
  i_aggregate (f \<Up> n) k ag = i_aggregate f k ag \<Up> (n div k)"
  by (clarsimp simp: mult.commute[of k] i_aggregate_i_drop_mult ilist_eq_iff elim!: dvdE)

lemma i_aggregate_assoc: "
  \<lbrakk> 0 < a; 0 < b;
    \<And>xs. length xs mod a = 0 \<Longrightarrow> ag (f_aggregate xs a ag) = ag xs \<rbrakk> \<Longrightarrow>
  i_aggregate (i_aggregate f a ag) b ag = i_aggregate f (a * b) ag"
apply (simp add: ilist_eq_iff i_aggregate_nth)
apply (simp add: i_aggregate_i_drop_mult[symmetric] i_aggregate_i_take_mult[symmetric] mult.commute[of a] mult.assoc)
done

lemma i_aggregate_commute: "
  \<lbrakk> 0 < a; 0 < b;
    \<And>xs. length xs mod a = 0 \<Longrightarrow> ag (f_aggregate xs a ag) = ag xs;
    \<And>xs. length xs mod b = 0 \<Longrightarrow> ag (f_aggregate xs b ag) = ag xs \<rbrakk> \<Longrightarrow>
  i_aggregate (i_aggregate xs a ag) b ag = i_aggregate (i_aggregate xs b ag) a ag"
by (simp add: i_aggregate_assoc mult.commute[of _ b])


subsubsection \<open>Compressing message streams\<close>

text \<open>Determines the last non-empty message.\<close>
primrec last_message :: "'a fstream_af \<Rightarrow> 'a message_af"
where
  "last_message [] = \<NoMsg>"
| "last_message (x # xs) = (if last_message xs = \<NoMsg> then x else last_message xs)"

definition f_shrink :: "'a fstream_af \<Rightarrow> nat \<Rightarrow> 'a fstream_af" (infixl "\<div>\<^sub>f" 100)
  where "f_shrink xs k \<equiv> f_aggregate xs k last_message"

definition i_shrink :: "'a istream_af \<Rightarrow> nat \<Rightarrow> 'a istream_af" (infixl "\<div>\<^sub>i" 100)
  where "i_shrink f k \<equiv> i_aggregate f k last_message"

notation
  f_shrink  (infixl "\<div>" 100) and
  i_shrink  (infixl "\<div>" 100)


lemmas f_shrink_defs = f_shrink_def f_aggregate_def
lemmas i_shrink_defs = i_shrink_def i_aggregate_def

lemma last_message_Nil: "last_message [] = \<NoMsg>"
by simp

lemma last_message_one: "last_message [m] = m"
by simp


lemma last_message_replicate: "0 < n \<Longrightarrow> last_message (m\<^bsup>n\<^esup>) = m"
apply (induct n, simp)
apply (case_tac n, simp+)
done

lemma last_message_replicate_NoMsg: "last_message (\<NoMsg>\<^bsup>n\<^esup>) = \<NoMsg>"
apply (case_tac "n = 0", simp)
apply (simp add: last_message_replicate)
done

lemma last_message_Cons_NoMsg: "last_message (\<NoMsg> # xs) = last_message xs"
by simp

lemma last_message_append_one: "
  last_message (xs @ [m]) = (if m = \<NoMsg> then last_message xs else m)"
apply (induct xs, simp)
apply (case_tac "m = \<NoMsg>", simp+)
done

lemma last_message_append: "\<And>xs.
  last_message (xs @ ys) = (
  if last_message ys = \<NoMsg> then last_message xs else last_message ys)"
apply (induct ys, simp)
apply (drule_tac x="xs @ [a]" in meta_spec)
apply (simp add: last_message_append_one)
done

corollary last_message_append_replicate_NoMsg: "
  last_message (xs @ \<NoMsg>\<^bsup>n\<^esup>) = last_message xs"
by (simp add: last_message_append last_message_replicate_NoMsg)

lemma last_message_replicate_NoMsg_append: "
  last_message (\<NoMsg>\<^bsup>n\<^esup> @ xs) = last_message xs"
by (simp add: last_message_append last_message_replicate_NoMsg)

lemma last_message_NoMsg_conv: "
  (last_message xs = \<NoMsg>) = (\<forall>i<length xs. xs ! i = \<NoMsg>)"
apply (induct xs, simp)
apply (simp add: nth_Cons')
apply (safe, simp_all)
apply (rename_tac i)
apply (drule_tac x="Suc i" in spec)
apply simp
done

lemma last_message_not_NoMsg_conv: "
  (last_message xs \<noteq> \<NoMsg>) = (\<exists>i<length xs. xs ! i \<noteq> \<NoMsg>)"
by (simp add: last_message_NoMsg_conv)

lemma not_NoMsg_imp_last_message: "
  \<lbrakk> i < length xs; xs ! i \<noteq> \<NoMsg> \<rbrakk> \<Longrightarrow> last_message xs \<noteq> \<NoMsg>"
by (rule last_message_not_NoMsg_conv[THEN iffD2, OF exI, OF conjI])

lemma last_message_exists_nth: "
  last_message xs \<noteq> \<NoMsg> \<Longrightarrow>
  \<exists>i<length xs. last_message xs = xs ! i \<and> (\<forall>j<length xs. i < j \<longrightarrow> xs ! j = \<NoMsg>)"
apply (induct xs, simp)
apply (rename_tac a xs)
apply (case_tac "last_message xs = \<NoMsg>")
 apply (rule_tac x=0 in exI)
 apply clarsimp
 apply (rename_tac j, case_tac j, simp)
 apply (simp add: last_message_NoMsg_conv)
apply (rule ccontr)
apply (clarsimp, rename_tac i)
apply (drule_tac x="Suc i" in spec)
apply (clarsimp simp: nth_Cons')
done

lemma last_message_exists_nth': "
  last_message xs \<noteq> \<NoMsg> \<Longrightarrow> \<exists>i<length xs. last_message xs = xs ! i"
by (blast dest: last_message_exists_nth)

lemma last_messageI2_aux: "\<And>i.
  \<lbrakk> i < length xs; xs ! i \<noteq> \<NoMsg>;
    \<forall>j. i < j \<and> j < length xs \<longrightarrow> xs ! j = \<NoMsg> \<rbrakk> \<Longrightarrow>
  last_message xs = xs ! i"
apply (induct xs, simp)
apply (simp add: nth_Cons')
apply (case_tac i)
 apply simp
 apply (subgoal_tac "\<forall>j. j < length xs \<longrightarrow> xs ! j = \<NoMsg>")
  prefer 2
  apply (clarify, drule_tac x="Suc j" in spec)
  apply simp
 apply (simp add: last_message_NoMsg_conv)
apply clarsimp
apply (rename_tac i)
apply (intro conjI impI)
 apply (simp add: not_NoMsg_imp_last_message)
apply (subgoal_tac "\<forall>j. i < j \<and> j < length xs \<longrightarrow> xs ! j = \<NoMsg>")
 prefer 2
 apply (clarify, drule_tac x="Suc j" in spec)
 apply simp
apply simp
done

lemma last_messageI2: "
  \<lbrakk> i < length xs; xs ! i \<noteq> \<NoMsg>;
    \<And>j. \<lbrakk> i < j; j < length xs \<rbrakk> \<Longrightarrow> xs ! j = \<NoMsg> \<rbrakk> \<Longrightarrow>
  last_message xs = xs ! i"
by (blast intro: last_messageI2_aux)

lemma last_messageI: "
  \<lbrakk> m \<noteq> \<NoMsg>; i < length xs; xs ! i = m;
    \<And>j. \<lbrakk> i < j; j < length xs \<rbrakk> \<Longrightarrow> xs ! j = \<NoMsg> \<rbrakk> \<Longrightarrow>
  last_message xs = m"
by (blast intro: last_messageI2)

lemma last_message_Msg_eq_last: "
  \<lbrakk> xs \<noteq> []; last xs \<noteq> \<NoMsg> \<rbrakk> \<Longrightarrow> last_message xs = last xs"
by (simp add: last_nth last_messageI2)

lemma last_message_conv: "
  m \<noteq> \<NoMsg> \<Longrightarrow>
  (last_message xs = m) =
  (\<exists>i<length xs. xs ! i = m \<and> (\<forall>j<length xs. i < j \<longrightarrow> xs ! j = \<NoMsg>))"
apply (rule iffI)
 apply (cut_tac xs=xs in last_message_exists_nth, simp)
 apply clarify
 apply (rule_tac x=i in exI)
 apply simp
apply (clarsimp simp: last_messageI)
done

lemma last_message_conv_if: "
  (last_message xs = m) =
  (if m = \<NoMsg> then \<forall>i<length xs. xs ! i = \<NoMsg>
   else \<exists>i<length xs. xs ! i = m \<and> (\<forall>j<length xs. i < j \<longrightarrow> xs ! j = \<NoMsg>))"
by (simp add: last_message_NoMsg_conv last_message_conv)

lemma last_message_not_NoMsg_eq_conv: "
  \<lbrakk> last_message xs \<noteq> \<NoMsg>; last_message ys \<noteq> \<NoMsg> \<rbrakk> \<Longrightarrow>
  (last_message xs = last_message ys) =
  (\<exists>i j. i < length xs \<and> j < length ys \<and> xs ! i \<noteq> \<NoMsg> \<and>
         xs ! i = ys ! j \<and>
         (\<forall>n<length xs. i < n \<longrightarrow> xs ! n = \<NoMsg>) \<and>
         (\<forall>n<length ys. j < n \<longrightarrow> ys ! n = \<NoMsg>))"
apply (simp add: last_message_conv[where m="last_message ys"])
apply (frule last_message_exists_nth[of xs])
apply (frule last_message_exists_nth[of ys])
apply (rule iffI)
 apply (clarsimp, rename_tac i j)
 apply (rule_tac x=j in exI, simp)
 apply (rule_tac x=i in exI, simp)
apply (clarsimp, rename_tac i1 j1 i j)
apply (rule_tac x=i in exI, simp)
apply (subgoal_tac "last_message ys = ys ! j", simp)
apply (rule last_messageI2)
apply simp+
done

lemma f_shrink_0[simp]: "xs \<div>\<^sub>f 0 = []"
by (simp add: f_shrink_defs list_slice_0)

lemma f_shrink_1[simp]: "xs \<div>\<^sub>f Suc 0 = xs"
by (simp add: f_shrink_def f_aggregate_1)

lemma f_shrink_Nil[simp]: "[] \<div>\<^sub>f k = []"
by (simp add: f_shrink_def list_slice_Nil)

lemma f_shrink_length: "length (xs \<div>\<^sub>f k) = length xs div k"
by (simp add: f_shrink_def)

lemma f_shrink_empty_conv: "0 < k \<Longrightarrow> (xs \<div>\<^sub>f k = []) = (length xs < k)"
by (simp add: f_shrink_def f_aggregate_empty_conv)

lemma f_shrink_Cons: "
  \<lbrakk> 0 < k; length xs = k \<rbrakk> \<Longrightarrow> (xs @ ys) \<div>\<^sub>f k = last_message xs # (ys \<div>\<^sub>f k)"
by (simp add: f_shrink_def f_aggregate_Cons)

lemma f_shrink_one: "
  \<lbrakk> 0 < k; length xs = k \<rbrakk> \<Longrightarrow> xs \<div>\<^sub>f k = [last_message xs]"
by (simp add: f_shrink_def f_aggregate_one)


lemma f_shrink_eq_f_shrink_take: "
  xs \<down> (length xs div k * k) \<div>\<^sub>f k = xs \<div>\<^sub>f k"
by (simp add: f_shrink_defs list_slice_eq_list_slice_take)

lemma f_shrink_nth: "
  n < length xs div k \<Longrightarrow>
  (xs \<div>\<^sub>f k) ! n = last_message (xs \<up> (n * k) \<down> k)"
by (simp add: f_shrink_def f_aggregate_nth)

lemma f_shrink_nth_eq_sublist_list: "
  n < length xs div k \<Longrightarrow>
  (xs \<div>\<^sub>f k) ! n = last_message (sublist_list xs [n * k..<n * k + k])"
by (simp add: f_shrink_def f_aggregate_nth_eq_sublist_list)

lemma f_shrink_take_nth: "
  \<lbrakk> n < length xs div k; n < m div k \<rbrakk> \<Longrightarrow> (xs \<down> m) \<div>\<^sub>f k ! n = xs \<div>\<^sub>f k ! n"
by (simp add: f_shrink_def f_aggregate_take_nth)

lemma f_shrink_hd: "
  \<lbrakk> 0 < k; k \<le> length xs \<rbrakk> \<Longrightarrow> hd (xs \<div>\<^sub>f k) = last_message (xs \<down> k)"
by (simp add: f_shrink_def f_aggregate_hd)

lemma f_shrink_append_mod: "
  length xs mod k = 0 \<Longrightarrow> (xs @ ys) \<div>\<^sub>f k = xs \<div>\<^sub>f k @ (ys \<div>\<^sub>f k)"
by (simp add: f_shrink_defs list_slice_append_mod)

lemma f_shrink_append_mult: "
  length xs = m * k \<Longrightarrow> (xs @ ys) \<div>\<^sub>f k = xs \<div>\<^sub>f k @ (ys \<div>\<^sub>f k)"
by (simp add: f_shrink_append_mod)

lemma f_shrink_snoc: "
  \<lbrakk> 0 < k; length ys = k; length xs mod k = 0 \<rbrakk> \<Longrightarrow>
  (xs @ ys) \<div>\<^sub>f k = xs \<div>\<^sub>f k @ [last_message ys]"
by (simp add: f_shrink_append_mod f_shrink_one)

lemma f_shrink_last_message[rule_format]: "
  length xs mod k = 0 \<longrightarrow> last_message (xs \<div>\<^sub>f k) = last_message xs"
apply (case_tac "k = 0", simp)
apply (rule append_constant_length_induct[of k])
 apply simp
apply (simp add: f_shrink_Cons last_message_append)
done

lemma f_shrink_replicate: "m\<^bsup>n\<^esup> \<div>\<^sub>f k = m\<^bsup>n div k\<^esup>"
apply (case_tac "k = 0", simp)
apply (case_tac "n < k")
 apply (simp add: f_shrink_empty_conv)
apply (clarsimp simp: list_eq_iff f_shrink_length f_shrink_nth)
apply (rule last_message_replicate)
apply (clarsimp simp: min_def)
apply (drule mult_less_mono1[of _ "n div k" k], simp)
apply (simp add: div_mult_cancel)
done

lemma f_shrink_f_expand_id: "0 < k \<Longrightarrow> xs \<odot>\<^sub>f k \<div>\<^sub>f k = xs"
apply (simp add: list_eq_iff)
apply (simp add: f_shrink_length f_shrink_nth f_expand_drop_mult f_expand_take_mod drop_take_1 last_message_replicate_NoMsg)
done

lemma f_expand_f_shrink_id_take[rule_format]: "
  \<lbrakk> \<forall>i<length xs. 0 < i mod k \<longrightarrow> xs ! i = \<NoMsg> \<rbrakk> \<Longrightarrow>
  xs \<div>\<^sub>f k \<odot>\<^sub>f k = xs \<down> (length xs div k * k)"
apply (case_tac "k = 0", simp)
apply (induct xs rule: append_constant_length_induct[of k])
 apply (simp add: f_shrink_empty_conv[symmetric])
apply (drule meta_mp)
 apply clarify
 apply (drule_tac x="length xs + i" in spec, simp)
apply (simp add: f_shrink_append_mod)
apply (rule_tac t=xs and s="(xs ! 0) # replicate (k - Suc 0) \<NoMsg>" in subst)
 apply (simp (no_asm_simp) add: list_eq_iff nth_Cons')
 apply (clarify, rename_tac i)
 apply (drule_tac x=i in spec)
 apply (simp add: nth_append)
apply (simp (no_asm_simp) add: list_eq_iff)
apply (clarsimp simp: f_shrink_length f_expand_nth_if f_shrink_nth last_message_replicate_NoMsg nth_Cons')
done

corollary f_expand_f_shrink_id_mod_0: "
  \<lbrakk> length xs mod k = 0;
    \<And>i. \<lbrakk> i < length xs; 0 < i mod k \<rbrakk> \<Longrightarrow> xs ! i = \<NoMsg> \<rbrakk> \<Longrightarrow>
  xs \<div>\<^sub>f k \<odot>\<^sub>f k = xs"
by (clarsimp simp: f_expand_f_shrink_id_take)

lemma f_shrink_take: "
  xs \<down> n \<div>\<^sub>f k = xs \<div>\<^sub>f k \<down> (n div k)"
by (simp add: f_shrink_def f_aggregate_take)

lemma f_shrink_take_mult: "xs \<down> (n * k) \<div>\<^sub>f k = xs \<div>\<^sub>f k \<down> n"
by (simp add: f_shrink_def f_aggregate_take_mult)

lemma f_shrink_drop_mult: "xs \<up> (n * k) \<div>\<^sub>f k = xs \<div>\<^sub>f k \<up> n"
by (simp add: f_shrink_def f_aggregate_drop_mult)

lemma f_shrink_drop_mod: "
  n mod k = 0 \<Longrightarrow> xs \<up> n \<div>\<^sub>f k = xs \<div>\<^sub>f k \<up> (n div k)"
by (simp add: f_shrink_def f_aggregate_drop_mod)

lemma f_shrink_eq_conv: "
  (xs \<div>\<^sub>f k1 = ys \<div>\<^sub>f k2) =
  (length xs div k1 = length ys div k2 \<and>
  (\<forall>i<length xs div k1.
      last_message (xs \<up> (i * k1) \<down> k1) = last_message (ys \<up> (i * k2) \<down> k2)))"
apply (case_tac "k1 = 0")
 apply (simp add: eq_commute[of "[]"] length_0_conv[symmetric] f_shrink_length del: length_0_conv)
apply (case_tac "k2 = 0")
 apply (fastforce simp: f_shrink_empty_conv div_eq_0_conv')
apply (simp add: list_eq_iff f_shrink_length)
apply (rule conj_cong, simp)
apply (rule all_imp_eqI, simp)
apply (simp add: f_shrink_nth)
done

lemma f_shrink_eq_conv': "
  (xs' \<div>\<^sub>f k = xs) =
  (length xs' div k = length xs \<and>
  (\<forall>i<length xs.
      if xs ! i = \<NoMsg> then (\<forall>j<k. xs' ! (i * k + j) = \<NoMsg>)
      else (\<exists>n<k. xs' ! (i * k + n) = xs ! i \<and>
                  (\<forall>j<k. n < j \<longrightarrow> xs' ! (i * k + j) = \<NoMsg>))))"
apply (case_tac "k = 0", fastforce)
apply (simp add: list_eq_iff f_shrink_length split del: if_split)
apply (rule conj_cong, simp)
apply (rule all_imp_eqI, simp)
apply (cut_tac x=i in less_div_imp_mult_add_divisor_le[of _ "length xs'" k], simp)
apply (clarsimp simp: f_shrink_nth last_message_conv_if min_eqR)
apply (rule ex_imp_eqI, simp)
apply simp
done

lemma f_shrink_assoc: "xs \<div>\<^sub>f a \<div>\<^sub>f b = xs \<div>\<^sub>f (a * b)"
by (unfold f_shrink_def, rule f_aggregate_assoc, fold f_shrink_def, rule f_shrink_last_message)

lemma f_shrink_commute: "xs \<div>\<^sub>f a \<div>\<^sub>f b = xs \<div>\<^sub>f b \<div>\<^sub>f a"
by (simp add: f_shrink_assoc mult.commute[of a])

lemma i_shrink_0[simp]: "f \<div>\<^sub>i 0 = (\<lambda>n. \<NoMsg>)"
by (simp add: i_shrink_defs)
lemma i_shrink_1[simp]: "f \<div>\<^sub>i Suc 0 = f"
by (simp add: i_shrink_def i_aggregate_1)
lemma i_shrink_nth: "(f \<div>\<^sub>i k) n = last_message (f \<Up> (n * k) \<Down> k)"
by (simp add: i_shrink_defs)
lemma i_shrink_nth_eq_map: "(f \<div>\<^sub>i k) n = last_message (map f [n * k..<n * k + k])"
by (simp add: i_shrink_def i_aggregate_nth_eq_map)
lemma i_shrink_hd: "(f \<div>\<^sub>i k) 0 = last_message (f \<Down> k)"
by (simp add: i_shrink_nth)

lemma i_shrink_i_append_mod: "
  length xs mod k = 0 \<Longrightarrow> (xs \<frown> f) \<div>\<^sub>i k = xs \<div>\<^sub>f k \<frown> (f \<div>\<^sub>i k)"
by (simp add: f_shrink_def i_shrink_def i_aggregate_i_append_mod)

lemma i_shrink_i_append_mult: "
  length xs = m * k \<Longrightarrow> (xs \<frown> f) \<div>\<^sub>i k = xs \<div>\<^sub>f k \<frown> (f \<div>\<^sub>i k)"
by (simp add: i_shrink_i_append_mod)

lemma i_shrink_Cons: "
  \<lbrakk> 0 < k; length xs = k \<rbrakk> \<Longrightarrow> (xs \<frown> f) \<div>\<^sub>i k = [last_message xs] \<frown> (f \<div>\<^sub>i k)"
by (simp add: f_shrink_def i_shrink_def i_aggregate_Cons)

lemma i_shrink_take_nth: "
  n < m div k \<Longrightarrow> (f \<Down> m) \<div>\<^sub>f k ! n = (f \<div>\<^sub>i k) n"
by (simp add: f_shrink_def i_shrink_def i_aggregate_take_nth)

lemma i_shrink_const[simp]: "0 < k \<Longrightarrow> (\<lambda>x. m) \<div>\<^sub>i k = (\<lambda>x. m)"
by (simp add: ilist_eq_iff i_shrink_nth last_message_replicate)

lemma i_shrink_const_NoMsg[simp]: "(\<lambda>x. \<NoMsg>) \<div>\<^sub>i k = (\<lambda>x. \<NoMsg>)"
by (case_tac "k = 0", simp+)

lemma i_shrink_i_expand_id: "0 < k \<Longrightarrow> f \<odot>\<^sub>i k \<div>\<^sub>i k = f"
by (simp add: ilist_eq_iff i_shrink_nth i_expand_i_drop_mult i_expand_i_take_mod i_drop_i_take_1 last_message_replicate_NoMsg)

lemma i_shrink_i_take_mult: "0 < k \<Longrightarrow> f \<Down> (n * k) \<div>\<^sub>f k = f \<div>\<^sub>i k \<Down> n"
by (simp add: f_shrink_def i_shrink_def i_aggregate_i_take_mult)

lemma i_shrink_i_take: "
  f \<Down> n \<div>\<^sub>f k = f \<div>\<^sub>i k \<Down> (n div k)"
by (simp add: f_shrink_def i_shrink_def i_aggregate_i_take)

lemma i_shrink_i_drop_mult: "f \<Up> (n * k) \<div>\<^sub>i k = f \<div>\<^sub>i k \<Up> n"
by (simp add: f_shrink_def i_shrink_def i_aggregate_i_drop_mult)
lemma i_shrink_i_drop_mod: "
  n mod k = 0 \<Longrightarrow> f \<Up> n \<div>\<^sub>i k = f \<div>\<^sub>i k \<Up> (n div k)"
by (simp add: f_shrink_def i_shrink_def i_aggregate_i_drop_mod)

lemma i_shrink_eq_conv: "
  (f \<div>\<^sub>i k1 = g \<div>\<^sub>i k2) =
  (\<forall>i. last_message (f \<Up> (i * k1) \<Down> k1) =
       last_message (g \<Up> (i * k2) \<Down> k2))"
by (simp add: ilist_eq_iff i_shrink_nth)

lemma i_shrink_eq_conv': "
  (f' \<div>\<^sub>i k = f) =
  (\<forall>i. if f i = \<NoMsg> then \<forall>j<k. f' (i * k + j) = \<NoMsg>
       else \<exists>n<k. f' (i * k + n) = f i \<and>
                    (\<forall>j<k. n < j \<longrightarrow> f' (i * k + j) = \<NoMsg>))"
apply (simp add: ilist_eq_iff)
apply (case_tac "k = 0", fastforce)
apply (rule all_eqI, rename_tac i)
apply (simp add: i_shrink_nth)
apply (case_tac "f i = NoMsg")
 apply (simp add: last_message_NoMsg_conv)
apply (force simp add: last_message_conv)
done

lemma i_shrink_assoc: "f \<div>\<^sub>i a \<div>\<^sub>i b = f \<div>\<^sub>i (a * b)"
apply (case_tac "a = 0", simp)
apply (case_tac "b = 0", simp)
apply (unfold i_shrink_def, rule i_aggregate_assoc, simp+)
apply (fold f_shrink_def, simp add: f_shrink_last_message)
done

lemma i_shrink_commute: "f \<div>\<^sub>i a \<div>\<^sub>i b = f \<div>\<^sub>i b \<div>\<^sub>i a"
by (simp add: i_shrink_assoc mult.commute[of a])


subsubsection \<open>Holding last messages in everly cycle of a stream\<close>

primrec last_message_hold_init :: "'a fstream_af \<Rightarrow> 'a message_af \<Rightarrow> 'a fstream_af"
where
  "last_message_hold_init [] m = []"
| "last_message_hold_init (x # xs) m =
    (if x = \<NoMsg> then m else x) #
    (last_message_hold_init xs (if x = \<NoMsg> then m else x))"

definition last_message_hold :: "'a fstream_af \<Rightarrow> 'a fstream_af"
  where "last_message_hold xs \<equiv> last_message_hold_init xs \<NoMsg>"

lemma last_message_hold_init_length[simp]: "
  \<And>m. length (last_message_hold_init xs m) = length xs"
by (induct xs, simp+)

lemma last_message_hold_init_nth: "
  \<And>i m. i < length xs \<Longrightarrow>
  (last_message_hold_init xs m) ! i = last_message (m # xs \<down> Suc i)"
apply (induct xs, simp)
apply (simp add: nth_Cons')
done

lemma last_message_hold_init_snoc: "
  last_message_hold_init (xs @ [x]) m =
  last_message_hold_init xs m @
    [if x = \<NoMsg> then last_message (m # xs) else x]"
by (simp add: list_eq_iff nth_append last_message_hold_init_nth last_message_append)

lemma last_message_hold_init_append[rule_format]: "
  \<And>xs m. last_message_hold_init (xs @ ys) m =
  last_message_hold_init xs m @ last_message_hold_init ys (last_message (m # xs))"
apply (induct ys, simp)
apply (rule_tac x=a in subst[OF append_eq_Cons, rule_format])
apply (simp only: append_Cons[symmetric] append_assoc[symmetric])
apply (simp add: last_message_hold_init_snoc last_message_append)
done

lemma last_message_hold_length[simp]: "length (last_message_hold xs) = length xs"
by (simp add: last_message_hold_def)

lemma last_message_hold_Nil[simp]: "last_message_hold [] = []"
by (simp add: last_message_hold_def)

lemma last_message_hold_one[simp]: "last_message_hold [x] = [x]"
by (simp add: last_message_hold_def)

lemma last_message_hold_nth: "
  i < length xs \<Longrightarrow> last_message_hold xs ! i = last_message (xs \<down> Suc i)"
by (simp add: last_message_hold_def last_message_hold_init_nth)

lemma last_message_hold_last: "
  xs \<noteq> [] \<Longrightarrow> last (last_message_hold xs) = last_message xs"
apply (subgoal_tac "last_message_hold xs \<noteq> []")
 prefer 2
 apply (simp add: length_greater_0_conv[symmetric] del: length_greater_0_conv)
apply (simp add: last_nth last_message_hold_nth length_greater_0_conv[symmetric] del: length_greater_0_conv)
done

lemma last_message_hold_take: "
  last_message_hold xs \<down> n = last_message_hold (xs \<down> n)"
apply (case_tac "length xs \<le> n", simp)
apply (simp add: list_eq_iff last_message_hold_nth min_eqL)
done

lemma last_message_hold_snoc: "
  last_message_hold (xs @ [x]) =
  last_message_hold xs @ [if x = \<NoMsg> then last_message xs else x]"
by (simp add: last_message_hold_def last_message_hold_init_snoc)

lemma last_message_hold_append: "
  last_message_hold (xs @ ys) =
  last_message_hold xs @ last_message_hold_init ys (last_message xs)"
by (simp add: last_message_hold_def last_message_hold_init_append)

lemma last_message_hold_append': "
  last_message_hold (xs @ ys) =
  last_message_hold xs @ tl (last_message_hold (last_message xs # ys))"
apply (simp add: last_message_hold_append)
apply (simp add: last_message_hold_def)
done

lemma last_message_last_message_hold[simp]: "
  last_message (last_message_hold xs) = last_message xs"
apply (induct xs rule: rev_induct, simp)
apply (simp add: last_message_hold_snoc last_message_append)
done

lemma last_message_hold_idem[simp]: "
  last_message_hold (last_message_hold xs) = last_message_hold xs"
by (simp add: list_eq_iff last_message_hold_nth last_message_hold_take)


text \<open>
  Returns for each point in time the currently last non-empty message
  of the current stream cycle of length \<open>k\<close>.\<close>

definition f_last_message_hold :: "'a fstream_af \<Rightarrow> nat \<Rightarrow> 'a fstream_af" (infixl "\<longmapsto>\<^sub>f" 100)
  where "f_last_message_hold xs k \<equiv> concat (map last_message_hold (list_slice2 xs k))"

definition i_last_message_hold :: "'a istream_af \<Rightarrow> nat \<Rightarrow> 'a istream_af" (infixl "\<longmapsto>\<^sub>i" 100)
  where "i_last_message_hold f k \<equiv> \<lambda>n. last_message (f \<Up> (n - n mod k) \<Down> Suc (n mod k))"

notation
  f_last_message_hold  (infixl "\<longmapsto>" 100) and
  i_last_message_hold  (infixl "\<longmapsto>" 100)

lemma f_last_message_hold_0[simp]: "xs \<longmapsto>\<^sub>f 0 = last_message_hold xs"
by (simp add: f_last_message_hold_def list_slice2_0)

lemma f_last_message_hold_1[simp]: "xs \<longmapsto>\<^sub>f (Suc 0) = xs"
apply (simp add: f_last_message_hold_def list_slice2_1)
apply (induct xs, simp+)
done

lemma f_last_message_hold_Nil[simp]: "[] \<longmapsto>\<^sub>f k = []"
by (simp add: f_last_message_hold_def list_slice2_Nil)

lemma f_last_message_hold_length[simp]: "length (xs \<longmapsto>\<^sub>f k) = length xs"
apply (case_tac "k = 0", simp)
apply (simp add: f_last_message_hold_def)
apply (induct xs rule: append_constant_length_induct[of k])
 apply (simp add: list_slice2_le)
apply (simp add: list_slice2_append_mod list_slice2_mod_0 list_slice_div_eq_1)
done

lemma f_last_message_hold_le: "length xs \<le> k \<Longrightarrow> xs \<longmapsto>\<^sub>f k = last_message_hold xs"
by (simp add: f_last_message_hold_def list_slice2_le)

lemma f_last_message_hold_append_mult: "
  length xs = m * k \<Longrightarrow> (xs @ ys) \<longmapsto>\<^sub>f k = xs \<longmapsto>\<^sub>f k @ (ys \<longmapsto>\<^sub>f k)"
by (simp add: f_last_message_hold_def list_slice2_append_mod)

lemma f_last_message_hold_append_mod: "
  length xs mod k = 0 \<Longrightarrow> (xs @ ys) \<longmapsto>\<^sub>f k = xs \<longmapsto>\<^sub>f k @ (ys \<longmapsto>\<^sub>f k)"
by (simp add: f_last_message_hold_def list_slice2_append_mod)

lemma f_last_message_hold_nth[rule_format]: "
  \<forall>n. n < length xs \<longrightarrow> xs \<longmapsto>\<^sub>f k ! n = last_message (xs \<up> (n div k * k) \<down> Suc (n mod k))"
apply (case_tac "k = 0")
 apply (simp add: last_message_hold_nth)
apply (induct xs rule: append_constant_length_induct[of k])
 apply (simp add: f_last_message_hold_def list_slice2_le last_message_hold_nth)
apply (simp add: f_last_message_hold_append_mod nth_append)
apply (intro allI conjI impI)
 apply (simp add: f_last_message_hold_def list_slice2_mod_0 list_slice_div_eq_1 last_message_hold_nth)
apply (case_tac "n < k", simp)
apply (simp add: linorder_not_less last_message_append div_mult_cancel)
apply (subgoal_tac "k + n mod k \<le> n")
 prefer 2
 apply (drule div_le_mono[of _ _ k], drule mult_le_mono1[of _ _ k])
 apply (simp add: div_mult_cancel)
apply (simp add: mod_diff_self2 add.commute[of k])
done

lemma f_last_message_hold_take: "xs \<down> n \<longmapsto>\<^sub>f k = xs \<longmapsto>\<^sub>f k \<down> n"
by (clarsimp simp: list_eq_iff f_last_message_hold_nth drop_take div_mult_cancel min_eqL)

lemma f_last_message_hold_drop_mult: "
  xs \<up> (n * k) \<longmapsto>\<^sub>f k = xs \<longmapsto>\<^sub>f k \<up> (n * k)"
apply (rule subst[OF append_take_drop_id, of _ "n * k" xs])
apply (case_tac "length xs \<le> n * k", simp)
apply (simp add: f_last_message_hold_append_mod min_eqR del: append_take_drop_id)
done

lemma f_last_message_hold_drop_mod: "
  n mod k = 0 \<Longrightarrow> xs \<up> n \<longmapsto>\<^sub>f k = xs \<longmapsto>\<^sub>f k \<up> n"
  by (clarsimp simp: mult.commute[of k] f_last_message_hold_drop_mult elim!: dvdE)

lemma f_last_message_hold_idem: "xs \<longmapsto>\<^sub>f k \<longmapsto>\<^sub>f k = xs \<longmapsto>\<^sub>f k"
apply (case_tac "k = 0", simp)
apply (simp add: list_eq_iff f_last_message_hold_nth f_last_message_hold_drop_mod[symmetric] f_last_message_hold_take[symmetric])
apply (simp add: f_last_message_hold_le min.coboundedI2 Suc_mod_le_divisor)
done

lemma f_shrink_nth_eq_f_last_message_hold_last: "
  n < length xs div k \<Longrightarrow> xs \<div>\<^sub>f k ! n = last (xs \<longmapsto>\<^sub>f k \<up> (n * k) \<down> k)"
apply (case_tac "k = 0", simp)
apply (case_tac "xs = []", simp)
apply (simp add: f_shrink_nth f_last_message_hold_drop_mult[symmetric] f_last_message_hold_take[symmetric])
apply (drule less_div_imp_mult_add_divisor_le)
apply (simp add: f_last_message_hold_le last_message_hold_last)
done

lemma f_shrink_nth_eq_f_last_message_hold_nth: "
  n < length xs div k \<Longrightarrow> xs \<div>\<^sub>f k ! n = xs \<longmapsto>\<^sub>f k ! (n * k + k - Suc 0)"
apply (case_tac "k = 0", simp)
apply (simp add: f_shrink_nth_eq_f_last_message_hold_last)
apply (frule less_div_imp_mult_add_divisor_le)
apply (simp add: last_nth min_eqR)
done

lemma last_message_f_last_message_hold: "
  last_message (xs \<longmapsto>\<^sub>f k) = last_message xs"
apply (case_tac "k = 0", simp)
apply (induct xs rule: append_constant_length_induct[of k])
 apply (simp add: f_last_message_hold_le)
apply (simp add: f_last_message_hold_append_mult last_message_append f_last_message_hold_le)
done

lemma i_last_message_hold_0[simp]: "f \<longmapsto>\<^sub>i 0 = (\<lambda>n. last_message (f \<Down> Suc n))"
by (simp add: i_last_message_hold_def)
lemma i_last_message_hold_1[simp]: "f \<longmapsto>\<^sub>i Suc 0 = f"
by (simp add: i_last_message_hold_def i_drop_i_take_1)

lemma i_last_message_hold_nth: "
  (f \<longmapsto>\<^sub>i k) n = last_message (f \<Up> (n - n mod k) \<Down> Suc (n mod k))"
by (simp add: i_last_message_hold_def)

lemma i_last_message_hold_i_append_mult: "
  length xs = m * k \<Longrightarrow> (xs \<frown> f) \<longmapsto>\<^sub>i k = (xs \<longmapsto>\<^sub>f k) \<frown> (f \<longmapsto>\<^sub>i k)"
apply (case_tac "k = 0", simp)
apply (clarsimp simp: ilist_eq_iff i_last_message_hold_nth i_append_nth f_last_message_hold_nth div_mult_cancel linorder_not_less)
apply (subgoal_tac "length xs \<le> x - x mod k")
 prefer 2
 apply (drule div_le_mono[of _ _ k])
 apply (simp add: div_mult_cancel[symmetric])
apply (simp add: mod_diff_mult_self1)
apply (drule_tac j="x - x mod k" and k="x mod k" in add_le_mono1)
apply (simp add: add.commute[of "m * k"])
done

lemma i_last_message_hold_i_append_mod: "
  length xs mod k = 0 \<Longrightarrow> (xs \<frown> f) \<longmapsto>\<^sub>i k = (xs \<longmapsto>\<^sub>f k) \<frown> (f \<longmapsto>\<^sub>i k)"
  by (clarsimp simp: mult.commute[of k] elim!: dvdE, rule i_last_message_hold_i_append_mult)

lemma i_last_message_hold_i_take: "f \<Down> n \<longmapsto>\<^sub>f k = (f \<longmapsto>\<^sub>i k) \<Down> n"
by (simp add: list_eq_iff f_last_message_hold_nth i_last_message_hold_nth div_mult_cancel i_take_drop min_eqR)

lemma i_last_message_hold_i_drop_mult: "
  f \<Up> (n * k) \<longmapsto>\<^sub>i k = f \<longmapsto>\<^sub>i k \<Up> (n * k)"
by (simp add: ilist_eq_iff i_last_message_hold_nth)

lemma i_last_message_hold_i_drop_mod: "
  n mod k = 0 \<Longrightarrow> f \<Up> n \<longmapsto>\<^sub>i k = f \<longmapsto>\<^sub>i k \<Up> n"
  by (clarsimp simp: mult.commute[of k] elim!: dvdE, rule i_last_message_hold_i_drop_mult)

lemma i_last_message_hold_idem: "f \<longmapsto>\<^sub>i k \<longmapsto>\<^sub>i k = f \<longmapsto>\<^sub>i k"
by (simp add: ilist_eq_iff i_last_message_hold_nth minus_mod_eq_mult_div i_last_message_hold_i_drop_mod[symmetric] i_last_message_hold_i_take[symmetric] last_message_f_last_message_hold)

lemma i_shrink_nth_eq_i_last_message_hold_nth: "
  0 < k \<Longrightarrow> (f \<div>\<^sub>i k) n = (f \<longmapsto>\<^sub>i k) (n * k + k - Suc 0)"
apply (simp add: i_shrink_nth i_last_message_hold_nth)
apply (simp add: diff_add_assoc del: add_diff_assoc)
done

lemma i_shrink_nth_eq_i_last_message_hold_last: "
  0 < k \<Longrightarrow> (f \<div>\<^sub>i k) n = last (f \<longmapsto>\<^sub>i k \<Up> (n * k) \<Down> k)"
by (simp add: last_nth i_shrink_nth_eq_i_last_message_hold_nth)


subsubsection \<open>Compressing lists\<close>

text \<open>
  Lists/Non-message streams
  do not have to permit the empty message \<open>\<NoMsg>\<close>
  to be element.
  Thus, they are compressed by factor @{term k}
  by just aggregating every sequence of length k
  to its last element.\<close>

definition f_shrink_last :: "'a list \<Rightarrow> nat \<Rightarrow> 'a list"   (infixl "\<div>\<^bsub>fl\<^esub>" 100)
  where "f_shrink_last xs k \<equiv> f_aggregate xs k last"

definition i_shrink_last :: "'a ilist \<Rightarrow> nat \<Rightarrow> 'a ilist" (infixl "\<div>\<^bsub>il\<^esub>" 100)
  where "i_shrink_last f k \<equiv> i_aggregate f k last"

notation
  f_shrink_last  (infixl "\<div>\<^sub>l" 100) and
  i_shrink_last  (infixl "\<div>\<^sub>l" 100)


lemma f_shrink_last_0[simp]: "xs \<div>\<^bsub>fl\<^esub> 0 = []"
by (simp add: f_shrink_last_def f_aggregate_def list_slice_0)

lemma f_shrink_last_1[simp]: "xs \<div>\<^bsub>fl\<^esub> Suc 0 = xs"
by (simp add: f_shrink_last_def f_aggregate_1)

lemma f_shrink_last_Nil[simp]: "[] \<div>\<^bsub>fl\<^esub> k = []"
by (simp add: f_shrink_last_def f_aggregate_def list_slice_Nil)

lemma f_shrink_last_length: "length (xs \<div>\<^bsub>fl\<^esub> k) = length xs div k"
by (simp add: f_shrink_last_def)

lemma f_shrink_last_empty_conv: "
  0 < k \<Longrightarrow> (xs \<div>\<^bsub>fl\<^esub> k = []) = (length xs < k)"
by (simp add: f_shrink_last_def f_aggregate_empty_conv)

lemma f_shrink_last_Cons: "
  \<lbrakk> 0 < k;
 length xs = k \<rbrakk> \<Longrightarrow> (xs @ ys) \<div>\<^bsub>fl\<^esub> k = last xs # (ys \<div>\<^bsub>fl\<^esub> k)"
by (simp add: f_shrink_last_def f_aggregate_Cons)

lemma f_shrink_last_one: "
  \<lbrakk> 0 < k; length xs = k \<rbrakk> \<Longrightarrow> xs \<div>\<^bsub>fl\<^esub> k = [last xs]"
by (simp add: f_shrink_last_def f_aggregate_one)

lemma f_shrink_last_eq_f_shrink_last_take: "
  xs \<down> (length xs div k * k) \<div>\<^bsub>fl\<^esub> k = xs \<div>\<^bsub>fl\<^esub> k"
by (simp add: f_shrink_last_def f_aggregate_eq_f_aggregate_take)

lemma f_shrink_last_nth: "
  n < length xs div k \<Longrightarrow> (xs \<div>\<^bsub>fl\<^esub> k) ! n = xs ! (n * k + k - Suc 0)"
apply (case_tac "k = 0", simp)
apply (frule less_div_imp_mult_add_divisor_le)
apply (simp add: f_shrink_last_def f_aggregate_nth last_take2)
done

corollary f_shrink_last_nth': "
  n < length xs div k \<Longrightarrow> (xs \<div>\<^bsub>fl\<^esub> k) ! n = xs ! (Suc n * k - Suc 0)"
by (simp add: f_shrink_last_nth add.commute[of k])

lemma f_shrink_last_hd: "
  \<lbrakk> 0 < k; k \<le> length xs \<rbrakk> \<Longrightarrow> hd (xs \<div>\<^bsub>fl\<^esub> k) = xs ! (k - Suc 0)"
by (simp add: f_shrink_last_def f_aggregate_hd last_take2)


lemma f_shrink_last_map: "(map f xs) \<div>\<^bsub>fl\<^esub> k = map f (xs \<div>\<^bsub>fl\<^esub> k)"
apply (case_tac "k = 0", simp)
apply (clarsimp simp: list_eq_iff f_shrink_last_length)
apply (frule less_div_imp_mult_add_divisor_le)
apply (simp add: f_shrink_last_nth)
done

lemma f_shrink_last_append_mod: "
  length xs mod k = 0 \<Longrightarrow> (xs @ ys) \<div>\<^bsub>fl\<^esub> k = xs \<div>\<^bsub>fl\<^esub> k @ (ys \<div>\<^bsub>fl\<^esub> k)"
by (simp add: f_shrink_last_def f_aggregate_append_mod)

lemma f_shrink_last_append_mult: "
  length xs = m * k \<Longrightarrow> (xs @ ys) \<div>\<^bsub>fl\<^esub> k = xs \<div>\<^bsub>fl\<^esub> k @ (ys \<div>\<^bsub>fl\<^esub> k)"
by (unfold f_shrink_last_def, rule f_aggregate_append_mult)

lemma f_shrink_last_snoc: "
  \<lbrakk> 0 < k; length ys = k; length xs mod k = 0 \<rbrakk> \<Longrightarrow>
  (xs @ ys) \<div>\<^bsub>fl\<^esub> k = xs \<div>\<^bsub>fl\<^esub> k @ [last ys]"
by (simp add: f_shrink_last_append_mod f_shrink_last_one)

lemma f_shrink_last_last: "
  length xs mod k = 0 \<Longrightarrow> last (xs \<div>\<^bsub>fl\<^esub> k) = last xs"
apply (case_tac "k = 0", simp)
apply (case_tac "xs = []", simp)
apply (subgoal_tac "k \<le> length xs")
 prefer 2
 apply (rule ccontr, simp)
apply (rule subst[OF append_take_drop_id[of "length xs - k" xs]])
apply (subst f_shrink_last_snoc)
apply (simp add: min_eqR mod_diff_self2)+
done

lemma f_shrink_last_replicate: "m\<^bsup>n\<^esup> \<div>\<^bsub>fl\<^esub> k = m\<^bsup>n div k\<^esup>"
apply (case_tac "k = 0", simp)
apply (clarsimp simp: list_eq_iff f_shrink_last_length)
apply (frule less_div_imp_mult_add_divisor_le)
apply (simp add: f_shrink_last_nth)
done

lemma f_shrink_last_take: "
  xs \<down> n \<div>\<^bsub>fl\<^esub> k = xs \<div>\<^bsub>fl\<^esub> k \<down> (n div k)"
by (unfold f_shrink_last_def, rule f_aggregate_take)

lemma f_shrink_last_take_mult: "xs \<down> (n * k) \<div>\<^bsub>fl\<^esub> k = xs \<div>\<^bsub>fl\<^esub> k \<down> n"
by (unfold f_shrink_last_def, rule f_aggregate_take_mult)


lemma f_shrink_last_drop_mult: "xs \<up> (n * k) \<div>\<^bsub>fl\<^esub> k = xs \<div>\<^bsub>fl\<^esub> k \<up> n"
by (unfold f_shrink_last_def, rule f_aggregate_drop_mult)

lemma f_shrink_last_drop_mod: "
  n mod k = 0 \<Longrightarrow> xs \<up> n \<div>\<^bsub>fl\<^esub> k = xs \<div>\<^bsub>fl\<^esub> k \<up> (n div k)"
by (unfold f_shrink_last_def, rule f_aggregate_drop_mod)

lemma f_shrink_last_assoc: "xs \<div>\<^bsub>fl\<^esub> a \<div>\<^bsub>fl\<^esub> b = xs \<div>\<^bsub>fl\<^esub> (a * b)"
by (unfold f_shrink_last_def, rule f_aggregate_assoc, fold f_shrink_last_def, rule f_shrink_last_last)

lemma f_shrink_last_commute: "xs \<div>\<^bsub>fl\<^esub> a \<div>\<^bsub>fl\<^esub> b = xs \<div>\<^bsub>fl\<^esub> b \<div>\<^bsub>fl\<^esub> a"
by (simp add: f_shrink_last_assoc mult.commute[of a])

lemma i_shrink_last_1[simp]: "f \<div>\<^bsub>il\<^esub> Suc 0 = f"
by (simp add: i_shrink_last_def i_aggregate_1)

lemma i_shrink_last_nth: "0 < k \<Longrightarrow> (f \<div>\<^bsub>il\<^esub> k) n =  f (n * k + k - Suc 0)"
by (simp add: i_shrink_last_def i_aggregate_nth last_i_take2)

lemma i_shrink_last_nth': "0 < k \<Longrightarrow> (f \<div>\<^bsub>il\<^esub> k) n =  f (Suc n * k - Suc 0)"
by (simp add: i_shrink_last_nth add.commute[of k])

lemma i_shrink_last_hd: "(f \<div>\<^bsub>il\<^esub> k) 0 = last (f \<Down> k)"
apply (case_tac "k = 0")
 apply (simp add: i_shrink_last_def)
apply (simp add: i_shrink_last_nth last_i_take2)
done

lemma i_shrink_last_o: "0 < k \<Longrightarrow> (f \<circ> g) \<div>\<^bsub>il\<^esub> k = f \<circ> (g \<div>\<^bsub>il\<^esub> k)"
by (simp add: ilist_eq_iff i_shrink_last_nth)

lemma i_shrink_last_i_append_mod: "
  length xs mod k = 0 \<Longrightarrow> (xs \<frown> f) \<div>\<^bsub>il\<^esub> k = xs \<div>\<^bsub>fl\<^esub> k \<frown> (f \<div>\<^bsub>il\<^esub> k)"
by (simp add: f_shrink_last_def i_shrink_last_def i_aggregate_i_append_mod)

lemma i_shrink_last_i_append_mult: "
  length xs = m * k \<Longrightarrow> (xs \<frown> f) \<div>\<^bsub>il\<^esub> k = xs \<div>\<^bsub>fl\<^esub> k \<frown> (f \<div>\<^bsub>il\<^esub> k)"
by (simp add: i_shrink_last_i_append_mod)

lemma i_shrink_last_Cons: "
  \<lbrakk> 0 < k; length xs = k \<rbrakk> \<Longrightarrow> (xs \<frown> f) \<div>\<^bsub>il\<^esub> k = [last xs] \<frown> (f \<div>\<^bsub>il\<^esub> k)"
by (simp add: f_shrink_last_def i_shrink_last_def i_aggregate_Cons)

lemma i_shrink_last_const: "0 < k \<Longrightarrow> (\<lambda>x. m) \<div>\<^bsub>il\<^esub> k = (\<lambda>x. m)"
by (simp add: ilist_eq_iff i_shrink_last_nth)

lemma i_shrink_last_i_take_mult: "
  0 < k \<Longrightarrow> f \<Down> (n * k) \<div>\<^bsub>fl\<^esub> k = f \<div>\<^bsub>il\<^esub> k \<Down> n"
by (simp add: f_shrink_last_def i_shrink_last_def i_aggregate_i_take_mult)

lemma i_shrink_last_i_take: "
  f \<Down> n \<div>\<^bsub>fl\<^esub> k = f \<div>\<^bsub>il\<^esub> k \<Down> (n div k)"
by (simp add: f_shrink_last_def i_shrink_last_def i_aggregate_i_take)

lemma i_shrink_last_i_drop_mult: "f \<Up> (n * k) \<div>\<^bsub>il\<^esub> k = f \<div>\<^bsub>il\<^esub> k \<Up> n"
by (simp add: f_shrink_last_def i_shrink_last_def i_aggregate_i_drop_mult)
lemma i_shrink_last_i_drop_mod: "
  n mod k = 0 \<Longrightarrow> f \<Up> n \<div>\<^bsub>il\<^esub> k = f \<div>\<^bsub>il\<^esub> k \<Up> (n div k)"
by (simp add: f_shrink_last_def i_shrink_last_def i_aggregate_i_drop_mod)

lemma i_shrink_last_assoc: "f \<div>\<^bsub>il\<^esub> a \<div>\<^bsub>il\<^esub> b = f \<div>\<^bsub>il\<^esub> (a * b)"
apply (unfold i_shrink_last_def)
apply (case_tac "b = 0", simp)
apply (case_tac "a = 0", simp add: i_aggregate_def)
apply (simp add: i_aggregate_assoc f_shrink_last_last[unfolded f_shrink_last_def])
done

lemma i_shrink_last_commute: "f \<div>\<^bsub>il\<^esub> a \<div>\<^bsub>il\<^esub> b = f \<div>\<^bsub>il\<^esub> b \<div>\<^bsub>il\<^esub> a"
by (simp add: i_shrink_last_assoc mult.commute[of a])


text \<open>
  Shrinking a message stream with \<open>last_message\<close> as aggregation function
  corresponds to shrinking the stream holding last message in each cycle
  with \<open>last\<close> as aggregation function.\<close>

lemma f_shrink_eq_f_last_message_hold_shrink_last: "
  xs \<div>\<^sub>f k = xs \<longmapsto>\<^sub>f k \<div>\<^bsub>fl\<^esub> k"
by (simp add: list_eq_iff f_shrink_length f_shrink_last_length f_shrink_nth_eq_f_last_message_hold_nth f_shrink_last_nth)

lemma i_shrink_eq_i_last_message_hold_shrink_last: "
  0 < k \<Longrightarrow> f \<div>\<^sub>i k = f \<longmapsto>\<^sub>i k \<div>\<^bsub>il\<^esub> k"
by (simp add: ilist_eq_iff i_shrink_last_nth i_shrink_nth_eq_i_last_message_hold_nth)

end
