(*<*)
(*
   Title:  Theory ListExtras.thy
   Author: Maria Spichkova <maria.spichkova at rmit.edu.au>, 2014
*)
(*>*)
section \<open>Auxiliary Theory ListExtras.thy\<close>

theory ListExtras 
imports Main
begin

definition
  disjoint :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool"
where
 "disjoint x y \<equiv>  (set x) \<inter> (set y) = {}"

primrec
  mem ::  "'a \<Rightarrow> 'a list \<Rightarrow> bool" (infixr "mem" 65)
where
  "x mem [] = False" |
  "x mem (y # l) = ((x = y) \<or> (x mem l))"

definition
  memS ::  "'a \<Rightarrow> 'a list \<Rightarrow> bool"
where
 "memS x l  \<equiv>  x \<in> (set l)"

lemma mem_memS_eq:  "x mem l \<equiv> memS x l"
proof (induct l)
  case Nil
  from this show ?case by (simp add: memS_def)
next
    fix a la case (Cons a la)
    from Cons show ?case by (simp add: memS_def)
 qed

lemma mem_set_1:
assumes "a mem l"
shows "a \<in> set l"
using assms by (metis memS_def mem_memS_eq)

lemma mem_set_2:
assumes "a \<in> set l"
shows "a mem l"
using assms by (metis (full_types) memS_def mem_memS_eq)

lemma set_inter_mem: 
assumes "x mem l1"
       and "x mem l2"
shows "set l1 \<inter> set l2 \<noteq> {}"
using assms  by (metis IntI empty_iff mem_set_1)

lemma mem_notdisjoint: 
assumes "x mem l1"
       and "x mem l2"
shows "\<not> disjoint l1 l2"
using assms by (metis disjoint_def set_inter_mem)

lemma mem_notdisjoint2:
assumes h1:"disjoint (schedule A) (schedule B)"
       and h2:"x mem schedule A"
shows "\<not> x mem schedule B"
proof - 
  { assume " x mem schedule B"
     from h2 and this have "\<not>  disjoint (schedule A) (schedule B)" 
       by (simp add: mem_notdisjoint)
    from h1 and this have "False" by simp
   } then have "\<not> x mem schedule B" by blast
  then show ?thesis by simp
qed

lemma Add_Less: 
assumes "0 < b"
shows    "(Suc a - b < Suc a) = True"
using assms by auto

lemma list_length_hint1: 
assumes "l \<noteq> []"
shows    "0 < length l" 
using assms by simp

lemma list_length_hint1a: 
assumes "l \<noteq> []"
shows    "0 < length l" 
using assms by simp

lemma list_length_hint2: 
assumes "length x  = Suc 0"
shows    "[hd x] = x"
using assms  
by (metis Zero_neq_Suc list.sel(1) length_Suc_conv neq_Nil_conv)

lemma list_length_hint2a: 
assumes "length l = Suc 0"
shows    "tl l = []"
using assms
by (metis list_length_hint2 list.sel(3)) 

lemma list_length_hint3: 
assumes "length l = Suc 0"
shows    "l \<noteq> []"
using assms
by (metis Zero_neq_Suc list.size(3))

lemma list_length_hint4: 
assumes "length x \<le> Suc 0"
       and "x \<noteq> []"
shows "length x = Suc 0"
using assms
by (metis le_0_eq le_Suc_eq length_greater_0_conv less_numeral_extra(3))

lemma length_nonempty: 
assumes "x \<noteq> []" 
shows    "Suc 0 \<le> length x"
using assms
by (metis length_greater_0_conv less_eq_Suc_le) 

lemma last_nth_length: 
assumes "x \<noteq> []"
shows    "x ! ((length x) - Suc 0) = last x"
using assms
by (metis One_nat_def last_conv_nth)

lemma list_nth_append0:
assumes "i < length x"
shows    "x ! i = (x @ z) ! i"
using assms
by (metis nth_append) 

lemma list_nth_append1:
assumes "i < length x"
shows    "(b # x) ! i = (b # x @ y) ! i"
proof -
  from assms have "i < length (b # x)" by auto
  then have sg2: "(b # x) ! i = ((b # x) @ y) ! i" 
    by (rule list_nth_append0)
  then show ?thesis by simp
qed
  
lemma list_nth_append2:
assumes "i < Suc (length x)"
shows    "(b # x) ! i = (b # x @ a # y) ! i"
using assms
by (metis Cons_eq_appendI length_Suc_conv list_nth_append0)

lemma list_nth_append3:
assumes h1:"\<not> i < Suc (length x)"
       and "i - Suc (length x) < Suc (length y)"
shows "(a # y) ! (i - Suc (length x)) = (b # x @ a # y) ! i"
proof (cases i)
  assume "i=0" 
  with h1  show ?thesis by (simp add: nth_append)
next
  fix ii assume "i = Suc ii"
  with h1  show ?thesis  by (simp add: nth_append)
qed

lemma list_nth_append4:
assumes "i < Suc (length x + length y)"
       and "\<not> i - Suc (length x) < Suc (length y)" 
shows "False"
using assms  by arith

lemma list_nth_append5:
assumes "i - length x < Suc (length y)" 
       and "\<not> i - Suc (length x) < Suc (length y)"
shows "\<not>  i < Suc (length x + length y)"
using assms  by arith

lemma list_nth_append6:
assumes "\<not> i - length x < Suc (length y)"
       and "\<not> i - Suc (length x) < Suc (length y)"
shows "\<not> i < Suc (length x + length y)"
using assms by arith

lemma list_nth_append6a:
assumes "i < Suc (length x + length y)"
       and "\<not> i - length x < Suc (length y)"
shows "False"
using assms by arith 

lemma list_nth_append7:
assumes "i - length x < Suc (length y)"
       and "i - Suc (length x) < Suc (length y)"
shows    "i < Suc (Suc (length x + length y))"
using assms  by arith

lemma list_nth_append8:
assumes "\<not> i < Suc (length x + length y)"
       and "i < Suc (Suc (length x + length y))"
shows     "i = Suc (length x + length y)"
using assms  by arith

lemma list_nth_append9:
assumes "i - Suc (length x) < Suc (length y)"
shows    "i < Suc (Suc (length x + length y))"
using assms by arith
  
lemma list_nth_append10:
assumes "\<not> i < Suc (length x)"
       and "\<not> i - Suc (length x) < Suc (length y)"
shows    "\<not> i < Suc (Suc (length x + length y))"
using assms by arith

end
