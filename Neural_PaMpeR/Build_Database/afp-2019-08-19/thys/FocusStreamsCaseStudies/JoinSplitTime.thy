(*<*)
(*
   Title:  Theory JoinSplitTime.thy
   Author: Maria Spichkova <maria.spichkova at rmit.edu.au>, 2013
*) 
(*>*)
 section \<open>Changing time granularity of the streams\<close> 

theory JoinSplitTime
imports stream arith_hints
begin

subsection  \<open>Join time units\<close>

primrec
  join_ti ::"'a istream \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a list"
where
join_ti_0:
 "join_ti s x 0 = s x" |
join_ti_Suc:
 "join_ti s x (Suc i) = (join_ti s x i) @ (s (x + (Suc i)))"

primrec
  fin_join_ti ::"'a fstream \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a list"
where
fin_join_ti_0:
 "fin_join_ti s x 0 = nth s x" |
fin_join_ti_Suc:
 "fin_join_ti s x (Suc i) = (fin_join_ti s x i) @ (nth s (x + (Suc i)))"

definition 
  join_time ::"'a istream \<Rightarrow> nat \<Rightarrow> 'a istream"
where
 "join_time s n t \<equiv> 
  (case n of 
        0  \<Rightarrow> []
  |(Suc i) \<Rightarrow>  join_ti s (n*t) i)"

lemma join_ti_hint1:
  assumes "join_ti s x (Suc i) = []"
  shows   "join_ti s x i = []"
using assms by auto

lemma join_ti_hint2:
  assumes "join_ti s x (Suc i) = []"
  shows   "s (x + (Suc i)) = []"
using assms by auto

lemma join_ti_hint3:
  assumes "join_ti s x (Suc i) = []"
  shows   "s (x + i) = []"
using assms by (induct i, auto)

lemma join_ti_empty_join:
  assumes "i \<le> n"
         and "join_ti s x n = []"
  shows      "s (x+i) = []"
using assms 
proof (induct n)
  case 0 then show ?case by auto
next 
  case (Suc n) then show ?case
  by (metis join_ti_hint1 join_ti_hint2 le_SucE) 
qed
  
lemma join_ti_empty_ti:
  assumes "\<forall> i \<le> n. s (x+i) = []"
  shows    "join_ti s x n = []"
using assms by (induct n, auto)
 
lemma join_ti_1nempty:
  assumes "\<forall> i. 0 < i \<and> i < Suc n \<longrightarrow> s (x+i) = []" 
  shows    "join_ti s x n = s x"
using assms by (induct n, auto)

lemma join_time1t: "\<forall> t. join_time s (1::nat) t = s t"
by (simp add: join_time_def)

 
lemma join_time1: "join_time s 1 = s"
by (simp add: fun_eq_iff join_time_def)

lemma join_time_empty1:
  assumes h1:"i < n"
         and h2:"join_time s n t = []"
  shows      "s (n*t + i) = []"
proof (cases n) 
  assume "n = 0"
  from assms and this show ?thesis by (simp add: join_time_def)
next
  fix x
  assume a2:"n = Suc x"
  from assms and a2 have sg1:"join_ti s (t + x * t) x = []"    
    by (simp add: join_time_def)
  from a2 and h1 have "i \<le> x" by simp
  from this and sg1 and a2 show ?thesis by (simp add: join_ti_empty_join)
qed

lemma fin_join_ti_hint1:
  assumes "fin_join_ti s x (Suc i) = []"
  shows   "fin_join_ti s x i = []"
using assms by auto

lemma fin_join_ti_hint2:
  assumes "fin_join_ti s x (Suc i) = []"
  shows    "nth s (x + (Suc i)) = []"
using assms by auto
 
lemma fin_join_ti_hint3:
  assumes "fin_join_ti s x (Suc i) = []"
  shows    "nth s (x + i) = []"
using assms by (induct i, auto)

lemma fin_join_ti_empty_join:
  assumes "i \<le> n"
         and "fin_join_ti s x n = []"
  shows      "nth s (x+i) = []"
using assms
proof (induct n)
  case 0 then show ?case by auto
next
  case (Suc n) then show ?case
  proof (cases "i = Suc n")
    assume "i = Suc n"
    from Suc and this show ?thesis by simp
  next
    assume "i \<noteq> Suc n"
    from Suc and this show ?thesis by simp
  qed
qed

lemma fin_join_ti_empty_ti:
  assumes "\<forall> i \<le> n. nth s (x+i) = []"
  shows    "fin_join_ti s x n = []"
using assms by (induct n, auto)

lemma fin_join_ti_1nempty:
  assumes "\<forall> i. 0 < i \<and> i < Suc n \<longrightarrow> nth s (x+i) = []" 
  shows    "fin_join_ti s x n = nth s x"
using assms  by (induct n, auto)


subsection \<open>Split time units\<close>

definition 
  split_time ::"'a istream \<Rightarrow> nat \<Rightarrow> 'a istream"
where
 "split_time s n t \<equiv> 
  ( if (t mod n = 0) 
    then s (t div n)
    else [])"

lemma split_time1t: "\<forall> t. split_time s 1 t = s t"
by (simp add: split_time_def)

lemma split_time1: "split_time s 1 = s"
by (simp add: fun_eq_iff split_time_def)

lemma split_time_mod: 
  assumes "t mod n \<noteq> 0"
  shows    "split_time s n t = []"
using assms by (simp add: split_time_def)

lemma split_time_nempty: 
  assumes "0 < n"
  shows    "split_time s n (n * t) = s t"
using assms by (simp add: split_time_def)

lemma split_time_nempty_Suc:
  assumes "0 < n"
  shows   "split_time s (Suc n) ((Suc n) * t) = split_time s n (n * t)"
proof - 
  have "0 < Suc n" by simp
  then have sg1:"split_time s (Suc n) ((Suc n) * t) =  s t"
    by (rule split_time_nempty)
  from assms have sg2:"split_time s n (n * t) = s t"  
    by (rule split_time_nempty)
  from sg1 and sg2 show ?thesis by simp
qed

lemma split_time_empty:
  assumes "i < n" and h2:"0 < i"
  shows    "split_time s n (n * t + i) = []" 
proof -
  from assms have "0 < (n * t + i) mod n" by (simp add: arith_mod_nzero)
  from assms and this show ?thesis by (simp add: split_time_def)
qed

lemma split_time_empty_Suc:
  assumes h1:"i < n" 
         and h2:"0 < i"
  shows "split_time s (Suc n) ((Suc n)* t + i)  = split_time s n (n * t + i)"
proof - 
  from h1 have "i < Suc n" by simp
  from this and h2 have sg2:"split_time s (Suc n) (Suc n * t + i) = []"
    by (rule split_time_empty)
  from assms have sg3:"split_time s n (n * t + i) = []"
    by (rule split_time_empty)
  from sg3 and sg2 show ?thesis by simp
qed

lemma split_time_hint1:
  assumes "n = Suc m"
  shows   "split_time s (Suc n) (i + n * i + n) = []"
proof - 
  have sg1:"i + n * i + n = (Suc n) * i + n" by simp
  have sg2:"n < Suc n" by simp
  from assms have sg3:"0 < n" by simp
  from sg2 and sg3 have sg4:"split_time s (Suc n) (Suc n * i + n) = []"
     by (rule split_time_empty)
  from sg1 and sg4  show ?thesis by auto
qed


subsection \<open>Duality of the split and the join operators\<close>

lemma join_split_i:
  assumes "0 < n"
  shows   "join_time (split_time s n) n i = s i"
proof (cases n)
  assume "n = 0"
  from this and assms show ?thesis by simp
next
  fix k
  assume a2:"n = Suc k"
  have sg0:"0 < Suc k" by simp
  then have sg1:"(split_time s (Suc k)) (Suc k * i) = s i"
    by (rule split_time_nempty)
  have sg2:"i + k * i = (Suc k) * i" by simp
  have sg3:"\<forall> j. 0 < j \<and> j < Suc k \<longrightarrow> split_time s (Suc k) (Suc k * i + j) = []"
    by (clarify, rule split_time_empty, auto)
  from sg3 have sg4:"join_ti (split_time s (Suc k)) ((Suc k) * i) k = 
                     (split_time s (Suc k)) (Suc k * i)"
    by (rule join_ti_1nempty)
  from a2 and sg4 and sg1 show ?thesis by (simp add: join_time_def)
qed

lemma join_split:
  assumes "0 < n"
  shows "join_time (split_time s n) n = s"
using assms  by (simp add: fun_eq_iff join_split_i)

end
