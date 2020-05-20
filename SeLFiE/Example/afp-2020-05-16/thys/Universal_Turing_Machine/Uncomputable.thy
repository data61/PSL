(* Title: thys/Uncomputable.thy
   Author: Jian Xu, Xingyuan Zhang, and Christian Urban
   Modifications: Sebastiaan Joosten
*)

chapter \<open>Undeciablity of the Halting Problem\<close>

theory Uncomputable
  imports Turing_Hoare
begin

lemma numeral:
  shows "2 = Suc 1"
    and "3 = Suc 2"
    and "4 = Suc 3" 
    and "5 = Suc 4" 
    and "6 = Suc 5" 
    and "7 = Suc 6"
    and "8 = Suc 7" 
    and "9 = Suc 8" 
    and "10 = Suc 9"
    and "11 = Suc 10"
    and "12 = Suc 11"
  by simp_all

lemma gr1_conv_Suc:"Suc 0 < mr \<longleftrightarrow> (\<exists> nat. mr = Suc (Suc nat))" by presburger

text \<open>The Copying TM, which duplicates its input.\<close>

definition 
  tcopy_begin :: "instr list"
  where
    "tcopy_begin \<equiv> [(W0, 0), (R, 2), (R, 3), (R, 2),
                 (W1, 3), (L, 4), (L, 4), (L, 0)]"

definition 
  tcopy_loop :: "instr list"
  where
    "tcopy_loop \<equiv> [(R, 0), (R, 2),  (R, 3), (W0, 2),
                 (R, 3), (R, 4), (W1, 5), (R, 4),
                 (L, 6), (L, 5), (L, 6), (L, 1)]"

definition 
  tcopy_end :: "instr list"
  where
    "tcopy_end \<equiv> [(L, 0), (R, 2), (W1, 3), (L, 4),
                (R, 2), (R, 2), (L, 5), (W0, 4),
                (R, 0), (L, 5)]"

definition 
  tcopy :: "instr list"
  where
    "tcopy \<equiv> (tcopy_begin |+| tcopy_loop) |+| tcopy_end"


(* tcopy_begin *)

fun 
  inv_begin0 :: "nat \<Rightarrow> tape \<Rightarrow> bool" and
  inv_begin1 :: "nat \<Rightarrow> tape \<Rightarrow> bool" and
  inv_begin2 :: "nat \<Rightarrow> tape \<Rightarrow> bool" and
  inv_begin3 :: "nat \<Rightarrow> tape \<Rightarrow> bool" and
  inv_begin4 :: "nat \<Rightarrow> tape \<Rightarrow> bool"
  where
    "inv_begin0 n (l, r) = ((n > 1 \<and> (l, r) = (Oc \<up> (n - 2), [Oc, Oc, Bk, Oc])) \<or>   
                          (n = 1 \<and> (l, r) = ([], [Bk, Oc, Bk, Oc])))"
  | "inv_begin1 n (l, r) = ((l, r) = ([], Oc \<up> n))"
  | "inv_begin2 n (l, r) = (\<exists> i j. i > 0 \<and> i + j = n \<and> (l, r) = (Oc \<up> i, Oc \<up> j))"
  | "inv_begin3 n (l, r) = (n > 0 \<and> (l, tl r) = (Bk # Oc \<up> n, []))"
  | "inv_begin4 n (l, r) = (n > 0 \<and> (l, r) = (Oc \<up> n, [Bk, Oc]) \<or> (l, r) = (Oc \<up> (n - 1), [Oc, Bk, Oc]))"

fun inv_begin :: "nat \<Rightarrow> config \<Rightarrow> bool"
  where
    "inv_begin n (s, tp) = 
        (if s = 0 then inv_begin0 n tp else
         if s = 1 then inv_begin1 n tp else
         if s = 2 then inv_begin2 n tp else
         if s = 3 then inv_begin3 n tp else
         if s = 4 then inv_begin4 n tp 
         else False)"

lemma split_head_repeat[simp]:
  "Oc # list1 = Bk \<up> j @ list2 \<longleftrightarrow> j = 0 \<and> Oc # list1 = list2"
  "Bk # list1 = Oc \<up> j @ list2 \<longleftrightarrow> j = 0 \<and> Bk # list1 = list2"
  "Bk \<up> j @ list2 = Oc # list1 \<longleftrightarrow> j = 0 \<and> Oc # list1 = list2"
  "Oc \<up> j @ list2 = Bk # list1 \<longleftrightarrow> j = 0 \<and> Bk # list1 = list2"
  by(cases j;force)+

lemma inv_begin_step_E: "\<lbrakk>0 < i; 0 < j\<rbrakk> \<Longrightarrow> 
  \<exists>ia>0. ia + j - Suc 0 = i + j \<and> Oc # Oc \<up> i = Oc \<up> ia"
  by (rule_tac x = "Suc i" in exI, simp)

lemma inv_begin_step: 
  assumes "inv_begin n cf"
    and "n > 0"
  shows "inv_begin n (step0 cf tcopy_begin)"
  using assms
  unfolding tcopy_begin_def
  apply(cases cf)
  apply(auto simp: numeral split: if_splits elim:inv_begin_step_E)
  apply(cases "hd (snd (snd cf))";cases "(snd (snd cf))",auto)
  done

lemma inv_begin_steps: 
  assumes "inv_begin n cf"
    and "n > 0"
  shows "inv_begin n (steps0 cf tcopy_begin stp)"
  apply(induct stp)
   apply(simp add: assms)
  apply(auto simp del: steps.simps)
  apply(rule_tac inv_begin_step)
   apply(simp_all add: assms)
  done

lemma begin_partial_correctness:
  assumes "is_final (steps0 (1, [], Oc \<up> n) tcopy_begin stp)"
  shows "0 < n \<Longrightarrow> {inv_begin1 n} tcopy_begin {inv_begin0 n}"
proof(rule_tac Hoare_haltI)
  fix l r
  assume h: "0 < n" "inv_begin1 n (l, r)"
  have "inv_begin n (steps0 (1, [], Oc \<up> n) tcopy_begin stp)"
    using h by (rule_tac inv_begin_steps) (simp_all)
  then show
    "\<exists>stp. is_final (steps0 (1, l, r) tcopy_begin stp) \<and> 
    inv_begin0 n holds_for steps (1, l, r) (tcopy_begin, 0) stp"
    using h assms
    apply(rule_tac x = stp in exI)
    apply(case_tac "(steps0 (1, [], Oc \<up> n) tcopy_begin stp)", simp)
    done
qed

fun measure_begin_state :: "config \<Rightarrow> nat"
  where
    "measure_begin_state (s, l, r) = (if s = 0 then 0 else 5 - s)"

fun measure_begin_step :: "config \<Rightarrow> nat"
  where
    "measure_begin_step (s, l, r) = 
        (if s = 2 then length r else
         if s = 3 then (if r = [] \<or> r = [Bk] then 1 else 0) else
         if s = 4 then length l 
         else 0)"

definition
  "measure_begin = measures [measure_begin_state, measure_begin_step]"

lemma wf_measure_begin:
  shows "wf measure_begin" 
  unfolding measure_begin_def 
  by auto

lemma measure_begin_induct [case_names Step]: 
  "\<lbrakk>\<And>n. \<not> P (f n) \<Longrightarrow> (f (Suc n), (f n)) \<in> measure_begin\<rbrakk> \<Longrightarrow> \<exists>n. P (f n)"
  using wf_measure_begin
  by (metis wf_iff_no_infinite_down_chain)

lemma begin_halts: 
  assumes h: "x > 0"
  shows "\<exists> stp. is_final (steps0 (1, [], Oc \<up> x) tcopy_begin stp)"
proof (induct rule: measure_begin_induct) 
  case (Step n)
  have "\<not> is_final (steps0 (1, [], Oc \<up> x) tcopy_begin n)" by fact
  moreover
  have "inv_begin x (steps0 (1, [], Oc \<up> x) tcopy_begin n)"
    by (rule_tac inv_begin_steps) (simp_all add:  h)
  moreover
  obtain s l r where eq: "(steps0 (1, [], Oc \<up> x) tcopy_begin n) = (s, l, r)"
    by (metis measure_begin_state.cases)
  ultimately 
  have "(step0 (s, l, r) tcopy_begin, s, l, r) \<in> measure_begin"
    apply(auto simp: measure_begin_def tcopy_begin_def numeral split: if_splits)
    apply(subgoal_tac "r = [Oc]")
     apply(auto)
    by (metis cell.exhaust list.exhaust list.sel(3))
  then 
  show "(steps0 (1, [], Oc \<up> x) tcopy_begin (Suc n), steps0 (1, [], Oc \<up> x) tcopy_begin n) \<in> measure_begin"
    using eq by (simp only: step_red)
qed

lemma begin_correct: 
  shows "0 < n \<Longrightarrow> {inv_begin1 n} tcopy_begin {inv_begin0 n}"
  using begin_partial_correctness begin_halts by blast

declare tm_comp.simps [simp del] 
declare adjust.simps[simp del] 
declare shift.simps[simp del]
declare tm_wf.simps[simp del]
declare step.simps[simp del]
declare steps.simps[simp del]

(* tcopy_loop *)

fun 
  inv_loop1_loop :: "nat \<Rightarrow> tape \<Rightarrow> bool" and
  inv_loop1_exit :: "nat \<Rightarrow> tape \<Rightarrow> bool" and
  inv_loop5_loop :: "nat \<Rightarrow> tape \<Rightarrow> bool" and
  inv_loop5_exit :: "nat \<Rightarrow> tape \<Rightarrow> bool" and
  inv_loop6_loop :: "nat \<Rightarrow> tape \<Rightarrow> bool" and
  inv_loop6_exit :: "nat \<Rightarrow> tape \<Rightarrow> bool"
  where
    "inv_loop1_loop n (l, r) = (\<exists> i j. i + j + 1 = n \<and> (l, r) = (Oc\<up>i, Oc#Oc#Bk\<up>j @ Oc\<up>j) \<and> j > 0)"
  | "inv_loop1_exit n (l, r) = (0 < n \<and> (l, r) = ([], Bk#Oc#Bk\<up>n @ Oc\<up>n))"
  | "inv_loop5_loop x (l, r) = 
     (\<exists> i j k t. i + j = Suc x \<and> i > 0 \<and> j > 0 \<and> k + t = j \<and> t > 0 \<and> (l, r) = (Oc\<up>k@Bk\<up>j@Oc\<up>i, Oc\<up>t))"
  | "inv_loop5_exit x (l, r) = 
     (\<exists> i j. i + j = Suc x \<and> i > 0 \<and> j > 0 \<and> (l, r) = (Bk\<up>(j - 1)@Oc\<up>i, Bk # Oc\<up>j))"
  | "inv_loop6_loop x (l, r) = 
     (\<exists> i j k t. i + j = Suc x \<and> i > 0 \<and> k + t + 1 = j \<and> (l, r) = (Bk\<up>k @ Oc\<up>i, Bk\<up>(Suc t) @ Oc\<up>j))"
  | "inv_loop6_exit x (l, r) = 
     (\<exists> i j. i + j = x \<and> j > 0 \<and> (l, r) = (Oc\<up>i, Oc#Bk\<up>j @ Oc\<up>j))"

fun 
  inv_loop0 :: "nat \<Rightarrow> tape \<Rightarrow> bool" and
  inv_loop1 :: "nat \<Rightarrow> tape \<Rightarrow> bool" and
  inv_loop2 :: "nat \<Rightarrow> tape \<Rightarrow> bool" and
  inv_loop3 :: "nat \<Rightarrow> tape \<Rightarrow> bool" and
  inv_loop4 :: "nat \<Rightarrow> tape \<Rightarrow> bool" and
  inv_loop5 :: "nat \<Rightarrow> tape \<Rightarrow> bool" and
  inv_loop6 :: "nat \<Rightarrow> tape \<Rightarrow> bool"
  where
    "inv_loop0 n (l, r) =  (0 < n \<and> (l, r) = ([Bk], Oc # Bk\<up>n @ Oc\<up>n))"
  | "inv_loop1 n (l, r) = (inv_loop1_loop n (l, r) \<or> inv_loop1_exit n (l, r))"
  | "inv_loop2 n (l, r) = (\<exists> i j any. i + j = n \<and> n > 0 \<and> i > 0 \<and> j > 0 \<and> (l, r) = (Oc\<up>i, any#Bk\<up>j@Oc\<up>j))"
  | "inv_loop3 n (l, r) = 
     (\<exists> i j k t. i + j = n \<and> i > 0 \<and> j > 0 \<and>  k + t = Suc j \<and> (l, r) = (Bk\<up>k@Oc\<up>i, Bk\<up>t@Oc\<up>j))"
  | "inv_loop4 n (l, r) = 
     (\<exists> i j k t. i + j = n \<and> i > 0 \<and> j > 0 \<and>  k + t = j \<and> (l, r) = (Oc\<up>k @ Bk\<up>(Suc j)@Oc\<up>i, Oc\<up>t))"
  | "inv_loop5 n (l, r) = (inv_loop5_loop n (l, r) \<or> inv_loop5_exit n (l, r))"
  | "inv_loop6 n (l, r) = (inv_loop6_loop n (l, r) \<or> inv_loop6_exit n (l, r))"

fun inv_loop :: "nat \<Rightarrow> config \<Rightarrow> bool"
  where
    "inv_loop x (s, l, r) = 
         (if s = 0 then inv_loop0 x (l, r)
          else if s = 1 then inv_loop1 x (l, r)
          else if s = 2 then inv_loop2 x (l, r)
          else if s = 3 then inv_loop3 x (l, r)
          else if s = 4 then inv_loop4 x (l, r)
          else if s = 5 then inv_loop5 x (l, r)
          else if s = 6 then inv_loop6 x (l, r)
          else False)"

declare inv_loop.simps[simp del] inv_loop1.simps[simp del]
  inv_loop2.simps[simp del] inv_loop3.simps[simp del] 
  inv_loop4.simps[simp del] inv_loop5.simps[simp del] 
  inv_loop6.simps[simp del]

lemma Bk_no_Oc_repeatE[elim]: "Bk # list = Oc \<up> t \<Longrightarrow> RR"
  by (cases t, auto)

lemma inv_loop3_Bk_empty_via_2[elim]: "\<lbrakk>0 < x; inv_loop2 x (b, [])\<rbrakk> \<Longrightarrow> inv_loop3 x (Bk # b, [])"
  by (auto simp: inv_loop2.simps inv_loop3.simps)

lemma inv_loop3_Bk_empty[elim]: "\<lbrakk>0 < x; inv_loop3 x (b, [])\<rbrakk> \<Longrightarrow> inv_loop3 x (Bk # b, [])"
  by (auto simp: inv_loop3.simps)

lemma inv_loop5_Oc_empty_via_4[elim]: "\<lbrakk>0 < x; inv_loop4 x (b, [])\<rbrakk> \<Longrightarrow> inv_loop5 x (b, [Oc])"
  by(auto simp: inv_loop4.simps inv_loop5.simps;force)

lemma inv_loop1_Bk[elim]: "\<lbrakk>0 < x; inv_loop1 x (b, Bk # list)\<rbrakk> \<Longrightarrow> list = Oc # Bk \<up> x @ Oc \<up> x"
  by (auto simp: inv_loop1.simps)

lemma inv_loop3_Bk_via_2[elim]: "\<lbrakk>0 < x; inv_loop2 x (b, Bk # list)\<rbrakk> \<Longrightarrow> inv_loop3 x (Bk # b, list)"
  by(auto simp: inv_loop2.simps inv_loop3.simps;force)

lemma inv_loop3_Bk_move[elim]: "\<lbrakk>0 < x; inv_loop3 x (b, Bk # list)\<rbrakk> \<Longrightarrow> inv_loop3 x (Bk # b, list)"
  apply(auto simp: inv_loop3.simps)
   apply (rename_tac i j k t)
   apply(rule_tac [!] x = i in exI, 
      rule_tac [!] x = j in exI, simp_all)
   apply(case_tac [!] t, auto)
  done

lemma inv_loop5_Oc_via_4_Bk[elim]: "\<lbrakk>0 < x; inv_loop4 x (b, Bk # list)\<rbrakk> \<Longrightarrow> inv_loop5 x (b, Oc # list)"
  by (auto simp: inv_loop4.simps inv_loop5.simps)

lemma inv_loop6_Bk_via_5[elim]: "\<lbrakk>0 < x; inv_loop5 x ([], Bk # list)\<rbrakk> \<Longrightarrow> inv_loop6 x ([], Bk # Bk # list)"
  by (auto simp: inv_loop6.simps inv_loop5.simps)

lemma inv_loop5_loop_no_Bk[simp]: "inv_loop5_loop x (b, Bk # list) = False"
  by (auto simp: inv_loop5.simps)

lemma inv_loop6_exit_no_Bk[simp]: "inv_loop6_exit x (b, Bk # list) = False"
  by (auto simp: inv_loop6.simps)

declare inv_loop5_loop.simps[simp del]  inv_loop5_exit.simps[simp del]
  inv_loop6_loop.simps[simp del]  inv_loop6_exit.simps[simp del]

lemma inv_loop6_loopBk_via_5[elim]:"\<lbrakk>0 < x; inv_loop5_exit x (b, Bk # list); b \<noteq> []; hd b = Bk\<rbrakk> 
          \<Longrightarrow> inv_loop6_loop x (tl b, Bk # Bk # list)"
  apply(simp only: inv_loop5_exit.simps inv_loop6_loop.simps )
  apply(erule_tac exE)+
  apply(rename_tac i j)
  apply(rule_tac x = i in exI, 
      rule_tac x = j in exI,
      rule_tac x = "j - Suc (Suc 0)" in exI, 
      rule_tac x = "Suc 0" in exI, auto)
   apply(case_tac [!] j, simp_all)
   apply(case_tac [!] "j-1", simp_all)
  done

lemma inv_loop6_loop_no_Oc_Bk[simp]: "inv_loop6_loop x (b, Oc # Bk # list) = False"
  by (auto simp: inv_loop6_loop.simps)

lemma inv_loop6_exit_Oc_Bk_via_5[elim]: "\<lbrakk>x > 0; inv_loop5_exit x (b, Bk # list); b \<noteq> []; hd b = Oc\<rbrakk> \<Longrightarrow> 
  inv_loop6_exit x (tl b, Oc # Bk # list)"
  apply(simp only: inv_loop5_exit.simps inv_loop6_exit.simps)
  apply(erule_tac exE)+
  apply(rule_tac x = "x - 1" in exI, rule_tac x = 1 in exI, simp)
  apply(rename_tac i j)
  apply(case_tac j;case_tac "j-1", auto)
  done

lemma inv_loop6_Bk_tail_via_5[elim]: "\<lbrakk>0 < x; inv_loop5 x (b, Bk # list); b \<noteq> []\<rbrakk> \<Longrightarrow> inv_loop6 x (tl b, hd b # Bk # list)"
  apply(simp add: inv_loop5.simps inv_loop6.simps)
  apply(cases "hd b", simp_all, auto)
  done

lemma inv_loop6_loop_Bk_Bk_drop[elim]: "\<lbrakk>0 < x; inv_loop6_loop x (b, Bk # list); b \<noteq> []; hd b = Bk\<rbrakk>
              \<Longrightarrow> inv_loop6_loop x (tl b, Bk # Bk # list)"
  apply(simp only: inv_loop6_loop.simps)
  apply(erule_tac exE)+
  apply(rename_tac i j k t)
  apply(rule_tac x = i in exI, rule_tac x = j in exI, 
      rule_tac x = "k - 1" in exI, rule_tac x = "Suc t" in exI, auto)
   apply(case_tac [!] k, auto)
  done

lemma inv_loop6_exit_Oc_Bk_via_loop6[elim]: "\<lbrakk>0 < x; inv_loop6_loop x (b, Bk # list); b \<noteq> []; hd b = Oc\<rbrakk> 
        \<Longrightarrow> inv_loop6_exit x (tl b, Oc # Bk # list)"
  apply(simp only: inv_loop6_loop.simps inv_loop6_exit.simps)
  apply(erule_tac exE)+
  apply(rename_tac i j k t)
  apply(rule_tac x = "i - 1" in exI, rule_tac x = j in exI, auto)
   apply(case_tac [!] k, auto)
  done

lemma inv_loop6_Bk_tail[elim]: "\<lbrakk>0 < x; inv_loop6 x (b, Bk # list); b \<noteq> []\<rbrakk> \<Longrightarrow> inv_loop6 x (tl b, hd b # Bk # list)"
  apply(simp add: inv_loop6.simps)
  apply(case_tac "hd b", simp_all, auto)
  done

lemma inv_loop2_Oc_via_1[elim]: "\<lbrakk>0 < x; inv_loop1 x (b, Oc # list)\<rbrakk> \<Longrightarrow> inv_loop2 x (Oc # b, list)"
  apply(auto simp: inv_loop1.simps inv_loop2.simps,force)
  done

lemma inv_loop2_Bk_via_Oc[elim]: "\<lbrakk>0 < x; inv_loop2 x (b, Oc # list)\<rbrakk> \<Longrightarrow> inv_loop2 x (b, Bk # list)"
  by (auto simp: inv_loop2.simps)

lemma inv_loop4_Oc_via_3[elim]: "\<lbrakk>0 < x; inv_loop3 x (b, Oc # list)\<rbrakk> \<Longrightarrow> inv_loop4 x (Oc # b, list)"
  apply(auto simp: inv_loop3.simps inv_loop4.simps)
   apply(rename_tac i j)
   apply(rule_tac [!] x = i in exI, auto)
   apply(rule_tac [!] x = "Suc 0" in exI, rule_tac [!] x = "j - 1" in exI)
   apply(case_tac [!] j, auto)
  done

lemma inv_loop4_Oc_move[elim]:
  assumes "0 < x" "inv_loop4 x (b, Oc # list)"
  shows "inv_loop4 x (Oc # b, list)"
proof -
  from assms[unfolded inv_loop4.simps] obtain i j k t where
    "i + j = x"
    "0 < i" "0 < j" "k + t = j" "(b, Oc # list) = (Oc \<up> k @ Bk \<up> Suc j @ Oc \<up> i, Oc \<up> t)"
    by auto  
  thus ?thesis unfolding inv_loop4.simps
    apply(rule_tac [!] x = "i" in exI,rule_tac [!] x = "j" in exI)
    apply(rule_tac [!] x = "Suc k" in exI,rule_tac [!] x = "t - 1" in exI)
    by(cases t,auto)
qed

lemma inv_loop5_exit_no_Oc[simp]: "inv_loop5_exit x (b, Oc # list) = False"
  by (auto simp: inv_loop5_exit.simps)

lemma inv_loop5_exit_Bk_Oc_via_loop[elim]: " \<lbrakk>inv_loop5_loop x (b, Oc # list); b \<noteq> []; hd b = Bk\<rbrakk>
  \<Longrightarrow> inv_loop5_exit x (tl b, Bk # Oc # list)"
  apply(simp only: inv_loop5_loop.simps inv_loop5_exit.simps)
  apply(erule_tac exE)+
  apply(rename_tac i j k t)
  apply(rule_tac x = i in exI)
  apply(case_tac k, auto)
  done

lemma inv_loop5_loop_Oc_Oc_drop[elim]: "\<lbrakk>inv_loop5_loop x (b, Oc # list); b \<noteq> []; hd b = Oc\<rbrakk> 
           \<Longrightarrow> inv_loop5_loop x (tl b, Oc # Oc # list)"
  apply(simp only:  inv_loop5_loop.simps)
  apply(erule_tac exE)+
  apply(rename_tac i j k t)
  apply(rule_tac x = i in exI, rule_tac x = j in exI)
  apply(rule_tac x = "k - 1" in exI, rule_tac x = "Suc t" in exI)
  apply(case_tac k, auto)
  done

lemma inv_loop5_Oc_tl[elim]: "\<lbrakk>inv_loop5 x (b, Oc # list); b \<noteq> []\<rbrakk> \<Longrightarrow> inv_loop5 x (tl b, hd b # Oc # list)"
  apply(simp add: inv_loop5.simps)
  apply(cases "hd b", simp_all, auto)
  done

lemma inv_loop1_Bk_Oc_via_6[elim]: "\<lbrakk>0 < x; inv_loop6 x ([], Oc # list)\<rbrakk> \<Longrightarrow> inv_loop1 x ([], Bk # Oc # list)"
  by(auto simp: inv_loop6.simps inv_loop1.simps inv_loop6_loop.simps inv_loop6_exit.simps)

lemma inv_loop1_Oc_via_6[elim]: "\<lbrakk>0 < x; inv_loop6 x (b, Oc # list); b \<noteq> []\<rbrakk> 
           \<Longrightarrow> inv_loop1 x (tl b, hd b # Oc # list)"
  by(auto simp: inv_loop6.simps inv_loop1.simps inv_loop6_loop.simps inv_loop6_exit.simps)


lemma inv_loop_nonempty[simp]:
  "inv_loop1 x (b, []) = False"
  "inv_loop2 x ([], b) = False"
  "inv_loop2 x (l', []) = False"
  "inv_loop3 x (b, []) = False"
  "inv_loop4 x ([], b) = False"
  "inv_loop5 x ([], list) = False"
  "inv_loop6 x ([], Bk # xs) = False"
  by (auto simp: inv_loop1.simps inv_loop2.simps inv_loop3.simps inv_loop4.simps 
      inv_loop5.simps inv_loop6.simps inv_loop5_exit.simps inv_loop5_loop.simps
      inv_loop6_loop.simps)

lemma inv_loop_nonemptyE[elim]:
  "\<lbrakk>inv_loop5 x (b, [])\<rbrakk> \<Longrightarrow> RR" "inv_loop6 x (b, []) \<Longrightarrow> RR" 
  "\<lbrakk>inv_loop1 x (b, Bk # list)\<rbrakk> \<Longrightarrow> b = []"
  by (auto simp: inv_loop4.simps inv_loop5.simps inv_loop5_exit.simps inv_loop5_loop.simps
      inv_loop6.simps inv_loop6_exit.simps inv_loop6_loop.simps inv_loop1.simps)

lemma inv_loop6_Bk_Bk_drop[elim]: "\<lbrakk>inv_loop6 x ([], Bk # list)\<rbrakk> \<Longrightarrow> inv_loop6 x ([], Bk # Bk # list)"
  by (simp)

lemma inv_loop_step: 
  "\<lbrakk>inv_loop x cf; x > 0\<rbrakk> \<Longrightarrow> inv_loop x (step cf (tcopy_loop, 0))"
  apply(cases cf, cases "snd (snd cf)"; cases "hd (snd (snd cf))")
     apply(auto simp: inv_loop.simps step.simps tcopy_loop_def numeral split: if_splits)
  done

lemma inv_loop_steps:
  "\<lbrakk>inv_loop x cf; x > 0\<rbrakk> \<Longrightarrow> inv_loop x (steps cf (tcopy_loop, 0) stp)"
  apply(induct stp, simp add: steps.simps, simp)
  apply(erule_tac inv_loop_step, simp)
  done

fun loop_stage :: "config \<Rightarrow> nat"
  where
    "loop_stage (s, l, r) = (if s = 0 then 0
                           else (Suc (length (takeWhile (\<lambda>a. a = Oc) (rev l @ r)))))"

fun loop_state :: "config \<Rightarrow> nat"
  where
    "loop_state (s, l, r) = (if s = 2 \<and> hd r = Oc then 0
                           else if s = 1 then 1
                           else 10 - s)"

fun loop_step :: "config \<Rightarrow> nat"
  where
    "loop_step (s, l, r) = (if s = 3 then length r
                          else if s = 4 then length r
                          else if s = 5 then length l 
                          else if s = 6 then length l
                          else 0)"

definition measure_loop :: "(config \<times> config) set"
  where
    "measure_loop = measures [loop_stage, loop_state, loop_step]"

lemma wf_measure_loop: "wf measure_loop"
  unfolding measure_loop_def
  by (auto)

lemma measure_loop_induct [case_names Step]: 
  "\<lbrakk>\<And>n. \<not> P (f n) \<Longrightarrow> (f (Suc n), (f n)) \<in> measure_loop\<rbrakk> \<Longrightarrow> \<exists>n. P (f n)"
  using wf_measure_loop
  by (metis wf_iff_no_infinite_down_chain)

lemma inv_loop4_not_just_Oc[elim]: 
  "\<lbrakk>inv_loop4 x (l', []);
  length (takeWhile (\<lambda>a. a = Oc) (rev l' @ [Oc])) \<noteq> 
  length (takeWhile (\<lambda>a. a = Oc) (rev l'))\<rbrakk>
  \<Longrightarrow> RR"
  "\<lbrakk>inv_loop4 x (l', Bk # list);
   length (takeWhile (\<lambda>a. a = Oc) (rev l' @ Oc # list)) \<noteq> 
    length (takeWhile (\<lambda>a. a = Oc) (rev l' @ Bk # list))\<rbrakk>
    \<Longrightarrow> RR"
   apply(auto simp: inv_loop4.simps)
  apply(rename_tac i j)
  apply(case_tac [!] j, simp_all add: List.takeWhile_tail)
  done

lemma takeWhile_replicate_append: 
  "P a \<Longrightarrow> takeWhile P (a\<up>x @ ys) = a\<up>x @ takeWhile P ys"
  by (induct x, auto)

lemma takeWhile_replicate: 
  "P a \<Longrightarrow> takeWhile P (a\<up>x) = a\<up>x"
  by (induct x, auto)

lemma inv_loop5_Bk_E[elim]: 
  "\<lbrakk>inv_loop5 x (l', Bk # list); l' \<noteq> []; 
   length (takeWhile (\<lambda>a. a = Oc) (rev (tl l') @ hd l' # Bk # list)) \<noteq>
   length (takeWhile (\<lambda>a. a = Oc) (rev l' @ Bk # list))\<rbrakk>
   \<Longrightarrow> RR"
  apply(cases "length list";cases "length list - 1"
      ,auto simp: inv_loop5.simps inv_loop5_exit.simps
      takeWhile_replicate_append takeWhile_replicate)
   apply(cases "length list - 2"; force simp add: List.takeWhile_tail)+
  done

lemma inv_loop1_hd_Oc[elim]: "\<lbrakk>inv_loop1 x (l', Oc # list)\<rbrakk> \<Longrightarrow> hd list = Oc"
  by (auto simp: inv_loop1.simps)

lemma inv_loop6_not_just_Bk[dest!]: 
  "\<lbrakk>length (takeWhile P (rev (tl l') @ hd l' # list)) \<noteq> 
  length (takeWhile P (rev l' @ list))\<rbrakk>
  \<Longrightarrow> l' = []"
  apply(cases l', simp_all)
  done

lemma inv_loop2_OcE[elim]:
  "\<lbrakk>inv_loop2 x (l', Oc # list); l' \<noteq> []\<rbrakk> \<Longrightarrow> 
  length (takeWhile (\<lambda>a. a = Oc) (rev l' @ Bk # list)) <
  length (takeWhile (\<lambda>a. a = Oc) (rev l' @ Oc # list))"
  apply(auto simp: inv_loop2.simps takeWhile_tail takeWhile_replicate_append
      takeWhile_replicate)
  done

lemma loop_halts: 
  assumes h: "n > 0" "inv_loop n (1, l, r)"
  shows "\<exists> stp. is_final (steps0 (1, l, r) tcopy_loop stp)"
proof (induct rule: measure_loop_induct) 
  case (Step stp)
  have "\<not> is_final (steps0 (1, l, r) tcopy_loop stp)" by fact
  moreover
  have "inv_loop n (steps0 (1, l, r) tcopy_loop stp)"
    by (rule_tac inv_loop_steps) (simp_all only: h)
  moreover
  obtain s l' r' where eq: "(steps0 (1, l, r) tcopy_loop stp) = (s, l', r')"
    by (metis measure_begin_state.cases)
  ultimately 
  have "(step0 (s, l', r') tcopy_loop, s, l', r') \<in> measure_loop"
    using h(1)
    apply(cases r';cases "hd r'")
       apply(auto simp: inv_loop.simps step.simps tcopy_loop_def numeral measure_loop_def split: if_splits)
    done
  then 
  show "(steps0 (1, l, r) tcopy_loop (Suc stp), steps0 (1, l, r) tcopy_loop stp) \<in> measure_loop"
    using eq by (simp only: step_red)
qed

lemma loop_correct:
  assumes "0 < n"
  shows "{inv_loop1 n} tcopy_loop {inv_loop0 n}"
  using assms
proof(rule_tac Hoare_haltI)
  fix l r
  assume h: "0 < n" "inv_loop1 n (l, r)"
  then obtain stp where k: "is_final (steps0 (1, l, r) tcopy_loop stp)" 
    using loop_halts
    apply(simp add: inv_loop.simps)
    apply(blast)
    done
  moreover
  have "inv_loop n (steps0 (1, l, r) tcopy_loop stp)"
    using h 
    by (rule_tac inv_loop_steps) (simp_all add: inv_loop.simps)
  ultimately show
    "\<exists>stp. is_final (steps0 (1, l, r) tcopy_loop stp) \<and> 
    inv_loop0 n holds_for steps0 (1, l, r) tcopy_loop stp"
    using h(1) 
    apply(rule_tac x = stp in exI)
    apply(case_tac "(steps0 (1, l, r) tcopy_loop stp)")
    apply(simp add: inv_loop.simps)
    done
qed




(* tcopy_end *)

fun
  inv_end5_loop :: "nat \<Rightarrow> tape \<Rightarrow> bool" and
  inv_end5_exit :: "nat \<Rightarrow> tape \<Rightarrow> bool" 
  where  
    "inv_end5_loop x (l, r) = 
     (\<exists> i j. i + j = x \<and> x > 0 \<and> j > 0 \<and> l = Oc\<up>i @ [Bk] \<and> r = Oc\<up>j @ Bk # Oc\<up>x)"
  | "inv_end5_exit x (l, r) = (x > 0 \<and> l = [] \<and> r = Bk # Oc\<up>x @ Bk # Oc\<up>x)"

fun 
  inv_end0 :: "nat \<Rightarrow> tape \<Rightarrow>  bool" and
  inv_end1 :: "nat \<Rightarrow> tape \<Rightarrow> bool" and
  inv_end2 :: "nat \<Rightarrow> tape \<Rightarrow> bool" and
  inv_end3 :: "nat \<Rightarrow> tape \<Rightarrow> bool" and
  inv_end4 :: "nat \<Rightarrow> tape \<Rightarrow> bool" and 
  inv_end5 :: "nat \<Rightarrow> tape \<Rightarrow> bool" 
  where
    "inv_end0 n (l, r) = (n > 0 \<and> (l, r) = ([Bk], Oc\<up>n @ Bk # Oc\<up>n))"
  | "inv_end1 n (l, r) = (n > 0 \<and> (l, r) = ([Bk], Oc # Bk\<up>n @ Oc\<up>n))"
  | "inv_end2 n (l, r) = (\<exists> i j. i + j = Suc n \<and> n > 0 \<and> l = Oc\<up>i @ [Bk] \<and> r = Bk\<up>j @ Oc\<up>n)"
  | "inv_end3 n (l, r) =
     (\<exists> i j. n > 0 \<and> i + j = n \<and> l = Oc\<up>i @ [Bk] \<and> r = Oc # Bk\<up>j@ Oc\<up>n)"
  | "inv_end4 n (l, r) = (\<exists> any. n > 0 \<and> l = Oc\<up>n @ [Bk] \<and> r = any#Oc\<up>n)"
  | "inv_end5 n (l, r) = (inv_end5_loop n (l, r) \<or> inv_end5_exit n (l, r))"

fun 
  inv_end :: "nat \<Rightarrow> config \<Rightarrow> bool"
  where
    "inv_end n (s, l, r) = (if s = 0 then inv_end0 n (l, r)
                          else if s = 1 then inv_end1 n (l, r)
                          else if s = 2 then inv_end2 n (l, r)
                          else if s = 3 then inv_end3 n (l, r)
                          else if s = 4 then inv_end4 n (l, r)
                          else if s = 5 then inv_end5 n (l, r)
                          else False)"

declare inv_end.simps[simp del] inv_end1.simps[simp del]
  inv_end0.simps[simp del] inv_end2.simps[simp del]
  inv_end3.simps[simp del] inv_end4.simps[simp del]
  inv_end5.simps[simp del]

lemma inv_end_nonempty[simp]:
  "inv_end1 x (b, []) = False"
  "inv_end1 x ([], list) = False"
  "inv_end2 x (b, []) = False"
  "inv_end3 x (b, []) = False"
  "inv_end4 x (b, []) = False"
  "inv_end5 x (b, []) = False"
  "inv_end5 x ([], Oc # list) = False"
  by (auto simp: inv_end1.simps inv_end2.simps inv_end3.simps inv_end4.simps inv_end5.simps)

lemma inv_end0_Bk_via_1[elim]: "\<lbrakk>0 < x; inv_end1 x (b, Bk # list); b \<noteq> []\<rbrakk>
  \<Longrightarrow> inv_end0 x (tl b, hd b # Bk # list)"
  by (auto simp: inv_end1.simps inv_end0.simps)

lemma inv_end3_Oc_via_2[elim]: "\<lbrakk>0 < x; inv_end2 x (b, Bk # list)\<rbrakk> 
  \<Longrightarrow> inv_end3 x (b, Oc # list)"
  apply(auto simp: inv_end2.simps inv_end3.simps)
  by (metis Cons_replicate_eq One_nat_def Suc_inject Suc_pred add_Suc_right cell.distinct(1)
      empty_replicate list.sel(3) neq0_conv self_append_conv2 tl_append2 tl_replicate)

lemma inv_end2_Bk_via_3[elim]: "\<lbrakk>0 < x; inv_end3 x (b, Bk # list)\<rbrakk> \<Longrightarrow> inv_end2 x (Bk # b, list)"
  by (auto simp: inv_end2.simps inv_end3.simps)

lemma inv_end5_Bk_via_4[elim]: "\<lbrakk>0 < x; inv_end4 x ([], Bk # list)\<rbrakk> \<Longrightarrow> 
  inv_end5 x ([], Bk # Bk # list)"
  by (auto simp: inv_end4.simps inv_end5.simps)

lemma inv_end5_Bk_tail_via_4[elim]: "\<lbrakk>0 < x; inv_end4 x (b, Bk # list); b \<noteq> []\<rbrakk> \<Longrightarrow> 
  inv_end5 x (tl b, hd b # Bk # list)"
  apply(auto simp: inv_end4.simps inv_end5.simps)
  apply(rule_tac x = 1 in exI, simp)
  done

lemma inv_end0_Bk_via_5[elim]: "\<lbrakk>0 < x; inv_end5 x (b, Bk # list)\<rbrakk> \<Longrightarrow> inv_end0 x (Bk # b, list)"
  by(auto simp: inv_end5.simps inv_end0.simps gr0_conv_Suc)

lemma inv_end2_Oc_via_1[elim]: "\<lbrakk>0 < x; inv_end1 x (b, Oc # list)\<rbrakk> \<Longrightarrow> inv_end2 x (Oc # b, list)"
  by (auto simp: inv_end1.simps inv_end2.simps)

lemma inv_end4_Bk_Oc_via_2[elim]: "\<lbrakk>0 < x; inv_end2 x ([], Oc # list)\<rbrakk> \<Longrightarrow>
               inv_end4 x ([], Bk # Oc # list)"
  by (auto simp: inv_end2.simps inv_end4.simps)

lemma inv_end4_Oc_via_2[elim]:  "\<lbrakk>0 < x; inv_end2 x (b, Oc # list); b \<noteq> []\<rbrakk> \<Longrightarrow>
  inv_end4 x (tl b, hd b # Oc # list)"
  by(auto simp: inv_end2.simps inv_end4.simps gr0_conv_Suc)

lemma inv_end2_Oc_via_3[elim]: "\<lbrakk>0 < x; inv_end3 x (b, Oc # list)\<rbrakk> \<Longrightarrow> inv_end2 x (Oc # b, list)"
  by (auto simp: inv_end2.simps inv_end3.simps)

lemma inv_end4_Bk_via_Oc[elim]: "\<lbrakk>0 < x; inv_end4 x (b, Oc # list)\<rbrakk> \<Longrightarrow> inv_end4 x (b, Bk # list)"
  by (auto simp: inv_end2.simps inv_end4.simps)

lemma inv_end5_Bk_drop_Oc[elim]: "\<lbrakk>0 < x; inv_end5 x ([], Oc # list)\<rbrakk> \<Longrightarrow> inv_end5 x ([], Bk # Oc # list)"
  by (auto simp: inv_end2.simps inv_end5.simps)

declare inv_end5_loop.simps[simp del]
  inv_end5_exit.simps[simp del]

lemma inv_end5_exit_no_Oc[simp]: "inv_end5_exit x (b, Oc # list) = False"
  by (auto simp: inv_end5_exit.simps)

lemma inv_end5_loop_no_Bk_Oc[simp]: "inv_end5_loop x (tl b, Bk # Oc # list) = False"
  by (auto simp: inv_end5_loop.simps)

lemma inv_end5_exit_Bk_Oc_via_loop[elim]:
  "\<lbrakk>0 < x; inv_end5_loop x (b, Oc # list); b \<noteq> []; hd b = Bk\<rbrakk> \<Longrightarrow>
  inv_end5_exit x (tl b, Bk # Oc # list)"
  apply(auto simp: inv_end5_loop.simps inv_end5_exit.simps)
  using hd_replicate apply fastforce
  by (metis cell.distinct(1) hd_append2 hd_replicate list.sel(3) self_append_conv2
      split_head_repeat(2))

lemma inv_end5_loop_Oc_Oc_drop[elim]: 
  "\<lbrakk>0 < x; inv_end5_loop x (b, Oc # list); b \<noteq> []; hd b = Oc\<rbrakk> \<Longrightarrow>
  inv_end5_loop x (tl b, Oc # Oc # list)"
  apply(simp only: inv_end5_loop.simps inv_end5_exit.simps)
  apply(erule_tac exE)+
  apply(rename_tac i j)
  apply(rule_tac x = "i - 1" in exI, 
      rule_tac x = "Suc j" in exI, auto)
   apply(case_tac [!] i, simp_all)
  done

lemma inv_end5_Oc_tail[elim]: "\<lbrakk>0 < x; inv_end5 x (b, Oc # list); b \<noteq> []\<rbrakk> \<Longrightarrow> 
  inv_end5 x (tl b, hd b # Oc # list)"
  apply(simp add: inv_end2.simps inv_end5.simps)
  apply(case_tac "hd b", simp_all, auto)
  done

lemma inv_end_step:
  "\<lbrakk>x > 0; inv_end x cf\<rbrakk> \<Longrightarrow> inv_end x (step cf (tcopy_end, 0))"
  apply(cases cf, cases "snd (snd cf)"; cases "hd (snd (snd cf))")
     apply(auto simp: inv_end.simps step.simps tcopy_end_def numeral split: if_splits)
  done

lemma inv_end_steps:
  "\<lbrakk>x > 0; inv_end x cf\<rbrakk> \<Longrightarrow> inv_end x (steps cf (tcopy_end, 0) stp)"
  apply(induct stp, simp add:steps.simps, simp)
  apply(erule_tac inv_end_step, simp)
  done

fun end_state :: "config \<Rightarrow> nat"
  where
    "end_state (s, l, r) = 
       (if s = 0 then 0
        else if s = 1 then 5
        else if s = 2 \<or> s = 3 then 4
        else if s = 4 then 3 
        else if s = 5 then 2
        else 0)"

fun end_stage :: "config \<Rightarrow> nat"
  where
    "end_stage (s, l, r) = 
          (if s = 2 \<or> s = 3 then (length r) else 0)"

fun end_step :: "config \<Rightarrow> nat"
  where
    "end_step (s, l, r) = 
         (if s = 4 then (if hd r = Oc then 1 else 0)
          else if s = 5 then length l
          else if s = 2 then 1
          else if s = 3 then 0
          else 0)"

definition end_LE :: "(config \<times> config) set"
  where
    "end_LE = measures [end_state, end_stage, end_step]"

lemma wf_end_le: "wf end_LE"
  unfolding end_LE_def by auto

lemma halt_lemma: 
  "\<lbrakk>wf LE; \<forall>n. (\<not> P (f n) \<longrightarrow> (f (Suc n), (f n)) \<in> LE)\<rbrakk> \<Longrightarrow> \<exists>n. P (f n)"
  by (metis wf_iff_no_infinite_down_chain)

lemma end_halt: 
  "\<lbrakk>x > 0; inv_end x (Suc 0, l, r)\<rbrakk> \<Longrightarrow> 
      \<exists> stp. is_final (steps (Suc 0, l, r) (tcopy_end, 0) stp)"
proof(rule halt_lemma[OF wf_end_le])
  assume great: "0 < x"
    and inv_start: "inv_end x (Suc 0, l, r)"
  show "\<forall>n. \<not> is_final (steps (Suc 0, l, r) (tcopy_end, 0) n) \<longrightarrow> 
    (steps (Suc 0, l, r) (tcopy_end, 0) (Suc n), steps (Suc 0, l, r) (tcopy_end, 0) n) \<in> end_LE"
  proof(rule_tac allI, rule_tac impI)
    fix n
    assume notfinal: "\<not> is_final (steps (Suc 0, l, r) (tcopy_end, 0) n)"
    obtain s' l' r' where d: "steps (Suc 0, l, r) (tcopy_end, 0) n = (s', l', r')"
      apply(case_tac "steps (Suc 0, l, r) (tcopy_end, 0) n", auto)
      done
    hence "inv_end x (s', l', r') \<and> s' \<noteq> 0"
      using great inv_start notfinal
      apply(drule_tac stp = n in inv_end_steps, auto)
      done
    hence "(step (s', l', r') (tcopy_end, 0), s', l', r') \<in> end_LE"
      apply(cases r'; cases "hd r'")
         apply(auto simp: inv_end.simps step.simps tcopy_end_def numeral end_LE_def split: if_splits)
      done
    thus "(steps (Suc 0, l, r) (tcopy_end, 0) (Suc n), 
      steps (Suc 0, l, r) (tcopy_end, 0) n) \<in> end_LE"
      using d
      by simp
  qed
qed

lemma end_correct:
  "n > 0 \<Longrightarrow> {inv_end1 n} tcopy_end {inv_end0 n}"
proof(rule_tac Hoare_haltI)
  fix l r
  assume h: "0 < n"
    "inv_end1 n (l, r)"
  then have "\<exists> stp. is_final (steps0 (1, l, r) tcopy_end stp)"
    by (simp add: end_halt inv_end.simps)
  then obtain stp where "is_final (steps0 (1, l, r) tcopy_end stp)" ..
  moreover have "inv_end n (steps0 (1, l, r) tcopy_end stp)"
    apply(rule_tac inv_end_steps)
    using h by(simp_all add: inv_end.simps)
  ultimately show
    "\<exists>stp. is_final (steps (1, l, r) (tcopy_end, 0) stp) \<and> 
    inv_end0 n holds_for steps (1, l, r) (tcopy_end, 0) stp"        
    using h
    apply(rule_tac x = stp in exI)
    apply(cases "(steps0 (1, l, r) tcopy_end stp)") 
    apply(simp add: inv_end.simps)
    done
qed

(* tcopy *)

lemma tm_wf_tcopy[intro]:
  "tm_wf (tcopy_begin, 0)"
  "tm_wf (tcopy_loop, 0)"
  "tm_wf (tcopy_end, 0)"
  by (auto simp: tm_wf.simps tcopy_end_def tcopy_loop_def tcopy_begin_def)

lemma tcopy_correct1: 
  assumes "0 < x"
  shows "{inv_begin1 x} tcopy {inv_end0 x}"
proof -
  have "{inv_begin1 x} tcopy_begin {inv_begin0 x}"
    by (metis assms begin_correct) 
  moreover 
  have "inv_begin0 x \<mapsto> inv_loop1 x"
    unfolding assert_imp_def
    unfolding inv_begin0.simps inv_loop1.simps
    unfolding inv_loop1_loop.simps inv_loop1_exit.simps
    apply(auto simp add: numeral Cons_eq_append_conv)
    by (rule_tac x = "Suc 0" in exI, auto)
  ultimately have "{inv_begin1 x} tcopy_begin {inv_loop1 x}"
    by (rule_tac Hoare_consequence) (auto)
  moreover
  have "{inv_loop1 x} tcopy_loop {inv_loop0 x}"
    by (metis assms loop_correct) 
  ultimately 
  have "{inv_begin1 x} (tcopy_begin |+| tcopy_loop) {inv_loop0 x}"
    by (rule_tac Hoare_plus_halt) (auto)
  moreover 
  have "{inv_end1 x} tcopy_end {inv_end0 x}"
    by (metis assms end_correct) 
  moreover 
  have "inv_loop0 x = inv_end1 x"
    by(auto simp: inv_end1.simps inv_loop1.simps assert_imp_def)
  ultimately 
  show "{inv_begin1 x} tcopy {inv_end0 x}"
    unfolding tcopy_def
    by (rule_tac Hoare_plus_halt) (auto)
qed

abbreviation (input)
  "pre_tcopy n \<equiv> \<lambda>tp. tp = ([]::cell list, Oc \<up> (Suc n))"
abbreviation (input)
  "post_tcopy n \<equiv> \<lambda>tp. tp= ([Bk], <(n, n::nat)>)"

lemma tcopy_correct:
  shows "{pre_tcopy n} tcopy {post_tcopy n}"
proof -
  have "{inv_begin1 (Suc n)} tcopy {inv_end0 (Suc n)}"
    by (rule tcopy_correct1) (simp)
  moreover
  have "pre_tcopy n = inv_begin1 (Suc n)"
    by (auto)
  moreover
  have "inv_end0 (Suc n) = post_tcopy n"
    unfolding fun_eq_iff
    by (auto simp add: inv_end0.simps tape_of_nat_def tape_of_prod_def)
  ultimately
  show "{pre_tcopy n} tcopy {post_tcopy n}" 
    by simp
qed


section \<open>The {\em Dithering} Turing Machine\<close>

text \<open>
  The {\em Dithering} TM, when the input is \<open>1\<close>, it will loop forever, otherwise, it will
  terminate.
\<close>

definition dither :: "instr list"
  where
    "dither \<equiv> [(W0, 1), (R, 2), (L, 1), (L, 0)] "

(* invariants of dither *)
abbreviation (input)
  "dither_halt_inv \<equiv> \<lambda>tp. \<exists>k. tp = (Bk \<up> k, <1::nat>)"

abbreviation (input)
  "dither_unhalt_inv \<equiv> \<lambda>tp. \<exists>k. tp = (Bk \<up> k, <0::nat>)"

lemma dither_loops_aux: 
  "(steps0 (1, Bk \<up> m, [Oc]) dither stp = (1, Bk \<up> m, [Oc])) \<or> 
   (steps0 (1, Bk \<up> m, [Oc]) dither stp = (2, Oc # Bk \<up> m, []))"
  apply(induct stp)
   apply(auto simp: steps.simps step.simps dither_def numeral)
  done

lemma dither_loops:
  shows "{dither_unhalt_inv} dither \<up>" 
  apply(rule Hoare_unhaltI)
  using dither_loops_aux
  apply(auto simp add: numeral tape_of_nat_def)
  by (metis Suc_neq_Zero is_final_eq)

lemma dither_halts_aux: 
  shows "steps0 (1, Bk \<up> m, [Oc, Oc]) dither 2 = (0, Bk \<up> m, [Oc, Oc])"
  unfolding dither_def
  by (simp add: steps.simps step.simps numeral)

lemma dither_halts:
  shows "{dither_halt_inv} dither {dither_halt_inv}" 
  apply(rule Hoare_haltI)
  using dither_halts_aux
  apply(auto simp add: tape_of_nat_def)
  by (metis (lifting, mono_tags) holds_for.simps is_final_eq)


section \<open>The diagnal argument below shows the undecidability of Halting problem\<close>

text \<open>
  \<open>halts tp x\<close> means TM \<open>tp\<close> terminates on input \<open>x\<close>
  and the final configuration is standard.
\<close>

definition halts :: "tprog0 \<Rightarrow> nat list \<Rightarrow> bool"
  where
    "halts p ns \<equiv> {(\<lambda>tp. tp = ([], <ns>))} p {(\<lambda>tp. (\<exists>k n l. tp = (Bk \<up> k,  <n::nat> @ Bk \<up> l)))}"

lemma tm_wf0_tcopy[intro, simp]: "tm_wf0 tcopy"
  by (auto simp: tcopy_def)

lemma tm_wf0_dither[intro, simp]: "tm_wf0 dither"
  by (auto simp: tm_wf.simps dither_def)

text \<open>
  The following locale specifies that TM \<open>H\<close> can be used to solve 
  the {\em Halting Problem} and \<open>False\<close> is going to be derived 
  under this locale. Therefore, the undecidability of {\em Halting Problem}
  is established. 
\<close>

locale uncomputable = 
  (* The coding function of TM, interestingly, the detailed definition of this 
  funciton @{text "code"} does not affect the final result. *)
  fixes code :: "instr list \<Rightarrow> nat" 
    (* 
  The TM @{text "H"} is the one which is assummed being able to solve the Halting problem.
  *)
    and H :: "instr list"
  assumes h_wf[intro]: "tm_wf0 H"
    (*
  The following two assumptions specifies that @{text "H"} does solve the Halting problem.
  *)
    and h_case: 
    "\<And> M ns. halts M ns \<Longrightarrow> {(\<lambda>tp. tp = ([Bk], <(code M, ns)>))} H {(\<lambda>tp. \<exists>k. tp = (Bk \<up> k, <0::nat>))}"
    and nh_case: 
    "\<And> M ns. \<not> halts M ns \<Longrightarrow> {(\<lambda>tp. tp = ([Bk], <(code M, ns)>))} H {(\<lambda>tp. \<exists>k. tp = (Bk \<up> k, <1::nat>))}"
begin

(* invariants for H *)
abbreviation (input)
  "pre_H_inv M ns \<equiv> \<lambda>tp. tp = ([Bk], <(code M, ns::nat list)>)"

abbreviation (input)
  "post_H_halt_inv \<equiv> \<lambda>tp. \<exists>k. tp = (Bk \<up> k, <1::nat>)"

abbreviation (input)
  "post_H_unhalt_inv \<equiv> \<lambda>tp. \<exists>k. tp = (Bk \<up> k, <0::nat>)"


lemma H_halt_inv:
  assumes "\<not> halts M ns" 
  shows "{pre_H_inv M ns} H {post_H_halt_inv}"
  using assms nh_case by auto

lemma H_unhalt_inv:
  assumes "halts M ns" 
  shows "{pre_H_inv M ns} H {post_H_unhalt_inv}"
  using assms h_case by auto

(* TM that produces the contradiction and its code *)

definition
  "tcontra \<equiv> (tcopy |+| H) |+| dither"
abbreviation
  "code_tcontra \<equiv> code tcontra"

(* assume tcontra does not halt on its code *)
lemma tcontra_unhalt: 
  assumes "\<not> halts tcontra [code tcontra]"
  shows "False"
proof -
  (* invariants *)
  define P1 where "P1 \<equiv> \<lambda>tp. tp = ([]::cell list, <code_tcontra>)"
  define P2 where "P2 \<equiv> \<lambda>tp. tp = ([Bk], <(code_tcontra, code_tcontra)>)"
  define P3 where "P3 \<equiv> \<lambda>tp. \<exists>k. tp = (Bk \<up> k, <1::nat>)"

(*
  {P1} tcopy {P2}  {P2} H {P3} 
  ----------------------------
     {P1} (tcopy |+| H) {P3}     {P3} dither {P3}
  ------------------------------------------------
                 {P1} tcontra {P3}
  *)

  have H_wf: "tm_wf0 (tcopy |+| H)" by auto

(* {P1} (tcopy |+| H) {P3} *)
  have first: "{P1} (tcopy |+| H) {P3}" 
  proof (cases rule: Hoare_plus_halt)
    case A_halt (* of tcopy *)
    show "{P1} tcopy {P2}" unfolding P1_def P2_def tape_of_nat_def
      by (rule tcopy_correct)
  next
    case B_halt (* of H *)
    show "{P2} H {P3}"
      unfolding P2_def P3_def 
      using H_halt_inv[OF assms]
      by (simp add: tape_of_prod_def tape_of_list_def)
  qed (simp)

(* {P3} dither {P3} *)
  have second: "{P3} dither {P3}" unfolding P3_def 
    by (rule dither_halts)

(* {P1} tcontra {P3} *)
  have "{P1} tcontra {P3}" 
    unfolding tcontra_def
    by (rule Hoare_plus_halt[OF first second H_wf])

  with assms show "False"
    unfolding P1_def P3_def
    unfolding halts_def
    unfolding Hoare_halt_def 
    apply(auto) apply(rename_tac n)
    apply(drule_tac x = n in spec)
    apply(case_tac "steps0 (Suc 0, [], <code tcontra>) tcontra n")
    apply(auto simp add: tape_of_list_def)
    by (metis append_Nil2 replicate_0)
qed

(* asumme tcontra halts on its code *)
lemma tcontra_halt: 
  assumes "halts tcontra [code tcontra]"
  shows "False"
proof - 
  (* invariants *)
  define P1 where "P1 \<equiv> \<lambda>tp. tp = ([]::cell list, <code_tcontra>)"
  define P2 where "P2 \<equiv> \<lambda>tp. tp = ([Bk], <(code_tcontra, code_tcontra)>)"
  define Q3 where "Q3 \<equiv> \<lambda>tp. \<exists>k. tp = (Bk \<up> k, <0::nat>)"

(*
  {P1} tcopy {P2}  {P2} H {Q3} 
  ----------------------------
     {P1} (tcopy |+| H) {Q3}     {Q3} dither loops
  ------------------------------------------------
               {P1} tcontra loops
  *)

  have H_wf: "tm_wf0 (tcopy |+| H)" by auto

(* {P1} (tcopy |+| H) {Q3} *)
  have first: "{P1} (tcopy |+| H) {Q3}" 
  proof (cases rule: Hoare_plus_halt)
    case A_halt (* of tcopy *)
    show "{P1} tcopy {P2}" unfolding P1_def P2_def tape_of_nat_def
      by (rule tcopy_correct)
  next
    case B_halt (* of H *)
    then show "{P2} H {Q3}"
      unfolding P2_def Q3_def using H_unhalt_inv[OF assms]
      by(simp add: tape_of_prod_def tape_of_list_def)
  qed (simp)

(* {P3} dither loops *)
  have second: "{Q3} dither \<up>" unfolding Q3_def 
    by (rule dither_loops)

(* {P1} tcontra loops *)
  have "{P1} tcontra \<up>" 
    unfolding tcontra_def
    by (rule Hoare_plus_unhalt[OF first second H_wf])

  with assms show "False"
    unfolding P1_def
    unfolding halts_def
    unfolding Hoare_halt_def Hoare_unhalt_def
    by (auto simp add: tape_of_list_def)
qed


text \<open>
  \<open>False\<close> can finally derived.
\<close>

lemma false: "False"
  using tcontra_halt tcontra_unhalt 
  by auto

end

declare replicate_Suc[simp del]

end

