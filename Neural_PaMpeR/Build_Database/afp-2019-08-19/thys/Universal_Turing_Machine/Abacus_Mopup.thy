(* Title: thys/Abacus_Mopup.thy
   Author: Jian Xu, Xingyuan Zhang, and Christian Urban
   Modifications: Sebastiaan Joosten
*)

chapter \<open>Mopup Turing Machine that deletes all "registers", except one\<close>

theory Abacus_Mopup
  imports Uncomputable
begin

fun mopup_a :: "nat \<Rightarrow> instr list"
  where
    "mopup_a 0 = []" |
    "mopup_a (Suc n) = mopup_a n @ 
       [(R, 2*n + 3), (W0, 2*n + 2), (R, 2*n + 1), (W1, 2*n + 2)]"

definition mopup_b :: "instr list"
  where
    "mopup_b \<equiv> [(R, 2), (R, 1), (L, 5), (W0, 3), (R, 4), (W0, 3),
            (R, 2), (W0, 3), (L, 5), (L, 6), (R, 0), (L, 6)]"

fun mopup :: "nat \<Rightarrow> instr list"
  where 
    "mopup n = mopup_a n @ shift mopup_b (2*n)"

type_synonym mopup_type = "config \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> cell list \<Rightarrow> bool"

fun mopup_stop :: "mopup_type"
  where
    "mopup_stop (s, l, r) lm n ires= 
        (\<exists> ln rn. l = Bk\<up>ln @ Bk # Bk # ires \<and> r = <lm ! n> @ Bk\<up>rn)"

fun mopup_bef_erase_a :: "mopup_type"
  where
    "mopup_bef_erase_a (s, l, r) lm n ires= 
         (\<exists> ln m rn. l = Bk\<up>ln @ Bk # Bk # ires \<and> 
                  r = Oc\<up>m@ Bk # <(drop ((s + 1) div 2) lm)> @ Bk\<up>rn)"

fun mopup_bef_erase_b :: "mopup_type"
  where
    "mopup_bef_erase_b (s, l, r) lm n ires = 
      (\<exists> ln m rn. l = Bk\<up>ln @ Bk # Bk # ires \<and> r = Bk # Oc\<up>m @ Bk # 
                                      <(drop (s div 2) lm)> @ Bk\<up>rn)"

fun mopup_jump_over1 :: "mopup_type"
  where
    "mopup_jump_over1 (s, l, r) lm n ires = 
      (\<exists> ln m1 m2 rn. m1 + m2 = Suc (lm ! n) \<and> 
        l = Oc\<up>m1 @ Bk\<up>ln @ Bk # Bk # ires \<and> 
     (r = Oc\<up>m2 @ Bk # <(drop (Suc n) lm)> @ Bk\<up>rn \<or> 
     (r = Oc\<up>m2 \<and> (drop (Suc n) lm) = [])))"

fun mopup_aft_erase_a :: "mopup_type"
  where
    "mopup_aft_erase_a (s, l, r) lm n ires = 
      (\<exists> lnl lnr rn (ml::nat list) m. 
          m = Suc (lm ! n) \<and> l = Bk\<up>lnr @ Oc\<up>m @ Bk\<up>lnl @ Bk # Bk # ires \<and> 
                                   (r = <ml> @ Bk\<up>rn))"

fun mopup_aft_erase_b :: "mopup_type"
  where
    "mopup_aft_erase_b (s, l, r) lm n ires= 
   (\<exists> lnl lnr rn (ml::nat list) m. 
      m = Suc (lm ! n) \<and> 
      l = Bk\<up>lnr @ Oc\<up>m @ Bk\<up>lnl @ Bk # Bk # ires \<and> 
     (r = Bk # <ml> @ Bk\<up>rn \<or>
      r = Bk # Bk # <ml> @ Bk\<up>rn))"

fun mopup_aft_erase_c :: "mopup_type"
  where
    "mopup_aft_erase_c (s, l, r) lm n ires = 
 (\<exists> lnl lnr rn (ml::nat list) m. 
     m = Suc (lm ! n) \<and> 
     l = Bk\<up>lnr @ Oc\<up>m @ Bk\<up>lnl @ Bk # Bk # ires \<and> 
    (r = <ml> @ Bk\<up>rn \<or> r = Bk # <ml> @ Bk\<up>rn))"

fun mopup_left_moving :: "mopup_type"
  where
    "mopup_left_moving (s, l, r) lm n ires = 
  (\<exists> lnl lnr rn m.
     m = Suc (lm ! n) \<and> 
   ((l = Bk\<up>lnr @ Oc\<up>m @ Bk\<up>lnl @ Bk # Bk # ires \<and> r = Bk\<up>rn) \<or>
    (l = Oc\<up>(m - 1) @ Bk\<up>lnl @ Bk # Bk # ires \<and> r = Oc # Bk\<up>rn)))"

fun mopup_jump_over2 :: "mopup_type"
  where
    "mopup_jump_over2 (s, l, r) lm n ires = 
     (\<exists> ln rn m1 m2.
          m1 + m2 = Suc (lm ! n) 
        \<and> r \<noteq> [] 
        \<and> (hd r = Oc \<longrightarrow> (l = Oc\<up>m1 @ Bk\<up>ln @ Bk # Bk # ires \<and> r = Oc\<up>m2 @ Bk\<up>rn)) 
        \<and> (hd r = Bk \<longrightarrow> (l = Bk\<up>ln @ Bk # ires \<and> r = Bk # Oc\<up>(m1+m2)@ Bk\<up>rn)))"


fun mopup_inv :: "mopup_type"
  where
    "mopup_inv (s, l, r) lm n ires = 
      (if s = 0 then mopup_stop (s, l, r) lm n ires
       else if s \<le> 2*n then
               if s mod 2 = 1 then mopup_bef_erase_a (s, l, r) lm n ires
                   else mopup_bef_erase_b (s, l, r) lm n ires
            else if s = 2*n + 1 then 
                mopup_jump_over1 (s, l, r) lm n ires
            else if s = 2*n + 2 then mopup_aft_erase_a (s, l, r) lm n ires
            else if s = 2*n + 3 then mopup_aft_erase_b (s, l, r) lm n ires
            else if s = 2*n + 4 then mopup_aft_erase_c (s, l, r) lm n ires
            else if s = 2*n + 5 then mopup_left_moving (s, l, r) lm n ires
            else if s = 2*n + 6 then mopup_jump_over2 (s, l, r) lm n ires
            else False)"

lemma mop_bef_length[simp]: "length (mopup_a n) = 4 * n"
  by(induct n, simp_all)

lemma mopup_a_nth: 
  "\<lbrakk>q < n; x < 4\<rbrakk> \<Longrightarrow> mopup_a n ! (4 * q + x) = 
                             mopup_a (Suc q) ! ((4 * q) + x)"
proof(induct n)
  case (Suc n)
  then show ?case 
    by(cases "q < n";cases "q = n", auto simp add: nth_append)
qed auto

lemma fetch_bef_erase_a_o[simp]: 
  "\<lbrakk>0 < s; s \<le> 2 * n; s mod 2 = Suc 0\<rbrakk>
  \<Longrightarrow> (fetch (mopup_a n @ shift mopup_b (2 * n)) s Oc) = (W0, s + 1)"
  apply(subgoal_tac "\<exists> q. s = 2*q + 1", auto)
   apply(subgoal_tac "length (mopup_a n) = 4*n")
    apply(auto simp: nth_append)
   apply(subgoal_tac "mopup_a n ! (4 * q + 1) = 
                      mopup_a (Suc q) ! ((4 * q) + 1)", 
      simp add: nth_append)
   apply(rule mopup_a_nth, auto)
  apply arith
  done

lemma fetch_bef_erase_a_b[simp]:
  "\<lbrakk>0 < s; s \<le> 2 * n; s mod 2 = Suc 0\<rbrakk>
   \<Longrightarrow>  (fetch (mopup_a n @ shift mopup_b (2 * n)) s Bk) = (R, s + 2)"
  apply(subgoal_tac "\<exists> q. s = 2*q + 1", auto)
   apply(subgoal_tac "length (mopup_a n) = 4*n")
    apply(auto simp: nth_append)
   apply(subgoal_tac "mopup_a n ! (4 * q + 0) = 
                       mopup_a (Suc q) ! ((4 * q + 0))", 
      simp add: nth_append)
   apply(rule mopup_a_nth, auto)
  apply arith
  done

lemma fetch_bef_erase_b_b: 
  assumes "n < length lm" "0 < s" "s \<le> 2 * n" "s mod 2 = 0"
  shows "(fetch (mopup_a n @ shift mopup_b (2 * n)) s Bk) = (R, s - 1)"
proof -
  from assms obtain q where q:"s = 2 * q" by auto
  then obtain nat where nat:"q = Suc nat" using assms(2) by (cases q, auto)
  from assms(3) mopup_a_nth[of nat n 2]
  have "mopup_a n ! (4 * nat + 2) = mopup_a (Suc nat) ! ((4 * nat) + 2)"
    unfolding nat q by auto
  thus ?thesis using assms nat q by (auto simp: nth_append)
qed

lemma fetch_jump_over1_o: 
  "fetch (mopup_a n @ shift mopup_b (2 * n)) (Suc (2 * n)) Oc
  = (R, Suc (2 * n))"
  apply(subgoal_tac "length (mopup_a n) = 4 * n")
   apply(auto simp: mopup_b_def nth_append shift.simps)
  done

lemma fetch_jump_over1_b: 
  "fetch (mopup_a n @ shift mopup_b (2 * n)) (Suc (2 * n)) Bk 
 = (R, Suc (Suc (2 * n)))"
  apply(subgoal_tac "length (mopup_a n) = 4 * n")
   apply(auto simp: mopup_b_def nth_append shift.simps)
  done

lemma fetch_aft_erase_a_o: 
  "fetch (mopup_a n @ shift mopup_b (2 * n)) (Suc (Suc (2 * n))) Oc 
 = (W0, Suc (2 * n + 2))"
  apply(subgoal_tac "length (mopup_a n) = 4 * n")
   apply(auto simp: mopup_b_def nth_append shift.simps)
  done

lemma fetch_aft_erase_a_b: 
  "fetch (mopup_a n @ shift mopup_b (2 * n)) (Suc (Suc (2 * n))) Bk
  = (L, Suc (2 * n + 4))"
  apply(subgoal_tac "length (mopup_a n) = 4 * n")
   apply(auto simp: mopup_b_def nth_append shift.simps)
  done

lemma fetch_aft_erase_b_b: 
  "fetch (mopup_a n @ shift mopup_b (2 * n)) (2*n + 3) Bk
  = (R, Suc (2 * n + 3))"
  apply(subgoal_tac "length (mopup_a n) = 4 * n")
   apply(subgoal_tac "2*n + 3 = Suc (2*n + 2)", simp only: fetch.simps)
    apply(auto simp: mopup_b_def nth_append shift.simps)
  done

lemma fetch_aft_erase_c_o: 
  "fetch (mopup_a n @ shift mopup_b (2 * n)) (2 * n + 4) Oc 
 = (W0, Suc (2 * n + 2))"
  apply(subgoal_tac "length (mopup_a n) = 4 * n")
   apply(subgoal_tac "2*n + 4 = Suc (2*n + 3)", simp only: fetch.simps)
    apply(auto simp: mopup_b_def nth_append shift.simps)
  done

lemma fetch_aft_erase_c_b: 
  "fetch (mopup_a n @ shift mopup_b (2 * n)) (2 * n + 4) Bk 
 = (R, Suc (2 * n + 1))"
  apply(subgoal_tac "length (mopup_a n) = 4 * n")
   apply(subgoal_tac "2*n + 4 = Suc (2*n + 3)", simp only: fetch.simps)
    apply(auto simp: mopup_b_def nth_append shift.simps)
  done

lemma fetch_left_moving_o: 
  "(fetch (mopup_a n @ shift mopup_b (2 * n)) (2 * n + 5) Oc) 
 = (L, 2*n + 6)"
  apply(subgoal_tac "length (mopup_a n) = 4 * n")
   apply(subgoal_tac "2*n + 5 = Suc (2*n + 4)", simp only: fetch.simps)
    apply(auto simp: mopup_b_def nth_append shift.simps)
  done

lemma fetch_left_moving_b: 
  "(fetch (mopup_a n @ shift mopup_b (2 * n)) (2 * n + 5) Bk)
  = (L, 2*n + 5)"
  apply(subgoal_tac "length (mopup_a n) = 4 * n")
   apply(subgoal_tac "2*n + 5 = Suc (2*n + 4)", simp only: fetch.simps)
    apply(auto simp: mopup_b_def nth_append shift.simps)
  done

lemma fetch_jump_over2_b:
  "(fetch (mopup_a n @ shift mopup_b (2 * n)) (2 * n + 6) Bk) 
 = (R, 0)"
  apply(subgoal_tac "length (mopup_a n) = 4 * n")
   apply(subgoal_tac "2*n + 6 = Suc (2*n + 5)", simp only: fetch.simps)
    apply(auto simp: mopup_b_def nth_append shift.simps)
  done

lemma fetch_jump_over2_o: 
  "(fetch (mopup_a n @ shift mopup_b (2 * n)) (2 * n + 6) Oc) 
 = (L, 2*n + 6)"
  apply(subgoal_tac "length (mopup_a n) = 4 * n")
   apply(subgoal_tac "2*n + 6 = Suc (2*n + 5)", simp only: fetch.simps)
    apply(auto simp: mopup_b_def nth_append shift.simps)
  done

lemmas mopupfetchs = 
  fetch_bef_erase_a_o fetch_bef_erase_a_b fetch_bef_erase_b_b 
  fetch_jump_over1_o fetch_jump_over1_b fetch_aft_erase_a_o 
  fetch_aft_erase_a_b fetch_aft_erase_b_b fetch_aft_erase_c_o 
  fetch_aft_erase_c_b fetch_left_moving_o fetch_left_moving_b 
  fetch_jump_over2_b fetch_jump_over2_o

declare 
  mopup_jump_over2.simps[simp del] mopup_left_moving.simps[simp del]
  mopup_aft_erase_c.simps[simp del] mopup_aft_erase_b.simps[simp del] 
  mopup_aft_erase_a.simps[simp del] mopup_jump_over1.simps[simp del]
  mopup_bef_erase_a.simps[simp del] mopup_bef_erase_b.simps[simp del]
  mopup_stop.simps[simp del]

lemma mopup_bef_erase_b_Bk_via_a_Oc[simp]: 
  "\<lbrakk>mopup_bef_erase_a (s, l, Oc # xs) lm n ires\<rbrakk> \<Longrightarrow> 
  mopup_bef_erase_b (Suc s, l, Bk # xs) lm n ires"
  apply(auto simp: mopup_bef_erase_a.simps mopup_bef_erase_b.simps)
  by (metis cell.distinct(1) hd_append list.sel(1) list.sel(3) tl_append2 tl_replicate)

lemma mopup_false1:
  "\<lbrakk>0 < s; s \<le> 2 * n; s mod 2 = Suc 0;  \<not> Suc s \<le> 2 * n\<rbrakk> 
  \<Longrightarrow> RR"
  apply(arith)
  done

lemma mopup_bef_erase_a_implies_two[simp]: 
  "\<lbrakk>n < length lm; 0 < s; s \<le> 2 * n; s mod 2 = Suc 0; 
   mopup_bef_erase_a (s, l, Oc # xs) lm n ires; r = Oc # xs\<rbrakk>
 \<Longrightarrow> (Suc s \<le> 2 * n \<longrightarrow> mopup_bef_erase_b (Suc s, l, Bk # xs) lm n ires)  \<and>
     (\<not> Suc s \<le> 2 * n \<longrightarrow> mopup_jump_over1 (Suc s, l, Bk # xs) lm n ires) "
  apply(auto elim!: mopup_false1)
  done

lemma tape_of_nl_cons: "<m # lm> = (if lm = [] then Oc\<up>(Suc m)
                    else Oc\<up>(Suc m) @ Bk # <lm>)"
  by(cases lm, simp_all add: tape_of_list_def  tape_of_nat_def split: if_splits)

lemma drop_tape_of_cons: 
  "\<lbrakk>Suc q < length lm; x = lm ! q\<rbrakk> \<Longrightarrow> <drop q lm> = Oc # Oc \<up> x @ Bk # <drop (Suc q) lm>"
  using Suc_lessD append_Cons list.simps(2) Cons_nth_drop_Suc replicate_Suc tape_of_nl_cons
  by metis

lemma erase2jumpover1:
  "\<lbrakk>q < length list; 
             \<forall>rn. <drop q list> \<noteq> Oc # Oc \<up> (list ! q) @ Bk # <drop (Suc q) list> @ Bk \<up> rn\<rbrakk>
       \<Longrightarrow> <drop q list> = Oc # Oc \<up> (list ! q)"
  apply(erule_tac x = 0 in allE, simp)
  apply(cases "Suc q < length list")
   apply(erule_tac notE)
   apply(rule_tac drop_tape_of_cons, simp_all)
  apply(subgoal_tac "length list = Suc q", auto)
  apply(subgoal_tac "drop q list = [list ! q]")
   apply(simp add: tape_of_nat_def tape_of_list_def replicate_Suc)
  by (metis append_Nil2 append_eq_conv_conj Cons_nth_drop_Suc lessI)

lemma erase2jumpover2:
  "\<lbrakk>q < length list; \<forall>rn. <drop q list> @ Bk # Bk \<up> n \<noteq>
  Oc # Oc \<up> (list ! q) @ Bk # <drop (Suc q) list> @ Bk \<up> rn\<rbrakk>
  \<Longrightarrow> RR"
  apply(cases "Suc q < length list")
   apply(erule_tac x = "Suc n" in allE, simp)
   apply(erule_tac notE, simp add: replicate_Suc)
   apply(rule_tac drop_tape_of_cons, simp_all)
  apply(subgoal_tac "length list = Suc q", auto)
  apply(erule_tac x = "n" in allE, simp add: tape_of_list_def)
  by (metis append_Nil2 append_eq_conv_conj Cons_nth_drop_Suc lessI replicate_Suc tape_of_list_def tape_of_nl_cons)

lemma mod_ex1: "(a mod 2 = Suc 0) = (\<exists> q. a = Suc (2 * q))"
  by arith

declare replicate_Suc[simp]

lemma mopup_bef_erase_a_2_jump_over[simp]:
  "\<lbrakk>n < length lm; 0 < s; s mod 2 = Suc 0;  s \<le> 2 * n;
   mopup_bef_erase_a (s, l, Bk # xs) lm n ires; \<not> (Suc (Suc s) \<le> 2 * n)\<rbrakk> 
\<Longrightarrow> mopup_jump_over1 (s', Bk # l, xs) lm n ires"
proof(cases n)
  case (Suc nat)
  assume assms: "n < length lm" "0 < s" "s mod 2 = Suc 0" "s \<le> 2 * n"
    "mopup_bef_erase_a (s, l, Bk # xs) lm n ires" "\<not> (Suc (Suc s) \<le> 2 * n)"
  from assms obtain a lm' where Cons:"lm = Cons a lm'" by (cases lm,auto)
  from assms have n:"Suc s div 2 = n" by auto
  have [simp]:"s = Suc (2 * q) \<longleftrightarrow> q = nat" for q using assms Suc by presburger
  from assms obtain ln m rn where ln:"l = Bk \<up> ln @ Bk # Bk # ires"
    and "Bk # xs = Oc \<up> m @ Bk # <drop (Suc s div 2) lm> @ Bk \<up> rn"
    by (auto simp: mopup_bef_erase_a.simps mopup_jump_over1.simps)
  hence xs:"xs = <drop n lm> @ Bk \<up> rn" by(cases m;auto simp: n mod_ex1)
  have [intro]:"nat < length lm' \<Longrightarrow>
    \<forall>rna. xs \<noteq> Oc # Oc \<up> (lm' ! nat) @ Bk # <drop (Suc nat) lm'> @ Bk \<up> rna \<Longrightarrow>
    <drop nat lm'> @ Bk \<up> rn = Oc # Oc \<up> (lm' ! nat)"
    by(cases rn, auto elim: erase2jumpover1 erase2jumpover2 simp:xs Suc Cons)
  have [intro]:"<drop nat lm'> \<noteq> Oc # Oc \<up> (lm' ! nat) @ Bk # <drop (Suc nat) lm'> @ Bk \<up> 0 \<Longrightarrow> length lm' \<le> Suc nat"
    using drop_tape_of_cons[of nat lm'] by fastforce
  from assms(1,3) have [intro!]:"
            0 + Suc (lm' ! nat) = Suc (lm' ! nat) \<and>
            Bk # Bk \<up> ln = Oc \<up> 0 @ Bk \<up> Suc ln \<and>
            ((\<exists>rna. xs = Oc \<up> Suc (lm' ! nat) @ Bk # <drop (Suc nat) lm'> @ Bk \<up> rna) \<or>
             xs = Oc \<up> Suc (lm' ! nat) \<and> length lm' \<le> Suc nat)"
    by (auto simp:Cons ln xs Suc)
  from assms(1,3) show ?thesis unfolding Cons ln Suc
    by(auto simp: mopup_bef_erase_a.simps mopup_jump_over1.simps simp del:split_head_repeat)
qed auto


lemma Suc_Suc_div:  "\<lbrakk>0 < s; s mod 2 = Suc 0; Suc (Suc s) \<le> 2 * n\<rbrakk>
           \<Longrightarrow> (Suc (Suc (s div 2))) \<le> n" by(arith)

lemma mopup_bef_erase_a_2_a[simp]: 
  assumes "n < length lm" "0 < s" "s mod 2 = Suc 0" 
    "mopup_bef_erase_a (s, l, Bk # xs) lm n ires"
    "Suc (Suc s) \<le> 2 * n"
  shows "mopup_bef_erase_a (Suc (Suc s), Bk # l, xs) lm n ires"
proof-
  from assms obtain rn m ln where
    rn:"l = Bk \<up> ln @ Bk # Bk # ires" "Bk # xs = Oc \<up> m @ Bk # <drop (Suc s div 2) lm> @ Bk \<up> rn"
    by (auto simp: mopup_bef_erase_a.simps)
  hence m:"m = 0" using assms by (cases m,auto)
  hence d:"drop (Suc (Suc (s div 2))) lm \<noteq> []"
    using assms(1,3,5) by auto arith
  hence "Bk # l = Bk \<up> Suc ln @ Bk # Bk # ires \<and>
    xs = Oc \<up> Suc (lm ! (Suc s div 2)) @ Bk # <drop ((Suc (Suc s) + 1) div 2) lm> @ Bk \<up> rn"
    using rn by(auto intro:drop_tape_of_cons simp:m) 
  thus ?thesis unfolding mopup_bef_erase_a.simps by blast
qed

lemma mopup_false2: 
  "\<lbrakk>0 < s; s \<le> 2 * n; 
   s mod 2 = Suc 0; Suc s \<noteq> 2 * n;
   \<not> Suc (Suc s) \<le> 2 * n\<rbrakk> \<Longrightarrow> RR"
  by(arith)

lemma ariths[simp]: "\<lbrakk>0 < s; s \<le> 2 *n; s mod 2 \<noteq> Suc 0\<rbrakk> \<Longrightarrow> 
                                      (s - Suc 0) mod 2 = Suc 0"
  "\<lbrakk>0 < s; s \<le> 2 *n; s mod 2 \<noteq> Suc 0\<rbrakk> \<Longrightarrow>
                                       s - Suc 0 \<le> 2 * n"
  "\<lbrakk>0 < s; s \<le> 2 *n; s mod 2 \<noteq> Suc 0\<rbrakk> \<Longrightarrow> \<not> s \<le> Suc 0"
  by(arith)+

lemma take_suc[intro]:
  "\<exists>lna. Bk # Bk \<up> ln = Bk \<up> lna"
  by(rule_tac x = "Suc ln" in exI, simp)


lemma mopup_bef_erase[simp]: "mopup_bef_erase_a (s, l, []) lm n ires \<Longrightarrow> 
                        mopup_bef_erase_a (s, l, [Bk]) lm n ires"
  "\<lbrakk>n < length lm; 0 < s; s \<le> 2 * n; s mod 2 = Suc 0; \<not> Suc (Suc s) \<le> 2 *n;
     mopup_bef_erase_a (s, l, []) lm n ires\<rbrakk>
    \<Longrightarrow>  mopup_jump_over1 (s', Bk # l, []) lm n ires"
  "mopup_bef_erase_b (s, l, Oc # xs) lm n ires \<Longrightarrow> l \<noteq> []"
  "\<lbrakk>n < length lm; 0 < s; s \<le> 2 * n; 
               s mod 2 \<noteq> Suc 0; 
               mopup_bef_erase_b (s, l, Bk # xs) lm n ires; r = Bk # xs\<rbrakk> 
           \<Longrightarrow> mopup_bef_erase_a (s - Suc 0, Bk # l, xs) lm n ires"
  "\<lbrakk>mopup_bef_erase_b (s, l, []) lm n ires\<rbrakk> \<Longrightarrow> 
                   mopup_bef_erase_a (s - Suc 0, Bk # l, []) lm n ires"
  by(auto simp: mopup_bef_erase_b.simps mopup_bef_erase_a.simps)


lemma mopup_jump_over1_in_ctx[simp]:
  assumes "mopup_jump_over1 (Suc (2 * n), l, Oc # xs) lm n ires"
  shows "mopup_jump_over1 (Suc (2 * n), Oc # l, xs) lm n ires"
proof -
  from assms obtain ln m1 m2 rn where
    "m1 + m2 = Suc (lm ! n)"
    "l = Oc \<up> m1 @ Bk \<up> ln @ Bk # Bk # ires"
    "(Oc # xs = Oc \<up> m2 @ Bk # <drop (Suc n) lm> @ Bk \<up> rn \<or>
         Oc # xs = Oc \<up> m2 \<and> drop (Suc n) lm = [])" unfolding mopup_jump_over1.simps by blast
  thus ?thesis unfolding mopup_jump_over1.simps
    apply(rule_tac x = ln in exI, rule_tac x = "Suc m1" in exI
        ,rule_tac x = "m2 - 1" in exI)
    by(cases "m2", auto)
qed

lemma mopup_jump_over1_2_aft_erase_a[simp]:  
  assumes "mopup_jump_over1 (Suc (2 * n), l, Bk # xs) lm n ires"
  shows "mopup_aft_erase_a (Suc (Suc (2 * n)), Bk # l, xs) lm n ires"
proof -
  from assms obtain ln m1 m2 rn where
    "m1 + m2 = Suc (lm ! n)"
    "l = Oc \<up> m1 @ Bk \<up> ln @ Bk # Bk # ires"
    "(Bk # xs = Oc \<up> m2 @ Bk # <drop (Suc n) lm> @ Bk \<up> rn \<or>
        Bk # xs = Oc \<up> m2 \<and> drop (Suc n) lm = [])" unfolding mopup_jump_over1.simps by blast
  thus ?thesis unfolding mopup_aft_erase_a.simps
    apply( rule_tac x = ln in exI, rule_tac x = "Suc 0" in exI,rule_tac x = rn in exI
        , rule_tac x = "drop (Suc n) lm" in exI)
    by(cases m2, auto)
qed

lemma mopup_aft_erase_a_via_jump_over1[simp]: 
  "\<lbrakk>mopup_jump_over1 (Suc (2 * n), l, []) lm n ires\<rbrakk> \<Longrightarrow> 
    mopup_aft_erase_a (Suc (Suc (2 * n)), Bk # l, []) lm n ires"
proof(rule mopup_jump_over1_2_aft_erase_a)
  assume a:"mopup_jump_over1 (Suc (2 * n), l, []) lm n ires"
  then obtain ln where ln:"length lm \<le> Suc n \<Longrightarrow> l = Oc # Oc \<up> (lm ! n) @ Bk \<up> ln @ Bk # Bk # ires"
    unfolding mopup_jump_over1.simps by auto
  show "mopup_jump_over1 (Suc (2 * n), l, [Bk]) lm n ires"
    unfolding mopup_jump_over1.simps
    apply(rule_tac x = ln in exI, rule_tac x = "Suc (lm ! n)" in exI, 
        rule_tac x = 0 in exI)
    using a ln by(auto simp: mopup_jump_over1.simps tape_of_list_def )
qed

lemma tape_of_list_empty[simp]: "<[]> = []" by(simp add: tape_of_list_def)

lemma mopup_aft_erase_b_via_a[simp]: 
  assumes "mopup_aft_erase_a (Suc (Suc (2 * n)), l, Oc # xs) lm n ires"
  shows "mopup_aft_erase_b (Suc (Suc (Suc (2 * n))), l, Bk # xs) lm n ires"
proof -
  from assms obtain lnl lnr rn ml where
    assms:
    "l = Bk \<up> lnr @ Oc \<up> Suc (lm ! n) @ Bk \<up> lnl @ Bk # Bk # ires"
    "Oc # xs = <ml::nat list> @ Bk \<up> rn"
    unfolding mopup_aft_erase_a.simps by auto
  then obtain a list where ml:"ml = a # list" by (cases ml,cases rn,auto)
  with assms show ?thesis unfolding mopup_aft_erase_b.simps
    apply(auto simp add: tape_of_nl_cons split: if_splits)
     apply(cases a, simp_all)
      apply(rule_tac x = rn in exI, rule_tac x = "[]" in exI, force)
     apply(rule_tac x = rn in exI, rule_tac x = "[a-1]" in exI)
     apply(cases "a"; force simp add: tape_of_list_def tape_of_nat_def) 
    apply(cases "a")
     apply(rule_tac x = rn in exI, rule_tac x = list in exI, force)
    apply(rule_tac x = rn in exI,rule_tac x = "(a-1) # list" in exI, simp add: tape_of_nl_cons)
    done
qed

lemma mopup_left_moving_via_aft_erase_a[simp]:
  assumes "mopup_aft_erase_a (Suc (Suc (2 * n)), l, Bk # xs) lm n ires"
  shows "mopup_left_moving (5 + 2 * n, tl l, hd l # Bk # xs) lm n ires"
proof-
  from assms[unfolded mopup_aft_erase_a.simps] obtain lnl lnr rn ml where
    "l = Bk \<up> lnr @ Oc \<up> Suc (lm ! n) @ Bk \<up> lnl @ Bk # Bk # ires"
    "Bk # xs = <ml::nat list> @ Bk \<up> rn"
    by auto
  thus ?thesis unfolding mopup_left_moving.simps
    by(cases lnr;cases ml,auto simp: tape_of_nl_cons)
qed

lemma mopup_aft_erase_a_nonempty[simp]:
  "mopup_aft_erase_a (Suc (Suc (2 * n)), l, xs) lm n ires \<Longrightarrow> l \<noteq> []"
  by(auto simp only: mopup_aft_erase_a.simps)

lemma mopup_left_moving_via_aft_erase_a_emptylst[simp]:
  assumes "mopup_aft_erase_a (Suc (Suc (2 * n)), l, []) lm n ires"
  shows "mopup_left_moving (5 + 2 * n, tl l, [hd l]) lm n ires"
proof -
  have [intro!]:"[Bk] = Bk \<up> 1" by auto
  from assms obtain lnl lnr where "l = Bk \<up> lnr @ Oc # Oc \<up> (lm ! n) @ Bk \<up> lnl @ Bk # Bk # ires"
    unfolding mopup_aft_erase_a.simps by auto
  thus ?thesis by(case_tac lnr, auto simp add:mopup_left_moving.simps)
qed

lemma mopup_aft_erase_b_no_Oc[simp]: "mopup_aft_erase_b (2 * n + 3, l, Oc # xs) lm n ires = False"
  by(auto simp: mopup_aft_erase_b.simps)

lemma tape_of_ex1[intro]: 
  "\<exists>rna ml. Oc \<up> a @ Bk \<up> rn = <ml::nat list> @ Bk \<up> rna \<or> Oc \<up> a @ Bk \<up> rn = Bk # <ml> @ Bk \<up> rna"
  by(rule_tac x = rn in exI, rule_tac x = "if a = 0 then [] else [a-1]" in exI,
      simp add: tape_of_list_def tape_of_nat_def)

lemma mopup_aft_erase_b_via_c_helper: "\<exists>rna ml. Oc \<up> a @ Bk # <list::nat list> @ Bk \<up> rn = 
  <ml> @ Bk \<up> rna \<or> Oc \<up> a @ Bk # <list> @ Bk \<up> rn = Bk # <ml::nat list> @ Bk \<up> rna"
  apply(cases "list = []", simp add: replicate_Suc[THEN sym] del: replicate_Suc split_head_repeat)
   apply(rule_tac rn = "Suc rn" in tape_of_ex1)
  apply(cases a, simp)
   apply(rule_tac x = rn in exI, rule_tac x = list in exI, simp)
  apply(rule_tac x = rn in exI, rule_tac x = "(a-1) # list" in exI)
  apply(simp add: tape_of_nl_cons)
  done

lemma mopup_aft_erase_b_via_c[simp]: 
  assumes "mopup_aft_erase_c (2 * n + 4, l, Oc # xs) lm n ires"
  shows "mopup_aft_erase_b (Suc (Suc (Suc (2 * n))), l, Bk # xs) lm n ires"
proof-
  from assms obtain lnl rn lnr ml where assms:
    "l = Bk \<up> lnr @ Oc # Oc \<up> (lm ! n) @ Bk \<up> lnl @ Bk # Bk # ires"
    "Oc # xs = <ml::nat list> @ Bk \<up> rn" unfolding mopup_aft_erase_c.simps by auto
  hence "Oc # xs = Bk \<up> rn \<Longrightarrow> False" by(cases rn,auto)
  thus ?thesis using assms unfolding mopup_aft_erase_b.simps
    by(cases ml)
      (auto simp add: tape_of_nl_cons split: if_splits intro:mopup_aft_erase_b_via_c_helper
        simp del:split_head_repeat)
qed

lemma mopup_aft_erase_c_aft_erase_a[simp]: 
  assumes "mopup_aft_erase_c (2 * n + 4, l, Bk # xs) lm n ires"
  shows "mopup_aft_erase_a (Suc (Suc (2 * n)), Bk # l, xs) lm n ires"
proof -
  from assms obtain lnl lnr rn ml where
    "l = Bk \<up> lnr @ Oc \<up> Suc (lm ! n) @ Bk \<up> lnl @ Bk # Bk # ires"
    "(Bk # xs = <ml::nat list> @ Bk \<up> rn \<or> Bk # xs = Bk # <ml> @ Bk \<up> rn)"
    unfolding mopup_aft_erase_c.simps by auto
  thus ?thesis unfolding mopup_aft_erase_a.simps
    apply(clarify)
    apply(erule disjE)
     apply(subgoal_tac "ml = []", simp, case_tac rn, 
        simp, simp, rule conjI)
       apply(rule_tac x = lnl in exI, rule_tac x = "Suc lnr" in exI, simp)
      apply (insert tape_of_list_empty,blast)
     apply(case_tac ml, simp, simp add: tape_of_nl_cons split: if_splits)
    apply(rule_tac x = lnl in exI, rule_tac x = "Suc lnr" in exI)
    apply(rule_tac x = rn in exI, rule_tac x = "ml" in exI, simp)
    done
qed

lemma mopup_aft_erase_a_via_c[simp]: 
  "\<lbrakk>mopup_aft_erase_c (2 * n + 4, l, []) lm n ires\<rbrakk> 
 \<Longrightarrow> mopup_aft_erase_a (Suc (Suc (2 * n)), Bk # l, []) lm n ires"
  by (rule mopup_aft_erase_c_aft_erase_a)
    (auto simp:mopup_aft_erase_c.simps)

lemma mopup_aft_erase_b_2_aft_erase_c[simp]:
  assumes "mopup_aft_erase_b (2 * n + 3, l, Bk # xs) lm n ires"
  shows "mopup_aft_erase_c (4 + 2 * n, Bk # l, xs) lm n ires"
proof -
  from assms obtain lnl lnr ml rn where
    "l = Bk \<up> lnr @ Oc \<up> Suc (lm ! n) @ Bk \<up> lnl @ Bk # Bk # ires"
    "Bk # xs = Bk # <ml::nat list> @ Bk \<up> rn \<or> Bk # xs = Bk # Bk # <ml> @ Bk \<up> rn"
    unfolding  mopup_aft_erase_b.simps by auto
  thus ?thesis unfolding mopup_aft_erase_c.simps
    by (rule_tac x = "lnl" in exI) auto
qed

lemma mopup_aft_erase_c_via_b[simp]: 
  "\<lbrakk>mopup_aft_erase_b (2 * n + 3, l, []) lm n ires\<rbrakk> 
 \<Longrightarrow> mopup_aft_erase_c (4 + 2 * n, Bk # l, []) lm n ires"
  by(auto simp add: mopup_aft_erase_b.simps intro:mopup_aft_erase_b_2_aft_erase_c)

lemma mopup_left_moving_nonempty[simp]: 
  "mopup_left_moving (2 * n + 5, l, Oc # xs) lm n ires \<Longrightarrow> l \<noteq> []"
  by(auto simp: mopup_left_moving.simps)

lemma exp_ind: "a\<up>(Suc x) = a\<up>x @ [a]"
  by(induct x, auto)

lemma mopup_jump_over2_via_left_moving[simp]:  
  "\<lbrakk>mopup_left_moving (2 * n + 5, l, Oc # xs) lm n ires\<rbrakk>
  \<Longrightarrow> mopup_jump_over2 (2 * n + 6, tl l, hd l # Oc # xs) lm n ires"
  apply(simp only: mopup_left_moving.simps mopup_jump_over2.simps)
  apply(erule_tac exE)+
  apply(erule conjE, erule disjE, erule conjE)
   apply (simp add: Cons_replicate_eq)
  apply(rename_tac Lnl lnr rn m)
  apply(cases "hd l", simp add:  )
   apply(cases "lm ! n", simp)
    apply(rule exI, rule_tac x = "length xs" in exI, 
      rule_tac x = "Suc 0" in exI, rule_tac x = 0 in exI)
    apply(case_tac Lnl, simp,simp,  simp add: exp_ind[THEN sym])
   apply(cases "lm ! n", simp)
   apply(case_tac Lnl, simp, simp)
  apply(rule_tac x = Lnl in exI, rule_tac x = "length xs" in exI, auto)
  apply(cases "lm ! n", simp)
   apply(case_tac Lnl, simp_all add: numeral_2_eq_2)
  done

lemma mopup_left_moving_nonempty_snd[simp]: "mopup_left_moving (2 * n + 5, l, xs) lm n ires \<Longrightarrow> l \<noteq> []"
  apply(auto simp: mopup_left_moving.simps)
  done

lemma mopup_left_moving_hd_Bk[simp]:
  "\<lbrakk>mopup_left_moving (2 * n + 5, l, Bk # xs) lm n ires\<rbrakk> 
 \<Longrightarrow> mopup_left_moving (2 * n + 5, tl l, hd l # Bk # xs) lm n ires"
  apply(simp only: mopup_left_moving.simps)
  apply(erule exE)+ apply(rename_tac lnl Lnr rn m)
  apply(case_tac Lnr, auto)
  done

lemma mopup_left_moving_emptylist[simp]: 
  "\<lbrakk>mopup_left_moving (2 * n + 5, l, []) lm n ires\<rbrakk>
    \<Longrightarrow> mopup_left_moving (2 * n + 5, tl l, [hd l]) lm n ires"
  apply(simp only: mopup_left_moving.simps)
  apply(erule exE)+ apply(rename_tac lnl Lnr rn m)
  apply(case_tac Lnr, auto)
  apply(rule_tac x = 1 in exI, simp)
  done


lemma mopup_jump_over2_Oc_nonempty[simp]: 
  "mopup_jump_over2 (2 * n + 6, l, Oc # xs) lm n ires \<Longrightarrow> l \<noteq> []"
  apply(auto simp: mopup_jump_over2.simps )
  done

lemma mopup_jump_over2_context[simp]: 
  "\<lbrakk>mopup_jump_over2 (2 * n + 6, l, Oc # xs) lm n ires\<rbrakk>
 \<Longrightarrow>  mopup_jump_over2 (2 * n + 6, tl l, hd l # Oc # xs) lm n ires"
  apply(simp only: mopup_jump_over2.simps)
  apply(erule_tac exE)+
  apply(simp, erule conjE, erule_tac conjE)
  apply(rename_tac Ln Rn M1 M2)
  apply(case_tac M1, simp)
   apply(rule_tac x = Ln in exI, rule_tac x = Rn in exI, 
      rule_tac x = 0 in exI)
   apply(case_tac Ln, simp, simp, simp only: exp_ind[THEN sym], simp)
  apply(rule_tac x = Ln in exI, rule_tac x = Rn in exI, 
      rule_tac x = "M1-1" in exI, rule_tac x = "Suc M2" in exI, simp)
  done

lemma mopup_stop_via_jump_over2[simp]: 
  "\<lbrakk>mopup_jump_over2 (2 * n + 6, l, Bk # xs) lm n ires\<rbrakk> 
  \<Longrightarrow> mopup_stop (0, Bk # l, xs) lm n ires"
  apply(auto simp: mopup_jump_over2.simps mopup_stop.simps tape_of_nat_def)
  apply(simp add: exp_ind[THEN sym])
  done

lemma mopup_jump_over2_nonempty[simp]: "mopup_jump_over2 (2 * n + 6, l, []) lm n ires = False"
  by(auto simp: mopup_jump_over2.simps)

declare fetch.simps[simp del]
lemma mod_ex2: "(a mod (2::nat) = 0) = (\<exists> q. a = 2 * q)"
  by arith

lemma mod_2: "x mod 2  = 0 \<or>  x mod 2 = Suc 0"
  by arith


lemma mopup_inv_step:
  "\<lbrakk>n < length lm; mopup_inv (s, l, r) lm n ires\<rbrakk>
  \<Longrightarrow> mopup_inv (step (s, l, r) (mopup_a n @ shift mopup_b (2 * n), 0)) lm n ires"
  apply(cases r;cases "hd r")
     apply(auto split:if_splits simp add:step.simps mopupfetchs fetch.simps(1))
      apply(drule_tac mopup_false2, simp_all add: mopup_bef_erase_b.simps)
    apply(drule_tac mopup_false2, simp_all)
   apply(drule_tac mopup_false2, simp_all)
  by presburger

declare mopup_inv.simps[simp del]
lemma mopup_inv_steps: 
  "\<lbrakk>n < length lm; mopup_inv (s, l, r) lm n ires\<rbrakk> \<Longrightarrow> 
     mopup_inv (steps (s, l, r) (mopup_a n @ shift mopup_b (2 * n), 0)  stp) lm n ires"
proof(induct stp)
  case (Suc stp)
  then show ?case 
    by ( cases "steps (s, l, r) 
                (mopup_a n @ shift mopup_b (2 * n), 0) stp"
        , auto simp add: steps.simps intro:mopup_inv_step)
qed (auto simp add: steps.simps)

fun abc_mopup_stage1 :: "config \<Rightarrow> nat \<Rightarrow> nat"
  where
    "abc_mopup_stage1 (s, l, r) n = 
           (if s > 0 \<and> s \<le> 2*n then 6
            else if s = 2*n + 1 then 4
            else if s \<ge> 2*n + 2 \<and> s \<le> 2*n + 4 then 3
            else if s = 2*n + 5 then 2
            else if s = 2*n + 6 then 1
            else 0)"

fun abc_mopup_stage2 :: "config \<Rightarrow> nat \<Rightarrow> nat"
  where
    "abc_mopup_stage2 (s, l, r) n = 
           (if s > 0 \<and> s \<le> 2*n then length r
            else if s = 2*n + 1 then length r
            else if s = 2*n + 5 then length l
            else if s = 2*n + 6 then length l
            else if s \<ge> 2*n + 2 \<and> s \<le> 2*n + 4 then length r
            else 0)"

fun abc_mopup_stage3 :: "config \<Rightarrow> nat \<Rightarrow> nat"
  where
    "abc_mopup_stage3 (s, l, r) n = 
          (if s > 0 \<and> s \<le> 2*n then 
              if hd r = Bk then 0
              else 1
           else if s = 2*n + 2 then 1 
           else if s = 2*n + 3 then 0
           else if s = 2*n + 4 then 2
           else 0)"

definition
  "abc_mopup_measure = measures [\<lambda>(c, n). abc_mopup_stage1 c n, 
                                 \<lambda>(c, n). abc_mopup_stage2 c n, 
                                 \<lambda>(c, n). abc_mopup_stage3 c n]"

lemma wf_abc_mopup_measure:
  shows "wf abc_mopup_measure" 
  unfolding abc_mopup_measure_def 
  by auto

lemma abc_mopup_measure_induct [case_names Step]: 
  "\<lbrakk>\<And>n. \<not> P (f n) \<Longrightarrow> (f (Suc n), (f n)) \<in> abc_mopup_measure\<rbrakk> \<Longrightarrow> \<exists>n. P (f n)"
  using wf_abc_mopup_measure
  by (metis wf_iff_no_infinite_down_chain)

lemma mopup_erase_nonempty[simp]:
  "mopup_bef_erase_a (a, aa, []) lm n ires = False"
  "mopup_bef_erase_b (a, aa, []) lm n ires = False"
  "mopup_aft_erase_b (2 * n + 3, aa, []) lm n ires = False"
  by(auto simp: mopup_bef_erase_a.simps mopup_bef_erase_b.simps mopup_aft_erase_b.simps)

declare mopup_inv.simps[simp del]

lemma fetch_mopup_a_shift[simp]: 
  assumes "0 < q" "q \<le> n"
  shows "fetch (mopup_a n @ shift mopup_b (2 * n)) (2*q) Bk = (R, 2*q - 1)"
proof(cases q)
  case (Suc nat) with assms
  have "mopup_a n ! (4 * nat + 2) = mopup_a (Suc nat) ! ((4 * nat) + 2)" using assms
    by (metis Suc_le_lessD add_2_eq_Suc' less_Suc_eq mopup_a_nth numeral_Bit0)
  then show ?thesis using assms Suc
    by(auto simp: fetch.simps nth_of.simps nth_append)
qed (insert assms,auto)

lemma mopup_halt:
  assumes 
    less: "n < length lm"
    and inv: "mopup_inv (Suc 0, l, r) lm n ires"
    and f: "f = (\<lambda> stp. (steps (Suc 0, l, r) (mopup_a n @ shift mopup_b (2 * n), 0) stp, n))"
    and P: "P = (\<lambda> (c, n). is_final c)"
  shows "\<exists> stp. P (f stp)"
proof (induct rule: abc_mopup_measure_induct) 
  case (Step na)
  have h: "\<not> P (f na)" by fact
  show "(f (Suc na), f na) \<in> abc_mopup_measure"
  proof(simp add: f)
    obtain a b c where g:"steps (Suc 0, l, r) (mopup_a n @ shift mopup_b (2 * n), 0) na = (a, b, c)"
      apply(case_tac "steps (Suc 0, l, r) (mopup_a n @ shift mopup_b (2 * n), 0) na", auto)
      done
    then have "mopup_inv (a, b, c) lm n ires"
      using inv less mopup_inv_steps[of n lm "Suc 0" l r ires na]
      apply(simp)
      done
    moreover have "a > 0"
      using h g
      apply(simp add: f P)
      done
    ultimately 
    have "((step (a, b, c) (mopup_a n @ shift mopup_b (2 * n), 0), n), (a, b, c), n) \<in> abc_mopup_measure"
      apply(case_tac c;cases "hd c")
         apply(auto split:if_splits simp add:step.simps mopup_inv.simps mopup_bef_erase_b.simps)
      by (auto split:if_splits simp: mopupfetchs abc_mopup_measure_def )
    thus "((step (steps (Suc 0, l, r) (mopup_a n @ shift mopup_b (2 * n), 0) na) 
      (mopup_a n @ shift mopup_b (2 * n), 0), n),
      steps (Suc 0, l, r) (mopup_a n @ shift mopup_b (2 * n), 0) na, n)
      \<in> abc_mopup_measure"
      using g by simp
  qed
qed

lemma mopup_inv_start: 
  "n < length am \<Longrightarrow> mopup_inv (Suc 0, Bk # Bk # ires, <am> @ Bk \<up> k) am n ires"
  apply(cases am;auto simp: mopup_inv.simps mopup_bef_erase_a.simps mopup_jump_over1.simps)
    apply(auto simp: tape_of_nl_cons)
     apply(rule_tac x = "Suc (hd am)" in exI, rule_tac x = k in exI, simp)
    apply(cases k;cases n;force)
   apply(cases n; force)
  by(cases n; force split:if_splits)

lemma mopup_correct:
  assumes less: "n < length (am::nat list)"
    and rs: "am ! n = rs"
  shows "\<exists> stp i j. (steps (Suc 0, Bk # Bk # ires, <am> @ Bk \<up> k) (mopup_a n @ shift mopup_b (2 * n), 0) stp)
    = (0, Bk\<up>i @ Bk # Bk # ires, Oc # Oc\<up> rs @ Bk\<up>j)"
  using less
proof -
  have a: "mopup_inv (Suc 0, Bk # Bk # ires, <am> @ Bk \<up> k) am n ires"
    using less
    apply(simp add: mopup_inv_start)
    done    
  then have "\<exists> stp. is_final (steps (Suc 0, Bk # Bk # ires, <am> @ Bk \<up> k) (mopup_a n @ shift mopup_b (2 * n), 0) stp)"
    using less mopup_halt[of n am  "Bk # Bk # ires" "<am> @ Bk \<up> k" ires
        "(\<lambda>stp. (steps (Suc 0, Bk # Bk # ires, <am> @ Bk \<up> k) (mopup_a n @ shift mopup_b (2 * n), 0) stp, n))"
        "(\<lambda>(c, n). is_final c)"]
    apply(simp)
    done
  from this obtain stp where b:
    "is_final (steps (Suc 0, Bk # Bk # ires, <am> @ Bk \<up> k) (mopup_a n @ shift mopup_b (2 * n), 0) stp)" ..
  from a b have
    "mopup_inv (steps (Suc 0, Bk # Bk # ires, <am> @ Bk \<up> k) (mopup_a n @ shift mopup_b (2 * n), 0) stp)
    am n ires"
    apply(rule_tac mopup_inv_steps, simp_all add: less)
    done    
  from b and this show "?thesis"
    apply(rule_tac x = stp in exI, simp)
    apply(case_tac "steps (Suc 0, Bk # Bk # ires, <am> @ Bk \<up> k) 
      (mopup_a n @ shift mopup_b (2 * n), 0) stp")
    apply(simp add: mopup_inv.simps mopup_stop.simps rs)
    using rs
    apply(simp add: tape_of_nat_def)
    done
qed

lemma wf_mopup[intro]: "tm_wf (mopup n, 0)"
  by(induct n, auto simp add: shift.simps mopup_b_def tm_wf.simps)

end