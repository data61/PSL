(* Title: thys/Recursive.thy
   Author: Jian Xu, Xingyuan Zhang, and Christian Urban
   Modifications: Sebastiaan Joosten
*)

theory Recursive
  imports Abacus Rec_Def Abacus_Hoare
begin

fun addition :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> abc_prog"
  where
    "addition m n p = [Dec m 4, Inc n, Inc p, Goto 0, Dec p 7, Inc m, Goto 4]"

fun mv_box :: "nat \<Rightarrow> nat \<Rightarrow> abc_prog"
  where
    "mv_box m n = [Dec m 3, Inc n, Goto 0]"

text \<open>The compilation of \<open>z\<close>-operator.\<close>
definition rec_ci_z :: "abc_inst list"
  where
    "rec_ci_z \<equiv> [Goto 1]"

text \<open>The compilation of \<open>s\<close>-operator.\<close>
definition rec_ci_s :: "abc_inst list"
  where
    "rec_ci_s \<equiv> (addition 0 1 2 [+] [Inc 1])"


text \<open>The compilation of \<open>id i j\<close>-operator\<close>
fun rec_ci_id :: "nat \<Rightarrow> nat \<Rightarrow> abc_inst list"
  where
    "rec_ci_id i j = addition j i (i + 1)"

fun mv_boxes :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> abc_inst list"
  where
    "mv_boxes ab bb 0 = []" |
    "mv_boxes ab bb (Suc n) = mv_boxes ab bb n [+] mv_box (ab + n) (bb + n)"

fun empty_boxes :: "nat \<Rightarrow> abc_inst list"
  where
    "empty_boxes 0 = []" |
    "empty_boxes (Suc n) = empty_boxes n [+] [Dec n 2, Goto 0]"

fun cn_merge_gs ::
  "(abc_inst list \<times> nat \<times> nat) list \<Rightarrow> nat \<Rightarrow> abc_inst list"
  where
    "cn_merge_gs [] p = []" |
    "cn_merge_gs (g # gs) p = 
      (let (gprog, gpara, gn) = g in 
         gprog [+] mv_box gpara p [+] cn_merge_gs gs (Suc p))"


text \<open>
  The compiler of recursive functions, where \<open>rec_ci recf\<close> return 
  \<open>(ap, arity, fp)\<close>, where \<open>ap\<close> is the Abacus program, \<open>arity\<close> is the 
  arity of the recursive function \<open>recf\<close>, 
  \<open>fp\<close> is the amount of memory which is going to be
  used by \<open>ap\<close> for its execution. 
\<close>

fun rec_ci :: "recf \<Rightarrow> abc_inst list \<times> nat \<times> nat"
  where
    "rec_ci z = (rec_ci_z, 1, 2)" |
    "rec_ci s = (rec_ci_s, 1, 3)" |
    "rec_ci (id m n) = (rec_ci_id m n, m, m + 2)" |
    "rec_ci (Cn n f gs) = 
      (let cied_gs = map (\<lambda> g. rec_ci g) gs in
       let (fprog, fpara, fn) = rec_ci f in 
       let pstr = Max (set (Suc n # fn # (map (\<lambda> (aprog, p, n). n) cied_gs))) in
       let qstr = pstr + Suc (length gs) in 
       (cn_merge_gs cied_gs pstr [+] mv_boxes 0 qstr n [+] 
          mv_boxes pstr 0 (length gs) [+] fprog [+] 
            mv_box fpara pstr [+] empty_boxes (length gs) [+] 
             mv_box pstr n [+] mv_boxes qstr 0 n, n,  qstr + n))" |
    "rec_ci (Pr n f g) = 
         (let (fprog, fpara, fn) = rec_ci f in 
          let (gprog, gpara, gn) = rec_ci g in 
          let p = Max (set ([n + 3, fn, gn])) in 
          let e = length gprog + 7 in 
           (mv_box n p [+] fprog [+] mv_box n (Suc n) [+] 
               (([Dec p e] [+] gprog [+] 
                 [Inc n, Dec (Suc n) 3, Goto 1]) @
                     [Dec (Suc (Suc n)) 0, Inc (Suc n), Goto (length gprog + 4)]),
             Suc n, p + 1))" |
    "rec_ci (Mn n f) =
         (let (fprog, fpara, fn) = rec_ci f in 
          let len = length (fprog) in 
            (fprog @ [Dec (Suc n) (len + 5), Dec (Suc n) (len + 3),
             Goto (len + 1), Inc n, Goto 0], n, max (Suc n) fn))"

declare rec_ci.simps [simp del] rec_ci_s_def[simp del] 
  rec_ci_z_def[simp del] rec_ci_id.simps[simp del]
  mv_boxes.simps[simp del] 
  mv_box.simps[simp del] addition.simps[simp del]

declare abc_steps_l.simps[simp del] abc_fetch.simps[simp del] 
  abc_step_l.simps[simp del] 

inductive_cases terminate_pr_reverse: "terminate (Pr n f g) xs"

inductive_cases terminate_z_reverse[elim!]: "terminate z xs"

inductive_cases terminate_s_reverse[elim!]: "terminate s xs"

inductive_cases terminate_id_reverse[elim!]: "terminate (id m n) xs"

inductive_cases terminate_cn_reverse[elim!]: "terminate (Cn n f gs) xs"

inductive_cases terminate_mn_reverse[elim!]:"terminate (Mn n f) xs"

fun addition_inv :: "nat \<times> nat list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>     
                     nat list \<Rightarrow> bool"
  where
    "addition_inv (as, lm') m n p lm = 
        (let sn = lm ! n in
         let sm = lm ! m in
         lm ! p = 0 \<and>
             (if as = 0 then \<exists> x. x \<le> lm ! m \<and> lm' = lm[m := x,
                                    n := (sn + sm - x), p := (sm - x)]
             else if as = 1 then \<exists> x. x < lm ! m \<and> lm' = lm[m := x,
                            n := (sn + sm - x - 1), p := (sm - x - 1)]
             else if as = 2 then \<exists> x. x < lm ! m \<and> lm' = lm[m := x, 
                               n := (sn + sm - x), p := (sm - x - 1)]
             else if as = 3 then \<exists> x. x < lm ! m \<and> lm' = lm[m := x,
                                   n := (sn + sm - x), p := (sm - x)]
             else if as = 4 then \<exists> x. x \<le> lm ! m \<and> lm' = lm[m := x,
                                       n := (sn + sm), p := (sm - x)] 
             else if as = 5 then \<exists> x. x < lm ! m \<and> lm' = lm[m := x, 
                                  n := (sn + sm), p := (sm - x - 1)] 
             else if as = 6 then \<exists> x. x < lm ! m \<and> lm' =
                     lm[m := Suc x, n := (sn + sm), p := (sm - x - 1)]
             else if as = 7 then lm' = lm[m := sm, n := (sn + sm)]
             else False))"

fun addition_stage1 :: "nat \<times> nat list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat"
  where
    "addition_stage1 (as, lm) m p = 
          (if as = 0 \<or> as = 1 \<or> as = 2 \<or> as = 3 then 2 
           else if as = 4 \<or> as = 5 \<or> as = 6 then 1
           else 0)"

fun addition_stage2 :: "nat \<times> nat list \<Rightarrow> nat \<Rightarrow>  nat \<Rightarrow> nat"
  where
    "addition_stage2 (as, lm) m p = 
              (if 0 \<le> as \<and> as \<le> 3 then lm ! m
               else if 4 \<le> as \<and> as \<le> 6 then lm ! p
               else 0)"

fun addition_stage3 :: "nat \<times> nat list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat"
  where
    "addition_stage3 (as, lm) m p = 
             (if as = 1 then 4  
              else if as = 2 then 3 
              else if as = 3 then 2
              else if as = 0 then 1 
              else if as = 5 then 2
              else if as = 6 then 1 
              else if as = 4 then 0 
              else 0)"

fun addition_measure :: "((nat \<times> nat list) \<times> nat \<times> nat) \<Rightarrow> 
                                                 (nat \<times> nat \<times> nat)"
  where
    "addition_measure ((as, lm), m, p) =
     (addition_stage1 (as, lm) m p, 
      addition_stage2 (as, lm) m p,
      addition_stage3 (as, lm) m p)"

definition addition_LE :: "(((nat \<times> nat list) \<times> nat \<times> nat) \<times> 
                          ((nat \<times> nat list) \<times> nat \<times> nat)) set"
  where "addition_LE \<equiv> (inv_image lex_triple addition_measure)"

lemma wf_additon_LE[simp]: "wf addition_LE"
  by(auto simp: addition_LE_def lex_triple_def lex_pair_def)

declare addition_inv.simps[simp del]

lemma update_zero_to_zero[simp]: "\<lbrakk>am ! n = (0::nat); n < length am\<rbrakk> \<Longrightarrow> am[n := 0] = am"
  apply(simp add: list_update_same_conv)
  done

lemma addition_inv_init: 
  "\<lbrakk>m \<noteq> n; max m n < p; length lm > p; lm ! p = 0\<rbrakk> \<Longrightarrow>
                                   addition_inv (0, lm) m n p lm"
  apply(simp add: addition_inv.simps Let_def )
  apply(rule_tac x = "lm ! m" in exI, simp)
  done

lemma abs_fetch[simp]:
  "abc_fetch 0 (addition m n p) = Some (Dec m 4)"
  "abc_fetch (Suc 0) (addition m n p) = Some (Inc n)"
  "abc_fetch 2 (addition m n p) = Some (Inc p)"
  "abc_fetch 3 (addition m n p) = Some (Goto 0)"
  "abc_fetch 4 (addition m n p) = Some (Dec p 7)"
  "abc_fetch 5 (addition m n p) = Some (Inc m)"
  "abc_fetch 6 (addition m n p) = Some (Goto 4)"
  by(simp_all add: abc_fetch.simps addition.simps)

lemma exists_small_list_elem1[simp]:
  "\<lbrakk>m \<noteq> n; p < length lm; lm ! p = 0; m < p; n < p; x \<le> lm ! m; 0 < x\<rbrakk>
 \<Longrightarrow> \<exists>xa<lm ! m. lm[m := x, n := lm ! n + lm ! m - x, 
                    p := lm ! m - x, m := x - Suc 0] =
                 lm[m := xa, n := lm ! n + lm ! m - Suc xa,
                    p := lm ! m - Suc xa]"
  apply(cases x, simp, simp)
  apply(rule_tac x = "x - 1" in exI, simp add: list_update_swap 
      list_update_overwrite)
  done

lemma exists_small_list_elem2[simp]:
  "\<lbrakk>m \<noteq> n; p < length lm; lm ! p = 0; m < p; n < p; x < lm ! m\<rbrakk>
   \<Longrightarrow> \<exists>xa<lm ! m. lm[m := x, n := lm ! n + lm ! m - Suc x,
                      p := lm ! m - Suc x, n := lm ! n + lm ! m - x]
                 = lm[m := xa, n := lm ! n + lm ! m - xa, 
                      p := lm ! m - Suc xa]"
  apply(rule_tac x = x in exI, 
      simp add: list_update_swap list_update_overwrite)
  done

lemma exists_small_list_elem3[simp]: 
  "\<lbrakk>m \<noteq> n; p < length lm; lm ! p = 0; m < p; n < p; x < lm ! m\<rbrakk>
   \<Longrightarrow> \<exists>xa<lm ! m. lm[m := x, n := lm ! n + lm ! m - x, 
                          p := lm ! m - Suc x, p := lm ! m - x]
                 = lm[m := xa, n := lm ! n + lm ! m - xa, 
                          p := lm ! m - xa]"
  apply(rule_tac x = x in exI, simp add: list_update_overwrite)
  done

lemma exists_small_list_elem4[simp]: 
  "\<lbrakk>m \<noteq> n; p < length lm; lm ! p = (0::nat); m < p; n < p; x < lm ! m\<rbrakk>
  \<Longrightarrow> \<exists>xa\<le>lm ! m. lm[m := x, n := lm ! n + lm ! m - x,
                                   p := lm ! m - x] = 
                  lm[m := xa, n := lm ! n + lm ! m - xa, 
                                   p := lm ! m - xa]"
  apply(rule_tac x = x in exI, simp)
  done

lemma exists_small_list_elem5[simp]: 
  "\<lbrakk>m \<noteq> n; p < length lm; lm ! p = 0; m < p; n < p;
    x \<le> lm ! m; lm ! m \<noteq> x\<rbrakk>
  \<Longrightarrow> \<exists>xa<lm ! m. lm[m := x, n := lm ! n + lm ! m, 
                       p := lm ! m - x, p := lm ! m - Suc x] 
               = lm[m := xa, n := lm ! n + lm ! m, 
                       p := lm ! m - Suc xa]"
  apply(rule_tac x = x in exI, simp add: list_update_overwrite)
  done

lemma exists_small_list_elem6[simp]:
  "\<lbrakk>m \<noteq> n; p < length lm; lm ! p = 0; m < p; n < p; x < lm ! m\<rbrakk>
  \<Longrightarrow> \<exists>xa<lm ! m. lm[m := x, n := lm ! n + lm ! m,
                             p := lm ! m - Suc x, m := Suc x]
                = lm[m := Suc xa, n := lm ! n + lm ! m, 
                             p := lm ! m - Suc xa]"
  apply(rule_tac x = x in exI, 
      simp add: list_update_swap list_update_overwrite)
  done

lemma exists_small_list_elem7[simp]: 
  "\<lbrakk>m \<noteq> n; p < length lm; lm ! p = 0; m < p; n < p; x < lm ! m\<rbrakk>
  \<Longrightarrow> \<exists>xa\<le>lm ! m. lm[m := Suc x, n := lm ! n + lm ! m, 
                             p := lm ! m - Suc x] 
               = lm[m := xa, n := lm ! n + lm ! m, p := lm ! m - xa]"
  apply(rule_tac x = "Suc x" in exI, simp)
  done

lemma abc_steps_zero: "abc_steps_l asm ap 0 = asm"
  apply(cases asm, simp add: abc_steps_l.simps)
  done

lemma list_double_update_2:
  "lm[a := x, b := y, a := z] = lm[b := y, a:=z]"
  by (metis list_update_overwrite list_update_swap)

declare Let_def[simp]
lemma addition_halt_lemma: 
  "\<lbrakk>m \<noteq> n; max m n < p; length lm > p\<rbrakk> \<Longrightarrow>
  \<forall>na. \<not> (\<lambda>(as, lm') (m, p). as = 7) 
        (abc_steps_l (0, lm) (addition m n p) na) (m, p) \<and> 
  addition_inv (abc_steps_l (0, lm) (addition m n p) na) m n p lm 
\<longrightarrow> addition_inv (abc_steps_l (0, lm) (addition m n p) 
                                 (Suc na)) m n p lm 
  \<and> ((abc_steps_l (0, lm) (addition m n p) (Suc na), m, p), 
     abc_steps_l (0, lm) (addition m n p) na, m, p) \<in> addition_LE"
proof -
  assume assms:"m\<noteq>n" "max m n < p" "length lm > p"
  { fix na
    obtain a b where ab:"abc_steps_l (0, lm) (addition m n p) na = (a, b)" by force
    assume assms2: "\<not> (\<lambda>(as, lm') (m, p). as = 7) 
        (abc_steps_l (0, lm) (addition m n p) na) (m, p)"
      "addition_inv (abc_steps_l (0, lm) (addition m n p) na) m n p lm"
    have r1:"addition_inv (abc_steps_l (0, lm) (addition m n p) 
                                 (Suc na)) m n p lm" using assms(1-3) assms2
      unfolding abc_step_red2 ab abc_step_l.simps abc_lm_v.simps abc_lm_s.simps 
        addition_inv.simps
      by (auto split:if_splits simp add: addition_inv.simps Suc_diff_Suc)
    have r2:"((abc_steps_l (0, lm) (addition m n p) (Suc na), m, p), 
              abc_steps_l (0, lm) (addition m n p) na, m, p) \<in> addition_LE" using assms(1-3) assms2
      unfolding abc_step_red2 ab 
      apply(auto split:if_splits simp add: addition_inv.simps abc_steps_zero)
      by(auto simp add: addition_LE_def lex_triple_def lex_pair_def 
          abc_step_l.simps abc_lm_v.simps abc_lm_s.simps split: if_splits)
    note r1 r2
  }
  thus ?thesis by auto
qed

lemma  addition_correct': 
  "\<lbrakk>m \<noteq> n; max m n < p; length lm > p; lm ! p = 0\<rbrakk> \<Longrightarrow> 
  \<exists> stp. (\<lambda> (as, lm'). as = 7 \<and> addition_inv (as, lm') m n p lm) 
                        (abc_steps_l (0, lm) (addition m n p) stp)"
  apply(insert halt_lemma2[of addition_LE
        "\<lambda> ((as, lm'), m, p). addition_inv (as, lm') m n p lm"
        "\<lambda> stp. (abc_steps_l (0, lm) (addition m n p) stp, m, p)"
        "\<lambda> ((as, lm'), m, p). as = 7"], 
      simp add: abc_steps_zero addition_inv_init)
  apply(drule_tac addition_halt_lemma,force,force)
  apply (simp,erule_tac exE)
  apply(rename_tac na)
  apply(rule_tac x = na in exI)
  apply(auto)
  done

lemma length_addition[simp]: "length (addition a b c) = 7"
  by(auto simp: addition.simps)

lemma addition_correct:
  assumes "m \<noteq> n" "max m n < p" "length lm > p" "lm ! p = 0"
  shows "{\<lambda> a. a = lm} (addition m n p) {\<lambda> nl. addition_inv (7, nl) m n p lm}"
  using assms
proof(rule_tac abc_Hoare_haltI, simp)
  fix lma
  assume "m \<noteq> n" "m < p \<and> n < p" "p < length lm" "lm ! p = 0"
  then have "\<exists> stp. (\<lambda> (as, lm'). as = 7 \<and> addition_inv (as, lm') m n p lm) 
                        (abc_steps_l (0, lm) (addition m n p) stp)"
    by(rule_tac addition_correct', auto simp: addition_inv.simps)
  then obtain stp where "(\<lambda> (as, lm'). as = 7 \<and> addition_inv (as, lm') m n p lm) 
                        (abc_steps_l (0, lm) (addition m n p) stp)"
    using exE by presburger
  thus "\<exists>na. abc_final (abc_steps_l (0, lm) (addition m n p) na) (addition m n p) \<and>
                  (\<lambda>nl. addition_inv (7, nl) m n p lm) abc_holds_for abc_steps_l (0, lm) (addition m n p) na"
    by(auto intro:exI[of _ stp])
qed

lemma compile_s_correct':
  "{\<lambda>nl. nl = n # 0 \<up> 2 @ anything} addition 0 (Suc 0) 2 [+] [Inc (Suc 0)] {\<lambda>nl. nl = n # Suc n # 0 # anything}"
proof(rule_tac abc_Hoare_plus_halt)
  show "{\<lambda>nl. nl = n # 0 \<up> 2 @ anything} addition 0 (Suc 0) 2 {\<lambda> nl. addition_inv (7, nl) 0 (Suc 0) 2 (n # 0 \<up> 2 @ anything)}"
    by(rule_tac addition_correct, auto simp: numeral_2_eq_2)
next
  show "{\<lambda>nl. addition_inv (7, nl) 0 (Suc 0) 2 (n # 0 \<up> 2 @ anything)} [Inc (Suc 0)] {\<lambda>nl. nl = n # Suc n # 0 # anything}"
    by(rule_tac abc_Hoare_haltI, rule_tac x = 1 in exI, auto simp: addition_inv.simps 
        abc_steps_l.simps abc_step_l.simps abc_fetch.simps numeral_2_eq_2 abc_lm_s.simps abc_lm_v.simps)
qed

declare rec_exec.simps[simp del]

lemma abc_comp_commute: "(A [+] B) [+] C = A [+] (B [+] C)"
  apply(auto simp: abc_comp.simps abc_shift.simps)
  apply(rename_tac x)
  apply(case_tac x, auto)
  done



lemma compile_z_correct: 
  "\<lbrakk>rec_ci z = (ap, arity, fp); rec_exec z [n] = r\<rbrakk> \<Longrightarrow> 
  {\<lambda>nl. nl = n # 0 \<up> (fp - arity) @ anything} ap {\<lambda>nl. nl = n # r # 0 \<up> (fp - Suc arity) @ anything}"
  apply(rule_tac abc_Hoare_haltI)
  apply(rule_tac x = 1 in exI)
  apply(auto simp: abc_steps_l.simps rec_ci.simps rec_ci_z_def 
      numeral_2_eq_2 abc_fetch.simps abc_step_l.simps rec_exec.simps)
  done

lemma compile_s_correct: 
  "\<lbrakk>rec_ci s = (ap, arity, fp); rec_exec s [n] = r\<rbrakk> \<Longrightarrow> 
  {\<lambda>nl. nl = n # 0 \<up> (fp - arity) @ anything} ap {\<lambda>nl. nl = n # r # 0 \<up> (fp - Suc arity) @ anything}"
  apply(auto simp: rec_ci.simps rec_ci_s_def compile_s_correct' rec_exec.simps)
  done

lemma compile_id_correct':
  assumes "n < length args" 
  shows "{\<lambda>nl. nl = args @ 0 \<up> 2 @ anything} addition n (length args) (Suc (length args))
  {\<lambda>nl. nl = args @ rec_exec (recf.id (length args) n) args # 0 # anything}"
proof -
  have "{\<lambda>nl. nl = args @ 0 \<up> 2 @ anything} addition n (length args) (Suc (length args))
  {\<lambda>nl. addition_inv (7, nl) n (length args) (Suc (length args)) (args @ 0 \<up> 2 @ anything)}"
    using assms
    by(rule_tac addition_correct, auto simp: numeral_2_eq_2 nth_append)
  thus "?thesis"
    using assms
    by(simp add: addition_inv.simps rec_exec.simps 
        nth_append numeral_2_eq_2 list_update_append)
qed

lemma compile_id_correct: 
  "\<lbrakk>n < m; length xs = m; rec_ci (recf.id m n) = (ap, arity, fp); rec_exec (recf.id m n) xs = r\<rbrakk>
       \<Longrightarrow> {\<lambda>nl. nl = xs @ 0 \<up> (fp - arity) @ anything} ap {\<lambda>nl. nl = xs @ r # 0 \<up> (fp - Suc arity) @ anything}"
  apply(auto simp: rec_ci.simps rec_ci_id.simps compile_id_correct')
  done

lemma cn_merge_gs_tl_app: 
  "cn_merge_gs (gs @ [g]) pstr = 
        cn_merge_gs gs pstr [+] cn_merge_gs [g] (pstr + length gs)"
  apply(induct gs arbitrary: pstr, simp add: cn_merge_gs.simps, auto)
  apply(simp add: abc_comp_commute)
  done

lemma footprint_ge: 
  "rec_ci a = (p, arity, fp) \<Longrightarrow> arity < fp"
proof(induct a)
  case (Cn x1 a x3)
  then show ?case by(cases "rec_ci a", auto simp:rec_ci.simps)
next
  case (Pr x1 a1 a2)
  then show ?case by(cases "rec_ci a1";cases "rec_ci a2", auto simp:rec_ci.simps)
next
  case (Mn x1 a)
  then show ?case by(cases "rec_ci a", auto simp:rec_ci.simps)
qed (auto simp: rec_ci.simps)

lemma param_pattern: 
  "\<lbrakk>terminate f xs; rec_ci f = (p, arity, fp)\<rbrakk> \<Longrightarrow> length xs = arity"
proof(induct arbitrary: p arity fp rule: terminate.induct)
  case (termi_cn f xs gs n) thus ?case 
    by(cases "rec_ci f", (auto simp: rec_ci.simps))
next
  case (termi_pr x g xs n f) thus ?case 
    by (cases "rec_ci f", cases "rec_ci g", auto simp: rec_ci.simps)
next
  case (termi_mn xs n f r) thus ?case 
    by (cases "rec_ci f", auto simp: rec_ci.simps)
qed (auto simp: rec_ci.simps)

lemma replicate_merge_anywhere: 
  "x\<up>a @ x\<up>b @ ys = x\<up>(a+b) @ ys"
  by(simp add:replicate_add)

fun mv_box_inv :: "nat \<times> nat list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> bool"
  where
    "mv_box_inv (as, lm) m n initlm = 
         (let plus = initlm ! m + initlm ! n in
           length initlm > max m n \<and> m \<noteq> n \<and> 
              (if as = 0 then \<exists> k l. lm = initlm[m := k, n := l] \<and> 
                    k + l = plus \<and> k \<le> initlm ! m 
              else if as = 1 then \<exists> k l. lm = initlm[m := k, n := l]
                             \<and> k + l + 1 = plus \<and> k < initlm ! m 
              else if as = 2 then \<exists> k l. lm = initlm[m := k, n := l] 
                              \<and> k + l = plus \<and> k \<le> initlm ! m
              else if as = 3 then lm = initlm[m := 0, n := plus]
              else False))"

fun mv_box_stage1 :: "nat \<times> nat list \<Rightarrow> nat \<Rightarrow> nat"
  where
    "mv_box_stage1 (as, lm) m  = 
            (if as = 3 then 0 
             else 1)"

fun mv_box_stage2 :: "nat \<times> nat list \<Rightarrow> nat \<Rightarrow> nat"
  where
    "mv_box_stage2 (as, lm) m = (lm ! m)"

fun mv_box_stage3 :: "nat \<times> nat list \<Rightarrow> nat \<Rightarrow> nat"
  where
    "mv_box_stage3 (as, lm) m = (if as = 1 then 3 
                                else if as = 2 then 2
                                else if as = 0 then 1 
                                else 0)"

fun mv_box_measure :: "((nat \<times> nat list) \<times> nat) \<Rightarrow> (nat \<times> nat \<times> nat)"
  where
    "mv_box_measure ((as, lm), m) = 
     (mv_box_stage1 (as, lm) m, mv_box_stage2 (as, lm) m,
      mv_box_stage3 (as, lm) m)"

definition lex_pair :: "((nat \<times> nat) \<times> nat \<times> nat) set"
  where
    "lex_pair = less_than <*lex*> less_than"

definition lex_triple :: 
  "((nat \<times> (nat \<times> nat)) \<times> (nat \<times> (nat \<times> nat))) set"
  where
    "lex_triple \<equiv> less_than <*lex*> lex_pair"

definition mv_box_LE :: 
  "(((nat \<times> nat list) \<times> nat) \<times> ((nat \<times> nat list) \<times> nat)) set"
  where 
    "mv_box_LE \<equiv> (inv_image lex_triple mv_box_measure)"

lemma wf_lex_triple: "wf lex_triple"
  by (auto simp:lex_triple_def lex_pair_def)

lemma wf_mv_box_le[intro]: "wf mv_box_LE"
  by(auto intro:wf_lex_triple simp: mv_box_LE_def)

declare mv_box_inv.simps[simp del]

lemma mv_box_inv_init:  
  "\<lbrakk>m < length initlm; n < length initlm; m \<noteq> n\<rbrakk> \<Longrightarrow> 
  mv_box_inv (0, initlm) m n initlm"
  apply(simp add: abc_steps_l.simps mv_box_inv.simps)
  apply(rule_tac x = "initlm ! m" in exI, 
      rule_tac x = "initlm ! n" in exI, simp)
  done

lemma abc_fetch[simp]:
  "abc_fetch 0 (mv_box m n) = Some (Dec m 3)"
  "abc_fetch (Suc 0) (mv_box m n) = Some (Inc n)"
  "abc_fetch 2 (mv_box m n) = Some (Goto 0)"
  "abc_fetch 3 (mv_box m n) = None"
     apply(simp_all add: mv_box.simps abc_fetch.simps)
  done

lemma replicate_Suc_iff_anywhere: "x # x\<up>b @ ys = x\<up>(Suc b) @ ys"
  by simp

lemma exists_smaller_in_list0[simp]: 
  "\<lbrakk>m \<noteq> n; m < length initlm; n < length initlm;
    k + l = initlm ! m + initlm ! n; k \<le> initlm ! m; 0 < k\<rbrakk>
 \<Longrightarrow> \<exists>ka la. initlm[m := k, n := l, m := k - Suc 0] = 
     initlm[m := ka, n := la] \<and>
     Suc (ka + la) = initlm ! m + initlm ! n \<and> 
     ka < initlm ! m"
  apply(rule_tac x = "k - Suc 0" in exI, rule_tac x = l in exI, auto)
  apply(subgoal_tac 
      "initlm[m := k, n := l, m := k - Suc 0] = 
       initlm[n := l, m := k, m := k - Suc 0]",force intro:list_update_swap)
  by(simp add: list_update_swap)

lemma exists_smaller_in_list1[simp]:
  "\<lbrakk>m \<noteq> n; m < length initlm; n < length initlm; 
    Suc (k + l) = initlm ! m + initlm ! n;
    k < initlm ! m\<rbrakk>
    \<Longrightarrow> \<exists>ka la. initlm[m := k, n := l, n := Suc l] = 
                initlm[m := ka, n := la] \<and> 
                ka + la = initlm ! m + initlm ! n \<and> 
                ka \<le> initlm ! m"
  apply(rule_tac x = k in exI, rule_tac x = "Suc l" in exI, auto)
  done

lemma abc_steps_prop[simp]: 
  "\<lbrakk>length initlm > max m n; m \<noteq> n\<rbrakk> \<Longrightarrow> 
   \<not> (\<lambda>(as, lm) m. as = 3) 
    (abc_steps_l (0, initlm) (mv_box m n) na) m \<and> 
  mv_box_inv (abc_steps_l (0, initlm) 
           (mv_box m n) na) m n initlm \<longrightarrow>
  mv_box_inv (abc_steps_l (0, initlm) 
           (mv_box m n) (Suc na)) m n initlm \<and>
  ((abc_steps_l (0, initlm) (mv_box m n) (Suc na), m),
   abc_steps_l (0, initlm) (mv_box m n) na, m) \<in> mv_box_LE"
  apply(rule impI, simp add: abc_step_red2)
  apply(cases "(abc_steps_l (0, initlm) (mv_box m n) na)",
      simp)
  apply(auto split:if_splits simp add:abc_steps_l.simps mv_box_inv.simps)
       apply(auto simp add: mv_box_LE_def lex_triple_def lex_pair_def 
      abc_step_l.simps abc_steps_l.simps
      mv_box_inv.simps abc_lm_v.simps abc_lm_s.simps
      split: if_splits )
  apply(rule_tac x = k in exI, rule_tac x = "Suc l" in exI, simp)
  done

lemma mv_box_inv_halt: 
  "\<lbrakk>length initlm > max m n; m \<noteq> n\<rbrakk> \<Longrightarrow> 
  \<exists> stp. (\<lambda> (as, lm). as = 3 \<and> 
  mv_box_inv (as, lm) m n initlm) 
             (abc_steps_l (0::nat, initlm) (mv_box m n) stp)"
  apply(insert halt_lemma2[of mv_box_LE
        "\<lambda> ((as, lm), m). mv_box_inv (as, lm) m n initlm"
        "\<lambda> stp. (abc_steps_l (0, initlm) (mv_box m n) stp, m)"
        "\<lambda> ((as, lm), m). as = (3::nat)"
        ])
  apply(insert wf_mv_box_le)
  apply(simp add: mv_box_inv_init abc_steps_zero)
  apply(erule_tac exE)
  by (metis (no_types, lifting) case_prodE' case_prodI)

lemma mv_box_halt_cond:
  "\<lbrakk>m \<noteq> n; mv_box_inv (a, b) m n lm; a = 3\<rbrakk> \<Longrightarrow> 
  b = lm[n := lm ! m + lm ! n, m := 0]"
  apply(simp add: mv_box_inv.simps, auto)
  apply(simp add: list_update_swap)
  done

lemma mv_box_correct':
  "\<lbrakk>length lm > max m n; m \<noteq> n\<rbrakk> \<Longrightarrow> 
  \<exists> stp. abc_steps_l (0::nat, lm) (mv_box m n) stp
  = (3, (lm[n := (lm ! m + lm ! n)])[m := 0::nat])"
  by(drule mv_box_inv_halt, auto dest:mv_box_halt_cond)

lemma length_mvbox[simp]: "length (mv_box m n) = 3"
  by(simp add: mv_box.simps)

lemma mv_box_correct: 
  "\<lbrakk>length lm > max m n; m\<noteq>n\<rbrakk> 
  \<Longrightarrow> {\<lambda> nl. nl = lm} mv_box m n {\<lambda> nl. nl = lm[n := (lm ! m + lm ! n), m:=0]}"
  apply(drule_tac mv_box_correct', simp)
  apply(auto simp: abc_Hoare_halt_def)
  by (metis abc_final.simps abc_holds_for.simps length_mvbox)

declare list_update.simps(2)[simp del]

lemma zero_case_rec_exec[simp]:
  "\<lbrakk>length xs < gf; gf \<le> ft; n < length gs\<rbrakk>
  \<Longrightarrow> (rec_exec (gs ! n) xs # 0 \<up> (ft - Suc (length xs)) @ map (\<lambda>i. rec_exec i xs) (take n gs) @ 0 \<up> (length gs - n) @ 0 # 0 \<up> length xs @ anything)
  [ft + n - length xs := rec_exec (gs ! n) xs, 0 := 0] =
  0 \<up> (ft - length xs) @ map (\<lambda>i. rec_exec i xs) (take n gs) @ rec_exec (gs ! n) xs # 0 \<up> (length gs - Suc n) @ 0 # 0 \<up> length xs @ anything"
  using list_update_append[of "rec_exec (gs ! n) xs # 0 \<up> (ft - Suc (length xs)) @ map (\<lambda>i. rec_exec i xs) (take n gs)"
      "0 \<up> (length gs - n) @ 0 # 0 \<up> length xs @ anything" "ft + n - length xs" "rec_exec (gs ! n) xs"]
  apply(auto)
  apply(cases "length gs - n", simp, simp add: list_update.simps replicate_Suc_iff_anywhere Suc_diff_Suc del: replicate_Suc)
  apply(simp add: list_update.simps)
  done

lemma compile_cn_gs_correct':
  assumes
    g_cond: "\<forall>g\<in>set (take n gs). terminate g xs \<and>
  (\<forall>x xa xb. rec_ci g = (x, xa, xb) \<longrightarrow> (\<forall>xc. {\<lambda>nl. nl = xs @ 0 \<up> (xb - xa) @ xc} x {\<lambda>nl. nl = xs @ rec_exec g xs # 0 \<up> (xb - Suc xa) @ xc}))"
    and ft: "ft = max (Suc (length xs)) (Max (insert ffp ((\<lambda>(aprog, p, n). n) ` rec_ci ` set gs)))"
  shows 
    "{\<lambda>nl. nl = xs @ 0 # 0 \<up> (ft + length gs) @ anything}
    cn_merge_gs (map rec_ci (take n gs)) ft
  {\<lambda>nl. nl = xs @ 0 \<up> (ft - length xs) @
                    map (\<lambda>i. rec_exec i xs) (take n gs) @ 0\<up>(length gs - n) @ 0 \<up> Suc (length xs) @ anything}"
  using g_cond
proof(induct n)
  case 0
  have "ft > length xs"
    using ft
    by simp
  thus "?case"
    apply(rule_tac abc_Hoare_haltI)
    apply(rule_tac x = 0 in exI, simp add: abc_steps_l.simps replicate_add[THEN sym] 
        replicate_Suc[THEN sym] del: replicate_Suc)
    done
next
  case (Suc n)
  have ind': "\<forall>g\<in>set (take n gs).
     terminate g xs \<and> (\<forall>x xa xb. rec_ci g = (x, xa, xb) \<longrightarrow> 
    (\<forall>xc. {\<lambda>nl. nl = xs @ 0 \<up> (xb - xa) @ xc} x {\<lambda>nl. nl = xs @ rec_exec g xs # 0 \<up> (xb - Suc xa) @ xc})) \<Longrightarrow>
    {\<lambda>nl. nl = xs @ 0 # 0 \<up> (ft + length gs) @ anything} cn_merge_gs (map rec_ci (take n gs)) ft 
    {\<lambda>nl. nl = xs @ 0 \<up> (ft - length xs) @ map (\<lambda>i. rec_exec i xs) (take n gs) @ 0 \<up> (length gs - n) @ 0 \<up> Suc (length xs) @ anything}"
    by fact
  have g_newcond: "\<forall>g\<in>set (take (Suc n) gs).
     terminate g xs \<and> (\<forall>x xa xb. rec_ci g = (x, xa, xb) \<longrightarrow> (\<forall>xc. {\<lambda>nl. nl = xs @ 0 \<up> (xb - xa) @ xc} x {\<lambda>nl. nl = xs @ rec_exec g xs # 0 \<up> (xb - Suc xa) @ xc}))"
    by fact
  from g_newcond have ind:
    "{\<lambda>nl. nl = xs @ 0 # 0 \<up> (ft + length gs) @ anything} cn_merge_gs (map rec_ci (take n gs)) ft 
    {\<lambda>nl. nl = xs @ 0 \<up> (ft - length xs) @ map (\<lambda>i. rec_exec i xs) (take n gs) @ 0 \<up> (length gs - n) @ 0 \<up> Suc (length xs) @ anything}"
    apply(rule_tac ind', rule_tac ballI, erule_tac x = g in ballE, simp_all add: take_Suc)
    by(cases "n < length gs", simp add:take_Suc_conv_app_nth, simp)    
  show "?case"
  proof(cases "n < length gs")
    case True
    have h: "n < length gs" by fact
    thus "?thesis"
    proof(simp add: take_Suc_conv_app_nth cn_merge_gs_tl_app)
      obtain gp ga gf where a: "rec_ci (gs!n) = (gp, ga, gf)"
        by (metis prod_cases3)
      moreover have "min (length gs) n = n"
        using h by simp
      moreover have 
        "{\<lambda>nl. nl = xs @ 0 # 0 \<up> (ft + length gs) @ anything}
        cn_merge_gs (map rec_ci (take n gs)) ft [+] (gp [+] mv_box ga (ft + n))
        {\<lambda>nl. nl = xs @ 0 \<up> (ft - length xs) @ map (\<lambda>i. rec_exec i xs) (take n gs) @ 
        rec_exec (gs ! n) xs # 0 \<up> (length gs - Suc n) @ 0 # 0 \<up> length xs @ anything}"
      proof(rule_tac abc_Hoare_plus_halt)
        show "{\<lambda>nl. nl = xs @ 0 # 0 \<up> (ft + length gs) @ anything} cn_merge_gs (map rec_ci (take n gs)) ft
          {\<lambda>nl. nl = xs @ 0 \<up> (ft - length xs) @ map (\<lambda>i. rec_exec i xs) (take n gs) @ 0 \<up> (length gs - n) @ 0 \<up> Suc (length xs) @ anything}"
          using ind by simp
      next
        have x: "gs!n \<in> set (take (Suc n) gs)"
          using h
          by(simp add: take_Suc_conv_app_nth)
        have b: "terminate (gs!n) xs"
          using a g_newcond h x
          by(erule_tac x = "gs!n" in ballE, simp_all)
        hence c: "length xs = ga"
          using a param_pattern by metis  
        have d: "gf > ga" using footprint_ge a by simp
        have e: "ft \<ge> gf"
          using ft a h Max_ge image_eqI
          by(simp, rule_tac max.coboundedI2, rule_tac Max_ge, simp, 
              rule_tac insertI2,  
              rule_tac f = "(\<lambda>(aprog, p, n). n)" and x = "rec_ci (gs!n)" in image_eqI, simp, 
              rule_tac x = "gs!n" in image_eqI, simp, simp)
        show "{\<lambda>nl. nl = xs @ 0 \<up> (ft - length xs) @ 
          map (\<lambda>i. rec_exec i xs) (take n gs) @ 0 \<up> (length gs - n) @ 0 \<up> Suc (length xs) @ anything} gp [+] mv_box ga (ft + n)
          {\<lambda>nl. nl = xs @ 0 \<up> (ft - length xs) @ map (\<lambda>i. rec_exec i xs) 
          (take n gs) @ rec_exec (gs ! n) xs # 0 \<up> (length gs - Suc n) @ 0 # 0 \<up> length xs @ anything}"
        proof(rule_tac abc_Hoare_plus_halt)
          show "{\<lambda>nl. nl = xs @ 0 \<up> (ft - length xs) @ map (\<lambda>i. rec_exec i xs) (take n gs) @ 0 \<up> (length gs - n) @ 0 \<up> Suc (length xs) @ anything} gp 
                {\<lambda>nl. nl = xs @ (rec_exec (gs!n) xs) # 0 \<up> (ft - Suc (length xs)) @ map (\<lambda>i. rec_exec i xs) 
                              (take n gs) @  0 \<up> (length gs - n) @ 0 # 0 \<up> length xs @ anything}"
          proof -
            have 
              "({\<lambda>nl. nl = xs @ 0 \<up> (gf - ga) @ 0\<up>(ft - gf)@map (\<lambda>i. rec_exec i xs) (take n gs) @ 0 \<up> (length gs - n) @ 0 \<up> Suc (length xs) @ anything} 
            gp {\<lambda>nl. nl = xs @ (rec_exec (gs!n) xs) # 0 \<up> (gf - Suc ga) @ 
              0\<up>(ft - gf)@map (\<lambda>i. rec_exec i xs) (take n gs) @ 0 \<up> (length gs - n) @ 0 \<up> Suc (length xs) @ anything})"
              using a g_newcond h x
              apply(erule_tac x = "gs!n" in ballE)
               apply(simp, simp)
              done            
            thus "?thesis"
              using a b c d e
              by(simp add: replicate_merge_anywhere)
          qed
        next
          show 
            "{\<lambda>nl. nl = xs @ rec_exec (gs ! n) xs #
            0 \<up> (ft - Suc (length xs)) @ map (\<lambda>i. rec_exec i xs) (take n gs) @ 0 \<up> (length gs - n) @ 0 # 0 \<up> length xs @ anything}
            mv_box ga (ft + n)
            {\<lambda>nl. nl = xs @ 0 \<up> (ft - length xs) @ map (\<lambda>i. rec_exec i xs) (take n gs) @
            rec_exec (gs ! n) xs # 0 \<up> (length gs - Suc n) @ 0 # 0 \<up> length xs @ anything}"
          proof -
            have "{\<lambda>nl. nl = xs @ rec_exec (gs ! n) xs # 0 \<up> (ft - Suc (length xs)) @
              map (\<lambda>i. rec_exec i xs) (take n gs) @ 0 \<up> (length gs - n) @ 0 # 0 \<up> length xs @ anything}
              mv_box ga (ft + n) {\<lambda>nl. nl = (xs @ rec_exec (gs ! n) xs # 0 \<up> (ft - Suc (length xs)) @
              map (\<lambda>i. rec_exec i xs) (take n gs) @ 0 \<up> (length gs - n) @ 0 # 0 \<up> length xs @ anything)
              [ft + n := (xs @ rec_exec (gs ! n) xs # 0 \<up> (ft - Suc (length xs)) @ map (\<lambda>i. rec_exec i xs) (take n gs) @ 
              0 \<up> (length gs - n) @ 0 # 0 \<up> length xs @ anything) ! ga +
              (xs @ rec_exec (gs ! n) xs # 0 \<up> (ft - Suc (length xs)) @ 
              map (\<lambda>i. rec_exec i xs) (take n gs) @ 0 \<up> (length gs - n) @ 0 # 0 \<up> length xs @ anything) !
                      (ft + n),  ga := 0]}"
              using a c d e h
              apply(rule_tac mv_box_correct)
               apply(simp, arith, arith)
              done
            moreover have "(xs @ rec_exec (gs ! n) xs # 0 \<up> (ft - Suc (length xs)) @
              map (\<lambda>i. rec_exec i xs) (take n gs) @ 0 \<up> (length gs - n) @ 0 # 0 \<up> length xs @ anything)
              [ft + n := (xs @ rec_exec (gs ! n) xs # 0 \<up> (ft - Suc (length xs)) @ map (\<lambda>i. rec_exec i xs) (take n gs) @ 
              0 \<up> (length gs - n) @ 0 # 0 \<up> length xs @ anything) ! ga +
              (xs @ rec_exec (gs ! n) xs # 0 \<up> (ft - Suc (length xs)) @ 
              map (\<lambda>i. rec_exec i xs) (take n gs) @ 0 \<up> (length gs - n) @ 0 # 0 \<up> length xs @ anything) !
                      (ft + n),  ga := 0]= 
              xs @ 0 \<up> (ft - length xs) @ map (\<lambda>i. rec_exec i xs) (take n gs) @ rec_exec (gs ! n) xs # 0 \<up> (length gs - Suc n) @ 0 # 0 \<up> length xs @ anything"
              using a c d e h
              by(simp add: list_update_append nth_append length_replicate split: if_splits del: list_update.simps(2), auto)
            ultimately show "?thesis"
              by(simp)
          qed
        qed  
      qed
      ultimately show 
        "{\<lambda>nl. nl = xs @ 0 # 0 \<up> (ft + length gs) @ anything}
        cn_merge_gs (map rec_ci (take n gs)) ft [+] (case rec_ci (gs ! n) of (gprog, gpara, gn) \<Rightarrow>
        gprog [+] mv_box gpara (ft + min (length gs) n))
        {\<lambda>nl. nl = xs @ 0 \<up> (ft - length xs) @ map (\<lambda>i. rec_exec i xs) (take n gs) @ rec_exec (gs ! n) xs # 0 \<up> (length gs - Suc n) @ 0 # 0 \<up> length xs @ anything}"
        by simp
    qed
  next
    case False
    have h: "\<not> n < length gs" by fact
    hence ind': 
      "{\<lambda>nl. nl = xs @ 0 # 0 \<up> (ft + length gs) @ anything} cn_merge_gs (map rec_ci gs) ft
        {\<lambda>nl. nl = xs @ 0 \<up> (ft - length xs) @ map (\<lambda>i. rec_exec i xs) gs @ 0 \<up> Suc (length xs) @ anything}"
      using ind
      by simp
    thus "?thesis"
      using h
      by(simp)
  qed
qed

lemma compile_cn_gs_correct:
  assumes
    g_cond: "\<forall>g\<in>set gs. terminate g xs \<and>
  (\<forall>x xa xb. rec_ci g = (x, xa, xb) \<longrightarrow> (\<forall>xc. {\<lambda>nl. nl = xs @ 0 \<up> (xb - xa) @ xc} x {\<lambda>nl. nl = xs @ rec_exec g xs # 0 \<up> (xb - Suc xa) @ xc}))"
    and ft: "ft = max (Suc (length xs)) (Max (insert ffp ((\<lambda>(aprog, p, n). n) ` rec_ci ` set gs)))"
  shows 
    "{\<lambda>nl. nl = xs @ 0 # 0 \<up> (ft + length gs) @ anything}
    cn_merge_gs (map rec_ci gs) ft
  {\<lambda>nl. nl = xs @ 0 \<up> (ft - length xs) @
                    map (\<lambda>i. rec_exec i xs) gs @ 0 \<up> Suc (length xs) @ anything}"
  using assms
  using compile_cn_gs_correct'[of "length gs" gs xs ft ffp anything ]
  apply(auto)
  done

lemma length_mvboxes[simp]: "length (mv_boxes aa ba n) = 3*n"
  by(induct n, auto simp: mv_boxes.simps)

lemma exp_suc: "a\<up>Suc b = a\<up>b @ [a]"
  by(simp add: exp_ind del: replicate.simps)

lemma last_0[simp]: 
  "\<lbrakk>Suc n \<le> ba - aa;  length lm2 = Suc n;
    length lm3 = ba - Suc (aa + n)\<rbrakk>
  \<Longrightarrow> (last lm2 # lm3 @ butlast lm2 @ 0 # lm4) ! (ba - aa) = (0::nat)"
proof -
  assume h: "Suc n \<le> ba - aa"
    and g: "length lm2 = Suc n" "length lm3 = ba - Suc (aa + n)"
  from h and g have k: "ba - aa = Suc (length lm3 + n)"
    by arith
  from  k show 
    "(last lm2 # lm3 @ butlast lm2 @ 0 # lm4) ! (ba - aa) = 0"
    apply(simp, insert g)
    apply(simp add: nth_append)
    done
qed

lemma butlast_last[simp]: "length lm1 = aa \<Longrightarrow>
      (lm1 @ 0\<up>n @ last lm2 # lm3 @ butlast lm2 @ 0 # lm4) ! (aa + n) = last lm2"
  apply(simp add: nth_append)
  done

lemma arith_as_simp[simp]: "\<lbrakk>Suc n \<le> ba - aa; aa < ba\<rbrakk> \<Longrightarrow> 
                    (ba < Suc (aa + (ba - Suc (aa + n) + n))) = False"
  apply arith
  done

lemma butlast_elem[simp]: "\<lbrakk>Suc n \<le> ba - aa; aa < ba; length lm1 = aa; 
       length lm2 = Suc n; length lm3 = ba - Suc (aa + n)\<rbrakk>
     \<Longrightarrow> (lm1 @ 0\<up>n @ last lm2 # lm3 @ butlast lm2 @ 0 # lm4) ! (ba + n) = 0"
  using nth_append[of "lm1 @ (0::'a)\<up>n @ last lm2 # lm3 @ butlast lm2" 
      "(0::'a) # lm4" "ba + n"]
  apply(simp)
  done

lemma update_butlast_eq0[simp]: 
  "\<lbrakk>Suc n \<le> ba - aa; aa < ba; length lm1 = aa; length lm2 = Suc n;
                 length lm3 = ba - Suc (aa + n)\<rbrakk>
  \<Longrightarrow> (lm1 @ 0\<up>n @ last lm2 # lm3 @ butlast lm2 @ (0::nat) # lm4)
  [ba + n := last lm2, aa + n := 0] = 
  lm1 @ 0 # 0\<up>n @ lm3 @ lm2 @ lm4"
  using list_update_append[of "lm1 @ 0\<up>n @ last lm2 # lm3 @ butlast lm2" "0 # lm4" 
      "ba + n" "last lm2"]
  apply(simp add: list_update_append list_update.simps(2-) replicate_Suc_iff_anywhere exp_suc
      del: replicate_Suc)
  apply(cases lm2, simp, simp)
  done

lemma update_butlast_eq1[simp]:
  "\<lbrakk>Suc (length lm1 + n) \<le> ba; length lm2 = Suc n; length lm3 = ba - Suc (length lm1 + n); 
  \<not> ba - Suc (length lm1) < ba - Suc (length lm1 + n); \<not> ba + n - length lm1 < n\<rbrakk>
    \<Longrightarrow> (0::nat) \<up> n @ (last lm2 # lm3 @ butlast lm2 @ 0 # lm4)[ba - length lm1 := last lm2, 0 := 0] =
  0 # 0 \<up> n @ lm3 @ lm2 @ lm4"
  apply(subgoal_tac "ba - length lm1 = Suc n + length lm3", simp add: list_update.simps(2-) list_update_append)
   apply(simp add: replicate_Suc_iff_anywhere exp_suc del: replicate_Suc)
   apply(cases lm2, simp, simp)
  apply(auto)
  done

lemma mv_boxes_correct: 
  "\<lbrakk>aa + n \<le> ba; ba > aa; length lm1 = aa; length lm2 = n; length lm3 = ba - aa - n\<rbrakk>
 \<Longrightarrow> {\<lambda> nl. nl = lm1 @ lm2 @ lm3 @ 0\<up>n @ lm4} (mv_boxes aa ba n) 
     {\<lambda> nl. nl = lm1 @ 0\<up>n @ lm3 @ lm2 @ lm4}"
proof(induct n arbitrary: lm2 lm3 lm4)
  case 0
  thus "?case"
    by(simp add: mv_boxes.simps abc_Hoare_halt_def, rule_tac  x = 0 in exI, simp add: abc_steps_l.simps)
next
  case (Suc n)
  have ind: 
    "\<And>lm2 lm3 lm4.
    \<lbrakk>aa + n \<le> ba; aa < ba; length lm1 = aa; length lm2 = n; length lm3 = ba - aa - n\<rbrakk>
    \<Longrightarrow> {\<lambda>nl. nl = lm1 @ lm2 @ lm3 @ 0 \<up> n @ lm4} mv_boxes aa ba n {\<lambda>nl. nl = lm1 @ 0 \<up> n @ lm3 @ lm2 @ lm4}"
    by fact
  have h1: "aa + Suc n \<le> ba"  by fact
  have h2: "aa < ba" by fact
  have h3: "length lm1 = aa" by fact
  have h4: "length lm2 = Suc n" by fact 
  have h5: "length lm3 = ba - aa - Suc n" by fact
  have "{\<lambda>nl. nl = lm1 @ lm2 @ lm3 @ 0 \<up> Suc n @ lm4} mv_boxes aa ba n [+] mv_box (aa + n) (ba + n)
    {\<lambda>nl. nl = lm1 @ 0 \<up> Suc n @ lm3 @ lm2 @ lm4}"
  proof(rule_tac abc_Hoare_plus_halt)
    have "{\<lambda>nl. nl = lm1 @ butlast lm2 @ (last lm2 # lm3) @ 0 \<up> n @ (0 # lm4)} mv_boxes aa ba n
          {\<lambda> nl. nl = lm1 @ 0\<up>n @ (last lm2 # lm3) @ butlast lm2 @ (0 # lm4)}"
      using h1 h2 h3 h4 h5
      by(rule_tac ind, simp_all)
    moreover have " lm1 @ butlast lm2 @ (last lm2 # lm3) @ 0 \<up> n @ (0 # lm4)
                  = lm1 @ lm2 @ lm3 @ 0 \<up> Suc n @ lm4"
      using h4
      by(simp add: replicate_Suc[THEN sym] exp_suc del: replicate_Suc, 
          cases lm2, simp_all)
    ultimately show "{\<lambda>nl. nl = lm1 @ lm2 @ lm3 @ 0 \<up> Suc n @ lm4} mv_boxes aa ba n
          {\<lambda> nl. nl = lm1 @ 0\<up>n @ last lm2 # lm3 @ butlast lm2 @ 0 # lm4}"
      by (metis append_Cons)
  next
    let ?lm = "lm1 @ 0 \<up> n @ last lm2 # lm3 @ butlast lm2 @ 0 # lm4"
    have "{\<lambda>nl. nl = ?lm} mv_box (aa + n) (ba + n)
          {\<lambda> nl. nl = ?lm[(ba + n) := ?lm!(aa+n) + ?lm!(ba+n), (aa+n):=0]}"
      using h1 h2 h3 h4  h5
      by(rule_tac mv_box_correct, simp_all)
    moreover have "?lm[(ba + n) := ?lm!(aa+n) + ?lm!(ba+n), (aa+n):=0]
                 =  lm1 @ 0 \<up> Suc n @ lm3 @ lm2 @ lm4"
      using h1 h2 h3 h4 h5
      by(auto simp: nth_append list_update_append split: if_splits)
    ultimately show "{\<lambda>nl. nl = lm1 @ 0 \<up> n @ last lm2 # lm3 @ butlast lm2 @ 0 # lm4} mv_box (aa + n) (ba + n)
          {\<lambda>nl. nl = lm1 @ 0 \<up> Suc n @ lm3 @ lm2 @ lm4}"
      by simp
  qed
  thus "?case"
    by(simp add: mv_boxes.simps)
qed

lemma update_butlast_eq2[simp]:
  "\<lbrakk>Suc n \<le> aa - length lm1; length lm1 < aa; 
  length lm2 = aa - Suc (length lm1 + n); 
  length lm3 = Suc n; 
  \<not> aa - Suc (length lm1) < aa - Suc (length lm1 + n);
  \<not> aa + n - length lm1 < n\<rbrakk>
  \<Longrightarrow> butlast lm3 @ ((0::nat) # lm2 @ 0 \<up> n @ last lm3 # lm4)[0 := last lm3, aa - length lm1 := 0] = lm3 @ lm2 @ 0 # 0 \<up> n @ lm4"
  apply(subgoal_tac "aa - length lm1 = length lm2 + Suc n")
   apply(simp add: list_update.simps list_update_append)
   apply(simp add: replicate_Suc[THEN sym] exp_suc del: replicate_Suc)
   apply(cases lm3, simp, simp)
  apply(auto)
  done

lemma mv_boxes_correct2:
  "\<lbrakk>n \<le> aa - ba; 
    ba < aa; 
    length (lm1::nat list) = ba;
    length (lm2::nat list) = aa - ba - n; 
    length (lm3::nat list) = n\<rbrakk>
  \<Longrightarrow>{\<lambda> nl. nl = lm1 @ 0\<up>n @ lm2 @ lm3 @ lm4}
                (mv_boxes aa ba n) 
     {\<lambda> nl. nl = lm1 @ lm3 @ lm2 @ 0\<up>n @ lm4}"
proof(induct n arbitrary: lm2 lm3 lm4)
  case 0
  thus "?case"
    by(simp add: mv_boxes.simps abc_Hoare_halt_def, rule_tac  x = 0 in exI, simp add: abc_steps_l.simps)
next
  case (Suc n)
  have ind:
    "\<And>lm2 lm3 lm4.
    \<lbrakk>n \<le> aa - ba; ba < aa; length lm1 = ba; length lm2 = aa - ba - n; length lm3 = n\<rbrakk>
    \<Longrightarrow> {\<lambda>nl. nl = lm1 @ 0 \<up> n @ lm2 @ lm3 @ lm4} mv_boxes aa ba n {\<lambda>nl. nl = lm1 @ lm3 @ lm2 @ 0 \<up> n @ lm4}"
    by fact
  have h1: "Suc n \<le> aa - ba" by fact
  have h2: "ba < aa" by fact
  have h3: "length lm1 = ba" by fact 
  have h4: "length lm2 = aa - ba - Suc n" by fact
  have h5: "length lm3 = Suc n" by fact
  have "{\<lambda>nl. nl = lm1 @ 0 \<up> Suc n @ lm2 @ lm3 @ lm4}  mv_boxes aa ba n [+] mv_box (aa + n) (ba + n) 
    {\<lambda>nl. nl = lm1 @ lm3 @ lm2 @ 0 \<up> Suc n @ lm4}"
  proof(rule_tac abc_Hoare_plus_halt)
    have "{\<lambda> nl. nl = lm1 @ 0 \<up> n @ (0 # lm2) @ (butlast lm3) @ (last lm3 # lm4)} mv_boxes aa ba n
           {\<lambda> nl. nl = lm1 @ butlast lm3 @ (0 # lm2) @ 0\<up>n @ (last lm3 # lm4)}"
      using h1 h2 h3 h4 h5
      by(rule_tac ind, simp_all)
    moreover have "lm1 @ 0 \<up> n @ (0 # lm2) @ (butlast lm3) @ (last lm3 # lm4) 
                   = lm1 @ 0 \<up> Suc n @ lm2 @ lm3 @ lm4"
      using h5
      by(simp add: replicate_Suc_iff_anywhere exp_suc 
          del: replicate_Suc, cases lm3, simp_all)
    ultimately show "{\<lambda>nl. nl = lm1 @ 0 \<up> Suc n @ lm2 @ lm3 @ lm4} mv_boxes aa ba n
     {\<lambda> nl. nl = lm1 @ butlast lm3 @ (0 # lm2) @ 0\<up>n @ (last lm3 # lm4)}"
      by metis
  next
    thm mv_box_correct
    let ?lm = "lm1 @ butlast lm3 @ (0 # lm2) @ 0 \<up> n @ last lm3 # lm4"
    have "{\<lambda>nl. nl = ?lm} mv_box (aa + n) (ba + n)
         {\<lambda>nl. nl = ?lm[ba+n := ?lm!(aa+n)+?lm!(ba+n), (aa+n):=0]}"
      using h1 h2 h3 h4 h5
      by(rule_tac mv_box_correct, simp_all)
    moreover have "?lm[ba+n := ?lm!(aa+n)+?lm!(ba+n), (aa+n):=0]
               = lm1 @ lm3 @ lm2 @ 0 \<up> Suc n @ lm4"
      using h1 h2 h3 h4 h5
      by(auto simp: nth_append list_update_append split: if_splits)
    ultimately show "{\<lambda>nl. nl = lm1 @ butlast lm3 @ (0 # lm2) @ 0 \<up> n @ last lm3 # lm4} mv_box (aa + n) (ba + n)
     {\<lambda>nl. nl = lm1 @ lm3 @ lm2 @ 0 \<up> Suc n @ lm4}"
      by simp
  qed
  thus "?case"
    by(simp add: mv_boxes.simps)
qed    

lemma save_paras: 
  "{\<lambda>nl. nl = xs @ 0 \<up> (max (Suc (length xs)) (Max (insert ffp ((\<lambda>(aprog, p, n). n) ` rec_ci ` set gs))) - length xs) @
  map (\<lambda>i. rec_exec i xs) gs @ 0 \<up> Suc (length xs) @ anything}
  mv_boxes 0 (Suc (max (Suc (length xs)) (Max (insert ffp ((\<lambda>(aprog, p, n). n) ` rec_ci ` set gs))) + length gs)) (length xs)
  {\<lambda>nl. nl = 0 \<up> max (Suc (length xs)) (Max (insert ffp ((\<lambda>(aprog, p, n). n) ` rec_ci ` set gs))) @ map (\<lambda>i. rec_exec i xs) gs @ 0 # xs @ anything}"
proof -
  let ?ft = "max (Suc (length xs)) (Max (insert ffp ((\<lambda>(aprog, p, n). n) ` rec_ci ` set gs)))"
  have "{\<lambda>nl. nl = [] @ xs @ (0\<up>(?ft - length xs) @  map (\<lambda>i. rec_exec i xs) gs @ [0]) @ 
          0 \<up> (length xs) @ anything} mv_boxes 0 (Suc ?ft + length gs) (length xs) 
        {\<lambda>nl. nl = [] @ 0 \<up> (length xs) @ (0\<up>(?ft - length xs) @  map (\<lambda>i. rec_exec i xs) gs @ [0]) @ xs @ anything}"
    by(rule_tac mv_boxes_correct, auto)
  thus "?thesis"
    by(simp add: replicate_merge_anywhere)
qed

lemma length_le_max_insert_rec_ci[intro]: 
  "length gs \<le> ffp \<Longrightarrow> length gs \<le> max x1 (Max (insert ffp (x2 ` x3 ` set gs)))"
  apply(rule_tac max.coboundedI2)
  apply(simp add: Max_ge_iff)
  done

lemma restore_new_paras:
  "ffp \<ge> length gs 
 \<Longrightarrow> {\<lambda>nl. nl = 0 \<up> max (Suc (length xs)) (Max (insert ffp ((\<lambda>(aprog, p, n). n) ` rec_ci ` set gs))) @ map (\<lambda>i. rec_exec i xs) gs @ 0 # xs @ anything}
    mv_boxes (max (Suc (length xs)) (Max (insert ffp ((\<lambda>(aprog, p, n). n) ` rec_ci ` set gs)))) 0 (length gs)
  {\<lambda>nl. nl = map (\<lambda>i. rec_exec i xs) gs @ 0 \<up> max (Suc (length xs)) (Max (insert ffp ((\<lambda>(aprog, p, n). n) ` rec_ci ` set gs))) @ 0 # xs @ anything}"
proof -
  let ?ft = "max (Suc (length xs)) (Max (insert ffp ((\<lambda>(aprog, p, n). n) ` rec_ci ` set gs)))"
  assume j: "ffp \<ge> length gs"
  hence "{\<lambda> nl. nl = [] @ 0\<up>length gs @ 0\<up>(?ft - length gs) @  map (\<lambda>i. rec_exec i xs) gs @ ((0 # xs) @ anything)}
       mv_boxes ?ft 0 (length gs)
        {\<lambda> nl. nl = [] @ map (\<lambda>i. rec_exec i xs) gs @ 0\<up>(?ft - length gs) @ 0\<up>length gs @ ((0 # xs) @ anything)}"
    by(rule_tac mv_boxes_correct2, auto)
  moreover have "?ft \<ge> length gs"
    using j
    by(auto)
  ultimately show "?thesis"
    using j
    by(simp add: replicate_merge_anywhere le_add_diff_inverse)
qed

lemma le_max_insert[intro]: "ffp \<le> max x0 (Max (insert ffp (x1 ` x2 ` set gs)))"
  by (rule max.coboundedI2) auto

declare max_less_iff_conj[simp del]

lemma save_rs:
  "\<lbrakk>far = length gs;
  ffp \<le> max (Suc (length xs)) (Max (insert ffp ((\<lambda>(aprog, p, n). n) ` rec_ci ` set gs)));
  far < ffp\<rbrakk>
\<Longrightarrow>  {\<lambda>nl. nl = map (\<lambda>i. rec_exec i xs) gs @
  rec_exec (Cn (length xs) f gs) xs # 0 \<up> max (Suc (length xs))
  (Max (insert ffp ((\<lambda>(aprog, p, n). n) ` rec_ci ` set gs))) @ xs @ anything}
    mv_box far (max (Suc (length xs)) (Max (insert ffp ((\<lambda>(aprog, p, n). n) ` rec_ci ` set gs))))
    {\<lambda>nl. nl = map (\<lambda>i. rec_exec i xs) gs @
               0 \<up> (max (Suc (length xs)) (Max (insert ffp ((\<lambda>(aprog, p, n). n) ` rec_ci ` set gs))) - length gs) @
               rec_exec (Cn (length xs) f gs) xs # 0 \<up> length gs @ xs @ anything}"
proof -
  let ?ft = "max (Suc (length xs)) (Max (insert ffp ((\<lambda>(aprog, p, n). n) ` rec_ci ` set gs)))"
  thm mv_box_correct
  let ?lm= " map (\<lambda>i. rec_exec i xs) gs @ rec_exec (Cn (length xs) f gs) xs # 0 \<up> ?ft @ xs @ anything"
  assume h: "far = length gs" "ffp \<le> ?ft" "far < ffp"
  hence "{\<lambda> nl. nl = ?lm} mv_box far ?ft {\<lambda> nl. nl = ?lm[?ft := ?lm!far + ?lm!?ft, far := 0]}"
    apply(rule_tac mv_box_correct)
    by( auto)  
  moreover have "?lm[?ft := ?lm!far + ?lm!?ft, far := 0]
    = map (\<lambda>i. rec_exec i xs) gs @
    0 \<up> (?ft - length gs) @
    rec_exec (Cn (length xs) f gs) xs # 0 \<up> length gs @ xs @ anything"
    using h
    apply(simp add: nth_append)
    using list_update_length[of "map (\<lambda>i. rec_exec i xs) gs @ rec_exec (Cn (length xs) f gs) xs #
       0 \<up> (?ft - Suc (length gs))" 0 "0 \<up> length gs @ xs @ anything" "rec_exec (Cn (length xs) f gs) xs"]
    apply(simp add: replicate_merge_anywhere replicate_Suc_iff_anywhere del: replicate_Suc)
    by(simp add: list_update_append list_update.simps replicate_Suc_iff_anywhere del: replicate_Suc)
  ultimately show "?thesis"
    by(simp)
qed

lemma length_empty_boxes[simp]: "length (empty_boxes n) = 2*n"
  apply(induct n, simp, simp)
  done

lemma empty_one_box_correct:
  "{\<lambda>nl. nl = 0 \<up> n @ x # lm} [Dec n 2, Goto 0] {\<lambda>nl. nl = 0 # 0 \<up> n @ lm}"
proof(induct x)
  case 0
  thus "?case"
    by(simp add: abc_Hoare_halt_def, 
        rule_tac x = 1 in exI, simp add: abc_steps_l.simps 
        abc_step_l.simps abc_fetch.simps abc_lm_v.simps nth_append abc_lm_s.simps
        replicate_Suc[THEN sym] exp_suc del: replicate_Suc)
next
  case (Suc x)
  have "{\<lambda>nl. nl = 0 \<up> n @ x # lm} [Dec n 2, Goto 0] {\<lambda>nl. nl = 0 # 0 \<up> n @ lm}"
    by fact
  then obtain stp where "abc_steps_l (0, 0 \<up> n @ x # lm) [Dec n 2, Goto 0] stp
                      = (Suc (Suc 0), 0 # 0 \<up> n @ lm)"
    apply(auto simp: abc_Hoare_halt_def)
    by (smt abc_final.simps abc_holds_for.elims(2) length_Cons list.size(3))
  moreover have "abc_steps_l (0, 0\<up>n @ Suc x # lm) [Dec n 2, Goto 0] (Suc (Suc 0)) 
        = (0,  0 \<up> n @ x # lm)"
    by(auto simp: abc_steps_l.simps abc_step_l.simps abc_fetch.simps abc_lm_v.simps
        nth_append abc_lm_s.simps list_update.simps list_update_append)
  ultimately have "abc_steps_l (0, 0\<up>n @ Suc x # lm) [Dec n 2, Goto 0] (Suc (Suc 0) + stp) 
                = (Suc (Suc 0), 0 # 0\<up>n @ lm)"
    by(simp only: abc_steps_add)
  thus "?case"
    apply(simp add: abc_Hoare_halt_def)
    apply(rule_tac x = "Suc (Suc stp)" in exI, simp)
    done
qed

lemma empty_boxes_correct: 
  "length lm \<ge> n \<Longrightarrow>
  {\<lambda> nl. nl = lm} empty_boxes n {\<lambda> nl. nl = 0\<up>n @ drop n lm}"
proof(induct n)
  case 0
  thus "?case"
    by(simp add: empty_boxes.simps abc_Hoare_halt_def, 
        rule_tac x = 0 in exI, simp add: abc_steps_l.simps)
next
  case (Suc n)
  have ind: "n \<le> length lm \<Longrightarrow> {\<lambda>nl. nl = lm} empty_boxes n {\<lambda>nl. nl = 0 \<up> n @ drop n lm}" by fact
  have h: "Suc n \<le> length lm" by fact
  have "{\<lambda>nl. nl = lm} empty_boxes n [+] [Dec n 2, Goto 0] {\<lambda>nl. nl = 0 # 0 \<up> n @ drop (Suc n) lm}"
  proof(rule_tac abc_Hoare_plus_halt)
    show "{\<lambda>nl. nl = lm} empty_boxes n {\<lambda>nl. nl = 0 \<up> n @ drop n lm}"
      using h
      by(rule_tac ind, simp)
  next
    show "{\<lambda>nl. nl = 0 \<up> n @ drop n lm} [Dec n 2, Goto 0] {\<lambda>nl. nl = 0 # 0 \<up> n @ drop (Suc n) lm}"
      using empty_one_box_correct[of n "lm ! n" "drop (Suc n) lm"]
      using h
      by(simp add: Cons_nth_drop_Suc)
  qed
  thus "?case"
    by(simp add: empty_boxes.simps)
qed

lemma insert_dominated[simp]: "length gs \<le> ffp \<Longrightarrow>
    length gs + (max xs (Max (insert ffp (x1 ` x2 ` set gs))) - length gs) =
    max xs (Max (insert ffp (x1 ` x2 ` set gs)))"
  apply(rule_tac le_add_diff_inverse)
  apply(rule_tac max.coboundedI2)
  apply(simp add: Max_ge_iff)
  done


lemma clean_paras: 
  "ffp \<ge> length gs \<Longrightarrow>
  {\<lambda>nl. nl = map (\<lambda>i. rec_exec i xs) gs @
  0 \<up> (max (Suc (length xs)) (Max (insert ffp ((\<lambda>(aprog, p, n). n) ` rec_ci ` set gs))) - length gs) @
  rec_exec (Cn (length xs) f gs) xs # 0 \<up> length gs @ xs @ anything}
  empty_boxes (length gs)
  {\<lambda>nl. nl = 0 \<up> max (Suc (length xs)) (Max (insert ffp ((\<lambda>(aprog, p, n). n) ` rec_ci ` set gs))) @ 
  rec_exec (Cn (length xs) f gs) xs # 0 \<up> length gs @ xs @ anything}"
proof-
  let ?ft = "max (Suc (length xs)) (Max (insert ffp ((\<lambda>(aprog, p, n). n) ` rec_ci ` set gs)))"
  assume h: "length gs \<le> ffp"
  let ?lm = "map (\<lambda>i. rec_exec i xs) gs @ 0 \<up> (?ft - length gs) @
    rec_exec (Cn (length xs) f gs) xs # 0 \<up> length gs @ xs @ anything"
  have "{\<lambda> nl. nl = ?lm} empty_boxes (length gs) {\<lambda> nl. nl = 0\<up>length gs @ drop (length gs) ?lm}"
    by(rule_tac empty_boxes_correct, simp)
  moreover have "0\<up>length gs @ drop (length gs) ?lm 
           =  0 \<up> ?ft @  rec_exec (Cn (length xs) f gs) xs # 0 \<up> length gs @ xs @ anything"
    using h
    by(simp add: replicate_merge_anywhere)
  ultimately show "?thesis"
    by metis
qed


lemma restore_rs:
  "{\<lambda>nl. nl = 0 \<up> max (Suc (length xs)) (Max (insert ffp ((\<lambda>(aprog, p, n). n) ` rec_ci ` set gs))) @ 
  rec_exec (Cn (length xs) f gs) xs # 0 \<up> length gs @ xs @ anything}
  mv_box (max (Suc (length xs)) (Max (insert ffp ((\<lambda>(aprog, p, n). n) ` rec_ci ` set gs)))) (length xs)
  {\<lambda>nl. nl = 0 \<up> length xs @
  rec_exec (Cn (length xs) f gs) xs #
  0 \<up> (max (Suc (length xs)) (Max (insert ffp ((\<lambda>(aprog, p, n). n) ` rec_ci ` set gs))) - (length xs)) @
  0 \<up> length gs @ xs @ anything}"
proof -
  let ?ft = "max (Suc (length xs)) (Max (insert ffp ((\<lambda>(aprog, p, n). n) ` rec_ci ` set gs)))"
  let ?lm = "0\<up>(length xs) @  0\<up>(?ft - (length xs)) @ rec_exec (Cn (length xs) f gs) xs # 0 \<up> length gs @ xs @ anything"
  thm mv_box_correct
  have "{\<lambda> nl. nl = ?lm} mv_box ?ft (length xs) {\<lambda> nl. nl = ?lm[length xs := ?lm!?ft + ?lm!(length xs), ?ft := 0]}"
    by(rule_tac mv_box_correct, simp, simp)
  moreover have "?lm[length xs := ?lm!?ft + ?lm!(length xs), ?ft := 0]
               =  0 \<up> length xs @ rec_exec (Cn (length xs) f gs) xs # 0 \<up> (?ft - (length xs)) @ 0 \<up> length gs @ xs @ anything"
    apply(auto simp: list_update_append nth_append) (* ~ 7 sec *)
    apply(cases ?ft, simp_all add: Suc_diff_le list_update.simps)
    apply(simp add: exp_suc replicate_Suc[THEN sym] del: replicate_Suc)
    done
  ultimately show "?thesis"
    by(simp add: replicate_merge_anywhere)
qed

lemma restore_orgin_paras:
  "{\<lambda>nl. nl = 0 \<up> length xs @
  rec_exec (Cn (length xs) f gs) xs #
  0 \<up> (max (Suc (length xs)) (Max (insert ffp ((\<lambda>(aprog, p, n). n) ` rec_ci ` set gs))) - length xs) @ 0 \<up> length gs @ xs @ anything}
  mv_boxes (Suc (max (Suc (length xs)) (Max (insert ffp ((\<lambda>(aprog, p, n). n) ` rec_ci ` set gs))) + length gs)) 0 (length xs)
  {\<lambda>nl. nl = xs @ rec_exec (Cn (length xs) f gs) xs # 0 \<up> 
  (max (Suc (length xs)) (Max (insert ffp ((\<lambda>(aprog, p, n). n) ` rec_ci ` set gs))) + length gs) @ anything}"
proof -
  let ?ft = "max (Suc (length xs)) (Max (insert ffp ((\<lambda>(aprog, p, n). n) ` rec_ci ` set gs)))"
  thm mv_boxes_correct2
  have "{\<lambda> nl. nl = [] @ 0\<up>(length xs) @ (rec_exec (Cn (length xs) f gs) xs # 0 \<up> (?ft - length xs) @ 0 \<up> length gs) @ xs @ anything}
        mv_boxes (Suc ?ft + length gs) 0 (length xs)
        {\<lambda> nl. nl = [] @ xs @ (rec_exec (Cn (length xs) f gs) xs # 0 \<up> (?ft - length xs) @ 0 \<up> length gs) @ 0\<up>length xs @ anything}"
    by(rule_tac mv_boxes_correct2, auto)
  thus "?thesis"
    by(simp add: replicate_merge_anywhere)
qed

lemma compile_cn_correct':
  assumes f_ind: 
    "\<And> anything r. rec_exec f (map (\<lambda>g. rec_exec g xs) gs) = rec_exec (Cn (length xs) f gs) xs \<Longrightarrow>
  {\<lambda>nl. nl = map (\<lambda>g. rec_exec g xs) gs @ 0 \<up> (ffp - far) @ anything} fap
                {\<lambda>nl. nl = map (\<lambda>g. rec_exec g xs) gs @ rec_exec (Cn (length xs) f gs) xs # 0 \<up> (ffp - Suc far) @ anything}"
    and compile: "rec_ci f = (fap, far, ffp)"
    and term_f: "terminate f (map (\<lambda>g. rec_exec g xs) gs)"
    and g_cond: "\<forall>g\<in>set gs. terminate g xs \<and>
  (\<forall>x xa xb. rec_ci g = (x, xa, xb) \<longrightarrow> 
  (\<forall>xc. {\<lambda>nl. nl = xs @ 0 \<up> (xb - xa) @ xc} x {\<lambda>nl. nl = xs @ rec_exec g xs # 0 \<up> (xb - Suc xa) @ xc}))"
  shows 
    "{\<lambda>nl. nl = xs @ 0 # 0 \<up> (max (Suc (length xs)) (Max (insert ffp ((\<lambda>(aprog, p, n). n) ` rec_ci ` set gs))) + length gs) @ anything}
  cn_merge_gs (map rec_ci gs) (max (Suc (length xs)) (Max (insert ffp ((\<lambda>(aprog, p, n). n) ` rec_ci ` set gs)))) [+]
  (mv_boxes 0 (Suc (max (Suc (length xs)) (Max (insert ffp ((\<lambda>(aprog, p, n). n) ` rec_ci ` set gs))) + length gs)) (length xs) [+]
  (mv_boxes (max (Suc (length xs)) (Max (insert ffp ((\<lambda>(aprog, p, n). n) ` rec_ci ` set gs)))) 0 (length gs) [+]
  (fap [+] (mv_box far (max (Suc (length xs)) (Max (insert ffp ((\<lambda>(aprog, p, n). n) ` rec_ci ` set gs)))) [+]
  (empty_boxes (length gs) [+]
  (mv_box (max (Suc (length xs)) (Max (insert ffp ((\<lambda>(aprog, p, n). n) ` rec_ci ` set gs)))) (length xs) [+]
  mv_boxes (Suc (max (Suc (length xs)) (Max (insert ffp ((\<lambda>(aprog, p, n). n) ` rec_ci ` set gs))) + length gs)) 0 (length xs)))))))
  {\<lambda>nl. nl = xs @ rec_exec (Cn (length xs) f gs) xs # 
0 \<up> (max (Suc (length xs)) (Max (insert ffp ((\<lambda>(aprog, p, n). n) ` rec_ci ` set gs))) + length gs) @ anything}"
proof -
  let ?ft = "max (Suc (length xs)) (Max (insert ffp ((\<lambda>(aprog, p, n). n) ` rec_ci ` set gs)))"
  let ?A = "cn_merge_gs (map rec_ci gs) ?ft"
  let ?B = "mv_boxes 0 (Suc (?ft+length gs)) (length xs)"
  let ?C = "mv_boxes ?ft 0 (length gs)"
  let ?D = fap
  let ?E = "mv_box far ?ft"
  let ?F = "empty_boxes (length gs)"
  let ?G = "mv_box ?ft (length xs)"
  let ?H = "mv_boxes (Suc (?ft + length gs)) 0 (length xs)"
  let ?P1 = "\<lambda>nl. nl = xs @ 0 # 0 \<up> (?ft + length gs) @ anything"
  let ?S = "\<lambda>nl. nl = xs @ rec_exec (Cn (length xs) f gs) xs # 0 \<up> (?ft + length gs) @ anything"
  let ?Q1 = "\<lambda> nl. nl = xs @ 0\<up>(?ft - length xs) @ map (\<lambda> i. rec_exec i xs) gs @ 0\<up>(Suc (length xs)) @ anything"
  show "{?P1} (?A [+] (?B [+] (?C [+] (?D [+] (?E [+] (?F [+] (?G [+] ?H))))))) {?S}"
  proof(rule_tac abc_Hoare_plus_halt)
    show "{?P1} ?A {?Q1}"
      using g_cond
      by(rule_tac compile_cn_gs_correct, auto)
  next
    let ?Q2 = "\<lambda>nl. nl = 0 \<up> ?ft @
                    map (\<lambda>i. rec_exec i xs) gs @ 0 # xs @ anything"
    show "{?Q1} (?B [+] (?C [+] (?D [+] (?E [+] (?F [+] (?G [+] ?H)))))) {?S}"
    proof(rule_tac abc_Hoare_plus_halt)
      show "{?Q1} ?B {?Q2}"
        by(rule_tac save_paras)
    next
      let ?Q3 = "\<lambda> nl. nl = map (\<lambda>i. rec_exec i xs) gs @ 0\<up>?ft @ 0 # xs @ anything" 
      show "{?Q2} (?C [+] (?D [+] (?E [+] (?F [+] (?G [+] ?H))))) {?S}"
      proof(rule_tac abc_Hoare_plus_halt)
        have "ffp \<ge> length gs"
          using compile term_f
          apply(subgoal_tac "length gs = far")
           apply(drule_tac footprint_ge, simp)
          by(drule_tac param_pattern, auto)          
        thus "{?Q2} ?C {?Q3}"
          by(erule_tac restore_new_paras)
      next
        let ?Q4 = "\<lambda> nl. nl = map (\<lambda>i. rec_exec i xs) gs @ rec_exec (Cn (length xs) f gs) xs # 0\<up>?ft @ xs @ anything"
        have a: "far = length gs"
          using compile term_f
          by(drule_tac param_pattern, auto)
        have b:"?ft \<ge> ffp"
          by auto
        have c: "ffp > far"
          using compile
          by(erule_tac footprint_ge)
        show "{?Q3} (?D [+] (?E [+] (?F [+] (?G [+] ?H)))) {?S}"
        proof(rule_tac abc_Hoare_plus_halt)
          have "{\<lambda>nl. nl = map (\<lambda>g. rec_exec g xs) gs @ 0 \<up> (ffp - far) @ 0\<up>(?ft - ffp + far) @ 0 # xs @ anything} fap
            {\<lambda>nl. nl = map (\<lambda>g. rec_exec g xs) gs @ rec_exec (Cn (length xs) f gs) xs # 
            0 \<up> (ffp - Suc far) @ 0\<up>(?ft - ffp + far) @ 0 # xs @ anything}"
            by(rule_tac f_ind, simp add: rec_exec.simps)
          thus "{?Q3} fap {?Q4}"
            using a b c
            by(simp add: replicate_merge_anywhere,
                cases "?ft", simp_all add: exp_suc del: replicate_Suc)
        next
          let ?Q5 = "\<lambda>nl. nl = map (\<lambda>i. rec_exec i xs) gs @
               0\<up>(?ft - length gs) @ rec_exec (Cn (length xs) f gs) xs # 0\<up>(length gs)@ xs @ anything"
          show "{?Q4} (?E [+] (?F [+] (?G [+] ?H))) {?S}"
          proof(rule_tac abc_Hoare_plus_halt)
            from a b c show "{?Q4} ?E {?Q5}"
              by(erule_tac save_rs, simp_all)
          next
            let ?Q6 = "\<lambda>nl. nl = 0\<up>?ft @ rec_exec (Cn (length xs) f gs) xs # 0\<up>(length gs)@ xs @ anything"
            show "{?Q5} (?F [+] (?G [+] ?H)) {?S}"
            proof(rule_tac abc_Hoare_plus_halt)
              have "length gs \<le> ffp" using a b c
                by simp
              thus "{?Q5} ?F {?Q6}"
                by(erule_tac clean_paras)
            next
              let ?Q7 = "\<lambda>nl. nl = 0\<up>length xs @ rec_exec (Cn (length xs) f gs) xs # 0\<up>(?ft - (length xs)) @ 0\<up>(length gs)@ xs @ anything"
              show "{?Q6} (?G [+] ?H) {?S}"
              proof(rule_tac abc_Hoare_plus_halt)
                show "{?Q6} ?G {?Q7}"
                  by(rule_tac restore_rs)
              next
                show "{?Q7} ?H {?S}"
                  by(rule_tac restore_orgin_paras)
              qed
            qed
          qed
        qed        
      qed
    qed
  qed
qed

lemma compile_cn_correct:
  assumes termi_f: "terminate f (map (\<lambda>g. rec_exec g xs) gs)"
    and f_ind: "\<And>ap arity fp anything.
  rec_ci f = (ap, arity, fp)
  \<Longrightarrow> {\<lambda>nl. nl = map (\<lambda>g. rec_exec g xs) gs @ 0 \<up> (fp - arity) @ anything} ap
  {\<lambda>nl. nl = map (\<lambda>g. rec_exec g xs) gs @ rec_exec f (map (\<lambda>g. rec_exec g xs) gs) # 0 \<up> (fp - Suc arity) @ anything}"
    and g_cond: 
    "\<forall>g\<in>set gs. terminate g xs \<and>
  (\<forall>x xa xb. rec_ci g = (x, xa, xb) \<longrightarrow>   (\<forall>xc. {\<lambda>nl. nl = xs @ 0 \<up> (xb - xa) @ xc} x {\<lambda>nl. nl = xs @ rec_exec g xs # 0 \<up> (xb - Suc xa) @ xc}))"
    and compile: "rec_ci (Cn n f gs) = (ap, arity, fp)"
    and len: "length xs = n"
  shows "{\<lambda>nl. nl = xs @ 0 \<up> (fp - arity) @ anything} ap {\<lambda>nl. nl = xs @ rec_exec (Cn n f gs) xs # 0 \<up> (fp - Suc arity) @ anything}"
proof(cases "rec_ci f")
  fix fap far ffp
  assume h: "rec_ci f = (fap, far, ffp)"
  then have f_newind: "\<And> anything .{\<lambda>nl. nl = map (\<lambda>g. rec_exec g xs) gs @ 0 \<up> (ffp - far) @ anything} fap
    {\<lambda>nl. nl = map (\<lambda>g. rec_exec g xs) gs @ rec_exec f (map (\<lambda>g. rec_exec g xs) gs) # 0 \<up> (ffp - Suc far) @ anything}"
    by(rule_tac f_ind, simp_all)
  thus "{\<lambda>nl. nl = xs @ 0 \<up> (fp - arity) @ anything} ap {\<lambda>nl. nl = xs @ rec_exec (Cn n f gs) xs # 0 \<up> (fp - Suc arity) @ anything}"
    using compile len h termi_f g_cond
    apply(auto simp: rec_ci.simps abc_comp_commute)
    apply(rule_tac compile_cn_correct', simp_all)
    done
qed

lemma mv_box_correct_simp[simp]: 
  "\<lbrakk>length xs = n; ft = max (n+3) (max fft gft)\<rbrakk> 
 \<Longrightarrow> {\<lambda>nl. nl = xs @ 0 # 0 \<up> (ft - n) @ anything} mv_box n ft 
       {\<lambda>nl. nl = xs @ 0 # 0 \<up> (ft - n) @ anything}"
  using mv_box_correct[of n ft "xs @ 0 # 0 \<up> (ft - n) @ anything"]
  by(auto)

lemma length_under_max[simp]: "length xs < max (length xs + 3) fft"
  by auto

lemma save_init_rs: 
  "\<lbrakk>length xs = n; ft = max (n+3) (max fft gft)\<rbrakk> 
     \<Longrightarrow>  {\<lambda>nl. nl = xs @ rec_exec f xs # 0 \<up> (ft - n) @ anything} mv_box n (Suc n) 
       {\<lambda>nl. nl = xs @ 0 # rec_exec f xs # 0 \<up> (ft - Suc n) @ anything}"
  using mv_box_correct[of n "Suc n" "xs @ rec_exec f xs # 0 \<up> (ft - n) @ anything"]
  apply(auto simp: list_update_append list_update.simps nth_append split: if_splits)
  apply(cases "(max (length xs + 3) (max fft gft))", simp_all add: list_update.simps Suc_diff_le)
  done

lemma less_then_max_plus2[simp]: "n + (2::nat) < max (n + 3) x"
  by auto

lemma less_then_max_plus3[simp]: "n < max (n + (3::nat)) x"
  by auto

lemma mv_box_max_plus_3_correct[simp]:
  "length xs = n \<Longrightarrow> 
  {\<lambda>nl. nl = xs @ x # 0 \<up> (max (n + (3::nat)) (max fft gft) - n) @ anything} mv_box n (max (n + 3) (max fft gft))
  {\<lambda>nl. nl = xs @ 0 \<up> (max (n + 3) (max fft gft) - n) @ x # anything}"
proof -
  assume h: "length xs = n"
  let ?ft = "max (n+3) (max fft gft)"
  let ?lm = "xs @ x # 0\<up>(?ft - Suc n) @ 0 # anything"
  have g: "?ft > n + 2"
    by simp
  thm mv_box_correct
  have a: "{\<lambda> nl. nl = ?lm} mv_box n ?ft {\<lambda> nl. nl = ?lm[?ft := ?lm!n + ?lm!?ft, n := 0]}"
    using h
    by(rule_tac mv_box_correct, auto)
  have b:"?lm = xs @ x # 0 \<up> (max (n + 3) (max fft gft) - n) @ anything"
    by(cases ?ft, simp_all add: Suc_diff_le exp_suc del: replicate_Suc)
  have c: "?lm[?ft := ?lm!n + ?lm!?ft, n := 0] = xs @ 0 \<up> (max (n + 3) (max fft gft) - n) @ x # anything"
    using h g
    apply(auto simp: nth_append list_update_append split: if_splits)
    using list_update_append[of "x # 0 \<up> (max (length xs + 3) (max fft gft) - Suc (length xs))" "0 # anything"
        "max (length xs + 3) (max fft gft) - length xs" "x"]
    apply(auto simp: if_splits)
    apply(simp add: list_update.simps replicate_Suc[THEN sym] del: replicate_Suc)
    done
  from a c show "?thesis"
    using h
    apply(simp)
    using b
    by simp
qed

lemma max_less_suc_suc[simp]: "max n (Suc n) < Suc (Suc (max (n + 3) x + anything - Suc 0))"
  by arith    

lemma suc_less_plus_3[simp]: "Suc n < max (n + 3) x"
  by arith

lemma mv_box_ok_suc_simp[simp]:
  "length xs = n
 \<Longrightarrow> {\<lambda>nl. nl = xs @ rec_exec f xs # 0 \<up> (max (n + 3) (max fft gft) - Suc n) @ x # anything} mv_box n (Suc n)
    {\<lambda>nl. nl = xs @ 0 # rec_exec f xs # 0 \<up> (max (n + 3) (max fft gft) - Suc (Suc n)) @ x # anything}"
  using mv_box_correct[of n "Suc n" "xs @ rec_exec f xs # 0 \<up> (max (n + 3) (max fft gft) - Suc n) @ x # anything"]
  apply(simp add: nth_append list_update_append list_update.simps)
  apply(cases "max (n + 3) (max fft gft)", simp_all)
  apply(cases "max (n + 3) (max fft gft) - 1", simp_all add: Suc_diff_le list_update.simps(2))
  done

lemma abc_append_frist_steps_eq_pre: 
  assumes notfinal: "abc_notfinal (abc_steps_l (0, lm)  A n) A"
    and notnull: "A \<noteq> []"
  shows "abc_steps_l (0, lm) (A @ B) n = abc_steps_l (0, lm) A n"
  using notfinal
proof(induct n)
  case 0
  thus "?case"
    by(simp add: abc_steps_l.simps)
next
  case (Suc n)
  have ind: "abc_notfinal (abc_steps_l (0, lm) A n) A \<Longrightarrow> abc_steps_l (0, lm) (A @ B) n = abc_steps_l (0, lm) A n"
    by fact
  have h: "abc_notfinal (abc_steps_l (0, lm) A (Suc n)) A" by fact
  then have a: "abc_notfinal (abc_steps_l (0, lm) A n) A"
    by(simp add: notfinal_Suc)
  then have b: "abc_steps_l (0, lm) (A @ B) n = abc_steps_l (0, lm) A n"
    using ind by simp
  obtain s lm' where c: "abc_steps_l (0, lm) A n = (s, lm')"
    by (metis prod.exhaust)
  then have d: "s < length A \<and> abc_steps_l (0, lm) (A @ B) n = (s, lm')" 
    using a b by simp
  thus "?case"
    using c
    by(simp add: abc_step_red2 abc_fetch.simps abc_step_l.simps nth_append)
qed

lemma abc_append_first_step_eq_pre: 
  "st < length A
 \<Longrightarrow> abc_step_l (st, lm) (abc_fetch st (A @ B)) = 
    abc_step_l (st, lm) (abc_fetch st A)"
  by(simp add: abc_step_l.simps abc_fetch.simps nth_append)

lemma abc_append_frist_steps_halt_eq': 
  assumes final: "abc_steps_l (0, lm) A n = (length A, lm')"
    and notnull: "A \<noteq> []"
  shows "\<exists> n'. abc_steps_l (0, lm) (A @ B) n' = (length A, lm')"
proof -
  have "\<exists> n'. abc_notfinal (abc_steps_l (0, lm) A n') A \<and> 
    abc_final (abc_steps_l (0, lm) A (Suc n')) A"
    using assms
    by(rule_tac n = n in abc_before_final, simp_all)
  then obtain na where a:
    "abc_notfinal (abc_steps_l (0, lm) A na) A \<and> 
            abc_final (abc_steps_l (0, lm) A (Suc na)) A" ..
  obtain sa lma where b: "abc_steps_l (0, lm) A na = (sa, lma)"
    by (metis prod.exhaust)
  then have c: "abc_steps_l (0, lm) (A @ B) na = (sa, lma)"
    using a abc_append_frist_steps_eq_pre[of lm A na B] assms 
    by simp
  have d: "sa < length A" using b a by simp
  then have e: "abc_step_l (sa, lma) (abc_fetch sa (A @ B)) = 
    abc_step_l (sa, lma) (abc_fetch sa A)"
    by(rule_tac abc_append_first_step_eq_pre)
  from a have "abc_steps_l (0, lm) A (Suc na) = (length A, lm')"
    using final equal_when_halt
    by(cases "abc_steps_l (0, lm) A (Suc na)" , simp)
  then have "abc_steps_l (0, lm) (A @ B) (Suc na) = (length A, lm')"
    using a b c e
    by(simp add: abc_step_red2)
  thus "?thesis"
    by blast
qed

lemma abc_append_frist_steps_halt_eq: 
  assumes final: "abc_steps_l (0, lm) A n = (length A, lm')"
  shows "\<exists> n'. abc_steps_l (0, lm) (A @ B) n' = (length A, lm')"
  using final
  apply(cases "A = []")
   apply(rule_tac x = 0 in exI, simp add: abc_steps_l.simps abc_exec_null)
  apply(rule_tac abc_append_frist_steps_halt_eq', simp_all)
  done

lemma suc_suc_max_simp[simp]: "Suc (Suc (max (xs + 3) fft - Suc (Suc ( xs))))
           = max ( xs + 3) fft - ( xs)"
  by arith

lemma contract_dec_ft_length_plus_7[simp]: "\<lbrakk>ft = max (n + 3) (max fft gft); length xs = n\<rbrakk> \<Longrightarrow>
     {\<lambda>nl. nl = xs @ (x - Suc y) # rec_exec (Pr n f g) (xs @ [x - Suc y]) # 0 \<up> (ft - Suc (Suc n)) @ Suc y # anything}
     [Dec ft (length gap + 7)] 
     {\<lambda>nl. nl = xs @ (x - Suc y) # rec_exec (Pr n f g) (xs @ [x - Suc y]) # 0 \<up> (ft - Suc (Suc n)) @ y # anything}"
  apply(simp add: abc_Hoare_halt_def)
  apply(rule_tac x = 1 in exI)
  apply(auto simp: abc_steps_l.simps abc_step_l.simps abc_fetch.simps nth_append 
      abc_lm_v.simps abc_lm_s.simps list_update_append)
  using list_update_length
    [of "(x - Suc y) # rec_exec (Pr (length xs) f g) (xs @ [x - Suc y]) #
          0 \<up> (max (length xs + 3) (max fft gft) - Suc (Suc (length xs)))" "Suc y" anything y]
  apply(simp)
  done

lemma adjust_paras': 
  "length xs = n \<Longrightarrow> {\<lambda>nl. nl = xs @ x # y # anything}  [Inc n] [+] [Dec (Suc n) 2, Goto 0]
       {\<lambda>nl. nl = xs @ Suc x # 0 # anything}"
proof(rule_tac abc_Hoare_plus_halt)
  assume "length xs = n"
  thus "{\<lambda>nl. nl = xs @ x # y # anything} [Inc n] {\<lambda> nl. nl = xs @ Suc x # y # anything}"
    apply(simp add: abc_Hoare_halt_def)
    apply(rule_tac x = 1 in exI, force simp add: abc_steps_l.simps abc_step_l.simps
        abc_fetch.simps abc_comp.simps
        abc_lm_v.simps abc_lm_s.simps nth_append list_update_append list_update.simps(2))
    done
next
  assume h: "length xs = n"
  thus "{\<lambda>nl. nl = xs @ Suc x # y # anything} [Dec (Suc n) 2, Goto 0] {\<lambda>nl. nl = xs @ Suc x # 0 # anything}"
  proof(induct y)
    case 0
    thus "?case"
      apply(simp add: abc_Hoare_halt_def)
      apply(rule_tac x = 1 in exI, simp add: abc_steps_l.simps abc_step_l.simps abc_fetch.simps
          abc_comp.simps
          abc_lm_v.simps abc_lm_s.simps nth_append list_update_append list_update.simps(2))
      done
  next
    case (Suc y)
    have "length xs = n \<Longrightarrow> 
      {\<lambda>nl. nl = xs @ Suc x # y # anything} [Dec (Suc n) 2, Goto 0] {\<lambda>nl. nl = xs @ Suc x # 0 # anything}" by fact
    then obtain stp where 
      "abc_steps_l (0, xs @ Suc x # y # anything) [Dec (Suc n) 2, Goto 0] stp = (2, xs @ Suc x # 0 # anything)"
      using h
      apply(auto simp: abc_Hoare_halt_def numeral_2_eq_2)
      by (metis (mono_tags, lifting) abc_final.simps abc_holds_for.elims(2) length_Cons list.size(3))
    moreover have "abc_steps_l (0, xs @ Suc x # Suc y # anything) [Dec (Suc n) 2, Goto 0] 2 = 
                 (0, xs @ Suc x # y # anything)"
      using h
      by(simp add: abc_steps_l.simps numeral_2_eq_2 abc_step_l.simps abc_fetch.simps
          abc_lm_v.simps abc_lm_s.simps nth_append list_update_append list_update.simps(2))
    ultimately show "?case"
      apply(simp add: abc_Hoare_halt_def)
      by(rule exI[of _ "2 + stp"], simp only: abc_steps_add, simp)
  qed
qed

lemma adjust_paras: 
  "length xs = n \<Longrightarrow> {\<lambda>nl. nl = xs @ x # y # anything}  [Inc n, Dec (Suc n) 3, Goto (Suc 0)]
       {\<lambda>nl. nl = xs @ Suc x # 0 # anything}"
  using adjust_paras'[of xs n x y anything]
  by(simp add: abc_comp.simps abc_shift.simps numeral_2_eq_2 numeral_3_eq_3)

lemma rec_ci_SucSuc_n[simp]: "\<lbrakk>rec_ci g = (gap, gar, gft); \<forall>y<x. terminate g (xs @ [y, rec_exec (Pr n f g) (xs @ [y])]);
        length xs = n; Suc y\<le>x\<rbrakk> \<Longrightarrow> gar = Suc (Suc n)"
  by(auto dest:param_pattern elim!:allE[of _ y])

lemma loop_back':  
  assumes h: "length A = length gap + 4" "length xs = n"
    and le: "y \<ge> x"
  shows "\<exists> stp. abc_steps_l (length A, xs @ m # (y - x) # x # anything) (A @ [Dec (Suc (Suc n)) 0, Inc (Suc n), Goto (length gap + 4)]) stp
     = (length A, xs @ m # y # 0 # anything)"
  using le
proof(induct x)
  case 0
  thus "?case"
    using h
    by(rule_tac x = 0 in exI,
        auto simp: abc_steps_l.simps abc_step_l.simps abc_fetch.simps nth_append abc_lm_s.simps abc_lm_v.simps)
next
  case (Suc x)
  have "x \<le> y \<Longrightarrow> \<exists>stp. abc_steps_l (length A, xs @ m # (y - x) # x # anything) (A @ [Dec (Suc (Suc n)) 0, Inc (Suc n), Goto (length gap + 4)]) stp =
              (length A, xs @ m # y # 0 # anything)" by fact
  moreover have "Suc x \<le> y" by fact
  moreover then have "\<exists> stp. abc_steps_l (length A, xs @ m # (y - Suc x) # Suc x # anything) (A @ [Dec (Suc (Suc n)) 0, Inc (Suc n), Goto (length gap + 4)]) stp
                = (length A, xs @ m # (y - x) # x # anything)"
    using h
    apply(rule_tac x = 3 in exI)
    by(simp add: abc_steps_l.simps numeral_3_eq_3 abc_step_l.simps abc_fetch.simps nth_append
        abc_lm_v.simps abc_lm_s.simps list_update_append list_update.simps(2))
  ultimately show "?case"
    apply(auto simp add: abc_steps_add)
    by (metis abc_steps_add)
qed


lemma loop_back:  
  assumes h: "length A = length gap + 4" "length xs = n"
  shows "\<exists> stp. abc_steps_l (length A, xs @ m # 0 # x # anything) (A @ [Dec (Suc (Suc n)) 0, Inc (Suc n), Goto (length gap + 4)]) stp
     = (0, xs @ m # x # 0 # anything)"
  using loop_back'[of A gap xs n x x m anything] assms
  apply(auto) apply(rename_tac stp)
  apply(rule_tac x = "stp + 1" in exI)
  apply(simp only: abc_steps_add, simp)
  apply(simp add: abc_steps_l.simps abc_step_l.simps abc_fetch.simps nth_append abc_lm_v.simps
      abc_lm_s.simps)
  done

lemma rec_exec_pr_0_simps: "rec_exec (Pr n f g) (xs @ [0]) = rec_exec f xs"
  by(simp add: rec_exec.simps)

lemma rec_exec_pr_Suc_simps: "rec_exec (Pr n f g) (xs @ [Suc y])
          = rec_exec g (xs @ [y, rec_exec (Pr n f g) (xs @ [y])])"
  apply(induct y)
   apply(simp add: rec_exec.simps)
  apply(simp add: rec_exec.simps)
  done

lemma suc_max_simp[simp]: "Suc (max (n + 3) fft - Suc (Suc (Suc n))) = max (n + 3) fft - Suc (Suc n)"
  by arith

lemma pr_loop:
  assumes code: "code = ([Dec (max (n + 3) (max fft gft)) (length gap + 7)] [+] (gap [+] [Inc n, Dec (Suc n) 3, Goto (Suc 0)])) @
    [Dec (Suc (Suc n)) 0, Inc (Suc n), Goto (length gap + 4)]"
    and len: "length xs = n"
    and g_ind: "\<forall> y<x. (\<forall>anything. {\<lambda>nl. nl = xs @ y # rec_exec (Pr n f g) (xs @ [y]) # 0 \<up> (gft - gar) @ anything} gap
  {\<lambda>nl. nl = xs @ y # rec_exec (Pr n f g) (xs @ [y]) # rec_exec g (xs @ [y, rec_exec (Pr n f g) (xs @ [y])]) # 0 \<up> (gft - Suc gar) @ anything})"
    and compile_g: "rec_ci g = (gap, gar, gft)"
    and termi_g: "\<forall> y<x. terminate g (xs @ [y, rec_exec (Pr n f g) (xs @ [y])])"
    and ft: "ft = max (n + 3) (max fft gft)"
    and less: "Suc y \<le> x"
  shows 
    "\<exists>stp. abc_steps_l (0, xs @ (x - Suc y) # rec_exec (Pr n f g) (xs @ [x - Suc y]) # 0 \<up> (ft - Suc (Suc n)) @ Suc y # anything)
  code stp = (0, xs @ (x - y) # rec_exec (Pr n f g) (xs @ [x - y]) # 0 \<up> (ft - Suc (Suc n)) @ y # anything)"
proof -
  let ?A = "[Dec  ft (length gap + 7)]"
  let ?B = "gap"
  let ?C = "[Inc n, Dec (Suc n) 3, Goto (Suc 0)]"
  let ?D = "[Dec (Suc (Suc n)) 0, Inc (Suc n), Goto (length gap + 4)]"
  have "\<exists> stp. abc_steps_l (0, xs @ (x - Suc y) # rec_exec (Pr n f g) (xs @ [x - Suc y]) # 0 \<up> (ft - Suc (Suc n)) @ Suc y # anything)
            ((?A [+] (?B [+] ?C)) @ ?D) stp = (length (?A [+] (?B [+] ?C)), 
          xs @ (x - y) # 0 # rec_exec g (xs @ [x - Suc y, rec_exec (Pr n f g) (xs @ [x - Suc y])])
                  # 0 \<up> (ft - Suc (Suc (Suc n))) @ y # anything)"
  proof -
    have "\<exists> stp. abc_steps_l (0, xs @ (x - Suc y) # rec_exec (Pr n f g) (xs @ [x - Suc y]) # 0 \<up> (ft - Suc (Suc n)) @ Suc y # anything)
      ((?A [+] (?B [+] ?C))) stp = (length (?A [+] (?B [+] ?C)),  xs @ (x - y) # 0 # 
      rec_exec g (xs @ [x - Suc y, rec_exec (Pr n f g) (xs @ [x - Suc y])]) # 0 \<up> (ft - Suc (Suc (Suc n))) @ y # anything)"
    proof -
      have "{\<lambda> nl. nl = xs @ (x - Suc y) # rec_exec (Pr n f g) (xs @ [x - Suc y]) # 0 \<up> (ft - Suc (Suc n)) @ Suc y # anything}
        (?A [+] (?B [+] ?C)) 
        {\<lambda> nl. nl = xs @ (x - y) # 0 # 
        rec_exec g (xs @ [x - Suc y, rec_exec (Pr n f g) (xs @ [x - Suc y])]) # 0 \<up> (ft - Suc (Suc (Suc n))) @ y # anything}"
      proof(rule_tac abc_Hoare_plus_halt)
        show "{\<lambda>nl. nl = xs @ (x - Suc y) # rec_exec (Pr n f g) (xs @ [x - Suc y]) # 0 \<up> (ft - Suc (Suc n)) @ Suc y # anything}
          [Dec ft (length gap + 7)] 
          {\<lambda>nl. nl = xs @ (x - Suc y) # rec_exec (Pr n f g) (xs @ [x - Suc y]) # 0 \<up> (ft - Suc (Suc n)) @ y # anything}"
          using ft len
          by(simp)
      next
        show 
          "{\<lambda>nl. nl = xs @ (x - Suc y) # rec_exec (Pr n f g) (xs @ [x - Suc y]) # 0 \<up> (ft - Suc (Suc n)) @ y # anything} 
          ?B [+] ?C
          {\<lambda>nl. nl = xs @ (x - y) # 0 # rec_exec g (xs @ [x - Suc y, rec_exec (Pr n f g) (xs @ [x - Suc y])]) # 0 \<up> (ft - Suc (Suc (Suc n))) @ y # anything}"
        proof(rule_tac abc_Hoare_plus_halt)
          have a: "gar = Suc (Suc n)" 
            using compile_g termi_g len less
            by simp
          have b: "gft > gar"
            using compile_g
            by(erule_tac footprint_ge)
          show "{\<lambda>nl. nl = xs @ (x - Suc y) # rec_exec (Pr n f g) (xs @ [x - Suc y]) # 0 \<up> (ft - Suc (Suc n)) @ y # anything} gap 
                {\<lambda>nl. nl = xs @ (x - Suc y) # rec_exec (Pr n f g) (xs @ [x - Suc y]) # 
                      rec_exec g (xs @ [x - Suc y, rec_exec (Pr n f g) (xs @ [x - Suc y])]) # 0 \<up> (ft - Suc (Suc (Suc n))) @ y # anything}"
          proof -
            have 
              "{\<lambda>nl. nl = xs @ (x - Suc y) # rec_exec (Pr n f g) (xs @ [x - Suc y]) # 0 \<up> (gft - gar) @ 0\<up>(ft - gft) @ y # anything} gap
              {\<lambda>nl. nl = xs @ (x - Suc y) # rec_exec (Pr n f g) (xs @ [x - Suc y]) # 
              rec_exec g (xs @ [(x - Suc y), rec_exec (Pr n f g) (xs @ [x - Suc y])]) # 0 \<up> (gft - Suc gar) @ 0\<up>(ft - gft) @ y # anything}"
              using g_ind less by simp
            thus "?thesis"
              using a b ft
              by(simp add: replicate_merge_anywhere numeral_3_eq_3)
          qed
        next
          show "{\<lambda>nl. nl = xs @ (x - Suc y) #
                    rec_exec (Pr n f g) (xs @ [x - Suc y]) #
            rec_exec g (xs @ [x - Suc y, rec_exec (Pr n f g) (xs @ [x - Suc y])]) # 0 \<up> (ft - Suc (Suc (Suc n))) @ y # anything}
            [Inc n, Dec (Suc n) 3, Goto (Suc 0)]
            {\<lambda>nl. nl = xs @ (x - y) # 0 # rec_exec g (xs @ [x - Suc y, rec_exec (Pr n f g) 
                    (xs @ [x - Suc y])]) # 0 \<up> (ft - Suc (Suc (Suc n))) @ y # anything}"
            using len less
            using adjust_paras[of xs n "x - Suc y" " rec_exec (Pr n f g) (xs @ [x - Suc y])"
                " rec_exec g (xs @ [x - Suc y, rec_exec (Pr n f g) (xs @ [x - Suc y])]) # 
              0 \<up> (ft - Suc (Suc (Suc n))) @ y # anything"]
            by(simp add: Suc_diff_Suc)
        qed
      qed
      thus "?thesis"
        apply(simp add: abc_Hoare_halt_def, auto)
        apply(rename_tac na)
        apply(rule_tac x = na in exI, case_tac "abc_steps_l (0, xs @ (x - Suc y) # rec_exec (Pr n f g) (xs @ [x - Suc y]) # 
          0 \<up> (ft - Suc (Suc n)) @ Suc y # anything)
             ([Dec ft (length gap + 7)] [+] (gap [+] [Inc n, Dec (Suc n) 3, Goto (Suc 0)])) na", simp)
        done
    qed
    then obtain stpa where "abc_steps_l (0, xs @ (x - Suc y) # rec_exec (Pr n f g) (xs @ [x - Suc y]) # 0 \<up> (ft - Suc (Suc n)) @ Suc y # anything)
            ((?A [+] (?B [+] ?C))) stpa = (length (?A [+] (?B [+] ?C)), 
          xs @ (x - y) # 0 # rec_exec g (xs @ [x - Suc y, rec_exec (Pr n f g) (xs @ [x - Suc y])])
                  # 0 \<up> (ft - Suc (Suc (Suc n))) @ y # anything)" ..
    thus "?thesis"
      by(erule_tac abc_append_frist_steps_halt_eq)
  qed
  moreover have 
    "\<exists> stp. abc_steps_l (length (?A [+] (?B [+] ?C)),
    xs @ (x - y) # 0 # rec_exec g (xs @ [x - Suc y, rec_exec (Pr n f g) (xs @ [x - Suc y])]) # 0 \<up> (ft - Suc (Suc (Suc n))) @ y # anything)
    ((?A [+] (?B [+] ?C)) @ ?D) stp  = (0, xs @ (x - y) # rec_exec g (xs @ [x - Suc y, rec_exec (Pr n f g) (xs @ [x - Suc y])]) # 
    0 # 0 \<up> (ft - Suc (Suc (Suc n))) @ y # anything)"
    using len
    by(rule_tac loop_back, simp_all)
  moreover have "rec_exec g (xs @ [x - Suc y, rec_exec (Pr n f g) (xs @ [x - Suc y])]) = rec_exec (Pr n f g) (xs @ [x - y])"
    using less
    apply(cases "x - y", simp_all add: rec_exec_pr_Suc_simps)
    apply(rename_tac nat)
    by(subgoal_tac "nat = x - Suc y", simp, arith)    
  ultimately show "?thesis"
    using code ft 
    apply (auto simp add: abc_steps_add replicate_Suc_iff_anywhere)
    apply(rename_tac stp stpa)
    apply(rule_tac x = "stp + stpa" in exI)
    by (simp add: abc_steps_add replicate_Suc_iff_anywhere del: replicate_Suc)
qed

lemma abc_lm_s_simp0[simp]: 
  "length xs = n \<Longrightarrow> abc_lm_s (xs @ x # rec_exec (Pr n f g) (xs @ [x]) # 0 \<up> (max (n + 3) 
  (max fft gft) - Suc (Suc n)) @ 0 # anything) (max (n + 3) (max fft gft)) 0 =
    xs @ x # rec_exec (Pr n f g) (xs @ [x]) # 0 \<up> (max (n + 3) (max fft gft) - Suc n) @ anything"
  apply(simp add: abc_lm_s.simps)
  using list_update_length[of "xs @ x # rec_exec (Pr n f g) (xs @ [x]) # 0 \<up> (max (n + 3) (max fft gft) - Suc (Suc n))"
      0 anything 0]
  apply(auto simp: Suc_diff_Suc)
  apply(simp add: exp_suc[THEN sym] Suc_diff_Suc  del: replicate_Suc)
  done

lemma index_at_zero_elem[simp]:
  "(xs @ x # re # 0 \<up> (max (length xs + 3)
  (max fft gft) - Suc (Suc (length xs))) @ 0 # anything) !
    max (length xs + 3) (max fft gft) = 0"
  using nth_append_length[of "xs @ x # re #
  0 \<up> (max (length xs + 3) (max fft gft) - Suc (Suc (length xs)))" 0  anything]
  by(simp)

lemma pr_loop_correct:
  assumes less: "y \<le> x" 
    and len: "length xs = n"
    and compile_g: "rec_ci g = (gap, gar, gft)"
    and termi_g: "\<forall> y<x. terminate g (xs @ [y, rec_exec (Pr n f g) (xs @ [y])])"
    and g_ind: "\<forall> y<x. (\<forall>anything. {\<lambda>nl. nl = xs @ y # rec_exec (Pr n f g) (xs @ [y]) # 0 \<up> (gft - gar) @ anything} gap
  {\<lambda>nl. nl = xs @ y # rec_exec (Pr n f g) (xs @ [y]) # rec_exec g (xs @ [y, rec_exec (Pr n f g) (xs @ [y])]) # 0 \<up> (gft - Suc gar) @ anything})"
  shows "{\<lambda>nl. nl = xs @ (x - y) # rec_exec (Pr n f g) (xs @ [x - y]) # 0 \<up> (max (n + 3) (max fft gft) - Suc (Suc n)) @ y # anything}
   ([Dec (max (n + 3) (max fft gft)) (length gap + 7)] [+] (gap [+] [Inc n, Dec (Suc n) 3, Goto (Suc 0)])) @ [Dec (Suc (Suc n)) 0, Inc (Suc n), Goto (length gap + 4)]
   {\<lambda>nl. nl = xs @ x # rec_exec (Pr n f g) (xs @ [x]) # 0 \<up> (max (n + 3) (max fft gft) - Suc n) @ anything}" 
  using less
proof(induct y)
  case 0
  thus "?case"
    using len
    apply(simp add: abc_Hoare_halt_def)
    apply(rule_tac x = 1 in exI)
    by(auto simp: abc_steps_l.simps abc_step_l.simps abc_fetch.simps 
        nth_append abc_comp.simps abc_shift.simps, simp add: abc_lm_v.simps)
next
  case (Suc y)
  let ?ft = "max (n + 3) (max fft gft)"
  let ?C = "[Dec (max (n + 3) (max fft gft)) (length gap + 7)] [+] (gap [+] 
    [Inc n, Dec (Suc n) 3, Goto (Suc 0)]) @ [Dec (Suc (Suc n)) 0, Inc (Suc n), Goto (length gap + 4)]"
  have ind: "y \<le> x \<Longrightarrow>
         {\<lambda>nl. nl = xs @ (x - y) # rec_exec (Pr n f g) (xs @ [x - y]) # 0 \<up> (?ft - Suc (Suc n)) @ y # anything}
         ?C {\<lambda>nl. nl = xs @ x # rec_exec (Pr n f g) (xs @ [x]) # 0 \<up> (?ft - Suc n) @ anything}" by fact 
  have less: "Suc y \<le> x" by fact
  have stp1: 
    "\<exists> stp. abc_steps_l (0, xs @ (x - Suc y) # rec_exec (Pr n f g) (xs @ [x - Suc y]) # 0 \<up> (?ft - Suc (Suc n)) @ Suc y # anything)
    ?C stp  = (0, xs @ (x - y) # rec_exec (Pr n f g) (xs @ [x - y]) # 0 \<up> (?ft - Suc (Suc n)) @ y # anything)"
    using assms less
    by(rule_tac  pr_loop, auto)
  then obtain stp1 where a:
    "abc_steps_l (0, xs @ (x - Suc y) # rec_exec (Pr n f g) (xs @ [x - Suc y]) # 0 \<up> (?ft - Suc (Suc n)) @ Suc y # anything)
   ?C stp1 = (0, xs @ (x - y) # rec_exec (Pr n f g) (xs @ [x - y]) # 0 \<up> (?ft - Suc (Suc n)) @ y # anything)" ..
  moreover have 
    "\<exists> stp. abc_steps_l (0, xs @ (x - y) # rec_exec (Pr n f g) (xs @ [x - y]) # 0 \<up> (?ft - Suc (Suc n)) @ y # anything)
    ?C stp = (length ?C, xs @ x # rec_exec (Pr n f g) (xs @ [x]) # 0 \<up> (?ft - Suc n) @ anything)"
    using ind less
    apply(auto simp: abc_Hoare_halt_def)
    apply(rename_tac na,case_tac "abc_steps_l (0, xs @ (x - y) # rec_exec (Pr n f g) 
      (xs @ [x - y]) # 0 \<up> (?ft - Suc (Suc n)) @ y # anything) ?C na", rule_tac x = na in exI)
    by simp
  then obtain stp2 where b:
    "abc_steps_l (0, xs @ (x - y) # rec_exec (Pr n f g) (xs @ [x - y]) # 0 \<up> (?ft - Suc (Suc n)) @ y # anything)
    ?C stp2 = (length ?C, xs @ x # rec_exec (Pr n f g) (xs @ [x]) # 0 \<up> (?ft - Suc n) @ anything)" ..
  from a b show "?case"
    apply(simp add: abc_Hoare_halt_def)
    apply(rule_tac x = "stp1 + stp2" in exI, simp add: abc_steps_add).
qed

lemma compile_pr_correct':
  assumes termi_g: "\<forall> y<x. terminate g (xs @ [y, rec_exec (Pr n f g) (xs @ [y])])"
    and g_ind: 
    "\<forall> y<x. (\<forall>anything. {\<lambda>nl. nl = xs @ y # rec_exec (Pr n f g) (xs @ [y]) # 0 \<up> (gft - gar) @ anything} gap
  {\<lambda>nl. nl = xs @ y # rec_exec (Pr n f g) (xs @ [y]) # rec_exec g (xs @ [y, rec_exec (Pr n f g) (xs @ [y])]) # 0 \<up> (gft - Suc gar) @ anything})"
    and termi_f: "terminate f xs"
    and f_ind: "\<And> anything. {\<lambda>nl. nl = xs @ 0 \<up> (fft - far) @ anything} fap {\<lambda>nl. nl = xs @ rec_exec f xs # 0 \<up> (fft - Suc far) @ anything}"
    and len: "length xs = n"
    and compile1: "rec_ci f = (fap, far, fft)"
    and compile2: "rec_ci g = (gap, gar, gft)"
  shows 
    "{\<lambda>nl. nl = xs @ x # 0 \<up> (max (n + 3) (max fft gft) - n) @ anything}
  mv_box n (max (n + 3) (max fft gft)) [+]
  (fap [+] (mv_box n (Suc n) [+]
  ([Dec (max (n + 3) (max fft gft)) (length gap + 7)] [+] (gap [+] [Inc n, Dec (Suc n) 3, Goto (Suc 0)]) @
  [Dec (Suc (Suc n)) 0, Inc (Suc n), Goto (length gap + 4)])))
  {\<lambda>nl. nl = xs @ x # rec_exec (Pr n f g) (xs @ [x]) # 0 \<up> (max (n + 3) (max fft gft) - Suc n) @ anything}"
proof -
  let ?ft = "max (n+3) (max fft gft)"
  let ?A = "mv_box n ?ft"
  let ?B = "fap"
  let ?C = "mv_box n (Suc n)"
  let ?D = "[Dec ?ft (length gap + 7)]"
  let ?E = "gap [+] [Inc n, Dec (Suc n) 3, Goto (Suc 0)]"
  let ?F = "[Dec (Suc (Suc n)) 0, Inc (Suc n), Goto (length gap + 4)]"
  let ?P = "\<lambda>nl. nl = xs @ x # 0 \<up> (?ft - n) @ anything"
  let ?S = "\<lambda>nl. nl = xs @ x # rec_exec (Pr n f g) (xs @ [x]) # 0 \<up> (?ft - Suc n) @ anything"
  let ?Q1 = "\<lambda>nl. nl = xs @ 0 \<up> (?ft - n) @  x # anything"
  show "{?P} (?A [+] (?B [+] (?C [+] (?D [+] ?E @ ?F)))) {?S}"
  proof(rule_tac abc_Hoare_plus_halt)
    show "{?P} ?A {?Q1}"
      using len by simp
  next
    let ?Q2 = "\<lambda>nl. nl = xs @ rec_exec f xs # 0 \<up> (?ft - Suc n) @  x # anything"
    have a: "?ft \<ge> fft"
      by arith
    have b: "far = n"
      using compile1 termi_f len
      by(drule_tac param_pattern, auto)
    have c: "fft > far"
      using compile1
      by(simp add: footprint_ge)
    show "{?Q1} (?B [+] (?C [+] (?D [+] ?E @ ?F))) {?S}"
    proof(rule_tac abc_Hoare_plus_halt)
      have "{\<lambda>nl. nl = xs @ 0 \<up> (fft - far) @ 0\<up>(?ft - fft) @ x # anything} fap 
            {\<lambda>nl. nl = xs @ rec_exec f xs # 0 \<up> (fft - Suc far) @ 0\<up>(?ft - fft) @ x # anything}"
        by(rule_tac f_ind)
      moreover have "fft - far + ?ft - fft = ?ft - far"
        using a b c by arith
      moreover have "fft - Suc n + ?ft - fft = ?ft - Suc n"
        using a b c by arith
      ultimately show "{?Q1} ?B {?Q2}"
        using b
        by(simp add: replicate_merge_anywhere)
    next
      let ?Q3 = "\<lambda> nl. nl = xs @ 0 # rec_exec f xs # 0\<up>(?ft - Suc (Suc n)) @ x # anything"
      show "{?Q2} (?C [+] (?D [+] ?E @ ?F)) {?S}"
      proof(rule_tac abc_Hoare_plus_halt)
        show "{?Q2} (?C) {?Q3}"
          using mv_box_correct[of n "Suc n" "xs @ rec_exec f xs # 0 \<up> (max (n + 3) (max fft gft) - Suc n) @ x # anything"]
          using len
          by(auto)
      next
        show "{?Q3} (?D [+] ?E @ ?F) {?S}"
          using pr_loop_correct[of x x xs n g  gap gar gft f fft anything] assms
          by(simp add: rec_exec_pr_0_simps)
      qed
    qed
  qed
qed 

lemma compile_pr_correct:
  assumes g_ind: "\<forall>y<x. terminate g (xs @ [y, rec_exec (Pr n f g) (xs @ [y])]) \<and>
  (\<forall>x xa xb. rec_ci g = (x, xa, xb) \<longrightarrow>
  (\<forall>xc. {\<lambda>nl. nl = xs @ y # rec_exec (Pr n f g) (xs @ [y]) # 0 \<up> (xb - xa) @ xc} x
  {\<lambda>nl. nl = xs @ y # rec_exec (Pr n f g) (xs @ [y]) # rec_exec g (xs @ [y, rec_exec (Pr n f g) (xs @ [y])]) # 0 \<up> (xb - Suc xa) @ xc}))"
    and termi_f: "terminate f xs"
    and f_ind:
    "\<And>ap arity fp anything.
  rec_ci f = (ap, arity, fp) \<Longrightarrow> {\<lambda>nl. nl = xs @ 0 \<up> (fp - arity) @ anything} ap {\<lambda>nl. nl = xs @ rec_exec f xs # 0 \<up> (fp - Suc arity) @ anything}"
    and len: "length xs = n"
    and compile: "rec_ci (Pr n f g) = (ap, arity, fp)"
  shows "{\<lambda>nl. nl = xs @ x # 0 \<up> (fp - arity) @ anything} ap {\<lambda>nl. nl = xs @ x # rec_exec (Pr n f g) (xs @ [x]) # 0 \<up> (fp - Suc arity) @ anything}"
proof(cases "rec_ci f", cases "rec_ci g")
  fix fap far fft gap gar gft
  assume h: "rec_ci f = (fap, far, fft)" "rec_ci g = (gap, gar, gft)"
  have g: 
    "\<forall>y<x. (terminate g (xs @ [y, rec_exec (Pr n f g) (xs @ [y])]) \<and>
     (\<forall>anything. {\<lambda>nl. nl = xs @ y # rec_exec (Pr n f g) (xs @ [y]) # 0 \<up> (gft - gar) @ anything} gap
    {\<lambda>nl. nl = xs @ y # rec_exec (Pr n f g) (xs @ [y]) # rec_exec g (xs @ [y, rec_exec (Pr n f g) (xs @ [y])]) # 0 \<up> (gft - Suc gar) @ anything}))"
    using g_ind h
    by(auto)
  hence termi_g: "\<forall> y<x. terminate g (xs @ [y, rec_exec (Pr n f g) (xs @ [y])])"
    by simp
  from g have g_newind: 
    "\<forall> y<x. (\<forall>anything. {\<lambda>nl. nl = xs @ y # rec_exec (Pr n f g) (xs @ [y]) # 0 \<up> (gft - gar) @ anything} gap
    {\<lambda>nl. nl = xs @ y # rec_exec (Pr n f g) (xs @ [y]) # rec_exec g (xs @ [y, rec_exec (Pr n f g) (xs @ [y])]) # 0 \<up> (gft - Suc gar) @ anything})"
    by auto
  have f_newind: "\<And> anything. {\<lambda>nl. nl = xs @ 0 \<up> (fft - far) @ anything} fap {\<lambda>nl. nl = xs @ rec_exec f xs # 0 \<up> (fft - Suc far) @ anything}"
    using h
    by(rule_tac f_ind, simp)
  show "?thesis"
    using termi_f termi_g h compile
    apply(simp add: rec_ci.simps abc_comp_commute, auto)
    using g_newind f_newind len
    by(rule_tac compile_pr_correct', simp_all)
qed

fun mn_ind_inv ::
  "nat \<times> nat list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> bool"
  where
    "mn_ind_inv (as, lm') ss x rsx suf_lm lm = 
           (if as = ss then lm' = lm @ x # rsx # suf_lm
            else if as = ss + 1 then 
                 \<exists>y. (lm' = lm @ x # y # suf_lm) \<and> y \<le> rsx
            else if as = ss + 2 then 
                 \<exists>y. (lm' = lm @ x # y # suf_lm) \<and> y \<le> rsx
            else if as = ss + 3 then lm' = lm @ x # 0 # suf_lm
            else if as = ss + 4 then lm' = lm @ Suc x # 0 # suf_lm
            else if as = 0 then lm' = lm @ Suc x # 0 # suf_lm
            else False
)"

fun mn_stage1 :: "nat \<times> nat list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat"
  where
    "mn_stage1 (as, lm) ss n = 
            (if as = 0 then 0 
             else if as = ss + 4 then 1
             else if as = ss + 3 then 2
             else if as = ss + 2 \<or> as = ss + 1 then 3
             else if as = ss then 4
             else 0
)"

fun mn_stage2 :: "nat \<times> nat list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat"
  where
    "mn_stage2 (as, lm) ss n = 
            (if as = ss + 1 \<or> as = ss + 2 then (lm ! (Suc n))
             else 0)"

fun mn_stage3 :: "nat \<times> nat list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat"
  where
    "mn_stage3 (as, lm) ss n = (if as = ss + 2 then 1 else 0)"


fun mn_measure :: "((nat \<times> nat list) \<times> nat \<times> nat) \<Rightarrow>
                                                (nat \<times> nat \<times> nat)"
  where
    "mn_measure ((as, lm), ss, n) = 
     (mn_stage1 (as, lm) ss n, mn_stage2 (as, lm) ss n,
                                       mn_stage3 (as, lm) ss n)"

definition mn_LE :: "(((nat \<times> nat list) \<times> nat \<times> nat) \<times>
                     ((nat \<times> nat list) \<times> nat \<times> nat)) set"
  where "mn_LE \<equiv> (inv_image lex_triple mn_measure)"

lemma wf_mn_le[intro]: "wf mn_LE"
  by(auto intro:wf_inv_image wf_lex_triple simp: mn_LE_def)

declare mn_ind_inv.simps[simp del]

lemma put_in_tape_small_enough0[simp]: 
  "0 < rsx \<Longrightarrow> 
 \<exists>y. (xs @ x # rsx # anything)[Suc (length xs) := rsx - Suc 0] = xs @ x # y # anything \<and> y \<le> rsx"
  apply(rule_tac x = "rsx - 1" in exI)
  apply(simp add: list_update_append list_update.simps)
  done

lemma put_in_tape_small_enough1[simp]: 
  "\<lbrakk>y \<le> rsx; 0 < y\<rbrakk>
            \<Longrightarrow> \<exists>ya. (xs @ x # y # anything)[Suc (length xs) := y - Suc 0] = xs @ x # ya # anything \<and> ya \<le> rsx"
  apply(rule_tac x = "y - 1" in exI)
  apply(simp add: list_update_append list_update.simps)
  done

lemma abc_comp_null[simp]: "(A [+] B = []) = (A = [] \<and> B = [])"
  by(auto simp: abc_comp.simps abc_shift.simps)

lemma rec_ci_not_null[simp]: "(rec_ci f \<noteq> ([], a, b))"
proof(cases f)
  case (Cn x41 x42 x43)
  then show ?thesis
    by(cases "rec_ci x42", auto simp: mv_box.simps rec_ci.simps rec_ci_id.simps)
next
  case (Pr x51 x52 x53)
  then show ?thesis 
    apply(cases "rec_ci x52", cases "rec_ci x53")
    by (auto simp: mv_box.simps rec_ci.simps rec_ci_id.simps)
next
  case (Mn x61 x62)
  then show ?thesis 
    by(cases "rec_ci x62") (auto simp: rec_ci.simps rec_ci_id.simps)
qed (auto simp: rec_ci_z_def rec_ci_s_def rec_ci.simps addition.simps rec_ci_id.simps)


lemma mn_correct:
  assumes compile: "rec_ci rf = (fap, far, fft)"
    and ge: "0 < rsx"
    and len: "length xs = arity"
    and B: "B = [Dec (Suc arity) (length fap + 5), Dec (Suc arity) (length fap + 3), Goto (Suc (length fap)), Inc arity, Goto 0]"
    and f: "f = (\<lambda> stp. (abc_steps_l (length fap, xs @ x # rsx # anything) (fap @ B) stp, (length fap), arity)) "
    and P: "P =(\<lambda> ((as, lm), ss, arity). as = 0)"
    and Q: "Q = (\<lambda> ((as, lm), ss, arity). mn_ind_inv (as, lm) (length fap) x rsx anything xs)"
  shows "\<exists> stp. P (f stp) \<and> Q (f stp)"
proof(rule_tac halt_lemma2)
  show "wf mn_LE"
    using wf_mn_le by simp
next
  show "Q (f 0)"
    by(auto simp: Q f abc_steps_l.simps mn_ind_inv.simps)
next
  have "fap \<noteq> []"
    using compile by auto
  thus "\<not> P (f 0)"
    by(auto simp: f P abc_steps_l.simps)
next
  have "fap \<noteq> []"
    using compile by auto
  then have "\<lbrakk>\<not> P (f stp); Q (f stp)\<rbrakk> \<Longrightarrow> Q (f (Suc stp)) \<and> (f (Suc stp), f stp) \<in> mn_LE" for stp
    using ge len
    apply(cases "(abc_steps_l (length fap, xs @ x # rsx # anything) (fap @ B) stp)")
    apply(simp add: abc_step_red2  B f P Q)
    apply(auto split:if_splits simp add:abc_steps_l.simps  mn_ind_inv.simps abc_steps_zero B abc_fetch.simps nth_append)
    by(auto simp: mn_LE_def lex_triple_def lex_pair_def 
        abc_step_l.simps abc_steps_l.simps mn_ind_inv.simps
        abc_lm_v.simps abc_lm_s.simps nth_append abc_fetch.simps
        split: if_splits)    
  thus "\<forall>stp. \<not> P (f stp) \<and> Q (f stp) \<longrightarrow> Q (f (Suc stp)) \<and> (f (Suc stp), f stp) \<in> mn_LE"
    by(auto)
qed

lemma abc_Hoare_haltE:
  "{\<lambda> nl. nl = lm1} p {\<lambda> nl. nl = lm2}
    \<Longrightarrow> \<exists> stp. abc_steps_l (0, lm1) p stp = (length p, lm2)"
  by(auto simp:abc_Hoare_halt_def elim!: abc_holds_for.elims)

lemma mn_loop:
  assumes B:  "B = [Dec (Suc arity) (length fap + 5), Dec (Suc arity) (length fap + 3), Goto (Suc (length fap)), Inc arity, Goto 0]"
    and ft: "ft = max (Suc arity) fft"
    and len: "length xs = arity"
    and far: "far = Suc arity"
    and ind: " (\<forall>xc. ({\<lambda>nl. nl = xs @ x # 0 \<up> (fft - far) @ xc} fap
    {\<lambda>nl. nl = xs @ x # rec_exec f (xs @ [x]) # 0 \<up> (fft - Suc far) @ xc}))"
    and exec_less: "rec_exec f (xs @ [x]) > 0"
    and compile: "rec_ci f = (fap, far, fft)"
  shows "\<exists> stp > 0. abc_steps_l (0, xs @ x # 0 \<up> (ft - Suc arity) @ anything) (fap @ B) stp =
    (0, xs @ Suc x # 0 \<up> (ft - Suc arity) @ anything)"
proof -
  have "\<exists> stp. abc_steps_l (0, xs @ x # 0 \<up> (ft - Suc arity) @ anything) (fap @ B) stp =
    (length fap, xs @ x # rec_exec f (xs @ [x]) # 0 \<up> (ft - Suc (Suc arity)) @ anything)"
  proof -
    have "\<exists> stp. abc_steps_l (0, xs @ x # 0 \<up> (ft - Suc arity) @ anything) fap stp =
      (length fap, xs @ x # rec_exec f (xs @ [x]) # 0 \<up> (ft - Suc (Suc arity)) @ anything)"
    proof -
      have "{\<lambda>nl. nl = xs @ x # 0 \<up> (fft - far) @ 0\<up>(ft - fft) @ anything} fap 
            {\<lambda>nl. nl = xs @ x # rec_exec f (xs @ [x]) # 0 \<up> (fft - Suc far) @ 0\<up>(ft - fft) @ anything}"
        using ind by simp
      moreover have "fft > far"
        using compile
        by(erule_tac footprint_ge)
      ultimately show "?thesis"
        using ft far
        apply(drule_tac abc_Hoare_haltE)
        by(simp add: replicate_merge_anywhere max_absorb2)
    qed
    then obtain stp where "abc_steps_l (0, xs @ x # 0 \<up> (ft - Suc arity) @ anything) fap stp =
      (length fap, xs @ x # rec_exec f (xs @ [x]) # 0 \<up> (ft - Suc (Suc arity)) @ anything)" ..
    thus "?thesis"
      by(erule_tac abc_append_frist_steps_halt_eq)
  qed
  moreover have 
    "\<exists> stp > 0. abc_steps_l (length fap, xs @ x # rec_exec f (xs @ [x]) # 0 \<up> (ft - Suc (Suc arity)) @ anything) (fap @ B) stp =
    (0, xs @ Suc x # 0 # 0 \<up> (ft - Suc (Suc arity)) @ anything)"
    using mn_correct[of f fap far fft "rec_exec f (xs @ [x])" xs arity B
        "(\<lambda>stp. (abc_steps_l (length fap, xs @ x # rec_exec f (xs @ [x]) # 0 \<up> (ft - Suc (Suc arity)) @ anything) (fap @ B) stp, length fap, arity))"     
        x "0 \<up> (ft - Suc (Suc arity)) @ anything" "(\<lambda>((as, lm), ss, arity). as = 0)" 
        "(\<lambda>((as, lm), ss, aritya). mn_ind_inv (as, lm) (length fap) x (rec_exec f (xs @ [x])) (0 \<up> (ft - Suc (Suc arity)) @ anything) xs) "]  
      B compile  exec_less len
    apply(subgoal_tac "fap \<noteq> []", auto)
    apply(rename_tac stp y)
    apply(rule_tac x = stp in exI, auto simp: mn_ind_inv.simps)
    by(case_tac "stp", simp_all add: abc_steps_l.simps)
  moreover have "fft > far"
    using compile
    by(erule_tac footprint_ge)
  ultimately show "?thesis"
    using ft far
    apply(auto) apply(rename_tac stp1 stp2)
    by(rule_tac x = "stp1 + stp2" in exI, 
        simp add: abc_steps_add replicate_Suc[THEN sym] diff_Suc_Suc del: replicate_Suc)
qed

lemma mn_loop_correct': 
  assumes B:  "B = [Dec (Suc arity) (length fap + 5), Dec (Suc arity) (length fap + 3), Goto (Suc (length fap)), Inc arity, Goto 0]"
    and ft: "ft = max (Suc arity) fft"
    and len: "length xs = arity"
    and ind_all: "\<forall>i\<le>x. (\<forall>xc. ({\<lambda>nl. nl = xs @ i # 0 \<up> (fft - far) @ xc} fap
    {\<lambda>nl. nl = xs @ i # rec_exec f (xs @ [i]) # 0 \<up> (fft - Suc far) @ xc}))"
    and exec_ge: "\<forall> i\<le>x. rec_exec f (xs @ [i]) > 0"
    and compile: "rec_ci f = (fap, far, fft)"
    and far: "far = Suc arity"
  shows "\<exists> stp > x. abc_steps_l (0, xs @ 0 # 0 \<up> (ft - Suc arity) @ anything) (fap @ B) stp = 
               (0, xs @ Suc x # 0 \<up> (ft - Suc arity) @ anything)"
  using ind_all exec_ge
proof(induct x)
  case 0
  thus "?case"
    using assms
    by(rule_tac mn_loop, simp_all)
next
  case (Suc x)
  have ind': "\<lbrakk>\<forall>i\<le>x. \<forall>xc. {\<lambda>nl. nl = xs @ i # 0 \<up> (fft - far) @ xc} fap {\<lambda>nl. nl = xs @ i # rec_exec f (xs @ [i]) # 0 \<up> (fft - Suc far) @ xc};
               \<forall>i\<le>x. 0 < rec_exec f (xs @ [i])\<rbrakk> \<Longrightarrow> 
            \<exists>stp > x. abc_steps_l (0, xs @ 0 # 0 \<up> (ft - Suc arity) @ anything) (fap @ B) stp = (0, xs @ Suc x # 0 \<up> (ft - Suc arity) @ anything)" by fact
  have exec_ge: "\<forall>i\<le>Suc x. 0 < rec_exec f (xs @ [i])" by fact
  have ind_all: "\<forall>i\<le>Suc x. \<forall>xc. {\<lambda>nl. nl = xs @ i # 0 \<up> (fft - far) @ xc} fap 
    {\<lambda>nl. nl = xs @ i # rec_exec f (xs @ [i]) # 0 \<up> (fft - Suc far) @ xc}" by fact
  have ind: "\<exists>stp > x. abc_steps_l (0, xs @ 0 # 0 \<up> (ft - Suc arity) @ anything) (fap @ B) stp =
    (0, xs @ Suc x # 0 \<up> (ft - Suc arity) @ anything)" using ind' exec_ge ind_all by simp
  have stp: "\<exists> stp > 0. abc_steps_l (0, xs @ Suc x # 0 \<up> (ft - Suc arity) @ anything) (fap @ B) stp =
    (0, xs @ Suc (Suc x) # 0 \<up> (ft - Suc arity) @ anything)"
    using ind_all exec_ge B ft len far compile
    by(rule_tac mn_loop, simp_all)
  from ind stp show "?case"
    apply(auto simp add: abc_steps_add)
    apply(rename_tac stp1 stp2)
    by(rule_tac x = "stp1 + stp2" in exI, simp add: abc_steps_add)
qed

lemma mn_loop_correct: 
  assumes B:  "B = [Dec (Suc arity) (length fap + 5), Dec (Suc arity) (length fap + 3), Goto (Suc (length fap)), Inc arity, Goto 0]"
    and ft: "ft = max (Suc arity) fft"
    and len: "length xs = arity"
    and ind_all: "\<forall>i\<le>x. (\<forall>xc. ({\<lambda>nl. nl = xs @ i # 0 \<up> (fft - far) @ xc} fap
    {\<lambda>nl. nl = xs @ i # rec_exec f (xs @ [i]) # 0 \<up> (fft - Suc far) @ xc}))"
    and exec_ge: "\<forall> i\<le>x. rec_exec f (xs @ [i]) > 0"
    and compile: "rec_ci f = (fap, far, fft)"
    and far: "far = Suc arity"
  shows "\<exists> stp. abc_steps_l (0, xs @ 0 # 0 \<up> (ft - Suc arity) @ anything) (fap @ B) stp = 
               (0, xs @ Suc x # 0 \<up> (ft - Suc arity) @ anything)"
proof -
  have "\<exists>stp>x. abc_steps_l (0, xs @ 0 # 0 \<up> (ft - Suc arity) @ anything) (fap @ B) stp = (0, xs @ Suc x # 0 \<up> (ft - Suc arity) @ anything)"
    using assms
    by(rule_tac mn_loop_correct', simp_all)
  thus "?thesis"
    by(auto)
qed

lemma compile_mn_correct': 
  assumes B:  "B = [Dec (Suc arity) (length fap + 5), Dec (Suc arity) (length fap + 3), Goto (Suc (length fap)), Inc arity, Goto 0]"
    and ft: "ft = max (Suc arity) fft"
    and len: "length xs = arity"
    and termi_f: "terminate f (xs @ [r])"
    and f_ind: "\<And>anything. {\<lambda>nl. nl = xs @ r # 0 \<up> (fft - far) @ anything} fap 
        {\<lambda>nl. nl = xs @ r # 0 # 0 \<up> (fft - Suc far) @ anything}"
    and ind_all: "\<forall>i < r. (\<forall>xc. ({\<lambda>nl. nl = xs @ i # 0 \<up> (fft - far) @ xc} fap
    {\<lambda>nl. nl = xs @ i # rec_exec f (xs @ [i]) # 0 \<up> (fft - Suc far) @ xc}))"
    and exec_less: "\<forall> i<r. rec_exec f (xs @ [i]) > 0"
    and exec: "rec_exec f (xs @ [r]) = 0"
    and compile: "rec_ci f = (fap, far, fft)"
  shows "{\<lambda>nl. nl = xs @ 0 \<up> (max (Suc arity) fft - arity) @ anything}
    fap @ B
    {\<lambda>nl. nl = xs @ rec_exec (Mn arity f) xs # 0 \<up> (max (Suc arity) fft - Suc arity) @ anything}"
proof -
  have a: "far = Suc arity"
    using len compile termi_f
    by(drule_tac param_pattern, auto)
  have b: "fft > far"
    using compile
    by(erule_tac footprint_ge)
  have "\<exists> stp. abc_steps_l (0, xs @ 0 # 0 \<up> (ft - Suc arity) @ anything) (fap @ B) stp = 
    (0, xs @ r # 0 \<up> (ft - Suc arity) @ anything)"
    using assms a
    apply(cases r, rule_tac x = 0 in exI, simp add: abc_steps_l.simps, simp)
    by(rule_tac mn_loop_correct, auto)  
  moreover have 
    "\<exists> stp. abc_steps_l (0, xs @ r # 0 \<up> (ft - Suc arity) @ anything) (fap @ B) stp = 
    (length fap, xs @ r # rec_exec f (xs @ [r]) # 0 \<up> (ft - Suc (Suc arity)) @ anything)"
  proof -
    have "\<exists> stp. abc_steps_l (0, xs @ r # 0 \<up> (ft - Suc arity) @ anything) fap stp =
      (length fap, xs @ r # rec_exec f (xs @ [r]) # 0 \<up> (ft - Suc (Suc arity)) @ anything)"
    proof -
      have "{\<lambda>nl. nl = xs @ r # 0 \<up> (fft - far) @ 0\<up>(ft - fft) @ anything} fap 
            {\<lambda>nl. nl = xs @ r # rec_exec f (xs @ [r]) # 0 \<up> (fft - Suc far) @ 0\<up>(ft - fft) @ anything}"
        using f_ind exec by simp
      thus "?thesis"
        using ft a b
        apply(drule_tac abc_Hoare_haltE)
        by(simp add: replicate_merge_anywhere max_absorb2)
    qed
    then obtain stp where "abc_steps_l (0, xs @ r # 0 \<up> (ft - Suc arity) @ anything) fap stp =
      (length fap, xs @ r # rec_exec f (xs @ [r]) # 0 \<up> (ft - Suc (Suc arity)) @ anything)" ..
    thus "?thesis"
      by(erule_tac abc_append_frist_steps_halt_eq)
  qed
  moreover have 
    "\<exists> stp. abc_steps_l (length fap, xs @ r # rec_exec f (xs @ [r]) # 0 \<up> (ft - Suc (Suc arity)) @ anything) (fap @ B) stp = 
             (length fap + 5, xs @ r # rec_exec f (xs @ [r]) # 0 \<up> (ft - Suc (Suc arity)) @ anything)"
    using ft a b len B exec
    apply(rule_tac x = 1 in exI, auto)
    by(auto simp: abc_steps_l.simps B abc_step_l.simps 
        abc_fetch.simps nth_append max_absorb2 abc_lm_v.simps abc_lm_s.simps)
  moreover have "rec_exec (Mn (length xs) f) xs = r"
    using exec exec_less
    apply(auto simp: rec_exec.simps Least_def)
    thm the_equality
    apply(rule_tac the_equality, auto)
     apply(metis exec_less less_not_refl3 linorder_not_less)
    by (metis le_neq_implies_less less_not_refl3)
  ultimately show "?thesis"
    using ft a b len B exec
    apply(auto simp: abc_Hoare_halt_def)
    apply(rename_tac stp1 stp2 stp3)
    apply(rule_tac x = "stp1 + stp2 + stp3"  in exI)
    by(simp add: abc_steps_add replicate_Suc_iff_anywhere max_absorb2 Suc_diff_Suc del: replicate_Suc)
qed

lemma compile_mn_correct:
  assumes len: "length xs = n"
    and termi_f: "terminate f (xs @ [r])"
    and f_ind: "\<And>ap arity fp anything. rec_ci f = (ap, arity, fp) \<Longrightarrow> 
  {\<lambda>nl. nl = xs @ r # 0 \<up> (fp - arity) @ anything} ap {\<lambda>nl. nl = xs @ r # 0 # 0 \<up> (fp - Suc arity) @ anything}"
    and exec: "rec_exec f (xs @ [r]) = 0"
    and ind_all: 
    "\<forall>i<r. terminate f (xs @ [i]) \<and>
  (\<forall>x xa xb. rec_ci f = (x, xa, xb) \<longrightarrow> 
  (\<forall>xc. {\<lambda>nl. nl = xs @ i # 0 \<up> (xb - xa) @ xc} x {\<lambda>nl. nl = xs @ i # rec_exec f (xs @ [i]) # 0 \<up> (xb - Suc xa) @ xc})) \<and>
  0 < rec_exec f (xs @ [i])"
    and compile: "rec_ci (Mn n f) = (ap, arity, fp)"
  shows "{\<lambda>nl. nl = xs @ 0 \<up> (fp - arity) @ anything} ap 
  {\<lambda>nl. nl = xs @ rec_exec (Mn n f) xs # 0 \<up> (fp - Suc arity) @ anything}"
proof(cases "rec_ci f")
  fix fap far fft
  assume h: "rec_ci f = (fap, far, fft)"
  hence f_newind: 
    "\<And>anything. {\<lambda>nl. nl = xs @ r # 0 \<up> (fft - far) @ anything} fap 
        {\<lambda>nl. nl = xs @ r # 0 # 0 \<up> (fft - Suc far) @ anything}"
    by(rule_tac f_ind, simp)
  have newind_all: 
    "\<forall>i < r. (\<forall>xc. ({\<lambda>nl. nl = xs @ i # 0 \<up> (fft - far) @ xc} fap
    {\<lambda>nl. nl = xs @ i # rec_exec f (xs @ [i]) # 0 \<up> (fft - Suc far) @ xc}))"
    using ind_all h
    by(auto)
  have all_less: "\<forall> i<r. rec_exec f (xs @ [i]) > 0"
    using ind_all by auto
  show "?thesis"
    using h compile f_newind newind_all all_less len termi_f exec
    apply(auto simp: rec_ci.simps)
    by(rule_tac compile_mn_correct', auto)
qed

lemma recursive_compile_correct:
  "\<lbrakk>terminate recf args; rec_ci recf = (ap, arity, fp)\<rbrakk>
  \<Longrightarrow> {\<lambda> nl. nl = args @ 0\<up>(fp - arity) @ anything} ap 
         {\<lambda> nl. nl = args@ rec_exec recf args # 0\<up>(fp - Suc arity) @ anything}"
  apply(induct arbitrary: ap arity fp anything rule: terminate.induct)
       apply(simp_all add: compile_s_correct compile_z_correct compile_id_correct 
      compile_cn_correct compile_pr_correct compile_mn_correct)
  done

definition dummy_abc :: "nat \<Rightarrow> abc_inst list"
  where
    "dummy_abc k = [Inc k, Dec k 0, Goto 3]"

definition abc_list_crsp:: "nat list \<Rightarrow> nat list \<Rightarrow> bool"
  where
    "abc_list_crsp xs ys = (\<exists> n. xs = ys @ 0\<up>n \<or> ys = xs @ 0\<up>n)"

lemma abc_list_crsp_simp1[intro]: "abc_list_crsp (lm @ 0\<up>m) lm"
  by(auto simp: abc_list_crsp_def)


lemma abc_list_crsp_lm_v: 
  "abc_list_crsp lma lmb \<Longrightarrow> abc_lm_v lma n = abc_lm_v lmb n"
  by(auto simp: abc_list_crsp_def abc_lm_v.simps 
      nth_append)


lemma abc_list_crsp_elim: 
  "\<lbrakk>abc_list_crsp lma lmb; \<exists> n. lma = lmb @ 0\<up>n \<or> lmb = lma @ 0\<up>n \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by(auto simp: abc_list_crsp_def)

lemma abc_list_crsp_simp[simp]: 
  "\<lbrakk>abc_list_crsp lma lmb; m < length lma; m < length lmb\<rbrakk> \<Longrightarrow>
          abc_list_crsp (lma[m := n]) (lmb[m := n])"
  by(auto simp: abc_list_crsp_def list_update_append)

lemma abc_list_crsp_simp2[simp]: 
  "\<lbrakk>abc_list_crsp lma lmb; m < length lma; \<not> m < length lmb\<rbrakk> \<Longrightarrow> 
  abc_list_crsp (lma[m := n]) (lmb @ 0 \<up> (m - length lmb) @ [n])"
  apply(auto simp: abc_list_crsp_def list_update_append)
  apply(rename_tac N)
  apply(rule_tac x = "N + length lmb - Suc m" in exI)
  apply(rule_tac disjI1)
  apply(simp add: upd_conv_take_nth_drop min_absorb1)
  done

lemma abc_list_crsp_simp3[simp]:
  "\<lbrakk>abc_list_crsp lma lmb; \<not> m < length lma; m < length lmb\<rbrakk> \<Longrightarrow> 
  abc_list_crsp (lma @ 0 \<up> (m - length lma) @ [n]) (lmb[m := n])"
  apply(auto simp: abc_list_crsp_def list_update_append)
  apply(rename_tac N)
  apply(rule_tac x = "N + length lma - Suc m" in exI)
  apply(rule_tac disjI2)
  apply(simp add: upd_conv_take_nth_drop min_absorb1)
  done

lemma abc_list_crsp_simp4[simp]: "\<lbrakk>abc_list_crsp lma lmb; \<not> m < length lma; \<not> m < length lmb\<rbrakk> \<Longrightarrow> 
  abc_list_crsp (lma @ 0 \<up> (m - length lma) @ [n]) (lmb @ 0 \<up> (m - length lmb) @ [n])"
  by(auto simp: abc_list_crsp_def list_update_append replicate_merge_anywhere)

lemma abc_list_crsp_lm_s: 
  "abc_list_crsp lma lmb \<Longrightarrow> 
      abc_list_crsp (abc_lm_s lma m n) (abc_lm_s lmb m n)"
  by(auto simp: abc_lm_s.simps)

lemma abc_list_crsp_step: 
  "\<lbrakk>abc_list_crsp lma lmb; abc_step_l (aa, lma) i = (a, lma'); 
    abc_step_l (aa, lmb) i = (a', lmb')\<rbrakk>
    \<Longrightarrow> a' = a \<and> abc_list_crsp lma' lmb'"
  apply(cases i, auto simp: abc_step_l.simps 
      abc_list_crsp_lm_s abc_list_crsp_lm_v 
      split: abc_inst.splits if_splits)
  done

lemma abc_list_crsp_steps: 
  "\<lbrakk>abc_steps_l (0, lm @ 0\<up>m) aprog stp = (a, lm'); aprog \<noteq> []\<rbrakk> 
      \<Longrightarrow> \<exists> lma. abc_steps_l (0, lm) aprog stp = (a, lma) \<and> 
                                          abc_list_crsp lm' lma"
proof(induct stp arbitrary: a lm')
  case (Suc stp)
  then show ?case apply(cases "abc_steps_l (0, lm @ 0\<up>m) aprog stp", simp add: abc_step_red)
  proof -
    fix stp a lm' aa b
    assume ind:
      "\<And>a lm'. aa = a \<and> b = lm' \<Longrightarrow> 
     \<exists>lma. abc_steps_l (0, lm) aprog stp = (a, lma) \<and>
                                          abc_list_crsp lm' lma"
      and h: "abc_step_l (aa, b) (abc_fetch aa aprog) = (a, lm')" 
      "abc_steps_l (0, lm @ 0\<up>m) aprog stp = (aa, b)" 
      "aprog \<noteq> []"
    have "\<exists>lma. abc_steps_l (0, lm) aprog stp = (aa, lma) \<and> 
              abc_list_crsp b lma"
      apply(rule_tac ind, simp)
      done
    from this obtain lma where g2: 
      "abc_steps_l (0, lm) aprog stp = (aa, lma) \<and> 
     abc_list_crsp b lma"   ..
    hence g3: "abc_steps_l (0, lm) aprog (Suc stp)
          = abc_step_l (aa, lma) (abc_fetch aa aprog)"
      apply(rule_tac abc_step_red, simp)
      done
    show "\<exists>lma. abc_steps_l (0, lm) aprog (Suc stp) = (a, lma) \<and> abc_list_crsp lm' lma"
      using g2 g3 h
      apply(auto)
      apply(cases "abc_step_l (aa, b) (abc_fetch aa aprog)",
          cases "abc_step_l (aa, lma) (abc_fetch aa aprog)", simp)
      apply(rule_tac abc_list_crsp_step, auto)
      done
  qed
qed (force simp add: abc_steps_l.simps)

lemma list_crsp_simp2: "abc_list_crsp (lm1 @ 0\<up>n) lm2 \<Longrightarrow> abc_list_crsp lm1 lm2"
proof(induct n)
  case 0
  thus "?case"
    by(auto simp: abc_list_crsp_def)
next
  case (Suc n)
  have ind: "abc_list_crsp (lm1 @ 0 \<up> n) lm2 \<Longrightarrow> abc_list_crsp lm1 lm2" by fact
  have h: "abc_list_crsp (lm1 @ 0 \<up> Suc n) lm2" by fact
  then have "abc_list_crsp (lm1 @ 0 \<up> n) lm2"
    apply(auto simp only: exp_suc abc_list_crsp_def del: replicate_Suc)
     apply (metis Suc_pred append_eq_append_conv
        append_eq_append_conv2 butlast_append butlast_snoc length_replicate list.distinct(1)
        neq0_conv replicate_Suc replicate_Suc_iff_anywhere replicate_app_Cons_same 
        replicate_empty self_append_conv self_append_conv2)
    apply (auto,metis replicate_Suc)
    .
  thus "?case"
    using ind
    by auto
qed

lemma recursive_compile_correct_norm': 
  "\<lbrakk>rec_ci f = (ap, arity, ft);  
    terminate f args\<rbrakk>
  \<Longrightarrow> \<exists> stp rl. (abc_steps_l (0, args) ap stp) = (length ap, rl) \<and> abc_list_crsp (args @ [rec_exec f args]) rl"
  using recursive_compile_correct[of f args ap arity ft "[]"]
  apply(auto simp: abc_Hoare_halt_def)
  apply(rename_tac n)
  apply(rule_tac x = n in exI)
  apply(case_tac "abc_steps_l (0, args @ 0 \<up> (ft - arity)) ap n", auto)
  apply(drule_tac abc_list_crsp_steps, auto)
  apply(rule_tac list_crsp_simp2, auto)
  done

lemma find_exponent_rec_exec[simp]:
  assumes a: "args @ [rec_exec f args] = lm @ 0 \<up> n"
    and b: "length args < length lm"
  shows "\<exists>m. lm = args @ rec_exec f args # 0 \<up> m"
  using assms
  apply(cases n, simp)
   apply(rule_tac x = 0 in exI, simp)
  apply(drule_tac length_equal, simp)
  done

lemma find_exponent_complex[simp]: 
  "\<lbrakk>args @ [rec_exec f args] = lm @ 0 \<up> n; \<not> length args < length lm\<rbrakk>
  \<Longrightarrow> \<exists>m. (lm @ 0 \<up> (length args - length lm) @ [Suc 0])[length args := 0] =
  args @ rec_exec f args # 0 \<up> m"
  apply(cases n, simp_all add: exp_suc list_update_append list_update.simps del: replicate_Suc)
   apply(subgoal_tac "length args = Suc (length lm)", simp)
    apply(rule_tac x = "Suc (Suc 0)" in exI, simp)
   apply(drule_tac length_equal, simp, auto)
  done

lemma compile_append_dummy_correct: 
  assumes compile: "rec_ci f = (ap, ary, fp)"
    and termi: "terminate f args"
  shows "{\<lambda> nl. nl = args} (ap [+] dummy_abc (length args)) {\<lambda> nl. (\<exists> m. nl = args @ rec_exec f args # 0\<up>m)}"
proof(rule_tac abc_Hoare_plus_halt)
  show "{\<lambda>nl. nl = args} ap {\<lambda> nl. abc_list_crsp (args @ [rec_exec f args]) nl}"
    using compile termi recursive_compile_correct_norm'[of f ap ary fp args]
    apply(auto simp: abc_Hoare_halt_def)
    by (metis abc_final.simps abc_holds_for.simps)
next
  show "{abc_list_crsp (args @ [rec_exec f args])} dummy_abc (length args) 
    {\<lambda>nl. \<exists>m. nl = args @ rec_exec f args # 0 \<up> m}"
    apply(auto simp: dummy_abc_def abc_Hoare_halt_def)
    apply(rule_tac x = 3 in exI)
    by(force simp: abc_steps_l.simps abc_list_crsp_def abc_step_l.simps numeral_3_eq_3 abc_fetch.simps
        abc_lm_v.simps nth_append abc_lm_s.simps)
qed

lemma cn_merge_gs_split: 
  "\<lbrakk>i < length gs; rec_ci (gs!i) = (ga, gb, gc)\<rbrakk> \<Longrightarrow> 
  cn_merge_gs (map rec_ci gs) p =  cn_merge_gs (map rec_ci (take i gs)) p [+] (ga [+] 
       mv_box gb (p + i)) [+]  cn_merge_gs (map rec_ci (drop (Suc i) gs)) (p + Suc i)"
proof(induct i arbitrary: gs p)
  case 0
  then show ?case by(cases gs; simp)
next
  case (Suc i)
  then show ?case 
    by(cases gs, simp, cases "rec_ci (hd gs)", 
        simp add: abc_comp_commute[THEN sym])
qed

lemma cn_unhalt_case:
  assumes compile1: "rec_ci (Cn n f gs) = (ap, ar, ft) \<and> length args = ar"
    and g: "i < length gs"
    and compile2: "rec_ci (gs!i) = (gap, gar, gft) \<and> gar = length args"
    and g_unhalt: "\<And> anything. {\<lambda> nl. nl = args @ 0\<up>(gft - gar) @ anything} gap \<up>"
    and g_ind: "\<And> apj arj ftj j anything. \<lbrakk>j < i; rec_ci (gs!j) = (apj, arj, ftj)\<rbrakk> 
  \<Longrightarrow> {\<lambda> nl. nl = args @ 0\<up>(ftj - arj) @ anything} apj {\<lambda> nl. nl = args @ rec_exec (gs!j) args # 0\<up>(ftj - Suc arj) @ anything}"
    and all_termi: "\<forall> j<i. terminate (gs!j) args"
  shows "{\<lambda> nl. nl = args @ 0\<up>(ft - ar) @ anything} ap \<up>"
  using compile1
  apply(cases "rec_ci f", auto simp: rec_ci.simps abc_comp_commute)
proof(rule_tac abc_Hoare_plus_unhalt1)
  fix fap far fft
  let ?ft = "max (Suc (length args)) (Max (insert fft ((\<lambda>(aprog, p, n). n) ` rec_ci ` set gs)))"
  let ?Q = "\<lambda>nl. nl = args @ 0\<up> (?ft - length args) @ map (\<lambda>i. rec_exec i args) (take i gs) @ 
    0\<up>(length gs - i) @ 0\<up> Suc (length args) @ anything"
  have "cn_merge_gs (map rec_ci gs) ?ft = 
    cn_merge_gs (map rec_ci (take i gs)) ?ft [+] (gap [+] 
    mv_box gar (?ft + i)) [+]  cn_merge_gs (map rec_ci (drop (Suc i) gs)) (?ft + Suc i)"
    using g compile2 cn_merge_gs_split by simp
  thus "{\<lambda>nl. nl = args @ 0 # 0 \<up> (?ft + length gs) @ anything} (cn_merge_gs (map rec_ci gs) ?ft) \<up>"
  proof(simp, rule_tac abc_Hoare_plus_unhalt1, rule_tac abc_Hoare_plus_unhalt2, 
      rule_tac abc_Hoare_plus_unhalt1)
    let ?Q_tmp = "\<lambda>nl. nl = args @ 0\<up> (gft - gar) @ 0\<up>(?ft - (length args) - (gft -gar)) @ map (\<lambda>i. rec_exec i args) (take i gs) @ 
      0\<up>(length gs - i) @ 0\<up> Suc (length args) @ anything"
    have a: "{?Q_tmp} gap \<up>"
      using g_unhalt[of "0 \<up> (?ft - (length args) - (gft - gar)) @
        map (\<lambda>i. rec_exec i args) (take i gs) @ 0 \<up> (length gs - i) @ 0 \<up> Suc (length args) @ anything"]
      by simp
    moreover have "?ft \<ge> gft"
      using g compile2
      apply(rule_tac max.coboundedI2, rule_tac Max_ge, simp, rule_tac insertI2)
      apply(rule_tac  x = "rec_ci (gs ! i)" in image_eqI, simp)
      by(rule_tac x = "gs!i"  in image_eqI, simp, simp)
    then have b:"?Q_tmp = ?Q"
      using compile2
      apply(rule_tac arg_cong)
      by(simp add: replicate_merge_anywhere)
    thus "{?Q} gap \<up>"
      using a by simp
  next
    show "{\<lambda>nl. nl = args @ 0 # 0 \<up> (?ft + length gs) @ anything} 
      cn_merge_gs (map rec_ci (take i gs)) ?ft
       {\<lambda>nl. nl = args @ 0 \<up> (?ft - length args) @
      map (\<lambda>i. rec_exec i args) (take i gs) @ 0 \<up> (length gs - i) @ 0 \<up> Suc (length args) @ anything}"
      using all_termi
      by(rule_tac compile_cn_gs_correct', auto simp: set_conv_nth intro:g_ind)
  qed
qed



lemma mn_unhalt_case':
  assumes compile: "rec_ci f = (a, b, c)"
    and all_termi: "\<forall>i. terminate f (args @ [i]) \<and> 0 < rec_exec f (args @ [i])"
    and B: "B = [Dec (Suc (length args)) (length a + 5), Dec (Suc (length args)) (length a + 3), 
  Goto (Suc (length a)), Inc (length args), Goto 0]"
  shows "{\<lambda>nl. nl = args @ 0 \<up> (max (Suc (length args)) c - length args) @ anything}
  a @ B \<up>"
proof(rule_tac abc_Hoare_unhaltI, auto)
  fix n
  have a:  "b = Suc (length args)"
    using all_termi compile
    apply(erule_tac x = 0 in allE)
    by(auto, drule_tac param_pattern,auto)
  moreover have b: "c > b"
    using compile by(elim footprint_ge)
  ultimately have c: "max (Suc (length args)) c = c" by arith
  have "\<exists> stp > n. abc_steps_l (0, args @ 0 # 0\<up>(c - Suc (length args)) @ anything) (a @ B) stp
         = (0, args @ Suc n # 0\<up>(c - Suc (length args)) @ anything)"
    using assms a b c
  proof(rule_tac mn_loop_correct', auto)
    fix i xc
    show "{\<lambda>nl. nl = args @ i # 0 \<up> (c - Suc (length args)) @ xc} a 
      {\<lambda>nl. nl = args @ i # rec_exec f (args @ [i]) # 0 \<up> (c - Suc (Suc (length args))) @ xc}"
      using all_termi recursive_compile_correct[of f "args @ [i]" a b c xc] compile a
      by(simp)
  qed
  then obtain stp where d: "stp > n \<and> abc_steps_l (0, args @ 0 # 0\<up>(c - Suc (length args)) @ anything) (a @ B) stp
         = (0, args @ Suc n # 0\<up>(c - Suc (length args)) @ anything)" ..
  then obtain d where e: "stp = n + Suc d"
    by (metis add_Suc_right less_iff_Suc_add)
  obtain s nl where f: "abc_steps_l (0, args @ 0 # 0\<up>(c - Suc (length args)) @ anything) (a @ B) n = (s, nl)"
    by (metis prod.exhaust)
  have g: "s < length (a @ B)"
    using d e f
    apply(rule_tac classical, simp only: abc_steps_add)
    by(simp add: halt_steps2 leI)
  from f g show "abc_notfinal (abc_steps_l (0, args @ 0 \<up> 
    (max (Suc (length args)) c - length args) @ anything) (a @ B) n) (a @ B)"
    using c b a
    by(simp add: replicate_Suc_iff_anywhere Suc_diff_Suc del: replicate_Suc)
qed

lemma mn_unhalt_case: 
  assumes compile: "rec_ci (Mn n f) = (ap, ar, ft) \<and> length args = ar"
    and all_term: "\<forall> i. terminate f (args @ [i]) \<and> rec_exec f (args @ [i]) > 0"
  shows "{\<lambda> nl. nl = args @ 0\<up>(ft - ar) @ anything} ap \<up> "
  using assms
  apply(cases "rec_ci f", auto simp: rec_ci.simps abc_comp_commute)
  by(rule_tac mn_unhalt_case', simp_all)

fun tm_of_rec :: "recf \<Rightarrow> instr list"
  where "tm_of_rec recf = (let (ap, k, fp) = rec_ci recf in
                         let tp = tm_of (ap [+] dummy_abc k) in 
                           tp @ (shift (mopup k) (length tp div 2)))"

lemma recursive_compile_to_tm_correct1: 
  assumes  compile: "rec_ci recf = (ap, ary, fp)"
    and termi: " terminate recf args"
    and tp: "tp = tm_of (ap [+] dummy_abc (length args))"
  shows "\<exists> stp m l. steps0 (Suc 0, Bk # Bk # ires, <args> @ Bk\<up>rn)
  (tp @ shift (mopup (length args)) (length tp div 2)) stp = (0, Bk\<up>m @ Bk # Bk # ires, Oc\<up>Suc (rec_exec recf args) @ Bk\<up>l)"
proof -
  have "{\<lambda>nl. nl = args} ap [+] dummy_abc (length args) {\<lambda>nl. \<exists>m. nl = args @ rec_exec recf args # 0 \<up> m}"
    using compile termi compile
    by(rule_tac compile_append_dummy_correct, auto)
  then obtain stp m where h: "abc_steps_l (0, args) (ap [+] dummy_abc (length args)) stp = 
    (length (ap [+] dummy_abc (length args)), args @ rec_exec recf args # 0\<up>m) "
    apply(simp add: abc_Hoare_halt_def, auto)
    apply(rename_tac n)
    by(case_tac "abc_steps_l (0, args) (ap [+] dummy_abc (length args)) n", auto)
  thus "?thesis"
    using assms tp compile_correct_halt[OF refl refl _ h _ _ refl]
    by(auto simp: crsp.simps start_of.simps abc_lm_v.simps)
qed

lemma recursive_compile_to_tm_correct2: 
  assumes termi: " terminate recf args"
  shows "\<exists> stp m l. steps0 (Suc 0, [Bk, Bk], <args>) (tm_of_rec recf) stp = 
                     (0, Bk\<up>Suc (Suc m), Oc\<up>Suc (rec_exec recf args) @ Bk\<up>l)"
proof(cases "rec_ci recf", simp add: tm_of_rec.simps)
  fix ap ar fp
  assume "rec_ci recf = (ap, ar, fp)"
  thus "\<exists>stp m l. steps0 (Suc 0, [Bk, Bk], <args>) 
    (tm_of (ap [+] dummy_abc ar) @ shift (mopup ar) (sum_list (layout_of (ap [+] dummy_abc ar)))) stp =
    (0, Bk # Bk # Bk \<up> m, Oc # Oc \<up> rec_exec recf args @ Bk \<up> l)"
    using recursive_compile_to_tm_correct1[of recf ap ar fp args "tm_of (ap [+] dummy_abc (length args))" "[]" 0]
      assms param_pattern[of recf args ap ar fp]
    by(simp add: replicate_Suc[THEN sym] replicate_Suc_iff_anywhere del: replicate_Suc, 
        simp add: exp_suc del: replicate_Suc)
qed

lemma recursive_compile_to_tm_correct3: 
  assumes termi: "terminate recf args"
  shows "{\<lambda> tp. tp =([Bk, Bk], <args>)} (tm_of_rec recf) 
         {\<lambda> tp. \<exists> k l. tp = (Bk\<up> k, <rec_exec recf args> @ Bk \<up> l)}"
  using recursive_compile_to_tm_correct2[OF assms]
  apply(auto simp add: Hoare_halt_def ) apply(rename_tac stp M l)
  apply(rule_tac x = stp in exI)
  apply(auto simp add: tape_of_nat_def)
  apply(rule_tac x = "Suc (Suc M)" in exI)
  apply(simp)
  done 

lemma list_all_suc_many[simp]:
  "list_all (\<lambda>(acn, s). s \<le> Suc (Suc (Suc (Suc (Suc (Suc (2 * n))))))) xs \<Longrightarrow>
  list_all (\<lambda>(acn, s). s \<le> Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (2 * n))))))))) xs"
proof(induct xs)
  case (Cons a xs)
  then show ?case by(cases a, simp)
qed simp


lemma shift_append: "shift (xs @ ys) n = shift xs n @ shift ys n"
  apply(simp add: shift.simps)
  done

lemma length_shift_mopup[simp]: "length (shift (mopup n) ss) = 4 * n + 12"
  apply(auto simp: mopup.simps shift_append mopup_b_def)
  done

lemma length_tm_even[intro]: "length (tm_of ap) mod 2 = 0"
  apply(simp add: tm_of.simps)
  done

lemma tms_of_at_index[simp]: "k < length ap \<Longrightarrow> tms_of ap ! k  = 
 ci (layout_of ap) (start_of (layout_of ap) k) (ap ! k)"
  apply(simp add: tms_of.simps tpairs_of.simps)
  done

lemma start_of_suc_inc:
  "\<lbrakk>k < length ap; ap ! k = Inc n\<rbrakk> \<Longrightarrow> start_of (layout_of ap) (Suc k) =
                        start_of (layout_of ap) k + 2 * n + 9"
  apply(rule_tac start_of_Suc1, auto simp: abc_fetch.simps)
  done

lemma start_of_suc_dec:
  "\<lbrakk>k < length ap; ap ! k = (Dec n e)\<rbrakk> \<Longrightarrow> start_of (layout_of ap) (Suc k) =
                        start_of (layout_of ap) k + 2 * n + 16"
  apply(rule_tac start_of_Suc2, auto simp: abc_fetch.simps)
  done

lemma inc_state_all_le:
  "\<lbrakk>k < length ap; ap ! k = Inc n; 
       (a, b) \<in> set (shift (shift tinc_b (2 * n)) 
                            (start_of (layout_of ap) k - Suc 0))\<rbrakk>
       \<Longrightarrow> b \<le> start_of (layout_of ap) (length ap)"
  apply(subgoal_tac "b \<le> start_of (layout_of ap) (Suc k)")
   apply(subgoal_tac "start_of (layout_of ap) (Suc k) \<le> start_of (layout_of ap) (length ap) ")
    apply(arith)
   apply(cases "Suc k = length ap", simp)
   apply(rule_tac start_of_less, simp)
  apply(auto simp: tinc_b_def shift.simps start_of_suc_inc length_of.simps )
  done

lemma findnth_le[elim]: 
  "(a, b) \<in> set (shift (findnth n) (start_of (layout_of ap) k - Suc 0))
  \<Longrightarrow> b \<le> Suc (start_of (layout_of ap) k + 2 * n)"
  apply(induct n, force simp add: shift.simps)
  apply(simp add: shift_append, auto)
  apply(auto simp: shift.simps)
  done

lemma findnth_state_all_le1:
  "\<lbrakk>k < length ap; ap ! k = Inc n;
  (a, b) \<in> 
  set (shift (findnth n) (start_of (layout_of ap) k - Suc 0))\<rbrakk> 
  \<Longrightarrow> b \<le> start_of (layout_of ap) (length ap)"
  apply(subgoal_tac "b \<le> start_of (layout_of ap) (Suc k)")
   apply(subgoal_tac "start_of (layout_of ap) (Suc k) \<le> start_of (layout_of ap) (length ap) ")
    apply(arith)
   apply(cases "Suc k = length ap", simp)
   apply(rule_tac start_of_less, simp)
  apply(subgoal_tac "b \<le> start_of (layout_of ap) k + 2*n + 1 \<and> 
     start_of (layout_of ap) k + 2*n + 1 \<le>  start_of (layout_of ap) (Suc k)", auto)
  apply(auto simp: tinc_b_def shift.simps length_of.simps  start_of_suc_inc)
  done

lemma start_of_eq: "length ap < as \<Longrightarrow> start_of (layout_of ap) as = start_of (layout_of ap) (length ap)"
proof(induct as)
  case (Suc as)
  then show ?case 
    apply(cases "length ap < as", simp add: start_of.simps)
    apply(subgoal_tac "as = length ap")
     apply(simp add: start_of.simps)
    apply arith
    done
qed simp

lemma start_of_all_le: "start_of (layout_of ap) as \<le> start_of (layout_of ap) (length ap)"
  apply(subgoal_tac "as > length ap \<or> as = length ap \<or> as < length ap", 
      auto simp: start_of_eq start_of_less)
  done

lemma findnth_state_all_le2: 
  "\<lbrakk>k < length ap; 
  ap ! k = Dec n e;
  (a, b) \<in> set (shift (findnth n) (start_of (layout_of ap) k - Suc 0))\<rbrakk>
  \<Longrightarrow> b \<le> start_of (layout_of ap) (length ap)"
  apply(subgoal_tac "b \<le> start_of (layout_of ap) k + 2*n + 1 \<and> 
     start_of (layout_of ap) k + 2*n + 1 \<le>  start_of (layout_of ap) (Suc k) \<and>
      start_of (layout_of ap) (Suc k) \<le> start_of (layout_of ap) (length ap)", auto)
   apply(subgoal_tac "start_of (layout_of ap) (Suc k) = 
  start_of  (layout_of ap)  k + 2*n + 16", simp)
   apply(simp add: start_of_suc_dec)
  apply(rule_tac start_of_all_le)
  done

lemma dec_state_all_le[simp]:
  "\<lbrakk>k < length ap; ap ! k = Dec n e; 
  (a, b) \<in> set (shift (shift tdec_b (2 * n))
  (start_of (layout_of ap) k - Suc 0))\<rbrakk>
       \<Longrightarrow> b \<le> start_of (layout_of ap) (length ap)"
  apply(subgoal_tac "2*n + start_of (layout_of ap) k + 16 \<le> start_of (layout_of ap) (length ap) \<and> start_of (layout_of ap) k > 0")
   prefer 2
   apply(subgoal_tac "start_of (layout_of ap) (Suc k) = start_of (layout_of ap) k + 2*n + 16
                 \<and> start_of (layout_of ap) (Suc k) \<le> start_of (layout_of ap) (length ap)")
    apply(simp, rule_tac conjI)
    apply(simp add: start_of_suc_dec)
   apply(rule_tac start_of_all_le)
  apply(auto simp: tdec_b_def shift.simps)
  done

lemma tms_any_less: 
  "\<lbrakk>k < length ap; (a, b) \<in> set (tms_of ap ! k)\<rbrakk> \<Longrightarrow> 
  b \<le> start_of (layout_of ap) (length ap)"
  apply(cases "ap!k", auto simp: tms_of.simps tpairs_of.simps ci.simps shift_append adjust.simps)
      apply(erule_tac findnth_state_all_le1, simp_all)
     apply(erule_tac inc_state_all_le, simp_all)
    apply(erule_tac findnth_state_all_le2, simp_all)
   apply(rule_tac start_of_all_le)
  apply(rule_tac start_of_all_le)
  done

lemma concat_in: "i < length (concat xs) \<Longrightarrow> 
  \<exists>k < length xs. concat xs ! i \<in> set (xs ! k)"
proof(induct xs rule: rev_induct)
  case (snoc x xs)
  then show ?case
    apply(cases "i < length (concat xs)", simp)
     apply(erule_tac exE, rule_tac x = k in exI)
     apply(simp add: nth_append)
    apply(rule_tac x = "length xs" in exI, simp)
    apply(simp add: nth_append)
    done 
qed auto

declare length_concat[simp]

lemma in_tms: "i < length (tm_of ap) \<Longrightarrow> \<exists> k < length ap. (tm_of ap ! i) \<in> set (tms_of ap ! k)"
  apply(simp only: tm_of.simps)
  using concat_in[of i "tms_of ap"]
  apply(auto)
  done

lemma all_le_start_of: "list_all (\<lambda>(acn, s). 
  s \<le> start_of (layout_of ap) (length ap)) (tm_of ap)"
  apply(simp only: list_all_length)
  apply(rule_tac allI, rule_tac impI)
  apply(drule_tac in_tms, auto elim: tms_any_less)
  done

lemma length_ci: 
  "\<lbrakk>k < length ap; length (ci ly y (ap ! k)) = 2 * qa\<rbrakk>
      \<Longrightarrow> layout_of ap ! k = qa"
  apply(cases "ap ! k")
    apply(auto simp: layout_of.simps ci.simps 
      length_of.simps tinc_b_def tdec_b_def length_findnth adjust.simps)
  done

lemma ci_even[intro]: "length (ci ly y i) mod 2 = 0"
  apply(cases i, auto simp: ci.simps length_findnth
      tinc_b_def adjust.simps tdec_b_def)
  done

lemma sum_list_ci_even[intro]: "sum_list (map (length \<circ> (\<lambda>(x, y). ci ly x y)) zs) mod 2 = 0"
proof(induct zs rule: rev_induct)
  case (snoc x xs)
  then show ?case 
    apply(cases x, simp)
    apply(subgoal_tac "length (ci ly (fst x) (snd x)) mod 2 = 0")
     apply(auto)
    done
qed (simp)

lemma zip_pre:
  "(length ys) \<le> length ap \<Longrightarrow>
  zip ys ap = zip ys (take (length ys) (ap::'a list))"
proof(induct ys arbitrary: ap)
  case (Cons a ys)
  from Cons(2) have z:"ap = aa # list \<Longrightarrow> zip (a # ys) ap = zip (a # ys) (take (length (a # ys)) ap)"
    for aa list using Cons(1)[of list] by simp
  thus ?case by (cases ap;simp)
qed simp

lemma length_start_of_tm: "start_of (layout_of ap) (length ap) = Suc (length (tm_of ap)  div 2)"
  using tpa_states[of "tm_of ap"  "length ap" ap]
  by(simp add: tm_of.simps)

lemma list_all_add_6E[elim]: "list_all (\<lambda>(acn, s). s \<le> Suc q) xs
        \<Longrightarrow> list_all (\<lambda>(acn, s). s \<le> q + (2 * n + 6)) xs"
  by(auto simp: list_all_length)

lemma mopup_b_12[simp]: "length mopup_b = 12"
  by(simp add: mopup_b_def)

lemma mp_up_all_le: "list_all  (\<lambda>(acn, s). s \<le> q + (2 * n + 6)) 
  [(R, Suc (Suc (2 * n + q))), (R, Suc (2 * n + q)), 
  (L, 5 + 2 * n + q), (W0, Suc (Suc (Suc (2 * n + q)))), (R, 4 + 2 * n + q),
  (W0, Suc (Suc (Suc (2 * n + q)))), (R, Suc (Suc (2 * n + q))),
  (W0, Suc (Suc (Suc (2 * n + q)))), (L, 5 + 2 * n + q),
  (L, 6 + 2 * n + q), (R, 0),  (L, 6 + 2 * n + q)]"
  by(auto)

lemma mopup_le6[simp]: "(a, b) \<in> set (mopup_a n) \<Longrightarrow> b \<le> 2 * n + 6"
  by(induct n, auto simp: mopup_a.simps)

lemma shift_le2[simp]: "(a, b) \<in> set (shift (mopup n) x)
  \<Longrightarrow> b \<le> (2 * x + length (mopup n)) div 2"
  apply(auto simp: mopup.simps shift_append shift.simps)
  apply(auto simp: mopup_b_def)
  done

lemma mopup_ge2[intro]: " 2 \<le> x + length (mopup n)"
  apply(simp add: mopup.simps)
  done

lemma mopup_even[intro]: " (2 * x + length (mopup n)) mod 2 = 0"
  by(auto simp: mopup.simps)

lemma mopup_div_2[simp]: "b \<le> Suc x
          \<Longrightarrow> b \<le> (2 * x + length (mopup n)) div 2"
  by(auto simp: mopup.simps)

lemma wf_tm_from_abacus: assumes "tp = tm_of ap"
  shows "tm_wf0 (tp @ shift (mopup n) (length tp div 2))"
proof -
  have "is_even (length (mopup n))" for n using tm_wf.simps by blast
  moreover have "(aa, ba) \<in> set (mopup n) \<Longrightarrow> ba \<le> length (mopup n) div 2" for aa ba
    by (metis (no_types, lifting) add_cancel_left_right case_prodD tm_wf.simps wf_mopup)
  moreover have "(\<forall>x\<in>set (tm_of ap). case x of (acn, s) \<Rightarrow> s \<le> Suc (sum_list (layout_of ap))) \<Longrightarrow>
           (a, b) \<in> set (tm_of ap) \<Longrightarrow> b \<le> sum_list (layout_of ap) + length (mopup n) div 2"
    for a b s
    by (metis (no_types, lifting) add_Suc add_cancel_left_right case_prodD div_mult_mod_eq le_SucE mult_2_right not_numeral_le_zero tm_wf.simps trans_le_add1 wf_mopup)
  ultimately show ?thesis unfolding assms
    using length_start_of_tm[of ap] all_le_start_of[of ap] tm_wf.simps 
    by(auto simp: List.list_all_iff shift.simps)
qed

lemma wf_tm_from_recf:
  assumes compile: "tp = tm_of_rec recf"
  shows "tm_wf0 tp"
proof -
  obtain a b c where "rec_ci recf = (a, b, c)"
    by (metis prod_cases3)
  thus "?thesis"
    using compile
    using wf_tm_from_abacus[of "tm_of (a [+] dummy_abc b)" "(a [+] dummy_abc b)" b]
    by simp
qed

end