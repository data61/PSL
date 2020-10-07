section \<open>The programming language and its semantics\<close> 

theory Language_Semantics imports Interface begin


subsection \<open>Syntax and operational semantics\<close>

datatype ('test,'atom) com = 
  Atm 'atom | 
  Seq "('test,'atom) com" "('test,'atom) com" 
    ("_ ;; _"  [60, 61] 60) |
  If 'test "('test,'atom) com" "('test,'atom) com" 
    ("(if _/ then _/ else _)"  [0, 0, 61] 61) |
  While 'test "('test,'atom) com" 
    ("(while _/ do _)"  [0, 61] 61) |
  Par "('test,'atom) com" "('test,'atom) com" 
    ("_ | _"  [60, 61] 60)
  
locale PL = 
fixes 
  tval :: "'test \<Rightarrow> 'state \<Rightarrow> bool" and 
  aval :: "'atom \<Rightarrow> 'state \<Rightarrow> 'state"

(* *****************************************)
context PL
begin

text\<open>Conventions and notations:
-- suffixes: ``C" for ``Continuation", ``T" for ``termination"
-- prefix: ``M" for multistep
-- tst, tst' are tests
-- atm, atm' are atoms (atomic commands)
-- s, s', t, t' are states
-- c, c', d, d' are commands
-- cf, cf' are configurations, i.e., pairs command-state\<close>

inductive transT :: 
"(('test,'atom)com * 'state) \<Rightarrow> 'state \<Rightarrow> bool"
(infix "\<rightarrow>t" 55)
where
  Atm[simp]: 
"(Atm atm, s) \<rightarrow>t aval atm s"
| WhileFalse[simp]:  
"~ tval tst s \<Longrightarrow> (While tst c, s) \<rightarrow>t s"

lemmas trans_Atm = Atm  
lemmas trans_WhileFalse = WhileFalse

(* The RT-closure of \<rightarrow>c is inlined since later versions of \<rightarrow>c may refer to it. *)
inductive transC :: 
"(('test,'atom)com * 'state) \<Rightarrow> (('test,'atom)com * 'state) \<Rightarrow> bool"
(infix "\<rightarrow>c" 55)
and MtransC :: 
"(('test,'atom)com * 'state) \<Rightarrow> (('test,'atom)com * 'state) \<Rightarrow> bool"
(infix "\<rightarrow>*c" 55)
where
  SeqC[simp]:
"(c1, s) \<rightarrow>c (c1', s') \<Longrightarrow> (c1 ;; c2, s) \<rightarrow>c (c1' ;; c2, s')" 
| SeqT[simp]:
"(c1, s) \<rightarrow>t s' \<Longrightarrow> (c1 ;; c2, s) \<rightarrow>c (c2, s')" 
| IfTrue[simp]:  
"tval tst s \<Longrightarrow> (If tst c1 c2, s) \<rightarrow>c (c1, s)"
| IfFalse[simp]:  
"~ tval tst s \<Longrightarrow> (If tst c1 c2,s) \<rightarrow>c (c2, s)"
| WhileTrue[simp]:  
"tval tst s \<Longrightarrow> (While tst c, s) \<rightarrow>c (c ;; (While tst c), s)"
(*  *)
| ParCL[simp]:
"(c1, s) \<rightarrow>c (c1', s') \<Longrightarrow> (Par c1 c2, s) \<rightarrow>c (Par c1' c2, s')" 
| ParCR[simp]:
"(c2, s) \<rightarrow>c (c2', s') \<Longrightarrow> (Par c1 c2, s) \<rightarrow>c (Par c1 c2', s')" 
| ParTL[simp]:
"(c1, s) \<rightarrow>t s' \<Longrightarrow> (Par c1 c2, s) \<rightarrow>c (c2, s')" 
| ParTR[simp]:
"(c2, s) \<rightarrow>t s' \<Longrightarrow> (Par c1 c2, s) \<rightarrow>c (c1, s')" 
| Refl:
"(c,s) \<rightarrow>*c (c,s)"
| Step:
"\<lbrakk>(c,s) \<rightarrow>*c (c',s'); (c',s') \<rightarrow>c (c'',s'')\<rbrakk> \<Longrightarrow> (c,s) \<rightarrow>*c (c'',s'')"

lemmas trans_SeqC = SeqC lemmas trans_SeqT = SeqT 
lemmas trans_IfTrue = IfTrue lemmas trans_IfFalse = IfFalse
lemmas trans_WhileTrue = WhileTrue 
lemmas trans_ParCL = ParCL  lemmas trans_ParCR = ParCR
lemmas trans_ParTL = ParTL  lemmas trans_ParTR = ParTR
lemmas trans_Refl = Refl  lemmas trans_Step = Step

lemma MtransC_Refl[simp]: "cf \<rightarrow>*c cf"
using trans_Refl by(cases cf, simp)

lemmas transC_induct = transC_MtransC.inducts(1)
  [split_format(complete), 
   where ?P2.0 = "\<lambda> c s c' s'. True"]
lemmas MtransC_induct_temp = transC_MtransC.inducts(2)[split_format(complete)]

inductive MtransT :: 
"(('test,'atom)com * 'state) \<Rightarrow> 'state \<Rightarrow> bool"
(infix "\<rightarrow>*t" 55)
where
  StepT:
"\<lbrakk>cf \<rightarrow>*c cf'; cf' \<rightarrow>t s''\<rbrakk> \<Longrightarrow> cf \<rightarrow>*t s''"

lemma MtransC_rtranclp_transC:
"MtransC = transC ^**"
proof-
  {fix c s c' s'
   have "(c,s) \<rightarrow>*c (c',s') \<Longrightarrow> transC ^** (c,s) (c',s')"
   apply(rule MtransC_induct_temp[of _ _ c s c' s' "\<lambda>c s c' s'. True"]) by auto
  }
  moreover 
  {fix c s c' s'
   have "transC ^** (c,s) (c',s') \<Longrightarrow> (c,s) \<rightarrow>*c (c',s')"
   apply(erule rtranclp.induct) using trans_Step by auto
  }
  ultimately show ?thesis
  apply - apply(rule ext, rule ext) by auto
qed

lemma transC_MtransC[simp]:
assumes "cf \<rightarrow>c cf'"
shows "cf \<rightarrow>*c cf'"
using assms unfolding MtransC_rtranclp_transC by blast

lemma MtransC_Trans:
assumes "cf \<rightarrow>*c cf'" and "cf' \<rightarrow>*c cf''"
shows "cf \<rightarrow>*c cf''"
using assms rtranclp_trans[of transC cf cf' cf''] 
unfolding MtransC_rtranclp_transC by blast

lemma MtransC_StepC:
assumes *: "cf \<rightarrow>*c cf'" and **: "cf' \<rightarrow>c cf''"
shows "cf \<rightarrow>*c cf''"
proof-
  have "cf' \<rightarrow>*c cf''" using ** by simp
  thus ?thesis using * MtransC_Trans by blast
qed

lemma MtransC_induct[consumes 1, case_names Refl Trans]:
assumes "cf \<rightarrow>*c cf'"
and "\<And>cf. phi cf cf"
and 
"\<And> cf cf' cf''. 
   \<lbrakk>cf \<rightarrow>*c cf'; phi cf cf'; cf' \<rightarrow>c cf''\<rbrakk>
   \<Longrightarrow> phi cf cf''"
shows "phi cf cf'"
using assms unfolding MtransC_rtranclp_transC 
using rtranclp.induct[of transC cf cf'] by blast

lemma MtransC_induct2[consumes 1, case_names Refl Trans, induct pred: MtransC]:
assumes "(c,s) \<rightarrow>*c (c',s')"
and "\<And>c s. phi c s c s"
and 
"\<And> c s c' s' c'' s''. 
   \<lbrakk>(c,s) \<rightarrow>*c (c',s'); phi c s c' s'; (c',s') \<rightarrow>c (c'',s'')\<rbrakk>
   \<Longrightarrow> phi c s c'' s''"
shows "phi c s c' s'"
using assms 
MtransC_induct[of "(c,s)" "(c',s')" "\<lambda>(c,s) (c',s'). phi c s c' s'"] by blast

lemma transT_MtransT[simp]:
assumes "cf \<rightarrow>t s'"
shows "cf \<rightarrow>*t s'"
by (metis PL.MtransC_Refl PL.MtransT.intros assms)

lemma MtransC_MtransT:
assumes "cf \<rightarrow>*c cf'" and "cf' \<rightarrow>*t cf''"
shows "cf \<rightarrow>*t cf''"
by (metis MtransT.cases PL.MtransC_Trans PL.MtransT.intros assms)

lemma transC_MtransT[simp]:
assumes "cf \<rightarrow>c cf'" and "cf' \<rightarrow>*t s''"
shows "cf \<rightarrow>*t s''"
by (metis PL.MtransC_MtransT assms(1) assms(2) transC_MtransC)

text\<open>Inversion rules, nchotomies and such:\<close>

lemma Atm_transC_simp[simp]:
"~ (Atm atm, s) \<rightarrow>c cf"
apply clarify apply(erule transC.cases) by auto

lemma Atm_transC_invert[elim!]:
assumes "(Atm atm, s) \<rightarrow>c cf"
shows phi
using assms by simp

lemma Atm_transT_invert[elim!]:
assumes "(Atm atm, s) \<rightarrow>t s'"
and "s' = aval atm s \<Longrightarrow> phi"
shows phi
using assms apply - apply(erule transT.cases) by auto

lemma Seq_transC_invert[elim!]:
assumes "(c1 ;; c2, s) \<rightarrow>c (c', s')"
and "\<And> c1'. \<lbrakk>(c1, s) \<rightarrow>c (c1',s'); c' = c1' ;; c2\<rbrakk> \<Longrightarrow> phi"
and "\<lbrakk>(c1, s) \<rightarrow>t s'; c' = c2\<rbrakk> \<Longrightarrow> phi"
shows phi
using assms apply - apply(erule transC.cases) by auto

lemma Seq_transT_invert[simp]:
"~ (c1 ;; c2, s) \<rightarrow>t s'"
apply clarify apply(erule transT.cases) by auto

lemma If_transC_invert[elim!]:
assumes "(If tst c1 c2, s) \<rightarrow>c (c', s')"
and "\<lbrakk>tval tst s; c' = c1; s' = s\<rbrakk> \<Longrightarrow> phi"
and "\<lbrakk>~ tval tst s; c' = c2; s' = s\<rbrakk> \<Longrightarrow> phi"
shows phi
using assms apply - apply(erule transC.cases) by auto

lemma If_transT_simp[simp]:
"~ (If b c1 c2, s) \<rightarrow>t s'"
apply clarify apply(erule transT.cases) by auto

lemma If_transT_invert[elim!]:
assumes "(If b c1 c2, s) \<rightarrow>t s'"
shows phi
using assms by simp

lemma While_transC_invert[elim]:
assumes "(While tst c1, s) \<rightarrow>c (c', s')"
and "\<lbrakk>tval tst s; c' = c1 ;; (While tst c1); s' = s\<rbrakk> \<Longrightarrow> phi"
shows phi
using assms apply - apply(erule transC.cases) by auto

lemma While_transT_invert[elim!]:
assumes "(While tst c1, s) \<rightarrow>t s'"
and "\<lbrakk>~ tval tst s; s' = s\<rbrakk> \<Longrightarrow> phi"
shows phi
using assms apply - apply(erule transT.cases) by blast+

lemma Par_transC_invert[elim!]:
assumes "(Par c1 c2, s) \<rightarrow>c (c', s')"
and "\<And> c1'. \<lbrakk>(c1, s) \<rightarrow>c (c1',s'); c' = Par c1' c2\<rbrakk> \<Longrightarrow> phi"
and "\<lbrakk>(c1, s) \<rightarrow>t s'; c' = c2\<rbrakk> \<Longrightarrow> phi"
and "\<And> c2'. \<lbrakk>(c2, s) \<rightarrow>c (c2',s'); c' = Par c1 c2'\<rbrakk> \<Longrightarrow> phi"
and "\<lbrakk>(c2, s) \<rightarrow>t s'; c' = c1\<rbrakk> \<Longrightarrow> phi"
shows phi
using assms apply - apply(erule transC.cases) by auto

lemma Par_transT_simp[simp]:
"~ (Par c1 c2, s) \<rightarrow>t s'"
apply clarify apply(erule transT.cases) by auto

lemma Par_transT_invert[elim!]:
assumes "(Par c1 c2, s) \<rightarrow>t s'"
shows phi
using assms by simp

lemma trans_nchotomy:
"(\<exists> c' s'. (c,s) \<rightarrow>c (c',s')) \<or> 
 (\<exists> s'. (c,s) \<rightarrow>t s')"
proof-
  let ?phiC = "\<lambda>c. \<exists> c' s'. (c,s) \<rightarrow>c (c',s')"
  let ?phiT = "\<lambda>c. \<exists> s'. (c,s) \<rightarrow>t s'"
  let ?phi = "\<lambda>c. ?phiC c \<or> ?phiT c"
  show "?phi c"
  apply(induct c)
  by(metis Atm, metis SeqC SeqT, metis IfFalse IfTrue, 
  metis WhileFalse WhileTrue, 
  metis ParCL ParCR ParTL ParTR)
qed

corollary trans_invert:
assumes 
"\<And> c' s'. (c,s) \<rightarrow>c (c',s') \<Longrightarrow> phi"
and "\<And> s'. (c,s) \<rightarrow>t s' \<Longrightarrow> phi" 
shows phi
using assms trans_nchotomy by blast

lemma not_transC_transT:
"\<lbrakk>cf \<rightarrow>c cf'; cf \<rightarrow>t s'\<rbrakk> \<Longrightarrow> phi"
apply(erule transC.cases) by auto

lemmas MtransT_invert = MtransT.cases

lemma MtransT_invert2:
assumes "(c, s) \<rightarrow>*t s''"
and "\<And> c' s'. \<lbrakk>(c,s) \<rightarrow>*c (c',s'); (c', s') \<rightarrow>t s''\<rbrakk> \<Longrightarrow> phi"
shows phi
using assms apply - apply(erule MtransT.cases) by auto

lemma Seq_MtransC_invert[elim!]:
assumes "(c1 ;; c2, s) \<rightarrow>*c (d', t')"
and "\<And> c1'. \<lbrakk>(c1, s) \<rightarrow>*c (c1',t'); d' = c1' ;; c2\<rbrakk> \<Longrightarrow> phi"
and "\<And> s'. \<lbrakk>(c1, s) \<rightarrow>*t s'; (c2, s') \<rightarrow>*c (d',t')\<rbrakk> \<Longrightarrow> phi"
shows phi
proof-
  {fix c
   have "(c,s) \<rightarrow>*c (d',t') \<Longrightarrow> 
   \<forall> c1 c2. 
     c = c1 ;; c2 \<longrightarrow>  
     (\<exists> c1'. (c1, s) \<rightarrow>*c (c1',t') \<and> d' = c1' ;; c2) \<or> 
     (\<exists> s'. (c1, s) \<rightarrow>*t s' \<and> (c2, s') \<rightarrow>*c (d',t'))"
   apply(erule MtransC_induct2) proof(tactic \<open>mauto_no_simp_tac @{context}\<close>)
     fix c s d' t' d'' t'' c1 c2
     assume (*  "(c, s) \<rightarrow>*c (d', t')" and *)
     "\<forall>c1 c2. c = c1 ;; c2 \<longrightarrow> 
        (\<exists>c1'. (c1, s) \<rightarrow>*c (c1', t') \<and> d' = c1' ;; c2) \<or> 
        (\<exists>s'. (c1, s) \<rightarrow>*t s' \<and> (c2, s') \<rightarrow>*c (d', t'))"
     and 1: "(d', t') \<rightarrow>c (d'', t'')" and "c = c1 ;; c2"
     hence IH: 
     "(\<exists>c1'. (c1, s) \<rightarrow>*c (c1', t') \<and> d' = c1' ;; c2) \<or> 
      (\<exists>s'. (c1, s) \<rightarrow>*t s' \<and> (c2, s') \<rightarrow>*c (d', t'))" by simp 
     show "(\<exists>c1''. (c1, s) \<rightarrow>*c (c1'', t'') \<and> d'' = c1'' ;; c2) \<or> 
           (\<exists>s''. (c1, s) \<rightarrow>*t s'' \<and> (c2, s'') \<rightarrow>*c (d'', t''))"
     proof-
       {fix c1' assume 2: "(c1, s) \<rightarrow>*c (c1', t')" and d': "d' = c1' ;; c2"
        have ?thesis
        using 1 unfolding d' apply - proof(erule Seq_transC_invert)
          fix c1'' assume "(c1', t') \<rightarrow>c (c1'', t'')" and d'': "d'' = c1'' ;; c2"
          hence "(c1, s) \<rightarrow>*c (c1'', t'')" using 2 MtransC_StepC by blast
          thus ?thesis using d'' by blast
        next
          assume "(c1', t') \<rightarrow>t t''" and d'': "d'' = c2"
          hence "(c1, s) \<rightarrow>*t t''" using 2 MtransT.StepT by blast
          thus ?thesis unfolding d'' by auto
        qed
       }
       moreover
       {fix s' assume 2: "(c1, s) \<rightarrow>*t s'" and "(c2, s') \<rightarrow>*c (d', t')"
        hence "(c2, s') \<rightarrow>*c (d'', t'')" using 1 MtransC_StepC by blast
        hence ?thesis using 2 by blast
       }
       ultimately show ?thesis using IH by blast
     qed
   qed (metis PL.MtransC_Refl)
  }
  thus ?thesis using assms by blast
qed

lemma Seq_MtransT_invert[elim!]:
assumes *: "(c1 ;; c2, s) \<rightarrow>*t s''"
and **: "\<And> s'. \<lbrakk>(c1, s) \<rightarrow>*t s'; (c2, s') \<rightarrow>*t s''\<rbrakk> \<Longrightarrow> phi"
shows phi
proof-
  obtain d' t' where 1: "(c1 ;; c2, s) \<rightarrow>*c (d',t')" and 2: "(d',t') \<rightarrow>t s''"
  using * apply - apply(erule MtransT_invert2) by auto
  show ?thesis 
  using 1 apply - proof(erule Seq_MtransC_invert) 
    fix c1' assume "d' = c1' ;; c2"
    hence False using 2 by simp
    thus ?thesis by simp
  next
    fix s' assume 3: "(c1, s) \<rightarrow>*t s'" and "(c2, s') \<rightarrow>*c (d', t')"
    hence "(c2, s') \<rightarrow>*t s''" using 2 MtransT.StepT by blast
    thus ?thesis using 3 ** by blast
  qed
qed

text\<open>Direct rules for the multi-step relations\<close>

lemma Seq_MtransC[simp]:
assumes "(c1, s) \<rightarrow>*c (c1', s')"
shows "(c1 ;; c2, s) \<rightarrow>*c (c1' ;; c2, s')"
using assms apply - apply(erule MtransC_induct2) 
apply simp by (metis MtransC_StepC SeqC)

lemma Seq_MtransT_MtransC[simp]:
assumes "(c1, s) \<rightarrow>*t s'"
shows "(c1 ;; c2, s) \<rightarrow>*c (c2, s')"
using assms apply - apply(erule MtransT_invert)
by (metis MtransC_StepC MtransT_invert2 PL.SeqT PL.Seq_MtransC assms) 

lemma ParCL_MtransC[simp]:
assumes "(c1, s) \<rightarrow>*c (c1', s')"
shows "(Par c1 c2, s) \<rightarrow>*c (Par c1' c2, s')"
using assms apply - apply(erule MtransC_induct2) 
apply simp by (metis MtransC_StepC ParCL)

lemma ParCR_MtransC[simp]:
assumes "(c2, s) \<rightarrow>*c (c2', s')"
shows "(Par c1 c2, s) \<rightarrow>*c (Par c1 c2', s')"
using assms apply - apply(erule MtransC_induct2) 
apply simp by (metis MtransC_StepC ParCR)

lemma ParTL_MtransC[simp]:
assumes "(c1, s) \<rightarrow>*t s'"
shows "(Par c1 c2, s) \<rightarrow>*c (c2, s')"
using assms apply - apply(erule MtransT_invert)
by (metis MtransC_StepC MtransT_invert2 PL.ParTL ParCL_MtransC assms) 

lemma ParTR_MtransC[simp]:
assumes "(c2, s) \<rightarrow>*t s'"
shows "(Par c1 c2, s) \<rightarrow>*c (c1, s')"
using assms apply - apply(erule MtransT_invert)
by (metis MtransC_StepC MtransT_invert2 PL.ParTR ParCR_MtransC assms)


subsection\<open>Sublanguages\<close>

(* Commands not containing "while": *)
fun noWhile where 
 "noWhile (Atm atm) = True"
|"noWhile (c1 ;; c2) = (noWhile c1 \<and> noWhile c2)"
|"noWhile (If b c1 c2) = (noWhile c1 \<and> noWhile c2)"
|"noWhile (While b c) = False"
|"noWhile (Par c1 c2) = (noWhile c1 \<and> noWhile c2)"

(* Sequential commands: *)
fun seq where 
 "seq (Atm atm) = True"
|"seq (c1 ;; c2) = (seq c1 \<and> seq c2)"
|"seq (If b c1 c2) = (seq c1 \<and> seq c2)"
|"seq (While b c) = seq c"
|"seq (Par c1 c2) = False"

lemma noWhile_transC:
assumes "noWhile c" and "(c,s) \<rightarrow>c (c',s')"
shows "noWhile c'"
proof-
  have "(c,s) \<rightarrow>c (c',s') \<Longrightarrow> noWhile c \<longrightarrow> noWhile c'"
  by(erule transC_induct, auto)
  thus ?thesis using assms by simp
qed

lemma seq_transC:
assumes "seq c" and "(c,s) \<rightarrow>c (c',s')"
shows "seq c'"
proof-
  have "(c,s) \<rightarrow>c (c',s') \<Longrightarrow> seq c \<longrightarrow> seq c'"
  by(erule transC_induct, auto)
  thus ?thesis using assms by simp
qed

abbreviation wfP_on where 
"wfP_on phi A \<equiv> wfP (\<lambda>a b. a \<in> A \<and> b \<in> A \<and> phi a b)"

(* The number of steps -- makes sense only for the noWhile sublanguage: *)
fun numSt where 
 "numSt (Atm atm) = Suc 0"
|"numSt (c1 ;; c2) = numSt c1 + numSt c2"
|"numSt (If b c1 c2) = 1 + max (numSt c1) (numSt c2)"
|"numSt (Par c1 c2) = numSt c1 + numSt c2"

lemma numSt_gt_0[simp]:
"noWhile c \<Longrightarrow> numSt c > 0"
by(induct c, auto)

lemma numSt_transC:
assumes "noWhile c" and "(c,s) \<rightarrow>c (c',s')"
shows "numSt c' < numSt c"
using assms apply - apply(induct c arbitrary: c') by auto
  
corollary wfP_tranC_noWhile:
"wfP (\<lambda> (c',s') (c,s). noWhile c \<and> (c,s) \<rightarrow>c (c',s'))"
proof-
  let ?K = "{((c',s'),(c,s)). noWhile c \<and> (c,s) \<rightarrow>c (c',s')}"
  have "?K \<le> inv_image {(m,n). m < n} (\<lambda>(c,s). numSt c)" by(auto simp add: numSt_transC)
  hence "wf ?K" using wf_less wf_subset[of _ ?K] by blast
  thus ?thesis unfolding wfP_def
  by (metis CollectD Collect_mem_eq Compl_eq Compl_iff double_complement)
qed

lemma noWhile_MtransT:
assumes "noWhile c"
shows "\<exists> s'. (c,s) \<rightarrow>*t s'"
proof-
  have "noWhile c \<longrightarrow> (\<forall> s. \<exists> s'. (c,s) \<rightarrow>*t s')"
  apply(rule measure_induct[of numSt]) proof clarify
    fix c :: "('test,'atom) com" and s 
    assume IH: "\<forall>c'. numSt c' < numSt c \<longrightarrow> noWhile c' \<longrightarrow> 
                     (\<forall>s'. \<exists>s''. (c', s') \<rightarrow>*t s'')" and c: "noWhile c"
    show "\<exists>s''. (c, s) \<rightarrow>*t s''"
    proof(rule trans_invert[of c s])
      fix c' s' assume cs: "(c, s) \<rightarrow>c (c', s')"
      hence "numSt c' < numSt c" and "noWhile c'" 
      using numSt_transC noWhile_transC c by blast+
      then obtain s'' where "(c', s') \<rightarrow>*t s''" using IH by blast
      hence "(c, s) \<rightarrow>*t s''" using cs by simp
      thus ?thesis by blast
    next
      fix s' assume "(c, s) \<rightarrow>t s'"
      hence "(c, s) \<rightarrow>*t s'" by simp
      thus ?thesis by blast 
    qed 
  qed
  thus ?thesis using assms by blast
qed 

(* Configurations that may diverge: *)

coinductive mayDiverge where 
intro: 
"\<lbrakk>(c,s) \<rightarrow>c (c',s') \<and> mayDiverge c' s'\<rbrakk> 
  \<Longrightarrow> mayDiverge c s"

text\<open>Coinduction for may-diverge :\<close>

lemma mayDiverge_coind[consumes 1, case_names Hyp, induct pred: mayDiverge]:
assumes *: "phi c s" and 
**: "\<And> c s. phi c s \<Longrightarrow> 
            \<exists> c' s'. (c,s) \<rightarrow>c (c',s') \<and> (phi c' s' \<or> mayDiverge c' s')" 
shows "mayDiverge c s"
using * apply(elim mayDiverge.coinduct) using ** by auto 

lemma mayDiverge_raw_coind[consumes 1, case_names Hyp]:
assumes *: "phi c s" and 
**: "\<And> c s. phi c s \<Longrightarrow> 
            \<exists> c' s'. (c,s) \<rightarrow>c (c',s') \<and> phi c' s'" 
shows "mayDiverge c s"
using * apply induct using ** by blast


text\<open>May-diverge versus transition:\<close>

lemma mayDiverge_transC:
assumes "mayDiverge c s"
shows "\<exists> c' s'. (c,s) \<rightarrow>c (c',s') \<and> mayDiverge c' s'"
using assms by (elim mayDiverge.cases) blast

lemma transC_mayDiverge:
assumes "(c,s) \<rightarrow>c (c',s')" and "mayDiverge c' s'"
shows "mayDiverge c s"
using assms by (metis mayDiverge.intro)

lemma mayDiverge_not_transT:
assumes "mayDiverge c s"
shows "\<not> (c,s) \<rightarrow>t s'"
by (metis assms mayDiverge_transC not_transC_transT)

lemma MtransC_mayDiverge:
assumes "(c,s) \<rightarrow>*c (c',s')" and "mayDiverge c' s'"
shows "mayDiverge c s"
using assms transC_mayDiverge by (induct) auto

lemma not_MtransT_mayDiverge: 
assumes "\<And> s'. \<not> (c,s) \<rightarrow>*t s'"
shows "mayDiverge c s"
proof-
  have "\<forall> s'. \<not> (c,s) \<rightarrow>*t s' \<Longrightarrow> ?thesis"
  proof (induct rule: mayDiverge_raw_coind)
    case (Hyp c s)
    hence "\<forall> s''. \<not> (c, s) \<rightarrow>t s''" by (metis transT_MtransT) 
    then obtain c' s' where 1: "(c,s) \<rightarrow>c (c',s')" by (metis trans_invert) 
    hence "\<forall> s''. \<not> (c', s') \<rightarrow>*t s''" using Hyp 1 by (metis transC_MtransT)
    thus ?case using 1 by blast
  qed
  thus ?thesis using assms by simp
qed

lemma not_mayDiverge_Atm[simp]:
"\<not> mayDiverge (Atm atm) s"
by (metis Atm_transC_invert mayDiverge.simps) 

lemma mayDiverge_Seq_L:
assumes "mayDiverge c1 s" 
shows "mayDiverge (c1 ;; c2) s"
proof-
 {fix c
  assume "\<exists> c1 c2. c = c1 ;; c2 \<and> mayDiverge c1 s"
  hence "mayDiverge c s"
  proof (induct rule: mayDiverge_raw_coind)
    case (Hyp c s)
    then obtain c1 c2 where c: "c = c1 ;; c2" 
    and "mayDiverge c1 s" by blast
    then obtain c1' s' where "(c1,s) \<rightarrow>c (c1',s')" 
    and "mayDiverge c1' s'" by (metis mayDiverge_transC)
    thus ?case using c SeqC by metis
  qed
 }
 thus ?thesis using assms by auto
qed

lemma mayDiverge_Seq_R:
assumes c1: "(c1, s) \<rightarrow>*t s'" and c2: "mayDiverge c2 s'"
shows "mayDiverge (c1 ;; c2) s"
proof-
  have "(c1 ;; c2, s) \<rightarrow>*c (c2, s')"
  using c1 by (metis Seq_MtransT_MtransC)
  thus ?thesis by (metis MtransC_mayDiverge c2) 
qed

lemma mayDiverge_If_L: 
assumes "tval tst s" and "mayDiverge c1 s"
shows "mayDiverge (If tst c1 c2) s"
using assms IfTrue transC_mayDiverge by metis

lemma mayDiverge_If_R: 
assumes "\<not> tval tst s" and "mayDiverge c2 s"
shows "mayDiverge (If tst c1 c2) s"
using assms IfFalse transC_mayDiverge by metis

lemma mayDiverge_If: 
assumes "mayDiverge c1 s" and "mayDiverge c2 s"
shows "mayDiverge (If tst c1 c2) s"
using assms mayDiverge_If_L mayDiverge_If_R 
by (cases "tval tst s") auto

lemma mayDiverge_Par_L: 
assumes "mayDiverge c1 s"
shows "mayDiverge (Par c1 c2) s"
proof-
 {fix c
  assume "\<exists> c1 c2. c = Par c1 c2 \<and> mayDiverge c1 s"
  hence "mayDiverge c s"
  proof (induct rule: mayDiverge_raw_coind)
    case (Hyp c s)
    then obtain c1 c2 where c: "c = Par c1 c2" 
    and "mayDiverge c1 s" by blast
    then obtain c1' s' where "(c1,s) \<rightarrow>c (c1',s')" 
    and "mayDiverge c1' s'" by (metis mayDiverge_transC)
    thus ?case using c ParCL by metis
  qed
 }
 thus ?thesis using assms by auto
qed

lemma mayDiverge_Par_R: 
assumes "mayDiverge c2 s"
shows "mayDiverge (Par c1 c2) s"
proof-
 {fix c
  assume "\<exists> c1 c2. c = Par c1 c2 \<and> mayDiverge c2 s"
  hence "mayDiverge c s"
  proof (induct rule: mayDiverge_raw_coind)
    case (Hyp c s)
    then obtain c1 c2 where c: "c = Par c1 c2" 
    and "mayDiverge c2 s" by blast
    then obtain c2' s' where "(c2,s) \<rightarrow>c (c2',s')" 
    and "mayDiverge c2' s'" by (metis mayDiverge_transC)
    thus ?case using c ParCR by metis
  qed
 }
 thus ?thesis using assms by auto
qed

(* Configurations that must terminate: *)
definition mustT where 
"mustT c s \<equiv> \<not> mayDiverge c s"

lemma mustT_transC:
assumes "mustT c s" and "(c,s) \<rightarrow>c (c',s')"
shows "mustT c' s'"
using assms intro unfolding mustT_def by blast

lemma transT_not_mustT:
assumes "(c,s) \<rightarrow>t s'"
shows "mustT c s"
by (metis assms mayDiverge_not_transT mustT_def)

lemma mustT_MtransC:
assumes "mustT c s" and "(c,s) \<rightarrow>*c (c',s')"
shows "mustT c' s'"
proof-
  have "(c,s) \<rightarrow>*c (c',s') \<Longrightarrow> mustT c s \<longrightarrow> mustT c' s'"
  apply(erule MtransC_induct2) using mustT_transC by blast+
  thus ?thesis using assms by blast
qed

lemma mustT_MtransT:
assumes "mustT c s"
shows "\<exists> s'. (c,s) \<rightarrow>*t s'"
using assms not_MtransT_mayDiverge unfolding mustT_def by blast

lemma mustT_Atm[simp]:
"mustT (Atm atm) s"
by (metis not_mayDiverge_Atm mustT_def)

lemma mustT_Seq_L:
assumes "mustT (c1 ;; c2) s"
shows "mustT c1 s"
by (metis PL.mayDiverge_Seq_L assms mustT_def) 

lemma mustT_Seq_R:
assumes "mustT (c1 ;; c2) s" and "(c1, s) \<rightarrow>*t s'" 
shows "mustT c2 s'"
by (metis Seq_MtransT_MtransC mustT_MtransC assms)

lemma mustT_If_L: 
assumes "tval tst s" and "mustT (If tst c1 c2) s" 
shows "mustT c1 s"
by (metis assms trans_IfTrue  mustT_transC)

lemma mustT_If_R: 
assumes "\<not> tval tst s" and "mustT (If tst c1 c2) s" 
shows "mustT c2 s"
by (metis assms trans_IfFalse  mustT_transC)

lemma mustT_If: 
assumes "mustT (If tst c1 c2) s"
shows "mustT c1 s \<or> mustT c2 s"
by (metis assms mustT_If_L mustT_If_R)

lemma mustT_Par_L: 
assumes "mustT (Par c1 c2) s"
shows "mustT c1 s"
by (metis assms mayDiverge_Par_L mustT_def)

lemma mustT_Par_R: 
assumes "mustT (Par c1 c2) s"
shows "mustT c2 s"
by (metis assms mayDiverge_Par_R mustT_def)
 
(* Semantically deterministic commands: *)
definition determOn where
"determOn phi r \<equiv> 
 \<forall> a b b'. phi a \<and> r a b \<and> r a b' \<longrightarrow> b = b'"

lemma determOn_seq_transT:
"determOn (\<lambda>(c,s). seq c) transT"
proof-
  {fix c s s1' s2'
   have "seq c \<and> (c,s) \<rightarrow>t s1' \<and> (c,s) \<rightarrow>t s2' \<longrightarrow> s1' = s2'"
   apply(induct c arbitrary: s1' s2') by auto
  }
  thus ?thesis unfolding determOn_def by fastforce
qed

end (* context PL *)
(*******************************************)


end







