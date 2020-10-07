section \<open>Compositionality of Resumption-Based Noninterference\<close>

theory Compositionality
imports Resumption_Based
begin

(* The results corresponding to the paper's Prop. 2 are marked below with "theorem". *)

context PL_Indis
begin

subsection\<open>Compatibility and discreetness of atoms, tests and choices\<close>

definition compatAtm where
"compatAtm atm \<equiv>
 ALL s t. s \<approx> t \<longrightarrow> aval atm s \<approx> aval atm t"

definition presAtm where
"presAtm atm \<equiv>
 ALL s. s \<approx> aval atm s"

definition compatTst where
"compatTst tst \<equiv>
 ALL s t. s \<approx> t \<longrightarrow> tval tst s = tval tst t"

lemma discrAt_compatAt[simp]:
assumes "presAtm atm"
shows "compatAtm atm"
using assms unfolding compatAtm_def
by (metis presAtm_def indis_sym indis_trans)

definition compatCh where
"compatCh ch \<equiv> \<forall> s t. s \<approx> t \<longrightarrow> cval ch s = cval ch t"

lemma compatCh_cval[simp]:
assumes "compatCh ch" and "s \<approx> t"
shows " cval ch s = cval ch t"
using assms unfolding compatCh_def by auto


subsection\<open>Compositionality of self-isomorphism\<close>

text\<open>Self-Isomorphism versus language constructs:\<close>

lemma siso_Done[simp]:
"siso Done"
proof-
  {fix c :: "('test, 'atom, 'choice) cmd"
   assume "c = Done" hence "siso c"
   apply induct by auto
  }
  thus ?thesis by blast
qed

lemma siso_Atm[simp]:
"siso (Atm atm) = compatAtm atm"
proof-
  {fix c :: "('test, 'atom, 'choice) cmd"
   assume "\<exists> atm. c = Atm atm \<and> compatAtm atm"
   hence "siso c"
   apply induct
   apply (metis compatAtm_def eff_Atm cont_Atm wt_Atm)
   by (metis cont_Atm siso_Done)
  }
  moreover have "siso (Atm atm) \<Longrightarrow> compatAtm atm" unfolding compatAtm_def
  by (metis brn.simps eff_Atm less_Suc_eq mult_less_cancel1 nat_mult_1 siso_cont_indis)
  ultimately show ?thesis by blast
qed

lemma siso_Seq[simp]:
assumes *: "siso c1" and **: "siso c2"
shows "siso (c1 ;; c2)"
proof-
  {fix c :: "('test, 'atom, 'choice) cmd"
   assume "\<exists> c1 c2. c = c1 ;; c2 \<and> siso c1 \<and> siso c2"
   hence "siso c"
   proof induct
     case (Obs c s t i)
     then obtain c1 c2 where "i < brn c1"
     and "c = c1 ;; c2" and "siso c1 \<and> siso c2"
     and "s \<approx> t" by auto
     thus ?case by (cases "finished (cont c1 s i)") auto
   next
     case (Cont c s i)
     then obtain c1 c2 where "i < brn c1" and
     "c = c1 ;; c2 \<and> siso c1 \<and> siso c2" by fastforce
     thus ?case by(cases "finished (cont c1 s i)", auto)
   qed
  }
  thus ?thesis using assms by blast
qed

lemma siso_While[simp]:
assumes "compatTst tst" and "siso c"
shows "siso (While tst c)"
proof-
  {fix c :: "('test, 'atom, 'choice) cmd"
   assume
   "(\<exists> tst d. compatTst tst \<and> c = While tst d \<and> siso d) \<or>
    (\<exists> tst d1 d. compatTst tst \<and> c = d1 ;; (While tst d) \<and> siso d1 \<and> siso d)"
   hence "siso c"
   proof induct
     case (Obs c s t i)
     hence i: " i < brn c" and st: "s \<approx> t" by auto
     from Obs show ?case
     proof(elim disjE exE conjE)
       fix tst d
       assume "compatTst tst" and "c = While tst d" and "siso d"
       thus ?thesis using i st unfolding compatTst_def
       by (cases "tval tst s", simp_all)
     next
       fix tst d1 d
       assume "compatTst tst" and "c = d1 ;; While tst d"
       and "siso d1" and "siso d"
       thus ?thesis
       using i st unfolding compatTst_def
       apply(cases "tval tst s", simp_all)
       by (cases "finished (cont d1 s i)", simp_all)+
     qed
   next
     case (Cont c s i)
     hence i: " i < brn c" by simp
     from Cont show ?case
     proof(elim disjE exE conjE)
       fix tst d
       assume "compatTst tst" and "c = While tst d" and "siso d"
       thus ?thesis by (cases "tval tst s", simp_all)
     next
       fix tst d1 d
       assume "compatTst tst" and "c = d1 ;; While tst d" and "siso d1" and "siso d"
       thus ?thesis using i unfolding compatTst_def
       apply (cases "tval tst s", simp_all)
       by (cases "finished (cont d1 s i)", simp_all)+
     qed
   qed
  }
  thus ?thesis using assms by blast
qed

lemma siso_Ch[simp]:
assumes "compatCh ch"
and *: "siso c1" and **: "siso c2"
shows "siso (Ch ch c1 c2)"
proof-
  {fix c :: "('test, 'atom, 'choice) cmd"
   assume "\<exists> ch c1 c2. compatCh ch \<and> c = Ch ch c1 c2 \<and> siso c1 \<and> siso c2"
   hence "siso c"
   proof induct
     case (Obs c s t i)
     then obtain ch c1 c2 where "i < 2"
     and "compatCh ch" and "c = Ch ch c1 c2" and "siso c1 \<and> siso c2"
     and "s \<approx> t" by fastforce
     thus ?case by (cases i) auto
   next
     case (Cont c s i)
     then obtain ch c1 c2 where "i < 2" and
     "compatCh ch \<and> c = Ch ch c1 c2 \<and> siso c1 \<and> siso c2" by fastforce
     thus ?case by (cases i) auto
   qed
  }
  thus ?thesis using assms by blast
qed

lemma siso_Par[simp]:
assumes "properL cl" and "sisoL cl"
shows "siso (Par cl)"
proof-
  {fix c :: "('test, 'atom, 'choice) cmd"
   assume "\<exists> cl. c = Par cl \<and> properL cl \<and> sisoL cl"
   hence "siso c"
   proof induct
     case (Obs c s t ii)
     then obtain cl where ii: "ii < brnL cl (length cl)"
     and cl: "properL cl"
     and c: "c = Par cl" and siso: "sisoL cl"
     and st: "s \<approx> t" by auto
     let ?N = "length cl"
     from cl ii show ?case
     apply(cases rule: brnL_cases)
     using siso st cl unfolding c by fastforce
   next
     case (Cont c s ii)
     then obtain cl where ii: "ii < brnL cl (length cl)"
     and cl: "properL cl"
     and c: "c = Par cl" and sisoL: "sisoL cl"
     by auto
     from cl ii show ?case
     apply (cases rule: brnL_cases)
     using cl sisoL unfolding c by auto
   qed
  }
  thus ?thesis using assms by blast
qed

lemma siso_ParT[simp]:
assumes "properL cl" and "sisoL cl"
shows "siso (ParT cl)"
proof-
  {fix c :: "('test, 'atom, 'choice) cmd"
   assume "\<exists> cl. c = ParT cl \<and> properL cl \<and> sisoL cl"
   hence "siso c"
   proof induct
     case (Obs c s t ii)
     then obtain cl where ii: "ii < brnL cl (length cl)"
     and cl: "properL cl"
     and c: "c = ParT cl" and siso: "sisoL cl"
     and st: "s \<approx> t" by auto
     let ?N = "length cl"
     from cl ii show ?case proof (cases rule: brnL_cases)
       case (Local n i)
       show ?thesis (is "?eff \<and> ?wt \<and> ?mv")
       proof-
         have eff_mv: "?eff \<and> ?mv" using Local siso cl st unfolding c by force
         have wt: ?wt
         proof(cases "WtFT cl = 1")
           case True
           thus ?thesis unfolding c using Local cl st siso True
           by (cases "n = pickFT cl \<and> i = 0") auto
         next
           case False
           thus ?thesis unfolding c using Local cl st siso False
           by (cases "finished (cl!n)") auto
         qed
         from eff_mv wt show ?thesis by simp
       qed
     qed
   next
     case (Cont c s ii)
     then obtain cl where ii: "ii < brnL cl (length cl)"
     and cl: "properL cl"
     and c: "c = ParT cl" and siso: "sisoL cl"
     by auto
     from cl ii show ?case apply (cases rule: brnL_cases)
     using siso cl unfolding c by force
   qed
  }
  thus ?thesis using assms by blast
qed

text\<open>Self-isomorphism implies strong bisimilarity:\<close>

lemma bij_betw_emp[simp]:
"bij_betw f {} {}"
unfolding bij_betw_def by auto

lemma part_full[simp]:
"part I {I}"
unfolding part_def by auto

definition singlPart where
"singlPart I \<equiv> {{i} | i . i \<in> I}"

lemma part_singlPart[simp]:
"part I (singlPart I)"
unfolding part_def singlPart_def by auto

lemma singlPart_inj_on[simp]:
"inj_on (image f) (singlPart I) = inj_on f I"
unfolding inj_on_def singlPart_def
apply auto
by (metis image_insert insertI1 insert_absorb insert_code singleton_inject)

lemma singlPart_surj[simp]:
"(image f) ` (singlPart I) = (singlPart J) \<longleftrightarrow> f ` I = J"
unfolding inj_on_def singlPart_def apply auto by blast

lemma singlPart_bij_betw[simp]:
"bij_betw (image f) (singlPart I) (singlPart J) = bij_betw f I J"
unfolding bij_betw_def by auto

lemma singlPart_finite1:
assumes "finite (singlPart I)"
shows "finite (I::'a set)"
proof-
  define u where "u i = {i}" for i :: 'a
  have "u ` I \<subseteq> singlPart I" unfolding u_def singlPart_def by auto
  moreover have "inj_on u I" unfolding u_def inj_on_def by auto
  ultimately show ?thesis using assms
  by (metis \<open>inj_on u I\<close> finite_imageD infinite_super)
qed

lemma singlPart_finite[simp]:
"finite (singlPart I) = finite I"
 using singlPart_finite1[of I] unfolding singlPart_def by auto

lemma emp_notIn_singlPart[simp]:
"{} \<notin> singlPart I"
unfolding singlPart_def by auto

lemma Sbis_coinduct[consumes 1, case_names step, coinduct set]:
  "R c d \<Longrightarrow>
    (\<And>c d s t. R c d \<Longrightarrow> s \<approx> t \<Longrightarrow>
      \<exists>P F. mC_C_part c d P F \<and> inj_on F P \<and> mC_C_wt c d s t P F \<and>
        (\<forall>I\<in>P. \<forall>i\<in>I. \<forall>j\<in>F I. 
                eff c s i \<approx> eff d t j \<and> (R (cont c s i) (cont d t j) \<or> (cont c s i, cont d t j) \<in> Sbis)))
  \<Longrightarrow> (c, d) \<in> Sbis"
  using Sbis_coind[of "{(x, y). R x y}"]
  unfolding Sretr_def matchC_C_def mC_C_def mC_C_eff_cont_def
  apply (simp add: subset_eq Ball_def )
  apply metis
  done

lemma siso_Sbis[simp]: "siso c \<Longrightarrow> c \<approx>s c"
proof (coinduction arbitrary: c)
  case (step s t c) with siso_cont_indis[of c s t] part_singlPart[of "{..<brn c}"] show ?case
    by (intro exI[of _ "singlPart {..< brn c}"] exI[of _ id])
       (auto simp add: mC_C_part_def mC_C_wt_def singlPart_def)
qed

subsection \<open>Discreetness versus language constructs:\<close>

lemma discr_Done[simp]: "discr Done"
  by coinduction auto

lemma discr_Atm_presAtm[simp]: "discr (Atm atm) = presAtm atm"
proof-
  have "presAtm atm \<Longrightarrow> discr (Atm atm)"
    by (coinduction arbitrary: atm) (auto simp: presAtm_def)
  moreover have "discr (Atm atm) \<Longrightarrow> presAtm atm"
    unfolding presAtm_def
    by (metis One_nat_def brn.simps(2) discr.simps eff_Atm lessI)
  ultimately show ?thesis by blast
qed

lemma discr_Seq[simp]:
  "discr c1 \<Longrightarrow> discr c2 \<Longrightarrow> discr (c1 ;; c2)"
  by (coinduction arbitrary: c1 c2)
     (simp, metis cont_Seq_finished discr_cont cont_Seq_notFinished)

lemma discr_While[simp]: assumes "discr c" shows "discr (While tst c)"
proof-
  {fix c :: "('test, 'atom, 'choice) cmd"
   assume
   "(\<exists> tst d. c = While tst d \<and> discr d) \<or>
    (\<exists> tst d1 d. c = d1 ;; (While tst d) \<and> discr d1 \<and> discr d)"
   hence "discr c"
   apply induct apply safe
   apply (metis eff_While indis_refl)
   apply (metis cont_While_False discr_Done cont_While_True)
   apply (metis eff_Seq discr.simps brn.simps)
   by (metis cont_Seq_finished discr.simps cont_Seq_notFinished brn.simps)
  }
  thus ?thesis using assms by blast
qed

lemma discr_Ch[simp]: "discr c1 \<Longrightarrow> discr c2 \<Longrightarrow> discr (Ch ch c1 c2)"
  by coinduction (simp, metis indis_refl less_2_cases cont_Ch_L cont_Ch_R)

lemma discr_Par[simp]: "properL cl \<Longrightarrow> discrL cl \<Longrightarrow> discr (Par cl)"
proof (coinduction arbitrary: cl, clarsimp)
  fix cl ii s
  assume *: "properL cl" "ii < brnL cl (length cl)" and "discrL cl"
  from * show "s \<approx> eff (Par cl) s ii \<and>
    ((\<exists>cl'. cont (Par cl) s ii = Par cl' \<and> properL cl' \<and> discrL cl') \<or> discr (cont (Par cl) s ii))"
  proof (cases rule: brnL_cases)
    case (Local n i)
    with \<open>discrL cl\<close> have "s \<approx> eff (cl ! n) s i" by simp
    thus ?thesis
      using Local \<open>discrL cl\<close> \<open>properL cl\<close> by auto
  qed
qed

lemma discr_ParT[simp]: "properL cl \<Longrightarrow> discrL cl \<Longrightarrow> discr (ParT cl)"
proof (coinduction arbitrary: cl, clarsimp)
  fix p cl s ii assume "properL cl" "ii < brnL cl (length cl)" "discrL cl"
  then show "s \<approx> eff (ParT cl) s ii \<and>
    ((\<exists>cl'. cont (ParT cl) s ii = ParT cl' \<and> properL cl' \<and> discrL cl') \<or> discr (cont (ParT cl) s ii))"
  proof (cases rule: brnL_cases)
    case (Local n i)
    have "s \<approx> eff (cl ! n) s i" using Local \<open>discrL cl\<close> by simp
    thus ?thesis using Local \<open>discrL cl\<close> \<open>properL cl\<close> by simp
  qed
qed

lemma discr_finished[simp]: "proper c \<Longrightarrow> finished c \<Longrightarrow> discr c"
  by (induct c rule: proper_induct) (auto simp: discrL_intro)

subsection\<open>Strong bisimilarity versus language constructs\<close>

lemma Sbis_pres_discr_L:
  "c \<approx>s d \<Longrightarrow> discr d \<Longrightarrow> discr c"
proof (coinduction arbitrary: d c, clarsimp)
  fix c d s i
  assume d: "c \<approx>s d" "discr d" and i: "i < brn c" 
  then obtain P F where
    match: "mC_C Sbis c d s s P F"
    using Sbis_mC_C[of c d s s] by blast
  hence "\<Union>P = {..<brn c}"
    using i unfolding mC_C_def mC_C_part_def part_def by simp
  then obtain I where I: "I \<in> P" and i: "i \<in> I" using i by auto
  obtain j where j: "j \<in> F I"
    using match I unfolding mC_C_def mC_C_part_def by blast
  hence "j < brn d" using I match
    unfolding mC_C_def mC_C_part_def part_def apply simp by blast
  hence md: "discr (cont d s j)" and s: "s \<approx> eff d s j"
    using d discr_cont[of d j s] discr_eff_indis[of d j s] by auto
  have "eff c s i \<approx> eff d s j" and md2: "cont c s i \<approx>s cont d s j"
    using I i j match unfolding mC_C_def mC_C_eff_cont_def by auto
  hence "s \<approx> eff c s i" using s indis_sym indis_trans by blast
  thus "s \<approx> eff c s i \<and> ((\<exists>d. cont c s i \<approx>s d \<and> discr d) \<or> discr (cont c s i))"
    using md md2 by blast
qed

lemma Sbis_pres_discr_R:
assumes "discr c" and "c \<approx>s d"
shows "discr d"
using assms Sbis_pres_discr_L Sbis_sym by blast

lemma Sbis_finished_discr_L:
assumes "c \<approx>s d" and "proper d" and "finished d"
shows "discr c"
using assms Sbis_pres_discr_L by auto

lemma Sbis_finished_discr_R:
assumes "proper c" and "finished c" and "c \<approx>s d"
shows "discr d"
using assms Sbis_pres_discr_R[of c d] by auto

(*  *)

definition thetaSD where
"thetaSD \<equiv> {(c, d) | c d . proper c \<and> proper d \<and> discr c \<and> discr d}"

lemma thetaSD_Sretr:
"thetaSD \<subseteq> Sretr thetaSD"
unfolding Sretr_def matchC_C_def proof safe
  fix c d s t
  assume c_d: "(c, d) \<in> thetaSD" and st: "s \<approx> t"
  hence p: "proper c \<and> proper d" unfolding thetaSD_def by auto
  let ?P = "{{..<brn c}}"
  let ?F = "% I. {..< brn d}"
  have 0: "{..<brn c} \<noteq> {}"  "{..<brn d} \<noteq> {}"
  using p int_emp brn_gt_0 by blast+
  show "\<exists>P F. mC_C thetaSD c d s t P F"
  apply -
  apply(rule exI[of _ ?P]) apply(rule exI[of _ ?F])
  unfolding mC_C_def proof(intro conjI)
    show "mC_C_part c d ?P ?F"
    unfolding mC_C_part_def using 0 unfolding part_def by auto
  next
    show "inj_on ?F ?P" unfolding inj_on_def by simp
  next
    show "mC_C_wt c d s t ?P ?F" unfolding mC_C_wt_def using p by auto
  next
    show "mC_C_eff_cont thetaSD c d s t ?P ?F"
    unfolding mC_C_eff_cont_def proof clarify
      fix I i j
      assume i: "i < brn c" and j: "j < brn d"
      hence "s \<approx> eff c s i" using c_d unfolding thetaSD_def by simp
      moreover have "t \<approx> eff d t j" using i j c_d unfolding thetaSD_def by simp
      ultimately have "eff c s i \<approx> eff d t j" using st indis_sym indis_trans by blast
      thus "eff c s i \<approx> eff d t j \<and> (cont c s i, cont d t j) \<in> thetaSD"
      using c_d i j unfolding thetaSD_def by auto
    qed
  qed
qed

lemma thetaSD_Sbis:
"thetaSD \<subseteq> Sbis"
using Sbis_raw_coind thetaSD_Sretr by blast

theorem discr_Sbis[simp]:
assumes "proper c" and "proper d" and "discr c" and "discr d"
shows "c \<approx>s d"
using assms thetaSD_Sbis unfolding thetaSD_def by auto

(* Done: *)

definition thetaSDone where
"thetaSDone \<equiv> {(Done, Done)}"

lemma thetaSDone_Sretr:
"thetaSDone \<subseteq> Sretr thetaSDone"
unfolding Sretr_def matchC_C_def thetaSDone_def proof safe
  fix s t assume st: "s \<approx> t"
  let ?P = "{{0}}" let ?F = id
  show "\<exists>P F. mC_C {(Done, Done)} Done Done s t P F"
  apply(intro exI[of _ ?P]) apply(intro exI[of _ ?F])
  unfolding m_defsAll part_def using st by auto
qed

lemma thetaSDone_Sbis:
"thetaSDone \<subseteq> Sbis"
using Sbis_raw_coind thetaSDone_Sretr by blast

theorem Done_Sbis[simp]:
"Done \<approx>s Done"
using thetaSDone_Sbis unfolding thetaSDone_def by auto

(* Atm: *)
definition thetaSAtm where
"thetaSAtm atm \<equiv>
 {(Atm atm, Atm atm), (Done, Done)}"

lemma thetaSAtm_Sretr:
assumes "compatAtm atm"
shows "thetaSAtm atm \<subseteq> Sretr (thetaSAtm atm)"
unfolding Sretr_def matchC_C_def thetaSAtm_def proof safe
  fix s t assume st: "s \<approx> t"
  let ?P = "{{0}}" let ?F = id
  show "\<exists>P F. mC_C {(Atm atm, Atm atm), (Done, Done)} Done Done s t P F"
  apply(intro exI[of _ ?P]) apply(intro exI[of _ ?F])
  unfolding m_defsAll part_def using st by auto
next
  fix s t assume st: "s \<approx> t"
  let ?P = "{{0}}" let ?F = id
  show "\<exists>P F. mC_C {(Atm atm, Atm atm), (Done, Done)} (Atm atm) (Atm atm) s t P F"
  apply(intro exI[of _ ?P]) apply(intro exI[of _ ?F])
  unfolding m_defsAll part_def using st assms unfolding compatAtm_def by auto
qed

lemma thetaSAtm_Sbis:
assumes "compatAtm atm"
shows "thetaSAtm atm \<subseteq> Sbis"
using assms Sbis_raw_coind thetaSAtm_Sretr by blast

theorem Atm_Sbis[simp]:
assumes "compatAtm atm"
shows "Atm atm \<approx>s Atm atm"
using assms thetaSAtm_Sbis unfolding thetaSAtm_def by auto

(* Seq *)
definition thetaSSeqI where
"thetaSSeqI \<equiv>
 {(e ;; c, e ;; d) | e c d . siso e \<and> c \<approx>s d}"

lemma thetaSSeqI_Sretr:
"thetaSSeqI \<subseteq> Sretr (thetaSSeqI Un Sbis)"
unfolding Sretr_def matchC_C_def proof safe
  fix c d s t
  assume c_d: "(c, d) \<in> thetaSSeqI" and st: "s \<approx> t"
  then obtain e c1 d1 where e: "siso e" and c1d1: "c1 \<approx>s d1"
  and c: "c = e ;; c1" and d: "d = e ;; d1"
  unfolding thetaSSeqI_def by auto
  let ?P = "{{i} | i . i < brn e}"
  let ?F = "%I. I"
  show "\<exists>P F. mC_C (thetaSSeqI Un Sbis) c d s t P F"
  apply(rule exI[of _ ?P]) apply(rule exI[of _ ?F])
  unfolding mC_C_def proof (intro conjI)
    show "mC_C_part c d ?P ?F"
    unfolding mC_C_part_def proof (intro conjI)
      show "part {..<brn c} ?P"
      unfolding part_def proof safe
        fix i assume "i < brn c"
        thus "i \<in> \<Union> ?P" using c e st siso_cont_indis[of e s t] by auto
      qed (unfold c, simp)
      (*  *)
      thus "part {..<brn d} (?F ` ?P)" unfolding c d by auto
    qed auto
  next
    show "mC_C_eff_cont (thetaSSeqI Un Sbis) c d s t ?P ?F"
    unfolding mC_C_eff_cont_def proof (intro impI allI, elim conjE)
      fix I i j
      assume I: "I \<in> ?P" and i: "i \<in> I" and j: "j \<in> I"
      show "eff c s i \<approx> eff d t j \<and> (cont c s i, cont d t j) \<in> thetaSSeqI \<union> Sbis"
      proof(cases "I = {}")
        case True thus ?thesis using i by simp
      next
        case False
        then obtain i' where "j \<in> ?F {i'}" and "i' < brn e"
        using I j by auto
        thus ?thesis
        using st c_d e i j I unfolding c d thetaSSeqI_def
        by (cases "finished (cont e s i')") auto
      qed
    qed
  qed (insert st c_d c, unfold m_defsAll thetaSSeqI_def part_def, auto)
qed

lemma thetaSSeqI_Sbis:
"thetaSSeqI \<subseteq> Sbis"
using Sbis_coind thetaSSeqI_Sretr by blast

theorem Seq_siso_Sbis[simp]:
assumes "siso e" and "c2 \<approx>s d2"
shows "e ;; c2 \<approx>s e ;; d2"
using assms thetaSSeqI_Sbis unfolding thetaSSeqI_def by auto

(*  *)
definition thetaSSeqD where
"thetaSSeqD \<equiv>
 {(c1 ;; c2, d1 ;; d2) |
     c1 c2 d1 d2.
        proper c1 \<and> proper d1 \<and> proper c2 \<and> proper d2 \<and>
        discr c2 \<and> discr d2 \<and>
        c1 \<approx>s d1}"

lemma thetaSSeqD_Sretr:
"thetaSSeqD \<subseteq> Sretr (thetaSSeqD Un Sbis)"
unfolding Sretr_def matchC_C_def proof safe
  fix c d s t
  assume c_d: "(c, d) \<in> thetaSSeqD" and st: "s \<approx> t"
  then obtain c1 c2 d1 d2 where
  c1d1: "proper c1" "proper d1" "c1 \<approx>s d1" and
  c2d2: "proper c2" "proper d2" "discr c2" "discr d2"
  and c: "c = c1 ;; c2" and d: "d = d1 ;; d2"
  unfolding thetaSSeqD_def by auto
  from c1d1 st obtain P F
  where match: "mC_C Sbis c1 d1 s t P F"
  using Sbis_mC_C by blast
  have P: "\<Union>P = {..<brn c1}" and FP: "\<Union> (F ` P) = {..<brn d1}"
  using match unfolding mC_C_def mC_C_part_def part_def by metis+
  show "\<exists>P F. mC_C (thetaSSeqD Un Sbis) c d s t P F"
  apply(rule exI[of _ P]) apply(rule exI[of _ F])
  unfolding mC_C_def proof (intro conjI)
    show "mC_C_eff_cont (thetaSSeqD \<union> Sbis) c d s t P F"
    unfolding mC_C_eff_cont_def proof(intro allI impI, elim conjE)
      fix i j I assume I : "I \<in> P" and i: "i \<in> I" and j: "j \<in> F I"
      let ?c1' = "cont c1 s i"  let ?d1' = "cont d1 t j"
      let ?s' = "eff c1 s i"  let ?t' = "eff d1 t j"
      have "i < brn c1" using i I P by blast note i = this i
      have "j < brn d1" using j I FP by blast note j = this j
      have c1'd1': "?c1' \<approx>s ?d1'"
      "proper ?c1'" "proper ?d1'"
      using c1d1 i j I match unfolding c mC_C_def mC_C_eff_cont_def by auto
      show "eff c s i \<approx> eff d t j \<and> (cont c s i, cont d t j) \<in> thetaSSeqD \<union> Sbis"
      (is "?eff \<and> ?cont") proof
        show ?eff using match I i j unfolding c d m_defsAll by simp
      next
        show ?cont
        proof(cases "finished ?c1'")
          case True note c1' = True
          hence csi: "cont c s i = c2" using i match unfolding c m_defsAll by simp
          show ?thesis
          proof(cases "finished ?d1'")
            case True
            hence "cont d t j = d2" using j match unfolding d m_defsAll by simp
            thus ?thesis using csi c2d2 by simp
          next
            case False
            hence dtj: "cont d t j = ?d1' ;; d2"
            using j match unfolding d m_defsAll by simp
            have "discr ?d1'" using c1'd1'  c1' Sbis_finished_discr_R by blast
            thus ?thesis using c1'd1' c2d2 unfolding csi dtj by simp
          qed
        next
          case False note Done_c = False
          hence csi: "cont c s i = ?c1' ;; c2"
          using i match unfolding c m_defsAll by simp
          show ?thesis
          proof(cases "finished (cont d1 t j)")
            case True note d1' = True
            hence dtj: "cont d t j = d2" using j match unfolding d m_defsAll by simp
            have "discr ?c1'" using c1'd1'  d1' Sbis_finished_discr_L by blast
            thus ?thesis using c1'd1' c2d2 unfolding csi dtj by simp
          next
            case False
            hence dtj: "cont d t j = ?d1' ;; d2" using j match unfolding d m_defsAll by simp
            thus ?thesis unfolding csi dtj thetaSSeqD_def
            using c1'd1' c2d2 by blast
          qed
        qed
      qed
    qed
  qed(insert match, unfold m_defsAll c d, auto)
qed

lemma thetaSSeqD_Sbis:
"thetaSSeqD \<subseteq> Sbis"
using Sbis_coind thetaSSeqD_Sretr by blast

theorem Seq_Sbis[simp]:
assumes "proper c1" and "proper d1" and "proper c2" and "proper d2"
and "c1 \<approx>s d1" and "discr c2" and "discr d2"
shows "c1 ;; c2 \<approx>s d1 ;; d2"
using assms thetaSSeqD_Sbis unfolding thetaSSeqD_def by auto

(* Note: no compositionality w.r.t. while loop. *)

(* Ch *)
definition thetaSCh where
"thetaSCh ch c1 c2 d1 d2 \<equiv> {(Ch ch c1 c2, Ch ch d1 d2)}"

lemma thetaSCh_Sretr:
assumes "compatCh ch" and "c1 \<approx>s d1" and "c2 \<approx>s d2"
shows "thetaSCh ch c1 c2 d1 d2 \<subseteq>
       Sretr (thetaSCh ch c1 c2 d1 d2 \<union> Sbis)"
(is "?th \<subseteq> Sretr (?th \<union> Sbis)")
unfolding Sretr_def matchC_C_def proof safe
  fix c d s t
  assume c_d: "(c, d) \<in> ?th" and st: "s \<approx> t"
  hence c: "c = Ch ch c1 c2" "brn c = 2"
  and d: "d = Ch ch d1 d2" "brn d = 2"
  unfolding thetaSCh_def by auto
  let ?P = "{{0}, {1}}"
  let ?F = "%I. I"
  show "\<exists>P F. mC_C (?th Un Sbis) c d s t P F"
  apply(rule exI[of _ ?P]) apply(rule exI[of _ ?F])
  using assms st c_d c unfolding m_defsAll thetaSCh_def part_def by auto
qed

lemma thetaSCh_Sbis:
assumes "compatCh ch" and "c1 \<approx>s d1" and "c2 \<approx>s d2"
shows "thetaSCh ch c1 c2 d1 d2 \<subseteq> Sbis"
using Sbis_coind thetaSCh_Sretr[OF assms] by blast

theorem Ch_siso_Sbis[simp]:
assumes "compatCh ch" and "c1 \<approx>s d1" and "c2 \<approx>s d2"
shows "Ch ch c1 c2 \<approx>s Ch ch d1 d2"
using thetaSCh_Sbis[OF assms] unfolding thetaSCh_def by auto

(* Par: *)

definition shift where
"shift cl n \<equiv> image (%i. brnL cl n + i)"

definition "back" where
"back cl n \<equiv> image (% ii. ii - brnL cl n)"

lemma emp_shift[simp]:
"shift cl n I = {} \<longleftrightarrow> I = {}"
unfolding shift_def by auto

lemma emp_shift_rev[simp]:
"{} = shift cl n I \<longleftrightarrow> I = {}"
unfolding shift_def by auto

lemma emp_back[simp]:
"back cl n II = {} \<longleftrightarrow> II = {}"
unfolding back_def by force

lemma emp_back_rev[simp]:
"{} = back cl n II \<longleftrightarrow> II = {}"
unfolding back_def by force

lemma in_shift[simp]:
"brnL cl n + i \<in> shift cl n I \<longleftrightarrow> i \<in> I"
unfolding shift_def by auto

lemma in_back[simp]:
"ii \<in> II \<Longrightarrow> ii - brnL cl n \<in> back cl n II"
unfolding back_def by auto

lemma in_back2[simp]:
assumes "ii > brnL cl n" and "II \<subseteq> {brnL cl n ..<+ brn (cl!n)}"
shows "ii - brnL cl n \<in> back cl n II \<longleftrightarrow> ii \<in> II" (is "?L \<longleftrightarrow> ?R")
using assms unfolding back_def by force

lemma shift[simp]:
assumes "I \<subseteq> {..< brn (cl!n)}"
shows "shift cl n I \<subseteq> {brnL cl n ..<+ brn (cl!n)}"
using assms unfolding shift_def by auto

lemma shift2[simp]:
assumes "I \<subseteq> {..< brn (cl!n)}"
and "ii \<in> shift cl n I"
shows "brnL cl n \<le> ii \<and> ii < brnL cl n + brn (cl!n)"
using assms unfolding shift_def by auto

lemma shift3[simp]:
assumes n: "n < length cl" and I: "I \<subseteq> {..< brn (cl!n)}"
and ii: "ii \<in> shift cl n I"
shows "ii < brnL cl (length cl)"
proof-
  have "ii < brnL cl n + brn (cl!n)" using I ii by simp
  also have "... \<le> brnL cl (length cl)" using n
  by (metis brnL_Suc brnL_mono Suc_leI)
  finally show ?thesis .
qed

lemma "back"[simp]:
assumes "II \<subseteq> {brnL cl n ..<+ brn (cl!n)}"
shows "back cl n II \<subseteq> {..< brn (cl!n)}"
using assms unfolding back_def by force

lemma back2[simp]:
assumes "II \<subseteq> {brnL cl n ..<+ brn (cl!n)}"
and "i \<in> back cl n II"
shows "i < brn (cl!n)"
using assms unfolding back_def by force

lemma shift_inj[simp]:
"shift cl n I1 = shift cl n I2 \<longleftrightarrow> I1 = I2"
unfolding shift_def by force

lemma shift_mono[simp]:
"shift cl n I1 \<subseteq> shift cl n I2 \<longleftrightarrow> I1 \<subseteq> I2"
unfolding shift_def by auto

lemma shift_Int[simp]:
"shift cl n I1 \<inter> shift cl n I2 = {} \<longleftrightarrow> I1 \<inter> I2 = {}"
unfolding shift_def by force

lemma inj_shift: "inj (shift cl n)"
unfolding inj_on_def by simp

lemma inj_on_shift: "inj_on (shift cl n) K"
using inj_shift unfolding inj_on_def by simp

lemma back_shift[simp]:
"back cl n (shift cl n I) = I"
unfolding back_def shift_def by force

lemma shift_back[simp]:
assumes "II \<subseteq> {brnL cl n ..<+ brn (cl!n)}"
shows "shift cl n (back cl n II) = II"
using assms unfolding shift_def back_def atLeastLessThan_def by force

lemma back_inj[simp]:
assumes II1: "II1 \<subseteq> {brnL cl n ..<+ brn (cl!n)}"
and II2: "II2 \<subseteq> {brnL cl n ..<+ brn (cl!n)}"
shows "back cl n II1 = back cl n II2 \<longleftrightarrow> II1 = II2" (is "?L = ?R \<longleftrightarrow> II1 = II2")
proof
  have "II1 = shift cl n ?L" using II1 by simp
  also assume "?L = ?R"
  also have "shift cl n ?R = II2" using II2 by simp
  finally show "II1 = II2" .
qed auto

lemma back_mono[simp]:
assumes "II1 \<subseteq> {brnL cl n ..<+ brn (cl!n)}"
and "II2 \<subseteq> {brnL cl n ..< brnL cl n + brn (cl!n)}"
shows "back cl n II1 \<subseteq> back cl n II2 \<longleftrightarrow> II1 \<subseteq> II2"
(is "?L \<subseteq> ?R \<longleftrightarrow> II1 \<subseteq> II2")
proof-
  have "?L \<subseteq> ?R \<longleftrightarrow> shift cl n ?L \<subseteq> shift cl n ?R" by simp
  also have "... \<longleftrightarrow> II1 \<subseteq> II2" using assms by simp
  finally show ?thesis .
qed

lemma back_Int[simp]:
assumes "II1 \<subseteq> {brnL cl n ..<+ brn (cl!n)}"
and "II2 \<subseteq> {brnL cl n ..< brnL cl n + brn (cl!n)}"
shows "back cl n II1 \<inter> back cl n II2 = {} \<longleftrightarrow> II1 \<inter> II2 = {}"
(is "?L \<inter> ?R = {} \<longleftrightarrow> II1 \<inter> II2 = {}")
proof-
  have "?L \<inter> ?R = {} \<longleftrightarrow> shift cl n ?L \<inter> shift cl n ?R = {}" by simp
  also have "... \<longleftrightarrow> II1 \<inter> II2 = {}" using assms by simp
  finally show ?thesis .
qed

lemma inj_on_back:
"inj_on (back cl n) (Pow {brnL cl n ..<+ brn (cl!n)})"
unfolding inj_on_def by simp

lemma shift_surj:
assumes "II \<subseteq> {brnL cl n ..<+ brn (cl!n)}"
shows "\<exists> I. I \<subseteq> {..< brn (cl!n)} \<and> shift cl n I = II"
apply(intro exI[of _ "back cl n II"]) using assms by simp

lemma back_surj:
assumes "I \<subseteq> {..< brn (cl!n)}"
shows "\<exists> II. II \<subseteq> {brnL cl n ..<+ brn (cl!n)} \<and> back cl n II = I"
apply(intro exI[of _ "shift cl n I"]) using assms by simp

lemma shift_part[simp]:
assumes "part {..< brn (cl!n)} P"
shows "part {brnL cl n ..<+ brn (cl!n)} (shift cl n ` P)"
unfolding part_def proof(intro conjI allI impI)
  show "\<Union> (shift cl n ` P) = {brnL cl n ..<+ brn (cl!n)}"
  proof safe
    fix ii I assume ii: "ii \<in> shift cl n I" and "I \<in> P"
    hence "I \<subseteq> {..< brn (cl!n)}" using assms unfolding part_def by blast
    thus "ii \<in> {brnL cl n ..<+ brn (cl!n)}" using ii by simp
  next
    fix ii assume ii_in: "ii \<in> {brnL cl n..<+brn (cl ! n)}"
    define i where "i = ii - brnL cl n"
    have ii: "ii = brnL cl n + i" unfolding i_def using ii_in by force
    have "i \<in> {..< brn (cl!n)}" unfolding i_def using ii_in by auto
    then obtain I where i: "i \<in> I" and I: "I \<in> P"
    using assms unfolding part_def by blast
    thus "ii \<in> \<Union> (shift cl n ` P)" unfolding ii by force
  qed
qed(insert assms, unfold part_def, force)

lemma part_brn_disj1:
assumes P: "\<And> n. n < length cl \<Longrightarrow> part {..< brn (cl!n)} (P n)"
and n1: "n1 < length cl" and n2: "n2 < length cl"
and II1: "II1 \<in> shift cl n1 ` (P n1)" and II2: "II2 \<in> shift cl n2 ` (P n2)" and d: "n1 \<noteq> n2"
shows "II1 \<inter> II2 = {}"
proof-
  let ?N = "length cl"
  obtain I1 I2 where I1: "I1 \<in> P n1" and I2: "I2 \<in> P n2"
  and II1: "II1 = shift cl n1 I1" and II2: "II2 = shift cl n2 I2"
  using II1 II2 by auto
  have "I1 \<subseteq> {..< brn (cl!n1)}" and "I2 \<subseteq> {..< brn (cl!n2)}"
  using n1 I1 n2 I2 P unfolding part_def by blast+
  hence "II1 \<subseteq> {brnL cl n1 ..<+ brn (cl!n1)}" and "II2 \<subseteq> {brnL cl n2 ..<+ brn (cl!n2)}"
  unfolding II1 II2 by auto
  thus ?thesis using n1 n2 d brnL_Int by blast
qed

lemma part_brn_disj2:
assumes P: "\<And> n. n < length cl \<Longrightarrow> part {..< brn (cl!n)} (P n) \<and> {} \<notin> P n"
and n1: "n1 < length cl" and n2: "n2 < length cl" and d: "n1 \<noteq> n2"
shows "shift cl n1 ` (P n1) \<inter> shift cl n2 ` (P n2) = {}" (is "?L \<inter> ?R = {}")
proof-
  {fix II assume II: "II \<in> ?L \<inter> ?R"
   hence "II = {}" using part_brn_disj1[of cl P n1 n2 II II] assms by blast
   hence "{} \<in> ?L" using II by blast
   then obtain I where I: "I \<in> P n1" and II: "{} = shift cl n1 I" by blast
   hence "I = {}" by simp
   hence False using n1 P I by blast
  }
  thus ?thesis by blast
qed

lemma part_brn_disj3:
assumes P: "\<And> n. n < length cl \<Longrightarrow> part {..< brn (cl!n)} (P n)"
and n1: "n1 < length cl" and n2: "n2 < length cl"
and I1: "I1 \<in> P n1" and I2: "I2 \<in> P n2" and d: "n1 \<noteq> n2"
shows "shift cl n1 I1 \<inter> shift cl n2 I2 = {}"
apply(rule part_brn_disj1)
using assms by auto

lemma sum_wt_Par_sub_shift[simp]:
assumes cl: "properL cl" and n: "n < length cl" and
I: "I \<subseteq> {..< brn (cl ! n)}"
shows
"sum (wt (Par cl) s) (shift cl n I) =
 1 / (length cl) * sum (wt (cl ! n) s) I"
using assms sum_wt_Par_sub unfolding shift_def by simp

lemma sum_wt_ParT_sub_WtFT_pickFT_0_shift[simp]:
assumes cl: "properL cl" and nf: "WtFT cl = 1"
and I: "I \<subseteq> {..< brn (cl ! (pickFT cl))}" "0 \<in> I"
shows
"sum (wt (ParT cl) s) (shift cl (pickFT cl) I) = 1"
using assms sum_wt_ParT_sub_WtFT_pickFT_0
unfolding shift_def by simp

lemma sum_wt_ParT_sub_WtFT_notPickFT_0_shift[simp]:
assumes cl: "properL cl" and nf: "WtFT cl = 1" and n: "n < length cl"
and I: "I \<subseteq> {..< brn (cl ! n)}" and nI: "n = pickFT cl \<longrightarrow> 0 \<notin> I"
shows "sum (wt (ParT cl) s) (shift cl n I) = 0"
using assms sum_wt_ParT_sub_WtFT_notPickFT_0 unfolding shift_def by simp

lemma sum_wt_ParT_sub_notWtFT_finished_shift[simp]:
assumes cl: "properL cl" and nf: "WtFT cl \<noteq> 1" and n: "n < length cl" and cln: "finished (cl!n)"
and I: "I \<subseteq> {..< brn (cl ! n)}"
shows "sum (wt (ParT cl) s) (shift cl n I) = 0"
using assms sum_wt_ParT_sub_notWtFT_finished
unfolding shift_def by simp

lemma sum_wt_ParT_sub_notWtFT_notFinished_shift[simp]:
assumes cl: "properL cl" and nf: "WtFT cl \<noteq> 1"
and n: "n < length cl" and cln: "\<not> finished (cl!n)"
and I: "I \<subseteq> {..< brn (cl ! n)}"
shows
"sum (wt (ParT cl) s) (shift cl n I) =
 (1 / (length cl)) / (1 - WtFT cl) * sum (wt (cl ! n) s) I"
using assms sum_wt_ParT_sub_notWtFT_notFinished
unfolding shift_def by simp

(*  *)

definition UNpart where
"UNpart cl P \<equiv> \<Union> n < length cl. shift cl n ` (P n)"

lemma UNpart_cases[elim, consumes 1, case_names Local]:
assumes "II \<in> UNpart cl P" and
"\<And> n I. \<lbrakk>n < length cl; I \<in> P n; II = shift cl n I\<rbrakk> \<Longrightarrow> phi"
shows phi
using assms unfolding UNpart_def by auto

lemma emp_UNpart:
assumes "\<And> n. n < length cl \<Longrightarrow> {} \<notin> P n"
shows "{} \<notin> UNpart cl P"
using assms unfolding UNpart_def by auto

lemma part_UNpart:
assumes cl: "properL cl" and
P: "\<And> n. n < length cl \<Longrightarrow> part {..< brn (cl!n)} (P n)"
shows "part {..< brnL cl (length cl)} (UNpart cl P)"
(is "part ?J ?Q")
proof-
  let ?N = "length cl"
  have J: "?J = (\<Union> n \<in> {..< ?N}. {brnL cl n ..<+ brn (cl!n)})"
  using cl brnL_UN by auto
  have Q: "?Q = (\<Union> n \<in> {..< ?N}. shift cl n ` (P n))"
  unfolding UNpart_def by auto
  show ?thesis unfolding J Q apply(rule part_UN)
  using P brnL_Int by auto
qed

(*  *)

definition pickT_pred where
"pickT_pred cl P II n \<equiv> n < length cl \<and> II \<in> shift cl n ` (P n)"

definition pickT where
"pickT cl P II \<equiv> SOME n. pickT_pred cl P II n"

lemma pickT_pred:
assumes "II \<in> UNpart cl P"
shows "\<exists> n. pickT_pred cl P II n"
using assms unfolding UNpart_def pickT_pred_def by auto

lemma pickT_pred_unique:
assumes P: "\<And> n. n < length cl \<Longrightarrow> part {..< brn (cl!n)} (P n)  \<and> {} \<notin> P n"
and 1: "pickT_pred cl P II n1" and 2: "pickT_pred cl P II n2"
shows "n1 = n2"
proof-
  {assume "n1 \<noteq> n2"
   hence "shift cl n1 ` (P n1) \<inter> shift cl n2 ` (P n2) = {}"
   using assms part_brn_disj2 unfolding pickT_pred_def by blast
   hence False using 1 2 unfolding pickT_pred_def by blast
  }
  thus ?thesis by auto
qed

lemma pickT_pred_pickT:
assumes "II \<in> UNpart cl P"
shows "pickT_pred cl P II (pickT cl P II)"
unfolding pickT_def apply(rule someI_ex)
using assms pickT_pred by auto

lemma pickT_pred_pickT_unique:
assumes P: "\<And> n. n < length cl \<Longrightarrow> part {..< brn (cl!n)} (P n) \<and> {} \<notin> P n"
and "pickT_pred cl P II n"
shows "n = pickT cl P II"
unfolding pickT_def apply(rule sym, rule some_equality)
using assms pickT_pred_unique[of cl P II] by auto

lemma pickT_length[simp]:
assumes "II \<in> UNpart cl P"
shows "pickT cl P II < length cl"
using assms pickT_pred_pickT unfolding pickT_pred_def by auto

lemma pickT_shift[simp]:
assumes "II \<in> UNpart cl P"
shows "II \<in> shift cl (pickT cl P II) ` (P (pickT cl P II))"
using assms pickT_pred_pickT unfolding pickT_pred_def by auto

lemma pickT_unique:
assumes P: "\<And> n. n < length cl \<Longrightarrow> part {..< brn (cl!n)} (P n) \<and> {} \<notin> P n"
and "n < length cl" and "II \<in> shift cl n ` (P n)"
shows "n = pickT cl P II"
using assms pickT_pred_pickT_unique unfolding pickT_pred_def by auto

definition UNlift where
"UNlift cl dl P F II \<equiv>
 shift dl (pickT cl P II) (F (pickT cl P II) (back cl (pickT cl P II) II))"

lemma UNlift_shift[simp]:
assumes P: "\<And> n. n < length cl \<Longrightarrow> part {..< brn (cl!n)} (P n) \<and> {} \<notin> P n"
and n: "n < length cl" and I: "I \<in> P n"
shows "UNlift cl dl P F (shift cl n I) = shift dl n (F n I)"
proof-
  let ?N = "length cl"
  define II where "II = shift cl n I"
  have II: "shift cl n I = II" using II_def by simp
  have n: "n = pickT cl P II" apply(rule pickT_unique)
  using assms unfolding II_def by auto
  have "back cl n II = I" unfolding II_def by simp
  hence "shift dl n (F n (back cl n II)) = shift dl n (F n I)" by simp
  thus ?thesis unfolding UNlift_def II n[THEN sym] .
qed

lemma UNlift_inj_on:
assumes l: "length cl = length dl"
and P: "\<And> n. n < length cl \<Longrightarrow> part {..< brn (cl!n)} (P n) \<and> {} \<notin> P n"
and FP: "\<And> n. n < length dl \<Longrightarrow> part {..< brn (dl!n)} (F n ` (P n)) \<and> {} \<notin> F n ` (P n)"
and F: "\<And> n. n < length cl \<Longrightarrow> inj_on (F n) (P n)"
shows "inj_on (UNlift cl dl P F) (UNpart cl P)" (is "inj_on ?G ?Q")
unfolding inj_on_def proof clarify
  fix II1 II2
  assume II1: "II1 \<in> ?Q" and II2: "II2 \<in> ?Q" and G: "?G II1 = ?G II2"
  from II1 show "II1 = II2"
  proof(cases rule: UNpart_cases)
    case (Local n1 I1)
    hence n1: "n1 < length cl" "n1 < length dl" and I1: "I1 \<in> P n1"
    and II1: "II1 = shift cl n1 I1" using l by auto
    hence G1_def: "?G II1 = shift dl n1 (F n1 I1)" using P by simp
    have Pn1: "part {..< brn (dl!n1)} (F n1 ` (P n1))" "{} \<notin> F n1 ` (P n1)"
    using n1 FP by auto
    have F1_in: "F n1 I1 \<in> F n1 ` (P n1)" using I1 by simp
    hence Fn1I1: "F n1 I1 \<noteq> {}" "F n1 I1 \<subseteq> {..< brn (dl!n1)}"
    using Pn1 by (blast, unfold part_def, blast)
    hence G1: "?G II1 \<noteq> {}" "?G II1 \<subseteq> {brnL dl n1 ..<+ brn (dl!n1)}"
    unfolding G1_def by simp_all
    from II2 show ?thesis
    proof(cases rule: UNpart_cases)
      case (Local n2 I2)
      hence n2: "n2 < length cl" "n2 < length dl" and I2: "I2 \<in> P n2"
      and II2: "II2 = shift cl n2 I2" using l by auto
      hence G2_def: "?G II2 = shift dl n2 (F n2 I2)" using P by simp
      have Pn2: "part {..< brn (dl!n2)} (F n2 ` (P n2))" "{} \<notin> F n2 ` (P n2)"
      using n2 FP by auto
      have F2_in: "F n2 I2 \<in> F n2 ` (P n2)" using I2 by simp
      hence Fn2I2: "F n2 I2 \<noteq> {}" "F n2 I2 \<subseteq> {..< brn (dl!n2)}"
      using Pn2 by (blast, unfold part_def, blast)
      hence G2: "?G II2 \<noteq> {}" "?G II2 \<subseteq> {brnL dl n2 ..<+ brn (dl!n2)}"
      unfolding G2_def by simp_all
      (*  *)
      have n12: "n1 = n2" using n1 n2 G1 G2 G brnL_Int by blast
      have "F n1 I1 = F n2 I2" using G unfolding G1_def G2_def n12 by simp
      hence "I1 = I2" using I1 I2 n1 F unfolding n12 inj_on_def by simp
      thus ?thesis unfolding II1 II2 n12 by simp
    qed
  qed
qed

lemma UNlift_UNpart:
assumes l: "length cl = length dl"
and P: "\<And> n. n < length cl \<Longrightarrow> part {..< brn (cl!n)} (P n) \<and> {} \<notin> P n"
shows "(UNlift cl dl P F) ` (UNpart cl P) = UNpart dl (%n. F n ` (P n))" (is "?G ` ?Q = ?R")
proof safe
  fix II assume II: "II \<in> ?Q"
  thus "?G II \<in> ?R"
  proof(cases rule: UNpart_cases)
    case (Local n I)
    hence n: "n < length cl" "n < length dl" and I: "I \<in> P n"
    and II: "II = shift cl n I" using l by auto
    hence G: "?G II = shift dl n (F n I)" using P by simp
    show ?thesis using n I unfolding G UNpart_def by auto
  qed
next
  fix JJ assume JJ: "JJ \<in> ?R"
  thus "JJ \<in> ?G ` ?Q"
  proof(cases rule: UNpart_cases)
    case (Local n J)
    hence n: "n < length cl" "n < length dl" and J: "J \<in> F n ` (P n)"
    and JJ: "JJ = shift dl n J" using l by auto
    then obtain I where I: "I \<in> P n" and "J = F n I" by auto
    hence "JJ = shift dl n (F n I)" using JJ by simp
    also have "... = UNlift cl dl P F (shift cl n I)" using n I P by simp
    finally have JJ: "JJ = UNlift cl dl P F (shift cl n I)" .
    show ?thesis using n I unfolding JJ UNpart_def by auto
  qed
qed

lemma emp_UNlift_UNpart:
assumes l: "length cl = length dl"
and P: "\<And> n. n < length cl \<Longrightarrow> part {..< brn (cl!n)} (P n) \<and> {} \<notin> P n"
and FP: "\<And> n. n < length dl \<Longrightarrow> {} \<notin> F n ` (P n)"
shows "{} \<notin> (UNlift cl dl P F) ` (UNpart cl P)" (is "{} \<notin> ?R")
proof-
  have R: "?R = UNpart dl (%n. F n ` (P n))"
  apply(rule UNlift_UNpart) using assms by auto
  show ?thesis unfolding R apply(rule emp_UNpart) using FP by simp
qed

lemma part_UNlift_UNpart:
assumes l: "length cl = length dl" and dl: "properL dl"
and P: "\<And> n. n < length cl \<Longrightarrow> part {..< brn (cl!n)} (P n) \<and> {} \<notin> P n"
and FP: "\<And> n. n < length dl \<Longrightarrow> part {..< brn (dl!n)} (F n ` (P n))"
shows "part {..< brnL dl (length dl)} ((UNlift cl dl P F) ` (UNpart cl P))" (is "part ?C ?R")
proof-
  have R: "?R = UNpart dl (%n. F n ` (P n))"
  apply(rule UNlift_UNpart) using assms by auto
  show ?thesis unfolding R apply(rule part_UNpart) using dl FP by auto
qed

lemma ss_wt_Par_UNlift:
assumes l: "length cl = length dl"
and cldl: "properL cl" "properL dl" and II: "II \<in> UNpart cl P"
and P: "\<And> n. n < length cl \<Longrightarrow> part {..< brn (cl!n)} (P n) \<and> {} \<notin> P n"
and FP: "\<And> n. n < length dl \<Longrightarrow> part {..< brn (dl!n)} (F n ` (P n))"
and sw:
"\<And>n I. \<lbrakk>n < length cl; I \<in> P n\<rbrakk> \<Longrightarrow>
     sum (wt (cl ! n) s) I =
     sum (wt (dl ! n) t) (F n I)"
and st: "s \<approx> t"
shows
"sum (wt (Par cl) s) II =
 sum (wt (Par dl) t) (UNlift cl dl P F II)" (is "?L = ?R")
proof-
  let ?N = "length cl"
  let ?p = "%n. 1 / ?N" let ?q = "%n. 1 / (length dl)"
  let ?ss = "%n. s" let ?tt = "%n. t"
  have sstt: "\<And> n. n < ?N \<Longrightarrow> ?ss n \<approx> ?tt n" using st by auto
  have pq: "\<And> n. n < ?N \<Longrightarrow> ?p n = ?q n" and sstt: "\<And> n. n < ?N \<Longrightarrow> ?ss n \<approx> ?tt n"
  using assms l by auto
  from II show ?thesis
  proof(cases rule: UNpart_cases)
    case (Local n I)
    hence n: "n < ?N" "n < length dl" and I: "I \<in> P n"
    and II: "II = shift cl n I" using l by auto
    have I_sub: "I \<subseteq> {..< brn (cl!n)}" using n I P unfolding part_def by blast
    hence FnI_sub: "F n I \<subseteq> {..< brn (dl!n)}" using n I FP unfolding part_def by blast
    have "?L = (?p n) * sum (wt (cl ! n) (?ss n)) I"
    unfolding II using n cldl I_sub by simp
    also have "... = (?q n) * sum (wt (dl ! n) (?tt n)) (F n I)"
    using n pq apply simp using I sw[of n I] unfolding l by auto
    also have "... = ?R"
    unfolding II using l cldl n FnI_sub P I by simp
    finally show ?thesis .
  qed
qed

(* *)

definition thetaSPar where
"thetaSPar \<equiv>
 {(Par cl, Par dl) |
    cl dl. properL cl \<and> properL dl \<and> SbisL cl dl}"

lemma cont_eff_Par_UNlift:
assumes l: "length cl = length dl"
and cldl: "properL cl" "properL dl" "SbisL cl dl"
and II: "II \<in> UNpart cl P" and ii: "ii \<in> II" and jj: "jj \<in> UNlift cl dl P F II"
and P: "\<And> n. n < length cl \<Longrightarrow> part {..< brn (cl!n)} (P n) \<and> {} \<notin> P n"
and FP: "\<And> n. n < length dl \<Longrightarrow> part {..< brn (dl!n)} (F n ` (P n))"
and eff_cont:
"\<And>n I i j. \<lbrakk>n < length cl; I \<in> P n; i \<in> I; j \<in> F n I\<rbrakk> \<Longrightarrow>
  eff (cl!n) s i \<approx> eff (dl!n) t j \<and>
  cont (cl!n) s i \<approx>s cont (dl!n) t j"
and st: "s \<approx> t"
shows
"eff (Par cl) s ii \<approx> eff (Par dl) t jj \<and>
 (cont (Par cl) s ii, cont (Par dl) t jj) \<in> thetaSPar"
(is "?eff \<and> ?cont")
proof-
  let ?N = "length cl"
  let ?p = "%n. 1/?N" let ?q = "%n. 1/(length dl)"
  let ?ss = "%n. s" let ?tt = "%n. t"
  have sstt: "\<And> n. n < ?N \<Longrightarrow> ?ss n \<approx> ?tt n"
  using st l by auto
  have pq: "\<And> n. n < ?N \<Longrightarrow> ?p n = ?q n" and sstt: "\<And> n. n < ?N \<Longrightarrow> ?ss n \<approx> ?tt n"
  using assms l by auto
  from II show ?thesis
  proof(cases rule: UNpart_cases)
    case (Local n I)
    hence n: "n < length cl" "n < length dl" and I: "I \<in> P n"
    and II: "II = shift cl n I" using l by auto
    from ii II obtain i where i: "i \<in> I" and ii: "ii = brnL cl n + i"
    unfolding shift_def by auto
    have "i < brn (cl!n)" using i I n P unfolding part_def by blast note i = this i
    have jj: "jj \<in> shift dl n (F n I)" using jj P n I unfolding II by simp
    from jj II obtain j where j: "j \<in> F n I" and jj: "jj = brnL dl n + j"
    unfolding shift_def by auto
    have "j < brn (dl!n)" using j I n FP unfolding part_def by blast note j = this j
    show ?thesis
    proof
      have "eff (cl!n) (?ss n) i \<approx> eff (dl!n) (?tt n) j"
      using n I i j eff_cont by blast
      thus ?eff unfolding ii jj using st cldl n i j by simp
    next
      have "cont (cl!n) (?ss n) i \<approx>s cont (dl!n) (?tt n) j"
      using n I i j eff_cont by blast
      thus ?cont unfolding ii jj thetaSPar_def using n i j l cldl by simp
    qed
  qed
qed

lemma thetaSPar_Sretr: "thetaSPar \<subseteq> Sretr (thetaSPar)"
unfolding Sretr_def matchC_C_def proof safe
  fix c d s t
  assume c_d: "(c, d) \<in> thetaSPar" and st: "s \<approx> t"
  then obtain cl dl where
  c: "c = Par cl" and d: "d = Par dl" and
  cldl: "properL cl" "properL dl" "SbisL cl dl"
  unfolding thetaSPar_def by blast
  let ?N = "length cl"
  let ?ss = "%n. s" let ?tt = "%n. t"
  have N: "?N = length dl" using cldl by simp
  have sstt: "\<And> n. n < ?N \<Longrightarrow> ?ss n \<approx> ?tt n"
  using st N by auto
  let ?phi = "%n PFn. mC_C Sbis (cl ! n) (dl ! n) (?ss n) (?tt n) (fst PFn) (snd PFn)"
  {fix n assume n: "n < ?N"
   hence "cl ! n \<approx>s dl ! n" using cldl by auto
   hence "\<exists> PFn. ?phi n PFn" using n Sbis_mC_C sstt by fastforce
  }
  then obtain PF where phi: "\<And>n. n < ?N \<Longrightarrow> ?phi n (PF n)"
  using bchoice[of "{..< ?N}" ?phi] by blast
  define P F where "P = fst o PF" and "F = snd o PF"
  have m: "\<And>n. n < ?N \<Longrightarrow> mC_C Sbis (cl ! n) (dl ! n) (?ss n) (?tt n) (P n) (F n)"
  using phi unfolding P_def F_def by auto
  (*  *)
  have brn_c: "brn c = brnL cl ?N" unfolding c by simp
  have brn_d: "brn d = brnL dl (length dl)" unfolding d by simp
  have P: "\<And>n. n < ?N \<Longrightarrow> part {..< brn (cl ! n)} (P n) \<and> {} \<notin> (P n)"
  using m unfolding m_defsAll part_def by auto
  have FP: "\<And>n. n < length dl \<Longrightarrow> part {..< brn (dl ! n)} (F n ` (P n)) \<and> {} \<notin> F n ` (P n)"
  using m N unfolding m_defsAll part_def by auto
  have F: "\<And>n. n < ?N \<Longrightarrow> inj_on (F n) (P n)" using m unfolding m_defsAll by auto
  have sw: "\<And>n I. \<lbrakk>n < length cl; I \<in> P n\<rbrakk> \<Longrightarrow>
     sum (wt (cl ! n) (?ss n)) I = sum (wt (dl ! n) (?tt n)) (F n I)"
  using m unfolding mC_C_def mC_C_wt_def by auto
  have eff_cont: "\<And>n I i j. \<lbrakk>n < length cl; I \<in> P n; i \<in> I; j \<in> F n I\<rbrakk> \<Longrightarrow>
     eff (cl!n) (?ss n) i \<approx> eff (dl!n) (?tt n) j \<and>
     cont (cl!n) (?ss n) i \<approx>s cont (dl!n) (?tt n) j"
  using m unfolding mC_C_def mC_C_eff_cont_def by auto
  (*  *)
  define Q G where "Q = UNpart cl P" and "G = UNlift cl dl P F"
  note defi = Q_def G_def brn_c brn_d
  show "\<exists>Q G. mC_C (thetaSPar) c d s t Q G"
  apply(rule exI[of _ Q]) apply(rule exI[of _ G])
  unfolding mC_C_def proof (intro conjI)
    show "mC_C_part c d Q G" unfolding mC_C_part_def proof(intro conjI)
      show "{} \<notin> Q" unfolding defi apply(rule emp_UNpart) using P by simp
      show "{} \<notin> G ` Q" unfolding defi apply(rule emp_UNlift_UNpart) using N P FP by auto
      show "part {..<brn c} Q"
      unfolding defi apply(rule part_UNpart) using cldl P by auto
      show "part {..<brn d} (G ` Q)"
      unfolding defi apply(rule part_UNlift_UNpart) using N cldl P FP by auto
    qed
  next
    show "inj_on G Q"
    unfolding defi apply(rule UNlift_inj_on) using N P FP F by auto
  next
    show "mC_C_wt c d s t Q G"
    unfolding mC_C_wt_def defi proof clarify
      fix I assume "I \<in> UNpart cl P"
      thus "sum (wt c s) I = sum (wt d t) (UNlift cl dl P F I)"
      unfolding c d apply(intro ss_wt_Par_UNlift)
      using N cldl P FP sw st by auto
    qed
  next
    show "mC_C_eff_cont (thetaSPar) c d s t Q G"
    unfolding mC_C_eff_cont_def proof clarify
      fix II ii jj assume II: "II \<in> Q" and ii: "ii \<in> II" and jj: "jj \<in> G II"
      thus "eff c s ii \<approx> eff d t jj \<and> (cont c s ii, cont d t jj) \<in> thetaSPar"
      unfolding defi c d apply(intro cont_eff_Par_UNlift)
      using N cldl P FP eff_cont st by blast+
    qed
  qed
qed

lemma thetaSPar_Sbis: "thetaSPar \<subseteq> Sbis"
using Sbis_raw_coind thetaSPar_Sretr by blast

theorem Par_Sbis[simp]:
assumes "properL cl" and "properL dl" "SbisL cl dl"
shows "Par cl \<approx>s Par dl"
using assms thetaSPar_Sbis unfolding thetaSPar_def by blast


subsection\<open>01-bisimilarity versus language constructs\<close>

(* Discreetness: *)
lemma ZObis_pres_discr_L: "c \<approx>01 d \<Longrightarrow> discr d \<Longrightarrow> discr c"
proof (coinduction arbitrary: d c, clarsimp)
  fix s i c d assume i: "i < brn c" and d: "discr d" and c_d: "c \<approx>01 d"
  then obtain I0 P F where
    match: "mC_ZOC ZObis c d s s I0 P F"
    using ZObis_mC_ZOC[of c d s s] by blast
  hence "\<Union>P = {..<brn c}"
    using i unfolding mC_ZOC_def mC_ZOC_part_def part_def by simp
  then obtain I where I: "I \<in> P" and i: "i \<in> I" using i by auto
  show "s \<approx> eff c s i \<and> ((\<exists>d. cont c s i \<approx>01 d \<and> discr d) \<or> discr (cont c s i))"
  proof(cases "I = I0")
    case False
    then obtain j where j: "j \<in> F I"
      using match I False unfolding mC_ZOC_def mC_ZOC_part_def by blast
    hence "j < brn d" using I match
      unfolding mC_ZOC_def mC_ZOC_part_def part_def apply simp by blast
    hence md: "discr (cont d s j)" and s: "s \<approx> eff d s j"
      using d discr_cont[of d j s] discr_eff_indis[of d j s] by auto
    have "eff c s i \<approx> eff d s j" and md2: "cont c s i \<approx>01 cont d s j"
      using I i j match False unfolding mC_ZOC_def mC_ZOC_eff_cont_def by auto
    hence "s \<approx> eff c s i" using s indis_sym indis_trans by blast
    thus ?thesis using md md2 by blast
  next
    case True
    hence "s \<approx> eff c s i \<and> cont c s i \<approx>01 d"
      using match i ZObis_sym unfolding mC_ZOC_def mC_ZOC_eff_cont0_def by blast
    thus ?thesis using d by blast
  qed
qed

theorem ZObis_pres_discr_R:
assumes "discr c" and "c \<approx>01 d"
shows "discr d"
using assms ZObis_pres_discr_L ZObis_sym by blast

theorem ZObis_finished_discr_L:
assumes "c \<approx>01 d" and "proper d" and "finished d"
shows "discr c"
using assms ZObis_pres_discr_L by auto

theorem ZObis_finished_discr_R:
assumes "proper c" and "finished c" and "c \<approx>01 d"
shows "discr d"
using assms ZObis_pres_discr_R[of c d] by auto

theorem discr_ZObis[simp]:
assumes "proper c" and "proper d" and "discr c" and "discr d"
shows "c \<approx>01 d"
using assms by auto

(* Done: *)
 theorem Done_ZObis[simp]:
"Done \<approx>01 Done"
by simp

(* Atm: *)
theorem Atm_ZObis[simp]:
assumes "compatAtm atm"
shows "Atm atm \<approx>01 Atm atm"
using assms by simp

(* Seq *)

definition thetaZOSeqI where
"thetaZOSeqI \<equiv>
 {(e ;; c, e ;; d) | e c d . siso e \<and> c \<approx>01 d}"

lemma thetaZOSeqI_ZOretr:
"thetaZOSeqI \<subseteq> ZOretr (thetaZOSeqI Un ZObis)"
unfolding ZOretr_def matchC_LC_def proof safe
  fix c d s t
  assume c_d: "(c, d) \<in> thetaZOSeqI" and st: "s \<approx> t"
  then obtain e c1 d1 where e: "siso e" and c1d1: "c1 \<approx>01 d1"
  and c: "c = e ;; c1" and d: "d = e ;; d1"
  unfolding thetaZOSeqI_def by auto
  let ?I0 = "{}" let ?J0 = "{}"
  let ?P = "{?I0} Un {{i} | i . i < brn e}"
  let ?F = "%I. I"
  show "\<exists>I0 P F. mC_ZOC (thetaZOSeqI Un ZObis) c d s t I0 P F"
  apply(rule exI[of _ ?I0])
  apply(rule exI[of _ ?P]) apply(rule exI[of _ ?F])
  unfolding mC_ZOC_def proof (intro conjI)
    show "mC_ZOC_part c d s t ?I0 ?P ?F"
    unfolding mC_ZOC_part_def proof (intro conjI)
      show "part {..<brn c} ?P"
      unfolding part_def proof safe
        fix i assume "i < brn c"
        thus "i \<in> \<Union> ?P" using c e st siso_cont_indis[of e s t] by auto
      qed (unfold c, simp)
      (*  *)
      thus "part {..<brn d} (?F ` ?P)" unfolding c d by auto
    qed auto
  next
    show "mC_ZOC_eff_cont (thetaZOSeqI Un ZObis) c d s t ?I0 ?P ?F"
    unfolding mC_ZOC_eff_cont_def proof(intro allI impI, elim conjE)
      fix I i j
      assume I: "I \<in> ?P - {?I0}" and i: "i \<in> I" and j: "j \<in> I"
      then obtain i' where "j \<in> ?F {i'}" and "i' < brn e"
      using I j by auto
      thus "eff c s i \<approx> eff d t j \<and> (cont c s i, cont d t j) \<in> thetaZOSeqI \<union> ZObis"
      using st c_d e i j I unfolding c d thetaZOSeqI_def
      by (cases "finished (cont e s i')") auto
    qed
  qed (insert st c_d c, unfold m_defsAll thetaZOSeqI_def part_def, auto)
qed

lemma thetaZOSeqI_ZObis:
"thetaZOSeqI \<subseteq> ZObis"
using ZObis_coind thetaZOSeqI_ZOretr by blast

theorem Seq_siso_ZObis[simp]:
assumes "siso e" and "c2 \<approx>01 d2"
shows "e ;; c2 \<approx>01 e ;; d2"
using assms thetaZOSeqI_ZObis unfolding thetaZOSeqI_def by auto

(*  *)

definition thetaZOSeqD where
"thetaZOSeqD \<equiv>
 {(c1 ;; c2, d1 ;; d2) |
     c1 c2 d1 d2.
        proper c1 \<and> proper d1 \<and> proper c2 \<and> proper d2 \<and>
        discr c2 \<and> discr d2 \<and>
        c1 \<approx>01 d1}"

lemma thetaZOSeqD_ZOretr:
"thetaZOSeqD \<subseteq> ZOretr (thetaZOSeqD Un ZObis)"
unfolding ZOretr_def matchC_LC_def proof safe
  fix c d s t
  assume c_d: "(c, d) \<in> thetaZOSeqD" and st: "s \<approx> t"
  then obtain c1 c2 d1 d2 where
  c1d1: "proper c1" "proper d1" "c1 \<approx>01 d1" and
  c2d2: "proper c2" "proper d2" "discr c2" "discr d2"
  and c: "c = c1 ;; c2" and d: "d = d1 ;; d2"
  unfolding thetaZOSeqD_def by auto
  from c1d1 st obtain P F I0
  where match: "mC_ZOC ZObis c1 d1 s t I0 P F"
  using ZObis_mC_ZOC by blast
  have P: "\<Union>P = {..<brn c1}" and FP: "\<Union>(F ` P) = {..<brn d1}"
  using match unfolding mC_ZOC_def mC_ZOC_part_def part_def by metis+
  show "\<exists>I0 P F. mC_ZOC (thetaZOSeqD Un ZObis) c d s t I0 P F"
  apply(intro exI[of _ I0] exI[of _ P] exI[of _ F])
  unfolding mC_ZOC_def proof (intro conjI)
    have I0: "I0 \<in> P" using match unfolding m_defsAll by blast
    show "mC_ZOC_eff_cont0 (thetaZOSeqD \<union> ZObis) c d s t I0 F"
    unfolding mC_ZOC_eff_cont0_def proof(intro conjI ballI)
      fix i assume i: "i \<in> I0"
      let ?c1' = "cont c1 s i" let ?s' = "eff c1 s i"
      have "i < brn c1" using i I0 P by blast note i = this i
      have c1'd1: "?c1' \<approx>01 d1" "proper ?c1'"
      using c1d1 i I0 match unfolding mC_ZOC_def mC_ZOC_eff_cont0_def by auto
      show "s \<approx> eff c s i"
        using i match unfolding c mC_ZOC_def mC_ZOC_eff_cont0_def by simp
      show "(cont c s i, d) \<in> thetaZOSeqD \<union> ZObis"
      proof(cases "finished ?c1'")
        case False note f_c1' = False
        hence csi: "cont c s i = ?c1' ;; c2" using i unfolding c by simp
        hence "(cont c s i, d) \<in> thetaZOSeqD"
        using c1'd1 c1d1 c2d2 f_c1' i match
        unfolding csi d thetaZOSeqD_def mC_ZOC_def mC_ZOC_eff_cont0_def by blast
        thus ?thesis by simp
      next
        case True note f_c1' = True
        hence csi: "cont c s i = c2" using i unfolding c by simp
        have "discr d1" using f_c1' c1'd1 ZObis_finished_discr_R by blast
        hence "c2 \<approx>01 d" using c2d2 c1d1 unfolding d by simp
        thus ?thesis unfolding csi by simp
      qed
    next
      fix j assume j: "j \<in> F I0"
      let ?d1' = "cont d1 t j" let ?t' = "eff d1 t j"
      have "j < brn d1" using j I0 FP by blast note j = this j
      have c1d1': "c1 \<approx>01 ?d1'" "proper ?d1'"
      using c1d1 j I0 match unfolding mC_ZOC_def mC_ZOC_eff_cont0_def by auto
      show "t \<approx> eff d t j"
        using j match unfolding d mC_ZOC_def mC_ZOC_eff_cont0_def by simp
      show "(c, cont d t j) \<in> thetaZOSeqD \<union> ZObis"
      proof (cases "finished ?d1'")
        case False note f_d1' = False
        hence dtj: "cont d t j = ?d1' ;; d2" using j unfolding d by simp
        hence "(c, cont d t j) \<in> thetaZOSeqD"
        using c1d1' c1d1 c2d2 f_d1' j match
        unfolding c dtj thetaZOSeqD_def mC_ZOC_def mC_ZOC_eff_cont0_def by blast
        thus ?thesis by simp
      next
        case True note f_d1' = True
        hence dtj: "cont d t j = d2" using j unfolding d by simp
        hence "discr c1" using f_d1' c1d1' ZObis_finished_discr_L by blast
        hence "c \<approx>01 d2" using c2d2 c1d1 unfolding c by simp
        thus ?thesis unfolding dtj by simp
      qed
    qed
  next
    show "mC_ZOC_eff_cont (thetaZOSeqD \<union> ZObis) c d s t I0 P F"
    unfolding mC_ZOC_eff_cont_def proof(intro allI impI, elim conjE)
      fix i j I assume I : "I \<in> P - {I0}" and i: "i \<in> I" and j: "j \<in> F I"
      let ?c1' = "cont c1 s i"  let ?d1' = "cont d1 t j"
      let ?s' = "eff c1 s i"  let ?t' = "eff d1 t j"
      have "i < brn c1" using i I P by blast note i = this i
      have "j < brn d1" using j I FP by blast note j = this j
      have c1'd1': "?c1' \<approx>01 ?d1'" "proper ?c1'" "proper ?d1'"
      using c1d1 i j I match unfolding c mC_ZOC_def mC_ZOC_eff_cont_def by auto
      show "eff c s i \<approx> eff d t j \<and> (cont c s i, cont d t j) \<in> thetaZOSeqD \<union> ZObis"
      (is "?eff \<and> ?cont") proof
        show ?eff using match I i j unfolding c d m_defsAll apply simp by blast
      next
        show ?cont
        proof(cases "finished ?c1'")
          case True note c1' = True
          hence csi: "cont c s i = c2" using i match unfolding c m_defsAll by simp
          show ?thesis
          proof(cases "finished ?d1'")
            case True
            hence "cont d t j = d2" using j match unfolding d m_defsAll by simp
            thus ?thesis using csi c2d2 by simp
          next
            case False
            hence dtj: "cont d t j = ?d1' ;; d2"
            using j match unfolding d m_defsAll by simp
            have "discr ?d1'" using c1'd1' c1' ZObis_finished_discr_R by blast
            thus ?thesis using c1'd1' c2d2 unfolding csi dtj by simp
          qed
        next
          case False
          hence csi: "cont c s i = ?c1' ;; c2"
          using i match unfolding c m_defsAll by simp
          show ?thesis
          proof(cases "finished (cont d1 t j)")
            case True note d1' = True
            hence dtj: "cont d t j = d2" using j match unfolding d m_defsAll by simp
            have "discr ?c1'" using c1'd1' d1' ZObis_finished_discr_L by blast
            thus ?thesis using c1'd1' c2d2 unfolding csi dtj by simp
          next
            case False
            hence dtj: "cont d t j = ?d1' ;; d2" using j match unfolding d m_defsAll by simp
            thus ?thesis unfolding csi dtj thetaZOSeqD_def
            using c1'd1' c2d2 by blast
          qed
        qed
      qed
    qed
  qed(insert match, unfold m_defsAll c d, auto)
qed

lemma thetaZOSeqD_ZObis:
"thetaZOSeqD \<subseteq> ZObis"
using ZObis_coind thetaZOSeqD_ZOretr by blast

theorem Seq_ZObis[simp]:
assumes "proper c1" and "proper d1" and "proper c2" and "proper d2"
and "c1 \<approx>01 d1" and "discr c2" and "discr d2"
shows "c1 ;; c2 \<approx>01 d1 ;; d2"
using assms thetaZOSeqD_ZObis unfolding thetaZOSeqD_def by auto

(* Ch *)
definition thetaZOCh where
"thetaZOCh ch c1 c2 d1 d2 \<equiv> {(Ch ch c1 c2, Ch ch d1 d2)}"

lemma thetaZOCh_Sretr:
assumes "compatCh ch" and "c1 \<approx>01 d1" and "c2 \<approx>01 d2"
shows "thetaZOCh ch c1 c2 d1 d2 \<subseteq>
       Sretr (thetaZOCh ch c1 c2 d1 d2 \<union> ZObis)"
(is "?th \<subseteq> Sretr (?th \<union> ZObis)")
unfolding Sretr_def matchC_C_def proof safe
  fix c d s t
  assume c_d: "(c, d) \<in> ?th" and st: "s \<approx> t"
  hence c: "c = Ch ch c1 c2" "brn c = 2"
  and d: "d = Ch ch d1 d2" "brn d = 2"
  unfolding thetaZOCh_def by auto
  let ?P = "{{0}, {1}}"
  let ?F = "%I. I"
  show "\<exists>P F. mC_C (?th Un ZObis) c d s t P F"
  apply(rule exI[of _ ?P]) apply(rule exI[of _ ?F])
  using assms st c_d c unfolding m_defsAll thetaZOCh_def part_def by auto
qed

lemma thetaZOCh_ZOretr:
assumes "compatCh ch" and "c1 \<approx>01 d1" and "c2 \<approx>01 d2"
shows "thetaZOCh ch c1 c2 d1 d2 \<subseteq>
       ZOretr (thetaZOCh ch c1 c2 d1 d2 \<union> ZObis)"
using thetaZOCh_Sretr[OF assms]
by (metis (no_types) Retr_incl subset_trans)

lemma thetaZOCh_ZObis:
assumes "compatCh ch" and "c1 \<approx>01 d1" and "c2 \<approx>01 d2"
shows "thetaZOCh ch c1 c2 d1 d2 \<subseteq> ZObis"
using ZObis_coind thetaZOCh_ZOretr[OF assms] by blast

theorem Ch_siso_ZObis[simp]:
assumes "compatCh ch" and "c1 \<approx>01 d1" and "c2 \<approx>01 d2"
shows "Ch ch c1 c2 \<approx>01 Ch ch d1 d2"
using thetaZOCh_ZObis[OF assms] unfolding thetaZOCh_def by auto

(*  *)
definition theFTOne where
"theFTOne cl dl \<equiv> theFT cl \<union> theFT dl"

definition theNFTBoth where
"theNFTBoth cl dl \<equiv> theNFT cl \<inter> theNFT dl"

lemma theFTOne_sym: "theFTOne cl dl = theFTOne dl cl"
unfolding theFTOne_def by auto

lemma finite_theFTOne[simp]:
"finite (theFTOne cl dl)"
unfolding theFTOne_def by simp

lemma theFTOne_length_finished[simp]:
assumes "n \<in> theFTOne cl dl"
shows "(n < length cl \<and> finished (cl!n)) \<or> (n < length dl \<and> finished (dl!n))"
using assms unfolding theFTOne_def by auto

lemma theFTOne_length[simp]:
assumes "length cl = length dl" and "n \<in> theFTOne cl dl"
shows "n < length cl" and "n < length dl"
using assms theFTOne_length_finished[of n cl dl] by auto

lemma theFTOne_intro[intro]:
assumes "\<And> n. (n < length cl \<and> finished (cl!n)) \<or> (n < length dl \<and> finished (dl!n))"
shows "n \<in> theFTOne cl dl"
using assms unfolding theFTOne_def by auto

lemma pickFT_theFTOne[simp]:
assumes "WtFT cl = 1"
shows "pickFT cl \<in> theFTOne cl dl"
using assms unfolding theFTOne_def by auto

lemma finite_theNFTBoth[simp]:
"finite (theNFTBoth cl dl)"
unfolding theNFTBoth_def by simp

lemma theNFTBoth_sym: "theNFTBoth cl dl = theNFTBoth dl cl"
unfolding theNFTBoth_def by auto

lemma theNFTBoth_length_finished[simp]:
assumes "n \<in> theNFTBoth cl dl"
shows "n < length cl" and "\<not> finished (cl!n)"
and "n < length dl" and "\<not> finished (dl!n)"
using assms unfolding theNFTBoth_def by auto

lemma theNFTBoth_intro[intro]:
assumes "\<And> n. n < length cl \<and> \<not> finished (cl!n) \<and> n < length dl \<and> \<not> finished (dl!n)"
shows "n \<in> theNFTBoth cl dl"
using assms unfolding theNFTBoth_def by auto

lemma theFTOne_Int_theNFTBoth[simp]:
"theFTOne cl dl \<inter> theNFTBoth cl dl = {}"
and "theNFTBoth cl dl \<inter> theFTOne cl dl = {}"
unfolding theFTOne_def theNFTBoth_def theFT_def theNFT_def by auto

lemma theFT_Un_theNFT_One_Both[simp]:
assumes "length cl = length dl"
shows
"theFTOne cl dl \<union> theNFTBoth cl dl = {..< length cl}" and
"theNFTBoth cl dl \<union> theFTOne cl dl = {..< length cl}"
using assms
unfolding theFTOne_def theNFTBoth_def theFT_def theNFT_def by auto

lemma in_theFTOne_theNFTBoth[simp]:
assumes "n1 \<in> theFTOne cl dl" and "n2 \<in> theNFTBoth cl dl"
shows "n1 \<noteq> n2" and "n2 \<noteq> n1"
using assms theFTOne_Int_theNFTBoth by blast+


(*  *)

definition BrnFT where
"BrnFT cl dl \<equiv> \<Union> n \<in> theFTOne cl dl. {brnL cl n ..<+ brn (cl!n)}"

definition BrnNFT where
"BrnNFT cl dl \<equiv> \<Union> n \<in> theNFTBoth cl dl. {brnL cl n ..<+ brn (cl!n)}"

lemma BrnFT_elim[elim, consumes 1, case_names Local]:
assumes "ii \<in> BrnFT cl dl"
and "\<And> n i. \<lbrakk>n \<in> theFTOne cl dl; i < brn (cl!n); ii = brnL cl n + i\<rbrakk> \<Longrightarrow> phi"
shows phi
using assms unfolding BrnFT_def by auto

lemma finite_BrnFT[simp]:
"finite (BrnFT cl dl)"
unfolding BrnFT_def by auto

lemma BrnFT_incl_brnL[simp]:
assumes l: "length cl = length dl" and cl: "properL cl"
shows "BrnFT cl dl \<subseteq> {..< brnL cl (length cl)}" (is "?L \<subseteq> ?R")
proof-
  have "?L \<subseteq> (\<Union> n<length cl. {brnL cl n..<+brn (cl ! n)})"
  using l unfolding BrnFT_def theFTOne_def theFT_def by auto
  also have "... = ?R" using cl brnL_UN by auto
  finally show ?thesis .
qed

lemma BrnNFT_elim[elim, consumes 1, case_names Local]:
assumes "ii \<in> BrnNFT cl dl"
and "\<And> n i. \<lbrakk>n \<in> theNFTBoth cl dl; i < brn (cl!n); ii = brnL cl n + i\<rbrakk> \<Longrightarrow> phi"
shows phi
using assms unfolding BrnNFT_def by auto

lemma finite_BrnNFT[simp]:
"finite (BrnNFT cl dl)"
unfolding BrnNFT_def by auto

lemma BrnNFT_incl_brnL[simp]:
assumes cl: "properL cl"
shows "BrnNFT cl dl \<subseteq> {..< brnL cl (length cl)}" (is "?L \<subseteq> ?R")
proof-
  have "?L \<subseteq> (\<Union> n<length cl. {brnL cl n..<+brn (cl ! n)})"
  unfolding BrnNFT_def theNFTBoth_def theNFT_def by auto
  also have "... = ?R" using cl brnL_UN by auto
  finally show ?thesis .
qed

lemma BrnFT_Int_BrnNFT[simp]:
assumes l: "length cl = length dl"
shows
"BrnFT cl dl \<inter> BrnNFT cl dl = {}" (is "?L")
and "BrnNFT cl dl \<inter> BrnFT cl dl = {}" (is "?R")
proof-
  {fix ii assume 1: "ii \<in> BrnFT cl dl" and 2: "ii \<in> BrnNFT cl dl"
   from 1 have False
   proof (cases rule: BrnFT_elim)
     case (Local n1 i1)
     hence n1: "n1 < length cl" "n1 < length dl" "n1 \<in> theFTOne cl dl"
     and i1: "i1 < brn (cl ! n1)"
     and ii1: "ii = brnL cl n1 + i1" using l by auto
     from 2 show ?thesis
     proof (cases rule: BrnNFT_elim)
       case (Local n2 i2)
       hence n2: "n2 \<in> theNFTBoth cl dl" and i2: "i2 < brn (cl ! n2)"
       and ii2: "ii = brnL cl n2 + i2" by auto
       have n12: "n1 \<noteq> n2" using n1 n2 by simp
       show ?thesis
       proof(cases "n1 < n2")
         case True hence Suc: "Suc n1 \<le> n2" by simp
         have "ii < brnL cl (Suc n1)" unfolding ii1 using i1 n1 by simp
         also have "... \<le> brnL cl n2" using Suc by auto
         also have "... \<le> ii" unfolding ii2 by simp
         finally show False by simp
       next
         case False hence Suc: "Suc n2 \<le> n1" using n12 by simp
         have "ii < brnL cl (Suc n2)" unfolding ii2 using i2 n2 by simp
         also have "... \<le> brnL cl n1" using Suc by auto
         also have "... \<le> ii" unfolding ii1 by simp
         finally show False by simp
       qed
     qed
   qed
  }
  thus ?L by blast  thus ?R by blast
qed

lemma BrnFT_Un_BrnNFT[simp]:
assumes l: "length cl = length dl" and cl: "properL cl"
shows "BrnFT cl dl \<union> BrnNFT cl dl = {..< brnL cl (length cl)}" (is "?L1 = ?R")
and "BrnNFT cl dl \<union> BrnFT cl dl = {..< brnL cl (length cl)}" (is "?L2 = ?R")
proof-
  have R: "?R = (\<Union> n<length cl. {brnL cl n..<+brn (cl ! n)})"
  using cl brnL_UN by auto
  thus "?L1 = ?R" unfolding R
  unfolding l BrnFT_def BrnNFT_def
  theFTOne_def theNFTBoth_def theFT_def theNFT_def by blast
  thus "?L2 = ?R" by blast
qed

lemma BrnFT_part:
assumes l: "length cl = length dl"
and P: "\<And> n. n < length cl \<Longrightarrow> part {..< brn (cl!n)} (P n)"
shows "BrnFT cl dl = (\<Union> n \<in> theFTOne cl dl. Union (shift cl n ` (P n)))" (is "?L = ?R")
proof (safe elim!: BrnFT_elim)
  fix x n i assume n: "n \<in> theFTOne cl dl" and i: "i < brn (cl ! n)"
  hence "n < length cl" "n < length dl" using l by auto note n = this n
  hence "i \<in> Union (P n)" using P i unfolding part_def by auto
  then obtain I where "i \<in> I" and "I \<in> P n" by blast
  thus "brnL cl n + i \<in> ?R" using n unfolding shift_def by auto
next
  fix n ii I assume n: "n \<in> theFTOne cl dl" and ii: "ii \<in> shift cl n I" and I: "I \<in> P n"
  hence "n < length cl" using l by simp
  hence "I \<subseteq> {..< brn (cl ! n)}" using I P unfolding part_def by blast
  hence "ii \<in> {brnL cl n..<+brn (cl ! n)}" using ii unfolding shift_def by auto
  thus "ii \<in> ?L" using n unfolding BrnFT_def by auto
qed

lemma brnL_pickFT_BrnFT[simp]:
assumes "properL cl" and "WtFT cl = 1"
shows "brnL cl (pickFT cl) \<in> BrnFT cl dl"
using assms brn_gt_0_L unfolding BrnFT_def by auto

lemma WtFT_ParT_BrnFT[simp]:
assumes "length cl = length dl" "properL cl" and "WtFT cl = 1"
shows "sum (wt (ParT cl) s) (BrnFT cl dl) = 1"
proof-
  have "brnL cl (pickFT cl) \<in> BrnFT cl dl" and
  "BrnFT cl dl \<subseteq> {..<brnL cl (length cl)}"
  using assms BrnFT_incl_brnL by (simp, blast)
  thus ?thesis using assms by simp
qed

(*  *)

definition UNpart1 where
"UNpart1 cl dl P \<equiv> \<Union> n \<in> theNFTBoth cl dl. shift cl n ` (P n)"

definition UNpart01 where
"UNpart01 cl dl P \<equiv> {BrnFT cl dl} \<union> UNpart1 cl dl P"

lemma BrnFT_UNpart01[simp]:
"BrnFT cl dl \<in> UNpart01 cl dl P"
unfolding UNpart01_def by simp

lemma UNpart1_cases[elim, consumes 1, case_names Local]:
assumes "II \<in> UNpart1 cl dl P"
"\<And> n I. \<lbrakk>n \<in> theNFTBoth cl dl; I \<in> P n; II = shift cl n I\<rbrakk> \<Longrightarrow> phi"
shows phi
using assms unfolding UNpart1_def by auto

lemma UNpart01_cases[elim, consumes 1, case_names Local0 Local]:
assumes "II \<in> UNpart01 cl dl P" and "II = BrnFT cl dl \<Longrightarrow> phi"
"\<And> n I. \<lbrakk>n \<in> theNFTBoth cl dl; I \<in> P n; II = shift cl n I; II \<in> UNpart1 cl dl P\<rbrakk> \<Longrightarrow> phi"
shows phi
using assms unfolding UNpart01_def UNpart1_def by auto

lemma emp_UNpart1:
assumes "\<And> n. n < length cl \<Longrightarrow> {} \<notin> P n"
shows "{} \<notin> UNpart1 cl dl P"
using assms unfolding UNpart1_def by auto

lemma emp_UNpart01:
assumes "\<And> n. n < length cl \<Longrightarrow> {} \<notin> P n"
shows "{} \<notin> UNpart01 cl dl P - {BrnFT cl dl}"
using assms emp_UNpart1 unfolding UNpart01_def by auto

lemma BrnFT_Int_UNpart1[simp]:
assumes l: "length cl = length dl"
and P: "\<And> n. n < length cl \<Longrightarrow> part {..< brn (cl!n)} (P n) \<and> {} \<notin> P n"
and II: "II \<in> UNpart1 cl dl P"
shows "BrnFT cl dl \<inter> II = {}"
using II proof(cases rule: UNpart1_cases)
  have 1: "BrnFT cl dl = (\<Union> n \<in> theFTOne cl dl. Union (shift cl n ` (P n)))"
  apply(rule BrnFT_part) using l P by auto
  case (Local n I)
  hence n: "n < length cl" "n < length dl" "n \<in> theNFTBoth cl dl"
  and I: "I \<in> P n" and II: "II = shift cl n I" by auto
  {fix n0 assume n0: "n0 \<in> theFTOne cl dl"
   hence "n0 < length cl" "n0 < length dl" using l by auto note n0 = this n0
   {fix JJ assume  "JJ \<in> shift cl n0 ` (P n0)"
    then obtain J where J: "J \<in> P n0" and JJ: "JJ = shift cl n0 J" by auto
    have "n \<noteq> n0" using n n0 by simp
    have "JJ Int II = {}" unfolding JJ II
    apply(rule part_brn_disj3) using P I J n n0 by auto
   }
   hence "Union (shift cl n0 ` (P n0)) Int II = {}" by blast
  }
  thus ?thesis unfolding II 1 by blast
qed

lemma BrnFT_notIn_UNpart1:
assumes l: "length cl = length dl"
and P: "\<And> n. n < length cl \<Longrightarrow> part {..< brn (cl!n)} (P n) \<and> {} \<notin> P n"
shows "BrnFT cl dl \<notin> UNpart1 cl dl P"
using assms BrnFT_Int_UNpart1 emp_UNpart1 by (metis Int_absorb)

lemma UNpart1_UNpart01:
assumes l: "length cl = length dl"
and P: "\<And> n. n < length cl \<Longrightarrow> part {..< brn (cl!n)} (P n) \<and> {} \<notin> P n"
shows "UNpart1 cl dl P = UNpart01 cl dl P - {BrnFT cl dl}"
proof-
  have "BrnFT cl dl \<notin> UNpart1 cl dl P"
  apply(rule BrnFT_notIn_UNpart1) using assms by auto
  thus ?thesis unfolding UNpart01_def by auto
qed

lemma part_UNpart1[simp]:
assumes l: "length cl = length dl"
and P: "\<And> n. n < length cl \<Longrightarrow> part {..< brn (cl!n)} (P n)"
shows "part (BrnNFT cl dl) (UNpart1 cl dl P)"
unfolding BrnNFT_def UNpart1_def apply(rule part_UN)
  using l P apply fastforce
  apply(rule brnL_Int) using l by auto

lemma part_UNpart01:
assumes cl: "properL cl" and l: "length cl = length dl"
and P: "\<And> n. n < length cl \<Longrightarrow> part {..< brn (cl!n)} (P n) \<and> {} \<notin> P n"
shows "part {..< brnL cl (length cl)} (UNpart01 cl dl P)"
unfolding UNpart01_def apply(rule part_Un_singl2[of _ _ "BrnNFT cl dl"])
using assms using BrnFT_Int_UNpart1 by (simp, simp, blast)

(*  *)

definition UNlift01 where
"UNlift01 cl dl P F II \<equiv>
 if II = BrnFT cl dl
   then BrnFT dl cl
   else shift dl (pickT cl P II) (F (pickT cl P II) (back cl (pickT cl P II) II))"

lemma UNlift01_BrnFT[simp]:
"UNlift01 cl dl P F (BrnFT cl dl) = BrnFT dl cl"
unfolding UNlift01_def by simp

lemma UNlift01_shift[simp]:
assumes l: "length cl = length dl"
and P: "\<And> n. n < length cl \<Longrightarrow> part {..< brn (cl!n)} (P n) \<and> {} \<notin> P n"
and n: "n \<in> theNFTBoth cl dl" and I: "I \<in> P n"
shows "UNlift01 cl dl P F (shift cl n I) = shift dl n (F n I)"
proof-
  let ?N = "length cl"
  define II where "II = shift cl n I"
  have "n < length cl" using n l by auto note n = this n
  have II: "shift cl n I = II" using II_def by simp
  have "II \<in> UNpart1 cl dl P" unfolding II_def UNpart1_def using n I by auto
  hence "II \<noteq> BrnFT cl dl" using BrnFT_notIn_UNpart1[of cl dl P] l n P by auto
  hence 1: "UNlift01 cl dl P F II =
  shift dl (pickT cl P II) (F (pickT cl P II) (back cl (pickT cl P II) II))"
  unfolding UNlift01_def by simp
  have n: "n = pickT cl P II" apply(rule pickT_unique)
  using assms unfolding II_def by auto
  have "back cl n II = I" unfolding II_def by simp
  hence "shift dl n (F n (back cl n II)) = shift dl n (F n I)" by simp
  thus ?thesis unfolding 1 II n[THEN sym] .
qed

lemma UNlift01_inj_on_UNpart1:
assumes l: "length cl = length dl"
and P: "\<And> n. n < length cl \<Longrightarrow> part {..< brn (cl!n)} (P n) \<and> {} \<notin> P n"
and FP: "\<And> n. n < length dl \<Longrightarrow> part {..< brn (dl!n)} (F n ` (P n)) \<and> {} \<notin> F n ` (P n)"
and F: "\<And> n. n < length cl \<Longrightarrow> inj_on (F n) (P n)"
shows "inj_on (UNlift01 cl dl P F) (UNpart1 cl dl P)" (is "inj_on ?G ?Q")
unfolding inj_on_def proof clarify
  fix II1 II2
  assume II1: "II1 \<in> ?Q" and II2: "II2 \<in> ?Q" and G: "?G II1 = ?G II2"
  from II1 show "II1 = II2"
  proof(cases rule: UNpart1_cases)
    case (Local n1 I1)
    hence n1: "n1 \<in> theNFTBoth cl dl" "n1 < length cl" "n1 < length dl" and I1: "I1 \<in> P n1"
    and II1: "II1 = shift cl n1 I1" using l by auto
    hence G1_def: "?G II1 = shift dl n1 (F n1 I1)" using l P by simp
    have Pn1: "part {..< brn (dl!n1)} (F n1 ` (P n1))" "{} \<notin> F n1 ` (P n1)"
    using n1 FP by auto
    have F1_in: "F n1 I1 \<in> F n1 ` (P n1)" using I1 by simp
    hence Fn1I1: "F n1 I1 \<noteq> {}" "F n1 I1 \<subseteq> {..< brn (dl!n1)}"
    using Pn1 by (blast, unfold part_def, blast)
    hence G1: "?G II1 \<noteq> {}" "?G II1 \<subseteq> {brnL dl n1 ..<+ brn (dl!n1)}"
    unfolding G1_def by simp_all
    from II2 show ?thesis
    proof(cases rule: UNpart1_cases)
      case (Local n2 I2)
      hence n2: "n2 \<in> theNFTBoth cl dl" "n2 < length cl" "n2 < length dl"
      and I2: "I2 \<in> P n2" and II2: "II2 = shift cl n2 I2" using l by auto
      hence G2_def: "?G II2 = shift dl n2 (F n2 I2)" using l P by auto
      have Pn2: "part {..< brn (dl!n2)} (F n2 ` (P n2))" "{} \<notin> F n2 ` (P n2)"
      using n2 FP by auto
      have F2_in: "F n2 I2 \<in> F n2 ` (P n2)" using I2 by simp
      hence Fn2I2: "F n2 I2 \<noteq> {}" "F n2 I2 \<subseteq> {..< brn (dl!n2)}"
      using Pn2 by (blast, unfold part_def, blast)
      hence G2: "?G II2 \<noteq> {}" "?G II2 \<subseteq> {brnL dl n2 ..<+ brn (dl!n2)}"
      unfolding G2_def by simp_all
      (*  *)
      have n12: "n1 = n2" using n1 n2 G1 G2 G brnL_Int by blast
      have "F n1 I1 = F n2 I2" using G unfolding G1_def G2_def n12 by simp
      hence "I1 = I2" using I1 I2 n1 F unfolding n12 inj_on_def by blast
      thus ?thesis unfolding II1 II2 n12 by simp
    qed
  qed
qed

lemma inj_on_singl:
assumes "inj_on f A" and "a0 \<notin> A" and "\<And> a. a \<in> A \<Longrightarrow> f a \<noteq> f a0"
shows "inj_on f ({a0} Un A)"
using assms unfolding inj_on_def by fastforce

lemma UNlift01_inj_on:
assumes l: "length cl = length dl"
and P: "\<And> n. n < length cl \<Longrightarrow> part {..< brn (cl!n)} (P n) \<and> {} \<notin> P n"
and FP: "\<And> n. n < length dl \<Longrightarrow> part {..< brn (dl!n)} (F n ` (P n)) \<and> {} \<notin> F n ` (P n)"
and F: "\<And> n. n < length cl \<Longrightarrow> inj_on (F n) (P n)"
shows "inj_on (UNlift01 cl dl P F) (UNpart01 cl dl P)"
unfolding UNpart01_def proof(rule inj_on_singl)
  show "inj_on (UNlift01 cl dl P F) (UNpart1 cl dl P)"
  apply (rule UNlift01_inj_on_UNpart1) using assms by auto
next
  show "BrnFT cl dl \<notin> UNpart1 cl dl P"
  apply(rule BrnFT_notIn_UNpart1) using l P by auto
next
  let ?Q = "%n. F n ` (P n)"
  fix II assume "II \<in> UNpart1 cl dl P"
  hence "UNlift01 cl dl P F II \<noteq> BrnFT dl cl"
  proof(cases rule: UNpart1_cases)
    case (Local n I)
    hence n: "n \<in> theNFTBoth cl dl" "n \<in> theNFTBoth dl cl" "n < length cl" "n < length dl"
    and I: "I \<in> P n" and II: "II = shift cl n I" using l theNFTBoth_sym by auto
    have "shift dl n (F n I) \<in> UNpart1 dl cl ?Q"
    unfolding UNpart1_def shift_def using n I by auto
    hence "shift dl n (F n I) \<noteq> BrnFT dl cl"
    using BrnFT_notIn_UNpart1[of dl cl ?Q] n l FP by auto
    thus ?thesis unfolding II using n I l P by simp
  qed
  thus "UNlift01 cl dl P F II \<noteq> UNlift01 cl dl P F (BrnFT cl dl)" by simp
qed

lemma UNlift01_UNpart1:
assumes l: "length cl = length dl"
and P: "\<And> n. n < length cl \<Longrightarrow> part {..< brn (cl!n)} (P n) \<and> {} \<notin> P n"
shows "(UNlift01 cl dl P F) ` (UNpart1 cl dl P) = UNpart1 dl cl (%n. F n ` (P n))" (is "?G ` ?Q = ?R")
proof safe
  fix II assume II: "II \<in> ?Q"
  thus "?G II \<in> ?R"
  proof(cases rule: UNpart1_cases)
    case (Local n I)
    hence n: "n \<in> theNFTBoth cl dl" "n \<in> theNFTBoth dl cl" "n < length cl"
    "n < length dl" and I: "I \<in> P n"
    and II: "II = shift cl n I" using l theNFTBoth_sym by auto
    hence G: "?G II = shift dl n (F n I)" using l P by simp
    show ?thesis using n I unfolding G UNpart1_def by auto
  qed
next
  fix JJ assume JJ: "JJ \<in> ?R"
  thus "JJ \<in> ?G ` ?Q"
  proof(cases rule: UNpart1_cases)
    case (Local n J)
    hence n: "n \<in> theNFTBoth cl dl" "n \<in> theNFTBoth dl cl" "n < length cl" "n < length dl"
    and J: "J \<in> F n ` (P n)"
    and JJ: "JJ = shift dl n J" using l theNFTBoth_sym by auto
    then obtain I where I: "I \<in> P n" and "J = F n I" by auto
    hence "JJ = shift dl n (F n I)" using JJ by simp
    also have "... = UNlift01 cl dl P F (shift cl n I)" using n I l P by simp
    finally have JJ: "JJ = UNlift01 cl dl P F (shift cl n I)" .
    show ?thesis using n l I unfolding JJ UNpart1_def by auto
  qed
qed

lemma UNlift01_UNpart01:
assumes l: "length cl = length dl"
and P: "\<And> n. n < length cl \<Longrightarrow> part {..< brn (cl!n)} (P n) \<and> {} \<notin> P n"
shows "(UNlift01 cl dl P F) ` (UNpart01 cl dl P) = UNpart01 dl cl (%n. F n ` (P n))"
using assms UNlift01_UNpart1[of cl dl P] unfolding UNpart01_def by auto

lemma emp_UNlift01_UNpart1:
assumes l: "length cl = length dl"
and P: "\<And> n. n < length cl \<Longrightarrow> part {..< brn (cl!n)} (P n) \<and> {} \<notin> P n"
and FP: "\<And> n. n < length dl \<Longrightarrow> {} \<notin> F n ` (P n)"
shows "{} \<notin> (UNlift01 cl dl P F) ` (UNpart1 cl dl P)" (is "{} \<notin> ?R")
proof-
  have R: "?R = UNpart1 dl cl (%n. F n ` (P n))"
  apply(rule UNlift01_UNpart1) using assms by auto
  show ?thesis unfolding R apply(rule emp_UNpart1) using FP by simp
qed

lemma emp_UNlift01_UNpart01:
assumes l: "length cl = length dl"
and P: "\<And> n. n < length cl \<Longrightarrow> part {..< brn (cl!n)} (P n) \<and> {} \<notin> P n"
and FP: "\<And> n. n < length dl \<Longrightarrow> {} \<notin> F n ` (P n)"
shows "{} \<notin> (UNlift01 cl dl P F) ` (UNpart01 cl dl P - {BrnFT cl dl})"
(is "{} \<notin> ?U ` ?V")
proof-
  have V: "?V = UNpart1 cl dl P" apply(rule UNpart1_UNpart01[THEN sym])
  using assms by auto
  show ?thesis unfolding V apply(rule emp_UNlift01_UNpart1)
  using assms by auto
qed

lemma part_UNlift01_UNpart1:
assumes l: "length cl = length dl" and dl: "properL dl"
and P: "\<And> n. n < length cl \<Longrightarrow> part {..< brn (cl!n)} (P n) \<and> {} \<notin> P n"
and FP: "\<And> n. n < length dl \<Longrightarrow> part {..< brn (dl!n)} (F n ` (P n))"
shows "part (BrnNFT dl cl) ((UNlift01 cl dl P F) ` (UNpart1 cl dl P))" (is "part ?C ?R")
proof-
  let ?Q = "%n. F n ` (P n)"
  have R: "?R = UNpart1 dl cl ?Q"
  apply(rule UNlift01_UNpart1[of cl dl P F]) using assms by auto
  show ?thesis unfolding R apply(rule part_UNpart1) using dl l FP by auto
qed

lemma part_UNlift01_UNpart01:
assumes l: "length cl = length dl" and dl: "properL dl"
and P: "\<And> n. n < length cl \<Longrightarrow> part {..< brn (cl!n)} (P n) \<and> {} \<notin> P n"
and FP: "\<And> n. n < length dl \<Longrightarrow> part {..< brn (dl!n)} (F n ` (P n)) \<and> {} \<notin> (F n ` (P n))"
shows "part {..< brnL dl (length dl)} ((UNlift01 cl dl P F) ` (UNpart01 cl dl P))"
(is "part ?K ?R")
proof-
  let ?G = "UNlift01 cl dl P F" let ?Q = "%n. F n ` (P n)"
  have R: "?R = {?G (BrnFT cl dl)} \<union> ?G ` (UNpart1 cl dl P)"
  unfolding UNpart01_def by simp
  show ?thesis unfolding R apply(rule part_Un_singl2[of _ _ "BrnNFT dl cl"])
  using assms part_UNlift01_UNpart1
  apply(force, force)
  using assms apply simp apply(rule BrnFT_Int_UNpart1[of dl cl ?Q])
  apply(force, force) using UNlift01_UNpart1 by auto
qed

(* fixme: cont *)
lemma diff_frac_eq_1:
assumes "b \<noteq> (0::real)"
shows "1 - a / b = (b - a) / b"
by (metis assms diff_divide_distrib divide_self_if)

lemma diff_frac_eq_2:
assumes "b \<noteq> (1::real)"
shows "1 - (a - b) / (1 - b) = (1 - a) / (1 - b)"
(is "?L = ?R")
proof-
  have b: "1 - b \<noteq> 0" using assms by simp
  hence "?L = (1 - b - (a - b)) / (1 - b)"  (is "?L = ?A / ?B")
  using diff_frac_eq_1 by blast
  also have "?A = 1 - a" by simp
  finally show ?thesis by simp
qed

lemma triv_div_mult:
assumes vSF: "vSF \<noteq> (1::real)"
and L: "L = (K - vSF) / (1 - vSF)" and Ln: "L \<noteq> 1"
shows "(VS / (1 - vSF) * V) / (1 - L) = (VS * V) / (1 - K)"
(is "?A = ?B")
proof-
  have vSF_0: "1 - vSF \<noteq> 0" using vSF by simp
  {assume "K = 1"
   hence "L = 1" using L vSF by simp
   hence False using Ln by simp
  }
  hence Kn: "K \<noteq> 1" by auto
  hence K_0: "1 - K \<noteq> 0" by simp
  have "1 - L = (1 - K) / (1 - vSF)" unfolding L using vSF diff_frac_eq_2 by blast
  hence "?A = (VS / (1 - vSF) * V) / ((1 - K) / (1 - vSF))" by simp
  also have "... = ?B" using vSF_0 K_0 by auto
  finally show ?thesis .
qed
(* end fixme *)

lemma ss_wt_ParT_UNlift01:
assumes l: "length cl = length dl"
and cldl: "properL cl" "properL dl" and II: "II \<in> UNpart01 cl dl P - {BrnFT cl dl}"
and P: "\<And> n. n < length cl \<Longrightarrow> part {..< brn (cl!n)} (P n) \<and> {} \<notin> P n"
and FP: "\<And> n. n < length dl \<Longrightarrow> part {..< brn (dl!n)} (F n ` (P n))"
and sw:
"\<And>n I. \<lbrakk>n < length cl; I \<in> P n\<rbrakk> \<Longrightarrow>
     sum (wt (cl ! n) s) I =
     sum (wt (dl ! n) t) (F n I)"
and st: "s \<approx> t"
and le1: "sum (wt (ParT cl) s) (BrnFT cl dl) < 1"
"sum (wt (ParT dl) t) (BrnFT dl cl) < 1"
shows
"sum (wt (ParT cl) s) II /
 (1 - sum (wt (ParT cl) s) (BrnFT cl dl)) =
 sum (wt (ParT dl) t) (UNlift01 cl dl P F II) /
 (1 - sum (wt (ParT dl) t) (BrnFT dl cl))"
(is "sum ?vP II / (1 - sum ?vP ?II_0) =
     sum ?wP ?JJ / (1 - sum ?wP ?JJ_0)")
proof-
  let ?N = "length cl"
  let ?vS = "%n. 1 / ?N" let ?wS = "%n. 1 / (length dl)"
  let ?vSF = "WtFT cl" let ?wSF = "WtFT dl"
  let ?ss = "%n. s" let ?tt = "%n. t"
  let ?v = "%n. wt (cl ! n) (?ss n)" let ?w = "%n. wt (dl ! n) (?tt n)"
  (*  *)
  have sstt: "\<And> n. n < ?N \<Longrightarrow> ?ss n \<approx> ?tt n"
  using st l by auto
  have vSwS: "\<And> n. n < ?N \<Longrightarrow> ?vS n = ?wS n" and sstt: "\<And> n. n < ?N \<Longrightarrow> ?ss n \<approx> ?tt n"
  using assms by auto
  have nf: "?vSF \<noteq> 1" "?wSF \<noteq> 1" using le1 cldl l by auto
  have theFT_theNFT[simp]:
  "\<And> n. n \<in> theFT dl - theFT cl \<Longrightarrow> n < length cl \<and> \<not> finished (cl ! n)"
  "\<And> n. n \<in> theFT cl - theFT dl \<Longrightarrow> n < length dl \<and> \<not> finished (dl ! n)"
  unfolding theFT_def using l by auto
  have sum_v[simp]:
  "\<And> n. n < length cl \<Longrightarrow> sum (?v n) {..< brn (cl ! n)} = 1"
  using cldl by auto
  have sum_w[simp]:
  "\<And> n. n < length dl \<Longrightarrow> sum (?w n) {..< brn (dl ! n)} = 1"
  using cldl by auto
  have theFTOne: "theFTOne cl dl = theFT dl - theFT cl \<union> theFT cl"
  "theFTOne dl cl = theFT cl - theFT dl \<union> theFT dl"
  unfolding theFTOne_def by blast+
  have sum_vS_wS: "sum ?vS (theFTOne cl dl) = sum ?wS (theFTOne dl cl)"
  unfolding theFTOne_sym[of cl dl] apply (rule sum.cong)
  using vSwS l unfolding theFTOne_def theFT_def theNFT_def by auto
  (*  *)
  have II: "II \<in> UNpart1 cl dl P" using II l P UNpart1_UNpart01 by blast
  thus ?thesis
  proof(cases rule: UNpart1_cases)
    case (Local n I)
    hence n: "n < ?N" "n < length dl" "n \<in> theNFTBoth cl dl"
    "\<not> finished (cl!n)"  "\<not> finished (dl!n)"
    and I: "I \<in> P n"
    and II: "II = shift cl n I" using l by auto
    have I_sub: "I \<subseteq> {..< brn (cl!n)}" using n I P unfolding part_def by blast
    hence FnI_sub: "F n I \<subseteq> {..< brn (dl!n)}" using n I FP unfolding part_def by blast
    have JJ: "?JJ = shift dl n (F n I)"
    unfolding II using l P n I by simp
    (*  *)
    have "sum ?vP ?II_0 =
    sum (%n. sum ?vP {brnL cl n..<+brn (cl ! n)}) (theFTOne cl dl)"
    unfolding BrnFT_def apply(rule sum.UNION_disjoint)
    using brnL_Int l by auto
    also have "... =
    sum
      (%n. sum ?vP {brnL cl n..<+brn (cl ! n)})
      ((theFT dl - theFT cl) \<union> theFT cl)" unfolding theFTOne_def
    by (metis Un_Diff_cancel2 Un_commute)
    also have "... =
    sum
      (%n. sum ?vP {brnL cl n..<+brn (cl ! n)})
      (theFT dl - theFT cl) +
    sum
      (%n. sum ?vP {brnL cl n..<+brn (cl ! n)})
      (theFT cl)" (is "... = ?L + ?R")
    apply(rule sum.union_disjoint) by auto
    also have "?R = 0" apply(rule sum.neutral) using cldl nf by auto
    finally have "sum ?vP ?II_0 = ?L" by simp
    also have "?L =
    sum
      (%n. ?vS n / (1 - ?vSF) * sum (?v n) {..< brn (cl ! n)})
      (theFT dl - theFT cl)"
    apply(intro sum.cong) using cldl nf
    using theFT_theNFT sum_wt_ParT_notWtFT_notFinished[of cl] by metis+
    also have "... =
    sum
      (%n. ?vS n * sum (?v n) {..< brn (cl ! n)})
      (theFT dl - theFT cl) / (1 - ?vSF)" (is "... = ?L / (1 - ?vSF)")
    unfolding times_divide_eq_left sum_divide_distrib by simp
    also have "?L = sum ?vS (theFT dl - theFT cl)"
    apply(intro sum.cong) by auto
    finally have
    "sum ?vP ?II_0 = (sum ?vS (theFT dl - theFT cl)) / (1 - ?vSF)"
    (is "... = ?L / ?R") by simp
    also have "?L = sum ?vS (theFTOne cl dl) - ?vSF"
    unfolding eq_diff_eq WtFT_def theFTOne
    apply(rule sum.union_disjoint[THEN sym]) by auto
    finally have vPII0: "sum ?vP ?II_0 =
    (sum ?vS (theFTOne cl dl) - ?vSF) / (1 - ?vSF)" by simp
    (*  *)
    (*  *)
    have "sum ?wP ?JJ_0 =
    sum (%n. sum ?wP {brnL dl n..<+brn (dl ! n)}) (theFTOne dl cl)"
    unfolding BrnFT_def apply(rule sum.UNION_disjoint)
    unfolding theFTOne_def theFT_def apply (force, force, clarify)
    apply(rule brnL_Int) using l by auto
    also have "... =
    sum
      (%n. sum ?wP {brnL dl n..<+ brn (dl ! n)})
      ((theFT cl - theFT dl) \<union> theFT dl)" unfolding theFTOne_def
    by (metis Un_Diff_cancel2 Un_commute)
    also have "... =
    sum
      (%n. sum ?wP {brnL dl n..<+brn (dl ! n)})
      (theFT cl - theFT dl) +
    sum
      (%n. sum ?wP {brnL dl n..<+brn (dl ! n)})
      (theFT dl)" (is "... = ?L + ?R")
    apply(rule sum.union_disjoint) by auto
    also have "?R = 0" apply(rule sum.neutral) using cldl nf by auto
    finally have "sum ?wP ?JJ_0 = ?L" by simp
    also have "?L =
    sum
      (%n. ?wS n / (1 - ?wSF) * sum (?w n) {..< brn (dl ! n)})
      (theFT cl - theFT dl)"
    apply(intro sum.cong) using cldl nf
    using theFT_theNFT sum_wt_ParT_notWtFT_notFinished[of dl] by metis+
    also have "... =
    sum
      (%n. ?wS n * sum (?w n) {..< brn (dl ! n)})
      (theFT cl - theFT dl) / (1 - ?wSF)" (is "... = ?L / (1 - ?wSF)")
    unfolding times_divide_eq_left sum_divide_distrib by simp
    also have "?L = sum ?wS (theFT cl - theFT dl)"
    apply(intro sum.cong) by auto
    finally have
    "sum ?wP ?JJ_0 = (sum ?wS (theFT cl - theFT dl)) / (1 - ?wSF)"
    (is "... = ?L / ?R") by simp
    also have "?L = sum ?wS (theFTOne dl cl) - ?wSF"
    unfolding eq_diff_eq WtFT_def theFTOne
    apply(rule sum.union_disjoint[THEN sym]) by auto
    finally have wPJJ0: "sum ?wP ?JJ_0 =
    (sum ?wS (theFTOne dl cl) - ?wSF) / (1 - ?wSF)" by simp
    (*  *)
    have "sum ?vP II / (1 - sum ?vP ?II_0) =
    (?vS n) / (1 - ?vSF) * (sum (?v n) I) / (1 - sum ?vP ?II_0)"
    unfolding II using n nf cldl I_sub by simp
    also have "... =
    (?vS n) * (sum (?v n) I) / (1 - sum ?vS (theFTOne cl dl))"
      using nf(1) vPII0 by (rule triv_div_mult) (insert le1, auto)
    also have "... =
    (?wS n) * (sum (?w n) (F n I)) / (1 - sum ?wS (theFTOne dl cl))"
    using n vSwS[of n] sw[of n I] I unfolding sum_vS_wS by simp
    also have "... =
    (?wS n) / (1 - ?wSF) * (sum (?w n) (F n I)) / (1 - sum ?wP ?JJ_0)"
      using nf(2) wPJJ0 by (rule triv_div_mult[THEN sym]) (insert le1, auto)
    also have "... = sum ?wP ?JJ / (1 - sum ?wP ?JJ_0)"
    unfolding JJ using n nf cldl FnI_sub by simp
    finally show ?thesis .
  qed
qed

(* *)

definition thetaZOParT where
"thetaZOParT \<equiv>
 {(ParT cl, ParT dl) |
    cl dl.
      properL cl \<and> properL dl \<and> SbisL cl dl}"

lemma cont_eff_ParT_BrnFT_L:
assumes l: "length cl = length dl"
and cldl: "properL cl" "properL dl" "SbisL cl dl"
and ii: "ii \<in> BrnFT cl dl"
and eff_cont:
"\<And>n I i j. \<lbrakk>n < length cl; I \<in> P n; i \<in> I; j \<in> F n I\<rbrakk> \<Longrightarrow>
  eff (cl!n) s i \<approx> eff (dl!n) t j \<and>
  cont (cl!n) s i \<approx>s cont (dl!n) t j"
shows
"s \<approx> eff (ParT cl) s ii \<and>
 (cont (ParT cl) s ii, ParT dl) \<in> thetaZOParT"
(is "?eff \<and> ?cont")
proof-
  let ?N = "length cl" let ?p = "%n. 1 / length cl" let ?ss = "%n. s"
  from ii show ?thesis
  proof(cases rule: BrnFT_elim)
    case (Local n i)
    hence n: "n \<in> theFTOne cl dl"
    and i: "i < brn (cl ! n)" and ii: "ii = brnL cl n + i" by auto
    from n have "n < length cl" "n < length dl" using l cldl
    unfolding theFTOne_def theFT_def by auto note n = this n
    have discr: "discr (cl!n)"
    proof(cases "finished (cl!n)")
      case True
      thus ?thesis using n cldl discr_finished by auto
    next
      case False
      hence "finished (dl!n)" using n unfolding theFTOne_def theFT_def by auto
      moreover have "proper (cl!n)" and "proper (dl!n)" and "cl!n \<approx>01 dl!n"
      using n cldl by auto
      ultimately show ?thesis using ZObis_finished_discr_L by blast
    qed
    hence eff: "?ss n \<approx> eff (cl!n) (?ss n) i"
    and cont: "proper (cont (cl!n) (?ss n) i) \<and> discr (cont (cl!n) (?ss n) i)"
    using i cldl n by auto
    show ?thesis
    proof
      have "s \<approx> eff (cl!n) (?ss n) i" using eff n indis_trans by blast
      thus ?eff using i n cldl unfolding ii by simp
    next
      have "cont (cl!n) (?ss n) i \<approx>s cl!n" using discr cont cldl n by auto
      moreover have "cl!n \<approx>s dl!n" using cldl n by auto
      ultimately have "cont (cl!n) (?ss n) i \<approx>s dl!n" using Sbis_trans by blast
      thus ?cont using i n cldl unfolding ii thetaZOParT_def by auto
    qed
  qed
qed

lemma cont_eff_ParT_BrnFT_R:
assumes l: "length cl = length dl"
and cldl: "properL cl" "properL dl" "SbisL cl dl"
and jj: "jj \<in> BrnFT dl cl"
and eff_cont:
"\<And>n I i j. \<lbrakk>n < length cl; I \<in> P n; i \<in> I; j \<in> F n I\<rbrakk> \<Longrightarrow>
  eff (cl!n) s i \<approx> eff (dl!n) t j \<and> cont (cl!n) s i \<approx>s cont (dl!n) t j"
shows
"t \<approx> eff (ParT dl) t jj \<and>
 (ParT cl, cont (ParT dl) t jj) \<in> thetaZOParT"
(is "?eff \<and> ?cont")
proof-
  let ?N = "length dl"  let ?q = "%n. 1 /?N" let ?tt = "%n. t"
  from jj show ?thesis
  proof(cases rule: BrnFT_elim)
    case (Local n j)
    hence n: "n \<in> theFTOne dl cl"
    and j: "j < brn (dl ! n)" and jj: "jj = brnL dl n + j" by auto
    from n have "n < length cl" "n < length dl" using l cldl
    unfolding theFTOne_def theFT_def by auto note n = this n
    have discr: "discr (dl!n)"
    proof(cases "finished (dl!n)")
      case True
      thus ?thesis using n cldl discr_finished by auto
    next
      case False
      hence "finished (cl!n)" using n unfolding theFTOne_def theFT_def by auto
      moreover have "proper (cl!n)" and "proper (dl!n)" and "cl!n \<approx>01 dl!n"
      using n cldl by auto
      ultimately show ?thesis using ZObis_finished_discr_R by blast
    qed
    hence eff: "?tt n \<approx> eff (dl!n) (?tt n) j"
    and cont: "proper (cont (dl!n) (?tt n) j) \<and> discr (cont (dl!n) (?tt n) j)"
    using j cldl n by auto
    show ?thesis
    proof
      have "t \<approx> eff (dl!n) (?tt n) j" using eff n indis_trans by blast
      thus ?eff using j n cldl unfolding jj by simp
    next
      have "cl!n \<approx>s dl!n" using cldl n by auto
      moreover have "dl!n \<approx>s cont (dl!n) (?tt n) j" using discr cont cldl n by auto
      ultimately have "cl!n \<approx>s cont (dl!n) (?tt n) j" using Sbis_trans by blast
      thus ?cont using j n cldl unfolding jj thetaZOParT_def by simp
    qed
  qed
qed

lemma cont_eff_ParT_UNlift01:
assumes l: "length cl = length dl"
and cldl: "properL cl" "properL dl" "SbisL cl dl"
and II: "II \<in> UNpart01 cl dl P - {BrnFT cl dl}"
and ii: "ii \<in> II" and jj: "jj \<in> UNlift01 cl dl P F II"
and P: "\<And> n. n < length cl \<Longrightarrow> part {..< brn (cl!n)} (P n) \<and> {} \<notin> P n"
and FP: "\<And> n. n < length dl \<Longrightarrow> part {..< brn (dl!n)} (F n ` (P n))"
and eff_cont:
"\<And>n I i j. \<lbrakk>n < length cl; I \<in> P n; i \<in> I; j \<in> F n I\<rbrakk> \<Longrightarrow>
  eff (cl!n) s i \<approx>
  eff (dl!n) t j \<and>
  cont (cl!n) s i \<approx>s
  cont (dl!n) t j"
and st: "s \<approx> t"
shows
"eff (ParT cl) s ii \<approx> eff (ParT dl) t jj \<and>
 (cont (ParT cl) s ii, cont (ParT dl) t jj) \<in> thetaZOParT"
(is "?eff \<and> ?cont")
proof-
  let ?N = "length cl"
  let ?p = "%n. 1 / ?N" let ?q = "%n. 1 / (length dl)"
  let ?ss = "%n. s" let ?tt = "%n. t"
  have sstt: "\<And> n. n < ?N \<Longrightarrow> ?ss n \<approx> ?tt n" using st l by auto
  have pq: "\<And> n. n < ?N \<Longrightarrow> ?p n = ?q n" and sstt: "\<And> n. n < ?N \<Longrightarrow> ?ss n \<approx> ?tt n"
  using assms l by auto
  have II: "II \<in> UNpart1 cl dl P" using II l P UNpart1_UNpart01 by blast
  thus ?thesis
  proof(cases rule: UNpart1_cases)
    case (Local n I)
    hence n: "n < ?N" "n < length dl" "n \<in> theNFTBoth cl dl"
    "\<not> finished (cl!n)"  "\<not> finished (dl!n)"
    and I: "I \<in> P n" and II: "II = shift cl n I" using l by auto
    from ii II obtain i where i: "i \<in> I" and ii: "ii = brnL cl n + i"
    unfolding shift_def by auto
    have "i < brn (cl!n)" using i I n P unfolding part_def by blast note i = this i
    have jj: "jj \<in> shift dl n (F n I)" using jj P n I l unfolding II by simp
    from jj II obtain j where j: "j \<in> F n I" and jj: "jj = brnL dl n + j"
    unfolding shift_def by auto
    have "j < brn (dl!n)" using j I n FP unfolding part_def by blast note j = this j
    show ?thesis
    proof
      have "eff (cl!n) (?ss n) i \<approx> eff (dl!n) (?tt n) j"
      using n I i j eff_cont by blast
      thus ?eff unfolding ii jj using st cldl n i j by simp
    next
      have 1: "cont (cl!n) (?ss n) i \<approx>s cont (dl!n) (?tt n) j"
      using n I i j eff_cont by blast
      have "(cont (ParT cl) s ii, cont (ParT dl) t jj) =
            (ParT (cl[n := cont (cl ! n) (?ss n) i]),
              ParT (dl[n := cont (dl ! n) (?tt n) j]))"
      (is "?A = ?B")
      unfolding ii jj using n i j cldl by simp
      moreover have "?B \<in> thetaZOParT"
      unfolding thetaZOParT_def apply (simp, safe)
      apply(intro properL_update)
        using cldl apply force
        apply(rule proper_cont) using cldl i n apply (force,force)
      apply(intro properL_update)
        using cldl apply force
        apply(rule proper_cont) using cldl j n apply (force,force)
      apply(intro SbisL_update)
      using 1 cldl n i apply (force,force)
      done
      ultimately show ?cont by auto
    qed
  qed
qed

lemma thetaZOParT_ZOretr: "thetaZOParT \<subseteq> ZOretr (thetaZOParT)"
unfolding ZOretr_def matchC_LC_def proof safe
  fix c d s t
  assume c_d: "(c, d) \<in> thetaZOParT" and st: "s \<approx> t"
  then obtain cl dl where
  c: "c = ParT cl" and d: "d = ParT dl" and
  cldl: "properL cl" "properL dl" "SbisL cl dl"
  unfolding thetaZOParT_def by blast
  let ?N = "length cl"
  let ?ss = "%n. s" let ?tt = "%n. t"
  have N: "?N = length dl" using cldl by simp
  have sstt: "\<And> n. n < ?N \<Longrightarrow> ?ss n \<approx> ?tt n" using st N by auto
  let ?phi = "%n PFn. mC_C Sbis (cl ! n) (dl ! n) (?ss n) (?tt n) (fst PFn) (snd PFn)"
  {fix n assume n: "n < ?N"
   hence "cl ! n \<approx>s dl ! n" using cldl by auto
   hence "\<exists> PFn. ?phi n PFn" using n Sbis_mC_C sstt by fastforce
  }
  then obtain PF where phi: "\<And>n. n < ?N \<Longrightarrow> ?phi n (PF n)"
  using bchoice[of "{..< ?N}" ?phi] by blast
  define P F where "P = fst o PF" and "F = snd o PF"
  have m: "\<And>n. n < ?N \<Longrightarrow> mC_C Sbis (cl ! n) (dl ! n) (?ss n) (?tt n) (P n) (F n)"
  using phi unfolding P_def F_def by auto
  (*  *)
  have brn_c: "brn c = brnL cl ?N" unfolding c by simp
  have brn_d: "brn d = brnL dl (length dl)" unfolding d by simp
  have P: "\<And>n. n < ?N \<Longrightarrow> part {..< brn (cl ! n)} (P n) \<and> {} \<notin> (P n)"
  using m unfolding m_defsAll part_def by auto
  have FP: "\<And>n. n < length dl \<Longrightarrow> part {..< brn (dl ! n)} (F n ` (P n)) \<and> {} \<notin> F n ` (P n)"
  using m N unfolding m_defsAll part_def by auto
  have F: "\<And>n. n < ?N \<Longrightarrow> inj_on (F n) (P n)" using m unfolding m_defsAll by auto
  have sw: "\<And>n I. \<lbrakk>n < length cl; I \<in> P n\<rbrakk> \<Longrightarrow>
     sum (wt (cl ! n) (?ss n)) I = sum (wt (dl ! n) (?tt n)) (F n I)"
  using m unfolding mC_C_def mC_C_wt_def by auto
  have eff_cont: "\<And>n I i j. \<lbrakk>n < length cl; I \<in> P n; i \<in> I; j \<in> F n I\<rbrakk> \<Longrightarrow>
     eff (cl!n) (?ss n) i \<approx> eff (dl!n) (?tt n) j \<and> cont (cl!n) (?ss n) i \<approx>s cont (dl!n) (?tt n) j"
  using m unfolding mC_C_def mC_C_eff_cont_def by auto
  (*  *)
  define II0 where "II0 = BrnFT cl dl"
  define Q G where "Q = UNpart01 cl dl P" and "G = UNlift01 cl dl P F"
  note defi = II0_def Q_def G_def brn_c brn_d
  show "\<exists>II0 Q G. mC_ZOC (thetaZOParT) c d s t II0 Q G"
  apply(rule exI[of _ II0]) apply(rule exI[of _ Q]) apply(rule exI[of _ G])
  unfolding mC_ZOC_def proof (intro conjI)
    show "mC_ZOC_part c d s t II0 Q G" unfolding mC_ZOC_part_def proof(intro conjI)
      show "{} \<notin> Q - {II0}" unfolding defi apply(rule emp_UNpart01) using P by simp
      show "{} \<notin> G ` (Q - {II0})" unfolding defi
      apply(rule emp_UNlift01_UNpart01) using N P FP by auto
      show "II0 \<in> Q" unfolding defi by simp
      show "part {..<brn c} Q"
      unfolding defi apply(rule part_UNpart01) using cldl P by auto
      show "part {..<brn d} (G ` Q)"
      unfolding defi apply(rule part_UNlift01_UNpart01) using N cldl P FP by auto
    qed
  next
    show "inj_on G Q"
    unfolding defi apply(rule UNlift01_inj_on) using N P FP F by auto
  next
    show "mC_ZOC_wt c d s t II0 Q G"
    unfolding mC_ZOC_wt_def proof (intro impI ballI, elim conjE)
      fix II assume II: "II \<in> Q - {II0}" and
      le1: "sum (wt c s) II0 < 1" "sum (wt d t) (G II0) < 1"
      thus
      "sum (wt c s) II / (1 - sum (wt c s) II0) =
       sum (wt d t) (G II) / (1 - sum (wt d t) (G II0))"
      unfolding c d defi UNlift01_BrnFT apply(intro ss_wt_ParT_UNlift01)
      using N cldl II P FP sw st by auto
    qed
  next
    show "mC_ZOC_eff_cont0 (thetaZOParT) c d s t II0 G"
    unfolding mC_ZOC_eff_cont0_def
    proof(intro conjI[OF ballI ballI])
      fix ii assume "ii \<in> II0" thus "s \<approx> eff c s ii \<and> (cont c s ii, d) \<in> thetaZOParT"
      unfolding defi c d apply(intro cont_eff_ParT_BrnFT_L)
      using N cldl P FP eff_cont st by (auto intro!: )
    next
      fix jj assume "jj \<in> G II0"
      hence "jj \<in> BrnFT dl cl" unfolding defi UNlift01_BrnFT by simp
      thus "t \<approx> eff d t jj \<and> (c, cont d t jj) \<in> thetaZOParT"
      unfolding defi c d apply(intro cont_eff_ParT_BrnFT_R)
      using N cldl P FP eff_cont st by auto
    qed
  next
    show "mC_ZOC_eff_cont (thetaZOParT) c d s t II0 Q G"
    unfolding mC_ZOC_eff_cont_def proof (intro allI impI, elim conjE)
      fix II ii jj assume II: "II \<in> Q - {II0}" and ii: "ii \<in> II" and jj: "jj \<in> G II"
      thus "eff c s ii \<approx> eff d t jj \<and> (cont c s ii, cont d t jj) \<in> thetaZOParT"
      unfolding defi c d apply(intro cont_eff_ParT_UNlift01)
      using N cldl P FP eff_cont st by auto
    qed
  qed
qed

lemma thetaZOParT_ZObis: "thetaZOParT \<subseteq> ZObis"
using ZObis_raw_coind thetaZOParT_ZOretr by auto

theorem ParT_ZObis[simp]:
assumes "properL cl" and "properL dl" and "SbisL cl dl"
shows "ParT cl \<approx>01 ParT dl"
using assms thetaZOParT_ZObis unfolding thetaZOParT_def by blast


end (* context PL_Indis *)
(*******************************************)


end
