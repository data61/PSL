section \<open>Syntactic Criteria\<close>
theory Syntactic_Criteria
  imports Compositionality
begin

context PL_Indis
begin

lemma proper_intros[intro]:
  "proper Done"
  "proper (Atm atm)"
  "proper c1 \<Longrightarrow> proper c2 \<Longrightarrow> proper (Seq c1 c2)"
  "proper c1 \<Longrightarrow> proper c2 \<Longrightarrow> proper (Ch ch c1 c2)"
  "proper c \<Longrightarrow> proper (While tst c)"
  "properL cs \<Longrightarrow> proper (Par cs)"
  "properL cs \<Longrightarrow> proper (ParT cs)"
  "(\<And>c. c \<in> set cs \<Longrightarrow> proper c) \<Longrightarrow> cs \<noteq> [] \<Longrightarrow> properL cs"
  by auto

lemma discr:
  "discr Done"
  "presAtm atm \<Longrightarrow> discr (Atm atm)"
  "discr c1 \<Longrightarrow> discr c2 \<Longrightarrow> discr (Seq c1 c2)"
  "discr c1 \<Longrightarrow> discr c2 \<Longrightarrow> discr (Ch ch c1 c2)"
  "discr c \<Longrightarrow> discr (While tst c)"
  "properL cs \<Longrightarrow> (\<And>c. c \<in> set cs \<Longrightarrow> discr c) \<Longrightarrow> discr (Par cs)"
  "properL cs \<Longrightarrow> (\<And>c. c \<in> set cs \<Longrightarrow> discr c) \<Longrightarrow> discr (ParT cs)"
  by (auto intro!: discr_Par discr_ParT)

lemma siso:
  "compatAtm atm \<Longrightarrow> siso (Atm atm)"
  "siso c1 \<Longrightarrow> siso c2 \<Longrightarrow> siso (Seq c1 c2)"
  "compatCh ch \<Longrightarrow> siso c1 \<Longrightarrow> siso c2 \<Longrightarrow> siso (Ch ch c1 c2)"
  "compatTst tst \<Longrightarrow> siso c \<Longrightarrow> siso (While tst c)"
  "properL cs \<Longrightarrow> (\<And>c. c \<in> set cs \<Longrightarrow> siso c) \<Longrightarrow> siso (Par cs)"
  "properL cs \<Longrightarrow> (\<And>c. c \<in> set cs \<Longrightarrow> siso c) \<Longrightarrow> siso (ParT cs)"
  by (auto intro!: siso_Par siso_ParT)

lemma Sbis:
  "compatAtm atm \<Longrightarrow> Atm atm \<approx>s Atm atm"
  "siso c1 \<Longrightarrow> c2 \<approx>s c2 \<Longrightarrow> Seq c1 c2 \<approx>s Seq c1 c2"
  "proper c1 \<Longrightarrow> proper c2 \<Longrightarrow> c1 \<approx>s c1 \<Longrightarrow> discr c2 \<Longrightarrow> Seq c1 c2 \<approx>s Seq c1 c2"
  "compatCh ch \<Longrightarrow> c1 \<approx>s c1 \<Longrightarrow> c2 \<approx>s c2 \<Longrightarrow> Ch ch c1 c2 \<approx>s Ch ch c1 c2"
  "properL cs \<Longrightarrow> (\<And>c. c \<in> set cs \<Longrightarrow> c \<approx>s c) \<Longrightarrow> Par cs \<approx>s Par cs"
  by (auto intro!: Par_Sbis)

lemma ZObis:
  "compatAtm atm \<Longrightarrow> Atm atm \<approx>01 Atm atm"
  "siso c1 \<Longrightarrow> c2 \<approx>01 c2 \<Longrightarrow> Seq c1 c2 \<approx>01 Seq c1 c2"
  "proper c1 \<Longrightarrow> proper c2 \<Longrightarrow> c1 \<approx>01 c1 \<Longrightarrow> discr c2 \<Longrightarrow> Seq c1 c2 \<approx>01 Seq c1 c2"
  "compatCh ch \<Longrightarrow> c1 \<approx>01 c1 \<Longrightarrow> c2 \<approx>01 c2 \<Longrightarrow> Ch ch c1 c2 \<approx>01 Ch ch c1 c2"
  "properL cs \<Longrightarrow> (\<And>c. c \<in> set cs \<Longrightarrow> c \<approx>s c) \<Longrightarrow> ParT cs \<approx>01 ParT cs"
  by (auto intro!: ParT_ZObis)

lemma discr_imp_Sbis: "proper c \<Longrightarrow> discr c \<Longrightarrow> c \<approx>s c"
  by auto

lemma siso_imp_Sbis: "siso c \<Longrightarrow> c \<approx>s c"
  by auto

lemma Sbis_imp_ZObis: "c \<approx>s c \<Longrightarrow> c \<approx>01 c"
  by auto


(* The syntactic predicates: SC_\<phi> corresponds to the paper's overlined \<phi>: *) 

fun SC_discr where
  "SC_discr Done          \<longleftrightarrow> True"
| "SC_discr (Atm atm)     \<longleftrightarrow> presAtm atm"
| "SC_discr (Seq c1 c2)   \<longleftrightarrow> SC_discr c1 \<and> SC_discr c2"
| "SC_discr (Ch ch c1 c2) \<longleftrightarrow> SC_discr c1 \<and> SC_discr c2"
| "SC_discr (While tst c) \<longleftrightarrow> SC_discr c"
| "SC_discr (ParT cs) \<longleftrightarrow> (\<forall>c\<in>set cs. SC_discr c)"
| "SC_discr (Par cs)  \<longleftrightarrow> (\<forall>c\<in>set cs. SC_discr c)"

theorem SC_discr_discr[intro]: "proper c \<Longrightarrow> SC_discr c \<Longrightarrow> discr c"
  by (induct c) (auto intro!: discr)

fun SC_siso where
  "SC_siso Done           \<longleftrightarrow> True"
| "SC_siso (Atm atm)      \<longleftrightarrow> compatAtm atm"
| "SC_siso (Seq c1 c2)    \<longleftrightarrow> SC_siso c1 \<and> SC_siso c2"
| "SC_siso (Ch ch c1 c2)  \<longleftrightarrow> compatCh ch \<and> SC_siso c1 \<and> SC_siso c2"
| "SC_siso (While tst c)  \<longleftrightarrow> compatTst tst \<and> SC_siso c"
| "SC_siso (Par cs)   \<longleftrightarrow> (\<forall>c\<in>set cs. SC_siso c)"
| "SC_siso (ParT cs)  \<longleftrightarrow> (\<forall>c\<in>set cs. SC_siso c)"

theorem SC_siso_siso[intro]: "proper c \<Longrightarrow> SC_siso c \<Longrightarrow> siso c"
  by (induct c) (auto intro!: siso)

fun SC_Sbis where
  "SC_Sbis Done           \<longleftrightarrow> True"
| "SC_Sbis (Atm atm)      \<longleftrightarrow> compatAtm atm"
| "SC_Sbis (Seq c1 c2)    \<longleftrightarrow> (SC_siso c1 \<and> SC_Sbis c2) \<or>
                             (SC_Sbis c1 \<and> SC_discr c2) \<or>
                             SC_discr (Seq c1 c2) \<or> SC_siso (Seq c1 c2)"
| "SC_Sbis (Ch ch c1 c2)  \<longleftrightarrow> (if compatCh ch
                             then SC_Sbis c1 \<and> SC_Sbis c2
                             else (SC_discr (Ch ch c1 c2) \<or> SC_siso (Ch ch c1 c2)))"
| "SC_Sbis (While tst c)  \<longleftrightarrow> SC_discr (While tst c) \<or> SC_siso (While tst c)"
| "SC_Sbis (Par cs)   \<longleftrightarrow> (\<forall>c\<in>set cs. SC_Sbis c)"
| "SC_Sbis (ParT cs)  \<longleftrightarrow> SC_siso (ParT cs) \<or> SC_discr (ParT cs)"

theorem SC_siso_SCbis[intro]: "SC_siso c \<Longrightarrow> SC_Sbis c"
  by (induct c) auto

theorem SC_discr_SCbis[intro]: "SC_discr c \<Longrightarrow> SC_Sbis c"
  by (induct c) auto

declare SC_siso.simps[simp del]

declare SC_discr.simps[simp del]

theorem SC_Sbis_Sbis[intro]: "proper c \<Longrightarrow> SC_Sbis c \<Longrightarrow> c \<approx>s c"
  by (induct c)
     (auto intro: Sbis discr_imp_Sbis siso_imp_Sbis
           split: if_split_asm)

fun SC_ZObis where
  "SC_ZObis Done           \<longleftrightarrow> True"
| "SC_ZObis (Atm atm)      \<longleftrightarrow> compatAtm atm"
| "SC_ZObis (Seq c1 c2)    \<longleftrightarrow> (SC_siso c1 \<and> SC_ZObis c2) \<or>
                             (SC_ZObis c1 \<and> SC_discr c2) \<or>
                             SC_Sbis (Seq c1 c2)"
| "SC_ZObis (Ch ch c1 c2)  \<longleftrightarrow> (if compatCh ch
                             then SC_ZObis c1 \<and> SC_ZObis c2
                             else SC_Sbis (Ch ch c1 c2))"
| "SC_ZObis (While tst c)  \<longleftrightarrow> SC_Sbis (While tst c)"
| "SC_ZObis (Par cs)   \<longleftrightarrow> SC_Sbis (Par cs)"
| "SC_ZObis (ParT cs)  \<longleftrightarrow> (\<forall>c\<in>set cs. SC_Sbis c)"

theorem SC_Sbis_SC_ZObis[intro]: "SC_Sbis c \<Longrightarrow> SC_ZObis c"
  by (induct c) (auto simp: SC_siso.simps SC_discr.simps)

declare SC_Sbis.simps[simp del]

theorem SC_ZObis_ZObis: "proper c \<Longrightarrow> SC_ZObis c \<Longrightarrow> c \<approx>01 c"
  apply (induct c)
  apply (auto intro: Sbis_imp_ZObis ZObis split: if_split_asm)
  apply (auto intro!: ZObis(5))
  done

end

end
