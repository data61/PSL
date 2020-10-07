theory Syntactic_Criteria
  imports Compositionality
begin

context PL_Indis
begin

(* Table: Compositionality of during-execution noninterferences *)

lemma noWhile[intro]:
  "noWhile (Atm atm)"
  "noWhile c1 \<Longrightarrow> noWhile c2 \<Longrightarrow> noWhile (Seq c1 c2)"
  "noWhile c1 \<Longrightarrow> noWhile c2 \<Longrightarrow> noWhile (If tst c1 c2)"
  "noWhile c1 \<Longrightarrow> noWhile c2 \<Longrightarrow> noWhile (Par c1 c2)"
  by auto

lemma discr[intro]:
  "presAtm atm \<Longrightarrow> discr (Atm atm)"
  "discr c1 \<Longrightarrow> discr c2 \<Longrightarrow> discr (Seq c1 c2)"
  "discr c1 \<Longrightarrow> discr c2 \<Longrightarrow> discr (If tst c1 c2)"
  "discr c \<Longrightarrow> discr (While tst c)"
  "discr c1 \<Longrightarrow> discr c2 \<Longrightarrow> discr (Par c1 c2)"
  by auto

lemma siso[intro]:
  "compatAtm atm \<Longrightarrow> siso (Atm atm)"
  "siso c1 \<Longrightarrow> siso c2 \<Longrightarrow> siso (Seq c1 c2)"
  "compatTst tst \<Longrightarrow> siso c1 \<Longrightarrow> siso c2 \<Longrightarrow> siso (If tst c1 c2)"
  "compatTst tst \<Longrightarrow> siso c \<Longrightarrow> siso (While tst c)"
  "siso c1 \<Longrightarrow> siso c2 \<Longrightarrow> siso (Par c1 c2)"
  by auto

lemma Sbis[intro]:
  "compatAtm atm \<Longrightarrow> Atm atm \<approx>s Atm atm"
  "c1 \<approx>s c1 \<Longrightarrow> c2 \<approx>s c2 \<Longrightarrow> Seq c1 c2 \<approx>s Seq c1 c2"
  "compatTst tst \<Longrightarrow> c1 \<approx>s c1 \<Longrightarrow> c2 \<approx>s c2 \<Longrightarrow> If tst c1 c2 \<approx>s If tst c1 c2"
  "compatTst tst \<Longrightarrow> c \<approx>s c \<Longrightarrow> While tst c \<approx>s While tst c"
  "c1 \<approx>s c1 \<Longrightarrow> c2 \<approx>s c2 \<Longrightarrow> Par c1 c2 \<approx>s Par c1 c2"
  by auto

lemma ZObisT[intro]:
  "compatAtm atm \<Longrightarrow> Atm atm \<approx>01T Atm atm"
  "c1 \<approx>01T c1 \<Longrightarrow> c2 \<approx>01T c2 \<Longrightarrow> Seq c1 c2 \<approx>01T Seq c1 c2"
  "compatTst tst \<Longrightarrow> c1 \<approx>01T c1 \<Longrightarrow> c2 \<approx>01T c2 \<Longrightarrow> If tst c1 c2 \<approx>01T If tst c1 c2"
  "compatTst tst \<Longrightarrow> c \<approx>01T c \<Longrightarrow> While tst c \<approx>01T While tst c"
  "c1 \<approx>01T c1 \<Longrightarrow> c2 \<approx>01T c2 \<Longrightarrow> Par c1 c2 \<approx>01T Par c1 c2"
  by auto

lemma BisT[intro]:
  "compatAtm atm \<Longrightarrow> Atm atm \<approx>T Atm atm"
  "c1 \<approx>T c1 \<Longrightarrow> c2 \<approx>T c2 \<Longrightarrow> Seq c1 c2 \<approx>T Seq c1 c2"
  "compatTst tst \<Longrightarrow> c1 \<approx>T c1 \<Longrightarrow> c2 \<approx>T c2 \<Longrightarrow> If tst c1 c2 \<approx>T If tst c1 c2"
  "compatTst tst \<Longrightarrow> c \<approx>T c \<Longrightarrow> While tst c \<approx>T While tst c"
  "c1 \<approx>T c1 \<Longrightarrow> c2 \<approx>T c2 \<Longrightarrow> Par c1 c2 \<approx>T Par c1 c2"
  by auto

lemma WbisT[intro]:
  "compatAtm atm \<Longrightarrow> Atm atm \<approx>wT Atm atm"
  "c1 \<approx>wT c1 \<Longrightarrow> c2 \<approx>wT c2 \<Longrightarrow> Seq c1 c2 \<approx>wT Seq c1 c2"
  "compatTst tst \<Longrightarrow> c1 \<approx>wT c1 \<Longrightarrow> c2 \<approx>wT c2 \<Longrightarrow> If tst c1 c2 \<approx>wT If tst c1 c2"
  "compatTst tst \<Longrightarrow> c \<approx>wT c \<Longrightarrow> While tst c \<approx>wT While tst c"
  "c1 \<approx>wT c1 \<Longrightarrow> c2 \<approx>wT c2 \<Longrightarrow> Par c1 c2 \<approx>wT Par c1 c2"
  by auto

lemma ZObis[intro]:
  "compatAtm atm \<Longrightarrow> Atm atm \<approx>01 Atm atm"
  "c1 \<approx>01T c1 \<Longrightarrow> c2 \<approx>01 c2 \<Longrightarrow> Seq c1 c2 \<approx>01 Seq c1 c2"
  "c1 \<approx>01 c1 \<Longrightarrow> discr c2 \<Longrightarrow> Seq c1 c2 \<approx>01 Seq c1 c2"
  "compatTst tst \<Longrightarrow> c1 \<approx>01 c1 \<Longrightarrow> c2 \<approx>01 c2 \<Longrightarrow> If tst c1 c2 \<approx>01 If tst c1 c2"
  "c1 \<approx>01 c1 \<Longrightarrow> c2 \<approx>01 c2 \<Longrightarrow> Par c1 c2 \<approx>01 Par c1 c2"
  by auto

lemma Wbis[intro]:
  "compatAtm atm \<Longrightarrow> Atm atm \<approx>w Atm atm"
  "c1 \<approx>wT c1 \<Longrightarrow> c2 \<approx>w c2 \<Longrightarrow> Seq c1 c2 \<approx>w Seq c1 c2"
  "c1 \<approx>w c1 \<Longrightarrow> discr c2 \<Longrightarrow> Seq c1 c2 \<approx>w Seq c1 c2"
  "compatTst tst \<Longrightarrow> c1 \<approx>w c1 \<Longrightarrow> c2 \<approx>w c2 \<Longrightarrow> If tst c1 c2 \<approx>w If tst c1 c2"
  "c1 \<approx>w c1 \<Longrightarrow> c2 \<approx>w c2 \<Longrightarrow> Par c1 c2 \<approx>w Par c1 c2"
  by auto

(* Graph: The cleaned-up graph of implcations between security notions *)


lemma discr_noWhile_WbisT[intro]: "discr c \<Longrightarrow> noWhile c \<Longrightarrow> c \<approx>wT c"
  by auto

lemma siso_ZObis[intro]: "siso c \<Longrightarrow> c \<approx>01 c"
  by auto

lemma WbisT_Wbis[intro]: "c \<approx>wT c \<Longrightarrow> c \<approx>w c"
  by auto

lemma ZObis_Wbis[intro]: "c \<approx>01 c \<Longrightarrow> c \<approx>w c"
  by auto

lemma discr_BisT[intro]: "discr c \<Longrightarrow> c \<approx>T c"
  by auto

lemma WbisT_BisT[intro]: "c \<approx>wT c \<Longrightarrow> c \<approx>T c"
  using bis_incl by auto

lemma ZObisT_ZObis[intro]: "c \<approx>01T c \<Longrightarrow> c \<approx>01 c"
  by auto

lemma siso_ZObisT[intro]: "siso c \<Longrightarrow> c \<approx>01T c"
  by auto

primrec SC_discr where
  "SC_discr (Atm atm)      \<longleftrightarrow> presAtm atm"
| "SC_discr (Seq c1 c2)    \<longleftrightarrow> SC_discr c1 \<and> SC_discr c2"
| "SC_discr (If tst c1 c2) \<longleftrightarrow> SC_discr c1 \<and> SC_discr c2"
| "SC_discr (While tst c)  \<longleftrightarrow> SC_discr c"
| "SC_discr (Par c1 c2)    \<longleftrightarrow> SC_discr c1 \<and> SC_discr c2"

primrec SC_siso where
  "SC_siso (Atm atm)      \<longleftrightarrow> compatAtm atm"
| "SC_siso (Seq c1 c2)    \<longleftrightarrow> SC_siso c1 \<and> SC_siso c2"
| "SC_siso (If tst c1 c2) \<longleftrightarrow> compatTst tst \<and> SC_siso c1 \<and> SC_siso c2"
| "SC_siso (While tst c)  \<longleftrightarrow> compatTst tst \<and> SC_siso c"
| "SC_siso (Par c1 c2)    \<longleftrightarrow> SC_siso c1 \<and> SC_siso c2"

primrec SC_WbisT where
  "SC_WbisT (Atm atm)      \<longleftrightarrow> compatAtm atm"
| "SC_WbisT (Seq c1 c2)    \<longleftrightarrow> (SC_WbisT c1 \<and> SC_WbisT c2) \<or>
                              (noWhile (Seq c1 c2) \<and> SC_discr (Seq c1 c2)) \<or> 
                              SC_siso (Seq c1 c2)"
| "SC_WbisT (If tst c1 c2) \<longleftrightarrow> (if compatTst tst
                              then (SC_WbisT c1 \<and> SC_WbisT c2)
                              else ((noWhile (If tst c1 c2) \<and> SC_discr (If tst c1 c2)) \<or> 
                                    SC_siso (If tst c1 c2)))"
| "SC_WbisT (While tst c)  \<longleftrightarrow> (if compatTst tst
                              then SC_WbisT c
                              else ((noWhile (While tst c) \<and> SC_discr (While tst c)) \<or> 
                                    SC_siso (While tst c)))"
| "SC_WbisT (Par c1 c2)    \<longleftrightarrow> (SC_WbisT c1 \<and> SC_WbisT c2) \<or>
                              (noWhile (Par c1 c2) \<and> SC_discr (Par c1 c2)) \<or> 
                              SC_siso (Par c1 c2)"

primrec SC_ZObis where
  "SC_ZObis (Atm atm)      \<longleftrightarrow> compatAtm atm"
| "SC_ZObis (Seq c1 c2)    \<longleftrightarrow> (SC_siso c1 \<and> SC_ZObis c2) \<or>
                              (SC_ZObis c1 \<and> SC_discr c2) \<or>
                              SC_discr (Seq c1 c2) \<or> 
                              SC_siso (Seq c1 c2)"
| "SC_ZObis (If tst c1 c2) \<longleftrightarrow> (if compatTst tst
                              then (SC_ZObis c1 \<and> SC_ZObis c2)
                              else (SC_discr (If tst c1 c2) \<or> 
                                    SC_siso (If tst c1 c2)))"
| "SC_ZObis (While tst c)  \<longleftrightarrow> SC_discr (While tst c) \<or> 
                              SC_siso (While tst c)"
| "SC_ZObis (Par c1 c2)    \<longleftrightarrow> (SC_ZObis c1 \<and> SC_ZObis c2) \<or>
                              SC_discr (Par c1 c2) \<or> 
                              SC_siso (Par c1 c2)"

primrec SC_Wbis where
  "SC_Wbis (Atm atm)      \<longleftrightarrow> compatAtm atm"
| "SC_Wbis (Seq c1 c2)    \<longleftrightarrow> (SC_WbisT c1 \<and> SC_Wbis c2) \<or>
                             (SC_Wbis c1 \<and> SC_discr c2) \<or>
                             SC_ZObis (Seq c1 c2) \<or> 
                             SC_WbisT (Seq c1 c2)"
| "SC_Wbis (If tst c1 c2) \<longleftrightarrow> (if compatTst tst
                             then (SC_Wbis c1 \<and> SC_Wbis c2)
                             else (SC_ZObis (If tst c1 c2) \<or> 
                                   SC_WbisT (If tst c1 c2)))"
| "SC_Wbis (While tst c)  \<longleftrightarrow> SC_ZObis (While tst c) \<or> 
                             SC_WbisT (While tst c)"
| "SC_Wbis (Par c1 c2)    \<longleftrightarrow> (SC_Wbis c1 \<and> SC_Wbis c2) \<or>
                             SC_ZObis (Par c1 c2) \<or> 
                             SC_WbisT (Par c1 c2)"

primrec SC_BisT where
  "SC_BisT (Atm atm)      \<longleftrightarrow> compatAtm atm"
| "SC_BisT (Seq c1 c2)    \<longleftrightarrow> (SC_BisT c1 \<and> SC_BisT c2) \<or>
                             SC_discr (Seq c1 c2) \<or> 
                             SC_WbisT (Seq c1 c2)"
| "SC_BisT (If tst c1 c2) \<longleftrightarrow> (if compatTst tst
                             then (SC_BisT c1 \<and> SC_BisT c2)
                             else (SC_discr (If tst c1 c2) \<or> 
                                   SC_WbisT (If tst c1 c2)))"
| "SC_BisT (While tst c)  \<longleftrightarrow> (if compatTst tst
                             then SC_BisT c
                             else (SC_discr (While tst c) \<or> 
                                   SC_WbisT (While tst c)))"
| "SC_BisT (Par c1 c2)    \<longleftrightarrow> (SC_BisT c1 \<and> SC_BisT c2) \<or>
                             SC_discr (Par c1 c2) \<or> 
                             SC_WbisT (Par c1 c2)"

theorem SC_discr[intro]: "SC_discr c \<Longrightarrow> discr c"
  by (induct c) auto

theorem SC_siso[intro]: "SC_siso c \<Longrightarrow> siso c"
  by (induct c) auto

theorem SC_siso_imp_SC_WbisT[intro]: "SC_siso c \<Longrightarrow> SC_WbisT c"
  by (induct c) auto

theorem SC_discr_imp_SC_WbisT[intro]: "noWhile c \<Longrightarrow> SC_discr c \<Longrightarrow> SC_WbisT c"
  by (induct c) (auto simp: presAtm_compatAtm)

theorem SC_WbisT[intro]: "SC_WbisT c \<Longrightarrow> c \<approx>wT c"
  by (induct c) (auto split: if_split_asm)

theorem SC_discr_imp_SC_ZObis[intro]: "SC_discr c \<Longrightarrow> SC_ZObis c"
  by (induct c) (auto simp: presAtm_compatAtm)

theorem SC_siso_imp_SC_ZObis[intro]: "SC_siso c \<Longrightarrow> SC_ZObis c"
  by (induct c) auto
  
theorem SC_ZObis[intro]: "SC_ZObis c \<Longrightarrow> c \<approx>01 c"
  by (induct c) (auto split: if_split_asm intro: discr_ZObis)

theorem SC_ZObis_imp_SC_Wbis[intro]: "SC_ZObis c \<Longrightarrow> SC_Wbis c"
  by (induct c) auto

theorem SC_WbisT_imp_SC_Wbis[intro]: "SC_WbisT c \<Longrightarrow> SC_Wbis c"
  by (induct c) auto

theorem SC_Wbis[intro]: "SC_Wbis c \<Longrightarrow> c \<approx>w c"
  by (induct c) (auto split: if_split_asm intro: discr_ZObis)

theorem SC_discr_imp_SC_BisT[intro]: "SC_discr c \<Longrightarrow> SC_BisT c"
  by (induct c) (auto simp: presAtm_compatAtm)

theorem SC_WbisT_imp_SC_BisT[intro]: "SC_WbisT c \<Longrightarrow> SC_BisT c"
  by (induct c) auto

theorem SC_ZObis_imp_SC_BisT[intro]: "SC_ZObis c \<Longrightarrow> SC_BisT c"
  by (induct c) auto

theorem SC_Wbis_imp_SC_BisT[intro]: "SC_Wbis c \<Longrightarrow> SC_BisT c"
  by (induct c) (auto split: if_split_asm)

theorem SC_BisT[intro]: "SC_BisT c \<Longrightarrow> c \<approx>T c"
  by (induct c) (auto split: if_split_asm)

(* reductions *)

theorem SC_WbisT_While: "SC_WbisT (While tst c) \<longleftrightarrow> SC_WbisT c \<and> compatTst tst"
  by simp

theorem SC_ZObis_While: "SC_ZObis (While tst c) \<longleftrightarrow> (compatTst tst \<and> SC_siso c) \<or> SC_discr c"
  by auto

theorem SC_ZObis_If: "SC_ZObis (If tst c1 c2) \<longleftrightarrow> (if compatTst tst then SC_ZObis c1 \<and> SC_ZObis c2 else SC_discr c1 \<and> SC_discr c2)"
  by simp

theorem SC_WbisT_Seq: "SC_WbisT (Seq c1 c2)  \<longleftrightarrow> (SC_WbisT c1 \<and> SC_WbisT c2)"
  by auto

theorem SC_ZObis_Seq: "SC_ZObis (Seq c1 c2) \<longleftrightarrow> (SC_siso c1 \<and> SC_ZObis c2) \<or>
                              (SC_ZObis c1 \<and> SC_discr c2)"
  by auto

theorem SC_Wbis_Seq: "SC_Wbis (Seq c1 c2) \<longleftrightarrow> (SC_WbisT c1 \<and> SC_Wbis c2) \<or> (SC_Wbis c1 \<and> SC_discr c2)"
  by auto

theorem SC_BisT_Par:
  "SC_BisT (Par c1 c2)    \<longleftrightarrow> (SC_BisT c1 \<and> SC_BisT c2)"
  by auto

end

end
