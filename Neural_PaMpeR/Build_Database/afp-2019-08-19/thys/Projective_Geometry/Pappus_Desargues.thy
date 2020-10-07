theory Pappus_Desargues
  imports Main Projective_Plane_Axioms Pappus_Property Pascal_Property Desargues_Property
begin

(* Author: Anthony Bordg, University of Cambridge, apdb3@cam.ac.uk .*)

text \<open> 
Contents:
\<^item> We prove Hessenberg's theorem ([\<open>hessenberg_theorem\<close>]): Pappus's property implies Desargues's 
property in a projective plane. 
\<close>

section \<open>Hessenberg's Theorem\<close>

lemma col_ABC_ABD_1:
  assumes "A \<noteq> B" and "col A B C" and "col A B D"
  shows "col B C D"
  by (metis assms ax_uniqueness col_def)

lemma col_ABC_ABD_2:
  assumes "A \<noteq> B" and "col A B C" and "col A B D"
  shows "col A C D"
  by (metis assms ax_uniqueness col_def)

lemma col_line_eq_1:
  assumes "A \<noteq> B" and "B \<noteq> C"and "col A B C"
  shows "line A B = line B C"
  by (metis assms ax_uniqueness col_def incidA_lAB incidB_lAB)

lemma col_line_eq_2:
  assumes "A \<noteq> B" and "A \<noteq> C" and "col A B C"
  shows "line A B = line A C"
  by (metis assms col_line_eq_1 col_rot_CW line_comm)

lemma desargues_config_not_col_1: 
  assumes "desargues_config A B C A' B' C' M N P R"
  shows "\<not> col A A' B'"
proof
  assume a1:"col A A' B'"
  have f1:"A \<noteq> A'" 
    using assms desargues_config_def distinct7_def 
    by blast
  have f2:"col A A' R"
    using assms desargues_config_def meet_3_col_1 
    by blast
  from f1 and f2 and a1 have f3:"col A' B' R"
    using col_ABC_ABD_1 
    by blast
  from a1 have f4:"line A A' = line A' B'"
    by (metis assms ax_uniqueness col_def desargues_config_def f1 incidA_lAB incidB_lAB)
  have f5:"A' \<noteq> B'" 
    using assms desargues_config_def distinct7_def 
    by blast
  have f6:"B' \<noteq> R" 
    using assms desargues_config_def distinct7_def 
    by blast
  from f3 and f5 and f6 have f7:"line A' B' = line B' R"
    using col_line_eq_1 
    by blast
  have "line B' R = line B B'"
    by (metis a1 assms col_2cycle col_AAB col_line_eq_1 desargues_config_def f6 meet_3_col_2)
  have "line A A' = line B B'"
    by (simp add: \<open>line B' R = line B B'\<close> f4 f7)
  then have "False"
    using assms desargues_config_def distinct3l_def 
    by auto
  then show f8:"col A A' B' \<Longrightarrow> False"
    by simp
qed

lemma desargues_config_not_col_2:
  assumes "desargues_config A B C A' B' C' M N P R"
  shows "\<not> col B B' C'"
  using assms desargues_config_not_col_1 desargues_config_rot_CCW 
  by blast

lemma desargues_config_not_col_3:
  assumes "desargues_config A B C A' B' C' M N P R"
  shows "\<not> col C C' B'"
  by (smt assms col_line_eq_1 col_rot_CW desargues_config_def desargues_config_not_col_2 
      desargues_config_rot_CW distinct3l_def meet_3_in_def meet_col_1 meet_col_2)

lemma desargues_config_not_col_4:
  assumes "desargues_config A B C A' B' C' M N P R"
  shows "\<not> col A A' C'"
  using assms desargues_config_not_col_3 desargues_config_rot_CCW 
  by blast

lemma desargues_config_not_col_5:
  assumes "desargues_config A B C A' B' C' M N P R"
  shows "\<not> col B B' A'"
  using assms desargues_config_not_col_3 desargues_config_rot_CW 
  by blast

lemma desargues_config_not_col_6:
  assumes "desargues_config A B C A' B' C' M N P R"
  shows "\<not> col C C' A'"
  using assms desargues_config_not_col_1 desargues_config_rot_CW 
  by blast

lemma desargues_config_not_col_7:
  assumes "desargues_config A B C A' B' C' M N P R"
  shows "\<not> col A B B'"
proof
  assume a1:"col A B B'"
  have f1:"col A B R"
    by (metis a1 assms col_ABB col_ABC_ABD_2 col_rot_CW desargues_config_def desargues_config_not_col_5 
        meet_3_col_2)
  have f2:"col A A' R"
    using assms desargues_config_def meet_3_col_1 
    by blast
  have f3:"A \<noteq> A'"
    using assms col_AAB desargues_config_not_col_4 
    by blast
  have f4:"A \<noteq> R" using assms desargues_config_def distinct7_def 
    by auto
  from f2 and f3 and f4 have f5:"line A A' = line A R"
    using col_line_eq_2 
    by blast
  from f1 have f6:"line A R = line B R"
    by (metis a1 assms col_2cycle col_ABC_ABD_2 desargues_config_not_col_1 f2 f4)
  have f7:"line B R = line B B'"
    by (metis \<open>line A R = line B R\<close> a1 assms col_AAB col_line_eq_1 desargues_config_def 
        desargues_config_not_col_2 f1)
  from f5 and f6 and f7 have "line A A' = line B B'"
    by simp
  then have "False"
    using assms desargues_config_def distinct3l_def 
    by auto
  thus "col A B B' \<Longrightarrow> False"
    by simp
qed

lemma desargues_config_not_col_8:
  assumes "desargues_config A B C A' B' C' M N P R"
  shows "\<not> col A C C'"
  by (metis assms col_ABA col_line_eq_1 col_rot_CW desargues_config_def desargues_config_not_col_3 
      desargues_config_not_col_7 distinct3l_def meet_3_col_1 meet_3_col_2 meet_3_col_3)

lemma desargues_config_not_col_9:
  assumes "desargues_config A B C A' B' C' M N P R"
  shows "\<not> col B A A'"
  using assms desargues_config_not_col_8 desargues_config_rot_CCW 
  by blast
 
lemma desargues_config_not_col_10:
  assumes "desargues_config A B C A' B' C' M N P R"
  shows "\<not> col B C C'"
  using assms desargues_config_not_col_7 desargues_config_rot_CCW 
  by blast

lemma desargues_config_not_col_11:
  assumes "desargues_config A B C A' B' C' M N P R"
  shows "\<not> col C A A'"
  using assms desargues_config_not_col_7 desargues_config_rot_CW 
  by blast
 
lemma desargues_config_not_col_12:
  assumes "desargues_config A B C A' B' C' M N P R"
  shows "\<not> col C B B'"
  using assms desargues_config_not_col_8 desargues_config_rot_CW 
  by blast

lemma col_inter:
  assumes "A \<noteq> C" and "B \<noteq> C" and "col A B C"
  shows "inter l (line B C) = inter l (line A C)"
  by (metis assms col_line_eq_1 col_line_eq_2)

lemma lemma_1:
  assumes "desargues_config A B C A' B' C' M N P R" and "is_pappus"
  shows "col M N P \<or> incid A (line B' C') \<or> incid C' (line A B)"
proof-
  have "?thesis" if "incid A (line B' C') \<or> incid C' (line A B)"
    by (simp add: that)
(* The proof consists in three successive applications of Pappus property *)
  define Q E X F where "Q = inter (line A B) (line B' C')" and "E = inter (line A C) (line R Q)"
    and "X = inter (line A C') (line R B)" and "F = inter (line A' C') (line R Q)"
  have "col X E M" if "\<not> incid A (line B' C')" and "\<not> incid C' (line A B)"
  proof-
    have f1:"distinct6 C C' R Q B A"
      by (smt Q_def \<open>\<not> incid A (line B' C')\<close> \<open>\<not> incid C' (line A B)\<close> assms(1) col_ABB col_A_B_ABl 
          col_A_B_lAB col_line_eq_2 col_rot_CW desargues_config_def desargues_config_not_col_12 
          desargues_config_not_col_2 desargues_config_not_col_3 desargues_config_not_col_7 
          desargues_config_not_col_9 distinct6_def incidA_lAB line_comm meet_3_col_1 meet_3_col_2) 
    have f2: "col C C' R"
      using assms(1) desargues_config_def meet_3_col_3 
      by blast
    have f3: "col Q B A"
      using Q_def col_2cycle col_A_B_ABl col_rot_CW 
      by blast
    have f4: "is_a_intersec E C A Q R"
      using E_def col_2cycle inter_is_a_intersec is_a_intersec_def 
      by auto
    have f5:"is_a_intersec M C B Q C'"
      by (metis Q_def assms(1) col_2cycle col_ABB col_ABC_ABD_1 col_A_B_lAB col_rot_CW 
          desargues_config_def is_a_intersec_def meet_col_1 meet_col_2)
    have f6:"is_a_intersec X C' A B R"
      using X_def col_2cycle inter_is_a_intersec is_a_intersec_def 
      by auto
    from f1 and f2 and f3 and f4 and f5 and f6 have "col M X E"
      using assms(2) is_pappus2_def is_pappus_def 
      by blast
    then show "col X E M"
      using col_def 
      by auto
  qed
  have "col P X F" if "\<not> incid A (line B' C')" and "\<not> incid C' (line A B)"
  proof-
    have f1:"distinct6 A' A R Q B' C'"
      by (smt Q_def \<open>\<not> incid A (line B' C')\<close> \<open>\<not> incid C' (line A B)\<close> assms(1) col_AAB col_A_B_ABl 
          col_A_B_lAB col_line_eq_1 col_rot_CW desargues_config_def desargues_config_not_col_2 
          desargues_config_not_col_3 desargues_config_not_col_4 desargues_config_not_col_6 
          desargues_config_not_col_7 distinct6_def incidB_lAB meet_3_col_2 meet_3_col_3)
    have f2:"col A' A R"
      by (metis assms(1) col_ABA col_line_eq_1 desargues_config_def meet_3_col_1)
    have f3:"col Q B' C'"
      by (simp add: Q_def col_A_B_lAB col_rot_CW)
    have "is_a_intersec (inter (line A B) (line A' B')) A' B' Q A"
      by (metis Q_def col_def incidA_lAB incid_inter_left inter_is_a_intersec is_a_intersec_def)
    then have f4:"is_a_intersec P A' B' Q A"
      using assms(1) desargues_config_def meet_in_def uniq_inter 
      by auto
    have f5:"is_a_intersec X A C' B' R"
      by (metis X_def assms(1) col_def col_line_eq_2 desargues_config_def desargues_config_not_col_9 
          f2 inter_is_a_intersec is_a_intersec_def line_comm meet_3_col_2)
    have f6:"is_a_intersec F A' C' Q R"
      by (metis F_def inter_is_a_intersec inter_line_line_comm)
    from f1 and f2 and f3 and f4 and f5 and f6 and assms(2) 
      show "col P X F"
        using is_pappus2_def is_pappus_def 
        by blast
    qed
    have "col M N P" if "\<not> incid A (line B' C')" and "\<not> incid C' (line A B)"
    proof-
      have f1:"Q \<noteq> C' \<and> X \<noteq> E \<and> line Q C' \<noteq> line X E"
        by (smt E_def Q_def X_def \<open>\<not> incid A (line B' C')\<close> \<open>\<not> incid C' (line A B)\<close> assms(1) col_ABB 
            col_A_B_ABl col_A_B_lAB col_line_eq_2 col_rot_CW desargues_config_def 
            desargues_config_not_col_10 desargues_config_not_col_2 desargues_config_not_col_8 
            incidB_lAB incid_C_AB line_comm meet_3_col_1 meet_3_col_2 meet_3_col_3) 
      have f2:"E \<noteq> A \<and> C' \<noteq> F \<and> line E A \<noteq> line C' F"
        by (smt E_def F_def Q_def X_def \<open>\<lbrakk>\<not> incid A (line B' C'); \<not> incid C' (line A B)\<rbrakk> \<Longrightarrow> col X E M\<close> 
            assms(1) ax_uniqueness col_def desargues_config_def desargues_config_not_col_10 
            desargues_config_not_col_3 f1 incidA_lAB incidB_lAB incid_inter_left incid_inter_right 
            meet_in_def that(1))
      have f3:"Q \<noteq> A \<and> X \<noteq> F \<and> line Q A \<noteq> line X F"
        by (smt F_def Q_def X_def \<open>\<not> incid A (line B' C')\<close> \<open>\<not> incid C' (line A B)\<close> assms(1) 
            ax_uniqueness col_def desargues_config_def desargues_config_not_col_10 
            desargues_config_not_col_2 desargues_config_not_col_7 incidA_lAB incidB_lAB incid_inter_left 
            incid_inter_right meet_3_col_2 meet_3_col_3)
      have f4:"col Q E F"
        using E_def F_def col_def incidB_lAB incid_inter_right 
        by blast
      have f5:"col X C' A"
        using X_def col_2cycle col_A_B_ABl col_rot_CW 
        by blast
      have f6:"is_a_intersec M Q C' X E"
        by (metis Q_def \<open>\<lbrakk>\<not> incid A (line B' C'); \<not> incid C' (line A B)\<rbrakk> \<Longrightarrow> col X E M\<close> assms(1) 
            col_ABB col_A_B_lAB col_def col_line_eq_1 desargues_config_def incidB_lAB is_a_intersec_def 
            meet_in_def that(1) that(2))
      have f7:"is_a_intersec N E A C' F"
        by (metis E_def F_def assms(1) ax_uniqueness col_rot_CW desargues_config_def f2 incidA_lAB 
            incidB_lAB incid_inter_left is_a_intersec_def meet_col_1 meet_col_2)
      have f8:"is_a_intersec P Q A X F"
        by (metis Q_def \<open>\<lbrakk>\<not> incid A (line B' C'); \<not> incid C' (line A B)\<rbrakk> \<Longrightarrow> col P X F\<close> assms(1) 
            ax_uniqueness col_rot_CW desargues_config_def f3 incidA_lAB incidB_lAB incid_inter_left 
            is_a_intersec_def meet_col_2 meet_comm that(1) that(2))
      from f1 and f2 and f3 and f4 and f5 and f6 and f7 and f8 and assms(2) show "col M N P"
        using is_pappus2_def is_pappus_def 
        by blast
    qed
    show "col M N P \<or> incid A (line B' C') \<or> incid C' (line A B)"
      using \<open>\<lbrakk>\<not> incid A (line B' C'); \<not> incid C' (line A B)\<rbrakk> \<Longrightarrow> col M N P\<close> 
      by auto
qed

corollary corollary_1:
  assumes "desargues_config A B C A' B' C' M N P R" and "is_pappus"
  shows "col M N P \<or> ((incid A (line B' C') \<or> incid C' (line A B)) \<and> 
  (incid C (line A' B') \<or> incid B' (line A C)) \<and> (incid B (line A' C') \<or> incid A' (line B C)))"
  by (metis assms(1) assms(2) col_rot_CW desargues_config_rot_CCW lemma_1 line_comm)

definition triangle_circumscribes_triangle :: 
  "[Points, Points, Points, Points, Points, Points] \<Rightarrow> bool" where
"triangle_circumscribes_triangle A' B' C' A B C \<equiv> incid A (line B' C') \<and> incid C (line A' B') \<and>
incid B (line A' C')"

lemma lemma_2:
  assumes "desargues_config A B C A' B' C' M N P R" and "incid A (line B' C') \<or> incid C' (line A B)" 
    and "incid C (line A' B') \<or> incid B' (line A C)" and "incid B (line A' C') \<or> incid A' (line B C)"
  shows "col M N P \<or> triangle_circumscribes_triangle A B C A' B' C' \<or> triangle_circumscribes_triangle A' B' C' A B C"
  by (smt assms ax_uniqueness col_def desargues_config_not_col_1 
      desargues_config_not_col_11 desargues_config_not_col_12 desargues_config_not_col_2 
      desargues_config_not_col_3 desargues_config_not_col_9 incidA_lAB incidB_lAB 
      triangle_circumscribes_triangle_def)

lemma lemma_3:
  assumes "is_pappus" and "desargues_config A B C A' B' C' M N P R" and 
    "triangle_circumscribes_triangle A' B' C' A B C"
  shows "col M N P"
proof-
  define S T where "S = inter (line C' P) (line R A)" and "T = inter (line C' P) (line R B)"
(* The collinearity of M N P follows from three applications of Pappus property *)
  have "col N S B'"
  proof-
    have f1:"distinct6 R C C' P B A"
      by (smt assms(2) col_AAB col_line_eq_2 col_rot_CW desargues_config_def 
          desargues_config_not_col_1 desargues_config_not_col_12 desargues_config_not_col_2 
          desargues_config_not_col_5 desargues_config_not_col_7 desargues_config_not_col_8 
          desargues_config_not_col_9 distinct6_def line_comm meet_3_col_1 meet_3_col_2 meet_col_1 
          meet_col_2)
    have f2:"col R C C'"
      using assms(2) col_rot_CW desargues_config_def meet_3_col_3 
      by blast
    have f3:"col P B A"
      by (metis assms(2) col_rot_CW desargues_config_def line_comm meet_col_1)
    have f4:"is_a_intersec B' R B P C"
      by (metis assms(2) assms(3) col_def desargues_config_def incidB_lAB is_a_intersec_def 
          meet_3_col_2 meet_in_def triangle_circumscribes_triangle_def)
    have f5:"is_a_intersec S R A P C'"
      using S_def col_2cycle inter_is_a_intersec is_a_intersec_def 
      by auto
    have "line B C' = line A' C'"
      by (metis \<open>distinct6 R C C' P B A\<close> assms(3) ax_uniqueness distinct6_def incidA_lAB incidB_lAB 
          triangle_circumscribes_triangle_def)
    then have f6:"is_a_intersec N C A B C'"
      by (metis assms(2) desargues_config_def inter_is_a_intersec line_comm meet_in_def uniq_inter)
    from f1 and f2 and f3 and f4 and f5 and f6 and assms(1) have "col B' N S"
      using is_pappus2_def is_pappus_def 
      by blast
    then show "col N S B'"
      by (simp add: col_rot_CW)
  qed
  have "col M T A'"
  proof-
    have f1:"distinct6 R C C' P A B"
      by (smt assms(2) col_ABA col_line_eq_2 col_rot_CW desargues_config_def desargues_config_not_col_1 
          desargues_config_not_col_12 desargues_config_not_col_2 desargues_config_not_col_5 
          desargues_config_not_col_7 desargues_config_not_col_8 desargues_config_not_col_9 distinct6_def 
          line_comm meet_3_col_1 meet_3_col_2 meet_col_1 meet_col_2)
    have f2:"col R C C'"
      using assms(2) col_rot_CW desargues_config_def meet_3_col_3 
      by blast
    have f3:"col P A B"
      using assms(2) col_rot_CW desargues_config_def meet_col_1 
      by blast
    have f4:"line P C = line A' B'"
      by (metis \<open>distinct6 R C C' P A B\<close> assms(2) assms(3) ax_uniqueness desargues_config_def 
          distinct6_def incidA_lAB incidB_lAB meet_in_def triangle_circumscribes_triangle_def)
    have f5:"line R A = line A A'"
      by (metis \<open>distinct6 R C C' P A B\<close> assms(2) col_AAB col_line_eq_2 desargues_config_def 
          desargues_config_not_col_1 distinct6_def line_comm meet_3_col_1)
    from f4 and f5 have f6:"is_a_intersec A' R A P C"
      by (metis col_def incidA_lAB incidB_lAB is_a_intersec_def)
    have "line A C' = line B' C'"
      by (metis assms(3) ax_uniqueness distinct6_def f1 incidA_lAB incidB_lAB 
          triangle_circumscribes_triangle_def)
    then have f7:"is_a_intersec M C B A C'"
      by (metis assms(2) col_rot_CW desargues_config_def is_a_intersec_def line_comm meet_col_1 
          meet_col_2)
    have f8:"is_a_intersec T R B P C'"
      by (metis T_def distinct6_def f1 inter_comm_line_line_comm inter_is_a_intersec line_comm)
    from f1 and f2 and f3 and f6 and f7 and f8 and assms(1) have "col A' M T"
      using is_pappus2_def is_pappus_def 
      by blast
    thus "col M T A'"
      by (simp add: col_rot_CW)
  qed
  then show "col M N P"
  proof-
    have f1:"S \<noteq> T \<and> B \<noteq> A \<and> line S T \<noteq> line B A"
      by (smt T_def \<open>col N S B'\<close> assms(2) assms(3) ax_uniqueness col_AAB col_line_eq_2 col_rot_CW 
          desargues_config_def desargues_config_not_col_10 desargues_config_not_col_7 
          desargues_config_not_col_9 incidB_lAB incid_inter_left incid_inter_right 
          line_comm meet_3_col_2 meet_3_col_3 meet_col_1 meet_col_2 triangle_circumscribes_triangle_def)
    have f2:"A \<noteq> B' \<and> T \<noteq> A' \<and> line A B' \<noteq> line T A'"
      by (smt T_def assms(2) col_def desargues_config_def desargues_config_not_col_1 
          desargues_config_not_col_9 incidB_lAB incid_C_AB incid_inter_left line_comm meet_in_def)
    have f3:"S \<noteq> B' \<and> B \<noteq> A'"
      by (smt S_def assms(2) assms(3) ax_uniqueness col_A_B_ABl col_line_eq_2 col_rot_CW 
          desargues_config_def desargues_config_not_col_2 desargues_config_not_col_5 
          desargues_config_not_col_7 incidA_lAB incidB_lAB incid_inter_right inter_comm line_comm 
          meet_3_col_2 meet_in_def triangle_circumscribes_triangle_def)
    then have f4:"line S B' \<noteq> line B A'"
      by (metis assms(2) col_def desargues_config_not_col_5 incidA_lAB incidB_lAB)
    have f5:"col S A A'"
      by (metis S_def assms(2) col_ABC_ABD_1 col_A_B_lAB col_rot_CW desargues_config_def 
          desargues_config_not_col_8 meet_3_col_1 meet_3_col_3)
    have f6:"col B T B'"
      by (metis T_def assms(2) col_def col_line_eq_2 desargues_config_def desargues_config_not_col_10 
          incidB_lAB incid_inter_right line_comm meet_3_col_2 meet_3_col_3)
    have f7:"is_a_intersec P S T B A"
      by (metis S_def T_def assms(2) col_ABC_ABD_1 col_A_B_ABl col_def desargues_config_def incidA_lAB 
          incidB_lAB is_a_intersec_def meet_in_def)
    have f8:"is_a_intersec M A B' T A'"
      by (metis \<open>col M T A'\<close> assms(2) assms(3) col_rot_CW desargues_config_def f2 incidA_lAB incidB_lAB 
          is_a_intersec_def meet_col_2 triangle_circumscribes_triangle_def uniq_inter)
    have f9:"is_a_intersec N S B' B A'"
      using \<open>col N S B'\<close> assms(2) assms(3) col_def desargues_config_def incidA_lAB is_a_intersec_def 
        meet_in_def triangle_circumscribes_triangle_def 
      by auto
    from f1 and f2 and f3 and f4 and f5 and f6 and f7 and f8 and f9 and assms(1) have "col P M N"
      using is_pappus2_def is_pappus_def 
      by blast
    thus "col M N P"
      by (simp add: col_rot_CW)
  qed
qed

theorem pappus_desargues:
  assumes "is_pappus" and "desargues_config A B C A' B' C' M N P R"
  shows "col M N P"
proof-
  have f1:"col M N P \<or> ((incid A (line B' C') \<or> incid C' (line A B)) \<and> 
  (incid C (line A' B') \<or> incid B' (line A C)) \<and> (incid B (line A' C') \<or> incid A' (line B C)))"
    using assms corollary_1 
    by auto
  have f2:"col M N P \<or> triangle_circumscribes_triangle A B C A' B' C' \<or> triangle_circumscribes_triangle A' B' C' A B C"
    if "(incid A (line B' C') \<or> incid C' (line A B)) \<and> (incid C (line A' B') \<or> incid B' (line A C)) 
    \<and> (incid B (line A' C') \<or> incid A' (line B C))"
    using assms(2) lemma_2 that 
    by auto
  have f3:"col M N P" if "triangle_circumscribes_triangle A' B' C' A B C"
    using assms lemma_3 that 
    by auto
  have f4:"col M N P" if "triangle_circumscribes_triangle A B C A' B' C'"
  proof-
    have "desargues_config A' B' C' A B C M N P R"
    proof-
      have f1:"distinct7 A' B' C' A B C R" 
        using assms(2) desargues_config_def distinct7_def 
        by auto
      have f2:"\<not> col A' B' C'"
        using assms(2) desargues_config_def 
        by blast
      have f3:"\<not> col A B C"
        using assms(2) desargues_config_def 
        by blast
      have f4:"distinct3l (line A' A) (line B' B) (line C' C)"
        by (metis assms(2) desargues_config_def line_comm)
      have f5:"meet_3_in (line A' A) (line B' B) (line C' C) R"
        by (metis assms(2) desargues_config_def line_comm)
      have f6:"(line A' B') \<noteq> (line A B) \<and> (line B' C') \<noteq> (line B C) \<and> (line A' C') \<noteq> (line A C)"
        using assms(2) desargues_config_def 
        by auto
      have f7:"meet_in (line B' C') (line B C) M \<and> meet_in (line A' C') (line A C) N \<and> 
      meet_in (line A' B') (line A B) P"
        using assms(2) desargues_config_def meet_comm 
        by blast
      from f1 and f2 and f3 and f4 and f5 and f6 and f7 show "desargues_config A' B' C' A B C M N P R"
        by (simp add: desargues_config_def)
    qed
    then show "col M N P"
      using assms(1) lemma_3 that 
      by blast
  qed
  from f1 and f2 and f3 and f4 show "col M N P"
    by blast
qed

theorem hessenberg_thereom:
  assumes "is_pappus"
  shows "desargues_prop"
  by (smt are_perspective_from_line_def assms col_def desargues_prop_def pappus_desargues 
      perspective_from_point_desargues_config)

corollary pascal_desargues:
  assumes "pascal_prop"
  shows "desargues_prop"
  by (simp add: assms hessenberg_thereom pascal_pappus)

end


    













