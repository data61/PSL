theory Desargues_Property
  imports Main Projective_Plane_Axioms Pappus_Property Pascal_Property
begin

(* Author: Anthony Bordg, University of Cambridge, apdb3@cam.ac.uk .*)

text \<open>
Contents:
\<^item> We formalize Desargues's property, [\<open>desargues_prop\<close>], that states that if two triangles are perspective 
from a point, then they are perspective from a line. 
Note that some planes satisfy that property and some others don't, hence Desargues's property is
not a theorem though it is a theorem in projective space geometry. 
\<close>

section \<open>Desargues's Property\<close>

definition distinct3 :: "[Points, Points, Points] \<Rightarrow> bool" where
"distinct3 A B C \<equiv> A \<noteq> B \<and> A \<noteq> C \<and> B \<noteq> C"

definition triangle :: "[Points, Points, Points] \<Rightarrow> bool" where
"triangle A B C \<equiv> distinct3 A B C \<and> (line A B \<noteq> line A C)"

definition meet_in :: "Lines \<Rightarrow> Lines => Points => bool " where
"meet_in l m P \<equiv> incid P l \<and> incid P m"

lemma meet_col_1:
  assumes "meet_in (line A B) (line C D) P"
  shows "col A B P"
  using assms col_def incidA_lAB incidB_lAB meet_in_def 
  by blast

lemma meet_col_2:
  assumes "meet_in (line A B) (line C D) P"
  shows "col C D P"
  using assms meet_col_1 meet_in_def 
  by auto

definition meet_3_in :: "[Lines, Lines, Lines, Points] \<Rightarrow> bool" where
"meet_3_in l m n P \<equiv> meet_in l m P \<and> meet_in l n P"

lemma meet_all_3:
  assumes "meet_3_in l m n P"
  shows "meet_in m n P"
  using assms meet_3_in_def meet_in_def 
  by auto

lemma meet_comm:
  assumes "meet_in l m P"
  shows "meet_in m l P"
  using assms meet_in_def 
  by auto

lemma meet_3_col_1:
  assumes "meet_3_in (line A B) m n P"
  shows "col A B P"
  using assms meet_3_in_def meet_col_2 meet_in_def 
  by auto

lemma meet_3_col_2:
  assumes "meet_3_in l (line A B) n P"
  shows "col A B P"
  using assms col_def incidA_lAB incidB_lAB meet_3_in_def meet_in_def 
  by blast

lemma meet_3_col_3:
  assumes "meet_3_in l m (line A B) P"
  shows "col A B P"
  using assms meet_3_col_2 meet_3_in_def 
  by auto

definition distinct7 ::
  "[Points, Points, Points, Points, Points, Points, Points] \<Rightarrow> bool" where
"distinct7 A B C D E F G \<equiv> (A \<noteq> B) \<and> (A \<noteq> C) \<and> (A \<noteq> D) \<and> (A \<noteq> E) \<and> (A \<noteq> F) \<and> (A \<noteq> G) \<and>
(B \<noteq> C) \<and> (B \<noteq> D) \<and> (B \<noteq> E) \<and> (B \<noteq> F) \<and> (B \<noteq> G) \<and>
(C \<noteq> D) \<and> (C \<noteq> E) \<and> (C \<noteq> F) \<and> (C \<noteq> G) \<and>
(D \<noteq> E) \<and> (D \<noteq> F) \<and> (D \<noteq> G) \<and>
(E \<noteq> F) \<and> (E \<noteq> G) \<and>
(F \<noteq> G)"

definition distinct3l :: "[Lines, Lines, Lines] \<Rightarrow> bool" where
"distinct3l l m n \<equiv> l \<noteq> m \<and> l \<noteq> n \<and> m \<noteq> n"

(* From now on we give less general statements on purpose to avoid a lot of uninteresting 
degenerate cases, since we can hardly think of any interesting application where one would need 
to instantiate a statement on such degenerate case, hence our statements and proofs will be more 
textbook-like. For the working mathematician the only thing that probably matters is the main
theorem without considering all the degenerate cases for which the statement might still hold. *)

definition desargues_config :: 
  "[Points, Points, Points, Points, Points, Points, Points, Points, Points, Points] => bool" where
"desargues_config A B C A' B' C' M N P R \<equiv> distinct7 A B C A' B' C' R \<and> \<not> col A B C 
\<and> \<not> col A' B' C' \<and> distinct3l (line A A') (line B B') (line C C') \<and> 
meet_3_in (line A A') (line B B') (line C C') R \<and> (line A B) \<noteq> (line A' B') \<and> 
(line B C) \<noteq> (line B' C') \<and> (line A C) \<noteq> (line A' C') \<and> meet_in (line B C) (line B' C') M \<and>
meet_in (line A C) (line A' C') N \<and> meet_in (line A B) (line A' B') P"

lemma distinct7_rot_CW:
  assumes "distinct7 A B C D E F G"
  shows "distinct7 C A B F D E G"
  using assms distinct7_def 
  by auto

(* Desargues configurations are stable under any rotation (i,j,k) of {1,2,3} *)
lemma desargues_config_rot_CW:
  assumes "desargues_config A B C A' B' C' M N P R"
  shows "desargues_config C A B C' A' B' P M N R"
  by (smt assms col_rot_CW desargues_config_def distinct3l_def distinct7_rot_CW line_comm 
      meet_3_in_def meet_all_3 meet_comm)

lemma desargues_config_rot_CCW:
  assumes "desargues_config A B C A' B' C' M N P R"
  shows "desargues_config B C A B' C' A' N P M R"
  by (simp add: assms desargues_config_rot_CW)

(* With the two following definitions we repackage the definition of a Desargues configuration in a 
"high-level", i.e. textbook-like, way. *)

definition are_perspective_from_point :: 
  "[Points, Points, Points, Points, Points, Points, Points] \<Rightarrow> bool" where
"are_perspective_from_point A B C A' B' C' R \<equiv> distinct7 A B C A' B' C' R \<and> triangle A B C \<and>
triangle A' B' C' \<and> distinct3l (line A A') (line B B') (line C C') \<and> 
meet_3_in (line A A') (line B B') (line C C') R"

definition are_perspective_from_line ::
  "[Points, Points, Points, Points, Points, Points] \<Rightarrow> bool" where
"are_perspective_from_line A B C A' B' C' \<equiv> distinct6 A B C A' B' C' \<longrightarrow> triangle A B C \<longrightarrow>
triangle A' B' C' \<longrightarrow> line A B \<noteq> line A' B' \<longrightarrow> line A C \<noteq> line A' C' \<longrightarrow> line B C \<noteq> line B' C' \<longrightarrow>
col (inter (line A B) (line A' B')) (inter (line A C) (line A' C')) (inter (line B C) (line B' C'))"

lemma meet_in_inter:
  assumes "l \<noteq> m"
  shows "meet_in l m (inter l m)"
  by (simp add: incid_inter_left incid_inter_right meet_in_def)

lemma perspective_from_point_desargues_config:
  assumes "are_perspective_from_point A B C A' B' C' R" and "line A B \<noteq> line A' B'" and 
    "line A C \<noteq> line A' C'" and "line B C \<noteq> line B' C'"
  shows "desargues_config A B C A' B' C' (inter (line B C) (line B' C')) (inter (line A C) (line A' C')) 
    (inter (line A B) (line A' B')) R"
  by (smt are_perspective_from_point_def assms(1) assms(2) assms(3) assms(4) col_line_ext_1 
      desargues_config_def distinct3_def incidB_lAB inter_line_ext_2 line_comm meet_in_inter 
      triangle_def uniq_inter)

(* Now, we state Desargues's property in a textbook-like form *)
definition desargues_prop :: "bool" where
"desargues_prop \<equiv> 
\<forall>A B C A' B' C' P. 
  are_perspective_from_point A B C A' B' C' P \<longrightarrow> are_perspective_from_line A B C A' B' C'"

end






