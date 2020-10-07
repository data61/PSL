theory Desargues_3D
  imports Main Higher_Projective_Space_Rank_Axioms Matroid_Rank_Properties
begin

(* Author: Anthony Bordg, University of Cambridge, apdb3@cam.ac.uk .*)

text \<open>
Contents:
\<^item> We prove Desargues's theorem: if two triangles ABC and A'B'C' are perspective from a point P (ie. 
the lines AA', BB' and CC' are concurrent in P), then they are perspective from a line (ie. the points
\<open>\<alpha> = BC \<inter> B'C'\<close>, \<open>\<beta> = AC \<inter> A'C'\<close> and \<open>\<gamma> = AB \<inter> A'B'\<close> are collinear).
In this file we restrict ourself to the case where the two triangles ABC and A'B'C' are not coplanar. 
\<close>

section \<open>Desargues's Theorem: The Non-coplanar Case\<close>

definition desargues_config_3D :: 
  "[Points, Points, Points, Points, Points, Points, Points, Points, Points, Points] => bool" 
  where "desargues_config_3D A B C A' B' C' P \<alpha> \<beta> \<gamma> \<equiv> rk {A, B, C} = 3 \<and> rk {A', B', C'} = 3 \<and> 
rk {A, A', P} = 2 \<and> rk {B, B', P} = 2 \<and> rk {C, C', P} = 2 \<and> rk {A, B, C, A', B', C'} \<ge> 4 \<and> 
rk {B, C, \<alpha>} = 2 \<and> rk {B', C', \<alpha>} = 2 \<and> rk {A, C, \<beta>} = 2 \<and> rk {A', C', \<beta>} = 2 \<and> rk {A, B, \<gamma>} = 2 \<and>
rk {A', B', \<gamma>} = 2"

lemma coplanar_4 :
  assumes "rk {A, B, C} = 3" and "rk {B, C, \<alpha>} = 2" 
  shows "rk {A, B, C, \<alpha>} = 3"
proof-
  have f1:"rk {A, B, C, \<alpha>} \<ge> 3" 
    using matroid_ax_2
    by (metis assms(1) empty_subsetI insert_mono)
  have "rk {A, B, C, \<alpha>} + rk {B, C} \<le> rk {A, B, C} + rk {B, C, \<alpha>}" 
    using matroid_ax_3_alt
    by (metis Un_insert_right add_One_commute add_mono assms(1) assms(2) matroid_ax_2_alt 
        nat_1_add_1 numeral_plus_one rk_singleton semiring_norm(3) sup_bot.right_neutral)
  then have f2:"rk {A, B, C, \<alpha>} \<le> 3"
    by (metis Un_insert_right add_One_commute assms(2) matroid_ax_2_alt numeral_plus_one 
        semiring_norm(3) sup_bot.right_neutral)
  from f1 and f2 show "rk {A, B, C, \<alpha>} = 3" 
    by auto
qed

lemma desargues_config_3D_coplanar_4 :
  assumes "desargues_config_3D A B C A' B' C' P \<alpha> \<beta> \<gamma>"
  shows "rk {A, B, C, \<alpha>} = 3" and "rk {A', B', C', \<alpha>} = 3"
proof-
  show "rk {A, B, C, \<alpha>} = 3"
    using assms desargues_config_3D_def[of A B C A' B' C' P \<alpha> \<beta> \<gamma>] coplanar_4 
    by blast
  show "rk {A', B', C', \<alpha>} = 3"
    using assms desargues_config_3D_def[of A B C A' B' C' P \<alpha> \<beta> \<gamma>] coplanar_4 
    by blast
qed

lemma coplanar_4_bis :
  assumes "rk {A, B, C} = 3" and "rk {A, C, \<beta>} = 2"
  shows "rk {A, B, C, \<beta>} = 3"
  by (smt assms(1) assms(2) coplanar_4 insert_commute)

lemma desargues_config_3D_coplanar_4_bis :
  assumes "desargues_config_3D A B C A' B' C' P \<alpha> \<beta> \<gamma>"
  shows "rk {A, B, C, \<beta>} = 3" and "rk {A', B', C', \<beta>} = 3"
proof-
  show "rk {A, B, C, \<beta>} = 3"
    using assms desargues_config_3D_def[of A B C A' B' C' P \<alpha> \<beta> \<gamma>] coplanar_4_bis 
    by auto
  show "rk {A', B', C', \<beta>} = 3"
    using assms desargues_config_3D_def[of A B C A' B' C' P \<alpha> \<beta> \<gamma>] coplanar_4_bis 
    by auto
qed

lemma coplanar_4_ter :
  assumes "rk {A, B, C} = 3" and "rk {A, B, \<gamma>} = 2"
  shows "rk {A, B, C, \<gamma>} = 3"
  by (smt assms(1) assms(2) coplanar_4 insert_commute)

lemma desargues_config_3D_coplanar_4_ter :
  assumes "desargues_config_3D A B C A' B' C' P \<alpha> \<beta> \<gamma>"
  shows "rk {A, B, C, \<gamma>} = 3" and "rk {A', B', C', \<gamma>} = 3"
proof-
  show "rk {A, B, C, \<gamma>} = 3"
    using assms desargues_config_3D_def[of A B C A' B' C' P \<alpha> \<beta> \<gamma>] coplanar_4_ter 
    by auto
  show "rk {A', B', C', \<gamma>} = 3"
    using assms desargues_config_3D_def[of A B C A' B' C' P \<alpha> \<beta> \<gamma>] coplanar_4_ter 
    by auto
qed

lemma coplanar_5 :
  assumes "rk {A, B, C} = 3" and "rk {B, C, \<alpha>} = 2" and "rk {A, C, \<beta>} = 2"
  shows "rk {A, B, C, \<alpha>, \<beta>} = 3"
proof-
  have f1:"rk {A, B, C, \<alpha>} = 3" 
    using coplanar_4
    by (smt One_nat_def Un_assoc Un_commute add.commute add_Suc_right assms(1) assms(2) insert_is_Un 
        le_antisym matroid_ax_2_alt numeral_2_eq_2 numeral_3_eq_3 one_add_one)
  have f2:"rk {A, B, C, \<beta>} = 3" 
    using coplanar_4_bis
    by (smt One_nat_def Un_assoc Un_commute add.commute add_Suc_right assms(1) assms(3) insert_is_Un 
        le_antisym matroid_ax_2_alt numeral_2_eq_2 numeral_3_eq_3 one_add_one)
  from f1 and f2 show "rk {A, B, C, \<alpha>, \<beta>} = 3" 
    using matroid_ax_3_alt'
    by (metis Un_assoc assms(1) insert_is_Un)
qed

lemma desargues_config_3D_coplanar_5 :
  assumes "desargues_config_3D A B C A' B' C' P \<alpha> \<beta> \<gamma>"
  shows "rk {A, B, C, \<alpha>, \<beta>} = 3" and "rk {A', B', C', \<alpha>, \<beta>} = 3"
proof-
  show "rk {A, B, C, \<alpha>, \<beta>} = 3"
    using assms desargues_config_3D_def coplanar_5 
    by auto
  show "rk {A', B', C', \<alpha>, \<beta>} = 3"
    using assms desargues_config_3D_def coplanar_5 
    by auto
qed


lemma coplanar_5_bis :
  assumes "rk {A, B, C} = 3" and "rk {B, C, \<alpha>} = 2" and "rk {A, B, \<gamma>} = 2"
  shows "rk {A, B, C, \<alpha>, \<gamma>} = 3"
  by (smt assms coplanar_5 insert_commute)

lemma desargues_config_3D_coplanar_5_bis :
  assumes "desargues_config_3D A B C A' B' C' P \<alpha> \<beta> \<gamma>"
  shows "rk {A, B, C, \<alpha>, \<gamma>} = 3" and "rk {A', B', C', \<alpha>, \<gamma>} = 3"
proof-
  show "rk {A, B, C, \<alpha>, \<gamma>} = 3"
    using assms desargues_config_3D_def[of A B C A' B' C' P \<alpha> \<beta> \<gamma>] coplanar_5_bis 
    by auto
  show "rk {A', B', C', \<alpha>, \<gamma>} = 3"
    using assms desargues_config_3D_def[of A B C A' B' C' P \<alpha> \<beta> \<gamma>] coplanar_5_bis 
    by auto
qed

lemma coplanar_6 :
  assumes "rk {A, B, C} = 3" and "rk {B, C, \<alpha>} = 2" and "rk {A, B, \<gamma>} = 2" and "rk {A, C, \<beta>} = 2"
  shows "rk {A, B, C, \<alpha>, \<beta>, \<gamma>} = 3"
proof-
  have f1:"rk {A, B, C, \<alpha>, \<gamma>} = 3" 
    using coplanar_5_bis assms(1) assms(2) assms(3) 
    by auto
  have f2:"rk {A, B, C, \<alpha>, \<beta>} = 3"
    using coplanar_5 assms(1) assms(2) assms(4) 
    by auto
  have f3:"rk {A, B, C, \<alpha>} = 3" 
    using coplanar_4 assms(1) assms(2) 
    by auto
  from f1 and f2 and f3 show "rk {A, B, C, \<alpha>, \<beta>, \<gamma>} = 3" 
    using matroid_ax_3_alt'[of "{A, B, C, \<alpha>}" "\<beta>" "\<gamma>"]
    by (metis Un_insert_left sup_bot.left_neutral)
qed

lemma desargues_config_3D_coplanar_6 :
  assumes "desargues_config_3D A B C A' B' C' P \<alpha> \<beta> \<gamma>"
  shows "rk {A, B, C, \<alpha>, \<beta>, \<gamma>} = 3" and "rk {A', B', C', \<alpha>, \<beta>, \<gamma>} = 3"
proof-
  show "rk {A, B, C, \<alpha>, \<beta>, \<gamma>} = 3"
    using assms desargues_config_3D_def[of A B C A' B' C' P \<alpha> \<beta> \<gamma>] coplanar_6 
    by auto
  show "rk {A', B', C', \<alpha>, \<beta>, \<gamma>} = 3"
    using assms desargues_config_3D_def[of A B C A' B' C' P \<alpha> \<beta> \<gamma>] coplanar_6 
    by auto
qed

lemma desargues_config_3D_non_coplanar :
  assumes "desargues_config_3D A B C A' B' C' P \<alpha> \<beta> \<gamma>"
  shows "rk {A, B, C, A', B', C', \<alpha>, \<beta>, \<gamma>} \<ge> 4" 
proof-
  have "rk {A, B, C, A', B', C'} \<le> rk {A, B, C, A', B', C', \<alpha>, \<beta>, \<gamma>}" 
    using matroid_ax_2 
    by auto
  thus "4 \<le> rk {A, B, C, A', B', C', \<alpha>, \<beta>, \<gamma>}" 
    using matroid_ax_2 assms desargues_config_3D_def[of A B C A' B' C' P \<alpha> \<beta> \<gamma>] 
    by linarith
qed

theorem desargues_3D :
  assumes "desargues_config_3D A B C A' B' C' P \<alpha> \<beta> \<gamma>"
  shows "rk {\<alpha>, \<beta>, \<gamma>} \<le> 2"
proof-
  have "rk {A, B, C, A', B', C', \<alpha>, \<beta>, \<gamma>} + rk {\<alpha>, \<beta>, \<gamma>} \<le> rk {A, B, C, \<alpha>, \<beta>, \<gamma>} + rk {A', B', C', \<alpha>, \<beta>, \<gamma>}"
    using matroid_ax_3_alt[of "{\<alpha>, \<beta>, \<gamma>}" "{A, B, C, \<alpha>, \<beta>, \<gamma>}" "{A', B', C', \<alpha>, \<beta>, \<gamma>}"]
    by (simp add: insert_commute)
  then have "rk {\<alpha>, \<beta>, \<gamma>} \<le> rk {A, B, C, \<alpha>, \<beta>, \<gamma>} + rk {A', B', C', \<alpha>, \<beta>, \<gamma>} - rk {A, B, C, A', B', C', \<alpha>, \<beta>, \<gamma>}"
    by linarith
  thus "rk {\<alpha>, \<beta>, \<gamma>} \<le> 2" 
    using assms desargues_config_3D_coplanar_6 desargues_config_3D_non_coplanar
    by fastforce
qed

end








