theory Matroid_Rank_Properties
  imports Main Higher_Projective_Space_Rank_Axioms
begin

(* Author: Anthony Bordg, University of Cambridge, apdb3@cam.ac.uk .*)

text \<open>
Contents:
\<^item> In this file we introduce the basic lemmas and properties derived from our based-rank axioms
that will allow us to simplify our future proofs.
\<close>

section \<open>Proof Techniques Using Ranks\<close>

lemma matroid_ax_3_alt:
  assumes "I \<subseteq> X \<inter> Y"
  shows "rk (X \<union> Y) + rk I \<le> rk X + rk Y"
  by (metis add.commute add_le_cancel_right assms matroid_ax_2 matroid_ax_3 order_trans)

lemma rk_uniqueness:
  assumes "rk {A,B} = 2" and "rk {C,D} = 2" and "rk {A,B,M} \<le> 2" and "rk {C,D,M} \<le> 2" and
  "rk {A,B,P} \<le> 2" and "rk {C,D,P} \<le> 2" and "rk {A,B,C,D} \<ge> 3"
  shows "rk {M,P} = 1"
proof-
  have "{A,B,M} \<union> {A,B,P} = {A,B,M,P}"
    by auto
  have "rk {A,B,M,P} + rk {A,B} \<le> rk {A,B,M} + rk {A,B,P}"
    by (metis (full_types) \<open>{A, B, M} \<union> {A, B, P} = {A, B, M, P}\<close> insert_commute le_inf_iff 
        matroid_ax_3_alt subset_insertI)
  then have "rk {A,B,M,P} = 2"
    by (smt Un_upper1 Un_upper2 \<open>{A, B, M} \<union> {A, B, P} = {A, B, M, P}\<close> add_diff_cancel_left' 
        add_diff_cancel_right' add_mono antisym assms(1) assms(3) assms(5) le_diff_conv matroid_ax_2)
  have "{C,D,M} \<union> {C,D,P} = {C,D,M,P}"
    by auto
  have "rk {C,D,M,P} + rk {C,D} \<le> rk {C,D,M} + rk {C,D,P}"
    by (metis Un_insert_left Un_upper1 \<open>{C, D, M} \<union> {C, D, P} = {C, D, M, P}\<close> insert_is_Un le_inf_iff 
        matroid_ax_3_alt)
  then have i1:"rk {C,D,M,P} + 2 \<le> 4"
    using assms(2) assms(4) assms(6) 
    by linarith
  moreover have i2:"rk {C,D,M,P} \<ge> 2"
    by (metis assms(2) insertI1 insert_subset matroid_ax_2 subset_insertI)
  from i1 and i2 have "rk {C,D,M,P} = 2"
    by linarith
  have "rk {A,B,C,D,M,P} \<ge> 3"
    by (metis Un_insert_right Un_upper2 assms(7) matroid_ax_2 order_trans sup_bot.right_neutral)
  have "{A,B,M,P} \<union> {C,D,M,P} = {A,B,C,D,M,P}"
    by auto 
  then have "rk {A,B,C,D,M,P} + rk {M,P} \<le> rk {A,B,M,P} + rk {C,D,M,P}"
    by (smt le_inf_iff matroid_ax_3_alt order_trans subset_insertI)
  then have i3:"rk {A,B,C,D,M,P} + rk {M,P} \<le> 4"
    using \<open>rk {A, B, M, P} = 2\<close> \<open>rk {C, D, M, P} = 2\<close> 
    by linarith
  have i4:"rk {A,B,C,D,M,P} + rk {M,P} \<ge> 3 + rk{M,P}"
    by (simp add: \<open>3 \<le> rk {A, B, C, D, M, P}\<close>)
  from i3 and i4 show "rk {M,P} = 1"
    by (metis (no_types, lifting) \<open>rk {A, B, C, D, M, P} + rk {M, P} \<le> rk {A, B, M, P} + rk {C, D, M, P}\<close> 
        \<open>rk {A, B, M, P} = 2\<close> \<open>rk {C, D, M, P} = 2\<close> add_le_cancel_left add_numeral_left antisym 
        insert_absorb2 numeral_Bit1 numeral_One numeral_plus_one one_add_one one_le_numeral 
        order_trans rk_ax_couple rk_ax_singleton)
qed

(* The following lemma allows to derive that there exists two lines that do not meet, i.e that belong
to two different planes *)
lemma rk_ax_dim_alt: "\<exists>A B C D. \<forall>M. rk {A,B,M} \<noteq> 2 \<or> rk {C,D,M} \<noteq> 2"
proof-
  obtain A B C D where f1:"rk {A,B,C,D} \<ge> 4"
    using rk_ax_dim 
    by auto
  have "\<forall>M. rk {A,B,M} \<noteq> 2 \<or> rk {C,D,M} \<noteq> 2"
  proof
    fix M
    have "{A,B,C,D,M} = {A,B,M} \<union> {C,D,M}"
      by auto
    then have "rk {A,B,C,D,M} + rk {M} \<le> rk {A,B,M} + rk {C,D,M}"
      by (smt le_inf_iff matroid_ax_3_alt order_trans subset_insertI)
    then have "rk {A,B,C,D,M} \<le> 3" if "rk {A,B,M} = 2" and "rk {C,D,M} = 2"
      by (smt One_nat_def Suc_leI Suc_le_mono Suc_numeral add_Suc_right add_leD1 add_mono le_antisym 
          not_le numeral_3_eq_3 numeral_One numeral_plus_one one_add_one rk_ax_singleton that(1) 
          that(2))
    then have "rk {A,B,C,D} \<le> 3" if "rk {A,B,M} = 2" and "rk {C,D,M} = 2"
      by (smt insert_commute matroid_ax_2 order_trans subset_insertI that(1) that(2))
    thus "rk {A, B, M} \<noteq> 2 \<or> rk {C, D, M} \<noteq> 2 "
      using \<open>4 \<le> rk {A, B, C, D}\<close> 
      by linarith
  qed
  thus "\<exists>A B C D. \<forall>M. rk {A, B, M} \<noteq> 2 \<or> rk {C, D, M} \<noteq> 2"
    by blast
qed

lemma rk_empty: "rk {} = 0"
proof-
  have "rk {} \<ge> 0" 
    by simp
  have "rk {} \<le> 0"
    by (metis card.empty matroid_ax_1b)
  thus "rk {} = 0" 
    by blast
qed

lemma matroid_ax_2_alt: "rk X \<le> rk (X \<union> {x}) \<and> rk (X \<union> {x}) \<le> rk X + 1"
proof
  have "X \<subseteq> X \<union> {x}" 
    by auto
  thus "rk X \<le> rk (X \<union> {x})"
    by (simp add: matroid_ax_2)
  have "rk {x} \<le> 1"
    by (metis One_nat_def card.empty card_Suc_eq insert_absorb insert_not_empty matroid_ax_1b)
  thus "rk (X \<union> {x}) \<le> rk X + 1"
    by (metis add_leD1 le_antisym matroid_ax_3 rk_ax_singleton)
qed

lemma matroid_ax_3_alt': "rk (X \<union> {y}) = rk (X \<union> {z}) \<longrightarrow> rk (X \<union> {z}) = rk X \<longrightarrow> rk X = rk (X \<union> {y,z})"
proof-
  have i1:"rk X \<le> rk (X \<union> {y,z})"
    using matroid_ax_2 
    by blast
  have i2:"rk X \<ge> rk (X \<union> {y,z})" if "rk (X \<union> {y}) = rk (X \<union> {z})" and "rk (X \<union> {z}) = rk X"
  proof-
    have "(X \<union> {y}) \<union> (X \<union> {z}) = X \<union> {y,z}" 
      by blast
    then have "rk (X \<union> {y,z}) + rk X \<le> rk X + rk X"
      by (metis \<open>rk (X \<union> {y}) = rk (X \<union> {z})\<close> \<open>rk (X \<union> {z}) = rk X\<close> inf_sup_ord(3) le_inf_iff 
          matroid_ax_3_alt)
    thus "rk (X \<union> {y,z}) \<le> rk X" 
      by simp
  qed
  thus "rk (X \<union> {y}) = rk (X \<union> {z}) \<longrightarrow> rk (X \<union> {z}) = rk X \<longrightarrow> rk X = rk (X \<union> {y, z})"
    using antisym i1 
    by blast
qed

lemma rk_ext:
  assumes "rk X \<le> 3"
  shows "\<exists>P. rk(X \<union> {P}) = rk X + 1"
proof-
  obtain A B C D where "rk {A,B,C,D} \<ge> 4"
    using rk_ax_dim 
    by auto
  have f1:"rk (X \<union> {A, B, C, D}) \<ge> 4"
    by (metis Un_upper2 \<open>4 \<le> rk {A, B, C, D}\<close> matroid_ax_2 sup.coboundedI2 sup.orderE)
  have "rk (X \<union> {A, B, C, D}) = rk X" if "rk(X \<union> {A}) = rk(X \<union> {B})" and "rk(X \<union> {B}) = rk(X \<union> {C})" 
    and "rk(X \<union> {C}) = rk(X \<union> {D})" and "rk(X \<union> {D}) = rk X"
    using matroid_ax_3_alt' that(1) that(2) that(3) that(4) 
    by auto
  then have f2:"rk (X \<union> {A, B, C, D}) \<le> 3" if "rk(X \<union> {A}) = rk(X \<union> {B})" and "rk(X \<union> {B}) = rk(X \<union> {C})" 
    and "rk(X \<union> {C}) = rk(X \<union> {D})" and "rk(X \<union> {D}) = rk X"
    using assms that(1) that(2) that(3) that(4) 
    by linarith
  from f1 and f2 have "False" if "rk(X \<union> {A}) = rk(X \<union> {B})" and "rk(X \<union> {B}) = rk(X \<union> {C})" 
    and "rk(X \<union> {C}) = rk(X \<union> {D})" and "rk(X \<union> {D}) = rk X"
    using that(1) that(2) that(3) that(4) 
    by linarith
  then have "rk (X \<union> {A}) = rk X + 1 \<or> rk (X \<union> {B}) = rk X + 1 \<or> rk (X \<union> {C}) = rk X + 1 \<or> 
    rk (X \<union> {D}) = rk X + 1"
    by (smt One_nat_def Suc_le_eq Suc_numeral Un_upper2 \<open>4 \<le> rk {A, B, C, D}\<close> 
        \<open>\<lbrakk>rk (X \<union> {A}) = rk (X \<union> {B}); rk (X \<union> {B}) = rk (X \<union> {C}); rk (X \<union> {C}) = rk (X \<union> {D}); rk (X \<union> {D}) = rk X\<rbrakk> \<Longrightarrow> rk (X \<union> {A, B, C, D}) = rk X\<close> 
        add.right_neutral add_Suc_right assms linorder_antisym_conv1 matroid_ax_2 matroid_ax_2_alt 
        not_less semiring_norm(2) semiring_norm(8) sup.coboundedI2 sup.orderE)
  thus "\<exists>P . rk (X \<union> {P}) = rk X + 1" 
    by blast
qed

lemma rk_singleton : "\<forall>P. rk {P} = 1"
proof
  fix P
  have f1:"rk {P} \<le> 1"
    by (metis One_nat_def card.empty card_Suc_eq insert_absorb insert_not_empty matroid_ax_1b)
  have f2:"rk {P} \<ge> 1"
    using rk_ax_singleton 
    by auto
  from f1 and f2 show "rk {P} = 1"
    using antisym 
    by blast
qed

lemma rk_singleton_bis :
  assumes "A = B"
  shows "rk {A, B} = 1"
  by (simp add: assms rk_singleton)

lemma rk_couple :
  assumes "A \<noteq> B"
  shows "rk {A, B} = 2"
proof-
  have f1:"rk {A, B} \<le> 2"
    by (metis insert_is_Un matroid_ax_2_alt one_add_one rk_singleton)
  have f2:"rk {A, B} \<ge> 2"
    by (simp add: assms rk_ax_couple)
  from f1 and f2 show "?thesis"
    by (simp add: f1 le_antisym)
qed

lemma rk_triple_le : "rk {A, B, C} \<le> 3"
  by (metis Suc_numeral Un_commute insert_absorb2 insert_is_Un linear matroid_ax_2_alt numeral_2_eq_2 
      numeral_3_eq_3 numeral_le_one_iff numeral_plus_one rk_couple rk_singleton semiring_norm(70))

lemma rk_couple_to_singleton :
  assumes "rk {A, B} = 1"
  shows "A = B"
proof-
  have "rk {A, B} = 2" if "A \<noteq> B"
    using rk_couple 
    by (simp add: that)
  thus "A = B" 
    using assms 
    by auto
qed

lemma rk_triple_to_rk_couple :
  assumes "rk {A, B, C} = 3"
  shows "rk {A, B} = 2"
proof-
  have "rk {A, B} \<le> 2" 
    using matroid_ax_1b
    by (metis one_le_numeral rk_ax_couple rk_couple rk_singleton_bis)
  have "rk {A, B, C} \<le> 2" if "rk {A, B} = 1"
    using matroid_ax_2_alt[of "{A, B}" C]
    by (simp add: insert_commute that)
  then have "rk {A, B} \<ge> 2"
    using assms rk_ax_couple rk_singleton_bis 
    by force
  thus "rk {A, B} = 2"
    by (simp add: \<open>rk {A, B} \<le> 2\<close> le_antisym)
qed


end
















    



