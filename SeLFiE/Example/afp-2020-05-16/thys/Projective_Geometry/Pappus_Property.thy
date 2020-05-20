theory Pappus_Property
  imports Main Projective_Plane_Axioms
begin

(* Author: Anthony Bordg, University of Cambridge, apdb3@cam.ac.uk .*)
 
text \<open>
Contents:
\<^item> We give two formulations of Pappus's property for a configuration of nine points
 [\<open>is_pappus1\<close>] [\<open>is_pappus2\<close>].
\<^item> We prove the equivalence of these two formulations [\<open>pappus_equiv\<close>].
\<^item> We state Pappus property for a plane [\<open>is_pappus\<close>]. 
\<close>

section \<open>Pappus's Property\<close>

definition col :: "[Points, Points, Points] \<Rightarrow> bool" where
"col A B C \<equiv> \<exists>l. incid A l \<and> incid B l \<and> incid C l"

definition distinct6 ::
  "[Points, Points, Points, Points, Points, Points] \<Rightarrow> bool" where
"distinct6 A B C D E F \<equiv> (A \<noteq> B) \<and> (A \<noteq> C) \<and> (A \<noteq> D) \<and> (A \<noteq> E) \<and> (A \<noteq> F) \<and>
(B \<noteq> C) \<and> (B \<noteq> D) \<and> (B \<noteq> E) \<and> (B \<noteq> F) \<and>
(C \<noteq> D) \<and> (C \<noteq> E) \<and> (C \<noteq> F) \<and>
(D \<noteq> E) \<and> (D \<noteq> F) \<and>
(E \<noteq> F)"

definition lines :: "Points \<Rightarrow> Points \<Rightarrow> Lines set" where
"lines P Q \<equiv> {l. incid P l \<and> incid Q l}"

lemma uniq_line:
  assumes "P \<noteq> Q" and "l \<in> lines P Q" and "m \<in> lines P Q"
  shows "l = m"
  using assms lines_def ax_uniqueness 
  by blast

definition line :: "Points \<Rightarrow> Points \<Rightarrow> Lines" where
"line P Q \<equiv> @l. incid P l \<and> incid Q l"


(* The point P is the intersection of the lines AB and CD. For P to be well-defined,
A and B should be distinct, C and D should be distinct, and the lines AB and CD should
be distinct *)
definition is_a_proper_intersec :: "[Points, Points, Points, Points, Points] \<Rightarrow> bool" where
"is_a_proper_intersec P A B C D \<equiv> (A \<noteq> B) \<and> (C \<noteq> D) \<and> (line A B \<noteq> line C D)
\<and> col P A B \<and> col P C D"

(* We state a first form of Pappus's property *)
definition is_pappus1 :: 
"[Points, Points, Points, Points, Points, Points, Points, Points, Points] => bool " where
"is_pappus1 A B C A' B' C' P Q R \<equiv> 
  distinct6 A B C A' B' C' \<longrightarrow> col A B C \<longrightarrow> col A' B' C'
  \<longrightarrow> is_a_proper_intersec P A B' A' B \<longrightarrow> is_a_proper_intersec Q B C' B' C
  \<longrightarrow> is_a_proper_intersec R A C' A' C 
  \<longrightarrow> col P Q R"

definition is_a_intersec :: "[Points, Points, Points, Points, Points] \<Rightarrow> bool" where
"is_a_intersec P A B C D \<equiv> col P A B \<and> col P C D"

(* We state a second form of Pappus's property *)
definition is_pappus2 ::
"[Points, Points, Points, Points, Points, Points, Points, Points, Points] \<Rightarrow> bool" where
"is_pappus2 A B C A' B' C' P Q R \<equiv> 
  (distinct6 A B C A' B' C' \<or> (A \<noteq> B' \<and> A'\<noteq> B \<and> line A B' \<noteq> line A' B \<and> 
  B \<noteq> C' \<and> B' \<noteq> C \<and> line B C' \<noteq> line B' C \<and> 
  A \<noteq> C' \<and> A' \<noteq> C \<and> line A C' \<noteq> line A' C)) 
  \<longrightarrow> col A B C \<longrightarrow> col A' B' C' \<longrightarrow> is_a_intersec P A B' A' B 
  \<longrightarrow> is_a_intersec Q B C' B' C \<longrightarrow> is_a_intersec R A C' A' C 
  \<longrightarrow> col P Q R"

lemma is_a_proper_intersec_is_a_intersec:
  assumes "is_a_proper_intersec P A B C D"
  shows "is_a_intersec P A B C D"
  using assms is_a_intersec_def is_a_proper_intersec_def 
  by auto

(* The first and the second forms of Pappus's property are equivalent *)
lemma pappus21:
  assumes "is_pappus2 A B C A' B' C' P Q R"
  shows "is_pappus1 A B C A' B' C' P Q R"
  using assms is_pappus2_def is_pappus1_def is_a_proper_intersec_is_a_intersec 
  by auto

lemma col_AAB: "col A A B"
  by (simp add: ax1 col_def)

lemma col_ABA: "col A B A"
  using ax1 col_def 
  by blast

lemma col_ABB: "col A B B"
  by (simp add: ax1 col_def)

lemma incidA_lAB: "incid A (line A B)"
  by (metis (no_types, lifting) ax1 line_def someI_ex)

lemma incidB_lAB: "incid B (line A B)"
  by (metis (no_types, lifting) ax1 line_def someI_ex)

lemma degenerate_hexagon_is_pappus:
  assumes "distinct6 A B C A' B' C'" and "col A B C" and "col A' B' C'" and
"is_a_intersec P A B' A' B" and "is_a_intersec Q B C' B' C" and "is_a_intersec R A C' A' C"
and "line A B' = line A' B \<or> line B C' = line B' C \<or> line A C' = line A' C"
  shows "col P Q R"
proof -
  have "col P Q R" if "line A B' = line A' B"
    by (smt assms(1) assms(3) assms(4) assms(5) assms(6) ax_uniqueness col_def distinct6_def 
        incidA_lAB incidB_lAB is_a_intersec_def that)
  have "col P Q R" if "line B C' = line B' C"
    by (smt \<open>line A B' = line A' B \<Longrightarrow> col P Q R\<close> assms(1) assms(2) assms(3) ax_uniqueness col_def 
        distinct6_def incidA_lAB incidB_lAB that)
  have "col P Q R" if "line A C' = line A' C"
    by (smt \<open>line B C' = line B' C \<Longrightarrow> col P Q R\<close> assms(1) assms(2) assms(3) assms(7) ax_uniqueness 
        col_def distinct6_def incidA_lAB incidB_lAB)
  show "col P Q R"
    using \<open>line A B' = line A' B \<Longrightarrow> col P Q R\<close> \<open>line A C' = line A' C \<Longrightarrow> col P Q R\<close> 
      \<open>line B C' = line B' C \<Longrightarrow> col P Q R\<close> assms(7) 
    by blast
qed

lemma pappus12:
  assumes "is_pappus1 A B C A' B' C' P Q R"
  shows "is_pappus2 A B C A' B' C' P Q R"
proof -
  have "col P Q R" if "(A \<noteq> B' \<and> A'\<noteq> B \<and> line A B' \<noteq> line A' B \<and> 
  B \<noteq> C' \<and> B' \<noteq> C \<and> line B C' \<noteq> line B' C \<and> 
  A \<noteq> C' \<and> A' \<noteq> C \<and> line A C' \<noteq> line A' C)" and h1:"col A B C" and h2:"col A' B' C'"
  and "is_a_intersec P A B' A' B" and "is_a_intersec Q B C' B' C" 
  and "is_a_intersec R A C' A' C"
  proof -
    have "col P Q R" if "A = B" (* in this case P = A = B and P, Q, R lie on AC' *)
    proof -
      have "P = A"
        by (metis \<open>A \<noteq> B' \<and> A' \<noteq> B \<and> line A B' \<noteq> line A' B \<and> B \<noteq> C' \<and> B' \<noteq> C \<and> line B C' \<noteq> line B' C 
  \<and> A \<noteq> C' \<and> A' \<noteq> C \<and> line A C' \<noteq> line A' C\<close> \<open>is_a_intersec P A B' A' B\<close> ax_uniqueness col_def 
            incidA_lAB incidB_lAB is_a_intersec_def that)
      have "col P A C' \<and> col Q A C' \<and> col R A C'"
        using \<open>P = A\<close> \<open>is_a_intersec Q B C' B' C\<close> \<open>is_a_intersec R A C' A' C\<close> col_AAB 
          is_a_intersec_def that 
        by auto
      then show "col P Q R"
        by (smt \<open>A \<noteq> B' \<and> A' \<noteq> B \<and> line A B' \<noteq> line A' B \<and> B \<noteq> C' \<and> B' \<noteq> C \<and> line B C' \<noteq> line B' C 
          \<and> A \<noteq> C' \<and> A' \<noteq> C \<and> line A C' \<noteq> line A' C\<close> ax_uniqueness col_def)
  qed
  have "col P Q R" if "A = C" (* case where P = A = C = Q and P,Q,R belong to AB' *)
  proof -
    have "R = A"
      by (metis \<open>A \<noteq> B' \<and> A' \<noteq> B \<and> line A B' \<noteq> line A' B \<and> B \<noteq> C' \<and> B' \<noteq> C \<and> line B C' \<noteq> line B' C 
        \<and> A \<noteq> C' \<and> A' \<noteq> C \<and> line A C' \<noteq> line A' C\<close> \<open>is_a_intersec R A C' A' C\<close> ax_uniqueness col_def incidA_lAB incidB_lAB is_a_intersec_def that)
    have "col P A B' \<and> col Q A B' \<and> col R A B'"
      using \<open>R = A\<close> \<open>is_a_intersec P A B' A' B\<close> \<open>is_a_intersec Q B C' B' C\<close> col_def 
        is_a_intersec_def that 
      by auto
    then show "col P Q R"
      by (smt \<open>A \<noteq> B' \<and> A' \<noteq> B \<and> line A B' \<noteq> line A' B \<and> B \<noteq> C' \<and> B' \<noteq> C \<and> line B C' \<noteq> line B' C 
        \<and> A \<noteq> C' \<and> A' \<noteq> C \<and> line A C' \<noteq> line A' C\<close> ax_uniqueness col_def)
  qed
  have "col P Q R" if "A = A'" (* very degenerate case, all the 9 points are collinear*)
    by (smt \<open>A \<noteq> B' \<and> A' \<noteq> B \<and> line A B' \<noteq> line A' B \<and> B \<noteq> C' \<and> B' \<noteq> C \<and> line B C' \<noteq> line B' C \<and> 
      A \<noteq> C' \<and> A' \<noteq> C \<and> line A C' \<noteq> line A' C\<close> \<open>is_a_intersec P A B' A' B\<close> \<open>is_a_intersec R A C' A' C\<close> 
        ax_uniqueness col_ABA col_def incidA_lAB incidB_lAB is_a_intersec_def that)
  have "col P Q R" if "B = C" (* case where B = C = Q and P,Q,R belong to A'B *)
    by (smt \<open>A \<noteq> B' \<and> A' \<noteq> B \<and> line A B' \<noteq> line A' B \<and> B \<noteq> C' \<and> B' \<noteq> C \<and> line B C' \<noteq> line B' C \<and> 
      A \<noteq> C' \<and> A' \<noteq> C \<and> line A C' \<noteq> line A' C\<close> \<open>is_a_intersec P A B' A' B\<close> \<open>is_a_intersec Q B C' B' C\<close> 
        \<open>is_a_intersec R A C' A' C\<close> ax_uniqueness col_def incidA_lAB incidB_lAB is_a_intersec_def that)
  have "col P Q R" if "B = B'" (* very degenerate case, the 9 points are collinear *)
    by (smt \<open>A \<noteq> B' \<and> A' \<noteq> B \<and> line A B' \<noteq> line A' B \<and> B \<noteq> C' \<and> B' \<noteq> C \<and> line B C' \<noteq> line B' C \<and> 
      A \<noteq> C' \<and> A' \<noteq> C \<and> line A C' \<noteq> line A' C\<close> \<open>is_a_intersec P A B' A' B\<close> \<open>is_a_intersec Q B C' B' C\<close> 
        ax_uniqueness col_AAB col_def incidA_lAB incidB_lAB is_a_intersec_def that)
  have "col P Q R" if "C = C'" (* again, very degenerate case, the 9 points are collinear *)
    by (smt \<open>A \<noteq> B' \<and> A' \<noteq> B \<and> line A B' \<noteq> line A' B \<and> B \<noteq> C' \<and> B' \<noteq> C \<and> line B C' \<noteq> line B' C \<and> 
      A \<noteq> C' \<and> A' \<noteq> C \<and> line A C' \<noteq> line A' C\<close> \<open>is_a_intersec Q B C' B' C\<close> \<open>is_a_intersec R A C' A' C\<close> 
        ax_uniqueness col_ABB col_def incidA_lAB incidB_lAB is_a_intersec_def that)
  have "col P Q R" if "A' = B'" (* case where P = A' = B', and P,Q,R belong to A'C *)
    by (smt \<open>A \<noteq> B' \<and> A' \<noteq> B \<and> line A B' \<noteq> line A' B \<and> B \<noteq> C' \<and> B' \<noteq> C \<and> line B C' \<noteq> line B' C \<and> 
      A \<noteq> C' \<and> A' \<noteq> C \<and> line A C' \<noteq> line A' C\<close> \<open>is_a_intersec P A B' A' B\<close> \<open>is_a_intersec Q B C' B' C\<close> 
        \<open>is_a_intersec R A C' A' C\<close> ax_uniqueness col_def incidA_lAB incidB_lAB is_a_intersec_def that)
  have "col P Q R" if "A' = C'" (* case where R = A' = B', the points P,Q,R belong to A'B *)
    by (smt \<open>A \<noteq> B' \<and> A' \<noteq> B \<and> line A B' \<noteq> line A' B \<and> B \<noteq> C' \<and> B' \<noteq> C \<and> line B C' \<noteq> line B' C \<and> 
      A \<noteq> C' \<and> A' \<noteq> C \<and> line A C' \<noteq> line A' C\<close> \<open>is_a_intersec P A B' A' B\<close> \<open>is_a_intersec Q B C' B' C\<close> 
        \<open>is_a_intersec R A C' A' C\<close> ax_uniqueness col_def incidA_lAB incidB_lAB is_a_intersec_def that)
  have "col P Q R" if "B' = C'" (* case where Q = B' = C', the points P,Q,R belong to AB' *)
    by (smt \<open>A \<noteq> B' \<and> A' \<noteq> B \<and> line A B' \<noteq> line A' B \<and> B \<noteq> C' \<and> B' \<noteq> C \<and> line B C' \<noteq> line B' C \<and> 
      A \<noteq> C' \<and> A' \<noteq> C \<and> line A C' \<noteq> line A' C\<close> \<open>is_a_intersec P A B' A' B\<close> \<open>is_a_intersec Q B C' B' C\<close> 
        \<open>is_a_intersec R A C' A' C\<close> ax_uniqueness col_def incidA_lAB incidB_lAB is_a_intersec_def that)
  have "col P Q R" if "A \<noteq> B \<and> A \<noteq> C \<and> A \<noteq> A' \<and> B \<noteq> C \<and> B \<noteq> B' \<and> C \<noteq> C' \<and> A'\<noteq> B'
    \<and> A' \<noteq> C' \<and> B' \<noteq> C'"
  proof -
    have a1:"distinct6 A B C A' B' C'"
      using \<open>A \<noteq> B' \<and> A' \<noteq> B \<and> line A B' \<noteq> line A' B \<and> B \<noteq> C' \<and> B' \<noteq> C \<and> line B C' \<noteq> line B' C \<and> 
        A \<noteq> C' \<and> A' \<noteq> C \<and> line A C' \<noteq> line A' C\<close> distinct6_def that 
      by auto
    have "is_a_proper_intersec P A B' A' B"
      using \<open>A \<noteq> B' \<and> A' \<noteq> B \<and> line A B' \<noteq> line A' B \<and> B \<noteq> C' \<and> B' \<noteq> C \<and> line B C' \<noteq> line B' C \<and> 
        A \<noteq> C' \<and> A' \<noteq> C \<and> line A C' \<noteq> line A' C\<close> \<open>is_a_intersec P A B' A' B\<close> is_a_intersec_def 
        is_a_proper_intersec_def 
      by auto
    have "is_a_proper_intersec Q B C' B' C"
      using \<open>A \<noteq> B' \<and> A' \<noteq> B \<and> line A B' \<noteq> line A' B \<and> B \<noteq> C' \<and> B' \<noteq> C \<and> line B C' \<noteq> line B' C \<and> 
        A \<noteq> C' \<and> A' \<noteq> C \<and> line A C' \<noteq> line A' C\<close> \<open>is_a_intersec Q B C' B' C\<close> is_a_intersec_def 
        is_a_proper_intersec_def 
      by auto
    have "is_a_proper_intersec R A C' A' C"
      using \<open>A \<noteq> B' \<and> A' \<noteq> B \<and> line A B' \<noteq> line A' B \<and> B \<noteq> C' \<and> B' \<noteq> C \<and> line B C' \<noteq> line B' C \<and> 
        A \<noteq> C' \<and> A' \<noteq> C \<and> line A C' \<noteq> line A' C\<close> \<open>is_a_intersec R A C' A' C\<close> is_a_intersec_def 
        is_a_proper_intersec_def 
      by auto
    show "col P Q R"
      using \<open>is_a_proper_intersec P A B' A' B\<close> \<open>is_a_proper_intersec Q B C' B' C\<close> 
        \<open>is_a_proper_intersec R A C' A' C\<close> a1 assms h1 h2 is_pappus1_def 
      by blast
  qed
    show "col P Q R"
      using \<open>A = A' \<Longrightarrow> col P Q R\<close> \<open>A = B \<Longrightarrow> col P Q R\<close> \<open>A = C \<Longrightarrow> col P Q R\<close> 
        \<open>A \<noteq> B \<and> A \<noteq> C \<and> A \<noteq> A' \<and> B \<noteq> C \<and> B \<noteq> B' \<and> C \<noteq> C' \<and> A' \<noteq> B' \<and> A' \<noteq> C' \<and> B' \<noteq> C' \<Longrightarrow> col P Q R\<close> 
        \<open>A' = B' \<Longrightarrow> col P Q R\<close> \<open>A' = C' \<Longrightarrow> col P Q R\<close> \<open>B = B' \<Longrightarrow> col P Q R\<close> \<open>B = C \<Longrightarrow> col P Q R\<close> 
        \<open>B' = C' \<Longrightarrow> col P Q R\<close> \<open>C = C' \<Longrightarrow> col P Q R\<close> 
      by blast
  qed  
  have "col P Q R" if "distinct6 A B C A' B' C'" and "col A B C" and "col A' B' C'"
    and "is_a_intersec P A B' A' B" and "is_a_intersec Q B C' B' C" and "is_a_intersec R A C' A' C"
  proof -
    have "col P Q R" if "line A B' = line A' B"
      using \<open>col A B C\<close> \<open>col A' B' C'\<close> \<open>distinct6 A B C A' B' C'\<close> \<open>is_a_intersec P A B' A' B\<close> 
        \<open>is_a_intersec Q B C' B' C\<close> \<open>is_a_intersec R A C' A' C\<close> degenerate_hexagon_is_pappus that 
      by blast
    have "col P Q R" if "line B C' = line B' C"
      using \<open>col A B C\<close> \<open>col A' B' C'\<close> \<open>distinct6 A B C A' B' C'\<close> \<open>is_a_intersec P A B' A' B\<close> 
        \<open>is_a_intersec Q B C' B' C\<close> \<open>is_a_intersec R A C' A' C\<close> degenerate_hexagon_is_pappus that 
      by blast
    have "col P Q R" if "line A' C = line A C'"
      using \<open>col A B C\<close> \<open>col A' B' C'\<close> \<open>distinct6 A B C A' B' C'\<close> \<open>is_a_intersec P A B' A' B\<close> 
        \<open>is_a_intersec Q B C' B' C\<close> \<open>is_a_intersec R A C' A' C\<close> degenerate_hexagon_is_pappus that 
      by auto
    have "col P Q R" if "line A B' \<noteq> line A' B" and "line B C' \<noteq> line B' C" and
      "line A C' \<noteq> line A' C"
    proof -
      have "is_a_proper_intersec P A B' A' B"
        using \<open>distinct6 A B C A' B' C'\<close> \<open>is_a_intersec P A B' A' B\<close> distinct6_def is_a_intersec_def 
          is_a_proper_intersec_def that(1) 
        by auto
      have "is_a_proper_intersec Q B C' B' C"
        using \<open>distinct6 A B C A' B' C'\<close> \<open>is_a_intersec Q B C' B' C\<close> distinct6_def is_a_intersec_def 
          is_a_proper_intersec_def that(2) 
        by auto
      have "is_a_proper_intersec R A C' A' C"
        using \<open>distinct6 A B C A' B' C'\<close> \<open>is_a_intersec R A C' A' C\<close> distinct6_def is_a_intersec_def 
          is_a_proper_intersec_def that(3) 
        by auto
      show "col P Q R"
        using \<open>col A B C\<close> \<open>col A' B' C'\<close> \<open>distinct6 A B C A' B' C'\<close> \<open>is_a_proper_intersec P A B' A' B\<close> 
          \<open>is_a_proper_intersec Q B C' B' C\<close> \<open>is_a_proper_intersec R A C' A' C\<close> assms is_pappus1_def 
        by blast
    qed
    show "col P Q R"
      using \<open>\<lbrakk>line A B' \<noteq> line A' B; line B C' \<noteq> line B' C; line A C' \<noteq> line A' C\<rbrakk> \<Longrightarrow> col P Q R\<close> 
        \<open>line A B' = line A' B \<Longrightarrow> col P Q R\<close> \<open>line A' C = line A C' \<Longrightarrow> col P Q R\<close> 
        \<open>line B C' = line B' C \<Longrightarrow> col P Q R\<close> 
      by fastforce
  qed
  show "is_pappus2 A B C A' B' C' P Q R"
    by (simp add: \<open>\<lbrakk>A \<noteq> B' \<and> A' \<noteq> B \<and> line A B' \<noteq> line A' B \<and> B \<noteq> C' \<and> B' \<noteq> C \<and> line B C' \<noteq> line B' C 
      \<and> A \<noteq> C' \<and> A' \<noteq> C \<and> line A C' \<noteq> line A' C; col A B C; col A' B' C'; is_a_intersec P A B' A' B; is_a_intersec Q B C' B' C; is_a_intersec R A C' A' C\<rbrakk> \<Longrightarrow> col P Q R\<close> 
        \<open>\<lbrakk>distinct6 A B C A' B' C'; col A B C; col A' B' C'; is_a_intersec P A B' A' B; is_a_intersec Q B C' B' C; is_a_intersec R A C' A' C\<rbrakk> \<Longrightarrow> col P Q R\<close> 
        is_pappus2_def)
qed

lemma pappus_equiv: "is_pappus1 A B C A' B' C' P Q R = is_pappus2 A B C A' B' C' P Q R"
  using pappus12 pappus21 
  by blast

(* Finally, we give Pappus's property for a plane stating that the diagonal points 
of any hexagon of that plane, whose vertices lie alternately on two lines, are collinear *)

definition is_pappus :: "bool" where
"is_pappus \<equiv> \<forall>A B C D E F P Q R. is_pappus2 A B C D E F P Q R"

end
