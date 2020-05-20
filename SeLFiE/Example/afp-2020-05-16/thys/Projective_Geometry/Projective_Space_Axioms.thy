theory Projective_Space_Axioms
  imports Main
begin

(* Author: Anthony Bordg, University of Cambridge, apdb3@cam.ac.uk .*)

text \<open>
Contents:
\<^item> We introduce the types of points and lines and an incidence relation between them.
\<^item> A set of axioms for the (3-dimensional) projective space. 
An alternative set of axioms could use planes as basic objects in addition to points and lines  
\<close>

section \<open>The axioms of the Projective Space\<close>

(* One has a type of points *)
typedecl "points"
(* We don't need an axiom for the existence of at least one point, 
since we know that the type "points" is not empty *)

(* One has a type of lines *)
typedecl "lines"
(* idem *)

(* There is a relation of incidence between points and lines *)
consts incid :: "points \<Rightarrow> lines \<Rightarrow> bool"

axiomatization where
(* The relation of incidence is decidable *)
incid_dec: "(incid P l) \<or> \<not>(incid P l)"

axiomatization where
(* Ax1: Any two distinct points are incident with just one line *)
ax1_existence: "\<exists>l. (incid P l) \<and> (incid M l)"
axiomatization where
ax1_uniqueness: "(incid P k) \<longrightarrow> (incid M k) \<longrightarrow> (incid P l) \<longrightarrow> (incid M l) \<longrightarrow> (P = M) \<or> (k = l)"

definition distinct4 :: "points \<Rightarrow> points \<Rightarrow> points \<Rightarrow> points \<Rightarrow> bool" where
"distinct4 A B C D \<equiv> (A \<noteq> B) \<and> (A \<noteq> C) \<and> (A \<noteq> D)\<and> (B \<noteq> C) \<and> (B \<noteq> D) \<and> (C \<noteq> D)"

(* Ax2: If A B C D are four distinct points such that AB meets CD then AC meets BD.
Sometimes this is called Pasch's axiom, but according to Wikipedia it is misleading
since Pasch's axiom refers to something else. *)
axiomatization where
ax2: "distinct4 A B C D \<longrightarrow> (incid A lAB \<and> incid B lAB) 
\<longrightarrow> (incid C lCD \<and> incid D lCD) \<longrightarrow> (incid A lAC \<and> incid C lAC) \<longrightarrow> 
(incid B lBD \<and> incid D lBD) \<longrightarrow> (\<exists>I.(incid I lAB \<and> incid I lCD)) \<longrightarrow> 
(\<exists>J.(incid J lAC \<and> incid J lBD))"

definition distinct3 :: "points => points => points => bool" where
"distinct3 A B C \<equiv> (A \<noteq> B) \<and> (A \<noteq> C) \<and> (B \<noteq> C)"

(** Dimension-related axioms **)
(* Ax3: Every line is incident with at least three points.
As I understand it, this axiom makes sure that lines are not degenerated into points
and since it asks for three distinct points, not only 2, it captures the idea that
lines are continuous, i.e. there is always a point between two distinct points. *)
axiomatization where
ax3: "\<exists>A B C. distinct3 A B C \<and> (incid A l) \<and> (incid B l) \<and> (incid C l)"

(* Ax4: There exists two lines that do not meet, 
hence the geometry is at least 3-dimensional *)
axiomatization where
ax4: "\<exists>l m.\<forall>P. \<not>(incid P l \<and> incid P m)"

definition meet :: "lines \<Rightarrow> lines \<Rightarrow> bool" where
"meet l m \<equiv> \<exists>P. (incid P l \<and> incid P m)"

definition meet_in :: "lines \<Rightarrow> lines \<Rightarrow> points \<Rightarrow> bool" where
"meet_in l m P \<equiv> incid P l \<and> incid P m"

definition distinct3_line :: "lines \<Rightarrow> lines \<Rightarrow> lines \<Rightarrow> bool" where
"distinct3_line l m n \<equiv> (l \<noteq> m) \<and> (l \<noteq> n) \<and> (m \<noteq> n)"

(* Ax5: The geometry is not 4-dimensional, hence it is exactly 3-dimensional *)
axiomatization where
ax5: "distinct3_line l1 l2 l3 \<longrightarrow> (\<exists>l4 J1 J2 J3. distinct3 J1 J2 J3 \<and> 
meet_in l1 l4 J1 \<and> meet_in l2 l4 J2 \<and> meet_in l3 l4 J3)"


end