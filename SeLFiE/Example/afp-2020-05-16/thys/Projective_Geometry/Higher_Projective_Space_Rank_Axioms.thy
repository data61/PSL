theory Higher_Projective_Space_Rank_Axioms
  imports Main
begin

(* Author: Anthony Bordg, University of Cambridge, apdb3@cam.ac.uk .*)

text \<open>
Contents:
\<^item> Following @{cite Magaud_2012} we introduce a set of axioms for projective space geometry based on
the notions of matroid and rank.
\<close>

section \<open>A Based-rank Set of Axioms for Projective Space Geometry\<close>

(* We have a type of points *)
typedecl "Points"

(* We have a rank function "rk" on the sets of points *)
consts rk :: "Points set \<Rightarrow> nat"

(* The function rk satisfies the following axioms *)
axiomatization where
matroid_ax_1a: "rk X \<ge> 0" (* Useless if rk is defined with values in \<nat>, not \<int> *) and
matroid_ax_1b: "rk X \<le> card X" and
matroid_ax_2: "X \<subseteq> Y \<longrightarrow> rk X \<le> rk Y" and
matroid_ax_3: "rk (X \<union> Y) + rk (X \<inter> Y) \<le> rk X + rk Y"

(* To capture higher projective geometry, we need to introduce the following additional axioms *)
axiomatization where
rk_ax_singleton: "rk {P} \<ge> 1" and
rk_ax_couple: "P \<noteq> Q \<longrightarrow> rk {P,Q} \<ge> 2" and
rk_ax_pasch: "rk {A,B,C,D} \<le> 3 \<longrightarrow> (\<exists>J. rk {A,B,J} = 2 \<and> rk {C,D,J} = 2)" and
rk_ax_3_pts: "\<exists>C. rk {A,B,C} = 2 \<and> rk {B,C} = 2 \<and> rk {A,C} = 2" and
rk_ax_dim: "\<exists>A B C D. rk {A,B,C,D} \<ge> 4"

(* Note that the rank-based axioms system above deals only with points. 
Projective geometry developped this way is dimension-independent and it can be scaled to any dimension
without adding any entity to the theory or modifying the language of the theory *)

end





