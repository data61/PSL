(* Title: Refinement KAT
   Author: Victor Gomes, Georg Struth
   Maintainer: Victor Gomes <victor.gomes@cl.cam.ac.uk>
               Georg Struth <g.struth@sheffield.ac.uk> 
*)

subsection \<open>Refinement Component\<close>

theory RKAT
  imports "AVC_KAT/VC_KAT"

begin

subsubsection\<open>RKAT: Definition and Basic Properties\<close>

text \<open>A refinement KAT is a KAT expanded by Morgan's specification statement.\<close>

class rkat = kat +
  fixes R :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
  assumes spec_def:  "x \<le> R p q \<longleftrightarrow> H p x q"

begin

lemma R1: "H p (R p q) q"
  using spec_def by blast

lemma R2: "H p x q \<Longrightarrow> x \<le> R p q"
  by (simp add: spec_def)

subsubsection\<open>Propositional Refinement Calculus\<close>

lemma R_skip: "1 \<le> R p p"
proof -
  have "H p 1 p"
    by (simp add: H_skip)
  thus ?thesis
    by (rule R2)
qed

lemma R_cons: "t p \<le> t p' \<Longrightarrow> t q' \<le> t q \<Longrightarrow> R p' q' \<le> R p q"
proof -
  assume h1: "t p \<le> t p'" and h2: "t q' \<le> t q"
  have "H p' (R p' q') q'"
    by (simp add: R1)
  hence "H p (R p' q') q"
    using h1 h2 H_cons_1 H_cons_2 by blast
  thus ?thesis
    by (rule R2)
qed

lemma R_seq: "(R p r) \<cdot> (R r q) \<le> R p q"
proof -
  have "H p (R p r) r" and "H r (R r q) q"
    by (simp add: R1)+
  hence "H p ((R p r) \<cdot> (R r q)) q"
    by (rule H_seq_swap)
  thus ?thesis
    by (rule R2)
qed

lemma R_cond: "if v then (R (t v \<cdot> t p) q) else (R (n v \<cdot> t p) q) fi \<le> R p q"
proof - 
  have "H (t v \<cdot> t p) (R (t v \<cdot> t p) q) q" and "H (n v \<cdot> t p) (R (n v \<cdot> t p) q) q"
    by (simp add: R1)+
  hence "H p (if v then (R (t v \<cdot> t p) q) else (R (n v \<cdot> t p) q) fi) q"
    by (simp add: H_cond n_mult_comm)
 thus ?thesis
    by (rule R2)
qed

lemma R_loop: "while q do (R (t p \<cdot> t q) p) od \<le> R p (t p \<cdot> n q)"
proof -
  have "H (t p \<cdot> t q) (R (t p \<cdot> t q) p)  p" 
    by (simp_all add: R1)
  hence "H p (while q do (R (t p \<cdot> t q) p) od) (t p \<cdot> n q)"
    by (simp add: H_loop)
  thus ?thesis
    by (rule R2)
  qed

lemma R_zero_one: "x \<le> R 0 1"
proof -
  have "H 0 x 1"
    by (simp add: H_def)
  thus ?thesis
    by (rule R2)
qed

lemma R_one_zero: "R 1 0 = 0"
proof -
  have "H 1 (R 1 0) 0"
    by (simp add: R1)
  thus ?thesis
    by (simp add: H_def join.le_bot)
qed

end

end
