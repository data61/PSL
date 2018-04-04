(*  Title:       Preservation and respectfulness theorems for coinductive lists
    Author:      Andreas Lochbihler
    Maintainer:  Andreas Lochbihler
*)

section {* Setup for Isabelle's quotient package for lazy lists *}

theory Quotient_Coinductive_List imports
  "HOL-Library.Quotient_List"
  "HOL-Library.Quotient_Set"
  Coinductive_List
begin

subsection {* Rules for the Quotient package *}

declare llist.rel_eq[id_simps]

lemma transpD: "\<lbrakk> transp R; R a b; R b c \<rbrakk> \<Longrightarrow> R a c"
  by (erule transpE) blast

lemma id_respect [quot_respect]:
  "(R ===> R) id id"
  by (fact id_rsp)

lemma id_preserve [quot_preserve]:
  assumes "Quotient3 R Abs Rep"
  shows "(Rep ---> Abs) id = id"
  using Quotient3_abs_rep [OF assms] by (simp add: fun_eq_iff)

functor lmap: lmap
   by (simp_all add: fun_eq_iff id_def llist.map_comp)

declare llist.map_id0 [id_simps]

lemma reflp_llist_all2: "reflp R \<Longrightarrow> reflp (llist_all2 R)"
  by (rule reflpI) (auto simp add: llist_all2_conv_all_lnth elim: reflpE)

lemma symp_llist_all2: "symp R \<Longrightarrow> symp (llist_all2 R)"
  by (rule sympI) (auto simp add: llist_all2_conv_all_lnth elim: sympE)

lemma transp_llist_all2: "transp R \<Longrightarrow> transp (llist_all2 R)"
  by (rule transpI) (rule llist_all2_trans)

lemma llist_equivp [quot_equiv]:
  "equivp R \<Longrightarrow> equivp (llist_all2 R)"
  by (simp add: equivp_reflp_symp_transp reflp_llist_all2 symp_llist_all2 transp_llist_all2)

lemma unfold_llist_preserve [quot_preserve]:
  assumes q1: "Quotient3 R1 Abs1 Rep1"
  and q2: "Quotient3 R2 Abs2 Rep2"
  shows "((Abs1 ---> id) ---> (Abs1 ---> Rep2) ---> (Abs1 ---> Rep1) ---> Rep1 ---> lmap Abs2) unfold_llist = unfold_llist"
  (is "?lhs = ?rhs")
proof(intro ext)
  fix IS_LNIL LHD LTL a
  show "?lhs IS_LNIL LHD LTL a = ?rhs IS_LNIL LHD LTL a"
    by(coinduction arbitrary: a)(auto simp add: Quotient3_abs_rep[OF q1] Quotient3_abs_rep[OF q2])
qed

lemma Quotient_lmap_Abs_Rep:
  "Quotient3 R Abs Rep \<Longrightarrow> lmap Abs (lmap Rep a) = a"
  by (drule abs_o_rep) (simp add: llist.map_id0 llist.map_comp)

lemma llist_all2_rel:
  assumes "Quotient3 R Abs Rep"
  shows "llist_all2 R r s \<longleftrightarrow> llist_all2 R r r \<and> llist_all2 R s s \<and> (lmap Abs r = lmap Abs s)"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume "?lhs"
  hence "llist_all2 R r r"
    apply -
    apply(rule llist_all2_reflI)
    apply(clarsimp simp add: lset_conv_lnth)
    apply(metis Quotient3_rel[OF assms] llist_all2_lnthD)
    done
  moreover from `?lhs` have "llist_all2 R s s"
    apply -
    apply(rule llist_all2_reflI)
    apply(clarsimp simp add: lset_conv_lnth)
    apply(metis Quotient3_rel[OF assms] llist_all2_lnthD2)
    done
  moreover from `?lhs` have "llength r = llength s" by(rule llist_all2_llengthD)
  hence "lmap Abs r = lmap Abs s" using `?lhs`
    unfolding lmap_eq_lmap_conv_llist_all2
    apply -
    apply(erule llist_all2_all_lnthI)
    apply(drule (1) llist_all2_lnthD)
    apply(metis Quotient3_rel[OF assms])
    done
  ultimately show ?rhs by blast
next
  assume ?rhs thus ?lhs
    unfolding lmap_eq_lmap_conv_llist_all2
    by(clarsimp simp add: llist_all2_conv_all_lnth simp del: llist_all2_same)(metis Quotient3_rel[OF assms])
qed

lemma Quotient_llist_all2_lmap_Rep:
  "Quotient3 R Abs Rep \<Longrightarrow> llist_all2 R (lmap Rep a) (lmap Rep a)"
by(auto intro!: llist_all2_all_lnthI intro: Quotient3_rep_reflp)

lemma llist_quotient [quot_thm]:
  "Quotient3 R Abs Rep \<Longrightarrow> Quotient3 (llist_all2 R) (lmap Abs) (lmap Rep)"
by(blast intro: Quotient3I dest: Quotient_lmap_Abs_Rep Quotient_llist_all2_lmap_Rep llist_all2_rel)

declare [[mapQ3 llist = (llist_all2, llist_quotient)]]

lemma LCons_preserve [quot_preserve]:
  assumes "Quotient3 R Abs Rep"
  shows "(Rep ---> (lmap Rep) ---> (lmap Abs)) LCons = LCons"
using Quotient3_abs_rep[OF assms]
by(simp add: fun_eq_iff llist.map_comp o_def)

lemmas LCons_respect [quot_respect] = LCons_transfer 

lemma LNil_preserve [quot_preserve]:
  "lmap Abs LNil = LNil"
by simp

lemmas LNil_respect [quot_respect] = LNil_transfer

lemma lmap_preserve [quot_preserve]:
  assumes a: "Quotient3 R1 abs1 rep1"
  and     b: "Quotient3 R2 abs2 rep2"
  shows "((abs1 ---> rep2) ---> (lmap rep1) ---> (lmap abs2)) lmap = lmap"
  and   "((abs1 ---> id) ---> lmap rep1 ---> id) lmap = lmap"
using Quotient3_abs_rep[OF a] Quotient3_abs_rep[OF b]
by(simp_all add: fun_eq_iff llist.map_comp o_def)

lemma lmap_respect [quot_respect]:
  shows "((R1 ===> R2) ===> (llist_all2 R1) ===> llist_all2 R2) lmap lmap"
  and   "((R1 ===> op =) ===> (llist_all2 R1) ===> op =) lmap lmap"
by(fact lmap_transfer)(simp add: llist_all2_conv_all_lnth lmap_eq_lmap_conv_llist_all2 rel_fun_def)

lemmas llist_all2_respect [quot_respect] = llist_all2_transfer

lemma llist_all2_preserve [quot_preserve]:
  assumes "Quotient3 R Abs Rep"
  shows "((Abs ---> Abs ---> id) ---> lmap Rep ---> lmap Rep ---> id) llist_all2 = llist_all2"
using Quotient3_abs_rep[OF assms]
by(simp add: fun_eq_iff llist_all2_lmap1 llist_all2_lmap2)

lemma llist_all2_preserve2 [quot_preserve]:
  assumes "Quotient3 R Abs Rep"
  shows "(llist_all2 ((Rep ---> Rep ---> id) R) l m) = (l = m)"
  by (simp add: map_fun_def [abs_def] Quotient3_rel_rep [OF assms] llist.rel_eq comp_def)

lemma corec_llist_preserve [quot_preserve]:
  assumes q1: "Quotient3 R1 Abs1 Rep1"
  and q2: "Quotient3 R2 Abs2 Rep2"
  shows "((Abs1 ---> id) ---> (Abs1 ---> Rep2) ---> (Abs1 ---> id) ---> 
          (Abs1 ---> lmap Rep2) ---> (Abs1 ---> Rep1) ---> Rep1 ---> lmap Abs2) corec_llist = corec_llist"
  (is "?lhs = ?rhs")
proof(intro ext)
  fix IS_LNIL LHD endORmore LTL_end LTL_more b
  show "?lhs IS_LNIL LHD endORmore LTL_end LTL_more b = ?rhs IS_LNIL LHD endORmore LTL_end LTL_more b"
    by(coinduction arbitrary: b rule: llist.coinduct_strong)
      (auto simp add: Quotient3_abs_rep[OF q1] Quotient3_abs_rep[OF q2] Quotient_lmap_Abs_Rep[OF q2])
qed

end
