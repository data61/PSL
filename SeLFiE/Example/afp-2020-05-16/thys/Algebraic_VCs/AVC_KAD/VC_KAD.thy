(* Title: Verification Component Based on KAD
   Author: Victor Gomes, Georg Struth
   Maintainer: Victor Gomes <victor.gomes@cl.cam.ac.uk>
               Georg Struth <g.struth@sheffield.ac.uk> 
*)

section \<open>Components Based on Kleene Algebra with Domain\<close>

theory VC_KAD

imports KAD.Modal_Kleene_Algebra_Models "../P2S2R"      

begin

subsection\<open>Verification Component for Backward Reasoning\<close>

text \<open>This component supports the verification of simple while programs
in a partial correctness setting.\<close>

no_notation Archimedean_Field.ceiling ("\<lceil>_\<rceil>")
no_notation Archimedean_Field.floor ("\<lfloor>_\<rfloor>")

notation p2r ("\<lceil>_\<rceil>")
notation r2p ("\<lfloor>_\<rfloor>")

context antidomain_kleene_algebra
begin

subsubsection \<open>Additional Facts for KAD\<close>

lemma fbox_shunt: "d p \<cdot> d q \<le> |x] t \<longleftrightarrow> d p \<le> ad q + |x] t"
  by (metis a_6 a_antitone' a_loc add_commute addual.ars_r_def am_d_def da_shunt2 fbox_def)

subsubsection \<open>Syntax for Conditionals and Loops\<close>

definition cond :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" ("if _ then _ else _ fi" [64,64,64] 63) where
  "if p then x else y fi = d p \<cdot> x + ad p \<cdot> y"

definition while :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" ("while _ do _ od" [64,64] 63) where
  "while p do x od = (d p \<cdot> x)\<^sup>\<star> \<cdot> ad p"

definition whilei :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" ("while _ inv _ do _ od" [64,64,64] 63) where
  "while p inv i do x od = while p do x od"

subsubsection \<open>Basic Weakest (Liberal) Precondition Calculus\<close>

text \<open>In the setting of Kleene algebra with domain, the wlp operator is the forward modal box operator 
of antidomain Kleene algebra.\<close>

lemma fbox_export1: "ad p + |x] q = |d p \<cdot> x] q"
  using a_d_add_closure addual.ars_r_def fbox_def fbox_mult by auto

lemma fbox_export2: "|x] p \<le> |x \<cdot> ad q] (d p \<cdot> ad q)"
proof -
  {fix t
   have "d t \<cdot> x \<le> x \<cdot> d p \<Longrightarrow> d t \<cdot> x \<cdot> ad q \<le> x \<cdot> ad q \<cdot> d p \<cdot> ad q"
     by (metis (full_types) a_comm_var a_mult_idem ads_d_def am2 ds.ddual.mult_assoc phl_export2)
   hence "d t \<le> |x] p \<Longrightarrow> d t \<le> |x \<cdot> ad q] (d p \<cdot> ad q)"
     by (metis a_closure' addual.ars_r_def ans_d_def dka.dsg3 ds.ddual.mult_assoc fbox_def fbox_demodalisation3)
  }
  thus ?thesis
    by (metis a_closure' addual.ars_r_def ans_d_def fbox_def order_refl)
qed

lemma fbox_export3: "|x \<cdot> ad p] q = |x] (d p + d q)"
  using a_de_morgan_var_3 ds.ddual.mult_assoc fbox_def by auto

lemma fbox_seq [simp]: "|x \<cdot> y] q = |x] |y] q"
  by (simp add: fbox_mult) 

lemma fbox_seq_var: "p' \<le> |y] q \<Longrightarrow> p \<le> |x] p' \<Longrightarrow> p \<le> |x \<cdot> y] q"
proof -
  assume h1: "p \<le> |x] p'" and h2: "p' \<le> |y] q"
  hence "|x] p' \<le> |x] |y] q"
    by (simp add: dka.dom_iso fbox_iso)
  thus ?thesis
    by (metis h1 dual_order.trans fbox_seq)
qed

lemma fbox_cond_var [simp]: "|if p then x else y fi] q = (ad p + |x] q) \<cdot> (d p + |y] q)"  
  using cond_def a_closure' ads_d_def ans_d_def fbox_add2 fbox_export1 by auto

lemma fbox_cond_aux1 [simp]: "d p \<cdot> |if p then x else y fi] q = d p \<cdot> |x] q"
proof -
  have "d p \<cdot> |if p then x else y fi] q = d p \<cdot> |x] q \<cdot> (d p + d ( |y] q))"
    using a_d_add_closure addual.ars_r_def ds.ddual.mult_assoc fbox_def fbox_cond_var by auto
  thus ?thesis
    by (metis addual.ars_r_def am2 dka.dns5 ds.ddual.mult_assoc fbox_def)
qed

lemma fbox_cond_aux2 [simp]: "ad p \<cdot> |if p then x else y fi] q = ad p \<cdot> |y] q"
  by (metis cond_def a_closure' add_commute addual.ars_r_def ans_d_def fbox_cond_aux1)

lemma fbox_cond [simp]: "|if p then x else y fi] q = (d p \<cdot> |x] q) + (ad p \<cdot> |y] q)"
proof -
  have "|if p then x else y fi] q = (d p + ad p) \<cdot> |if p then x else y fi] q"
    by (simp add: addual.ars_r_def)
  thus ?thesis
    by (metis  distrib_right' fbox_cond_aux1 fbox_cond_aux2)
qed

lemma fbox_cond_var2 [simp]: "|if p then x else y fi] q = if p then |x] q else |y] q fi"
  using cond_def fbox_cond by auto

lemma fbox_while_unfold: "|while t do x od] p = (d t + d p) \<cdot> (ad t + |x] |while t do x od] p)"
  by (metis fbox_export1 fbox_export3 dka.dom_add_closed fbox_star_unfold_var while_def)

lemma fbox_while_var1: "d t \<cdot> |while t do x od] p = d t \<cdot> |x] |while t do x od] p"
  by (metis fbox_while_unfold a_mult_add ads_d_def dka.dns5 ds.ddual.mult_assoc join.sup_commute)

lemma fbox_while_var2: "ad t \<cdot> |while t do x od] p \<le> d p"
proof - 
  have "ad t \<cdot> |while t do x od] p = ad t \<cdot> (d t + d p) \<cdot> (ad t + |x] |while t do x od] p)"
    by (metis fbox_while_unfold ds.ddual.mult_assoc)
  also have "... =  ad t \<cdot> d p \<cdot> (ad t + |x] |while t do x od] p)"
    by (metis a_de_morgan_var_3 addual.ars_r_def dka.dom_add_closed s4)
  also have "... \<le> d p \<cdot> (ad t + |x] |while t do x od] p)"
    using a_subid_aux1' mult_isor by blast
  finally show ?thesis
    by (metis a_de_morgan_var_3 a_mult_idem addual.ars_r_def ans4 dka.dsr5 dpdz.domain_1'' dual_order.trans fbox_def)
qed

lemma fbox_while: "d p \<cdot> d t \<le> |x] p \<Longrightarrow> d p \<le> |while t do x od] (d p \<cdot> ad t)"
proof -
  assume "d p \<cdot> d t \<le> |x] p"
  hence "d p \<le> |d t \<cdot> x] p"
    by (simp add: fbox_export1 fbox_shunt)
  hence "d p \<le> |(d t \<cdot> x)\<^sup>\<star>] p"
    by (simp add: fbox_star_induct_var)
  thus ?thesis
    using order_trans while_def fbox_export2 by presburger
qed

lemma fbox_while_var: "d p = |d t \<cdot> x] p \<Longrightarrow> d p \<le> |while t do x od] (d p \<cdot> ad t)"
  by (metis eq_refl fbox_export1 fbox_shunt fbox_while)
 
lemma fbox_whilei: "d p \<le> d i \<Longrightarrow> d i \<cdot> ad t \<le> d q \<Longrightarrow> d i \<cdot> d t \<le> |x] i \<Longrightarrow> d p \<le> |while t inv i do x od] q"
proof -
  assume a1: "d p \<le> d i" and a2: "d i \<cdot> ad t \<le> d q" and "d i \<cdot> d t \<le> |x] i"
  hence "d i \<le> |while t inv i do x od] (d i \<cdot> ad t)"
    by (simp add: fbox_while whilei_def)
  also have "... \<le> |while t inv i do x od] q"
    using a2 dka.dom_iso fbox_iso by fastforce
  finally show ?thesis
    using a1 dual_order.trans by blast
qed

text \<open>The next rule is used for dealing with while loops after a series of sequential steps.\<close>

lemma fbox_whilei_break: "d p \<le> |y] i \<Longrightarrow> d i \<cdot> ad t \<le> d q \<Longrightarrow> d i \<cdot> d t \<le> |x] i \<Longrightarrow> d p \<le> |y \<cdot> (while t inv i do x od)] q"
  apply (rule fbox_seq_var, rule fbox_whilei, simp_all, blast)
  using fbox_simp by auto

text \<open>Finally we derive a frame rule.\<close>

lemma fbox_frame: "d p \<cdot> x \<le> x \<cdot> d p \<Longrightarrow> d q \<le> |x] t \<Longrightarrow> d p \<cdot> d q \<le> |x] (d p \<cdot> d t)"    
  using dual.mult_isol_var fbox_add1 fbox_demodalisation3 fbox_simp by auto

lemma fbox_frame_var: "d p \<le> |x] p \<Longrightarrow> d q \<le> |x] t \<Longrightarrow> d p \<cdot> d q \<le> |x] (d p \<cdot> d t)"
  using fbox_frame fbox_demodalisation3 fbox_simp by auto   

end

subsubsection \<open>Store and Assignment\<close>

type_synonym 'a store = "string  \<Rightarrow> 'a"

notation rel_antidomain_kleene_algebra.fbox ("wp")
and rel_antidomain_kleene_algebra.fdia ("relfdia")

definition gets :: "string \<Rightarrow> ('a store \<Rightarrow> 'a) \<Rightarrow> 'a store rel" ("_ ::= _" [70, 65] 61) where 
   "v ::= e = {(s,s (v := e s)) |s. True}"

lemma assign_prop: "\<lceil>\<lambda>s. P (s (v := e s))\<rceil> ; (v ::= e) = (v ::= e) ; \<lceil>P\<rceil>"
  by (auto simp add: p2r_def gets_def)
                                                                                 
lemma wp_assign [simp]: "wp (v ::= e) \<lceil>Q\<rceil> = \<lceil>\<lambda>s. Q (s (v := e s))\<rceil>"
  by (auto simp: rel_antidomain_kleene_algebra.fbox_def gets_def rel_ad_def p2r_def)

lemma wp_assign_var [simp]: "\<lfloor>wp (v ::= e) \<lceil>Q\<rceil>\<rfloor> = (\<lambda>s. Q (s (v := e s)))"
  by (simp, auto simp: r2p_def p2r_def)

lemma wp_assign_det: "wp (v ::= e) \<lceil>Q\<rceil> = relfdia (v ::= e) \<lceil>Q\<rceil>"
  by (auto simp add: rel_antidomain_kleene_algebra.fbox_def rel_antidomain_kleene_algebra.fdia_def gets_def p2r_def rel_ad_def, fast)
 
subsubsection \<open>Simplifications\<close>

notation rel_antidomain_kleene_algebra.ads_d ("rdom")

abbreviation spec_sugar :: "'a pred \<Rightarrow> 'a rel \<Rightarrow> 'a pred \<Rightarrow> bool" ("PRE _ _ POST _" [64,64,64] 63) where
  "PRE P X POST Q \<equiv> rdom \<lceil>P\<rceil> \<subseteq> wp X \<lceil>Q\<rceil>"

abbreviation cond_sugar :: "'a pred \<Rightarrow> 'a rel \<Rightarrow> 'a rel \<Rightarrow> 'a rel" ("IF _ THEN _ ELSE _ FI" [64,64,64] 63) where
  "IF P THEN X ELSE Y FI \<equiv> rel_antidomain_kleene_algebra.cond \<lceil>P\<rceil> X Y"

abbreviation whilei_sugar :: "'a pred \<Rightarrow> 'a pred \<Rightarrow> 'a rel \<Rightarrow> 'a rel" ("WHILE _ INV _ DO _ OD" [64,64,64] 63) where
  "WHILE P INV I DO X OD \<equiv> rel_antidomain_kleene_algebra.whilei \<lceil>P\<rceil> \<lceil>I\<rceil> X"

lemma d_p2r [simp]: "rdom \<lceil>P\<rceil> = \<lceil>P\<rceil>"
  by (simp add: p2r_def rel_antidomain_kleene_algebra.ads_d_def rel_ad_def)

lemma p2r_conj_hom_var_symm [simp]: "\<lceil>P\<rceil> ; \<lceil>Q\<rceil> = \<lceil>P \<sqinter> Q\<rceil>"
  by (simp add: p2r_conj_hom_var)

lemma p2r_neg_hom [simp]: "rel_ad \<lceil>P\<rceil> = \<lceil>- P\<rceil>"
  by (simp add: rel_ad_def p2r_def)

lemma wp_trafo: "\<lfloor>wp X \<lceil>Q\<rceil>\<rfloor> = (\<lambda>s. \<forall>s'. (s,s') \<in> X \<longrightarrow> Q s')"  
  by (auto simp: rel_antidomain_kleene_algebra.fbox_def rel_ad_def p2r_def r2p_def)

lemma wp_trafo_var: "\<lfloor>wp X \<lceil>Q\<rceil>\<rfloor> s = (\<forall>s'. (s,s') \<in> X \<longrightarrow> Q s')"
  by (simp add: wp_trafo)

lemma wp_simp: "rdom \<lceil>\<lfloor>wp X Q\<rfloor>\<rceil> = wp X Q"
  by (metis d_p2r rel_antidomain_kleene_algebra.a_subid' rel_antidomain_kleene_algebra.addual.bbox_def rpr)

lemma wp_simp_var [simp]: "wp \<lceil>P\<rceil> \<lceil>Q\<rceil> = \<lceil>- P \<squnion> Q\<rceil>"
  by (simp add: rel_antidomain_kleene_algebra.fbox_def)

lemma impl_prop [simp]: "\<lceil>P\<rceil> \<subseteq> \<lceil>Q\<rceil> \<longleftrightarrow> (\<forall>s. P s \<longrightarrow>  Q s)"
  by (auto simp: p2r_def)

lemma p2r_eq_prop [simp]: "\<lceil>P\<rceil> = \<lceil>Q\<rceil> \<longleftrightarrow> (\<forall>s. P s \<longleftrightarrow>  Q s)"
  by (auto simp: p2r_def)

lemma impl_prop_var [simp]: "rdom \<lceil>P\<rceil> \<subseteq> rdom \<lceil>Q\<rceil> \<longleftrightarrow> (\<forall>s. P s \<longrightarrow>  Q s)"
  by simp     

lemma p2r_eq_prop_var [simp]: "rdom \<lceil>P\<rceil> = rdom \<lceil>Q\<rceil> \<longleftrightarrow> (\<forall>s. P s \<longleftrightarrow>  Q s)"
  by simp                                                     
 
lemma wp_whilei: "(\<forall>s. P s \<longrightarrow> I s) \<Longrightarrow> (\<forall>s. (I \<sqinter> -T) s \<longrightarrow> Q s) \<Longrightarrow> (\<forall>s. (I \<sqinter> T) s \<longrightarrow> \<lfloor>wp X \<lceil>I\<rceil>\<rfloor> s) 
                  \<Longrightarrow> (\<forall>s. P s \<longrightarrow> \<lfloor>wp (WHILE T INV I DO X OD) \<lceil>Q\<rceil>\<rfloor> s)"
  apply (simp only: impl_prop_var[symmetric] wp_simp)
  by (rule rel_antidomain_kleene_algebra.fbox_whilei, simp_all, simp_all add: p2r_def)

end
