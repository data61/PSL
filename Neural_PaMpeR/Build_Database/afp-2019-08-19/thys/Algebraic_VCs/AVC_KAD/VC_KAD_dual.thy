(* Title: Verification Component Based on KAD for Forward Reasoning
   Author: Victor Gomes, Georg Struth
   Maintainer: Victor Gomes <victor.gomes@cl.cam.ac.uk>
               Georg Struth <g.struth@sheffield.ac.uk> 
*)

subsection\<open>Verification Component for Forward Reasoning\<close>

theory VC_KAD_dual
  imports VC_KAD
begin

context modal_kleene_algebra
begin

text \<open>This component supports the verification of simple while programs
in a partial correctness setting.\<close>

subsubsection \<open>Basic Strongest Postcondition Calculus\<close>

text \<open>In modal Kleene algebra, strongest postconditions are backward diamond operators. These
are linked with forward boxes aka weakest preconditions by a Galois connection.  This duality has been
implemented in the AFP entry for Kleene algebra with domain and is picked up automatically in
the following proofs.\<close>

lemma r_ad [simp]: "r (ad p) = ad p"
  using a_closure addual.ars_r_def am_d_def domrangefix by auto

lemma bdia_export1: "\<langle>x| (r p \<cdot> r t) = \<langle>r t \<cdot> x| p"
  by (metis ardual.ads_d_def ardual.ds.ddual.rsr2 ardual.ds.fdia_mult bdia_def)

lemma bdia_export2: "r p \<cdot> \<langle>x| q = \<langle>x \<cdot> r p| q"
  using ardual.ads_d_def ardual.am2 ardual.fdia_export_2 bdia_def by auto

lemma bdia_seq [simp]: "\<langle>x \<cdot> y| q = \<langle>y| \<langle>x| q"
  by (simp add: ardual.ds.fdia_mult)

lemma bdia_seq_var: "\<langle>x| p \<le> p' \<Longrightarrow> \<langle>y| p' \<le> q \<Longrightarrow> \<langle>x \<cdot> y| p \<le> q"
  by (metis ardual.ds.fd_subdist_1 ardual.ds.fdia_mult dual_order.trans join.sup_absorb2)

lemma bdia_cond_var [simp]: "\<langle>if p then x else y fi| q = \<langle>x| (d p \<cdot> r q) + \<langle>y| (ad p \<cdot> r q)"
  by (metis (no_types, lifting) bdia_export1 a4' a_de_morgan a_de_morgan_var_3 a_subid_aux1' ardual.ds.fdia_add2 dka.dnso1 dka.dsg4 domrange dpdz.dnso1 cond_def join.sup.absorb_iff1 rangedom)

lemma bdia_while: "\<langle>x| (d t \<cdot> r p) \<le> r p  \<Longrightarrow> \<langle>while t do x od| p \<le> r p \<cdot> ad t"
proof -
  assume "\<langle>x| (d t \<cdot> r p) \<le> r p"
  hence "\<langle>d t \<cdot> x| p \<le> r p"
    by (metis bdia_export1 dka.dsg4 domrange rangedom)
  hence "\<langle>(d t \<cdot> x)\<^sup>\<star>| p \<le> r p"
    by (meson ardual.fdemodalisation22 ardual.kat_2_equiv_opp star_sim1)
  hence "r (ad t) \<cdot> \<langle>(d t \<cdot> x)\<^sup>\<star>| p \<le> r p \<cdot> ad t"
    by (metis ardual.dpdz.dsg4 ars_r_def mult_isol r_ad)
  thus ?thesis
    by (metis bdia_export2 while_def r_ad)
qed

lemma bdia_whilei: "r p \<le> r i \<Longrightarrow> r i \<cdot> ad t \<le> r q \<Longrightarrow> \<langle>x| (d t \<cdot> r i) \<le> r i \<Longrightarrow> \<langle>while t inv i do x od| p \<le> r q"
proof -
  assume a1: "r p \<le> r i" and a2: "r i \<cdot> ad t \<le> r q" and "\<langle>x| (d t \<cdot> r i) \<le> r i"
  hence "\<langle>while t inv i do x od| i \<le> r i \<cdot> ad t"
    by (simp add: bdia_while whilei_def)
  hence "\<langle>while t inv i do x od| i \<le> r q"
    using a2 dual_order.trans by blast
  hence "r i \<le> |while t inv i do x od] r q"
    using ars_r_def box_diamond_galois_1 domrange by fastforce
  hence "r p \<le> |while t inv i do x od] r q"
    using a1 dual_order.trans by blast
  thus ?thesis
    using ars_r_def box_diamond_galois_1 domrange by fastforce
qed

lemma bdia_whilei_break: "\<langle>y| p \<le> r i \<Longrightarrow> r i \<cdot> ad t \<le> r q \<Longrightarrow> \<langle>x| (d t \<cdot> r i) \<le> r i \<Longrightarrow> \<langle>y \<cdot> (while t inv i do x od)| p \<le> r q"
  using bdia_whilei ardual.ads_d_def ardual.ds.fdia_mult bdia_def by auto
 
end

subsubsection \<open>Floyd's Assignment Rule\<close>

lemma bdia_assign [simp]: "rel_antirange_kleene_algebra.bdia (v ::= e) \<lceil>P\<rceil> = \<lceil>\<lambda>s. \<exists>w. s v = e (s(v := w)) \<and> P (s(v:=w))\<rceil>"
  apply (simp add: rel_antirange_kleene_algebra.bdia_def gets_def p2r_def rel_ar_def)
  apply safe
  by (metis fun_upd_apply fun_upd_triv fun_upd_upd, fastforce)

lemma d_p2r [simp]: "rel_antirange_kleene_algebra.ars_r  \<lceil>P\<rceil> = \<lceil>P\<rceil>"
  by (simp add: p2r_def rel_antirange_kleene_algebra.ars_r_def rel_ar_def)

abbreviation fspec_sugar :: "'a pred \<Rightarrow> 'a rel \<Rightarrow> 'a pred \<Rightarrow> bool" ("FPRE _ _ POST _" [64,64,64] 63) where
  "FPRE P X POST Q \<equiv> rel_antirange_kleene_algebra.bdia X \<lceil>P\<rceil> \<subseteq> rel_antirange_kleene_algebra.ars_r \<lceil>Q\<rceil>"

end
