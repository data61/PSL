(* Title:      Modal Kleene Algebras
   Author:     Victor B. F. Gomes, Walter Guttmann, Peter Höfner, Georg Struth, Tjark Weber
   Maintainer: Walter Guttmann <walter.guttman at canterbury.ac.nz>
               Georg Struth <g.struth at sheffield.ac.uk>
               Tjark Weber <tjark.weber at it.uu.se>
*)

section \<open>Modal Kleene Algebras\<close>

text \<open>This section studies laws that relate antidomain and antirange semirings and Kleene algebra,
notably Galois connections and conjugations as those studied in~\cite{MoellerStruth,DesharnaisStruthSCP}.\<close>

theory Modal_Kleene_Algebra
imports Range_Semiring
begin

class modal_semiring = antidomain_semiring + antirange_semiring +
  assumes domrange [simp]: "d (r x) = r x"
  and rangedom [simp]: "r (d x) = d x"

begin

text \<open>These axioms force that the domain algebra and the range algebra coincide.\<close>

lemma domrangefix: "d x = x \<longleftrightarrow> r x = x"
  by (metis domrange rangedom)

lemma box_diamond_galois_1:
assumes "d p = p" and "d q = q"
shows "\<langle>x| p \<le> q \<longleftrightarrow> p \<le> |x] q"
proof -
  have "\<langle>x| p \<le> q \<longleftrightarrow> p \<cdot> x \<le> x \<cdot> q"
    by (metis assms domrangefix local.ardual.ds.fdemodalisation2 local.ars_r_def)
  thus ?thesis
    by (metis assms fbox_demodalisation3)
qed

lemma box_diamond_galois_2:
assumes "d p = p" and "d q = q"
shows "|x\<rangle> p \<le> q \<longleftrightarrow> p \<le> [x| q"
proof -
  have "|x\<rangle> p \<le> q \<longleftrightarrow> x \<cdot> p \<le> q \<cdot> x"
    by (metis assms local.ads_d_def local.ds.fdemodalisation2)
  thus ?thesis
    by (metis assms domrangefix local.ardual.fbox_demodalisation3)
qed

lemma diamond_conjugation_var_1:
assumes "d p = p" and "d q = q"
shows "|x\<rangle> p \<le> ad q \<longleftrightarrow> \<langle>x| q \<le> ad p"
proof -
  have "|x\<rangle> p \<le> ad q \<longleftrightarrow> x \<cdot> p \<le> ad q \<cdot> x"
    by (metis assms local.ads_d_def local.ds.fdemodalisation2)
  also have "... \<longleftrightarrow> q \<cdot> x \<le> x \<cdot> ad p"
    by (metis assms local.ads_d_def local.kat_1_equiv_opp)
  finally show ?thesis
    by (metis assms box_diamond_galois_1 local.ads_d_def local.fbox_demodalisation3)
qed

lemma diamond_conjungation_aux:
assumes "d p = p" and "d q = q"
shows "\<langle>x| p \<le> ad q \<longleftrightarrow> q \<cdot> \<langle>x| p = 0"
apply standard
 apply (metis assms(2) local.a_antitone' local.a_gla local.ads_d_def)
proof -
  assume a1: "q \<cdot> \<langle>x| p = zero_class.zero"
  have "ad (ad q) = q"
    using assms(2) local.ads_d_def by fastforce
  then show "\<langle>x| p \<le> ad q"
    using a1 by (metis (no_types) domrangefix local.a_gla local.ads_d_def local.antisym local.ardual.a_gla2 local.ardual.gla_1 local.ars_r_def local.bdia_def local.eq_refl)
qed

lemma diamond_conjugation:
assumes "d p = p" and "d q = q"
shows "p \<cdot> |x\<rangle> q = 0 \<longleftrightarrow> q \<cdot> \<langle>x| p = 0"
proof -
  have "p \<cdot> |x\<rangle> q = 0 \<longleftrightarrow> |x\<rangle> q \<le> ad p"
    by (metis assms(1) local.a_gla local.ads_d_def local.am2 local.fdia_def)
  also have "... \<longleftrightarrow> \<langle>x| p \<le> ad q"
    by (simp add: assms diamond_conjugation_var_1)
  finally show ?thesis
    by (simp add: assms diamond_conjungation_aux)
qed

lemma box_conjugation_var_1:
assumes "d p = p" and "d q = q"
shows "ad p \<le> [x| q \<longleftrightarrow> ad q \<le> |x] p"
  by (metis assms box_diamond_galois_1 box_diamond_galois_2 diamond_conjugation_var_1 local.ads_d_def)

lemma box_diamond_cancellation_1: "d p = p \<Longrightarrow> p \<le> |x] \<langle>x| p"
  using box_diamond_galois_1 domrangefix local.ars_r_def local.bdia_def by fastforce

lemma box_diamond_cancellation_2: "d p = p \<Longrightarrow> p \<le> [x| |x\<rangle> p"
  by (metis box_diamond_galois_2 local.ads_d_def local.dpdz.domain_invol local.eq_refl local.fdia_def)

lemma box_diamond_cancellation_3: "d p = p \<Longrightarrow> |x\<rangle> [x| p \<le> p"
  using box_diamond_galois_2 domrangefix local.ardual.fdia_fbox_de_morgan_2 local.ars_r_def local.bbox_def local.bdia_def by auto

lemma box_diamond_cancellation_4: "d p = p \<Longrightarrow> \<langle>x| |x] p \<le> p"
  using box_diamond_galois_1 local.ads_d_def local.fbox_def local.fdia_def local.fdia_fbox_de_morgan_2 by auto

end

class modal_kleene_algebra = modal_semiring + kleene_algebra
begin

subclass antidomain_kleene_algebra ..

subclass antirange_kleene_algebra ..

end

end
