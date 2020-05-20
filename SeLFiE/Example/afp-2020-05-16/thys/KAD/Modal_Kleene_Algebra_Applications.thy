(* Title:      Applications of Modal Kleene Algebras
   Author:     Victor B. F. Gomes, Walter Guttmann, Peter Höfner, Georg Struth, Tjark Weber
   Maintainer: Walter Guttmann <walter.guttman at canterbury.ac.nz>
               Georg Struth <g.struth at sheffield.ac.uk>
               Tjark Weber <tjark.weber at it.uu.se>
*)

section \<open>Applications of Modal Kleene Algebras\<close>

theory Modal_Kleene_Algebra_Applications
imports Antidomain_Semiring
begin

text \<open>This file collects some applications of the theories developed so far. These are described
 in~\cite{guttmannstruthweber11algmeth}.\<close>

context antidomain_kleene_algebra
begin

subsection \<open>A Reachability Result\<close>

text \<open>This example is taken from~\cite{desharnaismoellerstruth06kad}.\<close>

lemma opti_iterate_var [simp]: "|(ad y \<cdot> x)\<^sup>\<star>\<rangle> y = |x\<^sup>\<star>\<rangle> y"
proof (rule antisym)
  show "|(ad y \<cdot> x)\<^sup>\<star>\<rangle> y \<le> |x\<^sup>\<star>\<rangle> y"
    by (simp add: a_subid_aux1' ds.fd_iso2 star_iso)
  have "d y + |x\<rangle> |(ad y \<cdot> x)\<^sup>\<star>\<rangle> y = d y + ad y \<cdot> |x\<rangle> |(ad y \<cdot> x)\<^sup>\<star>\<rangle> y"
    using local.ads_d_def local.d_6 local.fdia_def by auto
  also have "... = d y + |ad y \<cdot> x\<rangle> |(ad y \<cdot> x)\<^sup>\<star>\<rangle> y"
    by (simp add: fdia_export_2)
  finally have "d y + |x\<rangle> |(ad y \<cdot> x)\<^sup>\<star>\<rangle> y = |(ad y \<cdot> x)\<^sup>\<star>\<rangle> y"
    by simp
  thus "|x\<^sup>\<star>\<rangle> y \<le> |(ad y \<cdot> x)\<^sup>\<star>\<rangle> y"
    using local.dka.fd_def local.dka.fdia_star_induct_eq by auto
qed

lemma opti_iterate [simp]: "d y + |(x \<cdot> ad y)\<^sup>\<star>\<rangle> |x\<rangle> y = |x\<^sup>\<star>\<rangle> y"
proof -
  have "d y + |(x \<cdot> ad y)\<^sup>\<star>\<rangle> |x\<rangle> y = d y + |x\<rangle> |(ad y \<cdot> x)\<^sup>\<star>\<rangle> y"
    by (metis local.conway.dagger_slide local.ds.fdia_mult)
  also have "... = d y + |x\<rangle> |x\<^sup>\<star>\<rangle> y"
    by simp
  finally show ?thesis
    by force
qed

lemma opti_iterate_var_2 [simp]: "d y + |ad y \<cdot> x\<rangle> |x\<^sup>\<star>\<rangle> y = |x\<^sup>\<star>\<rangle> y"
  by (metis local.dka.fdia_star_unfold_var opti_iterate_var)

subsection \<open>Derivation of Segerberg's Formula\<close>

text \<open>This example is taken from~\cite{DesharnaisMoellerStruthLMCS}.\<close>

definition Alpha :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" ("A")
  where "A x y = d (x \<cdot> y) \<cdot> ad y"

lemma A_dom [simp]: "d (A x y) = A x y"
  using Alpha_def local.a_d_closed local.ads_d_def local.apd_d_def by auto

lemma A_fdia: "A x y = |x\<rangle> y \<cdot> ad y"
  by (simp add: Alpha_def local.dka.fd_def)

lemma A_fdia_var: "A x y = |x\<rangle> d y \<cdot> ad y"
  by (simp add: A_fdia)

lemma a_A: "ad (A x (ad y)) = |x] y + ad y"
  using Alpha_def local.a_6 local.a_d_closed local.apd_d_def local.fbox_def by force

lemma fsegerberg [simp]: "d y + |x\<^sup>\<star>\<rangle> A x y = |x\<^sup>\<star>\<rangle> y"
proof (rule antisym)
  have "d y + |x\<rangle> (d y + |x\<^sup>\<star>\<rangle> A x y) = d y + |x\<rangle> y + |x\<rangle> |x\<^sup>\<star>\<rangle> ( |x\<rangle> y \<cdot> ad y )"
    by (simp add: A_fdia add_assoc local.ds.fdia_add1)
  also have "... = d y + |x\<rangle> y \<cdot> ad y + |x\<rangle> |x\<^sup>\<star>\<rangle> ( |x\<rangle> y \<cdot> ad y )"
    by (metis local.am2 local.d_6 local.dka.fd_def local.fdia_def)
  finally have "d y + |x\<rangle> (d y + |x\<^sup>\<star>\<rangle> A x y) = d y + |x\<^sup>\<star>\<rangle> A x y"
    by (metis A_dom A_fdia add_assoc local.dka.fdia_star_unfold_var)
  thus "|x\<^sup>\<star>\<rangle> y \<le> d y + |x\<^sup>\<star>\<rangle> A x y"
    by (metis local.a_d_add_closure local.ads_d_def local.dka.fdia_star_induct_eq local.fdia_def)
  have "d y + |x\<^sup>\<star>\<rangle> A x y = d y + |x\<^sup>\<star>\<rangle> ( |x\<rangle> y \<cdot> ad y )"
    by (simp add: A_fdia)
  also have "... \<le> d y + |x\<^sup>\<star>\<rangle> |x\<rangle> y"
    using local.dpdz.domain_1'' local.ds.fd_iso1 local.join.sup_mono by blast
  finally show "d y + |x\<^sup>\<star>\<rangle> A x y \<le> |x\<^sup>\<star>\<rangle> y"
    by simp
qed

lemma fbox_segerberg [simp]: "d y \<cdot> |x\<^sup>\<star>] ( |x] y + ad y ) = |x\<^sup>\<star>] y"
proof -
  have "|x\<^sup>\<star>] ( |x] y + ad y ) = d ( |x\<^sup>\<star>] ( |x] y + ad y ) )"
    using local.a_d_closed local.ads_d_def local.apd_d_def local.fbox_def by auto
  hence f1: "|x\<^sup>\<star>] ( |x] y + ad y ) = ad ( |x\<^sup>\<star>\<rangle> (A x (ad y)) )"
    by (simp add: a_A local.fdia_fbox_de_morgan_2)
  have "ad y + |x\<^sup>\<star>\<rangle> (A x (ad y)) = |x\<^sup>\<star>\<rangle> ad y"
    by (metis fsegerberg local.a_d_closed local.ads_d_def local.apd_d_def)
  thus ?thesis
    by (metis f1 local.ads_d_def local.ans4 local.fbox_simp local.fdia_fbox_de_morgan_2)
qed

subsection \<open>Wellfoundedness and Loeb's Formula\<close>

text \<open>This example is taken from~\cite{DesharnaisStruthSCP}.\<close>

definition Omega :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" ("\<Omega>")
  where "\<Omega> x y = d y \<cdot> ad (x \<cdot> y)"

text \<open>If $y$ is a set, then $\Omega(x,y)$ describes those elements in $y$ from which no further $x$ transitions are possible.\<close>

lemma omega_fdia: "\<Omega> x y = d y \<cdot> ad ( |x\<rangle> y )"
  using Omega_def local.a_d_closed local.ads_d_def local.apd_d_def local.dka.fd_def by auto

lemma omega_fbox: "\<Omega> x y = d y \<cdot> |x] (ad y)"
  by (simp add: fdia_fbox_de_morgan_2 omega_fdia)

lemma omega_absorb1 [simp]: "\<Omega> x y \<cdot> ad ( |x\<rangle> y ) = \<Omega> x y"
  by (simp add: mult_assoc omega_fdia)

lemma omega_absorb2 [simp]: "\<Omega> x y \<cdot> ad (x \<cdot> y) = \<Omega> x y"
  by (simp add: Omega_def mult_assoc)

lemma omega_le_1: "\<Omega> x y \<le> d y"
  by (simp add: Omega_def d_a_galois1)

lemma omega_subid: "\<Omega> x (d y) \<le> d y"
  by (simp add: Omega_def local.a_subid_aux2)

lemma omega_le_2: "\<Omega> x y \<le> ad ( |x\<rangle> y )"
  by (simp add: local.dka.dom_subid_aux2 omega_fdia)

lemma omega_dom [simp]: "d (\<Omega> x y) = \<Omega> x y"
  using Omega_def local.a_d_closed local.ads_d_def local.apd_d_def by auto

lemma a_omega: "ad (\<Omega> x y) = ad y + |x\<rangle> y"
  by (simp add: Omega_def local.a_6 local.ds.fd_def)

lemma omega_fdia_3 [simp]: "d y \<cdot> ad (\<Omega> x y) = d y \<cdot> |x\<rangle> y"
  using Omega_def local.ads_d_def local.fdia_def local.s4 by presburger

lemma omega_zero_equiv_1: "\<Omega> x y = 0 \<longleftrightarrow> d y \<le> |x\<rangle> y"
  by (simp add: Omega_def local.a_gla local.ads_d_def local.fdia_def)

definition Loebian :: "'a \<Rightarrow> bool"
  where "Loebian x = (\<forall>y. |x\<rangle> y \<le> |x\<rangle> \<Omega> x y)"

definition PreLoebian :: "'a \<Rightarrow> bool"
  where "PreLoebian x = (\<forall>y. d y \<le> |x\<^sup>\<star>\<rangle> \<Omega> x y)"

definition Noetherian :: "'a \<Rightarrow> bool"
  where "Noetherian x = (\<forall>y. \<Omega> x y = 0 \<longrightarrow> d y = 0)"

lemma noetherian_alt: "Noetherian x \<longleftrightarrow> (\<forall>y. d y \<le> |x\<rangle> y \<longrightarrow> d y = 0)"
  by (simp add: Noetherian_def omega_zero_equiv_1)

lemma Noetherian_iff_PreLoebian: "Noetherian x \<longleftrightarrow> PreLoebian x"
proof
  assume hyp: "Noetherian x"
  {
    fix y
    have "d y \<cdot> ad ( |x\<^sup>\<star>\<rangle> \<Omega> x y ) = d y \<cdot> ad (\<Omega> x y + |x\<rangle> |x\<^sup>\<star>\<rangle> \<Omega> x y)"
      by (metis local.dka.fdia_star_unfold_var omega_dom)
    also have "... = d y \<cdot> ad (\<Omega> x y) \<cdot> ad ( |x\<rangle> |x\<^sup>\<star>\<rangle> \<Omega> x y )"
      using ans4 mult_assoc by presburger
    also have "... \<le> |x\<rangle> d y \<cdot> ad ( |x\<rangle> |x\<^sup>\<star>\<rangle> \<Omega> x y )"
      by (simp add: local.dka.dom_subid_aux2 local.mult_isor)
    also have "... \<le> |x\<rangle> (d y \<cdot> ad ( |x\<^sup>\<star>\<rangle> \<Omega> x y ))"
      by (simp add: local.dia_diff)
    finally have "d y \<cdot> ad ( |x\<^sup>\<star>\<rangle> \<Omega> x y ) \<le> |x\<rangle> (d y \<cdot> ad ( |x\<^sup>\<star>\<rangle> \<Omega> x y ))"
      by blast
    hence "d y \<cdot> ad ( |x\<^sup>\<star>\<rangle> \<Omega> x y ) = 0"
      by (metis hyp local.ads_d_def local.dpdz.dom_mult_closed local.fdia_def noetherian_alt)
    hence "d y \<le> |x\<^sup>\<star>\<rangle> \<Omega> x y"
      by (simp add: local.a_gla local.ads_d_def local.dka.fd_def)
  }
  thus "PreLoebian x"
    using PreLoebian_def by blast
next
  assume a: "PreLoebian x"
  {
    fix y
    assume b: "\<Omega> x y = 0"
    hence "d y \<le> |x\<rangle> d y"
      using omega_zero_equiv_1 by auto
    hence "d y = 0"
      by (metis (no_types) PreLoebian_def a b a_one a_zero add_zeror annir fdia_def less_eq_def)
  }
  thus "Noetherian x"
    by (simp add: Noetherian_def)
qed

lemma Loebian_imp_Noetherian: "Loebian x \<Longrightarrow> Noetherian x"
proof -
  assume a: "Loebian x"
  {
    fix y
    assume b: "\<Omega> x y = 0"
    hence "d y \<le> |x\<rangle> d y"
      using omega_zero_equiv_1 by auto
    also have "... \<le> |x\<rangle> (\<Omega> x y)"
      using Loebian_def a by auto
    finally have "d y = 0"
      by (simp add: b local.antisym local.fdia_def)
  }
  thus "Noetherian x"
    by (simp add: Noetherian_def)
qed

lemma d_transitive: "(\<forall>y. |x\<rangle> |x\<rangle> y \<le> |x\<rangle> y) \<Longrightarrow> (\<forall>y. |x\<rangle> y = |x\<^sup>\<star>\<rangle> |x\<rangle> y)"
proof -
  assume a: "\<forall>y. |x\<rangle> |x\<rangle> y \<le> |x\<rangle> y"
  {
    fix y
    have "|x\<rangle> y + |x\<rangle> |x\<rangle> y \<le> |x\<rangle> y"
      by (simp add: a)
    hence "|x\<^sup>\<star>\<rangle> |x\<rangle> y \<le> |x\<rangle> y"
      using local.dka.fd_def local.dka.fdia_star_induct_var by auto
    have "|x\<rangle> y \<le> |x\<^sup>\<star>\<rangle> |x\<rangle> y"
      using local.dka.fd_def local.order_prop opti_iterate by force
  }
  thus ?thesis
    using a local.antisym local.dka.fd_def local.dka.fdia_star_induct_var by auto
qed

lemma d_transitive_var: "(\<forall>y. |x\<rangle> |x\<rangle> y \<le> |x\<rangle> y) \<Longrightarrow> (\<forall>y. |x\<rangle> y = |x\<rangle> |x\<^sup>\<star>\<rangle> y)"
proof -
  assume "\<forall>y. |x\<rangle> |x\<rangle> y \<le> |x\<rangle> y"
  then have "\<forall>a. |x\<rangle> |x\<^sup>\<star>\<rangle> a = |x\<rangle> a"
    by (metis (full_types) d_transitive local.dka.fd_def local.dka.fdia_d_simp local.star_slide_var mult_assoc)
  then show ?thesis
    by presburger
qed

lemma d_transitive_PreLoebian_imp_Loebian: "(\<forall>y. |x\<rangle> |x\<rangle> y \<le> |x\<rangle> y) \<Longrightarrow> PreLoebian x \<Longrightarrow> Loebian x"
proof -
  assume wt: "(\<forall>y. |x\<rangle> |x\<rangle> y \<le> |x\<rangle> y)"
  and "PreLoebian x"
  hence "\<forall>y. |x\<rangle> y \<le> |x\<rangle> |x\<^sup>\<star>\<rangle> \<Omega> x y"
    using PreLoebian_def local.ads_d_def local.dka.fd_def local.ds.fd_iso1 by auto
  hence "\<forall>y. |x\<rangle> y \<le> |x\<rangle> \<Omega> x y"
    by (metis wt d_transitive_var)
  then show "Loebian x"
    using Loebian_def fdia_def by auto
qed

lemma d_transitive_Noetherian_iff_Loebian: "\<forall>y. |x\<rangle> |x\<rangle> y \<le> |x\<rangle> y \<Longrightarrow> Noetherian x \<longleftrightarrow> Loebian x"
  using Loebian_imp_Noetherian Noetherian_iff_PreLoebian d_transitive_PreLoebian_imp_Loebian by blast

lemma Loeb_iff_box_Loeb: "Loebian x \<longleftrightarrow> (\<forall>y. |x] (ad ( |x] y ) + d y) \<le> |x] y)"
proof -
  have "Loebian x \<longleftrightarrow> (\<forall>y. |x\<rangle> y \<le> |x\<rangle> (d y \<cdot> |x] (ad y)))"
    using Loebian_def omega_fbox by auto
  also have "... \<longleftrightarrow> (\<forall>y. ad ( |x\<rangle> (d y \<cdot> |x] (ad y)) ) \<le> ad ( |x\<rangle> y ))"
    using a_antitone' fdia_def by fastforce
  also have "... \<longleftrightarrow> (\<forall>y. |x] ad (d y \<cdot> |x] (ad y)) \<le> |x] (ad y))"
    by (simp add: fdia_fbox_de_morgan_2)
  also have "... \<longleftrightarrow> (\<forall>y. |x] (d (ad y) + ad ( |x] (ad y) )) \<le> |x] (ad y))"
    by (simp add: local.ads_d_def local.fbox_def)
  finally show ?thesis
    by (metis add_commute local.a_d_closed local.ads_d_def local.apd_d_def local.fbox_def)
qed

end

subsection \<open>Divergence Kleene Algebras and Separation of Termination\<close>

text \<open>The notion of divergence has been added to modal Kleene algebras in~\cite{DesharnaisMoellerStruthLMCS}.
More facts about divergence could be added in the future. Some could be adapted from omega algebras.\<close>

class nabla_op =
  fixes nabla :: "'a \<Rightarrow> 'a" ("\<nabla>_" [999] 1000)

class fdivergence_kleene_algebra = antidomain_kleene_algebra + nabla_op +
  assumes nabla_closure [simp]: "d \<nabla> x = \<nabla> x"
  and nabla_unfold: "\<nabla> x \<le> |x\<rangle> \<nabla> x"
  and nabla_coinduction: "d y \<le> |x\<rangle> y + d z \<Longrightarrow> d y \<le> \<nabla> x + |x\<^sup>\<star>\<rangle> z"

begin

lemma nabla_coinduction_var: "d y \<le> |x\<rangle> y \<Longrightarrow> d y \<le> \<nabla> x"
proof -
  assume "d y \<le> |x\<rangle> y"
  hence "d y \<le> |x\<rangle> y + d 0"
    by simp
  hence "d y \<le> \<nabla> x + |x\<^sup>\<star>\<rangle> 0"
    using nabla_coinduction by blast
  thus "d y \<le> \<nabla> x"
    by (simp add: fdia_def)
qed

lemma nabla_unfold_eq [simp]: "|x\<rangle> \<nabla> x = \<nabla> x"
proof -
  have f1: "ad (ad (x \<cdot> \<nabla>x)) = ad (ad (x \<cdot> \<nabla>x)) + \<nabla>x"
    using local.ds.fd_def local.join.sup.order_iff local.nabla_unfold by presburger
  then have "ad (ad (x \<cdot> \<nabla>x)) \<cdot> ad (ad \<nabla>x) = \<nabla>x"
    by (metis local.ads_d_def local.dpdz.dns5 local.dpdz.dsg4 local.join.sup_commute local.nabla_closure)
  then show ?thesis
    using f1 by (metis local.ads_d_def local.ds.fd_def local.ds.fd_subdist_2 local.join.sup.order_iff local.join.sup_commute nabla_coinduction_var)
qed

lemma nabla_subdist: "\<nabla> x \<le> \<nabla> (x + y)"
proof -
  have "d \<nabla> x \<le> \<nabla> (x + y)"
    by (metis local.ds.fd_iso2 local.join.sup.cobounded1 local.nabla_closure nabla_coinduction_var nabla_unfold_eq)
  thus ?thesis
    by simp
qed

lemma nabla_iso: "x \<le> y \<Longrightarrow> \<nabla> x \<le> \<nabla> y"
  by (metis less_eq_def nabla_subdist)

lemma nabla_omega: "\<Omega> x (d y) = 0 \<Longrightarrow> d y \<le> \<nabla> x"
  using omega_zero_equiv_1 nabla_coinduction_var by fastforce

lemma nabla_noether: "\<nabla> x = 0 \<Longrightarrow> Noetherian x"
  using local.join.le_bot local.noetherian_alt nabla_coinduction_var by blast

lemma nabla_preloeb: "\<nabla> x = 0 \<Longrightarrow> PreLoebian x"
  using Noetherian_iff_PreLoebian nabla_noether by auto

lemma star_nabla_1 [simp]: "|x\<^sup>\<star>\<rangle> \<nabla> x = \<nabla> x"
proof (rule antisym)
  show "|x\<^sup>\<star>\<rangle> \<nabla> x \<le> \<nabla> x"
    by (metis local.dka.fdia_star_induct_var local.eq_iff local.nabla_closure nabla_unfold_eq)
  show "\<nabla> x \<le> |x\<^sup>\<star>\<rangle> \<nabla> x"
    by (metis local.ds.fd_iso2 local.star_ext nabla_unfold_eq)
qed

lemma nabla_sum_expand [simp]: "|x\<rangle> \<nabla> (x + y) + |y\<rangle> \<nabla> (x + y) = \<nabla> (x + y)"
proof -
  have "d ((x + y) \<cdot> \<nabla>(x + y)) = \<nabla>(x + y)"
    using local.dka.fd_def nabla_unfold_eq by presburger
  thus ?thesis
    by (simp add: local.dka.fd_def)
qed

lemma wagner_3:
  assumes "d z + |x\<rangle> \<nabla> (x + y) = \<nabla> (x + y)"
  shows "\<nabla> (x + y) = \<nabla> x + |x\<^sup>\<star>\<rangle> z"
proof (rule antisym)
  have "d \<nabla>(x + y) \<le> d z + |x\<rangle> \<nabla>(x + y)"
    by (simp add: assms)
  thus "\<nabla> (x + y) \<le> \<nabla> x + |x\<^sup>\<star>\<rangle> z"
    by (metis add_commute nabla_closure nabla_coinduction)
  have "d z + |x\<rangle> \<nabla> (x + y) \<le> \<nabla> (x + y)"
    using assms by auto
  hence "|x\<^sup>\<star>\<rangle> z \<le> \<nabla> (x + y)"
    by (metis local.dka.fdia_star_induct local.nabla_closure)
  thus "\<nabla> x + |x\<^sup>\<star>\<rangle> z \<le> \<nabla> (x + y)"
    by (simp add: sup_least nabla_subdist)
qed

lemma nabla_sum_unfold [simp]: "\<nabla> x + |x\<^sup>\<star>\<rangle> |y\<rangle> \<nabla> (x + y) = \<nabla> (x + y)"
proof -
  have "\<nabla> (x + y) = |x\<rangle> \<nabla> (x + y) + |y\<rangle> \<nabla> (x + y)"
    by simp
  thus ?thesis
    by (metis add_commute local.dka.fd_def local.ds.fd_def local.ds.fdia_d_simp wagner_3)
qed

lemma nabla_separation: "y \<cdot> x \<le> x \<cdot> (x + y)\<^sup>\<star> \<Longrightarrow> (\<nabla> (x + y) = \<nabla> x + |x\<^sup>\<star>\<rangle> \<nabla> y)"
proof (rule antisym)
  assume quasi_comm: "y \<cdot> x \<le> x \<cdot> (x + y)\<^sup>\<star>"
  hence a: "y\<^sup>\<star> \<cdot> x \<le> x \<cdot> (x + y)\<^sup>\<star>"
    using quasicomm_var by blast
  have "\<nabla> (x + y) = \<nabla> y + |y\<^sup>\<star>\<cdot> x\<rangle> \<nabla> (x + y)"
    by (metis local.ds.fdia_mult local.join.sup_commute nabla_sum_unfold)
  also have "... \<le> \<nabla> y + |x \<cdot> (x + y)\<^sup>\<star>\<rangle> \<nabla> (x + y)"
    using a local.ds.fd_iso2 local.join.sup.mono by blast
  also have "... = \<nabla> y + |x\<rangle> |(x + y)\<^sup>\<star>\<rangle> \<nabla> (x + y)"
    by (simp add: fdia_def mult_assoc)
  finally have "\<nabla> (x + y) \<le> \<nabla> y + |x\<rangle> \<nabla> (x + y)"
    by (metis star_nabla_1)
  thus "\<nabla> (x + y) \<le> \<nabla> x + |x\<^sup>\<star>\<rangle> \<nabla> y"
    by (metis add_commute nabla_closure nabla_coinduction)
next
  have "\<nabla> x + |x\<^sup>\<star>\<rangle> \<nabla> y = \<nabla> x + |x\<^sup>\<star>\<rangle> |y\<rangle> \<nabla> y"
    by simp
  also have "... = \<nabla> x + |x\<^sup>\<star> \<cdot> y\<rangle> \<nabla> y"
    by (simp add: fdia_def mult_assoc)
  also have "... \<le> \<nabla> x + |x\<^sup>\<star> \<cdot> y\<rangle> \<nabla> (x + y)"
    using dpdz.dom_iso eq_refl fdia_def join.sup_ge2 join.sup_mono mult_isol nabla_iso by presburger
  also have "... = \<nabla> x + |x\<^sup>\<star>\<rangle> |y\<rangle> \<nabla> (x + y)"
    by (simp add: fdia_def mult_assoc)
  finally show "\<nabla> x + |x\<^sup>\<star>\<rangle> \<nabla> y \<le> \<nabla> (x + y)"
    by (metis nabla_sum_unfold)
qed

text \<open>The next lemma is a separation of termination theorem by Bachmair and Dershowitz~\cite{bachmair86commutation}.\<close>

lemma bachmair_dershowitz: "y \<cdot> x \<le> x \<cdot> (x + y)\<^sup>\<star> \<Longrightarrow> \<nabla> x + \<nabla> y = 0 \<longleftrightarrow> \<nabla> (x + y) = 0"
proof -
  assume quasi_comm: "y \<cdot> x \<le> x \<cdot> (x + y)\<^sup>\<star>"
  have "\<forall>x. |x\<rangle> 0 = 0"
    by (simp add: fdia_def)
  hence "\<nabla>y = 0 \<Longrightarrow> \<nabla>x + \<nabla>y = 0 \<longleftrightarrow> \<nabla>(x + y) = 0"
    using quasi_comm nabla_separation by presburger
  thus ?thesis
    using add_commute local.join.le_bot nabla_subdist by fastforce
qed

text \<open>The next lemma is a more complex separation of termination theorem by Doornbos,
Backhouse and van der Woude~\cite{doornbos97calculational}.\<close>

lemma separation_of_termination:
assumes "y \<cdot> x \<le> x \<cdot> (x + y)\<^sup>\<star> + y"
shows "\<nabla> x + \<nabla> y = 0 \<longleftrightarrow> \<nabla> (x + y) = 0"
proof
  assume xy_wf: "\<nabla> x + \<nabla> y = 0"
  hence x_preloeb: "\<nabla> (x + y) \<le> |x\<^sup>\<star>\<rangle> \<Omega> x (\<nabla> (x + y))"
    by (metis PreLoebian_def no_trivial_inverse nabla_closure nabla_preloeb)
  hence y_div: "\<nabla> y = 0"
    using add_commute no_trivial_inverse xy_wf by blast
  have "\<nabla> (x + y) \<le> |y\<rangle> \<nabla> (x + y) + |x\<rangle> \<nabla> (x + y)"
    by (simp add: local.join.sup_commute)
  hence "\<nabla> (x + y) \<cdot> ad ( |x\<rangle> \<nabla> (x + y) ) \<le> |y\<rangle> \<nabla>(x + y)"
    by (simp add: local.da_shunt1 local.dka.fd_def local.join.sup_commute)
  hence "\<Omega> x \<nabla>(x + y) \<le> |y\<rangle> \<nabla> (x + y)"
    by (simp add: fdia_def omega_fdia)
  also have "... \<le> |y\<rangle> |x\<^sup>\<star>\<rangle> (\<Omega> x \<nabla>(x + y))"
    using local.dpdz.dom_iso local.ds.fd_iso1 x_preloeb by blast
  also have "... = |y \<cdot> x\<^sup>\<star>\<rangle> (\<Omega> x \<nabla>(x + y))"
    by (simp add: fdia_def mult_assoc)
  also have "... \<le> |x \<cdot> (x + y)\<^sup>\<star> + y\<rangle> (\<Omega> x \<nabla>(x + y))"
    using assms local.ds.fd_iso2 local.lazycomm_var by blast
  also have "... = |x \<cdot> (x + y)\<^sup>\<star>\<rangle> (\<Omega> x \<nabla>(x + y)) + |y\<rangle> (\<Omega> x \<nabla>(x + y))"
    by (simp add: local.dka.fd_def)
  also have "... \<le> |(x \<cdot> (x + y)\<^sup>\<star>)\<rangle> \<nabla>(x + y) + |y\<rangle> (\<Omega> x \<nabla>(x + y))"
    using local.add_iso local.dpdz.domain_1'' local.ds.fd_iso1 local.omega_fdia by auto
  also have "... \<le> |x\<rangle> |(x + y)\<^sup>\<star>\<rangle> \<nabla>(x + y) + |y\<rangle> (\<Omega> x \<nabla>(x + y))"
    by (simp add: fdia_def mult_assoc)
  finally have "\<Omega> x \<nabla>(x + y) \<le> |x\<rangle> \<nabla>(x + y) + |y\<rangle> (\<Omega> x \<nabla>(x + y))"
    by (metis star_nabla_1)
  hence "\<Omega> x \<nabla>(x + y) \<cdot> ad ( |x\<rangle> \<nabla>(x + y) ) \<le> |y\<rangle> (\<Omega> x \<nabla>(x + y))"
    by (simp add: local.da_shunt1 local.dka.fd_def)
  hence "\<Omega> x \<nabla>(x + y) \<le> |y\<rangle> (\<Omega> x \<nabla>(x + y))"
    by (simp add: omega_fdia mult_assoc)
  hence "(\<Omega> x \<nabla>(x + y)) = 0"
    by (metis noetherian_alt omega_dom nabla_noether y_div)
  thus "\<nabla> (x + y) = 0"
    using local.dka.fd_def local.join.le_bot x_preloeb by auto
next
  assume "\<nabla> (x + y) = 0"
  thus "(\<nabla> x) + (\<nabla> y) = 0"
    by (metis local.join.le_bot local.join.sup.order_iff local.join.sup_commute nabla_subdist)
qed

text \<open>The final examples can be found in~\cite{guttmannstruthweber11algmeth}.\<close>

definition T :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" ("_ \<leadsto> _ \<leadsto> _" [61,61,61] 60)
  where "p\<leadsto>x\<leadsto>q \<equiv> ad p + |x] d q"

lemma T_d [simp]: "d (p\<leadsto>x\<leadsto>q) = p\<leadsto>x\<leadsto>q"
  using T_def local.a_d_add_closure local.fbox_def by auto

lemma T_p: "d p \<cdot> (p\<leadsto>x\<leadsto>q) = d p \<cdot> |x] d q"
proof -
  have "d p \<cdot> (p\<leadsto>x\<leadsto>q) = ad (ad p + ad (p\<leadsto>x\<leadsto>q))"
    using T_d local.ads_d_def by auto
  thus ?thesis
    using T_def add_commute local.a_mult_add local.ads_d_def by auto
qed

lemma T_a [simp]: "ad p \<cdot> (p\<leadsto>x\<leadsto>q) = ad p"
  by (metis T_d T_def local.a_d_closed local.ads_d_def local.apd_d_def local.dpdz.dns5 local.join.sup.left_idem)

lemma T_seq: "(p\<leadsto>x\<leadsto>q) \<cdot> |x](q\<leadsto>y\<leadsto>s) \<le> p\<leadsto>x \<cdot> y\<leadsto>s"
proof -
  have f1: "|x] q = |x] d q"
    using local.fbox_simp by auto
  have "ad p \<cdot> ad (x \<cdot> ad (q\<leadsto>y\<leadsto>s)) + |x] d q \<cdot> |x] (ad q + |y] d s) \<le> ad p + |x] d q \<cdot> |x] (ad q + |y] d s)"
    using local.a_subid_aux2 local.add_iso by blast
  hence "(p\<leadsto>x\<leadsto>q) \<cdot> |x](q\<leadsto>y\<leadsto>s) \<le> ad p + |x](d q \<cdot> (q\<leadsto>y\<leadsto>s))"
    by (metis T_d T_def f1 local.distrib_right' local.fbox_add1 local.fbox_def)
  also have "... = ad p + |x](d q \<cdot> (ad q + |y] d s))"
    by (simp add: T_def)
  also have "... = ad p + |x](d q \<cdot> |y] d s)"
    using T_def T_p by auto
  also have "... \<le> ad p + |x] |y] d s"
    by (metis (no_types, lifting) local.dka.dom_subid_aux2 local.dka.dsg3 local.eq_iff local.fbox_iso local.join.sup.mono)
  finally show ?thesis
    by (simp add: T_def fbox_mult)
qed

lemma T_square: "(p\<leadsto>x\<leadsto>q) \<cdot> |x](q\<leadsto>x\<leadsto>p) \<le> p\<leadsto>x\<cdot>x\<leadsto>p"
  by (simp add: T_seq)

lemma T_segerberg [simp]: "d p \<cdot> |x\<^sup>\<star>](p\<leadsto>x\<leadsto>p) = |x\<^sup>\<star>] d p"
  using T_def add_commute local.fbox_segerberg local.fbox_simp by force

lemma lookahead [simp]: "|x\<^sup>\<star>](d p \<cdot> |x] d p) = |x\<^sup>\<star>] d p"
  by (metis (full_types) local.dka.dsg3 local.fbox_add1 local.fbox_mult local.fbox_simp local.fbox_star_unfold_var local.star_slide_var local.star_trans_eq)

lemma alternation: "d p \<cdot> |x\<^sup>\<star>]((p\<leadsto>x\<leadsto>q) \<cdot> (q\<leadsto>x\<leadsto>p)) = |(x\<cdot>x)\<^sup>\<star>](d p \<cdot> (q\<leadsto>x\<leadsto>p)) \<cdot> |x\<cdot>(x\<cdot>x)\<^sup>\<star>](d q \<cdot> (p\<leadsto>x\<leadsto>q))"
proof -
  have fbox_simp_2: "\<And>x p. |x]p = d( |x] p )"
    using local.a_d_closed local.ads_d_def local.apd_d_def local.fbox_def by fastforce
  have "|(x\<cdot>x)\<^sup>\<star>]((p\<leadsto>x\<leadsto>q) \<cdot> |x](q\<leadsto>x\<leadsto>p) \<cdot> (q\<leadsto>x\<leadsto>p) \<cdot> |x](p\<leadsto>x\<leadsto>q)) \<le> |(x\<cdot>x)\<^sup>\<star>]((p\<leadsto>x\<leadsto>q) \<cdot> |x](q\<leadsto>x\<leadsto>p))"
    using local.dka.domain_1'' local.fbox_iso local.order_trans by blast
  also have "... \<le> |(x\<cdot>x)\<^sup>\<star>](p\<leadsto>x\<cdot>x\<leadsto>p)"
    using T_seq local.dka.dom_iso local.fbox_iso by blast
  finally have 1: "|(x\<cdot>x)\<^sup>\<star>]((p\<leadsto>x\<leadsto>q) \<cdot> |x](q\<leadsto>x\<leadsto>p) \<cdot> (q\<leadsto>x\<leadsto>p) \<cdot> |x](p\<leadsto>x\<leadsto>q)) \<le> |(x\<cdot>x)\<^sup>\<star>](p\<leadsto>x\<cdot>x\<leadsto>p)".
  have "d p \<cdot> |x\<^sup>\<star>]((p\<leadsto>x\<leadsto>q) \<cdot> (q\<leadsto>x\<leadsto>p)) = d p \<cdot> |1+x] |(x\<cdot>x)\<^sup>\<star>]((p\<leadsto>x\<leadsto>q) \<cdot> (q\<leadsto>x\<leadsto>p))"
    by (metis (full_types) fbox_mult meyer_1)
  also have "... = d p \<cdot> |(x\<cdot>x)\<^sup>\<star>]((p\<leadsto>x\<leadsto>q) \<cdot> (q\<leadsto>x\<leadsto>p)) \<cdot> |x\<cdot>(x\<cdot>x)\<^sup>\<star>]((p\<leadsto>x\<leadsto>q) \<cdot> (q\<leadsto>x\<leadsto>p))"
    using fbox_simp_2 fbox_mult fbox_add2 mult_assoc by auto
  also have "... = d p \<cdot> |(x\<cdot>x)\<^sup>\<star>]((p\<leadsto>x\<leadsto>q) \<cdot> (q\<leadsto>x\<leadsto>p)) \<cdot> |(x\<cdot>x)\<^sup>\<star>\<cdot>x]((p\<leadsto>x\<leadsto>q) \<cdot> (q\<leadsto>x\<leadsto>p))"
    by (simp add: star_slide)
  also have "... = d p \<cdot> |(x\<cdot>x)\<^sup>\<star>]((p\<leadsto>x\<leadsto>q) \<cdot> (q\<leadsto>x\<leadsto>p)) \<cdot> |(x\<cdot>x)\<^sup>\<star>] |x]((p\<leadsto>x\<leadsto>q) \<cdot> (q\<leadsto>x\<leadsto>p))"
    by (simp add: fbox_mult)
  also have "... = d p \<cdot> |(x\<cdot>x)\<^sup>\<star>]((p\<leadsto>x\<leadsto>q) \<cdot> (q\<leadsto>x\<leadsto>p) \<cdot> |x]((p\<leadsto>x\<leadsto>q) \<cdot> (q\<leadsto>x\<leadsto>p)))"
    by (metis T_d fbox_simp_2 local.dka.dom_mult_closed local.fbox_add1 mult_assoc)
  also have "... = d p \<cdot> |(x\<cdot>x)\<^sup>\<star>]((p\<leadsto>x\<leadsto>q) \<cdot> |x](q\<leadsto>x\<leadsto>p) \<cdot> (q\<leadsto>x\<leadsto>p) \<cdot> |x](p\<leadsto>x\<leadsto>q))"
  proof -
    have f1: "d ((q \<leadsto> x \<leadsto> p) \<cdot> |x] (p \<leadsto> x \<leadsto> q)) = (q \<leadsto> x \<leadsto> p) \<cdot> |x] (p \<leadsto> x \<leadsto> q)"
      by (metis (full_types) T_d fbox_simp_2 local.dka.dsg3)
    then have "|(x \<cdot> x)\<^sup>\<star>] (d ( |x] (q \<leadsto> x \<leadsto> p)) \<cdot> ((q \<leadsto> x \<leadsto> p) \<cdot> |x] (p \<leadsto> x \<leadsto> q))) = |(x \<cdot> x)\<^sup>\<star>] d ( |x] (q \<leadsto> x \<leadsto> p)) \<cdot> |(x \<cdot> x)\<^sup>\<star>] ((q \<leadsto> x \<leadsto> p) \<cdot> |x] (p \<leadsto> x \<leadsto> q))"
      by (metis (full_types) fbox_simp_2 local.fbox_add1)
    then have f2: "|(x \<cdot> x)\<^sup>\<star>] (d ( |x] (q \<leadsto> x \<leadsto> p)) \<cdot> ((q \<leadsto> x \<leadsto> p) \<cdot> |x] (p \<leadsto> x \<leadsto> q))) = ad ((x \<cdot> x)\<^sup>\<star> \<cdot> ad ((q \<leadsto> x \<leadsto> p) \<cdot> |x] (p \<leadsto> x \<leadsto> q)) + (x \<cdot> x)\<^sup>\<star> \<cdot> ad (d ( |x] (q \<leadsto> x \<leadsto> p))))"
      by (simp add: add_commute local.fbox_def)
    have "d ( |x] (p \<leadsto> x \<leadsto> q)) \<cdot> d ( |x] (q \<leadsto> x \<leadsto> p)) = |x] ((p \<leadsto> x \<leadsto> q) \<cdot> (q \<leadsto> x \<leadsto> p))"
      by (metis (no_types) T_d fbox_simp_2 local.fbox_add1)
    then have "d ((q \<leadsto> x \<leadsto> p) \<cdot> |x] (p \<leadsto> x \<leadsto> q)) \<cdot> d (d ( |x] (q \<leadsto> x \<leadsto> p))) = (q \<leadsto> x \<leadsto> p) \<cdot> |x] ((p \<leadsto> x \<leadsto> q) \<cdot> (q \<leadsto> x \<leadsto> p))"
      using f1 fbox_simp_2 mult_assoc by force
    then have "|(x \<cdot> x)\<^sup>\<star>] (d ( |x] (q \<leadsto> x \<leadsto> p)) \<cdot> ((q \<leadsto> x \<leadsto> p) \<cdot> |x] (p \<leadsto> x \<leadsto> q))) = |(x \<cdot> x)\<^sup>\<star>] ((q \<leadsto> x \<leadsto> p) \<cdot> |x] ((p \<leadsto> x \<leadsto> q) \<cdot> (q \<leadsto> x \<leadsto> p)))"
      using f2 by (metis (no_types) local.ans4 local.fbox_add1 local.fbox_def)
    then show ?thesis
      by (metis (no_types) T_d fbox_simp_2 local.dka.dsg3 local.fbox_add1 mult_assoc)
  qed
  also have "... = d p \<cdot> |(x\<cdot>x)\<^sup>\<star>](p\<leadsto>x\<cdot>x\<leadsto>p) \<cdot> |(x\<cdot>x)\<^sup>\<star>]((p\<leadsto>x\<leadsto>q) \<cdot> |x](q\<leadsto>x\<leadsto>p) \<cdot> (q\<leadsto>x\<leadsto>p) \<cdot> |x](p\<leadsto>x\<leadsto>q))" using "1"
    by (metis fbox_simp_2 local.dka.dns5 local.dka.dsg4 local.join.sup.absorb2 mult_assoc)
  also have "... = |(x\<cdot>x)\<^sup>\<star>](d p \<cdot> (p\<leadsto>x\<leadsto>q) \<cdot> |x](q\<leadsto>x\<leadsto>p) \<cdot> (q\<leadsto>x\<leadsto>p) \<cdot> |x](p\<leadsto>x\<leadsto>q))"
    using T_segerberg local.a_d_closed local.ads_d_def local.apd_d_def local.distrib_left local.fbox_def mult_assoc by auto
  also have "... = |(x\<cdot>x)\<^sup>\<star>](d p \<cdot> |x] d q \<cdot> |x](q\<leadsto>x\<leadsto>p) \<cdot> (q\<leadsto>x\<leadsto>p) \<cdot> |x](p\<leadsto>x\<leadsto>q))"
    by (simp add: T_p)
  also have "... = |(x\<cdot>x)\<^sup>\<star>](d p \<cdot> |x] d q \<cdot> |x] |x] d p \<cdot> (q\<leadsto>x\<leadsto>p) \<cdot> |x](p\<leadsto>x\<leadsto>q))"
    by (metis T_d T_p fbox_simp_2 fbox_add1 fbox_simp mult_assoc)
  also have "... = |(x\<cdot>x)\<^sup>\<star>](d p \<cdot> |x\<cdot>x] d p \<cdot> (q\<leadsto>x\<leadsto>p) \<cdot> |x] d q \<cdot> |x](p\<leadsto>x\<leadsto>q))"
  proof -
    have f1: "ad (x \<cdot> ad ( |x] d p)) = |x \<cdot> x] d p"
      using local.fbox_def local.fbox_mult by presburger
    have f2: "ad (d q \<cdot> d (x \<cdot> ad (d p))) = q \<leadsto> x \<leadsto> p"
      by (simp add: T_def local.a_de_morgan_var_4 local.fbox_def)
    have "ad q + |x] d p = ad (d q \<cdot> d (x \<cdot> ad (d p)))"
      by (simp add: local.a_de_morgan_var_4 local.fbox_def)
    then have "ad (x \<cdot> ad ( |x] d p)) \<cdot> ((q \<leadsto> x \<leadsto> p) \<cdot> |x] d q) = ad (x \<cdot> ad ( |x] d p)) \<cdot> ad (x \<cdot> ad (d q)) \<cdot> (ad q + |x] d p)"
      using f2 by (metis (no_types) local.am2 local.fbox_def mult_assoc)
    then show ?thesis
      using f1 by (simp add: T_def local.am2 local.fbox_def mult_assoc)
  qed
  also have "... = |(x\<cdot>x)\<^sup>\<star>](d p \<cdot> |x\<cdot>x] d p \<cdot> (q\<leadsto>x\<leadsto>p) \<cdot> |x](d q \<cdot> (p\<leadsto>x\<leadsto>q)))"
    using local.a_d_closed local.ads_d_def local.apd_d_def local.distrib_left local.fbox_def mult_assoc by auto
  also have "... = |(x\<cdot>x)\<^sup>\<star>](d p \<cdot> |x\<cdot>x] d p) \<cdot> |(x\<cdot>x)\<^sup>\<star>](q\<leadsto>x\<leadsto>p) \<cdot> |(x\<cdot>x)\<^sup>\<star>] |x](d q \<cdot> (p\<leadsto>x\<leadsto>q))"
    by (metis T_d fbox_simp_2 local.dka.dom_mult_closed local.fbox_add1)
  also have "... = |(x\<cdot>x)\<^sup>\<star>](d p \<cdot> (q\<leadsto>x\<leadsto>p)) \<cdot> |(x\<cdot>x)\<^sup>\<star>] |x] (d q \<cdot> (p\<leadsto>x\<leadsto>q))"
    by (metis T_d local.fbox_add1 local.fbox_simp lookahead)
  finally show ?thesis
    by (metis fbox_mult star_slide)
qed

lemma "|(x\<cdot>x)\<^sup>\<star>] d p \<cdot> |x\<cdot>(x\<cdot>x)\<^sup>\<star>] ad p = d p \<cdot> |x\<^sup>\<star>]((p\<leadsto>x\<leadsto>ad p) \<cdot> (ad p\<leadsto>x\<leadsto>p))"
  using alternation local.a_d_closed local.ads_d_def local.apd_d_def by auto

lemma "|x\<^sup>\<star>] d p = d p \<cdot> |x\<^sup>\<star>](p\<leadsto>x\<leadsto>p)"
  by (simp add: alternation)

end

end
