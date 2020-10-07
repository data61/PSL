(* Title:      Kleene algebra with tests
   Author:     Alasdair Armstrong, Victor B. F. Gomes, Georg Struth
   Maintainer: Georg Struth <g.struth at sheffield.ac.uk>
*)

section \<open>Kleene Algebra with Tests\<close>

theory KAT
  imports Kleene_Algebra.Kleene_Algebra Conway_Tests
begin

text \<open>
  First, we study left Kleene algebras with tests which also have only a left zero.
  These structures can be expanded to demonic refinement algebras.
\<close>

class left_kat_zerol =  left_kleene_algebra_zerol + test_semiring_zerol
begin

lemma star_n_export1: "(n x \<cdot> y)\<^sup>\<star> \<cdot> n x \<le> n x \<cdot> y\<^sup>\<star>"
  by (simp add: local.n_restrictr local.star_sim1)

lemma star_test_export1: "test p \<Longrightarrow> (p \<cdot> x)\<^sup>\<star> \<cdot> p \<le> p \<cdot> x\<^sup>\<star>"
  using star_n_export1 by auto

lemma star_n_export2: "(n x \<cdot> y)\<^sup>\<star> \<cdot> n x \<le> y\<^sup>\<star> \<cdot> n x"
  by (simp add: local.mult_isor local.n_restrictl local.star_iso)

lemma star_test_export2: "test p \<Longrightarrow> (p \<cdot> x)\<^sup>\<star> \<cdot> p \<le> x\<^sup>\<star> \<cdot> p"
  using star_n_export2 by auto

lemma star_n_export_left: "x \<cdot> n y \<le> n y \<cdot> x \<Longrightarrow> x\<^sup>\<star> \<cdot> n y = n y \<cdot> (x \<cdot> n y)\<^sup>\<star>"
proof (rule antisym)
  assume a1: "x \<cdot> n y \<le> n y \<cdot> x"
  hence "x \<cdot> n y = n y \<cdot> x \<cdot> n y"
    by (simp add: local.n_kat_2_opp)
  thus "x\<^sup>\<star> \<cdot> n y \<le> n y \<cdot> (x \<cdot> n y)\<^sup>\<star>"
    by (simp add: local.star_sim1 mult_assoc)
next
  assume a1: "x \<cdot> n y \<le> n y \<cdot> x"
  thus "n y \<cdot> (x \<cdot> n y)\<^sup>\<star> \<le> x\<^sup>\<star> \<cdot> n y"
using local.star_slide star_n_export2 by force
qed

lemma star_test_export_left: "test p \<Longrightarrow> x \<cdot> p \<le> p \<cdot> x \<longrightarrow> x\<^sup>\<star> \<cdot> p = p \<cdot> (x \<cdot> p)\<^sup>\<star>"
  using star_n_export_left by auto

lemma star_n_export_right: "x \<cdot> n y \<le> n y \<cdot> x \<Longrightarrow> x\<^sup>\<star> \<cdot> n y = (n y \<cdot> x)\<^sup>\<star> \<cdot> n y"
  by (simp add: local.star_slide star_n_export_left)

lemma star_test_export_right: "test p \<Longrightarrow> x \<cdot> p \<le> p \<cdot> x \<longrightarrow> x\<^sup>\<star> \<cdot> p = (p \<cdot> x)\<^sup>\<star> \<cdot> p"
  using star_n_export_right by auto

lemma star_n_folk: "n z \<cdot> x = x \<cdot> n z \<Longrightarrow> n z \<cdot> y = y \<cdot> n z \<Longrightarrow> (n z \<cdot> x + t z \<cdot> y)\<^sup>\<star> \<cdot> n z = n z \<cdot> (n z \<cdot> x)\<^sup>\<star>"
proof -
assume a: "n z \<cdot> x = x \<cdot> n z" and b: "n z \<cdot> y = y \<cdot> n z"
  hence "n z \<cdot> (n z \<cdot> x + t z \<cdot> y) = (n z \<cdot> x + t z \<cdot> y) \<cdot> n z"
    using local.comm_add_var local.t_n_closed local.test_def by blast
  hence "(n z \<cdot> x + t z \<cdot> y)\<^sup>\<star> \<cdot> n z = n z \<cdot> ((n z \<cdot> x + t z \<cdot> y) \<cdot> n z)\<^sup>\<star>"
    using local.order_refl star_n_export_left by presburger
  also have "... = n z \<cdot> (n z \<cdot> x \<cdot> n z + t z \<cdot> y \<cdot> n z)\<^sup>\<star>"
    by simp
  also have "... = n z \<cdot> (n z \<cdot> n z \<cdot> x + t z \<cdot> n z \<cdot> y)\<^sup>\<star>"
    by (simp add: a b mult_assoc)
 also have "... = n z \<cdot> (n z \<cdot> x + 0 \<cdot> y)\<^sup>\<star>"
  by (simp add: local.n_mult_comm)
  finally show "(n z \<cdot> x + t z \<cdot> y)\<^sup>\<star> \<cdot> n z = n z \<cdot> (n z \<cdot> x)\<^sup>\<star>"
    by simp
qed

lemma star_test_folk: "test p \<Longrightarrow> p \<cdot> x = x \<cdot> p \<longrightarrow> p \<cdot> y = y \<cdot> p \<longrightarrow> (p \<cdot> x + !p \<cdot> y)\<^sup>\<star> \<cdot> p = p \<cdot> (p \<cdot> x)\<^sup>\<star>"
  using star_n_folk by auto

end

class kat_zerol = kleene_algebra_zerol + test_semiring_zerol
begin

sublocale conway: near_conway_zerol_tests star ..

lemma n_star_sim_right: "n y \<cdot> x = x \<cdot> n y \<Longrightarrow> n y \<cdot> x\<^sup>\<star> = (n y \<cdot> x)\<^sup>\<star> \<cdot> n y"
  by (metis local.n_mult_idem local.star_sim3 mult_assoc)

lemma star_sim_right: "test p \<Longrightarrow> p \<cdot> x = x \<cdot> p \<longrightarrow> p \<cdot> x\<^sup>\<star> = (p \<cdot> x)\<^sup>\<star> \<cdot> p"
  using n_star_sim_right by auto

lemma n_star_sim_left: "n y \<cdot> x = x \<cdot> n y \<Longrightarrow> n y \<cdot> x\<^sup>\<star> = n y \<cdot> (x \<cdot> n y)\<^sup>\<star>"
  by (metis local.star_slide n_star_sim_right)

lemma star_sim_left: "test p \<Longrightarrow> p \<cdot> x = x \<cdot> p \<longrightarrow> p \<cdot> x\<^sup>\<star> = p \<cdot> (x \<cdot> p)\<^sup>\<star>"
  using n_star_sim_left by auto

lemma n_comm_star: "n z \<cdot> x = x \<cdot> n z \<Longrightarrow>  n z \<cdot> y = y \<cdot> n z \<Longrightarrow> n z \<cdot> x \<cdot> (n z \<cdot> y)\<^sup>\<star> = n z \<cdot> x \<cdot> y\<^sup>\<star>"
  using mult_assoc n_star_sim_left by presburger

lemma comm_star: "test p \<Longrightarrow> p \<cdot> x = x \<cdot> p \<longrightarrow>  p \<cdot> y = y \<cdot> p \<longrightarrow> p \<cdot> x \<cdot> (p \<cdot> y)\<^sup>\<star> = p \<cdot> x \<cdot> y\<^sup>\<star>"
  using n_comm_star by auto

lemma n_star_sim_right_var: "n y \<cdot> x = x \<cdot> n y \<Longrightarrow> x\<^sup>\<star> \<cdot> n y = n y \<cdot> (x \<cdot> n y)\<^sup>\<star>"
  using local.star_sim3 n_star_sim_left by force

lemma star_sim_right_var: "test p \<Longrightarrow> p \<cdot> x = x \<cdot> p \<longrightarrow> x\<^sup>\<star> \<cdot> p = p \<cdot> (x \<cdot> p)\<^sup>\<star>"
  using n_star_sim_right_var by auto

end

text \<open>Finally, we define Kleene algebra with tests.\<close>

class kat = kleene_algebra + test_semiring

begin

sublocale conway: test_pre_conway star ..

end

end
