(* Title:      Kleene algebra with tests
   Author:     Alasdair Armstrong, Victor B. F. Gomes, Georg Struth
   Maintainer: Georg Struth <g.struth at sheffield.ac.uk>
*)

section \<open>Pre-Conway Algebra with Tests\<close>

theory Conway_Tests
  imports Kleene_Algebra.Conway Test_Dioid

begin

class near_conway_zerol_tests = near_conway_zerol + test_near_semiring_zerol_distrib

begin

lemma n_preserve1_var: "n x \<cdot> y \<le> n x \<cdot> y \<cdot> n x \<Longrightarrow> n x \<cdot> (n x \<cdot> y + t x \<cdot> z)\<^sup>\<dagger> \<le> (n x \<cdot> y)\<^sup>\<dagger> \<cdot> n x"
proof -
  assume a: "n x \<cdot> y \<le> n x \<cdot> y \<cdot> n x"
  have "n x \<cdot> (n x \<cdot> y + t x \<cdot> z) = n x \<cdot> y"
    by (metis (no_types) local.add_zeror local.annil local.n_left_distrib local.n_mult_idem local.test_mult_comp mult_assoc)
  hence "n x \<cdot> (n x \<cdot> y + t x \<cdot> z) \<le> n x \<cdot> y \<cdot> n x"
    by (simp add: a)
  thus " n x \<cdot> (n x \<cdot> y + t x \<cdot> z)\<^sup>\<dagger> \<le> (n x \<cdot> y)\<^sup>\<dagger> \<cdot> n x"
    by (simp add: local.dagger_simr)
qed

lemma test_preserve1_var: "test p \<Longrightarrow> p \<cdot> x \<le> p \<cdot> x \<cdot> p \<Longrightarrow> p \<cdot> (p \<cdot> x + !p \<cdot> y)\<^sup>\<dagger> \<le> (p \<cdot> x)\<^sup>\<dagger> \<cdot> p"
  by (metis local.test_double_comp_var n_preserve1_var)

end

class test_pre_conway = pre_conway + test_pre_dioid_zerol

begin

subclass near_conway_zerol_tests
  by (unfold_locales)

lemma test_preserve: "test p \<Longrightarrow>  p \<cdot> x \<le> p \<cdot> x \<cdot> p  \<Longrightarrow> p \<cdot> x\<^sup>\<dagger> = (p \<cdot> x)\<^sup>\<dagger> \<cdot> p"
  using local.preservation1_eq local.test_restrictr by auto

lemma test_preserve1: "test p \<Longrightarrow> p \<cdot> x \<le> p \<cdot> x \<cdot> p \<Longrightarrow> p \<cdot> (p \<cdot> x + !p \<cdot> y)\<^sup>\<dagger> = (p \<cdot> x)\<^sup>\<dagger> \<cdot> p"
proof (rule antisym)
  assume a: "test p" 
  and b: "p \<cdot> x \<le> p \<cdot> x \<cdot> p"
  hence "p \<cdot> (p \<cdot> x + !p \<cdot> y) \<le> (p \<cdot> x) \<cdot> p"
    by (metis local.add_0_right local.annil local.n_left_distrib_var local.test_comp_mult2 local.test_mult_idem_var mult_assoc)
  thus "p \<cdot> (p \<cdot> x + !p \<cdot> y)\<^sup>\<dagger> \<le> (p \<cdot> x)\<^sup>\<dagger> \<cdot> p"
    using local.dagger_simr by blast
next
  assume a: "test p" 
  and b: "p \<cdot> x \<le> p \<cdot> x \<cdot> p"
  hence "(p \<cdot> x)\<^sup>\<dagger> \<cdot> p = p \<cdot> (p \<cdot> x \<cdot> p)\<^sup>\<dagger>"
    by (metis dagger_slide local.test_mult_idem_var mult_assoc)
  also have "... = p \<cdot> (p \<cdot> x)\<^sup>\<dagger>"
    by (metis a b local.order.antisym local.test_restrictr)
  finally show "(p \<cdot> x)\<^sup>\<dagger> \<cdot> p \<le> p \<cdot> (p \<cdot> x + !p \<cdot> y)\<^sup>\<dagger>"
    by (simp add: a local.dagger_iso local.test_mult_isol)
qed

lemma test_preserve2: "test p \<Longrightarrow> p \<cdot> x \<cdot> p = p \<cdot> x \<Longrightarrow> p \<cdot> (p \<cdot> x + !p \<cdot> y)\<^sup>\<dagger> \<le> x\<^sup>\<dagger>"
  by (metis (no_types) local.eq_refl local.test_restrictl test_preserve test_preserve1)

end

end
