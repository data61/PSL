(*
    Title:      Descartes Roots Test
    Author:     Wenda Li <wl302@cam.ac.uk / liwenda1990@hotmail.com>
*)

section \<open>Descartes Roots Test\<close>

theory Descartes_Roots_Test imports Budan_Fourier
begin

text \<open>The Descartes roots test is a consequence of Descartes' rule of signs:
  through counting sign variations on coefficients of a base-transformed (i.e. Taylor shifted) 
  polynomial, it can over-approximate the number of real roots (counting multiplicity) 
  within an interval. Its ability is similar to the Budan-Fourier theorem, but is far more 
  efficient in practice. Therefore, this test is widely used in modern root isolation procedures. 

  More information can be found in the wiki page about Vincent's theorem:
    @{url "https://en.wikipedia.org/wiki/Vincent%27s_theorem"}
  and Collins and Akritas's classic paper of root isolation:
    Collins, G.E., Akritas, A.G.: Polynomial real root isolation using Descarte's rule of signs. SYMSACC. 272--275 (1976).
  A more modern treatment is available from a recent implementation of isolating real roots:
    Kobel, A., Rouillier, F., Sagraloff, M.: Computing Real Roots of Real Polynomials ... and now For Real! 
    Proceedings of ISSAC '16, New York, New York, USA (2016).
\<close>

lemma bij_betw_pos_interval:
  fixes a b::real
  assumes "a<b"
  shows "bij_betw (\<lambda>x. (a+b * x) / (1+x)) {x. x>0} {x. a<x \<and> x<b}"
proof (rule bij_betw_imageI)
  show "inj_on (\<lambda>x. (a + b * x) / (1 + x)) {x. 0 < x}"
    unfolding inj_on_def 
    apply (auto simp add:field_simps)
    using assms crossproduct_noteq by fastforce
  have "x \<in> (\<lambda>x. (a + b * x) / (1 + x)) ` {x. 0 < x}" when "a < x" "x < b" for x 
  proof (rule rev_image_eqI[of "(x-a)/(b-x)"])
    define bx where "bx=b-x"
    have x:"x=b-bx" unfolding bx_def by auto
    have "bx\<noteq>0" "b>a" unfolding bx_def using that by auto
    then show " x = (a + b * ((x - a) / (b - x))) / (1 + (x - a) / (b - x))"
      apply (fold bx_def,unfold x)
      by (auto simp add:field_simps)
    show "(x - a) / (b - x) \<in> {x. 0 < x}" using that by auto
  qed 
  then show "(\<lambda>x. (a + b * x) / (1 + x)) ` {x. 0 < x} = {x. a < x \<and> x < b}"
    using assms by (auto simp add:divide_simps algebra_simps)
qed

lemma proots_sphere_pos_interval:
  fixes a b::real
  defines "q1\<equiv>[:a,b:]" and "q2\<equiv>[:1,1:]"
  assumes "p\<noteq>0" "a<b"
  shows "proots_count p {x. a < x \<and> x < b} = proots_count (fcompose p q1 q2) {x. 0 < x}"
  apply (rule proots_fcompose_bij_eq[OF _ \<open>p\<noteq>0\<close>])
  unfolding q1_def q2_def using bij_betw_pos_interval[OF \<open>a<b\<close>] \<open>a<b\<close>
  by (auto simp add:algebra_simps infinite_UNIV_char_0)

definition descartes_roots_test::"real \<Rightarrow> real \<Rightarrow> real poly \<Rightarrow> nat" where
  "descartes_roots_test a b p = nat (changes (coeffs (fcompose p [:a,b:] [:1,1:])))"
  
theorem descartes_roots_test:
  fixes p::"real poly"
  assumes "p\<noteq>0" "a<b"
  shows "proots_count p {x. a < x \<and> x <b} \<le> descartes_roots_test a b p  \<and> 
          even (descartes_roots_test a b p - proots_count p {x. a < x \<and> x < b})"
proof -
  define q where "q=fcompose p [:a,b:] [:1,1:]"
  have "q\<noteq>0"
    unfolding q_def
    apply (rule fcompose_nzero[OF \<open>p\<noteq>0\<close>])
    using \<open>a<b\<close> infinite_UNIV_char_0 by auto
  have "proots_count p {x. a < x \<and> x <b} = proots_count q {x. 0 < x}"
    using proots_sphere_pos_interval[OF \<open>p\<noteq>0\<close> \<open>a<b\<close>,folded q_def] .
  moreover have "int (proots_count q {x. 0 < x}) \<le> changes (coeffs q) \<and>
          even (changes (coeffs q) - int (proots_count q {x. 0 < x}))"
    by (rule descartes_sign[OF \<open>q\<noteq>0\<close>])
  then have "proots_count q {x. 0 < x} \<le> nat (changes (coeffs q)) \<and>
          even (nat (changes (coeffs q)) - proots_count q {x. 0 < x})"
    using even_nat_iff by auto
  ultimately show ?thesis 
    unfolding descartes_roots_test_def
    apply (fold q_def)
    by auto
qed

text \<open>The roots test @{term descartes_roots_test} is exact if its result is 0 or 1.\<close>

corollary descartes_roots_test_zero:
  fixes p::"real poly"
  assumes "p\<noteq>0" "a<b" "descartes_roots_test a b p = 0"
  shows "\<forall>x. a<x \<and> x<b \<longrightarrow> poly p x\<noteq>0"
proof -
  have "proots_count p {x. a < x \<and> x <b} = 0"
    using descartes_roots_test[OF assms(1,2)] assms(3) by auto
  from proots_count_0_imp_empty[OF this \<open>p\<noteq>0\<close>] 
  show ?thesis by auto
qed

corollary descartes_roots_test_one:
  fixes p::"real poly"
  assumes "p\<noteq>0" "a<b" "descartes_roots_test a b p = 1"
  shows "proots_count p {x. a < x \<and> x <b} = 1"
  using descartes_roots_test[OF \<open>p\<noteq>0\<close> \<open>a<b\<close>] \<open>descartes_roots_test a b p = 1\<close> 
  by (metis dvd_diffD even_zero le_neq_implies_less less_one odd_one)


text \<open>Similar to the Budan-Fourier theorem, the Descartes roots test result is exact when all roots 
      are real.\<close>
corollary descartes_roots_test_real:
  fixes p::"real poly"
  assumes "p\<noteq>0" "a<b" 
  assumes "all_roots_real p"
  shows "proots_count p {x. a < x \<and> x <b} = descartes_roots_test a b p"
proof -
  define q where "q=fcompose p [:a,b:] [:1,1:]"
  have "q\<noteq>0"
    unfolding q_def
    apply (rule fcompose_nzero[OF \<open>p\<noteq>0\<close>])
    using \<open>a<b\<close> infinite_UNIV_char_0 by auto
  have "proots_count p {x. a < x \<and> x <b} = proots_count q {x. 0 < x}"
    using proots_sphere_pos_interval[OF \<open>p\<noteq>0\<close> \<open>a<b\<close>,folded q_def] .
  moreover have "int (proots_count q {x. 0 < x}) = changes (coeffs q)"
    apply (rule descartes_sign_real[OF \<open>q\<noteq>0\<close>])
    unfolding q_def by (rule all_real_roots_mobius[OF \<open>all_roots_real p\<close> \<open>a<b\<close>])
  then have "proots_count q {x. 0 < x} = nat (changes (coeffs q))"
    by simp
  ultimately show ?thesis unfolding descartes_roots_test_def 
    apply (fold q_def)
    by auto
qed

end