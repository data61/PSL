(* Title:      Kleene algebra with tests
   Author:     Alasdair Armstrong, Victor B. F. Gomes, Georg Struth
   Maintainer: Georg Struth <g.struth at sheffield.ac.uk>
*)

section \<open>Transformation Theorem for while Loops\<close>

theory FolkTheorem
  imports Conway_Tests KAT DRAT
begin

text \<open>
  We prove Kozen's transformation theorem for while loops \cite{Kozen97} in a weak setting that unifies
  previous proofs in Kleene algebra with tests, demonic refinement algebras and a variant of probabilistic
  Kleene algebra.
\<close>

context test_pre_conway
begin

abbreviation pres :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "pres x y \<equiv> y \<cdot> x = y \<cdot> x \<cdot> y"

lemma pres_comp: "pres y z \<Longrightarrow> pres x z \<Longrightarrow> pres (x \<cdot> y) z"
  by (metis mult_assoc)

lemma test_pres1: "test p \<Longrightarrow> test q \<Longrightarrow> pres p q"
  by (simp add: local.test_mult_comm_var mult_assoc)

lemma test_pres2: "test p \<Longrightarrow> test q \<Longrightarrow> pres x q \<Longrightarrow> pres (p \<cdot> x) q"
  using pres_comp test_pres1 by blast

lemma cond_helper1:
assumes "test p" and "pres x p" 
shows "p \<cdot> (p \<cdot> x + !p \<cdot> y)\<^sup>\<dagger> \<cdot> (p \<cdot> z + !p \<cdot> w) = p \<cdot> x\<^sup>\<dagger> \<cdot> z"
proof -
  have "p \<cdot> (p \<cdot> z + !p \<cdot> w) = p \<cdot> z"
    by (metis assms(1) local.add_zerol local.annil local.join.sup_commute local.n_left_distrib_var local.test_comp_mult2 local.test_mult_idem_var mult_assoc)
  hence "p \<cdot> (p \<cdot> x + !p \<cdot> y)\<^sup>\<dagger> \<cdot> (p \<cdot> z + !p \<cdot> w) = (p \<cdot> x)\<^sup>\<dagger> \<cdot> p \<cdot> z"
    using assms(1) assms(2) local.test_preserve1 mult_assoc by auto
  thus ?thesis
   using assms(1) assms(2) local.test_preserve mult_assoc by auto
qed

lemma cond_helper2: 
assumes "test p" and "pres y (!p)" 
shows "!p \<cdot> (p \<cdot> x + !p \<cdot> y)\<^sup>\<dagger> \<cdot> (p \<cdot> z + !p \<cdot> w) = !p \<cdot> y\<^sup>\<dagger> \<cdot> w"
proof -
  have "!p \<cdot> (!p \<cdot> y + !(!p) \<cdot> x)\<^sup>\<dagger> \<cdot> (!p \<cdot> w + !(!p) \<cdot> z) = !p \<cdot> y\<^sup>\<dagger> \<cdot> w"
    using assms(1) local.test_comp_closed assms(2) cond_helper1 by blast
  thus ?thesis
    using add_commute assms(1) by auto
qed

lemma cond_distr_var: 
  assumes "test p" and "test q" and "test r"
  shows "(q \<cdot> p + r \<cdot> !p) \<cdot> (p \<cdot> x + !p \<cdot> y) = q \<cdot> p \<cdot> x + r \<cdot> !p \<cdot> y" 
proof -
  have "(q \<cdot> p + r \<cdot> !p) \<cdot> (p \<cdot> x + !p \<cdot> y) = q \<cdot> p \<cdot> p \<cdot> x + q \<cdot> p \<cdot> !p \<cdot> y + r \<cdot> !p \<cdot> p \<cdot> x + r \<cdot> !p \<cdot> !p \<cdot> y"
    using assms(1) assms(2) assms(3) local.distrib_right' local.join.sup_assoc local.n_left_distrib_var local.test_comp_closed mult_assoc by presburger
  also have "... = q \<cdot> p \<cdot> x + q \<cdot> 0 \<cdot> y + r \<cdot> 0 \<cdot> x + r \<cdot> !p  \<cdot> y"
    by (simp add: assms(1) mult_assoc)
  finally show ?thesis
    by (metis assms(2) assms(3) local.add_zerol local.annil local.join.sup_commute local.test_mult_comm_var local.test_zero_var)
qed

lemma cond_distr: 
  assumes "test p" and "test q" and "test r"
  shows "(p \<cdot> q + !p \<cdot> r) \<cdot> (p \<cdot> x + !p \<cdot> y) = p \<cdot> q \<cdot> x + !p \<cdot> r \<cdot> y" 
    using  assms(1) assms(2) assms(3) local.test_mult_comm_var assms(1) assms(2) assms(3) cond_distr_var local.test_mult_comm_var by auto

theorem conditional: 
assumes "test p" and "test q" and "test r1" and "test r2"
and "pres x1 q" and "pres y1 q" and "pres x2 (!q)" and "pres y2 (!q)"
shows "(p \<cdot> q + !p \<cdot> !q) \<cdot> (q \<cdot> x1 + !q \<cdot> x2) \<cdot> ((q \<cdot> r1 + !q \<cdot> r2) \<cdot> (q \<cdot> y1 + !q \<cdot> y2))\<^sup>\<dagger> \<cdot> !(q \<cdot> r1 + !q \<cdot> r2) =     
(p \<cdot> q + !p \<cdot> !q) \<cdot> (p \<cdot> x1 \<cdot> (r1 \<cdot> y1)\<^sup>\<dagger> \<cdot> !r1 + !p \<cdot> x2 \<cdot> (r2 \<cdot> y2)\<^sup>\<dagger> \<cdot> !r2)"
proof -
  have a: "p \<cdot> q \<cdot> x1 \<cdot> q \<cdot> (q \<cdot> r1 \<cdot> y1 + !q \<cdot> r2 \<cdot> y2)\<^sup>\<dagger> \<cdot> (q \<cdot> !r1 + !q \<cdot> !r2) = p \<cdot> q \<cdot> x1 \<cdot> q \<cdot> (r1 \<cdot> y1)\<^sup>\<dagger> \<cdot> !r1"
    by (metis assms(2) assms(3)  assms(6) cond_helper1 mult_assoc test_pres2)
  have b: "!q \<cdot> (q \<cdot> r1 \<cdot> y1 + !q \<cdot> r2 \<cdot> y2)\<^sup>\<dagger> \<cdot> (q \<cdot> !r1 + !q \<cdot> !r2) = !q \<cdot> (r2 \<cdot> y2)\<^sup>\<dagger> \<cdot> !r2"
    by (metis assms(2) assms(4) assms(8) local.test_comp_closed cond_helper2 mult_assoc test_pres2)
  have "(p \<cdot> q + !p \<cdot> !q) \<cdot> (q \<cdot> x1 + !q \<cdot> x2) \<cdot> ((q \<cdot> r1 + !q \<cdot> r2) \<cdot> (q \<cdot> y1 + !q \<cdot> y2))\<^sup>\<dagger> \<cdot> !(q \<cdot> r1 + !q \<cdot> r2) =
        p \<cdot> q \<cdot> x1 \<cdot> q \<cdot> (q \<cdot> r1 \<cdot> y1 + !q \<cdot> r2 \<cdot> y2)\<^sup>\<dagger> \<cdot> (q \<cdot> !r1 + !q \<cdot> !r2) + !p \<cdot> !q \<cdot> x2 \<cdot> !q \<cdot> (q \<cdot> r1 \<cdot> y1 + !q \<cdot> r2 \<cdot> y2)\<^sup>\<dagger> \<cdot> (q \<cdot> !r1 + !q \<cdot> !r2)"
    using assms(1) assms(2) assms(3) assms(4) assms(5) assms(7) cond_distr cond_distr_var local.test_dist_var2 mult_assoc by auto
  also have "... =  p \<cdot> q \<cdot> x1 \<cdot> (r1 \<cdot> y1)\<^sup>\<dagger> \<cdot> !r1 + !p \<cdot> !q \<cdot>  x2 \<cdot> (r2 \<cdot> y2)\<^sup>\<dagger> \<cdot> !r2"
    by (metis a assms(5) assms(7) b mult_assoc)
  finally show ?thesis
    using assms(1) assms(2) cond_distr mult_assoc by auto
qed

theorem nested_loops: 
  assumes "test p" and "test q"
  shows "p \<cdot> x \<cdot> ((p + q) \<cdot> (q \<cdot> y + !q \<cdot> x))\<^sup>\<dagger> \<cdot> !(p + q) + !p = (p \<cdot> x \<cdot> (q \<cdot> y)\<^sup>\<dagger> \<cdot> !q)\<^sup>\<dagger> \<cdot> !p"
proof -
  have "p \<cdot> x \<cdot> ((p + q) \<cdot> (q \<cdot> y + !q \<cdot> x))\<^sup>\<dagger> \<cdot> !(p + q) + !p = p \<cdot> x \<cdot> (q \<cdot> y)\<^sup>\<dagger> \<cdot> (!q \<cdot> p \<cdot> x \<cdot> (q \<cdot> y)\<^sup>\<dagger>)\<^sup>\<dagger> \<cdot> !q \<cdot> !p + !p"
    using assms(1) assms(2) local.dagger_denest2 local.test_distrib mult_assoc test_mult_comm_var by auto
  also have "... =  p \<cdot> x \<cdot> (q \<cdot> y)\<^sup>\<dagger> \<cdot> !q \<cdot> (p \<cdot> x \<cdot> (q \<cdot> y)\<^sup>\<dagger> \<cdot> !q)\<^sup>\<dagger>  \<cdot> !p + !p"
    by (metis local.dagger_slide mult_assoc)
  finally show ?thesis
    using add_commute by force
qed

lemma postcomputation:
  assumes "test p" and "pres y (!p)"
  shows "!p \<cdot> y + p \<cdot> (p \<cdot> x \<cdot> (!p \<cdot> y + p))\<^sup>\<dagger> \<cdot> !p = (p \<cdot> x)\<^sup>\<dagger> \<cdot> !p \<cdot> y"
proof -
  have "p \<cdot> (p \<cdot> x \<cdot> (!p \<cdot> y + p))\<^sup>\<dagger> \<cdot> !p = p \<cdot> (1 + p \<cdot> x \<cdot> ((!p \<cdot> y + p) \<cdot> p \<cdot> x)\<^sup>\<dagger> \<cdot> (!p \<cdot> y + p)) \<cdot> !p"
    by (metis dagger_prod_unfold mult.assoc)
  also have "... = (p + p \<cdot> p \<cdot> x \<cdot> ((!p \<cdot> y + p) \<cdot> p \<cdot> x)\<^sup>\<dagger> \<cdot> (!p \<cdot> y + p)) \<cdot> !p"
    using assms(1) local.mult_oner local.n_left_distrib_var mult_assoc by presburger 
  also have "... = p \<cdot> x \<cdot> (!p \<cdot> y \<cdot> p \<cdot> x + p \<cdot> x)\<^sup>\<dagger> \<cdot> !p \<cdot> y \<cdot> !p"
    by (simp add: assms(1) mult_assoc)
  also have "... = p \<cdot> x \<cdot> (!p \<cdot> y \<cdot> 0 + p \<cdot> x)\<^sup>\<dagger> \<cdot> !p \<cdot> y"
    by (metis assms(1) assms(2) local.annil local.test_comp_mult1 mult_assoc)
  also have "... = p \<cdot> x  \<cdot> (p  \<cdot> x)\<^sup>\<dagger> \<cdot> (!p \<cdot> y \<cdot> 0 \<cdot> (p \<cdot> x)\<^sup>\<dagger>)\<^sup>\<dagger> \<cdot> !p \<cdot> y"
    by (metis mult.assoc add.commute dagger_denest2)
  finally have "p \<cdot> (p \<cdot> x \<cdot> (!p \<cdot> y + p))\<^sup>\<dagger> \<cdot> !p = p \<cdot> x \<cdot> (p \<cdot> x)\<^sup>\<dagger> \<cdot> !p \<cdot> y"
    by (metis local.add_zeror local.annil local.dagger_prod_unfold local.dagger_slide local.mult_oner mult_assoc)
  thus ?thesis
    by (metis dagger_unfoldl_distr mult.assoc)
qed

lemma composition_helper: 
  assumes "test p" and "test q"
  and "pres x p"
  shows "p \<cdot> (q \<cdot> x)\<^sup>\<dagger> \<cdot> !q \<cdot> p = p \<cdot> (q \<cdot> x)\<^sup>\<dagger> \<cdot> !q"
proof (rule antisym)
  show "p \<cdot> (q \<cdot> x)\<^sup>\<dagger> \<cdot> !q \<cdot> p \<le> p \<cdot> (q \<cdot> x)\<^sup>\<dagger> \<cdot> !q"
    by (simp add: assms(1) local.test_restrictr)
next
  have "p \<cdot> q \<cdot> x \<le> q \<cdot> x \<cdot> p"
    by (metis assms(1) assms(2) assms(3) local.test_kat_2 mult_assoc test_pres2)
  hence "p \<cdot> (q \<cdot> x)\<^sup>\<dagger> \<le> (q \<cdot> x)\<^sup>\<dagger> \<cdot> p"
    by (simp add: local.dagger_simr mult_assoc)
  thus "p \<cdot> (q \<cdot> x)\<^sup>\<dagger> \<cdot> !q \<le> p \<cdot> (q \<cdot> x)\<^sup>\<dagger> \<cdot> !q \<cdot> p"
    by (metis assms(1) assms(2) local.eq_iff local.test_comp_closed local.test_kat_2 local.test_mult_comm_var mult_assoc)
qed

theorem composition:
  assumes "test p" and "test q" 
  and "pres y p" and "pres y (!p)"
  shows "(p \<cdot> x)\<^sup>\<dagger> \<cdot> !p \<cdot> (q \<cdot> y)\<^sup>\<dagger> \<cdot> !q = !p \<cdot> (q \<cdot> y)\<^sup>\<dagger> \<cdot> !q + p \<cdot> (p \<cdot> x \<cdot> (!p \<cdot> (q \<cdot> y)\<^sup>\<dagger> \<cdot> !q + p))\<^sup>\<dagger> \<cdot> !p"
    by (metis assms(1) assms(2) assms(4) composition_helper local.test_comp_closed mult_assoc postcomputation)
end

text \<open>
  Kleene algebras with tests form pre-Conway algebras, therefore the transformation theorem is valid for KAT as well.
\<close>

sublocale kat \<subseteq> pre_conway star ..

text \<open>
  Demonic refinement algebras form pre-Conway algebras, therefore the transformation theorem is valid for DRA as well.
\<close>
sublocale drat \<subseteq> pre_conway strong_iteration
  apply standard
  apply (simp add: local.iteration_denest local.iteration_slide)
  apply (metis local.iteration_prod_unfold)
  by (simp add: local.iteration_sim)
 
text \<open>
  We do not currently consider an expansion of probabilistic Kleene algebra.
\<close>

end
