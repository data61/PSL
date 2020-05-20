(* Title:      Demonic refinement algebra
   Author:     Alasdair Armstrong, Victor B. F. Gomes, Georg Struth
   Maintainer: Georg Struth <g.struth at sheffield.ac.uk>
*)

section \<open>Demonic Refinement Algebra with Tests\<close>

theory DRAT
  imports KAT Kleene_Algebra.DRA
begin

text \<open>
  In this section, we define demonic refinement algebras with tests and prove the most important theorems from
  the literature. In this context, tests are also known as guards.
\<close>

class drat = dra + test_semiring_zerol
begin

subclass kat_zerol ..

text \<open>
  An assertion is a mapping from a guard to a subset similar to tests, but it aborts if the predicate does
  not hold.
\<close>

definition assertion :: "'a \<Rightarrow> 'a" ("_\<^sup>o" [101] 100) where
  "test p \<Longrightarrow> p\<^sup>o = !p\<cdot>\<top> + 1"

lemma asg: "\<lbrakk>test p; test q\<rbrakk> \<Longrightarrow> q \<le> 1 \<and> 1 \<le> p\<^sup>o"
  by (simp add: assertion_def local.test_subid)

lemma assertion_isol: "test p \<Longrightarrow> y \<le> p\<^sup>o\<cdot>x \<longleftrightarrow> p\<cdot>y \<le> x"
proof
  assume assms: "test p" "y \<le> p\<^sup>o\<cdot>x"
  hence "p\<cdot>y \<le> p\<cdot>!p\<cdot>\<top>\<cdot>x + p\<cdot>x"
    by (metis add_commute assertion_def local.distrib_left local.iteration_prod_unfold local.iteration_unfoldl_distr local.mult_isol local.top_mult_annil mult_assoc)
  also have "... \<le> x"
    by (simp add: assms(1) local.test_restrictl)
  finally show "p\<cdot>y \<le> x"
    by metis
next
  assume assms: "test p" "p\<cdot>y \<le> x"
  hence "p\<^sup>o\<cdot>p\<cdot>y = !p\<cdot>\<top>\<cdot>p\<cdot>y + p\<cdot>y"
    by (metis assertion_def distrib_right' mult_1_left mult.assoc)
  also have "... = !p\<cdot>\<top> + p\<cdot>y"
    by (metis mult.assoc top_mult_annil)
  moreover have "p\<^sup>o\<cdot>p\<cdot>y \<le> p\<^sup>o\<cdot>x"
    by (metis assms(2) mult.assoc mult_isol)
  moreover have "!p\<cdot>y + p\<cdot>y \<le> !p\<cdot>\<top> + p\<cdot>y"
    using local.add_iso local.top_elim by blast
  ultimately show "y \<le> p\<^sup>o\<cdot>x"    
    by (metis add.commute assms(1) distrib_right' mult_1_left order_trans test_add_comp)
qed

lemma assertion_isor: "test p \<Longrightarrow> y \<le> x\<cdot>p \<longleftrightarrow> y\<cdot>p\<^sup>o \<le> x"
proof
  assume assms: "test p" "y \<le> x\<cdot>p"
  hence "y\<cdot>p\<^sup>o \<le> x\<cdot>p\<cdot>!p\<cdot>\<top> + x\<cdot>p"
    by (metis mult_isor assertion_def assms(1) distrib_left mult_1_right mult.assoc)
  also have "... \<le> x"
    by (metis assms(1) local.iteration_idep local.join.sup.absorb_iff1 local.join.sup_commute local.join.sup_ge2 local.mult_1_right local.mult_isol_var local.mult_isor local.mult_onel local.test_add_comp local.test_comp_mult2 mult_assoc)
  finally show "y\<cdot>p\<^sup>o \<le> x"
    by metis
next
  assume assms: "test p" "y\<cdot>p\<^sup>o \<le> x"
  have "y \<le> y\<cdot>(!p\<cdot>\<top> + p)"
    by (metis join.sup_mono mult_isol order_refl order_refl top_elim add.commute assms(1) mult_1_right test_add_comp)
  also have "... = y\<cdot>p\<^sup>o\<cdot>p"
    by (metis assertion_def assms(1) distrib_right' mult_1_left mult.assoc top_mult_annil)
  finally show "y \<le> x\<cdot>p"
    by (metis assms(2) mult_isor order_trans)
qed

lemma assertion_iso: "\<lbrakk>test p; test q\<rbrakk> \<Longrightarrow> x\<cdot>q\<^sup>o \<le> p\<^sup>o\<cdot>x \<longleftrightarrow> p\<cdot>x \<le> x\<cdot>q"
  by (metis assertion_isol assertion_isor mult.assoc)

lemma total_correctness: "\<lbrakk>test p; test q\<rbrakk> \<Longrightarrow> p\<cdot>x\<cdot>!q = 0 \<longleftrightarrow> x\<cdot>!q \<le> !p\<cdot>\<top>"
  apply standard
  apply (metis local.test_eq4 local.top_elim mult_assoc)
  by (metis annil antisym test_comp_mult2 join.bot_least mult_assoc mult_isol)

lemma test_iteration_sim: "\<lbrakk>test p; p\<cdot>x \<le> x\<cdot>p\<rbrakk> \<Longrightarrow> p\<cdot>x\<^sup>\<infinity> \<le> x\<^sup>\<infinity>\<cdot>p"
  by (metis iteration_sim)

lemma test_iteration_annir: "test p \<Longrightarrow> !p\<cdot>(p\<cdot>x)\<^sup>\<infinity> = !p"
  by (metis annil test_comp_mult1 iteration_idep mult.assoc)

text \<open>Next we give an example of a program transformation from von Wright~\cite{Wright02}.\<close>

lemma loop_refinement: "\<lbrakk>test p; test q\<rbrakk> \<Longrightarrow> (p\<cdot>x)\<^sup>\<infinity>\<cdot>!p \<le> (p\<cdot>q\<cdot>x)\<^sup>\<infinity>\<cdot>!(p\<cdot>q)\<cdot>(p\<cdot>x)\<^sup>\<infinity>\<cdot>!p"
proof -
  assume assms: "test p" "test q"
  hence "(p\<cdot>x)\<^sup>\<infinity>\<cdot>!p = ((p\<cdot>q) + !(p\<cdot>q))\<cdot>(p\<cdot>x)\<^sup>\<infinity>\<cdot>!p"
    by (simp add: local.test_mult_closed)
  also have "... = (p\<cdot>q)\<cdot>(p\<cdot>x)\<^sup>\<infinity>\<cdot>!p + !(p\<cdot>q)\<cdot>(p\<cdot>x)\<^sup>\<infinity>\<cdot>!p"
    by (metis distrib_right')
  also have "... = (p\<cdot>q)\<cdot>!p + (p\<cdot>q)\<cdot>(p\<cdot>x)\<cdot>(p\<cdot>x)\<^sup>\<infinity>\<cdot>!p + !(p\<cdot>q)\<cdot>(p\<cdot>x)\<^sup>\<infinity>\<cdot>!p"
    by (metis iteration_unfoldr_distr mult.assoc iteration_unfold_eq distrib_left mult.assoc)
  also have "... = (p\<cdot>q)\<cdot>(p\<cdot>x)\<cdot>(p\<cdot>x)\<^sup>\<infinity>\<cdot>!p + !(p\<cdot>q)\<cdot>(p\<cdot>x)\<^sup>\<infinity>\<cdot>!p"
    by (metis assms less_eq_def test_preserve2 join.bot_least)
  finally have "(p\<cdot>x)\<^sup>\<infinity>\<cdot>!p \<le> p\<cdot>q\<cdot>x\<cdot>(p\<cdot>x)\<^sup>\<infinity>\<cdot>!p + !(p\<cdot>q)\<cdot>(p\<cdot>x)\<^sup>\<infinity>\<cdot>!p"
    by (metis assms(1) assms(2) local.eq_iff local.test_mult_comm_var local.test_preserve mult_assoc)
  thus ?thesis
    by (metis coinduction add.commute mult.assoc)
qed

text \<open>Finally, we prove different versions of Back's atomicity refinement theorem for action systems.\<close>

lemma atom_step1: "r\<cdot>b \<le> b\<cdot>r \<Longrightarrow> (a + b + r)\<^sup>\<infinity> = b\<^sup>\<infinity>\<cdot>r\<^sup>\<infinity>\<cdot>(a\<cdot>b\<^sup>\<infinity>\<cdot>r\<^sup>\<infinity>)\<^sup>\<infinity>"
  apply (subgoal_tac "(a + b + r)\<^sup>\<infinity> = (b + r)\<^sup>\<infinity>\<cdot>(a\<cdot>(b + r)\<^sup>\<infinity>)\<^sup>\<infinity>")
  apply (metis iteration_sep mult.assoc)
  by (metis add_assoc' add.commute iteration_denest)

 
lemma atom_step2: 
  assumes "s = s\<cdot>q" "q\<cdot>b = 0" "r\<cdot>q \<le> q\<cdot>r" "q\<cdot>l \<le> l\<cdot>q" "r\<^sup>\<infinity> = r\<^sup>\<star>" "test q"
  shows "s\<cdot>l\<^sup>\<infinity>\<cdot>b\<^sup>\<infinity>\<cdot>r\<^sup>\<infinity>\<cdot>q\<cdot>(a\<cdot>b\<^sup>\<infinity>\<cdot>r\<^sup>\<infinity>\<cdot>q)\<^sup>\<infinity> \<le> s\<cdot>l\<^sup>\<infinity>\<cdot>r\<^sup>\<infinity>\<cdot>(a\<cdot>b\<^sup>\<infinity>\<cdot>q\<cdot>r\<^sup>\<infinity>)\<^sup>\<infinity>"
proof -
  have "s\<cdot>l\<^sup>\<infinity>\<cdot>b\<^sup>\<infinity>\<cdot>r\<^sup>\<infinity>\<cdot>q\<cdot>(a\<cdot>b\<^sup>\<infinity>\<cdot>r\<^sup>\<infinity>\<cdot>q)\<^sup>\<infinity> \<le> s\<cdot>l\<^sup>\<infinity>\<cdot>b\<^sup>\<infinity>\<cdot>r\<^sup>\<infinity>\<cdot>q\<cdot>(a\<cdot>b\<^sup>\<infinity>\<cdot>q\<cdot>r\<^sup>\<infinity>)\<^sup>\<infinity>"
    by (metis assms(3) assms(5) star_sim1 mult.assoc mult_isol iteration_iso)
  also have "... \<le> s\<cdot>q\<cdot>l\<^sup>\<infinity>\<cdot>b\<^sup>\<infinity>\<cdot>r\<^sup>\<infinity>\<cdot>(a\<cdot>b\<^sup>\<infinity>\<cdot>q\<cdot>r\<^sup>\<infinity>)\<^sup>\<infinity>"
    using assms(1) assms(6) local.mult_isor local.test_restrictr by auto
  also have "... \<le> s\<cdot>l\<^sup>\<infinity>\<cdot>q\<cdot>b\<^sup>\<infinity>\<cdot>r\<^sup>\<infinity>\<cdot>(a\<cdot>b\<^sup>\<infinity>\<cdot>q\<cdot>r\<^sup>\<infinity>)\<^sup>\<infinity>"
    by (metis assms(4) iteration_sim mult.assoc mult_double_iso mult_double_iso)
  also have "... \<le> s\<cdot>l\<^sup>\<infinity>\<cdot>r\<^sup>\<infinity>\<cdot>q\<cdot>r\<^sup>\<infinity>\<cdot>(a\<cdot>b\<^sup>\<infinity>\<cdot>q\<cdot>r\<^sup>\<infinity>)\<^sup>\<infinity>" 
    by (metis assms(2) join.bot_least iteration_sim mult.assoc mult_double_iso)
  also have "... \<le> s\<cdot>l\<^sup>\<infinity>\<cdot>r\<^sup>\<infinity>\<cdot>(a\<cdot>b\<^sup>\<infinity>\<cdot>q\<cdot>r\<^sup>\<infinity>)\<^sup>\<infinity>"
    by (metis assms(6) mult.assoc mult_isol test_restrictl iteration_idem mult.assoc)
  finally show "s\<cdot>l\<^sup>\<infinity>\<cdot>b\<^sup>\<infinity>\<cdot>r\<^sup>\<infinity>\<cdot>q\<cdot>(a\<cdot>b\<^sup>\<infinity>\<cdot>r\<^sup>\<infinity>\<cdot>q)\<^sup>\<infinity> \<le> s\<cdot>l\<^sup>\<infinity>\<cdot>r\<^sup>\<infinity>\<cdot>(a\<cdot>b\<^sup>\<infinity>\<cdot>q\<cdot>r\<^sup>\<infinity>)\<^sup>\<infinity>"
    by metis
qed

lemma atom_step3: 
  assumes "r\<cdot>l \<le> l\<cdot>r" "a\<cdot>l \<le> l\<cdot>a" "b\<cdot>l \<le> l\<cdot>b" "q\<cdot>l \<le> l\<cdot>q" "b\<^sup>\<infinity> = b\<^sup>\<star>"
  shows "l\<^sup>\<infinity>\<cdot>r\<^sup>\<infinity>\<cdot>(a\<cdot>b\<^sup>\<infinity>\<cdot>q\<cdot>r\<^sup>\<infinity>)\<^sup>\<infinity> = (a\<cdot>b\<^sup>\<infinity>\<cdot>q + l + r)\<^sup>\<infinity>"
proof -
  have "(a\<cdot>b\<^sup>\<infinity>\<cdot>q + r)\<cdot>l \<le> a\<cdot>b\<^sup>\<infinity>\<cdot>l\<cdot>q + l\<cdot>r"
    by (metis distrib_right join.sup_mono assms(1,4) mult.assoc mult_isol)
  also have "... \<le> a\<cdot>l\<cdot>b\<^sup>\<infinity>\<cdot>q + l\<cdot>r"
    by (metis assms(3) assms(5) star_sim1 add_iso mult.assoc mult_double_iso)
  also have "... \<le> l\<cdot>(a\<cdot>b\<^sup>\<infinity>\<cdot>q + r)"
    by (metis add_iso assms(2) mult_isor distrib_left mult.assoc)
  finally have "(a\<cdot>b\<^sup>\<infinity>\<cdot>q + r)\<cdot>l \<le> l\<cdot>(a\<cdot>b\<^sup>\<infinity>\<cdot>q + r)"
    by metis
  moreover have "l\<^sup>\<infinity>\<cdot>r\<^sup>\<infinity>\<cdot>(a\<cdot>b\<^sup>\<infinity>\<cdot>q\<cdot>r\<^sup>\<infinity>)\<^sup>\<infinity> = l\<^sup>\<infinity>\<cdot>(a\<cdot>b\<^sup>\<infinity>\<cdot>q + r)\<^sup>\<infinity>"
    by (metis add.commute mult.assoc iteration_denest)
  ultimately show ?thesis
    by (metis add.commute add.left_commute iteration_sep)
qed

text \<open>
  This is Back's atomicity refinement theorem, as specified by von Wright~\cite {Wright02}.
\<close>

theorem atom_ref_back: 
  assumes "s = s\<cdot>q" "a = q\<cdot>a" "q\<cdot>b = 0"
          "r\<cdot>b \<le> b\<cdot>r" "r\<cdot>l \<le> l\<cdot>r" "r\<cdot>q \<le> q\<cdot>r"
          "a\<cdot>l \<le> l\<cdot>a" "b\<cdot>l \<le> l\<cdot>b" "q\<cdot>l \<le> l\<cdot>q"
          "r\<^sup>\<infinity> = r\<^sup>\<star>" "b\<^sup>\<infinity> = b\<^sup>\<star>" "test q"
  shows "s\<cdot>(a + b + r + l)\<^sup>\<infinity>\<cdot>q \<le> s\<cdot>(a\<cdot>b\<^sup>\<infinity>\<cdot>q + r + l)\<^sup>\<infinity>"
proof -
  have "(a + b + r)\<cdot>l \<le> l\<cdot>(a + b + r)"
    by (metis join.sup_mono distrib_right' assms(5) assms(7) assms(8) distrib_left)
  hence "s\<cdot>(l + a + b + r)\<^sup>\<infinity>\<cdot>q = s\<cdot>l\<^sup>\<infinity>\<cdot>(a + b + r)\<^sup>\<infinity>\<cdot>q"
    by (metis add.commute add.left_commute mult.assoc iteration_sep)
  also have "... \<le> s\<cdot>l\<^sup>\<infinity>\<cdot>b\<^sup>\<infinity>\<cdot>r\<^sup>\<infinity>\<cdot>q\<cdot>(a\<cdot>b\<^sup>\<infinity>\<cdot>r\<^sup>\<infinity>\<cdot>q)\<^sup>\<infinity>"
    by (metis assms(2,4,10,11) atom_step1 iteration_slide eq_refl mult.assoc)
  also have "... \<le> s\<cdot>l\<^sup>\<infinity>\<cdot>r\<^sup>\<infinity>\<cdot>(a\<cdot>b\<^sup>\<infinity>\<cdot>q\<cdot>r\<^sup>\<infinity>)\<^sup>\<infinity>" 
    by (metis assms(1) assms(10) assms(12) assms(3) assms(6) assms(9) atom_step2)
  also have "... \<le> s\<cdot>(a\<cdot>b\<^sup>\<infinity>\<cdot>q + l + r)\<^sup>\<infinity>"
    by (metis assms(11) assms(5) assms(7) assms(8) assms(9) atom_step3 eq_refl mult.assoc)
  finally show ?thesis
    by (metis add.commute add.left_commute)
qed

text \<open>
  This variant is due to H\"ofner, Struth and Sutcliffe~\cite{HofnerSS09}.
\<close>

theorem atom_ref_back_struth: 
  assumes "s \<le> s\<cdot>q" "a \<le> q\<cdot>a" "q\<cdot>b = 0"
          "r\<cdot>b \<le> b\<cdot>r" "r\<cdot>q \<le> q\<cdot>r"
          "(a + r + b)\<cdot>l \<le> l\<cdot>(a + r + b)" "q\<cdot>l \<le> l\<cdot>q"
          "r\<^sup>\<infinity> = r\<^sup>\<star>" "q \<le> 1"
  shows "s\<cdot>(a + b + r + l)\<^sup>\<infinity>\<cdot>q \<le> s\<cdot>(a\<cdot>b\<^sup>\<infinity>\<cdot>q + r + l)\<^sup>\<infinity>"
proof -
  have "s\<cdot>(a + b + r + l)\<^sup>\<infinity>\<cdot>q = s\<cdot>l\<^sup>\<infinity>\<cdot>(a + b + r)\<^sup>\<infinity>\<cdot>q"
    by (metis add.commute add.left_commute assms(6) iteration_sep mult.assoc)
  also have "... = s\<cdot>l\<^sup>\<infinity>\<cdot>(b + r)\<^sup>\<infinity>\<cdot>(a\<cdot>(b + r)\<^sup>\<infinity>)\<^sup>\<infinity>\<cdot>q"
    by (metis add_assoc' add.commute iteration_denest add.commute mult.assoc)
  also have "... = s\<cdot>l\<^sup>\<infinity>\<cdot>b\<^sup>\<infinity>\<cdot>r\<^sup>\<infinity>\<cdot>(a\<cdot>b\<^sup>\<infinity>\<cdot>r\<^sup>\<infinity>)\<^sup>\<infinity>\<cdot>q"
    by (metis assms(4) iteration_sep mult.assoc)
  also have "... \<le> s\<cdot>l\<^sup>\<infinity>\<cdot>b\<^sup>\<infinity>\<cdot>r\<^sup>\<infinity>\<cdot>(q\<cdot>a\<cdot>b\<^sup>\<infinity>\<cdot>r\<^sup>\<infinity>)\<^sup>\<infinity>\<cdot>q"
    by (metis assms(2) iteration_iso mult_isol_var eq_refl order_refl)
  also have "... = s\<cdot>l\<^sup>\<infinity>\<cdot>b\<^sup>\<infinity>\<cdot>r\<^sup>\<infinity>\<cdot>q\<cdot>(a\<cdot>b\<^sup>\<infinity>\<cdot>r\<^sup>\<infinity>\<cdot>q)\<^sup>\<infinity>"
    by (metis iteration_slide mult.assoc)
  also have "... \<le> s\<cdot>q\<cdot>l\<^sup>\<infinity>\<cdot>b\<^sup>\<infinity>\<cdot>r\<^sup>\<infinity>\<cdot>q\<cdot>(a\<cdot>b\<^sup>\<infinity>\<cdot>r\<^sup>\<infinity>\<cdot>q)\<^sup>\<infinity>"
    by (metis assms(1) mult_isor)
  also have "... \<le> s\<cdot>l\<^sup>\<infinity>\<cdot>q\<cdot>b\<^sup>\<infinity>\<cdot>r\<^sup>\<infinity>\<cdot>q\<cdot>(a\<cdot>b\<^sup>\<infinity>\<cdot>r\<^sup>\<infinity>\<cdot>q)\<^sup>\<infinity>"
    by (metis assms(7) iteration_sim mult.assoc mult_double_iso)
  also have "... \<le> s\<cdot>l\<^sup>\<infinity>\<cdot>q\<cdot>r\<^sup>\<infinity>\<cdot>q\<cdot>(a\<cdot>b\<^sup>\<infinity>\<cdot>r\<^sup>\<infinity>\<cdot>q)\<^sup>\<infinity>"
    by (metis assms(3) iteration_idep mult.assoc order_refl)
  also have "... \<le> s\<cdot>l\<^sup>\<infinity>\<cdot>q\<cdot>r\<^sup>\<infinity>\<cdot>q\<cdot>(a\<cdot>b\<^sup>\<infinity>\<cdot>r\<^sup>\<star>\<cdot>q)\<^sup>\<infinity>"
    by (metis assms(8) eq_refl)
  also have "... \<le> s\<cdot>l\<^sup>\<infinity>\<cdot>q\<cdot>r\<^sup>\<infinity>\<cdot>q\<cdot>(a\<cdot>b\<^sup>\<infinity>\<cdot>q\<cdot>r\<^sup>\<star>)\<^sup>\<infinity>"
    by (metis assms(5) iteration_iso mult.assoc mult_isol star_sim1)
  also have "... = s\<cdot>l\<^sup>\<infinity>\<cdot>q\<cdot>r\<^sup>\<infinity>\<cdot>q\<cdot>(a\<cdot>b\<^sup>\<infinity>\<cdot>q\<cdot>r\<^sup>\<infinity>)\<^sup>\<infinity>"
    by (metis assms(8))
  also have "... \<le> s\<cdot>l\<^sup>\<infinity>\<cdot>r\<^sup>\<infinity>\<cdot>q\<cdot>(a\<cdot>b\<^sup>\<infinity>\<cdot>q\<cdot>r\<^sup>\<infinity>)\<^sup>\<infinity>"
    by (metis assms(9) mult_1_right mult_double_iso mult_isor)
  also have "... \<le> s\<cdot>l\<^sup>\<infinity>\<cdot>r\<^sup>\<infinity>\<cdot>(a\<cdot>b\<^sup>\<infinity>\<cdot>q\<cdot>r\<^sup>\<infinity>)\<^sup>\<infinity>"
    by (metis assms(9) mult_1_right mult_double_iso)
  also have "... = s\<cdot>l\<^sup>\<infinity>\<cdot>(a\<cdot>b\<^sup>\<infinity>\<cdot>q + r)\<^sup>\<infinity>"
    by (metis add.commute mult.assoc iteration_denest)
  also have "... \<le> s\<cdot>(a\<cdot>b\<^sup>\<infinity>\<cdot>q + r + l)\<^sup>\<infinity>"
    by (metis add.commute iteration_subdenest mult.assoc mult_isol)
  finally show ?thesis .
qed
    

text \<open>Finally, we prove Cohen's~\cite{Cohen00} variation of the atomicity refinement theorem.\<close>

lemma atom_ref_cohen: 
  assumes "r\<cdot>p\<cdot>y \<le> y\<cdot>r" "y\<cdot>p\<cdot>l \<le> l\<cdot>y" "r\<cdot>p\<cdot>l \<le> l\<cdot>r"
          "p\<cdot>r\<cdot>!p = 0" "p\<cdot>l\<cdot>!p = 0" "!p\<cdot>l\<cdot>p = 0"
          "y\<cdot>0 = 0" "r\<cdot>0 = 0" "test p"
  shows "(y + r + l)\<^sup>\<infinity> = (p\<cdot>l)\<^sup>\<infinity>\<cdot>(y + !p\<cdot>l + r\<cdot>!p)\<^sup>\<infinity>\<cdot>(r\<cdot>p)\<^sup>\<infinity>"
proof -    
  have "(y + r)\<cdot>p\<cdot>l \<le> l\<cdot>y + l\<cdot>r"
    by (metis distrib_right' join.sup_mono assms(2) assms(3))
  hence stepA: "(y + r)\<cdot>p\<cdot>l \<le> (p\<cdot>l + !p\<cdot>l)\<cdot>(y + r)\<^sup>\<star>"
    by (metis assms(9) distrib_left distrib_right' mult_1_left mult_isol order_trans star_ext test_add_comp)
  have subStepB: "(!p\<cdot>l + y + p\<cdot>r + !p\<cdot>r)\<^sup>\<infinity> = (!p\<cdot>l + y + r\<cdot>p + r\<cdot>!p)\<^sup>\<infinity>"
    by (metis add_assoc' annil assms(8) assms(9) distrib_left distrib_right' star_slide star_subid test_add_comp join.bot_least)
  have "r\<cdot>p\<cdot>(y + r\<cdot>!p + !p\<cdot>l) \<le> y\<cdot>(r\<cdot>p + r\<cdot>!p)"
    by (metis assms(1,4,9) distrib_left add_0_left add.commute annil mult.assoc test_comp_mult2 distrib_left mult_oner test_add_comp)
  also have "... \<le> (y + r\<cdot>!p + !p\<cdot>l)\<cdot>(r\<cdot>p + (y + r\<cdot>!p + !p\<cdot>l))"
    by (meson local.eq_refl local.join.sup_ge1 local.join.sup_ge2 local.join.sup_mono local.mult_isol_var local.order_trans)
  finally have "r\<cdot>p\<cdot>(y + r\<cdot>!p + !p\<cdot>l) \<le> (y + r\<cdot>!p + !p\<cdot>l)\<cdot>(y + r\<cdot>!p + !p\<cdot>l + r\<cdot>p)" 
    by (metis add.commute)
  hence stepB: "(!p\<cdot>l + y + p\<cdot>r + !p\<cdot>r)\<^sup>\<infinity> = (y + !p\<cdot>l + r\<cdot>!p)\<^sup>\<infinity>\<cdot>(r\<cdot>p)\<^sup>\<infinity>" 
    by (metis subStepB iteration_sep3[of "r\<cdot>p" "y + r\<cdot>!p + !p\<cdot>l"]  add_assoc' add.commute)
  have "(y + r + l)\<^sup>\<infinity> = (p\<cdot>l + !p\<cdot>l + y + r)\<^sup>\<infinity>"
    by (metis add_comm add.left_commute assms(9) distrib_right' mult_onel test_add_comp)
  also have "... = (p\<cdot>l)\<^sup>\<infinity>\<cdot>(!p\<cdot>l + y + r)\<^sup>\<infinity>" using stepA
    by (metis assms(6-8) annil add.assoc add_0_left distrib_right' add.commute mult.assoc iteration_sep4[of "y+r" "!p\<cdot>l" "p\<cdot>l"])
  also have "... = (p\<cdot>l)\<^sup>\<infinity>\<cdot>(!p\<cdot>l + y + p\<cdot>r + !p\<cdot>r)\<^sup>\<infinity>"
    by (metis add.commute assms(9) combine_common_factor mult_1_left test_add_comp)
  finally show ?thesis using stepB
    by (metis mult.assoc)
qed
end

end
