(* Title:      Demonic refinement algebra
   Author:     Alasdair Armstrong, Victor B. F. Gomes, Georg Struth
   Maintainer: Georg Struth <g.struth at sheffield.ac.uk>
               Tjark Weber <tjark.weber at it.uu.se>
*)

section \<open>Demonic Refinement Algebras\<close>

theory DRA
  imports Kleene_Algebra 
begin

text \<open>
  A demonic refinement algebra *DRA)~\cite{vonwright04refinement} is a Kleene algebra without right annihilation plus 
  an operation for possibly infinite iteration.
\<close>
class dra = kleene_algebra_zerol +
  fixes strong_iteration :: "'a \<Rightarrow> 'a" ("_\<^sup>\<infinity>" [101] 100)
  assumes iteration_unfoldl [simp] : "1 + x \<cdot> x\<^sup>\<infinity> = x\<^sup>\<infinity>"
  and coinduction: "y \<le> z + x \<cdot> y \<longrightarrow> y \<le> x\<^sup>\<infinity> \<cdot> z"
  and isolation [simp]: "x\<^sup>\<star> + x\<^sup>\<infinity> \<cdot> 0 = x\<^sup>\<infinity>"
begin

text \<open>$\top$ is an abort statement, defined as an infinite skip. It is the maximal element of any DRA.\<close>

abbreviation top_elem :: "'a" ("\<top>") where "\<top> \<equiv> 1\<^sup>\<infinity>"

text \<open>Simple/basic lemmas about the iteration operator\<close>

lemma iteration_refl: "1 \<le> x\<^sup>\<infinity>"
  using local.iteration_unfoldl local.order_prop by blast

lemma iteration_1l: "x \<cdot> x\<^sup>\<infinity> \<le> x\<^sup>\<infinity>"
  by (metis local.iteration_unfoldl local.join.sup.cobounded2)

lemma top_ref: "x \<le> \<top>"
proof -
  have "x \<le> 1 + 1 \<cdot> x"
    by simp
  thus ?thesis
    using local.coinduction by fastforce
qed

lemma it_ext: "x \<le> x\<^sup>\<infinity>"
proof -
  have "x \<le> x \<cdot> x\<^sup>\<infinity>"
    using iteration_refl local.mult_isol by fastforce
  thus ?thesis
    by (metis (full_types) local.isolation local.join.sup.coboundedI1 local.star_ext)
qed

lemma it_idem [simp]: "(x\<^sup>\<infinity>)\<^sup>\<infinity> = x\<^sup>\<infinity>"
(*nitpick [expect=genuine]*)
oops

lemma top_mult_annil [simp]: "\<top> \<cdot> x = \<top>"
  by (simp add: local.coinduction local.order.antisym top_ref)

lemma top_add_annil [simp]: "\<top> + x = \<top>"
  by (simp add: local.join.sup.absorb1 top_ref)

lemma top_elim: "x \<cdot> y \<le> x \<cdot> \<top>"
  by (simp add: local.mult_isol top_ref)

lemma iteration_unfoldl_distl [simp]: " y + y \<cdot> x \<cdot> x\<^sup>\<infinity> = y \<cdot> x\<^sup>\<infinity>"
  by (metis distrib_left mult.assoc mult_oner iteration_unfoldl)

lemma iteration_unfoldl_distr [simp]: " y + x \<cdot> x\<^sup>\<infinity> \<cdot> y = x\<^sup>\<infinity> \<cdot> y"
  by (metis distrib_right' mult_1_left iteration_unfoldl)

lemma iteration_unfoldl' [simp]: "z \<cdot> y + z \<cdot> x \<cdot> x\<^sup>\<infinity> \<cdot> y = z \<cdot> x\<^sup>\<infinity> \<cdot> y"
  by (metis iteration_unfoldl_distl local.distrib_right)

lemma iteration_idem [simp]: "x\<^sup>\<infinity> \<cdot> x\<^sup>\<infinity> = x\<^sup>\<infinity>"
proof (rule antisym)
  have "x\<^sup>\<infinity> \<cdot> x\<^sup>\<infinity> \<le> 1 + x \<cdot> x\<^sup>\<infinity> \<cdot> x\<^sup>\<infinity>"
    by (metis add_assoc iteration_unfoldl_distr local.eq_refl local.iteration_unfoldl local.subdistl_eq mult_assoc)
  thus "x\<^sup>\<infinity> \<cdot> x\<^sup>\<infinity> \<le> x\<^sup>\<infinity>"
    using local.coinduction mult_assoc by fastforce
  show "x\<^sup>\<infinity> \<le>  x\<^sup>\<infinity> \<cdot> x\<^sup>\<infinity>"
    using local.coinduction by auto
qed

lemma iteration_induct: "x \<cdot> x\<^sup>\<infinity> \<le> x\<^sup>\<infinity> \<cdot> x"
proof -
  have "x + x \<cdot> (x \<cdot> x\<^sup>\<infinity>) = x \<cdot> x\<^sup>\<infinity>"
    by (metis (no_types) local.distrib_left local.iteration_unfoldl local.mult_oner)
  thus ?thesis
    by (simp add: local.coinduction)
qed

lemma iteration_ref_star: "x\<^sup>\<star> \<le> x\<^sup>\<infinity>"
  by (simp add: local.star_inductl_one)

lemma iteration_subdist: "x\<^sup>\<infinity> \<le> (x + y)\<^sup>\<infinity>"
  by (metis add_assoc' distrib_right' mult_oner coinduction join.sup_ge1 iteration_unfoldl)

lemma iteration_iso: "x \<le> y \<Longrightarrow> x\<^sup>\<infinity> \<le> y\<^sup>\<infinity>"
  using iteration_subdist local.order_prop by auto
 
lemma iteration_unfoldr [simp]: "1 + x\<^sup>\<infinity> \<cdot> x = x\<^sup>\<infinity>"
  by (metis add_0_left annil eq_refl isolation mult.assoc iteration_idem iteration_unfoldl iteration_unfoldl_distr star_denest star_one star_prod_unfold star_slide tc)

lemma iteration_unfoldr_distl [simp]: " y + y \<cdot> x\<^sup>\<infinity> \<cdot> x = y \<cdot> x\<^sup>\<infinity>"
  by (metis distrib_left mult.assoc mult_oner iteration_unfoldr)

lemma iteration_unfoldr_distr [simp]: " y + x\<^sup>\<infinity> \<cdot> x \<cdot> y = x\<^sup>\<infinity> \<cdot> y"
  by (metis iteration_unfoldl_distr iteration_unfoldr_distl)

lemma iteration_unfold_eq: "x\<^sup>\<infinity> \<cdot> x = x \<cdot> x\<^sup>\<infinity>"
  by (metis iteration_unfoldl_distr iteration_unfoldr_distl)
  
lemma iteration_unfoldr' [simp]: "z \<cdot> y + z \<cdot> x\<^sup>\<infinity> \<cdot> x \<cdot> y = z \<cdot> x\<^sup>\<infinity> \<cdot> y"
  by (metis distrib_left mult.assoc iteration_unfoldr_distr)

lemma iteration_double [simp]: "(x\<^sup>\<infinity>)\<^sup>\<infinity> = \<top>"
  by (simp add: iteration_iso iteration_refl local.eq_iff top_ref)

lemma star_iteration [simp]: "(x\<^sup>\<star>)\<^sup>\<infinity> = \<top>"
  by (simp add: iteration_iso local.eq_iff top_ref)

lemma iteration_star [simp]: "(x\<^sup>\<infinity>)\<^sup>\<star> = x\<^sup>\<infinity>"
  by (metis (no_types) iteration_idem iteration_refl local.star_inductr_var_eq2 local.sup_id_star1)

lemma iteration_star2 [simp]: "x\<^sup>\<star> \<cdot> x\<^sup>\<infinity> = x\<^sup>\<infinity>"
proof -
  have f1: "(x\<^sup>\<infinity>)\<^sup>\<star> \<cdot> x\<^sup>\<star> = x\<^sup>\<infinity>"
    by (metis (no_types) it_ext iteration_induct iteration_star local.bubble_sort local.join.sup.absorb1)
  have "x\<^sup>\<infinity> = x\<^sup>\<infinity> \<cdot> x\<^sup>\<infinity>"
    by simp
  hence "x\<^sup>\<star> \<cdot> x\<^sup>\<infinity> = x\<^sup>\<star> \<cdot> (x\<^sup>\<infinity>)\<^sup>\<star> \<cdot> (x\<^sup>\<star> \<cdot> (x\<^sup>\<infinity>)\<^sup>\<star>)\<^sup>\<star>"
    using f1 by (metis (no_types) iteration_star local.star_denest_var_4 mult_assoc)
  thus ?thesis
    using f1 by (metis (no_types) iteration_star local.star_denest_var_4 local.star_denest_var_8)
qed

lemma iteration_zero [simp]: "0\<^sup>\<infinity> = 1"
  by (metis add_zeror annil iteration_unfoldl)

lemma iteration_annil [simp]: "(x \<cdot> 0)\<^sup>\<infinity> = 1 + x \<cdot> 0"
  by (metis annil iteration_unfoldl mult.assoc)

lemma iteration_subdenest: "x\<^sup>\<infinity> \<cdot> y\<^sup>\<infinity> \<le> (x + y)\<^sup>\<infinity>"
  by (metis add_commute iteration_idem iteration_subdist local.mult_isol_var)
  
lemma sup_id_top: "1 \<le> y \<Longrightarrow> y \<cdot> \<top> = \<top>"
  using local.eq_iff local.mult_isol_var top_ref by fastforce

lemma iteration_top [simp]: "x\<^sup>\<infinity> \<cdot> \<top> = \<top>"
  by (simp add: iteration_refl sup_id_top)

text \<open>Next, we prove some simulation laws for data refinement.\<close>

lemma iteration_sim: "z \<cdot> y \<le> x \<cdot> z \<Longrightarrow> z \<cdot> y\<^sup>\<infinity> \<le> x\<^sup>\<infinity> \<cdot> z"
proof -
  assume assms: "z \<cdot> y \<le> x \<cdot> z"
  have "z \<cdot> y\<^sup>\<infinity> = z + z \<cdot> y \<cdot> y\<^sup>\<infinity>"
    by simp
  also have "... \<le> z + x \<cdot> z \<cdot> y\<^sup>\<infinity>"
    by (metis assms add.commute add_iso mult_isor)
  finally show "z \<cdot> y\<^sup>\<infinity> \<le> x\<^sup>\<infinity> \<cdot> z"
    by (simp add: local.coinduction mult_assoc)
qed

text \<open>Nitpick gives a counterexample to the dual simulation law.\<close>

lemma "y \<cdot> z \<le> z \<cdot> x \<Longrightarrow> y\<^sup>\<infinity> \<cdot> z \<le> z \<cdot> x\<^sup>\<infinity>"
(*nitpick [expect=genuine]*)
oops
  
text \<open>Next, we prove some sliding laws.\<close>

lemma iteration_slide_var: "x \<cdot> (y \<cdot> x)\<^sup>\<infinity> \<le> (x \<cdot> y)\<^sup>\<infinity> \<cdot> x"
  by (simp add: iteration_sim mult_assoc)

lemma iteration_prod_unfold [simp]: "1 + y \<cdot> (x \<cdot> y)\<^sup>\<infinity> \<cdot> x = (y \<cdot> x)\<^sup>\<infinity>"
proof (rule antisym)
  have "1 + y \<cdot> (x \<cdot> y)\<^sup>\<infinity> \<cdot> x \<le> 1 + (y \<cdot> x)\<^sup>\<infinity> \<cdot> y \<cdot> x"
    using iteration_slide_var local.join.sup_mono local.mult_isor by blast
  thus "1 + y \<cdot> (x \<cdot> y)\<^sup>\<infinity> \<cdot> x \<le>  (y \<cdot> x)\<^sup>\<infinity>"
    by (simp add: mult_assoc)
  have "(y \<cdot> x)\<^sup>\<infinity> = 1 + y \<cdot> x \<cdot> (y \<cdot> x)\<^sup>\<infinity>"
    by simp
  thus "(y \<cdot> x)\<^sup>\<infinity> \<le> 1 + y \<cdot> (x \<cdot> y)\<^sup>\<infinity> \<cdot> x"
    by (metis iteration_sim local.eq_refl local.join.sup.mono local.mult_isol mult_assoc)
qed

lemma iteration_slide: "x \<cdot> (y \<cdot> x)\<^sup>\<infinity> = (x \<cdot> y)\<^sup>\<infinity> \<cdot> x"
  by (metis iteration_prod_unfold iteration_unfoldl_distr distrib_left mult_1_right mult.assoc)

lemma star_iteration_slide [simp]: " y\<^sup>\<star> \<cdot> (x\<^sup>\<star> \<cdot> y)\<^sup>\<infinity> = (x\<^sup>\<star> \<cdot> y)\<^sup>\<infinity>"
  by (metis iteration_star2 local.conway.dagger_unfoldl_distr local.join.sup.orderE local.mult_isor local.star_invol local.star_subdist local.star_trans_eq)

text \<open>The following laws are called denesting laws.\<close>

lemma iteration_sub_denest: "(x + y)\<^sup>\<infinity> \<le> x\<^sup>\<infinity> \<cdot> (y \<cdot> x\<^sup>\<infinity>)\<^sup>\<infinity>"
proof -
  have "(x + y)\<^sup>\<infinity> = x \<cdot> (x + y)\<^sup>\<infinity> + y \<cdot> (x + y)\<^sup>\<infinity> + 1"
    by (metis add.commute distrib_right' iteration_unfoldl)
  hence "(x + y)\<^sup>\<infinity> \<le> x\<^sup>\<infinity> \<cdot> (y \<cdot> (x + y)\<^sup>\<infinity> + 1)"
    by (metis add_assoc' join.sup_least join.sup_ge1 join.sup_ge2 coinduction)
  moreover hence "x\<^sup>\<infinity> \<cdot> (y \<cdot> (x + y)\<^sup>\<infinity> + 1) \<le> x\<^sup>\<infinity> \<cdot> (y \<cdot> x\<^sup>\<infinity>)\<^sup>\<infinity>"
    by (metis add_iso mult.assoc mult_isol add.commute coinduction mult_oner mult_isol)
  ultimately show ?thesis
    using local.order_trans by blast
qed

lemma iteration_denest: "(x + y)\<^sup>\<infinity> = x\<^sup>\<infinity> \<cdot> (y \<cdot> x\<^sup>\<infinity>)\<^sup>\<infinity>"
proof -
  have "x\<^sup>\<infinity> \<cdot> (y \<cdot> x\<^sup>\<infinity>)\<^sup>\<infinity> \<le> x \<cdot> x\<^sup>\<infinity> \<cdot> (y \<cdot> x\<^sup>\<infinity>)\<^sup>\<infinity> + y \<cdot> x\<^sup>\<infinity> \<cdot> (y \<cdot> x\<^sup>\<infinity>)\<^sup>\<infinity> + 1"
    by (metis add.commute iteration_unfoldl_distr add_assoc' add.commute iteration_unfoldl order_refl)
  thus ?thesis
    by (metis add.commute iteration_sub_denest order.antisym coinduction distrib_right' iteration_sub_denest mult.assoc mult_oner order.antisym)
qed
(*
end

sublocale dra \<subseteq> conway_zerol strong_iteration 
  apply (unfold_locales)
  apply (simp add: iteration_denest iteration_slide)
  apply simp
  by (simp add: iteration_sim)


context dra
begin
*)
lemma iteration_denest2 [simp]: "y\<^sup>\<star> \<cdot> x \<cdot> (x + y)\<^sup>\<infinity> + y\<^sup>\<infinity> = (x + y)\<^sup>\<infinity>"
proof -
  have "(x + y)\<^sup>\<infinity> = y\<^sup>\<infinity> \<cdot> x \<cdot> (y\<^sup>\<infinity> \<cdot> x)\<^sup>\<infinity> \<cdot> y\<^sup>\<infinity> + y\<^sup>\<infinity>"
    by (metis add.commute iteration_denest iteration_slide iteration_unfoldl_distr)
  also have "... = y\<^sup>\<star> \<cdot> x \<cdot> (y\<^sup>\<infinity> \<cdot> x)\<^sup>\<infinity> \<cdot> y\<^sup>\<infinity> + y\<^sup>\<infinity> \<cdot> 0 + y\<^sup>\<infinity>"
    by (metis isolation mult.assoc distrib_right' annil mult.assoc)
  also have "... = y\<^sup>\<star> \<cdot> x \<cdot> (y\<^sup>\<infinity> \<cdot> x)\<^sup>\<infinity> \<cdot> y\<^sup>\<infinity> + y\<^sup>\<infinity>"
    by (metis add.assoc distrib_left mult_1_right add_0_left mult_1_right)
  finally show ?thesis
    by (metis add.commute iteration_denest iteration_slide mult.assoc)
qed

lemma iteration_denest3: "(y\<^sup>\<star> \<cdot> x)\<^sup>\<infinity> \<cdot> y\<^sup>\<infinity> = (x + y)\<^sup>\<infinity>"
proof (rule antisym)
  have  "(y\<^sup>\<star> \<cdot> x)\<^sup>\<infinity> \<cdot> y\<^sup>\<infinity> \<le> (y\<^sup>\<infinity> \<cdot> x)\<^sup>\<infinity> \<cdot> y\<^sup>\<infinity>"
    by (simp add: iteration_iso iteration_ref_star local.mult_isor)
  thus  "(y\<^sup>\<star> \<cdot> x)\<^sup>\<infinity> \<cdot> y\<^sup>\<infinity> \<le> (x + y)\<^sup>\<infinity>"
    by (metis iteration_denest iteration_slide local.join.sup_commute)
  have "(x + y)\<^sup>\<infinity> = y\<^sup>\<infinity> + y\<^sup>\<star> \<cdot> x \<cdot> (x + y)\<^sup>\<infinity>"
    by (metis iteration_denest2 local.join.sup_commute)
  thus "(x + y)\<^sup>\<infinity> \<le> (y\<^sup>\<star> \<cdot> x)\<^sup>\<infinity> \<cdot> y\<^sup>\<infinity>"
    by (simp add: local.coinduction) 
qed

text \<open>Now we prove separation laws for reasoning about distributed systems in the context of action systems.\<close>

lemma iteration_sep: "y \<cdot> x \<le> x \<cdot> y \<Longrightarrow> (x + y)\<^sup>\<infinity> = x\<^sup>\<infinity> \<cdot> y\<^sup>\<infinity>"
proof -
  assume "y \<cdot> x \<le> x \<cdot> y"
  hence "y\<^sup>\<star> \<cdot> x \<le> x\<cdot>(x + y)\<^sup>\<star>"
    by (metis star_sim1 add.commute mult_isol order_trans star_subdist)
  hence "y\<^sup>\<star> \<cdot> x \<cdot> (x + y)\<^sup>\<infinity> + y\<^sup>\<infinity> \<le> x \<cdot> (x + y)\<^sup>\<infinity> + y\<^sup>\<infinity>"
    by (metis mult_isor mult.assoc iteration_star2 join.sup.mono eq_refl)
  thus ?thesis
    by (metis iteration_denest2 add.commute coinduction add.commute less_eq_def iteration_subdenest)
qed

lemma iteration_sim2: "y \<cdot> x \<le> x \<cdot> y \<Longrightarrow> y\<^sup>\<infinity> \<cdot> x\<^sup>\<infinity> \<le> x\<^sup>\<infinity> \<cdot> y\<^sup>\<infinity>"
  by (metis add.commute iteration_sep iteration_subdenest)

lemma iteration_sep2: "y \<cdot> x \<le> x \<cdot> y\<^sup>\<star> \<Longrightarrow> (x + y)\<^sup>\<infinity> = x\<^sup>\<infinity> \<cdot> y\<^sup>\<infinity>"
proof - 
  assume "y \<cdot> x \<le> x \<cdot> y\<^sup>\<star>"
  hence "y\<^sup>\<star> \<cdot> (y\<^sup>\<star> \<cdot> x)\<^sup>\<infinity> \<cdot> y\<^sup>\<infinity> \<le> x\<^sup>\<infinity> \<cdot> y\<^sup>\<star> \<cdot> y\<^sup>\<infinity>"
    by (metis mult.assoc mult_isor iteration_sim star_denest_var_2 star_sim1 star_slide_var star_trans_eq tc_eq)
  moreover have "x\<^sup>\<infinity> \<cdot> y\<^sup>\<star> \<cdot> y\<^sup>\<infinity> \<le> x\<^sup>\<infinity> \<cdot> y\<^sup>\<infinity>"
    by (metis eq_refl mult.assoc iteration_star2)
  moreover have "(y\<^sup>\<star> \<cdot> x)\<^sup>\<infinity> \<cdot> y\<^sup>\<infinity> \<le> y\<^sup>\<star> \<cdot> (y\<^sup>\<star> \<cdot> x)\<^sup>\<infinity> \<cdot> y\<^sup>\<infinity>"
    by (metis mult_isor mult_onel star_ref)
  ultimately show ?thesis
    by (metis antisym iteration_denest3 iteration_subdenest order_trans)
qed

lemma iteration_sep3: "y \<cdot> x \<le> x \<cdot> (x + y) \<Longrightarrow> (x + y)\<^sup>\<infinity> = x\<^sup>\<infinity> \<cdot> y\<^sup>\<infinity>"
proof -
  assume "y \<cdot> x \<le> x \<cdot> (x + y)"
  hence "y\<^sup>\<star> \<cdot> x \<le> x \<cdot> (x + y)\<^sup>\<star>"
    by (metis star_sim1)
  hence "y\<^sup>\<star> \<cdot> x \<cdot> (x + y)\<^sup>\<infinity> + y\<^sup>\<infinity> \<le> x \<cdot> (x + y)\<^sup>\<star> \<cdot> (x + y)\<^sup>\<infinity> + y\<^sup>\<infinity>"
    by (metis add_iso mult_isor)
  hence "(x + y)\<^sup>\<infinity> \<le> x\<^sup>\<infinity> \<cdot> y\<^sup>\<infinity>"
    by (metis mult.assoc iteration_denest2 iteration_star2 add.commute coinduction)
  thus ?thesis
    by (metis add.commute less_eq_def iteration_subdenest)
qed

lemma iteration_sep4: "y \<cdot> 0 = 0 \<Longrightarrow> z \<cdot> x = 0 \<Longrightarrow> y \<cdot> x \<le> (x + z) \<cdot> y\<^sup>\<star> \<Longrightarrow> (x + y + z)\<^sup>\<infinity> = x\<^sup>\<infinity> \<cdot> (y + z)\<^sup>\<infinity>"
proof -
  assume assms: "y \<cdot> 0 = 0" "z \<cdot> x = 0" "y \<cdot> x \<le> (x + z) \<cdot> y\<^sup>\<star>"
  have "y \<cdot> y\<^sup>\<star> \<cdot> z \<le> y\<^sup>\<star> \<cdot> z \<cdot> y\<^sup>\<star>"
    by (metis mult_isor star_1l mult_oner order_trans star_plus_one subdistl)
  have "y\<^sup>\<star> \<cdot> z \<cdot> x \<le> x \<cdot> y\<^sup>\<star> \<cdot> z"
    by (metis join.bot_least assms(1) assms(2) independence1 mult.assoc)
  have "y \<cdot> (x + y\<^sup>\<star> \<cdot> z) \<le> (x + z) \<cdot> y\<^sup>\<star> + y \<cdot> y\<^sup>\<star> \<cdot> z"
    by (metis assms(3) distrib_left mult.assoc add_iso)
  also have "... \<le> (x + y\<^sup>\<star> \<cdot> z) \<cdot> y\<^sup>\<star> + y \<cdot> y\<^sup>\<star> \<cdot> z" 
    by (metis star_ref join.sup.mono eq_refl mult_1_left mult_isor)
  also have "... \<le> (x + y\<^sup>\<star> \<cdot> z) \<cdot> y\<^sup>\<star> + y\<^sup>\<star> \<cdot> z  \<cdot> y\<^sup>\<star>" using \<open>y \<cdot> y\<^sup>\<star> \<cdot> z \<le> y\<^sup>\<star> \<cdot> z \<cdot> y\<^sup>\<star>\<close>
    by (metis add.commute add_iso)
  finally have "y \<cdot> (x + y\<^sup>\<star> \<cdot> z) \<le> (x + y\<^sup>\<star> \<cdot> z) \<cdot> y\<^sup>\<star>"
    by (metis add.commute add_idem' add.left_commute distrib_right)
  moreover have "(x + y + z)\<^sup>\<infinity> \<le> (x + y + y\<^sup>\<star> \<cdot> z)\<^sup>\<infinity>"
    by (metis star_ref join.sup.mono eq_refl mult_1_left mult_isor iteration_iso)  
  moreover have "... = (x + y\<^sup>\<star> \<cdot> z)\<^sup>\<infinity> \<cdot> y\<^sup>\<infinity>"
    by (metis add_commute calculation(1) iteration_sep2 local.add_left_comm)
  moreover have "... = x\<^sup>\<infinity> \<cdot> (y\<^sup>\<star> \<cdot> z)\<^sup>\<infinity> \<cdot> y\<^sup>\<infinity>" using \<open>y\<^sup>\<star> \<cdot> z \<cdot> x \<le> x \<cdot> y\<^sup>\<star> \<cdot> z\<close>
    by (metis iteration_sep mult.assoc)
  ultimately have "(x + y + z)\<^sup>\<infinity> \<le> x\<^sup>\<infinity> \<cdot> (y + z)\<^sup>\<infinity>"
    by (metis add.commute mult.assoc iteration_denest3)
  thus ?thesis
    by (metis add.commute add.left_commute less_eq_def iteration_subdenest)
qed

text \<open>Finally, we prove some blocking laws.\<close>

text \<open>Nitpick refutes the next lemma.\<close>

lemma "x \<cdot> y = 0 \<Longrightarrow> x\<^sup>\<infinity> \<cdot> y = y"
(*nitpick*)
oops

lemma iteration_idep: "x \<cdot> y = 0 \<Longrightarrow> x \<cdot> y\<^sup>\<infinity> = x"
  by (metis add_zeror annil iteration_unfoldl_distl)

text \<open>Nitpick refutes the next lemma.\<close>

lemma "y \<cdot> w \<le> x \<cdot> y + z \<Longrightarrow> y \<cdot> w\<^sup>\<infinity> \<le> x\<^sup>\<infinity> \<cdot> z"
(*nitpick [expect=genuine]*)
oops

text \<open>At the end of this file, we consider a data refinement example from von Wright~\cite{Wright02}.\<close>

lemma data_refinement:
  assumes "s' \<le> s \<cdot> z" and "z \<cdot> e' \<le> e" and "z \<cdot> a' \<le> a \<cdot> z" and "z \<cdot> b \<le> z" and "b\<^sup>\<infinity> = b\<^sup>\<star>"
  shows "s' \<cdot> (a' + b)\<^sup>\<infinity> \<cdot> e' \<le> s \<cdot> a\<^sup>\<infinity> \<cdot> e"
proof -
  have "z \<cdot> b\<^sup>\<star> \<le> z"
    by (metis assms(4) star_inductr_var)
  have "(z \<cdot> a') \<cdot> b\<^sup>\<star> \<le> (a \<cdot> z) \<cdot> b\<^sup>\<star>"
    by (metis assms(3) mult.assoc mult_isor)
  hence "z \<cdot> (a' \<cdot> b\<^sup>\<star>)\<^sup>\<infinity> \<le>  a\<^sup>\<infinity> \<cdot> z" using \<open>z \<cdot> b\<^sup>\<star> \<le> z\<close>
    by (metis mult.assoc mult_isol order_trans iteration_sim mult.assoc)
  have "s' \<cdot> (a' + b)\<^sup>\<infinity> \<cdot> e' \<le> s' \<cdot> b\<^sup>\<star> \<cdot> (a' \<cdot> b\<^sup>\<star>)\<^sup>\<infinity> \<cdot> e'"
    by (metis add.commute assms(5) eq_refl iteration_denest mult.assoc)
  also have "... \<le> s \<cdot> z \<cdot> b\<^sup>\<star> \<cdot> (a' \<cdot> b\<^sup>\<star>)\<^sup>\<infinity> \<cdot> e'"
    by (metis assms(1) mult_isor)
  also have "... \<le> s \<cdot> z \<cdot> (a' \<cdot> b\<^sup>\<star>)\<^sup>\<infinity> \<cdot> e'" using \<open>z \<cdot> b\<^sup>\<star> \<le> z\<close>
    by (metis mult.assoc mult_isol mult_isor)
  also have "... \<le> s \<cdot> a\<^sup>\<infinity> \<cdot> z \<cdot> e'" using \<open>z \<cdot> (a' \<cdot> b\<^sup>\<star>)\<^sup>\<infinity> \<le>  a\<^sup>\<infinity> \<cdot> z\<close>
    by (metis mult.assoc mult_isol mult_isor)
  finally show ?thesis
    by (metis assms(2) mult.assoc mult_isol mult.assoc mult_isol order_trans)
qed

end

end
