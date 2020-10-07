(* Title: Star and Fixpoints in Quantales
   Author: Georg Struth
   Maintainer: Georg Struth <g.struth@sheffield.ac.uk> 
*)

section \<open>Star and Fixpoints in Quantales\<close>

theory Quantale_Star
  imports Quantales 
          Kleene_Algebra.Kleene_Algebra

begin

text \<open>This component formalises properties of the star in quantales. For pre-quantales these are modelled as 
fixpoints. For weak quantales they are given by iteration.\<close>


subsection \<open>Star and Fixpoints in Pre-Quantales\<close>
                     
context unital_near_quantale
begin 

definition "qiter_fun x y = (\<squnion>) x \<circ> (\<cdot>) y"

definition "qiterl x y = lfp (qiter_fun x y)"
  
definition "qiterg x y = gfp (qiter_fun x y)"

abbreviation "qiterl_id \<equiv> qiterl 1"
  
abbreviation "qiterq_id \<equiv> qiterg 1"

definition "qstar x = (\<Squnion>i. x ^ i)"

lemma qiter_fun_exp: "qiter_fun x y z = x \<squnion> y \<cdot> z"
  unfolding qiter_fun_def by simp

end

text \<open>Many properties of fixpoints have been developed for Isabelle's monotone functions. These carry
two type parameters, and must therefore be used outside of contexts.\<close>

lemma iso_qiter_fun: "mono (\<lambda>z::'a::unital_pre_quantale. qiter_fun x y z)"
  by (metis monoI proto_pre_quantale_class.mult_isol qiter_fun_exp sup.idem sup.mono sup.orderI)

text \<open>I derive the left unfold and induction laws of Kleene algebra. I link with the Kleene algebra components
at the end of this section, to bring properties into scope.\<close>

lemma qiterl_unfoldl [simp]: "x \<squnion> y \<cdot> qiterl x y = qiterl (x::'a::unital_pre_quantale) y"
  by (metis iso_qiter_fun lfp_unfold qiter_fun_exp qiterl_def)

lemma qiterg_unfoldl [simp]: "x \<squnion> y \<cdot> qiterg x y = qiterg (x::'a::unital_pre_quantale) y"
  by (metis gfp_fixpoint iso_qiter_fun qiter_fun_exp qiterg_def)

lemma qiterl_inductl: "x \<squnion> y \<cdot> z \<le> z \<Longrightarrow> qiterl (x::'a::unital_near_quantale) y \<le> z"
  by (simp add: lfp_lowerbound qiterl_def qiter_fun_def)
 
lemma qiterg_coinductl: "z \<le> x \<squnion> y \<cdot> z \<Longrightarrow> z \<le> qiterg (x::'a::unital_near_quantale) y"
  by (simp add: gfp_upperbound qiterg_def qiter_fun_def)

context unital_near_quantale
begin

lemma powers_distr: "qstar x \<cdot> y = (\<Squnion>i. x ^ i \<cdot> y)"
  by (simp add: qstar_def Sup_distr image_comp)

lemma Sup_iter_unfold: "x ^ 0 \<squnion> (\<Squnion>n. x ^ (Suc n)) = (\<Squnion>n. x ^ n)"
  using fSup_unfold by presburger 

lemma Sup_iter_unfold_var: "1 \<squnion> (\<Squnion>n. x \<cdot> x ^ n) = (\<Squnion>n. x ^ n)" 
  by (simp only: Sup_iter_unfold[symmetric]) auto

lemma power_inductr: "z \<squnion> y \<cdot> x \<le> y \<Longrightarrow> z \<cdot> x ^ i \<le> y"
  by (induct i, simp_all, metis power_commutes eq_iff mult_isor order.trans mult_assoc power.power.power_Suc)
    
end

context unital_pre_quantale
begin

lemma powers_subdistl: "(\<Squnion>i. x \<cdot> y ^ i) \<le> x \<cdot> qstar y"
   by (simp add: SUP_le_iff SUP_upper mult_isol qstar_def)

lemma qstar_subcomm: "qstar x \<cdot> x \<le> x \<cdot> qstar x"
  by (simp add: powers_distr powers_subdistl power_commutes)

lemma power_inductl: "z \<squnion> x \<cdot> y \<le> y \<Longrightarrow> x ^ i \<cdot> z \<le> y"
  by (induct i, simp_all, metis dual_order.trans mult_isol mult_assoc)

end

subsection \<open>Star and Iteration in Weak Quantales\<close>

context unital_weak_quantale
begin

text \<open>In unital weak quantales one can derive the star axioms of Kleene algebra for iteration. This
generalises the language and relation models from our Kleene algebra components.\<close>

lemma powers_distl: "x \<cdot> qstar y = (\<Squnion>i. x \<cdot> y ^ i)"
  by (simp add: qstar_def weak_Sup_distl image_comp)

lemma qstar_unfoldl: "1 \<squnion> x \<cdot> qstar x \<le> qstar x"
  by (simp only: powers_distl Sup_iter_unfold_var, simp add: qstar_def)
 
lemma qstar_comm: "x \<cdot> qstar x = qstar x \<cdot> x"
  using power_commutes powers_distr powers_distl by auto

lemma qstar_unfoldr [simp]: "1 \<squnion> qstar x \<cdot> x = qstar x"
  using qstar_comm qstar_unfoldl Sup_iter_unfold_var qstar_def powers_distl by auto 

lemma qstar_inductl: "z \<squnion> x \<cdot> y \<le> y \<Longrightarrow> qstar x \<cdot> z \<le> y"
  by (subst powers_distr, auto intro!: Sup_least power_inductl)

lemma qstar_inductr: "z \<squnion> y \<cdot> x \<le> y \<Longrightarrow> z \<cdot> qstar x \<le> y"
  by (subst powers_distl, auto intro!: Sup_least power_inductr)

text \<open>Hence in this setting one also obtains the right Kleene algebra axioms.\<close>

end

sublocale unital_weak_quantale \<subseteq> uwqlka: left_kleene_algebra_zerol "(\<squnion>)" "(\<cdot>)" 1 \<bottom> "(\<le>)" "(<)" qstar
  apply unfold_locales
  using qstar_unfoldl apply blast
  by (simp add: qstar_inductl)

sublocale unital_quantale \<subseteq> uqka: kleene_algebra "(\<squnion>)" "(\<cdot>)" 1 \<bottom> "(\<le>)" "(<)" qstar
  by unfold_locales (simp add: qstar_inductr)

text \<open>The star is indeed the least fixpoint.\<close>

lemma  qstar_qiterl: "qstar (x::'a::unital_weak_quantale) = qiterl_id x"
  by (simp add: antisym qiterl_inductl uwqlka.star_inductl_one)

context unital_weak_quantale
begin


subsection \<open>Deriving the Star Axioms of Action Algebras\<close>

text \<open>Finally the star axioms of action algebras are derived.\<close>

lemma act_star1: "1 \<squnion> x \<squnion> (qstar x) \<cdot> (qstar x) \<le> (qstar x)"
  by simp

lemma (in unital_quantale) act_star3: "qstar (x \<rightarrow> x) \<le> x \<rightarrow> x"
  by (simp add: bres_canc1 bres_galois_imp uqka.star_inductr_var)

lemma act_star3_var: "qstar (x \<leftarrow> x) \<le> x \<leftarrow> x"
  using fres_galois qstar_inductl by auto

end

text \<open>An integration of action algebras requires first resolving some notational issues within the components
where these algebras are located.\<close>
  
end

