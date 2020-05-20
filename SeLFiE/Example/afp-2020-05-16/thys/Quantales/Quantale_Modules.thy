(* Title: Quantale Modules and Semidirect Products 
   Author: Georg Struth
   Maintainer: Georg Struth <g.struth@sheffield.ac.uk> 
*)

section \<open>Quantale Modules and Semidirect Products\<close>

theory Quantale_Modules
  imports Quantale_Star

begin

subsection \<open>Quantale Modules\<close>
  
text \<open>Quantale modules are extensions of semigroup actions in that a quantale acts on a complete lattice.
These have been investigated by Abramsky and Vickers~\cite{AbramskyV93} and others, predominantly in the context
of pointfree topology.\<close>
  
locale unital_quantale_module = 
  fixes act :: "'a::unital_quantale \<Rightarrow> 'b::complete_lattice_with_dual \<Rightarrow> 'b" ("\<alpha>")
  assumes act1: "\<alpha> (x \<cdot> y) p = \<alpha> x (\<alpha> y p)"
    and act2 [simp]: "\<alpha> 1 p = p" 
    and act3: "\<alpha> (\<Squnion>X) p = (\<Squnion>x \<in> X. \<alpha> x p)"
    and act4: "\<alpha> x (\<Squnion>P) = (\<Squnion>p \<in> P. \<alpha> x p)"

context unital_quantale_module
begin
  
text \<open>Actions are morphisms. The curried notation is particularly convenient for this.\<close>
  
lemma act_morph1: "\<alpha> (x \<cdot> y) = (\<alpha> x) \<circ> (\<alpha> y)"
  by (simp add: fun_eq_iff act1)
    
lemma act_morph2 [simp]: "\<alpha> 1 = id"
  by (simp add: fun_eq_iff)
  
lemma emp_act [simp]: "\<alpha> (\<Squnion>{}) p = \<bottom>"
  by (simp only: act3, force)
    
lemma emp_act_var [simp]: "\<alpha> \<bottom> p = \<bottom>"
  using emp_act by auto

lemma act_emp [simp]: "\<alpha> x (\<Squnion>{}) = \<bottom>"
  by (simp only: act4, force)
    
lemma act_emp_var [simp]: "\<alpha> x \<bottom> = \<bottom>"
  using act_emp by auto
  
lemma act_sup_distl: "\<alpha> x (p \<squnion> q) = (\<alpha> x p) \<squnion> (\<alpha> x q)"
  by (metis (mono_tags, lifting) act4 image_insert image_is_empty sup_Sup)
  
lemma act_sup_distr: "\<alpha> (x \<squnion> y) p = (\<alpha> x p) \<squnion> (\<alpha> y p)"
  by (metis (no_types, lifting) SUP_insert Sup_empty Sup_insert act3 sup_bot_right)
  
lemma act_sup_distr_var: "\<alpha> (x \<squnion> y) = (\<alpha> x) \<squnion> (\<alpha> y)"
  by (simp add: fun_eq_iff act_sup_distr)

subsection \<open>Semidirect Products and Weak Quantales\<close>
    
text \<open>Next, the semidirect product of a  unital quantale and a complete lattice is defined. \<close>
  
definition "sd_prod x y = (fst x \<cdot> fst y, snd x \<squnion> \<alpha> (fst x) (snd y))"
   
lemma sd_distr: "sd_prod (Sup_prod X) y = Sup_prod {sd_prod x y |x. x \<in> X}"
proof -
  have "sd_prod (Sup_prod X) y = sd_prod ((\<Squnion>x \<in> X. fst x), (\<Squnion>x \<in> X. snd x)) y"
    by (simp add: Sup_prod_def)
  also have "... = ((\<Squnion>x \<in> X. fst x) \<cdot> fst y, (\<Squnion>x \<in> X. snd x) \<squnion> (\<alpha> (\<Squnion>x \<in> X. fst x) (snd y)))"
    by (simp add: sd_prod_def)
  also have "... = ((\<Squnion>x \<in> X. (fst x \<cdot> fst y)), (\<Squnion>x \<in> X. snd x) \<squnion> (\<alpha> (\<Squnion>x \<in> X. fst x) (snd y)))"
    by (simp add: Sup_distr image_comp)
  also have "... = ((\<Squnion>x \<in> X. (fst x \<cdot> fst y)), (\<Squnion>x \<in> X. snd x) \<squnion> (\<Squnion>x \<in> X. (\<alpha> (fst x) (snd y))))"
    by (simp add: act3 image_comp)
  also have "... = ((\<Squnion>x \<in> X. (fst x \<cdot> fst y)), (\<Squnion>x \<in> X. (snd x \<squnion> (\<alpha> (fst x) (snd y)))))"
    using complete_lattice_class.SUP_sup_distrib by fastforce
  also have "... = Sup_prod {(fst x \<cdot> fst y, snd x \<squnion> (\<alpha> (fst x) (snd y))) |x. x \<in> X}"
    apply (unfold Sup_prod_def, safe)
    by ( simp add: SUP_Sup_eq, rule_tac f=Sup in arg_cong, force)+
  finally show ?thesis
    by (simp add: sd_prod_def)
qed
  
lemma sd_distl_aux: "Y \<noteq> {} \<Longrightarrow> p \<squnion> (\<Squnion>y \<in> Y. \<alpha> x (snd y)) = (\<Squnion>y \<in> Y. p \<squnion> \<alpha> x (snd y))"
  apply (rule antisym)
   apply (rule sup_least, metis SUP_bot_conv(2) SUP_const SUP_upper2 sup_ge1)
   apply (rule Sup_least, force simp: SUP_upper2 image_iff)
  by (rule Sup_least, safe, metis Sup_upper image_iff sup.idem sup.mono sup_ge2)

lemma sd_distl: "Y \<noteq> {} \<Longrightarrow> sd_prod x (Sup_prod Y) = Sup_prod {sd_prod x y |y. y \<in> Y}"
proof -
  assume a: "Y \<noteq> {}"
  have "sd_prod x (Sup_prod Y) = sd_prod x ((\<Squnion>y \<in> Y. fst y), (\<Squnion>y \<in> Y. snd y))"
    by (simp add: Sup_prod_def)
  also have "... = ((fst x) \<cdot> (\<Squnion>y \<in> Y. fst y), (snd x \<squnion> (\<alpha> (fst x) (\<Squnion>y \<in> Y. snd y))))"
    by (simp add: sd_prod_def)
  also have "... = ((\<Squnion>y \<in> Y. fst x \<cdot> fst y), (snd x \<squnion> (\<alpha> (fst x) (\<Squnion>y \<in> Y. snd y))))"
    by (simp add: Sup_distl image_comp)
  also have "... = ((\<Squnion>y \<in> Y. fst x \<cdot> fst y), (snd x \<squnion> (\<Squnion>y \<in> Y. \<alpha> (fst x) (snd y))))"
    by (simp add: act4 image_comp)
  also have "... = ((\<Squnion>y \<in> Y. fst x \<cdot> fst y), (\<Squnion>y \<in> Y. snd x \<squnion> (\<alpha> (fst x) (snd y))))"
    using a sd_distl_aux by blast
  also have "... = Sup_prod {(fst x \<cdot> fst y, snd x \<squnion> (\<alpha> (fst x) (snd y))) |y. y \<in> Y}"
    apply (unfold Sup_prod_def, safe)
    by ( simp add: SUP_Sup_eq, rule_tac f=Sup in arg_cong, force)+
  finally show ?thesis
    by (simp add: sd_prod_def)
qed
  
definition "sd_unit = (1,\<bottom>)"
 
lemma sd_unitl [simp]: "sd_prod sd_unit x = x"
  by (simp add: sd_prod_def sd_unit_def)    
    
lemma sd_unitr [simp]: "sd_prod x sd_unit = x"
  by (simp add: sd_prod_def sd_unit_def)

text \<open>The following counterexamples rule out that semidirect products of quantales and complete lattices form quantales.
The reason is that the right annihilation law fails.\<close>
  
lemma "sd_prod x (Sup_prod Y) = Sup_prod {sd_prod x y |y. y \<in> Y}" (*nitpick[show_all,expect=genuine]*)
  oops
  
lemma "sd_prod x bot_prod = bot_prod" (*nitpick[show_all,expect=genuine]*)
  oops
    
  text \<open>However one can show that semidirect products of (unital) quantales with complete lattices form weak (unital) quantales. 
This provides an example of how weak quantales arise quite naturally.\<close>
    
sublocale dp_quantale: weak_quantale sd_prod Inf_prod Sup_prod inf_prod less_eq_prod less_prod sup_prod bot_prod top_prod
  apply unfold_locales
    apply (simp add: act1 act_sup_distl mult.assoc sd_prod_def sup_assoc)
   apply (metis Setcompr_eq_image sd_distr)
  by (metis Setcompr_eq_image sd_distl) 

sublocale dpu_quantale: unital_weak_quantale sd_unit sd_prod Inf_prod Sup_prod inf_prod less_eq_prod less_prod sup_prod bot_prod top_prod
  by unfold_locales simp_all

subsection \<open>The Star in Semidirect Products\<close>

text \<open>I define the star operation for a semidirect product of a quantale and a complete lattice, 
and prove a characteristic property.\<close>

abbreviation "sd_power \<equiv> dpu_quantale.power"

abbreviation "sd_star \<equiv> dpu_quantale.qstar"    

lemma sd_power_zero [simp]: "sd_power x 0 = (1,\<bottom>)"
  using sd_unit_def by simp

lemma sd_power_prop_aux: "\<alpha> (x ^ 0) y \<squnion> (\<Squnion>{\<alpha> (x ^ k) y |k.  0 < k \<and> k \<le> Suc i}) = \<Squnion>{\<alpha> (x ^ k) y |k. k \<le> Suc i}"
  apply (rule antisym)
  apply (rule sup_least, intro Sup_upper, blast, intro Sup_mono, blast)
  apply (rule Sup_least, safe)
  by (metis (mono_tags, lifting) Sup_insert Sup_upper insert_iff le_0_eq linorder_not_le mem_Collect_eq)

lemma sd_power_prop1 [simp]: "sd_power (x,y) (Suc i) = (x ^ (Suc i), \<Squnion>{\<alpha> (x ^ k) y|k. k \<le> i})"
proof (induct i)
  case 0 thus ?case 
    by auto
next
  case (Suc i) thus ?case
  proof-
    assume "sd_power (x,y) (Suc i) = (x ^ Suc i, \<Squnion>{\<alpha> (x ^ k) y |k. k \<le> i})"
    hence "sd_power (x,y) (Suc (Suc i)) = (x ^ Suc (Suc i), \<alpha> (x ^ 0) y \<squnion> (\<Squnion>{\<alpha> (x ^ (Suc k)) y |k. k \<le> i}))"
      apply (simp add: sd_prod_def act1 act4)
      apply safe
      by (metis act4 image_Collect image_image)
    also have "... = (x ^ Suc (Suc i), \<alpha> (x ^ 0) y \<squnion> (\<Squnion>{\<alpha> (x ^ k) y |k.  0 < k \<and> k \<le> Suc i}))"
      by (metis (no_types, hide_lams) Suc_le_eq Suc_le_mono le_0_eq not0_implies_Suc zero_less_Suc)
    finally show ?thesis 
      using sd_power_prop_aux by simp
  qed
qed

lemma sd_power_prop2 [simp]: "sd_power (x,y) i = (x ^ i, \<Squnion>{\<alpha> (x ^ k) y|k. k < i})"
  apply (case_tac i)
  using sd_unit_def apply force
  using le_simps(2) unital_quantale_module.sd_power_prop1 unital_quantale_module_axioms by fastforce

lemma sdstar_prop: "sd_star (x,y) = (qstar x, \<alpha> (qstar x) y)"
proof -
  have "sd_star (x,y) = sup_prod (1,\<bottom>) (Sup_prod {sd_power (x,y) (Suc i) |i. True})"
    by (metis dpu_quantale.Sup_iter_unfold dpu_quantale.qstar_def full_SetCompr_eq sd_power_zero)
  also have "... = sup_prod (1,\<bottom>) (Sup_prod {(x^(Suc i), \<Squnion>{\<alpha> (x ^ k) y|k. k \<le> i}) |i. True})"
    using sd_power_prop1 by auto 
  also have "... = (1 \<squnion>( \<Squnion>i. x ^ (Suc i)), (\<Squnion>i. \<Squnion>{\<alpha> (x ^ k) y|k. k \<le> i}))"
    apply (unfold sup_prod_def Sup_prod_def, safe)
     apply (simp, rule_tac f="\<lambda>x. 1 \<squnion> x" in arg_cong)
    by (simp add: SUP_Sup_eq, rule_tac f=Sup in arg_cong, force)+
  also have "... = (qstar x, (\<Squnion>i. \<Squnion>{\<alpha> (x ^ k) y|k. k \<le> i}))"
    by (safe, metis (no_types) fSup_unfold power_0 qstar_def)
  also have "... = (qstar x, (\<Squnion>i. \<alpha> (x ^ i) y))" 
    apply safe
    apply (rule antisym)
     apply (safe intro!: Sup_least, simp add: Sup_upper)
    by (metis (mono_tags, lifting) SUP_upper2 Sup_upper mem_Collect_eq order_refl)
  finally show ?thesis
    by (simp add: qstar_def act3 image_comp)
qed

end

end
