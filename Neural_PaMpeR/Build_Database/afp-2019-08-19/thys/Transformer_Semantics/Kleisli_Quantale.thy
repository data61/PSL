(* 
  Title: The Quantale of Kleisli Arrows
  Author: Georg Struth 
  Maintainer: Georg Struth <g.struth@sheffield.ac.uk> 
*)

section \<open>The Quantale of Kleisli Arrows\<close>

theory Kleisli_Quantale
  imports Kleisli_Quantaloid 
          "Quantales.Quantale_Star"

begin

text \<open>This component revisits the results of the quantaloid one in the single-typed setting, that is, in 
the context of quantales. An instance proof, showing that Kleisli arrows (or state transformers) form quantales, is
its main result. Facts proved for quantales are thus made available for state transformers.\<close>

typedef 'a nd_fun = "{f::'a \<Rightarrow> 'a set. f \<in> UNIV}"
  by simp

setup_lifting type_definition_nd_fun

text \<open>Definitions are lifted to gain access to the Kleisli categories.\<close>

lift_definition r2fnd :: "'a rel \<Rightarrow> 'a nd_fun" is "Abs_nd_fun \<circ> \<F>".

lift_definition f2rnd :: "'a nd_fun \<Rightarrow> 'a rel" is "\<R> \<circ> Rep_nd_fun".

declare Rep_nd_fun_inverse [simp]

lemma r2f2r_inv: "r2fnd \<circ> f2rnd = id"
  by transfer (simp add: fun_eq_iff pointfree_idE)

lemma f2r2f_inv: "f2rnd \<circ> r2fnd = id"
  by transfer (simp add: fun_eq_iff r2f_def f2r_def Abs_nd_fun_inverse)

instantiation nd_fun :: (type) monoid_mult
begin

lift_definition one_nd_fun :: "'a nd_fun" is "Abs_nd_fun \<eta>".

lift_definition times_nd_fun :: "'a::type nd_fun \<Rightarrow> 'a::type nd_fun \<Rightarrow> 'a::type nd_fun" is "\<lambda>f g. Abs_nd_fun (Rep_nd_fun f \<circ>\<^sub>K Rep_nd_fun g)". 

instance
  by intro_classes (transfer, simp add: Abs_nd_fun_inverse kcomp_assoc)+

end

instantiation nd_fun :: (type) order_lean
begin

lift_definition less_eq_nd_fun :: "'a nd_fun \<Rightarrow> 'a nd_fun \<Rightarrow> bool" is "\<lambda>f g. Rep_nd_fun f \<le> Rep_nd_fun g".

lift_definition less_nd_fun :: "'a nd_fun \<Rightarrow> 'a nd_fun \<Rightarrow> bool" is "\<lambda>f g. Rep_nd_fun f \<le> Rep_nd_fun g \<and> f \<noteq> g".

instance
  apply intro_classes
    apply (transfer, simp)
   apply transfer using order.trans apply blast
  by (simp add: Rep_nd_fun_inject less_eq_nd_fun.abs_eq)

end

instantiation nd_fun :: (type) Sup_lattice
begin

lift_definition Sup_nd_fun :: "'a nd_fun set \<Rightarrow> 'a nd_fun" is "Abs_nd_fun \<circ> Sup \<circ> \<P> Rep_nd_fun". 

instance
  by (intro_classes; transfer, simp_all add: Abs_nd_fun_inverse Sup_upper sup_absorb2 Sup_le_iff)

end

lemma Abs_comp_hom: "Abs_nd_fun (f \<circ>\<^sub>K g) = Abs_nd_fun f \<cdot> Abs_nd_fun g"
  by transfer (simp add: Abs_nd_fun_inverse)

lemma Rep_comp_hom: "Rep_nd_fun (f \<cdot> g) = Rep_nd_fun f \<circ>\<^sub>K Rep_nd_fun g"
  by (simp add: Abs_nd_fun_inverse times_nd_fun.abs_eq)

instance nd_fun :: (type) unital_Sup_quantale
  by (intro_classes; transfer, simp_all) (smt Abs_comp_hom Rep_comp_hom Rep_nd_fun_inverse SUP_cong image_image kSup_distr kSup_distl)+

text \<open>Unfortunately, this is not it yet. To benefit from Isabelle's theorems for orderings, lattices, 
Kleene algebras and quantales, Isabelle's complete lattices need to be in scope. Somewhat annoyingly, this
requires more work...\<close>

instantiation nd_fun :: (type) complete_lattice
begin

lift_definition Inf_nd_fun :: "'a nd_fun set \<Rightarrow> 'a nd_fun" is "Abs_nd_fun \<circ> Inf \<circ> \<P> Rep_nd_fun". 

lift_definition bot_nd_fun :: "'a::type nd_fun" is "Abs_nd_fun (Sup {})".

lift_definition sup_nd_fun :: "'a::type nd_fun \<Rightarrow> 'a::type nd_fun \<Rightarrow> 'a::type nd_fun" is "\<lambda>f g. Abs_nd_fun (Rep_nd_fun f \<squnion> Rep_nd_fun g)".

lift_definition top_nd_fun :: "'a::type nd_fun" is "Abs_nd_fun (Inf {})".

lift_definition inf_nd_fun :: "'a::type nd_fun \<Rightarrow> 'a::type nd_fun \<Rightarrow> 'a::type nd_fun" is "\<lambda>f g. Abs_nd_fun (Rep_nd_fun f \<sqinter> Rep_nd_fun g)".

instance
  apply intro_classes
                 apply transfer using Rep_nd_fun_inject dual_order.antisym apply blast
                apply (transfer, simp)
               apply (transfer, simp)
              apply (simp add: Abs_nd_fun_inverse)
  by (transfer; simp_all add: Abs_nd_fun_inverse Sup_le_iff SUP_upper2 le_INF_iff Inf_lower)+

end

instance nd_fun :: (type) unital_quantale
  apply intro_classes
  using supq.Sup_distr apply fastforce
  by (simp add: supq.Sup_distl)

text \<open>Now, theorems for the Kleene star, which come from quantales, are finally in scope.\<close>

lemma fun_star_unfoldl_eq: "(1::'a nd_fun) \<squnion> f \<cdot> qstar f = qstar f"
  by (simp add: qstar_comm)

lemma fun_star_unfoldl: "(1::'a nd_fun) \<squnion> f \<cdot> qstar f \<le> qstar f"
  using qstar_unfoldl by blast
 
lemma fun_star_unfoldr_eq: "(1::'a nd_fun) \<squnion> (qstar f) \<cdot> f = qstar f"
  by simp

lemma fun_star_unfoldr: "(1::'a nd_fun) \<squnion> qstar f \<cdot> f \<le> qstar f"
  by (simp add: fun_star_unfoldr_eq)

lemma fun_star_inductl: "(h::'a nd_fun) \<squnion> f \<cdot> g \<le> g \<Longrightarrow> qstar f \<cdot>  h \<le> g"
  using qstar_inductl by blast

lemma fun_star_inductr: "(h::'a nd_fun) \<squnion> g \<cdot> f \<le> g \<Longrightarrow> h \<cdot> qstar f \<le> g"
  by (simp add: qstar_inductr)

end

