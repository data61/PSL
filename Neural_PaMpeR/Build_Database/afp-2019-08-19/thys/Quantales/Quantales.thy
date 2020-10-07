(* Title: Quantales
   Author: Georg Struth 
   Maintainer: Georg Struth <g.struth@sheffield.ac.uk> 
   Contributions by Brijesh Dongol, Victor Gomes, Ian Hayes
*)

section \<open>Quantales\<close>

theory Quantales
  imports
    "Order_Lattice_Props.Closure_Operators"
   Kleene_Algebra.Dioid
begin

subsection \<open>Families of Proto-Quantales\<close>
  
text \<open>Proto-Quanales are complete lattices equipped with an operation of composition or multiplication
that need not be associative. The notation in this component differs from Rosenthal's \cite{Rosenthal90}, but is consistent with the one we use 
for semirings and Kleene algebras.\<close>
  
class proto_near_quantale = complete_lattice + times + 
  assumes Sup_distr: "\<Squnion>X \<cdot> y = (\<Squnion>x \<in> X. x \<cdot> y)"

lemma Sup_pres_multr: "Sup_pres (\<lambda>(z::'a::proto_near_quantale). z \<cdot> y)"
  unfolding fun_eq_iff comp_def Sup_distr by simp 

lemma sup_pres_multr: "sup_pres (\<lambda>(z::'a::proto_near_quantale). z \<cdot> y)"
  using Sup_pres_multr Sup_sup_pres by fastforce

lemma bot_pres_multr: "bot_pres (\<lambda>(z::'a::proto_near_quantale). z \<cdot> y)"
  by (metis SUP_empty Sup_distr Sup_empty)

context proto_near_quantale
begin

lemma mult_botl [simp]: "\<bottom> \<cdot> x = \<bottom>"
proof -
  have "\<bottom> \<cdot> x = (\<Squnion>a\<in>{}. a \<cdot> x)"
    using Sup_distr Sup_empty by blast
  thus ?thesis
    by simp
qed
  
lemma sup_distr: "(x \<squnion> y) \<cdot> z = (x \<cdot> z) \<squnion> (y \<cdot> z)"
  by (smt SUP_empty SUP_insert Sup_distr sup_Sup sup_bot.right_neutral)
   
lemma mult_isor: "x \<le> y \<Longrightarrow> x \<cdot> z \<le> y \<cdot> z"
  by (metis sup.absorb_iff1 sup_distr)

text \<open>Left and right residuals can be defined in every proto-nearquantale.\<close>
    
definition bres :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixr "\<rightarrow>" 60) where 
  "x \<rightarrow> z = \<Squnion>{y. x \<cdot> y \<le> z}"

definition fres :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<leftarrow>" 60) where 
  "z \<leftarrow> y = \<Squnion>{x. x \<cdot> y \<le> z}"

text \<open>The left one is a right adjoint  to composition. For the right one, additional assumptions are needed\<close>

lemma bres_galois_imp: "x \<cdot> y \<le> z \<Longrightarrow> y \<le> x \<rightarrow> z"
  by (simp add: Sup_upper bres_def)
    
lemma fres_galois: "(x \<cdot> y \<le> z) = (x \<le> z \<leftarrow> y)"
proof 
  show "x \<cdot> y \<le> z \<Longrightarrow> x \<le> z \<leftarrow> y"
    by (simp add: Sup_upper fres_def)
next
  assume "x \<le> z \<leftarrow> y"
  hence "x \<cdot> y \<le> \<Squnion>{x. x \<cdot> y \<le> z} \<cdot> y"
    by (simp add: fres_def mult_isor)
  also have "... = \<Squnion>{x \<cdot> y |x. x \<cdot> y \<le> z}"
    by (simp add: Sup_distr setcompr_eq_image)
  also have "... \<le> z"
    by (rule Sup_least, auto)
  finally show "x \<cdot> y \<le> z" .
qed

end

lemma fres_adj: "(\<lambda>(x::'a::proto_near_quantale). x \<cdot> y) \<stileturn> (\<lambda>x. x \<leftarrow> y)"
  by (simp add: adj_def fres_galois)

context proto_near_quantale
begin

lemma fres_canc1: "(y \<leftarrow> x) \<cdot> x \<le> y"
  by (simp add: fres_galois)

lemma fres_canc2: "y \<le> (y \<cdot> x) \<leftarrow> x"
  using fres_galois by force

lemma inf_fres: "y \<cdot> x = \<Sqinter>{z. y \<le> z \<leftarrow> x}"
  by (metis (mono_tags, lifting) fres_canc2 Inf_eqI fres_galois mem_Collect_eq)

lemma bres_iso: "x \<le> y \<Longrightarrow> z \<rightarrow> x \<le> z \<rightarrow> y"
  using Sup_le_iff bres_def bres_galois_imp by force

lemma bres_anti: "x \<le> y \<Longrightarrow> y \<rightarrow> z \<le> x \<rightarrow> z"
  by (smt Sup_le_iff bres_def bres_galois_imp fres_galois order_trans mem_Collect_eq)

lemma fres_iso: "x \<le> y \<Longrightarrow> x \<leftarrow> z \<le> y \<leftarrow> z"
  using fres_galois dual_order.trans by blast

lemma bres_top_top [simp]: "\<top> \<rightarrow> \<top> = \<top>"
  by (simp add: bres_galois_imp dual_order.antisym)

lemma fres_top_top [simp]: "\<top> \<leftarrow> \<top> = \<top>"
  using fres_galois top_greatest top_le by blast

lemma bres_bot_bot [simp]: "\<bottom> \<rightarrow> \<bottom> = \<top>"
  by (simp add: bres_galois_imp top_le)

lemma left_sided_localp: "\<top> \<cdot> y = y \<Longrightarrow> x \<cdot> y \<le> y"
  by (metis mult_isor top_greatest)

lemma fres_sol: "((y \<leftarrow> x) \<cdot> x = y) = (\<exists>z. z \<cdot> x = y)"
  using dual_order.antisym fres_canc1 fres_canc2 mult_isor by fastforce

lemma sol_fres: "((y \<cdot> x) \<leftarrow> x = y) = (\<exists>z. y = z \<leftarrow> x)"
  by (metis fres_canc1 fres_canc2 fres_sol eq_iff fres_galois)

end

class proto_pre_quantale = proto_near_quantale + 
  assumes Sup_subdistl: "(\<Squnion>y \<in> Y. x \<cdot> y) \<le> x \<cdot> \<Squnion>Y"
    
begin

lemma sup_subdistl: "(x \<cdot> y) \<squnion> (x \<cdot> z) \<le> x \<cdot> (y \<squnion> z)"
  by (smt SUP_empty SUP_insert Sup_subdistl sup_Sup sup_bot_right)

lemma mult_isol: "x \<le> y \<Longrightarrow> z \<cdot> x \<le> z \<cdot> y"
  by (metis le_iff_sup le_sup_iff sup_subdistl)

lemma fres_anti: "x \<le> y \<Longrightarrow> z \<leftarrow> y \<le> z \<leftarrow> x"
  using dual_order.trans fres_galois mult_isol by blast

end
    
class weak_proto_quantale = proto_near_quantale +
  assumes weak_Sup_distl: "Y \<noteq> {} \<Longrightarrow> x \<cdot> \<Squnion>Y = (\<Squnion>y \<in> Y. x \<cdot> y)" 

begin

subclass proto_pre_quantale
proof unfold_locales
  have a: "\<And>x Y. Y = {} \<Longrightarrow> (\<Squnion>y \<in> Y. x \<cdot> y) \<le> x \<cdot> \<Squnion>Y"
    by simp
  have b: "\<And>x Y. Y \<noteq> {} \<Longrightarrow> (\<Squnion>y \<in> Y. x \<cdot> y) \<le> x \<cdot> \<Squnion>Y"
    by (simp add: weak_Sup_distl)
  show  "\<And>x Y. (\<Squnion>y \<in> Y. x \<cdot> y) \<le> x \<cdot> \<Squnion>Y"
    using a b by blast
qed
  
lemma  sup_distl: "x \<cdot> (y \<squnion> z) = (x \<cdot> y) \<squnion> (x \<cdot> z)"  
  using weak_Sup_distl[where Y="{y, z}"] by (fastforce intro!: Sup_eqI)

lemma "y \<le> x \<rightarrow> z \<longrightarrow> x \<cdot> y \<le> z" (* nitpick [expect = genuine] *)
oops

end
  
class proto_quantale = proto_near_quantale +
  assumes Sup_distl: "x \<cdot> \<Squnion>Y = (\<Squnion>y \<in> Y. x \<cdot> y)"  

lemma Sup_pres_multl: "Sup_pres (\<lambda>(z::'a::proto_quantale). x \<cdot> z)"
  unfolding fun_eq_iff comp_def Sup_distl by simp 

lemma sup_pres_multl: "sup_pres (\<lambda>(z::'a::proto_quantale). x \<cdot> z)"
  by (metis (no_types, lifting) SUP_insert Sup_distl Sup_empty Sup_insert sup_bot_right)

lemma bot_pres_multl: "bot_pres (\<lambda>(z::'a::proto_quantale). x \<cdot> z)"
  by (metis SUP_empty Sup_distl Sup_empty)

context proto_quantale
begin
 
subclass weak_proto_quantale
  by standard (simp add: Sup_distl)

lemma mult_botr [simp]: "x \<cdot> \<bottom> = \<bottom>"
  by (smt image_empty Sup_distl Sup_empty)

text \<open>Now there is also an adjunction for the other residual.\<close>
    
lemma bres_galois: "x \<cdot> y \<le> z \<longleftrightarrow> y \<le> x \<rightarrow> z"
proof 
  show "x \<cdot> y \<le> z \<Longrightarrow> y \<le> x \<rightarrow> z"
    by (simp add: Sup_upper bres_def)
next
  assume "y \<le> x \<rightarrow> z"
  hence "x \<cdot> y \<le> x \<cdot> \<Squnion>{y. x \<cdot> y \<le> z}"
    by (simp add: bres_def mult_isol)
  also have "... = \<Squnion>{x \<cdot> y |y. x \<cdot> y \<le> z}"
    by (simp add: Sup_distl setcompr_eq_image)
  also have "... \<le> z"
    by (rule Sup_least, safe)
  finally show "x \<cdot> y \<le> z" .
qed 

end

lemma bres_adj: "(\<lambda>(y::'a::proto_quantale). x \<cdot> y) \<stileturn> (\<lambda>y. x \<rightarrow> y)"
  by (simp add: adj_def bres_galois)

context proto_quantale
begin

lemma bres_canc1: "x \<cdot> (x \<rightarrow> y) \<le> y"
  by (simp add: bres_galois)

lemma bres_canc2: "y \<le> x \<rightarrow> (x \<cdot> y)"
  by (simp add: bres_galois_imp)

lemma  inf_bres: "x \<cdot> y = \<Sqinter>{z. y \<le> x \<rightarrow> z}"
  using bres_galois fres_galois inf_fres by force

lemma bres_sol: "(x \<cdot> (x \<rightarrow> y) = y) = (\<exists>z. x \<cdot> z = y)"
  using bres_galois antisym mult_isol by force

lemma sol_bres: "(x \<rightarrow> (x \<cdot> y) = y) = (\<exists>z. y = x \<rightarrow> z)"
  by (metis bres_canc1 bres_canc2 bres_iso eq_iff)

end 

lemma bres_fres_clop: "clop (\<lambda>x::'a::proto_quantale. y \<leftarrow> (x \<rightarrow> y))"
  unfolding clop_def comp_def mono_def le_fun_def
  by (metis bres_anti bres_canc1 bres_galois_imp fres_anti fres_galois id_apply)

lemma fres_bres_clop: "clop (\<lambda>x::'a::proto_quantale. (y \<leftarrow> x) \<rightarrow> y)"
  unfolding clop_def comp_def mono_def le_fun_def
  by (metis bres_anti bres_canc1 bres_galois_imp fres_anti fres_canc1 fres_galois id_apply)


subsection \<open>Families of Quantales\<close>
  
class near_quantale = proto_near_quantale + semigroup_mult 

sublocale near_quantale \<subseteq> nsrnq: near_dioid "(\<squnion>)" "(\<cdot>)" "(\<le>)" "(<)"
  apply unfold_locales
       apply (simp add: sup_assoc)
      apply (simp add: sup_commute)
     apply (simp_all add: sup_distr)
   apply (simp add: le_iff_sup)
  by auto

context near_quantale
begin

lemma fres_curry: "(z \<leftarrow> y) \<leftarrow> x = z \<leftarrow> (x \<cdot> y)"
  by (metis eq_iff fres_canc1 fres_galois mult_assoc)

end
  
class unital_near_quantale = near_quantale + monoid_mult

sublocale unital_near_quantale \<subseteq> nsrnqo: near_dioid_one "(\<squnion>)" "(\<cdot>)" "1""(\<le>)" "(<)"
  by (unfold_locales, simp_all)

context unital_near_quantale
begin

definition iter :: "'a \<Rightarrow> 'a" where
  "iter x \<equiv> \<Sqinter>i. x ^ i"

lemma iter_ref [simp]: "iter x \<le> 1"
  by (metis iter_def Inf_lower power.power_0 rangeI)
   
lemma le_top: "x \<le> \<top> \<cdot> x"
  by (metis mult.left_neutral mult_isor top_greatest)

lemma top_times_top [simp]: "\<top> \<cdot> \<top> = \<top>"
  by (simp add: le_top top_le)

lemma bres_one: "1 \<le> x \<rightarrow> x"
  by (simp add: bres_galois_imp)

lemma fres_one: "1 \<le> x \<leftarrow> x"
  using fres_galois by fastforce

end
  
class pre_quantale = proto_pre_quantale + semigroup_mult 

begin

subclass near_quantale ..

lemma fres_interchange: "z \<cdot> (x \<leftarrow> y) \<le> (z \<cdot> x) \<leftarrow> y"
  using Sup_upper fres_canc1 fres_def mult_isol mult_assoc by fastforce

end

sublocale pre_quantale \<subseteq>  psrpq: pre_dioid "(\<squnion>)" "(\<cdot>)" "(\<le>)" "(<)"
  by (unfold_locales, simp add: mult_isol)

class unital_pre_quantale = pre_quantale + monoid_mult

begin
  
subclass unital_near_quantale ..

text \<open>Abstract rules of Hoare logic without the star can be derived.\<close>

lemma h_w1: "x \<le> x' \<Longrightarrow>  x' \<cdot> y \<le> z \<Longrightarrow> x \<cdot> y \<le> z"  
  by (simp add: fres_galois)

lemma h_w2: "x \<cdot> y \<le> z' \<Longrightarrow> z' \<le> z \<Longrightarrow> x \<cdot> y \<le> z"
  using order_trans by blast

lemma h_seq: "x \<cdot> v \<le> z \<Longrightarrow> y \<cdot> w \<le> v \<Longrightarrow> x \<cdot> y \<cdot> w \<le> z"
  using dual_order.trans mult_isol mult_assoc by presburger

lemma h_sup: "x \<cdot> w \<le> z \<Longrightarrow> y \<cdot> w \<le> z \<Longrightarrow> (x \<squnion> y) \<cdot> w \<le> z"
  by (simp add: fres_galois)

lemma h_Sup: "\<forall>x \<in> X. x \<cdot> w \<le> z \<Longrightarrow> \<Squnion>X \<cdot> w \<le> z"
  by (simp add: Sup_least fres_galois)

end

sublocale unital_pre_quantale \<subseteq>  psrpqo: pre_dioid_one "(\<squnion>)" "(\<cdot>)" "1" "(\<le>)" "(<)"..
    
class weak_quantale = weak_proto_quantale + semigroup_mult

begin
  
subclass pre_quantale ..
    
text \<open>The following counterexample shows an important consequence of weakness: 
the absence of right annihilation.\<close>
    
lemma "x \<cdot> \<bottom> = \<bottom>" (*nitpick[expect=genuine]*)
  oops

end

class unital_weak_quantale = weak_quantale + monoid_mult
    
lemma (in unital_weak_quantale) "x \<cdot> \<bottom> = \<bottom>" (*nitpick[expect=genuine]*)
  oops
  
subclass (in unital_weak_quantale) unital_pre_quantale ..

sublocale unital_weak_quantale \<subseteq>  wswq: dioid_one_zerol "(\<squnion>)" "(\<cdot>)" "1" "\<bottom>" "(\<le>)" "(<)"
  by (unfold_locales, simp_all add: sup_distl)

    
class quantale = proto_quantale + semigroup_mult 
  
begin
  
subclass weak_quantale ..   

lemma Inf_subdistl: "x \<cdot> \<Sqinter>Y \<le> (\<Sqinter>y \<in> Y. x \<cdot> y)"
  by (auto intro!: Inf_greatest Inf_lower mult_isol)

lemma Inf_subdistr: "\<Sqinter> X \<cdot> y \<le> (\<Sqinter>x \<in> X. x \<cdot> y)"
  by (auto intro!: Inf_greatest Inf_lower mult_isor)
    
lemma fres_bot_bot [simp]: "\<bottom> \<leftarrow> \<bottom> = \<top>"
  by (simp add: fres_def)

lemma bres_interchange: "(x \<rightarrow> y) \<cdot> z \<le> x \<rightarrow> (y \<cdot> z)"
  by (metis bres_canc1 bres_galois mult_isor mult_assoc)

lemma bres_curry: "x \<rightarrow> (y \<rightarrow> z) = (y \<cdot> x) \<rightarrow> z"
  by (metis bres_canc1 bres_galois dual_order.antisym mult_assoc)

lemma fres_bres: "x \<rightarrow> (y \<leftarrow> z) = (x \<rightarrow> y) \<leftarrow> z"
proof-
  {fix w
  have "(w \<le> x \<rightarrow> (y \<leftarrow> z)) = (x \<cdot> w \<le> y \<leftarrow> z)"
    by (simp add: bres_galois)
  also have "... = (x \<cdot> w \<cdot> z \<le> y)"
    by (simp add: fres_galois)
  also have "... = (w \<cdot> z \<le> x \<rightarrow> y)"
    by (simp add: bres_galois mult_assoc)
  also have "... = (w \<le> (x \<rightarrow> y) \<leftarrow> z)"
    by (simp add: fres_galois)
  finally have "(w \<le> x \<rightarrow> (y \<leftarrow> z)) = (w \<le> (x \<rightarrow> y) \<leftarrow> z)".}
  thus ?thesis
    using eq_iff by blast
qed

end

class quantale_with_dual = quantale + complete_lattice_with_dual

class unital_quantale = quantale + monoid_mult

class unital_quantale_with_dual = unital_quantale + quantale_with_dual
  
subclass (in unital_quantale) unital_weak_quantale ..

sublocale unital_quantale \<subseteq> wswq: dioid_one_zero "(\<squnion>)" "(\<cdot>)" "1" "\<bottom>" "(\<le>)" "(<)"
  by (unfold_locales, simp)

class ab_quantale = quantale + ab_semigroup_mult

begin

lemma bres_fres_eq: "x \<rightarrow> y = y \<leftarrow> x" 
  by (simp add: fres_def bres_def mult_commute)

end

class ab_unital_quantale = ab_quantale + unital_quantale

sublocale complete_heyting_algebra \<subseteq> chaq: ab_unital_quantale "(\<sqinter>)" _ _ _ _ _ _ _ _ \<top>
  by (unfold_locales, simp add: inf.assoc, simp_all add: inf.assoc ch_dist inf.commute)

class distrib_quantale = quantale + distrib_lattice
  
class bool_quantale = quantale + complete_boolean_algebra_alt 
  
class distrib_unital_quantale = unital_quantale + distrib_lattice
  
class bool_unital_quantale = unital_quantale + complete_boolean_algebra_alt
  
class distrib_ab_quantale = distrib_quantale + ab_quantale
  
class bool_ab_quantale = bool_quantale + ab_quantale
  
class distrib_ab_unital_quantale = distrib_quantale + unital_quantale
  
class bool_ab_unital_quantale = bool_ab_quantale + unital_quantale

sublocale complete_boolean_algebra \<subseteq> cba_quantale: bool_ab_unital_quantale inf _ _ _ _ _ _ _ _ _ _ \<top>
  by (unfold_locales, simp add: inf.assoc, simp_all add: inf.commute Setcompr_eq_image inf_Sup Sup_inf)

context complete_boolean_algebra
begin

text \<open>In this setting, residuation is classical implication.\<close>
  
lemma cba_bres1: "x \<sqinter> y \<le> z \<longleftrightarrow> x \<le> cba_quantale.bres y z"
  using cba_quantale.bres_galois inf.commute by fastforce
    
lemma cba_bres2: "x \<le> -y \<squnion> z \<longleftrightarrow> x \<le> cba_quantale.bres y z"
  using cba_bres1 shunt1 by auto
    
lemma cba_bres_prop: "cba_quantale.bres x y = -x \<squnion> y"
  using cba_bres2 eq_iff by blast
  
end

subsection \<open>Quantales Based on Sup-Lattices and Inf-Lattices\<close>

text \<open>These classes are defined for convenience in instantiation and interpretation proofs, or likewise. 
They are useful, e.g., in the context of predicate transformers, where only one of Sup or Inf may be well behaved.\<close>

class Sup_quantale = Sup_lattice + semigroup_mult + 
  assumes Supq_distr: "\<Squnion>X \<cdot> y = (\<Squnion>x \<in> X. x \<cdot> y)"
  and Supq_distl: "x \<cdot> \<Squnion>Y = (\<Squnion>y \<in> Y. x \<cdot> y)"

class unital_Sup_quantale = Sup_quantale + monoid_mult

class Inf_quantale = Inf_lattice + monoid_mult + 
  assumes Supq_distr: "\<Sqinter>X \<cdot> y = (\<Sqinter>x \<in> X. x \<cdot> y)"
  and Supq_distl: "x \<cdot> \<Sqinter>Y = (\<Sqinter>y \<in> Y. x \<cdot> y)"

class unital_Inf_quantale = Inf_quantale + monoid_mult

sublocale Inf_quantale \<subseteq> qdual: Sup_quantale _ Inf "(\<ge>)"
  by (unfold_locales, simp_all add: Supq_distr Supq_distl)

sublocale unital_Inf_quantale \<subseteq> uqdual: unital_Sup_quantale _ _ Inf  "(\<ge>)"..

sublocale Sup_quantale \<subseteq> supq: quantale _ Infs Sup_class.Sup infs "(\<le>)" le sups bots tops
  by (unfold_locales, simp_all add: Supq_distr Supq_distl)

sublocale unital_Sup_quantale \<subseteq> usupq: unital_quantale _ _ Infs Sup_class.Sup infs "(\<le>)" le sups bots tops..


subsection \<open>Products of Quantales\<close>
  
definition "Inf_prod X = ((\<Sqinter>x \<in> X. fst x), (\<Sqinter>x \<in> X. snd x))"
  
definition "inf_prod x y = (fst x \<sqinter> fst y, snd x \<sqinter> snd y)"

definition "bot_prod = (bot,bot)"
  
definition "Sup_prod X = ((\<Squnion>x \<in> X. fst x), (\<Squnion>x \<in> X. snd x))"
    
definition "sup_prod x y = (fst x \<squnion> fst y, snd x \<squnion> snd y)"
    
definition "top_prod = (top,top)"
    
definition "less_eq_prod x y \<equiv> less_eq (fst x) (fst y) \<and> less_eq (snd x) (snd y)"

definition "less_prod x y \<equiv> less_eq (fst x) (fst y) \<and> less_eq (snd x) (snd y) \<and> x \<noteq> y"
  
definition "times_prod' x y = (fst x \<cdot> fst y, snd x \<cdot> snd y)"

definition "one_prod = (1,1)"

definition "dual_prod x = (\<partial> (fst x),\<partial> (snd x))"
  
interpretation prod: complete_lattice Inf_prod Sup_prod inf_prod less_eq_prod less_prod sup_prod bot_prod "top_prod :: ('a::complete_lattice \<times> 'b::complete_lattice)"
  by standard (auto simp add: Inf_prod_def Sup_prod_def inf_prod_def sup_prod_def bot_prod_def top_prod_def less_eq_prod_def less_prod_def Sup_distl Sup_distr intro: Inf_lower Inf_greatest Sup_upper Sup_least)

interpretation prod: complete_lattice_with_dual Inf_prod Sup_prod inf_prod less_eq_prod less_prod sup_prod bot_prod "top_prod :: ('a::complete_lattice_with_dual \<times> 'b::complete_lattice_with_dual)" dual_prod
  by standard (simp_all add: dual_prod_def fun_eq_iff inj_def Sup_prod_def Inf_prod_def inj_dual_iff Sup_dual_def_var image_comp)

interpretation prod: proto_near_quantale Inf_prod Sup_prod inf_prod less_eq_prod less_prod sup_prod bot_prod "top_prod :: ('a::proto_near_quantale \<times> 'b::proto_near_quantale)" times_prod'
  by standard (simp add: times_prod'_def Sup_prod_def Sup_distr image_comp)

interpretation prod: proto_quantale Inf_prod Sup_prod inf_prod less_eq_prod less_prod sup_prod bot_prod "top_prod :: ('a::proto_quantale \<times> 'b::proto_quantale)" times_prod'
  by standard (simp add: times_prod'_def Sup_prod_def less_eq_prod_def Sup_distl image_comp)

interpretation prod: unital_quantale one_prod times_prod' Inf_prod Sup_prod inf_prod less_eq_prod less_prod sup_prod bot_prod "top_prod :: ('a::unital_quantale \<times> 'b::unital_quantale)" 
  by standard (simp_all add: one_prod_def times_prod'_def ac_simps image_comp)


subsection \<open>Quantale Morphisms\<close>

text \<open>There are various ways of defining quantale morphisms, depending on the application. Following Rosenthal, 
I present the most important one.\<close>

abbreviation comp_pres :: "('a::times \<Rightarrow> 'b::times) \<Rightarrow> bool" where
  "comp_pres f \<equiv> (\<forall>x y. f (x \<cdot> y) = f x \<cdot> f y)"

abbreviation un_pres :: "('a::one \<Rightarrow> 'b::one) \<Rightarrow> bool" where
  "un_pres f \<equiv> (f 1 = 1)"

definition "comp_closed_set X = (\<forall>x \<in> X. \<forall>y \<in> X. x \<cdot> y \<in> X)" 

definition "un_closed_set X = (1 \<in> X)" 

definition quantale_homset :: "('a::quantale \<Rightarrow> 'b::quantale) set" where
  "quantale_homset = {f. comp_pres f \<and> Sup_pres f}"

lemma quantale_homset_iff: "f \<in> quantale_homset = (comp_pres f \<and> Sup_pres f)"
  unfolding quantale_homset_def by clarsimp

definition unital_quantale_homset :: "('a::unital_quantale \<Rightarrow> 'b::unital_quantale) set" where
  "unital_quantale_homset = {f. comp_pres f \<and> Sup_pres f \<and> un_pres f}"

lemma unital_quantale_homset_iff: "f \<in> unital_quantale_homset = (comp_pres f \<and> Sup_pres f \<and> un_pres f)"
  unfolding unital_quantale_homset_def by clarsimp

text \<open>Though Infs can be defined from Sups in any quantale, quantale morphisms do not generally preserve Infs.
A different kind of morphism is needed if this is to be guaranteed.\<close>

lemma "f \<in> quantale_homset \<Longrightarrow> Inf_pres f" (*nitpick*)
  oops

text \<open>The images of quantale morphisms are closed under compositions and Sups, hence they form quantales.\<close>

lemma quantale_hom_q_pres: "f \<in> quantale_homset \<Longrightarrow> Sup_closed_set (range f) \<and> comp_closed_set (range f)"
  apply safe
   apply (simp add: Sup_pres_Sup_closed quantale_homset_iff)
  unfolding quantale_homset_iff comp_closed_set_def by (metis (no_types, lifting) imageE range_eqI) 

text \<open>Yet the image need not be Inf-closed.\<close>

lemma "f \<in> quantale_homset \<Longrightarrow> Inf_closed_set (range f)" (*nitpick*)
  oops

text \<open>Of course Sups are preserved by quantale-morphisms, hence they are the same in subsets as in the original set.
Infs in the subset, however, exist, since they subset forms a quantale in which Infs can be defined, but these are generally
different from the Infs in the superstructure. 

This fact is hidden in Isabelle's definition of complete lattices, where Infs are axiomatised. There is no easy way in general to
show that images of quantale morphisms form quantales, though the statement for Sup-quantales is straightforward. I show this for quantic nuclei 
and left-sided elements.\<close>

typedef (overloaded) ('a,'b) quantale_homset = "quantale_homset::('a::quantale \<Rightarrow> 'b::quantale) set"
proof-
  have a: "comp_pres (\<lambda>x::'a::quantale. bot::'b)"
    by simp
  have b: "Sup_pres (\<lambda>x::'a::quantale. bot::'b)"
    unfolding fun_eq_iff comp_def by simp
  hence "(\<lambda>x::'a::quantale. bot::'b) \<in> quantale_homset"
    by (simp add: quantale_homset_iff)
  thus ?thesis
    by auto
qed

setup_lifting type_definition_quantale_homset

text \<open>Interestingly, the following type is not (gobally) inhabited.\<close>

typedef (overloaded) ('a,'b) unital_quantale_homset = "unital_quantale_homset::('a::unital_quantale \<Rightarrow> 'b::unital_quantale) set" (*nitpick*)
  oops

lemma quantale_hom_radj: 
  fixes f :: "'a::quantale_with_dual \<Rightarrow> 'b::quantale_with_dual"
  shows "f \<in> quantale_homset \<Longrightarrow> f \<stileturn> radj f"
  unfolding quantale_homset_iff by (simp add: Sup_pres_ladj_aux)

lemma quantale_hom_prop1: 
  fixes f :: "'a::quantale_with_dual \<Rightarrow> 'b::quantale_with_dual"
  shows "f \<in> quantale_homset \<Longrightarrow> radj f (f x \<rightarrow> y) = x \<rightarrow> radj f y"
proof-
  assume h: "f \<in> quantale_homset"
  have "f x \<cdot> f (radj f (f x \<rightarrow> y)) \<le> y"
    by (meson h adj_def bres_galois order_refl quantale_hom_radj)
  hence "f (x \<cdot> radj f (f x \<rightarrow> y)) \<le> y"
    by (metis h quantale_homset_iff)
  hence "x \<cdot> radj f (f x \<rightarrow> y) \<le> radj f y"
    using adj_def h quantale_hom_radj by blast
  hence le: "radj f (f x \<rightarrow> y) \<le> x \<rightarrow> radj f y"
    by (simp add: bres_galois)
  have "x \<cdot> (x \<rightarrow> radj f y) \<le> radj f y"
    by (simp add: bres_canc1)
  hence  "f (x \<cdot> (x \<rightarrow> radj f y)) \<le> y"
    using adj_def h quantale_hom_radj by blast
  hence "f x \<cdot> f (x \<rightarrow> radj f y) \<le> y"
    by (metis h quantale_homset_iff)
  hence "f (x \<rightarrow> radj f y) \<le> f x \<rightarrow> y"
    by (simp add: bres_galois)
  hence "x \<rightarrow> radj f y \<le> radj f (f x \<rightarrow> y)"
    using adj_def h quantale_hom_radj by blast
  thus ?thesis
    by (simp add: dual_order.antisym le)
qed

lemma quantale_hom_prop2: 
  fixes f :: "'a::quantale_with_dual \<Rightarrow> 'b::quantale_with_dual"
  shows "f \<in> quantale_homset \<Longrightarrow> radj f (y \<leftarrow> f x) = radj f y \<leftarrow> x"
proof-
  assume h: "f \<in> quantale_homset"
  have "f (radj f (y \<leftarrow> f x)) \<cdot> f x \<le> y"
    by (meson adj_def fres_galois h order_refl quantale_hom_radj)
  hence "f (radj f (y \<leftarrow> f x) \<cdot> x) \<le> y"
    by (metis h quantale_homset_iff)
  hence "radj f (y \<leftarrow> f x) \<cdot> x\<le> radj f y"
    using adj_def h quantale_hom_radj by blast
  hence le: "radj f (y \<leftarrow> f x) \<le> radj f y \<leftarrow> x"
    by (simp add: fres_galois)
  have "(radj f y \<leftarrow> x) \<cdot> x \<le> radj f y"
    by (simp add: fres_canc1)
  hence  "f ((radj f y \<leftarrow> x) \<cdot> x) \<le> y"
    using adj_def h quantale_hom_radj by blast
  hence "f (radj f y \<leftarrow> x) \<cdot> f x\<le> y"
    by (metis h quantale_homset_iff)
  hence "f (radj f y \<leftarrow> x) \<le> y \<leftarrow> f x"
    by (simp add: fres_galois)
  hence "radj f y \<leftarrow> x\<le> radj f (y \<leftarrow> f x)"
    using adj_def h quantale_hom_radj by blast
  thus ?thesis
    by (simp add: dual_order.antisym le)
qed

definition quantale_closed_maps :: "('a::quantale \<Rightarrow> 'b::quantale) set" where
  "quantale_closed_maps = {f. (\<forall>x y. f x \<cdot> f y \<le> f (x \<cdot> y))}"

lemma quantale_closed_maps_iff: "f \<in> quantale_closed_maps = (\<forall> x y. f x \<cdot> f y \<le> f (x \<cdot> y))"
  unfolding quantale_closed_maps_def by clarsimp

definition quantale_closed_Sup_maps :: "('a::quantale \<Rightarrow> 'b::quantale) set" where
  "quantale_closed_Sup_maps = {f. (\<forall> x y. f x \<cdot> f y \<le> f (x \<cdot> y)) \<and> Sup_pres f}"

lemma quantale_closed_Sup_maps_iff: "f \<in> quantale_closed_Sup_maps = (\<forall> x y. f x \<cdot> f y \<le> f (x \<cdot> y) \<and> Sup_pres f)"
  unfolding quantale_closed_Sup_maps_def by clarsimp

definition quantale_closed_unital_maps :: "('a::unital_quantale \<Rightarrow> 'b::unital_quantale) set" where
  "quantale_closed_unital_maps = {f. (\<forall> x y. f x \<cdot> f y \<le> f (x \<cdot> y)) \<and> 1 \<le> f 1}"

lemma quantale_closed_unital_maps_iff: "f \<in> quantale_closed_unital_maps = (\<forall> x y. f x \<cdot> f y \<le> f (x \<cdot> y) \<and> 1 \<le> f 1)"
  unfolding quantale_closed_unital_maps_def by clarsimp

definition quantale_closed_unital_Sup_maps :: "('a::unital_quantale \<Rightarrow> 'b::unital_quantale) set" where
  "quantale_closed_unital_Sup_maps = {f. (\<forall> x y. f x \<cdot> f y \<le> f (x \<cdot> y)) \<and> Sup_pres f \<and> 1 \<le> f 1}"

lemma quantale_closed_unital_Sup_maps_iff: "f \<in> quantale_closed_unital_Sup_maps = (\<forall> x y. f x \<cdot> f y \<le> f (x \<cdot> y) \<and> Sup_pres f \<and> 1 \<le> f 1)"
  unfolding quantale_closed_unital_Sup_maps_def by clarsimp

text \<open>Closed maps are the right adjoints of quantale morphisms.\<close>

lemma quantale_hom_closed_map:
  fixes f :: "'a::quantale_with_dual \<Rightarrow> 'b::quantale_with_dual"
  shows "(f \<in> quantale_homset) \<Longrightarrow> (radj f \<in> quantale_closed_maps)"
proof-
  assume h: "f \<in> quantale_homset"
  have "\<forall>x y. f (radj f x) \<cdot> f (radj f y) \<le> x \<cdot> y"
    by (metis adj_def h order_refl psrpq.mult_isol_var quantale_hom_radj) 
  hence "\<forall>x y. f (radj f x \<cdot> radj f y) \<le> x \<cdot> y"
    by (metis h quantale_homset_iff)
  hence "\<forall>x y. radj f x \<cdot> radj f y \<le> radj f (x \<cdot> y)"
    using adj_def h quantale_hom_radj by blast
  thus ?thesis
    by (simp add: quantale_closed_maps_iff)
qed

lemma unital_quantale_hom_closed_unital_map:
  fixes f :: "'a::unital_quantale_with_dual \<Rightarrow> 'b::unital_quantale_with_dual"
  shows "(f \<in> unital_quantale_homset) \<Longrightarrow> (radj f \<in> quantale_closed_unital_maps)"
  by (metis (no_types, hide_lams) adj_def order_refl quantale_closed_maps_iff quantale_closed_unital_maps_iff quantale_hom_closed_map quantale_hom_radj quantale_homset_iff unital_quantale_homset_iff)

 end


  
