(* Title: Quantales
   Author: Brijesh Dongol, Victor Gomes, Ian J Hayes, Georg Struth
   Maintainer: Victor Gomes <victor.gomes@cl.cam.ac.uk>
               Georg Struth <g.struth@sheffield.ac.uk> 
*)

section \<open>Quantales\<close>
  
text \<open>This entry will be merged eventually with other quantale entries and become a standalone one.\<close>
  
theory Quantales
  imports Main

begin
  
notation sup (infixl "\<squnion>" 60)
  and inf (infixl "\<sqinter>" 55)
  and top ("\<top>")
  and bot ("\<bottom>")
  and relcomp (infixl ";" 70) 
  and times (infixl "\<cdot>" 70)
  and Sup ("\<Squnion>_" [900] 900)  
  and Inf ("\<Sqinter>_" [900] 900)
  
subsection \<open>Properties of Complete Lattices\<close>
  
lemma (in complete_lattice) Sup_sup_pred: "x \<squnion> \<Squnion>{y. P y} = \<Squnion>{y. y = x \<or> P y}"
  apply (rule antisym)
   apply (simp add: Collect_mono Sup_subset_mono Sup_upper)
  using Sup_least Sup_upper sup.coboundedI2 by force

lemma (in complete_lattice) sup_Sup: "x \<squnion> y = \<Squnion>{x,y}"
  by simp
    
lemma (in complete_lattice) sup_Sup_var: "x \<squnion> y = \<Squnion>{z. z \<in> {x,y}}"
  by (metis Collect_mem_eq sup_Sup)
    
lemma (in complete_boolean_algebra) shunt1: "x \<sqinter> y \<le> z \<longleftrightarrow> x \<le> -y \<squnion> z"
proof standard
  assume "x \<sqinter> y \<le> z"
  hence  "-y \<squnion> (x \<sqinter> y) \<le> -y \<squnion> z"
    using sup.mono by blast
  hence "-y \<squnion> x \<le> -y \<squnion> z"
    by (simp add: sup_inf_distrib1)
  thus "x \<le> -y \<squnion> z"
    by simp
next
  assume "x \<le> - y \<squnion> z"
  hence "x \<sqinter> y \<le> (-y \<squnion> z) \<sqinter> y"
    using inf_mono by auto
  thus  "x \<sqinter> y \<le> z"
    using inf.boundedE inf_sup_distrib2 by auto
qed
  
lemma (in complete_boolean_algebra) meet_shunt: "x \<sqinter> y = \<bottom> \<longleftrightarrow> x \<le> -y"
  by (metis bot_least inf_absorb2 inf_compl_bot_left2 shunt1 sup_absorb1)
  
lemma (in complete_boolean_algebra) join_shunt: "x \<squnion> y = \<top> \<longleftrightarrow> -x \<le> y"
  by (metis compl_sup compl_top_eq double_compl meet_shunt)
    

subsection \<open> Familes of Proto-Quantales\<close>
  
text \<open>Proto-Quanales are complete lattices equipped with an operation of composition or multiplication
that need not be associative.\<close>
  
class proto_near_quantale = complete_lattice + times + 
  assumes Sup_distr: "\<Squnion>X \<cdot> y = \<Squnion>{x \<cdot> y |x. x \<in> X}"
    
begin
  
lemma mult_botl [simp]: "\<bottom> \<cdot> x = \<bottom>"
  using Sup_distr[where X="{}"] by auto
  
lemma sup_distr: "(x \<squnion> y) \<cdot> z = (x \<cdot> z) \<squnion> (y \<cdot> z)"
  using Sup_distr[where X="{x, y}"] by (fastforce intro!: Sup_eqI)
    
lemma mult_isor: "x \<le> y \<Longrightarrow> x \<cdot> z \<le> y \<cdot> z"
  by (metis sup.absorb_iff1 sup_distr)
    
definition bres :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixr "\<rightarrow>" 60) where 
  "x \<rightarrow> z = \<Squnion>{y. x \<cdot> y \<le> z}"

definition fres :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<leftarrow>" 60) where 
  "z \<leftarrow> y = \<Squnion>{x. x \<cdot> y \<le> z}"

lemma bres_galois_imp: "x \<cdot> y \<le> z \<longrightarrow> y \<le> x \<rightarrow> z"
  by (simp add: Sup_upper bres_def)
    
lemma fres_galois: "x \<cdot> y \<le> z \<longleftrightarrow> x \<le> z \<leftarrow> y"
proof 
  show "x \<cdot> y \<le> z \<Longrightarrow> x \<le> z \<leftarrow> y"
    by (simp add: Sup_upper fres_def)
next
  assume "x \<le> z \<leftarrow> y"
  hence "x \<cdot> y \<le> \<Squnion>{x. x \<cdot> y \<le> z} \<cdot> y"
    by (simp add: fres_def mult_isor)
  also have "... = \<Squnion>{x \<cdot> y |x. x \<cdot> y \<le> z}"
    by (simp add: Sup_distr)
  also have "... \<le> z"
    by (rule Sup_least, auto)
  finally show "x \<cdot> y \<le> z" .
qed
  
end
  
class proto_pre_quantale = proto_near_quantale + 
  assumes Sup_subdistl: "\<Squnion>{x \<cdot> y | y . y \<in> Y} \<le> x \<cdot> \<Squnion>Y"
    
begin

lemma sup_subdistl: "(x \<cdot> y) \<squnion> (x \<cdot> z) \<le> x \<cdot> (y \<squnion> z)"
  using Sup_subdistl[where Y="{y, z}"] Sup_le_iff by auto

lemma mult_isol: "x \<le> y \<Longrightarrow> z \<cdot> x \<le> z \<cdot> y"
  by (metis le_iff_sup le_sup_iff sup_subdistl)

end
    
class weak_proto_quantale = proto_near_quantale +
  assumes weak_Sup_distl: "Y \<noteq> {} \<Longrightarrow> x \<cdot> \<Squnion>Y = \<Squnion>{x \<cdot> y |y. y \<in> Y}" 
  
begin

subclass proto_pre_quantale
proof standard
  have a: "\<And>x Y. Y = {} \<Longrightarrow> \<Squnion>{x \<cdot> y |y. y \<in> Y} \<le> x \<cdot> \<Squnion>Y"
    by simp
  have b: "\<And>x Y. Y \<noteq> {} \<Longrightarrow> \<Squnion>{x \<cdot> y |y. y \<in> Y} \<le> x \<cdot> \<Squnion>Y"
    by (simp add: weak_Sup_distl)
  show  "\<And>x Y. \<Squnion>{x \<cdot> y |y. y \<in> Y} \<le> x \<cdot> \<Squnion>Y"
    using a b by blast 
qed
  
lemma  sup_distl: "x \<cdot> (y \<squnion> z) = (x \<cdot> y) \<squnion> (x \<cdot> z)"  
  using weak_Sup_distl[where Y="{y, z}"] by (fastforce intro!: Sup_eqI)

lemma "y \<le> x \<rightarrow> z \<longrightarrow> x \<cdot> y \<le> z" (* nitpick [expect = genuine] *)
oops

end
  
class proto_quantale = proto_near_quantale +
  assumes Sup_distl: "x \<cdot> \<Squnion>Y = \<Squnion>{x \<cdot> y |y. y \<in> Y}"  

begin
  
subclass weak_proto_quantale
  by standard (simp add: Sup_distl)
    
lemma bres_galois: "x \<cdot> y \<le> z \<longleftrightarrow> y \<le> x \<rightarrow> z"
proof 
  show "x \<cdot> y \<le> z \<Longrightarrow> y \<le> x \<rightarrow> z"
    by (simp add: Sup_upper bres_def)
next
  assume "y \<le> x \<rightarrow> z"
  hence "x \<cdot> y \<le> x \<cdot> \<Squnion>{y. x \<cdot> y \<le> z}"
    by (simp add: bres_def mult_isol)
  also have "... = \<Squnion>{x \<cdot> y |y. x \<cdot> y \<le> z}"
    by (simp add: Sup_distl)
  also have "... \<le> z"
    by (rule Sup_least, auto)
  finally show "x \<cdot> y \<le> z" .
qed

end 
  
  
subsection \<open>Families of Quantales\<close>
  
class near_quantale = proto_near_quantale + semigroup_mult 
  
class unital_near_quantale = near_quantale + monoid_mult

begin

definition iter :: "'a \<Rightarrow> 'a" where
  "iter x \<equiv> \<Sqinter>{y. \<exists>i. y = x ^ i}"

lemma iter_ref [simp]: "iter x \<le> 1"
  apply (simp add: iter_def)
  by (metis (mono_tags, lifting) Inf_lower local.power.power_0 mem_Collect_eq)
    
lemma le_top: "x \<le> \<top> \<cdot> x"
  by (metis mult_isor mult.monoid_axioms top_greatest monoid.left_neutral)

end
  
class pre_quantale = proto_pre_quantale + semigroup_mult 
  
subclass (in pre_quantale) near_quantale ..
  
class unital_pre_quantale = pre_quantale + monoid_mult
  
subclass (in unital_pre_quantale) unital_near_quantale ..
    
class weak_quantale = weak_proto_quantale + semigroup_mult
  
subclass (in weak_quantale) pre_quantale ..
    
text \<open>The following counterexample shows an important consequence of weakness: 
the absence of right annihilation.\<close>
    
lemma (in weak_quantale) "x \<cdot> \<bottom> = \<bottom>" (*nitpick[expect=genuine]*)
  oops
    
class unital_weak_quantale = weak_quantale + monoid_mult
  
lemma (in unital_weak_quantale) "x \<cdot> \<bottom> = \<bottom>" (*nitpick[expect=genuine]*)
  oops
  
subclass (in unital_weak_quantale) unital_pre_quantale ..
    
class quantale = proto_quantale + semigroup_mult 
  
begin
  
subclass weak_quantale ..   

lemma mult_botr [simp]: "x \<cdot> \<bottom> = \<bottom>"
  using Sup_distl[where Y="{}"] by auto

end
  
class unital_quantale = quantale + monoid_mult

subclass (in unital_quantale) unital_weak_quantale ..

class ab_quantale = quantale + ab_semigroup_mult

begin

lemma bres_fres_eq: "x \<rightarrow> y = y \<leftarrow> x" 
  by (simp add: fres_def bres_def mult_commute)

end

class ab_unital_quantale = ab_quantale + unital_quantale
  
class distrib_quantale = quantale + complete_distrib_lattice
  
class bool_quantale = quantale + complete_boolean_algebra 
  
class distrib_unital_quantale = unital_quantale + complete_distrib_lattice
  
class bool_unital_quantale = unital_quantale + complete_boolean_algebra 
  
class distrib_ab_quantale = distrib_quantale + ab_quantale
  
class bool_ab_quantale = bool_quantale + ab_quantale
  
class distrib_ab_unital_quantale = distrib_quantale + unital_quantale
  
class bool_ab_unital_quantale = bool_ab_quantale + unital_quantale
  
  
subsection \<open>Quantales of Booleans and Complete Boolean Algebras\<close>
  
instantiation bool :: bool_ab_unital_quantale
begin
  
definition "one_bool = True"
  
definition "times_bool = (\<lambda>x y. x \<and> y)"
  
instance
  by standard (auto simp: times_bool_def one_bool_def)
    
end
  
context complete_distrib_lattice
begin
  
interpretation cdl_quantale: distrib_quantale _ _ _ _ _ _ _ _ inf
  by standard (simp_all add: inf.assoc Setcompr_eq_image Sup_inf inf_Sup)
    
end

context complete_boolean_algebra
begin

interpretation cba_quantale: bool_ab_unital_quantale inf _ _ _ _ _ _ _ _ _ _ top
  apply standard
  apply (simp add: inf.assoc)
  apply (simp add: inf.commute)
  apply (simp add: Setcompr_eq_image Sup_inf)
  apply (simp add: Setcompr_eq_image inf_Sup)
  by simp_all
    
text \<open>In this setting, residuation can be translated like classical implication.\<close>
  
lemma cba_bres1: "x \<sqinter> y \<le> z \<longleftrightarrow> x \<le> cba_quantale.bres y z"
  using cba_quantale.bres_galois inf.commute by fastforce
    
lemma cba_bres2: "x \<le> -y \<squnion> z \<longleftrightarrow> x \<le> cba_quantale.bres y z"
  using cba_bres1 shunt1 by auto
    
lemma cba_bres_prop: "cba_quantale.bres x y = -x \<squnion> y"
  using cba_bres2 eq_iff by blast
  
end
  
text \<open>Other models will follow.\<close>
  
   
subsection \<open>Products of Quantales\<close>
  
definition "Inf_prod X = (\<Sqinter>{fst x |x. x \<in> X}, \<Sqinter>{snd x |x.  x \<in> X})"
  
definition "inf_prod x y = (fst x \<sqinter> fst y, snd x \<sqinter> snd y)"

definition "bot_prod = (bot,bot)"
  
definition "Sup_prod X = (\<Squnion>{fst x |x. x \<in> X}, \<Squnion>{snd x |x.  x \<in> X})"
    
definition "sup_prod x y = (fst x \<squnion> fst y, snd x \<squnion> snd y)"
    
definition "top_prod = (top,top)"
    
definition "less_eq_prod x y \<equiv> less_eq (fst x) (fst y) \<and> less_eq (snd x) (snd y)"

definition "less_prod x y \<equiv> less_eq (fst x) (fst y) \<and> less_eq (snd x) (snd y) \<and> x \<noteq> y"
  
definition "times_prod' x y = (fst x \<cdot> fst y, snd x \<cdot> snd y)"

definition "one_prod = (1,1)"
  
interpretation prod: complete_lattice Inf_prod Sup_prod inf_prod less_eq_prod less_prod sup_prod bot_prod "top_prod :: ('a::complete_lattice \<times> 'b::complete_lattice)"
  apply standard
     apply (simp_all add: Inf_prod_def Sup_prod_def inf_prod_def sup_prod_def bot_prod_def top_prod_def less_eq_prod_def less_prod_def Sup_distl Sup_distr)
        apply force+
     apply (rule conjI, (rule Inf_lower, force)+)
    apply (rule conjI, (rule Inf_greatest, force)+)
   apply (rule conjI, (rule Sup_upper, force)+)
  by (rule conjI, (rule Sup_least, force)+)

interpretation prod: proto_near_quantale Inf_prod Sup_prod inf_prod less_eq_prod less_prod sup_prod bot_prod "top_prod :: ('a::proto_near_quantale \<times> 'b::proto_near_quantale)" times_prod'
  apply (standard, simp add: times_prod'_def Sup_prod_def)
  by (rule conjI, (simp add: Sup_distr, clarify, metis)+)
    
interpretation prod: proto_quantale Inf_prod Sup_prod inf_prod less_eq_prod less_prod sup_prod bot_prod "top_prod :: ('a::proto_quantale \<times> 'b::proto_quantale)" times_prod'
  apply (standard, simp add: times_prod'_def Sup_prod_def less_eq_prod_def)
  by (rule conjI, (simp add: Sup_distl, metis)+)

interpretation prod: unital_quantale one_prod times_prod' Inf_prod Sup_prod inf_prod less_eq_prod less_prod sup_prod bot_prod "top_prod :: ('a::unital_quantale \<times> 'b::unital_quantale)" 
  by standard (simp_all add: one_prod_def times_prod'_def mult.assoc)
    

subsection \<open>Quantale Modules and Semidirect Products\<close>
  
text \<open>Quantale modules are extensions of semigroup actions in that a quantale acts on a complete lattice.\<close>
  
locale unital_quantale_module = 
  fixes act :: "'a::unital_quantale \<Rightarrow> 'b::complete_lattice \<Rightarrow> 'b" ("\<alpha>")
  assumes act1: "\<alpha> (x \<cdot> y) p = \<alpha> x (\<alpha> y p)"
    and act2 [simp]: "\<alpha> 1 p = p" 
    and act3: "\<alpha> (\<Squnion>X) p = \<Squnion>{\<alpha> x p |x. x \<in> X}"
    and act4: "\<alpha> x (\<Squnion>P) = \<Squnion>{\<alpha> x p |p. p \<in> P}"

context unital_quantale_module
begin
  
text \<open>Actions are morphisms. The curried notation is particularly convenient for this.\<close>
  
lemma act_morph1: "\<alpha> (x \<cdot> y) = (\<alpha> x) \<circ> (\<alpha> y)"
  by (simp add: fun_eq_iff act1)
    
lemma act_morph2: "\<alpha> 1 = id"
  by (simp add: fun_eq_iff)
  
lemma emp_act: "\<alpha> (\<Squnion>{}) p = \<bottom>"
  by (simp only: act3, force)
    
lemma emp_act_var: "\<alpha> \<bottom> p = \<bottom>"
  using emp_act by auto

lemma act_emp: "\<alpha> x (\<Squnion>{}) = \<bottom>"
  by (simp only: act4, force)
    
lemma act_emp_var: "\<alpha> x \<bottom> = \<bottom>"
  using act_emp by auto
  
lemma act_sup_distl: "\<alpha> x (p \<squnion> q) = (\<alpha> x p) \<squnion> (\<alpha> x q)"
proof-
  have "\<alpha> x (p \<squnion> q) = \<alpha> x (\<Squnion>{p,q})"
    by simp
  also have "... = \<Squnion>{\<alpha> x y |y. y \<in> {p,q}}"
    by (rule act4)
  also have "... = \<Squnion>{v. v = \<alpha> x p \<or> v = \<alpha> x q}"
    by (metis empty_iff insert_iff)
  finally show ?thesis
    by (metis Collect_disj_eq Sup_insert ccpo_Sup_singleton insert_def singleton_conv)
qed
  
lemma act_sup_distr: "\<alpha> (x \<squnion> y) p = (\<alpha> x p) \<squnion> (\<alpha> y p)"
  proof-
  have "\<alpha> (x \<squnion> y) p  = \<alpha> (\<Squnion>{x,y}) p"
    by simp
  also have "... = \<Squnion>{\<alpha> v p |v. v \<in> {x,y}}"
    by (rule act3)
  also have "... = \<Squnion>{v. v = \<alpha> x p \<or> v = \<alpha> y p}"
    by (metis empty_iff insert_iff)
  finally show ?thesis
    by (metis Collect_disj_eq Sup_insert ccpo_Sup_singleton insert_def singleton_conv)
qed
  
lemma act_sup_distr_var: "\<alpha> (x \<squnion> y) = (\<alpha> x) \<squnion> (\<alpha> y)"
  by (simp add: fun_eq_iff act_sup_distr)
    
text \<open>Next we define the semidirect product of a  unital quantale and a complete lattice. \<close>
  
definition "sd_prod x y = (fst x \<cdot> fst y, snd x \<squnion> \<alpha> (fst x) (snd y))"
   
lemma sd_distr_aux: 
  "\<Squnion>{snd x |x. x \<in> X} \<squnion> \<Squnion>{\<alpha> (fst x) p |x. x \<in> X} = \<Squnion>{snd x \<squnion> \<alpha> (fst x) p |x. x \<in> X}"
proof (rule antisym, rule sup_least) 
  show "\<Squnion>{snd x |x. x \<in> X} \<le> \<Squnion>{snd x \<squnion> \<alpha> (fst x) p |x. x \<in> X}"
  proof (rule Sup_least)
    fix x :: 'b
    assume "x \<in> {snd x |x. x \<in> X}"
    hence "\<exists>b pa. x \<squnion> b = snd pa \<squnion> \<alpha> (fst pa) p \<and> pa \<in> X"
      by blast
    hence "\<exists>b. x \<squnion> b \<in> {snd pa \<squnion> \<alpha> (fst pa) p |pa. pa \<in> X}"
      by blast
    thus "x \<le> \<Squnion>{snd pa \<squnion> \<alpha> (fst pa) p |pa. pa \<in> X}"
      by (meson Sup_upper sup.bounded_iff)
  qed  
next
  show "\<Squnion>{\<alpha> (fst x) p |x. x \<in> X} \<le> \<Squnion>{snd x \<squnion> \<alpha> (fst x) p |x. x \<in> X}"
  proof (rule Sup_least)
    fix x :: 'b
    assume "x \<in> {\<alpha> (fst x) p |x. x \<in> X}"
    then have "\<exists>b pa. b \<squnion> x = snd pa \<squnion> \<alpha> (fst pa) p \<and> pa \<in> X"
      by blast
    then have "\<exists>b. b \<squnion> x \<in> {snd pa \<squnion> \<alpha> (fst pa) p |pa. pa \<in> X}"
      by blast
    then show "x \<le> \<Squnion>{snd pa \<squnion> \<alpha> (fst pa) p |pa. pa \<in> X}"
      by (meson Sup_upper le_supE)
  qed
next
  show "\<Squnion>{snd x \<squnion> \<alpha> (fst x) p |x. x \<in> X} \<le> \<Squnion>{snd x |x. x \<in> X} \<squnion> \<Squnion>{\<alpha> (fst x) p |x. x \<in> X}"
    apply (rule Sup_least)
    apply safe 
    apply (rule sup_least)
    apply (metis (mono_tags, lifting) Sup_upper mem_Collect_eq sup.coboundedI1)
    by (metis (mono_tags, lifting) Sup_upper mem_Collect_eq sup.coboundedI2)
qed

lemma sd_distr: "sd_prod (Sup_prod X) y = Sup_prod {sd_prod x y |x. x \<in> X}"
proof -
  have "sd_prod (Sup_prod X) y = sd_prod (\<Squnion>{fst x |x. x \<in> X}, \<Squnion>{snd x |x. x \<in> X}) y"
    by (simp add: Sup_prod_def)
  also have 
    "... = ((\<Squnion>{fst x |x. x \<in> X}) \<cdot> fst y, (\<Squnion>{snd x |x. x \<in> X}) \<squnion> (\<alpha> (\<Squnion>{fst x | x. x \<in> X})  (snd y)))"
    by (simp add: sd_prod_def)
  also have 
    "... = (\<Squnion>{fst x \<cdot> fst y|x. x \<in> X}, (\<Squnion>{snd x |x. x \<in> X}) \<squnion> (\<alpha> (\<Squnion>{fst x | x. x \<in> X})  (snd y)))"
    by (simp add: Sup_distr)
  also have 
    "... = (\<Squnion>{fst x \<cdot> fst y|x. x \<in> X}, (\<Squnion> {snd x |x. x \<in> X}) \<squnion> (\<Squnion>{\<alpha> (fst x) (snd y) | x. x \<in> X}))"
    by (simp add: act3)
  also have "... = (\<Squnion>{fst x \<cdot> fst y|x. x \<in> X}, \<Squnion>{snd x \<squnion> (\<alpha> (fst x) (snd y)) | x. x \<in> X})"
    by (simp only: sd_distr_aux)
  also have "... = Sup_prod {(fst x \<cdot> fst y, snd x \<squnion> (\<alpha> (fst x) (snd y))) |x. x \<in> X}"
    by (simp add: Sup_prod_def, metis)
  finally show ?thesis
    by (simp add: sd_prod_def)
qed
  
lemma sd_distl_aux: "Y \<noteq> {} \<Longrightarrow> p \<squnion> (\<Squnion>{\<alpha> x (snd y) |y. y \<in> Y}) = \<Squnion>{p \<squnion> \<alpha> x (snd y) |y. y \<in> Y}"
proof (rule antisym, rule sup_least)
  show "Y \<noteq> {} \<Longrightarrow> p \<le> \<Squnion>{p \<squnion> \<alpha> x (snd y) |y. y \<in> Y}"
  proof -
    assume "Y \<noteq> {}"
    hence "\<exists>b. b \<in> {p \<squnion> \<alpha> x (snd pa) |pa. pa \<in> Y} \<and> p \<le> b"
      by fastforce
    thus "p \<le> \<Squnion>{p \<squnion> \<alpha> x (snd pa) |pa. pa \<in> Y}"
      by (meson Sup_upper2)
  qed
next
  show "Y \<noteq> {} \<Longrightarrow> \<Squnion>{\<alpha> x (snd y) |y. y \<in> Y} \<le> \<Squnion>{p \<squnion> \<alpha> x (snd y) |y. y \<in> Y}"  
    apply (rule Sup_least)
  proof -
    fix xa :: 'b
    assume "xa \<in> {\<alpha> x (snd y) |y. y \<in> Y}"
    then have "\<exists>b. (\<exists>pa. b = p \<squnion> \<alpha> x (snd pa) \<and> pa \<in> Y) \<and> xa \<le> b"
      by fastforce
    then have "\<exists>b. b \<in> {p \<squnion> \<alpha> x (snd pa) |pa. pa \<in> Y} \<and> xa \<le> b"
      by blast
    then show "xa \<le> \<Squnion>{p \<squnion> \<alpha> x (snd pa) |pa. pa \<in> Y}"
      by (meson Sup_upper2)
  qed
next
  show "Y \<noteq> {} \<Longrightarrow> \<Squnion>{p \<squnion> \<alpha> x (snd y) |y. y \<in> Y} \<le> p \<squnion> \<Squnion>{\<alpha> x (snd y) |y. y \<in> Y}"
    apply (rule Sup_least)
    apply safe
    by (metis (mono_tags, lifting) Sup_le_iff le_sup_iff mem_Collect_eq sup_ge1 sup_ge2)
qed

lemma sd_distl: "Y \<noteq> {} \<Longrightarrow> sd_prod x (Sup_prod Y) = Sup_prod {sd_prod x y |y. y \<in> Y}"
proof -
  assume a: "Y \<noteq> {}"
  have "sd_prod x (Sup_prod Y) = sd_prod x (\<Squnion>{fst y |y. y \<in> Y}, \<Squnion>{snd y |y. y \<in> Y})"
    by (simp add: Sup_prod_def)
  also have "... = ((fst x) \<cdot> (\<Squnion>{fst y |y. y \<in> Y}), (snd x \<squnion> (\<alpha> (fst x) (\<Squnion>{snd y |y. y \<in> Y}))))"
    by (simp add: sd_prod_def)
  also have "... = (\<Squnion>{fst x \<cdot> fst y |y. y \<in> Y}, (snd x \<squnion> (\<alpha> (fst x) (\<Squnion>{snd y |y. y \<in> Y}))))"
    by (simp add: Sup_distl)
  also have "... = (\<Squnion>{fst x \<cdot> fst y |y. y \<in> Y}, (snd x \<squnion> (\<Squnion>{\<alpha> (fst x) (snd y) |y. y \<in> Y})))"
    by (simp add: act4, meson)
  also have "... = (\<Squnion>{fst x \<cdot> fst y |y. y \<in> Y}, \<Squnion>{snd x \<squnion> (\<alpha> (fst x) (snd y)) |y. y \<in> Y})"
    using a sd_distl_aux by blast
  also have "... = Sup_prod {(fst x \<cdot> fst y, snd x \<squnion> (\<alpha> (fst x) (snd y))) |y. y \<in> Y}"
    by (simp add: Sup_prod_def, metis)
  finally show ?thesis
    by (simp add: sd_prod_def)
qed
  
definition "sd_unit = (1,\<bottom>)"
 
lemma sd_unitl [simp]: "sd_prod sd_unit x = x"
  by (simp add: sd_prod_def sd_unit_def)    
    
lemma sd_unitr [simp]: "sd_prod x sd_unit = x"
  apply (simp add: sd_prod_def sd_unit_def)
  using act_emp by force
   
text \<open>The following counterexamples rule out that semidirect products of quantales and complete lattices form quantales.
The reason is that the right annihilation law fails.\<close>
  
lemma "sd_prod x (Sup_prod Y) = Sup_prod {sd_prod x y |y. y \<in> Y}" (*nitpick[show_all,expect=genuine]*)
  oops
  
lemma "sd_prod x bot_prod = bot_prod" (*nitpick[show_all,expect=genuine]*)
  oops
    
text \<open>However we can show that semidirect products of (unital) quantales with complete lattices form weak (unital) quantales. \<close>
    
interpretation dp_quantale: weak_quantale sd_prod Inf_prod Sup_prod inf_prod less_eq_prod less_prod sup_prod bot_prod top_prod
  apply standard 
  apply (simp_all add: sd_distl sd_distr)
  apply (simp_all add: sd_prod_def Inf_prod_def Sup_prod_def bot_prod_def sup_prod_def top_prod_def inf_prod_def less_eq_prod_def less_prod_def)
  by (rule conjI, simp add: mult.assoc, simp add: act1 act_sup_distl sup_assoc) 
    
interpretation dpu_quantale: unital_weak_quantale sd_unit sd_prod Inf_prod Sup_prod inf_prod less_eq_prod less_prod sup_prod bot_prod top_prod
  by (standard; simp_all)

end

end
  


