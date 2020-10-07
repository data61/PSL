(* Title: Binary Modalities
   Author: Brijesh Dongol, Victor Gomes, Ian J Hayes, Georg Struth
   Maintainer: Victor Gomes <victor.gomes@cl.cam.ac.uk>
               Georg Struth <g.struth@sheffield.ac.uk> 
*)

section \<open>Binary Modalities and Relational Convolution\<close>

theory Binary_Modalities
  imports Quantales

begin
 
subsection \<open>Auxiliary Properties\<close>
  
lemma SUP_is_Sup: "(SUP f\<in>F. f y) = \<Squnion>{(f::'a \<Rightarrow> 'b::proto_near_quantale) y |f. f \<in> F}"
proof (rule antisym)
  fix f::"'a \<Rightarrow> 'b::proto_near_quantale"
  have "f \<in> F \<Longrightarrow> f y \<in> {f y |f. f \<in> F}"
    by (simp add: Setcompr_eq_image)
  hence "f \<in> F \<Longrightarrow> f y \<le> \<Squnion>{f y |f. f \<in> F}"
    by (simp add: Sup_upper)
  thus "(SUP f\<in>F. f y) \<le> \<Squnion>{(f::'a \<Rightarrow> 'b::proto_near_quantale) y |f. f \<in> F}"
    by (simp add: Setcompr_eq_image)
next 
  fix x
  have "x \<in> {f y |f. f \<in> F} \<Longrightarrow> x \<le> (SUP f\<in>F. f y) "
    using mk_disjoint_insert by force
  thus "Sup {(f::'a \<Rightarrow> 'b::proto_near_quantale) y |f. f \<in> F} \<le> (SUP f\<in>F. f y)"
    by (simp add: Setcompr_eq_image)
qed

lemma bmod_auxl: "{x \<cdot> g z |x. \<exists>f. x = f y \<and> f \<in> F} = {f y \<cdot> g z |f. f \<in> F}"
  by force

lemma bmod_auxr: "{f y \<cdot> x |x. \<exists>g. x = g z \<and> g \<in> G} = {f y \<cdot> g z |g. g \<in> G}"
  by force

lemma bmod_assoc_aux1: 
  "\<Squnion>{\<Squnion>{(f :: 'a \<Rightarrow> 'b::proto_near_quantale) u \<cdot> g v \<cdot> h w |u v. R y u v} |y w. R x y w} 
     = \<Squnion>{(f u \<cdot> g v) \<cdot> h w |u v y w. R y u v \<and> R x y w}"
  apply (rule antisym)
  apply (rule Sup_least, safe)
  apply (intro Sup_least Sup_upper, force)
  apply (rule Sup_least, safe)
  by (rule Sup_upper2, auto)+
  
lemma bmod_assoc_aux2:   
  "\<Squnion>{\<Squnion>{(f::'a \<Rightarrow> 'b::proto_near_quantale) u \<cdot> g v \<cdot> h w |v w. R y v w} |u y. R x u y} 
     = \<Squnion>{f u \<cdot> g v \<cdot> h w |u v w y. R y v w \<and> R x u y}" 
  apply (rule antisym)
  apply (rule Sup_least, safe)
  apply (intro Sup_least Sup_upper, force)
  apply (rule Sup_least, safe)
  by (rule Sup_upper2, auto)+
    

subsection \<open>Binary Modalities\<close>
  
text \<open>Most of the development in the papers mentioned in the introduction generalises to proto-near-quantales. Binary modalities 
are interesting for various substructural logics over ternary Kripke frames. They also arise, e.g., 
as chop modalities in interval logics or as separation conjunction in separation logic. Binary modalities can be understood as a convolution
operation parametrised by a ternary operation. Our development yields a 
unifying framework.\<close>
  
text \<open>We would prefer a notation that is more similar to our articles, that is, $f\ast_R g$, but we don' know how we could 
index an infix operator by a variable in Isabelle.\<close>

definition bmod_comp :: "('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> 'd::proto_near_quantale) \<Rightarrow> ('c \<Rightarrow> 'd) \<Rightarrow> 'a \<Rightarrow> 'd" ("\<otimes>") where 
  "\<otimes> R f g x = \<Squnion>{f y \<cdot> g z |y z. R x y z}"

definition bmod_bres :: "('c \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> 'd::proto_near_quantale) \<Rightarrow> ('c \<Rightarrow> 'd) \<Rightarrow> 'a \<Rightarrow> 'd" ("\<lhd>") where 
  "\<lhd> R f g x = \<Sqinter>{(f y) \<rightarrow> (g z) |y z. R z y x}"

definition bmod_fres :: "('b \<Rightarrow> 'a \<Rightarrow> 'c \<Rightarrow> bool)  \<Rightarrow> ('b \<Rightarrow> 'd::proto_near_quantale) \<Rightarrow> ('c \<Rightarrow> 'd) \<Rightarrow> 'a \<Rightarrow> 'd" ("\<rhd>")where 
  "\<rhd> R f g x = \<Sqinter>{(f y) \<leftarrow> (g z) |y z. R y x z}"

lemma bmod_un_rel: "\<otimes> (R \<squnion> S) = \<otimes> R \<squnion> \<otimes> S"
  apply  (clarsimp simp: fun_eq_iff bmod_comp_def Sup_union_distrib[symmetric] Collect_disj_eq[symmetric])
  by (metis (no_types, lifting))

lemma bmod_Un_rel: "\<otimes> (\<Squnion>\<R>) f g x = \<Squnion>{\<otimes> R f g x |R. R \<in> \<R>}"
  apply (simp add: bmod_comp_def)
  apply (rule antisym)
  apply (rule Sup_least, safe)
  apply (rule Sup_upper2, force)
  apply (rule Sup_upper, force)
  apply (rule Sup_least, safe)+
  by (metis (mono_tags, lifting) Sup_upper mem_Collect_eq)
    
lemma bmod_sup_fun1: "\<otimes> R (f \<squnion> g) = \<otimes> R f \<squnion> \<otimes> R g"
  apply (clarsimp simp add: fun_eq_iff bmod_comp_def sup_distr)
  apply (rule antisym)
  apply (intro Sup_least, safe)
  apply (rule sup_least)
  apply (intro le_supI1 Sup_upper, force)
  apply (intro le_supI2 Sup_upper, force)
  apply (rule sup_least)
  by (intro Sup_least, safe, rule Sup_upper2, force, simp)+

lemma bmod_Sup_fun1: "\<otimes> R (\<Squnion>\<F>) g x = \<Squnion>{\<otimes> R f g x |f. f \<in> \<F>}"
proof -
  have "\<otimes> R (\<Squnion>{f. f \<in> \<F>}) g x = \<Squnion>{\<Squnion>{f y |f. f \<in> \<F>} \<cdot> g z |y z. R x y z}"
    by (simp add: bmod_comp_def SUP_is_Sup)
  also have "... = \<Squnion>{\<Squnion>{f y \<cdot> g z |f. f \<in> \<F>} |y z. R x y z}"
    by (simp add: Sup_distr bmod_auxl)
  also have "... = \<Squnion>{\<Squnion>{f y \<cdot> g z |y z. R x y z} |f. f \<in> \<F>}"
    apply (rule antisym)
    by ((rule Sup_least, safe)+ , (rule Sup_upper2, force, rule Sup_upper, force))+
  finally show ?thesis
    by (simp add: bmod_comp_def)
qed

lemma bmod_sup_fun2: "\<otimes> R (f::'a \<Rightarrow> 'b::weak_proto_quantale) (g \<squnion> h) = \<otimes> R f g \<squnion> \<otimes> R f h"
  apply (clarsimp simp add: fun_eq_iff bmod_comp_def sup_distl)
  apply (rule antisym)
  apply (intro Sup_least, safe)
  apply (rule sup_least)
  apply (intro le_supI1 Sup_upper, force)
  apply (intro le_supI2 Sup_upper, force)
  apply (rule sup_least)
  by (intro Sup_least, safe, rule Sup_upper2, force, simp)+
 
lemma bmod_Sup_fun2_weak:
  assumes "\<G> \<noteq> {}"
  shows "\<otimes> R f (\<Squnion>\<G>) x = \<Squnion>{\<otimes> R f (g::'a \<Rightarrow> 'b::weak_proto_quantale) x |g. g \<in> \<G>}"
proof -
  have set: "\<And>z. {g z |g::'a \<Rightarrow> 'b. g \<in> \<G>} \<noteq> {}"
    using assms by blast
  have "\<otimes> R f (\<Squnion>{g. g \<in> \<G>}) x = \<Squnion>{f y \<cdot> \<Squnion>{g z |g. g \<in> \<G>} |y z. R x y z}"
    by (simp add: bmod_comp_def SUP_is_Sup)
  also have "... = \<Squnion>{\<Squnion>{f y \<cdot> g z |g. g \<in> \<G>} |y z. R x y z}"
    by (simp add: weak_Sup_distl[OF set] bmod_auxr)           
  also have "... = \<Squnion>{\<Squnion>{f y \<cdot> g z |y z. R x y z} |g. g \<in> \<G>}"
    apply (rule antisym)
    by ((rule Sup_least, safe)+, (rule Sup_upper2, force, rule Sup_upper, force))+
  finally show ?thesis
    by (auto simp: bmod_comp_def)
qed
  
lemma bmod_Sup_fun2: "\<otimes> R f (\<Squnion>\<G>) x = \<Squnion>{\<otimes> R f (g::'a \<Rightarrow> 'b::proto_quantale) x |g. g \<in> \<G>}"
proof -
  have "\<otimes> R f (\<Squnion>{g. g \<in> \<G>}) x = \<Squnion>{f y \<cdot> \<Squnion>{g z |g. g \<in> \<G>} |y z. R x y z}"
    by (simp add:  bmod_comp_def SUP_is_Sup)
  also have "... = \<Squnion>{\<Squnion>{f y \<cdot> g z |g. g \<in> \<G>} |y z. R x y z}"
    by (simp add: Sup_distl bmod_auxr)
  also have "... =  \<Squnion>{\<Squnion>{f y \<cdot> g z |y z. R x y z} |g. g \<in> \<G>}"
    apply (rule antisym)
    by ((rule Sup_least, safe)+, (rule Sup_upper2, force, rule Sup_upper, force))+
  finally show ?thesis
    by (auto simp: bmod_comp_def)
qed

lemma bmod_comp_bres_galois: "(\<forall>x. \<otimes> R f g x \<le> h x) \<longleftrightarrow> (\<forall>x. g x \<le> \<lhd> R f h x)" (* nitpick[expect=genuine] *)
  oops
    
text \<open>The following Galois connection requires functions into proto-quantales.\<close>
    
lemma bmod_comp_bres_galois: "(\<forall>x. \<otimes> R (f::'a \<Rightarrow> 'b::proto_quantale) g x \<le> h x) \<longleftrightarrow> (\<forall>x. g x \<le> \<lhd> R f h x)"
proof -
  have "(\<forall>x. \<otimes> R f g x \<le> h x) \<longleftrightarrow> (\<forall>x y z. R x y z \<longrightarrow> (f y) \<cdot> (g z) \<le> h x)"
    apply (simp add: bmod_comp_def, standard, safe)
    apply (metis (mono_tags, lifting) CollectI Sup_le_iff)
    by (rule Sup_least, force)
  also have "... \<longleftrightarrow>  (\<forall>x y z. R x y z \<longrightarrow> g z \<le> (f y) \<rightarrow> (h x))"
    by (simp add: bres_galois)
  finally show ?thesis
    apply (simp add: fun_eq_iff bmod_bres_def)
    apply standard
    using le_Inf_iff apply fastforce
    by (metis (mono_tags, lifting) CollectI le_Inf_iff)
qed 

lemma bmod_comp_fres_galois: "(\<forall>x. \<otimes> R f g x \<le> h x) \<longleftrightarrow> (\<forall>x. f x \<le> \<rhd> R h g x)"
proof -
  have "(\<forall>x. \<otimes> R f g x \<le> h x) \<longleftrightarrow> (\<forall>x y z. R x y z \<longrightarrow> (f y) \<cdot> (g z) \<le> h x)"
    apply (simp add: bmod_comp_def, standard, safe)
    apply (metis (mono_tags, lifting) CollectI Sup_le_iff)
    by (rule Sup_least, force)
  also have "... \<longleftrightarrow>  (\<forall>x y z. R x y z \<longrightarrow> f y \<le> (h x) \<leftarrow> (g z))"
    by (simp add: fres_galois)
  finally show ?thesis
    apply (simp add: bmod_fres_def fun_eq_iff)
    apply standard
    using le_Inf_iff apply fastforce
    by (metis (mono_tags, lifting) CollectI le_Inf_iff)
qed 
  

subsection \<open>Relational Convolution and Correspondence Theory\<close>

text\<open>We now fix a ternary relation $\rho$ and can then hide the parameter in a convolution-style notation.\<close>
  
class rel_magma = 
  fixes \<rho> :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"

begin
  
definition times_rel_fun :: "('a \<Rightarrow> 'b::proto_near_quantale) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b" (infix "\<star>" 70) where
  "f \<star> g = \<otimes> \<rho> f g"
  
lemma rel_fun_Sup_distl_weak: 
  "G \<noteq> {} \<Longrightarrow> (f::'a \<Rightarrow> 'b::weak_proto_quantale) \<star> \<Squnion>G = \<Squnion>{f \<star> g |g. g \<in> G}"
proof- 
  fix f :: "'a \<Rightarrow> 'b" and G :: "('a \<Rightarrow> 'b) set" 
  assume a: "G \<noteq> {}"
  show "f \<star> \<Squnion>G = \<Squnion>{f \<star> g |g. g \<in> G}"
    apply (clarsimp simp: fun_eq_iff times_rel_fun_def bmod_Sup_fun2_weak[OF a])
    apply (rule antisym)
    apply (rule Sup_least, safe)
    apply (rule SUP_upper2, force+)
    apply (rule SUP_least, safe)
    by (rule Sup_upper2, force+)
qed
    
lemma rel_fun_Sup_distl: "(f::'a \<Rightarrow> 'b::proto_quantale) \<star> \<Squnion>G = \<Squnion>{f \<star> g |g. g \<in> G}"
  apply (clarsimp simp: fun_eq_iff times_rel_fun_def bmod_Sup_fun2)
  apply (rule antisym)
  apply (rule Sup_least, safe)
  apply (rule SUP_upper2, force+)
  apply (rule SUP_least, safe)
  by (rule Sup_upper2, force+)

lemma rel_fun_Sup_distr: "\<Squnion>G \<star> (f::'a \<Rightarrow> 'b::proto_near_quantale) = \<Squnion>{g \<star> f |g. g \<in> G}"
  apply (clarsimp simp: fun_eq_iff times_rel_fun_def bmod_Sup_fun1)
  apply (rule antisym)
  apply (rule Sup_least, safe)
  apply (rule SUP_upper2, force+)
  apply (rule SUP_least, safe)
  by (rule Sup_upper2, force+)

end

class rel_semigroup = rel_magma +
  assumes rel_assoc: "(\<exists>y. \<rho> y u v \<and> \<rho> x y w) \<longleftrightarrow> (\<exists>z. \<rho> z v w \<and> \<rho> x u z)"

begin
  
text \<open>Nitpick produces counterexamples even for weak quantales. 
Hence one cannot generally lift functions into weak quantales to weak quantales.\<close>
  
lemma bmod_assoc: "\<otimes> \<rho> (\<otimes> \<rho> (f::'a \<Rightarrow> 'b::weak_quantale) g) h x = \<otimes> \<rho> f (\<otimes> \<rho> g h) x"
  (*nitpick[show_all,expect=genuine]*)
    oops

lemma bmod_assoc: "\<otimes> \<rho> (\<otimes> \<rho> (f::'a \<Rightarrow> 'b::quantale) g) h x = \<otimes> \<rho> f (\<otimes> \<rho> g h) x"
proof -
  have "\<otimes> \<rho> (\<otimes> \<rho> f g) h x = \<Squnion>{\<Squnion>{f u \<cdot> g v \<cdot> h z |u v. \<rho> y u v} |y z. \<rho> x y z}" 
    apply (simp add: bmod_comp_def Sup_distr)
    apply (rule antisym) 
    by (intro Sup_least Sup_upper, safe, intro exI conjI, simp_all, rule_tac f = Sup and g = Sup in cong, auto)+
  also have "... = \<Squnion>{f u \<cdot> g v \<cdot> h z |u v y z. \<rho> y u v \<and> \<rho> x y z}"
    by (simp add: bmod_assoc_aux1)
  also have "... = \<Squnion>{f u \<cdot> g v \<cdot> h z |u v z y. \<rho> y v z \<and> \<rho> x u y}" 
    apply (rule antisym)
    apply (rule Sup_least, rule Sup_upper, safe)
    using rel_assoc apply force
    apply (rule Sup_least, rule Sup_upper, safe)
    using rel_assoc by blast 
  also have "... = \<Squnion>{\<Squnion>{f u \<cdot> g v \<cdot> h z |v z. \<rho> y v z} |u y. \<rho> x u y}" 
    by (simp add: bmod_assoc_aux2)
  also have "... = \<Squnion>{f u \<cdot> \<Squnion>{g v \<cdot> h z |v z. \<rho> y v z} |u y. \<rho> x u y}" 
    apply (simp add: Sup_distl mult.assoc)
    apply (rule antisym)
    by (intro Sup_least Sup_upper, safe, intro exI conjI, simp_all, rule_tac f = Sup and g = Sup in cong, auto)+
  finally show ?thesis
    by (auto simp: bmod_comp_def)
qed

lemma rel_fun_assoc: "((f :: 'a \<Rightarrow> 'b::quantale) \<star> g) \<star> h = f \<star> (g \<star> h)"
  by (simp add: times_rel_fun_def fun_eq_iff bmod_assoc[symmetric])

end

lemma "\<otimes> R (\<otimes> R f f) f x = \<otimes> R f (\<otimes> R f f) x"
(*apply (simp add: bmod_comp_def) nitpick[expect=genuine] *)
oops

class rel_monoid = rel_semigroup + 
  fixes \<xi> :: "'a set"
  assumes unitl_ex: "\<exists>e \<in> \<xi>. \<rho> x e x" 
  and unitr_ex: "\<exists>e \<in> \<xi>. \<rho> x x e"
  and unitl_eq: "e \<in> \<xi> \<Longrightarrow> \<rho> x e y \<Longrightarrow> x = y"
  and unitr_eq: "e \<in> \<xi> \<Longrightarrow> \<rho> x y e \<Longrightarrow> x = y"

begin

lemma xi_prop: "e1 \<in> \<xi> \<Longrightarrow> e2 \<in> \<xi> \<Longrightarrow> e1 \<noteq> e2 \<Longrightarrow> \<not> \<rho> x e1 e2 \<and> \<not> \<rho> x e2 e1"
  using unitl_eq unitr_eq by blast

definition pid :: "'a  \<Rightarrow> 'b::unital_weak_quantale" ("\<delta>") where
  "\<delta> x = (if x \<in> \<xi> then 1 else \<bottom>)"
  
text \<open>Due to the absence of right annihilation, the right unit law fails for functions into weak quantales.\<close>
  
lemma bmod_onel: "\<otimes> \<rho> f (\<delta>::'a \<Rightarrow> 'b::unital_weak_quantale) x = f x" 
(*nitpick[expect=genuine]*)
  oops
  
text \<open>A unital quantale is required for this lifting.\<close>
    
lemma bmod_onel: "\<otimes> \<rho> f (\<delta>::'a \<Rightarrow> 'b::unital_quantale) x = f x"
  apply (simp add: bmod_comp_def pid_def)
  apply (rule antisym)
  apply (rule Sup_least, safe)
  apply (simp add: bres_galois)
  using unitr_eq apply fastforce
  apply (metis bot.extremum)
  by (metis (mono_tags, lifting) Sup_upper mem_Collect_eq unitr_ex)

lemma  bmod_oner: "\<otimes> \<rho> \<delta> f x = f x"
  apply (simp add: bmod_comp_def pid_def)
  apply (rule antisym)
  apply (rule Sup_least, safe)
  apply (simp add: fres_galois)
  using unitl_eq apply fastforce
  apply (metis bot.extremum)
  by (metis (mono_tags, lifting) Sup_upper mem_Collect_eq unitl_ex)

lemma pid_unitl [simp]: "\<delta> \<star> f = f"
  by (simp add: fun_eq_iff times_rel_fun_def bmod_oner)

lemma pid_unitr [simp]: "f \<star> (\<delta>::'a \<Rightarrow> 'b::unital_quantale) = f"
  by (simp add: fun_eq_iff times_rel_fun_def bmod_onel)
    
lemma bmod_assoc_weak_aux: 
  "f u \<cdot> \<Squnion>{g v \<cdot> h z |v z. \<rho> y v z} = \<Squnion>{(f::'a \<Rightarrow> 'b::weak_quantale) u \<cdot> g v \<cdot> h z |v z. \<rho> y v z}"
  apply (subst weak_Sup_distl)
  using unitl_ex apply force
  apply simp
  by (metis (no_types, lifting) mult.assoc)
    
lemma bmod_assoc_weak: "\<otimes> \<rho> (\<otimes> \<rho> (f::'a \<Rightarrow> 'b::weak_quantale) g) h x = \<otimes> \<rho> f (\<otimes> \<rho> g h) x"
proof -
  have "\<otimes> \<rho> (\<otimes> \<rho> f g) h x = \<Squnion>{\<Squnion>{f u \<cdot> g v \<cdot> h z |u v. \<rho> y u v} |y z. \<rho> x y z}" 
    apply (simp add: bmod_comp_def Sup_distr)
    apply (rule antisym) 
    by (intro Sup_least Sup_upper, safe, intro exI conjI, simp_all, rule_tac f = Sup and g = Sup in cong, auto)+
  also have "... = \<Squnion>{f u \<cdot> g v \<cdot> h z |u v y z. \<rho> y u v \<and> \<rho> x y z}"
    by (simp add: bmod_assoc_aux1)
  also have "... = \<Squnion>{f u \<cdot> g v \<cdot> h z |u v z y. \<rho> y v z \<and> \<rho> x u y}" 
    apply (rule antisym)
    apply (rule Sup_least, rule Sup_upper, safe)
    using rel_assoc apply force
    apply (rule Sup_least, rule Sup_upper, safe)
    using rel_assoc by blast 
  also have "... = \<Squnion>{\<Squnion>{f u \<cdot> g v \<cdot> h z |v z. \<rho> y v z} |u y. \<rho> x u y}" 
    by (simp add: bmod_assoc_aux2)
  also have "... = \<Squnion>{f u \<cdot> \<Squnion>{g v \<cdot> h z |v z. \<rho> y v z} |u y. \<rho> x u y}"
    by (simp add: bmod_assoc_weak_aux) 
  finally show ?thesis
    by (auto simp: bmod_comp_def)
qed
  
lemma rel_fun_assoc_weak: "((f :: 'a \<Rightarrow> 'b::weak_quantale) \<star> g) \<star> h = f \<star> (g \<star> h)"
  by (simp add: times_rel_fun_def fun_eq_iff bmod_assoc_weak[symmetric])

end

lemma (in rel_semigroup) "\<exists>id. \<forall>f x. (\<otimes> \<rho> f id x = f x \<and> \<otimes> \<rho> id f x = f x)"
(* apply (simp add: bmod_comp_def) nitpick [expect=genuine] *)
  oops

class rel_ab_semigroup = rel_semigroup +
  assumes rel_comm: "\<rho> x y z \<Longrightarrow>  \<rho> x z y" 

begin 

lemma bmod_comm: "\<otimes> \<rho> (f::'a \<Rightarrow> 'b::ab_quantale) g = \<otimes> \<rho> g f"
  by (simp add: fun_eq_iff bmod_comp_def mult.commute, meson rel_comm)

lemma "\<otimes> \<rho> f g = \<otimes> \<rho> g f" (* nitpick [expect=genuine] *)
oops

lemma bmod_bres_fres_eq: "\<lhd> \<rho> (f::'a \<Rightarrow> 'b::ab_quantale) g = \<rhd> \<rho> g f"
  by (simp add: fun_eq_iff bmod_bres_def bmod_fres_def bres_fres_eq, meson rel_comm)

lemma rel_fun_comm: "(f :: 'a \<Rightarrow> 'b::ab_quantale) \<star> g = g \<star> f"
  by (simp add: times_rel_fun_def bmod_comm)

end

class rel_ab_monoid = rel_ab_semigroup + rel_monoid
  
subsection \<open>Lifting to Function Spaces\<close>

text \<open>We lift by interpretation, since we need sort instantiations to be
     used for functions from PAM's to Quantales. Both instantiations cannot be
     used in Isabelle at the same time.\<close>
  
interpretation rel_fun: weak_proto_quantale Inf Sup inf less_eq less sup bot "top :: 'a::rel_magma \<Rightarrow> 'b::weak_proto_quantale" times_rel_fun
  by standard (simp_all add: rel_fun_Sup_distr rel_fun_Sup_distl_weak)
  
interpretation rel_fun: proto_quantale Inf Sup inf less_eq less sup bot "top :: 'a::rel_magma \<Rightarrow> 'b::proto_quantale" times_rel_fun
  by standard (simp add: rel_fun_Sup_distl)
    
text \<open>Nitpick shows that the lifting of weak quantales to weak quantales does not work for relational semigroups, because associativity fails.\<close>
  
interpretation rel_fun: weak_quantale times_rel_fun Inf Sup inf less_eq less sup bot "top::'a::rel_semigroup \<Rightarrow> 'b::weak_quantale"
  (*apply standard  nitpick[expect=genuine]*)
  oops
    
text \<open>Associativity is obtained when lifting from relational monoids, but the right unit law doesn't hold
 in the quantale on the function space, according to our above results. Hence the lifting results into a
non-unital quantale, in which only the left unit law holds, as shown above. We don't provide a special class for 
such quantales. Hence we lift only to non-unital quantales.\<close>
    
interpretation rel_fun: weak_quantale times_rel_fun Inf Sup inf less_eq less sup bot "top::'a::rel_monoid \<Rightarrow> 'b::unital_weak_quantale"
  by standard (simp_all add: rel_fun_assoc_weak) 

interpretation rel_fun2: quantale times_rel_fun Inf Sup inf less_eq less sup bot "top::'a::rel_semigroup \<Rightarrow> 'b::quantale" 
  by standard (simp add: rel_fun_assoc)
    
interpretation rel_fun2: distrib_quantale Inf Sup inf less_eq less sup bot "top::'a::rel_semigroup \<Rightarrow> 'b::distrib_quantale" times_rel_fun ..

interpretation rel_fun2: bool_quantale Inf Sup inf less_eq less sup bot "top::'a::rel_semigroup \<Rightarrow> 'b::bool_quantale" minus uminus times_rel_fun ..

interpretation rel_fun2: unital_quantale pid times_rel_fun Inf Sup inf less_eq less sup bot "top::'a::rel_monoid \<Rightarrow> 'b::unital_quantale" 
  by (standard; simp)
    
interpretation rel_fun2: distrib_unital_quantale Inf Sup inf less_eq less sup bot "top::'a::rel_monoid \<Rightarrow> 'b::distrib_unital_quantale" pid times_rel_fun ..

interpretation rel_fun2: bool_unital_quantale Inf Sup inf less_eq less sup bot "top::'a::rel_monoid \<Rightarrow> 'b::bool_unital_quantale" minus uminus pid times_rel_fun ..

interpretation rel_fun: ab_quantale times_rel_fun Inf Sup inf less_eq less sup bot "top::'a::rel_ab_semigroup \<Rightarrow> 'b::ab_quantale"
  by standard (simp add: rel_fun_comm)

interpretation rel_fun: ab_unital_quantale times_rel_fun Inf Sup inf less_eq less sup bot "top::'a::rel_ab_monoid \<Rightarrow> 'b::ab_unital_quantale" pid ..

interpretation rel_fun2: distrib_ab_unital_quantale Inf Sup inf less_eq less sup bot "top::'a::rel_ab_monoid \<Rightarrow> 'b::distrib_ab_unital_quantale" times_rel_fun pid ..

interpretation rel_fun2: bool_ab_unital_quantale times_rel_fun Inf Sup inf less_eq less sup bot "top::'a::rel_ab_monoid \<Rightarrow> 'b::bool_ab_unital_quantale" minus uminus pid ..
    
end

  
  
  
