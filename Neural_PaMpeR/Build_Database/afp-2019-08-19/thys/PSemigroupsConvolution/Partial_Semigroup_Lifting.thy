(* Title: Liftings of Partial Semigroups
   Author: Brijesh Dongol, Victor Gomes, Ian J Hayes, Georg Struth
   Maintainer: Victor Gomes <victor.gomes@cl.cam.ac.uk>
               Georg Struth <g.struth@sheffield.ac.uk> 
*)

section \<open>Liftings of Partial Semigroups\<close>

theory Partial_Semigroup_Lifting
  imports Partial_Semigroups Binary_Modalities

begin  
  
text \<open>First we show that partial semigroups are instances of relational semigroups. Then we extend the lifting results for relational 
semigroups to partial semigroups.\<close>
  
  
subsection \<open>Relational Semigroups and Partial Semigroups\<close>
  
text \<open>Every partial semigroup is a relational partial semigroup.\<close>
  
context partial_semigroup 
begin

sublocale rel_partial_semigroup: rel_semigroup "R"
  by standard (metis add_assoc add_assocD)

end

text \<open>Every partial monoid is a relational monoid.\<close>
  
context partial_monoid 
begin
  
sublocale rel_partial_monoid: rel_monoid "R" "E"
  apply standard
    apply (metis unitl_ex)
    apply (metis unitr_ex)
   apply (metis add_assocD_var1 unitl_ex units_eq_var)
  by (metis add_assocD_var2 unitr_ex units_eq_var)

end

text \<open>Every PAS is a relational abelian semigroup.\<close>
  
context pas 
begin
  
sublocale rel_pas: rel_ab_semigroup "R"
  apply standard
  using add_comm by blast

end
  
text \<open>Every PAM is a relational abelian monoid.\<close>
  
context pam 
begin

sublocale rel_pam: rel_ab_monoid "R" "E" ..

end
  

subsection \<open>Liftings of Partial Abelian Semigroups\<close>

text \<open>Functions from partial semigroups into weak quantales form weak proto-quantales.\<close>  

instantiation "fun" :: (partial_semigroup, weak_quantale) weak_proto_quantale
begin
  
definition times_fun :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b" where
  "times_fun \<equiv> rel_partial_semigroup.times_rel_fun"
  
text \<open>The following counterexample shows that the associativity law may fail in convolution algebras
of functions from partial semigroups into weak quantales. \<close>
  
lemma "(rel_partial_semigroup.times_rel_fun (rel_partial_semigroup.times_rel_fun f f) f) x =
  (rel_partial_semigroup.times_rel_fun (f::'a::partial_semigroup \<Rightarrow> 'b::weak_quantale) (rel_partial_semigroup.times_rel_fun f f)) x"
(*  nitpick[show_all]*)
  oops
    
lemma "rel_partial_semigroup.times_rel_fun (rel_partial_semigroup.times_rel_fun f g) h =
  rel_partial_semigroup.times_rel_fun (f::'a::partial_semigroup \<Rightarrow> 'b::weak_quantale) (rel_partial_semigroup.times_rel_fun g h)"
(*  nitpick[show_all]*)
  oops
  
instance
  by standard (simp_all add: times_fun_def rel_partial_semigroup.rel_fun_Sup_distr rel_magma.rel_fun_Sup_distl_weak)

end
    
text \<open>Functions from partial semigroups into quantales form quantales.\<close>  
  
instance "fun" :: (partial_semigroup, quantale) quantale
  by standard (simp_all add: times_fun_def rel_partial_semigroup.rel_fun_assoc rel_magma.rel_fun_Sup_distl)

  
text \<open>The following counterexample shows that the right unit law may fail in convolution algebras
of functions from partial monoids into weak unital quantales. \<close>
  
lemma "(rel_partial_semigroup.times_rel_fun (f::'a::partial_monoid \<Rightarrow> 'b::unital_weak_quantale) rel_partial_monoid.pid) x = f x"
  (*nitpick[show_all]*)
  oops
    
text \<open>Functions from partial monoids into unital quantales form unital quantales.\<close>
    
instantiation "fun" :: (partial_monoid, unital_quantale) unital_quantale
begin

definition one_fun :: "'a \<Rightarrow> 'b" where
  "one_fun \<equiv> rel_partial_monoid.pid"

instance
  by standard (simp_all add: one_fun_def times_fun_def)

end
  
text \<open>These lifting results extend to PASs and PAMs as expected.\<close>

instance "fun" :: (pam, ab_quantale) ab_quantale
  by standard (simp_all add: times_fun_def rel_pas.rel_fun_comm)

instance "fun" :: (pam, bool_ab_quantale) bool_ab_quantale ..

instance "fun" :: (pam, bool_ab_unital_quantale) bool_ab_unital_quantale ..

sublocale ab_quantale < abq: pas "(*)" "\<lambda>_ _. True"
  apply standard
  apply (simp_all add: mult_assoc)
  by (simp add: mult_commute)

text \<open>Finally we prove some identities that hold in function spaces.\<close>
    
lemma times_fun_var: "(f * g) x = \<Squnion>{f y * g z | y z. R x y z}"
  by (simp add: times_fun_def rel_partial_semigroup.times_rel_fun_def bmod_comp_def)

lemma times_fun_var2: "(f * g) = (\<lambda>x. \<Squnion>{f y * g z | y z. R x y z})"
  by (auto simp: times_fun_var)

lemma one_fun_var1 [simp]: "x \<in> E \<Longrightarrow> 1 x = 1"
  by (simp add: one_fun_def rel_partial_monoid.pid_def)
    
lemma one_fun_var2 [simp]: "x \<notin> E \<Longrightarrow> 1 x = \<bottom>"
  by (simp add: one_fun_def rel_partial_monoid.pid_def)
    
lemma times_fun_canc: "(f * g) x = \<Squnion>{f y * g (rquot x y) | y. y \<preceq>\<^sub>R x}"
  apply (rule antisym)
   apply (simp add: times_fun_var, intro Sup_subset_mono, simp add: Collect_mono_iff)
  using gR_rel_mult add_canc1 apply force 
  apply (simp add: times_fun_var, intro Sup_subset_mono, simp add: Collect_mono_iff)
  using gR_rel_defined add_canc2 by fastforce

lemma times_fun_prod: "(f * g) = (\<lambda>(x, y). \<Squnion>{f (x, y1) * g (x, y2) | y1 y2. R y y1 y2})"
  by (auto simp: times_fun_var2 times_prod_def D_prod_def)

lemma one_fun_prod1 [simp]: "y \<in> E \<Longrightarrow> 1 (x, y) = 1"
  by (simp add: E_prod_def)

lemma one_fun_prod2 [simp]: "y \<notin> E \<Longrightarrow> 1 (x, y) = \<bottom>"
  by (simp add: E_prod_def)

lemma fres_galois_funI: "\<forall>x. (f * g) x \<le> h x \<Longrightarrow> f x \<le> (h \<leftarrow> g) x"
  by (meson fres_galois le_funD le_funI)
    
lemma times_fun_prod_canc: "(f * g) (x, y) = \<Squnion>{f (x, z) * g (x, rquot y z) | z. z \<preceq>\<^sub>R y}"
  apply (simp add: times_fun_prod)
  by (metis (no_types, lifting) gR_rel_defined gR_rel_mult add_canc1 add_canc2)
    
text \<open>The following statement shows, in a generalised setting, that the magic wand operator of separation
logic can be lifted from the heap subtraction operation generalised to a cancellative PAM.\<close>

lemma fres_lift: "(fres f g) (x::'b::cancellative_pam) = \<Sqinter>{(f y) \<leftarrow> (g z) | y z . z \<preceq>\<^sub>R y \<and> x = rquot y z}"
proof (rule antisym)
  { fix h y z 
    assume assms: "h \<cdot> g \<le> f" "z \<preceq>\<^sub>R y" "x = rquot y z"
    moreover hence  "D z x" 
      using add_rquot by blast
    moreover hence "h x \<cdot> g z \<le> (h \<cdot> g) (x \<oplus> z)"
      using add_comm by (auto simp add: times_fun_var intro!: Sup_upper)
    moreover hence "(h * g) (x \<oplus> z) \<le> f (z \<oplus> x)"
      by (simp add: \<open>D z x\<close> calculation(1) le_funD add_comm)
    ultimately have "h x \<le> (f (z \<oplus> x)) \<leftarrow> (g z)"
      by (auto simp: fres_def intro: Sup_upper)
    from this and assms have "h (rquot y z) \<le> (f y) \<leftarrow> (g z)"
      by (simp add: add_canc2)
} 
  thus "(f \<leftarrow> g) x \<le> \<Sqinter>{(f y) \<leftarrow> (g z) |y z. z \<preceq>\<^sub>R y \<and> x = rquot y z}"
    by (clarsimp simp: fres_def intro!: Inf_greatest SUP_least)
next
  have "\<Sqinter>{(f y) \<leftarrow> (g z) |y z. z \<preceq>\<^sub>R y \<and> x = rquot y z} \<le> Sup{x. x \<cdot> g \<le> f} x"
    apply (clarsimp simp: times_fun_var intro!: SUP_upper le_funI Sup_least)
    apply (simp add: fres_galois)
    apply (intro Inf_lower)
    apply safe
    by (metis gR_rel_mult add_canc1 add_comm)
  thus "\<Sqinter>{(f y) \<leftarrow> (g z) |y z. z \<preceq>\<^sub>R y \<and> x = rquot y z} \<le> (f \<leftarrow> g) x "
    by (simp add: fres_def)
qed

end

