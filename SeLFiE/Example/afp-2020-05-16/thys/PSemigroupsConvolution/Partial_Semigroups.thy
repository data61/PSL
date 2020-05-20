(* Title: Partial Semigroups
   Author: Brijesh Dongol, Victor Gomes, Ian J Hayes, Georg Struth
   Maintainer: Victor Gomes <victor.gomes@cl.cam.ac.uk>
               Georg Struth <g.struth@sheffield.ac.uk> 
*)

section \<open>Partial Semigroups\<close>

theory Partial_Semigroups
  imports Main

begin
  
notation times (infixl "\<cdot>" 70) 
  and times (infixl "\<oplus>" 70) 
  

subsection \<open>Partial Semigroups\<close>
  
text \<open>In this context, partiality is modelled by a definedness constraint $D$ instead of a bottom element, 
which would make the algebra total. This is common practice in mathematics.\<close>

class partial_times = times +
  fixes D :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
    
text \<open>The definedness constraints for associativity state that the right-hand side of the associativity
law is defined if and only if the left-hand side is and that, in this case, both sides are equal. This and
slightly different constraints can be found in the literature.\<close>

class partial_semigroup = partial_times + 
  assumes add_assocD: "D y z \<and> D x (y \<cdot> z) \<longleftrightarrow> D x y \<and> D (x \<cdot> y) z"
  and add_assoc: "D x y \<and> D (x \<cdot> y) z \<Longrightarrow> (x \<cdot> y) \<cdot> z = x \<cdot> (y \<cdot> z)"

text \<open>Every semigroup is a partial semigroup.\<close>
  
sublocale semigroup_mult \<subseteq> sg: partial_semigroup _ "\<lambda>x y. True" 
  by standard (simp_all add: mult_assoc)

context partial_semigroup 
begin
  
text \<open>The following abbreviation is useful for sublocale statements.\<close>
  
abbreviation (input) "R x y z \<equiv> D y z \<and> x = y \<cdot> z"
  
lemma add_assocD_var1: "D y z \<and> D x (y \<cdot> z) \<Longrightarrow> D x y \<and> D (x \<cdot> y) z"
  by (simp add: add_assocD)

lemma add_assocD_var2: " D x y \<and> D (x \<cdot> y) z \<Longrightarrow> D y z \<and> D x (y \<cdot> z)"
  by (simp add: add_assocD)

lemma add_assoc_var: " D y z \<and> D x (y \<cdot> z) \<Longrightarrow> (x \<cdot> y) \<cdot> z = x \<cdot> (y \<cdot> z)"
  by (simp add: add_assoc add_assocD)
    
    
subsection \<open>Green's Preorders and Green's Relations\<close>
  
text \<open>We define the standard Green's preorders and Green's relations. They are usually defined on monoids. 
  On (partial) semigroups, we only obtain transitive relations.\<close>

definition gR_rel :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<preceq>\<^sub>R" 50) where
  "x \<preceq>\<^sub>R y = (\<exists>z. D x z \<and> x \<cdot> z = y)"

definition strict_gR_rel :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<prec>\<^sub>R" 50) where
  "x \<prec>\<^sub>R y = (x \<preceq>\<^sub>R y \<and> \<not> y \<preceq>\<^sub>R x)"
  
definition gL_rel :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<preceq>\<^sub>L" 50) where
  "x \<preceq>\<^sub>L y = (\<exists>z. D z x \<and> z \<cdot> x = y)"

definition strict_gL_rel :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<prec>\<^sub>L" 50) where
  "x \<prec>\<^sub>L y = (x \<preceq>\<^sub>L y \<and> \<not> y \<preceq>\<^sub>L x)"
  
definition gH_rel :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<preceq>\<^sub>H" 50) where
  "x \<preceq>\<^sub>H y = (x \<preceq>\<^sub>L y \<and> x \<preceq>\<^sub>R y)"

definition gJ_rel :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<preceq>\<^sub>J" 50) where
  "x \<preceq>\<^sub>J y = (\<exists>v w. D v x \<and> D (v \<cdot> x) w \<and> (v \<cdot> x) \<cdot> w = y)"
  
definition "gR x y = (x \<preceq>\<^sub>R y \<and> y \<preceq>\<^sub>R x)" 
  
definition "gL x y = (x \<preceq>\<^sub>L y \<and> y \<preceq>\<^sub>L x)"  

definition "gH x y = (x \<preceq>\<^sub>H y \<and> y \<preceq>\<^sub>H x)"  

definition "gJ x y = (x \<preceq>\<^sub>J y \<and> y \<preceq>\<^sub>J x)"  
  
definition gR_downset :: "'a \<Rightarrow> 'a set" ("_\<down>" [100]100) where
  "x\<down> \<equiv> {y. y \<preceq>\<^sub>R x}"
  
text \<open>The following counterexample rules out reflexivity.\<close>
  
lemma "x \<preceq>\<^sub>R x" (* nitpick [expect=genuine] *)
  oops
    
lemma gR_rel_trans: "x \<preceq>\<^sub>R y \<Longrightarrow> y \<preceq>\<^sub>R z \<Longrightarrow> x \<preceq>\<^sub>R z"
  by (metis gR_rel_def add_assoc add_assocD_var2)
    
lemma gL_rel_trans: "x \<preceq>\<^sub>L y \<Longrightarrow> y \<preceq>\<^sub>L z \<Longrightarrow> x \<preceq>\<^sub>L z"
  by (metis gL_rel_def add_assocD_var1 add_assoc_var) 
    
lemma gR_add_isol: "D z y \<Longrightarrow> x \<preceq>\<^sub>R y \<Longrightarrow> z \<cdot> x \<preceq>\<^sub>R z \<cdot> y" 
  apply (simp add: gR_rel_def)
  using add_assocD_var1 add_assoc_var by blast
    
lemma gL_add_isor: "D y z \<Longrightarrow> x \<preceq>\<^sub>L y \<Longrightarrow> x \<cdot> z \<preceq>\<^sub>L y \<cdot> z"    
  apply (simp add: gL_rel_def)
  by (metis add_assoc add_assocD_var2)
 
definition annil :: "'a \<Rightarrow> bool" where
  "annil x = (\<forall>y. D x y \<and> x \<cdot> y = x)"
  
definition annir :: "'a \<Rightarrow> bool" where
  "annir x = (\<forall>y. D y x \<and> y \<cdot> x = x)"
  
end
  
  
subsection \<open>Morphisms\<close>
  
definition ps_morphism :: "('a::partial_semigroup \<Rightarrow> 'b::partial_semigroup) \<Rightarrow> bool" where
  "ps_morphism f = (\<forall>x y. D x y \<longrightarrow> D (f x) (f y) \<and> f (x \<cdot> y) = (f x) \<cdot> (f y))"

definition strong_ps_morphism :: "('a::partial_semigroup \<Rightarrow> 'b::partial_semigroup) \<Rightarrow> bool" where
  "strong_ps_morphism f = (ps_morphism f \<and> (\<forall>x y. D (f x) (f y) \<longrightarrow> D x y))"
  
  
subsection \<open> Locally Finite Partial Semigroups\<close>
  
text \<open>In locally finite partial semigroups,  elements can only be split in finitely many ways.\<close>
  
class locally_finite_partial_semigroup = partial_semigroup +
  assumes loc_fin: "finite (x\<down>)"
    
  
subsection \<open>Cancellative Partial Semigroups\<close>
  
class cancellative_partial_semigroup = partial_semigroup +
  assumes add_cancl: "D z x \<Longrightarrow> D z y \<Longrightarrow> z \<cdot> x = z \<cdot> y \<Longrightarrow> x = y" 
  and add_cancr: "D x z \<Longrightarrow> D y z \<Longrightarrow> x \<cdot> z = y \<cdot> z \<Longrightarrow> x = y" 
    
begin
  
lemma unique_resl: "D x z \<Longrightarrow> D x z' \<Longrightarrow> x \<cdot> z = y \<Longrightarrow> x \<cdot> z' = y \<Longrightarrow> z = z'"
  by (simp add: add_cancl)
    
lemma unique_resr: "D z x \<Longrightarrow> D z' x  \<Longrightarrow> z \<cdot> x = y \<Longrightarrow> z' \<cdot> x = y \<Longrightarrow> z = z'"
  by (simp add: add_cancr)

lemma gR_rel_mult: "D x y \<Longrightarrow> x \<preceq>\<^sub>R x \<cdot> y"
  using gR_rel_def by force
  
lemma gL_rel_mult: "D x y \<Longrightarrow> y \<preceq>\<^sub>L x \<cdot> y"
  using gL_rel_def by force
    
text \<open>By cancellation, the element z is uniquely defined for each pair x y, provided it exists.
       In both cases, z is therefore a function of x and y; it is a quotient or residual of x y.\<close>  
  
lemma quotr_unique: "x \<preceq>\<^sub>R y  \<Longrightarrow> (\<exists>!z. D x z \<and> y = x \<cdot> z)"
  using gR_rel_def add_cancl by force

lemma quotl_unique: "x \<preceq>\<^sub>L y \<Longrightarrow> (\<exists>!z. D z x \<and> y = z \<cdot> x)"
  using gL_rel_def unique_resr by force
 
definition "rquot y x = (THE z. D x z \<and> x \<cdot> z = y)"
  
definition "lquot y x = (THE z. D z x \<and> z \<cdot> x = y)"
  
lemma rquot_prop: "D x z \<and> y = x \<cdot> z \<Longrightarrow> z = rquot y x"
  by (metis (mono_tags, lifting) rquot_def the_equality unique_resl)
  
lemma rquot_mult: "x \<preceq>\<^sub>R y \<Longrightarrow> z = rquot y x \<Longrightarrow> x \<cdot> z = y"
  using gR_rel_def rquot_prop by force

lemma rquot_D: "x \<preceq>\<^sub>R y \<Longrightarrow> z = rquot y x \<Longrightarrow> D x z"
  using gR_rel_def rquot_prop by force

lemma add_rquot: "x \<preceq>\<^sub>R y \<Longrightarrow> (D x z \<and> x \<oplus> z = y \<longleftrightarrow> z = rquot y x)"
  using gR_rel_def rquot_prop by fastforce
 
lemma add_canc1: "D x y \<Longrightarrow> rquot (x \<cdot> y) x = y"
  using rquot_prop by simp
 
lemma add_canc2: "x \<preceq>\<^sub>R y \<Longrightarrow> x \<cdot> (rquot y x) = y"
  using gR_rel_def add_canc1 by force
    
lemma add_canc2_prop: "x \<preceq>\<^sub>R y \<Longrightarrow> rquot y x \<preceq>\<^sub>L y"
  using gL_rel_mult rquot_D rquot_mult by fastforce

text \<open>The next set of lemmas establishes standard Galois connections for cancellative partial semigroups.\<close>
  
lemma gR_galois_imp1: "D x z \<Longrightarrow> x \<cdot> z \<preceq>\<^sub>R y \<Longrightarrow> z \<preceq>\<^sub>R rquot y x"    
  by (metis gR_rel_def add_assoc add_assocD_var2 rquot_prop)

lemma gR_galois_imp21: "x \<preceq>\<^sub>R y \<Longrightarrow> z \<preceq>\<^sub>R rquot y x \<Longrightarrow> x \<cdot> z \<preceq>\<^sub>R y"
  using gR_add_isol rquot_D rquot_mult by fastforce
   
lemma gR_galois_imp22: "x \<preceq>\<^sub>R y \<Longrightarrow> z \<preceq>\<^sub>R rquot y x \<Longrightarrow> D x z"
  using gR_rel_def add_assocD add_canc1 by fastforce

lemma gR_galois: "x \<preceq>\<^sub>R y \<Longrightarrow> (D x z \<and> x \<cdot> z \<preceq>\<^sub>R y \<longleftrightarrow> z \<preceq>\<^sub>R rquot y x)"
  using gR_galois_imp1 gR_galois_imp21 gR_galois_imp22  by blast

lemma gR_rel_defined: "x \<preceq>\<^sub>R y \<Longrightarrow> D x (rquot y x)"
  by (simp add: rquot_D)
 
lemma ex_add_galois: "D x z \<Longrightarrow> (\<exists>y. x \<cdot> z = y \<longleftrightarrow> rquot y x = z)"
  using add_canc1 by force
    

             
end
  
  
subsection \<open>Partial Monoids\<close>
  
text \<open>We allow partial monoids with multiple units. This is similar to and inspired by small categories.\<close>
  
class partial_monoid = partial_semigroup +
  fixes E :: "'a set"
  assumes unitl_ex: "\<exists>e \<in> E. D e x \<and> e \<cdot> x = x"
  and unitr_ex: "\<exists>e \<in> E. D x e \<and> x \<cdot> e = x"
  and units_eq: "e1 \<in> E \<Longrightarrow> e2 \<in> E \<Longrightarrow> D e1 e2 \<Longrightarrow> e1 = e2"
  
text \<open>Every monoid is a partial monoid.\<close>
  
sublocale monoid_mult \<subseteq> mon: partial_monoid _ "\<lambda>x y. True" "{1}"
  by (standard; simp_all)

context partial_monoid 
begin
    
lemma units_eq_var: "e1 \<in> E \<Longrightarrow> e2 \<in> E \<Longrightarrow> e1 \<noteq> e2 \<Longrightarrow> \<not> D e1 e2"
  using units_eq by force
    
text \<open>In partial monoids, Green's relations become preorders, but need not be partial orders.\<close>
  
sublocale gR: preorder gR_rel strict_gR_rel
  apply standard
  apply (simp add: strict_gR_rel_def)
  using gR_rel_def unitr_ex apply force
  using gR_rel_trans by blast
    
sublocale gL: preorder gL_rel strict_gL_rel
  apply standard
  apply (simp add: strict_gL_rel_def)
  using gL_rel_def unitl_ex apply force
  using gL_rel_trans by blast

lemma "x \<preceq>\<^sub>R y \<Longrightarrow> y \<preceq>\<^sub>R x \<Longrightarrow> x = y" (* nitpick [expect=genuine] *)
  oops
    
lemma "annil x \<Longrightarrow> annil y \<Longrightarrow> x = y" (* nitpick [expext=genuine] *)
  oops
    
lemma  "annir x \<Longrightarrow> annir y \<Longrightarrow> x = y" (* nitpick [expect=genuine] *)
  oops

end
  
text \<open>Next we define partial monoid morphisms.\<close>
  
definition pm_morphism :: "('a::partial_monoid \<Rightarrow> 'b::partial_monoid) \<Rightarrow> bool" where
  "pm_morphism f = (ps_morphism f \<and> (\<forall>e. e \<in> E \<longrightarrow> (f e) \<in> E))"
  
definition strong_pm_morphism :: "('a::partial_monoid \<Rightarrow> 'b::partial_monoid) \<Rightarrow> bool" where
  "strong_pm_morphism f = (pm_morphism f \<and> (\<forall>e. (f e) \<in> E \<longrightarrow> e \<in> E))"
  
text \<open>Partial Monoids with a single unit form a special case.\<close>
  
class partial_monoid_one = partial_semigroup + one +
  assumes oneDl: "D x 1"
  and oneDr: "D 1 x"
  and oner: "x \<cdot> 1 = x" 
  and onel: "1 \<cdot> x = x"
  
begin

sublocale pmo: partial_monoid _ _ "{1}"
  by standard (simp_all add: oneDr onel oneDl oner)

end
  
  
subsection \<open>Cancellative Partial Monoids\<close>
  
class cancellative_partial_monoid = cancellative_partial_semigroup + partial_monoid
  
begin
  
lemma canc_unitr: "D x e \<Longrightarrow> x \<cdot> e = x \<Longrightarrow> e \<in> E"
  by (metis add_cancl unitr_ex)
    
lemma canc_unitl: "D e x \<Longrightarrow> e \<cdot> x = x \<Longrightarrow> e \<in> E"
  by (metis add_cancr unitl_ex)
    
end
  
  
subsection \<open>Positive Partial Monoids\<close>
  
class positive_partial_monoid  = partial_monoid +
  assumes posl: "D x y \<Longrightarrow> x \<cdot> y \<in> E \<Longrightarrow> x \<in> E"
  and posr: "D x y \<Longrightarrow> x \<cdot> y \<in> E \<Longrightarrow> y \<in> E"
  
begin
  
lemma pos_unitl: "D x y \<Longrightarrow> e \<in> E \<Longrightarrow> x \<cdot> y = e \<Longrightarrow> x = e"
  by (metis posl posr unitr_ex units_eq_var)
    
lemma pos_unitr: "D x y \<Longrightarrow> e \<in> E \<Longrightarrow> x \<cdot> y = e \<Longrightarrow> y = e"
  by (metis posl posr unitr_ex units_eq_var)
  
end
  
  
subsection \<open>Positive Cancellative Partial Monoids\<close>
  
class positive_cancellative_partial_monoid = positive_partial_monoid + cancellative_partial_monoid
  
begin
  
text \<open>In positive cancellative monoids, the Green's relations are partial orders.\<close>
  
sublocale pcpmR: order gR_rel strict_gR_rel
  apply standard
  apply (clarsimp simp: gR_rel_def)
  by (metis canc_unitr add_assoc add_assocD_var2 pos_unitl)
    
sublocale pcpmL: order gL_rel strict_gL_rel
  apply standard
  apply (clarsimp simp: gL_rel_def)
  by (metis canc_unitl add_assoc add_assocD_var1 pos_unitr)
  
end
  
  
subsection \<open>From Partial Abelian Semigroups to Partial Abelian Monoids\<close>
  
text \<open>Next we define partial abelian semigroups. These are interesting, e.g., for the foundations
of quantum mechanics and as resource monoids in separation logic.\<close>
  
class pas = partial_semigroup +
  assumes add_comm: "D x y \<Longrightarrow> D y x \<and> x \<oplus> y = y \<oplus> x"

begin

lemma D_comm: "D x y \<longleftrightarrow> D y x"
  by (auto simp add: add_comm)

lemma add_comm': "D x y \<Longrightarrow> x \<oplus> y = y \<oplus> x"
  by (auto simp add: add_comm)
  
lemma gL_gH_rel: "(x \<preceq>\<^sub>L y) = (x \<preceq>\<^sub>H y)"
  apply (simp add: gH_rel_def gL_rel_def gR_rel_def)
  using add_comm by force
    
lemma gR_gH_rel: "(x \<preceq>\<^sub>R y) = (x \<preceq>\<^sub>H y)"
  apply (simp add: gH_rel_def gL_rel_def gR_rel_def)
  using add_comm by blast

lemma annilr: "annil x = annir x"
  by (metis annil_def annir_def add_comm)
  
lemma anni_unique: "annil x \<Longrightarrow> annil y \<Longrightarrow> x = y"
  by (metis annilr annil_def annir_def)
    
end

text \<open>The following classes collect families of partially ordered abelian semigroups and monoids.\<close>

class locally_finite_pas = pas + locally_finite_partial_semigroup
  
class pam = pas + partial_monoid  
  
class cancellative_pam = pam + cancellative_partial_semigroup
  
class positive_pam = pam + positive_partial_monoid
  
class positive_cancellative_pam  = positive_pam + cancellative_pam
  
class generalised_effect_algebra = pas + partial_monoid_one
  
class cancellative_pam_one = cancellative_pam + partial_monoid_one
  
class positive_cancellative_pam_one = positive_cancellative_pam  + cancellative_pam_one

context cancellative_pam_one
begin
  
lemma E_eq_one: "E = {1}"
  by (metis oneDr oner unitl_ex units_eq singleton_iff subsetI subset_antisym)

lemma one_in_E: "1 \<in> E"
  by (simp add: E_eq_one)
  
end
  
 
subsection \<open>Alternative Definitions\<close>
  
text \<open>PAS's can be axiomatised more compactly as follows.\<close>

class pas_alt = partial_times +
  assumes pas_alt_assoc: "D x y \<and> D (x \<oplus> y) z \<Longrightarrow> D y z \<and> D x (y \<oplus> z) \<and> (x \<oplus> y) \<oplus> z = x \<oplus> (y \<oplus> z)"
  and pas_alt_comm: "D x y \<Longrightarrow> D y x \<and> x \<oplus> y = y \<oplus> x"
  
sublocale pas_alt \<subseteq> palt: pas
  apply standard
  using pas_alt_assoc pas_alt_comm by blast+

text \<open>Positive abelian PAM's can be axiomatised more compactly as well.\<close>
  
class pam_pos_alt = pam +
  assumes pos_alt: "D x y \<Longrightarrow> e \<in> E \<Longrightarrow> x \<oplus> y = e \<Longrightarrow> x = e"
    
sublocale pam_pos_alt \<subseteq> ppalt: positive_pam 
  apply standard
  using pos_alt apply force
  using add_comm pos_alt by fastforce
    

subsection \<open>Product Constructions\<close>
  
text \<open>We consider two kinds of product construction. The first one combines partial semigroups with sets, 
        the second one partial semigroups with partial semigroups. The first one is interesting for 
        Separation Logic. Semidirect product constructions are considered later.\<close>
  
instantiation prod :: (type, partial_semigroup) partial_semigroup
begin

definition "D_prod x y = (fst x = fst y \<and> D (snd x) (snd y))"
  for x y :: "'a \<times> 'b"

definition times_prod :: "'a \<times> 'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> 'a \<times> 'b" where
  "times_prod x y = (fst x, snd x \<cdot> snd y)"

instance
  apply (standard, simp_all add: D_prod_def times_prod_def)
  using partial_semigroup_class.add_assocD apply force
  by (simp add: partial_semigroup_class.add_assoc)

end

instantiation prod :: (type, partial_monoid) partial_monoid
begin
  
definition E_prod :: "('a \<times> 'b) set" where
  "E_prod = {x. snd x \<in> E}"
  
instance
  apply (standard, simp_all add: D_prod_def times_prod_def E_prod_def)
  using partial_monoid_class.unitl_ex apply fastforce
  using partial_monoid_class.unitr_ex apply fastforce
  by (simp add: partial_monoid_class.units_eq prod_eq_iff)

end
  
instance prod :: (type, pas) pas
  apply (standard, simp add: D_prod_def times_prod_def)
  using pas_class.add_comm by force

lemma prod_div1: "(x1::'a, y1::'b::pas) \<preceq>\<^sub>R (x2::'a, y2::'b::pas) \<Longrightarrow> x1 = x2"
  by (force simp: partial_semigroup_class.gR_rel_def times_prod_def)
 
lemma prod_div2: "(x1, y1) \<preceq>\<^sub>R (x2, y2) \<Longrightarrow> y1 \<preceq>\<^sub>R y2"
  by (force simp: partial_semigroup_class.gR_rel_def D_prod_def times_prod_def)

lemma prod_div_eq: "(x1, y1) \<preceq>\<^sub>R (x2, y2) \<longleftrightarrow> x1 = x2 \<and> y1 \<preceq>\<^sub>R y2"
  by (force simp: partial_semigroup_class.gR_rel_def D_prod_def times_prod_def)

instance prod :: (type, pam) pam 
  by standard

instance prod :: (type, cancellative_pam) cancellative_pam
  by (standard, auto simp: D_prod_def times_prod_def add_cancr add_cancl)
    
lemma prod_res_eq: "(x1, y1) \<preceq>\<^sub>R (x2::'a,y2::'b::cancellative_pam) 
    \<Longrightarrow> rquot (x2, y2) (x1, y1) = (x1, rquot y2 y1)"
  apply (clarsimp simp: partial_semigroup_class.gR_rel_def D_prod_def times_prod_def rquot_def)
  apply (rule theI2 conjI)
    apply force
  using add_cancl apply force
  by (rule the_equality, auto simp: add_cancl)

instance prod :: (type, positive_pam) positive_pam
   apply (standard, simp_all add: E_prod_def D_prod_def times_prod_def)
  using positive_partial_monoid_class.posl apply blast
  using positive_partial_monoid_class.posr by blast 
    
instance prod :: (type, positive_cancellative_pam) positive_cancellative_pam ..
    
instance prod :: (type, locally_finite_pas) locally_finite_pas    
proof (standard, case_tac x, clarsimp)
  fix s :: 'a and x :: 'b
  have "finite (x\<down>)"
    by (simp add: loc_fin)
  hence "finite {y. \<exists>z. D y z \<and> y \<oplus> z = x}"
    by (simp add: partial_semigroup_class.gR_downset_def partial_semigroup_class.gR_rel_def)
  hence "finite {(s, y)| y. \<exists>z. D y z \<and> y \<oplus> z = x}"
    by (drule_tac f="\<lambda>y. (s, y)" in finite_image_set) 
  moreover have "{y. \<exists>z1 z2. D y (z1, z2) \<and> y \<oplus> (z1, z2) = (s, x)} 
                    \<subseteq> {(s, y)| y. \<exists>z. D y z \<and> y \<oplus> z = x}"
    by (auto simp: D_prod_def times_prod_def)
  ultimately have "finite {y. \<exists>z1 z2. D y (z1, z2) \<and> y \<oplus> (z1, z2) = (s, x)}"
    by (auto intro: finite_subset)
  thus "finite ((s, x)\<down>)"
    by (simp add: partial_semigroup_class.gR_downset_def partial_semigroup_class.gR_rel_def)
qed
    
text \<open>Next we consider products of two partial semigroups.\<close>

definition ps_prod_D :: "'a :: partial_semigroup \<times> 'b :: partial_semigroup \<Rightarrow> 'a \<times> 'b  \<Rightarrow> bool"
  where "ps_prod_D x y \<equiv> D (fst x) (fst y) \<and> D (snd x) (snd y)"

definition ps_prod_times :: "'a :: partial_semigroup \<times> 'b :: partial_semigroup \<Rightarrow> 'a \<times> 'b \<Rightarrow> 'a \<times> 'b"
   where "ps_prod_times x y = (fst x \<cdot> fst y, snd x \<cdot> snd y)"

interpretation ps_prod: partial_semigroup ps_prod_times ps_prod_D
  apply (standard, simp_all add: ps_prod_D_def ps_prod_times_def)
  apply (meson partial_semigroup_class.add_assocD)
  by (simp add: partial_semigroup_class.add_assoc)

interpretation pas_prod: pas ps_prod_times "ps_prod_D :: 'a :: pas \<times> 'b :: pas \<Rightarrow> 'a \<times> 'b  \<Rightarrow> bool"
  by (standard, clarsimp simp: ps_prod_D_def ps_prod_times_def pas_class.add_comm)
  
definition pm_prod_E :: "('a :: partial_monoid \<times> 'b :: partial_monoid) set" where
  "pm_prod_E = {x. fst x \<in> E \<and> snd x \<in> E}"

interpretation pm_prod: partial_monoid ps_prod_times ps_prod_D pm_prod_E
  apply standard
  apply (simp_all add: ps_prod_times_def ps_prod_D_def pm_prod_E_def)
  apply (metis partial_monoid_class.unitl_ex prod.collapse)
  apply (metis partial_monoid_class.unitr_ex prod.collapse)
  by (simp add: partial_monoid_class.units_eq prod.expand)

interpretation pam_prod: pam ps_prod_times ps_prod_D "pm_prod_E :: ('a :: pam \<times> 'a :: pam) set" ..
  

subsection \<open>Partial Semigroup Actions and Semidirect Products\<close>
  
text \<open>(Semi)group actions are a standard mathematical construction. We generalise this to partial
semigroups and monoids. We use it to define semidirect products of partial semigroups. A generalisation 
to wreath products might be added in the future.\<close>
  
text \<open>First we define the (left) action of a partial semigroup on a set. A right action could be defined in a similar way, 
but we do not pursue this at the moment.\<close>
  
locale partial_sg_laction = 
  fixes Dla :: "'a::partial_semigroup \<Rightarrow> 'b \<Rightarrow> bool"
  and act :: "'a::partial_semigroup \<Rightarrow> 'b \<Rightarrow> 'b" ("\<alpha>") 
  assumes act_assocD: "D x y \<and> Dla (x \<cdot> y) p \<longleftrightarrow> Dla y p \<and> Dla x (\<alpha> y p)"
  and act_assoc: "D x y \<and> Dla (x \<cdot> y) p \<Longrightarrow> \<alpha> (x \<cdot> y) p = \<alpha> x (\<alpha> y p)"
  
text \<open>Next we define the action of a partial semigroup on another partial semigroup.
In the tradition of semigroup theory we use addition as a non-commutative operation for the second semigroup.\<close>
  
locale partial_sg_sg_laction = partial_sg_laction +
  assumes act_distribD: "D (p::'b::partial_semigroup) q \<and> Dla (x::'a::partial_semigroup) (p \<oplus> q) \<longleftrightarrow> Dla x p \<and> Dla x q \<and> D (\<alpha> x p) (\<alpha> x q)"
  and act_distrib: "D p q \<and> Dla x (p \<oplus> q) \<Longrightarrow> \<alpha> x (p \<oplus> q) = (\<alpha> x p) \<oplus> (\<alpha> x q)"  
  
begin
  
text \<open>Next we define the semidirect product as a partial operation and show that the semidirect 
product of two partial semigroups forms a partial semigroup.\<close>
  
definition sd_D :: "('a \<times> 'b) \<Rightarrow> ('a \<times> 'b) \<Rightarrow> bool" where
  "sd_D x y \<equiv> D (fst x) (fst y) \<and> Dla (fst x) (snd y) \<and> D (snd x) (\<alpha> (fst x) (snd y))"

definition sd_prod :: "('a \<times> 'b) \<Rightarrow> ('a \<times> 'b) \<Rightarrow> ('a \<times> 'b)" where
  "sd_prod x y = ((fst x) \<cdot> (fst y), (snd x) \<oplus> (\<alpha> (fst x) (snd y)))"   
  
sublocale dp_semigroup: partial_semigroup sd_prod sd_D
  apply unfold_locales
   apply (simp_all add: sd_prod_def sd_D_def)  
   apply (clarsimp, metis act_assoc act_assocD act_distrib act_distribD add_assocD) 
  by (clarsimp, metis act_assoc act_assocD act_distrib act_distribD add_assoc add_assocD)
    
end
  
text \<open>Finally we define the semigroup action for two partial monoids and show that the semidirect product of two partial monoids
is a partial monoid.\<close>

locale partial_mon_sg_laction = partial_sg_sg_laction Dla
  for Dla :: "'a::partial_monoid \<Rightarrow> 'b::partial_semigroup \<Rightarrow> bool" +
  assumes act_unitl: "e \<in> E \<Longrightarrow> Dla e p \<and> \<alpha> e p = p"

locale partial_mon_mon_laction = partial_mon_sg_laction _ Dla
  for Dla :: "'a::partial_monoid \<Rightarrow> 'b::partial_monoid \<Rightarrow> bool" +
  assumes act_annir: "e \<in> Ea \<Longrightarrow> Dla x e \<and> \<alpha> x e = e"

begin

definition sd_E :: "('a \<times> 'b) set" where
  "sd_E = {x. fst x \<in> E \<and> snd x \<in> E}" 

sublocale dp_semigroup : partial_monoid sd_prod sd_D sd_E
  apply unfold_locales
    apply (simp_all add: sd_prod_def sd_D_def sd_E_def)
    apply (metis act_annir eq_fst_iff eq_snd_iff mem_Collect_eq partial_monoid_class.unitl_ex)
   apply (metis act_annir eq_fst_iff eq_snd_iff partial_monoid_class.unitr_ex)
  by (metis act_annir partial_monoid_class.units_eq prod_eqI)
    
end

end
