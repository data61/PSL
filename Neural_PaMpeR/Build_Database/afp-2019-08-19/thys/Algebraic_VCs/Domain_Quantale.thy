(* Title: Domain Quantales
   Author: Victor Gomes, Georg Struth
   Maintainer: Victor Gomes <victor.gomes@cl.cam.ac.uk>
               Georg Struth <g.struth@sheffield.ac.uk> 
*)

section \<open>Component for Recursive Programs\<close>

theory Domain_Quantale
  imports KAD.Modal_Kleene_Algebra

begin

text \<open>This component supports the verification and step-wise refinement of recursive programs
in a partial correctness setting.\<close>

notation
  times (infixl "\<cdot>" 70) and
  bot ("\<bottom>") and
  top ("\<top>") and
  inf (infixl "\<sqinter>" 65) and
  sup (infixl "\<squnion>" 65)
(*
  Inf ("\<Sqinter>_" [900] 900) and
  Sup ("\<Squnion>_" [900] 900)
*)

(*
syntax
  "_INF1"     :: "pttrns \<Rightarrow> 'b \<Rightarrow> 'b"           ("(3\<Sqinter>_./ _)" [0, 10] 10)
  "_INF"      :: "pttrn \<Rightarrow> 'a set \<Rightarrow> 'b \<Rightarrow> 'b"  ("(3\<Sqinter>_\<in>_./ _)" [0, 0, 10] 10)
  "_SUP1"     :: "pttrns \<Rightarrow> 'b \<Rightarrow> 'b"           ("(3\<Squnion>_./ _)" [0, 10] 10)
  "_SUP"      :: "pttrn \<Rightarrow> 'a set \<Rightarrow> 'b \<Rightarrow> 'b"  ("(3\<Squnion>_\<in>_./ _)" [0, 0, 10] 10)

*)

subsection \<open>Lattice-Ordered Monoids with Domain\<close>

class bd_lattice_ordered_monoid = bounded_lattice + distrib_lattice + monoid_mult +
  assumes left_distrib: "x \<cdot> (y \<squnion> z) = x \<cdot> y \<squnion> x \<cdot> z"
  and right_distrib: "(x \<squnion> y) \<cdot> z = x \<cdot> z \<squnion> y \<cdot> z"
  and bot_annil [simp]: "\<bottom> \<cdot> x = \<bottom>"
  and bot_annir [simp]: "x \<cdot> \<bottom> = \<bottom>"

begin

sublocale semiring_one_zero "(\<squnion>)" "(\<cdot>)" "1" "bot" 
  by (standard, auto simp: sup.assoc sup.commute sup_left_commute left_distrib right_distrib sup_absorb1)   

sublocale dioid_one_zero "(\<squnion>)" "(\<cdot>)" "1" bot "(\<le>)" "(<)"
  by (standard, simp add: le_iff_sup, auto)

end

no_notation ads_d ("d")
  and ars_r ("r")
  and antirange_op ("ar _" [999] 1000)

class domain_bdlo_monoid = bd_lattice_ordered_monoid +
  assumes rdv: "(z \<sqinter> x \<cdot> top) \<cdot> y = z \<cdot> y \<sqinter> x \<cdot> top"  

begin 

definition "d x = 1 \<sqinter> x \<cdot> \<top>"

sublocale ds: domain_semiring "(\<squnion>)" "(\<cdot>)" "1" "\<bottom>" "d" "(\<le>)" "(<)"
proof standard
  fix x y
  show "x \<squnion> d x \<cdot> x = d x \<cdot> x"
    by (metis d_def inf_sup_absorb left_distrib mult_1_left mult_1_right rdv sup.absorb_iff1 sup.idem sup.left_commute top_greatest)
  show "d (x \<cdot> d y) = d (x \<cdot> y)"
    by (simp add: d_def inf_absorb2 rdv  mult_assoc)
  show "d x \<squnion> 1 = 1"
    by (simp add: d_def sup.commute)
  show "d bot = bot"
    by (simp add: d_def inf.absorb1 inf.commute)
  show "d (x \<squnion> y) = d x \<squnion> d y"
    by (simp add: d_def inf_sup_distrib1)
qed

end

subsection\<open>Boolean Monoids with Domain\<close>

class boolean_monoid = boolean_algebra + monoid_mult +  
  assumes left_distrib': "x \<cdot> (y \<squnion> z) = x \<cdot> y \<squnion> x \<cdot> z"
  and right_distrib': "(x \<squnion> y) \<cdot> z = x \<cdot> z \<squnion> y \<cdot> z"
  and bot_annil' [simp]: "\<bottom> \<cdot> x = \<bottom>"
  and bot_annir' [simp]: "x \<cdot> \<bottom> = \<bottom>"

begin

subclass bd_lattice_ordered_monoid
  by (standard, simp_all add: left_distrib' right_distrib')

lemma inf_bot_iff_le: "x \<sqinter> y = \<bottom> \<longleftrightarrow> x \<le> -y"
  by (metis le_iff_inf inf_sup_distrib1 inf_top_right sup_bot.left_neutral sup_compl_top compl_inf_bot inf.assoc inf_bot_right)

end

class domain_boolean_monoid = boolean_monoid + 
  assumes rdv': "(z \<sqinter> x \<cdot> \<top>) \<cdot> y = z \<cdot> y \<sqinter> x \<cdot> \<top>"     

begin

sublocale dblo: domain_bdlo_monoid "1" "(\<cdot>)" "(\<sqinter>)" "(\<le>)" "(<)" "(\<squnion>)" "\<bottom>" "\<top>"
  by (standard, simp add: rdv')

definition "a x = 1 \<sqinter> -(dblo.d x)"
                                
lemma a_d_iff: "a x = 1 \<sqinter> -(x \<cdot> \<top>)"
  by (clarsimp simp: a_def dblo.d_def inf_sup_distrib1) 

lemma topr: "-(x \<cdot> \<top>) \<cdot> \<top> = -(x \<cdot> \<top>)" 
proof (rule antisym)
  show "-(x \<cdot> \<top>) \<le> -(x \<cdot> \<top>) \<cdot> \<top>"
    by (metis mult_isol_var mult_oner order_refl top_greatest)
  have "-(x \<cdot> \<top>) \<sqinter> (x \<cdot> \<top>) = \<bottom>"
    by simp
  hence "(-(x \<cdot> \<top>) \<sqinter> (x \<cdot> \<top>)) \<cdot> \<top>  = \<bottom>"
    by simp 
  hence "-(x \<cdot> \<top>) \<cdot> \<top> \<sqinter> (x \<cdot> \<top>)  = \<bottom>"
    by (metis rdv') 
  thus "-(x \<cdot> \<top>) \<cdot> \<top> \<le> -(x \<cdot> \<top>)"
    by (simp add: inf_bot_iff_le)
qed

lemma dd_a: "dblo.d x = a (a x)"
  by (metis a_d_iff dblo.d_def double_compl inf_top.left_neutral mult_1_left rdv' topr)

lemma ad_a [simp]: "a (dblo.d x) = a x"
  by (simp add: a_def)

lemma da_a [simp]: "dblo.d (a x) = a x"
  using ad_a dd_a by auto

lemma a1 [simp]: "a x \<cdot> x = \<bottom>"
proof -
  have "a x \<cdot> x \<cdot> \<top> = \<bottom>"
    by (metis a_d_iff inf_compl_bot mult_1_left rdv' topr)
  then show ?thesis
    by (metis (no_types) dblo.d_def dblo.ds.domain_very_strict inf_bot_right)
qed

lemma a2 [simp]: "a (x \<cdot> y) \<squnion> a (x \<cdot> a (a y)) = a (x \<cdot> a (a y))"
  by (metis a_def dblo.ds.dsr2 dd_a sup.idem)

lemma a3 [simp]: "a (a x) \<squnion> a x = 1"
  by (metis a_def da_a inf.commute sup.commute sup_compl_top sup_inf_absorb sup_inf_distrib1)

subclass domain_bdlo_monoid ..

text \<open>The next statement shows that every boolean monoid with domain is an antidomain semiring. 
In this setting the domain operation has been defined explicitly.\<close>

sublocale ad: antidomain_semiring a "(\<squnion>)" "(\<cdot>)" "1" "\<bottom>" "(\<le>)" "(<)"
  rewrites ad_eq: "ad.ads_d x = d x"
proof -
  show "class.antidomain_semiring a (\<squnion>) (\<cdot>) 1 \<bottom> (\<le>) (<)"
    by (standard, simp_all)
  then interpret ad: antidomain_semiring a "(\<squnion>)" "(\<cdot>)" "1" "\<bottom>" "(\<le>)" "(<)" .
  show "ad.ads_d x = d x"
    by (simp add: ad.ads_d_def dd_a)
qed

end 

subsection\<open>Boolean Monoids with Range\<close>

class range_boolean_monoid = boolean_monoid + 
  assumes ldv': "y \<cdot> (z \<sqinter> \<top> \<cdot> x) = y \<cdot> z \<sqinter> \<top> \<cdot> x"

begin

definition "r x = 1 \<sqinter> \<top> \<cdot> x"

definition "ar x = 1 \<sqinter> -(r x)"
                                
lemma ar_r_iff: "ar x = 1 \<sqinter> -(\<top> \<cdot> x)"
  by (simp add: ar_def inf_sup_distrib1 r_def)

lemma topl: "\<top>\<cdot>(-(\<top> \<cdot> x)) = -(\<top> \<cdot> x)" 
proof (rule antisym)
  show "\<top> \<cdot> - (\<top> \<cdot> x) \<le> - (\<top> \<cdot> x)"
    by (metis bot_annir' compl_inf_bot inf_bot_iff_le ldv')
  show "- (\<top> \<cdot> x) \<le> \<top> \<cdot> - (\<top> \<cdot> x)"
    by (metis inf_le2 inf_top.right_neutral mult_1_left mult_isor)
qed

lemma r_ar: "r x = ar (ar x)"
  by (metis ar_r_iff double_compl inf.commute inf_top.right_neutral ldv' mult_1_right r_def topl)

lemma ar_ar [simp]: "ar (r x) = ar x"
  by (simp add: ar_def ldv' r_def)

lemma rar_ar [simp]: "r (ar x) = ar x"
  using r_ar ar_ar by force

lemma ar1 [simp]: "x \<cdot> ar x = \<bottom>"
proof -
  have "\<top> \<cdot> x \<cdot> ar x = \<bottom>"
    by (metis ar_r_iff inf_compl_bot ldv' mult_oner topl)
  then show ?thesis
    by (metis inf_bot_iff_le inf_le2 inf_top.right_neutral mult_1_left mult_isor mult_oner topl)
qed

lemma ars: "r (r x \<cdot> y) = r (x \<cdot> y)"
  by (metis inf.commute inf_top.right_neutral ldv' mult_oner mult_assoc r_def)

lemma ar2 [simp]: "ar (x \<cdot> y) \<squnion> ar (ar (ar x) \<cdot> y) = ar (ar (ar x) \<cdot> y)"
  by (metis ar_def ars r_ar sup.idem)
                         
lemma ar3 [simp]: "ar (ar x) \<squnion> ar x = 1 "
  by (metis ar_def rar_ar inf.commute sup.commute sup_compl_top sup_inf_absorb sup_inf_distrib1)

sublocale ar: antirange_semiring "(\<squnion>)" "(\<cdot>)" "1" "\<bottom>" ar "(\<le>)" "(<)"
  rewrites ar_eq: "ar.ars_r x = r x"
proof -
  show "class.antirange_semiring (\<squnion>) (\<cdot>) 1 \<bottom> ar (\<le>) (<)"
    by (standard, simp_all)
  then interpret ar: antirange_semiring "(\<squnion>)" "(\<cdot>)" "1" "\<bottom>" ar "(\<le>)" "(<)" .
  show "ar.ars_r x = r x"
    by (simp add: ar.ars_r_def r_ar)
qed

end

subsection \<open>Quantales\<close>

text \<open>This part will eventually move into an AFP quantale entry.\<close> 

class quantale = complete_lattice + monoid_mult +
  assumes Sup_distr: "Sup X \<cdot> y = Sup {z. \<exists>x \<in> X. z = x \<cdot> y}"
  and Sup_distl: "x \<cdot> Sup Y = Sup {z. \<exists>y \<in> Y. z = x \<cdot> y}"       

begin

lemma bot_annil'' [simp]: "\<bottom> \<cdot> x = \<bottom>"
  using Sup_distr[where X="{}"] by auto

lemma bot_annirr'' [simp]: "x \<cdot> \<bottom> = \<bottom>"
  using Sup_distl[where Y="{}"] by auto

lemma sup_distl: "x \<cdot> (y \<squnion> z) = x \<cdot> y \<squnion> x \<cdot> z"
  using Sup_distl[where Y="{y, z}"] by (fastforce intro!: Sup_eqI)

lemma sup_distr: "(x \<squnion> y) \<cdot> z = x \<cdot> z \<squnion> y \<cdot> z"
  using Sup_distr[where X="{x, y}"] by (fastforce intro!: Sup_eqI)

sublocale semiring_one_zero "(\<squnion>)" "(\<cdot>)" "1" "\<bottom>" 
  by (standard, auto simp: sup.assoc sup.commute sup_left_commute sup_distl sup_distr)     

sublocale dioid_one_zero "(\<squnion>)" "(\<cdot>)" "1" "\<bottom>" "(\<le>)" "(<)"
  by (standard, simp add: le_iff_sup, auto)

lemma Sup_sup_pred: "x \<squnion> Sup{y. P y} = Sup{y. y = x \<or> P y}"
  apply (rule antisym)
  apply (simp add: Collect_mono Sup_subset_mono Sup_upper) 
  using Sup_least Sup_upper le_supI2 by fastforce

definition star :: "'a \<Rightarrow> 'a" where
  "star x = (SUP i. x ^ i)"

lemma star_def_var1: "star x = Sup{y. \<exists>i. y = x ^ i}"
  by (simp add: star_def full_SetCompr_eq)

lemma star_def_var2: "star x = Sup{x ^ i |i. True}"
  by (simp add: star_def full_SetCompr_eq)

lemma star_unfoldl' [simp]: "1 \<squnion> x \<cdot> (star x) = star x"
proof -
  have "1 \<squnion> x \<cdot> (star x) = x ^ 0 \<squnion> x \<cdot> Sup{y. \<exists>i. y = x ^ i}"
    by (simp add: star_def_var1)
  also have "... = x ^ 0 \<squnion> Sup{y. \<exists>i. y = x ^ (i + 1)}"
    by (simp add: Sup_distl, metis)
  also have "... = Sup{y. y = x ^ 0 \<or> (\<exists>i. y = x ^ (i + 1))}"
    using Sup_sup_pred by simp
  also have "... = Sup{y. \<exists>i. y = x ^ i}"
    by (metis Suc_eq_plus1 power.power.power_Suc power.power_eq_if)
  finally show ?thesis
    by (simp add: star_def_var1)
qed

lemma star_unfoldr' [simp]: "1 \<squnion> (star x) \<cdot> x = star x"
proof -
  have "1 \<squnion> (star x) \<cdot> x = x ^ 0 \<squnion> Sup{y. \<exists>i. y = x ^ i} \<cdot> x"
    by (simp add: star_def_var1)
  also have "... = x ^ 0 \<squnion> Sup{y. \<exists>i. y = x ^ i \<cdot> x}"
    by (simp add: Sup_distr, metis)
  also have "... = x ^ 0 \<squnion> Sup{y. \<exists>i. y = x ^ (i + 1)}"
    using power_Suc2 by simp 
   also have "... = Sup{y. y = x ^ 0 \<or> (\<exists>i. y = x ^ (i + 1))}"
    using Sup_sup_pred by simp
  also have "... = Sup{y. \<exists>i. y = x ^ i}"
    by (metis Suc_eq_plus1 power.power.power_Suc power.power_eq_if)
  finally show ?thesis
    by (simp add: star_def_var1)
qed

lemma (in dioid_one_zero) power_inductl: "z + x \<cdot> y \<le> y \<Longrightarrow> (x ^ n) \<cdot> z \<le> y"
proof (induct n)
  case 0 show ?case
    using "0.prems" by simp
  case Suc thus ?case
    by (simp, metis mult.assoc mult_isol order_trans)
qed

lemma (in dioid_one_zero) power_inductr: "z + y \<cdot> x \<le> y \<Longrightarrow> z \<cdot> (x ^ n) \<le> y"
proof (induct n)
  case 0 show ?case
    using "0.prems" by auto
  case Suc
  {
    fix n
    assume "z + y \<cdot> x \<le> y \<Longrightarrow> z \<cdot> x ^ n \<le> y"
      and "z + y \<cdot> x \<le> y"
    hence "z \<cdot> x ^ n \<le> y"
      by simp
    also have "z \<cdot> x ^ Suc n = z \<cdot> x \<cdot> x ^ n"
      by (metis mult.assoc power_Suc)
    moreover have "... = (z \<cdot> x ^ n) \<cdot> x"
      by (metis mult.assoc power_commutes)
    moreover have "... \<le> y \<cdot> x"
      by (metis calculation(1) mult_isor)
    moreover have "... \<le> y"
      using \<open>z + y \<cdot> x \<le> y\<close> by simp
    ultimately have "z \<cdot> x ^ Suc n \<le> y" by simp
  }
  thus ?case
    by (metis Suc)
qed

lemma star_inductl': "z \<squnion> x \<cdot> y \<le> y \<Longrightarrow> (star x) \<cdot> z \<le> y" 
proof -
  assume "z \<squnion> x \<cdot> y \<le> y"
  hence "\<forall>i. x ^ i \<cdot> z \<le> y"
    by (simp add: power_inductl)
  hence "Sup{w. \<exists>i. w = x ^ i \<cdot> z} \<le> y"
    by (intro Sup_least, fast)
  hence "Sup{w. \<exists>i. w = x ^ i} \<cdot> z \<le> y"
    using Sup_distr Sup_le_iff by auto
  thus "(star x) \<cdot> z \<le> y"
    by (simp add: star_def_var1)
qed

lemma star_inductr': "z \<squnion> y \<cdot> x \<le> y \<Longrightarrow> z \<cdot> (star x) \<le> y" 
proof -
  assume "z \<squnion> y \<cdot> x \<le> y"
  hence "\<forall>i. z \<cdot> x ^ i  \<le> y"
    by (simp add: power_inductr)
  hence "Sup{w. \<exists>i. w = z \<cdot> x ^ i} \<le> y"
    by (intro Sup_least, fast)
  hence "z \<cdot> Sup{w. \<exists>i. w = x ^ i} \<le> y"
    using Sup_distl Sup_le_iff by auto
  thus "z \<cdot> (star x) \<le> y"
    by (simp add: star_def_var1)
qed

sublocale ka: kleene_algebra "(\<squnion>)" "(\<cdot>)" "1" "\<bottom>" "(\<le>)" "(<)" star
  by standard (simp_all add: star_inductl' star_inductr')

end

text \<open>Distributive quantales are often assumed to satisfy infinite distributivity laws between
joins and meets, but finite ones suffice for our purposes.\<close>

class distributive_quantale = quantale + distrib_lattice 

begin

subclass bd_lattice_ordered_monoid
  by (standard, simp_all add: distrib_left)

lemma "(1 \<sqinter> x \<cdot> \<top>) \<cdot> x = x"
(* nitpick [expect=genuine]*)
oops

end 

subsection \<open>Domain Quantales\<close>

class domain_quantale = distributive_quantale +
  assumes rdv'': "(z \<sqinter> x \<cdot> \<top>) \<cdot> y = z \<cdot> y \<sqinter> x \<cdot> \<top>"  

begin

subclass domain_bdlo_monoid 
  by (standard, simp add: rdv'')

end

class range_quantale = distributive_quantale +
  assumes ldv'': "y \<cdot> (z \<sqinter> \<top> \<cdot> x) = y \<cdot> z \<sqinter> \<top> \<cdot> x"

class boolean_quantale = quantale + complete_boolean_algebra

begin

subclass boolean_monoid
  by (standard, simp_all add: sup_distl)

lemma "(1 \<sqinter> x \<cdot> \<top>) \<cdot> x = x"
(*nitpick[expect=genuine]*)
oops

lemma "(1 \<sqinter> -(x \<cdot> \<top>)) \<cdot> x = \<bottom>"
(*nitpick[expect=genuine]*)
oops

end

subsection\<open>Boolean Domain Quantales\<close> 

class domain_boolean_quantale = domain_quantale + boolean_quantale

begin

subclass domain_boolean_monoid
  by (standard, simp add: rdv'')

lemma fbox_eq: "ad.fbox x q = Sup{d p |p. d p \<cdot> x \<le> x \<cdot> d q}"
  apply (rule Sup_eqI[symmetric])
  apply clarsimp
  using ad.fbox_demodalisation3 ad.fbox_simp apply auto[1]
  apply clarsimp
  by (metis ad.fbox_def ad.fbox_demodalisation3 ad.fbox_simp da_a eq_refl)

lemma fdia_eq: "ad.fdia x p = Inf{d q |q. x \<cdot> d p \<le> d q \<cdot> x}"
  apply (rule Inf_eqI[symmetric])
  apply clarsimp
  using ds.fdemodalisation2 apply auto[1]
  apply clarsimp
  by (metis ad.fd_eq_fdia ad.fdia_def da_a double_compl ds.fdemodalisation2 inf_bot_iff_le inf_compl_bot)

text \<open>The specification statement can be defined explicitly.\<close>

definition R :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" where
  "R p q \<equiv> Sup{x. (d p) \<cdot> x \<le> x \<cdot> d q}"

lemma "x \<le> R p q \<Longrightarrow> d p \<le> ad.fbox x (d q)"
proof (simp add: R_def ad.kat_1_equiv ad.kat_2_equiv)
  assume "x \<le> Sup{x. d p \<cdot> x \<cdot> a q = \<bottom>}"
  hence "d p \<cdot> x \<cdot> a q \<le> d p \<cdot> Sup{x. d p \<cdot> x \<cdot> a q = \<bottom>} \<cdot> a q "
    using mult_double_iso by blast
  also have "... = Sup{d p \<cdot> x \<cdot> a q |x. d p \<cdot> x \<cdot> a q = \<bottom>}"
    apply (subst Sup_distl)
    apply (subst Sup_distr)
    apply clarsimp
    by metis
  also have "... = \<bottom>"
    by (auto simp: Sup_eqI)
  finally show ?thesis
    using ad.fbox_demodalisation3 ad.kat_3 ad.kat_4 le_bot by blast
qed

lemma "d p \<le> ad.fbox x (d q) \<Longrightarrow> x \<le> R p q"
  apply (simp add: R_def)
  apply (rule Sup_upper)
  apply simp
  using ad.fbox_demodalisation3 ad.fbox_simp apply auto[1]
done

end

subsection\<open>Relational Model of Boolean Domain Quantales\<close>

interpretation rel_dbq: domain_boolean_quantale Inter Union "(\<inter>)" "(\<subseteq>)" "(\<subset>)" "(\<union>)" "{}" UNIV minus uminus Id "(O)"
  apply (standard, simp_all add: O_assoc)
  by blast +

subsection\<open>Modal Boolean Quantales\<close>

class range_boolean_quantale = range_quantale + boolean_quantale

begin

subclass range_boolean_monoid
  by (standard, simp add: ldv'')

lemma fbox_eq: "ar.bbox x (r q) = Sup{r p |p. x \<cdot> r p \<le> (r q) \<cdot> x}"
  apply (rule Sup_eqI[symmetric])
  apply clarsimp
  using ar.ardual.fbox_demodalisation3 ar.ardual.fbox_simp apply auto[1]
  apply clarsimp
  by (metis ar.ardual.fbox_def ar.ardual.fbox_demodalisation3 eq_refl rar_ar)

lemma fdia_eq: "ar.bdia x (r p) = Inf{r q |q. (r p) \<cdot> x \<le> x \<cdot> r q}"
  apply (rule Inf_eqI[symmetric])
  apply clarsimp
  using ar.ars_r_def ar.ardual.fdemodalisation22 ar.ardual.kat_3_equiv_opp ar.ardual.kat_4_equiv_opp apply auto[1]
  apply clarsimp
  using ar.bdia_def ar.ardual.ds.fdemodalisation2 r_ar by fastforce

end

class modal_boolean_quantale = domain_boolean_quantale + range_boolean_quantale +
  assumes domrange' [simp]: "d (r x) = r x"
  and rangedom' [simp]: "r (d x) = d x"

begin

sublocale mka: modal_kleene_algebra "(\<squnion>)" "(\<cdot>)" 1 \<bottom> "(\<le>)" "(<)" star a ar
  by standard (simp_all add: ar_eq ad_eq)

end

no_notation fbox ("( |_] _)" [61,81] 82)
  and antidomain_semiringl_class.fbox ("( |_] _)" [61,81] 82)

notation ad.fbox ("( |_] _)" [61,81] 82)

subsection \<open>Recursion Rule\<close>

lemma recursion: "mono (f :: 'a \<Rightarrow> 'a :: domain_boolean_quantale) \<Longrightarrow> 
  (\<And>x. d p \<le> |x] d q \<Longrightarrow> d p \<le> |f x] d q) \<Longrightarrow>  d p \<le> |lfp f] d q"
  apply (erule lfp_ordinal_induct [where f=f], simp)
  by (auto simp: ad.addual.ardual.fbox_demodalisation3 Sup_distr Sup_distl intro: Sup_mono)

text \<open>We have already tested this rule in the context of test quantales~\cite{ArmstrongGS15}, which is based
on a formalisation of quantales that is currently not in the AFP. The two theories will be merged as
soon as the quantale is available in the AFP.\<close>

end
