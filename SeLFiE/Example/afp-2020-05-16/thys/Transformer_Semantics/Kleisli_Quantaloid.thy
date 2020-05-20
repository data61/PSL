(* 
  Title: The Quantaloid of Kleisli Arrows
  Author: Georg Struth 
  Maintainer: Georg Struth <g.struth@sheffield.ac.uk> 
*)

section \<open>The Quantaloid of Kleisli Arrows\<close>

theory Kleisli_Quantaloid

imports Kleisli_Transformers 
begin          

text \<open>This component formalises the quantalic structure of Kleisli arrows or state transformers, that is, 
the homset of the Kleisli category. Of course, by the previous isomorphisms, this is reflected at least 
partially in the Eilenberg-Moore algebras, via the comparison functor. The main result is that Kleisli arrows 
form a quantaloid, hence essentially a typed quantale. Some emphasis is on the star. This component thus complements 
that in which the quantaloid structure of Sup- and Inf-preserving transformers has been formalised.\<close>

text \<open>The first set of lemmas shows that Kleisli arrows form a typed dioid, that is, a typed idempotent semiring.\<close>

lemma ksup_assoc: "((f::'a \<Rightarrow> 'b set) \<squnion> g) \<squnion> h = f \<squnion> (g \<squnion> h)"
  unfolding sup.assoc by simp

lemma ksup_comm: "(f::'a => 'b set) \<squnion> g = g \<squnion> f"
  by (simp add: sup.commute)

lemma ksup_idem [simp]: "(f::'a \<Rightarrow> 'b set) \<squnion> f = f"
  by simp

lemma kcomp_distl: "f \<circ>\<^sub>K (g \<squnion> h) = (f \<circ>\<^sub>K g) \<squnion> (f \<circ>\<^sub>K h)"
  unfolding kcomp_klift fun_eq_iff comp_def sup_fun_def by (simp add: UN_Un_distrib klift_prop)

lemma kcomp_distr: "(f \<squnion> g) \<circ>\<^sub>K h = (f \<circ>\<^sub>K h) \<squnion> (g \<circ>\<^sub>K h)"
  by (simp add: kcomp_klift fun_eq_iff klift_def)

lemma ksup_zerol [simp]: "\<zeta> \<squnion> f = f"
  by force

lemma ksup_annil [simp]: "\<zeta> \<circ>\<^sub>K f = \<zeta>"
  by (force simp: kcomp_klift klift_def)

lemma ksup_annir [simp]: "f \<circ>\<^sub>K \<zeta> = \<zeta>"
  by (force simp: kcomp_klift klift_def)

text \<open>Associativity of Kleisli composition has already been proved.\<close>

text \<open>The next laws establish typed quantales --- or quantaloids.\<close>

lemma kSup_distl: "f \<circ>\<^sub>K (\<Squnion>G) = (\<Squnion>g \<in> G. f \<circ>\<^sub>K g)"
proof-
  have "f \<circ>\<^sub>K (\<Squnion>G) = ((klift \<circ> Sup) G) \<circ> f"
    by (simp add: kcomp_klift)
  also have "... = (\<Squnion>g \<in> G. (klift g)) \<circ> f"
    by (simp add: fbd_Sup_pres fun_eq_iff)
  also have "... = (\<Squnion>g \<in> G. (klift g) \<circ> f)"
    by auto
  finally show ?thesis
    by (simp add: kcomp_klift)
qed

lemma kSup_distr: "(\<Squnion>F) \<circ>\<^sub>K g = (\<Squnion>f \<in> F. f \<circ>\<^sub>K g)"
  unfolding kcomp_klift fun_eq_iff comp_def by (simp add: klift_prop)

lemma kcomp_isol: "f \<le> g \<Longrightarrow> h \<circ>\<^sub>K f \<le> h \<circ>\<^sub>K g"
  by (force simp: kcomp_klift le_fun_def klift_def)
  
lemma kcomp_isor: "f \<le> g \<Longrightarrow> f \<circ>\<^sub>K h \<le> g \<circ>\<^sub>K h"
  by (force simp: kcomp_klift le_fun_def klift_def)


subsection \<open>Kleene Star\<close>

text \<open>The Kleene star can be defined in any quantale or quantaloid by iteration. For Kleisli arrows,
laws for the star can be obtained via the isomorphism to binary relations, where the star is the reflexive-transitive
closure operation.\<close>

abbreviation "kpower \<equiv> kmon.power"

lemma r2f_pow: "\<F> (R ^^ i) = kpower (\<F> R) i"
  by (induct i, simp, metis power.power.power_Suc r2f_comp_pres relpow.simps(2) relpow_commute)

lemma f2r_kpower: "\<R> (kpower f i) = (\<R> f) ^^ i"
  by (induct i, simp, metis f2r2f_inv2 pointfree_idE r2f2r_inv1 r2f_pow)

definition "kstar f = (\<Squnion>i. kpower f i)"
                                              
lemma r2f_rtrancl_hom: "\<F> (rtrancl R) = kstar (\<F> R)"
proof-
  have "\<F> (rtrancl R) = \<F> (\<Union>i. R ^^ i)"
    by (simp add: full_SetCompr_eq rtrancl_is_UN_relpow)
  also have "... = (\<Squnion>i. kpower (\<F> R) i)"
    by (auto simp: r2f_Sup_pres_var r2f_pow)
  finally show ?thesis
    by (simp add: kstar_def)
qed

lemma r2f_rtrancl_hom_var: "\<F> \<circ> rtrancl = kstar \<circ> \<F>"
  by standard (simp add: r2f_rtrancl_hom)

lemma f2r_kstar_hom: "\<R> (kstar f) = rtrancl (\<R> f)"
  by (metis r2f_f2r_galois r2f_rtrancl_hom)

lemma f2r_kstar_hom_var: "\<R> \<circ> kstar = rtrancl \<circ> \<R>"
  by standard (simp add: f2r_kstar_hom)

lemma kstar_unfoldl_eq: "\<eta> \<squnion> f \<circ>\<^sub>K kstar f = kstar f"
proof -
  have "\<R> (kstar f) = (\<R> \<eta>) \<union> (\<R> f)\<^sup>* ; \<R> f"
    using f2r_kstar_hom rtrancl_unfold
    by (metis f2r_eta_pres)
  thus ?thesis
    by (metis f2r_kcomp_pres f2r_kstar_hom f2r_sup_pres r2f_inj_iff r_comp_rtrancl_eq)
qed

lemma kstar_unfoldl: "\<eta> \<squnion> f \<circ>\<^sub>K  kstar f \<le> kstar f"
  by (simp add: kstar_unfoldl_eq)

lemma kstar_unfoldr_eq: "\<eta> \<squnion> (kstar f) \<circ>\<^sub>K f = kstar f"
  by (metis (no_types) f2r2f_inv2 f2r_kcomp_pres f2r_kstar_hom kstar_unfoldl_eq pointfree_idE r_comp_rtrancl_eq)

lemma kstar_unfoldr: "\<eta> \<squnion> (kstar f) \<circ>\<^sub>K f \<le> kstar f"
  by (simp add: kstar_unfoldr_eq)

text \<open>Relational induction laws seem to be missing in Isabelle Main. So I derive functional laws directly.\<close>

lemma kpower_inductl: "f \<circ>\<^sub>K g \<le> g \<Longrightarrow> kpower f i \<circ>\<^sub>K g \<le> g"
  by (induct i, simp_all add: kcomp_assoc kcomp_isol order_subst2)

lemma kpower_inductl_var: "h \<squnion> f \<circ>\<^sub>K g \<le> g \<Longrightarrow> kpower f i \<circ>\<^sub>K h \<le> g"
proof -
  assume h1: "h \<squnion> f \<circ>\<^sub>K g \<le> g"
  then have h2: "f \<circ>\<^sub>K g \<le> g"
    using le_sup_iff by blast
  have "h \<le> g"
    using h1 by simp
  then show ?thesis
    using h2 kcomp_isol kpower_inductl order_trans by blast
qed

lemma kstar_inductl: "h \<squnion> f \<circ>\<^sub>K g \<le> g \<Longrightarrow> kstar f \<circ>\<^sub>K h \<le> g"
  apply (simp add: kstar_def kSup_distr, rule Sup_least)
  using kpower_inductl_var by fastforce   

lemma kpower_inductr: "g \<circ>\<^sub>K f \<le> g \<Longrightarrow> g \<circ>\<^sub>K kpower f i \<le> g"
  apply (induct i, simp_all)
  by (metis (mono_tags, lifting) dual_order.trans kcomp_assoc kcomp_isor)

lemma kpower_inductr_var: "h \<squnion> g \<circ>\<^sub>K f \<le> g \<Longrightarrow> h \<circ>\<^sub>K kpower f i \<le> g"
  by (metis (no_types) dual_order.trans kcomp_isor kpower_inductr le_sup_iff)

lemma kstar_inductr: "h \<squnion> g \<circ>\<^sub>K f \<le> g \<Longrightarrow> h \<circ>\<^sub>K kstar f \<le> g"
  apply (simp add: kstar_def kSup_distl, rule Sup_least)
  using kpower_inductr_var by fastforce

lemma kpower_prop: "f \<le> \<eta> \<Longrightarrow> kpower f i \<le> \<eta>"
  by (metis kcomp_idl kpower_inductr)

lemma kstar_prop: "f \<le> \<eta> \<Longrightarrow> kstar f \<le> \<eta>"
  by (simp add: SUP_le_iff kpower_prop kstar_def)


subsection \<open>Antidomain\<close>

text \<open>Next I define an antidomain operation and prove the axioms of antidomain semirings~\cite{GomesGHSW16,DesharnaisS11}.\<close>

definition "kad f = (\<lambda>x. if (f x = {}) then {x} else {})"

definition "ad_rel R = {(x,x) |x. \<not>(\<exists>y. (x,y) \<in> R)}"

lemma f2r_ad_fun_hom: "\<R> (kad f) = ad_rel (\<R> f)"
  apply (simp add: kad_def ad_rel_def f2r_def, safe)
  by simp_all (meson empty_iff singletonD)

lemma f2r_ad_fun_hom_var:"\<R> \<circ> kad = ad_rel \<circ> \<R>"
  by standard (simp add: f2r_ad_fun_hom)

lemma r2f_ad_rel_hom: "\<F> (ad_rel R) = kad (\<F> R)"
  by (force simp add: kad_def ad_rel_def r2f_def fun_eq_iff)

lemma r2f_ad_rel_hom_var:"\<F> \<circ> ad_rel = kad \<circ> \<F>"
  by standard (simp add: r2f_ad_rel_hom)

lemma ad_fun_as1 [simp]: "(kad f) \<circ>\<^sub>K f = \<zeta>"
  by (simp add: kad_def kcomp_def fun_eq_iff)

lemma ad_fun_as2 [simp]: "kad (f \<circ>\<^sub>K g) \<squnion> kad (f \<circ>\<^sub>K kad (kad g)) = kad (f \<circ>\<^sub>K kad (kad g))"
  by (force simp: kad_def kcomp_def fun_eq_iff)

lemma ad_fun_as3 [simp]: "kad (kad f) \<squnion> kad f = \<eta>"
  by (simp add: kad_def fun_eq_iff)

definition "set2fun X = (\<lambda>x. if (x \<in> X) then {x} else {})"

definition "p2fun = set2fun \<circ> Collect"

lemma ffb_ad_fun: "fb\<^sub>\<F> f X = {x. (kad (f \<circ>\<^sub>K kad (set2fun X))) x \<noteq> {}}" 
  unfolding ffb_prop_var klift_def kop_def fun_eq_iff comp_def f2r_def r2f_def converse_def kad_def kcomp_def set2fun_def
  by auto

lemma ffb_ad_fun2: "set2fun (fb\<^sub>\<F> f X) = kad (f \<circ>\<^sub>K kad (set2fun X))"
  by standard (subst ffb_ad_fun, subst set2fun_def, simp add: kad_def)

text \<open>The final statements check that the relational forward diamond is consistent with the Kleene-algebraic definition.\<close>

lemma fb_ad_rel: "fb\<^sub>\<R> R X = Domain (ad_rel (R ; ad_rel (Id_on X)))"
  unfolding rfb_def ffb_prop_var klift_def comp_def r2f_def kop_def f2r_def converse_def Domain_def Id_on_def ad_rel_def
  by auto

lemma fb_ad_rel2: "Id_on (fb\<^sub>\<R> R X) = ad_rel (R ; ad_rel (Id_on X))"
  unfolding rfb_def ffb_prop_var klift_def comp_def r2f_def kop_def f2r_def converse_def Domain_def Id_on_def ad_rel_def
  by auto

end

