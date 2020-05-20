(* 
  Title: Locale-Based Duality
  Author: Georg Struth 
  Maintainer:Georg Struth <g.struth@sheffield.ac.uk> 
*)

section \<open>Locale-Based Duality\<close>

theory Order_Lattice_Props_Loc
  imports Main 
          "HOL-Library.Lattice_Syntax"

begin

text \<open>This section explores order and lattice duality based on locales. Used within the context of a class or locale, 
this is very effective, though more opaque than the previous approach. Outside of such a context, however, it apparently
cannot be used for dualising theorems. Examples are properties of  functions between orderings or lattices.\<close>

definition Fix :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a set" where 
  "Fix f = {x. f x = x}"

context ord
begin

definition min_set :: "'a set \<Rightarrow> 'a set" where 
 "min_set X = {y \<in> X. \<forall>x \<in> X. x \<le> y \<longrightarrow> x = y}"

definition max_set :: "'a set \<Rightarrow> 'a set" where 
 "max_set X = {x \<in> X. \<forall>y \<in> X. x \<le> y \<longrightarrow> x = y}"

definition directed :: "'a set \<Rightarrow> bool" where
 "directed X = (\<forall>Y. finite Y \<and> Y \<subseteq> X \<longrightarrow> (\<exists>x \<in> X. \<forall>y \<in> Y. y \<le> x))"

definition filtered :: "'a set \<Rightarrow> bool" where
 "filtered X = (\<forall>Y. finite Y \<and> Y \<subseteq> X \<longrightarrow> (\<exists>x \<in> X. \<forall>y \<in> Y. x \<le> y))"

definition downset_set :: "'a set \<Rightarrow> 'a set" ("\<Down>") where
  "\<Down>X = {y. \<exists>x \<in> X. y \<le> x}"

definition upset_set :: "'a set \<Rightarrow> 'a set" ("\<Up>") where
 "\<Up>X = {y. \<exists>x \<in> X. x \<le> y}"

definition downset :: "'a \<Rightarrow> 'a set" ("\<down>") where 
  "\<down> = \<Down> \<circ> (\<lambda>x. {x})"

definition upset :: "'a \<Rightarrow> 'a set" ("\<up>") where 
  "\<up> = \<Up> \<circ> (\<lambda>x. {x})"

definition downsets :: "'a set set" where  
  "downsets = Fix \<Down>"
 
definition upsets :: "'a set set" where
  "upsets = Fix \<Up>"

abbreviation "downset_setp X \<equiv> X \<in> downsets"

abbreviation "upset_setp X \<equiv> X \<in> upsets"

definition ideals :: "'a set set" where
  "ideals = {X. X \<noteq> {} \<and> downset_setp X \<and> directed X}"

definition filters :: "'a  set set" where
  "filters = {X. X \<noteq> {} \<and> upset_setp X \<and> filtered X}"

abbreviation "idealp X \<equiv> X \<in> ideals"

abbreviation "filterp X \<equiv> X \<in> filters"

end

abbreviation Sup_pres :: "('a::Sup \<Rightarrow> 'b::Sup) \<Rightarrow> bool" where
  "Sup_pres f \<equiv> f \<circ> Sup = Sup \<circ> (`) f"

abbreviation Inf_pres :: "('a::Inf \<Rightarrow> 'b::Inf) \<Rightarrow> bool" where
  "Inf_pres f \<equiv> f \<circ> Inf = Inf \<circ> (`) f"

abbreviation sup_pres :: "('a::sup \<Rightarrow> 'b::sup) \<Rightarrow> bool" where
  "sup_pres f \<equiv> (\<forall>x y. f (x \<squnion> y) = f x \<squnion> f y)"

abbreviation inf_pres :: "('a::inf \<Rightarrow> 'b::inf) \<Rightarrow> bool" where
 "inf_pres f \<equiv> (\<forall>x y. f (x \<sqinter> y) = f x \<sqinter> f y)"

abbreviation bot_pres :: "('a::bot \<Rightarrow> 'b::bot) \<Rightarrow> bool" where
  "bot_pres f \<equiv> f \<bottom> = \<bottom>"

abbreviation top_pres :: "('a::top \<Rightarrow> 'b::top) \<Rightarrow> bool" where
  "top_pres f \<equiv> f \<top> = \<top>"

abbreviation Sup_dual :: "('a::Sup \<Rightarrow> 'b::Inf) \<Rightarrow> bool" where
  "Sup_dual f \<equiv> f \<circ> Sup = Inf \<circ> (`) f"

abbreviation Inf_dual :: "('a::Inf \<Rightarrow> 'b::Sup) \<Rightarrow> bool" where
  "Inf_dual f \<equiv> f \<circ> Inf = Sup \<circ> (`) f"

abbreviation sup_dual :: "('a::sup \<Rightarrow> 'b::inf) \<Rightarrow> bool" where
  "sup_dual f \<equiv> (\<forall>x y. f (x \<squnion> y) = f x \<sqinter> f y)"

abbreviation inf_dual :: "('a::inf \<Rightarrow> 'b::sup) \<Rightarrow> bool" where
 "inf_dual f \<equiv> (\<forall>x y. f (x \<sqinter> y) = f x \<squnion> f y)"

abbreviation bot_dual :: "('a::bot \<Rightarrow> 'b::top) \<Rightarrow> bool" where 
 "bot_dual f \<equiv> f \<bottom> = \<top>"

abbreviation top_dual :: "('a::top \<Rightarrow> 'b::bot) \<Rightarrow> bool" where 
  "top_dual f \<equiv> f \<top> = \<bottom>"


subsection \<open>Duality via Locales\<close>

sublocale ord \<subseteq> dual_ord: ord "(\<ge>)" "(>)"
  rewrites dual_max_set: "max_set = dual_ord.min_set"
  and dual_filtered: "filtered = dual_ord.directed"
  and dual_upset_set: "upset_set = dual_ord.downset_set"
  and dual_upset: "upset = dual_ord.downset"
  and dual_upsets: "upsets = dual_ord.downsets"
  and dual_filters: "filters = dual_ord.ideals"
       apply unfold_locales
  unfolding max_set_def ord.min_set_def fun_eq_iff apply blast
  unfolding filtered_def ord.directed_def apply simp 
  unfolding upset_set_def ord.downset_set_def apply simp
  apply (simp add: ord.downset_def ord.downset_set_def ord.upset_def ord.upset_set_def)
  unfolding upsets_def ord.downsets_def apply (metis ord.downset_set_def upset_set_def)
  unfolding filters_def ord.ideals_def Fix_def ord.downsets_def upsets_def ord.downset_set_def upset_set_def ord.directed_def filtered_def
  by simp

sublocale preorder \<subseteq> dual_preorder: preorder "(\<ge>)" "(>)"
  apply unfold_locales
  apply (simp add: less_le_not_le)
  apply simp
  using order_trans by blast

sublocale order \<subseteq> dual_order: order "(\<ge>)" "(>)"
  by (unfold_locales, simp)

sublocale lattice \<subseteq> dual_lattice: lattice sup "(\<ge>)" "(>)" inf
  by (unfold_locales, simp_all)

sublocale bounded_lattice \<subseteq> dual_bounded_lattice: bounded_lattice sup "(\<ge>)" "(>)" inf \<top> \<bottom>
  by (unfold_locales, simp_all)

sublocale boolean_algebra \<subseteq> dual_boolean_algebra: boolean_algebra "\<lambda>x y. x \<squnion> -y" uminus sup "(\<ge>)" "(>)" inf \<top> \<bottom>
  by (unfold_locales, simp_all add: inf_sup_distrib1)

sublocale complete_lattice \<subseteq> dual_complete_lattice: complete_lattice Sup Inf sup "(\<ge>)" "(>)" inf \<top> \<bottom>
  rewrites dual_gfp: "gfp = dual_complete_lattice.lfp"  
proof-
  show "class.complete_lattice Sup Inf sup (\<ge>) (>) inf \<top> \<bottom>"
    by (unfold_locales, simp_all add: Sup_upper Sup_least Inf_lower Inf_greatest)
  then interpret dual_complete_lattice: complete_lattice Sup Inf sup "(\<ge>)" "(>)" inf \<top> \<bottom>.
  show "gfp = dual_complete_lattice.lfp"  
    unfolding gfp_def dual_complete_lattice.lfp_def fun_eq_iff by simp
qed

context ord
begin

lemma dual_min_set: "min_set = dual_ord.max_set"
  by (simp add: dual_ord.dual_max_set)

lemma dual_directed: "directed = dual_ord.filtered"
  by (simp add:dual_ord.dual_filtered)

lemma dual_downset: "downset = dual_ord.upset"
  by (simp add: dual_ord.dual_upset)

lemma dual_downset_set: "downset_set = dual_ord.upset_set"
  by (simp add: dual_ord.dual_upset_set)

lemma dual_downsets: "downsets = dual_ord.upsets"
  by (simp add: dual_ord.dual_upsets)

lemma dual_ideals: "ideals = dual_ord.filters"
  by (simp add: dual_ord.dual_filters)

end

context complete_lattice
begin

lemma dual_lfp: "lfp = dual_complete_lattice.gfp"
  by (simp add: dual_complete_lattice.dual_gfp)

end

subsection \<open>Properties of Orderings, Again\<close>

context ord
begin

lemma directed_nonempty: "directed X \<Longrightarrow> X \<noteq> {}"
  unfolding directed_def by fastforce

lemma directed_ub: "directed X \<Longrightarrow> (\<forall>x \<in> X. \<forall>y \<in> X. \<exists>z \<in> X. x \<le> z \<and> y \<le> z)"
  by (meson empty_subsetI directed_def finite.emptyI finite_insert insert_subset order_refl)

lemma downset_set_prop: "\<Down> = Union \<circ> (`) \<down>"
  unfolding downset_set_def downset_def fun_eq_iff by fastforce

lemma downset_set_prop_var: "\<Down>X = (\<Union>x \<in> X. \<down>x)"
  by (simp add: downset_set_prop)

lemma downset_prop: "\<down>x = {y. y \<le> x}"
  unfolding downset_def downset_set_def fun_eq_iff comp_def by fastforce

end

context preorder
begin

lemma directed_prop: "X \<noteq> {} \<Longrightarrow> (\<forall>x \<in> X. \<forall>y \<in> X. \<exists>z \<in> X. x \<le> z \<and> y \<le> z) \<Longrightarrow> directed X"
proof-
  assume h1: "X \<noteq> {}"
  and h2: "\<forall>x \<in> X. \<forall>y \<in> X. \<exists>z \<in> X. x \<le> z \<and> y \<le> z"
  {fix Y
  have "finite Y \<Longrightarrow> Y \<subseteq> X \<Longrightarrow> (\<exists>x \<in> X. \<forall>y \<in> Y. y \<le> x)"
  proof (induct rule: finite_induct)
    case empty
    then show ?case
      using h1 by blast 
  next
    case (insert x F)
    then show ?case
      by (metis h2 insert_iff insert_subset order_trans) 
  qed}
  thus ?thesis
    by (simp add: directed_def)
qed

lemma directed_alt: "directed X = (X \<noteq> {} \<and> (\<forall>x \<in> X. \<forall>y \<in> X. \<exists>z \<in> X. x \<le> z \<and> y \<le> z))"
  by (metis directed_prop directed_nonempty directed_ub)

lemma downset_set_ext: "id \<le> \<Down>"
  unfolding le_fun_def id_def downset_set_def by auto 

lemma downset_set_iso: "mono \<Down>"
  unfolding mono_def downset_set_def by blast

lemma downset_set_idem [simp]: "\<Down> \<circ> \<Down> = \<Down>"
  unfolding fun_eq_iff downset_set_def comp_def using order_trans by auto

lemma downset_faithful: "\<down>x \<subseteq> \<down>y \<Longrightarrow> x \<le> y"
  by (simp add: downset_prop subset_eq)

lemma downset_iso_iff: "(\<down>x \<subseteq> \<down>y) = (x \<le> y)"
  using atMost_iff downset_prop order_trans by blast

lemma downset_directed_downset_var [simp]: "directed (\<Down>X) = directed X"
proof
  assume h1: "directed X"
  {fix Y
  assume h2: "finite Y" and h3: "Y \<subseteq> \<Down>X"
  hence "\<forall>y. \<exists>x. y \<in> Y \<longrightarrow> x \<in> X \<and>  y \<le> x"
    by (force simp: downset_set_def)
  hence "\<exists>f. \<forall>y. y \<in> Y \<longrightarrow>  f y \<in> X \<and> y \<le> f y"
    by (rule choice)
  hence "\<exists>f. finite (f ` Y) \<and> f ` Y \<subseteq> X \<and> (\<forall>y \<in> Y. y \<le> f y)"
    by (metis finite_imageI h2 image_subsetI)
  hence "\<exists>Z. finite Z \<and> Z \<subseteq> X \<and> (\<forall>y \<in> Y. \<exists> z \<in> Z. y \<le> z)"
    by fastforce
  hence "\<exists>Z. finite Z \<and> Z \<subseteq> X \<and> (\<forall>y \<in> Y. \<exists> z \<in> Z. y \<le> z) \<and> (\<exists>x \<in> X. \<forall> z \<in> Z. z \<le> x)"
    by (metis directed_def h1)
  hence "\<exists>x \<in> X. \<forall>y \<in> Y. y \<le> x"
    by (meson order_trans)}
  thus "directed (\<Down>X)"
    unfolding directed_def downset_set_def by fastforce
next 
  assume "directed (\<Down>X)"
  thus "directed X"
    unfolding directed_def downset_set_def 
    apply clarsimp
    by (smt Ball_Collect order_refl order_trans subsetCE)
qed

lemma downset_directed_downset [simp]: "directed \<circ> \<Down> = directed"
  unfolding fun_eq_iff comp_def by simp

lemma directed_downset_ideals: "directed (\<Down>X) = (\<Down>X \<in> ideals)"
  by (metis (mono_tags, lifting) Fix_def comp_apply directed_alt downset_set_idem downsets_def ideals_def mem_Collect_eq)

end

lemma downset_iso: "mono (\<down>::'a::order \<Rightarrow> 'a set)"
  by (simp add: downset_iso_iff mono_def)

context order
begin

lemma downset_inj: "inj \<down>"
  by (metis injI downset_iso_iff eq_iff)

end

context lattice
begin

lemma lat_ideals: "X \<in> ideals = (X \<noteq> {} \<and> X \<in> downsets \<and> (\<forall>x \<in> X. \<forall> y \<in> X. x \<squnion> y \<in> X))"
  unfolding ideals_def directed_alt downsets_def Fix_def downset_set_def 
  by (clarsimp, smt sup.cobounded1 sup.orderE sup.orderI sup_absorb2 sup_left_commute mem_Collect_eq)

end

context bounded_lattice
begin

lemma bot_ideal: "X \<in> ideals \<Longrightarrow> \<bottom> \<in> X"
  unfolding ideals_def downsets_def Fix_def downset_set_def by fastforce

end

context complete_lattice
begin

lemma Sup_downset_id [simp]: "Sup \<circ> \<down> = id"
  using Sup_atMost atMost_def downset_prop by fastforce

lemma downset_Sup_id: "id \<le> \<down> \<circ> Sup"
  by (simp add: Sup_upper downset_prop le_funI subsetI)

lemma Inf_Sup_var: "\<Squnion>(\<Inter>x \<in> X. \<down>x) = \<Sqinter>X"
  unfolding downset_prop by (simp add: Collect_ball_eq Inf_eq_Sup)

lemma Inf_pres_downset_var: "(\<Inter>x \<in> X. \<down>x) = \<down>(\<Sqinter>X)"
  unfolding downset_prop by (safe, simp_all add: le_Inf_iff)

end

lemma lfp_in_Fix: 
  fixes f :: "'a::complete_lattice \<Rightarrow> 'a"
  shows "mono f \<Longrightarrow> lfp f \<in> Fix f"
  using Fix_def lfp_unfold by fastforce

lemma gfp_in_Fix: 
  fixes f :: "'a::complete_lattice \<Rightarrow> 'a"
  shows "mono f \<Longrightarrow> gfp f \<in> Fix f"
  using Fix_def gfp_unfold by fastforce

lemma nonempty_Fix: 
  fixes f :: "'a::complete_lattice \<Rightarrow> 'a"
  shows "mono f \<Longrightarrow> Fix f \<noteq> {}"
  using lfp_in_Fix by fastforce


subsection \<open>Dual Properties of Orderings from Locales\<close>

text \<open>These properties can be proved very smoothly overall. But only within the context of a class
or locale!\<close>

context ord
begin

lemma filtered_nonempty: "filtered X \<Longrightarrow> X \<noteq> {}"
  by (simp add: dual_filtered dual_ord.directed_nonempty)

lemma filtered_lb: "filtered X \<Longrightarrow> (\<forall>x \<in> X. \<forall>y \<in> X. \<exists>z \<in> X. z \<le> x \<and> z \<le> y)"
  by (simp add: dual_filtered dual_ord.directed_ub)

lemma upset_set_prop: "\<Up> = Union \<circ> (`) \<up>"
  by (simp add: dual_ord.downset_set_prop dual_upset dual_upset_set)

lemma upset_set_prop_var: "\<Up>X = (\<Union>x \<in> X. \<up>x)"
  by (simp add: dual_ord.downset_set_prop_var dual_upset dual_upset_set)

lemma upset_prop: "\<up>x = {y. x \<le> y}"
  by (simp add: dual_ord.downset_prop dual_upset)

end

context preorder
begin

lemma filtered_prop: "X \<noteq> {} \<Longrightarrow> (\<forall>x \<in> X. \<forall>y \<in> X. \<exists>z \<in> X. z \<le> x \<and> z \<le> y) \<Longrightarrow> filtered X"
  by (simp add: dual_filtered dual_preorder.directed_prop)

lemma filtered_alt: "filtered X = (X \<noteq> {} \<and> (\<forall>x \<in> X. \<forall>y \<in> X. \<exists>z \<in> X. z \<le> x \<and> z \<le> y))"
  by (simp add: dual_filtered dual_preorder.directed_alt)

lemma upset_set_ext: "id \<le> \<Up>"
  by (simp add: dual_preorder.downset_set_ext dual_upset_set)

lemma upset_set_anti: "mono \<Up>"
  by (simp add: dual_preorder.downset_set_iso dual_upset_set) 

lemma up_set_idem [simp]: "\<Up> \<circ> \<Up> = \<Up>"
  by (simp add: dual_upset_set)

lemma upset_faithful: "\<up>x \<subseteq> \<up>y \<Longrightarrow> y \<le> x"
  by (metis dual_preorder.downset_faithful dual_upset)

lemma upset_anti_iff: "(\<up>y \<subseteq> \<up>x) = (x \<le> y)"
  by (simp add: dual_preorder.downset_iso_iff dual_upset)

lemma upset_filtered_upset [simp]: "filtered \<circ> \<Up> = filtered"
  by (simp add: dual_filtered dual_upset_set)

lemma filtered_upset_filters: "filtered (\<Up>X) = (\<Up>X \<in> filters)"
  using dual_filtered dual_preorder.directed_downset_ideals dual_upset_set ord.dual_filters by fastforce

end

context order
begin

lemma upset_inj: "inj \<up>"
  by (simp add: dual_order.downset_inj dual_upset)

end

context lattice
begin

lemma lat_filters: "X \<in> filters = (X \<noteq> {} \<and> X \<in> upsets \<and> (\<forall>x \<in> X. \<forall> y \<in> X. x \<sqinter> y \<in> X))"
  by (simp add: dual_filters dual_lattice.lat_ideals dual_ord.downsets_def dual_upset_set upsets_def)

end

context bounded_lattice
begin

lemma top_filter: "X \<in> filters \<Longrightarrow> \<top> \<in> X"
  by (simp add: dual_bounded_lattice.bot_ideal dual_filters)

end

context complete_lattice
begin

lemma Inf_upset_id [simp]: "Inf \<circ> \<up> = id"
  by (simp add:  dual_upset)

lemma upset_Inf_id: "id \<le> \<up> \<circ> Inf"
  by (simp add: dual_complete_lattice.downset_Sup_id dual_upset)

lemma Sup_Inf_var: " \<Sqinter>(\<Inter>x \<in> X. \<up>x) = \<Squnion>X"
  by (simp add: dual_complete_lattice.Inf_Sup_var dual_upset)

lemma Sup_dual_upset_var: "(\<Inter>x \<in> X. \<up>x) = \<up>(\<Squnion>X)"
  by (simp add: dual_complete_lattice.Inf_pres_downset_var dual_upset)

end

subsection \<open>Examples that Do Not Dualise\<close>

lemma upset_anti: "antimono (\<up>::'a::order \<Rightarrow> 'a set)"
  by (simp add: antimono_def upset_anti_iff)

context complete_lattice 
begin

lemma fSup_unfold: "(f::nat \<Rightarrow> 'a) 0 \<squnion> (\<Squnion>n. f (Suc n)) = (\<Squnion>n. f n)"
  apply (intro antisym sup_least)
    apply (rule Sup_upper, force)
   apply (rule Sup_mono, force)
  apply (safe intro!: Sup_least)
 by (case_tac n, simp_all add: Sup_upper le_supI2)


lemma fInf_unfold: "(f::nat \<Rightarrow> 'a) 0 \<sqinter> (\<Sqinter>n. f (Suc n)) = (\<Sqinter>n. f n)"
  apply (intro antisym inf_greatest)
  apply (rule Inf_greatest, safe)
  apply (case_tac n)
   apply simp_all
  using Inf_lower inf.coboundedI2 apply force
   apply (simp add: Inf_lower)
  by (auto intro: Inf_mono)

end

lemma fun_isol: "mono f \<Longrightarrow> mono ((\<circ>) f)"
  by (simp add: le_fun_def mono_def)

lemma fun_isor: "mono f \<Longrightarrow> mono (\<lambda>x. x \<circ> f)"
  by (simp add: le_fun_def mono_def)

lemma Sup_sup_pres: 
  fixes f :: "'a::complete_lattice \<Rightarrow> 'b::complete_lattice"
  shows "Sup_pres f \<Longrightarrow> sup_pres f"
  by (metis (no_types, hide_lams) Sup_empty Sup_insert comp_apply image_insert sup_bot.right_neutral)

lemma Inf_inf_pres: 
  fixes f :: "'a::complete_lattice \<Rightarrow> 'b::complete_lattice"
  shows"Inf_pres f \<Longrightarrow> inf_pres f"
  by (smt INF_insert comp_eq_elim dual_complete_lattice.Sup_empty dual_complete_lattice.Sup_insert inf_top.right_neutral)

lemma Sup_bot_pres: 
  fixes f :: "'a::complete_lattice \<Rightarrow> 'b::complete_lattice"
  shows "Sup_pres f \<Longrightarrow> bot_pres f"
  by (metis SUP_empty Sup_empty comp_eq_elim)

lemma Inf_top_pres: 
  fixes f :: "'a::complete_lattice \<Rightarrow> 'b::complete_lattice"
  shows "Inf_pres f \<Longrightarrow> top_pres f"
  by (metis INF_empty comp_eq_elim dual_complete_lattice.Sup_empty)

context complete_lattice
begin

lemma iso_Inf_subdistl: 
  assumes "mono (f::'a \<Rightarrow> 'b::complete_lattice)"
  shows "f \<circ> Inf \<le> Inf \<circ> (`) f"
  by (simp add: assms complete_lattice_class.le_Inf_iff le_funI Inf_lower monoD)

lemma iso_Sup_supdistl: 
  assumes "mono (f::'a \<Rightarrow> 'b::complete_lattice)"
  shows "Sup \<circ> (`) f \<le> f \<circ> Sup"
  by (simp add: assms complete_lattice_class.SUP_le_iff le_funI dual_complete_lattice.Inf_lower monoD)

lemma Inf_subdistl_iso: 
  fixes f :: "'a \<Rightarrow> 'b::complete_lattice"
  shows "f \<circ> Inf \<le> Inf \<circ> (`) f \<Longrightarrow> mono f"
  unfolding mono_def le_fun_def comp_def by (metis complete_lattice_class.le_INF_iff Inf_atLeast atLeast_iff)

lemma Sup_supdistl_iso: 
  fixes f :: "'a \<Rightarrow> 'b::complete_lattice"
  shows "Sup \<circ> (`) f \<le> f \<circ> Sup \<Longrightarrow> mono f"
  unfolding mono_def le_fun_def comp_def by (metis complete_lattice_class.SUP_le_iff Sup_atMost atMost_iff)

lemma supdistl_iso: 
  fixes f :: "'a \<Rightarrow> 'b::complete_lattice"
  shows "(Sup \<circ> (`) f \<le> f \<circ> Sup) = mono f"
  using Sup_supdistl_iso iso_Sup_supdistl by force

lemma subdistl_iso: 
  fixes f :: "'a \<Rightarrow> 'b::complete_lattice"
  shows "(f \<circ> Inf \<le> Inf \<circ> (`) f) = mono f"
  using Inf_subdistl_iso iso_Inf_subdistl by force

end

lemma fSup_distr: "Sup_pres (\<lambda>x. x \<circ> f)"
  unfolding fun_eq_iff comp_def
  by (smt Inf.INF_cong SUP_apply Sup_apply)

lemma fSup_distr_var: "\<Squnion>F \<circ> g = (\<Squnion>f \<in> F. f \<circ> g)"
  unfolding fun_eq_iff comp_def
  by (smt Inf.INF_cong SUP_apply Sup_apply)

lemma fInf_distr: "Inf_pres (\<lambda>x. x \<circ> f)"
  unfolding fun_eq_iff comp_def
  by (smt INF_apply Inf.INF_cong Inf_apply)

lemma fInf_distr_var: "\<Sqinter>F \<circ> g = (\<Sqinter>f \<in> F. f \<circ> g)"
  unfolding fun_eq_iff comp_def
  by (smt INF_apply Inf.INF_cong Inf_apply)

lemma fSup_subdistl: 
  assumes "mono (f::'a::complete_lattice \<Rightarrow> 'b::complete_lattice)"
  shows "Sup \<circ> (`) ((\<circ>) f) \<le> (\<circ>) f \<circ> Sup"
  using assms by (simp add: SUP_least Sup_upper le_fun_def monoD image_comp)

lemma fSup_subdistl_var: 
  fixes f :: "'a::complete_lattice \<Rightarrow> 'b::complete_lattice"
  shows  "mono f \<Longrightarrow> (\<Squnion>g \<in> G. f \<circ> g) \<le> f \<circ> \<Squnion>G"
  by (simp add: SUP_least Sup_upper le_fun_def monoD image_comp)

lemma fInf_subdistl: 
  fixes f :: "'a::complete_lattice \<Rightarrow> 'b::complete_lattice"
  shows  "mono f \<Longrightarrow> (\<circ>) f \<circ> Inf \<le> Inf \<circ> (`) ((\<circ>) f)"
  by (simp add: INF_greatest Inf_lower le_fun_def monoD image_comp)

lemma fInf_subdistl_var: 
  fixes f :: "'a::complete_lattice \<Rightarrow> 'b::complete_lattice"
  shows "mono f \<Longrightarrow> f \<circ> \<Sqinter>G \<le> (\<Sqinter>g \<in> G. f \<circ> g)"
  by (simp add: INF_greatest Inf_lower le_fun_def monoD image_comp)

lemma Inf_pres_downset: "Inf_pres (\<down>::'a::complete_lattice \<Rightarrow> 'a set)"
  unfolding downset_prop fun_eq_iff comp_def
  by (safe, simp_all add: le_Inf_iff)
 
lemma Sup_dual_upset: "Sup_dual (\<up>::'a::complete_lattice \<Rightarrow> 'a set)"
  unfolding upset_prop fun_eq_iff comp_def
  by (safe, simp_all add: Sup_le_iff)

text \<open>This approach could probably be combined with the explicit functor-based one. This may be good for proofs, but seems conceptually rather ugly.\<close>

end