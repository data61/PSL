(* 
  Title: Properties of Orderings and Lattices
  Author: Georg Struth 
  Maintainer: Georg Struth <g.struth@sheffield.ac.uk> 
*)

section \<open>Properties of Orderings and Lattices\<close>

theory Order_Lattice_Props
  imports Order_Duality

begin

subsection \<open>Basic Definitions for Orderings and Lattices\<close>

text \<open>The first definition is for order morphisms --- isotone (order-preserving, monotone) functions. 
An order isomorphism is an order-preserving bijection. This should be defined in the class ord, but mono requires order.\<close>

definition ord_homset :: "('a::order \<Rightarrow> 'b::order) set" where
 "ord_homset = {f::'a::order \<Rightarrow> 'b::order. mono f}"

definition ord_embed :: "('a::order \<Rightarrow> 'b::order) \<Rightarrow> bool" where
 "ord_embed f = (\<forall>x y. f x \<le> f y \<longleftrightarrow> x \<le> y)"

definition ord_iso :: "('a::order \<Rightarrow> 'b::order) \<Rightarrow> bool" where
  "ord_iso = bij \<sqinter> mono \<sqinter> (mono \<circ> the_inv)"

lemma ord_embed_alt: "ord_embed f = (mono f \<and> (\<forall>x y. f x \<le> f y \<longrightarrow> x \<le> y))"
  using mono_def ord_embed_def by auto

lemma ord_embed_homset: "ord_embed f \<Longrightarrow> f \<in> ord_homset"
  by (simp add: mono_def ord_embed_def ord_homset_def)

lemma ord_embed_inj: "ord_embed f \<Longrightarrow> inj f"
  unfolding ord_embed_def inj_def by (simp add: eq_iff)

lemma ord_iso_ord_embed: "ord_iso f \<Longrightarrow> ord_embed f"
  unfolding ord_iso_def ord_embed_def bij_def inj_def mono_def
  by (clarsimp, metis inj_def the_inv_f_f)

lemma ord_iso_alt: "ord_iso f = (ord_embed f \<and> surj f)"
  unfolding ord_iso_def ord_embed_def surj_def bij_def inj_def mono_def 
  apply safe
  by simp_all (metis eq_iff inj_def the_inv_f_f)+

lemma ord_iso_the_inv: "ord_iso f \<Longrightarrow> mono (the_inv f)"
  by (simp add: ord_iso_def)

lemma ord_iso_inv1: "ord_iso f \<Longrightarrow> (the_inv f) \<circ> f = id"
  using ord_embed_inj ord_iso_ord_embed the_inv_into_f_f by fastforce

lemma ord_iso_inv2: "ord_iso f \<Longrightarrow> f \<circ> (the_inv f) = id"
  using f_the_inv_into_f ord_embed_inj ord_iso_alt by fastforce

typedef (overloaded) ('a,'b) ord_homset = "ord_homset::('a::order \<Rightarrow> 'b::order) set" 
  by (force simp: ord_homset_def mono_def) 

setup_lifting type_definition_ord_homset 

text \<open>The next definition is for the set of fixpoints of a given function. It is important in the context of orders,
for instance for proving Tarski's fixpoint theorem, but does not really belong here.\<close>

definition Fix :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a set" where 
  "Fix f = {x. f x = x}"

lemma retraction_prop: "f \<circ> f = f \<Longrightarrow> f x = x \<longleftrightarrow> x \<in> range f"
  by (metis comp_apply f_inv_into_f rangeI)

lemma retraction_prop_fix: "f \<circ> f = f \<Longrightarrow> range f = Fix f"
  unfolding Fix_def using retraction_prop by fastforce

lemma Fix_map_dual: "Fix \<circ> \<partial>\<^sub>F = (`) \<partial> \<circ> Fix"
  unfolding Fix_def map_dual_def comp_def fun_eq_iff
  by (smt Collect_cong invol_dual pointfree_idE setcompr_eq_image)

lemma Fix_map_dual_var: "Fix (\<partial>\<^sub>F f) = \<partial> ` (Fix f)"
  by (metis Fix_map_dual o_def)

lemma gfp_dual: "(\<partial>::'a::complete_lattice_with_dual \<Rightarrow> 'a) \<circ> gfp = lfp \<circ> \<partial>\<^sub>F"
proof-
  {fix f:: "'a \<Rightarrow> 'a"
  have "\<partial> (gfp f) = \<partial> (\<Squnion>{u. u \<le> f u})"
    by (simp add: gfp_def)
  also have "... = \<Sqinter>(\<partial> ` {u. u \<le> f u})"
    by (simp add: Sup_dual_def_var)
  also have "... = \<Sqinter>{\<partial> u |u. u \<le> f u}"
    by (simp add: setcompr_eq_image)
  also have "... = \<Sqinter>{u |u. (\<partial>\<^sub>F f) u \<le> u}"
    by (metis (no_types, hide_lams) dual_dual_ord dual_iff map_dual_def o_def)
  finally have "\<partial> (gfp f) = lfp (\<partial>\<^sub>F f)"
    by (metis lfp_def)}
  thus ?thesis
    by auto
qed

lemma gfp_dual_var: 
  fixes f :: "'a::complete_lattice_with_dual \<Rightarrow> 'a"
  shows "\<partial> (gfp f) = lfp (\<partial>\<^sub>F f)"
  using comp_eq_elim gfp_dual by blast

lemma gfp_to_lfp: "gfp = (\<partial>::'a::complete_lattice_with_dual \<Rightarrow> 'a) \<circ> lfp \<circ> \<partial>\<^sub>F"
  by (simp add: comp_assoc fun_dual2 gfp_dual)

lemma gfp_to_lfp_var: 
  fixes f :: "'a::complete_lattice_with_dual \<Rightarrow> 'a"
  shows "gfp f = \<partial> (lfp (\<partial>\<^sub>F f))"
  by (metis gfp_dual_var invol_dual_var)

lemma lfp_dual: "(\<partial>::'a::complete_lattice_with_dual \<Rightarrow> 'a) \<circ> lfp = gfp \<circ> \<partial>\<^sub>F"
  by (simp add: comp_assoc gfp_to_lfp map_dual_invol)

lemma lfp_dual_var: 
  fixes f :: "'a::complete_lattice_with_dual \<Rightarrow> 'a"
  shows "\<partial> (lfp f) = gfp (map_dual f)"
  using comp_eq_dest_lhs lfp_dual by fastforce

lemma lfp_to_gfp: "lfp = (\<partial>::'a::complete_lattice_with_dual \<Rightarrow> 'a) \<circ> gfp \<circ> \<partial>\<^sub>F"
  by (simp add: comp_assoc gfp_dual map_dual_invol)

lemma lfp_to_gfp_var: 
  fixes f :: "'a::complete_lattice_with_dual \<Rightarrow> 'a"
  shows "lfp f = \<partial> (gfp (\<partial>\<^sub>F f))"
  by (metis invol_dual_var lfp_dual_var)

lemma lfp_in_Fix: 
  fixes f :: "'a::complete_lattice \<Rightarrow> 'a"
  shows "mono f \<Longrightarrow> lfp f \<in> Fix f"
  by (metis (mono_tags, lifting) Fix_def lfp_unfold mem_Collect_eq)

lemma gfp_in_Fix: 
  fixes f :: "'a::complete_lattice \<Rightarrow> 'a"
  shows "mono f \<Longrightarrow> gfp f \<in> Fix f"
  by (metis (mono_tags, lifting) Fix_def gfp_unfold mem_Collect_eq)

lemma nonempty_Fix: 
  fixes f :: "'a::complete_lattice \<Rightarrow> 'a"
  shows "mono f \<Longrightarrow> Fix f \<noteq> {}"
  using lfp_in_Fix by fastforce


text \<open>Next the minimal and maximal elements of an ordering are defined.\<close>

context ord
begin

definition min_set :: "'a set \<Rightarrow> 'a set" where 
  "min_set X = {y \<in> X. \<forall>x \<in> X. x \<le> y \<longrightarrow> x = y}"

definition max_set :: "'a set \<Rightarrow> 'a set" where 
  "max_set X = {x \<in> X. \<forall>y \<in> X. x \<le> y \<longrightarrow> x = y}"

end

context ord_with_dual
begin

lemma min_max_set_dual: "(`) \<partial> \<circ> min_set = max_set \<circ> (`) \<partial>"  
  unfolding max_set_def min_set_def fun_eq_iff comp_def 
  apply safe
  using dual_dual_ord inj_dual_iff by auto

lemma min_max_set_dual_var: "\<partial> ` (min_set X) = max_set (\<partial> ` X)"
  using comp_eq_dest min_max_set_dual by fastforce  

lemma max_min_set_dual: "(`) \<partial> \<circ> max_set = min_set \<circ> (`) \<partial>"
  by (metis (no_types, hide_lams) comp_id fun.map_comp id_comp image_dual min_max_set_dual)  

lemma min_to_max_set: "min_set = (`) \<partial> \<circ> max_set \<circ> (`) \<partial>"
  by (metis comp_id image_dual max_min_set_dual o_assoc)

lemma max_min_set_dual_var: "\<partial> ` (max_set X) = min_set (\<partial> ` X)"
  using comp_eq_dest max_min_set_dual by fastforce

lemma min_to_max_set_var: "min_set X = \<partial> ` (max_set (\<partial> ` X))"
  by (simp add: max_min_set_dual_var pointfree_idE)

end

text \<open>Next, directed and filtered sets, upsets, downsets, filters and ideals in posets are defined.\<close>

context ord
begin

definition directed :: "'a set \<Rightarrow> bool" where
 "directed X = (\<forall>Y. finite Y \<and> Y \<subseteq> X \<longrightarrow> (\<exists>x \<in> X. \<forall>y \<in> Y. y \<le> x))"

definition filtered :: "'a set \<Rightarrow> bool" where
 "filtered X = (\<forall>Y. finite Y \<and> Y \<subseteq> X \<longrightarrow> (\<exists>x \<in> X. \<forall>y \<in> Y. x \<le> y))"

definition downset_set :: "'a set \<Rightarrow> 'a set" ("\<Down>") where
  "\<Down>X = {y. \<exists>x \<in> X. y \<le> x}"

definition upset_set :: "'a set \<Rightarrow> 'a set" ("\<Up>") where
 "\<Up>X = {y. \<exists>x \<in> X. x \<le> y}"

definition downset :: "'a \<Rightarrow> 'a set" ("\<down>") where 
  "\<down> = \<Down> \<circ> \<eta>"

definition upset :: "'a \<Rightarrow> 'a set" ("\<up>") where 
  "\<up> = \<Up> \<circ> \<eta>"

definition downsets :: "'a set set" where  
  "downsets = Fix \<Down>"
 
definition upsets :: "'a set set" where
  "upsets = Fix \<Up>"

definition "downclosed_set X = (X \<in> downsets)"

definition "upclosed_set X = (X \<in> upsets)"

definition ideals :: "'a set set" where
  "ideals = {X. X \<noteq> {} \<and> downclosed_set X \<and> directed X}"

definition filters :: "'a set set" where
  "filters = {X. X \<noteq> {} \<and> upclosed_set X \<and> filtered X}"

abbreviation "idealp X \<equiv> X \<in> ideals"

abbreviation "filterp X \<equiv> X \<in> filters"

end

text \<open>These notions are pair-wise dual.\<close>

text \<open>Filtered and directed sets are dual.\<close>

context ord_with_dual
begin

lemma filtered_directed_dual: "filtered \<circ> (`) \<partial> = directed"
  unfolding filtered_def directed_def fun_eq_iff comp_def
  apply clarsimp
  apply safe
   apply (meson finite_imageI imageI image_mono dual_dual_ord)
  by (smt finite_subset_image imageE ord_dual)

lemma directed_filtered_dual: "directed \<circ> (`) \<partial> = filtered"
  using filtered_directed_dual by (metis comp_id image_dual o_assoc) 

lemma filtered_to_directed: "filtered X = directed (\<partial> ` X)"
  by (metis comp_apply directed_filtered_dual)

text \<open>Upsets and downsets are dual.\<close>

lemma downset_set_upset_set_dual: "(`) \<partial> \<circ> \<Down> = \<Up> \<circ> (`) \<partial>"
  unfolding downset_set_def upset_set_def fun_eq_iff comp_def
  apply safe
   apply (meson image_eqI ord_dual)
  by (clarsimp, metis (mono_tags, lifting) dual_iff image_iff mem_Collect_eq ord_dual)

lemma upset_set_downset_set_dual: "(`) \<partial> \<circ> \<Up> = \<Down> \<circ> (`) \<partial>"
  using downset_set_upset_set_dual by (metis (no_types, hide_lams) comp_id id_comp image_dual o_assoc)

lemma upset_set_to_downset_set: "\<Up> = (`) \<partial> \<circ> \<Down> \<circ> (`) \<partial>"
  by (simp add: comp_assoc downset_set_upset_set_dual)

lemma upset_set_to_downset_set2: "\<Up> X = \<partial> ` (\<Down> (\<partial> ` X))"
  by (simp add: upset_set_to_downset_set)

lemma downset_upset_dual: "(`) \<partial> \<circ> \<down> = \<up> \<circ> \<partial>"
  using downset_def upset_def upset_set_to_downset_set by fastforce

lemma upset_to_downset: "(`) \<partial> \<circ> \<up> = \<down> \<circ> \<partial>"
  by (metis comp_assoc id_apply ord.downset_def ord.upset_def power_set_func_nat_trans upset_set_downset_set_dual)

lemma upset_to_downset2: "\<up> = (`) \<partial> \<circ> \<down> \<circ> \<partial>"
  by (simp add: comp_assoc downset_upset_dual)

lemma upset_to_downset3: "\<up> x = \<partial> ` (\<down> (\<partial> x))"
  by (simp add: upset_to_downset2)

lemma downsets_upsets_dual: "(X \<in> downsets) = (\<partial> ` X \<in> upsets)"
  unfolding downsets_def upsets_def Fix_def
  by (smt comp_eq_dest downset_set_upset_set_dual image_inv_f_f inj_dual mem_Collect_eq)

lemma downset_setp_upset_setp_dual: "upclosed_set \<circ> (`) \<partial> = downclosed_set"
  unfolding downclosed_set_def upclosed_set_def using downsets_upsets_dual by fastforce

lemma upsets_to_downsets: "(X \<in> upsets) = (\<partial> ` X \<in> downsets)"
  by (simp add: downsets_upsets_dual image_comp)

lemma upset_setp_downset_setp_dual: "downclosed_set \<circ> (`) \<partial> = upclosed_set"
  by (metis comp_id downset_setp_upset_setp_dual image_dual o_assoc)

text \<open>Filters and ideals are dual.\<close>

lemma ideals_filters_dual: "(X \<in> ideals) = ((\<partial> ` X) \<in> filters)"
  by (smt comp_eq_dest_lhs directed_filtered_dual image_inv_f_f image_is_empty inv_unique_comp filters_def ideals_def inj_dual invol_dual mem_Collect_eq upset_setp_downset_setp_dual)

lemma idealp_filterp_dual: "idealp = filterp \<circ> (`) \<partial>"
  unfolding fun_eq_iff by (simp add: ideals_filters_dual)

lemma filters_to_ideals: "(X \<in> filters) = ((\<partial> ` X) \<in> ideals)"
  by (simp add: ideals_filters_dual image_comp)

lemma filterp_idealp_dual: "filterp = idealp \<circ> (`) \<partial>"
  unfolding fun_eq_iff by (simp add: filters_to_ideals)

end

subsection \<open>Properties of Orderings\<close>

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
  unfolding downset_def downset_set_def fun_eq_iff by fastforce

lemma downset_prop2: "y \<le> x \<Longrightarrow> y \<in> \<down>x"
  by (simp add: downset_prop)

lemma ideals_downsets: "X \<in> ideals \<Longrightarrow> X \<in> downsets"
  by (simp add: downclosed_set_def ideals_def)

lemma ideals_directed: "X \<in> ideals \<Longrightarrow> directed X"
  by (simp add: ideals_def)

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

lemma downset_set_prop_var2: "x \<in> \<Down>X \<Longrightarrow> y \<le> x \<Longrightarrow> y \<in> \<Down>X"
  unfolding downset_set_def using order_trans by blast

lemma downclosed_set_iff: "downclosed_set X = (\<forall>x \<in> X. \<forall>y. y \<le> x \<longrightarrow> y \<in> X)"
  unfolding downclosed_set_def downsets_def Fix_def downset_set_def by auto

lemma downclosed_downset_set: "downclosed_set (\<Down>X)"
  by (simp add: downclosed_set_iff downset_set_prop_var2 downset_def)

lemma downclosed_downset: "downclosed_set (\<down>x)"
  by (simp add: downclosed_downset_set downset_def)
 
lemma downset_set_ext: "id \<le> \<Down>"
  unfolding le_fun_def id_def downset_set_def by auto 

lemma downset_set_iso: "mono \<Down>"
  unfolding mono_def downset_set_def by blast

lemma downset_set_idem [simp]: "\<Down> \<circ> \<Down> = \<Down>"
  unfolding fun_eq_iff downset_set_def using order_trans by auto

lemma downset_faithful: "\<down>x \<subseteq> \<down>y \<Longrightarrow> x \<le> y"
  by (simp add: downset_prop subset_eq)

lemma downset_iso_iff: "(\<down>x \<subseteq> \<down>y) = (x \<le> y)"
  using atMost_iff downset_prop order_trans by blast

text \<open>The following proof uses the Axiom of Choice.\<close>

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
  unfolding fun_eq_iff by simp

lemma directed_downset_ideals: "directed (\<Down>X) = (\<Down>X \<in> ideals)"
  by (metis (mono_tags, lifting) CollectI Fix_def directed_alt downset_set_idem downclosed_set_def downsets_def ideals_def o_def ord.ideals_directed)

lemma downclosed_Fix: "downclosed_set X = (\<Down>X = X)"
  by (metis (mono_tags, lifting) CollectD Fix_def downclosed_downset_set downclosed_set_def downsets_def)
  
end

lemma downset_iso: "mono (\<down>::'a::order \<Rightarrow> 'a set)"
  by (simp add: downset_iso_iff mono_def)

lemma mono_downclosed: 
  fixes f :: "'a::order \<Rightarrow> 'b::order"
  assumes "mono f"
  shows "\<forall>Y. downclosed_set Y \<longrightarrow> downclosed_set (f -` Y)"   
  by (simp add: assms downclosed_set_iff monoD)

lemma
  fixes f :: "'a::order \<Rightarrow> 'b::order"
  assumes "mono f"
  shows "\<forall>Y. downclosed_set X \<longrightarrow> downclosed_set (f ` X)" (*nitpick*)
  oops

lemma downclosed_mono:
  fixes f :: "'a::order \<Rightarrow> 'b::order"
  assumes "\<forall>Y. downclosed_set Y \<longrightarrow> downclosed_set (f -` Y)"
  shows "mono f"
proof-
  {fix x y :: "'a::order"
  assume h: "x \<le> y"
  have "downclosed_set (\<down> (f y))"
    unfolding downclosed_set_def downsets_def Fix_def downset_set_def downset_def by auto
  hence "downclosed_set (f -` (\<down> (f y)))"
    by (simp add: assms)
  hence "downclosed_set {z. f z \<le> f y}"
    unfolding vimage_def downset_def downset_set_def by auto
  hence "\<forall>z w. (f z \<le> f y \<and> w \<le> z) \<longrightarrow> f w \<le> f y"
    unfolding downclosed_set_def downclosed_set_def downsets_def Fix_def downset_set_def by force
  hence "f x \<le> f y"
    using h by blast}
  thus ?thesis..
qed

lemma mono_downclosed_iff: "mono f = (\<forall>Y. downclosed_set Y \<longrightarrow> downclosed_set (f -` Y))"
  using mono_downclosed downclosed_mono by auto

context order
begin

lemma downset_inj: "inj \<down>"
  by (metis injI downset_iso_iff eq_iff)

lemma "(X \<subseteq> Y) = (\<Down>X \<subseteq> \<Down>Y)" (*nitpick*)
  oops

end

context lattice
begin

lemma lat_ideals: "X \<in> ideals = (X \<noteq> {} \<and> X \<in> downsets \<and> (\<forall>x \<in> X. \<forall> y \<in> X. x \<squnion> y \<in> X))"
  unfolding ideals_def directed_alt downsets_def Fix_def downset_set_def downclosed_set_def
  by (clarsimp, smt sup.cobounded1 sup.orderE sup.orderI sup_absorb2 sup_left_commute mem_Collect_eq)

end

context bounded_lattice
begin

lemma bot_ideal: "X \<in> ideals \<Longrightarrow> \<bottom> \<in> X"
  unfolding ideals_def downclosed_set_def downsets_def Fix_def downset_set_def by fastforce

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


subsection \<open>Dual Properties of Orderings\<close>

context ord_with_dual
begin

lemma filtered_nonempty: "filtered X \<Longrightarrow> X \<noteq> {}"
  using filtered_to_directed ord.directed_nonempty by auto

lemma filtered_lb: "filtered X \<Longrightarrow> (\<forall>x \<in> X. \<forall>y \<in> X. \<exists>z \<in> X. z \<le> x \<and> z \<le> y)"
  using filtered_to_directed directed_ub dual_dual_ord by fastforce

lemma upset_set_prop_var: "\<Up>X = (\<Union>x \<in> X. \<up>x)"
  by (simp add: image_Union downset_set_prop_var upset_set_to_downset_set2 upset_to_downset2)

lemma upset_set_prop: "\<Up> = Union \<circ> (`) \<up>"
  unfolding fun_eq_iff by (simp add: upset_set_prop_var)

lemma upset_prop: "\<up>x = {y. x \<le> y}"
  unfolding upset_to_downset3 downset_prop image_def using dual_dual_ord by fastforce

lemma upset_prop2: "x \<le> y \<Longrightarrow> y \<in> \<up>x"
  by (simp add: upset_prop)

lemma filters_upsets: "X \<in> filters \<Longrightarrow> X \<in> upsets"
  by (simp add: upclosed_set_def filters_def)

lemma filters_filtered: "X \<in> filters \<Longrightarrow> filtered X"
  by (simp add: filters_def)

end

context preorder_with_dual
begin

lemma filtered_prop: "X \<noteq> {} \<Longrightarrow> (\<forall>x \<in> X. \<forall>y \<in> X. \<exists>z \<in> X. z \<le> x \<and> z \<le> y) \<Longrightarrow> filtered X"
  unfolding filtered_to_directed 
    by (rule directed_prop, blast, metis (full_types) image_iff ord_dual)
 
lemma filtered_alt: "filtered X = (X \<noteq> {} \<and> (\<forall>x \<in> X. \<forall>y \<in> X. \<exists>z \<in> X. z \<le> x \<and> z \<le> y))"
  by (metis image_empty directed_alt filtered_to_directed filtered_lb filtered_prop)

lemma up_set_prop_var2: "x \<in> \<Up>X \<Longrightarrow> x \<le> y \<Longrightarrow> y \<in> \<Up>X"
  using downset_set_prop_var2 dual_iff ord_dual upset_set_to_downset_set2 by fastforce

lemma upclosed_set_iff: "upclosed_set X = (\<forall>x \<in> X. \<forall>y. x \<le> y \<longrightarrow> y \<in> X)"
  unfolding upclosed_set_def upsets_def Fix_def upset_set_def by auto

lemma upclosed_upset_set: "upclosed_set (\<Up>X)"
  using up_set_prop_var2 upclosed_set_iff by blast

lemma upclosed_upset: "upclosed_set (\<up>x)"
  by (simp add: upset_def upclosed_upset_set) 
  
lemma upset_set_ext: "id \<le> \<Up>"
  by (smt comp_def comp_id image_mono le_fun_def downset_set_ext image_dual upset_set_to_downset_set2)

lemma upset_set_anti: "mono \<Up>"
  by (metis image_mono downset_set_iso upset_set_to_downset_set2 mono_def)

lemma up_set_idem [simp]: "\<Up> \<circ> \<Up> = \<Up>"
  by (metis comp_assoc downset_set_idem upset_set_downset_set_dual upset_set_to_downset_set)

lemma upset_faithful: "\<up>x \<subseteq> \<up>y \<Longrightarrow> y \<le> x"
  by (metis inj_image_subset_iff downset_faithful dual_dual_ord inj_dual upset_to_downset3)

lemma upset_anti_iff: "(\<up>y \<subseteq> \<up>x) = (x \<le> y)"
  by (metis downset_iso_iff ord_dual upset_to_downset3 subset_image_iff upset_faithful)

lemma upset_filtered_upset [simp]: "filtered \<circ> \<Up> = filtered"
  by (metis comp_assoc directed_filtered_dual downset_directed_downset upset_set_downset_set_dual)

lemma filtered_upset_filters: "filtered (\<Up>X) = (\<Up>X \<in> filters)"
  by (metis comp_apply directed_downset_ideals filtered_to_directed filterp_idealp_dual upset_set_downset_set_dual)

lemma upclosed_Fix: "upclosed_set X = (\<Up>X = X)"
  by (simp add: Fix_def upclosed_set_def upsets_def)

end

lemma upset_anti: "antimono (\<up>::'a::order_with_dual \<Rightarrow> 'a set)"
  by (simp add: antimono_def upset_anti_iff)

lemma mono_upclosed: 
  fixes f :: "'a::order_with_dual \<Rightarrow> 'b::order_with_dual"
  assumes "mono f"
  shows "\<forall>Y. upclosed_set Y \<longrightarrow> upclosed_set (f -` Y)"
  by (simp add: assms monoD upclosed_set_iff)

lemma mono_upclosed: 
  fixes f :: "'a::order_with_dual \<Rightarrow> 'b::order_with_dual"
  assumes "mono f"
  shows "\<forall>Y. upclosed_set X \<longrightarrow> upclosed_set (f ` X)" (*nitpick*)
  oops

lemma upclosed_mono:
  fixes f :: "'a::order_with_dual \<Rightarrow> 'b::order_with_dual"
  assumes "\<forall>Y. upclosed_set Y \<longrightarrow> upclosed_set (f -` Y)"
  shows "mono f"
  by (metis (mono_tags, lifting) assms dual_order.refl mem_Collect_eq monoI order.trans upclosed_set_iff vimageE vimageI2)

lemma mono_upclosed_iff: 
  fixes f :: "'a::order_with_dual \<Rightarrow> 'b::order_with_dual"
  shows "mono f = (\<forall>Y. upclosed_set Y \<longrightarrow> upclosed_set (f -` Y))"
  using mono_upclosed upclosed_mono by auto

context order_with_dual
begin

lemma upset_inj: "inj \<up>"
  by (metis inj_compose inj_on_imageI2 downset_inj inj_dual upset_to_downset)

lemma "(X \<subseteq> Y) = (\<Up>Y \<subseteq> \<Up>X)" (*nitpick*)
  oops

end

context lattice_with_dual
begin

lemma lat_filters: "X \<in> filters = (X \<noteq> {} \<and> X \<in> upsets \<and> (\<forall>x \<in> X. \<forall> y \<in> X. x \<sqinter> y \<in> X))"
  unfolding filters_to_ideals upsets_to_downsets inf_to_sup lat_ideals
  by (smt image_iff image_inv_f_f image_is_empty inj_image_mem_iff inv_unique_comp inj_dual invol_dual)

end

context bounded_lattice_with_dual
begin

lemma top_filter: "X \<in> filters \<Longrightarrow> \<top> \<in> X"
  using bot_ideal inj_image_mem_iff inj_dual filters_to_ideals top_dual by fastforce

end

context complete_lattice_with_dual
begin

lemma Inf_upset_id [simp]: "Inf \<circ> \<up> = id"
  by (metis comp_assoc comp_id Sup_downset_id Sups_dual_def downset_upset_dual invol_dual)

lemma upset_Inf_id: "id \<le> \<up> \<circ> Inf"
  by (simp add: Inf_lower le_funI subsetI upset_prop)

lemma Sup_Inf_var: " \<Sqinter>(\<Inter>x \<in> X. \<up>x) = \<Squnion>X"
  unfolding upset_prop by (simp add: Collect_ball_eq Sup_eq_Inf)

lemma Sup_dual_upset_var: "(\<Inter>x \<in> X. \<up>x) = \<up>(\<Squnion>X)"
  unfolding upset_prop by (safe, simp_all add: Sup_le_iff)

end


subsection \<open>Shunting Laws\<close>

text \<open>The first set of laws supplies so-called shunting laws for boolean algebras. 
Such laws rather belong into Isabelle Main.\<close>

context boolean_algebra
begin
    
lemma shunt1: "(x \<sqinter> y \<le> z) = (x \<le> -y \<squnion> z)"
proof standard
  assume "x \<sqinter> y \<le> z"
  hence  "-y \<squnion> (x \<sqinter> y) \<le> -y \<squnion> z"
    using sup.mono by blast
  hence "-y \<squnion> x \<le> -y \<squnion> z"
    by (simp add: sup_inf_distrib1)
  thus "x \<le> -y \<squnion> z"
    by simp
next
  assume "x \<le> -y \<squnion> z"
  hence "x \<sqinter> y \<le> (-y \<squnion> z) \<sqinter> y"
    using inf_mono by auto
  thus  "x \<sqinter> y \<le> z"
    using inf.boundedE inf_sup_distrib2 by auto
qed

lemma shunt2: "(x \<sqinter> -y \<le> z) = (x \<le> y \<squnion> z)"
  by (simp add: shunt1)

lemma meet_shunt: "(x \<sqinter> y = \<bottom>) = (x \<le> -y)"
  by (simp add: eq_iff shunt1)
  
lemma join_shunt: "(x \<squnion> y = \<top>) = (-x \<le> y)"
  by (metis compl_sup compl_top_eq double_compl meet_shunt)

lemma meet_shunt_var: "(x - y = \<bottom>) = (x \<le> y)"
  by (simp add: diff_eq meet_shunt)

lemma join_shunt_var: "(x \<longrightarrow> y = \<top>) = (x \<le> y)"  
  by simp

end

subsection \<open>Properties of Complete Lattices\<close>

definition "Inf_closed_set X = (\<forall>Y \<subseteq> X. \<Sqinter>Y \<in> X)"

definition "Sup_closed_set X = (\<forall>Y \<subseteq> X. \<Squnion>Y \<in> X)"

definition "inf_closed_set X = (\<forall>x \<in> X. \<forall>y \<in> X. x \<sqinter> y \<in> X)" 

definition "sup_closed_set X = (\<forall>x \<in> X. \<forall>y \<in> X. x \<squnion> y \<in> X)"

text \<open>The following facts about complete lattices add to those in the Isabelle libraries.\<close>

context complete_lattice 
begin

text \<open>The translation between sup and Sup could be improved. The sup-theorems should be direct
consequences of Sup-ones. In addition, duality between sup and inf is currently not exploited.\<close>

lemma sup_Sup: "x \<squnion> y = \<Squnion>{x,y}"
  by simp

lemma inf_Inf: "x \<sqinter> y = \<Sqinter>{x,y}"
  by simp

text \<open>The next two lemmas are about Sups and Infs of indexed families. These are interesting for
iterations and fixpoints.\<close>

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

lemma Sup_sup_closed: "Sup_closed_set (X::'a::complete_lattice set) \<Longrightarrow> sup_closed_set X"
  by (metis Sup_closed_set_def empty_subsetI insert_subsetI sup_Sup sup_closed_set_def)

lemma Inf_inf_closed: "Inf_closed_set (X::'a::complete_lattice set) \<Longrightarrow> inf_closed_set X"
  by (metis Inf_closed_set_def empty_subsetI inf_Inf inf_closed_set_def insert_subset)


subsection \<open>Sup- and Inf-Preservation\<close>

text \<open>Next, important notation for morphism between posets and lattices is introduced: 
sup-preservation, inf-preservation and related properties.\<close>

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

text \<open>Inf-preservation and sup-preservation relate with duality.\<close>

lemma Inf_pres_map_dual_var: 
  "Inf_pres f = Sup_pres (\<partial>\<^sub>F f)"
  for f :: "'a::complete_lattice_with_dual \<Rightarrow> 'b::complete_lattice_with_dual"
proof -
  { fix x :: "'a set"
    assume "\<partial> (f (\<Sqinter> (\<partial> ` x))) = (\<Squnion>y\<in>x. \<partial> (f (\<partial> y)))" for x
    then have "\<Sqinter> (f ` \<partial> ` A) = f (\<partial> (\<Squnion> A))" for A
      by (metis (no_types) Sup_dual_def_var image_image invol_dual_var subset_dual)
    then have "\<Sqinter> (f ` x) = f (\<Sqinter> x)"
      by (metis Sup_dual_def_var subset_dual) }
  then show ?thesis
    by (auto simp add: map_dual_def fun_eq_iff Inf_dual_var Sup_dual_def_var image_comp)
qed

lemma Inf_pres_map_dual: "Inf_pres = Sup_pres \<circ> (\<partial>\<^sub>F::('a::complete_lattice_with_dual \<Rightarrow> 'b::complete_lattice_with_dual) \<Rightarrow> 'a \<Rightarrow> 'b)"
proof-
  {fix f::"'a \<Rightarrow> 'b"
  have "Inf_pres f = (Sup_pres \<circ> \<partial>\<^sub>F) f"
    by (simp add: Inf_pres_map_dual_var)}
  thus ?thesis
    by force
qed

lemma Sup_pres_map_dual_var: 
  fixes f :: "'a::complete_lattice_with_dual \<Rightarrow> 'b::complete_lattice_with_dual"
  shows "Sup_pres f = Inf_pres (\<partial>\<^sub>F f)"
  by (metis Inf_pres_map_dual_var fun_dual5 map_dual_def)

lemma Sup_pres_map_dual: "Sup_pres = Inf_pres \<circ> (\<partial>\<^sub>F::('a::complete_lattice_with_dual \<Rightarrow> 'b::complete_lattice_with_dual) \<Rightarrow> 'a \<Rightarrow> 'b)"
  by (simp add: Inf_pres_map_dual comp_assoc map_dual_invol)

text \<open>The following lemmas relate isotonicity of functions between complete lattices 
with weak (left) preservation properties of sups and infs.\<close>

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
  by (smt INF_insert Inf_empty Inf_insert comp_eq_elim inf_top.right_neutral)

lemma Sup_bot_pres: 
  fixes f :: "'a::complete_lattice \<Rightarrow> 'b::complete_lattice"
  shows "Sup_pres f \<Longrightarrow> bot_pres f"
  by (metis SUP_empty Sup_empty comp_eq_elim)

lemma Inf_top_pres: 
  fixes f :: "'a::complete_lattice \<Rightarrow> 'b::complete_lattice"
  shows "Inf_pres f \<Longrightarrow> top_pres f"
  by (metis INF_empty Inf_empty comp_eq_elim)

lemma Sup_sup_dual: 
  fixes f :: "'a::complete_lattice \<Rightarrow> 'b::complete_lattice"
  shows "Sup_dual f \<Longrightarrow> sup_dual f"
  by (smt comp_eq_elim image_empty image_insert inf_Inf sup_Sup)    

lemma Inf_inf_dual: 
  fixes f :: "'a::complete_lattice \<Rightarrow> 'b::complete_lattice"
  shows "Inf_dual f \<Longrightarrow> inf_dual f"
  by (smt comp_eq_elim image_empty image_insert inf_Inf sup_Sup)   

lemma Sup_bot_dual: 
  fixes f :: "'a::complete_lattice \<Rightarrow> 'b::complete_lattice"
  shows "Sup_dual f \<Longrightarrow> bot_dual f"
  by (metis INF_empty Sup_empty comp_eq_elim)

lemma Inf_top_dual: 
  fixes f :: "'a::complete_lattice \<Rightarrow> 'b::complete_lattice"
  shows "Inf_dual f \<Longrightarrow> top_dual f"
  by (metis Inf_empty SUP_empty comp_eq_elim)

text \<open>However, Inf-preservation does not imply top-preservation and 
Sup-preservation does not imply bottom-preservation.\<close>

lemma
  fixes f :: "'a::complete_lattice \<Rightarrow> 'b::complete_lattice"
  shows "Sup_pres f \<Longrightarrow> top_pres f" (*nitpick*)
  oops

lemma  
  fixes f :: "'a::complete_lattice \<Rightarrow> 'b::complete_lattice"
  shows "Inf_pres f \<Longrightarrow> bot_pres f" (*nitpick*)
  oops

context complete_lattice
begin

lemma iso_Inf_subdistl: 
  fixes f :: "'a \<Rightarrow> 'b::complete_lattice"
  shows "mono f \<Longrightarrow>f \<circ> Inf \<le> Inf \<circ> (`) f"
  by (simp add: complete_lattice_class.le_Inf_iff le_funI Inf_lower monoD)

lemma iso_Sup_supdistl: 
  fixes f :: "'a \<Rightarrow> 'b::complete_lattice" 
  shows "mono f \<Longrightarrow> Sup \<circ> (`) f \<le> f \<circ> Sup"
  by (simp add: complete_lattice_class.Sup_le_iff le_funI Sup_upper monoD)

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

lemma ord_iso_Inf_pres: 
  fixes f :: "'a::complete_lattice \<Rightarrow> 'b::complete_lattice"
  shows "ord_iso f \<Longrightarrow> Inf \<circ> (`) f = f \<circ> Inf"
proof-
  let ?g = "the_inv f"
  assume h: "ord_iso f"
  hence a: "mono ?g"
    by (simp add: ord_iso_the_inv)
  {fix X :: "'a::complete_lattice set"
    {fix y :: "'b::complete_lattice"
   have "(y \<le> f (\<Sqinter>X)) = (?g y \<le> \<Sqinter>X)"
     by (metis (mono_tags, lifting) UNIV_I f_the_inv_into_f h monoD ord_embed_alt ord_embed_inj ord_iso_alt)
   also have "... = (\<forall>x \<in> X. ?g y \<le> x)"
    by (simp add: le_Inf_iff)
  also have "... = (\<forall>x \<in> X. y \<le> f x)"
    by (metis (mono_tags, lifting) UNIV_I f_the_inv_into_f h monoD ord_embed_alt ord_embed_inj ord_iso_alt)
  also have "... = (y \<le> \<Sqinter> (f ` X))"
    by (simp add: le_INF_iff)
  finally have "(y \<le> f (\<Sqinter>X)) = (y \<le> \<Sqinter> (f ` X))".}
  hence "f (\<Sqinter>X) = \<Sqinter> (f ` X)"
    by (meson dual_order.antisym order_refl)}
  thus ?thesis
    unfolding fun_eq_iff by simp
qed

lemma ord_iso_Sup_pres: 
  fixes f :: "'a::complete_lattice \<Rightarrow> 'b::complete_lattice"
  shows "ord_iso f \<Longrightarrow> Sup \<circ> (`) f = f \<circ> Sup"
proof-
  let ?g = "the_inv f"
  assume h: "ord_iso f"
  hence a: "mono ?g"
    by (simp add: ord_iso_the_inv)
  {fix X :: "'a::complete_lattice set"
    {fix y :: "'b::complete_lattice"
   have "(f (\<Squnion>X) \<le> y) = (\<Squnion>X \<le> ?g y)"
     by (metis (mono_tags, lifting) UNIV_I f_the_inv_into_f h monoD ord_embed_alt ord_embed_inj ord_iso_alt)
   also have "... = (\<forall>x \<in> X. x \<le> ?g y)"
     by (simp add: Sup_le_iff)
     also have "... = (\<forall>x \<in> X. f x \<le> y)"
    by (metis (mono_tags, lifting) UNIV_I f_the_inv_into_f h monoD ord_embed_alt ord_embed_inj ord_iso_alt)
  also have "... = (\<Squnion> (f ` X) \<le> y)"
    by (simp add: SUP_le_iff)
  finally have "(f (\<Squnion>X) \<le> y) = (\<Squnion> (f ` X) \<le> y)".}
  hence "f (\<Squnion>X) = \<Squnion> (f ` X)"
    by (meson dual_order.antisym order_refl)}
  thus ?thesis
    unfolding fun_eq_iff by simp
qed

text \<open>Right preservation of sups and infs is trivial.\<close>

lemma fSup_distr: "Sup_pres (\<lambda>x. x \<circ> f)"
  unfolding fun_eq_iff by (simp add: image_comp)

lemma fSup_distr_var: "\<Squnion>F \<circ> g = (\<Squnion>f \<in> F. f \<circ> g)"
  unfolding fun_eq_iff by (simp add: image_comp)

lemma fInf_distr: "Inf_pres (\<lambda>x. x \<circ> f)"
  unfolding fun_eq_iff comp_def
  by (smt INF_apply Inf_fun_def Sup.SUP_cong) 

lemma fInf_distr_var: "\<Sqinter>F \<circ> g = (\<Sqinter>f \<in> F. f \<circ> g)"
  unfolding fun_eq_iff comp_def
  by (smt INF_apply INF_cong INF_image Inf_apply image_comp image_def image_image)


text \<open>The next set of lemma revisits the preservation properties in the function space.\<close>

lemma fSup_subdistl: 
  assumes "mono (f::'a::complete_lattice \<Rightarrow> 'b::complete_lattice)"
  shows "Sup \<circ> (`) ((\<circ>) f) \<le> (\<circ>) f \<circ> Sup"
  using assms by (simp add: fun_isol supdistl_iso) 

lemma fSup_subdistl_var: 
  fixes f :: "'a::complete_lattice \<Rightarrow> 'b::complete_lattice"
  shows  "mono f \<Longrightarrow> (\<Squnion>g \<in> G. f \<circ> g) \<le> f \<circ> \<Squnion>G"
  by (simp add: fun_isol mono_Sup)

lemma fInf_subdistl: 
  fixes f :: "'a::complete_lattice \<Rightarrow> 'b::complete_lattice"
  shows  "mono f \<Longrightarrow> (\<circ>) f \<circ> Inf \<le> Inf \<circ> (`) ((\<circ>) f)"
  by (simp add: fun_isol subdistl_iso)

lemma fInf_subdistl_var: 
  fixes f :: "'a::complete_lattice \<Rightarrow> 'b::complete_lattice"
  shows "mono f \<Longrightarrow> f \<circ> \<Sqinter>G \<le> (\<Sqinter>g \<in> G. f \<circ> g)"
  by (simp add: fun_isol mono_Inf)

lemma fSup_distl: "Sup_pres f \<Longrightarrow> Sup_pres ((\<circ>) f)"
  unfolding fun_eq_iff by (simp add: image_comp)

lemma fSup_distl_var: "Sup_pres f \<Longrightarrow> f \<circ> \<Squnion>G = (\<Squnion>g \<in> G. f \<circ> g)"
  unfolding fun_eq_iff by (simp add: image_comp)

lemma fInf_distl: "Inf_pres f \<Longrightarrow> Inf_pres ((\<circ>) f)"
  unfolding fun_eq_iff by (simp add: image_comp)

lemma fInf_distl_var: "Inf_pres f \<Longrightarrow> f \<circ> \<Sqinter>G = (\<Sqinter>g \<in> G. f \<circ> g)"
  unfolding fun_eq_iff by (simp add: image_comp)

text \<open>Downsets preserve infs whereas upsets preserve sups.\<close>

lemma Inf_pres_downset: "Inf_pres (\<down>::'a::complete_lattice_with_dual \<Rightarrow> 'a set)"
  unfolding downset_prop fun_eq_iff
  by (safe, simp_all add: le_Inf_iff)
 
lemma Sup_dual_upset: "Sup_dual (\<up>::'a::complete_lattice_with_dual \<Rightarrow> 'a set)"
  unfolding upset_prop fun_eq_iff
  by (safe, simp_all add: Sup_le_iff)

text \<open>Images of Sup-morphisms are closed under Sups and images of Inf-morphisms are closed under Infs.\<close>

lemma Sup_pres_Sup_closed: "Sup_pres f \<Longrightarrow> Sup_closed_set (range f)"
  by (metis (mono_tags, lifting) Sup_closed_set_def comp_eq_elim range_eqI subset_image_iff)

lemma Inf_pres_Inf_closed: "Inf_pres f \<Longrightarrow> Inf_closed_set (range f)"
  by (metis (mono_tags, lifting) Inf_closed_set_def comp_eq_elim range_eqI subset_image_iff)

text \<open>It is well known that functions into complete lattices form complete lattices. Here, such results are shown for
the subclasses of isotone functions, where additional closure conditions must be respected.\<close>

typedef (overloaded) 'a iso = "{f::'a::order \<Rightarrow> 'a::order. mono f}"
  by (metis Abs_ord_homset_cases ord_homset_def)

setup_lifting type_definition_iso

instantiation iso :: (complete_lattice) complete_lattice
begin

lift_definition Inf_iso :: "'a::complete_lattice iso set \<Rightarrow> 'a iso" is Sup
  by (metis (mono_tags, lifting) SUP_subset_mono Sup_apply mono_def subsetI)

lift_definition Sup_iso :: "'a::complete_lattice iso set \<Rightarrow> 'a iso" is Inf
  by (smt INF_lower2 Inf_apply le_INF_iff mono_def)

lift_definition bot_iso :: "'a::complete_lattice iso" is "\<top>"
  by (simp add: monoI)

lift_definition sup_iso :: "'a::complete_lattice iso \<Rightarrow> 'a iso \<Rightarrow> 'a iso" is inf
  by (smt inf_apply inf_mono monoD monoI)

lift_definition top_iso :: "'a::complete_lattice iso" is "\<bottom>"
  by (simp add: mono_def)

lift_definition inf_iso :: "'a::complete_lattice iso \<Rightarrow> 'a iso \<Rightarrow> 'a iso" is sup
  by (smt mono_def sup.mono sup_apply)

lift_definition less_eq_iso :: "'a::complete_lattice iso \<Rightarrow> 'a iso \<Rightarrow> bool" is "(\<ge>)".

lift_definition less_iso :: "'a::complete_lattice iso \<Rightarrow> 'a iso \<Rightarrow> bool" is "(>)".

instance
  by (intro_classes; transfer, simp_all add: less_fun_def Sup_upper Sup_least Inf_lower Inf_greatest)

end

text \<open>Duality has been baked into this result because of its relevance for predicate transformers. A proof
where Sups are mapped to Sups and Infs to Infs is certainly possible, but two instantiation of the same type
and the same classes are unfortunately impossible. Interpretations could be used instead.

A corresponding result for Inf-preseving functions and Sup-lattices, is proved in components on transformers,
as more advanced properties about Inf-preserving functions are needed.\<close>


subsection \<open>Alternative Definitions for Complete Boolean Algebras\<close>

text \<open>The current definitions of complete boolean algebras deviates from that in most textbooks in that
a distributive law with infinite sups and infinite infs is used. There are interesting applications, for instance 
in topology, where weaker laws are needed --- for instance for frames and locales.\<close>

class complete_heyting_algebra = complete_lattice +
  assumes ch_dist: "x \<sqinter> \<Squnion>Y = (\<Squnion>y \<in> Y. x \<sqinter> y)"

text \<open>Complete Heyting algebras are also known as frames or locales (they differ with respect to their morphisms).\<close>

class complete_co_heyting_algebra = complete_lattice +
  assumes co_ch_dist: "x \<squnion> \<Sqinter>Y = (\<Sqinter>y \<in> Y. x \<squnion> y)"

class complete_boolean_algebra_alt = complete_lattice + boolean_algebra

instance set :: (type) complete_boolean_algebra_alt..

context complete_boolean_algebra_alt
begin

subclass complete_heyting_algebra
proof
  fix x Y 
  {fix t
    have "(x \<sqinter> \<Squnion>Y \<le> t) = (\<Squnion>Y \<le> -x \<squnion> t)"
      by (simp add: inf.commute shunt1[symmetric])
    also have "... = (\<forall>y \<in> Y. y \<le> -x \<squnion> t)"
      using Sup_le_iff by blast
    also have "... = (\<forall>y \<in> Y. x \<sqinter> y \<le> t)"
      by (simp add: inf.commute shunt1)
    finally have "(x \<sqinter> \<Squnion>Y \<le> t) = ((\<Squnion>y\<in>Y. x \<sqinter> y) \<le> t)"
      by (simp add: local.SUP_le_iff)}
  thus "x \<sqinter> \<Squnion>Y = (\<Squnion>y\<in>Y. x \<sqinter> y)"
    using eq_iff by blast
qed

subclass complete_co_heyting_algebra
  apply unfold_locales
  apply (rule antisym)
   apply (simp add: INF_greatest Inf_lower2)
  by (meson eq_refl le_INF_iff le_Inf_iff shunt2)

lemma de_morgan1: "-(\<Squnion>X) = (\<Sqinter>x \<in> X. -x)"
proof-
  {fix y
  have "(y \<le> -(\<Squnion>X)) = (\<Squnion>X \<le> -y)"
    using compl_le_swap1 by blast
  also have "... = (\<forall>x \<in> X. x \<le> -y)"
    by (simp add: Sup_le_iff)
  also have "... = (\<forall>x \<in> X. y \<le> -x)"
    using compl_le_swap1 by blast
  also have "... = (y \<le> (\<Sqinter>x \<in> X. -x))"
    using le_INF_iff by force
  finally have "(y \<le> -(\<Squnion>X)) = (y \<le>(\<Sqinter>x \<in> X. -x))".}
  thus ?thesis
    using antisym by blast
qed

lemma de_morgan2: "-(\<Sqinter>X) = (\<Squnion>x \<in> X. -x)"
  by (metis de_morgan1 ba_dual.dual_iff ba_dual.image_dual pointfree_idE)

end

class complete_boolean_algebra_alt_with_dual = complete_lattice_with_dual + complete_boolean_algebra_alt

instantiation set :: (type) complete_boolean_algebra_alt_with_dual
begin

definition dual_set :: "'a set \<Rightarrow> 'a set" where
  "dual_set = uminus"

instance
  by intro_classes (simp_all add: ba_dual.inj_dual dual_set_def comp_def uminus_Sup id_def)

end

context complete_boolean_algebra_alt
begin

sublocale cba_dual: complete_boolean_algebra_alt_with_dual _ _ _ _ _ _ _ _ uminus _ _
  by unfold_locales (auto simp: de_morgan2 de_morgan1)

end


subsection \<open>Atomic Boolean Algebras\<close>

text \<open>Next, atomic boolean algebras are defined.\<close>

context bounded_lattice
begin

text \<open>Atoms are covers of bottom.\<close>

definition "atom x = (x \<noteq> \<bottom> \<and> \<not>(\<exists>y. \<bottom> < y \<and> y < x))"

definition "atom_map x = {y. atom y \<and> y \<le> x}"

lemma atom_map_def_var: "atom_map x = \<down>x \<inter> Collect atom"
  unfolding atom_map_def downset_def downset_set_def comp_def atom_def by fastforce

lemma atom_map_atoms: "\<Union>(range atom_map) = Collect atom"
  unfolding atom_map_def atom_def by auto

end

typedef (overloaded) 'a atoms = "range (atom_map::'a::bounded_lattice \<Rightarrow> 'a set)"
  by blast

setup_lifting type_definition_atoms

definition at_map :: "'a::bounded_lattice \<Rightarrow> 'a atoms" where
  "at_map = Abs_atoms \<circ> atom_map"

class atomic_boolean_algebra = boolean_algebra +
  assumes atomicity: "x \<noteq> \<bottom> \<Longrightarrow> (\<exists>y. atom y \<and> y \<le> x)"

class complete_atomic_boolean_algebra = complete_lattice + atomic_boolean_algebra

begin

subclass complete_boolean_algebra_alt..

end

text \<open>Here are two equivalent definitions for atoms; first in boolean algebras, and then in complete 
boolean algebras.\<close>

context boolean_algebra
begin

text \<open>The following two conditions are taken from Koppelberg's book~\cite{Koppelberg89}.\<close>

lemma atom_neg: "atom x \<Longrightarrow> x \<noteq> \<bottom> \<and> (\<forall>y z. x \<le> y \<or> x \<le> -y)"
  by (metis atom_def dual_order.order_iff_strict inf.cobounded1 inf.commute meet_shunt)

lemma atom_sup: "(\<forall>y. x \<le> y \<or> x \<le> -y) \<Longrightarrow> (\<forall>y z. (x \<le> y \<or> x \<le> z) = (x \<le> y \<squnion> z))"
  by (metis inf.orderE le_supI1 shunt2)

lemma sup_atom: "x \<noteq> \<bottom> \<Longrightarrow> (\<forall>y z. (x \<le> y \<or> x \<le> z) = (x \<le> y \<squnion> z)) \<Longrightarrow> atom x"
  unfolding atom_def apply clarsimp by (metis bot_less inf.absorb2 less_le_not_le meet_shunt sup_compl_top)

lemma atom_sup_iff: "atom x = (x \<noteq> \<bottom> \<and> (\<forall>y z. (x \<le> y \<or> x \<le> z) = (x \<le> y \<squnion> z)))"
  by  (standard, auto simp add: atom_neg atom_sup sup_atom)  

lemma atom_neg_iff: "atom x = (x \<noteq> \<bottom> \<and> (\<forall>y z. x \<le> y \<or> x \<le> -y))"
  by  (standard, auto simp add: atom_neg atom_sup sup_atom)

lemma atom_map_bot_pres: "atom_map \<bottom> = {}"
  using atom_def atom_map_def le_bot by auto

lemma atom_map_top_pres: "atom_map \<top> = Collect atom"
  using atom_map_def by auto

end

context complete_boolean_algebra_alt
begin

lemma atom_Sup: "\<And>Y. x \<noteq> \<bottom> \<Longrightarrow> (\<forall>y. x \<le> y \<or> x \<le> -y) \<Longrightarrow> ((\<exists>y \<in> Y. x \<le> y) = (x \<le> \<Squnion>Y))"
  by (metis Sup_least Sup_upper2 compl_le_swap1 le_iff_inf meet_shunt)

lemma Sup_atom: "x \<noteq> \<bottom> \<Longrightarrow> (\<forall>Y. (\<exists>y \<in> Y. x \<le> y) = (x \<le> \<Squnion>Y)) \<Longrightarrow> atom x"
proof-
  assume h1: "x \<noteq> \<bottom>"
  and h2: "\<forall>Y. (\<exists>y \<in> Y. x \<le> y) = (x \<le> \<Squnion>Y)"
  hence "\<forall>y z. (x \<le> y \<or> x \<le> z) = (x \<le> y \<squnion> z)"

    by (smt insert_iff sup_Sup sup_bot.right_neutral)
  thus "atom x"
    by (simp add: h1 sup_atom)
qed

lemma atom_Sup_iff: "atom x = (x \<noteq> \<bottom> \<and> (\<forall>Y. (\<exists>y \<in> Y. x \<le> y) = (x \<le> \<Squnion>Y)))"
  by standard (auto simp: atom_neg atom_Sup Sup_atom)

end

end




