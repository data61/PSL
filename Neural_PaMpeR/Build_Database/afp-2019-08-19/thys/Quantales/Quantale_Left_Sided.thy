(* Title: Left-Sided Elements in Quantales
   Author: Georg Struth
   Maintainer: Georg Struth <g.struth@sheffield.ac.uk> 
*)

section \<open>Left-Sided Elements in Quantales\<close>

theory Quantale_Left_Sided
  imports Quantic_Nuclei_Conuclei
begin

context quantale
begin

subsection \<open>Basic Definitions\<close>

text \<open>Left-sided elements are well investigated in quantale theory. They could be defined in weaker settings, for instance,
ord with a top element.\<close>

definition "lsd x = (\<top> \<cdot> x \<le> x)"

definition "rsd x = (x \<cdot> \<top> \<le> x)"

definition "twosd x = (lsd x \<and> rsd x)"

definition "slsd x = (\<top> \<cdot> x = x)"

definition "srsd x = (x \<cdot> \<top> = x)"

definition "stwsd x = (slsd x \<and> srsd x)"

lemma lsided_bres: "(lsd x) = (x \<le> \<top> \<rightarrow> x)" 
  by (simp add: bres_galois lsd_def)

lemma lsided_fres: "(lsd x) = (\<top> \<le> x \<leftarrow> x)"
  by (simp add: fres_galois lsd_def) 

lemma lsided_fres_eq: "(lsd x) = (x \<leftarrow> x = \<top>)"
  using fres_galois top_le lsd_def by force

lemma lsided_slsided: "lsd x \<Longrightarrow> x \<cdot> x = x \<Longrightarrow> slsd x"
  using fres_sol lsided_fres_eq slsd_def by force

lemma lsided_prop: "lsd x \<Longrightarrow> y \<cdot> x \<le> x"
  by (simp add: fres_galois lsided_fres_eq)

lemma rsided_fres: "(rsd x) = (x \<le> x \<leftarrow> \<top>)"
  by (simp add: fres_galois rsd_def) 

lemma rsided_bres: "(rsd x) = (\<top> \<le> x \<rightarrow> x)"
  by (simp add: bres_galois rsd_def)

lemma rsided_bres_eq: "(rsd x) = (x \<rightarrow> x = \<top>)"
  using top_le rsided_bres by blast

lemma rsided_srsided: "rsd x \<Longrightarrow> x \<cdot> x = x \<Longrightarrow> srsd x"
  using bres_sol rsided_bres_eq srsd_def by auto

lemma rsided_prop: "rsd x \<Longrightarrow> x \<cdot> y \<le> x"
  by (simp add: bres_galois rsided_bres_eq)

lemma lsided_top: "lsd \<top>"
  by (simp add: lsd_def)
    
lemma lsided_bot: "lsd \<bottom>"
  by (simp add: lsd_def)

lemma rsided_top: "rsd \<top>"
  by (simp add: rsd_def)
    
lemma rsided_bot: "rsd \<bottom>"
  by (simp add: rsd_def)

end

text \<open>Right-sided elements are henceforth not considered. Their properties arise by opposition
duality, which is not formalised.\<close>

text \<open>The following functions have left-sided elements as fixpoints.\<close>

definition lsl:: "'a::quantale \<Rightarrow> 'a" ("\<nu>") where 
  "\<nu> x = \<top> \<cdot> x"

definition lsu :: "'a::quantale \<Rightarrow> 'a" ("\<nu>\<^sup>\<natural>") where 
  "\<nu>\<^sup>\<natural> x = \<top> \<rightarrow> x"

text \<open>These functions are adjoints.\<close>

lemma ls_galois: "\<nu> \<stileturn> \<nu>\<^sup>\<natural>"
  by (simp add: adj_def bres_galois lsl_def lsu_def)

text \<open>Due to this, the following properties hold.\<close>

lemma lsl_iso: "mono \<nu>"
  using adj_iso1 ls_galois by blast

lemma lsl_iso_var: "x \<le> y \<Longrightarrow> \<nu> x \<le> \<nu> y"
  by (simp add: lsl_iso monoD)

lemma lsu_iso: "mono \<nu>\<^sup>\<natural>"
  using adj_iso2 ls_galois by blast

lemma lsu_iso_var: "x \<le> y \<Longrightarrow> \<nu>\<^sup>\<natural> x \<le> \<nu>\<^sup>\<natural> y"
  by (simp add: lsu_iso monoD)

lemma lsl_bot [simp]: "\<nu> \<bottom> = \<bottom>"
  by (simp add: lsl_def)

lemma lsu_top [simp]: "\<nu>\<^sup>\<natural> \<top> = \<top>"
  by (simp add: lsu_def bres_galois_imp top_le)

lemma lsu_Inf_pres: "Inf_pres \<nu>\<^sup>\<natural>"
  unfolding fun_eq_iff by (metis ls_galois radj_Inf_pres)

lemma lsl_Sup_pres: "Sup_pres (\<nu>::'a::quantale \<Rightarrow> 'a)"
  by (simp add: fun_eq_iff, metis SUP_cong Sup_distl lsl_def)

lemma lsu_Inf_closed: "Inf_closed_set (range \<nu>\<^sup>\<natural>)"
  by (simp add: Inf_pres_Inf_closed lsu_Inf_pres)

lemma lsl_Sup_closed: "Sup_closed_set (range (\<nu>::'a::quantale \<Rightarrow> 'a))"
  by (simp add: Sup_pres_Sup_closed lsl_Sup_pres)

lemma lsl_lsu_canc1: "\<nu> \<circ> \<nu>\<^sup>\<natural> \<le> id"
  by (simp add: adj_cancel1 ls_galois)

lemma lsl_lsu_canc2: "id \<le> \<nu>\<^sup>\<natural> \<circ> \<nu>"
  by (simp add: adj_cancel2 ls_galois)

lemma clop_lsu_lsl: "clop (\<nu>\<^sup>\<natural> \<circ> \<nu>)"
  by (simp add: clop_adj ls_galois)

lemma coclop_lsl_lsu: "coclop (\<nu> \<circ> \<nu>\<^sup>\<natural>)"
  by (simp add: coclop_adj ls_galois)

lemma dang1: "\<nu> (\<nu> x \<sqinter> y) \<le> \<nu> x"
  unfolding lsl_def by (metis bres_galois bres_interchange bres_top_top inf.coboundedI1)

lemma lsl_trans: "\<nu> \<circ> \<nu> \<le> \<nu>"
  unfolding lsl_def fun_eq_iff comp_def
  by (metis (no_types, lifting) bres_galois bres_interchange bres_top_top le_funI)

lemma lsl_lsu_prop: "\<nu> \<circ> \<nu>\<^sup>\<natural> \<le> \<nu>\<^sup>\<natural>"
  unfolding le_fun_def comp_def
  by (metis adj_def dang1 dual_order.trans le_iff_inf ls_galois order_refl top_greatest)

lemma lsu_lsl_prop: "\<nu> \<le> \<nu>\<^sup>\<natural> \<circ> \<nu>"
  unfolding le_fun_def comp_def by (metis adj_def comp_def le_fun_def ls_galois lsl_trans)

context unital_quantale
begin

text \<open>Left-sidedness and strict left-sidedness now coincide.\<close>

lemma lsided_eq: "lsd = slsd"
  unfolding fun_eq_iff by (simp add: eq_iff le_top lsd_def slsd_def)

lemma lsided_eq_var1:  "(x \<le> \<top> \<rightarrow> x) = (x = \<top> \<rightarrow> x)"
  using bres_galois dual_order.trans eq_iff le_top by blast

lemma lsided_eq_var2: "lsd x = (x = \<top> \<rightarrow> x)"
  using bres_galois lsided_eq lsided_eq_var1 lsd_def by simp

end

lemma lsided_def3: "(\<nu> (x::'a::unital_quantale) = x) = (\<nu>\<^sup>\<natural> x = x)"
  unfolding lsl_def lsu_def by (metis lsided_eq lsided_eq_var2 slsd_def)

lemma Fix_lsl_lsu: "Fix (\<nu>::'a::unital_quantale \<Rightarrow> 'a) = Fix \<nu>\<^sup>\<natural>"
  unfolding Fix_def by (simp add: lsided_def3) 

lemma Fix_lsl_left_slsided: "Fix \<nu> = {(x::'a::unital_quantale). lsd x}"
  unfolding Fix_def lsl_def lsd_def using eq_iff le_top by blast

lemma Fix_lsl_iff [simp]: "(x \<in> Fix \<nu>) = (\<nu> x = x)"
  by (simp add: Fix_def)

lemma Fix_lsu_iff [simp]: "(x \<in> Fix \<nu>\<^sup>\<natural>) = (\<nu>\<^sup>\<natural> x = x)"
  by (simp add: Fix_def)

lemma lsl_lsu_prop_eq [simp]: "(\<nu>::'a::unital_quantale \<Rightarrow> 'a) \<circ> \<nu>\<^sup>\<natural> = \<nu>\<^sup>\<natural>"
  by (smt antisym clop_extensive_var clop_lsu_lsl comp_apply le_fun_def lsided_eq_var1 lsl_lsu_prop lsu_def lsu_lsl_prop)

lemma lsu_lsl_prop_eq [simp]: "\<nu>\<^sup>\<natural> \<circ> \<nu> = (\<nu>::'a::unital_quantale \<Rightarrow> 'a)"
  by (metis adj_cancel_eq1 ls_galois lsl_lsu_prop_eq)


subsection \<open>Connection with Closure and Coclosure Operators, Nuclei and Conuclei\<close>

text \<open>lsl is therefore a closure operator, lsu a cocolosure operator.\<close>

lemma lsl_clop: "clop (\<nu>::'a::unital_quantale \<Rightarrow> 'a)"
  by (metis clop_lsu_lsl lsu_lsl_prop_eq)

lemma lsu_coclop: "coclop (\<nu>\<^sup>\<natural>::'a::unital_quantale \<Rightarrow> 'a)"
  by (metis coclop_lsl_lsu lsl_lsu_prop_eq)

lemma lsl_range_fix: "range (\<nu>::'a::unital_quantale \<Rightarrow> 'a) = Fix \<nu>"
  by (simp add: clop_closure_set lsl_clop)

lemma lsu_range_fix: "range (\<nu>\<^sup>\<natural>::'a::unital_quantale \<Rightarrow> 'a) = Fix \<nu>\<^sup>\<natural>"
  by (simp add: coclop_coclosure_set lsu_coclop)

lemma range_lsl_iff [simp]: "((x::'a::unital_quantale) \<in> range \<nu>) = (\<nu> x = x)"
  by (simp add: lsl_range_fix)

lemma range_lsu_iff [simp]: "((x::'a::unital_quantale) \<in> range \<nu>\<^sup>\<natural>) = (\<nu>\<^sup>\<natural> x = x)"
  by (simp add: lsu_range_fix)

text \<open>lsl and lsu are therefore both Sup and Inf closed.\<close>

lemma lsu_Sup_closed: "Sup_closed_set (Fix (\<nu>\<^sup>\<natural>::'a::unital_quantale \<Rightarrow> 'a))"
  by (metis Fix_lsl_lsu lsl_Sup_closed lsl_range_fix)

lemma lsl_Inf_closed: "Inf_closed_set (Fix (\<nu>::'a::unital_quantale \<Rightarrow> 'a))"
  by (metis Fix_lsl_lsu lsu_Inf_closed lsu_range_fix)

text \<open>lsl is even a quantic conucleus.\<close>

lemma lsu_lax: "\<nu>\<^sup>\<natural> (x::'a::unital_quantale) \<cdot> \<nu>\<^sup>\<natural> y \<le> \<nu>\<^sup>\<natural> (x \<cdot> y)"
  unfolding lsu_def by (meson bres_canc1 bres_galois bres_interchange le_top order_trans)

lemma lsu_one: "\<nu>\<^sup>\<natural> 1 \<le> (1::'a::unital_quantale)"
  unfolding lsu_def using bres_canc1 dual_order.trans le_top by blast

lemma lsl_one: "1 \<le> \<nu> (1::'a::unital_quantale)"
  unfolding lsl_def by simp

lemma lsu_conuc: "conucleus (\<nu>\<^sup>\<natural>::'a::unital_quantale \<Rightarrow> 'a)"
  by (simp add: lsu_coclop conucleus_def lsu_lax)

text \<open>It is therefore closed under composition.\<close>

lemma lsu_comp_closed_var [simp]: "\<nu>\<^sup>\<natural> (\<nu>\<^sup>\<natural> x \<cdot> \<nu>\<^sup>\<natural> y) = \<nu>\<^sup>\<natural> x \<cdot> \<nu>\<^sup>\<natural> (y::'a::unital_quantale)"
  by (simp add: conuc_comp_closed lsu_conuc)

lemma lsu_comp_closed: "comp_closed_set (Fix (\<nu>\<^sup>\<natural>::'a::unital_quantale \<Rightarrow> 'a))"
  by (simp add: conuc_Sup_qclosed lsu_conuc)
  
text \<open>lsl is not a quantic nucleus unless composition is commutative.\<close>      

lemma "\<nu> x \<cdot> \<nu> y \<le> \<nu> (x \<cdot> (y::'a::unital_quantale))" (*nitpick*)
  oops

text \<open>Yet it is closed under composition (because the set of fixpoints are the same).\<close>

lemma lsl_comp_closed: "comp_closed_set (Fix (\<nu>::'a::unital_quantale \<Rightarrow> 'a))"
  by (simp add: Fix_lsl_lsu lsu_comp_closed)

lemma lsl_comp_closed_var [simp]: "\<nu> (\<nu> x \<cdot> \<nu> (y::'a::unital_quantale)) = \<nu> x \<cdot> \<nu> y"
  by (metis Fix_lsl_iff lsl_def lsl_range_fix mult.assoc rangeI)

text \<open>The following simple properties go beyond nuclei and conuclei.\<close>  

lemma lsl_lsu_ran: "range \<nu>\<^sup>\<natural> = range (\<nu>::'a::unital_quantale \<Rightarrow> 'a)"
  by (simp add: Fix_lsl_lsu lsl_range_fix lsu_range_fix)

lemma lsl_top [simp]: "\<nu> \<top> = (\<top>::'a::unital_quantale)"
  by (simp add: clop_top lsl_clop)

lemma lsu_bot [simp]: "\<nu>\<^sup>\<natural> \<bottom> = (\<bottom>::'a::unital_quantale)"
  using lsided_def3 lsl_bot by blast

lemma lsu_inj_on: "inj_on \<nu>\<^sup>\<natural> (Fix (\<nu>\<^sup>\<natural>::'a::unital_quantale \<Rightarrow> 'a))"
  by (metis coclop_coclosure inj_onI lsu_coclop lsu_range_fix)

lemma lsl_inj_on: "inj_on \<nu> (Fix (\<nu>::'a::unital_quantale \<Rightarrow> 'a))"
  by (metis clop_closure inj_onI lsl_clop lsl_range_fix)

text \<open>Additional preservation properties of lsl and lsu are useful in proofs.\<close>

lemma lsl_Inf_closed_var [simp]: "\<nu> (\<Sqinter>x \<in> X. \<nu> x) = (\<Sqinter>x \<in> X.  \<nu> (x::'a::unital_quantale))"
  by (metis (no_types, hide_lams) INF_image lsided_def3 lsu_Inf_pres lsu_lsl_prop_eq o_apply)

lemma lsl_Sup_closed_var [simp]: "\<nu> (\<Squnion>x \<in> X. \<nu> x) = (\<Squnion>x \<in> X. \<nu> (x::'a::unital_quantale))"
  unfolding lsl_def by (metis Sup_distl mult.assoc top_times_top)

lemma lsu_Inf_closed_var [simp]: "\<nu>\<^sup>\<natural> (\<Sqinter>x \<in> X. \<nu>\<^sup>\<natural> x) = (\<Sqinter>x \<in> X. \<nu>\<^sup>\<natural> (x::'a::unital_quantale))"
  by (metis INF_image lsided_def3 lsl_Inf_closed_var lsl_lsu_prop_eq)

lemma lsu_Sup_closed_var [simp]: "\<nu>\<^sup>\<natural> (\<Squnion>x \<in> X. \<nu>\<^sup>\<natural> x) = (\<Squnion>x \<in> X. \<nu>\<^sup>\<natural> (x::'a::unital_quantale))"
  by (metis SUP_image lsided_def3 lsl_Sup_closed_var lsl_lsu_prop_eq)

lemma lsl_inf_closed_var [simp]: "\<nu> (\<nu> x \<sqinter> \<nu> y) = \<nu> (x::'a::unital_quantale) \<sqinter> \<nu> y"
  by (smt antisym clop_extensive_var dang1 inf_sup_aci(1) le_inf_iff lsl_clop)

lemma lsl_sup_closed_var [simp]: "\<nu> (\<nu> x \<squnion> \<nu> y) = \<nu> (x::'a::unital_quantale) \<squnion> \<nu> y"
  by (meson Sup_sup_closed lsl_Sup_closed range_eqI range_lsl_iff sup_closed_set_def)

lemma lsu_inf_closed_var [simp]: "\<nu>\<^sup>\<natural> (\<nu>\<^sup>\<natural> x \<sqinter> \<nu>\<^sup>\<natural> y) = \<nu>\<^sup>\<natural> (x::'a::unital_quantale) \<sqinter> \<nu>\<^sup>\<natural> y"
  by (metis (no_types, lifting) lsided_def3 lsl_inf_closed_var lsl_lsu_prop_eq o_apply)

lemma lsu_sup_closed_var [simp]: "\<nu>\<^sup>\<natural> (\<nu>\<^sup>\<natural> x \<squnion> \<nu>\<^sup>\<natural> y) = \<nu>\<^sup>\<natural> (x::'a::unital_quantale) \<squnion> \<nu>\<^sup>\<natural> y"
  by (metis (no_types, lifting) lsided_def3 lsl_lsu_prop_eq lsl_sup_closed_var o_def)

lemma lsu_fres_closed [simp]: "\<nu>\<^sup>\<natural> (\<nu>\<^sup>\<natural> x \<leftarrow> \<nu>\<^sup>\<natural> y) = \<nu>\<^sup>\<natural> x \<leftarrow> \<nu>\<^sup>\<natural> (y::'a::unital_quantale)"
  unfolding lsu_def by (simp add: bres_curry fres_bres)

lemma lsl_fres_closed [simp]: "\<nu> (\<nu> x \<leftarrow> \<nu> y) = \<nu> x \<leftarrow> \<nu> (y::'a::unital_quantale)"
  unfolding lsl_def by (metis fres_interchange lsd_def lsided_eq mult.assoc slsd_def top_times_top)

lemma lsl_almost_lax: "x \<cdot> \<nu> y \<le> \<nu> (y::'a::unital_quantale)"
  by (metis inf_top.right_neutral lsided_eq lsided_prop lsl_def lsl_inf_closed_var mult.right_neutral slsd_def)

text \<open>Finally, here are two counterexamples.\<close>

lemma "\<nu>\<^sup>\<natural> (\<nu>\<^sup>\<natural> x \<rightarrow> \<nu>\<^sup>\<natural> y) = \<nu>\<^sup>\<natural> x \<rightarrow> \<nu>\<^sup>\<natural> (y::'a::unital_quantale)" (*nitpick*)
  oops

lemma "\<nu> (\<nu> x \<rightarrow> \<nu> y) = \<nu> x \<rightarrow> \<nu> (y::'a::unital_quantale)" (*nitpick*)
  oops
 
context ab_quantale
begin
  
lemma lsided_times_top: "lsd (\<top> \<cdot> x)"
  by (metis lsd_def mult_isor top_greatest mult_assoc)

lemma lsided_le2: "lsd x \<Longrightarrow> x \<cdot> y \<le> x \<sqinter> (y \<cdot> \<top>)"
  using lsided_prop psrpq.mult_isol mult_commute by auto
    
lemma lsided_le3: "lsd x \<Longrightarrow> (x \<sqinter> y) \<cdot> z \<le> x"
  by (metis inf_le1 lsided_prop mult_isol order_trans mult_commute)
    
lemma lsided_le4: "lsd x \<Longrightarrow> (x \<sqinter> y) \<cdot> z \<le> x \<sqinter> (y \<cdot> z)"
  by (simp add: mult_isor lsided_le3)

lemma lsided_times_le_inf: "lsd x \<Longrightarrow> lsd y \<Longrightarrow> x \<cdot> y \<le> x \<sqinter> y"
  using lsided_prop lsided_le2 by force

end

text \<open>Now lsl is a quantic nucleus.\<close>

lemma lsl_lax: "\<nu> x \<cdot> \<nu> y \<le> \<nu> (x \<cdot> (y::'aa::ab_unital_quantale))"
  by (metis (no_types, hide_lams) lsl_almost_lax lsl_def mult.commute mult.left_commute)

lemma lsl_nuc: "nucleus (\<nu>::'a::ab_unital_quantale \<Rightarrow> 'a)" 
  by (simp add: lsl_clop nucleus_def lsl_lax)

text \<open>The following properties go beyond nuclei.\<close>

lemma lsl_comp_pres: "\<nu> (x \<cdot> y) = \<nu> x \<cdot> \<nu> (y::'a::ab_unital_quantale)"
  by (metis (no_types, lifting) lsl_comp_closed_var lsl_nuc nuc_prop1 nuc_prop2)

lemma lsl_bres_closed [simp]: "\<nu> (\<nu> x \<rightarrow> \<nu> y) = \<nu> x \<rightarrow> \<nu> (y::'a::ab_unital_quantale)"
  by (simp add: lsl_nuc nuc_bres_closed)

lemma lsu_bres_pres [simp]: "\<nu>\<^sup>\<natural> (\<nu>\<^sup>\<natural> x \<rightarrow> \<nu>\<^sup>\<natural> y) = \<nu>\<^sup>\<natural> x \<rightarrow> \<nu>\<^sup>\<natural> (y::'a::ab_unital_quantale)"
  by (simp add: bres_fres_eq)

lemma lsl_prelocalic_var: "\<nu> x \<cdot> y \<le> \<nu> x \<sqinter> \<nu> (y::'a::ab_unital_quantale)"
  by (metis inf_top.right_neutral lsided_le4 lsided_times_top lsl_def)

lemma dang3: "(\<nu> x \<sqinter> y) \<cdot> z \<le> \<nu> x \<sqinter> (y \<cdot> (z::'a::ab_unital_quantale))"
  by (metis lsided_le4 lsided_times_top lsl_def)

lemma lsl_prelocalic: "\<nu> x \<cdot> \<nu> y \<le> \<nu> x \<sqinter> \<nu> (y::'a::ab_unital_quantale)"
  by (metis lsided_times_le_inf lsided_times_top lsl_def) 

lemma lsl_local: "x \<cdot> \<nu> y \<le> \<nu> (x \<cdot> (y::'a::ab_unital_quantale))"
  by (simp add: lsl_def mult.left_commute)

lemma lsl_local_eq: "x \<cdot> \<nu> y = \<nu> (x \<cdot> (y::'a::ab_unital_quantale))"
  by (simp add: lsl_def mult.left_commute)


text \<open>Relative pseudocomplementation can be defined on the subquantale induced by lsu.\<close>

definition "rpc x y = \<nu>\<^sup>\<natural> (-x \<squnion> (y::'a::bool_unital_quantale))"

lemma lsl_rpc [simp]: "\<nu> (rpc x y) = rpc x y"
  by (metis lsl_lsu_prop_eq o_apply rpc_def)

lemma lsu_rpc [simp]: "\<nu>\<^sup>\<natural> (rpc x y) = rpc x y"
  using lsided_def3 lsl_rpc by blast

lemma lsl_rpc_galois: "(x \<sqinter> \<nu> z \<le> y) = (z \<le> rpc x (y::'a::bool_unital_quantale))"
  unfolding rpc_def by (metis adj_def inf_commute ls_galois shunt1) 

lemma lsl_rpc_galois_var: "x \<sqinter> \<nu> z \<le> y \<longleftrightarrow> \<nu> z \<le> rpc x y"
  by (metis adj_def ls_galois lsl_rpc_galois lsu_rpc)

lemma rpc_expl_aux: "\<Squnion>{z. x \<sqinter> \<nu> z \<le> y} = \<Squnion>{z. x \<sqinter> z \<le> y \<and> \<nu> z = (z::'a::bool_unital_quantale)}"
proof (rule antisym)
  show "\<Squnion>{z. x \<sqinter> \<nu> z \<le> y} \<le> \<Squnion>{z. x \<sqinter> z \<le> y \<and> \<nu> z = z}"
    apply (rule Sup_mono, safe)
    by (smt lsided_eq lsided_prop lsl_def lsl_lsu_prop_eq lsl_rpc_galois mem_Collect_eq o_apply rpc_def slsd_def)
  show " \<Squnion>{z. x \<sqinter> z \<le> y \<and> \<nu> z = z} \<le> \<Squnion>{z. x \<sqinter> \<nu> z \<le> y}"
     by (simp add: Collect_mono_iff Sup_subset_mono)
 qed
 
lemma rpc_expl: "rpc x y = \<Squnion>{z. x \<sqinter> z \<le> y \<and> \<nu> z = (z::'a::bool_unital_quantale)}"
proof-
  have "rpc x y = \<Squnion>{z. z \<le> rpc x y}"
    using Sup_atMost atMost_def by metis
  also have "... = \<Squnion>{z. x \<sqinter> \<nu> z \<le> y}"
    using lsl_rpc_galois by metis
  finally show ?thesis
    by (simp add: rpc_expl_aux)
qed


subsection \<open>Non-Preservation and Lack of Closure\<close>

context bool_ab_unital_quantale
begin

text \<open>A few counterexamples deal in particular with lack of closure with respect to boolean complementation.\<close>

lemma "\<nu>\<^sup>\<natural> (x \<cdot> y) = \<nu>\<^sup>\<natural> x \<cdot> \<nu>\<^sup>\<natural> y" (*nitpick    *)
  oops

lemma "\<nu> 1 = 1" (*nitpick*)
  oops

lemma "\<nu>\<^sup>\<natural> x = \<nu> x" (*nitpick*)
  oops

lemma "\<nu>\<^sup>\<natural> (\<Squnion> P) = \<Squnion>{\<nu>\<^sup>\<natural> p |p. p \<in> P}" (*nitpick*)
  oops

lemma "rpc (\<nu>\<^sup>\<natural> x) (\<nu>\<^sup>\<natural> y) = -(\<nu>\<^sup>\<natural> x) \<squnion> (\<nu>\<^sup>\<natural> y)" (*nitpick*)
  oops

lemma "rpc (\<nu> x) (\<nu> y) = -(\<nu> x) \<squnion> (\<nu> y)" (*nitpick*)
  oops

lemma "\<nu> (-(\<nu>\<^sup>\<natural> x) \<squnion> (\<nu>\<^sup>\<natural> y)) = -(\<nu>\<^sup>\<natural> x) \<squnion> (\<nu>\<^sup>\<natural> y)" (*nitpick*)
  oops

lemma "\<nu> (-(\<nu> x) \<squnion> (\<nu> y)) = -(\<nu> x) \<squnion> (\<nu> y)" (*nitpick*)
  oops

lemma  "\<nu> x \<cdot> \<nu> y = \<nu> x \<sqinter> \<nu> y" (*nitpick this rules out localic nuclei.*)
  oops

lemma "\<nu> (- (\<nu> x)) = - (\<nu> x)"  (*nitpick*)
  oops 

lemma "\<nu>\<^sup>\<natural> (- (\<nu>\<^sup>\<natural> x)) = - (\<nu>\<^sup>\<natural> x)"  (*nitpick*)
  oops

lemma "\<nu> (- (\<nu> x) \<squnion> (\<nu> y)) = - (\<nu> x) \<squnion> (\<nu> y)"  (*nitpick*)
  oops 

lemma "\<nu>\<^sup>\<natural> (- (\<nu>\<^sup>\<natural> x) \<squnion> (\<nu>\<^sup>\<natural> y)) = - (\<nu>\<^sup>\<natural> x) \<squnion> (\<nu>\<^sup>\<natural> y)"  (*nitpick*)
  oops  

end


subsection \<open>Properties of Quotient Algebras and Subalgebras\<close>

text \<open>Finally I replay Rosenthal's quotient and subalgebra proofs for nuclei and conuclei in the concrete setting of left-sided elements. Ideally
it should be sufficient to show that lsl is a (quantale with) nucleus and then pick up the quotient algebra proof from the nucleus section. But there is no
way of achieving this, apart from creating a type class for quantales with the lsl operation. This seems bizarre, since lsl is just a definition.
On the other hand, an approach in which interpretations are used instead of instantiations might do the job.\<close>

text \<open>The first proof shows that lsu, as a conucleus, yields a subalgebra.\<close>

typedef (overloaded) 'a lsu_set = "Fix (\<nu>\<^sup>\<natural>::'a::unital_quantale \<Rightarrow> 'a)"
  using Fix_lsu_iff lsu_bot by blast

setup_lifting type_definition_lsu_set

instantiation lsu_set :: (unital_quantale) quantale
begin

lift_definition times_lsu_set :: "'a lsu_set \<Rightarrow> 'a lsu_set \<Rightarrow> 'a lsu_set" is times
  using comp_closed_set_def lsu_comp_closed by blast
 
lift_definition Inf_lsu_set :: "'a lsu_set set \<Rightarrow> 'a lsu_set" is Inf
  by (metis Fix_lsl_lsu Inf_closed_set_def lsl_Inf_closed subset_eq)
 
lift_definition  Sup_lsu_set :: "'a lsu_set set \<Rightarrow> 'a lsu_set" is Sup
  using Sup_closed_set_def lsu_Sup_closed subsetI by blast
 
lift_definition  bot_lsu_set ::  "'a lsu_set" is "\<bottom>"
  by simp

lift_definition sup_lsu_set :: "'a lsu_set \<Rightarrow> 'a lsu_set \<Rightarrow> 'a lsu_set" is sup
  by (metis Fix_lsu_iff lsu_sup_closed_var)

lift_definition top_lsu_set ::  "'a lsu_set" is "\<top>"
  by simp

lift_definition inf_lsu_set :: "'a lsu_set \<Rightarrow> 'a lsu_set \<Rightarrow> 'a lsu_set" is inf
  by (metis Fix_lsu_iff lsu_inf_closed_var)
  
lift_definition less_eq_lsu_set :: "'a lsu_set \<Rightarrow> 'a lsu_set \<Rightarrow> bool" is less_eq .

lift_definition  less_lsu_set :: "'a lsu_set \<Rightarrow> 'a lsu_set \<Rightarrow> bool" is less .

instance
  by (intro_classes; transfer, simp_all add: mult.assoc Inf_lower Inf_greatest Sup_upper Sup_least less_le_not_le Sup_distr Sup_distl)

end

text \<open>This proof checks simply closure conditions, as one would expect for establishing a subalgebra.\<close>

instance lsu_set :: (bool_ab_unital_quantale) distrib_ab_quantale
  apply (intro_classes; transfer)
   apply (simp add: mult.commute)
  using sup_inf_distrib1 by blast
 
typedef (overloaded) 'a lsl_set = "range (\<nu>::'a:: unital_quantale \<Rightarrow> 'a)"
  by blast

setup_lifting type_definition_lsl_set

text \<open>The final statement shows that lsu, as a nucleus, yields a quotient algebra.\<close>

instantiation lsl_set :: (ab_unital_quantale) ab_unital_quantale
begin

lift_definition one_lsl_set :: "'a::ab_unital_quantale lsl_set" is "\<nu> 1"
  by blast

lift_definition Inf_lsl_set :: "'a lsl_set set \<Rightarrow> 'a lsl_set" is "\<lambda>X. \<nu> (\<Sqinter>X)"
  by blast

lift_definition Sup_lsl_set :: "'a lsl_set set \<Rightarrow> 'a lsl_set" is "\<lambda>X. \<nu> (\<Squnion>X)"
  by blast

lift_definition bot_lsl_set :: "'a lsl_set" is "\<nu> \<bottom>"
  by blast

lift_definition sup_lsl_set :: "'a lsl_set \<Rightarrow> 'a lsl_set \<Rightarrow> 'a lsl_set" is "\<lambda>x y. \<nu> x \<squnion> \<nu> y"
  by auto (metis lsl_sup_closed_var)

lift_definition   top_lsl_set :: "'a lsl_set" is "\<nu> \<top>"
  by blast

lift_definition  inf_lsl_set :: "'a lsl_set \<Rightarrow> 'a lsl_set \<Rightarrow> 'a lsl_set" is "\<lambda>x y. \<nu> x \<sqinter> \<nu> y"
  by (meson lsl_inf_closed_var range_lsl_iff)

lift_definition less_eq_lsl_set :: "'a lsl_set \<Rightarrow> 'a lsl_set \<Rightarrow> bool" is "\<lambda>x y . \<nu> x \<le> \<nu> y" .

lift_definition less_lsl_set :: "'a lsl_set \<Rightarrow> 'a lsl_set \<Rightarrow> bool" is "\<lambda>x y. \<nu> x \<le> \<nu> y \<and> x \<noteq> y" .

lift_definition   times_lsl_set :: "'a lsl_set \<Rightarrow> 'a lsl_set \<Rightarrow> 'a lsl_set" is "\<lambda> x y. \<nu> (x \<cdot> y)"
  by blast

instance
  apply (standard; transfer)
                      apply (simp add: lsl_local_eq mult.commute mult.left_commute)
                      apply (simp add: mult.commute)
                     apply auto[1]
                    apply fastforce+
                  apply auto[1]
                 apply fastforce+
           apply (metis Inf_lower lsl_iso_var range_lsl_iff)
          apply (metis Inf_greatest lsl_iso_var range_lsl_iff)
         apply (metis Sup_upper lsl_iso_var range_lsl_iff)
        apply (metis Sup_least lsl_iso_var range_lsl_iff)
       apply fastforce+
     apply (smt Sup_distl image_cong lsl_local_eq mult.commute)
    apply (smt Sup_distl image_cong lsl_local_eq mult.commute)
   apply (simp add: lsl_def cong del: image_cong_simp)
  apply (simp add: lsl_local_eq)
  done

end

text \<open>This proof checks preservation properties instead of closure ones.\<close>

end 
