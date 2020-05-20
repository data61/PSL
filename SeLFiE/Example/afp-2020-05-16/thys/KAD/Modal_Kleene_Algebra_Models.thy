(* Title:      Models of Modal Kleene Algebras
   Author:     Victor B. F. Gomes, Walter Guttmann, Peter Höfner, Georg Struth, Tjark Weber
   Maintainer: Walter Guttmann <walter.guttman at canterbury.ac.nz>
               Georg Struth <g.struth at sheffield.ac.uk>
               Tjark Weber <tjark.weber at it.uu.se>
*)

section \<open>Models of Modal Kleene Algebras\<close>

theory Modal_Kleene_Algebra_Models
imports Kleene_Algebra.Kleene_Algebra_Models
  Modal_Kleene_Algebra

begin

text \<open>
  This section develops the relation model. We also briefly develop the trace model for
  antidomain Kleene algebras, but not for antirange or full modal Kleene algebras.
  The reason is that traces are implemented as lists; we therefore expect tedious inductive
  proofs in the presence of range. The language model is not particularly interesting.
\<close>

definition rel_ad :: "'a rel \<Rightarrow> 'a rel" where
  "rel_ad R = {(x,x) | x. \<not> (\<exists>y. (x,y) \<in> R)}"

interpretation rel_antidomain_kleene_algebra: antidomain_kleene_algebra rel_ad "(\<union>)" "(O)" Id "{}" "(\<subseteq>)" "(\<subset>)" rtrancl
by unfold_locales (auto simp: rel_ad_def)

definition trace_a :: "('p, 'a) trace set \<Rightarrow> ('p, 'a) trace set" where
  "trace_a X = {(p,[]) | p. \<not> (\<exists>x. x \<in> X \<and> p = first x)}"

interpretation trace_antidomain_kleene_algebra: antidomain_kleene_algebra trace_a "(\<union>)" t_prod t_one t_zero "(\<subseteq>)" "(\<subset>)" t_star
proof
  show "\<And>x. t_prod (trace_a x) x = t_zero"
    by (auto simp: trace_a_def t_prod_def t_fusion_def t_zero_def)
  show "\<And>x y. trace_a (t_prod x y) \<union> trace_a (t_prod x (trace_a (trace_a y))) = trace_a (t_prod x (trace_a (trace_a y)))"
    by (auto simp: trace_a_def t_prod_def t_fusion_def)
  show "\<And>x. trace_a (trace_a x) \<union> trace_a x = t_one"
    by (auto simp: trace_a_def t_one_def)
qed

text \<open>The trace model should be extended to cover modal Kleene algebras in the future.\<close>

definition rel_ar :: "'a rel \<Rightarrow> 'a rel" where
  "rel_ar R = {(y,y) | y. \<not> (\<exists>x. (x,y) \<in> R)}"

interpretation rel_antirange_kleene_algebra: antirange_semiring "(\<union>)" "(O)" Id "{}" rel_ar "(\<subseteq>)" "(\<subset>)"
apply unfold_locales
apply (simp_all add: rel_ar_def)
by auto

interpretation rel_modal_kleene_algebra: modal_kleene_algebra "(\<union>)" "(O)" Id "{}" "(\<subseteq>)" "(\<subset>)" rtrancl rel_ad rel_ar
apply standard
apply (metis (no_types, lifting) rel_antidomain_kleene_algebra.a_d_closed rel_antidomain_kleene_algebra.a_one rel_antidomain_kleene_algebra.addual.ars_r_def rel_antidomain_kleene_algebra.am5_lem rel_antidomain_kleene_algebra.am6_lem rel_antidomain_kleene_algebra.apd_d_def rel_antidomain_kleene_algebra.dka.dns1 rel_antidomain_kleene_algebra.dpdz.dom_one rel_antirange_kleene_algebra.ardual.a_comm' rel_antirange_kleene_algebra.ardual.a_d_closed rel_antirange_kleene_algebra.ardual.a_mul_d' rel_antirange_kleene_algebra.ardual.a_mult_idem rel_antirange_kleene_algebra.ardual.a_zero rel_antirange_kleene_algebra.ardual.ads_d_def rel_antirange_kleene_algebra.ardual.am6_lem rel_antirange_kleene_algebra.ardual.apd_d_def rel_antirange_kleene_algebra.ardual.s4)
by (metis rel_antidomain_kleene_algebra.a_zero rel_antidomain_kleene_algebra.addual.ars1 rel_antidomain_kleene_algebra.addual.ars_r_def rel_antidomain_kleene_algebra.am5_lem rel_antidomain_kleene_algebra.am6_lem rel_antidomain_kleene_algebra.ds.ddual.mult_oner rel_antidomain_kleene_algebra.s4 rel_antirange_kleene_algebra.ardual.ads_d_def rel_antirange_kleene_algebra.ardual.am6_lem rel_antirange_kleene_algebra.ardual.apd1 rel_antirange_kleene_algebra.ardual.dpdz.dns1'')

end
