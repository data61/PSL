section \<open>Product Manifold\<close>
theory Product_Manifold
  imports Differentiable_Manifold
begin

locale c_manifold_prod =
  m1: c_manifold charts1 k + 
  m2: c_manifold charts2 k for k charts1 charts2

begin

lift_definition prod_chart :: "('a, 'b) chart \<Rightarrow> ('c, 'd) chart \<Rightarrow> ('a \<times> 'c, 'b \<times> 'd) chart"
  is "\<lambda>(d::'a set, d'::'b set, f::'a\<Rightarrow>'b, f'::'b\<Rightarrow>'a).
      \<lambda>(e::'c set, e'::'d set, g::'c\<Rightarrow>'d, g'::'d\<Rightarrow>'c).
        (d \<times> e, d' \<times> e', \<lambda>(x,y). (f x, g y), \<lambda>(x,y). (f' x, g' y))"
  by (auto intro: open_Times simp: homeomorphism_prod)

lemma domain_prod_chart[simp]: "domain (prod_chart c1 c2) = domain c1 \<times> domain c2"
  and codomain_prod_chart[simp]: "codomain (prod_chart c1 c2) = codomain c1 \<times> codomain c2"
  and apply_prod_chart[simp]: "apply_chart (prod_chart c1 c2) = (\<lambda>(x,y). (c1 x, c2 y))"
  and inv_chart_prod_chart[simp]: "inv_chart (prod_chart c1 c2) = (\<lambda>(x,y). (inv_chart c1 x, inv_chart c2 y))"
  by (transfer, auto)+

lemma prod_chart_compat:
  "k-smooth_compat (prod_chart c1 c2) (prod_chart d1 d2)"
  if compat1: "k-smooth_compat c1 d1" and compat2: "k-smooth_compat c2 d2"
  unfolding smooth_compat_def
  apply (auto simp add: comp_def case_prod_beta cong del: image_cong_simp)
   apply (simp add: Times_Int_Times image_prod)
   apply (rule smooth_on_Pair')
      apply (auto intro!: continuous_intros)
    apply (auto simp: compat1[unfolded smooth_compat_def comp_def])
    apply (auto simp: compat2[unfolded smooth_compat_def comp_def])
   apply (simp add: Times_Int_Times image_prod)
   apply (rule smooth_on_Pair')
     apply (auto intro!: continuous_intros)
    apply (auto simp: compat2[unfolded smooth_compat_def comp_def])
    apply (auto simp: compat1[unfolded smooth_compat_def comp_def])
  done

definition prod_charts :: "('a \<times> 'c, 'b \<times> 'd) chart set" where
  "prod_charts = {prod_chart c1 c2 | c1 c2. c1 \<in> charts1 \<and> c2 \<in> charts2}"

lemma c_manifold_atlas_product: "c_manifold prod_charts k"
  apply (unfold_locales)
proof -
  fix c d assume c: "c \<in> prod_charts" and d: "d \<in> prod_charts"
  obtain c1 c2 where c_def: "c = prod_chart c1 c2" and c1: "c1 \<in> charts1" and c2: "c2 \<in> charts2"
    using c prod_charts_def by auto
  obtain d1 d2 where d_def: "d = prod_chart d1 d2" and d1: "d1 \<in> charts1" and d2: "d2 \<in> charts2"
    using d prod_charts_def by auto
  have compat1: "k-smooth_compat c1 d1"
    using c1 d1 by (auto intro: m1.pairwise_compat)
  have compat2: "k-smooth_compat c2 d2"
    using c2 d2 by (auto intro: m2.pairwise_compat)
  show "k-smooth_compat c d"
    unfolding c_def d_def
  using compat1 compat2 by (rule prod_chart_compat)
qed

end

end