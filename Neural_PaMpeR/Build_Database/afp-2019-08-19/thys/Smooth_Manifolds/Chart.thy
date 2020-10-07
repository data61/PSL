section \<open>Charts\<close>
theory Chart
  imports Analysis_More
begin

subsection \<open>Definition\<close>

text \<open>A chart on \<open>M\<close> is a homeomorphism from an open subset of \<open>M\<close> to an open subset
  of some Euclidean space \<open>E\<close>. Here \<open>d\<close> and \<open>d'\<close> are open subsets of \<open>M\<close> and \<open>E\<close>, respectively,
  \<open>f: d \<rightarrow> d'\<close> is the mapping, and \<open>f': d' \<rightarrow> d\<close> is the inverse mapping.\<close>
typedef (overloaded) ('a::topological_space, 'e::euclidean_space) chart =
  "{(d::'a set, d'::'e set, f, f').
    open d \<and> open d' \<and> homeomorphism d d' f f'}"
  by (rule exI[where x="({}, {}, (\<lambda>x. undefined), (\<lambda>x. undefined))"]) simp

setup_lifting type_definition_chart

lift_definition apply_chart::"('a::topological_space, 'e::euclidean_space) chart \<Rightarrow> 'a \<Rightarrow> 'e"
  is "\<lambda>(d, d', f, f'). f" .

declare [[coercion apply_chart]]

lift_definition inv_chart::"('a::topological_space, 'e::euclidean_space) chart \<Rightarrow> 'e \<Rightarrow> 'a"
  is "\<lambda>(d, d', f, f'). f'" .

lift_definition domain::"('a::topological_space, 'e::euclidean_space) chart \<Rightarrow> 'a set"
  is "\<lambda>(d, d', f, f'). d" .

lift_definition codomain::"('a::topological_space, 'e::euclidean_space) chart \<Rightarrow> 'e set"
  is "\<lambda>(d, d', f, f'). d'" .


subsection \<open>Properties\<close>

lemma open_domain[intro, simp]: "open (domain c)"
  and open_codomain[intro, simp]: "open (codomain c)"
  and chart_homeomorphism: "homeomorphism (domain c) (codomain c) c (inv_chart c)"
  by (transfer, auto)+

lemma at_within_domain: "at x within domain c = at x" if "x \<in> domain c"
  by (rule at_within_open[OF that open_domain])

lemma at_within_codomain: "at x within codomain c = at x" if "x \<in> codomain c"
  by (rule at_within_open[OF that open_codomain])

lemma
  chart_in_codomain[intro, simp]: "x \<in> domain c \<Longrightarrow> c x \<in> codomain c"
  and inv_chart_inverse[simp]: "x \<in> domain c \<Longrightarrow> inv_chart c (c x) = x"
  and inv_chart_in_domain[intro, simp]:"y \<in> codomain c \<Longrightarrow> inv_chart c y \<in> domain c"
  and chart_inverse_inv_chart[simp]: "y \<in> codomain c \<Longrightarrow> c (inv_chart c y) = y"
  and image_domain_eq: "c ` (domain c) = codomain c"
  and inv_image_codomain_eq[simp]: "inv_chart c ` (codomain c) = domain c"
  and continuous_on_domain: "continuous_on (domain c) c"
  and continuous_on_codomain: "continuous_on (codomain c) (inv_chart c)"
  using chart_homeomorphism[of c]
  by (auto simp: homeomorphism_def)

lemma chart_eqI: "c = d"
  if "domain c = domain d"
    "codomain c = codomain d"
    "\<And>x. c x = d x"
    "\<And>x. inv_chart c x = inv_chart  d x"
  using that
  by transfer auto

lemmas continuous_on_chart[continuous_intros] =
  continuous_on_compose2[OF continuous_on_domain]
  continuous_on_compose2[OF continuous_on_codomain]

lemma continuous_apply_chart: "continuous (at x within X) c" if "x \<in> domain c"
  apply (rule continuous_at_imp_continuous_within)
  using continuous_on_domain[of c] that at_within_domain[OF that]
  by (auto simp: continuous_on_eq_continuous_within)

lemma continuous_inv_chart: "continuous (at x within X) (inv_chart c)" if "x \<in> codomain c"
  apply (rule continuous_at_imp_continuous_within)
  using continuous_on_codomain[of c] that at_within_codomain[OF that]
  by (auto simp: continuous_on_eq_continuous_within)

lemmas apply_chart_tendsto[tendsto_intros] = isCont_tendsto_compose[OF continuous_apply_chart, rotated]
lemmas inv_chart_tendsto[tendsto_intros] = isCont_tendsto_compose[OF continuous_inv_chart, rotated]

lemma continuous_within_compose2':
  "continuous (at (f x) within t) g \<Longrightarrow> f ` s \<subseteq> t \<Longrightarrow>
    continuous (at x within s) f \<Longrightarrow>
    continuous (at x within s) (\<lambda>x. g (f x))"
  by (simp add: continuous_within_compose2 continuous_within_subset)

lemmas continuous_chart[continuous_intros] =
  continuous_within_compose2'[OF continuous_apply_chart]
  continuous_within_compose2'[OF continuous_inv_chart]

lemma continuous_on_chart_inv:
  assumes "continuous_on s (apply_chart c o f)"
    "f ` s \<subseteq> domain c"
  shows "continuous_on s f"
proof -
  have "continuous_on s (inv_chart c o apply_chart c o f)"
    using assms by (auto intro!: continuous_on_chart(2))
  moreover have "\<And>x. x \<in> s \<Longrightarrow> (inv_chart c o apply_chart c o f) x = f x"
    using assms by auto
  ultimately show ?thesis by auto
qed

lemma continuous_on_chart_inv':
  assumes "continuous_on (apply_chart c ` s) (f o inv_chart c)"
    "s \<subseteq> domain c"
  shows "continuous_on s f"
proof -
  have "continuous_on s (apply_chart c)"
    using assms continuous_on_domain continuous_on_subset by blast
  then have "continuous_on s (f o inv_chart c o apply_chart c)"
    apply (rule continuous_on_compose) using assms by auto
  moreover have "(f o inv_chart c o apply_chart c) x = f x" if "x \<in> s" for x
    using assms that by auto
  ultimately show ?thesis by auto
qed

lemma inj_on_apply_chart: "inj_on (apply_chart f) (domain f)"
  by (auto simp: intro!: inj_on_inverseI[where g="inv_chart f"])

lemma apply_chart_Int: "f ` (X \<inter> Y) = f ` X \<inter> f ` Y" if "X \<subseteq> domain f" "Y \<subseteq> domain f"
  using inj_on_apply_chart that
  by (rule inj_on_image_Int)

lemma chart_image_eq_vimage: "c ` X = inv_chart c -` X \<inter> codomain c"
  if "X \<subseteq> domain c"
  using that
  by force

lemma open_chart_image[simp, intro]: "open (c ` X)"
  if "open X" "X \<subseteq> domain c"
proof -
  have "c ` X = inv_chart c -` X \<inter> codomain c"
    using that(2)
    by (rule chart_image_eq_vimage)
  also have "open \<dots>"
    using that
    by (metis continuous_on_codomain continuous_on_open_vimage open_codomain)
  finally show ?thesis .
qed

lemma open_inv_chart_image[simp, intro]: "open (inv_chart c ` X)"
  if "open X" "X \<subseteq> codomain c"
proof -
  have "inv_chart c ` X = c -` X \<inter> domain c"
    using that(2)
    apply (auto simp: )
    using image_iff by fastforce
  also have "open \<dots>"
    using that
    by (metis continuous_on_domain continuous_on_open_vimage open_domain)
  finally show ?thesis .
qed

lemma homeomorphism_UNIV_imp_open_map:
  "homeomorphism UNIV UNIV p p' \<Longrightarrow> open f' \<Longrightarrow> open (p ` f')"
  by (auto dest: homeomorphism_imp_open_map[where U=f'])


subsection \<open>Restriction\<close>

lemma homeomorphism_restrict:
  "homeomorphism (a \<inter> s) (b \<inter> f' -` s) f f'" if "homeomorphism a b f f'"
  using that
  by (fastforce simp: homeomorphism_def intro: continuous_on_subset intro!: imageI)

lift_definition restrict_chart::"'a set \<Rightarrow> ('a::t2_space, 'e::euclidean_space) chart \<Rightarrow> ('a, 'e) chart"
  is "\<lambda>S. \<lambda>(d, d', f, f'). if open S then (d \<inter> S, d' \<inter> f' -` S, f, f') else ({}, {}, f, f')"
  by (auto simp: split: if_splits intro!: open_continuous_vimage' homeomorphism_restrict
      intro: homeomorphism_cont2 homeomorphism_cont1 )

lemma restrict_chart_restrict_chart:
  "restrict_chart X (restrict_chart Y c) = restrict_chart (X \<inter> Y) c"
  if "open X" "open Y"
  using that
  by transfer auto

lemma domain_restrict_chart[simp]: "open S \<Longrightarrow> domain (restrict_chart S c) = domain c \<inter> S"
  and domain_restrict_chart_if: "domain (restrict_chart S c) = (if open S then domain c \<inter> S else {})"
  and codomain_restrict_chart[simp]: "open S \<Longrightarrow> codomain (restrict_chart S c) = codomain c \<inter> inv_chart c -` S"
  and codomain_restrict_chart_if: "codomain (restrict_chart S c) = (if open S then codomain c \<inter> inv_chart c -` S else {})"
  and apply_chart_restrict_chart[simp]: "apply_chart (restrict_chart S c) = apply_chart c"
  and inv_chart_restrict_chart[simp]: "inv_chart (restrict_chart S c) = inv_chart c"
  by (transfer, auto)+


subsection \<open>Composition\<close>

lift_definition compose_chart::"('e\<Rightarrow>'e) \<Rightarrow> ('e\<Rightarrow>'e) \<Rightarrow>
  ('a::topological_space, 'e::euclidean_space) chart \<Rightarrow> ('a, 'e) chart"
  is "\<lambda>p p'. \<lambda>(d, d', f, f'). if homeomorphism UNIV UNIV p p' then (d, p ` d', p o f, f' o p')
    else ({}, {}, f, f')"
  by (auto split: if_splits)
    (auto intro: homeomorphism_UNIV_imp_open_map homeomorphism_compose homeomorphism_of_subsets)

lemma compose_chart_apply_chart[simp]: "apply_chart (compose_chart p p' c) = p o apply_chart c"
  and compose_chart_inv_chart[simp]: "inv_chart (compose_chart p p' c) = inv_chart c o p'"
  and domain_compose_chart[simp]: "domain (compose_chart p p' c) = domain c"
  and codomain_compose_chart[simp]: "codomain (compose_chart p p' c) = p ` codomain c"
  if "homeomorphism UNIV UNIV p p'"
  using that by (transfer, auto)+

end
