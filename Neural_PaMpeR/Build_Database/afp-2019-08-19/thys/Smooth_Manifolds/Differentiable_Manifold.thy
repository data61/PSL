section \<open>Differentiable/Smooth Manifolds\<close>
theory Differentiable_Manifold
  imports
    Smooth
    Topological_Manifold
begin

subsection \<open>Smooth compatibility\<close>

definition smooth_compat::"enat \<Rightarrow> ('a::topological_space, 'e::euclidean_space)chart\<Rightarrow>('a, 'e)chart\<Rightarrow>bool"
  ("_-smooth'_compat" [1000])
  where
  "smooth_compat k c1 c2 \<longleftrightarrow>
    (k-smooth_on (c1 ` (domain c1 \<inter> domain c2)) (c2 \<circ> inv_chart c1) \<and>
     k-smooth_on (c2 ` (domain c1 \<inter> domain c2)) (c1 \<circ> inv_chart c2) )"

lemma smooth_compat_D1:
  "k-smooth_on (c1 ` (domain c1 \<inter> domain c2)) (c2 \<circ> inv_chart c1)"
  if "k-smooth_compat c1 c2"
proof -
  have "open (c1 ` (domain c1 \<inter> domain c2))"
    by (rule open_chart_image) auto
  moreover have "k-smooth_on (c1 ` (domain c1 \<inter> domain c2)) (c2 \<circ> inv_chart c1)"
    using that(1) by (auto simp: smooth_compat_def)
  ultimately show ?thesis by blast
qed

lemma smooth_compat_D2:
  "k-smooth_on (c2 ` (domain c1 \<inter> domain c2)) (c1 \<circ> inv_chart c2)"
  if "k-smooth_compat c1 c2"
proof -
  have "open (c2 ` (domain c1 \<inter> domain c2))"
    by (rule open_chart_image) auto
  moreover have "k-smooth_on (c2 ` (domain c1 \<inter> domain c2)) (c1 \<circ> inv_chart c2) "
    using that(1) by (auto simp: smooth_compat_def)
  ultimately show ?thesis by blast
qed

lemma smooth_compat_refl: "k-smooth_compat x x"
  unfolding smooth_compat_def
  by (auto intro: smooth_on_cong[where g="\<lambda>x. x"] simp: smooth_on_id)

lemma smooth_compat_commute: "k-smooth_compat x y \<longleftrightarrow> k-smooth_compat y x"
  by (auto simp: smooth_compat_def inf_commute)

lemma smooth_compat_restrict_chartI:
  "k-smooth_compat (restrict_chart S c) c'"
  if "k-smooth_compat c c'"
  using that
  by (auto simp: smooth_compat_def domain_restrict_chart_if intro: smooth_on_subset)

lemma smooth_compat_restrict_chartI2:
  "k-smooth_compat c' (restrict_chart S c)"
  if "k-smooth_compat c' c"
  using smooth_compat_restrict_chartI[of k c c'] that
  by (auto simp: smooth_compat_commute)

lemma smooth_compat_restrict_chartD:
  "domain c1 \<subseteq> U \<Longrightarrow> open U \<Longrightarrow> k-smooth_compat c1 (restrict_chart U c2) \<Longrightarrow> k-smooth_compat c1 c2"
  by (auto simp: smooth_compat_def domain_restrict_chart_if intro: smooth_on_subset)

lemma smooth_compat_restrict_chartD2:
  "domain c1 \<subseteq> U \<Longrightarrow> open U \<Longrightarrow> k-smooth_compat (restrict_chart U c2) c1 \<Longrightarrow> k-smooth_compat c2 c1"
  using smooth_compat_restrict_chartD[of c1 U k c2]
  by (auto simp: smooth_compat_commute)

lemma smooth_compat_le:
  "l-smooth_compat c1 c2" if "k-smooth_compat c1 c2" "l \<le> k"
  using that
  by (auto simp: smooth_compat_def smooth_on_le)


subsection \<open>\<open>C^k\<close>-Manifold\<close>

locale c_manifold = manifold +
  fixes k::enat
  assumes pairwise_compat: "c1 \<in> charts \<Longrightarrow> c2 \<in> charts \<Longrightarrow> k-smooth_compat c1 c2"
begin


subsubsection \<open>Atlas\<close>

definition atlas :: "('a, 'b) chart set" where
  "atlas = {c. domain c \<subseteq> carrier \<and> (\<forall>c' \<in> charts. k-smooth_compat c c')}"

lemma charts_subset_atlas: "charts \<subseteq> atlas"
  by (auto simp: atlas_def pairwise_compat)

lemma in_charts_in_atlas[intro]: "x \<in> charts \<Longrightarrow> x \<in> atlas"
  by (auto simp: atlas_def pairwise_compat)

lemma maximal_atlas:
  "c \<in> atlas"
  if "\<And>c'. c' \<in> atlas \<Longrightarrow> k-smooth_compat c c'"
    "domain c \<subseteq> carrier"
  using that charts_subset_atlas
  by (auto simp: atlas_def)

lemma chart_compose_lemma:
  fixes c1 c2
  defines [simp]: "U \<equiv> domain c1"
  defines [simp]: "V \<equiv> domain c2"
  assumes subsets: "U \<inter> V \<subseteq> carrier"
  assumes "\<And>c. c \<in> charts \<Longrightarrow> k-smooth_compat c1 c"
    "\<And>c. c \<in> charts \<Longrightarrow> k-smooth_compat c2 c"
  shows "k-smooth_on (c1 ` (U \<inter> V)) (c2 \<circ> inv_chart c1)"
proof (rule smooth_on_open_subsetsI)
  fix w' assume "w' \<in> c1 ` (U \<inter> V)"
  then obtain w where w': "w' = c1 w" and "w \<in> U" "w \<in> V" by auto
  then have "w \<in> carrier" using subsets
    by auto
  then obtain c3 where c3: "w \<in> domain c3" "c3 \<in> charts"
    by (rule carrierE)
  then have c13: "k-smooth_compat c1 c3" and c23: "k-smooth_compat c2 c3"
    using assms by auto
  define W where [simp]: "W = domain c3"
  have diff1: "k-smooth_on (c1 ` (U \<inter> W)) (c3 \<circ> inv_chart c1)"
  proof -
    have 1: "open (c1 ` (U \<inter> W))"
      by (rule open_chart_image) auto
    have 2: "w' \<in> c1 ` (U \<inter> W)"
      using \<open>w \<in> U\<close> by (auto simp: c3 w')
    from c13 show ?thesis
      by (auto simp: smooth_compat_def)
  qed

  define y where "y = (c3 \<circ> inv_chart c1) w'"
  have diff2: "k-smooth_on (c3 ` (V \<inter> W)) (c2 \<circ> inv_chart c3)"
  proof -
    have 1: "open (c3 ` (V \<inter> W))"
      by (rule open_chart_image) auto
    have 2: "y \<in> c3 ` (V \<inter> W)"
      using \<open>w \<in> U\<close> \<open>w \<in> V\<close> by (auto simp: y_def c3 w')
    from c23 show ?thesis
      by (auto simp: smooth_compat_def)
  qed
  
  have "k-smooth_on (c1 ` (U \<inter> V \<inter> W)) ((c2 \<circ> inv_chart c3) o (c3 \<circ> inv_chart c1))"
    using diff2 diff1
    by (rule smooth_on_compose2) auto
  then have "k-smooth_on (c1 ` (U \<inter> V \<inter> W)) (c2 \<circ> inv_chart c1)"
    by (rule smooth_on_cong) auto
  moreover have "w' \<in> c1 ` (U \<inter> V \<inter> W)" "open (c1 ` (U \<inter> V \<inter> W))"
    using \<open>w \<in> U\<close> \<open>w \<in> V\<close>
    by (auto simp: w' c3)
  ultimately show "\<exists>T. w' \<in> T \<and> open T \<and> k-smooth_on T (apply_chart c2 \<circ> inv_chart c1)"
    by (intro exI[where x="c1 ` (U \<inter> V \<inter> W)"]) simp
qed

lemma smooth_compat_trans: "k-smooth_compat c1 c2"
  if "\<And>c. c \<in> charts \<Longrightarrow> k-smooth_compat c1 c"
    "\<And>c. c \<in> charts \<Longrightarrow> k-smooth_compat c2 c"
    "domain c1 \<inter> domain c2 \<subseteq> carrier"
  unfolding smooth_compat_def
proof
  show "k-smooth_on (c1 ` (domain c1 \<inter> domain c2)) (c2 \<circ> inv_chart c1)"
    by (auto intro!: that chart_compose_lemma)
  show "k-smooth_on (c2 ` (domain c1 \<inter> domain c2)) (c1 \<circ> inv_chart c2)"
    using that
    by (subst inf_commute) (auto intro!: chart_compose_lemma)
qed

lemma maximal_atlas':
  "c \<in> atlas"
  if "\<And>c'. c' \<in> charts \<Longrightarrow> k-smooth_compat c c'"
    "domain c \<subseteq> carrier"
proof (rule maximal_atlas)
  fix c' assume "c' \<in> atlas"
  show "k-smooth_compat c c'"
    apply (rule smooth_compat_trans)
      apply (rule that(1)) apply assumption
    using atlas_def \<open>c' \<in> atlas\<close> by auto
qed fact

lemma atlas_is_atlas: "k-smooth_compat a1 a2"
  if "a1 \<in> atlas" "a2 \<in> atlas"
  using that atlas_def smooth_compat_trans by blast

lemma domain_atlas_subset_carrier: "c \<in> atlas \<Longrightarrow> domain c \<subseteq> carrier"
  and in_carrier_atlasI[intro, simp]: "c \<in> atlas \<Longrightarrow> x \<in> domain c \<Longrightarrow> x \<in> carrier"
  by (auto simp: atlas_def)

lemma atlasE:
  assumes "x \<in> carrier"
  obtains c where "c \<in> atlas" "x \<in> domain c"
  using carrierE[OF assms] charts_subset_atlas
  by blast

lemma restrict_chart_in_atlas: "restrict_chart S c \<in> atlas" if "c \<in> atlas"
proof (rule maximal_atlas)
  fix c' assume "c' \<in> atlas"
  then have "k-smooth_compat c c'" using \<open>c \<in> atlas\<close> by (auto simp: atlas_is_atlas)
  then show "k-smooth_compat (restrict_chart S c) c'"
    by (rule smooth_compat_restrict_chartI)
next
  have "domain (restrict_chart S c) \<subseteq> domain c"
    by (simp add: domain_restrict_chart_if)
  also have "\<dots> \<subseteq> carrier"
    using that
    by (rule domain_atlas_subset_carrier)
  finally
  show "domain (restrict_chart S c) \<subseteq> carrier"
    by auto
qed

lemma atlas_restrictE:
  assumes "x \<in> carrier" "x \<in> X" "open X"
  obtains c where "c \<in> atlas" "x \<in> domain c" "domain c \<subseteq> X"
proof -
  from assms(1) obtain c where c: "c \<in> atlas" "x \<in> domain c"
    by (blast elim!: carrierE)
  define d where "d = restrict_chart X c"
  from c have "d \<in> atlas" "x \<in> domain d" "domain d \<subseteq> X"
    using assms(2,3)
    by (auto simp: d_def restrict_chart_in_atlas)
  then show ?thesis ..
qed


lemma open_ball_chartE:
  assumes "x \<in> U" "open U" "U \<subseteq> carrier"
  obtains c r where
    "c \<in> atlas"
    "x \<in> domain c" "domain c \<subseteq> U" "codomain c = ball (c x) r" "r > 0"
proof -
  from assms have "x \<in> carrier" by auto
  from carrierE[OF this] obtain c where c: "c \<in> charts" "x \<in> domain c" by auto
  then have "x \<in> domain c \<inter> U" using assms by auto
  then have "open (apply_chart c ` (domain c \<inter> U))" "c x \<in> c ` (domain c \<inter> U)"
    by (auto intro!: assms)
  from openE[OF this]
  obtain e where e: "0 < e" "ball (c x) e \<subseteq> c ` (domain c \<inter> U)"
    by auto
  define C where "C = inv_chart c ` ball (c x) e"
  have "open C"
    using e
    by (auto simp: C_def)
  define c' where "c' = restrict_chart C c"
  from c have "c \<in> atlas" by auto
  then have "c' \<in> atlas" by (auto simp: c'_def restrict_chart_in_atlas)
  moreover
  have "x \<in> C"
    using c \<open>e > 0\<close>
    unfolding C_def
    by (auto intro!: image_eqI[where x="apply_chart c x"])
  have "x \<in> domain c'"
    by (auto simp: c'_def \<open>open C\<close> c \<open>x \<in> C\<close>)
  moreover
  have "C \<subseteq> U"
    using e by (auto simp: C_def)
  then have "domain c' \<subseteq> U"
    by (auto simp: c'_def \<open>open C\<close>)
  moreover have "codomain c' = ball (c' x) e"
    using e \<open>open C\<close>
    by (force simp: c'_def codomain_restrict_chart_if C_def)
  moreover
  have "e > 0"
    by fact
  ultimately show ?thesis ..
qed

lemma smooth_compat_compose_chart:
  fixes c'
  assumes "k-smooth_compat c c'"
  assumes diffeo: "diffeomorphism k UNIV UNIV p p'"
  shows "k-smooth_compat (compose_chart p p' c) c'"
proof -
  note dD[simp] = diffeomorphismD[OF diffeo]
  note homeo[simp] = diffeomorphism_imp_homeomorphism[OF diffeo]
  from assms(1) have c: "k-smooth_on (apply_chart c ` (domain c \<inter> domain c')) (apply_chart c' \<circ> inv_chart c)"
    and c': "k-smooth_on (apply_chart c' ` (domain c \<inter> domain c')) (apply_chart c \<circ> inv_chart c')"
    by (auto simp: smooth_compat_def)
  from homeo have *: "open (p ` apply_chart c ` (domain c \<inter> domain c'))"
    by (rule homeomorphism_UNIV_imp_open_map) auto
  have "k-smooth_on ((p \<circ> apply_chart c) ` (domain c \<inter> domain c')) (apply_chart c' \<circ> inv_chart c \<circ> p')"
    apply (rule smooth_on_compose2) prefer 2
         apply (rule dD)
        apply (rule c)
       apply (auto simp add: assms image_comp [symmetric] * cong del: image_cong_simp)
    done
  moreover
  have "k-smooth_on (apply_chart c' ` (domain c \<inter> domain c')) (p \<circ> (apply_chart c \<circ> inv_chart c'))"
    apply (rule smooth_on_compose2)
         apply (rule dD)
        apply fact
    by (auto simp: assms image_comp[symmetric])
  ultimately show ?thesis
    unfolding smooth_compat_def
    by (auto intro!: simp: o_assoc)
qed

lemma compose_chart_in_atlas:
  assumes "c \<in> atlas"
  assumes diffeo: "diffeomorphism k UNIV UNIV p p'"
  shows "compose_chart p p' c \<in> atlas"
proof (rule maximal_atlas)
  note [simp] = diffeomorphism_imp_homeomorphism[OF diffeo]
  show "domain (compose_chart p p' c) \<subseteq> carrier"
    using assms
    by auto
  fix c' assume "c' \<in> atlas"
  with \<open>c \<in> atlas\<close> have "k-smooth_compat c c'"
    by (rule atlas_is_atlas)
  then show "k-smooth_compat (compose_chart p p' c) c'"
    using diffeo
    by (rule smooth_compat_compose_chart)
qed

lemma open_centered_ball_chartE:
  assumes "x \<in> U" "open U" "U \<subseteq> carrier" "e > 0"
  obtains c where
    "c \<in> atlas" "x \<in> domain c" "c x = x0" "domain c \<subseteq> U" "codomain c = ball x0 e"
proof -
  from open_ball_chartE[OF assms(1-3)] obtain c r where c:
    "c \<in> atlas"
    "x \<in> domain c" "domain c \<subseteq> U" "codomain c = ball (c x) r"
    and r: "r > 0"
    by auto
  have nz: "e / r \<noteq> 0" using \<open>e > 0\<close> \<open>r > 0\<close> by auto
  have 1: "diffeomorphism k UNIV UNIV (\<lambda>y. y + (- c x)) (\<lambda>y. y - (- c x))"
    using diffeomorphism_add[of k "(- c x)"] by auto
  have 2: "diffeomorphism k UNIV UNIV (\<lambda>y. (e / r) *\<^sub>R y) (\<lambda>y. y /\<^sub>R (e / r))"
    using diffeomorphism_scaleR[of "e / r" k] \<open>e > 0\<close> \<open>r > 0\<close> by auto
  have 3: "diffeomorphism k UNIV UNIV (\<lambda>y. y + x0) (\<lambda>y. y - x0)"
    using diffeomorphism_add[of k x0] by auto
  define t where "t = (\<lambda>y. (e / r) *\<^sub>R (y + - c x) + x0)"
  define t' where "t' = (\<lambda>y. (y - x0) /\<^sub>R (e / r) + c x)"
  from diffeomorphism_compose[OF diffeomorphism_compose[OF 1 2] 3, unfolded o_def]
  have diffeo: "diffeomorphism k UNIV UNIV t t'"
    by (auto simp: t_def t'_def o_def)
  from compose_chart_in_atlas[OF \<open>c \<in> atlas\<close> this]
  have "compose_chart t t' c \<in> atlas" .
  moreover
  note [simp] = diffeomorphism_imp_homeomorphism[OF diffeo]
  have "x \<in> domain (compose_chart t t' c)" by (auto simp: \<open>x \<in> domain c\<close>)
  moreover
  have "t (c x) = x0"
    by (auto simp: t_def)
  then have "compose_chart t t' c x = x0"
    by simp
  moreover have "domain (compose_chart t t' c) \<subseteq> U"
    using \<open>domain c \<subseteq> U\<close>
    by auto
  moreover
  have "t ` codomain c = ball x0 e"
  proof -
    have "t ` codomain c = (+) x0 ` (*\<^sub>R) (e / r) ` (\<lambda>y. - apply_chart c x + y) ` ball (c x) r"
      by (auto simp add: c t_def image_image)
    also have "\<dots> = ball x0 e"
      using \<open>e > 0\<close> \<open>r > 0\<close>
      unfolding image_add_ball image_scaleR_ball[OF nz]
      by simp
    finally show ?thesis .
  qed
  then have "codomain (compose_chart t t' c) = ball x0 e"
    by auto
  ultimately show ?thesis ..
qed

end

subsubsection \<open>Submanifold\<close>

definition (in manifold) "charts_submanifold S = (restrict_chart S ` charts)"

locale c_manifold' = c_manifold

locale submanifold = c_manifold' charts k \<comment>\<open>breaks infinite loop for sublocale sub\<close>
  for charts::"('a::{t2_space,second_countable_topology}, 'b::euclidean_space) chart set" and k +
  fixes S::"'a set"
  assumes open_submanifold: "open S"
begin

lemma charts_submanifold: "c_manifold (charts_submanifold S) k" 
  by unfold_locales
    (auto simp: charts_submanifold_def atlas_is_atlas in_charts_in_atlas restrict_chart_in_atlas)

sublocale sub: c_manifold "(charts_submanifold S)" k
  by (rule charts_submanifold)

lemma carrier_submanifold[simp]: "sub.carrier = S \<inter> carrier"
  using open_submanifold
  by (auto simp: manifold.carrier_def charts_submanifold_def domain_restrict_chart_if split: if_splits)

lemma restrict_chart_carrier[simp]:
  "restrict_chart carrier x = x"
  if "x \<in> charts"
  using that
  by (auto intro!: chart_eqI)

lemma charts_submanifold_carrier[simp]: "charts_submanifold carrier = charts"
  by (force simp: charts_submanifold_def)

lemma charts_submanifold_Int_carrier:
  "charts_submanifold (S \<inter> carrier) = charts_submanifold S"
  using open_submanifold
  by (force simp: charts_submanifold_def restrict_chart_restrict_chart[symmetric])

lemma submanifold_atlasE:
  assumes "c \<in> sub.atlas"
  shows "c \<in> atlas"
proof (rule maximal_atlas')
  have dc: "domain c \<subseteq> S \<inter> carrier"
    using assms sub.domain_atlas_subset_carrier
    by auto
  then show "domain c \<subseteq> carrier"
    using open_submanifold by auto
  fix c' assume "c' \<in> charts"
  then have "restrict_chart S c' \<in> (charts_submanifold S)"
    by (auto simp: charts_submanifold_def)
  then have "restrict_chart S c' \<in> sub.atlas"
    by auto
  have "k-smooth_compat c (restrict_chart S c')"
    by (rule sub.atlas_is_atlas) fact+
  show "k-smooth_compat c c'"
    apply (rule smooth_compat_restrict_chartD[where U=S])
    subgoal using dc by auto
    subgoal by (rule open_submanifold)
    subgoal by fact
    done
qed

lemma submanifold_atlasI:
  "restrict_chart S c \<in> sub.atlas"
  if "c \<in> atlas"
proof (rule sub.maximal_atlas')
  fix c' assume "c' \<in> (charts_submanifold S)"
  then obtain c'' where c'': "c' = restrict_chart S c''" "c'' \<in> charts"
    unfolding charts_submanifold_def by auto
  show "k-smooth_compat (restrict_chart S c) c'"
    unfolding c''
    apply (rule smooth_compat_restrict_chartI)
    apply (rule smooth_compat_restrict_chartI2)
    apply (rule atlas_is_atlas)
     apply fact using \<open>c'' \<in> charts\<close> by auto
next
  show "domain (restrict_chart S c) \<subseteq> sub.carrier"
    using domain_atlas_subset_carrier[OF that]
    by (auto simp: open_submanifold )
qed

end



lemma (in c_manifold) restrict_chart_carrier[simp]:
  "restrict_chart carrier x = x"
  if "x \<in> charts"
  using that
  by (auto intro!: chart_eqI)

lemma (in c_manifold) charts_submanifold_carrier[simp]: "charts_submanifold carrier = charts"
  by (force simp: charts_submanifold_def)


subsection \<open>Differentiable maps\<close>

locale c_manifolds =
  src: c_manifold charts1 k + 
  dest: c_manifold charts2 k for k charts1 charts2

locale diff = c_manifolds k charts1 charts2
  for k
    and charts1 :: "('a::{t2_space,second_countable_topology}, 'e::euclidean_space) chart set"
    and charts2 :: "('b::{t2_space,second_countable_topology}, 'f::euclidean_space) chart set"
    +
  fixes f :: "('a \<Rightarrow> 'b)"
  assumes exists_smooth_on: "x \<in> src.carrier \<Longrightarrow>
    \<exists>c1\<in>src.atlas. \<exists>c2\<in>dest.atlas.
      x \<in> domain c1 \<and>
      f ` domain c1 \<subseteq> domain c2 \<and>
      k-smooth_on (codomain c1) (c2 \<circ> f \<circ> inv_chart c1)"
begin

lemma defined: "f ` src.carrier \<subseteq> dest.carrier"
  using exists_smooth_on
  by auto

end

context c_manifolds begin

lemma diff_iff: "diff k charts1 charts2 f \<longleftrightarrow>
  (\<forall>x\<in>src.carrier. \<exists>c1\<in>src.atlas. \<exists>c2\<in>dest.atlas.
    x \<in> domain c1 \<and>
    f ` domain c1 \<subseteq> domain c2 \<and>
    k-smooth_on (codomain c1) (apply_chart c2 \<circ> f \<circ> inv_chart c1))"
  (is "?l \<longleftrightarrow> (\<forall>x\<in>_. ?r x)")
proof safe
  assume ?l
  interpret diff k charts1 charts2 f by fact
  show "x \<in> src.carrier \<Longrightarrow> ?r x" for x
    by (rule exists_smooth_on)
next
  assume "\<forall>x\<in>src.carrier. ?r x"
  then show ?l
    by unfold_locales auto
qed

end

context diff begin

lemma diffE:
  assumes "x \<in> src.carrier"
  obtains c1::"('a, 'e) chart"
    and c2::"('b, 'f) chart"
  where
    "c1 \<in> src.atlas" "c2 \<in> dest.atlas" "x \<in> domain c1" "f ` domain c1 \<subseteq> domain c2"
    "k-smooth_on (codomain c1) (apply_chart c2 \<circ> f \<circ> inv_chart c1)"
  using exists_smooth_on assms by force

lemma continuous_at: "continuous (at x within T) f" if "x \<in> src.carrier"
proof -
  from that obtain c1 c2 where "c1 \<in> src.atlas" "c2 \<in> dest.atlas" "x \<in> domain c1"
    "f ` domain c1 \<subseteq> domain c2"
    "k-smooth_on (codomain c1) (apply_chart c2 \<circ> f \<circ> inv_chart c1)"
    by (rule diffE)
  from smooth_on_imp_continuous_on[OF this(5)]
  have "continuous_on (codomain c1) (apply_chart c2 \<circ> f \<circ> inv_chart c1)" .
  then have "continuous_on (c1 ` domain c1) (f \<circ> inv_chart c1)"
    using \<open>f ` domain c1 \<subseteq> domain c2\<close> continuous_on_chart_inv by (fastforce simp: image_domain_eq)
  then have "continuous_on (domain c1) f"
    by (rule continuous_on_chart_inv') simp
  then have "isCont f x"
    using \<open>x \<in> domain c1\<close>
    unfolding continuous_on_eq_continuous_at[OF open_domain] 
    by auto
  then show "continuous (at x within T) f"
    by (simp add: \<open>isCont f x\<close> continuous_at_imp_continuous_within)
qed

lemma continuous_on: "continuous_on src.carrier f"
  unfolding continuous_on_eq_continuous_within
  by (auto intro: continuous_at)

lemmas continuous_on_intro[continuous_intros] = continuous_on_compose2[OF continuous_on _]

lemmas continuous_within[continuous_intros] = continuous_within_compose3[OF continuous_at]

lemmas tendsto[tendsto_intros] = isCont_tendsto_compose[OF continuous_at]

lemma diff_chartsD:
  assumes "d1 \<in> src.atlas" "d2 \<in> dest.atlas"
  shows "k-smooth_on (codomain d1 \<inter> inv_chart d1 -` (src.carrier \<inter> f -` domain d2))
      (apply_chart d2 \<circ> f \<circ> inv_chart d1)"
proof (rule smooth_on_open_subsetsI)
  fix y assume "y \<in> codomain d1 \<inter> inv_chart d1 -` (src.carrier \<inter> f -` domain d2)"
  then have y: "f (inv_chart d1 y) \<in> domain d2" "y \<in> codomain d1"
    by auto
  then obtain x where x: "d1 x = y" "x \<in> domain d1"
    by force
  then have "x \<in> src.carrier" using assms by force
  obtain c1 c2 where "c1 \<in> src.atlas" "c2 \<in> dest.atlas"
    and fc1: "f ` domain c1 \<subseteq> domain c2"
    and xc1: "x \<in> domain c1"
    and d: "k-smooth_on (codomain c1) (apply_chart c2 \<circ> f \<circ> inv_chart c1)"
    using diffE[OF \<open>x \<in> src.carrier\<close>]
    by metis
  have [simp]: "x \<in> domain c1 \<Longrightarrow> f x \<in> domain c2" for x using fc1 by auto
  have r1: "k-smooth_on (d1 ` (domain d1 \<inter> domain c1)) (c1 \<circ> inv_chart d1)"
    using src.atlas_is_atlas[OF \<open>d1 \<in> src.atlas\<close> \<open>c1 \<in> src.atlas\<close>, THEN smooth_compat_D1] .
  have r2: "k-smooth_on (c2 ` (domain d2 \<inter> domain c2)) (d2 \<circ> inv_chart c2)"
    using dest.atlas_is_atlas[OF \<open>d2 \<in> dest.atlas\<close> \<open>c2 \<in> dest.atlas\<close>, THEN smooth_compat_D2] .
  define T where "T = (d1 ` (domain d1 \<inter> domain c1) \<inter> inv_chart d1 -` (src.carrier \<inter> (f -` domain d2)))"
  have "open T"
    unfolding T_def
    by (rule open_continuous_vimage')
      (auto intro!: continuous_intros open_continuous_vimage' src.open_carrier)
  have T_subset: "T \<subseteq> apply_chart d1 ` (domain d1 \<inter> domain c1)"
    by (auto simp: T_def)
  have opens: "open (c1 ` inv_chart d1 ` T)" "open (c2 ` (domain d2 \<inter> domain c2))"
    using fc1 \<open>open T\<close>
    by (force simp: T_def)+
  have "k-smooth_on ((apply_chart c1 \<circ> inv_chart d1) ` T) (d2 \<circ> inv_chart c2 \<circ> (c2 \<circ> f \<circ> inv_chart c1))"
    using r2 d opens
    unfolding image_comp[symmetric]
    by (rule smooth_on_compose2) (auto simp: T_def)
  from this r1 \<open>open T\<close> opens(1) have "k-smooth_on T
      ((d2 \<circ> inv_chart c2) \<circ> (c2 \<circ> f \<circ> inv_chart c1) \<circ> (c1 \<circ> inv_chart d1))"
    unfolding image_comp[symmetric]
    by (rule smooth_on_compose2) (force simp: T_def)+
  then have "k-smooth_on T (d2 \<circ> f \<circ> inv_chart d1)"
    using \<open>open T\<close>
    by (rule smooth_on_cong) (auto simp: T_def)
  moreover have "y \<in> T" 
    using x xc1 fc1 y \<open>c1 \<in> src.atlas\<close>
    by (auto simp: T_def)
  ultimately show "\<exists>T. y \<in> T \<and> open T \<and> k-smooth_on T (apply_chart d2 \<circ> f \<circ> inv_chart d1)"
    using \<open>open T\<close>
    by metis
qed

lemma diff_between_chartsE:
  assumes "d1 \<in> src.atlas" "d2 \<in> dest.atlas"
  assumes "y \<in> domain d1" "y \<in> src.carrier" "f y \<in> domain d2"
  obtains X where
    "k-smooth_on X (apply_chart d2 \<circ> f \<circ> inv_chart d1)"
    "d1 y \<in> X"
    "open X"
    "X = codomain d1 \<inter> inv_chart d1 -` (src.carrier \<inter> f -` domain d2)"
proof -
  define X where "X = (codomain d1 \<inter> inv_chart d1 -` (src.carrier \<inter> f -` domain d2))"
  from diff_chartsD[OF assms(1,2)]
  have "k-smooth_on X (apply_chart d2 \<circ> f \<circ> inv_chart d1)"
    by (simp add: X_def)
  moreover have "d1 y \<in> X"
    using assms(3-5)
    by (auto simp: X_def)
  moreover have "open X"
    unfolding X_def
    by (auto intro!: open_continuous_vimage' continuous_intros src.open_carrier)
  moreover note X_def
  ultimately show ?thesis ..
qed

end

lemma diff_compose:
  "diff k M1 M3 (g \<circ> f)"
  if "diff k M1 M2 f" "diff k M2 M3 g"
proof -
  interpret f: diff k M1 M2 f by fact
  interpret g: diff k M2 M3 g by fact
  interpret fg: c_manifolds k M1 M3 by unfold_locales
  show ?thesis
    unfolding fg.diff_iff
  proof safe
    fix x assume "x \<in> f.src.carrier"
    then obtain c1 c2 where c1: "c1 \<in> f.src.atlas"
      and c2: "c2 \<in> f.dest.atlas"
      and fc1: "f ` domain c1 \<subseteq> domain c2"
      and x: "x \<in> domain c1"
      and df: "k-smooth_on (codomain c1) (apply_chart c2 \<circ> f \<circ> inv_chart c1)"
      using f.diffE by metis

    have "f x \<in> f.dest.carrier" using f.defined \<open>x \<in> f.src.carrier\<close> by auto
    then obtain c2' c3 where c2': "c2' \<in> f.dest.atlas"
      and c3: "c3 \<in> g.dest.atlas"
      and gc2': "g ` domain c2' \<subseteq> domain c3"
      and fx: "f x \<in> domain c2'"
      and dg: "k-smooth_on (codomain c2') (apply_chart c3 \<circ> g \<circ> inv_chart c2')"
      using g.diffE by metis

    define D where "D = (g \<circ> f) -` domain c3 \<inter> domain c1"
    have "open D"
      using f.defined c1
      by (auto intro!: continuous_intros open_continuous_vimage simp: D_def)
    
    have "x \<in> D"
      using fc1 fx gc2'
      by (auto simp: D_def \<open>x \<in> domain c1\<close>)

    define d1 where "d1 = restrict_chart D c1"

    have "d1 \<in> f.src.atlas"
      by (auto simp: d1_def intro!: f.src.restrict_chart_in_atlas c1)
    moreover have "c3 \<in> g.dest.atlas" by fact
    moreover have "x \<in> domain d1" by (auto simp: d1_def \<open>open D\<close> \<open>x \<in> D\<close> x)
    moreover have sub_c3: "(g \<circ> f) ` domain d1 \<subseteq> domain c3"
      using \<open>open D\<close> by (auto simp: d1_def D_def)
    moreover have "k-smooth_on (codomain d1) (c3 \<circ> (g \<circ> f) \<circ> inv_chart d1)"
    proof (rule smooth_on_open_subsetsI)
      fix y assume y: "y \<in> codomain d1"
      then obtain iy where y_def: "y = d1 iy" and iy: "iy \<in> domain d1" by force
      note iy
      also note f.src.domain_atlas_subset_carrier[OF \<open>d1 \<in> f.src.atlas\<close>]
      finally have iS: "iy \<in> f.src.carrier" .
      then have "f iy \<in> f.dest.carrier"
        using f.defined by (auto simp: d1_def)
      with f.dest.atlasE obtain d2 where d2: "d2 \<in> f.dest.atlas"
        and fy: "f iy \<in> domain d2"
        by blast
      from f.diff_between_chartsE[OF \<open>d1 \<in> f.src.atlas\<close> \<open>d2 \<in> f.dest.atlas\<close> iy iS fy]
      obtain T where 1: "k-smooth_on T (apply_chart d2 \<circ> f \<circ> inv_chart d1)"
        and T: "d1 iy \<in> T" "open T"
        and T_def: "T = codomain d1 \<inter> inv_chart d1 -` (f.src.carrier \<inter> f -` domain d2)"
        by auto

      have gf: "g (f (iy)) \<in> domain c3" using sub_c3 iy by auto
      from iS f.defined have "f (iy) \<in> f.dest.carrier" by auto
      from g.diff_between_chartsE[OF \<open>d2 \<in> f.dest.atlas\<close> \<open>c3 \<in> g.dest.atlas\<close> fy this gf]
      obtain X where 2: "k-smooth_on X (apply_chart c3 \<circ> g \<circ> inv_chart d2)"
        and X: "apply_chart d2 (f iy) \<in> X" "open X"
        and X_def: "X = codomain d2 \<inter> inv_chart d2 -` (f.dest.carrier \<inter> g -` domain c3)"
        by auto
      have "y \<in> T" using T by (simp add: y_def)
      moreover
      note \<open>open T\<close>
      moreover
      have "k-smooth_on T (apply_chart c3 \<circ> g \<circ> inv_chart d2 \<circ> (apply_chart d2 \<circ> f \<circ> inv_chart d1))"
        using 2 1 \<open>open T\<close> \<open>open X\<close>
        by (rule smooth_on_compose) (use sub_c3 f.defined in \<open>force simp: T_def X_def\<close>)
      then have "k-smooth_on T (apply_chart c3 \<circ> (g \<circ> f) \<circ> inv_chart d1)"
        using \<open>open T\<close>
        by (rule smooth_on_cong) (auto simp: T_def)
      ultimately show "\<exists>T. y \<in> T \<and> open T \<and> k-smooth_on T (apply_chart c3 \<circ> (g \<circ> f) \<circ> inv_chart d1)"
        by metis
    qed
    ultimately show "\<exists>c1\<in>f.src.atlas.
            \<exists>c2\<in>g.dest.atlas.
               x \<in> domain c1 \<and>
               (g \<circ> f) ` domain c1 \<subseteq> domain c2 \<and> k-smooth_on (codomain c1) (apply_chart c2 \<circ> (g \<circ> f) \<circ> inv_chart c1)"
      by blast
  qed
qed

context diff begin

lemma diff_submanifold: "diff k (src.charts_submanifold S) charts2 f"
  if "open S"
proof -
  interpret submanifold charts1 k S
    by unfold_locales (auto intro!: that)
  show ?thesis
    unfolding that src.charts_submanifold_def[symmetric]
  proof unfold_locales
    fix x assume "x \<in> sub.carrier"
    then have "x \<in> src.carrier" "x \<in> S" using that
      by auto
    from diffE[OF \<open>x \<in> src.carrier\<close>] obtain c1 c2 where c1c2:
      "c1 \<in> src.atlas" "c2 \<in> dest.atlas" "x \<in> domain c1"
      "f ` domain c1 \<subseteq> domain c2" "k-smooth_on (codomain c1) (apply_chart c2 \<circ> f \<circ> inv_chart c1)"
      by auto
    have rc1: "restrict_chart S c1 \<in> sub.atlas"
      using c1c2(1) by (rule submanifold_atlasI)
    show "\<exists>c1\<in>sub.atlas. \<exists>c2\<in>dest.atlas. x \<in> domain c1 \<and> f ` domain c1 \<subseteq> domain c2 \<and>
      k-smooth_on (codomain c1) (c2 \<circ> f \<circ> inv_chart c1)"
      using rc1
      apply (rule rev_bexI)
      using c1c2(2)
      apply (rule rev_bexI)
      using c1c2 \<open>x \<in> S\<close> \<open>open S\<close>
      by (auto simp: smooth_on_subset)
  qed
qed

lemma diff_submanifold2: "diff k charts1 (dest.charts_submanifold S) f"
  if "open S" "f ` src.carrier \<subseteq> S"
proof -
  interpret submanifold charts2 k S
    by unfold_locales (auto intro!: that)
  show ?thesis
    unfolding that src.charts_submanifold_def[symmetric]
  proof unfold_locales
    fix x assume "x \<in> src.carrier"
    from diffE[OF this]
    obtain c1 c2 where c1c2:
      "c1 \<in> src.atlas" "c2 \<in> dest.atlas" "x \<in> domain c1"
      "f ` domain c1 \<subseteq> domain c2" "k-smooth_on (codomain c1) (apply_chart c2 \<circ> f \<circ> inv_chart c1)"
      by auto
    have r: "restrict_chart S c2 \<in> sub.atlas"
      using c1c2(2) by (rule submanifold_atlasI)
    show "\<exists>c1\<in>src.atlas. \<exists>c2\<in>sub.atlas. x \<in> domain c1 \<and> f ` domain c1 \<subseteq> domain c2 \<and>
      k-smooth_on (codomain c1) (c2 \<circ> f \<circ> inv_chart c1)"
      using c1c2(1)
      apply (rule rev_bexI)
      using r
      apply (rule rev_bexI)
      using c1c2 \<open>open S\<close> that(2)
      by (auto simp: smooth_on_subset)
  qed
qed

end

context c_manifolds begin

lemma diff_localI: "diff k charts1 charts2 f"
  if "\<And>x. x \<in> src.carrier \<Longrightarrow> diff k (src.charts_submanifold (U x)) charts2 f"
    "\<And>x. x \<in> src.carrier \<Longrightarrow> open (U x)"
    "\<And>x. x \<in> src.carrier \<Longrightarrow> x \<in> (U x)"
proof unfold_locales
  fix x assume x: "x \<in> src.carrier"
  have open_U[simp]: "open (U x)" by (rule that) fact
  have in_U[simp]: "x \<in> U x" by (rule that) fact
  interpret submanifold charts1 k "U x"
    using that x
    by unfold_locales auto
  from x interpret l: diff k "src.charts_submanifold (U x)" charts2 f
    by (rule that)
  have "x \<in> sub.carrier" using x
    by auto
  from l.diffE[OF this] obtain c1 c2 where c1c2: "c1 \<in> sub.atlas"
    "c2 \<in> dest.atlas" "x \<in> domain c1" "f ` domain c1 \<subseteq> domain c2"
    "k-smooth_on (codomain c1) (apply_chart c2 \<circ> f \<circ> inv_chart c1)"
    by auto
  have "c1 \<in> src.atlas"
    by (rule submanifold_atlasE[OF c1c2(1)])
  show "\<exists>c1\<in>src.atlas. \<exists>c2\<in>dest.atlas. x \<in> domain c1 \<and> f ` domain c1 \<subseteq> domain c2 \<and>
    k-smooth_on (codomain c1) (apply_chart c2 \<circ> f \<circ> inv_chart c1)"
    by (intro bexI[where x=c1] bexI[where x=c2] conjI \<open>c1 \<in> src.atlas\<close> \<open>c2 \<in> dest.atlas\<close> c1c2)
qed

lemma diff_open_coverI: "diff k charts1 charts2 f"
  if diff: "\<And>u. u \<in> U \<Longrightarrow> diff k (src.charts_submanifold u) charts2 f"
    and op: "\<And>u. u \<in> U \<Longrightarrow> open u"
    and cover: "src.carrier \<subseteq> \<Union>U"
proof -
  obtain V where V: "\<forall>x\<in>src.carrier. V x \<in> U \<and> x \<in> V x"
    apply (atomize_elim, rule bchoice)
    using cover
    by blast
  have "diff k (src.charts_submanifold (V x)) charts2 f"
    "open (V x)"
    "x \<in> V x"
    if "x \<in> src.carrier" for x
    using that diff op V
    by auto
  then show ?thesis
    by (rule diff_localI)
qed

lemma diff_open_Un: "diff k charts1 charts2 f"
  if "diff k (src.charts_submanifold U) charts2 f"
    "diff k (src.charts_submanifold V) charts2 f"
    and "open U" "open V" "src.carrier \<subseteq> U \<union> V"
  using diff_open_coverI[of "{U, V}" f] that
  by auto

end

context c_manifold begin

sublocale self: c_manifolds k charts charts
  by unfold_locales

lemma diff_id: "diff k charts charts (\<lambda>x. x)"
  by (force simp: self.diff_iff elim!: atlasE intro: smooth_on_cong)

lemma c_manifold_order_le: "c_manifold charts l" if "l \<le> k"
  by unfold_locales (use pairwise_compat smooth_compat_le[OF _ \<open>l \<le> k\<close>] in blast)

lemma in_atlas_order_le: "c \<in> c_manifold.atlas charts l" if "l \<le> k" "c \<in> atlas"
proof -
  interpret l: c_manifold charts l
    using \<open>l \<le> k\<close>
    by (rule c_manifold_order_le)
  show ?thesis
    using that
    by (auto simp: l.atlas_def atlas_def smooth_compat_le[OF _ \<open>l \<le> k\<close>])
qed

end

context c_manifolds begin

lemma c_manifolds_order_le: "c_manifolds l charts1 charts2" if "l \<le> k"
  by unfold_locales
    (use src.pairwise_compat dest.pairwise_compat smooth_compat_le[OF _ that] in blast)+

end

context diff begin

lemma diff_order_le: "diff l charts1 charts2 f" if "l \<le> k"
proof -
  interpret l: c_manifolds l charts1 charts2
    by (rule c_manifolds_order_le) fact
  show "diff l charts1 charts2 f"
    using diff_axioms
    unfolding l.diff_iff diff_iff
    by (auto dest!: smooth_on_le[OF _ that] src.in_atlas_order_le[OF that]
        dest.in_atlas_order_le[OF that] dest!: bspec)
qed

end


subsection \<open>Differentiable functions\<close>

lift_definition chart_eucl::"('a::euclidean_space, 'a) chart" is
  "(UNIV, UNIV, \<lambda>x. x, \<lambda>x. x)"
  by (auto simp: homeomorphism_def)

abbreviation "charts_eucl \<equiv> {chart_eucl}"

lemma chart_eucl_simps[simp]:
  "domain chart_eucl = UNIV"
  "codomain chart_eucl = UNIV"
  "apply_chart chart_eucl = (\<lambda>x. x)"
  "inv_chart chart_eucl = (\<lambda>x. x)"
  by (transfer, simp)+

locale diff_fun = diff k charts charts_eucl f
  for k charts and f::"'a::{t2_space,second_countable_topology} \<Rightarrow> 'b::euclidean_space"

lemma diff_fun_compose:
  "diff_fun k M1 (g \<circ> f)"
  if "diff k M1 M2 f" "diff_fun k M2 g"
  unfolding diff_fun_def
  by (rule diff_compose[OF that[unfolded diff_fun_def]])

lemma c1_manifold_atlas_eucl: "c_manifold charts_eucl k"
  by unfold_locales (auto simp: smooth_compat_refl)

interpretation manifold_eucl: c_manifold "charts_eucl" k
  by (rule c1_manifold_atlas_eucl)

lemma chart_eucl_in_atlas[intro,simp]: "chart_eucl \<in> manifold_eucl.atlas k"
  using manifold_eucl.charts_subset_atlas
  by auto

lemma apply_chart_smooth_on:
  "k-smooth_on (domain c) c" if "c \<in> manifold_eucl.atlas k"
proof -
  have "k-smooth_compat c chart_eucl"
    using that
    by (auto intro!: manifold_eucl.atlas_is_atlas)
  from smooth_compat_D2[OF this]
  show ?thesis
    by (auto simp: o_def)
qed

lemma inv_chart_smooth_on: "k-smooth_on (codomain c) (inv_chart c)" if "c \<in> manifold_eucl.atlas k"
proof -
  have "k-smooth_compat c chart_eucl"
    using that
    by (auto intro!: manifold_eucl.atlas_is_atlas)
  from smooth_compat_D1[OF this]
  show ?thesis
    by (auto simp: o_def image_domain_eq)
qed

lemma smooth_on_chart_inv:
  fixes c::"('a::euclidean_space, 'a) chart"
  assumes "k-smooth_on X (apply_chart c \<circ> f)"
  assumes "continuous_on X f"
  assumes "c \<in> manifold_eucl.atlas k" "open X" "f ` X \<subseteq> domain c"
  shows "k-smooth_on X f"
proof -
  have "k-smooth_on X (inv_chart c \<circ> (apply_chart c \<circ> f))"
    using assms
    by (auto intro!: smooth_on_compose inv_chart_smooth_on)
  with assms show ?thesis
    by (force intro!: open_continuous_vimage intro: smooth_on_cong)
qed

lemma smooth_on_chart_inv2:
  fixes c::"('a::euclidean_space, 'a) chart"
  assumes "k-smooth_on (c ` X) (f o inv_chart c)"
  assumes "c \<in> manifold_eucl.atlas k" "open X" "X \<subseteq> domain c"
  shows "k-smooth_on X f"
proof -
  have "k-smooth_on X ((f o inv_chart c) \<circ> apply_chart c)"
    using assms(1) apply_chart_smooth_on
    by (rule smooth_on_compose2) (auto simp: assms)
  with assms show ?thesis
    by (force intro!: open_continuous_vimage intro: smooth_on_cong)
qed

context diff_fun begin

lemma diff_fun_order_le: "diff_fun l charts f" if "l \<le> k"
  using diff_order_le[OF that]
  by (simp add: diff_fun_def)

end


subsection \<open>Diffeormorphism\<close>

locale diffeomorphism = diff k charts1 charts2 f + inv: diff k charts2 charts1 f'
  for k charts1 charts2 f f' +
  assumes f_inv[simp]:  "\<And>x. x \<in> src.carrier \<Longrightarrow> f' (f x) = x"
      and f'_inv[simp]: "\<And>y. y \<in> dest.carrier \<Longrightarrow> f (f' y) = y"

context c_manifold begin

sublocale manifold_eucl: c_manifolds k charts "{chart_eucl}"
  rewrites "diff k charts {chart_eucl} = diff_fun k charts"
  by unfold_locales (simp add: diff_fun_def[abs_def])

lemma diff_funI:
  "diff_fun k charts f"
  if "(\<And>x. x\<in>carrier \<Longrightarrow> \<exists>c1\<in>atlas. x \<in> domain c1 \<and> (k-smooth_on (codomain c1) (f \<circ> inv_chart c1)))"
  unfolding manifold_eucl.diff_iff
  by (auto dest!: that intro!: bexI[where x=chart_eucl] simp: o_def)

end

lemma (in diff) diff_cong: "diff k charts1 charts2 g" if "\<And>x. x \<in> src.carrier \<Longrightarrow> f x = g x"
  unfolding diff_iff
proof (rule ballI)
  fix x assume "x \<in> src.carrier"
  from diff_axioms[unfolded diff_iff, rule_format, OF this]
  obtain c1::"('a, 'e) chart" and c2::"('b, 'f) chart" where
    "c1\<in>src.atlas" "c2 \<in> dest.atlas"
     "x \<in> domain c1" "f ` domain c1 \<subseteq> domain c2" "k-smooth_on (codomain c1) (apply_chart c2 \<circ> f \<circ> inv_chart c1)"
    by auto
  then show "\<exists>c1\<in>src.atlas. \<exists>c2\<in>dest.atlas.
      x \<in> domain c1 \<and> g ` domain c1 \<subseteq> domain c2 \<and> k-smooth_on (codomain c1) (apply_chart c2 \<circ> g \<circ> inv_chart c1)"
    using that
    by (intro bexI[where x=c1] bexI[where x=c2]) (auto simp: intro: smooth_on_cong)
qed


context diff_fun begin

lemma diff_fun_cong: "diff_fun k charts g" if "\<And>x. x \<in> src.carrier \<Longrightarrow> f x = g x"
  using diff_cong[OF that]
  by (auto simp: diff_fun_def)

lemma diff_funD:
  "\<exists>c1\<in>src.atlas. x \<in> domain c1 \<and> (k-smooth_on (codomain c1) (f \<circ> inv_chart c1))"
  if x: "x \<in> src.carrier"
proof -
  from diff_fun_axioms[unfolded src.manifold_eucl.diff_iff, rule_format, OF x]
  obtain c1 c2 where a: "c1 \<in> src.atlas" "c2 \<in> manifold_eucl.atlas k" "x \<in> domain c1" "f ` domain c1 \<subseteq> domain c2"
    and s: "k-smooth_on (codomain c1) (apply_chart c2 \<circ> (f \<circ> inv_chart c1))"
    by (auto simp: o_assoc)
  from smooth_on_chart_inv[OF s] a
  show ?thesis
    by (force intro!: bexI[where x=c1] a continuous_intros)
qed

lemma diff_funE:
  assumes "x \<in> src.carrier"
  obtains c1 where
    "c1\<in>src.atlas" "x \<in> domain c1" "k-smooth_on (codomain c1) (f \<circ> inv_chart c1)"
  using diff_funD[OF assms]
  by blast

lemma diff_fun_between_chartsD:
  assumes "c \<in> src.atlas" "x \<in> domain c"
  shows "k-smooth_on (codomain c) (f \<circ> inv_chart c)"
proof -
  have "x \<in> src.carrier" "f x \<in> domain chart_eucl" using assms by auto
  from diff_between_chartsE[OF assms(1) chart_eucl_in_atlas assms(2) this]
  obtain X where s: "k-smooth_on X (f \<circ> inv_chart c)"
    and X_def: "X = codomain c \<inter> inv_chart c -` (src.carrier \<inter> f -` UNIV)"
    by (auto simp: o_def)
  then have X_def: "X = codomain c" using assms
    by (auto simp: X_def)
  with s show ?thesis by auto
qed

lemma diff_fun_submanifold: "diff_fun k (src.charts_submanifold S) f"
  if [simp]: "open S"
  using diff_submanifold
  unfolding diff_fun_def
  by simp

end

context c_manifold begin

lemma diff_fun_zero: "diff_fun k charts 0"
  by (rule diff_funI) (auto simp: o_def elim!: carrierE)

lemma diff_fun_const: "diff_fun k charts (\<lambda>x. c)"
  by (rule diff_funI) (auto simp: o_def elim!: carrierE)

lemma diff_fun_add: "diff_fun k charts (a + b)" if "diff_fun k charts a" "diff_fun k charts b"
proof (rule diff_funI)
  fix x
  assume x: "x \<in> carrier"
  interpret a: diff_fun k charts a by fact
  interpret b: diff_fun k charts b by fact
  from a.diff_funE[OF x]
  obtain c where ca: "c \<in> atlas" "x \<in> domain c" "k-smooth_on (codomain c) (a \<circ> inv_chart c)"
    by blast
  show "\<exists>c1\<in>atlas. x \<in> domain c1 \<and> k-smooth_on (codomain c1) (a + b \<circ> inv_chart c1)"
    using ca
    by (auto intro!: bexI[where x=c] ca smooth_on_add_fun simp: plus_compose b.diff_fun_between_chartsD)
qed

lemma diff_fun_sum: "diff_fun k charts (\<lambda>x. \<Sum>i\<in>S. f i x)" if "\<And>i. i \<in> S \<Longrightarrow> diff_fun k charts (f i)"
  using that
  apply (induction S rule: infinite_finite_induct)
  subgoal by (simp add: diff_fun_const)
  subgoal by (simp add: diff_fun_const)
  subgoal by (simp add: diff_fun_add[unfolded plus_fun_def])
  done

lemma diff_fun_scaleR: "diff_fun k charts (\<lambda>x. a x *\<^sub>R b x)"
    if "diff_fun k charts a" "diff_fun k charts b"
proof (rule diff_funI)
  fix x
  assume x: "x \<in> carrier"
  interpret a: diff_fun k charts a by fact
  interpret b: diff_fun k charts b by fact
  from a.diff_funE[OF x]
  obtain c where ca: "c \<in> atlas" "x \<in> domain c" "k-smooth_on (codomain c) (a \<circ> inv_chart c)"
    by blast
  have *: "(\<lambda>x. a x *\<^sub>R b x) \<circ> inv_chart c = (\<lambda>x. (a o inv_chart c) x *\<^sub>R (b o inv_chart c) x)"
    by auto
  show "\<exists>c1\<in>atlas. x \<in> domain c1 \<and> k-smooth_on (codomain c1) ((\<lambda>x. a x *\<^sub>R b x) \<circ> inv_chart c1)"
    using ca
    by (auto intro!: bexI[where x=c] smooth_on_scaleR
        simp: mult_compose b.diff_fun_between_chartsD[unfolded o_def] * o_def)
qed

lemma diff_fun_scaleR_left: "diff_fun k charts (c *\<^sub>R b)"
  if "diff_fun k charts b"
  by (auto simp: scaleR_fun_def intro!: diff_fun_scaleR that diff_fun_const)

lemma diff_fun_times: "diff_fun k charts (a * b)" if "diff_fun k charts a" "diff_fun k charts b"
  for a b::"_ \<Rightarrow> _::real_normed_algebra"
proof (rule diff_funI)
  fix x
  assume x: "x \<in> carrier"
  interpret a: diff_fun k charts a by fact
  interpret b: diff_fun k charts b by fact
  from a.diff_funE[OF x]
  obtain c where ca: "c \<in> atlas" "x \<in> domain c" "k-smooth_on (codomain c) (a \<circ> inv_chart c)"
    by blast
  show "\<exists>c1\<in>atlas. x \<in> domain c1 \<and> k-smooth_on (codomain c1) (a * b \<circ> inv_chart c1)"
    using ca
    by (auto intro!: bexI[where x=c] ca smooth_on_times_fun simp: mult_compose b.diff_fun_between_chartsD)
qed

lemma diff_fun_divide: "diff_fun k charts (\<lambda>x. a x / b x)"
  if "diff_fun k charts a" "diff_fun k charts b"
    and nz: "\<And>x. x \<in> carrier \<Longrightarrow> b x \<noteq> 0"
  for a b::"_ \<Rightarrow> _::real_normed_field"
proof (rule diff_funI)
  fix x
  assume x: "x \<in> carrier"
  interpret a: diff_fun k charts a by fact
  interpret b: diff_fun k charts b by fact
  from a.diff_funE[OF x]
  obtain c where ca: "c \<in> atlas" "x \<in> domain c" "k-smooth_on (codomain c) (a \<circ> inv_chart c)"
    by blast
  show "\<exists>c1\<in>atlas. x \<in> domain c1 \<and> k-smooth_on (codomain c1) ((\<lambda>x. a x / b x) \<circ> inv_chart c1)"
    using ca nz
    by (auto intro!: bexI[where x=c] ca smooth_on_mult smooth_on_inverse
        dest: b.diff_fun_between_chartsD
        simp: mult_compose o_def
        divide_inverse)
qed

lemma subspace_Collect_diff_fun:
  "subspace (Collect (diff_fun k charts))"
  by (auto simp: subspace_def diff_fun_zero diff_fun_add diff_fun_scaleR_left)

end

lemma manifold_eucl_carrier[simp]: "manifold_eucl.carrier = UNIV"
  by (simp add: manifold_eucl.carrier_def)

lemma diff_fun_charts_euclD: "k-smooth_on UNIV g" if "diff_fun k charts_eucl g"
proof (rule smooth_on_open_subsetsI)
  fix x::'a
  interpret diff_fun k charts_eucl g by fact
  have "x \<in> manifold_eucl.carrier" by simp
  from diff_funE[OF this] obtain c1
    where c: "c1 \<in> manifold_eucl.atlas k" "x \<in> domain c1"
      "k-smooth_on (codomain c1) (g \<circ> inv_chart c1)" by auto
  have "k-smooth_on (domain c1) g"
    apply (rule smooth_on_chart_inv2)
       apply (rule smooth_on_subset)
        apply (rule c)
    using c by auto
  then show "\<exists>T. x \<in> T \<and> open T \<and> k-smooth_on T g"
    using c by auto
qed

lemma diff_fun_charts_euclI: "diff_fun k charts_eucl g" if "k-smooth_on UNIV g"
  apply (rule manifold_eucl.diff_funI)
  apply auto
  apply (rule bexI[where x=chart_eucl])
  using that
  by (auto simp: o_def)

end
