theory Enclosure_Operations
imports
  Autoref_Misc
  Affine_Arithmetic.Print
  Ordinary_Differential_Equations.Reachability_Analysis
begin

section \<open>interfaces\<close>

consts i_appr :: interface \<comment> \<open>reachable set\<close>

section \<open>Operations on Enclosures (Sets)\<close>

definition [refine_vcg_def]: "split_spec X = SPEC (\<lambda>(A, B). X \<subseteq> A \<union> B)"

definition [refine_vcg_def]: "split_spec_param (n::nat) X = SPEC (\<lambda>(A, B). X \<subseteq> A \<union> B)"
definition [refine_vcg_def]: "split_spec_params d n X = SPEC (\<lambda>(A, B). env_len A d \<and> env_len B d \<and> X \<subseteq> A \<union> B)"

definition [refine_vcg_def]: "split_spec_exact x = SPEC (\<lambda>(a, b). x = a \<union> b)"

definition [refine_vcg_def]: "Inf_specs d X = SPEC (\<lambda>r::real list. length r = d \<and> (\<forall>x \<in> X. list_all2 (\<le>) r x))"
definition [refine_vcg_def]: "Inf_spec X = SPEC (\<lambda>r. \<forall>x \<in> X. r \<le> x)"

definition [refine_vcg_def]: "Sup_specs d X = SPEC (\<lambda>r::real list. length r = d \<and> (\<forall>x \<in> X. list_all2 (\<le>) x r))"
definition [refine_vcg_def]: "Sup_spec X = SPEC (\<lambda>r. \<forall>x \<in> X. x \<le> r)"

definition [refine_vcg_def]: "Inf_inners X y = SPEC (\<lambda>r::real. (\<forall>x \<in> X. r \<le> inner_lv_rel x y))" \<comment> \<open>TODO: generic image of aforms, then Inf\<close>
definition [refine_vcg_def]: "Inf_inner X y = SPEC (\<lambda>r. \<forall>x \<in> X. r \<le> x \<bullet> y)" \<comment> \<open>TODO: generic image of aforms, then Inf\<close>

definition [refine_vcg_def]: "Sup_inners X y = SPEC (\<lambda>r::real. (\<forall>x \<in> X. r \<ge> inner_lv_rel x y))" \<comment> \<open>TODO: generic image of aforms, then Inf\<close>
definition [refine_vcg_def]: "Sup_inner X y = SPEC (\<lambda>r. \<forall>x \<in> X. x \<bullet> y \<le> r)" \<comment> \<open>TODO: generic image of aforms. then Sup\<close>

definition "plane_ofs sctn = {x. inner_lv_rel x (normal sctn) = pstn sctn}"
definition [refine_vcg_def]: "inter_sctn_specs d X sctn = SPEC (\<lambda>R. env_len R d \<and> X \<inter> plane_ofs sctn \<subseteq> R \<and> R \<subseteq> plane_ofs sctn)"
definition [refine_vcg_def]: "inter_sctn_spec X sctn = SPEC (\<lambda>R. X \<inter> plane_of sctn \<subseteq> R \<and> R \<subseteq> plane_of sctn)"

definition [refine_vcg_def]: "intersects_spec X sctn = SPEC (\<lambda>b. b \<or> X \<inter> plane_of sctn = {})"

definition [refine_vcg_def]: "intersects_sctns_spec X sctns = SPEC (\<lambda>b. b \<or> X \<inter> \<Union>(plane_of ` sctns) = {})"

definition [refine_vcg_def]: "reduce_spec (reach_options_o::unit) X = SPEC (\<lambda>R. X \<subseteq> R)"
definition [refine_vcg_def]: "reduce_specs d (reach_options_o::unit) X = SPEC (\<lambda>R. env_len R d \<and> X \<subseteq> R)"

definition [refine_vcg_def]: "width_spec X = SPEC (top::real\<Rightarrow>_)"

definition [refine_vcg_def]: "ivl_rep_of_set X = SPEC (\<lambda>(i, s). i \<le> s \<and> X \<subseteq> {i .. s})"

definition "strongest_direction T =
  (let
    b = fold (\<lambda>b' b. if abs (T \<bullet> b') \<ge> abs (T \<bullet> b) then b' else b) (Basis_list::'a::executable_euclidean_space list) 0
  in
    (sgn (T \<bullet> b) *\<^sub>R b, abs (T \<bullet> b)))"

subsection \<open>subset approximation\<close>

definition[refine_vcg_def]:  "subset_spec X Y = SPEC (\<lambda>b. b \<longrightarrow> X \<subseteq> Y)"

definition [refine_vcg_def]: "above_sctn X sctn = SPEC (\<lambda>b. b \<longrightarrow> (X \<subseteq> sabove_halfspace sctn))"

lemma above_sctn_nres: "do { ii \<leftarrow> Inf_inner X (normal sctn); RETURN (ii > pstn sctn)} \<le> above_sctn X sctn"
  by (auto simp: above_sctn_def Inf_inner_def sabove_halfspace_def gt_halfspace_def intro!: refine_vcg)

definition [refine_vcg_def]: "below_sctn X sctn = SPEC (\<lambda>b. b \<longrightarrow> (X \<subseteq> below_halfspace sctn))"

lemma below_sctn_nres:
  "do { si \<leftarrow> Sup_inner X (normal sctn); RETURN (si \<le> pstn sctn)} \<le> below_sctn X sctn"
  by (auto simp: below_sctn_def Sup_inner_def below_halfspace_def le_halfspace_def intro!: refine_vcg)

definition [refine_vcg_def]: "sbelow_sctn X sctn = SPEC (\<lambda>b. b \<longrightarrow> (X \<subseteq> sbelow_halfspace sctn))"

lemma sbelow_sctn_nres:
  "do { si \<leftarrow> Sup_inner X (normal sctn); RETURN (si < pstn sctn)} \<le> sbelow_sctn X sctn"
  by (auto simp: sbelow_sctn_def Sup_inner_def sbelow_halfspace_def lt_halfspace_def intro!: refine_vcg)

definition [refine_vcg_def]: "sbelow_sctns X sctn = SPEC (\<lambda>b. b \<longrightarrow> (X \<subseteq> sbelow_halfspaces sctn))"

lemma sbelow_sctns_nres:
  assumes "finite sctns"
  shows "FOREACH\<^bsup>(\<lambda>it b. b \<longrightarrow> (\<forall>sctn \<in> sctns - it. X \<subseteq> sbelow_halfspace sctn))\<^esup> sctns  (\<lambda>sctn b.
    do {
      b' \<leftarrow> sbelow_sctn X sctn;
      RETURN (b' \<and> b)}) True \<le> sbelow_sctns X sctns"
  unfolding sbelow_sctns_def
  by (refine_vcg assms) (auto simp: sbelow_halfspaces_def)


definition [refine_vcg_def]: "disjoint_sets X Y = SPEC (\<lambda>b. b \<longrightarrow> X \<inter> Y = {})"


section \<open>Dependencies (Set of vectors)\<close>

subsection \<open>singleton projection\<close>

definition [refine_vcg_def]: "nth_image_precond X n \<longleftrightarrow> X \<noteq> {} \<and> (\<forall>xs\<in>X. n < length xs \<and> env_len X (length xs))"

definition [refine_vcg_def]: "nth_image X n = SPEC (\<lambda>R. nth_image_precond X n \<and> (R = (\<lambda>x. x ! n) ` X))"


subsection \<open>projection\<close>

definition "project_env_precond env is \<equiv> (\<forall>i \<in> set is. \<forall>xs\<in>env. i < length xs \<and> env_len env (length xs))"

definition project_env where [refine_vcg_def]:
  "project_env env is = SPEC (\<lambda>R. project_env_precond env is \<and> env_len R (length is) \<and> (\<lambda>xs. map (\<lambda>i. xs ! i) is) ` env \<subseteq> R)"

subsection \<open>expressions\<close>

definition approx_slp_spec::"floatarith list \<Rightarrow> nat \<Rightarrow> slp \<Rightarrow> real list set \<Rightarrow> real list set option nres"
  where [refine_vcg_def]: "approx_slp_spec fas l slp env =
    (ASSERT (slp_of_fas fas = slp \<and> length fas = l)) \<bind>
    (\<lambda>_. SPEC (\<lambda>R. case R of Some R \<Rightarrow> \<exists>e. env_len env e \<and> env_len R l \<and>
        (\<forall>e\<in>env. interpret_floatariths fas e \<in> R) | None \<Rightarrow> True))"

definition approx_form_spec::"form \<Rightarrow> real list set \<Rightarrow> bool nres"
where "approx_form_spec ea E = SPEC (\<lambda>r. r \<longrightarrow> (\<forall>e\<in>E. interpret_form ea e))"

definition isFDERIV_spec
  :: "nat \<Rightarrow> nat list \<Rightarrow> floatarith list \<Rightarrow> real list set \<Rightarrow> bool nres"
  where "isFDERIV_spec N xs fas VS = SPEC (\<lambda>r. r \<longrightarrow> (\<forall>vs \<in> VS. isFDERIV N xs fas vs))"

subsection \<open>singleton environment\<close>

definition sings_spec where [refine_vcg_def]:
  "sings_spec X = SPEC (\<lambda>env. env_len env 1 \<and> X \<noteq> {} \<and> (env = (\<lambda>x. [x]) ` X))"

definition [refine_vcg_def]: "project_set X b y = SPEC (\<lambda>ivl. X \<inter> {x. x \<bullet> b = y} \<subseteq> ivl \<and> ivl \<subseteq> {x. x \<bullet> b = y})"

definition [refine_vcg_def]: "sets_of_coll X = SPEC (\<lambda>XS. X = \<Union>XS)"

definition [simp]: "is_empty \<equiv> \<lambda>x. x = {}"
lemma [autoref_itype]: "is_empty ::\<^sub>i A \<rightarrow>\<^sub>i i_bool"
  by simp

definition [refine_vcg_def]: "project_sets X b y = SPEC (\<lambda>ivl. X \<inter> {x. x \<bullet> b = y} \<subseteq> ivl \<and> ivl \<subseteq> {x. x \<bullet> b = y})"

definition [refine_vcg_def]: "restrict_to_halfspaces sctns X = SPEC (\<lambda>R. R = X \<inter> below_halfspaces sctns)"

end