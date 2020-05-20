section\<open>Tangent Space\<close>
theory Tangent_Space
imports Partition_Of_Unity
begin

lemma linear_imp_linear_on: "linear_on A B scaleR scaleR f" if "linear f"
  "subspace A" "subspace B"
proof -
  interpret linear f by fact
  show ?thesis using that
    by unfold_locales (auto simp: add scaleR algebra_simps subspace_def)
qed

lemma (in vector_space_pair_on)
  linear_sum':
    "\<forall>x. x \<in> S1 \<longrightarrow> f x \<in> S2 \<Longrightarrow>
    \<forall>x. x \<in> S \<longrightarrow> g x \<in> S1 \<Longrightarrow>
    linear_on S1 S2 scale1 scale2 f \<Longrightarrow>
    f (sum g S) = (\<Sum>a\<in>S. f (g a))"
  using linear_sum[of f "\<lambda>x. if x \<in> S then g x else 0" S]
  by (auto simp: if_distrib if_distribR m1.mem_zero cong: if_cong)


subsection \<open>Real vector (sub)spaces\<close>

locale real_vector_space_on = fixes S assumes subspace: "subspace S"
begin

sublocale vector_space_on S scaleR
  rewrites span_eq_real: "local.span = real_vector.span"
    and dependent_eq_real: "local.dependent = real_vector.dependent"
    and subspace_eq_real: "local.subspace = real_vector.subspace"
proof -
  show "vector_space_on S (*\<^sub>R)"
    by unfold_locales (use subspace[unfolded subspace_def] in \<open>auto simp: algebra_simps\<close>)
  then interpret subspace: vector_space_on S scaleR .
  show 1: "subspace.span = span"
    unfolding subspace.span_on_def span_explicit by auto
  show 2: "subspace.dependent = dependent"
    unfolding subspace.dependent_on_def dependent_explicit by auto
  show 3: "subspace.subspace = subspace"
    unfolding subspace.subspace_on_def subspace_def by auto
qed

lemma dim_eq: "local.dim X = real_vector.dim X" if "X \<subseteq> S"
proof -
  have *: "b \<subseteq> S \<and> independent b \<and> span b = span X \<longleftrightarrow> independent b \<and> span b = span X"
    for b
    using that
    by auto (metis local.subspace_UNIV real_vector.span_base real_vector.span_eq_iff real_vector.span_mono subsetCE)
  show ?thesis
    using that
    unfolding local.dim_def real_vector.dim_def *
    by auto
qed

end

locale real_vector_space_pair_on = vs1: real_vector_space_on S + vs2: real_vector_space_on T for S T
begin

sublocale vector_space_pair_on S T scaleR scaleR
  rewrites span_eq_real1: "module_on.span scaleR = vs1.span"
    and dependent_eq_real1: "module_on.dependent scaleR = vs1.dependent"
    and subspace_eq_real1: "module_on.subspace scaleR = vs1.subspace"
    and span_eq_real2: "module_on.span scaleR = vs2.span"
    and dependent_eq_real2: "module_on.dependent scaleR = vs2.dependent"
    and subspace_eq_real2: "module_on.subspace scaleR = vs2.subspace"
  by unfold_locales (simp_all add: vs1.span_eq_real vs1.dependent_eq_real vs1.subspace_eq_real
      vs2.span_eq_real vs2.dependent_eq_real vs2.subspace_eq_real)

end

locale finite_dimensional_real_vector_space_on = real_vector_space_on S for S +
  fixes basis :: "'a set"
  assumes finite_dimensional_basis: "finite basis" "\<not> dependent basis" "span basis = S" "basis \<subseteq> S"
begin

sublocale finite_dimensional_vector_space_on S scaleR basis
  rewrites span_eq_real: "local.span = real_vector.span"
    and dependent_eq_real: "local.dependent = real_vector.dependent"
    and subspace_eq_real: "local.subspace = real_vector.subspace"
  by unfold_locales (simp_all add: finite_dimensional_basis dependent_eq_real span_eq_real)

end

locale finite_dimensional_real_vector_space_pair_1_on =
  vs1: finite_dimensional_real_vector_space_on S1 basis +
  vs2: real_vector_space_on S2
  for S1 S2 basis
begin

sublocale finite_dimensional_vector_space_pair_1_on S1 S2 scaleR scaleR basis
  rewrites span_eq_real1: "module_on.span scaleR = vs1.span"
    and dependent_eq_real1: "module_on.dependent scaleR = vs1.dependent"
    and subspace_eq_real1: "module_on.subspace scaleR = vs1.subspace"
    and span_eq_real2: "module_on.span scaleR = vs2.span"
    and dependent_eq_real2: "module_on.dependent scaleR = vs2.dependent"
    and subspace_eq_real2: "module_on.subspace scaleR = vs2.subspace"
  apply unfold_locales
  subgoal using real_vector_space_on.span_eq_real vs1.real_vector_space_on_axioms by blast
  subgoal using real_vector_space_on.dependent_eq_real vs1.real_vector_space_on_axioms by blast
  subgoal using real_vector_space_on.subspace_eq_real vs1.real_vector_space_on_axioms by blast 
  subgoal using real_vector_space_on.span_eq_real vs2.real_vector_space_on_axioms by blast
  subgoal using real_vector_space_on.dependent_eq_real vs2.real_vector_space_on_axioms by blast
  subgoal using real_vector_space_on.subspace_eq_real vs2.real_vector_space_on_axioms by blast
  done

end

locale finite_dimensional_real_vector_space_pair_on =
  vs1: finite_dimensional_real_vector_space_on S1 Basis1 +
  vs2: finite_dimensional_real_vector_space_on S2 Basis2 
  for S1 S2 Basis1 Basis2
begin

sublocale finite_dimensional_real_vector_space_pair_1_on S1 S2 Basis1
  by unfold_locales

sublocale finite_dimensional_vector_space_pair_on S1 S2 scaleR scaleR Basis1 Basis2
  rewrites "module_on.span scaleR = vs1.span"
    and "module_on.dependent scaleR = vs1.dependent"
    and "module_on.subspace scaleR = vs1.subspace"
    and "module_on.span scaleR = vs2.span"
    and "module_on.dependent scaleR = vs2.dependent"
    and "module_on.subspace scaleR = vs2.subspace"
  apply unfold_locales
  subgoal by (simp add:      span_eq_real1)
  subgoal by (simp add: dependent_eq_real1)
  subgoal by (simp add:  subspace_eq_real1)
  subgoal by (simp add:      span_eq_real2)
  subgoal by (simp add: dependent_eq_real2)
  subgoal by (simp add:  subspace_eq_real2)
  done

end


subsection \<open>Derivations\<close>

context c_manifold begin

text \<open>Set of \<open>C^k\<close> differentiable functions on carrier, where the smooth structure
   is given by charts. We assume \<open>f\<close> is zero outside carrier\<close>
definition diff_fun_space :: "('a \<Rightarrow> real) set" where
  "diff_fun_space = {f. diff_fun k charts f \<and> extensional0 carrier f}"

lemma diff_fun_spaceD: "diff_fun k charts f" if "f \<in> diff_fun_space"
  using that by (auto simp: diff_fun_space_def)

lemma diff_fun_space_order_le: "diff_fun_space \<subseteq> c_manifold.diff_fun_space charts l" if "l \<le> k"
proof -
  interpret l: c_manifold charts l
    by (rule c_manifold_order_le) fact
  show ?thesis
    unfolding diff_fun_space_def l.diff_fun_space_def
    using diff_fun.diff_fun_order_le[OF _ that]
    by auto
qed

lemma diff_fun_space_extensionalD:
  "g \<in> diff_fun_space \<Longrightarrow> extensional0 carrier g"
  by (auto simp: diff_fun_space_def)

lemma diff_fun_space_eq: "diff_fun_space = {f. diff_fun k charts f} \<inter> {f. extensional0 carrier f}"
  by (auto simp: diff_fun_space_def)

lemma subspace_diff_fun_space[intro, simp]:
  "subspace diff_fun_space"
  unfolding diff_fun_space_eq
  by (intro subspace_inter subspace_Collect_diff_fun subspace_extensional0)

lemma diff_fun_space_times: "f * g \<in> diff_fun_space"
  if "f \<in> diff_fun_space" "g \<in> diff_fun_space"
  using that by (auto simp: diff_fun_space_def intro!: diff_fun_times)

lemma diff_fun_space_add: "f + g \<in> diff_fun_space"
  if "f \<in> diff_fun_space" "g \<in> diff_fun_space"
  using that by (auto simp: diff_fun_space_def intro!: diff_fun_add)

text \<open>Set of differentiable functions is a vector space\<close>
sublocale diff_fun_space: vector_space_pair_on diff_fun_space "UNIV::real set" scaleR scaleR
  by unfold_locales
    (use subspace_diff_fun_space[unfolded subspace_def] in
      \<open>auto simp: diff_fun_space_add algebra_simps scaleR_fun_def\<close>)

text \<open>Linear functional from differentiable functions to real numbers\<close>
abbreviation "linear_diff_fun \<equiv> linear_on diff_fun_space (UNIV::real set) scaleR scaleR"

text \<open>
   Definition of a derivation.

   A linear functional \<open>X\<close> is a derivation if it additionally satisfies the property
   \<open>X (f * g) = f p * X g + g p * X f\<close>. This is suppose to represent the product rule.
\<close>
definition is_derivation :: "(('a \<Rightarrow> real) \<Rightarrow> real) \<Rightarrow> 'a \<Rightarrow> bool" where
  "is_derivation X p \<longleftrightarrow> (linear_diff_fun X \<and>
    (\<forall>f g. f \<in> diff_fun_space \<longrightarrow> g \<in> diff_fun_space \<longrightarrow> X (f * g) = f p * X g + g p * X f))"

lemma is_derivationI:
  "is_derivation X p"
  if "linear_diff_fun X"
    "\<And>f g. f \<in> diff_fun_space \<Longrightarrow> g \<in> diff_fun_space \<Longrightarrow> X (f * g) = f p * X g + g p * X f"
  using that
  unfolding is_derivation_def
  by blast

lemma is_derivationD:
  assumes "is_derivation X p"
  shows is_derivation_linear_on: "linear_diff_fun X"
    and is_derivation_derivation: "\<And>f g. f \<in> diff_fun_space \<Longrightarrow> g \<in> diff_fun_space \<Longrightarrow> X (f * g) = f p * X g + g p * X f"
  using assms
  unfolding is_derivation_def
  by blast+

text \<open>Differentiable functions on the Euclidean space\<close>
lemma manifold_eucl_diff_fun_space_iff[simp]:
  "g \<in> manifold_eucl.diff_fun_space k \<longleftrightarrow> k-smooth_on UNIV g"
  by (auto simp: manifold_eucl.diff_fun_space_def differentiable_on_def
      diff_fun_charts_euclI diff_fun_charts_euclD)


subsection \<open>Tangent space\<close>

text \<open>
  Definition of the tangent space.

  The tangent space at a point p is defined to be the set of derivations. Note
  we need to restrict the domain of the functional to differentiable functions.
\<close>
definition tangent_space :: "'a \<Rightarrow> (('a \<Rightarrow> real) \<Rightarrow> real) set" where
  "tangent_space p = {X. is_derivation X p \<and> extensional0 diff_fun_space X}"

lemma tangent_space_eq: "tangent_space p = {X. is_derivation X p} \<inter> {X. extensional0 diff_fun_space X}"
  by (auto simp: tangent_space_def)

lemma mem_tangent_space: "X \<in> tangent_space p \<longleftrightarrow> is_derivation X p \<and> extensional0 diff_fun_space X"
  by (auto simp: tangent_space_def)

lemma tangent_spaceI:
  "X \<in> tangent_space p"
  if
    "extensional0 diff_fun_space X"
    "linear_diff_fun X"
    "\<And>f g. f \<in> diff_fun_space \<Longrightarrow> g \<in> diff_fun_space \<Longrightarrow> X (f * g) = f p * X g + g p * X f"
  using that
  unfolding tangent_space_def is_derivation_def
  by blast

lemma tangent_spaceD:
  assumes "X \<in> tangent_space p"
  shows tangent_space_linear_on: "linear_diff_fun X"
    and tangent_space_restrict: "extensional0 diff_fun_space X"
    and tangent_space_derivation: "\<And>f g. f \<in> diff_fun_space \<Longrightarrow> g \<in> diff_fun_space \<Longrightarrow> X (f * g) = f p * X g + g p * X f"
  using assms
  unfolding tangent_space_def is_derivation_def
  by blast+

lemma is_derivation_0: "is_derivation 0 p"
  by (simp add: is_derivation_def diff_fun_space.linear_zero zero_fun_def)

lemma is_derivation_add: "is_derivation (x + y) p"
  if x: "is_derivation x p" and y: "is_derivation y p"
  apply (rule is_derivationI)
  subgoal using x y by (auto dest!: is_derivation_linear_on simp: diff_fun_space.linear_compose_add plus_fun_def)
  subgoal by (simp add: is_derivation_derivation[OF x] is_derivation_derivation[OF y] algebra_simps)
  done

lemma is_derivation_scaleR: "is_derivation (c *\<^sub>R x) p"
  if x: "is_derivation x p"
  apply (rule is_derivationI)
  subgoal using x diff_fun_space.linear_compose_scale_right[of x c]
    by (auto dest!: is_derivation_linear_on simp:scaleR_fun_def)
  subgoal by (simp add: is_derivation_derivation[OF x] algebra_simps)
  done

lemma subspace_is_derivation: "subspace {X. is_derivation X p}"
  by (auto simp: subspace_def is_derivation_0 is_derivation_add is_derivation_scaleR)

lemma subspace_tangent_space: "subspace (tangent_space p)"
  unfolding tangent_space_eq
  by (simp add: subspace_inter subspace_is_derivation subspace_extensional0)

sublocale tangent_space: real_vector_space_on "tangent_space p"
  by unfold_locales (rule subspace_tangent_space)

lemma tangent_space_dim_eq: "tangent_space.dim p X = dim X"
  if "X \<subseteq> tangent_space p"
proof -
  have *: "b \<subseteq> tangent_space p \<and> independent b \<and> span b = span X \<longleftrightarrow> independent b \<and> span b = span X"
    for b
    using that
    by auto (metis (no_types, lifting) c_manifold.subspace_tangent_space c_manifold_axioms span_base span_eq_iff span_mono subsetCE)  
  show ?thesis
    using that
    unfolding tangent_space.dim_def dim_def *
    by auto
qed


text \<open>properties of derivations\<close>

lemma restrict0_in_fun_space: "restrict0 carrier f \<in> diff_fun_space"
  if "diff_fun k charts f"
  by (auto simp: diff_fun_space_def intro!: diff_fun.diff_fun_cong[OF that])

lemma restrict0_const_diff_fun_space: "restrict0 carrier (\<lambda>x. c) \<in> diff_fun_space"
  by (rule restrict0_in_fun_space) (rule diff_fun_const)

lemma derivation_one_eq_zero: "X (restrict0 carrier (\<lambda>x. 1)) = 0" (is "X ?f1 = _")
  if "X \<in> tangent_space p" "p \<in> carrier"
proof -
  have "X ?f1 = X (?f1 * ?f1)" by (simp add: restrict0_times[symmetric]) (simp add: times_fun_def)
  also have "\<dots> = 1 * X (restrict0 carrier (\<lambda>x. 1)) + 1 * X (restrict0 carrier (\<lambda>x. 1))"
    apply (subst tangent_space_derivation[OF that(1)])
     apply (rule restrict0_const_diff_fun_space)
    using that
    by simp
  finally show ?thesis
    by auto
qed

lemma derivation_const_eq_zero: "X (restrict0 carrier (\<lambda>x. c)) = 0"
  if "X \<in> tangent_space p" "p \<in> carrier"
proof -
  note scaleR = diff_fun_space.linear_scale[OF _ _ tangent_space_linear_on[OF that(1)]]
  have "X (c *\<^sub>R (restrict0 carrier (\<lambda>x. 1))) = c *\<^sub>R X (restrict0 carrier (\<lambda>x. 1))"
    by (rule scaleR) (auto intro!: restrict0_const_diff_fun_space)
  also note derivation_one_eq_zero[OF that]
  also note restrict0_scaleR[symmetric]
  finally show ?thesis
    by (auto simp: scaleR_fun_def)
qed

lemma derivation_times_eq_zeroI: "X (f * g) = 0" if X:"X \<in> tangent_space p"
  and d: "f \<in> diff_fun_space" "g \<in> diff_fun_space"
  and z: "f p = 0" "g p = 0"
  using tangent_space_derivation[OF X d]
  by (simp add: z)

lemma derivation_zero_localI: "X f = 0"
  if "open W" "p \<in> W" "W \<subseteq> carrier"
    "X \<in> tangent_space p"
    "f \<in> diff_fun_space"
    "\<And>x. x \<in> W \<Longrightarrow> f x = 0"
proof -
  define A where "A = carrier - W"
  have clA: "closedin (top_of_set carrier) A"
    using \<open>open W\<close>
    apply (auto simp: A_def)
    using closedin_def openin_open by fastforce
  have \<open>A \<subseteq> carrier\<close> by (auto simp: A_def)
  have d1: "diff_fun_on A (\<lambda>x. 1)"
    unfolding diff_fun_on_def
    using \<open>A \<subseteq> carrier\<close>
    by (auto intro!:exI[where x=carrier] exI[where x="\<lambda>x. 1"] diff_fun_const)

  define U where "U = carrier - {p}"
  have "open U"
    by (auto simp: U_def)

  have "A \<subseteq> U" using that by (auto simp: A_def U_def)
  have "U \<subseteq> carrier" by (auto simp: U_def)

  from extension_lemmaE[of A "\<lambda>x. 1" U, OF clA d1 \<open>A \<subseteq> U\<close> \<open>U \<subseteq> carrier\<close> \<open>open U\<close>]
  obtain u::"'a\<Rightarrow>real" where u: "diff_fun k charts u" "(\<And>x. x \<in> A \<Longrightarrow> u x = 1)" "csupport_on carrier u \<inter> carrier \<subseteq> U"
    by blast

  have u_in_df: "restrict0 carrier u \<in> diff_fun_space"
    by (rule restrict0_in_fun_space) fact

  have "f p = 0"
    using that by auto
  have "p \<notin> U" by (auto simp: U_def)
  then have "restrict0 carrier u p = 0"
    using u(3)
    by (auto simp: restrict0_def) (meson IntI not_in_csupportD subsetCE)
  have "X (f * restrict0 carrier u) = 0"
    using \<open>X \<in> tangent_space p\<close> \<open>f \<in> diff_fun_space\<close> u_in_df \<open>f p = 0\<close>
    by (rule derivation_times_eq_zeroI) fact
  also have "f * restrict0 carrier u = f"
  proof (rule ext, cases)
    fix x assume "x \<in> W"
    then show "(f * restrict0 carrier u) x = f x"
      by (auto simp: that)
  next
    fix x assume "x \<notin> W"
    show "(f * restrict0 carrier u) x = f x"
    proof cases
      assume "x \<in> carrier"
      with \<open>x \<notin> W\<close> have "x \<in> A" by (auto simp: A_def)
      then show ?thesis using \<open>x \<in> carrier\<close>
        by (auto simp: u)
    next
      assume "x \<notin> carrier"
      then show ?thesis
        using \<open>f \<in> diff_fun_space\<close>
        by (auto dest!: diff_fun_space_extensionalD simp: extensional0_outside)
    qed
  qed
  finally show ?thesis .
qed

lemma derivation_eq_localI: "X f = X g"
  if "open U" "p \<in> U" "U \<subseteq> carrier"
    "X \<in> tangent_space p"
    "f \<in> diff_fun_space"
    "g \<in> diff_fun_space"
    "\<And>x. x \<in> U \<Longrightarrow> f x = g x"
proof -
  note minus = diff_fun_space.linear_diff[OF _ _ _ tangent_space_linear_on[OF that(4)]]
  have "f - g \<in> diff_fun_space"
    using subspace_diff_fun_space \<open>f \<in> _\<close> \<open>g \<in> _\<close>
    by (rule subspace_diff)
  have "X f - X g = X (f - g)"
    using that
    by (simp add: minus)
  also have "\<dots> = 0"
    using \<open>open U\<close> \<open>p \<in> U\<close> \<open>U \<subseteq> _\<close> \<open>X \<in> _\<close> \<open>f - g \<in> _\<close>
    by (rule derivation_zero_localI) (simp add: that)
  finally show ?thesis by simp
qed

end


subsection \<open>Push-forward on the tangent space\<close>

context diff begin

text \<open>
  Push-forward on tangent spaces.

  Given an element of the tangent space at src, considered as a functional \<open>X\<close>,
  the push-forward of \<open>X\<close> is a functional at dest, mapping \<open>g\<close> to \<open>X (g \<circ> f)\<close>.
\<close>
definition push_forward :: "(('a \<Rightarrow> real) \<Rightarrow> real) \<Rightarrow> ('b \<Rightarrow> real) \<Rightarrow> real" where
  "push_forward X = restrict0 dest.diff_fun_space (\<lambda>g. X (restrict0 src.carrier (g \<circ> f)))"

lemma extensional_push_forward: "extensional0 dest.diff_fun_space (push_forward X)"
  by (auto simp: push_forward_def)

lemma linear_push_forward: "linear push_forward"
  by (auto simp: push_forward_def[abs_def] o_def restrict0_def intro!: linearI)

text \<open>Properties of push-forwards\<close>

lemma restrict_compose_in_diff_fun_space:
  "x \<in> dest.diff_fun_space \<Longrightarrow> restrict0 src.carrier (x \<circ> f) \<in> src.diff_fun_space"
  apply (rule src.restrict0_in_fun_space)
  apply (rule diff_fun_compose)
   apply (rule diff_axioms)
  apply (rule dest.diff_fun_spaceD)
  by assumption

text \<open>Push-forward of a linear functional is a linear\<close>
lemma linear_on_diff_fun_push_forward:
  "dest.linear_diff_fun (push_forward X)"
  if "src.linear_diff_fun X"
proof unfold_locales
  note add = src.diff_fun_space.linear_add[OF _ _ _ that]
  note scale = src.diff_fun_space.linear_scale[OF _ _ that]
  fix x y::"'b \<Rightarrow> real" and c::real
  assume dfx: "x \<in> dest.diff_fun_space"
  then have dx: "diff_fun k charts2 x" and ex: "extensional0 dest.carrier x"
    by (auto simp: dest.diff_fun_space_def)
  show "push_forward X (c *\<^sub>R x) = c *\<^sub>R push_forward X x"
    unfolding push_forward_def
    using defined dfx
    by (auto simp: subspace_mul scaleR_compose restrict0_scaleR
        restrict_compose_in_diff_fun_space scale)
  assume dfy: "y \<in> dest.diff_fun_space"
  then have dy: "diff_fun k charts2 y" and ey: "extensional0 dest.carrier y"
    by (auto simp: dest.diff_fun_space_def)
  show "push_forward X (x + y) = push_forward X x + push_forward X y"
    unfolding push_forward_def
    using defined dfy dfx
    by (auto simp: subspace_add plus_compose restrict0_add restrict_compose_in_diff_fun_space add)
qed

text \<open>Push-forward preserves the product rule\<close>
lemma push_forward_is_derivation:
  "push_forward X (x * y) = x (f p) * push_forward X y + y (f p) * push_forward X x"
  (is "?l = ?r")
  if deriv: "\<And>x y. x \<in> src.diff_fun_space \<Longrightarrow> y \<in> src.diff_fun_space \<Longrightarrow> X (x * y) = x p * X y + y p * X x"
    and dx: "x \<in> dest.diff_fun_space"
    and dy: "y \<in> dest.diff_fun_space"
    and p: "p \<in> src.carrier"
proof -
  have "x * y \<in> dest.diff_fun_space"
    using dx dy
    by (auto simp: dest.diff_fun_space_def dest.diff_fun_times)
  then have "?l = X (restrict0 src.carrier (x \<circ> f) * restrict0 src.carrier (y \<circ> f))"
    by (simp add: push_forward_def mult_compose restrict0_times)
  also have "\<dots> = restrict0 src.carrier (x \<circ> f) p * X (restrict0 src.carrier (y \<circ> f)) +
    restrict0 src.carrier (y \<circ> f) p * X (restrict0 src.carrier (x \<circ> f))"
    using dx dy 
    by (simp add: deriv restrict_compose_in_diff_fun_space)
  also have "\<dots> = ?r"
    using dx dy
    by (simp add: push_forward_def p)
  finally show ?thesis .
qed

text \<open>Combining, we show that the push-forward of a derivation is a derivation\<close>
lemma push_forward_in_tangent_space:
  "push_forward ` (src.tangent_space p) \<subseteq> dest.tangent_space (f p)"
  if "p \<in> src.carrier"
  unfolding src.is_derivation_def dest.is_derivation_def src.tangent_space_def dest.tangent_space_def
  apply safe
  subgoal
    by (rule linear_on_diff_fun_push_forward)
  subgoal by (blast intro: dest.diff_fun_spaceD that push_forward_is_derivation)
  subgoal by (simp add: push_forward_def)
  done

end

text \<open>Functoriality of push-forward: identity\<close>

context c_manifold begin

lemma push_forward_id:
  "diff.push_forward k charts charts f X = X"
  if "\<And>x. x \<in> carrier \<Longrightarrow> f x = x"
    "X \<in> tangent_space p" "p \<in> carrier"
  apply (subst diff.push_forward_def)
   apply (rule diff.diff_cong[where f="\<lambda>x. x"])
    apply (rule diff_id)
   apply (rule that(1)[symmetric], assumption)
  apply (rule ext_extensional0)
  apply (rule extensional0_restrict0)
   apply (rule tangent_space_restrict)
   apply (rule that)
  apply (auto simp: )
  apply (rule arg_cong[where f=X])
  apply (rule ext_extensional0)
    apply (rule extensional0_restrict0)
   apply (rule diff_fun_space_extensionalD, assumption)
  apply (simp add: that)
  done

end

text \<open>Functoriality of push-forward: composition\<close>

lemma push_forward_compose:
  "diff.push_forward k M2 M3 g (diff.push_forward k M1 M2 f X) = diff.push_forward k M1 M3 (g o f) X"
  if "X \<in> c_manifold.tangent_space M1 k p" "p \<in> manifold.carrier M1"
    and df: "diff k M1 M2 f" and dg: "diff k M2 M3 g"
proof -
  interpret d12: diff k M1 M2 f by fact
  interpret d23: diff k M2 M3 g by fact
  interpret d13: diff k M1 M3 "g o f"
    by (rule diff_compose; fact)
  show ?thesis
    apply (rule ext_extensional0)
      apply (rule d23.extensional_push_forward)
      apply (rule d13.extensional_push_forward)
  proof -
    fix x
    assume x: "x \<in> d23.dest.diff_fun_space"
    show "d23.push_forward (d12.push_forward X) x = d13.push_forward X x"
      using x
      unfolding d12.push_forward_def d23.push_forward_def d13.push_forward_def
      apply (simp add: d23.restrict_compose_in_diff_fun_space)
      apply (rule arg_cong[where f=X])
      apply (rule ext_extensional0[OF extensional0_restrict0])
       apply (rule d12.src.diff_fun_space_extensionalD)
       apply (rule d13.restrict_compose_in_diff_fun_space, assumption)
      using d12.defined
      by auto
  qed
qed

context diffeomorphism begin

text \<open>If f is a diffeomorphism, then the push-forward \<open>f*\<close> is a bijection\<close>

lemma inv_push_forward_inverse: "push_forward (inv.push_forward X) = X"
  if "X \<in> dest.tangent_space p" "p \<in> dest.carrier"
  apply (subst push_forward_compose[OF that inv.diff_axioms diff_axioms])
  apply (rule dest.push_forward_id[OF _ that])
  by auto

lemma push_forward_inverse: "inv.push_forward (push_forward X) = X"
  if "X \<in> src.tangent_space p" "p \<in> src.carrier"
  apply (subst push_forward_compose[OF that diff_axioms inv.diff_axioms])
  apply (rule src.push_forward_id[OF _ that])
  by auto

lemma bij_betw_push_forward:
  "bij_betw push_forward (src.tangent_space p) (dest.tangent_space (f p))"
  if p: "p \<in> src.carrier"
proof (rule bij_betwI[where g="inv.push_forward"])
  show "push_forward \<in> src.tangent_space p \<rightarrow> dest.tangent_space (f p)"
    using push_forward_in_tangent_space[OF p] by auto
  show "inv.push_forward \<in> dest.tangent_space (f p) \<rightarrow> src.tangent_space p"
    using inv.push_forward_in_tangent_space[of "f p"] that defined by auto
  show "inv.push_forward (push_forward x) = x" if "x \<in> src.tangent_space p" for x
    by (rule push_forward_inverse[OF that p])
  show "push_forward (inv.push_forward y) = y" if "y \<in> dest.tangent_space (f p)" for y
    apply (rule inv_push_forward_inverse[OF that])
    using defined p by auto
qed

lemma dim_tangent_space_src_dest_eq: "dim (src.tangent_space p) = dim (dest.tangent_space (f p))"
  if p: "p \<in> src.carrier" and "dim (dest.tangent_space (f p)) > 0"
proof -
  from dest.tangent_space.dim_pos_finite_dimensional_vector_spaceE[
      unfolded dest.tangent_space_dim_eq[OF order_refl],
      OF that(2)]
  obtain basis where "basis \<subseteq> dest.tangent_space (f p)"
    "finite_dimensional_vector_space_on_with (dest.tangent_space (f p)) (+) (-) uminus 0 (*\<^sub>R) basis"
    by auto
  then interpret finite_dimensional_vector_space_on "(dest.tangent_space (f p))" scaleR basis
    unfolding finite_dimensional_vector_space_on_with_def
    by unfold_locales
      (auto simp: implicit_ab_group_add dest.tangent_space.dependent_eq_real dest.tangent_space.span_eq_real)
  interpret rev: finite_dimensional_vector_space_pair_1_on
     "dest.tangent_space (f p)" "src.tangent_space p" scaleR scaleR basis
    by unfold_locales
  from bij_betw_push_forward[OF p]
  have "inj_on push_forward (src.tangent_space p)"
    "dest.tangent_space (f p) = push_forward ` src.tangent_space p"
    unfolding bij_betw_def by auto
  have "dim (dest.tangent_space (f p)) = src.tangent_space.dim p (inv.push_forward ` dest.tangent_space (f p))"
    apply (rule rev.dim_image_eq[OF _ order_refl, of inv.push_forward, symmetric,
        unfolded dest.tangent_space_dim_eq[OF order_refl]])
    subgoal
      by (metis (no_types) contra_subsetD defined f_inv image_eqI inv.push_forward_in_tangent_space p)
    subgoal
      apply (rule linear_imp_linear_on)
        apply (rule inv.linear_push_forward)
      apply (rule dest.subspace_tangent_space)
      apply (rule src.subspace_tangent_space)
      done
    subgoal
      unfolding inj_on_def dest.tangent_space.span_eq_real 
      apply auto
    proof -
      fix x :: "('c \<Rightarrow> real) \<Rightarrow> real" and y :: "('c \<Rightarrow> real) \<Rightarrow> real"
      assume a1: "y \<in> span (dest.tangent_space (f p))"
      assume a2: "x \<in> span (dest.tangent_space (f p))"
      assume a3: "inv.push_forward x = inv.push_forward y"
      have "f p \<in> dest.carrier"
        by (meson contra_subsetD defined image_eqI p)
      then show "x = y"
        using a3 a2 a1 by (metis (no_types) c_manifold.subspace_tangent_space c_manifolds_axioms c_manifolds_def inv_push_forward_inverse span_eq_iff)
    qed
    done
  also
  have "f p \<in> dest.carrier"
    using defined p by auto
  then have "inv.push_forward ` dest.tangent_space (f p) = src.tangent_space p"
    using inv.push_forward_in_tangent_space[of "f p"] that(1)
    apply auto
    subgoal for x
      apply (rule image_eqI[where x="push_forward x"])
      apply (auto simp: push_forward_inverse)
      using \<open>dest.tangent_space (f p) = push_forward ` src.tangent_space p\<close> by blast
    done
  also have "src.tangent_space.dim p \<dots> = dim \<dots>"
    by (rule src.tangent_space_dim_eq) simp
  finally show ?thesis ..
qed

lemma dim_tangent_space_src_dest_eq2: "dim (src.tangent_space p) = dim (dest.tangent_space (f p))"
  if p: "p \<in> src.carrier" and "dim (src.tangent_space p) > 0"
proof -
  interpret rev: diffeomorphism k charts2 charts1 f' f
    by unfold_locales (auto simp: )
  from that rev.dim_tangent_space_src_dest_eq[of "f p"]
  show ?thesis
    by auto (metis contra_subsetD defined image_eqI)
qed

end

subsection \<open>Smooth inclusion map\<close>

context submanifold begin

lemma diff_inclusion: "diff k (charts_submanifold S) charts (\<lambda>x. x)"
  using diff_id
  apply (rule diff.diff_submanifold)
  unfolding charts_submanifold_def using open_submanifold
  by auto

sublocale inclusion: diff k "charts_submanifold S" charts "\<lambda>x. x"
  by (rule diff_inclusion)

lemma linear_on_push_forward_inclusion:
  "linear_on (sub.tangent_space p) (tangent_space p) scaleR scaleR inclusion.push_forward"
  apply (rule linear_imp_linear_on)
    apply (rule inclusion.linear_push_forward)
   apply (rule sub.subspace_tangent_space)
   apply (rule subspace_tangent_space)
  done

text \<open>Extension lemma: given a differentiable function on \<open>S\<close>, and a closed set \<open>B \<subseteq> S\<close>,
   there exists a function \<open>f'\<close> agreeing with \<open>f\<close> on \<open>B\<close>, such that the support
   of \<open>f'\<close> is contained in \<open>S.\<close>\<close>
lemma extension_lemma_submanifoldE:
  fixes f::"'a\<Rightarrow>'e::euclidean_space"
  assumes f: "diff_fun k (charts_submanifold S) f"
    and B: "closed B" "B \<subseteq> sub.carrier"
  obtains f' where
    "diff_fun k charts f'"
    "(\<And>x. x \<in> B \<Longrightarrow> f' x = f x)"
    "csupport_on carrier f' \<inter> carrier \<subseteq> sub.carrier"
proof -
  have 1: "closedin (top_of_set carrier) B"
    using B by (auto intro!: closed_subset)
  have 2: "diff_fun_on B f"
  proof (rule diff_fun_onI)
    show "B \<subseteq> sub.carrier" by fact
    show "sub.carrier \<subseteq> carrier" by auto
    show "open sub.carrier" using open_submanifold by auto
    have *: "charts_submanifold sub.carrier = charts_submanifold S"
      unfolding carrier_submanifold charts_submanifold_Int_carrier ..
    from f show "diff_fun k (charts_submanifold sub.carrier) f" unfolding * .
  qed simp
  from extension_lemmaE[OF 1 2 \<open>B \<subseteq> sub.carrier\<close>] open_submanifold
  obtain f' where f': "diff_fun k charts f'" "(\<And>x. x \<in> B \<Longrightarrow> f' x = f x)"
    "csupport_on carrier f' \<inter> carrier \<subseteq> sub.carrier"
    by auto
  then show ?thesis ..
qed

lemma inj_on_push_forward_inclusion: "inj_on inclusion.push_forward (sub.tangent_space p)"
  if p: "p \<in> sub.carrier"
proof -
  interpret sub: vector_space_pair_on "sub.tangent_space p" "tangent_space p" scaleR scaleR
    by unfold_locales
  show ?thesis
  proof (subst sub.linear_inj_iff_eq_0[OF _ linear_on_push_forward_inclusion], safe)
    fix v assume v: "v \<in> sub.tangent_space p"
    then show "inclusion.push_forward v \<in> tangent_space p"
      using inclusion.push_forward_in_tangent_space[OF p]
      by auto
    assume dv: "inclusion.push_forward v = 0"
    have "extensional0 sub.diff_fun_space v" using v[THEN sub.tangent_space_restrict] .
    then show "v = 0"
    proof (rule ext_extensional0)
      show "extensional0 sub.diff_fun_space (0:: ('a \<Rightarrow> real) \<Rightarrow> real)"
        by auto
      fix f assume f: "f \<in> sub.diff_fun_space"
      from sub.precompact_neighborhoodE[OF p]
      obtain B where B: "p \<in> B" "open B" "compact (closure B)" "closure B \<subseteq> sub.carrier" .
      with extension_lemma_submanifoldE[of f "closure B", OF sub.diff_fun_spaceD[OF f]]
      obtain f' where f': "diff_fun k charts f'"
        "(\<And>x. x \<in> closure B \<Longrightarrow> f' x = f x)"
        "csupport_on carrier f' \<inter> carrier \<subseteq> sub.carrier" by blast
      have rf': "restrict0 sub.carrier f' \<in> sub.diff_fun_space"
        apply (rule sub.restrict0_in_fun_space)
        apply (rule diff_fun.diff_fun_submanifold)
         apply (rule f')
        apply (rule open_submanifold)
        done
      have supp_f': "support_on carrier f' \<inter> carrier \<subseteq> sub.carrier"
        using f'(3)
        by (auto simp: csupport_on_def)
      from f'(1)
      have df': "diff_fun k charts (restrict0 sub.carrier f')"
        apply (rule diff_fun.diff_fun_cong)
        using supp_f'
        by (auto simp: restrict0_def support_on_def)
      have rf'_diff_fun: "restrict0 sub.carrier f' \<in> diff_fun_space"
        using f' df'
        by (auto simp: diff_fun_space_def extensional0_def)
      have "v f = v (restrict0 sub.carrier f')"
        apply (rule sub.derivation_eq_localI[where X=v and U="B" and p=p])
        subgoal by (rule B)
        subgoal by (rule B)
        subgoal using B by auto
        subgoal by (rule v)
        subgoal by (rule f)
        subgoal by (rule rf')
        subgoal using f' B
          by (auto simp: restrict0_def)
        done
      also have "\<dots> = inclusion.push_forward v (restrict0 sub.carrier f')"
        using rf' rf'_diff_fun
        by (auto simp: inclusion.push_forward_def o_def restrict0_restrict0)
      also have "\<dots> = 0"
        by (simp add: dv)
      finally show "v f = 0 f" by auto
    qed
  qed
qed

lemma surj_on_push_forward_inclusion:
  "inclusion.push_forward ` sub.tangent_space p \<supseteq> tangent_space p"
  if p: "p \<in> sub.carrier"
proof safe
  fix w
  assume w: "w \<in> tangent_space p"

  from sub.precompact_neighborhoodE[OF p]
  obtain B where B: "p \<in> B" "open B" "compact (closure B)" "closure B \<subseteq> sub.carrier" .
  have w_eqI: "w a = w b" if "a \<in> diff_fun_space" "b \<in> diff_fun_space" and "\<And>x. x \<in> B \<Longrightarrow> a x = b x" for a b
    apply (rule derivation_eq_localI[where X=w and U=B and p=p])
    using w B that by auto
  from tangent_space_linear_on[OF w]
  have linear_w: "linear_on diff_fun_space UNIV (*\<^sub>R) (*\<^sub>R) w" .
  note w_add = diff_fun_space.linear_add[OF _ _ _ linear_w]
  note w_scale = diff_fun_space.linear_scale[OF _ _ linear_w]
  note subspaceI = sub.subspace_diff_fun_space[THEN subspace_add]
    sub.subspace_diff_fun_space[THEN subspace_mul]
    subspace_diff_fun_space[THEN subspace_add]
    subspace_diff_fun_space[THEN subspace_mul]

  let ?P = "\<lambda>f f'. f' \<in> diff_fun_space \<and> (\<forall>x\<in>closure B. f x = f' x)"
  define extend where "extend f = (SOME f'. ?P f f')" for f
  have ex: "\<exists>f'. ?P f f'" if "f \<in> sub.diff_fun_space" for f
  proof -
    from that have "diff_fun k (charts_submanifold S) f"
      by (rule sub.diff_fun_spaceD)
    from extension_lemma_submanifoldE[OF this closed_closure \<open>closure B \<subseteq> sub.carrier\<close>]
    obtain f' where f': "diff_fun k charts f'" "(\<And>x. x \<in> closure B \<Longrightarrow> f' x = f x)" "csupport_on carrier f' \<inter> carrier \<subseteq> sub.carrier"
      by auto
    show ?thesis
      apply (rule exI[where x="restrict0 carrier f'"])
      using f' B
      by (auto intro!: restrict0_in_fun_space)
  qed
  have extend: "?P f (extend f)" if "f \<in> sub.diff_fun_space" for f
    using ex[OF that]
    unfolding extend_def
    by (rule someI_ex)
  note extend = extend[THEN conjunct1] extend[THEN conjunct2, rule_format]
  have extend2: "f \<in> sub.diff_fun_space \<Longrightarrow> x \<in> B \<Longrightarrow> extend f x = f x" for f x
    using extend by auto

  define v where "v f = w (extend f)" for f

  have ext_w: "extensional0 diff_fun_space w"
    using w by (rule tangent_space_restrict)

  have "w = inclusion.push_forward (restrict0 sub.diff_fun_space v)"
    unfolding inclusion.push_forward_def o_def
    using ext_w extensional0_restrict0
  proof (rule ext_extensional0)
    fix g
    assume g: "g \<in> diff_fun_space"
    then have "diff_fun k charts g"
      by (rule diff_fun_spaceD)
    then have "diff_fun k (charts_submanifold S) g"
      using open_submanifold
      by (rule diff_fun.diff_fun_submanifold)
    have rgsd: "restrict0 sub.carrier g \<in> sub.diff_fun_space"
      by (rule sub.restrict0_in_fun_space) fact
    have "w g = v (restrict0 sub.carrier g)"
      unfolding v_def
      apply (rule w_eqI)
      subgoal by fact
      subgoal by (rule extend) fact
      subgoal for x
        using extend(2)[of "restrict0 sub.carrier g" x] B(4) rgsd
        by (auto simp: restrict0_def split: if_splits)
      done
    with g rgsd show "w g = restrict0 diff_fun_space (\<lambda>g. restrict0 sub.diff_fun_space v (restrict0 sub.carrier g)) g"
      by auto
  qed
  moreover have "restrict0 sub.diff_fun_space v \<in> sub.tangent_space p"
    using extensional0_restrict0
  proof (rule sub.tangent_spaceI)
    have "v (x + y) = v x + v y" if "x \<in> sub.diff_fun_space" "y \<in> sub.diff_fun_space" for x y
      using that
      unfolding v_def
      by (subst w_add[symmetric]) (auto intro!: w_eqI simp: extend2 subspaceI extend(1))
    moreover have "v (c *\<^sub>R x) = c *\<^sub>R v x" if "x \<in> sub.diff_fun_space" for x c
      using that
      unfolding v_def
      by (subst w_scale[symmetric]) (auto intro!: w_eqI simp: extend2 subspaceI extend(1))
    ultimately show "linear_on sub.diff_fun_space UNIV (*\<^sub>R) (*\<^sub>R) (restrict0 sub.diff_fun_space v)"
      apply unfold_locales
      using sub.subspace_diff_fun_space[THEN subspace_add]
        sub.subspace_diff_fun_space[THEN subspace_mul]
      by auto
    fix f g assume f: "f \<in> sub.diff_fun_space" and g: "g \<in> sub.diff_fun_space"
    then have [simp]: "f * g \<in> sub.diff_fun_space" by (rule sub.diff_fun_space_times)
    have "restrict0 sub.diff_fun_space v (f * g) = w (extend (f * g))" by (simp add: v_def)
    also have "\<dots> = w (extend f * extend g)"
      apply (rule w_eqI)
      subgoal by (simp add: extend)
      subgoal by (simp add: diff_fun_space_times extend f g)
      subgoal using f g by (auto simp: extend2)
      done
    also have "\<dots> = extend f p * w (extend g) + extend g p * w (extend f)"
      apply (rule is_derivation_derivation)
      subgoal using w by (auto simp: tangent_space_def)
      by (auto intro!: extend f g)
    also have "\<dots> = f p * restrict0 sub.diff_fun_space v g + g p * restrict0 sub.diff_fun_space v f"
      by (simp add: f g v_def extend2 \<open>p \<in> B\<close>)
    finally show "restrict0 sub.diff_fun_space v (f * g) = f p * restrict0 sub.diff_fun_space v g + g p * restrict0 sub.diff_fun_space v f" .
  qed
  ultimately
  show "w \<in> inclusion.push_forward ` sub.tangent_space p" ..
qed

end

subsection \<open>Tangent space of submanifold\<close>

lemma span_idem: "span X = X" if "subspace X"
  using that by auto

context submanifold begin

lemma dim_tangent_space: "dim (tangent_space p) = dim (sub.tangent_space p)"
  if "p \<in> sub.carrier" "dim (sub.tangent_space p) > 0"
proof -
  from that(2) obtain basis where basis: "independent basis" "span basis = span (sub.tangent_space p)"
    by (auto simp: dim_def split: if_splits)
  have basis_sub: "basis \<subseteq> sub.tangent_space p"
    using basis
    apply auto
    by (metis basis(2) span_base span_eq_iff sub.subspace_tangent_space)
  have "dim (sub.tangent_space p) = card basis"
    apply (rule dim_unique[OF _ _ _ refl])
    using basis span_base
    apply auto
  proof -
    fix x :: "('a \<Rightarrow> real) \<Rightarrow> real"
    assume a1: "x \<in> basis"
    have "sub.tangent_space p = span basis"
      by (metis basis(2) span_eq_iff sub.subspace_tangent_space)
    then show "x \<in> sub.tangent_space p"
      using a1 by (metis span_base)
  qed
  with that have "finite basis"
    using card_ge_0_finite by auto
  interpret sub: finite_dimensional_vector_space_on "sub.tangent_space p" scaleR basis
       apply unfold_locales
    unfolding tangent_space.dependent_eq_real tangent_space.span_eq_real
    subgoal by fact
    subgoal by fact
    subgoal using basis by (simp add: sub.subspace_tangent_space)
    subgoal by fact
    done
  interpret sub: finite_dimensional_vector_space_pair_1_on "sub.tangent_space p" "tangent_space p" scaleR scaleR basis
    by unfold_locales
  have "dim (tangent_space p) = tangent_space.dim p (tangent_space p)"
    using order_refl by (rule tangent_space_dim_eq[symmetric])
  also have "\<dots> = tangent_space.dim p (inclusion.push_forward ` sub.tangent_space p)"
    using surj_on_push_forward_inclusion[OF that(1)] inclusion.push_forward_in_tangent_space[OF that(1)]
    by auto
  also have "tangent_space.dim p (inclusion.push_forward ` sub.tangent_space p) =
    sub.tangent_space.dim p (sub.tangent_space p)"
    apply (rule sub.dim_image_eq[of inclusion.push_forward, OF _ order_refl linear_on_push_forward_inclusion])
    subgoal using inclusion.push_forward_in_tangent_space[of p] that by auto
    subgoal unfolding tangent_space.span_eq_real span_idem[OF sub.subspace_tangent_space]
      apply (rule inj_on_push_forward_inclusion)
      apply (rule that)
      done
    done
  also have "\<dots> = dim (sub.tangent_space p)"
    using order_refl
    by (rule sub.tangent_space_dim_eq)
  finally show ?thesis  .
qed

lemma dim_tangent_space2: "dim (tangent_space p) = dim (sub.tangent_space p)"
  if "p \<in> sub.carrier" "dim (tangent_space p) > 0"
proof -
  from that(2) obtain basis where basis: "independent basis" "span basis = span (tangent_space p)"
    by (auto simp: dim_def split: if_splits)
  have basis_sub: "basis \<subseteq> tangent_space p"
    using basis
    apply auto
    using c_manifold.subspace_tangent_space c_manifold_axioms span_base span_eq_iff by blast
  have "dim (tangent_space p) = card basis"
    apply (rule dim_unique[OF _ _ _ refl])
    using basis span_base
    apply auto
  proof -
    fix x :: "('a \<Rightarrow> real) \<Rightarrow> real"
    assume a1: "x \<in> basis"
    have "tangent_space p = span basis"
      by (metis basis(2) span_eq_iff subspace_tangent_space)
    then show "x \<in> tangent_space p"
      using a1 by (metis span_base)
  qed
  with that have "finite basis"
    using card_ge_0_finite by auto
  interpret sub: finite_dimensional_vector_space_on "tangent_space p" scaleR basis
       apply unfold_locales
    unfolding tangent_space.dependent_eq_real tangent_space.span_eq_real
    subgoal by fact
    subgoal by fact
    subgoal using basis by (simp add: subspace_tangent_space)
    subgoal by fact
    done
  interpret vector_space_pair_on "sub.tangent_space p" "tangent_space p" scaleR scaleR by unfold_locales
  interpret finite_dimensional_vector_space_pair_1_on "tangent_space p" "sub.tangent_space p" scaleR scaleR basis
    by unfold_locales
  from linear_injective_left_inverse[OF _ linear_on_push_forward_inclusion inj_on_push_forward_inclusion[OF \<open>p \<in> sub.carrier\<close>]]
    inclusion.push_forward_in_tangent_space[OF \<open>p \<in> sub.carrier\<close>]
  obtain g where g: "\<And>x. x \<in> tangent_space p \<Longrightarrow> g x \<in> sub.tangent_space p"
    "linear_on (tangent_space p) (sub.tangent_space p) (*\<^sub>R) (*\<^sub>R) g"
    "\<And>x. x \<in> sub.tangent_space p \<Longrightarrow> g (inclusion.push_forward x) = x"
    by (auto simp: subset_eq)
  have inj_on_g: "inj_on g (tangent_space p)"
    using inj_on_push_forward_inclusion[OF \<open>p \<in> sub.carrier\<close>] g
    apply (auto simp: inj_on_def)
    by (metis (no_types, lifting) \<open>inclusion.push_forward ` sub.tangent_space p \<subseteq> tangent_space p\<close>
        imageE subset_antisym surj_on_push_forward_inclusion that(1))
  have "dim (tangent_space p) = tangent_space.dim p (tangent_space p)"
    using order_refl by (rule tangent_space.dim_eq[symmetric])
  also have "\<dots> = sub.tangent_space.dim p (g ` tangent_space p)"
    apply (rule dim_image_eq[OF _ order_refl, symmetric])
    subgoal using g by auto
    subgoal using g by auto
    subgoal using inj_on_g by (auto simp: tangent_space.span_eq_real span_idem subspace_tangent_space)
    done
  also have "g ` tangent_space p = sub.tangent_space p"
    using g inj_on_g     using inj_on_push_forward_inclusion[OF \<open>p \<in> sub.carrier\<close>] g
    apply (auto simp: inj_on_def)
    by (metis (no_types, lifting) \<open>inclusion.push_forward ` sub.tangent_space p \<subseteq> tangent_space p\<close>
        contra_subsetD image_eqI)
  also have "sub.tangent_space.dim p \<dots> = dim \<dots>"
    using order_refl by (rule sub.tangent_space_dim_eq)
  finally show ?thesis .
qed

end


subsection \<open>Directional derivatives\<close>

text \<open>When the manifold is the Euclidean space, The Frechet derivative
   at a in the direction of v is an element of the tangent space at a.\<close>
definition directional_derivative::"enat \<Rightarrow> 'a \<Rightarrow> 'a::euclidean_space \<Rightarrow>
  ('a \<Rightarrow> real) \<Rightarrow> real" where
  "directional_derivative k a v = restrict0 (manifold_eucl.diff_fun_space k) (\<lambda>f. frechet_derivative f (at a) v)"

lemma extensional0_directional_derivative:
  "extensional0 (manifold_eucl.diff_fun_space k) (directional_derivative k a v)"
  unfolding directional_derivative_def
  by simp

lemma extensional0_directional_derivative_le:
  "extensional0 (manifold_eucl.diff_fun_space k) (directional_derivative k' a v)"
  if "k \<le> k'"
  using that
  unfolding directional_derivative_def
  by (auto simp: extensional0_def restrict0_def manifold_eucl.diff_fun_space_def
      dest!: diff_fun.diff_fun_order_le[OF _ that])

lemma directional_derivative_add[simp]: "directional_derivative k a (x + y) = directional_derivative k a x + directional_derivative k a y"
  and directional_derivative_scaleR[simp]: "directional_derivative k a (c *\<^sub>R x) = c *\<^sub>R directional_derivative k a x"
  if "k \<noteq> 0"
  using that
  by (auto simp: directional_derivative_def restrict0_def[abs_def] fun_eq_iff
      differentiable_on_def linear_iff that
      dest!: linear_frechet_derivative spec[where x=a] smooth_on_imp_differentiable_on)

lemma linear_directional_derivative: "k \<noteq> 0 \<Longrightarrow> linear (directional_derivative k a)"
  by unfold_locales simp_all

lemma frechet_derivative_inner[simp]:
  "frechet_derivative (\<lambda>x. x \<bullet> j) (at a) = (\<lambda>x. x \<bullet> j)"
  apply (rule sym)
  apply (rule frechet_derivative_at)
  by (auto intro!: derivative_eq_intros)

lemma smooth_on_inner_const[simp]: "k-smooth_on UNIV (\<lambda>x. x \<bullet> j)"
  by (auto intro!: smooth_on_inner)    

lemma directional_derivative_inner[simp]: "directional_derivative k a x (\<lambda>x. x \<bullet> j) = x \<bullet> j"
  unfolding directional_derivative_def
  by (auto simp: restrict0_def differentiable_on_def)

lemma sum_apply: "sum f X i = sum (\<lambda>x. f x i) X"
  by (induction rule: infinite_finite_induct) auto

lemma inj_on_directional_derivative: "inj_on (directional_derivative k a) S" if "k \<noteq> 0"
  apply (rule inj_on_subset[OF _ subset_UNIV])
  unfolding linear_injective_0[OF linear_directional_derivative[OF that]]
proof safe
  fix v
  assume 0: "directional_derivative k a v = 0"
  interpret linear "directional_derivative k a" using that by (rule linear_directional_derivative)
  show "v = 0"
  proof (rule euclidean_eqI)
    fix j::'a
    assume "j \<in> Basis"
    have "0 = directional_derivative k a v (\<lambda>x. x \<bullet> j)"
      using 0 by simp
    also have "\<dots> = directional_derivative k a (\<Sum>i\<in>Basis. (v \<bullet> i) *\<^sub>R i) (\<lambda>x. x \<bullet> j)"
      by (simp add: euclidean_representation)
    also have "\<dots> = (\<Sum>i\<in>Basis. (v \<bullet> i) * frechet_derivative (\<lambda>x. x \<bullet> j) (at a) i)"
      unfolding sum
      by (auto simp: sum_apply intro!: sum.cong)
    also have "\<dots> = (v \<bullet> j)"
      using \<open>j \<in> Basis\<close>
      by (auto simp: inner_Basis if_distrib cong: if_cong)
    finally show "v \<bullet> j = 0 \<bullet> j" by simp
  qed
qed

lemma directional_derivative_eq_frechet_derivative:
  "directional_derivative k a v f = frechet_derivative f (at a) v"
  if "k-smooth_on UNIV f"
  using that
  by (auto simp: directional_derivative_def)

lemma directional_derivative_linear_on_diff_fun_space:
  "k \<noteq> 0 \<Longrightarrow> manifold_eucl.linear_diff_fun k (directional_derivative k a x)"
  by unfold_locales
    (auto simp: directional_derivative_eq_frechet_derivative differentiable_onD
      smooth_on_add_fun smooth_on_scaleR_fun
      frechet_derivative_plus_fun frechet_derivative_scaleR_fun)

lemma directional_derivative_is_derivation:
  "directional_derivative k a x (f * g) = f a * directional_derivative k a x g + g a * directional_derivative k a x f"
  if "f \<in> manifold_eucl.diff_fun_space k" "g \<in> manifold_eucl.diff_fun_space k" "k \<noteq> 0"
  using that
  by (auto simp: directional_derivative_eq_frechet_derivative smooth_on_times_fun
      frechet_derivative_times_fun differentiable_onD)

lemma directional_derivative_in_tangent_space[intro, simp]:
  "k \<noteq> 0 \<Longrightarrow> directional_derivative k a x \<in> manifold_eucl.tangent_space k a" for x
  apply (rule manifold_eucl.tangent_spaceI)
    apply (rule extensional0_directional_derivative)
   apply (rule directional_derivative_linear_on_diff_fun_space)
  apply assumption
  by (rule directional_derivative_is_derivation)


context c_manifold begin

lemma is_derivation_order_le:
  "is_derivation X p"
  if "l \<le> k" "c_manifold.is_derivation charts l X p"
proof -
  interpret l: c_manifold charts l
    by (rule c_manifold_order_le) fact
  show ?thesis
    using that(2) subspace_diff_fun_space
    using diff_fun_space_order_le[OF that(1)]
    by (auto simp: is_derivation_def l.is_derivation_def linear_on_def module_hom_on_def
        module_hom_on_axioms_def module_on_def subspace_def
        subset_iff)
qed

end

lemma smooth_on_imp_differentiable_on: "f differentiable_on S"
  if "k-smooth_on S f" "k > 0"
  using that
  by auto

text\<open>
  Key result: for the Euclidean space, the Frechet derivatives are the
  only elements of the tangent space.

  This result only holds for smooth manifolds, not for \<open>C^k\<close> differentiable
  manifolds. Smoothness is used at a key point in the proof.
\<close>
lemma surj_directional_derivative:
  "range (directional_derivative k a) = manifold_eucl.tangent_space k a"
  if "k = \<infinity>"
proof -
  have "k \<noteq> 0" using that by auto
  have "X \<in> range (directional_derivative k a)" if "X \<in> manifold_eucl.tangent_space k a" for X
  proof -
    define v where "v i = X (\<lambda>x. (x - a) \<bullet> i)" for i
    have linear_X: "manifold_eucl.linear_diff_fun k X"
      by (rule manifold_eucl.tangent_space_linear_on) fact
    note X_sum = manifold_eucl.diff_fun_space.linear_sum'[OF _ _ linear_X]
    note X_add = manifold_eucl.diff_fun_space.linear_add[OF _ _ _ linear_X]
    note X_scale = manifold_eucl.diff_fun_space.linear_scale[OF _ _ linear_X]
    have "X = directional_derivative k a (\<Sum>i\<in>Basis. v i *\<^sub>R i)"
      apply (rule ext_extensional0)
      using that
        apply (rule manifold_eucl.tangent_space_restrict)
       apply (rule extensional0_directional_derivative)
    proof -
      fix f::"'a \<Rightarrow> real"
      assume f: "f \<in> manifold_eucl.diff_fun_space k"
      then have "smooth_on UNIV f" using \<open>k = \<infinity>\<close>
        by simp
      from smooth_on_Taylor2E[OF this, of a]
      obtain g where f_exp:
        "\<And>x. f x = f a + frechet_derivative f (at a) (x - a) +
          (\<Sum>i\<in>Basis. \<Sum>j\<in>Basis. (x - a) \<bullet> j * ((x - a) \<bullet> i) * g i j x)"
        and g: "\<And>i j. i \<in> Basis \<Longrightarrow> j \<in> Basis \<Longrightarrow> smooth_on UNIV (g i j)"
        by auto
      note [simp] = \<open>k = _\<close>
      have *: "X (\<lambda>x. \<Sum>i\<in>Basis. \<Sum>j\<in>Basis. (x - a) \<bullet> j * ((x - a) \<bullet> i) * g i j x) = 0"
        thm X_sum[unfolded sum_fun_def]
        apply (subst X_sum[unfolded sum_fun_def], safe)
        subgoal by auto
        subgoal for i
          by (auto intro!: smooth_on_sum smooth_on_mult smooth_on_inner smooth_on_minus simp: g)
        apply (intro sum.neutral ballI)
        apply (subst X_sum[unfolded sum_fun_def])
        subgoal by (auto intro!: smooth_on_mult smooth_on_inner smooth_on_minus g)
        subgoal by (auto intro!: smooth_on_mult smooth_on_inner smooth_on_minus g)
      proof (intro sum.neutral ballI)
        fix i j::'a
        assume ij: "i \<in> Basis" "j \<in> Basis"
        have "X (\<lambda>xb. (xb - a) \<bullet> j * ((xb - a) \<bullet> i) * g i j xb) =
          X ((\<lambda>xb. (xb - a) \<bullet> j) * (\<lambda>xb. ((xb - a) \<bullet> i) * g i j xb))"
          by (auto simp: times_fun_def ac_simps)
        also have "\<dots> = 0"
          apply (rule manifold_eucl.derivation_times_eq_zeroI)
              apply fact
          subgoal
            by (auto intro!: smooth_on_sum smooth_on_mult smooth_on_inner smooth_on_minus)
          subgoal
            by (auto intro!: smooth_on_mult smooth_on_inner smooth_on_minus g ij)
           apply auto
          done
        finally
        show "X (\<lambda>xb. (xb - a) \<bullet> j * ((xb - a) \<bullet> i) * g i j xb) = 0"
          by simp
      qed
      from f have "smooth_on UNIV f"
        by (auto )
      have "f differentiable at a"
        apply (rule differentiable_onD)
         apply (rule smooth_on_imp_differentiable_on)
          apply fact
        by auto
      interpret Df: linear "frechet_derivative f (at a)"
        apply (rule linear_frechet_derivative)
        by fact
      have X_mult_right: "k-smooth_on UNIV xx \<Longrightarrow> X (\<lambda>x. xx x * cc) = X xx * cc" for xx cc
        using X_scale[unfolded scaleR_fun_def, simplified, of xx cc]
        by (auto simp: ac_simps)
      have blf: "bounded_linear (frechet_derivative f (at a))"
        apply (rule has_derivative_bounded_linear)
        apply (rule frechet_derivative_worksI)
        apply fact
        done
      note smooth_on_frechet = smooth_on_compose[OF bounded_linear.smooth_on[OF blf], unfolded o_def, OF _ _ open_UNIV subset_UNIV]
      have **: "X (\<lambda>x. frechet_derivative f (at a) (x - a)) = frechet_derivative f (at a) (\<Sum>i\<in>Basis. v i *\<^sub>R i)"
        unfolding v_def
        apply (subst frechet_derivative_componentwise)
        subgoal by fact
        apply (subst X_sum[unfolded sum_fun_def])
        subgoal by (auto intro!: smooth_on_sum smooth_on_mult smooth_on_inner smooth_on_minus)
        subgoal by (auto intro!: smooth_on_frechet smooth_on_minus smooth_on_mult smooth_on_inner)
        apply (subst X_mult_right)
        subgoal by (auto intro!: smooth_on_sum smooth_on_mult smooth_on_inner smooth_on_minus)
        apply (subst Df.sum)
        apply (rule sum.cong, rule refl)
        apply (subst Df.scaleR)
        apply auto
        done

      show "X f = directional_derivative k a (\<Sum>i\<in>Basis. v i *\<^sub>R i) f"
        apply (subst f_exp[abs_def])
        apply (subst X_add[unfolded plus_fun_def])
        subgoal by simp
        subgoal by (auto intro!: smooth_on_add smooth_on_frechet smooth_on_minus)
        subgoal
          by (auto intro!: smooth_on_add smooth_on_sum smooth_on_mult smooth_on_inner g smooth_on_minus)
        apply (subst X_add[unfolded plus_fun_def])
        subgoal by auto
        subgoal by (auto intro!: smooth_on_add smooth_on_frechet smooth_on_minus)
        subgoal by (auto intro!: smooth_on_frechet smooth_on_minus)
        apply (subst manifold_eucl.derivation_const_eq_zero[where c="f a" and X=X, simplified], fact)
        apply (subst *)
        apply simp
        using f
        by (simp add: directional_derivative_def **)
    qed
    then show ?thesis
      by (rule image_eqI) simp
  qed
  with directional_derivative_in_tangent_space[OF \<open>k \<noteq> 0\<close>] show ?thesis by auto
qed

lemma span_directional_derivative:
  "span (directional_derivative \<infinity> a ` Basis) = manifold_eucl.tangent_space \<infinity> a"
  by (subst span_linear_image)
    (simp_all add: linear_directional_derivative surj_directional_derivative)

lemma directional_derivative_in_span:
  "directional_derivative \<infinity> a x \<in> span (directional_derivative \<infinity> a ` Basis)"
  unfolding span_directional_derivative
  using surj_directional_derivative
  by blast

lemma linear_on_directional_derivative:
  "k \<noteq> 0 \<Longrightarrow> linear_on UNIV (manifold_eucl.tangent_space k a) (*\<^sub>R) (*\<^sub>R) (directional_derivative k a)"
  apply (rule linear_imp_linear_on)
    apply (rule linear_directional_derivative)
  by (auto simp: manifold_eucl.subspace_tangent_space)

text \<open>The directional derivatives at Basis forms a basis of the tangent space at a\<close>
interpretation manifold_eucl: finite_dimensional_real_vector_space_on
  "manifold_eucl.tangent_space \<infinity> a" "directional_derivative \<infinity> a ` Basis"
  apply unfold_locales
  subgoal by auto
  subgoal
  proof
    assume 4: "manifold_eucl.tangent_space.dependent (directional_derivative \<infinity> a ` Basis)"
    interpret rvo: real_vector_space_pair_on
       "UNIV::'a set"
       "manifold_eucl.tangent_space \<infinity> a"
      by unfold_locales simp
    have 1: "\<forall>x. x \<in> UNIV \<longrightarrow> directional_derivative \<infinity> a x \<in> manifold_eucl.tangent_space \<infinity> a"
      by auto
    have 2: "Basis \<subseteq> UNIV" by auto
    have 5: "inj_on (directional_derivative \<infinity> a) (span Basis)"
      by (rule inj_on_directional_derivative) simp_all
    from rvo.linear_dependent_inj_imageD[OF 1 2 linear_on_directional_derivative 4 5]
    show False using independent_Basis
      by auto
  qed
  subgoal by (simp add: span_directional_derivative)
  subgoal
    using surj_directional_derivative[of \<infinity> a]
    by auto
  done

lemma independent_directional_derivative:
  "k \<noteq> 0 \<Longrightarrow> independent (directional_derivative k a ` Basis)"
  by (rule linear_independent_injective_image)
    (auto simp: independent_Basis linear_directional_derivative inj_on_directional_derivative)

subsection \<open>Dimension\<close>

text \<open>For the Euclidean space, the dimension of the tangent space
   equals the dimension of the original space.\<close>
lemma dim_eucl_tangent_space:
  "dim (manifold_eucl.tangent_space \<infinity> a) = DIM('a)" for a::"'a::euclidean_space"
proof -
  interpret finite_dimensional_real_vector_space_pair_on
    "UNIV::'a set"
    "manifold_eucl.tangent_space \<infinity> a"
    Basis "directional_derivative \<infinity> a ` Basis"
    by unfold_locales (auto simp: independent_Basis)
  have "manifold_eucl.tangent_space.dim \<infinity> a (manifold_eucl.tangent_space \<infinity> a) = manifold_eucl.tangent_space.dim \<infinity> a (range (directional_derivative \<infinity> a))"
    by (simp add: surj_directional_derivative)
  also have "\<dots> = vs1.dim (UNIV::'a set)"
    by (rule dim_image_eq)
       (auto simp: linear_on_directional_derivative inj_on_directional_derivative)
  also have "\<dots> = DIM('a)"
    by (simp add: vs1.dim_UNIV)
  finally have *: "DIM('a) = manifold_eucl.tangent_space.dim \<infinity> a (manifold_eucl.tangent_space \<infinity> a)" ..
  also have "\<dots> = dim (manifold_eucl.tangent_space \<infinity> a)"
    using manifold_eucl.basis_subset _ independent_directional_derivative
  proof (rule dim_unique[symmetric])
    show "manifold_eucl.tangent_space \<infinity> a \<subseteq> span (directional_derivative \<infinity> a ` Basis)"
      by (simp add: span_directional_derivative)
    have "card (directional_derivative \<infinity> a ` Basis) = DIM('a)"
      apply (rule card_image)
      by (rule inj_on_directional_derivative) simp
    also note *
    finally show "card (directional_derivative \<infinity> a ` Basis) =
      manifold_eucl.tangent_space.dim \<infinity> a (manifold_eucl.tangent_space \<infinity> a)" .
  qed simp
  finally show ?thesis ..
qed


context c_manifold begin

text \<open>For a general manifold, the dimension of the tangent space at point p
   equals the dimension of the manifold.\<close>
lemma dim_tangent_space: "dim (tangent_space p) = DIM('b)" if p: "p \<in> carrier" and smooth: "k = \<infinity>"
proof -
  from carrierE[OF p] obtain c where "c \<in> charts" "p \<in> domain c" .
  interpret a: submanifold charts k "domain c"
    by unfold_locales simp
  let ?a = "charts_submanifold (domain c)"
  let ?b = "manifold_eucl.charts_submanifold (codomain c)"
  interpret a: diff k ?a ?b c
    apply (rule diff.diff_submanifold2)
      apply (rule diff_apply_chart)
    using \<open>c \<in> charts\<close>
    by auto
  interpret b: diff k ?b ?a "inv_chart c"
    apply (rule diff.diff_submanifold2)
      apply (rule diff_inv_chart)
    using \<open>c \<in> charts\<close>
    apply auto
    by (metis Int_iff a.dest.carrierE domain_restrict_chart image_empty image_insert
        inv_chart_in_domain manifold_eucl.dest.charts_submanifold_def open_codomain singletonD)
  interpret b: submanifold charts_eucl k "codomain c"
    by unfold_locales simp
  
  interpret diffeomorphism k "?a" "?b" "c" "inv_chart c"
    by unfold_locales auto

  have *: "DIM('b) = dim (a.dest.tangent_space (c p))"
  proof -
    have *: "DIM('b) = dim (manifold_eucl.tangent_space k (c p))"
      unfolding smooth dim_eucl_tangent_space ..
    also have "\<dots> = dim (a.dest.tangent_space (c p))"
      apply (rule b.dim_tangent_space2[of "c p"])
      subgoal
        using \<open>p \<in> domain c\<close> that
        by (auto simp: )
      subgoal unfolding *[symmetric] by simp
      done
    finally show ?thesis .
  qed
  also have **: "\<dots> = dim (a.sub.tangent_space p)"
    apply (rule dim_tangent_space_src_dest_eq[symmetric])
    unfolding *[symmetric]
    using \<open>p \<in> domain c\<close> that 
    by auto
  also have "\<dots> = dim (tangent_space p)"
    apply (rule a.dim_tangent_space[symmetric])
    unfolding *[symmetric] **[symmetric]
    using \<open>p \<in> domain c\<close> that 
    by auto
  finally show ?thesis ..
qed

end

end
