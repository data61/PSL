section \<open>Functions\<close>

theory Functions
imports "../Extensions/Set_Extensions"
begin

  locale bounded_function =
    fixes A :: "'a set"
    fixes B :: "'b set"
    fixes f :: "'a \<Rightarrow> 'b"
    assumes wellformed[intro?, simp]: "x \<in> A \<Longrightarrow> f x \<in> B"

  locale bounded_function_pair =
    f: bounded_function A B f +
    g: bounded_function B A g
    for A :: "'a set"
    and B :: "'b set"
    and f :: "'a \<Rightarrow> 'b"
    and g :: "'b \<Rightarrow> 'a"

  locale injection = bounded_function_pair +
    assumes left_inverse[simp]: "x \<in> A \<Longrightarrow> g (f x) = x"
  begin

    lemma inj_on[intro]: "inj_on f A" using inj_onI left_inverse by metis

    lemma injective_on:
      assumes "x \<in> A" "y \<in> A" "f x = f y"
      shows "x = y"
      using assms left_inverse by metis

  end

  locale injective = bounded_function +
    assumes injection: "\<exists> g. injection A B f g"
  begin

    definition "g \<equiv> SOME g. injection A B f g"

    sublocale injection A B f g unfolding g_def using someI_ex[OF injection] by this

  end

  locale surjection = bounded_function_pair +
    assumes right_inverse[simp]: "y \<in> B \<Longrightarrow> f (g y) = y"
  begin

    lemma image_superset[intro]: "f ` A \<supseteq> B"
      using g.wellformed image_iff right_inverse subsetI by metis

    lemma image_eq[simp]: "f ` A = B" using image_superset by auto

  end

  locale surjective = bounded_function +
    assumes surjection: "\<exists> g. surjection A B f g"
  begin

    definition "g \<equiv> SOME g. surjection A B f g"

    sublocale surjection A B f g unfolding g_def using someI_ex[OF surjection] by this

  end

  locale bijection = injection + surjection

  lemma inj_on_bijection:
    assumes "inj_on f A"
    shows "bijection A (f ` A) f (inv_into A f)"
  proof
    show "\<And> x. x \<in> A \<Longrightarrow> f x \<in> f ` A" using imageI by this
    show "\<And> y. y \<in> f ` A \<Longrightarrow> inv_into A f y \<in> A" using inv_into_into by this
    show "\<And> x. x \<in> A \<Longrightarrow> inv_into A f (f x) = x" using inv_into_f_f assms by this
    show "\<And> y. y \<in> f ` A \<Longrightarrow> f (inv_into A f y) = y" using f_inv_into_f by this
  qed

end
