section \<open>Maps\<close>

theory Maps
imports Sequence_Zip
begin

  section \<open>Basics\<close>

  lemma fun_upd_None[simp]:
    assumes "p \<notin> dom f"
    shows "f (p := None) = f"
    using assms by auto

  (* TODO: this is a strictly stronger version of finite_set_of_finite_maps, move to library *)
  lemma finite_set_of_finite_maps':
    assumes "finite A" "finite B"
    shows "finite {m. dom m \<subseteq> A \<and> ran m \<subseteq> B}"
  proof -
    have "{m. dom m \<subseteq> A \<and> ran m \<subseteq> B} = (\<Union> \<A> \<in> Pow A. {m. dom m = \<A> \<and> ran m \<subseteq> B})" by auto
    also have "finite \<dots>" using finite_subset assms by (auto intro: finite_set_of_finite_maps)
    finally show ?thesis by this
  qed

  lemma fold_map_of:
    assumes "distinct xs"
    shows "fold (\<lambda> x (k, m). (Suc k, m (x \<mapsto> k))) xs (k, m) =
      (k + length xs, m ++ map_of (xs || [k ..< k + length xs]))"
  using assms
  proof (induct xs arbitrary: k m)
    case Nil
    show ?case by simp
  next
    case (Cons x xs)
    have "fold (\<lambda> x (k, m). (Suc k, m (x \<mapsto> k))) (x # xs) (k, m) =
      (Suc k + length xs, (m ++ map_of (xs || [Suc k ..< Suc k + length xs])) (x \<mapsto> k))"
      using Cons by (fastforce simp add: map_add_upd_left)
    also have "\<dots> = (k + length (x # xs), m ++ map_of (x # xs || [k ..< k + length (x # xs)]))"
      by (simp add: upt_rec)
    finally show ?case by this
  qed

  subsection \<open>Expanding set functions to sets of functions\<close>

  definition expand :: "('a \<Rightarrow> 'b set) \<Rightarrow> ('a \<Rightarrow> 'b) set" where
    "expand f = {g. \<forall> x. g x \<in> f x}"

  lemma expand_update[simp]:
    assumes "f x \<noteq> {}"
    shows "expand (f (x := S)) = (\<Union> y \<in> S. (\<lambda> g. g (x := y)) ` expand f)"
  unfolding expand_def
  proof (intro equalityI subsetI)
    fix g
    assume 1: "g \<in> {g. \<forall> y. g y \<in> (f (x := S)) y}"
    have 2: "g x \<in> S" "\<And> y. x \<noteq> y \<Longrightarrow> g y \<in> f y" using 1 by (auto split: if_splits)
    obtain y where 3: "y \<in> f x" using assms by auto
    show "g \<in> (\<Union> y \<in> S. (\<lambda> g. g (x := y)) ` {g. \<forall> x. g x \<in> f x})"
    proof (intro UN_I image_eqI)
      show "g x \<in> S" using 2(1) by this
      show "g (x := y) \<in> {g. \<forall> x. g x \<in> f x}" using 2 3 by auto
      show "g = g (x := y, x := g x)" by simp
    qed
  next
    fix g
    assume 1: "g \<in> (\<Union> y \<in> S. (\<lambda> g. g (x := y)) ` {g. \<forall> x. g x \<in> f x})"
    show "g \<in> {g. \<forall> y. g y \<in> (f (x := S)) y}" using 1 by auto
  qed

  subsection \<open>Expanding set maps into sets of maps\<close>

  definition expand_map :: "('a \<rightharpoonup> 'b set) \<Rightarrow> ('a \<rightharpoonup> 'b) set" where
    "expand_map f \<equiv> expand (case_option {None} (image Some) \<circ> f)"

  lemma expand_map_alt_def: "expand_map f =
    {g. dom g = dom f \<and> (\<forall> x S y. f x = Some S \<longrightarrow> g x = Some y \<longrightarrow> y \<in> S)}"
    unfolding expand_map_def expand_def by (auto split: option.splits) (force+)

  lemma expand_map_dom:
    assumes "g \<in> expand_map f"
    shows "dom g = dom f"
    using assms unfolding expand_map_def expand_def by (auto split: option.splits)

  lemma expand_map_empty[simp]: "expand_map Map.empty = {Map.empty}" unfolding expand_map_def expand_def by auto
  lemma expand_map_update[simp]:
    "expand_map (f (x \<mapsto> S)) = (\<Union> y \<in> S. (\<lambda> g. g (x \<mapsto> y)) ` expand_map (f (x := None)))"
  proof -
    let ?m = "case_option {None} (image Some)"
    have 1: "((?m \<circ> f) (x := {None})) x \<noteq> {}" by simp
    have "expand_map (f (x := Some S)) = expand_map (f (x := None, x := Some S))" by simp
    also have "\<dots> = expand ((?m \<circ> f) (x := {None}, x := ?m (Some S)))"
      unfolding expand_map_def fun_upd_comp by simp
    also have "\<dots> = (\<Union> y \<in> ?m (Some S). (\<lambda> g. g (x := y)) ` expand ((?m \<circ> f) (x := {None})))"
      using expand_update 1 by this
    also have "\<dots> = (\<Union> y \<in> S. (\<lambda> g. g (x \<mapsto> y)) ` expand_map (f (x := None)))"
      unfolding expand_map_def fun_upd_comp by simp
    finally show ?thesis by this
  qed

end