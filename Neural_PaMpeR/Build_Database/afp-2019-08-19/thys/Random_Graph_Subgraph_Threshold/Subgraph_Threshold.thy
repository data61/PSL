section\<open>The subgraph threshold theorem\<close>

theory Subgraph_Threshold
imports
  Ugraph_Properties
begin

lemma (in edge_space) measurable_pred[measurable]: "Measurable.pred P Q"
  by (simp add: P_def sets_point_measure space_point_measure subset_eq)

text\<open>This section contains the main theorem. For a fixed nonempty graph $H$, we consider the graph
property of `containing an isomorphic subgraph of $H$'. This is obviously a valid property, since
it is closed under isomorphism.

The corresponding threshold function is

  \[ t(n) = n^{-\frac{1}{\rho'(H)}}, \]

where $\rho'$ denotes @{term max_density}.\<close>

definition subgraph_threshold :: "ugraph \<Rightarrow> nat \<Rightarrow> real" where
"subgraph_threshold H n = n powr (-(1 / max_density H))"

theorem
  assumes nonempty: "nonempty_graph H" and finite: "finite_graph H" and wellformed: "uwellformed H"
  shows "is_threshold {G. H \<sqsubseteq> G} (subgraph_threshold H)"
proof
  show "ugraph_property {G. H \<sqsubseteq> G}"
    unfolding ugraph_property_def using subgraph_isomorphic_closed by blast
next

  \<comment> \<open>To prove the 0-statement, we introduce the subgraph with the maximum density as $H_0$. Note
       that $\rho(H_0) = \rho'(H)$.\<close>

  fix p :: "nat \<Rightarrow> real"

  obtain H\<^sub>0 where H\<^sub>0: "density H\<^sub>0 = max_density H" "subgraph H\<^sub>0 H" "nonempty_graph H\<^sub>0" "finite_graph H\<^sub>0" "uwellformed H\<^sub>0"
    using subgraph_has_max_density assms by blast
  hence card: "0 < card (uverts H\<^sub>0)" "0 < card (uedges H\<^sub>0)"
    unfolding nonempty_graph_def finite_graph_def by auto

  let ?v = "card (uverts H\<^sub>0)"
  let ?e = "card (uedges H\<^sub>0)"

  assume p_nz: "nonzero_prob_fun p"
  hence p: "valid_prob_fun p"
    by (fact nonzero_fun_is_valid_fun)

  \<comment> \<open>Firstly, we follow from the assumption that @{term p} is asympotically less than the
       threshold function that the product
       \[ p(n)^{|E(H_0)|} \cdot n^{|V(H_0)|} \]
       tends to $0$.\<close>

  assume "p \<lless> subgraph_threshold H"
  moreover
  {
    fix n
    have "p n / n powr (-(1 / max_density H)) = p n * n powr (1 / max_density H)"
      by (simp add: powr_minus_divide)
    also have "\<dots> = p n * n powr (1 / density H\<^sub>0)"
      using H\<^sub>0 by simp
    also have "\<dots> = p n * n powr (?v / ?e)"
      using card unfolding density_def by simp
    finally have "p n / n powr (-(1 / max_density H)) = \<dots>"
      .
  }
  ultimately have "(\<lambda>n. p n * n powr (?v / ?e)) \<longlonglongrightarrow> 0"
    unfolding subgraph_threshold_def by simp
  moreover have "\<And>n. 1 \<le> n \<Longrightarrow> 0 < p n * n powr (?v / ?e)"
    by (auto simp: p_nz)
  ultimately have "(\<lambda>n. (p n * n powr (?v / ?e)) powr ?e) \<longlonglongrightarrow> 0"
    using card(2) p by (force intro: tendsto_zero_powrI)
  hence limit: "(\<lambda>n. p n powr ?e * n powr ?v) \<longlonglongrightarrow> 0"
    by (rule LIMSEQ_cong[OF _ eventually_sequentiallyI[where c = 1]])
       (auto simp: p card p_nz powr_powr powr_mult)

  {
    fix n
    assume n: "?v \<le> n"

    interpret ES: edge_space n "(p n)"
      by unfold_locales (auto simp: p)

    let ?graph_of = "ES.edge_ugraph"

    \<comment> \<open>After fixing an @{term n}, we define a family of random variables $X$ indexed by a set of
         vertices $v$ and a set of edges $e$. Each $X$ is an indicator for the event that $(v, e)$
         is isomorphic to $H_0$ and a subgraph of a random graph. The sum of all these variables
         is denoted by $Y$ and counts the total number of copies of $H_0$ in a random graph.\<close>

    let ?X = "\<lambda>H\<^sub>0'. rind {es \<in> space ES.P. subgraph H\<^sub>0' (?graph_of es) \<and> H\<^sub>0 \<simeq> H\<^sub>0'}"
    let ?I = "{(v, e). v \<subseteq> {1..n} \<and> card v = ?v \<and> e \<subseteq> all_edges v \<and> card e = ?e}"
    let ?Y = "\<lambda>es. \<Sum>H\<^sub>0' \<in> ?I. ?X H\<^sub>0' es"

    \<comment> \<open>Now we prove an upper bound for the probability that a random graph contains a copy of
         @{term H}. Observe that in that case, $Y$ takes a value greater or equal than $1$.\<close>

    have "prob_in_class p {G. H \<sqsubseteq> G} n = probGn p n (\<lambda>es. H \<sqsubseteq> ?graph_of es)"
      by simp
    also have "\<dots> \<le> probGn p n (\<lambda>es. 1 \<le> ?Y es)"
      proof (rule ES.finite_measure_mono, safe)
        fix es
        assume es: "es \<in> space (MGn p n)"

        assume "H \<sqsubseteq> ?graph_of es"
        hence "H\<^sub>0 \<sqsubseteq> ?graph_of es" \<comment> \<open>since @{term H\<^sub>0} is a subgraph of @{term H}\<close>
          using H\<^sub>0 by (fast intro: subgraph_isomorphic_pre_subgraph_closed)
        then obtain H\<^sub>0' where H\<^sub>0': "subgraph H\<^sub>0' (?graph_of es)" "H\<^sub>0 \<simeq> H\<^sub>0'"
          unfolding subgraph_isomorphic_def
          by blast

        show "1 \<le> ?Y es"
          proof (rule sum_lower_or_eq)
            \<comment> \<open>The only relevant step here is to provide the specific instance of $(v, e)$ such
                 that $X_{(v, e)}$ takes a value greater or equal than $1$. This is trivial, as we
                 already obtained that one above (i.e. @{term H\<^sub>0'}). The remainder of the proof is
                 just bookkeeping.\<close>
            show "1 \<le> ?X H\<^sub>0' es" \<comment> \<open>by definition of $X$\<close>
              using H\<^sub>0' es by simp
          next
            have "uverts H\<^sub>0' \<subseteq> {1..n}" "uedges H\<^sub>0' \<subseteq> es"
              using H\<^sub>0'(1) unfolding subgraph_def ES.edge_ugraph_def ES.S_verts_def ES.S_edges_def by simp+
            moreover have "card (uverts H\<^sub>0') = ?v" "card (uedges H\<^sub>0') = ?e"
              by (simp add: isomorphic_cards[OF \<open>H\<^sub>0 \<simeq> H\<^sub>0'\<close>])+
            moreover have "uedges H\<^sub>0' \<subseteq> all_edges (uverts H\<^sub>0')"
              using H\<^sub>0' by (simp add: wellformed_all_edges)
            ultimately show "H\<^sub>0' \<in> ?I"
              by auto
          next
            have "?I \<subseteq> subgraphs (complete {1..n})"
              unfolding complete_def subgraphs_def subgraph_def using all_edges_mono by auto blast
            moreover have "finite (subgraphs (complete {1..n}))"
              by (simp add: complete_finite subgraphs_finite)
            ultimately show "finite ?I"
              by (fact finite_subset)
        qed simp
      qed simp

    \<comment> \<open>Applying Markov's inequality leaves us with estimating the expectation of $Y$, which is
         the sum of the individual $X$.\<close>
    also have "\<dots> \<le> ES.expectation ?Y / 1"
      by (rule prob_space.markov_inequality) (auto simp: ES.prob_space_P sum_nonneg)
    also have "\<dots> = ES.expectation ?Y"
      by simp
    also have "\<dots> = (\<Sum>H\<^sub>0' \<in> ?I. ES.expectation (?X H\<^sub>0'))"
      by (rule Bochner_Integration.integral_sum(1)) simp

    \<comment> \<open>Each expectation is bound by $p(n)^{|E(H_0)|}$. For the proof, we ignore the fact that the
         corresponding graph has to be isomorphic to @{term H\<^sub>0}, which only increases the
         probability and thus the expectation. This only leaves us to compute the probability that
         all edges are present, which is given by @{thm [source] edge_space.cylinder_prob}.\<close>
    also have "\<dots> \<le> (\<Sum>H\<^sub>0' \<in> ?I. p n ^ ?e)"
      proof (rule sum_mono)
        fix H\<^sub>0'
        assume H\<^sub>0': "H\<^sub>0' \<in> ?I"
        have "ES.expectation (?X H\<^sub>0') = ES.prob {es \<in> space ES.P. subgraph H\<^sub>0' (?graph_of es) \<and> H\<^sub>0 \<simeq> H\<^sub>0'}"
          by (rule ES.expectation_indicator) (auto simp: ES.sets_eq ES.space_eq)
        also have "\<dots> \<le> ES.prob {es \<in> space ES.P. uedges H\<^sub>0' \<subseteq> es}"
          unfolding subgraph_def by (rule ES.finite_measure_mono) (auto simp: ES.sets_eq ES.space_eq)
        also have "\<dots> = ES.prob (cylinder ES.S_edges (uedges H\<^sub>0') {})"
          unfolding cylinder_def ES.space_eq by simp
        also have "\<dots> = p n ^ card (uedges H\<^sub>0')"
          proof (rule ES.cylinder_empty_prob)
            have "uverts H\<^sub>0' \<subseteq> {1..n}" "uedges H\<^sub>0' \<subseteq> all_edges (uverts H\<^sub>0')"
              using H\<^sub>0' by auto
            hence "uedges H\<^sub>0' \<subseteq> all_edges {1..n}"
              using all_edges_mono by blast
            thus "uedges H\<^sub>0' \<subseteq> ES.S_edges"
              unfolding ES.S_edges_def ES.S_verts_def by simp
          qed
        also have "\<dots> = p n ^ ?e"
          using H\<^sub>0' by fastforce
        finally show "ES.expectation (?X H\<^sub>0') \<le> \<dots>"
          .
      qed

    \<comment> \<open>Since we have a sum of constant summands, we can rewrite it as a product.\<close>
    also have "\<dots> = card ?I * p n ^ ?e"
      by (rule sum_constant)

    \<comment> \<open>We have to count the number of possible pairs $(v, e)$. From the definition of the index
         set, note that we first choose $|V(H_0)|$ elements out of a set of @{term n} vertices and
         then $|E(H_0)|$ elements out of all possible edges over these vertices.\<close>
    also have "\<dots> = ((n choose ?v) * ((?v choose 2) choose ?e)) * p n ^ ?e"
      proof (rule arg_cong[where x = "card ?I"])
        have "card ?I = (\<Sum>v | v \<subseteq> {1..n} \<and> card v = ?v. card (all_edges v) choose ?e)"
          by (rule card_dep_pair_set[where A = "{1..n}" and n = "?v" and f = all_edges])
             (auto simp: finite_subset all_edges_finite)
        also have "\<dots> = (\<Sum>v | v \<subseteq> {1..n} \<and> card v = ?v. (?v choose 2) choose ?e)"
          proof (rule sum.cong)
            fix v
            assume "v \<in> {v. v \<subseteq> {1..n} \<and> card v = ?v}"
            hence "v \<subseteq> {1..n}" "card v = ?v"
              by auto
            thus "card (all_edges v) choose ?e = (?v choose 2) choose ?e"
              by (simp add: card_all_edges finite_subset)
          qed rule
        also have "\<dots> = card ({v. v \<subseteq> {1..n} \<and> card v = ?v}) * ((?v choose 2) choose ?e)"
          by simp
        also have "\<dots> = (n choose ?v) * ((?v choose 2) choose ?e)"
          by (simp add: n_subsets)
        finally show "card ?I = \<dots>"
          .
      qed
    also have "\<dots> = (n choose ?v) * (((?v choose 2) choose ?e) * p n ^ ?e)"
      by simp

    \<comment> \<open>Here, we use $n^k$ as an upper bound for $\binom n k$.\<close>
    also have "\<dots> \<le> (n ^ ?v) * (((?v choose 2) choose ?e) * p n ^ ?e)" (is "_ \<le> _ * ?r")
      proof (rule mult_right_mono)
        have "n choose ?v \<le> n ^ ?v"
          by (rule binomial_le_pow) (rule n)
        thus "real (n choose ?v) \<le> real (n ^ ?v)"
          by (metis of_nat_le_iff)
      next
        show "0 \<le> ?r" using p by simp
      qed
    also have "\<dots> \<le> ((?v choose 2) choose ?e) * (p n ^ ?e * n ^ ?v)" (is "_ \<le> ?factor * _")
      by simp
    also have "\<dots> = ?factor * (p n powr ?e * n powr ?v)"
      using n card(1) \<open>nonzero_prob_fun p\<close> by (simp add: powr_realpow)

    finally have "prob_in_class p {G. H \<sqsubseteq> G} n \<le> ?factor * (p n powr ?e * n powr ?v)"
      .
  }

  \<comment> \<open>The final upper bound is a multiple of the expression which we have proven to tend to $0$
       in the beginning.\<close>
  thus "prob_in_class p {G. H \<sqsubseteq> G} \<longlonglongrightarrow> 0"
    by (rule LIMSEQ_le_zero[OF tendsto_mult_right_zero[OF limit] eventually_sequentiallyI[OF measure_nonneg] eventually_sequentiallyI])
next
  fix p :: "nat \<Rightarrow> real"
  assume p_threshold: "subgraph_threshold H \<lless> p"

  \<comment> \<open>To prove the 1-statement, we obtain a fixed selector @{term f} as defined in section
       \ref{sec:selector}.\<close>
  from assms obtain f where f: "is_fixed_selector H f"
    using ex_fixed_selector by blast

  let ?v = "card (uverts H)"
  let ?e = "card (uedges H)"

  \<comment> \<open>We observe that several terms involving $|V(H)|$ are positive.\<close>
  have v_e_nz: "0 < real ?v" "0 < real ?e"
    using nonempty finite unfolding nonempty_graph_def finite_graph_def by auto
  hence "0 < real ?v ^ ?v" by simp
  hence vpowv_inv_gr_z: "0 < 1 / ?v ^ ?v" by simp

  \<comment> \<open>For a given $n$, let $A$ be a family of events indexed by a set $S$. Each $A$ contains the
       graphs whose induced subgraphs over $S$ contain the selected copy of @{term H} by @{term f}
       over $S$.\<close>
  let ?A = "\<lambda>n. \<lambda>S. {es \<in> space (edge_space.P n (p n)). subgraph (f S) (induced_subgraph S (edge_space.edge_ugraph n es))}"
  let ?I = "\<lambda>n. {S. S \<subseteq> {1..n} \<and> card S = ?v}"

  assume p_nz: "nonzero_prob_fun p"
  hence p: "valid_prob_fun p"
    by (fact nonzero_fun_is_valid_fun)
  {
    fix n
    \<comment> \<open>At this point, we can assume almost anything about @{term n}: We only have to show that
         a function converges, hence the necessary properties are allowed to be violated for small
         values of @{term n}.\<close>
    assume n_2v: "2 * ?v \<le> n"
    hence n: "?v \<le> n"
      by simp

    have is_es: "edge_space (p n)"
      by unfold_locales (auto simp: p)

    then interpret edge_space n "p n"
      .

    let ?A = "?A n"
    let ?I = "?I n"

    \<comment> \<open>A nice potpourri with some technical facts about @{text S}.\<close>
    {
      fix S
      assume "S \<in> ?I"
      hence 0: "S \<subseteq> {1..n}" "?v = card S" "finite S"
        by (auto intro: finite_subset)
      hence 1: "H \<simeq> f S" "uverts (f S) = S"
        using f wellformed_finite unfolding finite_graph_def is_fixed_selector_def by auto
      have 2: "finite_graph (f S)"
        using 0(3) 1(1,2) by (metis wellformed_finite)
      have 3: "nonempty_graph (f S)"
        using 0(2) 1(1,2) by (metis card_eq_0_iff finite finite_graph_def isomorphic_cards(2) nonempty nonempty_graph_def prod.collapse snd_conv)
      note 0 1 2 3
    }
    note I = this

    \<comment> \<open>In the following two blocks, we prove the probabilities of the events $A$ and the
         probability of the intersection of two events $A$. For both cases, we employ the auxiliary
         lemma @{thm [source] edge_space.induced_subgraph_prob} which is not very interesting.
         For the latter however, the tricky part is to argue that such an intersection is equivalent
         to the \emph{union} of the desired copies of @{term H} to be contained in the \emph{union}
         of the induced subgraphs.\<close>
    {
      fix S
      assume S: "S \<in> ?I"
      note S' = I[OF S]
      have "prob (?A S) = p n ^ ?e"
        using isomorphic_cards(2)[OF S'(4)] S' by (simp add: S_verts_def induced_subgraph_prob)
    }
    note prob_A = this

    {
      fix S T
      assume "S \<in> ?I" note S = I[OF this]
      assume "T \<in> ?I" note T = I[OF this]
      \<comment> \<open>Note that we do not restrict @{term S} and @{term T} to be disjoint, since we need the
           general case later to determine when two events are independent. Additionally, it would
           be unneeded at this point.\<close>

      have "prob (?A S \<inter> ?A T) = prob {es \<in> space P. subgraph (S \<union> T, uedges (f S) \<union> uedges (f T)) (induced_subgraph (S \<union> T) (edge_ugraph es))}" (is "_ = prob ?M")
        proof (rule arg_cong[where f = prob])
          have "?A S \<inter> ?A T = {es \<in> space P. subgraph (f S) (induced_subgraph S (edge_ugraph es)) \<and> subgraph (f T) (induced_subgraph T (edge_ugraph es))}"
            by blast
          also have "\<dots> = ?M"
            using S T by (auto simp: subgraph_union_induced)
          finally show "?A S \<inter> ?A T = \<dots>"
            .
        qed
      also have "\<dots> = p n ^ card (uedges (S \<union> T, uedges (f S) \<union> uedges (f T)))"
        proof (rule induced_subgraph_prob)
          show "uwellformed (S \<union> T, uedges (f S) \<union> uedges (f T))"
            using S(4,5) T(4,5) unfolding uwellformed_def by auto
        next
          show "S \<union> T \<subseteq> S_verts"
            using S(1) T(1) unfolding S_verts_def by simp
        qed simp
      also have "\<dots> = p n ^ card (uedges (f S) \<union> uedges (f T))"
        by simp

      finally have "prob (?A S \<inter> ?A T) = p n ^ card (uedges (f S) \<union> uedges (f T))"
        .
    }
    note prob_A_intersect = this

    \<comment> \<open>Another technical detail is that our family of events $A$ are a valid instantiation for
         the ``$\Delta$ lemmas'' from section \ref{sec:delta}.\<close>
    have is_psi: "prob_space_with_indicators P ?I ?A"
      proof
        show "finite ?I"
          by (rule finite_subset[where B = "Pow {1..n}"]) auto
      next
        show "?A ` ?I \<subseteq> sets P"
          unfolding sets_eq space_eq by blast
      next
        let ?V = "{1..?v}"
        have "0 < prob (?A ?V)"
          by (simp add: prob_A n p_nz)
        moreover have "?V \<in> ?I"
          using n by force
        ultimately show "\<exists>i \<in> ?I. 0 < prob (?A i)"
          by blast
      qed

    then interpret prob_space_with_indicators "P" ?I ?A
      .

    \<comment> \<open>We proceed by reducing the claim of the 1-statement that the probability tends to $1$ to
         showing that the expectation that the sum of all indicators of the respective events $A$
         tends to $0$. (The actual reduction is done at the end of the proof, we merely collect
         the facts here.)\<close>
    have compl_prob: "1 - prob {es \<in> space P. \<not> H \<sqsubseteq> edge_ugraph es} = prob_in_class p {G. H \<sqsubseteq> G} n"
      by (subst prob_compl[symmetric]) (auto simp: space_eq sets_eq intro: arg_cong[where f = prob])

    have "prob {es \<in> space P. \<not> H \<sqsubseteq> edge_ugraph es} \<le> prob {es \<in> space P. Y es = 0}" (is "?compl \<le> _")
      proof (rule finite_measure_mono, safe)
        fix es
        assume "es \<in> space P"
        hence es: "uwellformed (edge_ugraph es)"
          unfolding space_eq by (rule wellformed_and_finite(2))
        assume H: "\<not> H \<sqsubseteq> edge_ugraph es"
        {
          fix S
          assume "S \<subseteq> {1..n}" "card S = ?v"
          moreover hence "finite S" "S \<subseteq> uverts (edge_ugraph es)"
            unfolding uverts_edge_ugraph S_verts_def by (auto intro: finite_subset)
          ultimately have "\<not> subgraph (f S) (induced_subgraph S (edge_ugraph es))"
            using H es by (metis fixed_selector_induced_subgraph[OF f])
          hence "X S es = 0"
            unfolding X_def by simp
        }
        thus "Y es = 0"
          unfolding Y_def by simp
      qed simp

    \<comment> \<open>By applying the $\Delta$ lemma, we obtain our central inequality. The rest of the proof
         gives bounds for @{text \<mu>}, @{text \<Delta>\<^sub>d} and quotients which occur on the right hand side.\<close>
    hence compl_upper: "?compl \<le> 1 / \<mu> + \<Delta>\<^sub>d / \<mu>^2"
      by (rule order_trans) (fact prob_\<mu>_\<Delta>\<^sub>d)

    \<comment> \<open>Lower bound for the expectation. We use $\left(\frac n k\right)^k$ as lower bound for
         $\binom n k$.\<close>
    have "1 / ?v ^ ?v * (real n ^ ?v * p n ^ ?e) = (n / ?v) ^ ?v * p n ^ ?e"
      by (simp add: power_divide)
    also have "\<dots> \<le> (n choose ?v) * p n ^ ?e"
      proof (rule mult_right_mono, rule binomial_ge_n_over_k_pow_k)
        show "?v \<le> n"
          using n .
        show "0 \<le> p n ^ ?e"
          using p by simp
      qed
    also have "\<dots> = (\<Sum>S \<in> ?I. p n ^ ?e)"
      by (simp add: n_subsets)
    also have "\<dots> = (\<Sum>S \<in> ?I. prob (?A S))"
      by (simp add: prob_A)
    also have "\<dots> = \<mu>"
      unfolding expectation_X_Y X_def using expectation_indicator by force
    finally have ex_lower: "1 / (?v ^ ?v) * (real n ^ ?v * p n ^ ?e) \<le> \<mu>"
      .

    \<comment> \<open>Upper bound for the inverse expectation. Follows trivially from above.\<close>
    have ex_lower_pos: "0 < 1 / ?v ^ ?v * (real n ^ ?v * p n ^ ?e)"
      proof (rule mult_pos_pos[OF vpowv_inv_gr_z mult_pos_pos])
        have "0 < real n"
          using n nonempty finite unfolding nonempty_graph_def finite_graph_def by auto
        thus "0 < real n ^ ?v"
          by simp
      next
        show "0 < p n ^ card (uedges H)"
          using p_nz by simp
      qed
    hence "1 / \<mu> \<le> 1 / (1 / ?v ^ ?v * (real n ^ ?v * p n ^ ?e))"
      by (rule divide_left_mono[OF ex_lower zero_le_one mult_pos_pos[OF \<mu>_non_zero]])
    hence inv_ex_upper: "1 / \<mu> \<le> ?v ^ ?v * (1 / (real n ^ ?v * p n ^ ?e))"
      by simp

    \<comment> \<open>Recall the definition of @{text "\<Delta>\<^sub>d"}:
         \[ \Delta_d = \sum\limits_{\substack{S \in I,\, T \in I\\S \neq T\\A_S,\, A_T \text{ not independent}}} \Pr[A_S \cap A_T] \]
         We are going to prove an upper bound for that sum, so we can safely augment the index set
         by replacing it with a neccessary condition.

         The idea is that if the two sets $S$ and $T$ are not independent, their intersection is not
         empty. We prove that by contraposition, i.e. if the intersection is empty, then they are
         independent. This in turn can be shown using some basic properties of @{term f}.\<close>
    {
      fix S T
      assume "S \<in> ?I" "T \<in> ?I"
      hence *: "prob (?A S) * prob (?A T) = p n ^ (2 * ?e)"
        using prob_A by (simp add: power_even_eq power2_eq_square)

      note S = I[OF \<open>S \<in> ?I\<close>]
      note T = I[OF \<open>T \<in> ?I\<close>]
      assume disj: "S \<inter> T = {}"

      have "prob (?A S \<inter> ?A T) = p n ^ card (uedges (f S) \<union> uedges (f T))"
        using \<open>S \<in> ?I\<close> \<open>T \<in> ?I\<close> by (fact prob_A_intersect)
      also have "\<dots> = p n ^ (card (uedges (f S)) + card (uedges (f T)))"
        proof (rule arg_cong[OF card_Un_disjoint])
          have "finite_graph (f S)" "finite_graph (f T)"
            using S T by (auto simp: wellformed_finite)
          thus "finite (uedges (f S))" "finite (uedges (f T))"
            unfolding finite_graph_def by auto
        next
          have "uedges (f S) \<subseteq> all_edges S" "uedges (f T) \<subseteq> all_edges T"
            using S(4,5) T(4,5) by (metis wellformed_all_edges)+
          moreover have "all_edges S \<inter> all_edges T = {}"
            by (fact all_edges_disjoint[OF disj])
          ultimately show "uedges (f S) \<inter> uedges (f T) = {}"
            by blast
        qed
      also have "\<dots> = p n ^ (2 * ?e)"
        using isomorphic_cards(2)[OF isomorphic_sym[OF S(4)]] isomorphic_cards(2)[OF isomorphic_sym[OF T(4)]] by (simp add: mult_2)
      finally have **: "prob (?A S \<inter> ?A T) = \<dots>"
        .

      from * ** have "indep (?A S) (?A T)"
        unfolding indep_def by force
    }
    note indep = this

    \<comment> \<open>Now we prove an upper bound for @{text "\<Delta>\<^sub>d"}.\<close>
    have "\<Delta>\<^sub>d = (\<Sum>S \<in> ?I. \<Sum>T | T \<in> ?I \<and> ineq_dep S T. prob (?A S \<inter> ?A T))"
      unfolding \<Delta>\<^sub>d_def ..

    \<comment> \<open>Augmenting the index set as described above.\<close>
    also have "\<dots> \<le> (\<Sum>S \<in> ?I. \<Sum>T | T \<in> ?I \<and> S \<inter> T \<noteq> {}. prob (?A S \<inter> ?A T))"
      by (rule sum_mono[OF sum_mono2]) (auto simp: indep measure_nonneg)

    \<comment> \<open>So far, we are adding the intersection probabilities over pairs of sets which have a
         nonempty intersection. Since we know that these intersections have at least one element
         (as they are nonempty) and at most $|V(H)|$ elements (by definition of $I$). In this step,
         we will partition this sum by cardinality of the intersections.\<close>
    also have "\<dots> = (\<Sum>S \<in> ?I. \<Sum>T \<in> (\<Union>k \<in> {1..?v}. {T \<in> ?I. card (S \<inter> T) = k}). prob (?A S \<inter> ?A T))"
      proof (rule sum.cong, rule refl, rule sum.cong)
        fix S
        assume "S \<in> ?I"
        note I(2,3)[OF this]
        hence "{T. S \<inter> T \<noteq> {}} = (\<Union>k \<in> {1..?v}. {T. card (S \<inter> T) = k})"
          by (simp add: partition_set_of_intersecting_sets_by_card)
        thus "{T \<in> ?I. S \<inter> T \<noteq> {}} = (\<Union>k\<in>{1..?v}. {T \<in> ?I. card (S \<inter> T) = k})"
          by blast
      qed simp
    also have "\<dots> = (\<Sum>S \<in> ?I. \<Sum>k = 1..?v. \<Sum>T | T \<in> ?I \<and> card (S \<inter> T) = k. prob (?A S \<inter> ?A T))"
      by (rule sum.cong, rule refl, rule sum.UNION_disjoint) auto
    also have "\<dots> = (\<Sum>k = 1..?v. \<Sum>S \<in> ?I. \<Sum>T | T \<in> ?I \<and> card (S \<inter> T) = k. prob (?A S \<inter> ?A T))"
      by (rule sum.swap)

    \<comment> \<open>In this step, we compute an upper bound for the intersection probability and argue that
         it only depends on the cardinality of the intersection.\<close>
    also have "\<dots> \<le> (\<Sum>k = 1..?v. \<Sum>S \<in> ?I. \<Sum>T | T \<in> ?I \<and> card (S \<inter> T) = k. p n powr (2 * ?e - max_density H * k))"
      proof (rule sum_mono)+
        fix k
        assume k: "k \<in> {1..?v}"
        fix S T
        assume "S \<in> ?I" "T \<in> {T. T \<in> ?I \<and> card (S \<inter> T) = k}"
        hence "T \<in> ?I" and ST_k: "card (S \<inter> T) = k"
          by auto
        note S = I[OF \<open>S \<in> ?I\<close>]
        note T = I[OF \<open>T \<in> ?I\<close>]

        let ?cST = "card (uedges (f S) \<inter> uedges (f T))"

        \<comment> \<open>We already know the intersection probability.\<close>
        have "prob (?A S \<inter> ?A T) = p n ^ card (uedges (f S) \<union> uedges (f T))"
          using \<open>S \<in> ?I\<close> \<open>T \<in> ?I\<close> by (fact prob_A_intersect)

        \<comment> \<open>Now, we consider the number of edges shared by the copies of @{term H} over @{term S}
             and @{term T}.\<close>
        also have "\<dots> = p n ^ (card (uedges (f S)) + card (uedges (f T)) - ?cST)"
          using S T unfolding finite_graph_def by (simp add: card_union)
        also have "\<dots> = p n ^ (?e + ?e - ?cST)"
          by (metis isomorphic_cards(2)[OF S(4)] isomorphic_cards(2)[OF T(4)])
        also have "\<dots> = p n ^ (2 * ?e - ?cST)"
          by (simp add: mult_2)
        also have "\<dots> = p n powr (2 * ?e - ?cST)"
          using p_nz by (simp add: powr_realpow)
        also have "\<dots> = p n powr (real (2 * ?e) - real ?cST)"
          using isomorphic_cards[OF S(4)] S(6) by (metis of_nat_diff card_mono finite_graph_def inf_le1 mult_le_mono mult_numeral_1 numeral_One one_le_numeral)

        \<comment> \<open>Since the intersection graph is also an isomorphic subgraph of @{term H}, we know that
             its density has to be less than or equal to the maximum density of @{term H}. The proof
             is quite technical.\<close>
        also have "\<dots> \<le> p n powr (2 * ?e - max_density H * k)"
          proof (rule powr_mono3)
            have "?cST = density (S \<inter> T, uedges (f S) \<inter> uedges (f T)) * k"
              unfolding density_def using k ST_k by simp
            also have "\<dots> \<le> max_density (f S) * k" (* EXTREME METIS!!!1 *)
              proof (rule mult_right_mono, cases "uedges (f S) \<inter> uedges (f T) = {}")
                case True
                hence "density (S \<inter> T, uedges (f S) \<inter> uedges (f T)) = 0"
                  unfolding density_def by simp
                also have "0 \<le> density (f S)"
                  unfolding density_def by simp
                also have "density (f S) \<le> max_density (f S)"
                  using S by (simp add: max_density_is_max subgraph_refl)
                finally show "density (S \<inter> T, uedges (f S) \<inter> uedges (f T)) \<le> max_density (f S)"
                  .
              next
                case False
                show "density (S \<inter> T, uedges (f S) \<inter> uedges (f T)) \<le> max_density (f S)"
                  proof (rule max_density_is_max)
                    show "finite_graph (S \<inter> T, uedges (f S) \<inter> uedges (f T))"
                      using T(3,6) by (metis finite_Int finite_graph_def fst_eqD snd_conv)
                    show "nonempty_graph (S \<inter> T, uedges (f S) \<inter> uedges (f T))"
                      unfolding nonempty_graph_def using k ST_k False by force
                    show "uwellformed (S \<inter> T, uedges (f S) \<inter> uedges (f T))"
                      using S(4,5) T(4,5) unfolding uwellformed_def by (metis Int_iff fst_eqD snd_eqD)
                    show "subgraph (S \<inter> T, uedges (f S) \<inter> uedges (f T)) (f S)"
                      using S(5) by (metis fst_eqD inf_sup_ord(1) snd_conv subgraph_def)
                  qed (simp add: S)
              qed simp
            also have "\<dots> = max_density H * k"
              using assms S by (simp add: isomorphic_max_density[where G\<^sub>1 = H and G\<^sub>2 = "f S"])
            finally have "?cST \<le> max_density H * k"
              .
            thus "2 * ?e - max_density H * k \<le> 2 * ?e - real ?cST"
              by linarith
          qed (auto simp: p_nz)
        finally show "prob (?A S \<inter> ?A T) \<le> \<dots>"
          .
      qed

    \<comment> \<open>Further rewriting the index sets.\<close>
    also have "\<dots> = (\<Sum>k = 1..?v. \<Sum>(S, T) \<in> (SIGMA S : ?I. {T \<in> ?I. card (S \<inter> T) = k}). p n powr (2 * ?e - max_density H * k))"
      by (rule sum.cong, rule refl, rule sum.Sigma) auto
    also have "\<dots> = (\<Sum>k = 1..?v. card (SIGMA S : ?I. {T \<in> ?I. card (S \<inter> T) = k}) * p n powr (2 * ?e - max_density H * k))"
      by (rule sum.cong) auto

    \<comment> \<open>Here, we compute the cardinality of the index sets and use the same upper bounds for
         the binomial coefficients as for the 0-statement.\<close>
    also have "\<dots> \<le> (\<Sum>k = 1..?v. ?v ^ k * (real n ^ (2 * ?v - k) * p n powr (2 * ?e - max_density H * k)))"
      proof (rule sum_mono)
        fix k
        assume k: "k \<in> {1..?v}"
        let ?p = "p n powr (2 * ?e - max_density H * k)"

        have "card (SIGMA S : ?I. {T \<in> ?I. card (S \<inter> T) = k}) = (\<Sum>S \<in> ?I. card {T \<in> ?I. card (S \<inter> T) = k})" (is "?lhs = _")
          by simp
        also have "\<dots> = (\<Sum>S \<in> ?I. (?v choose k) * ((n - ?v) choose (?v - k)))"
          using n k by (fastforce simp: card_set_of_intersecting_sets_by_card)
        also have "\<dots> = (n choose ?v) * ((?v choose k) * ((n - ?v) choose (?v - k)))"
          by (auto simp: n_subsets)
        also have "\<dots> \<le> n ^ ?v * ((?v choose k) * ((n - ?v) choose (?v - k)))"
          using n by (simp add: binomial_le_pow)
        also have "\<dots> \<le> n ^ ?v * ?v ^ k * ((n - ?v) choose (?v - k))"
          using k by (simp add: binomial_le_pow)
        also have "\<dots> \<le> n ^ ?v * ?v ^ k * (n - ?v) ^ (?v - k)"
          using n_2v by (simp add: binomial_le_pow)
        also have "\<dots> \<le> n ^ ?v * ?v ^ k * n ^ (?v - k)"
          by (simp add: power_mono)
        also have "\<dots> = ?v ^ k * (n ^ (?v + (?v - k)))"
          by (simp add: power_add)
        also have "\<dots> = ?v ^ k * n ^ (2 * ?v - k)" (is "_ = ?rhs")
          using k by (simp add: mult_2)
        finally have "?lhs \<le> ?rhs" .
        hence "real ?lhs \<le> real ?rhs"
          using of_nat_le_iff by blast
        moreover have "0 \<le> ?p"
          by simp
        ultimately have "?lhs * ?p \<le> ?rhs * ?p"
          by (rule mult_right_mono)
        also have "\<dots> = ?v ^ k * (real n ^ (2 * ?v - k) * ?p)"
          by simp
        finally show "?lhs * ?p \<le> \<dots>"
          .
      qed
    finally have delta_upper: "\<Delta>\<^sub>d \<le> (\<Sum>k = 1..?v. ?v ^ k * (real n ^ (2 * ?v - k) * p n powr (2 * ?e - max_density H * k)))"
      .

    \<comment> \<open>At this point, we have established all neccessary bounds.\<close>
    note is_es is_psi compl_prob compl_upper ex_lower ex_lower_pos inv_ex_upper delta_upper
  }
  note facts = this

  \<comment> \<open>Recall our central inequality. We now prove that both summands tend to $0$. This is mainly
       an exercise in bookkeeping and real arithmetics as no intelligent ideas are involved.\<close>
  have "(\<lambda>n. 1 / prob_space_with_indicators.\<mu> (MGn p n) (?I n) (?A n)) \<longlonglongrightarrow> 0"
    proof (rule LIMSEQ_le_zero)
      have "(\<lambda>n. 1 / (real n ^ ?v * p n ^ ?e)) \<longlonglongrightarrow> 0"
        proof (rule LIMSEQ_le_zero[OF _ eventually_sequentiallyI eventually_sequentiallyI])
          fix n
          show "0 \<le> 1 / (real n ^ ?v * p n ^ ?e)"
            using p by simp

          assume n: "1 \<le> n"
          have "1 / (real n ^ ?v * p n ^ ?e) = 1 / (real n powr ?v * p n powr ?e)"
            using n p_nz by (simp add: powr_realpow[symmetric])
          also have "\<dots> = real n powr -real ?v * p n powr -real ?e"
            by (simp add: powr_minus_divide)
          also have "\<dots> = (real n powr -(?v / ?e)) powr ?e * (p n powr -1) powr ?e"
            using v_e_nz by (simp add: powr_powr)
          also have "\<dots> = (real n powr -(?v / ?e) * p n powr -1) powr ?e"
            by (simp add: powr_mult)
          also have "\<dots> = (real n powr -(1 / (?e / ?v)) * p n powr -1) powr ?e"
            by simp
          also have "\<dots> \<le> (real n powr -(1 / max_density H) * p n powr -1) powr ?e"
            apply (rule powr_mono2[OF _ _ mult_right_mono[OF powr_mono[OF le_imp_neg_le[OF divide_left_mono]]]])
            using n v_e_nz p p_nz
            by (auto simp:
              max_density_is_max[unfolded density_def, OF finite finite nonempty wellformed subgraph_refl]
              max_density_gr_zero[OF finite nonempty wellformed])
          also have "\<dots> = (real n powr -(1 / max_density H) * (1 / p n powr 1)) powr ?e"
            by (simp add: powr_minus_divide[symmetric])
          also have "\<dots> = (real n powr -(1 / max_density H) / p n) powr ?e"
            using p p_nz by simp
          also have "\<dots> = (subgraph_threshold H n / p n) powr ?e"
            unfolding subgraph_threshold_def ..
          finally show "1 / (real n ^ ?v * p n ^ ?e) \<le> (subgraph_threshold H n / p n) powr ?e" .
        next
          show "(\<lambda>n. (subgraph_threshold H n / p n) powr real (card (uedges H))) \<longlonglongrightarrow> 0"
            using p_threshold p_nz v_e_nz
              by (auto simp: subgraph_threshold_def divide_nonneg_pos intro!: tendsto_zero_powrI)
        qed
      hence "(\<lambda>n. ?v ^ ?v * (1 / (real n ^ ?v * p n ^ ?e))) \<longlonglongrightarrow> real (?v ^ ?v) * 0"
        by (rule LIMSEQ_const_mult)
      thus "(\<lambda>n. ?v ^ ?v * (1 / (real n ^ ?v * p n ^ ?e))) \<longlonglongrightarrow> 0"
        by simp
    next
      show "\<forall>\<^sup>\<infinity>n. 0 \<le> 1 / prob_space_with_indicators.\<mu> (MGn p n) (?I n) (?A n)"
        by (rule eventually_sequentiallyI[OF less_imp_le[OF divide_pos_pos[OF _ prob_space_with_indicators.\<mu>_non_zero[OF facts(2)]]]]) simp+
    next
      show "\<forall>\<^sup>\<infinity>n. 1 / prob_space_with_indicators.\<mu> (MGn p n) (?I n) (?A n) \<le> ?v ^ ?v * (1 / (real n ^ ?v * p n ^ ?e))"
        using facts(7) by (rule eventually_sequentiallyI)
    qed
  moreover have "(\<lambda>n. prob_space_with_indicators.\<Delta>\<^sub>d (MGn p n) (?I n) (?A n)) \<lless> (\<lambda>n. (prob_space_with_indicators.\<mu> (MGn p n) (?I n) (?A n))^2)"
    proof (rule less_fun_bounds)
      let ?num = "\<lambda>n k. ?v ^ k * (real n ^ (2 * ?v - k) * p n powr (2 * ?e - max_density H * k))"
      let ?den = "\<lambda>n. ((1 / ?v ^ ?v) * (real n ^ ?v * p n ^ ?e))^2"

      \<comment> \<open>We have to show that a sum is asymptotically smaller than a constant term. We do that by
           showing that each summand is asymptotically smaller than the term.\<close>
      {
        fix k
        assume k: "k \<in> {1..?v}"
        let ?den' = "\<lambda>n. (1 / ?v ^ ?v)^2 * (real n ^ (2 * ?v) * p n ^ (2 * ?e))"
        have den': "?den' = ?den"
          by (subst power_mult_distrib) (simp add: power_mult_distrib power_even_eq)

        have "(\<lambda>n. ?num n k) \<lless> ?den'"
          proof (rule less_fun_const_quot)
            have "(\<lambda>n. (subgraph_threshold H n / p n) powr (max_density H * k)) \<longlonglongrightarrow> 0"
              using p_threshold mult_pos_pos[OF max_density_gr_zero[OF finite nonempty wellformed]] p_nz k
               by (auto simp: subgraph_threshold_def divide_nonneg_pos intro!: tendsto_zero_powrI)
            thus "(\<lambda>n. (real n ^ (2 * ?v - k) * p n powr (2 * ?e - max_density H * k)) / (real n ^ (2 * ?v) * p n ^ (2 * ?e))) \<longlonglongrightarrow> 0"
              proof (rule LIMSEQ_cong[OF _ eventually_sequentiallyI])
                fix n :: nat
                assume n: "1 \<le> n"
                have "(real n ^ (2 * ?v - k) * p n powr (2 * ?e - max_density H * k)) / (real n ^ (2 * ?v) * p n ^ (2 * ?e)) =
                      (n powr (2 * ?v - k) * p n powr (2 * ?e - max_density H * k)) / (n powr (2 * ?v) * p n powr (2 * ?e))" (is "?lhs = _")
                  using n p_nz by (simp add: powr_realpow[symmetric])
                also have "\<dots> = (n powr (2 * ?v - k) / n powr (2 * ?v)) * (p n powr (2 * ?e - max_density H * k) / (p n powr (2 * ?e)))"
                  by simp
                also have "\<dots> = (n powr (real (2 * ?v - k) - 2 * ?v)) * p n powr ((2 * ?e - max_density H * k) - (2 * ?e))"
                  by (simp add: powr_diff [symmetric] )
                also have "\<dots> = n powr -real k * p n powr ((2 * ?e - max_density H * k) - (2 * ?e))"
                  apply (rule arg_cong[where y = "- real k"])
                  using k by fastforce
                also have "\<dots> = n powr -real k * p n powr - (max_density H * k)"
                  by simp
                also have "\<dots> = (n powr -(1 / max_density H)) powr (max_density H * k) * p n powr - (max_density H * k)"
                  using max_density_gr_zero[OF finite nonempty wellformed] by (simp add: powr_powr)
                also have "\<dots> = (n powr -(1 / max_density H)) powr (max_density H * k) * (p n powr -1) powr (max_density H * k)"
                  by (simp add: powr_powr)
                also have "\<dots> = (n powr -(1 / max_density H) * p n powr -1) powr (max_density H * k)"
                  by (simp add: powr_mult)
                also have "\<dots> = (n powr -(1 / max_density H) * (1 / p n powr 1)) powr (max_density H * k)"
                  by (simp add: powr_minus_divide[symmetric])
                also have "\<dots> = (n powr -(1 / max_density H) / p n) powr (max_density H * k)"
                  by (simp add: p p_nz)
                also have "\<dots> = (subgraph_threshold H n / p n) powr (max_density H * k)" (is "_ = ?rhs")
                  unfolding subgraph_threshold_def ..
                finally have "?lhs = ?rhs"
                  .
                thus "?rhs = ?lhs"
                  by simp
              qed
          next
            show "(1 / ?v ^ ?v)^2 \<noteq> 0"
              using vpowv_inv_gr_z by auto
          qed

        hence "(\<lambda>n. ?num n k) \<lless> ?den"
          by (rule subst[OF den'])
      }
      hence "(\<lambda>n. \<Sum>k = 1..?v. ?num n k / ?den n) \<longlonglongrightarrow> (\<Sum>k = 1..?v. 0)"
        by (rule tendsto_sum)
      hence "(\<lambda>n. \<Sum>k = 1..?v. ?num n k / ?den n) \<longlonglongrightarrow> 0"
        by simp
      moreover have "(\<lambda>n. \<Sum>k = 1..?v. ?num n k / ?den n) = (\<lambda>n. (\<Sum>k = 1..?v. ?num n k) / ?den n)"
        by (simp add: sum_left_div_distrib)
      ultimately show "(\<lambda>n. \<Sum>k = 1..?v. ?num n k) \<lless> ?den"
        by metis

      show "\<forall>\<^sup>\<infinity>n. prob_space_with_indicators.\<Delta>\<^sub>d (MGn p n) (?I n) (?A n) \<le> (\<Sum>k = 1..?v. ?num n k)"
        using facts(8) by (rule eventually_sequentiallyI)

      show "\<forall>\<^sup>\<infinity>n. ?den n \<le> (prob_space_with_indicators.\<mu> (MGn p n) (?I n) (?A n))^2"
        using facts(5) facts(6) by (rule eventually_sequentiallyI[OF power_mono[OF _ less_imp_le]])

      show "\<forall>\<^sup>\<infinity>n. 0 \<le> prob_space_with_indicators.\<Delta>\<^sub>d (MGn p n) (?I n) (?A n)"
        using facts(2) by (rule eventually_sequentiallyI[OF prob_space_with_indicators.\<Delta>\<^sub>d_nonneg])

      show "\<forall>\<^sup>\<infinity>n. 0 < (prob_space_with_indicators.\<mu> (MGn p n) (?I n) (?A n))^2"
        using facts(2) by (rule eventually_sequentiallyI[OF prob_space_with_indicators.\<mu>_sq_non_zero])

      show "\<forall>\<^sup>\<infinity>n. 0 < ?den n"
        using facts(6) by (rule eventually_sequentiallyI[OF zero_less_power])
    qed
  ultimately have "(\<lambda>n.
      1 / prob_space_with_indicators.\<mu> (MGn p n) (?I n) (?A n) +
      prob_space_with_indicators.\<Delta>\<^sub>d (MGn p n) (?I n) (?A n) / (prob_space_with_indicators.\<mu> (MGn p n) (?I n) (?A n))^2
    ) \<longlonglongrightarrow> 0"
    by (subst add_0_left[where a = 0, symmetric]) (rule tendsto_add)

  \<comment> \<open>By now, we can actually perform the reduction mentioned above.\<close>
  hence "(\<lambda>n. probGn p n (\<lambda>es. \<not> H \<sqsubseteq> edge_space.edge_ugraph n es)) \<longlonglongrightarrow> 0"
    proof (rule LIMSEQ_le_zero)
      show "\<forall>\<^sup>\<infinity>n. 0 \<le> probGn p n (\<lambda>es. \<not> H \<sqsubseteq> edge_space.edge_ugraph n es)"
        by (rule eventually_sequentiallyI) (rule measure_nonneg)
    next
      show "\<forall>\<^sup>\<infinity>n.
        probGn p n (\<lambda>es. \<not> H \<sqsubseteq> edge_space.edge_ugraph n es) \<le>
          1 / prob_space_with_indicators.\<mu> (MGn p n) (?I n) (?A n) +
          prob_space_with_indicators.\<Delta>\<^sub>d (MGn p n) (?I n) (?A n) / (prob_space_with_indicators.\<mu> (MGn p n) (?I n) (?A n))^2"
        by (rule eventually_sequentiallyI[OF facts(4)])
    qed
  hence "(\<lambda>n. 1 - probGn p n (\<lambda>es. \<not> H \<sqsubseteq> edge_space.edge_ugraph n es)) \<longlonglongrightarrow> 1"
    using tendsto_diff[OF tendsto_const] by fastforce
  thus "prob_in_class p {G. H \<sqsubseteq> G} \<longlonglongrightarrow> 1"
    by (rule LIMSEQ_cong[OF _ eventually_sequentiallyI[OF facts(3)]])
qed

end
