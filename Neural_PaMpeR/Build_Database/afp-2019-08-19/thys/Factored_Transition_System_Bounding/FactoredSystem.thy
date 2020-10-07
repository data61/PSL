theory FactoredSystem
  imports Main "HOL-Library.Finite_Map" "HOL-Library.Sublist" FSSublist
    FactoredSystemLib ListUtils HoArithUtils FmapUtils
begin


section "Factored System"

\<comment> \<open>NOTE hide the '++' operator from 'Map' to prevent warnings.\<close>
hide_const (open) Map.map_add
no_notation Map.map_add (infixl "++" 100)


subsection "Semantics of Plan Execution"

text \<open> This section aims at characterizing the semantics of executing plans---i.e. sequences
of actions---on a given initial state.

The semantics of action execution were previously introduced
via the notion of succeding state (`state\_succ`). Plan execution (`exec\_plan`) extends this notion
to sequences of actions by calculating the succeding state from the given state and action pair and
then recursively executing the remaining actions on the succeding state. [Abdulaziz et al., HOL4
Definition 3, p.9] \<close>


lemma state_succ_pair: "state_succ s (p, e) = (if (p \<subseteq>\<^sub>f s) then (e ++ s) else s)"
  by (simp add: state_succ_def)


\<comment> \<open>NOTE shortened to 'exec\_plan'\<close>
\<comment> \<open>NOTE using 'fun' because of multiple definining equations.\<close>
\<comment> \<open>NOTE first argument was curried.\<close>
fun exec_plan where
  "exec_plan s [] = s"
| "exec_plan s (a # as) = exec_plan (state_succ s a) as"


lemma exec_plan_Append:
  fixes as_a as_b s
  shows "exec_plan s (as_a @ as_b) = exec_plan (exec_plan s as_a) as_b"
  by (induction as_a arbitrary: s as_b) auto


text \<open> Plan execution effectively eliminates cycles: i.e., if a given plan `as` may be partitioned
into plans `as1`, `as2` and `as3`, s.t. the sequential execution of `as1` and `as2` yields the same
state, `as2` may be skipped during plan execution. \<close>

lemma cycle_removal_lemma:
  fixes as1 as2 as3
  assumes "(exec_plan s (as1 @ as2) = exec_plan s as1)"
  shows "(exec_plan s (as1 @ as2 @ as3) = exec_plan s (as1 @ as3))"
  using assms exec_plan_Append
  by metis


subsubsection "Characterization of the Set of Possible States"

text \<open> To show the construction principle of the set of possible states---in lemma
`construction\_of\_all\_possible\_states\_lemma`---the following ancillary proves of finite map
properties are required.

Most importantly, in lemma `fmupd\_fmrestrict\_subset` we show how finite mappings `s` with domain
@{term "{v} \<union> X"} and `s v = (Some x)` are constructed from their restrictions to `X` via update, i.e.

  s = fmupd v x (fmrestrict\_set X s)

This is used in lemma `construction\_of\_all\_possible\_states\_lemma` to show that the set of possible
states for variables @{term "{v} \<union> X"} is constructed inductively from the set of all possible states for
variables `X` via update on point @{term "v \<notin> X"}.
\<close>

\<comment> \<open>NOTE added lemma.\<close>
lemma empty_domain_fmap_set: "{s. fmdom' s = {}} = {fmempty}"
proof -
  let ?A = "{s. fmdom' s = {}}"
  let ?B = "{fmempty}"
  fix s
  show ?thesis proof(rule ccontr)
    assume C: "?A \<noteq> ?B"
    then show False proof -
      {
        assume C1: "?A \<subset> ?B"
        have "?A = {}" using C1 by force
        then have False using fmdom'_empty by blast
      }
      moreover
      {
        assume C2: "\<not>(?A \<subset> ?B)"
        then have "fmdom' fmempty = {}"
          by auto
        moreover have "fmempty \<in> ?A"
          by auto
        moreover have "?A \<noteq> {}"
          using calculation(2) by blast
        moreover have "\<forall>a\<in>?A.a\<notin>?B"
          by (metis (mono_tags, lifting)
              C Collect_cong calculation(1) fmrestrict_set_dom fmrestrict_set_null singleton_conv)
        moreover have "fmempty \<in> ?B" by auto
        moreover have "\<exists>a\<in>?A.a\<in>?B"
          by simp
        moreover have "\<not>(\<forall>a\<in>?A.a\<notin>?B)"
          by simp
        ultimately have False
          by blast
      }
      ultimately show False
        by fastforce
    qed
  qed
qed

\<comment> \<open>NOTE added lemma.\<close>
lemma possible_states_set_ii_a:
  fixes s x v
  assumes "(v \<in> fmdom' s)"
  shows "(fmdom' ((\<lambda>s. fmupd v x s) s) = fmdom' s)"
  using assms insert_absorb
  by auto

\<comment> \<open>NOTE added lemma.\<close>
lemma possible_states_set_ii_b:
  fixes s x v
  assumes "(v \<notin> fmdom' s)"
  shows "(fmdom' ((\<lambda>s. fmupd v x s) s) = fmdom' s \<union> {v})"
  by auto

\<comment> \<open>NOTE added lemma.\<close>
lemma fmap_neq:
  fixes s :: "('a, bool) fmap" and s' :: "('a, bool) fmap"
  assumes "(fmdom' s = fmdom' s')"
  shows "((s \<noteq> s') \<longleftrightarrow> (\<exists>v\<in>(fmdom' s). fmlookup s v \<noteq> fmlookup s' v))"
  using assms fmap_ext fmdom'_notD
  by metis

\<comment> \<open>NOTE added lemma.\<close>
lemma fmdom'_fmsubset_restrict_set:
  fixes X1 X2 and s :: "('a, bool) fmap"
  assumes "X1 \<subseteq> X2" "fmdom' s = X2"
  shows "fmdom' (fmrestrict_set X1 s) = X1"
  using assms
  by (metis (no_types, lifting)
      antisym_conv fmdom'_notD fmdom'_notI fmlookup_restrict_set rev_subsetD subsetI)


\<comment> \<open>NOTE added lemma.\<close>
lemma fmsubset_restrict_set:
  fixes X1 X2 and s :: "'a state"
  assumes "X1 \<subseteq> X2" "s \<in> {s. fmdom' s = X2}"
  shows "fmrestrict_set X1 s \<in> {s. fmdom' s = X1}"
  using assms fmdom'_fmsubset_restrict_set
  by blast

\<comment> \<open>NOTE added lemma.\<close>
lemma fmupd_fmsubset_restrict_set:
  fixes X v x and s :: "'a state"
  assumes "s \<in> {s. fmdom' s = insert v X}" "fmlookup s v = Some x"
  shows "s = fmupd v x (fmrestrict_set X s)"
proof -
  \<comment> \<open>Show that domains of 's' and 'fmupd v x (fmrestrict\_set X s)' are identical.\<close>
  have 1: "fmdom' s = insert v X"
    using assms(1)
    by simp
  {
    have "X \<subseteq> insert v X"
      by auto
    then have "fmdom' (fmrestrict_set X s) = X"
      using 1 fmdom'_fmsubset_restrict_set
      by metis
    then have "fmdom' (fmupd v x (fmrestrict_set X s)) = insert v X"
      using assms(1) fmdom'_fmupd
      by auto
  }
  note 2 = this
  moreover
  {
    fix w
      \<comment> \<open>Show case for undefined variables (where lookup yields 'None').\<close>
    {
      assume "w \<notin> insert v X"
      then have "w \<notin> fmdom' s" "w \<notin> fmdom' (fmupd v x (fmrestrict_set X s))"
        using 1 2
        by argo+
      then have "fmlookup s w = fmlookup (fmupd v x (fmrestrict_set X s)) w"
        using fmdom'_notD
        by metis
    }
      \<comment> \<open>Show case for defined variables (where lookup yields 'Some y').\<close>
    moreover {
      assume "w \<in> insert v X"
      then have "w \<in> fmdom' s" "w \<in> fmdom' (fmupd v x (fmrestrict_set X s))"
        using 1 2
        by argo+
      then have "fmlookup s w = fmlookup (fmupd v x (fmrestrict_set X s)) w"
        by (cases "w = v")
          (auto simp add: assms calculation)
    }
    ultimately have "fmlookup s w = fmlookup (fmupd v x (fmrestrict_set X s)) w"
      by blast
  }
  then show ?thesis
    using fmap_ext
    by blast
qed

lemma construction_of_all_possible_states_lemma:
  fixes v X
  assumes "(v \<notin> X)"
  shows "({s. fmdom' s = insert v X}
    = ((\<lambda>s. fmupd v True s) ` {s. fmdom' s = X})
      \<union> ((\<lambda>s. fmupd v False s) ` {s. fmdom' s = X})
  )"
proof -
  fix v X
  let ?A = "{s :: 'a state. fmdom' s = insert v X}"
  let ?B = "
    ((\<lambda>s. fmupd v True s) ` {s :: 'a state. fmdom' s = X})
    \<union> ((\<lambda>s. fmupd v False s) ` {s :: 'a state. fmdom' s = X})
  "
  text \<open>Show the goal by mutual inclusion. The inclusion @{term "?B \<subseteq> ?A"} is trivial and can be solved by
    automation. For the complimentary proof @{term "?A \<subseteq> ?B"} however we need to do more work.
    In our case we choose a proof by contradiction and show that an @{term "s \<in> ?A"} which is not also in
    '?B' cannot exist.\<close>
  {
    have "?A \<subseteq> ?B" proof(rule ccontr)
      assume C: "\<not>(?A \<subseteq> ?B)"
      moreover have "\<exists>s\<in>?A. s\<notin>?B"
        using C
        by auto
      moreover obtain s where obtain_s: "s\<in>?A \<and> s\<notin>?B"
        using calculation
        by auto
      moreover have "s\<notin>?B"
        using obtain_s
        by auto
      moreover have "fmdom' s = X \<union> {v}"
        using obtain_s
        by auto
      moreover have "\<forall>s'\<in>?B. fmdom' s' = X \<union> {v}"
        by auto
      moreover have
        "(s \<notin> ((\<lambda>s. fmupd v True s) ` {s. fmdom' s = X}))"
        "(s \<notin> ((\<lambda>s. fmupd v False s) ` {s. fmdom' s = X}))"
        using obtain_s
        by blast+
      text \<open> Show that every state @{term "s \<in> ?A"} has been constructed from another state with domain
        'X'. \<close>
      moreover
      {
        fix s :: "'a state"
        assume 1: "s \<in> {s :: 'a state. fmdom' s = insert v X}"
        then have "fmrestrict_set X s \<in> {s :: 'a state. fmdom' s = X}"
          using subset_insertI fmsubset_restrict_set
          by metis
        moreover
        {
          assume "fmlookup s v = Some True"
          then have "s = fmupd v True (fmrestrict_set X s)"
            using 1 fmupd_fmsubset_restrict_set
            by metis
        }
        moreover {
          assume "fmlookup s v = Some False"
          then have "s = fmupd v False (fmrestrict_set X s)"
            using 1 fmupd_fmsubset_restrict_set
            by fastforce
        }
        moreover have "fmlookup s v \<noteq> None"
          using 1 fmdom'_notI
          by fastforce
        ultimately have "
          (s \<in> ((\<lambda>s. fmupd v True s) ` {s. fmdom' s = X}))
          \<or> (s \<in> ((\<lambda>s. fmupd v False s) ` {s. fmdom' s = X}))
        "
          by force
      }
      ultimately show False
        by meson
    qed
  }
  moreover have "?B \<subseteq> ?A"
    by force
  ultimately show "?A = ?B" by blast
qed


text \<open> Another important property of the state set is cardinality, i.e. the number of distinct
states which can be modelled using a given finite variable set.

As lemma `card\_of\_set\_of\_all\_possible\_states` shows, for a finite variable set `X`, the number of
possible states is `2 \^ card X`, i.e. the number of assigning two discrete values to `card X` slots
as known from combinatorics.

Again, some additional properties of finite maps had to be proven. Pivotally, in lemma
`updates\_disjoint`, it is shown that the image of updating a set of states with domain `X` on a
point @{term "x \<notin> X"} with either `True` or `False` yields two distinct sets of states with domain
@{term "{x} \<union> X"}. \<close>

\<comment> \<open>NOTE goal has to stay implication otherwise induction rule won't watch.\<close>
lemma FINITE_states:
  fixes X :: "'a set"
  shows "finite X \<Longrightarrow> finite {(s :: 'a state). fmdom' s = X}"
proof (induction  rule: finite.induct)
  case emptyI
  then have "{s. fmdom' s  = {}} = {fmempty}"
    by (simp add: empty_domain_fmap_set)
  then show ?case
    by (simp add: \<open>{s. fmdom' s = {}} = {fmempty}\<close>)
next
  case (insertI A a)
  assume P1: "finite A"
    and P2: "finite {s. fmdom' s = A}"
  then show ?case
  proof (cases "a \<in> A")
    case True
    then show ?thesis
      using insertI.IH insert_Diff
      by fastforce
  next
    case False
    then show ?thesis
    proof -
      have "finite (
          ((\<lambda>s. fmupd a True s) ` {s. fmdom' s = A})
            \<union> ((\<lambda>s. fmupd a False s) ` {s. fmdom' s = A}))"
        using False construction_of_all_possible_states_lemma insertI.IH
        by blast
      then show ?thesis
        using False construction_of_all_possible_states_lemma
        by fastforce
    qed
  qed
qed

\<comment> \<open>NOTE added lemma.\<close>
lemma bool_update_effect:
  fixes s X x v b
  assumes "finite X" "s \<in> {s :: 'a state. fmdom' s = X}" "x \<in> X" "x \<noteq> v"
  shows "fmlookup ((\<lambda>s :: 'a state. fmupd v b s) s) x = fmlookup s x"
  using assms fmupd_lookup
  by auto

\<comment> \<open>NOTE added lemma.\<close>
lemma bool_update_inj:
  fixes X :: "'a set" and v b
  assumes "finite X" "v \<notin> X"
  shows "inj_on (\<lambda>s. fmupd v b s) {s :: 'a state. fmdom' s = X}"
proof -
  let ?f = "\<lambda>s :: 'a state. fmupd v b s"
  {
    fix s1 s2 :: "'a state"
    assume "s1 \<in> {s :: 'a state. fmdom' s = X}" "s2 \<in> {s :: 'a state. fmdom' s = X}"
      "?f s1 = ?f s2"
    moreover
    {
      have
        "\<forall>x\<in>X. x \<noteq> v \<longrightarrow> fmlookup (?f s1) x = fmlookup s1 x"
        "\<forall>x\<in>X. x \<noteq> v \<longrightarrow> fmlookup (?f s2) x = fmlookup s2 x"
        by simp+
      then have
        "\<forall>x\<in>X. x \<noteq> v \<longrightarrow> fmlookup s1 x = fmlookup s2 x"
        using calculation(3)
        by auto
    }
    moreover have "fmlookup s1 v = fmlookup s2 v"
      using calculation \<open>v \<notin> X\<close>
      by force
    ultimately have "s1 = s2"
      using fmap_neq
      by fastforce
  }
  then show "inj_on (\<lambda>s. fmupd v b s) {s :: 'a state. fmdom' s = X}"
    using inj_onI
    by blast
qed

\<comment> \<open>NOTE added lemma.\<close>
lemma card_update:
  fixes X v b
  assumes "finite (X :: 'a set)" "v \<notin> X"
  shows "
    card ((\<lambda>s. fmupd v b s) ` {s :: 'a state. fmdom' s = X})
    = card {s :: 'a state. fmdom' s = X}
  "
proof -
  have "inj_on (\<lambda>s. fmupd v b s) {s :: 'a state. fmdom' s = X}"
    using assms bool_update_inj
    by fast
  then show
    "card ((\<lambda>s. fmupd v b s) ` {s :: 'a state. fmdom' s = X}) = card {s :: 'a state. fmdom' s = X}"
    using card_image by blast
qed

\<comment> \<open>NOTE added lemma.\<close>
lemma updates_disjoint:
  fixes X x
  assumes "finite X" "x \<notin> X"
  shows "
    ((\<lambda>s. fmupd x True s) ` {s. fmdom' s = X})
    \<inter> ((\<lambda>s. fmupd x False s) ` {s. fmdom' s = X}) = {}
  "
proof -
  let ?A = "((\<lambda>s. fmupd x True s) ` {s. fmdom' s = X})"
  let ?B = "((\<lambda>s. fmupd x False s) ` {s. fmdom' s = X})"
  {
    assume C: "\<not>(\<forall>a\<in>?A. \<forall>b\<in>?B. a \<noteq> b)"
    then have
      "\<forall>a\<in>?A. \<forall>b\<in>?B. fmlookup a x \<noteq> fmlookup b x"
      by simp
    then have "\<forall>a\<in>?A. \<forall>b\<in>?B. a \<noteq> b"
      by blast
    then have False
      using C
      by blast
  }
  then show "?A \<inter> ?B = {}"
    using disjoint_iff_not_equal
    by blast
qed


lemma card_of_set_of_all_possible_states:
  fixes X :: "'a set"
  assumes "finite X"
  shows "card {(s :: 'a state). fmdom' s = X} = 2 ^ (card X)"
  using assms
proof (induction X)
  case empty
  then have 1: "{s :: 'a state. fmdom' s = {}} = {fmempty}"
    using empty_domain_fmap_set
    by simp
  then have "card {fmempty} = 1"
    using is_singleton_altdef
    by blast
  then have "2^(card {}) = 1"
    by auto
  then show ?case
    using 1
    by auto
next
  case (insert x F)
  then show ?case
    \<comment> \<open>TODO refactor and simplify proof further.\<close>
  proof (cases "x \<in> F")
    case True
    then show ?thesis
      using insert.hyps(2)
      by blast
  next
    case False
    then have "
        {s :: 'a state. fmdom' s = insert x F}
        = (\<lambda>s. fmupd x True s) ` {s. fmdom' s = F} \<union> (\<lambda>s. fmupd x False s) ` {s. fmdom' s = F}
      "
      using False construction_of_all_possible_states_lemma
      by metis
    then have 2: "
        card ({s :: 'a state. fmdom' s = insert x F})
        = card ((\<lambda>s. fmupd x True s) ` {s. fmdom' s = F} \<union> (\<lambda>s. fmupd x False s) ` {s. fmdom' s = F})
      "
      by argo
    then have 3: "2^(card (insert x F)) = 2 * 2^(card F)"
      using False insert.hyps(1)
      by simp
    then have
      "card ((\<lambda>s. fmupd x True s) ` {s. fmdom' s = F}) = 2^(card F)"
      "card ((\<lambda>s. fmupd x False s) ` {s. fmdom' s = F}) = 2^(card F)"
      using False card_update insert.IH insert.hyps(1)
      by metis+
    moreover have "
          ((\<lambda>s. fmupd x True s) ` {s. fmdom' s = F})
          \<inter> ((\<lambda>s. fmupd x False s) ` {s. fmdom' s = F})
        = {}
      "
      using False insert.hyps(1) updates_disjoint
      by metis
    moreover have "card (
          ((\<lambda>s. fmupd x True s) ` {s. fmdom' s = F})
          \<union> ((\<lambda>s. fmupd x False s) ` {s. fmdom' s = F})
        )
        = card (((\<lambda>s. fmupd x True s) ` {s. fmdom' s = F}))
          + card ((\<lambda>s. fmupd x False s) ` {s. fmdom' s = F})
      "
      using calculation card_Un_disjoint card_infinite
        power_eq_0_iff rel_simps(76)
      by metis
    then have "card (
          ((\<lambda>s. fmupd x True s) ` {s. fmdom' s = F})
          \<union> ((\<lambda>s. fmupd x False s) ` {s. fmdom' s = F})
        )
        = 2 * (2^(card F))"
      using calculation(1, 2)
      by presburger
    then have "card (
          ((\<lambda>s. fmupd x True s) ` {s. fmdom' s = F})
          \<union> ((\<lambda>s. fmupd x False s) ` {s. fmdom' s = F})
        )
        = 2^(card (insert x F))"
      using insert.IH 3
      by metis
    then show ?thesis
      using "2"
      by argo
  qed
qed


subsubsection "State Lists and State Sets"


\<comment> \<open>NOTE using fun because of two defining equations.\<close>
\<comment> \<open>NOTE paired argument replaced by currying.\<close>
fun state_list where
  "state_list s [] = [s]"
| "state_list s (a # as) = s # state_list (state_succ s a) as"


lemma empty_state_list_lemma:
  fixes as s
  shows "\<not>([] = state_list s as)"
proof (induction as)
qed auto


lemma state_list_length_non_zero:
  fixes as s
  shows "\<not>(0 = length (state_list s as))"
proof (induction as)
qed auto


lemma state_list_length_lemma:
  fixes as s
  shows "length as = length (state_list s as) - 1"
proof (induction as arbitrary: s)
next case (Cons a as)
  have "length (state_list s (Cons a as)) - 1 =  length (state_list (state_succ s a) as)"
    by auto
      \<comment> \<open>TODO unwrap metis proof.\<close>
  then show "length (Cons a as) = length (state_list s (Cons a as)) - 1"
    by (metis Cons.IH Suc_diff_1 empty_state_list_lemma length_Cons length_greater_0_conv)
qed simp


lemma state_list_length_lemma_2:
  fixes as s
  shows "(length (state_list s as)) = (length as + 1)"
proof (induction as arbitrary: s)
qed auto


\<comment> \<open>NOTE using fun because of multiple defining equations.\<close>
\<comment> \<open>NOTE name shortened to 'state\_def'\<close>
fun state_set where
  "state_set [] = {}"
| "state_set (s # ss) = insert [s] (Cons s ` (state_set ss))"


lemma state_set_thm:
  fixes s1
  shows "s1 \<in> state_set s2 \<longleftrightarrow> prefix s1 s2 \<and> s1 \<noteq> []"
proof -
  \<comment> \<open>NOTE Show equivalence by proving both directions. Left-to-right is trivial. Right-to-Left
  primarily involves exploiting the prefix premise, induction hypothesis  and  `state\_set`
  definition.\<close>
  have "s1 \<in> state_set s2 \<Longrightarrow> prefix s1 s2 \<and> s1 \<noteq> []"
    by (induction s2 arbitrary: s1) auto
  moreover {
    assume P: "prefix s1 s2" "s1 \<noteq> []"
    then have "s1 \<in> state_set s2"
    proof (induction s2 arbitrary: s1)
      case (Cons a s2)
      obtain s1' where 1: "s1 = a # s1'" "prefix s1' s2"
        using Cons.prems(1, 2) prefix_Cons
        by metis
      then show ?case proof (cases "s1' = []")
        case True
        then show ?thesis
          using 1
          by force
      next
        case False
        then have "s1' \<in> state_set s2"
          using 1 False Cons.IH
          by blast
        then show ?thesis
          using 1
          by fastforce
      qed
    qed simp
  }
  ultimately show "s1 \<in> state_set s2 \<longleftrightarrow> prefix s1 s2 \<and> s1 \<noteq> []"
    by blast
qed


lemma state_set_finite:
  fixes X
  shows "finite (state_set X)"
  by (induction X) auto


lemma LENGTH_state_set:
  fixes X e
  assumes "e \<in> state_set X"
  shows "length e \<le> length X"
  using assms
  by (induction X arbitrary: e) auto


lemma lemma_temp:
  fixes x s as h
  assumes "x \<in> state_set (state_list s as)"
  shows "length (h # state_list s as) > length x"
  using assms LENGTH_state_set le_imp_less_Suc
  by force


lemma NIL_NOTIN_stateset:
  fixes X
  shows "[] \<notin> state_set X"
  by (induction X) auto


\<comment> \<open>NOTE added lemma.\<close>
lemma state_set_card_i:
  fixes X a
  shows "[a] \<notin> (Cons a ` state_set X)"
  by (induction X) auto

\<comment> \<open>NOTE added lemma.\<close>
lemma state_set_card_ii:
  fixes X a
  shows "card (Cons a ` state_set X) = card (state_set X)"
proof -
  have "inj_on (Cons a) (state_set X)"
    by simp
  then show ?thesis
    using card_image
    by blast
qed

\<comment> \<open>NOTE added lemma.\<close>
lemma state_set_card_iii:
  fixes X a
  shows "card (state_set (a # X)) = 1 + card (state_set X)"
proof -
  have "card (state_set (a # X)) = card (insert [a] (Cons a ` state_set X))"
    by auto
      \<comment> \<open>TODO unwrap this metis step.\<close>
  also have "\<dots> = 1 + card (Cons a ` state_set X)"
    using state_set_card_i
    by (metis Suc_eq_plus1_left card_insert_disjoint finite_imageI state_set_finite)
  also have"\<dots> = 1 + card (state_set X)"
    using state_set_card_ii
    by metis
  finally show "card (state_set (a # X)) = 1 + card (state_set X)"
    by blast
qed

lemma state_set_card:
  fixes X
  shows "card (state_set X) = length X"
proof (induction X)
  case (Cons a X)
  then have "card (state_set (a # X)) = 1 + card (state_set X)"
    using state_set_card_iii
    by fast
  then show ?case
    using Cons
    by fastforce
qed auto


subsubsection "Properties of Domain Changes During Plan Execution"


lemma FDOM_state_succ:
  assumes "fmdom' (snd a) \<subseteq> fmdom' s"
  shows "(fmdom' (state_succ s a) = fmdom' s)"
  unfolding state_succ_def fmap_add_ltr_def
  using assms
  by force


lemma FDOM_state_succ_subset:
  "fmdom' (state_succ s a) \<subseteq> (fmdom' s \<union> fmdom' (snd a))"
  unfolding state_succ_def fmap_add_ltr_def
  by simp


\<comment> \<open>NOTE definition `qispl\_then` removed (was not being used).\<close>


lemma FDOM_eff_subset_FDOM_valid_states:
  fixes p e s
  assumes "(p, e) \<in> PROB" "(s \<in> valid_states PROB)"
  shows "(fmdom' e \<subseteq> fmdom' s)"
proof -
  {
    have "fmdom' e \<subseteq> action_dom p e"
      unfolding action_dom_def
      by blast
    also have "\<dots> \<subseteq> prob_dom PROB"
      unfolding action_dom_def prob_dom_def
      using assms(1)
      by blast
    finally have "fmdom' e \<subseteq> fmdom' s"
      using assms
      by (auto simp: valid_states_def)
  }
  then show "fmdom' e \<subseteq> fmdom' s"
    by simp
qed


lemma FDOM_eff_subset_FDOM_valid_states_pair:
  fixes a s
  assumes "a \<in> PROB" "s \<in> valid_states PROB"
  shows "fmdom' (snd a) \<subseteq> fmdom' s"
proof -
  {
    have "fmdom' (snd a) \<subseteq> (\<lambda>(s1, s2). action_dom s1 s2) a"
      unfolding action_dom_def
      using case_prod_beta
      by fastforce
    also have "\<dots> \<subseteq> prob_dom PROB"
      using assms(1) prob_dom_def Sup_upper
      by fast
    finally have "fmdom' (snd a) \<subseteq> fmdom' s"
      using assms(2) valid_states_def
      by fast
  }
  then show ?thesis
    by simp
qed


lemma FDOM_pre_subset_FDOM_valid_states:
  fixes p e s
  assumes "(p, e) \<in> PROB" "s \<in> valid_states PROB"
  shows "fmdom' p \<subseteq> fmdom' s"
proof -
  {
    have "fmdom' p \<subseteq> (\<lambda>(s1, s2). action_dom s1 s2) (p, e)"
      using action_dom_def
      by fast
    also have "\<dots> \<subseteq> prob_dom PROB"
      using assms(1)
      by (simp add: Sup_upper pair_imageI prob_dom_def)
    finally have "fmdom' p \<subseteq> fmdom' s"
      using assms(2) valid_states_def
      by fast
  }
  then show ?thesis
    by simp
qed


lemma FDOM_pre_subset_FDOM_valid_states_pair:
  fixes a s
  assumes "a \<in> PROB" "s \<in> valid_states PROB"
  shows "fmdom' (fst a) \<subseteq> fmdom' s"
proof -
  {
    have "fmdom' (fst a) \<subseteq> (\<lambda>(s1, s2). action_dom s1 s2) a"
      using action_dom_def
      by force
    also have "\<dots> \<subseteq> prob_dom PROB"
      using assms(1)
      by (simp add: Sup_upper pair_imageI prob_dom_def)
    finally have "fmdom' (fst a) \<subseteq> fmdom' s"
      using assms(2) valid_states_def
      by fast
  }
  then show ?thesis
    by simp
qed


\<comment> \<open>TODO unwrap the simp proof.\<close>
lemma action_dom_subset_valid_states_FDOM:
  fixes p e s
  assumes "(p, e) \<in> PROB" "s \<in> valid_states PROB"
  shows "action_dom p e \<subseteq> fmdom' s"
  using assms
  by (simp add: Sup_upper pair_imageI prob_dom_def valid_states_def)


\<comment> \<open>TODO unwrap the metis proof.\<close>
lemma FDOM_eff_subset_prob_dom:
  fixes p e
  assumes "(p, e) \<in> PROB"
  shows "fmdom' e \<subseteq> prob_dom PROB"
  using assms
  by (metis Sup_upper Un_subset_iff action_dom_def pair_imageI prob_dom_def)


lemma FDOM_eff_subset_prob_dom_pair:
  fixes a
  assumes "a \<in> PROB"
  shows "fmdom' (snd a) \<subseteq> prob_dom PROB"
  using assms(1) FDOM_eff_subset_prob_dom surjective_pairing
  by metis


\<comment> \<open>TODO unwrap metis proof.\<close>
lemma FDOM_pre_subset_prob_dom:
  fixes p e
  assumes "(p, e) \<in> PROB"
  shows "fmdom' p \<subseteq> prob_dom PROB"
  using assms
  by (metis (no_types) Sup_upper Un_subset_iff action_dom_def pair_imageI prob_dom_def)


lemma FDOM_pre_subset_prob_dom_pair:
  fixes a
  assumes "a \<in> PROB"
  shows "fmdom' (fst a) \<subseteq> prob_dom PROB"
  using assms FDOM_pre_subset_prob_dom surjective_pairing
  by metis


subsubsection "Properties of Valid Plans"


lemma valid_plan_valid_head:
  assumes "(h # as \<in> valid_plans PROB)"
  shows  "h \<in> PROB"
  using assms valid_plans_def
  by force


lemma valid_plan_valid_tail:
  assumes "(h # as \<in> valid_plans PROB)"
  shows "(as \<in> valid_plans PROB)"
  using assms
  by (simp add: valid_plans_def)


\<comment> \<open>TODO unwrap simp proof.\<close>
lemma valid_plan_pre_subset_prob_dom_pair:
  assumes "as \<in> valid_plans PROB"
  shows "(\<forall>a. ListMem a as \<longrightarrow> fmdom' (fst a) \<subseteq> (prob_dom PROB))"
  unfolding valid_plans_def
  using assms
  by (simp add: FDOM_pre_subset_prob_dom_pair ListMem_iff rev_subsetD valid_plans_def)


lemma valid_append_valid_suff:
  assumes "as1 @ as2 \<in> (valid_plans PROB)"
  shows "as2 \<in> (valid_plans PROB)"
  using assms
  by (simp add: valid_plans_def)


lemma valid_append_valid_pref:
  assumes "as1 @ as2 \<in> (valid_plans PROB)"
  shows "as1 \<in> (valid_plans PROB)"
  using assms
  by (simp add: valid_plans_def)


lemma valid_pref_suff_valid_append:
  assumes "as1 \<in> (valid_plans PROB)" "as2 \<in> (valid_plans PROB)"
  shows "(as1 @ as2) \<in> (valid_plans PROB)"
  using assms
  by (simp add: valid_plans_def)


\<comment> \<open>NOTE showcase (case split seems necessary for MP of IH but the original proof does not need it).\<close>
lemma MEM_statelist_FDOM:
  fixes PROB h as s0
  assumes "s0 \<in> (valid_states PROB)" "as \<in> (valid_plans PROB)" "ListMem h (state_list s0 as)"
  shows "(fmdom' h = fmdom' s0)"
  using assms
proof (induction as arbitrary: PROB h s0)
  case Nil
  have "h = s0"
    using Nil.prems(3) ListMem_iff
    by force
  then show ?case
    by simp
next
  case (Cons a as)
  then show ?case
    \<comment> \<open>NOTE This case split seems necessary to be able to infer

          'ListMem h (state\_list (state\_succ s0 a) as)'

        which is required in order to apply MP to the induction hypothesis.\<close>
  proof (cases "h = s0")
    case False
      \<comment> \<open>TODO proof steps could be refactored into auxillary lemmas.\<close>
    {
      have "a \<in> PROB"
        using Cons.prems(2) valid_plan_valid_head
        by fast
      then have "fmdom' (snd a) \<subseteq> fmdom' s0"
        using Cons.prems(1) FDOM_eff_subset_FDOM_valid_states_pair
        by blast
      then have "fmdom' (state_succ s0 a) = fmdom' s0"
        using FDOM_state_succ[of _ s0] Cons.prems(1) valid_states_def
        by presburger
    }
    note 1 = this
    {
      have "fmdom' s0 = prob_dom PROB"
        using Cons.prems(1) valid_states_def
        by fast
      then have "state_succ s0 a \<in> valid_states PROB"
        unfolding valid_states_def
        using 1
        by force
    }
    note 2 = this
    {
      have "ListMem h (state_list (state_succ s0 a) as)"
        using Cons.prems(3) False
        by (simp add: ListMem_iff)
    }
    note 3 = this
    {
      have "as \<in> valid_plans PROB"
        using Cons.prems(2) valid_plan_valid_tail
        by fast
      then have "fmdom' h = fmdom' (state_succ s0 a)"
        using 1 2 3 Cons.IH[of "state_succ s0 a"]
        by blast
    }
    then show ?thesis
      using 1
      by argo
  qed simp
qed


\<comment> \<open>TODO unwrap metis proof.\<close>
lemma MEM_statelist_valid_state:
  fixes PROB h as s0
  assumes "s0 \<in> valid_states PROB" "as \<in> valid_plans PROB" "ListMem h (state_list s0 as)"
  shows "(h \<in> valid_states PROB)"
  using assms
  by (metis MEM_statelist_FDOM mem_Collect_eq valid_states_def)


\<comment> \<open>TODO refactor (characterization lemma for 'state\_succ').\<close>
\<comment> \<open>TODO unwrap metis proof.\<close>
\<comment> \<open>NOTE added lemma.\<close>
lemma lemma_1_i:
  fixes s a PROB
  assumes "s \<in> valid_states PROB" "a \<in> PROB"
  shows "state_succ s a \<in> valid_states PROB"
  using assms
  by (metis FDOM_eff_subset_FDOM_valid_states_pair FDOM_state_succ mem_Collect_eq  valid_states_def)

\<comment> \<open>TODO unwrap smt proof.\<close>
\<comment> \<open>NOTE added lemma.\<close>
lemma lemma_1_ii:
  "last ` ((#) s ` state_set (state_list (state_succ s a) as))
  = last ` state_set (state_list (state_succ s a) as)"
  by (smt NIL_NOTIN_stateset image_cong image_image last_ConsR)

lemma lemma_1:
  fixes as :: "(('a, 'b) fmap \<times> ('a, 'b) fmap) list" and PPROB
  assumes "(s \<in> valid_states PROB)" "(as \<in> valid_plans PROB)"
  shows "((last ` (state_set (state_list s as))) \<subseteq> valid_states PROB)"
  using assms
proof (induction as arbitrary: s PROB)
  \<comment> \<open>NOTE Base case simplifies to @{term "{s} \<subseteq> valid_states PROB"} which itself follows directly from
    1st assumption.\<close>
  case (Cons a as)
  text \<open> Split the 'insert' term produced by @{term "state_set (state_list s (a # as))"} and proof
      inclusion in 'valid\_states PROB' for both parts. \<close>
  {
    \<comment> \<open>NOTE Inclusion of the first subset follows from the induction premise by simplification.
      The inclusion of the second subset is shown by applying the induction hypothesis to
      `state\_succ s a` and some elementary set simplifications.\<close>
    have "last [s] \<in> valid_states PROB"
      using Cons.prems(1)
      by simp
    moreover {
      {
        have "a \<in> PROB"
          using Cons.prems(2) valid_plan_valid_head
          by fast
        then have "state_succ s a \<in> valid_states PROB"
          using Cons.prems(1) lemma_1_i
          by blast
      }
      moreover have "as \<in> valid_plans PROB"
        using Cons.prems(2) valid_plan_valid_tail
        by fast
      then have "(last ` state_set (state_list (state_succ s a) as)) \<subseteq> valid_states PROB"
        using  calculation Cons.IH[of "state_succ s a"]
        by presburger
      then have "(last ` ((#) s ` state_set (state_list (state_succ s a) as))) \<subseteq> valid_states PROB"
        using lemma_1_ii
        by metis
    }
    ultimately have
      "(last ` insert [s] ((#) s ` state_set (state_list (state_succ s a) as))) \<subseteq> valid_states PROB"
      by simp
  }
  then show ?case
    by fastforce
qed auto


\<comment> \<open>TODO unwrap metis proof.\<close>
lemma len_in_state_set_le_max_len:
  fixes as x PROB
  assumes "(s \<in> valid_states PROB)" "(as \<in> valid_plans PROB)" "\<not>(as = [])"
    "(x \<in> state_set (state_list s as))"
  shows "(length x \<le> (Suc (length as)))"
  using assms
  by (metis LENGTH_state_set Suc_eq_plus1_left add.commute state_list_length_lemma_2)


lemma card_state_set_cons:
  fixes as s h
  shows "
    (card (state_set (state_list s (h # as)))
    = Suc (card (state_set (state_list (state_succ s h) as))))
  "
  by (metis length_Cons state_list.simps(2) state_set_card)


lemma card_state_set:
  fixes as s
  shows "(Suc (length as)) = card (state_set (state_list s as))"
  by (simp add: state_list_length_lemma_2 state_set_card)


lemma neq_mems_state_set_neq_len:
  fixes as x y s
  assumes "x \<in> state_set (state_list s as)" "(y \<in> state_set (state_list s as))" "\<not>(x = y)"
  shows "\<not>(length x = length y)"
proof -
  have "x \<noteq> []" "prefix x (state_list s as)"
    using assms(1) state_set_thm
    by blast+
  moreover have "y \<noteq> []" "prefix y (state_list s as)"
    using assms(2) state_set_thm
    by blast+
  ultimately show ?thesis
    using assms(3) append_eq_append_conv prefixE
    by metis
qed


\<comment> \<open>NOTE added definition (imported from pred\_setScript.sml:1562).\<close>
definition inj :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> 'b set \<Rightarrow> bool" where
  "inj f A B \<equiv> (\<forall>x \<in> A. f x \<in> B) \<and> inj_on f A"


\<comment> \<open>NOTE added lemma; refactored from `not\_eq\_last\_diff\_paths`.\<close>
lemma not_eq_last_diff_paths_i:
  fixes s as PROB
  assumes "s \<in> valid_states PROB" "as \<in> valid_plans PROB" "x \<in> state_set (state_list s as)"
  shows "last x \<in> valid_states PROB"
proof -
  have "last x \<in> last ` (state_set (state_list s as))"
    using assms(3)
    by simp
  then show ?thesis
    using assms(1, 2) lemma_1
    by blast
qed

lemma not_eq_last_diff_paths_ii:
  assumes "(s \<in> valid_states PROB)" "(as \<in> valid_plans PROB)"
    "\<not>(inj (last) (state_set (state_list s as)) (valid_states PROB))"
  shows "\<exists>l1. \<exists>l2.
    l1 \<in> state_set (state_list s as)
    \<and> l2 \<in> state_set (state_list s as)
    \<and> last l1 = last l2
    \<and> l1 \<noteq> l2
  "
proof -
  let ?S="state_set (state_list s as)"
  have 1: "\<not>(\<forall>x\<in>?S. last x \<in> valid_states PROB) = False"
    using assms(1, 2) not_eq_last_diff_paths_i
    by blast
  {
    have
      "(\<not>(inj (last) ?S (valid_states PROB))) = (\<not>((\<forall>x\<in>?S. \<forall>y\<in>?S. last x = last y \<longrightarrow> x = y)))"
      unfolding inj_def inj_on_def
      using 1
      by blast
    then have "
        (\<not>(inj (last) ?S (valid_states PROB)))
        = (\<exists>x. \<exists>y. x\<in>?S \<and> y\<in>?S \<and> last x = last y \<and> x \<noteq> y)
      "
      using assms(3)
      by blast
  }
  then show ?thesis
    using assms(3) by blast
qed

lemma not_eq_last_diff_paths:
  fixes as PROB s
  assumes "(s \<in> valid_states PROB)" "(as \<in> valid_plans PROB)"
    "\<not>(inj (last) (state_set (state_list s as)) (valid_states PROB))"
  shows "(\<exists>slist_1 slist_2.
    (slist_1 \<in> state_set (state_list s as))
    \<and> (slist_2 \<in> state_set (state_list s as))
    \<and> ((last slist_1) = (last slist_2))
    \<and> \<not>(length slist_1 = length slist_2))
  "
proof -
  obtain l1 l2 where "
      l1 \<in> state_set (state_list s as)
      \<and> l2 \<in> state_set (state_list s as)
      \<and> last l1 = last l2
      \<and> l1 \<noteq> l2
    "
    using assms(1, 2, 3) not_eq_last_diff_paths_ii
    by blast
  then show ?thesis
    using neq_mems_state_set_neq_len
    by blast
qed


\<comment> \<open>NOTE this lemma was removed due to being redundant and being shadowed later on:

  lemma empty\_list\_nin\_state\_set\<close>


lemma nempty_sl_in_state_set:
  fixes sl
  assumes "sl \<noteq> []"
  shows "sl \<in> state_set sl"
  using assms state_set_thm
  by auto


lemma empty_list_nin_state_set:
  fixes h slist as
  assumes "(h # slist) \<in> state_set (state_list s as)"
  shows "(h = s)"
  using assms
  by (induction as) auto


lemma cons_in_state_set_2:
  fixes s slist h t
  assumes "(slist \<noteq> [])" "((s # slist) \<in> state_set (state_list s (h # t)))"
  shows "(slist \<in> state_set (state_list (state_succ s h) t))"
  using assms
  by (induction slist) auto


\<comment> \<open>TODO move up and replace 'FactoredSystem.lemma\_1\_i'?\<close>
lemma valid_action_valid_succ:
  assumes "h \<in> PROB" "s \<in> valid_states PROB"
  shows "(state_succ s h) \<in> valid_states PROB"
  using assms lemma_1_i
  by blast


lemma in_state_set_imp_eq_exec_prefix:
  fixes slist as PROB s
  assumes "(as \<noteq> [])" "(slist \<noteq> [])" "(s \<in> valid_states PROB)" "(as \<in> valid_plans PROB)"
    "(slist \<in> state_set (state_list s as))"
  shows
    "(\<exists>as'. (prefix as' as) \<and> (exec_plan s as' = last slist) \<and> (length slist = Suc (length as')))"
  using assms
proof (induction slist arbitrary: as s PROB)
  case cons_1: (Cons a slist)
  have 1: "s # slist \<in> state_set (state_list s as)"
    using cons_1.prems(5) empty_list_nin_state_set
    by auto
  then show ?case
    using cons_1
  proof (cases as)
    case cons_2: (Cons a' R\<^sub>a\<^sub>s)
    then have a: "state_succ s a' \<in> valid_states PROB"
      using cons_1.prems(3, 4) valid_action_valid_succ valid_plan_valid_head
      by metis
    then have b: "R\<^sub>a\<^sub>s \<in> valid_plans PROB"
      using cons_1.prems(4) cons_2 valid_plan_valid_tail
      by fast
    then show ?thesis
    proof (cases slist)
      case Nil
      then show ?thesis
        using cons_1.prems(5) empty_list_nin_state_set
        by auto
    next
      case cons_3: (Cons a'' R\<^sub>s\<^sub>l\<^sub>i\<^sub>s\<^sub>t)
      then have i: "a'' # R\<^sub>s\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<in> state_set (state_list (state_succ s a') R\<^sub>a\<^sub>s)"
        using 1 cons_2 cons_in_state_set_2
        by blast
      then show ?thesis
      proof (cases R\<^sub>a\<^sub>s)
        case Nil
        then show ?thesis
          using i cons_2 cons_3
          by auto
      next
        case (Cons a''' R\<^sub>a\<^sub>s')
        then obtain as' where
          "prefix as' (a''' # R\<^sub>a\<^sub>s')" "exec_plan (state_succ s a') as' = last slist"
          "length slist = Suc (length as')"
          using cons_1.IH[of "a''' # R\<^sub>a\<^sub>s'" "state_succ s a'" PROB]
          using i a b cons_3
          by blast
        then show ?thesis
          using Cons_prefix_Cons cons_2 cons_3 exec_plan.simps(2) last.simps length_Cons
            list.distinct(1) local.Cons
          by metis
      qed
    qed
  qed auto
qed auto


lemma eq_last_state_imp_append_nempty_as:
  fixes as PROB slist_1 slist_2
  assumes "(as \<noteq> [])" "(s \<in> valid_states PROB)" "(as \<in> valid_plans PROB)" "(slist_1 \<noteq> [])"
    "(slist_2 \<noteq> [])" "(slist_1 \<in> state_set (state_list s as))"
    "(slist_2 \<in> state_set (state_list s as))" "\<not>(length slist_1 = length slist_2)"
    "(last slist_1 = last slist_2)"
  shows "(\<exists>as1 as2 as3.
    (as1 @ as2 @ as3 = as)
    \<and> (exec_plan s (as1 @ as2) = exec_plan s as1)
    \<and>  \<not>(as2 = [])
  )"
proof -
  obtain as_1 where 1: "(prefix as_1 as)" "(exec_plan s as_1 = last slist_1)"
    "length slist_1 = Suc (length as_1)"
    using assms(1, 2, 3, 4, 6) in_state_set_imp_eq_exec_prefix
    by blast
  obtain as_2 where 2: "(prefix as_2 as)" "(exec_plan s as_2 = last slist_2)"
    "(length slist_2) = Suc (length as_2)"
    using assms(1, 2, 3, 5, 7) in_state_set_imp_eq_exec_prefix
    by blast
  then have "length as_1 \<noteq> length as_2"
    using assms(8) 1(3) 2(3)
    by fastforce
  then consider (i) "length as_1 < length as_2" | (ii) "length as_1 > length as_2"
    by force
  then show ?thesis
  proof (cases)
    case i
    then have "prefix as_1 as_2"
      using 1(1) 2(1) len_gt_pref_is_pref
      by blast
    then obtain a where a1: "as_2 = as_1 @ a"
      using prefixE
      by blast
    then obtain b where b1: "as = as_2 @ b"
      using prefixE 2(1)
      by blast
    let ?as1="as_1"
    let ?as2="a"
    let ?as3="b"
    have "as = ?as1 @ ?as2 @ ?as3"
      using a1 b1
      by simp
    moreover have "exec_plan s (?as1 @ ?as2) = exec_plan s ?as1"
      using 1(2) 2(2) a1 assms(9)
      by auto
    moreover have "?as2 \<noteq> []"
      using i a1
      by simp
    ultimately show ?thesis
      by blast
  next
    case ii
    then have "prefix as_2 as_1"
      using 1(1) 2(1) len_gt_pref_is_pref
      by blast
    then obtain a where a2: "as_1 = as_2 @ a"
      using prefixE
      by blast
    then obtain b where b2: "as = as_1 @ b"
      using prefixE 1(1)
      by blast
    let ?as1="as_2"
    let ?as2="a"
    let ?as3="b"
    have "as = ?as1 @ ?as2 @ ?as3"
      using a2 b2
      by simp
    moreover have "exec_plan s (?as1 @ ?as2) = exec_plan s ?as1"
      using 1(2) 2(2) a2 assms(9)
      by auto
    moreover have "?as2 \<noteq> []"
      using ii a2
      by simp
    ultimately show ?thesis
      by blast
  qed
qed


lemma FINITE_prob_dom:
  assumes "finite PROB"
  shows  "finite (prob_dom PROB)"
proof -
  {
    fix x
    assume P2: "x \<in> PROB"
    then have 1: "(\<lambda>(s1, s2). action_dom s1 s2) x = fmdom' (fst x) \<union> fmdom' (snd x)"
      by (simp add: action_dom_def case_prod_beta')
    then have 2: "finite (fset (fmdom (fst x)))" "finite (fset (fmdom (snd x)))"
      by auto
    then have 3: "fset (fmdom (fst x)) = fmdom' (fst x)" "fset (fmdom (snd x)) = fmdom' (snd x)"
      by (auto simp add: fmdom'_alt_def)
    then have "finite (fmdom' (fst x))"
      using 2 by auto
    then have "finite (fmdom' (snd x))"
      using 2 3 by auto
    then have "finite ((\<lambda>(s1, s2). action_dom s1 s2) x)"
      using 1 2 3
      by simp
  }
  then show "finite (prob_dom PROB)"
    unfolding prob_dom_def
    using assms
    by blast
qed


lemma CARD_valid_states:
  assumes "finite (PROB :: 'a problem)"
  shows "(card (valid_states PROB :: 'a state set) = 2 ^ card (prob_dom PROB))"
proof -
  have 1: "finite (prob_dom PROB)"
    using assms FINITE_prob_dom
    by blast
  have"(card (valid_states PROB :: 'a state set)) = card {s :: 'a state. fmdom' s = prob_dom PROB}"
    unfolding valid_states_def
    by simp
  also have "...  = 2 ^ (card (prob_dom PROB))"
    using 1 card_of_set_of_all_possible_states
    by blast
  finally show ?thesis
    by blast
qed


\<comment> \<open>NOTE type of 'valid\_states PROB' has to be asserted to match 'FINITE\_states' in the proof.\<close>
lemma FINITE_valid_states:
  fixes PROB :: "'a problem"
  shows "finite PROB \<Longrightarrow> finite ((valid_states PROB) :: 'a state set)"
proof (induction PROB rule: finite.induct)
  case emptyI
  then have "valid_states {} = {fmempty}"
    unfolding valid_states_def prob_dom_def
    using empty_domain_fmap_set
    by force
  then show ?case
    by(subst \<open>valid_states {} = {fmempty}\<close>) auto
next
  case (insertI A a)
  {
    then have "finite (insert a A)"
      by blast
    then have "finite (prob_dom (insert a A))"
      using FINITE_prob_dom
      by blast
    then have "finite {s :: 'a state. fmdom' s = prob_dom (insert a A)}"
      using FINITE_states
      by blast
  }
  then show ?case
    unfolding valid_states_def
    by simp
qed


\<comment> \<open>NOTE type of 'PROB' had to be fixed for use of 'FINITE\_valid\_states'.\<close>
lemma lemma_2:
  fixes PROB :: "'a problem" and as :: "('a action) list" and s :: "'a state"
  assumes "finite PROB" "s \<in> (valid_states PROB)" "(as \<in> valid_plans PROB)"
    "((length as) > (2 ^ (card (fmdom' s)) - 1))"
  shows "(\<exists>as1 as2 as3.
    (as1 @ as2 @ as3 = as)
    \<and> (exec_plan s (as1 @ as2) = exec_plan s as1)
    \<and> \<not>(as2 = [])
  )"
proof -
  have "Suc (length as) > 2^(card (fmdom' s))"
    using assms(4)
    by linarith
  then have 1: "card (state_set (state_list s as)) > 2^card (fmdom' s)"
    using card_state_set[symmetric]
    by metis
  {
    \<comment> \<open>NOTE type of 'valid\_states PROB' had to be asserted to match 'FINITE\_valid\_states'.\<close>
    have 2: "finite (prob_dom PROB)" "finite ((valid_states PROB)  :: 'a state set)"
      using assms(1) FINITE_prob_dom FINITE_valid_states
      by blast+
    have 3: "fmdom' s = prob_dom PROB"
      using assms(2) valid_states_def
      by fast
    then have "card ((valid_states PROB) :: 'a state set) = 2^card (fmdom' s)"
      using assms(1) CARD_valid_states
      by auto
    then have 4: "card (state_set (state_list (s :: 'a state) as)) > card ((valid_states PROB) :: 'a state set)"
      unfolding valid_states_def
      using 1 2(1) 3 card_of_set_of_all_possible_states[of "prob_dom PROB"]
      by argo
        \<comment> \<open>TODO refactor into lemma.\<close>
    {
      let ?S="state_set (state_list (s :: 'a state) as)"
      let ?T="valid_states PROB :: 'a state set"
      assume C2: "inj_on last ?S"
        \<comment> \<open>TODO unwrap the metis step or refactor into lemma.\<close>
      have a: "?T \<subseteq> last ` ?S"
        using C2
        by (metis "2"(2) "4" assms(2) assms(3) card_image card_mono lemma_1 not_less)
      have "finite (state_set (state_list s as))"
        using state_set_finite
        by auto
      then have "card (last ` ?S) = card ?S"
        using C2 inj_on_iff_eq_card
        by blast
      also have "\<dots> > card ?T"
        using 4
        by blast
      then have "\<exists>x. x \<in> (last ` ?S) \<and> x \<notin> ?T"
        using C2 a assms(2) assms(3) calculation lemma_1
        by fastforce
    }
    note 5 = this
    moreover
    {
      assume C: "inj last (state_set (state_list (s :: 'a state) as)) (valid_states PROB)"
      then have "inj_on last (state_set (state_list (s :: 'a state) as))"
        using C inj_def
        by blast
      then obtain x where "x \<in> last ` (state_set (state_list s as)) \<and> x \<notin> valid_states PROB"
        using 5
        by presburger
      then have "\<not>(\<forall>x\<in>state_set (state_list s as). last x \<in> valid_states PROB)"
        by blast
      then have "\<not>inj last (state_set (state_list (s :: 'a state) as)) (valid_states PROB)"
        using inj_def
        by metis
      then have False
        using C
        by simp
    }
    ultimately have "\<not>inj last (state_set (state_list (s :: 'a state) as)) (valid_states PROB)"
      unfolding inj_def
      by blast
  }
  then obtain slist_1 slist_2 where 6:
    "slist_1 \<in> state_set (state_list s as)"
    "slist_2 \<in> state_set (state_list s as)"
    "(last slist_1 = last slist_2)"
    "length slist_1 \<noteq> length slist_2"
    using assms(2, 3) not_eq_last_diff_paths
    by blast
  then show ?thesis
  proof (cases as)
    case Nil
    text \<open> 4th assumption is violated in the 'Nil' case. \<close>
    then have "\<not>(2 ^ card (fmdom' s) - 1 < length as)"
      using Nil
      by simp
    then show ?thesis
      using assms(4)
      by blast
  next
    case (Cons a list)
    then have "as \<noteq> []"
      by simp
    moreover have "slist_1 \<noteq> []" "slist_2 \<noteq> []"
      using 6(1, 2) NIL_NOTIN_stateset
      by blast+
    ultimately show ?thesis
      using assms(2, 3) 6(1, 2, 3, 4) eq_last_state_imp_append_nempty_as
      by fastforce
  qed
qed


lemma lemma_2_prob_dom:
  fixes PROB and as :: "('a action) list" and s :: "'a state"
  assumes "finite PROB" "(s \<in> valid_states PROB)" "(as \<in> valid_plans PROB)"
    "(length as > (2 ^ (card (prob_dom PROB))) - 1)"
  shows "(\<exists>as1 as2 as3.
    (as1 @ as2 @ as3 = as)
    \<and> (exec_plan s (as1 @ as2) = exec_plan s as1)
    \<and> \<not>(as2 = [])
  )"
proof -
  have "prob_dom PROB = fmdom' s"
    using assms(2) valid_states_def
    by fast
  then have "2 ^ card (fmdom' s) - 1 < length as"
    using assms(4)
    by argo
  then show ?thesis
    using assms(1, 2, 3) lemma_2
    by blast
qed


\<comment> \<open>NOTE type for `s` had to be fixed (type mismatch in obtain statement).\<close>
\<comment> \<open>NOTE type for `as1`, `as2` and `as3` had to be fixed (due type mismatch on `as1` in
`cycle\_removal\_lemma`)\<close>
lemma lemma_3:
  fixes PROB :: "'a problem" and s :: "'a state"
  assumes "finite PROB" "(s \<in> valid_states PROB)" "(as \<in> valid_plans PROB)"
    "(length as > (2 ^ (card (prob_dom PROB)) - 1))"
  shows "(\<exists>as'.
    (exec_plan s as = exec_plan s as')
    \<and> (length as' < length as)
    \<and> (subseq as' as)
  )"
proof -
  have "prob_dom PROB = fmdom' s"
    using assms(2) valid_states_def
    by fast
  then have "2 ^ card (fmdom' s) - 1 < length as"
    using assms(4)
    by argo
  then obtain as1 as2 as3 :: "'a action list" where 1:
    "as1 @ as2 @ as3 = as" "exec_plan s (as1 @ as2) = exec_plan s as1" "as2 \<noteq> []"
    using assms(1, 2, 3) lemma_2
    by metis
  have 2: "exec_plan s (as1 @ as3) = exec_plan s (as1 @ as2 @ as3)"
    using 1 cycle_removal_lemma
    by fastforce
  let ?as' = "as1 @ as3"
  have "exec_plan s as = exec_plan s ?as'"
    using 1 2
    by auto
  moreover have "length ?as' < length as"
    using 1 nempty_list_append_length_add
    by blast
  moreover have "subseq ?as' as"
    using 1 subseq_append'
    by blast
  ultimately show "(\<exists>as'.
      (exec_plan s as = exec_plan s as') \<and> (length as' < length as) \<and> (subseq as' as))"
    by blast
qed


\<comment> \<open>TODO unwrap meson step.\<close>
lemma sublist_valid_is_valid:
  fixes as' as PROB
  assumes "(as \<in> valid_plans PROB)" "(subseq as' as)"
  shows "as' \<in> valid_plans PROB"
  using assms
  by (simp add: valid_plans_def) (meson dual_order.trans fset_of_list_subset sublist_subset)


\<comment> \<open>NOTE type of 's' had to be fixed (type mismatch in goal).\<close>
theorem main_lemma:
  fixes PROB :: "'a problem" and as s
  assumes "finite PROB" "(s \<in> valid_states PROB)" "(as \<in> valid_plans PROB)"
  shows "(\<exists>as'.
    (exec_plan s as = exec_plan s as')
    \<and> (subseq as' as)
    \<and> (length  as' \<le> (2 ^ (card (prob_dom PROB))) - 1)
  )"
proof (cases "length as \<le> (2 ^ (card (prob_dom PROB))) - 1")
  case True
  then have "exec_plan s as = exec_plan s as"
    by simp
  then have "subseq as as"
    by auto
  then have "length as \<le> (2^(card (prob_dom PROB)) - 1)"
    using True
    by auto
  then show ?thesis
    by blast
next
  case False
  then have "length as > (2 ^ (card (prob_dom PROB))) - 1"
    using False
    by auto
  then obtain as' where 1:
    "exec_plan s as = exec_plan s as'" "length as' < length as" "subseq as' as"
    using assms lemma_3
    by blast
  {
    fix p
    assume "exec_plan s as = exec_plan s p" "subseq p as"
      "2 ^ card (prob_dom PROB) - 1 < length p"
    then have "(\<exists>p'. (exec_plan s as = exec_plan s p' \<and> subseq p' as) \<and> length p' < length p)"
      using assms(1, 2, 3) lemma_3 sublist_valid_is_valid
      by fastforce
  }
  then have "\<forall>p. exec_plan s as = exec_plan s p \<and> subseq p as \<longrightarrow>
      (\<exists>p'. (exec_plan s as = exec_plan s p' \<and> subseq p' as)
      \<and> length p' \<le> 2 ^ card (prob_dom PROB) - 1)"
    using general_theorem[where
        P = "\<lambda>(as'' :: 'a action list). (exec_plan s as = exec_plan s as'') \<and> subseq as'' as"
        and l = "(2 ^ (card (prob_dom (PROB ::'a problem)))) - 1" and f = length]
    by blast
  then obtain p' where
    "exec_plan s as = exec_plan s p'" "subseq p' as" "length p' \<le> 2 ^ card (prob_dom PROB) - 1"
    by blast
  then show ?thesis
    using sublist_refl
    by blast
qed


subsection "Reachable States"


\<comment> \<open>NOTE shortened to 'reachable\_s'\<close>
definition reachable_s where
  "reachable_s PROB s \<equiv> {exec_plan s as | as. as \<in> valid_plans PROB}"


\<comment> \<open>NOTE types for `s` and `PROB` had to be fixed (type mismatch in goal).\<close>
lemma valid_as_valid_exec:
  fixes as and s :: "'a state" and PROB :: "'a problem"
  assumes "(as \<in> valid_plans PROB)" "(s \<in> valid_states PROB)"
  shows "(exec_plan s as \<in> valid_states PROB)"
  using assms
proof (induction as arbitrary: s PROB)
  case (Cons a as)
  then have "a \<in> PROB"
    using valid_plan_valid_head
    by metis
  then have "state_succ s a \<in> valid_states PROB"
    using Cons.prems(2) valid_action_valid_succ
    by blast
  moreover have "as \<in> valid_plans PROB"
    using Cons.prems(1) valid_plan_valid_tail
    by fast
  ultimately show ?case
    using Cons.IH
    by force
qed simp


lemma exec_plan_fdom_subset:
  fixes as s PROB
  assumes "(as \<in> valid_plans PROB)"
  shows "(fmdom' (exec_plan s as) \<subseteq> (fmdom' s \<union> prob_dom PROB))"
  using assms
proof (induction as arbitrary: s PROB)
  case (Cons a as)
  have "as \<in> valid_plans PROB"
    using Cons.prems valid_plan_valid_tail
    by fast
  then have "fmdom' (exec_plan (state_succ s a) as) \<subseteq> fmdom' (state_succ s a) \<union> prob_dom PROB"
    using Cons.IH[of _ "state_succ s a"]
    by simp
      \<comment> \<open>TODO unwrap metis proofs.\<close>
  moreover have "fmdom' s \<union> fmdom' (snd a) \<union> prob_dom PROB = fmdom' s \<union> prob_dom PROB"
    by (metis
        Cons.prems FDOM_eff_subset_prob_dom_pair sup_absorb2 sup_assoc valid_plan_valid_head)
  ultimately show ?case
    by (metis (no_types, lifting)
        FDOM_state_succ_subset exec_plan.simps(2) order_refl subset_trans sup.mono)
qed simp


\<comment> \<open>NOTE added lemma.\<close>
lemma reachable_s_finite_thm_1_a:
  fixes s and PROB :: "'a problem"
  assumes "(s :: 'a state) \<in> valid_states PROB"
  shows "(\<forall>l\<in>reachable_s PROB s. l\<in>valid_states PROB)"
proof -
  have 1: "\<forall>l\<in>reachable_s PROB s. \<exists>as. l = exec_plan s as \<and> as \<in> valid_plans PROB"
    using reachable_s_def
    by fastforce
  {
    fix l
    assume P1: "l \<in> reachable_s PROB s"
      \<comment> \<open>NOTE type for 's' and 'as' had to be fixed due to type mismatch in obtain statement.\<close>
    then obtain as :: "'a action list" where a: "l = exec_plan s as \<and> as \<in> valid_plans PROB"
      using 1
      by blast
    then have "exec_plan s as \<in> valid_states PROB"
      using assms a valid_as_valid_exec
      by blast
    then have "l \<in> valid_states PROB"
      using a
      by simp
  }
  then show "\<forall>l \<in> reachable_s PROB s. l \<in> valid_states PROB"
    by blast
qed

lemma reachable_s_finite_thm_1:
  assumes "((s :: 'a state) \<in> valid_states PROB)"
  shows "(reachable_s PROB s \<subseteq> valid_states PROB)"
  using assms reachable_s_finite_thm_1_a
  by blast


\<comment> \<open>NOTE second declaration skipped (this is declared twice in the source; see above)\<close>
\<comment> \<open>NOTE type for `s` had to be fixed (type mismatch in goal).\<close>
lemma reachable_s_finite_thm:
  fixes s :: "'a state"
  assumes "finite (PROB :: 'a problem)" "(s \<in> valid_states PROB)"
  shows "finite (reachable_s PROB s)"
  using assms
  by (meson FINITE_valid_states reachable_s_finite_thm_1 rev_finite_subset)


lemma empty_plan_is_valid: "[] \<in> (valid_plans PROB)"
  by (simp add: valid_plans_def)


lemma valid_head_and_tail_valid_plan:
  assumes "(h \<in> PROB)" "(as \<in> valid_plans PROB)"
  shows "((h # as) \<in> valid_plans PROB)"
  using assms
  by (auto simp: valid_plans_def)


\<comment> \<open>TODO refactor\<close>
\<comment> \<open>NOTE added lemma\<close>
lemma lemma_1_reachability_s_i:
  fixes PROB s
  assumes "s \<in> valid_states PROB"
  shows "s \<in> reachable_s PROB s"
proof -
  have "[] \<in> valid_plans PROB"
    using empty_plan_is_valid
    by blast
  then show ?thesis
    unfolding reachable_s_def
    by force
qed

\<comment> \<open>NOTE types for 'PROB' and 's' had to be fixed (type mismatch in goal).\<close>
lemma lemma_1_reachability_s:
  fixes PROB :: "'a problem" and s :: "'a state" and as
  assumes "(s \<in> valid_states PROB)" "(as \<in> valid_plans PROB)"
  shows "((last ` state_set (state_list s as)) \<subseteq> (reachable_s PROB s))"
  using assms
proof(induction as arbitrary: PROB s)
  case Nil
  then have "(last ` state_set (state_list s [])) = {s}"
    by force
  then show ?case
    unfolding reachable_s_def
    using empty_plan_is_valid
    by force
next
  case cons: (Cons a as)
  let ?S="last ` state_set (state_list s (a # as))"
  {
    let ?as="[]"
    have "last [s] = exec_plan s ?as"
      by simp
    moreover have "?as \<in> valid_plans PROB"
      using empty_plan_is_valid
      by auto
    ultimately have "\<exists>as. (last [s] = exec_plan s as) \<and> as \<in> valid_plans PROB"
      by blast
  }
  note 1 = this
  {
    fix x
    assume P: "x \<in> ?S"
    then consider
      (a) "x = last [s]"
      | (b) "x \<in> last ` ((#) s ` state_set (state_list (state_succ s a) as))"
      by auto
    then have "x \<in> reachable_s PROB s"
    proof (cases)
      case a
      then have "x = s"
        by simp
      then show ?thesis
        using cons.prems(1) P lemma_1_reachability_s_i
        by blast
    next
      case b
      then obtain x'' where i:
        "x'' \<in> state_set (state_list (state_succ s a) as)"
        "x = last (s # x'')"
        by blast
      then show ?thesis
      proof (cases "x''")
        case Nil
        then have "x = s"
          using i
          by fastforce
        then show ?thesis
          using cons.prems(1) lemma_1_reachability_s_i
          by blast
      next
        case (Cons a' list)
        then obtain x' where a:
          "last (a' # list) = last x'" "x' \<in> state_set (state_list (state_succ s a) as)"
          using i(1)
          by blast
        {
          have "state_succ s a \<in> valid_states PROB"
            using cons.prems(1, 2) valid_action_valid_succ valid_plan_valid_head
            by metis
          moreover have "as \<in> valid_plans PROB"
            using cons.prems(2) valid_plan_valid_tail
            by fast
          ultimately have
            "last ` state_set (state_list (state_succ s a) as) \<subseteq> reachable_s PROB (state_succ s a)"
            using cons.IH[of "state_succ s a"]
            by auto
          then have "\<exists>as'.
                  last (a' # list) = exec_plan (state_succ s a) as' \<and> (as' \<in> (valid_plans PROB))"
            unfolding state_set.simps state_list.simps reachable_s_def
            using i(1) Cons
            by blast
        }
        then obtain as' where b:
          "last (a' # list) = exec_plan (state_succ s a) as'" "(as' \<in> (valid_plans PROB))"
          by blast
        then have "x = exec_plan (state_succ s a) as'"
          using i(2) Cons a(1)
          by auto
        then show ?thesis unfolding reachable_s_def
          using cons.prems(2) b(2)
          by (metis (mono_tags, lifting)  exec_plan.simps(2) mem_Collect_eq
              valid_head_and_tail_valid_plan valid_plan_valid_head)
      qed
    qed
  }
  then show ?case
    by blast
qed


\<comment> \<open>NOTE types for `PROB` and `s` had to be fixed for use of `lemma\_1\_reachability\_s`.\<close>
lemma not_eq_last_diff_paths_reachability_s:
  fixes PROB :: "'a problem" and s :: "'a state" and as
  assumes "s \<in> valid_states PROB" "as \<in> valid_plans PROB"
    "\<not>(inj last (state_set (state_list s as)) (reachable_s PROB s))"
  shows "(\<exists>slist_1 slist_2.
    slist_1 \<in> state_set (state_list s as)
    \<and> slist_2 \<in> state_set (state_list s as)
    \<and> (last slist_1 = last slist_2)
    \<and> \<not>(length slist_1 = length slist_2)
  )"
proof -
  {
    fix x
    assume P1: "x \<in> state_set (state_list s as)"
    have a: "last ` state_set (state_list s as) \<subseteq> reachable_s PROB s"
      using assms(1, 2) lemma_1_reachability_s
      by fast
    then have "\<forall>as PROB. s \<in> (valid_states PROB) \<and> as \<in> (valid_plans PROB) \<longrightarrow> (last ` (state_set (state_list s as)) \<subseteq> reachable_s PROB s)"
      using lemma_1_reachability_s
      by fast
    then have "last x \<in> valid_states PROB"
      using assms(1, 2) P1 lemma_1
      by fast
    then have "last x \<in> reachable_s PROB s"
      using P1 a
      by fast
  }
  note 1 = this
  text \<open> Show the goal by disproving the contradiction. \<close>
  {
    assume C: "(\<forall>slist_1 slist_2. (slist_1 \<in> state_set (state_list s as)
      \<and> slist_2 \<in> state_set (state_list s as)
      \<and> (last slist_1 = last slist_2)) \<longrightarrow> (length slist_1 = length slist_2))"
    moreover {
      fix slist_1 slist_2
      assume C1: "slist_1 \<in> state_set (state_list s as)" "slist_2 \<in> state_set (state_list s as)"
        "(last slist_1 = last slist_2)"
      moreover have i: "(length slist_1 = length slist_2)"
        using C1 C
        by blast
      moreover have "slist_1 = slist_2"
        using C1(1, 2) i neq_mems_state_set_neq_len
        by auto
      ultimately have "inj_on last (state_set (state_list s as))"
        unfolding inj_on_def
        using C neq_mems_state_set_neq_len
        by blast
      then have False
        using 1 inj_def assms(3)
        by blast
    }
    ultimately have False
      by (metis empty_state_list_lemma nempty_sl_in_state_set)
  }
  then show ?thesis
    by blast
qed


\<comment> \<open>NOTE added lemma ( translation of `PHP` in pred\_setScript.sml:3155).\<close>
lemma lemma_2_reachability_s_i:
  fixes f :: "'a \<Rightarrow> 'b" and s t
  assumes "finite t" "card t < card s"
  shows "\<not>(inj f s t)"
proof -
  {
    assume C: "inj f s t"
    then have 1: "(\<forall>x\<in>s. f x \<in> t)" "inj_on f s"
      unfolding inj_def
      by blast+
    moreover {
      have "f ` s \<subseteq> t"
        using 1
        by fast
      then have "card (f ` s) \<le> card t"
        using assms(1) card_mono
        by auto
    }
    moreover have "card (f ` s) = card s"
      using 1 card_image
      by fast
    ultimately have False
      using assms(2)
      by linarith
  }
  then show ?thesis
    by blast
qed

lemma lemma_2_reachability_s:
  fixes PROB :: "'a problem" and as s
  assumes "finite PROB" "(s \<in> valid_states PROB)" "(as \<in> valid_plans PROB)"
    "(length as > card (reachable_s PROB s) - 1)"
  shows "(\<exists>as1 as2 as3.
    (as1 @ as2 @ as3 = as) \<and> (exec_plan s (as1 @ as2) = exec_plan s as1) \<and> \<not>(as2 = []))"
proof -
  {
    have "Suc (length as) > card (reachable_s PROB s)"
      using assms(4)
      by fastforce
    then have "card (state_set (state_list s as)) > card (reachable_s PROB s)"
      using card_state_set
      by metis
  }
  note 1 = this
  {
    have "finite (reachable_s PROB s)"
      using assms(1, 2) reachable_s_finite_thm
      by blast
    then have "\<not>(inj last (state_set (state_list s as)) (reachable_s PROB s))"
      using assms(4) 1 lemma_2_reachability_s_i
      by blast
  }
  note 2 = this
  obtain slist_1 slist_2 where 3:
    "slist_1 \<in> state_set (state_list s as)" "slist_2 \<in> state_set (state_list s as)"
    "(last slist_1 = last slist_2)" "length slist_1 \<noteq> length slist_2"
    using assms(2, 3) 2 not_eq_last_diff_paths_reachability_s
    by blast
  then show ?thesis using assms
  proof(cases as)
    case (Cons a list)
    then show ?thesis
      using assms(2, 3) 3 eq_last_state_imp_append_nempty_as state_set_thm list.distinct(1)
      by metis
  qed force
qed


lemma lemma_3_reachability_s:
  fixes as and PROB :: "'a problem" and s
  assumes "finite PROB" "(s \<in> valid_states PROB)" "(as \<in> valid_plans PROB)"
    "(length as > (card (reachable_s PROB s) - 1))"
  shows "(\<exists>as'.
    (exec_plan s as = exec_plan s as')
    \<and> (length as' < length as)
    \<and> (subseq as' as)
  )"
proof -
  obtain as1 as2 as3 :: "'a action list" where 1:
    "(as1 @ as2 @ as3 = as)" "(exec_plan s (as1 @ as2) = exec_plan s as1)" "~(as2=[])"
    using assms lemma_2_reachability_s
    by metis
  then have "(exec_plan s (as1 @ as2) = exec_plan s as1)"
    using 1
    by blast
  then have 2: "exec_plan s (as1 @ as3) = exec_plan s (as1 @ as2 @ as3)"
    using 1 cycle_removal_lemma
    by fastforce
  let ?as' = "as1 @ as3"
  have 3: "exec_plan s as = exec_plan s ?as'"
    using 1 2
    by argo
  then have "as2 \<noteq> []"
    using 1
    by blast
  then have 4: "length ?as' < length as"
    using nempty_list_append_length_add 1
    by blast
  then have "subseq ?as' as"
    using 1 subseq_append'
    by blast
  then show ?thesis
    using 3 4
    by blast
qed


\<comment> \<open>NOTE type for `as` had to be fixed (type mismatch in goal).\<close>
lemma main_lemma_reachability_s:
  fixes PROB :: "'a problem" and as and s :: "'a state"
  assumes "finite PROB" "(s \<in> valid_states PROB)" "(as \<in> valid_plans PROB)"
  shows "(\<exists>as'.
      (exec_plan s as = exec_plan s as') \<and> subseq as' as
      \<and> (length as' \<le> (card (reachable_s PROB s) - 1)))"
proof (cases "length as \<le> card (reachable_s PROB s) - 1")
  case False
  let ?as' = "as"
  have "length as > card (reachable_s PROB s) - 1"
    using False
    by simp
  {
    fix p
    assume P: "exec_plan s as = exec_plan s p" "subseq p as"
      "card (reachable_s PROB s) - 1 < length p"
    moreover have "p \<in> valid_plans PROB"
      using assms(3) P(2) sublist_valid_is_valid
      by blast
    ultimately obtain as' where 1:
      "exec_plan s p = exec_plan s as'" "length as' < length p" "subseq as' p"
      using assms lemma_3_reachability_s
      by blast
    then have "exec_plan s as = exec_plan s as'"
      using P
      by presburger
    moreover have "subseq as' as"
      using P 1 sublist_trans
      by blast
    ultimately have "(\<exists>p'. (exec_plan s as = exec_plan s p' \<and> subseq p' as) \<and> length p' < length p)"
      using 1
      by blast
  }
  then have "\<forall>p.
      exec_plan s as = exec_plan s p \<and> subseq p as
      \<longrightarrow> (\<exists>p'.
        (exec_plan s as = exec_plan s p' \<and> subseq p' as)
        \<and> length p' \<le> card (reachable_s PROB s) - 1)"
    using general_theorem[of "\<lambda>as''. (exec_plan s as = exec_plan s as'') \<and> subseq as'' as"
        "(card (reachable_s (PROB :: 'a problem) (s :: 'a state)) - 1)" length]
    by blast
  then show ?thesis
    by blast
qed blast


lemma reachable_s_non_empty: "\<not>(reachable_s PROB s = {})"
  using empty_plan_is_valid reachable_s_def
  by blast


lemma card_reachable_s_non_zero:
  fixes s
  assumes "finite (PROB :: 'a problem)" "(s \<in> valid_states PROB)"
  shows "(0 < card (reachable_s PROB s))"
  using assms
  by (simp add: card_gt_0_iff reachable_s_finite_thm reachable_s_non_empty)


lemma exec_fdom_empty_prob:
  fixes s
  assumes "(prob_dom PROB = {})" "(s \<in> valid_states PROB)" "(as \<in> valid_plans PROB)"
  shows "(exec_plan s as = fmempty)"
proof -
  have "fmdom' s = {}"
    using assms(1, 2)
    by (simp add: valid_states_def)
  then show "exec_plan s as = fmempty"
    using assms(1, 3)
    by (metis
        exec_plan_fdom_subset fmrestrict_set_dom fmrestrict_set_null subset_empty
        sup_bot.left_neutral)
qed


\<comment> \<open>NOTE types for `PROB` and `s` had to be fixed (type mismatch in goal).\<close>
lemma reachable_s_empty_prob:
  fixes PROB :: "'a problem" and s :: "'a state"
  assumes "(prob_dom PROB = {})" "(s \<in> valid_states PROB)"
  shows "((reachable_s PROB s) \<subseteq> {fmempty})"
proof -
  {
    fix x
    assume P1: "x \<in> reachable_s PROB s"
    then obtain as :: "'a action list" where a:
      "as \<in> valid_plans PROB" "x = exec_plan s as"
      using reachable_s_def
      by blast
    then have "as \<in> valid_plans PROB" "x = exec_plan s as"
      using a
      by auto
    then have "x = fmempty" using assms(1, 2) exec_fdom_empty_prob
      by blast
  }
  then show "((reachable_s PROB s) \<subseteq> {fmempty})"
    by blast
qed


\<comment> \<open>NOTE this is semantically equivalent to `sublist\_valid\_is\_valid`.\<close>
\<comment> \<open>NOTE Renamed to 'sublist\_valid\_plan\_alt' because another lemma by the same name is declared
later.\<close>
lemma sublist_valid_plan__alt:
  assumes "(as1 \<in> valid_plans PROB)" "(subseq as2 as1)"
  shows "(as2 \<in> valid_plans PROB)"
  using assms
  by (auto simp add: sublist_valid_is_valid)


lemma fmsubset_eq:
  assumes "s1 \<subseteq>\<^sub>f s2"
  shows "(\<forall>a. a |\<in>| fmdom s1 \<longrightarrow> fmlookup s1 a = fmlookup s2 a)"
  using assms
  by (metis (mono_tags, lifting) domIff fmdom_notI fmsubset.rep_eq map_le_def)


\<comment> \<open>NOTE added lemma.\<close>
\<comment> \<open>TODO refactor/move into 'FmapUtils.thy'.\<close>
lemma submap_imp_state_succ_submap_a:
  assumes "s1 \<subseteq>\<^sub>f s2" "s2 \<subseteq>\<^sub>f s3"
  shows "s1 \<subseteq>\<^sub>f s3"
  using assms fmsubset.rep_eq map_le_trans
  by blast


\<comment> \<open>NOTE added lemma.\<close>
\<comment> \<open>TODO refactor into FmapUtils?\<close>
lemma submap_imp_state_succ_submap_b:
  assumes "s1 \<subseteq>\<^sub>f s2"
  shows "(s0 ++ s1) \<subseteq>\<^sub>f (s0 ++ s2)"
proof -
  {
    assume C: "\<not>((s0 ++ s1) \<subseteq>\<^sub>f (s0 ++ s2))"
    then have 1: "(s0 ++ s1) = (s1 ++\<^sub>f s0)"
      using fmap_add_ltr_def
      by blast
    then have 2: "(s0 ++ s2) = (s2 ++\<^sub>f s0)"
      using fmap_add_ltr_def
      by auto
    then obtain a where 3:
      "a |\<in>| fmdom (s1 ++\<^sub>f s0) \<and> fmlookup (s1 ++\<^sub>f s0) \<noteq> fmlookup (s2 ++\<^sub>f s0)"
      using C 1 2 fmsubset.rep_eq domIff fmdom_notD map_le_def
      by (metis (no_types, lifting))
    then have False
      using assms(1) C proof (cases "a |\<in>| fmdom s1")
      case True
      moreover have "fmlookup s1 a = fmlookup s2 a"
        by (meson assms(1) calculation fmsubset_eq)
      moreover have "fmlookup (s0 ++\<^sub>f s1) a = fmlookup s1 a"
        by (simp add: True)
      moreover have "a |\<in>| fmdom s2"
        using True calculation(2) fmdom_notD by fastforce
      moreover have "fmlookup (s0 ++\<^sub>f s2) a = fmlookup s2 a"
        by (simp add: calculation(4))
      moreover have "fmlookup (s0 ++\<^sub>f s1) a = fmlookup (s0 ++\<^sub>f s2) a"
        using calculation(2, 3, 5)
        by auto
      ultimately show ?thesis
        by (smt "1" "2" C assms domIff fmlookup_add fmsubset.rep_eq map_le_def)
    next
      case False
      moreover have "fmlookup (s0 ++\<^sub>f s1) a = fmlookup s0 a"
        by (auto simp add: False)
      ultimately show ?thesis proof (cases "a |\<in>| fmdom s0")
        case True
        have "a |\<notin>| fmdom (s1 ++\<^sub>f s0)"
          by (smt "1" "2" C UnE assms dom_map_add fmadd.rep_eq fmsubset.rep_eq map_add_def
              map_add_dom_app_simps(1) map_le_def)
        then show ?thesis
          using 3 by blast
      next
        case False
        then have "a |\<notin>| fmdom (s1 ++\<^sub>f s0)"
          using \<open>fmlookup (s0 ++\<^sub>f s1) a = fmlookup s0 a\<close>
          by force
        then show ?thesis
          using 3
          by blast
      qed
    qed
  }
  then show ?thesis
    by blast
qed

\<comment> \<open>NOTE type for `a` had to be fixed (type mismatch in goal).\<close>
lemma submap_imp_state_succ_submap:
  fixes a :: "'a action" and s1 s2
  assumes "(fst a \<subseteq>\<^sub>f s1)" "(s1 \<subseteq>\<^sub>f s2)"
  shows "(state_succ s1 a \<subseteq>\<^sub>f state_succ s2 a)"
proof -
  have 1: "state_succ s1 a = (snd a ++ s1)"
    using assms(1)
    by (simp add: state_succ_def)
  then have "fst a \<subseteq>\<^sub>f s2"
    using assms(1, 2) submap_imp_state_succ_submap_a
    by auto
  then have 2: "state_succ s2 a = (snd a ++ s2)"
    using 1 state_succ_def
    by metis
  then have "snd a ++ s1 \<subseteq>\<^sub>f snd a ++ s2"
    using assms(2) submap_imp_state_succ_submap_b
    by fast
  then show ?thesis
    using 1 2
    by argo
qed


\<comment> \<open>NOTE types for `a`, `s1` and `s2` had to be fixed (type mismatch in goal).\<close>
lemma pred_dom_subset_succ_submap:
  fixes a :: "'a action" and s1 s2 :: "'a state"
  assumes "(fmdom' (fst a) \<subseteq> fmdom' s1)" "(s1 \<subseteq>\<^sub>f s2)"
  shows "(state_succ s1 a \<subseteq>\<^sub>f state_succ s2 a)"
  using assms
  unfolding state_succ_def
proof (auto)
  assume P1: "fmdom' (fst a) \<subseteq> fmdom' s1" "s1 \<subseteq>\<^sub>f s2" "fst a \<subseteq>\<^sub>f s1" "fst a \<subseteq>\<^sub>f s2"
  then show "snd a ++ s1 \<subseteq>\<^sub>f snd a ++ s2"
    using submap_imp_state_succ_submap_b
    by fast
next
  assume P2: "fmdom' (fst a) \<subseteq> fmdom' s1" "s1 \<subseteq>\<^sub>f s2" "fst a \<subseteq>\<^sub>f s1" "\<not> fst a \<subseteq>\<^sub>f s2"
  then show "snd a ++ s1 \<subseteq>\<^sub>f s2"
    using submap_imp_state_succ_submap_a
    by blast
next
  assume P3: "fmdom' (fst a) \<subseteq> fmdom' s1" "s1 \<subseteq>\<^sub>f s2" "\<not> fst a \<subseteq>\<^sub>f s1" "fst a \<subseteq>\<^sub>f s2"
  {
    have a: "fmlookup s1 \<subseteq>\<^sub>m fmlookup s2"
      using P3(2) fmsubset.rep_eq
      by blast
    {
      have "\<not>(fmlookup (fst a) \<subseteq>\<^sub>m fmlookup s1)"
        using P3(3) fmsubset.rep_eq
        by blast
      then have "\<exists>v \<in> dom (fmlookup (fst a)). fmlookup (fst a) v \<noteq> fmlookup s1 v"
        using map_le_def
        by fast
    }
    then obtain v where b: "v \<in> dom (fmlookup (fst a))" "fmlookup (fst a) v \<noteq> fmlookup s1 v"
      by blast
    then have "fmlookup (fst a) v \<noteq> fmlookup s2 v"
      using assms(1) a  contra_subsetD fmdom'.rep_eq map_le_def
      by metis
    then have "\<not>(fst a \<subseteq>\<^sub>f s2)"
      using b fmsubset.rep_eq map_le_def
      by metis
  }
  then show "s1 \<subseteq>\<^sub>f snd a ++ s2"
    using P3(4)
    by simp
qed


\<comment> \<open>NOTE added lemma.\<close>
\<comment> \<open>TODO refactor.\<close>
lemma valid_as_submap_init_submap_exec_i:
  fixes s a
  shows "fmdom' s \<subseteq> fmdom' (state_succ s a)"
proof (cases "fst a \<subseteq>\<^sub>f s")
  case True
  then have "state_succ s a = s ++\<^sub>f (snd a)"
    unfolding state_succ_def
    using fmap_add_ltr_def
    by auto
  then have "fmdom' (state_succ s a) = fmdom' s \<union> fmdom' (snd a)"
    using fmdom'_add
    by simp
  then show ?thesis
    by simp
next
  case False
  then show ?thesis
    unfolding state_succ_def
    by simp
qed

\<comment> \<open>NOTE types for `s1` and `s2` had to be fixed in order to apply `pred\_dom\_subset\_succ\_submap`.\<close>
lemma valid_as_submap_init_submap_exec:
  fixes s1 s2 :: "'a state"
  assumes "(s1 \<subseteq>\<^sub>f s2) " "(\<forall>a. ListMem a as \<longrightarrow> (fmdom' (fst a) \<subseteq> fmdom' s1))"
  shows "(exec_plan s1 as \<subseteq>\<^sub>f exec_plan s2 as)"
  using assms
proof (induction as arbitrary: s1 s2)
  case (Cons a as)
  {
    have "ListMem a (a # as)"
      using elem
      by fast
    then have "fmdom' (fst a) \<subseteq> fmdom' s1"
      using Cons.prems(2)
      by blast
    then have "state_succ s1 a \<subseteq>\<^sub>f state_succ s2 a"
      using Cons.prems(1) pred_dom_subset_succ_submap
      by fast
  }
  note 1 = this
  {
    fix b
    assume "ListMem b as"
    then have "ListMem b (a # as)"
      using insert
      by fast
    then have a: "fmdom' (fst b) \<subseteq> fmdom' s1"
      using Cons.prems(2)
      by blast
    then have "fmdom' s1 \<subseteq> fmdom' (state_succ s1 a)"
      using valid_as_submap_init_submap_exec_i
      by metis
    then have "fmdom' (fst b) \<subseteq> fmdom' (state_succ s1 a)"
      using a
      by simp
  }
  then show ?case
    using 1 Cons.IH[of "(state_succ s1 a)" "(state_succ s2 a)"]
    by fastforce
qed auto


lemma valid_plan_mems:
  assumes "(as \<in> valid_plans PROB)" "(ListMem a as)"
  shows "a \<in> PROB"
  using assms ListMem_iff in_set_conv_decomp valid_append_valid_suff valid_plan_valid_head
  by (metis)


\<comment> \<open>NOTE typing moved into 'fixes' due to type mismatches when using lemma.\<close>
\<comment> \<open>NOTE showcase (this can't be used due to type problems when the type is specified within
proposition.\<close>
lemma valid_states_nempty:
  fixes PROB :: "(('a, 'b) fmap \<times> ('a, 'b) fmap) set"
  assumes "finite PROB"
  shows "\<exists>s. s \<in> (valid_states PROB)"
  unfolding valid_states_def
  using fmchoice'[OF FINITE_prob_dom[OF assms], where Q = "\<lambda>_ _. True"]
  by auto


lemma empty_prob_dom_single_val_state:
  assumes "(prob_dom PROB = {})"
  shows "(\<exists>s. valid_states PROB = {s})"
proof -
  {
    assume C: "\<not>(\<exists>s. valid_states PROB = {s})"
    then have "valid_states PROB = {s. fmdom' s = {}}"
      using assms
      by (simp add: valid_states_def)
    then have "\<exists>s. valid_states PROB = {s}"
      using empty_domain_fmap_set
      by blast
    then have False
      using C
      by blast
  }
  then show ?thesis
    by blast
qed


lemma empty_prob_dom_imp_empty_plan_always_good:
  fixes PROB s
  assumes "(prob_dom PROB = {})" "(s \<in> valid_states PROB)" "(as \<in> valid_plans PROB)"
  shows "(exec_plan s [] = exec_plan s as)"
  using assms empty_plan_is_valid exec_fdom_empty_prob
  by fastforce


lemma empty_prob_dom:
  fixes PROB
  assumes "(prob_dom PROB = {})"
  shows "(PROB = {(fmempty, fmempty)} \<or> PROB = {})"
  using assms
proof (cases "PROB = {}")
  case False
  have "\<Union>((\<lambda>(s1, s2). fmdom' s1 \<union> fmdom' s2) ` PROB) = {}"
    using assms
    by (simp add: prob_dom_def action_dom_def)
  then have 1:"\<forall>a\<in>PROB. (\<lambda>(s1, s2). fmdom' s1 \<union> fmdom' s2) a = {}"
    using  Union_empty_conv
    by auto
  {
    fix a
    assume P1: "a\<in>PROB"
    then have "(\<lambda>(s1, s2). fmdom' s1 \<union> fmdom' s2) a = {}"
      using 1
      by simp
    then have a: "fmdom' (fst a) = {}" "fmdom' (snd a) = {}"
      by auto+
    then have b: "fst a = fmempty"
      using fmrestrict_set_dom fmrestrict_set_null
      by metis
    then have "snd a = fmempty"
      using a(2) fmrestrict_set_dom fmrestrict_set_null
      by metis
    then have "a = (fmempty, fmempty)"
      using b surjective_pairing
      by metis
  }
  then have "PROB = {(fmempty, fmempty)}"
    using False
    by blast
  then show ?thesis
    by blast
qed simp


lemma empty_prob_dom_finite:
  fixes PROB :: "'a problem"
  assumes "prob_dom PROB = {}"
  shows "finite PROB"
proof -
  consider (i) "PROB = {(fmempty, fmempty)}" | (ii) "PROB = {}"
    using assms empty_prob_dom
    by auto
  then show ?thesis by (cases) auto
qed


\<comment> \<open>NOTE type for `a` had to be fixed (type mismatch in goal).\<close>
lemma disj_imp_eq_proj_exec:
  fixes a :: "('a, 'b) fmap \<times> ('a, 'b) fmap" and vs s
  assumes "(fmdom' (snd a) \<inter> vs) = {}"
  shows "(fmrestrict_set vs s = fmrestrict_set vs (state_succ s a))"
proof -
  have "disjnt (fmdom' (snd a)) vs"
    using assms disjnt_def
    by fast
  then show ?thesis
    using disj_dom_drest_fupdate_eq state_succ_pair surjective_pairing
    by metis
qed


lemma no_change_vs_eff_submap:
  fixes a vs s
  assumes "(fmrestrict_set vs s = fmrestrict_set vs (state_succ s a))" "(fst a \<subseteq>\<^sub>f s)"
  shows "(fmrestrict_set vs (snd a) \<subseteq>\<^sub>f (fmrestrict_set vs s))"
proof -
  {
    fix x
    assume P3: "x \<in> dom (fmlookup (fmrestrict_set vs (snd a)))"
    then have "(fmlookup (fmrestrict_set vs (snd a))) x = (fmlookup (fmrestrict_set vs s)) x"
    proof (cases "fmlookup (fmrestrict_set vs (snd a)) x")
      case None
      then show ?thesis using P3 by blast
    next
      case (Some y)
      then have "fmrestrict_set vs s = fmrestrict_set vs (s ++\<^sub>f snd a)"
        using assms
        by (simp add: state_succ_def fmap_add_ltr_def)
      then have "fmlookup (fmrestrict_set vs s) = fmlookup (fmrestrict_set vs (s ++\<^sub>f snd a))"
        by auto
      then have 1: "
            fmlookup (fmrestrict_set vs s) x
            = (if x \<in> vs then fmlookup (s ++\<^sub>f snd a) x else None)
          "
        using fmlookup_restrict_set
        by metis
      then show ?thesis
      proof (cases "x \<in> vs")
        case True
        then have "fmlookup (fmrestrict_set vs s) x = fmlookup (s ++\<^sub>f snd a) x"
          using True 1
          by auto
        then show ?thesis
          using Some fmadd.rep_eq fmlookup_restrict_set map_add_Some_iff
          by (metis (mono_tags, lifting))
      next
        case False
        then have 1: "fmlookup (fmrestrict_set vs s) x = None"
          using False "1"
          by auto
        then show ?thesis
          using 1 False
          by auto
      qed
    qed
  }
  then have "(fmlookup (fmrestrict_set vs (snd a)) \<subseteq>\<^sub>m fmlookup (fmrestrict_set vs s))"
    using map_le_def
    by blast
  then show ?thesis
    using fmsubset.rep_eq
    by blast
qed


\<comment> \<open>NOTE type of `a` had to be fixed.\<close>
lemma sat_precond_as_proj_3:
  fixes s and a :: "('a, 'b) fmap \<times> ('a, 'b) fmap" and vs
  assumes "(fmdom' (fmrestrict_set vs (snd a)) = {})"
  shows "((fmrestrict_set vs (state_succ s a)) = (fmrestrict_set vs s))"
proof -
  have "fmdom' (fmrestrict_set vs (fmrestrict_set vs (snd a))) = {}"
    using assms fmrestrict_set_dom fmrestrict_set_empty fmrestrict_set_null
    by metis
  {
    fix x
    assume C: "x \<in> fmdom' (snd a) \<and> x \<in> vs"
    then have a: "x \<in> fmdom' (snd a)" "x \<in> vs"
      using C
      by blast+
    then have "fmlookup (snd a) x \<noteq> None"
      using fmdom'_notI
      by metis
    then have "fmlookup (fmrestrict_set vs (snd a)) x \<noteq> None"
      using a(2)
      by force
    then have "x \<in> fmdom' (fmrestrict_set vs (snd a))"
      using fmdom'_notD
      by metis
    then have "fmdom' (fmrestrict_set vs (snd a)) \<noteq> {}"
      by blast
    then have False
      using assms
      by blast
  }
  then have "\<forall>x. \<not>(x \<in> fmdom' (snd a) \<and> x \<in> vs)"
    by blast
  then have 1: "fmdom' (snd a) \<inter> vs = {}"
    by blast
  have "disjnt (fmdom' (snd a)) vs"
    using 1 disjnt_def
    by blast
  then show ?thesis
    using 1 disj_imp_eq_proj_exec
    by metis
qed


\<comment> \<open>NOTE type for `a` had to be fixed (type mismatch in goal).\<close>
\<comment> \<open>TODO showcase (quick win with simp).\<close>
lemma proj_eq_proj_exec_eq:
  fixes s s' vs and a :: "('a, 'b) fmap \<times> ('a, 'b) fmap" and a'
  assumes "((fmrestrict_set vs s) = (fmrestrict_set vs s'))" "((fst a \<subseteq>\<^sub>f s) = (fst a' \<subseteq>\<^sub>f s'))"
    "(fmrestrict_set vs (snd a) = fmrestrict_set vs (snd a'))"
  shows "(fmrestrict_set vs (state_succ s a) = fmrestrict_set vs (state_succ s' a'))"
  using assms
  by (simp add: fmap_add_ltr_def state_succ_def)


lemma empty_eff_exec_eq:
  fixes s a
  assumes "(fmdom' (snd a) = {})"
  shows "(state_succ s a = s)"
  using assms
  unfolding state_succ_def fmap_add_ltr_def
  by (metis fmadd_empty(2) fmrestrict_set_dom fmrestrict_set_null)


lemma exec_as_proj_valid_2:
  fixes a
  assumes "a \<in> PROB"
  shows "(action_dom (fst a) (snd a) \<subseteq> prob_dom PROB)"
  using assms
  by (simp add: FDOM_eff_subset_prob_dom_pair FDOM_pre_subset_prob_dom_pair action_dom_def)


lemma valid_filter_valid_as:
  assumes "(as \<in> valid_plans PROB)"
  shows "(filter P as \<in> valid_plans PROB)"
  using assms
  by(auto simp: valid_plans_def)


lemma sublist_valid_plan:
  assumes "(subseq as' as)" "(as \<in> valid_plans PROB)"
  shows "(as' \<in> valid_plans PROB)"
  using assms
  by (auto simp: valid_plans_def) (meson fset_mp fset_of_list_elem sublist_subset subsetCE)


lemma prob_subset_dom_subset:
  assumes "PROB1 \<subseteq> PROB2"
  shows "(prob_dom PROB1 \<subseteq> prob_dom PROB2)"
  using assms
  by (auto simp add: prob_dom_def)


lemma state_succ_valid_act_disjoint:
  assumes "(a \<in> PROB)" "(vs \<inter> (prob_dom PROB) = {})"
  shows "(fmrestrict_set vs (state_succ s a) = fmrestrict_set vs s)"
  using assms
  by (smt
      FDOM_eff_subset_prob_dom_pair disj_imp_eq_proj_exec inf.absorb1
      inf_bot_right inf_commute inf_left_commute
      )


lemma exec_valid_as_disjoint:
  fixes s
  assumes "(vs \<inter> (prob_dom PROB) = {})" "(as \<in> valid_plans PROB)"
  shows "(fmrestrict_set vs (exec_plan s as) = fmrestrict_set vs s)"
  using assms
proof (induction as arbitrary: s vs PROB)
  case (Cons a as)
  then show ?case
    by (metis exec_plan.simps(2) state_succ_valid_act_disjoint valid_plan_valid_head
        valid_plan_valid_tail)
qed simp


definition state_successors where
  "state_successors PROB s \<equiv> ((state_succ s ` PROB) - {s})"


subsection "State Spaces"


definition stateSpace where
  "stateSpace ss vs \<equiv> (\<forall>s. s \<in> ss \<longrightarrow> (fmdom' s = vs))"


lemma EQ_SS_DOM:
  assumes "\<not>(ss = {})" "(stateSpace ss vs1)" "(stateSpace ss vs2)"
  shows "(vs1 = vs2)"
  using assms
  by (auto simp: stateSpace_def)


\<comment> \<open>NOTE Name 'dom' changed to 'domain' because of name clash with 'Map.dom'.\<close>
lemma FINITE_SS:
  fixes ss :: "('a, bool) fmap set"
  assumes "\<not>(ss = {})" "(stateSpace ss domain)"
  shows "finite ss"
proof -
  have 1: "stateSpace ss domain = (\<forall>s. s \<in> ss \<longrightarrow> (fmdom' s = domain))"
    by (simp add: stateSpace_def)
  {
    fix s
    assume P1: "s \<in> ss"
    have "fmdom' s = domain"
      using assms 1 P1
      by blast
    then have "s \<in> {s. fmdom' s = domain}"
      by auto
  }
  then have 2: "ss \<subseteq> {s. fmdom' s = domain}"
    by blast
      \<comment> \<open>TODO add lemma (finite (fmdom' s))\<close>
  then have "finite domain"
    using 1 assms
    by fastforce
  then have "finite {s :: 'a state. fmdom' s = domain}"
    using FINITE_states
    by blast
  then show ?thesis
    using 2 finite_subset
    by auto
qed


lemma disjoint_effects_no_effects:
  fixes s
  assumes "(\<forall>a. ListMem a as \<longrightarrow> (fmdom' (fmrestrict_set vs (snd a)) = {}))"
  shows "(fmrestrict_set vs (exec_plan s as) = (fmrestrict_set vs s))"
  using assms
proof (induction as arbitrary: s vs)
  case (Cons a as)
  then have "ListMem a (a # as)"
    using elem
    by fast
  then have "fmdom' (fmrestrict_set vs (snd a)) = {}"
    using Cons.prems(1)
    by blast
  then have "fmrestrict_set vs (state_succ s a) = fmrestrict_set vs s"
    using sat_precond_as_proj_3
    by blast
  then show ?case
    by (simp add: Cons.IH Cons.prems insert)
qed auto


subsection "Needed Asses"


\<comment> \<open>NOTE name shortened.\<close>
definition action_needed_vars where
  "action_needed_vars a s \<equiv> {v. (v \<in> fmdom' s) \<and> (v \<in> fmdom' (fst a))
    \<and> (fmlookup (fst a) v = fmlookup s v)}"
  \<comment> \<open>NOTE name shortened to 'action\_needed\_asses'.\<close>
definition action_needed_asses where
  "action_needed_asses a s \<equiv> fmrestrict_set (action_needed_vars a s) s"


\<comment> \<open>NOTE type for 'a' had to be fixed (type mismatch in goal).\<close>
lemma act_needed_asses_submap_succ_submap:
  fixes a s1 s2
  assumes "(action_needed_asses a s2 \<subseteq>\<^sub>f action_needed_asses a s1)" "(s1 \<subseteq>\<^sub>f s2)"
  shows "(state_succ s1 a \<subseteq>\<^sub>f state_succ s2 a)"
  using assms
  unfolding state_succ_def
proof (auto)
  assume P1: "action_needed_asses a s2 \<subseteq>\<^sub>f action_needed_asses a s1" "s1 \<subseteq>\<^sub>f s2" "fst a \<subseteq>\<^sub>f s1"
    "fst a \<subseteq>\<^sub>f s2"
  then show "snd a ++ s1 \<subseteq>\<^sub>f snd a ++ s2"
    using submap_imp_state_succ_submap_b
    by blast
next
  assume P2: "action_needed_asses a s2 \<subseteq>\<^sub>f action_needed_asses a s1" "s1 \<subseteq>\<^sub>f s2" "fst a \<subseteq>\<^sub>f s1"
    "\<not> fst a \<subseteq>\<^sub>f s2"
  then show "snd a ++ s1 \<subseteq>\<^sub>f s2"
    using submap_imp_state_succ_submap_a
    by blast
next
  assume P3: "action_needed_asses a s2 \<subseteq>\<^sub>f action_needed_asses a s1" "s1 \<subseteq>\<^sub>f s2" "\<not> fst a \<subseteq>\<^sub>f s1"
    "fst a \<subseteq>\<^sub>f s2"
  let ?vs1="{v \<in> fmdom' s1. v \<in> fmdom' (fst a) \<and> fmlookup (fst a) v = fmlookup s1 v}"
  let ?vs2="{v \<in> fmdom' s2. v \<in> fmdom' (fst a) \<and> fmlookup (fst a) v = fmlookup s2 v}"
  let ?f="fmrestrict_set ?vs1 s1"
  let ?g="fmrestrict_set ?vs2 s2"
  have 1: "fmdom' ?f = ?vs1" "fmdom' ?g = ?vs2"
    unfolding action_needed_asses_def action_needed_vars_def fmdom'_restrict_set_precise
    by blast+
  have 2: "fmlookup ?g \<subseteq>\<^sub>m fmlookup ?f"
    using P3(1)
    unfolding action_needed_asses_def action_needed_vars_def
    using fmsubset.rep_eq
    by blast
  {
    {
      fix v
      assume P3_1: "v \<in> fmdom' ?g"
      then have "v \<in> fmdom' s2" "v \<in> fmdom' (fst a)" "fmlookup (fst a) v = fmlookup s2 v"
        using 1
        by simp+
      then have "fmlookup (fst a) v = fmlookup ?g v"
        by simp
      then have "fmlookup (fst a) v = fmlookup ?f v"
        using 2
        by (metis (mono_tags, lifting) P3_1 domIff fmdom'_notI map_le_def)
    }
    then have i: "fmlookup (fst a) \<subseteq>\<^sub>m fmlookup ?f"
      using P3(4) 1(2)
      by (smt domIff fmdom'_notD fmsubset.rep_eq map_le_def mem_Collect_eq)
    {
      fix v
      assume P3_2: "v \<in> dom (fmlookup (fst a))"
      then have "fmlookup (fst a) v = fmlookup ?f v"
        using i
        by (meson domIff fmdom'_notI map_le_def)
      then have "v \<in> ?vs1"
        using P3_2 1(1)
        by (metis (no_types, lifting) domIff fmdom'_notD)
      then have "fmlookup (fst a) v = fmlookup s1 v"
        by blast
    }
    then have "fst a \<subseteq>\<^sub>f s1"
      by (simp add: map_le_def fmsubset.rep_eq)
  }
  then show "s1 \<subseteq>\<^sub>f snd a ++ s2"
    using P3(3)
    by simp
qed


\<comment> \<open>NOTE added lemma.\<close>
\<comment> \<open>TODO refactor.\<close>
lemma as_needed_asses_submap_exec_i:
  fixes a s
  assumes "v \<in> fmdom' (action_needed_asses a s)"
  shows "
    fmlookup (action_needed_asses a s) v = fmlookup s v
    \<and> fmlookup (action_needed_asses a s) v = fmlookup (fst a) v"
  using assms
  unfolding action_needed_asses_def action_needed_vars_def
  using fmdom'_notI fmlookup_restrict_set
  by (smt mem_Collect_eq)

\<comment> \<open>NOTE added lemma.\<close>
\<comment> \<open>TODO refactor.\<close>
lemma as_needed_asses_submap_exec_ii:
  fixes f g v
  assumes "v \<in> fmdom' f" "f \<subseteq>\<^sub>f g"
  shows "fmlookup f v = fmlookup g v"
  using assms
  by (meson fmdom'_notI fmdom_notD fmsubset_eq)

\<comment> \<open>NOTE added lemma.\<close>
\<comment> \<open>TODO refactor.\<close>
lemma as_needed_asses_submap_exec_iii:
  fixes f g v
  shows "
    fmdom' (action_needed_asses a s)
    = {v \<in> fmdom' s. v \<in> fmdom' (fst a) \<and> fmlookup (fst a) v = fmlookup s v}"
  unfolding action_needed_asses_def action_needed_vars_def
  by (simp add: Set.filter_def fmfilter_alt_defs(4))

\<comment> \<open>NOTE added lemma.\<close>
lemma as_needed_asses_submap_exec_iv:
  fixes f a v
  assumes "v \<in> fmdom' (action_needed_asses a s)"
  shows "
    fmlookup (action_needed_asses a s) v = fmlookup s v
    \<and> fmlookup (action_needed_asses a s) v = fmlookup (fst a) v
    \<and> fmlookup (fst a) v = fmlookup s v"
  using assms
proof -
  have 1: "v \<in> {v \<in> fmdom' s. v \<in> fmdom' (fst a) \<and> fmlookup (fst a) v = fmlookup s v}"
    using assms as_needed_asses_submap_exec_iii
    by metis
  then have 2: "fmlookup (action_needed_asses a s) v = fmlookup s v"
    unfolding action_needed_asses_def action_needed_vars_def
    by force
  moreover have 3: "fmlookup (action_needed_asses a s) v = fmlookup (fst a) v"
    using 1 2
    by simp
  moreover have "fmlookup (fst a) v = fmlookup s v"
    using 2 3
    by argo
  ultimately show ?thesis
    by blast
qed

\<comment> \<open>NOTE added lemma.\<close>
\<comment> \<open>TODO refactor (into Fmap\_Utils.thy).\<close>
lemma as_needed_asses_submap_exec_v:
  fixes f g v
  assumes "v \<in> fmdom' f" "f \<subseteq>\<^sub>f g"
  shows "v \<in> fmdom' g"
proof -
  obtain b where 1: "fmlookup f v = b" "b \<noteq> None"
    using assms(1)
    by (meson fmdom'_notI)
  then have "fmlookup g v = b"
    using as_needed_asses_submap_exec_ii[OF assms]
    by argo
  then show ?thesis
    using 1 fmdom'_notD
    by fastforce
qed

\<comment> \<open>NOTE added lemma.\<close>
\<comment> \<open>TODO refactor.\<close>
lemma as_needed_asses_submap_exec_vi:
  fixes a s1 s2 v
  assumes "v \<in> fmdom' (action_needed_asses a s1)"
    "(action_needed_asses a s1) \<subseteq>\<^sub>f (action_needed_asses a s2)"
  shows
    "(fmlookup (action_needed_asses a s1) v) = fmlookup (fst a) v
    \<and> (fmlookup (action_needed_asses a s2) v) = fmlookup (fst a) v \<and>
    fmlookup s1 v = fmlookup (fst a) v \<and> fmlookup s2 v = fmlookup (fst a) v"
  using assms
proof -
  have 1:
    "fmlookup (action_needed_asses a s1) v = fmlookup s1 v"
    "fmlookup (action_needed_asses a s1) v = fmlookup (fst a) v"
    "fmlookup (fst a) v = fmlookup s1 v"
    using as_needed_asses_submap_exec_iv[OF assms(1)]
    by blast+
  moreover {
    have "fmlookup (action_needed_asses a s1) v = fmlookup (action_needed_asses a s2) v"
      using as_needed_asses_submap_exec_ii[OF assms]
      by simp
    then have "fmlookup (action_needed_asses a s2) v = fmlookup (fst a) v"
      using 1(2)
      by argo
  }
  note 2 = this
  moreover {
    have "v \<in> fmdom' (action_needed_asses a s2)"
      using as_needed_asses_submap_exec_v[OF assms]
      by simp
    then have "fmlookup s2 v = fmlookup (action_needed_asses a s2) v"
      using as_needed_asses_submap_exec_i
      by metis
    also have "\<dots> = fmlookup (fst a) v"
      using 2
      by simp
    finally have "fmlookup s2 v = fmlookup (fst a) v"
      by simp
  }
  ultimately show ?thesis
    by argo
qed

\<comment> \<open>TODO refactor.\<close>
\<comment> \<open>NOTE added lemma.\<close>
lemma as_needed_asses_submap_exec_vii:
  fixes f g v
  assumes "\<forall>v \<in> fmdom' f. fmlookup f v = fmlookup g v"
  shows "f \<subseteq>\<^sub>f g"
proof -
  {
    fix v
    assume a: "v \<in> fmdom' f"
    then have "v \<in> dom (fmlookup f)"
      by simp
    moreover have "fmlookup f v = fmlookup g v"
      using assms a
      by blast
    ultimately have "v \<in> dom (fmlookup f) \<longrightarrow> fmlookup f v = fmlookup g v"
      by blast
  }
  then have "fmlookup f \<subseteq>\<^sub>m fmlookup g"
    by (simp add: map_le_def)
  then show ?thesis
    by (simp add: fmsubset.rep_eq)
qed

\<comment> \<open>TODO refactor.\<close>
\<comment> \<open>NOTE added lemma.\<close>
lemma as_needed_asses_submap_exec_viii:
  fixes f g v
  assumes "f \<subseteq>\<^sub>f g"
  shows "\<forall>v \<in> fmdom' f. fmlookup f v = fmlookup g v"
proof -
  have 1: "fmlookup f \<subseteq>\<^sub>m fmlookup g"
    using assms
    by (simp add: fmsubset.rep_eq)
  {
    fix v
    assume "v \<in> fmdom' f"
    then have "v \<in> dom (fmlookup f)"
      by simp
    then have "fmlookup f v = fmlookup g v"
      using 1 map_le_def
      by metis
  }
  then show ?thesis
    by blast
qed

\<comment> \<open>NOTE added lemma.\<close>
lemma as_needed_asses_submap_exec_viii':
  fixes f g v
  assumes "f \<subseteq>\<^sub>f g"
  shows "fmdom' f \<subseteq> fmdom' g"
  using assms as_needed_asses_submap_exec_v subsetI
  by metis

\<comment> \<open>NOTE added lemma.\<close>
\<comment> \<open>TODO refactor.\<close>
lemma as_needed_asses_submap_exec_ix:
  fixes f g
  shows "f \<subseteq>\<^sub>f g = (\<forall>v \<in> fmdom' f. fmlookup f v = fmlookup g v)"
  using as_needed_asses_submap_exec_vii  as_needed_asses_submap_exec_viii
  by metis

\<comment> \<open>NOTE added lemma.\<close>
lemma as_needed_asses_submap_exec_x:
  fixes f a v
  assumes "v \<in> fmdom' (action_needed_asses a f)"
  shows "v \<in> fmdom' (fst a) \<and> v \<in> fmdom' f \<and> fmlookup (fst a) v = fmlookup f v"
  using assms
  unfolding action_needed_asses_def action_needed_vars_def
  using as_needed_asses_submap_exec_i assms
  by (metis fmdom'_notD fmdom'_notI)

\<comment> \<open>NOTE added lemma.\<close>
\<comment> \<open>TODO refactor.\<close>
lemma as_needed_asses_submap_exec_xi:
  fixes v a f g
  assumes "v \<in> fmdom' (action_needed_asses a (f ++ g))" "v \<in> fmdom' f"
  shows "
    fmlookup (action_needed_asses a (f ++ g)) v = fmlookup f v
    \<and> fmlookup (action_needed_asses a (f ++ g)) v = fmlookup (fst a) v"
proof -
  have 1: "v \<in> {v \<in> fmdom' (f ++ g). v \<in> fmdom' (fst a) \<and> fmlookup (fst a) v = fmlookup (f ++ g) v}"
    using as_needed_asses_submap_exec_x[OF assms(1)]
    by blast
  {
    have "v |\<in>| fmdom f"
      using assms(2)
      by (meson fmdom'_notI fmdom_notD)
    then have "fmlookup (f ++ g) v = fmlookup f v"
      unfolding fmap_add_ltr_def fmlookup_add
      by simp
  }
  note 2 = this
  {

    have "fmlookup (action_needed_asses a (f ++ g)) v = fmlookup (f ++ g) v"
      unfolding action_needed_asses_def action_needed_vars_def
      using 1
      by force
    then have "fmlookup (action_needed_asses a (f ++ g)) v = fmlookup f v"
      using 2
      by simp
  }
  note 3 = this
  moreover {
    have "fmlookup (fst a) v = fmlookup (f ++ g) v"
      using 1
      by simp
    also have "\<dots> = fmlookup f v"
      using 2
      by simp
    also have "\<dots> = fmlookup (action_needed_asses a (f ++ g)) v"
      using 3
      by simp
    finally have "fmlookup (action_needed_asses a (f ++ g)) v = fmlookup (fst a) v"
      by simp
  }
  ultimately show ?thesis
    by blast
qed

\<comment> \<open>NOTE added lemma.\<close>
\<comment> \<open>TODO refactor (into Fmap\_Utils.thy).\<close>
lemma as_needed_asses_submap_exec_xii:
  fixes f g v
  assumes "v \<in> fmdom' f"
  shows "fmlookup (f ++ g) v = fmlookup f v"
proof -
  have "v |\<in>| fmdom f"
    using assms(1) fmdom'_notI fmdom_notD
    by metis
  then show ?thesis
    unfolding fmap_add_ltr_def
    using fmlookup_add
    by force
qed

\<comment> \<open>NOTE added lemma.\<close>
lemma as_needed_asses_submap_exec_xii':
  fixes f g v
  assumes "v \<notin> fmdom' f" "v \<in> fmdom' g"
  shows "fmlookup (f ++ g) v = fmlookup g v"
proof -
  have "\<not>(v |\<in>| fmdom f)"
    using assms(1) fmdom'_notI fmdom_notD
    by fastforce
  moreover have "v |\<in>| fmdom g"
    using assms(2) fmdom'_notI fmdom_notD
    by metis
  ultimately show ?thesis
    unfolding fmap_add_ltr_def
    using fmlookup_add
    by simp
qed


\<comment> \<open>NOTE showcase.\<close>
lemma as_needed_asses_submap_exec:
  fixes s1 s2
  assumes "(s1 \<subseteq>\<^sub>f s2)"
    "(\<forall>a. ListMem a as \<longrightarrow> (action_needed_asses a s2 \<subseteq>\<^sub>f action_needed_asses a s1))"
  shows "(exec_plan s1 as \<subseteq>\<^sub>f exec_plan s2 as)"
  using assms
proof (induction as arbitrary: s1 s2)
  case (Cons a as)
    \<comment> \<open>Proof the premises of the induction hypothesis for 'state\_succ s1 a' and 'state\_succ s2 a'.\<close>
  {
    then have "action_needed_asses a s2 \<subseteq>\<^sub>f action_needed_asses a s1"
      using Cons.prems(2) elem
      by metis
    then have "state_succ s1 a \<subseteq>\<^sub>f state_succ s2 a"
      using Cons.prems(1) act_needed_asses_submap_succ_submap
      by blast
  }
  note 1 = this
  moreover {
    fix a'
    assume P: "ListMem a' as"
      \<comment> \<open>Show the goal by rule 'as\_needed\_asses\_submap\_exec\_ix'.\<close>
    let ?f="action_needed_asses a' (state_succ s2 a)"
    let ?g="action_needed_asses a' (state_succ s1 a)"
    {
      fix v
      assume P_1: "v \<in> fmdom' ?f"
      then have "fmlookup ?f v = fmlookup ?g v"
        unfolding state_succ_def
        text \<open> Split cases on the if-then branches introduced by the definition of 'state\_succ'.\<close>
      proof (auto)
        assume P_1_1: "v \<in> fmdom' (action_needed_asses a' (snd a ++ s2))" "fst a \<subseteq>\<^sub>f s2"
          "fst a \<subseteq>\<^sub>f s1"
        have i: "action_needed_asses a' s2 \<subseteq>\<^sub>f action_needed_asses a' s1"
          using Cons.prems(2) P insert
          by fast
        then show "
            fmlookup (action_needed_asses a' (snd a ++ s2)) v
            = fmlookup (action_needed_asses a' (snd a ++ s1)) v"
        proof (cases "v \<in> fmdom' ?g")
          case true: True
          then have A:
            "v \<in> fmdom' (fst a') \<and> v \<in> fmdom' (snd a ++ s1)
                \<and> fmlookup (fst a') v = fmlookup (snd a ++ s1) v"
            using as_needed_asses_submap_exec_x[OF true]
            unfolding state_succ_def
            using P_1_1(3)
            by simp
          then have B:
            "v \<in> fmdom' (fst a') \<and> v \<in> fmdom' (snd a ++ s2)
                \<and> fmlookup (fst a') v = fmlookup (snd a ++ s2) v"
            using as_needed_asses_submap_exec_x[OF P_1]
            unfolding state_succ_def
            using P_1_1(2)
            by simp
          then show ?thesis
          proof (cases "v \<in> fmdom' (snd a)")
            case True
            then have I:
              "fmlookup (snd a ++ s2) v = fmlookup (snd a) v"
              "fmlookup (snd a ++ s1) v = fmlookup (snd a) v"
              using as_needed_asses_submap_exec_xii
              by fast+
            moreover {
              have "fmlookup ?f v = fmlookup (snd a ++ s2) v"
                using as_needed_asses_submap_exec_iv[OF P_1]
                unfolding state_succ_def
                using P_1_1(2)
                by presburger
              then have "fmlookup ?f v = fmlookup (snd a) v"
                using I(1)
                by argo
            }
            moreover {
              have "fmlookup ?g v = fmlookup (snd a ++ s1) v"
                using as_needed_asses_submap_exec_iv[OF true]
                unfolding state_succ_def
                using P_1_1(3)
                by presburger
              then have "fmlookup ?g v = fmlookup (snd a) v"
                using I(2)
                by argo
            }
            ultimately show ?thesis
              unfolding state_succ_def
              using P_1_1(2, 3)
              by presburger
          next
            case False
            then have I: "v \<in> fmdom' s1" "v \<in> fmdom' s2"
              using A B
              unfolding fmap_add_ltr_def fmdom'_add
              by blast+
            {
              have "fmlookup ?g v = fmlookup (snd a ++ s1) v"
                using as_needed_asses_submap_exec_iv[OF true]
                unfolding state_succ_def
                using P_1_1(3)
                by presburger
              then have "fmlookup ?g v = fmlookup s1 v"
                using as_needed_asses_submap_exec_xii'[OF False I(1)]
                by simp
              moreover {
                have "fmlookup (snd a ++ s1) v = fmlookup s1 v"
                  using as_needed_asses_submap_exec_xii'[OF False I(1)]
                  by simp
                moreover from \<open>fmlookup (snd a ++ s1) v = fmlookup s1 v\<close>
                have "fmlookup (fst a') v = fmlookup s1 v"
                  using A(1)
                  by argo
                ultimately have "fmlookup (action_needed_asses a' s1) v = fmlookup s1 v"
                  using A(1) I(1)
                  unfolding action_needed_asses_def action_needed_vars_def
                    fmlookup_restrict_set
                  by simp
              }
              ultimately have "fmlookup ?g v = fmlookup (action_needed_asses a' s1) v"
                by argo
            }
            note II = this
            {
              have "fmlookup ?f v = fmlookup (snd a ++ s2) v"
                using as_needed_asses_submap_exec_iv[OF P_1]
                unfolding state_succ_def
                using P_1_1(2)
                by presburger
              moreover from \<open>fmlookup ?f v = fmlookup (snd a ++ s2) v\<close>
              have \<alpha>: "fmlookup ?f v = fmlookup s2 v"
                using as_needed_asses_submap_exec_xii'[OF False I(2)]
                by argo
              ultimately have "fmlookup (snd a ++ s2) v = fmlookup s2 v"
                by argo
              moreover {
                from \<open>fmlookup (snd a ++ s2) v = fmlookup s2 v\<close>
                have "fmlookup (fst a') v = fmlookup s2 v"
                  using B(1)
                  by argo
                then have "fmlookup (action_needed_asses a' s2) v = fmlookup s2 v"
                  using B(1) I(2)
                  unfolding action_needed_asses_def action_needed_vars_def
                    fmlookup_restrict_set
                  by simp
              }
              ultimately have "fmlookup ?f v = fmlookup (action_needed_asses a' s2) v"
                using \<alpha>
                by argo
            }
            note III = this
            {
              have "v \<in> fmdom' (action_needed_asses a' s2)"
              proof -
                have "fmlookup (fst a') v = fmlookup s1 v"
                  by (simp add: A False I(1) as_needed_asses_submap_exec_xii')
                then show ?thesis
                  by (simp add: A Cons.prems(1) I(1, 2)
                      as_needed_asses_submap_exec_ii as_needed_asses_submap_exec_iii)
              qed
              then have "
                      fmlookup (action_needed_asses a' s2) v
                      = fmlookup (action_needed_asses a' s1) v"
                using i as_needed_asses_submap_exec_ix[of "action_needed_asses a' s2"
                    "action_needed_asses a' s1"]
                by blast
            }
            note IV = this
            {
              have "fmlookup ?f v = fmlookup (action_needed_asses a' s2) v"
                using III
                by simp
              also have "\<dots> = fmlookup (action_needed_asses a' s1) v"
                using IV
                by simp
              finally have "\<dots> = fmlookup ?g v"
                using II
                by simp
            }
            then show ?thesis
              unfolding action_needed_asses_def action_needed_vars_def state_succ_def
              using P_1_1 A B
              by simp
          qed
        next
          case false: False
          have A:
            "v \<in> fmdom' (fst a') \<and> v \<in> fmdom' (snd a ++ s2)
                \<and> fmlookup (fst a') v = fmlookup (snd a ++ s2) v"
            using as_needed_asses_submap_exec_x[OF P_1]
            unfolding state_succ_def
            using P_1_1(2)
            by simp
          from false have B:
            "\<not>(v \<in> fmdom' (snd a ++ s1)) \<or> \<not>(fmlookup (fst a') v = fmlookup (snd a ++ s1) v)"
            by (simp add: A P_1_1(3) as_needed_asses_submap_exec_iii state_succ_def)
          then show ?thesis
          proof (cases "v \<in> fmdom' (snd a)")
            case True
            then have I: "v \<in> fmdom' (snd a ++ s1)"
              unfolding fmap_add_ltr_def fmdom'_add
              by simp
            {
              from True have
                "fmlookup (snd a ++ s2) v = fmlookup (snd a) v"
                "fmlookup (snd a ++ s1) v = fmlookup (snd a) v"
                using as_needed_asses_submap_exec_xii
                by fast+
              then have "fmlookup (snd a ++ s1) v = fmlookup (snd a ++ s2) v"
                by auto
              also have " \<dots> = fmlookup (fst a') v"
                using A
                by simp
              finally have "fmlookup (snd a ++ s1) v = fmlookup (fst a') v"
                by simp
            }
            then show ?thesis using B I
              by presburger
          next
            case False
            then have I: "v \<in> fmdom' s2"
              using A unfolding fmap_add_ltr_def fmdom'_add
              by blast
            {
              from P_1 have "fmlookup ?f v \<noteq> None"
                by (meson fmdom'_notI)
              moreover from false
              have "fmlookup ?g v = None"
                by (simp add: fmdom'_notD)
              ultimately have "fmlookup ?f v \<noteq> fmlookup ?g v"
                by simp
            }
            moreover
            {
              {
                from P_1_1(2) have "state_succ s2 a = snd a ++ s2"
                  unfolding state_succ_def
                  by simp
                moreover from \<open>state_succ s2 a = snd a ++ s2\<close> have
                  "fmlookup (state_succ s2 a) v = fmlookup s2 v"
                  using as_needed_asses_submap_exec_xii'[OF False I]
                  by simp
                ultimately have "fmlookup ?f v = fmlookup (action_needed_asses a' s2) v"
                  unfolding action_needed_asses_def action_needed_vars_def
                  by (simp add: A I)
              }
              note I = this
              moreover {
                from P_1_1(3) have "state_succ s1 a = snd a ++ s1"
                  unfolding state_succ_def
                  by simp
                moreover from \<open>state_succ s1 a = snd a ++ s1\<close> False
                have "fmlookup (state_succ s1 a) v = fmlookup s1 v"
                  unfolding fmap_add_ltr_def
                  using fmlookup_add
                  by (simp add: fmdom'_alt_def fmember.rep_eq)
                ultimately have "fmlookup ?g v = fmlookup (action_needed_asses a' s1) v"
                  unfolding action_needed_asses_def action_needed_vars_def
                  using FDOM_state_succ_subset
                  by auto
              }
              moreover {
                have "v \<in> fmdom' (action_needed_asses a' s2)"
                proof -
                  have "v \<in> fmdom' s2 \<union> fmdom' (snd a)"
                    by (metis (no_types) A FDOM_state_succ_subset P_1_1(2) state_succ_def subsetCE)
                  then show ?thesis
                    by (simp add: A False as_needed_asses_submap_exec_iii as_needed_asses_submap_exec_xii')
                qed
                then have "
                      fmlookup (action_needed_asses a' s2) v
                      = fmlookup (action_needed_asses a' s1) v"
                  using i as_needed_asses_submap_exec_ix[of "action_needed_asses a' s2"
                      "action_needed_asses a' s1"]
                  by blast
              }
              ultimately have "fmlookup ?f v = fmlookup ?g v"
                by simp
            }
            ultimately show ?thesis
              by simp
          qed
        qed
      next
        assume P2: "v \<in> fmdom' (action_needed_asses a' (snd a ++ s2))" "fst a \<subseteq>\<^sub>f s2"
          "\<not> fst a \<subseteq>\<^sub>f s1"
        then show "
            fmlookup (action_needed_asses a' (snd a ++ s2)) v
            = fmlookup (action_needed_asses a' s1) v"
        proof -
          obtain aa :: "('a, 'b) fmap \<Rightarrow> ('a, 'b) fmap \<Rightarrow> 'a" where
            "\<forall>x0 x1. (\<exists>v2. v2 \<in> fmdom' x1
                \<and> fmlookup x1 v2 \<noteq> fmlookup x0 v2) = (aa x0 x1 \<in> fmdom' x1
                \<and> fmlookup x1 (aa x0 x1) \<noteq> fmlookup x0 (aa x0 x1))"
            by moura
          then have f1: "\<forall>f fa. aa fa f \<in> fmdom' f
              \<and> fmlookup f (aa fa f) \<noteq> fmlookup fa (aa fa f) \<or> f \<subseteq>\<^sub>f fa"
            by (meson as_needed_asses_submap_exec_vii)
          then have f2: "aa s1 (fst a) \<in> fmdom' (fst a)
              \<and> fmlookup (fst a) (aa s1 (fst a)) \<noteq> fmlookup s1 (aa s1 (fst a))"
            using P2(3) by blast
          then have "aa s1 (fst a) \<in> fmdom' s2"
            by (metis (full_types) P2(2) as_needed_asses_submap_exec_v)
          then have "aa s1 (fst a) \<in> fmdom' (action_needed_asses a s2)"
            using f2 by (simp add: P2(2) as_needed_asses_submap_exec_iii
                as_needed_asses_submap_exec_viii)
          then show ?thesis
            using f1 by (metis (no_types) Cons.prems(2) P2(3) as_needed_asses_submap_exec_vi elem)
        qed
      next
        assume P3: "v \<in> fmdom' (action_needed_asses a' s2)" "\<not> fst a \<subseteq>\<^sub>f s2" "fst a \<subseteq>\<^sub>f s1"
        then show "
            fmlookup (action_needed_asses a' s2) v
            = fmlookup (action_needed_asses a' (snd a ++ s1)) v"
          using Cons.prems(1) submap_imp_state_succ_submap_a
          by blast
      next
        assume P4: "v \<in> fmdom' (action_needed_asses a' s2)" "\<not> fst a \<subseteq>\<^sub>f s2" "\<not> fst a \<subseteq>\<^sub>f s1"
        then show "
            fmlookup (action_needed_asses a' s2) v
            = fmlookup (action_needed_asses a' s1) v"
          by (simp add: Cons.prems(2) P as_needed_asses_submap_exec_ii insert)
      qed
    }
    then have a: "?f \<subseteq>\<^sub>f ?g"
      using as_needed_asses_submap_exec_ix
      by blast
  }
  note 2 = this
  then show ?case
    unfolding exec_plan.simps
    using Cons.IH[of "state_succ s1 a" "state_succ s2 a", OF 1]
    by blast
qed simp


\<comment> \<open>NOTE name shortened.\<close>
definition system_needed_vars where
  "system_needed_vars PROB s \<equiv> (\<Union>{action_needed_vars a s | a. a \<in> PROB})"

\<comment> \<open>NOTE name shortened.\<close>
definition system_needed_asses where
  "system_needed_asses PROB s \<equiv> (fmrestrict_set (system_needed_vars PROB s) s)"


lemma action_needed_vars_subset_sys_needed_vars_subset:
  assumes "(a \<in> PROB)"
  shows "(action_needed_vars a s \<subseteq> system_needed_vars PROB s)"
  using assms
  by (auto simp: system_needed_vars_def) (metis surjective_pairing)


lemma action_needed_asses_submap_sys_needed_asses:
  assumes "(a \<in> PROB)"
  shows "(action_needed_asses a s \<subseteq>\<^sub>f system_needed_asses PROB s)"
proof -
  have "action_needed_asses a s = fmrestrict_set (action_needed_vars a s) s"
    unfolding action_needed_asses_def
    by simp
  then have "system_needed_asses PROB s = (fmrestrict_set (system_needed_vars PROB s) s)"
    unfolding system_needed_asses_def
    by simp
  then have 1: "action_needed_vars a s \<subseteq> system_needed_vars PROB s"
    unfolding action_needed_vars_subset_sys_needed_vars_subset
    using assms action_needed_vars_subset_sys_needed_vars_subset
    by fast
  {
    fix x
    assume P1: "x \<in> dom (fmlookup (fmrestrict_set (action_needed_vars a s) s))"
    then have a: "fmlookup (fmrestrict_set (action_needed_vars a s) s) x = fmlookup s x"
      by (auto simp: fmdom'_restrict_set_precise)
    then have "fmlookup (fmrestrict_set (system_needed_vars PROB s) s) x = fmlookup s x"
      using 1 contra_subsetD
      by fastforce
    then have "
      fmlookup (fmrestrict_set (action_needed_vars a s) s) x
      = fmlookup (fmrestrict_set (system_needed_vars PROB s) s) x
    "
      using a
      by argo
  }
  then have "
      fmlookup (fmrestrict_set (action_needed_vars a s) s)
      \<subseteq>\<^sub>m fmlookup (fmrestrict_set (system_needed_vars PROB s) s)
    "
    using map_le_def
    by blast
  then show "(action_needed_asses a s \<subseteq>\<^sub>f system_needed_asses PROB s)"
    by (simp add: fmsubset.rep_eq action_needed_asses_def system_needed_asses_def)
qed


lemma system_needed_asses_include_action_needed_asses_1:
  assumes "(a \<in> PROB)"
  shows "(action_needed_vars a (fmrestrict_set (system_needed_vars PROB s) s) = action_needed_vars a s)"
proof -
  let ?A="{v \<in> fmdom' (fmrestrict_set (system_needed_vars PROB s) s).
      v \<in> fmdom' (fst a)
      \<and> fmlookup (fst a) v = fmlookup (fmrestrict_set (system_needed_vars PROB s) s) v}"
  let ?B="{v \<in> fmdom' s. v \<in> fmdom' (fst a) \<and> fmlookup (fst a) v = fmlookup s v}"
  {
    fix v
    assume "v \<in> ?A"
    then have i: "v \<in> fmdom' (fmrestrict_set (system_needed_vars PROB s) s)" "v \<in> fmdom' (fst a)"
      "fmlookup (fst a) v = fmlookup (fmrestrict_set (system_needed_vars PROB s) s) v"
      by blast+
    then have "v \<in> fmdom' s"
      by (simp add: fmdom'_restrict_set_precise)
    moreover have "fmlookup (fst a) v = fmlookup s v"
      using i(2, 3) fmdom'_notI
      by force
    ultimately have "v \<in> ?B"
      using i
      by blast
  }
  then have 1: "?A \<subseteq> ?B"
    by blast
  {
    fix v
    assume P: "v \<in> ?B"
    then have ii: "v \<in> fmdom' s" "v \<in> fmdom' (fst a)" "fmlookup (fst a) v = fmlookup s v"
      by blast+
    moreover {
      have "\<exists>s'. v \<in> s' \<and> (\<exists>a. (s' = action_needed_vars a s) \<and> a \<in> PROB)"
        unfolding action_needed_vars_def
        using assms P action_needed_vars_def
        by metis
      then obtain s' where \<alpha>: "v \<in> s'" "(\<exists>a. (s' = action_needed_vars a s) \<and> a \<in> PROB)"
        by blast
      moreover obtain a' where "s' = action_needed_vars a' s" "a' \<in> PROB"
        using \<alpha>
        by blast
      ultimately have "v \<in> fmdom' (fmrestrict_set (system_needed_vars PROB s) s)"
        unfolding fmdom'_restrict_set_precise
        using action_needed_vars_subset_sys_needed_vars_subset ii(1) by blast
    }
    note iii = this
    moreover have "fmlookup (fst a) v = fmlookup (fmrestrict_set (system_needed_vars PROB s) s) v"
      using ii(3) iii fmdom'_notI
      by force
    ultimately have "v \<in> ?A"
      by blast
  }
  then have "?B \<subseteq> ?A"
    by blast
  then show ?thesis
    unfolding action_needed_vars_def
    using 1
    by blast
qed

\<comment> \<open>NOTE added lemma.\<close>
\<comment> \<open>TODO refactor (proven elsewhere?).\<close>
lemma system_needed_asses_include_action_needed_asses_i:
  fixes A B f
  assumes "A \<subseteq> B"
  shows "fmrestrict_set A (fmrestrict_set B f) = fmrestrict_set A f"
proof -
  {
    let ?f'="fmrestrict_set A f"
    let ?f''="fmrestrict_set A (fmrestrict_set B f)"
    assume C: "?f'' \<noteq> ?f'"
    then obtain v where 1: "fmlookup ?f'' v \<noteq> fmlookup ?f' v"
      by (meson fmap_ext)
    then have False
    proof (cases "v \<in> A")
      case True
      have "fmlookup ?f'' v = fmlookup (fmrestrict_set B f) v"
        using True fmlookup_restrict_set
        by simp
      moreover have "fmlookup (fmrestrict_set B f) v = fmlookup ?f' v"
        using True assms(1)
        by auto
      ultimately show ?thesis
        using 1
        by argo
    next
      case False
      then have "fmlookup ?f' v = None" "fmlookup ?f'' v = None"
        using fmlookup_restrict_set
        by auto+
      then show ?thesis
        using 1
        by argo
    qed
  }
  then show ?thesis
    by blast
qed


lemma system_needed_asses_include_action_needed_asses:
  assumes "(a \<in> PROB)"
  shows "(action_needed_asses a (system_needed_asses PROB s) = action_needed_asses a s)"
proof -
  {
    have " action_needed_vars a s \<subseteq> system_needed_vars PROB s"
      using action_needed_vars_subset_sys_needed_vars_subset[OF assms]
      by simp
    then have "
        fmrestrict_set (action_needed_vars a s) (fmrestrict_set (system_needed_vars PROB s) s) =
        fmrestrict_set (action_needed_vars a s) s"
      using system_needed_asses_include_action_needed_asses_i
      by fast
  }
  moreover
  {
    have
      "action_needed_vars a (fmrestrict_set (system_needed_vars PROB s) s) = action_needed_vars a s"
      using system_needed_asses_include_action_needed_asses_1[OF assms]
      by simp
    then have "fmrestrict_set (action_needed_vars a (fmrestrict_set (system_needed_vars PROB s) s))
        (fmrestrict_set (system_needed_vars PROB s) s) =
        fmrestrict_set (action_needed_vars a s) s
        \<longleftrightarrow> fmrestrict_set (action_needed_vars a s) (fmrestrict_set (system_needed_vars PROB s) s) =
            fmrestrict_set (action_needed_vars a s) s"
      by simp
  }
  ultimately show ?thesis
    unfolding  action_needed_asses_def system_needed_asses_def
    by simp
qed


lemma system_needed_asses_submap:
  "system_needed_asses PROB s \<subseteq>\<^sub>f s"
proof -
  {
    fix x
    assume P: "x\<in> dom (fmlookup (system_needed_asses PROB s))"
    then have "system_needed_asses PROB s = (fmrestrict_set (system_needed_vars PROB s) s)"
      by (simp add: system_needed_asses_def)
    then have "fmlookup (system_needed_asses PROB s) x = fmlookup s x"
      using P
      by (auto simp: fmdom'_restrict_set_precise)
  }
  then have "fmlookup (system_needed_asses PROB s) \<subseteq>\<^sub>m fmlookup s"
    using map_le_def
    by blast
  then show ?thesis
    using fmsubset.rep_eq
    by fast
qed


lemma as_works_from_system_needed_asses:
  assumes "(as \<in> valid_plans PROB)"
  shows "(exec_plan (system_needed_asses PROB s) as \<subseteq>\<^sub>f exec_plan s as)"
  using assms
  by (metis
      action_needed_asses_def
      as_needed_asses_submap_exec
      fmsubset_restrict_set_mono system_needed_asses_def
      system_needed_asses_include_action_needed_asses
      system_needed_asses_include_action_needed_asses_1
      system_needed_asses_submap
      valid_plan_mems
      )


end