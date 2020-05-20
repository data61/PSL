theory Dependency
  imports Main "HOL-Library.Finite_Map" FactoredSystem ActionSeqProcess RelUtils
begin 


section \<open>Dependency\<close>

text \<open> State variable dependency analysis may be used to find structure in a factored system and 
find useful projections, for example on variable sets which are closed under mutual dependency. 
[Abdulaziz et al., p.13]

In the following the dependency predicate (`dep`) is formalized and some dependency related 
propositions are proven. Dependency between variables `v1`, `v2` w.r.t to an action set @{term "\<delta>"} is given
if one of the following holds:
  (1) `v1` and `v2` are equal
  (2) an action @{term "(p, e) \<in> \<delta>"} exists where @{term "v1 \<in> \<D>(p)"} and @{term "v2 \<in> \<D>(e)"} (meaning that it is a
necessary condition that `p v1` is given if the action has effect `e v2`).
  (3) or, an action @{term "(p, e) \<in> \<delta>"} exists s.t. @{term "v1 v2 \<in> \<D>(e)"}
This notion is extended to sets of variables `vs1`, `vs2` (`dep\_var\_set`): `vs1` and `vs2` are 
dependent iff `vs1` and `vs2` are disjoint and if dependent `v1`, `v2` exist where @{term "v1 \<in> vs1"}, 
@{term "v2 \<in> vs2"}. [Abdulaziz et al., Definition 7, p.13][Abdulaziz et al., HOL4 Definition 5, p.14] \<close>


subsection \<open>Dependent Variables and Variable Sets\<close>

\<comment> \<open>NOTE name shortened to 'dep'.\<close>
definition dep where
  "dep PROB v1 v2 \<equiv> (\<exists>a. 
    a \<in> PROB 
    \<and> (
      ((v1 \<in> fmdom' (fst a)) \<and> (v2 \<in> fmdom' (snd a))) 
      \<or> ((v1 \<in> fmdom' (snd a) \<and> v2 \<in> fmdom' (snd a)))
    )
  ) 
    \<or> (v1 = v2)"

\<comment> \<open>NOTE name shortened to 'dep\_var\_set'.\<close>
definition dep_var_set where
  "dep_var_set PROB vs1 vs2 \<equiv> (disjnt vs1 vs2) \<and> 
                              (\<exists> v1 v2. (v1 \<in> vs1) \<and> (v2 \<in> vs2) \<and> (dep PROB v1 v2)
  )"


lemma  dep_var_set_self_empty: 
  fixes PROB vs
  assumes "dep_var_set PROB vs vs"
  shows "(vs = {})"
  using assms
  unfolding dep_var_set_def
proof -
  obtain v1 v2 where
    "v1 \<in> vs" "v2 \<in> vs" "disjnt vs vs" "dep PROB v1 v2" 
    using assms 
    unfolding dep_var_set_def
    by blast
  then show ?thesis
    by force
qed


lemma DEP_REFL: 
  fixes PROB 
  shows "reflexive (\<lambda>v v'. dep PROB v v')"
  unfolding dep_def reflexive_def
  by presburger


\<comment> \<open>NOTE added lemma.\<close> 
lemma NEQ_DEP_IMP_IN_DOM_i:
  fixes a v
  assumes "a \<in> PROB" "v \<in> fmdom' (fst a)"
  shows "v \<in> prob_dom PROB"
proof -
  have "v \<in> fmdom' (fst a)"
    using assms(2)
    by simp
  moreover have "fmdom' (fst a) \<subseteq> prob_dom PROB" 
    using assms(1)
    unfolding prob_dom_def action_dom_def
    using case_prod_beta' 
    by auto
  ultimately show ?thesis
    by blast
qed

\<comment> \<open>NOTE added lemma.\<close> 
lemma NEQ_DEP_IMP_IN_DOM_ii:
  fixes a v
  assumes "a \<in> PROB" "v \<in> fmdom' (snd a)"
  shows "v \<in> prob_dom PROB"
proof -
  have "v \<in> fmdom' (snd a)"
    using assms(2)
    by simp
  moreover have "fmdom' (snd a) \<subseteq> prob_dom PROB" 
    using assms(1)
    unfolding prob_dom_def action_dom_def
    using case_prod_beta' 
    by auto
  ultimately show ?thesis
    by blast
qed

lemma NEQ_DEP_IMP_IN_DOM: 
  fixes PROB :: "(('a, 'b) fmap \<times> ('a, 'b) fmap) set" and  v v'
  assumes "\<not>(v = v')" "(dep PROB v v')" 
  shows "(v \<in> (prob_dom PROB) \<and> v' \<in> (prob_dom PROB))"
  using assms 
  unfolding dep_def 
  using FDOM_pre_subset_prob_dom_pair FDOM_eff_subset_prob_dom_pair
proof -
  obtain a where 1:
    "a \<in> PROB"
    "(v \<in> fmdom' (fst a) \<and> v' \<in> fmdom' (snd a) \<or> v \<in> fmdom' (snd a) \<and> v' \<in> fmdom' (snd a))"
    using assms
    unfolding dep_def
    by blast
  then consider 
    (i) "v \<in> fmdom' (fst a) \<and> v' \<in> fmdom' (snd a)"
    | (ii) "v \<in> fmdom' (snd a) \<and> v' \<in> fmdom' (snd a)" 
    by blast
  then show ?thesis 
  proof (cases)
    case i
    then have "v \<in> fmdom' (fst a)" "v' \<in> fmdom' (snd a)"
      by simp+
    then have "v \<in> prob_dom PROB"  "v' \<in> prob_dom PROB" 
      using 1 NEQ_DEP_IMP_IN_DOM_i NEQ_DEP_IMP_IN_DOM_ii
      by metis+
    then show ?thesis
      by simp
  next
    case ii
    then have "v \<in> fmdom' (snd a)" "v' \<in> fmdom' (snd a)"
      by simp+
    then have "v \<in> prob_dom PROB"  "v' \<in> prob_dom PROB" 
      using 1 NEQ_DEP_IMP_IN_DOM_ii
      by metis+
    then show ?thesis
      by simp
  qed
qed


lemma dep_sos_imp_mem_dep: 
  fixes PROB S vs
  assumes "(dep_var_set PROB (\<Union> S) vs)"
  shows "(\<exists>vs'. vs' \<in> S \<and> dep_var_set PROB vs' vs)"
proof -
  obtain v1 v2 where obtain_v1_v2: "v1 \<in> \<Union>S" "v2 \<in> vs" "disjnt (\<Union>S) vs" "dep PROB v1 v2"
    using assms dep_var_set_def[of PROB "\<Union> S" vs]
    by blast
  moreover
  {
    fix vs'
    assume "vs' \<in> S" 
    moreover have "vs' \<subseteq> (\<Union>S)"
      using calculation Union_upper
      by blast
    ultimately have "disjnt vs' vs" 
      using obtain_v1_v2(3) disjnt_subset1
      by blast
  }
  ultimately show ?thesis 
    unfolding dep_var_set_def
    by blast
qed


lemma dep_union_imp_or_dep: 
  fixes PROB vs vs' vs''
  assumes "(dep_var_set PROB vs (vs' \<union> vs''))"
  shows "(dep_var_set PROB vs vs' \<or> dep_var_set PROB vs vs'')"
proof -
  obtain v1 v2 where 
    obtain_v1_v2: "v1 \<in> vs" "v2 \<in> vs' \<union> vs''" "disjnt vs (vs' \<union> vs'')" "dep PROB v1 v2"
    using assms dep_var_set_def[of PROB vs "(vs' \<union> vs'')"]
    by blast
      \<comment> \<open>NOTE The proofs for the cases introduced here yield the goal's left and right side 
    respectively.\<close>
  consider (i) "v2 \<in> vs'" | (ii) "v2 \<in> vs''" 
    using obtain_v1_v2(2) 
    by blast
  then show ?thesis 
  proof (cases)
    case i
    have "vs' \<subseteq> vs' \<union> vs''" 
      by auto
    moreover have "disjnt (vs' \<union> vs'') vs" 
      using obtain_v1_v2(3) disjnt_sym
      by blast
    ultimately have "disjnt vs vs'" 
      using disjnt_subset1 disjnt_sym
      by blast
    then have "dep_var_set PROB vs vs'" 
      unfolding dep_var_set_def 
      using obtain_v1_v2(1, 4) i
      by blast
    then show ?thesis 
      by simp
  next
    case ii
    then have "vs'' \<subseteq> vs' \<union> vs''" 
      by simp
    moreover have "disjnt (vs' \<union> vs'') vs" 
      using obtain_v1_v2(3) disjnt_sym
      by fast
    ultimately have "disjnt vs vs''" 
      using disjnt_subset1 disjnt_sym
      by metis
    then have "dep_var_set PROB vs vs''" 
      unfolding dep_var_set_def 
      using obtain_v1_v2(1, 4) ii 
      by blast
    then show ?thesis 
      by simp
  qed
qed


\<comment> \<open>NOTE This is symmetrical to `dep\_sos\_imp\_mem\_dep` w.r.t to `vs` and @{term "\<Union> S"}.\<close>
lemma dep_biunion_imp_or_dep: 
  fixes PROB vs S
  assumes "(dep_var_set PROB vs (\<Union>S))"
  shows "(\<exists>vs'. vs' \<in> S \<and> dep_var_set PROB vs vs')"
proof -
  obtain v1 v2 where obtain_v1_v2: "v1 \<in> vs" "v2 \<in> (\<Union>S)" "disjnt vs (\<Union>S)" "dep PROB v1 v2"
    using assms dep_var_set_def[of PROB vs "\<Union> S"]
    by blast
  moreover
  {
    fix vs'
    assume "vs' \<in> S" 
    then have "vs' \<subseteq> (\<Union>S)"
      using calculation Union_upper
      by blast
    moreover have "disjnt (\<Union>S) vs" 
      using obtain_v1_v2(3) disjnt_sym
      by blast
    ultimately have "disjnt vs vs'" 
      using obtain_v1_v2(3) disjnt_subset1 disjnt_sym
      by metis
  }
  ultimately show ?thesis 
    unfolding dep_var_set_def
    by blast
qed


subsection "Transitive Closure of Dependent Variables and Variable Sets"


definition dep_tc where
  "dep_tc PROB = TC (\<lambda>v1' v2'. dep PROB v1' v2')"


\<comment> \<open>NOTE type of `PROB` had to be fixed for MP on `NEQ\_DEP\_IMP\_IN\_DOM`.\<close>
lemma dep_tc_imp_in_dom: 
  fixes PROB :: "(('a, 'b) fmap \<times> ('a, 'b) fmap) set" and v1 v2
  assumes "\<not>(v1 = v2)" "(dep_tc PROB v1 v2)"
  shows "(v1 \<in> prob_dom PROB)"
proof -
  have "TC (dep PROB) v1 v2" 
    using assms(2) 
    unfolding dep_tc_def
    by simp
  then have "dep PROB v1 v2 \<or> (\<exists>y. v1 \<noteq> y \<and> y \<noteq> v2 \<and> dep PROB v1 y \<and> TC (dep PROB) y v2)"
    using TC_CASES1_NEQ[where R = "(\<lambda>v1' v2'. dep PROB v1' v2')" and x = v1 and z = v2]
    by (simp add: TC_equiv_tranclp)
      \<comment> \<open>NOTE Split on the disjunction yielded by the previous step.\<close>
  then consider 
    (i) "dep PROB v1 v2" 
    | (ii) "(\<exists>y. v1 \<noteq> y \<and> y \<noteq> v2 \<and> dep PROB v1 y \<and> TC (dep PROB) y v2)"
    by fast 
  then show ?thesis 
  proof (cases)
    case i
    {
      consider 
        (II) "(\<exists>a. 
            a \<in> PROB \<and>
            (
              v1 \<in> fmdom' (fst a) \<and> v2 \<in> fmdom' (snd a) 
              \<or> v1 \<in> fmdom' (snd a) \<and> v2 \<in> fmdom' (snd a)))"
        | (III) "v1 = v2"
        using i 
        unfolding dep_def 
        by blast
      then have ?thesis 
      proof (cases)
        case II
        then obtain a where 1:
          "a \<in> PROB" "(v1 \<in> fmdom' (fst a) \<and> v2 \<in> fmdom' (snd a) 
              \<or> v1 \<in> fmdom' (snd a) \<and> v2 \<in> fmdom' (snd a))"
          by blast
        then have "v1 \<in> fmdom' (fst a) \<union> fmdom' (snd a)" 
          by blast 
        then have 2: "v1 \<in> action_dom (fst a) (snd a)" 
          unfolding action_dom_def
          by blast 
        then have "action_dom (fst a) (snd a) \<subseteq> prob_dom PROB" 
          using 1(1) exec_as_proj_valid_2
          by fast
        then have "v1 \<in> prob_dom PROB"
          using 1 2
          by fast
        then show ?thesis
          by simp
      next
        case III
        then show ?thesis 
          using assms(1)
          by simp 
      qed
    }
    then show ?thesis
      by simp
  next
    case ii
    then obtain y where "v1 \<noteq> y" "y \<noteq> v2" "dep PROB v1 y" "TC (dep PROB) y v2"
      using ii
      by blast
    then show ?thesis 
      using NEQ_DEP_IMP_IN_DOM 
      by metis
  qed
qed


lemma not_dep_disj_imp_not_dep: 
  fixes PROB vs_1 vs_2 vs_3
  assumes "((vs_1 \<inter> vs_2) = {})" "(vs_3 \<subseteq> vs_2)" "\<not>(dep_var_set PROB vs_1 vs_2)"
  shows "\<not>(dep_var_set PROB vs_1 vs_3)"
  using assms subset_eq
  unfolding dep_var_set_def disjnt_def
  by blast


lemma dep_slist_imp_mem_dep: 
  fixes PROB vs lvs
  assumes "(dep_var_set PROB (\<Union> (set lvs)) vs)"
  shows "(\<exists>vs'. ListMem vs' lvs \<and> dep_var_set PROB vs' vs)"
proof -
  obtain v1 v2 where 
    obtain_v1_v2: "v1 \<in> \<Union>(set lvs)" "v2 \<in> vs" "disjnt (\<Union>(set lvs)) vs" "dep PROB v1 v2" 
    using assms dep_var_set_def[of PROB "\<Union> (set lvs)" vs] 
    by blast
  then obtain vs' where obtain_vs': "vs' \<in> set lvs" "v1 \<in> vs'" 
    by blast
  then have "ListMem vs' lvs" 
    using ListMem_iff
    by fast
  moreover {
    have "disjnt vs' vs"
      using obtain_v1_v2(3) obtain_vs'(1) by auto
    then have "dep_var_set PROB vs' vs" 
      unfolding dep_var_set_def 
      using obtain_v1_v2(1, 2, 4) obtain_vs'(2)
      by blast
  }
  ultimately show ?thesis
    by blast
qed


lemma n_bigunion_le_sum_3: 
  fixes PROB vs svs
  assumes "(\<forall> vs'. vs' \<in> svs \<longrightarrow> \<not>(dep_var_set PROB vs' vs))"
  shows "\<not>(dep_var_set PROB (\<Union>svs) vs)"
proof -
  {
    assume "(dep_var_set PROB (\<Union>svs) vs)"
    then obtain v1 v2 where obtain_vs: "v1 \<in> \<Union>svs" "v2 \<in> vs" "disjnt (\<Union>svs) vs" "dep PROB v1 v2"
      unfolding dep_var_set_def
      by blast
    then obtain vs' where obtain_vs': "v1 \<in> vs'" "vs' \<in> svs" 
      by blast 
    then have a: "disjnt vs' vs" 
      using obtain_vs(3) obtain_vs'(2) disjnt_subset1 
      by blast
    then have "\<forall>v1 v2. \<not>(v1 \<in> vs') \<or> \<not>(v2 \<in> vs) \<or> \<not>disjnt vs' vs \<or> \<not>dep PROB v1 v2" 
      using assms obtain_vs'(2) dep_var_set_def
      by fast
    then have False
      using a obtain_vs'(1) obtain_vs(2, 4)
      by blast
  }
  then show ?thesis
    by blast
qed


lemma disj_not_dep_vset_union_imp_or:
  fixes PROB a vs vs' 
  assumes "(a \<in> PROB)" "(disjnt vs vs')" 
    "(\<not>(dep_var_set PROB vs' vs) \<or> \<not>(dep_var_set PROB vs vs'))"
    "(varset_action a (vs \<union> vs'))"
  shows "(varset_action a vs \<or> varset_action a vs')"
  using assms
  unfolding varset_action_def dep_var_set_def dep_def
proof -
  assume a1: "fmdom' (snd a) \<subseteq> vs \<union> vs'"
  assume "disjnt vs vs'"
  assume " \<not> (disjnt vs' vs \<and>
        (\<exists>v1 v2. v1 \<in> vs' \<and> v2 \<in> vs \<and> ((\<exists>a. a \<in> PROB \<and> (v1 \<in> fmdom' (fst a) \<and> v2 \<in> fmdom' (snd a) \<or> v1 \<in> fmdom' (snd a) \<and> v2 \<in> fmdom' (snd a))) \<or> v1 = v2))) \<or>
       \<not> (disjnt vs vs' \<and>
        (\<exists>v1 v2. v1 \<in> vs \<and> v2 \<in> vs' \<and> ((\<exists>a. a \<in> PROB \<and> (v1 \<in> fmdom' (fst a) \<and> v2 \<in> fmdom' (snd a) \<or> v1 \<in> fmdom' (snd a) \<and> v2 \<in> fmdom' (snd a))) \<or> v1 = v2))) "
  then have f2: "\<And>aa ab. aa \<notin> vs \<or> ab \<notin> vs' \<or> aa \<notin> fmdom' (snd a) \<or> ab \<notin> fmdom' (snd a)"
    using \<open>a \<in> PROB\<close> \<open>disjnt vs vs'\<close> disjnt_sym by blast
  obtain aa :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a" where
    f3: "\<And>A Aa a Ab Ac. (A \<subseteq> Aa \<or> aa A Aa \<in> A) \<and> (aa A Aa \<notin> Aa \<or> A \<subseteq> Aa) 
      \<and> ((a::'a) \<notin> Ab \<or> \<not> Ab \<subseteq> Ac \<or> a \<in> Ac)"
    by moura
  then have "\<And>A. fmdom' (snd a) \<subseteq> A \<or> aa (fmdom' (snd a)) A \<in> vs \<or> aa (fmdom' (snd a)) A \<in> vs'"
    using a1 by (meson Un_iff)
  then show "fmdom' (snd a) \<subseteq> vs \<or> fmdom' (snd a) \<subseteq> vs'"
    using f3 f2 by meson
qed


end