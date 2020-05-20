(*  
  Title:    Random_Serial_Dictatorship.thy
  Author:   Manuel Eberl, TU München

  Definition and basic properties of Random Serial Dictatorship
*)

section \<open>Random Serial Dictatorship\<close>

theory Random_Serial_Dictatorship
imports
  Complex_Main
  Social_Decision_Schemes
  Random_Dictatorship
begin

text \<open>
  Random Serial Dictatorship is an anonymous, neutral, strongly strategy-proof, 
  and ex-post efficient Social Decision Scheme that extends Random Dictatorship
  to the domain of weak preferences.
  
  We define RSD using a fold over a random permutation. Effectively, we choose a random
  order of the agents (in the form of a list) and then traverse that list from left to right,
  where each agent in turn removes all the alternatives that are not top-ranked among the 
  remaining ones.
\<close>
definition random_serial_dictatorship :: 
    "'agent set \<Rightarrow> 'alt set \<Rightarrow> ('agent, 'alt) pref_profile \<Rightarrow> 'alt lottery" where
  "random_serial_dictatorship agents alts R = 
     fold_bind_random_permutation (\<lambda>i alts. Max_wrt_among (R i) alts) pmf_of_set alts agents"

text \<open>
  The following two facts correspond give an alternative recursive definition to
  the above definition, which uses random permutations and list folding.
\<close>
lemma random_serial_dictatorship_empty [simp]:
  "random_serial_dictatorship {} alts R = pmf_of_set alts"
  by (simp add: random_serial_dictatorship_def)

lemma random_serial_dictatorship_nonempty:
  "finite agents \<Longrightarrow> agents \<noteq> {} \<Longrightarrow> 
    random_serial_dictatorship agents alts R =
      do {
        i \<leftarrow> pmf_of_set agents;
        random_serial_dictatorship (agents - {i}) (Max_wrt_among (R i) alts) R
      }"
  by (simp add: random_serial_dictatorship_def)
     
     
text \<open>
  We define the RSD winners w.r.t. a given set of alternatives and a fixed permutation 
  (i.e. list) of agents. In contrast to the above definition, the RSD winners are 
  determined by traversing the list of agents from right to left.
    This may seem strange, but it makes induction much easier, since induction over @{term foldr}
  does not require generalisation over the set of alternatives and is therefore much 
  easier than over @{term foldl}. 
\<close>
definition rsd_winners where
  "rsd_winners R alts agents = foldr (\<lambda>i alts. Max_wrt_among (R i) alts) agents alts"

lemma rsd_winners_empty [simp]: "rsd_winners R alts [] = alts"
  by (simp add: rsd_winners_def)

lemma rsd_winners_Cons [simp]:
  "rsd_winners R alts (i # agents) = Max_wrt_among (R i) (rsd_winners R alts agents)"
  by (simp add: rsd_winners_def)

lemma rsd_winners_map [simp]: 
  "rsd_winners R alts (map f agents) = rsd_winners (R \<circ> f) alts agents"
  by (simp add: rsd_winners_def foldr_map o_def)

  
text \<open>
  There is now another alternative definition of RSD in terms of the
  RSD winners. This will mostly be used for induction.
\<close>
lemma random_serial_dictatorship_altdef:
  assumes "finite agents"
  shows   "random_serial_dictatorship agents alts R =
             do {
               agents' \<leftarrow> pmf_of_set (permutations_of_set agents);
               pmf_of_set (rsd_winners R alts agents')
             }"
   by (simp add: random_serial_dictatorship_def 
         fold_bind_random_permutation_foldr assms rsd_winners_def)
   
text \<open>
  The following lemma shows that folding from left to right yields the same
  distribution. This is probably the most commonly used definition in the literature,
  along with the recursive one.
\<close>
lemma random_serial_dictatorship_foldl:
  assumes "finite agents"
  shows   "random_serial_dictatorship agents alts R =
             do {
               agents' \<leftarrow> pmf_of_set (permutations_of_set agents);
               pmf_of_set (foldl (\<lambda>alts i. Max_wrt_among (R i) alts) alts agents')
             }"
   by (simp add: random_serial_dictatorship_def fold_bind_random_permutation_foldl assms)


   
subsection \<open>Auxiliary facts about RSD\<close>


subsubsection \<open>Pareto-equivalence classes\<close>

text \<open>
  First of all, we introduce the auxiliary notion of a Pareto-equivalence class.
  A non-empty set of alternatives is a Pareto equivalence class if all agents are 
  indifferent between all alternatives in it, and if some alternative @{term "x::'alt"} 
  is contained in the set, any other alternative @{term "y::'alt"} is contained in it
  if and only if, to all agents, @{term y} is at least as good as @{term x}.
    The importance of this notion lies in the fact that the set of RSD winners is always
  a Pareto-equivalence class, which we will later use to show ex-post efficiency and
  strategy-proofness.
\<close>

definition RSD_pareto_eqclass where
  "RSD_pareto_eqclass agents alts R A \<longleftrightarrow>
     A \<noteq> {} \<and> A \<subseteq> alts \<and> (\<forall>x\<in>A. \<forall>y\<in>alts. y \<in> A \<longleftrightarrow> (\<forall>i\<in>agents. R i x y))"

lemma RSD_pareto_eqclassI:
  assumes "A \<noteq> {}" "A \<subseteq> alts" "\<And>x y. x \<in> A \<Longrightarrow> y \<in> alts \<Longrightarrow> y \<in> A \<longleftrightarrow> (\<forall>i\<in>agents. R i x y)"
  shows   "RSD_pareto_eqclass agents alts R A"
  using assms unfolding RSD_pareto_eqclass_def by simp_all

lemma RSD_pareto_eqclassD:
  assumes "RSD_pareto_eqclass agents alts R A"
  shows   "A \<noteq> {}" "A \<subseteq> alts" "\<And>x y. x \<in> A \<Longrightarrow> y \<in> alts \<Longrightarrow> y \<in> A \<longleftrightarrow> (\<forall>i\<in>agents. R i x y)"
  using assms unfolding RSD_pareto_eqclass_def by simp_all

lemma RSD_pareto_eqclass_indiff_set:
  assumes "RSD_pareto_eqclass agents alts R A" "i \<in> agents" "x \<in> A" "y \<in> A"
  shows   "R i x y"
  using assms unfolding RSD_pareto_eqclass_def by blast

lemma RSD_pareto_eqclass_empty [simp, intro!]:
  "alts \<noteq> {} \<Longrightarrow> RSD_pareto_eqclass {} alts R alts"
  by (auto intro!: RSD_pareto_eqclassI)

lemma (in pref_profile_wf) RSD_pareto_eqclass_insert:
  assumes "RSD_pareto_eqclass agents' alts R A" "finite alts"
          "i \<in> agents" "agents' \<subseteq> agents"
  shows   "RSD_pareto_eqclass (insert i agents') alts R (Max_wrt_among (R i) A)"
proof -
  from assms interpret total_preorder_on alts "R i" by simp
  show ?thesis
  proof (intro RSD_pareto_eqclassI Max_wrt_among_nonempty Max_wrt_among_subset, goal_cases)
    case (3 x y)
    with RSD_pareto_eqclassD[OF assms(1)] 
      show ?case unfolding Max_wrt_among_total_preorder 
      by (blast intro: trans)
  qed (insert RSD_pareto_eqclassD[OF assms(1)] assms(2), 
       simp_all add: Int_absorb1 Int_absorb2 finite_subset)[2]
qed


subsubsection \<open>Facts about RSD winners\<close>

context pref_profile_wf
begin

text \<open>
  Any RSD winner is a valid alternative.  
\<close>
lemma rsd_winners_subset:
  assumes "set agents' \<subseteq> agents" 
  shows   "rsd_winners R alts' agents' \<subseteq> alts'"
proof -
  {
    fix i assume "i \<in> agents"
    then interpret total_preorder_on alts "R i" by simp
    have "Max_wrt_among (R i) A \<subseteq> A" for A
      using Max_wrt_among_subset by blast
  } note A = this

  from \<open>set agents' \<subseteq> agents\<close> show "rsd_winners R alts' agents' \<subseteq> alts'"
    using A by (induction agents') auto
qed

text \<open>
  There is always at least one RSD winner.  
\<close>
lemma rsd_winners_nonempty:
  assumes finite: "finite alts"  and "alts' \<noteq> {}"  "set agents' \<subseteq> agents" "alts' \<subseteq> alts" 
  shows   "rsd_winners R alts' agents' \<noteq> {}"
proof -
  {
    fix i assume "i \<in> agents"
    then interpret total_preorder_on alts "R i" by simp
    have "Max_wrt_among (R i) A \<noteq> {}" if "A \<subseteq> alts" "A \<noteq> {}" for A
      using that assms by (intro Max_wrt_among_nonempty) (auto simp: Int_absorb)
  } note B = this

  with \<open>set agents' \<subseteq> agents\<close> \<open>alts' \<subseteq> alts\<close> \<open>alts' \<noteq> {}\<close> 
    show "rsd_winners R alts' agents' \<noteq> {}"
  proof (induction agents')
    case (Cons i agents')
    with B[of i "rsd_winners R alts' agents'"] rsd_winners_subset[of agents' alts'] finite wf
      show ?case by auto
  qed simp
qed

text \<open>
  Obviously, the set of RSD winners is always finite.
\<close>
lemma rsd_winners_finite: 
  assumes "set agents' \<subseteq> agents" "finite alts" "alts' \<subseteq> alts"
  shows   "finite (rsd_winners R alts' agents')"
  by (rule finite_subset[OF subset_trans[OF rsd_winners_subset]]) fact+

lemmas rsd_winners_wf = 
  rsd_winners_subset rsd_winners_nonempty rsd_winners_finite


text \<open>
  The set of RSD winners is a Pareto-equivalence class.
\<close>
lemma RSD_pareto_eqclass_rsd_winners_aux:
  assumes finite: "finite alts" and "alts \<noteq> {}" and "set agents' \<subseteq> agents"
  shows   "RSD_pareto_eqclass (set agents') alts R (rsd_winners R alts agents')"
  using \<open>set agents' \<subseteq> agents\<close>
proof (induction agents')
  case (Cons i agents')
  from Cons.prems show ?case
    by (simp only: set_simps rsd_winners_Cons,
        intro RSD_pareto_eqclass_insert[OF Cons.IH finite]) simp_all
qed (insert assms, simp_all)

lemma RSD_pareto_eqclass_rsd_winners:
  assumes finite: "finite alts" and "alts \<noteq> {}" and "set agents' = agents"
  shows   "RSD_pareto_eqclass agents alts R (rsd_winners R alts agents')"
  using RSD_pareto_eqclass_rsd_winners_aux[of agents'] assms by simp


text \<open>
  For the proof of strategy-proofness, we need to define indifference sets
  and lift preference relations to sets in a specific way.
\<close>
context
begin

text \<open>
  An indifference set for a given preference relation is a non-empty set of alternatives 
  such that the agent is indifferent over all of them.
\<close>
private definition indiff_set where
  "indiff_set S A \<longleftrightarrow> A \<noteq> {} \<and> (\<forall>x\<in>A. \<forall>y\<in>A. S x y)"
  
private lemma indiff_set_mono: "indiff_set S A \<Longrightarrow> B \<subseteq> A \<Longrightarrow> B \<noteq> {} \<Longrightarrow> indiff_set S B"
  unfolding indiff_set_def by blast

  
text \<open>
  Given an arbitrary set of alternatives @{term A} and an indifference set @{term B},
  we say that @{term B} is set-preferred over @{term A} w.r.t. the preference 
  relation @{term R} if all (or, equivalently, any) of the alternatives in @{term B} 
  are preferred over all alternatives in @{term A}.
\<close>
private definition RSD_set_rel where
  "RSD_set_rel S A B \<longleftrightarrow> indiff_set S B \<and> (\<forall>x\<in>A. \<forall>y\<in>B. S x y)" 

text \<open>
  The most-preferred alternatives (w.r.t. @{term R}) among any non-empty set of alternatives 
  form an indifference set w.r.t. @{term R}.
\<close>
private lemma indiff_set_Max_wrt_among:
  assumes "finite carrier" "A \<subseteq> carrier" "A \<noteq> {}" "total_preorder_on carrier S" 
  shows   "indiff_set S (Max_wrt_among S A)"
  unfolding indiff_set_def
proof
  from assms(4) interpret total_preorder_on carrier S .
  from assms(1-3) 
    show "Max_wrt_among S A \<noteq> {}" by (intro Max_wrt_among_nonempty) auto
  from assms(1-3) show "\<forall>x\<in>Max_wrt_among S A. \<forall>y\<in>Max_wrt_among S A. S x y"
    by (auto simp: indiff_set_def Max_wrt_among_total_preorder)
qed


text \<open>
  We now consider the set of RSD winners in the setting of a preference profile @{term R}
  and a manipulated profile @{term "R(i := Ri')"}.
    This theorem shows that the set of RSD winners in the outcome is either the same
  in both cases or the outcome for the truthful profile is an indifference set that is
  set-preferred over the outcome for the manipulated profile.
\<close>
lemma rsd_winners_manipulation_aux:
  assumes wf: "total_preorder_on alts Ri'"
      and i: "i \<in> agents" and "set agents' \<subseteq> agents" "finite agents" 
      and finite: "finite alts" and "alts \<noteq> {}"
  defines [simp]: "w' \<equiv> rsd_winners (R(i := Ri')) alts" and [simp]: "w \<equiv> rsd_winners R alts"
  shows   "w' agents' = w agents' \<or> RSD_set_rel (R i) (w' agents') (w agents')"
using \<open>set agents' \<subseteq> agents\<close>
proof (induction agents')
  case (Cons j agents')
  from wf i interpret Ri: total_preorder_on alts "R i" by simp
  from wf Cons.prems interpret Rj: total_preorder_on alts "R j" by simp
  from wf interpret Ri': total_preorder_on alts "Ri'" .
  from wf assms Cons.prems 
    have indiff_set: "indiff_set (R i) (Max_wrt_among (R i) (rsd_winners R alts agents'))"
    by (intro indiff_set_Max_wrt_among[OF finite] rsd_winners_wf) simp_all
        
  show ?case
  proof (cases "j = i")
    assume j [simp]: "j = i"
    from indiff_set Cons have "RSD_set_rel (R i) (w' (j # agents')) (w (j # agents'))"
      unfolding RSD_set_rel_def
      by (auto simp: Ri.Max_wrt_among_total_preorder Ri'.Max_wrt_among_total_preorder)
    thus ?case ..
  next
    assume j [simp]: "j \<noteq> i"
    from Cons have "w' agents' = w agents' \<or> RSD_set_rel (R i) (w' agents') (w agents')" by simp
    thus ?case
    proof
      assume rel: "RSD_set_rel (R i) (w' agents') (w agents')"
      hence indiff_set: "indiff_set (R i) (w agents')" by (simp add: RSD_set_rel_def)
      moreover from Cons.prems finite \<open>alts \<noteq> {}\<close> 
        have "w agents' \<subseteq> alts" "w agents' \<noteq> {}" unfolding w_def
        by (intro rsd_winners_wf; simp)+
      with finite have "Max_wrt_among (R j) (w agents') \<noteq> {}"
        by (intro Rj.Max_wrt_among_nonempty) auto
      ultimately have "indiff_set (R i) (w (j # agents'))"
        by (intro indiff_set_mono[OF indiff_set] Rj.Max_wrt_among_subset)
           (simp_all add: Rj.Max_wrt_among_subset)
      moreover from rel have "\<forall>x\<in>w' (j # agents'). \<forall>y\<in>w (j # agents'). R i x y"
        by (auto simp: RSD_set_rel_def Rj.Max_wrt_among_total_preorder)
      ultimately have "RSD_set_rel (R i) (w' (j # agents')) (w (j # agents'))"
        unfolding RSD_set_rel_def ..
      thus ?case ..
    qed simp_all
  qed
qed simp_all


text \<open>
  The following variant of the previous theorem is slightly easier to use.
  We eliminate the case where the two outcomes are the same by observing that
  the original outcome is then also set-preferred to the manipulated one.
    In essence, this means that no matter what manipulation is done, the 
  original outcome is always set-preferred to the manipulated one.
\<close>
lemma rsd_winners_manipulation:
  assumes wf: "total_preorder_on alts Ri'"
      and i: "i \<in> agents" and "set agents' = agents" "finite agents" 
      and finite: "finite alts" and "alts \<noteq> {}"
  defines [simp]: "w' \<equiv> rsd_winners (R(i := Ri')) alts" and [simp]: "w \<equiv> rsd_winners R alts"
  shows   "\<forall>x\<in>w' agents'. \<forall>y\<in>w agents'. x \<preceq>[R i] y"
proof -
  have "w' agents' = w agents' \<or> RSD_set_rel (R i) (w' agents') (w agents')"
    using rsd_winners_manipulation_aux[OF assms(1-2) _ assms(4-6)] assms(3) by simp
  thus ?thesis
  proof
    assume eq: "w' agents' = w agents'"
    from assms have "RSD_pareto_eqclass (set agents') alts R (w agents')" unfolding w_def
      by (intro RSD_pareto_eqclass_rsd_winners_aux) simp_all
    from RSD_pareto_eqclass_indiff_set[OF this, of i] i eq assms(3) show ?thesis by auto
  qed (auto simp: RSD_set_rel_def)
qed

end


text \<open>
  The lottery that RSD yields is well-defined.
\<close>
lemma random_serial_dictatorship_support:
  assumes "finite agents" "finite alts" "agents' \<subseteq> agents" "alts' \<noteq> {}" "alts' \<subseteq> alts"
  shows   "set_pmf (random_serial_dictatorship agents' alts' R) \<subseteq> alts'"
proof -
  from assms have [simp]: "finite agents'" by (auto intro: finite_subset)
  have A: "set_pmf (pmf_of_set (rsd_winners R alts' agents'')) \<subseteq> alts'"
    if "agents'' \<in> permutations_of_set agents'" for agents''
    using that assms rsd_winners_wf[where alts' = alts' and agents' = agents'']
    by (auto simp: permutations_of_set_def)
  from assms show ?thesis
    by (auto dest!: A simp add: random_serial_dictatorship_altdef)
qed

text \<open>
  Permutation of alternatives commutes with RSD winners.
\<close>
lemma rsd_winners_permute_profile:
  assumes perm: "\<sigma> permutes alts" and "set agents' \<subseteq> agents" 
  shows   "rsd_winners (permute_profile \<sigma> R) alts agents' = \<sigma> ` rsd_winners R alts agents'"
  using \<open>set agents' \<subseteq> agents\<close>
proof (induction agents')
  case Nil
  from perm show ?case by (simp add: permutes_image)
next
  case (Cons i agents')
  from wf Cons interpret total_preorder_on alts "R i" by simp
  from perm Cons show ?case
    by (simp add: permute_profile_map_relation Max_wrt_among_map_relation_bij permutes_bij)
qed

lemma random_serial_dictatorship_singleton:
  assumes "finite agents" "finite alts" "agents' \<subseteq> agents" "x \<in> alts"
  shows   "random_serial_dictatorship agents' {x} R = return_pmf x" (is "?d = _")
proof -
  from assms have "set_pmf ?d \<subseteq> {x}" 
    by (intro random_serial_dictatorship_support) simp_all
  thus ?thesis by (simp add: set_pmf_subset_singleton)
qed

end


subsection \<open>Proofs of properties\<close>

text \<open>
  With all the facts that we have proven about the RSD winners, the hard work is
  mostly done. We can now simply fix some arbitrary order of the agents, apply the 
  theorems about the RSD winners, and show the properties we want to show without 
  doing much reasoning about probabilities.
\<close>

context election
begin     

abbreviation "RSD \<equiv> random_serial_dictatorship agents alts"

subsubsection \<open>Well-definedness\<close>

sublocale RSD: social_decision_scheme agents alts RSD
  using pref_profile_wf.random_serial_dictatorship_support[of agents alts]
  by unfold_locales (simp_all add: lotteries_on_def)


subsubsection \<open>RD extension\<close>

lemma RSD_extends_RD:
  assumes wf: "is_pref_profile R" and unique: "has_unique_favorites R"
  shows   "RSD R = RD R"
proof -
  from wf interpret pref_profile_wf agents alts R .
  from unique interpret pref_profile_unique_favorites by unfold_locales
  have "RSD R = pmf_of_set agents \<bind> 
                  (\<lambda>i. random_serial_dictatorship (agents - {i}) (favorites R i) R)"
    by (simp add: random_serial_dictatorship_nonempty favorites_altdef Max_wrt_def)
  also from assms have "\<dots> = pmf_of_set agents \<bind> (\<lambda>i. return_pmf (favorite R i))"
    by (intro bind_pmf_cong refl, subst random_serial_dictatorship_singleton [symmetric])
       (auto simp: unique_favorites favorite_in_alts)
  also from assms have "\<dots> = RD R"
    by (simp add: random_dictatorship_unique_favorites map_pmf_def)
  finally show ?thesis .
qed
  

subsubsection \<open>Anonymity\<close>

text \<open>
  Anonymity is a direct consequence of the fact that we randomise over all
  permutations in a uniform way.
\<close>

sublocale RSD: anonymous_sds agents alts RSD
proof
  fix \<pi> R assume perm: "\<pi> permutes agents" and wf: "is_pref_profile R"
  let ?f = "\<lambda>agents'. pmf_of_set (rsd_winners R alts agents')"
  from perm wf have "RSD (R \<circ> \<pi>) = map_pmf (map \<pi>) (pmf_of_set (permutations_of_set agents)) \<bind> ?f"
    by (simp add: random_serial_dictatorship_altdef bind_map_pmf)
  also from perm have "\<dots> = RSD R"
    by (simp add: map_pmf_of_set_inj permutes_inj_on inj_on_mapI
                  permutations_of_set_image_permutes random_serial_dictatorship_altdef)
  finally show "RSD (R \<circ> \<pi>) = RSD R" .
qed


subsubsection \<open>Neutrality\<close>

text \<open>
  Neutrality follows from the fact that the RSD winners of a permuted profile 
  are simply the image of the original RSD winners under the permutation.
\<close>

sublocale RSD: neutral_sds agents alts RSD
proof
  fix \<sigma> R assume perm: "\<sigma> permutes alts" and wf: "is_pref_profile R"
  from wf interpret pref_profile_wf agents alts R .
  from perm show "RSD (permute_profile \<sigma> R) = map_pmf \<sigma> (RSD R)"
    by (auto intro!: bind_pmf_cong dest!: permutations_of_setD(1) 
             simp: random_serial_dictatorship_altdef rsd_winners_permute_profile
                   map_bind_pmf map_pmf_of_set_inj permutes_inj_on rsd_winners_wf)
qed


subsubsection \<open>Ex-post efficiency\<close>

text \<open>
  Ex-post efficiency follows from the fact that the set of RSD winners 
  is a Pareto-equivalence class.
\<close>

sublocale RSD: ex_post_efficient_sds agents alts RSD
proof
  fix R assume wf: "is_pref_profile R"
  then interpret pref_profile_wf agents alts R .
  {
    fix x assume x: "x \<in> set_pmf (RSD R)" "x \<in> pareto_losers R"
    from x(2) obtain y where [simp]: "y \<in> alts" and pareto: "y \<succ>[Pareto(R)] x" 
      by (cases rule: pareto_losersE)
    from x have [simp]: "x \<in> alts" using pareto_loser_in_alts by simp

    from x(1) obtain agents' where agents': "set agents' = agents" and 
        "x \<in> set_pmf (pmf_of_set (rsd_winners R alts agents'))"
      by (auto simp: random_serial_dictatorship_altdef dest: permutations_of_setD)
    with wf have x': "x \<in> rsd_winners R alts agents'"
      using rsd_winners_wf[where alts' = alts and agents' = agents']
      by (subst (asm) set_pmf_of_set) (auto simp: permutations_of_setD)

    from wf agents' 
      have "RSD_pareto_eqclass agents alts R (rsd_winners R alts agents')"
      by (intro RSD_pareto_eqclass_rsd_winners) simp_all
    hence winner_iff: "y \<in> rsd_winners R alts agents' \<longleftrightarrow> (\<forall>i\<in>agents. x \<preceq>[R i] y)"
      if "x \<in> rsd_winners R alts agents'" "y \<in> alts" for x y
      using that unfolding RSD_pareto_eqclass_def by blast
    from x' pareto winner_iff[of x y] winner_iff[of y x] have False
      by (force simp: strongly_preferred_def Pareto_iff)
  }
  thus "set_pmf (RSD R) \<inter> pareto_losers R = {}" by blast
qed


subsubsection \<open>Strong strategy-proofness\<close>

text \<open>
  Strong strategy-proofness is slightly more difficult to show. We have already shown
  that the set of RSD winners for the truthful profile is always set-preferred (by the
  manipulating agent) to the RSD winners for the manipulated profile.
    This can now be used to show strategy-proofness: We recall that the set of RSD 
  winners is always an indifference class. Therefore, given any fixed alternative @{term "x::'alt"}
  and considering a fixed order of the agents, either all of the RSD winners in the original
  profile are at least as good as @{term "x::'alt"} or none of them are, and, since the original 
  RSD winners are set-preferred to the manipulated ones, none of the RSD winners in the
  manipulated case are at least as good than @{term "x::'alt"} either in that case.
    This means that for a fixed order of agents, either the probability that the original  
  outcome is at least as good as @{term "x::'alt"} is 1 or the probability that the manipulated
  outcome is at least as good as @{term "x::'alt"} is 0.
    Therefore, the original lottery is clearly SD-preferred to the manipulated one.
\<close>

sublocale RSD: strongly_strategyproof_sds agents alts RSD
proof (unfold_locales, rule)
  fix R i Ri' x
  assume wf: "is_pref_profile R" and i [simp]: "i \<in> agents" and x: "x \<in> alts" and
         wf': "total_preorder_on alts Ri'"
  interpret R: pref_profile_wf agents alts R by fact
  define R' where "R' = R (i := Ri')"
  from wf wf' have "is_pref_profile R'" by (simp add: R'_def R.wf_update)
  then interpret R': pref_profile_wf agents alts R' .
  note wf = wf wf'
  let ?A = "preferred_alts (R i) x"
  from wf interpret Ri: total_preorder_on alts "R i" by simp

  {
    fix agents' assume agents': "agents' \<in> permutations_of_set agents"
    from agents' have [simp]: "set agents' = agents"
      by (simp add: permutations_of_set_def)
      
    let ?W = "rsd_winners R alts agents'" and ?W' = "rsd_winners R' alts agents'"
    have indiff_set: "RSD_pareto_eqclass agents alts R ?W"
      by (rule R.RSD_pareto_eqclass_rsd_winners; simp add: wf)+
    from R.rsd_winners_wf R'.rsd_winners_wf
      have winners: "?W \<subseteq> alts" "?W \<noteq> {}" "finite ?W" "?W' \<subseteq> alts" "?W' \<noteq> {}" "finite ?W'"
      by simp_all
    
    from \<open>?W \<noteq> {}\<close> obtain y where y: "y \<in> ?W" by blast
    with winners have [simp]: "y \<in> alts" by blast
    from wf' i have mono: "\<forall>x\<in>?W'. \<forall>y\<in>?W. R i x y" unfolding R'_def
      by (intro R.rsd_winners_manipulation) simp_all
    
    have "lottery_prob (pmf_of_set ?W) ?A \<ge> lottery_prob (pmf_of_set ?W') ?A"
    proof (cases "y \<succeq>[R i] x")
      case True
      with y RSD_pareto_eqclass_indiff_set[OF indiff_set(1), of i]  winners
        have "?W \<subseteq> preferred_alts (R i) x"
        by (auto intro: Ri.trans simp: preferred_alts_def)
      with winners show ?thesis
        by (subst (2) measure_pmf_of_set) (simp_all add: Int_absorb2)
    next
      case False
      with y mono have "?W' \<inter> preferred_alts (R i) x = {}" 
        by (auto intro: Ri.trans simp: preferred_alts_def)
      with winners show ?thesis
        by (subst (1) measure_pmf_of_set)
           (simp_all add: Int_absorb2 one_ereal_def measure_nonneg)
    qed
    hence "emeasure (measure_pmf (pmf_of_set ?W)) ?A \<ge> emeasure (measure_pmf (pmf_of_set ?W')) ?A"
      by (simp add: measure_pmf.emeasure_eq_measure)
  }
  hence "emeasure (measure_pmf (RSD R)) ?A \<ge> emeasure (measure_pmf (RSD R')) ?A"
    by (auto simp: random_serial_dictatorship_altdef AE_measure_pmf_iff
             intro!: nn_integral_mono_AE)
  thus "lottery_prob (RSD R) ?A \<ge> lottery_prob (RSD R') ?A" 
    by (simp add: measure_pmf.emeasure_eq_measure)
qed

end

end
