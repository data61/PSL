(*  
  Title:    Social_Choice_Functions.thy
  Author:   Manuel Eberl, TU München

  Definitions of Social Choice Functions, their properties, and related concepts
*)

section \<open>Social Choice Functions\<close>

theory Social_Choice_Functions
imports 
  "Randomised_Social_Choice.Preference_Profile_Cmd"
begin

subsection \<open>Weighted majority graphs\<close>

definition supporters :: "('agent, 'alt) pref_profile \<Rightarrow> 'alt \<Rightarrow> 'alt \<Rightarrow> 'agent set" where
  supporters_auxdef: "supporters R x y = {i. x \<succeq>[R i] y}" 

definition weighted_majority :: "('agent, 'alt) pref_profile \<Rightarrow> 'alt \<Rightarrow> 'alt \<Rightarrow> int" where
  "weighted_majority R x y = int (card (supporters R x y)) - int (card (supporters R y x))"
  
lemma weighted_majority_refl [simp]: "weighted_majority R x x = 0"
  by (simp add: weighted_majority_def)
  
lemma weighted_majority_swap: "weighted_majority R x y = -weighted_majority R y x"
  by (simp add: weighted_majority_def)

lemma eval_set_filter: 
  "Set.filter P {} = {}" 
  "P x \<Longrightarrow> Set.filter P (insert x A) = insert x (Set.filter P A)"
  "\<not>P x \<Longrightarrow> Set.filter P (insert x A) = Set.filter P A"
  unfolding Set.filter_def by auto
  
context election
begin

lemma supporters_def: 
  assumes "is_pref_profile R"
  shows   "supporters R x y = {i\<in>agents. x \<succeq>[R i] y}"
proof -
  interpret pref_profile_wf agents alts R by fact
  show ?thesis using not_outside unfolding supporters_auxdef by blast
qed

lemma supporters_nonagent1:
  assumes "is_pref_profile R" "x \<notin> alts"
  shows   "supporters R x y = {}"
proof -
  interpret pref_profile_wf agents alts R by fact
  from assms show ?thesis by (auto simp: supporters_def dest: not_outside)
qed

lemma supporters_nonagent2:
  assumes "is_pref_profile R" "y \<notin> alts"
  shows   "supporters R x y = {}"
proof -
  interpret pref_profile_wf agents alts R by fact
  from assms show ?thesis by (auto simp: supporters_def dest: not_outside)
qed

lemma weighted_majority_nonagent1:
  assumes "is_pref_profile R" "x \<notin> alts"
  shows   "weighted_majority R x y = 0"
  using assms by (simp add: weighted_majority_def supporters_nonagent1 supporters_nonagent2)

lemma weighted_majority_nonagent2:
  assumes "is_pref_profile R" "y \<notin> alts"
  shows   "weighted_majority R x y = 0"
  using assms by (simp add: weighted_majority_def supporters_nonagent1 supporters_nonagent2)

lemma weighted_majority_eq_iff:
  assumes "is_pref_profile R1" "is_pref_profile R2"
  shows   "weighted_majority R1 = weighted_majority R2 \<longleftrightarrow>
             (\<forall>x\<in>alts. \<forall>y\<in>alts. weighted_majority R1 x y = weighted_majority R2 x y)"
proof (intro iffI ext)
  fix x y :: 'alt
  assume "\<forall>x\<in>alts. \<forall>y\<in>alts. weighted_majority R1 x y = weighted_majority R2 x y"
  with assms show "weighted_majority R1 x y = weighted_majority R2 x y"
    by (cases "x \<in> alts"; cases "y \<in> alts") 
       (auto simp: fun_eq_iff weighted_majority_nonagent1 weighted_majority_nonagent2)
qed auto

end

  
subsection \<open>Definition of Social Choice Functions\<close>

locale social_choice_function = election agents alts 
  for agents :: "'agent set" and alts :: "'alt set" +
  fixes scf :: "('agent, 'alt) pref_profile \<Rightarrow> 'alt set"
  assumes scf_nonempty: "is_pref_profile R \<Longrightarrow> scf R \<noteq> {}"
  assumes scf_alts: "is_pref_profile R \<Longrightarrow> scf R \<subseteq> alts"

subsection \<open>Anonymity\<close>

text \<open>
  An SCF is anonymous if permuting the agents in the input does not change the result.
\<close>
locale anonymous_scf = social_choice_function agents alts scf
  for agents :: "'agent set" and alts :: "'alt set" and scf +
  assumes anonymous: "\<pi> permutes agents \<Longrightarrow> is_pref_profile R \<Longrightarrow> scf (R \<circ> \<pi>) = scf R" 
begin

lemma anonymous':
  assumes "anonymous_profile R1 = anonymous_profile R2"
  assumes "is_pref_profile R1" "is_pref_profile R2"
  shows   "scf R1 = scf R2"
proof -
  from anonymous_profile_agent_permutation[OF assms finite_agents]
    obtain \<pi> where "\<pi> permutes agents" "R1 = R2 \<circ> \<pi>" by blast
  with anonymous[of \<pi> R2] assms show ?thesis by simp
qed

lemma anonymity_prefs_from_table:
  assumes "prefs_from_table_wf agents alts xs" "prefs_from_table_wf agents alts ys"
  assumes "mset (map snd xs) = mset (map snd ys)"
  shows   "scf (prefs_from_table xs) = scf (prefs_from_table ys)"
proof -
  from prefs_from_table_agent_permutation[OF assms] guess \<pi> .
  with anonymous[of \<pi>, of "prefs_from_table xs"] assms(1) show ?thesis 
    by (simp add: pref_profile_from_tableI)
qed

context
begin
qualified lemma anonymity_prefs_from_table_aux:
  assumes "R1 = prefs_from_table xs" "prefs_from_table_wf agents alts xs"
  assumes "R2 = prefs_from_table ys" "prefs_from_table_wf agents alts ys"
  assumes "mset (map snd xs) = mset (map snd ys)"
  shows   "scf R1 = scf R2" unfolding assms(1,3)
  by (rule anonymity_prefs_from_table) (simp_all add: assms del: mset_map)
end

end


subsection \<open>Neutrality\<close>

text \<open>
  An SCF is neutral if permuting the alternatives in the input does not change the
  result, modulo the equivalent permutation in the output lottery.
\<close>
locale neutral_scf = social_choice_function agents alts scf
  for agents :: "'agent set" and alts :: "'alt set" and scf +
  assumes neutral: "\<sigma> permutes alts \<Longrightarrow> is_pref_profile R \<Longrightarrow> 
                        scf (permute_profile \<sigma> R) = \<sigma> ` scf R"
begin

text \<open>
  Alternative formulation of neutrality that shows that our definition is 
  equivalent to that in the paper.
\<close>
lemma neutral':
  assumes "\<sigma> permutes alts"
  assumes "is_pref_profile R"
  assumes "a \<in> alts"
  shows   "\<sigma> a \<in> scf (permute_profile \<sigma> R) \<longleftrightarrow> a \<in> scf R"
proof -
  have *: "x = y" if "\<sigma> x = \<sigma> y" for x y
    using permutes_inj[OF assms(1)] that by (auto dest: injD)
  from assms show ?thesis by (auto simp: neutral dest!: *)
qed

end


locale an_scf = 
  anonymous_scf agents alts scf + neutral_scf agents alts scf
  for agents :: "'agent set" and alts :: "'alt set" and scf
begin

lemma scf_anonymous_neutral:
  assumes perm: "\<sigma> permutes alts" and wf: "is_pref_profile R1" "is_pref_profile R2"
  assumes eq: "anonymous_profile R1 = 
                 image_mset (map (\<lambda>A. \<sigma> ` A)) (anonymous_profile R2)"
  shows   "scf R1 = \<sigma> ` scf R2"
proof -
  interpret R1: pref_profile_wf agents alts R1 by fact
  interpret R2: pref_profile_wf agents alts R2 by fact
  from perm have wf': "is_pref_profile (permute_profile \<sigma> R2)"
    by (rule R2.wf_permute_alts)
  from eq perm have "anonymous_profile R1 = anonymous_profile (permute_profile \<sigma> R2)"
    by (simp add: R2.anonymous_profile_permute)
  from anonymous_profile_agent_permutation[OF this wf(1) wf']
    obtain \<pi> where "\<pi> permutes agents" "permute_profile \<sigma> R2 \<circ> \<pi> = R1" by auto
  have "scf (permute_profile \<sigma> R2 \<circ> \<pi>) = scf (permute_profile \<sigma> R2)"
    by (rule anonymous) fact+
  also have "\<dots> = \<sigma> ` scf R2"
    by (rule neutral) fact+
  also have "permute_profile \<sigma> R2 \<circ> \<pi> = R1" by fact
  finally show ?thesis .
qed


lemma scf_anonymous_neutral':
  assumes perm: "\<sigma> permutes alts" and wf: "is_pref_profile R1" "is_pref_profile R2"
  assumes eq: "anonymous_profile R1 = 
                 image_mset (map (\<lambda>A. \<sigma> ` A)) (anonymous_profile R2)"
  shows   "\<sigma> x \<in> scf R1 \<longleftrightarrow> x \<in> scf R2"
proof -
  have "scf R1 = \<sigma> ` scf R2" by (intro scf_anonymous_neutral) fact+
  also have "\<sigma> x \<in> \<dots> \<longleftrightarrow> x \<in> scf R2"
    by (blast dest: injD[OF permutes_inj[OF perm]])
  finally show ?thesis .
qed

lemma scf_automorphism:
  assumes perm: "\<sigma> permutes alts" and wf: "is_pref_profile R"
  assumes eq: "image_mset (map (\<lambda>A. \<sigma> ` A)) (anonymous_profile R) = anonymous_profile R"
  shows   "\<sigma> ` scf R = scf R"
  using scf_anonymous_neutral[OF perm wf wf eq [symmetric]] ..

end

lemma an_scf_automorphism_aux:
  assumes wf: "prefs_from_table_wf agents alts yss" "R \<equiv> prefs_from_table yss"
  assumes an: "an_scf agents alts scf"
  assumes eq: "mset (map ((map (\<lambda>A. permutation_of_list xs ` A)) \<circ> snd) yss) = mset (map snd yss)"
  assumes perm: "set (map fst xs) \<subseteq> alts" "set (map snd xs) = set (map fst xs)" 
                "distinct (map fst xs)" 
      and x: "x \<in> alts" "y = permutation_of_list xs x"
  shows   "x \<in> scf R \<longleftrightarrow> y \<in> scf R"
proof -
  note perm = list_permutesI[OF perm]
  let ?\<sigma> = "permutation_of_list xs"
  note perm' = permutation_of_list_permutes [OF perm]
  from wf have wf': "pref_profile_wf agents alts R" by (simp add: pref_profile_from_tableI)
  then interpret R: pref_profile_wf agents alts R .
  from perm' interpret R': pref_profile_wf agents alts "permute_profile ?\<sigma> R"
    by (simp add: R.wf_permute_alts)
  from an interpret an_scf agents alts scf .

  from eq wf have eq': "image_mset (map (\<lambda>A. ?\<sigma> ` A)) (anonymous_profile R) = anonymous_profile R"
    by (simp add: anonymise_prefs_from_table mset_map multiset.map_comp)
  have "x \<in> scf R \<longleftrightarrow> ?\<sigma> x \<in> ?\<sigma> ` scf R"
    by (blast dest: injD[OF permutes_inj[OF perm']])
  also from eq' x wf' perm' have "?\<sigma> ` scf R = scf R"
    by (intro scf_automorphism) 
       (simp_all add: R.anonymous_profile_permute pref_profile_from_tableI)
  finally show ?thesis using x by simp
qed


subsection \<open>Weighted-majoritarian SCFs\<close>

locale pairwise_scf = social_choice_function agents alts scf
  for agents :: "'agent set" and alts :: "'alt set" and scf +
  assumes pairwise:
    "is_pref_profile R1 \<Longrightarrow> is_pref_profile R2 \<Longrightarrow> weighted_majority R1 = weighted_majority R2 \<Longrightarrow>
       scf R1 = scf R2"

subsection \<open>Pareto efficiency\<close>

locale pareto_efficient_scf = social_choice_function agents alts scf
  for agents :: "'agent set" and alts :: "'alt set" and scf +
  assumes pareto_efficient: 
    "is_pref_profile R \<Longrightarrow> scf R \<inter> pareto_losers R = {}"
begin

lemma pareto_efficient':
  assumes "is_pref_profile R" "y \<succ>[Pareto(R)] x"
  shows   "x \<notin> scf R"
  using pareto_efficient[of R] assms 
  by (auto simp: pareto_losers_def)

lemma pareto_efficient'':
  assumes "is_pref_profile R" "i \<in> agents"  "\<forall>i\<in>agents. y \<succeq>[R i] x" "\<not>y \<preceq>[R i] x"
  shows   "x \<notin> scf R"
proof -
  from assms(1) interpret pref_profile_wf agents alts R .
  from assms(2-) show ?thesis
    by (intro pareto_efficient'[OF assms(1), of _ y])
       (auto simp: Pareto_iff strongly_preferred_def)
qed

end


subsection \<open>Set extensions\<close>

type_synonym 'alt set_extension = "'alt relation \<Rightarrow> 'alt set relation"

definition Kelly :: "'alt set_extension" where
  "A \<succeq>[Kelly(R)] B \<longleftrightarrow> (\<forall>a\<in>A. \<forall>b\<in>B. a \<succeq>[R] b)"

lemma Kelly_strict_iff: "A \<succ>[Kelly(R)] B \<longleftrightarrow> ((\<forall>a\<in>A. \<forall>b\<in>B. R b a) \<and> \<not> (\<forall>a\<in>B. \<forall>b\<in>A. R b a))"
  unfolding strongly_preferred_def Kelly_def ..

lemmas Kelly_eval = Kelly_def Kelly_strict_iff

definition Fishb :: "'alt set_extension" where
  "A \<succeq>[Fishb(R)] B \<longleftrightarrow> (\<forall>a\<in>A. \<forall>b\<in>B-A. a \<succeq>[R] b) \<and> (\<forall>a\<in>A-B. \<forall>b\<in>B. a \<succeq>[R] b)"

lemma Fishb_strict_iff: 
  "A \<succ>[Fishb(R)] B \<longleftrightarrow> 
     ((\<forall>a\<in>A. \<forall>b\<in>B - A. R b a) \<and> (\<forall>a\<in>A - B. \<forall>b\<in>B. R b a)) \<and>
     \<not> ((\<forall>a\<in>B. \<forall>b\<in>A - B. R b a) \<and> (\<forall>a\<in>B - A. \<forall>b\<in>A. R b a))"
  unfolding strongly_preferred_def Fishb_def ..

lemmas Fishb_eval = Fishb_def Fishb_strict_iff


subsection \<open>Strategyproofness\<close>

locale strategyproof_scf = 
  social_choice_function agents alts scf
  for agents :: "'agent set" and alts :: "'alt set" and scf +
  fixes set_ext :: "'alt set_extension"
  assumes strategyproof: 
    "is_pref_profile R \<Longrightarrow> total_preorder_on alts Ri' \<Longrightarrow> i \<in> agents \<Longrightarrow>
       \<not> scf (R(i := Ri')) \<succ>[set_ext(R i)] scf R"

locale strategyproof_anonymous_scf =
  anonymous_scf agents alts scf + strategyproof_scf agents alts scf set_ext
  for agents :: "'agent set" and alts :: "'alt set" and scf and set_ext
begin

lemma strategyproof':
  assumes "is_pref_profile R1" "is_pref_profile R2" "i \<in> agents" "j \<in> agents"
  assumes "anonymous_profile R2 = anonymous_profile R1 - 
             {#weak_ranking (R1 i)#} + {#weak_ranking (R2 j)#}"
  shows   "\<not>scf R2 \<succ>[set_ext (R1 i)] scf R1"
proof -
  let ?R3 = "R1(i := R2 j)"
  interpret R1: pref_profile_wf agents alts R1 by fact
  interpret R2: pref_profile_wf agents alts R2 by fact
  from \<open>j \<in> agents\<close> have "total_preorder_on alts (R2 j)" by simp
  from strategyproof[OF assms(1) this \<open>i \<in> agents\<close>] 
    have "\<not>scf ?R3 \<succ>[set_ext (R1 i)] scf R1" .
  also from assms have "scf ?R3 = scf R2"
    by (intro anonymous') (simp_all add: R1.anonymous_profile_update)
  finally show ?thesis .
qed

end

context preorder_on
begin

lemma strict_not_outside:
  assumes "x \<prec>[le] y"
  shows   "x \<in> carrier" "y \<in> carrier"
  using assms not_outside[of x y] unfolding strongly_preferred_def by blast+

end


subsection \<open>Lifting preferences\<close>

text \<open>
  Preference profiles can be lifted to a setting with more agents and alternatives by padding
  them with dummy agents and alternatives in such a way that every original agent prefers and
  original alternative over any dummy alternative and is indifferent between the dummy alternatives.
  Moreover, every dummy agent is completely indifferent.
\<close>

definition lift_prefs :: 
    "'alt set \<Rightarrow> 'alt set \<Rightarrow> 'alt relation \<Rightarrow> 'alt relation" where
  "lift_prefs alts alts' R = (\<lambda>x y. 
     x \<in> alts' \<and> y \<in> alts' \<and> (x = y \<or> x \<notin> alts \<or> (y \<in> alts \<and> R x y)))"

lemma lift_prefs_wf:
  assumes "total_preorder_on alts R" "alts \<subseteq> alts'"
  shows   "total_preorder_on alts' (lift_prefs alts alts' R)"
proof -
  interpret R: total_preorder_on alts R by fact
  show ?thesis
    by standard (insert R.total, auto dest: R.trans simp: lift_prefs_def)
qed

definition lift_pref_profile :: 
    "'agent set \<Rightarrow> 'alt set \<Rightarrow> 'agent set \<Rightarrow> 'alt set \<Rightarrow>
       ('agent, 'alt) pref_profile \<Rightarrow> ('agent, 'alt) pref_profile" where
  "lift_pref_profile agents alts agents' alts' R = (\<lambda>i x y. 
     x \<in> alts' \<and> y \<in> alts' \<and> i \<in> agents' \<and>
     (x = y \<or> x \<notin> alts \<or> i \<notin> agents \<or> (y \<in> alts \<and> R i x y)))"

lemma lift_pref_profile_conv_vector:
  assumes "i \<in> agents" "i \<in> agents'"
  shows   "lift_pref_profile agents alts agents' alts' R i = lift_prefs alts alts' (R i)"
  using assms by (auto simp: lift_pref_profile_def lift_prefs_def)

lemma lift_pref_profile_wf:
  assumes "pref_profile_wf agents alts R"
  assumes "agents \<subseteq> agents'" "alts \<subseteq> alts'" "finite alts'"
  defines "R' \<equiv> lift_pref_profile agents alts agents' alts' R"
  shows   "pref_profile_wf agents' alts' R'"
proof -
  from assms interpret R: pref_profile_wf agents alts by simp
  have "finite_total_preorder_on alts' (R' i)" 
    if i: "i \<in> agents'" for i
  proof (cases "i \<in> agents")
    case True
    then interpret finite_total_preorder_on alts "R i" by simp
    from True assms show ?thesis
      by unfold_locales (auto simp: lift_pref_profile_def dest: total intro: trans)
  next 
    case False
    with assms i show ?thesis
      by unfold_locales (simp_all add: lift_pref_profile_def)
  qed
  moreover have "R' i = (\<lambda>_ _. False)" if "i \<notin> agents'" for i
    unfolding lift_pref_profile_def R'_def using that by simp
  ultimately show ?thesis unfolding pref_profile_wf_def using assms by auto
qed

lemma lift_pref_profile_permute_agents:
  assumes "\<pi> permutes agents" "agents \<subseteq> agents'"
  shows   "lift_pref_profile agents alts agents' alts' (R \<circ> \<pi>) = 
             lift_pref_profile agents alts agents' alts' R \<circ> \<pi>"
  using assms permutes_subset[OF assms]
  by (auto simp add: lift_pref_profile_def o_def permutes_in_image)

lemma lift_pref_profile_permute_alts:
  assumes "\<sigma> permutes alts" "alts \<subseteq> alts'"
  shows   "lift_pref_profile agents alts agents' alts' (permute_profile \<sigma> R) = 
             permute_profile \<sigma> (lift_pref_profile agents alts agents' alts' R)"
proof -
  from assms have inv: "inv \<sigma> permutes alts" by (intro permutes_inv)
  from this assms(2) have "inv \<sigma> permutes alts'" by (rule permutes_subset)
  with inv show ?thesis using assms permutes_inj[OF \<open>inv \<sigma> permutes alts\<close>]
    by (fastforce simp add: lift_pref_profile_def permutes_in_image
          permute_profile_def fun_eq_iff dest: injD)
qed


context
  fixes agents alts R agents' alts' R'
  assumes R_wf: "pref_profile_wf agents alts R"
  assumes election: "agents \<subseteq> agents'" "alts \<subseteq> alts'" "alts \<noteq> {}" "agents \<noteq> {}" "finite alts'"
  defines "R' \<equiv> lift_pref_profile agents alts agents' alts' R"
begin

interpretation R: pref_profile_wf agents alts R by fact
interpretation R': pref_profile_wf agents' alts' R' 
  using election R_wf by (simp add: R'_def lift_pref_profile_wf)

lemma lift_pref_profile_strict_iff:
  "x \<prec>[lift_pref_profile agents alts agents' alts' R i] y \<longleftrightarrow>
     i \<in> agents \<and> ((y \<in> alts \<and> x \<in> alts' - alts) \<or> x \<prec>[R i] y)"
proof (cases "i \<in> agents")
  case True
  then interpret total_preorder_on alts "R i" by simp
  show ?thesis using not_outside election
    by (auto simp: lift_pref_profile_def strongly_preferred_def)
qed (simp_all add: lift_pref_profile_def strongly_preferred_def)

lemma preferred_alts_lift_pref_profile: 
  assumes i: "i \<in> agents'" and x: "x \<in> alts'"
  shows   "preferred_alts (R' i) x = 
             (if i \<in> agents \<and> x \<in> alts then preferred_alts (R i) x else alts')"
proof (cases "i \<in> agents")
  assume i: "i \<in> agents"
  then interpret Ri: total_preorder_on alts "R i" by simp
  show ?thesis
  using i x election Ri.not_outside
    by (auto simp: preferred_alts_def R'_def lift_pref_profile_def Ri.refl)
qed (auto simp: preferred_alts_def R'_def lift_pref_profile_def i x)

lemma lift_pref_profile_Pareto_iff:
  "x \<preceq>[Pareto(R')] y \<longleftrightarrow> x \<in> alts' \<and> y \<in> alts' \<and> (x \<notin> alts \<or> x \<preceq>[Pareto(R)] y)"
proof -
  from R.nonempty_agents obtain i where i: "i \<in> agents" by blast
  then interpret Ri: finite_total_preorder_on alts "R i" by simp
  show ?thesis unfolding R'.Pareto_iff R.Pareto_iff unfolding R'_def lift_pref_profile_def
    using election i by (auto simp: preorder_on.refl[OF R.in_dom] 
      simp del: R.nonempty_alts R.nonempty_agents  intro: Ri.not_outside)
qed

lemma lift_pref_profile_Pareto_strict_iff:
  "x \<prec>[Pareto(R')] y \<longleftrightarrow> x \<in> alts' \<and> y \<in> alts' \<and> (x \<notin> alts \<and> y \<in> alts \<or> x \<prec>[Pareto(R)] y)"
  by (auto simp: strongly_preferred_def lift_pref_profile_Pareto_iff R.Pareto.not_outside)

lemma pareto_losers_lift_pref_profile:
  shows   "pareto_losers R' = pareto_losers R \<union> (alts' - alts)"
proof -
  have A: "x \<in> alts" "y \<in> alts" if "x \<prec>[Pareto(R)] y" for x y
    using that R.Pareto.not_outside unfolding strongly_preferred_def by auto
  have B: "x \<in> alts'" if "x \<in> alts" for x using election that by blast
  from R.nonempty_alts obtain x where x: "x \<in> alts" by blast
  thus ?thesis unfolding pareto_losers_def lift_pref_profile_Pareto_strict_iff [abs_def]
    by (auto dest: A B)
qed

end


subsection \<open>Lowering SCFs\<close>

text \<open>
  Using the preference lifting, we can now \emph{lower} an SCF to a setting with fewer agents
  and alternatives under mild conditions to the original SCF. This preserves many nice properties, 
  such as anonymity, neutrality, and strategyproofness.
\<close>

locale scf_lowering = 
  pareto_efficient_scf agents alts scf
  for agents :: "'agent set" and alts :: "'alt set" and scf +
  fixes agents' alts' 
  assumes agents'_subset: "agents' \<subseteq> agents" and alts'_subset: "alts' \<subseteq> alts"
      and agents'_nonempty [simp]: "agents' \<noteq> {}" and alts'_nonempty [simp]: "alts' \<noteq> {}"
begin

lemma finite_agents' [simp]: "finite agents'"
  using agents'_subset finite_agents by (rule finite_subset)

lemma finite_alts' [simp]: "finite alts'"
  using alts'_subset finite_alts by (rule finite_subset)

abbreviation lift :: "('agent, 'alt) pref_profile \<Rightarrow> ('agent, 'alt) pref_profile" where
  "lift \<equiv> lift_pref_profile agents' alts' agents alts"

definition lowered :: "('agent, 'alt) pref_profile \<Rightarrow> 'alt set" where
  "lowered = scf \<circ> lift"

lemma lift_wf [simp, intro]: 
  "pref_profile_wf agents' alts' R \<Longrightarrow> is_pref_profile (lift R)"
  using alts'_subset agents'_subset by (intro lift_pref_profile_wf) simp_all

sublocale lowered: election agents' alts'
  by unfold_locales simp_all

lemma preferred_alts_lift:
  "lowered.is_pref_profile R \<Longrightarrow> i \<in> agents \<Longrightarrow> x \<in> alts \<Longrightarrow>
     preferred_alts (lift R i) x = 
       (if i \<in> agents' \<and> x \<in> alts' then preferred_alts (R i) x else alts)"
  using alts'_subset agents'_subset
  by (intro preferred_alts_lift_pref_profile) simp_all

lemma pareto_losers_lift:
  "lowered.is_pref_profile R \<Longrightarrow> pareto_losers (lift R) = pareto_losers R \<union> (alts - alts')"
  using agents'_subset alts'_subset by (intro pareto_losers_lift_pref_profile) simp_all


sublocale lowered: social_choice_function agents' alts' lowered
proof
  fix R assume R_wf: "pref_profile_wf agents' alts' R"
  from R_wf have R'_wf: "pref_profile_wf agents alts (lift R)" by (rule lift_wf)
  show "lowered R \<subseteq> alts'"
  proof safe
    fix x assume "x \<in> lowered R"
    hence "x \<in> scf (lift R)" by (auto simp: o_def lowered_def)
    moreover have "scf (lift R) \<inter> pareto_losers (lift R) = {}"
      by (intro pareto_efficient R'_wf)
    ultimately show "x \<in> alts'" using scf_alts[of "lift R"]
      by (auto simp: pareto_losers_lift R_wf R'_wf)
  qed
  show "lowered R \<noteq> {}"
    using R'_wf by (auto simp: lowered_def scf_nonempty)
qed

sublocale lowered: pareto_efficient_scf agents' alts' lowered
proof
  fix R assume R_wf: "pref_profile_wf agents' alts' R"
  from R_wf have R'_wf: "pref_profile_wf agents alts (lift R)" by (rule lift_wf)
  have "lowered R \<inter> pareto_losers (lift R) = {}" unfolding lowered_def o_def
    by (intro pareto_efficient R'_wf)
  with R_wf show "lowered R \<inter> pareto_losers R = {}"
    by (auto simp: pareto_losers_lift)
qed

end


locale scf_lowering_anonymous = 
  anonymous_scf agents alts scf +
  scf_lowering agents alts scf agents' alts'
  for agents :: "'agent set" and alts :: "'alt set" and scf agents' alts'
begin

sublocale lowered: anonymous_scf agents' alts' lowered
proof
  fix \<pi> R
  assume "\<pi> permutes agents'" and "lowered.is_pref_profile R"
  thus "lowered (R \<circ> \<pi>) = lowered R" using agents'_subset
    by (auto simp: lowered_def lift_pref_profile_permute_agents anonymous permutes_subset)
qed

end


locale scf_lowering_neutral = 
  neutral_scf agents alts scf +
  scf_lowering agents alts scf agents' alts'
  for agents :: "'agent set" and alts :: "'alt set" and scf agents' alts'
begin

sublocale lowered: neutral_scf agents' alts' lowered
proof
  fix \<sigma> R
  assume "\<sigma> permutes alts'" and "lowered.is_pref_profile R"
  thus "lowered (permute_profile \<sigma> R) = \<sigma> ` lowered R" using alts'_subset
    by (auto simp: lowered_def lift_pref_profile_permute_alts neutral permutes_subset)
qed

end

text \<open>
  The following is a technical condition that we need from a set extensions in order for
  strategyproofness to survive the lowering. The condition could probably be weakened a bit,
  but it is good enough for our purposes the way it is.
\<close>
locale liftable_set_extension =
  fixes alts' alts :: "'alt set" and set_ext :: "'alt relation \<Rightarrow> 'alt set relation"
  assumes set_ext_strong_lift:
    "total_preorder_on alts' R \<Longrightarrow> A \<noteq> {} \<Longrightarrow> B \<noteq> {} \<Longrightarrow> A \<subseteq> alts' \<Longrightarrow> B \<subseteq> alts' \<Longrightarrow>
       A \<prec>[set_ext R] B \<Longrightarrow> A \<prec>[set_ext (lift_prefs alts' alts R)] B"

lemma liftable_set_extensionI_weak:
  assumes "\<And>R A B. total_preorder_on alts' R \<Longrightarrow> A \<noteq> {} \<Longrightarrow> B \<noteq> {} \<Longrightarrow> 
                      A \<subseteq> alts' \<Longrightarrow> B \<subseteq> alts' \<Longrightarrow>
              A \<preceq>[set_ext R] B \<longleftrightarrow> A \<preceq>[set_ext (lift_prefs alts' alts R)] B"
  shows   "liftable_set_extension alts' alts set_ext"
proof (standard, goal_cases)
  case (1 R A B)
  from assms[of R A B] and assms[of R B A] and 1 show ?case
    by (auto simp: strongly_preferred_def)
qed

lemma Kelly_liftable:
  assumes "alts' \<subseteq> alts"
  shows   "liftable_set_extension alts' alts Kelly"
proof (rule liftable_set_extensionI_weak, goal_cases)
  case (1 R A B)
  interpret R: total_preorder_on alts' R by fact
  from 1(2-5) show ?case using assms  R.refl
    by (force simp: Kelly_def lift_prefs_def)
qed

lemma Fishburn_liftable:
  assumes "alts' \<subseteq> alts"
  shows   "liftable_set_extension alts' alts Fishb"
proof (rule liftable_set_extensionI_weak, goal_cases)
  case (1 R A B)
  interpret R: total_preorder_on alts' R by fact
  have conj_cong: "P1 \<and> Q1 \<longleftrightarrow> P2 \<and> Q2" if "P1 \<longleftrightarrow> P2" "Q1 \<longleftrightarrow> Q2" for P1 P2 Q1 Q2
    using that by blast
  from 1(2-5) show ?case using assms
    unfolding Fishb_def lift_prefs_def by (intro conj_cong ball_cong refl) auto
qed

locale scf_lowering_strategyproof =
  strategyproof_scf agents alts scf set_ext +
  liftable_set_extension alts' alts set_ext +
  scf_lowering agents alts scf agents' alts'
  for agents :: "'agent set" and alts :: "'alt set" and scf agents' alts' set_ext
begin

sublocale lowered: strategyproof_scf agents' alts' lowered
proof
  fix R Ri' i
  assume R_wf: "lowered.is_pref_profile R" and Ri'_wf: "total_preorder_on alts' Ri'" 
     and i: "i \<in> agents'"
  interpret R: pref_profile_wf agents' alts' R by fact
  interpret Ri': total_preorder_on alts' Ri' by fact
  from R_wf have R'_wf: "is_pref_profile (lift R)" by (rule lift_wf)

  \<comment> \<open>We lift the alternative preference for the agent @{term i} in @{term R} to 
      preferences in the lifted profile. \<close>
  define Ri'' where "Ri'' = lift_prefs alts' alts Ri'"

  have "\<not>scf (lift R) \<prec>[set_ext (lift R i)] scf ((lift R)(i := Ri''))"
    using i agents'_subset alts'_subset unfolding Ri''_def
    by (intro strategyproof R'_wf Ri'_wf lift_prefs_wf) auto
  also have "(lift R)(i := Ri'') = lift (R(i := Ri'))" using i agents'_subset
    by (auto simp: fun_eq_iff Ri''_def lift_pref_profile_def lift_prefs_def)
  finally have not_less: "\<not>scf (lift R) \<prec>[set_ext (lift R i)] scf (lift (R(i := Ri')))" .

  show "\<not>lowered R \<prec>[set_ext (R i)] lowered (R(i := Ri'))"
  proof
    assume "lowered R \<prec>[set_ext (R i)] lowered (R(i := Ri'))"
    hence "lowered R \<prec>[set_ext (lift_prefs alts' alts (R i))] lowered (R(i := Ri'))"
      by (intro set_ext_strong_lift R.prefs_wf'(1) i lowered.scf_nonempty lowered.scf_alts
                R.wf_update R_wf Ri'_wf)
    also have "lift_prefs alts' alts (R i) = lift R i"
      using agents'_subset i by (subst lift_pref_profile_conv_vector) auto
    finally show False using not_less unfolding lowered_def o_def by contradiction
  qed
qed
    
end

end