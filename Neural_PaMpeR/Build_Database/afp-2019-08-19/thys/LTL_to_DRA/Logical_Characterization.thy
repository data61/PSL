(*  
    Author:      Salomon Sickert
    License:     BSD
*)

section \<open>Logical Characterization Theorems\<close>

theory Logical_Characterization
  imports Main af "Auxiliary/Preliminaries2"
begin

subsection \<open>Eventually True G-Subformulae\<close>

fun \<G>\<^sub>F\<^sub>G :: "'a ltl \<Rightarrow> 'a set word \<Rightarrow> 'a ltl set"
where
  "\<G>\<^sub>F\<^sub>G true w = {}"
| "\<G>\<^sub>F\<^sub>G (false) w = {}"
| "\<G>\<^sub>F\<^sub>G (p(a)) w = {}"
| "\<G>\<^sub>F\<^sub>G (np(a)) w = {}"
| "\<G>\<^sub>F\<^sub>G (\<phi>\<^sub>1 and \<phi>\<^sub>2) w = \<G>\<^sub>F\<^sub>G \<phi>\<^sub>1 w \<union> \<G>\<^sub>F\<^sub>G \<phi>\<^sub>2 w"
| "\<G>\<^sub>F\<^sub>G (\<phi>\<^sub>1 or \<phi>\<^sub>2) w = \<G>\<^sub>F\<^sub>G \<phi>\<^sub>1 w \<union> \<G>\<^sub>F\<^sub>G \<phi>\<^sub>2 w"
| "\<G>\<^sub>F\<^sub>G (F \<phi>) w = \<G>\<^sub>F\<^sub>G \<phi> w"
| "\<G>\<^sub>F\<^sub>G (G \<phi>) w = (if w \<Turnstile> F G \<phi> then {G \<phi>} \<union> \<G>\<^sub>F\<^sub>G \<phi> w else \<G>\<^sub>F\<^sub>G \<phi> w)"
| "\<G>\<^sub>F\<^sub>G (X \<phi>) w = \<G>\<^sub>F\<^sub>G \<phi> w"
| "\<G>\<^sub>F\<^sub>G (\<phi> U \<psi>) w = \<G>\<^sub>F\<^sub>G \<phi> w \<union> \<G>\<^sub>F\<^sub>G \<psi> w"
 
lemma \<G>\<^sub>F\<^sub>G_alt_def:
  "\<G>\<^sub>F\<^sub>G \<phi> w = {G \<psi> | \<psi>. G \<psi> \<in> \<^bold>G \<phi> \<and> w \<Turnstile> F (G \<psi>)}"
  by (induction \<phi> arbitrary: w) (simp; blast)+

lemma \<G>\<^sub>F\<^sub>G_Only_G:
  "Only_G (\<G>\<^sub>F\<^sub>G \<phi> w)"
   by (induction \<phi>) auto

lemma \<G>\<^sub>F\<^sub>G_suffix[simp]:
  "\<G>\<^sub>F\<^sub>G \<phi> (suffix i w) = \<G>\<^sub>F\<^sub>G \<phi> w"
  unfolding \<G>\<^sub>F\<^sub>G_alt_def LTL_FG_suffix ..

subsection \<open>Eventually Provable and Almost All Eventually Provable\<close>

abbreviation \<PP>
where
  "\<PP> \<phi> \<G> w i \<equiv> \<exists>j. \<G> \<Turnstile>\<^sub>P af\<^sub>G \<phi> (w [i \<rightarrow> j])"

definition almost_all_eventually_provable :: "'a ltl \<Rightarrow> 'a ltl set \<Rightarrow> 'a set word \<Rightarrow> bool" ("\<PP>\<^sub>\<infinity>") 
where
  "\<PP>\<^sub>\<infinity> \<phi> \<G> w \<equiv> \<forall>\<^sub>\<infinity>i. \<PP> \<phi> \<G> w i"

subsubsection \<open>Proof Rules\<close>

lemma almost_all_eventually_provable_monotonI[intro]:
  "\<PP>\<^sub>\<infinity> \<phi> \<G> w \<Longrightarrow> \<G> \<subseteq> \<G>' \<Longrightarrow> \<PP>\<^sub>\<infinity> \<phi> \<G>' w"
  unfolding almost_all_eventually_provable_def MOST_nat_le by blast

lemma almost_all_eventually_provable_restrict_to_G:
  "\<PP>\<^sub>\<infinity> \<phi> \<G> w \<Longrightarrow> Only_G \<G> \<Longrightarrow> \<PP>\<^sub>\<infinity> \<phi> (\<G> \<inter> \<^bold>G \<phi>) w"
proof -
  assume "Only_G \<G>" and "\<PP>\<^sub>\<infinity> \<phi> \<G> w"
  moreover
  hence "\<And>\<phi>. \<G> \<Turnstile>\<^sub>P \<phi> = (\<G> \<inter> \<^bold>G \<phi>) \<Turnstile>\<^sub>P \<phi>"
    using LTL_prop_entailment_restrict_to_propos propos_subset
    unfolding G_nested_propos_alt_def by blast
  ultimately
  show ?thesis
    unfolding almost_all_eventually_provable_def by force
qed

fun G_depth :: "'a ltl \<Rightarrow> nat"
where 
  "G_depth (\<phi> and \<psi>) = max (G_depth \<phi>) (G_depth \<psi>)"
| "G_depth (\<phi> or \<psi>) = max (G_depth \<phi>) (G_depth \<psi>)"
| "G_depth (F \<phi>) = G_depth \<phi>"
| "G_depth (G \<phi>) = G_depth \<phi> + 1"
| "G_depth (X \<phi>) = G_depth \<phi>"
| "G_depth (\<phi> U \<psi>) = max (G_depth \<phi>) (G_depth \<psi>)"
| "G_depth \<phi> = 0"

lemma almost_all_eventually_provable_restrict_to_G_depth:
  assumes "\<PP>\<^sub>\<infinity> \<phi> \<G> w"
  assumes "Only_G \<G>"
  shows "\<PP>\<^sub>\<infinity> \<phi> (\<G> \<inter> {\<psi>. G_depth \<psi> \<le> G_depth \<phi>}) w"
proof -
  { 
    fix \<phi> 
    have "\<G> \<Turnstile>\<^sub>P \<phi> = (\<G> \<inter> {\<psi>. G_depth \<psi> \<le> G_depth \<phi>}) \<Turnstile>\<^sub>P \<phi>"
      by (induction \<phi>) (insert \<open>Only_G \<G>\<close>, auto) 
  } 
  note Unfold1 = this
  
  {
    fix w
    { 
      fix \<phi> \<nu> 
      have "{\<psi>. G_depth \<psi> \<le> G_depth (af_G_letter \<phi> \<nu>)} = {\<psi>. G_depth \<psi> \<le> G_depth \<phi>}" 
        by (induction \<phi>) (unfold af_G_letter.simps G_depth.simps, simp_all, (metis le_max_iff_disj mem_Collect_eq)+) 
    }
    hence "{\<psi>. G_depth \<psi> \<le> G_depth (af\<^sub>G \<phi> w)} = {\<psi>. G_depth \<psi> \<le> G_depth \<phi>}"
      by (induction w arbitrary: \<phi> rule: rev_induct) fastforce+
  }
  note Unfold2 = this

  from assms(1) show ?thesis
    unfolding almost_all_eventually_provable_def Unfold1 Unfold2 .
qed

lemma almost_all_eventually_provable_suffix:
  "\<PP>\<^sub>\<infinity> \<phi> \<G>' w \<Longrightarrow> \<PP>\<^sub>\<infinity> \<phi> \<G>' (suffix i w)"
  unfolding almost_all_eventually_provable_def MOST_nat_le
  by (metis Nat.add_0_right subsequence_shift subsequence_prefix_suffix suffix_0 add.assoc diff_zero trans_le_add2) 

subsubsection \<open>Threshold\<close>

text \<open>The first index, such that the formula is eventually provable from this time on\<close>

fun threshold :: "'a ltl \<Rightarrow> 'a set  word \<Rightarrow> 'a ltl set \<Rightarrow> nat option"
where
  "threshold \<phi> w \<G> = index (\<lambda>j. \<PP> \<phi> \<G> w j)"

lemma threshold_properties:
  "threshold \<phi> w \<G> = Some i \<Longrightarrow> 0 < i \<Longrightarrow> \<not> \<G> \<Turnstile>\<^sub>P af\<^sub>G \<phi> (w [(i - 1) \<rightarrow> k])"
  "threshold \<phi> w \<G> = Some i \<Longrightarrow> j \<ge> i \<Longrightarrow> \<exists>k. \<G> \<Turnstile>\<^sub>P af\<^sub>G \<phi> (w [j \<rightarrow> k])"
  using index_properties unfolding threshold.simps by blast+

lemma threshold_suffix:
  assumes "threshold \<phi> w \<G> = Some k"
  assumes "threshold \<phi> (suffix i w) \<G> = Some k'"
  shows "k \<le> k' + i"
proof (rule ccontr)
  assume "\<not>k \<le> k' + i"
  hence "k > k' + i"
    by arith
  then obtain j where "k = k' + i + Suc j"
    by (metis Suc_diff_Suc le_Suc_eq le_add1 le_add_diff_inverse less_imp_Suc_add)
  hence "0 < k" and "k' + i + Suc j - 1 = i + (k' + j)"
    using \<open>k > k' + i\<close> by arith+
  show False
    using threshold_properties(1)[OF assms(1) \<open>0 < k\<close>] threshold_properties(2)[OF assms(2), of "k' + j", OF le_add1] 
    unfolding subsequence_shift \<open>k = k' + i + Suc j\<close> \<open>k' + i + Suc j - 1 = i + (k' + j)\<close> by blast
qed

subsubsection \<open>Relation to LTL semantics\<close>

lemma ltl_implies_provable:
  "w \<Turnstile> \<phi> \<Longrightarrow> \<PP> \<phi> (\<G>\<^sub>F\<^sub>G \<phi> w) w 0"
proof (induction \<phi> arbitrary: w)
  case (LTLProp a)
    hence "{} \<Turnstile>\<^sub>P af\<^sub>G (p(a)) (w [0 \<rightarrow> 1])"
      by (simp add: subsequence_def)
    thus ?case 
      by blast
next
  case (LTLPropNeg a)
    hence "{} \<Turnstile>\<^sub>P af\<^sub>G (np(a)) (w [0 \<rightarrow> 1])"
      by (simp add: subsequence_def)
    thus ?case 
      by blast
next
  case (LTLAnd \<phi>\<^sub>1 \<phi>\<^sub>2)
    obtain i\<^sub>1 i\<^sub>2 where "(\<G>\<^sub>F\<^sub>G \<phi>\<^sub>1 w) \<Turnstile>\<^sub>P af\<^sub>G \<phi>\<^sub>1 (w [0 \<rightarrow> i\<^sub>1])" and "(\<G>\<^sub>F\<^sub>G \<phi>\<^sub>2 w) \<Turnstile>\<^sub>P af\<^sub>G \<phi>\<^sub>2 (w [0 \<rightarrow> i\<^sub>2])"
      using LTLAnd unfolding ltl_semantics.simps by blast
    have "(\<G>\<^sub>F\<^sub>G \<phi>\<^sub>1 w) \<Turnstile>\<^sub>P af\<^sub>G \<phi>\<^sub>1 (w [0 \<rightarrow> i\<^sub>1 + i\<^sub>2])" and "(\<G>\<^sub>F\<^sub>G \<phi>\<^sub>2 w) \<Turnstile>\<^sub>P af\<^sub>G \<phi>\<^sub>2 (w [0 \<rightarrow> i\<^sub>2 + i\<^sub>1])"
      using af\<^sub>G_sat_core_generalized[OF \<G>\<^sub>F\<^sub>G_Only_G _ \<open>(\<G>\<^sub>F\<^sub>G \<phi>\<^sub>1 w) \<Turnstile>\<^sub>P af\<^sub>G \<phi>\<^sub>1 (w [0 \<rightarrow> i\<^sub>1])\<close>]
      using af\<^sub>G_sat_core_generalized[OF \<G>\<^sub>F\<^sub>G_Only_G _ \<open>(\<G>\<^sub>F\<^sub>G \<phi>\<^sub>2 w) \<Turnstile>\<^sub>P af\<^sub>G \<phi>\<^sub>2 (w [0 \<rightarrow> i\<^sub>2])\<close>]
      by simp+
    thus ?case 
      by (simp only: af\<^sub>G_decompose add.commute) auto
next
  case (LTLOr \<phi>\<^sub>1 \<phi>\<^sub>2)
    thus ?case 
      unfolding af\<^sub>G_decompose by (cases "w \<Turnstile> \<phi>\<^sub>1") force+
next
  case (LTLNext \<phi>)
    obtain i where "(\<G>\<^sub>F\<^sub>G \<phi> w) \<Turnstile>\<^sub>P af\<^sub>G \<phi> (suffix 1 w [0 \<rightarrow> i])"
      using LTLNext(1)[OF LTLNext(2)[unfolded ltl_semantics.simps]] 
      unfolding \<G>\<^sub>F\<^sub>G_suffix by blast
    hence "(\<G>\<^sub>F\<^sub>G (X \<phi>) w) \<Turnstile>\<^sub>P af\<^sub>G (X \<phi>) (w [0 \<rightarrow> 1 + i])"  
      unfolding subsequence_shift subsequence_append by (simp add: subsequence_def)
    thus ?case
      by blast
next
  case (LTLFinal \<phi>)
    then obtain i where "suffix i w \<Turnstile> \<phi>" 
      by auto
    then obtain j where "\<G>\<^sub>F\<^sub>G \<phi> w \<Turnstile>\<^sub>P af\<^sub>G \<phi> (suffix i w [0 \<rightarrow> j])"
      using LTLFinal \<G>\<^sub>F\<^sub>G_suffix by blast
    hence A: "\<G>\<^sub>F\<^sub>G \<phi> w \<Turnstile>\<^sub>P af\<^sub>G \<phi> (suffix i w [0 \<rightarrow> Suc j])"
      using af\<^sub>G_sat_core_generalized[OF \<G>\<^sub>F\<^sub>G_Only_G, of j "Suc j", OF le_SucI] by blast
    from af\<^sub>G_keeps_F_and_S[OF _ A] have "\<G>\<^sub>F\<^sub>G \<phi> w \<Turnstile>\<^sub>P af\<^sub>G (F \<phi>) (w [0 \<rightarrow> Suc (i + j)])"  
      unfolding subsequence_shift subsequence_append Suc_eq_plus1 by simp
    thus ?case
      using \<G>\<^sub>F\<^sub>G.simps(7) by blast
next
  case (LTLUntil \<phi> \<psi>)
    then obtain k where "suffix k w \<Turnstile> \<psi>" and "\<forall>j < k. suffix j w \<Turnstile> \<phi>"
      by auto
    thus ?case
    proof (induction k arbitrary: w)
      case 0
        then obtain i where "\<G>\<^sub>F\<^sub>G \<psi> w \<Turnstile>\<^sub>P af\<^sub>G \<psi> (w [0 \<rightarrow> i])"
          using LTLUntil by (metis suffix_0) 
        hence "\<G>\<^sub>F\<^sub>G \<psi> w \<Turnstile>\<^sub>P af\<^sub>G \<psi> (w [0 \<rightarrow> Suc i])"
          using af\<^sub>G_sat_core_generalized[OF \<G>\<^sub>F\<^sub>G_Only_G, of i "Suc i", OF  le_SucI] by auto
        hence "\<G>\<^sub>F\<^sub>G (\<phi> U \<psi>) w \<Turnstile>\<^sub>P af\<^sub>G (\<phi> U \<psi>) (w [0 \<rightarrow> Suc i])"
          unfolding af\<^sub>G_subsequence_U ltl_prop_entailment.simps \<G>\<^sub>F\<^sub>G.simps by blast  
        thus ?case
          by blast  
    next
      case (Suc k)
        hence "w \<Turnstile> \<phi>" and "suffix k (suffix 1 w) \<Turnstile> \<psi>" and "\<forall>j<k. suffix j (suffix 1 w) \<Turnstile> \<phi>"
          unfolding suffix_0 suffix_suffix by (auto, metis Suc_less_eq)+
        then obtain i where i_def: "\<G>\<^sub>F\<^sub>G (\<phi> U \<psi>) w \<Turnstile>\<^sub>P af\<^sub>G (\<phi> U \<psi>) (suffix 1 w [0 \<rightarrow> i])"
          using Suc(1)[of "suffix 1 w"] unfolding LTL_FG_suffix \<G>\<^sub>F\<^sub>G_alt_def by blast
        obtain j where j_def: "\<G>\<^sub>F\<^sub>G \<phi> w \<Turnstile>\<^sub>P af\<^sub>G \<phi> (w [0 \<rightarrow> j])"
          using LTLUntil(1)[OF \<open>w \<Turnstile> \<phi>\<close>] by auto
        hence "\<G>\<^sub>F\<^sub>G (\<phi> U \<psi>) w \<Turnstile>\<^sub>P af\<^sub>G \<phi> (w [0 \<rightarrow> j])"
          by auto

        hence "\<G>\<^sub>F\<^sub>G (\<phi> U \<psi>) w \<Turnstile>\<^sub>P af\<^sub>G \<phi> (w [0 \<rightarrow> j + (i + 1)])"
          by (blast intro: af\<^sub>G_sat_core_generalized[OF \<G>\<^sub>F\<^sub>G_Only_G le_add1])
        moreover
        have "1 + (i + j) = j + (i + 1)"
          by arith
        have "\<G>\<^sub>F\<^sub>G (\<phi> U \<psi>) w \<Turnstile>\<^sub>P af\<^sub>G (\<phi> U \<psi>) (w [1 \<rightarrow> j + (i + 1)])"
          using af\<^sub>G_sat_core_generalized[OF \<G>\<^sub>F\<^sub>G_Only_G le_add1 i_def, of j]
          unfolding subsequence_shift \<G>\<^sub>F\<^sub>G_suffix \<open>1 + (i + j) = j + (i + 1)\<close> by simp
        ultimately
        have "\<G>\<^sub>F\<^sub>G (\<phi> U \<psi>) w \<Turnstile>\<^sub>P af\<^sub>G (\<phi> U \<psi>) (w [1 \<rightarrow> Suc (j + i)]) and af\<^sub>G \<phi> (w [0 \<rightarrow> Suc (j + i)])"
          by simp
        hence "\<G>\<^sub>F\<^sub>G (\<phi> U \<psi>) w \<Turnstile>\<^sub>P af\<^sub>G (\<phi> U \<psi>) (w [0 \<rightarrow> Suc (j + i)])"
          unfolding af\<^sub>G_subsequence_U ltl_prop_entailment.simps by blast 
        thus ?case
          using af\<^sub>G_subsequence_U ltl_prop_entailment.simps by blast
    qed
qed simp+

lemma ltl_implies_provable_almost_all:
  "w \<Turnstile> \<phi> \<Longrightarrow> \<forall>\<^sub>\<infinity>i. \<G>\<^sub>F\<^sub>G \<phi> w \<Turnstile>\<^sub>P af\<^sub>G \<phi> (w [0 \<rightarrow> i])"
  using ltl_implies_provable af\<^sub>G_sat_core_generalized[OF \<G>\<^sub>F\<^sub>G_Only_G] 
  unfolding MOST_nat_le by metis

subsubsection \<open>Closed Sets\<close>

abbreviation closed
where
  "closed \<G> w \<equiv> finite \<G> \<and> Only_G \<G> \<and> (\<forall>\<psi>. G \<psi> \<in> \<G> \<longrightarrow> \<PP>\<^sub>\<infinity> \<psi> \<G> w)"

lemma closed_FG:
  assumes "closed \<G> w"
  assumes "G \<psi> \<in> \<G>"
  shows "w \<Turnstile> F G \<psi>"
proof - 
  have "finite \<G>" and "Only_G \<G>" and "(\<And>\<psi>. G \<psi> \<in> \<G> \<Longrightarrow> \<PP>\<^sub>\<infinity> \<psi> \<G> w)"
    using assms by simp+
  moreover
  note \<open>G \<psi> \<in> \<G>\<close>
  ultimately
  show "w \<Turnstile> F G \<psi>" 
  proof (induction arbitrary: \<psi> rule: finite_ranking_induct[where f = G_depth])
    case (insert x \<G>)
      (* Split \<psi>' out *)
      then obtain \<psi>' where "x = G \<psi>'"
        by auto
      {
        fix \<psi> assume "G \<psi> \<in> insert x \<G>" (is "_ \<in> ?\<G>'")
        hence "\<PP>\<^sub>\<infinity> \<psi> (?\<G>' \<inter> {\<psi>'. G_depth \<psi>' \<le> G_depth \<psi>}) w"  
          using insert(4-5) by (blast dest: almost_all_eventually_provable_restrict_to_G_depth)
        moreover
        have "G_depth \<psi> < G_depth x"
          using insert(2) \<open>G \<psi> \<in> insert x \<G>\<close> \<open>x = G \<psi>'\<close> by force
        ultimately
        have "\<PP>\<^sub>\<infinity> \<psi> \<G> w"
          by auto
      }
      hence "\<PP>\<^sub>\<infinity> \<psi>' \<G> w" and "closed \<G> w"
        using insert \<open>x = G \<psi>'\<close> by simp+
  
      (* Wait until all G-subformulae are "stable" *)
      have "Only_G \<G>" and "Only_G (\<G> \<union> \<^bold>G \<psi>')" and "finite (\<G> \<union> \<^bold>G \<psi>')"
        using G_nested_finite G_nested_propos_Only_G insert by blast+
      then obtain k\<^sub>1 where k1_def: "\<And>\<psi> i. \<psi> \<in> \<G> \<union> \<^bold>G \<psi>' \<Longrightarrow> suffix k\<^sub>1 w \<Turnstile> \<psi> = suffix (k\<^sub>1 + i) w \<Turnstile> \<psi>" 
        by (blast intro: ltl_G_stabilize)
       
      (* Wait until the formula is provable for all suffixes *)
      hence "\<And>\<psi>. G \<psi> \<in> \<G> \<Longrightarrow> w \<Turnstile> F (G \<psi>)"
        using insert \<open>closed \<G> w\<close> by simp
      then obtain k\<^sub>2 where k2_def: "\<forall>i \<ge> k\<^sub>2. \<exists>j. \<PP> \<psi>' \<G> w i"
        using \<open>\<PP>\<^sub>\<infinity> \<psi>' \<G> w\<close> unfolding almost_all_eventually_provable_def MOST_nat_le by blast
       
      {
        fix i 
        assume "i \<ge> max k\<^sub>1 k\<^sub>2"
        hence "i \<ge> k\<^sub>1" and "i \<ge> k\<^sub>2"
          by simp+
        then obtain j' where "\<G> \<Turnstile>\<^sub>P af\<^sub>G \<psi>' (w [i \<rightarrow> j'])"
          using k2_def by blast
        then obtain j where "\<G> \<Turnstile>\<^sub>P af\<^sub>G \<psi>' (w [i \<rightarrow> i + j])"
          by (cases "i \<le> j'") (blast dest: le_Suc_ex, metis subsequence_empty le_add_diff_inverse nat_le_linear)
        moreover
        have "\<And>\<psi>. G \<psi> \<in> \<G>  \<Longrightarrow> suffix k\<^sub>1 w \<Turnstile> G \<psi>"
          using ltl_G_stabilize_property[OF \<open>finite (\<G> \<union> \<^bold>G \<psi>')\<close> \<open>Only_G (\<G> \<union> \<^bold>G \<psi>')\<close> k1_def]
          using \<open>\<And>\<psi>. G \<psi> \<in> \<G> \<Longrightarrow> w \<Turnstile> F (G \<psi>)\<close> by blast
        hence "\<And>\<psi>. G \<psi> \<in> \<G> \<Longrightarrow> suffix (i + j) w \<Turnstile> G \<psi>"
          by (metis \<open>i \<ge> max k\<^sub>1 k\<^sub>2\<close> LTL_suffix_G suffix_suffix le_Suc_ex max.cobounded1) 
        hence "\<And>\<psi>. \<psi> \<in> \<G> \<Longrightarrow> suffix (i + j) w \<Turnstile> \<psi>"
          using \<open>Only_G \<G>\<close> by fast
        ultimately
        have Suffix: "suffix (i + j) w \<Turnstile> af\<^sub>G \<psi>' (w [i \<rightarrow> i + j])"
          using ltl_models_equiv_prop_entailment by blast 
        
        obtain c where "i = k\<^sub>1 + c"
          using \<open>i \<ge> k\<^sub>1\<close> unfolding le_iff_add by blast
        hence Stable: "\<forall>\<psi> \<in> \<^bold>G \<psi>'. suffix i w \<Turnstile> \<psi> = suffix j (suffix i w) \<Turnstile> \<psi>"
          using k1_def k1_def[of _ "c + j"] unfolding suffix_suffix add.assoc[symmetric] by blast
        from Suffix have "suffix i w \<Turnstile> \<psi>'"
          unfolding suffix_suffix subsequence_shift af\<^sub>G_ltl_continuation_suffix[OF Stable] by simp
      }
      hence "w \<Turnstile> F G \<psi>'"
        unfolding MOST_nat_le LTL_FG_almost_all_suffixes by blast 
      thus ?case
        using insert using \<open>\<And>\<psi>. G \<psi> \<in> \<G> \<Longrightarrow> w \<Turnstile> F G \<psi>\<close> \<open>x = G \<psi>'\<close> by auto
  qed blast
qed

lemma closed_\<G>\<^sub>F\<^sub>G:
  "closed (\<G>\<^sub>F\<^sub>G \<phi> w) w"
proof (induction \<phi>)
  case (LTLGlobal \<phi>)  
    thus ?case 
    proof (cases "w \<Turnstile> F G \<phi>")
      case True
        hence "\<forall>\<^sub>\<infinity>i. suffix i w \<Turnstile> \<phi>"
          using LTL_FG_almost_all_suffixes by blast
        then obtain i where "\<forall>j \<ge> i. suffix j w \<Turnstile> \<phi>"
          unfolding MOST_nat_le by blast
        {
          fix k
          assume "k \<ge> i"
          hence "suffix k w \<Turnstile> \<phi>"
            using \<open>\<forall>j\<ge>i. suffix j w \<Turnstile> \<phi>\<close> by blast
          hence "\<PP> \<phi> {G \<psi> |\<psi>. w \<Turnstile> F G \<psi>} (suffix k w) 0"
            using LTL_FG_suffix 
            by (blast dest: ltl_implies_provable[unfolded \<G>\<^sub>F\<^sub>G_alt_def])
          hence "\<PP> \<phi> {G \<psi> |\<psi>. w \<Turnstile> F G \<psi>} w k"
            unfolding subsequence_shift by auto
        }
        hence "\<PP>\<^sub>\<infinity> \<phi> {G \<psi> | \<psi>. w \<Turnstile> F G \<psi>} w"
          using almost_all_eventually_provable_def[of \<phi> _ w]
          unfolding MOST_nat_le by auto
        hence "\<PP>\<^sub>\<infinity> \<phi> (\<G>\<^sub>F\<^sub>G \<phi> w) w"
          unfolding \<G>\<^sub>F\<^sub>G_alt_def
          using almost_all_eventually_provable_restrict_to_G by blast
        thus ?thesis
          using LTLGlobal insert by auto
    qed auto
qed auto

subsubsection \<open>Conjunction of Eventually Provable Formulas\<close>

definition \<F> 
where 
  "\<F> \<phi> w \<G> j = And (map (\<lambda>i. af\<^sub>G \<phi> (w [i \<rightarrow> j])) [the (threshold \<phi> w \<G>) ..< Suc j])"

lemma almost_all_suffixes_model_\<F>:
  assumes "closed \<G> w"
  assumes "G \<phi> \<in> \<G>"
  shows "\<forall>\<^sub>\<infinity>j. suffix j w \<Turnstile> eval\<^sub>G \<G> (\<F> \<phi> w \<G> j)"
proof -
  have "Only_G \<G>"
    using assms(1) by simp
  hence "\<G> \<subseteq> {\<chi>. w \<Turnstile> F \<chi>}" and "\<PP>\<^sub>\<infinity> \<phi> \<G> w"
    using closed_FG[OF assms(1)] assms by auto
  then obtain k where "threshold \<phi> w \<G> = Some k"
    by (simp add: almost_all_eventually_provable_def)
  hence k_def: "k = the (threshold \<phi> w \<G>)"
    by simp
  moreover
  have "finite (\<^bold>G \<phi> \<union> \<G>)" and "Only_G (\<^bold>G \<phi> \<union> \<G>)"
    using assms(1) G_nested_finite unfolding G_nested_propos_alt_def by auto
  then obtain l where S: "\<And>j \<psi>. \<psi> \<in> \<^bold>G \<phi> \<union> \<G> \<Longrightarrow> suffix l w \<Turnstile> \<psi> = suffix (l + j) w \<Turnstile> \<psi>"
    using ltl_G_stabilize by metis
  hence \<G>_sat:"\<And>j \<psi>. G \<psi> \<in> \<G> \<Longrightarrow> suffix (l + j) w \<Turnstile> G \<psi>"
    using ltl_G_stabilize_property \<open>\<G> \<subseteq> {\<chi>. w \<Turnstile> F \<chi>}\<close> by blast
  {
    fix j
    assume "l \<le> j"
    {
      fix i 
      assume "k \<le> i" "i \<le> j"
      then obtain j' where "j = i + j'" 
        by (blast dest: le_Suc_ex)
      hence "\<exists>j \<ge> i. \<G> \<Turnstile>\<^sub>P af\<^sub>G \<phi> (w [i \<rightarrow> j])"
        using \<open>\<PP>\<^sub>\<infinity> \<phi> \<G> w\<close> unfolding almost_all_eventually_provable_def MOST_nat_le
        by (metis \<open>k \<le> i\<close> \<open>threshold \<phi> w \<G> = Some k\<close> threshold_properties(2) linear subsequence_empty)  
      then obtain j'' where "\<G> \<Turnstile>\<^sub>P af\<^sub>G \<phi> (w [i \<rightarrow> j''])" and "i \<le> j''"
        by (blast )
      have "suffix j w \<Turnstile> eval\<^sub>G \<G> (af\<^sub>G \<phi> (w [i \<rightarrow> j]))"
      proof (cases "j'' \<le> j")
        case True
          hence "\<G> \<Turnstile>\<^sub>P af\<^sub>G \<phi> (w [i \<rightarrow> j])"
            using af\<^sub>G_sat_core_generalized[OF \<open>Only_G \<G>\<close>, of _ j' \<phi> "suffix i w"] le_Suc_ex[OF \<open>i \<le> j''\<close>] le_Suc_ex[OF \<open>j'' \<le> j\<close>]  
            by (metis add.right_neutral subsequence_shift \<open>j = i + j'\<close> \<open>\<G> \<Turnstile>\<^sub>P af\<^sub>G \<phi> (w [i \<rightarrow> j''])\<close> nat_add_left_cancel_le ) 
          hence "\<G> \<Turnstile>\<^sub>P eval\<^sub>G \<G> (af\<^sub>G \<phi> (w [i \<rightarrow> j]))"
            unfolding eval\<^sub>G_prop_entailment .
          moreover
          have "\<G> \<subseteq> {\<chi>. suffix j w \<Turnstile> \<chi>}"
            using \<G>_sat \<open>l \<le> j\<close> \<open>Only_G \<G>\<close> by (fast dest: le_Suc_ex)
          ultimately
          have "{\<chi>. suffix j w \<Turnstile> \<chi>} \<Turnstile>\<^sub>P eval\<^sub>G \<G> (af\<^sub>G \<phi> (w [i \<rightarrow> j]))"
            by blast
          thus ?thesis
            unfolding ltl_models_equiv_prop_entailment[symmetric] by simp
      next
        case False
          hence "\<G> \<Turnstile>\<^sub>P eval\<^sub>G \<G> (af\<^sub>G (af\<^sub>G \<phi> (w [i \<rightarrow> j])) (w [j \<rightarrow> j'']))"
            unfolding foldl_append[symmetric] eval\<^sub>G_prop_entailment
            by (metis le_iff_add \<open>i \<le> j\<close> map_append upt_add_eq_append nat_le_linear subsequence_def \<open>\<G> \<Turnstile>\<^sub>P af\<^sub>G \<phi> (w [i \<rightarrow> j''])\<close>) 
          hence "\<G> \<Turnstile>\<^sub>P af\<^sub>G (eval\<^sub>G \<G> (af\<^sub>G \<phi> (w [i \<rightarrow> j]))) (w [j \<rightarrow> j''])" (is "\<G> \<Turnstile>\<^sub>P ?af\<^sub>G")
            using af\<^sub>G_eval\<^sub>G[OF \<open>Only_G \<G>\<close>] by blast
          moreover
          have "l \<le> j''"
            using False \<open>l \<le> j\<close> by linarith
          hence "\<G> \<subseteq> {\<chi>. suffix j'' w \<Turnstile> \<chi>}"
            using \<G>_sat \<open>Only_G \<G>\<close> by (fast dest: le_Suc_ex)
          ultimately
          have "suffix j'' w \<Turnstile> ?af\<^sub>G"
            using ltl_models_equiv_prop_entailment[symmetric] by blast
          moreover
          {
            have "\<And>\<psi>. \<psi> \<in> \<^bold>G \<phi> \<union> \<G> \<Longrightarrow> suffix j w \<Turnstile> \<psi> = suffix j'' w \<Turnstile> \<psi>"
              using S \<open>l \<le> j\<close> \<open>l \<le> j''\<close> by (metis le_add_diff_inverse)
            moreover
            have "\<^bold>G (eval\<^sub>G \<G> (af\<^sub>G \<phi> (w [i \<rightarrow> j]))) \<subseteq> \<^bold>G \<phi>" (is "?G \<subseteq> _")
              using eval\<^sub>G_G_nested by force
            ultimately
            have "\<And>\<psi>. \<psi> \<in> ?G \<Longrightarrow> suffix j w \<Turnstile> \<psi> = suffix j'' w \<Turnstile> \<psi>"
              by auto
          }
          ultimately
          show ?thesis
            using af\<^sub>G_ltl_continuation_suffix[of "eval\<^sub>G \<G> (af\<^sub>G \<phi> (w [i \<rightarrow> j]))" "suffix j w", unfolded suffix_suffix]
            by (metis False le_Suc_ex nat_le_linear add_diff_cancel_left' subsequence_prefix_suffix)
      qed   
    }
    hence "suffix j w \<Turnstile> And (map (\<lambda>i. eval\<^sub>G \<G> (af\<^sub>G \<phi> (w [i \<rightarrow> j]))) [k..<Suc j])"
      unfolding And_semantics set_map set_upt image_def by force 
    hence "suffix j w \<Turnstile> eval\<^sub>G \<G> (And (map (\<lambda>i. af\<^sub>G \<phi> (w [i \<rightarrow> j])) [k..<Suc j]))"
      unfolding eval\<^sub>G_And_map map_map comp_def .
  }
  thus ?thesis 
    unfolding \<F>_def And_semantics MOST_nat_le k_def[symmetric] by meson
qed

lemma almost_all_commutative'':
  assumes "finite S"
  assumes "Only_G S"
  assumes "\<And>x. G x \<in> S \<Longrightarrow> \<forall>\<^sub>\<infinity>i. P x (i::nat)"
  shows "\<forall>\<^sub>\<infinity>i. \<forall>x. G x \<in> S \<longrightarrow> P x i"
proof -
  from assms have "(\<And>x. x \<in> S \<Longrightarrow> \<forall>\<^sub>\<infinity>i. P (theG x) (i::nat))"
    by fastforce
  with assms(1) have "\<forall>\<^sub>\<infinity>i. \<forall>x \<in> S. P (theG x) i"
    using almost_all_commutative' by force
  thus ?thesis
    using assms(2) unfolding MOST_nat_le by force
qed

lemma almost_all_suffixes_model_\<F>_generalized:
  assumes "closed \<G> w"
  shows "\<forall>\<^sub>\<infinity>j. \<forall>\<psi>. G \<psi> \<in> \<G> \<longrightarrow> suffix j w \<Turnstile> eval\<^sub>G \<G> (\<F> \<psi> w \<G> j)"
  using almost_all_suffixes_model_\<F>[OF assms] almost_all_commutative''[of \<G>] assms by fast

subsection \<open>Technical Lemmas\<close>

lemma threshold_suffix_2:
  assumes "threshold \<psi> w \<G>' = Some k"
  assumes "k \<le> l"
  shows "threshold \<psi> (suffix l w) \<G>' = Some 0"
proof -
  have "\<PP>\<^sub>\<infinity> \<psi> \<G>' w"
    using \<open>threshold \<psi> w \<G>' = Some k\<close>  option.distinct(1)
    unfolding threshold.simps index.simps almost_all_eventually_provable_def by metis
  hence "\<PP>\<^sub>\<infinity> \<psi> \<G>' (suffix l w)"
    using almost_all_eventually_provable_suffix by blast
  moreover
  have "\<forall>i \<ge> k. \<exists>j. \<G>' \<Turnstile>\<^sub>P af\<^sub>G \<psi> (w [i \<rightarrow> j])" 
    using threshold_properties(2)[OF assms(1)] by blast
  hence "\<forall>m. \<exists>j. \<G>' \<Turnstile>\<^sub>P af\<^sub>G \<psi> ((suffix l w) [m \<rightarrow> j])"
    unfolding subsequence_shift using \<open>k \<le> l\<close> \<open>\<forall>i \<ge> k. \<exists>j. \<G>' \<Turnstile>\<^sub>P af\<^sub>G \<psi> (w [i \<rightarrow> j])\<close> 
    by (metis (mono_tags, hide_lams) leI less_imp_add_positive order_refl subsequence_empty trans_le_add1)
  ultimately
  show ?thesis
    by simp
qed

lemma threshold_closed:
  assumes "closed \<G> w"
  shows "\<exists>k. \<forall>\<psi>. G \<psi> \<in> \<G> \<longrightarrow> threshold \<psi> (suffix k w) \<G> = Some 0"
proof -
  define k where "k = Max {the (threshold \<psi> w \<G>) | \<psi>. G \<psi> \<in> \<G>}" (is "_ = Max ?S")

  have "finite \<G>" and "Only_G \<G>" and "\<And>\<psi>. G \<psi> \<in> \<G> \<Longrightarrow> \<PP>\<^sub>\<infinity> \<psi> \<G> w"
    using assms by blast+
  hence "\<And>\<psi>. G \<psi> \<in> \<G> \<Longrightarrow> \<exists>k. threshold \<psi> w \<G> = Some k"
    unfolding almost_all_eventually_provable_def by simp
  moreover
  have "?S = (\<lambda>x. the (threshold (theG x) w \<G>)) ` \<G>"
    unfolding image_def using \<open>Only_G \<G>\<close> ltl.sel(8) by metis 
  hence "finite ?S"
    using \<open>finite \<G>\<close> finite_imageI by simp
  hence "\<And>\<psi> k'. G \<psi> \<in> \<G> \<Longrightarrow> threshold \<psi> w \<G> = Some k' \<Longrightarrow> k' \<le> k"
    by (metis (mono_tags, lifting) CollectI Max_ge k_def option.sel)  
  ultimately
  have "\<And>\<psi>. G \<psi> \<in> \<G> \<Longrightarrow> threshold \<psi> (suffix k w) \<G> = Some 0"
    using threshold_suffix[of _ w \<G> _ k 0] threshold_suffix_2 by blast
  thus ?thesis
    by blast
qed

lemma \<F>_drop:
  assumes "\<PP>\<^sub>\<infinity> \<phi> \<G>' w"
  assumes "S \<Turnstile>\<^sub>P \<F> \<phi> w \<G>' (i + j)"
  shows "S \<Turnstile>\<^sub>P \<F> \<phi> (suffix i w) \<G>' j"
proof - 
  obtain k k' where k_def: "threshold \<phi> w \<G>' = Some k" and k'_def: "threshold \<phi> (suffix i w) \<G>' = Some k'"
    using assms almost_all_eventually_provable_suffix 
    unfolding threshold.simps index.simps almost_all_eventually_provable_def by fastforce
  hence k_def_2: "the (threshold \<phi> w \<G>') = k" and k'_def_2: "the (threshold \<phi> (suffix i w) \<G>') = k'"
    by simp+
  moreover
  hence "k \<le> i + j \<Longrightarrow> S \<Turnstile>\<^sub>P \<phi>"
    using \<open>S \<Turnstile>\<^sub>P \<F> \<phi> w \<G>' (i + j)\<close> unfolding \<F>_def And_semantics And_prop_entailment by (simp add: subsequence_def)
  moreover
  have "k' \<le> j \<Longrightarrow> k \<le> i + j"
    using k_def k'_def threshold_suffix by fastforce 
  ultimately
  have "the (threshold \<phi> (suffix i w) \<G>') \<le> j \<Longrightarrow> S \<Turnstile>\<^sub>P \<phi>"
    by blast
  moreover
  {
    fix pos
    assume "k' \<le> pos" and "pos \<le> j"
    have "k \<le> i + pos"
      by (metis threshold_suffix k_def k'_def \<open>k' \<le> pos\<close> add.commute add_le_cancel_right order.trans) 
    hence "(i + pos) \<in> set [k..<Suc (i + j)]"
      using \<open>pos \<le> j\<close> by auto
    hence "af\<^sub>G \<phi> ((suffix i w) [pos \<rightarrow> j]) \<in> set (map (\<lambda>ia. af\<^sub>G \<phi> (subsequence w ia (i + j))) [k..<Suc (i + j)])"
      unfolding subsequence_shift set_map by blast
    hence "S \<Turnstile>\<^sub>P af\<^sub>G \<phi> ((suffix i w) [pos \<rightarrow> j])"  
      using assms(2) unfolding \<F>_def And_prop_entailment k_def_2 by (cases "k \<le> i + j") auto
  }
  ultimately
  show ?thesis
     unfolding \<F>_def And_prop_entailment k'_def_2 by auto
qed

subsection \<open>Main Results\<close>

definition accept\<^sub>M
where
  "accept\<^sub>M \<phi> \<G> w \<equiv> (\<forall>\<^sub>\<infinity>j. \<forall>S. (\<forall>\<psi>. G \<psi> \<in> \<G> \<longrightarrow> S \<Turnstile>\<^sub>P G \<psi> \<and> S \<Turnstile>\<^sub>P eval\<^sub>G \<G> (\<F> \<psi> w \<G> j)) \<longrightarrow> S \<Turnstile>\<^sub>P af \<phi> (w [0 \<rightarrow> j]))"

lemma lemmaD:
  assumes "w \<Turnstile> \<phi>"
  assumes "\<And>\<psi>. G \<psi> \<in> \<G>\<^sub>F\<^sub>G \<phi> w \<Longrightarrow> threshold \<psi> w (\<G>\<^sub>F\<^sub>G \<phi> w) = Some 0"
  shows "accept\<^sub>M \<phi> (\<G>\<^sub>F\<^sub>G \<phi> w) w"
proof -
  obtain i where "\<G>\<^sub>F\<^sub>G \<phi> w \<Turnstile>\<^sub>P af\<^sub>G \<phi> (w [0 \<rightarrow> i])"
    using ltl_implies_provable[OF \<open>w \<Turnstile> \<phi>\<close>] by metis
  {
    fix S j
    assume assm1: "j \<ge> i"
    assume assm2: "\<And>\<psi>. G \<psi> \<in> \<G>\<^sub>F\<^sub>G \<phi> w \<Longrightarrow> S \<Turnstile>\<^sub>P G \<psi> \<and> S \<Turnstile>\<^sub>P eval\<^sub>G (\<G>\<^sub>F\<^sub>G \<phi> w) (\<F> \<psi> w (\<G>\<^sub>F\<^sub>G \<phi> w) j)"
    moreover
    {
      have "\<G>\<^sub>F\<^sub>G \<phi> w \<Turnstile>\<^sub>P af\<^sub>G \<phi> (w [0 \<rightarrow> j])"
        using \<open>\<G>\<^sub>F\<^sub>G \<phi> w \<Turnstile>\<^sub>P af\<^sub>G \<phi> (w [0 \<rightarrow> i])\<close> \<open>j \<ge> i\<close> 
        by (metis af\<^sub>G_sat_core_generalized \<G>\<^sub>F\<^sub>G_Only_G) 
      moreover
      have "\<G>\<^sub>F\<^sub>G \<phi> w \<subseteq> S"
        using assm2 unfolding \<G>\<^sub>F\<^sub>G_alt_def by auto
      ultimately
      have "S \<Turnstile>\<^sub>P eval\<^sub>G (\<G>\<^sub>F\<^sub>G \<phi> w) (af\<^sub>G \<phi> (w [0 \<rightarrow> j]))"
        using eval\<^sub>G_prop_entailment by blast
    }
    moreover
    {
      fix \<psi> assume "G \<psi> \<in> \<G>\<^sub>F\<^sub>G \<phi> w"
      hence "the (threshold \<psi> w (\<G>\<^sub>F\<^sub>G \<phi> w)) = 0" and "S \<Turnstile>\<^sub>P eval\<^sub>G (\<G>\<^sub>F\<^sub>G \<phi> w) (\<F> \<psi> w (\<G>\<^sub>F\<^sub>G \<phi> w) j)"
        using assms assm2 option.sel by metis+
      hence "\<And>i. i \<le> j \<Longrightarrow> S \<Turnstile>\<^sub>P eval\<^sub>G (\<G>\<^sub>F\<^sub>G \<phi> w) (af\<^sub>G \<psi> (w[i \<rightarrow> j]))" 
        unfolding \<F>_def And_prop_entailment eval\<^sub>G_And_map by auto
    }
    ultimately
    have "S \<Turnstile>\<^sub>P af \<phi> (w [0 \<rightarrow> j])"
      using af\<^sub>G_implies_af_eval\<^sub>G[of _ _ \<phi>] by presburger
  }
  thus ?thesis
     unfolding accept\<^sub>M_def MOST_nat_le by meson 
qed

theorem ltl_FG_logical_characterization:
  "w \<Turnstile> F G \<phi> \<longleftrightarrow> (\<exists>\<G> \<subseteq> \<^bold>G (F G \<phi>). G \<phi> \<in> \<G> \<and> closed \<G> w)"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?lhs
  hence "G \<phi> \<in> \<G>\<^sub>F\<^sub>G (F G \<phi>) w" and "\<G>\<^sub>F\<^sub>G (F G \<phi>) w \<subseteq> \<^bold>G (F G \<phi>)"
    unfolding \<G>\<^sub>F\<^sub>G_alt_def by auto
  thus ?rhs
    using closed_\<G>\<^sub>F\<^sub>G by metis
qed (blast intro: closed_FG)

theorem ltl_logical_characterization:
  "w \<Turnstile> \<phi> \<longleftrightarrow> (\<exists>\<G> \<subseteq> \<^bold>G \<phi>. accept\<^sub>M \<phi> \<G> w \<and> closed \<G> w)"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof 
  assume ?lhs

  obtain k where k_def: "\<And>\<psi>. G \<psi> \<in> \<G>\<^sub>F\<^sub>G \<phi> w \<Longrightarrow> threshold \<psi> (suffix k w) (\<G>\<^sub>F\<^sub>G \<phi> w) = Some 0"
    using threshold_closed[OF closed_\<G>\<^sub>F\<^sub>G] by blast

  (* Define new constants *)
  define w' where "w' = suffix k w"
  define \<phi>' where "\<phi>' = af \<phi> (w[0 \<rightarrow> k])"

  (* Facts about w' and \<phi>' *)
  from \<open>?lhs\<close> have "w' \<Turnstile> \<phi>'"
    unfolding af_ltl_continuation_suffix[of w \<phi> k] w'_def \<phi>'_def .   
  have G_eq: "\<^bold>G \<phi>' = \<^bold>G \<phi>"
    unfolding \<phi>'_def G_af_simp ..
  have \<G>_eq: "\<G>\<^sub>F\<^sub>G \<phi>' w' = \<G>\<^sub>F\<^sub>G \<phi> w"
    unfolding \<G>\<^sub>F\<^sub>G_alt_def w'_def \<phi>'_def G_af_simp LTL_FG_suffix ..
  have \<phi>'_eq: "\<And>j. af \<phi>' (w' [0 \<rightarrow>j]) = af \<phi> (w [0 \<rightarrow> k + j])"
    unfolding \<phi>'_def w'_def foldl_append[symmetric] subsequence_shift
    unfolding Nat.add_0_right by (metis subsequence_append) 

  (* Apply helper lemma *)
  have "accept\<^sub>M \<phi>' (\<G>\<^sub>F\<^sub>G \<phi>' w') w'"
    using lemmaD[OF \<open>w' \<Turnstile> \<phi>'\<close>] k_def 
    unfolding \<G>_eq w'_def[symmetric] by blast

  then obtain j' where j'_def: "\<And>j S. j \<ge> j' \<Longrightarrow> 
    (\<forall>\<psi>. G \<psi> \<in> \<G>\<^sub>F\<^sub>G \<phi>' w' \<longrightarrow> S \<Turnstile>\<^sub>P G \<psi> \<and> S \<Turnstile>\<^sub>P eval\<^sub>G (\<G>\<^sub>F\<^sub>G \<phi>' w') (\<F> \<psi> w' (\<G>\<^sub>F\<^sub>G \<phi>' w') j)) \<Longrightarrow> S \<Turnstile>\<^sub>P af \<phi>' (w' [0 \<rightarrow> j])"
    unfolding accept\<^sub>M_def MOST_nat_le by blast

 
  (* Change formula, s.t. it matches ?lhs *)
  {
    fix j S
    let ?af = "af \<phi> (w[0 \<rightarrow> k + j' + j])"
    assume "(\<forall>\<psi>. G \<psi> \<in> (\<G>\<^sub>F\<^sub>G \<phi>' w') \<longrightarrow> S \<Turnstile>\<^sub>P G \<psi> \<and> S \<Turnstile>\<^sub>P eval\<^sub>G (\<G>\<^sub>F\<^sub>G \<phi>' w') (\<F> \<psi> w (\<G>\<^sub>F\<^sub>G \<phi>' w') (k + j' + j)))"
    moreover
    {
      fix \<psi>
      assume "G \<psi> \<in> \<G>\<^sub>F\<^sub>G \<phi>' w'" (is "_ \<in> ?\<G>")
      hence "\<PP>\<^sub>\<infinity> \<psi> ?\<G> w"
        unfolding \<G>_eq using closed_\<G>\<^sub>F\<^sub>G by blast
      have "\<And>S. S \<Turnstile>\<^sub>P eval\<^sub>G ?\<G> (\<F> \<psi> w ?\<G> (k + j' + j)) \<Longrightarrow> S \<Turnstile>\<^sub>P eval\<^sub>G ?\<G> (\<F> \<psi> w' ?\<G> (j' + j))"
        using \<F>_drop[OF \<open>\<PP>\<^sub>\<infinity> \<psi> (\<G>\<^sub>F\<^sub>G \<phi>' w') w\<close>, of _ k "j' + j"] eval\<^sub>G_respectfulness(1)[unfolded ltl_prop_implies_def] 
        unfolding add.assoc w'_def by metis
      moreover 
      assume "S \<Turnstile>\<^sub>P eval\<^sub>G ?\<G> (\<F> \<psi> w ?\<G> (k + j' + j))"
      ultimately
      have "S \<Turnstile>\<^sub>P eval\<^sub>G ?\<G> (\<F> \<psi> w' ?\<G> (j' + j))"
         by simp
    }
    ultimately
    have "S \<Turnstile>\<^sub>P ?af"
      using j'_def unfolding \<phi>'_eq add.assoc by simp
  }
  hence "accept\<^sub>M \<phi> (\<G>\<^sub>F\<^sub>G \<phi> w) w"
    unfolding accept\<^sub>M_def MOST_nat_le \<G>_eq by (metis le_Suc_ex) 
  moreover
  have "\<G>\<^sub>F\<^sub>G \<phi> w \<subseteq> \<^bold>G \<phi>"
    unfolding \<G>\<^sub>F\<^sub>G_alt_def by auto
  ultimately
  show ?rhs
    by (metis closed_\<G>\<^sub>F\<^sub>G)
next
  assume ?rhs

  then obtain \<G> where \<G>_prop: "\<G> \<subseteq> \<^bold>G \<phi>" "finite \<G>" "Only_G \<G>" "accept\<^sub>M \<phi> \<G> w" "closed \<G> w"
    using \<G>_elements \<G>_finite by blast
  then obtain i where "\<And>\<chi> j. \<chi> \<in> \<G> \<Longrightarrow> suffix i w \<Turnstile> \<chi> = suffix (i + j) w \<Turnstile> \<chi>"
    using ltl_G_stabilize by blast
  hence i_def: "\<And>\<psi>. G \<psi> \<in> \<G> \<Longrightarrow> suffix i w \<Turnstile> G \<psi>"
    using ltl_G_stabilize_property[OF \<open>finite \<G>\<close> \<open>Only_G \<G>\<close>] \<G>_prop closed_FG[of \<G>] by blast
  obtain j where j_def: "\<And>j' S. j' \<ge> j \<Longrightarrow> 
    (\<forall>\<psi>. G \<psi> \<in> \<G> \<longrightarrow> S \<Turnstile>\<^sub>P G \<psi> \<and> S \<Turnstile>\<^sub>P eval\<^sub>G \<G> (\<F> \<psi> w \<G> j')) \<longrightarrow> S \<Turnstile>\<^sub>P af \<phi> (w [0 \<rightarrow> j'])"
    using \<open>accept\<^sub>M \<phi> \<G> w\<close> unfolding accept\<^sub>M_def MOST_nat_le by presburger
  obtain j' where lemma19: "\<And>j \<psi>. j \<ge> j' \<Longrightarrow> G \<psi> \<in> \<G> \<Longrightarrow> suffix j w \<Turnstile> eval\<^sub>G \<G> (\<F> \<psi> w \<G> j)"
    using almost_all_suffixes_model_\<F>_generalized[OF \<open>closed \<G> w\<close>] unfolding MOST_nat_le by blast
  
  (* Define new constants *)
  define k where "k = max (max i j) j'"
  define w' where "w' = suffix k w"
  define \<phi>' where "\<phi>' = af \<phi> (w[0 \<rightarrow> k])"
  define S where "S = {\<chi>. w' \<Turnstile> \<chi>}"

  have "(\<And>\<psi>. G \<psi> \<in> \<G> \<Longrightarrow> S \<Turnstile>\<^sub>P G \<psi> \<and> S \<Turnstile>\<^sub>P eval\<^sub>G \<G> (\<F> \<psi> w \<G> k)) \<Longrightarrow> S \<Turnstile>\<^sub>P \<phi>'"
    using j_def[of k S] unfolding \<phi>'_def k_def by fastforce
  moreover
  {
    fix \<psi>
    assume "G \<psi> \<in> \<G>"
    have "\<And>j. i \<le> j \<Longrightarrow> suffix i w \<Turnstile> G \<psi> \<Longrightarrow> suffix j w \<Turnstile> G \<psi>"
      by (metis LTL_suffix_G le_Suc_ex suffix_suffix)
    hence "w' \<Turnstile> G \<psi>"
      unfolding w'_def k_def max_def 
      using i_def[OF \<open>G \<psi> \<in> \<G>\<close>] by simp
    moreover
    have "w' \<Turnstile> eval\<^sub>G \<G> (\<F> \<psi> w \<G> k)"
      using lemma19[OF _ \<open>G \<psi> \<in> \<G>\<close>, of k]
      unfolding w'_def k_def by fastforce
    ultimately
    have "S \<Turnstile>\<^sub>P G \<psi>" and "S \<Turnstile>\<^sub>P eval\<^sub>G \<G> (\<F> \<psi> w \<G> k)" 
      unfolding S_def ltl_models_equiv_prop_entailment[symmetric] by blast+
  }
  ultimately
  have "S \<Turnstile>\<^sub>P \<phi>'"
    by simp
  hence "w' \<Turnstile> \<phi>'"
    using S_def ltl_models_equiv_prop_entailment by blast
  thus ?lhs
    using w'_def \<phi>'_def af_ltl_continuation_suffix by blast
qed

end
