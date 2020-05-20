(*  
    Author:      Salomon Sickert
    License:     BSD
*)

section \<open>af - Unfolding Functions\<close>

theory af
  imports Main LTL_FGXU "Auxiliary/List2"
begin

subsection \<open>af\<close>

fun af_letter :: "'a ltl \<Rightarrow> 'a set \<Rightarrow> 'a ltl"
where
  "af_letter true \<nu> = true"
| "af_letter false \<nu> = false"
| "af_letter p(a) \<nu> = (if a \<in> \<nu> then true else false)"
| "af_letter (np(a)) \<nu>  = (if a \<notin> \<nu> then true else false)"
| "af_letter (\<phi> and \<psi>) \<nu> = (af_letter \<phi> \<nu>) and (af_letter \<psi> \<nu>)"
| "af_letter (\<phi> or \<psi>) \<nu> = (af_letter \<phi> \<nu>) or (af_letter \<psi> \<nu>)"
| "af_letter (X \<phi>) \<nu> = \<phi>"
| "af_letter (G \<phi>) \<nu> = (G \<phi>) and (af_letter \<phi> \<nu>)"
| "af_letter (F \<phi>) \<nu> = (F \<phi>) or (af_letter \<phi> \<nu>)"
| "af_letter (\<phi> U \<psi>) \<nu> = (\<phi> U \<psi> and (af_letter \<phi> \<nu>)) or (af_letter \<psi> \<nu>)"

abbreviation af :: "'a ltl \<Rightarrow> 'a set list \<Rightarrow> 'a ltl" ("af")
where
  "af \<phi> w \<equiv> foldl af_letter \<phi> w"

lemma af_decompose:
  "af (\<phi> and \<psi>) w = (af \<phi> w) and (af \<psi> w)"
  "af (\<phi> or \<psi>) w = (af \<phi> w) or (af \<psi> w)"
  by (induction w rule: rev_induct) simp_all

lemma af_simps[simp]:
  "af true w = true"
  "af false w = false"
  "af (X \<phi>) (x#xs) = af \<phi> (xs)"
  by (induction w) simp_all

lemma af_F:
  "af (F \<phi>) w = Or (F \<phi> # map (af \<phi>) (suffixes w))"
proof (induction w)
  case (Cons x xs)
    have "af (F \<phi>) (x # xs) = af (af_letter (F \<phi>) x) xs"
      by simp
    also
    have "\<dots> = (af (F \<phi>) xs) or (af (af_letter (\<phi>) x) xs)"
      unfolding af_decompose[symmetric] by simp
    finally
    show ?case using Cons Or_append_syntactic by force
qed simp

lemma af_G:
  "af (G \<phi>) w = And (G \<phi> # map (af \<phi>) (suffixes w))"
proof (induction w)
  case (Cons x xs)
    have "af (G \<phi>) (x # xs) = af (af_letter (G \<phi>) x) xs"
      by simp
    also
    have "\<dots> = (af (G \<phi>) xs) and (af (af_letter (\<phi>) x) xs)"
      unfolding af_decompose[symmetric] by simp
    finally
    show ?case using Cons Or_append_syntactic by force
qed simp

lemma af_U:
  "af (\<phi> U \<psi>) (x#xs) = (af (\<phi> U \<psi>) xs and af \<phi> (x#xs)) or af \<psi> (x#xs)"
  by (induction xs) (simp add: af_decompose)+

lemma af_respectfulness:
  "\<phi> \<longrightarrow>\<^sub>P \<psi> \<Longrightarrow> af_letter \<phi> \<nu> \<longrightarrow>\<^sub>P af_letter \<psi> \<nu>"
  "\<phi> \<equiv>\<^sub>P \<psi> \<Longrightarrow> af_letter \<phi> \<nu> \<equiv>\<^sub>P af_letter \<psi> \<nu>"
proof -
  { 
    fix \<phi> 
    have "af_letter \<phi> \<nu> = subst \<phi> (\<lambda>\<chi>. Some (af_letter \<chi> \<nu>))" 
      by (induction \<phi>) auto 
  }
  thus "\<phi> \<longrightarrow>\<^sub>P \<psi> \<Longrightarrow> af_letter \<phi> \<nu> \<longrightarrow>\<^sub>P af_letter \<psi> \<nu>"
    and "\<phi> \<equiv>\<^sub>P \<psi> \<Longrightarrow> af_letter \<phi> \<nu> \<equiv>\<^sub>P af_letter \<psi> \<nu>"
    using subst_respects_ltl_prop_entailment by metis+
qed

lemma af_respectfulness':
  "\<phi> \<longrightarrow>\<^sub>P \<psi> \<Longrightarrow> af \<phi> w \<longrightarrow>\<^sub>P af \<psi> w"
  "\<phi> \<equiv>\<^sub>P \<psi> \<Longrightarrow> af \<phi> w \<equiv>\<^sub>P af \<psi> w"
  by (induction w arbitrary: \<phi> \<psi>) (insert af_respectfulness, fastforce+)

lemma af_nested_propos:
  "nested_propos (af_letter \<phi> \<nu>) \<subseteq> nested_propos \<phi>"
  by (induction \<phi>) auto

subsection \<open>@{term af\<^sub>G}\<close>

fun af_G_letter :: "'a ltl \<Rightarrow> 'a set \<Rightarrow> 'a ltl"
where
  "af_G_letter true \<nu> = true"
| "af_G_letter false \<nu> = false"
| "af_G_letter p(a) \<nu> = (if a \<in> \<nu> then true else false)"
| "af_G_letter (np(a)) \<nu>  = (if a \<notin> \<nu> then true else false)"
| "af_G_letter (\<phi> and \<psi>) \<nu> = (af_G_letter \<phi> \<nu>) and (af_G_letter \<psi> \<nu>)"
| "af_G_letter (\<phi> or \<psi>) \<nu> = (af_G_letter \<phi> \<nu>) or (af_G_letter \<psi> \<nu>)"
| "af_G_letter (X \<phi>) \<nu> = \<phi>"
| "af_G_letter (G \<phi>) \<nu> = (G \<phi>)"
| "af_G_letter (F \<phi>) \<nu> = (F \<phi>) or (af_G_letter \<phi> \<nu>)"
| "af_G_letter (\<phi> U \<psi>) \<nu> = (\<phi> U \<psi> and (af_G_letter \<phi> \<nu>)) or (af_G_letter \<psi> \<nu>)"

abbreviation af\<^sub>G :: "'a ltl \<Rightarrow> 'a set list \<Rightarrow> 'a ltl"
where
  "af\<^sub>G \<phi> w \<equiv> (foldl af_G_letter \<phi> w)"

lemma af\<^sub>G_decompose:
  "af\<^sub>G (\<phi> and \<psi>) w = (af\<^sub>G \<phi> w) and (af\<^sub>G \<psi> w)"
  "af\<^sub>G (\<phi> or \<psi>) w = (af\<^sub>G \<phi> w) or (af\<^sub>G \<psi> w)"
  by (induction w rule: rev_induct) simp_all

lemma af\<^sub>G_simps[simp]:
  "af\<^sub>G true w = true"
  "af\<^sub>G false w = false"
  "af\<^sub>G (G \<phi>) w = G \<phi>"
  "af\<^sub>G (X \<phi>) (x#xs) = af\<^sub>G \<phi> (xs)"
  by (induction w) simp_all

lemma af\<^sub>G_F:
  "af\<^sub>G (F \<phi>) w = Or (F \<phi> # map (af\<^sub>G \<phi>) (suffixes w))"
proof (induction w)
  case (Cons x xs)
    have "af\<^sub>G (F \<phi>) (x # xs) = af\<^sub>G (af_G_letter (F \<phi>) x) xs"
      by simp
    also
    have "\<dots> = (af\<^sub>G (F \<phi>) xs) or (af\<^sub>G (af_G_letter (\<phi>) x) xs)"
      unfolding af\<^sub>G_decompose[symmetric] by simp
    finally
    show ?case using Cons Or_append_syntactic by force
qed simp

lemma af\<^sub>G_U:
  "af\<^sub>G (\<phi> U \<psi>) (x#xs) = (af\<^sub>G (\<phi> U \<psi>) xs and af\<^sub>G \<phi> (x#xs)) or af\<^sub>G \<psi> (x#xs)"
  by (simp add: af\<^sub>G_decompose)

lemma af\<^sub>G_subsequence_U:
  "af\<^sub>G (\<phi> U \<psi>) (w [0 \<rightarrow> Suc n]) = (af\<^sub>G (\<phi> U \<psi>) (w [1 \<rightarrow> Suc n]) and af\<^sub>G \<phi> (w [0 \<rightarrow> Suc n])) or af\<^sub>G \<psi> (w [0 \<rightarrow> Suc n])"
proof -
  have "\<And>n. w [0 \<rightarrow> Suc n] = w 0 # w [1 \<rightarrow> Suc n]"
    using subsequence_append[of w 1] by (simp add: subsequence_def upt_conv_Cons) 
  thus ?thesis
    using af\<^sub>G_U by metis
qed

lemma af_G_respectfulness:
  "\<phi> \<longrightarrow>\<^sub>P \<psi> \<Longrightarrow> af_G_letter \<phi> \<nu> \<longrightarrow>\<^sub>P af_G_letter \<psi> \<nu>"
  "\<phi> \<equiv>\<^sub>P \<psi> \<Longrightarrow> af_G_letter \<phi> \<nu> \<equiv>\<^sub>P af_G_letter \<psi> \<nu>"
proof -
  { 
    fix \<phi> 
    have "af_G_letter \<phi> \<nu> = subst \<phi> (\<lambda>\<chi>. Some (af_G_letter \<chi> \<nu>))" 
      by (induction \<phi>) auto 
  }
  thus "\<phi> \<longrightarrow>\<^sub>P \<psi> \<Longrightarrow> af_G_letter \<phi> \<nu> \<longrightarrow>\<^sub>P af_G_letter \<psi> \<nu>"
    and "\<phi> \<equiv>\<^sub>P \<psi> \<Longrightarrow> af_G_letter \<phi> \<nu> \<equiv>\<^sub>P af_G_letter \<psi> \<nu>"
    using subst_respects_ltl_prop_entailment by metis+
qed

lemma af_G_respectfulness':
  "\<phi> \<longrightarrow>\<^sub>P \<psi> \<Longrightarrow> af\<^sub>G \<phi> w \<longrightarrow>\<^sub>P af\<^sub>G \<psi> w"
  "\<phi> \<equiv>\<^sub>P \<psi> \<Longrightarrow> af\<^sub>G \<phi> w \<equiv>\<^sub>P af\<^sub>G \<psi> w"
  by (induction w arbitrary: \<phi> \<psi>) (insert af_G_respectfulness, fastforce+) 

lemma af_G_nested_propos:
  "nested_propos (af_G_letter \<phi> \<nu>) \<subseteq> nested_propos \<phi>"
  by (induction \<phi>) auto

lemma af_G_letter_sat_core:
  "Only_G \<G> \<Longrightarrow> \<G> \<Turnstile>\<^sub>P \<phi> \<Longrightarrow> \<G> \<Turnstile>\<^sub>P af_G_letter \<phi> \<nu>"
  by (induction \<phi>) (simp_all, blast+)

lemma af\<^sub>G_sat_core:
  "Only_G \<G> \<Longrightarrow> \<G> \<Turnstile>\<^sub>P \<phi> \<Longrightarrow> \<G> \<Turnstile>\<^sub>P af\<^sub>G \<phi> w"
  using af_G_letter_sat_core by (induction w rule: rev_induct) (simp_all, blast)

lemma af\<^sub>G_sat_core_generalized:
  "Only_G \<G> \<Longrightarrow> i \<le> j \<Longrightarrow> \<G> \<Turnstile>\<^sub>P af\<^sub>G \<phi> (w [0 \<rightarrow> i]) \<Longrightarrow> \<G> \<Turnstile>\<^sub>P af\<^sub>G \<phi> (w [0 \<rightarrow> j])"
  by (metis af\<^sub>G_sat_core foldl_append subsequence_append le_add_diff_inverse)

lemma af\<^sub>G_eval\<^sub>G:
  "Only_G \<G> \<Longrightarrow> \<G> \<Turnstile>\<^sub>P af\<^sub>G (eval\<^sub>G \<G> \<phi>) w \<longleftrightarrow> \<G> \<Turnstile>\<^sub>P eval\<^sub>G \<G> (af\<^sub>G \<phi> w)" 
  by (induction \<phi>) (simp_all add: eval\<^sub>G_prop_entailment af\<^sub>G_decompose)

lemma af\<^sub>G_keeps_F_and_S:
  assumes "ys \<noteq> []"
  assumes "S \<Turnstile>\<^sub>P af\<^sub>G \<phi> ys"
  shows "S \<Turnstile>\<^sub>P af\<^sub>G (F \<phi>) (xs @ ys)"
proof -
  have "af\<^sub>G \<phi> ys \<in> set (map (af\<^sub>G \<phi>) (suffixes (xs @ ys)))"
    using assms(1) unfolding suffixes_append map_append
    by (induction ys rule: List.list_nonempty_induct) auto
  thus ?thesis
    unfolding af\<^sub>G_F Or_prop_entailment using assms(2) by force
qed

subsection \<open>G-Subformulae Simplification\<close>

lemma G_af_simp[simp]:
  "\<^bold>G (af \<phi> w) = \<^bold>G \<phi>"
proof -
  { fix \<phi> \<nu> have "\<^bold>G (af_letter \<phi> \<nu>) = \<^bold>G \<phi>" by (induction \<phi>) auto }
  thus ?thesis
    by (induction w arbitrary: \<phi> rule: rev_induct) fastforce+
qed

lemma G_af\<^sub>G_simp[simp]:
  "\<^bold>G (af\<^sub>G \<phi> w) = \<^bold>G \<phi>"
proof -
  { fix \<phi> \<nu> have "\<^bold>G (af_G_letter \<phi> \<nu>) = \<^bold>G \<phi>" by (induction \<phi>) auto }
  thus ?thesis
    by (induction w arbitrary: \<phi> rule: rev_induct) fastforce+
qed

subsection \<open>Relation between af and $af_G$\<close>

lemma af_G_letter_free_F:
  "\<^bold>G \<phi> = {} \<Longrightarrow> \<^bold>G (af_letter \<phi> \<nu>) = {}"
  "\<^bold>G \<phi> = {} \<Longrightarrow> \<^bold>G (af_G_letter \<phi> \<nu>) = {}"
  by (induction \<phi>) auto

lemma af_G_free:
  assumes "\<^bold>G \<phi> = {}"
  shows "af \<phi> w = af\<^sub>G \<phi> w"
  using assms
proof (induction w arbitrary: \<phi>)
  case (Cons x xs)
    hence "af (af_letter \<phi> x) xs = af\<^sub>G (af_letter \<phi> x) xs"
      using af_G_letter_free_F[OF Cons.prems, THEN Cons.IH] by blast
    moreover
    have "af_letter \<phi> x = af_G_letter \<phi> x"
      using Cons.prems by (induction \<phi>) auto
    ultimately
    show ?case 
      by simp
qed simp

lemma af_equals_af\<^sub>G_base_cases:
  "af true w = af\<^sub>G true w"
  "af false w = af\<^sub>G false w"
  "af p(a) w = af\<^sub>G p(a) w"
  "af (np(a)) w = af\<^sub>G (np(a)) w"
  by (auto intro: af_G_free)

lemma af_implies_af\<^sub>G:
  "S \<Turnstile>\<^sub>P af \<phi> w \<Longrightarrow> S \<Turnstile>\<^sub>P af\<^sub>G \<phi> w"
proof (induction w arbitrary: S rule: rev_induct)
  case (snoc x xs)
    hence "S \<Turnstile>\<^sub>P af_letter (af \<phi> xs) x"
      by simp
    hence "S \<Turnstile>\<^sub>P af_letter (af\<^sub>G \<phi> xs) x"
      using af_respectfulness(1) snoc.IH unfolding ltl_prop_implies_def by blast
    moreover
    {
      fix \<phi> 
      have "\<And>\<nu>. S \<Turnstile>\<^sub>P af_letter \<phi> \<nu> \<Longrightarrow> S \<Turnstile>\<^sub>P af_G_letter \<phi> \<nu>"
        by (induction \<phi>) auto
    }
    ultimately
    show ?case
      using snoc.prems foldl_append by simp
qed simp

lemma af_implies_af\<^sub>G_2:
  "w \<Turnstile> af \<phi> xs \<Longrightarrow> w \<Turnstile> af\<^sub>G \<phi> xs"
  by (metis ltl_prop_implication_implies_ltl_implication af_implies_af\<^sub>G ltl_prop_implies_def)

lemma af\<^sub>G_implies_af_eval\<^sub>G':
  assumes "S \<Turnstile>\<^sub>P eval\<^sub>G \<G> (af\<^sub>G \<phi> w)"
  assumes "\<And>\<psi>. G \<psi> \<in> \<G> \<Longrightarrow> S \<Turnstile>\<^sub>P G \<psi>"
  assumes "\<And>\<psi> i. G \<psi> \<in> \<G> \<Longrightarrow> i < length w \<Longrightarrow> S \<Turnstile>\<^sub>P eval\<^sub>G \<G> (af\<^sub>G \<psi> (drop i w))" 
  shows   "S \<Turnstile>\<^sub>P af \<phi> w"
  using assms
proof (induction \<phi> arbitrary: w)
  case (LTLGlobal \<phi>)
    hence "G \<phi> \<in> \<G>"
      unfolding af\<^sub>G_simps eval\<^sub>G.simps by (cases "G \<phi> \<in> \<G>") simp+
    hence "S \<Turnstile>\<^sub>P G \<phi>"
      using LTLGlobal by simp
    moreover
    {
      fix x
      assume "x \<in> set (map (af \<phi>) (suffixes w))"
      then obtain w' where "x = af \<phi> w'" and "w' \<in> set (suffixes w)"
        by auto
      then obtain i where "w' = drop i w" and "i < length w"
        by (auto simp add: suffixes_alt_def subsequence_def)
      hence "S \<Turnstile>\<^sub>P eval\<^sub>G \<G> (af\<^sub>G \<phi> w')"
        using LTLGlobal.prems \<open>G \<phi> \<in> \<G>\<close> by simp
      hence "S \<Turnstile>\<^sub>P x"
        using LTLGlobal(1)[OF \<open>S \<Turnstile>\<^sub>P eval\<^sub>G \<G> (af\<^sub>G \<phi> w')\<close>] LTLGlobal(3-4) drop_drop
        unfolding \<open>x = af \<phi> w'\<close> \<open>w' = drop i w\<close> by simp
    }
    ultimately
    show ?case
      unfolding af_G eval\<^sub>G_And_map And_prop_entailment by simp
next
  case (LTLFinal \<phi>)
    then obtain x where x_def: "x \<in> set (F \<phi> # map (eval\<^sub>G \<G> o af\<^sub>G \<phi>) (suffixes w))" 
      and "S \<Turnstile>\<^sub>P x"
      unfolding Or_prop_entailment af\<^sub>G_F eval\<^sub>G_Or_map by force
    hence "\<exists>y \<in> set (F \<phi> # map (af \<phi>) (suffixes w)). S \<Turnstile>\<^sub>P y"
    proof (cases "x \<noteq> F \<phi>")
      case True
        then obtain w' where "S \<Turnstile>\<^sub>P eval\<^sub>G \<G> (af\<^sub>G \<phi> w')" and "w' \<in> set (suffixes w)"
          using x_def \<open>S \<Turnstile>\<^sub>P x\<close> by auto
        hence "\<And>\<psi> i. G \<psi> \<in> \<G> \<Longrightarrow> i < length w' \<Longrightarrow> S \<Turnstile>\<^sub>P eval\<^sub>G \<G> (af\<^sub>G \<psi> (drop i w'))"
          using LTLFinal.prems by (auto simp add: suffixes_alt_def subsequence_def)
        moreover
        have "\<And>\<psi>. G \<psi> \<in> \<G> \<Longrightarrow> S \<Turnstile>\<^sub>P eval\<^sub>G \<G> (G \<psi>)"
          using LTLFinal by simp
        ultimately
        have "S \<Turnstile>\<^sub>P af \<phi> w'"
          using LTLFinal.IH[OF \<open>S \<Turnstile>\<^sub>P eval\<^sub>G \<G> (af\<^sub>G \<phi> w')\<close>] using assms(2) by blast 
        thus ?thesis
          using \<open>w' \<in> set (suffixes w)\<close> by auto
    qed simp
    thus ?case
      unfolding af_F Or_prop_entailment eval\<^sub>G_Or_map by simp
next
  case (LTLNext \<phi>)
    thus ?case
    proof (cases w)
      case (Cons x xs)
        {
          fix \<psi> i
          assume "G \<psi> \<in> \<G>" and "Suc i < length (x#xs)"
          hence "S \<Turnstile>\<^sub>P eval\<^sub>G \<G> (af\<^sub>G \<psi> (drop (Suc i) (x#xs)))"
            using LTLNext.prems unfolding Cons by blast
          hence "S \<Turnstile>\<^sub>P eval\<^sub>G \<G> (af\<^sub>G \<psi> (drop i xs))"
            by simp
        }
        hence "\<And>\<psi> i. G \<psi> \<in> \<G> \<Longrightarrow> i < length xs \<Longrightarrow> S \<Turnstile>\<^sub>P eval\<^sub>G \<G> (af\<^sub>G \<psi> (drop i xs))"
          by simp
        thus ?thesis
          using LTLNext Cons by simp
    qed simp
next
  case (LTLUntil \<phi> \<psi>)
    thus ?case
    proof (induction w)
      case (Cons x xs)
        {
          assume "S \<Turnstile>\<^sub>P eval\<^sub>G \<G> (af\<^sub>G \<psi> (x # xs))"
          moreover
          have "\<And>\<psi> i. G \<psi> \<in> \<G> \<Longrightarrow> i < length (x#xs) \<Longrightarrow> S \<Turnstile>\<^sub>P eval\<^sub>G \<G> (af\<^sub>G \<psi> (drop i (x#xs)))"
            using Cons by simp
          ultimately
          have "S \<Turnstile>\<^sub>P af \<psi> (x # xs)"
            using Cons.prems by blast
          hence ?case
            unfolding af_U by simp
        }
        moreover
        {
          assume "S \<Turnstile>\<^sub>P eval\<^sub>G \<G> (af\<^sub>G (\<phi> U \<psi>) xs)" and "S \<Turnstile>\<^sub>P eval\<^sub>G \<G> (af\<^sub>G \<phi> (x # xs))"
          moreover
          have "\<And>\<psi> i. G \<psi> \<in> \<G> \<Longrightarrow> i < length (x#xs) \<Longrightarrow> S \<Turnstile>\<^sub>P eval\<^sub>G \<G> (af\<^sub>G \<psi> (drop i (x#xs)))"
            using Cons by simp
          ultimately
          have "S \<Turnstile>\<^sub>P af \<phi> (x # xs)" and "S \<Turnstile>\<^sub>P af (\<phi> U \<psi>) xs"  
            using Cons by (blast, force) 
          hence ?case
            unfolding af_U by simp
        }
        ultimately
        show ?case
          using Cons(4) unfolding af\<^sub>G_U by auto
    qed simp
next
  case (LTLProp a)
    thus ?case
    proof (cases w)
      case (Cons x xs)
        thus ?thesis
          using LTLProp by (cases "a \<in> x") simp+
    qed simp
next
  case (LTLPropNeg a)
    thus ?case
    proof (cases w)
      case (Cons x xs)
        thus ?thesis
          using LTLPropNeg by (cases "a \<in> x") simp+
    qed simp
qed (unfold af_equals_af\<^sub>G_base_cases af\<^sub>G_decompose af_decompose, auto)

lemma af\<^sub>G_implies_af_eval\<^sub>G:
  assumes "S \<Turnstile>\<^sub>P eval\<^sub>G \<G> (af\<^sub>G \<phi> (w [0\<rightarrow>j]))"
  assumes "\<And>\<psi>. G \<psi> \<in> \<G> \<Longrightarrow> S \<Turnstile>\<^sub>P G \<psi>"
  assumes "\<And>\<psi> i. G \<psi> \<in> \<G> \<Longrightarrow> i \<le> j \<Longrightarrow> S \<Turnstile>\<^sub>P eval\<^sub>G \<G> (af\<^sub>G \<psi> (w [i \<rightarrow> j]))" 
  shows "S \<Turnstile>\<^sub>P af \<phi> (w [0\<rightarrow>j])"
  using af\<^sub>G_implies_af_eval\<^sub>G'[OF assms(1-2), unfolded subsequence_length subsequence_drop] assms(3) by force 

subsection \<open>Continuation\<close>

\<comment> \<open>af fulfills the infinite continuation w' of a word after skipping some finite prefix w.
    Corresponds to Lemma 7 in arXiv: 1402.3388v2\<close>

lemma af_ltl_continuation:
  "(w \<frown> w') \<Turnstile> \<phi> \<longleftrightarrow> w' \<Turnstile> af \<phi> w"
proof (induction w arbitrary: \<phi> w')
  case (Cons x xs)
    have "((x # xs) \<frown> w') 0 = x"
      unfolding conc_def nth_Cons_0 by simp
    moreover
    have "suffix 1 ((x # xs) \<frown> w') = xs \<frown> w'"
      unfolding suffix_def conc_def by fastforce
    moreover
    {
      fix \<phi> :: "'a ltl"
      have "\<And>w. w \<Turnstile> \<phi> \<longleftrightarrow> suffix 1 w \<Turnstile> af_letter \<phi> (w 0)"
        by (induction \<phi>) ((unfold LTL_F_one_step_unfolding LTL_G_one_step_unfolding LTL_U_one_step_unfolding)?, auto)
    }
    ultimately
    have "((x # xs) \<frown> w') \<Turnstile> \<phi> \<longleftrightarrow> (xs \<frown> w') \<Turnstile> af_letter \<phi> x"
      by metis
    also
    have "\<dots> \<longleftrightarrow> w' \<Turnstile> af \<phi> (x#xs)"
      using Cons.IH by simp
    finally
    show ?case .
qed simp

lemma af_ltl_continuation_suffix:
  "w \<Turnstile> \<phi> \<longleftrightarrow> suffix i w \<Turnstile> af \<phi> (w[0 \<rightarrow> i])"
  using af_ltl_continuation prefix_suffix subsequence_def by metis

lemma af_G_ltl_continuation:
  "\<forall>\<psi> \<in> \<^bold>G \<phi>. w' \<Turnstile> \<psi> = (w \<frown> w') \<Turnstile> \<psi> \<Longrightarrow> (w \<frown> w') \<Turnstile> \<phi> \<longleftrightarrow> w' \<Turnstile> af\<^sub>G \<phi> w"
proof (induction w arbitrary: w' \<phi>)
  case (Cons x xs)
    {
      fix \<psi> :: "'a ltl" fix  w w' w'' 
      assume "w'' \<Turnstile> G \<psi> = ((w @ w') \<frown> w'') \<Turnstile> G \<psi>"
      hence "w'' \<Turnstile> G \<psi> = (w' \<frown>  w'') \<Turnstile> G \<psi>" and "(w' \<frown> w'') \<Turnstile> G \<psi> = ((w @ w') \<frown> w'') \<Turnstile> G \<psi>"
        by (induction w' arbitrary: w) (metis LTL_suffix_G suffix_conc_length conc_conc)+
    }
    note G_stable = this
    have A: "\<forall>\<psi>\<in>\<^bold>G (af\<^sub>G \<phi> [x]). w' \<Turnstile> \<psi> = (xs \<frown> w') \<Turnstile> \<psi>"
      using G_stable(1)[of w' _ "[x]"] Cons.prems unfolding G_af\<^sub>G_simp conc_conc append.simps unfolding G_nested_propos_alt_def by blast
    have B: "\<forall>\<psi>\<in>\<^bold>G \<phi>. ([x] \<frown> xs \<frown> w') \<Turnstile> \<psi> = (xs \<frown> w') \<Turnstile> \<psi>"
      using G_stable(2)[of w' _ "[x]"] Cons.prems unfolding conc_conc append.simps unfolding G_nested_propos_alt_def by blast 
    hence "([x] \<frown> xs \<frown> w') \<Turnstile> \<phi> = (xs \<frown> w') \<Turnstile> af\<^sub>G \<phi> [x]"
    proof (induction \<phi>)
      case (LTLFinal \<phi>)
        thus ?case
          unfolding LTL_F_one_step_unfolding
          by (auto simp add: suffix_conc_length[of "[x]", simplified])
    next
      case (LTLUntil \<phi> \<psi>)
        thus ?case
          unfolding LTL_U_one_step_unfolding
          by (auto simp add: suffix_conc_length[of "[x]", simplified])
    qed (auto simp add: conc_fst[of 0 "[x]"] suffix_conc_length[of "[x]", simplified])
    also
    have "... = w' \<Turnstile> af\<^sub>G \<phi> (x # xs)"
      using Cons.IH[of "af\<^sub>G \<phi> [x]" w'] A by simp
    finally
    show ?case unfolding conc_conc 
      by simp
qed simp

lemma af\<^sub>G_ltl_continuation_suffix:
  "\<forall>\<psi> \<in> \<^bold>G \<phi>. w \<Turnstile> \<psi> = (suffix i w) \<Turnstile> \<psi> \<Longrightarrow> w \<Turnstile> \<phi> \<longleftrightarrow> suffix i w \<Turnstile> af\<^sub>G \<phi> (w [0 \<rightarrow> i])"  
  by (metis af_G_ltl_continuation[of \<phi> "suffix i w"] prefix_suffix subsequence_def)

subsection \<open>Eager Unfolding @{term af} and @{term af\<^sub>G}\<close> 

fun Unf :: "'a ltl \<Rightarrow> 'a ltl"
where
  "Unf (F \<phi>) = F \<phi> or Unf \<phi>"
| "Unf (G \<phi>) = G \<phi> and Unf \<phi>" 
| "Unf (\<phi> U \<psi>) = (\<phi> U \<psi> and Unf \<phi>) or Unf \<psi>"
| "Unf (\<phi> and \<psi>) = Unf \<phi> and Unf \<psi>"
| "Unf (\<phi> or \<psi>) = Unf \<phi> or Unf \<psi>"
| "Unf \<phi> = \<phi>"

fun Unf\<^sub>G :: "'a ltl \<Rightarrow> 'a ltl"
where
  "Unf\<^sub>G (F \<phi>) = F \<phi> or Unf\<^sub>G \<phi>"
| "Unf\<^sub>G (G \<phi>) = G \<phi>" 
| "Unf\<^sub>G (\<phi> U \<psi>) = (\<phi> U \<psi> and Unf\<^sub>G \<phi>) or Unf\<^sub>G \<psi>"
| "Unf\<^sub>G (\<phi> and \<psi>) = Unf\<^sub>G \<phi> and Unf\<^sub>G \<psi>"
| "Unf\<^sub>G (\<phi> or \<psi>) = Unf\<^sub>G \<phi> or Unf\<^sub>G \<psi>"
| "Unf\<^sub>G \<phi> = \<phi>"

fun step :: "'a ltl \<Rightarrow> 'a set \<Rightarrow> 'a ltl"
where
  "step p(a) \<nu> = (if a \<in> \<nu> then true else false)"
| "step (np(a)) \<nu> = (if a \<notin> \<nu> then true else false)"
| "step (X \<phi>) \<nu> = \<phi>"
| "step (\<phi> and \<psi>) \<nu> = step \<phi> \<nu> and step \<psi> \<nu>"
| "step (\<phi> or \<psi>) \<nu> = step \<phi> \<nu> or step \<psi> \<nu>"
| "step \<phi> \<nu> = \<phi>"

fun af_letter_opt
where
  "af_letter_opt \<phi> \<nu> = Unf (step \<phi> \<nu>)"

fun af_G_letter_opt
where
  "af_G_letter_opt \<phi> \<nu> = Unf\<^sub>G (step \<phi> \<nu>)"

abbreviation af_opt :: "'a ltl \<Rightarrow> 'a set list \<Rightarrow> 'a ltl" ("af\<^sub>\<UU>")
where
  "af\<^sub>\<UU> \<phi> w \<equiv> (foldl af_letter_opt \<phi> w)"

abbreviation af_G_opt :: "'a ltl \<Rightarrow> 'a set list \<Rightarrow> 'a ltl" ("af\<^sub>G\<^sub>\<UU>")
where
  "af\<^sub>G\<^sub>\<UU> \<phi> w \<equiv> (foldl af_G_letter_opt \<phi> w)"

lemma af_letter_alt_def:
  "af_letter \<phi> \<nu> = step (Unf \<phi>) \<nu>"
  "af_G_letter \<phi> \<nu> = step (Unf\<^sub>G \<phi>) \<nu>"
  by (induction \<phi>) simp_all

lemma af_to_af_opt:
  "Unf (af \<phi> w) = af\<^sub>\<UU> (Unf \<phi>) w"
  "Unf\<^sub>G (af\<^sub>G \<phi> w) = af\<^sub>G\<^sub>\<UU> (Unf\<^sub>G \<phi>) w"
  by (induction w arbitrary: \<phi>)
     (simp_all add: af_letter_alt_def)

lemma af_equiv:
  "af \<phi> (w @ [\<nu>]) = step (af\<^sub>\<UU> (Unf \<phi>) w) \<nu>"
  using af_to_af_opt(1) by (metis af_letter_alt_def(1) foldl_Cons foldl_Nil foldl_append)

lemma af_equiv':
  "af \<phi> (w [0 \<rightarrow> Suc i]) = step (af\<^sub>\<UU> (Unf \<phi>) (w [0 \<rightarrow> i])) (w i)"
  using af_equiv unfolding subsequence_def by auto

subsection \<open>Lifted Functions\<close>

lemma respectfulness:
  "\<phi> \<longrightarrow>\<^sub>P \<psi> \<Longrightarrow> af_letter_opt \<phi> \<nu> \<longrightarrow>\<^sub>P af_letter_opt \<psi> \<nu>"
  "\<phi> \<equiv>\<^sub>P \<psi> \<Longrightarrow> af_letter_opt \<phi> \<nu> \<equiv>\<^sub>P af_letter_opt \<psi> \<nu>"
  "\<phi> \<longrightarrow>\<^sub>P \<psi> \<Longrightarrow> af_G_letter_opt \<phi> \<nu> \<longrightarrow>\<^sub>P af_G_letter_opt \<psi> \<nu>"
  "\<phi> \<equiv>\<^sub>P \<psi> \<Longrightarrow> af_G_letter_opt \<phi> \<nu> \<equiv>\<^sub>P af_G_letter_opt \<psi> \<nu>"
  "\<phi> \<longrightarrow>\<^sub>P \<psi> \<Longrightarrow> step \<phi> \<nu> \<longrightarrow>\<^sub>P step \<psi> \<nu>"
  "\<phi> \<equiv>\<^sub>P \<psi> \<Longrightarrow> step \<phi> \<nu> \<equiv>\<^sub>P step \<psi> \<nu>"
  "\<phi> \<longrightarrow>\<^sub>P \<psi> \<Longrightarrow> Unf \<phi> \<longrightarrow>\<^sub>P Unf \<psi>"
  "\<phi> \<equiv>\<^sub>P \<psi> \<Longrightarrow> Unf \<phi> \<equiv>\<^sub>P Unf \<psi>"
  "\<phi> \<longrightarrow>\<^sub>P \<psi> \<Longrightarrow> Unf\<^sub>G \<phi> \<longrightarrow>\<^sub>P Unf\<^sub>G \<psi>"
  "\<phi> \<equiv>\<^sub>P \<psi> \<Longrightarrow> Unf\<^sub>G \<phi> \<equiv>\<^sub>P Unf\<^sub>G \<psi>"
  using decomposable_function_subst[of "\<lambda>\<chi>. af_letter_opt \<chi> \<nu>", simplified] af_letter_opt.simps
  using decomposable_function_subst[of "\<lambda>\<chi>. af_G_letter_opt \<chi> \<nu>", simplified] af_G_letter_opt.simps
  using decomposable_function_subst[of "\<lambda>\<chi>. step \<chi> \<nu>", simplified]
  using decomposable_function_subst[of Unf, simplified] 
  using decomposable_function_subst[of Unf\<^sub>G, simplified]
  using subst_respects_ltl_prop_entailment by metis+

lemma nested_propos:
  "nested_propos (step \<phi> \<nu>) \<subseteq> nested_propos \<phi>"
  "nested_propos (Unf \<phi>) \<subseteq> nested_propos \<phi>"
  "nested_propos (Unf\<^sub>G \<phi>) \<subseteq> nested_propos \<phi>"
  "nested_propos (af_letter_opt \<phi> \<nu>) \<subseteq> nested_propos \<phi>"
  "nested_propos (af_G_letter_opt \<phi> \<nu>) \<subseteq> nested_propos \<phi>"
  by (induction \<phi>) auto

text \<open>Lift functions and bind to new names\<close>

interpretation af_abs: lift_ltl_transformer af_letter
  using lift_ltl_transformer_def af_respectfulness af_nested_propos by blast

definition af_letter_abs ("\<up>af")
where
  "\<up>af \<equiv> af_abs.f_abs"

interpretation af_G_abs: lift_ltl_transformer af_G_letter
  using lift_ltl_transformer_def af_G_respectfulness af_G_nested_propos by blast

definition af_G_letter_abs ("\<up>af\<^sub>G")
where
  "\<up>af\<^sub>G \<equiv> af_G_abs.f_abs"

interpretation af_abs_opt: lift_ltl_transformer af_letter_opt
  using lift_ltl_transformer_def respectfulness nested_propos by blast

definition af_letter_abs_opt ("\<up>af\<^sub>\<UU>")
where
  "\<up>af\<^sub>\<UU> \<equiv> af_abs_opt.f_abs"

interpretation af_G_abs_opt: lift_ltl_transformer af_G_letter_opt
  using lift_ltl_transformer_def respectfulness nested_propos by blast

definition af_G_letter_abs_opt ("\<up>af\<^sub>G\<^sub>\<UU>")
where
  "\<up>af\<^sub>G\<^sub>\<UU> \<equiv> af_G_abs_opt.f_abs"

lift_definition step_abs :: "'a ltl\<^sub>P \<Rightarrow> 'a set \<Rightarrow> 'a ltl\<^sub>P" ("\<up>step") is step
  by (insert respectfulness)

lift_definition Unf_abs :: "'a ltl\<^sub>P \<Rightarrow> 'a ltl\<^sub>P" ("\<up>Unf") is Unf
  by (insert respectfulness)

lift_definition Unf\<^sub>G_abs :: "'a ltl\<^sub>P \<Rightarrow> 'a ltl\<^sub>P" ("\<up>Unf\<^sub>G") is Unf\<^sub>G
  by (insert respectfulness)

subsubsection \<open>Properties\<close>

lemma af_G_letter_opt_sat_core:
  "Only_G \<G> \<Longrightarrow> \<G> \<Turnstile>\<^sub>P \<phi> \<Longrightarrow> \<G> \<Turnstile>\<^sub>P af_G_letter_opt \<phi> \<nu>"
  by (induction \<phi>) auto 

lemma af_G_letter_sat_core_lifted:
  "Only_G \<G> \<Longrightarrow> \<G> \<Turnstile>\<^sub>P Rep \<phi> \<Longrightarrow> \<G> \<Turnstile>\<^sub>P Rep (af_G_letter_abs \<phi> \<nu>)"
  by (metis af_G_letter_sat_core Quotient_ltl_prop_equiv_quotient[THEN Quotient_rep_abs] Quotient3_ltl_prop_equiv_quotient[THEN Quotient3_abs_rep] af_G_abs.f_abs.abs_eq ltl_prop_equiv_def af_G_letter_abs_def) 

lemma af_G_letter_opt_sat_core_lifted:
  "Only_G \<G> \<Longrightarrow> \<G> \<Turnstile>\<^sub>P Rep \<phi> \<Longrightarrow> \<G> \<Turnstile>\<^sub>P Rep (\<up>af\<^sub>G\<^sub>\<UU> \<phi> \<nu>)"
  unfolding af_G_letter_abs_opt_def
  by (metis af_G_letter_opt_sat_core Quotient_ltl_prop_equiv_quotient[THEN Quotient_rep_abs] Quotient3_ltl_prop_equiv_quotient[THEN Quotient3_abs_rep] af_G_abs_opt.f_abs.abs_eq ltl_prop_equiv_def) 

lemma af_G_letter_abs_opt_split:
  "\<up>Unf\<^sub>G (\<up>step \<Phi> \<nu>) = \<up>af\<^sub>G\<^sub>\<UU> \<Phi> \<nu>"
  unfolding af_G_letter_abs_opt_def step_abs_def comp_def af_G_abs_opt.f_abs_def 
  using map_fun_apply Unf\<^sub>G_abs.abs_eq af_G_letter_opt.simps by auto

lemma af_unfold: 
  "\<up>af = (\<lambda>\<phi> \<nu>. \<up>step (\<up>Unf \<phi>) \<nu>)" 
  by (metis Unf_abs_def af_abs.f_abs.abs_eq af_letter_abs_def af_letter_alt_def(1) ltl\<^sub>P_abs_rep map_fun_apply step_abs.abs_eq)
 
lemma af_opt_unfold: 
  "\<up>af\<^sub>\<UU> = (\<lambda>\<phi> \<nu>. \<up>Unf (\<up>step \<phi> \<nu>))"
  by (metis (no_types, lifting) Quotient3_abs_rep Quotient3_ltl_prop_equiv_quotient Unf_abs.abs_eq af_abs_opt.f_abs.abs_eq af_letter_abs_opt_def af_letter_opt.elims id_apply map_fun_apply  step_abs_def)

lemma af_abs_equiv:
  "foldl \<up>af \<psi> (xs @ [x]) = \<up>step (foldl \<up>af\<^sub>\<UU> (\<up>Unf \<psi>) xs) x" 
  unfolding af_unfold af_opt_unfold by (induction xs arbitrary: x \<psi> rule: rev_induct) simp+

lemma Rep_Abs_equiv: 
  "Rep (Abs \<phi>) \<equiv>\<^sub>P \<phi>"
  using Rep_Abs_prop_entailment unfolding ltl_prop_equiv_def by auto

lemma Rep_step: 
  "Rep (\<up>step \<Phi> \<nu>) \<equiv>\<^sub>P step (Rep \<Phi>) \<nu>"
  by (metis Quotient3_abs_rep Quotient3_ltl_prop_equiv_quotient ltl_prop_equiv_quotient.abs_eq_iff step_abs.abs_eq)

lemma step_\<G>:
  "Only_G \<G> \<Longrightarrow> \<G> \<Turnstile>\<^sub>P \<phi> \<Longrightarrow> \<G> \<Turnstile>\<^sub>P step \<phi> \<nu>"
  by (induction \<phi>) auto

lemma Unf\<^sub>G_\<G>:
  "Only_G \<G> \<Longrightarrow> \<G> \<Turnstile>\<^sub>P \<phi> \<Longrightarrow> \<G> \<Turnstile>\<^sub>P Unf\<^sub>G \<phi>"
  by (induction \<phi>) auto

hide_fact (open) respectfulness nested_propos

end
