(*
  File:    SDS_Automation.thy
  Author:  Manuel Eberl <eberlm@in.tum.de>

  This theory provides a number of commands to automatically derive restrictions on the 
  results of Social Decision Schemes fulfilling properties like Anonymity, Neutrality, 
  Ex-post- or SD-efficiency, and SD-Strategy-Proofness.
*)

section \<open>Automatic Fact Gathering for Social Decision Schemes\<close>

theory SDS_Automation
  imports 
    Preference_Profile_Cmd
    QSOpt_Exact
    "../Social_Decision_Schemes"
keywords 
  "derive_orbit_equations"
  "derive_support_conditions" 
  "derive_ex_post_conditions"
  "find_inefficient_supports"
  "prove_inefficient_supports"
  "derive_strategyproofness_conditions" :: thy_goal
begin

text \<open>
  We now provide the following commands to automatically derive restrictions on the results
  of Social Decision Schemes satisfying Anonymity, Neutrality, Efficiency, or Strategy-Proofness:
  \begin{description}
    \item[@{command derive_orbit_equations}] to derive equalities arising from automorphisms of the 
      given profiles due to Anonymity and Neutrality
    \item[@{command derive_ex_post_conditions}] to find all Pareto losers and the given profiles and 
      derive the facts that they must be assigned probability 0 by any \textit{ex-post}-efficient
      SDS
    \item[@{command find_inefficient_supports}] to use Linear Programming to find all minimal SD-inefficient 
      (but not \textit{ex-post}-inefficient) supports in the given profiles and output a 
      corresponding witness lottery for each of them
    \item[@{command prove_inefficient_supports}] to prove a specified set of support conditions arising from
      \textit{ex-post}- or \textit{SD}-Efficiency. For conditions arising from \textit{SD}-Efficiency,
      a witness lottery must be specified (e.\,g. as computed by @{command derive_orbit_equations}).
    \item[@{command derive_support_conditions}] to automatically find and prove all support conditions
      arising from \textit{ex-post-} and \textit{SD}-Efficiency
    \item [@{command derive_strategyproofness_conditions}] to automatically derive all conditions
      arising from weak Strategy-Proofness and any manipulations between the given preference 
      profiles. An optional maximum manipulation size can be specified.
  \end{description}
  All commands except @{command find_inefficient_supports} open a proof state and leave behind 
  proof obligations for the user to discharge. This should always be possible using the Simplifier,
  possibly with a few additional rules, depending on the context.
 
\<close>

lemma disj_False_right: "P \<or> False \<longleftrightarrow> P" by simp

lemmas multiset_add_ac = add_ac[where ?'a = "'a multiset"]

lemma less_or_eq_real: 
  "(x::real) < y \<or> x = y \<longleftrightarrow> x \<le> y" "x < y \<or> y = x \<longleftrightarrow> x \<le> y" by linarith+

lemma multiset_Diff_single_normalize:
  fixes a c assumes "a \<noteq> c"
  shows   "({#a#} + B) - {#c#} = {#a#} + (B - {#c#})"
  using assms by auto

lemma ex_post_efficient_aux:
  assumes "prefs_from_table_wf agents alts xss" "R \<equiv> prefs_from_table xss"
  assumes "i \<in> agents" "\<forall>i\<in>agents. y \<succeq>[prefs_from_table xss i] x" "\<not>y \<preceq>[prefs_from_table xss i] x"
  shows   "ex_post_efficient_sds agents alts sds \<longrightarrow> pmf (sds R) x = 0"
proof
  assume ex_post: "ex_post_efficient_sds agents alts sds"
  from assms(1,2) have wf: "pref_profile_wf agents alts R"
    by (simp add: pref_profile_from_tableI')
  from ex_post interpret ex_post_efficient_sds agents alts sds .
  from assms(2-) show "pmf (sds R) x = 0"
    by (intro ex_post_efficient''[OF wf, of i x y]) simp_all
qed

lemma SD_inefficient_support_aux:
  assumes R: "prefs_from_table_wf agents alts xss" "R \<equiv> prefs_from_table xss"
  assumes as: "as \<noteq> []" "set as \<subseteq> alts" "distinct as" "A = set as" 
  assumes ys: "\<forall>x\<in>set (map snd ys). 0 \<le> x" "sum_list (map snd ys) = 1" "set (map fst ys) \<subseteq> alts"
  assumes i: "i \<in> agents"
  assumes SD1: "\<forall>i\<in>agents. \<forall>x\<in>alts. 
    sum_list (map snd (filter (\<lambda>y. prefs_from_table xss i x (fst y)) ys)) \<ge>
    real (length (filter (prefs_from_table xss i x) as)) / real (length as)"
  assumes SD2: "\<exists>x\<in>alts. sum_list (map snd (filter (\<lambda>y. prefs_from_table xss i x (fst y)) ys)) >
                        real (length (filter (prefs_from_table xss i x) as)) / real (length as)"
  shows   "sd_efficient_sds agents alts sds \<longrightarrow> (\<exists>x\<in>A. pmf (sds R) x = 0)"
proof
  assume "sd_efficient_sds agents alts sds"
  from R have wf: "pref_profile_wf agents alts R" 
    by (simp add: pref_profile_from_tableI')
  then interpret pref_profile_wf agents alts R .
  interpret sd_efficient_sds agents alts sds by fact
  from ys have ys': "pmf_of_list_wf ys" by (intro pmf_of_list_wfI) auto
  
  {
    fix i x assume "x \<in> alts" "i \<in> agents"
    with ys' have "lottery_prob (pmf_of_list ys) (preferred_alts (R i) x) = 
      sum_list (map snd (filter (\<lambda>y. prefs_from_table xss i x (fst y)) ys))"
      by (subst measure_pmf_of_list) (simp_all add: preferred_alts_def R)
  } note A = this
  {
    fix i x assume "x \<in> alts" "i \<in> agents"
    with as have "lottery_prob (pmf_of_set (set as)) (preferred_alts (R i) x) = 
      real (card (set as \<inter> preferred_alts (R i) x)) / real (card (set as))"
      by (subst measure_pmf_of_set) simp_all
    also have "set as \<inter> preferred_alts (R i) x = set (filter (\<lambda>y. R i x y) as)"
      by (auto simp add: preferred_alts_def)
    also have "card \<dots> = length (filter (\<lambda>y. R i x y) as)"
      by (intro distinct_card distinct_filter assms)
    also have "card (set as) = length as" by (intro distinct_card assms)
    finally have "lottery_prob (pmf_of_set (set as)) (preferred_alts (R i) x) =
      real (length (filter (prefs_from_table xss i x) as)) / real (length as)"
      by (simp add: R)
  } note B = this

  from wf show "\<exists>x\<in>A. pmf (sds R) x = 0"
  proof (rule SD_inefficient_support')
    from ys ys' show lottery1: "pmf_of_list ys \<in> lotteries" by (intro pmf_of_list_lottery)
    show i: "i \<in> agents" by fact
    from as have lottery2: "pmf_of_set (set as) \<in> lotteries"
      by (intro pmf_of_set_lottery) simp_all
    from i as SD2 lottery1 lottery2 show "\<not>SD (R i) (pmf_of_list ys) (pmf_of_set A)"
      by (subst preorder_on.SD_preorder[of alts]) (auto simp: A B not_le)
    from as SD1 lottery1 lottery2 
      show "\<forall>i\<in>agents. SD (R i) (pmf_of_set A) (pmf_of_list ys)"
        by safe (auto simp: preorder_on.SD_preorder[of alts] A B)
  qed (insert as, simp_all)
qed



definition pref_classes where
  "pref_classes alts le = preferred_alts le ` alts - {alts}"

primrec pref_classes_lists where
  "pref_classes_lists [] = {}"
| "pref_classes_lists (xs#xss) = insert (\<Union>(set (xs#xss))) (pref_classes_lists xss)"

fun pref_classes_lists_aux where
  "pref_classes_lists_aux acc [] = {}"
| "pref_classes_lists_aux acc (xs#xss) = insert acc (pref_classes_lists_aux (acc \<union> xs) xss)"

lemma pref_classes_lists_append: 
  "pref_classes_lists (xs @ ys) = (\<union>) (\<Union>(set ys)) ` pref_classes_lists xs \<union> pref_classes_lists ys"
  by (induction xs) auto

lemma pref_classes_lists_aux:
  assumes "is_weak_ranking xss" "acc \<inter> (\<Union>(set xss)) = {}"
  shows  "pref_classes_lists_aux acc xss = 
            (insert acc ((\<lambda>A. A \<union> acc) ` pref_classes_lists (rev xss)) - {acc \<union> \<Union>(set xss)})"
using assms
proof (induction acc xss rule: pref_classes_lists_aux.induct [case_names Nil Cons]) 
  case (Cons acc xs xss)
  from Cons.prems have A: "acc \<inter> (xs \<union> \<Union>(set xss)) = {}" "xs \<noteq> {}" 
    by (simp_all add: is_weak_ranking_Cons)
  from Cons.prems have "pref_classes_lists_aux (acc \<union> xs) xss =
                          insert (acc \<union> xs) ((\<lambda>A. A \<union> (acc \<union> xs)) `pref_classes_lists (rev xss)) -
                          {acc \<union> xs \<union> \<Union>(set xss)}"
    by (intro Cons.IH) (auto simp: is_weak_ranking_Cons)
  with Cons.prems have "pref_classes_lists_aux acc (xs # xss) = 
      insert acc (insert (acc \<union> xs) ((\<lambda>A. A \<union> (acc \<union> xs)) ` pref_classes_lists (rev xss)) -
         {acc \<union> (xs \<union> \<Union>(set xss))})"
    by (simp_all add: is_weak_ranking_Cons pref_classes_lists_append image_image Un_ac)
  also from  A have "\<dots> = insert acc (insert (acc \<union> xs) ((\<lambda>x. x \<union> (acc \<union> xs)) ` 
                            pref_classes_lists (rev xss))) - {acc \<union> (xs \<union> \<Union>(set xss))}" 
    by blast
  finally show ?case
    by (simp_all add: pref_classes_lists_append image_image Un_ac)
qed simp_all

lemma pref_classes_list_aux_hd_tl:
  assumes "is_weak_ranking xss" "xss \<noteq> []"
  shows   "pref_classes_lists_aux (hd xss) (tl xss) = pref_classes_lists (rev xss) - {\<Union>(set xss)}"
proof -
  from assms have A: "xss = hd xss # tl xss" by simp
  from assms have "hd xss \<inter> \<Union>(set (tl xss)) = {} \<and> is_weak_ranking (tl xss)"
    by (subst (asm) A, subst (asm) is_weak_ranking_Cons) simp_all
  hence "pref_classes_lists_aux (hd xss) (tl xss) = 
           insert (hd xss) ((\<lambda>A. A \<union> hd xss) ` pref_classes_lists (rev (tl xss))) -
           {hd xss \<union> \<Union>(set (tl xss))}" by (intro pref_classes_lists_aux) simp_all
  also have "hd xss \<union> \<Union>(set (tl xss)) = \<Union>(set xss)" by (subst (3) A, subst set_simps) simp_all
  also have "insert (hd xss) ((\<lambda>A. A \<union> hd xss) ` pref_classes_lists (rev (tl xss))) =
               pref_classes_lists (rev (tl xss) @ [hd xss])"
    by (subst pref_classes_lists_append) auto
  also have "rev (tl xss) @ [hd xss] = rev xss" by (subst (3) A) (simp only: rev.simps)
  finally show ?thesis .
qed

lemma pref_classes_of_weak_ranking_aux:
  assumes "is_weak_ranking xss"
  shows   "of_weak_ranking_Collect_ge xss ` (\<Union>(set xss)) = pref_classes_lists xss"
proof safe
  fix X x assume "x \<in> X" "X \<in> set xss"
  with assms show "of_weak_ranking_Collect_ge xss x \<in> pref_classes_lists xss"
    by (induction xss) (auto simp: is_weak_ranking_Cons of_weak_ranking_Collect_ge_Cons')
next
  fix x assume "x \<in> pref_classes_lists xss"
  with assms show "x \<in> of_weak_ranking_Collect_ge xss ` \<Union>(set xss)"
  proof (induction xss)
    case (Cons xs xss)
    from Cons.prems consider "x = xs \<union> \<Union>(set xss)" | "x \<in> pref_classes_lists xss" by auto
    thus ?case
    proof cases
      assume "x = xs \<union> \<Union>(set xss)"
      with Cons.prems show ?thesis
        by (auto simp: is_weak_ranking_Cons of_weak_ranking_Collect_ge_Cons')
    next
      assume x: "x \<in> pref_classes_lists xss"
      from Cons.prems x have "x \<in> of_weak_ranking_Collect_ge xss ` \<Union>(set xss)"
        by (intro Cons.IH) (simp_all add: is_weak_ranking_Cons)
      moreover from Cons.prems have "xs \<inter> \<Union>(set xss) = {}"
        by (simp add: is_weak_ranking_Cons)
      ultimately have "x \<in> of_weak_ranking_Collect_ge xss `
                         ((xs \<union> \<Union>(set xss)) \<inter> {x. x \<notin> xs})" by blast
      thus ?thesis by (simp add: of_weak_ranking_Collect_ge_Cons')
    qed
  qed simp_all
qed

lemma eval_pref_classes_of_weak_ranking:
  assumes "\<Union>(set xss) = alts" "is_weak_ranking xss" "alts \<noteq> {}"
  shows   "pref_classes alts (of_weak_ranking xss) = pref_classes_lists_aux (hd xss) (tl xss)"
proof -
  have "pref_classes alts (of_weak_ranking xss) = 
               preferred_alts (of_weak_ranking xss) ` (\<Union>(set (rev xss))) - {\<Union>(set xss)}"
    by (simp add: pref_classes_def assms)
  also {
    have "of_weak_ranking_Collect_ge (rev xss) ` (\<Union>(set (rev xss))) = pref_classes_lists (rev xss)"
      using assms by (intro pref_classes_of_weak_ranking_aux) simp_all
    also have "of_weak_ranking_Collect_ge (rev xss) = preferred_alts (of_weak_ranking xss)"
      by (intro ext) (simp_all add: of_weak_ranking_Collect_ge_def preferred_alts_def)
    finally have "preferred_alts (of_weak_ranking xss) ` (\<Union>(set (rev xss))) = 
                    pref_classes_lists (rev xss)" .
  }
  also from assms have "pref_classes_lists (rev xss) - {\<Union>(set xss)} = 
                          pref_classes_lists_aux (hd xss) (tl xss)"
    by (intro pref_classes_list_aux_hd_tl [symmetric]) auto
  finally show ?thesis by simp
qed


context preorder_on
begin

lemma SD_iff_pref_classes:
  assumes "p \<in> lotteries_on carrier" "q \<in> lotteries_on carrier"
  shows   "p \<preceq>[SD(le)] q \<longleftrightarrow> 
             (\<forall>A\<in>pref_classes carrier le. measure_pmf.prob p A \<le> measure_pmf.prob q A)"
proof safe
  fix A assume "p \<preceq>[SD(le)] q" "A \<in> pref_classes carrier le"
  thus "measure_pmf.prob p A \<le> measure_pmf.prob q A"
    by (auto simp: SD_preorder pref_classes_def)
next
  assume A: "\<forall>A\<in>pref_classes carrier le. measure_pmf.prob p A \<le> measure_pmf.prob q A"
  show "p \<preceq>[SD(le)] q"
  proof (rule SD_preorderI)
    fix x assume x: "x \<in> carrier"
    show "measure_pmf.prob p (preferred_alts le x)
             \<le> measure_pmf.prob q (preferred_alts le x)"
    proof (cases "preferred_alts le x = carrier")
      case False
      with x have "preferred_alts le x \<in> pref_classes carrier le"
        unfolding pref_classes_def by (intro DiffI imageI) simp_all
      with A show ?thesis by simp
    next
      case True
      from assms have "measure_pmf.prob p carrier = 1" "measure_pmf.prob q carrier = 1"
        by (auto simp: measure_pmf.prob_eq_1 lotteries_on_def AE_measure_pmf_iff)
      with True show ?thesis by simp
    qed
  qed (insert assms, simp_all)
qed

end

lemma (in strategyproof_an_sds) strategyproof':
  assumes wf: "is_pref_profile R" "total_preorder_on alts Ri'" and i: "i \<in> agents"
  shows   "(\<exists>A\<in>pref_classes alts (R i). lottery_prob (sds (R(i := Ri'))) A <
                        lottery_prob (sds R) A) \<or>
           (\<forall>A\<in>pref_classes alts (R i). lottery_prob (sds (R(i := Ri'))) A =
                        lottery_prob (sds R) A)"
proof -
  from wf(1) interpret R: pref_profile_wf agents alts R .
  from i interpret total_preorder_on alts "R i" by simp
  from assms have "\<not> manipulable_profile R i Ri'" by (intro strategyproof)
  moreover from wf i have "sds R \<in> lotteries" "sds (R(i := Ri')) \<in> lotteries"
    by (simp_all add: sds_wf)
  ultimately show ?thesis
    by (fastforce simp: manipulable_profile_def strongly_preferred_def
                        SD_iff_pref_classes not_le not_less)
qed

lemma pref_classes_lists_aux_finite: 
  "A \<in> pref_classes_lists_aux acc xss \<Longrightarrow> finite acc \<Longrightarrow> (\<And>A. A \<in> set xss \<Longrightarrow> finite A)
      \<Longrightarrow> finite A"
  by (induction acc xss rule: pref_classes_lists_aux.induct) auto

lemma strategyproof_aux:
  assumes wf: "prefs_from_table_wf agents alts xss1" "R1 = prefs_from_table xss1"
              "prefs_from_table_wf agents alts xss2" "R2 = prefs_from_table xss2"
  assumes sds: "strategyproof_an_sds agents alts sds" and i: "i \<in> agents" and j: "j \<in> agents"
  assumes eq:  "R1(i := R2 j) = R2" "the (map_of xss1 i) = xs" 
               "pref_classes_lists_aux (hd xs) (tl xs) = ps"
  shows   "(\<exists>A\<in>ps. (\<Sum>x\<in>A. pmf (sds R2) x) < (\<Sum>x\<in>A. pmf (sds R1) x)) \<or>
           (\<forall>A\<in>ps. (\<Sum>x\<in>A. pmf (sds R2) x) = (\<Sum>x\<in>A. pmf (sds R1) x))"
proof -
  from sds interpret strategyproof_an_sds agents alts sds .
  let ?Ri' = "R2 j"
  from wf j have wf': "is_pref_profile R1" "total_preorder_on alts ?Ri'"
    by (auto intro: pref_profile_from_tableI pref_profile_wf.prefs_wf'(1))

  from wf(1) i have "i \<in> set (map fst xss1)" by (simp add: prefs_from_table_wf_def)
  with prefs_from_table_wfD(3)[OF wf(1)] eq
    have "xs \<in> set (map snd xss1)" by force
  note xs = prefs_from_table_wfD(2)[OF wf(1)] prefs_from_table_wfD(5,6)[OF wf(1) this]

  {
    fix p A assume A: "A \<in> pref_classes_lists_aux (hd xs) (tl xs)"
    from xs have "xs \<noteq> []" by auto
    with xs have "finite A"
      by (intro pref_classes_lists_aux_finite[OF A])
         (auto simp: is_finite_weak_ranking_def list.set_sel)
    hence "lottery_prob p A = (\<Sum>x\<in>A. pmf p x)"
      by (rule measure_measure_pmf_finite)
  } note A = this

  from strategyproof'[OF wf' i] eq have
    "(\<exists>A\<in>pref_classes alts (R1 i). lottery_prob (sds R2) A < lottery_prob (sds R1) A) \<or>
     (\<forall>A\<in>pref_classes alts (R1 i). lottery_prob (sds R2) A = lottery_prob (sds R1) A)"
    by simp
  also from wf eq i have "R1 i = of_weak_ranking xs"
    by (simp add: prefs_from_table_map_of)
  also from xs have "pref_classes alts (of_weak_ranking xs) = pref_classes_lists_aux (hd xs) (tl xs)"
    unfolding is_finite_weak_ranking_def by (intro eval_pref_classes_of_weak_ranking) simp_all
  finally show ?thesis by (simp add: A eq)
qed

lemma strategyproof_aux':
  assumes wf: "prefs_from_table_wf agents alts xss1" "R1 \<equiv> prefs_from_table xss1"
              "prefs_from_table_wf agents alts xss2" "R2 \<equiv> prefs_from_table xss2"
  assumes sds: "strategyproof_an_sds agents alts sds" and i: "i \<in> agents" and j: "j \<in> agents"
  assumes perm: "list_permutes ys alts"
  defines "\<sigma> \<equiv> permutation_of_list ys" and "\<sigma>' \<equiv> inverse_permutation_of_list ys"
  defines "xs \<equiv> the (map_of xss1 i)"
  defines xs': "xs' \<equiv> map ((`) \<sigma>) (the (map_of xss2 j))"
  defines "Ri' \<equiv> of_weak_ranking xs'"
  assumes distinct_ps: "\<forall>A\<in>ps. distinct A"
  assumes eq:  "mset (map snd xss1) - {#the (map_of xss1 i)#} + {#xs'#} =
                  mset (map (map ((`) \<sigma>) \<circ> snd) xss2)"
               "pref_classes_lists_aux (hd xs) (tl xs) = set ` ps" 
  shows   "list_permutes ys alts \<and> 
             ((\<exists>A\<in>ps. (\<Sum>x\<leftarrow>A. pmf (sds R2) (\<sigma>' x)) < (\<Sum>x\<leftarrow>A. pmf (sds R1) x)) \<or>
              (\<forall>A\<in>ps. (\<Sum>x\<leftarrow>A. pmf (sds R2) (\<sigma>' x)) = (\<Sum>x\<leftarrow>A. pmf (sds R1) x)))"
            (is "_ \<and> ?th")
proof
  from perm have perm': "\<sigma> permutes alts" by (simp add: \<sigma>_def)
  from sds interpret strategyproof_an_sds agents alts sds .
  from wf(3) j have "j \<in> set (map fst xss2)" by (simp add: prefs_from_table_wf_def)
  with prefs_from_table_wfD(3)[OF wf(3)] 
    have xs'_aux: "the (map_of xss2 j) \<in> set (map snd xss2)" by force
  with wf(3) have xs'_aux': "is_finite_weak_ranking (the (map_of xss2 j))"
    by (auto simp: prefs_from_table_wf_def)
  hence *: "is_weak_ranking xs'" unfolding xs'
    by (intro is_weak_ranking_map_inj permutes_inj_on[OF perm'])
       (auto simp add: is_finite_weak_ranking_def)
  moreover from * xs'_aux' have "is_finite_weak_ranking xs'"
    by (auto simp: xs' is_finite_weak_ranking_def)
  moreover from prefs_from_table_wfD(5)[OF wf(3) xs'_aux] 
    have "\<Union>(set xs') = alts" unfolding xs' 
    by (simp add: image_Union [symmetric] permutes_image[OF perm'])
  ultimately have wf_xs': "is_weak_ranking xs'" "is_finite_weak_ranking xs'" "\<Union>(set xs') = alts"
    by (simp_all add: is_finite_weak_ranking_def)
  from this wf j have wf': "is_pref_profile R1" "total_preorder_on alts Ri'" 
                      "is_pref_profile R2" "finite_total_preorder_on alts Ri'"
    unfolding Ri'_def by (auto intro: pref_profile_from_tableI pref_profile_wf.prefs_wf'(1)
                                 total_preorder_of_weak_ranking)

 interpret R1: pref_profile_wf agents alts R1 by fact
 interpret R2: pref_profile_wf agents alts R2 by fact

  from wf(1) i have "i \<in> set (map fst xss1)" by (simp add: prefs_from_table_wf_def)
  with prefs_from_table_wfD(3)[OF wf(1)] eq(2)
    have "xs \<in> set (map snd xss1)" unfolding xs_def by force
  note xs = prefs_from_table_wfD(2)[OF wf(1)] prefs_from_table_wfD(5,6)[OF wf(1) this]

  from wf i wf' wf_xs' xs eq 
    have eq': "anonymous_profile (R1(i := Ri')) = image_mset (map ((`) \<sigma>)) (anonymous_profile R2)"
    by (subst R1.anonymous_profile_update)
       (simp_all add: Ri'_def weak_ranking_of_weak_ranking mset_map multiset.map_comp xs_def
          anonymise_prefs_from_table prefs_from_table_map_of)

  {
    fix p A assume A: "A \<in> pref_classes_lists_aux (hd xs) (tl xs)"
    from xs have "xs \<noteq> []" by auto
    with xs have "finite A"
      by (intro pref_classes_lists_aux_finite[OF A])
         (auto simp: is_finite_weak_ranking_def list.set_sel)
    hence "lottery_prob p A = (\<Sum>x\<in>A. pmf p x)"
      by (rule measure_measure_pmf_finite)
  } note A = this

  from strategyproof'[OF wf'(1,2) i] eq' have
    "(\<exists>A\<in>pref_classes alts (R1 i). lottery_prob (sds (R1(i := Ri'))) A < lottery_prob (sds R1) A) \<or>
     (\<forall>A\<in>pref_classes alts (R1 i). lottery_prob (sds (R1(i := Ri'))) A = lottery_prob (sds R1) A)"
    by simp
  also from eq' i have "sds (R1(i := Ri')) = map_pmf \<sigma> (sds R2)"
    unfolding \<sigma>_def by (intro sds_anonymous_neutral permutation_of_list_permutes perm wf'
                              pref_profile_wf.wf_update eq)
  also from wf eq i have "R1 i = of_weak_ranking xs"
    by (simp add: prefs_from_table_map_of xs_def)
  also from xs have "pref_classes alts (of_weak_ranking xs) = pref_classes_lists_aux (hd xs) (tl xs)"
    unfolding is_finite_weak_ranking_def by (intro eval_pref_classes_of_weak_ranking) simp_all
  finally have "(\<exists>A\<in>ps. (\<Sum>x\<leftarrow>A. pmf (map_pmf \<sigma> (sds R2)) x) < (\<Sum>x\<leftarrow>A. pmf (sds R1) x)) \<or>
                (\<forall>A\<in>ps. (\<Sum>x\<leftarrow>A. pmf (map_pmf \<sigma> (sds R2)) x) = (\<Sum>x\<leftarrow>A. pmf (sds R1) x))"
    using distinct_ps
    by (simp add: A eq sum.distinct_set_conv_list del: measure_map_pmf)
  also from perm' have "pmf (map_pmf \<sigma> (sds R2)) = (\<lambda>x. pmf (sds R2) (inv \<sigma> x))"
    using pmf_map_inj'[of \<sigma> _ "inv \<sigma> x" for x]
    by (simp add: fun_eq_iff permutes_inj permutes_inverses)
  also from perm have "inv \<sigma> = \<sigma>'" unfolding \<sigma>_def \<sigma>'_def
    by (rule inverse_permutation_of_list_correct [symmetric])
  finally show ?th .
qed fact+

ML_file \<open>randomised_social_choice.ML\<close>
ML_file \<open>sds_automation.ML\<close>

end
