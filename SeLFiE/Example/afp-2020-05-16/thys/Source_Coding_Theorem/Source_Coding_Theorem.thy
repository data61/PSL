(* Title:       One Part of Shannon's Source Coding Theorem
   Author:      Quentin Hibon <qh225@cl.cam.ac.uk>, Lawrence Paulson <lp15@cam.ac.uk>, 2014
   Maintainer:  Quentin Hibon <qh225@cl.cam.ac.uk>
*)

theory Source_Coding_Theorem
imports "HOL-Probability.Information"
begin
section\<open>Basic types\<close>

type_synonym bit = bool
type_synonym bword = "bit list"
type_synonym letter = nat
type_synonym 'b word = "'b list"

type_synonym 'b encoder = "'b word \<Rightarrow> bword"
type_synonym 'b decoder = "bword \<Rightarrow> 'b word option"

section\<open>Locale for the source coding theorem\<close>
locale source_code = information_space +
  fixes fi :: "'b \<Rightarrow> real"
  fixes X :: "'a \<Rightarrow> 'b"

  assumes distr_i: "simple_distributed M X fi"
  assumes b_val: "b = 2"

  fixes enc::"'b encoder"
  fixes dec::"'b decoder"
  assumes real_code:
  "dec (enc x) = Some x"
  "enc w = [] \<longleftrightarrow> w = []"
  "x \<noteq> [] \<longrightarrow> enc x = enc [hd x] @ enc (tl x)"

section\<open>Source coding theorem, direct: the entropy is a lower bound of the code rate\<close>
context source_code
begin
subsection\<open>The letter set\<close>

definition L :: "'b set" where
  "L \<equiv> X ` space M"

lemma fin_L: "finite L"
    using L_def distr_i
    by auto

lemma emp_L: "L \<noteq> {}"
    using L_def subprob_not_empty
    by auto

subsection\<open>Codes and words\<close>

abbreviation real_word :: "'b word \<Rightarrow> bool" where
  "real_word w \<equiv> (set w \<subseteq> L)"

abbreviation k_words :: "nat \<Rightarrow> ('b word) set" where
  "k_words k \<equiv> {w. length w = k \<and> real_word w}"

lemma rw_tail:
  assumes "real_word w"
shows "w = [] \<or> real_word (tl w)"
    by (meson assms list.set_sel(2) subset_code(1))

definition code_word_length :: "'e encoder \<Rightarrow> 'e \<Rightarrow> nat" where
  "code_word_length e l = length (e [l])"

abbreviation cw_len :: "'b \<Rightarrow> nat" where
  "cw_len l \<equiv> code_word_length enc l"

definition code_rate :: "'e encoder \<Rightarrow> ('a \<Rightarrow> 'e) \<Rightarrow> real" where
  "code_rate e Xo = expectation (\<lambda>a. (code_word_length e ((Xo) a)))"

lemma fi_pos: "i\<in> L \<Longrightarrow> 0 \<le> fi i"
    using simple_distributed_nonneg[OF distr_i] L_def by auto

lemma (in prob_space) simp_exp_composed:
  assumes X: "simple_distributed M X Px"
shows "expectation (\<lambda>a. f (X a)) = (\<Sum>x \<in> X`space M. f x * Px x)"
  using distributed_integral[OF simple_distributed[OF X], of f]
    simple_distributed_nonneg[OF X]
    lebesgue_integral_count_space_finite[OF simple_distributed_finite[OF X], of "\<lambda>x. f x * Px x"]
  by (simp add:  ac_simps)

lemma cr_rw:
  "code_rate enc X = (\<Sum>i \<in> X ` space M. fi i * cw_len i)"
    using simp_exp_composed[OF distr_i, of "cw_len"]
    by (simp add: mult.commute code_rate_def)

abbreviation cw_len_concat :: "'b word \<Rightarrow> nat" where
  "cw_len_concat w \<equiv> foldr (\<lambda>x s. (cw_len x) + s) w 0"

lemma cw_len_length: "cw_len_concat w = length (enc w)"
proof (induction w)
    case Nil
    show ?case using real_code by simp
    case (Cons a w)
    have "cw_len_concat (a # w) = cw_len a + cw_len_concat w" by simp
    thus ?case using code_word_length_def real_code Cons
      by (metis length_append list.distinct(1) list.sel(1) list.sel(3))
qed

lemma maj_fold:
  assumes "\<And>l. l\<in>L \<Longrightarrow> f l \<le> bound"
  assumes "real_word w"
shows "foldr (\<lambda>x s. f x + s) w 0 \<le> length w * bound"
    using assms
    by(induction w) (simp,fastforce)

definition max_len :: "nat" where
  "max_len = Max ((\<lambda>x. cw_len x) ` L)"

lemma max_cw:
  "l \<in> L \<Longrightarrow> cw_len l \<le> max_len"
    by (simp add: max_len_def fin_L)

subsection\<open>Related to the Kraft theorem\<close>
definition \<K> :: "real" where
  "\<K> = (\<Sum>i\<in>L. 1 / b ^ (cw_len i))"

lemma pos_cw_len: "0 < 1 / b ^ cw_len i" using b_gt_1 by simp

lemma \<K>_pos: "0 < \<K>"
    using emp_L fin_L pos_cw_len sum_pos \<K>_def
    by metis

lemma \<K>_pow: "\<K> = (\<Sum>i\<in>L. 1 / b powr cw_len i)"
    using powr_realpow b_gt_1
    by (simp add: \<K>_def)

lemma k_words_rel:
  "k_words (Suc k) = {w. (hd w \<in> L \<and> tl w \<in> k_words k \<and> w \<noteq> [])}"
proof
    fix k
    show "k_words (Suc k) \<subseteq> {w. (hd w \<in> L \<and> tl w \<in> k_words k \<and> w \<noteq> [] )}" (is "?l \<subseteq> ?r")
  proof
      fix w
      assume w_kw: "w \<in> k_words (Suc k)"
      hence "real_word w" by simp
      hence "hd w \<in> L"
        by (metis (mono_tags) w_kw hd_in_set list.size(3) mem_Collect_eq nat.distinct(1) subset_code(1))
      moreover have "length w = Suc k" using w_kw by simp
      moreover hence "w \<noteq> []" by auto
      moreover have "real_word (tl w)" using \<open>real_word w\<close> calculation(3) rw_tail by auto
      ultimately show "w \<in> ?r" using w_kw by simp
  qed
next
    fix k
    show "k_words (Suc k) \<supseteq> {w. (hd w \<in> L \<and> tl w \<in> k_words k \<and> w \<noteq> [])}"
  proof
      fix w
      assume asm: "w \<in> {w. hd w \<in> L \<and> tl w \<in> {w. length w = k \<and> real_word w} \<and> w \<noteq> []}"
      hence "hd w \<in> L \<and> length (tl w) = k \<and> real_word (tl w)" by simp
      hence "real_word w"
        by (metis empty_iff insert_subset list.collapse list.set(1) set_simps(2) subsetI)
      moreover hence "length w = Suc k" using asm by auto
      ultimately show "w \<in> k_words (Suc k)" by simp
  qed
qed

lemma bij_k_words:
shows "bij_betw (\<lambda>wi. Cons (fst wi) (snd wi)) (L \<times> k_words k) (k_words (Suc k))"
    unfolding bij_betw_def
proof
    fix k
    let ?f = "(\<lambda>wi. Cons (fst wi) (snd wi))"
    let ?S = "L \<times> (k_words k)"
    let ?T = "k_words (Suc k)"
    show "inj_on ?f ?S" by (simp add: inj_on_def)
    show "?f`?S = ?T"
  proof (rule ccontr)
      assume "?f ` ?S \<noteq> ?T"
      hence "\<exists>w. w\<in> ?T \<and> w \<notin> ?f`?S" by auto
      then obtain w where asm: "w\<in> ?T \<and> w \<notin> ?f`?S" by blast
      hence "w = ?f (hd w,tl w)" using k_words_rel by simp
      moreover have "(hd w,tl w) \<in> ?S" using k_words_rel asm by simp
      ultimately have "w \<in> ?f`?S" by blast
      thus "False" using asm by simp
  qed
qed

lemma finite_k_words: "finite (k_words k)"
proof (induct k)
    case 0
    show ?case by simp
    case (Suc n)
    thus ?case using bij_k_words bij_betw_finite fin_L by blast
qed

lemma cartesian_product:
  fixes f::"('c \<Rightarrow> real)"
  fixes g::"('d \<Rightarrow> real)"
  assumes "finite A"
  assumes "finite B"
shows "(\<Sum>b\<in>B. g b) * (\<Sum>a\<in>A. f a) = (\<Sum>ab\<in>A\<times>B. f (fst ab) * g (snd ab))"
    using bilinear_times bilinear_sum[where h="(\<lambda>x y. x * y)" and f="f" and g="g"] assms
    by (metis (erased, lifting) sum.cong split_beta' Groups.ab_semigroup_mult_class.mult.commute)

lemma \<K>_power:
shows "\<K>^k = (\<Sum>w \<in> (k_words k). 1 / b^(cw_len_concat w))"
proof (induct k)
    case 0
    have "k_words 0 = {[]}" by auto
    thus ?case by simp
next
    case (Suc n)
    have " \<K> ^Suc n = \<K> ^n * \<K> " by simp
    also have "\<dots> = (\<Sum>w \<in> k_words n. 1 / b^cw_len_concat w) * (\<Sum>i\<in>L. 1 / b^cw_len i)"
      using Suc.hyps \<K>_def by auto
    also have "\<dots> = (\<Sum>wi \<in> L \<times> k_words n. 1/b^cw_len (fst wi) * (1 / b^cw_len_concat (snd wi)))"
      using fin_L finite_k_words cartesian_product
      by blast
    also have "\<dots> = (\<Sum>wi \<in> L \<times> k_words n. 1 / b^(cw_len_concat (snd wi) + cw_len (fst wi)))"
      by (metis (no_types, lifting) power_add add.commute power_one_over)
    also have "\<dots> = (\<Sum>wi \<in> L \<times> k_words n. 1 / b^cw_len_concat (fst wi # snd wi))"
      by (metis (erased, lifting) add.commute comp_apply foldr.simps(2))
    also have "\<dots> = (\<Sum>w \<in> (k_words (Suc n)). 1 / b^(cw_len_concat w))"
      using bij_k_words sum.reindex_bij_betw by fastforce
    finally show ?case by simp
qed

lemma bound_len_concat:
shows "w \<in> k_words k \<Longrightarrow> cw_len_concat w \<le> k * max_len"
    using max_cw maj_fold by blast

subsection\<open>Inequality of the kraft sum (source coding theorem, direct)\<close>
subsubsection\<open>Sum manipulation lemmas and McMillan theorem\<close>

lemma sum_vimage_proof:
  fixes g::"nat \<Rightarrow> real"
  assumes "\<And>w. f w < bd"
shows "finite S \<Longrightarrow> (\<Sum>w\<in>S. g (f w)) = (\<Sum> m=0..<bd. (card ((f-`{m}) \<inter> S) )* g m)"
(is "_ \<Longrightarrow> _ = (\<Sum> m=0..<bd. ?ff m S)")
proof (induct S rule: finite_induct)
    case empty
    show ?case by simp
next
    case (insert x F)
    let ?rr = "(\<Sum>m = 0..<bd. ?ff m (insert x F))"
    have "(f x) \<in> {0..<bd}" using assms by simp
    hence "\<And>h::(nat \<Rightarrow> real). (\<Sum>m=0..<bd. h m) = (\<Sum>y\<in>({0..<bd} - {f x}).h y) + h (f x)"
      by (metis diff_add_cancel finite_atLeastLessThan sum_diff1)
    moreover hence
    "(\<Sum>m = 0..<bd. ?ff m (insert x F))
    = (\<Sum>m\<in>{0..<bd} - {f x}. ?ff m (insert x F)) + card (f -` {f x} \<inter> F) * g (f x) + g (f x)"
      by (simp add: semiring_normalization_rules(2), simp add: insert)
    ultimately have "(\<Sum>m = 0..<bd. ?ff m (insert x F)) = (\<Sum>m\<in>{0..<bd}. ?ff m F) + g (f x)"
      by fastforce
    thus ?case using insert by simp
qed

lemma sum_vimage:
  fixes g::"nat \<Rightarrow> real"
  assumes bounded: "\<And>w. w \<in> S \<Longrightarrow> f w < bd" and "0 < bd"
  assumes finite: "finite S"
shows "(\<Sum>w\<in>S. g (f w)) = (\<Sum> m=0..<bd. (card ((f-`{m}) \<inter> S) ) * g m)"
(is "?s1 = ?s2")
proof -
    let ?ff = "(\<lambda>x. if x\<in>S then f x else 0)"
    let ?ss1 = "(\<Sum>w\<in>S. g (?ff w))"
    let ?ss2 = "(\<Sum> m=0..<bd. (card ((?ff-`{m}) \<inter> S) ) * g m)"
    have "?s1 =?ss1" by simp
    moreover have"\<And>m. ?ff -`{m} \<inter> S = f-`{m} \<inter> S" by auto
    moreover hence "?s2 = ?ss2" by simp
    moreover have "\<And>w . ?ff w < bd" using assms by simp
    moreover hence "?ss1 = ?ss2" using sum_vimage_proof[of "?ff"] finite by blast
    ultimately show "?s1 = ?s2" by metis
qed

lemma \<K>_rw:
  "(\<Sum>w \<in> (k_words k). 1 / b^(cw_len_concat w)) = (\<Sum>m=0..<Suc (k*max_len). card (k_words k \<inter>
((cw_len_concat) -` {m})) * (1 / b^m))" (is "?L = ?R")
proof -
    have "\<And>w. w \<in> k_words k \<Longrightarrow> cw_len_concat w < Suc ( k * max_len)"
      by (simp add: bound_len_concat le_imp_less_Suc)
    moreover have
    "?R = (\<Sum>m = 0..<Suc (k * max_len).
  (card (cw_len_concat -` {m} \<inter> k_words k)) * (1 / b ^ m))"
      by (metis Int_commute)
    moreover have "0 < Suc (k*max_len)" by simp
    ultimately show ?thesis
      using finite_k_words
    sum_vimage[where f="cw_len_concat" and g = "\<lambda>i. 1/ (b^i)"]
      by fastforce
qed

definition set_of_k_words_length_m :: "nat \<Rightarrow> nat \<Rightarrow> 'b word set" where
  "set_of_k_words_length_m k m = {xk. xk \<in> k_words k} \<inter> (cw_len_concat)-`{m}"

lemma am_inj_code: "inj_on enc ((cw_len_concat)-`{m})" (is "inj_on _ ?s")
  using inj_on_def[of enc "?s"] real_code
  by (metis option.inject)

lemma img_inc: "enc`cw_len_concat-`{m} \<subseteq> {bl. length bl = m}" using cw_len_length by auto

lemma bool_lists_card: "card {bl::bool list. length bl = m} = b^m"
 using card_lists_length_eq[of "UNIV::bool set"]
  by (simp add: b_val)

lemma bool_list_fin: "finite {bl::bool list. length bl = m}"
  using finite_lists_length_eq[of "UNIV::bool set"]
  by (simp add: b_val)

lemma set_of_k_words_bound:
shows "card (set_of_k_words_length_m k m) \<le> b^m" (is "?c \<le> ?b")
proof -
    have card_w_len_m_bound: "card (cw_len_concat-`{m}) \<le> b^m"
      by (metis (no_types, lifting) am_inj_code bool_list_fin bool_lists_card card_image card_mono
    img_inc of_nat_le_iff)
    have "set_of_k_words_length_m k m \<subseteq> (cw_len_concat)-`{m}"
      by (simp add: set_of_k_words_length_m_def)
    hence "card (set_of_k_words_length_m k m) \<le> card ((cw_len_concat)-`{m})"
      by (metis (no_types, lifting) am_inj_code bool_list_fin card.infinite card_0_eq
    card_image card_mono empty_iff finite_subset img_inc inf_img_fin_dom)
    thus ?thesis using card_w_len_m_bound by simp
qed

lemma empty_set_k_words:
  assumes "0 < k"
shows "set_of_k_words_length_m k 0 = {}"
proof(rule ccontr)
    assume "\<not> set_of_k_words_length_m k 0 = {}"
    hence "\<exists>x. x \<in> set_of_k_words_length_m k 0" by auto
    then obtain x where x_def: "x \<in> set_of_k_words_length_m k 0" by auto
    hence "x \<noteq> []" unfolding set_of_k_words_length_m_def using assms by auto
    moreover have "cw_len_concat (hd x#tl x) = cw_len_concat (tl x) + cw_len (hd x)"
      by (metis add.commute comp_apply foldr.simps(2))
    moreover have "enc [(hd x)] \<noteq> []" using assms real_code by blast
    moreover hence "0 < cw_len (hd x)" unfolding code_word_length_def by simp
    ultimately have "x \<notin> set_of_k_words_length_m k 0" by (simp add:set_of_k_words_length_m_def)
    thus "False" using x_def by simp
qed

lemma \<K>_rw2:
  assumes "0 < k"
shows "(\<Sum>m=0..<Suc (k * max_len). card (set_of_k_words_length_m k m)/ b^m) \<le> (k * max_len)"
proof -
    have
    "(\<Sum>m=1..<Suc (k * max_len). card (set_of_k_words_length_m k m) / b^m)
    \<le> (\<Sum>m=1..<Suc(k * max_len). b^m / b^m)"
      using set_of_k_words_bound b_val
    Groups_Big.sum_mono[of "{1..<Suc(k * max_len)}"
    "(\<lambda>m. (card (set_of_k_words_length_m k m))/b^m)" "\<lambda>m. b^m /b^m"]
      by simp
    moreover have"(\<Sum>m=1..<Suc(k * max_len). b^m / b^m) = (\<Sum>m=1..<Suc(k *max_len). 1)"
      using b_gt_1 by simp
    moreover have "(\<Sum>m=1..<Suc(k * max_len). 1) = (k * max_len)"
      by simp
    ultimately have
    "(\<Sum>m = 1..<Suc (k * max_len). card (set_of_k_words_length_m k m) / b ^ m) \<le> k * max_len"
      by (metis One_nat_def card_atLeastLessThan card_eq_sum diff_Suc_Suc real_of_card)
    thus ?thesis using empty_set_k_words assms
      by (simp add: sum_shift_lb_Suc0_0_upt split: if_split_asm)
qed

lemma \<K>_power_bound :
  assumes "0 < k"
shows " \<K>^k \<le> k * max_len"
    using assms \<K>_power \<K>_rw \<K>_rw2
    by (simp add: set_of_k_words_length_m_def)

theorem McMillan :
shows "\<K> \<le> 1"
proof -
    have ineq: "\<And>k. 0 < k \<Longrightarrow> \<K> \<le> root k k * root k max_len"
      using \<K>_pos \<K>_power_bound
      by (metis (no_types, hide_lams) not_less of_nat_0_le_iff of_nat_mult power_strict_mono real_root_mult real_root_pos_pos_le real_root_pos_unique real_root_power)
    hence "0 < max_len \<Longrightarrow> (\<lambda>k. root k k * root k max_len) \<longlonglongrightarrow> 1"
      by (auto intro!: tendsto_eq_intros LIMSEQ_root LIMSEQ_root_const)
    moreover have "\<forall>n\<ge>1. \<K> \<le> root n n * root n max_len"
      using ineq by simp
    moreover have "max_len = 0 \<Longrightarrow> \<K> \<le> 1" using ineq by fastforce
    ultimately show " \<K> \<le> 1" using LIMSEQ_le_const by blast
qed

lemma entropy_rw: "\<H>(X) = -(\<Sum>i \<in> L. fi i * log b (fi i))"
    using entropy_simple_distributed[OF distr_i]
    by (simp add: L_def)

subsubsection\<open>Technical lemmas about the logarithm\<close>
lemma log_mult_ext3:
  "0 \<le> x \<Longrightarrow> 0 < y \<Longrightarrow> 0 < z \<Longrightarrow> x * log b (x*y*z) = x * log b (x*y) + x * log b z"
    by(cases "x=0")(simp add: log_mult_eq abs_of_pos distrib_left less_eq_real_def)+

lemma log_mult_ext2:
  "0 \<le> x \<Longrightarrow> 0 < y \<Longrightarrow> x * log b (x*y) = x * log b x + x * log b y"
    using log_mult_ext3[where y=1] by simp

subsubsection \<open>KL divergence and properties\<close>
definition KL_div ::"'b set \<Rightarrow> ('b \<Rightarrow> real) \<Rightarrow> ('b \<Rightarrow> real) \<Rightarrow> real" where
  "KL_div S a d = (\<Sum> i \<in> S. a i * log b (a i / d i))"

lemma KL_div_mul:
  assumes "0 < d" "d \<le> 1"
  assumes "\<And>i. i\<in>S \<Longrightarrow> 0 \<le> a i"
  assumes "\<And>i. i\<in>S \<Longrightarrow> 0 < e i"
shows "KL_div S a e \<ge> KL_div S a (\<lambda>i. e i / d)"
    unfolding KL_div_def
proof -
    {
    fix i
    assume "i\<in>S"
    hence "a i / (e i / d) \<le> a i / e i" using assms
      by (metis (no_types) div_by_1 frac_le less_imp_triv not_less)
    hence "log b (a i / (e i / d)) \<le> log b (a i / e i)" using assms(1)
      by (metis (full_types) b_gt_1 divide_divide_eq_left inverse_divide le_less_linear log_le
    log_neg_const order_refl times_divide_eq_right zero_less_mult_iff)
    }
    thus "(\<Sum>i\<in>S. a i * log b (a i / (e i / d))) \<le> (\<Sum>i\<in>S. a i * log b (a i / e i))"
      by (meson mult_left_mono assms sum_mono)
qed

lemma KL_div_pos:
  fixes a e::"'b \<Rightarrow> real"
  assumes fin: "finite S"
  assumes nemp: "S \<noteq> {}"
  assumes non_null: "\<And>i. i\<in>S \<Longrightarrow> 0 < a i" "\<And>i. i\<in> S \<Longrightarrow> 0 < e i"
  assumes sum_a_one: "(\<Sum> i \<in> S. a i) = 1"
  assumes sum_c_one: "(\<Sum> i \<in> S. e i) = 1"
shows "0 \<le> KL_div S a e"
    unfolding KL_div_def
proof -
    let ?f = "\<lambda>i. e i / a i"
    have f_pos: "\<And>i. i\<in>S \<Longrightarrow> 0 < ?f i"
      using non_null
      by simp
    have a_pos: "\<And>i. i\<in> S \<Longrightarrow> 0 \<le> a i"
      using non_null
      by (simp add: order.strict_implies_order)
    have "- log b (\<Sum>i\<in>S. a i * e i / a i) \<le> (\<Sum>i\<in>S. a i * - log b (e i / a i))"
      using convex_on_sum[OF fin nemp  minus_log_convex[OF b_gt_1] convex_real_interval(3)
                             sum_a_one a_pos, of "\<lambda>i. e i / a i"] f_pos by simp
    also have "-log b (\<Sum>i\<in>S. a i * e i / a i) = -log b (\<Sum>i\<in>S. e i)"
  proof -
      from non_null(1) have "\<And>i. i \<in> S \<Longrightarrow> a i * e i / a i = e i" by force
      thus ?thesis by simp
  qed
    finally have "0 \<le> (\<Sum>i\<in>S. a i * - log b (e i / a i))"
      by (simp add: sum_c_one)
    thus "0 \<le> (\<Sum>i\<in>S. a i * log b (a i / e i))"
      using b_gt_1 log_divide non_null
      by simp
qed

lemma KL_div_pos_emp:
  "0 \<le> KL_div {} a e" by (simp add: KL_div_def)

lemma KL_div_pos_gen:
  fixes a d::"'b \<Rightarrow> real"
  assumes fin: "finite S"
  assumes non_null: "\<And>i. i\<in>S \<Longrightarrow> 0 < a i" "\<And>i. i\<in> S \<Longrightarrow> 0 < d i"
  assumes sum_a_one: "(\<Sum> i \<in> S. a i) = 1"
  assumes sum_d_one: "(\<Sum> i \<in> S. d i) = 1"
shows "0 \<le> KL_div S a d"
    using KL_div_pos KL_div_pos_emp assms by metis

theorem KL_div_pos2:
  fixes a d::"'b \<Rightarrow> real"
  assumes fin: "finite S"
  assumes non_null: "\<And>i. i\<in>S \<Longrightarrow> 0 \<le> a i" "\<And>i. i\<in> S \<Longrightarrow> 0 < d i"
  assumes sum_a_one: "(\<Sum> i \<in> S. a i) = 1"
  assumes sum_c_one: "(\<Sum> i \<in> S. d i) = 1"
shows "0 \<le> KL_div S a d"
proof -
    have "S = (S \<inter> {i. 0 < a i}) \<union> (S \<inter> {i. 0 = a i})" using non_null(1) by fastforce
    moreover have "(S \<inter> {i. 0 < a i}) \<inter> (S \<inter> {i. 0 = a i}) = {}" by auto
    ultimately have
    eq: "KL_div S a d = KL_div (S \<inter> {i. 0 < a i}) a d + KL_div (S \<inter> {i. 0 = a i}) a d"
      unfolding KL_div_def
      by (metis (mono_tags, lifting) fin finite_Un sum.union_disjoint)
    have "KL_div (S \<inter> {i. 0 = a i}) a d = 0" unfolding KL_div_def by simp
    hence "KL_div S a d = KL_div (S \<inter> {i. 0 < a i}) a d" using eq by simp
    moreover have "0 \<le> KL_div (S \<inter> {i. 0 < a i}) a d"
  proof(cases "(S \<inter> {i. 0 < a i}) = {}")
      case True
      thus ?thesis unfolding KL_div_def by simp
  next
      case False
      let ?c = "\<lambda>i. d i / (\<Sum>j \<in>(S \<inter> {i. 0 < a i}). d j)"
      have 1: "(\<And>i. i \<in> S \<inter> {i. 0 < a i} \<Longrightarrow> 0 < a i)" by simp
      have 2: "(\<And>i. i \<in> S \<inter> {i. 0 < a i} \<Longrightarrow> 0 < ?c i)"
        by (metis False IntD1 divide_pos_pos fin finite_Int non_null(2) sum_pos)
      have 3: "(\<Sum>i\<in> (S \<inter> {i. 0 < a i}). a i) = 1"
        using sum.cong[of S, of S, of "(\<lambda>x. if x \<in> {i. 0 < a i} then a x else 0)", of a]
      sum.inter_restrict[OF fin, of a] non_null(1) sum_a_one
        by fastforce
      have "(\<Sum>i\<in>S \<inter> {j. 0 < a j}. ?c i) = (\<Sum>i\<in>S \<inter> {j. 0 < a j}. d i) / (\<Sum>i\<in>S \<inter> {j. 0 < a j}. d i)"
        by (metis sum_divide_distrib)
      hence 5: "(\<Sum>i\<in>S \<inter> {j. 0 < a j}. ?c i) = 1" using 2 False by force
      hence "0 \<le> KL_div (S \<inter> {j. 0 < a j}) a ?c"
        using KL_div_pos_gen[
      OF finite_Int[OF disjI1, of S, of "{j. 0 < a j}"], of a, of ?c
      ] 1 2 3
        by (metis fin)
      have fstdb: "0 < (\<Sum>i\<in>S \<inter> {i. 0 < a i}. d i)" using non_null(2) False
        by (metis Int_Collect fin finite_Int sum_pos)
      have 6: "0 \<le> KL_div (S \<inter> {i. 0 < a i}) a (\<lambda>i. d i / (\<Sum>i\<in>(S \<inter> {i. 0 < a i}). d i))"
        using 2 3 5
        KL_div_pos_gen[
      OF finite_Int[OF disjI1, OF fin], of "{i. 0 < a i}", of "a", of "?c"
      ]
        by simp
      hence
      "KL_div (S \<inter> {j. 0 < a j}) a (\<lambda>i. d i / (\<Sum>i\<in>(S \<inter> {i. 0 < a i}). d i)) \<le> KL_div (S \<inter> {j. 0 < a j}) a d"
        using non_null sum.inter_restrict[OF fin, of d, of "{i. 0 < a i}"]
        sum_mono[of S, of "(\<lambda>x. if x \<in> {i. 0 < a i} then d x else 0)", of d] non_null(2) sum_c_one
        non_null(2) fstdb KL_div_mul
        by force
      moreover have "0 \<le> KL_div (S \<inter> {j. 0 < a j}) a (\<lambda>i. d i / (\<Sum>i\<in>(S \<inter> {i. 0 < a i}). d i))"
        using KL_div_pos_gen[ OF finite_Int[OF disjI1, OF fin]] using 2 3 5 by fastforce
      ultimately show "0 \<le> KL_div (S \<inter> {j. 0 < a j}) a d" by simp
  qed
    ultimately show ?thesis by simp
qed

lemma sum_div_1:
  fixes f::"'b \<Rightarrow> 'c::field"
  assumes "(\<Sum>i\<in>A. f i) \<noteq> 0"
shows "(\<Sum>i\<in>A. f i / (\<Sum>j\<in>A. f j)) = 1"
    by (metis (no_types) assms right_inverse_eq sum_divide_distrib)

theorem rate_lower_bound:
shows "\<H>(X) \<le> code_rate enc X"
proof -
    let ?cr = "code_rate enc X"
    let ?r = "(\<lambda>i. 1 / ((b powr cw_len i) * \<K>))"
    have pos_pi: "\<And>i. i \<in> L \<Longrightarrow> 0 \<le> fi i" using fi_pos by simp
    {
    fix i
    assume "i \<in> L"
    hence
    "fi i * (log b (1 / (1 / b powr (cw_len i))) + log b (fi i))
    = fi i * log b (fi i / (1 / b powr (cw_len i)))"
      using log_mult_ext2 [OF pos_pi, of i] b_gt_1
      by simp (simp add: algebra_simps)
    }
    hence eqpi:
    "\<And>i. i\<in> L \<Longrightarrow> fi i * (log b (1 / (1 / b powr (cw_len i))) + log b (fi i))
    = fi i * log b (fi i / (1 / b powr (cw_len i)))"
      by simp
    have sum_one_L: "(\<Sum> i \<in> L. fi i) = 1"
      using simple_distributed_sum_space[OF distr_i] by (simp add: L_def)
    {
    fix i
    assume "i \<in> L"
    hence h1: "0 \<le> fi i" using pos_pi by blast
    have h2: "0 < \<K> / (1/b powr cw_len i)" using b_gt_1 \<K>_pos by auto
    have h3: "0 < 1 / \<K>" using \<K>_pos by simp
    have
    "fi i * log b (fi i * \<K> / (1/b powr cw_len i) * (1/ \<K>)) =
    fi i * log b (fi i * \<K> / (1/b powr cw_len i)) + fi i * log b (1/ \<K>)"
      using log_mult_ext3[OF h1 h2 h3]
      by (metis times_divide_eq_right)
    } hence big_eq:
    "\<And>i. i \<in> L \<Longrightarrow> fi i * log b (fi i * \<K> / (1/b powr cw_len i) * (1 / \<K>)) =
    fi i * log b (fi i * \<K> / (1/b powr cw_len i)) + fi i * log b (1 / \<K>)"
      by (simp add: inverse_eq_divide)
    have 1: "?cr - \<H>(X) = (\<Sum>i \<in> L. fi i * cw_len i) + (\<Sum>i \<in> L. fi i * log b (fi i))"
      using \<K>_def entropy_rw cr_rw L_def by simp
    also have 2: "(\<Sum>i\<in>L. fi i * cw_len i) = (\<Sum>i \<in> L. fi i * (-log b (1/(b powr (cw_len i)))))"
      using b_gt_1 log_divide by simp
    also have "\<dots> = -1 * (\<Sum>i \<in> L. fi i * (log b (1/(b powr (cw_len i)))))"
      using sum_distrib_left[of "-1" "(\<lambda>i. fi i * (- 1 * log b (1 / b powr (cw_len i))))" L]
      by simp
    finally have
    "?cr - \<H>(X) = -(\<Sum>i \<in> L. fi i * log b (1/b powr cw_len i)) + (\<Sum>i \<in> L. fi i * log b (fi i))"
      by simp
    have "?cr - \<H>(X) = (\<Sum>i \<in> L. fi i * ((log b (1/ (1/(b powr (cw_len i))))) + log b (fi i)))"
      using b_gt_1 1
      by (simp add: distrib_left sum.distrib)
    also have "\<dots> = (\<Sum>i \<in> L. fi i *((log b (fi i / (1/(b powr (cw_len i)))))))"
      using Finite_Cartesian_Product.sum_cong_aux[OF eqpi] by simp
    also from big_eq have
    "\<dots> = (\<Sum>i\<in>L. fi i * (log b (fi i * \<K> / (1 / b powr (cw_len i))))) + (\<Sum>i \<in> L. fi i) * log b (1/ \<K>)"
      using \<K>_pos
      by (simp add: sum_distrib_right sum.distrib)
    also have "\<dots> = (\<Sum>i\<in>L. fi i * (log b (fi i * \<K> / (1 / b powr (cw_len i))))) - log b (\<K>)"
      using \<K>_pos
      by (simp add: log_inverse_eq divide_inverse sum_one_L)
    also have "\<dots> = (\<Sum> i \<in> L. fi i * log b (fi i / ?r i)) - log b (\<K>)"
      by (metis (mono_tags, hide_lams) divide_divide_eq_left divide_divide_eq_right)
    also have "\<dots> = KL_div L fi ?r - log b ( \<K>)"
      using b_gt_1 \<K>_pos log_inverse KL_div_def
      by simp
    also have "\<dots> = KL_div L fi ?r + log b (1 / \<K>)"
      using log_inverse b_val \<K>_pos
      by (simp add: inverse_eq_divide)
    finally have code_ent_kl_log: "?cr - \<H>(X) = KL_div L fi ?r + log b (1 / \<K>)" by simp
    have "(\<Sum>i\<in>L. ?r i) = 1"
      using sum_div_1[of "\<lambda>i. 1 / (b powr (cw_len i))"] \<K>_pos \<K>_pow
      by simp
    moreover have "\<And>i. 0 < ?r i" using b_gt_1 \<K>_pos by simp
    moreover have "(\<Sum>i\<in>L. fi i) = 1" using sum_one_L by simp
    ultimately have "0 \<le> KL_div L fi ?r"
      using KL_div_pos2[OF fin_L fi_pos] by simp
    hence "log b (1 / \<K>) \<le> ?cr - \<H>(X)" using code_ent_kl_log by simp
    moreover from McMillan have "0 \<le> log b (1 / \<K>)"
      using \<K>_pos
      by (simp add: b_gt_1)
    ultimately show ?thesis by simp
qed

end

end
