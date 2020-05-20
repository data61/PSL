(* Title: Fast_Dice_Roll.thy
   Author: Andreas Lochbihler, ETH Zurich *)

subsection \<open>Arbitrary uniform distributions\<close>

theory Fast_Dice_Roll imports
  Bernoulli
  While_SPMF
begin

text \<open>This formalisation follows the ideas by J\'er\'emie Lumbroso \cite{Lumbroso2013arxiv}.\<close>

lemma sample_bits_fusion:
  fixes v :: nat
  assumes "0 < v"
  shows
  "bind_pmf (pmf_of_set {..<v}) (\<lambda>c. bind_pmf (pmf_of_set UNIV) (\<lambda>b. f (2 * c + (if b then 1 else 0)))) =
   bind_pmf (pmf_of_set {..<2 * v}) f"
  (is "?lhs = ?rhs")
proof -
  have "?lhs = bind_pmf (map_pmf (\<lambda>(c, b). (2 * c + (if b then 1 else 0))) (pair_pmf (pmf_of_set {..<v}) (pmf_of_set UNIV))) f"
    (is "_ = bind_pmf (map_pmf ?f _) _")
    by(simp add: pair_pmf_def bind_map_pmf bind_assoc_pmf bind_return_pmf)
  also have "map_pmf ?f (pair_pmf (pmf_of_set {..<v}) (pmf_of_set UNIV)) = pmf_of_set {..<2 * v}"
    (is "?l = ?r" is "map_pmf ?f ?p = _")
  proof(rule pmf_eqI)
    fix i :: nat
    have [simp]: "inj ?f" by(auto simp add: inj_on_def) arith+
    define i' where "i' \<equiv> i div 2"
    define b where "b \<equiv> odd i"
    have i: "i = ?f (i', b)" by(simp add: i'_def b_def)
    show "pmf ?l i = pmf ?r i"
      by(subst i; subst pmf_map_inj')(simp_all add: pmf_pair i'_def assms lessThan_empty_iff split: split_indicator)
  qed
  finally show ?thesis .
qed

lemma sample_bits_fusion2:
  fixes v :: nat
  assumes "0 < v"
  shows
  "bind_pmf (pmf_of_set UNIV) (\<lambda>b. bind_pmf (pmf_of_set {..<v}) (\<lambda>c. f (c + v * (if b then 1 else 0)))) =
   bind_pmf (pmf_of_set {..<2 * v}) f"
  (is "?lhs = ?rhs")
proof -
  have "?lhs = bind_pmf (map_pmf (\<lambda>(c, b). (c + v * (if b then 1 else 0))) (pair_pmf (pmf_of_set {..<v}) (pmf_of_set UNIV))) f"
    (is "_ = bind_pmf (map_pmf ?f _) _")
    unfolding pair_pmf_def by(subst bind_commute_pmf)(simp add: bind_map_pmf bind_assoc_pmf bind_return_pmf)
  also have "map_pmf ?f (pair_pmf (pmf_of_set {..<v}) (pmf_of_set UNIV)) = pmf_of_set {..<2 * v}"
    (is "?l = ?r" is "map_pmf ?f ?p = _")
  proof(rule pmf_eqI)
    fix i :: nat
    have [simp]: "inj_on ?f ({..<v} \<times> UNIV)" by(auto simp add: inj_on_def)
    define i' where "i' \<equiv> if i \<ge> v then i - v else i"
    define b where "b \<equiv> i \<ge> v"
    have i: "i = ?f (i', b)" by(simp add: i'_def b_def)
    show "pmf ?l i = pmf ?r i"
    proof(cases "i < 2 * v")
      case True
      thus ?thesis
        by(subst i; subst pmf_map_inj)(auto simp add: pmf_pair i'_def assms lessThan_empty_iff split: split_indicator)
    next
      case False
      hence "i \<notin> set_pmf ?l" "i \<notin> set_pmf ?r" 
        using assms by(auto simp add: lessThan_empty_iff split: if_split_asm)
      thus ?thesis by(simp add: set_pmf_iff del: set_map_pmf)
    qed
  qed
  finally show ?thesis .
qed

context fixes n :: nat notes [[function_internals]] begin

text \<open>
  The check for @{term "v >= n"} should be done already at the start of the loop. 
  Otherwise we do not see why this algorithm should be optimal (when we start with @{term "v = n"}
  and @{term "c = n - 1"}, then it can go round a few loops before it returns something).

  We define the algorithm as a least fixpoint. To prove termination, we later show that it is
  equivalent to a while loop which samples bitstrings of a given length, which could in turn 
  be implemented as a loop.  The fixpoint formulation is more elegant because we do not need to
  nest any loops.
\<close>

partial_function (spmf) fast_dice_roll :: "nat \<Rightarrow> nat \<Rightarrow> nat spmf"
where
  "fast_dice_roll v c = 
  (if v \<ge> n then if c < n then return_spmf c else fast_dice_roll (v - n) (c - n)
   else do {
     b \<leftarrow> coin_spmf;
     fast_dice_roll (2 * v) (2 * c + (if b then 1 else 0)) } )"

lemma fast_dice_roll_fixp_induct [case_names adm bottom step]:
  assumes "spmf.admissible (\<lambda>fast_dice_roll. P (curry fast_dice_roll))"
  and "P (\<lambda>v c. return_pmf None)"
  and "\<And>fdr. P fdr \<Longrightarrow> P (\<lambda>v c. if v \<ge> n then if c < n then return_spmf c else fdr (v - n) (c - n)
        else bind_spmf coin_spmf (\<lambda>b. fdr (2 * v) (2 * c + (if b then 1 else 0))))"
  shows "P fast_dice_roll"
using assms by(rule fast_dice_roll.fixp_induct)

definition fast_uniform :: "nat spmf"
where "fast_uniform = fast_dice_roll 1 0"

lemma spmf_fast_dice_roll_ub:
  assumes "0 < v"
  shows "spmf (bind_pmf (pmf_of_set {..<v}) (fast_dice_roll v)) x \<le> (if x < n then 1 / n else 0)"
  (is "?lhs \<le> ?rhs")
proof -
  have "ennreal ?lhs \<le> ennreal ?rhs" using assms
  proof(induction arbitrary: v x rule: fast_dice_roll_fixp_induct)
    case adm thus ?case 
      by(rule cont_intro ccpo_class.admissible_leI)+ simp_all
    case bottom thus ?case by simp
    case (step fdr)
    show ?case (is "?lhs \<le> ?rhs")
    proof(cases "n \<le> v")
      case le: True
      then have "?lhs = spmf (bind_pmf (pmf_of_set {..<v}) (\<lambda>c. if c < n then return_spmf c else fdr (v - n) (c - n))) x"
        by simp
      also have "\<dots> = (\<integral>\<^sup>+ c'. indicator (if x < n then {x} else {}) c' \<partial>measure_pmf (pmf_of_set {..<v})) +
        (\<integral>\<^sup>+ c'. indicator {n ..< v} c' * spmf (fdr (v - n) (c' - n)) x \<partial>measure_pmf (pmf_of_set {..<v}))"
        (is "?then = ?found + ?continue") using step.prems
        by(subst nn_integral_add[symmetric])(auto simp add: ennreal_pmf_bind AE_measure_pmf_iff lessThan_empty_iff split: split_indicator intro!: nn_integral_cong_AE)
      also have "?found = (if x < n then 1 else 0) / v" using step.prems le
        by(auto simp add: measure_pmf.emeasure_eq_measure measure_pmf_of_set lessThan_empty_iff Iio_Int_singleton)
      also have "?continue = (\<integral>\<^sup>+ c'. indicator {n ..< v} c' * 1 / v * spmf (fdr (v - n) (c' - n)) x \<partial>count_space UNIV)"
        using step.prems by(auto simp add: nn_integral_measure_pmf lessThan_empty_iff ennreal_mult[symmetric] intro!: nn_integral_cong split: split_indicator)
      also have "\<dots> = (if v = n then 0 else ennreal ((v - n) / v) * spmf (bind_pmf (pmf_of_set {n..<v}) (\<lambda>c'. fdr (v - n) (c' - n))) x)"
        using le step.prems
        by(subst ennreal_pmf_bind)(auto simp add: ennreal_mult[symmetric] nn_integral_measure_pmf nn_integral_0_iff_AE AE_count_space nn_integral_cmult[symmetric] split: split_indicator)
      also {
        assume *: "n < v"
        then have "pmf_of_set {n..<v} = map_pmf ((+) n) (pmf_of_set {..<v - n})"
          by(subst map_pmf_of_set_inj)(auto 4 3 simp add: inj_on_def lessThan_empty_iff intro!: arg_cong[where f=pmf_of_set] intro: rev_image_eqI[where x="_ - n"] diff_less_mono)
        also have "bind_pmf \<dots> (\<lambda>c'. fdr (v - n) (c' - n)) = bind_pmf (pmf_of_set {..<v - n}) (fdr (v - n))"
          by(simp add: bind_map_pmf)
        also have "ennreal (spmf \<dots> x) \<le> (if x < n then 1 / n else 0)" 
          by(rule step.IH)(simp add: *)
        also note calculation }
      then have "\<dots> \<le> ennreal ((v - n) / v) * (if x < n then 1 / n else 0)" using le
        by(cases "v = n")(auto split del: if_split intro: divide_right_mono mult_left_mono)
      also have "\<dots> = (v - n) / v * (if x < n then 1 / n else 0)" by(simp add: ennreal_mult[symmetric])
      finally show ?thesis using le by(auto simp add: add_mono field_simps of_nat_diff ennreal_plus[symmetric] simp del: ennreal_plus)
    next
      case False
      then have "?lhs = spmf (bind_pmf (pmf_of_set {..<v}) (\<lambda>c. bind_pmf (pmf_of_set UNIV) (\<lambda>b. fdr (2 * v) (2 * c + (if b then 1 else 0))))) x"
        by(simp add: bind_spmf_spmf_of_set)
      also have "\<dots> = spmf (bind_pmf (pmf_of_set {..<2 * v}) (fdr (2 * v))) x" using step.prems
        by(simp add: sample_bits_fusion[symmetric])
      also have "\<dots> \<le> ?rhs" using step.prems by(intro step.IH) simp
      finally show ?thesis .
    qed
  qed
  thus ?thesis by simp
qed

lemma spmf_fast_uniform_ub:
  "spmf fast_uniform x \<le> (if x < n then 1 / n else 0)"
proof -
  have "{..<Suc 0} = {0}" by auto
  then show ?thesis using spmf_fast_dice_roll_ub[of 1 x]
    by(simp add: fast_uniform_def pmf_of_set_singleton bind_return_pmf split: if_split_asm)
qed

lemma fast_dice_roll_0 [simp]: "fast_dice_roll 0 c = return_pmf None"
by(induction arbitrary: c rule: fast_dice_roll_fixp_induct)(simp_all add: bind_eq_return_pmf_None)

text \<open>To prove termination, we fold all the iterations that only double into one big step\<close>

definition fdr_step :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat) spmf"
where
  "fdr_step v c =
  (if v = 0 then return_pmf None
   else let x = 2 ^ (nat \<lceil>log 2 (max 1 n) - log 2 v\<rceil>) in
     map_spmf (\<lambda>bs. (x * v, x * c + bs)) (spmf_of_set {..<x}))"

lemma fdr_step_unfold:
  "fdr_step v c =
  (if v = 0 then return_pmf None 
   else if n \<le> v then return_spmf (v, c)
   else do {
     b \<leftarrow> coin_spmf;
     fdr_step (2 * v) (2 * c + (if b then 1 else 0)) })"
  (is "?lhs = ?rhs" is "_ = (if _ then _ else ?else)")
proof(cases "v = 0")
  case v: False
  define x where "x \<equiv> \<lambda>v :: nat. 2 ^ (nat \<lceil>log 2 (max 1 n) - log 2 v\<rceil>) :: nat"
  have x_pos: "x v > 0" by(simp add: x_def)

  show ?thesis
  proof(cases "n \<le> v")
    case le: True
    hence "x v = 1" using v by(simp add: x_def log_le)
    moreover have "{..<1} = {0 :: nat}" by auto
    ultimately show ?thesis using le v by(simp add: fdr_step_def spmf_of_set_singleton)
  next
    case less: False
    hence even: "even (x v)" using v by(simp add: x_def)
    with x_pos have x_ge_1: "x v > 1" by(cases "x v = 1") auto
    have *: "x (2 * v) = x v div 2" using v less unfolding x_def 
      apply(simp add: log_mult diff_add_eq_diff_diff_swap)
      apply(rewrite in "_ = 2 ^ \<hole> div _" le_add_diff_inverse2[symmetric, where b=1])
       apply (simp add: Suc_leI)
      apply(simp del: Suc_pred)
      done

    have "?lhs = map_spmf (\<lambda>bs. (x v * v, x v * c + bs)) (spmf_of_set {..<x v})"
      using v by(simp add: fdr_step_def x_def Let_def)
    also from even have "\<dots> = bind_pmf (pmf_of_set {..<2 * (x v div 2)}) (\<lambda>bs. return_spmf (x v * v, x v * c + bs))"
      by(simp add: map_spmf_conv_bind_spmf bind_spmf_spmf_of_set x_pos lessThan_empty_iff)
    also have "\<dots> = bind_spmf coin_spmf (\<lambda>b. bind_spmf (spmf_of_set {..<x v div 2}) 
      (\<lambda>c'. return_spmf (x v * v, x v * c + c' + (x v div 2) * (if b then 1 else 0))))"
      using x_ge_1
      by(simp add: sample_bits_fusion2[symmetric] bind_spmf_spmf_of_set lessThan_empty_iff add.assoc)
    also have "\<dots> = bind_spmf coin_spmf (\<lambda>b. map_spmf (\<lambda>bs. (x (2 * v) * (2 * v), x (2 * v) * (2 * c + (if b then 1 else 0)) + bs)) (spmf_of_set {..<x (2 * v)}))"
      using * even by(simp add: map_spmf_conv_bind_spmf algebra_simps)
    also have "\<dots> = ?rhs" using v less by(simp add: fdr_step_def Let_def x_def)
    finally show ?thesis .
  qed
qed(simp add: fdr_step_def)

lemma fdr_step_induct [case_names fdr_step]: 
  "(\<And>v c. (\<And>b. \<lbrakk>v \<noteq> 0; v < n\<rbrakk> \<Longrightarrow> P (2 * v) (2 * c + (if b then 1 else 0))) \<Longrightarrow> P v c)
  \<Longrightarrow> P v c"
apply induction_schema
apply pat_completeness
apply(relation "Wellfounded.measure (\<lambda>(v, c). n - v)")
apply simp_all
done

partial_function (spmf) fdr_alt :: "nat \<Rightarrow> nat \<Rightarrow> nat spmf"
where
  "fdr_alt v c = do {
    (v', c') \<leftarrow> fdr_step v c;
    if c' < n then return_spmf c' else fdr_alt (v' - n) (c' - n) }"

lemma fast_dice_roll_alt: "fdr_alt = fast_dice_roll"
proof(intro ext)
  show "fdr_alt v c = fast_dice_roll v c" for v c
  proof(rule spmf.leq_antisym)
    show "ord_spmf (=) (fdr_alt v c) (fast_dice_roll v c)"
    proof(induction arbitrary: v c rule: fdr_alt.fixp_induct[case_names adm bottom step])
      case adm show ?case by simp
      case bottom show ?case by simp
      case (step fdra)
      show ?case
      proof(induction v c rule: fdr_step_induct)
        case inner: (fdr_step v c)
        show ?case
          apply(rewrite fdr_step_unfold)
          apply(rewrite fast_dice_roll.simps)
          apply(auto intro!: ord_spmf_bind_reflI simp add: Let_def inner.IH step.IH)
          done
      qed
    qed
    have "ord_spmf (=) (fast_dice_roll v c) (fdr_alt v c)"
      and "fast_dice_roll 0 c = return_pmf None"
    proof(induction arbitrary: v c rule: fast_dice_roll_fixp_induct)
      case adm thus ?case by simp
      case bottom case 1 thus ?case by simp
      case bottom case 2 thus ?case by simp
      case (step fdr) case 1 show ?case
        apply(rewrite fdr_alt.simps)
        apply(rewrite fdr_step_unfold)
        apply(clarsimp simp add: Let_def)
        apply(auto intro!: ord_spmf_bind_reflI simp add: fdr_alt.simps[symmetric] step.IH rel_pmf_return_pmf2 set_pmf_bind_spmf o_def set_pmf_spmf_of_set split: if_split_asm)
        done
      case step case 2 from step.IH show ?case by(simp add: Let_def bind_eq_return_pmf_None)
    qed
    then show "ord_spmf (=) (fast_dice_roll v c) (fdr_alt v c)" by -
  qed
qed

lemma lossless_fdr_step [simp]: "lossless_spmf (fdr_step v c) \<longleftrightarrow> v > 0"
by(simp add: fdr_step_def Let_def lessThan_empty_iff)

lemma fast_dice_roll_alt_conv_while:
  "fdr_alt v c = 
  map_spmf snd (bind_spmf (fdr_step v c) (loop_spmf.while (\<lambda>(v, c). n \<le> c) (\<lambda>(v, c). fdr_step (v - n) (c - n))))"
proof(induction arbitrary: v c rule: parallel_fixp_induct_2_1[OF partial_function_definitions_spmf partial_function_definitions_spmf fdr_alt.mono loop_spmf.while.mono fdr_alt_def loop_spmf.while_def, case_names adm bottom step])
  case adm show ?case by(simp)
  case bottom show ?case by simp
  case (step fdr while)
  show ?case using step.IH
    by(auto simp add: map_spmf_bind_spmf o_def intro!: bind_spmf_cong[OF refl])
qed

lemma lossless_fast_dice_roll: 
  assumes "c < v" "v \<le> n"
  shows "lossless_spmf (fast_dice_roll v c)"
proof(cases "v < n")
  case True
  let ?I = "\<lambda>(v, c). c < v \<and> n \<le> v \<and> v < 2 * n"
  let ?f = "\<lambda>(v, c). if n \<le> c then n + c - v + 1 else 0"
  have invar: "?I (v', c')" if step: "(v', c') \<in> set_spmf (fdr_step (v - n) (c - n))" 
    and I: "c < v" "n \<le> v" "v < 2 * n" and c: "n \<le> c" for v' c' v c
  proof(clarsimp; safe)
    define x where "x = nat \<lceil>log 2 (max 1 n) - log 2 (v - n)\<rceil>"
    have **: "-1 < log 2 (real n / real (v - n))" by(rule less_le_trans[where y=0])(use I c in \<open>auto\<close>)

    from I c step obtain bs where v': "v' = 2 ^ x * (v - n)" 
      and c': "c' = 2 ^ x * (c - n) + bs"
      and bs: "bs < 2 ^ x"
      unfolding fdr_step_def x_def[symmetric] by(auto simp add: Let_def)
    have "2 ^ x * (c - n) + bs < 2 ^ x * (c - n + 1)" unfolding distrib_left using bs
      by(intro add_strict_left_mono) simp
    also have "\<dots> \<le> 2 ^ x * (v - n)" using I c by(intro mult_left_mono) auto
    finally show "c' < v'" using c' v' by simp
    
    have "v' = 2 powr x * (v - n)" by(simp add: powr_realpow v')
    also have "\<dots> < 2 powr (log 2 (max 1 n) - log 2 (v - n) + 1) * (v - n)"
      using ** I c by(intro mult_strict_right_mono)(auto simp add: x_def log_divide)
    also have "\<dots> \<le> 2 * n" unfolding powr_add using I c
      by(simp add: log_divide[symmetric] max_def)
    finally show "v' < 2 * n" using c' by(simp del: of_nat_add)
    
    have "log 2 (n / (v - n)) \<le> x" using I c ** by(auto simp add: x_def log_divide max_def)
    hence "2 powr log 2 (n / (v - n)) \<le> 2 powr x" by(rule powr_mono) simp
    also have "2 powr log 2 (n / (v - n)) = n / (v - n)" using I c by(simp)
    finally have "n \<le> real (2 ^ x * (v - n))" using I c by(simp add: field_simps powr_realpow)
    then show "n \<le> v'" by(simp add: v' del: of_nat_mult)
  qed
  
  have loop: "lossless_spmf (loop_spmf.while (\<lambda>(v, c). n \<le> c) (\<lambda>(v, c). fdr_step (v - n) (c - n)) (v, c))"
    if "c < 2 * n" and "n \<le> v" and "c < v" and "v < 2 * n"
    for v c
  proof(rule termination_variant_invar; clarify?)
    fix v c
    assume I: "?I (v, c)" and c: "n \<le> c"
    show "?f (v, c) \<le> n" using I c by auto

    define x where "x = nat \<lceil>log 2 (max 1 n) - log 2 (v - n)\<rceil>"
    define p :: real where "p \<equiv> 1 / (2 * n)"

    from I c have n: "0 < n" and v: "n < v" by auto
    from I c v n have x_pos: "x > 0" by(auto simp add: x_def max_def)
    
    have **: "-1 < log 2 (real n / real (v - n))" by(rule less_le_trans[where y=0])(use I c in \<open>auto\<close>)
    then have "x \<le> log 2 (real n) + 1" using v n
      by(auto simp add: x_def log_divide[symmetric] max_def field_simps intro: order_trans[OF of_int_ceiling_le_add_one])
    hence "2 powr x \<le> 2 powr \<dots>" by(rule powr_mono) simp
    hence "p \<le> 1 / 2 ^ x" unfolding powr_add using n
      by(subst (asm) powr_realpow, simp)(subst (asm) powr_log_cancel; simp_all add: p_def field_simps)
    also
    let ?X = "{c'. n \<le> 2 ^ x * (c - n) + c' \<longrightarrow> n + (2 ^ x * (c - n) + c') - 2 ^ x * (v - n) < n + c - v}"
    have "n + c * 2 ^ x - v * 2 ^ x < c + n - v" using I c
    proof(cases "n + c * 2 ^ x \<ge> v * 2 ^ x")
      case True
      have "(int c - v) * 2 ^ x < (int c - v) * 1"
        using x_pos I c by(intro mult_strict_left_mono_neg) simp_all
      then have "int n + c * 2 ^ x - v * 2 ^ x < c + int n - v" by(simp add: algebra_simps)
      also have "\<dots> = int (c + n - v)" using I c by auto
      also have "int n + c * 2 ^ x - v * 2 ^ x = int (n + c * 2 ^ x - v * 2 ^ x)"
        using True that by(simp add: of_nat_diff)
      finally show ?thesis by simp
    qed auto
    then have "{..<2 ^ x} \<inter> ?X \<noteq> {}" using that n v
      by(auto simp add: disjoint_eq_subset_Compl Collect_neg_eq[symmetric] lessThan_subset_Collect algebra_simps intro: exI[where x=0])
    then have "0 < card ({..<2 ^ x} \<inter> ?X)" by(simp add: card_gt_0_iff)
    hence "1 / 2 ^ x \<le> \<dots> / 2 ^ x" by(simp add: field_simps)
    finally show "p \<le> spmf (map_spmf (\<lambda>s'. ?f s' < ?f (v, c)) (fdr_step (v - n) (c - n))) True"
      using I c unfolding fdr_step_def x_def[symmetric]
      by(clarsimp simp add: Let_def spmf.map_comp o_def spmf_map measure_spmf_of_set vimage_def p_def)

    show "lossless_spmf (fdr_step (v - n) (c - n))" using I c by simp
    show "?I (v', c')" if step: "(v', c') \<in> set_spmf (fdr_step (v - n) (c - n))" for v' c' 
      using that by(rule invar)(use I c in auto)
  next
    show "(0 :: real) < 1 / (2 * n)" using that by(simp)
    show "?I (v, c)" using that by simp
  qed
  show ?thesis using assms True 
    by(auto simp add: fast_dice_roll_alt[symmetric] fast_dice_roll_alt_conv_while intro!: loop dest: invar[of _ _ "n + v" "n + c", simplified])
next
  case False
  with assms have "v = n" by simp
  thus ?thesis using assms by(subst fast_dice_roll.simps) simp
qed

lemma fast_dice_roll_n0: 
  assumes "n = 0"
  shows "fast_dice_roll v c = return_pmf None"
  by(induction arbitrary: v c rule: fast_dice_roll_fixp_induct)(simp_all add: assms)

lemma lossless_fast_uniform [simp]: "lossless_spmf fast_uniform \<longleftrightarrow> n > 0"
proof(cases "n = 0")
  case True
  then show ?thesis using fast_dice_roll_n0 unfolding fast_uniform_def by(simp)
next
  case False
  then show ?thesis by(simp add: fast_uniform_def lossless_fast_dice_roll)
qed

lemma spmf_fast_uniform: "spmf fast_uniform x = (if x < n then 1 / n else 0)"
proof(cases "n > 0")
  case n: True
  show ?thesis using spmf_fast_uniform_ub
  proof(rule spmf_ub_tight)
    have "(\<Sum>\<^sup>+ x. ennreal (if x < n then 1 / n else 0)) = (\<Sum>\<^sup>+ x\<in>{..<n}. 1 / n)"
      by(auto simp add: nn_integral_count_space_indicator simp del: nn_integral_const intro: nn_integral_cong)
    also have "\<dots> = 1" using n by(simp add: field_simps ennreal_of_nat_eq_real_of_nat ennreal_mult[symmetric])
    also have "\<dots> = weight_spmf fast_uniform" using lossless_fast_uniform n unfolding lossless_spmf_def by simp
    finally show "(\<Sum>\<^sup>+ x. ennreal (if x < n then 1 / n else 0)) = \<dots>" .
  qed
next
  case False
  with fast_dice_roll_n0[of 1 0] show ?thesis unfolding fast_uniform_def by(simp)
qed

end

lemma fast_uniform_conv_uniform: "fast_uniform n = spmf_of_set {..<n}"
by(rule spmf_eqI)(simp add: spmf_fast_uniform spmf_of_set)

end
