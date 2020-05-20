section\<open>Trace-Based Noninterference\<close>

theory Trace_Based
  imports Resumption_Based
begin

(* This contains the development leading to the paper's Prop. 4. *)

subsection\<open>Preliminaries\<close>

lemma dist_sum:
  fixes f :: "'a \<Rightarrow> real" and g :: "'a \<Rightarrow> real"
  assumes "\<And>i. i \<in> I \<Longrightarrow> dist (f i) (g i) \<le> e i"
  shows "dist (\<Sum>i\<in>I. f i) (\<Sum>i\<in>I. g i) \<le> (\<Sum>i\<in>I. e i)"
proof cases
  assume "finite I" from this assms show ?thesis
  proof induct
    case (insert i I)
    then have "dist (\<Sum>i\<in>insert i I. f i) (\<Sum>i\<in>insert i I. g i) \<le> dist (f i) (g i) + dist (\<Sum>i\<in>I. f i) (\<Sum>i\<in>I. g i)"
      by (simp add: dist_triangle_add)
    also have "\<dots> \<le> e i + (\<Sum>i\<in>I. e i)"
      using insert by (intro add_mono) auto
    finally show ?case using insert by simp
  qed simp
qed simp

lemma dist_mult[simp]: "dist (x * y) (x * z) = \<bar>x\<bar> * dist y z"
  unfolding dist_real_def abs_mult[symmetric] right_diff_distrib ..

lemma dist_divide[simp]: "dist (y / r) (z / r) = dist y z / \<bar>r\<bar>"
  unfolding dist_real_def abs_divide[symmetric] diff_divide_distrib ..

lemma dist_weighted_sum:
  fixes f :: "'a \<Rightarrow> real" and g :: "'b \<Rightarrow> real"
  assumes eps: "\<And>i j. i \<in> I \<Longrightarrow> j \<in> J \<Longrightarrow> w i \<noteq> 0 \<Longrightarrow> v j \<noteq> 0 \<Longrightarrow> dist (f i) (g j) \<le> d i + e j"
    and pos: "\<And>i. i\<in>I \<Longrightarrow> 0 \<le> w i" "\<And>j. j\<in>J \<Longrightarrow> 0 \<le> v j"
    and sum: "(\<Sum>i\<in>I. w i) = 1" "(\<Sum>j\<in>J. v j) = 1"
  shows "dist (\<Sum>i\<in>I. w i * f i) (\<Sum>j\<in>J. v j * g j) \<le> (\<Sum>i\<in>I. w i * d i) + (\<Sum>j\<in>J. v j * e j)"
proof -
  let "?W h" = "(\<Sum>(i,j)\<in>I\<times>J. (w i * v j) * h (i,j))"
  { fix g :: "'b \<Rightarrow> real"
    have "(\<Sum>j\<in>J. v j * g j) = (\<Sum>i\<in>I. w i) * (\<Sum>j\<in>J. v j * g j)"
      using sum by simp
    also have "\<dots> = ?W (g\<circ>snd)"
      by (simp add: ac_simps sum_product sum.cartesian_product)
    finally have "(\<Sum>j\<in>J. v j * g j) = ?W (g\<circ>snd)" . }
  moreover
  { fix f :: "'a \<Rightarrow> real"
    have "(\<Sum>i\<in>I. w i * f i) = (\<Sum>i\<in>I. w i * f i) * (\<Sum>j\<in>J. v j)"
      using sum by simp
    also have "\<dots> = ?W (f\<circ>fst)"
      unfolding sum_product sum.cartesian_product by (simp add: ac_simps)
    finally have "(\<Sum>i\<in>I. w i * f i) = ?W (f\<circ>fst)" . }
  moreover
  { have "dist (?W (f\<circ>fst)) (?W (g\<circ>snd)) \<le> ?W (\<lambda>(i,j). d i + e j)"
      using eps pos
      by (intro dist_sum)
         (auto simp: mult_le_cancel_left zero_less_mult_iff mult_le_0_iff not_le[symmetric])
    also have "\<dots> = ?W (d \<circ> fst) + ?W (e \<circ> snd)"
      by (auto simp add: sum.distrib[symmetric] field_simps intro!: sum.cong)
    finally have "dist (?W (f\<circ>fst)) (?W (g\<circ>snd)) \<le> ?W (d \<circ> fst) + ?W (e \<circ> snd)" by simp }
  ultimately show ?thesis by simp
qed

lemma field_abs_le_zero_epsilon:
  fixes x :: "'a::{linordered_field}"
  assumes epsilon: "\<And>e. 0 < e \<Longrightarrow> \<bar>x\<bar> \<le> e"
  shows "\<bar>x\<bar> = 0"
proof (rule antisym)
  show "\<bar>x\<bar> \<le> 0"
  proof (rule field_le_epsilon)
    fix e :: 'a assume "0 < e" then show "\<bar>x\<bar> \<le> 0 + e" by simp fact
  qed
qed simp

lemma nat_nat_induct[case_names less]:
  fixes P :: "nat \<Rightarrow> nat \<Rightarrow> bool"
  assumes less: "\<And>n m. (\<And>j k. j + k < n + m \<Longrightarrow> P j k) \<Longrightarrow> P n m"
  shows "P n m"
proof -
  define N where "N \<equiv> n + m"
  then show ?thesis
  proof (induct N arbitrary: n m rule: nat_less_induct)
    case 1 show "P n m"
      apply (rule less)
      apply (rule 1[rule_format])
      apply auto
      done
  qed
qed

lemma part_insert:
  assumes "part A P" assumes "X \<inter> A = {}"
  shows "part (A \<union> X) (insert X P)"
  using assms by (auto simp: part_def)

lemma part_insert_subset:
  assumes X: "part (A - X) P" "X \<subseteq> A"
  shows "part A (insert X P)"
  using X part_insert[of "A - X" P X] by (simp add: Un_absorb2)

lemma part_is_subset:
  "part S P \<Longrightarrow> p \<in> P \<Longrightarrow> p \<subseteq> S"
  unfolding part_def by (metis Union_upper)

lemma dist_nonneg_bounded:
  fixes l u x y :: real
  assumes "l \<le> x" "x \<le> u" "l \<le> y" "y \<le> u"
  shows "dist x y \<le> u - l"
  using assms unfolding dist_real_def by arith

lemma integrable_count_space_finite_support:
  fixes f :: "'a \<Rightarrow> 'b::{banach,second_countable_topology}"
  shows "finite {x\<in>X. f x \<noteq> 0} \<Longrightarrow> integrable (count_space X) f"
  by (auto simp: nn_integral_count_space integrable_iff_bounded)

lemma lebesgue_integral_point_measure:
  fixes g :: "_ \<Rightarrow> real"
  assumes f: "finite {a\<in>A. 0 < f a \<and> g a \<noteq> 0}"
  shows "integral\<^sup>L (point_measure A f) g = (\<Sum>a|a\<in>A \<and> 0 < f a \<and> g a \<noteq> 0. f a * g a)"

proof -
  have eq: "{a \<in> A. max 0 (f a) \<noteq> 0 \<and> g a \<noteq> 0} = {a\<in>A. 0 < f a \<and> g a \<noteq> 0}"
    by auto
  have *: "ennreal (f x) = ennreal (max 0 (f x))" for x
    by (cases "0 \<le> f x") (auto simp: max.absorb1 ennreal_neg)

  show ?thesis
    unfolding point_measure_def *
    using f
    apply (subst integral_real_density)
    apply (auto simp add: integral_real_density lebesgue_integral_count_space_finite_support eq
      intro!: sum.cong)
    done
qed

lemma (in finite_measure) finite_measure_dist:
  assumes AE: "AE x in M. x \<notin> C \<longrightarrow> (x \<in> A \<longleftrightarrow> x \<in> B)"
  assumes sets: "A \<in> sets M" "B \<in> sets M" "C \<in> sets M"
  shows "dist (measure M A) (measure M B) \<le> measure M C"
proof -
  { have "measure M A \<le> measure M (B \<union> C)"
      using AE sets by (auto intro: finite_measure_mono_AE)
    also have "\<dots> \<le> measure M B + measure M C"
      using sets by (auto intro: finite_measure_subadditive)
    finally have A: "measure M A \<le> measure M B + measure M C" . }
  moreover
  { have "measure M B \<le> measure M (A \<union> C)"
      using AE sets by (auto intro: finite_measure_mono_AE)
    also have "\<dots> \<le> measure M A + measure M C"
      using sets by (auto intro: finite_measure_subadditive)
    finally have B: "measure M B \<le> measure M A + measure M C" . }
  ultimately show ?thesis
    by (simp add: dist_real_def)
qed

lemma (in prob_space) prob_dist:
  assumes AE: "AE x in M. \<not> C x \<longrightarrow> (A x \<longleftrightarrow> B x)"
  assumes sets: "Measurable.pred M A" "Measurable.pred M B" "Measurable.pred M C"
  shows "dist \<P>(x in M. A x) \<P>(x in M. B x) \<le> \<P>(x in M. C x)"
  using assms by (intro finite_measure_dist) auto

lemma Least_eq_0_iff: "(\<exists>i::nat. P i) \<Longrightarrow> (LEAST i. P i) = 0 \<longleftrightarrow> P 0"
  by (metis LeastI_ex neq0_conv not_less_Least)

lemma case_nat_comp_Suc[simp]: "case_nat x f \<circ> Suc = f"
  by auto

lemma sum_eq_0_iff:
  fixes f :: "_ \<Rightarrow> 'a :: {comm_monoid_add,ordered_ab_group_add}"
  shows "finite A \<Longrightarrow> (\<And>i. i \<in> A \<Longrightarrow> 0 \<le> f i) \<Longrightarrow> (\<Sum>i\<in>A. f i) = 0 \<longleftrightarrow> (\<forall>i\<in>A. f i = 0)"
  apply rule
  apply (blast intro: sum_nonneg_0)
  apply simp
  done

lemma sum_less_0_iff:
  fixes f :: "_ \<Rightarrow> 'a :: {comm_monoid_add,ordered_ab_group_add}"
  shows "finite A \<Longrightarrow> (\<And>i. i \<in> A \<Longrightarrow> 0 \<le> f i) \<Longrightarrow> 0 < (\<Sum>i\<in>A. f i) \<longleftrightarrow> (\<exists>i\<in>A. 0 < f i)"
  using sum_nonneg[of A f] sum_eq_0_iff[of A f] by (simp add: less_le)

context PL_Indis
begin

declare emp_gen[simp del]

interpretation pmf_as_function .

lift_definition wt_pmf :: "('test, 'atom, 'choice) cmd \<times> 'state \<Rightarrow> nat pmf" is
  "\<lambda>(c, s) i. if proper c then if i < brn c then wt c s i else 0 else if i = 0 then 1 else 0"
proof
  let ?f = "\<lambda>(c, s) i. if proper c then if i < brn c then wt c s i else 0 else if i = 0 then 1 else 0"
  fix cf show "\<forall>i. 0 \<le> ?f cf i"
    by (auto split: prod.split)
  show "(\<integral>\<^sup>+i. ?f cf i \<partial>count_space UNIV) = 1"
    by (subst nn_integral_count_space'[where A="if proper (fst cf) then {..<brn (fst cf)} else {0}" for n])
       (auto split: prod.split)
qed

definition trans :: "('test, 'atom, 'choice) cmd \<times> 'state \<Rightarrow> (('test, 'atom, 'choice) cmd \<times> 'state) pmf" where
  "trans cf = map_pmf (\<lambda>i. if proper (fst cf) then cont_eff cf i else cf) (wt_pmf cf)"

sublocale T?: MC_syntax trans .

abbreviation "G cf \<equiv> set_pmf (trans cf)"

lemma set_pmf_map: "set_pmf (map_pmf f M) = f ` set_pmf M"
  using pmf_set_map[of f] by (simp add: comp_def fun_eq_iff)

lemma set_pmf_wt:
  "set_pmf (wt_pmf cf) = (if proper (fst cf) then {i. i < brn (fst cf) \<and> 0 < wt (fst cf) (snd cf) i} else {0})"
  by (auto simp: set_eq_iff set_pmf_iff wt_pmf.rep_eq split: prod.split) (metis less_le wt_ge_0)

lemma G_eq:
  "G cf = (if proper (fst cf) then {cont_eff cf i | i. i < brn (fst cf) \<and> 0 < wt (fst cf) (snd cf) i } else {cf})"
  by (auto simp add: trans_def set_pmf_map set_pmf_wt)

lemma discrCf_G: "discrCf cf \<Longrightarrow> cf' \<in> G cf \<Longrightarrow> discrCf cf'"
  using discrCf_cont[of cf] by (auto simp: G_eq split: if_split_asm)

lemma measurable_discrCf[measurable]: "Measurable.pred (count_space UNIV) discrCf"
  by auto

lemma measurable_indis[measurable]: "Measurable.pred (count_space UNIV) (\<lambda>x. snd x \<approx> c)"
  by auto

lemma integral_trans:
  "proper (fst cf) \<Longrightarrow>
    (\<integral>x. f x \<partial>trans cf) = (\<Sum>i<brn (fst cf). wt (fst cf) (snd cf) i * f (cont_eff cf i))"
  unfolding trans_def map_pmf_rep_eq
  apply (simp add: integral_distr)
  apply (subst integral_measure_pmf[of "{..< brn (fst cf)}"])
  apply (auto simp: set_pmf_wt mult_ac wt_pmf.rep_eq split: prod.split)
  done

subsection "Quasi strong termination traces"

abbreviation "qsend \<equiv> sfirst (holds discrCf)"

lemma qsend_eq_0_iff: "qsend cfT = 0 \<longleftrightarrow> discrCf (shd cfT)"
  by (simp add: sfirst.simps[of _ cfT])

lemma qsend_eq_0[simp]: "discrCf cf \<Longrightarrow> qsend (cf ## \<omega>) = 0"
  by (simp add: qsend_eq_0_iff)

lemma alw_discrCf: "enabled cf \<omega> \<Longrightarrow> discrCf cf \<Longrightarrow> alw (holds discrCf) \<omega>"
  by (coinduction arbitrary: cf \<omega>)
     (auto simp add: HLD_iff elim: enabled.cases intro: discrCf_G simp del: split_paired_Ex)

lemma alw_discrCf_indis':
  "enabled cf \<omega> \<Longrightarrow> discrCf cf \<Longrightarrow> snd cf \<approx> t \<Longrightarrow> alw (holds (\<lambda>cf'. snd cf' \<approx> t)) \<omega>"
proof (coinduction arbitrary: cf \<omega>)
  case alw with discrCf_eff_indis[of cf] show ?case
    by (auto simp add: HLD_iff enabled.simps[of _ \<omega>] G_eq
             simp del: split_paired_Ex discrCf_eff_indis
             intro!: exI[of _ "shd \<omega>"]
             split: if_split_asm)
       (blast intro: indis_trans indis_sym)+
qed

lemma alw_discrCf_indis:
  "enabled cf \<omega> \<Longrightarrow> discrCf cf \<Longrightarrow> alw (holds (\<lambda>cf'. snd cf' \<approx> snd cf)) (cf ## \<omega>)"
  using alw_discrCf_indis'[of cf \<omega>, OF _ _ indis_refl]
  by (simp add: alw.simps[of _ "cf ## \<omega>"] indis_refl)

lemma enabled_sdrop: "enabled cf \<omega> \<Longrightarrow> enabled ((cf ## \<omega>) !! n) (sdrop n \<omega>)"
proof (induction n arbitrary: cf \<omega>)
  case (Suc n) from Suc.IH[of "shd \<omega>" "stl \<omega>"] Suc.prems show ?case
    unfolding enabled.simps[of cf] by simp
qed simp

lemma sfirst_eq_eSuc: "sfirst P \<omega> = eSuc n \<longleftrightarrow> (\<not> P \<omega>) \<and> sfirst P (stl \<omega>) = n"
  by (subst sfirst.simps) auto

lemma qsend_snth: "qsend \<omega> = enat n \<Longrightarrow> discrCf (\<omega> !! n)"
  by (induction n arbitrary: \<omega>)
     (simp_all add: eSuc_enat[symmetric] enat_0 sfirst_eq_0 sfirst_eq_eSuc)

lemma indis_iff: "a \<approx> d \<Longrightarrow> b \<approx> d \<Longrightarrow> a \<approx> c \<longleftrightarrow> b \<approx> c"
  by (metis indis_trans indis_sym indis_refl)

lemma enabled_qsend_indis:
  assumes "enabled cf \<omega>" "qsend (cf ## \<omega>) \<le> n" "qsend (cf ## \<omega>) \<le> m"
  shows "snd ((cf ## \<omega>) !! n) \<approx> t \<longleftrightarrow> snd ((cf ## \<omega>) !! m) \<approx> t"
proof -
  from assms obtain N :: nat where N: "qsend (cf ## \<omega>) = N"
    by (cases "qsend (cf ## \<omega>)") auto
  note discr_N = qsend_snth[OF this] and sd = enabled_sdrop[OF assms(1), of N]
  have "\<And>\<omega>. \<omega> !! N ## sdrop N (stl \<omega>) = sdrop N \<omega>"
    by (induct N) auto
  from this[of "cf ## \<omega>"] have eq: "(cf ## \<omega>) !! N ## sdrop N \<omega> = sdrop N (cf ## \<omega>)"
    by simp

  from discr_N alw_discrCf_indis[OF sd _] assms(2,3) show ?thesis
    by (simp add: N alw_iff_sdrop le_iff_add[where 'a=nat] eq)
       (metis indis_iff)
qed

lemma enabled_imp_UNTIL_alw_discrCf:
  "enabled (shd \<omega>) (stl \<omega>) \<Longrightarrow> (not (holds discrCf) until (alw (holds discrCf))) \<omega>"
proof (coinduction arbitrary: \<omega>)
  case UNTIL then show ?case
    using alw_discrCf[of "shd \<omega>" "stl \<omega>"]
    by (cases "discrCf (shd \<omega>)")
       (simp_all add: enabled.simps[of "shd \<omega>"] alw.simps[of _ \<omega>])
qed

lemma less_qsend_iff_not_discrCf:
  "enabled cf bT \<Longrightarrow> n < qsend (cf ## bT) \<longleftrightarrow> \<not> discrCf ((cf ## bT) !! n)"
  using enabled_imp_UNTIL_alw_discrCf[THEN less_sfirst_iff, of "cf ## bT"]
  by (simp add: holds.simps[abs_def])

subsection "Terminating configurations"

definition "qstermCf cf \<longleftrightarrow> (\<forall>cfT. enabled cf cfT \<longrightarrow> qsend (cf ## cfT) < \<infinity>)"

lemma qstermCf_E:
  "qstermCf cf \<Longrightarrow> cf' \<in> G cf \<Longrightarrow> qstermCf cf'"
  apply (auto simp: qstermCf_def)
  apply (erule_tac x="cf' ## cfT" in allE)
  apply (auto simp: sfirst_Stream intro: enat_0 discrCf_G split: if_split_asm intro: enabled.intros)
  done

abbreviation "eff_at cf bT n \<equiv> snd ((cf ## bT) !! n)"
abbreviation "cont_at cf bT n \<equiv> fst ((cf ## bT) !! n)"

definition "amSec c \<longleftrightarrow> (\<forall>s1 s2 n t. s1 \<approx> s2 \<longrightarrow>
  \<P>(bT in T.T (c, s1). eff_at (c, s1) bT n \<approx> t) =
  \<P>(bT in T.T (c, s2). eff_at (c, s2) bT n \<approx> t))"

definition "eSec c \<longleftrightarrow> (\<forall>s1 s2 t. s1 \<approx> s2 \<longrightarrow>
  \<P>(bT in T.T (c, s1). \<exists>n. qsend ((c, s1) ## bT) = n \<and> eff_at (c, s1) bT n \<approx> t) =
  \<P>(bT in T.T (c, s2). \<exists>n. qsend ((c, s2) ## bT) = n \<and> eff_at (c, s2) bT n \<approx> t))"

definition "aeT c \<longleftrightarrow> (\<forall>s. AE bT in T.T (c,s). qsend ((c,s) ## bT) < \<infinity>)"

lemma dist_Ps_upper_bound:
  fixes cf1 cf2 :: "('test, 'atom, 'choice) cmd \<times> 'state" and s :: "'state" and S
  defines "S cf bT \<equiv> \<exists>n. qsend (cf ## bT) = n \<and> eff_at cf bT n \<approx> s"
  defines "Ps cf \<equiv> \<P>(bT in T.T cf. S cf bT)"
  defines "N cf n bT \<equiv> \<not> discrCf ((cf ## bT) !! n)"
  defines "Pn cf n \<equiv> \<P>(bT in T.T cf. N cf n bT)"
  assumes bisim: "proper (fst cf1)" "proper (fst cf2)" "fst cf1 \<approx>01 fst cf2" "snd cf1 \<approx> snd cf2"
  shows "dist (Ps cf1) (Ps cf2) \<le> Pn cf1 n + Pn cf2 m"
using bisim proof (induct n m arbitrary: cf1 cf2 rule: nat_nat_induct)
  case (less n m)
  note \<open>proper (fst cf1)\<close>[simp, intro]
  note \<open>proper (fst cf2)\<close>[simp, intro]

  define W where "W c = sum (wt (fst c) (snd c))" for c
  from ZObis_mC_ZOC[OF \<open>fst cf1 \<approx>01 fst cf2\<close> \<open>snd cf1 \<approx> snd cf2\<close>]
  obtain I0 P F where mC: "mC_ZOC ZObis (fst cf1) (fst cf2) (snd cf1) (snd cf2) I0 P F" by blast
  then have P: "{} \<notin> P - {I0}" "part {..<brn (fst cf1)} P" and "I0 \<in> P"
    and FP: "{} \<notin> F`(P-{I0})" "part {..<brn (fst cf2)} (F`P)" "inj_on F P"
    and eff: "\<And>q i j. q\<in>P \<Longrightarrow> q\<noteq>I0 \<Longrightarrow> i\<in>q \<Longrightarrow> j\<in>F q \<Longrightarrow> eff (fst cf1) (snd cf1) i \<approx> eff (fst cf2) (snd cf2) j"
    and cont: "\<And>q i j. q\<in>P \<Longrightarrow> q\<noteq>I0 \<Longrightarrow> i\<in>q \<Longrightarrow> j\<in>F q \<Longrightarrow> cont (fst cf1) (snd cf1) i \<approx>01 cont (fst cf2) (snd cf2) j"
    and wt:
      "\<And>I. I \<in> P - {I0} \<Longrightarrow> W cf1 I0 < 1 \<Longrightarrow> W cf2 (F I0) < 1 \<Longrightarrow>
      W cf1 I / (1 - W cf1 I0) = W cf2 (F I) / (1 - W cf2 (F I0))"
    and I0:
      "\<And>i. i \<in> I0 \<Longrightarrow> snd cf1 \<approx> eff (fst cf1) (snd cf1) i"
      "\<And>i. i \<in> I0 \<Longrightarrow> cont (fst cf1) (snd cf1) i \<approx>01 fst cf2"
    and FI0:
      "\<And>i. i \<in> F I0 \<Longrightarrow> snd cf2 \<approx> eff (fst cf2) (snd cf2) i"
      "\<And>i. i \<in> F I0 \<Longrightarrow> fst cf1 \<approx>01 cont (fst cf2) (snd cf2) i"
    unfolding mC_ZOC_def mC_ZOC_part_def mC_ZOC_eff_cont_def mC_ZOC_eff_cont0_def mC_ZOC_wt_def W_def
    by simp_all

  have "finite P" "inj_on F (P - {I0})" and FP': "finite (F`P)" "F I0 \<in> F`P"
    using finite_part[OF _ P(2)] finite_part[OF _ FP(2)] \<open>I0 \<in> P\<close> \<open>inj_on F P\<close>
    by (auto intro: inj_on_diff)

  { fix I i assume "I \<in> P" "i \<in> I"
    with P have "0 \<le> wt (fst cf1) (snd cf1) i"
      by (auto dest: part_is_subset intro!: wt_ge_0) }
  note wt1_nneg[intro] = this

  { fix I i assume "I \<in> P" "i \<in> F I"
    with FP have "0 \<le> wt (fst cf2) (snd cf2) i"
      by (auto dest: part_is_subset intro!: wt_ge_0) }
  note wt2_nneg[intro] = this

  { fix I assume "I \<in> P"
    then have "0 \<le> W cf1 I"
      unfolding W_def by (auto intro!: sum_nonneg) }
  note W1_nneg[intro] = this

  { fix I assume "I \<in> P"
    then have "0 \<le> W cf2 (F I)"
      unfolding W_def by (auto intro!: sum_nonneg) }
  note W2_nneg[intro] = this

  show ?case
  proof cases
    { fix n cf1 cf2 assume *: "fst cf1 \<approx>01 fst cf2" "snd cf1 \<approx> snd cf2"
      have "dist (Ps cf1) (Ps cf2) \<le> Pn cf1 0"
      proof cases
        assume cf1: "discrCf cf1"
        moreover
        note cf2 = ZObis_pres_discrCfR[OF cf1 *]
        from cf1 cf2 have "S cf1 = (\<lambda>bT. snd cf1 \<approx> s)" "S cf2 = (\<lambda>bT. snd cf2 \<approx> s)"
          unfolding S_def[abs_def] by (auto simp: enat_0[symmetric])
        moreover from \<open>snd cf1 \<approx> snd cf2\<close> have "snd cf1 \<approx> s \<longleftrightarrow> snd cf2 \<approx> s"
          by (blast intro: indis_sym indis_trans)
        ultimately show ?thesis
          using T.prob_space by (cases "snd cf2 \<approx> s") (simp_all add: Ps_def Pn_def measure_nonneg)
      next
        assume cf1: "\<not> discrCf cf1"
        then have "Pn cf1 0 = 1"
          using T.prob_space by (simp add: Pn_def N_def)
        moreover have "dist (Ps cf1) (Ps cf2) \<le> 1"
          using dist_nonneg_bounded[where u=1 and l=0 and x="Ps cf1" and y="Ps cf2"]
          by (auto simp add: dist_real_def Ps_def measure_nonneg split: abs_split)
        ultimately show ?thesis by simp
      qed }
    note base_case = this

    assume "n = 0 \<or> m = 0"
    then show ?thesis
    proof
      assume "n = 0"
      moreover
      with T.prob_space \<open>fst cf1 \<approx>01 fst cf2\<close> \<open>snd cf1 \<approx> snd cf2\<close>
      have "dist (Ps cf1) (Ps cf2) \<le> Pn cf1 0"
        by (intro base_case) (auto simp: Ps_def Pn_def)
      moreover have "0 \<le> Pn cf2 m"
        by (simp add: Pn_def measure_nonneg)
      ultimately show ?thesis
        by simp
    next
      assume "m = 0"
      moreover
      with T.prob_space \<open>fst cf1 \<approx>01 fst cf2\<close> \<open>snd cf1 \<approx> snd cf2\<close>
      have "dist (Ps cf2) (Ps cf1) \<le> Pn cf2 0"
        by (intro base_case) (auto simp: Ps_def Pn_def intro: indis_sym ZObis_sym)
      moreover have "0 \<le> Pn cf1 n"
        by (simp add: Pn_def measure_nonneg)
      ultimately show ?thesis
        by (simp add: dist_commute)
    qed
  next
    assume "\<not> (n = 0 \<or> m = 0)"
    then have "n \<noteq> 0" "m \<noteq> 0" by auto
    then obtain n' m' where nm: "n = Suc n'" "m = Suc m'"
      by (metis nat.exhaust)

    define ps pn
      where "ps cf I = (\<Sum>b\<in>I. wt (fst cf) (snd cf) b / W cf I * Ps (cont_eff cf b))"
        and "pn cf I n = (\<Sum>b\<in>I. wt (fst cf) (snd cf) b / W cf I * Pn (cont_eff cf b) n)"
      for cf I n

    { fix I assume "I \<in> P" "I \<noteq> I0" and W: "W cf1 I \<noteq> 0" "W cf2 (F I) \<noteq> 0"
      then have "dist (ps cf1 I) (ps cf2 (F I)) \<le> pn cf1 I n' + pn cf2 (F I) m'"
        unfolding ps_def pn_def
      proof (intro dist_weighted_sum)
        fix i j assume ij: "i \<in> I" "j \<in> F I"
        assume "wt (fst cf1) (snd cf1) i / W cf1 I \<noteq> 0"
          and "wt (fst cf2) (snd cf2) j / W cf2 (F I) \<noteq> 0"
        from \<open>I \<in> P\<close> ij P(2) FP(2) have br: "i < brn (fst cf1)" "j < brn (fst cf2)"
          by (auto dest: part_is_subset)
        show "dist (Ps (cont_eff cf1 i)) (Ps (cont_eff cf2 j)) \<le>
          Pn (cont_eff cf1 i) n' + Pn (cont_eff cf2 j) m'"
        proof (rule less.hyps)
          show "n' + m' < n + m" using nm by simp
          show "proper (fst (cont_eff cf1 i))" "proper (fst (cont_eff cf2 j))"
            using br less.prems by (auto simp: cont_eff)
          show "fst (cont_eff cf1 i) \<approx>01 fst (cont_eff cf2 j)"
            "snd (cont_eff cf1 i) \<approx> snd (cont_eff cf2 j)"
            using cont[OF \<open>I \<in> P\<close> \<open>I \<noteq> I0\<close> ij] eff[OF \<open>I \<in> P\<close> \<open>I \<noteq> I0\<close> ij] by (auto simp: cont_eff)
        qed
      next
        show "(\<Sum>b\<in>F I. wt (fst cf2) (snd cf2) b / W cf2 (F I)) = 1"
          "(\<Sum>b\<in>I. wt (fst cf1) (snd cf1) b / W cf1 I) = 1"
          using W by (auto simp: sum_divide_distrib[symmetric] sum_nonneg W_def)
      qed auto }
    note dist_n'_m' = this

    { fix I assume "I \<in> P" "I \<noteq> I0" and W: "W cf1 I = 0 \<longleftrightarrow> W cf2 (F I) = 0"
      have "dist (ps cf1 I) (ps cf2 (F I)) \<le> pn cf1 I n' + pn cf2 (F I) m'"
      proof cases
        assume "W cf2 (F I) = 0"
        then have "W cf2 (F I) = 0" "W cf1 I = 0" by (auto simp: W)
        then show ?thesis by (simp add: ps_def pn_def)
      next
        assume "W cf2 (F I) \<noteq> 0"
        then have "W cf1 I \<noteq> 0" "W cf2 (F I) \<noteq> 0" by (auto simp: W)
        from dist_n'_m'[OF \<open>I \<in> P\<close> \<open>I \<noteq> I0\<close> this] show ?thesis .
      qed }
    note dist_n'_m'_W_iff = this

    { fix I j assume W: "W cf2 (F I0) \<noteq> 0"
      from \<open>I0 \<in> P\<close> have "dist (\<Sum>i\<in>{()}. 1 * Ps cf1) (ps cf2 (F I0)) \<le> (\<Sum>i\<in>{()}. 1 * Pn cf1 n) + pn cf2 (F I0) m'"
        unfolding ps_def pn_def
      proof (intro dist_weighted_sum)
        fix j assume "j \<in> F I0"
        with FP(2) \<open>I0 \<in> P\<close> have br: "j < brn (fst cf2)"
          by (auto dest: part_is_subset)
        show "dist (Ps cf1) (Ps (cont_eff cf2 j)) \<le> Pn cf1 n + Pn (cont_eff cf2 j) m'"
        proof (rule less.hyps)
          show "n + m' < n + m" using nm by simp
          show "proper (fst cf1)" "proper (fst (cont_eff cf2 j))"
            using br by (auto simp: cont_eff)
          show "fst cf1 \<approx>01 fst (cont_eff cf2 j)"
            "snd cf1 \<approx> snd (cont_eff cf2 j)"
            using FI0[OF \<open>j \<in> F I0\<close>] \<open>snd cf1 \<approx> snd cf2\<close>
            by (auto simp: cont_eff intro: indis_trans)
        qed
      next
        show "(\<Sum>b\<in>F I0. wt (fst cf2) (snd cf2) b / W cf2 (F I0)) = 1"
          using W \<open>I0 \<in> P\<close> by (auto simp: sum_divide_distrib[symmetric] sum_nonneg W_def)
      qed auto
      then have "dist (Ps cf1) (ps cf2 (F I0)) \<le> Pn cf1 n + pn cf2 (F I0) m'"
        by simp }
    note dist_n_m' = this

    { fix I j assume W: "W cf1 I0 \<noteq> 0"
      from \<open>I0 \<in> P\<close> have "dist (ps cf1 I0) (\<Sum>i\<in>{()}. 1 * Ps cf2) \<le> pn cf1 I0 n' + (\<Sum>i\<in>{()}. 1 * Pn cf2 m)"
        unfolding ps_def pn_def
      proof (intro dist_weighted_sum)
        fix i assume "i \<in> I0"
        with P(2) \<open>I0 \<in> P\<close> have br: "i < brn (fst cf1)"
          by (auto dest: part_is_subset)
        show "dist (Ps (cont_eff cf1 i)) (Ps cf2) \<le> Pn (cont_eff cf1 i) n' + Pn cf2 m"
        proof (rule less.hyps)
          show "n' + m < n + m" using nm by simp
          show "proper (fst (cont_eff cf1 i))" "proper (fst cf2)"
            using br less.prems by (auto simp: cont_eff)
          show "fst (cont_eff cf1 i) \<approx>01 fst cf2"
            "snd (cont_eff cf1 i) \<approx> snd cf2"
            using I0[OF \<open>i \<in> I0\<close>] \<open>snd cf1 \<approx> snd cf2\<close>
            by (auto simp: cont_eff intro: indis_trans indis_sym)
        qed
      next
        show "(\<Sum>b\<in>I0. wt (fst cf1) (snd cf1) b / W cf1 I0) = 1"
          using W \<open>I0 \<in> P\<close> by (auto simp: sum_divide_distrib[symmetric] sum_nonneg W_def)
      qed auto
      then have "dist (ps cf1 I0) (Ps cf2) \<le> pn cf1 I0 n' + Pn cf2 m"
        by simp }
    note dist_n'_m = this

    have S_measurable[measurable]: "\<And>cf. Measurable.pred T.S (S cf)"
      unfolding S_def[abs_def]
      by measurable

    { fix cf' cf assume cf[simp]: "proper (fst cf)" and cf': "cf' \<in> G cf"
      let ?S = "\<lambda>bT n. qsend bT = enat n \<and> snd (bT !! n) \<approx> s"
      { fix bT n assume *: "?S (cf ## cf' ## bT) n" have "S cf' bT"
        proof (cases n)
          case 0 with * cf' show ?thesis
            by (auto simp: S_def enat_0 sfirst_Stream G_eq split: if_split_asm intro!: exI[of _ 0])
               (blast intro: indis_trans indis_sym discrCf_eff_indis)
        next
          case (Suc n) with * cf' show "S cf' bT"
            by (auto simp: eSuc_enat[symmetric] sfirst_Stream S_def split: if_split_asm)
        qed }
      moreover
      { fix bT n assume "?S (cf' ## bT) n" with cf' have "?S (cf ## cf' ## bT) (if discrCf cf then 0 else Suc n)"
          by (auto simp: eSuc_enat[symmetric] enat_0[symmetric] sfirst_Stream G_eq split: if_split_asm)
             (blast intro: indis_trans indis_sym discrCf_eff_indis)
        then have "S cf (cf' ## bT)"
          by (auto simp: S_def) }
      ultimately have "AE bT in T.T cf'. S cf (cf' ## bT) = S cf' bT"
        by (auto simp: S_def) }
    note S_sets = this

    { fix cf :: "('test, 'atom, 'choice) cmd \<times> 'state" and P I0 S n st
      assume cf[simp]: "proper (fst cf)" and P: "part {..<brn (fst cf)} P" and "finite P" "I0 \<in> P"

      { fix I i assume "I \<in> P" "i \<in> I"
        with P have "0 \<le> wt (fst cf) (snd cf) i"
          by (auto dest: part_is_subset intro!: wt_ge_0) }
      note wt_nneg[simp] = this

      assume S_measurable[measurable]: "\<And>cf n. Measurable.pred T.S (\<lambda>bT. S cf n bT)"
        and S_next: "\<And>cf cf' n. proper (fst cf) \<Longrightarrow> cf' \<in> G cf \<Longrightarrow>
          AE bT in T.T cf'. S cf (Suc n) (cf' ## bT) = S cf' n bT"
      have finite_I: "\<And>I. I \<in> P \<Longrightarrow> finite I"
        using finite_subset[OF part_is_subset[OF P]] by blast
      let ?P = "\<lambda>I. \<Sum>i\<in>I. wt (fst cf) (snd cf) i * \<P>(bT in T.T (cont_eff cf i). S (cont_eff cf i) n bT)"
      let ?P' = "\<lambda>I. W cf I * (\<Sum>i\<in>I. wt (fst cf) (snd cf) i / W cf I * \<P>(bT in T.T (cont_eff cf i). S (cont_eff cf i) n bT))"
      have "\<P>(bT in T.T cf. S cf (Suc n) bT) = (\<integral>cf'. \<P>(bT in T.T cf'. S cf' n bT) \<partial>trans cf)"
        apply (subst T.prob_T[OF S_measurable])
        apply (intro integral_cong_AE)
        apply (auto simp: AE_measure_pmf_iff intro!: T.prob_eq_AE S_next simp del: space_T)
        apply auto
        done
      also have "\<dots> = (\<Sum>I\<in>P. ?P I)"
        unfolding integral_trans[OF cf] by (simp add: part_sum[OF P])
      also have "\<dots> = (\<Sum>I\<in>P. ?P' I)"
        using finite_I
        by (auto intro!: sum.cong simp add: sum_distrib_left sum_nonneg_eq_0_iff W_def)
      also have "\<dots> = ?P' I0 + (\<Sum>I\<in>P-{I0}. ?P' I)"
        unfolding sum.remove[OF \<open>finite P\<close> \<open>I0 \<in> P\<close>] ..
      finally have "\<P>(bT in T.T cf. S cf (Suc n) bT) = \<dots>" . }
    note P_split = this

    have Ps1: "Ps cf1 = W cf1 I0 * ps cf1 I0 + (\<Sum>I\<in>P-{I0}. W cf1 I * ps cf1 I)"
      unfolding Ps_def ps_def using P(2) \<open>finite P\<close> \<open>I0 \<in> P\<close> by (intro P_split S_sets) simp_all

    have "Ps cf2 = W cf2 (F I0) * ps cf2 (F I0) + (\<Sum>I\<in>F`P-{F I0}. W cf2 I * ps cf2 I)"
      unfolding Ps_def ps_def using FP(2) \<open>finite P\<close> \<open>I0 \<in> P\<close> by (intro P_split S_sets) simp_all
    moreover have F_diff: "F ` P - {F I0} = F ` (P - {I0})"
      by (auto simp: \<open>inj_on F P\<close>[THEN inj_on_eq_iff] \<open>I0 \<in> P\<close>)
    ultimately have Ps2: "Ps cf2 = W cf2 (F I0) * ps cf2 (F I0) + (\<Sum>I\<in>P-{I0}. W cf2 (F I) * ps cf2 (F I))"
      by (simp add: sum.reindex \<open>inj_on F (P-{I0})\<close>)

    have Pn1: "Pn cf1 n = W cf1 I0 * pn cf1 I0 n' + (\<Sum>I\<in>P-{I0}. W cf1 I * pn cf1 I n')"
      unfolding Pn_def pn_def nm using P(2) \<open>finite P\<close> \<open>I0 \<in> P\<close> by (intro P_split) (simp_all add: N_def)

    have "Pn cf2 m = W cf2 (F I0) * pn cf2 (F I0) m' + (\<Sum>I\<in>F`P-{F I0}. W cf2 I * pn cf2 I m')"
      unfolding Pn_def pn_def nm using FP(2) \<open>finite P\<close> \<open>I0 \<in> P\<close> by (intro P_split) (simp_all add: N_def)
    with F_diff have Pn2: "Pn cf2 m = W cf2 (F I0) * pn cf2 (F I0) m' + (\<Sum>I\<in>P-{I0}. W cf2 (F I) * pn cf2 (F I) m')"
      by (simp add: sum.reindex \<open>inj_on F (P-{I0})\<close>)

    show ?thesis
    proof cases
      assume "W cf1 I0 = 1 \<or> W cf2 (F I0) = 1"
      then show ?thesis
      proof
        assume *: "W cf1 I0 = 1"
        then have "W cf1 I0 = W cf1 {..<brn (fst cf1)}" by (simp add: W_def)
        also have "\<dots> = W cf1 I0 + (\<Sum>I\<in>P - {I0}. W cf1 I)"
          unfolding \<open>part {..<brn (fst cf1)} P\<close>[THEN part_sum] W_def
          unfolding sum.remove[OF \<open>finite P\<close> \<open>I0 \<in> P\<close>] ..
        finally have "(\<Sum>I\<in>P - {I0}. W cf1 I) = 0" by simp
        then have "\<forall>I\<in>P - {I0}. W cf1 I = 0"
          using \<open>finite P\<close> by (subst (asm) sum_nonneg_eq_0_iff) auto
        then have "Ps cf1 = ps cf1 I0" "Pn cf1 n = pn cf1 I0 n'"
          unfolding Ps1 Pn1 * by simp_all
        moreover note dist_n'_m *
        ultimately show ?thesis by simp
      next
        assume *: "W cf2 (F I0) = 1"
        then have "W cf2 (F I0) = W cf2 {..<brn (fst cf2)}" by (simp add: W_def)
        also have "\<dots> = W cf2 (F I0) + (\<Sum>I\<in>F ` P - {F I0}. W cf2 I)"
          unfolding FP(2)[THEN part_sum] W_def
          unfolding sum.remove[OF FP'] ..
        finally have "(\<Sum>I\<in>F`P - {F I0}. W cf2 I) = 0" by simp
        then have "\<forall>I\<in>F`P - {F I0}. W cf2 I = 0"
          using \<open>finite P\<close> by (subst (asm) sum_nonneg_eq_0_iff) auto
        then have "Ps cf2 = ps cf2 (F I0)" "Pn cf2 m = pn cf2 (F I0) m'"
          unfolding Ps2 Pn2 * by (simp_all add: F_diff)
        moreover note dist_n_m' *
        ultimately show ?thesis by simp
      qed
    next
      assume W_neq1: "\<not> (W cf1 I0 = 1 \<or> W cf2 (F I0) = 1)"
      moreover
      { fix cf :: "('test, 'atom, 'choice) cmd \<times> 'state" and I P
        assume "proper (fst cf)" "part {..<brn (fst (cf))} P" "I \<in> P"
        then have "W cf I \<le> W cf {..<brn (fst (cf))}"
          unfolding W_def
          by (intro sum_mono2 part_is_subset) auto
        then have "W cf I \<le> 1" using \<open>proper (fst cf)\<close> by (simp add: W_def) }
      ultimately have wt_less1: "W cf1 I0 < 1" "W cf2 (F I0) < 1"
        using FP(2) FP'(2) P(2) \<open>I0 \<in> P\<close>
        unfolding le_less by blast+

      { fix I assume *: "I \<in> P - {I0}"
        have "W cf1 I = 0 \<longleftrightarrow> W cf2 (F I) = 0"
          using wt[OF * wt_less1] wt_less1 by auto
        with * have "dist (ps cf1 I) (ps cf2 (F I)) \<le> pn cf1 I n' + pn cf2 (F I) m'"
          by (intro dist_n'_m'_W_iff) auto }
      note dist_eps = this

      { fix a b c d :: real
        have "dist a b = dist ((a - c) + c) ((b - d) + d)" by simp
        also have "\<dots> \<le> dist (a - c) (b - d) + dist c d"
          using dist_triangle_add .
        finally have "dist a b \<le> dist (a - c) (b - d) + dist c d" . }
      note dist_triangle_diff = this

      have dist_diff_diff: "\<And>a b c d::real. dist (a - b) (c - d) \<le> dist a b + dist c d"
        unfolding dist_real_def by auto

      let ?v0 = "W cf1 I0" and ?w0 = "W cf2 (F I0)"
      let ?v1 = "1 - ?v0" and ?w1 = "1 - ?w0"
      let ?wQ = "(Ps cf2 - ?w0 * ps cf2 (F I0)) / ?w1"
      let ?wP = "(Ps cf1 - ?v0 * ps cf1 I0) / ?v1"
      let ?D = "(?w0 * ?v1 * Ps cf1 + ?w1 * ?v0 * ps cf1 I0)"
      let ?E = "(?v0 * ?w1 * Ps cf2 + ?v1 * ?w0 * ps cf2 (F I0))"

      have w0v0_less1: "?w0 * ?v0 < 1 * 1"
        using wt_less1 \<open>I0 \<in> P\<close> by (intro mult_strict_mono) auto
      then have neg_w0v0_nonneg: "0 \<le> 1 - ?w0 * ?v0" by simp

      let ?e1 = "(\<Sum>I\<in>P-{I0}. W cf1 I / ?v1 * pn cf1 I n') +
            (\<Sum>I\<in>P-{I0}. W cf2 (F I) / ?w1 * pn cf2 (F I) m')"
      have "dist ((1 - ?w0 * ?v0) * Ps cf1) ((1 - ?w0 * ?v0) * Ps cf2) \<le>
        dist ((1 - ?w0 * ?v0) * Ps cf1 - ?D) ((1 - ?w0 * ?v0) * Ps cf2 - ?E) + dist ?D ?E"
        by (rule dist_triangle_diff)
      also have "\<dots> \<le> ?v1 * ?w1 * ?e1 + (?v1 * ?w0 * (Pn cf1 n + pn cf2 (F I0) m') + ?w1 * ?v0 * (pn cf1 I0 n' + Pn cf2 m))"
      proof (rule add_mono)
        { have "?wP = (\<Sum>I\<in>P-{I0}. W cf1 I * ps cf1 I) / ?v1"
            unfolding Ps1 by (simp add: field_simps)
          also have "\<dots> = (\<Sum>I\<in>P-{I0}. W cf1 I / ?v1 * ps cf1 I)"
            by (subst sum_divide_distrib) simp
          finally have "?wP = (\<Sum>I\<in>P-{I0}. W cf1 I / ?v1 * ps cf1 I)" . }
        moreover
        { have "?wQ = (\<Sum>I\<in>P-{I0}. W cf2 (F I) * ps cf2 (F I)) / ?w1"
            using Ps2 by (simp add: field_simps)
          also have "\<dots> = (\<Sum>I\<in>P-{I0}. W cf2 (F I) / ?w1 * ps cf2 (F I))"
            by (subst sum_divide_distrib) simp
          also have "\<dots> = (\<Sum>I\<in>P-{I0}. W cf1 I / ?v1 * ps cf2 (F I))"
            using wt[OF _ wt_less1] by simp
          finally have "?wQ = (\<Sum>I\<in>P-{I0}. W cf1 I / ?v1 * ps cf2 (F I))" . }
        ultimately
        have "dist ?wP ?wQ \<le> (\<Sum>I\<in>P-{I0}. W cf1 I / ?v1 * (pn cf1 I n' + pn cf2 (F I) m'))"
          using wt_less1 dist_eps
          by (simp, intro dist_sum)
             (simp add: sum_nonneg divide_le_cancel mult_le_cancel_left not_le[symmetric] W1_nneg)
        also have "\<dots> = ?e1"
          unfolding sum.distrib[symmetric] using  wt[OF _ wt_less1]
          by (simp add: field_simps add_divide_distrib)
        finally have "dist (?v1 * ?w1 * ?wP) (?v1 * ?w1 * ?wQ) \<le> ?v1 * ?w1 * ?e1"
          using wt_less1 unfolding dist_mult by simp
        also {
          have "?v1 * ?w1 * ?wP = ?w1 * (?v0 * Ps cf1 + ?v1 * Ps cf1) - ?w1 * ?v0 * ps cf1 I0"
            using wt_less1 unfolding divide_eq_eq by (simp add: field_simps)
          also have "\<dots> = (1 - ?w0 * ?v0) * Ps cf1 - ?D"
            by (simp add: field_simps)
          finally have "?v1 * ?w1 * ?wP = (1 - ?w0 * ?v0) * Ps cf1 - ?D" . }
        also {
          have "?v1 * ?w1 * ?wQ = ?v1 * (?w0 * Ps cf2 + ?w1 * Ps cf2) - ?v1 * ?w0 * (ps cf2 (F I0))"
            using wt_less1 unfolding divide_eq_eq by (simp add: field_simps)
          also have "\<dots> = (1 - ?w0 * ?v0) * Ps cf2 - ?E"
            by (simp add: field_simps)
          finally have "?v1 * ?w1 * ?wQ = (1 - ?w0 * ?v0) * Ps cf2 - ?E" . }
        finally show "dist ((1 - ?w0 * ?v0) * Ps cf1 - ?D) ((1 - ?w0 * ?v0) * Ps cf2 - ?E) \<le> ?v1 * ?w1 * ?e1" .
      next
        have "dist ?D ?E = dist
          (?v1 * ?w0 * Ps cf1 - ?v1 * ?w0 * ps cf2 (F I0))
          (?w1 * ?v0 * Ps cf2 - ?w1 * ?v0 * ps cf1 I0)"
          unfolding dist_real_def by (simp add: ac_simps)
        also have "\<dots> \<le> dist (?v1 * ?w0 * Ps cf1) (?v1 * ?w0 * ps cf2 (F I0)) +
          dist (?w1 * ?v0 * Ps cf2) (?w1 * ?v0 * ps cf1 I0)"
          using dist_diff_diff .
        also have "\<dots> \<le> ?v1 * ?w0 * (Pn cf1 n + pn cf2 (F I0) m') + ?w1 * ?v0 * (pn cf1 I0 n' + Pn cf2 m)"
        proof (rule add_mono)
          show "dist (?v1 * ?w0 * Ps cf1) (?v1 * ?w0 * ps cf2 (F I0)) \<le> ?v1 * ?w0 * (Pn cf1 n + pn cf2 (F I0) m')"
            using wt_less1 dist_n_m' \<open>I0 \<in> P\<close>
            by (simp add: sum_nonneg mult_le_cancel_left not_le[symmetric] mult_le_0_iff W2_nneg)
          show "dist (?w1 * ?v0 * Ps cf2) (?w1 * ?v0 * ps cf1 I0) \<le> ?w1 * ?v0 * (pn cf1 I0 n' + Pn cf2 m)"
            using wt_less1 dist_n'_m \<open>I0 \<in> P\<close>
            by (subst dist_commute)
               (simp add: sum_nonneg mult_le_cancel_left not_le[symmetric] mult_le_0_iff W1_nneg)
        qed
        finally show "dist ?D ?E \<le> ?v1 * ?w0 * (Pn cf1 n + pn cf2 (F I0) m') + ?w1 * ?v0 * (pn cf1 I0 n' + Pn cf2 m)" .
      qed
      also  have "\<dots> = ?w1 * (\<Sum>I\<in>P-{I0}. W cf1 I * pn cf1 I n') + ?v1 * (\<Sum>I\<in>P-{I0}. W cf2 (F I) * pn cf2 (F I) m') +
        ?v1 * ?w0 * (Pn cf1 n + pn cf2 (F I0) m') + ?w1 * ?v0 * (pn cf1 I0 n' + Pn cf2 m)"
        using W_neq1 by (simp add: sum_divide_distrib[symmetric] add_divide_eq_iff divide_add_eq_iff)
      also have "\<dots> = (1 - ?w0 * ?v0) * (Pn cf1 n + Pn cf2 m)"
        unfolding Pn1 Pn2 by (simp add: field_simps)
      finally show "dist (Ps cf1) (Ps cf2) \<le> Pn cf1 n + Pn cf2 m"
        using neg_w0v0_nonneg w0v0_less1 by (simp add: mult_le_cancel_left)
    qed
  qed
qed

lemma AE_T_max_qsend_time:
  fixes cf and e :: real assumes AE: "AE bT in T.T cf. qsend (cf ## bT) < \<infinity>" "0 < e"
  shows "\<exists>N. \<P>(bT in T.T cf. \<not> discrCf ((cf ## bT) !! N)) < e"
proof -
  from AE_T_max_sfirst[OF _ AE] obtain N :: nat
    where "\<P>(bT in T.T cf. N < qsend (cf ## bT)) < e"
    by auto
  also have "\<P>(bT in T.T cf. N < qsend (cf ## bT)) = \<P>(bT in T.T cf. \<not> discrCf ((cf ## bT) !! N))"
    using less_qsend_iff_not_discrCf[of cf] AE_T_enabled[of cf]
    by (intro T.prob_eq_AE) auto
  finally show ?thesis ..
qed

lemma Ps_eq:
  fixes cf1 cf2 s and S
  defines "S cf bT \<equiv> \<exists>n. qsend (cf ## bT) = n \<and> eff_at cf bT n \<approx> s"
  defines "Ps cf \<equiv> \<P>(bT in T.T cf. S cf bT)"
  assumes qsterm1: "AE bT in T.T cf1. qsend (cf1 ## bT) < \<infinity>"
  assumes qsterm2: "AE bT in T.T cf2. qsend (cf2 ## bT) < \<infinity>"
  and bisim: "proper (fst cf1)" "proper (fst cf2)" "fst cf1 \<approx>01 fst cf2" "snd cf1 \<approx> snd cf2"
  shows "Ps cf1 = Ps cf2"
proof -
  let ?nT = "\<lambda>cf n bT. \<not> discrCf ((cf ## bT) !! n)"
  let ?PnT = "\<lambda>cf n. \<P>(bT in T.T cf. ?nT cf n bT)"

   have "dist (Ps cf1) (Ps cf2) = 0"
     unfolding dist_real_def
   proof (rule field_abs_le_zero_epsilon)
     fix e ::real assume "0 < e"
     then have "0 < e / 2" by auto
     from AE_T_max_qsend_time[OF qsterm1 this] AE_T_max_qsend_time[OF qsterm2 this]
     obtain n m where "?PnT cf1 n < e / 2" "?PnT cf2 m < e / 2" by auto
     moreover have "dist (Ps cf1) (Ps cf2) \<le> ?PnT cf1 n + ?PnT cf2 m"
       unfolding Ps_def S_def using bisim by (rule dist_Ps_upper_bound)
     ultimately show "\<bar>Ps cf1 - Ps cf2\<bar> \<le> e"
       unfolding dist_real_def by auto
   qed
   then show "Ps cf1 = Ps cf2" by auto
qed

lemma siso_trace:
  assumes "siso c" "s \<approx> t" "enabled (c, t) cfT"
  shows "siso (cont_at (c, s) cfT n)"
    and "cont_at (c, s) cfT n = cont_at (c, t) cfT n"
    and "eff_at (c, s) cfT n \<approx> eff_at (c, t) cfT n"
  using assms
proof (induction n arbitrary: c s t cfT)
  case (Suc n) case 1
  with Suc(1)[of "fst (shd cfT)" "snd (shd cfT)" "snd (shd cfT)" "stl cfT"] show ?case
    by (auto simp add: enabled.simps[of _ cfT] G_eq cont_eff indis_refl split: if_split_asm)
qed auto

lemma Sbis_trace:
  assumes "proper (fst cf1)" "proper (fst cf2)" "fst cf1 \<approx>s fst cf2" "snd cf1 \<approx> snd cf2"
  shows "\<P>(cfT in T.T cf1. eff_at cf1 cfT n \<approx> s') = \<P>(cfT in T.T cf2. eff_at cf2 cfT n \<approx> s')"
    (is "?P cf1 n = ?P cf2 n")
using assms proof (induct n arbitrary: cf1 cf2)
  case 0
  show ?case
  proof cases
    assume "snd cf1 \<approx> s'"
    with \<open>snd cf1 \<approx> snd cf2\<close> \<open>fst cf1 \<approx>s fst cf2\<close> have "snd cf1 \<approx> s'" "snd cf2 \<approx> s'"
      by (metis indis_trans indis_sym)+
    then show ?case
      using T.prob_space by simp
  next
    assume "\<not> snd cf1 \<approx> s'"
    with \<open>snd cf1 \<approx> snd cf2\<close> \<open>fst cf1 \<approx>s fst cf2\<close> have "\<not> snd cf1 \<approx> s' \<and> \<not> snd cf2 \<approx> s'"
      by (metis indis_trans indis_sym)
    then show ?case
      by auto
  qed
next
  case (Suc n)
  note \<open>proper (fst cf1)\<close>[simp] \<open>proper (fst cf2)\<close>[simp]

  from Sbis_mC_C \<open>fst cf1 \<approx>s fst cf2\<close> \<open>snd cf1 \<approx> snd cf2\<close>
  obtain P F where mP: "mC_C Sbis (fst cf1) (fst cf2) (snd cf1) (snd cf2) P F"
    by blast
  then have
    P: "part {..<brn (fst cf1)} P" "{} \<notin> P" and
    FP: "part {..<brn (fst cf2)} (F`P)" "{} \<notin> F ` P" "inj_on F P" and
    W: "\<And>I. I \<in> P \<Longrightarrow> sum (wt (fst cf1) (snd cf1)) I = sum (wt (fst cf2) (snd cf2)) (F I)" and
    eff: "\<And>I i j. I \<in> P \<Longrightarrow> i \<in> I \<Longrightarrow> j \<in> F I \<Longrightarrow>
      eff (fst cf1) (snd cf1) i \<approx> eff (fst cf2) (snd cf2) j" and
    cont: "\<And>I i j. I \<in> P \<Longrightarrow> i \<in> I \<Longrightarrow> j \<in> F I \<Longrightarrow>
      cont (fst cf1) (snd cf1) i \<approx>s cont (fst cf2) (snd cf2) j"
    unfolding mC_C_def mC_C_eff_cont_def mC_C_part_def mC_C_wt_def by metis+
  { fix cf1 :: "('test, 'atom, 'choice) cmd \<times> 'state" and P assume cf[simp]: "proper (fst cf1)" and P: "part {..<brn (fst cf1)} P"
    have "?P cf1 (Suc n) = (\<integral>cf'. ?P cf' n \<partial>trans cf1)"
      by (subst T.prob_T) auto
    also have "\<dots> = (\<Sum>b<brn (fst cf1). wt (fst cf1) (snd cf1) b * ?P (cont_eff cf1 b) n)"
      unfolding integral_trans[OF cf] ..
    also have "\<dots> = (\<Sum>I\<in>P. \<Sum>b\<in>I. wt (fst cf1) (snd cf1) b * ?P (cont_eff cf1 b) n)"
      unfolding part_sum[OF P] ..
    finally have "?P cf1 (Suc n) = \<dots>" . }
  note split = this

  { fix I i assume "I \<in> P" "i \<in> I"
    with \<open>proper (fst cf1)\<close> have "i < brn (fst cf1)"
      using part_is_subset[OF P(1) \<open>I \<in> P\<close>] by auto }
  note brn_cf[simp] = this

  { fix I i assume "I \<in> P" "i \<in> F I"
    with \<open>proper (fst cf2)\<close> have "i < brn (fst cf2)"
      using part_is_subset[OF FP(1), of "F I"] by auto }
  note brn_cf2[simp] = this

  { fix I assume "I \<in> P"
    with \<open>{} \<notin> P\<close> obtain i where "i \<in> I" by (metis all_not_in_conv)
    from \<open>I \<in> P\<close> FP have "F I \<noteq> {}" "F I \<subseteq> {..<brn (fst cf2)}"
      by (auto simp: part_is_subset)
    then obtain j where "j < brn (fst cf2)" "j \<in> F I" by auto
    { fix b assume "b \<in> F I"
      then have "?P (cont_eff cf1 i) n = ?P (cont_eff cf2 b) n"
        using \<open>I \<in> P\<close> \<open>i \<in> I\<close> cont eff
        by (intro Suc) (auto simp add: cont_eff) }
    note cont_d_const = this[symmetric]
    { fix a assume "a \<in> I"
      with \<open>I \<in> P\<close> \<open>i \<in> I\<close> \<open>j \<in> F I\<close> cont eff
      have "?P (cont_eff cf1 i) n = ?P (cont_eff cf2 j) n \<and>
        ?P (cont_eff cf1 a) n = ?P (cont_eff cf2 j) n"
        by (intro conjI Suc) (auto simp add: cont_eff)
      then have "?P (cont_eff cf1 a) n = ?P (cont_eff cf1 i) n" by simp }
    then have "(\<Sum>b\<in>I. wt (fst cf1) (snd cf1) b * ?P (cont_eff cf1 b) n) =
        (\<Sum>b\<in>I. wt (fst cf1) (snd cf1) b) * ?P (cont_eff cf1 i) n"
      by (simp add: sum_distrib_right)
    also have "\<dots> = (\<Sum>b\<in>F I. wt (fst cf2) (snd cf2) b) * ?P (cont_eff cf1 i) n"
      using W \<open>I \<in> P\<close> by auto
    also have "\<dots> = (\<Sum>b\<in>F I. wt (fst cf2) (snd cf2) b * ?P (cont_eff cf2 b) n)"
      using cont_d_const by (auto simp add: sum_distrib_right)
    finally have "(\<Sum>b\<in>I. wt (fst cf1) (snd cf1) b * ?P (cont_eff cf1 b) n) = \<dots>" . }
  note sum_eq = this

  have "?P cf1 (Suc n) = (\<Sum>I\<in>P. \<Sum>b\<in>I. wt (fst cf1) (snd cf1) b * ?P (cont_eff cf1 b) n)"
    using \<open>proper (fst cf1)\<close> P(1) by (rule split)
  also have "\<dots> = (\<Sum>I\<in>P. \<Sum>b\<in>F I. wt (fst cf2) (snd cf2) b * ?P (cont_eff cf2 b) n)"
    using sum_eq by simp
  also have "\<dots> = (\<Sum>I\<in>F`P. \<Sum>b\<in>I. wt (fst cf2) (snd cf2) b * ?P (cont_eff cf2 b) n)"
    using \<open>inj_on F P\<close> by (simp add: sum.reindex)
  also have "\<dots> = ?P cf2 (Suc n)"
    using \<open>proper (fst cf2)\<close> FP(1) by (rule split[symmetric])
  finally show ?case .
qed

subsection \<open>Final Theorems\<close>

theorem ZObis_eSec: "\<lbrakk>proper c; c \<approx>01 c; aeT c\<rbrakk> \<Longrightarrow> eSec c"
  by (auto simp: aeT_def eSec_def intro!: Ps_eq[simplified])

theorem Sbis_amSec: "\<lbrakk>proper c; c \<approx>s c\<rbrakk> \<Longrightarrow> amSec c"
  by (auto simp: amSec_def intro!: Sbis_trace[simplified])

theorem amSec_eSec:
  assumes [simp]: "proper c" and "aeT c" "amSec c" shows "eSec c"
proof (unfold eSec_def, intro allI impI)
  fix s1 s2 t assume "s1 \<approx> s2"
  let ?T = "\<lambda>s bT. \<exists>n. qsend ((c, s) ## bT) = n \<and> eff_at (c,s) bT n \<approx> t"
  let ?P = "\<lambda>s. \<P>(bT in T.T (c, s). ?T s bT)"

  have "dist (?P s1) (?P s2) = 0"
    unfolding dist_real_def
  proof (rule field_abs_le_zero_epsilon)
    fix e :: real assume "0 < e"
    then have "0 < e / 2" by simp
    let ?N = "\<lambda>s n bT. \<not> discrCf (((c,s) ## bT) !! n)"
    from AE_T_max_qsend_time[OF _ \<open>0 < e / 2\<close>, of "(c,s1)"]
    obtain N1 where N1: "\<P>(bT in T.T (c, s1). ?N s1 N1 bT) < e / 2"
      using \<open>aeT c\<close> unfolding aeT_def by auto
    from AE_T_max_qsend_time[OF _ \<open>0 < e / 2\<close>, of "(c,s2)"]
    obtain N2 where N2: "\<P>(bT in T.T (c, s2). ?N s2 N2 bT) < e / 2"
      using \<open>aeT c\<close> unfolding aeT_def by auto
    define N where "N = max N1 N2"

    let ?Tn = "\<lambda>n s bT. eff_at (c,s) bT n \<approx> t"

    have "dist \<P>(bT in T.T (c, s1). ?T s1 bT) \<P>(bT in T.T (c, s1). ?Tn N s1 bT) \<le>
        \<P>(bT in T.T (c, s1). ?N s1 N1 bT)"
      using \<open>aeT c\<close>[unfolded aeT_def, rule_format] AE_T_enabled AE_space
    proof (intro T.prob_dist, eventually_elim, intro impI)
      fix bT assume bT: "enabled (c,s1) bT" and "\<not> \<not> discrCf (((c,s1) ## bT) !! N1)"
      with bT have "qsend ((c,s1) ## bT) \<le> N1"
        using less_qsend_iff_not_discrCf[of "(c,s1)" bT N1] by simp
      then show "?T s1 bT \<longleftrightarrow> ?Tn N s1 bT"
        using bT
        by (cases "qsend ((c, s1) ## bT)")
           (auto intro!: enabled_qsend_indis del: iffI simp: N_def)
    qed measurable
    moreover
    have "dist \<P>(bT in T.T (c, s2). ?T s2 bT) \<P>(bT in T.T (c, s2). ?Tn N s2 bT) \<le>
        \<P>(bT in T.T (c, s2). ?N s2 N2 bT)"
      using \<open>aeT c\<close>[unfolded aeT_def, rule_format] AE_T_enabled AE_space
    proof (intro T.prob_dist, eventually_elim, intro impI)
      fix bT assume bT: "enabled (c,s2) bT" "\<not> \<not> discrCf (((c,s2) ## bT) !! N2)"
      with bT have "qsend ((c,s2) ## bT) \<le> N2"
        using less_qsend_iff_not_discrCf[of "(c,s2)" bT N2] by simp
      then show "?T s2 bT \<longleftrightarrow> ?Tn N s2 bT"
        using bT
        by (cases "qsend ((c, s2) ## bT)")
           (auto intro!: enabled_qsend_indis del: iffI simp: N_def)
    qed measurable
    ultimately have "dist \<P>(bT in T.T (c, s1). ?T s1 bT) \<P>(bT in T.T (c, s1). ?Tn N s1 bT) +
      dist \<P>(bT in T.T (c, s2). ?T s2 bT) \<P>(bT in T.T (c, s1). ?Tn N s1 bT) \<le> e"
      using \<open>amSec c\<close>[unfolded amSec_def, rule_format, OF \<open>s1 \<approx> s2\<close>, of N t]
      using N1 N2 by simp
    from dist_triangle_le[OF this]
    show "\<bar>?P s1 - ?P s2\<bar> \<le> e" by (simp add: dist_real_def)
  qed
  then show "?P s1 = ?P s2"
    by simp
qed

end

end
