theory Option_Price_Examples imports CRR_Model

begin

text \<open> This file contains pricing results for four options in the Cox-Ross-Rubinstein model. The first section contains results
relating some functions to the more abstract counterparts that were used to prove fairness and completeness results. The second
section contains the pricing results for a few options; some path-dependent and others not. \<close>

section  \<open> Effective computation definitions and results \<close>

subsection \<open> Generation of lists of boolean elements \<close>

text \<open> The function gener-bool-list permits to generate lists of boolean elements. It is used to generate a list representative
of the range of boolean streams by the function pseudo-proj-True. \<close>

fun gener_bool_list where
"gener_bool_list 0 = {[]}"
| "gener_bool_list (Suc n) = {True # w| w. w\<in> gener_bool_list n} \<union> {False # w| w. w\<in> gener_bool_list n}"

lemma gener_bool_list_elem_length:
  shows "\<And>x. x\<in> gener_bool_list n \<Longrightarrow> length x = n"
proof (induction n)
  case 0
  fix x
  assume "x\<in> gener_bool_list 0"
  hence "x = []" by simp
  thus "length x = 0" by simp
next
  case (Suc n)
  fix x
  assume "x\<in> gener_bool_list (Suc n)"
  hence mem: "x\<in> {True # w| w. w\<in> gener_bool_list n} \<union> {False # w| w. w\<in> gener_bool_list n}" by simp
  show "length x = Suc n"
  proof (cases "x\<in> {True # w| w. w\<in> gener_bool_list n}")
    case True
    hence "\<exists>w \<in> gener_bool_list n. x = True # w" by auto
    from this obtain w where "w\<in> gener_bool_list n" and "x = True # w" by auto
    hence "length w = n" using Suc by simp
    thus "length x = Suc n" using \<open>x = True # w\<close> by simp
  next
    case False
    hence "x\<in> {False # w| w. w\<in> gener_bool_list n}" using mem by auto
    hence "\<exists>w \<in> gener_bool_list n. x = False # w" by auto
    from this obtain w where "w\<in> gener_bool_list n" and "x = False # w" by auto
    hence "length w = n" using Suc by simp
    thus "length x = Suc n" using \<open>x = False # w\<close> by simp
  qed
qed

lemma (in infinite_coin_toss_space) stake_gener_bool_list:
  shows "stake n`streams (UNIV::bool set) = gener_bool_list n"
proof (induction n)
  case 0
  thus "stake 0 ` streams UNIV = gener_bool_list 0" by auto
next
  case (Suc n)
  show "stake (Suc n) ` streams UNIV = gener_bool_list (Suc n)"
  proof -
    have "stake (Suc n)`streams (UNIV::bool set) = {s#w| s w. s\<in> UNIV \<and> w\<in> (stake n `(streams UNIV))}"
      by (metis (no_types) UNIV_bool UNIV_not_empty stake_finite_universe_induct[of UNIV n] finite.emptyI finite_insert)
    also have "... = {s#w| s w. s\<in> {True, False} \<and> w\<in> (stake n `(streams UNIV))}" by simp
    also have "... = {s#w| s w. s\<in> {True, False} \<and> w\<in> gener_bool_list n}" using Suc by simp
    also have "... = {s#w| s w. s\<in> {True} \<and> w\<in> gener_bool_list n} \<union> {s#w| s w. s\<in> { False} \<and> w\<in> gener_bool_list n}" by auto
    also have "... = {True # w | w. w\<in> gener_bool_list n} \<union> {False#w | w. w\<in> gener_bool_list n}" by auto
    also have "... = gener_bool_list (Suc n)" by simp
    finally show ?thesis .
  qed
qed

lemma (in infinite_coin_toss_space) pseudo_range_stake:
  assumes "\<And>w. f w = g (stake n w)"
  shows "(\<Sum> w\<in> range (pseudo_proj_True n). f w) = (\<Sum> y\<in> (gener_bool_list n). g y)"
proof (rule sum.reindex_cong)
  show "inj_on (\<lambda> l. shift l (sconst True)) (gener_bool_list n)" 
  proof
    fix x y
    assume "x\<in> gener_bool_list n"
    and "y\<in> gener_bool_list n"
    and "x @- sconst True = y @- sconst True"
    have "length x = n" using gener_bool_list_elem_length \<open>x\<in> gener_bool_list n\<close> by simp
    have "length y = n" using gener_bool_list_elem_length \<open>y\<in> gener_bool_list n\<close> by simp
    show "x = y"
    proof -
      have "\<forall> i < n. nth x i = nth y i"
      proof (intro allI impI)
        fix i
        assume "i < n"   
        have xi: "snth (x @- sconst True) i = nth x i" using \<open>i < n\<close> \<open>length x = n\<close> by simp
        have yi: "snth (y @- sconst True) i = nth y i" using \<open>i < n\<close> \<open>length y = n\<close> by simp
        have "snth (x @- sconst True) i = snth (y @- sconst True) i"  using \<open>x @- sconst True = y @- sconst True\<close>
          by simp
        thus "nth x i = nth y i" using xi yi by simp
      qed
      thus ?thesis using \<open>length x = n\<close> \<open>length y = n\<close> by (simp add: list_eq_iff_nth_eq)
    qed
  qed        
  have  "range (pseudo_proj_True n) = {shift l (sconst True)|l. l\<in>(stake n `streams (UNIV::bool set))} " 
    unfolding pseudo_proj_True_def by auto
  also have "... = {shift l (sconst True)|l. l\<in>(gener_bool_list n)} " using stake_gener_bool_list by simp
  also have "... = (\<lambda>l. l @- sconst True) ` gener_bool_list n" by auto
  finally show "range (pseudo_proj_True n) = (\<lambda>l. l @- sconst True) ` gener_bool_list n" .
  fix x
  assume "x\<in> gener_bool_list n"
  have "length x = n" using gener_bool_list_elem_length \<open>x\<in> gener_bool_list n\<close> by simp
  have "f (x @- sconst True) = g (stake n (x @- sconst True))" using assms by simp
  also have "... = g x" using \<open>length x = n\<close> by (simp add: stake_shift)
  finally show "f (x @- sconst True) = g x" .
qed


subsection \<open> Probability components for lists \<close>

fun lprob_comp where
"lprob_comp (p::real) [] = 1"
| "lprob_comp p (x # xs) = (if x then p else (1-p)) * lprob_comp p xs"


lemma lprob_comp_last:
  shows "lprob_comp p (xs @ [x]) = (lprob_comp p xs) * (if x then p else (1 - p))"
proof (induction xs)
  case Nil
  have "lprob_comp p (Nil @ [x]) = lprob_comp p [x]" by simp
  also have "... = (if x then p else (1 - p))" by simp
  also have "... = (lprob_comp p Nil) * (if x then p else (1 - p))" by simp
  finally show "lprob_comp p (Nil @ [x]) = (lprob_comp p Nil) * (if x then p else (1 - p))" .
next
  case (Cons a xs)
  have "lprob_comp p ((Cons a xs) @ [x]) = (if a then p else (1 - p)) * lprob_comp p (xs @ [x])" by simp
  also have "... = (if a then p else (1 - p)) * (lprob_comp p xs) * (if x then p else (1-p))" using Cons by simp
  also have "... = lprob_comp p (Cons a xs) * (if x then p else (1-p))" by simp
  finally show "lprob_comp p ((Cons a xs) @ [x]) = lprob_comp p (Cons a xs) * (if x then p else (1-p))" .
qed

lemma (in infinite_coin_toss_space) lprob_comp_stake:
  shows "(prod (prob_component pr w) {0..<matur}) = lprob_comp pr (stake matur w)"
proof (induction matur)
  case 0
  have "prod (prob_component pr w) {0..<0} = 1" by simp
  also have "... = lprob_comp pr []" by simp
  also have "... = lprob_comp pr (stake 0 w)" by simp
  finally show "prod (prob_component pr w) {0..<0} = lprob_comp pr (stake 0 w)" .
next
  case (Suc n)
  have "prod (prob_component pr w) {0..<Suc n} = prod (prob_component pr w) {0..< n} *
    (prob_component pr w n)" using prod.atLeast0_lessThan_Suc by blast 
  also have "... = lprob_comp pr (stake n w) * (prob_component pr w n)" using Suc by simp
  also have "... = lprob_comp pr (stake n w) * (if (snth w n) then pr else 1-pr)" by (simp add: prob_component_def)
  also have "... = lprob_comp pr ((stake n w) @ [snth w n])" by (simp add: lprob_comp_last)
  also have "... = lprob_comp pr (stake (Suc n) w)" by (metis Stream.stake_Suc) 
  finally show "prod (prob_component pr w) {0..<Suc n} = lprob_comp pr (stake (Suc n) w)" .
qed

subsection \<open> Geometric process applied to lists \<close>

fun lrev_geom where
"lrev_geom u d v [] = v"
| "lrev_geom u d v (x#xs) = (if x then u else d) * lrev_geom u d v xs"

fun lgeom_proc where "lgeom_proc u d v l = lrev_geom u d v (rev l)"

lemma (in infinite_coin_toss_space) geom_lgeom:
  shows "geom_rand_walk u d v n w = lgeom_proc u d v (stake n w)"
proof (induction n)
  case 0
  have "geom_rand_walk u d v 0 w = v" by simp
  also have "... = lrev_geom u d v []" by simp
  also have "... = lrev_geom u d v (rev (stake 0 w))" by simp
  also have "... = lgeom_proc u d v (stake 0 w)" by simp
  finally show "geom_rand_walk u d v 0 w = lgeom_proc u d v (stake 0 w)" .
next
  case (Suc n)
  have "snth w n = nth (stake (Suc n) w) n" using stake_nth by blast
  have "(stake n w) @ [nth (stake (Suc n) w) n] = stake (Suc n) w"
    by (metis Stream.stake_Suc lessI stake_nth)
  have "geom_rand_walk u d v (Suc n) w = ((\<lambda>True \<Rightarrow> u | False \<Rightarrow> d) (snth w n)) * geom_rand_walk u d v n w" by simp
  also have "... = (if (snth w n) then u else d) * geom_rand_walk u d v n w" by simp
  also have "... = (if (snth w n) then u else d) * lgeom_proc u d v (stake n w)" using Suc by simp
  also have "... = (if (snth w n) then u else d) * lrev_geom u d v (rev (stake n w))" by simp
  also have "... = lrev_geom u d v ((snth w n) # (rev (stake n w)))" by simp
  also have "... = lrev_geom u d v (rev ((stake n w) @ [snth w n]))" by simp 
  also have "... = lrev_geom u d v (rev ((stake n w) @ [nth (stake (Suc n) w) n]))" 
    using \<open>snth w n = nth (stake (Suc n) w) n\<close> by simp
  also have "... = lrev_geom u d v (rev (stake (Suc n) w))" 
    using \<open>(stake n w) @ [nth (stake (Suc n) w) n] = stake (Suc n) w\<close> by simp
  also have "... = lgeom_proc u d v (stake (Suc n) w)" by simp
  finally show "geom_rand_walk u d v (Suc n) w = lgeom_proc u d v (stake (Suc n) w)" .
qed

lemma lgeom_proc_take:
  assumes "i \<le> n"
  shows "lgeom_proc u d init (stake i w) = lgeom_proc u d init (take i (stake n w))"
proof -
  have "stake i w = take i (stake n w)" using assms by (simp add: min.absorb1 take_stake)
  thus ?thesis by simp
qed

subsection \<open> Effective computation of discounted values \<close>


fun det_discount where
"det_discount (r::real) 0 = 1"
| "det_discount r (Suc n) = (inverse (1+r)) * (det_discount r n)"


lemma det_discounted:
  shows "discounted_value r X n w = (det_discount r n) * (X n w)" unfolding discounted_value_def discount_factor_def
proof (induction n arbitrary: X)
  case 0
  have "inverse (disc_rfr_proc r 0 w) * X 0 w =  X 0 w" by simp
  also have "... = (det_discount r 0) * (X 0 w)" by simp
  finally show "inverse (disc_rfr_proc r 0 w) * X 0 w = (det_discount r 0) * (X 0 w)" .
next
  case (Suc n)
  have "inverse (disc_rfr_proc r (Suc n) w) * X (Suc n) w = 
    inverse ((1+r) * (disc_rfr_proc r) n w) * X (Suc n) w" by simp
  also have "... = (inverse (1+r)) * inverse ((disc_rfr_proc r) n w) * X (Suc n) w" by simp
  also have "... = (inverse (1+r)) * (det_discount r n) * X (Suc n) w" using Suc[of "\<lambda>n. X (Suc n)"] by auto
  also have "... = (det_discount r (Suc n)) * X (Suc n) w" by simp
  finally show "inverse (disc_rfr_proc r (Suc n) w) * X (Suc n) w = (det_discount r (Suc n)) * X (Suc n) w" .
qed

section \<open>Pricing results on options \<close>

subsection \<open> Call option \<close>

text \<open> A call option is parameterized by a strike K and maturity T. If S denotes the price of the (unique) risky asset at 
time T, then the option pays max(S - K, 0) at that time.\<close>

definition (in CRR_market) call_option where
"call_option (T::nat) (K::real) = (\<lambda> w. max (prices Mkt stk T w - K) 0)"

lemma (in CRR_market) call_borel:
  shows "call_option T K \<in> borel_measurable (G T)" unfolding call_option_def
proof (rule borel_measurable_max)
  show "(\<lambda>x. 0) \<in> borel_measurable (G T)" by simp
  show "(\<lambda>x. prices Mkt stk T x - K) \<in> borel_measurable (G T)"
  proof (rule borel_measurable_diff)
    show "prices Mkt stk T \<in> borel_measurable (G T)" 
      by (metis  adapt_stoch_proc_def stock_price_borel_measurable)
  qed simp
qed

lemma (in CRR_market_viable) call_option_lgeom:
  shows "call_option T K w = max ((lgeom_proc u d init (stake T w)) - K) 0"
  using geom_lgeom stk_price geometric_process unfolding call_option_def by simp

lemma (in CRR_market_viable) disc_call_option_lgeom:
  shows "(discounted_value r (\<lambda>m. (call_option T K)) T w) = 
    (det_discount r T) * (max ((lgeom_proc u d init (stake T w)) - K) 0)"
    using det_discounted[of r "\<lambda>m. call_option T K" T w] call_option_lgeom[of T K w] by simp

lemma (in CRR_market_viable) call_effect_compute:
shows "(\<Sum> w\<in> range (pseudo_proj_True matur). (prod (prob_component pr w) {0..<matur}) * 
      (discounted_value r (\<lambda>m. (call_option matur K)) matur w)) =
      (\<Sum> y\<in> (gener_bool_list matur). lprob_comp pr y * (det_discount r matur) * 
      (max ((lgeom_proc u d init (take matur y)) - K) 0))" 
proof (rule pseudo_range_stake)
  fix w
  have "prod (prob_component pr w) {0..<matur} * discounted_value r (\<lambda>m. call_option matur K) matur w =
    lprob_comp pr (stake matur w) * discounted_value r (\<lambda>m. call_option matur K) matur w"
    using lprob_comp_stake by simp 
  also have "... = lprob_comp pr (stake matur w) *
    (det_discount r matur) * (max ((lgeom_proc u d init (take matur (stake matur w))) - K) 0)" 
    using disc_call_option_lgeom[of matur K] by simp
  finally show "prod (prob_component pr w) {0..<matur} * discounted_value r (\<lambda>m. call_option matur K) matur w =
    lprob_comp pr (stake matur w) *
    (det_discount r matur) * (max ((lgeom_proc u d init (take matur (stake matur w))) - K) 0)" .
qed

fun call_price where
"call_price u d init r matur K = (\<Sum> y\<in> (gener_bool_list matur). lprob_comp ((1 + r - d) / (u - d)) y * (det_discount r matur) * 
      (max ((lgeom_proc u d init (take matur (take matur y))) - K) 0))"

text \<open> Evaluating the function above returns the fair price of a call option. \<close>

lemma (in CRR_market_viable) call_price:
  shows "fair_price Mkt 
    (call_price u d init r matur K) 
    (call_option matur K) matur"
proof -
  have "fair_price Mkt 
    (\<Sum> w\<in> range (pseudo_proj_True matur). (prod (prob_component ((1 + r - d) / (u - d)) w) {0..<matur}) * 
      (discounted_value r (\<lambda>m. (call_option matur K)) matur w)) 
    (call_option matur K) matur"
    by (rule CRR_market_fair_price, rule call_borel)
  thus ?thesis using call_effect_compute by simp
qed

subsection \<open> Put option \<close>

text \<open> A put option is also parameterized by a strike K and maturity T. If S denotes the price of the (unique) risky asset at 
time T, then the option pays max(K - S, 0) at that time. \<close>

definition (in CRR_market) put_option where
"put_option (T::nat) (K::real) = (\<lambda> w. max (K - prices Mkt stk T w) 0)"

lemma (in CRR_market) put_borel:
  shows "put_option T K \<in> borel_measurable (G T)" unfolding put_option_def
proof (rule borel_measurable_max)
  show "(\<lambda>x. 0) \<in> borel_measurable (G T)" by simp
  show "(\<lambda>x. K - prices Mkt stk T x) \<in> borel_measurable (G T)"
  proof (rule borel_measurable_diff)
    show "prices Mkt stk T \<in> borel_measurable (G T)" 
      by (metis  adapt_stoch_proc_def stock_price_borel_measurable)
  qed simp
qed

lemma (in CRR_market_viable) put_option_lgeom:
  shows "put_option T K w = max (K - (lgeom_proc u d init (stake T w))) 0"
  using geom_lgeom stk_price geometric_process unfolding put_option_def by simp

lemma (in CRR_market_viable) disc_put_option_lgeom:
  shows "(discounted_value r (\<lambda>m. (put_option T K)) T w) = 
    (det_discount r T) * (max (K - (lgeom_proc u d init (stake T w))) 0)"
    using det_discounted[of r "\<lambda>m. put_option T K" T w] put_option_lgeom[of T K w] by simp

lemma (in CRR_market_viable) put_effect_compute:
shows "(\<Sum> w\<in> range (pseudo_proj_True matur). (prod (prob_component pr w) {0..<matur}) * 
      (discounted_value r (\<lambda>m. (put_option matur K)) matur w)) =
      (\<Sum> y\<in> (gener_bool_list matur). lprob_comp pr y * (det_discount r matur) * 
      (max (K - (lgeom_proc u d init (take matur y))) 0))" 
proof (rule pseudo_range_stake)
  fix w
  have "prod (prob_component pr w) {0..<matur} * discounted_value r (\<lambda>m. put_option matur K) matur w =
    lprob_comp pr (stake matur w) * discounted_value r (\<lambda>m. put_option matur K) matur w"
    using lprob_comp_stake by simp 
  also have "... = lprob_comp pr (stake matur w) *
    (det_discount r matur) * (max (K - (lgeom_proc u d init (take matur (stake matur w)))) 0)" 
    using disc_put_option_lgeom[of matur K] by simp
  finally show "prod (prob_component pr w) {0..<matur} * discounted_value r (\<lambda>m. put_option matur K) matur w =
    lprob_comp pr (stake matur w) *
    (det_discount r matur) * (max (K - (lgeom_proc u d init (take matur (stake matur w)))) 0)" .
qed

fun put_price where
"put_price u d init r matur K = (\<Sum> y\<in> (gener_bool_list matur). lprob_comp ((1 + r - d) / (u - d)) y * (det_discount r matur) * 
      (max (K - (lgeom_proc u d init (take matur (take matur y)))) 0))"

text \<open> Evaluating the function above returns the fair price of a put option. \<close>

lemma (in CRR_market_viable) put_price:
  shows "fair_price Mkt 
    (put_price u d init r matur K) 
    (put_option matur K) matur"
proof -
  have "fair_price Mkt 
    (\<Sum> w\<in> range (pseudo_proj_True matur). (prod (prob_component ((1 + r - d) / (u - d)) w) {0..<matur}) * 
      (discounted_value r (\<lambda>m. (put_option matur K)) matur w)) 
    (put_option matur K) matur"
    by (rule CRR_market_fair_price, rule put_borel)
  thus ?thesis using put_effect_compute by simp
qed


subsection \<open> Lookback option \<close>

text \<open> A lookback option is parameterized by a maturity T. If Sn denotes the price of the (unique) risky asset at 
time n, then the option pays max(Sn. 0 <= n <= T) - ST at that time. \<close>

definition (in CRR_market) lbk_option where
"lbk_option (T::nat) = (\<lambda> w. Max ((\<lambda>i. (prices Mkt stk) i w)`{0 .. T}) - (prices Mkt stk T w))"

lemma borel_measurable_Max_finite:
  fixes f::"'a \<Rightarrow> 'b \<Rightarrow> 'c::{second_countable_topology, linorder_topology}"
  assumes "0 < (n::nat)"
shows "\<And>A. card A = n \<Longrightarrow> \<forall>a \<in> A. f a \<in> borel_measurable M \<Longrightarrow> (\<lambda>w. Max ((\<lambda>a. f a w)`A)) \<in> borel_measurable M" using assms
proof (induct n)
  case 0
  show "\<And>A. card A = 0 \<Longrightarrow> \<forall>a\<in>A. f a \<in> borel_measurable M \<Longrightarrow> (0::nat) < 0 \<Longrightarrow> (\<lambda>w. Max ((\<lambda>a. f a w) ` A)) \<in> borel_measurable M" 
  proof -
    fix A::"'a set"
    assume "card A = 0" and  "\<forall>a\<in>A. f a \<in> borel_measurable M" and "(0::nat) < 0" 
    thus "(\<lambda>w. Max ((\<lambda>a. f a w) ` A)) \<in> borel_measurable M" by simp
  qed
next
  case Suc
  show "\<And>n A. (\<And>A. card A = n \<Longrightarrow>
                 \<forall>a\<in>A. f a \<in> borel_measurable M \<Longrightarrow> 0 < n \<Longrightarrow> (\<lambda>w. Max ((\<lambda>a. f a w) ` A)) \<in> borel_measurable M) \<Longrightarrow>
           card A = Suc n \<Longrightarrow>
           \<forall>a\<in>A. f a \<in> borel_measurable M \<Longrightarrow> 0 < Suc n \<Longrightarrow> (\<lambda>w. Max ((\<lambda>a. f a w) ` A)) \<in> borel_measurable M"
  proof -
    fix n
    fix A::"'a set"
    assume ameas: "(\<And>A. card A = n \<Longrightarrow>
                 \<forall>a\<in>A. f a \<in> borel_measurable M \<Longrightarrow> 0 < n \<Longrightarrow> (\<lambda>w. Max ((\<lambda>a. f a w) ` A)) \<in> borel_measurable M)"
    and "card A = Suc n"
    and "\<forall>a\<in>A. f a \<in> borel_measurable M"
    and "0 < Suc n"
    from \<open>card A = Suc n\<close> have aprop: "A\<noteq> {} \<and> finite A" using card_eq_0_iff[of A] by simp
    hence "\<exists>x. x\<in> A" by auto
    from this obtain a where "a\<in> A" by auto
    hence "Suc (card (A - {a})) = Suc n" using aprop card_Suc_Diff1[of A] \<open>card A = Suc n\<close> by auto  
    hence "card (A - {a}) = n" by simp
    show "(\<lambda>w. Max ((\<lambda>a. f a w) ` A)) \<in> borel_measurable M"
    proof (cases "n = 0")
      case False
      hence "0 < n" by simp
      moreover have "\<forall>a\<in>A - {a}. f a \<in> borel_measurable M" using \<open>\<forall>a\<in>A. f a \<in> borel_measurable M\<close> by simp
      ultimately have "(\<lambda>w. Max ((\<lambda>a. f a w) ` (A-{a}))) \<in> borel_measurable M" using \<open>card (A - {a}) = n\<close>
        ameas[of "A - {a}"] by simp
      moreover have "f a \<in> borel_measurable M" using \<open>\<forall>a\<in>A. f a \<in> borel_measurable M\<close> \<open>a\<in>A\<close> by simp
      ultimately have "(\<lambda> w. max (f a w) (Max ((\<lambda>a. f a w) ` (A-{a})))) \<in> borel_measurable M"
        using borel_measurable_max by simp
      moreover have "\<And>w. max (f a w) (Max ((\<lambda>a. f a w) ` (A-{a}))) = Max ((\<lambda>a. f a w) `A)"
      proof -
        fix w
        define FA where "FA = ((\<lambda>a. f a w) ` (A-{a}))"
        have "finite FA" unfolding FA_def using aprop by simp 
        have "A - {a} \<noteq> {}" using aprop False \<open>card (A - {a}) = n\<close> card_eq_0_iff[of "A - {a}"] by simp 
        hence "FA \<noteq> {}" unfolding FA_def by simp
        have "max (f a w) (Max FA) = Max (insert (f a w) FA)" using \<open>finite FA\<close> \<open>FA \<noteq> {}\<close> by simp
        hence  "max (f a w) (Max ((\<lambda>a. f a w) ` (A-{a}))) = Max (insert (f a w) ((\<lambda>a. f a w) `(A-{a})))"
          unfolding FA_def by simp
        also have "... = Max ((\<lambda>a. f a w) `A)"
        proof -
          have "insert (f a w) ((\<lambda>a. f a w) `(A-{a})) = (\<lambda>a. f a w) `(insert a (A - {a}))"
            by auto
          also have "... = ((\<lambda>a. f a w) `A)" using \<open>a \<in> A\<close> by blast
          finally have "insert (f a w) ((\<lambda>a. f a w) `(A-{a})) = ((\<lambda>a. f a w) `A)" .
          thus ?thesis by simp 
        qed
        finally show "max (f a w) (Max ((\<lambda>a. f a w) ` (A-{a}))) = Max ((\<lambda>a. f a w) `A)" .
      qed
      ultimately show "(\<lambda>w. Max ((\<lambda>a. f a w) `A)) \<in> borel_measurable M" by simp
    next
      case True
      hence "A - {a} = {}" using aprop card_eq_0_iff[of "A - {a}"] \<open>card (A - {a}) = n\<close> by simp
      hence "{a} = insert a (A - {a})" by simp
      also have "... = A" using \<open>a\<in> A\<close> by blast
      finally have "{a} = A" .
      hence "\<And>w. (\<lambda>a. f a w) `A = {f a w}" by auto
      hence "\<And>w. Max ((\<lambda>a. f a w) `A) = Max {f a w}" by simp
      hence "\<And>w. Max ((\<lambda>a. f a w) `A) = f a w" by simp
      hence "(\<lambda>w. Max ((\<lambda>a. f a w) `A)) = f a" by simp
      thus "(\<lambda>w. Max ((\<lambda>a. f a w) `A)) \<in> borel_measurable M" using \<open>\<forall>a\<in>A. f a \<in> borel_measurable M\<close> 
        \<open>a\<in> A\<close> by simp
    qed
  qed
qed


lemma (in CRR_market) lbk_borel:
  shows "lbk_option T \<in> borel_measurable (G T)" unfolding lbk_option_def
proof (rule borel_measurable_diff)
  show "(\<lambda>x. Max ((\<lambda>i. prices Mkt stk i x) ` {0..T})) \<in> borel_measurable (G T)"
  proof (rule borel_measurable_Max_finite)
    show "card {0..T} = Suc T" by simp
    show "0 < Suc T" by simp
    show "\<forall>i\<in>{0..T}. prices Mkt stk i \<in> borel_measurable (G T)"
    proof
      fix i
      assume "i\<in> {0..T}"
      show "prices Mkt stk i \<in> borel_measurable (G T)"
        by (metis \<open>i \<in> {0..T}\<close> adapt_stoch_proc_def atLeastAtMost_iff increasing_measurable_info 
            stock_price_borel_measurable)
    qed
  qed
  show "prices Mkt stk T \<in> borel_measurable (G T)" by (metis  adapt_stoch_proc_def stock_price_borel_measurable)
qed

lemma (in CRR_market_viable) lbk_option_lgeom:
  shows "lbk_option T w = Max ((\<lambda>i. (lgeom_proc u d init (stake i w)))`{0 .. T}) - (lgeom_proc u d init (stake T w))"
  using geom_lgeom stk_price geometric_process unfolding lbk_option_def by simp


lemma (in CRR_market_viable) disc_lbk_option_lgeom:
  shows "(discounted_value r (\<lambda>m. (lbk_option T)) T w) = 
    (det_discount r T) * (Max ((\<lambda>i. (lgeom_proc u d init (take i (stake T w))))`{0 .. T}) - (lgeom_proc u d init (stake T w)))"
    using det_discounted[of r "\<lambda>m. lbk_option T" T w] lbk_option_lgeom[of T w] lgeom_proc_take
    by (metis (no_types, lifting) atLeastAtMost_iff image_cong) 

lemma (in CRR_market_viable) lbk_effect_compute:
shows "(\<Sum> w\<in> range (pseudo_proj_True matur). (prod (prob_component pr w) {0..<matur}) * 
      (discounted_value r (\<lambda>m. (lbk_option matur)) matur w)) =
      (\<Sum> y\<in> (gener_bool_list matur). lprob_comp pr y * (det_discount r matur) * 
      (Max ((\<lambda>i. (lgeom_proc u d init (take i y)))`{0 .. matur}) - (lgeom_proc u d init y)))" 
proof (rule pseudo_range_stake)
  fix w
  have "prod (prob_component pr w) {0..<matur} * discounted_value r (\<lambda>m. lbk_option matur) matur w =
    lprob_comp pr (stake matur w) * discounted_value r (\<lambda>m. lbk_option matur) matur w"
    using lprob_comp_stake by simp 
  also have "... = lprob_comp pr (stake matur w) *
    (det_discount r matur) * (Max ((\<lambda>i. (lgeom_proc u d init (take i (stake matur w))))`{0 .. matur}) - 
      (lgeom_proc u d init (stake matur w)))" using disc_lbk_option_lgeom by simp
  finally show "prod (prob_component pr w) {0..<matur} * discounted_value r (\<lambda>m. lbk_option matur) matur w =
    lprob_comp pr (stake matur w) *
    (det_discount r matur) * (Max ((\<lambda>i. (lgeom_proc u d init (take i (stake matur w))))`{0 .. matur}) - 
      (lgeom_proc u d init (stake matur w)))" .
qed

fun lbk_price where
"lbk_price u d init r matur = (\<Sum> y\<in> (gener_bool_list matur). lprob_comp ((1 + r - d) / (u - d)) y * (det_discount r matur) * 
      (Max ((\<lambda>i. (lgeom_proc u d init (take i y)))`{0 .. matur}) - (lgeom_proc u d init y)))"


text \<open> Evaluating the function above returns the fair price of a lookback option. \<close>

lemma (in CRR_market_viable) lbk_price:
  shows "fair_price Mkt 
    (lbk_price u d init r matur) 
    (lbk_option matur) matur"
proof -
  have "fair_price Mkt 
    (\<Sum> w\<in> range (pseudo_proj_True matur). (prod (prob_component ((1 + r - d) / (u - d)) w) {0..<matur}) * 
      (discounted_value r (\<lambda>m. (lbk_option matur)) matur w)) 
    (lbk_option matur) matur"
    by (rule CRR_market_fair_price, rule lbk_borel)
  thus ?thesis using lbk_effect_compute by simp
qed

value "lbk_price 1.2 0.8 10 0.03 2"

subsection \<open> Asian option \<close>

text \<open> An asian option is parameterized by a maturity T. This option pays the average price of the 
risky asset at time T. \<close>

definition (in CRR_market) asian_option where
"asian_option (T::nat) = (\<lambda> w. (\<Sum> i\<in> {1.. T}. prices Mkt stk i w)/T)"

lemma (in CRR_market) asian_borel:
  shows "asian_option T \<in> borel_measurable (G T)" unfolding asian_option_def
proof -
  have "(\<lambda> w. (\<Sum> i\<in> {1.. T}. prices Mkt stk i w)) \<in> borel_measurable (G T)"
  proof (rule borel_measurable_sum)
    fix i
    assume "i\<in> {1..T}"
    show "prices Mkt stk i \<in> borel_measurable (G T)" 
      by (metis \<open>i \<in> {1..T}\<close> adapt_stoch_proc_def atLeastAtMost_iff increasing_measurable_info 
            stock_price_borel_measurable)
  qed
  from this show "(\<lambda>w. (\<Sum>i = 1..T. prices Mkt stk i w) / real T) \<in> borel_measurable (G T)" by simp
qed


lemma (in CRR_market_viable) asian_option_lgeom:
  shows "asian_option T w = (\<Sum> i\<in> {1.. T}. lgeom_proc u d init (stake i w))/ T"
  using geom_lgeom stk_price geometric_process unfolding asian_option_def by simp

lemma (in CRR_market_viable) disc_asian_option_lgeom:
  shows "(discounted_value r (\<lambda>m. (asian_option T)) T w) = 
    (det_discount r T) * (\<Sum> i\<in> {1.. T}. lgeom_proc u d init (take i (stake T w)))/ T"
proof -
  have "\<forall> i\<in> {1..T}. lgeom_proc u d init (stake i w) = lgeom_proc u d init (take i (stake T w))"
    using lgeom_proc_take by auto
  hence "(\<Sum> i\<in> {1.. T}. lgeom_proc u d init (stake i w)) = 
    (\<Sum> i\<in> {1.. T}. lgeom_proc u d init (take i (stake T w)))" by auto
  thus ?thesis
    using det_discounted[of r "\<lambda>m. asian_option T" T w] asian_option_lgeom[of T w] by auto
qed

lemma (in CRR_market_viable) asian_effect_compute:
shows "(\<Sum> w\<in> range (pseudo_proj_True matur). (prod (prob_component pr w) {0..<matur}) * 
      (discounted_value r (\<lambda>m. (asian_option matur)) matur w)) =
      (\<Sum> y\<in> (gener_bool_list matur). lprob_comp pr y * (det_discount r matur) * 
      (\<Sum> i\<in> {1.. matur}. lgeom_proc u d init (take i y))/ matur)" 
proof (rule pseudo_range_stake)
  fix w
  have "prod (prob_component pr w) {0..<matur} * discounted_value r (\<lambda>m. asian_option matur) matur w =
    lprob_comp pr (stake matur w) * discounted_value r (\<lambda>m. asian_option matur) matur w"
    using lprob_comp_stake by simp 
  also have "... = lprob_comp pr (stake matur w) *
    (det_discount r matur) * (\<Sum> i\<in> {1.. matur}. lgeom_proc u d init (take i (stake matur w)))/ matur" 
    using disc_asian_option_lgeom[of matur w] by simp
  finally show "prod (prob_component pr w) {0..<matur} * discounted_value r (\<lambda>m. asian_option matur) matur w =
    lprob_comp pr (stake matur w) *
    (det_discount r matur) * (\<Sum> i\<in> {1.. matur}. lgeom_proc u d init (take i (stake matur w)))/ matur" .
qed

fun asian_price where
"asian_price u d init r matur = (\<Sum> y\<in> (gener_bool_list matur). lprob_comp ((1 + r - d) / (u - d)) y * (det_discount r matur) * 
      (\<Sum> i\<in> {1.. matur}. lgeom_proc u d init (take i y))/ matur)"

text \<open> Evaluating the function above returns the fair price of an asian option. \<close>

lemma (in CRR_market_viable) asian_price:
  shows "fair_price Mkt 
    (asian_price u d init r matur) 
    (asian_option matur) matur"
proof -
  have "fair_price Mkt 
    (\<Sum> w\<in> range (pseudo_proj_True matur). (prod (prob_component ((1 + r - d) / (u - d)) w) {0..<matur}) * 
      (discounted_value r (\<lambda>m. (asian_option matur)) matur w)) 
    (asian_option matur) matur"
    by (rule CRR_market_fair_price, rule asian_borel)
  thus ?thesis using asian_effect_compute by simp
qed

end