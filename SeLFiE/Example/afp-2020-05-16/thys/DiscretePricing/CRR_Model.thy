(*  Title:      CRR_Model.thy
    Author:     Mnacho Echenim, Univ. Grenoble Alpes
*)

section \<open>The Cox Ross Rubinstein model\<close>

text \<open>This section defines the Cox-Ross-Rubinstein model of a financial market, and charcterizes a risk-neutral
probability space for this market. This, together with the proof that every derivative is attainable, permits to
obtain a formula to explicitely compute the fair price of any derivative.\<close>

theory CRR_Model imports Fair_Price

begin

locale CRR_hyps = prob_grw + rsk_free_asset +
  fixes stk
assumes stocks: "stocks Mkt = {stk, risk_free_asset}"
  and stk_price: "prices Mkt stk = geom_proc"
  and S0_positive: "0 < init"
  and down_positive: "0 < d" and down_lt_up: "d < u"
  and psgt: "0 < p"
  and pslt: "p < 1"


locale CRR_market = CRR_hyps +
  fixes G
assumes stock_filtration:"G = stoch_proc_filt M geom_proc borel"

subsection \<open>Preliminary results on the market\<close>

lemma (in CRR_market) case_asset:
  assumes "asset \<in> stocks Mkt"
  shows "asset = stk \<or> asset = risk_free_asset"
proof (rule ccontr)
  assume "\<not> (asset = stk \<or> asset = risk_free_asset)"
  hence "asset \<noteq> stk \<and> asset \<noteq> risk_free_asset" by simp
  moreover have "asset \<in> {stk, risk_free_asset}" using assms stocks by simp
  ultimately show False by auto
qed

lemma (in CRR_market)
  assumes "N = bernoulli_stream q"
and "0 < q"
and "q < 1"
shows bernoulli_gen_filtration: "filtration N G"
and bernoulli_sigma_finite: "\<forall>n. sigma_finite_subalgebra N (G n)"
proof -
  show "filtration N G"
  proof -
    have "disc_filtr M (stoch_proc_filt M geom_proc borel)"
    proof (rule stoch_proc_filt_disc_filtr)
      fix i
      show "random_variable borel (geom_proc i)"
        by (simp add: geom_rand_walk_borel_measurable)
    qed
    hence "filtration M G" using stock_filtration  by (simp add: filtration_def disc_filtr_def)
    have "filt_equiv nat_filtration M N" using pslt psgt by (simp add: assms bernoulli_stream_equiv)
    hence "sets N = sets M" unfolding filt_equiv_def by simp
    thus ?thesis unfolding filtration_def
      by (metis filtration_def \<open>Filtration.filtration M G\<close> sets_eq_imp_space_eq subalgebra_def)
  qed
  show "\<forall>n. sigma_finite_subalgebra N (G n)" using assms unfolding subalgebra_def
    using  filtration_def  subalgebra_sigma_finite
    by (metis \<open>Filtration.filtration N G\<close> bernoulli_stream_def prob_space.prob_space_stream_space
        prob_space.subalgebra_sigma_finite prob_space_measure_pmf)
qed


sublocale CRR_market \<subseteq> rfr_disc_equity_market  _ G
proof (unfold_locales)
  show  "disc_filtr M G \<and> sets (G \<bottom>) = {{}, space M}"
  proof
    show "sets (G \<bottom>) = {{}, space M}" using infinite_cts_filtration.stoch_proc_filt_triv_init stock_filtration geometric_process
        geom_rand_walk_borel_adapted
      by (meson infinite_coin_toss_space_axioms infinite_cts_filtration_axioms.intro infinite_cts_filtration_def
          init_triv_filt_def)
    show "disc_filtr M G"
      by (metis Filtration.filtration_def bernoulli bernoulli_gen_filtration disc_filtr_def psgt pslt)
  qed
  show "\<forall>asset\<in>stocks Mkt. borel_adapt_stoch_proc G (prices Mkt asset)"
  proof -
    have "borel_adapt_stoch_proc G (prices Mkt stk)" using stk_price stock_filtration stoch_proc_filt_adapt
      by (simp add: stoch_proc_filt_adapt geom_rand_walk_borel_measurable)
    moreover have "borel_adapt_stoch_proc G (prices Mkt risk_free_asset)"
      using \<open>disc_filtr M G \<and> sets (G \<bottom>) = {{}, space M}\<close> disc_filtr_prob_space.disc_rfr_proc_borel_adapted
        disc_filtr_prob_space.intro disc_filtr_prob_space_axioms.intro prob_space_axioms rf_price by fastforce
    moreover have "disc_filtr_prob_space M G" proof (unfold_locales)
      show "disc_filtr M G" by (simp add: \<open>disc_filtr M G \<and> sets (G \<bottom>) = {{}, space M}\<close>)
    qed
    ultimately show ?thesis using stocks by force
  qed
qed




lemma (in CRR_market) two_stocks:
shows "stk \<noteq> risk_free_asset"
proof (rule ccontr)
  assume "\<not>stk \<noteq> risk_free_asset"
  hence "disc_rfr_proc r = prices Mkt stk" using rf_price by simp
  also have "... = geom_proc" using stk_price by simp
  finally have eqf: "disc_rfr_proc r = geom_proc" .
  hence "\<forall>w. disc_rfr_proc r 0 w = geom_proc 0 w" by simp
  hence "1 = init" using geometric_process by simp
  have eqfs: "\<forall>w. disc_rfr_proc r (Suc 0) w = geom_proc (Suc 0) w" using eqf by simp
  hence "disc_rfr_proc r (Suc 0) (sconst True) = geom_proc (Suc 0) (sconst True)" by simp
  hence "1+r = u" using geometric_process \<open>1 = init\<close> by simp
  have "disc_rfr_proc r (Suc 0) (sconst False) = geom_proc (Suc 0) (sconst False)" using eqfs by simp
  hence "1+r = d" using geometric_process \<open>1 = init\<close> by simp
  show False using \<open>1+r = u\<close> \<open>1+r = d\<close> down_lt_up by simp
qed


lemma (in CRR_market) stock_pf_vp_expand:
  assumes "stock_portfolio Mkt pf"
  shows "val_process Mkt pf n w = geom_proc n w * pf stk (Suc n) w +
    disc_rfr_proc r n w * pf risk_free_asset (Suc n) w"
proof -
  have "val_process Mkt pf n w =(sum (\<lambda>x. ((prices Mkt) x n w) * (pf x (Suc n) w)) (stocks Mkt))"
  proof (rule subset_val_process')
    show "finite (stocks Mkt)" using stocks by auto
    show "support_set pf \<subseteq> stocks Mkt" using assms unfolding stock_portfolio_def by simp
  qed
  also have "... = (\<Sum>x\<in> {stk, risk_free_asset}. ((prices Mkt) x n w) * (pf x (Suc n) w))" using stocks  by simp
  also have "... =  prices Mkt stk n w * pf stk (Suc n) w +
    (\<Sum> x\<in> {risk_free_asset}. ((prices Mkt) x n w) * (pf x (Suc n) w))" by (simp add:two_stocks)
  also have "... = prices Mkt stk n w * pf stk (Suc n) w +
    prices Mkt risk_free_asset n w * pf risk_free_asset (Suc n) w" by simp
  also have "... = geom_proc n w * pf stk (Suc n) w + disc_rfr_proc r n w * pf risk_free_asset (Suc n) w"
    using rf_price stk_price by simp
  finally show ?thesis .
qed

lemma (in CRR_market) stock_pf_uvp_expand:
  assumes "stock_portfolio Mkt pf"
  shows "cls_val_process Mkt pf (Suc n) w = geom_proc (Suc n) w * pf stk (Suc n) w +
    disc_rfr_proc r (Suc n) w * pf risk_free_asset (Suc n) w"
proof -
  have "cls_val_process Mkt pf (Suc n) w =(sum (\<lambda>x. ((prices Mkt) x (Suc n) w) * (pf x (Suc n) w)) (stocks Mkt))"
  proof (rule subset_cls_val_process')
    show "finite (stocks Mkt)" using stocks by auto
    show "support_set pf \<subseteq> stocks Mkt" using assms unfolding stock_portfolio_def by simp
  qed
  also have "... = (\<Sum>x\<in> {stk, risk_free_asset}. ((prices Mkt) x (Suc n) w) * (pf x (Suc n) w))" using  stocks by simp
  also have "... =  prices Mkt stk (Suc n) w * pf stk (Suc n) w +
    (\<Sum> x\<in> {risk_free_asset}. ((prices Mkt) x (Suc n) w) * (pf x (Suc n) w))" by (simp add:two_stocks)
  also have "... = prices Mkt stk (Suc n) w * pf stk (Suc n) w +
    prices Mkt risk_free_asset (Suc n) w * pf risk_free_asset (Suc n) w" by simp
  also have "... = geom_proc (Suc n) w * pf stk (Suc n) w + disc_rfr_proc r (Suc n) w * pf risk_free_asset (Suc n) w"
    using rf_price stk_price by simp
  finally show ?thesis .
qed



lemma (in CRR_market) pos_pf_neg_uvp:
  assumes "stock_portfolio Mkt pf"
  and "d < 1+r"
  and "0 < pf stk (Suc n) (spick w n False)"
  and "val_process Mkt pf n (spick w n False) \<le> 0"
shows "cls_val_process Mkt pf (Suc n) (spick w n False) < 0"
proof -
  define wnf where "wnf = spick w n False"
  have "cls_val_process Mkt pf (Suc n) (spick w n False) =
    geom_proc (Suc n) wnf * pf stk (Suc n) wnf +
    disc_rfr_proc r (Suc n) wnf * pf risk_free_asset (Suc n) wnf" unfolding wnf_def
    using assms by (simp add:stock_pf_uvp_expand)
  also have "... = d * geom_proc n wnf * pf stk (Suc n) wnf + disc_rfr_proc r (Suc n) wnf * pf risk_free_asset (Suc n) wnf"
    unfolding wnf_def using geometric_process spickI[of n w False] by simp
  also have "... = d * geom_proc n wnf * pf stk (Suc n) wnf + (1+r) * disc_rfr_proc r n wnf * pf risk_free_asset (Suc n) wnf"
    by simp
  also have "... < (1+r) * geom_proc n wnf * pf stk (Suc n) wnf + (1+r) * disc_rfr_proc r n wnf * pf risk_free_asset (Suc n) wnf"
    unfolding wnf_def using assms geom_rand_walk_strictly_positive S0_positive
      down_positive down_lt_up by simp
  also have "... = (1+r) * (geom_proc n wnf * pf stk (Suc n) wnf + disc_rfr_proc r n wnf * pf risk_free_asset (Suc n) wnf)"
    by (simp add: distrib_left)
  also have "... = (1+r) * val_process Mkt pf n wnf" using stock_pf_vp_expand assms by simp
  also have "... \<le> 0"
  proof -
    have "0 < 1+r" using assms down_positive by simp
    moreover have "val_process Mkt pf n wnf \<le> 0" using assms unfolding wnf_def by simp
    ultimately show "(1+r) * (val_process Mkt pf n wnf) \<le>  0" unfolding wnf_def
      using less_eq_real_def[of 0 "1+r"] mult_nonneg_nonpos[of "1+r" "val_process Mkt pf n (spick w n False)"] by simp
  qed
  finally show ?thesis .
qed


lemma (in CRR_market) neg_pf_neg_uvp:
  assumes "stock_portfolio Mkt pf"
  and "1+r < u"
  and "pf stk (Suc n) (spick w n True) < 0"
  and "val_process Mkt pf n (spick w n True) \<le> 0"
shows "cls_val_process Mkt pf (Suc n) (spick w n True) < 0"
proof -
  define wnf where "wnf = spick w n True"
  have "cls_val_process Mkt pf (Suc n) (spick w n True) =
    geom_proc (Suc n) wnf * pf stk (Suc n) wnf +
    disc_rfr_proc r (Suc n) wnf * pf risk_free_asset (Suc n) wnf" unfolding wnf_def
    using assms by (simp add:stock_pf_uvp_expand)
  also have "... = u * geom_proc n wnf * pf stk (Suc n) wnf + disc_rfr_proc r (Suc n) wnf * pf risk_free_asset (Suc n) wnf"
    unfolding wnf_def using geometric_process spickI[of n w True] by simp
  also have "... = u * geom_proc n wnf * pf stk (Suc n) wnf + (1+r) * disc_rfr_proc r n wnf * pf risk_free_asset (Suc n) wnf"
    by simp
  also have "... < (1+r) * geom_proc n wnf * pf stk (Suc n) wnf + (1+r) * disc_rfr_proc r n wnf * pf risk_free_asset (Suc n) wnf"
    unfolding wnf_def using assms geom_rand_walk_strictly_positive S0_positive
      down_positive down_lt_up by simp
  also have "... = (1+r) * (geom_proc n wnf * pf stk (Suc n) wnf + disc_rfr_proc r n wnf * pf risk_free_asset (Suc n) wnf)"
    by (simp add: distrib_left)
  also have "... = (1+r) * val_process Mkt pf n wnf" using stock_pf_vp_expand assms by simp
  also have "... \<le> 0"
  proof -
    have "0 < 1+r" using acceptable_rate by simp
    moreover have "val_process Mkt pf n wnf \<le> 0" using assms unfolding wnf_def by simp
    ultimately show "(1+r) * (val_process Mkt pf n wnf) \<le>  0" unfolding wnf_def
      using less_eq_real_def[of 0 "1+r"] mult_nonneg_nonpos[of "1+r" "val_process Mkt pf n (spick w n True)"] by simp
  qed
  finally show ?thesis .
qed




lemma (in CRR_market) zero_pf_neg_uvp:
  assumes "stock_portfolio Mkt pf"
  and "pf stk (Suc n) w = 0"
  and "pf risk_free_asset (Suc n) w \<noteq> 0"
  and "val_process Mkt pf n w \<le> 0"
shows "cls_val_process Mkt pf (Suc n) w < 0"
proof -
  have "cls_val_process Mkt pf (Suc n) w =
    S (Suc n) w * pf stk (Suc n) w +
    disc_rfr_proc r (Suc n) w * pf risk_free_asset (Suc n) w"
    using assms by (simp add:stock_pf_uvp_expand)
  also have "... = disc_rfr_proc r (Suc n) w * pf risk_free_asset (Suc n) w" using assms by simp
  also have "... = (1+r) * disc_rfr_proc r n w * pf risk_free_asset (Suc n) w" by simp
  also have "... < 0"
  proof -
    have "0 < 1+r" using acceptable_rate by simp
    moreover have "0 < disc_rfr_proc r n w" using acceptable_rate by (simp add: disc_rfr_proc_positive)
    ultimately have "0 < (1+r) * disc_rfr_proc r n w" by simp
    have 1: "0< pf risk_free_asset (Suc n) w \<longrightarrow> 0 <(1+r) * disc_rfr_proc r n w * pf risk_free_asset (Suc n) w"
    proof (intro impI)
      assume "0 < pf risk_free_asset (Suc n) w"
      thus "0 < (1 + r) * disc_rfr_proc r n w * pf risk_free_asset (Suc n) w" using \<open>0 < (1+r) * disc_rfr_proc r n w\<close>
        by simp
    qed
    have 2: "pf risk_free_asset (Suc n) w < 0 \<longrightarrow> (1+r) * disc_rfr_proc r n w * pf risk_free_asset (Suc n) w < 0"
    proof (intro impI)
      assume "pf risk_free_asset (Suc n) w < 0"
      thus "(1 + r) * disc_rfr_proc r n w * pf risk_free_asset (Suc n) w < 0" using \<open>0 < (1+r) * disc_rfr_proc r n w\<close>
        by (simp add:mult_pos_neg)
    qed
    have "0 \<ge> val_process Mkt pf n w" using assms by simp
    also have "val_process Mkt pf n w = geom_proc n w * pf stk (Suc n) w +
      disc_rfr_proc r n w * pf risk_free_asset (Suc n) w" using assms by (simp add:stock_pf_vp_expand)
    also have "... = disc_rfr_proc r n w * pf risk_free_asset (Suc n) w" using assms by simp
    finally have "0\<ge> disc_rfr_proc r n w * pf risk_free_asset (Suc n) w" .
    have "0< pf risk_free_asset (Suc n) w \<or> pf risk_free_asset (Suc n) w < 0"  using assms
       by linarith
    thus ?thesis
      using "2" \<open>0 < disc_rfr_proc r n w\<close> \<open>disc_rfr_proc r n w * pf risk_free_asset (Suc n) w \<le> 0\<close>
        mult_pos_pos by fastforce
  qed
  finally show ?thesis .
qed



lemma (in CRR_market) neg_pf_exists:
  assumes "stock_portfolio Mkt pf"
  and "trading_strategy pf"
  and "1+r < u"
  and "d < 1+r"
  and "val_process Mkt pf n w \<le> 0"
  and "pf stk (Suc n) w \<noteq> 0 \<or> pf risk_free_asset (Suc n) w \<noteq> 0"
shows "\<exists>y. cls_val_process Mkt pf (Suc n) y < 0"
proof -
  have "borel_predict_stoch_proc G (pf stk)"
  proof (rule inc_predict_support_trading_strat')
    show "trading_strategy pf" using assms by simp
    show "stk \<in> support_set pf \<union> {stk}" by simp
  qed
  hence "pf stk (Suc n) \<in> borel_measurable (G n)" unfolding predict_stoch_proc_def by simp
  have "val_process Mkt pf n \<in> borel_measurable (G n)"
  proof -
    have "borel_adapt_stoch_proc G (val_process Mkt pf)" using assms
      using support_adapt_def ats_val_process_adapted readable unfolding  stock_portfolio_def by blast
    thus ?thesis unfolding adapt_stoch_proc_def by simp
  qed
  define wn where "wn = pseudo_proj_True n w"
  show ?thesis
  proof (cases "pf stk (Suc n) w \<noteq> 0")
    case True
    show ?thesis
    proof (cases "pf stk (Suc n) w > 0")
      case True
      have "0 <pf stk (Suc n) (spick wn n False)"
      proof -
        have "0 < pf stk (Suc n) w" using \<open>0 < pf stk (Suc n) w\<close> by simp
        also have "... = pf stk (Suc n) wn" unfolding wn_def
          using \<open>pf stk (Suc n) \<in> borel_measurable (G n)\<close> stoch_proc_subalg_nat_filt[of geom_proc] geometric_process
          nat_filtration_info stock_filtration
          by (metis comp_apply geom_rand_walk_borel_adapted measurable_from_subalg)
        also have "... = pf stk (Suc n) (spick wn n False)" using \<open>pf stk (Suc n) \<in> borel_measurable (G n)\<close> comp_def nat_filtration_info
              pseudo_proj_True_stake_image spickI stoch_proc_subalg_nat_filt[of geom_proc] geometric_process stock_filtration
          by (metis geom_rand_walk_borel_adapted measurable_from_subalg)
        finally show ?thesis .
      qed
      moreover have "0 \<ge> val_process Mkt pf n (spick wn n False)"
      proof -
        have "0 \<ge> val_process Mkt pf n w" using assms by simp
        also have "val_process Mkt pf n w = val_process Mkt pf n wn" unfolding wn_def using \<open>val_process Mkt pf n \<in> borel_measurable (G n)\<close>
          nat_filtration_info stoch_proc_subalg_nat_filt[of geom_proc] geometric_process
          stock_filtration by (metis comp_apply geom_rand_walk_borel_adapted measurable_from_subalg)
        also have "... = val_process Mkt pf n (spick wn n False)" using \<open>val_process Mkt pf n \<in> borel_measurable (G n)\<close>
          comp_def nat_filtration_info
              pseudo_proj_True_stake_image spickI stoch_proc_subalg_nat_filt[of geom_proc] geometric_process stock_filtration
          by (metis geom_rand_walk_borel_adapted measurable_from_subalg)
        finally show ?thesis .
      qed
      ultimately have "cls_val_process Mkt pf (Suc n) (spick wn n False) < 0" using assms
        by (simp add:pos_pf_neg_uvp)
      thus "\<exists>y. cls_val_process Mkt pf (Suc n) y < 0" by auto
    next
      case False
      have "0 >pf stk (Suc n) (spick wn n True)"
      proof -
        have "0 > pf stk (Suc n) w" using \<open>\<not> 0 < pf stk (Suc n) w\<close> \<open>pf stk (Suc n) w \<noteq> 0\<close> by simp
        also have "pf stk (Suc n) w = pf stk (Suc n) wn" unfolding wn_def using \<open>pf stk (Suc n) \<in> borel_measurable (G n)\<close>
          nat_filtration_info stoch_proc_subalg_nat_filt[of geom_proc] geometric_process
          stock_filtration by (metis comp_apply geom_rand_walk_borel_adapted measurable_from_subalg)
        also have "... = pf stk (Suc n) (spick wn n True)" using \<open>pf stk (Suc n) \<in> borel_measurable (G n)\<close>
          comp_def nat_filtration_info
              pseudo_proj_True_stake_image spickI stoch_proc_subalg_nat_filt[of geom_proc] geometric_process stock_filtration
          by (metis geom_rand_walk_borel_adapted measurable_from_subalg)
        finally show ?thesis .
      qed
      moreover have "0 \<ge> val_process Mkt pf n (spick wn n True)"
      proof -
        have "0 \<ge> val_process Mkt pf n w" using assms by simp
        also have "val_process Mkt pf n w = val_process Mkt pf n wn" unfolding wn_def using \<open>val_process Mkt pf n \<in> borel_measurable (G n)\<close>
          comp_def nat_filtration_info
              pseudo_proj_True_stake_image spickI stoch_proc_subalg_nat_filt[of geom_proc] geometric_process stock_filtration
          by (metis geom_rand_walk_borel_adapted measurable_from_subalg)
        also have "... = val_process Mkt pf n (spick wn n True)" using \<open>val_process Mkt pf n \<in> borel_measurable (G n)\<close>
          comp_def nat_filtration_info
              pseudo_proj_True_stake_image spickI stoch_proc_subalg_nat_filt[of geom_proc] geometric_process stock_filtration
          by (metis geom_rand_walk_borel_adapted measurable_from_subalg)
        finally show ?thesis .
      qed
      ultimately have "cls_val_process Mkt pf (Suc n) (spick wn n True) < 0" using assms
        by (simp add:neg_pf_neg_uvp)
      thus "\<exists>y. cls_val_process Mkt pf (Suc n) y < 0" by auto
    qed
  next
    case False
    hence "pf risk_free_asset (Suc n) w \<noteq> 0" using assms by simp
    hence "cls_val_process Mkt pf (Suc n) w < 0" using False assms by (auto simp add:zero_pf_neg_uvp)
    thus "\<exists>y. cls_val_process Mkt pf (Suc n) y < 0" by auto
  qed
qed


lemma (in CRR_market) non_zero_components:
assumes "val_process Mkt pf n y \<noteq> 0"
and "stock_portfolio Mkt pf"
shows  "pf stk (Suc n) y \<noteq> 0 \<or> pf risk_free_asset (Suc n) y \<noteq> 0"
proof (rule ccontr)
  assume "\<not>(pf stk (Suc n) y \<noteq> 0 \<or> pf risk_free_asset (Suc n) y \<noteq> 0)"
  hence "pf stk (Suc n) y = 0" "pf risk_free_asset (Suc n) y = 0" by auto
  have "val_process Mkt pf n y = geom_proc n y * pf stk (Suc n) y +
    disc_rfr_proc r n y * pf risk_free_asset (Suc n) y" using \<open>stock_portfolio Mkt pf\<close>
    stock_pf_vp_expand[of pf n]  by simp
  also have "... = 0" using \<open>pf stk (Suc n) y = 0\<close> \<open>pf risk_free_asset (Suc n) y = 0\<close> by simp
  finally have "val_process Mkt pf n y = 0" .
  moreover have "val_process Mkt pf n y \<noteq> 0" using assms by simp
  ultimately show False by simp
qed

lemma (in CRR_market) neg_pf_Suc:
  assumes "stock_portfolio Mkt pf"
  and "trading_strategy pf"
  and "self_financing Mkt pf"
  and "1+r < u"
  and "d < 1+r"
  and "cls_val_process Mkt pf n w < 0"
shows "n \<le> m \<Longrightarrow> \<exists>y. cls_val_process Mkt pf m y < 0"
proof (induct m)
  case 0
  assume "n \<le> 0"
  hence "n=0" by simp
  thus "\<exists>y. cls_val_process Mkt pf 0 y < 0" using assms by auto
next
  case (Suc m)
  assume "n \<le> Suc m"
  thus "\<exists>y. cls_val_process Mkt pf (Suc m) y < 0"
  proof (cases "n < Suc m")
    case False
    hence "n = Suc m" using \<open>n \<le> Suc m\<close> by simp
    thus "\<exists>y. cls_val_process Mkt pf (Suc m) y < 0" using assms by auto
  next
    case True
    hence "n \<le> m" by simp
    hence "\<exists>y. cls_val_process Mkt pf m y < 0" using Suc by simp
    from this obtain y where "cls_val_process Mkt pf m y < 0" by auto
    hence "val_process Mkt pf m y < 0" using assms by (simp add:self_financingE)
    hence "val_process Mkt pf m y \<le> 0" by simp
    have "val_process Mkt pf m y \<noteq> 0" using \<open>val_process Mkt pf m y < 0\<close> by simp
    hence "pf stk (Suc m) y \<noteq> 0 \<or> pf risk_free_asset (Suc m) y \<noteq> 0" using assms non_zero_components by simp
    thus "\<exists>y. cls_val_process Mkt pf (Suc m) y < 0" using neg_pf_exists[of pf m y] assms
      \<open>val_process Mkt pf m y \<le> 0\<close> by simp
  qed
qed




lemma (in CRR_market) viable_if:
  assumes "1+r < u"
  and "d < 1+r"
shows "viable_market Mkt" unfolding viable_market_def
proof (rule ccontr)
  assume "\<not>(\<forall>p. stock_portfolio Mkt p \<longrightarrow> \<not> arbitrage_process Mkt p)"
  hence "\<exists>p. stock_portfolio Mkt p \<and> arbitrage_process Mkt p" by simp
  from this obtain pf where "stock_portfolio Mkt pf" and "arbitrage_process Mkt pf" by auto
  have "(\<exists> m. (self_financing Mkt pf) \<and> (trading_strategy pf) \<and>
    (\<forall>w \<in> space M. cls_val_process Mkt pf 0 w = 0) \<and>
    (AE w in M. 0 \<le> cls_val_process Mkt pf m w) \<and>
    0 < \<P>(w in M. cls_val_process Mkt pf m w > 0))" using \<open>arbitrage_process Mkt pf\<close>
    using arbitrage_processE by simp
  from this obtain m where "self_financing Mkt pf" and "(trading_strategy pf)"
    and "(\<forall>w \<in> space M. cls_val_process Mkt pf 0 w = 0)"
    and "(AE w in M. 0 \<le> cls_val_process Mkt pf m w)"
    and "0 < \<P>(w in M. cls_val_process Mkt pf m w > 0)" by auto
  have "{w\<in> space M. cls_val_process Mkt pf m w > 0} \<noteq> {}" using
    \<open>0 < \<P>(w in M. cls_val_process Mkt pf m w > 0)\<close> by force
  hence "\<exists>w\<in> space M. cls_val_process Mkt pf m w > 0" by auto
  from this obtain y where "y\<in> space M" and "cls_val_process Mkt pf m y > 0" by auto
  define A where "A = {n::nat. n \<le> m \<and> cls_val_process Mkt pf n y > 0}"
  have "finite A" unfolding A_def by auto
  have "m \<in> A" using \<open>cls_val_process Mkt pf m y > 0\<close> unfolding A_def by simp
  hence "A \<noteq> {}" by auto
  hence "Min A \<in> A" using \<open>finite A\<close> by simp
  have "Min A \<le> m" using \<open>finite A\<close> \<open>m\<in> A\<close> by simp
  have "0 < Min A"
  proof -
    have "cls_val_process Mkt pf 0 y = 0" using \<open>y\<in> space M\<close> \<open>\<forall>w \<in> space M. cls_val_process Mkt pf 0 w = 0\<close>
      by simp
    hence "0\<notin> A" unfolding A_def by simp
    moreover have "0 \<le> Min A" by simp
    ultimately show ?thesis using \<open>Min A \<in> A\<close> neq0_conv by fastforce
  qed
  hence "\<exists>l. Suc l = Min A" using Suc_diff_1 by blast
  from this obtain l where "Suc l = Min A" by auto
  have "cls_val_process Mkt pf l y \<le> 0"
  proof -
    have "l < Min A" using \<open>Suc l = Min A\<close> by simp
    hence "l\<notin> A" using \<open>finite A\<close> \<open>A \<noteq> {}\<close> by auto
    moreover have "l \<le> m" using \<open>Suc l = Min A\<close> \<open>m\<in> A\<close> \<open>finite A\<close> \<open>A \<noteq> {}\<close> \<open>l < Min A\<close> by auto
    ultimately show ?thesis unfolding A_def by auto
  qed
  hence "val_process Mkt pf l y \<le> 0" using \<open>self_financing Mkt pf\<close> by (simp add:self_financingE)
  moreover have "pf stk (Suc l) y \<noteq> 0 \<or> pf risk_free_asset (Suc l) y \<noteq> 0"
  proof (rule ccontr)
    assume "\<not>(pf stk (Suc l) y \<noteq> 0 \<or> pf risk_free_asset (Suc l) y \<noteq> 0)"
    hence "pf stk (Suc l) y = 0" "pf risk_free_asset (Suc l) y = 0" by auto
    have "cls_val_process Mkt pf (Min A) y = geom_proc (Suc l) y * pf stk (Suc l) y +
      disc_rfr_proc r (Suc l) y * pf risk_free_asset (Suc l) y" using \<open>stock_portfolio Mkt pf\<close>
      \<open>Suc l = Min A\<close> stock_pf_uvp_expand[of pf l]  by simp
    also have "... = 0" using \<open>pf stk (Suc l) y = 0\<close> \<open>pf risk_free_asset (Suc l) y = 0\<close> by simp
    finally have "cls_val_process Mkt pf (Min A) y = 0" .
    moreover have "cls_val_process Mkt pf (Min A) y > 0" using \<open>Min A \<in> A\<close> unfolding A_def by simp
    ultimately show False by simp
  qed
  ultimately have "\<exists>z. cls_val_process Mkt pf (Suc l) z < 0" using assms \<open>stock_portfolio Mkt pf\<close>
    \<open>trading_strategy pf\<close> by (simp add:neg_pf_exists)
  from this obtain z where "cls_val_process Mkt pf (Suc l) z < 0" by auto
  hence "\<exists>x'. cls_val_process Mkt pf m x' < 0" using neg_pf_Suc assms \<open>trading_strategy pf\<close>
      \<open>self_financing Mkt pf\<close> \<open>Suc l = Min A\<close> \<open>Min A \<le> m\<close> \<open>stock_portfolio Mkt pf\<close> by simp
  from this obtain x' where "cls_val_process Mkt pf m x' < 0" by auto
  have "x'\<in> space M" using bernoulli_stream_space bernoulli by auto
  hence "x'\<in> {w\<in> space M. \<not>0 \<le> cls_val_process Mkt pf m w}" using \<open>cls_val_process Mkt pf m x' < 0\<close> by auto
  from \<open>AE w in M. 0 \<le> cls_val_process Mkt pf m w\<close> obtain N where
    "{w\<in> space M. \<not>0 \<le> cls_val_process Mkt pf m w} \<subseteq> N" and "emeasure M N = 0" and "N\<in> sets M" using AE_E by auto
  have "{w\<in> space M. (stake m w = stake m x')} \<subseteq> N"
  proof
    fix x
    assume "x \<in> {w \<in> space M. stake m w = stake m x'}"
    hence "x\<in> space M" and "stake m x = stake m x'" by auto
    have "cls_val_process Mkt pf m \<in> borel_measurable (G m)"
    proof -
      have "borel_adapt_stoch_proc G (cls_val_process Mkt pf)" using \<open>trading_strategy pf\<close> \<open>stock_portfolio Mkt pf\<close>
        by (meson support_adapt_def readable  stock_portfolio_def subsetCE cls_val_process_adapted)
      thus ?thesis unfolding adapt_stoch_proc_def by simp
    qed
    hence "cls_val_process Mkt pf m x' = cls_val_process Mkt pf m x"
      using  \<open>stake m x = stake m x'\<close> borel_measurable_stake[of "cls_val_process Mkt pf m" m x x']
      pseudo_proj_True_stake_image spickI stoch_proc_subalg_nat_filt[of geom_proc] geometric_process stock_filtration
          by (metis geom_rand_walk_borel_adapted measurable_from_subalg)
    hence "cls_val_process Mkt pf m x < 0" using \<open>cls_val_process Mkt pf m x' < 0\<close> by simp
    thus "x\<in> N" using \<open>{w\<in> space M. \<not>0 \<le> cls_val_process Mkt pf m w} \<subseteq> N\<close> \<open>x\<in> space M\<close>
      \<open>cls_val_process Mkt pf (Suc l) z < 0\<close> by auto
  qed
  moreover have "emeasure M {w\<in> space M. (stake m w = stake m x')} \<noteq> 0" using bernoulli_stream_pref_prob_neq_zero psgt pslt by simp
  ultimately show False using \<open>emeasure M N = 0\<close> \<open>N \<in> events\<close> emeasure_eq_0 by blast
qed


lemma (in CRR_market) viable_only_if_d:
  assumes "viable_market Mkt"
  shows "d < 1+r"
proof (rule ccontr)
  assume "\<not> d < 1+r"
  hence "1+r \<le> d" by simp
  define arb_pf where "arb_pf = (\<lambda> (x::'a) (n::nat) w. 0::real)(stk:= (\<lambda> n w. 1), risk_free_asset := (\<lambda> n w. - geom_proc 0 w))"
  have "support_set arb_pf = {stk, risk_free_asset}"
  proof
    show "support_set arb_pf \<subseteq> {stk, risk_free_asset}"
      by (simp add: arb_pf_def subset_iff support_set_def)
    have "stk\<in> support_set arb_pf" unfolding arb_pf_def support_set_def using two_stocks by simp
    moreover have "risk_free_asset\<in> support_set arb_pf" unfolding arb_pf_def support_set_def
      using two_stocks geometric_process S0_positive by simp
    ultimately show "{stk, risk_free_asset}\<subseteq> support_set arb_pf" by simp
  qed
  hence "stock_portfolio Mkt arb_pf" using stocks
    by (simp add: portfolio_def stock_portfolio_def)
  have "arbitrage_process Mkt arb_pf"
  proof (rule arbitrage_processI, intro exI conjI)
    show "self_financing Mkt arb_pf" unfolding arb_pf_def using \<open>support_set arb_pf = {stk, risk_free_asset}\<close>
      by (simp add: static_portfolio_self_financing)
    show "trading_strategy arb_pf" unfolding trading_strategy_def
    proof (intro conjI ballI)
      show "portfolio arb_pf" unfolding portfolio_def using \<open>support_set arb_pf = {stk, risk_free_asset}\<close> by simp
      fix asset
      assume "asset\<in> support_set arb_pf"
      show "borel_predict_stoch_proc G (arb_pf asset)"
      proof (cases "asset = stk")
        case True
        hence "arb_pf asset = (\<lambda> n w. 1)" unfolding arb_pf_def by (simp add: two_stocks)
        show ?thesis unfolding predict_stoch_proc_def
        proof
          show "arb_pf asset 0 \<in> borel_measurable (G 0)" using \<open>arb_pf asset = (\<lambda> n w. 1)\<close> by simp
          show "\<forall>n. arb_pf asset (Suc n) \<in> borel_measurable (G n)"
          proof
            fix n
            show "arb_pf asset (Suc n) \<in> borel_measurable (G n)" using \<open>arb_pf asset = (\<lambda> n w. 1)\<close> by simp
          qed
        qed
      next
        case False
        hence "arb_pf asset = (\<lambda> n w. - geom_proc 0 w)" using \<open>support_set arb_pf = {stk, risk_free_asset}\<close>
          \<open>asset \<in> support_set arb_pf\<close> unfolding arb_pf_def by simp
        show ?thesis unfolding predict_stoch_proc_def
        proof
          show "arb_pf asset 0 \<in> borel_measurable (G 0)" using \<open>arb_pf asset = (\<lambda> n w. - geom_proc 0 w)\<close>
            geometric_process by simp
          show "\<forall>n. arb_pf asset (Suc n) \<in> borel_measurable (G n)"
          proof
            fix n
            show "arb_pf asset (Suc n) \<in> borel_measurable (G n)" using \<open>arb_pf asset = (\<lambda> n w. - geom_proc 0 w)\<close>
              geometric_process by simp
          qed
        qed
      qed
    qed
    show "\<forall>w\<in>space M. cls_val_process Mkt arb_pf 0 w = 0"
    proof
      fix w
      assume "w\<in> space M"
      have "cls_val_process Mkt arb_pf 0 w = geom_proc 0 w * arb_pf stk (Suc 0) w +
        disc_rfr_proc r 0 w * arb_pf risk_free_asset (Suc 0) w" using stock_pf_vp_expand
        \<open>stock_portfolio Mkt arb_pf\<close>
        using \<open>self_financing Mkt arb_pf\<close> self_financingE by fastforce
      also have "... = geom_proc 0 w * (1) + disc_rfr_proc r 0 w * arb_pf risk_free_asset (Suc 0) w"
        by (simp add: arb_pf_def two_stocks)
      also have "... = geom_proc 0 w + arb_pf risk_free_asset (Suc 0) w" by simp
      also have "... = geom_proc 0 w  - geom_proc 0 w" unfolding arb_pf_def by simp
      also have "... = 0" by simp
      finally show "cls_val_process Mkt arb_pf 0 w = 0" .
    qed
    have dev: "\<forall>w\<in> space M. cls_val_process Mkt arb_pf (Suc 0) w = geom_proc (Suc 0) w - (1+r) * geom_proc 0 w"
    proof (intro ballI)
      fix w
      assume "w\<in> space M"
      have "cls_val_process Mkt arb_pf (Suc 0) w =  geom_proc (Suc 0) w * arb_pf stk (Suc 0) w +
        disc_rfr_proc r (Suc 0) w * arb_pf risk_free_asset (Suc 0) w" using stock_pf_uvp_expand
        \<open>stock_portfolio Mkt arb_pf\<close> by simp
      also have "... = geom_proc (Suc 0) w + disc_rfr_proc r (Suc 0) w * arb_pf risk_free_asset (Suc 0) w"
        by (simp add: arb_pf_def two_stocks)
      also have "... = geom_proc (Suc 0) w + (1+r) * arb_pf risk_free_asset (Suc 0) w" by simp
      also have "... = geom_proc (Suc 0) w - (1+r) * geom_proc 0 w" by (simp add:arb_pf_def)
      finally show "cls_val_process Mkt arb_pf (Suc 0) w = geom_proc (Suc 0) w - (1+r) * geom_proc 0 w" .
    qed
    have iniT: "\<forall>w\<in> space M. snth w 0 \<longrightarrow> cls_val_process Mkt arb_pf (Suc 0) w > 0"
    proof (intro ballI impI)
      fix w
      assume "w\<in> space M" and "snth w 0"
      have "cls_val_process Mkt arb_pf (Suc 0) w =  geom_proc (Suc 0) w - (1+r) * geom_proc 0 w"
        using dev \<open>w\<in> space M\<close> by simp
      also have "... = u * geom_proc 0 w - (1+r) * geom_proc 0 w" using \<open>snth w 0\<close> geometric_process by simp
      also have "... = (u - (1+r)) * geom_proc 0 w" by (simp add: left_diff_distrib)
      also have "... > 0" using S0_positive \<open>1 + r \<le> d\<close> down_lt_up geometric_process by auto
      finally show "cls_val_process Mkt arb_pf (Suc 0) w > 0" .
    qed
    have iniF: "\<forall>w\<in> space M. \<not>snth w 0 \<longrightarrow> cls_val_process Mkt arb_pf (Suc 0) w \<ge> 0"
    proof (intro ballI impI)
      fix w
      assume "w\<in> space M" and "\<not>snth w 0"
      have "cls_val_process Mkt arb_pf (Suc 0) w =  geom_proc (Suc 0) w - (1+r) * geom_proc 0 w"
        using dev \<open>w\<in> space M\<close> by simp
      also have "... = d * geom_proc 0 w - (1+r) * geom_proc 0 w" using \<open>\<not>snth w 0\<close> geometric_process by simp
      also have "... = (d - (1+r)) * geom_proc 0 w" by (simp add: left_diff_distrib)
      also have "... \<ge> 0" using S0_positive \<open>1 + r \<le> d\<close> down_lt_up geometric_process by auto
      finally show "cls_val_process Mkt arb_pf (Suc 0) w \<ge> 0" .
    qed
    have "\<forall>w\<in> space M. cls_val_process Mkt arb_pf (Suc 0) w \<ge> 0"
    proof
      fix w
      assume "w\<in> space M"
      show "cls_val_process Mkt arb_pf (Suc 0) w \<ge> 0"
      proof (cases "snth w 0")
        case True
        thus ?thesis using \<open>w\<in> space M\<close> iniT by auto
      next
        case False
        thus ?thesis using \<open>w\<in> space M\<close> iniF by simp
      qed
    qed
    thus "AE w in M. 0 \<le> cls_val_process Mkt arb_pf (Suc 0) w" by simp
    show "0 < prob {w \<in> space M. 0 < cls_val_process Mkt arb_pf (Suc 0) w}"
    proof -
      have "cls_val_process Mkt arb_pf (Suc 0) \<in> borel_measurable M" using borel_adapt_stoch_proc_borel_measurable
        cls_val_process_adapted \<open>trading_strategy arb_pf\<close> \<open>stock_portfolio Mkt arb_pf\<close>
        using support_adapt_def readable unfolding  stock_portfolio_def by blast
      hence set_event:"{w \<in> space M. 0 < cls_val_process Mkt arb_pf (Suc 0) w} \<in> sets M"
        using borel_measurable_iff_greater by blast
      have "\<forall>n. emeasure M {w \<in> space M. w !! n} = ennreal p"
        using bernoulli p_gt_0 p_lt_1 bernoulli_stream_component_probability[of M p]
        by auto
      hence "emeasure M {w \<in> space M. w !! 0} = ennreal p" by blast
      moreover have "{w \<in> space M. w !! 0} \<subseteq> {w \<in> space M. 0 < cls_val_process Mkt arb_pf 1 w}"
      proof
        fix w
        assume "w\<in> {w \<in> space M. w !! 0}"
        hence "w \<in> space M" and "w !! 0" by auto note wprops = this
        hence "0 < cls_val_process Mkt arb_pf 1 w" using iniT by simp
        thus "w\<in> {w \<in> space M. 0 < cls_val_process Mkt arb_pf 1 w}" using wprops by simp
      qed
      ultimately have "p \<le> emeasure M {w \<in> space M. 0 < cls_val_process Mkt arb_pf 1 w}"
        using emeasure_mono set_event by fastforce
      hence "p \<le> prob {w \<in> space M. 0 < cls_val_process Mkt arb_pf 1 w}" by (simp add: emeasure_eq_measure)
      thus "0 < prob {w \<in> space M. 0 < cls_val_process Mkt arb_pf (Suc 0) w}" using psgt by simp
    qed
  qed
  thus False using assms unfolding viable_market_def using \<open>stock_portfolio Mkt arb_pf\<close> by simp
qed


lemma (in CRR_market) viable_only_if_u:
  assumes "viable_market Mkt"
  shows "1+r < u"
proof (rule ccontr)
  assume "\<not> 1+r < u"
  hence "u \<le> 1+r" by simp
  define arb_pf where "arb_pf = (\<lambda> (x::'a) (n::nat) w. 0::real)(stk:= (\<lambda> n w. -1), risk_free_asset := (\<lambda> n w. geom_proc 0 w))"
  have "support_set arb_pf = {stk, risk_free_asset}"
  proof
    show "support_set arb_pf \<subseteq> {stk, risk_free_asset}"
      by (simp add: arb_pf_def subset_iff support_set_def)
    have "stk\<in> support_set arb_pf" unfolding arb_pf_def support_set_def using two_stocks by simp
    moreover have "risk_free_asset\<in> support_set arb_pf" unfolding arb_pf_def support_set_def
      using two_stocks geometric_process S0_positive by simp
    ultimately show "{stk, risk_free_asset}\<subseteq> support_set arb_pf" by simp
  qed
  hence "stock_portfolio Mkt arb_pf" using stocks
    by (simp add: portfolio_def stock_portfolio_def)
  have "arbitrage_process Mkt arb_pf"
  proof (rule arbitrage_processI, intro exI conjI)
    show "self_financing Mkt arb_pf" unfolding arb_pf_def using \<open>support_set arb_pf = {stk, risk_free_asset}\<close>
      by (simp add: static_portfolio_self_financing)
    show "trading_strategy arb_pf" unfolding trading_strategy_def
    proof (intro conjI ballI)
      show "portfolio arb_pf" unfolding portfolio_def using \<open>support_set arb_pf = {stk, risk_free_asset}\<close> by simp
      fix asset
      assume "asset\<in> support_set arb_pf"
      show "borel_predict_stoch_proc G (arb_pf asset)"
      proof (cases "asset = stk")
        case True
        hence "arb_pf asset = (\<lambda> n w. -1)" unfolding arb_pf_def by (simp add: two_stocks)
        show ?thesis unfolding predict_stoch_proc_def
        proof
          show "arb_pf asset 0 \<in> borel_measurable (G 0)" using \<open>arb_pf asset = (\<lambda> n w. -1)\<close> by simp
          show "\<forall>n. arb_pf asset (Suc n) \<in> borel_measurable (G n)"
          proof
            fix n
            show "arb_pf asset (Suc n) \<in> borel_measurable (G n)" using \<open>arb_pf asset = (\<lambda> n w. -1)\<close> by simp
          qed
        qed
      next
        case False
        hence "arb_pf asset = (\<lambda> n w. geom_proc 0 w)" using \<open>support_set arb_pf = {stk, risk_free_asset}\<close>
          \<open>asset \<in> support_set arb_pf\<close> unfolding arb_pf_def by simp
        show ?thesis unfolding predict_stoch_proc_def
        proof
          show "arb_pf asset 0 \<in> borel_measurable (G 0)" using \<open>arb_pf asset = (\<lambda> n w. geom_proc 0 w)\<close>
            geometric_process by simp
          show "\<forall>n. arb_pf asset (Suc n) \<in> borel_measurable (G n)"
          proof
            fix n
            show "arb_pf asset (Suc n) \<in> borel_measurable (G n)" using \<open>arb_pf asset = (\<lambda> n w. geom_proc 0 w)\<close>
              geometric_process by simp
          qed
        qed
      qed
    qed
    show "\<forall>w\<in>space M. cls_val_process Mkt arb_pf 0 w = 0"
    proof
      fix w
      assume "w\<in> space M"
      have "cls_val_process Mkt arb_pf 0 w = geom_proc 0 w * arb_pf stk (Suc 0) w +
        disc_rfr_proc r 0 w * arb_pf risk_free_asset (Suc 0) w" using stock_pf_vp_expand
        \<open>stock_portfolio Mkt arb_pf\<close>
        using \<open>self_financing Mkt arb_pf\<close> self_financingE by fastforce
      also have "... = geom_proc 0 w * (-1) + disc_rfr_proc r 0 w * arb_pf risk_free_asset (Suc 0) w"
        by (simp add: arb_pf_def two_stocks)
      also have "... = -geom_proc 0 w + arb_pf risk_free_asset (Suc 0) w" by simp
      also have "... = geom_proc 0 w  - geom_proc 0 w" unfolding arb_pf_def by simp
      also have "... = 0" by simp
      finally show "cls_val_process Mkt arb_pf 0 w = 0" .
    qed
    have dev: "\<forall>w\<in> space M. cls_val_process Mkt arb_pf (Suc 0) w = -geom_proc (Suc 0) w + (1+r) * geom_proc 0 w"
    proof (intro ballI)
      fix w
      assume "w\<in> space M"
      have "cls_val_process Mkt arb_pf (Suc 0) w =  geom_proc (Suc 0) w * arb_pf stk (Suc 0) w +
        disc_rfr_proc r (Suc 0) w * arb_pf risk_free_asset (Suc 0) w" using stock_pf_uvp_expand
        \<open>stock_portfolio Mkt arb_pf\<close> by simp
      also have "... = -geom_proc (Suc 0) w + disc_rfr_proc r (Suc 0) w * arb_pf risk_free_asset (Suc 0) w"
        by (simp add: arb_pf_def two_stocks)
      also have "... = -geom_proc (Suc 0) w + (1+r) * arb_pf risk_free_asset (Suc 0) w" by simp
      also have "... = -geom_proc (Suc 0) w + (1+r) * geom_proc 0 w" by (simp add:arb_pf_def)
      finally show "cls_val_process Mkt arb_pf (Suc 0) w = -geom_proc (Suc 0) w + (1+r) * geom_proc 0 w" .
    qed
    have iniT: "\<forall>w\<in> space M. snth w 0 \<longrightarrow> cls_val_process Mkt arb_pf (Suc 0) w \<ge> 0"
    proof (intro ballI impI)
      fix w
      assume "w\<in> space M" and "snth w 0"
      have "cls_val_process Mkt arb_pf (Suc 0) w =  -geom_proc (Suc 0) w + (1+r) * geom_proc 0 w"
        using dev \<open>w\<in> space M\<close> by simp
      also have "... = - u * geom_proc 0 w + (1+r) * geom_proc 0 w" using \<open>snth w 0\<close> geometric_process by simp
      also have "... = (-u + (1+r)) * geom_proc 0 w" by (simp add: left_diff_distrib)
      also have "... \<ge> 0" using S0_positive \<open>u\<le> 1 + r\<close> down_lt_up geometric_process by auto
      finally show "cls_val_process Mkt arb_pf (Suc 0) w \<ge> 0" .
    qed
    have iniF: "\<forall>w\<in> space M. \<not>snth w 0 \<longrightarrow> cls_val_process Mkt arb_pf (Suc 0) w > 0"
    proof (intro ballI impI)
      fix w
      assume "w\<in> space M" and "\<not>snth w 0"
      have "cls_val_process Mkt arb_pf (Suc 0) w =  -geom_proc (Suc 0) w + (1+r) * geom_proc 0 w"
        using dev \<open>w\<in> space M\<close> by simp
      also have "... = -d * geom_proc 0 w + (1+r) * geom_proc 0 w" using \<open>\<not>snth w 0\<close> geometric_process by simp
      also have "... = (-d + (1+r)) * geom_proc 0 w" by (simp add: left_diff_distrib)
      also have "... > 0" using S0_positive \<open>u <= 1 + r\<close> down_lt_up geometric_process by auto
      finally show "cls_val_process Mkt arb_pf (Suc 0) w > 0" .
    qed
    have "\<forall>w\<in> space M. cls_val_process Mkt arb_pf (Suc 0) w \<ge> 0"
    proof
      fix w
      assume "w\<in> space M"
      show "cls_val_process Mkt arb_pf (Suc 0) w \<ge> 0"
      proof (cases "snth w 0")
        case True
        thus ?thesis using \<open>w\<in> space M\<close> iniT by simp
      next
        case False
        thus ?thesis using \<open>w\<in> space M\<close> iniF by auto
      qed
    qed
    thus "AE w in M. 0 \<le> cls_val_process Mkt arb_pf (Suc 0) w" by simp
    show "0 < prob {w \<in> space M. 0 < cls_val_process Mkt arb_pf (Suc 0) w}"
    proof -
      have "cls_val_process Mkt arb_pf (Suc 0) \<in> borel_measurable M" using borel_adapt_stoch_proc_borel_measurable
        cls_val_process_adapted \<open>trading_strategy arb_pf\<close> \<open>stock_portfolio Mkt arb_pf\<close>
         using support_adapt_def readable unfolding stock_portfolio_def by blast
      hence set_event:"{w \<in> space M. 0 < cls_val_process Mkt arb_pf (Suc 0) w} \<in> sets M"
        using borel_measurable_iff_greater by blast
      have "\<forall>n. emeasure M {w \<in> space M. \<not>w !! n} = ennreal (1-p)"
        using bernoulli p_gt_0 p_lt_1 bernoulli_stream_component_probability_compl[of M p]
        by auto
      hence "emeasure M {w \<in> space M. \<not>w !! 0} = ennreal (1-p)" by blast
      moreover have "{w \<in> space M. \<not>w !! 0} \<subseteq> {w \<in> space M. 0 < cls_val_process Mkt arb_pf 1 w}"
      proof
        fix w
        assume "w\<in> {w \<in> space M. \<not>w !! 0}"
        hence "w \<in> space M" and "\<not>w !! 0" by auto note wprops = this
        hence "0 < cls_val_process Mkt arb_pf 1 w" using iniF by simp
        thus "w\<in> {w \<in> space M. 0 < cls_val_process Mkt arb_pf 1 w}" using wprops by simp
      qed
      ultimately have "1-p \<le> emeasure M {w \<in> space M. 0 < cls_val_process Mkt arb_pf 1 w}"
        using emeasure_mono set_event by fastforce
      hence "1-p \<le> prob {w \<in> space M. 0 < cls_val_process Mkt arb_pf 1 w}" by (simp add: emeasure_eq_measure)
      thus "0 < prob {w \<in> space M. 0 < cls_val_process Mkt arb_pf (Suc 0) w}" using pslt by simp
    qed
  qed
  thus False using assms unfolding viable_market_def using \<open>stock_portfolio Mkt arb_pf\<close> by simp
qed

lemma (in CRR_market) viable_iff:
shows "viable_market Mkt \<longleftrightarrow> (d < 1+r \<and> 1+r < u)" using viable_if viable_only_if_d viable_only_if_u by auto


subsection \<open>Risk-neutral probability space for the geometric random walk\<close>



lemma (in CRR_market) stock_price_borel_measurable:
  shows "borel_adapt_stoch_proc G (prices Mkt stk)"
proof -
  have "borel_adapt_stoch_proc (stoch_proc_filt M geom_proc borel) (prices Mkt stk)"
    by (simp add: geom_rand_walk_borel_measurable stk_price stoch_proc_filt_adapt)
  thus ?thesis by (simp add:stock_filtration)
qed


lemma (in CRR_market) risk_free_asset_martingale:
  assumes "N = bernoulli_stream q"
  and "0 < q"
  and "q < 1"
  shows "martingale N G (discounted_value r (prices Mkt risk_free_asset))"
proof -
  have "filtration N G" by (simp add: assms bernoulli_gen_filtration)
  moreover have "\<forall>n. sigma_finite_subalgebra N (G n)" by (simp add: assms bernoulli_sigma_finite)
  moreover have "finite_measure N" using assms bernoulli_stream_def prob_space.prob_space_stream_space
    prob_space_def prob_space_measure_pmf by auto
  moreover have "discounted_value r (prices Mkt risk_free_asset) = (\<lambda> n w. 1)" using discounted_rfr by auto
  ultimately show ?thesis using finite_measure.constant_martingale by simp
qed


lemma (in infinite_coin_toss_space) nat_filtration_from_eq_sets:
  assumes "N = bernoulli_stream q"
  and "0 < q"
  and "q < 1"
shows "sets (infinite_coin_toss_space.nat_filtration N n) = sets (nat_filtration n)"
proof -
  have "sigma_sets (space (bernoulli_stream q)) {pseudo_proj_True n -` B \<inter> space N |B. B \<in> sets (bernoulli_stream q)} = sigma_sets (space (bernoulli_stream p))
          {pseudo_proj_True n -` B \<inter> space M |B. B \<in> sets (bernoulli_stream p)}"
  proof -
    have "sets N = events"
      by (metis assms(1) bernoulli_stream_def infinite_coin_toss_space_axioms infinite_coin_toss_space_def sets_measure_pmf sets_stream_space_cong)
    then show ?thesis
      using assms(1) bernoulli_stream_space infinite_coin_toss_space_axioms infinite_coin_toss_space_def by auto
  qed
  thus ?thesis using infinite_coin_toss_space.nat_filtration_sets
    using assms(1) assms(2) assms(3) infinite_coin_toss_space_axioms infinite_coin_toss_space_def by auto
qed




lemma (in CRR_market) geom_proc_integrable:
  assumes "N = bernoulli_stream q"
and "0 \<le> q"
and "q \<le> 1"
shows "integrable N (geom_proc n)"
proof (rule infinite_coin_toss_space.nat_filtration_borel_measurable_integrable)
  show "infinite_coin_toss_space q N" using assms by unfold_locales
  show "geom_proc n \<in> borel_measurable (infinite_coin_toss_space.nat_filtration N n)" using geometric_process
    prob_grw.geom_rand_walk_borel_adapted[of q N geom_proc u d init]
    by (metis \<open>infinite_coin_toss_space q N\<close> geom_rand_walk_pseudo_proj_True infinite_coin_toss_space.nat_filtration_borel_measurable_characterization
         prob_grw.geom_rand_walk_borel_measurable prob_grw_axioms prob_grw_def)
qed

lemma (in CRR_market) CRR_infinite_cts_filtration:
  shows "infinite_cts_filtration p M nat_filtration"
  by (unfold_locales, simp)


lemma (in CRR_market) proj_stoch_proc_geom_disc_fct:
  shows "disc_fct (proj_stoch_proc geom_proc n)" unfolding disc_fct_def using CRR_infinite_cts_filtration
    by (simp add: countable_finite geom_rand_walk_borel_adapted infinite_cts_filtration.proj_stoch_set_finite_range)

lemma (in CRR_market) proj_stoch_proc_geom_rng:
  assumes "N = bernoulli_stream q"
shows  "proj_stoch_proc geom_proc n \<in> N \<rightarrow>\<^sub>M stream_space borel"
proof -
  have "random_variable (stream_space borel) (proj_stoch_proc geom_proc n)" using CRR_infinite_cts_filtration
    using geom_rand_walk_borel_adapted nat_discrete_filtration proj_stoch_measurable_if_adapted by blast
  then show ?thesis
    using assms(1) bernoulli bernoulli_stream_def by auto
qed

lemma (in CRR_market) proj_stoch_proc_geom_open_set:
  shows  "\<forall>r\<in>range (proj_stoch_proc geom_proc n) \<inter> space (stream_space borel).
     \<exists>A\<in>sets (stream_space borel). range (proj_stoch_proc geom_proc n) \<inter> A = {r}"
proof
  fix r
  assume "r\<in> range (proj_stoch_proc geom_proc n) \<inter> space (stream_space borel)"
  show "\<exists>A\<in>sets (stream_space borel). range (proj_stoch_proc geom_proc n) \<inter> A = {r}"
  proof
    show "infinite_cts_filtration.stream_space_single (proj_stoch_proc geom_proc n) r \<in> sets (stream_space borel)"
      using infinite_cts_filtration.stream_space_single_set \<open>r \<in> range (proj_stoch_proc geom_proc n) \<inter> space (stream_space borel)\<close>
        geom_rand_walk_borel_adapted CRR_infinite_cts_filtration by blast
    show "range (proj_stoch_proc geom_proc n) \<inter> infinite_cts_filtration.stream_space_single (proj_stoch_proc geom_proc n) r = {r}"
      using infinite_cts_filtration.stream_space_single_preimage \<open>r \<in> range (proj_stoch_proc geom_proc n) \<inter> space (stream_space borel)\<close>
        geom_rand_walk_borel_adapted CRR_infinite_cts_filtration by blast
  qed
qed

lemma (in CRR_market) bernoulli_AE_cond_exp:
  assumes "N = bernoulli_stream q"
and "0 < q"
and "q < 1"
and "integrable N X"
shows "AE w in N. real_cond_exp N (fct_gen_subalgebra N (stream_space borel) (proj_stoch_proc geom_proc n)) X w =
    expl_cond_expect N (proj_stoch_proc geom_proc n) X w"
proof (rule finite_measure.charact_cond_exp')
  have "infinite_cts_filtration p M nat_filtration"
    by (unfold_locales, simp)
  show "finite_measure N" using assms
    by (simp add: bernoulli_stream_def prob_space.finite_measure prob_space.prob_space_stream_space prob_space_measure_pmf)
  show "disc_fct (proj_stoch_proc geom_proc n)" using proj_stoch_proc_geom_disc_fct by simp
  show "integrable N X"  using assms by simp
  show "proj_stoch_proc geom_proc n \<in> N \<rightarrow>\<^sub>M stream_space borel" using assms proj_stoch_proc_geom_rng by simp
  show "\<forall>r\<in>range (proj_stoch_proc geom_proc n) \<inter> space (stream_space borel).
     \<exists>A\<in>sets (stream_space borel). range (proj_stoch_proc geom_proc n) \<inter> A = {r}"
    using proj_stoch_proc_geom_open_set by simp
qed

lemma (in CRR_market) geom_proc_cond_exp:
  assumes "N = bernoulli_stream q"
and "0 < q"
and "q < 1"
shows "AE w in N. real_cond_exp N (fct_gen_subalgebra N (stream_space borel) (proj_stoch_proc geom_proc n)) (geom_proc (Suc n)) w =
    expl_cond_expect N (proj_stoch_proc geom_proc n) (geom_proc (Suc n)) w"
proof (rule bernoulli_AE_cond_exp)
  show "integrable N (geom_proc (Suc n))"  using assms geom_proc_integrable[of N q "Suc n"] by simp
qed (auto simp add: assms)


lemma (in CRR_market) expl_cond_eq_sets:
  assumes "N = bernoulli_stream q"
  shows  "expl_cond_expect N (proj_stoch_proc geom_proc n) X \<in>
        borel_measurable (fct_gen_subalgebra N (stream_space borel) (proj_stoch_proc geom_proc n))"
proof (rule expl_cond_exp_borel)
  show "proj_stoch_proc geom_proc n \<in> space N \<rightarrow> space (stream_space borel)"
  proof -
    have "random_variable (stream_space borel) (proj_stoch_proc geom_proc n)"
      using CRR_infinite_cts_filtration geom_rand_walk_borel_adapted proj_stoch_measurable_if_adapted
        nat_discrete_filtration by blast
    then show ?thesis
      by (simp add: assms(1) bernoulli bernoulli_stream_space measurable_def)
  qed
  show "disc_fct (proj_stoch_proc geom_proc n)" unfolding disc_fct_def using CRR_infinite_cts_filtration
    by (simp add: countable_finite geom_rand_walk_borel_adapted infinite_cts_filtration.proj_stoch_set_finite_range)
  show "\<forall>r\<in>range (proj_stoch_proc geom_proc n) \<inter> space (stream_space borel).
    \<exists>A\<in>sets (stream_space borel). range (proj_stoch_proc geom_proc n) \<inter> A = {r}"
  proof
    fix r
    assume "r\<in>range (proj_stoch_proc geom_proc n) \<inter> space (stream_space borel)"
    show "\<exists>A\<in>sets (stream_space borel). range (proj_stoch_proc geom_proc n) \<inter> A = {r}"
    proof
      show "infinite_cts_filtration.stream_space_single (proj_stoch_proc geom_proc n) r \<in> sets (stream_space borel)"
        using infinite_cts_filtration.stream_space_single_set \<open>r \<in> range (proj_stoch_proc geom_proc n) \<inter> space (stream_space borel)\<close>
          geom_rand_walk_borel_adapted CRR_infinite_cts_filtration by blast
      show "range (proj_stoch_proc geom_proc n) \<inter> infinite_cts_filtration.stream_space_single (proj_stoch_proc geom_proc n) r = {r}"
        using infinite_cts_filtration.stream_space_single_preimage \<open>r \<in> range (proj_stoch_proc geom_proc n) \<inter> space (stream_space borel)\<close>
          geom_rand_walk_borel_adapted CRR_infinite_cts_filtration by blast
    qed
  qed
qed


lemma (in CRR_market) bernoulli_real_cond_exp_AE:
  assumes "N = bernoulli_stream q"
and "0 < q"
and "q < 1"
and "integrable N X"
shows "real_cond_exp N (fct_gen_subalgebra N (stream_space borel) (proj_stoch_proc geom_proc n))
   X w = expl_cond_expect N (proj_stoch_proc geom_proc n) X w"
proof -
  have "real_cond_exp N (fct_gen_subalgebra N (stream_space borel) (proj_stoch_proc geom_proc n))
   X w = expl_cond_expect N (proj_stoch_proc geom_proc n) X w"
  proof (rule infinite_coin_toss_space.nat_filtration_AE_eq)
    show "infinite_coin_toss_space q N" using assms
      by (simp add: infinite_coin_toss_space_def)
    show "AE w in N. real_cond_exp N (fct_gen_subalgebra N (stream_space borel) (proj_stoch_proc geom_proc n)) X w =
    expl_cond_expect N (proj_stoch_proc geom_proc n) X w"  using assms bernoulli_AE_cond_exp by simp
    show "real_cond_exp N (fct_gen_subalgebra N (stream_space borel) (proj_stoch_proc geom_proc n)) X
      \<in> borel_measurable (infinite_coin_toss_space.nat_filtration N n)"
    proof -
      have "real_cond_exp N (fct_gen_subalgebra N (stream_space borel) (proj_stoch_proc geom_proc n)) X
        \<in> borel_measurable (fct_gen_subalgebra N (stream_space borel) (proj_stoch_proc geom_proc n))"
        by simp
      moreover have "subalgebra (infinite_coin_toss_space.nat_filtration N n) (fct_gen_subalgebra N (stream_space borel) (proj_stoch_proc geom_proc n))"
        using stock_filtration infinite_coin_toss_space.stoch_proc_subalg_nat_filt[of q N geom_proc n]
        infinite_cts_filtration.stoch_proc_filt_gen[of q N]
        by (metis \<open>infinite_coin_toss_space q N\<close> infinite_cts_filtration_axioms.intro infinite_cts_filtration_def
            prob_grw.geom_rand_walk_borel_adapted prob_grw_axioms prob_grw_def)
      ultimately show ?thesis using measurable_from_subalg by blast
    qed
    show "expl_cond_expect N (proj_stoch_proc geom_proc n) X \<in>
      borel_measurable (infinite_coin_toss_space.nat_filtration N n)"
    proof -
      have "expl_cond_expect N (proj_stoch_proc geom_proc n) X \<in>
        borel_measurable (fct_gen_subalgebra N (stream_space borel) (proj_stoch_proc geom_proc n))"
        by (simp add: expl_cond_eq_sets assms)
      moreover have "subalgebra (infinite_coin_toss_space.nat_filtration N n) (fct_gen_subalgebra N (stream_space borel) (proj_stoch_proc geom_proc n))"
      using stock_filtration infinite_coin_toss_space.stoch_proc_subalg_nat_filt[of q N geom_proc n]
        infinite_cts_filtration.stoch_proc_filt_gen[of q N]
        by (metis \<open>infinite_coin_toss_space q N\<close> infinite_cts_filtration_axioms.intro infinite_cts_filtration_def
            prob_grw.geom_rand_walk_borel_adapted prob_grw_axioms prob_grw_def)
      ultimately show ?thesis using measurable_from_subalg by blast
    qed
    show "0 < q" and "q < 1" using assms by auto
  qed
  thus ?thesis by simp
qed

lemma (in CRR_market) geom_proc_real_cond_exp_AE:
  assumes "N = bernoulli_stream q"
and "0 < q"
and "q < 1"
shows "real_cond_exp N (fct_gen_subalgebra N (stream_space borel) (proj_stoch_proc geom_proc n))
   (geom_proc (Suc n)) w = expl_cond_expect N (proj_stoch_proc geom_proc n) (geom_proc (Suc n)) w"
proof (rule bernoulli_real_cond_exp_AE)
show "integrable N (geom_proc (Suc n))"  using assms geom_proc_integrable[of N q "Suc n"] by simp
qed (auto simp add: assms)


lemma (in CRR_market) geom_proc_stoch_proc_filt:
  assumes "N= bernoulli_stream q"
and "0 < q"
and "q < 1"
shows "stoch_proc_filt N geom_proc borel n = fct_gen_subalgebra N (stream_space borel) (proj_stoch_proc geom_proc n)"
proof (rule infinite_cts_filtration.stoch_proc_filt_gen)
  show "infinite_cts_filtration q N (infinite_coin_toss_space.nat_filtration N)" unfolding infinite_cts_filtration_def
  proof
    show "infinite_coin_toss_space q N" using assms
      by (simp add: infinite_coin_toss_space_def)
    show "infinite_cts_filtration_axioms N (infinite_coin_toss_space.nat_filtration N)"
      using infinite_cts_filtration_axioms_def by blast
  qed
  show "borel_adapt_stoch_proc (infinite_coin_toss_space.nat_filtration N) geom_proc"
    using \<open>infinite_cts_filtration q N (infinite_coin_toss_space.nat_filtration N)\<close>
      prob_grw.geom_rand_walk_borel_adapted prob_grw_axioms prob_grw_def
    using infinite_cts_filtration_def by auto
qed

lemma (in CRR_market) bernoulli_cond_exp:
  assumes "N = bernoulli_stream q"
  and "0 < q"
  and "q < 1"
and "integrable N X"
shows "real_cond_exp N (stoch_proc_filt N geom_proc borel n) X w = expl_cond_expect N (proj_stoch_proc geom_proc n) X w"
proof -
  have aeq: "AE w in N. real_cond_exp N (fct_gen_subalgebra N (stream_space borel) (proj_stoch_proc geom_proc n)) X w =
    expl_cond_expect N (proj_stoch_proc geom_proc n) X w"  using assms
    bernoulli_AE_cond_exp by simp
  have "\<forall>w. real_cond_exp N (fct_gen_subalgebra N (stream_space borel) (proj_stoch_proc geom_proc n))
   X w = expl_cond_expect N (proj_stoch_proc geom_proc n) X w"  using assms bernoulli_real_cond_exp_AE by simp
  moreover have "stoch_proc_filt N geom_proc borel n = fct_gen_subalgebra N (stream_space borel) (proj_stoch_proc geom_proc n)"
    using assms geom_proc_stoch_proc_filt by simp
  ultimately show ?thesis by simp
qed

lemma (in CRR_market) stock_cond_exp:
  assumes "N = bernoulli_stream q"
  and "0 < q"
  and "q < 1"
shows "real_cond_exp N (stoch_proc_filt N geom_proc borel n) (geom_proc (Suc n)) w = expl_cond_expect N (proj_stoch_proc geom_proc n) (geom_proc (Suc n)) w"
proof (rule bernoulli_cond_exp)
show "integrable N (geom_proc (Suc n))"  using assms geom_proc_integrable[of N q "Suc n"] by simp
qed (auto simp add: assms)




lemma (in prob_space) discount_factor_real_cond_exp:
  assumes "integrable M X"
and "subalgebra M G"
and "-1 < r"
shows "AE w in M. real_cond_exp M G (\<lambda>x. discount_factor r n x * X x) w = discount_factor r n w * (real_cond_exp M G X) w"
proof (rule sigma_finite_subalgebra.real_cond_exp_mult)
  show "sigma_finite_subalgebra M G" using assms subalgebra_sigma_finite by simp
  show "discount_factor r n \<in> borel_measurable G" by (simp add: discount_factor_borel_measurable)
  show "random_variable borel X" using assms by simp
  show "integrable M (\<lambda>x. discount_factor r n x * X x)"  using assms discounted_integrable[of M "\<lambda>n. X"]
    unfolding discounted_value_def by simp
qed


lemma (in prob_space) discounted_value_real_cond_exp:
  assumes "integrable M X"
  and "-1 < r"
and "subalgebra M G"
  shows "AE w in M. real_cond_exp M G ((discounted_value r (\<lambda> m. X)) n) w =
    discounted_value r (\<lambda>m. (real_cond_exp M G X)) n w" using  assms
  unfolding discounted_value_def  init_triv_filt_def filtration_def
  by (simp add: assms discount_factor_real_cond_exp)


lemma (in CRR_market)
  assumes "q = (1 + r - d)/(u -d)"
  and "viable_market Mkt"
  shows gt_param: "0 < q"
    and lt_param: "q < 1"
    and risk_neutral_param: "u * q + d * (1 - q) = 1 + r"
proof -
  show "0 < q" using  down_lt_up viable_only_if_d assms by simp
  show "q < 1" using down_lt_up viable_only_if_u assms by simp
  show "u * q + d * (1 - q) = 1 + r"
  proof -
    have "1 - q = 1 - (1 + r - d) / (u - d)" using assms by simp
    also have "... = (u - d)/(u - d) - (1 + r - d) / (u - d)" using down_lt_up by simp
    also have "... = (u - d - (1 + r - d))/(u-d)" using  diff_divide_distrib[of "u - d" "1 + r -d" "u -d"] by simp
    also have "... = (u - 1 - r)/(u-d)" by simp
    finally have "1 - q = (u - 1 - r)/(u -d)" .
    hence "u * q + d * (1 - q) = u * (1 + r - d)/(u - d) + d * (u - 1 - r)/(u - d)" using assms by simp
    also have "... = (u * (1 + r - d) + d * (u - 1 - r))/(u - d)" using add_divide_distrib[of "u * (1 + r - d)"] by simp
    also have "... = (u * (1 + r) - u * d + d * u - d * (1 + r))/(u - d)"
      by (simp add: diff_diff_add right_diff_distrib')
    also have "... = (u * (1+r) - d * (1+r))/(u - d)" by simp
    also have "... = ((u - d) * (1+r))/(u - d)" by (simp add: left_diff_distrib)
    also have "... = 1 + r" using down_lt_up by simp
    finally show ?thesis .
  qed
qed

lemma (in CRR_market) bernoulli_expl_cond_expect_adapt:
  assumes "N = bernoulli_stream q"
and "0 < q"
and "q < 1"
  shows "expl_cond_expect N (proj_stoch_proc geom_proc n) f\<in> borel_measurable (G n)"
proof -
  have "sets N = sets M" using assms by (simp add: bernoulli bernoulli_stream_def sets_stream_space_cong)
  have icf: "infinite_cts_filtration p M nat_filtration" by (unfold_locales, simp)
  have "G n = stoch_proc_filt M geom_proc borel n" using stock_filtration by simp
  also have "... = fct_gen_subalgebra M (stream_space borel) (proj_stoch_proc geom_proc n)"
  proof (rule infinite_cts_filtration.stoch_proc_filt_gen)
    show "infinite_cts_filtration p M nat_filtration" using icf .
    show "borel_adapt_stoch_proc nat_filtration geom_proc" using geom_rand_walk_borel_adapted .
  qed
  also have "... = fct_gen_subalgebra N (stream_space borel) (proj_stoch_proc geom_proc n)"
    by (rule fct_gen_subalgebra_eq_sets, (simp add: \<open>sets N = sets M\<close>))
  finally have "G n = fct_gen_subalgebra N (stream_space borel) (proj_stoch_proc geom_proc n)" .
  moreover have "expl_cond_expect N (proj_stoch_proc geom_proc n) f \<in>
    borel_measurable (fct_gen_subalgebra N (stream_space borel) (proj_stoch_proc geom_proc n))"
    by (simp add: expl_cond_eq_sets assms)
  ultimately show ?thesis by simp
qed



lemma (in CRR_market) real_cond_exp_discount_stock:
  assumes "N = bernoulli_stream q"
and "0 < q"
and "q < 1"
shows "AE w in N. real_cond_exp N (G n)
   (discounted_value r (prices Mkt stk) (Suc n)) w =
                  discounted_value r (\<lambda>m w. (q * u + (1 - q) * d) * prices Mkt stk n w) (Suc n) w"
proof -
  have qlt: "0 < q" and qgt: "q < 1" using assms by auto
  have "G n = (fct_gen_subalgebra M (stream_space borel)
                                (proj_stoch_proc geom_proc n))"
    using stock_filtration infinite_cts_filtration.stoch_proc_filt_gen[of p M nat_filtration geom_proc n] geometric_process
      geom_rand_walk_borel_adapted CRR_infinite_cts_filtration by simp
  also have "... = (fct_gen_subalgebra N (stream_space borel)
                                (proj_stoch_proc geom_proc n))"
  proof (rule fct_gen_subalgebra_eq_sets)
    show "events = sets N" using assms qlt qgt
      by (simp add: bernoulli bernoulli_stream_def sets_stream_space_cong)
  qed
  finally have "G n = (fct_gen_subalgebra N (stream_space borel)
                                (proj_stoch_proc geom_proc n))" .
  hence "AE w in N. real_cond_exp N (G n)
   (discounted_value r (prices Mkt stk) (Suc n)) w = real_cond_exp N (fct_gen_subalgebra N (stream_space borel)
                                (proj_stoch_proc geom_proc n))
                                (discounted_value r (prices Mkt stk) (Suc n)) w" by simp
  moreover have "AE w in N. real_cond_exp N (fct_gen_subalgebra N (stream_space borel)
                                (proj_stoch_proc geom_proc n))
                                (discounted_value r (prices Mkt stk) (Suc n)) w =
                            real_cond_exp N (fct_gen_subalgebra N (stream_space borel)
                                (proj_stoch_proc geom_proc n))
                                (discounted_value r (\<lambda>m. (prices Mkt stk) (Suc n)) (Suc n)) w"
  proof -
    have "\<forall>w. (discounted_value r (prices Mkt stk) (Suc n)) w =
      (discounted_value r (\<lambda>m. (prices Mkt stk) (Suc n)) (Suc n)) w"
    proof
      fix w
      show "discounted_value r (prices Mkt stk) (Suc n) w = discounted_value r (\<lambda>m. prices Mkt stk (Suc n)) (Suc n) w"
        by (simp add: discounted_value_def)
    qed
    hence "(discounted_value r (prices Mkt stk) (Suc n)) =
      (discounted_value r (\<lambda>m. (prices Mkt stk) (Suc n)) (Suc n))" by auto
    thus ?thesis by simp
    qed
  moreover have "AE w in N. (real_cond_exp N (fct_gen_subalgebra N (stream_space borel)
                                (proj_stoch_proc geom_proc n))
                                (discounted_value r (\<lambda>m. (prices Mkt stk) (Suc n)) (Suc n))) w =
               discounted_value r (\<lambda>m. real_cond_exp N (fct_gen_subalgebra N (stream_space borel)
                                                     (proj_stoch_proc geom_proc n))
                                                     ((prices Mkt stk) (Suc n))) (Suc n) w"
  proof (rule prob_space.discounted_value_real_cond_exp)
    show "-1 < r" using acceptable_rate by simp
    show "integrable N (prices Mkt stk (Suc n))" using stk_price geom_proc_integrable assms qlt qgt by simp
    show "subalgebra N (fct_gen_subalgebra N (stream_space borel) (proj_stoch_proc geom_proc n))"
    proof (rule fct_gen_subalgebra_is_subalgebra)
      show "proj_stoch_proc geom_proc n \<in> N \<rightarrow>\<^sub>M stream_space borel"
      proof -
        have "proj_stoch_proc geom_proc n \<in> measurable M (stream_space borel)"
        proof (rule proj_stoch_measurable_if_adapted)
          show "borel_adapt_stoch_proc nat_filtration geom_proc" using
            geometric_process
            geom_rand_walk_borel_adapted by simp
          show "filtration M nat_filtration" using CRR_infinite_cts_filtration
            by (simp add: nat_discrete_filtration)
        qed
        thus ?thesis using assms bernoulli_stream_equiv filt_equiv_measurable qlt qgt psgt pslt by blast
      qed
    qed
    show "prob_space N" using assms
      by (simp add: bernoulli bernoulli_stream_def prob_space.prob_space_stream_space prob_space_measure_pmf)
  qed
  moreover have "AE w in N. discounted_value r (\<lambda>m. real_cond_exp N (fct_gen_subalgebra N (stream_space borel)
                                                     (proj_stoch_proc geom_proc n))
                                                     ((prices Mkt stk) (Suc n))) (Suc n) w =
                    discounted_value r (\<lambda>m w. (q * u + (1 - q) * d) * prices Mkt stk n w) (Suc n) w"
  proof (rule discounted_AE_cong)
   have "AEeq N (real_cond_exp N (fct_gen_subalgebra N (stream_space borel)
                                (proj_stoch_proc geom_proc n))
                                ((prices Mkt stk) (Suc n)))
               (\<lambda>w. q * (prices Mkt stk) (Suc n) (pseudo_proj_True n w) +
                (1 - q) * (prices Mkt stk) (Suc n) (pseudo_proj_False n w))"
     proof (rule infinite_cts_filtration.f_borel_Suc_real_cond_exp)
      show icf: "infinite_cts_filtration q N (infinite_coin_toss_space.nat_filtration N)" unfolding infinite_cts_filtration_def
      proof
        show "infinite_coin_toss_space q N" using assms qlt qgt
          by (simp add: infinite_coin_toss_space_def)
        show "infinite_cts_filtration_axioms N (infinite_coin_toss_space.nat_filtration N)"
          using infinite_cts_filtration_axioms_def by blast
      qed
      have badapt: "borel_adapt_stoch_proc (infinite_coin_toss_space.nat_filtration N) (prices Mkt stk)"
        using stk_price prob_grw.geom_rand_walk_borel_adapted[of q N  geom_proc]
        unfolding adapt_stoch_proc_def
        by (metis (full_types) borel_measurable_integrable geom_proc_integrable geom_rand_walk_pseudo_proj_True icf
            infinite_coin_toss_space.nat_filtration_borel_measurable_characterization infinite_coin_toss_space_def
            infinite_cts_filtration_def)
      show "prices Mkt stk (Suc n) \<in> borel_measurable (infinite_coin_toss_space.nat_filtration N (Suc n))"
        using badapt unfolding adapt_stoch_proc_def by simp
      show "proj_stoch_proc geom_proc n \<in> infinite_coin_toss_space.nat_filtration N n \<rightarrow>\<^sub>M stream_space borel"
      proof (rule proj_stoch_adapted_if_adapted)
        show "filtration N (infinite_coin_toss_space.nat_filtration N)" using icf
          using infinite_coin_toss_space.nat_discrete_filtration infinite_cts_filtration_def by blast
        show "borel_adapt_stoch_proc (infinite_coin_toss_space.nat_filtration N) geom_proc" using badapt stk_price by simp
      qed
      show "set_discriminating n (proj_stoch_proc geom_proc n) (stream_space borel)" unfolding set_discriminating_def
      proof (intro allI impI)
        fix w
        assume "proj_stoch_proc geom_proc n w \<noteq> proj_stoch_proc geom_proc n (pseudo_proj_True n w)"
        hence False using CRR_infinite_cts_filtration
          by (metis \<open>proj_stoch_proc geom_proc n w \<noteq> proj_stoch_proc geom_proc n (pseudo_proj_True n w)\<close>
            geom_rand_walk_borel_adapted infinite_cts_filtration.proj_stoch_proj_invariant)
        thus "\<exists>A\<in>sets (stream_space borel).
      (proj_stoch_proc geom_proc n w \<in> A) = (proj_stoch_proc geom_proc n (pseudo_proj_True n w) \<notin> A)" by simp
      qed
      show "\<forall>w. proj_stoch_proc geom_proc n -` {proj_stoch_proc geom_proc n w} \<in>
        sets (infinite_coin_toss_space.nat_filtration N n)"
      proof
        fix w
        show "proj_stoch_proc geom_proc n -` {proj_stoch_proc geom_proc n w} \<in> sets (infinite_coin_toss_space.nat_filtration N n)"
          using \<open>proj_stoch_proc geom_proc n \<in> infinite_coin_toss_space.nat_filtration N n \<rightarrow>\<^sub>M stream_space borel\<close>
          using assms geom_rand_walk_borel_adapted nat_filtration_from_eq_sets   qlt qgt
            infinite_cts_filtration.proj_stoch_singleton_set CRR_infinite_cts_filtration by blast
      qed
      show "\<forall>r\<in>range (proj_stoch_proc geom_proc n) \<inter> space (stream_space borel).
        \<exists>A\<in>sets (stream_space borel). range (proj_stoch_proc geom_proc n) \<inter> A = {r}"
      proof
        fix r
        assume asm: "r \<in> range (proj_stoch_proc geom_proc n) \<inter> space (stream_space borel)"
        define A where "A = infinite_cts_filtration.stream_space_single (proj_stoch_proc geom_proc n) r"
        have "A \<in> sets (stream_space borel)"  using infinite_cts_filtration.stream_space_single_set
          unfolding A_def using badapt icf stk_price asm by blast
        moreover have "range (proj_stoch_proc geom_proc n) \<inter> A = {r}"
          unfolding A_def using badapt icf stk_price infinite_cts_filtration.stream_space_single_preimage asm by blast
        ultimately show "\<exists>A\<in>sets (stream_space borel). range (proj_stoch_proc geom_proc n) \<inter> A = {r}" by auto
      qed
      show "\<forall>y z. proj_stoch_proc geom_proc n y = proj_stoch_proc geom_proc n z \<and> y !! n = z !! n \<longrightarrow>
        prices Mkt stk (Suc n) y = prices Mkt stk (Suc n) z"
      proof (intro allI impI)
        fix y z
        assume "proj_stoch_proc geom_proc n y = proj_stoch_proc geom_proc n z \<and> y !! n = z !! n"
        hence "geom_proc n y = geom_proc n z" using proj_stoch_proc_component(2)[of n n]
        proof -
          show ?thesis
            by (metis \<open>\<And>w f. n \<le> n \<Longrightarrow> proj_stoch_proc f n w !! n = f n w\<close> \<open>proj_stoch_proc geom_proc n y = proj_stoch_proc geom_proc n z \<and> y !! n = z !! n\<close> order_refl)
        qed
        hence "geom_proc (Suc n) y = geom_proc (Suc n) z" using geometric_process
          by (simp add: \<open>proj_stoch_proc geom_proc n y = proj_stoch_proc geom_proc n z \<and> y !! n = z !! n\<close>)
        thus "prices Mkt stk (Suc n) y = prices Mkt stk (Suc n) z" using stk_price by simp
      qed
      show "0 < q" and "q < 1" using assms by auto
    qed
    moreover have "\<forall>w. q * prices Mkt stk (Suc n) (pseudo_proj_True n w) + (1 - q) * prices Mkt stk (Suc n) (pseudo_proj_False n w) =
      (q * u + (1 - q) * d) * prices Mkt stk n w"
    proof
      fix w
      have "q * prices Mkt stk (Suc n) (pseudo_proj_True n w) + (1 - q) * prices Mkt stk (Suc n) (pseudo_proj_False n w) =
        q * geom_proc (Suc n) (pseudo_proj_True n w) + (1-q) * geom_proc (Suc n) (pseudo_proj_False n w)"
        by (simp add:stk_price)
      also have "... = q * u * geom_proc n (pseudo_proj_True n w) + (1-q) * geom_proc (Suc n) (pseudo_proj_False n w)"
        using geometric_process unfolding pseudo_proj_True_def by simp
      also have "... = q * u * geom_proc n w + (1-q) * geom_proc (Suc n) (pseudo_proj_False n w)"
        by (metis geom_rand_walk_pseudo_proj_True o_apply)
      also have "... = q * u * geom_proc n w + (1-q) * d * geom_proc n (pseudo_proj_False n w)"
        using geometric_process unfolding pseudo_proj_False_def by simp
      also have "... = q * u * geom_proc n w + (1-q) * d * geom_proc n w"
        by (metis geom_rand_walk_pseudo_proj_False o_apply)
      also have "... = (q * u + (1 - q) * d) * geom_proc n w" by (simp add: distrib_right)
      finally show "q * prices Mkt stk (Suc n) (pseudo_proj_True n w) + (1 - q) * prices Mkt stk (Suc n) (pseudo_proj_False n w) =
        (q * u + (1 - q) * d) * prices Mkt stk n w" using stk_price by simp
    qed
    ultimately show "AEeq N (real_cond_exp N (fct_gen_subalgebra N (stream_space borel)
                                  (proj_stoch_proc geom_proc n))
                                  ((prices Mkt stk) (Suc n)))
                    (\<lambda>w. (q * u + (1 - q) * d) * prices Mkt stk n w)" by simp
  qed
  ultimately show ?thesis by auto
qed



lemma (in CRR_market) risky_asset_martingale_only_if:
  assumes "N = bernoulli_stream q"
  and "0 < q"
  and "q < 1"
  and  "martingale N G (discounted_value r (prices Mkt stk))"
shows "q = (1 + r - d) / (u - d)"
proof -
  have "AE w in N. real_cond_exp N (G 0)
       (discounted_value r (prices Mkt stk) (Suc 0)) w =  discounted_value r (prices Mkt stk) 0 w" using assms
    unfolding martingale_def by simp
  hence "AE w in N. real_cond_exp N (G 0)
       (discounted_value r (prices Mkt stk) (Suc 0)) w =  prices Mkt stk 0 w" by (simp add: discounted_init)
  moreover have "AE w in N. real_cond_exp N (G 0) (discounted_value r (prices Mkt stk) (Suc 0)) w =
    discounted_value r (\<lambda>m w. (q * u + (1 - q) * d) * prices Mkt stk 0 w) (Suc 0) w"
    using assms real_cond_exp_discount_stock by simp
  ultimately have "AE w in N. discounted_value r (\<lambda>m w. (q * u + (1 - q) * d) * prices Mkt stk 0 w) (Suc 0) w =
    prices Mkt stk 0 w" by auto
  hence "AE w in N. discounted_value r (\<lambda>m w. (q * u + (1 - q) * d) * init) (Suc 0) w =
    (\<lambda>w. init) w" using stk_price geometric_process by simp
  hence "AE w in N. discount_factor r (Suc 0) w * (q * u + (1 - q) * d) * init =
    (\<lambda>w. init) w" unfolding discounted_value_def by simp
  hence "AE w in N. (1+r) * discount_factor r (Suc 0) w * (q * u + (1 - q) * d) * init =
    (1+r) * (\<lambda>w. init) w" by auto
  hence prev: "AE w in N. discount_factor r 0 w * (q * u + (1 - q) * d) * init =
    (1+r) * (\<lambda>w. init) w" using discount_factor_times_rfr[of r 0] acceptable_rate
  proof -
    have "\<forall>s. (1 + r) * discount_factor r (Suc 0) (s::bool stream) = discount_factor r 0 s"
    by (metis (no_types) \<open>\<And>w. - 1 < r \<Longrightarrow> (1 + r) * discount_factor r (Suc 0) w = discount_factor r 0 w\<close> acceptable_rate)
    then show ?thesis
    using \<open>AEeq N (\<lambda>w. (1 + r) * discount_factor r (Suc 0) w * (q * u + (1 - q) * d) * init) (\<lambda>w. (1 + r) * init)\<close> by presburger
  qed
  hence "\<forall>w. (\<lambda>w. discount_factor r 0 w * (q * u + (1 - q) * d) * init) w =
    (\<lambda>w. (1+r) * init) w"
  proof -
    have "(\<lambda>w. discount_factor r 0 w *  (q * u + (1 - q) * d) * init)
      \<in> borel_measurable (infinite_coin_toss_space.nat_filtration N 0)"
    proof (rule borel_measurable_times)+
      show "(\<lambda>x. init) \<in> borel_measurable (infinite_coin_toss_space.nat_filtration N 0)" by simp
      show "(\<lambda>x. q * u + (1 - q) * d) \<in> borel_measurable (infinite_coin_toss_space.nat_filtration N 0)" by simp
      show "discount_factor r 0 \<in> borel_measurable (infinite_coin_toss_space.nat_filtration N 0)"
        using discount_factor_nonrandom[of r 0 "infinite_coin_toss_space.nat_filtration N 0"] by simp
    qed
    moreover have "(\<lambda>w. (1 + r) * init) \<in> borel_measurable (infinite_coin_toss_space.nat_filtration N 0)" by simp
    moreover have "infinite_coin_toss_space q N" using assms by (simp add: infinite_coin_toss_space_def)
    ultimately show ?thesis
      using  prev infinite_coin_toss_space.nat_filtration_AE_eq[of q N
        "(\<lambda>w. discount_factor r 0 w * (q * u + (1 - q) * d) * init)" "(\<lambda>w. (1 + r) * init)" 0] assms
      by (simp add: discount_factor_init)
  qed
  hence "(q * u + (1 - q) * d) * init = (1+r) * init" by (simp add: discount_factor_init)
  hence "q * u + (1 - q) * d = 1+r" using S0_positive by simp
  hence "q * u + d - q * d = 1+r" by (simp add: left_diff_distrib)
  hence "q * (u - d) = 1 + r - d"
    by (metis (no_types, hide_lams) add.commute add.left_commute add_diff_cancel_left' add_uminus_conv_diff left_diff_distrib mult.commute)
  thus "q = (1 + r - d) / (u - d)" using down_lt_up
    by (metis add.commute add.right_neutral diff_add_cancel nonzero_eq_divide_eq order_less_irrefl)
qed



locale CRR_market_viable = CRR_market +
  assumes CRR_viable: "viable_market Mkt"


lemma (in CRR_market_viable) real_cond_exp_discount_stock_q_const:
  assumes "N = bernoulli_stream q"
and "q = (1+r-d) / (u-d)"
shows "AE w in N. real_cond_exp N (G n)
   (discounted_value r (prices Mkt stk) (Suc n)) w =
                  discounted_value r (prices Mkt stk) n w"
proof -
  have qlt: "0 < q" and qgt: "q < 1" using assms gt_param lt_param CRR_viable by auto
  have "AE w in N. real_cond_exp N (G n) (discounted_value r (prices Mkt stk) (Suc n)) w =
                  discounted_value r (\<lambda>m w. (q * u + (1 - q) * d) * prices Mkt stk n w) (Suc n) w"
    using assms real_cond_exp_discount_stock[of N q] qlt qgt by simp
  moreover have "\<forall>w. (q * u + (1 - q) * d) * prices Mkt stk n w =
    (1+r) * prices Mkt stk n w" using risk_neutral_param assms CRR_viable
      by (simp add: mult.commute)
  ultimately have "AE w in N. real_cond_exp N (G n) (discounted_value r (prices Mkt stk) (Suc n)) w =
                  discounted_value r (\<lambda>m w. (1+r) * prices Mkt stk n w) (Suc n) w" by simp
  moreover have "\<forall>w\<in> space N. discounted_value r (\<lambda>m w. (1+r) * prices Mkt stk n w) (Suc n) w =
                     discounted_value r (\<lambda>m w. prices Mkt stk n w) n w"
    using  acceptable_rate by (simp add:discounted_mult_times_rfr)
  moreover hence "\<forall>w\<in> space N. discounted_value r (\<lambda>m w. (1+r) * prices Mkt stk n w) (Suc n) w =
                     discounted_value r (prices Mkt stk) n w"
    using  acceptable_rate by (simp add:discounted_value_def)
  ultimately show "AE w in N. real_cond_exp N (G n) (discounted_value r (prices Mkt stk) (Suc n)) w =
                    discounted_value r (prices Mkt stk) n w" by simp
qed


lemma (in CRR_market_viable) risky_asset_martingale_if:
  assumes "N = bernoulli_stream q"
  and "q = (1 + r - d) / (u - d)"
shows "martingale N G (discounted_value r (prices Mkt stk))"
proof (rule disc_martingale_charact)
  have qlt: "0 < q" and qgt: "q < 1" using assms gt_param lt_param CRR_viable by auto
  show "\<forall>n. integrable N (discounted_value r (prices Mkt stk) n)"
  proof
    fix n
    show "integrable N (discounted_value r (prices Mkt stk) n)"
    proof (rule discounted_integrable)
      show "space N = space M" using assms by (simp add: bernoulli bernoulli_stream_space)
      show "integrable N (prices Mkt stk n)"
      proof (rule infinite_coin_toss_space.nat_filtration_borel_measurable_integrable)
        show "infinite_coin_toss_space q N" using assms qlt qgt
          by (simp add: infinite_coin_toss_space_def)
        show "prices Mkt stk n \<in> borel_measurable (infinite_coin_toss_space.nat_filtration N n)"
          using geom_rand_walk_borel_adapted stk_price  nat_filtration_from_eq_sets unfolding adapt_stoch_proc_def
          by (metis \<open>infinite_coin_toss_space q N\<close> borel_measurable_integrable geom_proc_integrable geom_rand_walk_pseudo_proj_True
              infinite_coin_toss_space.nat_filtration_borel_measurable_characterization infinite_coin_toss_space_def)
      qed
      show "-1 < r" using acceptable_rate by simp
    qed
  qed
  show "filtration N G" using qlt qgt by (simp add: bernoulli_gen_filtration assms)
  show "\<forall>n. sigma_finite_subalgebra N (G n)" using qlt qgt by (simp add: assms bernoulli_sigma_finite)
  show "\<forall>m. discounted_value r (prices Mkt stk) m \<in> borel_measurable (G m)"
  proof
    fix m
    have "discounted_value r (\<lambda>ma. prices Mkt stk m) m \<in> borel_measurable (G m)"
    proof (rule discounted_measurable)
      show "prices Mkt stk m \<in> borel_measurable (G m)" using stock_price_borel_measurable
        unfolding adapt_stoch_proc_def by simp
    qed
    thus "discounted_value r (prices Mkt stk) m \<in> borel_measurable (G m)"
      by (metis (mono_tags, lifting) discounted_value_def measurable_cong)
  qed
  show "\<forall>n. AE w in N. real_cond_exp N (G n)
       (discounted_value r (prices Mkt stk) (Suc n)) w = discounted_value r (prices Mkt stk) n w"
  proof
    fix n
    show "AE w in N. real_cond_exp N (G n)
       (discounted_value r (prices Mkt stk) (Suc n)) w = discounted_value r (prices Mkt stk) n w"
      using assms real_cond_exp_discount_stock_q_const by simp
  qed
qed


lemma (in CRR_market_viable) risk_neutral_iff':
  assumes "N = bernoulli_stream q"
and "0 \<le> q"
and "q \<le> 1"
and "filt_equiv nat_filtration M N"
shows "rfr_disc_equity_market.risk_neutral_prob G Mkt r N \<longleftrightarrow> q= (1 + r - d) / (u - d)"
proof
  have "0 < q" and "q < 1" using assms filt_equiv_sgt filt_equiv_slt psgt pslt by auto note qprops = this
  have dem: "rfr_disc_equity_market M G Mkt r risk_free_asset"  by unfold_locales
  {
    assume "rfr_disc_equity_market.risk_neutral_prob G Mkt r N"
    hence "(prob_space N) \<and> (\<forall> asset \<in> stocks Mkt. martingale N G (discounted_value r (prices Mkt asset)))"
      using rfr_disc_equity_market.risk_neutral_prob_def[of M G Mkt] dem  by simp
    hence "martingale N G (discounted_value r (prices Mkt stk))" using stocks by simp
    thus "q = (1 + r - d) / (u - d)" using assms risky_asset_martingale_only_if[of N q] qprops by simp
  }
  {
    assume "q = (1 + r - d) / (u - d)"
    hence "martingale N G (discounted_value r (prices Mkt stk))" using risky_asset_martingale_if[of N q] assms by simp
    moreover have "martingale N G (discounted_value r (prices Mkt risk_free_asset))" using risk_free_asset_martingale
      assms qprops by simp
    ultimately show "rfr_disc_equity_market.risk_neutral_prob G Mkt r N" using stocks
      using assms(1) bernoulli_stream_def dem prob_space.prob_space_stream_space prob_space_measure_pmf
        rfr_disc_equity_market.risk_neutral_prob_def by fastforce
  }
qed

lemma (in CRR_market_viable) risk_neutral_iff:
  assumes "N = bernoulli_stream q"
and "0 < q"
and "q < 1"
shows "rfr_disc_equity_market.risk_neutral_prob G Mkt r N \<longleftrightarrow> q= (1 + r - d) / (u - d)"
  using bernoulli_stream_equiv assms risk_neutral_iff' psgt pslt by auto

subsection \<open>Existence of a replicating portfolio\<close>




fun (in CRR_market) rn_rev_price where
  "rn_rev_price N der matur 0 w = der w" |
  "rn_rev_price N der matur (Suc n) w = discount_factor r (Suc 0) w *
                                  expl_cond_expect N (proj_stoch_proc geom_proc (matur - Suc n)) (rn_rev_price N der matur n) w"






lemma (in CRR_market) stock_filtration_eq:
  assumes "N = bernoulli_stream q"
and "0 < q"
and "q < 1"
shows "G n = stoch_proc_filt N geom_proc borel n"
proof -
  have "G n= stoch_proc_filt M geom_proc borel n" using stock_filtration by simp
  also have "... = stoch_proc_filt N geom_proc borel n"
  proof (rule stoch_proc_filt_filt_equiv)
    show "filt_equiv nat_filtration M N" using assms bernoulli_stream_equiv psgt pslt by simp
  qed
  finally show ?thesis .
qed



lemma (in CRR_market) real_exp_eq:
  assumes "der\<in> borel_measurable (G matur)"
and "N = bernoulli_stream q"
and "0 < q"
and "q < 1"
shows "real_cond_exp N (stoch_proc_filt N geom_proc borel n) der w =
      expl_cond_expect N (proj_stoch_proc geom_proc n) der w"
proof -
  have "der \<in> borel_measurable (nat_filtration matur)" using assms
      using geom_rand_walk_borel_adapted measurable_from_subalg stoch_proc_subalg_nat_filt stock_filtration by blast
  have "integrable N der"
  proof (rule infinite_coin_toss_space.nat_filtration_borel_measurable_integrable)
    show "infinite_coin_toss_space q N" using assms
      by (simp add: infinite_coin_toss_space_def)
    show "der \<in> borel_measurable (infinite_coin_toss_space.nat_filtration N matur)"
      by (metis \<open>der \<in> borel_measurable (nat_filtration matur)\<close> \<open>infinite_coin_toss_space q N\<close>
          assms(2) assms(3) assms(4) infinite_coin_toss_space.nat_filtration_space measurable_from_subalg
          nat_filtration_from_eq_sets nat_filtration_space subalgebra_def subset_eq)
  qed
  show "real_cond_exp N (stoch_proc_filt N geom_proc borel n) der w =
    expl_cond_expect N (proj_stoch_proc geom_proc n) der w"
  proof (rule bernoulli_cond_exp)
    show "N = bernoulli_stream q" "0 < q" "q < 1" using assms by auto
    show "integrable N der" using \<open>integrable N der\<close> .
  qed
qed

lemma (in CRR_market) rn_rev_price_rev_borel_adapt:
assumes "cash_flow \<in> borel_measurable (G matur)"
and "N = bernoulli_stream q"
and "0 < q"
and "q < 1"
shows "(n \<le> matur) \<Longrightarrow> (rn_rev_price N cash_flow matur n) \<in> borel_measurable (G (matur - n))"
proof (induct n)
case 0 thus ?case using assms by simp
next
  case (Suc n)
  have "rn_rev_price N cash_flow matur (Suc n) =
      (\<lambda>w. discount_factor r (Suc 0) w *
        (expl_cond_expect N (proj_stoch_proc geom_proc (matur - Suc n)) (rn_rev_price N cash_flow matur n)) w)"
    using rn_rev_price.simps(2) by blast
  also have "... \<in> borel_measurable (G (matur - Suc n))"
  proof (rule borel_measurable_times)
    show "discount_factor r (Suc 0) \<in> borel_measurable (G (matur - Suc n))" by (simp add:discount_factor_borel_measurable)
    show "expl_cond_expect N (proj_stoch_proc geom_proc (matur - Suc n)) (rn_rev_price N cash_flow matur n)
      \<in> borel_measurable (G (matur - Suc n))" using assms by (simp add: bernoulli_expl_cond_expect_adapt)
  qed
  finally show "rn_rev_price N cash_flow matur (Suc n) \<in> borel_measurable (G (matur - Suc n))" .
qed

lemma (in infinite_coin_toss_space) bernoulli_discounted_integrable:
  assumes "N = bernoulli_stream q"
and "0 < q"
and "q < 1"
  and "der \<in> borel_measurable (nat_filtration n)"
and "-1 < r"
  shows "integrable N (discounted_value r (\<lambda>m. der) m)"
proof -
  have "prob_space N" using assms
    by (simp add: bernoulli bernoulli_stream_def prob_space.prob_space_stream_space prob_space_measure_pmf)
  have "integrable N der"
  proof (rule infinite_coin_toss_space.nat_filtration_borel_measurable_integrable)
    show "infinite_coin_toss_space q N" using assms
      by (simp add: infinite_coin_toss_space_def)
    show "der \<in> borel_measurable (infinite_coin_toss_space.nat_filtration N n)"
      using assms filt_equiv_filtration
      by (simp add: assms(1) measurable_def nat_filtration_from_eq_sets nat_filtration_space)
  qed
  thus ?thesis using discounted_integrable assms
    by (metis \<open>prob_space N\<close> prob_space.discounted_integrable)
qed



lemma (in CRR_market) rn_rev_expl_cond_expect:
  assumes "der\<in> borel_measurable (G matur)"
and "N = bernoulli_stream q"
and "0 < q"
and "q < 1"
shows "n \<le> matur \<Longrightarrow> rn_rev_price N der matur n w =
  expl_cond_expect N (proj_stoch_proc geom_proc (matur - n)) (discounted_value r (\<lambda>m. der) n) w"
proof (induct n arbitrary: w)
  case 0
  have "der \<in> borel_measurable (nat_filtration matur)" using assms
      using geom_rand_walk_borel_adapted measurable_from_subalg stoch_proc_subalg_nat_filt stock_filtration by blast
  have "integrable N der"
  proof (rule infinite_coin_toss_space.nat_filtration_borel_measurable_integrable)
    show "infinite_coin_toss_space q N" using assms
      by (simp add: infinite_coin_toss_space_def)
    show "der \<in> borel_measurable (infinite_coin_toss_space.nat_filtration N matur)"
      by (metis \<open>der \<in> borel_measurable (nat_filtration matur)\<close> \<open>infinite_coin_toss_space q N\<close>
          assms(2) assms(3) assms(4) infinite_coin_toss_space.nat_filtration_space measurable_from_subalg
          nat_filtration_from_eq_sets nat_filtration_space subalgebra_def subset_eq)
  qed
  have "rn_rev_price N der matur 0 w = der w" by simp
  also have "... = expl_cond_expect N (proj_stoch_proc geom_proc matur) (discounted_value r (\<lambda>m. der) 0) w"
  proof (rule nat_filtration_AE_eq)
    show "der \<in> borel_measurable (nat_filtration matur)" using \<open>der \<in> borel_measurable (nat_filtration matur)\<close> .
    have "(discounted_value r (\<lambda>m. der) 0) = der" unfolding discounted_value_def discount_factor_def by simp
    moreover have "AEeq N (real_cond_exp N (G matur) der) der"
    proof (rule sigma_finite_subalgebra.real_cond_exp_F_meas)
      show "der \<in> borel_measurable (G matur)" using assms by simp
      show "integrable N der" using \<open>integrable N der\<close> .
      show "sigma_finite_subalgebra N (G matur)" using bernoulli_sigma_finite
        using assms by simp
    qed
    moreover have "\<forall>w. real_cond_exp N (stoch_proc_filt N geom_proc borel matur) der w =
      expl_cond_expect N (proj_stoch_proc geom_proc matur) der w" using assms real_exp_eq by simp
    ultimately have eqn: "AEeq N der (expl_cond_expect N (proj_stoch_proc geom_proc matur) (discounted_value r (\<lambda>m. der) 0))"
      using stock_filtration_eq assms by auto
    have "stoch_proc_filt M geom_proc borel matur = stoch_proc_filt N geom_proc borel matur"
      using  bernoulli_stream_equiv[of N q] assms psgt pslt by (simp add: stoch_proc_filt_filt_equiv)
    also have "stoch_proc_filt N geom_proc borel matur =
      fct_gen_subalgebra N (stream_space borel) (proj_stoch_proc geom_proc matur)"
      using assms geom_proc_stoch_proc_filt by simp
    finally have "stoch_proc_filt M geom_proc borel matur =
      fct_gen_subalgebra N (stream_space borel) (proj_stoch_proc geom_proc matur)" .
    moreover have "expl_cond_expect N (proj_stoch_proc geom_proc matur) (discounted_value r (\<lambda>m. der) 0)
      \<in> borel_measurable (fct_gen_subalgebra N (stream_space borel) (proj_stoch_proc geom_proc matur))"
    proof (rule expl_cond_exp_borel)
      show "proj_stoch_proc geom_proc matur \<in> space N \<rightarrow> space (stream_space borel)"
        using assms proj_stoch_proc_geom_rng by (simp add: measurable_def)
      show "disc_fct (proj_stoch_proc geom_proc matur)" using proj_stoch_proc_geom_disc_fct by simp
      show "\<forall>r\<in>range (proj_stoch_proc geom_proc matur) \<inter> space (stream_space borel).
        \<exists>A\<in>sets (stream_space borel). range (proj_stoch_proc geom_proc matur) \<inter> A = {r}"
        using proj_stoch_proc_geom_open_set by simp
    qed
    ultimately show ebm: "expl_cond_expect N (proj_stoch_proc geom_proc matur) (discounted_value r (\<lambda>m. der) 0)
      \<in> borel_measurable (nat_filtration matur)"
      by (metis geom_rand_walk_borel_adapted measurable_from_subalg stoch_proc_subalg_nat_filt)
    show "AEeq M der (expl_cond_expect N (proj_stoch_proc geom_proc matur) (discounted_value r (\<lambda>m. der) 0))"
    proof (rule filt_equiv_borel_AE_eq_iff[THEN iffD2])
      show "filt_equiv nat_filtration M N" using assms bernoulli_stream_equiv psgt pslt by simp
      show "der \<in> borel_measurable (nat_filtration matur)" using \<open>der \<in> borel_measurable (nat_filtration matur)\<close> .
      show "AEeq N der (expl_cond_expect N (proj_stoch_proc geom_proc matur) (discounted_value r (\<lambda>m. der) 0))"
        using eqn .
      show "expl_cond_expect N (proj_stoch_proc geom_proc matur) (discounted_value r (\<lambda>m. der) 0)
        \<in> borel_measurable (nat_filtration matur)" using ebm .
      show "prob_space N" using assms by (simp add: bernoulli_stream_def
            prob_space.prob_space_stream_space prob_space_measure_pmf)
      show "prob_space M" by (simp add: bernoulli bernoulli_stream_def
            prob_space.prob_space_stream_space prob_space_measure_pmf)
    qed
    show "0 < p" "p < 1" using psgt pslt by auto
  qed
  also have "... = expl_cond_expect N (proj_stoch_proc geom_proc (matur - 0)) (discounted_value r (\<lambda>m. der) 0) w"
    by simp
  finally show "rn_rev_price N der matur 0 w =
    expl_cond_expect N (proj_stoch_proc geom_proc (matur - 0)) (discounted_value r (\<lambda>m. der) 0) w" .
next
  case (Suc n)
  have "rn_rev_price N der matur (Suc n) w = discount_factor r (Suc 0) w *
          expl_cond_expect N (proj_stoch_proc geom_proc (matur - Suc n)) (rn_rev_price N der matur n) w" by simp
  also have "... = discount_factor r (Suc 0) w *
    real_cond_exp N (stoch_proc_filt N geom_proc borel (matur - Suc n)) (rn_rev_price N der matur n) w"
  proof -
    have "expl_cond_expect N (proj_stoch_proc geom_proc (matur - Suc n)) (rn_rev_price N der matur n) w =
     real_cond_exp N (stoch_proc_filt N geom_proc borel (matur - Suc n)) (rn_rev_price N der matur n) w"
    proof (rule real_exp_eq[symmetric])
      show "rn_rev_price N der matur n \<in> borel_measurable (G (matur - n))"
        using assms rn_rev_price_rev_borel_adapt Suc by simp
      show "N = bernoulli_stream q" "0 < q" "q < 1" using assms by auto
    qed
    thus ?thesis by simp
  qed
  also have "... = discount_factor r (Suc 0) w *
    real_cond_exp N (stoch_proc_filt N geom_proc borel (matur - Suc n))
    (expl_cond_expect N (proj_stoch_proc geom_proc (matur - n)) (discounted_value r (\<lambda>m. der) n)) w"
  proof -
    have "real_cond_exp N (stoch_proc_filt N geom_proc borel (matur - Suc n)) (rn_rev_price N der matur n) w =
      real_cond_exp N (stoch_proc_filt N geom_proc borel (matur - Suc n))
    (expl_cond_expect N (proj_stoch_proc geom_proc (matur - n)) (discounted_value r (\<lambda>m. der) n)) w"
    proof (rule infinite_coin_toss_space.nat_filtration_AE_eq)
      show "AEeq N (real_cond_exp N (stoch_proc_filt N geom_proc borel (matur - Suc n)) (rn_rev_price N der matur n))
        (real_cond_exp N (stoch_proc_filt N geom_proc borel (matur - Suc n))
        (expl_cond_expect N (proj_stoch_proc geom_proc (matur - n)) (discounted_value r (\<lambda>m. der) n)))"
      proof (rule sigma_finite_subalgebra.real_cond_exp_cong)
        show "sigma_finite_subalgebra N (stoch_proc_filt N geom_proc borel (matur - Suc n))"
          using assms(2) assms(3) assms(4) bernoulli_sigma_finite stock_filtration_eq by auto
        show "rn_rev_price N der matur n \<in> borel_measurable N"
        proof -
          have "rn_rev_price N der matur n \<in> borel_measurable (G (matur - n))"
            by (metis (full_types) Suc.prems Suc_leD assms(1) assms(2) assms(3) assms(4) rn_rev_price_rev_borel_adapt)
          then show ?thesis
            by (metis (no_types) assms(2) bernoulli bernoulli_stream_def filtration_measurable measurable_cong_sets sets_measure_pmf sets_stream_space_cong)
        qed
        show "expl_cond_expect N (proj_stoch_proc geom_proc (matur - n)) (discounted_value r (\<lambda>m. der) n) \<in> borel_measurable N"
          using Suc.hyps Suc.prems Suc_leD \<open>rn_rev_price N der matur n \<in> borel_measurable N\<close> by presburger
        show "AEeq N (rn_rev_price N der matur n)
          (expl_cond_expect N (proj_stoch_proc geom_proc (matur - n)) (discounted_value r (\<lambda>m. der) n))" using Suc by auto
      qed
      show "real_cond_exp N (stoch_proc_filt N geom_proc borel (matur - Suc n)) (rn_rev_price N der matur n)
        \<in> borel_measurable (infinite_coin_toss_space.nat_filtration N (matur - Suc n))"
        by (metis assms(2) assms(3) assms(4) borel_measurable_cond_exp infinite_coin_toss_space.intro
            infinite_coin_toss_space.stoch_proc_subalg_nat_filt linear measurable_from_subalg not_less
            prob_grw.geom_rand_walk_borel_adapted prob_grw_axioms prob_grw_def)
      show "real_cond_exp N (stoch_proc_filt N geom_proc borel (matur - Suc n))
         (expl_cond_expect N (proj_stoch_proc geom_proc (matur - n)) (discounted_value r (\<lambda>m. der) n))
        \<in> borel_measurable (infinite_coin_toss_space.nat_filtration N (matur - Suc n))"
        by (metis assms(2) assms(3) assms(4) borel_measurable_cond_exp infinite_coin_toss_space.intro
              infinite_coin_toss_space.stoch_proc_subalg_nat_filt linear measurable_from_subalg not_less
              prob_grw.geom_rand_walk_borel_adapted prob_grw_axioms prob_grw_def)
      show "0 < q" "q < 1" using assms by auto
      show "infinite_coin_toss_space q N" using assms
        by (simp add: infinite_coin_toss_space_def)
    qed
    thus ?thesis by simp
  qed
  also have "... = discount_factor r (Suc 0) w *
  real_cond_exp N (stoch_proc_filt N geom_proc borel (matur - Suc n))
   (real_cond_exp N (stoch_proc_filt N geom_proc borel (matur - n)) (discounted_value r (\<lambda>m. der) n)) w"
  proof -
    have "real_cond_exp N (stoch_proc_filt N geom_proc borel (matur - Suc n))
      (expl_cond_expect N (proj_stoch_proc geom_proc (matur - n)) (discounted_value r (\<lambda>m. der) n)) w =
      real_cond_exp N (stoch_proc_filt N geom_proc borel (matur - Suc n))
      (real_cond_exp N (stoch_proc_filt N geom_proc borel (matur - n)) (discounted_value r (\<lambda>m. der) n)) w"
    proof (rule infinite_coin_toss_space.nat_filtration_AE_eq)
      show "AEeq N (real_cond_exp N (stoch_proc_filt N geom_proc borel (matur - Suc n))
             (expl_cond_expect N (proj_stoch_proc geom_proc (matur - n)) (discounted_value r (\<lambda>m. der) n)))
         (real_cond_exp N (stoch_proc_filt N geom_proc borel (matur - Suc n))
           (real_cond_exp N (stoch_proc_filt N geom_proc borel (matur - n)) (discounted_value r (\<lambda>m. der) n)))"
      proof (rule sigma_finite_subalgebra.real_cond_exp_cong)
        show "sigma_finite_subalgebra N (stoch_proc_filt N geom_proc borel (matur - Suc n))"
          using assms(2) assms(3) assms(4) bernoulli_sigma_finite stock_filtration_eq by auto
        show "real_cond_exp N (stoch_proc_filt N geom_proc borel (matur - n)) (discounted_value r (\<lambda>m. der) n) \<in> borel_measurable N"
          by simp
        show "expl_cond_expect N (proj_stoch_proc geom_proc (matur - n)) (discounted_value r (\<lambda>m. der) n) \<in> borel_measurable N"
          by (metis assms(2) assms(3) assms(4) bernoulli bernoulli_expl_cond_expect_adapt bernoulli_stream_def filtration_measurable
              measurable_cong_sets sets_measure_pmf sets_stream_space_cong)
        show "AEeq N (expl_cond_expect N (proj_stoch_proc geom_proc (matur - n)) (discounted_value r (\<lambda>m. der) n))
          (real_cond_exp N (stoch_proc_filt N geom_proc borel (matur - n)) (discounted_value r (\<lambda>m. der) n))"
        proof -
          have "discounted_value r (\<lambda>m. der) n \<in> borel_measurable (G matur)" using assms discounted_measurable[of der]
            by simp
          hence "\<forall>w. (expl_cond_expect N (proj_stoch_proc geom_proc (matur - n)) (discounted_value r (\<lambda>m. der) n)) w =
            (real_cond_exp N (stoch_proc_filt N geom_proc borel (matur - n)) (discounted_value r (\<lambda>m. der) n)) w"
            using real_exp_eq[of _ matur N q "matur-n"] assms by simp
          thus ?thesis by simp
        qed
      qed
      show "real_cond_exp N (stoch_proc_filt N geom_proc borel (matur - Suc n))
         (real_cond_exp N (stoch_proc_filt N geom_proc borel (matur - n)) (discounted_value r (\<lambda>m. der) n))
        \<in> borel_measurable (infinite_coin_toss_space.nat_filtration N (matur - Suc n))"
        by (metis assms(2) assms(3) assms(4) borel_measurable_cond_exp infinite_coin_toss_space.intro
              infinite_coin_toss_space.stoch_proc_subalg_nat_filt linear measurable_from_subalg not_less
              prob_grw.geom_rand_walk_borel_adapted prob_grw_axioms prob_grw_def)
      show "real_cond_exp N (stoch_proc_filt N geom_proc borel (matur - Suc n))
         (expl_cond_expect N (proj_stoch_proc geom_proc (matur - n)) (discounted_value r (\<lambda>m. der) n))
        \<in> borel_measurable (infinite_coin_toss_space.nat_filtration N (matur - Suc n))"
        by (metis assms(2) assms(3) assms(4) borel_measurable_cond_exp infinite_coin_toss_space.intro
              infinite_coin_toss_space.stoch_proc_subalg_nat_filt linear measurable_from_subalg not_less
              prob_grw.geom_rand_walk_borel_adapted prob_grw_axioms prob_grw_def)
      show "0 < q" "q < 1" using assms by auto
      show "infinite_coin_toss_space q N" using assms
        by (simp add: infinite_coin_toss_space_def)
    qed
    thus ?thesis by simp
  qed
  also have "... = real_cond_exp N (stoch_proc_filt N geom_proc borel (matur - Suc n))
    (discounted_value r (\<lambda>m. der) (Suc n)) w"
  proof (rule infinite_coin_toss_space.nat_filtration_AE_eq)
    show "real_cond_exp N (stoch_proc_filt N geom_proc borel (matur - Suc n)) (discounted_value r (\<lambda>m. der) (Suc n))
      \<in> borel_measurable (infinite_coin_toss_space.nat_filtration N (matur - Suc n))"
        by (metis assms(2) assms(3) assms(4) borel_measurable_cond_exp infinite_coin_toss_space.intro
              infinite_coin_toss_space.stoch_proc_subalg_nat_filt linear measurable_from_subalg not_less
              prob_grw.geom_rand_walk_borel_adapted prob_grw_axioms prob_grw_def)
      show "(\<lambda>a. discount_factor r (Suc 0) a *
          real_cond_exp N (stoch_proc_filt N geom_proc borel (matur - Suc n))
           (real_cond_exp N (stoch_proc_filt N geom_proc borel (matur - n)) (discounted_value r (\<lambda>m. der) n)) a)
        \<in> borel_measurable (infinite_coin_toss_space.nat_filtration N (matur - Suc n))"
      proof -
        have "real_cond_exp N (stoch_proc_filt N geom_proc borel (matur - Suc n))
           (real_cond_exp N (stoch_proc_filt N geom_proc borel (matur - n)) (discounted_value r (\<lambda>m. der) n))
        \<in> borel_measurable (infinite_coin_toss_space.nat_filtration N (matur - Suc n))"
        by (metis assms(2) assms(3) assms(4) borel_measurable_cond_exp infinite_coin_toss_space.intro
              infinite_coin_toss_space.stoch_proc_subalg_nat_filt linear measurable_from_subalg not_less
              prob_grw.geom_rand_walk_borel_adapted prob_grw_axioms prob_grw_def)
      thus ?thesis using discounted_measurable[of "real_cond_exp N (stoch_proc_filt N geom_proc borel (matur - Suc n))
        (real_cond_exp N (stoch_proc_filt N geom_proc borel (matur - n)) (discounted_value r (\<lambda>m. der) n))"]
        unfolding discounted_value_def by simp
    qed
    show "0 < q" "q < 1" using assms by auto
    show "infinite_coin_toss_space q N" using assms
      by (simp add: infinite_coin_toss_space_def)
    show "AEeq N (\<lambda>w. discount_factor r (Suc 0) w *
                 real_cond_exp N (stoch_proc_filt N geom_proc borel (matur - Suc n))
                  (real_cond_exp N (stoch_proc_filt N geom_proc borel (matur - n)) (discounted_value r (\<lambda>m. der) n)) w)
     (real_cond_exp N (stoch_proc_filt N geom_proc borel (matur - Suc n)) (discounted_value r (\<lambda>m. der) (Suc n)))"
    proof-
      have "AEeq N
        (\<lambda>w. discount_factor r (Suc 0) w *
                 real_cond_exp N (stoch_proc_filt N geom_proc borel (matur - Suc n))
                  (real_cond_exp N (stoch_proc_filt N geom_proc borel (matur - n)) (discounted_value r (\<lambda>m. der) n)) w)
        (\<lambda>w. discount_factor r (Suc 0) w *
                 real_cond_exp N (stoch_proc_filt N geom_proc borel (matur - Suc n)) (discounted_value r (\<lambda>m. der) n) w)"
      proof -
        have "AEeq N (real_cond_exp N (stoch_proc_filt N geom_proc borel (matur - Suc n))
                  (real_cond_exp N (stoch_proc_filt N geom_proc borel (matur - n)) (discounted_value r (\<lambda>m. der) n)))
                (real_cond_exp N (stoch_proc_filt N geom_proc borel (matur - Suc n)) (discounted_value r (\<lambda>m. der) n))"
        proof (rule sigma_finite_subalgebra.real_cond_exp_nested_subalg)
          show "sigma_finite_subalgebra N (stoch_proc_filt N geom_proc borel (matur - Suc n))"
            using assms(2) assms(3) assms(4) bernoulli_sigma_finite stock_filtration_eq by auto
          show "subalgebra N (stoch_proc_filt N geom_proc borel (matur - n))"
            using assms(2) assms(3) assms(4) bernoulli_sigma_finite sigma_finite_subalgebra.subalg
              stock_filtration_eq by fastforce
          show "subalgebra (stoch_proc_filt N geom_proc borel (matur - n)) (stoch_proc_filt N geom_proc borel (matur - Suc n))"
          proof -
            have "init_triv_filt M (stoch_proc_filt M geom_proc borel)" using infinite_cts_filtration.stoch_proc_filt_triv_init
              using info_filtration stock_filtration by auto
            moreover have "matur - (Suc n) \<le> matur - n" by simp
            ultimately show ?thesis unfolding init_triv_filt_def filtration_def
              using assms(2) assms(3) assms(4) stock_filtration stock_filtration_eq by auto
          qed
          show "integrable N (discounted_value r (\<lambda>m. der) n) " using bernoulli_discounted_integrable[of N q der matur r n] acceptable_rate assms
            using geom_rand_walk_borel_adapted measurable_from_subalg stoch_proc_subalg_nat_filt stock_filtration by blast
        qed
        thus ?thesis  by auto
      qed
      moreover have "AEeq N
        (\<lambda>w. discount_factor r (Suc 0) w *
         real_cond_exp N (stoch_proc_filt N geom_proc borel (matur - Suc n)) (discounted_value r (\<lambda>m. der) n) w)
        (\<lambda>w. discount_factor r (Suc 0) w * (discounted_value r
         (\<lambda>m. real_cond_exp N (stoch_proc_filt N geom_proc borel (matur - Suc n)) der) n) w)"
      proof -
        have "AEeq N (real_cond_exp N (stoch_proc_filt N geom_proc borel (matur - Suc n)) (discounted_value r (\<lambda>m. der) n))
          (discounted_value r
         (\<lambda>m. real_cond_exp N (stoch_proc_filt N geom_proc borel (matur - Suc n)) der) n)"
        proof (rule prob_space.discounted_value_real_cond_exp)
          show "prob_space N" using assms
            by (simp add: bernoulli bernoulli_stream_def prob_space.prob_space_stream_space prob_space_measure_pmf)
          have "der \<in> borel_measurable (nat_filtration matur)" using assms
            using geom_rand_walk_borel_adapted measurable_from_subalg stoch_proc_subalg_nat_filt stock_filtration by blast
          show "integrable N der"
          proof (rule infinite_coin_toss_space.nat_filtration_borel_measurable_integrable)
            show "infinite_coin_toss_space q N" using assms
              by (simp add: infinite_coin_toss_space_def)
            show "der \<in> borel_measurable (infinite_coin_toss_space.nat_filtration N matur)"
              by (metis \<open>der \<in> borel_measurable (nat_filtration matur)\<close> \<open>infinite_coin_toss_space q N\<close>
                  assms(2) assms(3) assms(4) infinite_coin_toss_space.nat_filtration_space measurable_from_subalg
                  nat_filtration_from_eq_sets nat_filtration_space subalgebra_def subset_eq)
          qed
          show "-1 < r" using acceptable_rate .
          show "subalgebra N (stoch_proc_filt N geom_proc borel (matur - Suc n))"
            using assms(2) assms(3) assms(4) bernoulli_sigma_finite sigma_finite_subalgebra.subalg
              stock_filtration_eq by fastforce
        qed
        thus ?thesis  by auto
      qed
      moreover have "\<forall>w. (\<lambda>w. discount_factor r (Suc 0) w * (discounted_value r
         (\<lambda>m. real_cond_exp N (stoch_proc_filt N geom_proc borel (matur - Suc n)) der) n) w) w =
        (discounted_value r
         (\<lambda>m. real_cond_exp N (stoch_proc_filt N geom_proc borel (matur - Suc n)) der) (Suc n)) w"
        unfolding discounted_value_def discount_factor_def  by simp
      moreover have "AEeq N
        (real_cond_exp N (stoch_proc_filt N geom_proc borel (matur - Suc n))
        (discounted_value r (\<lambda>m. der) (Suc n)))
        (discounted_value r
        (\<lambda>m. real_cond_exp N (stoch_proc_filt N geom_proc borel (matur - Suc n)) der) (Suc n))"
      proof (rule prob_space.discounted_value_real_cond_exp)
        show "prob_space N" using assms
            by (simp add: bernoulli bernoulli_stream_def prob_space.prob_space_stream_space prob_space_measure_pmf)
        have "der \<in> borel_measurable (nat_filtration matur)" using assms
          using geom_rand_walk_borel_adapted measurable_from_subalg stoch_proc_subalg_nat_filt stock_filtration by blast
        show "integrable N der"
        proof (rule infinite_coin_toss_space.nat_filtration_borel_measurable_integrable)
          show "infinite_coin_toss_space q N" using assms
            by (simp add: infinite_coin_toss_space_def)
          show "der \<in> borel_measurable (infinite_coin_toss_space.nat_filtration N matur)"
            by (metis \<open>der \<in> borel_measurable (nat_filtration matur)\<close> \<open>infinite_coin_toss_space q N\<close>
                assms(2) assms(3) assms(4) infinite_coin_toss_space.nat_filtration_space measurable_from_subalg
                nat_filtration_from_eq_sets nat_filtration_space subalgebra_def subset_eq)
        qed
        show "-1 < r" using acceptable_rate .
        show "subalgebra N (stoch_proc_filt N geom_proc borel (matur - Suc n))"
          using assms(2) assms(3) assms(4) bernoulli_sigma_finite sigma_finite_subalgebra.subalg
            stock_filtration_eq by fastforce
      qed
      ultimately show ?thesis by auto
    qed
  qed
  also have "... = expl_cond_expect N (proj_stoch_proc geom_proc (matur - Suc n))
    (discounted_value r (\<lambda>m. der) (Suc n)) w"
  proof (rule real_exp_eq)
    show "discounted_value r (\<lambda>m. der) (Suc n) \<in> borel_measurable (G matur)" using assms discounted_measurable[of der]
      by simp
    show "N = bernoulli_stream q" "0 < q" "q < 1" using assms by auto
  qed
  finally show "rn_rev_price N der matur (Suc n) w =
    expl_cond_expect N (proj_stoch_proc geom_proc (matur - Suc n)) (discounted_value r (\<lambda>m. der) (Suc n)) w" .
qed

definition (in CRR_market) rn_price where
"rn_price N der matur n w = expl_cond_expect N (proj_stoch_proc geom_proc n) (discounted_value r (\<lambda>m. der) (matur - n)) w"


definition (in CRR_market) rn_price_ind where
"rn_price_ind N der matur n w = rn_rev_price N der matur (matur - n) w"

lemma (in CRR_market) rn_price_eq:
  assumes "N = bernoulli_stream q"
and "0 < q"
and "q < 1"
and "der \<in> borel_measurable (G matur)"
and "n \<le> matur"
shows "rn_price N der matur n w = rn_price_ind N der matur n w" using rn_rev_expl_cond_expect
  unfolding rn_price_def rn_price_ind_def
  by (simp add: assms)


lemma (in CRR_market) geom_proc_filt_info:
  fixes f::"bool stream \<Rightarrow> 'b::{t0_space}"
  assumes "f \<in> borel_measurable (G n)"
  shows "f w = f (pseudo_proj_True n w)"
proof -
  have "subalgebra (nat_filtration n) (G n)" using stoch_proc_subalg_nat_filt[of geom_proc n] geometric_process
    stock_filtration geom_rand_walk_borel_adapted by simp
  hence "f\<in> borel_measurable (nat_filtration n)" using assms by (simp add: measurable_from_subalg)
  thus ?thesis using nat_filtration_info[of f n] by (metis comp_apply)
qed

lemma (in CRR_market) geom_proc_filt_info':
  fixes f::"bool stream \<Rightarrow> 'b::{t0_space}"
  assumes "f \<in> borel_measurable (G n)"
  shows "f w = f (pseudo_proj_False n w)"
proof -
  have "subalgebra (nat_filtration n) (G n)" using stoch_proc_subalg_nat_filt[of geom_proc n] geometric_process
    stock_filtration geom_rand_walk_borel_adapted by simp
  hence "f\<in> borel_measurable (nat_filtration n)" using assms by (simp add: measurable_from_subalg)
  thus ?thesis using nat_filtration_info'[of f n] by (metis comp_apply)
qed




lemma (in CRR_market) rn_price_borel_adapt:
assumes "cash_flow \<in> borel_measurable (G matur)"
and "N = bernoulli_stream q"
and "0 < q"
and "q < 1"
and "n \<le> matur"
shows "(rn_price N cash_flow matur n) \<in> borel_measurable (G n)"
proof -
  show "(rn_price N cash_flow matur n) \<in> borel_measurable (G n)"
    using assms rn_rev_price_rev_borel_adapt[of cash_flow matur N q "matur - n"] rn_price_eq rn_price_ind_def
    by (smt add.right_neutral cancel_comm_monoid_add_class.diff_cancel diff_commute diff_le_self
        increasing_measurable_info measurable_cong nat_le_linear ordered_cancel_comm_monoid_diff_class.add_diff_inverse)
qed


definition (in CRR_market) delta_price where
  "delta_price N cash_flow T =
    (\<lambda> n w. if (Suc n \<le> T)
      then (rn_price N cash_flow T (Suc n) (pseudo_proj_True n w) - rn_price N cash_flow T (Suc n) (pseudo_proj_False n w))/
        (geom_proc (Suc n) (spick w n True) - geom_proc (Suc n) (spick w n False))
      else 0)"


lemma (in CRR_market) delta_price_eq:
  assumes "Suc n \<le> T"
  shows "delta_price N cash_flow T n w = (rn_price N cash_flow T (Suc n) (spick w n True) - rn_price N cash_flow T (Suc n) (spick w n False))/
    ((geom_proc n w) * (u - d))"
proof -
  have "(geom_proc (Suc n) (spick w n True) - geom_proc (Suc n) (spick w n False)) = geom_proc n w * (u - d)"
    by (simp add: geom_rand_walk_diff_induct)
  then show ?thesis unfolding delta_price_def using assms spick_eq_pseudo_proj_True spick_eq_pseudo_proj_False by simp
qed



lemma (in CRR_market) geom_proc_spick:
  shows "geom_proc (Suc n) (spick w n x)  = (if x then u else d) * geom_proc n w"
proof -
  have "geom_proc (Suc n) (spick w n x)  = geom_rand_walk u d init (Suc n) (spick w n x)" using geometric_process by simp
  also have "... = (case (spick w n x) !! n of True \<Rightarrow> u | False \<Rightarrow> d) * geom_rand_walk u d init n (spick w n x)"
    by simp
  also have "... = (case x of True \<Rightarrow> u | False \<Rightarrow> d) * geom_rand_walk u d init n (spick w n x)"
    unfolding spick_def by simp
  also have "... = (if x then u else d) * geom_rand_walk u d init n (spick w n x)" by simp
  also have "... = (if x then u else d) * geom_rand_walk u d init n w"
    by (metis comp_def geom_rand_walk_pseudo_proj_True geometric_process pseudo_proj_True_stake_image spickI)
  finally show ?thesis using geometric_process by simp
qed


lemma (in CRR_market) spick_red_geom:
  shows "(\<lambda>w. spick w n x) \<in> measurable (fct_gen_subalgebra M borel (geom_proc n)) (fct_gen_subalgebra M borel (geom_proc (Suc n)))"
  unfolding measurable_def
proof (intro CollectI conjI)
  show "(\<lambda>w. spick w n x)
    \<in> space (fct_gen_subalgebra M borel (geom_proc n)) \<rightarrow> space (fct_gen_subalgebra M borel (geom_proc (Suc n)))"
    by (simp add: bernoulli bernoulli_stream_space fct_gen_subalgebra_space)
  show "\<forall>y\<in>sets (fct_gen_subalgebra M borel (geom_proc (Suc n))).
       (\<lambda>w. spick w n x) -` y \<inter> space (fct_gen_subalgebra M borel (geom_proc n))
       \<in> sets (fct_gen_subalgebra M borel (geom_proc n))"
  proof
    fix A
    assume A: "A \<in> sets (fct_gen_subalgebra M borel (geom_proc (Suc n)))"
    show "(\<lambda>w. spick w n x) -` A \<inter> space (fct_gen_subalgebra M borel (geom_proc n)) \<in>
    sets (fct_gen_subalgebra M borel (geom_proc n))"
    proof -
      define sp where "sp = (\<lambda>w. spick w n x)"
      have "A \<in> {(geom_proc (Suc n)) -` B \<inter> space M |B. B \<in> sets borel}" using A
        by (simp add:fct_gen_subalgebra_sigma_sets)
      from this obtain C where "C\<in> sets borel" and "A = (geom_proc (Suc n)) -`C \<inter> space M" by auto
      hence "A = (geom_proc (Suc n)) -`C" using bernoulli bernoulli_stream_space by simp
      hence "sp -`A = sp -` (geom_proc (Suc n)) -`C" by simp
      also have "... = (geom_proc (Suc n) \<circ> sp) -` C" by auto
      also have "... = (\<lambda>w. (if x then u else d) * geom_proc n w) -` C" using geom_proc_spick
        sp_def by auto
      also have "... \<in> sets (fct_gen_subalgebra M borel (geom_proc n))"
      proof (cases x)
        case True
        hence "(\<lambda>w. (if x then u else d) * geom_proc n w) -` C = (\<lambda>w. u * geom_proc n w) -` C" by simp
        moreover have "(\<lambda>w. u * geom_proc n w) \<in> borel_measurable (fct_gen_subalgebra M borel (geom_proc n))"
        proof -
          have "geom_proc n \<in>borel_measurable (fct_gen_subalgebra M borel (geom_proc n))"
            using fct_gen_subalgebra_fct_measurable
            by (metis (no_types, lifting) geom_rand_walk_borel_measurable measurable_def mem_Collect_eq)
          thus ?thesis by simp
        qed
        ultimately show ?thesis using \<open>C\<in> sets borel\<close>
          by (metis bernoulli bernoulli_stream_preimage fct_gen_subalgebra_space measurable_sets)
      next
        case False
        hence "(\<lambda>w. (if x then u else d) * geom_proc n w) -` C = (\<lambda>w. d * geom_proc n w) -` C" by simp
        moreover have "(\<lambda>w. d * geom_proc n w) \<in> borel_measurable (fct_gen_subalgebra M borel (geom_proc n))"
        proof -
          have "geom_proc n \<in>borel_measurable (fct_gen_subalgebra M borel (geom_proc n))"
            using fct_gen_subalgebra_fct_measurable
            by (metis (no_types, lifting) geom_rand_walk_borel_measurable measurable_def mem_Collect_eq)
          thus ?thesis by simp
        qed
        ultimately show ?thesis using \<open>C\<in> sets borel\<close>
          by (metis bernoulli bernoulli_stream_preimage fct_gen_subalgebra_space measurable_sets)
      qed
      finally show ?thesis unfolding sp_def by (simp add: bernoulli bernoulli_stream_space fct_gen_subalgebra_space)
    qed
  qed
qed

lemma (in CRR_market) geom_spick_Suc:
  assumes "A \<in> {(geom_proc (Suc n)) -` B |B. B \<in> sets borel}"
  shows "(\<lambda>w. spick w n x) -`A \<in> {geom_proc n -`B | B. B\<in> sets borel}"
proof -
  have "sets (fct_gen_subalgebra M borel (geom_proc n)) = {geom_proc n -` B \<inter>space M |B. B \<in> sets borel}"
    by (simp add: fct_gen_subalgebra_sigma_sets)
  also have "... =  {geom_proc n -` B |B. B \<in> sets borel}" using bernoulli bernoulli_stream_space by simp
  finally have sf: "sets (fct_gen_subalgebra M borel (geom_proc n)) = {geom_proc n -` B |B. B \<in> sets borel}" .
  define sp where "sp = (\<lambda>w. spick w n x)"
  from assms(1) obtain C where "C\<in> sets borel" and "A = (geom_proc (Suc n)) -`C" by auto
  hence "A = (geom_proc (Suc n)) -`C" using bernoulli bernoulli_stream_space by simp
  hence "sp -`A = sp -` (geom_proc (Suc n)) -`C" by simp
  also have "... = (geom_proc (Suc n) \<circ> sp) -` C" by auto
  also have "... = (\<lambda>w. (if x then u else d) * geom_proc n w) -` C" using geom_proc_spick
    sp_def by auto
  also have "... \<in> {geom_proc n -`B | B. B\<in> sets borel}"
  proof (cases x)
    case True
    hence "(\<lambda>w. (if x then u else d) * geom_proc n w) -` C = (\<lambda>w. u * geom_proc n w) -` C" by simp
    moreover have "(\<lambda>w. u * geom_proc n w) \<in> borel_measurable (fct_gen_subalgebra M borel (geom_proc n))"
    proof -
      have "geom_proc n \<in>borel_measurable (fct_gen_subalgebra M borel (geom_proc n))"
        using fct_gen_subalgebra_fct_measurable
        by (metis (no_types, lifting) geom_rand_walk_borel_measurable measurable_def mem_Collect_eq)
      thus ?thesis by simp
    qed
    ultimately show ?thesis using \<open>C\<in> sets borel\<close> sf
      by (simp add: bernoulli bernoulli_stream_preimage fct_gen_subalgebra_space in_borel_measurable_borel)
  next
    case False
    hence "(\<lambda>w. (if x then u else d) * geom_proc n w) -` C = (\<lambda>w. d * geom_proc n w) -` C" by simp
    moreover have "(\<lambda>w. d * geom_proc n w) \<in> borel_measurable (fct_gen_subalgebra M borel (geom_proc n))"
    proof -
      have "geom_proc n \<in>borel_measurable (fct_gen_subalgebra M borel (geom_proc n))"
        using fct_gen_subalgebra_fct_measurable
        by (metis (no_types, lifting) geom_rand_walk_borel_measurable measurable_def mem_Collect_eq)
      thus ?thesis by simp
    qed
    ultimately show ?thesis using \<open>C\<in> sets borel\<close> sf
      by (simp add: bernoulli bernoulli_stream_preimage fct_gen_subalgebra_space in_borel_measurable_borel)
  qed
  finally show ?thesis unfolding sp_def .
qed


lemma (in CRR_market) geom_spick_lt:
  assumes "m< n"
  shows "geom_proc m (spick w n x) = geom_proc m w"
proof -
  have "geom_proc m (spick w n x) = geom_proc m (pseudo_proj_True m (spick w n x))"
    using  geom_rand_walk_pseudo_proj_True by (metis comp_apply)
  also have "... = geom_proc m (pseudo_proj_True m w)" using assms
    by (metis less_imp_le_nat pseudo_proj_True_def pseudo_proj_True_prefix spickI)
  also have "... = geom_proc m w" using  geom_rand_walk_pseudo_proj_True by (metis comp_apply)
  finally show ?thesis .
qed

lemma (in CRR_market) geom_spick_eq:
  shows "geom_proc m (spick w m x) = geom_proc m w"
proof (cases x)
  case True
  have "geom_proc m (spick w m x) = geom_proc m (pseudo_proj_True m (spick w m x))"
    using  geom_rand_walk_pseudo_proj_True by (metis comp_apply)
  also have "... = geom_proc m (pseudo_proj_True m w)" using True
    by (metis pseudo_proj_True_def spickI)
  also have "... = geom_proc m w" using  geom_rand_walk_pseudo_proj_True by (metis comp_apply)
  finally show ?thesis .
next
  case False
  have "geom_proc m (spick w m x) = geom_proc m (pseudo_proj_False m (spick w m x))"
    using  geom_rand_walk_pseudo_proj_False by (metis comp_apply)
  also have "... = geom_proc m (pseudo_proj_False m w)" using False
    by (metis pseudo_proj_False_def spickI)
  also have "... = geom_proc m w" using  geom_rand_walk_pseudo_proj_False by (metis comp_apply)
  finally show ?thesis .
qed


lemma (in CRR_market) spick_red_geom_filt:
  shows "(\<lambda>w. spick w n x) \<in> measurable (G n) (G (Suc n))" unfolding measurable_def
proof (intro CollectI conjI)
  show "(\<lambda>w. spick w n x) \<in> space (G n) \<rightarrow> space (G (Suc n))" using stock_filtration
    by (simp add: bernoulli bernoulli_stream_space stoch_proc_filt_space)
  show "\<forall>y\<in>sets (G (Suc n)). (\<lambda>w. spick w n x) -` y \<inter> space (G n) \<in> sets (G n)"
  proof
    fix B
    assume "B\<in> sets (G (Suc n))"
    hence "B\<in> (sigma_sets (space M) (\<Union> i\<in> {m. m\<le> (Suc n)}. {(geom_proc i -`A) \<inter> (space M) | A. A\<in> sets borel }))"
      using stock_filtration stoch_proc_filt_sets geometric_process
    proof -
      have "\<forall>n. sigma_sets (space M) (\<Union>n\<in>{na. na \<le> n}. {geom_proc n -` R \<inter> space M |R. R \<in> sets borel}) = sets (G n)"
        by (simp add: geom_rand_walk_borel_measurable stoch_proc_filt_sets stock_filtration)
      then show ?thesis
        using \<open>B \<in> sets (G (Suc n))\<close> by blast
    qed
    hence "(\<lambda>w. spick w n x) -` B \<in> sets (G n)"
    proof (induct rule:sigma_sets.induct)
      {
        fix C
        assume "C \<in> (\<Union>i\<in>{m. m \<le> Suc n}. {geom_proc i -` A \<inter> space M |A. A \<in> sets borel})"
        hence "\<exists>m \<le> Suc n. C\<in> {geom_proc m -` A \<inter> space M |A. A \<in> sets borel}" by auto
        from this obtain m where "m\<le> Suc n" and "C\<in> {geom_proc m -` A \<inter> space M |A. A \<in> sets borel}" by auto
        note Cprops = this
        from this obtain D where "C = geom_proc m -` D\<inter> space M" and "D\<in> sets borel" by auto
        hence "C = geom_proc m -`D" using bernoulli bernoulli_stream_space by simp
        have "C\<in> {geom_proc m -` A |A. A \<in> sets borel}" using bernoulli bernoulli_stream_space Cprops by simp
        show "(\<lambda>w. spick w n x) -` C \<in> sets (G n)"
        proof (cases "m \<le> n")
          case True
          have "(\<lambda>w. spick w n x) -` C = (\<lambda>w. spick w n x) -` geom_proc m -`D" using \<open>C = geom_proc m -`D\<close> by simp
          also have "... = (geom_proc m \<circ> (\<lambda>w. spick w n x)) -`D" by auto
          also have "... = geom_proc m -`D" using geom_spick_lt geom_spick_eq \<open>m\<le>n\<close>
            using le_eq_less_or_eq by auto
          also have "... \<in> sets (G n)" using stock_filtration geometric_process
            \<open>D\<in> sets borel\<close>
            by (metis (no_types, lifting) True adapt_stoch_proc_def bernoulli bernoulli_stream_preimage
                geom_rand_walk_borel_measurable increasing_measurable_info measurable_sets stoch_proc_filt_adapt
                stoch_proc_filt_space)
          finally show "(\<lambda>w. spick w n x) -` C \<in> sets (G n)" .
        next
          case False
          hence "m = Suc n" using \<open>m \<le> Suc n\<close> by simp
          hence "(\<lambda>w. spick w n x) -` C \<in> {geom_proc n -` B |B. B \<in> sets borel}"
            using \<open>C\<in> {geom_proc m -` A |A. A \<in> sets borel}\<close> geom_spick_Suc by simp
          also have "... \<subseteq> sets (G n)"
          proof -
            have "{geom_proc n -` B |B. B \<in> sets borel} \<subseteq> {geom_proc n -` B \<inter> space M |B. B \<in> sets borel}"
              using bernoulli bernoulli_stream_space by simp
            also have "... \<subseteq> (\<Union>i\<in>{m. m \<le> n}. {geom_proc i -` A \<inter> space M |A. A \<in> sets borel})"
               by auto
            also have "... \<subseteq>  sigma_sets (space M) (\<Union>i\<in>{m. m \<le> n}. {geom_proc i -` A \<inter> space M |A. A \<in> sets borel})"
              by (rule sigma_sets_superset_generator)
            also have "... = sets (G n)" using stock_filtration geometric_process
              stoch_proc_filt_sets[of n geom_proc M borel] geom_rand_walk_borel_measurable by blast
            finally show ?thesis .
          qed
          finally show ?thesis .
        qed
      }
      show "(\<lambda>w. spick w n x) -` {} \<in> sets (G n)" by simp
      {
        fix C
        assume "C \<in> sigma_sets (space M) (\<Union>i\<in>{m. m \<le> Suc n}. {geom_proc i -` A \<inter> space M |A. A \<in> sets borel})"
          and "(\<lambda>w. spick w n x) -` C \<in> sets (G n)"
        hence "(\<lambda>w. spick w n x) -` (space M - C) = (\<lambda>w. spick w n x) -` (space M) - (\<lambda>w. spick w n x) -` C"
          by (simp add: vimage_Diff)
        also have "... = space M - (\<lambda>w. spick w n x) -` C" using bernoulli bernoulli_stream_space by simp
        also have "... \<in> sets (G n)" using \<open>(\<lambda>w. spick w n x) -` C \<in> sets (G n)\<close>
          by (metis algebra.compl_sets disc_filtr_def discrete_filtration sets.sigma_algebra_axioms
              sigma_algebra_def subalgebra_def)
        finally show "(\<lambda>w. spick w n x) -` (space M - C) \<in> sets (G n)" .
      }
      {
        fix C::"nat \<Rightarrow> bool stream set"
        assume "(\<And>i. C i \<in> sigma_sets (space M) (\<Union>i\<in>{m. m \<le> Suc n}. {geom_proc i -` A \<inter> space M |A. A \<in> sets borel}))"
          and "(\<And>i. (\<lambda>w. spick w n x) -` C i \<in> sets (G n))"
        hence "(\<lambda>w. spick w n x) -` \<Union>(C ` UNIV) = (\<Union> i\<in> UNIV. (\<lambda>w. spick w n x) -` (C i))" by blast
        also have "... \<in> sets (G n)" using \<open>\<And>i. (\<lambda>w. spick w n x) -` C i \<in> sets (G n)\<close> by simp
        finally show "(\<lambda>w. spick w n x) -` \<Union>(C ` UNIV) \<in> sets (G n)" .
      }
    qed
    thus "(\<lambda>w. spick w n x) -` B \<inter> space (G n) \<in> sets (G n)" using stock_filtration stoch_proc_filt_space
      bernoulli bernoulli_stream_space by simp
  qed
qed

lemma (in CRR_market) delta_price_adapted:
   fixes cash_flow::"bool stream \<Rightarrow> real"
   assumes "cash_flow \<in> borel_measurable (G T)"
and "N = bernoulli_stream q"
and "0 < q"
and "q < 1"
  shows "borel_adapt_stoch_proc G (delta_price N cash_flow T)"
unfolding adapt_stoch_proc_def
proof
  fix n
  show "delta_price N cash_flow T n \<in> borel_measurable (G n)"
  proof (cases "Suc n \<le> T")
    case True
    hence deleq: "\<forall>w. delta_price N cash_flow T n w = (rn_price N cash_flow T (Suc n) (spick w n True) - rn_price N cash_flow T (Suc n) (spick w n False))/
    ((geom_proc n w) * (u - d))" using delta_price_eq by simp
    have "(\<lambda>w. rn_price N cash_flow T (Suc n) (spick w n True)) \<in> borel_measurable (G n)"
    proof -
      have "rn_price N cash_flow T (Suc n) \<in> borel_measurable  (G (Suc n))" using rn_price_borel_adapt assms
        using True by blast
      moreover have "(\<lambda>w. spick w n True) \<in> G n \<rightarrow>\<^sub>M G (Suc n)" using spick_red_geom_filt by simp
      ultimately show ?thesis by simp
    qed
    moreover have "(\<lambda>w. rn_price N cash_flow T (Suc n) (spick w n False)) \<in> borel_measurable (G n)"
    proof -
      have "rn_price N cash_flow T (Suc n) \<in> borel_measurable  (G (Suc n))" using rn_price_borel_adapt assms
        using True by blast
      moreover have "(\<lambda>w. spick w n False) \<in> G n \<rightarrow>\<^sub>M G (Suc n)" using spick_red_geom_filt by simp
      ultimately show ?thesis by simp
    qed
    ultimately have "(\<lambda>w. rn_price N cash_flow T (Suc n) (spick w n True) - rn_price N cash_flow T (Suc n) (spick w n False))
      \<in> borel_measurable (G n)" by simp
    moreover have "(\<lambda>w. (geom_proc n w) * (u - d)) \<in> borel_measurable (G n)"
    proof -
      have "geom_proc n \<in> borel_measurable (G n)" using stock_filtration
        by (metis adapt_stoch_proc_def stk_price stock_price_borel_measurable)
      thus ?thesis by simp
    qed
    ultimately have "(\<lambda>w. (rn_price N cash_flow T (Suc n) (spick w n True) - rn_price N cash_flow T (Suc n) (spick w n False))/
      ((geom_proc n w) * (u - d)))\<in> borel_measurable (G n)" by simp
    thus ?thesis using deleq by presburger
  next
    case False
    thus ?thesis unfolding delta_price_def by simp
  qed
qed

fun (in CRR_market) delta_predict where
  "delta_predict N der matur 0  = (\<lambda>w. delta_price N der matur 0 w)" |
  "delta_predict N der matur (Suc n) = (\<lambda>w. delta_price N der matur n w)"

lemma (in CRR_market) delta_predict_predict:
  assumes "der \<in> borel_measurable (G matur)"
and "N = bernoulli_stream q"
and "0 < q"
and "q < 1"
  shows "borel_predict_stoch_proc G (delta_predict N der matur)" unfolding predict_stoch_proc_def
proof (intro conjI)
  show "delta_predict N der matur 0 \<in> borel_measurable (G 0)" using delta_price_adapted[of der matur N q]
    assms unfolding adapt_stoch_proc_def by force
  show "\<forall>n. delta_predict N der matur (Suc n) \<in> borel_measurable (G n)"
  proof
    fix n
    show "delta_predict N der matur (Suc n) \<in> borel_measurable (G n)" using delta_price_adapted[of der matur N q]
    assms unfolding adapt_stoch_proc_def by force
  qed
qed


definition (in CRR_market) delta_pf where
"delta_pf N der matur = qty_single stk (delta_predict N der matur)"

lemma (in CRR_market) delta_pf_support:
  shows "support_set (delta_pf N der matur) \<subseteq> {stk}" unfolding delta_pf_def
  using single_comp_support[of stk "delta_predict N der matur"] by simp

definition (in CRR_market) self_fin_delta_pf where
"self_fin_delta_pf N der matur v0 = self_finance Mkt v0 (delta_pf N der matur) risk_free_asset"

lemma (in disc_equity_market) self_finance_trading_strat:
  assumes "trading_strategy pf"
and "portfolio pf"
and "borel_adapt_stoch_proc F (prices Mkt asset)"
and "support_adapt Mkt pf"
shows "trading_strategy (self_finance Mkt v pf asset)" unfolding self_finance_def
proof (rule sum_trading_strat)
  show "trading_strategy pf" using assms by simp
  show "trading_strategy (qty_single asset (remaining_qty Mkt v pf asset))" unfolding trading_strategy_def
  proof (intro conjI ballI)
  show "portfolio (qty_single asset (remaining_qty Mkt v pf asset))"
    by (simp add: self_finance_def single_comp_portfolio)
  show "\<And>a.
       a \<in> support_set (qty_single asset (remaining_qty Mkt v pf asset)) \<Longrightarrow>
       borel_predict_stoch_proc F (qty_single asset (remaining_qty Mkt v pf asset) a)"
  proof (cases "support_set (qty_single asset (remaining_qty Mkt v pf asset)) = {}")
    case False
    hence eqasset: "support_set (qty_single asset (remaining_qty Mkt v pf asset)) = {asset}"
      using single_comp_support by fastforce
    fix a
    assume "a\<in> support_set (qty_single asset (remaining_qty Mkt v pf asset))"
    hence "a = asset" using eqasset by simp
    hence "qty_single asset (remaining_qty Mkt v pf asset) a = (remaining_qty Mkt v pf asset)"
      unfolding qty_single_def by simp
    moreover have "borel_predict_stoch_proc F (remaining_qty Mkt v pf asset)"
    proof (rule remaining_qty_predict)
      show "trading_strategy pf" using assms by simp
      show "borel_adapt_stoch_proc F (prices Mkt asset)" using assms by simp
      show "support_adapt Mkt pf" using assms by simp
    qed
    ultimately show "borel_predict_stoch_proc F (qty_single asset (remaining_qty Mkt v pf asset) a)"
      by simp
  next
    case True
    thus "\<And>a. a \<in> support_set (qty_single asset (remaining_qty Mkt v pf asset)) \<Longrightarrow>
         support_set (qty_single asset (remaining_qty Mkt v pf asset)) = {} \<Longrightarrow>
         borel_predict_stoch_proc F (qty_single asset (remaining_qty Mkt v pf asset) a)" by simp
  qed
qed
qed

lemma (in CRR_market) self_fin_delta_pf_trad_strat:
  assumes "der\<in> borel_measurable (G matur)"
and "N = bernoulli_stream q"
and "0 < q"
and "q < 1"
  shows "trading_strategy (self_fin_delta_pf N der matur v0)" unfolding self_fin_delta_pf_def
proof (rule self_finance_trading_strat)
  show "trading_strategy (delta_pf N der matur)" unfolding trading_strategy_def
  proof (intro conjI ballI)
    show "portfolio (delta_pf N der matur)" unfolding portfolio_def using delta_pf_support
      by (meson finite.emptyI finite_insert infinite_super)
    show "\<And>asset. asset \<in> support_set (delta_pf N der matur) \<Longrightarrow> borel_predict_stoch_proc G (delta_pf N der matur asset)"
    proof (cases "support_set (delta_pf N der matur) = {}")
      case False
      fix asset
      assume "asset \<in> support_set (delta_pf N der matur)"
      hence "asset = stk" using False delta_pf_support by auto
      hence "delta_pf N der matur asset = delta_predict N der matur" unfolding delta_pf_def qty_single_def by simp
      thus "borel_predict_stoch_proc G (delta_pf N der matur asset)" using delta_predict_predict
        assms by simp
    next
      case True
      thus "\<And>asset. asset \<in> support_set (delta_pf N der matur) \<Longrightarrow>
             support_set (delta_pf N der matur) = {} \<Longrightarrow> borel_predict_stoch_proc G (delta_pf N der matur asset)" by simp
    qed
  qed
  show "portfolio (delta_pf N der matur)" using delta_pf_support unfolding portfolio_def
    by (meson finite.emptyI finite_insert infinite_super)
  show "borel_adapt_stoch_proc G (prices Mkt risk_free_asset)" using rf_price
    disc_rfr_proc_borel_adapted by simp
  show "support_adapt Mkt (delta_pf N der matur)" unfolding support_adapt_def
  proof
    show "\<And>asset. asset \<in> support_set (delta_pf N der matur) \<Longrightarrow> borel_adapt_stoch_proc G (prices Mkt asset)"
    proof (cases "support_set (delta_pf N der matur) = {}")
      case False
      fix asset
      assume "asset \<in> support_set (delta_pf N der matur)"
      hence "asset = stk" using False delta_pf_support by auto
      hence "prices Mkt asset = geom_proc" using stk_price by simp
      thus "borel_adapt_stoch_proc G (prices Mkt asset)"
        using \<open>asset = stk\<close> stock_price_borel_measurable by auto
    next
      case True
      thus "\<And>asset. asset \<in> support_set (delta_pf N der matur) \<Longrightarrow> borel_adapt_stoch_proc G (prices Mkt asset)"
        by simp
    qed
  qed
qed

definition (in CRR_market) delta_hedging where
"delta_hedging N der matur = self_fin_delta_pf N der matur
  (prob_space.expectation N (discounted_value r (\<lambda>m. der) matur))"


lemma (in CRR_market)  geom_proc_eq_snth:
  shows "(\<And>m. m \<le> Suc n \<Longrightarrow> geom_proc m x = geom_proc m y) \<Longrightarrow>
    (\<And>m. m \<le> n \<Longrightarrow> snth x m = snth y m)"
proof (induct n )
  case 0
  assume asm: "(\<And>m. m \<le>Suc  0 \<Longrightarrow> geom_proc m x = geom_proc m y)" and "m\<le> 0"
  hence "m = 0" by simp
  have "geom_proc (Suc 0) x = geom_proc (Suc 0) y" using asm by simp
  have "snth x 0 = snth y 0"
  proof (rule ccontr)
    assume "snth x 0 \<noteq> snth y 0"
    show False
    proof (cases "snth x 0")
      case True
      hence "\<not> snth y 0" using \<open>snth x 0 \<noteq> snth y 0\<close> by simp
      have "geom_proc (Suc 0) x = u * init" using geometric_process True by simp
      moreover have "geom_proc (Suc 0) y = d * init" using geometric_process \<open>\<not> snth y 0\<close> by simp
      ultimately have "geom_proc (Suc 0) x \<noteq> geom_proc (Suc 0) y" using S0_positive down_lt_up by simp
      thus ?thesis using \<open>geom_proc (Suc 0) x = geom_proc (Suc 0) y\<close> by simp
    next
      case False
      hence "snth y 0" using \<open>snth x 0 \<noteq> snth y 0\<close> by simp
      have "geom_proc (Suc 0) x = d * init" using geometric_process False by simp
      moreover have "geom_proc (Suc 0) y = u * init" using geometric_process \<open>snth y 0\<close> by simp
      ultimately have "geom_proc (Suc 0) x \<noteq> geom_proc (Suc 0) y" using S0_positive down_lt_up by simp
      thus ?thesis using \<open>geom_proc (Suc 0) x = geom_proc (Suc 0) y\<close> by simp
    qed
  qed
  thus "\<And>m. (\<And>m. m \<le> Suc 0 \<Longrightarrow> geom_proc m x = geom_proc m y) \<Longrightarrow> m \<le> 0 \<Longrightarrow> x !! m = y !! m" by simp
next
  case (Suc n)
  assume fst: "(\<And>m. (\<And>m. m \<le> Suc n \<Longrightarrow> geom_proc m x = geom_proc m y) \<Longrightarrow> m \<le> n \<Longrightarrow> x !! m = y !! m)"
    and scd: "(\<And>m. m \<le> Suc (Suc n) \<Longrightarrow> geom_proc m x = geom_proc m y)" and "m \<le> Suc n"
  show "x !! m = y !! m"
  proof (cases "m \<le> n")
    case True
    thus ?thesis using fst scd by simp
  next
    case False
    hence "m = Suc n" using \<open>m\<le> Suc n\<close> by simp
    have "geom_proc (Suc (Suc n)) x = geom_proc (Suc (Suc n)) y" using scd by simp
    show ?thesis
    proof (rule ccontr)
      assume "x !! m \<noteq> y !! m"
      thus False
      proof (cases "x !! m")
        case True
        hence "\<not> y !! m" using \<open>x !! m \<noteq> y !! m\<close> by simp
        have "geom_proc (Suc (Suc n)) x = u * geom_proc (Suc n) x" using geometric_process True
          \<open>m = Suc n\<close> by simp
        also have "... = u * geom_proc (Suc n) y" using scd \<open>m = Suc n\<close> by simp
        finally have "geom_proc (Suc (Suc n)) x = u * geom_proc (Suc n) y" .
        moreover have "geom_proc (Suc (Suc n)) y = d * geom_proc (Suc n) y" using geometric_process
          \<open>m = Suc n\<close> \<open>\<not> y !! m\<close> by simp
        ultimately have "geom_proc (Suc (Suc n)) x \<noteq> geom_proc (Suc (Suc n)) y"
          by (metis S0_positive down_lt_up down_positive geom_rand_walk_strictly_positive less_irrefl mult_cancel_right)
        thus ?thesis using \<open>geom_proc (Suc (Suc n)) x = geom_proc (Suc (Suc n)) y\<close> by simp
      next
        case False
        hence "y !! m" using \<open>x !! m \<noteq> y !! m\<close> by simp
        have "geom_proc (Suc (Suc n)) x = d * geom_proc (Suc n) x" using geometric_process False
          \<open>m = Suc n\<close> by simp
        also have "... = d * geom_proc (Suc n) y" using scd \<open>m = Suc n\<close> by simp
        finally have "geom_proc (Suc (Suc n)) x = d * geom_proc (Suc n) y" .
        moreover have "geom_proc (Suc (Suc n)) y = u * geom_proc (Suc n) y" using geometric_process
          \<open>m = Suc n\<close> \<open>y !! m\<close> by simp
        ultimately have "geom_proc (Suc (Suc n)) x \<noteq> geom_proc (Suc (Suc n)) y"
          by (metis S0_positive down_lt_up down_positive geom_rand_walk_strictly_positive less_irrefl mult_cancel_right)
        thus ?thesis using \<open>geom_proc (Suc (Suc n)) x = geom_proc (Suc (Suc n)) y\<close> by simp
      qed
    qed
  qed
qed

lemma (in CRR_market)  geom_proc_eq_pseudo_proj_True:
  shows "(\<And>m. m \<le>  n \<Longrightarrow> geom_proc m x = geom_proc m y) \<Longrightarrow>
    (pseudo_proj_True (n) x = pseudo_proj_True (n) y)"
proof -
  assume a1: "\<And>m. m \<le> n \<Longrightarrow> geom_proc m x = geom_proc m y"
  obtain nn :: "bool stream \<Rightarrow> bool stream \<Rightarrow> nat \<Rightarrow> nat" where
    "\<forall>x1 x2 x3. (\<exists>v4<Suc (Suc x3). geom_proc v4 x2 \<noteq> geom_proc v4 x1) = (nn x1 x2 x3 < Suc (Suc x3) \<and> geom_proc (nn x1 x2 x3) x2 \<noteq> geom_proc (nn x1 x2 x3) x1)"
    by moura
  then have f2: "\<forall>n s sa na. (nn sa s n < Suc (Suc n) \<and> geom_proc (nn sa s n) s \<noteq> geom_proc (nn sa s n) sa \<or> \<not> na < Suc n) \<or> s !! na = sa !! na"
    by (meson geom_proc_eq_snth less_Suc_eq_le)
  obtain nna :: "bool stream \<Rightarrow> bool stream \<Rightarrow> nat \<Rightarrow> nat" where
    f3: "\<forall>x0 x1 x2. (\<exists>v3. Suc v3 < Suc x2 \<and> x1 !! v3 \<noteq> x0 !! v3) = (Suc (nna x0 x1 x2) < Suc x2 \<and> x1 !! nna x0 x1 x2 \<noteq> x0 !! nna x0 x1 x2)"
    by moura
  obtain nnb :: "nat \<Rightarrow> nat" where
    f4: "\<forall>x0. (\<exists>v2. x0 = Suc v2) = (x0 = Suc (nnb x0))"
    by moura
  moreover
  { assume "\<not> nn y x (nnb n) < Suc (Suc (nnb n)) \<or> geom_proc (nn y x (nnb n)) x = geom_proc (nn y x (nnb n)) y"
    moreover
    { assume "\<not> nna y x n < Suc (nnb n)"
      then have "\<not> Suc (nna y x n) < Suc n \<or> x !! nna y x n = y !! nna y x n"
        using f4 by (metis (no_types) Suc_le_D Suc_le_lessD less_Suc_eq_le) }
    ultimately have "pseudo_proj_True n x = pseudo_proj_True n y \<or> \<not> Suc (nna y x n) < Suc n \<or> x !! nna y x n = y !! nna y x n"
using f2 by meson }
  ultimately have "pseudo_proj_True n x = pseudo_proj_True n y \<or> \<not> Suc (nna y x n) < Suc n \<or> x !! nna y x n = y !! nna y x n"
    using a1 Suc_le_D less_Suc_eq_le by presburger
  then show ?thesis
    using f3 by (meson less_Suc_eq_le pseudo_proj_True_snth')
qed




lemma (in CRR_market)  proj_stoch_eq_pseudo_proj_True:
  assumes "proj_stoch_proc geom_proc m x = proj_stoch_proc geom_proc m y"
  shows "pseudo_proj_True m x = pseudo_proj_True m y"
proof -
  have "\<forall> k \<le> m. geom_proc k x = geom_proc k y"
  proof (intro allI impI)
    fix k
    assume "k \<le> m"
    thus "geom_proc k x = geom_proc k y" using proj_stoch_proc_eq_snth[of geom_proc m x y k] assms by simp
  qed
  thus ?thesis  using geom_proc_eq_pseudo_proj_True[of m x y] by auto
qed

lemma (in CRR_market_viable) rn_rev_price_cond_expect:
  assumes "N = bernoulli_stream q"
and "0 <q"
and "q < 1"
and "der \<in> borel_measurable (G matur)"
and "Suc n \<le> matur"
shows "expl_cond_expect N (proj_stoch_proc geom_proc n) (rn_rev_price N der matur (matur - Suc n)) w=
  (q * rn_rev_price N der matur (matur - Suc n) (pseudo_proj_True n w)  +
      (1 - q) * rn_rev_price N der matur (matur - Suc n) (pseudo_proj_False n w))"
proof (rule infinite_cts_filtration.f_borel_Suc_expl_cond_expect)
  show "infinite_cts_filtration q N nat_filtration" using  assms  pslt psgt
    bernoulli_nat_filtration by simp
  show "rn_rev_price N der matur (matur - Suc n) \<in> borel_measurable (nat_filtration (Suc n))"
    using rn_rev_price_rev_borel_adapt[of der matur N q "Suc n"]   assms
      stock_filtration stoch_proc_subalg_nat_filt[of geom_proc] geom_rand_walk_borel_adapted
    by (metis add_diff_cancel_right' diff_le_self measurable_from_subalg
        ordered_cancel_comm_monoid_diff_class.add_diff_inverse rn_rev_price_rev_borel_adapt)
  show "proj_stoch_proc geom_proc n \<in> nat_filtration n \<rightarrow>\<^sub>M stream_space borel"
    using proj_stoch_adapted_if_adapted[of M nat_filtration geom_proc borel n]
    pslt psgt bernoulli_nat_filtration[of M p] bernoulli geom_rand_walk_borel_adapted
    nat_discrete_filtration by blast
  show "set_discriminating n (proj_stoch_proc geom_proc n) (stream_space borel)"
    using infinite_cts_filtration.proj_stoch_set_discriminating
    pslt psgt bernoulli_nat_filtration[of M p] bernoulli geom_rand_walk_borel_adapted by simp
  show "proj_stoch_proc geom_proc n -` {proj_stoch_proc geom_proc n w} \<in> sets (nat_filtration n)"
    using infinite_cts_filtration.proj_stoch_singleton_set
    pslt psgt bernoulli_nat_filtration[of M p] bernoulli geom_rand_walk_borel_adapted by simp
  show "\<forall>y z. proj_stoch_proc geom_proc n y = proj_stoch_proc geom_proc n z \<and> y !! n = z !! n \<longrightarrow>
    rn_rev_price N der matur (matur - Suc n) y = rn_rev_price N der matur (matur - Suc n) z"
  proof (intro allI impI)
    fix y z
    assume as:"proj_stoch_proc geom_proc n y = proj_stoch_proc geom_proc n z \<and> y !! n = z !! n"
    hence "pseudo_proj_True n y = pseudo_proj_True n z" using proj_stoch_eq_pseudo_proj_True[of n y z] by simp
    moreover have "snth y n = snth z n" using as by simp
    ultimately have "pseudo_proj_True (Suc n) y = pseudo_proj_True (Suc n) z"
    proof -
    have f1: "\<forall>n s sa. (\<exists>na. Suc na \<le> n \<and> s !! na \<noteq> sa !! na) \<or> pseudo_proj_True n s = pseudo_proj_True n sa"
    by (meson pseudo_proj_True_snth')
      obtain nn :: "bool stream \<Rightarrow> bool stream \<Rightarrow> nat \<Rightarrow> nat" where
        "\<forall>x0 x1 x2. (\<exists>v3. Suc v3 \<le> x2 \<and> x1 !! v3 \<noteq> x0 !! v3) = (Suc (nn x0 x1 x2) \<le> x2 \<and> x1 !! nn x0 x1 x2 \<noteq> x0 !! nn x0 x1 x2)"
        by moura
        then have f2: "\<forall>n s sa. Suc (nn sa s n) \<le> n \<and> s !! nn sa s n \<noteq> sa !! nn sa s n \<or> pseudo_proj_True n s = pseudo_proj_True n sa"
          using f1 by presburger
        have f3: "stake n y = stake n (pseudo_proj_True n z)"
          by (metis \<open>pseudo_proj_True n y = pseudo_proj_True n z\<close> pseudo_proj_True_stake)
        { assume "stake (Suc n) z \<noteq> stake (Suc n) (pseudo_proj_True (Suc n) y)"
          then have "stake n y @ [y !! n] \<noteq> stake n z @ [z !! n]"
            by (metis (no_types) pseudo_proj_True_stake stake_Suc)
          then have "stake (Suc n) z = stake (Suc n) (pseudo_proj_True (Suc n) y)"
            using f3 by (simp add: \<open>y !! n = z !! n\<close> pseudo_proj_True_stake) }
        then have "\<not> Suc (nn z y (Suc n)) \<le> Suc n \<or> y !! nn z y (Suc n) = z !! nn z y (Suc n)"
        by (metis (no_types) pseudo_proj_True_stake stake_snth)
      then show ?thesis
        using f2 by blast
    qed
    have "rn_rev_price N der matur (matur - Suc n) y =
      rn_rev_price N der matur (matur - Suc n) (pseudo_proj_True (Suc n) y)" using nat_filtration_info[of "rn_rev_price N der matur (matur - Suc n)" "Suc n"]
      rn_rev_price_rev_borel_adapt[of der matur N q]
      by (metis \<open>rn_rev_price N der matur (matur - Suc n) \<in> borel_measurable (nat_filtration (Suc n))\<close> o_apply)
    also have "... = rn_rev_price N der matur (matur - Suc n) (pseudo_proj_True (Suc n) z)"
      using \<open>pseudo_proj_True (Suc n) y = pseudo_proj_True (Suc n) z\<close> by simp
    also have "... = rn_rev_price N der matur (matur - Suc n) z" using nat_filtration_info[of "rn_rev_price N der matur (matur - Suc n)" "Suc n"]
      rn_rev_price_rev_borel_adapt[of der matur N q]
      by (metis \<open>rn_rev_price N der matur (matur - Suc n) \<in> borel_measurable (nat_filtration (Suc n))\<close> o_apply)
    finally show "rn_rev_price N der matur (matur - Suc n) y = rn_rev_price N der matur (matur - Suc n) z" .
  qed
  show "0 < q" and "q < 1" using assms by auto
qed




lemma (in CRR_market_viable) rn_price_eq_ind:
  assumes "N = bernoulli_stream q"
and "n < matur"
and "0 < q"
and "q < 1"
and "der \<in> borel_measurable (G matur)"
shows "(1+r) * rn_price N der matur n w = q * rn_price N der matur (Suc n) (pseudo_proj_True n w) +
  (1 - q) * rn_price N der matur (Suc n) (pseudo_proj_False n w)"
proof -
  define V where "V = rn_price N der matur"
  let ?m = "matur - Suc n"
  have "matur -n = Suc ?m" by (simp add: assms Suc_diff_Suc Suc_le_lessD)
  have "(1+r) * V n w = (1+r) * rn_price_ind N der matur n w" using rn_price_eq assms unfolding V_def by simp
  also have "... = (1+r) * rn_rev_price N der matur (Suc ?m) w" using \<open>matur -n = Suc ?m\<close>
    unfolding rn_price_ind_def by simp
  also have "... = (1+r) * discount_factor r (Suc 0) w *
                    expl_cond_expect N (proj_stoch_proc geom_proc (matur - Suc ?m)) (rn_rev_price N der matur ?m) w"
    by simp
  also have "... = expl_cond_expect N (proj_stoch_proc geom_proc (matur - Suc ?m)) (rn_rev_price N der matur ?m) w"
    unfolding discount_factor_def using acceptable_rate by auto
  also have "... = expl_cond_expect N (proj_stoch_proc geom_proc n) (rn_rev_price N der matur ?m) w"
    using \<open>matur -n = Suc ?m\<close> by simp
  also have "... = (q * rn_rev_price N der matur ?m (pseudo_proj_True n w)  +
    (1 - q) * rn_rev_price N der matur ?m (pseudo_proj_False n w))"
    using rn_rev_price_cond_expect[of N q der matur n w] assms   by simp
  also have "... =  q * rn_price_ind N der matur (Suc n) (pseudo_proj_True n w) +
    (1 - q) * rn_price_ind N der matur (Suc n) (pseudo_proj_False n w)" unfolding rn_price_ind_def by simp
  also have "... = q * rn_price N der matur (Suc n) (pseudo_proj_True n w) +
    (1 - q) * rn_price N der matur (Suc n) (pseudo_proj_False n w)" using rn_price_eq assms  by simp
  also have "... = q * V (Suc n) (pseudo_proj_True n w) + (1 - q) *V (Suc n) (pseudo_proj_False n w)"
    unfolding V_def by simp
  finally have "(1+r) * V n w = q * V (Suc n) (pseudo_proj_True n w) + (1 - q) *V (Suc n) (pseudo_proj_False n w)" .
  thus ?thesis unfolding V_def by simp
qed



lemma self_finance_updated_suc_suc:
  assumes "portfolio pf"
  and "\<forall>n. prices Mkt asset n w \<noteq> 0"
  shows "cls_val_process Mkt (self_finance Mkt v pf asset) (Suc (Suc n)) w = cls_val_process Mkt pf (Suc (Suc n)) w +
    (prices Mkt asset (Suc (Suc n)) w / (prices Mkt asset (Suc n) w)) *
      (cls_val_process Mkt (self_finance Mkt v pf asset) (Suc n) w -
     val_process Mkt pf (Suc n) w)"
proof -
  have "cls_val_process Mkt (self_finance Mkt v pf asset) (Suc (Suc n)) w = cls_val_process Mkt pf (Suc (Suc n)) w +
    prices Mkt asset (Suc (Suc n)) w * remaining_qty Mkt v pf asset (Suc (Suc n)) w" using assms
    by (simp add: self_finance_updated)
  also have "... = cls_val_process Mkt pf (Suc (Suc n)) w +
    prices Mkt asset (Suc (Suc n)) w * ((remaining_qty Mkt v pf asset (Suc n) w) +
    (cls_val_process Mkt pf (Suc n) w - val_process Mkt pf (Suc n) w)/(prices Mkt asset (Suc n) w))"
    by simp
  also have "... = cls_val_process Mkt pf (Suc (Suc n)) w +
    prices Mkt asset (Suc (Suc n)) w *
      ((prices Mkt asset (Suc n) w) * (remaining_qty Mkt v pf asset (Suc n) w) / (prices Mkt asset (Suc n) w) +
    (cls_val_process Mkt pf (Suc n) w - val_process Mkt pf (Suc n) w)/(prices Mkt asset (Suc n) w))" using assms
    by (metis nonzero_mult_div_cancel_left)
  also have "... = cls_val_process Mkt pf (Suc (Suc n)) w +
    prices Mkt asset (Suc (Suc n)) w * ((prices Mkt asset (Suc n) w) * (remaining_qty Mkt v pf asset (Suc n) w) +
    cls_val_process Mkt pf (Suc n) w - val_process Mkt pf (Suc n) w)/(prices Mkt asset (Suc n) w)"
    using add_divide_distrib[symmetric, of "prices Mkt asset (Suc n) w * remaining_qty Mkt v pf asset (Suc n) w"
        "prices Mkt asset (Suc n) w"]  by simp
  also have "... = cls_val_process Mkt pf (Suc (Suc n)) w +
    (prices Mkt asset (Suc (Suc n)) w / (prices Mkt asset (Suc n) w)) *
    ((prices Mkt asset (Suc n) w) * (remaining_qty Mkt v pf asset (Suc n) w) +
    cls_val_process Mkt pf (Suc n) w - val_process Mkt pf (Suc n) w)" by simp
  also have "... = cls_val_process Mkt pf (Suc (Suc n)) w +
    (prices Mkt asset (Suc (Suc n)) w / (prices Mkt asset (Suc n) w)) *
      (cls_val_process Mkt (self_finance Mkt v pf asset) (Suc n) w -
     val_process Mkt pf (Suc n) w)"
    using self_finance_updated[of Mkt asset n w pf v] assms by auto
  finally show ?thesis .
qed

lemma self_finance_updated_suc_0:
  assumes "portfolio pf"
  and "\<forall>n w. prices Mkt asset n w \<noteq> 0"
  shows "cls_val_process Mkt (self_finance Mkt v pf asset) (Suc 0) w = cls_val_process Mkt pf (Suc 0) w +
    (prices Mkt asset (Suc 0) w / (prices Mkt asset 0 w)) *
      (val_process Mkt (self_finance Mkt v pf asset) 0 w -
     val_process Mkt pf 0 w)"
proof -
  have "cls_val_process Mkt (self_finance Mkt v pf asset) (Suc 0) w = cls_val_process Mkt pf (Suc 0) w +
    prices Mkt asset (Suc 0) w * remaining_qty Mkt v pf asset (Suc 0) w" using assms
    by (simp add: self_finance_updated)
  also have "... = cls_val_process Mkt pf (Suc 0) w +
    prices Mkt asset (Suc 0) w * ((v - val_process Mkt pf 0 w)/(prices Mkt asset 0 w))"
    by simp
  also have "... = cls_val_process Mkt pf (Suc 0) w +
    prices Mkt asset (Suc 0) w * ((remaining_qty Mkt v pf asset 0 w) +
    (v - val_process Mkt pf 0 w)/(prices Mkt asset 0 w))"
    by simp
  also have "... = cls_val_process Mkt pf (Suc 0) w +
    prices Mkt asset (Suc 0) w *
      ((prices Mkt asset 0 w) * (remaining_qty Mkt v pf asset 0 w) / (prices Mkt asset 0 w) +
    (v - val_process Mkt pf 0 w)/(prices Mkt asset 0 w))" using assms
    by (metis nonzero_mult_div_cancel_left)
  also have "... = cls_val_process Mkt pf (Suc 0) w +
    prices Mkt asset (Suc 0) w * ((prices Mkt asset 0 w) * (remaining_qty Mkt v pf asset 0 w) +
    v - val_process Mkt pf 0 w)/(prices Mkt asset 0 w)"
    using add_divide_distrib[symmetric, of "prices Mkt asset 0 w * remaining_qty Mkt v pf asset 0 w"
        "prices Mkt asset 0 w"]  by simp
  also have "... = cls_val_process Mkt pf (Suc 0) w +
    (prices Mkt asset (Suc 0) w / (prices Mkt asset 0 w)) *
    ((prices Mkt asset 0 w) * (remaining_qty Mkt v pf asset 0 w) +
    v - val_process Mkt pf 0 w)" by simp
  also have "... = cls_val_process Mkt pf (Suc 0) w +
    (prices Mkt asset (Suc 0) w / (prices Mkt asset 0 w)) *
    ((prices Mkt asset 0 w) * (remaining_qty Mkt v pf asset 0 w) +
    val_process Mkt (self_finance Mkt v pf asset) 0 w - val_process Mkt pf 0 w)"
    using self_finance_init[of Mkt asset pf v w] assms by simp
  also have "... = cls_val_process Mkt pf (Suc 0) w +
    (prices Mkt asset (Suc 0) w / (prices Mkt asset 0 w)) *
      (val_process Mkt (self_finance Mkt v pf asset) 0 w -
     val_process Mkt pf 0 w)" by simp
  finally show ?thesis .
qed

lemma self_finance_updated_ind:
  assumes "portfolio pf"
  and "\<forall>n w. prices Mkt asset n w \<noteq> 0"
  shows "cls_val_process Mkt (self_finance Mkt v pf asset) (Suc n) w = cls_val_process Mkt pf (Suc n) w +
    (prices Mkt asset (Suc n) w / (prices Mkt asset n w)) *
      (val_process Mkt (self_finance Mkt v pf asset) n w -
     val_process Mkt pf n w)"
proof (cases "n = 0")
  case True
  thus ?thesis using assms self_finance_updated_suc_0 by simp
next
  case False
  hence "\<exists>m. n = Suc m" by (simp add: not0_implies_Suc)
  from this obtain m where "n = Suc m" by auto
  hence "cls_val_process Mkt (self_finance Mkt v pf asset) (Suc n) w =
    cls_val_process Mkt (self_finance Mkt v pf asset) (Suc (Suc m)) w" by simp
  also have "...  = cls_val_process Mkt pf (Suc (Suc m)) w +
    (prices Mkt asset (Suc (Suc m)) w / (prices Mkt asset (Suc m) w)) *
      (cls_val_process Mkt (self_finance Mkt v pf asset) (Suc m) w -
     val_process Mkt pf (Suc m) w)" using assms self_finance_updated_suc_suc[of pf] by simp
  also have "... = cls_val_process Mkt pf (Suc (Suc m)) w +
    (prices Mkt asset (Suc (Suc m)) w / (prices Mkt asset (Suc m) w)) *
      (val_process Mkt (self_finance Mkt v pf asset) (Suc m) w -
     val_process Mkt pf (Suc m) w)" using assms self_finance_charact unfolding self_financing_def
    by (simp add: self_finance_succ self_finance_updated)
  also have "... = cls_val_process Mkt pf (Suc n) w +
    (prices Mkt asset (Suc n) w / (prices Mkt asset n w)) *
      (val_process Mkt (self_finance Mkt v pf asset) n w -
     val_process Mkt pf n w)" using \<open>n = Suc m\<close> by simp
  finally show ?thesis .
qed


lemma  (in rfr_disc_equity_market) self_finance_risk_free_update_ind:
  assumes "portfolio pf"
  shows "cls_val_process Mkt (self_finance Mkt v pf risk_free_asset) (Suc n) w = cls_val_process Mkt pf (Suc n) w +
    (1 + r) * (val_process Mkt (self_finance Mkt v pf risk_free_asset) n w - val_process Mkt pf n w)"
proof -
  have "cls_val_process Mkt (self_finance Mkt v pf risk_free_asset) (Suc n) w =
    cls_val_process Mkt pf (Suc n) w +
    (prices Mkt risk_free_asset (Suc n) w / (prices Mkt risk_free_asset n w)) *
      (val_process Mkt (self_finance Mkt v pf risk_free_asset) n w -
     val_process Mkt pf n w)"
  proof (rule self_finance_updated_ind, (simp add: assms), intro allI)
    fix n w
    show "prices Mkt risk_free_asset n w \<noteq> 0" using positive by (metis less_irrefl)
  qed
  also have "... = cls_val_process Mkt pf (Suc n) w +
    (1+r) * (val_process Mkt (self_finance Mkt v pf risk_free_asset) n w -
     val_process Mkt pf n w)" using rf_price  positive
    by (metis acceptable_rate disc_rfr_proc_Suc_div)
  finally show ?thesis .
qed



lemma (in CRR_market) delta_pf_portfolio:
  shows "portfolio (delta_pf N der matur)" unfolding delta_pf_def by (simp add: single_comp_portfolio)

lemma (in CRR_market) delta_pf_updated:
  shows "cls_val_process Mkt (delta_pf N der matur) (Suc n) w =
    geom_proc (Suc n) w * delta_price N der matur n w" unfolding delta_pf_def
    using stk_price qty_single_updated[of Mkt] by simp

lemma (in CRR_market) delta_pf_val_process:
  shows "val_process Mkt (delta_pf N der matur) n w =
    geom_proc n w * delta_price N der matur n w" unfolding delta_pf_def
  using stk_price qty_single_val_process[of Mkt] by simp

lemma (in CRR_market) delta_hedging_cls_val_process:
  shows "cls_val_process Mkt (delta_hedging N der matur) (Suc n) w =
    geom_proc (Suc n) w * delta_price N der matur n w +
    (1 + r) * (val_process Mkt (delta_hedging N der matur) n w - geom_proc n w * delta_price N der matur n w)"
proof -
  define X where "X = delta_hedging N der matur"
  define init where "init = integral\<^sup>L N (discounted_value r (\<lambda>m. der) matur)"
  have "cls_val_process Mkt X (Suc n) w = cls_val_process Mkt (delta_pf N der matur) (Suc n) w +
    (1 + r) * (val_process Mkt X n w - val_process Mkt (delta_pf N der matur) n w)"
    unfolding X_def delta_hedging_def self_fin_delta_pf_def init_def
  proof (rule self_finance_risk_free_update_ind)
    show "portfolio (delta_pf N der matur)" unfolding  portfolio_def using delta_pf_support
      by (meson finite.simps infinite_super)
  qed
  also have "... = geom_proc (Suc n) w * delta_price N der matur n w +
    (1 + r) * (val_process Mkt X n w - val_process Mkt (delta_pf N der matur) n w)"
    using delta_pf_updated by simp
  also have "... = geom_proc (Suc n) w * delta_price N der matur n w +
    (1 + r) * (val_process Mkt X n w - geom_proc n w * delta_price N der matur n w)"
    using delta_pf_val_process by simp
  finally show ?thesis unfolding X_def .
qed







lemma (in CRR_market_viable) delta_hedging_eq_derivative_price:
  fixes der::"bool stream \<Rightarrow> real" and matur::nat
  assumes "N = bernoulli_stream ((1 + r - d) / (u - d))"
  and "der\<in> borel_measurable (G matur)"
  shows "\<And>n w. n\<le> matur \<Longrightarrow>
    val_process Mkt (delta_hedging N der matur) n w =
    (rn_price N der matur) n w"
unfolding delta_hedging_def
proof -
  define q where "q = (1 + r - d) / (u - d)"
  have "0 < q" and "q < 1" unfolding q_def using assms gt_param lt_param CRR_viable by auto
  note qprops = this
  define init where  "init = (prob_space.expectation N (discounted_value r (\<lambda>m. der) matur))"
  define X where "X = val_process Mkt (delta_hedging N der matur)"
  define V where "V = rn_price N der matur"
  define \<Delta> where "\<Delta> = delta_price N der matur"
  {
    fix n
    fix w
    have "n \<le> matur \<Longrightarrow> X n w = V n w"
    proof (induct n)
    case 0
    have v0: "V 0 \<in> borel_measurable (G 0)" using assms rn_price_borel_adapt "0.prems" qprops
      unfolding V_def q_def by auto
    have "X 0 w= init" using self_finance_init[of Mkt risk_free_asset "delta_pf N der matur" "integral\<^sup>L N (discounted_value r (\<lambda>m. der) matur)"]
        delta_pf_support
      unfolding  X_def init_def delta_hedging_def self_fin_delta_pf_def init_def
      by (metis finite_insert infinite_imp_nonempty infinite_super less_irrefl portfolio_def positive)
    also have "... = V 0 w" 
    proof -
      have "\<forall>x\<in>space N. real_cond_exp N (G 0) (discounted_value r (\<lambda>m. der) matur) x =
        integral\<^sup>L N (discounted_value r (\<lambda>m. der) matur)"
      proof (rule prob_space.trivial_subalg_cond_expect_eq)
        show "prob_space N" using assms qprops unfolding q_def
          by (simp add: bernoulli bernoulli_stream_def prob_space.prob_space_stream_space prob_space_measure_pmf)
        have "init_triv_filt M (stoch_proc_filt M geom_proc borel)"
        proof (rule infinite_cts_filtration.stoch_proc_filt_triv_init)
          show "borel_adapt_stoch_proc nat_filtration geom_proc" using geom_rand_walk_borel_adapted by simp
          show "infinite_cts_filtration p M nat_filtration" using bernoulli_nat_filtration[of M p] bernoulli psgt pslt
            by simp
        qed
        hence "init_triv_filt N (stoch_proc_filt M geom_proc borel)" using assms qprops
          filt_equiv_triv_init[of nat_filtration N] stock_filtration
          bernoulli_stream_equiv[of N] psgt pslt unfolding q_def by simp
        thus "subalgebra N (G 0)" and "sets (G 0) = {{}, space N}" using stock_filtration unfolding init_triv_filt_def
          filtration_def bot_nat_def by auto
        show "integrable N (discounted_value r (\<lambda>m. der) matur)"
        proof (rule bernoulli_discounted_integrable)
          show "der \<in> borel_measurable (nat_filtration matur)" using assms geom_rand_walk_borel_adapted
              measurable_from_subalg stoch_proc_subalg_nat_filt stock_filtration by blast
          show "N = bernoulli_stream q" using assms unfolding q_def by simp
          show "0 < q" "q < 1" using qprops by auto
        qed (simp add: acceptable_rate)
      qed
      hence "integral\<^sup>L N (discounted_value r (\<lambda>m. der) matur) =
        real_cond_exp N (G 0) (discounted_value r (\<lambda>m. der) matur) w" using bernoulli_stream_space[of N q]
        by (simp add: assms(1) q_def)
      also have "... = real_cond_exp N (stoch_proc_filt M geom_proc borel 0) (discounted_value r (\<lambda>m. der) matur) w"
        using stock_filtration by simp
      also have "... = real_cond_exp N (stoch_proc_filt N geom_proc borel 0) (discounted_value r (\<lambda>m. der) matur) w"
        using stoch_proc_filt_filt_equiv[of nat_filtration M N geom_proc]
          bernoulli_stream_equiv[of N] q_def qprops assms pslt psgt by auto
      also have "... = expl_cond_expect N (proj_stoch_proc geom_proc 0) (discounted_value r (\<lambda>m. der) matur) w"
      proof (rule bernoulli_cond_exp)
        show "N = bernoulli_stream q" using assms unfolding q_def by simp
        show "0 < q" "q < 1" using qprops by auto
        show "integrable N (discounted_value r (\<lambda>m. der) matur)"
        proof (rule bernoulli_discounted_integrable)
          show "der \<in> borel_measurable (nat_filtration matur)" using assms geom_rand_walk_borel_adapted
              measurable_from_subalg stoch_proc_subalg_nat_filt stock_filtration by blast
          show "N = bernoulli_stream q" using assms unfolding q_def by simp
          show "0 < q" "q < 1" using qprops by auto
        qed (simp add: acceptable_rate)
      qed
      finally show "init = V 0 w" unfolding init_def V_def rn_price_def by simp
    qed
    finally show "X 0 w = V 0 w" .
    next
      case (Suc n)
      hence "n < matur" by simp
      show ?case
      proof -
        have "X n w = V n w" using Suc by (simp add: Suc.hyps Suc.prems Suc_leD)
        have "0< 1+r" using acceptable_rate by simp
        let ?m = "matur - Suc n"
        have "matur -n = Suc ?m" by (simp add: Suc.prems Suc_diff_Suc Suc_le_lessD)
        have "(1+r) * V n w = q * V (Suc n) (pseudo_proj_True n w) + (1 - q) *V (Suc n) (pseudo_proj_False n w)"
          using rn_price_eq_ind qprops assms Suc q_def V_def by simp
        show "X (Suc n) w = V (Suc n) w"
        proof (cases "snth w n")
        case True
          hence pseq: "pseudo_proj_True (Suc n) w = pseudo_proj_True (Suc n) (spick w n True)"
            by (metis (mono_tags, lifting) pseudo_proj_True_stake_image spickI stake_Suc)
          have "X (Suc n) w = cls_val_process Mkt (delta_hedging N der matur) (Suc n) w"
            unfolding X_def delta_hedging_def self_fin_delta_pf_def using  delta_pf_portfolio
            unfolding self_financing_def
            by (metis less_irrefl positive self_finance_charact self_financingE)
          also have "... = geom_proc (Suc n) w * \<Delta> n w + (1 + r) * (X n w - geom_proc n w * \<Delta> n w)"
            using delta_hedging_cls_val_process unfolding X_def \<Delta>_def by simp
          also have "... = u * geom_proc n w * \<Delta> n w + (1 + r) * (X n w - geom_proc n w * \<Delta> n w)"
            using True geometric_process by simp
          also have "... = u * geom_proc n w * \<Delta> n w + (1 + r) * X n w - (1+r) * geom_proc n w * \<Delta> n w"
            by (simp add: right_diff_distrib)
          also have "... = (1+r) * X n w + geom_proc n w * \<Delta> n w * u - geom_proc n w * \<Delta> n w * (1 + r)"
            by (simp add: mult.commute mult.left_commute)
          also have "... = (1+r)* X n w + geom_proc n w * \<Delta> n w * (u - (1 + r))" by (simp add: right_diff_distrib)
          also have "... = (1+r) * X n w + geom_proc n w * (V (Suc n) (pseudo_proj_True n w) - V (Suc n) (pseudo_proj_False n w))/
            (geom_proc (Suc n) (spick w n True) - geom_proc (Suc n) (spick w n False)) * (u - (1 + r))"
            using Suc V_def by (simp add: \<Delta>_def delta_price_def geom_rand_walk_diff_induct)
          also have "... = (1+r) * X n w + geom_proc n w * ((V (Suc n) (pseudo_proj_True n w) - V (Suc n) (pseudo_proj_False n w))) /
            (geom_proc n w * (u - d)) * (u - (1 + r))"
          proof -
            have "geom_proc (Suc n) (spick w n True) - geom_proc (Suc n) (spick w n False) =
              geom_proc n w * (u - d)"
              by (simp add: geom_rand_walk_diff_induct)
            then show ?thesis by simp
          qed
          also have "... = (1+r) * X n w + ((V (Suc n) (pseudo_proj_True n w) - V (Suc n) (pseudo_proj_False n w)))* (u - (1 + r))/ (u-d)"
          proof -
            have "geom_proc n w \<noteq> 0"
              by (metis S0_positive down_lt_up down_positive geom_rand_walk_strictly_positive less_irrefl)
            then show ?thesis
              by simp
          qed
          also have "... = (1+r) * X n w + ((V (Suc n) (pseudo_proj_True n w) - V (Suc n) (pseudo_proj_False n w))* (1 - q))"
          proof -
            have "1 - q = 1 - (1 + r - d)/(u -d)" unfolding q_def by simp
            also have "... = (u - d)/(u - d) - (1 + r - d)/(u -d)" using down_lt_up by simp
            also have "... = (u - d - (1 + r - d))/(u - d)" using diff_divide_distrib[of "u - d" "1 + r -d"] by simp
            also have "... = (u - (1+r))/(u-d)" by simp
            finally have "1 - q = (u - (1+r))/(u-d)" .
            thus ?thesis by simp
          qed
          also have "... = (1+r) * X n w + (1 - q) * V (Suc n) (pseudo_proj_True n w) -
            (1 - q) * V (Suc n) (pseudo_proj_False n w)"
            by (simp add: mult.commute right_diff_distrib)
          also have "... = (1+r) * V n w + (1 - q) * V (Suc n) (pseudo_proj_True n w) -
            (1 - q) * V (Suc n) (pseudo_proj_False n w)" using \<open>X n w = V n w\<close> by simp
          also have "... = q * V (Suc n) (pseudo_proj_True n w) + (1 - q) * V (Suc n) (pseudo_proj_False n w) +
            (1 - q) * V (Suc n) (pseudo_proj_True n w) - (1 - q) * V (Suc n) (pseudo_proj_False n w)"
          using assms Suc rn_price_eq_ind[of N q n matur der w] \<open>n < matur\<close> qprops unfolding V_def q_def
            by simp
          also have "... = q * V (Suc n) (pseudo_proj_True n w) + (1 - q) * V (Suc n) (pseudo_proj_True n w)" by simp
          also have "... = V (Suc n) (pseudo_proj_True n w)"
            using distrib_right[of q "1 - q"  "V (Suc n) (pseudo_proj_True n w)"] by simp
          also have "... = V (Suc n) w"
          proof -
            have "V (Suc n) \<in> borel_measurable (G (Suc n))" unfolding V_def q_def
            proof (rule rn_price_borel_adapt)
              show "der \<in> borel_measurable (G matur)" using assms by simp
              show "N = bernoulli_stream q" using assms unfolding q_def by simp
              show "0 < q" and "q < 1" using qprops by auto
              show "Suc n \<le> matur" using Suc by simp
            qed
            hence "V (Suc n) (pseudo_proj_True n w) = V (Suc n) (pseudo_proj_True (Suc n) (pseudo_proj_True n w))"
              using  geom_proc_filt_info[of "V (Suc n)" "Suc n"] by simp
            also have "... = V (Suc n) (pseudo_proj_True (Suc n) w)" using True
              by (simp add: pseq spick_eq_pseudo_proj_True)
            also have "... = V (Suc n) w" using \<open>V (Suc n) \<in> borel_measurable (G (Suc n))\<close>
              geom_proc_filt_info[of "V (Suc n)" "Suc n"] by simp
            finally show ?thesis .
          qed
          finally show "X (Suc n) w = V (Suc n) w" .
        next
        case False
          hence pseq: "pseudo_proj_True (Suc n) w = pseudo_proj_True (Suc n) (spick w n False)" using filtration
            by (metis (full_types) pseudo_proj_True_def spickI stake_Suc)
          have "X (Suc n) w = cls_val_process Mkt (delta_hedging N der matur) (Suc n) w"
            unfolding X_def delta_hedging_def self_fin_delta_pf_def using  delta_pf_portfolio
            unfolding self_financing_def
            by (metis less_irrefl positive self_finance_charact self_financingE)
          also have "... = geom_proc (Suc n) w * \<Delta> n w + (1 + r) * (X n w - geom_proc n w * \<Delta> n w)"
            using delta_hedging_cls_val_process unfolding X_def \<Delta>_def by simp
          also have "... = d * geom_proc n w * \<Delta> n w + (1 + r) * (X n w - geom_proc n w * \<Delta> n w)"
            using False geometric_process by simp
          also have "... = d * geom_proc n w * \<Delta> n w + (1 + r) * X n w - (1+r) * geom_proc n w * \<Delta> n w"
            by (simp add: right_diff_distrib)
          also have "... = (1+r) * X n w + geom_proc n w * \<Delta> n w * d - geom_proc n w * \<Delta> n w * (1 + r)"
            by (simp add: mult.commute mult.left_commute)
          also have "... = (1+r)* X n w + geom_proc n w * \<Delta> n w * (d - (1 + r))" by (simp add: right_diff_distrib)
          also have "... = (1+r) * X n w + geom_proc n w * (V (Suc n) (pseudo_proj_True n w) - V (Suc n) (pseudo_proj_False n w))/
            (geom_proc (Suc n) (spick w n True) - geom_proc (Suc n) (spick w n False)) * (d - (1 + r))"
            using Suc V_def by (simp add: \<Delta>_def delta_price_def geom_rand_walk_diff_induct)
          also have "... = (1+r) * X n w + geom_proc n w * ((V (Suc n) (pseudo_proj_True n w) - V (Suc n) (pseudo_proj_False n w))) /
            (geom_proc n w * (u - d)) * (d - (1 + r))"
            by (simp add: geom_rand_walk_diff_induct)
          also have "... = (1+r) * X n w + ((V (Suc n) (pseudo_proj_True n w) - V (Suc n) (pseudo_proj_False n w)))* (d - (1 + r))/ (u-d)"
          proof -
            have "geom_proc n w \<noteq> 0"
              by (metis S0_positive down_lt_up down_positive geom_rand_walk_strictly_positive less_irrefl)
            then show ?thesis
              by simp
          qed
          also have "... = (1+r) * X n w + ((V (Suc n) (pseudo_proj_True n w) - V (Suc n) (pseudo_proj_False n w))* (-q))"
          proof -
            have "0-q = 0-(1 + r - d)/(u -d)" unfolding q_def by simp
            also have "... = (d - (1 + r))/(u -d)" by (simp add: minus_divide_left)
            finally have "0 - q = (d - (1+r))/(u-d)" .
            thus ?thesis by simp
          qed
          also have "... = (1+r) * X n w + (- V (Suc n) (pseudo_proj_True n w) * q + V (Suc n) (pseudo_proj_False n w)* q)"
            by (metis (no_types, hide_lams) add.inverse_inverse distrib_right minus_mult_commute minus_real_def mult_minus_left)
          also have "... = (1+r) * X n w - q * V (Suc n) (pseudo_proj_True n w) + q * V (Suc n) (pseudo_proj_False n w)" by simp
          also have "... = (1+r) * V n w -q * V (Suc n) (pseudo_proj_True n w) +
            q * V (Suc n) (pseudo_proj_False n w)" using \<open>X n w = V n w\<close> by simp
          also have "... = q * V (Suc n) (pseudo_proj_True n w) + (1 - q) * V (Suc n) (pseudo_proj_False n w) -
            q * V (Suc n) (pseudo_proj_True n w) + q * V (Suc n) (pseudo_proj_False n w)"
            using assms Suc rn_price_eq_ind[of N q n matur der w] \<open>n < matur\<close> qprops unfolding V_def q_def
            by simp
          also have "... = (1-q) * V (Suc n) (pseudo_proj_False n w) + q * V (Suc n) (pseudo_proj_False n w)" by simp
          also have "... = V (Suc n) (pseudo_proj_False n w)"
            using distrib_right[of q "1 - q"  "V (Suc n) (pseudo_proj_False n w)"] by simp
          also have "... = V (Suc n) w"
          proof -
            have "V (Suc n) \<in> borel_measurable (G (Suc n))" unfolding V_def q_def
            proof (rule rn_price_borel_adapt)
              show "der \<in> borel_measurable (G matur)" using assms by simp
              show "N = bernoulli_stream q" using assms unfolding q_def by simp
              show "0 < q" and "q < 1" using qprops by auto
              show "Suc n \<le> matur" using Suc by simp
            qed
            hence "V (Suc n) (pseudo_proj_False n w) = V (Suc n) (pseudo_proj_False (Suc n) (pseudo_proj_False n w))"
              using  geom_proc_filt_info'[of "V (Suc n)" "Suc n"] by simp
            also have "... = V (Suc n) (pseudo_proj_False (Suc n) w)" using False  spick_eq_pseudo_proj_False
              by (metis pseq pseudo_proj_True_imp_False)
            also have "... = V (Suc n) w" using \<open>V (Suc n) \<in> borel_measurable (G (Suc n))\<close>
              geom_proc_filt_info'[of "V (Suc n)" "Suc n"] by simp
            finally show ?thesis .
          qed
          finally show "X (Suc n) w = V (Suc n) w" .
        qed
      qed
    qed
  }
  thus "\<And>n w. n \<le> matur \<Longrightarrow>
           val_process Mkt (self_fin_delta_pf N der matur (integral\<^sup>L N (discounted_value r (\<lambda>m. der) matur))) n w =
            rn_price N der matur n w" by (simp add: X_def init_def V_def delta_hedging_def)
qed


lemma (in CRR_market_viable) delta_hedging_same_cash_flow:
  assumes "der \<in> borel_measurable (G matur)"
and "N = bernoulli_stream ((1 + r - d) / (u - d))"
  shows "cls_val_process Mkt (delta_hedging N der matur) matur w =
    der w"
proof  -
  define q where "q = (1 + r - d) / (u - d)"
  have "0 < q" and "q < 1" unfolding q_def using assms gt_param lt_param CRR_viable by auto
  note qprops = this
  have "cls_val_process Mkt (delta_hedging N der matur) matur w =
    val_process Mkt (delta_hedging N der matur) matur w" using self_financingE self_finance_charact
    unfolding delta_hedging_def self_fin_delta_pf_def
    by (metis delta_pf_portfolio mult_1s(1) mult_cancel_right not_real_square_gt_zero positive)
  also have "... = rn_price N der matur matur w" using delta_hedging_eq_derivative_price assms by simp
  also have "... = rn_rev_price N der matur 0 w" using rn_price_eq qprops assms
    unfolding rn_price_ind_def q_def by simp
  also have "... = der w" by simp
  finally show ?thesis .
qed

lemma (in CRR_market) delta_hedging_trading_strat:
  assumes "N = bernoulli_stream q"
  and "0 < q"
and "q < 1"
and "der \<in> borel_measurable (G matur)"
  shows "trading_strategy (delta_hedging N der matur)" unfolding delta_hedging_def
  by (simp add: assms self_fin_delta_pf_trad_strat)

lemma (in CRR_market) delta_hedging_self_financing:
  shows "self_financing Mkt (delta_hedging N der matur)" unfolding delta_hedging_def self_fin_delta_pf_def
proof (rule self_finance_charact)
  show "\<forall>n w. prices Mkt risk_free_asset (Suc n) w \<noteq> 0" using positive
    by (metis less_numeral_extra(3))
  show "portfolio (delta_pf N der matur)" using delta_pf_portfolio .
qed

lemma (in CRR_market_viable) delta_hedging_replicating:
  assumes "der \<in> borel_measurable (G matur)"
  and "N = bernoulli_stream ((1 + r - d) / (u - d))"
  shows "replicating_portfolio (delta_hedging N der matur) der matur"
unfolding replicating_portfolio_def
proof (intro conjI)
  define q where "q = (1 + r - d) / (u - d)"
  have "0 < q" and "q < 1" unfolding q_def using assms gt_param lt_param CRR_viable by auto
  note qprops = this
  let ?X = "(delta_hedging N der matur)"
  show "trading_strategy ?X" using delta_hedging_trading_strat qprops assms unfolding q_def by simp
  show "self_financing Mkt ?X" using delta_hedging_self_financing .
  show "stock_portfolio Mkt (delta_hedging N der matur)" unfolding delta_hedging_def self_fin_delta_pf_def
    stock_portfolio_def portfolio_def using stocks delta_pf_support
    by (smt Un_insert_right delta_pf_portfolio insert_commute portfolio_def self_finance_def
        self_finance_portfolio single_comp_support subset_insertI2 subset_singleton_iff
        sum_support_set sup_bot.right_neutral)
  show "AEeq M (cls_val_process Mkt (delta_hedging N der matur) matur) der"
    using delta_hedging_same_cash_flow assms by simp
qed

definition (in disc_equity_market) complete_market where
"complete_market \<longleftrightarrow> (\<forall>matur. \<forall> der\<in> borel_measurable (F matur). (\<exists>p. replicating_portfolio p der matur))"

lemma (in CRR_market_viable) CRR_market_complete:
  shows "complete_market" unfolding complete_market_def
proof (intro allI impI)
  fix matur::nat
  show "\<forall> der \<in> borel_measurable (G matur). (\<exists>p. replicating_portfolio p der matur)"
  proof
    fix der::"bool stream\<Rightarrow>real"
    assume "der \<in> borel_measurable (G matur)"
    define N where "N = bernoulli_stream ((1 + r - d) / (u - d))"
    hence "replicating_portfolio (delta_hedging N der matur) der matur" using delta_hedging_replicating
      \<open>der \<in> borel_measurable (G matur)\<close> by simp
    thus "\<exists>pf. replicating_portfolio pf der matur" by auto
  qed
qed


lemma subalgebras_filtration:
  assumes "filtration M F"
and "\<forall>t. subalgebra (F t) (G t)"
and "\<forall> s t. s \<le> t \<longrightarrow> subalgebra (G t) (G s)"
shows "filtration M G" unfolding filtration_def
proof (intro conjI allI impI)
  {
    fix t
    have "subalgebra (F t) (G t)" using assms by simp
    moreover have "subalgebra M (F t)" using assms unfolding filtration_def by simp
    ultimately show "subalgebra M (G t)" by (metis subalgebra_def subsetCE subsetI)
  }
  {
    fix s t::'b
    assume "s \<le> t"
    thus "subalgebra (G t) (G s)" using assms by simp
  }
qed



lemma subfilt_filt_equiv:
  assumes "filt_equiv F M N"
and "\<forall> t. subalgebra (F t) (G t)"
and "\<forall> s t. s \<le> t \<longrightarrow> subalgebra (G t) (G s)"
shows "filt_equiv G M N" unfolding filt_equiv_def
proof (intro conjI)
  show "sets M = sets N" using assms unfolding filt_equiv_def by simp
  show "filtration M G" using assms subalgebras_filtration[of M F G] unfolding filt_equiv_def by simp
  show "\<forall>t A. A \<in> sets (G t) \<longrightarrow> (emeasure M A = 0) = (emeasure N A = 0)"
  proof (intro allI ballI impI)
    fix t
    fix A
    assume "A\<in> sets (G t)"
    hence "A \<in> sets (F t)" using assms unfolding subalgebra_def by auto
    thus "(emeasure M A = 0) = (emeasure N A = 0)" using assms unfolding filt_equiv_def by simp
  qed
qed

lemma (in CRR_market_viable) CRR_market_fair_price:
  assumes "pyf\<in> borel_measurable (G matur)"
  shows "fair_price Mkt
    (\<Sum> w\<in> range (pseudo_proj_True matur). (prod (prob_component ((1 + r - d) / (u - d)) w) {0..<matur}) *
      ((discounted_value r (\<lambda>m. pyf) matur) w))
    pyf matur"
proof -
  define dpf where "dpf = (discounted_value r (\<lambda>m. pyf) matur)"
  define q where "q = (1 + r - d) / (u - d)"
  have "\<exists>pf. replicating_portfolio pf pyf matur" using CRR_market_complete assms unfolding complete_market_def by simp
  from this obtain pf where "replicating_portfolio pf pyf matur" by auto note pfprop = this
  define N where "N = bernoulli_stream ((1 + r - d) / (u - d))"
  have "fair_price Mkt (integral\<^sup>L N dpf) pyf matur" unfolding dpf_def
  proof (rule replicating_expectation_finite)
    show "risk_neutral_prob N" using assms risk_neutral_iff
      using CRR_viable gt_param lt_param N_def by blast
    have "filt_equiv nat_filtration M N"  using bernoulli_stream_equiv[of N "(1+r-d)/(u-d)"]
        assms gt_param lt_param CRR_viable psgt pslt N_def by simp
    thus "filt_equiv G M N" using subfilt_filt_equiv
      using Filtration.filtration_def filtration geom_rand_walk_borel_adapted
        stoch_proc_subalg_nat_filt stock_filtration by blast
    show "pyf \<in> borel_measurable (G matur)" using assms by simp
    show "viable_market Mkt" using CRR_viable by simp
    have "infinite_cts_filtration p M nat_filtration" using bernoulli_nat_filtration[of M p] bernoulli psgt pslt
      by simp
    thus "sets (G 0) = {{}, space M}" using stock_filtration
      infinite_cts_filtration.stoch_proc_filt_triv_init[of p M nat_filtration geom_proc]
      geom_rand_walk_borel_adapted bot_nat_def unfolding init_triv_filt_def by simp
    show "replicating_portfolio pf pyf matur" using pfprop .
    show "\<forall>n. \<forall>asset\<in>support_set pf. finite (prices Mkt asset n ` space M)"
    proof (intro allI ballI)
      fix n
      fix asset
      assume "asset \<in> support_set pf"
      hence "prices Mkt asset n \<in> borel_measurable (G n)" using readable pfprop
        unfolding  replicating_portfolio_def stock_portfolio_def adapt_stoch_proc_def by auto
      hence "prices Mkt asset n \<in> borel_measurable (nat_filtration n)" using stock_filtration
        stoch_proc_subalg_nat_filt geom_rand_walk_borel_adapted
        measurable_from_subalg[of "nat_filtration n" "G n" "prices Mkt asset n" borel]
        unfolding adapt_stoch_proc_def by auto
      thus "finite (prices Mkt asset n ` space M)" using nat_filtration_vimage_finite[of "prices Mkt asset n"] by simp
    qed
    show "\<forall>n. \<forall>asset\<in>support_set pf. finite (pf asset n ` space M)"
    proof (intro allI ballI)
      fix n
      fix asset
      assume "asset \<in> support_set pf"
      hence "pf asset n \<in> borel_measurable (G n)" using pfprop predict_imp_adapt[of "pf asset"]
        unfolding replicating_portfolio_def trading_strategy_def adapt_stoch_proc_def by auto
      hence "pf asset n \<in> borel_measurable (nat_filtration n)" using stock_filtration
        stoch_proc_subalg_nat_filt geom_rand_walk_borel_adapted
        measurable_from_subalg[of "nat_filtration n" "G n" "pf asset n" borel]
        unfolding adapt_stoch_proc_def by auto
      thus "finite (pf asset n ` space M)" using nat_filtration_vimage_finite[of "pf asset n"] by simp
    qed
  qed
  moreover have "integral\<^sup>L N dpf =
    (\<Sum> w\<in> range (pseudo_proj_True matur). (prod (prob_component q w) {0..<matur}) * (dpf w))"
  proof (rule infinite_cts_filtration.expect_prob_comp)
    show "infinite_cts_filtration q N nat_filtration" using  assms  pslt psgt
        bernoulli_nat_filtration unfolding q_def using gt_param lt_param CRR_viable N_def by auto
    have "dpf \<in> borel_measurable (G matur)" using assms discounted_measurable[of pyf "G matur"]
      unfolding dpf_def by simp
    thus "dpf \<in> borel_measurable (nat_filtration matur)" using stock_filtration
        stoch_proc_subalg_nat_filt geom_rand_walk_borel_adapted
        measurable_from_subalg[of "nat_filtration matur" "G matur" dpf]
      unfolding adapt_stoch_proc_def by auto
  qed
  ultimately show ?thesis unfolding dpf_def q_def by simp
qed

end