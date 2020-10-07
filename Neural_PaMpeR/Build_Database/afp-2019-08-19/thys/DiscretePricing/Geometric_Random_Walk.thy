theory Geometric_Random_Walk imports Infinite_Coin_Toss_Space

begin

section \<open>Geometric random walk\<close>
text \<open>A geometric random walk is a stochastic process that can, at each time, move upwards or downwards,
depending on the outcome of a coin toss.\<close>

fun (in infinite_coin_toss_space) geom_rand_walk:: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> (nat \<Rightarrow> bool stream \<Rightarrow> real)" where
  base: "(geom_rand_walk u d v) 0 = (\<lambda>w. v)"|
  step: "(geom_rand_walk u d v) (Suc n)  = (\<lambda>w. ((\<lambda>True \<Rightarrow> u | False \<Rightarrow> d) (snth w n)) * (geom_rand_walk u d v) n w)"


locale prob_grw = infinite_coin_toss_space +
  fixes geom_proc::"nat \<Rightarrow> bool stream \<Rightarrow> real" and u::real and d::real and init::real
  assumes geometric_process:"geom_proc = geom_rand_walk u d init"

lemma (in prob_grw) geom_rand_walk_borel_measurable:
shows "(geom_proc n) \<in> borel_measurable M"
proof (induct n)
case (Suc n)
  thus "geom_proc (Suc n) \<in> borel_measurable M"
  proof -
    have "geom_rand_walk u d init n \<in> borel_measurable M" using Suc geometric_process by simp
    moreover have "(\<lambda>w. ((\<lambda>True \<Rightarrow> u | False \<Rightarrow> d) (snth w n))) \<in> borel_measurable M"
    proof -
      have "(\<lambda>w. snth w n) \<in> measurable M (measure_pmf (bernoulli_pmf p))" by (simp add: bernoulli measurable_snth_count_space)
      moreover have "(\<lambda>True \<Rightarrow> u | False \<Rightarrow> d) \<in> borel_measurable (measure_pmf (bernoulli_pmf p))" by simp
      ultimately show ?thesis by (simp add: measurable_comp)
    qed
    ultimately show ?thesis by (simp add:borel_measurable_times geometric_process)
  qed
  next
  show "random_variable borel (geom_proc 0)" using geometric_process by simp
qed



lemma (in prob_grw) geom_rand_walk_pseudo_proj_True:
shows "geom_proc n = geom_proc n \<circ> pseudo_proj_True n"
proof (induct n)
case (Suc n)
  let ?tf = "(\<lambda>True \<Rightarrow> u | False \<Rightarrow> d)"
  {
    fix w
    have "geom_proc (Suc n) w  =  ?tf  (snth w n) * geom_proc n w"
      using geom_rand_walk.simps(2) geometric_process by simp
    also have "... = ?tf (snth (pseudo_proj_True (Suc n) w) n) * geom_proc n w"
      by (metis  lessI pseudo_proj_True_stake stake_nth)
    also have "... = ?tf (snth (pseudo_proj_True (Suc n) w) n) * geom_proc n (pseudo_proj_True n w)"
      using Suc geometric_process by (metis comp_apply)
    also have "... = ?tf (snth (pseudo_proj_True (Suc n) w) n) * geom_proc n (pseudo_proj_True (Suc n) w)"
      using geometric_process by (metis Suc.hyps comp_apply pseudo_proj_True_proj_Suc)
    also have "... = geom_proc (Suc n) (pseudo_proj_True (Suc n) w)" using geometric_process by simp
    finally have "geom_proc (Suc n) w  = geom_proc (Suc n) (pseudo_proj_True (Suc n) w)" .
  }
  thus "geom_proc (Suc n) = geom_proc (Suc n) \<circ> (pseudo_proj_True  (Suc n))" using geometric_process by auto
next
  show "geom_proc 0 = geom_proc 0 \<circ> pseudo_proj_True 0" using geometric_process by auto
qed

lemma (in prob_grw) geom_rand_walk_pseudo_proj_False:
shows "geom_proc n = geom_proc n \<circ> pseudo_proj_False n"
proof (induct n)
case (Suc n)
  let ?tf = "(\<lambda>True \<Rightarrow> u | False \<Rightarrow> d)"
  {
    fix w
    have "geom_proc (Suc n) w  =  ?tf  (snth w n) * geom_proc n w"
      using geom_rand_walk.simps(2) geometric_process by simp
    also have "... = ?tf (snth (pseudo_proj_False (Suc n) w) n) * geom_proc n w"
      by (metis  lessI pseudo_proj_False_stake stake_nth)
    also have "... = ?tf (snth (pseudo_proj_False (Suc n) w) n) * geom_proc n (pseudo_proj_False n w)"
      using Suc geometric_process by (metis comp_apply)
    also have "... = ?tf (snth (pseudo_proj_False (Suc n) w) n) * geom_proc n (pseudo_proj_True n (pseudo_proj_False n w))"
      using  geometric_process by (metis geom_rand_walk_pseudo_proj_True o_apply)
    also have "... = ?tf (snth (pseudo_proj_False (Suc n) w) n) * geom_proc n (pseudo_proj_True n (pseudo_proj_False (Suc n) w))"
      unfolding pseudo_proj_True_def pseudo_proj_False_def
      by (metis pseudo_proj_False_def pseudo_proj_False_stake pseudo_proj_True_def pseudo_proj_True_proj_Suc)
    also have "... = ?tf (snth (pseudo_proj_False (Suc n) w) n) * geom_proc n (pseudo_proj_False (Suc n) w)"
      using geometric_process by (metis geom_rand_walk_pseudo_proj_True o_apply)
    also have "... = geom_proc (Suc n) (pseudo_proj_False (Suc n) w)" using geometric_process by simp
    finally have "geom_proc (Suc n) w  = geom_proc (Suc n) (pseudo_proj_False (Suc n) w)" .
  }
  thus "geom_proc (Suc n) = geom_proc (Suc n) \<circ> (pseudo_proj_False  (Suc n))" using geometric_process by auto
next
  show "geom_proc 0 = geom_proc 0 \<circ> pseudo_proj_False 0" using geometric_process by auto
qed



lemma (in prob_grw) geom_rand_walk_borel_adapted:
  shows "borel_adapt_stoch_proc nat_filtration geom_proc"
unfolding adapt_stoch_proc_def
proof (auto simp add:nat_discrete_filtration)
  fix n
  show "geom_proc n \<in> borel_measurable (nat_filtration n)"
  proof -
    have "geom_proc n \<in> borel_measurable (nat_filtration n)"
    proof (rule nat_filtration_comp_measurable)
      show "geom_proc n \<in> borel_measurable M"
        by (simp add: geom_rand_walk_borel_measurable)
      show "geom_proc n \<circ> pseudo_proj_True n = geom_proc n"
        using geom_rand_walk_pseudo_proj_True  by simp
    qed
    then show ?thesis by simp
  qed
qed


lemma (in prob_grw) grw_succ_img:
  assumes "(geom_proc n) -` {x} \<noteq> {}"
  shows "(geom_proc (Suc n)) ` ((geom_proc n) -` {x}) = {u*x, d*x}"
proof
  have "\<exists> w. geom_proc n w = x" using assms by auto
  from this obtain w where "geom_proc n w = x" by auto
  let ?wT = "spick w n True"
  let ?wF = "spick w n False"
  have bel: "(?wT \<in> (geom_proc n) -` {x}) \<and> (?wF \<in> (geom_proc n) -` {x})"
    by (metis \<open>geom_proc n w = x\<close> geom_rand_walk_pseudo_proj_True o_def
        pseudo_proj_True_stake_image spickI vimage_singleton_eq)
  have "geom_proc (Suc n) ?wT = u*x"
  proof -
    have "x = geom_rand_walk u d init n (spick w n True)"
      by (metis \<open>geom_proc n w = x\<close> comp_apply geom_rand_walk_pseudo_proj_True geometric_process pseudo_proj_True_stake_image spickI)
    then show ?thesis
      by (simp add: geometric_process spickI)
  qed
  moreover have "geom_proc (Suc n) ?wF = d*x"
  proof -
    have "x = geom_rand_walk u d init n (spick w n False)"
      by (metis \<open>geom_proc n w = x\<close> comp_apply geom_rand_walk_pseudo_proj_True geometric_process pseudo_proj_True_stake_image spickI)
    then show ?thesis
      by (simp add: geometric_process spickI)
  qed
  ultimately show "{u*x, d*x} \<subseteq> (geom_proc (Suc n)) ` ((geom_proc n) -` {x})" using bel
    by (metis empty_subsetI insert_subset rev_image_eqI)
  have "\<forall>w \<in> (geom_proc n) -` {x}. geom_proc (Suc n) w \<in> {u*x, d*x}"
  proof
    fix w
    assume "w \<in> (geom_proc n) -` {x}"
    have dis: "((snth w (Suc n)) = True) \<or> (snth w (Suc n) = False)" by simp
    show "geom_proc (Suc n) w \<in> {u*x, d*x}"
    proof -
      have "geom_proc n w = x"
        by (metis \<open>w \<in> geom_proc n -` {x}\<close> vimage_singleton_eq)
      then have "geom_rand_walk u d init n w = x"
        using geometric_process by blast
      then show ?thesis
        by (simp add: case_bool_if geometric_process)
    qed
  qed
  thus "(geom_proc (Suc n)) ` ((geom_proc n) -` {x}) \<subseteq> {u*x, d*x}" by auto
qed

lemma (in prob_grw) geom_rand_walk_strictly_positive:
  assumes "0 < init"
  and "0 < d"
  and "d < u"
  shows "\<forall> n w. 0 < geom_proc n w"
proof (intro allI)
  fix n
  fix w
  show "0 < geom_proc n w"
  proof (induct n)
  case 0 thus ?case using assms geometric_process by simp
  next
  case (Suc n)
    thus ?case
    proof (cases "snth w n")
    case True
      hence "geom_proc (Suc n) w = u * geom_proc n w" using geom_rand_walk.simps geometric_process by simp
      also have "... > 0" using Suc assms  by simp
      finally show ?thesis .
    next
    case False
      hence "geom_proc (Suc n) w = d * geom_proc n w" using geom_rand_walk.simps geometric_process by simp
      also have "... > 0" using Suc assms by simp
      finally show ?thesis .
    qed
  qed
qed


lemma (in prob_grw) geom_rand_walk_diff_induct:
  shows "\<And>w. (geom_proc (Suc n) (spick w n True) - geom_proc (Suc n) (spick w n False)) = (geom_proc n w * (u - d))"
proof -
  fix w
  have "geom_proc (Suc n) (spick w n True) = u * geom_proc n w"
  proof -
    have "snth (spick w n True) n = True" by (simp add: spickI)
    hence "(\<lambda>w. (case w !! n of True \<Rightarrow> u | False \<Rightarrow> d)) (spick w n True) = u" by simp
    thus ?thesis using geometric_process geom_rand_walk.simps(2)[of u d init n]
      by (metis comp_apply geom_rand_walk_pseudo_proj_True pseudo_proj_True_def spickI)
  qed
  moreover have "geom_proc (Suc n) (spick w n False) = d * geom_proc n w"
  proof -
    have "snth (spick w n False) n = False" by (simp add: spickI)
    hence "(\<lambda>w. (case w !! n of True \<Rightarrow> u | False \<Rightarrow> d)) (spick w n False) = d" by simp
    thus ?thesis using geometric_process geom_rand_walk.simps(2)[of u d init n]
      by (metis comp_apply geom_rand_walk_pseudo_proj_True pseudo_proj_True_def spickI)
  qed
  ultimately show "(geom_proc (Suc n) (spick w n True) - geom_proc (Suc n) (spick w n False)) = (geom_proc n w * (u - d))"
    by (simp add:field_simps)
qed



end