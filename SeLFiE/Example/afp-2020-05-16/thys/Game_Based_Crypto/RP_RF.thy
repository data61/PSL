(* Title: RP_RF.thy
  Author: Andreas Lochbihler, ETH Zurich *)

subsection \<open>The random-permutation random-function switching lemma\<close>

theory RP_RF imports
  Pseudo_Random_Function
  Pseudo_Random_Permutation
  CryptHOL.GPV_Bisim
begin

lemma rp_resample:
  assumes "B \<subseteq> A \<union> C" "A \<inter> C = {}" "C \<subseteq> B" and finB: "finite B"
  shows "bind_spmf (spmf_of_set B) (\<lambda>x. if x \<in> A then spmf_of_set C else return_spmf x) = spmf_of_set C"
proof(cases "C = {} \<or> A \<inter> B = {}")
  case False
  define A' where "A' \<equiv> A \<inter> B"
  from False have C: "C \<noteq> {}" and A': "A' \<noteq> {}" by(auto simp add: A'_def)
  have B: "B = A' \<union> C" using assms by(auto simp add: A'_def)
  with finB have finA: "finite A'" and finC: "finite C" by simp_all
  from assms have A'C: "A' \<inter> C = {}" by(auto simp add: A'_def)
  have "bind_spmf (spmf_of_set B) (\<lambda>x. if x \<in> A then spmf_of_set C else return_spmf x) = 
        bind_spmf (spmf_of_set B) (\<lambda>x. if x \<in> A' then spmf_of_set C else return_spmf x)"
    by(rule bind_spmf_cong[OF refl])(simp add: set_spmf_of_set finB A'_def)
  also have "\<dots> = spmf_of_set C" (is "?lhs = ?rhs")
  proof(rule spmf_eqI)
    fix i
    have "(\<Sum>x\<in>C. spmf (if x \<in> A' then spmf_of_set C else return_spmf x) i) = indicator C i" using finA finC 
      by(simp add: disjoint_notin1[OF A'C] indicator_single_Some sum_mult_indicator[of C "\<lambda>_. 1 :: real" "\<lambda>_. _" "\<lambda>x. x", simplified] split: split_indicator cong: conj_cong sum.cong)
    then show "spmf ?lhs i = spmf ?rhs i" using B finA finC A'C C A'
      by(simp add: spmf_bind integral_spmf_of_set sum_Un spmf_of_set field_simps)(simp add: field_simps card_Un_disjoint)
  qed
  finally show ?thesis .
qed(use assms in \<open>auto 4 3 cong: bind_spmf_cong_simp simp add: subsetD bind_spmf_const spmf_of_set_empty disjoint_notin1 intro!: arg_cong[where f=spmf_of_set]\<close>)

locale rp_rf =
  rp: random_permutation A +
  rf: random_function "spmf_of_set A"
  for A :: "'a set"
  +
  assumes finite_A: "finite A"
  and nonempty_A: "A \<noteq> {}"
begin

type_synonym 'a' adversary = "(bool, 'a', 'a') gpv"
  
definition game :: "bool \<Rightarrow> 'a adversary \<Rightarrow> bool spmf" where
  "game b \<A> = run_gpv (if b then rp.random_permutation else rf.random_oracle) \<A> Map.empty"
  
abbreviation prp_game :: "'a adversary \<Rightarrow> bool spmf" where "prp_game \<equiv> game True"
abbreviation prf_game :: "'a adversary \<Rightarrow> bool spmf" where "prf_game \<equiv> game False"
  
definition advantage :: "'a adversary \<Rightarrow> real" where
  "advantage \<A> = \<bar>spmf (prp_game \<A>) True - spmf (prf_game \<A>) True\<bar>"
  
lemma advantage_nonneg: "0 \<le> advantage \<A>" by(simp add: advantage_def)

lemma advantage_le_1: "advantage \<A> \<le> 1"
  by(auto simp add: advantage_def intro!: abs_leI)(metis diff_0_right diff_left_mono order_trans pmf_le_1 pmf_nonneg) +

context includes \<I>.lifting begin
lift_definition \<I> :: "('a, 'a) \<I>" is "(\<lambda>x. if x \<in> A then A else {})" .
lemma outs_\<I>_\<I> [simp]: "outs_\<I> \<I> = A" by transfer auto
lemma responses_\<I>_\<I> [simp]: "responses_\<I> \<I> x = (if x \<in> A then A else {})" by transfer simp
lifting_update \<I>.lifting
lifting_forget \<I>.lifting
end

lemma rp_rf:
  assumes bound: "interaction_any_bounded_by \<A> q"
    and lossless: "lossless_gpv \<I> \<A>"
    and WT: "\<I> \<turnstile>g \<A> \<surd>"
  shows "advantage \<A> \<le> q * q / card A"
  including lifting_syntax  
proof -
  let ?run = "\<lambda>b. exec_gpv (if b then rp.random_permutation else rf.random_oracle) \<A> Map.empty"
  define rp_bad :: "bool \<times> ('a \<rightharpoonup> 'a) \<Rightarrow> 'a \<Rightarrow> ('a \<times> (bool \<times> ('a \<rightharpoonup> 'a))) spmf"
    where "rp_bad = (\<lambda>(bad, \<sigma>) x. case \<sigma> x of Some y \<Rightarrow> return_spmf (y, (bad, \<sigma>))
      | None \<Rightarrow> bind_spmf (spmf_of_set A) (\<lambda>y. if y \<in> ran \<sigma> then map_spmf (\<lambda>y'. (y', (True, \<sigma>(x \<mapsto> y')))) (spmf_of_set (A - ran \<sigma>)) else return_spmf (y, (bad, (\<sigma>(x \<mapsto> y))))))"
  have rp_bad_simps: "rp_bad (bad, \<sigma>) x = (case \<sigma> x of Some y \<Rightarrow> return_spmf (y, (bad, \<sigma>))
      | None \<Rightarrow> bind_spmf (spmf_of_set A) (\<lambda>y. if y \<in> ran \<sigma> then map_spmf (\<lambda>y'. (y', (True, \<sigma>(x \<mapsto> y')))) (spmf_of_set (A - ran \<sigma>)) else return_spmf (y, (bad, (\<sigma>(x \<mapsto> y))))))"
    for bad \<sigma> x by(simp add: rp_bad_def)

  let ?S = "rel_prod2 (=)"
  define init :: "bool \<times> ('a \<rightharpoonup> 'a)" where "init = (False, Map.empty)"
  have rp: "rp.random_permutation = (\<lambda>\<sigma> x. case \<sigma> x of Some y \<Rightarrow> return_spmf (y, \<sigma>) 
    | None \<Rightarrow> bind_spmf (bind_spmf (spmf_of_set A) (\<lambda>y. if y \<in> ran \<sigma> then spmf_of_set (A - ran \<sigma>) else return_spmf y)) (\<lambda>y. return_spmf (y, \<sigma>(x \<mapsto> y))))"
    by(subst rp_resample)(auto simp add: finite_A rp.random_permutation_def[abs_def])
  have [transfer_rule]: "(?S ===> (=) ===> rel_spmf (rel_prod (=) ?S)) rp.random_permutation rp_bad"
    unfolding rp rp_bad_def
    by(auto simp add: rel_fun_def map_spmf_conv_bind_spmf split: option.split intro!: rel_spmf_bind_reflI)
  have [transfer_rule]: "?S Map.empty init" by(simp add: init_def)
  have "spmf (prp_game \<A>) True = spmf (run_gpv rp_bad \<A> init) True"
    unfolding vimage_def game_def if_True by transfer_prover
  moreover {
    define collision :: "('a \<rightharpoonup> 'a) \<Rightarrow> bool" where "collision m \<longleftrightarrow> \<not> inj_on m (dom m)" for m
    have [simp]: "\<not> collision Map.empty" by(simp add: collision_def)
    have [simp]: "\<lbrakk> collision m; m x = None \<rbrakk> \<Longrightarrow> collision (m(x := y))" for m x y
      by(auto simp add: collision_def fun_upd_idem dom_minus fun_upd_image dest: inj_on_fun_updD)
    have collision_map_updI: "\<lbrakk> m x = None; y \<in> ran m \<rbrakk> \<Longrightarrow> collision (m(x \<mapsto> y))" for m x y
      by(auto simp add: collision_def ran_def intro: rev_image_eqI)
    have collision_map_upd_iff: "\<not> collision m \<Longrightarrow> collision (m(x \<mapsto> y)) \<longleftrightarrow> y \<in> ran m \<and> m x \<noteq> Some y" for m x y
      by(auto simp add: collision_def ran_def fun_upd_idem intro: inj_on_fun_updI rev_image_eqI dest: inj_on_eq_iff)
  
    let ?bad1 = "collision" and ?bad2 = "fst"
      and ?X = "\<lambda>\<sigma>1 (bad, \<sigma>2). \<sigma>1 = \<sigma>2 \<and> \<not> collision \<sigma>1 \<and> \<not> bad"
      and ?I1 = "\<lambda>\<sigma>1. dom \<sigma>1 \<subseteq> A \<and> ran \<sigma>1 \<subseteq> A"
      and ?I2 = "\<lambda>(bad, \<sigma>2). dom \<sigma>2 \<subseteq> A \<and> ran \<sigma>2 \<subseteq> A"
    let ?X_bad = "\<lambda>\<sigma>1 s2. ?I1 \<sigma>1 \<and> ?I2 s2"
    have [simp]: "\<I> \<turnstile>c rf.random_oracle s1 \<surd>" if "ran s1 \<subseteq> A" for s1 using that
      by(intro WT_calleeI)(auto simp add: rf.random_oracle_def[abs_def] finite_A nonempty_A ran_def split: option.split_asm)
    have [simp]: "callee_invariant_on rf.random_oracle ?I1 \<I>"
      by(unfold_locales)(auto simp add: rf.random_oracle_def finite_A split: option.split_asm)
    then interpret rf: callee_invariant_on rf.random_oracle ?I1 \<I> .
    have [simp]: "\<I> \<turnstile>c rp_bad s2 \<surd> " if "ran (snd s2) \<subseteq> A" for s2 using that
      by(intro WT_calleeI)(auto simp add: rp_bad_def finite_A split: prod.split_asm option.split_asm if_split_asm intro: ranI)
    have [simp]: "callee_invariant_on rf.random_oracle (\<lambda>\<sigma>1. ?bad1 \<sigma>1 \<and> ?I1 \<sigma>1) \<I>"
      by(unfold_locales)(clarsimp simp add: rf.random_oracle_def finite_A  split: option.split_asm)+
    have [simp]: "callee_invariant_on rp_bad (\<lambda>s2. ?I2 s2) \<I>"
      by(unfold_locales)(auto 4 3 simp add: rp_bad_simps finite_A split: option.splits if_split_asm iff del: domIff)
    have [simp]: "callee_invariant_on rp_bad (\<lambda>s2. ?bad2 s2 \<and> ?I2 s2) \<I>"
      by(unfold_locales)(auto 4 3 simp add: rp_bad_simps finite_A split: option.splits if_split_asm iff del: domIff)
    have [simp]: "\<I> \<turnstile>c rp_bad (bad, \<sigma>2) \<surd>" if "ran \<sigma>2 \<subseteq> A" for bad \<sigma>2 using that
      by(intro WT_calleeI)(auto simp add: rp_bad_def finite_A nonempty_A ran_def split: option.split_asm if_split_asm)
    have [simp]: "lossless_spmf (rp_bad (b, \<sigma>2) x)" if "x \<in> A" "dom \<sigma>2 \<subseteq> A" "ran \<sigma>2 \<subseteq> A" for b \<sigma>2 x
      using finite_A that unfolding rp_bad_def
      by(clarsimp simp add: nonempty_A dom_subset_ran_iff eq_None_iff_not_dom split: option.split)
    have "rel_spmf (\<lambda>(b1, \<sigma>1) (b2, state2). (?bad1 \<sigma>1 \<longleftrightarrow> ?bad2 state2) \<and> (if ?bad2 state2 then ?X_bad \<sigma>1 state2 else b1 = b2 \<and> ?X \<sigma>1 state2))
            ((if False then rp.random_permutation else rf.random_oracle) s1 x) (rp_bad s2 x)"
      if "?X s1 s2" "x \<in> outs_\<I> \<I>" "?I1 s1" "?I2 s2" for s1 s2 x using that finite_A
      by(auto split!: option.split simp add: rf.random_oracle_def rp_bad_def rel_spmf_return_spmf1 collision_map_updI dom_subset_ran_iff eq_None_iff_not_dom collision_map_upd_iff intro!: rel_spmf_bind_reflI)
    with _ _ have "rel_spmf
       (\<lambda>(b1, \<sigma>1) (b2, state2). (?bad1 \<sigma>1 \<longleftrightarrow> ?bad2 state2) \<and> (if ?bad2 state2 then ?X_bad \<sigma>1 state2 else b1 = b2 \<and> ?X \<sigma>1 state2))
       (?run False) (exec_gpv rp_bad \<A> init)"
      by(rule exec_gpv_oracle_bisim_bad_invariant[where \<I> = \<I> and ?I1.0 = "?I1" and ?I2.0="?I2"])(auto simp add: init_def WT lossless finite_A nonempty_A)
   then have "\<bar>spmf (map_spmf fst (?run False)) True - spmf (run_gpv rp_bad \<A> init) True\<bar> \<le> spmf (map_spmf (?bad1 \<circ> snd) (?run False)) True"
      unfolding spmf_conv_measure_spmf measure_map_spmf vimage_def
      by(intro fundamental_lemma[where ?bad2.0="\<lambda>(_, s2). ?bad2 s2"])(auto simp add: split_def elim: rel_spmf_mono)
    also have "ennreal \<dots> \<le> ennreal (q / card A) * (enat q)" unfolding if_False using bound _ _ _ _ _ _ _ WT
      by(rule rf.interaction_bounded_by_exec_gpv_bad_count[where count="\<lambda>s. card (dom s)"])
        (auto simp add: rf.random_oracle_def finite_A nonempty_A card_insert_if finite_subset[OF _ finite_A] map_spmf_conv_bind_spmf[symmetric] spmf.map_comp o_def collision_map_upd_iff map_mem_spmf_of_set card_gt_0_iff card_mono field_simps Int_absorb2 intro: card_ran_le_dom[OF finite_subset, OF _ finite_A, THEN order_trans] split: option.splits)
    hence "spmf (map_spmf (?bad1 \<circ> snd) (?run False)) True \<le> q * q / card A"
      by(simp add: ennreal_of_nat_eq_real_of_nat ennreal_times_divide ennreal_mult''[symmetric])
    finally have "\<bar>spmf (run_gpv rp_bad \<A> init) True - spmf (run_gpv rf.random_oracle \<A> Map.empty) True\<bar> \<le> q * q / card A"
      by simp }
  ultimately show ?thesis by(simp add: advantage_def game_def)
qed

end

end
