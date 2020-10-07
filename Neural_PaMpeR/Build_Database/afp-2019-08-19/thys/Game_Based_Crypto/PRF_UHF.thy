(* Title: PRF_UHF.thy 
  Author: Bhargav Bhatt, ETH Zurich
  Author: Andreas Lochbihler, ETH Zurich *)

subsection \<open>Extending the input length of a PRF using a universal hash function\<close>

text \<open> This example is taken from \cite[\S 4.2]{Shoup2004IACR}.\<close>

theory PRF_UHF imports
  CryptHOL.GPV_Bisim
  Pseudo_Random_Function
begin

locale "hash" =
  fixes seed_gen :: "'seed spmf"
  and "hash" :: "'seed \<Rightarrow> 'domain \<Rightarrow> 'range"
begin

definition game_hash :: " 'domain \<Rightarrow> 'domain \<Rightarrow> bool spmf"
where 
 "game_hash w w' = do {
    seed \<leftarrow> seed_gen;
    return_spmf (hash seed w = hash seed w' \<and> w \<noteq> w')
  }"

definition game_hash_set :: "'domain set \<Rightarrow> bool spmf"
where 
  "game_hash_set W = do {
     seed  \<leftarrow> seed_gen;
     return_spmf (\<not> inj_on (hash seed) W)
   }"

definition \<epsilon>_uh :: "real"
where "\<epsilon>_uh  = (SUP w w'. spmf (game_hash w w') True)"

lemma \<epsilon>_uh_nonneg : "\<epsilon>_uh \<ge> 0"
by(auto 4 3 intro!: cSUP_upper2 bdd_aboveI2[where M=1] cSUP_least pmf_le_1 pmf_nonneg simp add: \<epsilon>_uh_def)

lemma hash_ineq_card:
  assumes "finite W"
  shows "spmf (game_hash_set W) True \<le> \<epsilon>_uh * card W * card W" 
proof -
  let ?M = "measure (measure_spmf seed_gen)"
  have bound: "?M {x. hash x w = hash x w' \<and> w \<noteq> w'} \<le> \<epsilon>_uh" for w w'
  proof -
    have "?M {x. hash x w = hash x w' \<and> w \<noteq> w'} = spmf (game_hash w w') True"
      by(simp add: game_hash_def spmf_conv_measure_spmf map_spmf_conv_bind_spmf[symmetric] measure_map_spmf vimage_def)
    also have "\<dots> \<le> \<epsilon>_uh" unfolding \<epsilon>_uh_def
      by(auto intro!: cSUP_upper2 bdd_aboveI[where M=1] cSUP_least simp add: pmf_le_1)
    finally show ?thesis .
  qed

  have "spmf (game_hash_set W) True = ?M {x. \<exists>xa\<in>W. \<exists>y\<in>W. hash x xa = hash x y \<and> xa \<noteq> y}"
    by(auto simp add: game_hash_set_def inj_on_def map_spmf_conv_bind_spmf[symmetric] spmf_conv_measure_spmf measure_map_spmf vimage_def)
  also have "{x. \<exists>xa\<in>W. \<exists>y\<in>W. hash x xa = hash x y \<and> xa \<noteq> y} = (\<Union>(w, w') \<in> W\<times> W. {x. hash x w = hash x w' \<and> w \<noteq> w'})"
    by(auto)
  also have "?M \<dots> \<le> (\<Sum>(w, w')\<in>W \<times> W. ?M {x. hash x w = hash x w' \<and> w \<noteq> w'})"
    by(auto intro!: measure_spmf.finite_measure_subadditive_finite simp add: split_def assms)
  also have "\<dots> \<le> (\<Sum>(w, w')\<in>W \<times> W. \<epsilon>_uh)" by(rule sum_mono)(clarsimp simp add: bound)
  also have "\<dots> =  \<epsilon>_uh * card(W) * card(W)" by(simp add: card_cartesian_product)
  finally show ?thesis .
qed

end 

locale prf_hash =
  fixes f :: "'key \<Rightarrow> '\<alpha> \<Rightarrow> '\<gamma>"
  and h :: "'seed \<Rightarrow> '\<beta> \<Rightarrow> '\<alpha>"
  and key_gen :: "'key spmf"
  and seed_gen :: "'seed spmf"
  and range_f :: "'\<gamma> set"
  assumes lossless_seed_gen: "lossless_spmf seed_gen"
  and range_f_finite: "finite range_f"
  and range_f_nonempty: "range_f \<noteq> {}"
begin

definition rand :: "'\<gamma> spmf"
where "rand = spmf_of_set range_f"

lemma lossless_rand [simp]: "lossless_spmf rand"
by(simp add: rand_def range_f_finite range_f_nonempty)

definition key_seed_gen :: "('key * 'seed) spmf"
where
  "key_seed_gen = do {
     k \<leftarrow> key_gen;
     s :: 'seed \<leftarrow> seed_gen;
     return_spmf (k, s)
   }"

interpretation "prf": "prf" key_gen f rand .
interpretation hash: hash "seed_gen" "h".

fun f' :: "'key \<times> 'seed \<Rightarrow> '\<beta> \<Rightarrow> '\<gamma>"
where "f' (key, seed) x = f key (h seed x)"

interpretation "prf'": "prf" key_seed_gen f' rand .

definition reduction_oracle :: "'seed \<Rightarrow> unit \<Rightarrow> '\<beta> \<Rightarrow> ('\<gamma> \<times> unit, '\<alpha>, '\<gamma>) gpv"
where "reduction_oracle seed x b = Pause (h seed b) (\<lambda>x. Done (x, ()))" 

definition prf'_reduction :: " ('\<beta>, '\<gamma>) prf'.adversary \<Rightarrow> ('\<alpha>, '\<gamma>) prf.adversary"
where
  "prf'_reduction \<A> = do {
      seed  \<leftarrow> lift_spmf seed_gen;
      (b, \<sigma>) \<leftarrow> inline (reduction_oracle seed) \<A> ();
      Done b
  }"

theorem prf_prf'_advantage: 
  assumes "prf'.lossless \<A>"
  and bounded: "prf'.ibounded_by \<A> q" 
  shows "prf'.advantage \<A>  \<le> prf.advantage (prf'_reduction \<A>) + hash.\<epsilon>_uh * q * q"
  including lifting_syntax
proof -
  let ?\<A> = "prf'_reduction \<A>"

  { define cr where "cr = (\<lambda>_ :: unit \<times> unit. \<lambda>_ :: unit. True)"
    have [transfer_rule]: "cr ((), ()) ()" by(simp add: cr_def)
    have "prf.game_0 ?\<A> = prf'.game_0 \<A>"
      unfolding prf'.game_0_def prf.game_0_def prf'_reduction_def unfolding key_seed_gen_def
      by(simp add: exec_gpv_bind split_def exec_gpv_inline reduction_oracle_def bind_map_spmf prf.prf_oracle_def prf'.prf_oracle_def[abs_def]) 
        (transfer_prover) }
  note hop1 = this[symmetric]

  define semi_forgetful_RO where "semi_forgetful_RO = (\<lambda>seed :: 'seed. \<lambda>(\<sigma> :: '\<alpha> \<rightharpoonup> '\<beta> \<times> '\<gamma>, b :: bool). \<lambda>x. 
    case \<sigma> (h seed x) of Some (a, y) \<Rightarrow> return_spmf (y, (\<sigma>, a \<noteq> x \<or> b))
     | None \<Rightarrow> bind_spmf rand (\<lambda>y. return_spmf (y, (\<sigma>(h seed x \<mapsto> (x, y)), b))))"

  define game_semi_forgetful where "game_semi_forgetful = do {
     seed :: 'seed \<leftarrow> seed_gen;
     (b, rep) \<leftarrow> exec_gpv (semi_forgetful_RO seed) \<A> (Map.empty, False);
     return_spmf (b, rep) 
   }"

  have bad_semi_forgetful [simp]: "callee_invariant (semi_forgetful_RO seed) snd" for seed
    by(unfold_locales)(auto simp add: semi_forgetful_RO_def split: option.split_asm)
  have lossless_semi_forgetful [simp]: "lossless_spmf (semi_forgetful_RO seed s1 x)" for seed s1 x
    by(simp add: semi_forgetful_RO_def split_def split: option.split)

  { define cr
      where "cr = (\<lambda>(_ :: unit, \<sigma>) (\<sigma>' :: '\<alpha> \<Rightarrow> ('\<beta> \<times> '\<gamma>) option, _ :: bool). \<sigma> = map_option snd \<circ> \<sigma>')"
    define initial where "initial = (Map.empty :: '\<alpha> \<Rightarrow> ('\<beta> \<times> '\<gamma>) option, False)"
    have [transfer_rule]: "cr ((), Map.empty) initial" by(simp add: cr_def initial_def fun_eq_iff)
    have [transfer_rule]:  "((=) ===> cr ===> (=) ===> rel_spmf (rel_prod (=) cr))
        (\<lambda>y p ya. do {y \<leftarrow> prf.random_oracle (snd p) (h y ya); return_spmf (fst y, (), snd y) })
        semi_forgetful_RO"
      by(auto simp add: semi_forgetful_RO_def cr_def prf.random_oracle_def rel_fun_def fun_eq_iff split: option.split intro!: rel_spmf_bind_reflI)
    have "prf.game_1 ?\<A> = map_spmf fst game_semi_forgetful"
      unfolding prf.game_1_def prf'_reduction_def game_semi_forgetful_def
      by(simp add: exec_gpv_bind exec_gpv_inline split_def bind_map_spmf map_spmf_bind_spmf o_def map_spmf_conv_bind_spmf reduction_oracle_def initial_def[symmetric])
        (transfer_prover) }
  note hop2 = this

  define game_semi_forgetful_bad where "game_semi_forgetful_bad = do {
       seed :: 'seed \<leftarrow> seed_gen;
       x \<leftarrow> exec_gpv (semi_forgetful_RO seed) \<A> (Map.empty, False);
       return_spmf (snd x) 
       }"
  have game_semi_forgetful_bad : "map_spmf snd game_semi_forgetful = game_semi_forgetful_bad"
    unfolding game_semi_forgetful_bad_def game_semi_forgetful_def
    by(simp add: map_spmf_bind_spmf o_def)

  have bad_random_oracle_A [simp]: "callee_invariant prf.random_oracle (\<lambda>\<sigma>. \<not> inj_on (h seed) (dom \<sigma>))" for seed
    by unfold_locales(auto simp add: prf.random_oracle_def split: option.split_asm)

  define invar
    where "invar = (\<lambda>seed (\<sigma>1, b) (\<sigma>2 :: '\<beta> \<Rightarrow> '\<gamma> option). \<not> b \<and> dom \<sigma>1 = h seed ` dom \<sigma>2 \<and> 
      (\<forall>x \<in> dom \<sigma>2. \<sigma>1 (h seed x) = map_option (Pair x) (\<sigma>2 x)))"

  have rel_spmf_oracle_adv: 
    "rel_spmf (\<lambda>(x, s1) (y, s2). snd s1 \<noteq> inj_on (h seed) (dom s2) \<and> (inj_on (h seed) (dom s2) \<longrightarrow> x = y \<and> invar seed s1 s2))
      (exec_gpv (semi_forgetful_RO seed) \<A> (Map.empty, False))
      (exec_gpv prf.random_oracle \<A> Map.empty)"
    if seed: "seed \<in> set_spmf seed_gen" for seed
  proof -
    have invar_initial [simp]: "invar seed (Map.empty, False) Map.empty" by(simp add: invar_def)
    have invarD_inj: "inj_on (h seed) (dom s2)" if "invar seed bs1 s2" for bs1 s2
      using that by(auto intro!: inj_onI simp add: invar_def)(metis domI domIff option.map_sel prod.inject)

    let ?R = "\<lambda>(a, s1) (b, s2 :: '\<beta> \<Rightarrow> '\<gamma> option).
        snd s1 = (\<not> inj_on (h seed) (dom s2)) \<and>
        (\<not> \<not> inj_on (h seed) (dom s2) \<longrightarrow> a = b \<and> invar seed s1 s2)"

    have step: "rel_spmf ?R (semi_forgetful_RO seed \<sigma>1b x) (prf.random_oracle s2 x)"
      if X: "invar seed \<sigma>1b s2" for s2 \<sigma>1b x
    proof -
      obtain \<sigma>1 b where [simp]: "\<sigma>1b = (\<sigma>1, b)" by(cases \<sigma>1b)
      from X have not_b: "\<not> b"
        and dom: "dom \<sigma>1 = h seed ` dom s2"
        and eq: "\<forall>x\<in>dom s2. \<sigma>1 (h seed x) = map_option (Pair x) (s2 x)" 
        by(simp_all add: invar_def)
      from X have inj: "inj_on (h seed) (dom s2)" by(rule invarD_inj)
  
      have not_in_image: "h seed x \<notin> h seed ` (dom s2 - {x})" if "\<sigma>1 (h seed x) = None"
      proof (rule notI)
        assume "h seed x \<in> h seed ` (dom s2 - {x})"
        then obtain y where "y \<in> dom s2" and hx_hy: "h seed x = h seed y" by (auto)
        then have "\<sigma>1 (h seed y) = None" using that by (auto)
        then have "h seed y \<notin> h seed ` dom s2" using dom by (auto)
        then have "y \<notin> dom s2" by (auto)
        then show False using \<open>y \<in> dom s2\<close> by(auto)
      qed
  
      show ?thesis
      proof(cases "\<sigma>1 (h seed x)")
        case \<sigma>1: None
        hence s2: "s2 x = None" using dom by(auto)
        have "insert (h seed x) (dom \<sigma>1) = insert (h seed x) (h seed ` dom s2)" by(simp add: dom)
        then have invar_update: "invar seed (\<sigma>1(h seed x \<mapsto> (x, bs)), False) (s2(x \<mapsto> bs))" for bs
          using inj not_b not_in_image \<sigma>1 dom
          by(auto simp add: invar_def domIff eq) (metis domI domIff imageI)
        with \<sigma>1 s2 show ?thesis using inj not_b not_in_image
          by(auto simp add: semi_forgetful_RO_def prf.random_oracle_def intro: rel_spmf_bind_reflI)
      next
        case \<sigma>1: (Some "by")
        show ?thesis
        proof(cases "s2 x")
          case s2: (Some z)
          with eq \<sigma>1 have "by = (x, z)" by(auto simp add: domIff)
          thus ?thesis using \<sigma>1 inj not_b s2 X
            by(simp add: semi_forgetful_RO_def prf.random_oracle_def split_beta)
        next
          case s2: None
          from \<sigma>1 dom obtain y where y: "y \<in> dom s2" and *: "h seed x = h seed y" 
            by(metis domIff imageE option.distinct(1))
          from y obtain z where z: "s2 y = Some z" by auto
          from eq z \<sigma>1 have "by": "by = (y, z)" by(auto simp add: * domIff)
          from y s2 have xny: "x \<noteq> y" by auto
          with y * have "h seed x \<in> h seed ` (dom s2 - {x})" by auto
          then show ?thesis using \<sigma>1 s2 not_b "by" xny inj
            by(simp add: semi_forgetful_RO_def prf.random_oracle_def split_beta)(rule rel_spmf_bindI2; simp)
        qed
      qed
    qed
    from invar_initial _ step show ?thesis
      by(rule exec_gpv_oracle_bisim_bad_full[where ?bad1.0 = "snd" and ?bad2.0 = "\<lambda>\<sigma>. \<not> inj_on (h seed) (dom \<sigma>)"])
        (simp_all add: assms)
  qed

  define game_A where "game_A = do {
      seed :: 'seed \<leftarrow> seed_gen;
      (b, \<sigma>) \<leftarrow> exec_gpv prf.random_oracle \<A> Map.empty;
      return_spmf (b, \<not> inj_on (h seed) (dom \<sigma>))
    }"

  let ?bad1 = "\<lambda>x. snd (snd x)" and ?bad2 = "snd"
  have hop3: "rel_spmf (\<lambda>x xa. (?bad1 x \<longleftrightarrow> ?bad2 xa) \<and> (\<not> ?bad2 xa \<longrightarrow> fst x \<longleftrightarrow> fst xa)) game_semi_forgetful game_A"
    unfolding game_semi_forgetful_def game_A_def 
    by(clarsimp simp add: restrict_bind_spmf split_def map_spmf_bind_spmf restrict_return_spmf o_def intro!: rel_spmf_bind_reflI simp del: bind_return_spmf)
      (rule rel_spmf_bindI[OF rel_spmf_oracle_adv]; auto)
  have bad1_bad2: "spmf (map_spmf (snd \<circ> snd) game_semi_forgetful) True = spmf (map_spmf snd game_A) True"
    using fundamental_lemma_bad[OF hop3] by(simp add: measure_map_spmf spmf_conv_measure_spmf vimage_def)
  have bound_bad1_event: "\<bar>spmf (map_spmf fst game_semi_forgetful) True - spmf (map_spmf fst game_A) True\<bar> \<le> spmf (map_spmf (snd \<circ> snd) game_semi_forgetful) True"
    using fundamental_lemma[OF hop3] by(simp add: measure_map_spmf spmf_conv_measure_spmf vimage_def)
  
  then have bound_bad2_event : "\<bar>spmf (map_spmf fst game_semi_forgetful) True - spmf (map_spmf fst game_A) True\<bar> \<le> spmf (map_spmf snd game_A) True"
    using bad1_bad2 by (simp)
  
  define game_B where "game_B = do {
      (b, \<sigma>) \<leftarrow> exec_gpv prf.random_oracle \<A> Map.empty;
      hash.game_hash_set (dom \<sigma>)
    }"
  
  have game_A_game_B: "map_spmf snd game_A = game_B"
    unfolding game_B_def game_A_def hash.game_hash_set_def including monad_normalisation
    by(simp add: map_spmf_bind_spmf o_def split_def)
  
  have game_B_bound : "spmf game_B True \<le> hash.\<epsilon>_uh * q * q" unfolding game_B_def
  proof(rule spmf_bind_leI, clarify)
    fix b \<sigma>
    assume *: "(b, \<sigma>) \<in> set_spmf (exec_gpv prf.random_oracle \<A> Map.empty)"
    have "finite (dom \<sigma>)" by(rule prf.finite.exec_gpv_invariant[OF *]) simp_all
    then have "spmf (hash.game_hash_set (dom \<sigma>)) True \<le> hash.\<epsilon>_uh * (card (dom \<sigma>) * card (dom \<sigma>))"
      using hash.hash_ineq_card[of "dom \<sigma>"] by simp
    also have p1: "card (dom \<sigma>) \<le> q + card (dom (Map.empty :: '\<beta> \<Rightarrow> '\<gamma> option))" 
      by(rule prf.card_dom_random_oracle[OF bounded *]) simp
    then have "card (dom \<sigma>) * card (dom \<sigma>) \<le> q * q" using mult_le_mono by auto
    finally show "spmf (hash.game_hash_set (dom \<sigma>)) True \<le> hash.\<epsilon>_uh * q * q"
      by(simp add: hash.\<epsilon>_uh_nonneg mult_left_mono)
  qed(simp add: hash.\<epsilon>_uh_nonneg)
  
  have hop4: "prf'.game_1 \<A> = map_spmf fst game_A"
    by(simp add: game_A_def prf'.game_1_def map_spmf_bind_spmf o_def split_def bind_spmf_const lossless_seed_gen lossless_weight_spmfD)
  
  have "prf'.advantage \<A> \<le> \<bar>spmf (prf.game_0 ?\<A>) True - spmf (prf'.game_1 \<A>) True\<bar>"
    using hop1 by(simp add: prf'.advantage_def)
  also have "\<dots> \<le> prf.advantage ?\<A> + \<bar>spmf (prf.game_1 ?\<A>) True - spmf (prf'.game_1 \<A>) True\<bar>"
    by(simp add: prf.advantage_def)
  also have "\<bar>spmf (prf.game_1 ?\<A>) True - spmf (prf'.game_1 \<A>) True\<bar> \<le>
    \<bar>spmf (map_spmf fst game_semi_forgetful) True - spmf (prf'.game_1 \<A>) True\<bar>"
    using hop2 by simp
  also have "\<dots> \<le> hash.\<epsilon>_uh * q * q"
    using game_A_game_B game_B_bound bound_bad2_event hop4 by(simp)
  finally show ?thesis by(simp add: add_left_mono)
qed

end

end
