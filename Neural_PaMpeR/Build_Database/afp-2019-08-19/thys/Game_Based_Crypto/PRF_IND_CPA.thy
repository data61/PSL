(* Title: PRF_IND_CPA.thy
  Author: Andreas Lochbihler, ETH Zurich *)

subsection \<open>IND-CPA from PRF\<close>

theory PRF_IND_CPA imports
  CryptHOL.GPV_Bisim
  CryptHOL.List_Bits
  Pseudo_Random_Function
  IND_CPA
begin

text \<open>
  Formalises the construction from \cite{PetcherMorrisett2015POST}.
\<close>

declare [[simproc del: let_simp]]

type_synonym key = "bool list"
type_synonym plain = "bool list"
type_synonym cipher = "bool list * bool list"

locale otp =
  fixes f :: "key \<Rightarrow> bool list \<Rightarrow> bool list"
  and len :: nat
  assumes length_f: "\<And>xs ys. \<lbrakk> length xs = len; length ys = len \<rbrakk> \<Longrightarrow> length (f xs ys) = len"
begin

definition key_gen :: "bool list spmf"
where "key_gen = spmf_of_set (nlists UNIV len)"

definition valid_plain :: "plain \<Rightarrow> bool"
where "valid_plain plain \<longleftrightarrow> length plain = len"

definition encrypt :: "key \<Rightarrow> plain \<Rightarrow> cipher spmf"
where
  "encrypt key plain = do {
     r \<leftarrow> spmf_of_set (nlists UNIV len);
     return_spmf (r, xor_list plain (f key r))
   }"

fun decrypt :: "key \<Rightarrow> cipher \<Rightarrow> plain option"
where "decrypt key (r, c) = Some (xor_list (f key r) c)"

lemma encrypt_decrypt_correct:
  "\<lbrakk> length key = len; length plain = len \<rbrakk>
  \<Longrightarrow> encrypt key plain \<bind> (\<lambda>cipher. return_spmf (decrypt key cipher)) = return_spmf (Some plain)"
by(simp add: encrypt_def zip_map2 o_def split_def bind_eq_return_spmf length_f in_nlists_UNIV xor_list_left_commute)

interpretation ind_cpa: ind_cpa key_gen encrypt decrypt valid_plain .
interpretation "prf": "prf" key_gen f "spmf_of_set (nlists UNIV len)" .

definition prf_encrypt_oracle :: "unit \<Rightarrow> plain \<Rightarrow> (cipher \<times> unit, plain, plain) gpv"
where
  "prf_encrypt_oracle x plain = do {
     r \<leftarrow> lift_spmf (spmf_of_set (nlists UNIV len));
     Pause r (\<lambda>pad. Done ((r, xor_list plain pad), ()))
  }"

lemma interaction_bounded_by_prf_encrypt_oracle [interaction_bound]:
  "interaction_any_bounded_by (prf_encrypt_oracle \<sigma> plain) 1"
unfolding prf_encrypt_oracle_def by simp

lemma lossless_prf_encyrpt_oracle [simp]: "lossless_gpv \<I>_top (prf_encrypt_oracle s x)"
by(simp add: prf_encrypt_oracle_def)

definition prf_adversary :: "(plain, cipher, 'state) ind_cpa.adversary \<Rightarrow> (plain, plain) prf.adversary"
where
  "prf_adversary \<A> = do {
     let (\<A>1, \<A>2) = \<A>;
     (((p1, p2), \<sigma>), n) \<leftarrow> inline prf_encrypt_oracle \<A>1 ();
     if valid_plain p1 \<and> valid_plain p2 then do { 
       b \<leftarrow> lift_spmf coin_spmf;
       let pb = (if b then p1 else p2);
       r \<leftarrow> lift_spmf (spmf_of_set (nlists UNIV len));
       pad \<leftarrow> Pause r Done;
       let c = (r, xor_list pb pad);
       (b', _) \<leftarrow> inline prf_encrypt_oracle (\<A>2 c \<sigma>) n;
       Done (b' = b)
     } else lift_spmf coin_spmf
  }"

theorem prf_encrypt_advantage:
  assumes "ind_cpa.ibounded_by \<A> q"
  and "lossless_gpv \<I>_full (fst \<A>)"
  and "\<And>cipher \<sigma>. lossless_gpv \<I>_full (snd \<A> cipher \<sigma>)"
  shows "ind_cpa.advantage \<A> \<le> prf.advantage (prf_adversary \<A>) + q / 2 ^ len"
proof -
  note [split del] = if_split
    and [cong del] = if_weak_cong
    and [simp] =
      bind_spmf_const map_spmf_bind_spmf bind_map_spmf 
      exec_gpv_bind exec_gpv_inline
      rel_spmf_bind_reflI rel_spmf_reflI
  obtain \<A>1 \<A>2 where \<A>: "\<A> = (\<A>1, \<A>2)" by(cases "\<A>")
  from \<open>ind_cpa.ibounded_by _ _\<close>
  obtain q1 q2 :: nat
    where q1: "interaction_any_bounded_by \<A>1 q1"
    and q2: "\<And>cipher \<sigma>. interaction_any_bounded_by (\<A>2 cipher \<sigma>) q2"
    and "q1 + q2 \<le> q"
    unfolding \<A> by(rule ind_cpa.ibounded_byE)(auto simp add: iadd_le_enat_iff)
  from \<A> assms have lossless1: "lossless_gpv \<I>_full \<A>1"
    and lossless2: "\<And>cipher \<sigma>. lossless_gpv \<I>_full (\<A>2 cipher \<sigma>)" by simp_all
  have weight1: "\<And>oracle s. (\<And>s x. lossless_spmf (oracle s x)) 
    \<Longrightarrow> weight_spmf (exec_gpv oracle \<A>1 s) = 1"
    by(rule lossless_weight_spmfD)(rule lossless_exec_gpv[OF lossless1], simp_all)
  have weight2: "\<And>oracle s cipher \<sigma>. (\<And>s x. lossless_spmf (oracle s x)) 
    \<Longrightarrow> weight_spmf (exec_gpv oracle (\<A>2 cipher \<sigma>) s) = 1"
    by(rule lossless_weight_spmfD)(rule lossless_exec_gpv[OF lossless2], simp_all)

  let ?oracle1 = "\<lambda>key (s', s) y. map_spmf (\<lambda>((x, s'), s). (x, (), ())) (exec_gpv (prf.prf_oracle key) (prf_encrypt_oracle () y) ())"
  have bisim1: "\<And>key. rel_spmf (\<lambda>(x, _) (y, _). x = y)
          (exec_gpv (ind_cpa.encrypt_oracle key) \<A>1 ())
          (exec_gpv (?oracle1 key) \<A>1 ((), ()))"
    using TrueI
    by(rule exec_gpv_oracle_bisim)(auto simp add: encrypt_def prf_encrypt_oracle_def ind_cpa.encrypt_oracle_def prf.prf_oracle_def o_def)
  have bisim2: "\<And>key cipher \<sigma>. rel_spmf (\<lambda>(x, _) (y, _). x = y)
             (exec_gpv (ind_cpa.encrypt_oracle key) (\<A>2 cipher \<sigma>) ())
             (exec_gpv (?oracle1 key) (\<A>2 cipher \<sigma>) ((), ()))"
    using TrueI
    by(rule exec_gpv_oracle_bisim)(auto simp add: encrypt_def prf_encrypt_oracle_def ind_cpa.encrypt_oracle_def prf.prf_oracle_def o_def)
   
  have ind_cpa_0: "rel_spmf (=) (ind_cpa.ind_cpa \<A>) (prf.game_0 (prf_adversary \<A>))"
    unfolding IND_CPA.ind_cpa.ind_cpa_def \<A> key_gen_def Let_def prf_adversary_def Pseudo_Random_Function.prf.game_0_def
    apply(simp)
    apply(rewrite in "bind_spmf _ \<hole>" bind_commute_spmf)
    apply(rule rel_spmf_bind_reflI)
    apply(rule rel_spmf_bindI[OF bisim1])
    apply(clarsimp simp add: if_distribs bind_coin_spmf_eq_const')
    apply(auto intro: rel_spmf_bindI[OF bisim2] intro!: rel_spmf_bind_reflI simp add: encrypt_def prf.prf_oracle_def cong del: if_cong)
    done

  define rf_encrypt where "rf_encrypt = (\<lambda>s plain. bind_spmf (spmf_of_set (nlists UNIV len)) (\<lambda>r :: bool list. 
    bind_spmf (prf.random_oracle s r) (\<lambda>(pad, s'). 
    return_spmf ((r, xor_list plain pad), s')))
  )"
  interpret rf_finite: callee_invariant_on rf_encrypt "\<lambda>s. finite (dom s)" \<I>_full
    by unfold_locales(auto simp add: rf_encrypt_def dest: prf.finite.callee_invariant)
  have lossless_rf_encrypt [simp]: "\<And>s plain. lossless_spmf (rf_encrypt s plain)"
    by(auto simp add: rf_encrypt_def)

  define game2 where "game2 = do {
    (((p0, p1), \<sigma>), s1) \<leftarrow> exec_gpv rf_encrypt \<A>1 Map.empty;
    if valid_plain p0 \<and> valid_plain p1 then do {
      b \<leftarrow> coin_spmf;
      let pb = (if b then p0 else p1);
      (cipher, s2) \<leftarrow> rf_encrypt s1 pb;
      (b', s3) \<leftarrow> exec_gpv rf_encrypt (\<A>2 cipher \<sigma>) s2;
      return_spmf (b' = b)
    } else coin_spmf
  }"

  let ?oracle2 = "\<lambda>(s', s) y. map_spmf (\<lambda>((x, s'), s). (x, (), s)) (exec_gpv prf.random_oracle (prf_encrypt_oracle () y) s)"
  let ?I = "\<lambda>(x, _, s) (y, s'). x = y \<and> s = s'"
  have bisim1: "rel_spmf ?I (exec_gpv ?oracle2 \<A>1 ((), Map.empty)) (exec_gpv rf_encrypt \<A>1 Map.empty)"
     by(rule exec_gpv_oracle_bisim[where X="\<lambda>(_, s) s'. s = s'"])
       (auto simp add: rf_encrypt_def prf_encrypt_oracle_def intro!: rel_spmf_bind_reflI)
  have bisim2: "\<And>cipher \<sigma> s. rel_spmf ?I (exec_gpv ?oracle2 (\<A>2 cipher \<sigma>) ((), s)) (exec_gpv rf_encrypt (\<A>2 cipher \<sigma>) s)"
    by(rule exec_gpv_oracle_bisim[where X="\<lambda>(_, s) s'. s = s'"])
      (auto simp add: prf_encrypt_oracle_def rf_encrypt_def intro!: rel_spmf_bind_reflI)
  have game1_2 [unfolded spmf_rel_eq]: "rel_spmf (=) (prf.game_1 (prf_adversary \<A>)) game2"
    unfolding prf.game_1_def game2_def prf_adversary_def
    by(rewrite in "if _ then \<hole> else _" rf_encrypt_def)
      (auto simp add: Let_def \<A> if_distribs intro!: rel_spmf_bindI[OF bisim2] rel_spmf_bind_reflI rel_spmf_bindI[OF bisim1])

  define game2_a where "game2_a = do {
    r \<leftarrow> spmf_of_set (nlists UNIV len);
    (((p0, p1), \<sigma>), s1) \<leftarrow> exec_gpv rf_encrypt \<A>1 Map.empty;
    let bad = r \<in> dom s1;
    if valid_plain p0 \<and> valid_plain p1 then do {
      b \<leftarrow> coin_spmf;
      let pb = (if b then p0 else p1);
      (pad, s2) \<leftarrow> prf.random_oracle s1 r;
      let cipher = (r, xor_list pb pad);
      (b', s3) \<leftarrow> exec_gpv rf_encrypt (\<A>2 cipher \<sigma>) s2;
      return_spmf (b' = b, bad)
    } else coin_spmf \<bind> (\<lambda>b. return_spmf (b, bad))
  }"
  define game2_b where "game2_b = do {
    r \<leftarrow> spmf_of_set (nlists UNIV len);
    (((p0, p1), \<sigma>), s1) \<leftarrow> exec_gpv rf_encrypt \<A>1 Map.empty;
    let bad = r \<in> dom s1;
    if valid_plain p0 \<and> valid_plain p1 then do {
      b \<leftarrow> coin_spmf;
      let pb = (if b then p0 else p1);
      pad \<leftarrow> spmf_of_set (nlists UNIV len);
      let cipher = (r, xor_list pb pad);
      (b', s3) \<leftarrow> exec_gpv rf_encrypt (\<A>2 cipher \<sigma>) (s1(r \<mapsto> pad));
      return_spmf (b' = b, bad)
    } else coin_spmf \<bind> (\<lambda>b. return_spmf (b, bad))
  }"
  
  have "game2 = do {
      r \<leftarrow> spmf_of_set (nlists UNIV len);
      (((p0, p1), \<sigma>), s1) \<leftarrow> exec_gpv rf_encrypt \<A>1 Map.empty;
      if valid_plain p0 \<and> valid_plain p1 then do {
        b \<leftarrow> coin_spmf;
        let pb = (if b then p0 else p1);
        (pad, s2) \<leftarrow> prf.random_oracle s1 r;
        let cipher = (r, xor_list pb pad);
        (b', s3) \<leftarrow> exec_gpv rf_encrypt (\<A>2 cipher \<sigma>) s2;
        return_spmf (b' = b)
      } else coin_spmf
    }"
    including monad_normalisation by(simp add: game2_def split_def rf_encrypt_def Let_def)
  also have "\<dots> = map_spmf fst game2_a" unfolding game2_a_def
    by(clarsimp simp add: map_spmf_conv_bind_spmf Let_def if_distribR if_distrib split_def cong: if_cong)
  finally have game2_2a: "game2 = \<dots>"  .

  have "map_spmf snd game2_a = map_spmf snd game2_b" unfolding game2_a_def game2_b_def
    by(auto simp add: o_def Let_def split_def if_distribs weight2 split: option.split intro: bind_spmf_cong[OF refl])
  moreover
  have "rel_spmf (=) (map_spmf fst (game2_a \<upharpoonleft> (snd -` {False}))) (map_spmf fst (game2_b \<upharpoonleft> (snd -` {False})))"
    unfolding game2_a_def game2_b_def
    by(clarsimp simp add: restrict_bind_spmf o_def Let_def if_distribs split_def restrict_return_spmf prf.random_oracle_def intro!: rel_spmf_bind_reflI split: option.splits)
  hence "spmf game2_a (True, False) = spmf game2_b (True, False)" 
     unfolding spmf_rel_eq by(subst (1 2) spmf_map_restrict[symmetric]) simp
  ultimately
  have game2a_2b: "\<bar>spmf (map_spmf fst game2_a) True - spmf (map_spmf fst game2_b) True\<bar> \<le> spmf (map_spmf snd game2_a) True"
    by(subst (1 2) spmf_conv_measure_spmf)(rule identical_until_bad; simp add: spmf.map_id[unfolded id_def] spmf_conv_measure_spmf)

  define game2_a_bad where "game2_a_bad = do {
      r \<leftarrow> spmf_of_set (nlists UNIV len);
      (((p0, p1), \<sigma>), s1) \<leftarrow> exec_gpv rf_encrypt \<A>1 Map.empty;
      return_spmf (r \<in> dom s1)
    }"
  have game2a_bad: "map_spmf snd game2_a = game2_a_bad"
    unfolding game2_a_def game2_a_bad_def
    by(auto intro!: bind_spmf_cong[OF refl] simp add: o_def weight2 Let_def split_def split: if_split)
  have card: "\<And>B :: bool list set. card (B \<inter> nlists UNIV len) \<le> card (nlists UNIV len :: bool list set)"
    by(rule card_mono) simp_all
  then have "spmf game2_a_bad True = \<integral>\<^sup>+ x. card (dom (snd x) \<inter> nlists UNIV len) / 2 ^ len \<partial>measure_spmf (exec_gpv rf_encrypt \<A>1 Map.empty)" 
    unfolding game2_a_bad_def
    by(rewrite bind_commute_spmf)(simp add: ennreal_spmf_bind split_def map_mem_spmf_of_set[unfolded map_spmf_conv_bind_spmf] card_nlists)
  also { fix x s
    assume *: "(x, s) \<in> set_spmf (exec_gpv rf_encrypt \<A>1 Map.empty)"
    hence "finite (dom s)" by(rule rf_finite.exec_gpv_invariant) simp_all
    hence 1: "card (dom s \<inter> nlists UNIV len) \<le> card (dom s)" by(intro card_mono) simp_all
    moreover from q1 *
    have "card (dom s) \<le> q1 + card (dom (Map.empty :: (plain, plain) prf.dict))"
      by(rule rf_finite.interaction_bounded_by'_exec_gpv_count)
        (auto simp add: rf_encrypt_def eSuc_enat prf.random_oracle_def card_insert_if split: option.split_asm if_split)
    ultimately have "card (dom s \<inter> nlists UNIV len) \<le> q1" by(simp) }
  then have "\<dots> \<le>  \<integral>\<^sup>+ x. q1 / 2 ^ len \<partial>measure_spmf (exec_gpv rf_encrypt \<A>1 Map.empty)"
    by(intro nn_integral_mono_AE)(clarsimp simp add: field_simps)
  also have "\<dots> \<le> q1 / 2 ^ len"
    by(simp add: measure_spmf.emeasure_eq_measure field_simps mult_left_le weight1)
  finally have game2a_bad_bound: "spmf game2_a_bad True \<le> q1 / 2 ^ len" by simp

  define rf_encrypt_bad
    where "rf_encrypt_bad = (\<lambda>secret (s :: (plain, plain) prf.dict, bad) plain. bind_spmf
     (spmf_of_set (nlists UNIV len)) (\<lambda>r.
     bind_spmf (prf.random_oracle s r) (\<lambda>(pad, s').
     return_spmf ((r, xor_list plain pad), (s', bad \<or> r = secret)))))"
  have rf_encrypt_bad_sticky [simp]: "\<And>s. callee_invariant (rf_encrypt_bad s) snd"
    by(unfold_locales)(auto simp add: rf_encrypt_bad_def)
  have lossless_rf_encrypt [simp]: "\<And>challenge s plain. lossless_spmf (rf_encrypt_bad challenge s plain)"
    by(clarsimp simp add: rf_encrypt_bad_def prf.random_oracle_def split: option.split)

  define game2_c where "game2_c = do {
    r \<leftarrow> spmf_of_set (nlists UNIV len);
    (((p0, p1), \<sigma>), s1) \<leftarrow> exec_gpv rf_encrypt \<A>1 Map.empty;
    if valid_plain p0 \<and> valid_plain p1 then do {
      b \<leftarrow> coin_spmf;
      let pb = (if b then p0 else p1);
      pad \<leftarrow> spmf_of_set (nlists UNIV len);
      let cipher = (r, xor_list pb pad);
      (b', (s2, bad)) \<leftarrow> exec_gpv (rf_encrypt_bad r) (\<A>2 cipher \<sigma>) (s1(r \<mapsto> pad), False);
      return_spmf (b' = b, bad)
    } else coin_spmf \<bind> (\<lambda>b. return_spmf (b, False))
  }"

  have bisim2c_bad: "\<And>cipher \<sigma> s x r. rel_spmf (\<lambda>(x, _) (y, _). x = y)
    (exec_gpv rf_encrypt (\<A>2 cipher \<sigma>) (s(x \<mapsto> r)))
    (exec_gpv (rf_encrypt_bad x) (\<A>2 cipher \<sigma>) (s(x \<mapsto> r), False))"
    by(rule exec_gpv_oracle_bisim[where X="\<lambda>s (s', _). s = s'"])
      (auto simp add: rf_encrypt_bad_def rf_encrypt_def intro!: rel_spmf_bind_reflI)

  have game2b_c [unfolded spmf_rel_eq]: "rel_spmf (=) (map_spmf fst game2_b) (map_spmf fst game2_c)"
    by(auto simp add: game2_b_def game2_c_def o_def split_def Let_def if_distribs intro!: rel_spmf_bind_reflI rel_spmf_bindI[OF bisim2c_bad])

  define game2_d where "game2_d = do {
    r \<leftarrow> spmf_of_set (nlists UNIV len);
    (((p0, p1), \<sigma>), s1) \<leftarrow> exec_gpv rf_encrypt \<A>1 Map.empty;
    if valid_plain p0 \<and> valid_plain p1 then do {
      b \<leftarrow> coin_spmf;
      let pb = (if b then p0 else p1);
      pad \<leftarrow> spmf_of_set (nlists UNIV len);
      let cipher = (r, xor_list pb pad);
      (b', (s2, bad)) \<leftarrow> exec_gpv (rf_encrypt_bad r) (\<A>2 cipher \<sigma>) (s1, False);
      return_spmf (b' = b, bad)
    } else coin_spmf \<bind> (\<lambda>b. return_spmf (b, False))
  }"


  { fix cipher \<sigma> and x :: plain and s r
    let ?I = "(\<lambda>(x, s, bad) (y, s', bad'). (bad \<longleftrightarrow> bad') \<and> (\<not> bad' \<longrightarrow> x \<longleftrightarrow> y))"
    let ?X = "\<lambda>(s, bad) (s', bad'). bad = bad' \<and> (\<forall>z. z \<noteq> x \<longrightarrow> s z = s' z)"
    have "\<And>s1 s2 x'. ?X s1 s2 \<Longrightarrow> rel_spmf (\<lambda>(a, s1') (b, s2'). snd s1' = snd s2' \<and> (\<not> snd s2' \<longrightarrow> a = b \<and> ?X s1' s2'))
       (rf_encrypt_bad x s1 x') (rf_encrypt_bad x s2 x')"
      by(case_tac "x = x'")(clarsimp simp add: rf_encrypt_bad_def prf.random_oracle_def rel_spmf_return_spmf1 rel_spmf_return_spmf2 Let_def split_def bind_UNION intro!: rel_spmf_bind_reflI split: option.split)+
    with _ _ have "rel_spmf ?I
             (exec_gpv (rf_encrypt_bad x) (\<A>2 cipher \<sigma>) (s(x \<mapsto> r), False))
             (exec_gpv (rf_encrypt_bad x) (\<A>2 cipher \<sigma>) (s, False))"
      by(rule exec_gpv_oracle_bisim_bad_full)(auto simp add: lossless2) }
  note bisim_bad = this
  have game2c_2d_bad [unfolded spmf_rel_eq]: "rel_spmf (=) (map_spmf snd game2_c) (map_spmf snd game2_d)"
    by(auto simp add: game2_c_def game2_d_def o_def Let_def split_def if_distribs intro!: rel_spmf_bind_reflI rel_spmf_bindI[OF bisim_bad])
  moreover
  have "rel_spmf (=) (map_spmf fst (game2_c \<upharpoonleft> (snd -` {False}))) (map_spmf fst (game2_d \<upharpoonleft> (snd -` {False})))"
    unfolding game2_c_def game2_d_def
    by(clarsimp simp add: restrict_bind_spmf o_def Let_def if_distribs split_def restrict_return_spmf intro!: rel_spmf_bind_reflI rel_spmf_bindI[OF bisim_bad])
  hence "spmf game2_c (True, False) = spmf game2_d (True, False)"
    unfolding spmf_rel_eq by(subst (1 2) spmf_map_restrict[symmetric]) simp
  ultimately have game2c_2d: "\<bar>spmf (map_spmf fst game2_c) True - spmf (map_spmf fst game2_d) True\<bar> \<le> spmf (map_spmf snd game2_c) True"
    apply(subst (1 2) spmf_conv_measure_spmf)
    apply(intro identical_until_bad) 
    apply(simp_all add: spmf.map_id[unfolded id_def] spmf_conv_measure_spmf)
    done
  { fix cipher \<sigma> and challenge :: plain and s
    have "card (nlists UNIV len \<inter> (\<lambda>x. x = challenge) -` {True}) \<le> card {challenge}"
      by(rule card_mono) auto
    then have "spmf (map_spmf (snd \<circ> snd) (exec_gpv (rf_encrypt_bad challenge) (\<A>2 cipher \<sigma>) (s, False))) True \<le> (1 / 2 ^ len) * q2"
      by(intro oi_True.interaction_bounded_by_exec_gpv_bad[OF q2])(simp_all add: rf_encrypt_bad_def o_def split_beta map_spmf_conv_bind_spmf[symmetric] spmf_map measure_spmf_of_set field_simps card_nlists)
    hence "(\<integral>\<^sup>+ x. ennreal (indicator {True} x) \<partial>measure_spmf (map_spmf (snd \<circ> snd) (exec_gpv (rf_encrypt_bad challenge) (\<A>2 cipher \<sigma>) (s, False)))) \<le> (1 / 2 ^ len) * q2"
      by(simp only: ennreal_indicator nn_integral_indicator sets_measure_spmf sets_count_space Pow_UNIV UNIV_I emeasure_spmf_single) simp }
  then have "spmf (map_spmf snd game2_d) True \<le>
        \<integral>\<^sup>+ (r :: plain). \<integral>\<^sup>+ (((p0, p1), \<sigma>), s). (if valid_plain p0 \<and> valid_plain p1 then
             \<integral>\<^sup>+ b . \<integral>\<^sup>+ (pad :: plain). q2 / 2 ^ len \<partial>measure_spmf (spmf_of_set (nlists UNIV len)) \<partial>measure_spmf coin_spmf
              else 0)
           \<partial>measure_spmf (exec_gpv rf_encrypt \<A>1 Map.empty) \<partial>measure_spmf (spmf_of_set (nlists UNIV len))"
      unfolding game2_d_def
      by(simp add: ennreal_spmf_bind o_def split_def Let_def if_distribs if_distrib[where f="\<lambda>x. ennreal (spmf x _)"] indicator_single_Some nn_integral_mono if_mono_cong del: nn_integral_const cong: if_cong)
  also have "\<dots> \<le> \<integral>\<^sup>+ (r :: plain). \<integral>\<^sup>+ (((p0, p1), \<sigma>), s). (if valid_plain p0 \<and> valid_plain p1 then ennreal (q2 / 2 ^ len) else q2 / 2 ^ len)
                   \<partial>measure_spmf (exec_gpv rf_encrypt \<A>1 Map.empty) \<partial>measure_spmf (spmf_of_set (nlists UNIV len))"
    unfolding split_def
    by(intro nn_integral_mono if_mono_cong)(auto simp add: measure_spmf.emeasure_eq_measure)
  also have "\<dots> \<le> q2 / 2 ^ len" by(simp add: split_def weight1 measure_spmf.emeasure_eq_measure)
  finally have game2_d_bad: "spmf (map_spmf snd game2_d) True \<le> q2 / 2 ^ len" by simp

  define game3 where "game3 = do {
      (((p0, p1), \<sigma>), s1) \<leftarrow> exec_gpv rf_encrypt \<A>1 Map.empty;
      if valid_plain p0 \<and> valid_plain p1 then do {
        b \<leftarrow> coin_spmf;
        let pb = (if b then p0 else p1);
        r \<leftarrow> spmf_of_set (nlists UNIV len);
        pad \<leftarrow> spmf_of_set (nlists UNIV len);
        let cipher = (r, xor_list pb pad);
        (b', s2) \<leftarrow> exec_gpv rf_encrypt (\<A>2 cipher \<sigma>) s1;
        return_spmf (b' = b)
      } else coin_spmf
    }"
  have bisim2d_3: "\<And>cipher \<sigma> s r. rel_spmf (\<lambda>(x, _) (y, _). x = y)
             (exec_gpv (rf_encrypt_bad r) (\<A>2 cipher \<sigma>) (s, False))
             (exec_gpv rf_encrypt (\<A>2 cipher \<sigma>) s)"
    by(rule exec_gpv_oracle_bisim[where X="\<lambda>(s1, _) s2. s1 = s2"])(auto simp add: rf_encrypt_bad_def rf_encrypt_def intro!: rel_spmf_bind_reflI)
  have game2d_3: "rel_spmf (=) (map_spmf fst game2_d) game3"
    unfolding game2_d_def game3_def Let_def including monad_normalisation
    by(clarsimp simp add: o_def split_def if_distribs cong: if_cong intro!: rel_spmf_bind_reflI rel_spmf_bindI[OF bisim2d_3])

  have "\<bar>spmf game2 True - 1 / 2\<bar> \<le>
    \<bar>spmf (map_spmf fst game2_a) True - spmf (map_spmf fst game2_b) True\<bar> + \<bar>spmf (map_spmf fst game2_b) True - 1 / 2\<bar>"
    unfolding game2_2a by(rule abs_diff_triangle_ineq2)
  also have "\<dots> \<le> q1 / 2 ^ len + \<bar>spmf (map_spmf fst game2_b) True - 1 / 2\<bar>"
    using game2a_2b game2a_bad_bound unfolding game2a_bad by(intro add_right_mono) simp
  also have "\<bar>spmf (map_spmf fst game2_b) True - 1 / 2\<bar> \<le>
    \<bar>spmf (map_spmf fst game2_c) True - spmf (map_spmf fst game2_d) True\<bar> + \<bar>spmf (map_spmf fst game2_d) True - 1 / 2\<bar>"
    unfolding game2b_c by(rule abs_diff_triangle_ineq2)
  also (add_left_mono_trans) have "\<dots> \<le> q2 / 2 ^ len + \<bar>spmf (map_spmf fst game2_d) True - 1 / 2\<bar>"
    using game2c_2d game2_d_bad unfolding game2c_2d_bad by(intro add_right_mono) simp
  finally (add_left_mono_trans) 
  have game2: "\<bar>spmf game2 True - 1 / 2\<bar> \<le> q1 / 2 ^ len + q2 / 2 ^ len +  \<bar>spmf game3 True - 1 / 2\<bar>"
    using game2d_3 by(simp add: field_simps spmf_rel_eq)

  have "game3 = do {
      (((p0, p1), \<sigma>), s1) \<leftarrow> exec_gpv rf_encrypt \<A>1 Map.empty;
      if valid_plain p0 \<and> valid_plain p1 then do {
        b \<leftarrow> coin_spmf;
        let pb = (if b then p0 else p1);
        r \<leftarrow> spmf_of_set (nlists UNIV len);
        pad \<leftarrow> map_spmf (xor_list pb) (spmf_of_set (nlists UNIV len));
        let cipher = (r, xor_list pb pad);
        (b', s2) \<leftarrow> exec_gpv rf_encrypt (\<A>2 cipher \<sigma>) s1;
        return_spmf (b' = b)
      } else coin_spmf
    }"
    by(simp add: valid_plain_def game3_def Let_def one_time_pad del: bind_map_spmf map_spmf_of_set_inj_on cong: bind_spmf_cong_simp if_cong split: if_split)
  also have "\<dots> = do {
       (((p0, p1), \<sigma>), s1) \<leftarrow> exec_gpv rf_encrypt \<A>1 Map.empty;
       if valid_plain p0 \<and> valid_plain p1 then do {
         b \<leftarrow> coin_spmf;
         let pb = (if b then p0 else p1);
         r \<leftarrow> spmf_of_set (nlists UNIV len);
         pad \<leftarrow> spmf_of_set (nlists UNIV len);
         let cipher = (r, pad);
         (b', _) \<leftarrow> exec_gpv rf_encrypt (\<A>2 cipher \<sigma>) s1;
         return_spmf (b' = b)
       } else coin_spmf
     }"
     by(simp add: game3_def Let_def valid_plain_def in_nlists_UNIV cong: bind_spmf_cong_simp if_cong split: if_split)
  also have "\<dots> = do {
      (((p0, p1), \<sigma>), s1) \<leftarrow> exec_gpv rf_encrypt \<A>1 Map.empty;
      if valid_plain p0 \<and> valid_plain p1 then do {
        r \<leftarrow> spmf_of_set (nlists UNIV len);
        pad \<leftarrow> spmf_of_set (nlists UNIV len);
        let cipher = (r, pad);
        (b', _) \<leftarrow> exec_gpv rf_encrypt (\<A>2 cipher \<sigma>) s1;
        map_spmf ((=) b') coin_spmf
      } else coin_spmf
    }"
    including monad_normalisation by(simp add: map_spmf_conv_bind_spmf split_def Let_def)
  also have "\<dots> = coin_spmf"
    by(simp add: map_eq_const_coin_spmf Let_def split_def weight2 weight1)
  finally have game3: "game3 = coin_spmf" .
  
  have "ind_cpa.advantage \<A> \<le> prf.advantage (prf_adversary \<A>) + \<bar>spmf (prf.game_1 (prf_adversary \<A>)) True - 1 / 2\<bar>"
    unfolding ind_cpa.advantage_def prf.advantage_def ind_cpa_0[unfolded spmf_rel_eq]
    by(rule abs_diff_triangle_ineq2)
  also have "\<bar>spmf (prf.game_1 (prf_adversary \<A>)) True - 1 / 2\<bar> \<le> q1 / 2 ^ len + q2 / 2 ^ len"
    using game1_2 game2 game3 by(simp add: spmf_of_set)
  also have "\<dots> = (q1 + q2) / 2 ^ len" by(simp add: field_simps)
  also have "\<dots> \<le> q / 2 ^ len" using \<open>q1 + q2 \<le> q\<close> by(simp add: divide_right_mono)
  finally show ?thesis by(simp add: field_simps)
qed

lemma interaction_bounded_prf_adversary: 
  fixes q :: nat
  assumes "ind_cpa.ibounded_by \<A> q"
  shows "prf.ibounded_by (prf_adversary \<A>) (1 + q)"
proof -
  fix \<eta>
  from assms have "ind_cpa.ibounded_by \<A> q" by blast
  then obtain q1 q2 where q: "q1 + q2 \<le> q"
    and [interaction_bound]: "interaction_any_bounded_by (fst \<A>) q1"
       "\<And>x \<sigma>. interaction_any_bounded_by (snd \<A> x \<sigma>) q2"
    unfolding ind_cpa.ibounded_by_def by(auto simp add: split_beta iadd_le_enat_iff)
  show "prf.ibounded_by (prf_adversary \<A>) (1 + q)" using q
    apply (simp only: prf_adversary_def Let_def split_def)
    apply -
    apply interaction_bound
      apply (auto simp add: iadd_SUP_le_iff SUP_le_iff add.assoc [symmetric] one_enat_def cong del: image_cong_simp cong add: SUP_cong_simp)
    done 
qed

lemma lossless_prf_adversary: "ind_cpa.lossless \<A> \<Longrightarrow> prf.lossless (prf_adversary \<A>)"
by(fastforce simp add: prf_adversary_def Let_def split_def ind_cpa.lossless_def intro: lossless_inline)

end

locale otp_\<eta> =
  fixes f :: "security \<Rightarrow> key \<Rightarrow> bool list \<Rightarrow> bool list"
  and len :: "security \<Rightarrow> nat"
  assumes length_f: "\<And>\<eta> xs ys. \<lbrakk> length xs = len \<eta>; length ys = len \<eta> \<rbrakk> \<Longrightarrow> length (f \<eta> xs ys) = len \<eta>"
  and negligible_len [negligible_intros]: "negligible (\<lambda>\<eta>. 1 / 2 ^ (len \<eta>))"
begin

interpretation otp "f \<eta>" "len \<eta>" for \<eta> by(unfold_locales)(rule length_f)
interpretation ind_cpa: ind_cpa "key_gen \<eta>" "encrypt \<eta>" "decrypt \<eta>" "valid_plain \<eta>" for \<eta> .
interpretation "prf": "prf" "key_gen \<eta>" "f \<eta>" "spmf_of_set (nlists UNIV (len \<eta>))" for \<eta> .

lemma prf_encrypt_secure_for:
  assumes [negligible_intros]: "negligible (\<lambda>\<eta>. prf.advantage \<eta> (prf_adversary \<eta> (\<A> \<eta>)))"
  and q: "\<And>\<eta>. ind_cpa.ibounded_by (\<A> \<eta>) (q \<eta>)" and [negligible_intros]: "polynomial q"
  and lossless: "\<And>\<eta>. ind_cpa.lossless (\<A> \<eta>)"
  shows "negligible (\<lambda>\<eta>. ind_cpa.advantage \<eta> (\<A> \<eta>))"
proof(rule negligible_mono)
  show "negligible (\<lambda>\<eta>. prf.advantage \<eta> (prf_adversary \<eta> (\<A> \<eta>)) + q \<eta> / 2 ^ len \<eta>)"
    by(intro negligible_intros)
  { fix \<eta>
    from \<open>ind_cpa.ibounded_by _ _\<close> have "ind_cpa.ibounded_by (\<A> \<eta>) (q \<eta>)" by blast
    moreover from lossless have "ind_cpa.lossless (\<A> \<eta>)" by blast
    hence "lossless_gpv \<I>_full (fst (\<A> \<eta>))" "\<And>cipher \<sigma>. lossless_gpv \<I>_full (snd (\<A> \<eta>) cipher \<sigma>)"
      by(auto simp add: ind_cpa.lossless_def)
    ultimately have "ind_cpa.advantage \<eta> (\<A> \<eta>) \<le> prf.advantage \<eta> (prf_adversary \<eta> (\<A> \<eta>)) + q \<eta> / 2 ^ len \<eta>"
      by(rule prf_encrypt_advantage) }
  hence "eventually (\<lambda>\<eta>. \<bar>ind_cpa.advantage \<eta> (\<A> \<eta>)\<bar> \<le> 1 * \<bar>prf.advantage \<eta> (prf_adversary \<eta> (\<A> \<eta>)) + q \<eta> / 2 ^ len \<eta>\<bar>) at_top"
    by(simp add: always_eventually ind_cpa.advantage_nonneg prf.advantage_nonneg)
  then show "(\<lambda>\<eta>. ind_cpa.advantage \<eta> (\<A> \<eta>)) \<in> O(\<lambda>\<eta>. prf.advantage \<eta> (prf_adversary \<eta> (\<A> \<eta>)) + q \<eta> / 2 ^ len \<eta>)"
    by(intro bigoI[where c=1]) simp
qed

end

end
