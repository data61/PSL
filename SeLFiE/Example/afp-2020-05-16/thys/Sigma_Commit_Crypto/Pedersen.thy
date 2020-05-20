subsection\<open>Pedersen Commitment Scheme\<close>

text\<open>The Pedersen commitment scheme \cite{BLP:conf/crypto/Pedersen91} is a commitment scheme based on a cyclic group. We use the 
construction of cyclic groups from CryptHOL to formalise the commitment scheme. We prove perfect hiding
and computational binding, with a reduction to the discrete log problem. We a proof of the Pedersen commitment scheme
is realised in the instantiation of the Schnorr \<open>\<Sigma>\<close>-protocol with the general construction of commitment schemes 
from \<open>\<Sigma>\<close>-protocols. The commitment scheme that is realised there however take the inverse of the message in the commitment 
phase due to the construction of the simulator in the \<open>\<Sigma>\<close>-protocol proof. The two schemes are in some way equal however
as we do not have a well defined notion of equality for commitment schemes we keep this section of the formalisation. This 
also serves as reference to the formal proof of the Pedersen commitment scheme we provide in \cite{DBLP:conf/post/ButlerAG19}.\<close>

theory Pedersen imports
  Commitment_Schemes
  "HOL-Number_Theory.Cong"
  Cyclic_Group_Ext
  Discrete_Log
  Number_Theory_Aux
  Uniform_Sampling
begin

locale pedersen_base = 
  fixes \<G> :: "'grp cyclic_group" (structure)
  assumes prime_order: "prime (order \<G>)"
begin

lemma order_gt_0 [simp]: "order \<G> > 0"
  by (simp add: prime_gt_0_nat prime_order)

type_synonym 'grp' ck = "'grp'"
type_synonym 'grp' vk = "'grp'"
type_synonym plain = "nat"
type_synonym 'grp' commit = "'grp'"
type_synonym opening = "nat"

definition key_gen :: "('grp ck \<times> 'grp vk) spmf"
where 
  "key_gen = do {
    x :: nat \<leftarrow> sample_uniform (order \<G>);
    let h = \<^bold>g [^] x;
    return_spmf (h, h) 
  }" 

definition commit :: "'grp ck \<Rightarrow> plain \<Rightarrow> ('grp commit \<times> opening) spmf"
where 
  "commit ck m = do {
    d :: nat \<leftarrow> sample_uniform (order \<G>);
    let c = (\<^bold>g [^] d) \<otimes> (ck [^] m);
    return_spmf (c,d) 
  }"

definition commit_inv :: "'grp ck \<Rightarrow> plain \<Rightarrow> ('grp commit \<times> opening) spmf"
where 
  "commit_inv ck m = do {
    d :: nat \<leftarrow> sample_uniform (order \<G>);
    let c = (\<^bold>g [^] d) \<otimes> (inv ck [^] m);
    return_spmf (c,d) 
  }"

definition verify :: "'grp vk \<Rightarrow> plain \<Rightarrow> 'grp commit \<Rightarrow> opening \<Rightarrow> bool"
where 
  "verify v_key m c d = (c = (\<^bold>g [^] d \<otimes>  v_key [^] m))"

definition valid_msg :: "plain \<Rightarrow> bool"
  where "valid_msg msg \<equiv> (msg < order \<G>)"

definition dis_log_\<A> :: "('grp ck, plain, 'grp commit, opening) bind_adversary \<Rightarrow> 'grp ck \<Rightarrow> nat spmf"
where "dis_log_\<A> \<A> h = do {
  (c, m, d, m', d') \<leftarrow> \<A> h;
  _ :: unit \<leftarrow> assert_spmf (m \<noteq> m'  \<and> valid_msg m \<and> valid_msg m');
  _ :: unit \<leftarrow> assert_spmf (c = \<^bold>g [^] d \<otimes> h [^] m \<and> c = \<^bold>g [^] d' \<otimes> h [^] m'); 
  return_spmf  (if (m > m') then (nat ((int d' - int d) * inverse (m - m') (order \<G>) mod order \<G>)) else 
                  (nat ((int d - int d') * inverse (m' - m) (order \<G>) mod order \<G>)))}"

sublocale ped_commit: abstract_commitment key_gen commit verify valid_msg .

sublocale discrete_log: dis_log _ 
  unfolding dis_log_def by(simp)

end

locale pedersen = pedersen_base + cyclic_group \<G> 
begin 

lemma mod_one_cancel: assumes "[int y * z * x = y' * x] (mod order \<G>)" and "[z * x = 1] (mod order \<G>)"
  shows "[int y = y' * x] (mod order \<G>)"
  by (metis assms Groups.mult_ac(2) cong_scalar_right cong_sym_eq cong_trans more_arith_simps(11) more_arith_simps(5))

lemma dis_log_break:
  fixes d d' m m' :: nat
  assumes c: " \<^bold>g [^] d' \<otimes> (\<^bold>g [^] y) [^] m' = \<^bold>g [^] d \<otimes> (\<^bold>g [^] y) [^] m"
    and y_less_order: "y < order \<G>"
    and m_ge_m': "m > m'"
    and m: "m < order \<G>"
  shows "y = nat ((int d' - int d) * (fst (bezw ((m - m')) (order \<G>))) mod order \<G>)" 
proof -
  have mm': "\<not> [m = m'] (mod order \<G>)"
    using m m_ge_m' basic_trans_rules(19) cong_less_modulus_unique_nat by blast
  hence gcd: "int (gcd ((m - m')) (order \<G>)) = 1" 
    using assms(3) assms(4) prime_field prime_order by auto
  have "\<^bold>g [^] (d + y * m) = \<^bold>g [^] (d' + y * m')" 
    using c by (simp add: nat_pow_mult nat_pow_pow)
  hence "[d + y * m = d' + y * m'] (mod order \<G>)"
    by(simp add: pow_generator_eq_iff_cong finite_carrier)
  hence "[int d + int y * int m = int d' + int y * int m'] (mod order \<G>)" 
    using cong_int_iff by force
  from cong_diff[OF this cong_refl, of "int d + int y * int m'"]
  have "[int y * int (m - m') = int d' - int d] (mod order \<G>)" using m_ge_m'
    by(simp add: int_distrib of_nat_diff)
  hence *: "[int y * int (m - m') * (fst (bezw ((m - m')) (order \<G>))) = (int d' - int d) * (fst (bezw ((m - m')) (order \<G>)))] (mod order \<G>)"
    by (simp add: cong_scalar_right)
  hence "[int y * (int (m - m') * (fst (bezw ((m - m')) (order \<G>)))) = (int d' - int d) * (fst (bezw ((m - m')) (order \<G>)))] (mod order \<G>)"
    by (simp add: more_arith_simps(11))
  hence "[int y * 1 = (int d' - int d) * (fst (bezw ((m - m')) (order \<G>)))] (mod order \<G>)"
    using inverse gcd 
    by (smt Groups.mult_ac(2) Number_Theory_Aux.inverse Totient.of_nat_eq_1_iff * cong_def int_ops(9) mod_mult_right_eq mod_one_cancel)
  hence "[int y = (int d' - int d) * (fst (bezw ((m - m')) (order \<G>)))] (mod order \<G>)" by simp
  hence "y mod order \<G> = (int d' - int d) * (fst (bezw ((m - m')) (order \<G>))) mod order \<G>"
    using cong_def zmod_int by auto
  thus ?thesis using y_less_order by simp
qed

lemma dis_log_break':
  assumes "y < order \<G>"
    and "\<not> m' < m"
    and "m \<noteq> m'"
    and m: "m' < order \<G>"
    and "\<^bold>g [^] d \<otimes> (\<^bold>g [^] y) [^] m = \<^bold>g [^] d' \<otimes> (\<^bold>g [^] y) [^] m'"
  shows "y = nat ((int d - int d') * fst (bezw ((m' - m)) (order \<G>)) mod int (order \<G>))"
proof-
  have "m' > m" using assms 
    using group_eq_pow_eq_mod nat_neq_iff order_gt_0  by blast
  thus ?thesis 
    using dis_log_break[of d y m d' m' ]assms cong_sym_eq assms by blast  
qed

lemma set_spmf_samp_uni [simp]: "set_spmf (sample_uniform (order \<G>)) = {x. x < order \<G>}"
  by(auto simp add: sample_uniform_def)

lemma correct:
  shows "spmf (ped_commit.correct_game m) True  = 1" 
  using finite_carrier order_gt_0_iff_finite  
  apply(simp add: abstract_commitment.correct_game_def Let_def commit_def verify_def)
    by(simp add: key_gen_def Let_def bind_spmf_const cong: bind_spmf_cong_simp)

theorem abstract_correct:
  shows "ped_commit.correct"
  unfolding abstract_commitment.correct_def using correct by simp

lemma perfect_hiding:
  shows "spmf (ped_commit.hiding_game_ind_cpa \<A>) True - 1/2 = 0"
  including monad_normalisation
proof -
  obtain \<A>1 \<A>2 where [simp]: "\<A> = (\<A>1, \<A>2)" by(cases \<A>)
  note [simp] = Let_def split_def 
  have "ped_commit.hiding_game_ind_cpa (\<A>1, \<A>2) = TRY do {
    (ck,vk) \<leftarrow> key_gen;
    ((m0, m1), \<sigma>) \<leftarrow> \<A>1 vk;
    _ :: unit \<leftarrow> assert_spmf (valid_msg m0 \<and> valid_msg m1);
    b \<leftarrow> coin_spmf;  
    (c,d) \<leftarrow> commit ck (if b then m0 else m1);
    b' \<leftarrow> \<A>2 c \<sigma>;
    return_spmf (b' = b)} ELSE coin_spmf"
      by(simp add: abstract_commitment.hiding_game_ind_cpa_def)
  also have "... = TRY do {
    x :: nat \<leftarrow> sample_uniform (order \<G>);
    let h = \<^bold>g [^] x;
    ((m0, m1), \<sigma>) \<leftarrow> \<A>1 h;
    _ :: unit \<leftarrow> assert_spmf (valid_msg m0 \<and> valid_msg m1);
     b \<leftarrow> coin_spmf; 
    d :: nat \<leftarrow> sample_uniform (order \<G>);
    let c = ((\<^bold>g [^] d) \<otimes> (h [^] (if b then m0 else m1)));
    b' \<leftarrow> \<A>2 c \<sigma>;
    return_spmf (b' = b)} ELSE coin_spmf"
      by(simp add: commit_def key_gen_def)
  also have "... = TRY do {
    x :: nat \<leftarrow> sample_uniform (order \<G>);
    let h = (\<^bold>g [^] x);
    ((m0, m1), \<sigma>) \<leftarrow> \<A>1 h;
    _ :: unit \<leftarrow> assert_spmf (valid_msg m0 \<and> valid_msg m1);
    b \<leftarrow> coin_spmf;  
    z \<leftarrow> map_spmf (\<lambda>z.  \<^bold>g [^] z \<otimes> (h [^] (if b then m0 else m1))) (sample_uniform (order \<G>));
    guess :: bool \<leftarrow> \<A>2 z \<sigma>;
    return_spmf(guess = b)} ELSE coin_spmf"
      by(simp add: bind_map_spmf o_def)
  also have "... = TRY do {
    x :: nat \<leftarrow> sample_uniform (order \<G>);
    let h = (\<^bold>g [^] x);
    ((m0, m1), \<sigma>) \<leftarrow> \<A>1 h;
    _ :: unit \<leftarrow> assert_spmf (valid_msg m0 \<and> valid_msg m1);
    b \<leftarrow> coin_spmf;  
    z \<leftarrow> map_spmf (\<lambda>z. \<^bold>g [^] z) (sample_uniform (order \<G>));
    guess :: bool \<leftarrow> \<A>2 z \<sigma>;
    return_spmf(guess = b)} ELSE coin_spmf"
    by(simp add: sample_uniform_one_time_pad)
  also have "... = TRY do {
    x :: nat \<leftarrow> sample_uniform (order \<G>);
    let h = (\<^bold>g [^] x);
    ((m0, m1), \<sigma>) \<leftarrow> \<A>1 h;
    _ :: unit \<leftarrow> assert_spmf (valid_msg m0 \<and> valid_msg m1);
    z \<leftarrow> map_spmf (\<lambda>z.  \<^bold>g [^] z)  (sample_uniform (order \<G>));
    guess :: bool \<leftarrow> \<A>2 z \<sigma>;
    map_spmf((=) guess) coin_spmf} ELSE coin_spmf"
      by(simp add: map_spmf_conv_bind_spmf)
  also have "... = coin_spmf"
     by(auto simp add: bind_spmf_const map_eq_const_coin_spmf try_bind_spmf_lossless2' scale_bind_spmf weight_spmf_le_1 scale_scale_spmf)
  ultimately show ?thesis by(simp add: spmf_of_set)
qed

theorem abstract_perfect_hiding: 
  shows "ped_commit.perfect_hiding_ind_cpa \<A>"
proof-
  have "spmf (ped_commit.hiding_game_ind_cpa \<A>) True - 1/2 = 0" 
    using perfect_hiding by fastforce
  thus ?thesis 
    by(simp add: abstract_commitment.perfect_hiding_ind_cpa_def abstract_commitment.hiding_advantage_ind_cpa_def)
qed

lemma bind_output_cong:  
  assumes "x < order \<G>" 
  shows "(x = nat ((int b - int ab) * fst (bezw (aa - ac) (order \<G>)) mod int (order \<G>)))
            \<longleftrightarrow> [x = nat ((int b - int ab) * fst (bezw (aa - ac) (order \<G>)) mod int (order \<G>))] (mod order \<G>)"
  using assms cong_less_modulus_unique_nat nat_less_iff by auto

lemma bind_game_eq_dis_log:
  shows "ped_commit.bind_game \<A> = discrete_log.dis_log (dis_log_\<A> \<A>)"
proof-
  note [simp] = Let_def split_def
  have "ped_commit.bind_game \<A> = TRY do {
    (ck,vk) \<leftarrow> key_gen;
    (c, m, d, m', d') \<leftarrow> \<A> ck;
    _ :: unit \<leftarrow> assert_spmf(m \<noteq> m' \<and> valid_msg m \<and> valid_msg m'); 
    let b = verify vk m c d;
    let b' = verify vk m' c d';
    _ :: unit \<leftarrow> assert_spmf (b \<and> b');
    return_spmf True} ELSE return_spmf False" 
    by(simp add: abstract_commitment.bind_game_alt_def) 
  also have "... = TRY do {
    x :: nat \<leftarrow> sample_uniform (Coset.order \<G>);
    (c, m, d, m', d') \<leftarrow> \<A> (\<^bold>g [^] x);
    _ :: unit \<leftarrow> assert_spmf (m \<noteq> m' \<and> valid_msg m \<and> valid_msg m'); 
    _ :: unit \<leftarrow> assert_spmf (c = \<^bold>g [^] d \<otimes>  (\<^bold>g [^] x) [^] m \<and> c = \<^bold>g [^] d' \<otimes> (\<^bold>g [^] x) [^] m');
    return_spmf True} ELSE return_spmf False" 
    by(simp add: verify_def key_gen_def)
  also have "... = TRY do {
    x :: nat \<leftarrow> sample_uniform (order \<G>);
    (c, m, d, m', d') \<leftarrow> \<A> (\<^bold>g [^] x);
    _ :: unit \<leftarrow> assert_spmf (m \<noteq> m' \<and> valid_msg m \<and> valid_msg m'); 
    _ :: unit \<leftarrow> assert_spmf (c = \<^bold>g [^] d \<otimes>  (\<^bold>g [^] x) [^] m \<and> c = \<^bold>g [^] d' \<otimes> (\<^bold>g [^] x) [^] m');
    return_spmf (x = (if (m > m') then (nat ((int d' - int d) * (fst (bezw ((m - m')) (order \<G>))) mod order \<G>)) else 
                  (nat ((int d - int d') * (fst (bezw ((m' - m)) (order \<G>))) mod order \<G>))))} ELSE return_spmf False" 
    apply(intro try_spmf_cong bind_spmf_cong[OF refl]; clarsimp?)
     apply(auto simp add: valid_msg_def)
     apply(intro bind_spmf_cong[OF refl]; clarsimp?)+
     apply(simp add: dis_log_break)
    apply(intro bind_spmf_cong[OF refl]; clarsimp?)+
    by(simp add: dis_log_break')
  ultimately show ?thesis 
    apply(simp add: discrete_log.dis_log_def dis_log_\<A>_def cong: bind_spmf_cong_simp)
    apply(intro try_spmf_cong bind_spmf_cong[OF refl]; clarsimp?)+
    using bind_output_cong by auto
qed

theorem pedersen_bind: "ped_commit.bind_advantage \<A> = discrete_log.advantage (dis_log_\<A> \<A>)"
  unfolding abstract_commitment.bind_advantage_def discrete_log.advantage_def 
  using bind_game_eq_dis_log by simp

end

locale pedersen_asymp = 
  fixes \<G> :: "nat \<Rightarrow> 'grp cyclic_group"
  assumes pedersen: "\<And>\<eta>. pedersen (\<G> \<eta>)"
begin
  
sublocale pedersen "\<G> \<eta>" for \<eta> by(simp add: pedersen)

theorem pedersen_correct_asym: 
 shows "ped_commit.correct n"
  using abstract_correct by simp
              
theorem pedersen_perfect_hiding_asym:
  shows "ped_commit.perfect_hiding_ind_cpa n (\<A> n)"
    by (simp add: abstract_perfect_hiding)

theorem pedersen_bind_asym: 
  shows "negligible (\<lambda> n. ped_commit.bind_advantage n (\<A> n)) 
            \<longleftrightarrow> negligible (\<lambda> n. discrete_log.advantage n (dis_log_\<A> n (\<A> n)))" 
  by(simp add: pedersen_bind)

end

end
