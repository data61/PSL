subsection\<open>Schnorr \<open>\<Sigma>\<close>-protocol\<close>

text\<open>In this section we show the Schnoor protocol \cite{DBLP:journals/joc/Schnorr91} is a \<open>\<Sigma>\<close>-protocol and then use it to construct a commitment scheme.
The security statements for the resulting commitment scheme come for free from our general proof of the construction.\<close> 

theory Schnorr_Sigma_Commit imports
  Commitment_Schemes
  Sigma_Protocols
  Cyclic_Group_Ext
  Discrete_Log
  Number_Theory_Aux
  Uniform_Sampling 
  "HOL-Number_Theory.Cong"
begin 

locale schnorr_base = 
  fixes \<G> :: "'grp cyclic_group" (structure)
  assumes prime_order: "prime (order \<G>)"
begin

lemma order_gt_0 [simp]: "order \<G> > 0"
  using prime_order prime_gt_0_nat by blast

text\<open>The types for the \<open>\<Sigma>\<close>-protocol.\<close>

type_synonym witness = "nat"
type_synonym rand = nat 
type_synonym 'grp' msg = "'grp'"
type_synonym response = nat
type_synonym challenge = nat
type_synonym 'grp' pub_in = "'grp'"

definition R_DL :: "('grp pub_in \<times> witness) set"
  where "R_DL = {(h, w). h = \<^bold>g [^] w}"

definition init :: "'grp pub_in \<Rightarrow> witness \<Rightarrow> (rand \<times> 'grp msg) spmf"
  where "init h w = do {
    r \<leftarrow> sample_uniform (order \<G>);
    return_spmf (r, \<^bold>g [^] r)}"

lemma  lossless_init: "lossless_spmf (init h w)"
  by(simp add: init_def)

definition "response r w c = return_spmf ((w*c + r) mod (order \<G>))"

lemma lossless_response: "lossless_spmf (response r w c)"
  by(simp add: response_def)

definition G :: "('grp pub_in \<times> witness) spmf" 
  where "G = do {
    w \<leftarrow> sample_uniform (order \<G>);
    return_spmf (\<^bold>g [^] w, w)}"

lemma lossless_G: "lossless_spmf G"
  by(simp add: G_def)

definition "challenge_space = {..< order \<G>}"

definition check :: "'grp pub_in \<Rightarrow> 'grp msg \<Rightarrow> challenge \<Rightarrow> response \<Rightarrow> bool"
  where "check h a e z = (a \<otimes> (h [^] e) = \<^bold>g [^] z \<and> a \<in> carrier \<G>)"

definition S2 :: "'grp \<Rightarrow> challenge \<Rightarrow> ('grp msg, response) sim_out spmf"
  where "S2 h e = do {
  c \<leftarrow> sample_uniform (order \<G>);
  let a = \<^bold>g [^] c \<otimes> (inv (h [^] e));
  return_spmf (a, c)}"

definition ss_adversary :: "'grp \<Rightarrow> ('grp msg, challenge, response) conv_tuple \<Rightarrow> ('grp msg, challenge, response) conv_tuple \<Rightarrow> nat spmf"
  where "ss_adversary x c1 c2 = do {
    let (a, e, z) = c1;
    let (a', e', z') = c2;
    return_spmf (if (e > e') then 
                    (nat ((int z - int z') * inverse ((e - e')) (order \<G>) mod order \<G>)) else 
                        (nat ((int z' - int z) * inverse ((e' - e)) (order \<G>) mod order \<G>)))}"

definition "valid_pub = carrier \<G>"

text\<open>We now use the Schnorr \<open>\<Sigma>\<close>-protocol use Schnorr to construct a commitment scheme.\<close>

type_synonym 'grp' ck = "'grp'" 
type_synonym 'grp' vk = "'grp' \<times> nat"
type_synonym plain = "nat"
type_synonym 'grp' commit = "'grp'"
type_synonym opening = "nat" 

text\<open>The adversary we use in the discrete log game to reduce the binding property to the discrete log assumption.\<close>

definition dis_log_\<A> :: "('grp ck, plain, 'grp commit, opening) bind_adversary \<Rightarrow> 'grp ck \<Rightarrow> nat spmf"
  where "dis_log_\<A> \<A> h = do {
  (c, e, z, e', z') \<leftarrow> \<A> h;
  _ :: unit \<leftarrow> assert_spmf (e > e' \<and> \<not> [e = e'] (mod order \<G>) \<and> (gcd (e - e') (order \<G>) = 1) \<and> c \<in> carrier \<G>);
  _ :: unit \<leftarrow> assert_spmf (((c \<otimes> h [^] e) = \<^bold>g [^] z) \<and> (c \<otimes> h [^] e') = \<^bold>g [^] z'); 
  return_spmf  (nat ((int z - int z') * inverse ((e - e')) (order \<G>) mod order \<G>))}"

sublocale discrete_log: dis_log \<G>
  unfolding dis_log_def by simp

end

locale schnorr_sigma_protocol = schnorr_base + cyclic_group \<G>
begin

sublocale Schnorr_\<Sigma>: \<Sigma>_protocols_base init response check R_DL S2 ss_adversary challenge_space valid_pub 
  apply unfold_locales
  by(simp add: R_DL_def valid_pub_def; blast)

text\<open>The Schnorr \<open>\<Sigma>\<close>-protocol is complete.\<close>

lemma completeness: "Schnorr_\<Sigma>.completeness"
proof-
  have "\<^bold>g [^] y \<otimes> (\<^bold>g [^] w') [^] e = \<^bold>g [^] (y + w' * e)" for y e w' :: nat
    using nat_pow_pow nat_pow_mult by simp
  then show ?thesis 
    unfolding Schnorr_\<Sigma>.completeness_game_def Schnorr_\<Sigma>.completeness_def 
    by(auto simp add: init_def response_def check_def pow_generator_mod R_DL_def add.commute bind_spmf_const)
qed

text\<open>The next two lemmas help us rewrite terms in the proof  of honest verfier zero knowledge.\<close>

lemma zr_rewrite: 
  assumes z: "z = (x*c + r) mod (order \<G>)" 
    and r: "r < order \<G>"
  shows "(z + (order \<G>)*x*c - x*c) mod (order \<G>) = r"
proof(cases "x = 0")
  case True
  then show ?thesis using assms by simp
next
  case x_neq_0: False
  then show ?thesis 
  proof(cases "c = 0")
    case True
    then show ?thesis 
      by (simp add: assms)
  next
    case False
    have cong: "[z + (order \<G>)*x*c = x*c + r] (mod (order \<G>))" 
      by (simp add: cong_def mult.assoc z)
    hence "[z + (order \<G>)*x*c - x*c = r] (mod (order \<G>))" 
    proof-
      have "z + (order \<G>)*x*c > x*c" 
        by (metis One_nat_def mult_less_cancel2 n_less_m_mult_n neq0_conv prime_gt_1_nat prime_order trans_less_add2 x_neq_0 False)
      then show ?thesis
        by (metis cong add_diff_inverse_nat cong_add_lcancel_nat less_imp_le linorder_not_le) 
    qed
    then show ?thesis
      by(simp add: cong_def r)
  qed
qed

lemma h_sub_rewrite:
  assumes "h = \<^bold>g [^] x" 
    and z: "z < order \<G>" 
  shows "\<^bold>g [^] ((z + (order \<G>)*x*c - x*c)) = \<^bold>g [^] z \<otimes> inv (h [^] c)" 
    (is "?lhs = ?rhs")
proof(cases "x = 0")
  case True
  then show ?thesis using assms by simp
next
  case x_neq_0: False
  then show ?thesis 
  proof-
    have "(z + order \<G> * x * c - x * c) = (z + (order \<G> * x * c - x * c))"
      using z by (simp add: less_imp_le_nat mult_le_mono) 
    then have lhs: "?lhs = \<^bold>g [^] z \<otimes> \<^bold>g [^] ((order \<G>)*x*c - x*c)" 
      by(simp add: nat_pow_mult)
    have " \<^bold>g [^] ((order \<G>)*x*c - x*c) =  inv (h [^] c)"  
    proof(cases "c = 0")
      case True
      then show ?thesis by simp
    next
      case False
      hence bound: "((order \<G>)*x*c - x*c) > 0"
        using assms x_neq_0 prime_gt_1_nat prime_order by auto 
      then have "\<^bold>g [^] ((order \<G>)*x*c- x*c) = \<^bold>g [^] int ((order \<G>)*x*c - x*c)"
        by (simp add: int_pow_int) 
      also have "... = \<^bold>g [^] int ((order \<G>)*x*c) \<otimes> inv (\<^bold>g [^] (x*c))" 
        by (metis bound generator_closed int_ops(6) int_pow_int of_nat_eq_0_iff of_nat_less_0_iff of_nat_less_iff int_pow_diff)
      also have "... = \<^bold>g [^] ((order \<G>)*x*c) \<otimes> inv (\<^bold>g [^] (x*c))"
        by (metis int_pow_int) 
      also have "... = \<^bold>g [^] ((order \<G>)*x*c) \<otimes> inv ((\<^bold>g [^] x) [^] c)"
        by(simp add: nat_pow_pow)
      also have "... = \<^bold>g [^] ((order \<G>)*x*c) \<otimes> inv (h [^] c)"
        using assms by simp
      also have "... = \<one> \<otimes> inv (h [^] c)"
        using generator_pow_order
        by (metis generator_closed mult_is_0 nat_pow_0 nat_pow_pow)
      ultimately show ?thesis
        by (simp add: assms(1)) 
    qed
    then show ?thesis using lhs by simp
  qed
qed

lemma hvzk_R_rewrite_grp:
  fixes x c r :: nat
  assumes "r < order \<G>"
  shows "\<^bold>g [^] (((x * c + order \<G> - r) mod order \<G> + order \<G> * x * c - x * c) mod order \<G>) = inv \<^bold>g [^] r"
    (is "?lhs = ?rhs")
proof-
  have "[(x * c + order \<G> - r) mod order \<G> + order \<G> * x * c - x * c = order \<G> - r] (mod order \<G>)"
  proof-
    have "[(x * c + order \<G> - r) mod order \<G> + order \<G> * x * c - x * c  
              = x * c + order \<G> - r + order \<G> * x * c - x * c] (mod order \<G>)"  
      by (smt cong_def One_nat_def add_diff_inverse_nat cong_diff_nat less_imp_le_nat linorder_not_less mod_add_left_eq mult.assoc n_less_m_mult_n prime_gt_1_nat prime_order trans_less_add2 zero_less_diff)
    hence "[(x * c + order \<G> - r) mod order \<G> + order \<G> * x * c - x * c  
              =  order \<G> - r + order \<G> * x * c] (mod order \<G>)"
      using assms by auto
    thus ?thesis 
      by (simp add: cong_def mult.assoc)
  qed
  hence "\<^bold>g [^] ((x * c + order \<G> - r) mod order \<G> + order \<G> * x * c - x * c) = \<^bold>g [^] (order \<G> - r)"
    using finite_carrier pow_generator_eq_iff_cong by blast
  thus ?thesis using neg_power_inverse 
    by (simp add: assms inverse_pow_pow pow_generator_mod)
qed

lemma hv_zk: 
  assumes "(h,x) \<in> R_DL"
  shows "Schnorr_\<Sigma>.R h x c = Schnorr_\<Sigma>.S h c"
  including monad_normalisation
proof-
  have "Schnorr_\<Sigma>.R h x c = do {
      r \<leftarrow> sample_uniform (order \<G>);
      let z = (x*c + r) mod (order \<G>);
      let a = \<^bold>g [^] ((z + (order \<G>)*x*c - x*c) mod (order \<G>)); 
      return_spmf (a,c,z)}"
    apply(simp add: Let_def Schnorr_\<Sigma>.R_def init_def response_def)
    using assms zr_rewrite R_DL_def 
    by(simp cong: bind_spmf_cong_simp)
  also have "... = do {
      z \<leftarrow> map_spmf (\<lambda> r. (x*c + r) mod (order \<G>)) (sample_uniform (order \<G>));
      let a = \<^bold>g [^] ((z + (order \<G>)*x*c - x*c) mod (order \<G>)); 
      return_spmf (a,c,z)}"
    by(simp add: bind_map_spmf o_def Let_def)
  also have "... = do {
      z \<leftarrow>  (sample_uniform (order \<G>));
      let a = \<^bold>g [^] ((z + (order \<G>)*x*c - x*c)); 
      return_spmf (a,c,z)}"
    by(simp add: samp_uni_plus_one_time_pad pow_generator_mod)
  also have "... = do {
      z \<leftarrow>  (sample_uniform (order \<G>));
      let a = \<^bold>g [^] z \<otimes> inv (h [^] c); 
      return_spmf (a,c,z)}"
    using h_sub_rewrite assms R_DL_def 
    by(simp cong: bind_spmf_cong_simp)
  ultimately show ?thesis 
    by(simp add: Schnorr_\<Sigma>.S_def S2_def map_spmf_conv_bind_spmf)
qed

text\<open>We can now prove that honest verifier zero knowledge holds for the Schnorr \<open>\<Sigma>\<close>-protocol.\<close>

lemma honest_verifier_ZK: 
  shows "Schnorr_\<Sigma>.HVZK"
  unfolding Schnorr_\<Sigma>.HVZK_def
  by(auto simp add: hv_zk R_DL_def S2_def check_def valid_pub_def challenge_space_def cyclic_group_assoc)

text\<open>It is left to prove the special soundness property. First we prove a lemma we use to rewrite a 
term in the special soundness proof and then prove the property itself.\<close>

lemma ss_rewrite:
  assumes "e' < e"
    and "e < order \<G>" 
    and a_mem:"a  \<in> carrier \<G>"
    and h_mem: "h \<in> carrier \<G>" 
    and a: "a \<otimes> h [^] e = \<^bold>g [^] z" 
    and a': "a \<otimes> h [^] e' = \<^bold>g [^] z'"
  shows  "h = \<^bold>g [^] ((int z - int z') * inverse ((e - e')) (order \<G>) mod int (order \<G>))"
proof-
  have gcd: "gcd (nat (int e - int e') mod (order \<G>)) (order \<G>) = 1" 
    using prime_field 
    by (metis Primes.prime_nat_def assms(1) assms(2) coprime_imp_gcd_eq_1 diff_is_0_eq less_imp_diff_less 
            mod_less nat_minus_as_int not_less schnorr_base.prime_order schnorr_base_axioms)
  have "a = \<^bold>g [^] z \<otimes> inv (h [^] e)" 
    using a a_mem 
    by (simp add: h_mem group.inv_solve_right)
  moreover have "a = \<^bold>g [^] z' \<otimes> inv (h [^] e')" 
    using a' a_mem 
    by (simp add: h_mem group.inv_solve_right)
  ultimately have "\<^bold>g [^] z \<otimes> h [^] e'  = \<^bold>g [^] z' \<otimes> h [^] e"
    using h_mem 
    by (metis (no_types, lifting) a a' h_mem a_mem cyclic_group_assoc cyclic_group_commute nat_pow_closed)
  moreover obtain t :: nat where  t: "h = \<^bold>g  [^] t" 
    using h_mem generatorE by blast
  ultimately have "\<^bold>g [^] (z + t * e')  = \<^bold>g [^] (z' +  t * e) "
    by (simp add: monoid.nat_pow_mult nat_pow_pow)
  hence "[z + t * e' = z' +  t * e] (mod  order \<G>)"
    using group_eq_pow_eq_mod order_gt_0 by blast
  hence "[int z + int t * int e' = int z' +  int t * int e] (mod  order \<G>)"
    using cong_int_iff by force
  hence "[int z - int z' = int t * int e - int t * int e'] (mod  order \<G>)"
    by (smt cong_iff_lin)
  hence "[int z - int z' = int t * (int e - int e')] (mod  order \<G>)"
    by (simp add: \<open>[int z - int z' = int t * int e - int t * int e'] (mod int (order \<G>))\<close> right_diff_distrib)
  hence "[int z - int z' = int t * (int e - int e')] (mod  order \<G>)"
    by (meson cong_diff cong_mod_left cong_mult cong_refl cong_trans)
  hence *: "[int z - int z' = int t * (int e - int e')] (mod  order \<G>)"
    using assms
    by (simp add: int_ops(9) of_nat_diff)
  hence "[int z - int z' = int t * nat (int e - int e')] (mod  order \<G>)"
    using assms 
    by auto
  hence **: "[(int z - int z') * fst (bezw ((nat (int e - int e'))) (order \<G>)) 
              = int t * (nat (int e - int e')
                  * fst (bezw ((nat (int e - int e'))) (order \<G>)))] (mod  order \<G>)"
    by (smt \<open>[int z - int z' = int t * (int e - int e')] (mod int (order \<G>))\<close> assms(1) assms(2)
          cong_scalar_right int_nat_eq less_imp_of_nat_less mod_less more_arith_simps(11) nat_less_iff of_nat_0_le_iff)
  hence "[(int z - int z') * fst (bezw ((nat (int e - int e'))) (order \<G>)) = int t * 1] (mod  order \<G>)"
    by (metis (no_types, hide_lams) gcd inverse assms(2) cong_scalar_left cong_trans less_imp_diff_less mod_less mult.comm_neutral nat_minus_as_int)
  hence "[(int z - int z') * fst (bezw ((nat (int e - int e'))) (order \<G>)) 
              = t] (mod  order \<G>)" by simp
  hence "[ ((int z - int z') * fst (bezw ((nat (int e - int e'))) (order \<G>)))mod order \<G> 
              = t] (mod  order \<G>)"
    using cong_mod_left by blast
  hence  **: "[nat (((int z - int z') * fst (bezw ((nat (int e - int e'))) (order \<G>)))mod order \<G>)
              = t] (mod  order \<G>)"
    by (metis Euclidean_Division.pos_mod_sign cong_int_iff int_nat_eq of_nat_0_less_iff order_gt_0)
  hence "\<^bold>g [^] (nat (((int z - int z') * fst (bezw ((nat (int e - int e'))) (order \<G>)))mod order \<G>)) = \<^bold>g [^] t"
    using cyclic_group.pow_generator_eq_iff_cong cyclic_group_axioms order_gt_0 order_gt_0_iff_finite by blast
  thus ?thesis using t 
    by (smt Euclidean_Division.pos_mod_sign discrete_log.order_gt_0 int_pow_def2 nat_minus_as_int of_nat_0_less_iff)
qed

text\<open>The special soundness property for the Schnorr \<open>\<Sigma>\<close>-protocol.\<close>

lemma special_soundness:
  shows "Schnorr_\<Sigma>.special_soundness"
  unfolding Schnorr_\<Sigma>.special_soundness_def 
  by(auto simp add: valid_pub_def ss_rewrite challenge_space_def split_def ss_adversary_def check_def R_DL_def Let_def) 

text\<open>We are now able to prove that the Schnorr \<open>\<Sigma>\<close>-protocol is a \<open>\<Sigma>\<close>-protocol, the proof comes from the properties of
completeness, HVZK and special soundness we have previously proven.\<close>

theorem sigma_protocol:
  shows "Schnorr_\<Sigma>.\<Sigma>_protocol"
  by(simp add: Schnorr_\<Sigma>.\<Sigma>_protocol_def completeness honest_verifier_ZK special_soundness)

text\<open>Having proven the \<open>\<Sigma>\<close>-protocol property is satisfied we can show the commitment scheme we construct from the 
Schnorr \<open>\<Sigma>\<close>-protocol has the desired properties. This result comes with very little proof effort as we can instantiate
our general proof.\<close>

sublocale Schnorr_\<Sigma>_commit: \<Sigma>_protocols_to_commitments init response check R_DL S2 ss_adversary challenge_space valid_pub G
  unfolding \<Sigma>_protocols_to_commitments_def \<Sigma>_protocols_to_commitments_axioms_def
  apply(auto simp add: \<Sigma>_protocols_base_def)
       apply(simp add: R_DL_def valid_pub_def)
      apply(auto simp add: sigma_protocol lossless_G lossless_init lossless_response)
  by(simp add: R_DL_def G_def)

lemma "Schnorr_\<Sigma>_commit.abstract_com.correct"
  by(fact Schnorr_\<Sigma>_commit.commit_correct)

lemma "Schnorr_\<Sigma>_commit.abstract_com.perfect_hiding_ind_cpa \<A>"
  by(fact Schnorr_\<Sigma>_commit.perfect_hiding)

lemma rel_adv_eq_dis_log_adv: 
  "Schnorr_\<Sigma>_commit.rel_advantage \<A> = discrete_log.advantage \<A>"
proof-
  have "Schnorr_\<Sigma>_commit.rel_game \<A> = discrete_log.dis_log \<A>"
    unfolding Schnorr_\<Sigma>_commit.rel_game_def discrete_log.dis_log_def
    by(auto intro: try_spmf_cong bind_spmf_cong[OF refl] 
       simp add: G_def R_DL_def cong_less_modulus_unique_nat group_eq_pow_eq_mod finite_carrier pow_generator_eq_iff_cong)
  thus ?thesis
    using Schnorr_\<Sigma>_commit.rel_advantage_def discrete_log.advantage_def by simp
qed

lemma bind_advantage_bound_dis_log: 
  "Schnorr_\<Sigma>_commit.abstract_com.bind_advantage \<A> \<le> discrete_log.advantage (Schnorr_\<Sigma>_commit.adversary \<A>)"
  using Schnorr_\<Sigma>_commit.bind_advantage rel_adv_eq_dis_log_adv by simp

end

locale schnorr_asymp = 
  fixes \<G> :: "nat \<Rightarrow> 'grp cyclic_group"
  assumes schnorr: "\<And>\<eta>. schnorr_sigma_protocol (\<G> \<eta>)"
begin

sublocale schnorr_sigma_protocol "\<G> \<eta>" for \<eta> 
  by(simp add: schnorr)

text\<open>The \<open>\<Sigma>\<close>-protocol statement comes easily in the asymptotic setting.\<close>

theorem sigma_protocol:
  shows "Schnorr_\<Sigma>.\<Sigma>_protocol n"
  by(simp add: sigma_protocol)

text\<open>We now show the statements of security for the commitment scheme in the asymptotic setting, the main difference is that
we are able to show the binding advantage is negligible in the security parameter.\<close>

lemma asymp_correct: "Schnorr_\<Sigma>_commit.abstract_com.correct n" 
  using  Schnorr_\<Sigma>_commit.commit_correct by simp

lemma asymp_perfect_hiding: "Schnorr_\<Sigma>_commit.abstract_com.perfect_hiding_ind_cpa n (\<A> n)"
  using Schnorr_\<Sigma>_commit.perfect_hiding by blast

lemma asymp_computational_binding: 
  assumes "negligible (\<lambda> n. discrete_log.advantage n (Schnorr_\<Sigma>_commit.adversary n (\<A> n)))"
  shows "negligible (\<lambda> n. Schnorr_\<Sigma>_commit.abstract_com.bind_advantage n (\<A> n))"
  using Schnorr_\<Sigma>_commit.bind_advantage assms Schnorr_\<Sigma>_commit.abstract_com.bind_advantage_def negligible_le bind_advantage_bound_dis_log by auto

end

end
