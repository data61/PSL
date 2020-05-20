subsection\<open>Okamoto \<open>\<Sigma>\<close>-protocol\<close>

theory Okamoto_Sigma_Commit imports
  Commitment_Schemes
  Sigma_Protocols
  Cyclic_Group_Ext
  Discrete_Log
  "HOL.GCD"
  Number_Theory_Aux
  Uniform_Sampling 
begin 

locale okamoto_base = 
  fixes \<G> :: "'grp cyclic_group" (structure)
    and x :: nat
  assumes prime_order: "prime (order \<G>)"
begin

definition "g' = \<^bold>g [^] x"

lemma order_gt_1: "order \<G> > 1" 
  using prime_order 
  using prime_gt_1_nat by blast

lemma order_gt_0 [simp]:"order \<G> > 0" 
  using order_gt_1 by simp

definition "response r w e = do {
  let (r1,r2) = r;
  let (x1,x2) = w;
  let z1 = (e * x1 + r1) mod (order \<G>);
  let z2 = (e * x2 + r2) mod (order \<G>);
  return_spmf ((z1,z2))}"

lemma lossless_response: "lossless_spmf (response r w e)"
  by(simp add: response_def split_def)

type_synonym witness = "nat \<times> nat"
type_synonym rand = "nat \<times> nat"
type_synonym 'grp' msg = "'grp'"
type_synonym response = "(nat \<times> nat)"
type_synonym challenge = nat
type_synonym 'grp' pub_in = "'grp'"

definition init :: "'grp pub_in \<Rightarrow> witness \<Rightarrow> (rand \<times> 'grp msg) spmf"
  where "init y w = do {
    let (x1,x2) = w; 
    r1 \<leftarrow> sample_uniform (order \<G>);
    r2 \<leftarrow> sample_uniform (order \<G>);
    return_spmf ((r1,r2), \<^bold>g [^] r1 \<otimes> g' [^] r2)}"

lemma lossless_init: "lossless_spmf (init h  w)"
  by(simp add: init_def)

definition check :: "'grp pub_in \<Rightarrow> 'grp msg \<Rightarrow> challenge \<Rightarrow> response \<Rightarrow> bool"
  where "check h a e z = (\<^bold>g [^] (fst z) \<otimes> g' [^] (snd z) = a \<otimes> (h [^] e) \<and> a \<in> carrier \<G>)"

definition R :: "('grp pub_in \<times> witness) set"
  where "R \<equiv> {(h, w). (h = \<^bold>g [^] (fst w) \<otimes> g' [^] (snd w))}"

definition G :: "('grp pub_in \<times> witness) spmf"
  where "G = do {
    w1 \<leftarrow> sample_uniform (order \<G>);
    w2 \<leftarrow> sample_uniform (order \<G>);
    return_spmf (\<^bold>g [^] w1 \<otimes> g' [^] w2 , (w1,w2))}"

definition "challenge_space = {..< order \<G>}"

lemma lossless_G: "lossless_spmf G"
  by(simp add: G_def)

definition S2 :: "'grp pub_in \<Rightarrow> challenge \<Rightarrow> ('grp msg, response) sim_out spmf"
  where "S2 h c = do {
    z1 \<leftarrow> sample_uniform  (order \<G>);
    z2 \<leftarrow> sample_uniform  (order \<G>);
  let a =  (\<^bold>g [^] z1 \<otimes> g' [^] z2) \<otimes> (inv h [^] c); 
  return_spmf (a, (z1,z2))}"

definition R2 :: "'grp pub_in \<Rightarrow> witness \<Rightarrow> challenge \<Rightarrow> ('grp msg, challenge, response) conv_tuple spmf"
  where "R2 h w c = do { 
    let (x1,x2) = w; 
    r1 \<leftarrow> sample_uniform (order \<G>);
    r2 \<leftarrow> sample_uniform (order \<G>);
    let z1 = (c * x1 + r1) mod (order \<G>);
    let z2 = (c * x2 + r2) mod (order \<G>);
    return_spmf (\<^bold>g [^] r1 \<otimes> g' [^] r2 ,c,(z1,z2))}"

definition ss_adversary :: "'grp \<Rightarrow> ('grp msg, challenge, response) conv_tuple \<Rightarrow> ('grp msg, challenge, response) conv_tuple \<Rightarrow> (nat \<times> nat) spmf"
  where "ss_adversary y c1 c2 = do {
    let (a, e, (z1,z2)) = c1;
    let (a', e', (z1',z2')) = c2;
    return_spmf (if (e > e') then (nat ((int z1 - int z1') * inverse (e - e') (order \<G>) mod order \<G>)) else 
                      (nat ((int z1' - int z1) * inverse (e' - e) (order \<G>) mod order \<G>)), 
                 if (e > e') then (nat ((int z2  - int z2') * inverse (e - e') (order \<G>) mod order \<G>)) else 
                      (nat ((int z2' - int z2) * inverse (e' - e) (order \<G>) mod order \<G>)))}"

definition "valid_pub = carrier \<G>"
end

locale okamoto = okamoto_base + cyclic_group \<G>
begin

lemma g'_in_carrier [simp]: "g' \<in> carrier \<G>" 
  using g'_def by auto

sublocale \<Sigma>_protocols_base: \<Sigma>_protocols_base init response check R S2 ss_adversary challenge_space valid_pub 
  by unfold_locales (auto simp add: R_def valid_pub_def)

lemma "\<Sigma>_protocols_base.R h w c = R2 h w c"
  by(simp add: \<Sigma>_protocols_base.R_def R2_def; simp add: init_def split_def response_def)

lemma completeness: 
  shows "\<Sigma>_protocols_base.completeness"
proof-
  have "(\<^bold>g [^] ((e * fst w' + y) mod order \<G>) \<otimes> g' [^] ((e * snd w' + ya) mod order \<G>) = \<^bold>g [^] y \<otimes> g' [^] ya \<otimes> (\<^bold>g [^] fst w' \<otimes> g' [^] snd w') [^] e)" 
    for e y ya :: nat and w' :: "nat \<times> nat"
  proof-
    have "\<^bold>g [^] ((e * fst w' + y) mod order \<G>) \<otimes> g' [^] ((e * snd w' + ya) mod order \<G>) = \<^bold>g [^] ((y + e * fst w')) \<otimes> g' [^] ((ya + e * snd w'))"
      by (simp add: cyclic_group.pow_carrier_mod cyclic_group_axioms g'_def add.commute pow_generator_mod)
    also have "... = \<^bold>g [^] y \<otimes> \<^bold>g [^] (e * fst w') \<otimes> g' [^] ya \<otimes> g' [^] (e * snd w')" 
      by (simp add: g'_def m_assoc nat_pow_mult)
    also have "... = \<^bold>g [^] y \<otimes> g' [^] ya \<otimes> \<^bold>g [^] (e * fst w') \<otimes> g' [^] (e * snd w')" 
      by (smt add.commute g'_def generator_closed m_assoc nat_pow_closed nat_pow_mult nat_pow_pow)
    also have "... = \<^bold>g [^] y \<otimes> g' [^] ya \<otimes> ((\<^bold>g [^] fst w') [^] e \<otimes> (g' [^] snd w') [^] e)" 
      by (simp add: m_assoc mult.commute nat_pow_pow)
    also have "... =  \<^bold>g [^] y \<otimes> g' [^] ya \<otimes> ((\<^bold>g [^] fst w' \<otimes> g' [^] snd w') [^] e)"   
      by (smt power_distrib g'_def generator_closed mult.commute nat_pow_closed nat_pow_mult nat_pow_pow)
    ultimately show ?thesis by simp
  qed
  thus ?thesis 
  unfolding \<Sigma>_protocols_base.completeness_def \<Sigma>_protocols_base.completeness_game_def
  by(simp add: R_def challenge_space_def init_def check_def response_def split_def bind_spmf_const)
qed

lemma hvzk_z_r:
  assumes r1: "r1 < order \<G>" 
  shows "r1 = ((r1 + c * (x1 :: nat)) mod (order \<G>) + order \<G> * c * x1 - c * x1) mod (order \<G>)"
proof(cases "x1 = 0")
  case True
  then show ?thesis using r1 by simp
next
  case x1_neq_0: False
  have z1_eq: "[(r1 + c * x1) mod (order \<G>) + order \<G> * c * x1 = r1 + c * x1] (mod (order \<G>))"
    using gr_implies_not_zero order_gt_1
    by (simp add: Groups.mult_ac(1) cong_def)
  hence "[(r1 + c * x1) mod (order \<G>) + order \<G> * c * x1 - c * x1 = r1] (mod (order \<G>))" 
  proof(cases "c = 0")
    case True
    then show ?thesis 
      using z1_eq by auto
  next
    case False
    have "order \<G> * c * x1 - c * x1 > 0" using x1_neq_0 False 
      using prime_gt_1_nat prime_order by auto 
    thus ?thesis 
      by (smt Groups.add_ac(2) add_diff_inverse_nat cong_add_lcancel_nat diff_is_0_eq le_simps(1) neq0_conv trans_less_add2 z1_eq zero_less_diff)
  qed
  thus ?thesis 
    by (simp add: r1 cong_def)
qed

lemma hvzk_z1_r1_tuple_rewrite: 
  assumes r1: "r1 < order \<G>" 
  shows "(\<^bold>g [^] r1 \<otimes> g' [^] r2, c, (r1 + c * x1) mod order \<G>, (r2 + c * x2) mod order \<G>) = 
              (\<^bold>g [^] (((r1 + c * x1) mod order \<G> + order \<G> * c * x1 - c * x1) mod order \<G>)  
                  \<otimes> g' [^] r2, c, (r1 + c * x1) mod order \<G>, (r2 + c * x2) mod order \<G>)"
proof-
  have "\<^bold>g [^] r1 = \<^bold>g [^] (((r1 + c * x1) mod order \<G> + order \<G> * c * x1 - c * x1) mod order \<G>)"
    using assms hvzk_z_r by simp
  thus ?thesis by argo
qed

lemma hvzk_z2_r2_tuple_rewrite: 
  assumes "xb < order \<G>" 
  shows "(\<^bold>g [^] (((x' + xa * x1) mod order \<G> + order \<G> * xa * x1 - xa * x1) mod order \<G>) 
            \<otimes> g' [^] xb, xa, (x' + xa * x1) mod order \<G>, (xb + xa * x2) mod order \<G>) =
               (\<^bold>g [^] (((x' + xa * x1) mod order \<G> + order \<G> * xa * x1 - xa * x1) mod order \<G>) 
                \<otimes> g' [^] (((xb + xa * x2) mod order \<G> + order \<G> * xa * x2 - xa * x2) mod order \<G>), xa, (x' + xa * x1) mod order \<G>, (xb + xa * x2) mod order \<G>)"
proof-
  have "g' [^] xb = g' [^] (((xb + xa * x2) mod order \<G> + order \<G> * xa * x2 - xa * x2) mod order \<G>)"
    using hvzk_z_r assms by simp
    thus ?thesis by argo
qed

lemma hvzk_sim_inverse_rewrite: 
  assumes h: "h =  \<^bold>g [^] (x1 :: nat) \<otimes> g' [^] (x2 :: nat)"
  shows "\<^bold>g [^] (((z1::nat) + order \<G> * c * x1 - c * x1) mod (order \<G>)) 
            \<otimes> g' [^] (((z2::nat) + order \<G> * c * x2 - c * x2) mod (order \<G>))
                = (\<^bold>g [^] z1 \<otimes> g' [^] z2) \<otimes> (inv h [^] c)"
(is "?lhs = ?rhs")
proof-
  have in_carrier1: "(g' [^] x2) [^] c \<in> carrier \<G>" by simp 
  have in_carrier2: "(\<^bold>g [^] x1) [^] c \<in> carrier \<G>" by simp
  have pow_distrib1: "order \<G> * c * x1 - c * x1 = (order \<G> - 1) * c * x1" 
    and pow_distrib2: "order \<G> * c * x2 - c * x2 = (order \<G> - 1) * c * x2" 
    using assms by (simp add: diff_mult_distrib)+
  have "?lhs = \<^bold>g [^] (z1 + order \<G> * c * x1 - c * x1) \<otimes> g' [^] (z2 + order \<G> * c  * x2 - c * x2)"
    by (simp add: pow_carrier_mod)
  also have "... = \<^bold>g [^] (z1 + (order \<G> * c * x1 - c * x1)) \<otimes> g' [^] (z2 + (order \<G> * c * x2 - c * x2))" 
    using h 
    by (smt Nat.add_diff_assoc diff_zero le_simps(1) nat_0_less_mult_iff neq0_conv pow_distrib1 pow_distrib2 prime_gt_1_nat prime_order zero_less_diff)
  also have "... =  \<^bold>g [^] z1 \<otimes> \<^bold>g [^] (order \<G> * c * x1 - c * x1) \<otimes> g' [^] z2 \<otimes> g' [^] (order \<G> * c * x2 - c * x2)"
    using nat_pow_mult 
    by (simp add: m_assoc) 
  also have "... = \<^bold>g [^] z1 \<otimes> g' [^] z2 \<otimes> \<^bold>g [^] (order \<G> * c * x1 - c * x1) \<otimes> g' [^] (order \<G> * c * x2 - c * x2)"
    by (smt add.commute g'_def generator_closed m_assoc nat_pow_closed nat_pow_mult nat_pow_pow)
  also have "... = \<^bold>g [^] z1 \<otimes> g' [^] z2 \<otimes> \<^bold>g [^] ((order \<G> - 1) * c * x1) \<otimes> g' [^] ((order \<G> - 1) * c * x2)" 
    using pow_distrib1 pow_distrib2 by argo
  also have "... = \<^bold>g [^] z1 \<otimes> g' [^] z2 \<otimes> (\<^bold>g [^] (order \<G> - 1)) [^] (c * x1) \<otimes> (g' [^] ((order \<G> - 1))) [^] (c * x2)" 
    by (simp add: more_arith_simps(11) nat_pow_pow)
  also have "... = \<^bold>g [^] z1 \<otimes> g' [^] z2 \<otimes> (inv (\<^bold>g [^] c)) [^] x1 \<otimes> (inv (g' [^] c)) [^] x2"
    using assms neg_power_inverse  inverse_pow_pow nat_pow_pow prime_gt_1_nat prime_order by auto
  also have "... = \<^bold>g [^] z1 \<otimes> g' [^] z2 \<otimes> (inv ((\<^bold>g [^] c) [^] x1)) \<otimes> (inv ((g' [^] c) [^] x2))" 
    by (simp add: inverse_pow_pow)
  also have "... = \<^bold>g [^] z1 \<otimes> g' [^] z2 \<otimes> ((inv ((\<^bold>g [^] x1) [^] c)) \<otimes> (inv ((g' [^] x2) [^] c)))" 
    by (simp add: mult.commute cyclic_group_assoc nat_pow_pow)
  also have "... = \<^bold>g [^] z1 \<otimes> g' [^] z2 \<otimes> inv ((\<^bold>g [^] x1) [^] c \<otimes> (g' [^] x2) [^] c)"
    using inverse_split in_carrier2 in_carrier1 by simp
  also have "... = \<^bold>g [^] z1 \<otimes> g' [^] z2 \<otimes> inv (h [^] c)" 
    using h  cyclic_group_commute monoid_comm_monoidI 
    by (simp add: pow_mult_distrib)
  ultimately show ?thesis 
    by (simp add: h inverse_pow_pow)
qed

lemma hv_zk: 
  assumes "h =  \<^bold>g [^] x1 \<otimes> g' [^] x2"
  shows "\<Sigma>_protocols_base.R h (x1,x2) c = \<Sigma>_protocols_base.S h c"
  including monad_normalisation
proof-
  have "\<Sigma>_protocols_base.R h (x1,x2) c = do { 
    r1 \<leftarrow> sample_uniform (order \<G>);
    r2 \<leftarrow> sample_uniform (order \<G>);
    let z1 = (r1 + c * x1) mod (order \<G>);
    let z2 = (r2 + c * x2) mod (order \<G>);
    return_spmf ( \<^bold>g [^] r1 \<otimes> g' [^] r2 ,c,(z1,z2))}"
      by(simp add: \<Sigma>_protocols_base.R_def R2_def; simp add: add.commute init_def split_def response_def)
    also have "... = do { 
    r2 \<leftarrow> sample_uniform (order \<G>);
    z1 \<leftarrow> map_spmf (\<lambda> r1. (r1 + c * x1) mod (order \<G>)) (sample_uniform (order \<G>));
    let z2 = (r2 + c * x2) mod (order \<G>);
    return_spmf (\<^bold>g [^] ((z1 + order \<G> * c * x1 - c * x1) mod (order \<G>)) \<otimes> g' [^] r2 ,c,(z1,z2))}"
      by(simp add: bind_map_spmf o_def Let_def hvzk_z1_r1_tuple_rewrite assms cong: bind_spmf_cong_simp)
  also have "... = do { 
    z1 \<leftarrow> map_spmf (\<lambda> r1. (r1 + c * x1) mod (order \<G>)) (sample_uniform (order \<G>));
    z2 \<leftarrow> map_spmf (\<lambda> r2. (r2 + c * x2) mod (order \<G>)) (sample_uniform (order \<G>));
    return_spmf (\<^bold>g [^] ((z1 + order \<G> * c * x1 - c * x1) mod (order \<G>)) \<otimes> g' [^] ((z2 + order \<G> * c * x2 - c * x2) mod (order \<G>)) ,c,(z1,z2))}"
    by(simp add: bind_map_spmf o_def Let_def hvzk_z2_r2_tuple_rewrite cong: bind_spmf_cong_simp)
  also have "... = do { 
    z1 \<leftarrow> map_spmf (\<lambda> r1. (c * x1 + r1) mod (order \<G>)) (sample_uniform (order \<G>));
    z2 \<leftarrow> map_spmf (\<lambda> r2. (c * x2 + r2) mod (order \<G>)) (sample_uniform (order \<G>));
    return_spmf (\<^bold>g [^] ((z1 + order \<G> * c * x1 - c * x1) mod (order \<G>)) \<otimes> g' [^] ((z2 + order \<G> * c * x2 - c * x2) mod (order \<G>)) ,c,(z1,z2))}"
    by(simp add: add.commute)
  also have "... = do { 
    z1 \<leftarrow> (sample_uniform (order \<G>));
    z2 \<leftarrow> (sample_uniform (order \<G>));
    return_spmf (\<^bold>g [^] ((z1 + order \<G> * c * x1 - c * x1) mod (order \<G>)) \<otimes> g' [^] ((z2 + order \<G> * c * x2 - c * x2) mod (order \<G>)) ,c,(z1,z2))}"
      by(simp add: samp_uni_plus_one_time_pad)
  also have "... = do { 
    z1 \<leftarrow> (sample_uniform (order \<G>));
    z2 \<leftarrow> (sample_uniform (order \<G>));
    return_spmf ((\<^bold>g [^] z1 \<otimes> g' [^] z2) \<otimes> (inv h [^] c) ,c,(z1,z2))}"
      by(simp add: hvzk_sim_inverse_rewrite assms cong: bind_spmf_cong_simp) 
  ultimately show ?thesis 
    by(simp add: \<Sigma>_protocols_base.S_def S2_def bind_map_spmf map_spmf_conv_bind_spmf)
qed

lemma HVZK: 
  shows "\<Sigma>_protocols_base.HVZK"
  unfolding \<Sigma>_protocols_base.HVZK_def 
  apply(auto simp add: R_def challenge_space_def hv_zk S2_def check_def valid_pub_def)
  by (metis (no_types, lifting) cyclic_group_commute g'_in_carrier generator_closed inv_closed inv_solve_left inverse_pow_pow m_closed nat_pow_closed)

lemma ss_rewrite:
  assumes "h \<in> carrier \<G>"
    and "a \<in> carrier \<G>"
    and "e < order \<G>" 
    and "\<^bold>g [^] z1 \<otimes> g' [^] z1' = a \<otimes> h [^] e"
    and "e' < e"
    and "\<^bold>g [^] z2 \<otimes> g' [^] z2' = a \<otimes> h [^] e' "
  shows "h = \<^bold>g [^] ((int z1 - int z2) * fst (bezw (e - e') (order \<G>)) mod int (order \<G>)) \<otimes> g' [^] ((int z1' - int z2') * fst (bezw (e - e') (order \<G>)) mod int (order \<G>))"
proof-
  have gcd: "gcd (e - e') (order \<G>) = 1"
    using prime_field assms prime_order by simp 
  have "\<^bold>g [^] z1 \<otimes> g' [^] z1' \<otimes> inv (h [^] e) = a" 
    by (simp add: inv_solve_right' assms)
  moreover have "\<^bold>g [^] z2 \<otimes> g' [^] z2' \<otimes> inv (h [^] e') = a" 
    by (simp add: assms inv_solve_right')
  ultimately have "\<^bold>g [^] z2 \<otimes> g' [^] z2' \<otimes> inv (h [^] e') = \<^bold>g [^] z1 \<otimes> g' [^] z1' \<otimes> inv (h [^] e)"
    using g'_def by (simp add: nat_pow_pow)
  moreover obtain t :: nat where t: "h = \<^bold>g [^] t" 
    using assms generatorE by blast
  ultimately have "\<^bold>g [^] z2 \<otimes> \<^bold>g [^] (x * z2') \<otimes> \<^bold>g [^] (t * e) = \<^bold>g [^] z1 \<otimes> \<^bold>g [^] (x * z1') \<otimes> (\<^bold>g [^] (t * e'))" 
    using assms(2) assms(4) cyclic_group_commute m_assoc g'_def nat_pow_pow by auto
  hence "\<^bold>g [^] (z2 + x * z2' + t * e) = \<^bold>g [^] (z1 + x * z1' + t * e')"  
    by (simp add: nat_pow_mult)
  hence "[z2 + x * z2' + t * e = z1 + x * z1' + t * e'] (mod order \<G>)"
    using group_eq_pow_eq_mod order_gt_0 by blast
  hence "[int z2 + int x * int z2' + int t * int e = int z1 + int x * int z1' + int t * int e'] (mod order \<G>)"
    using cong_int_iff by force
  hence "[int z1 + int x * int z1' - int z2 - int x * int z2' = int t * int e - int t * int e'] (mod order \<G>)"
    by (smt cong_diff_iff_cong_0 cong_sym)
  hence "[int z1 + int x * int z1' - int z2 - int x * int z2' = int t * (e - e')] (mod order \<G>)"
    using int_distrib(4) assms by (simp add: of_nat_diff)
  hence "[(int z1 + int x * int z1' - int z2 - int x * int z2') * fst (bezw (e - e') (order \<G>)) = int t * (e - e') * fst (bezw (e - e') (order \<G>))] (mod order \<G>)"
    using cong_scalar_right by blast
  hence "[(int z1 + int x * int z1' - int z2 - int x * int z2') * fst (bezw (e - e') (order \<G>)) = int t * ((e - e') * fst (bezw (e - e') (order \<G>)))] (mod order \<G>)"
    by (simp add: mult.assoc)
  hence "[(int z1 + int x * int z1' - int z2 - int x * int z2') * fst (bezw (e - e') (order \<G>)) = int t * 1] (mod order \<G>)"
    by (metis (no_types, hide_lams) cong_scalar_left cong_trans inverse gcd)
  hence "[(int z1 - int z2 + int x * int z1' - int x * int z2') * fst (bezw (e - e') (order \<G>)) = int t] (mod order \<G>)"
    by smt
  hence "[(int z1 - int z2 + int x * (int z1' - int z2')) * fst (bezw (e - e') (order \<G>)) = int t] (mod order \<G>)"
    by (simp add: Rings.ring_distribs(4) add_diff_eq)
  hence "[nat ((int z1 - int z2 + int x * (int z1' - int z2')) * fst (bezw (e - e') (order \<G>)) mod (order \<G>)) = int t] (mod order \<G>)"
    by auto
  hence "\<^bold>g [^] (nat ((int z1 - int z2 + int x * (int z1' - int z2')) * fst (bezw (e - e') (order \<G>)) mod (order \<G>))) = \<^bold>g [^] t"
    using cong_int_iff finite_carrier pow_generator_eq_iff_cong by blast
  hence "\<^bold>g [^] ((int z1 - int z2 + int x * (int z1' - int z2')) * fst (bezw (e - e') (order \<G>))) = \<^bold>g [^] t"
    using pow_generator_mod_int by auto
  hence "\<^bold>g [^] ((int z1 - int z2) * fst (bezw (e - e') (order \<G>)) + int x * (int z1' - int z2') * fst (bezw (e - e') (order \<G>))) = \<^bold>g [^] t"
    by (metis Rings.ring_distribs(2) t)
  hence "\<^bold>g [^] ((int z1 - int z2) * fst (bezw (e - e') (order \<G>))) \<otimes> \<^bold>g [^] (int x * (int z1' - int z2') * fst (bezw (e - e') (order \<G>))) = \<^bold>g [^] t"
    using int_pow_mult by auto
  thus ?thesis 
    by (metis (mono_tags, hide_lams) g'_def generator_closed int_pow_int int_pow_pow mod_mult_right_eq more_arith_simps(11) pow_generator_mod_int t)
qed

lemma 
  assumes h_mem: "h \<in> carrier \<G>" 
    and a_mem: "a \<in> carrier \<G>" 
    and a: "\<^bold>g [^] fst z \<otimes> g' [^] snd z = a \<otimes> h [^] e"
    and a': "\<^bold>g [^] fst z' \<otimes> g' [^] snd z' = a \<otimes> h [^] e'"
    and e_e'_mod: "e' mod order \<G> < e mod order \<G>"
  shows "h = \<^bold>g [^] ((int (fst z) - int (fst z')) * fst (bezw ((e mod order \<G> - e' mod order \<G>) mod order \<G>) (order \<G>)) mod int (order \<G>)) 
              \<otimes> g' [^] ((int (snd z) - int (snd z')) * fst (bezw ((e mod order \<G> - e' mod order \<G>) mod order \<G>) (order \<G>)) mod int (order \<G>))"
proof-
  have gcd: "gcd ((e mod order \<G> - e' mod order \<G>) mod order \<G>) (order \<G>) = 1"
    using prime_field 
    by (simp add: assms less_imp_diff_less linorder_not_le prime_order)
  have "\<^bold>g [^] fst z \<otimes> g' [^] snd z \<otimes> inv (h [^] e) = a" 
    using a h_mem a_mem by (simp add: inv_solve_right')
  moreover have "\<^bold>g [^] fst z' \<otimes> g' [^] snd z' \<otimes> inv (h [^] e') = a" 
    using a h_mem a_mem by (simp add: assms(4) inv_solve_right')
  ultimately have "\<^bold>g [^] fst z \<otimes> \<^bold>g [^] (x * snd z) \<otimes> inv (h [^] e) = \<^bold>g [^] fst z' \<otimes> \<^bold>g [^] (x * snd z') \<otimes> inv (h [^] e')"
    using g'_def by (simp add: nat_pow_pow)
  moreover obtain t :: nat where t: "h = \<^bold>g [^] t" 
    using h_mem generatorE by blast
  ultimately have "\<^bold>g [^] fst z \<otimes> \<^bold>g [^] (x * snd z) \<otimes> \<^bold>g [^] (t * e') = \<^bold>g [^] fst z' \<otimes> \<^bold>g [^] (x * snd z') \<otimes> \<^bold>g [^] (t * e)"
    using a_mem assms(3) assms(4) cyclic_group_assoc cyclic_group_commute g'_def nat_pow_pow by auto
  hence "\<^bold>g [^] (fst z + x * snd z + t * e') = \<^bold>g [^] (fst z' + x * snd z' + t * e)"
    by (simp add: nat_pow_mult)
  hence "[fst z + x * snd z + t * e' = fst z' + x * snd z' + t * e] (mod order \<G>)"
    using group_eq_pow_eq_mod order_gt_0 by blast
  hence "[int (fst z) + int x * int (snd z) + int t * int e' = int (fst z') + int x * int (snd z') + int t * int e] (mod order \<G>)"
    using cong_int_iff by force
  hence "[int (fst z) - int (fst z') + int x * int (snd z) - int x * int (snd z') =  int t * int e - int t  * int e'] (mod order \<G>)"
    by (smt cong_diff_iff_cong_0)
  hence "[int (fst z) - int (fst z') + int x * (int (snd z) - int (snd z')) =  int t * (int e -  int e')] (mod order \<G>)"
  proof -
    have "[int (fst z) + (int (x * snd z) - (int (fst z') + int (x * snd z'))) = int t * (int e - int e')] (mod int (order \<G>))"
      by (simp add: Rings.ring_distribs(4) \<open>[int (fst z) - int (fst z') + int x * int (snd z) - int x * int (snd z') = int t * int e - int t * int e'] (mod int (order \<G>))\<close> add_diff_add add_diff_eq)
    then have "\<exists>i. [int (fst z) + (int x * int (snd z) - (int (fst z') + i * int (snd z'))) = int t * (int e - int e') + int (snd z') * (int x - i)] (mod int (order \<G>))"
      by (metis (no_types) add.commute arith_simps(49) cancel_comm_monoid_add_class.diff_cancel int_ops(7) mult_eq_0_iff)
    then have "\<exists>i. [int (fst z) - int (fst z') + (int x * (int (snd z) - int (snd z')) + i) = int t * (int e - int e') + i] (mod int (order \<G>))"
      by (metis (no_types) add_diff_add add_diff_eq mult_diff_mult mult_of_nat_commute)
    then show ?thesis
      by (metis (no_types) add.assoc cong_add_rcancel)
  qed
  hence "[int (fst z) - int (fst z') + int x * (int (snd z) - int (snd z')) =  int t * (int e mod order \<G> - int e' mod order \<G>) mod order \<G>] (mod order \<G>)"
    by (metis (mono_tags, lifting) cong_def mod_diff_eq mod_mod_trivial mod_mult_right_eq)
  hence "[int (fst z) - int (fst z') + int x * (int (snd z) - int (snd z')) =  int t * (e mod order \<G> - e' mod order \<G>) mod order \<G>] (mod order \<G>)"
    using e_e'_mod 
    by (simp add: int_ops(9) of_nat_diff)
  hence "[(int (fst z) - int (fst z') + int x * (int (snd z) - int (snd z'))) 
            * fst (bezw ((e mod order \<G> - e' mod order \<G>) mod order \<G>) (order \<G>)) mod order \<G> 
               =  int t * (e mod order \<G> - e' mod order \<G>) mod order \<G> 
                  * fst (bezw ((e mod order \<G> - e' mod order \<G>) mod order \<G>) (order \<G>)) mod order \<G>] (mod order \<G>)"
    using cong_cong_mod_int cong_scalar_right by blast
  hence "[(int (fst z) - int (fst z') + int x * (int (snd z) - int (snd z'))) 
            * fst (bezw ((e mod order \<G> - e' mod order \<G>) mod order \<G>) (order \<G>)) mod order \<G> 
               =  int t * ((e mod order \<G> - e' mod order \<G>) mod order \<G> 
                  * fst (bezw ((e mod order \<G> - e' mod order \<G>) mod order \<G>) (order \<G>)) mod order \<G>)] (mod order \<G>)"
    by (metis (no_types, lifting) Groups.mult_ac(1) cong_mod_right less_imp_diff_less mod_less mod_mult_left_eq mod_mult_right_eq order_gt_0 unique_euclidean_semiring_numeral_class.pos_mod_bound)
  hence "[(int (fst z) - int (fst z') + int x * (int (snd z) - int (snd z'))) 
            * fst (bezw ((e mod order \<G> - e' mod order \<G>) mod order \<G>) (order \<G>)) mod order \<G> 
               =  int t * 1] (mod order \<G>)"
    using inverse gcd 
    by (smt Num.of_nat_simps(5) Number_Theory_Aux.inverse cong_def mod_mult_right_eq more_arith_simps(6) of_nat_1)
  hence "[((int (fst z) - int (fst z')) + (int x * (int (snd z) - int (snd z')))) 
            * fst (bezw ((e mod order \<G> - e' mod order \<G>) mod order \<G>) (order \<G>)) mod order \<G> 
               = int t] (mod order \<G>)"
    by auto
  hence "[(int (fst z) - int (fst z')) * (fst (bezw ((e mod order \<G> - e' mod order \<G>) mod order \<G>) (order \<G>)) mod order \<G>) + (int x * (int (snd z) - int (snd z'))) 
            * (fst (bezw ((e mod order \<G> - e' mod order \<G>) mod order \<G>) (order \<G>)) mod order \<G>) 
               = int t] (mod order \<G>)"
    by (metis (no_types, hide_lams) cong_mod_left distrib_right mod_mult_right_eq)
  hence "[(int (fst z) - int (fst z')) * fst (bezw ((e mod order \<G> - e' mod order \<G>) mod order \<G>) (order \<G>)) mod order \<G> + (int x * (int (snd z) - int (snd z'))) 
            * (fst (bezw ((e mod order \<G> - e' mod order \<G>) mod order \<G>) (order \<G>)) mod order \<G>) 
               = t] (mod order \<G>)"
  proof -
    have "[(int (fst z) - int (fst z')) * fst (bezw ((e mod order \<G> - e' mod order \<G>) mod order \<G>) (order \<G>)) = (int (fst z) - int (fst z')) * (fst (bezw ((e mod order \<G> - e' mod order \<G>) mod order \<G>) (order \<G>)) mod int (order \<G>))] (mod int (order \<G>))"
      by (metis (no_types) cong_def mod_mult_right_eq)
    then show ?thesis
      by (meson \<open>[(int (fst z) - int (fst z')) * (fst (bezw ((e mod order \<G> - e' mod order \<G>) mod order \<G>) (order \<G>)) mod int (order \<G>)) + int x * (int (snd z) - int (snd z')) * (fst (bezw ((e mod order \<G> - e' mod order \<G>) mod order \<G>) (order \<G>)) mod int (order \<G>)) = int t] (mod int (order \<G>))\<close> cong_add_rcancel cong_mod_left cong_trans)
  qed
  hence "[(int (fst z) - int (fst z')) * fst (bezw ((e mod order \<G> - e' mod order \<G>) mod order \<G>) (order \<G>)) mod order \<G> + (int x * (int (snd z) - int (snd z'))) 
            * fst (bezw ((e mod order \<G> - e' mod order \<G>) mod order \<G>) (order \<G>)) mod order \<G>
               = t] (mod order \<G>)"
  proof -
    have "int x * ((int (snd z) - int (snd z')) * (fst (bezw ((e mod order \<G> - e' mod order \<G>) mod order \<G>) (order \<G>)) mod int (order \<G>))) mod int (order \<G>) = int x * ((int (snd z) - int (snd z')) * fst (bezw ((e mod order \<G> - e' mod order \<G>) mod order \<G>) (order \<G>))) mod int (order \<G>) mod int (order \<G>)"
      by (metis (no_types) mod_mod_trivial mod_mult_right_eq)
    then have "[int x * ((int (snd z) - int (snd z')) * fst (bezw ((e mod order \<G> - e' mod order \<G>) mod order \<G>) (order \<G>))) mod int (order \<G>) = int x * ((int (snd z) - int (snd z')) * (fst (bezw ((e mod order \<G> - e' mod order \<G>) mod order \<G>) (order \<G>)) mod int (order \<G>)))] (mod int (order \<G>))"
      by (metis (no_types) cong_def)
    then have "[(int (fst z) - int (fst z')) * fst (bezw ((e mod order \<G> - e' mod order \<G>) mod order \<G>) (order \<G>)) mod int (order \<G>) + int x * ((int (snd z) - int (snd z')) * fst (bezw ((e mod order \<G> - e' mod order \<G>) mod order \<G>) (order \<G>))) mod int (order \<G>) = (int (fst z) - int (fst z')) * fst (bezw ((e mod order \<G> - e' mod order \<G>) mod order \<G>) (order \<G>)) mod int (order \<G>) + int x * (int (snd z) - int (snd z')) * (fst (bezw ((e mod order \<G> - e' mod order \<G>) mod order \<G>) (order \<G>)) mod int (order \<G>))] (mod int (order \<G>))"
      by (metis (no_types) Groups.mult_ac(1) cong_add cong_refl)
    then have "[(int (fst z) - int (fst z')) * fst (bezw ((e mod order \<G> - e' mod order \<G>) mod order \<G>) (order \<G>)) mod int (order \<G>) + int x * ((int (snd z) - int (snd z')) * fst (bezw ((e mod order \<G> - e' mod order \<G>) mod order \<G>) (order \<G>))) mod int (order \<G>) = int t] (mod int (order \<G>))"
      using \<open>[(int (fst z) - int (fst z')) * fst (bezw ((e mod order \<G> - e' mod order \<G>) mod order \<G>) (order \<G>)) mod int (order \<G>) + int x * (int (snd z) - int (snd z')) * (fst (bezw ((e mod order \<G> - e' mod order \<G>) mod order \<G>) (order \<G>)) mod int (order \<G>)) = int t] (mod int (order \<G>))\<close> cong_trans by blast
    then show ?thesis
      by (metis (no_types) Groups.mult_ac(1))
  qed
  hence "\<^bold>g [^] ((int (fst z) - int (fst z')) * fst (bezw ((e mod order \<G> - e' mod order \<G>) mod order \<G>) (order \<G>)) mod order \<G> + (int x * (int (snd z) - int (snd z'))) 
            * fst (bezw ((e mod order \<G> - e' mod order \<G>) mod order \<G>) (order \<G>)) mod order \<G>)
               = \<^bold>g [^] t"
    by (metis cong_def int_pow_int pow_generator_mod_int)
  hence "\<^bold>g [^] ((int (fst z) - int (fst z')) * fst (bezw ((e mod order \<G> - e' mod order \<G>) mod order \<G>) (order \<G>)) mod order \<G>) \<otimes> \<^bold>g [^] ((int x * (int (snd z) - int (snd z'))) 
            * fst (bezw ((e mod order \<G> - e' mod order \<G>) mod order \<G>) (order \<G>)) mod order \<G>)
               = \<^bold>g [^] t"
    using int_pow_mult by auto
  hence "\<^bold>g [^] ((int (fst z) - int (fst z')) * fst (bezw ((e mod order \<G> - e' mod order \<G>) mod order \<G>) (order \<G>)) mod order \<G>) \<otimes> \<^bold>g [^] ((int x * ((int (snd z) - int (snd z'))) 
            * fst (bezw ((e mod order \<G> - e' mod order \<G>) mod order \<G>) (order \<G>)) mod order \<G>))
               = \<^bold>g [^] t"
    by blast
  hence "\<^bold>g [^] ((int (fst z) - int (fst z')) * fst (bezw ((e mod order \<G> - e' mod order \<G>) mod order \<G>) (order \<G>)) mod order \<G>) \<otimes> g' [^] ((((int (snd z) - int (snd z'))) 
            * fst (bezw ((e mod order \<G> - e' mod order \<G>) mod order \<G>) (order \<G>)) mod order \<G>))
               = \<^bold>g [^] t"
    by (smt g'_def cyclic_group.generator_closed int_pow_int int_pow_pow mod_mult_right_eq more_arith_simps(11) okamoto_axioms okamoto_def pow_generator_mod_int)
  thus ?thesis using t by simp
qed

lemma special_soundness:
  shows "\<Sigma>_protocols_base.special_soundness"       
  unfolding \<Sigma>_protocols_base.special_soundness_def 
  by(auto simp add: valid_pub_def check_def R_def ss_adversary_def Let_def ss_rewrite challenge_space_def split_def)

theorem \<Sigma>_protocol: 
  shows "\<Sigma>_protocols_base.\<Sigma>_protocol"
  by(simp add: \<Sigma>_protocols_base.\<Sigma>_protocol_def completeness HVZK special_soundness)

sublocale okamoto_\<Sigma>_commit: \<Sigma>_protocols_to_commitments init response check R S2 ss_adversary challenge_space valid_pub G 
  apply unfold_locales
  apply(auto simp add: \<Sigma>_protocol)
  by(auto simp add: G_def R_def lossless_init lossless_response)

sublocale dis_log: dis_log \<G> 
  unfolding dis_log_def by simp

sublocale dis_log_alt: dis_log_alt \<G> x 
  unfolding dis_log_alt_def 
  by(simp add:)

lemma reduction_to_dis_log:
  shows "okamoto_\<Sigma>_commit.rel_advantage \<A> = dis_log.advantage (dis_log_alt.adversary2 \<A>)"
proof-
  have exp_rewrite: "\<^bold>g [^] w1 \<otimes> g' [^] w2 =  \<^bold>g [^] (w1 + x * w2)" for w1 w2 :: nat
    by (simp add: nat_pow_mult nat_pow_pow g'_def)
  have "okamoto_\<Sigma>_commit.rel_game \<A> = TRY do {
    w1 \<leftarrow> sample_uniform (order \<G>);
    w2 \<leftarrow> sample_uniform (order \<G>);
    let h = (\<^bold>g [^] w1 \<otimes> g' [^] w2);
    (w1',w2') \<leftarrow> \<A> h;
    return_spmf (h = \<^bold>g [^] w1' \<otimes> g' [^] w2')} ELSE return_spmf False"
    unfolding okamoto_\<Sigma>_commit.rel_game_def
    by(simp add: Let_def split_def R_def G_def)
  also have "... = TRY do {
    w1 \<leftarrow> sample_uniform (order \<G>);
    w2 \<leftarrow> sample_uniform (order \<G>);
    let w = (w1 + x * w2) mod (order \<G>);
    let h = \<^bold>g [^] w;
    (w1',w2') \<leftarrow> \<A> h;
    return_spmf (h = \<^bold>g [^] w1' \<otimes> g' [^] w2')} ELSE return_spmf False"
    using g'_def exp_rewrite pow_generator_mod by simp
  also have "... = TRY do {
    w2 \<leftarrow> sample_uniform (order \<G>);
    w \<leftarrow> map_spmf (\<lambda> w1. (x * w2 + w1) mod (order \<G>)) (sample_uniform (order \<G>));
    let h = \<^bold>g [^] w;
    (w1',w2') \<leftarrow> \<A> h;
    return_spmf (h = \<^bold>g [^] w1' \<otimes> g' [^] w2')} ELSE return_spmf False"
    including monad_normalisation
    by(simp add: bind_map_spmf o_def Let_def add.commute)
  also have "... = TRY do {
    w2 :: nat \<leftarrow> sample_uniform (order \<G>);
    w \<leftarrow> sample_uniform (order \<G>);
    let h = \<^bold>g [^] w;
    (w1',w2') \<leftarrow> \<A> h;
    return_spmf (h = \<^bold>g [^] w1' \<otimes> g' [^] w2')} ELSE return_spmf False"
    using samp_uni_plus_one_time_pad add.commute by simp
  also have "... = TRY do {
    w \<leftarrow> sample_uniform (order \<G>);
    let h = \<^bold>g [^] w;
    (w1',w2') \<leftarrow> \<A> h;
    return_spmf (h = \<^bold>g [^] w1' \<otimes> g' [^] w2')} ELSE return_spmf False"
    by(simp add: bind_spmf_const)
  also have "... = dis_log_alt.dis_log2 \<A>"
    apply(simp add: dis_log_alt.dis_log2_def Let_def dis_log_alt.g'_def g'_def)
    apply(intro try_spmf_cong)
     apply(intro bind_spmf_cong[OF refl]; clarsimp?)
     apply auto
    using exp_rewrite pow_generator_mod g'_def 
     apply (metis group_eq_pow_eq_mod okamoto_axioms okamoto_base.order_gt_0 okamoto_def)
    using exp_rewrite g'_def order_gt_0_iff_finite pow_generator_eq_iff_cong by auto
  ultimately have "okamoto_\<Sigma>_commit.rel_game \<A> = dis_log_alt.dis_log2 \<A>"
    by simp
  hence "okamoto_\<Sigma>_commit.rel_advantage \<A> = dis_log_alt.advantage2 \<A>"
    by(simp add: okamoto_\<Sigma>_commit.rel_advantage_def dis_log_alt.advantage2_def)
  thus ?thesis
    by (simp add: dis_log_alt_reductions.dis_log_adv2 cyclic_group_axioms dis_log_alt.dis_log_alt_axioms dis_log_alt_reductions.intro)
qed

lemma commitment_correct: "okamoto_\<Sigma>_commit.abstract_com.correct"
  by(simp add: okamoto_\<Sigma>_commit.commit_correct)

lemma "okamoto_\<Sigma>_commit.abstract_com.perfect_hiding_ind_cpa \<A>"
  using okamoto_\<Sigma>_commit.perfect_hiding by blast

lemma binding: 
  shows "okamoto_\<Sigma>_commit.abstract_com.bind_advantage \<A> 
          \<le> dis_log.advantage (dis_log_alt.adversary2 (okamoto_\<Sigma>_commit.adversary \<A>))"
  using okamoto_\<Sigma>_commit.bind_advantage reduction_to_dis_log by auto

end

locale okamoto_asymp = 
  fixes \<G> :: "nat \<Rightarrow> 'grp cyclic_group"
    and x :: nat
  assumes okamoto: "\<And>\<eta>. okamoto (\<G> \<eta>)"
begin

sublocale okamoto "\<G> \<eta>" for \<eta> 
  by(simp add: okamoto)

text\<open>The \<open>\<Sigma>\<close>-protocol statement comes easily in the asympotic setting.\<close>

theorem sigma_protocol:
  shows "\<Sigma>_protocols_base.\<Sigma>_protocol n"
  by(simp add: \<Sigma>_protocol)

text\<open>We now show the statements of security for the commitment scheme in the asymptotic setting, the main difference is that
we are able to show the binding advantage is negligible in the security parameter.\<close>

lemma asymp_correct: "okamoto_\<Sigma>_commit.abstract_com.correct n" 
  using  okamoto_\<Sigma>_commit.commit_correct by simp

lemma asymp_perfect_hiding: "okamoto_\<Sigma>_commit.abstract_com.perfect_hiding_ind_cpa n (\<A> n)"
  using okamoto_\<Sigma>_commit.perfect_hiding by blast

lemma asymp_computational_binding: 
  assumes "negligible (\<lambda> n. dis_log.advantage n (dis_log_alt.adversary2 (okamoto_\<Sigma>_commit.adversary n (\<A> n))))"
  shows "negligible (\<lambda> n. okamoto_\<Sigma>_commit.abstract_com.bind_advantage n (\<A> n))"
  using okamoto_\<Sigma>_commit.bind_advantage assms okamoto_\<Sigma>_commit.abstract_com.bind_advantage_def negligible_le binding by auto

end

end