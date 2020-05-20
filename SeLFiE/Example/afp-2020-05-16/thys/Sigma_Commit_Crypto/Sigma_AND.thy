subsection\<open>\<open>\<Sigma>\<close>-AND statements\<close>

theory Sigma_AND imports
  Sigma_Protocols
  Xor
begin 

locale \<Sigma>_AND_base = \<Sigma>0: \<Sigma>_protocols_base init0 response0 check0 Rel0 S0_raw \<A>ss0 "carrier L" valid_pub0
  + \<Sigma>1: \<Sigma>_protocols_base init1 response1 check1 Rel1 S1_raw \<A>ss1 "carrier L" valid_pub1
  for init1 :: "'pub1 \<Rightarrow> 'witness1 \<Rightarrow> ('rand1 \<times> 'msg1) spmf"
    and response1 :: "'rand1 \<Rightarrow> 'witness1 \<Rightarrow> 'bool  \<Rightarrow> 'response1 spmf"
    and check1 :: "'pub1 \<Rightarrow> 'msg1 \<Rightarrow> 'bool \<Rightarrow> 'response1 \<Rightarrow> bool"
    and Rel1 :: "('pub1 \<times> 'witness1) set"
    and S1_raw :: "'pub1 \<Rightarrow> 'bool \<Rightarrow> ('msg1 \<times> 'response1) spmf"
    and \<A>ss1 :: "'pub1 \<Rightarrow> 'msg1 \<times> 'bool \<times> 'response1 \<Rightarrow> 'msg1 \<times> 'bool \<times> 'response1 \<Rightarrow> 'witness1 spmf"
    and challenge_space1 :: "'bool set"
    and valid_pub1 :: "'pub1 set"
    and init0 :: "'pub0 \<Rightarrow> 'witness0 \<Rightarrow> ('rand0 \<times> 'msg0) spmf"
    and response0 :: "'rand0 \<Rightarrow> 'witness0 \<Rightarrow> 'bool \<Rightarrow> 'response0 spmf"
    and check0 :: "'pub0 \<Rightarrow> 'msg0 \<Rightarrow> 'bool \<Rightarrow> 'response0 \<Rightarrow> bool"
    and Rel0 :: "('pub0 \<times> 'witness0) set"
    and S0_raw :: "'pub0 \<Rightarrow> 'bool \<Rightarrow> ('msg0 \<times> 'response0) spmf"
    and \<A>ss0 :: "'pub0 \<Rightarrow> 'msg0 \<times> 'bool \<times> 'response0 \<Rightarrow> 'msg0 \<times> 'bool \<times> 'response0 \<Rightarrow> 'witness0 spmf"
    and challenge_space0 :: "'bool set"
    and valid_pub0 :: "'pub0 set"
    and G :: "(('pub0 \<times> 'pub1)  \<times> ('witness0 \<times> 'witness1)) spmf"
    and L :: "'bool boolean_algebra" (structure)
    + 
  assumes \<Sigma>_prot1: "\<Sigma>1.\<Sigma>_protocol"  
    and \<Sigma>_prot0: "\<Sigma>0.\<Sigma>_protocol"  
    and lossless_init: "lossless_spmf (init0 h0 w0)" "lossless_spmf (init1 h1 w1)"
    and lossless_response: "lossless_spmf (response0 r0 w0 e0)" "lossless_spmf (response1 r1 w1 e1)"
    and lossless_S: "lossless_spmf (S0 h0 e0)" "lossless_spmf (S1 h1 e1)"
    and lossless_\<A>ss: "lossless_spmf (\<A>ss0 x0 (a0,e,z0) (a0,e',z0'))" "lossless_spmf (\<A>ss1 x1 (a1,e,z1) (a1,e',z1'))" 
    and lossless_G: "lossless_spmf G"
    and set_spmf_G [simp]: "(h,w) \<in> set_spmf G \<Longrightarrow> Rel h w"
begin

definition "challenge_space = carrier L"

definition Rel_AND :: "(('pub0 \<times> 'pub1) \<times> 'witness0 \<times> 'witness1) set" 
  where "Rel_AND = {((x0,x1), (w0,w1)). ((x0,w0) \<in> Rel0 \<and> (x1,w1) \<in> Rel1)}"

definition init_AND :: "('pub0 \<times> 'pub1) \<Rightarrow> ('witness0 \<times> 'witness1) \<Rightarrow> (('rand0 \<times> 'rand1) \<times> 'msg0 \<times> 'msg1) spmf" 
  where "init_AND X W = do {
    let (x0, x1) = X;
    let (w0,w1) = W;
    (r0, a0) \<leftarrow> init0 x0 w0;
    (r1, a1) \<leftarrow> init1 x1 w1;
    return_spmf ((r0,r1), (a0,a1))}"   

lemma lossless_init_AND: "lossless_spmf (init_AND X W)"
  by(simp add: lossless_init init_AND_def split_def)
    
definition response_AND :: "('rand0 \<times> 'rand1) \<Rightarrow> ('witness0 \<times> 'witness1) \<Rightarrow> 'bool \<Rightarrow> ('response0 \<times> 'response1) spmf"
  where "response_AND R W s = do {
    let (r0,r1) = R;
    let (w0,w1) = W;  
    z0 \<leftarrow> response0 r0 w0 s;
    z1  :: 'response1 \<leftarrow> response1 r1 w1 s;
    return_spmf (z0,z1)}" 

lemma lossless_response_AND: "lossless_spmf (response_AND R W s)"
  by(simp add: response_AND_def lossless_response split_def)

fun check_AND :: "('pub0 \<times> 'pub1) \<Rightarrow> ('msg0 \<times> 'msg1) \<Rightarrow> 'bool \<Rightarrow> ('response0 \<times> 'response1) \<Rightarrow> bool"
  where "check_AND (x0,x1) (a0,a1) s (z0,z1) = (check0 x0 a0 s z0 \<and> check1 x1 a1 s z1)"

definition S_AND :: "'pub0 \<times> 'pub1 \<Rightarrow> 'bool \<Rightarrow> (('msg0 \<times> 'msg1) \<times> 'response0 \<times> 'response1) spmf"
  where "S_AND X e = do {
    let (x0,x1) = X;
    (a0, z0) \<leftarrow> S0_raw x0 e;
    (a1, z1) \<leftarrow> S1_raw x1 e;
    return_spmf ((a0,a1),(z0,z1))}"

fun \<A>ss_AND :: "'pub0 \<times> 'pub1 \<Rightarrow> ('msg0 \<times> 'msg1) \<times> 'bool \<times> 'response0 \<times> 'response1 \<Rightarrow> ('msg0 \<times> 'msg1) \<times> 'bool \<times> 'response0 \<times> 'response1 \<Rightarrow> ('witness0 \<times> 'witness1) spmf"
  where "\<A>ss_AND (x0,x1) ((a0,a1), e, (z0,z1)) ((a0',a1'), e', (z0',z1')) = do {
    w0 :: 'witness0 \<leftarrow> \<A>ss0 x0 (a0,e,z0) (a0',e',z0');
    w1 \<leftarrow> \<A>ss1 x1 (a1,e,z1) (a1',e',z1');
    return_spmf (w0,w1)}"

definition "valid_pub_AND = {(x0,x1). x0 \<in> valid_pub0 \<and> x1 \<in> valid_pub1}"

sublocale \<Sigma>_AND: \<Sigma>_protocols_base init_AND response_AND check_AND Rel_AND S_AND \<A>ss_AND challenge_space valid_pub_AND 
  apply unfold_locales apply(simp add: Rel_AND_def valid_pub_AND_def)
  using \<Sigma>1.domain_subset_valid_pub \<Sigma>0.domain_subset_valid_pub by blast

end 

locale \<Sigma>_AND = \<Sigma>_AND_base +
  assumes set_spmf_G_L: "((x0, x1), w0, w1) \<in> set_spmf G \<Longrightarrow> ((x0, x1), (w0,w1)) \<in> Rel_AND"
begin

lemma hvzk: 
  assumes Rel_AND: "((x0,x1), (w0,w1)) \<in> Rel_AND"
  and "e \<in> challenge_space" 
  shows "\<Sigma>_AND.R (x0,x1) (w0,w1) e = \<Sigma>_AND.S (x0,x1) e"
  including monad_normalisation
proof-
  have x_in_dom: "x0 \<in> Domain Rel0" and "x1 \<in> Domain Rel1" 
    using Rel_AND Rel_AND_def by auto
  have "\<Sigma>_AND.R (x0,x1) (w0,w1) e = do {
    ((r0,r1),(a0,a1)) \<leftarrow> init_AND (x0,x1) (w0,w1);
    (z0,z1) \<leftarrow> response_AND (r0,r1) (w0,w1) e;
    return_spmf ((a0,a1),e,(z0,z1))}"
    by(simp add: \<Sigma>_AND.R_def split_def)
  also have "... = do {
    (r0, a0) \<leftarrow> init0 x0 w0;
    z0 \<leftarrow> response0 r0 w0 e;
    (r1, a1) \<leftarrow> init1 x1 w1;
    z1 :: 'f \<leftarrow> response1 r1 w1 e;
    return_spmf ((a0,a1),e,(z0,z1))}"
    apply(simp add: init_AND_def response_AND_def split_def)
    apply(rewrite bind_commute_spmf[of "response0 _ w0 e"])
    by simp
  also have "... = do {
    (a0, c0, z0) \<leftarrow> \<Sigma>0.R x0 w0 e;
    (a1, c1, z1) \<leftarrow> \<Sigma>1.R x1 w1 e;
    return_spmf ((a0,a1),e,(z0,z1))}"
    by(simp add: \<Sigma>0.R_def \<Sigma>1.R_def split_def)
  also have "... = do {
    (a0, c0, z0) \<leftarrow> \<Sigma>0.S x0 e;
    (a1, c1, z1) \<leftarrow> \<Sigma>1.S x1 e;
    return_spmf ((a0,a1),e,(z0,z1))}"
    using Rel_AND_def S_AND_def \<Sigma>_prot1 \<Sigma>_prot0 assms  \<Sigma>0.HVZK_unfold1 \<Sigma>1.HVZK_unfold1 
          valid_pub_AND_def split_def challenge_space_def x_in_dom
    by auto
  ultimately show ?thesis 
    by(simp add: \<Sigma>0.S_def \<Sigma>1.S_def bind_map_spmf o_def split_def Let_def \<Sigma>_AND.S_def map_spmf_conv_bind_spmf S_AND_def)
qed

lemma HVZK: "\<Sigma>_AND.HVZK"
  using \<Sigma>_AND.HVZK_def hvzk challenge_space_def 
  apply(simp add: S_AND_def split_def)
  using \<Sigma>_prot1 \<Sigma>_prot0 \<Sigma>0.HVZK_unfold2 \<Sigma>1.HVZK_unfold2 valid_pub_AND_def by auto

lemma correct: 
  assumes Rel_AND: "((x0,x1), (w0,w1)) \<in> Rel_AND"
  and "e \<in> challenge_space" 
  shows "\<Sigma>_AND.completeness_game (x0,x1) (w0,w1) e = return_spmf True"
  including monad_normalisation
proof-
  have "\<Sigma>_AND.completeness_game (x0,x1) (w0,w1) e = do {
    ((r0,r1),(a0,a1)) \<leftarrow> init_AND (x0,x1) (w0,w1);
    (z0,z1) \<leftarrow> response_AND (r0,r1) (w0,w1) e;
    return_spmf (check_AND (x0,x1) (a0,a1) e (z0,z1))}" 
    by(simp add: \<Sigma>_AND.completeness_game_def split_def del: check_AND.simps)
  also have "... = do {
    (r0, a0) \<leftarrow> init0 x0 w0;
    z0 \<leftarrow> response0 r0 w0 e;
    (r1, a1) \<leftarrow> init1 x1 w1;
    z1 \<leftarrow> response1 r1 w1 e;
    return_spmf ((check0 x0 a0 e z0 \<and> check1 x1 a1 e z1))}" 
    apply(simp add: init_AND_def response_AND_def split_def)
    apply(rewrite bind_commute_spmf[of "response0 _ w0 e"])
    by simp
  ultimately show ?thesis
    using \<Sigma>1.complete_game_return_true \<Sigma>_prot1 \<Sigma>1.\<Sigma>_protocol_def \<Sigma>1.completeness_game_def assms
          \<Sigma>0.complete_game_return_true \<Sigma>_prot0 \<Sigma>0.\<Sigma>_protocol_def \<Sigma>0.completeness_game_def challenge_space_def
    apply(auto simp add: Let_def split_def bind_eq_return_spmf lossless_init lossless_response Rel_AND_def)
    by(metis (mono_tags, lifting) assms(2) fst_conv snd_conv)+
qed

lemma completeness: "\<Sigma>_AND.completeness"
  using \<Sigma>_AND.completeness_def correct challenge_space_def by force

lemma ss:
  assumes e_neq_e': "s \<noteq> s'"
    and valid_pub: "(x0,x1) \<in> valid_pub_AND"
    and challenge_space: "s \<in> challenge_space" "s' \<in> challenge_space"
    and "check_AND (x0,x1) (a0,a1) s (z0,z1)" 
    and "check_AND  (x0,x1) (a0,a1) s' (z0',z1')" 
  shows  "lossless_spmf (\<A>ss_AND  (x0,x1) ((a0,a1), s, (z0,z1)) ((a0,a1), s', (z0',z1'))) 
              \<and> (\<forall>w'\<in>set_spmf (\<A>ss_AND  (x0,x1) ((a0,a1), s, (z0,z1)) ((a0,a1), s', (z0',z1'))). ((x0,x1), w') \<in> Rel_AND)"
proof-
  have x0_in_dom: "x0 \<in> valid_pub0" and x1_in_dom: "x1 \<in> valid_pub1" 
    using valid_pub valid_pub_AND_def by auto
  moreover have 3: "check0 x0 a0 s z0"
      using assms  by simp 
  moreover have 4: "check1 x1 a1 s' z1'"
    using assms by simp 
  moreover have "w0 \<in> set_spmf (\<A>ss0 x0 (a0, s, z0) (a0, s', z0')) \<longrightarrow> (x0,w0) \<in> Rel0" for w0
    using 3 4 \<Sigma>0.special_soundness_def \<Sigma>_prot0 \<Sigma>0.\<Sigma>_protocol_def x0_in_dom challenge_space_def assms valid_pub_AND_def valid_pub by fastforce
  moreover have "w1 \<in> set_spmf (\<A>ss1 x1 (a1, s, z1) (a1, s', z1')) \<longrightarrow> (x1,w1) \<in> Rel1" for w1
     using 3 4 \<Sigma>1.special_soundness_def \<Sigma>_prot1 \<Sigma>1.\<Sigma>_protocol_def x1_in_dom challenge_space_def assms valid_pub_AND_def valid_pub by fastforce 
  ultimately show ?thesis
    by(auto simp add: lossless_\<A>ss Rel_AND_def) 
qed

lemma special_soundness:
  shows "\<Sigma>_AND.special_soundness"
  using \<Sigma>_AND.special_soundness_def ss by fast

theorem \<Sigma>_protocol:
  shows "\<Sigma>_AND.\<Sigma>_protocol"
  by(auto simp add: \<Sigma>_AND.\<Sigma>_protocol_def completeness HVZK special_soundness)

sublocale AND_\<Sigma>_commit: \<Sigma>_protocols_to_commitments init_AND response_AND check_AND Rel_AND S_AND \<A>ss_AND challenge_space valid_pub_AND G 
  apply unfold_locales
  by(auto simp add: \<Sigma>_protocol set_spmf_G_L lossless_G lossless_init_AND lossless_response_AND)

lemma "AND_\<Sigma>_commit.abstract_com.correct"
  using AND_\<Sigma>_commit.commit_correct by simp

lemma "AND_\<Sigma>_commit.abstract_com.perfect_hiding_ind_cpa \<A>"
  using AND_\<Sigma>_commit.perfect_hiding by blast

lemma bind_advantage_bound_dis_log: 
  shows "AND_\<Sigma>_commit.abstract_com.bind_advantage \<A> \<le> AND_\<Sigma>_commit.rel_advantage (AND_\<Sigma>_commit.adversary \<A>)"
  using AND_\<Sigma>_commit.bind_advantage by simp

end

end