section\<open>\<open>\<Sigma>\<close>-Protocols\<close>

text\<open>\<open>\<Sigma>\<close>-protocols were first introduced as an abstract notion by Cramer \cite{Cramerthesis}. 
We point the reader to \cite{sigma_protocols} for a good introduction to the primitive as well as informal proofs
of many of the constructions we formalise in this work. In particular the construction of commitment schemes from 
\<open>\<Sigma>\<close>-protocols and the construction of compound AND and OR statements.

In this section we define \<open>\<Sigma>\<close>-protocols then provide a general proof that they can be used to construct commitment schemes.
Defining security for \<open>\<Sigma>\<close>-protocols uses a mixture of the game-based and simulation-based paradigms. The honest verifier 
zero knowledge property is considered using simulation-based proof, thus we follow the follow the simulation-based formalisation 
of \cite{DBLP:journals/afp/AspinallB19} and \cite{DBLP:conf/itp/Butler0G17}.\<close>

subsection\<open>Defining \<open>\<Sigma>\<close>-protocols\<close>

theory Sigma_Protocols imports
  CryptHOL.CryptHOL
  Commitment_Schemes
begin

type_synonym ('msg', 'challenge', 'response') conv_tuple = "('msg' \<times> 'challenge' \<times> 'response')"

type_synonym ('msg','response') sim_out = "('msg' \<times> 'response')"

type_synonym ('pub_input', 'msg', 'challenge', 'response', 'witness') prover_adversary 
                  = "'pub_input' \<Rightarrow> ('msg', 'challenge', 'response') conv_tuple 
                        \<Rightarrow> ('msg', 'challenge', 'response') conv_tuple \<Rightarrow> 'witness' spmf"

locale \<Sigma>_protocols_base =
  fixes init :: "'pub_input \<Rightarrow> 'witness \<Rightarrow> ('rand \<times> 'msg) spmf" \<comment> \<open>initial message in \<open>\<Sigma>\<close>-protocol\<close>
    and response :: "'rand \<Rightarrow> 'witness \<Rightarrow> 'challenge  \<Rightarrow> 'response spmf" 
    and check :: "'pub_input \<Rightarrow> 'msg \<Rightarrow> 'challenge \<Rightarrow> 'response \<Rightarrow> bool"
    and Rel :: "('pub_input \<times> 'witness) set" \<comment> \<open>The relation the \<open>\<Sigma>\<close> protocol is considered over\<close>
    and S_raw :: "'pub_input \<Rightarrow> 'challenge \<Rightarrow> ('msg, 'response) sim_out spmf" \<comment> \<open>Simulator for the HVZK property\<close>
    and \<A>ss :: "('pub_input, 'msg, 'challenge, 'response, 'witness) prover_adversary" \<comment> \<open>Special soundness adversary\<close>
    and challenge_space :: "'challenge set" \<comment> \<open>The set of valid challenges\<close>
    and valid_pub :: "'pub_input set"
  assumes domain_subset_valid_pub: "Domain Rel \<subseteq> valid_pub"
begin

lemma assumes "x \<in> Domain Rel" shows "\<exists> w. (x,w) \<in> Rel"
  using assms by auto

text\<open>The language defined by the relation is the set of all public inputs such that there exists a witness that satisfies the relation.\<close> 

definition "L \<equiv> {x. \<exists> w. (x, w) \<in> Rel}"

text\<open>The first property of \<open>\<Sigma>\<close>-protocols we consider is completeness, we define a probabilistic programme 
that runs the components of the protocol and outputs the boolean defined by the check algorithm.\<close>

definition completeness_game :: "'pub_input \<Rightarrow> 'witness \<Rightarrow> 'challenge \<Rightarrow> bool spmf"
  where "completeness_game h w e = do {
    (r, a) \<leftarrow> init h w;
    z \<leftarrow> response r w e;
    return_spmf (check h a e z)}" 

text\<open>We define completeness as the probability that the completeness-game returns true for all challenges assuming the relation holds on \<open>h\<close> and \<open>w\<close>.\<close>

definition "completeness \<equiv> (\<forall> h w e . (h,w) \<in> Rel \<longrightarrow> e \<in> challenge_space \<longrightarrow> spmf (completeness_game h w e) True = 1)"

text\<open>Second we consider the honest verifier zero knowledge property (HVZK). To reason about this we construct the real view of the 
\<open>\<Sigma>\<close>-protocol given a challenge \<open>e\<close> as input.\<close>

definition R :: "'pub_input \<Rightarrow> 'witness \<Rightarrow> 'challenge \<Rightarrow> ('msg, 'challenge, 'response) conv_tuple spmf"
  where "R h w e = do { 
    (r,a) \<leftarrow> init h w;
    z \<leftarrow> response r w e;
    return_spmf (a,e,z)}"

definition S where "S h e = map_spmf (\<lambda> (a, z). (a, e, z)) (S_raw h e)"

lemma lossless_S_raw_imp_lossless_S: "lossless_spmf (S_raw h e) \<longrightarrow> lossless_spmf (S h e)"
  by(simp add: S_def)

text\<open>The HVZK property requires that the simulator's output distribution is equal to the real views output distribution.\<close> 

definition "HVZK \<equiv> (\<forall>e \<in> challenge_space. 
                      (\<forall>(h, w)\<in>Rel. R h w e = S h e)
                        \<and> (\<forall>h \<in> valid_pub. \<forall>(a, z) \<in> set_spmf (S_raw h e). check h a e z))"

text\<open>The final property to consider is that of special soundness. This says that given two valid transcripts such that the challenges 
are not equal there exists an adversary \<open>\<A>ss\<close> that can output the witness.\<close>  

definition "special_soundness \<equiv> (\<forall> h e e' a z z'. h \<in> valid_pub \<longrightarrow> e \<in> challenge_space \<longrightarrow> e' \<in> challenge_space \<longrightarrow>  e \<noteq> e' 
              \<longrightarrow> check h a e z \<longrightarrow> check h a e' z' \<longrightarrow> (lossless_spmf (\<A>ss h (a,e,z) (a, e', z')) \<and> 
                  (\<forall>w'\<in>set_spmf (\<A>ss h (a,e,z) (a,e',z')). (h,w') \<in> Rel)))"

lemma special_soundness_alt:
  "special_soundness \<longleftrightarrow>
      (\<forall> h a e z e' z'. e \<in> challenge_space \<longrightarrow> e' \<in> challenge_space \<longrightarrow> h \<in> valid_pub 
          \<longrightarrow> e \<noteq> e' \<longrightarrow> check h a e z \<and> check h a e' z' 
              \<longrightarrow> bind_spmf (\<A>ss h (a,e,z) (a,e',z')) (\<lambda> w'. return_spmf ((h,w') \<in> Rel)) = return_spmf True)"
  apply(auto simp add: special_soundness_def map_spmf_conv_bind_spmf[symmetric] map_pmf_eq_return_pmf_iff in_set_spmf lossless_iff_set_pmf_None)
  apply(metis Domain.DomainI in_set_spmf not_Some_eq)
  using Domain.intros by blast +

definition "\<Sigma>_protocol \<equiv> completeness \<and> special_soundness \<and> HVZK"

text\<open>General lemmas\<close>

lemma lossless_complete_game: 
  assumes lossless_init: "\<forall> h w. lossless_spmf (init h w)"
    and lossless_response: "\<forall> r w e. lossless_spmf (response r w e)"
  shows "lossless_spmf (completeness_game h w e)"
  by(simp add: completeness_game_def lossless_init lossless_response split_def)

lemma complete_game_return_true:
  assumes "(h,w) \<in> Rel" 
    and "completeness"
    and lossless_init: "\<forall> h w. lossless_spmf (init h w)"
    and lossless_response: "\<forall> r w e. lossless_spmf (response r w e)"
    and "e \<in> challenge_space"
  shows "completeness_game h w e = return_spmf True"  
proof -
  have "spmf (completeness_game h w e) True = spmf (return_spmf True) True"
    using assms \<Sigma>_protocol_def completeness_def by fastforce
  then have "completeness_game h w e = return_spmf True"
    by (metis (full_types) lossless_complete_game lossless_init lossless_response lossless_return_spmf spmf_False_conv_True spmf_eqI)
  then show ?thesis 
    by (simp add: completeness_game_def)
qed 

lemma HVZK_unfold1:
  assumes "\<Sigma>_protocol" 
  shows "\<forall> h w e. (h,w) \<in> Rel \<longrightarrow> e \<in> challenge_space \<longrightarrow> R h w e = S h e" 
  using assms by(auto simp add: \<Sigma>_protocol_def HVZK_def)

lemma HVZK_unfold2:
  assumes "\<Sigma>_protocol" 
  shows "\<forall> h e out. e \<in> challenge_space \<longrightarrow> h \<in> valid_pub \<longrightarrow> out \<in> set_spmf (S_raw h e) \<longrightarrow> check h (fst out) e (snd out)"
  using assms by(auto simp add: \<Sigma>_protocol_def HVZK_def split_def)

lemma HVZK_unfold2_alt:
  assumes "\<Sigma>_protocol" 
  shows "\<forall> h a e z. e \<in> challenge_space \<longrightarrow> h \<in> valid_pub \<longrightarrow> (a,z) \<in> set_spmf (S_raw h e) \<longrightarrow> check h a e z"
  using assms by(fastforce simp add: \<Sigma>_protocol_def HVZK_def)

end

subsection\<open>Commitments from \<open>\<Sigma>\<close>-protocols\<close>

text\<open>In this section we provide a general proof that \<open>\<Sigma>\<close>-protocols can be used to construct commitment schemes. 
We follow  the construction given by Damgard in \cite{sigma_protocols}.\<close>

locale \<Sigma>_protocols_to_commitments = \<Sigma>_protocols_base init response check Rel S_raw \<A>ss challenge_space valid_pub
  for init :: "'pub_input \<Rightarrow> 'witness \<Rightarrow> ('rand \<times> 'msg) spmf"
    and response :: "'rand \<Rightarrow> 'witness \<Rightarrow> 'challenge \<Rightarrow> 'response spmf"
    and check :: "'pub_input \<Rightarrow> 'msg \<Rightarrow> 'challenge \<Rightarrow> 'response \<Rightarrow> bool"
    and Rel :: "('pub_input \<times> 'witness) set"
    and S_raw :: "'pub_input \<Rightarrow> 'challenge \<Rightarrow> ('msg, 'response) sim_out spmf"
    and \<A>ss :: "('pub_input, 'msg, 'challenge, 'response, 'witness) prover_adversary"
    and challenge_space :: "'challenge set"
    and valid_pub :: "'pub_input set"
    and G :: "('pub_input \<times> 'witness) spmf" \<comment> \<open>generates pairs that satisfy the relation\<close>
    +
  assumes \<Sigma>_prot: "\<Sigma>_protocol" \<comment> \<open>assume we have a \<open>\<Sigma>\<close>-protocol\<close>
    and set_spmf_G_rel [simp]: "(h,w) \<in> set_spmf G \<Longrightarrow> (h,w) \<in> Rel" \<comment> \<open>the generator has the desired property\<close>  
    and lossless_G: "lossless_spmf G"
    and lossless_init: "lossless_spmf (init h w)"
    and lossless_response: "lossless_spmf (response r w e)"
begin

lemma set_spmf_G_domain_rel [simp]: "(h,w) \<in> set_spmf G \<Longrightarrow> h \<in> Domain Rel" 
  using set_spmf_G_rel by fast

lemma set_spmf_G_L [simp]: "(h,w) \<in> set_spmf G \<Longrightarrow> h \<in> L"
  by (metis mem_Collect_eq set_spmf_G_rel L_def)

text\<open>We define the advantage associated with the hard relation, this is used in the proof of the binding property where
we reduce the binding advantage to the relation advantage.\<close>

definition rel_game :: "('pub_input \<Rightarrow> 'witness spmf) \<Rightarrow> bool spmf"
  where "rel_game \<A> = TRY do {
    (h,w) \<leftarrow> G;
    w' \<leftarrow> \<A> h;
    return_spmf ((h,w') \<in> Rel)} ELSE return_spmf False"

definition rel_advantage :: "('pub_input \<Rightarrow> 'witness spmf) \<Rightarrow> real"
  where "rel_advantage \<A> \<equiv> spmf (rel_game \<A>) True"

text\<open>We now define the algorithms that define the commitment scheme constructed from a \<open>\<Sigma>\<close>-protocol.\<close>

definition key_gen :: "('pub_input \<times>  ('pub_input \<times> 'witness)) spmf"
  where 
   "key_gen = do {
    (x,w) \<leftarrow> G;
    return_spmf (x, (x,w))}"

definition commit :: "'pub_input \<Rightarrow> 'challenge \<Rightarrow> ('msg \<times>  'response) spmf"
  where
    "commit x e = do {
    (a,e,z) \<leftarrow> S x e;
    return_spmf (a, z)}"

definition verify :: "('pub_input \<times> 'witness) \<Rightarrow> 'challenge \<Rightarrow> 'msg \<Rightarrow>  'response \<Rightarrow> bool"
  where "verify x e a z = (check (fst x) a e z)"

text\<open>We allow the adversary to output any message, so this means the type constraint is enough\<close>

definition "valid_msg m = (m \<in> challenge_space)"

text\<open>Showing the construction of a commitment scheme from a \<open>\<Sigma>\<close>-protocol is a  valid commitment scheme is trivial.\<close>

sublocale abstract_com: abstract_commitment key_gen commit verify valid_msg .

paragraph\<open>Correctness\<close>

lemma commit_correct:
  shows "abstract_com.correct"
  including monad_normalisation
proof-
  have "\<forall> m \<in> challenge_space. abstract_com.correct_game m = return_spmf True"
  proof
    fix m
    assume m: "m \<in> challenge_space"
    show "abstract_com.correct_game m = return_spmf True"
    proof-
    have "abstract_com.correct_game m = do {
      (ck, (vk1,vk2)) \<leftarrow> key_gen;
      (a,e,z) \<leftarrow> S ck m;
      return_spmf (check vk1 a m z)}" 
      unfolding abstract_com.correct_game_def
      by(simp add: commit_def verify_def split_def)
    also have "... = do { 
      (x,w) \<leftarrow> G;
      let (ck, (vk1,vk2)) = (x,(x,w));
      (a,e,z) \<leftarrow> S ck m;
      return_spmf (check vk1 a m z)}"
      by(simp add: key_gen_def split_def)
    also have "... = do {
      (x,w) \<leftarrow> G;
      (a,e,z) \<leftarrow> S x m;
      return_spmf (check x a m z)}"
      by(simp add: Let_def)
    also have "... = do {
      (x,w) \<leftarrow> G;
      (a, e,z) \<leftarrow> R x w m;
      return_spmf (check x a m z)}"
      using \<Sigma>_prot HVZK_unfold1 m
      by(intro bind_spmf_cong bind_spmf_cong[OF refl]; clarsimp?)
    also have "... = do {
      (x,w) \<leftarrow> G;
      (r, a) \<leftarrow> init x w;
      z \<leftarrow> response r w m;
      return_spmf (check x a m z)}"
      by(simp add: R_def split_def)
    also have "... = do {
      (x,w) \<leftarrow> G;
      return_spmf True}"
      apply(intro bind_spmf_cong bind_spmf_cong[OF refl]; clarsimp?)
      using complete_game_return_true lossless_init lossless_response \<Sigma>_prot \<Sigma>_protocol_def
      by(simp add: split_def completeness_game_def \<Sigma>_protocols_base.\<Sigma>_protocol_def m cong: bind_spmf_cong_simp)
    ultimately show "abstract_com.correct_game m = return_spmf True"
      by(simp add: bind_spmf_const lossless_G lossless_weight_spmfD split_def)
  qed
qed
  thus ?thesis 
    using abstract_com.correct_def abstract_com.valid_msg_set_def valid_msg_def by simp
qed

paragraph\<open>The hiding property\<close>

text\<open>We first show we have perfect hiding with respect to the hiding game that allows the adversary to choose
the messages that are committed to, this is akin to the ind-cpa game for encryption schemes.\<close>

lemma perfect_hiding:
  shows "abstract_com.perfect_hiding_ind_cpa \<A>"
  including monad_normalisation
proof-
  obtain \<A>1 \<A>2 where [simp]: "\<A> = (\<A>1, \<A>2)" by(cases \<A>)
  have "abstract_com.hiding_game_ind_cpa (\<A>1, \<A>2) = TRY do {
    (x,w) \<leftarrow> G;
    ((m0, m1), \<sigma>) \<leftarrow> \<A>1 (x,w);
    _ :: unit \<leftarrow> assert_spmf (valid_msg m0 \<and> valid_msg m1);
    b \<leftarrow> coin_spmf; 
    (a,e,z) \<leftarrow> S x (if b then m0 else m1);
    b' \<leftarrow> \<A>2 a \<sigma>;
    return_spmf (b' = b)} ELSE coin_spmf"
    by(simp add: abstract_com.hiding_game_ind_cpa_def commit_def; simp add: key_gen_def split_def)
  also have "... = TRY do {
    (x,w) \<leftarrow> G;
    ((m0, m1), \<sigma>) \<leftarrow> \<A>1 (x,w);
    _ :: unit \<leftarrow> assert_spmf (valid_msg m0 \<and> valid_msg m1);
    b :: bool \<leftarrow> coin_spmf; 
    (a,e,z) \<leftarrow> R x w (if b then m0 else m1);
    b' :: bool \<leftarrow> \<A>2 a \<sigma>;
    return_spmf (b' = b)} ELSE coin_spmf"
    apply(intro try_spmf_cong bind_spmf_cong[OF refl]; clarsimp?)+
    by(simp add: \<Sigma>_prot  HVZK_unfold1 valid_msg_def)
  also have "... = TRY do {
    (x,w) \<leftarrow> G;
    ((m0, m1), \<sigma>) \<leftarrow> \<A>1 (x,w);
    _ :: unit \<leftarrow> assert_spmf (valid_msg m0 \<and> valid_msg m1);
    b \<leftarrow> coin_spmf; 
    (r,a) \<leftarrow> init x w;
    z :: 'response \<leftarrow> response r w (if b then m0 else m1);
    guess :: bool \<leftarrow> \<A>2 a \<sigma>;
    return_spmf(guess = b)} ELSE coin_spmf"
    using \<Sigma>_protocols_base.R_def 
    by(simp add: bind_map_spmf o_def R_def split_def)
  also have  "... = TRY do {
    (x,w) \<leftarrow> G;
    ((m0, m1), \<sigma>) \<leftarrow> \<A>1 (x,w);
    _ :: unit \<leftarrow> assert_spmf (valid_msg m0 \<and> valid_msg m1);
    b \<leftarrow> coin_spmf; 
    (r,a) \<leftarrow> init x w;
    guess :: bool \<leftarrow> \<A>2 a \<sigma>;
    return_spmf(guess = b)} ELSE coin_spmf"
    by(simp add: bind_spmf_const lossless_response lossless_weight_spmfD)
  also have  "... = TRY do {
    (x,w) \<leftarrow> G;
    ((m0, m1), \<sigma>) \<leftarrow> \<A>1 (x,w);
    _ :: unit \<leftarrow> assert_spmf (valid_msg m0 \<and> valid_msg m1);
    (r,a) \<leftarrow> init x w;
    guess :: bool \<leftarrow> \<A>2 a \<sigma>;
    map_spmf( (=) guess) coin_spmf} ELSE coin_spmf"
    apply(simp add: map_spmf_conv_bind_spmf)
    by(simp add: split_def)
  also have "... = coin_spmf" 
    by(auto simp add: map_eq_const_coin_spmf try_bind_spmf_lossless2' Let_def split_def bind_spmf_const scale_bind_spmf weight_spmf_le_1 scale_scale_spmf)
  ultimately have "spmf (abstract_com.hiding_game_ind_cpa \<A>) True = 1/2"
    by(simp add: spmf_of_set)
  thus ?thesis
    by (simp add: abstract_com.perfect_hiding_ind_cpa_def abstract_com.hiding_advantage_ind_cpa_def)
qed

text\<open>We reduce the security of the binding property to the relation advantage. To do this we first construct 
an adversary that interacts with the relation game. This adversary succeeds if the binding adversary succeeds.\<close>

definition adversary :: "('pub_input \<Rightarrow> ('msg \<times> 'challenge \<times> 'response \<times> 'challenge \<times> 'response) spmf) \<Rightarrow> 'pub_input \<Rightarrow> 'witness spmf"
  where "adversary \<A> x = do {
    (c, e, ez, e', ez') \<leftarrow> \<A> x;
    \<A>ss x (c,e,ez) (c,e',ez')}"

lemma bind_advantage:
  shows "abstract_com.bind_advantage \<A> \<le> rel_advantage (adversary \<A>)"
proof-
  have "abstract_com.bind_game \<A> = TRY do {
  (x,w) \<leftarrow> G;
  (c, m, d, m', d') \<leftarrow> \<A> x;
  _ :: unit \<leftarrow> assert_spmf (m \<noteq> m' \<and> m \<in> challenge_space \<and> m' \<in> challenge_space);
  let b = check x c m d;
  let b' = check x c m' d';
  _ :: unit \<leftarrow> assert_spmf (b \<and> b'); 
  w' \<leftarrow> \<A>ss x (c,m, d) (c,m', d');
  return_spmf ((x,w') \<in> Rel)} ELSE return_spmf False"
    unfolding abstract_com.bind_game_alt_def 
    apply(simp add:  key_gen_def verify_def Let_def split_def valid_msg_def)
    apply(intro try_spmf_cong bind_spmf_cong[OF refl]; clarsimp?)+
    using special_soundness_def \<Sigma>_prot \<Sigma>_protocol_def special_soundness_alt special_soundness_def set_spmf_G_rel set_spmf_G_domain_rel 
    by (smt basic_trans_rules(31) bind_spmf_cong domain_subset_valid_pub)
  hence "abstract_com.bind_advantage \<A> \<le> spmf (TRY do {
  (x,w) \<leftarrow> G;
  (c, m, d, m', d') \<leftarrow> \<A> x;
  w' \<leftarrow> \<A>ss x (c,m, d) (c,m', d');
  return_spmf ((x,w') \<in> Rel)} ELSE return_spmf False) True"
    unfolding abstract_com.bind_advantage_def
    apply(simp add: spmf_try_spmf)
    apply(rule ord_spmf_eq_leD)
    apply(rule ord_spmf_bind_reflI;clarsimp)+
    by(simp add: assert_spmf_def)
  thus ?thesis
    by(simp add: rel_game_def adversary_def split_def rel_advantage_def)
qed

end

end
