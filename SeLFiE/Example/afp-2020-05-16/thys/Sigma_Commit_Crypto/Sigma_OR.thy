subsection\<open>\<open>\<Sigma>\<close>-OR statements\<close>

theory Sigma_OR imports
  Sigma_Protocols
  Xor
begin 

locale \<Sigma>_OR_base = \<Sigma>0: \<Sigma>_protocols_base init0 response0 check0 Rel0 S0_raw \<A>ss0 "carrier L" valid_pub0
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
    and G :: "(('pub0 \<times> 'pub1)  \<times> ('witness0 + 'witness1)) spmf"
    and L :: "'bool boolean_algebra" (structure)
    + 
  assumes \<Sigma>_prot1: "\<Sigma>1.\<Sigma>_protocol"  
    and \<Sigma>_prot0: "\<Sigma>0.\<Sigma>_protocol"  
    and lossless_init: "lossless_spmf (init0 h0 w0)" "lossless_spmf (init1 h1 w1)"
    and lossless_response: "lossless_spmf (response0 r0 w0 e0)" "lossless_spmf (response1 r1 w1 e1)"
    and lossless_S: "lossless_spmf (S0 h0 e0)" "lossless_spmf (S1 h1 e1)"
    and finite_L: "finite (carrier L)"
    and carrier_L_not_empty: "carrier L \<noteq> {}"
    and lossless_G: "lossless_spmf G"
begin

inductive_set Rel_OR :: "(('pub0 \<times> 'pub1) \<times> ('witness0 + 'witness1)) set" where
  Rel_OR_I0: "((x0, x1), Inl w0) \<in> Rel_OR" if "(x0, w0) \<in> Rel0 \<and> x1 \<in> valid_pub1"
| Rel_OR_I1: "((x0, x1), Inr w1) \<in> Rel_OR" if "(x1, w1) \<in> Rel1 \<and> x0 \<in> valid_pub0"

inductive_simps Rel_OR_simps [simp]:
  "((x0, x1), Inl w0) \<in> Rel_OR"
  "((x0, x1), Inr w1) \<in> Rel_OR"

lemma Domain_Rel_cases: 
  assumes "(x0,x1) \<in> Domain Rel_OR"
  shows "(\<exists> w0. (x0,w0) \<in> Rel0 \<and> x1 \<in> valid_pub1) \<or> (\<exists> w1. (x1,w1) \<in> Rel1 \<and> x0 \<in> valid_pub0)"
  using assms 
  by (meson DomainE Rel_OR.cases)

lemma set_spmf_lists_sample [simp]: "set_spmf (spmf_of_set (carrier L)) = (carrier L)"
  using finite_L by simp

definition "challenge_space = carrier L"
 
fun init_OR :: "('pub0 \<times> 'pub1) \<Rightarrow> ('witness0 + 'witness1) \<Rightarrow> (((('rand0 \<times> 'bool \<times> 'response1 + 'rand1 \<times> 'bool \<times> 'response0)) \<times> 'msg0 \<times> 'msg1)) spmf"
  where "init_OR (x0,x1) (Inl w0) = do {
    (r0,a0) \<leftarrow> init0 x0 w0;
    e1 \<leftarrow> spmf_of_set (carrier L);
    (a1, e'1, z1) \<leftarrow> \<Sigma>1.S x1 e1;
    return_spmf (Inl (r0, e1, z1), a0, a1)}" |
    "init_OR (x0, x1) (Inr w1) = do {
    (r1, a1) \<leftarrow> init1 x1 w1;
    e0 \<leftarrow> spmf_of_set (carrier L);
    (a0, e'0, z0) \<leftarrow> \<Sigma>0.S x0 e0;
    return_spmf ((Inr (r1, e0, z0), a0, a1))}"

lemma lossless_\<Sigma>_S: "lossless_spmf (\<Sigma>1.S x1 e1)" "lossless_spmf (\<Sigma>0.S x0 e0)"
  using lossless_S by fast +

lemma lossless_init_OR: "lossless_spmf (init_OR (x0,x1) w)"
  by(cases w;simp add: lossless_\<Sigma>_S split_def lossless_init lossless_S finite_L carrier_L_not_empty) 

fun response_OR :: "(('rand0 \<times> 'bool \<times> 'response1 + 'rand1 \<times> 'bool \<times> 'response0)) \<Rightarrow> ('witness0 + 'witness1) 
                        \<Rightarrow> 'bool \<Rightarrow> (('bool \<times> 'response0) \<times> ('bool \<times> 'response1)) spmf"
  where "response_OR (Inl (r0 , e_1, z1)) (Inl w0) s = do {  
    let e0 = s \<oplus> e_1;
    z0 \<leftarrow> response0 r0 w0 e0;
    return_spmf ((e0,z0),  (e_1,z1))}" |
    "response_OR  (Inr (r1, e_0, z0)) (Inr w1) s = do {
    let e1 = s \<oplus> e_0;
    z1 \<leftarrow> response1 r1 w1 e1;
    return_spmf ((e_0, z0), (e1, z1))}" 

definition check_OR :: "('pub0 \<times> 'pub1) \<Rightarrow> ('msg0 \<times> 'msg1) \<Rightarrow> 'bool \<Rightarrow> (('bool \<times> 'response0) \<times> ('bool \<times> 'response1)) \<Rightarrow> bool"
  where "check_OR X A s Z
             = (s = (fst (fst Z)) \<oplus> (fst (snd Z)) 
                   \<and> (fst (fst Z)) \<in> challenge_space \<and> (fst (snd Z)) \<in> challenge_space 
                      \<and> check0 (fst X) (fst A) (fst (fst Z)) (snd (fst Z)) \<and> check1 (snd X) (snd A) (fst (snd Z)) (snd (snd Z)))"

lemma  "check_OR (x0,x1) (a0,a1) s ((e0,z0), (e1,z1))
             = (s = e0 \<oplus> e1 
                   \<and> e0 \<in> challenge_space \<and> e1 \<in> challenge_space 
                      \<and> check0 x0 a0 e0 z0 \<and> check1 x1 a1 e1 z1)"
  by(simp add: check_OR_def)

fun S_OR where "S_OR (x0,x1) c = do {
    e1 \<leftarrow> spmf_of_set (carrier L);
    (a1, e1', z1) \<leftarrow> \<Sigma>1.S x1 e1;
    let e0 = c \<oplus> e1;
    (a0, e0', z0) \<leftarrow> \<Sigma>0.S x0 e0; 
    let z = ((e0',z0), (e1',z1));
    return_spmf ((a0, a1),z)}"

definition \<A>ss_OR' :: "'pub0 \<times> 'pub1 \<Rightarrow> ('msg0 \<times> 'msg1) \<times> 'bool \<times> ('bool \<times> 'response0) \<times> 'bool \<times> 'response1
                    \<Rightarrow> ('msg0 \<times> 'msg1) \<times> 'bool \<times> ('bool \<times> 'response0) \<times> 'bool \<times> 'response1 \<Rightarrow> ('witness0 + 'witness1) spmf"
  where "\<A>ss_OR' X C1 C2 = TRY do {
    _ :: unit \<leftarrow> assert_spmf ((fst (fst  (snd (snd C1)))) \<noteq> (fst (fst (snd (snd C2)))));
    w0 :: 'witness0 \<leftarrow> \<A>ss0 (fst X) (fst (fst C1),fst (fst (snd (snd C1))),snd (fst (snd (snd C1)))) (fst (fst C2),fst (fst (snd (snd C2))),snd (fst (snd (snd C2))));
    return_spmf ((Inl w0)) :: ('witness0 + 'witness1) spmf} ELSE do {
     w1 :: 'witness1 \<leftarrow> \<A>ss1  (snd X) (snd (fst C1),fst (snd (snd (snd C1))), snd (snd (snd (snd C1)))) (snd (fst C2), fst (snd (snd (snd C2))), snd (snd (snd (snd C2))));
    (return_spmf ((Inr w1)) :: ('witness0 + 'witness1) spmf)}"

definition \<A>ss_OR :: "'pub0 \<times> 'pub1 \<Rightarrow> ('msg0 \<times> 'msg1) \<times> 'bool \<times> ('bool \<times> 'response0) \<times> 'bool \<times> 'response1
                    \<Rightarrow> ('msg0 \<times> 'msg1) \<times> 'bool \<times> ('bool \<times> 'response0) \<times> 'bool \<times> 'response1 \<Rightarrow> ('witness0 + 'witness1) spmf"
  where "\<A>ss_OR X C1 C2 = do {
    if ((fst (fst  (snd (snd C1)))) \<noteq> (fst (fst (snd (snd C2))))) then do 
        {w0 :: 'witness0 \<leftarrow> \<A>ss0 (fst X) (fst (fst C1),fst (fst (snd (snd C1))),snd (fst (snd (snd C1)))) (fst (fst C2),fst (fst (snd (snd C2))),snd (fst (snd (snd C2)))); return_spmf (Inl w0)} 
    else
    do  {w1 :: 'witness1 \<leftarrow> \<A>ss1  (snd X) (snd (fst C1),fst (snd (snd (snd C1))), snd (snd (snd (snd C1)))) (snd (fst C2), fst (snd (snd (snd C2))), snd (snd (snd (snd C2)))); return_spmf (Inr w1)}}"

lemma \<A>ss_OR_alt_def: "\<A>ss_OR (x0,x1) ((a0,a1),s,(e0,z0),e1,z1) ((a0,a1),s',(e0',z0'),e1',z1') = do {
    if (e0 \<noteq> e0') then do {w0 :: 'witness0 \<leftarrow> \<A>ss0 x0 (a0,e0,z0) (a0,e0',z0'); return_spmf (Inl w0)}
    else do {w1 :: 'witness1 \<leftarrow> \<A>ss1 x1 (a1,e1,z1) (a1,e1',z1'); return_spmf (Inr w1)}}"
  by(simp add: \<A>ss_OR_def)

definition "valid_pub_OR = {(x0,x1). x0 \<in> valid_pub0 \<and> x1 \<in> valid_pub1}"

sublocale \<Sigma>_OR: \<Sigma>_protocols_base init_OR response_OR check_OR Rel_OR S_OR \<A>ss_OR challenge_space valid_pub_OR 
  unfolding \<Sigma>_protocols_base_def
proof(goal_cases)
  case 1
  then show ?case 
  proof
    fix x 
    assume asm: "x \<in> Domain Rel_OR"
    then obtain x0 x1 where x: "(x0,x1) = x" 
      by (metis surj_pair)
    show "x \<in> valid_pub_OR"
    proof(cases "\<exists> w0. (x0,w0) \<in> Rel0 \<and> x1 \<in> valid_pub1")
      case True
      then show ?thesis 
        using \<Sigma>0.domain_subset_valid_pub valid_pub_OR_def x by auto
    next
      case False
      hence "\<exists> w1. (x1,w1) \<in> Rel1 \<and> x0 \<in> valid_pub0" 
        using Domain_Rel_cases asm x by auto
      then show ?thesis 
        using \<Sigma>1.domain_subset_valid_pub valid_pub_OR_def x by auto
    qed
  qed
qed

end 

locale \<Sigma>_OR_proofs = \<Sigma>_OR_base + boolean_algebra L +
  assumes G_Rel_OR: "((x0, x1), w) \<in> set_spmf G \<Longrightarrow> ((x0, x1), w) \<in> Rel_OR"
    and lossless_response_OR: "lossless_spmf (response_OR R W s)"
begin

lemma HVZK1:
  assumes "(x1,w1) \<in> Rel1"
  shows "\<forall> c \<in> challenge_space. \<Sigma>_OR.R (x0,x1) (Inr w1) c = \<Sigma>_OR.S (x0,x1) c"
  including monad_normalisation
proof
  fix c
  assume c: "c \<in> challenge_space"
  show "\<Sigma>_OR.R (x0,x1) (Inr w1) c = \<Sigma>_OR.S (x0,x1) c"
  proof-
    have *: "x \<in> carrier L \<longrightarrow> c \<oplus> c \<oplus> x = x" for x  
      using c challenge_space_def by auto
    have "\<Sigma>_OR.R (x0,x1) (Inr w1) c = do {
    (r1, ab1) \<leftarrow> init1 x1 w1;
    eb' \<leftarrow> spmf_of_set (carrier L);
    (ab0', eb0'', zb0') \<leftarrow> \<Sigma>0.S x0 eb';
    let ((r, eb', zb'),a) = ((r1, eb', zb0' ),  ab0' , ab1);
    let eb = c \<oplus> eb';
    zb1 \<leftarrow> response1 r w1 eb;
    let z = ((eb', zb') , (eb, zb1));
    return_spmf (a,c,z)}"
      supply [[simproc del: monad_normalisation]]
      by(simp add: \<Sigma>_OR.R_def split_def Let_def)
    also have "... = do {
    eb' \<leftarrow> spmf_of_set (carrier L);
    (ab0', eb0'', zb0') \<leftarrow> \<Sigma>0.S x0 eb';
    let eb = c \<oplus> eb';
    (ab1, c', zb1) \<leftarrow> \<Sigma>1.R x1 w1 eb;
    let z = ((eb', zb0'), (eb, zb1));
    return_spmf ((ab0',ab1),c,z)}"
      by(simp add: \<Sigma>1.R_def split_def Let_def)
    also have "... = do {
    eb' \<leftarrow> spmf_of_set (carrier L);
    (ab0', eb0'', zb0') \<leftarrow> \<Sigma>0.S x0 eb';
    let eb = c \<oplus> eb';
    (ab1, c', zb1) \<leftarrow> \<Sigma>1.S x1 eb;
    let z = ((eb', zb0'), (eb, zb1));
    return_spmf ((ab0',ab1),c,z)}"
      using c
      by(simp add: split_def Let_def \<Sigma>_prot1 \<Sigma>1.HVZK_unfold1 assms challenge_space_def  cong: bind_spmf_cong_simp)
    also have "... = do {
    eb \<leftarrow> map_spmf (\<lambda> eb'. c \<oplus> eb') (spmf_of_set (carrier L));
    (ab1, c', zb1) \<leftarrow> \<Sigma>1.S x1 eb;
    (ab0', eb0'', zb0') \<leftarrow> \<Sigma>0.S x0 (c \<oplus> eb);
    let z = ((c \<oplus> eb, zb0'), (eb, zb1));
    return_spmf ((ab0',ab1),c,z)}"
      apply(simp add: bind_map_spmf o_def Let_def)
      by(simp add: * split_def cong: bind_spmf_cong_simp)
    also have "... = do {
    eb \<leftarrow> (spmf_of_set (carrier L));
    (ab1, c', zb1) \<leftarrow> \<Sigma>1.S x1 eb;
    (ab0', eb0'', zb0') \<leftarrow> \<Sigma>0.S x0 (c \<oplus> eb);
    let z = ((c \<oplus> eb, zb0'), (eb, zb1));
    return_spmf ((ab0',ab1),c,z)}"
      using assms assms one_time_pad c challenge_space_def by simp
    also have "... = do {
    eb \<leftarrow> (spmf_of_set (carrier L));
    (ab1, c', zb1) \<leftarrow> \<Sigma>1.S x1 eb;
    (ab0', eb0'', zb0') \<leftarrow> \<Sigma>0.S x0 (c \<oplus> eb);
    let z = ((eb0'', zb0'), (c', zb1));
    return_spmf ((ab0',ab1),c,z)}"
      by(simp add: \<Sigma>0.S_def \<Sigma>1.S_def bind_map_spmf o_def split_def)
    ultimately show ?thesis by(simp add: Let_def map_spmf_conv_bind_spmf \<Sigma>_OR.S_def split_def)
  qed
qed

lemma HVZK0: 
  assumes "(x0,w0) \<in> Rel0"
  shows "\<forall> c \<in> challenge_space. \<Sigma>_OR.R (x0,x1) (Inl w0) c = \<Sigma>_OR.S (x0,x1) c"
proof
  fix c 
  assume c: "c \<in> challenge_space"
  show "\<Sigma>_OR.R (x0,x1) (Inl w0) c = \<Sigma>_OR.S (x0,x1) c"
  proof-
    have "\<Sigma>_OR.R (x0,x1) (Inl w0) c = do {
    (r0,ab0) \<leftarrow> init0 x0 w0;
    eb' \<leftarrow> spmf_of_set (carrier L);
    (ab1', eb1'', zb1') \<leftarrow> \<Sigma>1.S x1 eb';
    let ((r, eb', zb'),a) = ((r0, eb', zb1'),  ab0,  ab1');
    let eb = c \<oplus> eb';
    zb0 \<leftarrow> response0 r w0 eb;
    let z = ((eb,zb0), (eb',zb'));
    return_spmf (a,c,z)}"
      by(simp add: \<Sigma>_OR.R_def split_def Let_def)
    also have "... = do {
    eb' \<leftarrow> (spmf_of_set (carrier L));
    (ab1', eb1'', zb1') \<leftarrow> \<Sigma>1.S x1 eb';
    let eb = c \<oplus> eb';
    (ab0, c', zb0) \<leftarrow> \<Sigma>0.R x0 w0 eb;
    let z = ((eb,zb0),  (eb',zb1'));
    return_spmf ((ab0,  ab1'),c,z)}"
      apply(simp add: \<Sigma>0.R_def split_def Let_def)
      apply(rewrite bind_commute_spmf)
      apply(rewrite bind_commute_spmf[of _ "\<Sigma>1.S _ _"])
      by simp
    also have "... = do {
    eb' \<leftarrow> (spmf_of_set (carrier L));
    (ab1', eb1'', zb1') \<leftarrow> \<Sigma>1.S x1 eb';
    let eb = c \<oplus> eb';
    (ab0, c', zb0) \<leftarrow> \<Sigma>0.S x0 eb;
    let z = ((eb,zb0), (eb',zb1'));
    return_spmf ((ab0,  ab1'),c,z)}"
      using c
      by(simp add: \<Sigma>_prot0 \<Sigma>0.HVZK_unfold1 assms challenge_space_def split_def Let_def cong: bind_spmf_cong_simp)
    ultimately show ?thesis
      by(simp add: \<Sigma>_OR.S_def \<Sigma>1.S_def \<Sigma>0.S_def Let_def o_def bind_map_spmf split_def map_spmf_conv_bind_spmf)
  qed
qed

lemma HVZK:
  shows "\<Sigma>_OR.HVZK"
  unfolding \<Sigma>_OR.HVZK_def
  apply auto
  subgoal for e a b w
    apply(cases w)
    using HVZK0 HVZK1 by auto 
  apply(auto simp add: valid_pub_OR_def \<Sigma>_OR.S_def bind_map_spmf o_def check_OR_def image_def \<Sigma>0.S_def \<Sigma>1.S_def split_def challenge_space_def local.xor_ac(1))
  using \<Sigma>0.HVZK_unfold2 \<Sigma>_prot0 challenge_space_def apply force
  using \<Sigma>1.HVZK_unfold2 \<Sigma>_prot1 challenge_space_def by force

lemma assumes "(x0,x1) \<in> Domain Rel_OR"
  shows "(\<exists> w0. (x0,w0) \<in> Rel0) \<or> (\<exists> w1. (x1,w1) \<in> Rel1)"
  using assms Rel_OR.simps by blast

lemma ss: 
  assumes valid_pub_OR: "(x0,x1) \<in> valid_pub_OR" 
    and check: "check_OR (x0,x1) (a0,a1) s ((e0,z0), (e1,z1))"
    and check': "check_OR (x0,x1) (a0,a1) s' ((e0',z0'), (e1',z1'))"
    and "s \<noteq> s'"
    and challenge_space: "s \<in> challenge_space" "s' \<in> challenge_space"
  shows "lossless_spmf (\<A>ss_OR (x0,x1) ((a0,a1),s,(e0,z0), e1,z1) ((a0,a1),s',(e0',z0'), e1',z1')) \<and>
           (\<forall>w'\<in>set_spmf (\<A>ss_OR (x0,x1) ((a0,a1),s,(e0,z0), e1,z1) ((a0,a1),s',(e0',z0'), e1',z1')). ((x0,x1), w') \<in> Rel_OR)"
proof-
  have e_or: "e0 \<noteq> e0' \<or> e1 \<noteq> e1'" using assms check_OR_def by auto
  show ?thesis 
  proof(cases "e0 \<noteq> e0'")
    case True
    moreover have 2: "x0 \<in> valid_pub0" 
      using valid_pub_OR valid_pub_OR_def by simp 
    moreover have 3: "check0 x0 a0 e0 z0" 
      using assms check_OR_def by simp 
    moreover have 4: "check0 x0 a0 e0' z0'"
      using assms check_OR_def by simp 
    moreover have e: "e0 \<in> carrier L" "e0' \<in> carrier L" 
      using challenge_space_def check check' check_OR_def by auto 
    ultimately have "(\<forall>w'\<in>set_spmf (\<A>ss0 x0 (a0,e0,z0) (a0,e0',z0')). (x0, w') \<in> Rel0)" 
      using True \<Sigma>0.\<Sigma>_protocol_def \<Sigma>0.special_soundness_def \<Sigma>_prot0 challenge_space assms by blast
    moreover have  "lossless_spmf (\<A>ss0 x0 (a0, e0, z0) (a0, e0', z0'))"
      using 2 3 4 \<A>ss_OR_def True \<Sigma>_prot0  \<Sigma>0.\<Sigma>_protocol_def \<Sigma>0.special_soundness_def challenge_space_def e by blast
    ultimately have "\<forall> w' \<in> set_spmf (\<A>ss_OR (x0,x1) ((a0,a1),s,(e0,z0), e1,z1) ((a0,a1),s',(e0',z0'), e1',z1')). ((x0,x1),  w') \<in> Rel_OR"
      apply(auto simp only: \<A>ss_OR_alt_def True)
      apply(auto simp add: o_def \<A>ss_OR_def) 
      using assms valid_pub_OR_def by blast
    moreover have "lossless_spmf (\<A>ss_OR (x0,x1) ((a0,a1),s,(e0,z0), e1,z1) ((a0,a1),s',(e0',z0'), e1',z1'))"
      apply(simp add: \<A>ss_OR_def)   
      using 2 3 4 True \<Sigma>_prot0  \<Sigma>0.\<Sigma>_protocol_def \<Sigma>0.special_soundness_def challenge_space e by blast
    ultimately show ?thesis by simp
  next
    case False
    hence e1_neq_e1': "e1 \<noteq> e1'" using e_or by simp
    moreover have 2: "x1 \<in> valid_pub1" 
      using valid_pub_OR valid_pub_OR_def by simp 
    moreover have 3: "check1 x1 a1 e1 z1" 
      using assms check_OR_def by simp
    moreover have 4: "check1 x1 a1 e1' z1'"
      using assms check_OR_def by simp 
    moreover have e: "e1 \<in> carrier L" "e1' \<in> carrier L" 
      using challenge_space_def check check' check_OR_def by auto
    ultimately have "(\<forall>w'\<in>set_spmf (\<A>ss1 x1 (a1,e1,z1) (a1,e1',z1')). (x1,w') \<in> Rel1)" 
      using False \<Sigma>1.\<Sigma>_protocol_def \<Sigma>1.special_soundness_def \<Sigma>_prot1 e1_neq_e1' challenge_space by blast 
    hence "\<forall>w' \<in> set_spmf (\<A>ss_OR (x0,x1) ((a0,a1),s,(e0,z0), e1,z1) ((a0,a1),s',(e0',z0'), e1',z1')). ((x0,x1), w') \<in> Rel_OR"
      apply(auto simp add: o_def \<A>ss_OR_def) 
      using False assms \<Sigma>1.L_def assms valid_pub_OR_def by auto    
    moreover have "lossless_spmf (\<A>ss_OR (x0,x1) ((a0,a1),s,(e0,z0), e1,z1) ((a0,a1),s',(e0',z0'), e1',z1'))"
      apply(simp add: \<A>ss_OR_def)  
      using 2 3 4 \<Sigma>_prot1 \<Sigma>1.\<Sigma>_protocol_def \<Sigma>1.special_soundness_def False e1_neq_e1' challenge_space e by blast
    ultimately show ?thesis by simp
  qed
qed

lemma special_soundness: 
  shows "\<Sigma>_OR.special_soundness"
  unfolding \<Sigma>_OR.special_soundness_def 
  using ss prod.collapse by fastforce

lemma correct0: 
  assumes e_in_carrier: "e \<in> carrier L"
    and "(x0,w0) \<in> Rel0"
    and valid_pub: "x1 \<in> valid_pub1"
  shows "\<Sigma>_OR.completeness_game (x0,x1) (Inl w0) e = return_spmf True"
    (is "?lhs = ?rhs")
proof-
  have "x \<in> carrier L \<longrightarrow> e = (e \<oplus> x) \<oplus> x" for x 
    using e_in_carrier xor_assoc by simp
  hence "?lhs = do {
    (r0,ab0) \<leftarrow> init0 x0 w0;
    eb' \<leftarrow> spmf_of_set (carrier L);
    (ab1', eb1'', zb1') \<leftarrow> \<Sigma>1.S x1 eb';
    let eb = e \<oplus> eb';
    zb0 \<leftarrow> response0 r0 w0 eb;
    return_spmf ((check0 x0 ab0 eb zb0 \<and> check1 x1 ab1' eb' zb1'))}" 
    by(simp add: \<Sigma>_OR.completeness_game_def split_def Let_def challenge_space_def assms check_OR_def cong: bind_spmf_cong_simp)
  also have "... = do {
    eb' \<leftarrow> spmf_of_set (carrier L);
    (ab1', eb1'', zb1') \<leftarrow> \<Sigma>1.S x1 eb';
    let eb = e \<oplus> eb';
    (r0,ab0) \<leftarrow> init0 x0 w0;
    zb0 \<leftarrow> response0 r0 w0 eb;
    return_spmf ((check0 x0 ab0 eb zb0 \<and> check1 x1 ab1' eb' zb1'))}" 
    apply(simp add: Let_def split_def)
    apply(rewrite bind_commute_spmf)
    apply(rewrite bind_commute_spmf[of _ "\<Sigma>1.S _ _"])
    by simp
  also have "... = do {
    eb' :: 'e \<leftarrow> spmf_of_set (carrier L);
    (ab1', eb1'', zb1') \<leftarrow> \<Sigma>1.S x1 eb';
    return_spmf (check1 x1 ab1' eb' zb1')}" 
    apply(simp add: Let_def)
    apply(intro bind_spmf_cong; clarsimp?)+
    subgoal for e' a e z
      apply(cases "check1 x1 a e' z")
      using \<Sigma>0.complete_game_return_true \<Sigma>_prot0 \<Sigma>0.completeness_game_def \<Sigma>0.\<Sigma>_protocol_def  
      by(auto simp add: assms bind_spmf_const lossless_init lossless_response lossless_weight_spmfD split_def cong: bind_spmf_cong_simp)
    done
  also have "... = do {
    eb' :: 'e \<leftarrow> spmf_of_set (carrier L);
    (ab1', eb1'', zb1') \<leftarrow> \<Sigma>1.S x1 eb';
    return_spmf (True)}"
    apply(intro bind_spmf_cong; clarsimp?)
    subgoal for x a aa b
      using  \<Sigma>_prot1 
      apply(auto simp add: \<Sigma>1.S_def split_def image_def \<Sigma>1.HVZK_unfold2_alt)  
      using \<Sigma>1.S_def split_def image_def \<Sigma>1.HVZK_unfold2_alt \<Sigma>_prot1 valid_pub by blast
    done
  ultimately show ?thesis 
    using \<Sigma>1.HVZK_unfold2_alt
    by(simp add: bind_spmf_const Let_def \<Sigma>1.HVZK_unfold2_alt split_def lossless_\<Sigma>_S lossless_weight_spmfD carrier_L_not_empty finite_L)
qed

lemma correct1: 
  assumes rel1: "(x1,w1) \<in> Rel1"
    and valid_pub: "x0 \<in> valid_pub0"
    and e_in_carrier: "e \<in> carrier L"
  shows "\<Sigma>_OR.completeness_game (x0,x1) (Inr w1) e = return_spmf True"
    (is "?lhs = ?rhs")
proof-
  have x1_inL: "x1 \<in> \<Sigma>1.L"
    using \<Sigma>1.L_def rel1 by auto
  have "x \<in> carrier L \<longrightarrow> e = x \<oplus> e \<oplus> x" for x 
    by (simp add: e_in_carrier xor_assoc xor_commute  local.xor_ac(3)) 
  hence "?lhs = do {
    (r1, ab1) \<leftarrow> init1 x1 w1;
    eb' \<leftarrow> spmf_of_set (carrier L);
    (ab0', eb0'', zb0') \<leftarrow> \<Sigma>0.S x0 eb';
    let eb = e \<oplus> eb';
    zb1 \<leftarrow> response1 r1 w1 eb;
    return_spmf (check0 x0 ab0' eb' zb0' \<and> check1 x1 ab1 eb zb1)}" 
    by(simp add: \<Sigma>_OR.completeness_game_def split_def Let_def assms challenge_space_def check_OR_def cong: bind_spmf_cong_simp)
  also have "... = do {
    eb' \<leftarrow> spmf_of_set (carrier L);
    (ab0', eb0'', zb0') \<leftarrow> \<Sigma>0.S x0 eb';
    let eb = e \<oplus> eb';
    (r1, ab1) \<leftarrow> init1 x1 w1;
    zb1 \<leftarrow> response1 r1 w1 eb;
    return_spmf (check0 x0 ab0' eb' zb0' \<and> check1 x1 ab1 eb zb1)}" 
    apply(simp add: Let_def split_def)
    apply(rewrite bind_commute_spmf)
    apply(rewrite bind_commute_spmf[of _ "\<Sigma>0.S _ _"])
    by simp
  also have "... = do {
    eb' \<leftarrow> spmf_of_set (carrier L);
    (ab0', eb0'', zb0') \<leftarrow> \<Sigma>0.S x0 eb';
    return_spmf (check0 x0 ab0' eb' zb0')}" 
    apply(simp add: Let_def)
    apply(intro bind_spmf_cong; clarsimp?)+
    subgoal for e' a e z
      apply(cases "check0 x0 a e' z")
      using \<Sigma>1.complete_game_return_true \<Sigma>_prot1 \<Sigma>1.completeness_game_def \<Sigma>1.\<Sigma>_protocol_def
      by(auto simp add: x1_inL assms bind_spmf_const lossless_init lossless_response lossless_weight_spmfD split_def)
    done
  also have "... = do {
    eb' \<leftarrow> spmf_of_set (carrier L);
    (ab0', eb0'', zb0') \<leftarrow> \<Sigma>0.S x0 eb';
    return_spmf (True)}" 
    apply(intro bind_spmf_cong; clarsimp?)
    subgoal for x a aa b
      using  \<Sigma>_prot0
      by(auto simp add: valid_pub valid_pub_OR_def \<Sigma>0.S_def split_def image_def \<Sigma>0.HVZK_unfold2_alt)  
    done
  ultimately show ?thesis 
    apply(simp add: \<Sigma>0.HVZK_unfold2 Let_def)
    using \<Sigma>0.complete_game_return_true \<Sigma>_OR.completeness_game_def
    by(simp add: bind_spmf_const split_def lossless_\<Sigma>_S(2) lossless_weight_spmfD Let_def carrier_L_not_empty finite_L)
qed

lemma completeness':
  assumes  Rel_OR_asm: "((x0,x1), w) \<in> Rel_OR" 
  shows "\<forall> e \<in> carrier L. spmf (\<Sigma>_OR.completeness_game (x0,x1) w e) True = 1" 
proof
  fix e
  assume asm: "e \<in> carrier L"
  hence "(\<Sigma>_OR.completeness_game (x0,x1) w e) = return_spmf True"
  proof(cases w)
    case inl: (Inl a)
    then show ?thesis 
      using asm correct0 assms inl by auto
  next
    case inr: (Inr b)
    then show ?thesis 
      using asm correct1 assms inr by auto
  qed
  thus "spmf (\<Sigma>_OR.completeness_game (x0,x1) w e) True = 1" 
    by simp
qed

lemma completeness: shows "\<Sigma>_OR.completeness"
  unfolding \<Sigma>_OR.completeness_def
  using completeness' challenge_space_def by auto

lemma \<Sigma>_protocol: shows "\<Sigma>_OR.\<Sigma>_protocol"
 by(simp add: completeness HVZK special_soundness \<Sigma>_OR.\<Sigma>_protocol_def)

sublocale OR_\<Sigma>_commit: \<Sigma>_protocols_to_commitments init_OR response_OR check_OR Rel_OR S_OR \<A>ss_OR challenge_space valid_pub_OR G 
  by unfold_locales (auto simp add: \<Sigma>_protocol lossless_G lossless_init_OR G_Rel_OR lossless_response_OR)

lemma "OR_\<Sigma>_commit.abstract_com.correct"
  using OR_\<Sigma>_commit.commit_correct by simp

lemma "OR_\<Sigma>_commit.abstract_com.perfect_hiding_ind_cpa \<A>"
  using OR_\<Sigma>_commit.perfect_hiding by blast

lemma bind_advantage_bound_dis_log: 
  shows "OR_\<Sigma>_commit.abstract_com.bind_advantage \<A> \<le> OR_\<Sigma>_commit.rel_advantage (OR_\<Sigma>_commit.adversary \<A>)"
  using OR_\<Sigma>_commit.bind_advantage by simp

end

end