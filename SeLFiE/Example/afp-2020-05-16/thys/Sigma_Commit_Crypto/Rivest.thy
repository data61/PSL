subsection\<open>Rivest Commitment Scheme\<close>

text\<open>The Rivest commitment scheme was first introduced in \cite{rivest1999}. We note however the original
scheme did not allow for perfect hiding. This was pointed out by Blundo and Masucci in \cite{DBLP:journals/dcc/BlundoMSW02}
who alightly ammended the commitment scheme so that is provided perfect hiding.

The Rivest commitment scheme uses a trusted initialiser to provide correlated randomness to the two parties 
before an execution of the protocol. In our framework we set these as keys that held by the respective parties.\<close>

theory Rivest imports
  Commitment_Schemes
  "HOL-Number_Theory.Cong"
  CryptHOL.CryptHOL
  Cyclic_Group_Ext
  Discrete_Log
  Number_Theory_Aux
  Uniform_Sampling
begin

locale rivest = 
  fixes q :: nat
  assumes prime_q: "prime q"
begin

lemma q_gt_0 [simp]: "q > 0" 
  by (simp add: prime_q prime_gt_0_nat)

type_synonym ck = "nat \<times> nat"
type_synonym vk = "nat \<times> nat"
type_synonym plain = "nat"
type_synonym commit = "nat"
type_synonym opening = "nat \<times> nat"

definition key_gen :: "(ck \<times> vk) spmf"
  where 
    "key_gen = do {
    a :: nat \<leftarrow> sample_uniform q;
    b :: nat \<leftarrow> sample_uniform q;
    x1 :: nat \<leftarrow> sample_uniform q;
    let y1 = (a * x1 + b) mod q;
    return_spmf ((a,b), (x1,y1))}" 

definition commit :: "ck \<Rightarrow> plain \<Rightarrow> (commit \<times> opening) spmf"
  where 
    "commit ck m = do {
  let (a,b) = ck;
  return_spmf ((m + a) mod q, (a,b))}"

fun verify :: "vk \<Rightarrow> plain \<Rightarrow> commit \<Rightarrow> opening \<Rightarrow> bool"
  where 
    "verify (x1,y1) m c (a,b) = (((c = (m + a) mod q)) \<and> (y1 = (a * x1 + b) mod q))"

definition valid_msg :: "plain \<Rightarrow> bool"
  where "valid_msg msg \<equiv> msg \<in> {..< q}"

sublocale rivest_commit: abstract_commitment key_gen commit verify valid_msg .

lemma abstract_correct: "rivest_commit.correct"
  unfolding abstract_commitment.correct_def abstract_commitment.correct_game_def
  by(simp add: key_gen_def commit_def bind_spmf_const lossless_weight_spmfD)

lemma rivest_hiding: "(spmf (rivest_commit.hiding_game_ind_cpa \<A>) True - 1/2 = 0)"
  including monad_normalisation
proof-
  note [simp] = Let_def split_def 
  obtain \<A>1 \<A>2 where [simp]: "\<A> = (\<A>1, \<A>2)" by(cases \<A>)
  have "rivest_commit.hiding_game_ind_cpa (\<A>1, \<A>2) = TRY do {
    a :: nat \<leftarrow> sample_uniform q;
    x1 :: nat \<leftarrow> sample_uniform q;
    y1 \<leftarrow> map_spmf (\<lambda> b. (a * x1 + b) mod q) (sample_uniform q);
    ((m0, m1), \<sigma>) \<leftarrow> \<A>1 (x1,y1);
    _ :: unit \<leftarrow> assert_spmf (valid_msg m0 \<and> valid_msg m1);
    d \<leftarrow> coin_spmf;  
    let c = ((if d then m0 else m1) + a) mod q;
    b' \<leftarrow> \<A>2 c \<sigma>;
    return_spmf (b' = d)} ELSE coin_spmf"
    unfolding abstract_commitment.hiding_game_ind_cpa_def
    by(simp add: commit_def key_gen_def o_def bind_map_spmf)
  also have "... = TRY do {
    a :: nat \<leftarrow> sample_uniform q;
    x1 :: nat \<leftarrow> sample_uniform q;
    y1 \<leftarrow> sample_uniform q;
    ((m0, m1), \<sigma>) \<leftarrow> \<A>1 (x1,y1);
    _ :: unit \<leftarrow> assert_spmf (valid_msg m0 \<and> valid_msg m1);
    d \<leftarrow> coin_spmf;  
    let c = ((if d then m0 else m1) + a) mod q;
    b' \<leftarrow> \<A>2 c \<sigma>;
    return_spmf (b' = d)} ELSE coin_spmf"
    by(simp add: samp_uni_plus_one_time_pad)
  also have "... = TRY do {
    x1 :: nat \<leftarrow> sample_uniform q;
    y1 \<leftarrow> sample_uniform q;
    ((m0, m1), \<sigma>) \<leftarrow> \<A>1 (x1,y1);
    _ :: unit \<leftarrow> assert_spmf (valid_msg m0 \<and> valid_msg m1);
    d \<leftarrow> coin_spmf;  
    c \<leftarrow> map_spmf (\<lambda> a. ((if d then m0 else m1) + a) mod q) (sample_uniform q);
    b' \<leftarrow> \<A>2 c \<sigma>;
    return_spmf (b' = d)} ELSE coin_spmf" 
    by(simp add: o_def bind_map_spmf)
  also have "... = TRY do {
    x1 :: nat \<leftarrow> sample_uniform q;
    y1 \<leftarrow> sample_uniform q;
    ((m0, m1), \<sigma>) \<leftarrow> \<A>1 (x1,y1);
    _ :: unit \<leftarrow> assert_spmf (valid_msg m0 \<and> valid_msg m1);
    d \<leftarrow> coin_spmf;  
    c \<leftarrow> sample_uniform q;
    b' :: bool \<leftarrow> \<A>2 c \<sigma>;
    return_spmf (b' = d)} ELSE coin_spmf"
    by(simp add: samp_uni_plus_one_time_pad)
  also have "... = TRY do {
    x1 :: nat \<leftarrow> sample_uniform q;
    y1 \<leftarrow> sample_uniform q;
    ((m0, m1), \<sigma>) \<leftarrow> \<A>1 (x1,y1);
    _ :: unit \<leftarrow> assert_spmf (valid_msg m0 \<and> valid_msg m1);
    c :: nat \<leftarrow> sample_uniform q;
    guess :: bool \<leftarrow> \<A>2 c \<sigma>;
    map_spmf((=) guess) coin_spmf} ELSE coin_spmf"
    by(simp add: map_spmf_conv_bind_spmf)
  also have "... = coin_spmf" 
    by(simp add: map_eq_const_coin_spmf bind_spmf_const try_bind_spmf_lossless2' 
        scale_bind_spmf weight_spmf_le_1 scale_scale_spmf)
  ultimately show ?thesis 
    by(simp add: spmf_of_set)
qed

lemma rivest_perfect_hiding: "rivest_commit.perfect_hiding_ind_cpa \<A>"
  unfolding abstract_commitment.perfect_hiding_ind_cpa_def abstract_commitment.hiding_advantage_ind_cpa_def
  by(simp add: rivest_hiding)

lemma samp_uni_break':
  assumes fst_cond: "m \<noteq> m' \<and> valid_msg m \<and> valid_msg m'"
    and c: "c = (m + a) mod q \<and> y1 = (a * x1 + b) mod q" 
    and  c': "c = (m' + a') mod q \<and> y1 = (a' * x1 + b') mod q"
    and x1: "x1 < q" 
  shows "x1 = (if (a mod q > a' mod q) then nat ((int b'- int b) * (inverse (nat ((int a mod q - int a' mod q) mod q)) q) mod q)  else 
          nat ((int b- int b') * (inverse (nat ((int a' mod q - int a mod q) mod q)) q) mod q))"
proof-
  have m: "m < q \<and> m' < q" using fst_cond valid_msg_def by simp
  have a_a': "\<not> [a = a'] (mod q)"
  proof-
    have "[m + a = m' + a'] (mod q)" 
      using assms cong_def by blast
    thus ?thesis 
      by (metis m fst_cond c c' add.commute cong_less_modulus_unique_nat cong_add_rcancel_nat cong_mod_right)
  qed
  have cong_y1: "[int a * int x1 + int b = int a' * int x1 + int b'] (mod q)" 
    by (metis c c' cong_def Num.of_nat_simps(4) Num.of_nat_simps(5) cong_int_iff)
  show ?thesis 
  proof(cases "a mod q > a' mod q")
    case True
    hence gcd: "gcd (nat ((int a mod q - int a' mod q) mod q)) q = 1"
    proof-
      have "((int a mod q - int a' mod q) mod q) \<noteq> 0" 
        by (metis True comm_monoid_add_class.add_0 diff_add_cancel mod_add_left_eq mod_diff_eq nat_mod_as_int order_less_irrefl)
      moreover have "((int a mod q - int a' mod q) mod q) < q" by simp   
      ultimately show ?thesis
        using prime_field[of q "nat ((int a mod int q - int a' mod int q) mod int q)"] prime_q 
        by (smt Euclidean_Division.pos_mod_sign coprime_imp_gcd_eq_1 int_nat_eq nat_less_iff of_nat_0_less_iff q_gt_0)
    qed
    hence "[int a * int x1 - int a' * int x1 = int b'- int b] (mod q)"  
      by (smt cong_diff_iff_cong_0 cong_y1 cong_diff cong_diff)
    hence "[int a mod q * int x1 - int a' mod q * int x1 = int b'- int b] (mod q)"  
    proof -
      have "[int x1 * (int a mod int q - int a' mod int q) = int x1 * (int a - int a')] (mod int q)"
        by (meson cong_def cong_mult cong_refl mod_diff_eq)
      then show ?thesis
        by (metis (no_types, hide_lams) Groups.mult_ac(2) \<open>[int a * int x1 - int a' * int x1 = int b' - int b] (mod int q)\<close> cong_def mod_diff_left_eq mod_diff_right_eq mod_mult_right_eq)
    qed
    hence "[int x1 * (int a mod q - int a' mod q) = int b'- int b] (mod q)" 
      by(metis int_distrib(3) mult.commute)
    hence "[int x1 * (int a mod q - int a' mod q) mod q = int b'- int b] (mod q)"
      using cong_def by simp
    hence "[int x1 * nat ((int a mod q - int a' mod q) mod q) = int b'- int b] (mod q)"
      by (simp add: True cong_def mod_mult_right_eq)
    hence "[int x1 * nat ((int a mod q - int a' mod q) mod q) * inverse (nat ((int a mod q - int a' mod q) mod q)) q 
              = (int b'- int b) * inverse (nat ((int a mod q - int a' mod q) mod q)) q] (mod q)"
      using cong_scalar_right by blast
    hence "[int x1 * (nat ((int a mod q - int a' mod q) mod q) * inverse (nat ((int a mod q - int a' mod q) mod q)) q) 
              = (int b'- int b) * inverse (nat ((int a mod q - int a' mod q) mod q)) q] (mod q)"
      by (simp add: more_arith_simps(11))
    hence "[int x1 * 1 = (int b'- int b) * inverse (nat ((int a mod q - int a' mod q) mod q)) q] (mod q)"
      using inverse gcd 
      by (meson cong_scalar_left cong_sym_eq cong_trans)
    hence "[int x1 = (int b'- int b) * inverse (nat ((int a mod q - int a' mod q) mod q)) q] (mod q)"
      by simp
    hence "int x1 mod q = ((int b'- int b) * inverse (nat ((int a mod q - int a' mod q) mod q)) q) mod q"
      using cong_def by fast
    thus ?thesis using x1 True by simp
  next
    case False
    hence aa': "a mod q < a' mod q" 
      using a_a' cong_refl nat_neq_iff 
      by (simp add: cong_def)
    hence gcd: "gcd (nat ((int a' mod q - int a mod q) mod q)) q = 1"
    proof-
      have "((int a' mod q - int a mod q) mod q) \<noteq> 0" 
        by (metis aa' comm_monoid_add_class.add_0 diff_add_cancel mod_add_left_eq mod_diff_eq nat_mod_as_int order_less_irrefl)
      moreover have "((int a' mod q - int a mod q) mod q) < q" by simp   
      ultimately show ?thesis
        using prime_field[of q "nat ((int a' mod int q - int a mod int q) mod int q)"] prime_q
        by (smt Euclidean_Division.pos_mod_sign coprime_imp_gcd_eq_1 int_nat_eq nat_less_iff of_nat_0_less_iff q_gt_0) 
    qed
    have "[int b - int b' = int a' * int x1 - int a * int x1] (mod q)"
      by (smt cong_diff_iff_cong_0 cong_y1 cong_diff cong_diff)
    hence "[int b - int b' = int x1 * (int a' - int a)] (mod q)"
      using int_distrib mult.commute by metis
    hence "[int b - int b' = int x1 * (int a' mod q - int a mod q)] (mod q)"
      by (metis (no_types, lifting) cong_def mod_diff_eq mod_mult_right_eq)
    hence "[int b - int b' = int x1 * (int a' mod q - int a mod q) mod q] (mod q)"
      using cong_def by simp
    hence "[(int b - int b') * inverse (nat ((int a' mod q - int a mod q) mod q)) q 
               = int x1 * (int a' mod q - int a mod q) mod q *  inverse (nat ((int a' mod q - int a mod q) mod q)) q ] (mod q)"
      using cong_scalar_right by blast
    hence "[(int b - int b') * inverse (nat ((int a' mod q - int a mod q) mod q)) q 
               = int x1 * ((int a' mod q - int a mod q) mod q *  inverse (nat ((int a' mod q - int a mod q) mod q)) q)] (mod q)"
      by (metis (mono_tags, lifting) cong_def mod_mult_left_eq mod_mult_right_eq more_arith_simps(11))
    hence *: "[int x1 * ((int a' mod q - int a mod q) mod q * inverse (nat ((int a' mod q - int a mod q) mod q)) q) 
              = (int b - int b') * inverse (nat ((int a' mod q - int a mod q) mod q)) q] (mod q)"
      using cong_sym_eq by auto
    hence "[int x1 * 1 = (int b - int b') * inverse (nat ((int a' mod q - int a mod q) mod q)) q] (mod q)"
    proof -
      have "[(int a' mod int q - int a mod int q) mod int q * Number_Theory_Aux.inverse (nat ((int a' mod int q - int a mod int q) mod int q)) q = 1] (mod int q)"
        by (metis (no_types) Euclidean_Division.pos_mod_sign inverse gcd int_nat_eq of_nat_0_less_iff q_gt_0)
      then show ?thesis
        by (meson * cong_scalar_left cong_sym_eq cong_trans)
    qed
    hence "[int x1 = (int b - int b') * inverse (nat ((int a' mod q - int a mod q) mod q)) q] (mod q)"
      by simp
    hence "int x1 mod q = (int b - int b') * (inverse (nat ((int a' mod q - int a mod q) mod q)) q) mod q"
      using cong_def by auto
    thus ?thesis using x1 aa' by simp
  qed
qed


lemma samp_uni_spmf_mod_q:
  shows "spmf (sample_uniform q) (x mod q) = 1/q"
proof-
  have "indicator {..< q} (x mod q) = 1" 
    using q_gt_0 by auto
  moreover have "real (card {..< q}) = q" by simp
  ultimately show ?thesis 
    by(auto simp add: spmf_of_set sample_uniform_def)
qed

lemma spmf_samp_uni_eq_return_bool_mod:
  shows "spmf (do { 
          x1 \<leftarrow> sample_uniform q;
          return_spmf (int x1 = y mod q)}) True = 1/q" 
proof-
  have "spmf (do { 
          x1 \<leftarrow> sample_uniform q;
          return_spmf (x1 = y mod q)}) True = spmf (sample_uniform q \<bind> (\<lambda> x1. return_spmf x1)) (y mod q)"
    apply(simp only: spmf_bind)
    apply(rule Bochner_Integration.integral_cong[OF refl])+
  proof -
    fix x :: nat
    have "y mod q = x \<longrightarrow> indicator {True} (x = (y mod q)) = (indicator {(y mod q)} x::real)"
      by simp
    then have "indicator {True} (x = y mod q) = (indicator {y mod q} x::real)"
      by fastforce
    then show "spmf (return_spmf (x = y mod q)) True = spmf (return_spmf x) (y mod q)"
      by (metis pmf_return spmf_of_pmf_return_pmf spmf_spmf_of_pmf)
  qed 
  thus ?thesis using samp_uni_spmf_mod_q by simp
qed

lemma bind_game_le_inv_q:
  shows "spmf (rivest_commit.bind_game \<A>) True \<le> 1 / q"
proof -
  let ?eq = "\<lambda>a a' b b'. (=)
   (if (a mod q > a' mod q) then nat ((int b'- int b) * (inverse (nat ((int a mod q - int a' mod q) mod q)) q) mod q)
    else nat ((int b - int b') * (inverse (nat ((int a' mod q - int a mod q) mod q)) q) mod q))"
  have "spmf (rivest_commit.bind_game \<A>) True = spmf (do {
    (ck,(x1,y1)) \<leftarrow> key_gen;
    (c, m, (a,b), m', (a',b')) \<leftarrow> \<A> ck;
    _ :: unit \<leftarrow> assert_spmf(m \<noteq> m' \<and> valid_msg m \<and> valid_msg m');  
    let b = verify (x1,y1) m c (a,b);
    let b' = verify (x1,y1) m' c (a',b');
    _ :: unit \<leftarrow> assert_spmf (b \<and> b');
    return_spmf True}) True" 
    by(simp add: abstract_commitment.bind_game_alt_def split_def spmf_try_spmf del: verify.simps) 
  also have "... = spmf (do {
    a' :: nat \<leftarrow> sample_uniform q;
    b' :: nat \<leftarrow> sample_uniform q;
    x1 :: nat \<leftarrow> sample_uniform q;
    let y1 = (a' * x1 + b') mod q;
    (c, m, (a,b), m', (a',b')) \<leftarrow> \<A> (a',b');
    _ :: unit \<leftarrow> assert_spmf (m \<noteq> m' \<and> valid_msg m \<and> valid_msg m');  
    _ :: unit \<leftarrow> assert_spmf (c = (m + a) mod q \<and> y1 = (a * x1 + b) mod q \<and> c = (m' + a') mod q \<and> y1 = (a' * x1 + b') mod q);
    return_spmf True}) True" 
    by(simp add: key_gen_def Let_def)
  also have "... = spmf (do {
    a'' :: nat \<leftarrow> sample_uniform q;
    b'' :: nat \<leftarrow> sample_uniform q;
    x1 :: nat \<leftarrow> sample_uniform q;
    let y1 = (a'' * x1 + b'') mod q;
    (c, m, (a,b), m', (a',b')) \<leftarrow> \<A> (a'',b'');
    _ :: unit \<leftarrow> assert_spmf (m \<noteq> m' \<and> valid_msg m \<and> valid_msg m');  
    _ :: unit \<leftarrow> assert_spmf (c = (m + a) mod q \<and> y1 = (a * x1 + b) mod q \<and> c = (m' + a') mod q \<and> y1 = (a' * x1 + b') mod q);
    return_spmf (?eq a a' b b' x1)}) True" 
    unfolding split_def Let_def
    by(rule arg_cong2[where f=spmf, OF _ refl] bind_spmf_cong[OF refl])+
      (auto simp add: eq_commute samp_uni_break' Let_def split_def valid_msg_def cong: bind_spmf_cong_simp)
  also have "... \<le> spmf (do {
    a'' :: nat \<leftarrow> sample_uniform q;
    b'' :: nat \<leftarrow> sample_uniform q;
    (c, m, (a,(b::nat)), m', (a',b')) \<leftarrow> \<A> (a'',b'');
    map_spmf (?eq a a' b b') (sample_uniform q)}) True"
    including monad_normalisation
    unfolding split_def Let_def assert_spmf_def
    apply(simp add: map_spmf_conv_bind_spmf)
    apply(rule ord_spmf_eq_leD ord_spmf_bind_reflI)+
    apply auto
    done
  also have "... \<le> 1/q" 
  proof((rule spmf_bind_leI)+, clarify)
    fix a a' b b'
    define A where "A = Collect (?eq a a' b b')"
    define x1 where "x1 = The (?eq a a' b b')"
    note q_gt_0[simp del]
    have "A \<subseteq> {x1}" by(auto simp add: A_def x1_def)
    hence "card (A \<inter> {..<q}) \<le> card {x1}" by(intro card_mono) auto
    also have "\<dots> = 1" by simp
    finally have "spmf (map_spmf (\<lambda>x. x \<in> A) (sample_uniform q)) True \<le> 1 / q"
      using q_gt_0 unfolding sample_uniform_def
      by(subst map_mem_spmf_of_set)(auto simp add: field_simps)
    then show "spmf (map_spmf (?eq a a' b b') (sample_uniform q)) True \<le> 1 / q"
      unfolding A_def mem_Collect_eq .
  qed auto
  finally show ?thesis .
qed

lemma rivest_bind:
  shows "rivest_commit.bind_advantage \<A> \<le> 1 / q"
  using bind_game_le_inv_q rivest_commit.bind_advantage_def by simp

end

locale rivest_asymp = 
  fixes q :: "nat \<Rightarrow> nat"
  assumes rivest: "\<And>\<eta>. rivest (q \<eta>)"
begin

sublocale rivest "q \<eta>" for \<eta> by(simp add: rivest)

theorem rivest_correct: 
  shows "rivest_commit.correct n"
  using abstract_correct by simp

theorem rivest_perfect_hiding_asym:
  assumes lossless_\<A>: "rivest_commit.lossless (\<A> n)" 
  shows "rivest_commit.perfect_hiding_ind_cpa n (\<A> n)"
  by (simp add: lossless_\<A> rivest_perfect_hiding)

theorem rivest_binding_asym:
  assumes "negligible (\<lambda>n. 1 / (q n))"
  shows "negligible (\<lambda>n. rivest_commit.bind_advantage n (\<A> n))"
  using negligible_le rivest_bind assms rivest_commit.bind_advantage_def by auto

end

end
