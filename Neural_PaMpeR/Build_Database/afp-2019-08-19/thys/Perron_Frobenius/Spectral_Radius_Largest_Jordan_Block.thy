(* Author: Thiemann *)

section \<open>The Jordan Blocks of the Spectral Radius are Largest\<close>

text \<open>Consider a non-negative real matrix, and consider any Jordan-block
  of any eigenvalues whose norm is the spectral radius. We prove that there is
  a Jordan block of the spectral radius which has the same size or is larger.\<close>

theory Spectral_Radius_Largest_Jordan_Block
imports 
  Jordan_Normal_Form.Jordan_Normal_Form_Uniqueness
  Perron_Frobenius_General
begin

lemma sum_root_unity: fixes x :: "'a :: {comm_ring,division_ring}" 
  assumes "x^n = 1" 
  shows "sum (\<lambda> i. x^i) {..< n} = (if x = 1 then of_nat n else 0)" 
proof (cases "x = 1 \<or> n = 0")
  case x: False
  from x obtain m where n: "n = Suc m" by (cases n, auto)
  have id: "{..< n} = {0..m}" unfolding n by auto
  show ?thesis using assms x n unfolding id sum_gp by (auto simp: divide_inverse)
qed auto

lemma sum_root_unity_power_pos_implies_1:  
  assumes sumpos: "\<And> k. Re (sum (\<lambda> i. b i * x i ^ k) I) > 0" 
  and root_unity: "\<And> i. i \<in> I \<Longrightarrow> \<exists> d. d \<noteq> 0 \<and> x i ^ d = 1" 
shows "1 \<in> x ` I" 
proof (rule ccontr)
  assume "\<not> ?thesis" 
  hence x: "i \<in> I \<Longrightarrow> x i \<noteq> 1" for i by auto
  from sumpos[of 0] have I: "finite I" "I \<noteq> {}" 
    using sum.infinite by fastforce+
  have "\<forall> i. \<exists> d. i \<in> I \<longrightarrow> d \<noteq> 0 \<and> x i ^ d = 1" using root_unity by auto
  from choice[OF this] obtain d where d: "\<And> i. i \<in> I \<Longrightarrow> d i \<noteq> 0 \<and> x i ^ (d i) = 1" by auto
  define D where "D = prod d I" 
  have D0: "0 < D" unfolding D_def
    by (rule prod_pos, insert d, auto)
  have "0 < sum (\<lambda> k. Re (sum (\<lambda> i. b i * x i ^ k) I)) {..< D}" 
    by (rule sum_pos[OF _ _ sumpos], insert D0, auto)
  also have "\<dots> = Re (sum (\<lambda> k. sum (\<lambda> i. b i * x i ^ k) I) {..< D})" by auto
  also have "sum (\<lambda> k. sum (\<lambda> i. b i * x i ^ k) I) {..< D}
    = sum (\<lambda> i. sum (\<lambda> k. b i * x i ^ k) {..< D}) I" by (rule sum.swap)
  also have "\<dots> = sum (\<lambda> i. b i * sum (\<lambda> k. x i ^ k) {..< D}) I"
    by (rule sum.cong, auto simp: sum_distrib_left)
  also have "\<dots> = 0" 
  proof (rule sum.neutral, intro ballI)
    fix i
    assume i: "i \<in> I" 
    from d[OF this] x[OF this] have d: "d i \<noteq> 0" and rt_unity: "x i ^ d i = 1" 
      and x: "x i \<noteq> 1" by auto
    have "\<exists> C. D = d i * C" unfolding D_def
      by (subst prod.remove[of _ i], insert i I, auto)
    then obtain C where D: "D = d i * C" by auto
    have image: "(\<And> x. f x = x) \<Longrightarrow> {..< D} = f ` {..< D}" for f by auto
    let ?g = "(\<lambda> (a,c). a + d i * c)" 
    have "{..< D} = ?g ` (\<lambda> j. (j mod d i, j div d i)) ` {..< d i * C}" 
      unfolding image_image split D[symmetric] by (rule image, insert d mod_mult_div_eq, blast)
    also have "(\<lambda> j. (j mod d i, j div d i)) ` {..< d i * C} = {..< d i} \<times> {..< C}" (is "?f ` ?A = ?B")
    proof -
      {
        fix x
        assume "x \<in> ?B" then obtain a c where x: "x = (a,c)" and a: "a < d i" and c: "c < C" by auto 
        hence "a + c * d i < d i * (1 + c)" by simp
        also have "\<dots> \<le> d i * C" by (rule mult_le_mono2, insert c, auto)
        finally have "a + c * d i \<in> ?A" by auto
        hence "?f (a + c * d i) \<in> ?f ` ?A" by blast
        also have "?f (a + c * d i) = x" unfolding x using a by auto
        finally have "x \<in> ?f ` ?A" .
      }
      thus ?thesis using d by (auto simp: div_lt_nat)
    qed
    finally have D: "{..< D} = (\<lambda> (a,c). a + d i * c) ` ?B" by auto
    have inj: "inj_on ?g ?B"
    proof -
      {
        fix a1 a2 c1 c2
        assume id: "?g (a1,c1) = ?g (a2,c2)" and *: "(a1,c1) \<in> ?B" "(a2,c2) \<in> ?B" 
        from arg_cong[OF id, of "\<lambda> x. x div d i"] * have c: "c1 = c2" by auto
        from arg_cong[OF id, of "\<lambda> x. x mod d i"] * have a: "a1 = a2" by auto
        note a c
      }
      thus ?thesis by (smt SigmaE inj_onI)
    qed
    have "sum (\<lambda> k. x i ^ k) {..< D} = sum (\<lambda> (a,c). x i ^ (a + d i * c)) ?B" 
      unfolding D by (subst sum.reindex, rule inj, auto intro!: sum.cong) 
    also have "\<dots> = sum (\<lambda> (a,c). x i ^ a) ?B" 
      by (rule sum.cong, auto simp: power_add power_mult rt_unity)
    also have "\<dots> = 0" unfolding sum.cartesian_product[symmetric]  sum.swap[of _ "{..<C}"]
      by (rule sum.neutral, intro ballI, subst sum_root_unity[OF rt_unity], insert x, auto)
    finally 
    show "b i * sum (\<lambda> k. x i ^ k) {..< D} = 0" by simp
  qed
  finally show False by simp
qed

fun j_to_jb_index :: "(nat \<times> 'a)list \<Rightarrow> nat \<Rightarrow> nat \<times> nat" where
  "j_to_jb_index ((n,a) # n_as) i = (if i < n then (0,i) else 
     let rec = j_to_jb_index n_as (i - n) in (Suc (fst rec), snd rec))" 

fun jb_to_j_index :: "(nat \<times> 'a)list \<Rightarrow> nat \<times> nat \<Rightarrow> nat" where
  "jb_to_j_index n_as (0,j) = j" 
| "jb_to_j_index ((n,_) # n_as) (Suc i, j) = n + jb_to_j_index n_as (i,j)" 

lemma j_to_jb_index: assumes "i < sum_list (map fst n_as)" 
  and "j < sum_list (map fst n_as)" 
  and "j_to_jb_index n_as i = (bi, li)" 
  and "j_to_jb_index n_as j = (bj, lj)" 
  and "n_as ! bj = (n, a)" 
shows "((jordan_matrix n_as) ^\<^sub>m r) $$ (i,j) = (if bi = bj then ((jordan_block n a) ^\<^sub>m r) $$ (li, lj) else 0)
  \<and> (bi = bj \<longrightarrow> li < n \<and> lj < n \<and> bj < length n_as \<and> (n,a) \<in> set n_as)"
  unfolding jordan_matrix_pow using assms
proof (induct n_as arbitrary: i j bi bj)
  case (Cons mb n_as i j bi bj)
  obtain m b where mb: "mb = (m,b)" by force
  note Cons = Cons[unfolded mb]
  have [simp]: "dim_col (case x of (n, a) \<Rightarrow> 1\<^sub>m n) = fst x" for x by (cases x, auto)
  have [simp]: "dim_row (case x of (n, a) \<Rightarrow> 1\<^sub>m n) = fst x" for x by (cases x, auto)
  have [simp]: "dim_col (case x of (n, a) \<Rightarrow> jordan_block n a ^\<^sub>m r) = fst x" for x by (cases x, auto)
  have [simp]: "dim_row (case x of (n, a) \<Rightarrow> jordan_block n a ^\<^sub>m r) = fst x" for x by (cases x, auto)
  consider (UL) "i < m" "j < m" | (UR) "i < m" "j \<ge> m" | (LL) "i \<ge> m" "j < m" 
    | (LR) "i \<ge> m" "j \<ge> m" by linarith
  thus ?case
  proof cases
    case UL
    with Cons(2-) show ?thesis unfolding mb by (auto simp: Let_def)
  next
    case UR
    with Cons(2-) show ?thesis unfolding mb by (auto simp: Let_def dim_diag_block_mat o_def)
  next
    case LL
    with Cons(2-) show ?thesis unfolding mb by (auto simp: Let_def dim_diag_block_mat o_def)
  next
    case LR
    let ?i = "i - m" 
    let ?j = "j - m" 
    from LR Cons(2-) have bi: "j_to_jb_index n_as ?i = (bi - 1, li)" "bi \<noteq> 0" by (auto simp: Let_def)
    from LR Cons(2-) have bj: "j_to_jb_index n_as ?j = (bj - 1, lj)" "bj \<noteq> 0" by (auto simp: Let_def)
    from LR Cons(2-) have i: "?i < sum_list (map fst n_as)" by auto
    from LR Cons(2-) have j: "?j < sum_list (map fst n_as)" by auto
    from LR Cons(2-) bj(2) have nas: "n_as ! (bj - 1) = (n, a)" by (cases bj, auto)
    from bi(2) bj(2) have id: "(bi - 1 = bj - 1) = (bi = bj)" by auto
    note IH = Cons(1)[OF i j bi(1) bj(1) nas, unfolded id]
    have id: "diag_block_mat (map (\<lambda>a. case a of (n, a) \<Rightarrow> jordan_block n a ^\<^sub>m r) (mb # n_as)) $$ (i, j)
      = diag_block_mat (map (\<lambda>a. case a of (n, a) \<Rightarrow> jordan_block n a ^\<^sub>m r) n_as) $$ (?i, ?j)" 
      using i j LR unfolding mb by (auto simp: Let_def dim_diag_block_mat o_def)
    show ?thesis using IH unfolding id by auto
  qed     
qed auto

lemma j_to_jb_index_rev: assumes j: "j_to_jb_index n_as i = (bi, li)" 
  and i: "i < sum_list (map fst n_as)" 
  and k: "k \<le> li" 
shows "li \<le> i \<and> j_to_jb_index n_as (i - k) = (bi, li - k) \<and> (
  j_to_jb_index n_as j = (bi,li - k) \<longrightarrow> j < sum_list (map fst n_as) \<longrightarrow> j = i - k)"
  using j i
proof (induct n_as arbitrary: i bi j)
  case (Cons mb n_as i bi j)
  obtain m b where mb: "mb = (m,b)" by force
  note Cons = Cons[unfolded mb]
  show ?case
  proof (cases "i < m")
    case True
    thus ?thesis unfolding mb using Cons(2-) by (auto simp: Let_def)
  next
    case i_large: False
    let ?i = "i - m" 
    have i: "?i < sum_list (map fst n_as)" using Cons(2-) i_large by auto
    from Cons(2-) i_large have j: "j_to_jb_index n_as ?i = (bi - 1, li)" 
      and bi: "bi \<noteq> 0" by (auto simp: Let_def)
    note IH = Cons(1)[OF j i]
    from IH have IH1: "j_to_jb_index n_as (i - m - k) = (bi - 1, li - k)" and
       li: "li \<le> i - m" by auto
    from li have aim1: "li \<le> i" by auto
    from li k i_large have "i - k \<ge> m" by auto
    hence aim2: "j_to_jb_index (mb # n_as) (i - k) = (bi, li - k)" 
      using IH1 bi by (auto simp: mb Let_def add.commute)
    {
      assume *: "j_to_jb_index (mb # n_as) j = (bi, li - k)"
        "j < sum_list (map fst (mb # n_as))" 
      from * bi have j: "j \<ge> m" unfolding mb by (auto simp: Let_def split: if_splits)
      let ?j = "j - m" 
      from j * have jj: "?j < sum_list (map fst n_as)" unfolding mb by auto
      from j * have **: "j_to_jb_index n_as (j - m) = (bi - 1, li - k)" using bi mb 
        by (cases "j_to_jb_index n_as (j - m)", auto simp: Let_def)
      from IH[of ?j] jj ** have "j - m = i - m - k" by auto
      with j i_large k have "j = i - k" using \<open>m \<le> i - k\<close> by linarith
    } note aim3 = this
    show ?thesis using aim1 aim2 aim3 by blast
  qed
qed auto  
  

locale spectral_radius_1_jnf_max = 
  fixes A :: "real mat" and n m :: nat and lam :: complex and n_as
  assumes A: "A \<in> carrier_mat n n" 
  and nonneg: "nonneg_mat A" 
  and jnf: "jordan_nf (map_mat complex_of_real A) n_as" 
  and mem: "(m, lam) \<in> set n_as" 
  and lam1: "cmod lam = 1"  
  and sr1: "\<And>x. poly (char_poly A) x = 0 \<Longrightarrow> x \<le> 1" 
  and max_block: "\<And> k la. (k,la) \<in> set n_as \<Longrightarrow> cmod la \<le> 1 \<and> (cmod la = 1 \<longrightarrow> k \<le> m)" 
begin

lemma n_as0: "0 \<notin> fst ` set n_as" 
  using jnf[unfolded jordan_nf_def] ..

lemma m0: "m \<noteq> 0" using mem n_as0 by force

abbreviation cA where "cA \<equiv> map_mat complex_of_real A" 
abbreviation J where "J \<equiv> jordan_matrix n_as" 

lemma sim_A_J: "similar_mat cA J" 
  using jnf[unfolded jordan_nf_def] ..

definition "c = (\<Prod>ia = 0..<m-1. (of_nat m :: real) - 1 - of_nat ia)" 
lemma c_gt_0: "c > 0" unfolding c_def by (rule prod_pos, auto)
lemma c0: "c \<noteq> 0" using c_gt_0 by auto
lemma c_int_def: "c = (\<Prod>ia = 0..<m-1. (of_nat m :: int) - 1 - of_nat ia)" 
  using c_def by auto
lemma c_int: "c \<in> \<int>" using c_int_def Ints_of_int by metis
lemma c_ge_1: "c \<ge> 1" using c_gt_0 unfolding c_int_def by presburger

definition PP where "PP = (SOME PP. similar_mat_wit cA J (fst PP) (snd PP))" 
definition P where "P = fst PP" 
definition iP where "iP = snd PP" 

lemma JNF: "P \<in> carrier_mat n n" "iP \<in> carrier_mat n n" "J \<in> carrier_mat n n"
  "P * iP = 1\<^sub>m n" "iP * P = 1\<^sub>m n" "cA = P * J * iP" 
proof (atomize (full), goal_cases)
  case 1
  have n: "n = dim_row cA" using A by auto
  from sim_A_J[unfolded similar_mat_def] obtain Q iQ
    where "similar_mat_wit cA J Q iQ" by auto
  hence "similar_mat_wit cA J (fst (Q,iQ)) (snd (Q,iQ))" by auto
  hence "similar_mat_wit cA J P iP" unfolding PP_def iP_def P_def
    by (rule someI)
  from similar_mat_witD[OF n this]
  show ?case by auto
qed

definition I :: "nat set" where
  "I = {i | i bi li nn la. i < n \<and> j_to_jb_index n_as i = (bi, li) 
    \<and> n_as ! bi = (nn,la) \<and> cmod la = 1 \<and> nn = m \<and> li = nn - 1}"

lemma sumlist_nf: "sum_list (map fst n_as) = n" 
proof -
  have "sum_list (map fst n_as) = dim_row (jordan_matrix n_as)" by simp
  also have "\<dots> = dim_row cA" using similar_matD[OF sim_A_J] by auto
  finally show ?thesis using A by auto
qed

lemma I_nonempty: "I \<noteq> {}" 
proof -
  from split_list[OF mem] obtain as bs where n_as: "n_as = as @ (m,lam) # bs" by auto
  let ?i = "sum_list (map fst as) + (m - 1)"
  have "j_to_jb_index n_as ?i = (length as, m - 1)" 
    unfolding n_as by (induct as, insert m0, auto simp: Let_def)
  with lam1 have "?i \<in> I" unfolding I_def unfolding sumlist_nf[symmetric] n_as using m0 by auto
  thus ?thesis by blast
qed

lemma I_n: "I \<subseteq> {..<n}" unfolding I_def by auto

lemma root_unity_cmod_1: assumes la: "la \<in> snd ` set n_as" and 1: "cmod la = 1" 
  shows "\<exists> d. d \<noteq> 0 \<and> la ^ d = 1" 
proof -
  from la obtain k where kla: "(k,la) \<in> set n_as" by force
  from n_as0 kla have k0: "k \<noteq> 0" by force
  from split_list[OF kla] obtain as bs where nas: "n_as = as @ (k,la) # bs" by auto
  have rt: "poly (char_poly cA) la = 0" using k0
    unfolding jordan_nf_char_poly[OF jnf] nas poly_prod_list prod_list_zero_iff by auto
  obtain ks f where decomp: "decompose_prod_root_unity (char_poly A) = (ks, f)" by force
  from sumlist_nf[unfolded nas] k0 have n0: "n \<noteq> 0" by auto
  note pf = perron_frobenius_for_complexity_jnf(1,7)[OF A n0 nonneg sr1 decomp, simplified]
  from pf(1) pf(2)[OF 1 rt] show "\<exists> d. d \<noteq> 0 \<and> la ^ d = 1" by metis 
qed

definition d where "d = (SOME d. \<forall> la. la \<in> snd ` set n_as \<longrightarrow> cmod la = 1 \<longrightarrow> 
  d la \<noteq> 0 \<and> la ^ (d la) = 1)" 

lemma d: assumes "(k,la) \<in> set n_as" "cmod la = 1" 
  shows "la ^ (d la) = 1 \<and> d la \<noteq> 0" 
proof -
  let ?P = "\<lambda> d. \<forall> la. la \<in> snd ` set n_as \<longrightarrow> cmod la = 1 \<longrightarrow> 
    d la \<noteq> 0 \<and> la ^ (d la) = 1" 
  from root_unity_cmod_1 have "\<forall> la. \<exists> d. la \<in> snd ` set n_as \<longrightarrow> cmod la = 1 \<longrightarrow> 
    d \<noteq> 0 \<and> la ^ d = 1" by blast
  from choice[OF this] have "\<exists> d. ?P d" .
  from someI_ex[OF this] have "?P d" unfolding d_def .
  from this[rule_format, of la, OF _ assms(2)] assms(1) show ?thesis by force
qed

definition D where "D = prod_list (map (\<lambda> na. if cmod (snd na) = 1 then d (snd na) else 1) n_as)" 

lemma D0: "D \<noteq> 0" unfolding D_def
  by (unfold prod_list_zero_iff, insert d, force)

definition K where "K off k = D * k + (m-1) + off"

lemma mono_K: "strict_mono (K off)" unfolding strict_mono_def K_def
  using D0 by auto

definition C where "C off k = (c / real (K off k) ^ (m - 1))" 

lemma limit_jordan_block: assumes kla: "(k, la) \<in> set n_as"
  and ij: "i < k" "j < k" 
shows "(\<lambda>N. (jordan_block k la ^\<^sub>m (K off N)) $$ (i, j) * C off N)
  \<longlonglongrightarrow> (if i = 0 \<and> j = k - 1 \<and> cmod la = 1 \<and> k = m then la^off else 0)" 
proof -
  let ?c = "of_nat :: nat \<Rightarrow> complex" 
  let ?r = "of_nat :: nat \<Rightarrow> real" 
  let ?cr = complex_of_real 
  from ij have k0: "k \<noteq> 0" by auto
  from jordan_nf_char_poly[OF jnf] have cA: "char_poly cA = (\<Prod>(n, a)\<leftarrow>n_as. [:- a, 1:] ^ n)" .
  from degree_monic_char_poly[OF A] have "degree (char_poly A) = n" by auto
  have deg: "degree (char_poly cA) = n" using A by (simp add: degree_monic_char_poly)
  from this[unfolded cA] have "n = degree (\<Prod>(n, a)\<leftarrow>n_as. [:- a, 1:] ^ n)" by auto
  also have "\<dots> =  sum_list (map degree (map (\<lambda>(n, a). [:- a, 1:] ^ n) n_as))"
    by (subst degree_prod_list_eq, auto)
  also have "\<dots> = sum_list (map fst n_as)" 
    by (rule arg_cong[of _ _ sum_list], auto simp: degree_linear_power)
  finally have sum: "sum_list (map fst n_as) = n" by auto
  with split_list[OF kla] k0 have n0: "n \<noteq> 0" by auto
  obtain ks f where decomp: "decompose_prod_root_unity (char_poly A) = (ks, f)" by force
  note pf = perron_frobenius_for_complexity_jnf[OF A n0 nonneg sr1 decomp]
  define ji where "ji = j - i" 
  let ?f = "\<lambda> N. (c / (?r N)^(m-1))" 
  let ?jb = "\<lambda> N. (jordan_block k la ^\<^sub>m N) $$ (i,j)" 
  let ?jbc = "\<lambda> N. (jordan_block k la ^\<^sub>m N) $$ (i,j) * ?f N" 
  define e where "e = (if i = 0 \<and> j = k - 1 \<and> cmod la = 1 \<and> k = m then la^off else 0)"  
  let ?e1 = "\<lambda> N :: nat. (\<Prod>ia = 0..<ji. (?c N - ?c ia) / ?c (ji - ia)) * la ^ (N - ji)" 
  let ?e2 = "\<lambda> N. (\<Prod>ia = 0..<ji. (?c N - ?c ia) / ?c (ji - ia)) * la ^ (N - ji) * (c / ((?c N^(m-1))))" 
  define e2 where "e2 = ?e2" 
  let ?e3 = "\<lambda> N. (((\<Prod>ia = 0..<ji. (?c N - ?c ia) / ?c (ji - ia))) * la ^ (N - ji)) * ?f N" 
  {
    assume ij': "i \<le> j" and la0: "la \<noteq> 0" 
    {
      fix N
      assume "N \<ge> k" 
      with ij ij' have ji: "j - i \<le> N" and id: "N + i - j = N - ji" unfolding ji_def by auto
      have "?jb N = (?c (N choose (j - i)) * la ^ (N + i - j))" 
        unfolding jordan_block_pow using ij ij' by auto
      also have "\<dots> = ?e1 N" unfolding ji_def
        unfolding binomial_altdef_of_nat[OF ji] id ji_def
      proof (rule arg_cong[of _ _ "\<lambda> x. x * _"], rule prod.cong[OF refl], goal_cases) 
      case (1 x)
        hence "x \<le> N" using \<open>N \<ge> k\<close> ij by auto
        thus ?case by (simp add: of_nat_diff)
      qed
      finally have id: "?jb N = ?e1 N" .
      have "?jbc N = e2 N" 
        unfolding id e2_def using c_gt_0 by (simp add: norm_mult norm_divide norm_power) 
    } note jbc = this
    have e23: "?e2 N = ?e3 N" for N using c_gt_0 by auto
    have "(e2 o K off) \<longlonglongrightarrow> e" 
    proof (cases "cmod la = 1 \<and> k = m \<and> i = 0 \<and> j = k - 1")
      case False
      then consider (0) "la = 0" | (small) "la \<noteq> 0" "cmod la < 1" | 
        (medium) "cmod la = 1" "k < m \<or> i \<noteq> 0 \<or> j \<noteq> k - 1" 
        using max_block[OF kla] by linarith
      hence main: "e2 \<longlonglongrightarrow> e" 
      proof cases
        case 0
        hence e0: "e = 0" unfolding e_def by auto
        show ?thesis unfolding e0 0 LIMSEQ_iff e2_def
        proof (intro exI[of _ "Suc ji"] impI allI, goal_cases)
          case (1 r n) thus ?case by (cases "n - ji", auto)
        qed
      next
        case small
        have e0: "e = 0 * (of_real (if m - 1 = 0 then c else 0))" using small unfolding e_def by auto
        show ?thesis unfolding e0 unfolding e23 e2_def
        proof (rule tendsto_mult[OF _ tendsto_of_real])
          show "(\<lambda>x. c / real x ^ (m - 1)) \<longlonglongrightarrow> (if m - 1 = 0 then c else 0)" (is "_ \<longlonglongrightarrow> ?f")
          proof (cases "m - 1", force)
            case (Suc k)
            hence f: "?f = 0" by auto
            have inve:"c / real x ^ Suc k = inverse (inverse c * real x ^ Suc k)"
              for x using divide_real_def by auto
            show ?thesis unfolding f unfolding Suc inve
            proof(rule LIMSEQ_inverse_zero,standard,standard,standard)
              fix r::real fix x::nat
              let ?v = "ceiling c * ceiling (abs r)"
              have inv_pos:"inverse c > 0" using c_gt_0 by simp
              have c_int':"real_of_int \<lceil>c\<rceil> = c" using Ints_cases[OF c_int] by fastforce
              assume "nat ?v + 1 \<le> x"
              hence vr:"?v < real x" and "real x \<ge> 1" by linarith+
              hence "real x ^ k \<ge> 1" "real x \<ge> 1" using one_le_power by blast+
              hence x:"inverse c * real x \<le> inverse c * real x * real x ^ k"
                using inv_pos by simp
              have "inverse c * c * \<bar>r\<bar> \<le> inverse c * real_of_int (\<lceil>c\<rceil> * \<lceil>\<bar>r\<bar>\<rceil>)"
                using inv_pos c_int'
                by (metis c0 le_of_int_ceiling left_inverse mult.assoc mult_cancel_right2 of_int_mult)
              with mult_strict_left_mono[OF vr inv_pos]
              have "inverse c * c * (abs r) < inverse c * real x" by argo
              hence "r < inverse c * real x" using c_gt_0 by simp
              thus "r < inverse c * real x ^ Suc k" using x by simp
            qed
          qed
          let ?laji = "inverse (la^ji)" 
          let ?f = "(\<lambda>x. (\<Prod>ia = 0..<ji. (?c x - ?c ia) / ?c (ji - ia)) * la ^ (x - ji))" 
          let ?g = "\<lambda>x. (\<Prod>ia = 0..<ji. (1 - ?c ia * inverse (?c x)) / ?c (ji - ia)) * (((?c x)^ji * la ^ x) * ?laji)" 
          have fg: "\<forall>\<^sub>F x in sequentially. ?f x = ?g x" 
            apply (rule eventually_sequentiallyI[of "Suc ji"])
            unfolding prod_pow[symmetric] prod.distrib[symmetric] mult.assoc[symmetric]
            unfolding prod_pow mult.assoc
            by (rule arg_cong2[of _ _ _ _ "(*)"], rule prod.cong, auto simp: ring_distribs, 
              insert small, subst power_diff, auto simp: divide_inverse)
          have 0: "0 = (\<Prod>ia = 0..<ji. (1 - of_nat ia * 0) / of_nat (ji - ia)) * (0 * ?laji)" by simp
          show "?f \<longlonglongrightarrow> 0" unfolding tendsto_cong[OF fg]
          proof (subst 0, rule tendsto_mult[OF tendsto_prod tendsto_mult[OF _ tendsto_const]], 
              intro tendsto_intros inverse_of_nat_tendsto_zero)
            show "(\<lambda>x. of_nat x ^ ji * la ^ x) \<longlonglongrightarrow> 0"        
              by (rule poly_times_exp_tendsto_zero, insert small, auto)
          qed auto
        qed
      next
        case medium
        with max_block[OF kla] have "k \<le> m" and 1: "\<And> x. cmod la ^ x = 1" by auto
        with ij medium have "ji < m - 1" unfolding ji_def by linarith
        then obtain d where m1: "m - 1 = Suc d + ji" using less_iff_Suc_add by auto
        have e0: "e = 0" using medium unfolding e_def by auto
        have 0: "0 = (\<Prod>ia = 0..<ji. (1 - ?c ia * 0) / ?c (ji - ia)) * (of_real c) * 0" by simp       
        let ?e = "\<lambda> ia N. if N = 0 then 0 else (1 - ?c ia / ?c N) / ?c (ji - ia)" 
        let ?f = "\<lambda> ia N. (1 - ?c ia * (1 / ?c N)) / ?c (ji - ia)"
        {
          fix N          
          have "e2 N = ((\<Prod>ia = 0..<ji. (?c N - ?c ia) / ?c (ji - ia)) / ?c N ^ ji) * la ^ (N - ji) * (of_real c / ?c N ^ Suc d)" 
            unfolding medium m1 power_add e2_def by simp
          also have "(\<Prod>ia = 0..<ji. (?c N - ?c ia) / ?c (ji - ia)) / ?c N ^ ji 
            = (\<Prod>ia = 0..<ji. ?e ia N)" unfolding prod_pow[symmetric] prod_dividef[symmetric]
            by (cases "?c N = 0", auto simp add: field_simps)
          finally have "e2 N = (\<Prod>ia = 0..<ji. ?e ia N) * of_real c * inverse (?c N ^ Suc d) * la ^ (N - ji)"  
            by (simp add: divide_inverse)
          also have "cmod \<dots> = cmod ((\<Prod>ia = 0..<ji. ?e ia N) * of_real c * (inverse (?c N ^ Suc d)))" 
            unfolding norm_mult norm_power 1 by simp
          finally have "cmod (e2 N) = cmod ((\<Prod>ia = 0..<ji. ?e ia N) * of_real c * (inverse (?c N ^ Suc d)))" by simp
        } note e2 = this
        show ?thesis unfolding e0
          apply (rule tendsto_norm_zero_cancel, unfold e2, rule tendsto_norm_zero)
          apply (subst (2) 0)
          apply (rule tendsto_mult[OF tendsto_mult[OF tendsto_prod tendsto_const] inverse_power_tendsto_zero], goal_cases)
        proof -
          case (1 i)
          let ?g = "\<lambda> x. (1 - ?c i * (1 / of_nat x)) / of_nat (ji - i)" 
          have eq: "\<forall>\<^sub>F x in sequentially. ?e i x = ?g x" 
            by (rule eventually_sequentiallyI[of 1], auto) 
          show "?e i \<longlonglongrightarrow> (1 - ?c i * 0) / ?c (ji - i)" 
            unfolding tendsto_cong[OF eq] using 1
            by (intro tendsto_intros lim_1_over_n, auto) 
        qed
      qed
      show "(e2 o K off) \<longlonglongrightarrow> e"
        by (rule LIMSEQ_subseq_LIMSEQ[OF main mono_K])
    next
      case True
      hence large: "cmod la = 1" "k = m" "i = 0" "j = k - 1" by auto
      hence e: "e = la^off" unfolding e_def by auto
      from large k0 have m0: "m \<ge> 1" by auto
      define m1 where "m1 = m - 1" 
      have id: "(real (m - 1) - real ia) = ?r m - 1 - ?r ia" for ia using m0 unfolding m1_def by auto
      let ?e4 = "\<lambda> x. (\<Prod>ia = 0..<m1. 1 - ?cr (?r ia / x))" 
      {
        fix x :: nat
        assume x: "x \<noteq> 0" 
        have "?e2 x = ((\<Prod>ia = 0..<m1. (?c x - ?c ia) / ?c (m1 - ia)) *
            (\<Prod>ia = 0..<m1. ?cr (real m1 - real ia))) /
            (\<Prod>i = 0..<m1. ?c x) * la ^ (x - (m-1))" (is "_ = ?A / ?B * ?C") 
          unfolding m1_def ji_def large c_def prod_pow[symmetric] id by simp
        also have "?A = (\<Prod>ia = 0..<m1. (?cr x - ?c ia))" (is "_ = ?A")
          unfolding prod.distrib[symmetric] by (rule prod.cong[OF refl], subst of_nat_diff, auto) 
        also have "?A / ?B = (\<Prod>ia = 0..<m1. 1 - ?cr (?r ia / x))" 
          unfolding prod_dividef[symmetric] by (rule prod.cong[OF refl], insert x, auto simp: field_simps)
        finally have "?e2 x = ?e4 x * ?C" .
      } note main = this
      from d[OF kla large(1)] have 1: "la ^ d la = 1" by auto
      from split_list[OF kla] obtain as bs where n_as: "n_as = as @ (k,la) # bs" by auto
      obtain C where D: "D = d la * C" unfolding D_def unfolding n_as using large by auto
      have "(\<lambda> x. ?e4 x * e) \<longlonglongrightarrow> (\<Prod>ia = 0..<m1. 1 - ?cr 0) * e" 
        by (intro tendsto_intros real_tendsto_divide_at_top, auto simp: filterlim_real_sequentially)
      also have "(\<Prod>ia = 0..<m1. 1 - ?cr 0) = 1" unfolding e by simp
      finally have "(\<lambda> x. ?e4 x * e)  \<longlonglongrightarrow> e" by auto
      from LIMSEQ_subseq_LIMSEQ[OF this mono_K] 
      have e4: "(\<lambda> k. (?e4 o K off) k * e) \<longlonglongrightarrow> e" (is "?A \<longlonglongrightarrow> e")
        by (auto simp: o_def)
      {
        fix k :: nat
        assume k: "k \<noteq> 0" 
        hence 0: "K off k \<noteq> 0" unfolding K_def using D0 by auto
        have "?e2 (K off k) = ?e4 (K off k) * la^(K off k - (m-1))" unfolding main[OF 0] ..
        also have "K off k - (m-1) = D * k + off" unfolding K_def by simp
        also have "la ^ \<dots> = e" unfolding e power_add D power_mult 1 by auto
        finally have "e2 (K off k) = (?e4 o K off) k * e" unfolding o_def e2_def .
      } note main = this
      have id: "(?A \<longlonglongrightarrow> e) = ((e2 o K off) \<longlonglongrightarrow> e)" 
        by (rule tendsto_cong, unfold eventually_at_top_linorder, 
            rule exI[of _ 1], insert main, auto)
      from e4[unfolded id] show ?thesis .
    qed
    also have "((e2 o K off) \<longlonglongrightarrow> e) = ((?jbc o K off)  \<longlonglongrightarrow> e)"
    proof (rule tendsto_cong, unfold eventually_at_top_linorder, rule exI[of _ k], 
        intro allI impI, goal_cases)
      case (1 n)
      from mono_K[of off] 1 have "K off n \<ge> k" using le_trans seq_suble by blast
      from jbc[OF this] show ?case by (simp add: o_def)
    qed
    finally have "(?jbc o K off) \<longlonglongrightarrow> e" .
  } note part1 = this  
  {
    assume "i > j \<or> la = 0" 
    hence e: "e = 0" and jbn: "N \<ge> k \<Longrightarrow> ?jbc N = 0" for N 
      unfolding jordan_block_pow e_def using ij by auto
    have "?jbc \<longlonglongrightarrow> e" unfolding e LIMSEQ_iff by (intro exI[of _ k] allI impI, subst jbn, auto)
    from LIMSEQ_subseq_LIMSEQ[OF this mono_K]
    have "(?jbc o K off) \<longlonglongrightarrow> e" .
  } note part2 = this
  from part1 part2 have "(?jbc o K off) \<longlonglongrightarrow> e" by linarith
  thus ?thesis unfolding e_def o_def C_def .
qed

definition Lam where "Lam i = snd (n_as ! fst (j_to_jb_index n_as i))" 

lemma cmod_Lam: "i \<in> I \<Longrightarrow> cmod (Lam i) = 1" 
  unfolding I_def Lam_def by auto  

lemma I_Lam: assumes i: "i \<in> I" 
  shows "(m, Lam i) \<in> set n_as" 
proof -
  from i[unfolded I_def]
  obtain bi li la where i: "i < n" and jb: "j_to_jb_index n_as i = (bi, li)" 
    and nth: "n_as ! bi = (m, la)" and "cmod la = 1 \<and> li = m - 1" by auto
  hence lam: "Lam i = la" unfolding Lam_def by auto  
  from j_to_jb_index[of _ n_as, unfolded sumlist_nf, OF i i jb jb nth] lam
  show ?thesis by auto
qed

lemma limit_jordan_matrix: assumes ij: "i < n" "j < n" 
shows "(\<lambda>N. (J ^\<^sub>m (K off N)) $$ (i, j) * C off N)
  \<longlonglongrightarrow> (if j \<in> I \<and> i = j - (m - 1) then (Lam j)^off else 0)" 
proof -
  obtain bi li where bi: "j_to_jb_index n_as i = (bi, li)" by force
  obtain bj lj where bj: "j_to_jb_index n_as j = (bj, lj)" by force
  define la where "la = snd (n_as ! fst (j_to_jb_index n_as j))" 
  obtain nn where nbj: "n_as ! bj = (nn,la)" unfolding la_def bj fst_conv by (metis prod.collapse)
  from j_to_jb_index[OF ij[folded sumlist_nf] bi bj nbj]
  have eq: "bi = bj \<Longrightarrow> li < nn \<and> lj < nn \<and> bj < length n_as \<and> (nn, la) \<in> set n_as" and 
    index: "(J ^\<^sub>m r) $$ (i, j) =
    (if bi = bj then (jordan_block nn la ^\<^sub>m r) $$ (li, lj) else 0)" for r
    by auto
  note index_rev = j_to_jb_index_rev[OF bj, unfolded sumlist_nf, OF ij(2) le_refl]
  show ?thesis
  proof (cases "bi = bj")
    case False
    hence id: "(bi = bj) = False" by auto
    {
      assume "j \<in> I" "i = j - (m - 1)" 
      from this[unfolded I_def] bj nbj have "i = j - lj" by auto
      from index_rev[folded this] bi False have False by auto
    }
    thus ?thesis unfolding index id if_False by auto
  next
    case True
    hence id: "(bi = bj) = True" by auto
    from eq[OF True] have eq: "li < nn" "lj < nn" "(nn,la) \<in> set n_as" "bj < length n_as" by auto
    have "(\<lambda>N. (J ^\<^sub>m (K off N)) $$ (i, j) * C off N)
      \<longlonglongrightarrow> (if li = 0 \<and> lj = nn - 1 \<and> cmod la = 1 \<and> nn = m then la^off else 0)" 
      unfolding index id if_True using limit_jordan_block[OF eq(3,1,2)] .
    also have "(li = 0 \<and> lj = nn - 1 \<and> cmod la = 1 \<and> nn = m) = (j \<in> I \<and> i = j - (m - 1))" (is "?l = ?r")
    proof
      assume ?r
      hence "j \<in> I" ..
      from this[unfolded I_def] bj nbj 
      have *: "nn = m" "cmod la = 1" "lj = nn - 1" by auto
      from \<open>?r\<close> * have "i = j - lj" by auto
      with * have "li = 0" using index_rev bi by auto
      with * show ?l by auto
    next
      assume ?l
      hence jI: "j \<in> I" using bj nbj ij by (auto simp: I_def)
      from \<open>?l\<close> have "li = 0" by auto
      with index_rev[of i] bi ij(1) \<open>?l\<close> True
      have "i = j - (m - 1)" by auto
      with jI show ?r by auto
    qed
    finally show ?thesis unfolding la_def Lam_def .
  qed
qed

declare sumlist_nf[simp]

lemma A_power_P: "cA ^\<^sub>m k * P = P * J ^\<^sub>m k" 
proof (induct k)
  case 0
  show ?case using A JNF by simp
next
  case (Suc k) 
  have "cA ^\<^sub>m Suc k * P = cA ^\<^sub>m k * cA * P" by simp
  also have "\<dots> = cA ^\<^sub>m k * (P * J * iP) * P" using JNF by simp
  also have "\<dots> = (cA ^\<^sub>m k * P) * (J * (iP * P))" 
    using A JNF(1-3) by (simp add: assoc_mult_mat[of _ n n _ n _ n])
  also have "J * (iP * P) = J" unfolding JNF using JNF by auto
  finally show ?case unfolding Suc 
    using A JNF(1-3) by (simp add: assoc_mult_mat[of _ n n _ n _ n])
qed

lemma C_nonneg: "C off k \<ge> 0" unfolding C_def using c_gt_0 by auto

lemma P_nonzero_entry: assumes j: "j < n"
  shows "\<exists> i < n. P $$ (i,j) \<noteq> 0" 
proof (rule ccontr)
  assume "\<not> ?thesis" 
  hence 0: "\<And> i. i < n \<Longrightarrow> P $$ (i,j) = 0" by auto
  have "1 = (iP * P) $$ (j,j)" using j unfolding JNF by auto
  also have "\<dots> = (\<Sum>i = 0..<n. iP $$ (j, i) * P $$ (i, j))" 
    using j JNF(1-2) by (auto simp: scalar_prod_def)
  also have "\<dots> = 0" by (rule sum.neutral, insert 0, auto)
  finally show False by auto
qed

definition i where "i = (SOME i. i \<in> I)" 

lemma i: "i \<in> I" unfolding i_def using I_nonempty some_in_eq by blast

lemma i_n: "i < n" using i unfolding I_def by auto 

definition "j = (SOME j. j < n \<and> P $$ (j, i - (m - 1)) \<noteq> 0)" 

lemma j: "j < n" "P $$ (j, i - (m - 1)) \<noteq> 0"
proof -
  from i_n have lt: "i - (m - 1) < n" by auto
  show "j < n" "P $$ (j, i - (m - 1)) \<noteq> 0"
    unfolding j_def using someI_ex[OF P_nonzero_entry[OF lt]] by auto
qed

definition "B = cmod (P $$ (j, i - (m - 1))) / 2"

lemma B: "0 < B" unfolding B_def using j by auto

definition "w = P *\<^sub>v unit_vec n i" 

lemma w: "w \<in> carrier_vec n" using JNF unfolding w_def by auto

definition "v = map_vec cmod w"

lemma v: "v \<in> carrier_vec n" unfolding v_def using w by auto

lemma main_step: "\<exists> a. \<forall> l. 0 < Re (\<Sum>i\<in>I. a i * Lam i ^ l)" 
proof -
  let ?c = "complex_of_real" 
  let ?cv = "map_vec ?c" 
  let ?cm = "map_mat ?c" 
  let ?v = "?cv v" 
  define u where "u = iP *\<^sub>v ?v" 
  define cc where 
    "cc = (\<lambda> i. ((\<Sum>k = 0..<n. (if k = i - (m - 1) then P $$ (j, k) else 0)) * u $v i))" 
  define a where "a = (\<lambda> i. P $$ (j, i - (m - 1)) * u $v i)" 
  have u: "u \<in> carrier_vec n" unfolding u_def using JNF(2) v by auto
  {
    fix off
    from i i_n have iI: "i \<in> I" and i: "i < n" by auto
    let ?exp = "\<lambda> k. sum (\<lambda> ii. P $$ (j, ii) * (J ^\<^sub>m k) $$ (ii,i)) {..<n}" 
    define M where "M = (\<lambda> k. cmod (?exp (K off k) * C off k))" 
    let ?i = "i - (m - 1)"
    define G where "G = (\<lambda> k. (A ^\<^sub>m K off k *\<^sub>v v) $v j * C off k)" 
    {
      fix kk
      define k where "k = K off kk" 
      define cAk where "cAk = cA ^\<^sub>m k" 
      have cAk: "cAk \<in> carrier_mat n n" unfolding cAk_def using A by auto
      have "((A ^\<^sub>m k) *\<^sub>v v) $ j = ((map_mat cmod cAk) *\<^sub>v map_vec cmod w) $ j" 
        unfolding v_def[symmetric] cAk_def
        by (rule arg_cong[of _ _ "\<lambda> x. (x *\<^sub>v v) $ j"],
          unfold of_real_hom.mat_hom_pow[OF A, symmetric],
        insert nonneg_mat_power[OF A nonneg, of k], insert i j, 
        auto simp: nonneg_mat_def elements_mat_def)
      also have "\<dots> \<ge> cmod ((cAk *\<^sub>v w) $ j)" 
        by (subst (1 2) index_mult_mat_vec, insert j cAk w, auto simp: scalar_prod_def
        intro!: sum_norm_le norm_mult_ineq) 
      also have "cAk *\<^sub>v w = (cAk * P) *\<^sub>v unit_vec n i" 
        unfolding w_def i_def using JNF cAk by simp
      also have "\<dots> = P *\<^sub>v (J ^\<^sub>m k *\<^sub>v unit_vec n i)" unfolding cAk_def A_power_P
        using JNF by (subst assoc_mult_mat_vec[of _ n n _ n], auto)
      also have "J ^\<^sub>m k *\<^sub>v unit_vec n i = col (J ^\<^sub>m k) i"
        by (rule eq_vecI, insert i, auto)
      also have "(P *\<^sub>v (col (J ^\<^sub>m k) i)) $ j = Matrix.row P j \<bullet> col (J ^\<^sub>m k) i" 
        by (subst index_mult_mat_vec, insert j JNF, auto)
      also have "\<dots> = sum (\<lambda> ii. P $$ (j, ii) * (J ^\<^sub>m k) $$ (ii,i)) {..<n}" 
        unfolding scalar_prod_def by (rule sum.cong, insert i j JNF(1), auto)    
      finally have "(A ^\<^sub>m k *\<^sub>v v) $v j \<ge> cmod (?exp k)" .
      from mult_right_mono[OF this C_nonneg]
      have "(A ^\<^sub>m k *\<^sub>v v) $v j * C off kk \<ge> cmod (?exp k * C off kk)" unfolding norm_mult
        using C_nonneg by auto      
    }
    hence ge: "(A ^\<^sub>m K off k *\<^sub>v v) $v j * C off k \<ge> M k" for k unfolding M_def by auto 
    from i have mem: "i - (m - 1) \<in> {..<n}" by auto
    have "(\<lambda> k. ?exp (K off k) * C off k) \<longlonglongrightarrow> 
      (\<Sum>ii<n. P $$ (j, ii) * (if i \<in> I \<and> ii = i - (m - 1) then Lam i ^ off else 0))"
      (is "_ \<longlonglongrightarrow> ?sum")
      unfolding sum_distrib_right mult.assoc 
      by (rule tendsto_sum, rule tendsto_mult, force, rule limit_jordan_matrix[OF _ i], auto)
    also have "?sum = P $$ (j, i - (m - 1)) * Lam i ^ off" 
      by (subst sum.remove[OF _ mem], force, subst sum.neutral, insert iI, auto)
    finally have tend1: "(\<lambda> k. ?exp (K off k) * C off k) \<longlonglongrightarrow> P $$ (j, i - (m - 1)) * Lam i ^ off" .
    have tend2: "M \<longlonglongrightarrow> cmod (P $$ (j, i - (m - 1)) * Lam i ^ off)" unfolding M_def
      by (rule tendsto_norm, rule tend1)
    {
      from j have 0: "P $$ (j, i - (m - 1)) \<noteq> 0" by auto
      define E where "E = cmod (P $$ (j, i - (m - 1)) * Lam i ^ off)" 
      from cmod_Lam[OF iI] 0 have E: "E / 2 > 0" unfolding E_def by auto
      from tend2[folded E_def] have tend2: "M \<longlonglongrightarrow> E" .
      from ge have ge: "G k \<ge> M k" for k unfolding G_def .
      from tend2[unfolded LIMSEQ_iff, rule_format, OF E]
      obtain k' where diff: "\<And> k. k \<ge> k' \<Longrightarrow> norm (M k - E) < E / 2" by auto
      {
        fix k
        assume "k \<ge> k'"
        from diff[OF this] have norm: "norm (M k - E) < E / 2" .
        have "M k \<ge> 0" unfolding M_def by auto
        with E norm have "M k \<ge> E / 2"
          by (smt real_norm_def field_sum_of_halves)
        with ge[of k] E have "G k \<ge> E / 2" by auto
        also have "E / 2 = B" unfolding E_def B_def j norm_mult norm_power 
          cmod_Lam[OF iI] by auto
        finally have "G k \<ge> B" .
      }
      hence "\<exists> k'. \<forall> k. k \<ge> k' \<longrightarrow> G k \<ge> B" by auto
    }    
    hence Bound: "\<exists>k'. \<forall>k\<ge>k'. B \<le> G k" by auto
    {
      fix kk
      define k where "k = K off kk" 
      have "((A ^\<^sub>m k) *\<^sub>v v) $ j * C off kk = Re (?c (((A ^\<^sub>m k) *\<^sub>v v) $ j * C off kk))" by simp
      also have "?c (((A ^\<^sub>m k) *\<^sub>v v) $ j * C off kk) = ?cv ((A ^\<^sub>m k) *\<^sub>v v) $ j * ?c (C off kk)" 
        using j A by simp
      also have "?cv ((A ^\<^sub>m k) *\<^sub>v v) = (?cm (A ^\<^sub>m k) *\<^sub>v ?v)" using A
        by (subst of_real_hom.mult_mat_vec_hom[OF _ v], auto)
      also have "\<dots> = (cA ^\<^sub>m k *\<^sub>v ?v)" 
        by (simp add: of_real_hom.mat_hom_pow[OF A])
      also have "\<dots> = (cA ^\<^sub>m k *\<^sub>v ((P * iP) *\<^sub>v ?v))" unfolding JNF using v by auto
      also have "\<dots> = (cA ^\<^sub>m k *\<^sub>v (P *\<^sub>v u))" unfolding u_def
        by (subst assoc_mult_mat_vec, insert JNF v, auto)
      also have "\<dots> = (P * J ^\<^sub>m k *\<^sub>v u)" unfolding A_power_P[symmetric]
        by (subst assoc_mult_mat_vec, insert u JNF(1) A, auto)
      also have "\<dots> = (P *\<^sub>v (J ^\<^sub>m k *\<^sub>v u))"
        by (rule assoc_mult_mat_vec, insert u JNF(1) A, auto)
      finally have "(A ^\<^sub>m k *\<^sub>v v) $v j * C off kk = Re ((P *\<^sub>v (J ^\<^sub>m k *\<^sub>v u)) $ j * C off kk)" by simp
      also have "\<dots> = Re (\<Sum>i = 0..<n.
           P $$ (j, i) * (\<Sum>ia = 0..< n. (J ^\<^sub>m k) $$ (i, ia) * u $v ia * C off kk))"
        by (subst index_mult_mat_vec, insert JNF(1) j u, auto simp: scalar_prod_def sum_distrib_right[symmetric]
           mult.assoc[symmetric])  
      finally have "(A ^\<^sub>m k *\<^sub>v v) $v j * C off kk =
        Re (\<Sum>i = 0..<n. P $$ (j, i) * (\<Sum>ia = 0..<n. (J ^\<^sub>m k) $$ (i, ia) * C off kk * u $v ia))" 
        unfolding k_def
        by (simp only: ac_simps)
    } note A_to_u = this
    define F where "F = (\<Sum>ia\<in>I. a ia * Lam ia ^ off)" 
    have "G \<longlonglongrightarrow> 
       Re (\<Sum>i = 0..<n. P $$ (j, i) *
           (\<Sum>ia = 0..<n. (if ia \<in> I \<and> i = ia - (m - 1) then (Lam ia)^off else 0) * u $v ia))" 
      unfolding A_to_u G_def
      by (rule tendsto_Re[OF tendsto_sum[OF tendsto_mult[OF _ 
        tendsto_sum[OF tendsto_mult[OF limit_jordan_matrix]]]]], auto)
    also have "(\<Sum>i = 0..<n. P $$ (j, i) *
           (\<Sum>ia = 0..<n. (if ia \<in> I \<and> i = ia - (m - 1) then (Lam ia)^off else 0) * u $v ia))
      = (\<Sum>i = 0..<n. (\<Sum>ia \<in> I. (if ia \<in> I \<and> i = ia - (m - 1) then P $$ (j, i) else 0) * ((Lam ia)^off * u $v ia)))" 
      by (rule sum.cong[OF refl], unfold sum_distrib_left, subst (2) sum.mono_neutral_left[of "{0..<n}"],
        insert I_n, auto intro!: sum.cong)
    also have "\<dots> = (\<Sum>ia \<in> I. (\<Sum>i = 0..<n. (if i = ia - (m - 1) then P $$ (j, i) else 0)) * ((Lam ia)^off * u $v ia))"
      unfolding sum.swap[of _ I] sum_distrib_right
      by (rule sum.cong[OF refl], auto)
    also have "\<dots> = (\<Sum>ia \<in> I. cc ia * (Lam ia)^off)" unfolding cc_def
      by (rule sum.cong[OF refl], simp)
    also have "\<dots> = F" unfolding cc_def a_def F_def
      by (rule sum.cong[OF refl], insert I_n, auto)
    finally have tend3: "G \<longlonglongrightarrow> Re F" .
    from this[unfolded LIMSEQ_iff, rule_format, of "B / 2"] B
    obtain kk where kk: "\<And> k. k \<ge> kk \<Longrightarrow> norm (G k - Re F) < B / 2" by auto
    from Bound obtain kk' where kk': "\<And> k. k \<ge> kk' \<Longrightarrow> B \<le> G k" by auto
    define k where "k = max kk kk'" 
    with kk kk' have 1: "norm (G k - Re F) < B / 2" "B \<le> G k" by auto
    with B have "Re F > 0" by (smt real_norm_def field_sum_of_halves)
  }
  thus ?thesis by blast
qed


lemma main_theorem: "(m, 1) \<in> set n_as"
proof -
  from main_step obtain a where pos: "\<And> l. 0 < Re (\<Sum>i\<in>I. a i * Lam i ^ l)" by auto 
  have "1 \<in> Lam ` I" 
  proof (rule sum_root_unity_power_pos_implies_1[of a Lam I, OF pos])
    fix i
    assume "i \<in> I" 
    from d[OF I_Lam[OF this] cmod_Lam[OF this]]
    show "\<exists>d. d \<noteq> 0 \<and> Lam i ^ d = 1" by auto
  qed
  then obtain i where i: "i \<in> I" and "Lam i = 1" by auto
  with I_Lam[OF i] show ?thesis by auto
qed
end

lemma nonneg_sr_1_largest_jb:
  assumes nonneg: "nonneg_mat A" 
  and jnf: "jordan_nf (map_mat complex_of_real A) n_as" 
  and mem: "(m, lam) \<in> set n_as" 
  and lam1: "cmod lam = 1"
  and sr1: "\<And>x. poly (char_poly A) x = 0 \<Longrightarrow> x \<le> 1" 
  shows "\<exists> M. M \<ge> m \<and> (M,1) \<in> set n_as" 
proof -
  note jnf' = jnf[unfolded jordan_nf_def]
  from jnf' similar_matD[OF jnf'[THEN conjunct2]] obtain n 
    where A: "A \<in> carrier_mat n n" and n_as0: "0 \<notin> fst ` set n_as" by auto
  let ?M = "{ m. \<exists> lam. (m,lam) \<in> set n_as \<and> cmod lam = 1}" 
  have m: "m \<in> ?M" using mem lam1 by auto
  have fin: "finite ?M" 
    by (rule finite_subset[OF _ finite_set[of "map fst n_as"]], force)
  define M where "M = Max ?M"
  have "M \<in> ?M" using fin m unfolding M_def using Max_in by blast
  then obtain Lam where M: "(M,Lam) \<in> set n_as" "cmod Lam = 1" by auto
  from m fin have mM: "m \<le> M" unfolding M_def by simp
  interpret spectral_radius_1_jnf_max A n M Lam 
  proof (unfold_locales, rule A, rule nonneg, rule jnf, rule M, rule M, rule sr1)
    fix k la
    assume kla: "(k, la) \<in> set n_as" 
    with fin have 1: "cmod la = 1 \<longrightarrow> k \<le> M" unfolding M_def using Max_ge by blast
    obtain ks f where decomp: "decompose_prod_root_unity (char_poly A) = (ks, f)" by force
    from n_as0 kla have k0: "k \<noteq> 0" by force
    let ?cA = "map_mat complex_of_real A" 
    from split_list[OF kla] obtain as bs where nas: "n_as = as @ (k,la) # bs" by auto
    have rt: "poly (char_poly ?cA) la = 0" using k0
      unfolding jordan_nf_char_poly[OF jnf] nas poly_prod_list prod_list_zero_iff by auto
    have sumlist_nf: "sum_list (map fst n_as) = n" 
    proof -
      have "sum_list (map fst n_as) = dim_row (jordan_matrix n_as)" by simp
      also have "\<dots> = dim_row ?cA" using similar_matD[OF jnf'[THEN conjunct2]] by auto
      finally show ?thesis using A by auto
    qed
    from this[unfolded nas] k0 have n0: "n \<noteq> 0" by auto
    from perron_frobenius_for_complexity_jnf(4)[OF A n0 nonneg sr1 decomp rt]
    have "cmod la \<le> 1" .
    with 1 show "cmod la \<le> 1 \<and> (cmod la = 1 \<longrightarrow> k \<le> M)" by auto
  qed
  from main_theorem
  show ?thesis using mM by auto
qed
hide_const(open) spectral_radius

lemma (in ring_hom) hom_smult_mat: "mat\<^sub>h (a \<cdot>\<^sub>m A) = hom a \<cdot>\<^sub>m mat\<^sub>h A"
  by (rule eq_matI, auto simp: hom_mult)

lemma root_char_poly_smult: fixes A :: "complex mat" 
  assumes A: "A \<in> carrier_mat n n" 
  and k: "k \<noteq> 0" 
shows "(poly (char_poly (k \<cdot>\<^sub>m A)) x = 0) = (poly (char_poly A) (x / k) = 0)" 
  using order_char_poly_smult[OF A k, of x] 
  by (metis A degree_0 degree_monic_char_poly monic_degree_0 order_root smult_carrier_mat)

theorem real_nonneg_mat_spectral_radius_largest_jordan_block: 
  assumes "real_nonneg_mat A" 
  and "jordan_nf A n_as"
  and "(m, lam) \<in> set n_as" 
  and "cmod lam = spectral_radius A" 
shows "\<exists> M \<ge> m. (M, of_real (spectral_radius A)) \<in> set n_as" 
proof -
  from similar_matD[OF assms(2)[unfolded jordan_nf_def, THEN conjunct2]] obtain n where
    A: "A \<in> carrier_mat n n" by auto
  let ?c = complex_of_real
  define B where "B = map_mat Re A" 
  have B: "B \<in> carrier_mat n n" unfolding B_def using A by auto
  have AB: "A = map_mat ?c B" unfolding B_def using assms(1) 
    by (auto simp: real_nonneg_mat_def elements_mat_def)
  have nonneg: "nonneg_mat B" using assms(1) unfolding AB 
    by (auto simp: real_nonneg_mat_def elements_mat_def nonneg_mat_def)
  let ?sr = "spectral_radius A" 
  show ?thesis
  proof (cases "?sr = 0")
    case False
    define isr where "isr = inverse ?sr" 
    let ?nas = "map (\<lambda>(n, a). (n, ?c isr * a)) n_as" 
    from False have isr0: "isr \<noteq> 0" unfolding isr_def by auto
    hence cisr0: "?c isr \<noteq> 0" by auto
    from False assms(4) have isr_pos: "isr > 0" unfolding isr_def
      by (smt norm_ge_zero positive_imp_inverse_positive)    
    define C where "C = isr \<cdot>\<^sub>m B"
    have C: "C \<in> carrier_mat n n" using B unfolding C_def by auto
    have BC: "B = ?sr \<cdot>\<^sub>m C" using isr0 unfolding C_def isr_def by auto
    have nonneg: "nonneg_mat C" unfolding C_def using isr_pos nonneg
      unfolding nonneg_mat_def elements_mat_def by auto
    from jordan_nf_smult[OF assms(2)[unfolded AB] cisr0]
    have jnf: "jordan_nf (map_mat ?c C) ?nas" unfolding C_def by (auto simp: of_real_hom.hom_smult_mat)
    from assms(3) have mem: "(m, ?c isr * lam) \<in> set ?nas" by auto
    have 1: "cmod (?c isr * lam) = 1" using False isr_pos unfolding isr_def norm_mult assms(4)
      by (smt mult.commute norm_of_real right_inverse)        
    {
      fix x
      have B': "map_mat ?c B \<in> carrier_mat n n" using B by auto
      assume "poly (char_poly C) x = 0" 
      hence "poly (char_poly (map_mat ?c C)) (?c x) = 0" unfolding of_real_hom.char_poly_hom[OF C] by auto
      hence "poly (char_poly A) (?c x / ?c isr) = 0" unfolding C_def of_real_hom.hom_smult_mat AB
        unfolding root_char_poly_smult[OF B' cisr0] .
      hence "eigenvalue A (?c x / ?c isr)" unfolding eigenvalue_root_char_poly[OF A] .
      hence mem: "cmod (?c x / ?c isr) \<in> cmod ` spectrum A" unfolding spectrum_def by auto
      from Max_ge[OF finite_imageI this]
      have "cmod (?c x / ?c isr) \<le> ?sr" unfolding Spectral_Radius.spectral_radius_def
        using A card_finite_spectrum(1) by blast
      hence "cmod (?c x) \<le> 1" using isr0 isr_pos unfolding isr_def 
        by (auto simp: field_simps norm_divide norm_mult)
      hence "x \<le> 1" by auto
    } note sr = this 
    from nonneg_sr_1_largest_jb[OF nonneg jnf mem 1 sr] obtain M where
      M: "M \<ge> m" "(M,1) \<in> set ?nas" by blast
    from M(2) obtain a where mem: "(M,a) \<in> set n_as" and "1 = ?c isr * a" by auto
    from this(2) have a: "a = ?c ?sr" using isr0 unfolding isr_def by (auto simp: field_simps)
    show ?thesis
      by (intro exI[of _ M], insert mem a M(1), auto)
  next
    case True
    from jordan_nf_root_char_poly[OF assms(2,3)]
    have "eigenvalue A lam" unfolding eigenvalue_root_char_poly[OF A] .
    hence "cmod lam \<in> cmod ` spectrum A" unfolding spectrum_def by auto
    from Max_ge[OF finite_imageI this]
    have "cmod lam \<le> ?sr" unfolding Spectral_Radius.spectral_radius_def
      using A card_finite_spectrum(1) by blast
    from this[unfolded True] have lam0: "lam = 0" by auto
    show ?thesis unfolding True using assms(3)[unfolded lam0] by auto
  qed
qed
  
end