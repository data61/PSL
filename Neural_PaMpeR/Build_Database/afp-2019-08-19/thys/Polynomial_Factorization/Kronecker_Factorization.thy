section \<open>Kronecker Factorization\<close>

text \<open>This theory contains Kronecker's factorization algorithm to factor 
  integer or rational polynomials.\<close>

theory Kronecker_Factorization
imports 
  Polynomial_Interpolation.Polynomial_Interpolation
  Sqrt_Babylonian.Sqrt_Babylonian_Auxiliary
  Missing_List
  Prime_Factorization
  Precomputation
  Gauss_Lemma
  Dvd_Int_Poly
begin

subsection \<open>Definitions\<close>  
context 
  fixes df :: "int \<Rightarrow> int list"
  and dp :: "int \<Rightarrow> int list"
  and bnd :: nat
begin

definition kronecker_samples :: "nat \<Rightarrow> int list" where
  "kronecker_samples n \<equiv> let min = - int (n div 2) in [min .. min + int n]"

lemma kronecker_samples_0: "0 \<in> set (kronecker_samples n)" unfolding kronecker_samples_def by auto

text \<open>Since 0 is always a samples value, we make a case analysis: 
   we only take positive divisors of $p(0)$, and consider all divisors for other $p(j)$.\<close>
definition kronecker_factorization_main :: "int poly \<Rightarrow> int poly option" where
  "kronecker_factorization_main p \<equiv> if degree p \<le> 1 then None else let 
     p = primitive_part p;
     js = kronecker_samples bnd;
     cjs = map (\<lambda> j. (poly p j, j)) js
   in (case map_of cjs 0 of 
     Some j \<Rightarrow> Some ([:- j, 1 :])
   | None \<Rightarrow> let djs = map (\<lambda> (v,j). map (Pair j) (if j = 0 then dp v else df v)) cjs in 
     map_option the (find_map_filter newton_interpolation_poly_int
     (\<lambda> go. case go of None \<Rightarrow> False | Some g \<Rightarrow> dvd_int_poly_non_0 g p \<and> degree g \<ge> 1) 
       (concat_lists djs)))"

definition kronecker_factorization_rat_main :: "rat poly \<Rightarrow> rat poly option" where
  "kronecker_factorization_rat_main p \<equiv> map_option (map_poly of_int) 
     (kronecker_factorization_main (snd (rat_to_normalized_int_poly p)))"
end

definition kronecker_factorization :: "int poly \<Rightarrow> int poly option" where
  "kronecker_factorization p = 
     kronecker_factorization_main divisors_int divisors_int_pos (degree p div 2) p"

definition kronecker_factorization_rat :: "rat poly \<Rightarrow> rat poly option" where
  "kronecker_factorization_rat p = 
     kronecker_factorization_rat_main divisors_int divisors_int_pos (degree p div 2) p"

subsection \<open>Code setup for divisors\<close>

definition "divisors_nat_copy n \<equiv> if n = 0 then [] else remdups_adj (sort (map prod_list (subseqs (prime_factorization_nat n))))"

lemma divisors_nat_copy[simp]: "divisors_nat_copy = divisors_nat" 
  unfolding divisors_nat_def[abs_def] divisors_nat_copy_def[abs_def] ..

definition "memo_divisors_nat \<equiv> memo_nat 0 100 divisors_nat_copy"

lemma memo_divisors_nat[code_unfold]: "divisors_nat = memo_divisors_nat"  
  unfolding memo_divisors_nat_def by simp


subsection \<open>Proofs\<close>

context
begin

lemma rat_to_int_poly_of_int: assumes rp: "rat_to_int_poly (map_poly of_int p) = (c,q)"
  shows "c = 1" "q = p"
proof -
  define xs where "xs = map (snd \<circ> quotient_of) (coeffs (map_poly rat_of_int p))"
  have xs: "set xs \<subseteq> {1}" unfolding xs_def by auto
  from assms[unfolded rat_to_int_poly_def Let_def]
  have c: "c = fst (common_denom (coeffs (map_poly rat_of_int p)))" by auto
  also have "\<dots> = list_lcm xs" 
    unfolding common_denom_def Let_def xs_def by (simp add: o_assoc)
  also have "\<dots> = 1" using xs
    by (induct xs, auto)
  finally show c: "c = 1" by auto
  from rat_to_int_poly[OF rp, unfolded c] show "q = p" by auto
qed

lemma rat_to_normalized_int_poly_of_int: assumes "rat_to_normalized_int_poly (map_poly of_int p) = (c,q)"
  shows "c \<in> \<int>" "p \<noteq> 0 \<Longrightarrow> c = of_int (content p) \<and> q = primitive_part p"
proof -
  obtain d r where ri: "rat_to_int_poly (map_poly rat_of_int p) = (d,r)" by force
  from rat_to_int_poly_of_int[OF ri]
    assms[unfolded rat_to_normalized_int_poly_def ri split] 
  show "c \<in> \<int>" "p \<noteq> 0 \<Longrightarrow> c = of_int (content p) \<and> q = primitive_part p" 
    by (auto split: if_splits)
qed

lemma dvd_poly_int_content_1: assumes c_x: "content x = 1"
  shows "(x dvd y) = (map_poly rat_of_int x dvd map_poly of_int y)"
proof -
  let ?r = "rat_of_int"
  let ?rp = "map_poly ?r"
  show ?thesis
  proof
    assume "x dvd y"
    then obtain z where "y = x * z" unfolding dvd_def by auto
    from arg_cong[OF this, of ?rp]
    show "?rp x dvd ?rp y" by auto
  next
    assume dvd: "?rp x dvd ?rp y"
    show "x dvd y"
    proof (cases "y = 0")
      case True
      thus ?thesis by auto
    next
      case False note y0 = this
      hence "?rp y \<noteq> 0" by simp
      hence rx0: "?rp x \<noteq> 0" using dvd by auto
      hence x0: "x \<noteq> 0" by simp
      from dvd obtain z where prod: "?rp y = ?rp x * z" unfolding dvd_def by auto
      obtain cx xx where x: "rat_to_normalized_int_poly (?rp x) = (cx, xx)" by force
      from rat_to_int_factor_explicit[OF prod x] obtain z where y: "y = xx * smult (content y) z" by auto
      from rat_to_normalized_int_poly[OF x] rx0 have xx: "?rp x = smult cx (?rp xx)" 
        and cxx: "content xx = 1" and cx0: "cx > 0" by auto
      obtain cn cd where quot: "quotient_of cx = (cn,cd)" by force
      from quotient_of_div[OF quot] have cx: "cx = ?r cn / ?r cd" by auto
      from quotient_of_denom_pos[OF quot] have cd0: "cd > 0" by auto
      with cx cx0 have cn0: "cn > 0" by (simp add: zero_less_divide_iff)
      from arg_cong[OF xx, of "smult (?r cd)"] have "smult (?r cd) (?rp x) = smult (?r cn) (?rp xx)"
        unfolding cx using cd0 by (auto simp: field_simps)
      from this have id: "smult cd x = smult cn xx" by (fold hom_distribs, unfold of_int_poly_hom.eq_iff)
      from arg_cong[OF this, of content, unfolded content_smult_int cxx] cn0 cd0 
      have cn: "cn = cd * content x" by auto
      from quotient_of_coprime[OF quot, unfolded cn] cd0 have "cd = 1" by auto
      with cx have cx: "cx = ?r cn" by auto
      from xx[unfolded this] have x: "x = smult cn xx" by (fold hom_distribs, simp)
      from arg_cong[OF this, of content, unfolded content_smult_int c_x cxx] cn0 have "cn = 1" by auto
      with x have xx: "xx = x" by auto
      show "x dvd y" using y[unfolded xx] unfolding dvd_def by blast
    qed
  qed
qed

lemma content_x_minus_const_int[simp]: "content [: c, 1 :] = (1 :: int)"
  unfolding content_def by auto

lemma length_upto_add_nat[simp]: "length [a .. a + int n] = Suc n"
proof (induct n arbitrary: a)
  case (0 a)
  show ?case using upto.simps[of a a] by auto
next
  case (Suc n a)
  from Suc[of "a + 1"]
  show ?case using upto.simps[of a "a + int (Suc n)"] by (auto simp: ac_simps)
qed

lemma kronecker_samples: "distinct (kronecker_samples n)" "length (kronecker_samples n) = Suc n"
  unfolding kronecker_samples_def Let_def length_upto_add_nat by auto


lemma dvd_int_poly_non_0_degree_1[simp]: "degree q \<ge> 1 \<Longrightarrow> dvd_int_poly_non_0 q p = (q dvd p)"
  by (intro dvd_int_poly_non_0, auto)


context fixes df dp :: "int \<Rightarrow> int list"
  and bnd :: nat
begin

lemma kronecker_factorization_main_sound: assumes some: "kronecker_factorization_main df dp bnd p = Some q"
  and bnd: "degree p \<ge> 2 \<Longrightarrow> bnd \<ge> 1"
  shows "degree q \<ge> 1" "degree q \<le> bnd" "q dvd p"
proof -
  let ?r = "rat_of_int"
  let ?rp = "map_poly ?r"
  note res = some[unfolded kronecker_factorization_main_def Let_def]
  from res have dp: "degree p \<ge> 2" and "(degree p \<le> 1) = False" by (auto split: if_splits)
  note res = res[unfolded this if_False]
  note bnd = bnd[OF dp]
  define P where "P = primitive_part p"
  have degP: "degree P = degree p" unfolding P_def by simp
  define js where "js = kronecker_samples bnd"
  define filt where "filt = (case_option False (\<lambda>g. dvd_int_poly_non_0 g P \<and> 1 \<le> degree g))"
  define tests where "tests = concat_lists (map (\<lambda>(v, j). map (Pair j) (if j = 0 then dp v else df v)) (map (\<lambda>j. (poly P j, j)) js))"
  note res = res[folded P_def, folded js_def filt_def, folded tests_def]
  let ?zero = "map (\<lambda>j. (poly P j, j)) js"
  from res have res: "(case map_of ?zero 0 of
     None \<Rightarrow> map_option the (find_map_filter newton_interpolation_poly_int filt tests) | Some j \<Rightarrow> Some [:- j, 1:]) =
     Some q" by auto
  have "degree q \<ge> 1 \<and> degree q \<le> bnd \<and> q dvd P"
  proof (cases "map_of ?zero 0")
    case (Some j)
    with res have q: "q = [: - j, 1 :]" by auto
    from map_of_SomeD[OF Some] have 0: "poly P j = 0" by auto
    hence "poly (?rp P) (?r j) = 0" by simp
    hence "[: - ?r j, 1 :] dvd ?rp P" using poly_eq_0_iff_dvd by blast
    also have "[: - ?r j, 1 :] = ?rp q" unfolding q by simp
    finally have dvd: "?rp q dvd ?rp P" .
    have "q dvd P"
      by (subst dvd_poly_int_content_1, insert dvd q, auto)
    with q dp bnd show ?thesis by auto
  next
    case None
    from res[unfolded None] 
    have res: "map_option the (find_map_filter newton_interpolation_poly_int filt tests) = Some q" by auto
    then obtain qq where 
      res: "find_map_filter newton_interpolation_poly_int filt tests = Some qq" and q: "q = the qq" 
      by (auto split: option.splits)
    from find_map_filter_Some[OF res] 
    have filt: "filt qq" and tests: "qq \<in> newton_interpolation_poly_int ` set tests" by auto
    from filt[unfolded filt_def] q obtain g where dvd: "g dvd P" and dg: "1 \<le> degree g" and qq: "qq = Some g" 
      by (cases qq, auto)
    from q qq have gq: "g = q" by auto
    from tests obtain t where t: "t \<in> set tests" and l: "newton_interpolation_poly_int t = Some g" unfolding qq 
      by auto
    from t[unfolded tests_def]
    have lent: "length t = length js" and "\<And> i. i < length js \<Longrightarrow> map fst t ! i = js ! i" by auto
    hence id: "map fst t = js"
      by (intro nth_equalityI, auto)
    have dist: "distinct js" and lenj: "length js = Suc bnd" unfolding js_def degP
      using kronecker_samples by auto
    from newton_interpolation_poly_int_Some[OF dist[folded id] l, unfolded lent lenj]
    have "degree g \<le> bnd" by auto
    with dvd dg show ?thesis unfolding gq by auto
  qed note main = this
  thus "degree q \<ge> 1" "degree q \<le> bnd" by auto
  from content_times_primitive_part[of p] have "p = smult (content p) P" unfolding P_def by auto
  with main show "q dvd p" by (metis dvd_smult)
qed

lemma kronecker_factorization_rat_main_sound: assumes 
  some: "kronecker_factorization_rat_main df dp bnd p = Some q"
  and bnd: "degree p \<ge> 2 \<Longrightarrow> bnd \<ge> 1"
  shows "degree q \<ge> 1" "degree q \<le> bnd" "q dvd p"
proof -
  let ?r = "rat_of_int"
  let ?rp = "map_poly ?r"
  let ?p = "rat_to_normalized_int_poly p"
  obtain a P where rp: "?p = (a,P)" by force
  from rat_to_normalized_int_poly[OF this] have p: "p = smult a (?rp P)" and a: "a \<noteq> 0" 
    and deg: "degree P = degree p" by auto
  from some[unfolded kronecker_factorization_rat_main_def rp]
  obtain Q where some: "kronecker_factorization_main df dp bnd P = Some Q" and q: "q = ?rp Q" by auto
  from kronecker_factorization_main_sound[OF some bnd] have dQ: "1 \<le> degree Q" 
    "degree Q \<le> bnd"
    and dvd: "Q dvd P" unfolding deg by auto
  from dvd obtain R where PQR: "P = Q * R" unfolding dvd_def by auto
  from p[unfolded arg_cong[OF this, of ?rp]]
  have "p = q * smult a (?rp R)" unfolding q by (auto simp: hom_distribs)
  thus "q dvd p" unfolding dvd_def by blast
  from q dQ show "degree q \<ge> 1" "degree q \<le> bnd" by auto
qed


context
  assumes df: "divisors_fun df" and dpf: "divisors_pos_fun dp"
begin

lemma kronecker_factorization_main_complete: assumes 
  none: "kronecker_factorization_main df dp bnd p = None"
  and dp: "degree p \<ge> 2"
  shows "\<not> (\<exists> q. 1 \<le> degree q \<and> degree q \<le> bnd \<and> q dvd p)"
proof -
  let ?r = "rat_of_int"
  let ?rp = "map_poly ?r"
  from dp have "(degree p \<le> 1) = False" by auto
  note res = none[unfolded kronecker_factorization_main_def Let_def this if_False]
  define P where "P = primitive_part p"
  have degP: "degree P = degree p" unfolding P_def by simp
  define js where "js = kronecker_samples bnd"
  define filt where "filt = (case_option False (\<lambda>g. dvd_int_poly_non_0 g P \<and> 1 \<le> degree g))"
  define tests where "tests = concat_lists (map (\<lambda>(v, j). map (Pair j) (if j = 0 then dp v else df v)) (map (\<lambda>j. (poly P j, j)) js))"
  note res = res[folded P_def, folded js_def filt_def, folded tests_def]
  let ?zero = "map (\<lambda>j. (poly P j, j)) js"
  from res have res: "(case map_of ?zero 0 of
     None \<Rightarrow> map_option the (find_map_filter newton_interpolation_poly_int filt tests) | Some j \<Rightarrow> Some [:- j, 1:]) =
     None" by auto
  hence zero: "map_of ?zero 0 = None" by (auto split: option.splits)
  with res have res: "find_map_filter newton_interpolation_poly_int filt tests = None" by auto
  {
    fix qq
    assume qq: "1 \<le> degree qq" "degree qq \<le> bnd" and dvd: "qq dvd p"
    define q' where "q' = primitive_part qq"
    define q where "q = (if poly q' 0 > 0 then q' else -q')"
    from qq have q': "1 \<le> degree q'" "degree q' \<le> bnd" unfolding q'_def by auto
    hence q: "1 \<le> degree q" "degree q \<le> bnd" unfolding q_def by auto
    from dvd have "qq dvd (smult (content p) P)" 
      using content_times_primitive_part[of p] unfolding P_def by simp
    from dvd_smult_int[OF _ this] dp have "q' dvd P" unfolding q'_def
      by force
    hence dvd: "q dvd P" unfolding q_def by auto      
    then obtain r where P: "P = q * r" unfolding dvd_def by auto
    {
      fix j
      assume j: "j \<in> set js"
      from P have id: "poly P j = poly q j * poly r j" by auto
      hence dvd: "poly q j dvd poly P j" by auto
      from j have "(poly P j, j) \<in> set ?zero" by auto
      with zero have zero: "poly P j \<noteq> 0" unfolding map_of_eq_None_iff by force
      with id have "poly q j \<noteq> 0" by auto
      hence "j = 0 \<Longrightarrow> poly q j > 0" unfolding q_def by auto
      from divisors_funD[OF df zero dvd] divisors_pos_funD[OF dpf zero dvd this] 
      have "poly q j \<in> set (df (poly P j))" "j = 0 \<Longrightarrow> poly q j \<in> set (dp (poly P j))" .
    } note mem1 = this
    define t where "t = map (\<lambda> j. (j, poly q j)) js"
    have t: "t \<in> set tests" unfolding tests_def concat_lists_listset listset length_map map_map o_def
    proof (rule, intro conjI allI impI)
      show "length t = length js" unfolding t_def by simp
      fix i
      assume i: "i < length js"
      hence jsi: "js ! i \<in> set js" by auto
      have ti: "t ! i = (js ! i, poly q (js ! i))" unfolding t_def using i by auto
      let ?f = "(\<lambda>x. set (case (poly P x, x) of (v, j) \<Rightarrow> map (Pair j) (if j = 0 then dp v else df v)))"
      show "t ! i \<in> map ?f js ! i"
        unfolding ti nth_map[OF i] split using mem1[OF jsi] by auto
    qed
    have dist: "distinct js" and lenj: "length js = Suc bnd" unfolding js_def degP
      using kronecker_samples by auto
    have map_fst: "map fst t = js" unfolding t_def
      by (rule nth_equalityI, auto)
    with dist have dist: "distinct (map fst t)" by simp
    from lenj q degP have degq: "degree q < length t" unfolding t_def by auto
    from find_map_filter_None[OF res] t 
    have nfilt: "\<not> filt (newton_interpolation_poly_int t)" by auto
    have qt: "\<And>x y. (x, y) \<in> set t \<Longrightarrow> poly q x = y" unfolding t_def by auto
    from interpolation_poly_int_None[OF dist _ qt degq, of Newton] have
      "newton_interpolation_poly_int t \<noteq> None" by auto
    then obtain g where lt: "newton_interpolation_poly_int t = Some g" by auto
    from newton_interpolation_poly_int_Some[OF dist lt] 
    have gt: "\<And> x y. (x, y) \<in> set t \<Longrightarrow> poly g x = y" and degg: "degree g < length t" 
      using degq by auto
    from uniqueness_of_interpolation_point_list[OF dist qt degq gt degg]
    have g: "g = q" by auto
    from nfilt[unfolded lt g] have "\<not> filt (Some q)" .
    from this[unfolded filt_def] q dvd have False by auto
  } note main = this
  thus ?thesis by auto
qed

lemma kronecker_factorization_rat_main_complete: assumes 
  none: "kronecker_factorization_rat_main df dp bnd p = None"
  and dp: "degree p \<ge> 2"
  shows "\<not> (\<exists> q. 1 \<le> degree q \<and> degree q \<le> bnd \<and> q dvd p)"
proof 
  assume "\<exists> q. 1 \<le> degree q \<and> degree q \<le> bnd \<and> q dvd p"
  then obtain q where q: "1 \<le> degree q" "degree q \<le> bnd" and dvd: "q dvd p" by auto
  from dvd obtain r where prod: "p = q * r" unfolding dvd_def by auto
  let ?r = "rat_of_int"
  let ?rp = "map_poly ?r"
  let ?p = "rat_to_normalized_int_poly p"
  obtain a P where rp: "?p = (a,P)" by force
  from rat_to_normalized_int_poly[OF this] have deg: "degree P = degree p" by auto
  from rat_to_int_factor_normalized_int_poly[OF prod rp]
    obtain g' where dvd: "g' dvd P" and dg: "degree g' = degree q" by (auto intro: dvdI)
  have "kronecker_factorization_main df dp bnd P = None" 
      using none[unfolded kronecker_factorization_rat_main_def rp] by auto
  from kronecker_factorization_main_complete[OF this dp[folded deg]] dg dvd q show False by auto
qed
end
end

lemma kronecker_factorization:
  "kronecker_factorization p = Some q \<Longrightarrow> 
    degree q \<ge> 1 \<and> degree q < degree p \<and> q dvd p"
  "kronecker_factorization p = None \<Longrightarrow> degree p \<ge> 1 \<Longrightarrow> irreducible\<^sub>d p" 
proof -
  note d = kronecker_factorization_def
  {
    assume "kronecker_factorization p = Some q"
    from kronecker_factorization_main_sound[OF this[unfolded d]]
    show "degree q \<ge> 1 \<and> degree q < degree p \<and> q dvd p" by auto linarith
  }
  assume kf: "kronecker_factorization p = None" and deg: "degree p \<ge> 1"
  show "irreducible\<^sub>d p"
  proof (cases "degree p = 1")
    case True 
    thus ?thesis by (rule linear_irreducible\<^sub>d)
  next
    case False
    with deg have "degree p \<ge> 2" by auto
    with kronecker_factorization_main_complete[OF divisors_fun_int divisors_pos_fun_int kf[unfolded d] this]
    show ?thesis
      by (intro irreducible\<^sub>dI2, auto)
  qed
qed

lemma kronecker_factorization_rat:
  "kronecker_factorization_rat p = Some q \<Longrightarrow> 
    degree q \<ge> 1 \<and> degree q < degree p \<and> q dvd p"
  "kronecker_factorization_rat p = None \<Longrightarrow> degree p \<ge> 1 \<Longrightarrow> irreducible\<^sub>d p" 
proof -
  note d = kronecker_factorization_rat_def
  {
    assume "kronecker_factorization_rat p = Some q"
    from kronecker_factorization_rat_main_sound[OF this[unfolded d]]
    show "degree q \<ge> 1 \<and> degree q < degree p \<and> q dvd p" by auto linarith
  }
  assume kf: "kronecker_factorization_rat p = None" and deg: "degree p \<ge> 1"
  show "irreducible\<^sub>d p"
  proof (cases "degree p = 1")
    case True 
    thus ?thesis by (rule linear_irreducible\<^sub>d)
  next
    case False
    with deg have "degree p \<ge> 2" by auto
    with kronecker_factorization_rat_main_complete[OF divisors_fun_int divisors_pos_fun_int kf[unfolded d] this]
    show ?thesis
      by (intro irreducible\<^sub>dI2, auto)
  qed
qed

end  
end
