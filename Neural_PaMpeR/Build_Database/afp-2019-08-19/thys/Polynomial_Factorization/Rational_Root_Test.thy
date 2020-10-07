(*  
    Author:      René Thiemann 
                 Akihisa Yamada
    License:     BSD
*)
section \<open>Rational Root Test\<close>

text \<open>This theory contains a formalization of the rational root test, i.e., a decision
  procedure to test whether a polynomial over the rational numbers has a rational root.\<close>

theory Rational_Root_Test
imports
  Gauss_Lemma
  Missing_List
  Prime_Factorization
begin

definition rational_root_test_main :: 
  "(int \<Rightarrow> int list) \<Rightarrow> (int \<Rightarrow> int list) \<Rightarrow> rat poly \<Rightarrow> rat option" where
  "rational_root_test_main df dp p \<equiv> let ip = snd (rat_to_normalized_int_poly p); 
    a0 = coeff ip 0; an = coeff ip (degree ip)
    in if a0 = 0 then Some 0 else
     let d0 = df a0; dn = dp an 
     in map_option fst 
     (find_map_filter (\<lambda> x. (x,poly p x)) 
     (\<lambda> (_, res). res = 0) [rat_of_int b0 / of_int bn . b0 <- d0, bn <- dn, coprime b0 bn ])"

definition rational_root_test :: "rat poly \<Rightarrow> rat option" where
  "rational_root_test p = 
     rational_root_test_main divisors_int divisors_int_pos p"

lemma rational_root_test_main: 
  "rational_root_test_main df dp p = Some x \<Longrightarrow> poly p x = 0"
  "divisors_fun df \<Longrightarrow> divisors_pos_fun dp \<Longrightarrow> rational_root_test_main df dp p = None \<Longrightarrow> \<not> (\<exists> x. poly p x = 0)"
proof -
  let ?r = "rat_of_int"
  let ?rp = "map_poly ?r"
  obtain a ip where rp: "rat_to_normalized_int_poly p = (a,ip)" by force
  from rat_to_normalized_int_poly[OF this] have p: "p = smult a (?rp ip)" and a00: "a \<noteq> 0" 
    and cip: "p \<noteq> 0 \<Longrightarrow> content ip = 1" by auto
  let ?a0 = "coeff ip 0"
  let ?an = "coeff ip (degree ip)"
  let ?d0 = "df ?a0"
  let ?dn = "dp ?an"
  let ?ip = "?rp ip"
  define tests where "tests = [rat_of_int b0 / rat_of_int bn . b0 <- ?d0, bn <- ?dn, coprime b0 bn ]"
  let ?f = "(\<lambda> x. (x,poly p x))"
  let ?test = "(\<lambda> (_, res). res = 0)"
  define mo where "mo = find_map_filter ?f ?test tests"
  note d = rational_root_test_main_def[of df dp p, unfolded Let_def rp snd_conv mo_def[symmetric] tests_def[symmetric]]
  {
    assume "rational_root_test_main df dp p = Some x"
    from this[unfolded d] have "?a0 = 0 \<and> x = 0 \<or> map_option fst mo = Some x" by (auto split: if_splits)
    thus "poly p x = 0"
    proof
      assume *: "?a0 = 0 \<and> x = 0"
      hence "coeff p 0 = 0" unfolding p coeff_smult by simp
      hence "poly p 0 = 0" by (cases p, auto)
      with * show ?thesis by auto
    next
      assume "map_option fst mo = Some x"
      then obtain pair where find: "find_map_filter ?f ?test tests = Some pair" and x: "x = fst pair"
        unfolding mo_def by (auto split: option.splits)      
      then obtain z where pair: "pair = (x,z)" by (cases pair, auto)
      from find_map_filter_Some[OF find, unfolded pair split] show "poly p x = 0" by auto
    qed
  }
  assume df: "divisors_fun df" and dp: "divisors_pos_fun dp" and res: "rational_root_test_main df dp p = None"
  note df = divisors_funD[OF df] note dp = divisors_pos_funD[OF dp]
  from res[unfolded d] have a0: "?a0 \<noteq> 0" and res: "map_option fst mo = None" by (auto split: if_splits)
  from res[unfolded mo_def] have find: "find_map_filter ?f ?test tests = None" by auto  
  show "\<not> (\<exists> x. poly p x = 0)"
  proof
    assume "\<exists> x. poly p x = 0"
    then obtain x where "poly p x = 0" by auto
    from this[unfolded p] a00 have "poly (?rp ip) x = 0" by auto
    from this[unfolded poly_eq_0_iff_dvd] have "[: -x , 1 :] dvd ?ip" by auto
    then obtain q where ip_id: "?ip = [: -x, 1 :] * q" unfolding dvd_def by auto
    obtain c q where x1: "rat_to_normalized_int_poly [: -x, 1 :] = (c, q)" by force
    from rat_to_int_factor_explicit[OF ip_id x1] obtain r where  ip: "ip = q * r" by blast
    from rat_to_normalized_int_poly(4)[OF x1] have deg: "degree q = 1" by auto
    from degree1_coeffs[OF deg] obtain a b where q: "q = [: b, a :]" and a: "a \<noteq> 0" by auto
    have ipr: "ip = [: b, a :] * r" using ip q by auto
    from arg_cong[OF ipr, of "\<lambda> p. coeff p 0"] have ba0: "b dvd ?a0" by auto
    have rpq: "?rp q = [: ?r b, ?r a :]" unfolding q
    proof (rule poly_eqI, unfold of_int_hom.coeff_map_poly_hom)
      fix n
      show "?r (coeff [:b, a:] n) = coeff [: ?r b, ?r a:] n"
        unfolding coeff_pCons
        by (cases n, force, cases "n - 1", auto)
    qed
    from arg_cong[OF ip, of ?rp, unfolded of_int_poly_hom.hom_mult rpq] have "[: ?r b, ?r a :] dvd ?rp ip"
      unfolding dvd_def by blast
    hence "smult (inverse (?r a)) [: ?r b , ?r a :] dvd ?rp ip" 
      by (rule smult_dvd, insert a, auto)
    also have "smult (inverse (?r a)) [: ?r b , ?r a :] = [: ?r b / ?r a, 1 :]" using a 
      by (simp add: field_simps)
    finally have "[: - (- ?r b / ?r a), 1 :] dvd ?rp ip" by simp
    from this[unfolded poly_eq_0_iff_dvd[symmetric]] 
    have rt: "poly (?rp ip) (- ?r b / ?r a) = 0" .
    hence rt: "poly p (- ?r b / ?r a) = 0" 
      unfolding p using a00 by simp
    obtain aa bb where quot: "quotient_of (- ?r b / ?r a) = (bb,aa)" by force
    hence "quotient_of (?r (-b) / ?r a) = (bb, aa)" by simp
    from quotient_of_int_div[OF this \<open>a \<noteq> 0\<close>] obtain z where 
      z: "z \<noteq> 0" and b: "- b = z * bb" and a: "a = z * aa" by auto
    from rt[unfolded quotient_of_div[OF quot]] have rt: "poly p (?r bb / ?r aa) = 0" by auto
    from quotient_of_coprime[OF quot] have cop: "coprime bb aa" "coprime (- bb) aa" by auto
    from quotient_of_denom_pos[OF quot] have aa: "aa > 0" by auto
    from ba0 arg_cong[OF b, of uminus] z have bba0: "bb dvd ?a0" unfolding dvd_def
      by (metis ba0 dvdE dvd_mult_right minus_dvd_iff)      
    hence bb0: "bb \<noteq> 0" using a0 by auto
    from df[OF a0 bba0] have bb: "bb \<in> set ?d0" by auto
    from a0 have ip0: "ip \<noteq> 0" by auto
    hence an0: "?an \<noteq> 0" by auto
    from ipr ip0 have "r \<noteq> 0" by auto
    from degree_mult_eq[OF _ this, of "[:b,a:]", folded ipr] \<open>a \<noteq> 0\<close> ipr 
    have deg: "degree ip = Suc (degree r)" by auto
    from arg_cong[OF ipr, of "\<lambda> p. coeff p (degree ip)"] have ba0: "a dvd ?an"
      unfolding deg by (auto simp: coeff_eq_0)
    hence "aa dvd ?an" using \<open>a \<noteq> 0\<close> unfolding a by (auto simp: dvd_def)
    from dp[OF an0 this aa] have aa: "aa \<in> set ?dn" .
    from find_map_filter_None[OF find] rt have "(?r bb / ?r aa) \<notin> set tests" by auto
    note test = this[unfolded tests_def, simplified, rule_format, of _ aa]
    from this[of bb] cop bb aa
    show False by auto
  qed
qed

lemma rational_root_test:   
  "rational_root_test p = Some x \<Longrightarrow> poly p x = 0"
  "rational_root_test p = None \<Longrightarrow> \<not> (\<exists> x. poly p x = 0)"
  using rational_root_test_main(1) rational_root_test_main(2)[OF divisors_fun_int divisors_pos_fun_int]
  unfolding rational_root_test_def by blast+


end
