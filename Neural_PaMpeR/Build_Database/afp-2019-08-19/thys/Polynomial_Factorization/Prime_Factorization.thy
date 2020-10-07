(*  
    Author:      René Thiemann 
                 Akihisa Yamada
    License:     BSD
*)
section \<open>Prime Factorization\<close>

text \<open>This theory contains not-completely naive algorithms to test primality
  and to perform prime factorization. More precisely, it corresponds to prime factorization
  algorithm A in Knuth's textbook \cite{Knuth}.\<close>

theory Prime_Factorization
imports
  "HOL-Computational_Algebra.Primes"
  Missing_List
  Missing_Multiset
begin

subsection \<open>Definitions\<close>

definition primes_1000 :: "nat list" where
  "primes_1000 = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101,
  103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199,
  211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317,
  331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419, 421, 431, 433, 439, 443,
  449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509, 521, 523, 541, 547, 557, 563, 569, 571, 577,
  587, 593, 599, 601, 607, 613, 617, 619, 631, 641, 643, 647, 653, 659, 661, 673, 677, 683, 691, 701,
  709, 719, 727, 733, 739, 743, 751, 757, 761, 769, 773, 787, 797, 809, 811, 821, 823, 827, 829, 839,
  853, 857, 859, 863, 877, 881, 883, 887, 907, 911, 919, 929, 937, 941, 947, 953, 967, 971, 977, 983,
  991, 997]"

lemma primes_1000: "primes_1000 = filter prime [0..<1001]"
  by eval

definition next_candidates :: "nat \<Rightarrow> nat \<times> nat list" where
  "next_candidates n = (if n = 0 then (1001,primes_1000) else (n + 30, 
    [n,n+2,n+6,n+8,n+12,n+18,n+20,n+26]))"

definition "candidate_invariant n = (n = 0 \<or> n mod 30 = (11 :: nat))"

partial_function (tailrec) remove_prime_factor :: "nat \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> nat \<times> nat list " where
  [code]: "remove_prime_factor p n ps = (case Divides.divmod_nat n p of (n',m) \<Rightarrow> 
     if m = 0 then remove_prime_factor p n' (p # ps) else (n,ps))" 
  
partial_function (tailrec) prime_factorization_nat_main 
  :: "nat \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat list" where
  [code]: "prime_factorization_nat_main n j is ps = (case is of 
     [] \<Rightarrow> 
       (case next_candidates j of (j,is) \<Rightarrow> prime_factorization_nat_main n j is ps)
   | (i # is) \<Rightarrow> (case Divides.divmod_nat n i of (n',m) \<Rightarrow> 
       if m = 0 then case remove_prime_factor i n' (i # ps)
       of (n',ps') \<Rightarrow> if n' = 1 then ps' else 
         prime_factorization_nat_main n' j is ps'
       else if i * i \<le> n then prime_factorization_nat_main n j is ps
       else (n # ps)))"

partial_function (tailrec) prime_nat_main 
  :: "nat \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> bool" where
  [code]: "prime_nat_main n j is = (case is of 
    [] \<Rightarrow> (case next_candidates j of (j,is) \<Rightarrow> prime_nat_main n j is)
  | (i # is) \<Rightarrow> (if i dvd n then i \<ge> n else if i * i \<le> n then prime_nat_main n j is
    else True))"

definition prime_nat :: "nat \<Rightarrow> bool" where
  "prime_nat n \<equiv> if n < 2 then False else \<comment> \<open>TODO: integrate precomputed map\<close>
     case next_candidates 0 of (j,is) \<Rightarrow> prime_nat_main n j is"

definition prime_factorization_nat :: "nat \<Rightarrow> nat list" where
  "prime_factorization_nat n \<equiv> rev (if n < 2 then [] else 
    case next_candidates 0 of (j,is) \<Rightarrow> prime_factorization_nat_main n j is [])"

definition divisors_nat :: "nat \<Rightarrow> nat list" where 
  "divisors_nat n \<equiv> if n = 0 then [] else 
     remdups_adj (sort (map prod_list (subseqs (prime_factorization_nat n))))"

definition divisors_int_pos :: "int \<Rightarrow> int list" where
  "divisors_int_pos x \<equiv> map int (divisors_nat (nat (abs x)))"

definition divisors_int :: "int \<Rightarrow> int list" where
  "divisors_int x \<equiv> let xs = divisors_int_pos x in xs @ (map uminus xs)"

subsection \<open>Proofs\<close>

lemma remove_prime_factor: assumes res: "remove_prime_factor i n ps = (m,qs)"
  and i: "i > 1"
  and n: "n \<noteq> 0"
  shows "\<exists> rs. qs = rs @ ps \<and> n = m * prod_list rs \<and> \<not> i dvd m \<and> set rs \<subseteq> {i}"
  using res n
proof (induct n arbitrary: ps rule: less_induct)
  case (less n ps)
  obtain n' mo where dm: "Divides.divmod_nat n i = (n',mo)" by force
  hence n': "n' = n div i" and mo: "mo = n mod i" by (auto simp: divmod_nat_def)
  from less(2)[unfolded remove_prime_factor.simps[of i n] dm]
  have res: "(if mo = 0 then remove_prime_factor i n' (i # ps) else (n, ps)) = (m, qs)" by auto
  from less(3) have n: "n \<noteq> 0" by auto
  with n' i have "n' < n" by auto
  note IH = less(1)[OF this]
  show ?case
  proof (cases "mo = 0")
    case True
    with mo n' have n: "n = n' * i" by auto
    with \<open>n \<noteq> 0\<close> have n': "n' \<noteq> 0" by auto
    from True res have "remove_prime_factor i n' (i # ps) = (m,qs)" by auto
    from IH[OF this n'] obtain rs where 
      "qs = rs @ i # ps" and "n' = m * prod_list rs \<and> \<not> i dvd m \<and> set rs \<subseteq> {i}" by auto
    thus ?thesis
      by (intro exI[of _ "rs @ [i]"], unfold n, auto)
  next
    case False
    with mo have i_n: "\<not> i dvd n" by auto
    from False res have id: "m = n" "qs = ps" by auto
    show ?thesis unfolding id using i_n by auto
  qed
qed 

lemma prime_sqrtI: assumes n: "n \<ge> 2" 
  and small: "\<And> j. 2 \<le> j \<Longrightarrow> j < i \<Longrightarrow> \<not> j dvd n"
  and i: "\<not> i * i \<le> n"
  shows "prime (n::nat)" unfolding prime_nat_iff
proof (intro conjI impI allI)
  show "1 < n" using n by auto
  fix j
  assume jn: "j dvd n" 
  from jn obtain k where njk: "n = j * k" unfolding dvd_def by auto
  with \<open>1 < n\<close> have jn: "j \<le> n" by (metis dvd_imp_le jn neq0_conv not_less0)
  show "j = 1 \<or> j = n"
  proof (rule ccontr)
    assume "\<not> ?thesis"
    with njk n have j1: "j > 1 \<and> j \<noteq> n" by simp
    have "\<exists> j k. 1 < j \<and> j \<le> k \<and> n = j * k"
    proof (cases "j \<le> k")
      case True
      thus ?thesis unfolding njk using j1 by blast
    next
      case False
      show ?thesis by (rule exI[of _ k], rule exI[of _ j], insert \<open>1 < n\<close> j1 njk False, auto)
        (metis Suc_lessI mult_0_right neq0_conv)
    qed
    then obtain j k where j1: "1 < j" and jk: "j \<le> k" and njk: "n = j * k" by auto
    with small[of j] have ji: "j \<ge> i" unfolding dvd_def by force
    from mult_mono[OF ji ji] have "i * i \<le> j * j" by auto
    with i have "j * j > n" by auto
    from this[unfolded njk] have "k < j" by auto
    with jk show False by auto
  qed
qed

lemma candidate_invariant_0: "candidate_invariant 0"
  unfolding candidate_invariant_def by auto

lemma next_candidates: assumes res: "next_candidates n = (m,ps)"
  and n: "candidate_invariant n"
  shows "candidate_invariant m" "sorted ps" "{i. prime i \<and> n \<le> i \<and> i < m} \<subseteq> set ps" 
    "set ps \<subseteq> {2..} \<inter> {n..<m}" "distinct ps" "ps \<noteq> []" "n < m"
  unfolding candidate_invariant_def
proof -
  note res = res[unfolded next_candidates_def]
  note n = n[unfolded candidate_invariant_def]
  show "m = 0 \<or> m mod 30 = 11" using res n by (auto split: if_splits)
  show "sorted ps" using res n by (auto split: if_splits simp: primes_1000_def sorted2_simps simp del: sorted.simps(2))
  show "set ps \<subseteq> {2..} \<inter> {n..<m}" using res n by (auto split: if_splits simp: primes_1000_def)
  show "distinct ps" using res n by (auto split: if_splits simp: primes_1000_def)
  show "ps \<noteq> []" using res n by (auto split: if_splits simp: primes_1000_def)
  show "n < m" using res by (auto split: if_splits)
  show "{i. prime i \<and> n \<le> i \<and> i < m} \<subseteq> set ps"
  proof (cases "n = 0")
    case True
    hence *: "m = 1001" "ps = primes_1000" using res by auto
    show ?thesis unfolding * True primes_1000 by auto
  next
    case False
    hence n: "n mod 30 = 11" and m: "m = n + 30" and ps: "ps = [n,n+2,n+6,n+8,n+12,n+18,n+20,n+26]" 
      using res n by auto
    {
      fix i
      assume *: "prime i" "n \<le> i" "i < n + 30" "i \<notin> set ps"
      from n * have i11: "i \<ge> 11" by auto
      define j where "j = i - n" 
      have i: "i = n + j" using \<open>n \<le> i\<close> j_def by auto
      have "i mod 30 = (j + n) mod 30" using \<open>n \<le> i\<close> unfolding j_def by simp
      also have "\<dots> = (j mod 30 + n mod 30) mod 30"
        by (simp add: mod_simps)
      also have "\<dots> = (j mod 30 + 11) mod 30" unfolding n by simp
      finally have i30: "i mod 30 = (j mod 30 + 11) mod 30" by simp
      have 2: "2 dvd (30 :: nat)" and 112: "11 mod (2 :: nat) = 1" by simp_all
      have "(j + 11) mod 2 = (j + 1) mod 2"
        by (rule mod_add_cong) simp_all
      with arg_cong [OF i30, of "\<lambda>j. j mod 2"]
      have 2: "i mod 2 = (j mod 2 + 1) mod 2"
        by (simp add: mod_simps mod_mod_cancel [OF 2])
      have 3: "3 dvd (30 :: nat)" and 113: "11 mod (3 :: nat) = 2" by simp_all
      have "(j + 11) mod 3 = (j + 2) mod 3"
        by (rule mod_add_cong) simp_all
      with arg_cong [OF i30, of "\<lambda> j. j mod 3"] have 3: "i mod 3 = (j mod 3 + 2) mod 3"
        by (simp add: mod_simps mod_mod_cancel [OF 3])
      have 5: "5 dvd (30 :: nat)" and 115: "11 mod (5 :: nat) = 1" by simp_all
      have "(j + 11) mod 5 = (j + 1) mod 5"
        by (rule mod_add_cong) simp_all
      with arg_cong [OF i30, of "\<lambda> j. j mod 5"] have 5: "i mod 5 = (j mod 5 + 1) mod 5"
        by (simp add: mod_simps mod_mod_cancel [OF 5])
      
      from n *(2-)[unfolded ps i, simplified] have 
        "j \<in> {1,3,5,7,9,11,13,15,17,19,21,23,25,27,29} \<or> j \<in> {4,10,16,22,28} \<or> j \<in> {14,24}"
        (is "j \<in> ?j2 \<or> j \<in> ?j3 \<or> j \<in> ?j5")
        by simp presburger
      moreover
      {
        assume "j \<in> ?j2"
        hence "j mod 2 = 1" by auto
        with 2 have "i mod 2 = 0" by auto
        with i11 have "2 dvd i" "i \<noteq> 2" by auto 
        with *(1) have False unfolding prime_nat_iff by auto
      }
      moreover
      {
        assume "j \<in> ?j3"
        hence "j mod 3 = 1" by auto
        with 3 have "i mod 3 = 0" by auto
        with i11 have "3 dvd i" "i \<noteq> 3" by auto 
        with *(1) have False unfolding prime_nat_iff by auto
      }
      moreover
      {
        assume "j \<in> ?j5"
        hence "j mod 5 = 4" by auto
        with 5 have "i mod 5 = 0" by auto
        with i11 have "5 dvd i" "i \<noteq> 5" by auto 
        with *(1) have False unfolding prime_nat_iff by auto
      }
      ultimately have False by blast
    }
    thus ?thesis unfolding m ps by auto
  qed
qed


lemma prime_test_iterate2: assumes small: "\<And> j. 2 \<le> j \<Longrightarrow> j < (i :: nat) \<Longrightarrow> \<not> j dvd n"
  and odd: "odd n"
  and n: "n \<ge> 3"
  and i: "i \<ge> 3" "odd i"
  and mod: "\<not> i dvd n"
  and j: "2 \<le> j" "j < i + 2"
  shows "\<not> j dvd n"
proof 
  assume dvd: "j dvd n"
  with small[OF j(1)] have "j \<ge> i" by linarith
  with dvd mod have "j > i" by (cases "i = j", auto)
  with j have "j = Suc i" by simp
  with i have "even j" by auto
  with dvd j(1) have "2 dvd n" by (metis dvd_trans)
  with odd show False by auto
qed

lemma prime_divisor: assumes "j \<ge> 2" and "j dvd n" shows
  "\<exists> p :: nat. prime p \<and> p dvd j \<and> p dvd n"
proof -
  let ?pf = "prime_factors j"
  from assms have "j > 0" by auto
  from prime_factorization_nat[OF this]
  have "j = (\<Prod>p\<in>?pf. p ^ multiplicity p j)" by auto
  with \<open>j \<ge> 2\<close> have "?pf \<noteq> {}" by auto
  then obtain p where p: "p \<in> ?pf" by auto  
  hence pr: "prime p" by auto
  define rem where "rem = (\<Prod>p\<in>?pf - {p}. p ^ multiplicity p j)"
  from p have mult: "multiplicity p j \<noteq> 0"
    by (auto simp: prime_factors_multiplicity)
  have "finite ?pf" by simp
  have "j = (\<Prod>p\<in>?pf. p ^ multiplicity p j)" by fact
  also have "?pf = (insert p (?pf - {p}))" using p by auto
  also have "(\<Prod>p\<in>insert p (?pf - {p}). p ^ multiplicity p j) = 
    p ^ multiplicity p j * rem" unfolding rem_def
    by (subst prod.insert, auto)
  also have "\<dots> = p * (p ^ (multiplicity p j - 1) * rem)" using mult 
    by (cases "multiplicity p j", auto)
  finally have pj: "p dvd j" unfolding dvd_def by blast
  with \<open>j dvd n\<close> have "p dvd n" by (metis dvd_trans)
  with pj pr show ?thesis by blast
qed

lemma prime_nat_main: "ni = (n,i,is) \<Longrightarrow> i \<ge> 2 \<Longrightarrow> n \<ge> 2 \<Longrightarrow>
  (\<And> j. 2 \<le> j \<Longrightarrow> j < i \<Longrightarrow> \<not> (j dvd n)) \<Longrightarrow>
  (\<And> j. i \<le> j \<Longrightarrow> j < jj \<Longrightarrow> prime j \<Longrightarrow> j \<in> set is) \<Longrightarrow> i \<le> jj \<Longrightarrow>
  sorted is \<Longrightarrow> distinct is \<Longrightarrow> candidate_invariant jj \<Longrightarrow> set is \<subseteq> {i..<jj} \<Longrightarrow> 
  res = prime_nat_main n jj is \<Longrightarrow> 
  res = prime n"
proof (induct ni arbitrary: n i "is" jj res rule: wf_induct[OF 
    wf_measures[of "[\<lambda> (n,i,is). n - i, \<lambda> (n,i,is). if is = [] then 1 else 0]"]])
  case (1 ni n i "is" jj res)
  note res = 1(12)
  from 1(3-4) have i: "i \<ge> 2" and i2: "Suc i \<ge> 2" and n: "n \<ge> 2" by auto
  from 1(5) have dvd: "\<And> j. 2 \<le> j \<Longrightarrow> j < i \<Longrightarrow> \<not> j dvd n" .
  from 1(7) have ijj: "i \<le> jj" .
  note sort_dist = 1(8-9)
  have "is": "\<And> j. i \<le> j \<Longrightarrow> j < jj \<Longrightarrow> prime j \<Longrightarrow> j \<in> set is" by (rule 1(6))
  note simps = prime_nat_main.simps[of n jj "is"]
  note IH = 1(1)[rule_format, unfolded 1(2), OF _ refl]
  show ?case
  proof (cases "is")
    case Nil
    obtain jjj iis where can: "next_candidates jj = (jjj,iis)" by force
    from res[unfolded simps, unfolded Nil can split] have res: "res = prime_nat_main n jjj iis" by auto
    from next_candidates[OF can 1(10)] have can: 
      "sorted iis" "distinct iis" "candidate_invariant jjj" 
      "{i. prime i \<and> jj \<le> i \<and> i < jjj} \<subseteq> set iis" "set iis \<subseteq> {2..} \<inter> {jj..<jjj}"
      "iis \<noteq> []" "jj < jjj" by blast+
    from can ijj have "i \<le> jjj" by auto
    note IH = IH[OF _ i n dvd _ this can(1-3) _ res]
    show ?thesis
    proof (rule IH, force simp: Nil can(6))
      fix x
      assume ix: "i \<le> x" and xj: "x < jjj" and px: "prime x"
      from "is"[OF ix _ px] Nil have jx: "jj \<le> x" by force
      with can(4) xj px show "x \<in> set iis" by auto
    qed (insert can(5) ijj, auto)
  next
    case (Cons i' iis)
    with res[unfolded simps]
    have res: "res = (if i' dvd n then n \<le> i' else if i' * i' \<le> n then prime_nat_main n jj iis else True)" 
      by simp
    from 1(11) Cons have iis: "set iis \<subseteq> {i..<jj}" and i': "i \<le> i'" "i' < jj" "Suc i' \<le> jj" by auto
    from sort_dist have sd_iis: "sorted iis" "distinct iis" and "i' \<notin> set iis" by(auto simp: Cons)
    from sort_dist(1) have "set iis \<subseteq> {i'..}" by(auto simp: Cons)
    with iis have "set iis \<subseteq> {i'..<jj}" by force
    with \<open>i' \<notin> set iis\<close>  have iis: "set iis \<subseteq> {Suc i'..<jj}"
      by (auto, case_tac "x = i'", auto)
    {
      fix j
      assume j: "2 \<le> j" "j < i'"
      have "\<not> j dvd n"
      proof
        assume "j dvd n"
        from prime_divisor[OF j(1) this] obtain p where 
          p: "prime p" "p dvd j" "p dvd n" by auto
        have pj: "p \<le> j"
          by (rule dvd_imp_le[OF p(2)], insert j, auto)
        have p2: "2 \<le> p" using p(1) by (rule prime_ge_2_nat)
        from dvd[OF p2] p(3) have pi: "p \<ge> i" by force
        from pj j(2) i' "is"[OF pi _ p(1)] have "p \<in> set is" by auto
        with \<open>sorted is\<close> have "i' \<le> p" by(auto simp: Cons)
        with pj j(2) show False by arith
      qed
    } note dvd = this
    from i' i have i'2: "2 \<le> Suc i'" by auto
    note IH = IH[OF _ i'2 n _ _ i'(3) sd_iis 1(10) iis]
    show ?thesis
    proof (cases "i' dvd n")
      case False note dvdi = this
      {
        fix j
        assume j: "2 \<le> j" "j < Suc i'"
        have "\<not> j dvd n"
        proof (cases "j = i'")
          case False
          with j have "j < i'" by auto
          from dvd[OF j(1) this] show ?thesis .
        qed (insert False, auto)
      } note dvds = this
      show ?thesis
      proof (cases "i' * i' \<le> n")
        case True note iin = this
        with res False have res: "res = prime_nat_main n jj iis" by auto
        from iin have i_n: "i' < n"
          using dvd dvdi n nat_neq_iff dvd_refl by blast
        {
          fix x
          assume "Suc i' \<le> x" "x < jj" "prime x"
          hence "i \<le> x" "x < jj" "prime x" using i' by auto
          from "is"[OF this] have "x \<in> set is" . 
          with \<open>Suc i' \<le> x\<close> have "x \<in> set iis" unfolding Cons by auto
        } note iis = this
        show ?thesis 
          by (rule IH[OF _ dvds iis res], insert i_n i', auto)
      next
        case False
        with res dvdi have res: "res = True" by auto
        have n: "prime n" 
          by (rule prime_sqrtI[OF n dvd False])
        thus ?thesis unfolding res by auto
      qed
    next
      case True
      have "i' \<ge> 2" using i i' by auto
      from \<open>i' dvd n\<close> obtain k where "n = i' * k" ..
      with n have "k \<noteq> 0" by (cases "k = 0", auto)
      with \<open>n = i' * k\<close> have *: "i' < n \<or> i' = n"
        by auto
      with True res have "res \<longleftrightarrow> i' = n"
        by auto
      also have "\<dots> = prime n"
      using * proof
        assume "i' < n"
        with \<open>i' \<ge> 2\<close> \<open>i' dvd n\<close> have "\<not> prime n"
          by (auto simp add: prime_nat_iff)
        with \<open>i' < n\<close> show ?thesis
          by auto
      next
        assume "i' = n"
        with dvd n have "prime n"
          by (simp add: prime_nat_iff')
        with \<open>i' = n\<close> show ?thesis 
          by auto
      qed
      finally show ?thesis .
    qed
  qed
qed

lemma prime_factorization_nat_main: "ni = (n,i,is) \<Longrightarrow> i \<ge> 2 \<Longrightarrow> n \<ge> 2 \<Longrightarrow>
  (\<And> j. 2 \<le> j \<Longrightarrow> j < i \<Longrightarrow> \<not> (j dvd n)) \<Longrightarrow> 
  (\<And> j. i \<le> j \<Longrightarrow> j < jj \<Longrightarrow> prime j \<Longrightarrow> j \<in> set is) \<Longrightarrow> i \<le> jj \<Longrightarrow>
  sorted is \<Longrightarrow> distinct is \<Longrightarrow> candidate_invariant jj \<Longrightarrow> set is \<subseteq> {i..<jj} \<Longrightarrow> 
  res = prime_factorization_nat_main n jj is ps \<Longrightarrow> 
  \<exists> qs. res = qs @ ps \<and> Ball (set qs) prime \<and> n = prod_list qs"
proof (induct ni arbitrary: n i "is" jj res ps rule: wf_induct[OF 
  wf_measures[of "[\<lambda> (n,i,is). n - i, \<lambda> (n,i,is). if is = [] then 1 else 0]"]])
  case (1 ni n i "is" jj res ps)
  note res = 1(12)
  from 1(3-4) have i: "i \<ge> 2" and i2: "Suc i \<ge> 2" and n: "n \<ge> 2" by auto
  from 1(5) have dvd: "\<And> j. 2 \<le> j \<Longrightarrow> j < i \<Longrightarrow> \<not> j dvd n" .
  from 1(7) have ijj: "i \<le> jj" .
  note sort_dist = 1(8-9)
  have "is": "\<And> j. i \<le> j \<Longrightarrow> j < jj \<Longrightarrow> prime j \<Longrightarrow> j \<in> set is" by (rule 1(6))
  note simps = prime_factorization_nat_main.simps[of n jj "is"]
  note IH = 1(1)[rule_format, unfolded 1(2), OF _ refl]
  show ?case
  proof (cases "is")
    case Nil
    obtain jjj iis where can: "next_candidates jj = (jjj,iis)" by force
    from res[unfolded simps, unfolded Nil can split] have res: "res = prime_factorization_nat_main n jjj iis ps" by auto
    from next_candidates[OF can 1(10)] have can: 
      "sorted iis" "distinct iis" "candidate_invariant jjj" 
      "{i. prime i \<and> jj \<le> i \<and> i < jjj} \<subseteq> set iis" "set iis \<subseteq> {2..} \<inter> {jj..<jjj}"
      "iis \<noteq> []" "jj < jjj" by blast+
    from can ijj have "i \<le> jjj" by auto
    note IH = IH[OF _ i n dvd _ this can(1-3) _ res]
    show ?thesis
    proof (rule IH, force simp: Nil can(6))
      fix x
      assume ix: "i \<le> x" and xj: "x < jjj" and px: "prime x"
      from "is"[OF ix _ px] Nil have jx: "jj \<le> x" by force
      with can(4) xj px show "x \<in> set iis" by auto
    qed (insert can(5) ijj, auto)
  next
    case (Cons i' iis)
    obtain n' m where dm: "Divides.divmod_nat n i' = (n',m)" by force
    hence n': "n' = n div i'" and m: "m = n mod i'" by (auto simp: divmod_nat_def)
    have m: "(m = 0) = (i' dvd n)" unfolding m by auto
    from Cons res[unfolded simps] dm m n'
    have res: "res = (
       if i' dvd n then case remove_prime_factor i' (n div i') (i' # ps) of
            (n', ps') \<Rightarrow> if n' = 1 then ps' else prime_factorization_nat_main n' jj iis ps'
       else if i' * i' \<le> n then prime_factorization_nat_main n jj iis ps else n # ps)" 
      by simp
    from 1(11) i Cons have iis: "set iis \<subseteq> {i..<jj}" and i': "i \<le> i'" "i' < jj" "Suc i' \<le> jj" "i' > 1" by auto
    from sort_dist have sd_iis: "sorted iis" "distinct iis" and "i' \<notin> set iis" by(auto simp: Cons)
    from sort_dist(1) Cons have "set iis \<subseteq> {i'..}" by(auto)
    with iis have "set iis \<subseteq> {i'..<jj}" by force
    with \<open>i' \<notin> set iis\<close>  have iis: "set iis \<subseteq> {Suc i'..<jj}"
      by (auto, case_tac "x = i'", auto)
    {
      fix j
      assume j: "2 \<le> j" "j < i'"
      have "\<not> j dvd n"
      proof
        assume "j dvd n"
        from prime_divisor[OF j(1) this] obtain p where 
          p: "prime p" "p dvd j" "p dvd n" by auto
        have pj: "p \<le> j"
          by (rule dvd_imp_le[OF p(2)], insert j, auto)
        have p2: "2 \<le> p" using p(1) by (rule prime_ge_2_nat)
        from dvd[OF p2] p(3) have pi: "p \<ge> i" by force
        from pj j(2) i' "is"[OF pi _ p(1)] have "p \<in> set is" by auto
        with \<open>sorted is\<close> have "i' \<le> p" by (auto simp: Cons)
        with pj j(2) show False by arith
      qed
    } note dvd = this
    from i' i have i'2: "2 \<le> Suc i'" by auto
    note IH = IH[OF _ i'2 _ _ _ i'(3) sd_iis 1(10) iis]
    {
      fix x
      assume "Suc i' \<le> x" "x < jj" "prime x"
      hence "i \<le> x" "x < jj" "prime x" using i' by auto
      from "is"[OF this] have "x \<in> set is" . 
      with \<open>Suc i' \<le> x\<close> have "x \<in> set iis" unfolding Cons by auto
    } note iis = this
    show ?thesis
    proof (cases "i' dvd n")
      case False note dvdi = this
      {
        fix j
        assume j: "2 \<le> j" "j < Suc i'"
        have "\<not> j dvd n"
        proof (cases "j = i'")
          case False
          with j have "j < i'" by auto
          from dvd[OF j(1) this] show ?thesis .
        qed (insert False, auto)
      } note dvds = this
      show ?thesis
      proof (cases "i' * i' \<le> n")
        case True note iin = this
        with res False have res: "res = prime_factorization_nat_main n jj iis ps" by auto
        from iin have i_n: "i' < n" using dvd dvdi n nat_neq_iff dvd_refl by blast 
        show ?thesis 
          by (rule IH[OF _ n dvds iis res], insert i_n i', auto)
      next
        case False
        with res dvdi have res: "res = n # ps" by auto
        have n: "prime n" 
          by (rule prime_sqrtI[OF n dvd False])
        thus ?thesis unfolding res by auto
      qed    
    next
      case True note i_n = this
      obtain n'' qs where rp: "remove_prime_factor i' (n div i') (i' # ps) = (n'',qs)" by force
      with res True 
      have res: "res = (if n'' = 1 then qs else prime_factorization_nat_main n'' jj iis qs)" by auto
      have pi: "prime i'" unfolding prime_nat_iff
      proof (intro conjI allI impI)
        show "1 < i'" using i' i by auto
        fix j
        assume ji: "j dvd i'"
        with i' i have j0: "j \<noteq> 0" by (cases "j = 0", auto)
        from ji i_n have jn: "j dvd n" by (metis dvd_trans)
        with dvd[of j] have j: "2 > j \<or> j \<ge> i'" by linarith
        from ji \<open>1 < i'\<close> have "j \<le> i'" unfolding dvd_def 
          by (simp add: dvd_imp_le ji)
        with j j0 show "j = 1 \<or> j = i'" by linarith
      qed
      from True n' have id: "n = n' * i'" by auto
      from n id have "n' \<noteq> 0" by (cases "n = 0", auto)
      with id have "i' \<le> n" by auto
      from remove_prime_factor[OF rp[folded n'] \<open>1 < i'\<close> \<open>n' \<noteq> 0\<close>] obtain rs
        where qs: "qs = rs @ i' # ps" and n': "n' = n'' * prod_list rs" and i_n'': "\<not> i' dvd n''" 
        and rs: "set rs \<subseteq> {i'}" by auto
      {
        fix j
        assume "j dvd n''"
        hence "j dvd n" unfolding id n' by auto
      } note dvd' = this
      show ?thesis
      proof (cases "n'' = 1")
        case False
        with res have res: "res = prime_factorization_nat_main n'' jj iis qs" 
          by simp
        from i i' have "i' \<ge> 2" by simp
        from False n' \<open>n' \<noteq> 0\<close> have n2: "n'' \<ge> 2" by (cases "n'' = 0"; auto)
        have lrs: "prod_list rs \<noteq> 0" using n' \<open>n' \<noteq> 0\<close> by (cases "prod_list rs = 0", auto)
        with \<open>i' \<ge> 2\<close> have "prod_list rs * i' \<ge> 2" by (cases "prod_list rs", auto)
        hence nn'': "n > n''" unfolding id n' using n2 by simp
        have "i' \<noteq> n" unfolding id n' using pi False by fastforce
        with \<open>i' \<le> n\<close> i' have "n > i" by auto
        with nn'' i i' have less: "n - i > n'' - Suc i'" by simp
        {
          fix j
          assume 2: "2 \<le> j" and ji: "j < Suc i'" 
          have "\<not> j dvd n''" 
          proof (cases "j = i'")
            case False
            with ji have "j < i'" by auto
            from dvd' dvd[OF 2 this] show ?thesis by blast
          qed (insert i_n'', auto)
        }
        from IH[OF _ n2 this iis res] less obtain ss where 
          res: "res = ss @ qs \<and> Ball (set ss) prime \<and> n'' = prod_list ss" by auto
        thus ?thesis unfolding id n' qs using pi rs by auto
      next
        case True
        with res have res: "res = qs" by auto
        show ?thesis unfolding id n' res qs True using rs \<open>prime i'\<close>
          by (intro exI[of _ "rs @ [i']"], auto)
      qed
    qed
  qed
qed

lemma prime_nat[simp]: "prime_nat n = prime n"
proof (cases "n < 2")
  case True
  thus ?thesis unfolding prime_nat_def prime_nat_iff by auto
next
  case False
  hence n: "n \<ge> 2" by auto
  obtain jj "is" where can: "next_candidates 0 = (jj,is)" by force
  from next_candidates[OF this candidate_invariant_0]
  have cann: "sorted is" "distinct is" "candidate_invariant jj" 
    "{i. prime i \<and> 0 \<le> i \<and> i < jj} \<subseteq> set is"
    "set is \<subseteq> {2..} \<inter> {0..<jj}" "distinct is" "is \<noteq> []" by auto  
  from cann have sub: "set is \<subseteq> {2..<jj}" by force
  with \<open>is \<noteq> []\<close> have jj: "jj \<ge> 2" by (cases "is", auto)
  from n can have res: "prime_nat n = prime_nat_main n jj is"
    unfolding prime_nat_def by auto
  show ?thesis using prime_nat_main[OF refl le_refl n _ _ jj cann(1-3) sub res] cann(4) by auto
qed

lemma prime_factorization_nat: fixes n :: nat
  defines "pf \<equiv> prime_factorization_nat n"
  shows "Ball (set pf) prime"
  and "n \<noteq> 0 \<Longrightarrow> prod_list pf = n"
  and "n = 0 \<Longrightarrow> pf = []"
proof -
  note pf = pf_def[unfolded prime_factorization_nat_def]
  have "Ball (set pf) prime \<and> (n \<noteq> 0 \<longrightarrow> prod_list pf = n) \<and> (n = 0 \<longrightarrow> pf = [])"
  proof (cases "n < 2")
    case True
    thus ?thesis using pf by auto
  next
    case False
    hence n: "n \<ge> 2" by auto
    obtain jj "is" where can: "next_candidates 0 = (jj,is)" by force
    from next_candidates[OF this candidate_invariant_0]
    have cann: "sorted is" "distinct is" "candidate_invariant jj" 
      "{i. prime i \<and> 0 \<le> i \<and> i < jj} \<subseteq> set is"
      "set is \<subseteq> {2..} \<inter> {0..<jj}" "distinct is" "is \<noteq> []" by auto  
    from cann have sub: "set is \<subseteq> {2..<jj}" by force
    with \<open>is \<noteq> []\<close> have jj: "jj \<ge> 2" by (cases "is", auto)
    let ?pfm = "prime_factorization_nat_main n jj is []"
    from pf[unfolded can] False
    have res: "pf = rev ?pfm" by simp
    from prime_factorization_nat_main[OF refl le_refl n _ _ jj cann(1-3) sub refl, of Nil] cann(4)
    have "Ball (set ?pfm) prime" "n = prod_list ?pfm" by auto
    thus ?thesis unfolding res using n by auto
  qed
  thus "Ball (set pf) prime" "n \<noteq> 0 \<Longrightarrow> prod_list pf = n" "n = 0 \<Longrightarrow> pf = []" by auto
qed

lemma prod_mset_multiset_prime_factorization_nat [simp]: 
  "(x::nat) \<noteq> 0 \<Longrightarrow> prod_mset (prime_factorization x) = x"
  by simp

(* TODO Move *)
lemma prime_factorization_unique'':
  assumes "\<And>p. p \<in># A \<Longrightarrow> prime p"
  assumes "prod_mset A = normalize x"
  shows   "prime_factorization x = A"
proof -
  have "prod_mset A \<noteq> 0" by (auto dest: assms(1))
  with assms(2) have "x \<noteq> 0" by simp
  hence "prod_mset (prime_factorization x) = prod_mset A" 
    by (simp add: assms prod_mset_prime_factorization)
  with assms show ?thesis 
    by (intro prime_factorization_unique') auto
qed

lemma multiset_prime_factorization_nat_correct:
  "prime_factorization n = mset (prime_factorization_nat n)"
proof -
  note pf = prime_factorization_nat[of n]
  show ?thesis
  proof (cases "n = 0")
    case True
    thus ?thesis using pf(3) by simp
  next
    case False
    note pf = pf(1) pf(2)[OF False]
    show ?thesis
    proof (rule prime_factorization_unique'')
      show "prime p" if "p \<in># mset (prime_factorization_nat n)" for p
        using pf(1) that by simp
      let ?l = "\<Prod>i\<in>#prime_factorization n. i"
      let ?r = "\<Prod>i\<in>#mset (prime_factorization_nat n). i"
      show "prod_mset (mset (prime_factorization_nat n)) = normalize n"
        by (simp add: pf(2) prod_mset_prod_list)
    qed
  qed
qed

lemma multiset_prime_factorization_code[code_unfold]: 
  "prime_factorization = (\<lambda>n. mset (prime_factorization_nat n))"
  by (intro ext multiset_prime_factorization_nat_correct)

lemma divisors_nat: 
  "n \<noteq> 0 \<Longrightarrow> set (divisors_nat n) = {p. p dvd n}" "distinct (divisors_nat n)" "divisors_nat 0 = []"
proof -
  show "distinct (divisors_nat n)" "divisors_nat 0 = []" unfolding divisors_nat_def by auto
  assume n: "n \<noteq> 0"
  from n have "n > 0" by auto
  {
    fix x    
    have "(x dvd n) = (x \<noteq> 0 \<and> (\<forall>p. multiplicity p x \<le> multiplicity p n))"
    proof (cases "x = 0")
      case False
      with \<open>n > 0\<close> show ?thesis by (auto simp: dvd_multiplicity_eq)
    next
      case True
      with n show ?thesis by auto
    qed
  } note dvd = this
  let ?dn = "set (divisors_nat n)"
  let ?mf = "\<lambda> (n :: nat). prime_factorization n"
  have "?dn = prod_list ` set (subseqs (prime_factorization_nat n))" unfolding divisors_nat_def
    using n by auto
  also have "\<dots> = prod_mset ` mset ` set (subseqs (prime_factorization_nat n))"
    by (force simp: prod_mset_prod_list)
  also have "mset ` set (subseqs (prime_factorization_nat n))
    = { ps. ps \<subseteq># mset (prime_factorization_nat n)}" 
    unfolding multiset_of_subseqs by simp
  also have "\<dots> = { ps. ps \<subseteq># ?mf n}"
    thm multiset_prime_factorization_code[symmetric]
    unfolding multiset_prime_factorization_nat_correct[symmetric] by auto
  also have "prod_mset ` \<dots> = {p. p dvd n}" (is "?l = ?r")
  proof -
    {
      fix x
      assume "x dvd n"
      from this[unfolded dvd] have x: "x \<noteq> 0" by auto
      from \<open>x dvd n\<close> \<open>x \<noteq> 0\<close> \<open>n \<noteq> 0\<close> have sub: "?mf x \<subseteq># ?mf n"
        by (subst prime_factorization_subset_iff_dvd) auto
      have "prod_mset (?mf x) = x" using x
        by (simp add: prime_factorization_nat)
      hence "x \<in> ?l" using sub by force
    } 
    moreover
    {
      fix x
      assume "x \<in> ?l"
      then obtain ps where x: "x = prod_mset ps" and sub: "ps \<subseteq># ?mf n" by auto
      have "x dvd n" using prod_mset_subset_imp_dvd[OF sub] n x by simp
    }
    ultimately show ?thesis by blast
  qed
  finally show "set (divisors_nat n) = {p. p dvd n}" .
qed

lemma divisors_int_pos: "x \<noteq> 0 \<Longrightarrow> set (divisors_int_pos x) = {i. i dvd x \<and> i > 0}" "distinct (divisors_int_pos x)"
  "divisors_int_pos 0 = []"
proof -
  show "divisors_int_pos 0 = []" by code_simp
  show "distinct (divisors_int_pos x)" 
    unfolding divisors_int_pos_def using divisors_nat(2)[of "nat (abs x)"]
    by (simp add: distinct_map inj_on_def)
  assume x: "x \<noteq> 0"
  let ?x = "nat (abs x)"
  from x have xx: "?x \<noteq> 0" by auto
  from x have 0: "\<And> y. y dvd x \<Longrightarrow> y \<noteq> 0" by auto
  have id: "int ` {p. int p dvd x} = {i. i dvd x \<and> 0 < i}" (is "?l = ?r")
  proof -
    {
      fix y
      assume "y \<in> ?l"
      then obtain p where y: "y = int p" and dvd: "int p dvd x" by auto
      have "y \<in> ?r" unfolding y using dvd 0[OF dvd] by auto
    }
    moreover
    {
      fix y
      assume "y \<in> ?r"
      hence dvd: "y dvd x" and y0: "y > 0" by auto
      define n where "n = nat y"
      from y0 have y: "y = int n" unfolding n_def by auto
      with dvd have "y \<in> ?l" by auto
    }
    ultimately show ?thesis by blast
  qed
  from xx show "set (divisors_int_pos x) = {i. i dvd x \<and> i > 0}"
    by (simp add: divisors_int_pos_def divisors_nat id) 
qed

lemma divisors_int: "x \<noteq> 0 \<Longrightarrow> set (divisors_int x) = {i. i dvd x}" "distinct (divisors_int x)"
  "divisors_int 0 = []"
proof -
  show "divisors_int 0 = []" by code_simp
  show "distinct (divisors_int x)"
  proof (cases "x = 0")
    case True 
    show ?thesis unfolding True by code_simp
  next
    case False
    from divisors_int_pos(1)[OF False] divisors_int_pos(2)
    show ?thesis unfolding divisors_int_def Let_def distinct_append distinct_map inj_on_def by auto
  qed
  assume x: "x \<noteq> 0"
  show "set (divisors_int x) = {i. i dvd x}"
  unfolding divisors_int_def Let_def set_append set_map divisors_int_pos(1)[OF x] using x
  by auto (metis (no_types, lifting) dvd_mult_div_cancel image_eqI linorder_neqE_linordered_idom 
  mem_Collect_eq minus_dvd_iff minus_minus mult_zero_left neg_less_0_iff_less)
qed

definition divisors_fun :: "('a \<Rightarrow> ('a :: {comm_monoid_mult,zero}) list) \<Rightarrow> bool" where
  "divisors_fun df \<equiv> (\<forall> x. x \<noteq> 0 \<longrightarrow> set (df x) = { d. d dvd x }) \<and> (\<forall> x. distinct (df x))"

lemma divisors_funD: "divisors_fun df \<Longrightarrow> x \<noteq> 0 \<Longrightarrow> d dvd x \<Longrightarrow> d \<in> set (df x)" 
  unfolding divisors_fun_def by auto

definition divisors_pos_fun :: "('a \<Rightarrow> ('a :: {comm_monoid_mult,zero,ord}) list) \<Rightarrow> bool" where
  "divisors_pos_fun df \<equiv> (\<forall> x. x \<noteq> 0 \<longrightarrow> set (df x) = { d. d dvd x \<and> d > 0}) \<and> (\<forall> x. distinct (df x))"

lemma divisors_pos_funD: "divisors_pos_fun df \<Longrightarrow> x \<noteq> 0 \<Longrightarrow> d dvd x \<Longrightarrow> d > 0 \<Longrightarrow> d \<in> set (df x)" 
  unfolding divisors_pos_fun_def by auto

lemma divisors_fun_nat: "divisors_fun divisors_nat"
  unfolding divisors_fun_def using divisors_nat by auto

lemma divisors_fun_int: "divisors_fun divisors_int"
  unfolding divisors_fun_def using divisors_int by auto

lemma divisors_pos_fun_int: "divisors_pos_fun divisors_int_pos"
  unfolding divisors_pos_fun_def using divisors_int_pos by auto

end
