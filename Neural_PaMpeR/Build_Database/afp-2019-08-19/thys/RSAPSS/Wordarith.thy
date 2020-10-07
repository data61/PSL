(*  Title:      RSAPSS/Wordarith.thy
    Author:     Christina Lindenberg, Kai Wirt, Technische Universität Darmstadt
    Copyright:  2005 - Technische Universität Darmstadt
*)


section "Extensions to the Word theory required for PSS"

theory Wordarith
imports WordOperations "HOL-Computational_Algebra.Primes"
begin

definition
  nat_to_bv_length :: "nat \<Rightarrow> nat \<Rightarrow>  bv" where
    (* nat_to_bv_length converts nat (if 0 \<le> nat \<and> nat < 2^nat) nato a bit string of length l *)
  nat_to_bv_length:
  "nat_to_bv_length n l = (if length(nat_to_bv n) \<le> l then bv_extend l \<zero> (nat_to_bv n) else [])"


lemma length_nat_to_bv_length:
  "nat_to_bv_length x y \<noteq> [] \<Longrightarrow> length (nat_to_bv_length x y) = y"
  unfolding nat_to_bv_length by auto

lemma bv_to_nat_nat_to_bv_length:
  "nat_to_bv_length x y \<noteq> [] \<Longrightarrow> bv_to_nat (nat_to_bv_length x y) = x"
  unfolding nat_to_bv_length by auto


definition
  roundup :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  roundup: "roundup x y = (if (x mod y = 0) then (x div y) else (x div y) + 1)"


lemma rnddvd: "b dvd a \<Longrightarrow> roundup a b * b = a"
  by (auto simp add: roundup dvd_eq_mod_eq_0)

lemma bv_to_nat_zero_prepend: "bv_to_nat a = bv_to_nat (\<zero>#a)"
  by auto

primrec remzero:: "bv \<Rightarrow> bv" where
  "remzero [] = []"
| "remzero (a#b) = (if a = \<one> then (a#b) else remzero b)"

lemma remzeroeq: "bv_to_nat a = bv_to_nat (remzero a)"
proof (induct a)
  show "bv_to_nat [] = bv_to_nat (remzero [])"
    by simp
next
  case (Cons a1 a2)
  show "bv_to_nat a2 = bv_to_nat (remzero a2) \<Longrightarrow>
       bv_to_nat (a1 # a2) = bv_to_nat (remzero (a1 # a2))"
  proof (cases a1)
    assume a: "a1=\<zero>" then have "bv_to_nat (a1#a2) = bv_to_nat a2"
      using bv_to_nat_zero_prepend by simp
    moreover have "remzero (a1 # a2) = remzero a2" using a by simp
    ultimately show ?thesis using Cons by simp
  next
    assume "a1=\<one>" then show ?thesis by simp
  qed
qed

lemma len_nat_to_bv_pos: assumes x: "1 < a" shows "0< length (nat_to_bv a)"
proof (auto)
  assume b: "nat_to_bv a = []"
  have a: "bv_to_nat [] = 0" by simp
  have c: "bv_to_nat (nat_to_bv a) = 0" using a and b by simp
  from x have d: "bv_to_nat (nat_to_bv a) = a" by simp
  from d and c have "a=0" by simp
  then show False using x by simp
qed

lemma remzero_replicate: "remzero ((replicate n \<zero>)@l) = remzero l"
by (induct n, auto)

lemma length_bvxor_bound: "a <= length l \<Longrightarrow> a <= length (bvxor l l2)"
proof (induct a)
  case 0
  then show ?case by simp
next
  case (Suc a)
  have a: "Suc a \<le> length l" by fact
  with Suc.hyps have b: "a \<le> length (bvxor l l2)" by simp
  show "Suc a \<le> length (bvxor l l2)"
  proof cases
    assume c: "a = length (bvxor l l2)"
    show "Suc a \<le> length (bvxor l l2)"
    proof (simp add: bvxor)
      have "length l <= max (length l) (length l2)" by simp
      then show "Suc a \<le> max (length l) (length l2)" using a by simp
    qed
  next
    assume "a \<noteq> length (bvxor l l2)"
    then have "a < length (bvxor l l2)" using b by simp
    then show ?thesis by simp
  qed
qed

lemma nat_to_bv_helper_legacy_induct:
  "(\<And>n. n \<noteq> (0::nat) \<longrightarrow> P (n div 2) \<Longrightarrow> P n) \<Longrightarrow> P x"
unfolding atomize_imp[symmetric]
by (induction_schema, simp, lexicographic_order)

lemma len_lower_bound:
  assumes "0 < n"
  shows "2^(length (nat_to_bv n) - Suc 0) \<le> n"
proof (cases "1<n")
  assume l1: "1<n"
  then show ?thesis
  proof (simp add: nat_to_bv_def, induct n rule: nat_to_bv_helper_legacy_induct, auto)
    fix n
    assume a: "Suc 0 < (n::nat)" and b: "~Suc 0<n div 2"
    then have "n=2 \<or> n=3"
    proof (cases "n<=3")
      assume "n<=3" and "Suc 0<n"
      then show "n=2 \<or> n=3" by auto
    next
      assume "~n<=3" then have "3<n" by simp
      then have "1 < n div 2" by arith
      then show "n=2 \<or> n=3" using b by simp
    qed
    then show "2 ^ (length (nat_to_bv_helper n []) - Suc 0) \<le> n"
    proof (cases "n=2")
      assume a: "n=2" then have "nat_to_bv_helper n [] = [\<one>, \<zero>]"
      proof -
        have "nat_to_bv_helper n [] = nat_to_bv n" using b by (simp add: nat_to_bv_def)
        then show ?thesis using a by (simp add: nat_to_bv_non0)
      qed
      then show "2 ^ (length (nat_to_bv_helper n []) - Suc 0) \<le> n" using a by simp
    next
      assume "n=2 \<or> n=3" and "n~=2"
      then have a: "n=3" by simp
      then have "nat_to_bv_helper n [] = [\<one>, \<one>]"
      proof -
        have "nat_to_bv_helper n [] = nat_to_bv n" using a by (simp add: nat_to_bv_def)
        then show ?thesis using a by (simp add: nat_to_bv_non0)
      qed
      then show "2^(length (nat_to_bv_helper n []) - Suc 0) <=n" using a by simp
    qed
  next
    fix n
    assume a: "Suc 0<n" and
      b: "2 ^ (length (nat_to_bv_helper (n div 2) []) - Suc 0) \<le> n div 2"
    have "(2::nat) ^ (length (nat_to_bv_helper n []) - Suc 0) =
      2^(length (nat_to_bv_helper (n div 2) []) + 1 - Suc 0)"
    proof -
      have "length (nat_to_bv n) = length (nat_to_bv (n div 2)) + 1"
        using a by (simp add: nat_to_bv_non0)
      then show ?thesis by (simp add: nat_to_bv_def)
    qed
    moreover have "(2::nat)^(length (nat_to_bv_helper (n div 2) []) + 1 - Suc 0) =
      2^(length (nat_to_bv_helper (n div 2) []) - Suc 0) * 2"
    proof auto
      have "(2::nat)^(length (nat_to_bv_helper (n div 2) []) -Suc 0)*2 =
        2^(length (nat_to_bv_helper (n div 2) []) - Suc 0 + 1)" by simp
      moreover have "(2::nat)^(length (nat_to_bv_helper (n div 2) []) - Suc 0 + 1) =
        2^(length (nat_to_bv_helper (n div 2) []))"
      proof -
        have "0<n div 2" using a by arith
        then have "0<length (nat_to_bv (n div 2))" by (simp add: nat_to_bv_non0)
        then have "0< length (nat_to_bv_helper (n div 2) [])" using a by (simp add: nat_to_bv_def)
        then show ?thesis by simp
      qed
      ultimately show "(2::nat) ^ length (nat_to_bv_helper (n div 2) []) =
        2 ^ (length (nat_to_bv_helper (n div 2) []) - Suc 0) * 2" by simp
    qed
    ultimately show  "2 ^ (length (nat_to_bv_helper n []) - Suc 0) <= n"
      using b by (simp add: nat_to_bv_def) arith
  qed
next
  assume c: "~1<n"
  show ?thesis
  proof (cases "n=1")
    assume a: "n=1" then have "nat_to_bv n = [\<one>]" by (simp add: nat_to_bv_non0)
    then show "2^(length (nat_to_bv n) - Suc 0) <= n" using a by simp
  next
    assume "n~=1"
    with \<open>0 < n\<close> show "2^(length (nat_to_bv n) - Suc 0) <= n" using c by simp
  qed
qed

lemma length_lower: assumes a: "length a < length b" and b: "(hd b) ~= \<zero>" shows "bv_to_nat a < bv_to_nat b"
proof -
  have ha: "bv_to_nat a < 2^length a" by (simp add: bv_to_nat_upper_range)
  have "b ~= []" using a by auto
  then have "b=(hd b)#(tl b)" by simp
  then have "bv_to_nat b = bitval (hd b) * 2^(length (tl b)) + bv_to_nat (tl b)" using bv_to_nat_helper[of "hd b" "tl b"] by simp
  moreover have "bitval (hd b) = 1"
  proof (cases "hd b")
    assume "hd b = \<zero> "
    then show  "bitval (hd b) = 1" using b by simp
  next
    assume "hd b = \<one>"
    then show "bitval (hd b) = 1" by simp
  qed
  ultimately have hb: "2^length (tl b) <= bv_to_nat b" by simp
  have "2^(length a) <= (2::nat)^length (tl b)" using a by auto
  then show ?thesis using hb and ha by arith
qed

lemma nat_to_bv_non_empty: assumes a: "0<n" shows "nat_to_bv n ~= []"
proof -
  from nat_to_bv_non0[of n] have "\<exists>x. nat_to_bv n = x@[if n mod 2 = 0 then \<zero> else \<one>]" using a by simp
  then show ?thesis by auto
qed

lemma hd_append: "x ~= [] \<Longrightarrow> hd (x @ xs) = hd x"
  by (induct x) auto

lemma hd_one: "0<n \<Longrightarrow> hd (nat_to_bv_helper n []) = \<one>"
proof (induct n rule: nat_to_bv_helper_legacy_induct)
  fix n
  assume *: "n \<noteq> 0 \<longrightarrow> 0 < n div 2 \<longrightarrow> hd (nat_to_bv_helper (n div 2) []) = \<one>"
    and "0 < n"
  show "hd (nat_to_bv_helper n []) = \<one>"
  proof (cases "1<n")
    assume a: "1<n"
    with * have b: "0 < n div 2 \<longrightarrow> hd (nat_to_bv_helper (n div 2) []) = \<one>" by simp
    from a have c: "0<n div 2" by arith
    then have d: "hd (nat_to_bv_helper (n div 2) []) = \<one>" using b by simp
    also from a have "0<n" by simp
    then have "hd (nat_to_bv_helper n []) =
        hd (nat_to_bv (n div 2) @ [if n mod 2 = 0 then \<zero> else \<one>])"
      using nat_to_bv_def and nat_to_bv_non0[of n] by auto
    then have "hd (nat_to_bv_helper n []) =
        hd (nat_to_bv (n div 2))"
      using nat_to_bv_non0[of "n div 2"] and c and
        nat_to_bv_non_empty[of "n div 2"] and hd_append[of " nat_to_bv (n div 2)"] by auto
    then have "hd (nat_to_bv_helper n []) = hd (nat_to_bv_helper (n div 2) [])"
      using nat_to_bv_def by simp
    then show "hd (nat_to_bv_helper n []) = \<one>" using b and c by simp
  next
    assume "~1 < n" with \<open>0<n\<close> have c: "n=1" by simp
    have "nat_to_bv_helper 1 [] = [\<one>]" by (simp add: nat_to_bv_helper.simps)
    then show "hd (nat_to_bv_helper n []) = \<one>" using c by simp
  qed
qed

lemma prime_hd_non_zero: 
  fixes p::nat assumes a: "prime p" and b: "prime q" shows "hd (nat_to_bv (p*q)) ~= \<zero>"
proof -
  have "0 < p*q"
    by (metis a b mult_is_0 neq0_conv not_prime_0) 
  then show ?thesis using hd_one[of "p*q"] and nat_to_bv_def by auto
qed

lemma primerew: fixes p::nat shows  "\<lbrakk>m dvd p; m~=1; m~=p\<rbrakk> \<Longrightarrow> ~ prime p"
  by (auto simp add: prime_nat_iff)


lemma two_dvd_exp: "0<x \<Longrightarrow> (2::nat) dvd 2^x"
  by (induct x) auto

lemma exp_prod1: "\<lbrakk>1<b;2^x=2*(b::nat)\<rbrakk> \<Longrightarrow> 2 dvd b"
proof -
  assume a: "1<b" and b: "2^x=2*(b::nat)"
  have s1: "1<x"
  proof (cases "1<x")
    assume "1<x" then show ?thesis by simp
  next
   assume x: "~1 < x" then have "2^x <= (2::nat)" using b
   proof (cases "x=0")
      assume "x=0" then show "2^x <= (2::nat)" by simp
    next
      assume "x~=0" then have "x=1" using x by simp
      then show "2^x <= (2::nat)" by simp
    qed
    then have "b<=1" using b by simp
    then show ?thesis using a by simp
  qed
  have s2: "2^(x-(1::nat)) = b"
  proof -
    from s1 b have "2^((x-Suc 0)+1) = 2*b" by simp
    then have "2*2^(x-Suc 0) = 2*b" by simp
    then show "2^(x-(1::nat)) = b" by simp
  qed
  from s1 and s2 show ?thesis using two_dvd_exp[of "x-(1::nat)"] by simp
qed

lemma exp_prod2: "\<lbrakk>1<a; 2^x=a*2\<rbrakk> \<Longrightarrow> (2::nat) dvd a"
proof -
  assume "2^x=a*2"
  then have "2^x=2*a" by simp
  moreover assume "1<a"
  ultimately show "2 dvd a" using exp_prod1 by simp
qed

lemma odd_mul_odd: "\<lbrakk>~(2::nat) dvd p; ~2 dvd q\<rbrakk> \<Longrightarrow> ~2 dvd p*q"
  by simp

lemma prime_equal: fixes p::nat shows "\<lbrakk>prime p; prime q; 2^x=p*q\<rbrakk> \<Longrightarrow> (p=q)"
proof -
  assume a: "prime p" and b: "prime q" and c: "2^x=p*q"
  from a have d: "1 < p" by (simp add: prime_nat_iff)
  moreover from b have e: "1<q" by (simp add: prime_nat_iff)
  show "p=q"
  proof (cases "p=2")
    assume p: "p=2" then have "2 dvd q" using c and exp_prod1[of q x] and e by simp
    then have "2=q" using primerew[of 2 q] and b by auto
    then show ?thesis using p by simp
  next
    assume p: "p~=2" show "p=q"
    proof (cases "q=2")
      assume q: "q=2" then have "2 dvd p" using c and exp_prod1[of p x] and d by simp
      then have "2=p" using primerew[of 2 p] and a by auto
      then show ?thesis using p by simp
    next
      assume q: "q~=2" show "p=q"
      proof -
        from p have "~ 2 dvd p" using primerew and a by auto
        moreover from q have "~2 dvd q" using primerew and b by auto
        ultimately have "~2 dvd p*q" by (simp add: odd_mul_odd)
        then have "odd ((2 :: nat) ^ x)" by (simp only: c) simp
        moreover have "(2::nat) dvd 2^x"
        proof (cases "x=0")
          assume "x=0" then have "(2::nat)^x=1" by simp
          then show ?thesis using c and d and e by simp
        next
          assume "x~=0" then have "0<x" by simp
          then show ?thesis using two_dvd_exp by simp
        qed
        ultimately show ?thesis by simp
      qed
    qed
  qed
qed

lemma nat_to_bv_length_bv_to_nat:
  "length xs = n \<Longrightarrow> xs \<noteq> [] \<Longrightarrow> nat_to_bv_length (bv_to_nat xs) n = xs"
  apply (simp only: nat_to_bv_length)
  apply (auto)
  apply (simp add: bv_extend_norm_unsigned)
  done

end
