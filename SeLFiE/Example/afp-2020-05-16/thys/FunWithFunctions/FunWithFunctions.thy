(*  Title:      Fun With Functions
    Author:     Tobias Nipkow
*)

theory FunWithFunctions imports Complex_Main begin

text\<open>See \cite{Tao2006}. Was first brought to our attention by Herbert
Ehler who provided a similar proof.\<close>

theorem identity1: fixes f :: "nat \<Rightarrow> nat"
assumes fff: "\<And>n. f(f(n)) < f(Suc(n))"
shows "f(n) = n"
proof -
  { fix m n have key: "n \<le> m \<Longrightarrow> n \<le> f(m)"
    proof(induct n arbitrary: m)
      case 0 show ?case by simp
    next
      case (Suc n)
      hence "m \<noteq> 0" by simp
      then obtain k where [simp]: "m = Suc k" by (metis not0_implies_Suc)
      have "n \<le> f(k)" using Suc by simp
      hence "n \<le> f(f(k))" using Suc by simp
      also have "\<dots> < f(m)" using fff by simp
      finally show ?case by simp
    qed }
  hence "\<And>n. n \<le> f(n)" by simp
  hence "\<And>n. f(n) < f(Suc n)" by(metis fff order_le_less_trans)
  hence "f(n) < n+1" by (metis fff lift_Suc_mono_less_iff[of f] Suc_eq_plus1)
  with \<open>n \<le> f(n)\<close> show "f n = n" by arith
qed


text\<open>See \cite{Tao2006}. Possible extension:
Should also hold if the range of \<open>f\<close> is the reals!
\<close>

lemma identity2: fixes f :: "nat \<Rightarrow> nat"
assumes "f(k) = k" and "k \<ge> 2"
and f_times: "\<And>m n. f(m*n) = f(m)*f(n)"
and f_mono: "\<And>m n. m<n \<Longrightarrow> f m < f n"
shows "f(n) = n"
proof -
  have 0: "f(0) = 0"
    by (metis f_mono f_times mult_1_right mult_is_0 nat_less_le nat_mult_eq_cancel_disj not_less_eq)
  have 1: "f(1) = 1"
    by (metis f_mono f_times gr_implies_not0 mult_eq_self_implies_10 nat_mult_1_right zero_less_one)
  have 2: "f 2 = 2"
  proof -
    have "2 + (k - 2) = k" using \<open>k \<ge> 2\<close> by arith
    hence "f(2) \<le> 2"
      using mono_nat_linear_lb[of f 2 "k - 2",OF f_mono] \<open>f k = k\<close>
      by simp
    thus "f 2 = 2" using 1 f_mono[of 1 2] by arith
  qed
  show ?thesis
  proof(induct rule:less_induct)
    case (less i)
    show ?case
    proof cases
      assume "i\<le>1" thus ?case using 0 1 by (auto simp add:le_Suc_eq)
    next
      assume "~i\<le>1"
      show ?case
      proof cases
        assume "i mod 2 = 0"
        hence "\<exists>k. i=2*k" by arith
        then obtain k where "i = 2*k" ..
        hence "0 < k" and "k<i" using \<open>~i\<le>1\<close> by arith+
        hence "f(k) = k" using less(1) by blast
        thus "f(i) = i" using \<open>i = 2*k\<close> by(simp add:f_times 2)
      next
        assume "i mod 2 \<noteq> 0"
        hence "\<exists>k. i=2*k+1" by arith
        then obtain k where "i = 2*k+1" ..
        hence "0<k" and "k+1<i" using \<open>~i\<le>1\<close> by arith+
        have "2*k < f(2*k+1)"
        proof -
          have "2*k = 2*f(k)" using less(1) \<open>i=2*k+1\<close> by simp
          also have "\<dots> = f(2*k)" by(simp add:f_times 2)
          also have "\<dots> < f(2*k+1)" using f_mono[of "2*k" "2*k+1"] by simp
          finally show ?thesis .
        qed
        moreover
        have "f(2*k+1) < 2*(k+1)"
        proof -
          have "f(2*k+1) < f(2*k+2)" using f_mono[of "2*k+1" "2*k+2"] by simp
          also have "\<dots> = f(2*(k+1))" by simp
          also have "\<dots> = 2*f(k+1)" by(simp only:f_times 2)
          also have "f(k+1) = k+1" using less(1) \<open>i=2*k+1\<close> \<open>~i\<le>1\<close> by simp
          finally show ?thesis .
        qed
        ultimately show "f(i) = i" using \<open>i = 2*k+1\<close> by arith
      qed
    qed
  qed
qed


text\<open>One more from Tao's booklet. If \<open>f\<close> is also assumed to be
continuous, @{term"f(x::real) = x+1"} holds for all reals, not only
rationals. Extend the proof!\<close>

theorem plus1:
fixes f :: "real \<Rightarrow> real"
assumes 0: "f 0 = 1" and f_add: "\<And>x y. f(x+y+1) = f x + f y"

assumes "r : \<rat>" shows "f(r) = r + 1"
proof -
  { fix i have "f(of_int i) = of_int i + 1"
    proof (induct i rule: int_induct [where k=0])
      case base show ?case using 0 by simp
    next
      case (step1 i)
      have "f(of_int (i+1)) = f(of_int i + 0 + 1)" by simp
      also have "\<dots> = f(of_int i) + f 0" by(rule f_add)
      also have "\<dots> = of_int (i+1) + 1" using step1 0 by simp
      finally show ?case .
    next
      case (step2 i)
      have "f(of_int i) = f(of_int (i - 1) + 0 + 1)" by simp
      also have "\<dots> = f(of_int (i - 1)) + f 0" by(rule f_add)
      also have "\<dots> = f(of_int (i - 1)) + 1 " using 0 by simp
      finally show ?case using step2 by simp
    qed }
  note f_int = this
  { fix n r have "f(of_int (Suc n)*r + of_int n) = of_int (Suc n) * f r"
    proof(induct n)
      case 0 show ?case by simp
    next
      case (Suc n)
      have "of_int (Suc(Suc n))*r + of_int (Suc n) =
            r + (of_int (Suc n)*r + of_int n) + 1" (is "?a = ?b")
        by(simp add: field_simps)
      hence "f ?a = f ?b"
        by presburger
      also have "\<dots> = f r + f(of_int (Suc n)*r + of_int n)" by(rule f_add)
      also have "\<dots> = f r + of_int (Suc n) * f r" by(simp only:Suc)
      finally show ?case by(simp add: field_simps)
    qed }
  note 1 = this
  { fix n::nat and r assume "n\<noteq>0"
    have "f(of_int (n)*r + of_int (n - 1)) = of_int (n) * f r"
    proof(cases n)
      case 0 thus ?thesis using \<open>n\<noteq>0\<close> by simp
    next
      case Suc thus ?thesis using \<open>n\<noteq>0\<close> using "1" by auto
    qed }
  note f_mult = this
  from \<open>r:\<rat>\<close> obtain i::int and n::nat where r: "r = of_int i/of_int n" and "n\<noteq>0"
    by(fastforce simp:Rats_eq_int_div_nat)
  have "of_int (n) * f(of_int i / of_int n) = f(of_int i + of_int (n - 1))"
    using \<open>n\<noteq>0\<close>
    by (metis (no_types, hide_lams) f_mult mult.commute nonzero_divide_eq_eq of_int_of_nat_eq of_nat_0_eq_iff) 
  also have "\<dots> = f(of_int (i + int n - 1))" using \<open>n\<noteq>0\<close>[simplified]
    by (metis One_nat_def Suc_leI of_nat_1 add_diff_eq of_int_add of_nat_diff)
  also have "\<dots> = of_int (i + int n - 1) + 1" by(rule f_int)
  also have "\<dots> = of_int i + of_int n" by arith
  finally show ?thesis using \<open>n\<noteq>0\<close> unfolding r by (simp add:field_simps)
qed


text\<open>The only total model of a naive recursion equation of factorial on
integers is 0 for all negative arguments. Probably folklore.\<close>

theorem ifac_neg0: fixes ifac :: "int \<Rightarrow> int"
assumes ifac_rec: "\<And>i. ifac i = (if i=0 then 1 else i*ifac(i - 1))"
shows "i<0 \<Longrightarrow> ifac i = 0"
proof(rule ccontr)
  assume 0: "i<0" "ifac i \<noteq> 0"
  { fix j assume "j \<le> i"
    have "ifac j \<noteq> 0"
      apply(rule int_le_induct[OF \<open>j\<le>i\<close>])
       apply(rule \<open>ifac i \<noteq> 0\<close>)
      apply (metis \<open>i<0\<close> ifac_rec linorder_not_le mult_eq_0_iff)
      done
  } note below0 = this
  { fix j assume "j<i"
    have "1 < -j" using \<open>j<i\<close> \<open>i<0\<close> by arith
    have "ifac(j - 1) \<noteq> 0" using \<open>j<i\<close> by(simp add: below0)
    then have "\<bar>ifac (j - 1)\<bar> < (-j) * \<bar>ifac (j - 1)\<bar>" using \<open>j<i\<close>
      mult_le_less_imp_less[OF order_refl[of "abs(ifac(j - 1))"] \<open>1 < -j\<close>]
      by(simp add:mult.commute)
    hence "abs(ifac(j - 1)) < abs(ifac j)"
      using \<open>1 < -j\<close> by(simp add: ifac_rec[of "j"] abs_mult)
  } note not_wf = this
  let ?f = "%j. nat(abs(ifac(i - int(j+1))))"
  obtain k where "\<not> ?f (Suc k) < ?f k"
    using wf_no_infinite_down_chainE[OF wf_less, of "?f"] by blast
  moreover have "i - int (k + 1) - 1 = i - int (Suc k + 1)" by arith
  ultimately show False using not_wf[of "i - int(k+1)"]
    by (simp only:) arith
qed

end
