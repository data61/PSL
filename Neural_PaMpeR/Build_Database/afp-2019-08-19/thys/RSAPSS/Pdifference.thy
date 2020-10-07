(*  Title:      RSAPSS/Pdifference.thy

    Author:     Christina Lindenberg, Kai Wirt, Technische Universität Darmstadt
    Copyright:  2005 - Technische Universität Darmstadt
*)
section "Positive differences"

theory Pdifference
imports "HOL-Computational_Algebra.Primes" Mod
begin

definition
  pdifference :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  [simp]: "pdifference a b = (if a < b then (b-a) else (a-b))"

lemma timesdistributesoverpdifference:
    "m*(pdifference a b) = pdifference (m*(a::nat)) (m* (b::nat))"
  by (auto simp add: nat_distrib)

lemma addconst: "a = (b::nat) \<Longrightarrow> c+a = c+b"
  by auto

lemma invers: "a \<le> x \<Longrightarrow> (x::nat) = x - a + a"
  by auto

lemma invers2: "\<lbrakk>a \<le> b; (b-a) = p*q\<rbrakk> \<Longrightarrow> (b::nat) = a+p*q"
  apply (subst addconst [symmetric])
  apply (assumption)
  apply (subst add.commute, rule invers, simp)
  done

lemma modadd: "\<lbrakk>b = a+p*q\<rbrakk> \<Longrightarrow> (a::nat) mod p = b mod p"
  by auto

lemma equalmodstrick1: "pdifference a b mod p = 0 \<Longrightarrow> a mod p = b mod p"
  using mod_eq_dvd_iff_nat [of a b p] mod_eq_dvd_iff_nat [of b a p]
  by (cases "a < b") auto

lemma diff_add_assoc: "b \<le> c \<Longrightarrow> c - (c - b) = c - c + (b::nat)"
  by auto

lemma diff_add_assoc2: "a \<le> c \<Longrightarrow> c - (c - a + b) = (c - c + (a::nat) - b)"
  apply (subst diff_diff_left [symmetric])
  apply (subst diff_add_assoc)
  apply auto
  done

lemma diff_add_diff: "x \<le> b \<Longrightarrow> (b::nat) - x + y - b = y - x"
  by (induct b) auto

lemma equalmodstrick2:
  assumes "a mod p = b mod p"
  shows "pdifference a b mod p = 0"
proof -
  { fix a b
    assume *: "a mod p = b mod p"
    have "a - b = a div p * p + a mod p - b div p * p - b mod p"
      by simp
    also have "\<dots> = a div p * p - b div p * p"
      using * by (simp only:)
    also have "\<dots> = (a div p - b div p) * p"
      by (simp add: diff_mult_distrib)
    finally have "(a - b) mod p = 0"
      by simp
  }
  from this [OF assms] this [OF assms [symmetric]]
  show ?thesis by simp
qed

lemma primekeyrewrite:
  fixes p::nat shows "\<lbrakk>prime p; p dvd (a*b);~(p dvd a)\<rbrakk> \<Longrightarrow> p dvd b"
  apply (subst (asm) prime_dvd_mult_nat)
  apply auto
  done

lemma multzero: "\<lbrakk>0 < m mod p; m*a = 0\<rbrakk> \<Longrightarrow> (a::nat) = 0"
  by auto

lemma primekeytrick:
  fixes A B :: nat
  assumes "(M * A) mod P = (M * B) mod P"
  assumes "M mod P \<noteq> 0" and "prime P"
  shows "A mod P = B mod P"
proof -
  from assms have "M > 0"
    by (auto intro: ccontr)
  from assms have *: "\<And>q. P dvd M * q \<Longrightarrow> P dvd q"
    using primekeyrewrite [of P M] unfolding dvd_eq_mod_eq_0 [symmetric] by blast 
  from equalmodstrick2 [OF assms(1)] \<open>M > 0\<close> show ?thesis
    apply -
    apply (rule equalmodstrick1)
    apply (auto intro: * dvdI simp add: dvd_eq_mod_eq_0 [symmetric] diff_mult_distrib2 [symmetric])
    done
qed

end

