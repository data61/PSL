(*  Author: Lukas Bulwahn <lukas.bulwahn-at-gmail.com> *)

section \<open>Proving Falling Factorial of a Sum with Induction\<close>

theory Falling_Factorial_Sum_Induction
imports
  Discrete_Summation.Factorials
begin

text \<open>Note the potentially special copyright license condition of the following proof.\<close>

lemma ffact_add_nat:
  "ffact n (x + y) = (\<Sum>k=0..n. (n choose k) * ffact k x * ffact (n - k) y)"
proof (induct n)
  case 0
  show ?case by simp
next
  case (Suc n)
  let ?s = "\<lambda>k. (n choose k) * ffact k x * ffact (n - k) y"
  let ?t = "\<lambda>k. ffact k x * ffact (Suc n - k) y"
  let ?u = "\<lambda>k. ffact (Suc k) x * ffact (n - k) y"
  have "ffact (Suc n) (x + y) = (x + y - n) * ffact n (x + y)"
    by (simp add: ffact_Suc_rev_nat)
  also have "\<dots> = (x + y - n) * (\<Sum>k = 0..n. (n choose k) * ffact k x * ffact (n - k) y)"
    using Suc.hyps by simp
  also have "\<dots> = (\<Sum>k = 0..n. ?s k * (x + y - n))"
    by (simp add: mult.commute sum_distrib_left)
  also have "\<dots> = (\<Sum>k = 0..n. ?s k * ((y + k - n) + (x - k)))"
  proof -
    have "?s k * (x + y - n) = ?s k * ((y + k - n) + (x - k))" for k
      by (cases "k \<le> x \<or> n - k \<le> y") (auto simp add: ffact_nat_triv)
    from this show ?thesis
      by (auto intro: sum.cong simp only: refl)
  qed
  also have "\<dots> = (\<Sum>k = 0..n. (n choose k) * (?t k + ?u k))"
    by (auto intro!: sum.cong simp add: Suc_diff_le ffact_Suc_rev_nat) algebra
  also have "\<dots> = (\<Sum>k = 0..n. (n choose k) * ?t k) + (\<Sum>k = 0..n. (n choose k) * ?u k)"
    by (simp add: sum.distrib add_mult_distrib2 mult.commute mult.left_commute)
  also have "\<dots> = ?t 0 + (\<Sum>k = 0..n. (n choose k + (n choose Suc k)) * ?u k)"
  proof -
    have "\<dots> = (?t 0 + (\<Sum>k = 0..n. (n choose Suc k) * ?u k)) + (\<Sum>k = 0..n. (n choose k) * ?u k)"
    proof -
      have "(\<Sum>k = Suc 0..n. (n choose k) * ?t k) = (\<Sum>k = 0..n. (n choose Suc k) * ?u k)"
      proof -
        have "(\<Sum>k = Suc 0..n. (n choose k) * ?t k) = (\<Sum>k = Suc 0..Suc n. (n choose k) * ?t k)"
          by simp
        also have "\<dots> = (sum ((\<lambda>k. (n choose k) * ?t k) o Suc) {0..n})"
          by (simp only: sum.reindex[symmetric, of Suc] inj_Suc image_Suc_atLeastAtMost)
        also have "\<dots> = (\<Sum>k = 0..n. (n choose Suc k) * ?u k)"
          by simp
        finally show ?thesis .
      qed
      from this show ?thesis
        by (simp add: sum.atLeast_Suc_atMost[of _ _ "\<lambda>k. (n choose k) * ?t k"])
    qed
    also have "\<dots> = ?t 0 + (\<Sum>k = 0..n. (n choose k + (n choose Suc k)) * ?u k)"
      by (simp add: distrib_right sum.distrib)
    finally show ?thesis .
  qed
  also have "\<dots> = (\<Sum>k = 0..Suc n. (Suc n choose k) * ffact k x * ffact (Suc n - k) y)"
  proof -
    let ?v = "\<lambda>k. (Suc n choose k) * ffact k x * ffact (Suc n - k) y"
    have "\<dots> = ?v 0 + (\<Sum>k = 0..n. (Suc n choose (Suc k)) * ?u k)"
      by simp
    also have "\<dots> = ?v 0 + (\<Sum>k = Suc 0..Suc n. ?v k)"
      by (simp only: sum.shift_bounds_cl_Suc_ivl diff_Suc_Suc mult.assoc)
    also have "\<dots> = (\<Sum>k = 0..Suc n. (Suc n choose k) * ffact k x * ffact (Suc n - k) y)"
      by (simp add: sum.atLeast_Suc_atMost)
    finally show ?thesis .
  qed
  finally show ?case .
qed

(* TODO: what's the right class here? *)
lemma ffact_add:
  fixes x y :: "'a::{ab_group_add, comm_semiring_1_cancel, ring_1}"
  shows "ffact n (x + y) = (\<Sum>k=0..n. of_nat (n choose k) * ffact k x * ffact (n - k) y)"
proof (induct n)
  case 0
  show ?case by simp
next
  case (Suc n)
  let ?s = "\<lambda>k. of_nat (n choose k) * ffact k x * ffact (n - k) y"
  let ?t = "\<lambda>k. ffact k x * ffact (Suc n - k) y"
  let ?u = "\<lambda>k. ffact (Suc k) x * ffact (n - k) y"
  have "ffact (Suc n) (x + y) = (x + y - of_nat n) * ffact n (x + y)"
    by (simp add: ffact_Suc_rev)
  also have "\<dots> = (x + y - of_nat n) * (\<Sum>k = 0..n. of_nat (n choose k) * ffact k x * ffact (n - k) y)"
    using Suc.hyps by simp
  also have "\<dots> = (\<Sum>k = 0..n. ?s k * (x + y - of_nat n))"
    by (simp add: mult.commute sum_distrib_left)
  also have "\<dots> = (\<Sum>k = 0..n. ?s k * ((y + of_nat k - of_nat n) + (x - of_nat k)))"
    by (auto intro: sum.cong simp add: diff_add_eq add_diff_eq add.commute)
  also have "\<dots> = (\<Sum>k = 0..n. of_nat (n choose k) * (?t k + ?u k))"
  proof -
    {
      fix k
      assume "k \<le> n"
      have "?u k = ffact k x * ffact (n - k) y * (x - of_nat k)"
        by (simp add: ffact_Suc_rev Suc_diff_le of_nat_diff mult.commute mult.left_commute)
      moreover from \<open>k \<le> n\<close> have "?t k = ffact k x * ffact (n - k) y * (y + of_nat k - of_nat n)"
        by (simp add: ffact_Suc_rev Suc_diff_le of_nat_diff diff_diff_eq2 mult.commute mult.left_commute)
      ultimately have
        "?s k * ((y + of_nat k - of_nat n) + (x - of_nat k)) = of_nat (n choose k) * (?t k + ?u k)"
        by (metis (no_types, lifting) distrib_left mult.assoc)
    }
    from this show ?thesis by (auto intro: sum.cong)
  qed
  also have "\<dots> = (\<Sum>k = 0..n. of_nat (n choose k) * ?t k) + (\<Sum>k = 0..n. of_nat (n choose k) * ?u k)"
    by (simp add: sum.distrib distrib_left mult.commute mult.left_commute)
  also have "\<dots> = ?t 0 + (\<Sum>k = 0..n. of_nat (n choose k + (n choose Suc k)) * ?u k)"
  proof -
    have "\<dots> = (?t 0 + (\<Sum>k = 0..n. of_nat (n choose Suc k) * ?u k)) + (\<Sum>k = 0..n. of_nat (n choose k) * ?u k)"
    proof -
      have "(\<Sum>k = Suc 0..n. of_nat (n choose k) * ?t k) = (\<Sum>k = 0..n. of_nat (n choose Suc k) * ?u k)"
      proof -
        have "(\<Sum>k = Suc 0..n. of_nat (n choose k) * ?t k) = (\<Sum>k = Suc 0..Suc n. of_nat (n choose k) * ?t k)"
          by (simp add: binomial_eq_0)
        also have "\<dots> = (sum ((\<lambda>k. of_nat (n choose k) * ?t k) o Suc) {0..n})"
          by (simp only: sum.reindex[symmetric, of Suc] inj_Suc image_Suc_atLeastAtMost)
        also have "\<dots> = (\<Sum>k = 0..n. of_nat (n choose Suc k) * ?u k)"
          by simp
        finally show ?thesis .
      qed
      from this show ?thesis
        by (simp add: sum.atLeast_Suc_atMost[of _ _ "\<lambda>k. of_nat (n choose k) * ?t k"])
    qed
    also have "\<dots> = ?t 0 + (\<Sum>k = 0..n. of_nat (n choose k + (n choose Suc k)) * ?u k)"
      by (simp add: distrib_right sum.distrib)
    finally show ?thesis .
  qed
  also have "\<dots> = (\<Sum>k = 0..Suc n. of_nat (Suc n choose k) * ffact k x * ffact (Suc n - k) y)"
  proof -
    let ?v = "\<lambda>k. of_nat (Suc n choose k) * ffact k x * ffact (Suc n - k) y"
    have "\<dots> = ?v 0 + (\<Sum>k = 0..n. of_nat (Suc n choose (Suc k)) * ?u k)"
      by simp
    also have "\<dots> = ?v 0 + (\<Sum>k = Suc 0..Suc n. ?v k)"
      by (simp only: sum.shift_bounds_cl_Suc_ivl diff_Suc_Suc mult.assoc)
    also have "\<dots> = (\<Sum>k = 0..Suc n. of_nat (Suc n choose k) * ffact k x * ffact (Suc n - k) y)"
      by (simp add: sum.atLeast_Suc_atMost)
    finally show ?thesis .
  qed
  finally show ?case .
qed

end