theory Tables_real
imports Amortized_Complexity.Amortized_Framework0
begin

(* Final version with l :: real *)

fun \<Psi> :: "bool \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> nat \<Rightarrow> real" where
"\<Psi> b i d x\<^sub>1 x\<^sub>2 n = (if n \<ge> x\<^sub>2 then i*(n - x\<^sub>2) else
  if n \<le> x\<^sub>1 \<and> b then d*(x\<^sub>1 - n) else 0)"

declare of_nat_Suc[simp] of_nat_diff[simp]

text\<open>An automatic proof:\<close>
lemma Psi_diff_Ins:
  "0 < i \<Longrightarrow> 0 < d \<Longrightarrow> \<Psi> b i d x\<^sub>1 x\<^sub>2 (Suc n) - \<Psi> b i d x\<^sub>1 x\<^sub>2 n \<le> i"
by (simp add: add_mono algebra_simps)

lemma assumes [arith]: "0 < i" "0 \<le> d"
shows "\<Psi> b i d x\<^sub>1 x\<^sub>2 (n+1) - \<Psi> b i d x\<^sub>1 x\<^sub>2 n \<le> i" (is "?D \<le> _")
proof cases
  assume "n \<ge> x\<^sub>2"
  hence "?D = i*(n+1-x\<^sub>2) - i*(n-x\<^sub>2)" by (simp)
  also have "\<dots> = i" by (simp add: algebra_simps)
  finally show ?thesis by simp
next
  assume [arith]: "\<not> n \<ge> x\<^sub>2"
  show ?thesis
  proof cases
    assume *[arith]: "n \<le> x\<^sub>1 \<and> b"
    show ?thesis
    proof cases
      assume "n+1 \<ge> x\<^sub>2"
      hence "?D = i*(n+1-x\<^sub>2) - d*(x\<^sub>1-n)" using * by (simp)
      also have "\<dots> = i + i*(n-x\<^sub>2) + -(d*(x\<^sub>1-n))"
        by (simp add: algebra_simps)
      also have "i*(n-x\<^sub>2) \<le> 0" by (simp add: mult_le_0_iff)
      also have "-(d*(x\<^sub>1-n)) \<le> 0" using * by (simp)
      finally show ?thesis by simp
    next
      assume [arith]: "\<not> n+1 \<ge> x\<^sub>2"
      thus ?thesis
      proof cases
         assume "n+1 \<ge> x\<^sub>1"
         hence "?D = -(d*(x\<^sub>1-n))" using * by (simp)
         also have "-(d*(x\<^sub>1-n)) \<le> 0" using * by (simp)
         finally have "?D \<le> 0" by simp
         then show ?thesis by simp
      next
        assume "\<not> n+1 \<ge> x\<^sub>1"
        hence "?D = d*(x\<^sub>1-(n+1)) - d*(x\<^sub>1-n)" using * by (simp)
        also have "\<dots> = -d" by (simp add: algebra_simps)
        finally show ?thesis by (simp)
      qed
    qed
  next
    assume *: "\<not> (n \<le> x\<^sub>1 \<and> b)"
    show ?thesis
    proof cases
      assume "n+1 \<ge> x\<^sub>2"
      hence "?D = i*(n+1-x\<^sub>2)" using * by (auto)
      also have "\<dots> \<le> i" by(simp add: algebra_simps)
      finally show ?thesis by simp
    next
      assume "\<not> n+1 \<ge> x\<^sub>2"
      hence "?D = 0" using * by (auto)
      thus ?thesis by simp
    qed
  qed
qed

lemma Psi_diff_Del: assumes [arith]: "0 < i" "0 \<le> d" "n\<noteq>0" and "x\<^sub>1 \<le> x\<^sub>2"
shows "\<Psi> b i d x\<^sub>1 x\<^sub>2 (n-Suc 0) - \<Psi> b i d x\<^sub>1 x\<^sub>2 (n) \<le> d" (is "?D \<le> _")
proof cases
  assume "real n - 1 \<ge> x\<^sub>2"
  hence "?D = i*(n-1-x\<^sub>2) - i*(n-x\<^sub>2)" by(simp)
  also have "\<dots> = - i" by (simp add: algebra_simps)
  finally show ?thesis by simp
next
  assume [arith]: "\<not> real n - 1 \<ge> x\<^sub>2"
  show ?thesis
  proof cases
    assume *: "n-1 \<le> x\<^sub>1 \<and> b"
    show ?thesis
    proof cases
      assume [arith]: "n \<ge> x\<^sub>2"
      hence f1: "x\<^sub>1 \<le> n" using \<open>x\<^sub>1 \<le> x\<^sub>2\<close> by linarith
      have "?D = d*(x\<^sub>1-(n-1)) - i*(n-x\<^sub>2)" using * by (simp)
      also have "\<dots> = d + d*(x\<^sub>1-n) + -(i*(n-x\<^sub>2))"
        by (simp add: algebra_simps)
      also have "-(i*(n-x\<^sub>2)) \<le> 0" by (simp add: mult_le_0_iff)
      also have "d*(x\<^sub>1-n) \<le> 0" using f1 by (simp add: mult_le_0_iff)
      finally show ?thesis by simp
    next
      assume [arith]: "\<not> n \<ge> x\<^sub>2"
      thus ?thesis (* by (simp add: algebra_simps) *)
      proof cases
        assume [arith]: "n > x\<^sub>1"
        hence "?D = d*(x\<^sub>1-(n-1))" using * by (simp)
        also have "\<dots> = d + -(d*(n-x\<^sub>1))" by (simp add: algebra_simps)
        also have "-(d*(n-x\<^sub>1)) \<le> 0" by (simp add: mult_le_0_iff)
        finally show ?thesis by simp
      next
        assume "\<not> n > x\<^sub>1"
        hence "?D = d*(x\<^sub>1-(n-1)) - d*(x\<^sub>1-n)" using * by (simp)
        also have "\<dots> = d" by (simp add: algebra_simps)
        finally show ?thesis by (simp)
      qed
    qed
  next
    assume *: "\<not> (n-1 \<le> x\<^sub>1 \<and> b)"
    show ?thesis
    proof cases
      assume n: "n \<ge> x\<^sub>2"
      hence "?D = -(i*(n-x\<^sub>2))" using * by(auto)
      also have "-(i*(n-x\<^sub>2)) \<le> 0" using n by(simp)
      finally show ?thesis by simp
    next
      assume "\<not> n \<ge> x\<^sub>2"
      hence "?D = 0" using * by (auto)
      thus ?thesis by simp
    qed
  qed
qed

locale Table0 = 
fixes f1 f2 f1' f2' e c :: real
assumes e1[arith]: "e > 1"
assumes c1[arith]: "c > 1"
assumes f1[arith]: "f1 > 0"
assumes f1cf2: "f1*c < f2"
assumes f1f2e: "f1 < f2/e"
assumes f1'_def: "f1' = min (f1*c) (f2/e)"
assumes f2'_def: "f2' = max (f1*c) (f2/e)"
begin

lemma f2[arith]: "0 < f2"
using f1f2e zero_less_divide_iff[of f2 e] by simp

lemma f2'[arith]: "0 < f2'"
by (simp add: f2'_def max_def)

lemma f2'_less_f2: "f2' < f2"
using f1cf2 by(auto simp add: f2'_def field_simps)

lemma f1_less_f1': "f1 < f1'"
using f1f2e by(auto simp add: f1'_def field_simps)

lemma f1'_gr0[arith]: "f1' > 0"
using f1_less_f1' by linarith

lemma f1'_le_f2': "f1' \<le> f2'"
by(auto simp add: f1'_def f2'_def algebra_simps)

lemma f1'c_le_f1: "f1'/c \<le> f1"
by(simp add: f1'_def min_def field_simps)

lemma f2_le_f2'e: "f2 \<le> f2'*e"
by(simp add: f2'_def max_def field_simps)

lemma f1f2'c: "f1 \<le> f2'/c"
using f1f2e by(auto simp add: f2'_def field_simps)

lemma f1'ef2: "f1' * e \<le> f2"
using f1cf2 by(auto simp add: f1'_def field_simps min_def)

end

locale Table = Table0 +
fixes l0 :: real
assumes l0f2e: "l0 \<ge> 1/(f2 * (e-1))"
assumes l0f1c: "l0 \<ge> 1/(f1 * (c-1))"
assumes f2f2': "l0 \<ge> 1/(f2 - f2')"
assumes f1'f1: "l0 \<ge> 1/((f1' - f1)*c)"
begin

definition "ai = f2/(f2-f2')"
definition "ad = f1/(f1'-f1)"

lemma aigr0[arith]: "ai > 1"
using f2'_less_f2 by(simp add: ai_def field_simps)

lemma adgr0[arith]: "ad > 0"
using f1_less_f1' by(simp add: ad_def field_simps)

lemma l0_gr0[arith]: "l0 > 0"
proof -
  have "0 < 1/(f2*(e-1))" by(simp)
  also note l0f2e
  finally show ?thesis .
qed

lemma f1_l0: assumes "l0 \<le> l/c" shows "f1*(l/c) \<le> f1*l - 1"
proof -
  have "1 = f1*((c-1)/c)*(c*(1/(f1*(c-1))))" by(simp add: field_simps)
  also note l0f1c
  also note assms(1)
  finally show ?thesis by(simp add: divide_le_cancel) (simp add: field_simps)
qed

fun nxt :: "op\<^sub>t\<^sub>b \<Rightarrow> nat*real \<Rightarrow> nat*real" where
"nxt Ins (n,l) =
 (n+1, if n+1 \<le> f2*l then l else e*l)" |
"nxt Del (n,l) =
 (n-1, if f1*l \<le> real(n-1) then l else if l0 \<le> l/c then l/c else l)"

fun t :: "op\<^sub>t\<^sub>b \<Rightarrow> nat*real \<Rightarrow> real" where
"t Ins (n,l) = (if n+1 \<le> f2*l then 1 else n+1)" |
"t Del (n,l) = (if f1*l \<le> real(n-1) then 1 else if l0 \<le> l/c then n else 1)"

fun \<Phi> :: "nat * real \<Rightarrow> real" where
"\<Phi> (n,l) = (if n \<ge> f2'*l then ai*(n - f2'*l) else
  if n \<le> f1'*l \<and> l0 \<le> l/c then ad*(f1'*l - n) else 0)"

lemma Phi_Psi: "\<Phi> (n,l) = \<Psi> (l0 \<le> l/c) ai ad (f1'*l) (f2'*l) n"
by(simp)

fun invar where
"invar(n,l) = (l \<ge> l0 \<and> (l/c \<ge> l0 \<longrightarrow> f1*l \<le> n) \<and> n \<le> f2*l)"

abbreviation "U \<equiv> \<lambda>f _. case f of Ins \<Rightarrow> ai+1 | Del \<Rightarrow> ad+1"

interpretation tb: Amortized
  where init = "(0,l0)" and nxt = nxt
  and inv = invar
  and t = t and \<Phi> = \<Phi>
  and U = U
proof (standard, goal_cases)
  case 1 show ?case by (auto simp: field_simps)
next
  case (2 s f)
  obtain n l where [simp]: "s = (n,l)" by fastforce
  from 2 have "l0 \<le> l" and "n \<le> f2*l" by auto
  hence [arith]: "l > 0" by arith
  show ?case
  proof (cases f)
    case [simp]: Ins
    show ?thesis
    proof cases
      assume "n+1 \<le> f2*l" thus ?thesis using 2 by (auto)
    next
      assume 0: "\<not> n+1 \<le> f2*l"
      have f1: "f1 * (e*l) \<le> n+1"
      proof -
        have "f1*e < f2" using f1f2e by(simp add: field_simps)
        hence "f1 * (e*l) \<le> f2*l" by simp
        with 0 show ?thesis by linarith
      qed
      have f2: "n+1 \<le> f2*e*l"
      proof -
        have "n+1 \<le> f2*l+1" using \<open>n \<le> f2*l\<close> by linarith
        also have "1 = f2*(e-1)*(1/(f2*(e-1)))" by(simp)
        also note l0f2e
        also note \<open>l0 \<le> l\<close>
        finally show ?thesis by simp (simp add: algebra_simps)
      qed
      have "l \<le> l*e" by simp
      hence "l0 \<le> l * e" using \<open>l0\<le>l\<close> by linarith
      with 0 f1 f2 show ?thesis by(simp add: field_simps)
    qed
  next
    case [simp]: Del
    show ?thesis
    proof cases
      assume "f1*l \<le> real (n - 1)"
      thus ?thesis using 2 by(auto)
    next
      assume 0: "\<not> f1*l \<le> real (n - 1)"
      show ?thesis
      proof cases
        assume l: "l0 \<le> l/c"
        hence f1: "f1*(l/c) \<le> n-1" using f1_l0[OF l] 2 by simp linarith
        have "n - 1 \<le> f2 * (l/c)"
        proof -
          have "f1*l \<le> f2*(l/c)" using f1cf2 by (simp add: field_simps)
          thus ?thesis using 0 by linarith
        qed
        with l 0 f1 show ?thesis by (auto)
      next
        assume "\<not> l0 \<le> l/c"
        with 2 show ?thesis by (auto simp add: field_simps)
      qed
    qed
  qed
next
  case (3 s) thus ?case by(cases s)(simp split: if_splits)
next
  case 4 show ?case by(simp add: field_simps not_le)
next
  case (5 s f)
  obtain n l where [simp]: "s = (n,l)" by fastforce
  have [arith]: "l \<ge> l0"  "n \<le> f2*l" using 5 by auto
  show ?case
  proof (cases f)
    case [simp]: Ins
    show ?thesis (is "?A \<le> _")
    proof cases
      assume "n+1 \<le> f2*l"
      thus ?thesis by(simp del: \<Phi>.simps \<Psi>.simps add: Phi_Psi Psi_diff_Ins)
    next
      assume [arith]: "\<not> n+1 \<le> f2*l"
      have "(f2 - f2')*l \<ge> 1"
        using mult_mono[OF order_refl \<open>l\<ge>l0\<close>, of "f2-f2'"] f2'_less_f2 f2f2'
        by (simp add: field_simps)
      hence "n \<ge> f2'*l" by(simp add: algebra_simps)
      hence Phi: "\<Phi> s = ai * (n - f2'*l)" by simp
      have "f1'*e*l \<le> f2*l" using f1'ef2 by(simp)
      hence "f1'*e*l < n+1" by linarith
      have "?A \<le> n - ai*(f2 - f2')*l + ai + 1"
      proof cases
        assume "n+1 < f2'*(e*l)"
        hence "?A = n+1 - ai*(n - f2'*l)" using Phi \<open>f1'*e*l < n+1\<close> by simp
        also have "\<dots> = n + ai*(-(n+1) + f2'*l) + ai+1"
          by(simp add: algebra_simps)
        also have "-(n+1) \<le> -f2*l" by linarith
        finally show ?thesis by(simp add: algebra_simps)
      next
        assume "\<not> n+1 < f2'*(e*l)"
        hence "?A = n + ai*(-f2'*e + f2')*l + ai+1" using Phi
          by(simp add: algebra_simps)
        also have "-f2'*e \<le> -f2" using f2_le_f2'e by linarith
        finally show ?thesis by(simp add: algebra_simps)
      qed
      also have "\<dots> = n - f2*l + ai+1" using f2'_less_f2 by(simp add: ai_def)
      finally show ?thesis by simp
    qed
  next
    case [simp]: Del
    show ?thesis (is "?A \<le> _")
    proof cases
      assume "n=0" with 5 show ?thesis
        by(simp add: mult_le_0_iff field_simps)
    next
      assume [arith]: "n\<noteq>0"
      show ?thesis
      proof cases
        assume "real n - 1 \<ge> f1*l \<or> l/c < l0"
        thus ?thesis using f1'_le_f2'
          by(auto simp del: \<Phi>.simps \<Psi>.simps simp add: Phi_Psi Psi_diff_Del)
      next
        assume "\<not> (real n - 1 \<ge> f1*l \<or> l/c < l0)"
        hence [arith]: "real n - 1 < f1*l" "l/c \<ge> l0" by linarith+
        hence "l \<ge> l0*c" and "l/c \<ge> l0" and "f1*l \<le> n" using 5
          by (auto simp: field_simps)
        have "f1*l \<le> f2'*l/c" using f1f2'c by(simp add: field_simps)
        hence f2: "n-1 < f2'*l/c" by linarith
        have "f1'*l \<le> f2'*l" using f1'_le_f2' by simp
        have "(f1' - f1)*l \<ge> 1"
          using mult_mono[OF order_refl \<open>l\<ge>l0*c\<close>, of "f1'-f1"] f1_less_f1' f1'f1
          by (simp add: field_simps)
        hence "n < f1'*l" by(simp add: algebra_simps)
        hence Phi: "\<Phi> s = ad*(f1'*l - n)"
          apply(simp) using \<open>f1'*l \<le> f2'*l\<close> by linarith
        have "?A \<le> n - ad*(f1' - f1)*l + ad"
        proof cases
          assume "n-1 < f1'*l/c \<and> l/(c*c) \<ge> l0"
          hence "\<Phi> (nxt f s) = ad*(f1'*l/c - (n-1))" using f2 by(auto)
          hence "?A = n + ad*(f1'*l/c - (n-1)) - (ad*(f1'*l - n))"
            using Phi by (simp add: algebra_simps)
          also have "\<dots> = n + ad*(f1'/c - f1')*l + ad"
            by(simp add: algebra_simps)
          also note f1'c_le_f1
          finally show ?thesis by(simp add: algebra_simps)
        next
          assume "\<not>(n-1 < f1'*l/c \<and> l/(c*c) \<ge> l0)"
          hence "\<Phi> (nxt f s) = 0" using f2 by(auto)
          hence "?A = n + ad*(n - f1'*l)" using Phi
            by (simp add: algebra_simps)
          also have "\<dots> = n + ad*(n-1 - f1'*l) + ad" by(simp add: algebra_simps)
          also have "n-1 \<le> f1*l" by linarith
          finally show ?thesis by (simp add: algebra_simps)
        qed
        also have "\<dots> = n - f1*l + ad" using f1_less_f1' by(simp add: ad_def)
        finally show ?thesis by simp
      qed
    qed
  qed
qed

end


locale Optimal =
fixes f2 c e :: real and l0 :: nat
assumes e1[arith]: "e > 1"
assumes c1[arith]: "c > 1"
assumes [arith]: "f2 > 0"
assumes l0: "(e*c)/(f2*(min e c - 1)) \<le> l0"
begin

lemma l0e: "(e*c)/(f2*(e-1)) \<le> l0"
proof-
  have 0: "f2 * (l0 * min e c) \<le> e * (f2 * l0)"
    by (simp add: min_def ac_simps mult_right_mono)
  from l0 show ?thesis apply(simp add: field_simps) using 0 by linarith
qed

lemma l0c: "(e*c)/(f2*(c-1)) \<le> l0"
proof-
  have 0: "f2 * (l0 * min e c) \<le> c * (f2 * l0)"
    by (simp add: min_def ac_simps mult_right_mono)
  from l0 show ?thesis apply(simp add: field_simps) using 0 by linarith
qed

interpretation Table
where f1="f2/(e*c)" and f2=f2 and e=e and c=c and f1'="f2/e" and f2'="f2/e" and l0=l0
proof (standard, goal_cases)
  case 1 show ?case by(rule e1)
next
  case 2 show ?case by(rule c1)
next
  case 3 show ?case by(simp)
next
  case 4 show ?case by(simp add: field_simps)
next
  case 5 show ?case by(simp add: field_simps)
next
  case 6 show ?case by(simp)
next
  case 7 show ?case by(simp)
next
  case 8 show ?case using l0e less_1_mult[OF c1 e1] by(simp add: field_simps)
next
  case 9 show ?case using l0c by(simp)
next
  case 10 show ?case
  proof-
    have 1: "c*e>e" by (simp)
    show ?thesis using l0e apply(simp add: field_simps) using 1 by linarith
  qed
next
  case 11 show ?case
  proof-
    have 1: "c*e>e" by (simp)
    show ?thesis using l0c
      apply(simp add: algebra_simps pos_le_divide_eq)
      apply(simp add: field_simps)
      using 1 by linarith
  qed
qed

lemma "ai = e/(e-1)"
unfolding ai_def by(simp add: field_simps)

lemma "ad = 1/(c-1)"
unfolding ad_def by(simp add: field_simps)

end

interpretation I1: Optimal where e=2 and c=2 and f2=1 and l0=4 (* f1=1/4 *)
proof qed simp_all

interpretation I2: Optimal where e=2 and c=2 and f2="3/4" and l0=6 (* f1=3/16 *)
proof qed simp_all

interpretation I3: Optimal where e=2 and c=2 and f2="0.8" and l0=5 (* f1=1/5 *)
proof qed simp_all

interpretation I4: Optimal where e=3 and c=3 and f2="0.9" and l0=5 (* f1=1/10 *)
proof qed simp_all

interpretation I5: Optimal where e=4 and c=4 and f2=1 and l0=6 (* f1=1/16 *)
proof qed simp_all

interpretation I6: Optimal where e="2.5" and c="2.5" and f2=1 and l0=5 (* f1=4/25 *)
proof qed simp_all

interpretation I7: Optimal where f2=1 and c="3/2" and e=2 and l0=6 (* f1=1/3 *)
proof qed (simp_all add: min_def)

interpretation I8: Optimal where f2=1 and e="3/2" and c=2 and l0=6 (* f1=1/3 *)
proof qed (simp_all add: min_def)

end
