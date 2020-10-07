theory Tables_nat
imports Tables_real
begin

declare le_of_int_ceiling[simp] (* MOVE *)

(* Final version with l :: nat in fully localized form, no duplication *)

locale TableInv = Table0 f1 f2 f1' f2' e c for f1 f2 f1' f2' e c :: real +
fixes l0 :: nat
assumes l0f2e: "l0 \<ge> 1/(f2 * (e-1))"
assumes l0f1c: "l0 \<ge> 1/(f1 * (c-1))"

assumes l0f2f1e: "l0 \<ge> f1/(f2 - f1*e)"
assumes l0f2f1c: "l0 \<ge> f2/(f2 - f1*c)"
begin

lemma l0_gr0[arith]: "l0 > 0"
proof -
  have "0 < 1/(f2*(e-1))" by(simp)
  also note l0f2e
  finally show ?thesis by simp
qed

lemma f1_l0: assumes "l0 \<le> l/c" shows "f1*(l/c) \<le> f1*l - 1"
proof -
  have "1 = f1*((c-1)/c)*(c*(1/(f1*(c-1))))"
    using f1'_le_f2' f2'_less_f2 by(simp add: field_simps)
  also note l0f1c
  also have l': "c*l0 \<le> l" using assms(1) by(simp add: field_simps)
  finally show ?thesis by(simp add: divide_le_cancel) (simp add: field_simps)
qed

fun nxt :: "op\<^sub>t\<^sub>b \<Rightarrow> nat*nat \<Rightarrow> nat*nat" where
"nxt Ins (n,l) =
 (n+1, if n+1 \<le> f2*l then l else nat\<lceil>e*l\<rceil>)" |
"nxt Del (n,l) =
 (n-1, if f1*l \<le> real(n-1) then l else if l0 \<le> \<lfloor>l/c\<rfloor> then nat\<lfloor>l/c\<rfloor> else l)"

fun t :: "op\<^sub>t\<^sub>b \<Rightarrow> nat*nat \<Rightarrow> real" where
"t Ins (n,l) = (if n+1 \<le> f2*l then 1 else n+1)" |
"t Del (n,l) = (if f1*l \<le> real(n-1) then 1 else if l0 \<le> \<lfloor>l/c\<rfloor> then n else 1)"

fun invar :: "nat * nat \<Rightarrow> bool" where
"invar(n,l) = (l \<ge> l0 \<and> (\<lfloor>l/c\<rfloor> \<ge> l0 \<longrightarrow> f1*l \<le> n) \<and> n \<le> f2*l)"

lemma invar_init: "invar (0,l0)"
by (auto simp: le_floor_iff field_simps)

lemma invar_pres: assumes "invar s" shows "invar(nxt f s)"
proof -
  obtain n l where [simp]: "s = (n,l)" by fastforce
  from assms have "l0 \<le> l" and "n \<le> f2*l" by auto
  show ?thesis
  proof (cases f)
    case [simp]: Ins
    show ?thesis
    proof cases
      assume "n+1 \<le> f2*l" thus ?thesis using assms by (auto)
    next
      assume 0: "\<not> n+1 \<le> f2*l"
      have f1: "f1 * \<lceil>e*l\<rceil> \<le> n+1"
      proof -
        have "\<lceil>e*l\<rceil> \<le> e*l + 1" by linarith
        hence "f1 * \<lceil>e*l\<rceil> \<le> f1 * (e*l + 1)" by simp
        also have "\<dots> \<le> f2*l"
        proof -
          have "f1 \<le> (f2 - f1*e)*l0"
            using l0f2f1e f1f2e by(simp add: field_simps)
          also note \<open>l0 \<le> l\<close>
          finally show ?thesis using f1f2e[simplified field_simps]
            by (simp add:ac_simps mult_left_mono) (simp add:algebra_simps)
       qed
       finally show ?thesis using 0 by linarith
      qed
      have "n+1 \<le> f2*e*l"
      proof -
        have "n+1 \<le> f2*l+1" using \<open>n \<le> f2*l\<close> by linarith
        also have "1 = f2*(e-1)*(1/(f2*(e-1)))" by(simp)
        also note l0f2e
        also note \<open>l0 \<le> l\<close>
        finally show ?thesis by simp (simp add: algebra_simps)
      qed
      also have "f2*e*l \<le> f2*\<lceil>e*l\<rceil>" by simp
      finally have f2: "n+1 \<le> f2*\<lceil>e*l\<rceil>" .
      have "l < e*l" using \<open>l0 \<le> l\<close> by simp
      hence "l0 \<le> e*l" using \<open>l0\<le>l\<close> by linarith
      with 0 f1 f2 show ?thesis by (auto simp add: field_simps) linarith
    qed
  next
    case [simp]: Del
    show ?thesis
    proof cases
      assume "f1*l \<le> real n - 1"
      thus ?thesis using assms by(auto)
    next
      assume 0: "\<not> f1*l \<le> real n - 1"
      show ?thesis
      proof cases
        assume "n=0" thus ?thesis using 0 assms by(simp add: field_simps)
      next
        assume "n \<noteq> 0"
        show ?thesis
        proof cases
          assume l: "l0 \<le> \<lfloor>l/c\<rfloor>"
          hence l': "l0 \<le> l/c" by linarith
          have "f1 * \<lfloor>l/c\<rfloor> \<le> f1*(l/c)" by(simp del: times_divide_eq_right)
          hence f1: "f1*\<lfloor>l/c\<rfloor> \<le> n-1" using l' f1_l0[OF l'] assms \<open>n \<noteq> 0\<close>
            by(simp add: le_floor_iff)
          have "n-1 \<le> f2 * \<lfloor>l/c\<rfloor>"
          proof -
            have "n-1 < f1*l" using 0 \<open>n \<noteq> 0\<close> by linarith
            also have "f1*l \<le> f2*(l/c) - f2"
            proof -
              have "(f2 - f1*c)*l0 \<ge> f2"
                using l0f2f1c f1cf2 by(simp add: field_simps)
              with mult_left_mono[OF \<open>l0 \<le> l/c\<close>, of "f2-f1*c"] f1cf2
              have "(f2 - f1*c)*(l/c) \<ge> f2" by linarith
              thus ?thesis by(simp add: field_simps)
            qed
            also have "\<dots> \<le> f2*\<lfloor>l/c\<rfloor>"
            proof -
              have "l/c - 1 \<le> \<lfloor>l/c\<rfloor>" by linarith
              from mult_left_mono[OF this, of f2] show ?thesis
                by(simp add: algebra_simps)
            qed
            finally show ?thesis using 0 \<open>n \<noteq> 0\<close> by linarith
          qed
          with l 0 f1 \<open>n \<noteq> 0\<close> show ?thesis by (auto)
        next
          assume "\<not> l0 \<le> \<lfloor>l/c\<rfloor>"
          with 0 assms show ?thesis by (auto simp add: field_simps)
        qed
      qed
    qed
  qed
qed

end

locale Table1 = TableInv +
assumes f2f2': "l0 \<ge> 1/(f2 - f2')"
assumes f1'f1: "l0 \<ge> 1/((f1' - f1)*c)"
begin

definition "ai = f2/(f2-f2')"
definition "ad = f1/(f1'-f1)"

lemma aigr0[arith]: "ai > 1"
using f2'_less_f2 by(simp add: ai_def field_simps)

lemma adgr0[arith]: "ad > 0"
using f1_less_f1' by(simp add: ad_def field_simps)

lemma f1'ad[arith]: "f1'*ad > 0"
by simp

lemma f2'ai[arith]: "f2'*ai > 0"
by simp

fun \<Phi> :: "nat * nat \<Rightarrow> real" where
"\<Phi> (n,l) = (if n \<ge> f2'*l then ai*(n - f2'*l) else
  if n \<le> f1'*l \<and> l0 \<le> \<lfloor>l/c\<rfloor> then ad*(f1'*l - n) else 0)"

lemma Phi_Psi: "\<Phi> (n,l) = \<Psi> (l0 \<le> \<lfloor>l/c\<rfloor>) ai ad (f1'*l) (f2'*l) n"
by(simp)

abbreviation "U \<equiv> \<lambda>f _. case f of Ins \<Rightarrow> ai+1 + f1'*ad | Del \<Rightarrow> ad+1 + f2'*ai"

interpretation tb: Amortized
  where init = "(0,l0)" and nxt = nxt
  and inv = invar
  and t = t and \<Phi> = \<Phi>
  and U = U
proof (standard, goal_cases)
  case 1 show ?case by (fact invar_init)
next
  case 2 thus ?case by(fact invar_pres)
next
  case (3 s) thus ?case by(cases s)(simp split: if_splits)
next
  case 4 show ?case
    by(auto simp: field_simps mult_le_0_iff le_floor_iff)
next
  case (5 s f)
  obtain n l where [simp]: "s = (n,l)" by fastforce
  show ?case
  proof (cases f)
    case [simp]: Ins
    show ?thesis (is "?A \<le> _")
    proof cases
      assume "n+1 \<le> f2*l"
      hence "?A \<le> ai+1" by(simp del: \<Phi>.simps \<Psi>.simps add: Phi_Psi Psi_diff_Ins)
      thus ?thesis by simp
    next
      assume [arith]: "\<not> n+1 \<le> f2*l"
      have [arith]: "l \<ge> l0"  "n \<le> f2*l" using 5 by auto
      have "(f2 - f2')*l \<ge> 1"
        using mult_mono[OF order_refl, of l0 l "f2-f2'"] f2'_less_f2 f2f2'
        by (simp add: field_simps)
      hence "n \<ge> f2'*l" by(simp add: algebra_simps)
      hence Phi: "\<Phi> s = ai * (n - f2'*l)" by simp
      have [simp]: "real (nat \<lceil>e*l\<rceil>) = real_of_int \<lceil>e*l\<rceil>"
        by (simp add: order.order_iff_strict)
      have "?A \<le> n - ai*(f2 - f2')*l + ai + 1 + f1'*ad" (is "_ \<le> ?R")
      proof cases
        assume f2': "n+1 < f2'*\<lceil>e*l\<rceil>"
        show ?thesis
        proof cases
          assume "n+1 \<le> f1'*\<lceil>e*l\<rceil>"
          hence "?A \<le> n+1 + ad*(f1'*\<lceil>e*l\<rceil>-(n+1)) - ai*(n - f2'*l)"
            using Phi f2' by (simp add: )
          also have "f1'*\<lceil>e*l\<rceil> - (n+1) \<le> f1'"
          proof -
            have "f1'*\<lceil>e*l\<rceil> \<le> f1'*(e*l + 1)" by(simp)
            also have "\<dots> = f1'*e*l + f1'" by(simp add: algebra_simps)
            also have "f1'*e*l \<le> f2*l" using f1'ef2 by(simp)
            finally show ?thesis by linarith
          qed
          also have "n+1+ad*f1'-ai*(n-f2'*l) = n+ai*(-real(n+1)+f2'*l)+ai+f1'*ad+1"
            by(simp add: algebra_simps)
          also have "-real(n+1) \<le> -f2*l" by linarith
          finally show ?thesis by(simp add: algebra_simps) (* f1'*ad *)
        next
          assume "\<not> n+1 \<le> f1'*\<lceil>e*l\<rceil>"
          hence "?A = n+1 - ai*(n - f2'*l)" using Phi f2' by (simp)
          also have "n+1-ai*(n-f2'*l) = n+ai*(-real(n+1)+f2'*l)+ai+1"
            by(simp add: algebra_simps)
          also have "-real(n+1) \<le> -f2*l" by linarith
          also have "n+ai*(-f2*l+f2'*l)+ai+1 \<le> ?R"
            by(simp add: algebra_simps)
          finally show ?thesis by(simp)
        qed
      next
        assume "\<not> n+1 < f2'*\<lceil>e*l\<rceil>"
        hence "?A = n + ai*(-f2'*\<lceil>e*l\<rceil> + f2'*l) + ai+1" using Phi
          by(simp add: algebra_simps)
        also have "-f2'*\<lceil>e*l\<rceil> \<le> -f2'*e*l" by(simp)
        also have "-f2'*e \<le> -f2" using f2_le_f2'e by linarith
        also have "n+ai*(-f2*l+f2'*l)+ai+1 \<le> ?R" by(simp add: algebra_simps)
        finally show ?thesis by(simp)
      qed
      also have "\<dots> = n - f2*l + ai+f1'*ad+1" using f2'_less_f2
        by(simp add: ai_def)
      finally show ?thesis by simp
    qed
  next
    case [simp]: Del
    have [arith]: "l \<ge> l0" using 5 by simp
    show ?thesis
    proof cases
      assume "n=0" with 5 show ?thesis
        by(simp add: mult_le_0_iff field_simps)
    next
      assume [arith]: "n\<noteq>0"
      show ?thesis (is "?A \<le> _")
      proof cases
        assume "real n - 1 \<ge> f1*l \<or> \<lfloor>l/c\<rfloor> < l0"
        hence "?A \<le> ad+1" using f1'_le_f2'
          by(auto simp del: \<Phi>.simps \<Psi>.simps simp add: Phi_Psi Psi_diff_Del)
        thus ?thesis by simp
      next
        assume "\<not> (real n - 1 \<ge> f1*l \<or> \<lfloor>l/c\<rfloor> < l0)"
        hence n: "real n - 1 < f1*l" and lc': "\<lfloor>l/c\<rfloor> \<ge> l0" and lc: "l/c \<ge> l0"
          by linarith+
        have "f1'*l \<le> f2'*l" using f1'_le_f2' by simp
        have "(f1' - f1)*l \<ge> 1" using mult_mono[OF order_refl, of l0 "l/c" "f1'-f1"]
          lc f1_less_f1' f1'f1 by (simp add: field_simps)
        hence "n < f1'*l" using n by(simp add: algebra_simps)
        hence Phi: "\<Phi> s = ad*(f1'*l - n)"
          apply(simp) using \<open>f1'*l \<le> f2'*l\<close> lc by linarith
        have "?A \<le> n - ad*(f1' - f1)*l + ad + f2'*ai" (is "_ \<le> ?R + _")
        proof cases
          assume f2': "n-1 < f2'*\<lfloor>l/c\<rfloor>"
          show ?thesis
          proof cases
            assume "n-1 < f1'*\<lfloor>l/c\<rfloor> \<and> \<lfloor>\<lfloor>l/c\<rfloor>/c\<rfloor> \<ge> l0"
            hence "\<Phi> (nxt f s) = ad*(f1'*\<lfloor>l/c\<rfloor> - (n-1))" using f2' n lc' by(auto)
            hence "?A = n + ad*(f1'*\<lfloor>l/c\<rfloor> - (n-1)) - (ad*(f1'*l - n))"
              using Phi n lc' by (simp add: algebra_simps)
            also have "\<lfloor>l/c\<rfloor> \<le> l/c" by(simp)
            also have "n+ad*(f1'*(l/c)-(n-1))-(ad*(f1'*l-n)) = n+ad*(f1'/c-f1')*l+ad"
              by(simp add: algebra_simps)
            also note f1'c_le_f1
            finally have "?A \<le> ?R" by(simp add: algebra_simps)
            thus ?thesis by linarith
          next
            assume "\<not>(n-1 < f1'*\<lfloor>l/c\<rfloor> \<and> \<lfloor>\<lfloor>l/c\<rfloor>/c\<rfloor> \<ge> l0)"
            hence "\<Phi> (nxt f s) = 0" using f2' n lc' by(auto)
            hence "?A = n + ad*(n - f1'*l)" using Phi n lc'
              by (simp add: algebra_simps)
            also have "\<dots> = n + ad*(n-1 - f1'*l) + ad" by(simp add: algebra_simps)
            also have "n-1 \<le> f1*l" using n by linarith
            finally have "?A \<le> ?R" by (simp add: algebra_simps)
            thus ?thesis by linarith
          qed
        next
          assume f2': "\<not> n-1 < f2'*\<lfloor>l/c\<rfloor>"
          hence "?A = n + ai*(n-1-f2'*\<lfloor>l/c\<rfloor>) - ad*(f1'*l - n)"
            using Phi n lc' by (simp)
          also have "n-1-f2'*\<lfloor>l/c\<rfloor> \<le> f2'"
          proof -
            have "f1*l \<le> f2'*(l/c)" using f1f2'c by(simp add: field_simps)
            hence "n-1 < f2'*(l/c)" using n by linarith
            also have "l/c \<le> \<lfloor>l/c\<rfloor> + 1" by linarith
            finally show ?thesis by(fastforce simp: algebra_simps)
          qed
          also have "n+ai*f2'-ad*(f1'*l-n) = n + ad*(n-1 - f1'*l) + ad + f2'*ai"
            by(simp add: algebra_simps)
          also have "n-1 \<le> f1*l" using n by linarith
          finally show ?thesis by(simp add: algebra_simps)
        qed
        also have "\<dots> = n - f1*l + ad + f2'*ai" using f1_less_f1' by(simp add: ad_def)
        finally show ?thesis using n by simp
      qed
    qed
  qed
qed

end

locale Table2_f1f2'' = TableInv +
fixes f1'' f2'' :: real

locale Table2 = Table2_f1f2'' +
assumes f2f2'': "(f2 - f2'')*l0 \<ge> 1"
assumes f1''f1: "(f1'' - f1)*c*l0 \<ge> 1"

assumes f1_less_f1'': "f1 < f1''"
assumes f1''_less_f1': "f1'' < f1'"
assumes f2'_less_f2'': "f2' < f2''"
assumes f2''_less_f2: "f2'' < f2"
assumes f1''_f1': "l \<ge> real l0 \<Longrightarrow> f1'' * (l+1) \<le> f1'*l"
assumes f2'_f2'': "l \<ge> real l0 \<Longrightarrow> f2' * l \<le> f2'' * (l-1)"
begin

definition "ai = f2 / (f2 - f2'')"
definition "ad = f1 / (f1'' - f1)"

lemma f1''_gr0[arith]: "f1'' > 0"
using f1_less_f1'' f1 by linarith

lemma f2''_gr0[arith]: "f2'' > 0"
using f2' f2'_less_f2'' by linarith

lemma aigr0[arith]: "ai > 0"
using f2''_less_f2 by(simp add: ai_def field_simps)

lemma adgr0[arith]: "ad > 0"
using f1_less_f1'' by(simp add: ad_def field_simps)

fun \<Phi> :: "nat * nat \<Rightarrow> real" where
"\<Phi>(n,l) = (if n \<ge> f2''*l then ai*(n - f2''*l) else
  if n \<le> f1''*l \<and> l0 \<le> \<lfloor>l/c\<rfloor> then ad*(f1''*l - n) else 0)"

lemma Phi_Psi: "\<Phi> (n,l) = \<Psi> (l0 \<le> \<lfloor>l/c\<rfloor>) ai ad (f1''*l) (f2''*l) n"
by(simp)

abbreviation "U \<equiv> \<lambda>f _. case f of Ins \<Rightarrow> ai+1 | Del \<Rightarrow> ad+1"

interpretation tb: Amortized
  where init = "(0,l0)" and nxt = nxt
  and inv = invar
  and t = t and \<Phi> = \<Phi>
  and U = U
proof (standard, goal_cases)
  case 1 show ?case by (fact invar_init)
next
  case 2 thus ?case by(fact invar_pres)
next
  case (3 s) thus ?case by(cases s)(simp split: if_splits)
next
  case 4 show ?case
    by(auto simp: field_simps mult_le_0_iff le_floor_iff)
next
  case (5 s f)
  obtain n l where [simp]: "s = (n,l)" by fastforce
  show ?case
  proof (cases f)
    case [simp]: Ins
    show ?thesis (is "?L \<le> _")
    proof cases
      assume "n+1 \<le> f2*l"
      thus ?thesis by(simp del: \<Phi>.simps \<Psi>.simps add: Phi_Psi Psi_diff_Ins)
    next
      assume [arith]: "\<not> n+1 \<le> f2*l"
      have [arith]: "l \<ge> l0"  "n \<le> f2*l" using 5 by auto
      have "l0 \<le> e*l" using \<open>l0 \<le> l\<close> e1 mult_mono[of 1 e l0 l] by simp
      have "(f2 - f2'')*l \<ge> 1"
        using mult_mono[OF order_refl, of l0 l "f2-f2''"] f2''_less_f2 f2f2''
        by (simp add: algebra_simps)
      hence "n \<ge> f2''*l" by(simp add: algebra_simps)
      hence Phi: "\<Phi> s = ai * (n - f2''*l)" by simp
      have [simp]: "real (nat \<lceil>e*l\<rceil>) = real_of_int \<lceil>e*l\<rceil>"
        by (simp add: order.order_iff_strict)
      have "?L \<le> n - ai*(f2 - f2'')*l + ai + 1" (is "_ \<le> ?R")
      proof cases
        assume f2'': "n+1 < f2''*\<lceil>e*l\<rceil>"
        have "f1''*\<lceil>e*l\<rceil> \<le> f1''*(e*l + 1)" by(simp)
        also note f1''_f1'[OF \<open>l0 \<le> e*l\<close>]
        also have "f1'*(e*l) \<le> f2*l" using f1'ef2 by(simp)
        also have "f2*l \<le> n+1" by linarith
        finally have "?L \<le> n+1 - ai*(n - f2''*l)"
          using Phi f2'' by (simp)
        also have "n+1-ai*(n-f2''*l) = n+ai*(-real(n+1)+f2''*l)+ai+1"
          by(simp add: algebra_simps)
        also have "-real(n+1) \<le> -f2*l" by linarith
        finally show ?thesis by(simp add: algebra_simps)
      next
        assume "\<not> n+1 < f2''*\<lceil>e*l\<rceil>"
        hence "?L = n + ai*(-f2''*\<lceil>e*l\<rceil> + f2''*l) + ai+1" using Phi
          by(simp add: algebra_simps)
        also have "-f2''*\<lceil>e*l\<rceil> \<le> -f2''*e*l" by(simp)
        also have "-f2''*e \<le> -f2'*e" using f2'_less_f2'' by(simp)
        also have "-f2'*e \<le> -f2" using f2_le_f2'e by(simp)
        also have "n+ai*(-f2*l+f2''*l)+ai+1 \<le> ?R" by(simp add: algebra_simps)
        finally show ?thesis by(simp)
      qed
      also have "\<dots> = n - f2*l + ai+1" using f2''_less_f2
        by(simp add: ai_def)
      finally show ?thesis by simp
    qed
  next
    case [simp]: Del
    have [arith]: "l \<ge> l0" using 5 by simp
    show ?thesis
    proof cases
      assume "n=0" with 5 show ?thesis
        by(simp add: mult_le_0_iff field_simps)
    next
      assume [arith]: "n\<noteq>0"
      show ?thesis (is "?A \<le> _")
      proof cases
        assume "real n - 1 \<ge> f1*l \<or> \<lfloor>l/c\<rfloor> < l0"
        thus ?thesis using f1''_less_f1' f1'_le_f2' f2'_less_f2''
          by(auto simp del: \<Phi>.simps \<Psi>.simps simp add: Phi_Psi Psi_diff_Del)
      next
        assume "\<not> (real n - 1 \<ge> f1*l \<or> \<lfloor>l/c\<rfloor> < l0)"
        hence n: "real n - 1 < f1*l" and lc': "\<lfloor>l/c\<rfloor> \<ge> l0" and lc: "l/c \<ge> l0"
          by linarith+
        have "f1''*l \<le> f2''*l"
          using f1''_less_f1' f1'_le_f2' f2'_less_f2'' by simp
        have "(f1'' - f1)*l \<ge> 1"
          using mult_mono[OF order_refl, of l0 "l/c" "f1''-f1"] lc f1_less_f1'' f1''f1
          by (simp add: field_simps)
        hence "n < f1''*l" using n by(simp add: algebra_simps)
        hence Phi: "\<Phi> s = ad*(f1''*l - n)"
          apply(simp) using \<open>f1''*l \<le> f2''*l\<close> lc by linarith
        have f2': "n-1 < f2''*\<lfloor>l/c\<rfloor>"
        proof -
          have "n-1 < f1*l" using n by linarith
          also have "f1*l \<le> f2'*(l/c)" using f1f2'c by(auto simp: field_simps)
          also note f2'_f2''[OF \<open>l/c\<ge>l0\<close>]
          also have "f2''*(l/c - 1) \<le> f2''*\<lfloor>l/c\<rfloor>" by simp
          finally show ?thesis by(simp)
        qed
        have "?A \<le> n - ad*(f1'' - f1)*l + ad"
        proof cases
          assume "n-1 < f1''*\<lfloor>l/c\<rfloor> \<and> \<lfloor>\<lfloor>l/c\<rfloor>/c\<rfloor> \<ge> l0"
          hence "\<Phi> (nxt f s) = ad*(f1''*\<lfloor>l/c\<rfloor> - (n-1))" using f2' n lc' by(auto)
          hence "?A = n + ad*(f1''*\<lfloor>l/c\<rfloor> - (n-1)) - (ad*(f1''*l - n))"
            using Phi n lc' by (simp add: algebra_simps)
          also have "\<lfloor>l/c\<rfloor> \<le> l/c" by(simp)
          also have "n+ad*(f1''*(l/c)-(n-1))-(ad*(f1''*l-n)) = n+ad*(f1''/c-f1'')*l+ad"
            by(simp add: algebra_simps)
          also have "f1''/c \<le> f1'/c" using f1''_less_f1' by(simp add: field_simps)
          also note f1'c_le_f1
          finally show ?thesis by(simp add: algebra_simps)
        next
          assume "\<not>(n-1 < f1''*\<lfloor>l/c\<rfloor> \<and> \<lfloor>\<lfloor>l/c\<rfloor>/c\<rfloor> \<ge> l0)"
          hence "\<Phi> (nxt f s) = 0" using f2' n lc' by(auto)
          hence "?A = n + ad*(n - f1''*l)" using Phi n lc'
            by (simp add: algebra_simps)
          also have "\<dots> = n + ad*(n-1 - f1''*l) + ad" by(simp add: algebra_simps)
          also have "n-1 \<le> f1*l" using n by linarith
          finally show ?thesis by (simp add: algebra_simps)
        qed
        also have "\<dots> = n - f1*l + ad" using f1_less_f1'' by(simp add: ad_def)
        finally show ?thesis using n by simp
      qed
    qed
  qed
qed

end


locale Table3 = Table2_f1f2'' +
assumes f1''_def: "f1'' = (f1'::real)*l0/(l0+1)"
assumes f2''_def: "f2'' = (f2'::real)*l0/(l0-1)"

(* they imply (f2 - f2'')*l0 \<ge> 1 and (f1 - f1'')*l0*c \<ge> 1 *)
assumes l0_f2f2': "l0 \<ge> (f2+1)/(f2-f2')"
assumes l0_f1f1': "l0 \<ge> (f1'*c+1)/((f1'-f1)*c)"

(* they imply f1<f1'' and f2'<f2'' and l0 > 1 *)
assumes l0_f1_f1': "l0 > f1/((f1'-f1))"
assumes l0_f2_f2': "l0 > f2/(f2-f2')"
begin

lemma l0_gr1: "l0 > 1"
proof -
  have "f2/(f2-f2') \<ge> 1" using f2'_less_f2 by(simp add: field_simps)
  thus ?thesis using l0_f2_f2' f2'_less_f2 by linarith
qed

lemma f1''_less_f1': "f1'' < f1'"
by(simp add: f1''_def field_simps)

lemma f1_less_f1'': "f1 < f1''"
proof -
  have "1 + l0 > 0" by (simp add: add_pos_pos)
  hence "f1''> f1 \<longleftrightarrow> l0 > f1/((f1'-f1))"
    using f1_less_f1' by(simp add: f1''_def field_simps)
  also have "\<dots> \<longleftrightarrow> True" using l0_f1_f1' by blast
  finally show ?thesis by blast
qed

lemma f2'_less_f2'': "f2' < f2''"
using l0_gr1 by(simp add: f2''_def field_simps)

lemma f2''_less_f2: "f2'' < f2"
proof -
  have "f2''< f2 \<longleftrightarrow> l0 > f2/(f2-f2')"
    using f2'_less_f2 l0_gr1 by(simp add: f2''_def field_simps)
  also have "\<dots> \<longleftrightarrow> True" using l0_f2_f2' by blast
  finally show ?thesis by blast
qed

(* This is the real constraint we want, not l0_f2f2',
   but it involves f2'', which depends on l0 *)
lemma f2f2'': "(f2 - f2'')*l0 \<ge> 1"
proof -
  have "(f2 - f2'')*(l0-1) \<ge> 1"
    using l0_gr1 l0_f2f2' f2'_less_f2
    by(simp add: f2''_def algebra_simps del: of_nat_diff) (simp add: field_simps)
  thus ?thesis using f2''_less_f2 by (simp add: algebra_simps)
qed

(* This is the real constraint we want, not l0_f1f1',
   but it involves f1'', which depends on l0 *)
lemma f1''f1: "(f1'' - f1)*c*l0 \<ge> 1"
proof -
  have "1 \<le> (f1' - f1)*c*l0 - f1'*c" using l0_f1f1' f1_less_f1'
    by(simp add: field_simps)
  also have "\<dots> = (f1'*((l0-1)/l0) - f1)*c*l0"
    by(simp add: field_simps)
  also have "(l0-1)/l0 \<le> l0/(l0+1)"
    by(simp add: field_simps)
  also have "f1'*(l0/(l0+1)) = f1'*l0/(l0+1)"
    by(simp add: algebra_simps)
  also note f1''_def[symmetric]
  finally show ?thesis by(simp)
qed

lemma f1''_f1': assumes "l \<ge> real l0" shows "f1''*(l+1) \<le> f1' * l"
proof -
  have "f1''*(l+1) = f1'*(l0/(l0+1))*(l+1)"
    by(simp add: f1''_def field_simps)
  also have "l0/(l0+1) \<le> l/(l+1)" using assms
    by(simp add: field_simps)
  finally show ?thesis using \<open>l0 \<le> l\<close> by(simp)
qed

lemma f2'_f2'': assumes "l \<ge> real l0" shows "f2' * l \<le> f2'' * (l-1)"
proof -
  have "f2' * l = f2' * l + f2'*((l0-1)/(l0-1) - 1)" using l0_gr1 by simp
  also have "(l0-1)/(l0-1) \<le> (l-1)/(l0-1)" using \<open>l\<ge>l0\<close> by(simp)
  also have "f2'*l + f2'*((l-1)/(l0-1) - 1) = f2''*(l-1)"
    using l0_gr1 by(simp add: f2''_def field_simps)
  finally show ?thesis by simp
qed


sublocale Table2
proof
qed (fact f1_less_f1'' f1''_less_f1' f2'_less_f2'' f2''_less_f2 f1''f1 f2f2'' f1''_f1' f2'_f2'')+

end

end
