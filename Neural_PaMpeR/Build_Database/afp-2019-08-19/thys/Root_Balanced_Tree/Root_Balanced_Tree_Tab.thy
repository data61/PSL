section "Tabulating the Balanced Predicate"

theory Root_Balanced_Tree_Tab
imports
  Root_Balanced_Tree
  "HOL-Decision_Procs.Approximation"
  "HOL-Library.IArray"
begin

locale Min_tab =
fixes p :: "nat \<Rightarrow> nat \<Rightarrow> bool"
fixes tab :: "nat list"
assumes mono_p: "n \<le> n' \<Longrightarrow> p n h \<Longrightarrow> p n' h"
assumes p: "\<exists>n. p n h"
assumes tab_LEAST: "h < length tab \<Longrightarrow> tab!h = (LEAST n. p n h)"
begin

lemma tab_correct: "h < length tab \<Longrightarrow> p n h = (n \<ge> tab ! h)"
  apply auto
  using not_le_imp_less not_less_Least tab_LEAST apply auto[1]
  by (metis LeastI mono_p p tab_LEAST)

end

definition bal_tab :: "nat list" where
"bal_tab = [0, 1, 1, 2, 4, 6, 10, 16, 25, 40, 64, 101, 161, 256, 406, 645, 1024,
  1625, 2580, 4096, 6501, 10321, 16384, 26007, 41285, 65536, 104031, 165140,
  262144, 416127, 660561, 1048576, 1664510, 2642245, 4194304, 6658042, 10568983,
  16777216, 26632170, 42275935, 67108864, 106528681, 169103740, 268435456,
  426114725, 676414963, 1073741824, 1704458900, 2705659852, 4294967296\<^cancel>\<open>,
  6817835603\<close>]"
(*ML\<open>floor (Math.pow(2.0,5.0/1.5))\<close>*)

axiomatization where c_def: "c = 3/2"

fun is_floor :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
"is_floor n h = (let m = floor((2::real) powr ((real(h)-1)/c)) in n \<le> m \<and> m \<le> n)"
text\<open>Note that @{prop"n \<le> m \<and> m \<le> n"} avoids the technical restriction of the
\<open>approximation\<close> method which does not support \<open>=\<close>, even on integers.\<close>


lemma bal_tab_correct:
  "\<forall>i < length bal_tab. is_floor (bal_tab!i) i"
apply(simp add: bal_tab_def c_def All_less_Suc)
apply (approximation 50)
done

(* FIXME mv *)
lemma ceiling_least_real: "ceiling(r::real) = (LEAST i. r \<le> i)"
by (metis Least_equality ceiling_le le_of_int_ceiling)

lemma floor_greatest_real: "floor(r::real) = (GREATEST i. i \<le> r)"
by (metis Greatest_equality le_floor_iff of_int_floor_le)

lemma LEAST_eq_floor:
  "(LEAST n. int h \<le> \<lceil>c * log 2 (real n + 1)\<rceil>) = floor((2::real) powr ((real(h)-1)/c))"
proof -
  have "int h \<le> \<lceil>c * log 2 (real n + 1)\<rceil>
      \<longleftrightarrow> 2 powr ((real(h)-1)/c) < real(n)+1" (is "?L = ?R") for n
  proof -
    have "?L \<longleftrightarrow> h < c * log 2 (real n + 1) + 1" by linarith
    also have "\<dots> \<longleftrightarrow> (real h-1)/c < log 2 (real n + 1)"
      using c1 by(simp add: field_simps)
    also have "\<dots> \<longleftrightarrow> 2 powr ((real h-1)/c) < 2 powr (log 2 (real n + 1))"
      by(simp del: powr_log_cancel)
    also have "\<dots> \<longleftrightarrow> ?R"
      by(simp)
    finally show ?thesis .
  qed
  moreover have "((LEAST n::nat. r < n+1) = nat(floor r))" for r :: real
    by(rule Least_equality) linarith+
  ultimately show ?thesis by simp
qed

interpretation Min_tab
where p = bal_i and tab = bal_tab
proof(unfold bal_i_def, standard, goal_cases)
  case (1 n n' h)
  have "int h \<le> ceiling(c * log 2 (real n + 1))" by(rule 1[unfolded bal_i_def])
  also have "\<dots> \<le> ceiling(c * log 2 (real n' + 1))"
    using c1 "1"(1) by (simp add: ceiling_mono)
  finally show ?case .
next
  case (2 h)
  show ?case
  proof
    show "int h \<le> \<lceil>c * log 2 (real (2 ^ h - 1) + 1)\<rceil>"
      apply(simp add: of_nat_diff log_nat_power) using c1
      by (metis ceiling_mono ceiling_of_nat order.order_iff_strict mult.left_neutral mult_eq_0_iff of_nat_0_le_iff real_mult_le_cancel_iff1)
  qed
next
  case 3
  thus ?case using bal_tab_correct LEAST_eq_floor
     by (simp add: eq_iff[symmetric]) (metis nat_int)
qed

text\<open>Now we replace the list by an immutable array:\<close>

definition bal_array :: "nat iarray" where
"bal_array = IArray bal_tab"

text\<open>A trick for code generation: how to get rid of the precondition:\<close>

lemma bal_i_code:
  "bal_i n h =
  (if h < IArray.length bal_array then IArray.sub bal_array h \<le> n else bal_i n h)"
by (simp add: bal_array_def tab_correct)

end
