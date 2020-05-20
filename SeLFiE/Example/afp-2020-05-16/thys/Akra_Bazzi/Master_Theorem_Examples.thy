(*
  File:   Master_Theorem_Examples.thy
  Author: Manuel Eberl <eberlm@in.tum.de>

  Examples for the application of the Master theorem and related proof methods.
*)

section \<open>Examples\<close>
theory Master_Theorem_Examples
imports
  Complex_Main
  Akra_Bazzi_Method
  Akra_Bazzi_Approximation
begin

subsection \<open>Merge sort\<close>

(* A merge sort cost function that is parametrised with the recombination costs *)
function merge_sort_cost :: "(nat \<Rightarrow> real) \<Rightarrow> nat \<Rightarrow> real" where
  "merge_sort_cost t 0 = 0"
| "merge_sort_cost t 1 = 1"
| "n \<ge> 2 \<Longrightarrow> merge_sort_cost t n = 
     merge_sort_cost t (nat \<lfloor>real n / 2\<rfloor>) + merge_sort_cost t (nat \<lceil>real n / 2\<rceil>) + t n"
by force simp_all
termination by akra_bazzi_termination simp_all

lemma merge_sort_nonneg[simp]: "(\<And>n. t n \<ge> 0) \<Longrightarrow> merge_sort_cost t x \<ge> 0"
  by (induction t x rule: merge_sort_cost.induct) (simp_all del: One_nat_def)

lemma "t \<in> \<Theta>(\<lambda>n. real n) \<Longrightarrow> (\<And>n. t n \<ge> 0) \<Longrightarrow> merge_sort_cost t \<in> \<Theta>(\<lambda>n. real n * ln (real n))"
  by (master_theorem 2.3) simp_all

subsection \<open>Karatsuba multiplication\<close>

function karatsuba_cost :: "nat \<Rightarrow> real" where
  "karatsuba_cost 0 = 0"
| "karatsuba_cost 1 = 1"
| "n \<ge> 2 \<Longrightarrow> karatsuba_cost n = 
     3 * karatsuba_cost (nat \<lceil>real n / 2\<rceil>) + real n"
by force simp_all
termination by akra_bazzi_termination simp_all

lemma karatsuba_cost_nonneg[simp]: "karatsuba_cost n \<ge> 0"
  by (induction n rule: karatsuba_cost.induct) (simp_all del: One_nat_def)

lemma "karatsuba_cost \<in> O(\<lambda>n. real n powr log 2 3)"
   by (master_theorem 1 p': 1) (simp_all add: powr_divide)

lemma karatsuba_cost_pos: "n \<ge> 1 \<Longrightarrow> karatsuba_cost n > 0"
  by (induction n rule: karatsuba_cost.induct) (auto intro!: add_nonneg_pos simp del: One_nat_def)

lemma "karatsuba_cost \<in> \<Theta>(\<lambda>n. real n powr log 2 3)"
  using karatsuba_cost_pos
  by (master_theorem 1 p': 1) (auto simp add: powr_divide eventually_at_top_linorder)


subsection \<open>Strassen matrix multiplication\<close>

function strassen_cost :: "nat \<Rightarrow> real" where
  "strassen_cost 0 = 0"
| "strassen_cost 1 = 1"
| "n \<ge> 2 \<Longrightarrow> strassen_cost n = 7 * strassen_cost (nat \<lceil>real n / 2\<rceil>) + real (n^2)"
by force simp_all
termination by akra_bazzi_termination simp_all

lemma strassen_cost_nonneg[simp]: "strassen_cost n \<ge> 0"
  by (induction n rule: strassen_cost.induct) (simp_all del: One_nat_def)

lemma "strassen_cost \<in> O(\<lambda>n. real n powr log 2 7)"
  by (master_theorem 1 p': 2) (auto simp: powr_divide eventually_at_top_linorder)

lemma strassen_cost_pos: "n \<ge> 1 \<Longrightarrow> strassen_cost n > 0"
  by (cases n rule: strassen_cost.cases) (simp_all add: add_nonneg_pos del: One_nat_def)

lemma "strassen_cost \<in> \<Theta>(\<lambda>n. real n powr log 2 7)"
  using strassen_cost_pos
  by (master_theorem 1 p': 2) (auto simp: powr_divide eventually_at_top_linorder)


subsection \<open>Deterministic select\<close>

(* This is not possible with the standard Master theorem from literature *)
function select_cost :: "nat \<Rightarrow> real" where
  "n \<le> 20 \<Longrightarrow> select_cost n = 0"
| "n > 20 \<Longrightarrow> select_cost n = 
     select_cost (nat \<lfloor>real n / 5\<rfloor>) + select_cost (nat \<lfloor>7 * real n / 10\<rfloor> + 6) + 12 * real n / 5"
by force simp_all
termination by akra_bazzi_termination simp_all

lemma "select_cost \<in> \<Theta>(\<lambda>n. real n)"
  by (master_theorem 3) auto


subsection \<open>Decreasing function\<close>

function dec_cost :: "nat \<Rightarrow> real" where
  "n \<le> 2 \<Longrightarrow> dec_cost n = 1"
| "n > 2 \<Longrightarrow> dec_cost n = 0.5*dec_cost (nat \<lfloor>real n / 2\<rfloor>) + 1 / real n"
by force simp_all
termination by akra_bazzi_termination simp_all

lemma "dec_cost \<in> \<Theta>(\<lambda>x::nat. ln x / x)"
  by (master_theorem 2.3) simp_all


subsection \<open>Example taken from Drmota and Szpakowski\<close>

function drmota1 :: "nat \<Rightarrow> real" where
  "n < 20 \<Longrightarrow> drmota1 n = 1"
| "n \<ge> 20 \<Longrightarrow> drmota1 n = 2 * drmota1 (nat \<lfloor>real n/2\<rfloor>) + 8/9 * drmota1 (nat \<lfloor>3*real n/4\<rfloor>) + real n^2 / ln (real n)"
by force simp_all
termination by akra_bazzi_termination simp_all

lemma "drmota1 \<in> \<Theta>(\<lambda>n::real. n^2 * ln (ln n))"
  by (master_theorem 2.2) (simp_all add: power_divide)


function drmota2 :: "nat \<Rightarrow> real" where
  "n < 20 \<Longrightarrow> drmota2 n = 1"
| "n \<ge> 20 \<Longrightarrow> drmota2 n = 1/3 * drmota2 (nat \<lfloor>real n/3 + 1/2\<rfloor>) + 2/3 * drmota2 (nat \<lfloor>2*real n/3 - 1/2\<rfloor>) + 1"
by force simp_all
termination by akra_bazzi_termination simp_all

lemma "drmota2 \<in> \<Theta>(\<lambda>x. ln (real x))"
  by master_theorem simp_all

(* Average phrase length of Boncelet arithmetic coding. See Drmota and Szpankowski. *)
lemma boncelet_phrase_length:
  fixes p \<delta> :: real assumes p: "p > 0" "p < 1" and \<delta>: "\<delta> > 0" "\<delta> < 1" "2*p + \<delta> < 2"
  fixes d :: "nat \<Rightarrow> real"
  defines "q \<equiv> 1 - p"
  assumes d_nonneg: "\<And>n. d n \<ge> 0"
  assumes d_rec: "\<And>n. n \<ge> 2 \<Longrightarrow> d n = 1 + p * d (nat \<lfloor>p * real n + \<delta>\<rfloor>) + q * d (nat \<lfloor>q * real n - \<delta>\<rfloor>)"
  shows   "d \<in> \<Theta>(\<lambda>x. ln x)"
  using assms by (master_theorem recursion: d_rec, simp_all)



subsection \<open>Transcendental exponents\<close>

(* Certain number-theoretic conjectures would imply that if all the parameters are rational,
   the Akra-Bazzi parameter is either rational or transcendental. That makes this case 
   probably transcendental *)
function foo_cost :: "nat \<Rightarrow> real" where
  "n < 200 \<Longrightarrow> foo_cost n = 0"
| "n \<ge> 200 \<Longrightarrow> foo_cost n = 
     foo_cost (nat \<lfloor>real n / 3\<rfloor>) + foo_cost (nat \<lfloor>3 * real n / 4\<rfloor> + 42) + real n"
by force simp_all
termination by akra_bazzi_termination simp_all

lemma foo_cost_nonneg [simp]: "foo_cost n \<ge> 0"
  by (induction n rule: foo_cost.induct) simp_all

lemma "foo_cost \<in> \<Theta>(\<lambda>n. real n powr akra_bazzi_exponent [1,1] [1/3,3/4])"
proof (master_theorem 1 p': 1) 
  have "\<forall>n\<ge>200. foo_cost n > 0" by (simp add: add_nonneg_pos)
  thus "eventually (\<lambda>n. foo_cost n > 0) at_top" unfolding eventually_at_top_linorder by blast
qed simp_all

lemma "akra_bazzi_exponent [1,1] [1/3,3/4] \<in> {1.1519623..1.1519624}"
  by (akra_bazzi_approximate 29)


subsection \<open>Functions in locale contexts\<close>

locale det_select =
  fixes b :: real
  assumes b: "b > 0" "b < 7/10"
begin

function select_cost' :: "nat \<Rightarrow> real" where
  "n \<le> 20 \<Longrightarrow> select_cost' n = 0"
| "n > 20 \<Longrightarrow> select_cost' n = 
     select_cost' (nat \<lfloor>real n / 5\<rfloor>) + select_cost' (nat \<lfloor>b * real n\<rfloor> + 6) + 6 * real n + 5"
by force simp_all
termination using b by akra_bazzi_termination simp_all

lemma "a \<ge> 0 \<Longrightarrow> select_cost' \<in> \<Theta>(\<lambda>n. real n)"
  using b by (master_theorem 3, force+)

end


subsection \<open>Non-curried functions\<close>

(* Note: either a or b could be seen as recursion variables. *)
function baz_cost :: "nat \<times> nat \<Rightarrow> real" where
  "n \<le> 2 \<Longrightarrow> baz_cost (a, n) = 0"
| "n > 2 \<Longrightarrow> baz_cost (a, n) = 3 * baz_cost (a, nat \<lfloor>real n / 2\<rfloor>) + real a"
by force simp_all
termination by akra_bazzi_termination simp_all

lemma baz_cost_nonneg [simp]: "a \<ge> 0 \<Longrightarrow> baz_cost (a, n) \<ge> 0"
  by (induction a n rule: baz_cost.induct[split_format (complete)]) simp_all

lemma
  assumes "a > 0"
  shows   "(\<lambda>x. baz_cost (a, x)) \<in> \<Theta>(\<lambda>x. x powr log 2 3)"
proof (master_theorem 1 p': 0)
  from assms have "\<forall>x\<ge>3. baz_cost (a, x) > 0" by (auto intro: add_nonneg_pos)
  thus "eventually (\<lambda>x. baz_cost (a, x) > 0) at_top" by (force simp: eventually_at_top_linorder)
qed (insert assms, simp_all add: powr_divide)

(* Non-"Akra-Bazzi" variables may even be modified without impacting the termination proof.
   However, the Akra-Bazzi theorem and the Master theorem itself do not apply anymore, 
   because bar_cost cannot be seen as a recursive function with one parameter *)
function bar_cost :: "nat \<times> nat \<Rightarrow> real" where
  "n \<le> 2 \<Longrightarrow> bar_cost (a, n) = 0"
| "n > 2 \<Longrightarrow> bar_cost (a, n) = 3 * bar_cost (2 * a, nat \<lfloor>real n / 2\<rfloor>) + real a"
by force simp_all
termination by akra_bazzi_termination simp_all


subsection \<open>Ham-sandwich trees\<close>
(* f(n) = f(n/4) + f(n/2) + 1 *)
function ham_sandwich_cost :: "nat \<Rightarrow> real" where
  "n < 4 \<Longrightarrow> ham_sandwich_cost n = 1"
| "n \<ge> 4 \<Longrightarrow> ham_sandwich_cost n = 
      ham_sandwich_cost (nat \<lfloor>n/4\<rfloor>) + ham_sandwich_cost (nat \<lfloor>n/2\<rfloor>) + 1"
by force simp_all
termination by akra_bazzi_termination simp_all

lemma ham_sandwich_cost_pos [simp]: "ham_sandwich_cost n > 0"
  by (induction n rule: ham_sandwich_cost.induct) simp_all


text \<open>The golden ratio\<close>

definition "\<phi> = ((1 + sqrt 5) / 2 :: real)"

lemma \<phi>_pos [simp]: "\<phi> > 0" and \<phi>_nonneg [simp]: "\<phi> \<ge> 0" and \<phi>_nonzero [simp]: "\<phi> \<noteq> 0"
proof-
  show "\<phi> > 0" unfolding \<phi>_def by (simp add: add_pos_nonneg)
  thus "\<phi> \<ge> 0" "\<phi> \<noteq> 0" by simp_all
qed


lemma "ham_sandwich_cost \<in> \<Theta>(\<lambda>n. n powr (log 2 \<phi>))"
proof (master_theorem 1 p': 0)
  have "(1 / 4) powr log 2 \<phi> + (1 / 2) powr log 2 \<phi> =
            inverse (2 powr log 2 \<phi>)^2 + inverse (2 powr log 2 \<phi>)"
        by (simp add: powr_divide field_simps powr_powr power2_eq_square powr_mult[symmetric]
                 del: powr_log_cancel)
  also have "... = inverse (\<phi>^2) + inverse \<phi>" by (simp add: power2_eq_square)
  also have "\<phi> + 1 = \<phi>*\<phi>" by (simp add: \<phi>_def field_simps)
  hence "inverse (\<phi>^2) + inverse \<phi> = 1" by (simp add: field_simps power2_eq_square)
  finally show "(1 / 4) powr log 2 \<phi> + (1 / 2) powr log 2 \<phi> = 1" by simp
qed simp_all

end
