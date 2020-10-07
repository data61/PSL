(* Title: thys/Recs.thy
   Author: Christian Urban
*)
theory Recs
  imports Main
    "HOL-Library.Nat_Bijection"
    "HOL-Library.Discrete"
begin


text\<open>
  A more streamlined and cleaned-up version of Recursive
  Functions following

    A Course in Formal Languages, Automata and Groups
    I. M. Chiswell

  and

    Lecture on Undecidability
    Michael M. Wolf
\<close>

declare One_nat_def[simp del]


lemma if_zero_one [simp]:
  "(if P then 1 else 0) = (0::nat) \<longleftrightarrow> \<not> P"
  "(0::nat) < (if P then 1 else 0) = P"
  "(if P then 0 else 1) = (if \<not>P then 1 else (0::nat))"
  by (simp_all)

lemma nth:
  "(x # xs) ! 0 = x"
  "(x # y # xs) ! 1 = y"
  "(x # y # z # xs) ! 2 = z"
  "(x # y # z # u # xs) ! 3 = u"
  by (simp_all)


section \<open>Some auxiliary lemmas about \<open>\<Sum>\<close> and \<open>\<Prod>\<close>\<close>

lemma setprod_atMost_Suc[simp]:
  "(\<Prod>i \<le> Suc n. f i) = (\<Prod>i \<le> n. f i) * f(Suc n)"
  by(simp add:atMost_Suc mult_ac)

lemma setprod_lessThan_Suc[simp]:
  "(\<Prod>i < Suc n. f i) = (\<Prod>i < n. f i) * f n"
  by (simp add:lessThan_Suc mult_ac)

lemma setsum_add_nat_ivl2: "n \<le> p  \<Longrightarrow>
  sum f {..<n} + sum f {n..p} = sum f {..p::nat}"
  apply(subst sum.union_disjoint[symmetric])
     apply(auto simp add: ivl_disj_un_one)
  done

lemma setsum_eq_zero [simp]:
  fixes f::"nat \<Rightarrow> nat"
  shows "(\<Sum>i < n. f i) = 0 \<longleftrightarrow> (\<forall>i < n. f i = 0)"
    "(\<Sum>i \<le> n. f i) = 0 \<longleftrightarrow> (\<forall>i \<le> n. f i = 0)"
  by (auto)

lemma setprod_eq_zero [simp]:
  fixes f::"nat \<Rightarrow> nat"
  shows "(\<Prod>i < n. f i) = 0 \<longleftrightarrow> (\<exists>i < n. f i = 0)"
    "(\<Prod>i \<le> n. f i) = 0 \<longleftrightarrow> (\<exists>i \<le> n. f i = 0)"
  by (auto)

lemma setsum_one_less:
  fixes n::nat
  assumes "\<forall>i < n. f i \<le> 1"
  shows "(\<Sum>i < n. f i) \<le> n"
  using assms
  by (induct n) (auto)

lemma setsum_one_le:
  fixes n::nat
  assumes "\<forall>i \<le> n. f i \<le> 1"
  shows "(\<Sum>i \<le> n. f i) \<le> Suc n"
  using assms
  by (induct n) (auto)

lemma setsum_eq_one_le:
  fixes n::nat
  assumes "\<forall>i \<le> n. f i = 1"
  shows "(\<Sum>i \<le> n. f i) = Suc n"
  using assms
  by (induct n) (auto)

lemma setsum_least_eq:
  fixes f::"nat \<Rightarrow> nat"
  assumes h0: "p \<le> n"
  assumes h1: "\<forall>i \<in> {..<p}. f i = 1"
  assumes h2: "\<forall>i \<in> {p..n}. f i = 0"
  shows "(\<Sum>i \<le> n. f i) = p"
proof -
  have eq_p: "(\<Sum>i \<in> {..<p}. f i) = p"
    using h1 by (induct p) (simp_all)
  have eq_zero: "(\<Sum>i \<in> {p..n}. f i) = 0"
    using h2 by auto
  have "(\<Sum>i \<le> n. f i) = (\<Sum>i \<in> {..<p}. f i) + (\<Sum>i \<in> {p..n}. f i)"
    using h0 by (simp add: setsum_add_nat_ivl2)
  also have "... = (\<Sum>i \<in> {..<p}. f i)" using eq_zero by simp
  finally show "(\<Sum>i \<le> n. f i) = p" using eq_p by simp
qed

lemma nat_mult_le_one:
  fixes m n::nat
  assumes "m \<le> 1" "n \<le> 1"
  shows "m * n \<le> 1"
  using assms by (induct n) (auto)

lemma setprod_one_le:
  fixes f::"nat \<Rightarrow> nat"
  assumes "\<forall>i \<le> n. f i \<le> 1"
  shows "(\<Prod>i \<le> n. f i) \<le> 1"
  using assms
  by (induct n) (auto intro: nat_mult_le_one)

lemma setprod_greater_zero:
  fixes f::"nat \<Rightarrow> nat"
  assumes "\<forall>i \<le> n. f i \<ge> 0"
  shows "(\<Prod>i \<le> n. f i) \<ge> 0"
  using assms by (induct n) (auto)

lemma setprod_eq_one:
  fixes f::"nat \<Rightarrow> nat"
  assumes "\<forall>i \<le> n. f i = Suc 0"
  shows "(\<Prod>i \<le> n. f i) = Suc 0"
  using assms by (induct n) (auto)

lemma setsum_cut_off_less:
  fixes f::"nat \<Rightarrow> nat"
  assumes h1: "m \<le> n"
    and     h2: "\<forall>i \<in> {m..<n}. f i = 0"
  shows "(\<Sum>i < n. f i) = (\<Sum>i < m. f i)"
proof -
  have eq_zero: "(\<Sum>i \<in> {m..<n}. f i) = 0"
    using h2 by auto
  have "(\<Sum>i < n. f i) = (\<Sum>i \<in> {..<m}. f i) + (\<Sum>i \<in> {m..<n}. f i)"
    using h1 by (metis atLeast0LessThan le0 sum.atLeastLessThan_concat)
  also have "... = (\<Sum>i \<in> {..<m}. f i)" using eq_zero by simp
  finally show "(\<Sum>i < n. f i) = (\<Sum>i < m. f i)" by simp
qed

lemma setsum_cut_off_le:
  fixes f::"nat \<Rightarrow> nat"
  assumes h1: "m \<le> n"
    and     h2: "\<forall>i \<in> {m..n}. f i = 0"
  shows "(\<Sum>i \<le> n. f i) = (\<Sum>i < m. f i)"
proof -
  have eq_zero: "(\<Sum>i \<in> {m..n}. f i) = 0"
    using h2 by auto
  have "(\<Sum>i \<le> n. f i) = (\<Sum>i \<in> {..<m}. f i) + (\<Sum>i \<in> {m..n}. f i)"
    using h1 by (simp add: setsum_add_nat_ivl2)
  also have "... = (\<Sum>i \<in> {..<m}. f i)" using eq_zero by simp
  finally show "(\<Sum>i \<le> n. f i) = (\<Sum>i < m. f i)" by simp
qed

lemma setprod_one [simp]:
  fixes n::nat
  shows "(\<Prod>i < n. Suc 0) = Suc 0"
    "(\<Prod>i \<le> n. Suc 0) = Suc 0"
  by (induct n) (simp_all)



section \<open>Recursive Functions\<close>

datatype recf =  Z
  |  S
  |  Id nat nat
  |  Cn nat recf "recf list"
  |  Pr nat recf recf
  |  Mn nat recf

fun arity :: "recf \<Rightarrow> nat"
  where
    "arity Z = 1"
  | "arity S = 1"
  | "arity (Id m n) = m"
  | "arity (Cn n f gs) = n"
  | "arity (Pr n f g) = Suc n"
  | "arity (Mn n f) = n"

text \<open>Abbreviations for calculating the arity of the constructors\<close>

abbreviation
  "CN f gs \<equiv> Cn (arity (hd gs)) f gs"

abbreviation
  "PR f g \<equiv> Pr (arity f) f g"

abbreviation
  "MN f \<equiv> Mn (arity f - 1) f"

text \<open>the evaluation function and termination relation\<close>

fun rec_eval :: "recf \<Rightarrow> nat list \<Rightarrow> nat"
  where
    "rec_eval Z xs = 0"
  | "rec_eval S xs = Suc (xs ! 0)"
  | "rec_eval (Id m n) xs = xs ! n"
  | "rec_eval (Cn n f gs) xs = rec_eval f (map (\<lambda>x. rec_eval x xs) gs)"
  | "rec_eval (Pr n f g) (0 # xs) = rec_eval f xs"
  | "rec_eval (Pr n f g) (Suc x # xs) =
     rec_eval g (x # (rec_eval (Pr n f g) (x # xs)) # xs)"
  | "rec_eval (Mn n f) xs = (LEAST x. rec_eval f (x # xs) = 0)"

inductive
  terminates :: "recf \<Rightarrow> nat list \<Rightarrow> bool"
  where
    termi_z: "terminates Z [n]"
  | termi_s: "terminates S [n]"
  | termi_id: "\<lbrakk>n < m; length xs = m\<rbrakk> \<Longrightarrow> terminates (Id m n) xs"
  | termi_cn: "\<lbrakk>terminates f (map (\<lambda>g. rec_eval g xs) gs);
              \<forall>g \<in> set gs. terminates g xs; length xs = n\<rbrakk> \<Longrightarrow> terminates (Cn n f gs) xs"
  | termi_pr: "\<lbrakk>\<forall> y < x. terminates g (y # (rec_eval (Pr n f g) (y # xs) # xs));
              terminates f xs;
              length xs = n\<rbrakk>
              \<Longrightarrow> terminates (Pr n f g) (x # xs)"
  | termi_mn: "\<lbrakk>length xs = n; terminates f (r # xs);
              rec_eval f (r # xs) = 0;
              \<forall> i < r. terminates f (i # xs) \<and> rec_eval f (i # xs) > 0\<rbrakk> \<Longrightarrow> terminates (Mn n f) xs"


section \<open>Arithmetic Functions\<close>

text \<open>
  \<open>constn n\<close> is the recursive function which computes
  natural number \<open>n\<close>.
\<close>
fun constn :: "nat \<Rightarrow> recf"
  where
    "constn 0 = Z"  |
    "constn (Suc n) = CN S [constn n]"

definition
  "rec_swap f = CN f [Id 2 1, Id 2 0]"

definition
  "rec_add = PR (Id 1 0) (CN S [Id 3 1])"

definition
  "rec_mult = PR Z (CN rec_add [Id 3 1, Id 3 2])"

definition
  "rec_power = rec_swap (PR (constn 1) (CN rec_mult [Id 3 1, Id 3 2]))"

definition
  "rec_fact_aux = PR (constn 1) (CN rec_mult [CN S [Id 3 0], Id 3 1])"

definition
  "rec_fact = CN rec_fact_aux [Id 1 0, Id 1 0]"

definition
  "rec_predecessor = CN (PR Z (Id 3 0)) [Id 1 0, Id 1 0]"

definition
  "rec_minus = rec_swap (PR (Id 1 0) (CN rec_predecessor [Id 3 1]))"

lemma constn_lemma [simp]:
  "rec_eval (constn n) xs = n"
  by (induct n) (simp_all)

lemma swap_lemma [simp]:
  "rec_eval (rec_swap f) [x, y] = rec_eval f [y, x]"
  by (simp add: rec_swap_def)

lemma add_lemma [simp]:
  "rec_eval rec_add [x, y] =  x + y"
  by (induct x) (simp_all add: rec_add_def)

lemma mult_lemma [simp]:
  "rec_eval rec_mult [x, y] = x * y"
  by (induct x) (simp_all add: rec_mult_def)

lemma power_lemma [simp]:
  "rec_eval rec_power [x, y] = x ^ y"
  by (induct y) (simp_all add: rec_power_def)

lemma fact_aux_lemma [simp]:
  "rec_eval rec_fact_aux [x, y] = fact x"
  by (induct x) (simp_all add: rec_fact_aux_def)

lemma fact_lemma [simp]:
  "rec_eval rec_fact [x] = fact x"
  by (simp add: rec_fact_def)

lemma pred_lemma [simp]:
  "rec_eval rec_predecessor [x] =  x - 1"
  by (induct x) (simp_all add: rec_predecessor_def)

lemma minus_lemma [simp]:
  "rec_eval rec_minus [x, y] = x - y"
  by (induct y) (simp_all add: rec_minus_def)


section \<open>Logical functions\<close>

text \<open>
  The \<open>sign\<close> function returns 1 when the input argument
  is greater than \<open>0\<close>.\<close>

definition
  "rec_sign = CN rec_minus [constn 1, CN rec_minus [constn 1, Id 1 0]]"

definition
  "rec_not = CN rec_minus [constn 1, Id 1 0]"

text \<open>
  \<open>rec_eq\<close> compares two arguments: returns \<open>1\<close>
  if they are equal; \<open>0\<close> otherwise.\<close>
definition
  "rec_eq = CN rec_minus [CN (constn 1) [Id 2 0], CN rec_add [rec_minus, rec_swap rec_minus]]"

definition
  "rec_noteq = CN rec_not [rec_eq]"

definition
  "rec_conj = CN rec_sign [rec_mult]"

definition
  "rec_disj = CN rec_sign [rec_add]"

definition
  "rec_imp = CN rec_disj [CN rec_not [Id 2 0], Id 2 1]"

text \<open>@{term "rec_ifz [z, x, y]"} returns x if z is zero,
  y otherwise;  @{term "rec_if [z, x, y]"} returns x if z is *not*
  zero, y otherwise\<close>

definition
  "rec_ifz = PR (Id 2 0) (Id 4 3)"

definition
  "rec_if = CN rec_ifz [CN rec_not [Id 3 0], Id 3 1, Id 3 2]"


lemma sign_lemma [simp]:
  "rec_eval rec_sign [x] = (if x = 0 then 0 else 1)"
  by (simp add: rec_sign_def)

lemma not_lemma [simp]:
  "rec_eval rec_not [x] = (if x = 0 then 1 else 0)"
  by (simp add: rec_not_def)

lemma eq_lemma [simp]:
  "rec_eval rec_eq [x, y] = (if x = y then 1 else 0)"
  by (simp add: rec_eq_def)

lemma noteq_lemma [simp]:
  "rec_eval rec_noteq [x, y] = (if x \<noteq> y then 1 else 0)"
  by (simp add: rec_noteq_def)

lemma conj_lemma [simp]:
  "rec_eval rec_conj [x, y] = (if x = 0 \<or> y = 0 then 0 else 1)"
  by (simp add: rec_conj_def)

lemma disj_lemma [simp]:
  "rec_eval rec_disj [x, y] = (if x = 0 \<and> y = 0 then 0 else 1)"
  by (simp add: rec_disj_def)

lemma imp_lemma [simp]:
  "rec_eval rec_imp [x, y] = (if 0 < x \<and> y = 0 then 0 else 1)"
  by (simp add: rec_imp_def)

lemma ifz_lemma [simp]:
  "rec_eval rec_ifz [z, x, y] = (if z = 0 then x else y)"
  by (cases z) (simp_all add: rec_ifz_def)

lemma if_lemma [simp]:
  "rec_eval rec_if [z, x, y] = (if 0 < z then x else y)"
  by (simp add: rec_if_def)

section \<open>Less and Le Relations\<close>

text \<open>
  \<open>rec_less\<close> compares two arguments and returns \<open>1\<close> if
  the first is less than the second; otherwise returns \<open>0\<close>.\<close>

definition
  "rec_less = CN rec_sign [rec_swap rec_minus]"

definition
  "rec_le = CN rec_disj [rec_less, rec_eq]"

lemma less_lemma [simp]:
  "rec_eval rec_less [x, y] = (if x < y then 1 else 0)"
  by (simp add: rec_less_def)

lemma le_lemma [simp]:
  "rec_eval rec_le [x, y] = (if (x \<le> y) then 1 else 0)"
  by(simp add: rec_le_def)


section \<open>Summation and Product Functions\<close>

definition
  "rec_sigma1 f = PR (CN f [CN Z [Id 1 0], Id 1 0])
                     (CN rec_add [Id 3 1, CN f [CN S [Id 3 0], Id 3 2]])"

definition
  "rec_sigma2 f = PR (CN f [CN Z [Id 2 0], Id 2 0, Id 2 1])
                     (CN rec_add [Id 4 1, CN f [CN S [Id 4 0], Id 4 2, Id 4 3]])"

definition
  "rec_accum1 f = PR (CN f [CN Z [Id 1 0], Id 1 0])
                     (CN rec_mult [Id 3 1, CN f [CN S [Id 3 0], Id 3 2]])"

definition
  "rec_accum2 f = PR (CN f [CN Z [Id 2 0], Id 2 0, Id 2 1])
                     (CN rec_mult [Id 4 1, CN f [CN S [Id 4 0], Id 4 2, Id 4 3]])"

definition
  "rec_accum3 f = PR (CN f [CN Z [Id 3 0], Id 3 0, Id 3 1, Id 3 2])
                     (CN rec_mult [Id 5 1, CN f [CN S [Id 5 0], Id 5 2, Id 5 3, Id 5 4]])"


lemma sigma1_lemma [simp]:
  shows "rec_eval (rec_sigma1 f) [x, y] = (\<Sum> z \<le> x. rec_eval f [z, y])"
  by (induct x) (simp_all add: rec_sigma1_def)

lemma sigma2_lemma [simp]:
  shows "rec_eval (rec_sigma2 f) [x, y1, y2] = (\<Sum> z \<le> x. rec_eval f  [z, y1, y2])"
  by (induct x) (simp_all add: rec_sigma2_def)

lemma accum1_lemma [simp]:
  shows "rec_eval (rec_accum1 f) [x, y] = (\<Prod> z \<le> x. rec_eval f  [z, y])"
  by (induct x) (simp_all add: rec_accum1_def)

lemma accum2_lemma [simp]:
  shows "rec_eval (rec_accum2 f) [x, y1, y2] = (\<Prod> z \<le> x. rec_eval f  [z, y1, y2])"
  by (induct x) (simp_all add: rec_accum2_def)

lemma accum3_lemma [simp]:
  shows "rec_eval (rec_accum3 f) [x, y1, y2, y3] = (\<Prod> z \<le> x. (rec_eval f)  [z, y1, y2, y3])"
  by (induct x) (simp_all add: rec_accum3_def)


section \<open>Bounded Quantifiers\<close>

definition
  "rec_all1 f = CN rec_sign [rec_accum1 f]"

definition
  "rec_all2 f = CN rec_sign [rec_accum2 f]"

definition
  "rec_all3 f = CN rec_sign [rec_accum3 f]"

definition
  "rec_all1_less f = (let cond1 = CN rec_eq [Id 3 0, Id 3 1] in
                      let cond2 = CN f [Id 3 0, Id 3 2]
                      in CN (rec_all2 (CN rec_disj [cond1, cond2])) [Id 2 0, Id 2 0, Id 2 1])"

definition
  "rec_all2_less f = (let cond1 = CN rec_eq [Id 4 0, Id 4 1] in
                      let cond2 = CN f [Id 4 0, Id 4 2, Id 4 3] in
                      CN (rec_all3 (CN rec_disj [cond1, cond2])) [Id 3 0, Id 3 0, Id 3 1, Id 3 2])"

definition
  "rec_ex1 f = CN rec_sign [rec_sigma1 f]"

definition
  "rec_ex2 f = CN rec_sign [rec_sigma2 f]"


lemma ex1_lemma [simp]:
  "rec_eval (rec_ex1 f) [x, y] = (if (\<exists>z \<le> x. 0 < rec_eval f [z, y]) then 1 else 0)"
  by (simp add: rec_ex1_def)

lemma ex2_lemma [simp]:
  "rec_eval (rec_ex2 f) [x, y1, y2] = (if (\<exists>z \<le> x. 0 < rec_eval f [z, y1, y2]) then 1 else 0)"
  by (simp add: rec_ex2_def)

lemma all1_lemma [simp]:
  "rec_eval (rec_all1 f) [x, y] = (if (\<forall>z \<le> x. 0 < rec_eval f [z, y]) then 1 else 0)"
  by (simp add: rec_all1_def)

lemma all2_lemma [simp]:
  "rec_eval (rec_all2 f) [x, y1, y2] = (if (\<forall>z \<le> x. 0 < rec_eval f [z, y1, y2]) then 1 else 0)"
  by (simp add: rec_all2_def)

lemma all3_lemma [simp]:
  "rec_eval (rec_all3 f) [x, y1, y2, y3] = (if (\<forall>z \<le> x. 0 < rec_eval f [z, y1, y2, y3]) then 1 else 0)"
  by (simp add: rec_all3_def)

lemma all1_less_lemma [simp]:
  "rec_eval (rec_all1_less f) [x, y] = (if (\<forall>z < x. 0 < rec_eval f [z, y]) then 1 else 0)"
  apply(auto simp add: Let_def rec_all1_less_def)
   apply (metis nat_less_le)+
  done

lemma all2_less_lemma [simp]:
  "rec_eval (rec_all2_less f) [x, y1, y2] = (if (\<forall>z < x. 0 < rec_eval f [z, y1, y2]) then 1 else 0)"
  apply(auto simp add: Let_def rec_all2_less_def)
   apply(metis nat_less_le)+
  done

section \<open>Quotients\<close>

definition
  "rec_quo = (let lhs = CN S [Id 3 0] in
              let rhs = CN rec_mult [Id 3 2, CN S [Id 3 1]] in
              let cond = CN rec_eq [lhs, rhs] in
              let if_stmt = CN rec_if [cond, CN S [Id 3 1], Id 3 1]
              in PR Z if_stmt)"

fun Quo where
  "Quo x 0 = 0"
| "Quo x (Suc y) = (if (Suc y = x * (Suc (Quo x y))) then Suc (Quo x y) else Quo x y)"

lemma Quo0:
  shows "Quo 0 y = 0"
  by (induct y) (auto)

lemma Quo1:
  "x * (Quo x y) \<le> y"
  by (induct y) (simp_all)

lemma Quo2:
  "b * (Quo b a) + a mod b = a"
  by (induct a) (auto simp add: mod_Suc)

lemma Quo3:
  "n * (Quo n m) = m - m mod n"
  using Quo2[of n m] by (auto)

lemma Quo4:
  assumes h: "0 < x"
  shows "y < x + x * Quo x y"
proof -
  have "x - (y mod x) > 0" using mod_less_divisor assms by auto
  then have "y < y + (x - (y mod x))" by simp
  then have "y < x + (y - (y mod x))" by simp
  then show "y < x + x * (Quo x y)" by (simp add: Quo3)
qed

lemma Quo_div:
  shows "Quo x y = y div x"
  by (metis Quo0 Quo1 Quo4 div_by_0 div_nat_eqI mult_Suc_right neq0_conv)

lemma Quo_rec_quo:
  shows "rec_eval rec_quo [y, x] = Quo x y"
  by (induct y) (simp_all add: rec_quo_def)

lemma quo_lemma [simp]:
  shows "rec_eval rec_quo [y, x] = y div x"
  by (simp add: Quo_div Quo_rec_quo)


section \<open>Iteration\<close>

definition
  "rec_iter f = PR (Id 1 0) (CN f [Id 3 1])"

fun Iter where
  "Iter f 0 = id"
| "Iter f (Suc n) = f \<circ> (Iter f n)"

lemma Iter_comm:
  "(Iter f n) (f x) = f ((Iter f n) x)"
  by (induct n) (simp_all)

lemma iter_lemma [simp]:
  "rec_eval (rec_iter f) [n, x] =  Iter (\<lambda>x. rec_eval f [x]) n x"
  by (induct n) (simp_all add: rec_iter_def)


section \<open>Bounded Maximisation\<close>


fun BMax_rec where
  "BMax_rec R 0 = 0"
| "BMax_rec R (Suc n) = (if R (Suc n) then (Suc n) else BMax_rec R n)"

definition
  BMax_set :: "(nat \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> nat"
  where
    "BMax_set R x = Max ({z. z \<le> x \<and> R z} \<union> {0})"

lemma BMax_rec_eq1:
  "BMax_rec R x = (GREATEST z. (R z \<and> z \<le> x) \<or> z = 0)"
  apply(induct x)
   apply(auto intro: Greatest_equality Greatest_equality[symmetric])
  apply(simp add: le_Suc_eq)
  by metis

lemma BMax_rec_eq2:
  "BMax_rec R x = Max ({z. z \<le> x \<and> R z} \<union> {0})"
  apply(induct x)
   apply(auto intro: Max_eqI Max_eqI[symmetric])
  apply(simp add: le_Suc_eq)
  by metis

lemma BMax_rec_eq3:
  "BMax_rec R x = Max (Set.filter (\<lambda>z. R z) {..x} \<union> {0})"
  by (simp add: BMax_rec_eq2 Set.filter_def)

definition
  "rec_max1 f = PR Z (CN rec_ifz [CN f [CN S [Id 3 0], Id 3 2], CN S [Id 3 0], Id 3 1])"

lemma max1_lemma [simp]:
  "rec_eval (rec_max1 f) [x, y] = BMax_rec (\<lambda>u. rec_eval f [u, y] = 0) x"
  by (induct x) (simp_all add: rec_max1_def)

definition
  "rec_max2 f = PR Z (CN rec_ifz [CN f [CN S [Id 4 0], Id 4 2, Id 4 3], CN S [Id 4 0], Id 4 1])"

lemma max2_lemma [simp]:
  "rec_eval (rec_max2 f) [x, y1, y2] = BMax_rec (\<lambda>u. rec_eval f [u, y1, y2] = 0) x"
  by (induct x) (simp_all add: rec_max2_def)


section \<open>Encodings using Cantor's pairing function\<close>

text \<open>
  We use Cantor's pairing function from Nat-Bijection.
  However, we need to prove that the formulation of the
  decoding function there is recursive. For this we first
  prove that we can extract the maximal triangle number
  using @{term prod_decode}.
\<close>

abbreviation Max_triangle_aux where
  "Max_triangle_aux k z \<equiv> fst (prod_decode_aux k z) + snd (prod_decode_aux k z)"

abbreviation Max_triangle where
  "Max_triangle z \<equiv> Max_triangle_aux 0 z"

abbreviation
  "pdec1 z \<equiv> fst (prod_decode z)"

abbreviation
  "pdec2 z \<equiv> snd (prod_decode z)"

abbreviation
  "penc m n \<equiv> prod_encode (m, n)"

lemma fst_prod_decode:
  "pdec1 z = z - triangle (Max_triangle z)"
  by (subst (3) prod_decode_inverse[symmetric])
    (simp add: prod_encode_def prod_decode_def split: prod.split)

lemma snd_prod_decode:
  "pdec2 z = Max_triangle z - pdec1 z"
  by (simp only: prod_decode_def)

lemma le_triangle:
  "m \<le> triangle (n + m)"
  by (induct m) (simp_all)

lemma Max_triangle_triangle_le:
  "triangle (Max_triangle z) \<le> z"
  by (subst (9) prod_decode_inverse[symmetric])
    (simp add: prod_decode_def prod_encode_def split: prod.split)

lemma Max_triangle_le:
  "Max_triangle z \<le> z"
proof -
  have "Max_triangle z \<le> triangle (Max_triangle z)"
    using le_triangle[of _ 0, simplified] by simp
  also have "... \<le> z" by (rule Max_triangle_triangle_le)
  finally show "Max_triangle z \<le> z" .
qed

lemma w_aux:
  "Max_triangle (triangle k + m) = Max_triangle_aux k m"
  by (simp add: prod_decode_def[symmetric] prod_decode_triangle_add)

lemma y_aux: "y \<le> Max_triangle_aux y k"
  apply(induct k arbitrary: y rule: nat_less_induct)
  apply(subst (1 2) prod_decode_aux.simps)
  by(auto dest!:spec mp elim:Suc_leD)

lemma Max_triangle_greatest:
  "Max_triangle z = (GREATEST k. (triangle k \<le> z \<and> k \<le> z) \<or> k = 0)"
  apply(rule Greatest_equality[symmetric])
   apply(rule disjI1)
   apply(rule conjI)
    apply(rule Max_triangle_triangle_le)
   apply(rule Max_triangle_le)
  apply(erule disjE)
   apply(erule conjE)
   apply(subst (asm) (1) le_iff_add)
   apply(erule exE)
   apply(clarify)
   apply(simp only: w_aux)
   apply(rule y_aux)
  apply(simp)
  done


definition
  "rec_triangle = CN rec_quo [CN rec_mult [Id 1 0, S], constn 2]"

definition
  "rec_max_triangle =
       (let cond = CN rec_not [CN rec_le [CN rec_triangle [Id 2 0], Id 2 1]] in
        CN (rec_max1 cond) [Id 1 0, Id 1 0])"


lemma triangle_lemma [simp]:
  "rec_eval rec_triangle [x] = triangle x"
  by (simp add: rec_triangle_def triangle_def)

lemma max_triangle_lemma [simp]:
  "rec_eval rec_max_triangle [x] = Max_triangle x"
  by (simp add: Max_triangle_greatest rec_max_triangle_def Let_def BMax_rec_eq1)


text \<open>Encodings for Products\<close>

definition
  "rec_penc = CN rec_add [CN rec_triangle [CN rec_add [Id 2 0, Id 2 1]], Id 2 0]"

definition
  "rec_pdec1 = CN rec_minus [Id 1 0, CN rec_triangle [CN rec_max_triangle [Id 1 0]]]"

definition
  "rec_pdec2 = CN rec_minus [CN rec_max_triangle [Id 1 0], CN rec_pdec1 [Id 1 0]]"

lemma pdec1_lemma [simp]:
  "rec_eval rec_pdec1 [z] = pdec1 z"
  by (simp add: rec_pdec1_def fst_prod_decode)

lemma pdec2_lemma [simp]:
  "rec_eval rec_pdec2 [z] = pdec2 z"
  by (simp add: rec_pdec2_def snd_prod_decode)

lemma penc_lemma [simp]:
  "rec_eval rec_penc [m, n] = penc m n"
  by (simp add: rec_penc_def prod_encode_def)


text \<open>Encodings of Lists\<close>

fun
  lenc :: "nat list \<Rightarrow> nat"
  where
    "lenc [] = 0"
  | "lenc (x # xs) = penc (Suc x) (lenc xs)"

fun
  ldec :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  where
    "ldec z 0 = (pdec1 z) - 1"
  | "ldec z (Suc n) = ldec (pdec2 z) n"

lemma pdec_zero_simps [simp]:
  "pdec1 0 = 0"
  "pdec2 0 = 0"
  by (simp_all add: prod_decode_def prod_decode_aux.simps)

lemma ldec_zero:
  "ldec 0 n = 0"
  by (induct n) (simp_all add: prod_decode_def prod_decode_aux.simps)

lemma list_encode_inverse:
  "ldec (lenc xs) n = (if n < length xs then xs ! n else 0)"
  by (induct xs arbitrary: n rule: lenc.induct)
    (auto simp add: ldec_zero nth_Cons split: nat.splits)

lemma lenc_length_le:
  "length xs \<le> lenc xs"
  by (induct xs) (simp_all add: prod_encode_def)


text \<open>Membership for the List Encoding\<close>

fun inside :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
  "inside z 0 = (0 < z)"
| "inside z (Suc n) = inside (pdec2 z) n"

definition enclen :: "nat \<Rightarrow> nat" where
  "enclen z = BMax_rec (\<lambda>x. inside z (x - 1)) z"

lemma inside_False [simp]:
  "inside 0 n = False"
  by (induct n) (simp_all)

lemma inside_length [simp]:
  "inside (lenc xs) s = (s < length xs)"
proof(induct s arbitrary: xs)
  case 0
  then show ?case by (cases xs) (simp_all add: prod_encode_def)
next
  case (Suc s)
  then show ?case by (cases xs;auto)
qed

text \<open>Length of Encoded Lists\<close>

lemma enclen_length [simp]:
  "enclen (lenc xs) = length xs"
  unfolding enclen_def
  apply(simp add: BMax_rec_eq1)
  apply(rule Greatest_equality)
   apply(auto simp add: lenc_length_le)
  done

lemma enclen_penc [simp]:
  "enclen (penc (Suc x) (lenc xs)) = Suc (enclen (lenc xs))"
  by (simp only: lenc.simps[symmetric] enclen_length) (simp)

lemma enclen_zero [simp]:
  "enclen 0 = 0"
  by (simp add: enclen_def)


text \<open>Recursive Definitions for List Encodings\<close>

fun
  rec_lenc :: "recf list \<Rightarrow> recf"
  where
    "rec_lenc [] = Z"
  | "rec_lenc (f # fs) = CN rec_penc [CN S [f], rec_lenc fs]"

definition
  "rec_ldec = CN rec_predecessor [CN rec_pdec1 [rec_swap (rec_iter rec_pdec2)]]"

definition
  "rec_inside = CN rec_less [Z, rec_swap (rec_iter rec_pdec2)]"

definition
  "rec_enclen = CN (rec_max1 (CN rec_not [CN rec_inside [Id 2 1, CN rec_predecessor [Id 2 0]]])) [Id 1 0, Id 1 0]"

lemma ldec_iter:
  "ldec z n = pdec1 (Iter pdec2 n z) - 1"
  by (induct n arbitrary: z) (simp | subst Iter_comm)+

lemma inside_iter:
  "inside z n = (0 < Iter pdec2 n z)"
  by (induct n arbitrary: z) (simp | subst Iter_comm)+

lemma lenc_lemma [simp]:
  "rec_eval (rec_lenc fs) xs = lenc (map (\<lambda>f. rec_eval f xs) fs)"
  by (induct fs) (simp_all)

lemma ldec_lemma [simp]:
  "rec_eval rec_ldec [z, n] = ldec z n"
  by (simp add: ldec_iter rec_ldec_def)

lemma inside_lemma [simp]:
  "rec_eval rec_inside [z, n] = (if inside z n then 1 else 0)"
  by (simp add: inside_iter rec_inside_def)

lemma enclen_lemma [simp]:
  "rec_eval rec_enclen [z] = enclen z"
  by (simp add: rec_enclen_def enclen_def)


end

