(*  Gauss-Jordan elimination for matrices represented as functions
    Author: Tobias Nipkow
*)
section \<open>Gauss-Jordan elimination algorithm\<close>
theory Gauss_Jordan_Elim_Fun
imports Main
begin

text\<open>Matrices are functions:\<close>

type_synonym 'a matrix = "nat \<Rightarrow> nat \<Rightarrow> 'a"

text\<open>In order to restrict to finite matrices, a matrix is usually combined
with one or two natural numbers indicating the maximal row and column of the
matrix.

Gauss-Jordan elimination is parameterized with a natural number \<open>n\<close>. It indicates that the matrix \<open>A\<close> has \<open>n\<close> rows and columns.
In fact, \<open>A\<close> is the augmented matrix with \<open>n+1\<close> columns. Column
\<open>n\<close> is the ``right-hand side'', i.e.\ the constant vector \<open>b\<close>. The result is the unit matrix augmented with the solution in column
\<open>n\<close>; see the correctness theorem below.\<close>

fun gauss_jordan :: "('a::field)matrix \<Rightarrow> nat \<Rightarrow> ('a)matrix option" where
"gauss_jordan A 0 = Some(A)" |
"gauss_jordan A (Suc m) =
 (case dropWhile (\<lambda>i. A i m = 0) [0..<Suc m] of
   [] \<Rightarrow> None |
   p # _ \<Rightarrow>
    (let Ap' = (\<lambda>j. A p j / A p m);
         A' = (\<lambda>i. if i=p then Ap' else (\<lambda>j. A i j - A i m * Ap' j))
     in gauss_jordan (Fun.swap p m A') m))"

text\<open>Some auxiliary functions:\<close>

definition solution :: "('a::field)matrix \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> bool" where
"solution A n x = (\<forall>i<n. (\<Sum> j=0..<n. A i j * x j) = A i n)"

definition unit :: "('a::field)matrix \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
"unit A m n =
 (\<forall>i j::nat. m\<le>j \<longrightarrow> j<n \<longrightarrow> A i j = (if i=j then 1 else 0))"

lemma solution_swap:
assumes "p1 < n" "p2 < n"
shows "solution (Fun.swap p1 p2 A) n x = solution A n x" (is "?L = ?R")
proof(cases "p1=p2")
  case True thus ?thesis by simp
next
  case False
  show ?thesis
  proof
    assume ?R thus ?L using assms False by(simp add: solution_def Fun.swap_def)
  next
   assume ?L
   show ?R
   proof(auto simp: solution_def)
     fix i assume "i<n"
     show "(\<Sum>j = 0..<n. A i j * x j) = A i n"
     proof cases
       assume "i=p1"
       with \<open>?L\<close> assms False show ?thesis
         by(fastforce simp add: solution_def Fun.swap_def)
     next
       assume "i\<noteq>p1"
       show ?thesis
       proof cases
         assume "i=p2"
         with \<open>?L\<close> assms False show ?thesis
           by(fastforce simp add: solution_def Fun.swap_def)
       next
         assume "i\<noteq>p2"
         with \<open>i\<noteq>p1\<close> \<open>?L\<close> \<open>i<n\<close> assms False show ?thesis
           by(fastforce simp add: solution_def Fun.swap_def)
       qed
     qed
   qed
 qed
qed

(* Converting these apply scripts makes them blow up - see above *)

lemma solution_upd1:
  "c \<noteq> 0 \<Longrightarrow> solution (A(p:=(\<lambda>j. A p j / c))) n x = solution A n x"
apply(cases "p<n")
 prefer 2
 apply(simp add: solution_def)
apply(clarsimp simp add: solution_def)
apply rule
 apply clarsimp
 apply(case_tac "i=p")
  apply (simp add: sum_divide_distrib[symmetric] eq_divide_eq field_simps)
 apply simp
apply (simp add: sum_divide_distrib[symmetric] eq_divide_eq field_simps)
done

lemma solution_upd_but1: "\<lbrakk> ap = A p; \<forall>i j. i\<noteq>p \<longrightarrow> a i j = A i j; p<n \<rbrakk> \<Longrightarrow>
 solution (\<lambda>i. if i=p then ap else (\<lambda>j. a i j - c i * ap j)) n x =
 solution A n x"
apply(clarsimp simp add: solution_def)
apply rule
 prefer 2
 apply (simp add: field_simps sum_subtractf sum_distrib_left[symmetric])
apply(clarsimp)
apply(case_tac "i=p")
 apply simp
apply (auto simp add: field_simps sum_subtractf sum_distrib_left[symmetric] all_conj_distrib)
done

subsection\<open>Correctness\<close>

text\<open>The correctness proof:\<close>

lemma gauss_jordan_lemma: "m\<le>n \<Longrightarrow> unit A m n \<Longrightarrow> gauss_jordan A m = Some B \<Longrightarrow>
  unit B 0 n \<and> solution A n (\<lambda>j. B j n)"
proof(induct m arbitrary: A B)
  case 0
  { fix a and b c d :: "'a"
    have "(if a then b else c) * d = (if a then b*d else c*d)" by simp
  } with 0 show ?case by(simp add: unit_def solution_def sum.If_cases)
next
  case (Suc m)
  let "?Ap' p" = "(\<lambda>j. A p j / A p m)"
  let "?A' p" = "(\<lambda>i. if i=p then ?Ap' p else (\<lambda>j. A i j - A i m * ?Ap' p j))"
  from \<open>gauss_jordan A (Suc m) = Some B\<close>
  obtain p ks where "dropWhile (\<lambda>i. A i m = 0) [0..<Suc m] = p#ks" and
    rec: "gauss_jordan (Fun.swap p m (?A' p)) m = Some B"
    by (auto split: list.splits)
  from this have p: "p\<le>m" "A p m \<noteq> 0"
    apply(simp_all add: dropWhile_eq_Cons_conv del:upt_Suc)
    by (metis set_upt atLeast0AtMost atLeastLessThanSuc_atLeastAtMost atMost_iff in_set_conv_decomp)
  have "m\<le>n" "m<n" using \<open>Suc m \<le> n\<close> by arith+
  have "unit (Fun.swap p m (?A' p)) m n" using Suc.prems(2) p
    unfolding unit_def Fun.swap_def Suc_le_eq by (auto simp: le_less)
  from Suc.hyps[OF \<open>m\<le>n\<close> this rec] \<open>m<n\<close> p
  show ?case
    by(simp add: solution_swap solution_upd1 solution_upd_but1[where A = "A(p := ?Ap' p)"])
qed

theorem gauss_jordan_correct:
  "gauss_jordan A n = Some B \<Longrightarrow> solution A n (\<lambda>j. B j n)"
by(simp add:gauss_jordan_lemma[of n n] unit_def  field_simps)

definition solution2 :: "('a::field)matrix \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> bool"
where "solution2 A m n x = (\<forall>i<m. (\<Sum> j=0..<m. A i j * x j) = A i n)"

definition "usolution A m n x \<longleftrightarrow>
  solution2 A m n x \<and> (\<forall>y. solution2 A m n y \<longrightarrow> (\<forall>j<m. y j = x j))"

lemma non_null_if_pivot:
  assumes "usolution A m n x" and "q < m" shows "\<exists>p<m. A p q \<noteq> 0"
proof(rule ccontr)
  assume "\<not>(\<exists>p<m. A p q \<noteq> 0)"
  hence 1: "\<And>p. p<m \<Longrightarrow> A p q = 0" by simp
  { fix y assume 2: "\<forall>j. j\<noteq>q \<longrightarrow> y j = x j"
    { fix i assume "i<m"
      with assms(1) have "A i n = (\<Sum>j = 0..<m. A i j * x j)"
        by (auto simp: solution2_def usolution_def)
      with 1[OF \<open>i<m\<close>] 2
      have "(\<Sum>j = 0..<m. A i j * y j) = A i n"
        by (auto intro!: sum.cong)
    }
    hence "solution2 A m n y" by(simp add: solution2_def)
  }
  hence "solution2 A m n (x(q:=0))" and "solution2 A m n (x(q:=1))" by auto
  with assms(1) zero_neq_one \<open>q < m\<close>
  show False
    by (simp add: usolution_def)
       (metis fun_upd_same zero_neq_one)
qed

lemma lem1:
  fixes f :: "'a \<Rightarrow> 'b::field"
  shows "(\<Sum>x\<in>A. f x * (a * g x)) = a * (\<Sum>x\<in>A. f x * g x)"
  by (simp add: sum_distrib_left field_simps)

lemma lem2:
  fixes f :: "'a \<Rightarrow> 'b::field"
  shows "(\<Sum>x\<in>A. f x * (g x * a)) = a * (\<Sum>x\<in>A. f x * g x)"
  by (simp add: sum_distrib_left field_simps)

subsection\<open>Complete\<close>

lemma gauss_jordan_complete:
  "m \<le> n \<Longrightarrow> usolution A m n x \<Longrightarrow> \<exists>B. gauss_jordan A m = Some B"
proof(induction m arbitrary: A)
  case 0 show ?case by simp
next
  case (Suc m A)
  from \<open>Suc m \<le> n\<close> have "m\<le>n" and "m<Suc m" by arith+
  from non_null_if_pivot[OF Suc.prems(2) \<open>m<Suc m\<close>]
  obtain p' where "p'<Suc m" and "A p' m \<noteq> 0" by blast
  hence "dropWhile (\<lambda>i. A i m = 0) [0..<Suc m] \<noteq> []"
    by (simp add: atLeast0LessThan) (metis lessThan_iff linorder_neqE_nat not_less_eq)
  then obtain p xs where 1: "dropWhile (\<lambda>i. A i m = 0) [0..<Suc m] = p#xs"
    by (metis list.exhaust)
  from this have "p\<le>m" "A p m \<noteq> 0"
    by (simp_all add: dropWhile_eq_Cons_conv del: upt_Suc)
       (metis set_upt atLeast0AtMost atLeastLessThanSuc_atLeastAtMost atMost_iff in_set_conv_decomp)
  then have p: "p < Suc m" "A p m \<noteq> 0"
    by auto
  let ?Ap' = "(\<lambda>j. A p j / A p m)"
  let ?A' = "(\<lambda>i. if i=p then ?Ap' else (\<lambda>j. A i j - A i m * ?Ap' j))"
  let ?A = "Fun.swap p m ?A'"
  have A: "solution2 A (Suc m) n x" using Suc.prems(2) by(simp add: usolution_def)
  { fix i assume le_m: "p < Suc m" "i < Suc m" "A p m \<noteq> 0"
    have "(\<Sum>j = 0..<m. (A i j - A i m * A p j / A p m) * x j) =
      ((\<Sum>j = 0..<Suc m. A i j * x j) - A i m * x m) -
      ((\<Sum>j = 0..<Suc m. A p j * x j) - A p m * x m) * A i m / A p m"
      by (simp add: field_simps sum_subtractf sum_divide_distrib
                    sum_distrib_left)
    also have "\<dots> = A i n - A p n * A i m / A p m"
      using A le_m
      by (simp add: solution2_def field_simps del: sum.op_ivl_Suc)
    finally have "(\<Sum>j = 0..<m. (A i j - A i m * A p j / A p m) * x j) =
      A i n - A p n * A i m / A p m" . }
  then have "solution2 ?A m n x" using p
    by (auto simp add: solution2_def Fun.swap_def field_simps)
  moreover
  { fix y assume a: "solution2 ?A m n y"
    let ?y = "y(m := A p n / A p m - (\<Sum>j = 0..<m. A p j * y j) / A p m)"
    have "solution2 A (Suc m) n ?y" unfolding solution2_def
    proof safe
      fix i assume "i < Suc m"
      show "(\<Sum>j=0..<Suc m. A i j * ?y j) = A i n"
      proof (cases "i = p")
        assume "i = p" with p show ?thesis by (simp add: field_simps)
      next
        assume "i \<noteq> p"
        show ?thesis
        proof (cases "i = m")
          assume "i = m"
          with p \<open>i \<noteq> p\<close> have "p < m" by simp
          with a[unfolded solution2_def, THEN spec, of p] p(2)
          have "A p m * (A m m * A p n + A p m * (\<Sum>j = 0..<m. y j * A m j)) = A p m * (A m n * A p m + A m m * (\<Sum>j = 0..<m. y j * A p j))"
            by (simp add: Fun.swap_def field_simps sum_subtractf lem1 lem2 sum_divide_distrib[symmetric]
                     split: if_splits)
          with \<open>A p m \<noteq> 0\<close> show ?thesis unfolding \<open>i = m\<close>
            by simp (simp add: field_simps)
        next
          assume "i \<noteq> m"
          then have "i < m" using \<open>i < Suc m\<close> by simp
          with a[unfolded solution2_def, THEN spec, of i] p(2)
          have "A p m * (A i m * A p n + A p m * (\<Sum>j = 0..<m. y j * A i j)) = A p m * (A i n * A p m + A i m * (\<Sum>j = 0..<m. y j * A p j))"
            by (simp add: Fun.swap_def split: if_splits)
              (simp add: field_simps sum_subtractf lem1 lem2 sum_divide_distrib [symmetric])
          with \<open>A p m \<noteq> 0\<close> show ?thesis
            by simp (simp add: field_simps)
        qed
      qed
    qed
    with \<open>usolution A (Suc m) n x\<close>
    have "\<forall>j<Suc m. ?y j = x j" by (simp add: usolution_def)
    hence "\<forall>j<m. y j = x j"
      by simp (metis less_SucI nat_neq_iff)
  } ultimately have "usolution ?A m n x" by(simp add: usolution_def)
  from Suc.IH[OF \<open>m\<le>n\<close> this] 1 show ?case by(simp)
qed

text\<open>Future work: extend the proof to matrix inversion.\<close>

hide_const (open) unit

end
