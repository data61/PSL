(* Title:      Infinite Matrix Model of Kleene Algebra
   Author:     Alasdair Armstrong, Georg Struth, Tjark Weber
   Maintainer: Georg Struth <g.struth at sheffield.ac.uk>
               Tjark Weber <tjark.weber at it.uu.se>
*)

section \<open>Infinite Matrices\<close>

theory Inf_Matrix
imports Finite_Suprema
begin

text \<open>Matrices are functions from two index sets into some suitable
algebra. We consider arbitrary index sets, not necessarily the
positive natural numbers up to some bounds; our coefficient algebra is
a dioid. Our only restriction is that summation in the product of
matrices is over a finite index set. This follows essentially Droste
and Kuich's introductory article in the Handbook of Weighted Automata~\cite{weightedautomata09}.

Under these assumptions we show that dioids are closed under matrix
formation. Our proofs are similar to those for formal power series,
but simpler.\<close>

type_synonym ('a, 'b, 'c) matrix = "'a \<Rightarrow> 'b \<Rightarrow> 'c"

definition mat_one :: "('a, 'a, 'c::dioid_one_zero) matrix" ("\<epsilon>") where
  "\<epsilon> i j \<equiv> (if (i = j) then 1 else 0)"

definition mat_zero :: "('a, 'b, 'c::dioid_one_zero) matrix" ("\<delta>") where
  "\<delta> \<equiv> \<lambda>j i. 0"

definition mat_add :: "('a, 'b, 'c::dioid_one_zero) matrix \<Rightarrow> ('a, 'b, 'c) matrix \<Rightarrow> ('a, 'b, 'c) matrix" (infixl "\<oplus>" 70) where
  "(f \<oplus> g)  \<equiv> \<lambda>i j. (f i j) + (g i j)"

lemma mat_add_assoc: "(f \<oplus> g) \<oplus> h =  f \<oplus> (g \<oplus> h)"
  by (auto simp add: mat_add_def join.sup_assoc)

lemma mat_add_comm: "f \<oplus> g = g \<oplus> f"
  by (auto simp add: mat_add_def join.sup_commute)

lemma mat_add_idem[simp]: "f \<oplus> f = f"
  by (auto simp add: mat_add_def)

lemma mat_zerol[simp]: "f \<oplus> \<delta> = f"
  by (auto simp add: mat_add_def mat_zero_def)

lemma mat_zeror[simp]: "\<delta> \<oplus> f = f"
  by (auto simp add: mat_add_def mat_zero_def)

definition mat_mult :: "('a, 'k::finite, 'c::dioid_one_zero) matrix \<Rightarrow> ('k, 'b, 'c) matrix \<Rightarrow> ('a, 'b, 'c) matrix" (infixl "\<otimes>" 60) where
  "(f \<otimes> g) i j  \<equiv> \<Sum> {(f i k) \<cdot> (g k j) | k. k \<in> UNIV}"

lemma mat_annil[simp]: "\<delta> \<otimes> f = \<delta>"
  by (rule ext, auto simp add: mat_mult_def mat_zero_def)

lemma mat_annir[simp]: "f \<otimes> \<delta>  = \<delta>"
  by (rule ext, auto simp add: mat_mult_def mat_zero_def)

lemma mat_distl: "f \<otimes> (g \<oplus> h) = (f \<otimes> g) \<oplus> (f \<otimes> h)"
proof -
  {
    fix i j
    have "(f \<otimes> (g \<oplus> h)) i j  = \<Sum>{f i k \<cdot> (g k j + h k j) |k. k \<in> UNIV}"
      by (simp only: mat_mult_def mat_add_def)
    also have "... = \<Sum>{f i k \<cdot> g k j + f i k \<cdot> h k j |k. k \<in> UNIV}"
      by (simp only: distrib_left)
    also have "... = \<Sum>{f i k \<cdot> g k j |k. k \<in> UNIV} + \<Sum>{f i k \<cdot> h k j |k. k \<in> UNIV}"
      by (simp only: fset_to_im sum_fun_sum finite_UNIV)
    finally have "(f \<otimes> (g \<oplus> h)) i j  = ((f \<otimes> g) \<oplus> (f \<otimes> h)) i j"
      by (simp only: mat_mult_def mat_add_def)
  }
  thus ?thesis
    by auto
qed

lemma mat_distr: "(f \<oplus> g) \<otimes> h = (f \<otimes> h) \<oplus> (g \<otimes> h)"
proof -
  {
    fix i j
    have "((f \<oplus> g) \<otimes> h) i j  = \<Sum>{(f i k + g i k) \<cdot> h k j |k. k \<in> UNIV}"
      by (simp only: mat_mult_def mat_add_def)
    also have "... = \<Sum>{f i k \<cdot> h k j + g i k \<cdot> h k j |k. k \<in> UNIV}"
      by (simp only: distrib_right)
    also have "... = \<Sum>{f i k \<cdot> h k j |k. k \<in> UNIV} + \<Sum>{g i k \<cdot> h k j |k. k \<in> UNIV}"
      by (simp only: fset_to_im sum_fun_sum finite_UNIV)
    finally have "((f \<oplus> g) \<otimes> h) i j  = ((f \<otimes> h) \<oplus> (g \<otimes> h)) i j"
      by (simp only: mat_mult_def mat_add_def)
  }
  thus ?thesis
    by auto
qed

lemma logic_aux1: "(\<exists>k. (i = k \<longrightarrow> x = f i j) \<and> (i \<noteq> k \<longrightarrow> x = 0)) \<longleftrightarrow> (\<exists>k. i = k \<and> x = f i j) \<or> (\<exists>k. i \<noteq> k \<and> x = 0)"
  by blast

lemma logic_aux2: "(\<exists>k. (k = j \<longrightarrow> x = f i j) \<and> (k \<noteq> j \<longrightarrow> x = 0)) \<longleftrightarrow> (\<exists>k. k = j \<and> x = f i j) \<or> (\<exists>k. k \<noteq> j \<and> x = 0)"
  by blast

lemma mat_onel[simp]: "\<epsilon> \<otimes> f = f"
proof -
  {
    fix i j
    have "(\<epsilon> \<otimes> f) i j = \<Sum>{x. (\<exists>k. (i = k \<longrightarrow> x = f i j) \<and> (i \<noteq> k \<longrightarrow> x = 0))}"
      by (auto simp add: mat_mult_def mat_one_def)
    also have "... = \<Sum>({x. \<exists>k. (i = k \<and> x = f i j)} \<union> {x. \<exists>k. (i \<noteq> k \<and> x = 0)})"
      by (simp only: Collect_disj_eq logic_aux1)
    also have "... = \<Sum>{x. \<exists>k. (i = k \<and> x = f i j)} + \<Sum>{x. \<exists>k. (i \<noteq> k \<and> x = 0)}"
      by (rule sum_union, auto)
    finally have "(\<epsilon> \<otimes> f) i j = f i j"
      by (auto simp add: sum.neutral)
  }
  thus ?thesis
    by auto
qed

lemma mat_oner[simp]: "f \<otimes> \<epsilon> = f"
proof -
  {
    fix i j
    have "(f \<otimes> \<epsilon>) i j = \<Sum>{x. (\<exists>k. (k = j \<longrightarrow> x = f i j) \<and> (k \<noteq> j \<longrightarrow> x = 0))}"
      by (auto simp add: mat_mult_def mat_one_def)
    also have "... = \<Sum>({x. \<exists>k. (k = j \<and> x = f i j)} \<union> {x. \<exists>k. (k \<noteq> j \<and> x = 0)})"
      by (simp only: Collect_disj_eq logic_aux2)
    also have "... = \<Sum>{x. \<exists>k. (k = j \<and> x = f i j)} + \<Sum>{x. \<exists>k. (k \<noteq> j \<and> x = 0)}"
      by (rule sum_union, auto)
    finally have "(f \<otimes> \<epsilon>) i j = f i j"
      by (auto simp add: sum.neutral)
  }
  thus ?thesis
    by auto
qed

lemma mat_rearrange:
  fixes F :: "'a \<Rightarrow> 'k1 \<Rightarrow> 'k2 \<Rightarrow> 'b \<Rightarrow> 'c::dioid_one_zero"
  assumes fUNk1: "finite (UNIV::'k1 set)"
  assumes fUNk2: "finite (UNIV::'k2 set)"
  shows "\<Sum>{\<Sum>{F i k1 k2 j |k2. k2 \<in> (UNIV::'k2 set)} |k1. k1 \<in> (UNIV::'k1 set)} = \<Sum>{\<Sum>{F i k1 k2 j |k1. k1 \<in> UNIV} |k2. k2 \<in> UNIV}"
proof -
  {
    fix z :: 'c
    let ?lhs = "\<Sum>{\<Sum>{F i k1 k2 j |k2. k2 \<in> UNIV} |k1. k1 \<in> UNIV}"
    let ?rhs = "\<Sum>{\<Sum>{F i k1 k2 j |k1. k1 \<in> UNIV} |k2. k2 \<in> UNIV}"
    have "?lhs \<le> z \<longleftrightarrow> (\<forall>k1 k2. F i k1 k2 j \<le> z)"
      by (simp only: fset_to_im sum_fun_image_sup fUNk1 fUNk2, auto)
    hence "?lhs \<le> z \<longleftrightarrow> ?rhs \<le> z"
      by (simp only: fset_to_im sum_fun_image_sup fUNk1 fUNk2, auto)
  }
  thus ?thesis
    by (simp add: eq_iff)
qed

lemma mat_mult_assoc: "f \<otimes> (g \<otimes> h) = (f \<otimes> g) \<otimes> h"
proof -
  {
    fix i j
    have "(f \<otimes> (g \<otimes> h)) i j = \<Sum>{f i k1 \<cdot> \<Sum>{g k1 k2 \<cdot> h k2 j |k2. k2 \<in> UNIV} |k1. k1 \<in> UNIV}"
      by (simp only: mat_mult_def)
    also have "... = \<Sum>{\<Sum>{f i k1 \<cdot> g k1 k2 \<cdot> h k2 j |k2. k2 \<in> UNIV} |k1. k1 \<in> UNIV}"
      by (simp only: fset_to_im sum_fun_distl finite_UNIV mult.assoc)
    also have "... = \<Sum>{\<Sum>{(f i k1 \<cdot> g k1 k2) \<cdot> h k2 j|k1. k1 \<in> UNIV} |k2. k2 \<in> UNIV}"
      by (rule mat_rearrange, auto simp add: finite_UNIV)
    also have "... = \<Sum>{\<Sum>{f i k1 \<cdot> g k1 k2 |k1. k1 \<in> UNIV} \<cdot> h k2 j |k2. k2 \<in> UNIV}"
      by (simp only: fset_to_im sum_fun_distr finite_UNIV)
    finally have "(f \<otimes> (g \<otimes> h)) i j  = ((f \<otimes> g) \<otimes> h) i j "
      by (simp only: mat_mult_def)
  }
  thus ?thesis
    by auto
qed

definition mat_less_eq :: "('a, 'b, 'c::dioid_one_zero) matrix \<Rightarrow> ('a, 'b, 'c) matrix \<Rightarrow> bool" where
  "mat_less_eq f g   = (f \<oplus> g  = g)"

definition mat_less :: "('a, 'b, 'c::dioid_one_zero) matrix \<Rightarrow> ('a, 'b, 'c) matrix \<Rightarrow> bool" where
  "mat_less f g  = (mat_less_eq f g \<and> f \<noteq> g)"

interpretation matrix_dioid: dioid_one_zero  mat_add mat_mult mat_one mat_zero mat_less_eq mat_less
  by (unfold_locales) (metis mat_add_assoc mat_add_comm mat_mult_assoc[symmetric] mat_distr mat_onel mat_oner mat_zeror mat_annil mat_annir mat_less_eq_def mat_less_def mat_add_idem mat_distl)+

text \<open>As in the case of formal power series we currently do not
implement the Kleene star of matrices, since this is complicated.\<close>

end
