(*  Title:       The Cauchy-Schwarz Inequality
    Author:      Benjamin Porter <Benjamin.Porter at gmail.com>, 2006
    Maintainer:  Benjamin Porter <Benjamin.Porter at gmail.com>
*)

chapter \<open>The Cauchy-Schwarz Inequality\<close>

theory CauchySchwarz
imports Complex_Main
begin

(*<*)

(* Some basic results that don't need to be in the final doc ..*)


lemmas real_sq = power2_eq_square [where 'a = real, symmetric]

lemmas real_sq_exp = power_mult_distrib [where 'a = real and ?n = 2]

lemma double_sum_equiv:
  fixes f::"nat \<Rightarrow> real"
  shows
  "(\<Sum>k\<in>{1..n}. (\<Sum>j\<in>{1..n}. f k * g j)) =
   (\<Sum>k\<in>{1..n}. (\<Sum>j\<in>{1..n}. f j * g k))"
  by (rule sum.swap)

(*>*)



section \<open>Abstract\<close>

text \<open>The following document presents a formalised proof of the
Cauchy-Schwarz Inequality for the specific case of $R^n$. The system
used is Isabelle/Isar. 

{\em Theorem:} Take $V$ to be some vector space possessing a norm and
inner product, then for all $a,b \in V$ the following inequality
holds: \<open>\<bar>a\<cdot>b\<bar> \<le> \<parallel>a\<parallel>*\<parallel>b\<parallel>\<close>. Specifically, in the Real case, the
norm is the Euclidean length and the inner product is the standard dot
product.\<close>


section \<open>Formal Proof\<close>

subsection \<open>Vector, Dot and Norm definitions.\<close>

text \<open>This section presents definitions for a real vector type, a
dot product function and a norm function.\<close>

subsubsection \<open>Vector\<close>

text \<open>We now define a vector type to be a tuple of (function,
length). Where the function is of type @{typ "nat\<Rightarrow>real"}. We also
define some accessor functions and appropriate notation.\<close>

type_synonym vector = "(nat\<Rightarrow>real) * nat"

definition
  ith :: "vector \<Rightarrow> nat \<Rightarrow> real" ("((_)\<^bsub>_\<^esub>)" [80,100] 100) where
  "ith v i = fst v i"

definition
  vlen :: "vector \<Rightarrow> nat" where
  "vlen v = snd v"

text \<open>Now to access the second element of some vector $v$ the syntax
is $v_2$.\<close>

subsubsection \<open>Dot and Norm\<close>

text \<open>We now define the dot product and norm operations.\<close>

definition
  dot :: "vector \<Rightarrow> vector \<Rightarrow> real" (infixr "\<cdot>" 60) where
  "dot a b = (\<Sum>j\<in>{1..(vlen a)}. a\<^bsub>j\<^esub>*b\<^bsub>j\<^esub>)"

definition
  norm :: "vector \<Rightarrow> real"                  ("\<parallel>_\<parallel>" 100) where
  "norm v = sqrt (\<Sum>j\<in>{1..(vlen v)}. v\<^bsub>j\<^esub>^2)"

text \<open>Another definition of the norm is @{term "\<parallel>v\<parallel> = sqrt
(v\<cdot>v)"}. We show that our definition leads to this one.\<close>

lemma norm_dot:
 "\<parallel>v\<parallel> = sqrt (v\<cdot>v)"
proof -
  have "sqrt (v\<cdot>v) = sqrt (\<Sum>j\<in>{1..(vlen v)}. v\<^bsub>j\<^esub>*v\<^bsub>j\<^esub>)" unfolding dot_def by simp
  also with real_sq have "\<dots> = sqrt (\<Sum>j\<in>{1..(vlen v)}. v\<^bsub>j\<^esub>^2)" by simp
  also have "\<dots> = \<parallel>v\<parallel>" unfolding norm_def by simp
  finally show ?thesis ..
qed

text \<open>A further important property is that the norm is never negative.\<close>

lemma norm_pos:
  "\<parallel>v\<parallel> \<ge> 0"
proof -
  have "\<forall>j. v\<^bsub>j\<^esub>^2 \<ge> 0" unfolding ith_def by auto
  have "(\<Sum>j\<in>{1..(vlen v)}. v\<^bsub>j\<^esub>^2) \<ge> 0" by (simp add: sum_nonneg)
  with real_sqrt_ge_zero have "sqrt (\<Sum>j\<in>{1..(vlen v)}. v\<^bsub>j\<^esub>^2) \<ge> 0" .
  thus ?thesis unfolding norm_def .
qed

text \<open>We now prove an intermediary lemma regarding double summation.\<close>

lemma double_sum_aux:
  fixes f::"nat \<Rightarrow> real"
  shows
  "(\<Sum>k\<in>{1..n}. (\<Sum>j\<in>{1..n}. f k * g j)) =
   (\<Sum>k\<in>{1..n}. (\<Sum>j\<in>{1..n}. (f k * g j + f j * g k) / 2))"
proof -
  have
    "2 * (\<Sum>k\<in>{1..n}. (\<Sum>j\<in>{1..n}. f k * g j)) =
    (\<Sum>k\<in>{1..n}. (\<Sum>j\<in>{1..n}. f k * g j)) +
    (\<Sum>k\<in>{1..n}. (\<Sum>j\<in>{1..n}. f k * g j))"
    by simp
  also have
    "\<dots> =
    (\<Sum>k\<in>{1..n}. (\<Sum>j\<in>{1..n}. f k * g j)) +
    (\<Sum>k\<in>{1..n}. (\<Sum>j\<in>{1..n}. f j * g k))"
    by (simp only: double_sum_equiv)
  also have
    "\<dots> =
    (\<Sum>k\<in>{1..n}. (\<Sum>j\<in>{1..n}. f k * g j + f j * g k))"
    by (auto simp add: sum.distrib)
  finally have
    "2 * (\<Sum>k\<in>{1..n}. (\<Sum>j\<in>{1..n}. f k * g j)) =
    (\<Sum>k\<in>{1..n}. (\<Sum>j\<in>{1..n}. f k * g j + f j * g k))" .
  hence
    "(\<Sum>k\<in>{1..n}. (\<Sum>j\<in>{1..n}. f k * g j)) =
     (\<Sum>k\<in>{1..n}. (\<Sum>j\<in>{1..n}. (f k * g j + f j * g k)))*(1/2)"
    by auto
  also have
    "\<dots> =
     (\<Sum>k\<in>{1..n}. (\<Sum>j\<in>{1..n}. (f k * g j + f j * g k)*(1/2)))"
    by (simp add: sum_distrib_left mult.commute)
  finally show ?thesis by (auto simp add: inverse_eq_divide)
qed

text \<open>The final theorem can now be proven. It is a simple forward
proof that uses properties of double summation and the preceding
lemma.\<close>

theorem CauchySchwarzReal:
  fixes x::vector
  assumes "vlen x = vlen y"
  shows "\<bar>x\<cdot>y\<bar> \<le> \<parallel>x\<parallel>*\<parallel>y\<parallel>"
proof -
  have "\<bar>x\<cdot>y\<bar>^2 \<le> (\<parallel>x\<parallel>*\<parallel>y\<parallel>)^2"
  proof -
    txt \<open>We can rewrite the goal in the following form ...\<close>
    have "(\<parallel>x\<parallel>*\<parallel>y\<parallel>)^2 - \<bar>x\<cdot>y\<bar>^2 \<ge> 0"
    proof -
      obtain n where nx: "n = vlen x" by simp
      with \<open>vlen x = vlen y\<close> have ny: "n = vlen y" by simp
      {
        txt \<open>Some preliminary simplification rules.\<close>
        have "(\<Sum>j\<in>{1..n}. x\<^bsub>j\<^esub>^2) \<ge> 0" by (simp add: sum_nonneg)
        hence xp: "(sqrt (\<Sum>j\<in>{1..n}. x\<^bsub>j\<^esub>^2))^2 = (\<Sum>j\<in>{1..n}. x\<^bsub>j\<^esub>^2)"
          by (rule real_sqrt_pow2)

        have "(\<Sum>j\<in>{1..n}. y\<^bsub>j\<^esub>^2) \<ge> 0" by (simp add: sum_nonneg)
        hence yp: "(sqrt (\<Sum>j\<in>{1..n}. y\<^bsub>j\<^esub>^2))^2 = (\<Sum>j\<in>{1..n}. y\<^bsub>j\<^esub>^2)"
          by (rule real_sqrt_pow2)

        txt \<open>The main result of this section is that \<open>(\<parallel>x\<parallel>*\<parallel>y\<parallel>)^2\<close> can be written as a double sum.\<close>
        have
          "(\<parallel>x\<parallel>*\<parallel>y\<parallel>)^2 = \<parallel>x\<parallel>^2 * \<parallel>y\<parallel>^2"
          by (simp add: real_sq_exp)
        also from nx ny have
          "\<dots> = (sqrt (\<Sum>j\<in>{1..n}. x\<^bsub>j\<^esub>^2))^2 * (sqrt (\<Sum>j\<in>{1..n}. y\<^bsub>j\<^esub>^2))^2"
          unfolding norm_def by auto
        also from xp yp have
          "\<dots> = (\<Sum>j\<in>{1..n}. x\<^bsub>j\<^esub>^2)*(\<Sum>j\<in>{1..n}. y\<^bsub>j\<^esub>^2)"
          by simp
        also from sum_product have
          "\<dots> = (\<Sum>k\<in>{1..n}. (\<Sum>j\<in>{1..n}. (x\<^bsub>k\<^esub>^2)*(y\<^bsub>j\<^esub>^2)))" .
        finally have
          "(\<parallel>x\<parallel>*\<parallel>y\<parallel>)^2 = (\<Sum>k\<in>{1..n}. (\<Sum>j\<in>{1..n}. (x\<^bsub>k\<^esub>^2)*(y\<^bsub>j\<^esub>^2)))" .
      }
      moreover
      {
        txt \<open>We also show that \<open>\<bar>x\<cdot>y\<bar>^2\<close> can be expressed as a double sum.\<close>
        have
          "\<bar>x\<cdot>y\<bar>^2 = (x\<cdot>y)^2"
          by simp
        also from nx have
          "\<dots> = (\<Sum>j\<in>{1..n}. x\<^bsub>j\<^esub>*y\<^bsub>j\<^esub>)^2"
          unfolding dot_def by simp
        also from real_sq have
          "\<dots> = (\<Sum>j\<in>{1..n}. x\<^bsub>j\<^esub>*y\<^bsub>j\<^esub>)*(\<Sum>j\<in>{1..n}. x\<^bsub>j\<^esub>*y\<^bsub>j\<^esub>)"
          by simp
        also from sum_product have
          "\<dots> = (\<Sum>k\<in>{1..n}. (\<Sum>j\<in>{1..n}. (x\<^bsub>k\<^esub>*y\<^bsub>k\<^esub>)*(x\<^bsub>j\<^esub>*y\<^bsub>j\<^esub>)))" .
        finally have
          "\<bar>x\<cdot>y\<bar>^2 = (\<Sum>k\<in>{1..n}. (\<Sum>j\<in>{1..n}. (x\<^bsub>k\<^esub>*y\<^bsub>k\<^esub>)*(x\<^bsub>j\<^esub>*y\<^bsub>j\<^esub>)))" .
      }
      txt \<open>We now manipulate the double sum expressions to get the
      required inequality.\<close>
      ultimately have
        "(\<parallel>x\<parallel>*\<parallel>y\<parallel>)^2 - \<bar>x\<cdot>y\<bar>^2 =
         (\<Sum>k\<in>{1..n}. (\<Sum>j\<in>{1..n}. (x\<^bsub>k\<^esub>^2)*(y\<^bsub>j\<^esub>^2))) -
         (\<Sum>k\<in>{1..n}. (\<Sum>j\<in>{1..n}. (x\<^bsub>k\<^esub>*y\<^bsub>k\<^esub>)*(x\<^bsub>j\<^esub>*y\<^bsub>j\<^esub>)))"
        by simp
      also have
        "\<dots> =
         (\<Sum>k\<in>{1..n}. (\<Sum>j\<in>{1..n}. ((x\<^bsub>k\<^esub>^2*y\<^bsub>j\<^esub>^2) + (x\<^bsub>j\<^esub>^2*y\<^bsub>k\<^esub>^2))/2)) -
         (\<Sum>k\<in>{1..n}. (\<Sum>j\<in>{1..n}. (x\<^bsub>k\<^esub>*y\<^bsub>k\<^esub>)*(x\<^bsub>j\<^esub>*y\<^bsub>j\<^esub>)))"
        by (simp only: double_sum_aux)
      also have
        "\<dots> =
         (\<Sum>k\<in>{1..n}.  (\<Sum>j\<in>{1..n}. ((x\<^bsub>k\<^esub>^2*y\<^bsub>j\<^esub>^2) + (x\<^bsub>j\<^esub>^2*y\<^bsub>k\<^esub>^2))/2 - (x\<^bsub>k\<^esub>*y\<^bsub>k\<^esub>)*(x\<^bsub>j\<^esub>*y\<^bsub>j\<^esub>)))"
        by (auto simp add: sum_subtractf)
      also have
        "\<dots> =
         (\<Sum>k\<in>{1..n}.  (\<Sum>j\<in>{1..n}. (inverse 2)*2*
         (((x\<^bsub>k\<^esub>^2*y\<^bsub>j\<^esub>^2) + (x\<^bsub>j\<^esub>^2*y\<^bsub>k\<^esub>^2))*(1/2) - (x\<^bsub>k\<^esub>*y\<^bsub>k\<^esub>)*(x\<^bsub>j\<^esub>*y\<^bsub>j\<^esub>))))"
        by auto
      also have
        "\<dots> =
         (\<Sum>k\<in>{1..n}.  (\<Sum>j\<in>{1..n}. (inverse 2)*(2*
        (((x\<^bsub>k\<^esub>^2*y\<^bsub>j\<^esub>^2) + (x\<^bsub>j\<^esub>^2*y\<^bsub>k\<^esub>^2))*(1/2) - (x\<^bsub>k\<^esub>*y\<^bsub>k\<^esub>)*(x\<^bsub>j\<^esub>*y\<^bsub>j\<^esub>)))))"
        by (simp only: mult.assoc)
      also have
        "\<dots> =
         (\<Sum>k\<in>{1..n}.  (\<Sum>j\<in>{1..n}. (inverse 2)*
        ((((x\<^bsub>k\<^esub>^2*y\<^bsub>j\<^esub>^2) + (x\<^bsub>j\<^esub>^2*y\<^bsub>k\<^esub>^2))*2*(inverse 2) - 2*(x\<^bsub>k\<^esub>*y\<^bsub>k\<^esub>)*(x\<^bsub>j\<^esub>*y\<^bsub>j\<^esub>)))))"
        by (auto simp add: distrib_right mult.assoc ac_simps)
      also have
        "\<dots> =
        (\<Sum>k\<in>{1..n}.  (\<Sum>j\<in>{1..n}. (inverse 2)*
        ((((x\<^bsub>k\<^esub>^2*y\<^bsub>j\<^esub>^2) + (x\<^bsub>j\<^esub>^2*y\<^bsub>k\<^esub>^2)) - 2*(x\<^bsub>k\<^esub>*y\<^bsub>k\<^esub>)*(x\<^bsub>j\<^esub>*y\<^bsub>j\<^esub>)))))"
        by (simp only: mult.assoc, simp)
      also have
        "\<dots> =
         (inverse 2)*(\<Sum>k\<in>{1..n}. (\<Sum>j\<in>{1..n}.
         (((x\<^bsub>k\<^esub>^2*y\<^bsub>j\<^esub>^2) + (x\<^bsub>j\<^esub>^2*y\<^bsub>k\<^esub>^2)) - 2*(x\<^bsub>k\<^esub>*y\<^bsub>k\<^esub>)*(x\<^bsub>j\<^esub>*y\<^bsub>j\<^esub>))))"
        by (simp only: sum_distrib_left)
      also have
        "\<dots> =
         (inverse 2)*(\<Sum>k\<in>{1..n}. (\<Sum>j\<in>{1..n}. (x\<^bsub>k\<^esub>*y\<^bsub>j\<^esub> - x\<^bsub>j\<^esub>*y\<^bsub>k\<^esub>)^2))"
        by (simp only: power2_diff real_sq_exp, auto simp add: ac_simps)
      also have "\<dots> \<ge> 0"
      proof -
        have "(\<Sum>k\<in>{1..n}. (\<Sum>j\<in>{1..n}. (x\<^bsub>k\<^esub>*y\<^bsub>j\<^esub> - x\<^bsub>j\<^esub>*y\<^bsub>k\<^esub>)^2)) \<ge> 0"
          by (simp add: sum_nonneg)
        thus ?thesis by simp
      qed
      finally show "(\<parallel>x\<parallel>*\<parallel>y\<parallel>)^2 - \<bar>x\<cdot>y\<bar>^2 \<ge> 0" .
    qed
    thus ?thesis by simp
  qed
  moreover have "0 \<le> \<parallel>x\<parallel>*\<parallel>y\<parallel>"
    by (auto simp add: norm_pos)
  ultimately show ?thesis by (rule power2_le_imp_le)
qed

end
