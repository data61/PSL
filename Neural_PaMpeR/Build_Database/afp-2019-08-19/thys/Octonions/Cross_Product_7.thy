(* Title:      Cross_Product_7.thy
   Author:     Angeliki Koutsoukou-Argyraki, University of Cambridge
   Date:       September 2018
*)
section\<open>Vector Cross Product in 7 Dimensions\<close>
theory Cross_Product_7
  imports "HOL-Analysis.Analysis" 
begin

subsection\<open>Elementary auxiliary lemmas.\<close>

lemma exhaust_7:
  fixes x :: 7
  shows "x = 1 \<or> x = 2 \<or> x = 3 \<or> x = 4 \<or> x = 5 \<or> x = 6  \<or> x = 7 "
proof (induct x)
  case (of_int z)
  then have "0 \<le> z" and "z < 7" by simp_all
  then have "z = 0 \<or> z = 1 \<or> z = 2 \<or> z = 3 \<or> z = 4 \<or> z =5\<or> z = 6 \<or> z =7   " by arith
  then show ?case by auto
qed

lemma forall_7: "(\<forall>i::7. P i) \<longleftrightarrow> P 1 \<and> P 2 \<and> P 3\<and> P 4 \<and> P 5 \<and> P 6\<and> P 7  "
  by (metis exhaust_7)

lemma vector_7 [simp]:
 "(vector [x1,x2,x3,x4,x5,x6,x7] ::('a::zero)^7)$1 = x1"
 "(vector [x1,x2,x3,x4,x5,x6,x7] ::('a::zero)^7)$2 = x2"
 "(vector [x1,x2,x3,x4,x5,x6,x7] ::('a::zero)^7)$3 = x3"
 "(vector [x1,x2,x3,x4,x5,x6,x7] ::('a::zero)^7)$4 = x4"
 "(vector [x1,x2,x3,x4,x5,x6,x7] ::('a::zero)^7)$5 = x5"
 "(vector [x1,x2,x3,x4,x5,x6,x7] ::('a::zero)^7)$6 = x6"
 "(vector [x1,x2,x3,x4,x5,x6,x7] ::('a::zero)^7)$7 = x7"
  unfolding vector_def by auto

lemma forall_vector_7:
 "(\<forall>v::'a::zero^7. P v) \<longleftrightarrow> (\<forall>x1 x2 x3 x4 x5 x6 x7. P(vector[x1, x2, x3, x4, x5, x6, x7]))"
  apply auto
  apply (erule_tac x="v$1" in allE)
  apply (erule_tac x="v$2" in allE)
  apply (erule_tac x="v$3" in allE)
  apply (erule_tac x="v$4" in allE)
  apply (erule_tac x="v$5" in allE)
  apply (erule_tac x="v$6" in allE)
  apply (erule_tac x="v$7" in allE)
  apply (subgoal_tac "vector [v$1, v$2, v$3, v$4, v$5, v$6, v$7] = v")
  apply simp
  apply (vector vector_def)
  apply (simp add: forall_7)
  done

lemma UNIV_7: "UNIV = {1::7, 2::7, 3::7, 4::7, 5::7, 6::7, 7::7}"
  using exhaust_7 by auto

lemma sum_7: "sum f (UNIV::7 set) = f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7"
  unfolding UNIV_7 by (simp add: ac_simps)

lemma not_equal_vector7 : 
  fixes x::"real^7" and  y::"real^7"  
  assumes "x = vector[x1,x2,x3,x4,x5,x6,x7] " and "y= vector [y1,y2,y3,y4,y5,y6,y7]"
and  "x$1 \<noteq> y$1 \<or> x$2 \<noteq> y$2 \<or> x$3 \<noteq> y$3 \<or> x$4 \<noteq> y$4 \<or> x$5 \<noteq> y$5 \<or> x$6 \<noteq> y$6 \<or>  x$7 \<noteq> y$7    "
shows "x \<noteq> y"  using assms by blast

lemma equal_vector7:
  fixes  x::"real^7" and  y::"real^7"  
 assumes "x = vector[x1,x2,x3,x4,x5,x6,x7] " and "y= vector [y1,y2,y3,y4,y5,y6,y7]"
and "x = y"
shows "x$1 = y$1 \<and> x$2 = y$2 \<and> x$3 = y$3 \<and> x$4 = y$4 \<and> x$5 = y$5 \<and> x$6 = y$6 \<and>  x$7 = y$7    "
  using assms by blast

lemma numeral_4_eq_4: "4 = Suc( Suc (Suc (Suc 0)))"
  by (simp add: eval_nat_numeral)
lemma numeral_5_eq_5: "5 = Suc(Suc( Suc (Suc (Suc 0))))"
  by (simp add: eval_nat_numeral)
lemma numeral_6_eq_6: "6 = Suc( Suc(Suc( Suc (Suc (Suc 0)))))"
  by (simp add: eval_nat_numeral)
lemma numeral_7_eq_7: "7 = Suc(Suc( Suc(Suc( Suc (Suc (Suc 0))))))"
  by (simp add: eval_nat_numeral)

subsection\<open>The definition of the 7D cross product and related lemmas\<close>

context includes no_Set_Product_syntax 
begin (* locally disable syntax for set product, to avoid warnings *)

text \<open>Note: in total there exist 480 equivalent  multiplication tables for the definition,
 the following is based on the one most widely used: \<close>

definition cross7 :: "[real^7, real^7] \<Rightarrow> real^7"  (infixr "\<times>\<^sub>7" 80)
  where "a \<times>\<^sub>7 b \<equiv>
    vector [a$2 * b$4 - a$4 * b$2 +  a$3 * b$7 - a$7 * b$3  +  a$5 * b$6 - a$6 * b$5 ,
            a$3 * b$5 - a$5 * b$3 +  a$4 * b$1 - a$1 * b$4  +  a$6 * b$7 - a$7 * b$6 ,
            a$4 * b$6 - a$6 * b$4 +  a$5 * b$2 - a$2 * b$5  +  a$7 * b$1 - a$1 * b$7 ,
            a$5 * b$7 - a$7 * b$5 +  a$6 * b$3 - a$3 * b$6  +  a$1 * b$2 - a$2 * b$1 ,
            a$6 * b$1 - a$1 * b$6 +  a$7 * b$4 - a$4 * b$7  +  a$2 * b$3 - a$3 * b$2 ,
            a$7 * b$2 - a$2 * b$7 +  a$1 * b$5 - a$5 * b$1  +  a$3 * b$4 - a$4 * b$3 ,
            a$1 * b$3 - a$3 * b$1 +  a$2 * b$6 - a$6 * b$2  +  a$4 * b$5 - a$5 * b$4 ]"

end

bundle cross7_syntax begin
notation cross7 (infixr "\<times>\<^sub>7" 80)
no_notation Product_Type.Times (infixr "\<times>\<^sub>7" 80)
end

bundle no_cross7_syntax begin
no_notation cross7 (infixr "\<times>\<^sub>7" 80)
notation Product_Type.Times (infixr "\<times>\<^sub>7" 80)
end

unbundle cross7_syntax

lemmas cross7_simps = cross7_def inner_vec_def sum_7 det_def vec_eq_iff vector_def algebra_simps

lemma dot_cross7_self: "x \<bullet> (x \<times>\<^sub>7 y) = 0" "x \<bullet> (y \<times>\<^sub>7 x) = 0" "(x \<times>\<^sub>7 y) \<bullet> y = 0" "(y \<times>\<^sub>7 x) \<bullet> y = 0"
  by (simp_all add: orthogonal_def cross7_simps)

lemma orthogonal_cross7: "orthogonal (x \<times>\<^sub>7 y) x" "orthogonal (x \<times>\<^sub>7 y) y"
                         "orthogonal y (x\<times>\<^sub>7  y)" "orthogonal (x \<times>\<^sub>7 y) x"
  by (simp_all add: orthogonal_def dot_cross7_self)

lemma cross7_zero_left [simp]:  "0 \<times>\<^sub>7 x = 0" 
  and cross7_zero_right [simp]: "x \<times>\<^sub>7 0 = 0"
  by (simp_all add: cross7_simps)

lemma cross7_skew: "(x \<times>\<^sub>7 y) = -(y \<times>\<^sub>7 x)" 
  by (simp add: cross7_simps)

lemma cross7_refl [simp]: "x \<times>\<^sub>7 x = 0" 
  by (simp add: cross7_simps)

lemma cross7_add_left: "(x + y) \<times>\<^sub>7 z = (x \<times>\<^sub>7 z) + (y \<times>\<^sub>7 z)" 
  and   cross7_add_right: "x \<times>\<^sub>7 (y + z) = (x \<times>\<^sub>7 y) + (x \<times>\<^sub>7 z)"
  by (simp_all add: cross7_simps)

lemma cross7_mult_left: "(c *\<^sub>R x) \<times>\<^sub>7 y = c *\<^sub>R (x \<times>\<^sub>7 y)" 
  and  cross7_mult_right: "x \<times>\<^sub>7 (c *\<^sub>R y) = c *\<^sub>R (x \<times>\<^sub>7 y)" 
  by (simp_all add: cross7_simps)

lemma cross7_minus_left [simp]: "(-x) \<times>\<^sub>7 y = - (x \<times>\<^sub>7 y)" 
and cross7_minus_right [simp]: "x \<times>\<^sub>7 -y = - (x \<times>\<^sub>7 y)" 
  by (simp_all add: cross7_simps)

lemma left_diff_distrib: "(x - y) \<times>\<^sub>7 z = x \<times>\<^sub>7 z - y \<times>\<^sub>7 z"
  and  right_diff_distrib: "x \<times>\<^sub>7 (y - z) = x \<times>\<^sub>7 y - x \<times>\<^sub>7 z"  
  by (simp_all add: cross7_simps)

hide_fact (open) left_diff_distrib right_diff_distrib
 
lemma cross7_triple1: "(x \<times>\<^sub>7 y) \<bullet> z = (y \<times>\<^sub>7 z) \<bullet> x" 
and  cross7_triple2: "(x \<times>\<^sub>7 y) \<bullet> z = x \<bullet> (y \<times>\<^sub>7 z)  " 
  by (simp_all add: cross7_def inner_vec_def sum_7 vec_eq_iff algebra_simps)

lemma scalar7_triple1: "x \<bullet> (y \<times>\<^sub>7 z) = y \<bullet> (z \<times>\<^sub>7 x)"
 and  scalar7_triple2: "x \<bullet> (y \<times>\<^sub>7 z) = z \<bullet> (x \<times>\<^sub>7 y )   "
  by (simp_all add: cross7_def inner_vec_def sum_7 vec_eq_iff algebra_simps)

lemma cross7_components:
  "(x \<times>\<^sub>7 y)$1 = x$2 * y$4 - x$4 * y$2 + x$3 * y$7 -  x$7 * y$3 +  x$5 * y$6 -  x$6 * y$5  "
  "(x \<times>\<^sub>7 y)$2 = x$4 * y$1 - x$1 * y$4 + x$3 * y$5 -  x$5 * y$3 +  x$6 * y$7 -  x$7 * y$6  "
  "(x \<times>\<^sub>7 y)$3 = x$5 * y$2 - x$2 * y$5 + x$4 * y$6 -  x$6 * y$4 +  x$7 * y$1 -  x$1 * y$7  "
  "(x \<times>\<^sub>7 y)$4 = x$1 * y$2 - x$2 * y$1 + x$6 * y$3 -  x$3 * y$6 +  x$5 * y$7 -  x$7 * y$5  "
  "(x \<times>\<^sub>7 y)$5 = x$6 * y$1 - x$1 * y$6 + x$2 * y$3 -  x$3 * y$2 +  x$7 * y$4 -  x$4 * y$7  "
  "(x \<times>\<^sub>7 y)$6 = x$1 * y$5 - x$5 * y$1 + x$7 * y$2 -  x$2 * y$7 +  x$3 * y$4 -  x$4 * y$3  "
  "(x \<times>\<^sub>7 y)$7 = x$1 * y$3 - x$3 * y$1 + x$4 * y$5 -  x$5 * y$4 +  x$2 * y$6 -  x$6 * y$2  "
  by (simp_all add: cross7_def inner_vec_def sum_7 vec_eq_iff algebra_simps)

text \<open>Nonassociativity of the 7D cross product showed using a counterexample\<close>

lemma cross7_nonassociative: 
   " \<not> (\<forall> (c::real^7) (a::real^7) ( b::real^7) .  c \<times>\<^sub>7  (a \<times>\<^sub>7 b) = (c \<times>\<^sub>7 a ) \<times>\<^sub>7 b) "
proof-
  have *: " \<exists> (c::real^7) (a::real^7) ( b::real^7) .  c \<times>\<^sub>7  (a \<times>\<^sub>7 b) \<noteq> (c \<times>\<^sub>7 a ) \<times>\<^sub>7 b "
proof-
  define f::"real^7" where "f = vector[ 0, 0, 0, 0, 0, 1, 1 ]"
  define g::"real^7" where "g = vector[ 0, 0, 0, 1, 0, 0, 0 ]"
  define h::"real^7" where "h = vector[ 1, 0, 1, 0, 0, 0, 0 ]"
  define u where " u= (g \<times>\<^sub>7 h) "
  define v where " v= (f \<times>\<^sub>7 g) "
  
  have 1:" u  = vector[0, 1, 0, 0, 0, -1, 0]"
    unfolding cross7_def g_def h_def f_def u_def by simp
  have 3:"  f \<times>\<^sub>7 u = vector[0, 1, 0, 0, 0, 1, -1 ] "
    unfolding cross7_def f_def  using 1 by simp

  have 2:" v  = vector[0, 0, -1, 0, 1, 0, 0]"
    unfolding cross7_def g_def h_def f_def v_def by simp
  have  4:"  v \<times>\<^sub>7 h = vector[0, -1, 0, 0, 0, -1, 1 ] "
    unfolding cross7_def h_def  using 2 by simp

  define x::"real^7" where "x= vector[0, 1, 0, 0, 0, 1, -1]  "
  define y::"real^7" where "y= vector[0, -1, 0, 0, 0,-1, 1]  "

    have *:  "x$2 =  1" unfolding x_def by simp
    have **: "y$2 = -1" unfolding y_def by simp
 
    have ***: "x \<noteq> y" using * ** by auto
    have 5: " f \<times>\<^sub>7 u \<noteq>  v \<times>\<^sub>7 h" 
      unfolding x_def y_def 
      using ***
      by (simp add: "3" "4" x_def y_def)

have  6:"  f \<times>\<^sub>7  (g \<times>\<^sub>7 h) \<noteq> (f \<times>\<^sub>7 g ) \<times>\<^sub>7 h " using 5  by (simp add: u_def v_def)

 show ?thesis unfolding f_def g_def h_def using 6 by blast
qed
show ?thesis using * by blast
qed

text \<open>The 7D cross product does not satisfy the Jacobi Identity(shown using a counterexample) \<close>

lemma cross7_not_Jacobi: 
   " \<not> (\<forall> (c::real^7) (a::real^7) ( b::real^7) . (c \<times>\<^sub>7 a ) \<times>\<^sub>7 b +   (b \<times>\<^sub>7 c) \<times>\<^sub>7 a 
+  (a \<times>\<^sub>7 b ) \<times>\<^sub>7 c =0     ) "

proof-
  have *: " \<exists> (c::real^7) (a::real^7) ( b::real^7) . (c \<times>\<^sub>7 a ) \<times>\<^sub>7 b +   (b \<times>\<^sub>7 c) \<times>\<^sub>7 a 
+  (a \<times>\<^sub>7 b ) \<times>\<^sub>7 c \<noteq>0      "
  proof-

  define  f::"real^7"  where " f= vector[ 0, 0, 0, 0, 0, 1, 1 ] "
  define  g::"real^7"  where " g= vector[ 0, 0, 0, 1, 0, 0, 0 ] "
  define  h::"real^7" where " h= vector[ 1, 0, 1, 0, 0, 0, 0 ] "
  define u where " u= (g \<times>\<^sub>7 h) "
  define v where " v= (f \<times>\<^sub>7 g) "
  define w where " w = (h \<times>\<^sub>7 f)  "

  have 1:" u  = vector[0, 1, 0, 0, 0, -1, 0]"
    unfolding cross7_def g_def h_def f_def u_def by simp
  have 3:" u \<times>\<^sub>7 f = vector[0,- 1, 0, 0, 0,- 1, 1 ] "
    unfolding cross7_def f_def  using 1 by simp 

  have 2:" v  = vector[0, 0, -1, 0, 1, 0, 0]"
    unfolding cross7_def g_def h_def f_def v_def by simp
  have  4:"  v \<times>\<^sub>7 h = vector[0, -1, 0, 0, 0, -1, 1 ] "
    unfolding cross7_def h_def  using 2 by simp
  have 8: " w  = vector[1, 0, -1, -1, -1, 0, 0]"
    unfolding cross7_def  h_def f_def w_def by simp
  have 9: "  w \<times>\<^sub>7 g  = vector[0, -1, 0, 0, 0, -1, 1]"
    unfolding cross7_def  h_def f_def w_def g_def apply simp done
  have &: "(u \<times>\<^sub>7 f)$2+( v \<times>\<^sub>7 h) $2+( w \<times>\<^sub>7 g) $2 =-3" using 3 4 9 by simp
  have &&: " u \<times>\<^sub>7 f + v \<times>\<^sub>7 h +  w \<times>\<^sub>7 g \<noteq> 0 " using &
    by (metis vector_add_component zero_index zero_neq_neg_numeral)

  show ?thesis  using && u_def v_def w_def by blast
  qed

  show ?thesis using * by blast
qed

text\<open>The vector triple product property fulfilled for the 3D cross product does not hold
for the 7D cross product. Shown below with a counterexample.  \<close>

lemma cross7_not_vectortriple:
  "\<not>(\<forall> (c::real^7) (a::real^7) ( b::real^7).( c \<times>\<^sub>7 a ) \<times>\<^sub>7 b = (c  \<bullet> b ) *\<^sub>R a -  (c  \<bullet> a )*\<^sub>R b)"
proof-
  have *: "\<exists>(c::real^7) (a::real^7) ( b::real^7). (c \<times>\<^sub>7 a) \<times>\<^sub>7 b \<noteq> (c \<bullet> b ) *\<^sub>R a -  (c \<bullet> a )*\<^sub>R b"
  proof-
    define g:: "real ^ 7" where "g = vector[0, 0, 0, 1, 0, 0, 0]"
    define h:: "real ^ 7" where "h = vector[1, 0, 1, 0, 0, 0, 0]"
    define f:: "real ^ 7" where "f = vector[0, 0, 0, 0, 0, 1, 1]"
    define u where "u = (g \<times>\<^sub>7 h)"
    have 1: "u = vector[0, 1, 0, 0, 0, -1, 0]"
      unfolding cross7_def g_def h_def f_def u_def by simp
    have 2:" u \<times>\<^sub>7 f = vector[0,- 1, 0, 0, 0,- 1, 1 ]"
      unfolding cross7_def f_def using 1 by simp 
    have 3: "(g \<bullet> f) *\<^sub>R h = 0" unfolding g_def f_def  inner_vec_def 
      by (simp add: sum_7)
    have 4: "(g \<bullet> h) *\<^sub>R f = 0" unfolding g_def h_def  inner_vec_def 
      by (simp add: sum_7)
    have 5: "(g \<bullet> f) *\<^sub>R h -(g \<bullet> h) *\<^sub>R f = 0"
      using 3 4 by auto
    have 6: "u \<times>\<^sub>7 f \<noteq> 0" using 2
      by (metis one_neq_zero vector_7(7) zero_index)

    have 7: "(g \<times>\<^sub>7 h) \<times>\<^sub>7 f \<noteq> 0" using 2 6 u_def by blast
    have 8: "(g \<times>\<^sub>7 h) \<times>\<^sub>7 f \<noteq> (g \<bullet> f) *\<^sub>R h - (g \<bullet> h ) *\<^sub>R f"
      using 5 7 by simp
    show ?thesis using 8 by auto
  qed
  show ?thesis using * by auto
qed

lemma axis_nth_neq [simp]: "i \<noteq> j \<Longrightarrow> axis i x $ j = 0"
  by (simp add: axis_def)

lemma cross7_basis: 
  "(axis 1 1) \<times>\<^sub>7 (axis 2 1) = axis 4 1" "(axis 2 1) \<times>\<^sub>7 (axis 1 1) = -(axis 4 1)" 
  "(axis 2 1) \<times>\<^sub>7 (axis 3 1) = axis 5 1" "(axis 3 1) \<times>\<^sub>7 (axis 2 1) = -(axis 5 1)"
  "(axis 3 1) \<times>\<^sub>7 (axis 4 1) = axis 6 1" "(axis 4 1) \<times>\<^sub>7 (axis 3 1) = -(axis 6 1)"
  "(axis 2 1) \<times>\<^sub>7 (axis 4 1) = axis 1 1" "(axis 4 1) \<times>\<^sub>7 (axis 2 1) = -(axis 1 1)"
  "(axis 4 1) \<times>\<^sub>7 (axis 5 1) = axis 7 1" "(axis 5 1) \<times>\<^sub>7 (axis 4 1) = -(axis 7 1)"
  "(axis 3 1) \<times>\<^sub>7 (axis 5 1) = axis 2 1" "(axis 5 1) \<times>\<^sub>7 (axis 3 1) = -(axis 2 1)"
  "(axis 4 1) \<times>\<^sub>7 (axis 6 1) = axis 3 1" "(axis 6 1) \<times>\<^sub>7 (axis 4 1) = -(axis 3 1)"
  "(axis 5 1) \<times>\<^sub>7 (axis 7 1) = axis 4 1" "(axis 7 1) \<times>\<^sub>7 (axis 5 1) = -(axis 4 1)"
  "(axis 4 1) \<times>\<^sub>7 (axis 1 1) = axis 2 1" "(axis 1 1) \<times>\<^sub>7 (axis 4 1) = -(axis 2 1)"
  "(axis 5 1) \<times>\<^sub>7 (axis 2 1) = axis 3 1" "(axis 2 1) \<times>\<^sub>7 (axis 5 1) = -(axis 3 1)"
  "(axis 6 1) \<times>\<^sub>7 (axis 3 1) = axis 4 1" "(axis 3 1) \<times>\<^sub>7 (axis 6 1) = -(axis 4 1)"
  "(axis 7 1) \<times>\<^sub>7 (axis 4 1) = axis 5 1" "(axis 4 1) \<times>\<^sub>7 (axis 7 1) = -(axis 5 1)"
  "(axis 5 1) \<times>\<^sub>7 (axis 6 1) = axis 1 1" "(axis 6 1) \<times>\<^sub>7 (axis 5 1) = -(axis 1 1)"
  "(axis 6 1) \<times>\<^sub>7 (axis 7 1) = axis 2 1" "(axis 7 1) \<times>\<^sub>7 (axis 6 1) = -(axis 2 1)"
  "(axis 7 1) \<times>\<^sub>7 (axis 1 1) = axis 3 1" "(axis 1 1) \<times>\<^sub>7 (axis 7 1) = -(axis 3 1)"
  "(axis 6 1) \<times>\<^sub>7 (axis 1 1) = axis 5 1" "(axis 1 1) \<times>\<^sub>7 (axis 6 1) = -(axis 5 1)"
  "(axis 7 1) \<times>\<^sub>7 (axis 2 1) = axis 6 1" "(axis 2 1) \<times>\<^sub>7 (axis 7 1) = -(axis 6 1)"
  "(axis 1 1) \<times>\<^sub>7 (axis 3 1) = axis 7 1" "(axis 3 1) \<times>\<^sub>7 (axis 1 1) = -(axis 7 1)"
  "(axis 1 1) \<times>\<^sub>7 (axis 5 1) = axis 6 1" "(axis 5 1) \<times>\<^sub>7 (axis 1 1) = -(axis 6 1)"
  "(axis 2 1) \<times>\<^sub>7 (axis 6 1) = axis 7 1" "(axis 6 1) \<times>\<^sub>7 (axis 2 1) = -(axis 7 1)"
  "(axis 3 1) \<times>\<^sub>7 (axis 7 1) = axis 1 1" "(axis 7 1) \<times>\<^sub>7 (axis 3 1) = -(axis 1 1)"
  by (simp_all add: vec_eq_iff forall_7 cross7_components)
 
lemma cross7_basis_zero:
 "  u=0  \<Longrightarrow> (u \<times>\<^sub>7 axis 1 1 = 0) \<and> (u \<times>\<^sub>7 axis 2 1 = 0) \<and> (u \<times>\<^sub>7 axis 3 1 = 0)
 \<and> (u \<times>\<^sub>7 axis 4 1 = 0) \<and> (u \<times>\<^sub>7 axis 5 1 = 0 ) \<and> (u \<times>\<^sub>7 axis 6 1 = 0 )
 \<and> (u \<times>\<^sub>7 axis 7 1 = 0)  "
  by auto

lemma cross7_basis_nonzero:
"\<not> (u \<times>\<^sub>7 axis 1 1 = 0) \<or> \<not> (u \<times>\<^sub>7 axis 2 1 = 0) \<or> \<not> (u \<times>\<^sub>7 axis 3 1 = 0)
 \<or> \<not>   (u \<times>\<^sub>7 axis 4 1 = 0)  \<or> \<not>  (u \<times>\<^sub>7 axis 5 1 = 0 ) \<or> \<not>   (u \<times>\<^sub>7 axis 6 1 = 0 )
 \<or> \<not>   (u \<times>\<^sub>7 axis 7 1 = 0)  \<Longrightarrow> u \<noteq> 0"
  by auto

text\<open>Pythagorean theorem/magnitude\<close>

lemma norm_square_vec_eq: "norm x ^ 2 = (\<Sum>i\<in>UNIV. x $ i ^ 2)"
  by (auto simp: norm_vec_def L2_set_def intro!: sum_nonneg)

lemma norm_cross7_dot_magnitude: "(norm (x \<times>\<^sub>7 y))\<^sup>2 = (norm x)\<^sup>2 * (norm y)\<^sup>2 - (x \<bullet> y)\<^sup>2"
  unfolding norm_square_vec_eq sum_7 cross7_components inner_vec_def real_norm_def inner_real_def
  by algebra

lemma cross7_eq_0: "x \<times>\<^sub>7 y = 0 \<longleftrightarrow> collinear {0, x, y}"
proof -
  have "x \<times>\<^sub>7 y = 0 \<longleftrightarrow> norm (x \<times>\<^sub>7 y) = 0"
    by simp
  also have "... \<longleftrightarrow> (norm x * norm y)\<^sup>2 = (x \<bullet> y)\<^sup>2"
    using norm_cross7_dot_magnitude [of x y] by (auto simp: power_mult_distrib)
  also have "... \<longleftrightarrow> \<bar>x \<bullet> y\<bar> = norm x * norm y"
    using power2_eq_iff
    by (metis (mono_tags, hide_lams) abs_minus abs_norm_cancel
              abs_power2 norm_mult power_abs real_norm_def) 
  also have "... \<longleftrightarrow> collinear {0, x, y}"
    by (rule norm_cauchy_schwarz_equal)
  finally show ?thesis .
qed

lemma cross7_eq_self: "x \<times>\<^sub>7 y = x \<longleftrightarrow> x = 0" "x \<times>\<^sub>7 y = y \<longleftrightarrow> y = 0"
  apply (metis cross7_zero_left dot_cross7_self(1) inner_eq_zero_iff)
  apply (metis cross7_zero_right dot_cross7_self(2) inner_eq_zero_iff)
  done

lemma norm_and_cross7_eq_0:
   "x \<bullet> y = 0 \<and> x \<times>\<^sub>7 y = 0 \<longleftrightarrow> x = 0 \<or> y = 0" (is "?lhs = ?rhs")
proof 
  assume ?lhs
  then show ?rhs
    using cross7_eq_0 norm_cauchy_schwarz_equal by force
next
assume ?rhs
  then show ?lhs
    by auto
qed

lemma bilinear_cross7: "bilinear (\<times>\<^sub>7)"
  apply (auto simp add: bilinear_def linear_def)
  apply unfold_locales
  apply (simp_all add: cross7_add_right cross7_mult_right cross7_add_left cross7_mult_left)
  done

subsection\<open>Continuity\<close>

lemma continuous_cross7: "\<lbrakk>continuous F f; continuous F g\<rbrakk> \<Longrightarrow> continuous F (\<lambda>x. f x \<times>\<^sub>7 g x)"
  by (subst continuous_componentwise)(auto intro!: continuous_intros simp: cross7_simps)
 
lemma continuous_on_cross:
  fixes f :: "'a::t2_space \<Rightarrow> real^7"
  shows "\<lbrakk>continuous_on S f; continuous_on S g\<rbrakk> \<Longrightarrow> continuous_on S (\<lambda>x. f x \<times>\<^sub>7 g x)"
  by (simp add: continuous_on_eq_continuous_within continuous_cross7)

end