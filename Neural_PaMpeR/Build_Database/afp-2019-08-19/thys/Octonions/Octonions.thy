(* Title:      Octonions.thy
   Author:     Angeliki Koutsoukou-Argyraki, University of Cambridge
   Date:       September 2018
*)
section\<open>Theory of Octonions\<close>
theory Octonions
  imports Cross_Product_7 
begin

subsection\<open>Basic definitions\<close>

text\<open>As with the complex numbers, coinduction is convenient.\<close>

codatatype octo =
  Octo (Ree: real) (Im1: real) (Im2: real) (Im3: real) (Im4: real) 
       (Im5: real) (Im6: real) (Im7: real)

lemma octo_eqI [intro?]:
  "\<lbrakk>Ree x = Ree y; Im1 x = Im1 y; Im2 x = Im2 y; Im3 x = Im3 y;
    Im4 x = Im4 y;Im5 x = Im5 y;  Im6 x = Im6 y; Im7 x = Im7 y\<rbrakk> \<Longrightarrow> x = y"
  by (rule octo.expand) simp

lemma octo_eq_iff:
  "x = y \<longleftrightarrow> Ree x = Ree y \<and> Im1 x = Im1 y \<and> Im2 x = Im2 y \<and> Im3 x = Im3 y \<and>
             Im4 x = Im4 y \<and> Im5 x = Im5 y \<and> Im6 x = Im6 y  \<and> Im7 x = Im7 y"
  by (auto intro: octo.expand)

context
begin

primcorec octo_e0 :: octo ("e0")
where "Ree e0 = 1" | "Im1 e0 = 0" | "Im2 e0 = 0" | "Im3 e0 = 0"
  | "Im4 e0 = 0" | "Im5 e0 = 0" | "Im6 e0 = 0" | "Im7 e0 = 0"

primcorec octo_e1 :: octo  ("e1")
  where "Ree e1 = 0" | "Im1 e1 = 1" | "Im2 e1 = 0" | "Im3 e1 = 0"
  | "Im4 e1 = 0" | "Im5 e1 = 0" | "Im6 e1 = 0" | "Im7 e1 = 0"

primcorec octo_e2 :: octo  ("e2")
  where "Ree e2 = 0" | "Im1 e2 = 0" | "Im2 e2 = 1" | "Im3 e2 = 0"
  | "Im4 e2 = 0" | "Im5 e2 = 0" | "Im6 e2 = 0" | "Im7 e2 = 0"

primcorec octo_e3 :: octo ("e3")
  where "Ree e3 = 0" | "Im1 e3 = 0" | "Im2 e3 = 0" | "Im3 e3 = 1"
  | "Im4 e3 = 0" | "Im5 e3 = 0" | "Im6 e3 = 0" | "Im7 e3 = 0"

primcorec octo_e4 :: octo ("e4")
  where "Ree e4 = 0" | "Im1 e4 = 0" | "Im2 e4 = 0" | "Im3 e4 = 0"
  | "Im4 e4 = 1" | "Im5 e4 = 0" | "Im6 e4 = 0" | "Im7 e4 = 0"

primcorec octo_e5 :: octo ("e5")
  where "Ree e5 = 0" | "Im1 e5 = 0" | "Im2 e5 = 0" | "Im3 e5 = 0"
  | "Im4 e5 = 0" | "Im5 e5 = 1" | "Im6 e5 = 0" | "Im7 e5 = 0"

primcorec octo_e6 :: octo ("e6")
  where "Ree e6 = 0" | "Im1 e6 = 0" | "Im2 e6 = 0" | "Im3 e6 = 0"
  | "Im4 e6 = 0" | "Im5 e6 = 0" | "Im6 e6 = 1" | "Im7 e6 = 0"

primcorec octo_e7 :: octo ("e7")
  where "Ree e7 = 0" | "Im1 e7 = 0" | "Im2 e7 = 0" | "Im3 e7 = 0"
  | "Im4 e7 = 0" | "Im5 e7 = 0" | "Im6 e7 = 0" | "Im7 e7 = 1"
end

subsection \<open>Addition and Subtraction: An Abelian Group\<close>

instantiation octo :: ab_group_add

begin

primcorec zero_octo
  where "Ree 0 = 0" |"Im1 0 = 0" | "Im2 0 = 0" | "Im3 0 = 0"
 |"Im4 0 = 0" | "Im5 0 = 0" | "Im6 0 = 0" | "Im7 0 = 0"

primcorec plus_octo
  where
    "Ree (x + y) = Ree x + Ree y"
  | "Im1 (x + y) = Im1 x + Im1 y"
  | "Im2 (x + y) = Im2 x + Im2 y"
  | "Im3 (x + y) = Im3 x + Im3 y"
  | "Im4 (x + y) = Im4 x + Im4 y"
  | "Im5 (x + y) = Im5 x + Im5 y"
  | "Im6 (x + y) = Im6 x + Im6 y"
  | "Im7 (x + y) = Im7 x + Im7 y"

primcorec uminus_octo
  where
    "Ree (- x) = - Ree x"
  | "Im1 (- x) = - Im1 x"
  | "Im2 (- x) = - Im2 x"
  | "Im3 (- x) = - Im3 x"
  | "Im4 (- x) = - Im4 x"
  | "Im5 (- x) = - Im5 x"
  | "Im6 (- x) = - Im6 x"
  | "Im7 (- x) = - Im7 x"

primcorec minus_octo
  where
    "Ree (x - y) = Ree x - Ree y"
  | "Im1 (x - y) = Im1 x - Im1 y"
  | "Im2 (x - y) = Im2 x - Im2 y"
  | "Im3 (x - y) = Im3 x - Im3 y"
  | "Im4 (x - y) = Im4 x - Im4 y"
  | "Im5 (x - y) = Im5 x - Im5 y"
  | "Im6 (x - y) = Im6 x - Im6 y"
  | "Im7 (x - y) = Im7 x - Im7 y"

instance
  by standard (simp_all add: octo_eq_iff)

end

lemma octo_eq_0_iff:
  "x = 0 \<longleftrightarrow> Ree x ^ 2 + Im1 x ^ 2 + Im2 x ^ 2 + Im3 x ^ 2 +
               Im4 x ^ 2 + Im5 x ^ 2 + Im6 x ^ 2 + Im7 x ^ 2  = 0"
proof
  assume "(octo.Ree x)\<^sup>2 + (Im1 x)\<^sup>2 + (Im2 x)\<^sup>2 + (Im3 x)\<^sup>2 + (Im4 x)\<^sup>2 + (Im5 x)\<^sup>2 + (Im6 x)\<^sup>2
 + (Im7 x)\<^sup>2 = 0"
  then have "\<forall>qa. qa - x = qa"
    by (simp add: add_nonneg_eq_0_iff minus_octo.ctr)
  then show "x = 0"
    by simp
qed auto

subsection \<open>A Normed Vector Space\<close>

instantiation octo :: real_vector

begin

primcorec scaleR_octo
  where
    "Ree (scaleR r x) = r * Ree x"
  | "Im1 (scaleR r x) = r * Im1 x"
  | "Im2 (scaleR r x) = r * Im2 x"
  | "Im3 (scaleR r x) = r * Im3 x"
  | "Im4 (scaleR r x) = r * Im4 x"
  | "Im5 (scaleR r x) = r * Im5 x"
  | "Im6 (scaleR r x) = r * Im6 x"
  | "Im7 (scaleR r x) = r * Im7 x"

instance
  by standard (auto simp: octo_eq_iff distrib_left distrib_right  scaleR_add_right)

end

instantiation octo::one
begin
primcorec one_octo

  where
   "Ree 1 = 1" |  "Im1 1 = 0"  | "Im2 1 = 0" |  "Im3 1 = 0" |
   "Im4 1 = 0" |  "Im5 1 = 0"  | "Im6 1 = 0" | "Im7 1 = 0" 

instance by standard
end

fun octo_proj
  where
    "octo_proj x 0 = ( Ree (x))"
  | "octo_proj x (Suc 0) = ( Im1(x))"
  | "octo_proj x (Suc (Suc 0)) = ( Im2 ( x))"
  | "octo_proj x (Suc (Suc (Suc 0))) = ( Im3( x))"
  | "octo_proj x (Suc (Suc (Suc (Suc 0)))) = ( Im4( x))"
  | "octo_proj x (Suc(Suc (Suc (Suc (Suc 0))))) = ( Im5( x))"
  | "octo_proj x (Suc(Suc (Suc (Suc (Suc (Suc 0)))))) = ( Im6( x))"
  | "octo_proj x (Suc( Suc(Suc (Suc (Suc (Suc (Suc 0))))))) = ( Im7( x))"

lemma octo_proj_add:
  assumes "i \<le> 7"
  shows "octo_proj (x+y) i = octo_proj x i + octo_proj y i" 
 
proof -
  consider "i = 0" | "i = 1" | "i = 2" | "i = 3" | "i = 4" | "i = 5" | "i = 6" | "i = 7"
    using  assms by force

     then show ?thesis
    by cases (auto simp:  numeral_2_eq_2 numeral_3_eq_3 numeral_4_eq_4 numeral_5_eq_5 
 numeral_6_eq_6  numeral_7_eq_7 numeral_7_eq_7) 
qed

instantiation octo ::real_normed_vector
begin

definition  "norm x = sqrt ((Ree x)\<^sup>2 + (Im1 x)\<^sup>2 + (Im2 x)\<^sup>2 + (Im3 x)\<^sup>2  +
  (Im4 x)\<^sup>2 + (Im5 x)\<^sup>2 + (Im6 x)\<^sup>2+ (Im7 x)\<^sup>2  )" for x::octo 

definition "sgn x = x /\<^sub>R norm x" for x :: octo

definition "dist x y = norm (x - y)" for x y :: octo

definition [code del]:
  "(uniformity :: (octo \<times> octo) filter) = (INF e\<in>{0 <..}. principal {(x, y). dist x y < e})"

definition [code del]:
  "open (U :: octo set) \<longleftrightarrow> (\<forall>x\<in>U. eventually (\<lambda>(x', y). x' = x \<longrightarrow> y \<in> U) uniformity)"

lemma norm_eq_L2: "norm x = L2_set (octo_proj x) {..7}"
  by (simp add: norm_octo_def L2_set_def eval_nat_numeral)

instance proof
  fix r :: real and x y :: octo and S :: "octo set"
  show "(norm x = 0) \<longleftrightarrow> (x = 0)"
    by (simp add: norm_octo_def octo_eq_iff add_nonneg_eq_0_iff)
  have eq: "L2_set (octo_proj (x + y)) {..7} = L2_set (\<lambda>i. octo_proj x i + octo_proj y i) {..7}"
    by (rule L2_set_cong) (auto simp: octo_proj_add)
  show "norm (x + y) \<le> norm x + norm y"
    by (simp add: norm_eq_L2 eq L2_set_triangle_ineq)
  show "norm (scaleR r x) = \<bar>r\<bar> * norm x"
    by (simp add: norm_octo_def octo_eq_iff 
                  power_mult_distrib distrib_left [symmetric] real_sqrt_mult)
qed (rule sgn_octo_def dist_octo_def open_octo_def uniformity_octo_def)+

end

lemma norm_octo_squared:
  "norm x ^ 2 = Ree x ^ 2 + Im1 x ^ 2 + Im2 x ^ 2 + Im3 x ^ 2 +
     Im4 x ^ 2 + Im5 x ^ 2 + Im6 x ^ 2 + Im7 x ^ 2"
  by (simp add: norm_octo_def)

instantiation octo :: real_inner
begin

definition inner_octo where
  "inner_octo x y = Ree x * Ree y + Im1 x * Im1 y + Im2 x * Im2 y + Im3 x * Im3 y
      + Im4 x * Im4 y + Im5 x * Im5 y + Im6 x * Im6 y +  Im7 x * Im7 y " for x y::octo

instance
  by standard (auto simp: inner_octo_def algebra_simps norm_octo_def 
                          power2_eq_square octo_eq_iff add_nonneg_eq_0_iff)

end

lemma octo_inner_1 [simp]: "inner 1 x = Ree x"
 and octo_inner_1_right [simp]: "inner x 1 = Ree x"
  unfolding inner_octo_def by simp_all

lemma octo_inner_e1_left [simp]: "inner e1 x = Im1 x"
 and octo_inner_e1_right [simp]: "inner x e1 = Im1 x"
  unfolding inner_octo_def by simp_all

lemma octo_inner_e2_left [simp]: "inner e2 x = Im2 x"
  and octo_inner_e2_right [simp]: "inner x e2 = Im2 x"
  unfolding inner_octo_def by simp_all

lemma octo_inner_e3_left [simp]: "inner e3 x = Im3 x"
 and  octo_inner_e3_right [simp]: "inner x e3 = Im3 x"
  unfolding inner_octo_def by simp_all

lemma octo_inner_e4_left [simp]: "inner e4 x  = Im4 x"
 and octo_inner_e4_right [simp]: "inner x e4 = Im4 x"
  unfolding inner_octo_def by simp_all

lemma octo_inner_e5_left [simp]: "inner e5 x  = Im5 x"
 and  octo_inner_e5_right [simp]: "inner x e5 = Im5 x"
  unfolding inner_octo_def by simp_all

lemma octo_inner_e6_left [simp]: "inner e6 x  = Im6 x"
 and octo_inner_e6_right [simp]: "inner x e6 = Im6 x"
  unfolding inner_octo_def by simp_all

lemma octo_inner_e7_left [simp]: "inner e7 x  = Im7 x"
 and octo_inner_e7_right [simp]: "inner x e7 = Im7 x"
  unfolding inner_octo_def by simp_all

lemma octo_norm_pow_2_inner: "(norm x) ^ 2 = inner x x " for x::octo
  by (simp add: dot_square_norm)

lemma octo_norm_property:
  "inner x y = (1/2)* ((norm(x+y))^2 - (norm(x))^2 - (norm(y))^2) " for x y ::octo
  by (simp add: dot_norm norm_octo_def)

subsection \<open>The Octonionic product and related properties and lemmas\<close>

text\<open>The multiplication is defined following one of the 480 equivalent multiplication tables
in an analogy to the definition of the 7D cross product. \<close>

instantiation octo :: times
begin

definition times_octo :: "[octo, octo] \<Rightarrow> octo" 
  where 
    "(a * b) =  (let 
    t0 = Ree a * Ree b - Im1 a * Im1 b - Im2 a * Im2 b- Im3 a * Im3 b 
          - Im4 a * Im4 b  - Im5 a * Im5 b - Im6 a * Im6 b  -Im7 a * Im7 b ; 
    t1 =  Ree a * Im1 b +   Im1 a * Ree b + Im2 a * Im4 b +Im3 a * Im7 b -
          Im4 a * Im2  b  +Im5 a * Im6 b - Im6 a * Im5 b - Im7 a * Im3 b ;
    t2 =  Ree a *  Im2 b - Im1 a * Im4 b+ Im2 a  * Ree b + Im3 a * Im5 b 
          + Im4 a * Im1 b  - Im5 a * Im3 b + Im6 a * Im7 b - Im7 a *Im6 b  ;
    t3 =  Ree a * Im3 b -Im1 a * Im7 b -Im2 a *Im5 b +Im3 a * Ree b + Im4 a * Im6 b
         +  Im5 a *Im2 b  - Im6 a * Im4 b + Im7 a * Im1 b ;
    t4 = Ree a * Im4 b + Im1 a * Im2 b - Im2 a * Im1 b -Im3 a * Im6 b + Im4 a * Ree b 
        +Im5 a * Im7 b +Im6 a * Im3 b -Im7 a * Im5 b ;
    t5 = Ree a * Im5 b - Im1 a * Im6 b +Im2 a * Im3 b -Im3 a * Im2 b -Im4 a * Im7 b
         +Im5 a * Ree b  +Im6 a * Im1 b + Im7 a  * Im4 b;
    t6 = Ree a * Im6 b + Im1 a * Im5 b - Im2 a * Im7 b +Im3 a * Im4 b - Im4 a * Im3 b
        -Im5 a * Im1 b + Im6 a * Ree b + Im7 a * Im2 b  ;
    t7 = Ree a * Im7 b + Im1 a * Im3 b +Im2 a * Im6 b - Im3 a * Im1 b + Im4 a * Im5 b
          -Im5 a * Im4 b - Im6 a * Im2 b +Im7 a * Ree b 
  in Octo t0 t1 t2 t3 t4 t5 t6 t7)"

instance by standard

end

instantiation octo ::inverse
begin

primcorec inverse_octo
  where
    "Ree (inverse x) = Ree x / (Ree x ^ 2 + Im1 x ^ 2 + Im2 x ^ 2 + Im3 x ^ 2
      +Im4 x ^ 2 + Im5 x ^ 2 + Im6 x ^ 2 + Im7 x ^2   )"
  | "Im1 (inverse x) = - (Im1 x) / (Ree x ^ 2 + Im1 x ^ 2 + Im2 x ^ 2 + Im3 x ^ 2
             +Im4 x ^ 2 + Im5 x ^ 2 + Im6 x ^ 2 + Im7 x ^2)"
  | "Im2 (inverse x) = - (Im2 x) / (Ree x ^ 2 + Im1 x ^ 2 + Im2 x ^ 2 + Im3 x ^ 2
   +Im4 x ^ 2 + Im5 x ^ 2 + Im6 x ^ 2 + Im7 x ^2 )"
  | "Im3 (inverse x) = - (Im3 x) / (Ree x ^ 2 + Im1 x ^ 2 + Im2 x ^ 2 + Im3 x ^ 2
     +Im4 x ^ 2 + Im5 x ^ 2 + Im6 x ^ 2 + Im7 x ^2    )"
  | "Im4 (inverse x) = - (Im4 x) / (Ree x ^ 2 + Im1 x ^ 2 + Im2 x ^ 2 + Im3 x ^ 2
        +Im4 x ^ 2 + Im5 x ^ 2 + Im6 x ^ 2 + Im7 x ^2    )"
  | "Im5 (inverse x) = - (Im5 x) / (Ree x ^ 2 + Im1 x ^ 2 + Im2 x ^ 2 + Im3 x ^ 2
   +Im4 x ^ 2 + Im5 x ^ 2 + Im6 x ^ 2 + Im7 x ^2)"
  | "Im6 (inverse x) = - (Im6 x) / (Ree x ^ 2 + Im1 x ^ 2 + Im2 x ^ 2 + Im3 x ^ 2
       +Im4 x ^ 2 + Im5 x ^ 2 + Im6 x ^ 2 + Im7 x ^2    )"
  | "Im7 (inverse x) = - (Im7 x) / (Ree x ^ 2 + Im1 x ^ 2 + Im2 x ^ 2 + Im3 x ^ 2
     +Im4 x ^ 2 + Im5 x ^ 2 + Im6 x ^ 2 + Im7 x ^2    )"


definition "x div y = x  * ( inverse y)" for x y :: octo

instance by standard
 
end

lemma octo_mult_components: 
  "Ree (x *  y ) =  Ree x *  Ree y - Im1 x * Im1 y -  Im2 x * Im2 y - Im3 x * Im3 y
   - Im4 x * Im4 y - Im5 x * Im5 y - Im6 x * Im6 y-  Im7 x * Im7 y"
  "Im1 (x  *  y )  =  Ree x * Im1 y +   Im1 x * Ree y + Im2 x * Im4 y +Im3 x * Im7 y -
     Im4 x * Im2 y    +Im5 x * Im6 y - Im6 x * Im5 y - Im7 x * Im3 y "    
   " Im2 (x  *  y )  =  Ree x *  Im2 y - Im1 x * Im4 y+ Im2 x  * Ree y + Im3 x * Im5 y 
          + Im4 x * Im1 y  - Im5 x * Im3 y + Im6 x * Im7 y - Im7 x *Im6 y  "    
   " Im3 (x * y ) =  Ree x * Im3 y -Im1 x * Im7 y -Im2 x *Im5 y +Im3 x * Ree y + Im4 x * Im6 y
         +  Im5 x *Im2 y  - Im6 x * Im4 y + Im7 x * Im1 y "   
   "Im4  (x *y ) =  Ree x * Im4 y + Im1 x * Im2 y - Im2 x * Im1 y -Im3 x * Im6 y + Im4 x * Ree y 
        +Im5 x * Im7 y +Im6 x * Im3 y -Im7 x * Im5 y  "   
   "Im5  (x * y ) = Ree x * Im5 y - Im1 x * Im6 y +Im2 x * Im3 y -Im3 x * Im2 y -Im4 x * Im7 y
         +Im5 x * Ree y  +Im6 x * Im1 y + Im7 x  * Im4 y  "    
   " Im6  (x *  y) = Ree x * Im6 y + Im1 x * Im5 y - Im2 x * Im7 y +Im3 x * Im4 y - Im4 x * Im3 y
        -Im5 x * Im1 y + Im6 x * Ree y + Im7 x * Im2 y   "    
    "Im7 (x * y)  = Ree x * Im7 y + Im1 x * Im3 y +Im2 x * Im6 y - Im3 x * Im1 y + Im4 x * Im5 y
   -Im5 x * Im4 y - Im6 x * Im2 y +Im7 x * Ree y  "
 unfolding times_octo_def by auto

lemma octo_distrib_left :
  "a * (b + c) = a * b + a * c" for a b c ::octo
  unfolding times_octo_def  plus_octo_def minus_octo_def uminus_octo_def scaleR_octo_def
  by (simp add: octo_eq_iff octo_mult_components algebra_simps) 

lemma octo_distrib_right :
  "(b + c) * a = b * a + c * a" for a b c ::octo
  unfolding times_octo_def  plus_octo_def minus_octo_def uminus_octo_def scaleR_octo_def
  by (simp add: octo_eq_iff octo_mult_components algebra_simps) 

lemma multiplicative_norm_octo: "norm (x * y) = norm x * norm y" for x y ::octo
proof -
  have "norm (x * y) ^ 2 = norm x ^ 2 * norm y ^ 2"
    unfolding norm_octo_squared octo_mult_components by algebra
  also have "... = (norm x * norm y) ^ 2"
    by (simp add: power_mult_distrib)
  finally show ?thesis by simp
qed

lemma mult_1_right_octo [simp]: "x * 1 = (x :: octo)"
 and mult_1_left_octo [simp]: "1 * x = (x :: octo)"
  by (simp_all add: times_octo_def)

instance octo :: power ..

lemma power2_eq_square_octo: "x ^ 2 = (x * x :: octo)"
  by (simp add: numeral_2_eq_2 times_octo_def)

lemma octo_product_alternative_left: "x * (x * y) = (x * x :: octo) * y"
  unfolding octo_eq_iff octo_mult_components by algebra

lemma octo_product_alternative_right: "x * (y * y) = (x * y :: octo) * y"
  unfolding octo_eq_iff octo_mult_components by algebra

lemma octo_product_flexible: "(x * y) * x = x * (y * x :: octo)"
  unfolding octo_eq_iff octo_mult_components by algebra

lemma octo_power_commutes: "x ^ y * x = x * (x ^ y :: octo)"
  by (induction y) (simp_all add: octo_product_flexible)

lemma octo_product_noncommutative: "\<not>(\<forall>x y::octo. (x * y = y * x))"

  using inverse_1 left_inverse mult_not_zero octo.sel(8) octo_e4.sel(2)
  octo_e4.sel(3)   octo_e4.sel(5)  octo_e5.sel(1) octo_e5.sel(2)
  octo_e5.sel(3) octo_e5.sel(5) octo_e5.sel(6) octo_e5.sel(8) times_octo_def
  by smt

lemma octo_product_nonassociative :
  "\<not>(\<forall> x y z::octo. x * (y * z) = (x * y) * z)" 
proof-
  define x where "x = Octo 1 0 0 0 1 0 0 0"
  define y where "y = Octo 1 3 0 0 0 1 0 0"
  define z where "z = Octo 0 1 0 1 1 1 0 0"
  have "x * (y * z) \<noteq> (x * y) * z"
    by (simp add: octo_eq_iff octo_mult_components x_def y_def z_def)
  thus ?thesis by blast
qed

subsection \<open>Embedding of the Reals into the Octonions\<close>

definition octo_of_real :: "real \<Rightarrow>  octo"
  where "octo_of_real r = scaleR r 1"

definition octo_of_nat :: "nat \<Rightarrow>  octo"
  where "octo_of_nat r = scaleR r 1"

definition octo_of_int :: "int \<Rightarrow>  octo"
  where "octo_of_int r = scaleR r 1"

lemma octo_of_nat_sel [simp]:
  "Ree (octo_of_nat x) = of_nat x" "Im1 (octo_of_nat x) = 0" "Im2 (octo_of_nat x) = 0"
  "Im3 (octo_of_nat x) = 0" "Im4 (octo_of_nat x) = 0" "Im5 (octo_of_nat x) = 0"
  "Im6 (octo_of_nat x) = 0" "Im7 (octo_of_nat x) = 0"
  by (simp_all add: octo_of_nat_def)

lemma octo_of_real_sel [simp]:
  "Ree (octo_of_real x) = x" "Im1 (octo_of_real x) = 0" "Im2 (octo_of_real x) = 0"
  "Im3 (octo_of_real x) = 0" "Im4 (octo_of_real x) = 0" "Im5 (octo_of_real x) = 0"
  "Im6 (octo_of_real x) = 0" "Im7 (octo_of_real x) = 0"
  by (simp_all add: octo_of_real_def)

lemma octo_of_int_sel [simp]:
  "Ree (octo_of_int x) = of_int x" "Im1 (octo_of_int x) = 0" "Im2 (octo_of_int x) = 0"
  "Im3 (octo_of_int x) = 0" "Im4 (octo_of_int x) = 0" "Im5 (octo_of_int x) = 0"
  "Im6 (octo_of_int x) = 0" "Im7 (octo_of_int x) = 0"
  by (simp_all add: octo_of_int_def)

lemma scaleR_conv_octo_of_real: "scaleR r x = octo_of_real r * x"
  by (simp add: octo_eq_iff octo_mult_components octo_of_real_def)

lemma octo_of_real_0 [simp]: "octo_of_real 0 = 0"
  by (simp add: octo_of_real_def)

lemma octo_of_real_1 [simp]: "octo_of_real 1 = 1"
  by (simp add: octo_of_real_def)

lemma octo_of_real_add [simp]: "octo_of_real (x + y) = octo_of_real x + octo_of_real y"
  by (simp add: octo_of_real_def scaleR_left_distrib)

lemma octo_of_real_minus [simp]: "octo_of_real (- x) = - octo_of_real x"
  by (simp add: octo_of_real_def)

lemma octo_of_real_diff [simp]: "octo_of_real (x - y) = octo_of_real x - octo_of_real y"
  by (simp add: octo_of_real_def scaleR_left_diff_distrib)

lemma octo_of_real_mult [simp]: "octo_of_real (x * y) = octo_of_real x * octo_of_real y"
  using octo_of_real_def
  by (metis scaleR_conv_octo_of_real scaleR_scaleR)

lemma octo_of_real_sum[simp]: "octo_of_real (sum f s) = (\<Sum>x\<in>s. octo_of_real (f x))"
  by (induct s rule: infinite_finite_induct) auto 

lemma octo_of_real_power [simp]:
  "octo_of_real (x ^ y) = (octo_of_real x :: octo) ^ y"
  by (induct y)(simp_all)

lemma octo_of_real_eq_iff [simp]: "octo_of_real x = octo_of_real y \<longleftrightarrow> x = y"
  using octo_of_real_def
  by (simp add: octo_of_real_def one_octo.code zero_octo.code)

lemmas octo_of_real_eq_0_iff [simp] = octo_of_real_eq_iff [of _ 0, simplified]
lemmas octo_of_real_eq_1_iff [simp] = octo_of_real_eq_iff [of _ 1, simplified]

lemma minus_octo_of_real_eq_octo_of_real_iff [simp]: "-octo_of_real x = octo_of_real y \<longleftrightarrow> -x = y"
  using octo_of_real_eq_iff[of "-x" y] by (simp only: octo_of_real_minus)

lemma octo_of_real_eq_minus_of_real_iff [simp]: "octo_of_real x = -octo_of_real y \<longleftrightarrow> x = -y"
  using octo_of_real_eq_iff[of x "-y"] by (simp only: octo_of_real_minus)

lemma octo_of_real_of_nat_eq [simp]: "octo_of_real (of_nat x) = octo_of_nat x" 
  unfolding octo_of_real_def
  by (simp add: octo_of_nat_def)

lemma octo_of_real_of_int_eq [simp]: "octo_of_real (of_int z) = octo_of_int z"
 unfolding octo_of_real_def
  by (simp add: octo_of_int_def)

lemma octo_of_int_of_nat:  "octo_of_int (of_nat n) = octo_of_nat n"
  by (simp add: octo_eq_iff)

lemma octo_of_nat_add [simp]: "octo_of_nat (a + b) = octo_of_nat a + octo_of_nat b"
  and octo_of_nat_mult [simp]: "octo_of_nat (a * b) = octo_of_nat a * octo_of_nat b"
  and octo_of_nat_diff [simp]: "b \<le> a \<Longrightarrow> octo_of_nat (a - b) = octo_of_nat a - octo_of_nat b"
  and octo_of_nat_0 [simp]: "octo_of_nat 0 = 0"
  and octo_of_nat_1 [simp]: "octo_of_nat 1 = 1"
  and octo_of_nat_Suc_0 [simp]: "octo_of_nat (Suc 0) = 1"
  by (simp_all add: octo_eq_iff octo_mult_components)

lemma octo_of_int_add [simp]: "octo_of_int (a + b) = octo_of_int a + octo_of_int b"
  and octo_of_int_mult [simp]: "octo_of_int (a * b) = octo_of_int a * octo_of_int b"
  and octo_of_int_diff [simp]: "b \<le> a \<Longrightarrow> octo_of_int (a - b) = octo_of_int a - octo_of_int b"
  and octo_of_int_0 [simp]: "octo_of_int 0 = 0"
  and octo_of_int_1 [simp]: "octo_of_int 1 = 1"
  by (simp_all add: octo_eq_iff octo_mult_components)

instance octo :: numeral ..

lemma numeral_octo_conv_of_nat: "numeral x = octo_of_nat (numeral x)"
proof (induction x)
  case(Bit0 x) 
  have "numeral x+ numeral x = octo_of_nat(numeral x+ numeral x)"
    unfolding Bit0.IH octo_of_nat_add ..
  thus ?case by (simp add: numeral_Bit0)
next 
 case(Bit1 x) 
  have "numeral x+ numeral x + numeral num.One=
octo_of_nat (numeral x + numeral x + numeral num.One)"
    unfolding Bit1.IH octo_of_nat_add by simp
  thus ?case by (simp add: numeral_Bit1)
qed auto

lemma numeral_octo_sel [simp]:
  "Ree (numeral n) = numeral n" "Im1 (numeral n) = 0" "Im2 (numeral n) = 0"
  "Im3 (numeral n) = 0" "Im4 (numeral n) = 0" "Im5 (numeral n) = 0"
  "Im6 (numeral n) = 0" "Im7 (numeral n) = 0"
  by (simp_all add: numeral_octo_conv_of_nat)

lemma octo_of_real_numeral [simp]: "octo_of_real (numeral w) = numeral w"
  by (simp add: numeral_octo_conv_of_nat octo_of_real_def octo_of_nat_def)

lemma octo_of_real_neg_numeral [simp]: "octo_of_real (- numeral w) = - numeral w"
  by simp

lemma octo_of_real_times_commute: "octo_of_real r * q = q * octo_of_real r"
  using octo_of_real_def times_octo_def by simp

lemma octo_of_real_times_conv_scaleR: "octo_of_real x * y = scaleR x y"
  by (simp add: octo_eq_iff octo_mult_components)

lemma octo_mult_scaleR_left: "(r *\<^sub>R x) * y = r *\<^sub>R (x * y :: octo)"
  by (simp add: octo_eq_iff octo_mult_components algebra_simps)

lemma octo_mult_scaleR_right: "x * (r *\<^sub>R y) = r *\<^sub>R (x * y :: octo)"
  by (simp add: octo_eq_iff octo_mult_components algebra_simps)

lemma scaleR_octo_of_real [simp]: "scaleR r (octo_of_real s) = octo_of_real (r * s)"
  by (simp add: octo_of_real_def)

lemma octo_of_real_times_left_commute: "octo_of_real r * (x * q) = x * (octo_of_real r * q)"
  unfolding octo_of_real_times_conv_scaleR by (simp add: octo_mult_scaleR_right)

lemma nonzero_octo_of_real_inverse:
  "x \<noteq> 0 \<Longrightarrow> octo_of_real (inverse x) = inverse (octo_of_real x :: octo)"
  by (simp add: octo_eq_iff power2_eq_square divide_simps)

lemma octo_of_real_inverse [simp]:
  "octo_of_real (inverse x) = inverse (octo_of_real x )"
  by (simp add: octo_eq_iff power2_eq_square divide_simps)

lemma nonzero_octo_of_real_divide:
  "y \<noteq> 0 \<Longrightarrow> octo_of_real (x / y) = (octo_of_real x / octo_of_real y ::octo)"
   by (simp add: divide_inverse divide_octo_def)

lemma octo_of_real_divide [simp]:
  "octo_of_real (x / y) = (octo_of_real x / octo_of_real y :: octo)"
  using divide_inverse divide_octo_def octo_of_real_def octo_of_real_inverse
  by (metis octo_of_real_mult)

lemma octo_of_real_inverse_collapse [simp]:
  assumes "c \<noteq> 0"
  shows   "octo_of_real c * octo_of_real (inverse c) = 1"
          "octo_of_real (inverse c) * octo_of_real c = 1"
  using assms by (simp_all add: octo_eq_iff octo_mult_components power2_eq_square)

lemma octo_divide_numeral:
  fixes x::octo shows "x / numeral y = x /\<^sub>R numeral y"
  using octo_of_real_times_commute[of "inverse (numeral y)"]
  by (simp add: scaleR_conv_octo_of_real divide_octo_def flip: octo_of_real_numeral)

lemma octo_divide_numeral_sel [simp]:
  "Ree (x / numeral w) = Ree x / numeral w"
  "Im1 (x / numeral w) = Im1 x / numeral w"
  "Im2 (x / numeral w) = Im2 x / numeral w"
  "Im3 (x / numeral w) = Im3 x / numeral w"
  "Im4 (x / numeral w) = Im4 x / numeral w"
  "Im5 (x / numeral w) = Im5 x / numeral w"
  "Im6 (x / numeral w) = Im6 x / numeral w"
  "Im7 (x / numeral w) = Im7 x / numeral w"
  unfolding octo_divide_numeral by simp_all

lemma octo_norm_units [simp]:
  "norm octo_e1 = 1" "norm (e2::octo) = 1" "norm (e3::octo) = 1"
  "norm (e4::octo) = 1 "  "norm (e5::octo) = 1"   "norm (e6::octo) = 1" "norm (e7::octo) = 1" 
  by (auto simp: norm_octo_def)

lemma e1_nz [simp]: "e1 \<noteq> 0"
  and e2_nz [simp]: "e2 \<noteq> 0"
  and e3_nz [simp]: "e3 \<noteq> 0"
  and e4_nz [simp]: "e4 \<noteq> 0"
  and e5_nz [simp]: "e5 \<noteq> 0"
  and e6_nz [simp]: "e6 \<noteq> 0"
  and e7_nz [simp]: "e7 \<noteq> 0"
  by (simp_all add: octo_eq_iff)

subsection \<open>"Expansion" into the traditional notation\<close>

lemma octo_unfold:
   "q = (Ree q) *\<^sub>R e0 + (Im1 q) *\<^sub>R e1 + (Im2 q) *\<^sub>R e2 + (Im3 q) *\<^sub>R e3
      + (Im4 q) *\<^sub>R e4 + (Im5 q) *\<^sub>R e5 + (Im6 q) *\<^sub>R e6 + (Im7 q) *\<^sub>R  e7"
  by (simp add: octo_eq_iff)

lemma octo_trad: "Octo x y z w u v q g =
     x *\<^sub>R e0 + y *\<^sub>R e1 +  z *\<^sub>R e2  +  w *\<^sub>R e3  +  u *\<^sub>R e4 +  v *\<^sub>R e5 +  q *\<^sub>R e6  +  g*\<^sub>R e7 "
  by (simp add: octo_eq_iff)

lemma octo_of_real_eq_Octo: "octo_of_real a = Octo a 0 0 0 0 0 0 0 "
  by (simp add: octo_eq_iff)

lemma e1_squared [simp]: "e1 ^ 2 = -1"
  and e2_squared [simp]: "e2 ^ 2 = -1"
  and e3_squared [simp]: "e3 ^ 2 = -1"
  and e4_squared [simp]: "e4 ^ 2 = -1"
  and e5_squared [simp]: "e5 ^ 2 = -1"
  and e6_squared [simp]: "e6 ^ 2 = -1"
  and e7_squared [simp]: "e7 ^ 2 = -1"
  by (simp_all add: octo_eq_iff power2_eq_square_octo octo_mult_components)

lemma inverse_e1 [simp]: "inverse e1 = -e1"
  and inverse_e2 [simp]: "inverse e2 = -e2"
  and inverse_e3 [simp]: "inverse e3 = -e3"
  and inverse_e4 [simp]: "inverse e4 = -e4"
  and inverse_e5 [simp]: "inverse e5 = -e5"
  and inverse_e6 [simp]: "inverse e6 = -e6"
  and inverse_e7 [simp]: "inverse e7 = -e7"
  by (simp_all add: octo_eq_iff)

subsection \<open>Conjugate of an octonion and related properties.\<close>

primcorec cnj :: "octo \<Rightarrow> octo"
  where
    "Ree (cnj z) = Ree z"
  | "Im1 (cnj z) = - Im1 z"
  | "Im2 (cnj z) = - Im2 z"
  | "Im3 (cnj z) = - Im3 z"
  | "Im4 (cnj z) = - Im4 z"
  | "Im5 (cnj z) = - Im5 z"
  | "Im6 (cnj z) = - Im6 z"
  | "Im7 (cnj z) = - Im7 z"

lemma cnj_cancel_iff [simp]: "cnj x = cnj y \<longleftrightarrow> x = y"

proof
  show "cnj x = cnj y \<Longrightarrow> x = y"
    by (simp add: octo_eq_iff)
qed auto

lemma cnj_cnj [simp]:
   "cnj(cnj q) = q"
 by (simp add: octo_eq_iff)

lemma cnj_of_real [simp]: "cnj(octo_of_real x) = octo_of_real x"
  using  octo_eq_iff
  by (simp add: octo_of_real_eq_Octo)

lemma cnj_zero [simp]: "cnj 0 = 0"
  by (simp add: octo_eq_iff)

lemma cnj_zero_iff [iff]: "cnj z = 0 \<longleftrightarrow> z = 0"
 using cnj_cnj   by (metis cnj_zero)

lemma cnj_one [simp]: "cnj 1 = 1"
  by (simp add: octo_eq_iff)

lemma cnj_one_iff [simp]: "cnj z = 1 \<longleftrightarrow> z = 1"
  by (simp add: octo_eq_iff)

lemma octo_norm_cnj [simp]: "norm(cnj q) = norm q"
  by (simp add: norm_octo_def)

lemma cnj_add [simp]: "cnj (x + y) = cnj x + cnj y"
  using  octo_eq_iff inner_real_def of_real_0 of_real_inner_1  by simp

lemma cnj_sum [simp]: "cnj (sum f S) = (\<Sum>x\<in>S. cnj (f x))"
  by (induct S rule: infinite_finite_induct) auto

lemma cnj_diff [simp]: "cnj (x - y) = cnj x - cnj y"
  using  octo_eq_iff
  by (metis add.commute add_left_cancel cnj_add diff_add_cancel)

lemma cnj_minus [simp]: "cnj (- x) = - cnj x"
  using  octo_eq_iff  cnj_cnj by auto

lemma cnj_inverse [simp]: "cnj (inverse x) = inverse (cnj x)" for x y ::octo
  using  octo_eq_iff inner_real_def real_inner_1_right  by auto

lemma cnj_mult [simp]: "cnj (x * y) = cnj y * cnj x" for x y ::octo
  using octo_eq_iff  times_octo_def octo_mult_components cnj_cnj
 mult_not_zero nonzero_inverse_mult_distrib  by simp

lemma cnj_divide [simp]: "cnj (x / y) = (inverse (cnj y) ) *  cnj x"
  for x y ::octo
  unfolding  divide_octo_def times_octo_def
  using cnj_inverse cnj_mult octo_mult_components  by (metis times_octo_def)

lemma cnj_power [simp]: "cnj (x ^ y) = (cnj x) ^ y"  for x::octo
  by (induction y) (simp_all add: octo_power_commutes)

lemma cnj_of_nat [simp]: "cnj (octo_of_nat x) = octo_of_nat( x)" 
   using cnj_of_real octo_of_real_of_nat_eq by metis 

lemma cnj_of_int [simp]: "cnj (octo_of_int x) = octo_of_nat( x)"
   using  octo_of_real_def  octo_of_real_of_int_eq  octo_of_int_def octo_of_nat_def
   cnj_of_real by auto

lemma cnj_numeral [simp]: "cnj (numeral x) = numeral x" 
   by (simp add: numeral_octo_conv_of_nat)

lemma cnj_neg_numeral [simp]: "cnj (- numeral x) = - numeral x"
   by (simp add: numeral_octo_conv_of_nat)

lemma cnj_scaleR [simp]: "cnj (scaleR r x) = scaleR r (cnj x)"
   using octo_eq_iff inner_real_def ln_one of_real_inner_1 by simp

lemma cnj_units [simp]: "cnj e1 = -e1" "cnj e2 = -e2" "cnj e3 = -e3"
 "cnj e4 = -e4"   "cnj e5 = -e5"   "cnj e6 = -e6"  "cnj e7 = -e7"
  by (simp_all add: octo_eq_iff)

lemma cnj_eq_of_real: "cnj q = octo_of_real x \<longleftrightarrow> q = octo_of_real x"
proof
  show "cnj q = octo_of_real x \<Longrightarrow> q = octo_of_real x"
    by (metis cnj_of_real cnj_cnj)
qed auto

lemma octo_trad_cnj : "cnj q = (Ree q) *\<^sub>R e0 - (Im1 q) *\<^sub>R e1 - (Im2 q)*\<^sub>R e2  - (Im3 q) *\<^sub>R e3  - 
 (Im4 q) *\<^sub>R e4 -  (Im5 q) *\<^sub>R e5 -  (Im6 q) *\<^sub>R e6  -  (Im7 q)*\<^sub>R e7 " for q::octo
  using cnj_cnj octo_unfold octo_trad cnj_def Octonions.cnj.code by auto

lemma octonion_conjugate_property:
  "cnj x = -(1/6) *\<^sub>R (x + (e1 * x) *  e1  +  (e2 * x) * e2 +  (e3 * x) * e3 +
     (e4 * x) * e4 + (e5 * x) * e5 +  ( e6 * x) * e6 + (e7 * x) * e7)"
  by (simp add: octo_eq_iff octo_mult_components)

lemma octo_add_cnj: "q + cnj q = 2 *\<^sub>R (Ree q) *\<^sub>R e0" "cnj q + q = (2*\<^sub>R (Ree q)*\<^sub>R e0)"
  by (simp_all add: octo_eq_iff)

lemma octo_add_cnj1: "q + cnj q = octo_of_real (2*\<^sub>R (Ree q))" 
                     "cnj q + q = octo_of_real (2*\<^sub>R (Ree q))"
  by (auto simp: octo_eq_iff octo_mult_components)

lemma octo_subtract_cnj:
  "q - cnj q = 2 *\<^sub>R (Im1 q *\<^sub>R e1 + Im2 q *\<^sub>R e2 + Im3 q *\<^sub>R e3 + 
                     Im4 q *\<^sub>R e4 + Im5 q *\<^sub>R e5 + Im6 q*\<^sub>R e6 + Im7 q *\<^sub>R e7)"
  by (simp add: octo_eq_iff)

lemma octo_mult_cnj_commute: "cnj x * x = x * cnj x"
  using times_octo_def by auto

lemma octo_cnj_mult_conv_norm: "cnj x * x = octo_of_real (norm x) ^ 2"
  by (simp add: octo_eq_iff octo_mult_components norm_octo_def power2_eq_square
           flip: octo_of_real_power)

lemma octo_mult_cnj_conv_norm: "x * cnj x = octo_of_real (norm x) ^ 2"
  by (simp add: octo_eq_iff octo_mult_components norm_octo_def power2_eq_square 
           flip: octo_of_real_power)

lemma octo_mult_cnj_conv_norm_aux: "octo_of_real (norm x ^ 2) = x * cnj x " 
  using octo_mult_cnj_conv_norm[of x] by (simp add: octo_mult_cnj_commute)

lemma octo_norm_conj: "octo_of_real ( inner x y) = (1/2) *\<^sub>R (x * (cnj y) + y * (cnj x))"
  by (simp add: octo_eq_iff octo_mult_components inner_octo_def)

lemma octo_inverse_cnj: "inverse x = cnj x /\<^sub>R (norm x ^ 2)"
  by (auto simp: octo_eq_iff norm_octo_def field_simps)

lemma inverse_octo_1: "x \<noteq> 0 \<Longrightarrow> x * inverse x = (1 :: octo)"
  by (simp add: octo_mult_scaleR_right octo_mult_cnj_conv_norm_aux [symmetric] 
                divide_simps octo_inverse_cnj
           del: octo_of_real_power)

lemma inverse_octo_1_sym: "x \<noteq> 0 \<Longrightarrow> inverse x * x = (1 :: octo)"
  by (metis cnj_cnj cnj_inverse cnj_mult cnj_one cnj_zero inverse_octo_1)

lemma inverse_0_octo [simp]: "inverse 0 = (0 :: octo)"
  by (simp add: octo_eq_iff)

lemma inverse_octo_commutes: "inverse x * x = x * (inverse x :: octo)"
  by (cases "x = 0") (simp_all add: inverse_octo_1 inverse_octo_1_sym)

lemma octo_inverse_mult: "inverse (x * y) = inverse y * inverse x" for x y::octo
proof-
  have "inverse (x * y) = (cnj y * cnj x) /\<^sub>R (norm (x * y) ^ 2)"
     by (simp add: octo_inverse_cnj)
   also have "\<dots> = (cnj y /\<^sub>R norm y ^ 2) * (cnj x /\<^sub>R norm x ^ 2)"
     by (simp add: octo_mult_scaleR_left octo_mult_scaleR_right multiplicative_norm_octo
                   power2_eq_square)
   also have "\<dots> = inverse y * inverse x"
     by (simp add: octo_inverse_cnj)
   finally show ?thesis .
qed

lemma octo_inverse_eq_cnj: "norm q = 1 \<Longrightarrow> inverse q = cnj q" for q::octo
  by (simp add: octo_inverse_cnj)

lemma octo_in_Reals_if_Re: fixes q ::real shows " Ree( octo_of_real(q)) = q"
  by simp

lemma octo_in_Reals_if_Re_con: assumes "Ree (octo_of_real q) = q"
  shows "q \<in> Reals"
  by (metis Reals_of_real inner_real_def mult.right_neutral of_real_inner_1)

lemma octo_in_Reals_if_cnj: fixes q:: real shows " cnj( octo_of_real( q)) = octo_of_real q"
  by simp

lemma octo_in_Reals_if_cnj_con: assumes " cnj( octo_of_real( q)) = octo_of_real q" 
  shows "q \<in> Reals "
   by (metis Reals_of_real inner_real_def mult.right_neutral of_real_inner_1)

lemma norm_power2: "norm q ^ 2 = Ree (cnj q * q)"
  by (simp add: octo_mult_components norm_octo_def power2_eq_square)

lemma norm_power2_cnj: "norm q ^ 2 = Ree (q * cnj q)"
  by (simp add: octo_mult_components norm_octo_def power2_eq_square)

lemma octo_norm_imaginary: "Ree x = 0 \<Longrightarrow> x * x = -(octo_of_real (norm x))\<^sup>2"
  by (simp add: octo_eq_iff octo_mult_components norm_octo_def power2_eq_square
           flip: octo_of_real_power octo_of_real_mult)

subsection\<open> Linearity and continuity of the components.\<close>

lemma bounded_linear_Ree: "bounded_linear Ree"
  and bounded_linear_Im1: "bounded_linear Im1"
  and bounded_linear_Im2: "bounded_linear Im2"
  and bounded_linear_Im3: "bounded_linear Im3"
  and bounded_linear_Im4: "bounded_linear Im4"
  and bounded_linear_Im5: "bounded_linear Im5"
  and bounded_linear_Im6: "bounded_linear Im6"
  and bounded_linear_Im7: "bounded_linear Im7"
  by (simp_all add: bounded_linear_intro [where K=1] norm_octo_def real_le_rsqrt add.assoc)

lemmas Cauchy_Ree = bounded_linear.Cauchy [OF bounded_linear_Ree]
lemmas Cauchy_Im1 = bounded_linear.Cauchy [OF bounded_linear_Im1]
lemmas Cauchy_Im2 = bounded_linear.Cauchy [OF bounded_linear_Im2]
lemmas Cauchy_Im3 = bounded_linear.Cauchy [OF bounded_linear_Im3]
lemmas Cauchy_Im4 = bounded_linear.Cauchy [OF bounded_linear_Im4]
lemmas Cauchy_Im5 = bounded_linear.Cauchy [OF bounded_linear_Im5]
lemmas Cauchy_Im6 = bounded_linear.Cauchy [OF bounded_linear_Im6]
lemmas Cauchy_Im7 = bounded_linear.Cauchy [OF bounded_linear_Im7]

lemmas tendsto_Re [tendsto_intros] = bounded_linear.tendsto [OF bounded_linear_Ree]
lemmas tendsto_Im1 [tendsto_intros] = bounded_linear.tendsto [OF bounded_linear_Im1]
lemmas tendsto_Im2 [tendsto_intros] = bounded_linear.tendsto [OF bounded_linear_Im2]
lemmas tendsto_Im3 [tendsto_intros] = bounded_linear.tendsto [OF bounded_linear_Im3]
lemmas tendsto_Im4 [tendsto_intros] = bounded_linear.tendsto [OF bounded_linear_Im4]
lemmas tendsto_Im5 [tendsto_intros] = bounded_linear.tendsto [OF bounded_linear_Im5]
lemmas tendsto_Im6 [tendsto_intros] = bounded_linear.tendsto [OF bounded_linear_Im6]
lemmas tendsto_Im7 [tendsto_intros] = bounded_linear.tendsto [OF bounded_linear_Im7]

lemmas isCont_Ree [simp] = bounded_linear.isCont [OF bounded_linear_Ree]
lemmas isCont_Im1 [simp] = bounded_linear.isCont [OF bounded_linear_Im1]
lemmas isCont_Im2 [simp] = bounded_linear.isCont [OF bounded_linear_Im2]
lemmas isCont_Im3 [simp] = bounded_linear.isCont [OF bounded_linear_Im3]
lemmas isCont_Im4 [simp] = bounded_linear.isCont [OF bounded_linear_Im4]
lemmas isCont_Im5 [simp] = bounded_linear.isCont [OF bounded_linear_Im5]
lemmas isCont_Im6 [simp] = bounded_linear.isCont [OF bounded_linear_Im6]
lemmas isCont_Im7 [simp] = bounded_linear.isCont [OF bounded_linear_Im7]

lemmas continuous_Ree [simp] = bounded_linear.continuous [OF bounded_linear_Ree]
lemmas continuous_Im1 [simp] = bounded_linear.continuous [OF bounded_linear_Im1]
lemmas continuous_Im2 [simp] = bounded_linear.continuous [OF bounded_linear_Im2]
lemmas continuous_Im3 [simp] = bounded_linear.continuous [OF bounded_linear_Im3]
lemmas continuous_Im4 [simp] = bounded_linear.continuous [OF bounded_linear_Im4]
lemmas continuous_Im5 [simp] = bounded_linear.continuous [OF bounded_linear_Im5]
lemmas continuous_Im6 [simp] = bounded_linear.continuous [OF bounded_linear_Im6]
lemmas continuous_Im7 [simp] = bounded_linear.continuous [OF bounded_linear_Im7]

lemmas continuous_on_Ree [continuous_intros] = bounded_linear.continuous_on[OF bounded_linear_Ree]
lemmas continuous_on_Im1 [continuous_intros] = bounded_linear.continuous_on[OF bounded_linear_Im1]
lemmas continuous_on_Im2 [continuous_intros] = bounded_linear.continuous_on[OF bounded_linear_Im2]
lemmas continuous_on_Im3 [continuous_intros] = bounded_linear.continuous_on[OF bounded_linear_Im3]
lemmas continuous_on_Im4 [continuous_intros] = bounded_linear.continuous_on[OF bounded_linear_Im4]
lemmas continuous_on_Im5 [continuous_intros] = bounded_linear.continuous_on[OF bounded_linear_Im5]
lemmas continuous_on_Im6 [continuous_intros] = bounded_linear.continuous_on[OF bounded_linear_Im6]
lemmas continuous_on_Im7 [continuous_intros] = bounded_linear.continuous_on[OF bounded_linear_Im7]

lemmas has_derivative_Ree [derivative_intros] = bounded_linear.has_derivative[OF bounded_linear_Ree]
lemmas has_derivative_Im1 [derivative_intros] = bounded_linear.has_derivative[OF bounded_linear_Im1]
lemmas has_derivative_Im2 [derivative_intros] = bounded_linear.has_derivative[OF bounded_linear_Im2]
lemmas has_derivative_Im3 [derivative_intros] = bounded_linear.has_derivative[OF bounded_linear_Im3]
lemmas has_derivative_Im4 [derivative_intros] = bounded_linear.has_derivative[OF bounded_linear_Im4]
lemmas has_derivative_Im5 [derivative_intros] = bounded_linear.has_derivative[OF bounded_linear_Im5]
lemmas has_derivative_Im6 [derivative_intros] = bounded_linear.has_derivative[OF bounded_linear_Im6]
lemmas has_derivative_Im7 [derivative_intros] = bounded_linear.has_derivative[OF bounded_linear_Im7]

lemmas sums_Ree = bounded_linear.sums [OF bounded_linear_Ree]
lemmas sums_Im1 = bounded_linear.sums [OF bounded_linear_Im1]
lemmas sums_Im2 = bounded_linear.sums [OF bounded_linear_Im2]
lemmas sums_Im3 = bounded_linear.sums [OF bounded_linear_Im3]
lemmas sums_Im4 = bounded_linear.sums [OF bounded_linear_Im4]
lemmas sums_Im5 = bounded_linear.sums [OF bounded_linear_Im5]
lemmas sums_Im6 = bounded_linear.sums [OF bounded_linear_Im6]
lemmas sums_Im7 = bounded_linear.sums [OF bounded_linear_Im7]

subsubsection\<open> Octonionic-specific theorems about sums.                                \<close>

lemma Ree_sum [simp]: "Ree (sum f S) = sum (\<lambda>x.  Ree(f x)) S"
  and Im1_sum [simp]: "Im1 (sum f S) = sum (\<lambda>x. Im1 (f x)) S"
  and Im2_sum [simp]: "Im2 (sum f S) = sum (\<lambda>x. Im2 (f x)) S"
  and Im3_sum [simp]: "Im3 (sum f S) = sum (\<lambda>x. Im3 (f x)) S"
  and Im4_sum [simp]: "Im4 (sum f S) = sum (\<lambda>x. Im4 (f x)) S"
  and Im5_sum [simp]: "Im5 (sum f S) = sum (\<lambda>x. Im5 (f x)) S"
  and Im6_sum [simp]: "Im6 (sum f S) = sum (\<lambda>x. Im6 (f x)) S"
  and Im7_sum [simp]: "Im7 (sum f S) = sum (\<lambda>x. Im7 (f x)) S"
  by (induct S rule: infinite_finite_induct; simp)+

subsubsection\<open> Bound results for real and imaginary components of limits.                \<close>

lemma Ree_tendsto_upperbound:
   "\<lbrakk>(f \<longlongrightarrow> limit) net; \<forall>\<^sub>F x in net. octo.Ree (f x) \<le> b; net \<noteq> bot\<rbrakk> \<Longrightarrow> Ree limit \<le> b"
  by (blast intro: tendsto_upperbound [OF tendsto_Re])

lemma Im1_tendsto_upperbound:
   "\<lbrakk>(f \<longlongrightarrow> limit) net; \<forall>\<^sub>F x in net. Im1 (f x) \<le> b; net \<noteq> bot\<rbrakk> \<Longrightarrow> Im1 limit \<le> b"
  by (blast intro: tendsto_upperbound [OF tendsto_Im1])

lemma Im2_tendsto_upperbound:
   "\<lbrakk>(f \<longlongrightarrow> limit) net; \<forall>\<^sub>F x in net. Im2 (f x) \<le> b; net \<noteq> bot\<rbrakk> \<Longrightarrow> Im2 limit \<le> b"
  by (blast intro: tendsto_upperbound [OF tendsto_Im2])

lemma Im3_tendsto_upperbound:
   "\<lbrakk>(f \<longlongrightarrow> limit) net; \<forall>\<^sub>F x in net. Im3 (f x) \<le> b; net \<noteq> bot\<rbrakk> \<Longrightarrow> Im3 limit \<le> b"
  by (blast intro: tendsto_upperbound [OF tendsto_Im3])

lemma Im4_tendsto_upperbound:
   "\<lbrakk>(f \<longlongrightarrow> limit) net; \<forall>\<^sub>F x in net. Im4 (f x) \<le> b; net \<noteq> bot\<rbrakk> \<Longrightarrow> Im4 limit \<le> b"
  by (blast intro: tendsto_upperbound [OF tendsto_Im4])

lemma Im5_tendsto_upperbound:
   "\<lbrakk>(f \<longlongrightarrow> limit) net; \<forall>\<^sub>F x in net. Im5 (f x) \<le> b; net \<noteq> bot\<rbrakk> \<Longrightarrow> Im5 limit \<le> b"
  by (blast intro: tendsto_upperbound [OF tendsto_Im5])

lemma Im6_tendsto_upperbound:
   "\<lbrakk>(f \<longlongrightarrow> limit) net; \<forall>\<^sub>F x in net. Im6 (f x) \<le> b; net \<noteq> bot\<rbrakk> \<Longrightarrow> Im6 limit \<le> b"
  by (blast intro: tendsto_upperbound [OF tendsto_Im6])

lemma Im7_tendsto_upperbound:
   "\<lbrakk>(f \<longlongrightarrow> limit) net; \<forall>\<^sub>F x in net. Im7 (f x) \<le> b; net \<noteq> bot\<rbrakk> \<Longrightarrow> Im7 limit \<le> b"
  by (blast intro: tendsto_upperbound [OF tendsto_Im7])

lemma Ree_tendsto_lowerbound:
   "\<lbrakk>(f \<longlongrightarrow> limit) net; \<forall>\<^sub>F x in net. b \<le> octo.Ree (f x); net \<noteq> bot\<rbrakk> \<Longrightarrow> b \<le> Ree limit"
  by (blast intro: tendsto_lowerbound [OF tendsto_Re])

lemma Im1_tendsto_lowerbound:
   "\<lbrakk>(f \<longlongrightarrow> limit) net; \<forall>\<^sub>F x in net. b \<le> Im1 (f x); net \<noteq> bot\<rbrakk> \<Longrightarrow> b \<le> Im1 limit"
  by (blast intro: tendsto_lowerbound [OF tendsto_Im1])

lemma Im2_tendsto_lowerbound:
   "\<lbrakk>(f \<longlongrightarrow> limit) net; \<forall>\<^sub>F x in net. b \<le> Im2 (f x); net \<noteq> bot\<rbrakk> \<Longrightarrow> b \<le> Im2 limit"
  by (blast intro: tendsto_lowerbound [OF tendsto_Im2])

lemma Im3_tendsto_lowerbound:
   "\<lbrakk>(f \<longlongrightarrow> limit) net; \<forall>\<^sub>F x in net. b \<le> Im3 (f x); net \<noteq> bot\<rbrakk> \<Longrightarrow> b \<le> Im3 limit"
  by (blast intro: tendsto_lowerbound [OF tendsto_Im3])

lemma Im4_tendsto_lowerbound:
   "\<lbrakk>(f \<longlongrightarrow> limit) net; \<forall>\<^sub>F x in net. b \<le> Im4 (f x); net \<noteq> bot\<rbrakk> \<Longrightarrow> b \<le> Im4 limit"
  by (blast intro: tendsto_lowerbound [OF tendsto_Im4])

lemma Im5_tendsto_lowerbound:
   "\<lbrakk>(f \<longlongrightarrow> limit) net; \<forall>\<^sub>F x in net. b \<le> Im5 (f x); net \<noteq> bot\<rbrakk> \<Longrightarrow> b \<le> Im5 limit"
  by (blast intro: tendsto_lowerbound [OF tendsto_Im5])

lemma Im6_tendsto_lowerbound:
   "\<lbrakk>(f \<longlongrightarrow> limit) net; \<forall>\<^sub>F x in net. b \<le> Im6 (f x); net \<noteq> bot\<rbrakk> \<Longrightarrow> b \<le> Im6 limit"
  by (blast intro: tendsto_lowerbound [OF tendsto_Im6])

lemma Im7_tendsto_lowerbound:
   "\<lbrakk>(f \<longlongrightarrow> limit) net; \<forall>\<^sub>F x in net. b \<le> Im7 (f x); net \<noteq> bot\<rbrakk> \<Longrightarrow> b \<le> Im7 limit"
  by (blast intro: tendsto_lowerbound [OF tendsto_Im7])

lemma octo_of_real_continuous [continuous_intros]:
  "continuous net f \<Longrightarrow> continuous net (\<lambda>x. octo_of_real (f x))"
  by (auto simp: octo_of_real_def intro: continuous_intros)

lemma octo_of_real_continuous_on [continuous_intros]:
  "continuous_on S f \<Longrightarrow> continuous_on S (\<lambda>x. octo_of_real (f x))"
  by (auto simp: octo_of_real_def intro: continuous_intros)

lemma of_real_continuous_iff: "continuous net (\<lambda>x. octo_of_real (f x)) \<longleftrightarrow> continuous net f"
proof safe
  assume "continuous net (\<lambda>x. octo_of_real (f x))"
  hence "continuous net (\<lambda>x. Ree (octo_of_real (f x)))"
    by (rule continuous_Ree)
  thus "continuous net f" by simp
qed (auto intro: continuous_intros)

lemma of_real_continuous_on_iff:
   "continuous_on S (\<lambda>x. octo_of_real(f x)) \<longleftrightarrow> continuous_on S f"
proof safe
  assume "continuous_on S (\<lambda>x. octo_of_real (f x))"
  hence "continuous_on S (\<lambda>x. Ree (octo_of_real (f x)))"
    by (rule continuous_on_Ree)
  thus "continuous_on S f" by simp
qed (auto intro: continuous_intros)

subsection\<open>Octonions for describing 7D isometries\<close>

subsubsection\<open>The \<open>HIm\<close> operator\<close>

definition HIm :: "octo \<Rightarrow> real^7" where
  "HIm q \<equiv> vector[Im1 q, Im2 q, Im3 q, Im4 q, Im5 q, Im6 q, Im7 q]"

lemma HIm_Octo: "HIm (Octo w x y z u v q g) = vector[x,y,z, u, v, q, g]"
  by (simp add: HIm_def)

lemma him_eq: "HIm a = HIm b \<longleftrightarrow> Im1 a = Im1 b \<and> Im2 a = Im2 b \<and> Im3 a = Im3 b
 \<and> Im4 a = Im4 b \<and> Im5 a = Im5 b \<and> Im6 a = Im6 b \<and> Im7 a = Im7 b"

  by (metis HIm_def vector_7)

lemma him_of_real [simp]: "HIm(octo_of_real a) = 0" 
 by (simp add:octo_of_real_eq_Octo HIm_Octo vec_eq_iff vector_def)

lemma him_0 [simp]: "HIm 0 = 0"
 by (metis him_of_real octo_of_real_0)

lemma him_1 [simp]: "HIm 1 = 0"
 using HIm_def him_0 by auto

lemma him_cnj: "HIm(cnj q) = - HIm q"
  by (simp add: HIm_def vec_eq_iff vector_def)

lemma him_mult_left [simp]: "HIm (a *\<^sub>R q) = a  *\<^sub>R HIm q"
  by (simp add: HIm_def vec_eq_iff vector_def)

lemma him_mult_right [simp]: "HIm (q * octo_of_real a) = HIm q * of_real a"
 by (metis Octonions.scaleR_conv_octo_of_real Real_Vector_Spaces.scaleR_conv_of_real
 him_mult_left octo_of_real_times_commute semiring_normalization_rules(7))

lemma him_add [simp]: "HIm (x + y) = HIm x + HIm y"
 and  him_minus [simp]: "HIm (-x) = - HIm x"
 and  him_diff [simp]: "HIm (x - y) = HIm x - HIm y"
  by (simp_all add: HIm_def vec_eq_iff vector_def)

lemma him_sum [simp]: "HIm (sum f S) = (\<Sum>x\<in>S. HIm (f x))"
  by (induct S rule: infinite_finite_induct) auto

lemma linear_him: "linear HIm"
  by (simp add: linearI)

subsubsection\<open>The \<open>Hv\<close> operator\<close>

definition Hv :: "real^7 \<Rightarrow> octo" where
  "Hv v \<equiv> Octo 0 (v$1) (v$2) (v$3) (v$4) (v$5) (v$6) (v$7)  "

lemma Hv_sel [simp]:
  "Ree (Hv v) = 0" "Im1 (Hv v) = v $ 1" "Im2 (Hv v) = v $ 2" "Im3 (Hv v) = v $ 3"
  "Im4 (Hv v) = v $ 4" "Im5 (Hv v) = v $ 5" "Im6 (Hv v) = v $ 6" "Im7 (Hv v) = v $ 7"
  by (simp_all add: Hv_def)

lemma hv_vec: "Hv(vec r) = Octo 0 r r r r r r r "
  by (simp add: Hv_def)

lemma hv_eq_zero [simp]: "Hv v = 0 \<longleftrightarrow> v = 0"
  by (simp add: octo_eq_iff vec_eq_iff) (metis exhaust_7)

lemma hv_zero [simp]: "Hv 0 = 0"
  by simp

lemma hv_vector [simp]: "Hv(vector[x,y,z,u,v,q,g]) = Octo 0 x y z u v q g"
  by (simp add: Hv_def)

lemma hv_basis:
  "Hv(axis 1 1) = e1" "Hv(axis 2 1) = e2" "Hv(axis 3 1) = e3"
  "Hv(axis 4 1) = e4" "Hv(axis 5 1) = e5" "Hv(axis 6 1) = e6"  "Hv(axis 7 1) = e7"
  by (simp_all add: octo_eq_iff)

lemma hv_add [simp]: "Hv(x + y) = Hv x + Hv y"
  by (simp add: Hv_def octo_eq_iff)

lemma hv_minus [simp]: "Hv(-x) = -Hv x"
  by (simp add: Hv_def octo_eq_iff)

lemma hv_diff [simp]: "Hv(x - y) = Hv x - Hv y"
  by (simp add: Hv_def octo_eq_iff)

lemma hv_cmult [simp]:
 "Hv(scaleR a   x) = scaleR a  ( Hv x)" 
  by (simp add: Hv_def octo_eq_iff)

lemma hv_sum [simp]: "Hv (sum f S) = (\<Sum>x\<in>S. Hv (f x))"
  by (induct S rule: infinite_finite_induct) auto

lemma hv_inj: "Hv x = Hv y \<longleftrightarrow> x = y"
  by (simp add: Hv_def octo_eq_iff vec_eq_iff) (metis (full_types) exhaust_7)

lemma linear_hv: "linear Hv"
  using octo_of_real_def by (simp add: linearI)

lemma him_hv [simp]: "HIm(Hv x) = x"
  using HIm_def hv_inj octo_eq_iff by fastforce

lemma cnj_hv [simp]: "cnj(Hv v) = -Hv v"
  by (simp add: octo_eq_iff)

lemma hv_him: "Hv(HIm q) = Octo 0 (Im1 q) (Im2 q) (Im3 q)  (Im4 q) (Im5 q) (Im6 q)  (Im7 q)  "
  by (simp add: HIm_def)

lemma hv_him_eq: "Hv(HIm q) = q \<longleftrightarrow> Ree q = 0"
  by (simp add: hv_him octo_eq_iff)

lemma dot_hv [simp]: "Hv u \<bullet> Hv v = u \<bullet> v"
  by (simp add: Hv_def inner_octo_def inner_vec_def sum_7)

lemma norm_hv [simp]: "norm (Hv v) = norm v"
  by (simp add: norm_eq)

subsubsection\<open>Related basic identities \<close>

lemma mult_hv_eq_cross_dot: "Hv x * Hv y = Hv(x  \<times>\<^sub>7 y) - octo_of_real (inner x y)"
  by (simp add: octo_eq_iff inner_octo_def cross7_components octo_mult_components
                inner_vec_def sum_7)

lemma octonion_identity1_cross7 :
  "Hv (x \<times>\<^sub>7 y) = (1/2) *\<^sub>R (Hv x * Hv y - Hv y * Hv x)" 
  by (simp add: octo_eq_iff octo_mult_components cross7_components)

lemma octonion_identity2_cross7:
  "Hv (x \<times>\<^sub>7 (y \<times>\<^sub>7 z) + y \<times>\<^sub>7 (z \<times>\<^sub>7 x) + z \<times>\<^sub>7 (x \<times>\<^sub>7 y)) =
     -(3/2) *\<^sub>R ((Hv x * Hv y) * Hv z - Hv x * (Hv y * Hv z))"
  unfolding octo_eq_iff octo_mult_components cross7_components Hv_sel scaleR_octo.sel
            vector_add_component minus_octo.sel mult_zero_left mult_zero_right add_0_left
            add_0_right diff_0 diff_0_right
  by algebra

subsection\<open> Representing orthogonal transformations as conjugation or congruence with an octonion.\<close>

lemma HIm_nth [simp]:
  "HIm x $ 1 = Im1 x" "HIm x $ 2 = Im2 x" "HIm x $ 3 = Im3 x"  "HIm x $ 4 = Im4 x"
  "HIm x $ 5 = Im5 x" "HIm x $ 6 = Im6 x" "HIm x $ 7 = Im7 x"               
  by (simp_all add: HIm_def)

lemma orthogonal_transformation_octo_congruence:
  assumes "norm q = 1"
  shows "orthogonal_transformation (\<lambda>x. HIm(cnj q * Hv x * q))"
proof -
  have nq: "(Ree q)\<^sup>2 + (Im1 q)\<^sup>2 + (Im2 q)\<^sup>2 + (Im3 q)\<^sup>2 + (Im4 q)\<^sup>2 + (Im5 q)\<^sup>2 + (Im6 q)\<^sup>2 + (Im7 q)\<^sup>2 = 1"
    using assms norm_octo_def by auto 
  have "Vector_Spaces.linear (*\<^sub>R) (*\<^sub>R) (\<lambda>x. HIm (Octonions.cnj q * Hv x * q))"
    by unfold_locales (simp_all add: octo_distrib_left octo_distrib_right
                                     octo_mult_scaleR_left octo_mult_scaleR_right)
  moreover have "HIm (Octonions.cnj q * Hv v * q) \<bullet> HIm (Octonions.cnj q * Hv w * q) =
                   ((Ree q)\<^sup>2 + (Im1 q)\<^sup>2 + (Im2 q)\<^sup>2 + (Im3 q)\<^sup>2+ (Im4 q)\<^sup>2 + (Im5 q)\<^sup>2 + (Im6 q)\<^sup>2 +
                   (Im7 q)\<^sup>2)^2 * (v \<bullet> w)" for v w
    unfolding octo_mult_components cnj.sel Hv_sel inner_vec_def sum_7 HIm_nth inner_real_def
    by algebra
  ultimately show ?thesis
    by (simp add: orthogonal_transformation_def linear_def nq)
qed

lemma orthogonal_transformation_octo_conjugation:
  assumes "q \<noteq> 0"
  shows "orthogonal_transformation (\<lambda>x. HIm (inverse q * Hv x * q))"
proof -
  obtain c d where eq: "q = octo_of_real c * d" and 1: "norm d = 1"
  proof
    show 1: "q = octo_of_real (norm q) * (inverse (octo_of_real (norm q)) * q)"
      using assms norm_eq_zero right_inverse multiplicative_norm_octo
      by (metis Octonions.scaleR_conv_octo_of_real octo_of_real_inverse scaleR_one scaleR_scaleR)
    show "norm (inverse (octo_of_real (norm q)) * q) = 1"
      using assms 1  norm_octo_def norm_mult inverse_octo_1 inverse_octo_1_sym
      nonzero_octo_of_real_inverse  octo_inverse_eq_cnj
      cnj_of_real mult_cancel_left2 multiplicative_norm_octo
      norm_eq_zero norm_octo_squared norm_power2_cnj octo_mult_cnj_conv_norm power2_eq_square_octo
      by metis
   qed
  have "c \<noteq> 0"
    using assms eq by (metis Octonions.scaleR_conv_octo_of_real scale_zero_left)

  then have "HIm (Octonions.cnj d * Hv x * d) =
               HIm (inverse (octo_of_real c * d) * Hv x * (octo_of_real c * d))" for x
  proof(simp add: flip: octo_inverse_eq_cnj [OF 1] of_real_inverse)
    assume "c \<noteq> 0"
    then have "inverse d = inverse d * inverse (c *\<^sub>R 1) * c *\<^sub>R 1"
      using octo_of_real_def octo_of_real_inverse octo_of_real_inverse_collapse(1)
            octo_of_real_times_commute octo_of_real_times_left_commute by force
    then have "inverse d * Hv x * d = inverse (c *\<^sub>R 1 * d) * Hv x * c *\<^sub>R (d * 1)"
      by (metis (no_types) mult_1_right_octo octo_inverse_mult octo_mult_scaleR_left
                           octo_mult_scaleR_right)
    then show
      "HIm (inverse d * Hv x * d) = HIm (inverse (octo_of_real c * d) * Hv x * (octo_of_real c * d))"
      using octo_mult_scaleR_right octo_of_real_def octo_of_real_times_commute by presburger
  qed

  then show ?thesis
    using orthogonal_transformation_octo_congruence [OF 1]
    by (simp add: eq) 
qed

unbundle no_cross7_syntax

bundle octonion_syntax
begin

notation octo_e0 ("e0")
notation octo_e1 ("e1")
notation octo_e2 ("e2")
notation octo_e3 ("e3")
notation octo_e4 ("e4")
notation octo_e5 ("e5")
notation octo_e6 ("e6")
notation octo_e7 ("e7")

end

bundle no_octonion_syntax
begin

no_notation octo_e0 ("e0")
no_notation octo_e1 ("e1")
no_notation octo_e2 ("e2")
no_notation octo_e3 ("e3")
no_notation octo_e4 ("e4")
no_notation octo_e5 ("e5")
no_notation octo_e6 ("e6")
no_notation octo_e7 ("e7")

end

unbundle no_octonion_syntax
hide_const (open) Octonions.cnj

end