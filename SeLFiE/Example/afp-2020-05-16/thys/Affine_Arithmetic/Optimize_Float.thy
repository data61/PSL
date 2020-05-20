section \<open>Optimizations for Code Float\<close>
theory Optimize_Float
imports
  "HOL-Library.Float"
  Optimize_Integer
begin

lemma compute_bitlen[code]: "bitlen a = (if a > 0 then log2 a + 1 else 0)"
  by (simp add: bitlen_alt_def log2_def)

lemma compute_float_plus[code]: "Float m1 e1 + Float m2 e2 =
  (if m1 = 0 then Float m2 e2 else if m2 = 0 then Float m1 e1 else
  if e1 \<le> e2 then Float (m1 + m2 * power_int 2 (e2 - e1)) e1
              else Float (m2 + m1 * power_int 2 (e1 - e2)) e2)"
  by (simp add: Float.compute_float_plus power_int_def)

lemma compute_real_of_float[code]:
  "real_of_float (Float m e) = (if e \<ge> 0 then m * 2 ^ nat e else m / power_int 2 (-e))"
  unfolding power_int_def[symmetric, of 2 e]
  using compute_real_of_float power_int_def by auto

lemma compute_float_down[code]:
  "float_down p (Float m e) =
    (if p + e < 0 then Float (m div power_int 2 (-(p + e))) (-p) else Float m e)"
  by (simp add: Float.compute_float_down power_int_def)

lemma compute_lapprox_posrat[code]:
  fixes prec::nat and x y::nat
  shows "lapprox_posrat prec x y =
   (let
       l = rat_precision prec x y;
       d = if 0 \<le> l then int x * power_int 2 l div y else int x div power_int 2 (- l) div y
    in normfloat (Float d (- l)))"
  by (auto simp add: Float.compute_lapprox_posrat power_int_def Let_def zdiv_int of_nat_power of_nat_mult)

lemma compute_rapprox_posrat[code]:
  fixes prec x y
  defines "l \<equiv> rat_precision prec x y"
  shows "rapprox_posrat prec x y = (let
     l = l ;
     (r, s) = if 0 \<le> l then (int x * power_int 2 l, int y) else (int x, int y * power_int 2 (-l)) ;
     d = r div s ;
     m = r mod s
   in normfloat (Float (d + (if m = 0 \<or> y = 0 then 0 else 1)) (- l)))"
  by (auto simp add: l_def Float.compute_rapprox_posrat power_int_def Let_def zdiv_int of_nat_power of_nat_mult)

lemma compute_float_truncate_down[code]:
  "float_round_down prec (Float m e) = (let d = bitlen (abs m) - int prec - 1 in
    if 0 < d then let P = power_int 2 d ; n = m div P in Float n (e + d)
             else Float m e)"
  by (simp add: Float.compute_float_round_down power_int_def cong: if_cong)

lemma compute_int_floor_fl[code]:
  "int_floor_fl (Float m e) = (if 0 \<le> e then m * power_int 2 e else m div (power_int 2 (-e)))"
  by (simp add: Float.compute_int_floor_fl power_int_def)

lemma compute_floor_fl[code]:
  "floor_fl (Float m e) = (if 0 \<le> e then Float m e else Float (m div (power_int 2 ((-e)))) 0)"
  by (simp add: Float.compute_floor_fl power_int_def)

end

