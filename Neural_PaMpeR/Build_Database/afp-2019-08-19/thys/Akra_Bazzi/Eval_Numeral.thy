(*
  File:   Eval_Numeral.thy
  Author: Manuel Eberl <eberlm@in.tum.de>

  Evaluation of terms involving rational numerals with the simplifier.
*)
section \<open>Evaluating expressions with rational numerals\<close>
theory Eval_Numeral
imports
  Complex_Main
begin

lemma real_numeral_to_Ratreal:
  "(0::real) = Ratreal (Frct (0, 1))"
  "(1::real) = Ratreal (Frct (1, 1))"
  "(numeral x :: real) = Ratreal (Frct (numeral x, 1))"
  "(1::int) = numeral Num.One"
  by (simp_all add: rat_number_collapse)

lemma real_equals_code: "Ratreal x = Ratreal y \<longleftrightarrow> x = y"
  by simp

lemma Rat_normalize_idempotent: "Rat.normalize (Rat.normalize x) = Rat.normalize x"
apply (cases "Rat.normalize x")
using Rat.normalize_stable[OF normalize_denom_pos normalize_coprime] apply auto
done

lemma uminus_pow_Numeral1: "(-(x::_::monoid_mult)) ^ Numeral1 = -x" by simp

lemmas power_numeral_simps = power_0 uminus_pow_Numeral1 power_minus_Bit0 power_minus_Bit1

lemma Fract_normalize: "Fract (fst (Rat.normalize (x,y))) (snd (Rat.normalize (x,y))) = Fract x y"
  by (rule quotient_of_inject) (simp add: quotient_of_Fract Rat_normalize_idempotent)

lemma Frct_add: "Frct (a, numeral b) + Frct (c, numeral d) =
                   Frct (Rat.normalize (a * numeral d + c * numeral b, numeral (b*d)))"
  by (auto simp: rat_number_collapse Fract_normalize)


lemma Frct_uminus: "-(Frct (a,b)) = Frct (-a,b)" by simp

lemma Frct_diff: "Frct (a, numeral b) - Frct (c, numeral d) =
                    Frct (Rat.normalize (a * numeral d - c * numeral b, numeral (b*d)))"
  by (auto simp: rat_number_collapse Fract_normalize)

lemma Frct_mult: "Frct (a, numeral b) * Frct (c, numeral d) = Frct (a*c, numeral (b*d))"
  by simp

lemma Frct_inverse: "inverse (Frct (a, b)) = Frct (b, a)" by simp

lemma Frct_divide: "Frct (a, numeral b) / Frct (c, numeral d) = Frct (a*numeral d, numeral b * c)"
  by simp

lemma Frct_pow: "Frct (a, numeral b) ^ c = Frct (a ^ c, numeral b ^ c)"
  by (induction c) (simp_all add: rat_number_collapse)

lemma Frct_less: "Frct (a, numeral b) < Frct (c, numeral d) \<longleftrightarrow> a * numeral d < c * numeral b"
  by simp

lemma Frct_le: "Frct (a, numeral b) \<le> Frct (c, numeral d) \<longleftrightarrow> a * numeral d \<le> c * numeral b"
  by simp

lemma Frct_equals: "Frct (a, numeral b) = Frct (c, numeral d) \<longleftrightarrow> a * numeral d = c * numeral b"
apply (intro iffI antisym)
apply (subst Frct_le[symmetric], simp)+
apply (subst Frct_le, simp)+
done

lemma real_power_code: "(Ratreal x) ^ y = Ratreal (x ^ y)" by (simp add: of_rat_power)

lemmas real_arith_code =
  real_plus_code real_minus_code real_times_code real_uminus_code real_inverse_code
  real_divide_code real_power_code real_less_code real_less_eq_code real_equals_code

lemmas rat_arith_code =
  Frct_add Frct_uminus Frct_diff Frct_mult Frct_inverse Frct_divide Frct_pow
  Frct_less Frct_le Frct_equals

lemma gcd_numeral_red: "gcd (numeral x::int) (numeral y) = gcd (numeral y) (numeral x mod numeral y)"
  by (fact gcd_red_int)

lemma divmod_one:
  "divmod (Num.One) (Num.One) = (Numeral1, 0)"
  "divmod (Num.One) (Num.Bit0 x) = (0, Numeral1)"
  "divmod (Num.One) (Num.Bit1 x) = (0, Numeral1)"
  "divmod x (Num.One) = (numeral x, 0)"
  unfolding divmod_def by simp_all

lemmas divmod_numeral_simps =
  div_0 div_by_0 mod_0 mod_by_0
  fst_divmod [symmetric]
  snd_divmod [symmetric]
  divmod_cancel
  divmod_steps [simplified rel_simps if_True] divmod_trivial
  rel_simps

lemma Suc_0_to_numeral: "Suc 0 = Numeral1" by simp
lemmas Suc_to_numeral = Suc_0_to_numeral Num.Suc_1 Num.Suc_numeral

lemma rat_powr:
  "0 powr y = 0"
  "x > 0 \<Longrightarrow> x powr Ratreal (Frct (0, Numeral1)) = Ratreal (Frct (Numeral1, Numeral1))"
  "x > 0 \<Longrightarrow> x powr Ratreal (Frct (numeral a, Numeral1)) = x ^ numeral a"
  "x > 0 \<Longrightarrow> x powr Ratreal (Frct (-numeral a, Numeral1)) = inverse (x ^ numeral a)"
  by (simp_all add: rat_number_collapse powr_minus)

lemmas eval_numeral_simps =
  real_numeral_to_Ratreal real_arith_code rat_arith_code Num.arith_simps
  Rat.normalize_def fst_conv snd_conv gcd_0_int gcd_0_left_int gcd.bottom_right_bottom gcd.bottom_left_bottom
  gcd_neg1_int gcd_neg2_int gcd_numeral_red zmod_numeral_Bit0 zmod_numeral_Bit1 power_numeral_simps
  divmod_numeral_simps numeral_One [symmetric] Groups.Let_0 Num.Let_numeral Suc_to_numeral power_numeral
  greaterThanLessThan_iff atLeastAtMost_iff atLeastLessThan_iff greaterThanAtMost_iff rat_powr
  Num.pow.simps Num.sqr.simps Product_Type.split of_int_numeral of_int_neg_numeral of_nat_numeral

ML \<open>
signature EVAL_NUMERAL =
sig
  val eval_numeral_tac : Proof.context -> int -> tactic
end

structure Eval_Numeral : EVAL_NUMERAL =
struct

fun eval_numeral_tac ctxt =
  let
    val ctxt' = put_simpset HOL_ss ctxt addsimps @{thms eval_numeral_simps}
  in
    SELECT_GOAL (SOLVE (Simplifier.simp_tac ctxt' 1))
  end

end
\<close>

lemma "21254387548659589512*314213523632464357453884361*2342523623324234*564327438587241734743*
          12561712738645824362329316482973164398214286 powr 2 /
         (1130246312978423123+231212374631082764842731842*122474378389424362347451251263) >
        (12313244512931247243543279768645745929475829310651205623844::real)"
  by (tactic \<open>Eval_Numeral.eval_numeral_tac @{context} 1\<close>)

end
