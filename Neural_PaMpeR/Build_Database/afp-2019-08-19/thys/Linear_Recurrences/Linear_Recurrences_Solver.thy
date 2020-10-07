(*
  File:    Linear_Recurrences_Solver.thy
  Author:  Manuel Eberl, TU München
*)
section \<open>Solver for linear recurrences\<close>
theory Linear_Recurrences_Solver
imports
  Complex_Main
  Linear_Homogenous_Recurrences
  Linear_Inhomogenous_Recurrences
  "Algebraic_Numbers.Complex_Algebraic_Numbers"
begin

lemma factorize_complex_main:
  assumes "factorize_complex_main p = Some fctrs"
  shows   "is_factorization_of fctrs p"
  unfolding is_factorization_of_def
proof safe
  from assms have "p = Polynomial.smult (fst fctrs) (\<Prod>(x, i)\<leftarrow>snd fctrs. [:- x, 1:] ^ Suc i)"
    by (intro factorize_complex_main) simp_all
  also have "\<dots> = interp_factorization fctrs" 
    by (simp add: interp_factorization_def case_prod_unfold)
  finally show "interp_factorization fctrs = p" ..
qed (insert assms, simp_all add: distinct_factorize_complex_main)


definition solve_ratfps 
    :: "complex ratfps \<Rightarrow> (complex poly \<times> (complex poly \<times> complex) list) option" where
  "solve_ratfps f = 
     (case quot_of_ratfps f of (p, q) \<Rightarrow>  
       map_option (solve_factored_ratfps' p) (factorize_complex_main (reflect_poly q)))"

lemma solve_ratfps:
  assumes "solve_ratfps f = Some sol"
  shows   "Abs_fps (interp_ratfps_solution sol) = fps_of_ratfps f"
proof -
  define p and q where "p = fst (quot_of_ratfps f)" and "q = snd (quot_of_ratfps f)"
  with assms obtain fctrs where fctrs: "factorize_complex_main (reflect_poly q) = Some fctrs"
    by (auto simp: solve_ratfps_def p_def q_def case_prod_unfold split: if_splits)
  have q: "coeff q 0 \<noteq> 0" by (simp add: q_def)
  hence [simp]: "q \<noteq> 0" by auto
  from fctrs have "is_factorization_of fctrs (reflect_poly q)"
    by (rule factorize_complex_main)
  with assms have "is_alt_factorization_of fctrs (reflect_poly (reflect_poly q))"
    by (intro reflect_factorization) simp_all
  hence "is_alt_factorization_of fctrs q" by (simp add: q)
  with fctrs q 
    have "Abs_fps (interp_ratfps_solution (solve_factored_ratfps' p fctrs)) = 
            fps_of_poly p / fps_of_poly q"
    by (intro solve_factored_ratfps') (simp_all)
  also from fctrs assms have "solve_factored_ratfps' p fctrs = sol"
    by (simp add: solve_ratfps_def p_def q_def case_prod_unfold split: if_splits)
  finally show ?thesis by (simp add: fps_of_ratfps_altdef case_prod_unfold p_def q_def)
qed


definition solve_lhr 
    :: "complex list \<Rightarrow> complex list \<Rightarrow> (complex poly \<times> (complex poly \<times> complex) list) option" where
  "solve_lhr cs fs = (if cs = [] \<or> length fs < length cs - 1 then None else
     let m = length fs + 1 - length cs;
         p = lhr_fps_numerator m cs (\<lambda>n. fs ! n);
         q = lr_fps_denominator' cs
     in  map_option (solve_factored_ratfps' p) (factorize_complex_main q))"


lemma solve_lhr:
  assumes "linear_homogenous_recurrence f cs fs"
  assumes "Some sol = solve_lhr cs fs"
  shows   "f = interp_ratfps_solution sol"
proof -
  from assms(2) obtain fctrs where 
      fctrs: "factorize_complex_main (lr_fps_denominator' cs) = Some fctrs"
    by (cases "factorize_complex_main (lr_fps_denominator' cs)")
       (simp_all add: solve_lhr_def Let_def split: if_splits)
  from factorize_complex_main[OF this] 
    have factorization: "is_factorization_of fctrs (lr_fps_denominator' cs)" . 

  have "f = interp_ratfps_solution (solve_factored_ratfps' (lhr_fps_numerator 
              (length fs + 1 - length cs) cs ((!) fs)) fctrs)"
    (is "_ = interp_ratfps_solution ?sol") by (intro solve_lhr_aux) fact+
  also from assms(2) have "?sol = sol"
    by (auto simp: solve_lhr_def Let_def case_prod_unfold fctrs split: if_splits)
  finally show ?thesis .
qed

definition solve_lir 
    :: "complex list \<Rightarrow> complex list \<Rightarrow> complex polyexp \<Rightarrow> 
          (complex poly \<times> (complex poly \<times> complex) list) option" where
  "solve_lir cs fs g = Option.bind (lir_fps cs fs g) solve_ratfps"

lemma solve_lir:
  assumes "linear_inhomogenous_recurrence f (eval_polyexp g) cs fs"
  assumes "solve_lir cs fs g = Some sol"
  shows   "f = interp_ratfps_solution sol"
proof -
  from lir_fps_correct[OF assms(1)] obtain fps 
    where fps: "lir_fps cs fs g = Some fps" "fps_of_ratfps fps = Abs_fps f" by blast
  from assms(2) have "solve_ratfps fps = Some sol"
    by (simp add: solve_lir_def fps case_prod_unfold)
  from solve_ratfps[OF this] have "Abs_fps (interp_ratfps_solution sol) = fps_of_ratfps fps"
    by (simp add: case_prod_unfold fps_of_ratfps_altdef)
  with fps have "Abs_fps f = Abs_fps (interp_ratfps_solution sol)" by simp
  thus ?thesis by (simp add: fun_eq_iff fps_eq_iff)
qed

end
