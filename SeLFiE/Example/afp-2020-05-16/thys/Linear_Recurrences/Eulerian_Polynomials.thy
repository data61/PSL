(*
  File:    Eulerian_Polynomials.thy
  Author:  Manuel Eberl, TU München
*)
section \<open>Eulerian polynomials\<close>
theory Eulerian_Polynomials
imports 
  Complex_Main 
  "HOL-Computational_Algebra.Computational_Algebra"
  "HOL-Library.Stirling"
begin

text \<open>
  The Eulerian polynomials are a sequence of polynomials that is related to
  the closed forms of the power series
  \[\sum_{n=0}^\infty n^k X^n\]
  for a fixed $k$.
\<close>
primrec eulerian_poly :: "nat \<Rightarrow> 'a :: idom poly" where
  "eulerian_poly 0 = 1"
| "eulerian_poly (Suc n) = (let p = eulerian_poly n in 
     [:0,1,-1:] * pderiv p + p * [:1, of_nat n:])"

lemmas eulerian_poly_Suc [simp del] = eulerian_poly.simps(2)

lemma eulerian_poly:
  "fps_of_poly (eulerian_poly k :: 'a :: field poly) = 
     Abs_fps (\<lambda>n. of_nat (n+1) ^ k) * (1 - fps_X) ^ (k + 1)"
proof (induction k)
  case 0
  have "Abs_fps (\<lambda>_. 1 :: 'a) = inverse (1 - fps_X)"
    by (rule fps_inverse_unique [symmetric])
       (simp add: inverse_mult_eq_1 fps_inverse_gp' [symmetric])
  thus ?case by (simp add: inverse_mult_eq_1)
next
  case (Suc k)
  define p :: "'a fps" where "p = fps_of_poly (eulerian_poly k)"
  define F :: "'a fps" where "F = Abs_fps (\<lambda>n. of_nat (n+1) ^ k)"

  have p: "p = F * (1 - fps_X) ^ (k+1)" by (simp add: p_def Suc F_def)
  have p': "fps_deriv p = fps_deriv F * (1 - fps_X) ^ (k + 1) - F * (1 - fps_X) ^ k * of_nat (k + 1)"
    by (simp add: p fps_deriv_power algebra_simps fps_const_neg [symmetric] fps_of_nat 
             del: power_Suc of_nat_Suc fps_const_neg)
  
  have "fps_of_poly (eulerian_poly (Suc k)) = (fps_X * fps_deriv F + F) * (1 - fps_X) ^ (Suc k + 1)"
    apply (simp add: Let_def p_def [symmetric] fps_of_poly_simps eulerian_poly_Suc del: power_Suc)
    apply (simp add: p p' fps_deriv_power fps_const_neg [symmetric] fps_of_nat
                del: power_Suc of_nat_Suc fps_const_neg)
    apply (simp add: algebra_simps)
    done
  also have "fps_X * fps_deriv F + F = Abs_fps (\<lambda>n. of_nat (n + 1) ^ Suc k)"
    unfolding F_def by (intro fps_ext) (auto simp: algebra_simps)
  finally show ?case .
qed

lemma eulerian_poly':
  "Abs_fps (\<lambda>n. of_nat (n+1) ^ k) = 
     fps_of_poly (eulerian_poly k :: 'a :: field poly) / (1 - fps_X) ^ (k + 1)"
  by (subst eulerian_poly) simp
  
lemma eulerian_poly'':
  assumes k: "k > 0"
  shows "Abs_fps (\<lambda>n. of_nat n ^ k) = 
           fps_of_poly (pCons 0 (eulerian_poly k :: 'a :: field poly)) / (1 - fps_X) ^ (k + 1)"
proof -
  from assms have "Abs_fps (\<lambda>n. of_nat n ^ k :: 'a) = fps_X * Abs_fps (\<lambda>n. of_nat (n + 1) ^ k)"
    by (intro fps_ext) (auto simp: of_nat_diff)
  also have "Abs_fps (\<lambda>n. of_nat (n + 1) ^ k :: 'a) = 
               fps_of_poly (eulerian_poly k) / (1 - fps_X) ^ (k + 1)" by (rule eulerian_poly')
  also have "fps_X * \<dots> = fps_of_poly (pCons 0 (eulerian_poly k)) / (1 - fps_X) ^ (k + 1)"
    by (simp add: fps_of_poly_pCons fps_divide_unit)
  finally show ?thesis .
qed

definition fps_monom_poly :: "'a :: field \<Rightarrow> nat \<Rightarrow> 'a poly"
  where "fps_monom_poly c k = (if k = 0 then 1 else pcompose (pCons 0 (eulerian_poly k)) [:0,c:])"

primrec fps_monom_poly_aux :: "'a :: field \<Rightarrow> nat \<Rightarrow> 'a poly" where
  "fps_monom_poly_aux c 0 = [:c:]"
| "fps_monom_poly_aux c (Suc k) = 
      (let p = fps_monom_poly_aux c k
       in  [:0,1,-c:] * pderiv p + [:1, of_nat k * c:] * p)"

lemma fps_monom_poly_aux:
  "fps_monom_poly_aux c k = smult c (pcompose (eulerian_poly k) [:0,c:])"
  by (induction k) 
     (simp_all add: eulerian_poly_Suc Let_def pderiv_pcompose pcompose_pCons
                    pcompose_add pcompose_smult pcompose_uminus smult_add_right pderiv_pCons
                    pderiv_smult algebra_simps one_pCons)

lemma fps_monom_poly_code [code]:
  "fps_monom_poly c k = (if k = 0 then 1 else pCons 0 (fps_monom_poly_aux c k))"
  by (simp add: fps_monom_poly_def fps_monom_poly_aux pcompose_pCons)

lemma fps_monom_aux: 
  "Abs_fps (\<lambda>n. of_nat n ^ k) = fps_of_poly (fps_monom_poly 1 k) / (1 - fps_X) ^ (k+1)"
proof (cases "k = 0")
  assume [simp]: "k = 0"
  hence "Abs_fps (\<lambda>n. of_nat n ^ k :: 'a) = Abs_fps (\<lambda>_. 1)" by simp
  also have "\<dots> = 1 / (1 - fps_X)" by (subst gp [symmetric]) simp_all
  finally show ?thesis by (simp add: fps_monom_poly_def)
qed (insert eulerian_poly''[of k, where ?'a = 'a], simp add: fps_monom_poly_def)

lemma fps_monom:
  "Abs_fps (\<lambda>n. of_nat n ^ k * c ^ n) = 
      fps_of_poly (fps_monom_poly c k) / (1 - fps_const c * fps_X) ^ (k+1)"
proof -
  have "Abs_fps (\<lambda>n. of_nat n ^ k * c ^ n) = 
          fps_compose (Abs_fps (\<lambda>n. of_nat n ^ k)) (fps_const c * fps_X)"
    by (subst fps_compose_linear) (simp add: mult_ac)
  also have "Abs_fps (\<lambda>n. of_nat n ^ k) = fps_of_poly (fps_monom_poly 1 k) / (1 - fps_X) ^ (k+1)"
    by (rule fps_monom_aux)
  also have "fps_compose \<dots> (fps_const c * fps_X) = 
                 (fps_of_poly (fps_monom_poly 1 k) oo fps_const c * fps_X) /
                 ((1 - fps_X) ^ (k + 1) oo fps_const c * fps_X)"
    by (intro fps_compose_divide_distrib)
       (simp_all add: fps_compose_power [symmetric] fps_compose_sub_distrib del: power_Suc)
  also have "fps_of_poly (fps_monom_poly 1 k) oo (fps_const c * fps_X) = 
                fps_of_poly (fps_monom_poly c k)"
    by (simp add: fps_monom_poly_def fps_of_poly_pcompose fps_of_poly_simps
                  fps_of_poly_pCons mult_ac)
  also have "((1 - fps_X) ^ (k + 1) oo fps_const c * fps_X) = (1 - fps_const c * fps_X) ^ (k + 1)"
    by (simp add: fps_compose_power [symmetric] fps_compose_sub_distrib del: power_Suc)
  finally show ?thesis .
qed

end
