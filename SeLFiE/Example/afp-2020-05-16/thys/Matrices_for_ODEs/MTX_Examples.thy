(*  Title:       Verification Examples
    Author:      Jonathan Julián Huerta y Munive, 2020
    Maintainer:  Jonathan Julián Huerta y Munive <jjhuertaymunive1@sheffield.ac.uk>
*)

section \<open> Verification examples \<close>


theory MTX_Examples
  imports MTX_Flows "Hybrid_Systems_VCs.HS_VC_Spartan"

begin


subsection \<open> Examples \<close>

abbreviation hoareT :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a set) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool" 
  ("PRE_ HP _ POST _" [85,85]85) where "PRE P HP X POST Q \<equiv> (P \<le> |X]Q)"


subsubsection \<open> Verification by uniqueness. \<close>

abbreviation mtx_circ :: "2 sq_mtx" ("A")
  where "A \<equiv> mtx  
   ([0,  1] # 
    [-1, 0] # [])"

abbreviation mtx_circ_flow :: "real \<Rightarrow> real^2 \<Rightarrow> real^2" ("\<phi>")
  where "\<phi> t s \<equiv> (\<chi> i. if i = 1 then s$1 * cos t + s$2 * sin t else - s$1 * sin t + s$2 * cos t)"

lemma mtx_circ_flow_eq: "exp (t *\<^sub>R A) *\<^sub>V s = \<phi> t s"
  apply(rule local_flow.eq_solution[OF local_flow_sq_mtx_linear, symmetric])
    apply(rule ivp_solsI, simp_all add: sq_mtx_vec_mult_eq vec_eq_iff)
  unfolding UNIV_2 using exhaust_2
  by (force intro!: poly_derivatives simp: matrix_vector_mult_def)+

lemma mtx_circ: 
  "PRE(\<lambda>s. r\<^sup>2 = (s $ 1)\<^sup>2 + (s $ 2)\<^sup>2) 
  HP x\<acute>=(*\<^sub>V) A & G 
  POST (\<lambda>s. r\<^sup>2 = (s $ 1)\<^sup>2 + (s $ 2)\<^sup>2)"
  apply(subst local_flow.fbox_g_ode[OF local_flow_sq_mtx_linear])
  unfolding mtx_circ_flow_eq by auto

no_notation mtx_circ ("A")
        and mtx_circ_flow ("\<phi>")


subsubsection \<open> Flow of diagonalisable matrix. \<close>

abbreviation mtx_hOsc :: "real \<Rightarrow> real \<Rightarrow> 2 sq_mtx" ("A")
  where "A a b \<equiv> mtx  
   ([0, 1] # 
    [a, b] # [])"

abbreviation mtx_chB_hOsc :: "real \<Rightarrow> real \<Rightarrow> 2 sq_mtx" ("P")
  where "P a b \<equiv> mtx
   ([a, b] # 
    [1, 1] # [])"

lemma inv_mtx_chB_hOsc: 
  "a \<noteq> b \<Longrightarrow> (P a b)\<^sup>-\<^sup>1 = (1/(a - b)) *\<^sub>R mtx 
   ([ 1, -b] # 
    [-1,  a] # [])"
  apply(rule sq_mtx_inv_unique, unfold scaleR_mtx2 times_mtx2)
  by (simp add: diff_divide_distrib[symmetric] one_mtx2)+

lemma invertible_mtx_chB_hOsc: "a \<noteq> b \<Longrightarrow> mtx_invertible (P a b)"
  apply(rule mtx_invertibleI[of _ "(P a b)\<^sup>-\<^sup>1"])
   apply(unfold inv_mtx_chB_hOsc scaleR_mtx2 times_mtx2 one_mtx2)
  by (subst sq_mtx_eq_iff, simp add: vector_def frac_diff_eq1)+

lemma mtx_hOsc_diagonalizable:
  fixes a b :: real
  defines "\<iota>\<^sub>1 \<equiv> (b - sqrt (b^2+4*a))/2" and "\<iota>\<^sub>2 \<equiv> (b + sqrt (b^2+4*a))/2"
  assumes "b\<^sup>2 + a * 4 > 0" and "a \<noteq> 0"
  shows "A a b = P (-\<iota>\<^sub>2/a) (-\<iota>\<^sub>1/a) * (\<d>\<i>\<a>\<g> i. if i = 1 then \<iota>\<^sub>1 else \<iota>\<^sub>2) * (P (-\<iota>\<^sub>2/a) (-\<iota>\<^sub>1/a))\<^sup>-\<^sup>1"
  unfolding assms apply(subst inv_mtx_chB_hOsc)
  using assms(3,4) apply(simp_all add: diag2_eq[symmetric])
  unfolding sq_mtx_times_eq sq_mtx_scaleR_eq UNIV_2 apply(subst sq_mtx_eq_iff)
  using exhaust_2 assms by (auto simp: field_simps, auto simp: field_power_simps)

lemma mtx_hOsc_solution_eq:
  fixes a b :: real
  defines "\<iota>\<^sub>1 \<equiv> (b - sqrt (b\<^sup>2+4*a))/2" and "\<iota>\<^sub>2 \<equiv> (b + sqrt (b\<^sup>2+4*a))/2"
  defines "\<Phi> t \<equiv> mtx (
   [\<iota>\<^sub>2*exp(t*\<iota>\<^sub>1) - \<iota>\<^sub>1*exp(t*\<iota>\<^sub>2),     exp(t*\<iota>\<^sub>2)-exp(t*\<iota>\<^sub>1)]#
   [a*exp(t*\<iota>\<^sub>2) - a*exp(t*\<iota>\<^sub>1), \<iota>\<^sub>2*exp(t*\<iota>\<^sub>2)-\<iota>\<^sub>1*exp(t*\<iota>\<^sub>1)]#[])"
  assumes "b\<^sup>2 + a * 4 > 0" and "a \<noteq> 0"
  shows "P (-\<iota>\<^sub>2/a) (-\<iota>\<^sub>1/a) * (\<d>\<i>\<a>\<g> i. exp (t * (if i=1 then \<iota>\<^sub>1 else \<iota>\<^sub>2))) * (P (-\<iota>\<^sub>2/a) (-\<iota>\<^sub>1/a))\<^sup>-\<^sup>1 
  = (1/sqrt (b\<^sup>2 + a * 4)) *\<^sub>R (\<Phi> t)"
  unfolding assms apply(subst inv_mtx_chB_hOsc)
  using assms apply(simp_all add: mtx_times_scaleR_commute, subst sq_mtx_eq_iff)
  unfolding UNIV_2 sq_mtx_times_eq sq_mtx_scaleR_eq sq_mtx_uminus_eq apply(simp_all add: axis_def)
  by (auto simp: field_simps, auto simp: field_power_simps)+
 
lemma local_flow_mtx_hOsc:
  fixes a b
  defines "\<iota>\<^sub>1 \<equiv> (b - sqrt (b^2+4*a))/2" and "\<iota>\<^sub>2 \<equiv> (b + sqrt (b^2+4*a))/2"
  defines "\<Phi> t \<equiv> mtx (
   [\<iota>\<^sub>2*exp(t*\<iota>\<^sub>1) - \<iota>\<^sub>1*exp(t*\<iota>\<^sub>2),     exp(t*\<iota>\<^sub>2)-exp(t*\<iota>\<^sub>1)]#
   [a*exp(t*\<iota>\<^sub>2) - a*exp(t*\<iota>\<^sub>1), \<iota>\<^sub>2*exp(t*\<iota>\<^sub>2)-\<iota>\<^sub>1*exp(t*\<iota>\<^sub>1)]#[])"
  assumes "b\<^sup>2 + a * 4 > 0" and "a \<noteq> 0"
  shows "local_flow ((*\<^sub>V) (A a b)) UNIV UNIV (\<lambda>t. (*\<^sub>V) ((1/sqrt (b\<^sup>2 + a * 4)) *\<^sub>R \<Phi> t))"
  unfolding assms using local_flow_sq_mtx_linear[of "A a b"] assms
  apply(subst (asm) exp_scaleR_diagonal2[OF invertible_mtx_chB_hOsc mtx_hOsc_diagonalizable])
     apply(simp, simp, simp)
  by (subst (asm) mtx_hOsc_solution_eq) simp_all

lemma overdamped_door_arith:
  assumes "b\<^sup>2 + a * 4 > 0" and "a < 0" and "b \<le> 0" and "t \<ge> 0" and "s1 > 0"
  shows "0 \<le> ((b + sqrt (b\<^sup>2 + 4 * a)) * exp (t * (b - sqrt (b\<^sup>2 + 4 * a)) / 2) / 2 - 
(b - sqrt (b\<^sup>2 + 4 * a)) * exp (t * (b + sqrt (b\<^sup>2 + 4 * a)) / 2) / 2) * s1 / sqrt (b\<^sup>2 + a * 4)"
proof(subst diff_divide_distrib[symmetric], simp)
  have f0: "s1 / (2 * sqrt (b\<^sup>2 + a * 4)) > 0"  (is "s1/?c3 > 0")
    using assms(1,5) by simp
  have f1: "(b - sqrt (b\<^sup>2 + 4 * a)) < (b + sqrt (b\<^sup>2 + 4 * a))" (is "?c2 < ?c1") 
    and f2: "(b + sqrt (b\<^sup>2 + 4 * a)) < 0"
    using sqrt_ge_absD[of b "b\<^sup>2 + 4 * a"] assms by (force, linarith)
  hence f3: "exp (t * ?c2 / 2) \<le> exp (t * ?c1 / 2)" (is "exp ?t1 \<le> exp ?t2")
    unfolding exp_le_cancel_iff 
    using assms(4) by (case_tac "t=0", simp_all)
  hence "?c2 * exp ?t2 \<le> ?c2 * exp ?t1"
    using f1 f2 real_mult_le_cancel_iff2[of "-?c2" "exp ?t1" "exp ?t2"] by linarith 
  also have "... < ?c1 * exp ?t1"
    using f1 by auto
  also have"... \<le> ?c1 * exp ?t1"
    using f1 f2 by auto
  ultimately show "0 \<le> (?c1 * exp ?t1 - ?c2 * exp ?t2) * s1 / ?c3"
    using f0 f1 assms(5) by auto
qed

lemma overdamped_door:
  assumes "b\<^sup>2 + a * 4 > 0" and "a < 0" and "b \<le> 0" and "0 \<le> t"
  shows "PRE (\<lambda>s. s$1 = 0)
  HP (LOOP 
      (\<lambda>s. {s. s$1 > 0 \<and> s$2 = 0});
      (x\<acute>=(*\<^sub>V) (A a b) & G on {0..t} UNIV @ 0) 
     INV (\<lambda>s. 0 \<le> s$1))
  POST (\<lambda>s. 0 \<le> s $ 1)"
  apply(rule fbox_loopI, simp_all add: le_fun_def)
  apply(subst local_flow.fbox_g_ode_ivl[OF local_flow_mtx_hOsc[OF assms(1)]])
  using assms apply(simp_all add: le_fun_def fbox_def)
  unfolding sq_mtx_scaleR_eq UNIV_2 sq_mtx_vec_mult_eq
  by (clarsimp simp: overdamped_door_arith)


no_notation mtx_hOsc ("A")
        and mtx_chB_hOsc ("P")


subsubsection \<open> Flow of non-diagonalisable matrix. \<close>

abbreviation mtx_cnst_acc :: "3 sq_mtx" ("K")
  where "K \<equiv> mtx (
  [0,1,0] #
  [0,0,1] # 
  [0,0,0] # [])"

lemma pow2_scaleR_mtx_cnst_acc: "(t *\<^sub>R K)\<^sup>2 = mtx (
  [0,0,t\<^sup>2] #
  [0,0,0] # 
  [0,0,0] # [])"
  unfolding power2_eq_square apply(subst sq_mtx_eq_iff)
  unfolding sq_mtx_times_eq UNIV_3 by auto

lemma powN_scaleR_mtx_cnst_acc: "n > 2 \<Longrightarrow> (t *\<^sub>R K)^n = 0"
  apply(induct n, simp, case_tac "n \<le> 2")
   apply(subgoal_tac "n = 2", erule ssubst)
  unfolding power_Suc2 pow2_scaleR_mtx_cnst_acc sq_mtx_times_eq UNIV_3
  by (auto simp: sq_mtx_eq_iff)

lemma exp_mtx_cnst_acc: "exp (t *\<^sub>R K) = ((t *\<^sub>R K)\<^sup>2/\<^sub>R 2) + (t *\<^sub>R K) + 1"
  unfolding exp_def apply(subst suminf_eq_sum[of 2])
  using powN_scaleR_mtx_cnst_acc by (simp_all add: numeral_2_eq_2)
 
lemma exp_mtx_cnst_acc_simps:
  "exp (t *\<^sub>R K) $$ 1 $ 1 = 1" "exp (t *\<^sub>R K) $$ 1 $ 2 = t" "exp (t *\<^sub>R K) $$ 1 $ 3 = t^2/2"
  "exp (t *\<^sub>R K) $$ 2 $ 1 = 0" "exp (t *\<^sub>R K) $$ 2 $ 2 = 1" "exp (t *\<^sub>R K) $$ 2 $ 3 = t"
  "exp (t *\<^sub>R K) $$ 3 $ 1 = 0" "exp (t *\<^sub>R K) $$ 3 $ 2 = 0" "exp (t *\<^sub>R K) $$ 3 $ 3 = 1"
  unfolding exp_mtx_cnst_acc one_mtx3 pow2_scaleR_mtx_cnst_acc by simp_all

lemma exp_mtx_cnst_acc_vec_mult_eq: "exp (t *\<^sub>R K) *\<^sub>V s = 
  vector [s$3 * t^2/2 + s$2 * t + s$1, s$3 * t + s$2, s$3]"
  apply(simp add: sq_mtx_vec_mult_eq vector_def)
  unfolding UNIV_3 apply (simp add: exp_mtx_cnst_acc_simps fun_eq_iff)
  using exhaust_3 exp_mtx_cnst_acc_simps(7,8,9) by fastforce

lemma local_flow_mtx_cnst_acc:
  "local_flow ((*\<^sub>V) K) UNIV UNIV (\<lambda>t s. ((t *\<^sub>R K)\<^sup>2/\<^sub>R 2 + (t *\<^sub>R K) + 1) *\<^sub>V s)"
  using local_flow_sq_mtx_linear[of K] unfolding exp_mtx_cnst_acc .  

lemma docking_station_arith:
  assumes "(d::real) > x" and "v > 0"
  shows "(v = v\<^sup>2 * t / (2 * d - 2 * x)) \<longleftrightarrow> (v * t - v\<^sup>2 * t\<^sup>2 / (4 * d - 4 * x) + x = d)"
proof
  assume "v = v\<^sup>2 * t / (2 * d - 2 * x)"
  hence "v * t = 2 * (d - x)"
    using assms by (simp add: eq_divide_eq power2_eq_square) 
  hence "v * t - v\<^sup>2 * t\<^sup>2 / (4 * d - 4 * x) + x = 2 * (d - x) - 4 * (d - x)\<^sup>2 / (4 * (d - x)) + x"
    apply(subst power_mult_distrib[symmetric])
    by (erule ssubst, subst power_mult_distrib, simp)
  also have "... = d"
    apply(simp only: mult_divide_mult_cancel_left_if)
    using assms by (auto simp: power2_eq_square)
  finally show "v * t - v\<^sup>2 * t\<^sup>2 / (4 * d - 4 * x) + x = d" .
next
  assume "v * t - v\<^sup>2 * t\<^sup>2 / (4 * d - 4 * x) + x = d"
  hence "0 = v\<^sup>2 * t\<^sup>2 / (4 * (d - x)) + (d - x) - v * t"
    by auto
  hence "0 = (4 * (d - x)) * (v\<^sup>2 * t\<^sup>2 / (4 * (d - x)) + (d - x) - v * t)"
    by auto
  also have "... = v\<^sup>2 * t\<^sup>2 + 4 * (d - x)\<^sup>2  - (4 * (d - x)) * (v * t)"
    using assms apply(simp add: distrib_left right_diff_distrib)
    apply(subst right_diff_distrib[symmetric])+
    by (simp add: power2_eq_square)
  also have "... = (v * t - 2 * (d - x))\<^sup>2"
    by (simp only: power2_diff, auto simp: field_simps power2_diff)
  finally have "0 = (v * t - 2 * (d - x))\<^sup>2" .
  hence "v * t = 2 * (d - x)"
    by auto
  thus "v = v\<^sup>2 * t / (2 * d - 2 * x)"
    apply(subst power2_eq_square, subst mult.assoc)
    apply(erule ssubst, subst right_diff_distrib[symmetric])
    using assms by auto
qed

lemma docking_station:
  assumes "d > x\<^sub>0" and "v\<^sub>0 > 0"
  shows "PRE (\<lambda>s. s$1 = x\<^sub>0 \<and> s$2 = v\<^sub>0)
  HP ((3 ::= (\<lambda>s. -(v\<^sub>0^2/(2*(d-x\<^sub>0))))); x\<acute>=(*\<^sub>V) K & G)
  POST (\<lambda>s. s$2 = 0 \<longleftrightarrow> s$1 = d)"
  apply(clarsimp simp: le_fun_def local_flow.fbox_g_ode[OF local_flow_sq_mtx_linear[of K]])
  unfolding exp_mtx_cnst_acc_vec_mult_eq using assms by (simp add: docking_station_arith)

no_notation mtx_cnst_acc ("K")

end