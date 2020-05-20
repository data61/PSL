(*  Title:       Executable multivariate polynomials
    Author:      Christian Sternagel <christian.sternagel@uibk.ac.at>
                 Rene Thiemann       <rene.thiemann@uibk.ac.at>
    Maintainer:  Christian Sternagel and Rene Thiemann
    License:     LGPL
*)

(*
Copyright 2009 Christian Sternagel, René Thiemann, Sarah Winkler, Harald Zankl

This file is part of IsaFoR/CeTA.

IsaFoR/CeTA is free software: you can redistribute it and/or modify it under the
terms of the GNU Lesser General Public License as published by the Free Software
Foundation, either version 3 of the License, or (at your option) any later
version.

IsaFoR/CeTA is distributed in the hope that it will be useful, but WITHOUT ANY
WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A
PARTICULAR PURPOSE.  See the GNU Lesser General Public License for more details.

You should have received a copy of the GNU Lesser General Public License along
with IsaFoR/CeTA. If not, see <http://www.gnu.org/licenses/>.
*)

section \<open>Monotonicity criteria of Neurauter, Zankl, and Middeldorp\<close>

theory NZM
imports "Abstract-Rewriting.SN_Order_Carrier" Polynomials
begin

text \<open>
We show that our check on monotonicity is strong enough to capture the 
exact criterion for polynomials of degree 2 that is presented in \cite{NZM10}:
\begin{itemize}
\item $ax^2 + bx + c$ is monotone if $b + a > 0$ and $a \geq 0$
\item $ax^2 + bx + c$ is weakly monotone if $b + a \geq 0$ and $a \geq 0$
\end{itemize}
\<close>

lemma var_monom_x_x [simp]: "var_monom x * var_monom x \<noteq> 1" 
  by (unfold eq_monom_sum_var, auto simp: sum_var_monom_mult sum_var_monom_var)

lemma monom_list_x_x[simp]: "monom_list (var_monom x * var_monom x) = [(x,2)]"
  by (transfer, auto simp: monom_mult_list.simps)

lemma assumes b: "b + a > 0" and a: "(a :: int) \<ge> 0"
  shows "check_poly_strict_mono_discrete (>) (poly_of (PSum [PNum c, PMult [PNum b, PVar x], PMult [PNum a, PVar x, PVar x]])) x"
proof -
  note [simp] = poly_add.simps poly_mult.simps monom_mult_poly.simps zero_poly_def one_poly_def 
    extract_def check_poly_strict_mono_discrete_def poly_subst.simps monom_subst_def poly_power.simps
    check_poly_gt_def poly_split_def check_poly_ge.simps
  show ?thesis
  proof (cases "a = 0")
    case True
    with b have b: "b > 0 \<and> b \<noteq> 0" by auto
    show ?thesis using b True by simp
  next
    case False
    have [simp]: "2 = Suc (Suc 0)" by simp
    show ?thesis using False a b by simp
  qed
qed

lemma assumes b: "b + a \<ge> 0" and a: "(a :: int) \<ge> 0" 
  shows "check_poly_weak_mono_discrete (poly_of (PSum [PNum c, PMult [PNum b, PVar x], PMult [PNum a, PVar x, PVar x]])) x"
proof -
  note [simp] = poly_add.simps poly_mult.simps monom_mult_poly.simps zero_poly_def one_poly_def 
    extract_def check_poly_weak_mono_discrete_def poly_subst.simps monom_subst_def poly_power.simps
    check_poly_gt_def poly_split_def check_poly_ge.simps
  show ?thesis
  proof (cases "a = 0")
    case True
    with b have b: "0 \<le> b" by auto
    show ?thesis using b True by simp
  next
    case False
    have [simp]: "2 = Suc (Suc 0)" by simp
    show ?thesis using False a b by simp
  qed
qed

end
