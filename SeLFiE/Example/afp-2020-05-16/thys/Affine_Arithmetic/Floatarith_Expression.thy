section \<open>Operations on Expressions\<close>
theory Floatarith_Expression
imports
  "HOL-Decision_Procs.Approximation"
  Affine_Arithmetic_Auxiliarities
  Executable_Euclidean_Space
begin

text \<open>Much of this could move to the distribution...\<close>

subsection \<open>Approximating Expression*s*\<close>

unbundle floatarith_notation

text \<open>\label{sec:affineexpr}\<close>

primrec interpret_floatariths :: "floatarith list \<Rightarrow> real list \<Rightarrow> real list"
where
    "interpret_floatariths [] vs = []"
  | "interpret_floatariths (a#bs) vs = interpret_floatarith a vs#interpret_floatariths bs vs"

lemma length_interpret_floatariths[simp]: "length (interpret_floatariths fas xs) = length fas"
  by (induction fas) auto

lemma interpret_floatariths_nth[simp]:
  "interpret_floatariths fas xs ! n = interpret_floatarith (fas ! n) xs"
  if "n < length fas"
  using that
  by (induction fas arbitrary: n) (auto simp: nth_Cons split: nat.splits)

abbreviation "einterpret \<equiv> \<lambda>fas vs. eucl_of_list (interpret_floatariths fas vs)"

subsection \<open>Syntax\<close>

syntax interpret_floatarith::"floatarith \<Rightarrow> real list \<Rightarrow> real"

instantiation floatarith :: "{plus, minus, uminus, times, inverse, zero, one}"
begin

definition "- f = Minus f"
lemma interpret_floatarith_uminus[simp]:
  "interpret_floatarith (- f) xs = - interpret_floatarith f xs"
  by (auto simp: uminus_floatarith_def)

definition "f + g = Add f g"
lemma interpret_floatarith_plus[simp]:
  "interpret_floatarith (f + g) xs = interpret_floatarith f xs + interpret_floatarith g xs"
  by (auto simp: plus_floatarith_def)

definition "f - g = Add f (Minus g)"
lemma interpret_floatarith_minus[simp]:
  "interpret_floatarith (f - g) xs = interpret_floatarith f xs - interpret_floatarith g xs"
  by (auto simp: minus_floatarith_def)

definition "inverse f = Inverse f"
lemma interpret_floatarith_inverse[simp]:
  "interpret_floatarith (inverse f) xs = inverse (interpret_floatarith f xs)"
  by (auto simp: inverse_floatarith_def)

definition "f * g = Mult f g"
lemma interpret_floatarith_times[simp]:
  "interpret_floatarith (f * g) xs = interpret_floatarith f xs * interpret_floatarith g xs"
  by (auto simp: times_floatarith_def)

definition "f div g = f * Inverse g"
lemma interpret_floatarith_divide[simp]:
  "interpret_floatarith (f div g) xs = interpret_floatarith f xs / interpret_floatarith g xs"
  by (auto simp: divide_floatarith_def inverse_eq_divide)

definition "1 = Num 1"
lemma interpret_floatarith_one[simp]:
  "interpret_floatarith 1 xs = 1"
  by (auto simp: one_floatarith_def)

definition "0 = Num 0"
lemma interpret_floatarith_zero[simp]:
  "interpret_floatarith 0 xs = 0"
  by (auto simp: zero_floatarith_def)

instance proof qed
end


subsection \<open>Derived symbols\<close>

definition "R\<^sub>e r = (case quotient_of r of (n, d) \<Rightarrow> Num (of_int n) / Num (of_int d))"
declare [[coercion R\<^sub>e ]]

lemma interpret_R\<^sub>e[simp]: "interpret_floatarith (R\<^sub>e x) xs = real_of_rat x"
  by (auto simp: R\<^sub>e_def of_rat_divide dest!: quotient_of_div split: prod.splits)

definition "Sin x = Cos ((Pi * (Num (Float 1 (-1)))) - x)"

lemma interpret_floatarith_Sin[simp]:
  "interpret_floatarith (Sin x) vs = sin (interpret_floatarith x vs)"
  by (auto simp: Sin_def approximation_preproc_floatarith(11))

definition "Half x = Mult (Num (Float 1 (-1))) x"
lemma interpret_Half[simp]: "interpret_floatarith (Half x) xs = interpret_floatarith x xs / 2"
  by (auto simp: Half_def)

definition "Tan x = (Sin x) / (Cos x)"

lemma interpret_floatarith_Tan[simp]:
  "interpret_floatarith (Tan x) vs = tan (interpret_floatarith x vs)"
  by (auto simp: Tan_def approximation_preproc_floatarith(12) inverse_eq_divide)

primrec Sum\<^sub>e where
  "Sum\<^sub>e f [] = 0"
| "Sum\<^sub>e f (x#xs) = f x + Sum\<^sub>e f xs" 

lemma interpret_floatarith_Sum\<^sub>e[simp]:
  "interpret_floatarith (Sum\<^sub>e f x) vs = (\<Sum>i\<leftarrow>x. interpret_floatarith (f i) vs)"
  by (induction x) auto

definition Norm where "Norm is = Sqrt (Sum\<^sub>e (\<lambda>i. i * i) is)"

lemma interpret_floatarith_norm[simp]:
  assumes [simp]: "length x = DIM('a)"
  shows "interpret_floatarith (Norm x) vs = norm (einterpret x vs::'a::executable_euclidean_space)"
  apply (auto simp: Norm_def norm_eq_sqrt_inner)
  apply (subst euclidean_inner[where 'a='a])
  apply (auto simp: power2_eq_square[symmetric] )
  apply (subst sum_list_Basis_list[symmetric])
  apply (rule sum_list_nth_eqI)
  by (auto simp: in_set_zip eucl_of_list_inner)

notation floatarith.Power (infixr "^\<^sub>e" 80)

subsection \<open>Constant Folding\<close>

fun dest_Num_fa where
  "dest_Num_fa (floatarith.Num x) = Some x"
| "dest_Num_fa _ = None"

fun_cases dest_Num_fa_None: "dest_Num_fa fa = None"
  and dest_Num_fa_Some: "dest_Num_fa fa = Some x"

fun fold_const_fa where
  "fold_const_fa (Add fa1 fa2) =
    (let (ffa1, ffa2) = (fold_const_fa fa1, fold_const_fa fa2)
    in case (dest_Num_fa ffa1, dest_Num_fa (ffa2)) of
      (Some a, Some b) \<Rightarrow> Num (a + b)
    | (Some a, None) \<Rightarrow> (if a = 0 then ffa2 else Add (Num a) ffa2)
    | (None, Some a) \<Rightarrow> (if a = 0 then ffa1 else Add ffa1 (Num a))
    | (None, None) \<Rightarrow> Add ffa1 ffa2)"
| "fold_const_fa (Minus a) =
    (case (fold_const_fa a) of
      (Num x) \<Rightarrow> Num (-x)
    | x \<Rightarrow> Minus x)"
| "fold_const_fa (Mult fa1 fa2) =
    (let (ffa1, ffa2) = (fold_const_fa fa1, fold_const_fa fa2)
  in case (dest_Num_fa ffa1, dest_Num_fa (ffa2)) of
    (Some a, Some b) \<Rightarrow> Num (a * b)
  | (Some a, None) \<Rightarrow> (if a = 0 then Num 0 else if a = 1 then ffa2 else Mult (Num a) ffa2)
  | (None, Some a) \<Rightarrow> (if a = 0 then Num 0 else if a = 1 then ffa1 else Mult ffa1 (Num a))
  | (None, None) \<Rightarrow> Mult ffa1 ffa2)"
| "fold_const_fa (Inverse a) = Inverse (fold_const_fa a)"
| "fold_const_fa (Abs a) =
    (case (fold_const_fa a) of
      (Num x) \<Rightarrow> Num (abs x)
    | x \<Rightarrow> Abs x)"
| "fold_const_fa (Max a b) =
    (case (fold_const_fa a, fold_const_fa b) of
      (Num x, Num y) \<Rightarrow> Num (max x y)
    | (x, y) \<Rightarrow> Max x y)"
| "fold_const_fa (Min a b) =
    (case (fold_const_fa a, fold_const_fa b) of
      (Num x, Num y) \<Rightarrow> Num (min x y)
    | (x, y) \<Rightarrow> Min x y)"
| "fold_const_fa (Floor a) =
    (case (fold_const_fa a) of
      (Num x) \<Rightarrow> Num (floor_fl x)
    | x \<Rightarrow> Floor x)"
| "fold_const_fa (Power a b) =
    (case (fold_const_fa a) of
      (Num x) \<Rightarrow> Num (x ^ b)
    | x \<Rightarrow> Power x b)"
| "fold_const_fa (Cos a) = Cos (fold_const_fa a)"
| "fold_const_fa (Arctan a) = Arctan (fold_const_fa a)"
| "fold_const_fa (Sqrt a) = Sqrt (fold_const_fa a)"
| "fold_const_fa (Exp a) = Exp (fold_const_fa a)"
| "fold_const_fa (Ln a) = Ln (fold_const_fa a)"
| "fold_const_fa (Powr a b) = Powr (fold_const_fa a) (fold_const_fa b)"
| "fold_const_fa Pi = Pi"
| "fold_const_fa (Var v) = Var v"
| "fold_const_fa (Num x) = Num x"

fun_cases fold_const_fa_Num: "fold_const_fa fa = Num y"
  and fold_const_fa_Add: "fold_const_fa fa = Add x y"
  and fold_const_fa_Minus: "fold_const_fa fa = Minus y"

lemma fold_const_fa[simp]: "interpret_floatarith (fold_const_fa fa) xs = interpret_floatarith fa xs"
  by (induction fa) (auto split!: prod.splits floatarith.splits option.splits
      elim!: dest_Num_fa_None dest_Num_fa_Some
      simp: max_def min_def floor_fl_def)


subsection \<open>Free Variables\<close>

primrec max_Var_floatarith where\<comment> \<open>TODO: include bound in predicate\<close>
  "max_Var_floatarith (Add a b) = max (max_Var_floatarith a) (max_Var_floatarith b)"
| "max_Var_floatarith (Mult a b) = max (max_Var_floatarith a) (max_Var_floatarith b)"
| "max_Var_floatarith (Inverse a) = max_Var_floatarith a"
| "max_Var_floatarith (Minus a) = max_Var_floatarith a"
| "max_Var_floatarith (Num a) = 0"
| "max_Var_floatarith (Var i) = Suc i"
| "max_Var_floatarith (Cos a) = max_Var_floatarith a"
| "max_Var_floatarith (floatarith.Arctan a) = max_Var_floatarith a"
| "max_Var_floatarith (Abs a) = max_Var_floatarith a"
| "max_Var_floatarith (floatarith.Max a b) = max (max_Var_floatarith a) (max_Var_floatarith b)"
| "max_Var_floatarith (floatarith.Min a b) = max (max_Var_floatarith a) (max_Var_floatarith b)"
| "max_Var_floatarith (floatarith.Pi) = 0"
| "max_Var_floatarith (Sqrt a) = max_Var_floatarith a"
| "max_Var_floatarith (Exp a) = max_Var_floatarith a"
| "max_Var_floatarith (Powr a b) = max (max_Var_floatarith a) (max_Var_floatarith b)"
| "max_Var_floatarith (floatarith.Ln a) = max_Var_floatarith a"
| "max_Var_floatarith (Power a n) = max_Var_floatarith a"
| "max_Var_floatarith (Floor a) = max_Var_floatarith a"       
  
primrec max_Var_floatariths where
  "max_Var_floatariths [] = 0"
| "max_Var_floatariths (x#xs) = max (max_Var_floatarith x) (max_Var_floatariths xs)"

primrec max_Var_form where
  "max_Var_form (Conj a b) = max (max_Var_form a) (max_Var_form b)"
|  "max_Var_form (Disj a b) = max (max_Var_form a) (max_Var_form b)"
|  "max_Var_form (Less a b) = max (max_Var_floatarith a) (max_Var_floatarith b)"
|  "max_Var_form (LessEqual a b) = max (max_Var_floatarith a) (max_Var_floatarith b)"
|  "max_Var_form (Bound a b c d) = linorder_class.Max {max_Var_floatarith a,max_Var_floatarith b, max_Var_floatarith c, max_Var_form d}"
|  "max_Var_form (AtLeastAtMost a b c) = linorder_class.Max {max_Var_floatarith a,max_Var_floatarith b, max_Var_floatarith c}"
|  "max_Var_form (Assign a b c) = linorder_class.Max {max_Var_floatarith a,max_Var_floatarith b, max_Var_form c}"

lemma
  interpret_floatarith_eq_take_max_VarI:
  assumes "take (max_Var_floatarith ra) ys = take (max_Var_floatarith ra) zs"
  shows "interpret_floatarith ra ys = interpret_floatarith ra zs"
  using assms
  by (induct ra) (auto dest!: take_max_eqD simp: take_Suc_eq split: if_split_asm)

lemma
  interpret_floatariths_eq_take_max_VarI:
  assumes "take (max_Var_floatariths ea) ys = take (max_Var_floatariths ea) zs"
  shows "interpret_floatariths ea ys = interpret_floatariths ea zs"
  using assms
  apply (induction ea)
  subgoal by simp
  subgoal by (clarsimp) (metis interpret_floatarith_eq_take_max_VarI take_map take_max_eqD)
  done


lemma Max_Image_distrib:
  includes no_floatarith_notation
  assumes "finite X" "X \<noteq> {}"
  shows "Max ((\<lambda>x. max (f1 x) (f2 x)) ` X) = max (Max (f1 ` X)) (Max (f2 ` X))"
  apply (rule Max_eqI)
  subgoal using assms by simp
  subgoal for y
    using assms
    by (force intro: max.coboundedI1 max.coboundedI2 Max_ge)
  subgoal
  proof -
    have "Max (f1 ` X) \<in> f1 ` X" using assms by auto
    then obtain x1 where x1: "x1 \<in> X" "Max (f1 ` X) = f1 x1" by auto
    have "Max (f2 ` X) \<in> f2 ` X" using assms by auto
    then obtain x2 where x2: "x2 \<in> X" "Max (f2 ` X) = f2 x2" by auto
    show ?thesis
      apply (rule image_eqI[where x="if f1 x1 \<le> f2 x2 then x2 else x1"])
      using x1 x2 assms
       apply (auto simp: max_def)
       apply (metis Max_ge dual_order.trans finite_imageI image_eqI assms(1))
      apply (metis Max_ge dual_order.trans finite_imageI image_eqI assms(1))
      done
  qed
  done

lemma max_Var_floatarith_simps[simp]:
  "max_Var_floatarith (a / b) = max (max_Var_floatarith a) (max_Var_floatarith b)"
  "max_Var_floatarith (a * b) = max (max_Var_floatarith a) (max_Var_floatarith b)"
  "max_Var_floatarith (a + b) = max (max_Var_floatarith a) (max_Var_floatarith b)"
  "max_Var_floatarith (a - b) = max (max_Var_floatarith a) (max_Var_floatarith b)"
  "max_Var_floatarith (- b) = (max_Var_floatarith b)"
  by (auto simp: divide_floatarith_def times_floatarith_def plus_floatarith_def minus_floatarith_def
      uminus_floatarith_def)

lemma max_Var_floatariths_Max:
  "max_Var_floatariths xs = (if set xs = {} then 0 else linorder_class.Max (max_Var_floatarith ` set xs))"
  by (induct xs) auto


lemma max_Var_floatariths_map_plus[simp]:
  "max_Var_floatariths (map (\<lambda>i. fa1 i + fa2 i) xs) = max (max_Var_floatariths (map fa1 xs)) (max_Var_floatariths (map fa2 xs))"
  by (auto simp: max_Var_floatariths_Max image_image Max_Image_distrib)

lemma max_Var_floatariths_map_times[simp]:
  "max_Var_floatariths (map (\<lambda>i. fa1 i * fa2 i) xs) = max (max_Var_floatariths (map fa1 xs)) (max_Var_floatariths (map fa2 xs))"
  by (auto simp: max_Var_floatariths_Max image_image Max_Image_distrib)

lemma max_Var_floatariths_map_divide[simp]:
  "max_Var_floatariths (map (\<lambda>i. fa1 i / fa2 i) xs) = max (max_Var_floatariths (map fa1 xs)) (max_Var_floatariths (map fa2 xs))"
  by (auto simp: max_Var_floatariths_Max image_image Max_Image_distrib)

lemma max_Var_floatariths_map_uminus[simp]:
  "max_Var_floatariths (map (\<lambda>i. - fa1 i) xs) = max_Var_floatariths (map fa1 xs)"
  by (auto simp: max_Var_floatariths_Max image_image Max_Image_distrib)

lemma max_Var_floatariths_map_const[simp]:
  "max_Var_floatariths (map (\<lambda>i. fa) xs) = (if xs = [] then 0 else max_Var_floatarith fa)"
  by (auto simp: max_Var_floatariths_Max image_image image_constant_conv)

lemma max_Var_floatariths_map_minus[simp]:
  "max_Var_floatariths (map (\<lambda>i. fa1 i - fa2 i) xs) = max (max_Var_floatariths (map fa1 xs)) (max_Var_floatariths (map fa2 xs))"
  by (auto simp: max_Var_floatariths_Max image_image Max_Image_distrib)


primrec fresh_floatarith where
  "fresh_floatarith (Var y) x \<longleftrightarrow> (x \<noteq> y)"
| "fresh_floatarith (Num a) x \<longleftrightarrow> True"
| "fresh_floatarith Pi x \<longleftrightarrow> True"
| "fresh_floatarith (Cos a) x \<longleftrightarrow> fresh_floatarith a x"
| "fresh_floatarith (Abs a) x \<longleftrightarrow> fresh_floatarith a x"
| "fresh_floatarith (Arctan a) x \<longleftrightarrow> fresh_floatarith a x"
| "fresh_floatarith (Sqrt a) x \<longleftrightarrow> fresh_floatarith a x"
| "fresh_floatarith (Exp a) x \<longleftrightarrow> fresh_floatarith a x"
| "fresh_floatarith (Floor a) x \<longleftrightarrow> fresh_floatarith a x"
| "fresh_floatarith (Power a n) x \<longleftrightarrow> fresh_floatarith a x"
| "fresh_floatarith (Minus a) x \<longleftrightarrow> fresh_floatarith a x"
| "fresh_floatarith (Ln a) x \<longleftrightarrow> fresh_floatarith a x"
| "fresh_floatarith (Inverse a) x \<longleftrightarrow> fresh_floatarith a x"
| "fresh_floatarith (Add a b) x \<longleftrightarrow> fresh_floatarith a x \<and> fresh_floatarith b x"
| "fresh_floatarith (Mult a b) x \<longleftrightarrow> fresh_floatarith a x \<and> fresh_floatarith b x"
| "fresh_floatarith (Max a b) x \<longleftrightarrow> fresh_floatarith a x \<and> fresh_floatarith b x"
| "fresh_floatarith (Min a b) x \<longleftrightarrow> fresh_floatarith a x \<and> fresh_floatarith b x"
| "fresh_floatarith (Powr a b) x \<longleftrightarrow> fresh_floatarith a x \<and> fresh_floatarith b x"

lemma fresh_floatarith_subst:
  fixes v::float
  assumes "fresh_floatarith e x"
  assumes "x < length vs"
  shows "interpret_floatarith e (vs[x:=v]) = interpret_floatarith e vs"
  using assms
  by (induction e) (auto simp: map_update)

lemma fresh_floatarith_max_Var:
  assumes "max_Var_floatarith ea \<le> i"
  shows "fresh_floatarith ea i"
  using assms
  by (induction ea) auto

primrec fresh_floatariths where
  "fresh_floatariths [] x \<longleftrightarrow> True"
| "fresh_floatariths (a#as) x \<longleftrightarrow> fresh_floatarith a x \<and> fresh_floatariths as x"

lemma fresh_floatariths_max_Var:
  assumes "max_Var_floatariths ea \<le> i"
  shows "fresh_floatariths ea i"
  using assms
  by (induction ea) (auto simp: fresh_floatarith_max_Var)

lemma
  interpret_floatariths_take_eqI:
  assumes "take n ys = take n zs"
  assumes "max_Var_floatariths ea \<le> n"
  shows "interpret_floatariths ea ys = interpret_floatariths ea zs"
  by (rule interpret_floatariths_eq_take_max_VarI) (rule take_greater_eqI[OF assms])

lemma
  interpret_floatarith_fresh_eqI:
  assumes "\<And>i. fresh_floatarith ea i \<or> (i < length ys \<and> i < length zs \<and> ys ! i = zs ! i)"
  shows "interpret_floatarith ea ys = interpret_floatarith ea zs"
  using assms
  by (induction ea) force+

lemma
  interpret_floatariths_fresh_eqI:
  assumes "\<And>i. fresh_floatariths ea i \<or> (i < length ys \<and> i < length zs \<and> ys ! i = zs ! i)"
  shows "interpret_floatariths ea ys = interpret_floatariths ea zs"
  using assms
  apply (induction ea)
  subgoal by (force simp: interpret_floatarith_fresh_eqI intro: interpret_floatarith_fresh_eqI)
  subgoal for e ea
    apply clarsimp
    apply (auto simp: list_eq_iff_nth_eq)
    using interpret_floatarith_fresh_eqI by blast
  done

lemma
  interpret_floatarith_max_Var_cong:
  assumes "\<And>i. i < max_Var_floatarith f \<Longrightarrow> xs ! i = ys ! i"
  shows "interpret_floatarith f ys = interpret_floatarith f xs"
  using assms
  by (induction f) auto

lemma
  interpret_floatarith_fresh_cong:
  assumes "\<And>i. \<not>fresh_floatarith f i \<Longrightarrow> xs ! i = ys ! i"
  shows "interpret_floatarith f ys = interpret_floatarith f xs"
  using assms
  by (induction f) auto

lemma max_Var_floatarith_le_max_Var_floatariths:
  "fa \<in> set fas \<Longrightarrow> max_Var_floatarith fa \<le> max_Var_floatariths fas"
  by (induction fas) (auto simp: nth_Cons max_def split: nat.splits)

lemma max_Var_floatarith_le_max_Var_floatariths_nth:
  "n < length fas \<Longrightarrow> max_Var_floatarith (fas ! n) \<le> max_Var_floatariths fas"
  by (rule max_Var_floatarith_le_max_Var_floatariths) auto

lemma max_Var_floatariths_leI:
  assumes "\<And>i. i < length xs \<Longrightarrow> max_Var_floatarith (xs ! i) \<le> F"
  shows "max_Var_floatariths xs \<le> F"
  using assms
  by (auto simp: max_Var_floatariths_Max in_set_conv_nth)

lemma fresh_floatariths_map_Var[simp]:
  "fresh_floatariths (map floatarith.Var xs) i \<longleftrightarrow> i \<notin> set xs"
  by (induction xs) auto


lemma max_Var_floatarith_fold_const_fa:
  "max_Var_floatarith (fold_const_fa fa) \<le> max_Var_floatarith fa"
  by (induction fa) (auto simp: fold_const_fa.simps split!: option.splits floatarith.splits)

lemma max_Var_floatariths_fold_const_fa:
  "max_Var_floatariths (map fold_const_fa xs) \<le> max_Var_floatariths xs"
  by (auto simp: intro!: max_Var_floatariths_leI max_Var_floatarith_le_max_Var_floatariths_nth
      max_Var_floatarith_fold_const_fa[THEN order_trans])

lemma interpret_form_max_Var_cong:
  assumes "\<And>i. i < max_Var_form f \<Longrightarrow> xs ! i = ys ! i"
  shows "interpret_form f xs = interpret_form f ys"
  using assms
  by (induction f) (auto simp: interpret_floatarith_max_Var_cong[where xs=xs and ys=ys])

lemma max_Var_floatariths_lessI: "i < max_Var_floatarith (fas ! j) \<Longrightarrow> j < length fas \<Longrightarrow> i < max_Var_floatariths fas"
  by (metis leD le_trans less_le max_Var_floatarith_le_max_Var_floatariths nth_mem)

lemma interpret_floatariths_max_Var_cong:
  assumes "\<And>i. i < max_Var_floatariths f \<Longrightarrow> xs ! i = ys ! i"
  shows "interpret_floatariths f ys = interpret_floatariths f xs"
  by (auto intro!: nth_equalityI interpret_floatarith_max_Var_cong assms max_Var_floatariths_lessI)


lemma max_Var_floatarithimage_Var[simp]: "max_Var_floatarith ` Var ` X = Suc ` X" by force

lemma max_Var_floatariths_map_Var[simp]:
  "max_Var_floatariths (map Var xs) = (if xs = [] then 0 else Suc (linorder_class.Max (set xs)))"
  by (auto simp: max_Var_floatariths_Max hom_Max_commute split: if_splits)

lemma Max_atLeastLessThan_nat[simp]: "a < b \<Longrightarrow> linorder_class.Max {a..<b} = b - 1" for a b::nat
  by (auto intro!: Max_eqI)


subsection \<open>Derivatives\<close>

lemma isDERIV_Power_iff: "isDERIV j (Power fa n) xs = (if n = 0 then True else isDERIV j fa xs)"
  by (cases n) auto

lemma isDERIV_max_Var_floatarithI:
  assumes "isDERIV n f ys"
  assumes "\<And>i. i < max_Var_floatarith f \<Longrightarrow> xs ! i = ys ! i"
  shows "isDERIV n f xs"
  using assms
proof (induction f)
  case (Power f n) then show ?case by (cases n) auto
qed (auto simp: max_def interpret_floatarith_max_Var_cong[of _ xs ys] split: if_splits)

definition isFDERIV where "isFDERIV n xs fas vs \<longleftrightarrow>
  (\<forall>i<n. \<forall>j<n. isDERIV (xs ! i) (fas ! j) vs) \<and> length fas = n \<and> length xs = n"

lemma isFDERIV_I: "(\<And>i j. i < n \<Longrightarrow> j < n \<Longrightarrow> isDERIV (xs ! i) (fas ! j) vs) \<Longrightarrow>
  length fas = n \<Longrightarrow> length xs = n \<Longrightarrow> isFDERIV n xs fas vs"
  by (auto simp: isFDERIV_def)

lemma isFDERIV_isDERIV_D: "isFDERIV n xs fas vs \<Longrightarrow> i < n \<Longrightarrow> j < n \<Longrightarrow> isDERIV (xs ! i) (fas ! j) vs"
  by (auto simp: isFDERIV_def)

lemma isFDERIV_lengthD: "length fas = n" "length xs = n" if "isFDERIV n xs fas vs"
  using that by (auto simp: isFDERIV_def)

lemma isFDERIV_uptD: "isFDERIV n [0..<n] fas vs \<Longrightarrow> i < n \<Longrightarrow> j < n \<Longrightarrow> isDERIV i (fas ! j) vs"
  by (auto simp: isFDERIV_def)

lemma isFDERIV_max_Var_congI: "isFDERIV n xs fas ws"
  if f: "isFDERIV n xs fas vs" and c: "(\<And>i. i < max_Var_floatariths fas \<Longrightarrow> vs ! i = ws ! i)"
  using c f
  by (auto simp: isFDERIV_def max_Var_floatariths_lessI
      intro!: isFDERIV_I isDERIV_max_Var_floatarithI[OF isFDERIV_isDERIV_D[OF f]])

lemma isFDERIV_max_Var_cong: "isFDERIV n xs fas ws \<longleftrightarrow> isFDERIV n xs fas vs"
  if c: "(\<And>i. i < max_Var_floatariths fas \<Longrightarrow> vs ! i = ws ! i)"
  using c by (auto intro: isFDERIV_max_Var_congI)

lemma isDERIV_max_VarI:
  "i \<ge> max_Var_floatarith fa \<Longrightarrow> isDERIV j fa xs \<Longrightarrow> isDERIV i fa xs"
  by (induction fa) (auto simp: isDERIV_Power_iff)

lemmas max_Var_floatarith_le_max_Var_floatariths_nthI =
  max_Var_floatarith_le_max_Var_floatariths_nth[THEN order_trans]


lemma
  isFDERIV_appendD1:
  assumes "isFDERIV (J + K) [0..<J + K] (es @ rs) xs"
  assumes "length es = J"
  assumes "length rs = K"
  assumes "max_Var_floatariths es \<le> J"
  shows "isFDERIV J [0..<J] (es) xs"
  unfolding isFDERIV_def
  apply (safe)
  subgoal for i j
    using assms
    apply (cases "i < length es")
    subgoal by (auto simp: nth_append isFDERIV_def) (metis add.commute trans_less_add2)
    subgoal
      apply (rule isDERIV_max_VarI[where j=0])
       apply (rule max_Var_floatarith_le_max_Var_floatariths_nthI)
         apply force
        apply force
       apply force
      done
    done
  subgoal by (auto simp: assms)
  subgoal by (auto simp: assms)
  done

lemma interpret_floatariths_Var[simp]:
  "interpret_floatariths (map floatarith.Var xs) vs = (map (nth vs) xs)"
  by (induction xs) (auto simp: )

lemma max_Var_floatariths_append[simp]: "max_Var_floatariths (xs @ ys) = max (max_Var_floatariths xs) (max_Var_floatariths ys)"
  by (induction xs) (auto)

lemma map_nth_append_upt[simp]:
  assumes "a \<ge> length xs"
  shows "map ((!) (xs @ ys)) [a..<b] = map ((!) ys) [a - length xs..<b - length xs]"
  using assms
  by (auto intro!: nth_equalityI simp: nth_append)

lemma map_nth_Cons_upt[simp]:
  assumes "a > 0"
  shows "map ((!) (x # ys)) [a..<b] = map ((!) ys) [a - Suc 0..<b - Suc 0]"
  using assms
  by (auto intro!: nth_equalityI simp: nth_append)

lemma map_nth_eq_self[simp]:
  shows "length fas = l \<Longrightarrow> (map ((!) fas) [0..<l]) = fas"
  by (auto simp: intro!: nth_equalityI)


lemma
  isFDERIV_appendI1:
  assumes "isFDERIV J [0..<J] (es) xs"
  assumes "\<And>i j. i < J + K \<Longrightarrow> j < K \<Longrightarrow> isDERIV i (rs ! j) xs"
  assumes "length es = J"
  assumes "length rs = K"
  assumes "max_Var_floatariths es \<le> J"
  shows "isFDERIV (J + K) [0..<J + K] (es @ rs) xs"
  unfolding isFDERIV_def
  apply safe
  subgoal for i j
    using assms
    apply (cases "j < length es")
    subgoal
      apply (auto simp: nth_append isFDERIV_def)
      by (metis (no_types, hide_lams) isDERIV_max_VarI le_trans less_le
          max_Var_floatarith_le_max_Var_floatariths_nthI nat_le_linear)
    subgoal by (auto simp: nth_append)
    done
  subgoal by (auto simp: assms)
  subgoal by (auto simp: assms)
  done


lemma matrix_matrix_mult_zero[simp]:
  "a ** 0 = 0" "0 ** a = 0"
  by (vector matrix_matrix_mult_def)+

lemma scaleR_blinfun_compose_left: "i *\<^sub>R (A o\<^sub>L B) = i *\<^sub>R A o\<^sub>L B"
  and scaleR_blinfun_compose_right: "i *\<^sub>R (A o\<^sub>L B) = A o\<^sub>L i *\<^sub>R B"
  by (auto intro!: blinfun_eqI simp: blinfun.bilinear_simps)

lemma
  matrix_blinfun_compose:
  fixes A B::"(real ^ 'n) \<Rightarrow>\<^sub>L (real ^ 'n)"
  shows "matrix (A o\<^sub>L B) = (matrix A) ** (matrix B)"
  by transfer (auto simp: matrix_compose linear_linear)

lemma matrix_add_rdistrib: "((B + C) ** A) = (B ** A) + (C ** A)"
  by (vector matrix_matrix_mult_def sum.distrib[symmetric] field_simps)

lemma matrix_scaleR_right: "r *\<^sub>R (a::'a::real_algebra_1^'n^'m) ** b = r *\<^sub>R (a ** b)"
  by (vector matrix_matrix_mult_def algebra_simps scaleR_sum_right)

lemma matrix_scaleR_left: "(a::'a::real_algebra_1^'n^'m) ** r *\<^sub>R b = r *\<^sub>R (a ** b)"
  by (vector matrix_matrix_mult_def algebra_simps scaleR_sum_right)

lemma bounded_bilinear_matrix_matrix_mult[bounded_bilinear]:
   "bounded_bilinear ((**)::
    ('a::{euclidean_space, real_normed_algebra_1}^'n^'m) \<Rightarrow>
    ('a::{euclidean_space, real_normed_algebra_1}^'p^'n) \<Rightarrow>
    ('a::{euclidean_space, real_normed_algebra_1}^'p^'m))"
  unfolding bilinear_conv_bounded_bilinear[symmetric]
  unfolding bilinear_def
  apply safe
  by unfold_locales (auto simp: matrix_add_ldistrib matrix_add_rdistrib matrix_scaleR_right matrix_scaleR_left)

lemma norm_axis: "norm (axis ia 1::'a::{real_normed_algebra_1}^'n) = 1"
  by (auto simp: axis_def norm_vec_def L2_set_def if_distrib if_distribR sum.delta
      cong: if_cong)

lemma abs_vec_nth_blinfun_apply_lemma:
  fixes x::"(real^'n) \<Rightarrow>\<^sub>L (real^'m)"
  shows "abs (vec_nth (blinfun_apply x (axis ia 1)) i) \<le> norm x"
  apply (rule component_le_norm_cart[THEN order_trans])
  apply (rule norm_blinfun[THEN order_trans])
  by (auto simp: norm_axis)

lemma bounded_linear_matrix_blinfun_apply: "bounded_linear (\<lambda>x::(real^'n) \<Rightarrow>\<^sub>L (real^'m). matrix (blinfun_apply x))"
  apply standard
  subgoal by (vector blinfun.bilinear_simps matrix_def)
  subgoal by (vector blinfun.bilinear_simps matrix_def)
  apply (rule exI[where x="real (CARD('n) * CARD('m))"])
  apply (auto simp: matrix_def)
  apply (subst norm_vec_def)
  apply (rule L2_set_le_sum[THEN order_trans])
  apply simp
  apply auto
  apply (rule sum_mono[THEN order_trans])
  apply (subst norm_vec_def)
   apply (rule L2_set_le_sum)
   apply simp
  apply (rule sum_mono[THEN order_trans])
   apply (rule sum_mono)
    apply simp
    apply (rule abs_vec_nth_blinfun_apply_lemma)
  apply (simp add: abs_vec_nth_blinfun_apply_lemma)
  done

lemma matrix_has_derivative:
  shows "((\<lambda>x::(real^'n)\<Rightarrow>\<^sub>L(real^'n). matrix (blinfun_apply x)) has_derivative (\<lambda>h. matrix (blinfun_apply h))) (at x)"
  apply (auto simp: has_derivative_at2)
  unfolding linear_linear
  subgoal by (rule bounded_linear_matrix_blinfun_apply)
  subgoal
    by (auto simp: blinfun.bilinear_simps matrix_def) vector
  done

lemma
  matrix_comp_has_derivative[derivative_intros]:
  fixes f::"'a::real_normed_vector \<Rightarrow> ((real^'n)\<Rightarrow>\<^sub>L(real^'n))"
  assumes "(f has_derivative f') (at x within S)"
  shows "((\<lambda>x. matrix (blinfun_apply (f x))) has_derivative (\<lambda>x. matrix (f' x))) (at x within S)"
  using has_derivative_compose[OF assms matrix_has_derivative]
  by auto

fun inner_floatariths where
  "inner_floatariths [] _ = Num 0"
| "inner_floatariths _ [] = Num 0"
| "inner_floatariths (x#xs) (y#ys) = Add (Mult x y) (inner_floatariths xs ys)"

lemma interpret_floatarith_inner_eq:
  assumes "length xs = length ys"
  shows "interpret_floatarith (inner_floatariths xs ys) vs =
    (\<Sum>i<length ys. (interpret_floatariths xs vs ! i) * (interpret_floatariths ys vs ! i))"
  using assms
proof (induction rule: list_induct2)
  case Nil
  then show ?case by simp
next
  case (Cons x xs y ys)
  then show ?case
    unfolding length_Cons sum.lessThan_Suc_shift
    by simp
qed

lemma
  interpret_floatarith_inner_floatariths:
  assumes "length xs = DIM('a::executable_euclidean_space)"
  assumes "length ys = DIM('a)"
  assumes "eucl_of_list (interpret_floatariths xs vs) = (x::'a)"
  assumes "eucl_of_list (interpret_floatariths ys vs) = y"
  shows "interpret_floatarith (inner_floatariths xs ys) vs = x \<bullet> y"
  using assms
  by (subst euclidean_inner)
    (auto simp: interpret_floatarith_inner_eq sum_Basis_sum_nth_Basis_list eucl_of_list_inner
      index_nth_id
      intro!: euclidean_eqI[where 'a='a] sum.cong)

lemma max_Var_floatarith_inner_floatariths[simp]:
  assumes "length f = length g"
  shows "max_Var_floatarith (inner_floatariths f g) = max (max_Var_floatariths f) (max_Var_floatariths g)"
  using assms
  by (induction f g rule: list_induct2) auto


definition FDERIV_floatarith where
  "FDERIV_floatarith fa xs d = inner_floatariths (map (\<lambda>x. fold_const_fa (DERIV_floatarith x fa)) xs) d"
\<comment> \<open>TODO: specialize to \<open>FDERIV_floatarith fa [0..<n] [m..<m + n]\<close> and do the rest with @{term subst_floatarith}?
   TODO: introduce approximation on type @{typ "real^'i^'j"} and use @{term jacobian}?\<close>

lemma interpret_floatariths_map: "interpret_floatariths (map f xs) vs = map (\<lambda>x. interpret_floatarith (f x) vs) xs"
  by (induct xs) (auto simp: )

lemma max_Var_floatarith_DERIV_floatarith:
  "max_Var_floatarith (DERIV_floatarith x fa) \<le> max_Var_floatarith fa"
  by (induction x fa rule: DERIV_floatarith.induct) (auto)

lemma max_Var_floatarith_FDERIV_floatarith:
  "length xs = length d \<Longrightarrow>
    max_Var_floatarith (FDERIV_floatarith fa xs d) \<le> max (max_Var_floatarith fa) (max_Var_floatariths d)"
  unfolding FDERIV_floatarith_def
  by (auto simp: max_Var_floatariths_Max intro!: max_Var_floatarith_DERIV_floatarith[THEN order_trans]
      max_Var_floatarith_fold_const_fa[THEN order_trans])

definition FDERIV_floatariths where
  "FDERIV_floatariths fas xs d = map (\<lambda>fa. FDERIV_floatarith fa xs d) fas"

lemma max_Var_floatarith_FDERIV_floatariths:
  "length xs = length d \<Longrightarrow> max_Var_floatariths (FDERIV_floatariths fa xs d) \<le> max (max_Var_floatariths fa) (max_Var_floatariths d)"
  by (auto simp: FDERIV_floatariths_def max_Var_floatariths_Max
      intro!: max_Var_floatarith_FDERIV_floatarith[THEN order_trans])
    (auto simp: max_def)

lemma length_FDERIV_floatariths[simp]:
  "length (FDERIV_floatariths fas xs ds) = length fas"
  by (auto simp: FDERIV_floatariths_def)

lemma FDERIV_floatariths_nth[simp]:
  "i < length fas \<Longrightarrow> FDERIV_floatariths fas xs ds ! i  = FDERIV_floatarith (fas ! i) xs ds"
  by (auto simp: FDERIV_floatariths_def)

definition "FDERIV_n_floatariths fas xs ds n = ((\<lambda>x. FDERIV_floatariths x xs ds)^^n) fas"

lemma FDERIV_n_floatariths_Suc[simp]:
  "FDERIV_n_floatariths fa xs ds 0 = fa"
  "FDERIV_n_floatariths fa xs ds (Suc n) = FDERIV_floatariths (FDERIV_n_floatariths fa xs ds n) xs ds"
  by (auto simp: FDERIV_n_floatariths_def)

lemma length_FDERIV_n_floatariths[simp]: "length (FDERIV_n_floatariths fa xs ds n) = length fa"
  by (induction n) (auto simp: FDERIV_n_floatariths_def)

lemma max_Var_floatarith_FDERIV_n_floatariths:
  "length xs = length d \<Longrightarrow> max_Var_floatariths (FDERIV_n_floatariths fa xs d n) \<le> max (max_Var_floatariths fa) (max_Var_floatariths d)"
  by (induction n)
    (auto intro!: max_Var_floatarith_FDERIV_floatariths[THEN order_trans] simp: FDERIV_n_floatariths_def)

lemma interpret_floatarith_FDERIV_floatarith_cong:
  assumes rq: "\<And>i. i < max_Var_floatarith f \<Longrightarrow> rs ! i = qs ! i"
  assumes [simp]: "length ds = length xs" "length es = length xs"
  assumes "interpret_floatariths ds qs = interpret_floatariths es rs"
  shows "interpret_floatarith (FDERIV_floatarith f xs ds) qs =
   interpret_floatarith (FDERIV_floatarith f xs es) rs"
  apply (auto simp: FDERIV_floatarith_def interpret_floatarith_inner_eq)
  apply (rule sum.cong[OF refl])
  subgoal premises prems for i
  proof -
    have "interpret_floatarith (DERIV_floatarith (xs ! i) f) qs = interpret_floatarith (DERIV_floatarith (xs ! i) f) rs"
      apply (rule interpret_floatarith_max_Var_cong)
      apply (auto simp: intro!: rq)
      by (metis leD le_trans max_Var_floatarith_DERIV_floatarith nat_less_le)
    moreover
    have "interpret_floatarith (ds ! i) qs = interpret_floatarith (es ! i) rs"
      using assms
      by (metis \<open>i \<in> {..<length xs}\<close> interpret_floatariths_nth lessThan_iff)
    ultimately show ?thesis by auto
  qed
  done

theorem
  matrix_vector_mult_eq_list_of_eucl_nth:
  "(M::real^'n::enum^'m::enum) *v v =
    (\<Sum>i<CARD('m).
      (\<Sum>j<CARD('n). list_of_eucl M ! (i * CARD('n) + j) * list_of_eucl v ! j) *\<^sub>R Basis_list ! i)"
  using eucl_of_list_matrix_vector_mult_eq_sum_nth_Basis_list[of "list_of_eucl M" "list_of_eucl v",
      where 'n='n and 'm = 'm]
  by auto

definition "mmult_fa l m n AS BS =
  concat (map (\<lambda>i. map (\<lambda>k. inner_floatariths
    (map (\<lambda>j. AS ! (i * m + j)) [0..<m]) (map (\<lambda>j. BS ! (j * n + k)) [0..<m])) [0..<n]) [0..<l])"

lemma length_mmult_fa[simp]: "length (mmult_fa l m n AS BS) = l * n"
  by (auto simp: mmult_fa_def length_concat o_def sum_list_distinct_conv_sum_set)

lemma einterpret_mmult_fa:
  assumes [simp]: "Dn = CARD('n::enum)" "Dm = CARD('m::enum)" "Dl = CARD('l::enum)"
    "length A = CARD('l)*CARD('m)" "length B = CARD('m)*CARD('n)"
  shows "einterpret (mmult_fa Dl Dm Dn A B) vs = (einterpret A vs::((real, 'm::enum) vec, 'l) vec) ** (einterpret B vs::((real, 'n::enum) vec, 'm) vec)"
  apply (vector matrix_matrix_mult_def)
  apply (auto simp: mmult_fa_def vec_nth_eucl_of_list_eq2 index_Basis_list_axis2
      concat_map_map_index length_concat o_def sum_list_distinct_conv_sum_set
      interpret_floatarith_inner_eq)
  apply (subst sum_index_enum_eq)
  apply simp
  done

lemma max_Var_floatariths_mmult_fa:
  assumes [simp]: "length A = D * E" "length B = E * F"
  shows "max_Var_floatariths (mmult_fa D E F A B) \<le> max (max_Var_floatariths A) (max_Var_floatariths B)"
  apply (auto simp: mmult_fa_def concat_map_map_index intro!: max_Var_floatariths_leI)
   apply (rule max.coboundedI1)
   apply (auto intro!: max_Var_floatarith_le_max_Var_floatariths_nth max.coboundedI2)
  apply (cases "F = 0")
   apply simp_all
  done

lemma isDERIV_inner_iff:
  assumes "length xs = length ys"
  shows "isDERIV i (inner_floatariths xs ys) vs \<longleftrightarrow>
    (\<forall>k < length xs. isDERIV i (xs ! k) vs) \<and> (\<forall>k < length ys. isDERIV i (ys ! k) vs)"
  using assms
  by (induction xs ys rule: list_induct2) (auto simp: nth_Cons split: nat.splits)

lemma isDERIV_Power: "isDERIV x (fa) vs \<Longrightarrow> isDERIV x (fa ^\<^sub>e n) vs"
  by (induction n) (auto simp: FDERIV_floatarith_def isDERIV_inner_iff)

lemma isDERIV_mmult_fa_nth:
  assumes "\<And>j. j < D * E \<Longrightarrow> isDERIV i (A ! j) xs"
  assumes "\<And>j. j < E * F \<Longrightarrow> isDERIV i (B ! j) xs"
  assumes [simp]: "length A = D * E" "length B = E * F" "j < D * F"
  shows "isDERIV i (mmult_fa D E F A B ! j) xs"
  using assms
  apply (cases "F = 0")
  apply (auto simp: mmult_fa_def concat_map_map_index isDERIV_inner_iff ac_simps)
  apply (metis add.commute assms(5) in_square_lemma less_square_imp_div_less mult.commute)
  done

definition "mvmult_fa n m AS B =
  map (\<lambda>i. inner_floatariths (map (\<lambda>j. AS ! (i * m + j)) [0..<m]) (map (\<lambda>j. B ! j) [0..<m])) [0..<n]"

lemma einterpret_mvmult_fa:
  assumes [simp]: "Dn = CARD('n::enum)" "Dm = CARD('m::enum)"
    "length A = CARD('n)*CARD('m)" "length B = CARD('m)"
  shows "einterpret (mvmult_fa Dn Dm A B) vs = (einterpret A vs::((real, 'm::enum) vec, 'n) vec) *v (einterpret B vs::(real, 'm) vec)"
  apply (vector matrix_vector_mult_def)
  apply (auto simp: mvmult_fa_def vec_nth_eucl_of_list_eq2 index_Basis_list_axis2 index_Basis_list_axis1 vec_nth_eucl_of_list_eq
      concat_map_map_index length_concat o_def sum_list_distinct_conv_sum_set
      interpret_floatarith_inner_eq)
  apply (subst sum_index_enum_eq)
  apply simp
  done


lemma max_Var_floatariths_mvult_fa:
  assumes [simp]: "length A = D * E" "length B = E"
  shows "max_Var_floatariths (mvmult_fa D E A B) \<le> max (max_Var_floatariths A) (max_Var_floatariths B)"
  apply (auto simp: mvmult_fa_def concat_map_map_index intro!: max_Var_floatariths_leI)
   apply (rule max.coboundedI1)
  by (auto intro!: max_Var_floatarith_le_max_Var_floatariths_nth max.coboundedI2)

lemma isDERIV_mvmult_fa_nth:
  assumes "\<And>j. j < D * E \<Longrightarrow> isDERIV i (A ! j) xs"
  assumes "\<And>j. j < E \<Longrightarrow> isDERIV i (B ! j) xs"
  assumes [simp]: "length A = D * E" "length B = E" "j < D"
  shows "isDERIV i (mvmult_fa D E A B ! j) xs"
  using assms
  apply (auto simp: mvmult_fa_def concat_map_map_index isDERIV_inner_iff ac_simps)
  by (metis assms(5) in_square_lemma semiring_normalization_rules(24) semiring_normalization_rules(7))

lemma max_Var_floatariths_mapI:
  assumes "\<And>x. x \<in> set xs \<Longrightarrow> max_Var_floatarith (f x) \<le> m"
  shows "max_Var_floatariths (map f xs) \<le> m"
  using assms
  by (force intro!: max_Var_floatariths_leI simp: in_set_conv_nth)

lemma
  max_Var_floatariths_list_updateI:
  assumes "max_Var_floatariths xs \<le> m"
  assumes "max_Var_floatarith v \<le> m"
  assumes "i < length xs"
  shows "max_Var_floatariths (xs[i := v]) \<le> m"
  using assms
  apply (auto simp: nth_list_update intro!: max_Var_floatariths_leI )
  using max_Var_floatarith_le_max_Var_floatariths_nthI by blast

lemma
  max_Var_floatariths_replicateI:
  assumes "max_Var_floatarith v \<le> m"
  shows "max_Var_floatariths (replicate n v) \<le> m"
  using assms
  by (auto intro!: max_Var_floatariths_leI )

definition "FDERIV_n_floatarith fa xs ds n = ((\<lambda>x. FDERIV_floatarith x xs ds)^^n) fa"
lemma FDERIV_n_floatariths_nth: "i < length fas \<Longrightarrow> FDERIV_n_floatariths fas xs ds n ! i = FDERIV_n_floatarith (fas ! i) xs ds n"
  by (induction n)
    (auto simp: FDERIV_n_floatarith_def FDERIV_floatariths_nth)


lemma einterpret_fold_const_fa[simp]:
  "(einterpret (map (\<lambda>i. fold_const_fa (fa i)) xs) vs::'a::executable_euclidean_space) =
    einterpret (map fa xs) vs" if "length xs = DIM('a)"
  using that
  by (auto intro!: euclidean_eqI[where 'a='a] simp: algebra_simps eucl_of_list_inner)

lemma einterpret_plus[simp]:
  shows "(einterpret (map (\<lambda>i. fa1 i + fa2 i) [0..<DIM('a)]) vs::'a) =
    einterpret (map fa1 [0..<DIM('a::executable_euclidean_space)]) vs + einterpret (map fa2 [0..<DIM('a)]) vs"
  by (auto intro!: euclidean_eqI[where 'a='a] simp: algebra_simps eucl_of_list_inner)

lemma einterpret_uminus[simp]:
  shows "(einterpret (map (\<lambda>i. - fa1 i) [0..<DIM('a)]) vs::'a::executable_euclidean_space) =
    - einterpret (map fa1 [0..<DIM('a)]) vs"
  by (auto intro!: euclidean_eqI[where 'a='a] simp: algebra_simps eucl_of_list_inner)

lemma diff_floatarith_conv_add_uminus: "a - b = a + - b" for a b::floatarith
  by (auto simp: minus_floatarith_def plus_floatarith_def uminus_floatarith_def)

lemma einterpret_minus[simp]:
  shows "(einterpret (map (\<lambda>i. fa1 i - fa2 i) [0..<DIM('a)]) vs::'a::executable_euclidean_space) =
    einterpret (map fa1 [0..<DIM('a)]) vs - einterpret (map fa2 [0..<DIM('a)]) vs"
  by (simp add: diff_floatarith_conv_add_uminus)

lemma einterpret_scaleR[simp]:
  shows "(einterpret (map (\<lambda>i. fa1 * fa2 i) [0..<DIM('a)]) vs::'a::executable_euclidean_space) =
    interpret_floatarith (fa1) vs *\<^sub>R einterpret (map fa2 [0..<DIM('a)]) vs"
  by (auto intro!: euclidean_eqI[where 'a='a] simp: algebra_simps eucl_of_list_inner)

lemma einterpret_nth[simp]:
  assumes [simp]: "length xs = DIM('a)"
  shows "(einterpret (map ((!) xs) [0..<DIM('a)]) vs::'a::executable_euclidean_space) = einterpret xs vs"
  by (auto intro!: euclidean_eqI[where 'a='a] simp: algebra_simps eucl_of_list_inner)

type_synonym 'n rvec = "(real, 'n) vec"

lemma length_mvmult_fa[simp]: "length (mvmult_fa D E xs ys) = D"
  by (auto simp: mvmult_fa_def)

lemma interpret_mvmult_nth:
  assumes "D = CARD('n::enum)"
  assumes "E = CARD('m::enum)"
  assumes "length xs = D * E"
  assumes "length ys = E"
  assumes "n < CARD('n)"
  shows "interpret_floatarith (mvmult_fa D E xs ys ! n) vs =
    ((einterpret xs vs::((real, 'm) vec, 'n) vec) *v einterpret ys vs) \<bullet> (Basis_list ! n)"
proof -
  have "interpret_floatarith (mvmult_fa D E xs ys ! n) vs = einterpret (mvmult_fa D E xs ys) vs \<bullet> (Basis_list ! n::'n rvec)"
    using assms
    by (auto simp: eucl_of_list_inner)
  also
  from einterpret_mvmult_fa[OF assms(1,2), of xs ys vs]
  have "einterpret (mvmult_fa D E xs ys) vs = (einterpret xs vs::((real, 'm) vec, 'n) vec) *v einterpret ys vs"
    using assms by simp
  finally show ?thesis by simp
qed


lemmas [simp del] = fold_const_fa.simps

lemma take_eq_map_nth: "n < length xs \<Longrightarrow> take n xs = map ((!) xs) [0..<n]"
  by (induction xs) (auto intro!: nth_equalityI)

lemmas [simp del] = upt_rec_numeral
lemmas map_nth_eq_take = take_eq_map_nth[symmetric]


subsection \<open>Definition of Approximating Function using Affine Arithmetic\<close>

lemma interpret_Floatreal: "interpret_floatarith (floatarith.Num f) vs = (real_of_float f)"
  by simp

ML \<open>
(* Make a congruence rule out of a defining equation for the interpretation

   th is one defining equation of f,
     i.e. th is "f (Cp ?t1 ... ?tn) = P(f ?t1, .., f ?tn)" 
   Cp is a constructor pattern and P is a pattern 

   The result is:
     [|?A1 = f ?t1 ; .. ; ?An= f ?tn |] ==> P (?A1, .., ?An) = f (Cp ?t1 .. ?tn)
       + the a list of names of the A1 .. An, Those are fresh in the ctxt *)

fun mk_congeq ctxt fs th =
  let
    val Const (fN, _) = th |> Thm.prop_of |> HOLogic.dest_Trueprop |> HOLogic.dest_eq
      |> fst |> strip_comb |> fst;
    val ((_, [th']), ctxt') = Variable.import true [th] ctxt;
    val (lhs, rhs) = HOLogic.dest_eq (HOLogic.dest_Trueprop (Thm.prop_of th'));
    fun add_fterms (t as t1 $ t2) =
          if exists (fn f => Term.could_unify (t |> strip_comb |> fst, f)) fs
          then insert (op aconv) t
          else add_fterms t1 #> add_fterms t2
      | add_fterms (t as Abs _) =
          if exists_Const (fn (c, _) => c = fN) t
          then K [t]
          else K []
      | add_fterms _ = I;
    val fterms = add_fterms rhs [];
    val (xs, ctxt'') = Variable.variant_fixes (replicate (length fterms) "x") ctxt';
    val tys = map fastype_of fterms;
    val vs = map Free (xs ~~ tys);
    val env = fterms ~~ vs; (*FIXME*)
    fun replace_fterms (t as t1 $ t2) =
        (case AList.lookup (op aconv) env t of
            SOME v => v
          | NONE => replace_fterms t1 $ replace_fterms t2)
      | replace_fterms t =
        (case AList.lookup (op aconv) env t of
            SOME v => v
          | NONE => t);
    fun mk_def (Abs (x, xT, t), v) =
          HOLogic.mk_Trueprop (HOLogic.all_const xT $ Abs (x, xT, HOLogic.mk_eq (v $ Bound 0, t)))
      | mk_def (t, v) = HOLogic.mk_Trueprop (HOLogic.mk_eq (v, t));
    fun tryext x =
      (x RS @{lemma "(\<forall>x. f x = g x) \<Longrightarrow> f = g" by blast} handle THM _ => x);
    val cong =
      (Goal.prove ctxt'' [] (map mk_def env)
        (HOLogic.mk_Trueprop (HOLogic.mk_eq (lhs, replace_fterms rhs)))
        (fn {context, prems, ...} =>
          Local_Defs.unfold0_tac context (map tryext prems) THEN resolve_tac ctxt'' [th'] 1)) RS sym;
    val (cong' :: vars') =
      Variable.export ctxt'' ctxt (cong :: map (Drule.mk_term o Thm.cterm_of ctxt'') vs);
    val vs' = map (fst o fst o Term.dest_Var o Thm.term_of o Drule.dest_term) vars';

  in (vs', cong') end;

fun mk_congs ctxt eqs =
  let
    val fs = fold_rev (fn eq => insert (op =) (eq |> Thm.prop_of |> HOLogic.dest_Trueprop
      |> HOLogic.dest_eq |> fst |> strip_comb
      |> fst)) eqs [];
    val tys = fold_rev (fn f => fold (insert (op =)) (f |> fastype_of |> binder_types |> tl)) fs [];
    val (vs, ctxt') = Variable.variant_fixes (replicate (length tys) "vs") ctxt;
    val subst =
      the o AList.lookup (op =)
        (map2 (fn T => fn v => (T, Thm.cterm_of ctxt' (Free (v, T)))) tys vs);
    fun prep_eq eq =
      let
        val (_, _ :: vs) = eq |> Thm.prop_of |> HOLogic.dest_Trueprop
          |> HOLogic.dest_eq |> fst |> strip_comb;
        val subst = map_filter (fn Var v => SOME (v, subst (#2 v)) | _ => NONE) vs;
      in Thm.instantiate ([], subst) eq end;
    val (ps, congs) = map_split (mk_congeq ctxt' fs o prep_eq) eqs;
    val bds = AList.make (K ([], [])) tys;
  in (ps ~~ Variable.export ctxt' ctxt congs, bds) end
\<close>

ML \<open>
fun interpret_floatariths_congs ctxt =
  mk_congs ctxt @{thms interpret_floatarith.simps interpret_floatariths.simps}
  |> fst
  |> map snd
\<close>

ML \<open>
fun preproc_form_conv ctxt =
  Simplifier.rewrite
   (put_simpset HOL_basic_ss ctxt addsimps
     (Named_Theorems.get ctxt @{named_theorems approximation_preproc}))\<close>

ML \<open>fun reify_floatariths_tac ctxt i =
  CONVERSION (preproc_form_conv ctxt) i
  THEN REPEAT_ALL_NEW (fn i => resolve_tac ctxt (interpret_floatariths_congs ctxt) i) i\<close>

method_setup reify_floatariths = \<open>
  Scan.succeed (fn ctxt => SIMPLE_METHOD' (reify_floatariths_tac ctxt))
\<close> "reification of floatariths expression"

schematic_goal reify_example:
  "[xs!i * xs!j, xs!i + xs!j powr (sin (xs!0)), xs!k + (2 / 3 * xs!i * xs!j)] = interpret_floatariths ?fas xs"
  by (reify_floatariths)

ML \<open>fun interpret_floatariths_step_tac ctxt i = resolve_tac ctxt (interpret_floatariths_congs ctxt) i\<close>

method_setup reify_floatariths_step = \<open>
  Scan.succeed (fn ctxt => SIMPLE_METHOD' (interpret_floatariths_step_tac ctxt))
\<close> "reification of floatariths expression (step)"

lemma eucl_of_list_interpret_floatariths_cong:
  fixes y::"'a::executable_euclidean_space"
  assumes "\<And>b. b \<in> Basis \<Longrightarrow> interpret_floatarith (fa (index Basis_list b)) vs = y \<bullet> b"
  assumes "length xs = DIM('a)"
  shows "eucl_of_list (interpret_floatariths (map fa [0..<DIM('a)]) vs) = y"
  apply (rule euclidean_eqI)
  apply (subst eucl_of_list_inner)
  by (auto simp: assms)

lemma interpret_floatariths_fold_const_fa[simp]:
  "interpret_floatariths (map fold_const_fa ds) = interpret_floatariths ds"
  by (auto intro!: nth_equalityI)

fun subst_floatarith where
"subst_floatarith s (Add a b)         = Add (subst_floatarith s a) (subst_floatarith s b)" |
"subst_floatarith s (Mult a b)        = Mult (subst_floatarith s a) (subst_floatarith s b)" |
"subst_floatarith s (Minus a)         = Minus (subst_floatarith s a)" |
"subst_floatarith s (Inverse a)       = Inverse (subst_floatarith s a)" |
"subst_floatarith s (Cos a)           = Cos (subst_floatarith s a)" |
"subst_floatarith s (Arctan a)        = Arctan (subst_floatarith s a)" |
"subst_floatarith s (Min a b)         = Min (subst_floatarith s a) (subst_floatarith s b)" |
"subst_floatarith s (Max a b)         = Max (subst_floatarith s a) (subst_floatarith s b)" |
"subst_floatarith s (Abs a)           = Abs (subst_floatarith s a)" |
"subst_floatarith s Pi                = Pi" |
"subst_floatarith s (Sqrt a)          = Sqrt (subst_floatarith s a)" |
"subst_floatarith s (Exp a)           = Exp (subst_floatarith s a)" |
"subst_floatarith s (Powr a b)        = Powr (subst_floatarith s a) (subst_floatarith s b)" |
"subst_floatarith s (Ln a)            = Ln (subst_floatarith s a)" |
"subst_floatarith s (Power a i)       = Power (subst_floatarith s a) i" |
"subst_floatarith s (Floor a)         = Floor (subst_floatarith s a)" |
"subst_floatarith s (Num f)           = Num f" |
"subst_floatarith s (Var n)           = s n"

lemma interpret_floatarith_subst_floatarith:
  assumes "max_Var_floatarith fa \<le> D"
  shows "interpret_floatarith (subst_floatarith s fa) vs =
    interpret_floatarith fa (map (\<lambda>i. interpret_floatarith (s i) vs) [0..<D])"
  using assms
  by (induction fa) auto

lemma max_Var_floatarith_subst_floatarith_le[THEN order_trans]:
  assumes "length xs \<ge> max_Var_floatarith fa"
  shows "max_Var_floatarith (subst_floatarith ((!) xs) fa) \<le> max_Var_floatariths xs"
  using assms
  by (induction fa) (auto intro!: max_Var_floatarith_le_max_Var_floatariths_nth)

lemma max_Var_floatariths_subst_floatarith_le[THEN order_trans]:
  assumes "length xs \<ge> max_Var_floatariths fas"
  shows "max_Var_floatariths (map (subst_floatarith ((!) xs)) fas) \<le> max_Var_floatariths xs"
  using assms
  by (induction fas) (auto simp: max_Var_floatarith_subst_floatarith_le)

fun continuous_on_floatarith :: "floatarith \<Rightarrow> bool" where
  "continuous_on_floatarith (Add a b)         = (continuous_on_floatarith a \<and> continuous_on_floatarith b)" |
"continuous_on_floatarith (Mult a b)        = (continuous_on_floatarith a \<and> continuous_on_floatarith b)" |
"continuous_on_floatarith (Minus a)         = continuous_on_floatarith a" |
"continuous_on_floatarith (Inverse a)       = False" |
"continuous_on_floatarith (Cos a)           = continuous_on_floatarith a" |
"continuous_on_floatarith (Arctan a)        = continuous_on_floatarith a" |
"continuous_on_floatarith (Min a b)         = (continuous_on_floatarith a \<and> continuous_on_floatarith b)" |
"continuous_on_floatarith (Max a b) = (continuous_on_floatarith a \<and> continuous_on_floatarith b)" |
"continuous_on_floatarith (Abs a)           = continuous_on_floatarith a" |
"continuous_on_floatarith Pi                = True" |
"continuous_on_floatarith (Sqrt a)          = False" |
"continuous_on_floatarith (Exp a)           = continuous_on_floatarith a" |
"continuous_on_floatarith (Powr a b)        = False" |
"continuous_on_floatarith (Ln a)            = False" |
"continuous_on_floatarith (Floor a)         = False" |
"continuous_on_floatarith (Power a n)       = (if n = 0 then True else continuous_on_floatarith a)" |
"continuous_on_floatarith (Num f)           = True" |
"continuous_on_floatarith (Var n)           = True"

definition "Maxs\<^sub>e xs = fold (\<lambda>a b. floatarith.Max a b) xs"
definition "norm2\<^sub>e n = Maxs\<^sub>e (map (\<lambda>j. Norm (map (\<lambda>i. Var (Suc j * n + i)) [0..<n])) [0..<n]) (Num 0)"

definition "N\<^sub>r l = Num (float_of l)"

lemma interpret_floatarith_Norm:
  "interpret_floatarith (Norm xs) vs = L2_set (\<lambda>i. interpret_floatarith (xs ! i) vs) {0..<length xs}"
  by (auto simp: Norm_def L2_set_def sum_list_sum_nth power2_eq_square)

lemma interpret_floatarith_Nr[simp]: "interpret_floatarith (N\<^sub>r U) vs = real_of_float (float_of U)"
  by (auto simp: N\<^sub>r_def)


fun list_updates where
  "list_updates [] _ xs = xs"
| "list_updates _ [] xs = xs"
| "list_updates (i#is) (u#us) xs = list_updates is us (xs[i:=u])"


lemma list_updates_nth_notmem:
  assumes "length xs = length ys"
  assumes "i \<notin> set xs"
  shows "list_updates xs ys vs ! i = vs ! i"
  using assms
  by (induction xs ys arbitrary: i vs rule: list_induct2) auto

lemma list_updates_nth_less:
  assumes "length xs = length ys" "distinct xs"
  assumes "i < length vs"
  shows "list_updates xs ys vs ! i = (if i \<in> set xs then ys ! (index xs i) else vs ! i)"
  using assms
  by (induction xs ys arbitrary: i vs rule: list_induct2) (auto simp: list_updates_nth_notmem)

lemma length_list_updates[simp]: "length (list_updates xs ys vs) = length vs"
  by (induction xs ys vs rule: list_updates.induct) simp_all

lemma list_updates_nth_ge[simp]:
  "x \<ge> length vs \<Longrightarrow> length xs = length ys \<Longrightarrow> list_updates xs ys vs ! x = vs ! x"
  apply (induction xs ys vs rule: list_updates.induct)
  apply (auto simp: nth_list_update)
  by (metis list_update_beyond nth_list_update_neq)

lemma
  list_updates_nth:
  assumes [simp]: "length xs = length ys" "distinct xs"
  shows "list_updates xs ys vs ! i = (if i < length vs \<and> i \<in> set xs then ys ! index xs i else vs ! i)" 
  by (auto simp: list_updates_nth_less list_updates_nth_notmem)

lemma list_of_eucl_coord_update:
  assumes [simp]: "length xs = DIM('a::executable_euclidean_space)"
  assumes [simp]: "distinct xs"
  assumes [simp]: "i \<in> Basis"
  assumes [simp]: "\<And>n. n \<in> set xs \<Longrightarrow> n < length vs"
  shows "list_updates xs (list_of_eucl (x + (p - x \<bullet> i) *\<^sub>R i::'a)) vs =
   (list_updates xs (list_of_eucl x) vs)[xs ! index Basis_list i := p]"
  apply (auto intro!: nth_equalityI simp: list_updates_nth nth_list_update)
   apply (simp add: algebra_simps inner_Basis index_nth_id)
  apply (auto simp add: algebra_simps inner_Basis index_nth_id)
  done

definition "eucl_of_env is vs = eucl_of_list (map (nth vs) is)"

lemma list_updates_list_of_eucl_of_env[simp]:
  assumes [simp]: "length xs = DIM('a::executable_euclidean_space)" "distinct xs"
  shows "list_updates xs (list_of_eucl (eucl_of_env xs vs::'a)) vs = vs"
  by (auto intro!: nth_equalityI simp: list_updates_nth nth_list_update eucl_of_env_def)

lemma nth_nth_eucl_of_env_inner:
  "b \<in> Basis \<Longrightarrow> length is = DIM('a) \<Longrightarrow> vs ! (is ! index Basis_list b) = eucl_of_env is vs \<bullet> b"
  for b::"'a::executable_euclidean_space"
  by (auto simp: eucl_of_env_def eucl_of_list_inner)

lemma list_updates_idem[simp]:
  assumes "(\<And>i. i \<in> set X0 \<Longrightarrow> i < length vs)"
  shows "(list_updates X0 (map ((!) vs) X0) vs) = vs"
  using assms
  by (induction X0) auto


lemma pairwise_orthogonal_Basis[intro, simp]: "pairwise orthogonal Basis"
  by (auto simp: pairwise_alt orthogonal_def inner_Basis)

primrec freshs_floatarith where
  "freshs_floatarith (Var y) x \<longleftrightarrow> (y \<notin> set x)"
| "freshs_floatarith (Num a) x \<longleftrightarrow> True"
| "freshs_floatarith Pi x \<longleftrightarrow> True"
| "freshs_floatarith (Cos a) x \<longleftrightarrow> freshs_floatarith a x"
| "freshs_floatarith (Abs a) x \<longleftrightarrow> freshs_floatarith a x"
| "freshs_floatarith (Arctan a) x \<longleftrightarrow> freshs_floatarith a x"
| "freshs_floatarith (Sqrt a) x \<longleftrightarrow> freshs_floatarith a x"
| "freshs_floatarith (Exp a) x \<longleftrightarrow> freshs_floatarith a x"
| "freshs_floatarith (Floor a) x \<longleftrightarrow> freshs_floatarith a x"
| "freshs_floatarith (Power a n) x \<longleftrightarrow> freshs_floatarith a x"
| "freshs_floatarith (Minus a) x \<longleftrightarrow> freshs_floatarith a x"
| "freshs_floatarith (Ln a) x \<longleftrightarrow> freshs_floatarith a x"
| "freshs_floatarith (Inverse a) x \<longleftrightarrow> freshs_floatarith a x"
| "freshs_floatarith (Add a b) x \<longleftrightarrow> freshs_floatarith a x \<and> freshs_floatarith b x"
| "freshs_floatarith (Mult a b) x \<longleftrightarrow> freshs_floatarith a x \<and> freshs_floatarith b x"
| "freshs_floatarith (floatarith.Max a b) x \<longleftrightarrow> freshs_floatarith a x \<and> freshs_floatarith b x"
| "freshs_floatarith (floatarith.Min a b) x \<longleftrightarrow> freshs_floatarith a x \<and> freshs_floatarith b x"
| "freshs_floatarith (Powr a b) x \<longleftrightarrow> freshs_floatarith a x \<and> freshs_floatarith b x"

lemma freshs_floatarith[simp]:
  assumes "freshs_floatarith fa ds" "length ds = length xs"
  shows "interpret_floatarith fa (list_updates ds xs vs) = interpret_floatarith fa vs"
  using assms
  by (induction fa) (auto simp: list_updates_nth_notmem)

lemma freshs_floatarith_max_Var_floatarithI:
  assumes "\<And>x. x \<in> set xs \<Longrightarrow> max_Var_floatarith f \<le> x"
  shows "freshs_floatarith f xs"
  using assms Suc_n_not_le_n
  by (induction f; force)

definition "freshs_floatariths fas xs = (\<forall>fa\<in>set fas. freshs_floatarith fa xs)"

lemma freshs_floatariths_max_Var_floatarithsI:
  assumes "\<And>x. x \<in> set xs \<Longrightarrow> max_Var_floatariths f \<le> x"
  shows "freshs_floatariths f xs"
  using assms le_trans max_Var_floatarith_le_max_Var_floatariths
  by (force simp: freshs_floatariths_def intro!: freshs_floatarith_max_Var_floatarithI)

lemma freshs_floatariths_freshs_floatarithI:
  assumes "\<And>fa. fa \<in> set fas \<Longrightarrow> freshs_floatarith fa xs"
  shows "freshs_floatariths fas xs"
  by (auto simp: freshs_floatariths_def assms)

lemma fresh_floatariths_fresh_floatarithI:
  assumes "freshs_floatariths fas xs"
  assumes "fa \<in> set fas"
  shows "freshs_floatarith fa xs"
  using assms
  by (auto simp: freshs_floatariths_def)

lemma fresh_floatariths_fresh_floatarith[simp]:
  "fresh_floatariths (fas) i \<Longrightarrow> fa \<in> set fas \<Longrightarrow> fresh_floatarith fa i"
  by (induction fas) auto

lemma interpret_floatariths_fresh_cong:
  assumes "\<And>i. \<not>fresh_floatariths f i \<Longrightarrow> xs ! i = ys ! i"
  shows "interpret_floatariths f ys = interpret_floatariths f xs"
  by (auto intro!: nth_equalityI assms interpret_floatarith_fresh_cong simp: )

fun subterms :: "floatarith \<Rightarrow> floatarith set" where
"subterms (Add a b) = insert (Add a b) (subterms a \<union> subterms b)" |
"subterms (Mult a b) = insert (Mult a b) (subterms a \<union> subterms b)" |
"subterms (Min a b) = insert (Min a b) (subterms a \<union> subterms b)" |
"subterms (floatarith.Max a b) = insert (floatarith.Max a b) (subterms a \<union> subterms b)" |
"subterms (Powr a b) = insert (Powr a b) (subterms a \<union> subterms b)" |
"subterms (Inverse a) = insert (Inverse a) (subterms a)" |
"subterms (Cos a) = insert (Cos a) (subterms a)" |
"subterms (Arctan a) = insert (Arctan a) (subterms a)" |
"subterms (Abs a) = insert (Abs a) (subterms a)" |
"subterms (Sqrt a) = insert (Sqrt a) (subterms a)" |
"subterms (Exp a) = insert (Exp a) (subterms a)" |
"subterms (Ln a) = insert (Ln a) (subterms a)" |
"subterms (Power a n) = insert (Power a n) (subterms a)" |
"subterms (Floor a) = insert (Floor a) (subterms a)" |
"subterms (Minus a) = insert (Minus a) (subterms a)" |
"subterms Pi = {Pi}" |
"subterms (Var v) = {Var v}" |
"subterms (Num n) = {Num n}"

lemma subterms_self[simp]: "fa2 \<in> subterms fa2"
  by (induction fa2) auto

lemma interpret_floatarith_FDERIV_floatarith_eucl_of_env:\<comment> \<open>TODO: cleanup, reduce to DERIV?!\<close>
  assumes iD: "\<And>i. i < DIM('a) \<Longrightarrow> isDERIV (xs ! i) fa vs"
  assumes ds_fresh: "freshs_floatarith fa ds"
  assumes [simp]: "length xs = DIM ('a)" "length ds = DIM ('a)"
    "\<And>i. i \<in> set xs \<Longrightarrow> i < length vs" "distinct xs"
    "\<And>i. i \<in> set ds \<Longrightarrow> i < length vs" "distinct ds"
  shows "((\<lambda>x::'a::executable_euclidean_space.
    (interpret_floatarith fa (list_updates xs (list_of_eucl x) vs))) has_derivative
    (\<lambda>d. interpret_floatarith (FDERIV_floatarith fa xs (map Var ds)) (list_updates ds (list_of_eucl d) vs) )
    ) (at (eucl_of_env xs vs))"
  using iD ds_fresh
proof (induction fa)
  case (Add fa1 fa2)
  then show ?case
    by (auto intro!: derivative_eq_intros simp: FDERIV_floatarith_def interpret_floatarith_inner_floatariths 
        interpret_floatariths_map algebra_simps list_of_eucl_coord_update[symmetric])
next
  case (Minus fa)
  then show ?case
    by (auto intro!: derivative_eq_intros simp: FDERIV_floatarith_def interpret_floatarith_inner_floatariths 
        interpret_floatariths_map algebra_simps list_of_eucl_coord_update[symmetric])
next
  case (Mult fa1 fa2)
  then show ?case
    by (auto intro!: derivative_eq_intros simp: FDERIV_floatarith_def interpret_floatarith_inner_floatariths 
        interpret_floatariths_map algebra_simps list_of_eucl_coord_update[symmetric])
next
  case (Inverse fa)
  then show ?case
    by (force intro!: derivative_eq_intros DIM_positive simp: FDERIV_floatarith_def interpret_floatarith_inner_floatariths 
        interpret_floatariths_map algebra_simps list_of_eucl_coord_update[symmetric] power2_eq_square)
next
  case (Cos fa)
  then show ?case
    by (auto intro!: derivative_eq_intros ext simp: FDERIV_floatarith_def interpret_floatarith_inner_floatariths 
        interpret_floatariths_map add.commute minus_sin_cos_eq
        simp flip: mult_minus_left list_of_eucl_coord_update cos_pi_minus)
next
  case (Arctan fa)
  then show ?case
    by (auto intro!: derivative_eq_intros simp: FDERIV_floatarith_def interpret_floatarith_inner_floatariths 
        interpret_floatariths_map algebra_simps list_of_eucl_coord_update[symmetric])
next
  case (Abs fa)
  then show ?case
    by (auto intro!: derivative_eq_intros DIM_positive simp: FDERIV_floatarith_def interpret_floatarith_inner_floatariths 
        interpret_floatariths_map algebra_simps list_of_eucl_coord_update[symmetric] )
next
  case (Max fa1 fa2)
  then show ?case
    by (auto intro!: derivative_eq_intros DIM_positive simp: FDERIV_floatarith_def interpret_floatarith_inner_floatariths 
        interpret_floatariths_map algebra_simps list_of_eucl_coord_update[symmetric] )
next
  case (Min fa1 fa2)
  then show ?case
    by (auto intro!: derivative_eq_intros DIM_positive simp: FDERIV_floatarith_def interpret_floatarith_inner_floatariths 
        interpret_floatariths_map algebra_simps list_of_eucl_coord_update[symmetric] )
next
  case Pi
  then show ?case
    by (auto intro!: derivative_eq_intros DIM_positive simp: FDERIV_floatarith_def interpret_floatarith_inner_floatariths 
        interpret_floatariths_map algebra_simps list_of_eucl_coord_update[symmetric] )
next
  case (Sqrt fa)
  then show ?case
    by (force intro!: derivative_eq_intros DIM_positive simp: FDERIV_floatarith_def interpret_floatarith_inner_floatariths 
        interpret_floatariths_map algebra_simps list_of_eucl_coord_update[symmetric] )
next
  case (Exp fa)
  then show ?case
    by (auto intro!: derivative_eq_intros DIM_positive simp: FDERIV_floatarith_def interpret_floatarith_inner_floatariths 
        interpret_floatariths_map algebra_simps list_of_eucl_coord_update[symmetric] )
next
  case (Powr fa1 fa2)
  then show ?case
    by (force intro!: derivative_eq_intros DIM_positive simp: FDERIV_floatarith_def interpret_floatarith_inner_floatariths 
        interpret_floatariths_map algebra_simps divide_simps list_of_eucl_coord_update[symmetric] )
next
  case (Ln fa)
  then show ?case
    by (force intro!: derivative_eq_intros DIM_positive simp: FDERIV_floatarith_def interpret_floatarith_inner_floatariths 
        interpret_floatariths_map algebra_simps list_of_eucl_coord_update[symmetric] )
next
  case (Power fa x2a)
  then show ?case
    apply (cases x2a)
    apply (auto intro!: DIM_positive derivative_eq_intros simp: FDERIV_floatarith_def interpret_floatarith_inner_floatariths 
        interpret_floatariths_map algebra_simps list_of_eucl_coord_update[symmetric])
    apply (auto intro!: ext simp: )
    by (simp add: semiring_normalization_rules(27))
next
  case (Floor fa)
  then show ?case
    by (force intro!: derivative_eq_intros DIM_positive simp: FDERIV_floatarith_def interpret_floatarith_inner_floatariths 
        interpret_floatariths_map algebra_simps list_of_eucl_coord_update[symmetric] )
next
  case (Var x)
  then show ?case
    apply (auto intro!: derivative_eq_intros DIM_positive simp: FDERIV_floatarith_def interpret_floatarith_inner_floatariths 
        interpret_floatariths_map algebra_simps list_of_eucl_coord_update[symmetric] if_distrib)
    apply (subst list_updates_nth)
      apply (auto intro!: derivative_eq_intros ext split: if_splits
        cong: if_cong simp: if_distribR eucl_of_list_if)
    apply (subst inner_commute)
    apply (rule arg_cong[where f="\<lambda>b. a \<bullet> b" for a])
    apply (auto intro!: euclidean_eqI[where 'a='a] simp: eucl_of_list_inner list_updates_nth index_nth_id)
    done
next
  case (Num x)
  then show ?case
    by (auto intro!: derivative_eq_intros DIM_positive simp: FDERIV_floatarith_def interpret_floatarith_inner_floatariths 
        interpret_floatariths_map algebra_simps list_of_eucl_coord_update[symmetric] )
qed

lemma interpret_floatarith_FDERIV_floatarith_append:
  assumes iD: "\<And>i j. i < DIM('a) \<Longrightarrow> isDERIV i (fa) (list_of_eucl x @ params)"
  assumes m: "max_Var_floatarith fa \<le> DIM('a) + length params"
  shows "((\<lambda>x::'a::executable_euclidean_space.
      interpret_floatarith fa (list_of_eucl x @ params)) has_derivative
        (\<lambda>d. interpret_floatarith
         (FDERIV_floatarith fa [0..<DIM('a)] (map Var [length params + DIM('a)..<length params + 2*DIM('a)]))
         (list_of_eucl x @ params @ list_of_eucl d))) (at x)"
proof -
  have m_nth: "ia < max_Var_floatarith fa \<Longrightarrow> ia < DIM('a) + length params" for ia
    using less_le_trans m by blast
  have "((\<lambda>xa::'a. interpret_floatarith fa
           (list_updates [0..<DIM('a)] (list_of_eucl xa) (list_of_eucl x @ params @ replicate DIM('a) 0))) has_derivative
   (\<lambda>d. interpret_floatarith (FDERIV_floatarith fa [0..<DIM('a)] (map Var [length params + DIM('a)..<length params + 2 * DIM('a)]))
          (list_updates [length params + DIM('a)..<length params + 2 * DIM('a)] (list_of_eucl d)
            (list_of_eucl x @ params @ replicate DIM('a) 0))))
   (at (eucl_of_env [0..<DIM('a)] (list_of_eucl x @ params @ replicate DIM('a) 0)))"
    by (rule interpret_floatarith_FDERIV_floatarith_eucl_of_env)
      (auto intro!: iD freshs_floatarith_max_Var_floatarithI isDERIV_max_Var_floatarithI[OF iD]
        max_Var_floatarith_le_max_Var_floatariths[THEN order_trans] m[THEN order_trans]
        simp: nth_append add.commute less_diff_conv2 m_nth)
  moreover have "interpret_floatarith fa (list_updates [0..<DIM('a)] (list_of_eucl xa) (list_of_eucl x @ params @ replicate DIM('a) 0)) =
    interpret_floatarith fa (list_of_eucl xa @ params)" for xa::'a
    apply (auto intro!: nth_equalityI interpret_floatarith_max_Var_cong simp: )
    apply (auto simp: list_updates_nth nth_append dest: m_nth)
    done
  moreover have "(list_updates [length params + DIM('a)..<length params + 2 * DIM('a)] (list_of_eucl d) (list_of_eucl x @ params @ replicate DIM('a) 0)) =
    (list_of_eucl x @ params @ list_of_eucl d)" for d::'a
    by (auto simp: intro!: nth_equalityI simp: list_updates_nth nth_append add.commute)
  moreover have "(eucl_of_env [0..<DIM('a)] (list_of_eucl x @ params @ replicate DIM('a) 0)) = x"
    by (auto intro!: euclidean_eqI[where 'a='a] simp: eucl_of_env_def eucl_of_list_inner nth_append)
  ultimately show ?thesis by simp
qed

lemma interpret_floatarith_FDERIV_floatarith:
  assumes iD: "\<And>i j. i < DIM('a) \<Longrightarrow> isDERIV i (fa) (list_of_eucl x)"
  assumes m: "max_Var_floatarith fa \<le> DIM('a)"
  shows "((\<lambda>x::'a::executable_euclidean_space.
      interpret_floatarith fa (list_of_eucl x)) has_derivative
        (\<lambda>d. interpret_floatarith
         (FDERIV_floatarith fa [0..<DIM('a)] (map Var [DIM('a)..<2*DIM('a)]))
         (list_of_eucl x @ list_of_eucl d))) (at x)"
  using interpret_floatarith_FDERIV_floatarith_append[where params=Nil,simplified, OF assms]
  by simp

lemma interpret_floatarith_eventually_isDERIV:
  assumes iD: "\<And>i j. i < DIM('a) \<Longrightarrow> isDERIV i fa (list_of_eucl x @ params)"
  assumes m: "max_Var_floatarith fa \<le> DIM('a::executable_euclidean_space) + length params"
  shows "\<forall>i < DIM('a). \<forall>\<^sub>F (x::'a) in at x. isDERIV i fa (list_of_eucl x @ params)"
  using iD m
proof (induction fa)
  case (Inverse fa)
  then have "\<forall>i<DIM('a). \<forall>\<^sub>F x in at x. isDERIV i fa (list_of_eucl x @ params)"
    by auto
  moreover
  have iD: "i < DIM('a) \<Longrightarrow> isDERIV i fa (list_of_eucl x @ params)" "interpret_floatarith fa (list_of_eucl x @ params) \<noteq> 0" for i
    using Inverse.prems(1)[OF ] by force+
  from Inverse have m: "max_Var_floatarith fa \<le> DIM('a) + length params" by simp
  from has_derivative_continuous[OF interpret_floatarith_FDERIV_floatarith_append, OF iD(1) m]
  have "isCont (\<lambda>x. interpret_floatarith fa (list_of_eucl x @ params)) x" by simp
  then have "\<forall>\<^sub>F x in at x. interpret_floatarith fa (list_of_eucl x @ params) \<noteq> 0"
    using iD(2) tendsto_imp_eventually_ne
    by (auto simp: isCont_def)
  ultimately
  show ?case
    by (auto elim: eventually_elim2)
next
  case (Sqrt fa)
  then have "\<forall>i<DIM('a). \<forall>\<^sub>F x in at x. isDERIV i fa (list_of_eucl x @ params)"
    by auto
  moreover
  have iD: "i < DIM('a) \<Longrightarrow> isDERIV i fa (list_of_eucl x @ params)" "interpret_floatarith fa (list_of_eucl x @ params) > 0" for i
    using Sqrt.prems(1)[OF ] by force+
  from Sqrt have m: "max_Var_floatarith fa \<le> DIM('a) + length params" by simp
  from has_derivative_continuous[OF interpret_floatarith_FDERIV_floatarith_append, OF iD(1) m]
  have "isCont (\<lambda>x. interpret_floatarith fa (list_of_eucl x @ params)) x" by simp
  then have "\<forall>\<^sub>F x in at x. interpret_floatarith fa (list_of_eucl x @ params) > 0"
    using iD(2) order_tendstoD
    by (auto simp: isCont_def)
  ultimately
  show ?case
    by (auto elim: eventually_elim2)
next
  case (Powr fa1 fa2)
  then have "\<forall>i<DIM('a). \<forall>\<^sub>F x in at x. isDERIV i fa1 (list_of_eucl x @ params)"
    "\<forall>i<DIM('a). \<forall>\<^sub>F x in at x. isDERIV i fa2 (list_of_eucl x @ params)"
    by auto
  moreover
  have iD: "i < DIM('a) \<Longrightarrow> isDERIV i fa1 (list_of_eucl x @ params)" "interpret_floatarith fa1 (list_of_eucl x @ params) > 0"
    for i
    using Powr.prems(1) by force+
  from Powr have m: "max_Var_floatarith fa1 \<le> DIM('a) + length params" by simp
  from has_derivative_continuous[OF interpret_floatarith_FDERIV_floatarith_append, OF iD(1) m]
  have "isCont (\<lambda>x. interpret_floatarith fa1 (list_of_eucl x @ params)) x" by simp
  then have "\<forall>\<^sub>F x in at x. interpret_floatarith fa1 (list_of_eucl x @ params) > 0"
    using iD(2) order_tendstoD
    by (auto simp: isCont_def)
  ultimately
  show ?case
    apply safe
    subgoal for i
      apply (safe dest!: spec[of _ i])
      subgoal premises prems
        using prems(1,3,4)
        by eventually_elim auto
      done
    done
next
  case (Ln fa)
  then have "\<forall>i<DIM('a). \<forall>\<^sub>F x in at x. isDERIV i fa (list_of_eucl x @ params)"
    by auto
  moreover
  have iD: "i < DIM('a) \<Longrightarrow> isDERIV i fa (list_of_eucl x @ params)" "interpret_floatarith fa (list_of_eucl x @ params) > 0" for i
    using Ln.prems(1)[OF ] by force+
  from Ln have m: "max_Var_floatarith fa \<le> DIM('a) + length params" by simp
  from has_derivative_continuous[OF interpret_floatarith_FDERIV_floatarith_append, OF iD(1) m]
  have "isCont (\<lambda>x. interpret_floatarith fa (list_of_eucl x @ params)) x" by simp
  then have "\<forall>\<^sub>F x in at x. interpret_floatarith fa (list_of_eucl x @ params) > 0"
    using iD(2) order_tendstoD
    by (auto simp: isCont_def)
  ultimately
  show ?case
    by (auto elim: eventually_elim2)
next
  case (Power fa m) then show ?case by (cases m) auto
next
  case (Floor fa)
  then have "\<forall>i<DIM('a). \<forall>\<^sub>F x in at x. isDERIV i fa (list_of_eucl x @ params)"
    by auto
  moreover
  have iD: "i < DIM('a) \<Longrightarrow> isDERIV i fa (list_of_eucl x @ params)"
    "interpret_floatarith fa (list_of_eucl x @ params) \<notin> \<int>" for i
    using Floor.prems(1)[OF ] by force+
  from Floor have m: "max_Var_floatarith fa \<le> DIM('a) + length params" by simp
  from has_derivative_continuous[OF interpret_floatarith_FDERIV_floatarith_append, OF iD(1) m]
  have cont: "isCont (\<lambda>x. interpret_floatarith fa (list_of_eucl x @ params)) x" by simp
  let ?i = "\<lambda>x. interpret_floatarith fa (list_of_eucl x @ params)"
  have "\<forall>\<^sub>F y in at x. ?i y > floor (?i x)" "\<forall>\<^sub>F y in at x. ?i y < ceiling (?i x)"
    using cont
    by (auto simp: isCont_def eventually_floor_less eventually_less_ceiling iD(2))
  then have "\<forall>\<^sub>F x in at x. ?i x \<notin> \<int>"
    apply eventually_elim
    apply (auto simp: Ints_def)
    by linarith
  ultimately
  show ?case
    by (auto elim: eventually_elim2)
qed (fastforce intro: DIM_positive elim: eventually_elim2)+

lemma eventually_isFDERIV:
  assumes iD: "isFDERIV DIM('a) [0..<DIM('a)] fas (list_of_eucl x@params)"
  assumes m: "max_Var_floatariths fas \<le> DIM('a::executable_euclidean_space) + length params"
  shows "\<forall>\<^sub>F (x::'a) in at x. isFDERIV DIM('a) [0..<DIM('a)] fas (list_of_eucl x @ params)"
  by (auto simp: isFDERIV_def all_nat_less_eq eventually_ball_finite_distrib isFDERIV_lengthD[OF iD]
      intro!: interpret_floatarith_eventually_isDERIV[OF isFDERIV_uptD[OF iD], rule_format]
        max_Var_floatarith_le_max_Var_floatariths[THEN order_trans] m)

lemma isFDERIV_eventually_isFDERIV:
  assumes iD: "isFDERIV DIM('a) [0..<DIM('a)] fas (list_of_eucl x@params)"
  assumes m: "max_Var_floatariths fas \<le> DIM('a::executable_euclidean_space) + length params"
    shows "\<forall>\<^sub>F (x::'a) in at x. isFDERIV DIM('a) [0..<DIM('a)] fas (list_of_eucl x @ params)"
  by (rule eventually_isFDERIV) (use assms in \<open>auto simp: isFDERIV_def\<close>)

lemma interpret_floatarith_FDERIV_floatariths_eucl_of_env:
  assumes iD: "isFDERIV DIM('a) xs fas vs"
  assumes fresh: "freshs_floatariths (fas) ds"
  assumes [simp]: "length ds = DIM ('a)"
    "\<And>i. i \<in> set xs \<Longrightarrow> i < length vs" "distinct xs"
    "\<And>i. i \<in> set ds \<Longrightarrow> i < length vs" "distinct ds"
  shows "((\<lambda>x::'a::executable_euclidean_space.
    eucl_of_list
      (interpret_floatariths fas (list_updates xs (list_of_eucl x) vs))::'a) has_derivative
        (\<lambda>d. eucl_of_list (interpret_floatariths
         (FDERIV_floatariths fas xs (map Var ds))
         (list_updates ds (list_of_eucl d) vs)))) (at (eucl_of_env xs vs))"
  by (subst has_derivative_componentwise_within)
    (auto simp add: eucl_of_list_inner isFDERIV_lengthD[OF iD]
      intro!: interpret_floatarith_FDERIV_floatarith_eucl_of_env iD[THEN isFDERIV_isDERIV_D]
        fresh_floatariths_fresh_floatarithI fresh)

lemma interpret_floatarith_FDERIV_floatariths_append:
  assumes iD: "isFDERIV DIM('a) [0..<DIM('a)] fas (list_of_eucl x @ ramsch)"
  assumes m: "max_Var_floatariths fas \<le> DIM('a) + length ramsch"
  assumes [simp]: "length fas = DIM('a)"
  shows "((\<lambda>x::'a::executable_euclidean_space.
    eucl_of_list
      (interpret_floatariths fas (list_of_eucl x@ramsch))::'a) has_derivative
        (\<lambda>d. eucl_of_list (interpret_floatariths
         (FDERIV_floatariths fas [0..<DIM('a)] (map Var [DIM('a)+length ramsch..<2*DIM('a) + length ramsch]))
         (list_of_eucl x @ ramsch @ list_of_eucl d)))) (at x)"
proof -
  have m_nth: "ia < max_Var_floatariths fas \<Longrightarrow> ia < DIM('a) + length ramsch" for ia
    using m by simp
  have m_nth': "ia < max_Var_floatarith (fas ! j) \<Longrightarrow> ia < DIM('a) + length ramsch" if "j < DIM('a)" for j ia
    using m_nth max_Var_floatariths_lessI that by auto

  have "((\<lambda>xa::'a. eucl_of_list
         (interpret_floatariths fas
           (list_updates [0..<DIM('a)] (list_of_eucl xa)
             (list_of_eucl x @ ramsch @ replicate DIM('a) 0)))::'a) has_derivative
 (\<lambda>d. eucl_of_list
        (interpret_floatariths
          (FDERIV_floatariths fas [0..<DIM('a)] (map Var [length ramsch + DIM('a)..<length ramsch + 2 * DIM('a)]))
          (list_updates [length ramsch + DIM('a)..<length ramsch + 2 * DIM('a)] (list_of_eucl d)
            (list_of_eucl x @ ramsch @ replicate DIM('a) 0)))))
 (at (eucl_of_env [0..<DIM('a)] (list_of_eucl x @ ramsch @ replicate DIM('a) 0)))"
    by (rule interpret_floatarith_FDERIV_floatariths_eucl_of_env[of
          "[0..<DIM('a)]" fas "list_of_eucl x@ramsch@replicate DIM('a) 0" "[length ramsch+DIM('a)..<length ramsch+2*DIM('a)]"])
       (auto intro!: iD[THEN isFDERIV_uptD] freshs_floatarith_max_Var_floatarithI isFDERIV_max_Var_congI[OF iD]
        max_Var_floatarith_le_max_Var_floatariths[THEN order_trans] m[THEN order_trans]
        freshs_floatariths_max_Var_floatarithsI simp: nth_append m add.commute less_diff_conv2 m_nth)
  moreover have "interpret_floatariths fas (list_updates [0..<DIM('a)] (list_of_eucl xa) (list_of_eucl x @ ramsch @ replicate DIM('a) 0)) =
    interpret_floatariths fas (list_of_eucl xa @ ramsch)" for xa::'a
    apply (auto intro!: nth_equalityI interpret_floatarith_max_Var_cong simp: )
    apply (auto simp: list_updates_nth nth_append dest: m_nth')
    done
  moreover have
    "(list_updates [DIM('a) + length ramsch..<length ramsch + 2 * DIM('a)]
        (list_of_eucl d)
        (list_of_eucl x @ ramsch @ replicate DIM('a) 0)) =
      (list_of_eucl x @ ramsch @ list_of_eucl d)" for d::'a
    by (auto simp: intro!: nth_equalityI simp: list_updates_nth nth_append)
  moreover have "(eucl_of_env [0..<DIM('a)] (list_of_eucl x @ ramsch @ replicate DIM('a) 0)) = x"
    by (auto intro!: euclidean_eqI[where 'a='a] simp: eucl_of_env_def eucl_of_list_inner nth_append)
  ultimately show ?thesis by (simp add: add.commute)
qed

lemma interpret_floatarith_FDERIV_floatariths:
  assumes iD: "isFDERIV DIM('a) [0..<DIM('a)] fas (list_of_eucl x)"
  assumes m: "max_Var_floatariths fas \<le> DIM('a)"
  assumes [simp]: "length fas = DIM('a)"
  shows "((\<lambda>x::'a::executable_euclidean_space.
    eucl_of_list
      (interpret_floatariths fas (list_of_eucl x))::'a) has_derivative
        (\<lambda>d. eucl_of_list (interpret_floatariths
         (FDERIV_floatariths fas [0..<DIM('a)] (map Var [DIM('a)..<2*DIM('a)]))
         (list_of_eucl x @ list_of_eucl d)))) (at x)"
  using interpret_floatarith_FDERIV_floatariths_append[where ramsch=Nil, simplified, OF assms]
  by simp

lemma continuous_on_min[continuous_intros]:
  fixes f g :: "'a::topological_space \<Rightarrow> 'b::linorder_topology"
  shows "continuous_on A f \<Longrightarrow> continuous_on A g \<Longrightarrow> continuous_on A (\<lambda>x. min (f x) (g x))"
  by (auto simp: continuous_on_def intro!: tendsto_min)

lemmas [continuous_intros] = continuous_on_max
lemma continuous_on_if_const[continuous_intros]:
  "continuous_on s f \<Longrightarrow> continuous_on s g \<Longrightarrow> continuous_on s (\<lambda>x. if p then f x else g x)"
  by (cases p) auto

lemma continuous_on_floatarith:
  assumes "continuous_on_floatarith fa" "length xs = DIM('a)" "distinct xs"
  shows "continuous_on UNIV (\<lambda>x. interpret_floatarith fa (list_updates xs (list_of_eucl (x::'a::executable_euclidean_space)) vs))"
  using assms
  by (induction fa)
    (auto intro!: continuous_intros split: if_splits simp: list_updates_nth list_of_eucl_nth_if)

fun open_form :: "form \<Rightarrow> bool" where
"open_form (Bound x a b f)  = False" |
"open_form (Assign x a f)   = False" |
"open_form (Less a b) \<longleftrightarrow> continuous_on_floatarith a \<and> continuous_on_floatarith b" |
"open_form (LessEqual a b)  = False" |
"open_form (AtLeastAtMost x a b) = False" |
"open_form (Conj f g) \<longleftrightarrow> open_form f \<and> open_form g" |
"open_form (Disj f g) \<longleftrightarrow> open_form f \<and> open_form g"

lemma open_form:
  assumes "open_form f" "length xs = DIM('a::executable_euclidean_space)" "distinct xs"
  shows "open (Collect (\<lambda>x::'a. interpret_form f (list_updates xs (list_of_eucl x) vs)))"
  using assms
  by (induction f) (auto intro!: open_Collect_less continuous_on_floatarith open_Collect_conj open_Collect_disj)

primrec isnFDERIV where
  "isnFDERIV N fas xs ds vs 0 = True"
| "isnFDERIV N fas xs ds vs (Suc n) \<longleftrightarrow>
    isFDERIV N xs (FDERIV_n_floatariths fas xs (map Var ds) n) vs \<and>
    isnFDERIV N fas xs ds vs n"

lemma one_add_square_eq_0: "1 + (x)\<^sup>2 \<noteq> (0::real)"
  by (sos "((R<1 + (([~1] * A=0) + (R<1 * (R<1 * [x]^2)))))")

lemma isDERIV_fold_const_fa[intro]:
  assumes "isDERIV x fa vs"
  shows "isDERIV x (fold_const_fa fa) vs"
  using assms
  apply (induction fa)
  subgoal by (auto simp: fold_const_fa.simps split: floatarith.splits option.splits)
  subgoal by (auto simp: fold_const_fa.simps split: floatarith.splits)
  subgoal by (auto simp: fold_const_fa.simps split: floatarith.splits option.splits)
  subgoal by (auto simp: fold_const_fa.simps split: floatarith.splits)
  subgoal by (auto simp: fold_const_fa.simps split: floatarith.splits)
  subgoal by (auto simp: fold_const_fa.simps split: floatarith.splits)
  subgoal by (auto simp: fold_const_fa.simps split: floatarith.splits)
  subgoal by (auto simp: fold_const_fa.simps split: floatarith.splits)
  subgoal by (auto simp: fold_const_fa.simps split: floatarith.splits)
  subgoal by (auto simp: fold_const_fa.simps split: floatarith.splits)
  subgoal by (auto simp: fold_const_fa.simps split: floatarith.splits)
  subgoal by (auto simp: fold_const_fa.simps split: floatarith.splits)
  subgoal by (auto simp: fold_const_fa.simps split: floatarith.splits)
  subgoal by (auto simp: fold_const_fa.simps split: floatarith.splits)
  subgoal for fa n
    by (cases n) (auto simp: fold_const_fa.simps split: floatarith.splits nat.splits)
  subgoal
    by (auto simp: fold_const_fa.simps split: floatarith.splits) (subst (asm) fold_const_fa[symmetric], force)+
  subgoal by (auto simp: fold_const_fa.simps split: floatarith.splits)
  subgoal by (auto simp: fold_const_fa.simps split: floatarith.splits)
  done

lemma isDERIV_fold_const_fa_minus[intro!]:
  assumes "isDERIV x (fold_const_fa fa) vs"
  shows "isDERIV x (fold_const_fa (Minus fa)) vs"
  using assms
  by (induction fa) (auto simp: fold_const_fa.simps split: floatarith.splits)

lemma isDERIV_fold_const_fa_plus[intro!]:
  assumes "isDERIV x (fold_const_fa fa) vs"
  assumes "isDERIV x (fold_const_fa fb) vs"
  shows "isDERIV x (fold_const_fa (Add fa fb)) vs"
  using assms
  by (induction fa)
    (auto simp: fold_const_fa.simps
      split: floatarith.splits option.splits)

lemma isDERIV_fold_const_fa_mult[intro!]:
  assumes "isDERIV x (fold_const_fa fa) vs"
  assumes "isDERIV x (fold_const_fa fb) vs"
  shows "isDERIV x (fold_const_fa (Mult fa fb)) vs"
  using assms
  by (induction fa)
    (auto simp: fold_const_fa.simps
      split: floatarith.splits option.splits)

lemma isDERIV_fold_const_fa_power[intro!]:
  assumes "isDERIV x (fold_const_fa fa) vs"
  shows "isDERIV x (fold_const_fa (fa ^\<^sub>e n)) vs"
  apply (cases n, simp add: fold_const_fa.simps split: floatarith.splits)
  using assms
  by (induction fa)
    (auto simp: fold_const_fa.simps split: floatarith.splits option.splits)

lemma isDERIV_fold_const_fa_inverse[intro!]:
  assumes "isDERIV x (fold_const_fa fa) vs"
  assumes "interpret_floatarith fa vs \<noteq> 0"
  shows "isDERIV x (fold_const_fa (Inverse fa)) vs"
  using assms
  by (simp add: fold_const_fa.simps)

lemma add_square_ne_zero[simp]: "(y::'a::linordered_idom) > 0 \<Longrightarrow> y + x\<^sup>2 \<noteq> 0"
  by auto (metis less_add_same_cancel2 power2_less_0)

lemma isDERIV_FDERIV_floatarith:
  assumes "isDERIV x fa vs" "\<And>i. i < length ds \<Longrightarrow> isDERIV x (ds ! i) vs"
  assumes [simp]: "length xs = length ds"
  shows "isDERIV x (FDERIV_floatarith fa xs ds) vs"
  using assms
  apply (induction fa)
  subgoal by (auto simp: FDERIV_floatarith_def isDERIV_inner_iff)
  subgoal by (auto simp: FDERIV_floatarith_def isDERIV_inner_iff)
  subgoal by (auto simp: FDERIV_floatarith_def isDERIV_inner_iff)
  subgoal by (auto simp: FDERIV_floatarith_def isDERIV_inner_iff)
  subgoal by (auto simp: FDERIV_floatarith_def isDERIV_inner_iff)
  subgoal by (auto simp: FDERIV_floatarith_def isDERIV_inner_iff)
  subgoal by (auto simp: FDERIV_floatarith_def isDERIV_inner_iff)
  subgoal by (auto simp: FDERIV_floatarith_def isDERIV_inner_iff)
  subgoal by (auto simp: FDERIV_floatarith_def isDERIV_inner_iff)
  subgoal by (auto simp: FDERIV_floatarith_def isDERIV_inner_iff)
  subgoal by (auto simp: FDERIV_floatarith_def isDERIV_inner_iff)
  subgoal by (auto simp: FDERIV_floatarith_def isDERIV_inner_iff)
  subgoal by (auto simp: FDERIV_floatarith_def isDERIV_inner_iff)
  subgoal by (auto simp: FDERIV_floatarith_def isDERIV_inner_iff)
  subgoal for fa n by (cases n) (auto simp: FDERIV_floatarith_def isDERIV_inner_iff)
  subgoal by (auto simp: FDERIV_floatarith_def isDERIV_inner_iff)
  subgoal by (auto simp: FDERIV_floatarith_def isDERIV_inner_iff)
  subgoal by (auto simp: FDERIV_floatarith_def isDERIV_inner_iff)
  done

lemma isDERIV_FDERIV_floatariths:
  assumes "isFDERIV N xs fas vs" "isFDERIV N xs ds vs" and [simp]: "length fas = length ds"
  shows "isFDERIV N xs (FDERIV_floatariths fas xs ds) vs"
  using assms
  by (auto simp: isFDERIV_def FDERIV_floatariths_def intro!: isDERIV_FDERIV_floatarith)

lemma isFDERIV_imp_isFDERIV_FDERIV_n:
  assumes "length fas = length ds"
  shows "isFDERIV N xs fas vs \<Longrightarrow> isFDERIV N xs ds vs \<Longrightarrow>
    isFDERIV N xs (FDERIV_n_floatariths fas xs ds n) vs"
  using assms
  by (induction n) (auto intro!: isDERIV_FDERIV_floatariths)

lemma isFDERIV_map_Var:
  assumes [simp]: "length ds = N" "length xs = N"
  shows "isFDERIV N xs (map Var ds) vs"
  by (auto simp: isFDERIV_def)

theorem isFDERIV_imp_isnFDERIV:
  assumes "isFDERIV N xs fas vs" and [simp]: "length fas = N" "length xs = N" "length ds = N"
  shows "isnFDERIV N fas xs ds vs n"
  using assms
  by (induction n) (auto intro!: isFDERIV_imp_isFDERIV_FDERIV_n isFDERIV_map_Var)

lemma eventually_isnFDERIV:
  assumes iD: "isnFDERIV DIM('a) fas [0..<DIM('a)] [DIM('a)..<2*DIM('a)] (list_of_eucl x @ list_of_eucl (d::'a)) n"
  assumes m: "max_Var_floatariths fas \<le> 2 * DIM('a::executable_euclidean_space)"
  shows "\<forall>\<^sub>F (x::'a) in at x. isnFDERIV DIM('a) fas [0..<DIM('a)] [DIM('a)..<2*DIM('a)] (list_of_eucl x @ list_of_eucl d) n"
  using iD
proof (induction n)
  case (Suc n)
  then have 1: "\<forall>\<^sub>F x in at x. isnFDERIV DIM('a) fas [0..<DIM('a)] [DIM('a)..<2 * DIM('a)] (list_of_eucl x @ list_of_eucl d) n"
    and 2: "isFDERIV DIM('a) [0..<DIM('a)] (FDERIV_n_floatariths fas [0..<DIM('a)] (map Var [DIM('a)..<2 * DIM('a)]) n)
      (list_of_eucl x @ list_of_eucl d)"
    by simp_all
  have "max_Var_floatariths (FDERIV_n_floatariths fas [0..<DIM('a)] (map Var [DIM('a)..<2 * DIM('a)]) n) \<le>
      DIM('a) + length (list_of_eucl d)"
    by (auto intro!: max_Var_floatarith_FDERIV_n_floatariths[THEN order_trans] m[THEN order_trans])
  from eventually_isFDERIV[OF 2 this] 1
  show ?case
    by eventually_elim simp
qed simp

lemma isFDERIV_open:
  assumes "max_Var_floatariths fas \<le> DIM('a)"
  shows "open {x::'a. isFDERIV DIM('a::executable_euclidean_space)  [0..<DIM('a)] fas (list_of_eucl x)}"
    (is "open (Collect ?s)")
proof (safe intro!: topological_space_class.openI)
  fix x::'a assume x: "?s x"
  with eventually_isFDERIV[where 'a='a, of fas x Nil]
  have "\<forall>\<^sub>F x in at x. x \<in> Collect ?s"
    by (auto simp: assms)
  then obtain S where "open S" "x \<in> S"
    "(\<forall>xa\<in>S. xa \<noteq> x \<longrightarrow> ?s xa)"
    unfolding eventually_at_topological
    by auto
  with x show "\<exists>T. open T \<and> x \<in> T \<and> T \<subseteq> Collect ?s"
    by (auto intro!: exI[where x=S])
qed

lemma interpret_floatarith_FDERIV_floatarith_eq:
  assumes [simp]: "length xs = DIM('a::executable_euclidean_space)" "length ds = DIM('a)"
  shows "interpret_floatarith (FDERIV_floatarith fa xs ds) vs =
    einterpret (map (\<lambda>x. DERIV_floatarith x fa) xs) vs \<bullet> (einterpret ds vs::'a)"
  by (auto simp: FDERIV_floatarith_def interpret_floatarith_inner_floatariths)

lemma
  interpret_floatariths_FDERIV_floatariths_cong:
  assumes [simp]: "length d1s = DIM('a::executable_euclidean_space)" "length d2s = DIM('a)" "length fas1 = length fas2"
  assumes fresh1: "freshs_floatariths fas1 d1s"
  assumes fresh2: "freshs_floatariths fas2 d2s"
  assumes eq1: "\<And>i. i < length fas1 \<Longrightarrow> interpret_floatariths (map (\<lambda>x. DERIV_floatarith x (fas1 ! i)) [0..<DIM('a)]) xs1 =
    interpret_floatariths (map (\<lambda>x. DERIV_floatarith x (fas2 ! i)) [0..<DIM('a)]) xs2"
  assumes eq2: "\<And>i. i < DIM('a) \<Longrightarrow> xs1 ! (d1s ! i) = xs2 ! (d2s ! i)"
  shows "interpret_floatariths (FDERIV_floatariths fas1 [0..<DIM('a)] (map floatarith.Var d1s)) xs1 =
    interpret_floatariths (FDERIV_floatariths fas2 [0..<DIM('a)] (map floatarith.Var d2s)) xs2"
proof -
  note eq1
  moreover have "interpret_floatariths (map Var d1s) (xs1) =
    interpret_floatariths (map Var d2s) (xs2)"
    by (auto intro!: nth_equalityI eq2)
  ultimately
  show ?thesis
    by (auto intro!: nth_equalityI simp: interpret_floatarith_FDERIV_floatarith_eq)
qed

lemma subst_floatarith_Var_DERIV_floatarith:
  assumes "\<And>x. x = n \<longleftrightarrow> s x = n"
  shows "subst_floatarith (\<lambda>x. Var (s x)) (DERIV_floatarith n fa) =
  DERIV_floatarith n (subst_floatarith (\<lambda>x. Var (s x)) fa)"
  using assms
proof (induction fa)
  case (Power fa n)
  then show ?case by (cases n) auto
qed force+

lemma subst_floatarith_inner_floatariths[simp]:
  assumes "length fs = length gs"
  shows "subst_floatarith s (inner_floatariths fs gs) =
      inner_floatariths (map (subst_floatarith s) fs) (map (subst_floatarith s) gs)"
  using assms
  by (induction rule: list_induct2) auto

fun_cases subst_floatarith_Num: "subst_floatarith s fa = Num y"
  and subst_floatarith_Add: "subst_floatarith s fa = Add x y"
  and subst_floatarith_Minus: "subst_floatarith s fa = Minus y"

lemma Num_eq_subst_Var[simp]: "Num x = subst_floatarith (\<lambda>x. Var (s x)) fa \<longleftrightarrow> fa = Num x"
  by (cases fa) auto

lemma Add_eq_subst_VarE:
  assumes "Add fa1 fa2 = subst_floatarith (\<lambda>x. Var (s x)) fa"
  obtains a1 a2 where "fa = Add a1 a2" "fa1 = subst_floatarith (\<lambda>x. Var (s x)) a1"
      "fa2 = subst_floatarith (\<lambda>x. Var (s x)) a2"
  using assms
  by (cases fa) auto

lemma subst_floatarith_eq_self[simp]: "subst_floatarith s f = f" if "max_Var_floatarith f = 0"
  using that by (induction f) auto

lemma fold_const_fa_unique: "False" if "(\<And>x. f = Num x)"
  using that[of 0] that[of 1]
  by auto

lemma zero_unique: False if "(\<And>x::float. x = 0)"
  using that[of 0] that[of 1]
  by auto

lemma fold_const_fa_Mult_eq_NumE:
  assumes "fold_const_fa (Mult a b) = Num x"
  obtains y z where "fold_const_fa a = Num y" "fold_const_fa b = Num z" "x = y * z"
  | y where "fold_const_fa a = Num 0" "x = 0"
  | y where "fold_const_fa b = Num 0" "x = 0"
  using assms
  by atomize_elim (auto simp: fold_const_fa.simps split!: option.splits if_splits
      elim!: dest_Num_fa_Some dest_Num_fa_None)

lemma fold_const_fa_Add_eq_NumE:
  assumes "fold_const_fa (Add a b) = Num x"
  obtains y z where "fold_const_fa a = Num y" "fold_const_fa b = Num z" "x = y + z"
  using assms
  by atomize_elim (auto simp: fold_const_fa.simps split!: option.splits if_splits
      elim!: dest_Num_fa_Some dest_Num_fa_None)

lemma subst_floatarith_Var_fold_const_fa[symmetric]:
  "fold_const_fa (subst_floatarith (\<lambda>x. Var (s x)) fa) =
  subst_floatarith (\<lambda>x. Var (s x)) (fold_const_fa fa)"
proof (induction fa)
  case (Add fa1 fa2)
  then show ?case
    apply (auto simp: fold_const_fa.simps
        split!: floatarith.splits option.splits if_splits
        elim!: dest_Num_fa_Some)
    apply (metis Num_eq_subst_Var dest_Num_fa.simps(1) option.simps(3))
    apply (metis Num_eq_subst_Var dest_Num_fa.simps(1) option.simps(3))
    apply (metis Num_eq_subst_Var dest_Num_fa.simps(1) option.simps(3))
    apply (metis Num_eq_subst_Var dest_Num_fa.simps(1) option.simps(3))
    apply (metis Num_eq_subst_Var dest_Num_fa.simps(1) option.simps(3))
    apply (metis Num_eq_subst_Var dest_Num_fa.simps(1) option.simps(3))
    apply (metis Num_eq_subst_Var dest_Num_fa.simps(1) option.simps(3))
    apply (metis Num_eq_subst_Var dest_Num_fa.simps(1) option.simps(3))
    apply (metis Num_eq_subst_Var dest_Num_fa.simps(1) option.simps(3))
    apply (metis Num_eq_subst_Var dest_Num_fa.simps(1) option.simps(3))
    done
next
  case (Mult fa1 fa2)
  then show ?case
    apply (auto simp: fold_const_fa.simps
        split!: floatarith.splits option.splits if_splits
        elim!: dest_Num_fa_Some)
    apply (metis Num_eq_subst_Var dest_Num_fa.simps(1) option.simps(3))
    apply (metis Num_eq_subst_Var dest_Num_fa.simps(1) option.simps(3))
    apply (metis Num_eq_subst_Var dest_Num_fa.simps(1) option.simps(3))
    apply (metis Num_eq_subst_Var dest_Num_fa.simps(1) option.simps(3))
    apply (metis Num_eq_subst_Var dest_Num_fa.simps(1) option.simps(3))
    apply (metis Num_eq_subst_Var dest_Num_fa.simps(1) option.simps(3))
    apply (metis Num_eq_subst_Var dest_Num_fa.simps(1) option.simps(3))
    apply (metis Num_eq_subst_Var dest_Num_fa.simps(1) option.simps(3))
    apply (metis Num_eq_subst_Var dest_Num_fa.simps(1) option.simps(3))
    apply (metis Num_eq_subst_Var dest_Num_fa.simps(1) option.simps(3))
    apply (metis Num_eq_subst_Var dest_Num_fa.simps(1) option.simps(3))
    apply (metis Num_eq_subst_Var dest_Num_fa.simps(1) option.simps(3))
    apply (metis Num_eq_subst_Var dest_Num_fa.simps(1) option.simps(3))
    apply (metis Num_eq_subst_Var dest_Num_fa.simps(1) option.simps(3))
    apply (metis Num_eq_subst_Var dest_Num_fa.simps(1) option.simps(3))
    done
next
  case (Min)
  then show ?case
    by (auto simp: fold_const_fa.simps split: floatarith.splits)
next
  case (Max)
  then show ?case
    by (auto simp: fold_const_fa.simps split: floatarith.splits)
qed (auto simp: fold_const_fa.simps
        split!: floatarith.splits option.splits if_splits
        elim!: dest_Num_fa_Some)

lemma subst_floatarith_eq_Num[simp]: "(subst_floatarith (\<lambda>x. Var (s x)) fa = Num x) \<longleftrightarrow> fa = Num x"
  by (induction fa) (auto simp: )

lemma fold_const_fa_subst_eq_Num0_iff[simp]:
  "fold_const_fa (subst_floatarith (\<lambda>x. Var (s x)) fa) = Num x \<longleftrightarrow> fold_const_fa fa = Num x"
  unfolding subst_floatarith_Var_fold_const_fa[symmetric]
  by simp

lemma subst_floatarith_Var_FDERIV_floatarith:
  assumes len: "length xs = DIM('a::executable_euclidean_space)" and [simp]: "length ds = DIM('a)"
  assumes eq: "\<And>x y. x \<in> set xs \<Longrightarrow> (y = x) = (s y = x)"
  shows "subst_floatarith (\<lambda>x. Var (s x)) (FDERIV_floatarith fa xs ds) =
    (FDERIV_floatarith (subst_floatarith (\<lambda>x. Var (s x)) fa) xs (map (subst_floatarith (\<lambda>x. Var (s x))) ds))"
proof -
  have [simp]: "\<And>x. x \<in> set xs \<Longrightarrow> subst_floatarith (\<lambda>x. Var (s x)) (DERIV_floatarith x fa1) =
    (DERIV_floatarith x (subst_floatarith (\<lambda>x. Var (s x)) fa1))"
    for fa1
    by (rule subst_floatarith_Var_DERIV_floatarith) (rule eq)
  have map_eq: "(map (\<lambda>xa. if xa = s x then Num 1 else Num 0) xs) =
      (map (\<lambda>xa. if xa = x then Num 1 else Num 0) xs)"
    for x
    apply (subst map_eq_conv)
    using eq[of x x] eq[of "s x"]
    by (auto simp: )
  show ?thesis
    using len
    by (induction fa)
      (auto simp: FDERIV_floatarith_def o_def if_distrib
        subst_floatarith_Var_fold_const_fa fold_const_fa.simps(18) map_eq
        cong: map_cong if_cong)
qed

lemma subst_floatarith_Var_FDERIV_n_nth:
  assumes len: "length xs = DIM('a::executable_euclidean_space)" and [simp]: "length ds = DIM('a)"
  assumes eq: "\<And>x y. x \<in> set xs \<Longrightarrow> (y = x) = (s y = x)"
  assumes [simp]: "i < length fas"
  shows "subst_floatarith (\<lambda>x. Var (s x)) (FDERIV_n_floatariths fas xs ds n ! i) =
    (FDERIV_n_floatariths (map (subst_floatarith (\<lambda>x. Var (s x))) fas) xs (map (subst_floatarith (\<lambda>x. Var (s x))) ds) n ! i)"
proof (induction n)
  case (Suc n)
  show ?case
    by (simp add: subst_floatarith_Var_FDERIV_floatarith[OF len _ eq] Suc.IH[symmetric])
qed simp

lemma subst_floatarith_Var_max_Var_floatarith:
  assumes "\<And>i. i < max_Var_floatarith fa \<Longrightarrow> s i = i"
  shows "subst_floatarith (\<lambda>i. Var (s i)) fa = fa"
  using assms
  by (induction fa) auto

lemma interpret_floatarith_subst_floatarith_idem:
  assumes mv: "max_Var_floatarith fa \<le> length vs"
  assumes idem: "\<And>j. j < max_Var_floatarith fa \<Longrightarrow> vs ! s j = vs ! j"
  shows "interpret_floatarith (subst_floatarith (\<lambda>i. Var (s i)) fa) vs = interpret_floatarith fa vs"
  using assms
  by (induction fa) auto

lemma isDERIV_subst_Var_floatarith:
  assumes mv: "max_Var_floatarith fa \<le> length vs"
  assumes idem: "\<And>j. j < max_Var_floatarith fa \<Longrightarrow> vs ! s j = vs ! j"
  assumes "\<And>j. s j = i \<longleftrightarrow> j = i"
  shows "isDERIV i (subst_floatarith (\<lambda>i. Var (s i)) fa) vs = isDERIV i fa vs"
  using mv idem
proof (induction fa)
  case (Power fa n)
  then show ?case by (cases n) auto
qed (auto simp: interpret_floatarith_subst_floatarith_idem)

lemma isFDERIV_subst_Var_floatarith:
  assumes mv: "max_Var_floatariths fas \<le> length vs"
  assumes idem: "\<And>j. j < max_Var_floatariths fas \<Longrightarrow> vs ! (s j) = vs ! j"
  assumes "\<And>i j. i \<in> set xs \<Longrightarrow> s j = i \<longleftrightarrow> j = i"
  shows "isFDERIV n xs (map (subst_floatarith (\<lambda>i. Var (s i))) fas) vs = isFDERIV n xs fas vs"
proof -
  have mv: "\<And>i. i < length fas \<Longrightarrow> max_Var_floatarith (fas ! i) \<le> length vs"
    apply (rule order_trans[OF _ mv])
    by (intro max_Var_floatarith_le_max_Var_floatariths_nth)
  have idem: "\<And>i j. i < length fas \<Longrightarrow> j < max_Var_floatarith (fas ! i) \<Longrightarrow> vs ! s j = vs ! j"
    using idem
    by (auto simp: dest!: max_Var_floatariths_lessI)
  show ?thesis
    unfolding isFDERIV_def
    using mv idem assms(3)
    by (auto simp: isDERIV_subst_Var_floatarith)
qed

lemma interpret_floatariths_append[simp]:
  "interpret_floatariths (xs @ ys) vs = interpret_floatariths xs vs @ interpret_floatariths ys vs"
  by (induction xs) auto

lemma not_fresh_inner_floatariths:
  assumes "length xs = length ys"
  shows "\<not> fresh_floatarith (inner_floatariths xs ys) i \<longleftrightarrow> \<not>fresh_floatariths xs i \<or> \<not>fresh_floatariths ys i"
  using assms
  by (induction xs ys rule: list_induct2) auto

lemma fresh_inner_floatariths:
  assumes "length xs = length ys"
  shows "fresh_floatarith (inner_floatariths xs ys) i \<longleftrightarrow> fresh_floatariths xs i \<and> fresh_floatariths ys i"
  using not_fresh_inner_floatariths assms by auto

lemma not_fresh_floatariths_map:
  " \<not> fresh_floatariths (map f xs) i \<longleftrightarrow> (\<exists>x \<in> set xs. \<not>fresh_floatarith (f x) i)"
  by (induction xs) auto

lemma fresh_floatariths_map:
  " fresh_floatariths (map f xs) i \<longleftrightarrow> (\<forall>x \<in> set xs. fresh_floatarith (f x) i)"
  by (induction xs) auto

lemma fresh_floatarith_fold_const_fa: "fresh_floatarith fa i \<Longrightarrow> fresh_floatarith (fold_const_fa fa) i"
  by (induction fa) (auto simp: fold_const_fa.simps split: floatarith.splits option.splits)

lemma fresh_floatarith_fold_const_fa_Add[intro!]:
  assumes "fresh_floatarith (fold_const_fa a) i" "fresh_floatarith (fold_const_fa b) i"
  shows "fresh_floatarith (fold_const_fa (Add a b)) i"
  using assms
  by (auto simp: fold_const_fa.simps split!: floatarith.splits option.splits)

lemma fresh_floatarith_fold_const_fa_Mult[intro!]:
  assumes "fresh_floatarith (fold_const_fa a) i" "fresh_floatarith (fold_const_fa b) i"
  shows "fresh_floatarith (fold_const_fa (Mult a b)) i"
  using assms
  by (auto simp: fold_const_fa.simps split!: floatarith.splits option.splits)

lemma fresh_floatarith_fold_const_fa_Minus[intro!]:
  assumes "fresh_floatarith (fold_const_fa b) i"
  shows "fresh_floatarith (fold_const_fa (Minus b)) i"
  using assms
  by (auto simp: fold_const_fa.simps split!: floatarith.splits)

lemma fresh_FDERIV_floatarith:
  "fresh_floatarith ode_e i \<Longrightarrow> fresh_floatariths ds i
  \<Longrightarrow> length ds = DIM('a)
  \<Longrightarrow> fresh_floatarith (FDERIV_floatarith ode_e [0..<DIM('a::executable_euclidean_space)] ds) i"
proof (induction ode_e)
  case (Power ode_e n)
  then show ?case by (cases n) (auto simp: FDERIV_floatarith_def fresh_inner_floatariths fresh_floatariths_map fresh_floatarith_fold_const_fa)
qed (auto simp: FDERIV_floatarith_def fresh_inner_floatariths fresh_floatariths_map fresh_floatarith_fold_const_fa)

lemma not_fresh_FDERIV_floatarith:
  "\<not> fresh_floatarith (FDERIV_floatarith ode_e [0..<DIM('a::executable_euclidean_space)] ds) i
  \<Longrightarrow> length ds = DIM('a)
  \<Longrightarrow> \<not>fresh_floatarith ode_e i \<or> \<not>fresh_floatariths ds i"
  using fresh_FDERIV_floatarith by auto

lemma not_fresh_FDERIV_floatariths:
  "\<not> fresh_floatariths (FDERIV_floatariths ode_e [0..<DIM('a::executable_euclidean_space)] ds) i \<Longrightarrow>
  length ds = DIM('a) \<Longrightarrow> \<not>fresh_floatariths ode_e i \<or> \<not>fresh_floatariths ds i"
  by (induction ode_e) (auto simp: FDERIV_floatariths_def dest!: not_fresh_FDERIV_floatarith)

lemma isDERIV_FDERIV_floatarith_linear:
  fixes x h::"'a::executable_euclidean_space"
  assumes "\<And>k. k < DIM('a) \<Longrightarrow> isDERIV i (DERIV_floatarith k fa) xs"
  assumes "max_Var_floatarith fa \<le> DIM('a)"
  assumes [simp]: "length xs = DIM('a)" "length hs = DIM('a)"
  shows "isDERIV i (FDERIV_floatarith fa [0..<DIM('a)] (map Var [DIM('a)..<2 * DIM('a)]))
            (xs @ hs)"
  using assms
  apply (auto simp: FDERIV_floatarith_def isDERIV_inner_iff)
  apply (rule isDERIV_max_Var_floatarithI) apply force
  apply (auto simp: nth_append)
  by (metis add_diff_inverse_nat leD max_Var_floatarith_DERIV_floatarith
      max_Var_floatarith_fold_const_fa trans_le_add1)

lemma
  isFDERIV_FDERIV_floatariths_linear:
  fixes x h::"'a::executable_euclidean_space"
  assumes "\<And>i j k.
       i < DIM('a) \<Longrightarrow>
       j < DIM('a) \<Longrightarrow> k < DIM('a) \<Longrightarrow> isDERIV i (DERIV_floatarith k (fas ! j)) (xs)"
  assumes [simp]: "length fas = DIM('a::executable_euclidean_space)"
  assumes [simp]: "length xs = DIM('a)" "length hs = DIM('a)"
  assumes "max_Var_floatariths fas \<le> DIM('a)"
  shows "isFDERIV DIM('a) [0..<DIM('a::executable_euclidean_space)]
     (FDERIV_floatariths fas [0..<DIM('a)] (map floatarith.Var [DIM('a)..<2 * DIM('a)]))
     (xs @ hs)"
  apply (auto simp: isFDERIV_def intro!: isDERIV_FDERIV_floatarith_linear assms)
  using assms(5) max_Var_floatariths_lessI not_le_imp_less by fastforce

definition isFDERIV_approx where
  "isFDERIV_approx p n xs fas vs =
    ((\<forall>i<n. \<forall>j<n. isDERIV_approx p (xs ! i) (fas ! j) vs) \<and> length fas = n \<and> length xs = n)"

lemma isFDERIV_approx:
  "bounded_by vs VS \<Longrightarrow> isFDERIV_approx prec n xs fas VS \<Longrightarrow> isFDERIV n xs fas vs"
  by (auto simp: isFDERIV_approx_def isFDERIV_def intro!: isDERIV_approx)

primrec isnFDERIV_approx where
  "isnFDERIV_approx p N fas xs ds vs 0 = True"
| "isnFDERIV_approx p N fas xs ds vs (Suc n) \<longleftrightarrow>
    isFDERIV_approx p N xs (FDERIV_n_floatariths fas xs (map Var ds) n) vs \<and>
    isnFDERIV_approx p N fas xs ds vs n"

lemma isnFDERIV_approx:
  "bounded_by vs VS \<Longrightarrow> isnFDERIV_approx prec N fas xs ds VS n \<Longrightarrow> isnFDERIV N fas xs ds vs n"
  by (induction n) (auto intro!: isFDERIV_approx)

fun plain_floatarith::"nat \<Rightarrow> floatarith \<Rightarrow> bool" where
  "plain_floatarith N (floatarith.Add a b) \<longleftrightarrow> plain_floatarith N a \<and> plain_floatarith N b"
| "plain_floatarith N (floatarith.Mult a b) \<longleftrightarrow> plain_floatarith N a \<and> plain_floatarith N b"
| "plain_floatarith N (floatarith.Minus a) \<longleftrightarrow> plain_floatarith N a"
| "plain_floatarith N (floatarith.Pi) \<longleftrightarrow> True"
| "plain_floatarith N (floatarith.Num n) \<longleftrightarrow> True"
| "plain_floatarith N (floatarith.Var i) \<longleftrightarrow> i < N"
| "plain_floatarith N (floatarith.Max a b) \<longleftrightarrow> plain_floatarith N a \<and> plain_floatarith N b"
| "plain_floatarith N (floatarith.Min a b) \<longleftrightarrow> plain_floatarith N a \<and> plain_floatarith N b"
| "plain_floatarith N (floatarith.Power a n) \<longleftrightarrow> plain_floatarith N a"
| "plain_floatarith N (floatarith.Cos a) \<longleftrightarrow> False" \<comment> \<open>TODO: should be plain!\<close>
| "plain_floatarith N (floatarith.Arctan a) \<longleftrightarrow> False" \<comment> \<open>TODO: should be plain!\<close>
| "plain_floatarith N (floatarith.Abs a) \<longleftrightarrow> plain_floatarith N a"
| "plain_floatarith N (floatarith.Exp a) \<longleftrightarrow> False" \<comment> \<open>TODO: should be plain!\<close>
| "plain_floatarith N (floatarith.Sqrt a) \<longleftrightarrow> False" \<comment> \<open>TODO: should be plain!\<close>
| "plain_floatarith N (floatarith.Floor a) \<longleftrightarrow> plain_floatarith N a"

| "plain_floatarith N (floatarith.Powr a b) \<longleftrightarrow> False"
| "plain_floatarith N (floatarith.Inverse a) \<longleftrightarrow> False"
| "plain_floatarith N (floatarith.Ln a) \<longleftrightarrow> False"

lemma plain_floatarith_approx_not_None:
  assumes "plain_floatarith N fa" "N \<le> length XS" "\<And>i. i < N \<Longrightarrow> XS ! i \<noteq> None"
  shows "approx p fa XS \<noteq> None"
  using assms
  by (induction fa)
    (auto simp: Let_def split_beta' prod_eq_iff approx.simps)


definition "Rad_of w = w * (Pi / Num 180)"
lemma interpret_Rad_of[simp]: "interpret_floatarith (Rad_of w) xs = rad_of (interpret_floatarith w xs)"
  by (auto simp: Rad_of_def rad_of_def)

definition "Deg_of w = Num 180 * w / Pi"
lemma interpret_Deg_of[simp]: "interpret_floatarith (Deg_of w) xs = deg_of (interpret_floatarith w xs)"
  by (auto simp: Deg_of_def deg_of_def inverse_eq_divide)

unbundle no_floatarith_notation

end
