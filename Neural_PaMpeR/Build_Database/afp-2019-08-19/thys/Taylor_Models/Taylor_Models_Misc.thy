theory Taylor_Models_Misc
  imports
    "HOL-Library.Float"
    "HOL-Library.Function_Algebras"
    "HOL-Decision_Procs.Approximation"
    "Affine_Arithmetic.Floatarith_Expression"
begin

text \<open>This theory contains anything that doesn't belong anywhere else.\<close>

lemma of_nat_real_float_equiv: "(of_nat n :: real) = (of_nat n :: float)"
  by (induction n, simp_all add: of_nat_def)

lemma fact_real_float_equiv: "(fact n :: float) = (fact n :: real)"
  by (induction n) simp_all

lemma Some_those_length:
  "those ys = Some xs \<Longrightarrow> length xs = length ys"
  by (induction ys arbitrary: xs) (auto split: option.splits)

lemma those_eq_None_iff: "those ys = None \<longleftrightarrow> None \<in> set ys"
  by (induction ys) (auto simp: split: option.splits)

lemma those_eq_Some_iff: "those ys = (Some xs) \<longleftrightarrow> (ys = map Some xs)"
  by (induction ys arbitrary: xs) (auto simp: split: option.splits)

lemma Some_those_nth:
  assumes "those ys = Some xs"
  assumes "i < length xs"
  shows "Some (xs!i) = ys!i"
  using Some_those_length[OF assms(1)] assms
  by (induction xs ys arbitrary: i rule: list_induct2)
    (auto split: option.splits nat.splits simp: nth_Cons)

lemma fun_pow: "f^n = (\<lambda>x. (f x)^n)"
by (induction n, simp_all)

context includes floatarith_notation begin

text \<open>Translate floatarith expressions by a vector of floats.\<close>
fun fa_translate :: "float list \<Rightarrow> floatarith \<Rightarrow> floatarith"
where "fa_translate v (Add a b) = Add (fa_translate v a) (fa_translate v b)"
    | "fa_translate v (Minus a) = Minus (fa_translate v a)"
    | "fa_translate v (Mult a b) = Mult (fa_translate v a) (fa_translate v b)"
    | "fa_translate v (Inverse a) = Inverse (fa_translate v a)"
    | "fa_translate v (Cos a) = Cos (fa_translate v a)"
    | "fa_translate v (Arctan a) = Arctan (fa_translate v a)"
    | "fa_translate v (Min a b) = Min (fa_translate v a) (fa_translate v b)"
    | "fa_translate v (Max a b) = Max (fa_translate v a) (fa_translate v b)"
    | "fa_translate v (Abs a) = Abs (fa_translate v a)"
    | "fa_translate v (Sqrt a) = Sqrt (fa_translate v a)"
    | "fa_translate v (Exp a) = Exp (fa_translate v a)"
    | "fa_translate v (Ln a) = Ln (fa_translate v a)"
    | "fa_translate v (Var n) = Add (Var n) (Num (v!n))"
    | "fa_translate v (Power a n) = Power (fa_translate v a) n"
    | "fa_translate v (Powr a b) = Powr (fa_translate v a) (fa_translate v b)"
    | "fa_translate v (Floor x) = Floor (fa_translate v x)"
    | "fa_translate v (Num c) = Num c"
    | "fa_translate v Pi = Pi"

lemma fa_translate_correct:
  assumes "max_Var_floatarith f \<le> length I"
  assumes "length v = length I"
  shows "interpret_floatarith (fa_translate v f) I = interpret_floatarith f (map2 (+) I v)"
  using assms
  by (induction f, simp_all)

primrec vars_floatarith where
  "vars_floatarith (Add a b) = (vars_floatarith a) \<union> (vars_floatarith b)"
| "vars_floatarith (Mult a b) = (vars_floatarith a) \<union> (vars_floatarith b)"
| "vars_floatarith (Inverse a) = vars_floatarith a"
| "vars_floatarith (Minus a) = vars_floatarith a"
| "vars_floatarith (Num a) = {}"
| "vars_floatarith (Var i) = {i}"
| "vars_floatarith (Cos a) = vars_floatarith a"
| "vars_floatarith (Arctan a) = vars_floatarith a"
| "vars_floatarith (Abs a) = vars_floatarith a"
| "vars_floatarith (Max a b) = (vars_floatarith a) \<union> (vars_floatarith b)"
| "vars_floatarith (Min a b) = (vars_floatarith a) \<union> (vars_floatarith b)"
| "vars_floatarith (Pi) = {}"
| "vars_floatarith (Sqrt a) = vars_floatarith a"
| "vars_floatarith (Exp a) = vars_floatarith a"
| "vars_floatarith (Powr a b) = (vars_floatarith a) \<union> (vars_floatarith b)"
| "vars_floatarith (Ln a) = vars_floatarith a"
| "vars_floatarith (Power a n) = vars_floatarith a"
| "vars_floatarith (Floor a) = vars_floatarith a"       

lemma finite_vars_floatarith[simp]: "finite (vars_floatarith x)"
  by (induction x) auto

end

lemma max_Var_floatarith_eq_Max_vars_floatarith:
  "max_Var_floatarith fa = (if vars_floatarith fa = {} then 0 else Suc (Max (vars_floatarith fa)))"
  by (induction fa) (auto split: if_splits simp: Max_Un Max_eq_iff max_def)

end
