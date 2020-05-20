(*
  Theory: PDF_Semantics.thy
  Author: Manuel Eberl

  Defines the expressions of the PDF language and their typing rules and semantics
  as well as a number of standard semantics-related theorems such as substitution.
*)

theory PDF_Semantics
imports PDF_Values
begin

lemma measurable_subprob_algebra_density:
  assumes "sigma_finite_measure N"
  assumes "space N \<noteq> {}"
  assumes [measurable]: "case_prod f \<in> borel_measurable (M \<Otimes>\<^sub>M N)"
  assumes "\<And>x. x \<in> space M \<Longrightarrow> (\<integral>\<^sup>+y. f x y \<partial>N) \<le> 1"
  shows "(\<lambda>x. density N (f x)) \<in> measurable M (subprob_algebra N)"
proof (rule measurable_subprob_algebra)
  fix x assume "x \<in> space M"
  with assms show "subprob_space (density N (f x))"
    by (intro subprob_spaceI) (auto simp: emeasure_density cong: nn_integral_cong')
next
  interpret sigma_finite_measure N by fact
  fix X assume X: "X \<in> sets N"
  hence "(\<lambda>x. (\<integral>\<^sup>+y. f x y * indicator X y \<partial>N)) \<in> borel_measurable M" by simp
  moreover from X and assms have
      "\<And>x. x \<in> space M \<Longrightarrow> emeasure (density N (f x)) X = (\<integral>\<^sup>+y. f x y * indicator X y \<partial>N)"
    by (simp add: emeasure_density)
  ultimately show "(\<lambda>x. emeasure (density N (f x)) X) \<in> borel_measurable M"
    by (simp only: cong: measurable_cong)
qed simp_all

section \<open>Built-in Probability Distributions\<close>

subsection \<open>Bernoulli\<close>

definition bernoulli_density :: "real \<Rightarrow> bool \<Rightarrow> ennreal" where
  "bernoulli_density p b = (if p \<in> {0..1} then (if b then p else 1 - p) else 0)"

definition bernoulli :: "val \<Rightarrow> val measure" where
  "bernoulli p = density BOOL (bernoulli_density (extract_real p) o extract_bool)"

lemma measurable_bernoulli_density[measurable]:
  "case_prod bernoulli_density \<in> borel_measurable (borel \<Otimes>\<^sub>M count_space UNIV)"
  unfolding bernoulli_density_def[abs_def] by measurable

lemma measurable_bernoulli[measurable]: "bernoulli \<in> measurable REAL (subprob_algebra BOOL)"
  unfolding bernoulli_def[abs_def]
  by (auto intro!: measurable_subprob_algebra_density
           simp: measurable_split_conv nn_integral_BoolVal bernoulli_density_def
             ennreal_plus[symmetric]
           simp del: ennreal_plus)

subsection \<open>Uniform\<close>

definition uniform_real_density :: "real \<times> real \<Rightarrow> real \<Rightarrow> ennreal" where
  "uniform_real_density \<equiv> \<lambda>(a,b) x. ennreal (if a < b \<and> x \<in> {a..b} then inverse (b - a) else 0)"

definition uniform_int_density :: "int \<times> int \<Rightarrow> int \<Rightarrow> ennreal" where
  "uniform_int_density \<equiv> \<lambda>(a,b) x. (if x \<in> {a..b} then inverse (nat (b - a + 1)) else 0)"

lemma measurable_uniform_density_int[measurable]:
  "(case_prod uniform_int_density)
       \<in> borel_measurable ((count_space UNIV \<Otimes>\<^sub>M count_space UNIV) \<Otimes>\<^sub>M count_space UNIV)"
  by (simp add: pair_measure_countable)

lemma measurable_uniform_density_real[measurable]:
  "(case_prod uniform_real_density) \<in> borel_measurable (borel \<Otimes>\<^sub>M borel)"
proof-
  have "(case_prod uniform_real_density) =
            (\<lambda>x. uniform_real_density (fst (fst x), snd (fst x)) (snd x))"
      by (rule ext) (simp split: prod.split)
  also have "... \<in> borel_measurable (borel \<Otimes>\<^sub>M borel)"
      unfolding uniform_real_density_def
      by (simp only: prod.case) (simp add: borel_prod[symmetric])
  finally show ?thesis .
qed

definition uniform_int :: "val \<Rightarrow> val measure" where
  "uniform_int = map_int_pair (\<lambda>l u. density INTEG (uniform_int_density (l,u) o extract_int)) (\<lambda>_. undefined)"

definition uniform_real :: "val \<Rightarrow> val measure" where
  "uniform_real = map_real_pair (\<lambda>l u. density REAL (uniform_real_density (l,u) o extract_real)) (\<lambda>_. undefined)"

lemma if_bounded: "(if a \<le> i \<and> i \<le> b then v else 0) = (v::real) * indicator {a .. b} i"
  by auto

lemma measurable_uniform_int[measurable]:
  "uniform_int \<in> measurable (PRODUCT INTEG INTEG) (subprob_algebra INTEG)"
  unfolding uniform_int_def
proof (rule measurable measurable_subprob_algebra_density)+
  fix x :: "int \<times> int"

  show "integral\<^sup>N INTEG (uniform_int_density (fst x, snd x) \<circ> extract_int) \<le> 1"
  proof cases
    assume "fst x \<le> snd x" then show ?thesis
      by (cases x)
         (simp add: uniform_int_density_def comp_def nn_integral_IntVal nn_integral_cmult
                    nn_integral_set_ennreal[symmetric] ennreal_of_nat_eq_real_of_nat
                    if_bounded[where 'a=int] ennreal_mult[symmetric]
               del: ennreal_plus)
  qed (simp add: uniform_int_density_def comp_def split_beta' if_bounded[where 'a=int])
qed (auto simp: comp_def)

lemma density_cong':
  "(\<And>x. x \<in> space M \<Longrightarrow> f x = g x) \<Longrightarrow> density M f = density M g"
  unfolding density_def
  by (auto dest: sets.sets_into_space intro!: nn_integral_cong measure_of_eq)

lemma measurable_uniform_real[measurable]:
  "uniform_real \<in> measurable (PRODUCT REAL REAL) (subprob_algebra REAL)"
  unfolding uniform_real_def
proof (rule measurable measurable_subprob_algebra_density)+
  fix x :: "real \<times> real"
  obtain l u where [simp]: "x = (l, u)"
    by (cases x) auto
  show "(\<integral>\<^sup>+y. (uniform_real_density (fst x, snd x) o extract_real) y \<partial>REAL) \<le> 1"
  proof cases
    assume "l < u" then show ?thesis
      by (simp add: nn_integral_RealVal uniform_real_density_def if_bounded nn_integral_cmult
                    nn_integral_set_ennreal[symmetric] ennreal_mult[symmetric])
  qed (simp add: uniform_real_density_def comp_def)
qed (auto simp: comp_def borel_prod)

subsection \<open>Gaussian\<close>

definition gaussian_density :: "real \<times> real \<Rightarrow> real \<Rightarrow> ennreal" where
  "gaussian_density \<equiv>
      \<lambda>(m,s) x. (if s > 0 then exp (-(x - m)\<^sup>2 / (2 * s\<^sup>2)) / sqrt (2 * pi * s\<^sup>2) else 0)"

lemma measurable_gaussian_density[measurable]:
  "case_prod gaussian_density \<in> borel_measurable (borel \<Otimes>\<^sub>M borel)"
proof-
  have "case_prod gaussian_density =
              (\<lambda>(x,y). (if snd x > 0 then exp (-((y - fst x)^2) / (2 * snd x^2)) /
                             sqrt (2 * pi * snd x^2) else 0))"
    unfolding gaussian_density_def by (intro ext) (simp split: prod.split)
  also have "... \<in> borel_measurable (borel \<Otimes>\<^sub>M borel)"
    by (simp add: borel_prod[symmetric])
  finally show ?thesis .
qed

definition gaussian :: "val \<Rightarrow> val measure" where
  "gaussian = map_real_pair (\<lambda>m s. density REAL (gaussian_density (m,s) o extract_real)) undefined"

lemma measurable_gaussian[measurable]: "gaussian \<in> measurable (PRODUCT REAL REAL) (subprob_algebra REAL)"
  unfolding gaussian_def
proof (rule measurable measurable_subprob_algebra_density)+
  fix x :: "real \<times> real"
  show "integral\<^sup>N (stock_measure REAL) (gaussian_density (fst x, snd x) \<circ> extract_real) \<le> 1"
  proof cases
    assume "snd x > 0"
    then have "integral\<^sup>N lborel (gaussian_density x) = (\<integral>\<^sup>+y. normal_density (fst x) (snd x) y \<partial>lborel)"
      by (auto simp add: gaussian_density_def normal_density_def split_beta' intro!: nn_integral_cong)
    also have "\<dots> = 1"
      using \<open>snd x > 0\<close>
      by (subst nn_integral_eq_integral) (auto intro!: normal_density_nonneg)
    finally show ?thesis
      by (cases x) (simp add: nn_integral_RealVal comp_def)
  next
    assume "\<not> snd x > 0" then show ?thesis
      by (cases x)
         (simp add: nn_integral_RealVal comp_def gaussian_density_def zero_ennreal_def[symmetric])
  qed
qed (auto simp: comp_def borel_prod)

subsection \<open>Poisson\<close>

definition poisson_density' :: "real \<Rightarrow> int \<Rightarrow> ennreal" where
  "poisson_density' rate k = pmf (poisson_pmf rate) (nat k) * indicator ({0 <..} \<times> {0..}) (rate, k)"

lemma measurable_poisson_density'[measurable]:
    "case_prod poisson_density' \<in> borel_measurable (borel \<Otimes>\<^sub>M count_space UNIV)"
proof -
  have "case_prod poisson_density' =
    (\<lambda>(rate, k). rate ^ nat k / real_of_nat (fact (nat k)) * exp (-rate) * indicator ({0 <..} \<times> {0..}) (rate, k))"
    by (auto split: split_indicator simp: fun_eq_iff poisson_density'_def)
  then show ?thesis
    by simp
qed

definition poisson :: "val \<Rightarrow> val measure" where
  "poisson rate = density INTEG (poisson_density' (extract_real rate) o extract_int)"

lemma measurable_poisson[measurable]: "poisson \<in> measurable REAL (subprob_algebra INTEG)"
  unfolding poisson_def[abs_def]
proof (rule measurable measurable_subprob_algebra_density)+
  fix r :: real
  have [simp]: "nat ` {0..} = UNIV"
    by (auto simp: image_iff intro!: bexI[of _ "int x" for x])

  { assume "0 < r"
    then have "(\<integral>\<^sup>+ x. ennreal (r ^ nat x * exp (- r) * indicator ({0<..} \<times> {0..}) (r, x) / (fact (nat x))) \<partial>count_space UNIV)
      = (\<integral>\<^sup>+ x. ennreal (pmf (poisson_pmf r) (nat x)) \<partial>count_space {0 ..})"
      by (auto intro!: nn_integral_cong simp add: nn_integral_count_space_indicator split: split_indicator)
    also have "\<dots> = 1"
      using measure_pmf.emeasure_space_1[of "poisson_pmf r"]
      by (subst nn_integral_pmf') (auto simp: inj_on_def)
    finally have "(\<integral>\<^sup>+ x. ennreal (r ^ nat x * exp (- r) * indicator ({0<..} \<times> {0..}) (r, x) / (fact (nat x))) \<partial>count_space UNIV) = 1"
      . }
  then show "integral\<^sup>N INTEG (poisson_density' r \<circ> extract_int) \<le> 1"
    by (cases "0 < r")
       (auto simp: nn_integral_IntVal poisson_density'_def zero_ennreal_def[symmetric])
qed (auto simp: comp_def)

section \<open>Source Language Syntax and Semantics\<close>

subsection \<open>Expressions\<close>

class expr = fixes free_vars :: "'a \<Rightarrow> vname set"

datatype pdf_dist = Bernoulli | UniformInt | UniformReal | Poisson | Gaussian

datatype pdf_operator = Fst | Snd | Add | Mult | Minus | Less | Equals | And | Not | Or | Pow |
                        Sqrt | Exp | Ln | Fact | Inverse | Pi | Cast pdf_type

datatype expr =
      Var vname
    | Val val
    | LetVar expr expr ("LET _ IN _" [0, 60] 61)
    | Operator pdf_operator expr (infixl "$$" 999)
    | Pair expr expr  ("<_ ,  _>"  [0, 60] 1000)
    | Random pdf_dist expr
    | IfThenElse expr expr expr ("IF _ THEN _ ELSE _" [0, 0, 70] 71)
    | Fail pdf_type

type_synonym tyenv = "vname \<Rightarrow> pdf_type"

instantiation expr :: expr
begin

primrec free_vars_expr :: "expr \<Rightarrow> vname set" where
  "free_vars_expr (Var x) = {x}"
| "free_vars_expr (Val _) = {}"
| "free_vars_expr (LetVar e1 e2) = free_vars_expr e1 \<union> Suc -` free_vars_expr e2"
| "free_vars_expr (Operator _ e) = free_vars_expr e"
| "free_vars_expr (<e1, e2>) = free_vars_expr e1 \<union> free_vars_expr e2"
| "free_vars_expr (Random _ e) = free_vars_expr e"
| "free_vars_expr (IF b THEN e1 ELSE e2) =
       free_vars_expr b \<union> free_vars_expr e1 \<union> free_vars_expr e2"
| "free_vars_expr (Fail _) = {}"

instance ..
end

primrec free_vars_expr_code :: "expr \<Rightarrow> vname set" where
  "free_vars_expr_code (Var x) = {x}"
| "free_vars_expr_code (Val _) = {}"
| "free_vars_expr_code (LetVar e1 e2) =
      free_vars_expr_code e1 \<union> (\<lambda>x. x - 1) ` (free_vars_expr_code e2 - {0})"
| "free_vars_expr_code (Operator _ e) = free_vars_expr_code e"
| "free_vars_expr_code (<e1, e2>) = free_vars_expr_code e1 \<union> free_vars_expr_code e2"
| "free_vars_expr_code (Random _ e) = free_vars_expr_code e"
| "free_vars_expr_code (IF b THEN e1 ELSE e2) =
       free_vars_expr_code b \<union> free_vars_expr_code e1 \<union> free_vars_expr_code e2"
| "free_vars_expr_code (Fail _) = {}"

lemma free_vars_expr_code[code]:
  "free_vars (e::expr) = free_vars_expr_code e"
proof-
  have "\<And>A. Suc -` A = (\<lambda>x. x - 1) ` (A - {0})" by force
  thus ?thesis by (induction e) simp_all
qed


primrec dist_param_type where
  "dist_param_type Bernoulli = REAL"
| "dist_param_type Poisson = REAL"
| "dist_param_type Gaussian = PRODUCT REAL REAL"
| "dist_param_type UniformInt = PRODUCT INTEG INTEG"
| "dist_param_type UniformReal = PRODUCT REAL REAL"

primrec dist_result_type where
  "dist_result_type Bernoulli = BOOL"
| "dist_result_type UniformInt = INTEG"
| "dist_result_type UniformReal = REAL"
| "dist_result_type Poisson = INTEG"
| "dist_result_type Gaussian = REAL"

primrec dist_measure :: "pdf_dist \<Rightarrow> val \<Rightarrow> val measure" where
  "dist_measure Bernoulli = bernoulli"
| "dist_measure UniformInt = uniform_int"
| "dist_measure UniformReal = uniform_real"
| "dist_measure Poisson = poisson"
| "dist_measure Gaussian = gaussian"

lemma measurable_dist_measure[measurable]:
  "dist_measure d \<in> measurable (dist_param_type d) (subprob_algebra (dist_result_type d))"
  by (cases d) simp_all

lemma sets_dist_measure[simp]:
  "val_type x = dist_param_type dst \<Longrightarrow>
       sets (dist_measure dst x) = sets (stock_measure (dist_result_type dst))"
  by (rule sets_kernel[OF measurable_dist_measure]) simp

lemma space_dist_measure[simp]:
  "val_type x = dist_param_type dst \<Longrightarrow>
       space (dist_measure dst x) = type_universe (dist_result_type dst)"
  by (subst space_stock_measure[symmetric]) (intro sets_eq_imp_space_eq sets_dist_measure)

primrec dist_dens :: "pdf_dist \<Rightarrow> val \<Rightarrow> val \<Rightarrow> ennreal" where
  "dist_dens Bernoulli x y = bernoulli_density (extract_real x) (extract_bool y)"
| "dist_dens UniformInt x y = uniform_int_density (extract_int_pair x) (extract_int y)"
| "dist_dens UniformReal x y = uniform_real_density (extract_real_pair x) (extract_real y)"
| "dist_dens Gaussian x y = gaussian_density (extract_real_pair x) (extract_real y)"
| "dist_dens Poisson x y = poisson_density' (extract_real x) (extract_int y)"

lemma measurable_dist_dens[measurable]:
    assumes "f \<in> measurable M (stock_measure (dist_param_type dst))" (is "_ \<in> measurable M ?N")
    assumes "g \<in> measurable M (stock_measure (dist_result_type dst))" (is "_ \<in> measurable M ?R")
    shows "(\<lambda>x. dist_dens dst (f x) (g x)) \<in> borel_measurable M"
  apply (rule measurable_Pair_compose_split[of "dist_dens dst", OF _ assms])
  apply (subst dist_dens_def, cases dst, simp_all)
  done

lemma dist_measure_has_density:
  "v \<in> type_universe (dist_param_type dst) \<Longrightarrow>
       has_density (dist_measure dst v) (stock_measure (dist_result_type dst)) (dist_dens dst v)"
proof (intro has_densityI)
  fix v assume "v \<in> type_universe (dist_param_type dst)"
  thus "dist_measure dst v = density (stock_measure (dist_result_type dst)) (dist_dens dst v)"
    by (cases dst)
       (auto simp: bernoulli_def uniform_int_def uniform_real_def poisson_def gaussian_def
             intro!: density_cong' elim!: PROD_E REAL_E INTEG_E)
qed simp_all

lemma subprob_space_dist_measure:
    "v \<in> type_universe (dist_param_type dst) \<Longrightarrow> subprob_space (dist_measure dst v)"
  using subprob_space_kernel[OF measurable_dist_measure, of v dst] by simp

lemma dist_measure_has_subprob_density:
  "v \<in> type_universe (dist_param_type dst) \<Longrightarrow>
       has_subprob_density (dist_measure dst v) (stock_measure (dist_result_type dst)) (dist_dens dst v)"
  unfolding has_subprob_density_def
  by (auto intro: subprob_space_dist_measure dist_measure_has_density)

lemma dist_dens_integral_space:
  assumes "v \<in> type_universe (dist_param_type dst)"
  shows "(\<integral>\<^sup>+u. dist_dens dst v u \<partial>stock_measure (dist_result_type dst)) \<le> 1"
proof-
  let ?M = "density (stock_measure (dist_result_type dst)) (dist_dens dst v)"
  from assms have "(\<integral>\<^sup>+u. dist_dens dst v u \<partial>stock_measure (dist_result_type dst)) =
                       emeasure ?M (space ?M)"
    by (subst space_density, subst emeasure_density)
       (auto intro!: measurable_dist_dens cong: nn_integral_cong')
  also have "?M = dist_measure dst v" using dist_measure_has_density[OF assms]
    by (auto dest: has_densityD)
  also from assms have "emeasure ... (space ...) \<le> 1"
    by (intro subprob_space.emeasure_space_le_1 subprob_space_dist_measure)
  finally show ?thesis .
qed


subsection \<open>Typing\<close>

primrec op_type :: "pdf_operator \<Rightarrow> pdf_type \<Rightarrow> pdf_type option" where
  "op_type Add x =
      (case x of
         PRODUCT INTEG INTEG \<Rightarrow> Some INTEG
       | PRODUCT REAL REAL \<Rightarrow> Some REAL
       | _ \<Rightarrow> None)"
| "op_type Mult x =
      (case x of
         PRODUCT INTEG INTEG \<Rightarrow> Some INTEG
       | PRODUCT REAL REAL \<Rightarrow> Some REAL
       | _ \<Rightarrow> None)"
| "op_type Minus x =
      (case x of
         INTEG \<Rightarrow> Some INTEG
       | REAL \<Rightarrow> Some REAL
       | _ \<Rightarrow> None)"
| "op_type Equals x =
      (case x of
         PRODUCT t1 t2 \<Rightarrow> if t1 = t2 then Some BOOL else None
       | _ \<Rightarrow> None)"
| "op_type Less x =
      (case x of
         PRODUCT INTEG INTEG \<Rightarrow> Some BOOL
       | PRODUCT REAL REAL \<Rightarrow> Some BOOL
       | _ \<Rightarrow> None)"
| "op_type (Cast t) x =
      (case (x, t) of
         (BOOL, INTEG) \<Rightarrow> Some INTEG
       | (BOOL, REAL) \<Rightarrow> Some REAL
       | (INTEG, REAL) \<Rightarrow> Some REAL
       | (REAL, INTEG) \<Rightarrow> Some INTEG
       | _ \<Rightarrow> None)"
| "op_type Or x = (case x of PRODUCT BOOL BOOL \<Rightarrow> Some BOOL | _ \<Rightarrow> None)"
| "op_type And x = (case x of PRODUCT BOOL BOOL \<Rightarrow> Some BOOL | _ \<Rightarrow> None)"
| "op_type Not x = (case x of BOOL \<Rightarrow> Some BOOL | _ \<Rightarrow> None)"
| "op_type Inverse x = (case x of REAL \<Rightarrow> Some REAL | _ \<Rightarrow> None)"
| "op_type Fact x = (case x of INTEG \<Rightarrow> Some INTEG | _ \<Rightarrow> None)"
| "op_type Sqrt x = (case x of REAL \<Rightarrow> Some REAL | _ \<Rightarrow> None)"
| "op_type Exp x = (case x of REAL \<Rightarrow> Some REAL | _ \<Rightarrow> None)"
| "op_type Ln x = (case x of REAL \<Rightarrow> Some REAL | _ \<Rightarrow> None)"
| "op_type Pi x = (case x of UNIT \<Rightarrow> Some REAL | _ \<Rightarrow> None)"
| "op_type Pow x = (case x of
                      PRODUCT REAL INTEG \<Rightarrow> Some REAL
                    | PRODUCT INTEG INTEG \<Rightarrow> Some INTEG
                    | _ \<Rightarrow> None)"
| "op_type Fst x = (case x of PRODUCT t _  \<Rightarrow> Some t | _ \<Rightarrow> None)"
| "op_type Snd x = (case x of PRODUCT _ t  \<Rightarrow> Some t | _ \<Rightarrow> None)"


subsection \<open>Semantics\<close>

abbreviation (input) de_bruijn_insert (infixr "\<cdot>" 65) where
  "de_bruijn_insert x f \<equiv> case_nat x f"

inductive expr_typing :: "tyenv \<Rightarrow> expr \<Rightarrow> pdf_type \<Rightarrow> bool" ("(1_/ \<turnstile>/ (_ :/ _))" [50,0,50] 50) where
  et_var:  "\<Gamma> \<turnstile> Var x : \<Gamma> x"
| et_val:  "\<Gamma> \<turnstile> Val v : val_type v"
| et_let:  "\<Gamma> \<turnstile> e1 : t1 \<Longrightarrow> t1 \<cdot> \<Gamma> \<turnstile> e2 : t2 \<Longrightarrow> \<Gamma> \<turnstile> LetVar e1 e2 : t2"
| et_op:   "\<Gamma> \<turnstile> e : t \<Longrightarrow> op_type oper t = Some t' \<Longrightarrow> \<Gamma> \<turnstile> Operator oper e : t'"
| et_pair: "\<Gamma> \<turnstile> e1 : t1  \<Longrightarrow> \<Gamma> \<turnstile> e2 : t2 \<Longrightarrow>  \<Gamma> \<turnstile> <e1, e2> : PRODUCT t1 t2"
| et_rand: "\<Gamma> \<turnstile> e : dist_param_type dst \<Longrightarrow> \<Gamma> \<turnstile> Random dst e :  dist_result_type dst"
| et_if:   "\<Gamma> \<turnstile> b : BOOL \<Longrightarrow> \<Gamma> \<turnstile> e1 : t \<Longrightarrow> \<Gamma> \<turnstile> e2 : t \<Longrightarrow> \<Gamma> \<turnstile> IF b THEN e1 ELSE e2 : t"
| et_fail: "\<Gamma> \<turnstile> Fail t : t"

lemma expr_typing_cong':
  "\<Gamma> \<turnstile> e : t \<Longrightarrow> (\<And>x. x \<in> free_vars e \<Longrightarrow> \<Gamma> x = \<Gamma>' x) \<Longrightarrow> \<Gamma>' \<turnstile> e : t"
proof (induction arbitrary: \<Gamma>' rule: expr_typing.induct)
  case (et_let \<Gamma> e1 t1 e2 t2 \<Gamma>')
  have "\<Gamma>' \<turnstile> e1 : t1" using et_let.prems by (intro et_let.IH(1)) auto
  moreover have "case_nat t1 \<Gamma>' \<turnstile> e2 : t2"
    using et_let.prems by (intro et_let.IH(2)) (auto split: nat.split)
  ultimately show ?case by (auto intro!: expr_typing.intros)
qed (auto intro!: expr_typing.intros)

lemma expr_typing_cong:
  "(\<And>x. x \<in> free_vars e \<Longrightarrow> \<Gamma> x = \<Gamma>' x) \<Longrightarrow> \<Gamma> \<turnstile> e : t \<longleftrightarrow> \<Gamma>' \<turnstile> e : t"
  by (intro iffI) (simp_all add: expr_typing_cong')

inductive_cases expr_typing_valE[elim]:  "\<Gamma> \<turnstile> Val v : t"
inductive_cases expr_typing_varE[elim]:  "\<Gamma> \<turnstile> Var x : t"
inductive_cases expr_typing_letE[elim]:  "\<Gamma> \<turnstile> LetVar e1 e2 : t"
inductive_cases expr_typing_ifE[elim]:  "\<Gamma> \<turnstile> IfThenElse b e1 e2 : t"
inductive_cases expr_typing_opE[elim]:   "\<Gamma> \<turnstile> Operator oper e : t"
inductive_cases expr_typing_pairE[elim]: "\<Gamma> \<turnstile> <e1, e2> : t"
inductive_cases expr_typing_randE[elim]: "\<Gamma> \<turnstile> Random dst e : t"
inductive_cases expr_typing_failE[elim]: "\<Gamma> \<turnstile> Fail t : t'"

lemma expr_typing_unique:
  "\<Gamma> \<turnstile> e : t \<Longrightarrow> \<Gamma> \<turnstile> e : t' \<Longrightarrow> t = t'"
  apply (induction arbitrary: t' rule: expr_typing.induct)
  apply blast
  apply blast
  apply (erule expr_typing_letE, blast)
  apply (erule expr_typing_opE, simp)
  apply (erule expr_typing_pairE, blast)
  apply (erule expr_typing_randE, blast)
  apply (erule expr_typing_ifE, blast)
  apply blast
  done

fun expr_type :: "tyenv \<Rightarrow> expr \<Rightarrow> pdf_type option" where
  "expr_type \<Gamma> (Var x) = Some (\<Gamma> x)"
| "expr_type \<Gamma> (Val v) = Some (val_type v)"
| "expr_type \<Gamma> (LetVar e1 e2) =
       (case expr_type \<Gamma> e1 of
          Some t \<Rightarrow> expr_type (case_nat t \<Gamma>) e2
        | None \<Rightarrow> None)"
| "expr_type \<Gamma> (Operator oper e) =
       (case expr_type \<Gamma> e of Some t \<Rightarrow> op_type oper t | None \<Rightarrow> None)"
| "expr_type \<Gamma> (<e1, e2>) =
       (case (expr_type \<Gamma> e1, expr_type \<Gamma> e2) of
          (Some t1, Some t2) \<Rightarrow> Some (PRODUCT t1 t2)
        |  _ \<Rightarrow> None)"
| "expr_type \<Gamma> (Random dst e) =
       (if expr_type \<Gamma> e = Some (dist_param_type dst) then
           Some (dist_result_type dst)
        else None)"
| "expr_type \<Gamma> (IF b THEN e1 ELSE e2) =
       (if expr_type \<Gamma> b = Some BOOL then
          (case (expr_type \<Gamma> e1, expr_type \<Gamma> e2) of
             (Some t, Some t') \<Rightarrow> if t = t' then Some t else None
           | _ \<Rightarrow> None) else None)"
| "expr_type \<Gamma> (Fail t) = Some t"

lemma expr_type_Some_iff: "expr_type \<Gamma> e = Some t \<longleftrightarrow> \<Gamma> \<turnstile> e : t"
  apply rule
  apply (induction e arbitrary: \<Gamma> t,
         auto intro!: expr_typing.intros split: option.split_asm if_split_asm) []
  apply (induction rule: expr_typing.induct, auto simp del: fun_upd_apply)
  done

lemmas expr_typing_code[code_unfold] = expr_type_Some_iff[symmetric]


subsubsection \<open>Countable types\<close>

primrec countable_type :: "pdf_type \<Rightarrow> bool" where
  "countable_type UNIT = True"
| "countable_type BOOL = True"
| "countable_type INTEG = True"
| "countable_type REAL = False"
| "countable_type (PRODUCT t1 t2) = (countable_type t1 \<and> countable_type t2)"

lemma countable_type_countable[dest]:
    "countable_type t \<Longrightarrow> countable (space (stock_measure t))"
  by (induction t)
     (auto simp: pair_measure_countable space_embed_measure space_pair_measure stock_measure.simps)

lemma countable_type_imp_count_space:
  "countable_type t \<Longrightarrow> stock_measure t = count_space (type_universe t)"
proof (subst space_stock_measure[symmetric], induction t)
  case (PRODUCT t1 t2)
    hence countable: "countable_type t1" "countable_type t2" by simp_all
    note A = PRODUCT.IH(1)[OF countable(1)] and B = PRODUCT.IH(2)[OF countable(2)]
    show "stock_measure (PRODUCT t1 t2) = count_space (space (stock_measure (PRODUCT t1 t2)))"
      apply (subst (1 2) stock_measure.simps)
      apply (subst (1 2) A, subst (1 2) B)
      apply (subst (1 2) pair_measure_countable)
      apply (auto intro: countable_type_countable simp: countable simp del: space_stock_measure) [2]
      apply (subst (1 2) embed_measure_count_space, force intro: injI)
      apply simp
      done
qed (simp_all add: stock_measure.simps)

lemma return_val_countable:
  assumes "countable_type (val_type v)"
  shows "return_val v = density (stock_measure (val_type v)) (indicator {v})" (is "?M1 = ?M2")
proof (rule measure_eqI)
  let ?M3 = "count_space (type_universe (val_type v))"
  fix X assume asm: "X \<in> ?M1"
  with assms have "emeasure ?M2 X = \<integral>\<^sup>+ x. indicator {v} x * indicator X x
                                              \<partial>count_space (type_universe (val_type v))"
    by (simp add: return_val_def emeasure_density countable_type_imp_count_space)
  also have "(\<lambda>x. indicator {v} x * indicator X x :: ennreal) = (\<lambda>x. indicator (X \<inter> {v}) x)"
    by (rule ext, subst Int_commute) (simp split: split_indicator)
  also have "nn_integral ?M3 ... = emeasure ?M3 (X \<inter> {v})"
    by (subst nn_integral_indicator[symmetric]) auto
  also from asm have "... = emeasure ?M1 X" by (auto simp: return_val_def split: split_indicator)
  finally show "emeasure ?M1 X = emeasure ?M2 X" ..
qed (simp add: return_val_def)



subsection \<open>Semantics\<close>

definition bool_to_int :: "bool \<Rightarrow> int" where
  "bool_to_int b = (if b then 1 else 0)"

lemma measurable_bool_to_int[measurable]:
  "bool_to_int \<in> measurable (count_space UNIV) (count_space UNIV)"
  by (rule measurable_count_space)

definition bool_to_real :: "bool \<Rightarrow> real" where
  "bool_to_real b = (if b then 1 else 0)"

lemma measurable_bool_to_real[measurable]:
  "bool_to_real \<in> borel_measurable (count_space UNIV)"
  by (rule borel_measurable_count_space)

definition safe_ln :: "real \<Rightarrow> real" where
  "safe_ln x = (if x > 0 then ln x else 0)"

lemma safe_ln_gt_0[simp]: "x > 0 \<Longrightarrow> safe_ln x = ln x"
  by (simp add: safe_ln_def)

lemma borel_measurable_safe_ln[measurable]: "safe_ln \<in> borel_measurable borel"
  unfolding safe_ln_def[abs_def] by simp


definition safe_sqrt :: "real \<Rightarrow> real" where
  "safe_sqrt x = (if x \<ge> 0 then sqrt x else 0)"

lemma safe_sqrt_ge_0[simp]: "x \<ge> 0 \<Longrightarrow> safe_sqrt x = sqrt x"
  by (simp add: safe_sqrt_def)

lemma borel_measurable_safe_sqrt[measurable]: "safe_sqrt \<in> borel_measurable borel"
  unfolding safe_sqrt_def[abs_def] by simp


fun op_sem :: "pdf_operator \<Rightarrow> val \<Rightarrow> val" where
  "op_sem Add = lift_RealIntVal2 (+) (+)"
| "op_sem Mult = lift_RealIntVal2 (*) (*)"
| "op_sem Minus = lift_RealIntVal uminus uminus"
| "op_sem Equals = (\<lambda> <|v1, v2|> \<Rightarrow> BoolVal (v1 = v2))"
| "op_sem Less = lift_Comp (<) (<)"
| "op_sem Or = (\<lambda> <|BoolVal a, BoolVal b|> \<Rightarrow> BoolVal (a \<or> b))"
| "op_sem And = (\<lambda> <|BoolVal a, BoolVal b|> \<Rightarrow> BoolVal (a \<and> b))"
| "op_sem Not = (\<lambda> BoolVal a \<Rightarrow> BoolVal (\<not>a))"
| "op_sem (Cast t) = (case t of
                        INTEG \<Rightarrow> (\<lambda> BoolVal b \<Rightarrow> IntVal (bool_to_int b)
                                  | RealVal r \<Rightarrow> IntVal (floor r))
                      | REAL \<Rightarrow>  (\<lambda> BoolVal b \<Rightarrow> RealVal (bool_to_real b)
                                  | IntVal i \<Rightarrow> RealVal (real_of_int i)))"
| "op_sem Inverse = lift_RealVal inverse"
| "op_sem Fact = lift_IntVal (\<lambda>i::int. fact (nat i))"
| "op_sem Sqrt = lift_RealVal safe_sqrt"
| "op_sem Exp = lift_RealVal exp"
| "op_sem Ln = lift_RealVal safe_ln"
| "op_sem Pi = (\<lambda>_. RealVal pi)"
| "op_sem Pow = (\<lambda> <|RealVal x, IntVal n|> \<Rightarrow> if n < 0 then RealVal 0 else RealVal (x ^ nat n)
                 | <|IntVal x, IntVal n|> \<Rightarrow> if n < 0 then IntVal 0 else IntVal (x ^ nat n))"
| "op_sem Fst = fst \<circ> extract_pair"
| "op_sem Snd = snd \<circ> extract_pair"


text \<open>The semantics of expressions. Assumes that the expression given is well-typed.\<close>

primrec expr_sem :: "state \<Rightarrow> expr \<Rightarrow> val measure" where
  "expr_sem \<sigma> (Var x) = return_val (\<sigma> x)"
| "expr_sem \<sigma> (Val v) = return_val v"
| "expr_sem \<sigma> (LET e1 IN e2) =
      do {
        v \<leftarrow> expr_sem \<sigma> e1;
        expr_sem (v \<cdot> \<sigma>) e2
      }"
| "expr_sem \<sigma> (oper $$ e) =
      do {
        x \<leftarrow> expr_sem \<sigma> e;
        return_val (op_sem oper x)
      }"
| "expr_sem \<sigma> <v, w> =
      do {
        x \<leftarrow> expr_sem \<sigma> v;
        y \<leftarrow> expr_sem \<sigma> w;
        return_val <|x, y|>
      }"
| "expr_sem \<sigma> (IF b THEN e1 ELSE e2) =
     do {
       b' \<leftarrow> expr_sem \<sigma> b;
       if b' = TRUE then expr_sem \<sigma> e1 else expr_sem \<sigma> e2
     }"
| "expr_sem \<sigma> (Random dst e) =
     do {
       x \<leftarrow> expr_sem \<sigma> e;
       dist_measure dst x
     }"
| "expr_sem \<sigma> (Fail t) = null_measure (stock_measure t)"

lemma expr_sem_pair_vars: "expr_sem \<sigma> <Var x, Var y> = return_val <|\<sigma> x, \<sigma> y|>"
  by (simp add: return_val_def bind_return[where N="PRODUCT (val_type (\<sigma> x)) (val_type (\<sigma> y))"]
           cong: bind_cong_simp)

text \<open>
  Well-typed expressions produce a result in the measure space that corresponds to their type
\<close>

lemma op_sem_val_type:
    "op_type oper (val_type v) = Some t' \<Longrightarrow> val_type (op_sem oper v) = t'"
  by (cases oper) (auto split: val.split if_split_asm pdf_type.split_asm
                        simp: lift_RealIntVal_def lift_Comp_def
                              lift_IntVal_def lift_RealVal_def lift_RealIntVal2_def
                        elim!: PROD_E INTEG_E REAL_E)

lemma sets_expr_sem:
  "\<Gamma> \<turnstile> w : t \<Longrightarrow> (\<forall>x \<in> free_vars w. val_type (\<sigma> x) = \<Gamma> x) \<Longrightarrow>
       sets (expr_sem \<sigma> w) = sets (stock_measure t)"
proof (induction arbitrary: \<sigma> rule: expr_typing.induct)
  case (et_var \<Gamma> x \<sigma>)
  thus ?case by (simp add: return_val_def)
next
  case (et_val \<Gamma> v \<sigma>)
  thus ?case by (simp add: return_val_def)
next
  case (et_let \<Gamma> e1 t1 e2 t2 \<sigma>)
  hence "sets (expr_sem \<sigma> e1) = sets (stock_measure t1)" by simp
  from sets_eq_imp_space_eq[OF this]
    have A: "space (expr_sem \<sigma> e1) = type_universe t1" by (simp add:)
  hence B: "(SOME x. x \<in> space (expr_sem \<sigma> e1)) \<in> space (expr_sem \<sigma> e1)" (is "?v \<in> _")
    unfolding some_in_eq by simp
  with A et_let have "sets (expr_sem (case_nat ?v \<sigma>) e2) = sets (stock_measure t2)"
    by (intro et_let.IH(2)) (auto split: nat.split)
  with B show "sets (expr_sem \<sigma> (LetVar e1 e2)) = sets (stock_measure t2)"
    by (subst expr_sem.simps, subst bind_nonempty) auto
next
  case (et_op \<Gamma> e t oper t' \<sigma>)
  from et_op.IH[of \<sigma>] and et_op.prems
      have [simp]: "sets (expr_sem \<sigma> e) = sets (stock_measure t)" by simp
  from sets_eq_imp_space_eq[OF this]
      have [simp]: "space (expr_sem \<sigma> e) = type_universe t" by (simp add:)
  have "(SOME x. x \<in> space (expr_sem \<sigma> e)) \<in> space (expr_sem \<sigma> e)"
    unfolding some_in_eq by simp
  with et_op show ?case by (simp add: bind_nonempty return_val_def op_sem_val_type)
next
  case (et_pair \<Gamma> e1 t1 e2 t2 \<sigma>)
  hence [simp]: "space (expr_sem \<sigma> e1) = type_universe t1"
                "space (expr_sem \<sigma> e2) = type_universe t2"
    by (simp_all add: sets_eq_imp_space_eq)
  have "(SOME x. x \<in> space (expr_sem \<sigma> e1)) \<in> space (expr_sem \<sigma> e1)"
       "(SOME x. x \<in> space (expr_sem \<sigma> e2)) \<in> space (expr_sem \<sigma> e2)"
    unfolding some_in_eq by simp_all
  with et_pair.hyps show ?case by (simp add: bind_nonempty return_val_def)
next
  case (et_rand \<Gamma> e dst \<sigma>)
  from et_rand.IH[of \<sigma>] et_rand.prems
  have "sets (expr_sem \<sigma> e) = sets (stock_measure (dist_param_type dst))" by simp
  from this sets_eq_imp_space_eq[OF this]
  show ?case
    apply simp_all
    apply (subst sets_bind)
    apply auto
    done
next
  case (et_if \<Gamma> b e1 t e2 \<sigma>)
  have "sets (expr_sem \<sigma> b) = sets (stock_measure BOOL)"
    using et_if.prems by (intro et_if.IH) simp
  from sets_eq_imp_space_eq[OF this]
    have "space (expr_sem \<sigma> b) \<noteq> {}" by simp
  moreover have "sets (expr_sem \<sigma> e1) = sets (stock_measure t)"
                "sets (expr_sem \<sigma> e2) = sets (stock_measure t)"
    using et_if.prems by (intro et_if.IH, simp)+
  ultimately show ?case by (simp add: bind_nonempty)
qed simp_all

lemma space_expr_sem:
    "\<Gamma> \<turnstile> w : t \<Longrightarrow> (\<forall>x \<in> free_vars w. val_type (\<sigma> x) = \<Gamma> x)
      \<Longrightarrow> space (expr_sem \<sigma> w) = type_universe t"
  by (subst space_stock_measure[symmetric]) (intro sets_expr_sem sets_eq_imp_space_eq)

lemma measurable_expr_sem_eq:
    "\<Gamma> \<turnstile> e : t \<Longrightarrow> \<sigma> \<in> space (state_measure V \<Gamma>) \<Longrightarrow> free_vars e \<subseteq> V \<Longrightarrow>
       measurable (expr_sem \<sigma> e) = measurable (stock_measure t)"
  by (intro ext measurable_cong_sets sets_expr_sem)
     (auto simp: state_measure_def space_PiM dest: PiE_mem)

lemma measurable_expr_semI:
    "\<Gamma> \<turnstile> e : t \<Longrightarrow> \<sigma> \<in> space (state_measure V \<Gamma>) \<Longrightarrow> free_vars e \<subseteq> V \<Longrightarrow>
       f \<in> measurable (stock_measure t) M \<Longrightarrow> f \<in> measurable (expr_sem \<sigma> e) M"
  by (subst measurable_expr_sem_eq)

lemma expr_sem_eq_on_vars:
  "(\<And>x. x\<in>free_vars e \<Longrightarrow> \<sigma>\<^sub>1 x = \<sigma>\<^sub>2 x) \<Longrightarrow> expr_sem \<sigma>\<^sub>1 e = expr_sem \<sigma>\<^sub>2 e"
proof (induction e arbitrary: \<sigma>\<^sub>1 \<sigma>\<^sub>2)
  case (LetVar e1 e2 \<sigma>1 \<sigma>2)
    from LetVar.prems have A: "expr_sem \<sigma>1 e1 = expr_sem \<sigma>2 e1" by (rule LetVar.IH(1)) simp_all
    from LetVar.prems show ?case
      by (subst (1 2) expr_sem.simps, subst A)
         (auto intro!: bind_cong LetVar.IH(2) split: nat.split)
next
  case (Operator oper e \<sigma>1 \<sigma>2)
  from Operator.IH[OF Operator.prems] show ?case by simp
next
  case (Pair e1 e2 \<sigma>1 \<sigma>2)
  from Pair.prems have "expr_sem \<sigma>1 e1 = expr_sem \<sigma>2 e1" by (intro Pair.IH) auto
  moreover from Pair.prems have "expr_sem \<sigma>1 e2 = expr_sem \<sigma>2 e2" by (intro Pair.IH) auto
  ultimately show ?case by simp
next
  case (Random dst e \<sigma>1 \<sigma>2)
  from Random.prems have A: "expr_sem \<sigma>1 e = expr_sem \<sigma>2 e" by (rule Random.IH) simp_all
  show ?case
    by (subst (1 2) expr_sem.simps, subst A) (auto intro!: bind_cong)
next
  case (IfThenElse b e1 e2 \<sigma>1 \<sigma>2)
  have A: "expr_sem \<sigma>1 b = expr_sem \<sigma>2 b"
          "expr_sem \<sigma>1 e1 = expr_sem \<sigma>2 e1"
          "expr_sem \<sigma>1 e2 = expr_sem \<sigma>2 e2"
    using IfThenElse.prems by (intro IfThenElse.IH, simp)+
  thus ?case by (simp only: expr_sem.simps A)
qed simp_all


subsection \<open>Measurability\<close>

lemma borel_measurable_eq[measurable (raw)]:
  assumes [measurable]: "f \<in> borel_measurable M" "g \<in> borel_measurable M"
  shows "Measurable.pred M (\<lambda>x. f x = (g x::real))"
proof -
  have *: "(\<lambda>x. f x = g x) = (\<lambda>x. f x - g x = 0)"
    by simp
  show ?thesis
    unfolding * by measurable
qed

lemma measurable_equals:
  "(\<lambda>(x,y). x = y) \<in> measurable (stock_measure t \<Otimes>\<^sub>M stock_measure t) (count_space UNIV)"
proof (induction t)
  case REAL
  let ?f = "\<lambda>x. extract_real (fst x) = extract_real (snd x)"
  show ?case
  proof (subst measurable_cong)
    fix x assume "x \<in> space (stock_measure REAL \<Otimes>\<^sub>M stock_measure REAL)"
    thus "(\<lambda>(x,y). x = y) x = ?f x"
      by (auto simp: space_pair_measure elim!: REAL_E)
  next
    show "?f \<in> measurable (stock_measure REAL \<Otimes>\<^sub>M stock_measure REAL) (count_space UNIV)"
      by measurable
  qed
next
  case (PRODUCT t1 t2)
  let ?g = "\<lambda>(x,y). x = y"
  let ?f = "\<lambda>x. ?g (fst (extract_pair (fst x)), fst (extract_pair (snd x))) \<and>
                ?g (snd (extract_pair (fst x)), snd (extract_pair (snd x)))"
  show ?case
  proof (subst measurable_cong)
    fix x assume "x \<in> space (stock_measure (PRODUCT t1 t2) \<Otimes>\<^sub>M stock_measure (PRODUCT t1 t2))"
    thus "(\<lambda>(x,y). x = y) x = ?f x"
      apply (auto simp: space_pair_measure)
      apply (elim PROD_E)
      apply simp
      done
  next
    note PRODUCT[measurable]
    show "Measurable.pred (stock_measure (PRODUCT t1 t2) \<Otimes>\<^sub>M stock_measure (PRODUCT t1 t2)) ?f"
      by measurable
  qed
qed (simp_all add: pair_measure_countable stock_measure.simps)

lemma measurable_equals_stock_measure[measurable (raw)]:
  assumes "f \<in> measurable M (stock_measure t)" "g \<in> measurable M (stock_measure t)"
  shows "Measurable.pred M (\<lambda>x. f x = g x)"
  using measurable_compose[OF measurable_Pair[OF assms] measurable_equals] by simp

lemma measurable_op_sem:
  assumes "op_type oper t = Some t'"
  shows "op_sem oper \<in> measurable (stock_measure t) (stock_measure t')"
proof (cases oper)
  case Fst with assms show ?thesis by (simp split: pdf_type.split_asm)
next
  case Snd with assms show ?thesis by (simp split: pdf_type.split_asm)
next
  case Equals with assms show ?thesis
    by (auto intro!: val_case_stock_measurable split: if_split_asm)
next
  case Pow with assms show ?thesis
    apply (auto intro!: val_case_stock_measurable split: pdf_type.splits)
    apply (subst measurable_cong[where
      g="\<lambda>(x, n). if extract_int n < 0 then RealVal 0 else RealVal (extract_real x ^ nat (extract_int n))"])
    apply (auto simp: space_pair_measure elim!: REAL_E INTEG_E)
    done
next
  case Less with assms show ?thesis
    by (auto split: pdf_type.splits)
qed (insert assms, auto split: pdf_type.split_asm intro!: val_case_stock_measurable)

definition shift_var_set :: "vname set \<Rightarrow> vname set" where
  "shift_var_set V = insert 0 (Suc ` V)"

lemma shift_var_set_0[simp]: "0 \<in> shift_var_set V"
  by (simp add: shift_var_set_def)

lemma shift_var_set_Suc[simp]: "Suc x \<in> shift_var_set V \<longleftrightarrow> x \<in> V"
  by (auto simp add: shift_var_set_def)

lemma case_nat_update_0[simp]: "(case_nat x \<sigma>)(0 := y) = case_nat y \<sigma>"
  by (intro ext) (simp split: nat.split)

lemma case_nat_delete_var_1[simp]:
    "case_nat x (case_nat y \<sigma>) \<circ> case_nat 0 (\<lambda>x. Suc (Suc x)) = case_nat x \<sigma>"
  by (intro ext) (simp split: nat.split)

lemma delete_var_1_vimage[simp]:
    "case_nat 0 (\<lambda>x. Suc (Suc x)) -` (shift_var_set (shift_var_set V)) = shift_var_set V"
  by (auto simp: shift_var_set_def split: nat.split_asm)


lemma measurable_case_nat[measurable]:
  assumes "g \<in> measurable R N" "h \<in> measurable R (Pi\<^sub>M V M)"
  shows "(\<lambda>x. case_nat (g x) (h x)) \<in> measurable R (Pi\<^sub>M (shift_var_set V) (case_nat N M))"
proof (rule measurable_Pair_compose_split[OF _ assms])
  have "(\<lambda>(t,f). \<lambda>x\<in>shift_var_set V. case_nat t f x)
          \<in> measurable (N \<Otimes>\<^sub>M PiM V M) (PiM (shift_var_set V) (case_nat N M))" (is ?P)
    unfolding shift_var_set_def
    by (subst measurable_split_conv, rule measurable_restrict) (auto split: nat.split_asm)
  also have "\<And>x f. f \<in> space (PiM V M) \<Longrightarrow> x \<notin> V \<Longrightarrow> undefined = f x"
    by (rule sym, subst (asm) space_PiM, erule PiE_arb)
  hence "?P \<longleftrightarrow> (\<lambda>(t,f). case_nat t f)
           \<in> measurable (N \<Otimes>\<^sub>M PiM V M) (PiM (shift_var_set V) (case_nat N M))" (is "_ = ?P")
    by (intro measurable_cong ext)
       (auto split: nat.split simp: inj_image_mem_iff space_pair_measure shift_var_set_def)
  finally show ?P .
qed

lemma measurable_case_nat'[measurable]:
  assumes "g \<in> measurable R (stock_measure t)" "h \<in> measurable R (state_measure V \<Gamma>)"
  shows "(\<lambda>x. case_nat (g x) (h x)) \<in>
           measurable R (state_measure (shift_var_set V) (case_nat t \<Gamma>))"
proof-
  have A: "(\<lambda>x. stock_measure (case_nat t \<Gamma> x)) =
                 case_nat (stock_measure t) (\<lambda>x. stock_measure (\<Gamma> x))"
    by (intro ext) (simp split: nat.split)
  show ?thesis using assms unfolding state_measure_def by (simp add: A)
qed

lemma case_nat_in_state_measure[intro]:
  assumes "x \<in> type_universe t1" "\<sigma> \<in> space (state_measure V \<Gamma>)"
  shows "case_nat x \<sigma> \<in> space (state_measure (shift_var_set V) (case_nat t1 \<Gamma>))"
  apply (rule measurable_space[OF measurable_case_nat'])
  apply (rule measurable_ident_sets[OF refl], rule measurable_const[OF assms(2)])
  using assms
  apply simp
  done

lemma subset_shift_var_set:
    "Suc -` A \<subseteq> V \<Longrightarrow> A \<subseteq> shift_var_set V"
  by (rule subsetI, rename_tac x, case_tac x) (auto simp: shift_var_set_def)

lemma measurable_expr_sem[measurable]:
  assumes "\<Gamma> \<turnstile> e : t" and "free_vars e \<subseteq> V"
  shows "(\<lambda>\<sigma>. expr_sem \<sigma> e) \<in> measurable (state_measure V \<Gamma>)
                                         (subprob_algebra (stock_measure t))"
using assms
proof (induction arbitrary: V rule: expr_typing.induct)
  case (et_var \<Gamma> x)
  have A: "(\<lambda>\<sigma>. expr_sem \<sigma> (Var x)) = return_val \<circ> (\<lambda>\<sigma>. \<sigma> x)" by (simp add: o_def)
  with et_var show ?case unfolding state_measure_def
    by (subst A) (rule measurable_comp[OF measurable_component_singleton], simp_all)
next
  case (et_val \<Gamma> v)
  thus ?case by (auto intro!: measurable_const subprob_space_return
                      simp: space_subprob_algebra return_val_def)
next
  case (et_let \<Gamma> e1 t1 e2 t2 V)
    have A: "(\<lambda>v. stock_measure (case_nat t1 \<Gamma> v)) =
                 case_nat (stock_measure t1) (\<lambda>v. stock_measure (\<Gamma> v))"
      by (rule ext) (simp split: nat.split)
    from et_let.prems and et_let.hyps show ?case
      apply (subst expr_sem.simps, intro measurable_bind)
      apply (rule et_let.IH(1), simp)
      apply (rule measurable_compose[OF _ et_let.IH(2)[of "shift_var_set V"]])
      apply (simp_all add: subset_shift_var_set)
      done
next
  case (et_op \<Gamma> e t oper t')
  thus ?case by (auto intro!: measurable_bind2 measurable_compose[OF _ measurable_return_val]
                              measurable_op_sem cong: measurable_cong)
next
  case (et_pair t t1 t2 \<Gamma> e1 e2)
  have "inj (\<lambda>(a,b). <|a, b|>)" by (auto intro: injI)
  with et_pair show ?case
      apply (subst expr_sem.simps)
      apply (rule measurable_bind, (auto) [])
      apply (rule measurable_bind[OF measurable_compose[OF measurable_fst]], (auto) [])
      apply (rule measurable_compose[OF _ measurable_return_val], simp)
      done
next
  case (et_rand \<Gamma> e dst V)
  from et_rand.prems and et_rand.hyps show ?case
    by (auto intro!: et_rand.IH measurable_compose[OF measurable_snd]
                     measurable_bind measurable_dist_measure)
next
  case (et_if \<Gamma> b e1 t e2 V)
  let ?M = "\<lambda>e t. (\<lambda>\<sigma>. expr_sem \<sigma> e) \<in>
                      measurable (state_measure V \<Gamma>) (subprob_algebra (stock_measure t))"
  from et_if.prems have A[measurable]: "?M b BOOL" "?M e1 t" "?M e2 t" by (intro et_if.IH, simp)+
  show ?case by (subst expr_sem.simps, rule measurable_bind[OF A(1)]) simp_all
next
  case (et_fail \<Gamma> t V)
  show ?case
    by (auto intro!: measurable_subprob_algebra subprob_spaceI simp:)
qed


subsection \<open>Randomfree expressions\<close>

fun randomfree :: "expr \<Rightarrow> bool" where
  "randomfree (Val _) = True"
| "randomfree (Var _) = True"
| "randomfree (Pair e1 e2) = (randomfree e1 \<and> randomfree e2)"
| "randomfree (Operator _ e) = randomfree e"
| "randomfree (LetVar e1 e2) = (randomfree e1 \<and> randomfree e2)"
| "randomfree (IfThenElse b e1 e2) = (randomfree b \<and> randomfree e1 \<and> randomfree e2)"
| "randomfree (Random _ _) = False"
| "randomfree (Fail _) = False"

primrec expr_sem_rf :: "state \<Rightarrow> expr \<Rightarrow> val" where
  "expr_sem_rf _ (Val v) = v"
| "expr_sem_rf \<sigma> (Var x) = \<sigma> x"
| "expr_sem_rf \<sigma> (<e1, e2>) = <|expr_sem_rf \<sigma> e1, expr_sem_rf \<sigma> e2|>"
| "expr_sem_rf \<sigma> (Operator oper e) = op_sem oper (expr_sem_rf \<sigma> e)"
| "expr_sem_rf \<sigma> (LetVar e1 e2) = expr_sem_rf (expr_sem_rf \<sigma> e1 \<cdot> \<sigma>) e2"
| "expr_sem_rf \<sigma> (IfThenElse b e1 e2) =
      (if expr_sem_rf \<sigma> b = BoolVal True then expr_sem_rf \<sigma> e1 else expr_sem_rf \<sigma> e2)"
| "expr_sem_rf _ (Random _ _) = undefined"
| "expr_sem_rf _ (Fail _) = undefined"


lemma measurable_expr_sem_rf[measurable]:
  "\<Gamma> \<turnstile> e : t \<Longrightarrow> randomfree e \<Longrightarrow> free_vars e \<subseteq> V \<Longrightarrow>
       (\<lambda>\<sigma>. expr_sem_rf \<sigma> e) \<in> measurable (state_measure V \<Gamma>) (stock_measure t)"
proof (induction arbitrary: V rule: expr_typing.induct)
  case (et_val \<Gamma> v V)
  thus ?case by (auto intro!: measurable_const simp:)
next
  case (et_var \<Gamma> x V)
  thus ?case by (auto simp: state_measure_def intro!: measurable_component_singleton)
next
  case (et_pair \<Gamma> e1 t1 e2 t2 V)
  have "inj (\<lambda>(x,y). <|x, y|>)" by (auto intro: injI)
  with et_pair show ?case by simp
next
  case (et_op \<Gamma> e t oper t' V)
  thus ?case by (auto intro!: measurable_compose[OF _ measurable_op_sem])
next
  case (et_let \<Gamma> e1 t1 e2 t2 V)
  hence M1: "(\<lambda>\<sigma>. expr_sem_rf \<sigma> e1) \<in> measurable (state_measure V \<Gamma>) (stock_measure t1)"
    and M2: "(\<lambda>\<sigma>. expr_sem_rf \<sigma> e2) \<in> measurable (state_measure (shift_var_set V) (case_nat t1 \<Gamma>))
                                           (stock_measure t2)"
    using subset_shift_var_set
    by (auto intro!: et_let.IH(1)[of V] et_let.IH(2)[of "shift_var_set V"])
  have "(\<lambda>\<sigma>. expr_sem_rf \<sigma> (LetVar e1 e2)) =
            (\<lambda>\<sigma>. expr_sem_rf \<sigma> e2) \<circ> (\<lambda>(\<sigma>,y). case_nat y \<sigma>) \<circ> (\<lambda>\<sigma>. (\<sigma>, expr_sem_rf \<sigma> e1))" (is "_ = ?f")
    by (intro ext) simp
  also have "?f \<in> measurable (state_measure V \<Gamma>) (stock_measure t2)"
    apply (intro measurable_comp, rule measurable_Pair, rule measurable_ident_sets[OF refl])
    apply (rule M1, subst measurable_split_conv, rule measurable_case_nat')
    apply (rule measurable_snd, rule measurable_fst, rule M2)
    done
  finally show ?case .
qed (simp_all add: expr_sem_rf_def)

lemma expr_sem_rf_sound:
  "\<Gamma> \<turnstile> e : t \<Longrightarrow> randomfree e \<Longrightarrow> free_vars e \<subseteq> V \<Longrightarrow> \<sigma> \<in> space (state_measure V \<Gamma>) \<Longrightarrow>
       return_val (expr_sem_rf \<sigma> e) = expr_sem \<sigma> e"
proof (induction arbitrary: V \<sigma> rule: expr_typing.induct)
  case (et_val \<Gamma> v)
  thus ?case by simp
next
  case (et_var \<Gamma> x)
 thus ?case by simp
next
  case (et_pair \<Gamma> e1 t1 e2 t2 V \<sigma>)
  let ?M = "state_measure V \<Gamma>"
  from et_pair.hyps and et_pair.prems
    have e1: "return_val (expr_sem_rf \<sigma> e1) = expr_sem \<sigma> e1" and
         e2: "return_val (expr_sem_rf \<sigma> e2) = expr_sem \<sigma> e2"
      by (auto intro!: et_pair.IH[of V])

  from e1 and et_pair.prems have "space (return_val (expr_sem_rf \<sigma> e1)) = type_universe t1"
    by (subst e1, subst space_expr_sem[OF et_pair.hyps(1)])
       (auto dest: state_measure_var_type)
  hence A: "val_type (expr_sem_rf \<sigma> e1) = t1" "expr_sem_rf \<sigma> e1 \<in> type_universe t1"
      by (auto simp add: return_val_def)
  from e2 and et_pair.prems have "space (return_val (expr_sem_rf \<sigma> e2)) = type_universe t2"
    by (subst e2, subst space_expr_sem[OF et_pair.hyps(2)])
       (auto dest: state_measure_var_type)
  hence B: "val_type (expr_sem_rf \<sigma> e2) = t2" "expr_sem_rf \<sigma> e2 \<in> type_universe t2"
      by (auto simp add: return_val_def)

  have "expr_sem \<sigma> (<e1, e2>) = expr_sem \<sigma> e1 \<bind>
            (\<lambda>v. expr_sem \<sigma> e2 \<bind> (\<lambda>w. return_val (<|v,w|>)))" by simp
  also have "expr_sem \<sigma> e1 = return (stock_measure t1) (expr_sem_rf \<sigma> e1)"
    using e1 by (simp add: et_pair.prems return_val_def A)
  also have "... \<bind> (\<lambda>v. expr_sem \<sigma> e2 \<bind> (\<lambda>w. return_val (<|v,w|>))) =
          ... \<bind> (\<lambda>v. return_val (<|v, expr_sem_rf \<sigma> e2|>))"
  proof (intro bind_cong refl)
    fix v assume "v \<in> space (return (stock_measure t1) (expr_sem_rf \<sigma> e1))"
    hence v: "val_type v = t1" "v \<in> type_universe t1" by (simp_all add:)
    have "expr_sem \<sigma> e2 \<bind> (\<lambda>w. return_val (<|v,w|>)) =
              return (stock_measure t2) (expr_sem_rf \<sigma> e2) \<bind> (\<lambda>w. return_val (<|v,w|>))"
      using e2 by (simp add: et_pair.prems return_val_def B)
    also have "... = return (stock_measure t2) (expr_sem_rf \<sigma> e2) \<bind>
                         (\<lambda>w. return (stock_measure (PRODUCT t1 t2)) (<|v,w|>))"
    proof (intro bind_cong refl)
      fix w assume "w \<in> space (return (stock_measure t2) (expr_sem_rf \<sigma> e2))"
      hence w: "val_type w = t2" by (simp add:)
      thus "return_val (<|v,w|>) = return (stock_measure (PRODUCT t1 t2)) (<|v,w|>)"
        by (auto simp: return_val_def v w)
    qed
    also have "... = return_val (<|v, expr_sem_rf \<sigma> e2|>)"
      using v B
      by (subst bind_return[where N="PRODUCT t1 t2"]) (auto simp: return_val_def)
    finally show "expr_sem \<sigma> e2 \<bind> (\<lambda>w. return_val (<|v,w|>)) = return_val (<|v, expr_sem_rf \<sigma> e2|>)" .
  qed
  also have "(\<lambda>v. <|v, expr_sem_rf \<sigma> e2|>) \<in> measurable (stock_measure t1) (stock_measure (PRODUCT t1 t2))"
    using B by (auto intro!: injI)
  hence "return (stock_measure t1) (expr_sem_rf \<sigma> e1) \<bind> (\<lambda>v. return_val (<|v, expr_sem_rf \<sigma> e2|>)) =
             return_val (<|expr_sem_rf \<sigma> e1, expr_sem_rf \<sigma> e2|>)"
    by (subst bind_return, rule measurable_compose[OF _ measurable_return_val])
       (auto simp: A)
  finally show "return_val (expr_sem_rf \<sigma> (<e1,e2>)) = expr_sem \<sigma> (<e1, e2>)" by simp
next
  case (et_if \<Gamma> b e1 t e2 V \<sigma>)
  let ?P = "\<lambda>e. expr_sem \<sigma> e = return_val (expr_sem_rf \<sigma> e)"
  from et_if.prems have A: "?P b" "?P e1" "?P e2" by ((intro et_if.IH[symmetric], simp_all) [])+
  from et_if.prems and et_if.hyps have "space (expr_sem \<sigma> b) = type_universe BOOL"
    by (intro space_expr_sem) (auto simp: state_measure_var_type)
  hence [simp]: "val_type (expr_sem_rf \<sigma> b) = BOOL" by (simp add: A return_val_def)
  have B: "return_val (expr_sem_rf \<sigma> e1) \<in> space (subprob_algebra (stock_measure t))"
          "return_val (expr_sem_rf \<sigma> e2) \<in> space (subprob_algebra (stock_measure t))"
    using et_if.hyps and et_if.prems
    by ((subst A[symmetric], intro measurable_space[OF measurable_expr_sem], auto) [])+
  thus ?case
    by (auto simp: A bind_return_val''[where M=t])
next
  case (et_op \<Gamma> e t oper t' V)
  let ?M = "PiM V (\<lambda>x. stock_measure (\<Gamma> x))"
  from et_op.prems have e: "return_val (expr_sem_rf \<sigma> e) = expr_sem \<sigma> e"
    by (intro et_op.IH[of V]) auto

  with et_op.prems have "space (return_val (expr_sem_rf \<sigma> e)) = type_universe t"
    by (subst e, subst space_expr_sem[OF et_op.hyps(1)])
       (auto dest: state_measure_var_type)
  hence A: "val_type (expr_sem_rf \<sigma> e) = t" "expr_sem_rf \<sigma> e \<in> type_universe t"
    by (auto simp add: return_val_def)
  from et_op.prems e
    have "expr_sem \<sigma> (Operator oper e) =
                 return_val (expr_sem_rf \<sigma> e) \<bind> (\<lambda>v. return_val (op_sem oper v))" by simp
  also have "... = return_val (op_sem oper (expr_sem_rf \<sigma> e))"
    by (subst return_val_def, rule bind_return,
        rule measurable_compose[OF measurable_op_sem measurable_return_val])
       (auto simp: A et_op.hyps)
  finally show "return_val (expr_sem_rf \<sigma> (Operator oper e)) = expr_sem \<sigma> (Operator oper e)" by simp
next
  case (et_let \<Gamma> e1 t1 e2 t2 V)
  let ?M = "state_measure V \<Gamma>" and ?N = "state_measure (shift_var_set V) (case_nat t1 \<Gamma>)"
  let ?\<sigma>' = "case_nat (expr_sem_rf \<sigma> e1) \<sigma>"
  from et_let.prems have e1: "return_val (expr_sem_rf \<sigma> e1) = expr_sem \<sigma> e1"
    by (auto intro!: et_let.IH(1)[of V])
  from et_let.prems have S: "space (return_val (expr_sem_rf \<sigma> e1)) = type_universe t1"
    by (subst e1, subst space_expr_sem[OF et_let.hyps(1)])
       (auto dest: state_measure_var_type)
  hence A: "val_type (expr_sem_rf \<sigma> e1) = t1" "expr_sem_rf \<sigma> e1 \<in> type_universe t1"
    by (auto simp add: return_val_def)
  with et_let.prems have e2: "\<And>\<sigma>. \<sigma> \<in> space ?N \<Longrightarrow> return_val (expr_sem_rf \<sigma> e2) = expr_sem \<sigma> e2"
    using subset_shift_var_set
    by (intro et_let.IH(2)[of "shift_var_set V"]) (auto simp del: fun_upd_apply)

  from et_let.prems have "expr_sem \<sigma> (LetVar e1 e2) =
                              return_val (expr_sem_rf \<sigma> e1) \<bind> (\<lambda>v. expr_sem (case_nat v \<sigma>) e2)"
    by (simp add: e1)
  also from et_let.prems
    have "... = return_val (expr_sem_rf \<sigma> e1) \<bind> (\<lambda>v. return_val (expr_sem_rf (case_nat v \<sigma>) e2))"
    by (intro bind_cong refl, subst e2) (auto simp: S)
  also from et_let have Me2[measurable]: "(\<lambda>\<sigma>. expr_sem_rf \<sigma> e2) \<in> measurable ?N (stock_measure t2)"
    using subset_shift_var_set by (intro measurable_expr_sem_rf) auto
  have "(\<lambda>(\<sigma>,y). case_nat y \<sigma>) \<circ> (\<lambda>y. (\<sigma>, y)) \<in> measurable (stock_measure t1) ?N"
    using \<open>\<sigma> \<in> space ?M\<close> by simp
  have  "return_val (expr_sem_rf \<sigma> e1) \<bind> (\<lambda>v. return_val (expr_sem_rf (case_nat v \<sigma>) e2)) =
              return_val (expr_sem_rf ?\<sigma>' e2)" using \<open>\<sigma> \<in> space ?M\<close>
  by (subst return_val_def, intro bind_return, subst A)
     (rule measurable_compose[OF _ measurable_return_val[of t2]], simp_all)
  finally show ?case by simp
qed simp_all

lemma val_type_expr_sem_rf:
  assumes "\<Gamma> \<turnstile> e : t" "randomfree e" "free_vars e \<subseteq> V" "\<sigma> \<in> space (state_measure V \<Gamma>)"
  shows "val_type (expr_sem_rf \<sigma> e) = t"
proof-
  have "type_universe (val_type (expr_sem_rf \<sigma> e)) = space (return_val (expr_sem_rf \<sigma> e))"
    by (simp add: return_val_def)
  also from assms have "return_val (expr_sem_rf \<sigma> e) = expr_sem \<sigma> e"
    by (intro expr_sem_rf_sound) auto
  also from assms have "space ... = type_universe t"
    by (intro space_expr_sem[of \<Gamma>])
       (auto simp: state_measure_def space_PiM  dest: PiE_mem)
  finally show ?thesis by simp
qed

lemma expr_sem_rf_eq_on_vars:
  "(\<And>x. x\<in>free_vars e \<Longrightarrow> \<sigma>1 x = \<sigma>2 x) \<Longrightarrow> expr_sem_rf \<sigma>1 e = expr_sem_rf \<sigma>2 e"
proof (induction e arbitrary: \<sigma>1 \<sigma>2)
  case (Operator oper e \<sigma>1 \<sigma>2)
  hence "expr_sem_rf \<sigma>1 e = expr_sem_rf \<sigma>2 e" by (intro Operator.IH) auto
  thus ?case by simp
next
  case (LetVar e1 e2 \<sigma>1 \<sigma>2)
  hence A: "expr_sem_rf \<sigma>1 e1 = expr_sem_rf \<sigma>2 e1" by (intro LetVar.IH) auto
  {
    fix y assume "y \<in> free_vars e2"
    hence "case_nat (expr_sem_rf \<sigma>1 e1) \<sigma>1 y = case_nat (expr_sem_rf \<sigma>2 e1) \<sigma>2 y"
      using LetVar(3) by (auto simp add: A split: nat.split)
  }
  hence "expr_sem_rf (case_nat (expr_sem_rf \<sigma>1 e1) \<sigma>1) e2 =
           expr_sem_rf (case_nat (expr_sem_rf \<sigma>2 e1) \<sigma>2) e2" by (intro LetVar.IH) simp
  thus ?case by simp
next
  case (Pair e1 e2 \<sigma>1 \<sigma>2)
  have "expr_sem_rf \<sigma>1 e1 = expr_sem_rf \<sigma>2 e1" "expr_sem_rf \<sigma>1 e2 = expr_sem_rf \<sigma>2 e2"
    by (intro Pair.IH, simp add: Pair)+
  thus ?case by simp
next
  case (IfThenElse b e1 e2 \<sigma>1 \<sigma>2)
  have "expr_sem_rf \<sigma>1 b = expr_sem_rf \<sigma>2 b" "expr_sem_rf \<sigma>1 e1 = expr_sem_rf \<sigma>2 e1"
       "expr_sem_rf \<sigma>1 e2 = expr_sem_rf \<sigma>2 e2" by (intro IfThenElse.IH, simp add: IfThenElse)+
  thus ?case by simp
next
  case (Random dst e \<sigma>1 \<sigma>2)
  have "expr_sem_rf \<sigma>1 e = expr_sem_rf \<sigma>2 e" by (intro Random.IH) (simp add: Random)
  thus ?case by simp
qed auto


(*
subsection {* Substitution of free variables *}

primrec expr_subst :: "expr \<Rightarrow> expr \<Rightarrow> vname \<Rightarrow> expr" ("_\<langle>_'/_\<rangle>" [1000,0,0] 999) where
  "(Val v)\<langle>_/_\<rangle> = Val v"
| "(Var y)\<langle>f/x\<rangle> = (if y = x then f else Var y)"
| "<e1,e2>\<langle>f/x\<rangle> = <e1\<langle>f/x\<rangle>, e2\<langle>f/x\<rangle>>"
| "(<oper> e)\<langle>f/x\<rangle> = <oper> (e\<langle>f/x\<rangle>)"
| "(LET e1 IN e2)\<langle>f/x\<rangle> = LET y = e1\<langle>f/x\<rangle> IN if y = x then e2 else e2\<langle>f/x\<rangle>"
| "(IF b THEN e1 ELSE e2)\<langle>f/x\<rangle> = IF b\<langle>f/x\<rangle> THEN e1\<langle>f/x\<rangle> ELSE e2\<langle>f/x\<rangle>"
| "(Random dst e)\<langle>f/x\<rangle> = Random dst (e\<langle>f/x\<rangle>)"
| "(Fail t)\<langle>f/x\<rangle> = Fail t"

primrec bound_vars :: "expr \<Rightarrow> vname set" where
  "bound_vars (Val _) = {}"
| "bound_vars (Var _) = {}"
| "bound_vars <e1,e2> = bound_vars e1 \<union> bound_vars e2"
| "bound_vars (<_> e) = bound_vars e"
| "bound_vars (LET x = e1 IN e2) = {x} \<union> bound_vars e1 \<union> bound_vars e2"
| "bound_vars (IF b THEN e1 ELSE e2) = bound_vars b \<union> bound_vars e1 \<union> bound_vars e2"
| "bound_vars (Random _ e) = bound_vars e"
| "bound_vars (Fail _) = {}"

lemma expr_typing_eq_on_free_vars:
  "\<Gamma>1 \<turnstile> e : t \<Longrightarrow> (\<And>x. x \<in> free_vars e \<Longrightarrow> \<Gamma>1 x = \<Gamma>2 x) \<Longrightarrow> \<Gamma>2 \<turnstile> e : t"
proof (induction arbitrary: \<Gamma>2 rule: expr_typing.induct)
  case et_let
  thus ?case by (intro expr_typing.intros) auto
qed (auto intro!: expr_typing.intros simp del: fun_upd_apply)

lemma expr_typing_subst:
  assumes "\<Gamma> \<turnstile> e : t1" "\<Gamma> \<turnstile> f : t'" "\<Gamma> x = t'" "free_vars f \<inter> bound_vars e = {}"
  shows "\<Gamma> \<turnstile> e\<langle>f/x\<rangle> : t1"
using assms
proof (induction rule: expr_typing.induct)
  case (et_let \<Gamma> e1 t1 y e2 t2)
  from et_let.prems have A: "\<Gamma> \<turnstile> e1\<langle>f/x\<rangle> : t1" by (intro et_let.IH) auto
  show ?case
  proof (cases "y = x")
    assume "y \<noteq> x"
    from et_let.prems have "\<Gamma>(y := t1) \<turnstile> f : t'"
      by (intro expr_typing_eq_on_free_vars[OF `\<Gamma> \<turnstile> f : t'`]) auto
    moreover from `y \<noteq> x` have "(\<Gamma>(y := t1)) x = \<Gamma> x" by simp
    ultimately have "\<Gamma>(y := t1) \<turnstile> e2\<langle>f/x\<rangle> : t2" using et_let.prems
      by (intro et_let.IH) (auto simp del: fun_upd_apply)
    with A and `y \<noteq> x` show ?thesis by (auto intro: expr_typing.intros)
  qed (insert et_let, auto intro!: expr_typing.intros simp del: fun_upd_apply)
qed (insert assms(2), auto intro: expr_typing.intros)

lemma expr_subst_randomfree:
  assumes "\<Gamma> \<turnstile> f : t" "randomfree f" "free_vars f \<subseteq> V" "free_vars f \<inter> bound_vars e = {}"
          "\<sigma> \<in> space (state_measure V \<Gamma>)"
  shows   "expr_sem \<sigma> (e\<langle>f/x\<rangle>) = expr_sem (\<sigma>(x := expr_sem_rf f \<sigma>)) e"
using assms(1,3,4,5)
proof (induction e arbitrary: \<sigma> V \<Gamma>)
  case (Pair e1 e2 \<sigma> V \<Gamma>)
    from Pair.prems have "expr_sem \<sigma> (e1\<langle>f/x\<rangle>) = expr_sem (\<sigma>(x := expr_sem_rf f \<sigma>)) e1"
                     and "expr_sem \<sigma> (e2\<langle>f/x\<rangle>) = expr_sem (\<sigma>(x := expr_sem_rf f \<sigma>)) e2"
      by (auto intro!: Pair.IH[of \<Gamma> V \<sigma>])
    thus ?case by (simp del: fun_upd_apply)
next
  case (IfThenElse b e1 e2 \<sigma> V \<Gamma>)
    from IfThenElse.prems
      have "expr_sem \<sigma> (b\<langle>f/x\<rangle>) = expr_sem (\<sigma>(x := expr_sem_rf f \<sigma>)) b"
           "expr_sem \<sigma> (e1\<langle>f/x\<rangle>) = expr_sem (\<sigma>(x := expr_sem_rf f \<sigma>)) e1"
           "expr_sem \<sigma> (e2\<langle>f/x\<rangle>) = expr_sem (\<sigma>(x := expr_sem_rf f \<sigma>)) e2"
      by (auto intro!: IfThenElse.IH[of \<Gamma> V \<sigma>])
    thus ?case by (simp only: expr_sem.simps expr_subst.simps)
next
  case (LetVar y e1 e2)
  from LetVar.prems have A: "expr_sem \<sigma> (e1\<langle>f/x\<rangle>) = expr_sem (\<sigma>(x := expr_sem_rf f \<sigma>)) e1"
    by (intro LetVar.IH) auto
  show ?case
  proof (cases "y = x")
    assume "y = x"
    with LetVar.prems show ?case by (auto simp add: A simp del: fun_upd_apply)
  next
    assume "y \<noteq> x"
    {
      fix v assume "v \<in> space (expr_sem (\<sigma>(x := expr_sem_rf f \<sigma>)) e1)"
      let ?\<sigma>' = "\<sigma>(y := v)" and ?\<Gamma>' = "\<Gamma>(y := val_type v)"
      from LetVar.prems have "\<Gamma>(y := val_type v) \<turnstile> f : t" by (auto intro: expr_typing_eq_on_free_vars)
      moreover from LetVar.prems have "?\<sigma>' \<in> space (state_measure (insert y V) ?\<Gamma>')"
        by (auto simp: state_measure_def space_PiM split: if_split_asm)
      ultimately have "expr_sem ?\<sigma>' (e2\<langle>f/x\<rangle>) = expr_sem (?\<sigma>'(x := expr_sem_rf f ?\<sigma>')) e2"
        using LetVar.prems and `y \<noteq> x`
        by (intro LetVar.IH(2)[of "\<Gamma>(y := val_type v)" "insert y V"]) (auto simp del: fun_upd_apply)
      also from LetVar.prems have "expr_sem_rf f ?\<sigma>' = expr_sem_rf f \<sigma>"
        by (intro expr_sem_rf_eq_on_vars) auto
      finally have "expr_sem (\<sigma>(y := v)) (e2\<langle>f/x\<rangle>) = expr_sem (\<sigma>(x := expr_sem_rf f \<sigma>, y := v)) e2"
        using `y \<noteq> x` by (subst fun_upd_twist) (simp_all del: fun_upd_apply)
    }
    with A and `y \<noteq> x` show ?thesis by (auto simp del: fun_upd_apply intro!: bind_cong)
  qed
qed (simp_all add: expr_sem_rf_sound assms)

lemma stock_measure_context_upd:
  "(\<lambda>y. stock_measure ((\<Gamma>(x := t)) y)) = (\<lambda>y. stock_measure (\<Gamma> y))(x := stock_measure t)"
  by (intro ext) simp

lemma Let_det_eq_subst:
  assumes "\<Gamma> \<turnstile> LET x = f IN e : t" "randomfree f" "free_vars (LET x = f IN e) \<subseteq> V"
          "free_vars f \<inter> bound_vars e = {}" "\<sigma> \<in> space (state_measure V \<Gamma>)"
  shows   "expr_sem \<sigma> (LET x = f IN e) = expr_sem \<sigma> (e\<langle>f/x\<rangle>)"
proof-
  from assms(1) obtain t' where t1: "\<Gamma> \<turnstile> f : t'" and t2: "\<Gamma>(x := t') \<turnstile> e : t" by auto
  with assms have "expr_sem \<sigma> (LET x = f IN e) =
                       return_val (expr_sem_rf f \<sigma>) \<bind> (\<lambda>v. expr_sem (\<sigma>(x := v)) e)" (is "_ = ?M")
    by (auto simp: expr_sem_rf_sound)
  also have "(\<lambda>\<sigma>. expr_sem \<sigma> e) \<circ> (\<lambda>(\<sigma>,v). \<sigma>(x := v)) \<circ> (\<lambda>v. (\<sigma>,v)) \<in>
                 measurable (stock_measure ((\<Gamma>(x := t')) x)) (subprob_algebra (stock_measure t))"
    apply (intro measurable_comp, rule measurable_Pair1', rule assms)
    apply (subst fun_upd_same, unfold state_measure_def)
    apply (rule measurable_add_dim', subst stock_measure_context_upd[symmetric])
    apply (insert assms, auto intro!: measurable_expr_sem[unfolded state_measure_def] t1 t2
                              simp del: fun_upd_apply)
    done
  hence "(\<lambda>v. expr_sem (\<sigma>(x := v)) e) \<in>
                 measurable (stock_measure ((\<Gamma>(x := t')) x)) (subprob_algebra (stock_measure t))"
    by (simp add: o_def)
  with assms have "?M = expr_sem (\<sigma>(x := expr_sem_rf f \<sigma>)) e"
    unfolding return_val_def
    by (intro bind_return) (auto simp: val_type_expr_sem_rf[OF t1]
                                       type_universe_def simp del: type_universe_type)
  also from assms t1 t2 have "... = expr_sem \<sigma> (e\<langle>f/x\<rangle>)"
    by (intro expr_subst_randomfree[symmetric]) auto
  finally show ?thesis .
qed *)

end
