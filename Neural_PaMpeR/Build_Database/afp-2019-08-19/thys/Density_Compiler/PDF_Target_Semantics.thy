(*
  Theory: PDF_Target_Semantics.thy
  Authors: Manuel Eberl

  The semantics of the target language.
*)

section \<open>Target Language Syntax and Semantics\<close>

theory PDF_Target_Semantics
imports PDF_Semantics
begin

datatype cexpr =
    CVar vname
  | CVal val
  | CPair cexpr cexpr ("<_, _>\<^sub>c" [0, 0] 1000)
  | COperator pdf_operator cexpr (infixl "$$\<^sub>c" 999)
  | CIf cexpr cexpr cexpr ("IF\<^sub>c _ THEN _ ELSE _" [0, 0, 10] 10)
  | CIntegral cexpr pdf_type ("\<integral>\<^sub>c _ \<partial>_" [61] 110)

abbreviation (input) cexpr_fun :: "(cexpr \<Rightarrow> cexpr) \<Rightarrow> cexpr" (binder "\<lambda>\<^sub>c" 10) where
  "cexpr_fun f \<equiv> f (CVar 0)"
abbreviation cexpr_Add (infixl "+\<^sub>c" 65) where
  "cexpr_Add a b \<equiv> Add $$\<^sub>c <a, b>\<^sub>c"
abbreviation cexpr_Minus ("-\<^sub>c _" [81] 80) where
  "cexpr_Minus a \<equiv> Minus $$\<^sub>c a"
abbreviation cexpr_Sub (infixl "-\<^sub>c" 65) where
  "cexpr_Sub a b \<equiv> a +\<^sub>c -\<^sub>cb"
abbreviation cexpr_Mult (infixl "*\<^sub>c" 70) where
  "cexpr_Mult a b \<equiv> Mult $$\<^sub>c <a, b>\<^sub>c"
abbreviation "inverse\<^sub>c e \<equiv>Inverse $$\<^sub>c e"
abbreviation cexpr_Div (infixl "'/\<^sub>c" 70) where
  "cexpr_Div a b \<equiv> a *\<^sub>c inverse\<^sub>c b"
abbreviation "fact\<^sub>c e \<equiv> Fact $$\<^sub>c e"
abbreviation "sqrt\<^sub>c e \<equiv> Sqrt $$\<^sub>c e"
abbreviation "exp\<^sub>c e \<equiv> Exp $$\<^sub>c e"
abbreviation "ln\<^sub>c e \<equiv> Ln $$\<^sub>c e"
abbreviation "fst\<^sub>c e \<equiv> Fst $$\<^sub>c e"
abbreviation "snd\<^sub>c e \<equiv> Snd $$\<^sub>c e"
abbreviation cexpr_Pow (infixl "^\<^sub>c" 75) where
  "cexpr_Pow a b \<equiv> Pow $$\<^sub>c <a, b>\<^sub>c"
abbreviation cexpr_And (infixl "\<and>\<^sub>c" 35) where
  "cexpr_And a b \<equiv> And $$\<^sub>c <a, b>\<^sub>c"
abbreviation cexpr_Or (infixl "\<or>\<^sub>c" 30) where
  "cexpr_Or a b \<equiv> Or $$\<^sub>c <a, b>\<^sub>c"
abbreviation cexpr_Not ("\<not>\<^sub>c _" [40] 40) where
  "cexpr_Not a \<equiv> Not $$\<^sub>c a"
abbreviation cexpr_Equals (infixl "=\<^sub>c" 70) where
  "cexpr_Equals a b \<equiv> Equals $$\<^sub>c <a, b>\<^sub>c"
abbreviation cexpr_Less (infixl "<\<^sub>c" 70) where
  "cexpr_Less a b \<equiv> Less $$\<^sub>c <a, b>\<^sub>c"
abbreviation cexpr_LessEq (infixl "\<le>\<^sub>c" 70) where
  "cexpr_LessEq a b \<equiv> a =\<^sub>c b \<or>\<^sub>c a <\<^sub>c b"
abbreviation cexpr_RealCast ("\<langle>_\<rangle>\<^sub>c" [0] 90) where
  "cexpr_RealCast a \<equiv> Cast REAL $$\<^sub>c a"
abbreviation CReal where
  "CReal x \<equiv> CVal (RealVal x)"
abbreviation CInt where
  "CInt x \<equiv> CVal (IntVal x)"
abbreviation \<pi>\<^sub>c where
  "\<pi>\<^sub>c \<equiv> Pi $$\<^sub>c (CVal UnitVal)"

instantiation cexpr :: expr
begin

primrec free_vars_cexpr :: "cexpr \<Rightarrow> vname set" where
  "free_vars_cexpr (CVar x) = {x}"
| "free_vars_cexpr (CVal _) = {}"
| "free_vars_cexpr (oper $$\<^sub>c e) = free_vars_cexpr e"
| "free_vars_cexpr (<e1, e2>\<^sub>c) = free_vars_cexpr e1 \<union> free_vars_cexpr e2"
| "free_vars_cexpr (IF\<^sub>c b THEN e1 ELSE e2) =
       free_vars_cexpr b \<union> free_vars_cexpr e1 \<union> free_vars_cexpr e2"
| "free_vars_cexpr (\<integral>\<^sub>c e \<partial>t) = Suc -` free_vars_cexpr e"

instance ..
end

inductive cexpr_typing :: "tyenv \<Rightarrow> cexpr \<Rightarrow> pdf_type \<Rightarrow> bool" ("(1_/ \<turnstile>\<^sub>c/ (_ :/ _))" [50,0,50] 50) where
  cet_val:    "\<Gamma> \<turnstile>\<^sub>c CVal v: val_type v"
| cet_var:    "\<Gamma> \<turnstile>\<^sub>c CVar x : \<Gamma> x"
| cet_pair:   "\<Gamma> \<turnstile>\<^sub>c e1 : t1 \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>c e2 : t2 \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>c <e1, e2>\<^sub>c : PRODUCT t1 t2"
| cet_op:     "\<Gamma> \<turnstile>\<^sub>c e : t \<Longrightarrow> op_type oper t = Some t' \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>c oper $$\<^sub>c e : t'"
| cet_if:     "\<Gamma> \<turnstile>\<^sub>c b : BOOL \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>c e1 : t \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>c e2 : t
                   \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>c IF\<^sub>c b THEN e1 ELSE e2 : t"
| cet_int:    "t \<cdot> \<Gamma> \<turnstile>\<^sub>c e : REAL \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>c \<integral>\<^sub>c e \<partial>t : REAL"

lemma cet_val': "t = val_type v \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>c CVal v : t"
  by (simp add: cet_val)

lemma cet_var': "t = \<Gamma> x \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>c CVar x : t"
  by (simp add: cet_var)

lemma cet_not: "\<Gamma> \<turnstile>\<^sub>c e : BOOL \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>c \<not>\<^sub>c e : BOOL"
  by (intro cet_op[where t = "BOOL"] cet_pair, simp, simp)

lemma cet_and: "\<Gamma> \<turnstile>\<^sub>c e1 : BOOL \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>c e2 : BOOL \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>c e1 \<and>\<^sub>c e2 : BOOL" and
      cet_or: "\<Gamma> \<turnstile>\<^sub>c e1 : BOOL \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>c e2 : BOOL \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>c e1 \<or>\<^sub>c e2 : BOOL"
  by (intro cet_op[where t = "PRODUCT BOOL BOOL"] cet_pair, simp, simp, simp)+

lemma cet_minus_real: "\<Gamma> \<turnstile>\<^sub>c e : REAL \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>c -\<^sub>ce : REAL" and
      cet_inverse: "\<Gamma> \<turnstile>\<^sub>c e : REAL \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>c inverse\<^sub>c e : REAL" and
      cet_sqrt: "\<Gamma> \<turnstile>\<^sub>c e : REAL \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>c sqrt\<^sub>c e : REAL" and
      cet_exp: "\<Gamma> \<turnstile>\<^sub>c e : REAL \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>c exp\<^sub>c e : REAL" and
      cet_ln: "\<Gamma> \<turnstile>\<^sub>c e : REAL \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>c ln\<^sub>c e : REAL"
  by (rule cet_op[where t = "REAL"], simp, simp)+

lemma cet_pow_real: "\<Gamma> \<turnstile>\<^sub>c e1 : REAL \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>c e2 : INTEG \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>c e1 ^\<^sub>c e2 : REAL"
  by (intro cet_op[where t = "PRODUCT REAL INTEG"] cet_pair) simp_all

lemma cet_add_real: "\<Gamma> \<turnstile>\<^sub>c e1 : REAL \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>c e2 : REAL \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>c e1 +\<^sub>c e2 : REAL" and
      cet_mult_real: "\<Gamma> \<turnstile>\<^sub>c e1 : REAL \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>c e2 : REAL \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>c e1 *\<^sub>c e2 : REAL" and
      cet_less_real: "\<Gamma> \<turnstile>\<^sub>c e1 : REAL \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>c e2 : REAL \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>c e1 <\<^sub>c e2 : BOOL"
  by (intro cet_op[where t = "PRODUCT REAL REAL"] cet_pair, simp, simp, simp)+


lemma cet_eq: "\<Gamma> \<turnstile>\<^sub>c e1 : t \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>c e2 : t \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>c e1 =\<^sub>c e2 : BOOL"
  by (intro cet_op[where t = "PRODUCT t t"] cet_pair, simp, simp, simp)+

lemma cet_less_eq_real: "\<Gamma> \<turnstile>\<^sub>c e1 : REAL \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>c e2 : REAL \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>c e1 \<le>\<^sub>c e2 : BOOL"
  by (intro cet_less_real cet_or cet_eq)

lemma cet_minus_int: "\<Gamma> \<turnstile>\<^sub>c e : INTEG \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>c -\<^sub>ce : INTEG"
  by (rule cet_op[where t = "INTEG"], simp, simp)+

lemma cet_add_int: "\<Gamma> \<turnstile>\<^sub>c e1 : INTEG \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>c e2 : INTEG \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>c e1 +\<^sub>c e2 : INTEG" and
      cet_mult_int: "\<Gamma> \<turnstile>\<^sub>c e1 : INTEG \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>c e2 : INTEG \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>c e1 *\<^sub>c e2 : INTEG" and
      cet_less_int: "\<Gamma> \<turnstile>\<^sub>c e1 : INTEG \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>c e2 : INTEG \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>c e1 <\<^sub>c e2 : BOOL"
  by (intro cet_op[where t = "PRODUCT INTEG INTEG"] cet_pair, simp, simp, simp)+

lemma cet_less_eq_int: "\<Gamma> \<turnstile>\<^sub>c e1 : INTEG \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>c e2 : INTEG \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>c e1 \<le>\<^sub>c e2 : BOOL"
  by (intro cet_less_int cet_or cet_eq)

lemma cet_sub_int: "\<Gamma> \<turnstile>\<^sub>c e1 : INTEG \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>c e2 : INTEG \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>c e1 -\<^sub>c e2 : INTEG"
  by (intro cet_minus_int cet_add_int)

lemma cet_fst: "\<Gamma> \<turnstile>\<^sub>c e : PRODUCT t t' \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>c fst\<^sub>c e : t" and
      cet_snd: "\<Gamma> \<turnstile>\<^sub>c e : PRODUCT t t' \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>c snd\<^sub>c e : t'"
  by (erule cet_op, simp)+

lemma cet_cast_real: "\<Gamma> \<turnstile>\<^sub>c e : BOOL \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>c \<langle>e\<rangle>\<^sub>c : REAL"
  by (intro cet_op[where t = BOOL]) simp_all

lemma cet_cast_real_int: "\<Gamma> \<turnstile>\<^sub>c e : INTEG \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>c \<langle>e\<rangle>\<^sub>c : REAL"
  by (intro cet_op[where t = INTEG]) simp_all

lemma cet_sub_real: "\<Gamma> \<turnstile>\<^sub>c e1 : REAL \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>c e2 : REAL \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>c e1 -\<^sub>c e2 : REAL"
  by (intro cet_minus_real cet_add_real)

lemma cet_pi: "\<Gamma> \<turnstile>\<^sub>c \<pi>\<^sub>c : REAL"
  by (rule cet_op, rule cet_val, simp)

lemmas cet_op_intros =
  cet_minus_real cet_exp cet_sqrt cet_ln cet_inverse cet_pow_real cet_pi
  cet_cast_real cet_add_real cet_mult_real cet_less_real
  cet_not cet_and cet_or

inductive_cases cexpr_typing_valE[elim]:  "\<Gamma> \<turnstile>\<^sub>c CVal v : t"
inductive_cases cexpr_typing_varE[elim]:  "\<Gamma> \<turnstile>\<^sub>c CVar x : t"
inductive_cases cexpr_typing_pairE[elim]: "\<Gamma> \<turnstile>\<^sub>c <e1, e2>\<^sub>c : t"
inductive_cases cexpr_typing_opE[elim]:   "\<Gamma> \<turnstile>\<^sub>c oper $$\<^sub>c e : t"
inductive_cases cexpr_typing_ifE[elim]:   "\<Gamma> \<turnstile>\<^sub>c IF\<^sub>c b THEN e1 ELSE e2 : t"
inductive_cases cexpr_typing_intE[elim]:  "\<Gamma> \<turnstile>\<^sub>c \<integral>\<^sub>c e \<partial>t : t'"

primrec cexpr_type :: "tyenv \<Rightarrow> cexpr \<Rightarrow> pdf_type option" where
  "cexpr_type _ (CVal v) = Some (val_type v)"
| "cexpr_type \<Gamma> (CVar x) = Some (\<Gamma> x)"
| "cexpr_type \<Gamma> (<e1, e2>\<^sub>c) = (case (cexpr_type \<Gamma> e1, cexpr_type \<Gamma> e2) of
                                (Some t1, Some t2) \<Rightarrow> Some (PRODUCT t1 t2)
                              | _ \<Rightarrow> None)"
| "cexpr_type \<Gamma> (oper $$\<^sub>c e) = (case cexpr_type \<Gamma> e of
                                 Some t \<Rightarrow> op_type oper t
                               | _ \<Rightarrow> None)"
| "cexpr_type \<Gamma> (IF\<^sub>c b THEN e1 ELSE e2) =
                              (if cexpr_type \<Gamma> b = Some BOOL then
                                 case (cexpr_type \<Gamma> e1, cexpr_type \<Gamma> e2) of
                                   (Some t, Some t') \<Rightarrow> if t = t' then Some t else None
                                 | _ \<Rightarrow> None
                               else None)"
| "cexpr_type \<Gamma> (\<integral>\<^sub>c e \<partial>t) =
      (if cexpr_type (case_nat t \<Gamma>) e = Some REAL then Some REAL else None)"

lemma cexpr_type_Some_iff: "cexpr_type \<Gamma> e = Some t \<longleftrightarrow> \<Gamma> \<turnstile>\<^sub>c e : t"
  apply rule
  apply (induction e arbitrary: \<Gamma> t,
         auto intro!: cexpr_typing.intros split: option.split_asm if_split_asm) []
  apply (induction rule: cexpr_typing.induct, auto)
  done

lemmas cexpr_typing_code[code_unfold] = cexpr_type_Some_iff[symmetric]

lemma cexpr_typing_cong':
  assumes "\<Gamma> \<turnstile>\<^sub>c e : t" "\<And>x. x \<in> free_vars e \<Longrightarrow> \<Gamma> x = \<Gamma>' x"
  shows "\<Gamma>' \<turnstile>\<^sub>c e : t"
using assms
proof (induction arbitrary: \<Gamma>' rule: cexpr_typing.induct)
  case (cet_int t \<Gamma> e \<Gamma>')
  hence "\<And>x. x \<in> free_vars e \<Longrightarrow> case_nat t \<Gamma> x = case_nat t \<Gamma>' x"
    by (auto split: nat.split)
  from cet_int.IH[OF this] show ?case by (auto intro!: cexpr_typing.intros)
qed (auto intro!: cexpr_typing.intros)

lemma cexpr_typing_cong:
  assumes "\<And>x. x \<in> free_vars e \<Longrightarrow> \<Gamma> x = \<Gamma>' x"
  shows "\<Gamma> \<turnstile>\<^sub>c e : t \<longleftrightarrow> \<Gamma>' \<turnstile>\<^sub>c e : t"
  by (rule iffI) (erule cexpr_typing_cong', simp add: assms)+


primrec cexpr_sem :: "state \<Rightarrow> cexpr \<Rightarrow> val" where
  "cexpr_sem \<sigma> (CVal v) = v"
| "cexpr_sem \<sigma> (CVar x) = \<sigma> x"
| "cexpr_sem \<sigma> <e1, e2>\<^sub>c = <|cexpr_sem \<sigma> e1, cexpr_sem \<sigma> e2|>"
| "cexpr_sem \<sigma> (oper $$\<^sub>c e) = op_sem oper (cexpr_sem \<sigma> e)"
| "cexpr_sem \<sigma> (IF\<^sub>c b THEN e1 ELSE e2) = (if cexpr_sem \<sigma> b = TRUE then cexpr_sem \<sigma> e1 else cexpr_sem \<sigma> e2)"
| "cexpr_sem \<sigma> (\<integral>\<^sub>c e \<partial>t) = RealVal (\<integral>x. extract_real (cexpr_sem (x \<cdot> \<sigma>) e) \<partial>(stock_measure t))"

definition cexpr_equiv :: "cexpr \<Rightarrow> cexpr \<Rightarrow> bool" where
  "cexpr_equiv e1 e2 \<equiv> \<forall>\<sigma>. cexpr_sem \<sigma> e1 = cexpr_sem \<sigma> e2"

lemma cexpr_equiv_commute: "cexpr_equiv e1 e2 \<longleftrightarrow> cexpr_equiv e2 e1"
  by (auto simp: cexpr_equiv_def)


lemma val_type_cexpr_sem[simp]:
  assumes "\<Gamma> \<turnstile>\<^sub>c e : t" "free_vars e \<subseteq> V" "\<sigma> \<in> space (state_measure V \<Gamma>)"
  shows "val_type (cexpr_sem \<sigma> e) = t"
using assms by (induction arbitrary: \<sigma> V rule: cexpr_typing.induct)
               (auto intro: state_measure_var_type op_sem_val_type)

lemma cexpr_sem_eq_on_vars:
  assumes "\<And>x. x \<in> free_vars e \<Longrightarrow> \<sigma> x = \<sigma>' x"
  shows "cexpr_sem \<sigma> e = cexpr_sem \<sigma>' e"
using assms
proof (induction e arbitrary: \<sigma> \<sigma>')
  case (CPair e1 e2 \<sigma> \<sigma>')
  from CPair.prems show ?case by (auto intro!: CPair.IH)
next
  case (COperator oper e \<sigma> \<sigma>')
  from COperator.prems show ?case by (auto simp: COperator.IH[of \<sigma> \<sigma>'])
next
  case (CIf b e1 e2 \<sigma> \<sigma>')
  from CIf.prems show ?case by (auto simp: CIf.IH[of \<sigma> \<sigma>'])
next
  case (CIntegral e t \<sigma> \<sigma>')
  have "cexpr_sem \<sigma> (\<integral>\<^sub>c e \<partial>t) = RealVal (\<integral>x. extract_real (cexpr_sem (case_nat x \<sigma>) e) \<partial>stock_measure t)"
    by simp
  also from CIntegral.prems have A: "(\<lambda>v. cexpr_sem (case_nat v \<sigma>) e) = (\<lambda>v. cexpr_sem (case_nat v \<sigma>') e)"
    by (intro ext CIntegral.IH) (auto split: nat.split)
  also have "RealVal (\<integral>x. extract_real (cexpr_sem (case_nat x \<sigma>') e) \<partial>stock_measure t) = cexpr_sem \<sigma>' (\<integral>\<^sub>c e \<partial>t)"
    by simp
  finally show ?case .
qed simp_all


definition eval_cexpr :: "cexpr \<Rightarrow> state \<Rightarrow> val \<Rightarrow> real" where
  "eval_cexpr e \<sigma> v = extract_real (cexpr_sem (case_nat v \<sigma>) e)"

lemma measurable_cexpr_sem[measurable]:
  "\<Gamma> \<turnstile>\<^sub>c e : t \<Longrightarrow> free_vars e \<subseteq> V \<Longrightarrow>
      (\<lambda>\<sigma>. cexpr_sem \<sigma> e) \<in> measurable (state_measure V \<Gamma>) (stock_measure t)"
proof (induction arbitrary: V rule: cexpr_typing.induct)
  case (cet_op oper t t' \<Gamma> e)
      thus ?case using measurable_op_sem by simp
next
  case (cet_int t \<Gamma> e)
  interpret sigma_finite_measure "stock_measure t" by simp
  let ?M = "(\<Pi>\<^sub>M x\<in>V. stock_measure (\<Gamma> x)) \<Otimes>\<^sub>M stock_measure t"
  let ?N = "embed_measure lborel RealVal"
  have *[measurable]: "(\<lambda>a. cexpr_sem a e) \<in> measurable (state_measure (shift_var_set V) (case_nat t \<Gamma>)) REAL"
    using cet_int.prems subset_shift_var_set
    by (intro cet_int.IH) simp
  show ?case
    by simp
qed (simp_all add: state_measure_def inj_PairVal)

lemma measurable_eval_cexpr[measurable]:
  assumes "case_nat t \<Gamma> \<turnstile>\<^sub>c e : REAL"
  assumes "free_vars e \<subseteq> shift_var_set V"
  shows "case_prod (eval_cexpr e) \<in> borel_measurable (state_measure V \<Gamma> \<Otimes>\<^sub>M stock_measure t)"
  unfolding eval_cexpr_def[abs_def] using measurable_cexpr_sem[OF assms] by simp

lemma cexpr_sem_Add:
  assumes "\<Gamma> \<turnstile>\<^sub>c e1 : REAL" "\<Gamma> \<turnstile>\<^sub>c e2 : REAL"
  assumes "\<sigma> \<in> space (state_measure V \<Gamma>)" "free_vars e1 \<subseteq> V" "free_vars e2 \<subseteq> V"
  shows "extract_real (cexpr_sem \<sigma> (e1 +\<^sub>c e2)) = extract_real (cexpr_sem \<sigma> e1) + extract_real (cexpr_sem \<sigma> e2)"
  using val_type_cexpr_sem[OF assms(1,4,3)] val_type_cexpr_sem[OF assms(2,5,3)]
  by (auto simp: lift_RealIntVal2_def extract_real_def split: val.split)

lemma cexpr_sem_Mult:
  assumes "\<Gamma> \<turnstile>\<^sub>c e1 : REAL" "\<Gamma> \<turnstile>\<^sub>c e2 : REAL"
  assumes "\<sigma> \<in> space (state_measure V \<Gamma>)" "free_vars e1 \<subseteq> V" "free_vars e2 \<subseteq> V"
  shows "extract_real (cexpr_sem \<sigma> (e1 *\<^sub>c e2)) = extract_real (cexpr_sem \<sigma> e1) * extract_real (cexpr_sem \<sigma> e2)"
  using val_type_cexpr_sem[OF assms(1,4,3)] val_type_cexpr_sem[OF assms(2,5,3)]
  by (auto simp: lift_RealIntVal2_def extract_real_def split: val.split)


subsection \<open>General functions on Expressions\<close>

text \<open>
   Transform variable names in an expression.
\<close>
primrec map_vars :: "(vname \<Rightarrow> vname) \<Rightarrow> cexpr \<Rightarrow> cexpr" where
  "map_vars f (CVal v) = CVal v"
| "map_vars f (CVar x) = CVar (f x)"
| "map_vars f (<e1, e2>\<^sub>c) = <map_vars f e1, map_vars f e2>\<^sub>c"
| "map_vars f (oper $$\<^sub>c e) = oper $$\<^sub>c (map_vars f e)"
| "map_vars f (IF\<^sub>c b THEN e1 ELSE e2) = (IF\<^sub>c map_vars f b THEN map_vars f e1 ELSE map_vars f e2)"
| "map_vars f (\<integral>\<^sub>c e \<partial>t) = \<integral>\<^sub>c map_vars (case_nat 0 (\<lambda>x. Suc (f x))) e \<partial>t"

lemma free_vars_map_vars[simp]:
  "free_vars (map_vars f e) = f ` free_vars e"
proof (induction e arbitrary: f)
  case (CIntegral e t f)
  {
    fix x A assume "Suc x \<in> A"
    hence "Suc (f x) \<in> case_nat 0 (\<lambda>x. Suc (f x)) ` A"
      by (subst image_iff, intro bexI[of _ "Suc x"]) (simp split: nat.split)
  }
  with CIntegral show ?case by (auto split: nat.split_asm)
qed auto

lemma cexpr_typing_map_vars:
  "\<Gamma> \<circ> f \<turnstile>\<^sub>c e : t \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>c map_vars f e : t"
proof (induction "\<Gamma> \<circ> f" e t arbitrary: \<Gamma> f rule: cexpr_typing.induct)
  case (cet_int t e \<Gamma>)
  have "case_nat t (\<Gamma> \<circ> f) = case_nat t \<Gamma> \<circ> (case_nat 0 (\<lambda>x. Suc (f x)))"
    by (intro ext) (auto split: nat.split)
  from cet_int(2)[OF this] show ?case by (auto intro!: cexpr_typing.intros)
qed (auto intro!: cexpr_typing.intros)

lemma cexpr_sem_map_vars:
  "cexpr_sem \<sigma> (map_vars f e) = cexpr_sem (\<sigma> \<circ> f) e"
proof (induction e arbitrary: \<sigma> f)
  case (CIntegral e t \<sigma> f)
  {
    fix x
    have "cexpr_sem (case_nat x \<sigma>) (map_vars (case_nat 0 (\<lambda>x. Suc (f x))) e) =
                 cexpr_sem (case_nat x \<sigma> \<circ> case_nat 0 (\<lambda>x. Suc (f x))) e"
      by (rule CIntegral.IH)
    also have "case_nat x \<sigma> \<circ> case_nat 0 (\<lambda>x. Suc (f x)) = case_nat x (\<lambda>a. \<sigma> (f a))"
      by (intro ext) (auto simp add: o_def split: nat.split)
    finally have "cexpr_sem (case_nat x \<sigma>) (map_vars (case_nat 0 (\<lambda>x. Suc (f x))) e) =
                      cexpr_sem (case_nat x (\<lambda>a. \<sigma> (f a))) e" .
  }
  thus ?case by simp
qed simp_all

definition insert_var :: "vname \<Rightarrow> (vname \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> vname \<Rightarrow> 'a" where
  "insert_var v f x w \<equiv> if w = v then x else if w > v then f (w - 1) else f w"

lemma insert_var_0[simp]: "insert_var 0 f x = case_nat x f"
  by (intro ext) (simp add: insert_var_def split: nat.split)

text \<open>
  Substitutes expression e for variable x in e'.
\<close>
primrec cexpr_subst :: "vname \<Rightarrow> cexpr \<Rightarrow> cexpr \<Rightarrow> cexpr" where
  "cexpr_subst _ _ (CVal v) = CVal v"
| "cexpr_subst x e (CVar y) = insert_var x CVar e y"
| "cexpr_subst x e <e1, e2>\<^sub>c = <cexpr_subst x e e1, cexpr_subst x e e2>\<^sub>c"
| "cexpr_subst x e (oper $$\<^sub>c e') = oper $$\<^sub>c (cexpr_subst x e e')"
| "cexpr_subst x e (IF\<^sub>c b THEN e1 ELSE e2) =
      (IF\<^sub>c cexpr_subst x e b THEN cexpr_subst x e e1 ELSE cexpr_subst x e e2)"
| "cexpr_subst x e (\<integral>\<^sub>c e' \<partial>t) = (\<integral>\<^sub>c cexpr_subst (Suc x) (map_vars Suc e) e' \<partial>t)"

lemma cexpr_sem_cexpr_subst_aux:
    "cexpr_sem \<sigma> (cexpr_subst x e e') = cexpr_sem (insert_var x \<sigma> (cexpr_sem \<sigma> e)) e'"
proof (induction e' arbitrary: x e \<sigma>)
  case (CIntegral e' t x e \<sigma>)
    have A: "\<And>y. insert_var (Suc x) (case_nat y \<sigma>) (cexpr_sem \<sigma> e) =
                    case_nat y (insert_var x \<sigma> (cexpr_sem \<sigma> e))"
      by (intro ext) (simp add: insert_var_def split: nat.split)
  show ?case by (simp add: o_def A cexpr_sem_map_vars CIntegral.IH)
qed (simp_all add: insert_var_def)

text \<open>
   This corresponds to a Let-binding; the variable with index 0 is substituted
   with the given expression.
\<close>
lemma cexpr_sem_cexpr_subst:
    "cexpr_sem \<sigma> (cexpr_subst 0 e e') = cexpr_sem (case_nat (cexpr_sem \<sigma> e) \<sigma>) e'"
  using cexpr_sem_cexpr_subst_aux by simp

lemma cexpr_typing_subst_aux:
  assumes "insert_var x \<Gamma> t \<turnstile>\<^sub>c e' : t'" "\<Gamma> \<turnstile>\<^sub>c e : t"
  shows "\<Gamma> \<turnstile>\<^sub>c cexpr_subst x e e' : t'"
using assms
proof (induction e' arbitrary: x \<Gamma> e t')
  case CVar
  thus ?case by (auto intro!: cexpr_typing.intros simp: insert_var_def)
next
  case COperator
  thus ?case by (auto simp: cexpr_type_Some_iff[symmetric] split: option.split_asm)
next
  case (CIntegral e' t'')
  have t': "t' = REAL" using CIntegral.prems(1) by auto
  have "case_nat t'' (insert_var x \<Gamma> t) \<turnstile>\<^sub>c e' : t'" using CIntegral.prems(1) by auto
  also have "case_nat t'' (insert_var x \<Gamma> t) = insert_var (Suc x) (case_nat t'' \<Gamma>) t"
    by (intro ext) (simp add: insert_var_def split: nat.split)
  finally have "insert_var (Suc x) (case_nat t'' \<Gamma>) t \<turnstile>\<^sub>c e' : t'" .
  moreover from CIntegral.prems(2) have "case_nat t'' \<Gamma> \<turnstile>\<^sub>c map_vars Suc e : t"
    by (intro cexpr_typing_map_vars) (simp add: o_def)
  ultimately have "case_nat t'' \<Gamma> \<turnstile>\<^sub>c cexpr_subst (Suc x) (map_vars Suc e) e' : t'"
    by (rule CIntegral.IH)
  thus ?case by (auto intro: cet_int simp: t')
qed (auto intro!: cexpr_typing.intros)

lemma cexpr_typing_subst[intro]:
  assumes "\<Gamma> \<turnstile>\<^sub>c e : t" "case_nat t \<Gamma> \<turnstile>\<^sub>c e' : t'"
  shows "\<Gamma> \<turnstile>\<^sub>c cexpr_subst 0 e e' : t'"
  using cexpr_typing_subst_aux assms by simp


lemma free_vars_cexpr_subst_aux:
  "free_vars (cexpr_subst x e e') \<subseteq> (\<lambda>y. if y \<ge> x then y + 1 else y) -` free_vars e' \<union> free_vars e"
    (is "free_vars _ \<subseteq> ?f x -` _ \<union> _")
proof (induction e' arbitrary: x e)
  case (CVar y x e)
  show ?case by (auto simp: insert_var_def)
next
  case (CPair e'1 e'2 x e)
  from CPair.IH[of x e] show ?case by auto
next
  case (COperator _ _ x e)
  from COperator.IH[of x e] show ?case by auto
next
  case (CIf b e'1 e'2 x e)
  from CIf.IH[of x e] show ?case by auto
next
  case (CIntegral e' t x e)
  have "free_vars (cexpr_subst x e (\<integral>\<^sub>c e' \<partial>t)) \<subseteq>
          Suc -` (?f (Suc x) -` free_vars e') \<union>
          Suc -` (free_vars (map_vars Suc e))" (is "_ \<subseteq> ?A \<union> ?B")
    by (simp only: cexpr_subst.simps free_vars_cexpr.simps
                   vimage_mono CIntegral.IH vimage_Un[symmetric])
  also have "?B = free_vars e" by (simp add: inj_vimage_image_eq)
  also have "?A \<subseteq> ?f x -` free_vars (\<integral>\<^sub>c e' \<partial>t)" by auto
  finally show ?case by blast
qed simp_all

lemma free_vars_cexpr_subst:
    "free_vars (cexpr_subst 0 e e') \<subseteq> Suc -` free_vars e' \<union> free_vars e"
  by (rule order.trans[OF free_vars_cexpr_subst_aux]) (auto simp: shift_var_set_def)



primrec cexpr_comp_aux :: "vname \<Rightarrow> cexpr \<Rightarrow> cexpr \<Rightarrow> cexpr" where
  "cexpr_comp_aux _ _ (CVal v) = CVal v"
| "cexpr_comp_aux x e (CVar y) = (if x = y then e else CVar y)"
| "cexpr_comp_aux x e <e1, e2>\<^sub>c = <cexpr_comp_aux x e e1, cexpr_comp_aux x e e2>\<^sub>c"
| "cexpr_comp_aux x e (oper $$\<^sub>c e') = oper $$\<^sub>c (cexpr_comp_aux x e e')"
| "cexpr_comp_aux x e (IF\<^sub>c b THEN e1 ELSE e2) =
      (IF\<^sub>c cexpr_comp_aux x e b THEN cexpr_comp_aux x e e1 ELSE cexpr_comp_aux x e e2)"
| "cexpr_comp_aux x e (\<integral>\<^sub>c e' \<partial>t) = (\<integral>\<^sub>c cexpr_comp_aux (Suc x) (map_vars Suc e) e' \<partial>t)"

lemma cexpr_sem_cexpr_comp_aux:
    "cexpr_sem \<sigma> (cexpr_comp_aux x e e') = cexpr_sem (\<sigma>(x := cexpr_sem \<sigma> e)) e'"
proof (induction e' arbitrary: x e \<sigma>)
  case (CIntegral e' t x e \<sigma>)
  have "\<And>y. (case_nat y \<sigma>)(Suc x := cexpr_sem (case_nat y \<sigma>) (map_vars Suc e)) =
                 case_nat y (\<sigma>(x := cexpr_sem \<sigma> e))"
    by (intro ext) (auto simp: cexpr_sem_map_vars o_def split: nat.split)
  thus ?case by (auto intro!: integral_cong simp: CIntegral.IH simp del: fun_upd_apply)
qed (simp_all add: insert_var_def)

definition cexpr_comp (infixl "\<circ>\<^sub>c" 55) where
  "cexpr_comp b a \<equiv> cexpr_comp_aux 0 a b"

lemma cexpr_typing_cexpr_comp_aux:
  assumes "\<Gamma>(x := t1) \<turnstile>\<^sub>c e' : t2" "\<Gamma> \<turnstile>\<^sub>c e : t1"
  shows "\<Gamma> \<turnstile>\<^sub>c cexpr_comp_aux x e e' : t2"
using assms
proof (induction e' arbitrary: \<Gamma> e x t2)
  case COperator
  thus ?case by (elim cexpr_typing_opE) (auto intro!: cexpr_typing.intros) []
next
  case CPair
  thus ?case by (elim cexpr_typing_pairE) (auto intro!: cexpr_typing.intros) []
next
  case (CIntegral e' t \<Gamma> e x t2)
  from CIntegral.prems have [simp]: "t2 = REAL" by auto
  from CIntegral.prems have "case_nat t (\<Gamma>(x := t1)) \<turnstile>\<^sub>c e' : REAL" by (elim cexpr_typing_intE)
  also have "case_nat t (\<Gamma>(x := t1)) = (case_nat t \<Gamma>)(Suc x := t1)"
    by (intro ext) (simp split: nat.split)
  finally have "... \<turnstile>\<^sub>c e' : REAL" .
  thus "\<Gamma> \<turnstile>\<^sub>c cexpr_comp_aux x e (\<integral>\<^sub>c e' \<partial>t) : t2"
    by (auto intro!: cexpr_typing.intros CIntegral.IH cexpr_typing_map_vars
             simp: o_def CIntegral.prems)
qed (auto intro!: cexpr_typing.intros)

lemma cexpr_typing_cexpr_comp[intro]:
  assumes "case_nat t1 \<Gamma> \<turnstile>\<^sub>c g : t2"
  assumes "case_nat t2 \<Gamma> \<turnstile>\<^sub>c f : t3"
  shows "case_nat t1 \<Gamma> \<turnstile>\<^sub>c f \<circ>\<^sub>c g : t3"
proof (unfold cexpr_comp_def, intro cexpr_typing_cexpr_comp_aux)
  have "(case_nat t1 \<Gamma>)(0 := t2) = case_nat t2 \<Gamma>"
    by (intro ext) (simp split: nat.split)
  with assms show "(case_nat t1 \<Gamma>)(0 := t2) \<turnstile>\<^sub>c f : t3" by simp
qed (insert assms)


lemma free_vars_cexpr_comp_aux:
  "free_vars (cexpr_comp_aux x e e') \<subseteq> (free_vars e' - {x}) \<union> free_vars e"
proof (induction e' arbitrary: x e)
  case (CIntegral e' t x e)
  note IH = CIntegral.IH[of "Suc x" "map_vars Suc e"]
  have "free_vars (cexpr_comp_aux x e (\<integral>\<^sub>c e' \<partial>t)) =
           Suc -` free_vars (cexpr_comp_aux (Suc x) (map_vars Suc e) e')" by simp
  also have "... \<subseteq> Suc -` (free_vars e' - {Suc x} \<union> free_vars (map_vars Suc e))"
    by (rule vimage_mono, rule CIntegral.IH)
  also have "... \<subseteq> free_vars (\<integral>\<^sub>c e' \<partial>t) - {x} \<union> free_vars e"
    by (auto simp add: vimage_Diff vimage_image_eq)
  finally show ?case .
qed (simp, blast?)+

lemma free_vars_cexpr_comp:
  "free_vars (cexpr_comp e e') \<subseteq> (free_vars e - {0}) \<union> free_vars e'"
  by (simp add: free_vars_cexpr_comp_aux cexpr_comp_def)

lemma free_vars_cexpr_comp':
  "free_vars (cexpr_comp e e') \<subseteq> free_vars e \<union> free_vars e'"
  using free_vars_cexpr_comp by blast

lemma cexpr_sem_cexpr_comp:
    "cexpr_sem \<sigma> (f \<circ>\<^sub>c g) = cexpr_sem (\<sigma>(0 := cexpr_sem \<sigma> g)) f"
  unfolding cexpr_comp_def by (simp add: cexpr_sem_cexpr_comp_aux)

lemma eval_cexpr_comp:
    "eval_cexpr (f \<circ>\<^sub>c g) \<sigma> x = eval_cexpr f \<sigma> (cexpr_sem (case_nat x \<sigma>) g)"
proof-
  have "(case_nat x \<sigma>)(0 := cexpr_sem (case_nat x \<sigma>) g) = case_nat (cexpr_sem (case_nat x \<sigma>) g) \<sigma>"
    by (intro ext) (auto split: nat.split)
  thus ?thesis by (simp add: eval_cexpr_def cexpr_sem_cexpr_comp)
qed

primrec cexpr_subst_val_aux :: "nat \<Rightarrow> cexpr \<Rightarrow> val \<Rightarrow> cexpr" where
  "cexpr_subst_val_aux _ (CVal v) _ = CVal v"
| "cexpr_subst_val_aux x (CVar y) v = insert_var x CVar (CVal v) y"
| "cexpr_subst_val_aux x (IF\<^sub>c b THEN e1 ELSE e2) v =
    (IF\<^sub>c cexpr_subst_val_aux x b v THEN cexpr_subst_val_aux x e1 v ELSE cexpr_subst_val_aux x e2 v)"
| "cexpr_subst_val_aux x (oper $$\<^sub>c e) v = oper $$\<^sub>c (cexpr_subst_val_aux x e v)"
| "cexpr_subst_val_aux x <e1, e2>\<^sub>c v = <cexpr_subst_val_aux x e1 v, cexpr_subst_val_aux x e2 v>\<^sub>c"
| "cexpr_subst_val_aux x (\<integral>\<^sub>c e \<partial>t) v = \<integral>\<^sub>c cexpr_subst_val_aux (Suc x) e v \<partial>t"

lemma cexpr_subst_val_aux_eq_cexpr_subst:
    "cexpr_subst_val_aux x e v = cexpr_subst x (CVal v) e"
  by (induction e arbitrary: x) simp_all

definition cexpr_subst_val :: "cexpr \<Rightarrow> val \<Rightarrow> cexpr" where
  "cexpr_subst_val e v \<equiv> cexpr_subst_val_aux 0 e v"

lemma cexpr_sem_cexpr_subst_val[simp]:
    "cexpr_sem \<sigma> (cexpr_subst_val e v) = cexpr_sem (case_nat v \<sigma>) e"
  by (simp add: cexpr_subst_val_def cexpr_subst_val_aux_eq_cexpr_subst cexpr_sem_cexpr_subst)

lemma cexpr_typing_subst_val[intro]:
    "case_nat t \<Gamma> \<turnstile>\<^sub>c e : t' \<Longrightarrow> val_type v = t \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>c cexpr_subst_val e v : t'"
  by (auto simp: cexpr_subst_val_def cexpr_subst_val_aux_eq_cexpr_subst intro!: cet_val')

lemma free_vars_cexpr_subst_val_aux:
    "free_vars (cexpr_subst_val_aux x e v) = (\<lambda>y. if y \<ge> x then Suc y else y) -` free_vars e"
  by (induction e arbitrary: x) (auto simp: insert_var_def split: if_split_asm)

lemma free_vars_cexpr_subst_val[simp]:
    "free_vars (cexpr_subst_val e v) = Suc -` free_vars e"
  by (simp add: cexpr_subst_val_def free_vars_cexpr_subst_val_aux)


subsection \<open>Nonnegative expressions\<close>

definition "nonneg_cexpr V \<Gamma> e \<equiv>
    \<forall>\<sigma> \<in> space (state_measure V \<Gamma>). extract_real (cexpr_sem \<sigma> e) \<ge> 0"

lemma nonneg_cexprI:
    "(\<And>\<sigma>. \<sigma> \<in> space (state_measure V \<Gamma>) \<Longrightarrow> extract_real (cexpr_sem \<sigma> e) \<ge> 0) \<Longrightarrow> nonneg_cexpr V \<Gamma> e"
  unfolding nonneg_cexpr_def by simp

lemma nonneg_cexprD:
    "nonneg_cexpr V \<Gamma> e \<Longrightarrow> \<sigma> \<in> space (state_measure V \<Gamma>) \<Longrightarrow> extract_real (cexpr_sem \<sigma> e) \<ge> 0"
  unfolding nonneg_cexpr_def by simp

lemma nonneg_cexpr_map_vars:
  assumes "nonneg_cexpr (f -` V) (\<Gamma> \<circ> f) e"
  shows "nonneg_cexpr V \<Gamma> (map_vars f e)"
  by (intro nonneg_cexprI, subst cexpr_sem_map_vars, intro nonneg_cexprD[OF assms])
     (auto simp: state_measure_def space_PiM)

lemma nonneg_cexpr_subset:
  assumes "nonneg_cexpr V \<Gamma> e" "V \<subseteq> V'" "free_vars e \<subseteq> V"
  shows "nonneg_cexpr V' \<Gamma> e"
proof (intro nonneg_cexprI)
  fix \<sigma> assume "\<sigma> \<in> space (state_measure V' \<Gamma>)"
  with assms(2) have "restrict \<sigma> V \<in> space (state_measure V \<Gamma>)"
    by (auto simp: state_measure_def space_PiM restrict_def)
  from nonneg_cexprD[OF assms(1) this] have "extract_real (cexpr_sem (restrict \<sigma> V) e) \<ge> 0" .
  also have "cexpr_sem (restrict \<sigma> V) e = cexpr_sem \<sigma> e" using assms(3)
    by (intro cexpr_sem_eq_on_vars) auto
  finally show "extract_real (cexpr_sem \<sigma> e) \<ge> 0" .
qed

lemma nonneg_cexpr_Mult:
  assumes "\<Gamma> \<turnstile>\<^sub>c e1 : REAL" "\<Gamma> \<turnstile>\<^sub>c e2 : REAL"
  assumes "free_vars e1 \<subseteq> V" "free_vars e2 \<subseteq> V"
  assumes N1: "nonneg_cexpr V \<Gamma> e1" and N2: "nonneg_cexpr V \<Gamma> e2"
  shows "nonneg_cexpr V \<Gamma> (e1 *\<^sub>c e2)"
proof (rule nonneg_cexprI)
  fix \<sigma> assume \<sigma>: "\<sigma> \<in> space (state_measure V \<Gamma>)"
  hence "extract_real (cexpr_sem \<sigma> (e1 *\<^sub>c e2)) = extract_real (cexpr_sem \<sigma> e1) * extract_real (cexpr_sem \<sigma> e2)"
    using assms by (subst cexpr_sem_Mult[of \<Gamma> _ _ _ V]) simp_all
  also have "... \<ge> 0" using \<sigma> N1 N2 by (intro mult_nonneg_nonneg nonneg_cexprD)
  finally show "extract_real (cexpr_sem \<sigma> (e1 *\<^sub>c e2)) \<ge> 0" .
qed

lemma nonneg_indicator:
  assumes "\<Gamma> \<turnstile>\<^sub>c e : BOOL" "free_vars e \<subseteq> V"
  shows "nonneg_cexpr V \<Gamma> (\<langle>e\<rangle>\<^sub>c)"
proof (intro nonneg_cexprI)
  fix \<rho> assume "\<rho> \<in> space (state_measure V \<Gamma>)"
  with assms have "val_type (cexpr_sem \<rho> e) = BOOL" by (rule val_type_cexpr_sem)
  thus "extract_real (cexpr_sem \<rho> (\<langle>e\<rangle>\<^sub>c)) \<ge> 0"
    by (auto simp: extract_real_def bool_to_real_def split: val.split)
qed

lemma nonneg_cexpr_comp_aux:
  assumes nonneg: "nonneg_cexpr V (\<Gamma>(x := t1)) e"  and x:"x \<in> V"
  assumes t2: "\<Gamma>(x:=t1) \<turnstile>\<^sub>c e : t2" and t1: "\<Gamma> \<turnstile>\<^sub>c f : t1" and vars: "free_vars f \<subseteq> V"
  shows "nonneg_cexpr V \<Gamma> (cexpr_comp_aux x f e)"
proof (intro nonneg_cexprI)
  fix \<sigma> assume \<sigma>: "\<sigma> \<in> space (state_measure V \<Gamma>)"
  have "extract_real (cexpr_sem \<sigma> (cexpr_comp_aux x f e)) =
            extract_real (cexpr_sem (\<sigma>(x := cexpr_sem \<sigma> f)) e)"
    by (simp add: cexpr_sem_cexpr_comp_aux)
  also from val_type_cexpr_sem[OF t1 vars \<sigma>] have "cexpr_sem \<sigma> f \<in> type_universe t1" by auto
  with \<sigma> x have "\<sigma>(x := cexpr_sem \<sigma> f) \<in> space (state_measure V (\<Gamma>(x := t1)))"
    by (auto simp: state_measure_def space_PiM shift_var_set_def split: if_split_asm)
  hence "extract_real (cexpr_sem (\<sigma>(x := cexpr_sem \<sigma> f)) e) \<ge> 0"
    by(intro nonneg_cexprD[OF assms(1)])
  finally show "extract_real (cexpr_sem \<sigma> (cexpr_comp_aux x f e)) \<ge> 0" .
qed

lemma nonneg_cexpr_comp:
  assumes "nonneg_cexpr (shift_var_set V) (case_nat t2 \<Gamma>) e"
  assumes "case_nat t1 \<Gamma> \<turnstile>\<^sub>c f : t2" "free_vars f \<subseteq> shift_var_set V"
  shows "nonneg_cexpr (shift_var_set V) (case_nat t1 \<Gamma>) (e \<circ>\<^sub>c f)"
proof (intro nonneg_cexprI)
  fix \<sigma> assume \<sigma>: "\<sigma> \<in> space (state_measure (shift_var_set V) (case_nat t1 \<Gamma>))"
  have "extract_real (cexpr_sem \<sigma> (e \<circ>\<^sub>c f)) = extract_real (cexpr_sem (\<sigma>(0 := cexpr_sem \<sigma> f)) e)"
    by (simp add: cexpr_sem_cexpr_comp)
  also from val_type_cexpr_sem[OF assms(2,3) \<sigma>] have "cexpr_sem \<sigma> f \<in> type_universe t2" by auto
  with \<sigma> have "\<sigma>(0 := cexpr_sem \<sigma> f) \<in> space (state_measure (shift_var_set V) (case_nat t2 \<Gamma>))"
    by (auto simp: state_measure_def space_PiM shift_var_set_def split: if_split_asm)
  hence "extract_real (cexpr_sem (\<sigma>(0 := cexpr_sem \<sigma> f)) e) \<ge> 0"
    by(intro nonneg_cexprD[OF assms(1)])
  finally show "extract_real (cexpr_sem \<sigma> (e \<circ>\<^sub>c f)) \<ge> 0" .
qed

lemma nonneg_cexpr_subst_val:
  assumes "nonneg_cexpr (shift_var_set V) (case_nat t \<Gamma>) e" "val_type v = t"
  shows "nonneg_cexpr V \<Gamma> (cexpr_subst_val e v)"
proof (intro nonneg_cexprI)
  fix \<sigma> assume \<sigma>: "\<sigma> \<in> space (state_measure V \<Gamma>)"
  moreover from assms(2) have "v \<in> type_universe t" by auto
  ultimately show "extract_real (cexpr_sem \<sigma> (cexpr_subst_val e v)) \<ge> 0"
    by (auto intro!: nonneg_cexprD[OF assms(1)])
qed

lemma nonneg_cexpr_int:
  assumes "nonneg_cexpr (shift_var_set V) (case_nat t \<Gamma>) e"
  shows "nonneg_cexpr V \<Gamma> (\<integral>\<^sub>c e \<partial>t)"
proof (intro nonneg_cexprI)
  fix \<sigma> assume \<sigma>: "\<sigma> \<in> space (state_measure V \<Gamma>)"
  have "extract_real (cexpr_sem \<sigma> (\<integral>\<^sub>c e \<partial>t)) = \<integral>x. extract_real (cexpr_sem (case_nat x \<sigma>) e) \<partial>stock_measure t"
    by (simp add: extract_real_def)
  also from \<sigma> have "... \<ge> 0"
    by (intro integral_nonneg_AE AE_I2 nonneg_cexprD[OF assms]) auto
  finally show "extract_real (cexpr_sem \<sigma> (\<integral>\<^sub>c e \<partial>t)) \<ge> 0" .
qed


text \<open>Subprobability density expressions\<close>

definition "subprob_cexpr V V' \<Gamma> e \<equiv>
    \<forall>\<rho> \<in> space (state_measure V' \<Gamma>).
      (\<integral>\<^sup>+\<sigma>. extract_real (cexpr_sem (merge V V' (\<sigma>, \<rho>)) e) \<partial>state_measure V \<Gamma>) \<le> 1"

lemma subprob_cexprI:
  assumes "\<And>\<rho>. \<rho> \<in> space (state_measure V' \<Gamma>) \<Longrightarrow>
                 (\<integral>\<^sup>+\<sigma>. extract_real (cexpr_sem (merge V V' (\<sigma>, \<rho>)) e) \<partial>state_measure V \<Gamma>) \<le> 1"
  shows "subprob_cexpr V V' \<Gamma> e"
  using assms unfolding subprob_cexpr_def by simp

lemma subprob_cexprD:
  assumes "subprob_cexpr V V' \<Gamma> e"
  shows "\<And>\<rho>. \<rho> \<in> space (state_measure V' \<Gamma>) \<Longrightarrow>
               (\<integral>\<^sup>+\<sigma>. extract_real (cexpr_sem (merge V V' (\<sigma>, \<rho>)) e) \<partial>state_measure V \<Gamma>) \<le> 1"
  using assms unfolding subprob_cexpr_def by simp

lemma subprob_indicator:
  assumes subprob: "subprob_cexpr V V' \<Gamma> e1" and nonneg: "nonneg_cexpr (V \<union> V') \<Gamma> e1"
  assumes t1: "\<Gamma> \<turnstile>\<^sub>c e1 : REAL" and t2: "\<Gamma> \<turnstile>\<^sub>c e2 : BOOL"
  assumes vars1: "free_vars e1 \<subseteq> V \<union> V'" and vars2: "free_vars e2 \<subseteq> V \<union> V'"
  shows "subprob_cexpr V V' \<Gamma> (e1 *\<^sub>c \<langle>e2\<rangle>\<^sub>c)"
proof (intro subprob_cexprI)
  fix \<rho> assume \<rho>: "\<rho> \<in> space (state_measure V' \<Gamma>)"
  from t2 have t2': "\<Gamma> \<turnstile>\<^sub>c \<langle>e2\<rangle>\<^sub>c : REAL" by (rule cet_op) simp_all
  from vars2 have vars2': "free_vars (\<langle>e2\<rangle>\<^sub>c) \<subseteq> V \<union> V'" by simp
  let ?eval = "\<lambda>\<sigma> e. extract_real (cexpr_sem (merge V V' (\<sigma>, \<rho>)) e)"
  have "(\<integral>\<^sup>+\<sigma>. ?eval \<sigma> (e1 *\<^sub>c \<langle>e2\<rangle>\<^sub>c) \<partial>state_measure V \<Gamma>) =
            (\<integral>\<^sup>+\<sigma>. ?eval \<sigma> e1 * ?eval \<sigma> (\<langle>e2\<rangle>\<^sub>c) \<partial>state_measure V \<Gamma>)"
    by (intro nn_integral_cong)
       (simp only: cexpr_sem_Mult[OF t1 t2' merge_in_state_measure[OF _ \<rho>] vars1 vars2'])
  also {
    fix \<sigma> assume \<sigma>: "\<sigma> \<in> space (state_measure V \<Gamma>)"
    with \<rho> have "val_type (cexpr_sem (merge V V' (\<sigma>,\<rho>)) e2) = BOOL"
      by (intro val_type_cexpr_sem[OF t2 vars2] merge_in_state_measure)
    hence "?eval \<sigma> (\<langle>e2\<rangle>\<^sub>c) \<in> {0,1}"
      by (cases "cexpr_sem (merge V V' (\<sigma>,\<rho>)) e2") (auto simp: extract_real_def bool_to_real_def)
    moreover have "?eval \<sigma> e1 \<ge> 0" using nonneg \<rho> \<sigma>
      by (auto intro!: nonneg_cexprD merge_in_state_measure)
    ultimately have "?eval \<sigma> e1 * ?eval \<sigma> (\<langle>e2\<rangle>\<^sub>c) \<le> ?eval \<sigma> e1"
      by (intro mult_right_le_one_le) auto
  }
  hence "(\<integral>\<^sup>+\<sigma>. ?eval \<sigma> e1 * ?eval \<sigma> (\<langle>e2\<rangle>\<^sub>c) \<partial>state_measure V \<Gamma>) \<le>
             (\<integral>\<^sup>+\<sigma>. ?eval \<sigma> e1 \<partial>state_measure V \<Gamma>)"
    by (intro nn_integral_mono) (simp add: ennreal_leI)
  also from subprob and \<rho> have "... \<le> 1" by (rule subprob_cexprD)
  finally show "(\<integral>\<^sup>+\<sigma>. ?eval \<sigma> (e1 *\<^sub>c \<langle>e2\<rangle>\<^sub>c) \<partial>state_measure V \<Gamma>)  \<le> 1" .
qed

lemma measurable_cexpr_sem':
  assumes \<rho>: "\<rho> \<in> space (state_measure V' \<Gamma>)"
  assumes e: "\<Gamma> \<turnstile>\<^sub>c e : REAL" "free_vars e \<subseteq> V \<union> V'"
  shows "(\<lambda>\<sigma>. extract_real (cexpr_sem (merge V V' (\<sigma>, \<rho>)) e))
            \<in> borel_measurable (state_measure V \<Gamma>)"
  apply (rule measurable_compose[OF _ measurable_extract_real])
  apply (rule measurable_compose[OF _ measurable_cexpr_sem[OF e]])
  apply (insert \<rho>, unfold state_measure_def, rule measurable_compose[OF _ measurable_merge], simp)
  done

lemma measurable_fun_upd_state_measure[measurable]:
  assumes "v \<notin> V"
  shows "(\<lambda>(x,y). y(v := x)) \<in> measurable (stock_measure (\<Gamma> v) \<Otimes>\<^sub>M state_measure V \<Gamma>)
                                          (state_measure (insert v V) \<Gamma>)"
  unfolding state_measure_def by simp


lemma integrable_cexpr_projection:
  assumes fin: "finite V"
  assumes disjoint: "V \<inter> V' = {}" "v \<notin> V" "v \<notin> V'"
  assumes \<rho>: "\<rho> \<in> space (state_measure V' \<Gamma>)"
  assumes e: "\<Gamma> \<turnstile>\<^sub>c e : REAL" "free_vars e \<subseteq> insert v V \<union> V'"
  assumes int: "integrable (state_measure (insert v V) \<Gamma>)
                    (\<lambda>\<sigma>. extract_real (cexpr_sem (merge (insert v V) V' (\<sigma>, \<rho>)) e))"
                (is "integrable _ ?f'")
  shows "AE x in stock_measure (\<Gamma> v).
           integrable (state_measure V \<Gamma>)
               (\<lambda>\<sigma>. extract_real (cexpr_sem (merge V (insert v V') (\<sigma>, \<rho>(v := x))) e))"
    (is "AE x in ?N. integrable ?M (?f x)")
proof (unfold real_integrable_def, intro AE_conjI)
  show "AE x in ?N. ?f x \<in> borel_measurable ?M" using \<rho> e disjoint
    by (intro AE_I2 measurable_cexpr_sem')
       (auto simp: state_measure_def space_PiM dest: PiE_mem split: if_split_asm)

  let ?f'' = "\<lambda>x \<sigma>. extract_real (cexpr_sem (merge (insert v V) V' (\<sigma>(v := x), \<rho>)) e)"
  {
    fix x \<sigma> assume "x \<in> space ?N" "\<sigma> \<in> space ?M"
    hence "merge (insert v V) V' (\<sigma>(v := x), \<rho>) = merge V (insert v V') (\<sigma>, \<rho>(v := x))"
      using disjoint by (intro ext) (simp add: merge_def split: if_split_asm)
    hence "?f'' x \<sigma> = ?f x \<sigma>" by simp
  } note f''_eq_f = this

  interpret product_sigma_finite "(\<lambda>v. stock_measure (\<Gamma> v))"
    by (simp add: product_sigma_finite_def)
  interpret sigma_finite_measure "state_measure V \<Gamma>"
    by (rule sigma_finite_state_measure[OF fin])

  from int have "(\<integral>\<^sup>+\<sigma>. ennreal (?f' \<sigma>) \<partial>state_measure (insert v V) \<Gamma>) \<noteq> \<infinity>"
    by (simp add: real_integrable_def)
  also have "(\<integral>\<^sup>+\<sigma>. ennreal (?f' \<sigma>) \<partial>state_measure (insert v V) \<Gamma>) =
                 \<integral>\<^sup>+x. \<integral>\<^sup>+\<sigma>. ennreal (?f'' x \<sigma>) \<partial>?M \<partial>?N" (is "_ = ?I")
    using fin disjoint e \<rho>
    by (unfold state_measure_def, subst product_nn_integral_insert_rev)
       (auto intro!: measurable_compose[OF _ measurable_ennreal] measurable_cexpr_sem'[unfolded state_measure_def])
  finally have "AE x in ?N. (\<integral>\<^sup>+\<sigma>. ennreal (?f'' x \<sigma>) \<partial>?M) \<noteq> \<infinity>" (is ?P) using e disjoint
    by (intro nn_integral_PInf_AE)
       (auto simp: measurable_split_conv intro!: borel_measurable_nn_integral measurable_compose[OF _ measurable_ennreal]
                   measurable_compose[OF _ measurable_cexpr_sem'[OF \<rho>]])
  moreover have "\<And>x. x \<in> space ?N \<Longrightarrow> (\<integral>\<^sup>+\<sigma>. ennreal (?f'' x \<sigma>) \<partial>?M) = (\<integral>\<^sup>+\<sigma>. ennreal (?f x \<sigma>) \<partial>?M)"
    by (intro nn_integral_cong) (simp add: f''_eq_f)
  hence "?P \<longleftrightarrow> (AE x in ?N. (\<integral>\<^sup>+\<sigma>. ennreal (?f x \<sigma>) \<partial>?M) \<noteq> \<infinity>)" by (intro AE_cong) simp
  ultimately show "AE x in ?N. (\<integral>\<^sup>+\<sigma>. ennreal (?f x \<sigma>) \<partial>?M) \<noteq> \<infinity>" by simp

  from int have "(\<integral>\<^sup>+\<sigma>. ennreal (-?f' \<sigma>) \<partial>state_measure (insert v V) \<Gamma>) \<noteq> \<infinity>"
    by (simp add: real_integrable_def)
  also have "(\<integral>\<^sup>+\<sigma>. ennreal (-?f' \<sigma>) \<partial>state_measure (insert v V) \<Gamma>) =
                 \<integral>\<^sup>+x. \<integral>\<^sup>+\<sigma>. ennreal (-?f'' x \<sigma>) \<partial>?M \<partial>?N" (is "_ = ?I")
    using fin disjoint e \<rho>
    by (unfold state_measure_def, subst product_nn_integral_insert_rev)
       (auto intro!: measurable_compose[OF _ measurable_ennreal] borel_measurable_uminus
                     measurable_cexpr_sem'[unfolded state_measure_def])
  finally have "AE x in ?N. (\<integral>\<^sup>+\<sigma>. ennreal (-?f'' x \<sigma>) \<partial>?M) \<noteq> \<infinity>" (is ?P) using e disjoint
    by (intro nn_integral_PInf_AE)
       (auto simp: measurable_split_conv intro!: borel_measurable_nn_integral measurable_compose[OF _ measurable_ennreal]
                   measurable_compose[OF _ measurable_cexpr_sem'[OF \<rho>]] borel_measurable_uminus)
  moreover have "\<And>x. x \<in> space ?N \<Longrightarrow> (\<integral>\<^sup>+\<sigma>. ennreal (-?f'' x \<sigma>) \<partial>?M) = (\<integral>\<^sup>+\<sigma>. ennreal (-?f x \<sigma>) \<partial>?M)"
    by (intro nn_integral_cong) (simp add: f''_eq_f)
  hence "?P \<longleftrightarrow> (AE x in ?N. (\<integral>\<^sup>+\<sigma>. ennreal (-?f x \<sigma>) \<partial>?M) \<noteq> \<infinity>)" by (intro AE_cong) simp
  ultimately show "AE x in ?N. (\<integral>\<^sup>+\<sigma>. ennreal (-?f x \<sigma>) \<partial>?M) \<noteq> \<infinity>" by simp
qed


definition cdens_ctxt_invar :: "vname list \<Rightarrow> vname list \<Rightarrow> tyenv \<Rightarrow> cexpr \<Rightarrow> bool" where
  "cdens_ctxt_invar vs vs' \<Gamma> \<delta> \<equiv>
       distinct (vs @ vs') \<and>
       free_vars \<delta> \<subseteq> set (vs @ vs') \<and>
       \<Gamma> \<turnstile>\<^sub>c \<delta> : REAL \<and>
       nonneg_cexpr (set vs \<union> set vs') \<Gamma> \<delta> \<and>
       subprob_cexpr (set vs) (set vs') \<Gamma> \<delta>"

lemma cdens_ctxt_invarI:
  "\<lbrakk>distinct (vs @ vs'); free_vars \<delta> \<subseteq> set (vs @ vs'); \<Gamma> \<turnstile>\<^sub>c \<delta> : REAL;
    nonneg_cexpr (set vs \<union> set vs') \<Gamma> \<delta>;
    subprob_cexpr (set vs) (set vs') \<Gamma> \<delta> \<rbrakk> \<Longrightarrow>
      cdens_ctxt_invar vs vs' \<Gamma> \<delta>"
  by (simp add: cdens_ctxt_invar_def)

lemma cdens_ctxt_invarD:
  assumes "cdens_ctxt_invar vs vs' \<Gamma> \<delta>"
  shows "distinct (vs @ vs')" "free_vars \<delta> \<subseteq> set (vs @ vs')" "\<Gamma> \<turnstile>\<^sub>c \<delta> : REAL"
        "nonneg_cexpr (set vs \<union> set vs') \<Gamma> \<delta>" "subprob_cexpr (set vs) (set vs') \<Gamma> \<delta>"
  using assms by (simp_all add: cdens_ctxt_invar_def)

lemma cdens_ctxt_invar_empty:
  assumes "cdens_ctxt_invar vs vs' \<Gamma> \<delta>"
  shows "cdens_ctxt_invar [] (vs @ vs') \<Gamma> (CReal 1)"
  using cdens_ctxt_invarD[OF assms]
  by (intro cdens_ctxt_invarI)
     (auto simp: cexpr_type_Some_iff[symmetric] extract_real_def state_measure_def PiM_empty
           intro!: nonneg_cexprI subprob_cexprI)

lemma cdens_ctxt_invar_imp_integrable:
  assumes "cdens_ctxt_invar vs vs' \<Gamma> \<delta>" and \<rho>: "\<rho> \<in> space (state_measure (set vs') \<Gamma>)"
  shows "integrable (state_measure (set vs) \<Gamma>)
             (\<lambda>\<sigma>. extract_real (cexpr_sem (merge (set vs) (set vs') (\<sigma>, \<rho>)) \<delta>))" (is "integrable ?M ?f")
  unfolding integrable_iff_bounded
proof (intro conjI)
  note invar = cdens_ctxt_invarD[OF assms(1)]
  show "?f \<in> borel_measurable ?M"
    apply (rule measurable_compose[OF _ measurable_extract_real])
    apply (rule measurable_compose[OF _ measurable_cexpr_sem[OF invar(3,2)]])
    apply (simp only: state_measure_def set_append, rule measurable_compose[OF _ measurable_merge])
    apply (rule measurable_Pair, simp, insert assms(2), simp add: state_measure_def)
    done

  have nonneg: "\<And>\<sigma>. \<sigma> \<in> space ?M \<Longrightarrow> ?f \<sigma> \<ge> 0"
    using \<open>nonneg_cexpr (set vs \<union> set vs') \<Gamma> \<delta>\<close>
    by (rule nonneg_cexprD, intro merge_in_state_measure[OF _ \<rho>])
  with \<open>subprob_cexpr (set vs) (set vs') \<Gamma> \<delta>\<close> and \<rho>
  show "(\<integral>\<^sup>+\<sigma>. ennreal (norm (?f \<sigma>)) \<partial>?M) < \<infinity>" unfolding subprob_cexpr_def
    by (auto simp: less_top[symmetric] top_unique cong: nn_integral_cong)
qed


subsection \<open>Randomfree expressions\<close>

text \<open>
  Translates an expression with no occurrences of Random or Fail into an
  equivalent target language expression.
\<close>
primrec expr_rf_to_cexpr :: "expr \<Rightarrow> cexpr" where
  "expr_rf_to_cexpr (Val v) = CVal v"
| "expr_rf_to_cexpr (Var x) = CVar x"
| "expr_rf_to_cexpr <e1, e2> = <expr_rf_to_cexpr e1, expr_rf_to_cexpr e2>\<^sub>c"
| "expr_rf_to_cexpr (oper $$ e) = oper $$\<^sub>c (expr_rf_to_cexpr e)"
| "expr_rf_to_cexpr (IF b THEN e1 ELSE e2) =
      (IF\<^sub>c expr_rf_to_cexpr b THEN expr_rf_to_cexpr e1 ELSE expr_rf_to_cexpr e2)"
| "expr_rf_to_cexpr (LET e1 IN e2) =
      cexpr_subst 0 (expr_rf_to_cexpr e1) (expr_rf_to_cexpr e2)"
| "expr_rf_to_cexpr (Random _ _) = undefined"
| "expr_rf_to_cexpr (Fail _) = undefined"

lemma cexpr_sem_expr_rf_to_cexpr:
     "randomfree e \<Longrightarrow> cexpr_sem \<sigma> (expr_rf_to_cexpr e) = expr_sem_rf \<sigma> e"
  by (induction e arbitrary: \<sigma>) (auto simp: cexpr_sem_cexpr_subst)

lemma cexpr_typing_expr_rf_to_cexpr[intro]:
    assumes "\<Gamma> \<turnstile> e : t" "randomfree e"
    shows "\<Gamma> \<turnstile>\<^sub>c expr_rf_to_cexpr e : t"
  using assms by (induction rule: expr_typing.induct) (auto intro!: cexpr_typing.intros)

lemma free_vars_expr_rf_to_cexpr:
  "randomfree e \<Longrightarrow> free_vars (expr_rf_to_cexpr e) \<subseteq> free_vars e"
proof (induction e)
  case (LetVar e1 e2)
  thus ?case
    by (simp only: free_vars_cexpr.simps expr_rf_to_cexpr.simps,
        intro order.trans[OF free_vars_cexpr_subst]) auto
qed auto

subsection \<open>Builtin density expressions\<close>

primrec dist_dens_cexpr :: "pdf_dist \<Rightarrow> cexpr \<Rightarrow> cexpr \<Rightarrow> cexpr" where
  "dist_dens_cexpr Bernoulli p x = (IF\<^sub>c CReal 0 \<le>\<^sub>c p \<and>\<^sub>c p \<le>\<^sub>c CReal 1 THEN
                                       IF\<^sub>c x THEN p ELSE CReal 1 -\<^sub>c p
                                    ELSE CReal 0)"
| "dist_dens_cexpr UniformInt p x = (IF\<^sub>c fst\<^sub>c p \<le>\<^sub>c snd\<^sub>c p \<and>\<^sub>c fst\<^sub>c p \<le>\<^sub>c x \<and>\<^sub>c x \<le>\<^sub>c snd\<^sub>c p THEN
                                         inverse\<^sub>c (\<langle>snd\<^sub>c p -\<^sub>c fst\<^sub>c p +\<^sub>c CInt 1\<rangle>\<^sub>c) ELSE CReal 0)"
| "dist_dens_cexpr UniformReal p x = (IF\<^sub>c fst\<^sub>c p <\<^sub>c snd\<^sub>c p \<and>\<^sub>c fst\<^sub>c p \<le>\<^sub>c x \<and>\<^sub>c x \<le>\<^sub>c snd\<^sub>c p THEN
                                         inverse\<^sub>c (snd\<^sub>c p -\<^sub>c fst\<^sub>c p) ELSE CReal 0)"
| "dist_dens_cexpr Gaussian p x = (IF\<^sub>c CReal 0 <\<^sub>c snd\<^sub>c p THEN
                                     exp\<^sub>c (-\<^sub>c((x -\<^sub>c fst\<^sub>c p)^\<^sub>cCInt 2 /\<^sub>c (CReal 2 *\<^sub>c snd\<^sub>c p^\<^sub>cCInt 2))) /\<^sub>c
                                         sqrt\<^sub>c (CReal 2 *\<^sub>c \<pi>\<^sub>c *\<^sub>c snd\<^sub>c p ^\<^sub>c CInt 2) ELSE CReal 0)"
| "dist_dens_cexpr Poisson p x = (IF\<^sub>c CReal 0 <\<^sub>c p \<and>\<^sub>c CInt 0 \<le>\<^sub>c x THEN
                                    p ^\<^sub>c x /\<^sub>c \<langle>fact\<^sub>c x\<rangle>\<^sub>c *\<^sub>c exp\<^sub>c (-\<^sub>c p) ELSE CReal 0)"

lemma free_vars_dist_dens_cexpr:
    "free_vars (dist_dens_cexpr dst e1 e2) \<subseteq> free_vars e1 \<union> free_vars e2"
  by (subst dist_dens_cexpr_def, cases dst) simp_all

lemma cexpr_typing_dist_dens_cexpr:
    assumes "\<Gamma> \<turnstile>\<^sub>c e1 : dist_param_type dst" "\<Gamma> \<turnstile>\<^sub>c e2 : dist_result_type dst"
    shows "\<Gamma> \<turnstile>\<^sub>c dist_dens_cexpr dst e1 e2 : REAL"
  using assms
  apply (subst dist_dens_cexpr_def, cases dst)
  (* Bernoulli *)
  apply (simp, intro cet_op_intros cet_if cet_val' cet_var' cet_eq, simp_all) []
  (* Uniform int *)
  apply (simp, intro cet_if cet_and cet_or cet_less_int cet_eq)
  apply (erule cet_fst cet_snd | simp)+
  apply (rule cet_inverse, rule cet_op[where t = INTEG], intro cet_add_int cet_minus_int)
  apply (simp_all add: cet_val' cet_fst cet_snd) [5]
  (* Uniform real *)
  apply (simp, intro cet_if cet_op_intros cet_eq cet_fst cet_snd, simp_all add: cet_val') []
  (* Poisson *)
  apply (simp, intro cet_if cet_and, rule cet_less_real, simp add: cet_val', simp)
  apply (rule cet_less_eq_int, simp add: cet_val', simp)
  apply (intro cet_mult_real cet_pow_real cet_inverse cet_cast_real_int cet_exp cet_minus_real
               cet_op[where oper = Fact and t = INTEG] cet_var', simp_all add: cet_val') [2]
  (* Gaussian *)
  apply (simp, intro cet_if cet_op_intros cet_val', simp_all add: cet_fst cet_snd)
  done


lemma val_type_eq_BOOL: "val_type x = BOOL \<longleftrightarrow> x \<in> BoolVal`UNIV"
  by (cases x) auto

lemma val_type_eq_INTEG: "val_type x = INTEG \<longleftrightarrow> x \<in> IntVal`UNIV"
  by (cases x) auto

lemma val_type_eq_PRODUCT: "val_type x = PRODUCT t1 t2 \<longleftrightarrow>
  (\<exists>a b. val_type a = t1 \<and> val_type b = t2 \<and> x = <| a, b |>)"
  by (cases x) auto

lemma cexpr_sem_dist_dens_cexpr_nonneg:
  assumes "\<Gamma> \<turnstile>\<^sub>c e1 : dist_param_type dst" "\<Gamma> \<turnstile>\<^sub>c e2 : dist_result_type dst"
  assumes "free_vars e1 \<subseteq> V" "free_vars e2 \<subseteq> V"
  assumes "\<sigma> \<in> space (state_measure V \<Gamma>)"
  shows "ennreal (extract_real (cexpr_sem \<sigma> (dist_dens_cexpr dst e1 e2))) =
           dist_dens dst (cexpr_sem \<sigma> e1) (cexpr_sem \<sigma> e2) \<and>
           0 \<le> extract_real (cexpr_sem \<sigma> (dist_dens_cexpr dst e1 e2))"
proof-
  from val_type_cexpr_sem[OF assms(1,3,5)] and val_type_cexpr_sem[OF assms(2,4,5)]
    have "cexpr_sem \<sigma> e1 \<in> space (stock_measure (dist_param_type dst))" and
         "cexpr_sem \<sigma> e2 \<in> space (stock_measure (dist_result_type dst))"
    by (auto simp: type_universe_def simp del: type_universe_type)
  thus ?thesis
    by (subst dist_dens_cexpr_def, cases dst)
       (auto simp:
            lift_Comp_def lift_RealVal_def lift_RealIntVal_def lift_RealIntVal2_def
            bernoulli_density_def val_type_eq_REAL val_type_eq_BOOL val_type_eq_PRODUCT val_type_eq_INTEG
            uniform_int_density_def uniform_real_density_def
            lift_IntVal_def poisson_density'_def one_ennreal_def
            field_simps gaussian_density_def)
qed

lemma cexpr_sem_dist_dens_cexpr:
  assumes "\<Gamma> \<turnstile>\<^sub>c e1 : dist_param_type dst" "\<Gamma> \<turnstile>\<^sub>c e2 : dist_result_type dst"
  assumes "free_vars e1 \<subseteq> V" "free_vars e2 \<subseteq> V"
  assumes "\<sigma> \<in> space (state_measure V \<Gamma>)"
  shows "ennreal (extract_real (cexpr_sem \<sigma> (dist_dens_cexpr dst e1 e2))) =
           dist_dens dst (cexpr_sem \<sigma> e1) (cexpr_sem \<sigma> e2)"
  using cexpr_sem_dist_dens_cexpr_nonneg[OF assms] by simp

lemma nonneg_dist_dens_cexpr:
  assumes "\<Gamma> \<turnstile>\<^sub>c e1 : dist_param_type dst" "\<Gamma> \<turnstile>\<^sub>c e2 : dist_result_type dst"
  assumes "free_vars e1 \<subseteq> V" "free_vars e2 \<subseteq> V"
  shows "nonneg_cexpr V \<Gamma> (dist_dens_cexpr dst e1 e2)"
proof (intro nonneg_cexprI)
  fix \<sigma> assume \<rho>: "\<sigma> \<in> space (state_measure V \<Gamma>)"
  from cexpr_sem_dist_dens_cexpr_nonneg[OF assms this]
  show "0 \<le> extract_real (cexpr_sem \<sigma> (dist_dens_cexpr dst e1 e2))"
    by simp
qed

subsection \<open>Integral expressions\<close>

definition integrate_var :: "tyenv \<Rightarrow> vname \<Rightarrow> cexpr \<Rightarrow> cexpr" where
  "integrate_var \<Gamma> v e = \<integral>\<^sub>c map_vars (\<lambda>w. if v = w then 0 else Suc w) e \<partial>(\<Gamma> v)"

definition integrate_vars :: "tyenv \<Rightarrow> vname list \<Rightarrow> cexpr \<Rightarrow> cexpr" where
  "integrate_vars \<Gamma> = foldr (integrate_var \<Gamma>)"

lemma cexpr_sem_integrate_var:
  "cexpr_sem \<sigma> (integrate_var \<Gamma> v e) =
    RealVal (\<integral>x. extract_real (cexpr_sem (\<sigma>(v := x)) e) \<partial>stock_measure (\<Gamma> v))"
proof-
  let ?f = "(\<lambda>w. if v = w then 0 else Suc w)"
  have "cexpr_sem \<sigma> (integrate_var \<Gamma> v e) =
          RealVal (\<integral>x. extract_real (cexpr_sem (case_nat x \<sigma> \<circ> ?f) e) \<partial>stock_measure (\<Gamma> v))"
    by (simp add: extract_real_def integrate_var_def cexpr_sem_map_vars)
  also have "(\<lambda>x. case_nat x \<sigma> \<circ> ?f) = (\<lambda>x. \<sigma>(v := x))"
    by (intro ext) (simp add: o_def split: if_split)
  finally show ?thesis .
qed

lemma cexpr_sem_integrate_var':
  "extract_real (cexpr_sem \<sigma> (integrate_var \<Gamma> v e)) =
      (\<integral>x. extract_real (cexpr_sem (\<sigma>(v := x)) e) \<partial>stock_measure (\<Gamma> v))"
  by (subst cexpr_sem_integrate_var, simp add: extract_real_def)

lemma cexpr_typing_integrate_var[simp]:
    "\<Gamma> \<turnstile>\<^sub>c e : REAL \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>c integrate_var \<Gamma> v e : REAL"
  unfolding integrate_var_def
  by (rule cexpr_typing.intros, rule cexpr_typing_map_vars)
     (erule cexpr_typing_cong', simp split: nat.split)

lemma cexpr_typing_integrate_vars[simp]:
    "\<Gamma> \<turnstile>\<^sub>c e : REAL \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>c integrate_vars \<Gamma> vs e : REAL"
  by (induction vs arbitrary: e)
     (simp_all add: integrate_vars_def)

lemma free_vars_integrate_var[simp]:
    "free_vars (integrate_var \<Gamma> v e) = free_vars e - {v}"
  by (auto simp: integrate_var_def)

lemma free_vars_integrate_vars[simp]:
    "free_vars (integrate_vars \<Gamma> vs e) = free_vars e - set vs"
  by (induction vs arbitrary: e) (auto simp: integrate_vars_def)

lemma (in product_sigma_finite) product_integral_insert':
  fixes f :: "_ \<Rightarrow> real"
  assumes "finite I" "i \<notin> I" "integrable (Pi\<^sub>M (insert i I) M) f"
  shows "integral\<^sup>L (Pi\<^sub>M (insert i I) M) f = LINT y|M i. LINT x|Pi\<^sub>M I M. f (x(i := y))"
proof-
  interpret pair_sigma_finite "M i" "Pi\<^sub>M I M"
    by (simp_all add: sigma_finite assms pair_sigma_finite_def sigma_finite_measures)
  interpret Mi: sigma_finite_measure "M i"
    by (simp add: assms sigma_finite_measures)
  from assms(3) have int: "integrable (M i \<Otimes>\<^sub>M Pi\<^sub>M I M) (\<lambda>(x, y). f (y(i := x)))"
  unfolding real_integrable_def
    apply (elim conjE)
    apply (subst (1 2) nn_integral_snd[symmetric])
    apply ((subst (asm) (1 2) product_nn_integral_insert[OF assms(1,2)],
           auto intro!: measurable_compose[OF _ measurable_ennreal] borel_measurable_uminus) [])+
    done
  from assms have "integral\<^sup>L (Pi\<^sub>M (insert i I) M) f = LINT x|Pi\<^sub>M I M. LINT y|M i. f (x(i := y))"
    by (rule product_integral_insert)
  also from int have "... = LINT y|M i. LINT x|Pi\<^sub>M I M. f (x(i := y))"
    by (rule Fubini_integral)
  finally show ?thesis .
qed


lemma cexpr_sem_integrate_vars:
  assumes \<rho>: "\<rho> \<in> space (state_measure V' \<Gamma>)"
  assumes disjoint: "distinct vs" "set vs \<inter> V' = {}"
  assumes "integrable (state_measure (set vs) \<Gamma>)
               (\<lambda>\<sigma>. extract_real (cexpr_sem (merge (set vs) V' (\<sigma>, \<rho>)) e))"
  assumes e: "\<Gamma> \<turnstile>\<^sub>c e : REAL" "free_vars e \<subseteq> set vs \<union> V'"
  shows "extract_real (cexpr_sem \<rho> (integrate_vars \<Gamma> vs e)) =
           \<integral>\<sigma>. extract_real (cexpr_sem (merge (set vs) V' (\<sigma>, \<rho>)) e) \<partial>state_measure (set vs) \<Gamma>"
using assms
proof (induction vs arbitrary: \<rho> V')
  case Nil
  hence "\<And>v. (if v \<in> V' then \<rho> v else undefined) = \<rho> v"
    by (auto simp: state_measure_def space_PiM)
  thus ?case by (auto simp: integrate_vars_def state_measure_def merge_def PiM_empty)
next
  case (Cons v vs \<rho> V')
  interpret product_sigma_finite "\<lambda>v. stock_measure (\<Gamma> v)"
    by (simp add: product_sigma_finite_def)
  interpret sigma_finite_measure "state_measure (set vs) \<Gamma>"
    by (simp add: sigma_finite_state_measure)
  have \<rho>': "\<And>x. x \<in> type_universe (\<Gamma> v) \<Longrightarrow> \<rho>(v := x) \<in> space (state_measure (insert v V') \<Gamma>)"
    using Cons.prems(1) by (auto simp: state_measure_def space_PiM split: if_split_asm)
  have "extract_real (cexpr_sem \<rho> (integrate_vars \<Gamma> (v # vs) e)) =
          \<integral>x. extract_real (cexpr_sem (\<rho>(v := x)) (integrate_vars \<Gamma> vs e)) \<partial>stock_measure (\<Gamma> v)"
    (is "_ = ?I") by (simp add: integrate_vars_def cexpr_sem_integrate_var extract_real_def)
  also from Cons.prems(4) have int: "integrable (state_measure (insert v (set vs)) \<Gamma>)
      (\<lambda>\<sigma>. extract_real (cexpr_sem (merge (insert v (set vs)) V' (\<sigma>, \<rho>)) e))" by simp
  have "AE x in stock_measure (\<Gamma> v).
                extract_real (cexpr_sem (\<rho>(v := x)) (integrate_vars \<Gamma> vs e)) =
                  \<integral>\<sigma>. extract_real (cexpr_sem (merge (set vs) (insert v V') (\<sigma>, \<rho>(v := x))) e)
                      \<partial>state_measure (set vs) \<Gamma>"
    apply (rule AE_mp[OF _ AE_I2[OF impI]])
    apply (rule integrable_cexpr_projection[OF _ _ _ _ _ _ _ int])
    apply (insert Cons.prems, auto) [7]
    apply (subst Cons.IH, rule \<rho>', insert Cons.prems, auto)
    done
  hence "?I = \<integral>x. \<integral>\<sigma>. extract_real (cexpr_sem (merge (set vs) (insert v V') (\<sigma>, \<rho>(v := x))) e)
                  \<partial>state_measure (set vs) \<Gamma> \<partial>stock_measure (\<Gamma> v)" using Cons.prems
    apply (intro integral_cong_AE)
    apply (rule measurable_compose[OF measurable_Pair_compose_split[OF
                measurable_fun_upd_state_measure[of v V' \<Gamma>]]])
    apply (simp, simp, simp, rule measurable_compose[OF _ measurable_extract_real])
    apply (rule measurable_cexpr_sem, simp, (auto) [])
    apply (rule borel_measurable_lebesgue_integral)
    apply (subst measurable_split_conv)
    apply (rule measurable_compose[OF _ measurable_extract_real])
    apply (rule measurable_compose[OF _ measurable_cexpr_sem[of \<Gamma> _ _  "set vs \<union> insert v V'"]])
    apply (unfold state_measure_def, rule measurable_compose[OF _ measurable_merge])
    apply simp_all
    done
  also have "(\<lambda>x \<sigma>. merge (set vs) (insert v V') (\<sigma>, \<rho>(v := x))) =
                 (\<lambda>x \<sigma>. merge (set (v#vs)) V' (\<sigma>(v := x), \<rho>))"
    using Cons.prems by (intro ext) (auto simp: merge_def split: if_split)
  also have "(\<integral>x. \<integral>\<sigma>. extract_real (cexpr_sem (merge (set (v#vs)) V' (\<sigma>(v := x), \<rho>)) e)
                  \<partial>state_measure (set vs) \<Gamma> \<partial>stock_measure (\<Gamma> v)) =
               \<integral>\<sigma>. extract_real (cexpr_sem (merge (set (v#vs)) V' (\<sigma>, \<rho>)) e)
                  \<partial>state_measure (set (v#vs)) \<Gamma>"
    using Cons.prems unfolding state_measure_def
    by (subst (2) set_simps, subst product_integral_insert') simp_all
  finally show ?case .
qed

lemma cexpr_sem_integrate_vars':
  assumes \<rho>: "\<rho> \<in> space (state_measure V' \<Gamma>)"
  assumes disjoint: "distinct vs" "set vs \<inter> V' = {}"
  assumes nonneg: "nonneg_cexpr (set vs \<union> V') \<Gamma> e"
  assumes "integrable (state_measure (set vs) \<Gamma>)
               (\<lambda>\<sigma>. extract_real (cexpr_sem (merge (set vs) V' (\<sigma>, \<rho>)) e))"
  assumes e: "\<Gamma> \<turnstile>\<^sub>c e : REAL" "free_vars e \<subseteq> set vs \<union> V'"
  shows "ennreal (extract_real (cexpr_sem \<rho> (integrate_vars \<Gamma> vs e))) =
           \<integral>\<^sup>+\<sigma>. extract_real (cexpr_sem (merge (set vs) V' (\<sigma>, \<rho>)) e) \<partial>state_measure (set vs) \<Gamma>"
proof-
  from assms have "extract_real (cexpr_sem \<rho> (integrate_vars \<Gamma> vs e)) =
      \<integral>\<sigma>. extract_real (cexpr_sem (merge (set vs) V' (\<sigma>, \<rho>)) e) \<partial>state_measure (set vs) \<Gamma>"
    by (intro cexpr_sem_integrate_vars)
  also have "ennreal ... =
      \<integral>\<^sup>+\<sigma>. extract_real (cexpr_sem (merge (set vs) V' (\<sigma>, \<rho>)) e) \<partial>state_measure (set vs) \<Gamma>"
    using assms
    by (intro nn_integral_eq_integral[symmetric] AE_I2)
       (auto intro!: nonneg_cexprD merge_in_state_measure)
  finally show ?thesis .
qed

lemma nonneg_cexpr_sem_integrate_vars:
  assumes \<rho>: "\<rho> \<in> space (state_measure V' \<Gamma>)"
  assumes disjoint: "distinct vs" "set vs \<inter> V' = {}"
  assumes nonneg: "nonneg_cexpr (set vs \<union> V') \<Gamma> e"
  assumes e: "\<Gamma> \<turnstile>\<^sub>c e : REAL" "free_vars e \<subseteq> set vs \<union> V'"
  shows "extract_real (cexpr_sem \<rho> (integrate_vars \<Gamma> vs e)) \<ge> 0"
using assms
proof (induction vs arbitrary: \<rho> V')
  case Nil
  hence "\<And>v. (if v \<in> V' then \<rho> v else undefined) = \<rho> v"
    by (auto simp: state_measure_def space_PiM)
  with Nil show ?case
    by (auto simp: integrate_vars_def state_measure_def merge_def PiM_empty nonneg_cexprD)
next
  case (Cons v vs \<rho> V')
  have \<rho>': "\<And>x. x \<in> type_universe (\<Gamma> v) \<Longrightarrow> \<rho>(v := x) \<in> space (state_measure (insert v V') \<Gamma>)"
    using Cons.prems(1) by (auto simp: state_measure_def space_PiM split: if_split_asm)
  have "extract_real (cexpr_sem \<rho> (integrate_vars \<Gamma> (v # vs) e)) =
          \<integral>x. extract_real (cexpr_sem (\<rho>(v := x)) (integrate_vars \<Gamma> vs e)) \<partial>stock_measure (\<Gamma> v)"
    by (simp add: integrate_vars_def cexpr_sem_integrate_var extract_real_def)
  also have "... \<ge> 0"
    by (rule integral_nonneg_AE, rule AE_I2, subst Cons.IH[OF \<rho>']) (insert Cons.prems, auto)
  finally show "extract_real (cexpr_sem \<rho> (integrate_vars \<Gamma> (v # vs) e)) \<ge> 0" .
qed

lemma nonneg_cexpr_sem_integrate_vars':
  "distinct vs \<Longrightarrow> set vs \<inter> V' = {} \<Longrightarrow> nonneg_cexpr (set vs \<union> V') \<Gamma> e \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>c e : REAL \<Longrightarrow>
    free_vars e \<subseteq> set vs \<union> V' \<Longrightarrow> nonneg_cexpr V' \<Gamma> (integrate_vars \<Gamma> vs e)"
  apply (intro nonneg_cexprI allI)
  apply (rule nonneg_cexpr_sem_integrate_vars[where V'=V'])
  apply auto
  done

lemma cexpr_sem_integral_nonneg:
  assumes finite: "(\<integral>\<^sup>+x. extract_real (cexpr_sem (case_nat x \<sigma>) e) \<partial>stock_measure t) < \<infinity>"
  assumes nonneg: "nonneg_cexpr (shift_var_set V) (case_nat t \<Gamma>) e"
  assumes t: "case_nat t \<Gamma> \<turnstile>\<^sub>c e : REAL" and vars: "free_vars e \<subseteq> shift_var_set V"
  assumes \<rho>: "\<sigma> \<in> space (state_measure V \<Gamma>)"
  shows "ennreal (extract_real (cexpr_sem \<sigma> (\<integral>\<^sub>c e \<partial>t))) =
             \<integral>\<^sup>+x. extract_real (cexpr_sem (case_nat x \<sigma>) e) \<partial>stock_measure t"
proof-
  let ?f = "\<lambda>x. extract_real (cexpr_sem (case_nat x \<sigma>) e)"
  have meas: "?f \<in> borel_measurable (stock_measure t)"
    apply (rule measurable_compose[OF _ measurable_extract_real])
    apply (rule measurable_compose[OF measurable_case_nat' measurable_cexpr_sem])
    apply (rule measurable_ident_sets[OF refl], rule measurable_const[OF \<rho>])
    apply (simp_all add: t vars)
    done
  from this and finite and nonneg have int: "integrable (stock_measure t) ?f"
    by (auto intro!: integrableI_nonneg nonneg_cexprD case_nat_in_state_measure[OF _ \<rho>])

  have "extract_real (cexpr_sem \<sigma> (\<integral>\<^sub>c e \<partial>t)) =
          \<integral>x. extract_real (cexpr_sem (case_nat x \<sigma>) e) \<partial>stock_measure t"
    by (simp add: extract_real_def)
  also have "ennreal ... = \<integral>\<^sup>+x. extract_real (cexpr_sem (case_nat x \<sigma>) e) \<partial>stock_measure t"
    by (subst nn_integral_eq_integral[OF int AE_I2])
       (auto intro!: nonneg_cexprD[OF nonneg] case_nat_in_state_measure[OF _ \<rho>])
  finally show ?thesis .
qed

lemma has_parametrized_subprob_density_cexpr_sem_integral:
  assumes dens: "has_parametrized_subprob_density (state_measure V' \<Gamma>) M (stock_measure t)
                   (\<lambda>\<rho> x. \<integral>\<^sup>+y. eval_cexpr f (case_nat x \<rho>) y \<partial>stock_measure t')"
  assumes nonneg: "nonneg_cexpr (shift_var_set (shift_var_set V')) (case_nat t' (case_nat t \<Gamma>)) f"
  assumes tf: "case_nat t' (case_nat t \<Gamma>) \<turnstile>\<^sub>c f : REAL"
  assumes varsf: "free_vars f \<subseteq> shift_var_set (shift_var_set V')"
  assumes \<rho>: "\<rho> \<in> space (state_measure V' \<Gamma>)"
  shows "AE x in stock_measure t.
          (\<integral>\<^sup>+y. eval_cexpr f (case_nat x \<rho>) y \<partial>stock_measure t') = ennreal (eval_cexpr (\<integral>\<^sub>c f \<partial>t') \<rho> x)"
proof (rule AE_mp[OF _ AE_I2[OF impI]])
  interpret sigma_finite_measure "stock_measure t'" by simp
  let ?f = "\<lambda>x. \<integral>\<^sup>+y. eval_cexpr f (case_nat x \<rho>) y \<partial>stock_measure t'"
  from has_parametrized_subprob_density_integral[OF dens \<rho>]
    have "(\<integral>\<^sup>+x. ?f x \<partial>stock_measure t) \<noteq> \<infinity>" by (auto simp: eval_cexpr_def top_unique)
  thus "AE x in stock_measure t. ?f x \<noteq> \<infinity>" using \<rho> tf varsf by (intro nn_integral_PInf_AE) simp_all
  fix x assume x: "x \<in> space (stock_measure t)" and finite: "?f x \<noteq> \<infinity>"
  have nonneg': "AE y in stock_measure t'. eval_cexpr f (case_nat x \<rho>) y \<ge> 0"
    unfolding eval_cexpr_def using \<rho> x
    by (intro AE_I2 nonneg_cexprD[OF nonneg]) (auto intro!: case_nat_in_state_measure)
  hence "integrable (stock_measure t') (\<lambda>y. eval_cexpr f (case_nat x \<rho>) y)"
    using x \<rho> tf varsf finite by (intro integrableI_nonneg) (simp_all add: top_unique less_top)
  thus "?f x = ennreal (eval_cexpr (\<integral>\<^sub>c f \<partial>t') \<rho> x)" using nonneg'
    by (simp add: extract_real_def nn_integral_eq_integral eval_cexpr_def)
qed

end
