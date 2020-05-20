(*<*)
theory MFOTL
  imports Interval Trace Table
begin
(*>*)

section \<open>Metric First-order Temporal Logic\<close>

context begin

subsection \<open>Formulas and Satisfiability\<close>

qualified type_synonym name = string
qualified type_synonym 'a event = "(name \<times> 'a list)"
qualified type_synonym 'a database = "'a event set"
qualified type_synonym 'a prefix = "(name \<times> 'a list) prefix"
qualified type_synonym 'a trace = "(name \<times> 'a list) trace"

qualified type_synonym 'a env = "'a list"

qualified datatype 'a trm = Var nat | is_Const: Const 'a

qualified primrec fvi_trm :: "nat \<Rightarrow> 'a trm \<Rightarrow> nat set" where
  "fvi_trm b (Var x) = (if b \<le> x then {x - b} else {})"
| "fvi_trm b (Const _) = {}"

abbreviation "fv_trm \<equiv> fvi_trm 0"

qualified primrec eval_trm :: "'a env \<Rightarrow> 'a trm \<Rightarrow> 'a" where
  "eval_trm v (Var x) = v ! x"
| "eval_trm v (Const x) = x"

lemma eval_trm_cong: "\<forall>x\<in>fv_trm t. v ! x = v' ! x \<Longrightarrow> eval_trm v t = eval_trm v' t"
  by (cases t) simp_all

qualified datatype (discs_sels) 'a formula = Pred name "'a trm list" | Eq "'a trm" "'a trm"
  | Neg "'a formula" | Or "'a formula" "'a formula" | Exists "'a formula"
  | Prev \<I> "'a formula" | Next \<I> "'a formula"
  | Since "'a formula" \<I> "'a formula" | Until "'a formula" \<I> "'a formula"

qualified primrec fvi :: "nat \<Rightarrow> 'a formula \<Rightarrow> nat set" where
  "fvi b (Pred r ts) = (\<Union>t\<in>set ts. fvi_trm b t)"
| "fvi b (Eq t1 t2) = fvi_trm b t1 \<union> fvi_trm b t2"
| "fvi b (Neg \<phi>) = fvi b \<phi>"
| "fvi b (Or \<phi> \<psi>) = fvi b \<phi> \<union> fvi b \<psi>"
| "fvi b (Exists \<phi>) = fvi (Suc b) \<phi>"
| "fvi b (Prev I \<phi>) = fvi b \<phi>"
| "fvi b (Next I \<phi>) = fvi b \<phi>"
| "fvi b (Since \<phi> I \<psi>) = fvi b \<phi> \<union> fvi b \<psi>"
| "fvi b (Until \<phi> I \<psi>) = fvi b \<phi> \<union> fvi b \<psi>"

abbreviation "fv \<equiv> fvi 0"

lemma finite_fvi_trm[simp]: "finite (fvi_trm b t)"
  by (cases t) simp_all

lemma finite_fvi[simp]: "finite (fvi b \<phi>)"
  by (induction \<phi> arbitrary: b) simp_all

lemma fvi_trm_Suc: "x \<in> fvi_trm (Suc b) t \<longleftrightarrow> Suc x \<in> fvi_trm b t"
  by (cases t) auto

lemma fvi_Suc: "x \<in> fvi (Suc b) \<phi> \<longleftrightarrow> Suc x \<in> fvi b \<phi>"
  by (induction \<phi> arbitrary: b) (simp_all add: fvi_trm_Suc)

lemma fvi_Suc_bound:
  assumes "\<forall>i\<in>fvi (Suc b) \<phi>. i < n"
  shows "\<forall>i\<in>fvi b \<phi>. i < Suc n"
proof
  fix i
  assume "i \<in> fvi b \<phi>"
  with assms show "i < Suc n" by (cases i) (simp_all add: fvi_Suc)
qed

qualified definition nfv :: "'a formula \<Rightarrow> nat" where
  "nfv \<phi> = Max (insert 0 (Suc ` fv \<phi>))"

qualified definition envs :: "'a formula \<Rightarrow> 'a env set" where
  "envs \<phi> = {v. length v = nfv \<phi>}"

lemma nfv_simps[simp]:
  "nfv (Neg \<phi>) = nfv \<phi>"
  "nfv (Or \<phi> \<psi>) = max (nfv \<phi>) (nfv \<psi>)"
  "nfv (Prev I \<phi>) = nfv \<phi>"
  "nfv (Next I \<phi>) = nfv \<phi>"
  "nfv (Since \<phi> I \<psi>) = max (nfv \<phi>) (nfv \<psi>)"
  "nfv (Until \<phi> I \<psi>) = max (nfv \<phi>) (nfv \<psi>)"
  unfolding nfv_def by (simp_all add: image_Un Max_Un[symmetric])

lemma fvi_less_nfv: "\<forall>i\<in>fv \<phi>. i < nfv \<phi>"
  unfolding nfv_def
  by (auto simp add: Max_gr_iff intro: max.strict_coboundedI2)


qualified primrec future_reach :: "'a formula \<Rightarrow> enat" where
  "future_reach (Pred _ _) = 0"
| "future_reach (Eq _ _) = 0"
| "future_reach (Neg \<phi>) = future_reach \<phi>"
| "future_reach (Or \<phi> \<psi>) = max (future_reach \<phi>) (future_reach \<psi>)"
| "future_reach (Exists \<phi>) = future_reach \<phi>"
| "future_reach (Prev I \<phi>) = future_reach \<phi> - left I"
| "future_reach (Next I \<phi>) = future_reach \<phi> + right I + 1"
| "future_reach (Since \<phi> I \<psi>) = max (future_reach \<phi>) (future_reach \<psi> - left I)"
| "future_reach (Until \<phi> I \<psi>) = max (future_reach \<phi>) (future_reach \<psi>) + right I + 1"


qualified primrec sat :: "'a trace \<Rightarrow> 'a env \<Rightarrow> nat \<Rightarrow> 'a formula \<Rightarrow> bool" where
  "sat \<sigma> v i (Pred r ts) = ((r, map (eval_trm v) ts) \<in> \<Gamma> \<sigma> i)"
| "sat \<sigma> v i (Eq t1 t2) = (eval_trm v t1 = eval_trm v t2)"
| "sat \<sigma> v i (Neg \<phi>) = (\<not> sat \<sigma> v i \<phi>)"
| "sat \<sigma> v i (Or \<phi> \<psi>) = (sat \<sigma> v i \<phi> \<or> sat \<sigma> v i \<psi>)"
| "sat \<sigma> v i (Exists \<phi>) = (\<exists>z. sat \<sigma> (z # v) i \<phi>)"
| "sat \<sigma> v i (Prev I \<phi>) = (case i of 0 \<Rightarrow> False | Suc j \<Rightarrow> mem (\<tau> \<sigma> i - \<tau> \<sigma> j) I \<and> sat \<sigma> v j \<phi>)"
| "sat \<sigma> v i (Next I \<phi>) = (mem (\<tau> \<sigma> (Suc i) - \<tau> \<sigma> i) I \<and> sat \<sigma> v (Suc i) \<phi>)"
| "sat \<sigma> v i (Since \<phi> I \<psi>) = (\<exists>j\<le>i. mem (\<tau> \<sigma> i - \<tau> \<sigma> j) I \<and> sat \<sigma> v j \<psi> \<and> (\<forall>k \<in> {j <.. i}. sat \<sigma> v k \<phi>))"
| "sat \<sigma> v i (Until \<phi> I \<psi>) = (\<exists>j\<ge>i. mem (\<tau> \<sigma> j - \<tau> \<sigma> i) I \<and> sat \<sigma> v j \<psi> \<and> (\<forall>k \<in> {i ..< j}. sat \<sigma> v k \<phi>))"

lemma sat_Until_rec: "sat \<sigma> v i (Until \<phi> I \<psi>) \<longleftrightarrow>
  mem 0 I \<and> sat \<sigma> v i \<psi> \<or>
  (\<Delta> \<sigma> (i + 1) \<le> right I \<and> sat \<sigma> v i \<phi> \<and> sat \<sigma> v (i + 1) (Until \<phi> (subtract (\<Delta> \<sigma> (i + 1)) I) \<psi>))"
  (is "?L \<longleftrightarrow> ?R")
proof (rule iffI; (elim disjE conjE)?)
  assume ?L
  then obtain j where j: "i \<le> j" "mem (\<tau> \<sigma> j - \<tau> \<sigma> i) I" "sat \<sigma> v j \<psi>" "\<forall>k \<in> {i ..< j}. sat \<sigma> v k \<phi>"
    by auto
  then show ?R
  proof (cases "i = j")
    case False
    with j(1,2) have "\<Delta> \<sigma> (i + 1) \<le> right I"
      by (auto elim: order_trans[rotated] simp: diff_le_mono)
    moreover from False j(1,4) have "sat \<sigma> v i \<phi>" by auto
    moreover from False j have "sat \<sigma> v (i + 1) (Until \<phi> (subtract (\<Delta> \<sigma> (i + 1)) I) \<psi>)"
      by (cases "right I") (auto simp: le_diff_conv le_diff_conv2 intro!: exI[of _ j])
    ultimately show ?thesis by blast
  qed simp
next
  assume \<Delta>: "\<Delta> \<sigma> (i + 1) \<le> right I" and now: "sat \<sigma> v i \<phi>" and
   "next": "sat \<sigma> v (i + 1) (Until \<phi> (subtract (\<Delta> \<sigma> (i + 1)) I) \<psi>)"
  from "next" obtain j where j: "i + 1 \<le> j" "mem (\<tau> \<sigma> j - \<tau> \<sigma> (i + 1)) ((subtract (\<Delta> \<sigma> (i + 1)) I))"
      "sat \<sigma> v j \<psi>" "\<forall>k \<in> {i + 1 ..< j}. sat \<sigma> v k \<phi>"
    by auto
  from \<Delta> j(1,2) have "mem (\<tau> \<sigma> j - \<tau> \<sigma> i) I"
    by (cases "right I") (auto simp: le_diff_conv2)
  with now j(1,3,4) show ?L by (auto simp: le_eq_less_or_eq[of i] intro!: exI[of _ j])
qed auto

lemma sat_Since_rec: "sat \<sigma> v i (Since \<phi> I \<psi>) \<longleftrightarrow>
  mem 0 I \<and> sat \<sigma> v i \<psi> \<or>
  (i > 0 \<and> \<Delta> \<sigma> i \<le> right I \<and> sat \<sigma> v i \<phi> \<and> sat \<sigma> v (i - 1) (Since \<phi> (subtract (\<Delta> \<sigma> i) I) \<psi>))"
  (is "?L \<longleftrightarrow> ?R")
proof (rule iffI; (elim disjE conjE)?)
  assume ?L
  then obtain j where j: "j \<le> i" "mem (\<tau> \<sigma> i - \<tau> \<sigma> j) I" "sat \<sigma> v j \<psi>" "\<forall>k \<in> {j <.. i}. sat \<sigma> v k \<phi>"
    by auto
  then show ?R
  proof (cases "i = j")
    case False
    with j(1) obtain k where [simp]: "i = k + 1"
      by (cases i) auto
    with j(1,2) False have "\<Delta> \<sigma> i \<le> right I"
      by (auto elim: order_trans[rotated] simp: diff_le_mono2 le_Suc_eq)
    moreover from False j(1,4) have "sat \<sigma> v i \<phi>" by auto
    moreover from False j have "sat \<sigma> v (i - 1) (Since \<phi> (subtract (\<Delta> \<sigma> i) I) \<psi>)"
      by (cases "right I") (auto simp: le_diff_conv le_diff_conv2 intro!: exI[of _ j])
    ultimately show ?thesis by auto
  qed simp
next
  assume i: "0 < i" and \<Delta>: "\<Delta> \<sigma> i \<le> right I" and now: "sat \<sigma> v i \<phi>" and
   "prev": "sat \<sigma> v (i - 1) (Since \<phi> (subtract (\<Delta> \<sigma> i) I) \<psi>)"
  from "prev" obtain j where j: "j \<le> i - 1" "mem (\<tau> \<sigma> (i - 1) - \<tau> \<sigma> j) ((subtract (\<Delta> \<sigma> i) I))"
      "sat \<sigma> v j \<psi>" "\<forall>k \<in> {j <.. i - 1}. sat \<sigma> v k \<phi>"
    by auto
  from \<Delta> i j(1,2) have "mem (\<tau> \<sigma> i - \<tau> \<sigma> j) I"
    by (cases "right I") (auto simp: le_diff_conv2)
  with now i j(1,3,4) show ?L by (auto simp: le_Suc_eq gr0_conv_Suc intro!: exI[of _ j])
qed auto

lemma sat_Since_0: "sat \<sigma> v 0 (Since \<phi> I \<psi>) \<longleftrightarrow> mem 0 I \<and> sat \<sigma> v 0 \<psi>"
  by auto

lemma sat_Since_point: "sat \<sigma> v i (Since \<phi> I \<psi>) \<Longrightarrow>
    (\<And>j. j \<le> i \<Longrightarrow> mem (\<tau> \<sigma> i - \<tau> \<sigma> j) I \<Longrightarrow> sat \<sigma> v i (Since \<phi> (point (\<tau> \<sigma> i - \<tau> \<sigma> j)) \<psi>) \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto intro: diff_le_self)

lemma sat_Since_pointD: "sat \<sigma> v i (Since \<phi> (point t) \<psi>) \<Longrightarrow> mem t I \<Longrightarrow> sat \<sigma> v i (Since \<phi> I \<psi>)"
  by auto

lemma eval_trm_fvi_cong: "\<forall>x\<in>fv_trm t. v!x = v'!x \<Longrightarrow> eval_trm v t = eval_trm v' t"
  by (cases t) simp_all

lemma sat_fvi_cong: "\<forall>x\<in>fv \<phi>. v!x = v'!x \<Longrightarrow> sat \<sigma> v i \<phi> = sat \<sigma> v' i \<phi>"
proof (induct \<phi> arbitrary: v v' i)
  case (Pred n ts)
  show ?case by (simp cong: map_cong eval_trm_fvi_cong[OF Pred[simplified, THEN bspec]])
next
  case (Eq x1 x2)
  then show ?case  unfolding fvi.simps sat.simps by (metis UnCI eval_trm_fvi_cong)
next
  case (Exists \<phi>)
  then show ?case unfolding sat.simps by (intro iff_exI) (simp add: fvi_Suc nth_Cons')
qed (auto 8 0 simp add: nth_Cons' split: nat.splits intro!: iff_exI)


subsection \<open>Defined Connectives\<close>

qualified definition "And \<phi> \<psi> = Neg (Or (Neg \<phi>) (Neg \<psi>))"

lemma fvi_And: "fvi b (And \<phi> \<psi>) = fvi b \<phi> \<union> fvi b \<psi>"
  unfolding And_def by simp

lemma nfv_And[simp]: "nfv (And \<phi> \<psi>) = max (nfv \<phi>) (nfv \<psi>)"
  unfolding nfv_def by (simp add: fvi_And image_Un Max_Un[symmetric])

lemma future_reach_And: "future_reach (And \<phi> \<psi>) = max (future_reach \<phi>) (future_reach \<psi>)"
  unfolding And_def by simp

lemma sat_And: "sat \<sigma> v i (And \<phi> \<psi>) = (sat \<sigma> v i \<phi> \<and> sat \<sigma> v i \<psi>)"
  unfolding And_def by simp

qualified definition "And_Not \<phi> \<psi> = Neg (Or (Neg \<phi>) \<psi>)"

lemma fvi_And_Not: "fvi b (And_Not \<phi> \<psi>) = fvi b \<phi> \<union> fvi b \<psi>"
  unfolding And_Not_def by simp

lemma nfv_And_Not[simp]: "nfv (And_Not \<phi> \<psi>) = max (nfv \<phi>) (nfv \<psi>)"
  unfolding nfv_def by (simp add: fvi_And_Not image_Un Max_Un[symmetric])

lemma future_reach_And_Not: "future_reach (And_Not \<phi> \<psi>) = max (future_reach \<phi>) (future_reach \<psi>)"
  unfolding And_Not_def by simp

lemma sat_And_Not: "sat \<sigma> v i (And_Not \<phi> \<psi>) = (sat \<sigma> v i \<phi> \<and> \<not> sat \<sigma> v i \<psi>)"
  unfolding And_Not_def by simp


subsection \<open>Safe Formulas\<close>

fun safe_formula :: "'a MFOTL.formula \<Rightarrow> bool" where
  "safe_formula (MFOTL.Eq t1 t2) = (MFOTL.is_Const t1 \<or> MFOTL.is_Const t2)"
| "safe_formula (MFOTL.Neg (MFOTL.Eq (MFOTL.Const x) (MFOTL.Const y))) = True"
| "safe_formula (MFOTL.Neg (MFOTL.Eq (MFOTL.Var x) (MFOTL.Var y))) = (x = y)"
| "safe_formula (MFOTL.Pred e ts) = True"
| "safe_formula (MFOTL.Neg (MFOTL.Or (MFOTL.Neg \<phi>) \<psi>)) = (safe_formula \<phi> \<and>
    (safe_formula \<psi> \<and> MFOTL.fv \<psi> \<subseteq> MFOTL.fv \<phi> \<or> (case \<psi> of MFOTL.Neg \<psi>' \<Rightarrow> safe_formula \<psi>' | _ \<Rightarrow> False)))"
| "safe_formula (MFOTL.Or \<phi> \<psi>) = (MFOTL.fv \<psi> = MFOTL.fv \<phi> \<and> safe_formula \<phi> \<and> safe_formula \<psi>)"
| "safe_formula (MFOTL.Exists \<phi>) = (safe_formula \<phi>)"
| "safe_formula (MFOTL.Prev I \<phi>) = (safe_formula \<phi>)"
| "safe_formula (MFOTL.Next I \<phi>) = (safe_formula \<phi>)"
| "safe_formula (MFOTL.Since \<phi> I \<psi>) = (MFOTL.fv \<phi> \<subseteq> MFOTL.fv \<psi> \<and>
    (safe_formula \<phi> \<or> (case \<phi> of MFOTL.Neg \<phi>' \<Rightarrow> safe_formula \<phi>' | _ \<Rightarrow> False)) \<and> safe_formula \<psi>)"
| "safe_formula (MFOTL.Until \<phi> I \<psi>) = (MFOTL.fv \<phi> \<subseteq> MFOTL.fv \<psi> \<and>
    (safe_formula \<phi> \<or> (case \<phi> of MFOTL.Neg \<phi>' \<Rightarrow> safe_formula \<phi>' | _ \<Rightarrow> False)) \<and> safe_formula \<psi>)"
| "safe_formula _ = False"

lemma disjE_Not2: "P \<or> Q \<Longrightarrow> (P \<Longrightarrow> R) \<Longrightarrow> (\<not>P \<Longrightarrow> Q \<Longrightarrow> R) \<Longrightarrow> R"
  by blast

lemma safe_formula_induct[consumes 1]:
  assumes "safe_formula \<phi>"
    and "\<And>t1 t2. MFOTL.is_Const t1 \<Longrightarrow> P (MFOTL.Eq t1 t2)"
    and "\<And>t1 t2. MFOTL.is_Const t2 \<Longrightarrow> P (MFOTL.Eq t1 t2)"
    and "\<And>x y. P (MFOTL.Neg (MFOTL.Eq (MFOTL.Const x) (MFOTL.Const y)))"
    and "\<And>x y. x = y \<Longrightarrow> P (MFOTL.Neg (MFOTL.Eq (MFOTL.Var x) (MFOTL.Var y)))"
    and "\<And>e ts. P (MFOTL.Pred e ts)"
    and "\<And>\<phi> \<psi>. \<not> (safe_formula (MFOTL.Neg \<psi>) \<and> MFOTL.fv \<psi> \<subseteq> MFOTL.fv \<phi>) \<Longrightarrow> P \<phi> \<Longrightarrow> P \<psi> \<Longrightarrow> P (MFOTL.And \<phi> \<psi>)"
    and "\<And>\<phi> \<psi>. safe_formula \<psi> \<Longrightarrow> MFOTL.fv \<psi> \<subseteq> MFOTL.fv \<phi> \<Longrightarrow> P \<phi> \<Longrightarrow> P \<psi> \<Longrightarrow> P (MFOTL.And_Not \<phi> \<psi>)"
    and "\<And>\<phi> \<psi>. MFOTL.fv \<psi> = MFOTL.fv \<phi> \<Longrightarrow> P \<phi> \<Longrightarrow> P \<psi> \<Longrightarrow> P (MFOTL.Or \<phi> \<psi>)"
    and "\<And>\<phi>. P \<phi> \<Longrightarrow> P (MFOTL.Exists \<phi>)"
    and "\<And>I \<phi>. P \<phi> \<Longrightarrow> P (MFOTL.Prev I \<phi>)"
    and "\<And>I \<phi>. P \<phi> \<Longrightarrow> P (MFOTL.Next I \<phi>)"
    and "\<And>\<phi> I \<psi>. MFOTL.fv \<phi> \<subseteq> MFOTL.fv \<psi> \<Longrightarrow> safe_formula \<phi> \<Longrightarrow> P \<phi> \<Longrightarrow> P \<psi> \<Longrightarrow> P (MFOTL.Since \<phi> I \<psi>)"
    and "\<And>\<phi> I \<psi>. MFOTL.fv (MFOTL.Neg \<phi>) \<subseteq> MFOTL.fv \<psi> \<Longrightarrow>
      \<not> safe_formula (MFOTL.Neg \<phi>) \<Longrightarrow> P \<phi> \<Longrightarrow> P \<psi> \<Longrightarrow> P (MFOTL.Since (MFOTL.Neg \<phi>) I \<psi> )"
    and "\<And>\<phi> I \<psi>. MFOTL.fv \<phi> \<subseteq> MFOTL.fv \<psi> \<Longrightarrow> safe_formula \<phi> \<Longrightarrow> P \<phi> \<Longrightarrow> P \<psi> \<Longrightarrow> P (MFOTL.Until \<phi> I \<psi>)"
    and "\<And>\<phi> I \<psi>. MFOTL.fv (MFOTL.Neg \<phi>) \<subseteq> MFOTL.fv \<psi> \<Longrightarrow>
      \<not> safe_formula (MFOTL.Neg \<phi>) \<Longrightarrow> P \<phi> \<Longrightarrow> P \<psi> \<Longrightarrow> P (MFOTL.Until (MFOTL.Neg \<phi>) I \<psi>)"
  shows "P \<phi>"
  using assms(1)
proof (induction rule: safe_formula.induct)
  case (5 \<phi> \<psi>)
  then show ?case
    by (cases \<psi>)
      (auto 0 3 elim!: disjE_Not2 intro: assms[unfolded MFOTL.And_def MFOTL.And_Not_def])
next
  case (10 \<phi> I \<psi>)
  then show ?case
    by (cases \<phi>) (auto 0 3 elim!: disjE_Not2 intro: assms)
next
  case (11 \<phi> I \<psi>)
  then show ?case
    by (cases \<phi>) (auto 0 3 elim!: disjE_Not2 intro: assms)
qed (auto intro: assms)


subsection \<open>Slicing Traces\<close>

qualified primrec matches :: "'a env \<Rightarrow> 'a formula \<Rightarrow> name \<times> 'a list \<Rightarrow> bool" where
  "matches v (Pred r ts) e = (r = fst e \<and> map (eval_trm v) ts = snd e)"
| "matches v (Eq _ _) e = False"
| "matches v (Neg \<phi>) e = matches v \<phi> e"
| "matches v (Or \<phi> \<psi>) e = (matches v \<phi> e \<or> matches v \<psi> e)"
| "matches v (Exists \<phi>) e = (\<exists>z. matches (z # v) \<phi> e)"
| "matches v (Prev I \<phi>) e = matches v \<phi> e"
| "matches v (Next I \<phi>) e = matches v \<phi> e"
| "matches v (Since \<phi> I \<psi>) e = (matches v \<phi> e \<or> matches v \<psi> e)"
| "matches v (Until \<phi> I \<psi>) e = (matches v \<phi> e \<or> matches v \<psi> e)"

lemma matches_fvi_cong: "\<forall>x\<in>fv \<phi>. v!x = v'!x \<Longrightarrow> matches v \<phi> e = matches v' \<phi> e"
proof (induct \<phi> arbitrary: v v')
  case (Pred n ts)
  show ?case by (simp cong: map_cong eval_trm_fvi_cong[OF Pred[simplified, THEN bspec]])
next
  case (Exists \<phi>)
  then show ?case unfolding matches.simps by (intro iff_exI) (simp add: fvi_Suc nth_Cons')
qed (auto 5 0 simp add: nth_Cons')

abbreviation relevant_events where
  "relevant_events \<phi> S \<equiv> {e. S \<inter> {v. matches v \<phi> e} \<noteq> {}}"

qualified definition slice :: "'a formula \<Rightarrow> 'a env set \<Rightarrow> 'a trace \<Rightarrow> 'a trace" where
  "slice \<phi> S \<sigma> = map_\<Gamma> (\<lambda>D. D \<inter> relevant_events \<phi> S) \<sigma>"

lemma \<tau>_slice[simp]: "\<tau> (slice \<phi> S \<sigma>) = \<tau> \<sigma>"
  unfolding slice_def by (simp add: fun_eq_iff)

lemma sat_slice_strong: "relevant_events \<phi> S \<subseteq> E \<Longrightarrow> v \<in> S \<Longrightarrow>
  sat \<sigma> v i \<phi> \<longleftrightarrow> sat (map_\<Gamma> (\<lambda>D. D \<inter> E) \<sigma>) v i \<phi>"
proof (induction \<phi> arbitrary: v S i)
  case (Pred r ts)
  then show ?case by (auto simp: subset_eq)
next
  case (Eq t1 t2)
  show ?case
    unfolding sat.simps
    by simp
next
  case (Neg \<phi>)
  then show ?case by simp
next
  case (Or \<phi> \<psi>)
  show ?case using Or.IH[of S] Or.prems
    by (auto simp: Collect_disj_eq Int_Un_distrib subset_iff)
next
  case (Exists \<phi>)
  have "sat \<sigma> (z # v) i \<phi> = sat (map_\<Gamma> (\<lambda>D. D \<inter> E) \<sigma>) (z # v) i \<phi>" for z
    using Exists.prems by (auto intro!: Exists.IH[of "{z # v | v. v \<in> S}"])
  then show ?case by simp
next
  case (Prev I \<phi>)
  then show ?case by (auto cong: nat.case_cong)
next
  case (Next I \<phi>)
  then show ?case by simp
next
  case (Since \<phi> I \<psi>)
  show ?case using Since.IH[of S] Since.prems
   by (auto simp: Collect_disj_eq Int_Un_distrib subset_iff)
next
  case (Until \<phi> I \<psi>)
  show ?case using Until.IH[of S] Until.prems
   by (auto simp: Collect_disj_eq Int_Un_distrib subset_iff)
qed

lemma sat_slice_iff:
  assumes "v \<in> S"
  shows "sat \<sigma> v i \<phi> \<longleftrightarrow> sat (slice \<phi> S \<sigma>) v i \<phi>"
  unfolding slice_def
  by (rule sat_slice_strong[of S, OF subset_refl assms])

qualified lift_definition pslice :: "'a formula \<Rightarrow> 'a env set \<Rightarrow> 'a prefix \<Rightarrow> 'a prefix" is
  "\<lambda>\<phi> S \<pi>. map (\<lambda>(D, t). (D \<inter> relevant_events \<phi> S, t)) \<pi>"
  by (auto simp: o_def split_beta)

lemma prefix_of_pslice_slice: "prefix_of \<pi> \<sigma> \<Longrightarrow> prefix_of (pslice \<phi> R \<pi>) (MFOTL.slice \<phi> R \<sigma>)"
  unfolding MFOTL.slice_def
  by transfer simp

lemma plen_pslice[simp]: "plen (pslice \<phi> R \<pi>) = plen \<pi>"
  by transfer simp

lemma pslice_pnil[simp]: "pslice \<phi> R pnil = pnil"
  by transfer simp

lemma last_ts_pslice[simp]: "last_ts (pslice \<phi> R \<pi>) = last_ts \<pi>"
  by transfer (simp add: last_map case_prod_beta split: list.split)

lemma prefix_of_replace_prefix:
  "prefix_of (pslice \<phi> R \<pi>) \<sigma> \<Longrightarrow> prefix_of \<pi> (replace_prefix \<pi> \<sigma>)"
proof (transfer; safe; goal_cases)
  case (1 \<phi> R \<pi> \<sigma>)
  then show ?case
    by (subst (asm) (2) stake_sdrop[symmetric, of _ "length \<pi>"])
      (auto 0 3 simp: ssorted_shift split_beta o_def stake_shift sdrop_smap[symmetric]
        ssorted_sdrop not_le pslice_def simp del: sdrop_smap)
qed

lemma slice_replace_prefix:
  "prefix_of (pslice \<phi> R \<pi>) \<sigma> \<Longrightarrow> slice \<phi> R (replace_prefix \<pi> \<sigma>) = slice \<phi> R \<sigma>"
unfolding slice_def proof (transfer; safe; goal_cases)
  case (1 \<phi> R \<pi> \<sigma>)
  then show ?case
    by (subst (asm) (2) stake_sdrop[symmetric, of \<sigma> "length \<pi>"],
        subst (3) stake_sdrop[symmetric, of \<sigma> "length \<pi>"])
      (auto simp: ssorted_shift split_beta o_def stake_shift sdrop_smap[symmetric] ssorted_sdrop
        not_le pslice_def simp del: sdrop_smap cong: map_cong)
qed

lemma prefix_of_psliceD:
  assumes "prefix_of (pslice \<phi> R \<pi>) \<sigma>"
  shows "\<exists>\<sigma>'. prefix_of \<pi> \<sigma>' \<and> prefix_of (pslice \<phi> R \<pi>) (slice \<phi> R \<sigma>')"
proof -
  from assms(1) obtain \<sigma>' where 1: "prefix_of \<pi> \<sigma>'"
    using ex_prefix_of by blast
  then have "prefix_of (pslice \<phi> R \<pi>) (slice \<phi> R \<sigma>')"
    unfolding MFOTL.slice_def
    by transfer simp
  with 1 show ?thesis by blast
qed

lemma prefix_of_sliceD:
  assumes "prefix_of \<pi>' (slice \<phi> R \<sigma>)"
  shows "\<exists>\<pi>''. \<pi>' = pslice \<phi> R \<pi>'' \<and> prefix_of \<pi>'' \<sigma>"
  using assms unfolding slice_def
  by transfer (auto intro!: exI[of _ "stake (length _) _"] elim: sym dest: sorted_stake)

end (*context*)

(*<*)
end
(*>*)