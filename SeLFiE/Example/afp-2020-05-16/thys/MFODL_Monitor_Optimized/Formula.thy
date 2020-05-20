(*<*)
theory Formula
  imports Interval Trace Regex Event_Data
    "MFOTL_Monitor.Table"
    "HOL-Library.Mapping"
    Containers.Set_Impl
begin
(*>*)

section \<open>Metric first-order temporal logic\<close>

derive (eq) ceq enat

instantiation enat :: ccompare begin
definition ccompare_enat :: "enat comparator option" where
  "ccompare_enat = Some (\<lambda>x y. if x = y then order.Eq else if x < y then order.Lt else order.Gt)"

instance by intro_classes
    (auto simp: ccompare_enat_def split: if_splits intro!: comparator.intro)
end

context begin

subsection \<open>Formulas and satisfiability\<close>

qualified type_synonym name = string
qualified type_synonym event = "(name \<times> event_data list)"
qualified type_synonym database = "(name, event_data list set list) mapping"
qualified type_synonym prefix = "(name \<times> event_data list) prefix"
qualified type_synonym trace = "(name \<times> event_data list) trace"

qualified type_synonym env = "event_data list"

subsubsection \<open>Syntax\<close>

qualified datatype trm = is_Var: Var nat | is_Const: Const event_data
  | Plus trm trm | Minus trm trm | UMinus trm | Mult trm trm | Div trm trm | Mod trm trm
  | F2i trm | I2f trm

qualified primrec fvi_trm :: "nat \<Rightarrow> trm \<Rightarrow> nat set" where
  "fvi_trm b (Var x) = (if b \<le> x then {x - b} else {})"
| "fvi_trm b (Const _) = {}"
| "fvi_trm b (Plus x y) = fvi_trm b x \<union> fvi_trm b y"
| "fvi_trm b (Minus x y) = fvi_trm b x \<union> fvi_trm b y"
| "fvi_trm b (UMinus x) = fvi_trm b x"
| "fvi_trm b (Mult x y) = fvi_trm b x \<union> fvi_trm b y"
| "fvi_trm b (Div x y) = fvi_trm b x \<union> fvi_trm b y"
| "fvi_trm b (Mod x y) = fvi_trm b x \<union> fvi_trm b y"
| "fvi_trm b (F2i x) = fvi_trm b x"
| "fvi_trm b (I2f x) = fvi_trm b x"

abbreviation "fv_trm \<equiv> fvi_trm 0"

qualified primrec eval_trm :: "env \<Rightarrow> trm \<Rightarrow> event_data" where
  "eval_trm v (Var x) = v ! x"
| "eval_trm v (Const x) = x"
| "eval_trm v (Plus x y) = eval_trm v x + eval_trm v y"
| "eval_trm v (Minus x y) = eval_trm v x - eval_trm v y"
| "eval_trm v (UMinus x) = - eval_trm v x"
| "eval_trm v (Mult x y) = eval_trm v x * eval_trm v y"
| "eval_trm v (Div x y) = eval_trm v x div eval_trm v y"
| "eval_trm v (Mod x y) = eval_trm v x mod eval_trm v y"
| "eval_trm v (F2i x) = EInt (integer_of_event_data (eval_trm v x))"
| "eval_trm v (I2f x) = EFloat (double_of_event_data (eval_trm v x))"

lemma eval_trm_fv_cong: "\<forall>x\<in>fv_trm t. v ! x = v' ! x \<Longrightarrow> eval_trm v t = eval_trm v' t"
  by (induction t) simp_all


qualified datatype agg_type = Agg_Cnt | Agg_Min | Agg_Max | Agg_Sum | Agg_Avg | Agg_Med
qualified type_synonym agg_op = "agg_type \<times> event_data"

definition flatten_multiset :: "(event_data \<times> enat) set \<Rightarrow> event_data list" where
  "flatten_multiset M = concat (map (\<lambda>(x, c). replicate (the_enat c) x) (csorted_list_of_set M))"

fun eval_agg_op :: "agg_op \<Rightarrow> (event_data \<times> enat) set \<Rightarrow> event_data" where
  "eval_agg_op (Agg_Cnt, y0) M = EInt (integer_of_int (length (flatten_multiset M)))"
| "eval_agg_op (Agg_Min, y0) M = (case flatten_multiset M of
      [] \<Rightarrow> y0
    | x # xs \<Rightarrow> foldl min x xs)"
| "eval_agg_op (Agg_Max, y0) M = (case flatten_multiset M of
      [] \<Rightarrow> y0
    | x # xs \<Rightarrow> foldl max x xs)"
| "eval_agg_op (Agg_Sum, y0) M = foldl plus y0 (flatten_multiset M)"
| "eval_agg_op (Agg_Avg, y0) M = EFloat (let xs = flatten_multiset M in case xs of
      [] \<Rightarrow> 0
    | _ \<Rightarrow> double_of_event_data (foldl plus (EInt 0) xs) / double_of_int (length xs))"
| "eval_agg_op (Agg_Med, y0) M = EFloat (let xs = flatten_multiset M; u = length xs in
    if u = 0 then 0 else
      let u' = u div 2 in
      if even u then
        (double_of_event_data (xs ! (u'-1)) + double_of_event_data (xs ! u') / double_of_int 2)
      else double_of_event_data (xs ! u'))"

qualified datatype (discs_sels) formula = Pred name "trm list"
  | Let name nat formula formula
  | Eq trm trm | Less trm trm | LessEq trm trm
  | Neg formula | Or formula formula | And formula formula | Ands "formula list" | Exists formula
  | Agg nat agg_op nat trm formula
  | Prev \<I> formula | Next \<I> formula
  | Since formula \<I> formula | Until formula \<I> formula
  | MatchF \<I> "formula Regex.regex" | MatchP \<I> "formula Regex.regex"

qualified definition "FF = Exists (Neg (Eq (Var 0) (Var 0)))"
qualified definition "TT \<equiv> Neg FF"

qualified fun fvi :: "nat \<Rightarrow> formula \<Rightarrow> nat set" where
  "fvi b (Pred r ts) = (\<Union>t\<in>set ts. fvi_trm b t)"
| "fvi b (Let p _ \<phi> \<psi>) = fvi b \<psi>"
| "fvi b (Eq t1 t2) = fvi_trm b t1 \<union> fvi_trm b t2"
| "fvi b (Less t1 t2) = fvi_trm b t1 \<union> fvi_trm b t2"
| "fvi b (LessEq t1 t2) = fvi_trm b t1 \<union> fvi_trm b t2"
| "fvi b (Neg \<phi>) = fvi b \<phi>"
| "fvi b (Or \<phi> \<psi>) = fvi b \<phi> \<union> fvi b \<psi>"
| "fvi b (And \<phi> \<psi>) = fvi b \<phi> \<union> fvi b \<psi>"
| "fvi b (Ands \<phi>s) = (let xs = map (fvi b) \<phi>s in \<Union>x\<in>set xs. x)"
| "fvi b (Exists \<phi>) = fvi (Suc b) \<phi>"
| "fvi b (Agg y \<omega> b' f \<phi>) = fvi (b + b') \<phi> \<union> fvi_trm (b + b') f \<union> (if b \<le> y then {y - b} else {})"
| "fvi b (Prev I \<phi>) = fvi b \<phi>"
| "fvi b (Next I \<phi>) = fvi b \<phi>"
| "fvi b (Since \<phi> I \<psi>) = fvi b \<phi> \<union> fvi b \<psi>"
| "fvi b (Until \<phi> I \<psi>) = fvi b \<phi> \<union> fvi b \<psi>"
| "fvi b (MatchF I r) = Regex.fv_regex (fvi b) r"
| "fvi b (MatchP I r) = Regex.fv_regex (fvi b) r"

abbreviation "fv \<equiv> fvi 0"
abbreviation "fv_regex \<equiv> Regex.fv_regex fv"

lemma fv_abbrevs[simp]: "fv TT = {}" "fv FF = {}"
  unfolding TT_def FF_def by auto

lemma fv_subset_Ands: "\<phi> \<in> set \<phi>s \<Longrightarrow> fv \<phi> \<subseteq> fv (Ands \<phi>s)"
  by auto

lemma finite_fvi_trm[simp]: "finite (fvi_trm b t)"
  by (induction t) simp_all

lemma finite_fvi[simp]: "finite (fvi b \<phi>)"
  by (induction \<phi> arbitrary: b) simp_all

lemma fvi_trm_plus: "x \<in> fvi_trm (b + c) t \<longleftrightarrow> x + c \<in> fvi_trm b t"
  by (induction t) auto

lemma fvi_trm_iff_fv_trm: "x \<in> fvi_trm b t \<longleftrightarrow> x + b \<in> fv_trm t"
  using fvi_trm_plus[where b=0 and c=b] by simp_all

lemma fvi_plus: "x \<in> fvi (b + c) \<phi> \<longleftrightarrow> x + c \<in> fvi b \<phi>"
proof (induction \<phi> arbitrary: b rule: formula.induct)
  case (Exists \<phi>)
  then show ?case by force
next
  case (Agg y \<omega> b' f \<phi>)
  have *: "b + c + b' = b + b' + c" by simp
  from Agg show ?case by (force simp: * fvi_trm_plus)
qed (auto simp add: fvi_trm_plus fv_regex_commute[where g = "\<lambda>x. x + c"])

lemma fvi_Suc: "x \<in> fvi (Suc b) \<phi> \<longleftrightarrow> Suc x \<in> fvi b \<phi>"
  using fvi_plus[where c=1] by simp

lemma fvi_plus_bound:
  assumes "\<forall>i\<in>fvi (b + c) \<phi>. i < n"
  shows "\<forall>i\<in>fvi b \<phi>. i < c + n"
proof
  fix i
  assume "i \<in> fvi b \<phi>"
  show "i < c + n"
  proof (cases "i < c")
    case True
    then show ?thesis by simp
  next
    case False
    then obtain i' where "i = i' + c"
      using nat_le_iff_add by (auto simp: not_less)
    with assms \<open>i \<in> fvi b \<phi>\<close> show ?thesis by (simp add: fvi_plus)
  qed
qed

lemma fvi_Suc_bound:
  assumes "\<forall>i\<in>fvi (Suc b) \<phi>. i < n"
  shows "\<forall>i\<in>fvi b \<phi>. i < Suc n"
  using assms fvi_plus_bound[where c=1] by simp

lemma fvi_iff_fv: "x \<in> fvi b \<phi> \<longleftrightarrow> x + b \<in> fv \<phi>"
  using fvi_plus[where b=0 and c=b] by simp_all

qualified definition nfv :: "formula \<Rightarrow> nat" where
  "nfv \<phi> = Max (insert 0 (Suc ` fv \<phi>))"

qualified abbreviation nfv_regex where
  "nfv_regex \<equiv> Regex.nfv_regex fv"

qualified definition envs :: "formula \<Rightarrow> env set" where
  "envs \<phi> = {v. length v = nfv \<phi>}"

lemma nfv_simps[simp]:
  "nfv (Let p b \<phi> \<psi>) = nfv \<psi>"
  "nfv (Neg \<phi>) = nfv \<phi>"
  "nfv (Or \<phi> \<psi>) = max (nfv \<phi>) (nfv \<psi>)"
  "nfv (And \<phi> \<psi>) = max (nfv \<phi>) (nfv \<psi>)"
  "nfv (Prev I \<phi>) = nfv \<phi>"
  "nfv (Next I \<phi>) = nfv \<phi>"
  "nfv (Since \<phi> I \<psi>) = max (nfv \<phi>) (nfv \<psi>)"
  "nfv (Until \<phi> I \<psi>) = max (nfv \<phi>) (nfv \<psi>)"
  "nfv (MatchP I r) = Regex.nfv_regex fv r"
  "nfv (MatchF I r) = Regex.nfv_regex fv r"
  "nfv_regex (Regex.Skip n) = 0"
  "nfv_regex (Regex.Test \<phi>) = Max (insert 0 (Suc ` fv \<phi>))"
  "nfv_regex (Regex.Plus r s) = max (nfv_regex r) (nfv_regex s)"
  "nfv_regex (Regex.Times r s) = max (nfv_regex r) (nfv_regex s)"
  "nfv_regex (Regex.Star r) = nfv_regex r"
  unfolding nfv_def Regex.nfv_regex_def by (simp_all add: image_Un Max_Un[symmetric])

lemma nfv_Ands[simp]: "nfv (Ands l) = Max (insert 0 (nfv ` set l))"
proof (induction l)
  case Nil
  then show ?case unfolding nfv_def by simp
next
  case (Cons a l)
  have "fv (Ands (a # l)) = fv a \<union> fv (Ands l)" by simp
  then have "nfv (Ands (a # l)) = max (nfv a) (nfv (Ands l))"
    unfolding nfv_def
    by (auto simp: image_Un Max.union[symmetric])
  with Cons.IH show ?case
    by (cases l) auto
qed

lemma fvi_less_nfv: "\<forall>i\<in>fv \<phi>. i < nfv \<phi>"
  unfolding nfv_def
  by (auto simp add: Max_gr_iff intro: max.strict_coboundedI2)

lemma fvi_less_nfv_regex: "\<forall>i\<in>fv_regex \<phi>. i < nfv_regex \<phi>"
  unfolding Regex.nfv_regex_def
  by (auto simp add: Max_gr_iff intro: max.strict_coboundedI2)

subsubsection \<open>Future reach\<close>

qualified fun future_bounded :: "formula \<Rightarrow> bool" where
  "future_bounded (Pred _ _) = True"
| "future_bounded (Let p b \<phi> \<psi>) = (future_bounded \<phi> \<and> future_bounded \<psi>)"
| "future_bounded (Eq _ _) = True"
| "future_bounded (Less _ _) = True"
| "future_bounded (LessEq _ _) = True"
| "future_bounded (Neg \<phi>) = future_bounded \<phi>"
| "future_bounded (Or \<phi> \<psi>) = (future_bounded \<phi> \<and> future_bounded \<psi>)"
| "future_bounded (And \<phi> \<psi>) = (future_bounded \<phi> \<and> future_bounded \<psi>)"
| "future_bounded (Ands l) = list_all future_bounded l"
| "future_bounded (Exists \<phi>) = future_bounded \<phi>"
| "future_bounded (Agg y \<omega> b f \<phi>) = future_bounded \<phi>"
| "future_bounded (Prev I \<phi>) = future_bounded \<phi>"
| "future_bounded (Next I \<phi>) = future_bounded \<phi>"
| "future_bounded (Since \<phi> I \<psi>) = (future_bounded \<phi> \<and> future_bounded \<psi>)"
| "future_bounded (Until \<phi> I \<psi>) = (future_bounded \<phi> \<and> future_bounded \<psi> \<and> right I \<noteq> \<infinity>)"
| "future_bounded (MatchP I r) = Regex.pred_regex future_bounded r"
| "future_bounded (MatchF I r) = (Regex.pred_regex future_bounded r \<and> right I \<noteq> \<infinity>)"


subsubsection \<open>Semantics\<close>

definition "ecard A = (if finite A then card A else \<infinity>)"

qualified fun sat :: "trace \<Rightarrow> (name \<rightharpoonup> nat \<Rightarrow> event_data list set) \<Rightarrow> env \<Rightarrow> nat \<Rightarrow> formula \<Rightarrow> bool" where
  "sat \<sigma> V v i (Pred r ts) = (case V r of
       None \<Rightarrow> (r, map (eval_trm v) ts) \<in> \<Gamma> \<sigma> i
     | Some X \<Rightarrow> map (eval_trm v) ts \<in> X i)"
| "sat \<sigma> V v i (Let p b \<phi> \<psi>) =
    sat \<sigma> (V(p \<mapsto> \<lambda>i. {v. length v = nfv \<phi> - b \<and> (\<exists>zs. length zs = b \<and> sat \<sigma> V (zs @ v) i \<phi>)})) v i \<psi>"
| "sat \<sigma> V v i (Eq t1 t2) = (eval_trm v t1 = eval_trm v t2)"
| "sat \<sigma> V v i (Less t1 t2) = (eval_trm v t1 < eval_trm v t2)"
| "sat \<sigma> V v i (LessEq t1 t2) = (eval_trm v t1 \<le> eval_trm v t2)"
| "sat \<sigma> V v i (Neg \<phi>) = (\<not> sat \<sigma> V v i \<phi>)"
| "sat \<sigma> V v i (Or \<phi> \<psi>) = (sat \<sigma> V v i \<phi> \<or> sat \<sigma> V v i \<psi>)"
| "sat \<sigma> V v i (And \<phi> \<psi>) = (sat \<sigma> V v i \<phi> \<and> sat \<sigma> V v i \<psi>)"
| "sat \<sigma> V v i (Ands l) = (\<forall>\<phi> \<in> set l. sat \<sigma> V v i \<phi>)"
| "sat \<sigma> V v i (Exists \<phi>) = (\<exists>z. sat \<sigma> V (z # v) i \<phi>)"
| "sat \<sigma> V v i (Agg y \<omega> b f \<phi>) =
    (let M = {(x, ecard Zs) | x Zs. Zs = {zs. length zs = b \<and> sat \<sigma> V (zs @ v) i \<phi> \<and> eval_trm (zs @ v) f = x} \<and> Zs \<noteq> {}}
    in (M = {} \<longrightarrow> fv \<phi> \<subseteq> {0..<b}) \<and> v ! y = eval_agg_op \<omega> M)"
| "sat \<sigma> V v i (Prev I \<phi>) = (case i of 0 \<Rightarrow> False | Suc j \<Rightarrow> mem (\<tau> \<sigma> i - \<tau> \<sigma> j) I \<and> sat \<sigma> V v j \<phi>)"
| "sat \<sigma> V v i (Next I \<phi>) = (mem (\<tau> \<sigma> (Suc i) - \<tau> \<sigma> i) I \<and> sat \<sigma> V v (Suc i) \<phi>)"
| "sat \<sigma> V v i (Since \<phi> I \<psi>) = (\<exists>j\<le>i. mem (\<tau> \<sigma> i - \<tau> \<sigma> j) I \<and> sat \<sigma> V v j \<psi> \<and> (\<forall>k \<in> {j <.. i}. sat \<sigma> V v k \<phi>))"
| "sat \<sigma> V v i (Until \<phi> I \<psi>) = (\<exists>j\<ge>i. mem (\<tau> \<sigma> j - \<tau> \<sigma> i) I \<and> sat \<sigma> V v j \<psi> \<and> (\<forall>k \<in> {i ..< j}. sat \<sigma> V v k \<phi>))"
| "sat \<sigma> V v i (MatchP I r) = (\<exists>j\<le>i. mem (\<tau> \<sigma> i - \<tau> \<sigma> j) I \<and> Regex.match (sat \<sigma> V v) r j i)"
| "sat \<sigma> V v i (MatchF I r) = (\<exists>j\<ge>i. mem (\<tau> \<sigma> j - \<tau> \<sigma> i) I \<and> Regex.match (sat \<sigma> V v) r i j)"

lemma sat_abbrevs[simp]:
  "sat \<sigma> V v i TT" "\<not> sat \<sigma> V v i FF"
  unfolding TT_def FF_def by auto

lemma sat_Ands: "sat \<sigma> V v i (Ands l) \<longleftrightarrow> (\<forall>\<phi>\<in>set l. sat \<sigma> V v i \<phi>)"
  by (simp add: list_all_iff)

lemma sat_Until_rec: "sat \<sigma> V v i (Until \<phi> I \<psi>) \<longleftrightarrow>
  mem 0 I \<and> sat \<sigma> V v i \<psi> \<or>
  (\<Delta> \<sigma> (i + 1) \<le> right I \<and> sat \<sigma> V v i \<phi> \<and> sat \<sigma> V v (i + 1) (Until \<phi> (subtract (\<Delta> \<sigma> (i + 1)) I) \<psi>))"
  (is "?L \<longleftrightarrow> ?R")
proof (rule iffI; (elim disjE conjE)?)
  assume ?L
  then obtain j where j: "i \<le> j" "mem (\<tau> \<sigma> j - \<tau> \<sigma> i) I" "sat \<sigma> V v j \<psi>" "\<forall>k \<in> {i ..< j}. sat \<sigma> V v k \<phi>"
    by auto
  then show ?R
  proof (cases "i = j")
    case False
    with j(1,2) have "\<Delta> \<sigma> (i + 1) \<le> right I"
      by (auto elim: order_trans[rotated] simp: diff_le_mono)
    moreover from False j(1,4) have "sat \<sigma> V v i \<phi>" by auto
    moreover from False j have "sat \<sigma> V v (i + 1) (Until \<phi> (subtract (\<Delta> \<sigma> (i + 1)) I) \<psi>)"
      by (cases "right I") (auto simp: le_diff_conv le_diff_conv2 intro!: exI[of _ j])
    ultimately show ?thesis by blast
  qed simp
next
  assume \<Delta>: "\<Delta> \<sigma> (i + 1) \<le> right I" and now: "sat \<sigma> V v i \<phi>" and
   "next": "sat \<sigma> V v (i + 1) (Until \<phi> (subtract (\<Delta> \<sigma> (i + 1)) I) \<psi>)"
  from "next" obtain j where j: "i + 1 \<le> j" "mem (\<tau> \<sigma> j - \<tau> \<sigma> (i + 1)) ((subtract (\<Delta> \<sigma> (i + 1)) I))"
      "sat \<sigma> V v j \<psi>" "\<forall>k \<in> {i + 1 ..< j}. sat \<sigma> V v k \<phi>"
    by auto
  from \<Delta> j(1,2) have "mem (\<tau> \<sigma> j - \<tau> \<sigma> i) I"
    by (cases "right I") (auto simp: le_diff_conv2)
  with now j(1,3,4) show ?L by (auto simp: le_eq_less_or_eq[of i] intro!: exI[of _ j])
qed auto

lemma sat_Since_rec: "sat \<sigma> V v i (Since \<phi> I \<psi>) \<longleftrightarrow>
  mem 0 I \<and> sat \<sigma> V v i \<psi> \<or>
  (i > 0 \<and> \<Delta> \<sigma> i \<le> right I \<and> sat \<sigma> V v i \<phi> \<and> sat \<sigma> V v (i - 1) (Since \<phi> (subtract (\<Delta> \<sigma> i) I) \<psi>))"
  (is "?L \<longleftrightarrow> ?R")
proof (rule iffI; (elim disjE conjE)?)
  assume ?L
  then obtain j where j: "j \<le> i" "mem (\<tau> \<sigma> i - \<tau> \<sigma> j) I" "sat \<sigma> V v j \<psi>" "\<forall>k \<in> {j <.. i}. sat \<sigma> V v k \<phi>"
    by auto
  then show ?R
  proof (cases "i = j")
    case False
    with j(1) obtain k where [simp]: "i = k + 1"
      by (cases i) auto
    with j(1,2) False have "\<Delta> \<sigma> i \<le> right I"
      by (auto elim: order_trans[rotated] simp: diff_le_mono2 le_Suc_eq)
    moreover from False j(1,4) have "sat \<sigma> V v i \<phi>" by auto
    moreover from False j have "sat \<sigma> V v (i - 1) (Since \<phi> (subtract (\<Delta> \<sigma> i) I) \<psi>)"
      by (cases "right I") (auto simp: le_diff_conv le_diff_conv2 intro!: exI[of _ j])
    ultimately show ?thesis by auto
  qed simp
next
  assume i: "0 < i" and \<Delta>: "\<Delta> \<sigma> i \<le> right I" and now: "sat \<sigma> V v i \<phi>" and
   "prev": "sat \<sigma> V v (i - 1) (Since \<phi> (subtract (\<Delta> \<sigma> i) I) \<psi>)"
  from "prev" obtain j where j: "j \<le> i - 1" "mem (\<tau> \<sigma> (i - 1) - \<tau> \<sigma> j) ((subtract (\<Delta> \<sigma> i) I))"
      "sat \<sigma> V v j \<psi>" "\<forall>k \<in> {j <.. i - 1}. sat \<sigma> V v k \<phi>"
    by auto
  from \<Delta> i j(1,2) have "mem (\<tau> \<sigma> i - \<tau> \<sigma> j) I"
    by (cases "right I") (auto simp: le_diff_conv2)
  with now i j(1,3,4) show ?L by (auto simp: le_Suc_eq gr0_conv_Suc intro!: exI[of _ j])
qed auto

lemma sat_MatchF_rec: "sat \<sigma> V v i (MatchF I r) \<longleftrightarrow> mem 0 I \<and> Regex.eps (sat \<sigma> V v) i r \<or>
  \<Delta> \<sigma> (i + 1) \<le> right I \<and> (\<exists>s \<in> Regex.lpd (sat \<sigma> V v) i r. sat \<sigma> V v (i + 1) (MatchF (subtract (\<Delta> \<sigma> (i + 1)) I) s))"
  (is "?L \<longleftrightarrow> ?R1 \<or> ?R2")
proof (rule iffI; (elim disjE conjE bexE)?)
  assume ?L
  then obtain j where j: "j \<ge> i" "mem (\<tau> \<sigma> j - \<tau> \<sigma> i) I" and "Regex.match (sat \<sigma> V v) r i j" by auto
  then show "?R1 \<or> ?R2"
  proof (cases "i < j")
    case True
    with \<open>Regex.match (sat \<sigma> V v) r i j\<close> lpd_match[of i j "sat \<sigma> V v" r]
    obtain s where "s \<in> Regex.lpd (sat \<sigma> V v) i r" "Regex.match (sat \<sigma> V v) s (i + 1) j" by auto
    with True j have ?R2
      by (cases "right I")
        (auto simp: le_diff_conv le_diff_conv2 intro!: exI[of _ j] elim: le_trans[rotated])
    then show ?thesis by blast
  qed (auto simp: eps_match)
next
  assume "enat (\<Delta> \<sigma> (i + 1)) \<le> right I"
  moreover
  fix s
  assume [simp]: "s \<in> Regex.lpd (sat \<sigma> V v) i r" and "sat \<sigma> V v (i + 1) (MatchF (subtract (\<Delta> \<sigma> (i + 1)) I) s)"
  then obtain j where "j > i" "Regex.match (sat \<sigma> V v) s (i + 1) j"
    "mem (\<tau> \<sigma> j - \<tau> \<sigma> (Suc i)) (subtract (\<Delta> \<sigma> (i + 1)) I)" by (auto simp: Suc_le_eq)
  ultimately show ?L
    by (cases "right I")
      (auto simp: le_diff_conv lpd_match intro!: exI[of _ j] bexI[of _ s])
qed (auto simp: eps_match intro!: exI[of _ i])

lemma sat_MatchP_rec: "sat \<sigma> V v i (MatchP I r) \<longleftrightarrow> mem 0 I \<and> Regex.eps (sat \<sigma> V v) i r \<or>
  i > 0 \<and> \<Delta> \<sigma> i \<le> right I \<and> (\<exists>s \<in> Regex.rpd (sat \<sigma> V v) i r. sat \<sigma> V v (i - 1) (MatchP (subtract (\<Delta> \<sigma> i) I) s))"
  (is "?L \<longleftrightarrow> ?R1 \<or> ?R2")
proof (rule iffI; (elim disjE conjE bexE)?)
  assume ?L
  then obtain j where j: "j \<le> i" "mem (\<tau> \<sigma> i - \<tau> \<sigma> j) I" and "Regex.match (sat \<sigma> V v) r j i" by auto
  then show "?R1 \<or> ?R2"
  proof (cases "j < i")
    case True
    with \<open>Regex.match (sat \<sigma> V v) r j i\<close> rpd_match[of j i "sat \<sigma> V v" r]
    obtain s where "s \<in> Regex.rpd (sat \<sigma> V v) i r" "Regex.match (sat \<sigma> V v) s j (i - 1)" by auto
    with True j have ?R2
      by (cases "right I")
        (auto simp: le_diff_conv le_diff_conv2 intro!: exI[of _ j] elim: le_trans)
    then show ?thesis by blast
  qed (auto simp: eps_match)
next
  assume "enat (\<Delta> \<sigma> i) \<le> right I"
  moreover
  fix s
  assume [simp]: "s \<in> Regex.rpd (sat \<sigma> V v) i r" and "sat \<sigma> V v (i - 1) (MatchP (subtract (\<Delta> \<sigma> i) I) s)" "i > 0"
  then obtain j where "j < i" "Regex.match (sat \<sigma> V v) s j (i - 1)"
    "mem (\<tau> \<sigma> (i - 1) - \<tau> \<sigma> j) (subtract (\<Delta> \<sigma> i) I)" by (auto simp: gr0_conv_Suc less_Suc_eq_le)
  ultimately show ?L
    by (cases "right I")
      (auto simp: le_diff_conv rpd_match intro!: exI[of _ j] bexI[of _ s])
qed (auto simp: eps_match intro!: exI[of _ i])

lemma sat_Since_0: "sat \<sigma> V v 0 (Since \<phi> I \<psi>) \<longleftrightarrow> mem 0 I \<and> sat \<sigma> V v 0 \<psi>"
  by auto

lemma sat_MatchP_0: "sat \<sigma> V v 0 (MatchP I r) \<longleftrightarrow> mem 0 I \<and> Regex.eps (sat \<sigma> V v) 0 r"
  by (auto simp: eps_match)

lemma sat_Since_point: "sat \<sigma> V v i (Since \<phi> I \<psi>) \<Longrightarrow>
    (\<And>j. j \<le> i \<Longrightarrow> mem (\<tau> \<sigma> i - \<tau> \<sigma> j) I \<Longrightarrow> sat \<sigma> V v i (Since \<phi> (point (\<tau> \<sigma> i - \<tau> \<sigma> j)) \<psi>) \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto intro: diff_le_self)

lemma sat_MatchP_point: "sat \<sigma> V v i (MatchP I r) \<Longrightarrow>
    (\<And>j. j \<le> i \<Longrightarrow> mem (\<tau> \<sigma> i - \<tau> \<sigma> j) I \<Longrightarrow> sat \<sigma> V v i (MatchP (point (\<tau> \<sigma> i - \<tau> \<sigma> j)) r) \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto intro: diff_le_self)

lemma sat_Since_pointD: "sat \<sigma> V v i (Since \<phi> (point t) \<psi>) \<Longrightarrow> mem t I \<Longrightarrow> sat \<sigma> V v i (Since \<phi> I \<psi>)"
  by auto

lemma sat_MatchP_pointD: "sat \<sigma> V v i (MatchP (point t) r) \<Longrightarrow> mem t I \<Longrightarrow> sat \<sigma> V v i (MatchP I r)"
  by auto

lemma sat_fv_cong: "\<forall>x\<in>fv \<phi>. v!x = v'!x \<Longrightarrow> sat \<sigma> V v i \<phi> = sat \<sigma> V v' i \<phi>"
proof (induct \<phi> arbitrary: V v v' i rule: formula.induct)
  case (Pred n ts)
  show ?case by (simp cong: map_cong eval_trm_fv_cong[OF Pred[simplified, THEN bspec]] split: option.splits)
next
  case (Let p b \<phi> \<psi>)
  then show ?case
    by auto
next
  case (Eq x1 x2)
  then show ?case unfolding fvi.simps sat.simps by (metis UnCI eval_trm_fv_cong)
next
  case (Less x1 x2)
  then show ?case unfolding fvi.simps sat.simps by (metis UnCI eval_trm_fv_cong)
next
  case (LessEq x1 x2)
  then show ?case unfolding fvi.simps sat.simps by (metis UnCI eval_trm_fv_cong)
next
  case (Ands l)
  have "\<And>\<phi>. \<phi> \<in> set l \<Longrightarrow> sat \<sigma> V v i \<phi> = sat \<sigma> V v' i \<phi>"
  proof -
    fix \<phi> assume "\<phi> \<in> set l"
    then have "fv \<phi> \<subseteq> fv (Ands l)" using fv_subset_Ands by blast
    then have "\<forall>x\<in>fv \<phi>. v!x = v'!x" using Ands.prems by blast
    then show "sat \<sigma> V v i \<phi> = sat \<sigma> V v' i \<phi>" using Ands.hyps \<open>\<phi> \<in> set l\<close> by blast
  qed
  then show ?case using sat_Ands by blast
next
  case (Exists \<phi>)
  then show ?case unfolding sat.simps by (intro iff_exI) (simp add: fvi_Suc nth_Cons')
next
  case (Agg y \<omega> b f \<phi>)
  have "v ! y = v' ! y"
    using Agg.prems by simp
  moreover have "sat \<sigma> V (zs @ v) i \<phi> = sat \<sigma> V (zs @ v') i \<phi>" if "length zs = b" for zs
    using that Agg.prems by (simp add: Agg.hyps[where v="zs @ v" and v'="zs @ v'"]
        nth_append fvi_iff_fv(1)[where b=b])
  moreover have "eval_trm (zs @ v) f = eval_trm (zs @ v') f" if "length zs = b" for zs
    using that Agg.prems by (auto intro!: eval_trm_fv_cong[where v="zs @ v" and v'="zs @ v'"]
        simp: nth_append fvi_iff_fv(1)[where b=b] fvi_trm_iff_fv_trm[where b="length zs"])
  ultimately show ?case
    by (simp cong: conj_cong)
next
  case (MatchF I r)
  then have "Regex.match (sat \<sigma> V v) r = Regex.match (sat \<sigma> V v') r"
    by (intro match_fv_cong) (auto simp: fv_regex_alt)
  then show ?case
    by auto
next
  case (MatchP I r)
  then have "Regex.match (sat \<sigma> V v) r = Regex.match (sat \<sigma> V v') r"
    by (intro match_fv_cong) (auto simp: fv_regex_alt)
  then show ?case
    by auto
qed (auto 10 0 split: nat.splits intro!: iff_exI)

lemma match_fv_cong:
  "\<forall>x\<in>fv_regex r. v!x = v'!x \<Longrightarrow> Regex.match (sat \<sigma> V v) r = Regex.match (sat \<sigma> V v') r"
  by (rule match_fv_cong, rule sat_fv_cong) (auto simp: fv_regex_alt)

lemma eps_fv_cong:
  "\<forall>x\<in>fv_regex r. v!x = v'!x \<Longrightarrow> Regex.eps (sat \<sigma> V v) i r = Regex.eps (sat \<sigma> V v') i r"
  unfolding eps_match by (erule match_fv_cong[THEN fun_cong, THEN fun_cong])


subsection \<open>Safe formulas\<close>

fun remove_neg :: "formula \<Rightarrow> formula" where
  "remove_neg (Neg \<phi>) = \<phi>"
| "remove_neg \<phi> = \<phi>"

lemma fvi_remove_neg[simp]: "fvi b (remove_neg \<phi>) = fvi b \<phi>"
  by (cases \<phi>) simp_all

lemma partition_cong[fundef_cong]:
  "xs = ys \<Longrightarrow> (\<And>x. x\<in>set xs \<Longrightarrow> f x = g x) \<Longrightarrow> partition f xs = partition g ys"
  by (induction xs arbitrary: ys) auto

lemma size_remove_neg[termination_simp]: "size (remove_neg \<phi>) \<le> size \<phi>"
  by (cases \<phi>) simp_all

fun is_constraint :: "formula \<Rightarrow> bool" where
  "is_constraint (Eq t1 t2) = True"
| "is_constraint (Less t1 t2) = True"
| "is_constraint (LessEq t1 t2) = True"
| "is_constraint (Neg (Eq t1 t2)) = True"
| "is_constraint (Neg (Less t1 t2)) = True"
| "is_constraint (Neg (LessEq t1 t2)) = True"
| "is_constraint _ = False"

definition safe_assignment :: "nat set \<Rightarrow> formula \<Rightarrow> bool" where
  "safe_assignment X \<phi> = (case \<phi> of
       Eq (Var x) (Var y) \<Rightarrow> (x \<notin> X \<longleftrightarrow> y \<in> X)
     | Eq (Var x) t \<Rightarrow> (x \<notin> X \<and> fv_trm t \<subseteq> X)
     | Eq t (Var x) \<Rightarrow> (x \<notin> X \<and> fv_trm t \<subseteq> X)
     | _ \<Rightarrow> False)"

fun safe_formula :: "formula \<Rightarrow> bool" where
  "safe_formula (Eq t1 t2) = (is_Const t1 \<and> (is_Const t2 \<or> is_Var t2) \<or> is_Var t1 \<and> is_Const t2)"
| "safe_formula (Neg (Eq (Var x) (Var y))) = (x = y)"
| "safe_formula (Less t1 t2) = False"
| "safe_formula (LessEq t1 t2) = False"
| "safe_formula (Pred e ts) = (\<forall>t\<in>set ts. is_Var t \<or> is_Const t)"
| "safe_formula (Let p b \<phi> \<psi>) = ({0..<nfv \<phi>} \<subseteq> fv \<phi> \<and> b \<le> nfv \<phi> \<and> safe_formula \<phi> \<and> safe_formula \<psi>)"
| "safe_formula (Neg \<phi>) = (fv \<phi> = {} \<and> safe_formula \<phi>)"
| "safe_formula (Or \<phi> \<psi>) = (fv \<psi> = fv \<phi> \<and> safe_formula \<phi> \<and> safe_formula \<psi>)"
| "safe_formula (And \<phi> \<psi>) = (safe_formula \<phi> \<and>
    (safe_assignment (fv \<phi>) \<psi> \<or> safe_formula \<psi> \<or>
      fv \<psi> \<subseteq> fv \<phi> \<and> (is_constraint \<psi> \<or> (case \<psi> of Neg \<psi>' \<Rightarrow> safe_formula \<psi>' | _ \<Rightarrow> False))))"
| "safe_formula (Ands l) = (let (pos, neg) = partition safe_formula l in pos \<noteq> [] \<and>
    list_all safe_formula (map remove_neg neg) \<and> \<Union>(set (map fv neg)) \<subseteq> \<Union>(set (map fv pos)))"
| "safe_formula (Exists \<phi>) = (safe_formula \<phi>)"
| "safe_formula (Agg y \<omega> b f \<phi>) = (safe_formula \<phi> \<and> y + b \<notin> fv \<phi> \<and> {0..<b} \<subseteq> fv \<phi> \<and> fv_trm f \<subseteq> fv \<phi>)"
| "safe_formula (Prev I \<phi>) = (safe_formula \<phi>)"
| "safe_formula (Next I \<phi>) = (safe_formula \<phi>)"
| "safe_formula (Since \<phi> I \<psi>) = (fv \<phi> \<subseteq> fv \<psi> \<and>
    (safe_formula \<phi> \<or> (case \<phi> of Neg \<phi>' \<Rightarrow> safe_formula \<phi>' | _ \<Rightarrow> False)) \<and> safe_formula \<psi>)"
| "safe_formula (Until \<phi> I \<psi>) = (fv \<phi> \<subseteq> fv \<psi> \<and>
    (safe_formula \<phi> \<or> (case \<phi> of Neg \<phi>' \<Rightarrow> safe_formula \<phi>' | _ \<Rightarrow> False)) \<and> safe_formula \<psi>)"
| "safe_formula (MatchP I r) = Regex.safe_regex fv (\<lambda>g \<phi>. safe_formula \<phi> \<or>
     (g = Lax \<and> (case \<phi> of Neg \<phi>' \<Rightarrow> safe_formula \<phi>' | _ \<Rightarrow> False))) Past Strict r"
| "safe_formula (MatchF I r) = Regex.safe_regex fv (\<lambda>g \<phi>. safe_formula \<phi> \<or>
     (g = Lax \<and> (case \<phi> of Neg \<phi>' \<Rightarrow> safe_formula \<phi>' | _ \<Rightarrow> False))) Futu Strict r"

abbreviation "safe_regex \<equiv> Regex.safe_regex fv (\<lambda>g \<phi>. safe_formula \<phi> \<or>
  (g = Lax \<and> (case \<phi> of Neg \<phi>' \<Rightarrow> safe_formula \<phi>' | _ \<Rightarrow> False)))"

lemma safe_regex_safe_formula:
  "safe_regex m g r \<Longrightarrow> \<phi> \<in> Regex.atms r \<Longrightarrow> safe_formula \<phi> \<or>
  (\<exists>\<psi>. \<phi> = Neg \<psi> \<and> safe_formula \<psi>)"
  by (cases g) (auto dest!: safe_regex_safe[rotated] split: formula.splits[where formula=\<phi>])

lemma safe_abbrevs[simp]: "safe_formula TT" "safe_formula FF"
  unfolding TT_def FF_def by auto

definition safe_neg :: "formula \<Rightarrow> bool" where
  "safe_neg \<phi> \<longleftrightarrow> (\<not> safe_formula \<phi> \<longrightarrow> safe_formula (remove_neg \<phi>))"

definition atms :: "formula Regex.regex \<Rightarrow> formula set" where
  "atms r = (\<Union>\<phi> \<in> Regex.atms r.
     if safe_formula \<phi> then {\<phi>} else case \<phi> of Neg \<phi>' \<Rightarrow> {\<phi>'} | _ \<Rightarrow> {})"

lemma atms_simps[simp]:
  "atms (Regex.Skip n) = {}"
  "atms (Regex.Test \<phi>) = (if safe_formula \<phi> then {\<phi>} else case \<phi> of Neg \<phi>' \<Rightarrow> {\<phi>'} | _ \<Rightarrow> {})"
  "atms (Regex.Plus r s) = atms r \<union> atms s"
  "atms (Regex.Times r s) = atms r \<union> atms s"
  "atms (Regex.Star r) = atms r"
  unfolding atms_def by auto

lemma finite_atms[simp]: "finite (atms r)"
  by (induct r) (auto split: formula.splits)

lemma disjE_Not2: "P \<or> Q \<Longrightarrow> (P \<Longrightarrow> R) \<Longrightarrow> (\<not>P \<Longrightarrow> Q \<Longrightarrow> R) \<Longrightarrow> R"
  by blast

lemma safe_formula_induct[consumes 1, case_names Eq_Const Eq_Var1 Eq_Var2 neq_Var Pred Let
    And_assign And_safe And_constraint And_Not Ands Neg Or Exists Agg
    Prev Next Since Not_Since Until Not_Until MatchP MatchF]:
  assumes "safe_formula \<phi>"
    and Eq_Const: "\<And>c d. P (Eq (Const c) (Const d))"
    and Eq_Var1: "\<And>c x. P (Eq (Const c) (Var x))"
    and Eq_Var2: "\<And>c x. P (Eq (Var x) (Const c))"
    and neq_Var: "\<And>x. P (Neg (Eq (Var x) (Var x)))"
    and Pred: "\<And>e ts. \<forall>t\<in>set ts. is_Var t \<or> is_Const t \<Longrightarrow> P (Pred e ts)"
    and Let: "\<And>p b \<phi> \<psi>. {0..<nfv \<phi>} \<subseteq> fv \<phi> \<Longrightarrow> b \<le> nfv \<phi> \<Longrightarrow> safe_formula \<phi> \<Longrightarrow> safe_formula \<psi> \<Longrightarrow> P \<phi> \<Longrightarrow> P \<psi> \<Longrightarrow> P (Let p b \<phi> \<psi>)"
    and And_assign: "\<And>\<phi> \<psi>. safe_formula \<phi> \<Longrightarrow> safe_assignment (fv \<phi>) \<psi> \<Longrightarrow> P \<phi> \<Longrightarrow> P (And \<phi> \<psi>)"
    and And_safe: "\<And>\<phi> \<psi>. safe_formula \<phi> \<Longrightarrow> \<not> safe_assignment (fv \<phi>) \<psi> \<Longrightarrow> safe_formula \<psi> \<Longrightarrow>
      P \<phi> \<Longrightarrow> P \<psi> \<Longrightarrow> P (And \<phi> \<psi>)"
    and And_constraint: "\<And>\<phi> \<psi>. safe_formula \<phi> \<Longrightarrow> \<not> safe_assignment (fv \<phi>) \<psi> \<Longrightarrow> \<not> safe_formula \<psi> \<Longrightarrow>
      fv \<psi> \<subseteq> fv \<phi> \<Longrightarrow> is_constraint \<psi> \<Longrightarrow> P \<phi> \<Longrightarrow> P (And \<phi> \<psi>)"
    and And_Not: "\<And>\<phi> \<psi>. safe_formula \<phi> \<Longrightarrow> \<not> safe_assignment (fv \<phi>) (Neg \<psi>) \<Longrightarrow> \<not> safe_formula (Neg \<psi>) \<Longrightarrow>
      fv (Neg \<psi>) \<subseteq> fv \<phi> \<Longrightarrow> \<not> is_constraint (Neg \<psi>) \<Longrightarrow> safe_formula \<psi> \<Longrightarrow> P \<phi> \<Longrightarrow> P \<psi> \<Longrightarrow> P (And \<phi> (Neg \<psi>))"
    and Ands: "\<And>l pos neg. (pos, neg) = partition safe_formula l \<Longrightarrow> pos \<noteq> [] \<Longrightarrow>
      list_all safe_formula pos \<Longrightarrow> list_all safe_formula (map remove_neg neg) \<Longrightarrow>
      (\<Union>\<phi>\<in>set neg. fv \<phi>) \<subseteq> (\<Union>\<phi>\<in>set pos. fv \<phi>) \<Longrightarrow>
      list_all P pos \<Longrightarrow> list_all P (map remove_neg neg) \<Longrightarrow> P (Ands l)"
    and Neg: "\<And>\<phi>. fv \<phi> = {} \<Longrightarrow> safe_formula \<phi> \<Longrightarrow> P \<phi> \<Longrightarrow> P (Neg \<phi>)"
    and Or: "\<And>\<phi> \<psi>. fv \<psi> = fv \<phi> \<Longrightarrow> safe_formula \<phi> \<Longrightarrow> safe_formula \<psi> \<Longrightarrow> P \<phi> \<Longrightarrow> P \<psi> \<Longrightarrow> P (Or \<phi> \<psi>)"
    and Exists: "\<And>\<phi>. safe_formula \<phi> \<Longrightarrow> P \<phi> \<Longrightarrow> P (Exists \<phi>)"
    and Agg: "\<And>y \<omega> b f \<phi>. y + b \<notin> fv \<phi> \<Longrightarrow> {0..<b} \<subseteq> fv \<phi> \<Longrightarrow> fv_trm f \<subseteq> fv \<phi> \<Longrightarrow>
      safe_formula \<phi> \<Longrightarrow> P \<phi> \<Longrightarrow> P (Agg y \<omega> b f \<phi>)"
    and Prev: "\<And>I \<phi>. safe_formula \<phi> \<Longrightarrow> P \<phi> \<Longrightarrow> P (Prev I \<phi>)"
    and Next: "\<And>I \<phi>. safe_formula \<phi> \<Longrightarrow> P \<phi> \<Longrightarrow> P (Next I \<phi>)"
    and Since: "\<And>\<phi> I \<psi>. fv \<phi> \<subseteq> fv \<psi> \<Longrightarrow> safe_formula \<phi> \<Longrightarrow> safe_formula \<psi> \<Longrightarrow> P \<phi> \<Longrightarrow> P \<psi> \<Longrightarrow> P (Since \<phi> I \<psi>)"
    and Not_Since: "\<And>\<phi> I \<psi>. fv (Neg \<phi>) \<subseteq> fv \<psi> \<Longrightarrow> safe_formula \<phi> \<Longrightarrow>
      \<not> safe_formula (Neg \<phi>) \<Longrightarrow> safe_formula \<psi> \<Longrightarrow> P \<phi> \<Longrightarrow> P \<psi> \<Longrightarrow> P (Since (Neg \<phi>) I \<psi> )"
    and Until: "\<And>\<phi> I \<psi>. fv \<phi> \<subseteq> fv \<psi> \<Longrightarrow> safe_formula \<phi> \<Longrightarrow> safe_formula \<psi> \<Longrightarrow> P \<phi> \<Longrightarrow> P \<psi> \<Longrightarrow> P (Until \<phi> I \<psi>)"
    and Not_Until: "\<And>\<phi> I \<psi>. fv (Neg \<phi>) \<subseteq> fv \<psi> \<Longrightarrow> safe_formula \<phi> \<Longrightarrow>
      \<not> safe_formula (Neg \<phi>) \<Longrightarrow> safe_formula \<psi> \<Longrightarrow> P \<phi> \<Longrightarrow> P \<psi> \<Longrightarrow> P (Until (Neg \<phi>) I \<psi>)"
    and MatchP: "\<And>I r. safe_regex Past Strict r \<Longrightarrow> \<forall>\<phi> \<in> atms r. P \<phi> \<Longrightarrow> P (MatchP I r)"
    and MatchF: "\<And>I r. safe_regex Futu Strict r \<Longrightarrow> \<forall>\<phi> \<in> atms r. P \<phi> \<Longrightarrow> P (MatchF I r)"
  shows "P \<phi>"
using assms(1) proof (induction \<phi> rule: safe_formula.induct)
  case (1 t1 t2)
  then show ?case using Eq_Const Eq_Var1 Eq_Var2 by (auto simp: trm.is_Const_def trm.is_Var_def)
next
  case (9 \<phi> \<psi>)
  from \<open>safe_formula (And \<phi> \<psi>)\<close> have "safe_formula \<phi>" by simp
  from \<open>safe_formula (And \<phi> \<psi>)\<close> consider
    (a) "safe_assignment (fv \<phi>) \<psi>"
    | (b) "\<not> safe_assignment (fv \<phi>) \<psi>" "safe_formula \<psi>"
    | (c) "fv \<psi> \<subseteq> fv \<phi>" "\<not> safe_assignment (fv \<phi>) \<psi>" "\<not> safe_formula \<psi>" "is_constraint \<psi>"
    | (d) \<psi>' where "fv \<psi> \<subseteq> fv \<phi>" "\<not> safe_assignment (fv \<phi>) \<psi>" "\<not> safe_formula \<psi>" "\<not> is_constraint \<psi>"
        "\<psi> = Neg \<psi>'" "safe_formula \<psi>'"
    by (cases \<psi>) auto
  then show ?case proof cases
    case a
    then show ?thesis using "9.IH" \<open>safe_formula \<phi>\<close> by (intro And_assign)
  next
    case b
    then show ?thesis using "9.IH" \<open>safe_formula \<phi>\<close> by (intro And_safe)
  next
    case c
    then show ?thesis using "9.IH" \<open>safe_formula \<phi>\<close> by (intro And_constraint)
  next
    case d
    then show ?thesis using "9.IH" \<open>safe_formula \<phi>\<close> by (blast intro!: And_Not)
  qed
next
  case (10 l)
  obtain pos neg where posneg: "(pos, neg) = partition safe_formula l" by simp
  have "pos \<noteq> []" using "10.prems" posneg by simp
  moreover have "list_all safe_formula pos" using posneg by (simp add: list.pred_set)
  moreover have safe_remove_neg: "list_all safe_formula (map remove_neg neg)" using "10.prems" posneg by auto
  moreover have "list_all P pos"
    using posneg "10.IH"(1) by (simp add: list_all_iff)
  moreover have "list_all P (map remove_neg neg)"
    using "10.IH"(2)[OF posneg] safe_remove_neg by (simp add: list_all_iff)
  ultimately show ?case using "10.IH"(1) "10.prems" Ands posneg by simp
next
  case (15 \<phi> I \<psi>)
  then show ?case
  proof (cases \<phi>)
    case (Ands l)
    then show ?thesis using "15.IH"(1) "15.IH"(3) "15.prems" Since by auto
  qed (auto 0 3 elim!: disjE_Not2 intro: Since Not_Since) (*SLOW*)
next
  case (16 \<phi> I \<psi>)
  then show ?case
  proof (cases \<phi>)
    case (Ands l)
    then show ?thesis using "16.IH"(1) "16.IH"(3) "16.prems" Until by auto
  qed (auto 0 3 elim!: disjE_Not2 intro: Until Not_Until) (*SLOW*)
next
  case (17 I r)
  then show ?case
    by (intro MatchP) (auto simp: atms_def dest: safe_regex_safe_formula split: if_splits)
next
  case (18 I r)
  then show ?case
    by (intro MatchF) (auto simp: atms_def dest: safe_regex_safe_formula split: if_splits)
qed (auto simp: assms)

lemma safe_formula_NegD:
  "safe_formula (Formula.Neg \<phi>) \<Longrightarrow> fv \<phi> = {} \<or> (\<exists>x. \<phi> = Formula.Eq (Formula.Var x) (Formula.Var x))"
  by (induct "Formula.Neg \<phi>" rule: safe_formula_induct) auto


subsection \<open>Slicing traces\<close>

qualified fun matches ::
  "env \<Rightarrow> formula \<Rightarrow> name \<times> event_data list \<Rightarrow> bool" where
  "matches v (Pred r ts) e = (fst e = r \<and> map (eval_trm v) ts = snd e)"
| "matches v (Let p b \<phi> \<psi>) e =
    ((\<exists>zs v'. length zs = b \<and> matches (zs @ v') \<phi> e \<and> matches v \<psi> (p, v')) \<or>
    fst e \<noteq> p \<and> matches v \<psi> e)"
| "matches v (Eq _ _) e = False"
| "matches v (Less _ _) e = False"
| "matches v (LessEq _ _) e = False"
| "matches v (Neg \<phi>) e = matches v \<phi> e"
| "matches v (Or \<phi> \<psi>) e = (matches v \<phi> e \<or> matches v \<psi> e)"
| "matches v (And \<phi> \<psi>) e = (matches v \<phi> e \<or> matches v \<psi> e)"
| "matches v (Ands l) e = (\<exists>\<phi>\<in>set l. matches v \<phi> e)"
| "matches v (Exists \<phi>) e = (\<exists>z. matches (z # v) \<phi> e)"
| "matches v (Agg y \<omega> b f \<phi>) e = (\<exists>zs. length zs = b \<and> matches (zs @ v) \<phi> e)"
| "matches v (Prev I \<phi>) e = matches v \<phi> e"
| "matches v (Next I \<phi>) e = matches v \<phi> e"
| "matches v (Since \<phi> I \<psi>) e = (matches v \<phi> e \<or> matches v \<psi> e)"
| "matches v (Until \<phi> I \<psi>) e = (matches v \<phi> e \<or> matches v \<psi> e)"
| "matches v (MatchP I r) e = (\<exists>\<phi> \<in> Regex.atms r. matches v \<phi> e)"
| "matches v (MatchF I r) e = (\<exists>\<phi> \<in> Regex.atms r. matches v \<phi> e)"

lemma matches_cong:
  "\<forall>x\<in>fv \<phi>. v!x = v'!x \<Longrightarrow> matches v \<phi> e = matches v' \<phi> e"
proof (induct \<phi> arbitrary: v v' e)
  case (Pred n ts)
  show ?case
    by (simp cong: map_cong eval_trm_fv_cong[OF Pred(1)[simplified, THEN bspec]])
next
  case (Let p b \<phi> \<psi>)
  then show ?case
    by (cases e) (auto 11 0)
next
  case (Ands l)
  have "\<And>\<phi>. \<phi> \<in> (set l) \<Longrightarrow> matches v \<phi> e = matches v' \<phi> e"
  proof -
    fix \<phi> assume "\<phi> \<in> (set l)"
    then have "fv \<phi> \<subseteq> fv (Ands l)" using fv_subset_Ands by blast
    then have "\<forall>x\<in>fv \<phi>. v!x = v'!x" using Ands.prems by blast
    then show "matches v \<phi> e = matches v' \<phi> e" using Ands.hyps \<open>\<phi> \<in> set l\<close> by blast
  qed
  then show ?case by simp
next
  case (Exists \<phi>)
  then show ?case unfolding matches.simps by (intro iff_exI) (simp add: fvi_Suc nth_Cons')
next
  case (Agg y \<omega> b f \<phi>)
  have "matches (zs @ v) \<phi> e = matches (zs @ v') \<phi> e" if "length zs = b" for zs
    using that Agg.prems by (simp add: Agg.hyps[where v="zs @ v" and v'="zs @ v'"]
        nth_append fvi_iff_fv(1)[where b=b])
  then show ?case by auto
qed (auto 9 0 simp add: nth_Cons' fv_regex_alt)

abbreviation relevant_events where
  "relevant_events \<phi> S \<equiv> {e. S \<inter> {v. matches v \<phi> e} \<noteq> {}}"

qualified definition slice :: "formula \<Rightarrow> env set \<Rightarrow> trace \<Rightarrow> trace" where
  "slice \<phi> S \<sigma> = map_\<Gamma> (\<lambda>D. D \<inter> relevant_events \<phi> S) \<sigma>"

lemma \<tau>_slice[simp]: "\<tau> (slice \<phi> S \<sigma>) = \<tau> \<sigma>"
  unfolding slice_def by (simp add: fun_eq_iff)

lemma sat_slice_strong:
  assumes "v \<in> S" "dom V = dom V'"
    "\<And>p v i. p \<in> dom V \<Longrightarrow> (p, v) \<in> relevant_events \<phi> S \<Longrightarrow> v \<in> the (V p) i \<longleftrightarrow> v \<in> the (V' p) i"
  shows "relevant_events \<phi> S - {e. fst e \<in> dom V} \<subseteq> E \<Longrightarrow>
    sat \<sigma> V v i \<phi> \<longleftrightarrow> sat (map_\<Gamma> (\<lambda>D. D \<inter> E) \<sigma>) V' v i \<phi>"
  using assms
proof (induction \<phi> arbitrary: V V' v S i)
  case (Pred r ts)
  show ?case proof (cases "V r")
    case None
    then have "V' r = None" using \<open>dom V = dom V'\<close> by auto
    with None Pred(1,2) show ?thesis by (auto simp: domIff dest!: subsetD)
  next
    case (Some a)
    moreover obtain a' where "V' r = Some a'" using Some \<open>dom V = dom V'\<close> by auto
    moreover have "(map (eval_trm v) ts \<in> the (V r) i) = (map (eval_trm v) ts \<in> the (V' r) i)"
      using Some Pred(2,4) by (fastforce intro: domI)
    ultimately show ?thesis by simp
  qed
next
  case (Let p b \<phi> \<psi>)
  from Let.prems show ?case unfolding sat.simps
  proof (intro Let(2)[of S], goal_cases relevant v dom V)
    case (V p' v' i)
    then show ?case
    proof (cases "p' = p")
      case [simp]: True
      with V show ?thesis
        unfolding fun_upd_apply eqTrueI[OF True] if_True option.sel mem_Collect_eq
      proof (intro ex_cong conj_cong refl Let(1)[where
        S="{zs @ v' | zs v'. length zs = b \<and> (\<exists>v \<in> S. matches v \<psi> (p, v'))}" and V=V],
        goal_cases relevant' v' dom' V')
        case (relevant' zs)
        then show ?case
          by (elim subset_trans[rotated]) (auto simp: set_eq_iff)
      next
        case (V' zs p' v' i)
        then show ?case
          by (intro V(4)) (auto simp: set_eq_iff)
      qed auto
    next
      case False
      with V(2,3,5,6) show ?thesis
        unfolding fun_upd_apply eq_False[THEN iffD2, OF False] if_False
        by (intro V(4)) (auto simp: False)
    qed
  qed (auto simp: dom_def)
next
  case (Or \<phi> \<psi>)
  show ?case using Or.IH[of S V v V'] Or.prems
    by (auto simp: Collect_disj_eq Int_Un_distrib subset_iff)
next
  case (And \<phi> \<psi>)
  show ?case using And.IH[of S V v V'] And.prems
    by (auto simp: Collect_disj_eq Int_Un_distrib subset_iff)
next
  case (Ands l)
  obtain "relevant_events (Ands l) S - {e. fst e \<in> dom V} \<subseteq> E" "v \<in> S" using Ands.prems(1) Ands.prems(2) by blast
  then have "{e. S \<inter> {v. matches v (Ands l) e} \<noteq> {}} - {e. fst e \<in> dom V} \<subseteq> E" by simp
  have "\<And>\<phi>. \<phi> \<in> set l \<Longrightarrow> sat \<sigma> V v i \<phi> \<longleftrightarrow> sat (map_\<Gamma> (\<lambda>D. D \<inter> E) \<sigma>) V' v i \<phi>"
  proof -
    fix \<phi> assume "\<phi> \<in> set l"
    have "relevant_events \<phi> S = {e. S \<inter> {v. matches v \<phi> e} \<noteq> {}}" by simp
    have "{e. S \<inter> {v. matches v \<phi> e} \<noteq> {}} \<subseteq> {e. S \<inter> {v. matches v (Ands l) e} \<noteq> {}}" (is "?A \<subseteq> ?B")
    proof (rule subsetI)
      fix e assume "e \<in> ?A"
      then have "S \<inter> {v. matches v \<phi> e} \<noteq> {}" by blast
      moreover have "S \<inter> {v. matches v (Ands l) e} \<noteq> {}"
      proof -
        obtain v where "v \<in> S" "matches v \<phi> e" using calculation by blast
        then show ?thesis using \<open>\<phi> \<in> set l\<close> by auto
      qed
      then show "e \<in> ?B" by blast
    qed
    then have "relevant_events \<phi> S - {e. fst e \<in> dom V} \<subseteq> E" using Ands.prems(1) by auto
    then show "sat \<sigma> V v i \<phi> \<longleftrightarrow> sat (map_\<Gamma> (\<lambda>D. D \<inter> E) \<sigma>) V' v i \<phi>"
      using Ands.prems(2,3) \<open>\<phi> \<in> set l\<close>
      by (intro Ands.IH[of \<phi> S V v V' i] Ands.prems(4)) auto
  qed
  show ?case using \<open>\<And>\<phi>. \<phi> \<in> set l \<Longrightarrow> sat \<sigma> V v i \<phi> = sat (map_\<Gamma> (\<lambda>D. D \<inter> E) \<sigma>) V' v i \<phi>\<close> sat_Ands by blast
next
  case (Exists \<phi>)
  have "sat \<sigma> V (z # v) i \<phi> = sat (map_\<Gamma> (\<lambda>D. D \<inter> E) \<sigma>) V' (z # v) i \<phi>" for z
    using Exists.prems(1-3) by (intro Exists.IH[where S="{z # v | v. v \<in> S}"] Exists.prems(4)) auto
  then show ?case by simp
next
  case (Agg y \<omega> b f \<phi>)
  have "sat \<sigma> V (zs @ v) i \<phi> = sat (map_\<Gamma> (\<lambda>D. D \<inter> E) \<sigma>) V' (zs @ v) i \<phi>" if "length zs = b" for zs
    using that Agg.prems(1-3) by (intro Agg.IH[where S="{zs @ v | v. v \<in> S}"] Agg.prems(4)) auto
  then show ?case by (simp cong: conj_cong)
next
  case (Prev I \<phi>)
  then show ?case by (auto cong: nat.case_cong)
next
  case (Next I \<phi>)
  then show ?case by simp
next
  case (Since \<phi> I \<psi>)
  show ?case using Since.IH[of S V] Since.prems
   by (auto simp: Collect_disj_eq Int_Un_distrib subset_iff)
next
  case (Until \<phi> I \<psi>)
  show ?case using Until.IH[of S V] Until.prems
    by (auto simp: Collect_disj_eq Int_Un_distrib subset_iff)
next
  case (MatchP I r)
  from MatchP.prems(1-3) have "Regex.match (sat \<sigma> V v) r = Regex.match (sat (map_\<Gamma> (\<lambda>D. D \<inter> E) \<sigma>) V' v) r"
    by (intro Regex.match_fv_cong MatchP(1)[of _ S V v] MatchP.prems(4)) auto
  then show ?case
    by auto
next
  case (MatchF I r)
  from MatchF.prems(1-3) have "Regex.match (sat \<sigma> V v) r = Regex.match (sat (map_\<Gamma> (\<lambda>D. D \<inter> E) \<sigma>) V' v) r"
    by (intro Regex.match_fv_cong MatchF(1)[of _ S V v] MatchF.prems(4)) auto
  then show ?case
    by auto
qed simp_all

lemma sat_slice_iff:
  assumes "v \<in> S"
  shows "sat \<sigma> V v i \<phi> \<longleftrightarrow> sat (slice \<phi> S \<sigma>) V v i \<phi>"
  unfolding slice_def
  by (rule sat_slice_strong[OF assms]) auto

qualified lift_definition pslice :: "formula \<Rightarrow> env set \<Rightarrow> prefix \<Rightarrow> prefix" is
  "\<lambda>\<phi> S \<pi>. map (\<lambda>(D, t). (D \<inter> relevant_events \<phi> S, t)) \<pi>"
  by (auto simp: o_def split_beta)

lemma prefix_of_pslice_slice: "prefix_of \<pi> \<sigma> \<Longrightarrow> prefix_of (pslice \<phi> R \<pi>) (slice \<phi> R \<sigma>)"
  unfolding slice_def
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
    unfolding slice_def
    by transfer simp
  with 1 show ?thesis by blast
qed

lemma prefix_of_sliceD:
  assumes "prefix_of \<pi>' (slice \<phi> R \<sigma>)"
  shows "\<exists>\<pi>''. \<pi>' = pslice \<phi> R \<pi>'' \<and> prefix_of \<pi>'' \<sigma>"
  using assms unfolding slice_def
  by transfer (auto intro!: exI[of _ "stake (length _) _"] elim: sym dest: sorted_stake)


subsection \<open>Translation to n-ary conjunction\<close>

fun get_and_list :: "formula \<Rightarrow> formula list" where
  "get_and_list (Ands l) = l"
| "get_and_list \<phi> = [\<phi>]"

lemma fv_get_and: "(\<Union>x\<in>(set (get_and_list \<phi>)). fvi b x) = fvi b \<phi>"
  by (induction \<phi> rule: get_and_list.induct) simp_all

lemma safe_get_and: "safe_formula \<phi> \<Longrightarrow> list_all safe_neg (get_and_list \<phi>)"
  by (induction \<phi> rule: get_and_list.induct) (simp_all add: safe_neg_def list_all_iff)

lemma sat_get_and: "sat \<sigma> V v i \<phi> \<longleftrightarrow> list_all (sat \<sigma> V v i) (get_and_list \<phi>)"
  by (induction \<phi> rule: get_and_list.induct) (simp_all add: list_all_iff)

fun convert_multiway :: "formula \<Rightarrow> formula" where
  "convert_multiway (Neg \<phi>) = Neg (convert_multiway \<phi>)"
| "convert_multiway (Or \<phi> \<psi>) = Or (convert_multiway \<phi>) (convert_multiway \<psi>)"
| "convert_multiway (And \<phi> \<psi>) = (if safe_assignment (fv \<phi>) \<psi> then
      And (convert_multiway \<phi>) \<psi>
    else if safe_formula \<psi> then
      Ands (get_and_list (convert_multiway \<phi>) @ get_and_list (convert_multiway \<psi>))
    else if is_constraint \<psi> then
      And (convert_multiway \<phi>) \<psi>
    else Ands (convert_multiway \<psi> # get_and_list (convert_multiway \<phi>)))"
| "convert_multiway (Exists \<phi>) = Exists (convert_multiway \<phi>)"
| "convert_multiway (Agg y \<omega> b f \<phi>) = Agg y \<omega> b f (convert_multiway \<phi>)"
| "convert_multiway (Prev I \<phi>) = Prev I (convert_multiway \<phi>)"
| "convert_multiway (Next I \<phi>) = Next I (convert_multiway \<phi>)"
| "convert_multiway (Since \<phi> I \<psi>) = Since (convert_multiway \<phi>) I (convert_multiway \<psi>)"
| "convert_multiway (Until \<phi> I \<psi>) = Until (convert_multiway \<phi>) I (convert_multiway \<psi>)"
| "convert_multiway (MatchP I r) = MatchP I (Regex.map_regex convert_multiway r)"
| "convert_multiway (MatchF I r) = MatchF I (Regex.map_regex convert_multiway r)"
| "convert_multiway \<phi> = \<phi>"

abbreviation "convert_multiway_regex \<equiv> Regex.map_regex convert_multiway"

lemma fv_safe_get_and:
  "safe_formula \<phi> \<Longrightarrow> fv \<phi> \<subseteq> (\<Union>x\<in>(set (filter safe_formula (get_and_list \<phi>))). fv x)"
proof (induction \<phi> rule: get_and_list.induct)
  case (1 l)
  obtain pos neg where posneg: "(pos, neg) = partition safe_formula l" by simp
  have "get_and_list (Ands l) = l" by simp
  have sub: "(\<Union>x\<in>set neg. fv x) \<subseteq> (\<Union>x\<in>set pos. fv x)" using "1.prems" posneg by simp
  then have "fv (Ands l) \<subseteq> (\<Union>x\<in>set pos. fv x)"
  proof -
    have "fv (Ands l) = (\<Union>x\<in>set pos. fv x) \<union> (\<Union>x\<in>set neg. fv x)" using posneg by auto
    then show ?thesis using sub by simp
  qed
  then show ?case using posneg by auto
qed auto

lemma ex_safe_get_and:
  "safe_formula \<phi> \<Longrightarrow> list_ex safe_formula (get_and_list \<phi>)"
proof (induction \<phi> rule: get_and_list.induct)
  case (1 l)
  have "get_and_list (Ands l) = l" by simp
  obtain pos neg where posneg: "(pos, neg) = partition safe_formula l" by simp
  then have "pos \<noteq> []" using "1.prems" by simp
  then obtain x where "x \<in> set pos" by fastforce
  then show ?case using posneg using Bex_set_list_ex by fastforce
qed simp_all

lemma case_NegE: "(case \<phi> of Neg \<phi>' \<Rightarrow> P \<phi>' | _ \<Rightarrow> False) \<Longrightarrow> (\<And>\<phi>'. \<phi> = Neg \<phi>' \<Longrightarrow> P \<phi>' \<Longrightarrow> Q) \<Longrightarrow> Q"
  by (cases \<phi>) simp_all

lemma convert_multiway_remove_neg: "safe_formula (remove_neg \<phi>) \<Longrightarrow> convert_multiway (remove_neg \<phi>) = remove_neg (convert_multiway \<phi>)"
  by (cases \<phi>) (auto elim: case_NegE)

lemma fv_convert_multiway: "safe_formula \<phi> \<Longrightarrow> fvi b (convert_multiway \<phi>) = fvi b \<phi>"
proof (induction \<phi> arbitrary: b rule: safe_formula.induct)
  case (9 \<phi> \<psi>)
  then show ?case by (cases \<psi>) (auto simp: fv_get_and Un_commute)
next
  case (15 \<phi> I \<psi>)
  show ?case proof (cases "safe_formula \<phi>")
    case True
    with 15 show ?thesis by simp
  next
    case False
    with "15.prems" obtain \<phi>' where "\<phi> = Neg \<phi>'" by (simp split: formula.splits)
    with False 15 show ?thesis by simp
  qed
next
  case (16 \<phi> I \<psi>)
  show ?case proof (cases "safe_formula \<phi>")
    case True
    with 16 show ?thesis by simp
  next
    case False
    with "16.prems" obtain \<phi>' where "\<phi> = Neg \<phi>'" by (simp split: formula.splits)
    with False 16 show ?thesis by simp
  qed
next
  case (17 I r)
  then show ?case
    unfolding convert_multiway.simps fvi.simps fv_regex_alt regex.set_map image_image
    by (intro arg_cong[where f=Union, OF image_cong[OF refl]])
      (auto dest!: safe_regex_safe_formula)
next
  case (18 I r)
  then show ?case
    unfolding convert_multiway.simps fvi.simps fv_regex_alt regex.set_map image_image
    by (intro arg_cong[where f=Union, OF image_cong[OF refl]])
      (auto dest!: safe_regex_safe_formula)
qed (auto simp del: convert_multiway.simps(3))

lemma get_and_nonempty:
  assumes "safe_formula \<phi>"
  shows "get_and_list \<phi> \<noteq> []"
  using assms by (induction \<phi>) auto

lemma future_bounded_get_and:
  "list_all future_bounded (get_and_list \<phi>) = future_bounded \<phi>"
  by (induction \<phi>) simp_all

lemma safe_convert_multiway: "safe_formula \<phi> \<Longrightarrow> safe_formula (convert_multiway \<phi>)"
proof (induction \<phi> rule: safe_formula_induct)
  case (And_safe \<phi> \<psi>)
  let ?a = "And \<phi> \<psi>"
  let ?b = "convert_multiway ?a"
  let ?c\<phi> = "convert_multiway \<phi>"
  let ?c\<psi> = "convert_multiway \<psi>"
  have b_def: "?b = Ands (get_and_list ?c\<phi> @ get_and_list ?c\<psi>)"
    using And_safe by simp
  show ?case proof -
    let ?l = "get_and_list ?c\<phi> @ get_and_list ?c\<psi>"
    obtain pos neg where posneg: "(pos, neg) = partition safe_formula ?l" by simp
    then have "list_all safe_formula pos" by (auto simp: list_all_iff)
    have lsafe_neg: "list_all safe_neg ?l"
      using And_safe \<open>safe_formula \<phi>\<close> \<open>safe_formula \<psi>\<close>
      by (simp add: safe_get_and)
    then have "list_all safe_formula (map remove_neg neg)"
    proof -
      have "\<And>x. x \<in> set neg \<Longrightarrow> safe_formula (remove_neg x)"
      proof -
        fix x assume "x \<in> set neg"
        then have "\<not> safe_formula x" using posneg by auto
        moreover have "safe_neg x" using lsafe_neg \<open>x \<in> set neg\<close>
          unfolding safe_neg_def list_all_iff partition_set[OF posneg[symmetric], symmetric]
          by simp
        ultimately show "safe_formula (remove_neg x)" using safe_neg_def by blast
      qed
      then show ?thesis by (auto simp: list_all_iff)
    qed

    have pos_filter: "pos = filter safe_formula (get_and_list ?c\<phi> @ get_and_list ?c\<psi>)"
      using posneg by simp
    have "(\<Union>x\<in>set neg. fv x) \<subseteq> (\<Union>x\<in>set pos. fv x)"
    proof -
      have 1: "fv ?c\<phi> \<subseteq> (\<Union>x\<in>(set (filter safe_formula (get_and_list ?c\<phi>))). fv x)" (is "_ \<subseteq> ?fv\<phi>")
        using And_safe \<open>safe_formula \<phi>\<close> by (blast intro!: fv_safe_get_and)
      have 2: "fv ?c\<psi> \<subseteq> (\<Union>x\<in>(set (filter safe_formula (get_and_list ?c\<psi>))). fv x)" (is "_ \<subseteq> ?fv\<psi>")
        using And_safe \<open>safe_formula \<psi>\<close> by (blast intro!: fv_safe_get_and)
      have "(\<Union>x\<in>set neg. fv x) \<subseteq> fv ?c\<phi> \<union> fv ?c\<psi>" proof -
        have "\<Union> (fv ` set neg) \<subseteq> \<Union> (fv ` (set pos \<union> set neg))"
          by simp
        also have "... \<subseteq> fv (convert_multiway \<phi>) \<union> fv (convert_multiway \<psi>)"
          unfolding partition_set[OF posneg[symmetric], simplified]
          by (simp add: fv_get_and)
        finally show ?thesis .
      qed
      then have "(\<Union>x\<in>set neg. fv x) \<subseteq> ?fv\<phi> \<union> ?fv\<psi>" using 1 2 by blast
      then show ?thesis unfolding pos_filter by simp
    qed
    have "pos \<noteq> []"
    proof -
      obtain x where "x \<in> set (get_and_list ?c\<phi>)" "safe_formula x"
        using And_safe \<open>safe_formula \<phi>\<close> ex_safe_get_and by (auto simp: list_ex_iff)
      then show ?thesis
        unfolding pos_filter by (auto simp: filter_empty_conv)
    qed
    then show ?thesis unfolding b_def
      using \<open>\<Union> (fv ` set neg) \<subseteq> \<Union> (fv ` set pos)\<close> \<open>list_all safe_formula (map remove_neg neg)\<close>
        \<open>list_all safe_formula pos\<close> posneg
      by simp
  qed
next
  case (And_Not \<phi> \<psi>)
  let ?a = "And \<phi> (Neg \<psi>)"
  let ?b = "convert_multiway ?a"
  let ?c\<phi> = "convert_multiway \<phi>"
  let ?c\<psi> = "convert_multiway \<psi>"
  have b_def: "?b = Ands (Neg ?c\<psi> # get_and_list ?c\<phi>)"
    using And_Not by simp
  show ?case proof -
    let ?l = "Neg ?c\<psi> # get_and_list ?c\<phi>"
    note \<open>safe_formula ?c\<phi>\<close>
    then have "list_all safe_neg (get_and_list ?c\<phi>)" by (simp add: safe_get_and)
    moreover have "safe_neg (Neg ?c\<psi>)"
      using \<open>safe_formula ?c\<psi>\<close> by (simp add: safe_neg_def)
    then have lsafe_neg: "list_all safe_neg ?l" using calculation by simp
    obtain pos neg where posneg: "(pos, neg) = partition safe_formula ?l" by simp
    then have "list_all safe_formula pos" by (auto simp: list_all_iff)
    then have "list_all safe_formula (map remove_neg neg)"
    proof -
      have "\<And>x. x \<in> (set neg) \<Longrightarrow> safe_formula (remove_neg x)"
      proof -
        fix x assume "x \<in> set neg"
        then have "\<not> safe_formula x" using posneg by (auto simp del: filter.simps)
        moreover have "safe_neg x" using lsafe_neg \<open>x \<in> set neg\<close>
          unfolding safe_neg_def list_all_iff partition_set[OF posneg[symmetric], symmetric]
          by simp
        ultimately show "safe_formula (remove_neg x)" using safe_neg_def by blast
      qed
      then show ?thesis using Ball_set_list_all by force
    qed

    have pos_filter: "pos = filter safe_formula ?l"
      using posneg by simp
    have neg_filter: "neg = filter (Not \<circ> safe_formula) ?l"
      using posneg by simp
    have "(\<Union>x\<in>(set neg). fv x) \<subseteq> (\<Union>x\<in>(set pos). fv x)"
    proof -
      have fv_neg: "(\<Union>x\<in>(set neg). fv x) \<subseteq> (\<Union>x\<in>(set ?l). fv x)" using posneg by auto
      have "(\<Union>x\<in>(set ?l). fv x) \<subseteq> fv ?c\<phi> \<union> fv ?c\<psi>"
        using \<open>safe_formula \<phi>\<close> \<open>safe_formula \<psi>\<close>
        by (simp add: fv_get_and fv_convert_multiway)
      also have "fv ?c\<phi> \<union> fv ?c\<psi> \<subseteq> fv ?c\<phi>"
        using \<open>safe_formula \<phi>\<close> \<open>safe_formula \<psi>\<close> \<open>fv (Neg \<psi>) \<subseteq> fv \<phi>\<close>
        by (simp add: fv_convert_multiway[symmetric])
      finally have "(\<Union>x\<in>(set neg). fv x) \<subseteq> fv ?c\<phi>"
        using fv_neg unfolding neg_filter by blast
      then show ?thesis
        unfolding pos_filter
        using fv_safe_get_and[OF And_Not.IH(1)]
        by auto
    qed
    have "pos \<noteq> []"
    proof -
      obtain x where "x \<in> set (get_and_list ?c\<phi>)" "safe_formula x"
        using And_Not.IH \<open>safe_formula \<phi>\<close> ex_safe_get_and by (auto simp: list_ex_iff)
      then show ?thesis
        unfolding pos_filter by (auto simp: filter_empty_conv)
    qed
    then show ?thesis unfolding b_def
      using \<open>\<Union> (fv ` set neg) \<subseteq> \<Union> (fv ` set pos)\<close> \<open>list_all safe_formula (map remove_neg neg)\<close>
        \<open>list_all safe_formula pos\<close> posneg
      by simp
  qed
next
  case (Neg \<phi>)
  have "safe_formula (Neg \<phi>') \<longleftrightarrow> safe_formula \<phi>'" if "fv \<phi>' = {}" for \<phi>'
    using that by (cases "Neg \<phi>'" rule: safe_formula.cases) simp_all
  with Neg show ?case by (simp add: fv_convert_multiway)
next
  case (MatchP I r)
  then show ?case
    by (auto 0 3 simp: atms_def fv_convert_multiway intro!: safe_regex_map_regex
      elim!: disjE_Not2 case_NegE
      dest: safe_regex_safe_formula split: if_splits)
next
  case (MatchF I r)
  then show ?case
    by (auto 0 3 simp: atms_def fv_convert_multiway intro!: safe_regex_map_regex
      elim!: disjE_Not2 case_NegE
      dest: safe_regex_safe_formula split: if_splits)
qed (auto simp: fv_convert_multiway)

lemma future_bounded_convert_multiway: "safe_formula \<phi> \<Longrightarrow> future_bounded (convert_multiway \<phi>) = future_bounded \<phi>"
proof (induction \<phi> rule: safe_formula_induct)
  case (And_safe \<phi> \<psi>)
  let ?a = "And \<phi> \<psi>"
  let ?b = "convert_multiway ?a"
  let ?c\<phi> = "convert_multiway \<phi>"
  let ?c\<psi> = "convert_multiway \<psi>"
  have b_def: "?b = Ands (get_and_list ?c\<phi> @ get_and_list ?c\<psi>)"
    using And_safe by simp
  have "future_bounded ?a = (future_bounded ?c\<phi> \<and> future_bounded ?c\<psi>)"
    using And_safe by simp
  moreover have "future_bounded ?c\<phi> = list_all future_bounded (get_and_list ?c\<phi>)"
    using \<open>safe_formula \<phi>\<close> by (simp add: future_bounded_get_and safe_convert_multiway)
  moreover have "future_bounded ?c\<psi> = list_all future_bounded (get_and_list ?c\<psi>)"
    using \<open>safe_formula \<psi>\<close> by (simp add: future_bounded_get_and safe_convert_multiway)
  moreover have "future_bounded ?b = list_all future_bounded (get_and_list ?c\<phi> @ get_and_list ?c\<psi>)"
    unfolding b_def by simp
  ultimately show ?case by simp
next
  case (And_Not \<phi> \<psi>)
  let ?a = "And \<phi> (Neg \<psi>)"
  let ?b = "convert_multiway ?a"
  let ?c\<phi> = "convert_multiway \<phi>"
  let ?c\<psi> = "convert_multiway \<psi>"
  have b_def: "?b = Ands (Neg ?c\<psi> # get_and_list ?c\<phi>)"
    using And_Not by simp
  have "future_bounded ?a = (future_bounded ?c\<phi> \<and> future_bounded ?c\<psi>)"
    using And_Not by simp
  moreover have "future_bounded ?c\<phi> = list_all future_bounded (get_and_list ?c\<phi>)"
    using \<open>safe_formula \<phi>\<close> by (simp add: future_bounded_get_and safe_convert_multiway)
  moreover have "future_bounded ?b = list_all future_bounded (Neg ?c\<psi> # get_and_list ?c\<phi>)"
    unfolding b_def by (simp add: list.pred_map o_def)
  ultimately show ?case by auto
next
  case (MatchP I r)
  then show ?case
    by (fastforce simp: atms_def regex.pred_set regex.set_map ball_Un
        elim: safe_regex_safe_formula[THEN disjE_Not2])
next
  case (MatchF I r)
  then show ?case
    by (fastforce simp: atms_def regex.pred_set regex.set_map ball_Un
        elim: safe_regex_safe_formula[THEN disjE_Not2])
qed auto

lemma sat_convert_multiway: "safe_formula \<phi> \<Longrightarrow> sat \<sigma> V v i (convert_multiway \<phi>) \<longleftrightarrow> sat \<sigma> V v i \<phi>"
proof (induction \<phi> arbitrary: v i rule: safe_formula_induct)
  case (And_safe \<phi> \<psi>)
  let ?a = "And \<phi> \<psi>"
  let ?b = "convert_multiway ?a"
  let ?la = "get_and_list (convert_multiway \<phi>)"
  let ?lb = "get_and_list (convert_multiway \<psi>)"
  let ?sat = "sat \<sigma> V v i"
  have b_def: "?b = Ands (?la @ ?lb)" using And_safe by simp
  have "list_all ?sat ?la \<longleftrightarrow> ?sat \<phi>" using And_safe sat_get_and by blast
  moreover have "list_all ?sat ?lb \<longleftrightarrow> ?sat \<psi>" using And_safe sat_get_and by blast
  ultimately show ?case using And_safe by (auto simp: list.pred_set)
next
  case (And_Not \<phi> \<psi>)
  let ?a = "And \<phi> (Neg \<psi>)"
  let ?b = "convert_multiway ?a"
  let ?la = "get_and_list (convert_multiway \<phi>)"
  let ?lb = "convert_multiway \<psi>"
  let ?sat = "sat \<sigma> V v i"
  have b_def: "?b = Ands (Neg ?lb # ?la)" using And_Not by simp
  have "list_all ?sat ?la \<longleftrightarrow> ?sat \<phi>" using And_Not sat_get_and by blast
  then show ?case using And_Not by (auto simp: list.pred_set)
next
  case (Agg y \<omega> b f \<phi>)
  then show ?case
    by (simp add: nfv_def fv_convert_multiway cong: conj_cong)
next
  case (MatchP I r)
  then have "Regex.match (sat \<sigma> V v) (convert_multiway_regex r) = Regex.match (sat \<sigma> V v) r"
    unfolding match_map_regex
    by (intro Regex.match_fv_cong)
      (auto 0 4 simp: atms_def elim!: disjE_Not2 dest!: safe_regex_safe_formula)
  then show ?case
    by auto
next
  case (MatchF I r)
  then have "Regex.match (sat \<sigma> V v) (convert_multiway_regex r) = Regex.match (sat \<sigma> V v) r"
    unfolding match_map_regex
    by (intro Regex.match_fv_cong)
      (auto 0 4 simp: atms_def elim!: disjE_Not2 dest!: safe_regex_safe_formula)
  then show ?case
    by auto
qed (auto cong: nat.case_cong)

end (*context*)

lemma Neg_splits:
  "P (case \<phi> of formula.Neg \<psi> \<Rightarrow> f \<psi> | \<phi> \<Rightarrow> g \<phi>) =
   ((\<forall>\<psi>. \<phi> = formula.Neg \<psi> \<longrightarrow> P (f \<psi>)) \<and> ((\<not> Formula.is_Neg \<phi>) \<longrightarrow> P (g \<phi>)))"
  "P (case \<phi> of formula.Neg \<psi> \<Rightarrow> f \<psi> | _ \<Rightarrow> g \<phi>) =
   (\<not> ((\<exists>\<psi>. \<phi> = formula.Neg \<psi> \<and> \<not> P (f \<psi>)) \<or> ((\<not> Formula.is_Neg \<phi>) \<and> \<not> P (g \<phi>))))"
  by (cases \<phi>; auto simp: Formula.is_Neg_def)+

(*<*)
end
(*>*)
