section  \<open>Syntax tree helpers\<close>

theory CPSUtils
imports CPSScheme
begin

text \<open>
This theory defines the sets \<open>lambdas p\<close>, \<open>calls p\<close>, \<open>calls p\<close>, \<open>vars p\<close>, \<open>labels p\<close> and \<open>prims p\<close> as the subexpressions of the program \<open>p\<close>. Finiteness is shown for each of these sets, and some rules about how these sets relate. All these rules are proven more or less the same ways, which is very inelegant due to the nesting of the type and the shape of the derived induction rule.

It would be much nicer to start with these rules and define the set inductively. Unfortunately, that approach would make it very hard to show the finiteness of the sets in question.
\<close>


fun lambdas :: "lambda \<Rightarrow> lambda set"
and lambdasC :: "call \<Rightarrow> lambda set"
and lambdasV :: "val \<Rightarrow> lambda set"
where "lambdas  (Lambda l vs c) = ({Lambda l vs c} \<union> lambdasC c)"
    | "lambdasC (App l d ds) = lambdasV d \<union> \<Union> (lambdasV ` set ds)"
    | "lambdasC (Let l binds c') = (\<Union>(_, y)\<in>set binds. lambdas y) \<union> lambdasC c'"
    | "lambdasV (L l) = lambdas l"
    | "lambdasV _     = {}"

fun calls :: "lambda \<Rightarrow> call set"
and callsC :: "call \<Rightarrow> call set"
and callsV :: "val \<Rightarrow> call set"
where "calls  (Lambda l vs c) = callsC c"
    | "callsC (App l d ds) = {App l d ds} \<union> callsV d \<union> (\<Union>(callsV ` (set ds)))"
    | "callsC (Let l binds c') = {call.Let l binds c'} \<union> ((\<Union>(_, y)\<in>set binds. calls y) \<union> callsC c')"
    | "callsV (L l) = calls l"
    | "callsV _     = {}"

lemma finite_lambdas[simp]: "finite (lambdas l)" and "finite (lambdasC c)" "finite (lambdasV v)"
by (induct rule: lambdas_lambdasC_lambdasV.induct, auto)

lemma finite_calls[simp]: "finite (calls l)" and "finite (callsC c)" "finite (callsV v)"
by (induct rule: calls_callsC_callsV.induct, auto)

fun vars :: "lambda \<Rightarrow> var set"
and varsC :: "call \<Rightarrow> var set"
and varsV :: "val \<Rightarrow> var set"
where "vars (Lambda _ vs c) = set vs \<union> varsC c"
    | "varsC (App _ a as) = varsV a \<union> \<Union>(varsV ` (set as))"
    | "varsC (Let _ binds c') = (\<Union>(v, l)\<in>set binds. {v} \<union> vars l) \<union> varsC c'"
    | "varsV (L l) = vars l"
    | "varsV (R _ v) = {v}"
    | "varsV _  = {}"

lemma finite_vars[simp]: "finite (vars l)" and "finite (varsC c)" "finite (varsV v)"
by (induct rule: vars_varsC_varsV.induct, auto)

fun label :: "lambda + call \<Rightarrow> label"
where "label (Inl (Lambda l _ _)) = l"
    | "label (Inr (App l _ _)) = l"
    | "label (Inr (Let l _ _)) = l"

fun labels :: "lambda \<Rightarrow> label set"
and labelsC :: "call \<Rightarrow> label set"
and labelsV :: "val \<Rightarrow> label set"
where "labels (Lambda l vs c) = {l} \<union> labelsC c"
    | "labelsC (App l a as) = {l} \<union> labelsV a \<union> \<Union>(labelsV ` (set as))"
    | "labelsC (Let l binds c') = {l} \<union> (\<Union>(v, y)\<in>set binds. labels y) \<union> labelsC c'"
    | "labelsV (L l) = labels l"
    | "labelsV (R l _) = {l}"
    | "labelsV _  = {}"

lemma finite_labels[simp]: "finite (labels l)" and "finite (labelsC c)" "finite (labelsV v)"
by (induct rule: labels_labelsC_labelsV.induct, auto)

fun prims :: "lambda \<Rightarrow> prim set"
and primsC :: "call \<Rightarrow> prim set"
and primsV :: "val \<Rightarrow> prim set"
where "prims (Lambda _ vs c) = primsC c"
    | "primsC (App _ a as) = primsV a \<union> \<Union>(primsV ` (set as))"
    | "primsC (Let _ binds c') = (\<Union>(_, y)\<in>set binds. prims y) \<union> primsC c'"
    | "primsV (L l) = prims l"
    | "primsV (R l v) = {}"
    | "primsV (P prim) = {prim}"
    | "primsV (C l v) = {}"

lemma finite_prims[simp]: "finite (prims l)" and "finite (primsC c)" "finite (primsV v)"
by (induct rule: labels_labelsC_labelsV.induct, auto)

fun vals :: "lambda \<Rightarrow> val set"
and valsC :: "call \<Rightarrow> val set"
and valsV :: "val \<Rightarrow> val set"
where "vals (Lambda _ vs c) = valsC c"
    | "valsC (App _ a as) = valsV a \<union> \<Union>(valsV ` (set as))"
    | "valsC (Let _ binds c') = (\<Union>(_, y)\<in>set binds. vals y) \<union> valsC c'"
    | "valsV (L l) = {L l} \<union> vals l"
    | "valsV (R l v) = {R l v}"
    | "valsV (P prim) = {P prim}"
    | "valsV (C l v) = {C l v}"

lemma
  fixes list2 :: "(var \<times> lambda) list" and t :: "var\<times>lambda"
  shows lambdas1: "Lambda l vs c \<in> lambdas x \<Longrightarrow> c \<in> calls x"
  and "Lambda l vs c \<in> lambdasC y \<Longrightarrow> c \<in> callsC y"
  and "Lambda l vs c \<in> lambdasV z \<Longrightarrow> c \<in> callsV z"
  and "\<forall>z\<in> set list. Lambda l vs c \<in> lambdasV z \<longrightarrow> c \<in> callsV z"
  and "\<forall>x\<in> set list2. Lambda l vs c \<in> lambdas (snd x) \<longrightarrow> c \<in> calls (snd x)"
  and "Lambda l vs c \<in> lambdas (snd t) \<Longrightarrow> c \<in> calls (snd t)"
apply (induct rule:mutual_lambda_call_var_inducts)
apply auto
apply (case_tac c, auto)[1]
apply (rule_tac x="((a, b), ba)" in bexI, auto)
done

lemma 
  shows lambdas2: "Lambda l vs c \<in> lambdas x \<Longrightarrow> l \<in> labels x"
  and "Lambda l vs c \<in> lambdasC y \<Longrightarrow> l \<in> labelsC y"
  and "Lambda l vs c \<in> lambdasV z \<Longrightarrow> l \<in> labelsV z"
  and "\<forall>z\<in> set list. Lambda l vs c \<in> lambdasV z \<longrightarrow> l \<in> labelsV z"
  and "\<forall>x\<in> set (list2 :: (var \<times> lambda) list) . Lambda l vs c \<in> lambdas (snd x) \<longrightarrow> l \<in> labels (snd x)"
  and "Lambda l vs c \<in> lambdas (snd (t:: var\<times>lambda)) \<Longrightarrow> l \<in> labels (snd t)"
apply (induct rule:mutual_lambda_call_var_inducts)
apply auto
apply (rule_tac x="((a, b), ba)" in bexI, auto)
done

lemma 
  shows lambdas3: "Lambda l vs c \<in> lambdas x \<Longrightarrow> set vs \<subseteq> vars x"
  and "Lambda l vs c \<in> lambdasC y \<Longrightarrow> set vs \<subseteq> varsC y"
  and "Lambda l vs c \<in> lambdasV z \<Longrightarrow> set vs \<subseteq> varsV z"
  and "\<forall>z\<in> set list. Lambda l vs c \<in> lambdasV z \<longrightarrow> set vs \<subseteq> varsV z"
  and "\<forall>x\<in> set (list2 :: (var \<times> lambda) list) . Lambda l vs c \<in> lambdas (snd x) \<longrightarrow> set vs \<subseteq> vars (snd x)"
  and "Lambda l vs c \<in> lambdas (snd (t:: var\<times>lambda)) \<Longrightarrow> set vs \<subseteq> vars (snd t)"
apply (induct x and y and z and list and list2 and t rule:mutual_lambda_call_var_inducts)
apply auto
apply (erule_tac x="((aa, ba), bb)" in ballE)
apply (rule_tac x="((aa, ba), bb)" in bexI, auto)
done

lemma 
  shows app1: "App l d ds \<in> calls x \<Longrightarrow> d \<in> vals x"
  and "App l d ds \<in> callsC y \<Longrightarrow> d \<in> valsC y"
  and "App l d ds \<in> callsV z \<Longrightarrow> d \<in> valsV z"
  and "\<forall>z\<in> set list. App l d ds \<in> callsV z \<longrightarrow> d \<in> valsV z"
  and "\<forall>x\<in> set (list2 :: (var \<times> lambda) list) . App l d ds \<in> calls (snd x) \<longrightarrow> d \<in> vals (snd x)"
  and "App l d ds \<in> calls (snd (t:: var\<times>lambda)) \<Longrightarrow> d \<in> vals (snd t)"
apply (induct x and y and z and list and list2 and t rule:mutual_lambda_call_var_inducts)
apply auto
apply (case_tac d, auto)
apply (erule_tac x="((a, b), ba)" in ballE)
apply (rule_tac x="((a, b), ba)" in bexI, auto)
done

lemma 
  shows app2: "App l d ds \<in> calls x \<Longrightarrow> set ds \<subseteq> vals x"
  and "App l d ds \<in> callsC y \<Longrightarrow> set ds \<subseteq> valsC y"
  and "App l d ds \<in> callsV z \<Longrightarrow> set ds \<subseteq> valsV z"
  and "\<forall>z\<in> set list. App l d ds \<in> callsV z \<longrightarrow> set ds \<subseteq> valsV z"
  and "\<forall>x\<in> set (list2 :: (var \<times> lambda) list) . App l d ds \<in> calls (snd x) \<longrightarrow> set ds \<subseteq> vals (snd x)"
  and "App l d ds \<in> calls (snd (t:: var\<times>lambda)) \<Longrightarrow> set ds \<subseteq> vals (snd t)"
apply (induct  x and y and z and list and list2 and t rule:mutual_lambda_call_var_inducts)
apply auto
apply (case_tac x, auto)
apply (erule_tac x="((a, b), ba)" in ballE)
apply (rule_tac x="((a, b), ba)" in bexI, auto)
done

lemma 
  shows let1: "Let l binds c' \<in> calls x \<Longrightarrow> l \<in> labels x"
  and "Let l binds c' \<in> callsC y \<Longrightarrow> l \<in> labelsC y"
  and "Let l binds c' \<in> callsV z \<Longrightarrow> l \<in> labelsV z"
  and "\<forall>z\<in> set list. Let l binds c' \<in> callsV z \<longrightarrow> l \<in> labelsV z"
  and "\<forall>x\<in> set (list2 :: (var \<times> lambda) list) . Let l binds c' \<in> calls (snd x) \<longrightarrow> l \<in> labels (snd x)"
  and "Let l binds c' \<in> calls (snd (t:: var\<times>lambda)) \<Longrightarrow> l \<in> labels (snd t)"
apply (induct x and y and z and list and list2 and t rule:mutual_lambda_call_var_inducts)
apply auto
apply (erule_tac x="((a, b), ba)" in ballE)
apply (rule_tac x="((a, b), ba)" in bexI, auto)
done

lemma 
  shows let2: "Let l binds c' \<in> calls x \<Longrightarrow> c' \<in> calls x"
  and "Let l binds c' \<in> callsC y \<Longrightarrow> c' \<in> callsC y"
  and "Let l binds c' \<in> callsV z \<Longrightarrow> c' \<in> callsV z"
  and "\<forall>z\<in> set list. Let l binds c' \<in> callsV z \<longrightarrow> c' \<in> callsV z"
  and "\<forall>x\<in> set (list2 :: (var \<times> lambda) list) . Let l binds c' \<in> calls (snd x) \<longrightarrow> c' \<in> calls (snd x)"
  and "Let l binds c' \<in> calls (snd (t:: var\<times>lambda)) \<Longrightarrow> c' \<in> calls (snd t)"
apply (induct x and y and z and list and list2 and t rule:mutual_lambda_call_var_inducts)
apply auto
apply (case_tac c', auto)
apply (erule_tac x="((a, b), ba)" in ballE)
apply (rule_tac x="((a, b), ba)" in bexI, auto)
done

lemma 
  shows let3: "Let l binds c' \<in> calls x \<Longrightarrow> fst ` set binds \<subseteq> vars x"
  and "Let l binds c' \<in> callsC y \<Longrightarrow> fst ` set binds \<subseteq> varsC y"
  and "Let l binds c' \<in> callsV z \<Longrightarrow> fst ` set binds \<subseteq> varsV z"
  and "\<forall>z\<in> set list. Let l binds c' \<in> callsV z \<longrightarrow> fst ` set binds \<subseteq> varsV z"
  and "\<forall>x\<in> set (list2 :: (var \<times> lambda) list) . Let l binds c' \<in> calls (snd x) \<longrightarrow> fst ` set binds \<subseteq> vars (snd x)"
  and "Let l binds c' \<in> calls (snd (t:: var\<times>lambda)) \<Longrightarrow> fst ` set binds \<subseteq> vars (snd t)"
apply (induct x and y and z and list and list2 and t rule:mutual_lambda_call_var_inducts)
apply auto
apply (erule_tac x="((ab, bc), bd)" in ballE)
apply (rule_tac x="((ab, bc), bd)" in bexI, auto)
done

lemma
  shows let4: "Let l binds c' \<in> calls x \<Longrightarrow> snd ` set binds \<subseteq> lambdas x"
  and "Let l binds c' \<in> callsC y \<Longrightarrow> snd ` set binds \<subseteq> lambdasC y"
  and "Let l binds c' \<in> callsV z \<Longrightarrow> snd ` set binds \<subseteq> lambdasV z"
  and "\<forall>z\<in> set list. Let l binds c' \<in> callsV z \<longrightarrow> snd ` set binds \<subseteq> lambdasV z"
  and "\<forall>x\<in> set (list2 :: (var \<times> lambda) list) . Let l binds c' \<in> calls (snd x) \<longrightarrow> snd ` set binds \<subseteq> lambdas (snd x)"
  and "Let l binds c' \<in> calls (snd (t:: var\<times>lambda)) \<Longrightarrow> snd ` set binds \<subseteq> lambdas (snd t)"
apply (induct x and y and z and list and list2 and t rule:mutual_lambda_call_var_inducts)
apply auto
apply (rule_tac x="((a, b), ba)" in bexI, auto)
apply (case_tac ba, auto)
apply (erule_tac x="((aa, bb), bc)" in ballE)
apply (rule_tac x="((aa, bb), bc)" in bexI, auto)
done

lemma
shows vals1: "P prim \<in> vals p \<Longrightarrow> prim \<in> prims p"
  and "P prim \<in> valsC y \<Longrightarrow> prim \<in> primsC y"
  and "P prim \<in> valsV z \<Longrightarrow> prim \<in> primsV z"
  and "\<forall>z\<in> set list. P prim \<in> valsV z \<longrightarrow> prim \<in> primsV z"
  and "\<forall>x\<in> set (list2 :: (var \<times> lambda) list) . P prim \<in> vals (snd x) \<longrightarrow> prim \<in> prims (snd x)"
  and "P prim \<in> vals (snd (t:: var\<times>lambda)) \<Longrightarrow> prim \<in> prims (snd t)"
apply (induct rule:mutual_lambda_call_var_inducts)
apply auto
apply (erule_tac x="((a, b), ba)" in ballE)
apply (rule_tac x="((a, b), ba)" in bexI, auto)
done

lemma
shows vals2: "R l var \<in> vals p \<Longrightarrow> var \<in> vars p"
  and "R l var \<in> valsC y \<Longrightarrow> var \<in> varsC y"
  and "R l var \<in> valsV z \<Longrightarrow> var \<in> varsV z"
  and "\<forall>z\<in> set list. R l var \<in> valsV z \<longrightarrow> var \<in> varsV z"
  and "\<forall>x\<in> set (list2 :: (var \<times> lambda) list) . R l var \<in> vals (snd x) \<longrightarrow> var \<in> vars (snd x)"
  and "R l var \<in> vals (snd (t:: var\<times>lambda)) \<Longrightarrow> var \<in> vars (snd t)"
apply (induct rule:mutual_lambda_call_var_inducts)
apply auto
apply (erule_tac x="((a, b), ba)" in ballE)
apply (rule_tac x="((a, b), ba)" in bexI, auto)
done

lemma
shows vals3: "L l \<in> vals p \<Longrightarrow> l \<in> lambdas p"
  and "L l \<in> valsC y \<Longrightarrow> l \<in> lambdasC y"
  and "L l \<in> valsV z \<Longrightarrow> l \<in> lambdasV z"
  and "\<forall>z\<in> set list. L l \<in> valsV z \<longrightarrow> l \<in> lambdasV z"
  and "\<forall>x\<in> set (list2 :: (var \<times> lambda) list) . L l \<in> vals (snd x) \<longrightarrow> l \<in> lambdas (snd x)"
  and "L l \<in> vals (snd (t:: var\<times>lambda)) \<Longrightarrow> l \<in> lambdas (snd t)"
apply (induct rule:mutual_lambda_call_var_inducts)
apply auto
apply (erule_tac x="((a, b), ba)" in ballE)
apply (rule_tac x="((a, b), ba)" in bexI, auto)
apply (case_tac l, auto)
done


definition nList :: "'a set => nat => 'a list set"
where "nList A n \<equiv> {l. set l \<le> A \<and> length l = n}"

lemma finite_nList[intro]:
  assumes finA: "finite A"
  shows "finite (nList A n)"
proof(induct n)
case 0 thus ?case by (simp add:nList_def) next
case (Suc n) hence finn: "finite (nList (A) n)" by simp
  have "nList A (Suc n) = (case_prod (#)) ` (A \<times> nList A n)" (is "?lhs = ?rhs")
  proof(rule subset_antisym[OF subsetI subsetI])
  fix l assume "l \<in> ?lhs" thus "l \<in> ?rhs"
    by (cases l, auto simp add:nList_def)
  next
  fix l assume "l \<in> ?rhs" thus "l \<in> ?lhs"
    by (auto simp add:nList_def)
  qed
  thus "finite ?lhs" using finA and finn
    by auto
qed

definition NList :: "'a set => nat set => 'a list set"
where "NList A N \<equiv> \<Union> n \<in> N. nList A n"

lemma finite_Nlist[intro]:
  "\<lbrakk> finite A; finite N \<rbrakk> \<Longrightarrow> finite (NList A N)"
unfolding NList_def by auto

definition call_list_lengths
  where "call_list_lengths p = {0,1,2,3} \<union> (\<lambda>c. case c of (App _ _ ds) \<Rightarrow> length ds | _ \<Rightarrow> 0) ` calls p"

lemma finite_call_list_lengths[simp]: "finite (call_list_lengths p)"
  unfolding call_list_lengths_def by auto

end
